import Bench.SmtLib.Ast
import Bench.SmtLib.Sexp

namespace Bench.SmtLib
namespace Parser

open Sexp

abbrev M := Except String

private def fail (ctx : String) (s : Sexp) : M α :=
  .error s!"{ctx}: {Sexp.toString s}"

private def atom! (ctx : String) (s : Sexp) : M String :=
  match s with
  | .atom a => .ok a
  | _ => fail s!"{ctx}: expected an atom" s

private def list! (ctx : String) (s : Sexp) : M (Array Sexp) :=
  match s with
  | .list xs => .ok xs
  | _ => fail s!"{ctx}: expected a list" s

def parseSort (s : Sexp) : M Sort' := do
  match s with
  | .atom "Int" => .ok .int
  | .atom "Bool" => .ok .bool
  | .atom a => .ok (.named a)
  | _ => fail "unsupported sort" s

def parseBinder (s : Sexp) : M Binder := do
  match ← list! "binder" s with
  | #[n, so] => return { name := ← atom! "binder name" n, sort := ← parseSort so }
  | _ => fail "malformed binder" s

def parseBinders (s : Sexp) : M (Array Binder) := do
  (← list! "binder list" s).mapM parseBinder

private def isIntLit (a : String) : Bool :=
  !a.isEmpty && a.all Char.isDigit

private def toInt (a : String) : Int := Int.ofNat a.toNat!

private def binary (ctx : String) (f : Term → Term → Term) (args : Array Term)
    (s : Sexp) : M Term :=
  if args.size = 2 then .ok (f args[0]! args[1]!) else fail s!"{ctx} expects 2 arguments" s

mutual

partial def parseTerm (s : Sexp) : M Term := do
  match s with
  | .atom a =>
    if a == "true" then return .true
    else if a == "false" then return .false
    else if a == "emp" then return .emp
    else if isIntLit a then return .intLit (toInt a)
    else if a.startsWith "|" || a.startsWith "\"" then fail "unexpected literal in term" s
    else return .var a
  | .list xs =>
    if xs.isEmpty then fail "empty term" s
    else
      match xs[0]! with
      | .list _ => fail "unsupported applied term (head is not a symbol)" s
      | .atom head => parseApp head xs[1:].toArray s

partial def parseApp (head : String) (args : Array Sexp) (s : Sexp) : M Term := do
  match head with
  | "_" =>
    match args[0]? with
    | some (Sexp.atom "emp") => return .emp
    | _ => fail "unsupported indexed term" s
  | "as" =>
    match args with
    | #[Sexp.atom "nil", so] => return .nil (← atom! "nil sort" so)
    | _ => fail "unsupported 'as' term" s
  | "pto" =>
    match args with
    | #[loc, cell] =>
      let l ← parseTerm loc
      match cell with
      | .list cs =>
        if cs.isEmpty then fail "empty cell in pto" s
        else
          let cn ← atom! "pto constructor" cs[0]!
          return .pto l cn (← cs[1:].toArray.mapM parseTerm)
      | .atom a => return .pto l a #[]
    | _ => fail "pto expects 2 arguments" s
  | "sep" => return .sep (← args.mapM parseTerm)
  | "wand" => binary "wand" .wand (← args.mapM parseTerm) s
  | "and" => return .and (← args.mapM parseTerm)
  | "or" => return .or (← args.mapM parseTerm)
  | "not" =>
    match args with
    | #[t] => return .not (← parseTerm t)
    | _ => fail "not expects 1 argument" s
  | "=>" => binary "=>" .implies (← args.mapM parseTerm) s
  | "=" => return .eq (← args.mapM parseTerm)
  | "distinct" => return .distinct (← args.mapM parseTerm)
  | "exists" =>
    match args with
    | #[bs, body] => return .exists (← parseBinders bs) (← parseTerm body)
    | _ => fail "exists expects binders and a body" s
  | "forall" =>
    match args with
    | #[bs, body] => return .forall (← parseBinders bs) (← parseTerm body)
    | _ => fail "forall expects binders and a body" s
  | "+" => return .add (← args.mapM parseTerm)
  | "*" => return .mul (← args.mapM parseTerm)
  | "-" =>
    let ts ← args.mapM parseTerm
    if ts.size = 1 then return .neg ts[0]!
    else if ts.isEmpty then fail "- expects arguments" s
    else return .sub ts
  | "<" => binary "<" .lt (← args.mapM parseTerm) s
  | "<=" => binary "<=" .le (← args.mapM parseTerm) s
  | ">" => binary ">" .gt (← args.mapM parseTerm) s
  | ">=" => binary ">=" .ge (← args.mapM parseTerm) s
  | "ite" =>
    match args with
    | #[c, t, e] => return .ite (← parseTerm c) (← parseTerm t) (← parseTerm e)
    | _ => fail "ite expects 3 arguments" s
  | "let" =>
    match args with
    | #[bs, body] =>
      let bindings ← (← list! "let bindings" bs).mapM fun b => do
        match ← list! "let binding" b with
        | #[n, v] => return (← atom! "let binding name" n, ← parseTerm v)
        | _ => fail "malformed let binding" b
      return .letIn bindings (← parseTerm body)
    | _ => fail "let expects bindings and a body" s
  | _ =>
    if isIntLit head then fail "integer literal applied as a function" s
    else return .app head (← args.mapM parseTerm)

end

def parseConstructor (s : Sexp) : M Constructor := do
  match s with
  | .atom a => return { name := a, fields := #[] }
  | .list cs =>
    if cs.isEmpty then fail "empty constructor" s
    else
      let name ← atom! "constructor name" cs[0]!
      let fields ← cs[1:].toArray.mapM fun f => do
        match ← list! "selector" f with
        | #[n, so] => return ({ name := ← atom! "selector name" n, sort := ← parseSort so } : Field)
        | _ => fail "malformed selector" f
      return { name := name, fields := fields }

def parseDatatypes (args : Array Sexp) (s : Sexp) : M (Array Datatype) := do
  match args with
  | #[names, bodies] =>
    let names ← list! "datatype names" names
    let bodies ← list! "datatype bodies" bodies
    if names.size != bodies.size then fail "declare-datatypes arity mismatch" s
    else
      names.zipIdx.mapM fun (n, i) => do
        let name ← match n with
          | .atom a => pure a
          | .list ns =>
            if ns.isEmpty then fail "empty datatype name" n else atom! "datatype name" ns[0]!
        let ctors ← (← list! "constructor list" bodies[i]!).mapM parseConstructor
        return { name := name, constructors := ctors }
  | _ => fail "declare-datatypes expects 2 arguments" s

def parseCommand (s : Sexp) : M Command := do
  let xs ← list! "command" s
  if xs.isEmpty then fail "empty command" s else
  let head ← atom! "command name" xs[0]!
  let args := xs[1:].toArray
  match head with
  | "set-logic" =>
    match args with
    | #[l] => return .setLogic (← atom! "logic" l)
    | _ => fail "set-logic expects 1 argument" s
  | "set-info" =>
    if args.isEmpty then fail "set-info expects a keyword" s
    else
      let key ← atom! "set-info keyword" args[0]!
      let value := String.intercalate " " (args[1:].toArray.toList.map fun v =>
        match v with
        | .atom a => Sexp.unquote a
        | v => Sexp.toString v)
      return .setInfo key value
  | "set-option" => fail "unsupported command 'set-option'" s
  | "declare-sort" =>
    match args with
    | #[n, a] =>
      let ar ← atom! "sort arity" a
      if isIntLit ar then return .declareSort (← atom! "sort name" n) ar.toNat!
      else fail "declare-sort arity must be a numeral" s
    | _ => fail "declare-sort expects 2 arguments" s
  | "declare-datatypes" => return .declareDatatypes (← parseDatatypes args s)
  | "declare-datatype" =>
    match args with
    | #[n, body] =>
      let ctors ← (← list! "constructor list" body).mapM parseConstructor
      return .declareDatatypes #[{ name := ← atom! "datatype name" n, constructors := ctors }]
    | _ => fail "declare-datatype expects 2 arguments" s
  | "declare-heap" =>
    let pairs ← args.mapM fun p => do
      match ← list! "heap pair" p with
      | #[a, b] => return (← parseSort a, ← parseSort b)
      | _ => fail "malformed heap pair" p
    return .declareHeap pairs
  | "declare-const" =>
    match args with
    | #[n, so] => return .declareConst (← atom! "const name" n) (← parseSort so)
    | _ => fail "declare-const expects 2 arguments" s
  | "define-fun-rec" | "define-fun" =>
    match args with
    | #[n, ps, res, body] =>
      return .defineFunRec #[{ name := ← atom! "function name" n, params := ← parseBinders ps,
                               result := ← parseSort res, body := ← parseTerm body }]
    | _ => fail s!"{head} expects 4 arguments" s
  | "define-funs-rec" =>
    match args with
    | #[sigs, bodies] =>
      let sigs ← list! "signatures" sigs
      let bodies ← list! "bodies" bodies
      if sigs.size != bodies.size then fail "define-funs-rec arity mismatch" s
      else
        let defs ← sigs.zipIdx.mapM fun (sg, i) => do
          match ← list! "signature" sg with
          | #[n, ps, res] =>
            return ({ name := ← atom! "function name" n, params := ← parseBinders ps,
                      result := ← parseSort res, body := ← parseTerm bodies[i]! } : FunDef)
          | _ => fail "malformed signature" sg
        return .defineFunRec defs
    | _ => fail "define-funs-rec expects 2 arguments" s
  | "assert" =>
    match args with
    | #[t] => return .assert (← parseTerm t)
    | _ => fail "assert expects 1 argument" s
  | "check-sat" => return .checkSat
  | _ => fail s!"unknown command '{head}'" s

def parseProblem (path : String) (contents : String) : Except String Problem := do
  let sexps ← Sexp.parse contents
  let commands ← sexps.mapM fun s =>
    match parseCommand s with
    | .ok c => .ok c
    | .error e => .error s!"{path}: {e}"
  return { path := path, commands := commands }

def parseFile (path : System.FilePath) : IO (Except String Problem) := do
  let contents ← IO.FS.readFile path
  return parseProblem path.toString contents

end Parser
end Bench.SmtLib
