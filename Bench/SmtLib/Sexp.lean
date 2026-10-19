namespace Bench.SmtLib

inductive Sexp where
  | atom (s : String)
  | list (xs : Array Sexp)
  deriving Repr, BEq, Inhabited

namespace Sexp

partial def toString : Sexp → String
  | .atom s => s
  | .list xs => "(" ++ String.intercalate " " (xs.toList.map toString) ++ ")"

instance : ToString Sexp := ⟨toString⟩

def isDelim (c : Char) : Bool :=
  c.isWhitespace || c == '(' || c == ')' || c == ';' || c == '"' || c == '|'

structure State where
  src : Array Char
  pos : Nat
  line : Nat

private def peek? (s : State) : Option Char :=
  s.src[s.pos]?

private def advance (s : State) : State :=
  match s.src[s.pos]? with
  | none => s
  | some c => { s with pos := s.pos + 1, line := if c == '\n' then s.line + 1 else s.line }

private partial def dropLine (s : State) : State :=
  match peek? s with
  | none => s
  | some c => if c == '\n' then advance s else dropLine (advance s)

private partial def skipTrivia (s : State) : State :=
  match peek? s with
  | none => s
  | some c =>
    if c.isWhitespace then skipTrivia (advance s)
    else if c == ';' then skipTrivia (dropLine s)
    else s

private def err (s : State) (msg : String) : String :=
  s!"line {s.line}: {msg}"

private partial def readUntil (s : State) (close : Char) (acc : String) :
    Except String (String × State) :=
  match peek? s with
  | none => .error (err s s!"unterminated '{close}'-delimited token")
  | some c =>
    if c == close then .ok (acc, advance s)
    else readUntil (advance s) close (acc.push c)

private partial def readAtom (s : State) (acc : String) : String × State :=
  match peek? s with
  | none => (acc, s)
  | some c => if isDelim c then (acc, s) else readAtom (advance s) (acc.push c)

mutual

private partial def parseList (s : State) (acc : Array Sexp) : Except String (Sexp × State) := do
  let s := skipTrivia s
  match peek? s with
  | none => .error (err s "unterminated list")
  | some ')' => .ok (.list acc, advance s)
  | some _ =>
    let (x, s) ← parseOne s
    parseList s (acc.push x)

private partial def parseOne (s : State) : Except String (Sexp × State) := do
  let s := skipTrivia s
  match peek? s with
  | none => .error (err s "unexpected end of input")
  | some c =>
    if c == '(' then
      parseList (advance s) #[]
    else if c == ')' then
      .error (err s "unexpected ')'")
    else if c == '|' then
      let (body, s) ← readUntil (advance s) '|' ""
      .ok (.atom ("|" ++ body ++ "|"), s)
    else if c == '"' then
      let (body, s) ← readUntil (advance s) '"' ""
      .ok (.atom ("\"" ++ body ++ "\""), s)
    else
      let (a, s) := readAtom s ""
      if a.isEmpty then .error (err s s!"unexpected character '{c}'") else .ok (.atom a, s)

end

private partial def parseTop (s : State) (acc : Array Sexp) : Except String (Array Sexp) := do
  let s := skipTrivia s
  match peek? s with
  | none => .ok acc
  | some _ =>
    let (x, s) ← parseOne s
    parseTop s (acc.push x)

def parse (src : String) : Except String (Array Sexp) :=
  parseTop { src := src.toList.toArray, pos := 0, line := 1 } #[]

def asAtom? : Sexp → Option String
  | .atom s => some s
  | _ => none

def asList? : Sexp → Option (Array Sexp)
  | .list xs => some xs
  | _ => none

def unquote (s : String) : String :=
  if s.length ≥ 2 && ((s.front == '|' && s.back == '|') || (s.front == '"' && s.back == '"')) then
    ((s.drop 1).dropEnd 1).toString
  else s

end Sexp

end Bench.SmtLib
