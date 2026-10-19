namespace Bench.SmtLib

inductive Sort' where
  | int
  | bool
  | named (name : String)
  deriving Repr, BEq, Inhabited

structure Field where
  name : String
  sort : Sort'
  deriving Repr, BEq, Inhabited

structure Constructor where
  name   : String
  fields : Array Field
  deriving Repr, BEq, Inhabited

structure Datatype where
  name         : String
  constructors : Array Constructor
  deriving Repr, BEq, Inhabited

structure Binder where
  name : String
  sort : Sort'
  deriving Repr, BEq, Inhabited

inductive Term where
  | var (name : String)
  | nil (sort : String)
  | intLit (n : Int)
  | true
  | false
  | emp
  | pto (loc : Term) (ctor : String) (args : Array Term)
  | sep (args : Array Term)
  | wand (l r : Term)
  | app (pred : String) (args : Array Term)
  | and (args : Array Term)
  | or (args : Array Term)
  | not (t : Term)
  | implies (l r : Term)
  | eq (args : Array Term)
  | distinct (args : Array Term)
  | exists (binders : Array Binder) (body : Term)
  | forall (binders : Array Binder) (body : Term)
  | add (args : Array Term)
  | sub (args : Array Term)
  | mul (args : Array Term)
  | neg (t : Term)
  | lt (l r : Term)
  | le (l r : Term)
  | gt (l r : Term)
  | ge (l r : Term)
  | ite (c t e : Term)
  | letIn (bindings : Array (String × Term)) (body : Term)
  deriving Repr, BEq, Inhabited

structure FunDef where
  name   : String
  params : Array Binder
  result : Sort'
  body   : Term
  deriving Repr, BEq, Inhabited

inductive Command where
  | setLogic (name : String)
  | setInfo (key : String) (value : String)
  | declareSort (name : String) (arity : Nat)
  | declareDatatypes (types : Array Datatype)
  | declareHeap (pairs : Array (Sort' × Sort'))
  | declareConst (name : String) (sort : Sort')
  | defineFunRec (defs : Array FunDef)
  | assert (t : Term)
  | checkSat
  deriving Repr, BEq, Inhabited

structure Problem where
  path     : String
  commands : Array Command
  deriving Repr, Inhabited

def Problem.status (p : Problem) : Option String :=
  p.commands.findSome? fun
    | .setInfo ":status" v => some v
    | _ => none

def Problem.logic (p : Problem) : Option String :=
  p.commands.findSome? fun
    | .setLogic l => some l
    | _ => none

def Problem.funDefs (p : Problem) : Array FunDef :=
  p.commands.foldl (init := #[]) fun acc c => match c with
    | .defineFunRec ds => acc ++ ds
    | _ => acc

def Problem.datatypes (p : Problem) : Array Datatype :=
  p.commands.foldl (init := #[]) fun acc c => match c with
    | .declareDatatypes ds => acc ++ ds
    | _ => acc

def Problem.consts (p : Problem) : Array Binder :=
  p.commands.foldl (init := #[]) fun acc c => match c with
    | .declareConst n s => acc.push { name := n, sort := s }
    | _ => acc

def Problem.asserts (p : Problem) : Array Term :=
  p.commands.foldl (init := #[]) fun acc c => match c with
    | .assert t => acc.push t
    | _ => acc

def Problem.entailment (p : Problem) : Option (Term × Term) :=
  match p.asserts with
  | #[lhs, .not rhs] => some (lhs, rhs)
  | _ => none

end Bench.SmtLib
