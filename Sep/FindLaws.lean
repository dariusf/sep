module

public import Sep.SepLogic
public meta import Lean
public import Mathlib.Tactic.Linter.UnusedTacticExtension

public section

open Lean Meta

/-!
# Looking up a logic's operators

Given a type, finds its `SepLaws` instance and returns the six operators that
instance is stated for (entailment, star, emp, pure, exists, wand), along with
how to recognise each one in a goal.

This is how `xsimpl`, reordering, and frame inference work on any logic, by calling this to learn which constants to look for.

Entry points: `sepLaws?`, which finds the instance and its operators,
and `opTemplate`, which says how to recognise an operator in a goal.
-/

namespace Sep

meta structure NOp where
  name : Name
  arity : Nat
  pos : Array Nat
  deriving Inhabited, BEq

meta structure LawsAt where
  lv : Level
  ops : Array Expr
  inst : Expr
  deriving Inhabited

meta initialize lawsCache : IO.Ref (Name × Array (Name × Expr × Level × Option LawsAt)) ←
  IO.mkRef (.anonymous, #[])

meta def queryLaws (cls : Name) (carrier : Expr) (u lv : Level) : MetaM (Option LawsAt) := do
  let c := mkConst cls [u, lv]
  let ty ← instantiateForall (← inferType c) #[carrier]
  let (ms, _, _) ← forallMetaTelescope ty
  let some inst ← synthInstance? (mkAppN c (#[carrier] ++ ms)) | return none
  let inst ← instantiateMVars inst
  let ops ← ms.mapM fun m => do return (← Core.betaReduce (← instantiateMVars m)).eta
  if inst.hasMVar || ops.any (·.hasMVar) then return none
  return some { lv, ops, inst }

meta def lawsAt? (cls : Name) (carrier : Expr) (u lv : Level) : MetaM (Option LawsAt) := do
  let m := (← getEnv).mainModule
  let (m0, cache) ← lawsCache.get
  let cache := if m0 == m then cache else #[]
  match cache.find? (fun e => e.1 == cls && e.2.1 == carrier && e.2.2.1 == lv) with
  | some (_, _, _, r) => return r
  | none =>
    let r ← try queryLaws cls carrier u lv catch _ => pure none
    lawsCache.set (m, cache.push (cls, carrier, lv, r))
    return r

meta def sepLaws? (carrier : Expr) : MetaM (Option (Level × LawsAt)) := do
  let some u ← (try some <$> getDecLevel carrier catch _ => pure none) | return none
  if u.hasMVar then return none
  if let some l ← lawsAt? ``SepLaws carrier u Level.zero then return some (u, l)
  if let some l ← lawsAt? ``SepLaws carrier u Level.one then return some (u, l)
  return none

meta def opTemplate (op : Expr) (args : Array Expr) : Option (NOp × Expr × Array Expr) := do
  let e := (mkAppN op args).headBeta
  let fn := e.getAppFn
  guard fn.isConst
  let eargs := e.getAppArgs
  let pos ← args.mapM fun a => eargs.findIdx? (· == a)
  let tmpl := eargs.mapIdx fun i a => if pos.contains i then mkSort Level.zero else a
  guard (tmpl.all fun a => args.all fun x => !a.containsFVar x.fvarId!)
  return ({ name := fn.constName!, arity := eargs.size, pos }, fn, tmpl)

meta def mkOp (op : Expr) (args : Array Expr) : Expr := (mkAppN op args).headBeta

end Sep
