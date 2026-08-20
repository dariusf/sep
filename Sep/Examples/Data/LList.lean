import Sep.HProp
import Sep.Xsimpl
import Lean
open Lean Meta Elab Tactic
open HProp Notation

namespace Sep.LList

-- Fix val = Nat so Loc ≅ val and next-pointers are representable.
instance NatParams : Params where val := Nat

-- ============================================================
-- Definition
-- ============================================================

/-- `llist p xs` represents a singly-linked spine starting at `p` with values `xs`.
    Each node occupies two locations: `p` for the value, `p+1` for the next-pointer
    (a `Nat` ≅ `Loc`). -/
def llist : Loc → List Nat → HProp
  | _, []       => hempty
  | p, v :: vs  => hexists fun (q : Loc) =>
      (p ↦ v) ✶ ((p + 1) ↦ q) ✶ llist q vs

-- ============================================================
-- Fold / unfold lemmas
-- ============================================================

@[simp] theorem llist_nil (p : Loc) : llist p [] = emp := rfl

@[simp] theorem llist_cons (p : Loc) (v : Nat) (vs : List Nat) :
    llist p (v :: vs) = ∃✶ q : Loc, (p ↦ v) ✶ ((p + 1) ↦ q) ✶ llist q vs := rfl

-- ============================================================
-- xsimpl extension tactic
-- ============================================================

/-- Return `true` iff `e` is a `llist p (v :: vs)` (non-empty list). -/
private def isLlistCons (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``LList.llist, #[_, _, .app (.app (.const ``List.cons _) _) _]) => true
  | _ => false

/-- Unfold one `llist p (v :: vs)` atom using `llist_cons`, then normalize the
    new existential through the hstar chain. -/
private def rewriteLlistCons : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let (fn, args) := goalType.getAppFnArgs
  unless fn == ``HProp.himpl && args.size == 3 do return false
  let lhs := args[1]!
  let rhs := args[2]!
  for (side, items) in [("lhs", Sep.Xsimpl.parseHstar lhs), ("rhs", Sep.Xsimpl.parseHstar rhs)] do
    for item in items do
      if isLlistCons item then
        trace[xsimpl] m!"llist unfold on {side}: {← ppExpr item}"
        evalTactic (← `(tactic|
          simp only [Sep.LList.llist_cons,
                     HProp.hstar_hexists, Sep.Xsimpl.hstar_hexists_r]))
        return true
  return false

/-- One step: unfold any `llist p (v :: vs)` atom in the current goal. -/
elab "xsimpl_llist_step" : tactic => withMainContext do
  let progress ← rewriteLlistCons
  unless progress do throwError "xsimpl_llist_step: no llist cons to unfold"

/-- `xsimpl` extended with automatic unfolding of `llist` cons cells. -/
syntax "xsimpl_llist" : tactic
macro_rules
  | `(tactic| xsimpl_llist) => `(tactic|
      xsimpl_core_with xsimpl_llist_step)

-- ============================================================
-- Demonstration
-- ============================================================

-- (1) Unfolding is exact: xsimpl_llist closes the goal without residuals.
example (p : Loc) (v : Nat) (vs : List Nat) :
    llist p (v :: vs) ==>
      ∃✶ q : Loc, (p ↦ v) ✶ ((p + 1) ↦ q) ✶ llist q vs := by
  xsimpl_llist

-- (2) Frame: llist on both sides with extra heap — xsimpl_llist unfolds both
-- sides and the standard cancellation machinery handles the rest.
example (p : Loc) (v : Nat) (H : HProp) :
    H ✶ llist p [v] ==> llist p [v] ✶ H := by
  xsimpl_llist

-- (3) Two cons cells: unfold with llist_cons first, then use xsimpl for the ∃-algebra.
-- This illustrates that the fold/unfold lemmas integrate smoothly with xsimpl.
example (p : Loc) (v w : Nat) (vs : List Nat) :
    llist p (v :: w :: vs) ==>
      ∃✶ q : Loc, ∃✶ r : Loc,
        (p ↦ v) ✶ ((p + 1) ↦ q) ✶
        (q ↦ w) ✶ ((q + 1) ↦ r) ✶
        llist r vs := by
  simp only [llist_cons]
  xsimpl

end Sep.LList
