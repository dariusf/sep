import Sep.FinmapExt
import Lean

open Lean Meta Elab Tactic

namespace Finmap

universe u v

variable {α : Type u} {β : Type v}

def disjoint_3 (m1 m2 m3 : Finmap fun _ : α => β) : Prop :=
  Disjoint m1 m2 ∧ Disjoint m2 m3 ∧ Disjoint m1 m3

theorem disjoint_3_unfold (m1 m2 m3 : Finmap fun _ : α => β) :
    disjoint_3 m1 m2 m3 ↔ Disjoint m1 m2 ∧ Disjoint m2 m3 ∧ Disjoint m1 m3 :=
  Iff.rfl

section Tactics

variable [DecidableEq α]

theorem union_eq_cancel_1 (m1 m2 m3 : Finmap fun _ : α => β)
    (h : m2 = m3) :
    m1 ∪ m2 = m1 ∪ m3 := by
  rw [h]

theorem union_comm_assoc (m1 m2 m3 : Finmap fun _ : α => β)
    (h : Disjoint m1 m2) :
    m1 ∪ (m2 ∪ m3) = m2 ∪ (m1 ∪ m3) := by
  rw [← union_assoc, union_comm_of_disjoint h, union_assoc]

syntax "rew_fmap" : tactic
macro_rules
  | `(tactic| rew_fmap) =>
    `(tactic| simp only [Finmap.union_assoc, Finmap.empty_union, Finmap.union_empty])

syntax "fmap_disjoint" : tactic
macro_rules
  | `(tactic| fmap_disjoint) => `(tactic| (
      subst_vars
      simp_all only [Finmap.disjoint_union_left, Finmap.disjoint_union_right,
        Finmap.disjoint_3_unfold, Finmap.Disjoint.symm_iff, Finmap.disjoint_empty,
        Finmap.disjoint_empty_right, and_true, true_and] <;> tauto
    ))

def unionArgs? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e := e.consumeMData
  unless e.isAppOfArity ``Finmap.union 5 || e.isAppOfArity ``Union.union 4 do
    return none
  unless (← whnf (← inferType e)).isAppOf ``Finmap do
    return none
  let args := e.getAppArgs
  return some (args[args.size - 2]!, args[args.size - 1]!)

def eqRhs (proof : Expr) : MetaM Expr := do
  let some (_, _, rhs) := (← whnf (← inferType proof)).eq?
    | throwError m!"expected an equality proof, got {proof}"
  return rhs

partial def moveToFront (atom : Expr) (tree : Expr) (disjointMvars : IO.Ref (List MVarId)) :
    MetaM (Expr × Expr) := do
  let tree := tree.consumeMData
  if (← isDefEq atom tree) then
    return (tree, ← mkEqRefl tree)

  if let some (h1, h2) ← unionArgs? tree then
    if (← isDefEq atom h1) then
      return (tree, ← mkEqRefl tree)
    else
      let (newTail, tailProof) ← moveToFront atom h2 disjointMvars
      let headProof ← mkAppM ``union_eq_cancel_1 #[h1, h2, newTail, tailProof]
      if let some (atom1, tailTail) ← unionArgs? newTail then
        let swapType ← mkAppM ``Finmap.Disjoint #[h1, atom1]
        let swapGoal ← mkFreshExprMVar (some swapType)
        disjointMvars.modify (·.concat swapGoal.mvarId!)
        let step2 ← mkAppM ``union_comm_assoc #[h1, atom1, tailTail, swapGoal]
        let totalProof ← mkEqTrans headProof step2
        return (← eqRhs totalProof, totalProof)
      else
        let swapType ← mkAppM ``Finmap.Disjoint #[h1, atom]
        let swapGoal ← mkFreshExprMVar (some swapType)
        disjointMvars.modify (·.concat swapGoal.mvarId!)
        let resProof ← mkAppM ``Finmap.union_comm_of_disjoint #[swapGoal]
        let totalProof ← mkEqTrans headProof resProof
        return (← eqRhs totalProof, totalProof)

  throwError m!"Atom {atom} not found in tree {tree}"

partial def matchTrees (lhs rhs : Expr) (disjointMvars : IO.Ref (List MVarId)) : MetaM Expr := do
  let lhs := lhs.consumeMData
  let rhs := rhs.consumeMData
  if (← isDefEq lhs rhs) then
    return (← mkEqRefl lhs)

  if let some (h1, h2) ← unionArgs? lhs then
    let (newRhs, rhsPullProof) ← moveToFront h1 rhs disjointMvars
    if let some (_, nrTail) ← unionArgs? newRhs then
      let tailProof ← matchTrees h2 nrTail disjointMvars
      let headMatchProof ← mkAppM ``union_eq_cancel_1 #[h1, h2, nrTail, tailProof]
      return (← mkEqTrans headMatchProof (← mkEqSymm rhsPullProof))

  throwError m!"Cannot match LHS {lhs} with RHS {rhs}"

elab "fmap_eq" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let goals ← evalTacticAt (← `(tactic| (try subst_vars; try rew_fmap))) goal
    for g in goals do
      g.withContext do
        let type ← g.getType'
        if let some (_, lhs, rhs) := type.eq? then
          let disjointMvars ← IO.mkRef []
          let finalProof ← matchTrees lhs rhs disjointMvars
          g.assign finalProof

          let pending ← disjointMvars.get
          let mut remaining := []
          for mvarId in pending do
            try
              let subgoals ← evalTacticAt (← `(tactic| fmap_disjoint)) mvarId
              remaining := remaining ++ subgoals
            catch _ =>
              remaining := remaining ++ [mvarId]
          replaceMainGoal remaining
        else
          replaceMainGoal [g]

end Tactics
end Finmap
