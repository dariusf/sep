module

public import Sep.Xsimpl.Core
public meta import Lean

public section

open Lean Meta Elab Tactic

/-!
# Frame inference and biabduction over the `SepLaws` class

The `xsimpl` pipeline of `Sep/Xsimpl/Core.lean` cancels matching atoms.  This file
adds the two *granular* steps that make an entailment with metavariable
remainders solvable: a leftover atom on the left is absorbed into a frame
metavariable on the right, and a missing atom on the right is absorbed into an
anti-frame metavariable on the left.  Both accumulate item-by-item behind an
open tail, closed to `emp` at the end.

Everything is stated over the registered operations, so any `SepLaws` instance
inherits it.  `inferFrame` is the programmatic entry point other tactics call.
-/

namespace Sep.Xsimpl

/-- The user name marking an internally created open tail of a frame /
anti-frame accumulator.  User-supplied metavariables carry any other name and
survive `xsimpl_close_frames`. -/
meta def frameTailName : Name := `_xsimpl_frame_tail

private meta def isInternalTail (e : Expr) : MetaM Bool := do
  if !e.isMVar then return false
  return (← e.mvarId!.getDecl).userName == frameTailName

private meta def isUserMVar (e : Expr) : MetaM Bool := do
  if !e.isMVar then return false
  return (← e.mvarId!.getDecl).userName != frameTailName

/-- Absorb one atom into an accumulator metavariable: `acc := atom ∗ ?tail`. -/
private meta def absorbInto (c : NCtx) (acc atom : Expr) : MetaM Unit := do
  let tail ← mkFreshExprMVar (← inferType acc) (userName := frameTailName)
  acc.mvarId!.assign (c.mkStar atom tail)

/-- Absorb the first missing resource of the RHS into an anti-frame
metavariable on the LHS. -/
elab "xsimpl_abduce_step_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) ← matchEntails? goalType | throwError "not an entailment"
  let some acc := (parseStar c lhs).find? Expr.isMVar
    | throwError "xsimpl_abduce_step: no anti-frame metavariable on the LHS"
  let some missing := (parseStar c rhs).find? (fun e => !e.isMVar)
    | throwError "xsimpl_abduce_step: no missing resource on the RHS"
  absorbInto c acc missing
  trace[xsimpl] m!"Granularly Abduced: {missing}"

/-- Drop one leftover resource of the LHS, which affinity permits. -/
private meta def dropLeftover (goal : MVarId) (c : NCtx) (aff : LawsAt) (rhs leftover lhs : Expr) :
    TacticM Unit := do
  let (newLhs, lhsProof) ← starMoveToFront c leftover lhs
  let rest := (matchStar? c newLhs).map (·.2)
  let newGoalLhs := rest.getD c.empE
  let newGoal ← mkFreshExprMVar (c.mkEnt newGoalLhs rhs)
  let (eqProof, mid, weaken) ← match rest with
    | some tail => do
      let comm := c.lem ``SepLaws.star_comm #[leftover, tail]
      pure (← mkEqTrans lhsProof comm, c.mkStar tail leftover,
        c.lemAt aff ``Sep.Xsimpl.sep_weaken_leftover #[tail, leftover])
    | none => pure (lhsProof, leftover, c.lemAt aff ``AffineSepLaws.entails_emp #[leftover])
  let step := c.lem ``SepLaws.entails_trans #[mid, newGoalLhs, rhs, weaken, newGoal]
  goal.assign (← c.lhsEq eqProof step)
  replaceMainGoal [newGoal.mvarId!]

/-- Absorb the first leftover resource of the LHS into a frame metavariable on
the RHS.  With no frame metavariable and an affine carrier, drop it instead. -/
elab "xsimpl_frame_step_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) ← matchEntails? goalType | throwError "not an entailment"
  let some acc := (parseStar c rhs).find? Expr.isMVar
    | do
      let some aff ← affineLaws? c
        | throwError "xsimpl_frame_step: no frame metavariable on the RHS"
      let some leftover := (parseStar c lhs).find? (fun e => !e.isMVar)
        | throwError "xsimpl_frame_step: no leftover resource on the LHS"
      dropLeftover goal c aff rhs leftover lhs
      trace[xsimpl] m!"Affinely Dropped: {leftover}"
      return
  let some leftover := (parseStar c lhs).find? (fun e => !e.isMVar)
    | throwError "xsimpl_frame_step: no leftover resource on the LHS"
  absorbInto c acc leftover
  trace[xsimpl] m!"Granularly Framed: {leftover}"

/-- Close the open tails: a user metavariable facing an internal tail is
threaded into it (so the user's frame stays open across calls), and every
remaining internal tail becomes `emp`. -/
elab "xsimpl_close_frames_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) ← matchEntails? goalType | throwError "not an entailment"
  let lhsItems := parseStar c lhs
  let rhsItems := parseStar c rhs
  let emp := c.empE

  let lhsUsers ← lhsItems.filterM (fun e => isUserMVar e)
  let rhsUsers ← rhsItems.filterM (fun e => isUserMVar e)
  let lhsInternals ← lhsItems.filterM (fun e => isInternalTail e)
  let rhsInternals ← rhsItems.filterM (fun e => isInternalTail e)

  let mut progress := false
  if lhsUsers.length == 1 && rhsInternals.length == 1 && rhsUsers.isEmpty then
    rhsInternals[0]!.mvarId!.assign lhsUsers[0]!
    progress := true
  else if rhsUsers.length == 1 && lhsInternals.length == 1 && lhsUsers.isEmpty then
    lhsInternals[0]!.mvarId!.assign rhsUsers[0]!
    progress := true

  for item in lhsItems ++ rhsItems do
    if ← isInternalTail item then
      let m := item.mvarId!
      unless ← m.isAssigned do
        m.assign emp
        progress := true

  unless progress do throwError "xsimpl_close_frames: no open frames to close"

  let newGoalType ← instantiateMVars goalType
  let newGoal ← mkFreshExprMVar newGoalType
  goal.assign newGoal
  replaceMainGoal [newGoal.mvarId!]

syntax "xsimpl_abduce_step" : tactic
macro_rules
  | `(tactic| xsimpl_abduce_step) => `(tactic| xsimpl_abduce_step_core)

syntax "xsimpl_frame_step" : tactic
macro_rules
  | `(tactic| xsimpl_frame_step) => `(tactic| xsimpl_frame_step_core)

syntax "xsimpl_close_frames" : tactic
macro_rules
  | `(tactic| xsimpl_close_frames) => `(tactic| xsimpl_close_frames_core)

syntax "xsimpl_frame_steps" : tactic
macro_rules
  | `(tactic| xsimpl_frame_steps) => `(tactic| (
      first
      | xsimpl_abduce_step
      | xsimpl_frame_step
    ))

/-- `xsimpl` extended with granular frame / anti-frame inference: cancels what
matches and assigns the remainders to the metavariables the goal carries. -/
syntax "xsimpl_granular_frames" : tactic
macro_rules
  | `(tactic| xsimpl_granular_frames) => `(tactic| (
      xsimpl_core_with xsimpl_frame_steps
      try xsimpl_close_frames
      try xsimpl_normalize
      all_goals (
        try xsimpl_clean
      )
    ))

/-- **Programmatic entry point.**  Given a goal `P2 ⊢ P1 ∗ ?frame` (or any
entailment carrying frame / anti-frame metavariables), cancel the matching atoms
and assign the remainders.  Returns the goals left over. -/
meta def inferFrame (goal : MVarId) : TacticM (List MVarId) := do
  let gs ← Tactic.run goal (evalTactic (← `(tactic| xsimpl_granular_frames)))
  return gs

end Sep.Xsimpl
