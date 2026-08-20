import Sep.SepLogic

open Lean Meta Elab Tactic

/-!
# Frame inference and biabduction over the `SepLogic` class

The `xsimpl` pipeline of `Sep/SepLogic.lean` cancels matching atoms.  This file
adds the two *granular* steps that make an entailment with metavariable
remainders solvable: a leftover atom on the left is absorbed into a frame
metavariable on the right, and a missing atom on the right is absorbed into an
anti-frame metavariable on the left.  Both accumulate item-by-item behind an
open tail, closed to `emp` at the end.

Everything is stated in the class operations, so any `SepLogic` instance
inherits it.  `inferFrame` is the programmatic entry point other tactics call.
-/

namespace Sep.Xsimpl

/-- The user name marking an internally created open tail of a frame /
anti-frame accumulator.  User-supplied metavariables carry any other name and
survive `xsimpl_close_frames`. -/
def frameTailName : Name := `_xsimpl_frame_tail

private def isInternalTail (e : Expr) : MetaM Bool := do
  if !e.isMVar then return false
  return (← e.mvarId!.getDecl).userName == frameTailName

private def isUserMVar (e : Expr) : MetaM Bool := do
  if !e.isMVar then return false
  return (← e.mvarId!.getDecl).userName != frameTailName

/-- Absorb one atom into an accumulator metavariable: `acc := atom ∗ ?tail`. -/
private def absorbInto (c : SepCtx) (acc atom : Expr) : MetaM Unit := do
  let tail ← mkFreshExprMVar (← inferType acc) (userName := frameTailName)
  acc.mvarId!.assign (← mkAppOptM ``SepLogic.star
    #[some c.carrier, some c.inst, some atom, some tail])

/-- Absorb the first missing resource of the RHS into an anti-frame
metavariable on the LHS. -/
elab "xsimpl_abduce_step_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) := matchEntails? goalType | throwError "not an entailment"
  let some acc := (parseStar lhs).find? Expr.isMVar
    | throwError "xsimpl_abduce_step: no anti-frame metavariable on the LHS"
  let some missing := (parseStar rhs).find? (fun e => !e.isMVar)
    | throwError "xsimpl_abduce_step: no missing resource on the RHS"
  absorbInto c acc missing
  trace[xsimpl] m!"Granularly Abduced: {missing}"

/-- Drop one leftover resource of the LHS, which affinity permits. -/
private def dropLeftover (goal : MVarId) (c : SepCtx) (aff lhs rhs leftover : Expr) :
    TacticM Unit := do
  let (newLhs, lhsProof) ← starMoveToFront c leftover lhs
  let rest := match matchStar? newLhs with
    | some (_, _, tail) => some tail
    | none => none
  let newGoalLhs ← match rest with
    | some tail => pure tail
    | none => mkAppOptM ``SepLogic.emp #[some c.carrier, some c.inst]
  let newGoalType ← mkAppOptM ``SepLogic.Entails
    #[some c.carrier, some c.inst, some newGoalLhs, some rhs]
  let newGoal ← mkFreshExprMVar newGoalType
  let weaken ← match rest with
    | some tail => do
      let comm ← mkAppOptM ``SepLogic.star_comm
        #[some c.carrier, some c.inst, some leftover, some tail]
      let lhsProof ← mkEqTrans lhsProof comm
      pure (lhsProof, ← mkAppOptM ``Sep.Xsimpl.sep_weaken_leftover
        #[some c.carrier, some aff, some tail, some leftover])
    | none =>
      pure (lhsProof, ← mkAppOptM ``AffineSepLogic.entails_emp #[some c.carrier, some aff,
        some leftover])
  let step ← mkAppOptM ``SepLogic.entails_trans
    #[some c.carrier, some c.inst, none, none, none, some weaken.2, some newGoal]
  goal.assign (← mkAppOptM ``Sep.Xsimpl.himpl_lhs_eq
    #[some c.carrier, some c.inst, none, none, none, some weaken.1, some step])
  replaceMainGoal [newGoal.mvarId!]

/-- Absorb the first leftover resource of the LHS into a frame metavariable on
the RHS.  With no frame metavariable and an affine carrier, drop it instead. -/
elab "xsimpl_frame_step_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) := matchEntails? goalType | throwError "not an entailment"
  let some acc := (parseStar rhs).find? Expr.isMVar
    | do
      let some aff ← affineInst? c.carrier
        | throwError "xsimpl_frame_step: no frame metavariable on the RHS"
      let some leftover := (parseStar lhs).find? (fun e => !e.isMVar)
        | throwError "xsimpl_frame_step: no leftover resource on the LHS"
      dropLeftover goal c aff lhs rhs leftover
      trace[xsimpl] m!"Affinely Dropped: {leftover}"
      return
  let some leftover := (parseStar lhs).find? (fun e => !e.isMVar)
    | throwError "xsimpl_frame_step: no leftover resource on the LHS"
  absorbInto c acc leftover
  trace[xsimpl] m!"Granularly Framed: {leftover}"

/-- Close the open tails: a user metavariable facing an internal tail is
threaded into it (so the user's frame stays open across calls), and every
remaining internal tail becomes `emp`. -/
elab "xsimpl_close_frames_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) := matchEntails? goalType | throwError "not an entailment"
  let lhsItems := parseStar lhs
  let rhsItems := parseStar rhs
  let emp ← mkAppOptM ``SepLogic.emp #[some c.carrier, some c.inst]

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
  | `(tactic| xsimpl_abduce_step) => `(tactic| xsimpl_in_class xsimpl_abduce_step_core)

syntax "xsimpl_frame_step" : tactic
macro_rules
  | `(tactic| xsimpl_frame_step) => `(tactic| xsimpl_in_class xsimpl_frame_step_core)

syntax "xsimpl_close_frames" : tactic
macro_rules
  | `(tactic| xsimpl_close_frames) => `(tactic| xsimpl_in_class xsimpl_close_frames_core)

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
def inferFrame (goal : MVarId) : TacticM (List MVarId) := do
  let gs ← Tactic.run goal (evalTactic (← `(tactic| xsimpl_granular_frames)))
  return gs

end Sep.Xsimpl
