import Lean
import Lean.Elab.Tactic.Rewrite

/-!
# A typeclass of separation logics, and a generic `xsimpl`

`SepLogic α` bundles the operations and laws that the `xsimpl` entailment
simplifier depends on. `Sep/Xsimpl.lean` instantiates it at `HProp`; any other
separation logic can reuse the whole tactic pipeline by providing an instance.

The tactic works on goals headed by the *class projections* (`SepLogic.Entails`,
`SepLogic.star`, ...). Concrete logics register `rfl`-lemmas that translate their
own constants into the class operations with `@[xsimpl_fold]`, and the reverse
orientation with `@[xsimpl_unfold_class]`; `xsimpl` folds at the start and
unfolds residual goals at the end.
-/

open Lean Meta Elab Tactic

universe u v

/-- The fragment of a separation logic that `xsimpl` reasons about. -/
class SepLogic (α : Type u) where
  /-- Separating conjunction. -/
  star : α → α → α
  /-- The empty resource, the unit of `star`. -/
  emp : α
  /-- Pure propositions. Named `spure` to avoid clashing with `Monad.pure`. -/
  spure : Prop → α
  /-- Existential quantification. -/
  ex : {A : Sort v} → (A → α) → α
  /-- Separating implication. -/
  wand : α → α → α
  /-- Entailment. -/
  Entails : α → α → Prop
  star_comm : ∀ H1 H2, star H1 H2 = star H2 H1
  star_assoc : ∀ H1 H2 H3, star (star H1 H2) H3 = star H1 (star H2 H3)
  star_emp_l : ∀ H, star emp H = H
  star_emp_r : ∀ H, star H emp = H
  star_ex : ∀ {A : Sort v} (J : A → α) (H : α),
    star (ex J) H = ex (fun x => star (J x) H)
  entails_refl : ∀ H, Entails H H
  entails_trans : ∀ {H1 H2 H3}, Entails H1 H2 → Entails H2 H3 → Entails H1 H3
  entails_antisym : ∀ {H1 H2}, Entails H1 H2 → Entails H2 H1 → H1 = H2
  frame_r : ∀ {H P1 P2}, Entails P1 P2 → Entails (star H P1) (star H P2)
  frame_l : ∀ {H P1 P2}, Entails P1 P2 → Entails (star P1 H) (star P2 H)
  ex_l : ∀ {A : Sort v} {J : A → α} {H}, (∀ x, Entails (J x) H) → Entails (ex J) H
  ex_r : ∀ {A : Sort v} (x : A) {J : A → α} {H}, Entails H (J x) → Entails H (ex J)
  pure_l : ∀ {P : Prop} {H1 H2}, (P → Entails H1 H2) → Entails (star (spure P) H1) H2
  pure_r : ∀ {P : Prop} {H1 H2}, P → Entails H1 H2 → Entails H1 (star (spure P) H2)
  wand_cancel : ∀ H1 H2, Entails (star H1 (wand H1 H2)) H2
  wand_intro : ∀ {H1 P1 P2}, Entails (star H1 P1) P2 → Entails H1 (wand P1 P2)
  wand_curry : ∀ H1 H2 H3, wand (star H1 H2) H3 = wand H1 (wand H2 H3)

/-- A separation logic whose resources may be discarded. -/
class AffineSepLogic (α : Type u) extends SepLogic α where
  entails_emp : ∀ H, Entails H emp

namespace SepLogic

@[inherit_doc] scoped infixr:61 " ∗ " => SepLogic.star
@[inherit_doc] scoped infixr:60 " -∗ " => SepLogic.wand
@[inherit_doc] scoped infixr:25 " ==> " => SepLogic.Entails
scoped notation:max "emp" => SepLogic.emp
scoped notation:max "⌜" P "⌝" => SepLogic.spure P

open Lean in
scoped syntax:max (name := sepExists) "∃ₛ " explicitBinders ", " term : term

scoped macro_rules
  | `(sepExists| ∃ₛ $xs:explicitBinders, $b:term) =>
      Lean.expandExplicitBinders ``SepLogic.ex xs b

@[app_unexpander SepLogic.ex] def unexpandEx : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃ₛ $ys:binderIdent*, $body) =>
      `(∃ₛ $x:ident $ys*, $body)
  | `($(_) fun $x:ident => $body) => `(∃ₛ $x:ident, $body)
  | `($(_) fun ($x:ident : $_) => ∃ₛ $ys:binderIdent*, $body) =>
      `(∃ₛ $x:ident $ys*, $body)
  | `($(_) fun ($x:ident : $_) => $body) => `(∃ₛ $x:ident, $body)
  | _ => throw ()

end SepLogic

namespace Sep.Xsimpl

initialize registerTraceClass `xsimpl

/-- Lemmas rewriting a concrete separation logic's constants into the
    `SepLogic` class operations. -/
register_simp_attr xsimpl_fold

/-- Lemmas rewriting the `SepLogic` class operations back into a concrete
    separation logic's constants. -/
register_simp_attr xsimpl_unfold_class

open SepLogic

section Lemmas

variable {α : Type u} [SepLogic α]

-- ============================================================
-- Helper lemmas for star AC reasoning
-- ============================================================

/-- `∗` is associative, so `ac_rfl` can normalise `∗`-trees. -/
instance : Std.Associative (α := α) SepLogic.star := ⟨star_assoc⟩

/-- `∗` is commutative, so `ac_rfl` can normalise `∗`-trees. -/
instance : Std.Commutative (α := α) SepLogic.star := ⟨star_comm⟩

theorem hstar_left_comm (H1 H2 H3 : α) :
    H1 ∗ (H2 ∗ H3) = H2 ∗ (H1 ∗ H3) := by
  rw [← star_assoc, star_comm H1 H2, star_assoc]

-- Used by MetaM to rewrite goal LHS or RHS
theorem himpl_lhs_eq {H1 H2 Hr : α} :
    H1 = H2 → (H2 ==> Hr) → (H1 ==> Hr) := by
  rintro rfl h; exact h

theorem himpl_rhs_eq {Hl H1 H2 : α} :
    H1 = H2 → (Hl ==> H1) → (Hl ==> H2) := by
  rintro rfl h; exact h

-- ============================================================
-- Extraction / instantiation helpers
-- ============================================================

theorem hstar_hexists_r {A : Sort v} (H : α) (J : A → α) :
    H ∗ ex J = ex (fun x => H ∗ J x) := by
  rw [star_comm, star_ex]; apply congrArg; funext x; rw [star_comm]

theorem himpl_hexists_l_star {A : Sort v} {J : A → α} {H1 H2 : α} :
    (∀ x, J x ∗ H1 ==> H2) → (ex J ∗ H1 ==> H2) := by
  intro h; rw [star_ex]; exact ex_l h

theorem himpl_hpure_l {P : Prop} {H : α} :
    (P → (emp : α) ==> H) → (⌜P⌝ ==> H) := by
  intro h
  rw [show (⌜P⌝ : α) = ⌜P⌝ ∗ emp from (star_emp_r _).symm]
  exact pure_l h

theorem himpl_hexists_r_star {A : Sort v} (x : A) {H1 H2 : α} {J : A → α} :
    (H1 ==> J x ∗ H2) → (H1 ==> ex J ∗ H2) := by
  intro h; rw [star_ex]; exact ex_r x h

theorem himpl_hpure_r {P : Prop} {H : α} :
    P → (H ==> (emp : α)) → (H ==> ⌜P⌝) := by
  intro hP hH
  rw [show (⌜P⌝ : α) = ⌜P⌝ ∗ emp from (star_emp_r _).symm]
  exact pure_r hP hH

-- ============================================================
-- Cancellation
-- ============================================================

theorem himpl_cancel_rhs {H1 H2 : α} :
    ((emp : α) ==> H2) → (H1 ==> H1 ∗ H2) := by
  intro h
  have hf : H1 ∗ emp ==> H1 ∗ H2 := frame_r h
  rw [star_emp_r] at hf
  exact hf

theorem himpl_cancel_lhs {H1 H2 : α} :
    (H2 ==> (emp : α)) → (H1 ∗ H2 ==> H1) := by
  intro h
  have hf : H1 ∗ H2 ==> H1 ∗ emp := frame_r h
  rw [star_emp_r] at hf
  exact hf

section Affine

variable {α : Type u} [AffineSepLogic α]

theorem sep_weaken_leftover {H1 H2 : α} :
    (H1 ∗ H2) ==> H1 :=
  himpl_cancel_lhs (AffineSepLogic.entails_emp H2)

end Affine

-- ============================================================
-- Wand cancellation
-- ============================================================

theorem himpl_wand_apply_lhs {H1 H2 Hl Hr : α} :
    (H2 ∗ Hl ==> Hr) → (H1 ∗ ((H1 -∗ H2) ∗ Hl) ==> Hr) := by
  intro h
  have h1 : H1 ∗ ((H1 -∗ H2) ∗ Hl) ==> H2 ∗ Hl := by
    rw [← star_assoc]
    exact frame_l (wand_cancel H1 H2)
  exact entails_trans h1 h

theorem himpl_wand_apply_lhs_emp {H1 H2 Hr : α} :
    (H2 ==> Hr) → (H1 ∗ (H1 -∗ H2) ==> Hr) :=
  fun h => entails_trans (wand_cancel H1 H2) h

end Lemmas

section PureLemmas

variable {α : Type u} [SepLogic.{u, 0} α]

/-- A pure conjunct is an existential over its proof. Only available when the
    logic's existentials range over `Prop` (i.e. at class universe `v = 0`). -/
theorem hstar_hpure_eq_hexists (P : Prop) (H : α) :
    ⌜P⌝ ∗ H = ex (fun _ : P => H) := by
  apply entails_antisym
  · exact pure_l fun hP => ex_r hP (entails_refl _)
  · exact ex_l fun hP => pure_r hP (entails_refl _)

theorem hstar_hpure_r_eq_hexists (H : α) (P : Prop) :
    H ∗ ⌜P⌝ = ex (fun _ : P => H) := by
  rw [star_comm, hstar_hpure_eq_hexists]

end PureLemmas

-- ============================================================
-- MetaM: star chain manipulation
-- ============================================================

/-- The ambient separation logic of a goal: its carrier, `SepLogic` instance and
    universe levels, read off the goal's `Entails` application. -/
structure SepCtx where
  levels : List Level
  carrier : Expr
  inst : Expr

/-- Recognise `SepLogic.Entails α inst H1 H2`. -/
def matchEntails? (e : Expr) : Option (SepCtx × Expr × Expr) :=
  match e.consumeMData with
  | .app (.app (.app (.app (.const n ls) carrier) inst) lhs) rhs =>
    if n == ``SepLogic.Entails then
      some ({ levels := ls, carrier, inst }, lhs, rhs)
    else none
  | _ => none

/-- Recognise `SepLogic.star α inst H1 H2`, returning the instance found there. -/
def matchStar? (e : Expr) : Option (SepCtx × Expr × Expr) :=
  match e.consumeMData with
  | .app (.app (.app (.app (.const n ls) carrier) inst) H1) H2 =>
    if n == ``SepLogic.star then
      some ({ levels := ls, carrier, inst }, H1, H2)
    else none
  | _ => none

def isEmp (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``SepLogic.emp

def isSpure (e : Expr) : Bool :=
  e.consumeMData.getAppFn.isConstOf ``SepLogic.spure

/-- Parse `H1 ∗ H2 ∗ ... ∗ emp` into `[H1, H2, ...]` (not including trailing `emp`). -/
partial def parseStar (e : Expr) : List Expr :=
  match matchStar? e with
  | some (_, H1, H2) => H1 :: parseStar H2
  | none => if isEmp e then [] else [e]

/-- Build `H1 ∗ H2 ∗ ...` from a list. -/
def buildStar (c : SepCtx) (items : List Expr) : MetaM Expr := do
  match items with
  | [] => mkAppOptM ``SepLogic.emp #[some c.carrier, some c.inst]
  | [x] => return x
  | _ =>
    let rec go (l : List Expr) : MetaM Expr := do
      match l with
      | [] => unreachable!
      | [y] => return y
      | y :: ys => mkAppOptM ``SepLogic.star #[some c.carrier, some c.inst, some y, some (← go ys)]
    go items

private def mkStar (c : SepCtx) (H1 H2 : Expr) : MetaM Expr :=
  mkAppOptM ``SepLogic.star #[some c.carrier, some c.inst, some H1, some H2]

/-- Move `atom` to the front of a star chain `tree`, returning `(newTree, proof : tree = newTree)`.
    `newTree` starts with `atom`. Fails if `atom` is not in the chain. -/
partial def starMoveToFront (_c : SepCtx) (atom : Expr) (tree : Expr) : MetaM (Expr × Expr) := do
  let tree := tree.consumeMData
  match matchStar? tree with
  | some (c1, H1, H2) =>
    if ← isDefEq atom H1 then
      return (tree, ← mkEqRefl tree)
    else
      -- Recursively move atom to front of H2 (the tail)
      let (newTail, tailProof) ← starMoveToFront c1 atom H2
      match matchStar? newTail with
      | some (_, atomExpr, H2rest) =>
        -- Build f = fun x => H1 ∗ x  (to apply congrArg)
        let ty ← inferType H1
        let f ← withLocalDecl `x .default ty fun xVar => do
          mkLambdaFVars #[xVar] (← mkStar c1 H1 xVar)
        -- step1 : H1 ∗ H2 = H1 ∗ (atom ∗ H2rest)
        let step1 ← mkCongrArg f tailProof
        -- leftComm : atom ∗ (H1 ∗ H2rest) = H1 ∗ (atom ∗ H2rest)
        let leftComm ← mkAppOptM ``Sep.Xsimpl.hstar_left_comm
          #[some c1.carrier, some c1.inst, some atomExpr, some H1, some H2rest]
        let step2 ← mkEqSymm leftComm
        let total ← mkEqTrans step1 step2
        let h1Rest ← mkStar c1 H1 H2rest
        let result ← mkStar c1 atomExpr h1Rest
        return (result, total)
      | none =>
        -- newTail is just the atom
        let ty ← inferType H1
        let f ← withLocalDecl `x .default ty fun xVar => do
          mkLambdaFVars #[xVar] (← mkStar c1 H1 xVar)
        let step1 ← mkCongrArg f tailProof
        let comm ← mkAppOptM ``SepLogic.star_comm
          #[some c1.carrier, some c1.inst, some H1, some newTail]
        let total ← mkEqTrans step1 comm
        let result ← mkStar c1 newTail H1
        return (result, total)
  | none =>
    if ← isDefEq atom tree then
      return (tree, ← mkEqRefl tree)
    else
      throwError "starMoveToFront: {← ppExpr atom} not found in chain {← ppExpr tree}"

/-- Rewrite the LHS of the current entailment goal to `newLhs`, given `lhs = newLhs`. -/
private def replaceLhs (goal : MVarId) (c : SepCtx) (newLhs rhs proof : Expr) : MetaM MVarId := do
  let newGoalType ← mkAppOptM ``SepLogic.Entails
    #[some c.carrier, some c.inst, some newLhs, some rhs]
  let newGoalMVar ← mkFreshExprMVar newGoalType
  goal.assign (← mkAppOptM ``Sep.Xsimpl.himpl_lhs_eq
    #[some c.carrier, some c.inst, none, none, none, some proof, some newGoalMVar])
  return newGoalMVar.mvarId!

-- ============================================================
-- Cancellation
-- ============================================================

/-- Try to cancel matching items between LHS and RHS of an entailment goal. -/
def xsimplCancelAllCore : TacticM Unit := withMainContext do
  let mut progress := false
  let mut cont := true
  while cont do
    cont := false
    let goals ← getUnsolvedGoals
    if goals.isEmpty then break
    let goal ← getMainGoal
    let goalType ← goal.getType >>= instantiateMVars
    let some (c, lhs, rhs) := matchEntails? goalType | break
    let rhsItems := parseStar rhs
    if rhsItems.isEmpty then break
    let lhsItems := parseStar lhs
    if lhsItems.isEmpty then break

    let mut found : Option Expr := none
    for r in [:rhsItems.length] do
      let rhsItem ← instantiateMVars rhsItems[r]!
      if rhsItem.isMVar then continue
      for l in [:lhsItems.length] do
        let lhsItem ← instantiateMVars lhsItems[l]!
        if lhsItem.isMVar then continue
        if ← isDefEq lhsItem rhsItem then
          found := some rhsItems[r]!
          break
      if found.isSome then break

    let some atom := found | break
    cont := true
    progress := true
    trace[xsimpl] m!"Cancelling {atom}"

    let (newLhs, lhsProof) ← starMoveToFront c atom lhs
    let (newRhs, rhsProof) ← starMoveToFront c atom rhs

    let newGoalType ← mkAppOptM ``SepLogic.Entails
      #[some c.carrier, some c.inst, some newLhs, some newRhs]
    let newGoalMVar ← mkFreshExprMVar newGoalType

    -- goal : lhs ==> rhs, via (newLhs ==> rhs) via (newLhs ==> newRhs)
    let goalType1 ← mkAppOptM ``SepLogic.Entails
      #[some c.carrier, some c.inst, some newLhs, some rhs]
    let goalMVar1 ← mkFreshExprMVar goalType1
    let assignProof1 ← mkAppOptM ``Sep.Xsimpl.himpl_lhs_eq
      #[some c.carrier, some c.inst, none, none, none, some lhsProof, some goalMVar1]
    let rhsProofSymm ← mkEqSymm rhsProof
    let assignProof2 ← mkAppOptM ``Sep.Xsimpl.himpl_rhs_eq
      #[some c.carrier, some c.inst, none, none, none, some rhsProofSymm, some newGoalMVar]

    goal.assign assignProof1
    goalMVar1.mvarId!.assign assignProof2

    replaceMainGoal [newGoalMVar.mvarId!]

    let newLhsIsStar := (matchStar? newLhs).isSome
    let newRhsIsStar := (matchStar? newRhs).isSome

    if newLhsIsStar && newRhsIsStar then
      evalTactic (← `(tactic| apply SepLogic.frame_r))
    else if newLhsIsStar && not newRhsIsStar then
      evalTactic (← `(tactic| apply Sep.Xsimpl.himpl_cancel_lhs))
    else if not newLhsIsStar && newRhsIsStar then
      evalTactic (← `(tactic| apply Sep.Xsimpl.himpl_cancel_rhs))
    else
      evalTactic (← `(tactic| apply SepLogic.entails_refl))
  if not progress then
    throwError "xsimpl_cancel_all: no items to cancel"

elab "xsimpl_cancel_all_core" : tactic => xsimplCancelAllCore

def xsimplCancelWandCore : TacticM Unit := withMainContext do
  let mut progress := false
  let mut cont := true
  while cont do
    cont := false
    let goals ← getUnsolvedGoals
    if goals.isEmpty then break
    let goal ← getMainGoal
    let goalType ← goal.getType >>= instantiateMVars
    let some (c, lhs, rhs) := matchEntails? goalType | break
    let lhsItems := parseStar lhs
    if lhsItems.isEmpty then break

    -- Find an (H1 -∗ H2) and an H1 matching its premise
    let mut found : Option (Expr × Expr) := none
    for l in [:lhsItems.length] do
      let itemWand := lhsItems[l]!.consumeMData
      let (ifn, iargs) := itemWand.getAppFnArgs
      if ifn == ``SepLogic.wand && iargs.size == 4 then
        let wandLhs := iargs[2]!
        for l2 in [:lhsItems.length] do
          if l != l2 then
            let itemPremise := lhsItems[l2]!
            if ← isDefEq wandLhs itemPremise then
              found := some (itemPremise, itemWand)
              break
        if found.isSome then break

    let some (premise, wand) := found | break
    cont := true
    progress := true

    -- Move wand to front, then premise to front so we get `premise ∗ wand`
    let (newLhs1, lhsProof1) ← starMoveToFront c wand lhs
    let (newLhs2, lhsProof2) ← starMoveToFront c premise newLhs1
    let transProof ← mkEqTrans lhsProof1 lhsProof2

    let newGoal ← replaceLhs goal c newLhs2 rhs transProof
    replaceMainGoal [newGoal]

    if (matchStar? newLhs2).isSome then
      evalTactic (← `(tactic| (
        first
        | apply Sep.Xsimpl.himpl_wand_apply_lhs
        | apply Sep.Xsimpl.himpl_wand_apply_lhs_emp
      )))
    else
      evalTactic (← `(tactic| apply Sep.Xsimpl.himpl_wand_apply_lhs_emp))
  if not progress then
    throwError "xsimpl_cancel_wand: no wands to cancel"

elab "xsimpl_cancel_wand_core" : tactic => xsimplCancelWandCore

-- ============================================================
-- Folding / unfolding the class operations
-- ============================================================

/-- The `rfl`-lemmas tagged with a simp attribute, as `(lhs head, name)` pairs. -/
def taggedLemmas (attr : Name) : MetaM (Array Name) := do
  let some ext ← getSimpExtension? attr | throwError "unknown simp attribute {attr}"
  let thms ← ext.getTheorems
  return thms.lemmaNames.fold (init := #[]) fun acc o =>
    match o with
    | .decl n _ _ => acc.push n
    | _ => acc

/-- Rewrite `e` with the `rfl`-lemmas tagged `attr`, oriented left to right.
    Unlike `simp only`, this survives lemmas whose two sides are definitionally
    equal, which is exactly the case for the fold/unfold bridge. -/
private partial def lemmaLhsHead? (ty : Expr) : Option Name :=
  match ty with
  | .forallE _ _ b _ => lemmaLhsHead? b
  | e =>
    match e.eq? with
    | some (_, lhs, _) =>
      let fn := lhs.getAppFn
      if fn.isConst then some fn.constName! else none
    | none => none

def rewriteWithRfl (lemmas : Array Name) (e : Expr) : MetaM Expr := do
  let mut byHead : NameMap (Array Name) := {}
  for n in lemmas do
    let cinfo ← getConstInfo n
    if let some h := lemmaLhsHead? cinfo.type then
      byHead := byHead.insert h (((byHead.find? h).getD #[]).push n)
  Meta.transform e (post := fun sub => do
    let fn := sub.getAppFn
    unless fn.isConst do return .continue
    let some cands := byHead.find? fn.constName! | return .continue
    for n in cands do
      let cinfo ← getConstInfo n
      let lvls ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
      let ty := cinfo.type.instantiateLevelParams cinfo.levelParams lvls
      let (_, _, concl) ← forallMetaTelescope ty
      let some (_, lhs, rhs) := concl.eq? | continue
      -- Match with the lemma's pattern on the *left*, so that when both sides
      -- are metavariables it is the lemma's own metavariable that gets
      -- assigned, never the goal's (frame/antiframe metavariables owned by the
      -- caller must survive folding and unfolding untouched).
      if ← isDefEq lhs sub then
        return .done (← instantiateMVars rhs)
    return .continue)

/-- Force every `SepLogic` operation in `e` to mention the same instance, by
    unifying the universe levels of all class-projection occurrences. Returns
    `false` if they cannot be reconciled (e.g. existentials at two universes). -/
partial def unifyClassLevels (e : Expr) : MetaM Bool := do
  let mut ref : Option (List Level) := none
  let mut ok := true
  for c in collectConsts e do
    let (n, ls) := c
    unless isClassOp n do continue
    match ref with
    | none => ref := some ls
    | some ls0 =>
      if ls0.length == ls.length then
        for (l1, l2) in ls0.zip ls do
          unless ← isLevelDefEq l1 l2 do ok := false
  -- default any level still undetermined
  match ref with
  | none => pure ()
  | some ls0 => for l in ls0 do
      if l.hasMVar then
        _ ← isLevelDefEq l levelZero
  return ok
where
  isClassOp (n : Name) : Bool :=
    n == ``SepLogic.star || n == ``SepLogic.emp || n == ``SepLogic.spure ||
    n == ``SepLogic.ex || n == ``SepLogic.wand || n == ``SepLogic.Entails
  collectConsts (e : Expr) : Array (Name × List Level) := goCollect e #[]
  goCollect (e : Expr) (acc : Array (Name × List Level)) : Array (Name × List Level) :=
    match e with
    | .const n ls => acc.push (n, ls)
    | .app f a => goCollect a (goCollect f acc)
    | .lam _ t b _ => goCollect b (goCollect t acc)
    | .forallE _ t b _ => goCollect b (goCollect t acc)
    | .letE _ t v b _ => goCollect b (goCollect v (goCollect t acc))
    | .mdata _ b => goCollect b acc
    | .proj _ _ b => goCollect b acc
    | _ => acc

/-- Is `n` one of the `SepLogic` operation projections? -/
def isClassOpName (n : Name) : Bool :=
  n == ``SepLogic.star || n == ``SepLogic.emp || n == ``SepLogic.spure ||
  n == ``SepLogic.ex || n == ``SepLogic.wand || n == ``SepLogic.Entails

partial def replaceInstances (ref : List Level) (inst : Expr) (e : Expr) : Expr :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs.map (replaceInstances ref inst)
    match fn with
    | .const n _ =>
      if isClassOpName n && args.size ≥ 2 then
        mkAppN (mkConst n ref) (args.set! 1 inst)
      else mkAppN fn args
    | _ => mkAppN (replaceInstances ref inst fn) args
  | .lam nm t b bi => .lam nm (replaceInstances ref inst t) (replaceInstances ref inst b) bi
  | .forallE nm t b bi =>
    .forallE nm (replaceInstances ref inst t) (replaceInstances ref inst b) bi
  | .letE nm t v b nd =>
    .letE nm (replaceInstances ref inst t) (replaceInstances ref inst v)
      (replaceInstances ref inst b) nd
  | .mdata d b => .mdata d (replaceInstances ref inst b)
  | .proj s i b => .proj s i (replaceInstances ref inst b)
  | _ => e


/-- Make every `SepLogic` operation in `e` mention one and the same instance.
    Goals written directly with the class notation synthesize an instance per
    occurrence, and those can sit at different universes, which stops the class
    lemmas from applying. Returns `none` if no single instance fits (e.g. two
    existentials at different universes). -/
def uniformizeInstances (e : Expr) : MetaM (Option Expr) := do
  let occs := classOpOccurrences e
  if occs.isEmpty then return none
  let exLevels := occs.filterMap fun occ => if occ.1 == ``SepLogic.ex then some occ.2 else none
  if h : 0 < exLevels.size then
    for ls in exLevels do
      unless ls == exLevels[0] do return none
  let ref := if h : 0 < exLevels.size then exLevels[0] else occs[0]!.2
  -- the carrier is the first explicit argument of any occurrence
  let some carrier := carrierOf? e | return none
  let instTy := mkAppN (mkConst ``SepLogic ref) #[carrier]
  match ← trySynthInstance instTy with
  | .some inst => return some (replaceInstances ref inst e)
  | _ => return none
where
  isClassOp (n : Name) : Bool := isClassOpName n
  classOpOccurrences (e : Expr) : Array (Name × List Level) := Id.run do
    let mut acc := #[]
    for sub in subterms e do
      match sub.getAppFn with
      | .const n ls => if isClassOp n && sub.getAppNumArgs ≥ 2 then acc := acc.push (n, ls)
      | _ => pure ()
    return acc
  carrierOf? (e : Expr) : Option Expr := Id.run do
    for sub in subterms e do
      match sub.getAppFn with
      | .const n _ =>
        if isClassOp n && sub.getAppNumArgs ≥ 2 then return some sub.getAppArgs[0]!
      | _ => pure ()
    return none
  subterms (e : Expr) : Array Expr := go e #[]
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := acc.push e
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ => go b (go t acc)
    | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc

/-- Rewrite the goal with the lemmas tagged `attr`, make its `SepLogic`
    instances uniform, and `change` to the result. -/
def changeWithRfl (attr : Name) (uniformize : Bool) : TacticM Unit := withMainContext do
  let lemmas ← taggedLemmas attr
  let goal ← getMainGoal
  let target ← goal.getType >>= instantiateMVars
  let mut target1 ← rewriteWithRfl lemmas target
  if target1 != target then
    unless ← unifyClassLevels target1 do return
    target1 ← instantiateMVars target1
  if uniformize then
    if let some target2 ← uniformizeInstances target1 then
      if ← isDefEq target1 target2 then
        target1 := target2
  if target1 == target then return
  replaceMainGoal [← goal.change target1]

elab "xsimpl_fold_goal" : tactic => changeWithRfl `xsimpl_fold true
elab "xsimpl_unfold_goal" : tactic => changeWithRfl `xsimpl_unfold_class false

-- ============================================================
-- Tactic phases
-- ============================================================

/-- Run `t` on the class-folded goal, restoring the concrete logic's own
    notation on whatever goals remain. This keeps every goal a client ever sees
    (residual goals, and the goals handed to a user-supplied extension tactic)
    stated in the client's own constants. -/
syntax "xsimpl_in_class " tacticSeq : tactic
macro_rules
  | `(tactic| xsimpl_in_class $t) => `(tactic| (
      try xsimpl_fold_goal
      ($t)
      all_goals (try xsimpl_unfold_goal)
    ))

syntax "xsimpl_normalize" : tactic
macro_rules
  | `(tactic| xsimpl_normalize) => `(tactic| (
      try xsimpl_in_class (simp only [
        SepLogic.star_emp_l, SepLogic.star_emp_r, SepLogic.star_assoc,
        SepLogic.wand_curry,
        SepLogic.star_ex, Sep.Xsimpl.hstar_hexists_r,
        Sep.Xsimpl.hstar_hpure_eq_hexists, Sep.Xsimpl.hstar_hpure_r_eq_hexists
      ])
    ))

def hasExHead (items : List Expr) : Bool :=
  items.any fun i =>
    let fn := i.consumeMData.getAppFn
    fn.isConstOf ``SepLogic.ex || fn.isConstOf ``SepLogic.spure

private def movePureToFront (onLhs : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) := matchEntails? goalType | throwError "not an entailment"
  let side := if onLhs then lhs else rhs
  let items := parseStar side
  if items.length ≤ 1 then throwError "no pure conjunct to move"
  if isSpure items[0]! then throwError "pure conjunct already at the front"
  let some pureItem := items.find? isSpure | throwError "no pure conjunct to move"
  let (newSide, proof) ← starMoveToFront c pureItem side
  if onLhs then
    replaceMainGoal [← replaceLhs goal c newSide rhs proof]
  else
    let newGoalType ← mkAppOptM ``SepLogic.Entails
      #[some c.carrier, some c.inst, some lhs, some newSide]
    let newGoalMVar ← mkFreshExprMVar newGoalType
    goal.assign (← mkAppOptM ``Sep.Xsimpl.himpl_rhs_eq
      #[some c.carrier, some c.inst, none, none, none, some (← mkEqSymm proof),
        some newGoalMVar])
    replaceMainGoal [newGoalMVar.mvarId!]

elab "xsimpl_pure_front_lhs" : tactic => movePureToFront true
elab "xsimpl_pure_front_rhs" : tactic => movePureToFront false

def xsimplInstantiateStepCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (_, _, rhs) := matchEntails? goalType | throwError "not an entailment"

  -- If RHS is an MVar, applying ex_r will infinite loop by unifying it with ex
  let rhsItems := parseStar rhs
  for item in rhsItems do
    if item.isMVar then throwError "RHS contains MVar, skipping instantiate to prevent looping"
  unless hasExHead rhsItems do throwError "RHS has no existential"

  evalTactic (← `(tactic| (
    first
    | apply Sep.Xsimpl.himpl_hexists_r_star
    | apply SepLogic.ex_r
    | apply SepLogic.pure_r
    | apply Sep.Xsimpl.himpl_hpure_r
    | (xsimpl_pure_front_rhs; apply SepLogic.pure_r)
  )))

elab "xsimpl_instantiate_step_core" : tactic => xsimplInstantiateStepCore

def xsimplExtractStepCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (_, lhs, _) := matchEntails? goalType | throwError "not an entailment"

  let lhsItems := parseStar lhs
  for item in lhsItems do
    if item.isMVar then
      throwError "LHS contains MVar, skipping extract to prevent looping"
  unless hasExHead lhsItems do throwError "LHS has no existential"

  evalTactic (← `(tactic| (
    first
    | (apply Sep.Xsimpl.himpl_hexists_l_star; intro)
    | (apply SepLogic.ex_l; intro)
    | (apply SepLogic.pure_l; intro)
    | (apply Sep.Xsimpl.himpl_hpure_l; intro)
    | (xsimpl_pure_front_lhs; apply SepLogic.pure_l; intro)
  )))

elab "xsimpl_extract_step_core" : tactic => xsimplExtractStepCore

/-- Recognise `SepLogic.wand α inst H1 H2`. -/
def matchWand? (e : Expr) : Option (Expr × Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``SepLogic.wand, #[_, _, H1, H2]) => some (H1, H2)
  | _ => none

/-- **Wand introduction** (the adjunction, hence safe and invertible).
    Fires only when the whole RHS is a wand, i.e. the RHS star chain has a single
    remaining item and that item is `P1 -∗ P2`: then `H ==> P1 -∗ P2` becomes
    `H ∗ P1 ==> P2`. It cannot loop, since each step strips one wand. -/
def xsimplWandIntroCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (_, _, rhs) := matchEntails? goalType | throwError "not an entailment"
  let rhsItems := parseStar rhs
  let [item] := rhsItems | throwError "RHS is not a single wand"
  if item.isMVar then throwError "RHS is a metavariable"
  let some _ := matchWand? item | throwError "RHS is not a wand"
  evalTactic (← `(tactic| apply SepLogic.wand_intro))

elab "xsimpl_wand_intro_core" : tactic => xsimplWandIntroCore

def affineInst? (carrier : Expr) : MetaM (Option Expr) := do
  let info ← getConstInfo ``AffineSepLogic
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  Lean.Meta.synthInstance? (mkAppN (mkConst ``AffineSepLogic lvls) #[carrier])

def xsimplAffineEmpCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, _, rhs) := matchEntails? goalType | throwError "not an entailment"
  let rhs ← whnfR rhs
  let some _ ← affineInst? c.carrier | throwError "carrier is not affine"
  unless rhs.getAppFn.isConstOf ``SepLogic.emp do
    let e ← mkAppOptM ``SepLogic.emp #[some c.carrier, some c.inst]
    unless ← Lean.Meta.isDefEq rhs e do throwError "RHS is not emp"
  evalTactic (← `(tactic| exact AffineSepLogic.entails_emp _))

elab "xsimpl_affine_emp_core" : tactic => xsimplAffineEmpCore

elab "xsimpl_clean_refl_core" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  if (matchEntails? goalType).isSome then
    evalTactic (← `(tactic| apply SepLogic.entails_refl))
  else
    throwError "Not an entailment goal"


-- Each public step folds the goal into class form, runs, and restores the
-- concrete logic's constants on the goals it leaves behind.

syntax "xsimpl_cancel_all" : tactic
macro_rules
  | `(tactic| xsimpl_cancel_all) => `(tactic| xsimpl_in_class xsimpl_cancel_all_core)

syntax "xsimpl_cancel_wand" : tactic
macro_rules
  | `(tactic| xsimpl_cancel_wand) => `(tactic| xsimpl_in_class xsimpl_cancel_wand_core)

syntax "xsimpl_instantiate_step" : tactic
macro_rules
  | `(tactic| xsimpl_instantiate_step) =>
      `(tactic| xsimpl_in_class xsimpl_instantiate_step_core)

syntax "xsimpl_extract_step" : tactic
macro_rules
  | `(tactic| xsimpl_extract_step) => `(tactic| xsimpl_in_class xsimpl_extract_step_core)

syntax "xsimpl_wand_intro" : tactic
macro_rules
  | `(tactic| xsimpl_wand_intro) => `(tactic| xsimpl_in_class xsimpl_wand_intro_core)

syntax "xsimpl_clean_refl" : tactic
macro_rules
  | `(tactic| xsimpl_clean_refl) => `(tactic| xsimpl_in_class xsimpl_clean_refl_core)

syntax "xsimpl_affine_emp" : tactic
macro_rules
  | `(tactic| xsimpl_affine_emp) => `(tactic| xsimpl_in_class xsimpl_affine_emp_core)

syntax "xsimpl_close_goal" : tactic
macro_rules
  | `(tactic| xsimpl_close_goal) => `(tactic| (
      first
      | xsimpl_clean_refl
      | assumption
      | xsimpl_affine_emp
    ))

/-- Run `t`, and fail unless it changed the goals.  `xsimpl_core` drives its
steps with `repeat`, which stops only on failure, so a step that succeeds without
progress would not terminate. -/
def withProgress (t : TacticM Unit) : TacticM Unit := do
  let before ← (← getGoals).mapM fun g => do instantiateMVars (← g.getType)
  t
  let after ← (← getGoals).mapM fun g => do instantiateMVars (← g.getType)
  if before.length == after.length && (before.zip after).all (fun (x, y) => x == y) then
    throwError "xsimpl: step made no progress"

syntax "xsimpl_with_progress " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| xsimpl_with_progress $t) => withProgress (evalTactic t)

/-- One rewriting step. -/
syntax "xsimpl_step" : tactic
macro_rules
  | `(tactic| xsimpl_step) => `(tactic| (
      xsimpl_with_progress (xsimpl_in_class (
        first
        | xsimpl_cancel_all_core
        | xsimpl_extract_step_core
        | xsimpl_wand_intro_core
        | xsimpl_instantiate_step_core
        | xsimpl_cancel_wand_core
      ))
    ))

def xsimplStepFolded : TacticM Bool := do
  if ← tryTactic (withProgress xsimplCancelAllCore) then return true
  if ← tryTactic (withProgress xsimplExtractStepCore) then return true
  if ← tryTactic (withProgress xsimplWandIntroCore) then return true
  if ← tryTactic (withProgress xsimplInstantiateStepCore) then return true
  if ← tryTactic (withProgress xsimplCancelWandCore) then return true
  return false

def needsRelevel (goalType : Expr) : Bool :=
  match matchEntails? goalType with
  | some ({ levels := [_, v], .. }, _, _) =>
    !v.isZero && !v.hasMVar &&
      (goalType.find? (fun e => e.getAppFn.isConstOf ``SepLogic.spure)).isSome
  | _ => false

def xsimplRelevelGoals : TacticM Unit := do
  let gs ← getUnsolvedGoals
  let mut bad := false
  for g in gs do
    if needsRelevel (← instantiateMVars (← g.getType)) then bad := true
  if bad then
    evalTactic (← `(tactic| all_goals ((try xsimpl_unfold_goal); (try xsimpl_fold_goal))))

def xsimplDriver (extra : TSyntax ``Lean.Parser.Tactic.tacticSeq) : TacticM Unit := do
  let normalize ← `(tactic| all_goals (try (simp only [
    SepLogic.star_emp_l, SepLogic.star_emp_r, SepLogic.star_assoc,
    SepLogic.wand_curry,
    SepLogic.star_ex, Sep.Xsimpl.hstar_hexists_r,
    Sep.Xsimpl.hstar_hpure_eq_hexists, Sep.Xsimpl.hstar_hpure_r_eq_hexists
  ])))
  let extraTac ← `(tactic|
    ((try xsimpl_unfold_goal); ($extra); all_goals (try xsimpl_fold_goal)))
  evalTactic (← `(tactic| all_goals (try xsimpl_fold_goal)))
  xsimplRelevelGoals
  evalTactic normalize
  let mut progress := true
  while progress do
    progress := false
    let gs ← getUnsolvedGoals
    let mut acc : List MVarId := []
    for g in gs do
      if ← g.isAssigned then continue
      setGoals [g]
      let ok ← do
        if ← xsimplStepFolded then pure true
        else tryTactic (evalTactic extraTac)
      if ok then
        progress := true
        xsimplRelevelGoals
        evalTactic normalize
      acc := acc ++ (← getUnsolvedGoals)
    setGoals acc
  evalTactic (← `(tactic| all_goals (try xsimpl_unfold_goal)))

syntax "xsimpl_core_with " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| xsimpl_core_with $extra) => xsimplDriver extra

syntax "xsimpl_core" : tactic
macro_rules
  | `(tactic| xsimpl_core) => `(tactic| (
      xsimpl_core_with fail
    ))

syntax "xsimpl_clean" : tactic
macro_rules
  | `(tactic| xsimpl_clean) => `(tactic| (
      try xsimpl_clean_refl
      try assumption
      try xsimpl_affine_emp
    ))

syntax "xsimpl" : tactic
macro_rules
  | `(tactic| xsimpl) => `(tactic| (
      xsimpl_core
      all_goals (
        try xsimpl_clean
      )
    ))

end Sep.Xsimpl
