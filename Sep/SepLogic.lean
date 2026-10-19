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

initialize cheapCancel : IO.Ref Bool ← IO.mkRef false

def withCheapCancel {α : Type} (x : TacticM α) : TacticM α := do
  let old ← cheapCancel.get
  cheapCancel.set true
  try x finally cheapCancel.set old

def cheapDefEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if !(← cheapCancel.get) || a.hasMVar || b.hasMVar then isDefEq a b
  else withReducible (isDefEq a b)

def headMayMatch (h t : Expr) : MetaM Bool := do
  if h.hasMVar || t.hasMVar then return true
  let .const c2 _ := t.getAppFn | return true
  if ← isReducible c2 then return true
  let h' ← whnfR h
  match h'.getAppFn with
  | .const c1 _ => return c1 == c2
  | .fvar _ => return true
  | .mvar _ => return true
  | _ => return false

def cheapAssumptionCore (g : MVarId) : MetaM Bool := do
  unless ← cheapCancel.get do return ← g.assumptionCore
  let t ← instantiateMVars (← g.getType)
  let r ← (← getLCtx).findDeclRevM? fun d => do
    if d.isImplementationDetail then return none
    unless ← headMayMatch d.type t do return none
    if ← cheapDefEq d.type t then return some d.toExpr else return none
  match r with
  | some e => g.assign e; return true
  | none => return false

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

section NativeLemmas

theorem nt_trans.{w, z} {α : Type w} [SepLogic.{w, z} α] {a b c : α}
    (h1 : a ==> b) (h2 : b ==> c) : a ==> c :=
  entails_trans h1 h2

theorem nt_refl.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) : a ==> a :=
  entails_refl a

theorem nt_of_eq.{w, z} {α : Type w} [SepLogic.{w, z} α] {a b : α} (h : a = b) :
    a ==> b := by
  subst h; exact entails_refl _

theorem nt_frame.{w, z} {α : Type w} [SepLogic.{w, z} α] (c : α) {a b : α}
    (h : a ==> b) : c ∗ a ==> c ∗ b :=
  frame_r h

theorem nt_comm.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b : α) :
    a ∗ b ==> b ∗ a := by
  rw [star_comm]; exact entails_refl _

theorem nt_swap.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    a ∗ (b ∗ c) ==> b ∗ (a ∗ c) := by
  rw [hstar_left_comm]; exact entails_refl _

theorem nt_cancel_r.{w, z} {α : Type w} [SepLogic.{w, z} α] (c : α) {q : α}
    (h : (emp : α) ==> q) : c ==> c ∗ q :=
  himpl_cancel_rhs h

theorem nt_cancel_l.{w, z} {α : Type w} [SepLogic.{w, z} α] (c : α) {q : α}
    (h : q ==> (emp : α)) : c ∗ q ==> c :=
  himpl_cancel_lhs h

theorem nt_assoc.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    (a ∗ b) ∗ c = a ∗ (b ∗ c) :=
  star_assoc a b c

theorem nt_pushl.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    a ∗ (b ∗ c) ==> (b ∗ a) ∗ c :=
  nt_trans (nt_swap a b c) (nt_of_eq (nt_assoc b a c).symm)

theorem nt_empl.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) : emp ∗ a = a :=
  star_emp_l a

theorem nt_empr.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) : a ∗ emp = a :=
  star_emp_r a

theorem nt_exl_base.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (J : A → α)
    (q : α) : ex J ∗ q ==> ex (fun x => J x ∗ q) := by
  rw [star_ex]; exact entails_refl _

theorem nt_exl_layer.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} {K : A → α}
    {x : α} (s : α) (h : x ==> ex K) : s ∗ x ==> ex (fun y => s ∗ K y) :=
  entails_trans (frame_r h) (by rw [hstar_hexists_r]; exact entails_refl _)

theorem nt_exr_base.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (J : A → α)
    (q : α) : ex (fun x => J x ∗ q) ==> ex J ∗ q := by
  rw [star_ex]; exact entails_refl _

theorem nt_exr_layer.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} {K : A → α}
    {x : α} (s : α) (h : ex K ==> x) : ex (fun y => s ∗ K y) ==> s ∗ x :=
  entails_trans (by rw [← hstar_hexists_r]; exact entails_refl _) (frame_r h)

theorem nt_exl.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} {J : A → α} {r : α}
    (k : ∀ x, J x ==> r) : ex J ==> r :=
  ex_l k

theorem nt_exr.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (x : A) {J : A → α}
    {l : α} (h : l ==> J x) : l ==> ex J :=
  ex_r x h

theorem nt_purel.{w, z} {α : Type w} [SepLogic.{w, z} α] {P : Prop} {q r : α}
    (k : P → q ==> r) : ⌜P⌝ ∗ q ==> r :=
  pure_l k

theorem nt_purel1.{w, z} {α : Type w} [SepLogic.{w, z} α] {P : Prop} {r : α}
    (k : P → (emp : α) ==> r) : ⌜P⌝ ==> r :=
  himpl_hpure_l k

theorem nt_purer.{w, z} {α : Type w} [SepLogic.{w, z} α] {P : Prop} {l q : α}
    (p : P) (h : l ==> q) : l ==> ⌜P⌝ ∗ q :=
  pure_r p h

theorem nt_purer1.{w, z} {α : Type w} [SepLogic.{w, z} α] {P : Prop} {l : α}
    (p : P) (h : l ==> (emp : α)) : l ==> ⌜P⌝ :=
  himpl_hpure_r p h

theorem nt_eq_exl.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (J : A → α) (q : α) :
    ex J ∗ q = ex (fun x => J x ∗ q) :=
  star_ex J q

theorem nt_eq_exr.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (q : α) (J : A → α) :
    q ∗ ex J = ex (fun x => q ∗ J x) :=
  hstar_hexists_r q J

theorem nt_curry.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    (a ∗ b) -∗ c = a -∗ (b -∗ c) :=
  wand_curry a b c

theorem nt_wand_l.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b : α) {l r : α}
    (h : b ∗ l ==> r) : a ∗ ((a -∗ b) ∗ l) ==> r :=
  himpl_wand_apply_lhs h

theorem nt_wand_l1.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b : α) {r : α}
    (h : b ==> r) : a ∗ (a -∗ b) ==> r :=
  himpl_wand_apply_lhs_emp h

theorem nt_wand_r.{w, z} {α : Type w} [SepLogic.{w, z} α] {l a b : α}
    (h : l ∗ a ==> b) : l ==> a -∗ b :=
  wand_intro h

theorem nt_wand_same.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) {l r : α}
    (h : l ==> r) : l ==> (a -∗ a) ∗ r :=
  entails_trans h (entails_trans (nt_of_eq (star_emp_l r).symm)
    (frame_l (wand_intro (nt_of_eq (star_emp_l a)))))

theorem nt_wand_same1.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) {l : α}
    (h : l ==> emp) : l ==> a -∗ a :=
  entails_trans h (wand_intro (nt_of_eq (star_emp_l a)))

end NativeLemmas

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

private def mkStar (c : SepCtx) (H1 H2 : Expr) : MetaM Expr :=
  mkAppOptM ``SepLogic.star #[some c.carrier, some c.inst, some H1, some H2]

/-- Move `atom` to the front of a star chain `tree`, returning `(newTree, proof : tree = newTree)`.
    `newTree` starts with `atom`. Fails if `atom` is not in the chain. -/
partial def starMoveToFront (_c : SepCtx) (atom : Expr) (tree : Expr) : MetaM (Expr × Expr) := do
  let tree := tree.consumeMData
  match matchStar? tree with
  | some (c1, H1, H2) =>
    if ← cheapDefEq atom H1 then
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
    if ← cheapDefEq atom tree then
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
        if ← cheapDefEq lhsItem rhsItem then
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
            if ← cheapDefEq wandLhs itemPremise then
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

structure NOp where
  name : Name
  arity : Nat
  pos : Array Nat
  deriving Inhabited, BEq

def classOpOperands (n : Name) : Option (Array Nat) :=
  if n == ``SepLogic.star || n == ``SepLogic.wand || n == ``SepLogic.Entails then some #[2, 3]
  else if n == ``SepLogic.emp then some #[]
  else if n == ``SepLogic.spure then some #[2]
  else if n == ``SepLogic.ex then some #[2, 3]
  else none

def foldEntry (n : Name) : MetaM (Option (Name × NOp)) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun _ body => do
    let some (_, lhs, rhs) := body.eq? | return none
    let .const cn _ := rhs.getAppFn | return none
    let some idx := classOpOperands cn | return none
    let .const ln _ := lhs.getAppFn | return none
    if isClassOpName ln then return none
    let rargs := rhs.getAppArgs
    let largs := lhs.getAppArgs
    let mut pos := #[]
    for i in idx do
      let some a := rargs[i]? | return none
      unless a.isFVar do return none
      let some j := largs.findIdx? (· == a) | return none
      pos := pos.push j
    return some (cn, { name := ln, arity := largs.size, pos })

initialize foldEntryCache : IO.Ref (Array Name × Array (Name × NOp × Name)) ←
  IO.mkRef (#[], #[])

def foldEntries : MetaM (Array (Name × NOp × Name)) := do
  let names ← taggedLemmas `xsimpl_fold
  let (k, v) ← foldEntryCache.get
  if k == names then return v
  let mut out := #[]
  for n in names do
    if let some (cn, op) ← foldEntry n then out := out.push (cn, op, n)
  foldEntryCache.set (names, out)
  return out

structure NCtx where
  carrier : Expr
  u : Level
  entOp : NOp
  starOp : NOp
  empOp : NOp
  pureOp : NOp
  exOp : NOp
  wandOp : Option NOp
  starFn : Expr
  starArgs : Array Expr
  empE : Expr
  entFn : Expr
  entArgs : Array Expr
  lv0 : Level
  inst0 : Expr
  deriving Inhabited

initialize nctxCache :
    IO.Ref (Name × Array (Name × NOp × Name) × Array (Expr × Option NCtx)) ←
  IO.mkRef (.anonymous, #[], #[])

initialize ninstCache : IO.Ref (Name × Array (Expr × Level × Option Expr)) ←
  IO.mkRef (.anonymous, #[])

def sepInstAt (carrier : Expr) (u lv : Level) : MetaM (Option Expr) := do
  let m := (← getEnv).mainModule
  let (m0, cache) ← ninstCache.get
  let cache := if m0 == m then cache else #[]
  match cache.find? (fun e => e.1 == carrier && e.2.1 == lv) with
  | some (_, _, r) => return r
  | none =>
    let r ← try synthInstance? (mkApp (mkConst ``SepLogic [u, lv]) carrier) catch _ => pure none
    let r ← r.mapM instantiateMVars
    let r := r.filter (!·.hasMVar)
    ninstCache.set (m, cache.push (carrier, lv, r))
    return r

def foldTemplate (lem : Name) (carrier : Expr) (op : NOp) (byOperand : Bool) :
    MetaM (Option (Expr × Array Expr)) := withNewMCtxDepth do
  let ci ← getConstInfo lem
  let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  let ty := ci.type.instantiateLevelParams ci.levelParams lvls
  let (_, _, body) ← forallMetaTelescope ty
  let some (_, lhs, _) := body.eq? | return none
  let largs := lhs.getAppArgs
  let probe ← if byOperand then
      match op.pos[0]? >>= (largs[·]?) with
      | some a => inferType a
      | none => return none
    else inferType lhs
  unless ← isDefEq probe carrier do return none
  let fn ← instantiateMVars lhs.getAppFn
  let mut args := #[]
  for i in [0 : largs.size] do
    if op.pos.contains i then args := args.push (mkSort levelZero)
    else
      let a ← instantiateMVars largs[i]!
      if a.hasMVar then return none
      args := args.push a
  if fn.hasMVar then return none
  return some (fn, args)

def buildNCtx (entries : Array (Name × NOp × Name)) (carrier : Expr) (ent : NOp) :
    MetaM (Option NCtx) := do
  let some u ← (try some <$> getDecLevel carrier catch _ => pure none) | return none
  if u.hasMVar then return none
  let pick (cn : Name) (byOperand : Bool) : MetaM (Option (NOp × Expr × Array Expr)) := do
    for (c, op, lem) in entries do
      if c == cn then
        if let some (fn, args) ← foldTemplate lem carrier op byOperand then
          return some (op, fn, args)
    return none
  let some (starOp, starFn, starArgs) ← pick ``SepLogic.star false | return none
  let some (empOp, empFn, empArgs) ← pick ``SepLogic.emp false | return none
  let some (entOp, entFn, entArgs) ← pick ``SepLogic.Entails true | return none
  unless entOp == ent do return none
  let some pureOp := entries.findSome? (fun (c, op, _) =>
    if c == ``SepLogic.spure then some op else none) | return none
  let some exOp := entries.findSome? (fun (c, op, _) =>
    if c == ``SepLogic.ex then some op else none) | return none
  let wandOp := entries.findSome? (fun (c, op, _) =>
    if c == ``SepLogic.wand then some op else none)
  let mut lv0 := levelZero
  let mut inst0? ← sepInstAt carrier u levelZero
  if inst0?.isNone then
    lv0 := levelOne
    inst0? ← sepInstAt carrier u levelOne
  let some inst0 := inst0? | return none
  let empE := mkAppN empFn empArgs
  return some {
    carrier := carrier,
    u := u,
    entOp := entOp,
    starOp := starOp,
    empOp := empOp,
    pureOp := pureOp,
    exOp := exOp,
    wandOp := wandOp,
    starFn := starFn,
    starArgs := starArgs,
    empE := empE,
    entFn := entFn,
    entArgs := entArgs,
    lv0 := lv0,
    inst0 := inst0 }

def nctxFor? (t : Expr) : MetaM (Option (NCtx × Expr × Expr)) := do
  let .const hn _ := t.getAppFn | return none
  if isClassOpName hn then return none
  let entries ← foldEntries
  let some ent := entries.findSome? (fun (c, op, _) =>
    if c == ``SepLogic.Entails && op.name == hn && t.getAppNumArgs == op.arity then some op
    else none) | return none
  let args := t.getAppArgs
  let some l := args[ent.pos[0]!]? | return none
  let some r := args[ent.pos[1]!]? | return none
  let carrier ← instantiateMVars (← inferType l)
  if carrier.hasMVar then return none
  let m := (← getEnv).mainModule
  let (m0, k, cache) ← nctxCache.get
  let cache := if k == entries && m0 == m then cache else #[]
  match cache.find? (·.1 == carrier) with
  | some (_, some c) => return some (c, l, r)
  | some (_, none) => return none
  | none =>
    let c? ← buildNCtx entries carrier ent
    nctxCache.set (m, entries, cache.push (carrier, c?))
    return c?.map (·, l, r)

def hasClassOp (e : Expr) : Bool :=
  (e.find? fun s => match s with
    | .const n _ => isClassOpName n
    | _ => false).isSome

def classNCtx? (t : Expr) : Option (NCtx × Expr × Expr) := do
  let (sc, l, r) ← matchEntails? t
  let [u, v] := sc.levels | none
  let op2 := fun (n : Name) => ({ name := n, arity := 4, pos := #[2, 3] } : NOp)
  let hole := mkSort levelZero
  let c : NCtx := {
    carrier := sc.carrier,
    u := u,
    entOp := op2 ``SepLogic.Entails,
    starOp := op2 ``SepLogic.star,
    empOp := { name := ``SepLogic.emp, arity := 2, pos := #[] },
    pureOp := { name := ``SepLogic.spure, arity := 3, pos := #[2] },
    exOp := op2 ``SepLogic.ex,
    wandOp := some (op2 ``SepLogic.wand),
    starFn := mkConst ``SepLogic.star [u, v],
    starArgs := #[sc.carrier, sc.inst, hole, hole],
    empE := mkApp2 (mkConst ``SepLogic.emp [u, v]) sc.carrier sc.inst,
    entFn := mkConst ``SepLogic.Entails [u, v],
    entArgs := #[sc.carrier, sc.inst, hole, hole],
    lv0 := v,
    inst0 := sc.inst }
  return (c, l, r)

def sepGoal? (g : MVarId) : MetaM (Option (MVarId × NCtx × Expr × Expr)) := g.withContext do
  let mut g := g
  let mut t ← instantiateMVars (← g.getType)
  if hasClassOp t then
    let t' ← instantiateMVars (← rewriteWithRfl (← taggedLemmas `xsimpl_unfold_class) t)
    if t' != t then
      g ← g.replaceTargetDefEq t'
      t := t'
  match ← nctxFor? t with
  | some (c, l, r) => return some (g, c, l, r)
  | none => return (classNCtx? t).map fun (c, l, r) => (g, c, l, r)

namespace NCtx

def isOp (op : NOp) (e : Expr) : Bool := e.isAppOfArity op.name op.arity

def arg (op : NOp) (e : Expr) (i : Nat) : Expr := e.getArg! op.pos[i]!

def mkStar (c : NCtx) (a b : Expr) : Expr :=
  mkAppN c.starFn ((c.starArgs.set! c.starOp.pos[0]! a).set! c.starOp.pos[1]! b)

def mkEnt (c : NCtx) (a b : Expr) : Expr :=
  mkAppN c.entFn ((c.entArgs.set! c.entOp.pos[0]! a).set! c.entOp.pos[1]! b)

def starL (c : NCtx) : List Expr → Expr
  | [] => c.empE
  | [a] => a
  | a :: r => c.mkStar a (c.starL r)

def starLeft (c : NCtx) (xs : Array Expr) : Expr := Id.run do
  let mut acc := xs[0]!
  for i in [1 : xs.size] do
    acc := c.mkStar acc xs[i]!
  return acc

def lem (c : NCtx) (n : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst n [c.u, c.lv0]) (#[c.carrier, c.inst0] ++ args)

def lemAt (c : NCtx) (lv : Level) (inst : Expr) (n : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst n [c.u, lv]) (#[c.carrier, inst] ++ args)

def trans (c : NCtx) (a b d p q : Expr) : Expr := c.lem ``nt_trans #[a, b, d, p, q]

def transO (c : NCtx) (a b d : Expr) (p : Option Expr) (q : Expr) : Expr :=
  match p with
  | none => q
  | some p => c.trans a b d p q

def transO' (c : NCtx) (a b d : Expr) (p : Expr) (q : Option Expr) : Expr :=
  match q with
  | none => p
  | some q => c.trans a b d p q

def eqTrans (c : NCtx) (a b d p q : Expr) : Expr :=
  mkAppN (mkConst ``Eq.trans [c.u.succ]) #[c.carrier, a, b, d, p, q]

def eqSymm (c : NCtx) (a b p : Expr) : Expr :=
  mkAppN (mkConst ``Eq.symm [c.u.succ]) #[c.carrier, a, b, p]

def starFnOf (c : NCtx) (a : Expr) : Expr :=
  let n := c.starOp.arity
  if c.starOp.pos[0]! + 2 == n && c.starOp.pos[1]! + 1 == n then
    mkAppN c.starFn ((c.starArgs.set! c.starOp.pos[0]! a).extract 0 (n - 1))
  else .lam `x c.carrier (c.mkStar a (.bvar 0)) .default

def congrStar (c : NCtx) (a b1 b2 p : Expr) : Expr :=
  mkAppN (mkConst ``congrArg [c.u.succ, c.u.succ]) #[c.carrier, c.carrier, b1, b2, c.starFnOf a, p]

partial def flat (c : NCtx) (e : Expr) : List Expr × Option Expr :=
  if isOp c.starOp e then
    let a := arg c.starOp e 0
    let b := arg c.starOp e 1
    if isOp c.starOp a then
      let a1 := arg c.starOp a 0
      let a2 := arg c.starOp a 1
      let e' := c.mkStar a1 (c.mkStar a2 b)
      let p1 := c.lem ``nt_assoc #[a1, a2, b]
      let (l, p2) := c.flat e'
      (l, some (match p2 with
        | none => p1
        | some p2 => c.eqTrans e e' (c.starL l) p1 p2))
    else if isOp c.empOp a then
      let p1 := c.lem ``nt_empl #[b]
      let (l, p2) := c.flat b
      (l, some (match p2 with
        | none => p1
        | some p2 => c.eqTrans e b (c.starL l) p1 p2))
    else
      let (lb, pb) := c.flat b
      if lb.isEmpty then
        let p2 := c.lem ``nt_empr #[a]
        match pb with
        | none => ([a], some p2)
        | some q =>
          let mid := c.mkStar a c.empE
          ([a], some (c.eqTrans e mid a (c.congrStar a b c.empE q) p2))
      else
        (a :: lb, pb.map (c.congrStar a b (c.starL lb)))
  else if isOp c.empOp e then ([], none)
  else ([e], none)

partial def pullL (c : NCtx) (s : List Expr) (k : Nat) : Expr :=
  match s with
  | s0 :: s1 =>
    if k == 0 then c.lem ``nt_refl #[c.starL s]
    else
      let t0 := s1[k-1]!
      let s1' := s1.eraseIdx (k-1)
      if s1'.isEmpty then c.lem ``nt_comm #[s0, t0]
      else
        let r := c.starL s1'
        let p1 := c.pullL s1 (k-1)
        let fr := c.lem ``nt_frame #[s0, c.starL s1, c.mkStar t0 r, p1]
        let sw := c.lem ``nt_swap #[s0, t0, r]
        c.trans (c.starL s) (c.mkStar s0 (c.mkStar t0 r)) (c.mkStar t0 (c.mkStar s0 r)) fr sw
  | [] => c.lem ``nt_refl #[c.empE]

partial def pullR (c : NCtx) (s : List Expr) (k : Nat) : Expr :=
  match s with
  | s0 :: s1 =>
    if k == 0 then c.lem ``nt_refl #[c.starL s]
    else
      let t0 := s1[k-1]!
      let s1' := s1.eraseIdx (k-1)
      if s1'.isEmpty then c.lem ``nt_comm #[t0, s0]
      else
        let r := c.starL s1'
        let p1 := c.pullR s1 (k-1)
        let sw := c.lem ``nt_swap #[t0, s0, r]
        let fr := c.lem ``nt_frame #[s0, c.mkStar t0 r, c.starL s1, p1]
        c.trans (c.mkStar t0 (c.mkStar s0 r)) (c.mkStar s0 (c.mkStar t0 r)) (c.starL s) sw fr
  | [] => c.lem ``nt_refl #[c.empE]

partial def perm (c : NCtx) (s : List Expr) (idx : List Nat) : Option Expr :=
  match s, idx with
  | _ :: _ :: _, k :: rest =>
    let t := s[k]!
    let s' := s.eraseIdx k
    let rest' := rest.map (fun j => if j > k then j - 1 else j)
    let t' := rest'.map (s'[·]!)
    let fr := (c.perm s' rest').map (fun sub =>
      c.lem ``nt_frame #[t, c.starL s', c.starL t', sub])
    let pl := if k == 0 then none else some (c.pullL s k)
    match pl, fr with
    | none, none => none
    | some p, none => some p
    | none, some f => some f
    | some p, some f => some (c.trans (c.starL s) (c.mkStar t (c.starL s')) (c.mkStar t (c.starL t')) p f)
  | _, _ => none

partial def frameChain (c : NCtx) (cs xs ys : List Expr) (mv : Expr) : Expr :=
  match cs with
  | [c1] =>
    match xs.isEmpty, ys.isEmpty with
    | false, false => c.lem ``nt_frame #[c1, c.starL xs, c.starL ys, mv]
    | true, false => c.lem ``nt_cancel_r #[c1, c.starL ys, mv]
    | false, true => c.lem ``nt_cancel_l #[c1, c.starL xs, mv]
    | true, true => c.lem ``nt_refl #[c1]
  | c1 :: cs' =>
    c.lem ``nt_frame #[c1, c.starL (cs' ++ xs), c.starL (cs' ++ ys), c.frameChain cs' xs ys mv]
  | [] => mv

def selfEq (s : Expr) : Bool :=
  match s.getAppFnArgs with
  | (``Eq, #[_, a, b]) => a == b
  | (``Iff, #[a, b]) => a == b
  | _ => false

def bad (c : NCtx) (e : Expr) : Bool :=
  (e.find? (fun s =>
    match s with
    | .const n _ =>
      isClassOpName n || n == c.starOp.name || n == c.empOp.name || n == c.pureOp.name ||
        n == c.exOp.name || n == c.entOp.name ||
        (match c.wandOp with
         | some w => n == w.name
         | none => false)
    | .mdata .. => true
    | _ => selfEq s)).isSome

structure SpineAcc where
  lvs : Array Level := #[]
  hasEx : Bool := false
  nestedTypeEx : Bool := false

def exLevel (c : NCtx) (a : Expr) (acc : SpineAcc) (nested : Bool) : MetaM (Option SpineAcc) := do
  if a.hasLooseBVars || c.bad a || a == c.carrier then return none
  let lv ← try (some <$> getLevel a) catch _ => pure none
  let some lv := lv | return none
  let lv := (← instantiateLevelMVars lv).normalize
  if lv.hasMVar then return none
  let lvs := if acc.lvs.contains lv then acc.lvs else acc.lvs.push lv
  return some { acc with lvs, nestedTypeEx := acc.nestedTypeEx || (nested && lv != levelZero) }

mutual

partial def nestedSide (c : NCtx) (x : Expr) (acc : SpineAcc) : MetaM (Option SpineAcc) := do
  if x.isLambda then
    return ← lambdaTelescope x fun _ b => nestedSide c b acc
  let (items, _) := c.flat x
  let mut acc := acc
  for it in items do
    if isOp c.exOp it then
      let some acc' ← exLevel c (arg c.exOp it 0) acc true | return none
      let j := arg c.exOp it 1
      unless j.isLambda do return none
      let some acc' ← nestedSide c j acc' | return none
      acc := acc'
    else if isOp c.pureOp it then
      continue
    else
      let some acc' ← atomCheck c it acc | return none
      acc := acc'
  return some acc

partial def atomCheck (c : NCtx) (e : Expr) (acc : SpineAcc) : MetaM (Option SpineAcc) := do
  if !c.bad e then return some acc
  if let some w := c.wandOp then
    if isOp w e then
      let some acc ← nestedSide c (arg w e 0) acc | return none
      return ← nestedSide c (arg w e 1) acc
  let fn := e.getAppFn
  if e.getAppNumArgs == 0 || c.bad fn then return none
  let mut acc := acc
  for x in e.getAppArgs do
    if !c.bad x then continue
    let some acc' ← nestedSide c x acc | return none
    acc := acc'
  return some acc

end

partial def spine (c : NCtx) (e : Expr) (acc : SpineAcc) : MetaM (Option SpineAcc) := do
  if isOp c.starOp e then
    match ← c.spine (arg c.starOp e 0) acc with
    | none => return none
    | some acc => c.spine (arg c.starOp e 1) acc
  else if isOp c.empOp e then return some acc
  else if isOp c.pureOp e then return some acc
  else if isOp c.exOp e then
    let some acc ← exLevel c (arg c.exOp e 0) acc false | return none
    let acc := { acc with hasEx := true }
    let j := arg c.exOp e 1
    if j.isLambda then lambdaTelescope j fun _ b => c.spine b acc
    else if c.bad j || j.hasLooseBVars then return none
    else return some acc
  else if e.isMVar then return some acc
  else atomCheck c e acc

inductive Item where
  | atom
  | ex (a j : Expr)
  | pure (p : Expr)

def item (c : NCtx) (e : Expr) : Item :=
  if isOp c.exOp e then .ex (arg c.exOp e 0) (arg c.exOp e 1)
  else if isOp c.pureOp e then .pure (arg c.pureOp e 0)
  else .atom

def pick (c : NCtx) (s : List Expr) (typeEx leftPure : Bool) : Option Nat := Id.run do
  let n := s.length
  let arr := s.toArray
  if typeEx then
    let mut i := n
    while i > 0 do
      i := i - 1
      if isOp c.exOp arr[i]! then return some i
    if leftPure then
      for k in [0 : n] do
        if isOp c.pureOp arr[k]! then return some k
      return none
  let mut i := n
  while i > 0 do
    i := i - 1
    if isOp c.exOp arr[i]! || isOp c.pureOp arr[i]! then return some i
  return none

def pickEx (c : NCtx) (s : List Expr) : Option Nat := Id.run do
  let arr := s.toArray
  let mut i := arr.size
  while i > 0 do
    i := i - 1
    if isOp c.exOp arr[i]! then return some i
  return none

def exBody (j : Expr) : Name × Expr :=
  if j.isLambda then (j.bindingName!, j.bindingBody!) else (`x, mkApp j (.bvar 0))

end NCtx


def newGoal (cur : MVarId) (ty : Expr) (mk : Expr → Expr) : MetaM MVarId := cur.withContext do
  let m ← mkFreshExprMVar ty
  cur.assign (mk m)
  return m.mvarId!

def normLevel (a : Expr) : MetaM Level := do
  return (← instantiateLevelMVars (← getLevel a)).normalize

mutual

partial def itemsNorm (c : NCtx) (x : Expr) (items : List Expr) (p : Option Expr) :
    MetaM (List Expr × Option Expr) := do
  let mut cur := items
  let mut pf := p
  let mut lhs := c.starL items
  for k in [0 : items.length] do
    let it := cur[k]!
    let (it', q) ← itemNorm c it
    let some q := q | continue
    let next := cur.set k it'
    let f ← withLocalDeclD `y (← inferType it) fun y =>
      mkLambdaFVars #[y] (c.starL (cur.set k y))
    let step ← mkCongrArg f q
    let rhs := c.starL next
    pf := some (match pf with
      | none => step
      | some p0 => c.eqTrans x lhs rhs p0 step)
    lhs := rhs
    cur := next
  return (cur, pf)

partial def nestNorm (c : NCtx) (x : Expr) : MetaM (Expr × Option Expr) := do
  let (items0, p0) := c.flat x
  let (items, p1) ← itemsNorm c x items0 p0
  let flatE := c.starL items
  unless items.any (NCtx.isOp c.exOp) do return (flatE, p1)
  let arr := items.toArray
  let n := arr.size
  let mut acc := arr[n-1]!
  let mut accPf : Option Expr := none
  let mut k := n - 1
  while k > 0 do
    k := k - 1
    let orig := c.starL (items.drop (k+1))
    let start := c.mkStar arr[k]! orig
    let mid := c.mkStar arr[k]! acc
    let (acc', q) ← combine c arr[k]! acc
    let pa := accPf.map (c.congrStar arr[k]! orig acc)
    accPf := match pa, q with
      | none, none => none
      | some pa, none => some pa
      | none, some q => some q
      | some pa, some q => some (c.eqTrans start mid acc' pa q)
    acc := acc'
  let pf := match p1, accPf with
    | none, none => none
    | some p, none => some p
    | none, some q => some q
    | some p, some q => some (c.eqTrans x flatE acc p q)
  return (acc, pf)

partial def combine (c : NCtx) (a b : Expr) : MetaM (Expr × Option Expr) := do
  let e := c.mkStar a b
  let exLam := fun (x : Expr) => NCtx.isOp c.exOp x && (NCtx.arg c.exOp x 1).isLambda
  if exLam b || exLam a then
    let right := exLam b
    let x := if right then b else a
    let ax := NCtx.arg c.exOp x 0
    let jx := NCtx.arg c.exOp x 1
    let lv ← normLevel ax
    let some ins ← sepInstAt c.carrier c.u lv | throwError "xsimpl: no instance"
    let eq1 := if right then c.lemAt lv ins ``nt_eq_exr #[ax, a, jx]
      else c.lemAt lv ins ``nt_eq_exl #[ax, jx, b]
    let body1 := if right then c.mkStar a jx.bindingBody! else c.mkStar jx.bindingBody! b
    let mkEx := fun (j : Expr) => mkAppN x.getAppFn (x.getAppArgs.set! c.exOp.pos[1]! j)
    let e1 := mkEx (.lam jx.bindingName! ax body1 jx.bindingInfo!)
    let r ← withLocalDeclD jx.bindingName! ax fun y => do
      let inner := jx.bindingBody!.instantiate1 y
      let (bd', pb) ← if right then combine c a inner else combine c inner b
      match pb with
      | none => return none
      | some pb => return some (← mkLambdaFVars #[y] bd', ← mkFunExt (← mkLambdaFVars #[y] pb))
    match r with
    | none => return (e1, some eq1)
    | some (j', pj) =>
      let f ← withLocalDeclD `k (← inferType jx) fun k => mkLambdaFVars #[k] (mkEx k)
      return (mkEx j', some (c.eqTrans e e1 (mkEx j') eq1 (← mkCongrArg f pj)))
  else
    let (l, p) := c.flat e
    return (c.starL l, p)

partial def wandNorm (c : NCtx) (w : NOp) (e : Expr) : MetaM (Expr × Option Expr) := do
  let mkW := fun (a b : Expr) =>
    mkAppN e.getAppFn ((e.getAppArgs.set! w.pos[0]! a).set! w.pos[1]! b)
  let a := NCtx.arg w e 0
  let b := NCtx.arg w e 1
  let (a', pa) ← nestNorm c a
  let (b', pb) ← nestNorm c b
  let mut cur := e
  let mut pf : Option Expr := none
  let step := fun (pf : Option Expr) (lhs mid rhs q : Expr) =>
    match pf with
    | none => q
    | some p => c.eqTrans lhs mid rhs p q
  if let some pa := pa then
    let f ← withLocalDeclD `y c.carrier fun y => mkLambdaFVars #[y] (mkW y b)
    let nxt := mkW a' b
    pf := some (step pf e cur nxt (← mkCongrArg f pa))
    cur := nxt
  if let some pb := pb then
    let f ← withLocalDeclD `y c.carrier fun y => mkLambdaFVars #[y] (mkW a' y)
    let nxt := mkW a' b'
    pf := some (step pf e cur nxt (← mkCongrArg f pb))
    cur := nxt
  if NCtx.isOp c.starOp a' then
    let x := NCtx.arg c.starOp a' 0
    let y := NCtx.arg c.starOp a' 1
    let inner := mkW y b'
    let (inner', pi) ← itemNorm c inner
    let nxt := mkW x inner
    let q := c.lem ``nt_curry #[x, y, b']
    pf := some (step pf e cur nxt q)
    cur := nxt
    if let some pi := pi then
      let f ← withLocalDeclD `y c.carrier fun z => mkLambdaFVars #[z] (mkW x z)
      let nxt2 := mkW x inner'
      pf := some (step pf e cur nxt2 (← mkCongrArg f pi))
      cur := nxt2
  return (cur, pf)

partial def argNorm (c : NCtx) (x : Expr) : MetaM (Expr × Option Expr) := do
  let .lam n ty b bi := x | nestNorm c x
  withLocalDecl n bi ty fun v => do
    let (b', pb) ← argNorm c (b.instantiate1 v)
    match pb with
    | none => return (x, none)
    | some pb => return (← mkLambdaFVars #[v] b', some (← mkFunExt (← mkLambdaFVars #[v] pb)))

partial def itemNorm (c : NCtx) (e : Expr) : MetaM (Expr × Option Expr) := do
  if NCtx.isOp c.exOp e then
    let j := NCtx.arg c.exOp e 1
    unless j.isLambda do return (e, none)
    let a := NCtx.arg c.exOp e 0
    let r ← withLocalDeclD j.bindingName! a fun v => do
      let (b', pb) ← nestNorm c (j.bindingBody!.instantiate1 v)
      match pb with
      | none => return none
      | some pb => return some (← mkLambdaFVars #[v] b', ← mkFunExt (← mkLambdaFVars #[v] pb))
    let some (j', pj) := r | return (e, none)
    let e' := mkAppN e.getAppFn (e.getAppArgs.set! c.exOp.pos[1]! j')
    let f ← withLocalDeclD `y (← inferType j) fun y =>
      mkLambdaFVars #[y] (mkAppN e.getAppFn (e.getAppArgs.set! c.exOp.pos[1]! y))
    return (e', some (← mkCongrArg f pj))
  if NCtx.isOp c.pureOp e then
    let pr := NCtx.arg c.pureOp e 0
    unless NCtx.selfEq pr do return (e, none)
    let q ← if pr.isAppOf ``Eq then mkAppM ``eq_self #[pr.appArg!] else mkAppM ``iff_self #[pr.appArg!]
    let args := e.getAppArgs
    let e' := mkAppN e.getAppFn (args.set! c.pureOp.pos[0]! (mkConst ``True))
    let f ← withLocalDeclD `y (mkSort levelZero) fun y =>
      mkLambdaFVars #[y] (mkAppN e.getAppFn (args.set! c.pureOp.pos[0]! y))
    return (e', some (← mkCongrArg f q))
  if !c.bad e then return (e, none)
  if let some w := c.wandOp then
    if NCtx.isOp w e then return ← wandNorm c w e
  let args := e.getAppArgs
  let mut cur := args
  let mut pf : Option Expr := none
  for i in [0 : args.size] do
    if !c.bad args[i]! then continue
    let (a', q) ← argNorm c args[i]!
    let some q := q | continue
    let next := cur.set! i a'
    let f ← withLocalDeclD `y (← inferType args[i]!) fun y =>
      mkLambdaFVars #[y] (mkAppN e.getAppFn (cur.set! i y))
    let step ← mkCongrArg f q
    pf := some (← match pf with
      | none => pure step
      | some p0 => mkEqTrans p0 step)
    cur := next
  return (mkAppN e.getAppFn cur, pf)

end

def flatN (c : NCtx) (e : Expr) : MetaM (List Expr × Option Expr) := do
  let (s, p) := c.flat e
  let needs := fun (it : Expr) =>
    if NCtx.isOp c.pureOp it then NCtx.selfEq (NCtx.arg c.pureOp it 0)
    else !NCtx.isOp c.exOp it && c.bad it
  if !s.any needs then return (s, p)
  let (s', q) ← itemsNorm c e s p
  return (s', q)

def flatGoalL (c : NCtx) (cur : MVarId) (l r : Expr) : MetaM (MVarId × List Expr) :=
    cur.withContext do
  let (s, p) ← flatN c l
  match p with
  | none => return (cur, s)
  | some p =>
    let ls := c.starL s
    let g ← newGoal cur (c.mkEnt ls r) fun m => c.trans l ls r (c.lem ``nt_of_eq #[l, ls, p]) m
    return (g, s)

def flatGoalR (c : NCtx) (cur : MVarId) (l r : Expr) : MetaM (MVarId × List Expr) :=
    cur.withContext do
  let (t, p) ← flatN c r
  match p with
  | none => return (cur, t)
  | some p =>
    let lt := c.starL t
    let g ← newGoal cur (c.mkEnt l lt) fun m =>
      c.trans l lt r m (c.lem ``nt_of_eq #[lt, r, c.eqSymm r lt p])
    return (g, t)

def pureBlockPf (c : NCtx) (s : List Expr) : Option Expr × Expr × List Expr × List Expr := Id.run do
  let arr := s.toArray
  let n := arr.size
  let last := arr[n - 1]!
  let isP := fun (e : Expr) => NCtx.isOp c.pureOp e
  let mut P : Option Expr := if isP last then some last else none
  let mut R : Option Expr := if isP last then none else some last
  let mut ps : Array Expr := if isP last then #[last] else #[]
  let mut cs : List Expr := if isP last then [] else [last]
  let mut tail := last
  let mut pf : Option Expr := none
  let assemble := fun (P R : Option Expr) => match P, R with
    | some p, some r => c.mkStar p r
    | some p, none => p
    | none, some r => r
    | none, none => c.empE
  let mut j := n - 1
  while j > 0 do
    j := j - 1
    let x := arr[j]!
    let A := assemble P R
    let src := c.mkStar x tail
    let framed := pf.map (fun q => c.lem ``nt_frame #[x, tail, A, q])
    let (P', R', step) : Option Expr × Option Expr × Option Expr :=
      if isP x then
        match P, R with
        | none, some r => (some x, some r, none)
        | some p, none => (some (c.mkStar p x), none, some (c.lem ``nt_comm #[x, p]))
        | some p, some r => (some (c.mkStar p x), some r, some (c.lem ``nt_pushl #[x, p, r]))
        | none, none => (some x, none, none)
      else
        match P, R with
        | none, some r => (none, some (c.mkStar x r), none)
        | some p, none => (some p, some x, some (c.lem ``nt_comm #[x, p]))
        | some p, some r => (some p, some (c.mkStar x r), some (c.lem ``nt_swap #[x, p, r]))
        | none, none => (none, some x, none)
    let A' := assemble P' R'
    pf := match framed, step with
      | none, none => none
      | some f, none => some f
      | none, some st => some st
      | some f, some st => some (c.trans src (c.mkStar x A) A' f st)
    if isP x then ps := ps.push x else cs := x :: cs
    P := P'
    R := R'
    tail := src
  let k := ps.size
  let mut m := k
  while m > 1 do
    m := m - 1
    let y := ps[m]!
    let L := c.starLeft (ps.extract 0 m)
    match R with
    | none => R := some y
    | some r =>
      let A := c.mkStar (c.mkStar L y) r
      let A' := c.mkStar L (c.mkStar y r)
      let st := c.lem ``nt_of_eq #[A, A', c.lem ``nt_assoc #[L, y, r]]
      pf := some (match pf with
        | none => st
        | some q => c.trans (c.starL s) A A' q st)
      R := some (c.mkStar y r)
    P := some L
  let mid := c.starL (ps.toList ++ cs)
  return (pf, mid, ps.toList, cs)

mutual

partial def peelPures (c : NCtx) (inst : Level → MetaM Expr) (lctx0 : LocalContext)
    (li0 : LocalInstances) (rr : Expr) (typeEx leftPure : Bool) (xs : Array Expr)
    (ps cs : List Expr) : MetaM (Expr × Array Expr × List Expr × Expr) := do
  match ps with
  | [] => lhsRec c inst lctx0 li0 rr typeEx leftPure xs cs
  | it :: rest =>
    let p := NCtx.arg c.pureOp it 0
    let pA := p.abstract xs
    let restL := rest ++ cs
    withLocalDecl `a .default p fun h => do
      let (m, xsF, sF, inner) ← peelPures c inst lctx0 li0 rr typeEx leftPure (xs.push h) rest cs
      let lam := Expr.lam `a pA inner .default
      if restL.isEmpty then
        return (m, xsF, sF, c.lem ``nt_purel1 #[pA, rr, lam])
      else
        return (m, xsF, sF, c.lem ``nt_purel #[pA, (c.starL restL).abstract xs, rr, lam])

partial def lhsRec (c : NCtx) (inst : Level → MetaM Expr) (lctx0 : LocalContext)
    (li0 : LocalInstances) (rr : Expr) (typeEx leftPure : Bool) (xs : Array Expr)
    (s : List Expr) : MetaM (Expr × Array Expr × List Expr × Expr) := do
  let abs := fun (e : Expr) => e.abstract xs
  if !typeEx && !s.any (NCtx.isOp c.exOp) && (s.filter (NCtx.isOp c.pureOp)).length ≥ 2 then
    let (pf, mid, ps, cs) := pureBlockPf c s
    let (m, xsF, sF, inner) ← peelPures c inst lctx0 li0 rr typeEx leftPure xs ps cs
    return (m, xsF, sF, c.transO (abs (c.starL s)) (abs mid) rr (pf.map abs) inner)
  match c.pick s typeEx leftPure with
  | none =>
    let ty ← mkForallFVars xs (c.mkEnt (c.starL s) rr)
    let m ← mkFreshExprMVarAt lctx0 li0 ty
    let k := xs.size
    return (m, xs, s, mkAppN m ((List.range k).toArray.map (fun i => .bvar (k - 1 - i))))
  | some i =>
    let n := s.length
    let arr := s.toArray
    let ls := c.starL s
    match c.item arr[i]! with
    | .ex a j =>
      let lv ← normLevel a
      let ins ← inst lv
      let (bn, jb) := NCtx.exBody j
      let mut pf : Option Expr := none
      let mut body := jb
      if i + 1 < n then
        let q := c.starL (s.drop (i+1))
        pf := some (c.lemAt lv ins ``nt_exl_base #[a, j, q])
        body := c.mkStar jb q
      let mut k := i
      while k > 0 do
        k := k - 1
        let x := c.starL (s.drop (k+1))
        let kl := Expr.lam bn a body .default
        let h := pf.getD (c.lemAt lv ins ``nt_refl #[x])
        pf := some (c.lemAt lv ins ``nt_exl_layer #[a, kl, x, arr[k]!, h])
        body := c.mkStar arr[k]! body
      let kl := Expr.lam bn a body .default
      let exK := mkAppN (mkConst ``SepLogic.ex [c.u, lv]) #[c.carrier, ins, a, kl]
      let aA := abs a
      let klA := abs kl
      let head := c.transO (abs ls) (abs exK) rr (pf.map abs)
      withLocalDecl bn .default a fun x => do
        let xs2 := xs.push x
        let bx := body.instantiate1 x
        let (s2, p) ← flatN c bx
        let (m, xsF, sF, inner) ← lhsRec c inst lctx0 li0 rr typeEx leftPure xs2 s2
        let inner := match p with
          | none => inner
          | some p =>
            let bxA := bx.abstract xs2
            let ls2A := (c.starL s2).abstract xs2
            c.trans bxA ls2A rr (c.lem ``nt_of_eq #[bxA, ls2A, p.abstract xs2]) inner
        return (m, xsF, sF, head (c.lemAt lv ins ``nt_exl #[aA, klA, rr, .lam bn aA inner .default]))
    | .pure p =>
      let pA := abs p
      if n == 1 then
        withLocalDecl `a .default p fun h => do
          let (m, xsF, sF, inner) ← lhsRec c inst lctx0 li0 rr typeEx leftPure (xs.push h) []
          return (m, xsF, sF, c.lem ``nt_purel1 #[pA, rr, .lam `a pA inner .default])
      else
        let rest := s.eraseIdx i
        let lr := c.starL rest
        let pl := if i == 0 then none else some (c.pullL s i)
        let lrA := abs lr
        let head := c.transO (abs ls) (abs (c.mkStar arr[i]! lr)) rr (pl.map abs)
        withLocalDecl `a .default p fun h => do
          let (m, xsF, sF, inner) ← lhsRec c inst lctx0 li0 rr typeEx leftPure (xs.push h) rest
          return (m, xsF, sF, head (c.lem ``nt_purel #[pA, lrA, rr, .lam `a pA inner .default]))
    | .atom => throwError "xsimpl: native step on an atom"

end

def lhsBatch (c : NCtx) (inst : Level → MetaM Expr) (cur : MVarId) (s : List Expr) (rr : Expr)
    (typeEx leftPure : Bool) : MetaM (MVarId × List Expr × Nat) := cur.withContext do
  let (m, xsF, sF, pf) ← lhsRec c inst (← getLCtx) (← getLocalInstances) rr typeEx leftPure #[] s
  cur.assign pf
  let (fvs, g2) ← m.mvarId!.introN xsF.size
  return (g2, sF.map (·.replaceFVars xsF (fvs.map mkFVar)), xsF.size)

def rhsStep (c : NCtx) (inst : Level → MetaM Expr) (cur : MVarId) (ls : Expr) (tt : List Expr)
    (jx : Nat) : MetaM (MVarId × List Expr × Expr) := cur.withContext do
  let n := tt.length
  let arr := tt.toArray
  let lt := c.starL tt
  match c.item arr[jx]! with
  | .ex a j =>
    let lv ← normLevel a
    let ins ← inst lv
    let (bn, jb) := NCtx.exBody j
    let mut pf : Option Expr := none
    let mut body := jb
    if jx + 1 < n then
      let q := c.starL (tt.drop (jx+1))
      pf := some (c.lemAt lv ins ``nt_exr_base #[a, j, q])
      body := c.mkStar jb q
    let mut k := jx
    while k > 0 do
      k := k - 1
      let x := c.starL (tt.drop (k+1))
      let kl := Expr.lam bn a body .default
      let h := pf.getD (c.lemAt lv ins ``nt_refl #[x])
      pf := some (c.lemAt lv ins ``nt_exr_layer #[a, kl, x, arr[k]!, h])
      body := c.mkStar arr[k]! body
    let kl := Expr.lam bn a body .default
    let exK := mkAppN (mkConst ``SepLogic.ex [c.u, lv]) #[c.carrier, ins, a, kl]
    let y ← mkFreshExprMVar a (userName := bn)
    let nr := body.instantiate1 y
    let m ← newGoal cur (c.mkEnt ls nr) fun m =>
      c.transO' ls exK lt (c.lemAt lv ins ``nt_exr #[a, y, kl, ls, m]) pf
    let (g2, t') ← flatGoalR c m ls nr
    return (g2, t', y)
  | .pure p =>
    let q ← mkFreshExprMVar p (userName := `x)
    if p.isConstOf ``True then q.mvarId!.assign (mkConst ``True.intro)
    if n == 1 then
      let g2 ← newGoal cur (c.mkEnt ls c.empE) fun m => c.lem ``nt_purer1 #[p, ls, q, m]
      return (g2, [], q)
    else
      let rest := tt.eraseIdx jx
      let lr := c.starL rest
      let pl := if jx == 0 then none else some (c.pullR tt jx)
      let g2 ← newGoal cur (c.mkEnt ls lr) fun m =>
        c.transO' ls (c.mkStar arr[jx]! lr) lt (c.lem ``nt_purer #[p, ls, lr, q, m]) pl
      return (g2, rest, q)
  | .atom => throwError "xsimpl: native step on an atom"

def cancelScan (sa ta : Array Expr) : MetaM (Array (Nat × Nat) × Array Bool × Array Nat) := do
  let cheap ← cheapCancel.get
  let mut lAlive : Array Bool := sa.map (fun _ => true)
  let mut pairs : Array (Nat × Nat) := #[]
  let mut tIdx : Array Nat := (List.range ta.size).toArray
  let mut rStart := 0
  let mut cont := true
  while cont do
    cont := false
    let mut found : Option (Nat × Nat) := none
    for r in [rStart : tIdx.size] do
      let ri ← instantiateMVars ta[tIdx[r]!]!
      if ri.isMVar then continue
      for li in [0 : sa.size] do
        unless lAlive[li]! do continue
        let le ← instantiateMVars sa[li]!
        if le.isMVar then continue
        let mv := le.hasMVar || ri.hasMVar
        if cheap && !mv && le != ri then
          match le.getAppFn, ri.getAppFn with
          | .const a _, .const b _ =>
            if a != b && !(← isReducible a) && !(← isReducible b) then continue
          | _, _ => pure ()
        if ← cheapDefEq le ri then
          found := some (li, r)
          rStart := if mv then 0 else r
          break
      if found.isSome then break
    if let some (li, r) := found then
      pairs := pairs.push (li, tIdx[r]!)
      lAlive := lAlive.set! li false
      tIdx := tIdx.eraseIdx! r
      cont := true
  return (pairs, lAlive, tIdx)

def cancelStep (c : NCtx) (cur : MVarId) (s tt : List Expr) :
    MetaM (Option (Option MVarId × List Expr × List Expr)) :=
  cur.withContext do
  let (pairs, lAlive, tIdx) ← cancelScan s.toArray tt.toArray
  if pairs.isEmpty then return none
  let ta ← tt.toArray.mapM instantiateMVars
  let sa ← s.toArray.mapM instantiateMVars
  let cl := pairs.toList.map (fun (li, _) => sa[li]!)
  let cr : List Expr := pairs.toList.map (fun (_, ri) => ta[ri]!)
  for x in cr do trace[xsimpl] m!"Cancelling {x}"
  let lRestIdx := (List.range sa.size).filter (fun i => lAlive[i]!)
  let sr := lRestIdx.map (sa[·]!)
  let tr := tIdx.toList.map (ta[·]!)
  let pl := c.perm sa.toList (pairs.toList.map (·.1) ++ lRestIdx)
  let u := cr ++ tr
  let pos := (List.range ta.size).map (fun k =>
    match pairs.findIdx? (·.2 == k) with
    | some p => p
    | none => cr.length + tIdx.toList.idxOf k)
  let pr := c.perm u pos
  let ls := c.starL sa.toList
  let lcl := c.starL (cl ++ sr)
  let lcr := c.starL (cl ++ tr)
  let lt := c.starL ta.toList
  let body := fun (mv : Expr) =>
    c.transO ls lcl lt pl (c.transO' lcl lcr lt (c.frameChain cl sr tr mv) pr)
  if sr.isEmpty && tr.isEmpty then
    cur.assign (body (c.lem ``nt_refl #[c.empE]))
    return some (none, [], [])
  let g2 ← newGoal cur (c.mkEnt (c.starL sr) (c.starL tr)) body
  return some (some g2, sr, tr)

def closeRefl (c : NCtx) (g : MVarId) (l r : Expr) : MetaM Bool := g.withContext do
  unless ← cheapDefEq l r do return false
  g.assign (c.lem ``nt_refl #[l])
  return true

def wholeEq (c : NCtx) (g : MVarId) (l r : Expr) : MetaM Bool := do
  if l.hasExprMVar || r.hasExprMVar then return false
  closeRefl c g l r

def residualEq (c : NCtx) (g : MVarId) (created : Array Expr) (l r : Expr) : MetaM Bool := do
  let l ← instantiateMVars l
  let r ← instantiateMVars r
  let ok := fun (e : Expr) => (e.find? fun x => x.isMVar && !created.contains x).isNone
  unless ok l && ok r do return false
  closeRefl c g l r

def permClose (c : NCtx) (g : MVarId) (s : List Expr) (r : Expr) : MetaM Bool := g.withContext do
  let binder := fun (e : Expr) => NCtx.isOp c.exOp e || NCtx.isOp c.pureOp e
  unless s.any binder || (r.find? binder).isSome do return false
  let (t, _) ← flatN c r
  unless s.length == t.length do return false
  if s.any (·.hasExprMVar) || t.any (·.hasExprMVar) then return false
  let (pairs, _, _) ← cancelScan s.toArray t.toArray
  unless pairs.size == s.length do return false
  let (g2, t2) ← flatGoalR c g (c.starL s) r
  let some (none, _, _) ← cancelStep c g2 s t2 | return false
  return true

def appTag (t n : Name) : Name := if t.isAnonymous then n else appendTag t n

partial def nativeGoal (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let some (g, c, l0, r0) ← sepGoal? g | return none
  let some accL ← c.spine l0 {} | return none
  let some accR ← c.spine r0 { accL with hasEx := false } | return none
  let lvs := accR.lvs
  let rHasEx := accR.hasEx
  let foreverA := accR.nestedTypeEx
  let typeEx := lvs.any (· != levelZero)
  let mut insts : Array (Level × Expr) := #[(c.lv0, c.inst0)]
  for lv in lvs do
    if insts.any (·.1 == lv) then continue
    let some i ← sepInstAt c.carrier c.u lv | return none
    insts := insts.push (lv, i)
  let inst : Level → MetaM Expr := fun lv => do
    match insts.find? (·.1 == lv) with
    | some (_, i) => return i
    | none =>
      let some i ← sepInstAt c.carrier c.u lv | throwError "xsimpl: no instance"
      return i
  if ← wholeEq c g l0 r0 then return some []
  let mut tag ← g.getTag
  let (g1, s1) ← flatGoalL c g l0 r0
  if ← permClose c g1 s1 r0 then return some []
  let mut changed := g1 != g
  let mut cur := g1
  let mut s := s1
  let leftPure := typeEx && (rHasEx || foreverA)
  if (c.pick s typeEx leftPure).isSome then
    changed := true
    let (g2, s2, k) ← lhsBatch c inst cur s r0 typeEx leftPure
    for _ in [0 : k] do
      tag := appTag tag `a
    g2.setTag tag
    cur := g2
    s := s2
  let ls := c.starL s
  let (g3, t3) ← flatGoalR c cur ls r0
  if g3 != cur then changed := true
  cur := g3
  let mut tt := t3
  let mut created : Array Expr := #[]
  repeat
    let some j := (if foreverA then c.pickEx tt else c.pick tt typeEx false) | break
    changed := true
    let (g4, t4, y) ← rhsStep c inst cur ls tt j
    y.mvarId!.setTag (appTag tag `x)
    tag := appTag tag `a
    g4.setTag tag
    cur := g4
    tt := t4
    created := created.push y
  let (res, sr, tr) ← match ← cancelStep c cur s tt with
    | none => pure (some cur, s, tt)
    | some (r, sr, tr) =>
      changed := true
      if let some r := r then r.setTag `a
      pure (r, sr, tr)
  let mut res := res
  let mut tr := tr
  let mut pures : List MVarId := []
  if foreverA then
    if let some r0 := res then
      let mut r := r0
      let lsr := c.starL sr
      repeat
        let some j := (List.range tr.length).find? (fun k => NCtx.isOp c.pureOp tr[k]!) | break
        changed := true
        let (r2, tr2, q) ← rhsStep c inst r lsr tr j
        r := r2
        tr := tr2
        pures := pures ++ [q.mvarId!]
      res := some r
  if let some r := res then
    if ← residualEq c r created (c.starL sr) (c.starL tr) then
      changed := true
      res := none
  if let (some w, some r0) := (c.wandOp, res) then
    let mut r := r0
    repeat
      let tra ← r.withContext (tr.toArray.mapM instantiateMVars)
      let mut hit : Option Nat := none
      for j in [0 : tra.size] do
        let t := tra[j]!
        unless NCtx.isOp w t do continue
        let a := NCtx.arg w t 0
        let b := NCtx.arg w t 1
        if a.hasExprMVar || b.hasExprMVar then continue
        if ← r.withContext (cheapDefEq a b) then
          hit := some j
          break
      let some j := hit | break
      changed := true
      let rest := (List.range tra.size).filter (· != j)
      let restE := rest.map (tra[·]!)
      let a := NCtx.arg w tra[j]! 0
      let inv := (List.range tra.size).map (fun k => if k == j then 0 else if k < j then k + 1 else k)
      let mid := c.starL (tra[j]! :: restE)
      let rt := c.starL tra.toList
      let lsr := c.starL sr
      let ty := c.mkEnt lsr (c.starL restE)
      r ← newGoal r ty fun m =>
        c.transO' lsr mid rt (if restE.isEmpty then c.lem ``nt_wand_same1 #[a, lsr, m]
          else c.lem ``nt_wand_same #[a, lsr, c.starL restE, m]) (c.perm (tra[j]! :: restE) inv)
      tr := restE
    res := some r
    if tr.isEmpty then
      if ← closeRefl c r (c.starL sr) c.empE then res := none
  let mut sub : Option (List MVarId) := none
  if let (some w, some r) := (c.wandOp, res) then
    let sr ← r.withContext (sr.mapM instantiateMVars)
    if tr.length == 1 && NCtx.isOp w tr[0]! then
      let a := NCtx.arg w tr[0]! 0
      let b := NCtx.arg w tr[0]! 1
      let lsr := c.starL sr
      let g' ← newGoal r (c.mkEnt (c.mkStar lsr a) b) fun m => c.lem ``nt_wand_r #[lsr, a, b, m]
      sub := some ((← nativeGoal g').getD [g'])
    else
      let arr := sr.toArray
      let mut hit : Option (Nat × Nat) := none
      for l in [0 : arr.size] do
        if hit.isSome then break
        unless NCtx.isOp w arr[l]! do continue
        let prem := NCtx.arg w arr[l]! 0
        for l2 in [0 : arr.size] do
          if l2 == l then continue
          if ← r.withContext (cheapDefEq prem arr[l2]!) then
            hit := some (l, l2)
            break
      if let some (l, l2) := hit then
        let rest := (List.range arr.size).filter (fun k => k != l && k != l2)
        let order := [l2, l] ++ rest
        let pm := c.perm sr order
        let a := NCtx.arg w arr[l]! 0
        let b := NCtx.arg w arr[l]! 1
        let restE := rest.map (arr[·]!)
        let rt := c.starL tr
        let src := c.starL sr
        let mid := c.starL (order.map (arr[·]!))
        let lr := c.starL restE
        let ty := if restE.isEmpty then c.mkEnt b rt else c.mkEnt (c.mkStar b lr) rt
        let g' ← newGoal r ty fun m =>
          c.transO src mid rt pm (if restE.isEmpty then c.lem ``nt_wand_l1 #[a, b, rt, m]
            else c.lem ``nt_wand_l #[a, b, lr, rt, m])
        sub := some ((← nativeGoal g').getD [g'])
  if sub.isSome then changed := true
  unless changed do return some [g]
  let mut out : List MVarId := pures
  match sub with
  | some o => out := out ++ o
  | none => if let some r := res then out := out ++ [r]
  for y in created.reverse do
    if let .mvar id ← instantiateMVars y then
      unless ← id.isAssigned do out := out ++ [id]
  return some out

def nativeOrNone (g : MVarId) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    let r ← nativeGoal g
    if r.isNone then s.restore
    return r
  catch _ =>
    s.restore
    return none

mutual

partial def driveOne (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (g : MVarId) :
    TacticM (List MVarId) := do
  if ← g.isAssigned then return []
  withExtra extra ((← nativeOrNone g).getD [g])

partial def withExtra (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (hs : List MVarId) : TacticM (List MVarId) := do
  match extra with
  | none => return hs
  | some e =>
    let mut out : List MVarId := []
    for h in hs do
      if ← h.isAssigned then continue
      setGoals [h]
      if ← tryTactic (evalTactic e) then
        for h2 in ← getUnsolvedGoals do
          out := out ++ (← driveOne extra h2)
      else
        out := out ++ [h]
    return out

end

def xsimplDriver (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  let mut out : List MVarId := []
  for g in ← getGoals do
    out := out ++ (← driveOne extra g)
  setGoals out

syntax "xsimpl_core_with " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| xsimpl_core_with $extra) => xsimplDriver (some extra)

syntax "xsimpl_core" : tactic
elab_rules : tactic
  | `(tactic| xsimpl_core) => xsimplDriver none

def affineEmp (c : NCtx) (g : MVarId) (l r : Expr) : MetaM Bool := do
  unless NCtx.isOp c.empOp r || NCtx.isOp c.empOp (← whnfR r) do return false
  let some aff ← affineInst? c.carrier | return false
  let pf ← mkAppOptM ``AffineSepLogic.entails_emp #[some c.carrier, some aff, some l]
  unless ← isDefEq (← inferType pf) (← g.getType) do return false
  g.assign pf
  return true

def xsimplClean : TacticM Unit := do
  let g ← getMainGoal
  let (g, done) ← g.withContext do
    match ← sepGoal? g with
    | some (g, c, l, r) => g.withContext do
      if ← closeRefl c g l r then return (g, true)
      if ← cheapAssumptionCore g then return (g, true)
      return (g, ← affineEmp c g l r)
    | none => return (g, ← cheapAssumptionCore g)
  replaceMainGoal (if done then [] else [g])

syntax "xsimpl_clean" : tactic
elab_rules : tactic
  | `(tactic| xsimpl_clean) => xsimplClean

syntax "xsimpl" : tactic
macro_rules
  | `(tactic| xsimpl) => `(tactic| (
      xsimpl_core
      all_goals (
        try xsimpl_clean
      )
    ))

end Sep.Xsimpl
