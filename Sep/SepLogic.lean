import Lean

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

end Sep.Xsimpl
