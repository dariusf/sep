module

public import Lean

public section

open Lean Meta Elab Tactic

universe u v


/-- The fragment of a separation logic that `xsimpl` reasons about. -/
@[univ_out_params]
class SepLaws (α : Type u)
    (entails : outParam (α → α → Prop))
    (star : outParam (α → α → α))
    (emp : outParam α)
    (pure : outParam (Prop → α))
    (ex : outParam ({A : Sort v} → (A → α) → α))
    (wand : outParam (α → α → α)) : Prop where
  star_comm : ∀ H1 H2, star H1 H2 = star H2 H1
  star_assoc : ∀ H1 H2 H3, star (star H1 H2) H3 = star H1 (star H2 H3)
  star_emp_l : ∀ H, star emp H = H
  star_emp_r : ∀ H, star H emp = H
  star_ex : ∀ {A : Sort v} (J : A → α) (H : α),
    star (ex J) H = ex (fun x => star (J x) H)
  entails_refl : ∀ H, entails H H
  entails_trans : ∀ {H1 H2 H3}, entails H1 H2 → entails H2 H3 → entails H1 H3
  entails_antisym : ∀ {H1 H2}, entails H1 H2 → entails H2 H1 → H1 = H2
  frame_r : ∀ {H P1 P2}, entails P1 P2 → entails (star H P1) (star H P2)
  frame_l : ∀ {H P1 P2}, entails P1 P2 → entails (star P1 H) (star P2 H)
  ex_l : ∀ {A : Sort v} {J : A → α} {H}, (∀ x, entails (J x) H) → entails (ex J) H
  ex_r : ∀ {A : Sort v} (x : A) {J : A → α} {H}, entails H (J x) → entails H (ex J)
  pure_l : ∀ {P : Prop} {H1 H2}, (P → entails H1 H2) → entails (star (pure P) H1) H2
  pure_r : ∀ {P : Prop} {H1 H2}, P → entails H1 H2 → entails H1 (star (pure P) H2)
  wand_cancel : ∀ H1 H2, entails (star H1 (wand H1 H2)) H2
  wand_intro : ∀ {H1 P1 P2}, entails (star H1 P1) P2 → entails H1 (wand P1 P2)
  wand_curry : ∀ H1 H2 H3, wand (star H1 H2) H3 = wand H1 (wand H2 H3)

/-- A separation logic whose resources may be discarded. -/
@[univ_out_params]
class AffineSepLaws (α : Type u)
    (entails : outParam (α → α → Prop))
    (star : outParam (α → α → α))
    (emp : outParam α)
    (pure : outParam (Prop → α))
    (ex : outParam ({A : Sort v} → (A → α) → α))
    (wand : outParam (α → α → α)) : Prop
    extends SepLaws α entails star emp pure ex wand where
  entails_emp : ∀ H, entails H emp

namespace Sep.Xsimpl

section Lemmas

variable {α : Type u} {entails : α → α → Prop} {star : α → α → α} {emp : α} {pure : Prop → α}
  {ex : {A : Sort v} → (A → α) → α} {wand : α → α → α}
  [inst : SepLaws α entails star emp pure ex wand]

local infixr:61 " ∗ " => star
local infixr:60 " -∗ " => wand
local infixr:25 " ==> " => entails
local notation:max "⌜" P "⌝" => pure P

include inst

-- ============================================================
-- Helper lemmas for star AC reasoning
-- ============================================================

/-- `∗` is associative, so `ac_rfl` can normalise `∗`-trees. -/
instance : Std.Associative (α := α) star := ⟨inst.star_assoc⟩

/-- `∗` is commutative, so `ac_rfl` can normalise `∗`-trees. -/
instance : Std.Commutative (α := α) star := ⟨inst.star_comm⟩

theorem hstar_left_comm (H1 H2 H3 : α) :
    H1 ∗ (H2 ∗ H3) = H2 ∗ (H1 ∗ H3) := by
  rw [← inst.star_assoc, inst.star_comm H1 H2, inst.star_assoc]

-- Used by MetaM to rewrite goal LHS or RHS
omit inst in
theorem himpl_lhs_eq {H1 H2 Hr : α} :
    H1 = H2 → (H2 ==> Hr) → (H1 ==> Hr) := by
  rintro rfl h; exact h

omit inst in
theorem himpl_rhs_eq {Hl H1 H2 : α} :
    H1 = H2 → (Hl ==> H1) → (Hl ==> H2) := by
  rintro rfl h; exact h

-- ============================================================
-- Extraction / instantiation helpers
-- ============================================================

theorem hstar_hexists_r {A : Sort v} (H : α) (J : A → α) :
    H ∗ ex J = ex (fun x => H ∗ J x) := by
  rw [inst.star_comm, inst.star_ex]; apply congrArg; funext x; rw [inst.star_comm]

theorem himpl_hexists_l_star {A : Sort v} {J : A → α} {H1 H2 : α} :
    (∀ x, J x ∗ H1 ==> H2) → (ex J ∗ H1 ==> H2) := by
  intro h; rw [inst.star_ex]; exact inst.ex_l h

theorem himpl_hpure_l {P : Prop} {H : α} :
    (P → emp ==> H) → (⌜P⌝ ==> H) := by
  intro h
  rw [show (⌜P⌝ : α) = ⌜P⌝ ∗ emp from (inst.star_emp_r _).symm]
  exact inst.pure_l h

theorem himpl_hexists_r_star {A : Sort v} (x : A) {H1 H2 : α} {J : A → α} :
    (H1 ==> J x ∗ H2) → (H1 ==> ex J ∗ H2) := by
  intro h; rw [inst.star_ex]; exact inst.ex_r x h

theorem himpl_hpure_r {P : Prop} {H : α} :
    P → (H ==> emp) → (H ==> ⌜P⌝) := by
  intro hP hH
  rw [show (⌜P⌝ : α) = ⌜P⌝ ∗ emp from (inst.star_emp_r _).symm]
  exact inst.pure_r hP hH

-- ============================================================
-- Cancellation
-- ============================================================

theorem himpl_cancel_rhs {H1 H2 : α} :
    (emp ==> H2) → (H1 ==> H1 ∗ H2) := by
  intro h
  have hf : H1 ∗ emp ==> H1 ∗ H2 := inst.frame_r h
  rw [inst.star_emp_r] at hf
  exact hf

theorem himpl_cancel_lhs {H1 H2 : α} :
    (H2 ==> emp) → (H1 ∗ H2 ==> H1) := by
  intro h
  have hf : H1 ∗ H2 ==> H1 ∗ emp := inst.frame_r h
  rw [inst.star_emp_r] at hf
  exact hf

omit inst in
theorem sep_weaken_leftover [inst : AffineSepLaws α entails star emp pure ex wand] {H1 H2 : α} :
    (H1 ∗ H2) ==> H1 :=
  himpl_cancel_lhs (inst.entails_emp H2)

-- ============================================================
-- Wand cancellation
-- ============================================================

theorem himpl_wand_apply_lhs {H1 H2 Hl Hr : α} :
    (H2 ∗ Hl ==> Hr) → (H1 ∗ ((H1 -∗ H2) ∗ Hl) ==> Hr) := by
  intro h
  have h1 : H1 ∗ ((H1 -∗ H2) ∗ Hl) ==> H2 ∗ Hl := by
    rw [← inst.star_assoc]
    exact inst.frame_l (inst.wand_cancel H1 H2)
  exact inst.entails_trans h1 h

theorem himpl_wand_apply_lhs_emp {H1 H2 Hr : α} :
    (H2 ==> Hr) → (H1 ∗ (H1 -∗ H2) ==> Hr) :=
  fun h => inst.entails_trans (inst.wand_cancel H1 H2) h

end Lemmas

section PureLemmas

variable {α : Type u} {entails : α → α → Prop} {star : α → α → α} {emp : α} {pure : Prop → α}
  {ex : {A : Sort 0} → (A → α) → α} {wand : α → α → α}
  [inst : SepLaws.{u, 0} α entails star emp pure ex wand]

local infixr:61 " ∗ " => star
local notation:max "⌜" P "⌝" => pure P

include inst

/-- A pure conjunct is an existential over its proof. Only available when the
    logic's existentials range over `Prop` (i.e. at class universe `v = 0`). -/
theorem hstar_hpure_eq_hexists (P : Prop) (H : α) :
    ⌜P⌝ ∗ H = ex (fun _ : P => H) := by
  apply inst.entails_antisym
  · exact inst.pure_l fun hP => inst.ex_r hP (inst.entails_refl _)
  · exact inst.ex_l fun hP => inst.pure_r hP (inst.entails_refl _)

theorem hstar_hpure_r_eq_hexists (H : α) (P : Prop) :
    H ∗ ⌜P⌝ = ex (fun _ : P => H) := by
  rw [inst.star_comm, hstar_hpure_eq_hexists (inst := inst)]

end PureLemmas

end Sep.Xsimpl
