import Sep.SepLogic
import Mathlib.Tactic.GRewrite

namespace SepLogic

open scoped SepLogic

universe u v

variable {α : Type u} [SepLogic α]

attribute [refl] SepLogic.entails_refl

instance : Trans (SepLogic.Entails (α := α)) SepLogic.Entails SepLogic.Entails :=
  ⟨SepLogic.entails_trans⟩

@[gcongr]
theorem entails_imp_entails {H1 H1' H2 H2' : α} (h1 : H1' ==> H1) (h2 : H2 ==> H2') :
    (H1 ==> H2) → (H1' ==> H2') :=
  fun h => entails_trans h1 (entails_trans h h2)

@[gcongr]
theorem star_mono {H1 H1' H2 H2' : α} (h1 : H1 ==> H1') (h2 : H2 ==> H2') :
    (H1 ∗ H2) ==> (H1' ∗ H2') :=
  entails_trans (frame_l h1) (frame_r h2)

@[gcongr]
theorem ex_mono {A : Sort v} {J K : A → α} (h : ∀ x, J x ==> K x) :
    SepLogic.ex J ==> SepLogic.ex K :=
  ex_l fun x => ex_r x (h x)

@[gcongr]
theorem wand_mono {H1 H1' H2 H2' : α} (h1 : H1' ==> H1) (h2 : H2 ==> H2') :
    (H1 -∗ H2) ==> (H1' -∗ H2') := by
  refine wand_intro ?_
  rw [star_comm]
  exact entails_trans (frame_l h1) (entails_trans (wand_cancel H1 H2) h2)

end SepLogic
