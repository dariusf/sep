module

public import Sep.SepLogic
public import Mathlib.Tactic.GRewrite

public section

namespace SepLaws

universe u v

variable {α : Type u} {entails : α → α → Prop} {star : α → α → α} {emp : α} {pure : Prop → α}
  {ex : {A : Sort v} → (A → α) → α} {wand : α → α → α}
  [inst : SepLaws α entails star emp pure ex wand]

local infixr:61 " ∗ " => star
local infixr:60 " -∗ " => wand
local infixr:25 " ==> " => entails

include inst

theorem entails_imp_entails {H1 H1' H2 H2' : α} (h1 : H1' ==> H1) (h2 : H2 ==> H2') :
    (H1 ==> H2) → (H1' ==> H2') :=
  fun h => inst.entails_trans h1 (inst.entails_trans h h2)

theorem star_mono {H1 H1' H2 H2' : α} (h1 : H1 ==> H1') (h2 : H2 ==> H2') :
    (H1 ∗ H2) ==> (H1' ∗ H2') :=
  inst.entails_trans (inst.frame_l h1) (inst.frame_r h2)

theorem ex_mono {A : Sort v} {J K : A → α} (h : ∀ x, J x ==> K x) :
    ex J ==> ex K :=
  inst.ex_l fun x => inst.ex_r x (h x)

theorem wand_mono {H1 H1' H2 H2' : α} (h1 : H1' ==> H1) (h2 : H2 ==> H2') :
    (H1 -∗ H2) ==> (H1' -∗ H2') := by
  apply inst.wand_intro
  rw [inst.star_comm]
  exact inst.entails_trans (inst.frame_l h1) (inst.entails_trans (inst.wand_cancel H1 H2) h2)

end SepLaws
