import Sep.Xsearch
open HProp Notation

namespace XsearchTests

section Fix
variable [Params]

def hor (H1 H2 : HProp) : HProp := fun h => H1 h ∨ H2 h

theorem hor_mono {H1 H2 H3 H4 : HProp} (h13 : H1 ==> H3) (h24 : H2 ==> H4) :
    hor H1 H2 ==> hor H3 H4 := by
  intro h hh
  rcases hh with hh | hh
  · exact Or.inl (h13 h hh)
  · exact Or.inr (h24 h hh)

def Mono {α : Type} (F : (α → HProp) → α → HProp) : Prop :=
  ∀ X Y : α → HProp, (∀ a, X a ==> Y a) → ∀ a, F X a ==> F Y a

def lfp {α : Type} (F : (α → HProp) → α → HProp) : α → HProp :=
  fun a h => ∀ X : α → HProp, (∀ b, F X b ==> X b) → X a h

theorem lfp_pre {α : Type} (F : (α → HProp) → α → HProp) (hF : Mono F) (a : α) :
    F (lfp F) a ==> lfp F a := by
  intro h hh X hX
  exact hX a h (hF (lfp F) X (fun b hb hhb => hhb X hX) a h hh)

theorem lfp_post {α : Type} (F : (α → HProp) → α → HProp) (hF : Mono F) (a : α) :
    lfp F a ==> F (lfp F) a := by
  intro h hh
  exact hh (fun b => F (lfp F) b) (fun b => hF (F (lfp F)) (lfp F) (fun c => lfp_pre F hF c) b)

theorem lfp_unfold {α : Type} (F : (α → HProp) → α → HProp) (hF : Mono F) :
    lfp F = F (lfp F) :=
  funext fun a => himpl_antisym (lfp_post F hF a) (lfp_pre F hF a)

end Fix

instance : Params where
  val := Int

def f_ls (X : Nat × Nat → HProp) (p : Nat × Nat) : HProp :=
  hor (⌈p.1 = p.2⌉ ✶ emp)
    (∃✶ u : Nat, ⌈p.1 ≠ p.2⌉ ✶ (⌈p.1 ≠ 0⌉ ✶ p.1 ↦ (u : Int)) ✶ X (u, p.2))

theorem m_ls : Mono f_ls := by
  intro X Y hXY a
  apply hor_mono (himpl_refl _)
  apply himpl_hexists; intro u
  exact himpl_frame_r (himpl_frame_r (hXY _))

def p_ls (a b : Nat) : HProp := lfp f_ls (a, b)

@[xsearch_unfold] theorem e_ls (a b : Nat) :
    p_ls a b = hor (⌈a = b⌉ ✶ emp) (∃✶ u : Nat, ⌈a ≠ b⌉ ✶ (⌈a ≠ 0⌉ ✶ a ↦ (u : Int)) ✶ p_ls u b) :=
  congrFun (lfp_unfold f_ls m_ls) (a, b)

example (x y z : Nat) :
    ⌈x ≠ 0⌉ ✶ x ↦ (y : Int) ✶ ⌈y ≠ 0⌉ ✶ y ↦ (z : Int) ✶ ⌈z ≠ 0⌉ ✶ z ↦ (0 : Int) ==> p_ls x 0 := by
  xsearch

example (x y : Nat) : p_ls x y ✶ p_ls y 0 ==> p_ls x 0 := by
  xsearch


def f_rlist (X : Nat × Nat → HProp) (p : Nat × Nat) : HProp :=
  hor (⌈0 ≠ p.1⌉ ✶ ⌈p.1 ≠ 0⌉ ✶ p.1 ↦ (p.2 : Int))
    (∃✶ xp : Nat, ⌈0 ≠ xp⌉ ✶ (⌈xp ≠ 0⌉ ✶ xp ↦ (p.2 : Int)) ✶ X (p.1, xp))

theorem m_rlist : Mono f_rlist := by
  intro X Y hXY a
  apply hor_mono (himpl_refl _)
  apply himpl_hexists; intro xp
  exact himpl_frame_r (himpl_frame_r (hXY _))

def p_rlist (a b : Nat) : HProp := lfp f_rlist (a, b)

@[xsearch_unfold] theorem e_rlist (a b : Nat) :
    p_rlist a b = hor (⌈0 ≠ a⌉ ✶ ⌈a ≠ 0⌉ ✶ a ↦ (b : Int))
      (∃✶ xp : Nat, ⌈0 ≠ xp⌉ ✶ (⌈xp ≠ 0⌉ ✶ xp ↦ (b : Int)) ✶ p_rlist a xp) :=
  congrFun (lfp_unfold f_rlist m_rlist) (a, b)

example (x y z : Nat) : ⌈x ≠ 0⌉ ✶ x ↦ (y : Int) ✶ p_rlist y z ==> p_rlist x z := by
  xsearch

end XsearchTests
