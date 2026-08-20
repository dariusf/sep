import Sep.FmapTactics

open Finmap

variable {α β : Type} [DecidableEq α]

namespace Disjoint

example (m1 m2 m3 m4 m5 : Finmap fun _ : α => β) :
    m1 = m2 ∪ m3 →
    Finmap.Disjoint m2 m3 →
    Finmap.disjoint_3 m1 m4 m5 →
    Finmap.disjoint_3 m3 m2 m5 ∧ Finmap.Disjoint m4 m5 := by
  intros; fmap_disjoint

example (m1 m2 : Finmap fun _ : α => β) :
    Disjoint m1 m2 → Disjoint m2 m1 := by
  intros; fmap_disjoint

example (m1 m2 m3 : Finmap fun _ : α => β) :
    Disjoint m1 (m2 ∪ m3) →
    Disjoint m3 m1 := by
  intros; fmap_disjoint

example (m1 m2 m3 m4 : Finmap fun _ : α => β) :
    Disjoint (m1 ∪ m2) (m3 ∪ m4) →
    Disjoint m1 m3 ∧ Disjoint m1 m4 ∧ Disjoint m2 m3 ∧ Disjoint m2 m4 := by
  intros; fmap_disjoint

example (m1 m2 m3 : Finmap fun _ : α => β) :
    disjoint_3 m1 m2 m3 → Disjoint m2 m1 ∧ Disjoint m3 m2 ∧ Disjoint m3 m1 := by
  intros; fmap_disjoint

example (m1 m2 : Finmap fun _ : α => β) :
    Disjoint m1 m2 →
    Disjoint m1 ∅ ∧ Disjoint ∅ m2 := by
  intros; fmap_disjoint

example (m1 : Finmap fun _ : α => β) : Disjoint m1 ∅ := by
  fmap_disjoint

example (m1 m2 m3 m4 : Finmap fun _ : α => β) :
    Disjoint m1 m2 →
    Disjoint m1 m3 →
    Disjoint m1 m4 →
    Disjoint m1 (m2 ∪ (m3 ∪ m4)) := by
  intros; fmap_disjoint

example (m1 m2 m3 m4 : Finmap fun _ : α => β) :
    Disjoint (m1 ∪ (m2 ∪ m3)) m4 →
    Disjoint m1 m4 ∧ Disjoint m2 m4 ∧ Disjoint m3 m4 := by
  intros; fmap_disjoint

example (m1 m2 m3 m4 : Finmap fun _ : α => β) :
    disjoint_3 m1 m2 m3 →
    Disjoint m1 m4 →
    Disjoint m2 m4 →
    Disjoint m3 m4 →
    disjoint_3 (m1 ∪ m4) m2 m3 := by
  intros; fmap_disjoint

example (h hf hp hx : Finmap fun _ : α => β) :
    hf ∪ hp = h →
    Disjoint hf hx →
    Disjoint hp hx →
    Disjoint (hf ∪ hp) hx := by
  intros; fmap_disjoint

example (h hf hp hx : Finmap fun _ : α => β) :
    h = hf ∪ hp →
    Disjoint h hx →
    Disjoint hx hp ∧ Disjoint hx hf := by
  intros; fmap_disjoint

example (h hf hp hx : Finmap fun _ : α => β) :
    hf ∪ hp = h →
    Disjoint h hx →
    Disjoint hx hp ∧ Disjoint hx hf := by
  intros; fmap_disjoint

end Disjoint

namespace Equality

theorem fmap_eq_demo (m1 m2 m3 m4 m5 : Finmap fun _ : α => β) :
    Finmap.disjoint_3 m1 m2 m3 →
    Finmap.disjoint_3 ((m1 ∪ m2) ∪ m3) m4 m5 →
    m1 = m2 ∪ m3 →
    (m4 ∪ m1) ∪ m5 = ((m2 ∪ m5) ∪ m4) ∪ m3 := by
  intros; fmap_eq

example (m1 m2 : Finmap fun _ : α => β) :
    Disjoint m1 m2 →
    m1 ∪ m2 = m2 ∪ m1 := by
  intros; fmap_eq

example (m1 m2 m3 : Finmap fun _ : α => β) :
    Disjoint m1 m2 → Disjoint m1 m3 → Disjoint m2 m3 →
    m1 ∪ (m2 ∪ m3) = m2 ∪ (m3 ∪ m1) := by
  intros; fmap_eq

example (m1 m2 m3 m4 : Finmap fun _ : α => β) :
    Disjoint m1 m2 → Disjoint m1 m3 → Disjoint m1 m4 →
    m1 ∪ (m2 ∪ (m3 ∪ m4)) = m2 ∪ (m3 ∪ (m4 ∪ m1)) := by
  intros; fmap_eq

example (m1 m2 m3 m4 : Finmap fun _ : α => β) :
    disjoint_3 m1 m2 m3 → Disjoint (m1 ∪ (m2 ∪ m3)) m4 →
    (m1 ∪ m2) ∪ (m3 ∪ m4) = m4 ∪ (m3 ∪ (m2 ∪ m1)) := by
  intros; fmap_eq

example (m1 m2 m3 : Finmap fun _ : α => β) :
    m2 = m3 →
    m1 ∪ m2 = m1 ∪ m3 := by
  intros; fmap_eq

example (m1 m2 m3 : Finmap fun _ : α => β) :
    Disjoint m1 m2 →
    m1 ∪ (m2 ∪ m3) = m2 ∪ (m1 ∪ m3) := by
  intros; fmap_eq

example (m1 m2 m3 m4 : Finmap fun _ : α => β) :
    Disjoint m1 m2 → Disjoint m1 m3 →
    m1 ∪ (m2 ∪ (m3 ∪ m4)) = m2 ∪ (m3 ∪ (m1 ∪ m4)) := by
  intros; fmap_eq

example (a b c d : Finmap fun _ : α => β) :
    disjoint_3 a b c → Disjoint (a ∪ (b ∪ c)) d →
    a ∪ (b ∪ (c ∪ d)) = d ∪ (c ∪ (b ∪ a)) := by
  intros; fmap_eq

example (m1 m2 m3 : Finmap fun _ : α => β) :
    m1 = m2 →
    Disjoint m2 m3 →
    m1 ∪ m3 = m3 ∪ m2 := by
  intros; fmap_eq

example (m1 m2 : Finmap fun _ : α => β) :
    Disjoint m1 m2 →
    (m1 ∪ ∅) ∪ m2 = m2 ∪ m1 := by
  intros; fmap_eq

example (h1 hp hrest : Finmap fun _ : α => β) :
    h1 = hrest ∪ hp →
    Disjoint hrest hp →
    h1 = hp ∪ hrest := by
  intros; fmap_eq

example (h1 hp hrest : Finmap fun _ : α => β) :
    hrest ∪ hp = h1 →
    Disjoint hrest hp →
    h1 = hp ∪ hrest := by
  intros; fmap_eq

example (hp hrest : Finmap fun _ : α => β) :
    Disjoint hrest hp →
    let h1 := hrest ∪ hp
    h1 = hp ∪ hrest := by
  intro hd h1
  have hunion : h1 = hrest ∪ hp := rfl
  rw [hunion] -- let binding needs a manual step
  fmap_eq

example (h_after p_frame h1 h2 : Finmap fun _ : α => β) :
    h_after = p_frame ∪ h1 →
    Disjoint p_frame h1 →
    Disjoint p_frame h2 →
    Disjoint h1 h2 →
    h_after ∪ h2 = h1 ∪ (h2 ∪ p_frame) := by
  intros; fmap_eq

example (h_after p_frame h1 : Finmap fun _ : α => β) :
    p_frame ∪ h1 = h_after →
    Disjoint p_frame h1 →
    h1 ∪ p_frame = h_after := by
  intros; fmap_eq

end Equality
