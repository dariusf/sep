import Sep.HProp
import Sep.Xsearch

open HProp Notation

namespace Bench

variable [Params]

def hor (H1 H2 : HProp) : HProp := fun h => H1 h ∨ H2 h

theorem hor_mono {H1 H2 H3 H4 : HProp} (h13 : H1 ==> H3) (h24 : H2 ==> H4) :
    hor H1 H2 ==> hor H3 H4 := by
  intro h hh
  rcases hh with hh | hh
  · exact Or.inl (h13 h hh)
  · exact Or.inr (h24 h hh)

theorem sumElim_mono {α β : Type} {f1 f2 : α → HProp} {g1 g2 : β → HProp}
    (hf : ∀ a, f1 a ==> f2 a) (hg : ∀ b, g1 b ==> g2 b) :
    ∀ s, Sum.elim f1 g1 s ==> Sum.elim f2 g2 s
  | .inl a => hf a
  | .inr b => hg b

def Mono {α : Type} (F : (α → HProp) → α → HProp) : Prop :=
  ∀ X Y : α → HProp, (∀ a, X a ==> Y a) → ∀ a, F X a ==> F Y a

def lfp {α : Type} (F : (α → HProp) → α → HProp) : α → HProp :=
  fun a h => ∀ X : α → HProp, (∀ b, F X b ==> X b) → X a h

theorem lfp_pre {α : Type} (F : (α → HProp) → α → HProp) (hF : Mono F) (a : α) :
    F (lfp F) a ==> lfp F a := by
  intro h hh X hX
  have hsub : ∀ b, lfp F b ==> X b := by
    intro b hb hhb
    exact hhb X hX
  exact hX a h (hF (lfp F) X hsub a h hh)

theorem lfp_post {α : Type} (F : (α → HProp) → α → HProp) (hF : Mono F) (a : α) :
    lfp F a ==> F (lfp F) a := by
  intro h hh
  exact hh (fun b => F (lfp F) b)
    (fun b => hF (F (lfp F)) (lfp F) (fun c => lfp_pre F hF c) b)

theorem lfp_unfold {α : Type} (F : (α → HProp) → α → HProp) (hF : Mono F) :
    lfp F = F (lfp F) := by
  funext a
  exact himpl_antisym (lfp_post F hF a) (lfp_pre F hF a)

syntax "hmono" : tactic

macro_rules
  | `(tactic| hmono) => `(tactic| (
      intro X Y hXY a
      try (casesm* _ ⊕ _)
      all_goals (try simp only [Sum.elim_inl, Sum.elim_inr])
      all_goals (try dsimp only)
      repeat' first
        | exact hXY _
        | exact HProp.himpl_refl _
        | apply Bench.hor_mono
        | apply HProp.himpl_frame_lr
        | (apply HProp.himpl_hexists; intro _)))

end Bench
