import Sep.GrwSepLogic
import Sep.Reordering
import Sep.GrwHProp

open scoped SepLogic

namespace Sep.Grw.Tests

universe u

variable {α : Type u} [SepLogic α]

section Basic
variable (A B C D X : α) (F G : Nat → α)

-- Direction
example (law : A ==> B) (h : B ==> X) : A ==> X := by
  grw [law]
  exact h -- this asserts what the goal is exactly

example (law : A ==> B) (h : X ==> A) : X ==> B := by
  grw [← law]
  exact h

-- Under ∗
example (law : A ==> B) (h : C ∗ (B ∗ D) ==> X) : C ∗ (A ∗ D) ==> X := by
  grw [law]; exact h

example (law : A ==> B) (h : X ==> (C ∗ A) ∗ D) : X ==> (C ∗ B) ∗ D := by
  grw [← law]; exact h

-- Under wand, which is contravariant in its first argument
example (law : A ==> B) (h : (A -∗ C) ==> X) : (B -∗ C) ==> X := by
  grw [← law]; exact h

example (law : A ==> B) (h : (C -∗ B) ==> X) : (C -∗ A) ==> X := by
  grw [law]; exact h

-- ∃
-- cannot rewrite under binders, but gcongr works
example (law : ∀ n, F n ==> G n) : SepLogic.ex F ∗ A ==> SepLogic.ex G ∗ A := by
  gcongr
  exact law _

-- Multiple steps
example (l1 : A ==> B) (l2 : B ==> C) (h : C ∗ X ==> X) : A ∗ X ==> X := by
  grw [l1, l2]
  exact h

-- at h
example (law : A ==> B) (h : X ==> A ∗ C) : X ==> B ∗ C := by
  grw [law] at h
  exact h

-- reordering may sometimes be needed
example (law : A ∗ B ==> C) (h : C ∗ (D ∗ X) ==> X) : A ∗ (D ∗ (B ∗ X)) ==> X := by
  sl_perm (A ∗ B) ∗ (D ∗ X)
  grw [law]
  exact h

-- sl_pull reassociates to the right
example (law : C ∗ A ==> B) (h : D ∗ B ==> X) : C ∗ (D ∗ A) ==> X := by
  sl_pull D
  grw [law]
  exact h

end Basic

end Sep.Grw.Tests

/-! ## At a concrete instance

The same steps over `Sep.Xsimpl`'s `SepLogic HProp`.  Unlike for `sl_pull`, the
instance alone is *not* enough here: `gcongr` keys its lemmas on the constant a
goal's relation `whnf`s to, which at a concrete instance is that instance's own
entailment constant, and the second (existential) universe of `SepLogic` has to
be pinned so that the two sides of a `==>` agree on their instance.  Both are
done once and for all in `Sep/GrwHProp.lean`; the tests below are then
verbatim the generic ones. -/

namespace Sep.Xsimpl

variable [Params] (A B C X : HProp)

example (law : SepLogic.Entails A B) (h : SepLogic.Entails (C ∗ B) X) :
    SepLogic.Entails (C ∗ A) X := by
  grw [law]; exact h

example (law : SepLogic.Entails A B) : SepLogic.Entails (C ∗ A) (B ∗ C) := by
  grw [law]
  xsimpl

end Sep.Xsimpl
