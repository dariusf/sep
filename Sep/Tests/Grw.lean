import Sep.GrwSepLogic
import Sep.Reordering
import Sep.GrwHProp
import Sep.Tests.Notation

namespace Sep.Grw.Tests

open Sep.Tests.Notation

local notation "α" => HProp

variable [Params]

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
example (law : ∀ n, F n ==> G n) : HProp.hexists F ∗ A ==> HProp.hexists G ∗ A := by
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

/-! ## At a concrete instance -/

namespace Sep.Xsimpl

open HProp Notation

variable [Params] (A B C X : HProp)

example (law : A ==> B) (h : C ✶ B ==> X) : C ✶ A ==> X := by
  grw [law]; exact h

example (law : A ==> B) : C ✶ A ==> B ✶ C := by
  grw [law]
  xsimpl

end Sep.Xsimpl
