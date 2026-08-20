import Sep.Xsimpl

/-!
Tests for `xsimpl` on goals stated with the generic `SepLogic` notation
(`∗`, `-∗`, `==>`, `⌜⌝`, `emp`, `∃ₛ`) rather than the `HProp` notation.
-/

open SepLogic

instance UnitParamsGeneric : Params where
  val := Unit

-- Normalization

example {H : HProp} : H ∗ emp ==> H := by xsimpl

example {H : HProp} : H ==> emp ∗ H := by xsimpl

example {H1 H2 : HProp} : H1 ∗ emp ∗ H2 ==> H1 ∗ H2 := by xsimpl

-- Pure

example {P : Prop} {H : HProp} : ⌜P⌝ ∗ H ==> H := by xsimpl

example {P : Prop} {H : HProp} : H ∗ ⌜P⌝ ==> H := by xsimpl

example {P : Prop} {H : HProp} (hP : P) : H ==> ⌜P⌝ ∗ H := by xsimpl

-- Existentials, including multiple binders

example {A : Type} {a : A} {J : A → HProp} : J a ==> ∃ₛ x, J x := by xsimpl

example {A B : Type} {a : A} {b : B} {J : A → B → HProp} :
    J a b ==> ∃ₛ x y, J x y := by xsimpl

example {A : Type} {J : A → HProp} {H : HProp} :
    (∃ₛ x, J x) ∗ H ==> ∃ₛ x, J x ∗ H := by xsimpl

-- Cancellation

example {H1 H2 H3 : HProp} : H1 ∗ H2 ∗ H3 ==> H2 ∗ H3 ∗ H1 := by xsimpl

-- Wands

example {H1 H2 : HProp} : H1 ∗ (H1 -∗ H2) ==> H2 := by xsimpl

example {H1 H2 H3 : HProp} : H1 ∗ (H1 -∗ H2) ∗ H3 ==> H2 ∗ H3 := by xsimpl

-- Residual goals are handed back in the concrete logic's own notation

example {H1 H2 H3 H4 : HProp} (h : HProp.himpl (HProp.hstar H1 H3) H4) :
    H1 ∗ H2 ∗ H3 ==> H2 ∗ H4 := by xsimpl
