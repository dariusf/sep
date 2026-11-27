import Sep.HProp.SepLogic
import Sep.Xsimpl.Core
import Sep.FrameInference
import Sep.Tests.Notation

namespace SepLogicTests

universe v

structure AProp where
  p : Prop

namespace AProp

theorem eq_of_iff {a b : AProp} (h : a.p ↔ b.p) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact propext h

def tt : AProp := ⟨True⟩

def emp : AProp := tt

def star (a b : AProp) : AProp := ⟨a.p ∧ b.p⟩

def pure (P : Prop) : AProp := ⟨P⟩

def ex {A : Sort v} (J : A → AProp) : AProp := ⟨∃ x, (J x).p⟩

def wand (a b : AProp) : AProp := ⟨a.p → b.p⟩

def entails (a b : AProp) : Prop := a.p → b.p

end AProp

instance (priority := low) instAffineSepLawsAProp :
    AffineSepLaws.{0, v} AProp AProp.entails AProp.star AProp.emp AProp.pure AProp.ex
      AProp.wand where
  star_comm := fun _ _ => AProp.eq_of_iff ⟨And.symm, And.symm⟩
  star_assoc := fun _ _ _ => AProp.eq_of_iff and_assoc
  star_emp_l := fun _ => AProp.eq_of_iff ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  star_emp_r := fun _ => AProp.eq_of_iff ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
  star_ex := fun _ _ =>
    AProp.eq_of_iff ⟨fun ⟨⟨x, h⟩, hH⟩ => ⟨x, h, hH⟩, fun ⟨x, h, hH⟩ => ⟨⟨x, h⟩, hH⟩⟩
  entails_refl := fun _ h => h
  entails_trans := fun h1 h2 h => h2 (h1 h)
  entails_antisym := fun h1 h2 => AProp.eq_of_iff ⟨h1, h2⟩
  frame_r := fun h ⟨hH, hP⟩ => ⟨hH, h hP⟩
  frame_l := fun h ⟨hP, hH⟩ => ⟨h hP, hH⟩
  ex_l := fun h ⟨x, hx⟩ => h x hx
  ex_r := fun x _ _ h hH => ⟨x, h hH⟩
  pure_l := fun h ⟨hP, h1⟩ => h hP h1
  pure_r := fun hP h h1 => ⟨hP, h h1⟩
  wand_cancel := fun _ _ ⟨h, f⟩ => f h
  wand_intro := fun h h1 hP => h ⟨h1, hP⟩
  wand_curry := fun _ _ _ => AProp.eq_of_iff and_imp
  entails_emp := fun _ _ => trivial

instance instAffineSepLawsAPropType :
    AffineSepLaws.{0, 1} AProp AProp.entails AProp.star AProp.emp AProp.pure AProp.ex
      AProp.wand :=
  instAffineSepLawsAProp

local infixr:61 " ∗ " => AProp.star
local infixr:60 " -∗ " => AProp.wand
local infixr:25 " ==> " => AProp.entails
local notation:max "emp" => AProp.emp
local notation:max "⌜" P "⌝" => AProp.pure P

section Native

open AProp

example {P : AProp} : entails P emp := by xsimpl

example : entails emp emp := by xsimpl

example {P1 P2 : AProp} : entails (star P1 P2) P1 := by xsimpl

example {P1 P2 P3 : AProp} : entails (star P1 (star P2 P3)) P2 := by xsimpl

example {P : AProp} : entails P tt := by xsimpl

example {P1 P2 : AProp} : entails (star P1 P2) (star tt P2) := by xsimpl

example {P1 P2 : AProp} : entails (star P1 P2) (star P2 tt) := by xsimpl

example {P : AProp} {k : Nat} : entails P (star (pure (Nat.succ k = k + 1)) P) := by xsimpl

example {P : AProp} {f : Nat → Nat} {k : Nat} :
    entails (star P emp) (star (pure (f (Nat.succ k) = f (k + 1))) P) := by xsimpl

example {P : AProp} : P ==> emp := by xsimpl

example {P1 P2 : AProp} : P1 ∗ P2 ==> P1 := by xsimpl

example {P : AProp} : P ==> AProp.tt := by xsimpl

example {P1 P2 : AProp} : P1 ∗ P2 ==> AProp.tt ∗ P2 := by xsimpl

example {P : AProp} {k : Nat} : P ==> ⌜Nat.succ k = k + 1⌝ ∗ P := by xsimpl

example {P : AProp} : P ∗ AProp.emp ==> P ∗ emp := by xsimpl

end Native

section Frame

open AProp

@[refl] theorem entails_refl (a : AProp) : entails a a := fun h => h

theorem ramify {P Q R S F : AProp} (h1 : entails P (star Q F)) (h2 : entails (star R F) S) :
    entails (star P R) (star S Q) := fun ⟨hp, hr⟩ => ⟨h2 ⟨hr, (h1 hp).2⟩, (h1 hp).1⟩

example {P R : AProp} : entails (star P R) (star (star R emp) P) := by
  apply ramify
  case h1 => xsimpl_granular_frames
  with_reducible rfl

end Frame

end SepLogicTests

section HProp

/-!
Tests for `xsimpl` on goals stated with the notation of `Sep.Tests.Notation`
(`∗`, `-∗`, `==>`, `⌜⌝`, `emp`, `∃ₛ`) rather than the `HProp` notation.
-/

namespace SepLogicHPropTests

open Sep.Tests.Notation

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

end SepLogicHPropTests

end HProp
