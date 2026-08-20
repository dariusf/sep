import Sep.HProp
import Sep.SepLogic

open Lean Meta Elab Tactic

/-!
# `HProp` as a `SepLogic`

The `xsimpl` tactic itself lives in `Sep/SepLogic.lean`, generically over the
`SepLogic` class. This file supplies the instance for `HProp` and the
fold/unfold bridge lemmas the tactic uses to translate `HProp` goals into class
form and back.
-/

namespace Sep.Xsimpl

variable [Params]

instance instSepLogicHProp [Params] : SepLogic HProp where
  star := HProp.hstar
  emp := HProp.hempty
  spure := HProp.hpure
  ex := HProp.hexists
  wand := HProp.hwand
  Entails := HProp.himpl
  star_comm := HProp.hstar_comm
  star_assoc := HProp.hstar_assoc
  star_emp_l := HProp.hstar_hempty_l
  star_emp_r := HProp.hstar_hempty_r
  star_ex := HProp.hstar_hexists
  entails_refl := HProp.himpl_refl
  entails_trans := HProp.himpl_trans
  entails_antisym := HProp.himpl_antisym
  frame_r := HProp.himpl_frame_r
  frame_l := HProp.himpl_frame_l
  ex_l := HProp.himpl_hexists_l
  ex_r := fun {_A} x {_J _H} h => HProp.himpl_hexists_r x h
  pure_l := HProp.himpl_hstar_hpure_l
  pure_r := HProp.himpl_hstar_hpure_r
  wand_cancel := HProp.hwand_cancel
  wand_intro := fun {H1 P1 _P2} h =>
    HProp.himpl_hwand_r (by rw [HProp.hstar_comm P1 H1]; exact h)
  wand_curry := HProp.hwand_curry_eq

-- ============================================================
-- Fold / unfold bridge
-- ============================================================

@[xsimpl_fold] theorem fold_hstar (H1 H2 : HProp) :
    HProp.hstar H1 H2 = SepLogic.star H1 H2 := rfl

@[xsimpl_fold] theorem fold_hempty :
    (HProp.hempty : HProp) = SepLogic.emp := rfl

@[xsimpl_fold] theorem fold_hpure (P : Prop) :
    (HProp.hpure P : HProp) = SepLogic.spure P := rfl

@[xsimpl_fold] theorem fold_hexists {A : Sort _} (J : A → HProp) :
    HProp.hexists J = SepLogic.ex J := rfl

@[xsimpl_fold] theorem fold_hwand (H1 H2 : HProp) :
    HProp.hwand H1 H2 = SepLogic.wand H1 H2 := rfl

@[xsimpl_fold] theorem fold_himpl (H1 H2 : HProp) :
    HProp.himpl H1 H2 = SepLogic.Entails H1 H2 := rfl

@[xsimpl_unfold_class] theorem unfold_star (H1 H2 : HProp) :
    SepLogic.star H1 H2 = HProp.hstar H1 H2 := rfl

@[xsimpl_unfold_class] theorem unfold_emp :
    (SepLogic.emp : HProp) = HProp.hempty := rfl

@[xsimpl_unfold_class] theorem unfold_spure (P : Prop) :
    (SepLogic.spure P : HProp) = HProp.hpure P := rfl

@[xsimpl_unfold_class] theorem unfold_ex {A : Sort _} (J : A → HProp) :
    SepLogic.ex J = HProp.hexists J := rfl

@[xsimpl_unfold_class] theorem unfold_wand (H1 H2 : HProp) :
    SepLogic.wand H1 H2 = HProp.hwand H1 H2 := rfl

@[xsimpl_unfold_class] theorem unfold_entails (H1 H2 : HProp) :
    SepLogic.Entails H1 H2 = HProp.himpl H1 H2 := rfl

-- ============================================================
-- Compatibility layer for `HProp`-specific clients
-- ============================================================

/-- Parse a star chain stated with either the `HProp` constants or the
    `SepLogic` class operations. -/
partial def parseHstar (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, H1, H2]) => H1 :: parseHstar H2
  | (``HProp.hempty, _) => []
  | (``SepLogic.star, #[_, _, H1, H2]) => H1 :: parseHstar H2
  | (``SepLogic.emp, _) => []
  | _ => [e]

end Sep.Xsimpl
