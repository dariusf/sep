module

public import Sep.HProp
public import Sep.Xsimpl.Core
public meta import Lean

public section

open Lean Meta Elab Tactic

/-!
# `HProp` as a separation logic

The `xsimpl` tactic itself lives in `Sep/Xsimpl/Core.lean`, generically over the
`SepLaws` class. This file supplies the instance for `HProp`.
-/

namespace Sep.Xsimpl

universe v

variable [Params]

instance (priority := low) instSepLawsHProp :
    SepLaws.{0, v} HProp HProp.himpl HProp.hstar HProp.hempty HProp.hpure HProp.hexists
      HProp.hwand where
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

instance instSepLawsHPropType :
    SepLaws.{0, 1} HProp HProp.himpl HProp.hstar HProp.hempty HProp.hpure HProp.hexists
      HProp.hwand :=
  instSepLawsHProp

end Sep.Xsimpl
