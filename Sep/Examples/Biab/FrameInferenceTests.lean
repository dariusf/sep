import Sep.HProp
import Sep.Xsimpl
import Sep.Examples.Biab.FrameInference

open Lean Meta Elab Tactic
open HProp Notation

instance UnitParams : Params where
  val := Unit

example {H1 H2 H3 H4 : HProp} : ∃ AntiFrame_head AntiFrame_tail Frame_head Frame_tail, H1 ✶ H2 ✶ (AntiFrame_head ✶ AntiFrame_tail) ==> H1 ✶ H3 ✶ H4 ✶ (Frame_head ✶ Frame_tail) := by
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  xsimpl_granular_frames

-- ============================================================
-- Frame Inference and Biabduction via xsimpl
-- (moved from Sep.Tests.XsimplTests, which cannot depend on this example)
-- ============================================================

set_option trace.xsimpl true

-- Basic Frame Inference
/--
trace: [xsimpl] Cancelling H1
[xsimpl] Granularly Framed: H2
[xsimpl] Cancelling H2
[xsimpl] Granularly Framed: H3
[xsimpl] Cancelling H3
-/
#guard_msgs in
example {H1 H2 H3 : HProp} : ∃ Frame, H1 ✶ H2 ✶ H3 ==> H1 ✶ Frame := by
  apply Exists.intro
  xsimpl_granular_frames

-- Biabduction (Simultaneous Frame and AntiFrame Inference)
/--
trace: [xsimpl] Cancelling H1
[xsimpl] Granularly Abduced: H3
[xsimpl] Cancelling H3
[xsimpl] Granularly Framed: H2
[xsimpl] Cancelling H2
-/
#guard_msgs in
example {H1 H2 H3 : HProp} : ∃ AntiFrame Frame, H1 ✶ H2 ✶ AntiFrame ==> H1 ✶ H3 ✶ Frame := by
  apply Exists.intro
  apply Exists.intro
  xsimpl_granular_frames
