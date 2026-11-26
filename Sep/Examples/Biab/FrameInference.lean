import Sep.FrameInference
import Sep.HProp.SepLogic

/-!
The biabduction phases used to live here, over `HProp.himpl` only.  They are now
stated over the `SepLogic` class in `Sep/FrameInference.lean`; this module only
re-exports them together with the `HProp` instance, so existing clients keep
working.
-/
