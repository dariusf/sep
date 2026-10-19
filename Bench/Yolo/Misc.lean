-- https://github.com/verse-lab/yolo/blob/main/SPLean/Experiments/Misc.lean

import Sep.Xsearch

open HProp Notation

namespace Bench.Misc

instance intParams : Params where
  val := Int

variable (H1 H2 H3 H4 H5 H8 H11 H22 H23 H24 H25 H33 : HProp) (x : Loc)

theorem f :
  (H8 -✶ emp) ✶ H23 ✶ H33 ✶ ((H1 -✶ (x ↦ (2 : Int))) -✶ H5) ✶ (H1 -✶ (x ↦ ((1 + 1 : Int)))) ✶ H24 ✶ H11 ✶ (H1 ✶ H2 ✶ ((H1 ✶ H3) -✶ (H4 -✶ H5))) ✶ (H2 -✶ H3) ✶ H4 ✶ H25
  ==> H5 ✶ ((H11 -✶ H8) -✶ H5) ✶ H23 ✶ H24 ✶ H25 ✶ (H22 -✶ H22) ✶ H33 ✶ (H11 -✶ H11)
  := by xsearch

end Bench.Misc
