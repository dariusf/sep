-- https://github.com/verse-lab/yolo/blob/main/SPLean/Experiments/cancel100.lean

import Sep.Xsearch

open HProp Notation

namespace Bench.Cancel

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

variable [Params] (H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 H50 H51 H52 H53 H54 H55 H56 H57 H58 H59 H60 H61 H62 H63 H64 H65 H66 H67 H68 H69 H70 H71 H72 H73 H74 H75 H76 H77 H78 H79 H80 H81 H82 H83 H84 H85 H86 H87 H88 H89 H90 H91 H92 H93 H94 H95 H96 H97 H98 H99 H100 : HProp)

theorem q100 :
  H72 ✶ H22 ✶ H53 ✶ H37 ✶ H69 ✶ H2 ✶ H1 ✶ H34 ✶ H58 ✶ H5 ✶
  H56 ✶ H75 ✶ H87 ✶ H12 ✶ H45 ✶ H81 ✶ H93 ✶ H40 ✶ H83 ✶ H46 ✶
  H39 ✶ H59 ✶ H25 ✶ H60 ✶ H20 ✶ H38 ✶ H91 ✶ H49 ✶ H6 ✶ H14 ✶
  H67 ✶ H74 ✶ H50 ✶ H8 ✶ H79 ✶ H11 ✶ H27 ✶ H89 ✶ H42 ✶ H90 ✶
  H61 ✶ H4 ✶ H26 ✶ H71 ✶ H17 ✶ H19 ✶ H99 ✶ H13 ✶ H10 ✶ H97 ✶
  H66 ✶ H80 ✶ H18 ✶ H68 ✶ H82 ✶ H62 ✶ H78 ✶ H65 ✶ H44 ✶ H57 ✶
  H98 ✶ H41 ✶ H73 ✶ H95 ✶ H28 ✶ H32 ✶ H77 ✶ H86 ✶ H51 ✶ H54 ✶
  H23 ✶ H52 ✶ H7 ✶ H30 ✶ H16 ✶ H36 ✶ H88 ✶ H9 ✶ H85 ✶ H55 ✶
  H3 ✶ H96 ✶ H92 ✶ H33 ✶ H94 ✶ H15 ✶ H63 ✶ H29 ✶ H48 ✶ H84 ✶
  H35 ✶ H70 ✶ H64 ✶ H21 ✶ H47 ✶ H24 ✶ H100 ✶ H43 ✶ H31 ✶ H76
  ==>
  H52 ✶ H85 ✶ H35 ✶ H57 ✶ H43 ✶ H7 ✶ H15 ✶ H75 ✶ H41 ✶ H79 ✶
  H60 ✶ H42 ✶ H22 ✶ H37 ✶ H21 ✶ H25 ✶ H31 ✶ H98 ✶ H89 ✶ H100 ✶
  H53 ✶ H56 ✶ H46 ✶ H51 ✶ H32 ✶ H36 ✶ H17 ✶ H93 ✶ H1 ✶ H40 ✶
  H73 ✶ H34 ✶ H78 ✶ H39 ✶ H49 ✶ H70 ✶ H71 ✶ H74 ✶ H83 ✶ H24 ✶
  H64 ✶ H58 ✶ H92 ✶ H95 ✶ H86 ✶ H97 ✶ H82 ✶ H12 ✶ H16 ✶ H91 ✶
  H30 ✶ H69 ✶ H76 ✶ H18 ✶ H26 ✶ H67 ✶ H94 ✶ H80 ✶ H65 ✶ H4 ✶
  H19 ✶ H9 ✶ H14 ✶ H2 ✶ H50 ✶ H54 ✶ H77 ✶ H66 ✶ H27 ✶ H61 ✶
  H47 ✶ H28 ✶ H63 ✶ H72 ✶ H99 ✶ H88 ✶ H96 ✶ H10 ✶ H48 ✶ H3 ✶
  H87 ✶ H68 ✶ H23 ✶ H13 ✶ H20 ✶ H84 ✶ H33 ✶ H81 ✶ H38 ✶ H90 ✶
  H55 ✶ H29 ✶ H45 ✶ H8 ✶ H11 ✶ H44 ✶ H62 ✶ H6 ✶ H5 ✶ H59
  := by xsearch

end Bench.Cancel
