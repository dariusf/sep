import Sep.Xsimpl

open HProp Notation

namespace Sep

variable [Params]

def segC (c : Loc → Loc → HProp) : Nat → Loc → Loc → HProp
  | 0, x, y => ⌈x = y⌉
  | n + 1, x, y => ∃✶ u, c x u ✶ segC c n u y

def segI (c : Loc → Loc → HProp) (n : Int) (x y : Loc) : HProp :=
  ⌈0 ≤ n⌉ ✶ segC c n.toNat x y

theorem segC_join (c : Loc → Loc → HProp) (m n : Nat) (x y z : Loc) :
    segC c m x y ✶ segC c n y z ==> segC c (m + n) x z := by
  induction m generalizing x with
  | zero =>
    rw [Nat.zero_add]
    show ⌈x = y⌉ ✶ segC c n y z ==> segC c n x z
    refine HProp.himpl_hstar_hpure_l (fun h => ?_)
    subst h
    exact HProp.himpl_refl _
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    show (∃✶ u, c x u ✶ segC c m u y) ✶ segC c n y z ==> ∃✶ u, c x u ✶ segC c (m + n) u z
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun u => ?_)
    refine HProp.himpl_hexists_r u ?_
    rw [HProp.hstar_assoc]
    exact HProp.himpl_frame_r (ih u)

theorem segC_split (c : Loc → Loc → HProp) (m n : Nat) (x z : Loc) :
    segC c (m + n) x z ==> ∃✶ y, segC c m x y ✶ segC c n y z := by
  induction m generalizing x with
  | zero =>
    rw [Nat.zero_add]
    refine HProp.himpl_hexists_r x ?_
    show segC c n x z ==> ⌈x = x⌉ ✶ segC c n x z
    exact HProp.himpl_hstar_hpure_r rfl (HProp.himpl_refl _)
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    show (∃✶ u, c x u ✶ segC c (m + n) u z) ==> ∃✶ y, (∃✶ u, c x u ✶ segC c m u y) ✶ segC c n y z
    refine HProp.himpl_hexists_l (fun u => ?_)
    refine HProp.himpl_trans (HProp.himpl_frame_r (ih u)) ?_
    rw [HProp.hstar_comm, HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun y => ?_)
    refine HProp.himpl_hexists_r y ?_
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_r u ?_
    xsimpl

theorem segI_cell (c : Loc → Loc → HProp) (x y : Loc) : c x y ==> segI c 1 x y := by
  show c x y ==> ⌈(0 : Int) ≤ 1⌉ ✶ segC c (0 + 1) x y
  refine HProp.himpl_hstar_hpure_r (by omega) ?_
  show c x y ==> ∃✶ u, c x u ✶ ⌈u = y⌉
  refine HProp.himpl_hexists_r y ?_
  rw [HProp.hstar_comm]
  exact HProp.himpl_hstar_hpure_r rfl (HProp.himpl_refl _)

theorem segI_uncell (c : Loc → Loc → HProp) (x y : Loc) : segI c 1 x y ==> c x y := by
  show ⌈(0 : Int) ≤ 1⌉ ✶ (∃✶ u, c x u ✶ ⌈u = y⌉) ==> c x y
  refine HProp.himpl_hstar_hpure_l (fun _ => ?_)
  refine HProp.himpl_hexists_l (fun u => ?_)
  rw [HProp.hstar_comm]
  refine HProp.himpl_hstar_hpure_l (fun h => ?_)
  subst h
  exact HProp.himpl_refl _

theorem segI_zero_intro (c : Loc → Loc → HProp) (x y : Loc) (h : x = y) :
    (emp : HProp) ==> segI c 0 x y := by
  show (emp : HProp) ==> ⌈(0 : Int) ≤ 0⌉ ✶ ⌈x = y⌉
  refine HProp.himpl_hstar_hpure_r (by omega) ?_
  exact HProp.himpl_hempty_hpure h

theorem segI_zero_elim (c : Loc → Loc → HProp) (n : Int) (x y : Loc) (hn : n = 0) :
    segI c n x y ==> ⌈x = y⌉ := by
  subst hn
  show ⌈(0 : Int) ≤ 0⌉ ✶ ⌈x = y⌉ ==> ⌈x = y⌉
  exact HProp.himpl_hstar_hpure_l (fun _ => HProp.himpl_refl _)

theorem segI_join (c : Loc → Loc → HProp) (a b : Int) (x y z : Loc) :
    segI c a x y ✶ segI c b y z ==> segI c (a + b) x z := by
  show (⌈0 ≤ a⌉ ✶ segC c a.toNat x y) ✶ (⌈0 ≤ b⌉ ✶ segC c b.toNat y z) ==>
    ⌈0 ≤ a + b⌉ ✶ segC c (a + b).toNat x z
  rw [HProp.hstar_assoc]
  refine HProp.himpl_hstar_hpure_l (fun ha => ?_)
  rw [HProp.hstar_comm, HProp.hstar_assoc]
  refine HProp.himpl_hstar_hpure_l (fun hb => ?_)
  refine HProp.himpl_hstar_hpure_r (by omega) ?_
  rw [HProp.hstar_comm, show (a + b).toNat = a.toNat + b.toNat by omega]
  exact segC_join c a.toNat b.toNat x y z

theorem segI_split (c : Loc → Loc → HProp) (n a b : Int) (x z : Loc)
    (hn : n = a + b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    segI c n x z ==> ∃✶ y, segI c a x y ✶ segI c b y z := by
  show ⌈0 ≤ n⌉ ✶ segC c n.toNat x z ==> ∃✶ y, (⌈0 ≤ a⌉ ✶ segC c a.toNat x y) ✶
    (⌈0 ≤ b⌉ ✶ segC c b.toNat y z)
  refine HProp.himpl_hstar_hpure_l (fun _ => ?_)
  rw [show n.toNat = a.toNat + b.toNat by omega]
  refine HProp.himpl_trans (segC_split c a.toNat b.toNat x z) ?_
  refine HProp.himpl_hexists_l (fun y => ?_)
  refine HProp.himpl_hexists_r y ?_
  rw [HProp.hstar_assoc]
  refine HProp.himpl_hstar_hpure_r ha ?_
  exact HProp.himpl_frame_r (HProp.himpl_hstar_hpure_r hb (HProp.himpl_refl _))

theorem segI_cong (c : Loc → Loc → HProp) (a b : Int) (x y : Loc) (h : a = b) :
    segI c a x y ==> segI c b x y := by
  subst h
  exact HProp.himpl_refl _

end Sep
