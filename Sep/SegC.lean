import Sep.Xsimpl

open HProp Notation

namespace Sep

variable [Params]

def wseg {σ : Type} (c : σ → σ → Int → HProp) : Nat → Int → σ → σ → HProp
  | 0, n, s, t => ⌈s = t ∧ n = 0⌉
  | k + 1, n, s, t => ∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n - w) s' t

theorem wseg_nil {σ : Type} (c : σ → σ → Int → HProp) (n : Int) (s t : σ) (h : s = t) (hn : n = 0) :
    (emp : HProp) ==> wseg c 0 n s t := by
  show (emp : HProp) ==> ⌈s = t ∧ n = 0⌉
  exact HProp.himpl_hempty_hpure ⟨h, hn⟩

theorem wseg_zero_elim {σ : Type} (c : σ → σ → Int → HProp) (n : Int) (s t : σ) :
    wseg c 0 n s t ==> ⌈s = t ∧ n = 0⌉ := HProp.himpl_refl _

theorem wseg_cong {σ : Type} (c : σ → σ → Int → HProp) {k k' : Nat} {n n' : Int} {s s' t t' : σ}
    (hk : k = k') (hn : n = n') (hs : s = s') (ht : t = t') :
    wseg c k n s t ==> wseg c k' n' s' t' := by
  subst hk hn hs ht
  exact HProp.himpl_refl _

theorem wseg_cell {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (w : Int) :
    c s t w ==> wseg c 1 w s t := by
  show c s t w ==> ∃✶ s', ∃✶ w', c s s' w' ✶ ⌈s' = t ∧ w - w' = 0⌉
  refine HProp.himpl_hexists_r t (HProp.himpl_hexists_r w ?_)
  rw [HProp.hstar_comm]
  exact HProp.himpl_hstar_hpure_r ⟨rfl, by omega⟩ (HProp.himpl_refl _)

theorem wseg_uncell {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (n : Int) :
    wseg c 1 n s t ==> c s t n := by
  show (∃✶ s', ∃✶ w', c s s' w' ✶ ⌈s' = t ∧ n - w' = 0⌉) ==> c s t n
  refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w' => ?_))
  rw [HProp.hstar_comm]
  refine HProp.himpl_hstar_hpure_l (fun ⟨h1, h2⟩ => ?_)
  subst h1
  rw [show n = w' by omega]
  exact HProp.himpl_refl _

theorem wseg_join {σ : Type} (c : σ → σ → Int → HProp) (k₁ k₂ : Nat) (n₁ n₂ : Int) (s t u : σ) :
    wseg c k₁ n₁ s t ✶ wseg c k₂ n₂ t u ==> wseg c (k₁ + k₂) (n₁ + n₂) s u := by
  induction k₁ generalizing s n₁ with
  | zero =>
    rw [Nat.zero_add]
    show ⌈s = t ∧ n₁ = 0⌉ ✶ wseg c k₂ n₂ t u ==> wseg c k₂ (n₁ + n₂) s u
    refine HProp.himpl_hstar_hpure_l (fun ⟨h1, h2⟩ => ?_)
    subst h1 h2
    rw [Int.zero_add]
    exact HProp.himpl_refl _
  | succ k ih =>
    rw [show k + 1 + k₂ = (k + k₂) + 1 by omega]
    show (∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n₁ - w) s' t) ✶ wseg c k₂ n₂ t u ==>
      ∃✶ s', ∃✶ w, c s s' w ✶ wseg c (k + k₂) (n₁ + n₂ - w) s' u
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun s' => ?_)
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun w => ?_)
    refine HProp.himpl_hexists_r s' (HProp.himpl_hexists_r w ?_)
    rw [HProp.hstar_assoc, show n₁ + n₂ - w = (n₁ - w) + n₂ by omega]
    exact HProp.himpl_frame_r (ih (n₁ - w) s')

theorem wseg_split {σ : Type} (c : σ → σ → Int → HProp) (k₁ k₂ : Nat) (n : Int) (s u : σ) :
    wseg c (k₁ + k₂) n s u ==> ∃✶ t, ∃✶ m, wseg c k₁ m s t ✶ wseg c k₂ (n - m) t u := by
  induction k₁ generalizing s n with
  | zero =>
    rw [Nat.zero_add]
    refine HProp.himpl_hexists_r s (HProp.himpl_hexists_r 0 ?_)
    show wseg c k₂ n s u ==> ⌈s = s ∧ (0 : Int) = 0⌉ ✶ wseg c k₂ (n - 0) s u
    rw [Int.sub_zero]
    exact HProp.himpl_hstar_hpure_r ⟨rfl, rfl⟩ (HProp.himpl_refl _)
  | succ k ih =>
    rw [show k + 1 + k₂ = (k + k₂) + 1 by omega]
    show (∃✶ s', ∃✶ w, c s s' w ✶ wseg c (k + k₂) (n - w) s' u) ==>
      ∃✶ t, ∃✶ m, (∃✶ s', ∃✶ w', c s s' w' ✶ wseg c k (m - w') s' t) ✶ wseg c k₂ (n - m) t u
    refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
    refine HProp.himpl_trans (HProp.himpl_frame_r (ih (n - w) s')) ?_
    rw [HProp.hstar_comm, HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun t => ?_)
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun m => ?_)
    refine HProp.himpl_hexists_r t (HProp.himpl_hexists_r (m + w) ?_)
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_r s' ?_
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_r w ?_
    rw [show m + w - w = m by omega, show n - (m + w) = n - w - m by omega]
    rw [HProp.hstar_comm, HProp.hstar_assoc]
    exact HProp.himpl_refl _

theorem wseg_map {σ τ : Type} (c : σ → σ → Int → HProp) (c' : τ → τ → Int → HProp) (f : σ → τ)
    (h : ∀ s s' w, c s s' w ==> c' (f s) (f s') w) (k : Nat) (n : Int) (s t : σ) :
    wseg c k n s t ==> wseg c' k n (f s) (f t) := by
  induction k generalizing s n with
  | zero =>
    show ⌈s = t ∧ n = 0⌉ ==> ⌈f s = f t ∧ n = 0⌉
    intro _ hp
    obtain ⟨⟨h1, h2⟩, he⟩ := HProp.hpure_elim_hempty hp
    exact HProp.hpure_intro_hempty he ⟨congrArg f h1, h2⟩
  | succ k ih =>
    show (∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n - w) s' t) ==>
      ∃✶ s', ∃✶ w, c' (f s) s' w ✶ wseg c' k (n - w) s' (f t)
    refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
    refine HProp.himpl_hexists_r (f s') (HProp.himpl_hexists_r w ?_)
    exact HProp.himpl_frame_lr (h s s' w) (ih (n - w) s')

theorem wseg_map_fr {σ τ : Type} (c : σ → σ → Int → HProp) (c' : τ → τ → Int → HProp) (f : σ → τ)
    (F : HProp) (h : ∀ s s' w, c s s' w ✶ F ==> c' (f s) (f s') w ✶ F) (k : Nat) (n : Int) (s t : σ) :
    wseg c k n s t ✶ F ==> wseg c' k n (f s) (f t) ✶ F := by
  induction k generalizing s n with
  | zero =>
    show ⌈s = t ∧ n = 0⌉ ✶ F ==> ⌈f s = f t ∧ n = 0⌉ ✶ F
    refine HProp.himpl_hstar_hpure_l (fun ⟨h1, h2⟩ => ?_)
    exact HProp.himpl_hstar_hpure_r ⟨congrArg f h1, h2⟩ (HProp.himpl_refl _)
  | succ k ih =>
    show (∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n - w) s' t) ✶ F ==>
      (∃✶ s', ∃✶ w, c' (f s) s' w ✶ wseg c' k (n - w) s' (f t)) ✶ F
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun s' => ?_)
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun w => ?_)
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_r (f s') ?_
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_r w ?_
    rw [HProp.hstar_assoc, HProp.hstar_comm (wseg c k (n - w) s' t) F, ← HProp.hstar_assoc]
    refine HProp.himpl_trans (HProp.himpl_frame_l (h s s' w)) ?_
    rw [HProp.hstar_assoc, HProp.hstar_assoc]
    refine HProp.himpl_frame_r ?_
    rw [HProp.hstar_comm]
    exact ih (n - w) s'

theorem wseg_rev {σ τ : Type} (c : σ → σ → Int → HProp) (c' : τ → τ → Int → HProp) (f : σ → τ)
    (h : ∀ s s' w, c s s' w ==> c' (f s') (f s) w) (k : Nat) (n : Int) (s t : σ) :
    wseg c k n s t ==> wseg c' k n (f t) (f s) := by
  induction k generalizing s n with
  | zero =>
    show ⌈s = t ∧ n = 0⌉ ==> ⌈f t = f s ∧ n = 0⌉
    intro _ hp
    obtain ⟨⟨h1, h2⟩, he⟩ := HProp.hpure_elim_hempty hp
    exact HProp.hpure_intro_hempty he ⟨congrArg f h1.symm, h2⟩
  | succ k ih =>
    show (∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n - w) s' t) ==> wseg c' (k + 1) n (f t) (f s)
    refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
    refine HProp.himpl_trans (HProp.himpl_frame_lr (wseg_cell c' (f s') (f s) w |> HProp.himpl_trans (h s s' w)) (ih (n - w) s')) ?_
    rw [HProp.hstar_comm]
    refine HProp.himpl_trans (wseg_join c' k 1 (n - w) w (f t) (f s') (f s)) ?_
    rw [show n - w + w = n by omega]
    exact HProp.himpl_refl _

theorem wseg_inv {σ : Type} (c : σ → σ → Int → HProp) (r : σ → σ → Int → Prop)
    (I : Nat → σ → σ → Int → Prop)
    (hc : ∀ s s' w h, c s s' w h → r s s' w) (h0 : ∀ s, I 0 s s 0)
    (hs : ∀ k s s' t w m, r s s' w → I k s' t m → I (k + 1) s t (m + w))
    (k : Nat) (n : Int) (s t : σ) : ∀ h, wseg c k n s t h → I k s t n := by
  induction k generalizing s n with
  | zero =>
    intro h hh
    obtain ⟨⟨h1, h2⟩, _⟩ := HProp.hpure_elim hh
    subst h1 h2
    exact h0 s
  | succ k ih =>
    intro h hh
    obtain ⟨s', hh⟩ := HProp.hexists_elim hh
    obtain ⟨w, hh⟩ := HProp.hexists_elim hh
    obtain ⟨h1, h2, hc1, hw, _, _⟩ := HProp.hstar_elim hh
    have := hs k s s' t w (n - w) (hc s s' w h1 hc1) (ih (n - w) s' h2 hw)
    rwa [show n - w + w = n by omega] at this

def wor (H1 H2 : HProp) : HProp := fun h => H1 h ∨ H2 h

theorem wor_l {H B S : HProp} (h : H ==> B) : H ==> wor B S := fun k hk => Or.inl (h k hk)

theorem wor_r {H B S : HProp} (h : H ==> S) : H ==> wor B S := fun k hk => Or.inr (h k hk)

theorem wor_elim {B S H : HProp} (h1 : B ==> H) (h2 : S ==> H) : wor B S ==> H := by
  intro k hk
  rcases hk with hk | hk
  · exact h1 k hk
  · exact h2 k hk

theorem pure_r_intro {P : Prop} {H1 H2 : HProp} (hp : P) (h : H1 ==> H2) : H1 ==> H2 ✶ ⌈P⌉ := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_hstar_hpure_r hp h

theorem pure_l_intro {P : Prop} {H1 H2 : HProp} (hp : P) (h : H1 ==> H2) : H1 ==> ⌈P⌉ ✶ H2 :=
  HProp.himpl_hstar_hpure_r hp h

theorem pure_r_elim {P : Prop} {H1 H2 : HProp} (h : P → H1 ==> H2) : H1 ✶ ⌈P⌉ ==> H2 := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_hstar_hpure_l h

theorem wseg_two_elim {σ : Type} (c : σ → σ → Int → HProp) (n : Int) (s t : σ) :
    wseg c 2 n s t ==> ∃✶ u, ∃✶ w, c s u w ✶ c u t (n - w) := by
  show (∃✶ u, ∃✶ w, c s u w ✶ wseg c 1 (n - w) u t) ==> _
  refine HProp.himpl_hexists_l (fun u => HProp.himpl_hexists_l (fun w => ?_))
  refine HProp.himpl_hexists_r u (HProp.himpl_hexists_r w ?_)
  exact HProp.himpl_frame_r (wseg_uncell c u t (n - w))

noncomputable def pNthK {α : Type} (l : List α) (n : Nat) (d : α) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih n => Nat.rec (motive := fun _ => α) a (fun k _ => ih k) n) l n

noncomputable def pLenK {α : Type} (l : List α) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => ih + 1) l

omit [Params] in
theorem pLenK_eq {α : Type} (l : List α) : pLenK l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show pLenK l + 1 = _
    rw [ih, List.length_cons]

omit [Params] in
theorem pNthK_getD {α : Type} (l : List α) (n : Nat) (d : α) : pNthK l n d = l.getD n d := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

omit [Params] in
theorem pAll_nil {α : Type} {P : α → Prop} : ∀ b ∈ ([] : List α), P b := by
  intro b hb
  cases hb

omit [Params] in
theorem pAll_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ b ∈ l, P b) :
    ∀ b ∈ a :: l, P b := by
  intro b hb
  cases hb with
  | head => exact ha
  | tail _ h => exact hl b h

def pCell (C : Nat → Nat → HProp) (s s' : Nat) (w : Int) : HProp :=
  ∃✶ u, C s u ✶ ⌈s' = u ∧ w = 1⌉

def pLenC (S : Nat → Nat → Prop) : List (Option Nat) → Nat → Prop
  | [], k => k = 0
  | none :: r, k => ∃ k', k = k' + 1 ∧ pLenC S r k'
  | some j :: r, k => ∃ k1 k2, k = k1 + k2 ∧ S j k1 ∧ pLenC S r k2

def pLen (B : List (List (List (Option Nat)))) (i k : Nat) : Prop :=
  ∀ S : Nat → Nat → Prop, (∀ i k, (∃ b ∈ pNthK B i [], pLenC S b k) → S i k) → S i k

omit [Params] in
theorem pLenC_mono {S T : Nat → Nat → Prop} (hST : ∀ i k, S i k → T i k) :
    ∀ (b : List (Option Nat)) (k : Nat), pLenC S b k → pLenC T b k
  | [], _, h => h
  | none :: r, _, ⟨k', hk, h⟩ => ⟨k', hk, pLenC_mono hST r k' h⟩
  | some j :: r, _, ⟨k1, k2, hk, h1, h2⟩ => ⟨k1, k2, hk, hST j k1 h1, pLenC_mono hST r k2 h2⟩

omit [Params] in
theorem pLen_intro (B : List (List (List (Option Nat)))) (i k : Nat)
    (h : ∃ b ∈ pNthK B i [], pLenC (pLen B) b k) : pLen B i k := by
  intro S hS
  obtain ⟨b, hb, hl⟩ := h
  exact hS i k ⟨b, hb, pLenC_mono (fun j k' hj => hj S hS) b k hl⟩

theorem wseg_inv1 {σ : Type} (c : σ → σ → Int → HProp) (hc : ∀ s s' w h, c s s' w h → w = 1)
    (k : Nat) (n : Int) (s t : σ) : ∀ h, wseg c k n s t h → n = (k : Int) ∧ (k = 0 → s = t) :=
  wseg_inv c (fun _ _ w => w = 1) (fun k s t n => n = (k : Int) ∧ (k = 0 → s = t)) hc
    (fun _ => ⟨rfl, fun _ => rfl⟩)
    (fun k _ _ _ w m hw hi => ⟨by rw [hi.1, hw]; push_cast; rfl, fun h => absurd h (Nat.succ_ne_zero k)⟩) k n s t

theorem pCell_w (C : Nat → Nat → HProp) : ∀ (s s' : Nat) (w : Int) h, pCell C s s' w h → w = 1 := by
  intro s s' w h hc
  obtain ⟨u, hc⟩ := HProp.hexists_elim hc
  obtain ⟨_, _, _, m2, _, _⟩ := HProp.hstar_elim hc
  exact (HProp.hpure_elim m2).1.2

def pNth {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: l, n + 1, d => pNth l n d

def pMemB (x : Nat) : List Nat → Bool
  | [] => false
  | r :: rs => Nat.beq x r || pMemB x rs

omit [Params] in
theorem pNth_eq {α : Type} : ∀ (l : List α) (n : Nat) (d : α), pNth l n d = l.getD n d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, n + 1, d => pNth_eq l n d

omit [Params] in
theorem pble (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.ble_eq, decide_eq_true_eq])

omit [Params] in
theorem pblt (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_eq])

omit [Params] in
theorem pbeq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, beq_iff_eq])

omit [Params] in
theorem pMemB_eq (x : Nat) : ∀ l : List Nat, pMemB x l = l.contains x
  | [] => rfl
  | r :: rs => by
    show (Nat.beq x r || pMemB x rs) = (r :: rs).contains x
    rw [pMemB_eq x rs, List.contains_cons, pbeq]

def inS (m p : Nat) (rs : List Nat) (n : Nat) : Bool := Nat.ble m n && pMemB ((n - m) % p) rs

def slinR (d : Int) : List Nat → Prop
  | [] => False
  | [r] => d = (r : Int)
  | r :: r2 :: rs => d = (r : Int) ∨ slinR d (r2 :: rs)

def phiI (m p : Nat) (rs : List Nat) (n : Int) : Prop :=
  match p with
  | 1 => (m : Int) ≤ n
  | _ => (m : Int) ≤ n ∧ slinR ((n - (m : Int)) % (p : Int)) rs

omit [Params] in
theorem slinR_iff (d : Int) : ∀ rs : List Nat, slinR d rs ↔ ∃ r ∈ rs, d = (r : Int)
  | [] => by simp [slinR]
  | [r] => by simp [slinR]
  | r :: r2 :: rs => by
    show (d = (r : Int) ∨ slinR d (r2 :: rs)) ↔ _
    rw [slinR_iff d (r2 :: rs)]
    simp

omit [Params] in
theorem sub_mod_cast (k m p : Nat) (h : m ≤ k) : ((k : Int) - (m : Int)) % (p : Int) = (((k - m) % p : Nat) : Int) := by
  rw [Int.natCast_emod, Int.ofNat_sub h]

omit [Params] in
theorem phiI_of_inS {m p : Nat} {rs : List Nat} {k : Nat} (h : inS m p rs k = true) : phiI m p rs (k : Int) := by
  simp only [inS, pMemB_eq, pble, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨hmk, hr⟩ := h
  have hle : (m : Int) ≤ (k : Int) := Int.ofNat_le.mpr hmk
  match p, hr with
  | 0, hr =>
    refine ⟨hle, ?_⟩
    rw [sub_mod_cast k m 0 hmk, slinR_iff]
    exact ⟨_, hr, rfl⟩
  | 1, _ => exact hle
  | p + 2, hr =>
    refine ⟨hle, ?_⟩
    rw [sub_mod_cast k m (p + 2) hmk, slinR_iff]
    exact ⟨_, hr, rfl⟩

omit [Params] in
theorem inS_of_phiI {m p : Nat} {rs : List Nat} {k : Nat} (h1 : p = 1 → 0 ∈ rs) (h : phiI m p rs (k : Int)) :
    inS m p rs k = true := by
  simp only [inS, pMemB_eq, pble, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
  match p, h with
  | 0, ⟨hle, hs⟩ =>
    have hmk : m ≤ k := Int.ofNat_le.mp hle
    rw [sub_mod_cast k m 0 hmk, slinR_iff] at hs
    obtain ⟨r, hr, he⟩ := hs
    exact ⟨hmk, (Int.ofNat_inj.mp he) ▸ hr⟩
  | 1, hle =>
    have hmk : m ≤ k := Int.ofNat_le.mp hle
    exact ⟨hmk, by rw [Nat.mod_one]; exact h1 rfl⟩
  | p + 2, ⟨hle, hs⟩ =>
    have hmk : m ≤ k := Int.ofNat_le.mp hle
    rw [sub_mod_cast k m (p + 2) hmk, slinR_iff] at hs
    obtain ⟨r, hr, he⟩ := hs
    exact ⟨hmk, (Int.ofNat_inj.mp he) ▸ hr⟩

def pDflt : Nat × Nat × List Nat := (0, 1, [])

def pSet (prof : List (Nat × Nat × List Nat)) (q n : Nat) : Prop :=
  inS (prof.getD q pDflt).1 (prof.getD q pDflt).2.1 (prof.getD q pDflt).2.2 n = true

def pStepA (prof : List (Nat × Nat × List Nat)) (pj : Nat) : Option Nat → List Nat × Nat → List Nat × Nat
  | none, st => (st.1.map (fun a => (a + 1) % pj), st.2 + 1)
  | some q, st =>
    (st.1.flatMap (fun a => (pNth prof q pDflt).2.2.flatMap (fun r => (List.range pj).map
      (fun t => (a + (pNth prof q pDflt).1 + r + (pNth prof q pDflt).2.1 * t) % pj))),
     st.2 + (pNth prof q pDflt).1)

def pRunA (prof : List (Nat × Nat × List Nat)) (pj : Nat) :
    List (Option Nat) → List Nat × Nat → List Nat × Nat
  | [], st => st
  | it :: r, st => pRunA prof pj r (pStepA prof pj it st)

def pBrA (prof : List (Nat × Nat × List Nat)) (m p : Nat) (rs : List Nat) (b : List (Option Nat)) : Bool :=
  Nat.ble m (pRunA prof p b ([0], 0)).2 &&
    ((Nat.beq p 1 && pMemB 0 rs) || (pRunA prof p b ([0], 0)).1.all (fun a => pMemB ((a + p - m % p) % p) rs))

def pChkA (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) : Bool :=
  (List.range B.length).all (fun j =>
    Nat.blt (0) ((pNth prof j pDflt).2.1) &&
      (pNth B j []).all (pBrA prof (pNth prof j pDflt).1 (pNth prof j pDflt).2.1 (pNth prof j pDflt).2.2))

omit [Params] in
theorem mod_succ_eq (s p : Nat) : (s + 1) % p = (s % p + 1) % p := by
  rw [Nat.add_mod s 1, Nat.add_mod (s % p) 1, Nat.mod_mod]

omit [Params] in
theorem mod_step_eq (s k mq pq pj : Nat) (hk : mq ≤ k) :
    (s + k) % pj = (s % pj + mq + (k - mq) % pq + pq * ((k - mq) / pq % pj)) % pj := by
  have h1 := Nat.mod_add_div s pj
  have h2 := Nat.mod_add_div (k - mq) pq
  have h3 : pq * ((k - mq) / pq) = pq * ((k - mq) / pq % pj) + pj * (pq * ((k - mq) / pq / pj)) := by
    conv => lhs; rw [← Nat.mod_add_div ((k - mq) / pq) pj]
    rw [Nat.mul_add, Nat.mul_left_comm]
  have e : s + k = (s % pj + mq + (k - mq) % pq + pq * ((k - mq) / pq % pj)) +
      pj * (s / pj + pq * ((k - mq) / pq / pj)) := by
    rw [Nat.mul_add]
    omega
  rw [e, Nat.add_mul_mod_self_left]

omit [Params] in
theorem sub_mod_eq (k m p : Nat) (hp : 0 < p) (h : m ≤ k) : (k - m) % p = (k % p + p - m % p) % p := by
  have ha := Nat.mod_lt (k - m) hp
  have hb := Nat.mod_lt m hp
  have hk : k % p = ((k - m) % p + m % p) % p := by
    rw [← Nat.add_mod, Nat.sub_add_cancel h]
  rw [hk]
  generalize (k - m) % p = a at *
  generalize m % p = b at *
  by_cases hc : a + b < p
  · rw [Nat.mod_eq_of_lt hc, show a + b + p - b = a + p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hc), Nat.mod_eq_of_lt (show a + b - p < p by omega),
      show a + b - p + p - b = a by omega, Nat.mod_eq_of_lt ha]

omit [Params] in
theorem pRunA_sound (prof : List (Nat × Nat × List Nat)) (pj : Nat) (hp : 0 < pj) :
    ∀ (b : List (Option Nat)) (st : List Nat × Nat) (s k : Nat), s % pj ∈ st.1 → st.2 ≤ s →
      pLenC (pSet prof) b k →
      (s + k) % pj ∈ (pRunA prof pj b st).1 ∧ (pRunA prof pj b st).2 ≤ s + k
  | [], st, s, k, h1, h2, hk => by
    have hk' : k = 0 := hk
    subst hk'
    exact ⟨h1, h2⟩
  | none :: r, st, s, k, h1, h2, ⟨k', hk, hr⟩ => by
    have := pRunA_sound prof pj hp r (pStepA prof pj none st) (s + 1) k'
      (by
        show (s + 1) % pj ∈ st.1.map (fun a => (a + 1) % pj)
        rw [mod_succ_eq]
        exact List.mem_map_of_mem h1)
      (by show st.2 + 1 ≤ s + 1; omega) hr
    rw [show s + k = s + 1 + k' by omega]
    exact this
  | some q :: r, st, s, k, h1, h2, ⟨k1, k2, hk, hq, hr⟩ => by
    have hq' := hq
    simp only [pSet, inS, pMemB_eq, pble, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hq'
    obtain ⟨hmq, hrq⟩ := hq'
    have := pRunA_sound prof pj hp r (pStepA prof pj (some q) st) (s + k1) k2
      (by
        show (s + k1) % pj ∈ st.1.flatMap _
        simp only [pNth_eq]
        rw [List.mem_flatMap]
        refine ⟨s % pj, h1, ?_⟩
        rw [List.mem_flatMap]
        refine ⟨_, hrq, ?_⟩
        rw [List.mem_map]
        exact ⟨_, List.mem_range.mpr (Nat.mod_lt _ hp), (mod_step_eq s k1 _ _ pj hmq).symm⟩)
      (by show st.2 + (pNth prof q pDflt).1 ≤ s + k1; rw [pNth_eq]; omega) hr
    rw [show s + k = s + k1 + k2 by omega]
    exact this

omit [Params] in
theorem pBrA_sound (prof : List (Nat × Nat × List Nat)) (m p : Nat) (rs : List Nat) (hp : 0 < p)
    (b : List (Option Nat)) (hb : pBrA prof m p rs b = true) (k : Nat) (hk : pLenC (pSet prof) b k) :
    inS m p rs k = true := by
  simp only [pBrA, pMemB_eq, pble, pbeq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true] at hb
  obtain ⟨hm, hall⟩ := hb
  have := pRunA_sound prof p hp b ([0], 0) 0 k (by simp) (Nat.le_refl 0) hk
  rw [Nat.zero_add] at this
  have hmk : m ≤ k := Nat.le_trans hm this.2
  simp only [inS, pMemB_eq, pble, Bool.and_eq_true, decide_eq_true_eq]
  rcases hall with ⟨hp1, h0⟩ | hall
  · subst hp1
    exact ⟨hmk, by rw [Nat.mod_one]; exact h0⟩
  · have hc := hall _ this.1
    exact ⟨hmk, by rw [sub_mod_eq k m p hp hmk]; exact hc⟩

omit [Params] in
theorem pChkA_sound (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (h : pChkA B prof = true) (j k : Nat) (hk : pLen B j k) : pSet prof j k := by
  refine hk (pSet prof) ?_
  intro i n ⟨b, hb, hl⟩
  rw [pNthK_getD] at hb
  have hi : i < B.length := by
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hb
    cases hb
  simp only [pChkA, pNth_eq, pblt, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hp, hall⟩ := h i (List.mem_range.mpr hi)
  exact pBrA_sound prof _ _ _ hp b (hall b hb) n hl

def inSp (prof : List (Nat × Nat × List Nat)) (q n : Nat) : Bool :=
  inS (pNth prof q pDflt).1 (pNth prof q pDflt).2.1 (pNth prof q pDflt).2.2 n

def pWalk (ok : Nat → Nat → Bool) : List (Option Nat) → List (Option Nat) → Option (Nat × Option Nat)
  | [], [] => some (0, none)
  | none :: r, ls => (pWalk ok r ls).map (fun dh => (dh.1 + 1, dh.2))
  | some q :: r, some c :: ls => if ok q c then (pWalk ok r ls).map (fun dh => (dh.1 + c, dh.2)) else none
  | some q :: r, none :: ls => match pWalk ok r ls with
    | some (d, none) => some (d, some q)
    | _ => none
  | _, _ => none

omit [Params] in
theorem pWalk_sound (ok : Nat → Nat → Bool) (S : Nat → Nat → Prop) (hok : ∀ q c, ok q c = true → S q c) :
    ∀ (b ls : List (Option Nat)) (d : Nat) (h : Option Nat), pWalk ok b ls = some (d, h) →
      (h = none → pLenC S b d) ∧ (∀ q0 v, h = some q0 → S q0 v → pLenC S b (d + v))
  | [], [], d, h, e => by
    simp only [pWalk, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨fun _ => rfl, fun _ _ hc => by cases hc⟩
  | [], _ :: _, _, _, e => by simp [pWalk] at e
  | none :: r, ls, d, h, e => by
    simp only [pWalk, Option.map_eq_some_iff] at e
    obtain ⟨⟨d', h'⟩, e1, e2⟩ := e
    simp only [Prod.mk.injEq] at e2
    obtain ⟨rfl, rfl⟩ := e2
    have ih := pWalk_sound ok S hok r ls d' h' e1
    exact ⟨fun hn => ⟨d', rfl, ih.1 hn⟩,
      fun q0 v hq hs => ⟨d' + v, by omega, ih.2 q0 v hq hs⟩⟩
  | some q :: r, some c :: ls, d, h, e => by
    simp only [pWalk] at e
    split at e
    · rename_i hc
      simp only [Option.map_eq_some_iff] at e
      obtain ⟨⟨d', h'⟩, e1, e2⟩ := e
      simp only [Prod.mk.injEq] at e2
      obtain ⟨rfl, rfl⟩ := e2
      have ih := pWalk_sound ok S hok r ls d' h' e1
      exact ⟨fun hn => ⟨c, d', by omega, hok q c hc, ih.1 hn⟩,
        fun q0 v hq hs => ⟨c, d' + v, by omega, hok q c hc, ih.2 q0 v hq hs⟩⟩
    · cases e
  | some q :: r, none :: ls, d, h, e => by
    simp only [pWalk] at e
    split at e
    · rename_i d' e1
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨hd, hh⟩ := e
      subst hd hh
      have ih := pWalk_sound ok S hok r ls d' none e1
      refine ⟨fun hc => (by cases hc), fun q0 v hq hs => ?_⟩
      cases hq
      exact ⟨v, d', by omega, hs, ih.1 rfl⟩
    · cases e
  | some _ :: _, [], _, _, e => by simp [pWalk] at e

def pSmallOk (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (R j n : Nat) (e : Nat × Nat × List (Option Nat)) : Bool :=
  Nat.beq e.1 n && Nat.blt (e.2.1) ((pNth B j []).length) &&
    match pWalk (fun q c => Nat.blt (q) (R) && inSp prof q c && Nat.blt (c * R + pNth rk q 0) (n * R + pNth rk j 0))
      (pNth (pNth B j []) e.2.1 []) e.2.2 with
    | some (d, none) => Nat.beq d n
    | _ => false

def pBigOk (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (R N j sp : Nat) (e : Nat × Nat × Nat × List (Option Nat)) : Bool :=
  Nat.blt (e.2.1) ((pNth B j []).length) &&
    match pWalk (fun q c => Nat.blt (q) (R) && inSp prof q c && Nat.blt (c) (N))
      (pNth (pNth B j []) e.2.1 []) e.2.2.2 with
    | some (d, some q0) =>
      Nat.blt (q0) (R) && Nat.blt (0) ((pNth prof q0 pDflt).2.1) && Nat.ble (N) (e.2.2.1) &&
      Nat.blt (e.2.2.1) (N + sp) && Nat.ble ((pNth prof j pDflt).1) (e.2.2.1) &&
      Nat.beq ((e.2.2.1 - (pNth prof j pDflt).1) % sp) e.1 &&
      Nat.ble (d + (pNth prof q0 pDflt).1) (N) &&
      (Nat.blt (0) (d) || Nat.blt (pNth rk q0 0) (pNth rk j 0)) &&
      (List.range (pNth prof q0 pDflt).2.1).all (fun t => pMemB
        ((e.2.2.1 + sp * t - d - (pNth prof q0 pDflt).1) % (pNth prof q0 pDflt).2.1) (pNth prof q0 pDflt).2.2)
    | _ => false

def pChkC (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat) (N : Nat)
    (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat)))) : Bool :=
  (List.range B.length).all (fun j =>
    Nat.blt (pNth rk j 0) (B.length) && Nat.blt (0) ((pNth prof j pDflt).2.1) &&
    (!Nat.beq (pNth prof j pDflt).2.1 1 || pMemB 0 (pNth prof j pDflt).2.2) &&
    (List.range N).all (fun n => !inSp prof j n || (pNth cert j ([], [])).1.any (pSmallOk B prof rk B.length j n)) &&
    Nat.blt (0) (pNth sps j 1) && Nat.beq (pNth sps j 1 % (pNth prof j pDflt).2.1) 0 &&
    (List.range (pNth sps j 1)).all (fun r => !pMemB (r % (pNth prof j pDflt).2.1) (pNth prof j pDflt).2.2 ||
      (pNth cert j ([], [])).2.any (fun e => Nat.beq e.1 r && pBigOk B prof rk B.length N j (pNth sps j 1) e)))

omit [Params] in
theorem cls_ge (n n0 m p : Nat) (hm : m ≤ n0) (hmn : m ≤ n)
    (hr : (n - m) % p = (n0 - m) % p) (hlt : n0 < n + p) : n0 ≤ n ∧ (n - n0) % p = 0 := by
  have h1 := Nat.mod_add_div (n - m) p
  have h2 := Nat.mod_add_div (n0 - m) p
  have hq : (n0 - m) / p ≤ (n - m) / p := by
    by_contra hc
    have hc' : (n - m) / p + 1 ≤ (n0 - m) / p := by omega
    have := Nat.mul_le_mul_left p hc'
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  have hle : n0 ≤ n := by
    have := Nat.mul_le_mul_left p hq
    omega
  refine ⟨hle, ?_⟩
  have e : n - n0 = p * ((n - m) / p - (n0 - m) / p) := by
    rw [Nat.mul_sub]
    omega
  rw [e, Nat.mul_mod_right]

omit [Params] in
theorem mod_shift (X p t pq : Nat) : (X + p * t) % pq = (X + p * (t % pq)) % pq := by
  have h : p * t = p * (t % pq) + pq * (p * (t / pq)) := by
    conv => lhs; rw [← Nat.mod_add_div t pq]
    rw [Nat.mul_add, Nat.mul_left_comm]
  rw [h, ← Nat.add_assoc, Nat.add_mul_mod_self_left]

omit [Params] in
theorem mul_lt_of_lt (a b R r : Nat) (hab : a < b) (hr : r < R) (s : Nat) : a * R + r < b * R + s := by
  have : (a + 1) * R ≤ b * R := Nat.mul_le_mul_right R hab
  rw [Nat.succ_mul] at this
  omega

omit [Params] in
theorem pChkC_sound (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat))))
    (hc : pChkC B prof rk N sps cert = true) :
    ∀ μ j n, n * B.length + rk.getD j 0 = μ → j < B.length → inSp prof j n = true → pLen B j n := by
  intro μ
  induction μ using Nat.strongRecOn with
  | _ μ ih =>
  intro j n hμ hj hin
  have hc' := hc
  simp only [pChkC, pNth_eq, pMemB_eq, pblt, pbeq, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨hrk, hp⟩, _⟩, hsm⟩, hsp⟩, hdvd⟩, hbg⟩ := hc' j (List.mem_range.mpr hj)
  have hrkq : ∀ q, q < B.length → rk.getD q 0 < B.length := fun q hq =>
    (((((((hc' q (List.mem_range.mpr hq)).1).1).1).1).1).1)
  have hmem : ∀ bi, bi < (B.getD j []).length → (B.getD j []).getD bi [] ∈ pNthK B j [] := by
    intro bi hbi
    rw [pNthK_getD]
    generalize B.getD j [] = L at hbi ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbi, Option.getD_some]
    exact List.getElem_mem hbi
  by_cases hn : n < N
  · have h0 := hsm n (List.mem_range.mpr hn)
    rw [hin, Bool.not_true, Bool.false_or] at h0
    obtain ⟨e, _, he⟩ := List.any_eq_true.mp h0
    simp only [pSmallOk, pNth_eq, pblt, pbeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he
    obtain ⟨⟨he1, hbi⟩, hw⟩ := he
    split at hw
    · rename_i d hwe
      simp only [beq_iff_eq] at hw
      subst hw
      have := (pWalk_sound _ (pLen B) (fun q c hq => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
        obtain ⟨⟨hqR, hqin⟩, hlt⟩ := hq
        exact ih _ (by omega) q c rfl hqR hqin) _ _ _ _ hwe).1 rfl
      exact pLen_intro B j d ⟨_, hmem _ hbi, this⟩
    · cases hw
  · have hNn : N ≤ n := Nat.le_of_not_lt hn
    have hin' := hin
    simp only [inSp, inS, pNth_eq, pMemB_eq, pble, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hin'
    obtain ⟨hmn, hrs⟩ := hin'
    have hdvd' : (prof.getD j pDflt).2.1 ∣ sps.getD j 1 := Nat.dvd_of_mod_eq_zero (by simpa using hdvd)
    have hmm : (n - (prof.getD j pDflt).1) % sps.getD j 1 % (prof.getD j pDflt).2.1 =
        (n - (prof.getD j pDflt).1) % (prof.getD j pDflt).2.1 := Nat.mod_mod_of_dvd _ hdvd'
    have := hbg ((n - (prof.getD j pDflt).1) % sps.getD j 1) (List.mem_range.mpr (Nat.mod_lt _ hsp))
    rw [hmm, List.contains_iff_mem.mpr hrs, Bool.not_true, Bool.false_or] at this
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨e, _, he1, he⟩ := this
    simp only [pBigOk, pNth_eq, pMemB_eq, pble, pblt, pbeq, Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨hbi, hw⟩ := he
    split at hw
    · rename_i d q0 hwe
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
        List.contains_iff_mem] at hw
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hq0, hpq⟩, hN0⟩, hn0⟩, hm0⟩, hr0⟩, hdN⟩, hmeas⟩, hall⟩ := hw
      obtain ⟨hle0, hdiv⟩ := cls_ge n e.2.2.1 _ (sps.getD j 1) hm0 hmn (by rw [hr0, he1]) (by omega)
      have hv : inSp prof q0 (n - d) = true := by
        simp only [inSp, inS, pNth_eq, pMemB_eq, pble, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
        refine ⟨by omega, ?_⟩
        have hn' : n = e.2.2.1 + (sps.getD j 1) * ((n - e.2.2.1) / (sps.getD j 1)) := by
          have := Nat.mod_add_div (n - e.2.2.1) (sps.getD j 1)
          omega
        have key := hall _ (List.mem_range.mpr (Nat.mod_lt ((n - e.2.2.1) / (sps.getD j 1)) hpq))
        have h1 : n - d - (prof.getD q0 pDflt).1 = (e.2.2.1 - d - (prof.getD q0 pDflt).1) +
            (sps.getD j 1) * ((n - e.2.2.1) / (sps.getD j 1)) := by omega
        have h2 : e.2.2.1 + (sps.getD j 1) * ((n - e.2.2.1) / (sps.getD j 1) %
            (prof.getD q0 pDflt).2.1) - d - (prof.getD q0 pDflt).1 = (e.2.2.1 - d - (prof.getD q0 pDflt).1) +
            (sps.getD j 1) * ((n - e.2.2.1) / (sps.getD j 1) % (prof.getD q0 pDflt).2.1) := by
          omega
        rw [h1, mod_shift, ← h2]
        exact key
      have hIH := ih ((n - d) * B.length + rk.getD q0 0) (by
        rw [← hμ]
        by_cases hd : 0 < d
        · have hdn : d ≤ n := by omega
          exact mul_lt_of_lt _ _ _ _ (by omega) (hrkq q0 hq0) _
        · have hr : rk.getD q0 0 < rk.getD j 0 := by
            rcases hmeas with h | h
            · exact absurd h hd
            · exact h
          have : n - d = n := by omega
          rw [this]
          omega) q0 (n - d) rfl hq0 hv
      have := (pWalk_sound _ (pLen B) (fun q c hq => by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
        obtain ⟨⟨hqR, hqin⟩, hlt⟩ := hq
        exact ih _ (by rw [← hμ]; exact mul_lt_of_lt _ _ _ _ (by omega) (hrkq q hqR) _) q c rfl hqR hqin)
        _ _ _ _ hwe).2 q0 (n - d) rfl hIH
      rw [show d + (n - d) = n by omega] at this
      exact pLen_intro B j n ⟨_, hmem _ hbi, this⟩
    · cases hw

noncomputable def pAppK {α : Type} (l1 l2 : List α) : List α :=
  List.rec (motive := fun _ => List α) l2 (fun a _ ih => a :: ih) l1

noncomputable def pMapK {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun a _ ih => f a :: ih) l

noncomputable def pFlatMapK {α β : Type} (f : α → List β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun a _ ih => pAppK (f a) ih) l

noncomputable def pRangeK (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun k ih => pAppK ih [k]) n

noncomputable def pAllK {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => p a && ih) l

noncomputable def pAnyK {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => p a || ih) l

noncomputable def pAllLtK (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && p k) n

noncomputable def pMemK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => Nat.beq x r || ih) l

noncomputable def inSK (m p : Nat) (rs : List Nat) (n : Nat) : Bool := Nat.ble m n && pMemK ((n - m) % p) rs

noncomputable def inSpK (prof : List (Nat × Nat × List Nat)) (q n : Nat) : Bool :=
  inSK (pNthK prof q pDflt).1 (pNthK prof q pDflt).2.1 (pNthK prof q pDflt).2.2 n

noncomputable def pStepAK (prof : List (Nat × Nat × List Nat)) (pj : Nat) (it : Option Nat)
    (st : List Nat × Nat) : List Nat × Nat :=
  Option.rec (motive := fun _ => List Nat × Nat) (pMapK (fun a => (a + 1) % pj) st.1, st.2 + 1)
    (fun q => (pFlatMapK (fun a => pFlatMapK (fun r => pMapK
      (fun t => (a + (pNthK prof q pDflt).1 + r + (pNthK prof q pDflt).2.1 * t) % pj) (pRangeK pj))
      (pNthK prof q pDflt).2.2) st.1, st.2 + (pNthK prof q pDflt).1)) it

noncomputable def pRunAK (prof : List (Nat × Nat × List Nat)) (pj : Nat) (b : List (Option Nat))
    (st : List Nat × Nat) : List Nat × Nat :=
  List.rec (motive := fun _ => List Nat × Nat → List Nat × Nat) (fun st => st)
    (fun it _ ih st => ih (pStepAK prof pj it st)) b st

noncomputable def pBrAK (prof : List (Nat × Nat × List Nat)) (m p : Nat) (rs : List Nat) (b : List (Option Nat)) :
    Bool :=
  Nat.ble m (pRunAK prof p b ([0], 0)).2 &&
    ((Nat.beq p 1 && pMemK 0 rs) || pAllK (fun a => pMemK ((a + p - m % p) % p) rs) (pRunAK prof p b ([0], 0)).1)

noncomputable def pChkAK (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) : Bool :=
  pAllLtK B.length (fun j =>
    Nat.blt 0 (pNthK prof j pDflt).2.1 &&
      pAllK (pBrAK prof (pNthK prof j pDflt).1 (pNthK prof j pDflt).2.1 (pNthK prof j pDflt).2.2) (pNthK B j []))

noncomputable def pWalkK (ok : Nat → Nat → Bool) (b ls : List (Option Nat)) : Option (Nat × Option Nat) :=
  List.rec (motive := fun _ => List (Option Nat) → Option (Nat × Option Nat))
    (fun ls => List.rec (motive := fun _ => Option (Nat × Option Nat)) (some (0, none)) (fun _ _ _ => none) ls)
    (fun it _ ih ls => Option.rec (motive := fun _ => Option (Nat × Option Nat))
      (Option.rec (motive := fun _ => Option (Nat × Option Nat)) none
        (fun dh => some (dh.1 + 1, dh.2)) (ih ls))
      (fun q => List.rec (motive := fun _ => Option (Nat × Option Nat)) none
        (fun l ls' _ => Option.rec (motive := fun _ => Option (Nat × Option Nat))
          (Option.rec (motive := fun _ => Option (Nat × Option Nat)) none
            (fun dh => Option.rec (motive := fun _ => Option (Nat × Option Nat)) (some (dh.1, some q))
              (fun _ => none) dh.2) (ih ls'))
          (fun c => Bool.rec (motive := fun _ => Option (Nat × Option Nat)) none
            (Option.rec (motive := fun _ => Option (Nat × Option Nat)) none
              (fun dh => some (dh.1 + c, dh.2)) (ih ls')) (ok q c)) l) ls) it) b ls

noncomputable def pSmallOkK (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (R j n : Nat) (e : Nat × Nat × List (Option Nat)) : Bool :=
  Nat.beq e.1 n && Nat.blt e.2.1 (pLenK (pNthK B j [])) &&
    Option.rec (motive := fun _ => Bool) false
      (fun dh => Option.rec (motive := fun _ => Bool) (Nat.beq dh.1 n) (fun _ => false) dh.2)
      (pWalkK (fun q c => Nat.blt q R && inSpK prof q c && Nat.blt (c * R + pNthK rk q 0) (n * R + pNthK rk j 0))
        (pNthK (pNthK B j []) e.2.1 []) e.2.2)

noncomputable def pBigOkK (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (R N j sp : Nat) (e : Nat × Nat × Nat × List (Option Nat)) : Bool :=
  Nat.blt e.2.1 (pLenK (pNthK B j [])) &&
    Option.rec (motive := fun _ => Bool) false
      (fun dh => Option.rec (motive := fun _ => Bool) false (fun q0 =>
        Nat.blt q0 R && Nat.blt 0 (pNthK prof q0 pDflt).2.1 && Nat.ble N e.2.2.1 &&
        Nat.blt e.2.2.1 (N + sp) && Nat.ble (pNthK prof j pDflt).1 e.2.2.1 &&
        Nat.beq ((e.2.2.1 - (pNthK prof j pDflt).1) % sp) e.1 &&
        Nat.ble (dh.1 + (pNthK prof q0 pDflt).1) N &&
        (Nat.blt 0 dh.1 || Nat.blt (pNthK rk q0 0) (pNthK rk j 0)) &&
        pAllLtK (pNthK prof q0 pDflt).2.1 (fun t => pMemK
          ((e.2.2.1 + sp * t - dh.1 - (pNthK prof q0 pDflt).1) % (pNthK prof q0 pDflt).2.1) (pNthK prof q0 pDflt).2.2))
        dh.2)
      (pWalkK (fun q c => Nat.blt q R && inSpK prof q c && Nat.blt c N) (pNthK (pNthK B j []) e.2.1 []) e.2.2.2)

noncomputable def pChkCK (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat)))) : Bool :=
  pAllLtK (pLenK B) (fun j =>
    Nat.blt (pNthK rk j 0) (pLenK B) && Nat.blt 0 (pNthK prof j pDflt).2.1 &&
    (!Nat.beq (pNthK prof j pDflt).2.1 1 || pMemK 0 (pNthK prof j pDflt).2.2) &&
    pAllLtK N (fun n => !inSpK prof j n || pAnyK (pSmallOkK B prof rk (pLenK B) j n) (pNthK cert j ([], [])).1) &&
    Nat.blt 0 (pNthK sps j 1) && Nat.beq (pNthK sps j 1 % (pNthK prof j pDflt).2.1) 0 &&
    pAllLtK (pNthK sps j 1) (fun r => !pMemK (r % (pNthK prof j pDflt).2.1) (pNthK prof j pDflt).2.2 ||
      pAnyK (fun e => Nat.beq e.1 r && pBigOkK B prof rk (pLenK B) N j (pNthK sps j 1) e) (pNthK cert j ([], [])).2))

omit [Params] in
theorem pAppK_eq {α : Type} (l1 l2 : List α) : pAppK l1 l2 = l1 ++ l2 := by
  induction l1 with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

omit [Params] in
theorem pMapK_eq {α β : Type} (f : α → β) (l : List α) : pMapK f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (f a :: ·) ih

omit [Params] in
theorem pFlatMapK_eq {α β : Type} (f : α → List β) (l : List α) : pFlatMapK f l = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show pAppK (f a) (pFlatMapK f l) = _
    rw [pAppK_eq, ih, List.flatMap_cons]

omit [Params] in
theorem pRangeK_eq (n : Nat) : pRangeK n = List.range n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show pAppK (pRangeK k) [k] = _
    rw [pAppK_eq, ih, List.range_succ]

omit [Params] in
theorem pAllK_eq {α : Type} (p : α → Bool) (l : List α) : pAllK p l = l.all p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (p a && pAllK p l) = _
    rw [ih, List.all_cons]

omit [Params] in
theorem pAnyK_eq {α : Type} (p : α → Bool) (l : List α) : pAnyK p l = l.any p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (p a || pAnyK p l) = _
    rw [ih, List.any_cons]

omit [Params] in
theorem pAllLtK_eq (n : Nat) (p : Nat → Bool) : pAllLtK n p = (List.range n).all p := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (pAllLtK k p && p k) = _
    rw [ih, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]

omit [Params] in
theorem pNthK_eq {α : Type} (l : List α) (n : Nat) (d : α) : pNthK l n d = pNth l n d := by
  rw [pNthK_getD, pNth_eq]

omit [Params] in
theorem pMemK_eq (x : Nat) (l : List Nat) : pMemK x l = pMemB x l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    show (Nat.beq x r || pMemK x l) = (Nat.beq x r || pMemB x l)
    rw [ih]

omit [Params] in
theorem inSpK_eq (prof : List (Nat × Nat × List Nat)) (q n : Nat) : inSpK prof q n = inSp prof q n := by
  simp only [inSpK, inSK, inSp, inS, pNthK_eq, pMemK_eq]

omit [Params] in
theorem pStepAK_eq (prof : List (Nat × Nat × List Nat)) (pj : Nat) (it : Option Nat) (st : List Nat × Nat) :
    pStepAK prof pj it st = pStepA prof pj it st := by
  cases it with
  | none => simp only [pStepAK, pStepA, pMapK_eq]
  | some q => simp only [pStepAK, pStepA, pMapK_eq, pFlatMapK_eq, pRangeK_eq, pNthK_eq]

omit [Params] in
theorem pRunAK_eq (prof : List (Nat × Nat × List Nat)) (pj : Nat) (b : List (Option Nat)) (st : List Nat × Nat) :
    pRunAK prof pj b st = pRunA prof pj b st := by
  induction b generalizing st with
  | nil => rfl
  | cons it r ih =>
    show pRunAK prof pj r (pStepAK prof pj it st) = pRunA prof pj r (pStepA prof pj it st)
    rw [ih, pStepAK_eq]

omit [Params] in
theorem pBrAK_eq (prof : List (Nat × Nat × List Nat)) (m p : Nat) (rs : List Nat) :
    pBrAK prof m p rs = pBrA prof m p rs := by
  funext b
  simp only [pBrAK, pBrA, pAllK_eq, pMemK_eq, pRunAK_eq]

omit [Params] in
theorem pChkAK_eq (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) :
    pChkAK B prof = pChkA B prof := by
  simp only [pChkAK, pChkA, pBrAK_eq, pAllLtK_eq, pAllK_eq, pNthK_eq]

omit [Params] in
theorem pWalkK_eq (ok : Nat → Nat → Bool) (b ls : List (Option Nat)) : pWalkK ok b ls = pWalk ok b ls := by
  induction b generalizing ls with
  | nil => cases ls <;> rfl
  | cons it r ih =>
    cases it with
    | none =>
      show Option.rec (motive := fun _ => Option (Nat × Option Nat)) none (fun dh => some (dh.1 + 1, dh.2)) (pWalkK ok r ls) = _
      rw [ih]
      simp only [pWalk]
      cases pWalk ok r ls <;> rfl
    | some q =>
      cases ls with
      | nil => rfl
      | cons l ls' =>
        cases l with
        | none =>
          show Option.rec (motive := fun _ => Option (Nat × Option Nat)) none (fun dh => Option.rec (motive := fun _ => Option (Nat × Option Nat)) (some (dh.1, some q)) (fun _ => none) dh.2)
            (pWalkK ok r ls') = _
          rw [ih]
          simp only [pWalk]
          rcases pWalk ok r ls' with _ | ⟨d, _ | x⟩ <;> rfl
        | some c =>
          show Bool.rec (motive := fun _ => Option (Nat × Option Nat)) none (Option.rec (motive := fun _ => Option (Nat × Option Nat)) none (fun dh => some (dh.1 + c, dh.2)) (pWalkK ok r ls'))
            (ok q c) = _
          rw [ih]
          simp only [pWalk]
          cases ok q c <;> cases pWalk ok r ls' <;> rfl

omit [Params] in
theorem pChkCK_eq (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat)))) :
    pChkCK B prof rk N sps cert = pChkC B prof rk N sps cert := by
  have hs : ∀ R j n, pSmallOkK B prof rk R j n = pSmallOk B prof rk R j n := by
    intro R j n
    funext e
    simp only [pSmallOkK, pSmallOk, pLenK_eq, pNthK_eq, inSpK_eq, pWalkK_eq]
    rcases pWalk _ _ _ with _ | ⟨d, _ | x⟩ <;> rfl
  have hb : ∀ R j sp, pBigOkK B prof rk R N j sp = pBigOk B prof rk R N j sp := by
    intro R j sp
    funext e
    simp only [pBigOkK, pBigOk, pLenK_eq, pNthK_eq, inSpK_eq, pWalkK_eq, pAllLtK_eq, pMemK_eq]
    rcases pWalk _ _ _ with _ | ⟨d, _ | x⟩ <;> rfl
  simp only [pChkCK, pChkC, pLenK_eq, pNthK_eq, pAllLtK_eq, pAnyK_eq, pMemK_eq, inSpK_eq, hs, hb]

omit [Params] in
theorem pMem {α : Type} (l : List α) (i : Nat) (d : α) (hi : Nat.blt i (pLenK l) = true) : pNthK l i d ∈ l := by
  rw [Nat.blt_eq, pLenK_eq] at hi
  rw [pNthK_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

def pAllIdx (P : Nat → Prop) : Nat → Nat → Prop
  | _, 0 => True
  | i, n + 1 => P i ∧ pAllIdx P (i + 1) n

omit [Params] in
theorem pAllIdx_lt (P : Nat → Prop) : ∀ i n, pAllIdx P i n → ∀ j, i ≤ j → j < i + n → P j
  | _, 0, _, _, h1, h2 => absurd h2 (by omega)
  | i, n + 1, ⟨hp, hr⟩, j, h1, h2 => by
    by_cases hj : j = i
    · exact hj ▸ hp
    · exact pAllIdx_lt P (i + 1) n hr j (by omega) (by omega)

theorem pEqSymm (a b : Nat) : (⌈a = b⌉ : HProp) ==> ⌈b = a⌉ := by
  intro h hh
  obtain ⟨he, hh⟩ := HProp.hpure_elim_hempty hh
  exact HProp.hpure_intro_hempty hh he.symm

theorem pDrop (P : Prop) : (⌈P⌉ : HProp) ==> emp := by
  intro h hh
  exact (HProp.hpure_elim_hempty hh).2

theorem pDup (P : Prop) : (⌈P⌉ : HProp) ==> ⌈P⌉ ✶ ⌈P⌉ := by
  intro h hh
  obtain ⟨hp, he⟩ := HProp.hpure_elim_hempty hh
  exact (HProp.hstar_hpure_l P _ h).2 ⟨hp, HProp.hpure_intro_hempty he hp⟩

theorem pDupNe (a b : Nat) : (⌈a ≠ b⌉ : HProp) ==> ⌈a ≠ b⌉ ✶ ⌈b ≠ a⌉ := by
  intro h hh
  obtain ⟨hp, he⟩ := HProp.hpure_elim_hempty hh
  exact (HProp.hstar_hpure_l _ _ h).2 ⟨hp, HProp.hpure_intro_hempty he (Ne.symm hp)⟩

end Sep

namespace Sep.Xsearch

open HProp Notation

variable [Params]

theorem hpure_true {P : Prop} (hp : P) : (⌈P⌉ : HProp) = HProp.hempty := by
  funext h
  exact propext ⟨fun hh => (HProp.hpure_elim_hempty hh).2,
    fun hh => HProp.hpure_intro_hempty hh hp⟩

theorem hstar_hexists_rr {A : Sort _} (H : HProp) (J : A → HProp) :
    H ✶ (HProp.hexists J) = ∃✶ x, H ✶ J x := by
  rw [HProp.hstar_comm, HProp.hstar_hexists]
  exact congrArg _ (funext fun x => HProp.hstar_comm _ _)

def hdisj (H1 H2 : HProp) : HProp := fun h => H1 h ∨ H2 h

theorem hdisj_star_l (H1 H2 K : HProp) :
    hdisj H1 H2 ✶ K = hdisj (H1 ✶ K) (H2 ✶ K) := by
  funext h
  apply propext
  constructor
  · intro hh
    obtain ⟨h1, h2, ha, hb, hd, he⟩ := HProp.hstar_elim hh
    rcases ha with ha | ha
    · exact Or.inl (he ▸ HProp.hstar_intro ha hb hd)
    · exact Or.inr (he ▸ HProp.hstar_intro ha hb hd)
  · intro hh
    rcases hh with hh | hh
    · obtain ⟨h1, h2, ha, hb, hd, he⟩ := HProp.hstar_elim hh
      exact he ▸ HProp.hstar_intro (show hdisj H1 H2 h1 from Or.inl ha) hb hd
    · obtain ⟨h1, h2, ha, hb, hd, he⟩ := HProp.hstar_elim hh
      exact he ▸ HProp.hstar_intro (show hdisj H1 H2 h1 from Or.inr ha) hb hd

theorem hdisj_star_r (K H1 H2 : HProp) :
    K ✶ hdisj H1 H2 = hdisj (K ✶ H1) (K ✶ H2) := by
  rw [HProp.hstar_comm, hdisj_star_l, HProp.hstar_comm K H1, HProp.hstar_comm K H2]

theorem hdisj_hexists {A : Sort _} (J K : A → HProp) :
    HProp.hexists (fun x => hdisj (J x) (K x))
      = hdisj (HProp.hexists J) (HProp.hexists K) := by
  funext h
  simp only [HProp.hexists, hdisj]
  exact propext exists_or

theorem hdisj_elim {H1 H2 H : HProp} (h1 : H1 ==> H) (h2 : H2 ==> H) :
    hdisj H1 H2 ==> H := by
  intro h hh
  rcases hh with hh | hh
  · exact h1 h hh
  · exact h2 h hh

theorem hdisj_left {H H1 H2 : HProp} (h : H ==> H1) : H ==> hdisj H1 H2 :=
  fun h' hh => Or.inl (h h' hh)

theorem hdisj_right {H H1 H2 : HProp} (h : H ==> H2) : H ==> hdisj H1 H2 :=
  fun h' hh => Or.inr (h h' hh)

def hasLoc (p : Loc) (H : HProp) : Prop := ∀ h, H h → p ∈ h

def neLocs (p q : Loc) (H : HProp) : Prop := ∀ h, H h → p ≠ q

theorem hasLoc_single (p : Loc) (v : val) : hasLoc p (HProp.hsingle p v) := by
  intro h hh
  simp only [HProp.hsingle] at hh
  rw [hh]
  exact (Finmap.mem_singleton p p v).2 rfl

theorem hasLoc_star_l {p : Loc} {H1 H2 : HProp} (h1 : hasLoc p H1) :
    hasLoc p (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, he⟩ := HProp.hstar_elim hh
  rw [he]
  exact Finmap.mem_union.2 (Or.inl (h1 a ha))

theorem hasLoc_star_r {p : Loc} {H1 H2 : HProp} (h2 : hasLoc p H2) :
    hasLoc p (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, he⟩ := HProp.hstar_elim hh
  rw [he]
  exact Finmap.mem_union.2 (Or.inr (h2 b hb))

theorem hasLoc_hexists {A : Sort _} {p : Loc} {J : A → HProp}
    (h : ∀ a, hasLoc p (J a)) : hasLoc p (HProp.hexists J) := by
  intro hh hj
  simp only [HProp.hexists] at hj
  obtain ⟨a, ha⟩ := hj
  exact h a hh ha

theorem hasLoc_disj {p : Loc} {H1 H2 : HProp} (h1 : hasLoc p H1)
    (h2 : hasLoc p H2) : hasLoc p (hdisj H1 H2) := by
  intro h hh
  rcases hh with hh | hh
  · exact h1 h hh
  · exact h2 h hh

theorem hasLoc_mono {p : Loc} {F G : HProp} (h : F ==> G) (hg : hasLoc p G) :
    hasLoc p F := fun hh hf => hg hh (h hh hf)

def safeFar (f : Loc) (F : HProp) : Prop := f = 0 ∨ hasLoc f F

theorem safeFar_nil {f : Loc} {F : HProp} (h : f = 0) : safeFar f F := Or.inl h

theorem safeFar_loc {f : Loc} {F : HProp} (h : hasLoc f F) : safeFar f F :=
  Or.inr h

theorem safeFar_step {a b : Loc} {F : HProp} (h1 : a ≠ b → hasLoc a F)
    (h2 : a = b → safeFar b F) : safeFar a F := by
  by_cases h : a = b
  · rcases h2 h with hb | hb
    · exact Or.inl (h ▸ hb)
    · exact Or.inr (h ▸ hb)
  · exact Or.inr (h1 h)

theorem neLocs_star {p q : Loc} {H1 H2 : HProp}
    (h1 : hasLoc p H1) (h2 : hasLoc q H2) : neLocs p q (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, _⟩ := HProp.hstar_elim hh
  intro hpq
  exact hd p (h1 a ha) (hpq ▸ h2 b hb)

theorem neLocs_star' {p q : Loc} {H1 H2 : HProp}
    (h1 : hasLoc q H1) (h2 : hasLoc p H2) : neLocs p q (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, _⟩ := HProp.hstar_elim hh
  intro hpq
  exact hd q (h1 a ha) (hpq ▸ h2 b hb)

theorem neLocs_star_l {p q : Loc} {H1 H2 : HProp} (h : neLocs p q H1) :
    neLocs p q (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨a, b, ha, _, _, _⟩ := HProp.hstar_elim hh
  exact h a ha

theorem neLocs_star_r {p q : Loc} {H1 H2 : HProp} (h : neLocs p q H2) :
    neLocs p q (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨a, b, _, hb, _, _⟩ := HProp.hstar_elim hh
  exact h b hb

theorem neLocs_const {p q : Loc} {H : HProp} (h : p ≠ q) : neLocs p q H :=
  fun _ _ => h

theorem neLocs_disj {p q : Loc} {H1 H2 : HProp} (h1 : neLocs p q H1)
    (h2 : neLocs p q H2) : neLocs p q (hdisj H1 H2) := by
  intro h hh
  rcases hh with hh | hh
  · exact h1 h hh
  · exact h2 h hh

theorem neLocs_pure_star {p q : Loc} {P : Prop} {H : HProp}
    (h : P → neLocs p q H) : neLocs p q (⌈P⌉ ✶ H) := by
  intro hh hj
  rcases (HProp.hstar_hpure_l P H hh).1 hj with ⟨hP, hH⟩
  exact h hP hh hH

theorem neLocs_hexists {A : Sort _} {p q : Loc} {J : A → HProp}
    (h : ∀ a, neLocs p q (J a)) : neLocs p q (HProp.hexists J) := by
  intro hh hj
  simp only [HProp.hexists] at hj
  obtain ⟨a, ha⟩ := hj
  exact h a hh ha

theorem himpl_of_neLocs {p q : Loc} {H R : HProp} (hn : neLocs p q H)
    (k : p ≠ q → H ==> R) : H ==> R := fun h hh => k (hn h hh) h hh

def lfpG {α : Type} (F : (α → HProp) → α → HProp) : α → HProp :=
  fun a h => ∀ X : α → HProp, (∀ b, F X b ==> X b) → X a h

theorem lfpG_induct {α : Type} (F : (α → HProp) → α → HProp) (X : α → HProp)
    (hX : ∀ b, F X b ==> X b) (a : α) : lfpG F a ==> X a := fun _ hh => hh X hX

theorem frame_l_of (H3 : HProp) {H1 H2 : HProp} (h : H1 ==> H2) :
    H1 ✶ H3 ==> H2 ✶ H3 := HProp.himpl_frame_l h

theorem frame_r_of (H1 : HProp) {H2 H3 : HProp} (h : H2 ==> H3) :
    H1 ✶ H2 ==> H1 ✶ H3 := HProp.himpl_frame_r h

theorem perm_comm (A B : HProp) : A ✶ B ==> B ✶ A := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_refl _

theorem perm_swap (A B C : HProp) : A ✶ (B ✶ C) ==> B ✶ (A ✶ C) := by
  rw [← HProp.hstar_assoc, HProp.hstar_comm A B, HProp.hstar_assoc]
  exact HProp.himpl_refl _

theorem himpl_of_eq {A B : HProp} (h : A = B) : A ==> B := h ▸ HProp.himpl_refl A

theorem wand_use {A B D C : HProp} (h1 : D ==> A) (h2 : B ==> C) :
    (A -✶ B) ✶ D ==> C := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_trans (HProp.himpl_frame_l h1)
    (HProp.himpl_trans (HProp.hwand_cancel A B) h2)

theorem wand_use2 {A B E F C : HProp} (h1 : E ==> A) (h2 : B ✶ F ==> C) :
    (A -✶ B) ✶ (E ✶ F) ==> C := by
  refine HProp.himpl_trans (HProp.himpl_frame_r (HProp.himpl_frame_l h1)) ?_
  rw [← HProp.hstar_assoc, HProp.hstar_comm (A -✶ B) A]
  exact HProp.himpl_trans (HProp.himpl_frame_l (HProp.hwand_cancel A B)) h2

def hpack (H1 H2 : HProp) : HProp := H1 ✶ H2

theorem hpack_eq (H1 H2 : HProp) : hpack H1 H2 = H1 ✶ H2 := rfl

def holdsP (P : Prop) (H : HProp) : Prop := ∀ h, H h → P

theorem holdsP_pure (P : Prop) : holdsP P (⌈P⌉ : HProp) :=
  fun _ hh => (HProp.hpure_elim hh).1

theorem holdsP_star_l {P : Prop} {H1 H2 : HProp} (h : holdsP P H1) :
    holdsP P (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨a, _, ha, _, _, _⟩ := HProp.hstar_elim hh
  exact h a ha

theorem holdsP_star_r {P : Prop} {H1 H2 : HProp} (h : holdsP P H2) :
    holdsP P (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨_, b, _, hb, _, _⟩ := HProp.hstar_elim hh
  exact h b hb

theorem himpl_of_holds {P : Prop} {H R : HProp} (hn : holdsP P H)
    (k : P → H ==> R) : H ==> R := fun h hh => k (hn h hh) h hh

theorem holdsP_of_top {P : Prop} {H : HProp} (h : H ==> ⌈P⌉ ✶ HProp.htop) : holdsP P H :=
  fun hh hx => ((HProp.hstar_hpure_l P _ hh).1 (h hh hx)).1

theorem himpl_pure_top {P : Prop} {H : HProp} (hp : P) : H ==> ⌈P⌉ ✶ HProp.htop :=
  fun hh _ => (HProp.hstar_hpure_l P _ hh).2 ⟨hp, HProp.htop_intro hh⟩

theorem fwand_use {α : Sort _} {J : α → HProp} {A B E F C : HProp} (v : α)
    (hj : J v = (A -✶ B)) (h1 : E ==> A) (h2 : B ✶ F ==> C) :
    HProp.hforall J ✶ (E ✶ F) ==> C := by
  have hw : HProp.hforall J ==> (A -✶ B) := hj ▸ HProp.hforall_specialize v J
  refine HProp.himpl_trans (HProp.himpl_frame_l hw) ?_
  refine HProp.himpl_trans (HProp.himpl_frame_r (HProp.himpl_frame_l h1)) ?_
  rw [← HProp.hstar_assoc, HProp.hstar_comm (A -✶ B) A]
  exact HProp.himpl_trans (HProp.himpl_frame_l (HProp.hwand_cancel A B)) h2

def hwith (H1 H2 : HProp) : HProp := fun h => H1 h ∧ H2 h

theorem hwith_intro {H A B : HProp} (h1 : H ==> A) (h2 : H ==> B) :
    H ==> hwith A B := fun h hh => ⟨h1 h hh, h2 h hh⟩

theorem hwith_l (A B : HProp) : hwith A B ==> A := fun _ hh => hh.1

theorem hwith_r (A B : HProp) : hwith A B ==> B := fun _ hh => hh.2

theorem lfpG_induct_with {α : Type} (F : (α → HProp) → α → HProp) (M : α → HProp)
    (hmono : ∀ X Y : α → HProp, (∀ a, X a ==> Y a) → ∀ a, F X a ==> F Y a)
    (hfold : ∀ a, F (lfpG F) a ==> lfpG F a)
    (hM : ∀ a, F (fun b => hwith (lfpG F b) (M b)) a ==> M a) (a : α) : lfpG F a ==> M a := by
  have h : ∀ a, lfpG F a ==> hwith (lfpG F a) (M a) :=
    lfpG_induct F _ (fun b => hwith_intro
      (HProp.himpl_trans (hmono _ _ (fun c => hwith_l _ _) b) (hfold b)) (hM b))
  exact HProp.himpl_trans (h a) (hwith_r _ _)

theorem star_pure_drop (H : HProp) (P : Prop) : H ✶ ⌈P⌉ ==> H := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_hstar_hpure_l (fun _ => HProp.himpl_refl _)

theorem pures_emp_cons {P : Prop} {R : HProp} (h : R ==> emp) : ⌈P⌉ ✶ R ==> emp := by
  rw [← HProp.hstar_hempty_l emp]
  exact HProp.himpl_frame_lr (Sep.pDrop P) h

theorem pures_conj {A B : HProp} {P Q : Prop} (ha : A ==> ⌈P⌉) (hb : B ==> ⌈Q⌉) : A ✶ B ==> ⌈P ∧ Q⌉ := by
  rw [← HProp.hstar_hpure_conj]
  exact HProp.himpl_frame_lr ha hb

theorem emp_pure_true : (emp : HProp) ==> ⌈True⌉ := HProp.himpl_hempty_hpure trivial

theorem pure_l_emp {P : Prop} {R : HProp} (h : P → (emp ==> R)) : ⌈P⌉ ==> R := by
  rw [← HProp.hstar_hempty_r ⌈P⌉]
  exact HProp.himpl_hstar_hpure_l h

theorem emp_star_intro {A B : HProp} (ha : emp ==> A) (hb : emp ==> B) : emp ==> A ✶ B := by
  rw [← HProp.hstar_hempty_l emp]
  exact HProp.himpl_frame_lr ha hb

theorem star_drop_emp {H R : HProp} (h : R ==> emp) : H ✶ R ==> H :=
  HProp.himpl_trans (HProp.himpl_frame_r h) (by rw [HProp.hstar_hempty_r]; exact HProp.himpl_refl _)

theorem pure_l_of_holds {H G : HProp} {P : Prop} (hp : holdsP P H) (h : H ==> G) : H ==> ⌈P⌉ ✶ G :=
  fun k hk => Sep.pure_l_intro (hp k hk) h k hk

theorem holdsP_mono_imp {P : Prop} {F G : HProp} (h : F ==> G) (hg : holdsP P G) : holdsP P F :=
  fun k hk => hg k (h k hk)

theorem holdsP_ne_symm {a b : Loc} {H : HProp} (h : holdsP (a ≠ b) H) : holdsP (b ≠ a) H :=
  fun k hk => Ne.symm (h k hk)

theorem ne_far {a b : Loc} {X F : HProp} (hx : hasLoc a X) (hz : a ≠ 0) (hF : safeFar b F) :
    holdsP (a ≠ b) (X ✶ F) := by
  intro h hh
  obtain ⟨h1, h2, m1, m2, hd, _⟩ := HProp.hstar_elim hh
  rcases hF with h0 | hl
  · rw [h0]
    exact hz
  · intro heq
    rw [heq] at hx
    exact hd b (hx h1 m1) (hl h2 m2)

theorem wseg_retarget {σ : Type} (c : σ → σ → Int → HProp) (f : σ → σ) (loc : σ → Loc) (e : Loc)
    (F : HProp) (hF : safeFar e F) (hc : ∀ s s' w, hasLoc (loc s) (c s s' w))
    (hz : ∀ s s' w h, c s s' w h → loc s ≠ 0)
    (hg : ∀ s s' w, loc s ≠ e → c s s' w ==> c (f s) (f s') w) (k : Nat) (n : Int) (s t : σ) :
    Sep.wseg c k n s t ✶ F ==> Sep.wseg c k n (f s) (f t) ✶ F := by
  refine Sep.wseg_map_fr c c f F (fun s s' w => ?_) k n s t
  intro h hh
  obtain ⟨h1, h2, hc1, hf2, hd, he⟩ := HProp.hstar_elim hh
  have hne : loc s ≠ e := by
    rcases hF with h0 | hl
    · rw [h0]
      exact hz s s' w h1 hc1
    · intro heq
      have m1 := hc s s' w h1 hc1
      have m2 := hl h2 hf2
      rw [heq] at m1
      exact hd e m1 m2
  rw [he]
  exact HProp.hstar_intro (hg s s' w hne h1 hc1) hf2 hd

theorem safeFar_star_r {e : Loc} {W F : HProp} (h : safeFar e F) : safeFar e (W ✶ F) :=
  h.elim Or.inl (fun hl => Or.inr (hasLoc_star_r hl))

theorem cell_far {H G : HProp} {a e : Loc} (hH : hasLoc a H) (hz : ∀ h, H h → a ≠ 0)
    (hG : safeFar e G) : H ✶ G ==> ⌈a ≠ e⌉ ✶ (H ✶ G) := by
  intro h hh
  refine (HProp.hstar_hpure_l _ _ h).2 ⟨?_, hh⟩
  obtain ⟨h1, h2, m1, m2, hd, _⟩ := HProp.hstar_elim hh
  rcases hG with h0 | hl
  · rw [h0]
    exact hz h1 m1
  · intro heq
    rw [heq] at hH
    exact hd e (hH h1 m1) (hl h2 m2)

theorem himpl_pure_of {H : HProp} {P : Prop} (hp : holdsP P H) : H ==> ⌈P⌉ ✶ H :=
  fun h hh => (HProp.hstar_hpure_l P H h).2 ⟨hp h hh, hh⟩

theorem wseg_retarget_prev {σ : Type} (c : σ → σ → Int → HProp) (f : σ → σ) (adr prv : σ → Loc)
    (e : Loc) (F : HProp) (hF : safeFar e F) (hc : ∀ s s' w, hasLoc (adr s) (c s s' w))
    (hz : ∀ s s' w h, c s s' w h → adr s ≠ 0) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w))
    (hg : ∀ s s' w, prv s ≠ e → c s s' w ==> c (f s) (f s') w) (k : Nat) :
    ∀ (n : Int) (s t : σ), prv s ≠ e →
      Sep.wseg c k n s t ✶ F ==> Sep.wseg c k n (f s) (f t) ✶ F := by
  induction k with
  | zero =>
    intro n s t _
    show ⌈s = t ∧ n = 0⌉ ✶ F ==> ⌈f s = f t ∧ n = 0⌉ ✶ F
    refine HProp.himpl_hstar_hpure_l (fun ⟨h1, h2⟩ => ?_)
    exact HProp.himpl_hstar_hpure_r ⟨congrArg f h1, h2⟩ (HProp.himpl_refl _)
  | succ k ih =>
    intro n s t h0
    show (∃✶ s', ∃✶ w, c s s' w ✶ Sep.wseg c k (n - w) s' t) ✶ F ==>
      (∃✶ s', ∃✶ w, c (f s) s' w ✶ Sep.wseg c k (n - w) s' (f t)) ✶ F
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun s' => ?_)
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun w => ?_)
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_r (f s') ?_
    rw [HProp.hstar_hexists]
    refine HProp.himpl_hexists_r w ?_
    rw [HProp.hstar_assoc, HProp.hstar_assoc]
    refine HProp.himpl_trans (cell_far (hc s s' w) (hz s s' w) (safeFar_star_r hF)) ?_
    refine HProp.himpl_hstar_hpure_l (fun hne => ?_)
    refine HProp.himpl_trans (HProp.himpl_frame_l (himpl_pure_of (hp s s' w))) ?_
    rw [HProp.hstar_assoc]
    refine HProp.himpl_hstar_hpure_l (fun hpr => ?_)
    refine HProp.himpl_frame_lr (hg s s' w h0) (ih (n - w) s' t ?_)
    rw [hpr]
    exact hne

theorem hasLoc_wseg_last {σ : Type} (c : σ → σ → Int → HProp) (adr prv : σ → Loc)
    (hc : ∀ s s' w, hasLoc (adr s) (c s s' w)) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w)) :
    ∀ (k : Nat) (n : Int) (s t : σ), hasLoc (prv t) (Sep.wseg c (k + 1) n s t)
  | 0, n, s, t => by
    intro h hh
    obtain ⟨s', hh⟩ := HProp.hexists_elim hh
    obtain ⟨w, hh⟩ := HProp.hexists_elim hh
    obtain ⟨h1, h2, m1, m2, _, he⟩ := HProp.hstar_elim hh
    obtain ⟨⟨hst, _⟩, _⟩ := HProp.hpure_elim_hempty m2
    rw [he, ← hst, hp s s' w h1 m1]
    exact Finmap.mem_union.2 (Or.inl (hc s s' w h1 m1))
  | k + 1, n, s, t => by
    show hasLoc (prv t) (∃✶ s', ∃✶ w, c s s' w ✶ Sep.wseg c (k + 1) (n - w) s' t)
    exact hasLoc_hexists (fun s' => hasLoc_hexists (fun w =>
      hasLoc_star_r (hasLoc_wseg_last c adr prv hc hp k (n - w) s' t)))

theorem wseg_bk_zero {σ : Type} (c : σ → σ → Int → HProp) (adr prv : σ → Loc)
    (hc : ∀ s s' w, hasLoc (adr s) (c s s' w)) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w))
    (F : HProp) (k : Nat) (n : Int) (s t : σ) (hl : hasLoc (prv t) F) :
    holdsP (k = 0) (Sep.wseg c k n s t ✶ F) := by
  intro h hh
  cases k with
  | zero => rfl
  | succ k =>
    obtain ⟨h1, h2, m1, m2, hd, _⟩ := HProp.hstar_elim hh
    exact absurd (hl h2 m2) (hd _ (hasLoc_wseg_last c adr prv hc hp k n s t h1 m1))

theorem holdsP_abs_prev {σ : Type} (c : σ → σ → Int → HProp) (adr prv : σ → Loc)
    (hc : ∀ s s' w, hasLoc (adr s) (c s s' w)) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w))
    (X F : HProp) (st en : σ) (cond : Nat → Prop) (a : Loc)
    (hA : X ==> ∃✶ k, ∃✶ n, Sep.wseg c k n st en ✶ ⌈cond k⌉) (hF : hasLoc a F) (h0 : prv st ≠ a) :
    holdsP (a ≠ prv en) (X ✶ F) := by
  intro h hh
  obtain ⟨h1, h2, m1, m2, hd, _⟩ := HProp.hstar_elim hh
  obtain ⟨k, hk⟩ := HProp.hexists_elim (hA h1 m1)
  obtain ⟨n, hn⟩ := HProp.hexists_elim hk
  obtain ⟨g1, g2, s1, _, hd2, he2⟩ := HProp.hstar_elim hn
  cases k with
  | zero =>
    obtain ⟨⟨hst, _⟩, _⟩ := HProp.hpure_elim_hempty s1
    rw [← hst]
    exact fun e => h0 e.symm
  | succ k =>
    intro heq
    have m := hasLoc_wseg_last c adr prv hc hp k n st en g1 s1
    rw [← heq] at m
    have : a ∈ h1 := by rw [he2]; exact Finmap.mem_union.2 (Or.inl m)
    exact hd _ this (hF h2 m2)

theorem hasLoc_wseg_pos {σ : Type} (c : σ → σ → Int → HProp) (loc : σ → Loc)
    (hc : ∀ s s' w, hasLoc (loc s) (c s s' w)) (k : Nat) (n : Int) (s t : σ) (hk : 1 ≤ k) :
    hasLoc (loc s) (Sep.wseg c k n s t) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  show hasLoc (loc s) (∃✶ s', ∃✶ w, c s s' w ✶ Sep.wseg c k' (n - w) s' t)
  exact hasLoc_hexists (fun s' => hasLoc_hexists (fun w => hasLoc_star_l (hc s s' w)))

theorem hasLoc_wseg_ne {σ : Type} (c : σ → σ → Int → HProp) (loc : σ → Loc)
    (hc : ∀ s s' w, hasLoc (loc s) (c s s' w)) (k : Nat) (n : Int) (s t : σ) (h : loc s ≠ loc t) :
    hasLoc (loc s) (Sep.wseg c k n s t) := by
  cases k with
  | zero =>
    intro _ hp
    obtain ⟨⟨h1, _⟩, _⟩ := HProp.hpure_elim_hempty hp
    exact absurd (congrArg loc h1) h
  | succ k =>
    exact hasLoc_hexists (fun s' => hasLoc_hexists (fun w => hasLoc_star_l (hc s s' w)))

omit [Params] in
theorem inv_len0 : (0 : Int) = ((0 : Nat) : Int) := rfl

omit [Params] in
theorem inv_hyp {p : Prop} (h : p) : p := h

omit [Params] in
theorem inv_ne_of_eq {x y : Nat} (h : x = y) (hy : y ≠ 0) : x ≠ 0 := h ▸ hy

omit [Params] in
theorem inv_len_step {m w : Int} {k : Nat} (hw : w = 1) (h : m = (k : Int)) :
    m + w = ((k + 1 : Nat) : Int) := by
  subst hw
  rw [h]
  push_cast
  rfl

omit [Params] in
theorem inv_imp0 {α : Sort _} (x : α) : (0 : Nat) = 0 → x = x := fun _ => rfl

omit [Params] in
theorem inv_imp_step {α : Sort _} {k : Nat} (x y : α) : k + 1 = 0 → x = y :=
  fun h => absurd h (Nat.succ_ne_zero k)

omit [Params] in
theorem inv_or0 (y : Nat) : (0 : Nat) = 0 ∨ y ≠ 0 := Or.inl rfl

omit [Params] in
theorem inv_or_step {k x y : Nat} (hz : x ≠ 0) (himp : k = 0 → x = y) (hor : k = 0 ∨ y ≠ 0) :
    k + 1 = 0 ∨ y ≠ 0 := by
  right
  rcases hor with h | h
  · rw [← himp h]
    exact hz
  · exact h

omit [Params] in
theorem inv_rel0 (x b : Int) : x - x = b * ((0 : Nat) : Int) := by simp

omit [Params] in
theorem inv_rel0z (x : Int) : x - x = 0 := by simp

omit [Params] in
theorem inv_rel0le (x b : Int) : x - x ≤ b * ((0 : Nat) : Int) := by simp

omit [Params] in
theorem inv_rel0zle (x : Int) : x - x ≤ 0 := by simp

omit [Params] in
theorem inv_rel_l {x y z b : Int} {k : Nat} (hr : x - y = b) (hi : y - z = b * (k : Int)) :
    x - z = b * ((k + 1 : Nat) : Int) := by
  rw [show x - z = (x - y) + (y - z) by omega, hr, hi]
  push_cast
  rw [Int.mul_add, Int.mul_one, Int.add_comm]

omit [Params] in
theorem inv_rel_r {x y z b : Int} {k : Nat} (hi : x - y = b * (k : Int)) (hr : y - z = b) :
    x - z = b * ((k + 1 : Nat) : Int) := by
  rw [show x - z = (x - y) + (y - z) by omega, hr, hi]
  push_cast
  rw [Int.mul_add, Int.mul_one]

omit [Params] in
theorem inv_rel_lz {x y z : Int} (hr : x - y = 0) (hi : y - z = 0) : x - z = 0 := by omega

omit [Params] in
theorem inv_rel_lle {x y z b : Int} {k : Nat} (hr : x - y ≤ b) (hi : y - z ≤ b * (k : Int)) :
    x - z ≤ b * ((k + 1 : Nat) : Int) := by
  have h := Int.add_le_add hr hi
  rw [show x - y + (y - z) = x - z by omega] at h
  push_cast
  rw [Int.mul_add, Int.mul_one, Int.add_comm]
  exact h

omit [Params] in
theorem inv_rel_rle {x y z b : Int} {k : Nat} (hi : x - y ≤ b * (k : Int)) (hr : y - z ≤ b) :
    x - z ≤ b * ((k + 1 : Nat) : Int) := by
  have h := Int.add_le_add hi hr
  rw [show x - y + (y - z) = x - z by omega] at h
  push_cast
  rw [Int.mul_add, Int.mul_one]
  exact h

omit [Params] in
theorem inv_rel_lzle {x y z : Int} (hr : x - y ≤ 0) (hi : y - z ≤ 0) : x - z ≤ 0 := by omega

def hguard (P : Prop) (H : HProp) : HProp := fun h => P → H h

theorem hguard_intro {P : Prop} {H R : HProp} (k : P → H ==> R) : H ==> hguard P R :=
  fun h hh hp => k hp h hh

theorem hguard_elim {P : Prop} {H : HProp} (hp : P) : hguard P H ==> H :=
  fun _ hh => hh hp

theorem view_hexists {H X : HProp} {R V C : Int → HProp} (h : H ==> ∃✶ w, R w ✶ (V w ✶ X))
    (hv : ∀ w, V w ==> C w) : H ==> ∃✶ w, R w ✶ (C w ✶ X) :=
  HProp.himpl_trans h (HProp.himpl_hexists_l (fun w => HProp.himpl_hexists_r w
    (HProp.himpl_frame_r (HProp.himpl_frame_l (hv w)))))

theorem holdsP_true {H : HProp} : holdsP True H := fun _ _ => trivial

theorem star_emp_r (H : HProp) : H ==> H ✶ emp := by
  rw [HProp.hstar_hempty_r]
  exact HProp.himpl_refl _

theorem star_emp_elim (H : HProp) : H ✶ emp ==> H := by
  rw [HProp.hstar_hempty_r]
  exact HProp.himpl_refl _

theorem hdisj_star_elim {A B K H : HProp} (h1 : A ✶ K ==> H) (h2 : B ✶ K ==> H) : hdisj A B ✶ K ==> H := by
  rw [hdisj_star_l]
  exact hdisj_elim h1 h2

noncomputable def gChain {σ : Type} (c : σ → σ → Int → HProp) (X : Nat → σ → σ → Int → HProp)
    (b : List (Option Nat)) : σ → σ → Int → HProp :=
  List.rec (motive := fun _ => σ → σ → Int → HProp) (fun s t n => ⌈s = t ∧ n = 0⌉)
    (fun it _ ih s t n => Option.rec (motive := fun _ => HProp)
      (∃✶ s', ∃✶ w, c s s' w ✶ ih s' t (n - w))
      (fun j => ∃✶ s', ∃✶ m, X j s s' m ✶ ih s' t (n - m)) it) b

def gA {σ : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (j : Nat) (s t : σ) (n : Int) : HProp :=
  ∃✶ k, wseg c k n s t ✶ ⌈pLen B j k⌉

def gAny (B : List (List (List (Option Nat)))) (j : Nat) (f : List (Option Nat) → HProp) : HProp :=
  fun h => ∃ b ∈ pNthK B j [], f b h

def gQ {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp) (a : ι) : HProp :=
  ∃✶ j, gA c B (mem a) (st a) (E a j) (N a j) ✶ T a j

theorem gK_intro {W : Nat → HProp} {P : Nat → Prop} {h : Heap} (k : Nat) (hw : W k h) (hp : P k) :
    (∃✶ k, W k ✶ ⌈P k⌉) h :=
  HProp.hexists_intro k _ ((HProp.hstar_hpure_r (P k) (W k) h).2 ⟨hw, hp⟩)

theorem gK_elim {W : Nat → HProp} {P : Nat → Prop} {h : Heap} (hh : (∃✶ k, W k ✶ ⌈P k⌉) h) :
    ∃ k, W k h ∧ P k := by
  obtain ⟨k, hh⟩ := HProp.hexists_elim hh
  exact ⟨k, (HProp.hstar_hpure_r (P k) (W k) h).1 hh⟩

theorem gChain_abs {σ : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat)))) :
    ∀ (b : List (Option Nat)) (s t : σ) (n : Int),
      gChain c (gA c B) b s t n ==> ∃✶ k, wseg c k n s t ✶ ⌈pLenC (pLen B) b k⌉
  | [], s, t, n => by
    intro h hh
    exact gK_intro 0 hh (show pLenC (pLen B) [] 0 from rfl)
  | none :: r, s, t, n => by
    intro h hh
    obtain ⟨s', hh⟩ := HProp.hexists_elim hh
    obtain ⟨w, hh⟩ := HProp.hexists_elim hh
    obtain ⟨h1, h2, m1, m2, hd, he⟩ := HProp.hstar_elim hh
    obtain ⟨k, hw, hk⟩ := gK_elim (gChain_abs c B r s' t (n - w) h2 m2)
    refine gK_intro (k + 1) ?_ ⟨k, rfl, hk⟩
    show (∃✶ s'', ∃✶ w', c s s'' w' ✶ wseg c k (n - w') s'' t) h
    exact HProp.hexists_intro s' _ (HProp.hexists_intro w _ (he ▸ HProp.hstar_intro m1 hw hd))
  | some j :: r, s, t, n => by
    intro h hh
    obtain ⟨s', hh⟩ := HProp.hexists_elim hh
    obtain ⟨m, hh⟩ := HProp.hexists_elim hh
    obtain ⟨h1, h2, m1, m2, hd, he⟩ := HProp.hstar_elim hh
    obtain ⟨k1, hw1, hk1⟩ := gK_elim m1
    obtain ⟨k2, hw2, hk2⟩ := gK_elim (gChain_abs c B r s' t (n - m) h2 m2)
    have hj := wseg_join c k1 k2 m (n - m) s s' t h (he ▸ HProp.hstar_intro hw1 hw2 hd)
    rw [show m + (n - m) = n by omega] at hj
    exact gK_intro (k1 + k2) hj ⟨k1, k2, rfl, hk1, hk2⟩

theorem gAny_abs {σ : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (j : Nat) (s t : σ) (n : Int) :
    gAny B j (fun b => gChain c (gA c B) b s t n) ==> gA c B j s t n := by
  intro h ⟨b, hb, hh⟩
  obtain ⟨k, hw, hk⟩ := gK_elim (gChain_abs c B b s t n h hh)
  exact gK_intro k hw (pLen_intro B j k ⟨b, hb, hk⟩)

theorem gAbs {κ ι σ J : Type} (P : κ → HProp) (G : (κ → HProp) → κ → HProp)
    (hind : ∀ M : κ → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a) (emb : κ → ι)
    (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat)))) (mem : ι → Nat) (st : ι → σ)
    (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (hstep : ∀ a, G (fun b => gQ c B mem st E N T (emb b)) a ==>
      ∃✶ j, gAny B (mem (emb a)) (fun b => gChain c (gA c B) b (st (emb a)) (E (emb a) j) (N (emb a) j)) ✶
        T (emb a) j)
    (a : κ) : P a ==> gQ c B mem st E N T (emb a) :=
  hind _ (fun b => HProp.himpl_trans (hstep b) (HProp.himpl_hexists_l (fun j =>
    HProp.himpl_hexists_r j (HProp.himpl_frame_l
      (gAny_abs c B (mem (emb b)) (st (emb b)) (E (emb b) j) (N (emb b) j)))))) a

theorem gAbsP {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (a : ι) (R : Nat → J → HProp) (hR : ∀ k j, pLen B (mem a) k → T a j ==> R k j) :
    gQ c B mem st E N T a ==> ∃✶ k, ∃✶ j, wseg c k (N a j) (st a) (E a j) ✶ R k j := by
  refine HProp.himpl_hexists_l (fun j => ?_)
  intro h hh
  obtain ⟨h1, h2, m1, m2, hd, he⟩ := HProp.hstar_elim hh
  obtain ⟨k, hw, hk⟩ := gK_elim m1
  exact HProp.hexists_intro k _ (HProp.hexists_intro j _ (he ▸ HProp.hstar_intro hw (hR k j hk h2 m2) hd))

theorem gAny_intro {B : List (List (List (Option Nat)))} {j : Nat} {f : List (Option Nat) → HProp}
    {b : List (Option Nat)} (hb : b ∈ pNthK B j []) : f b ==> gAny B j f :=
  fun _ hh => ⟨b, hb, hh⟩

theorem gChain_step {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (a a' : ι) (w : Int) (jm : J → J)
    (hr : ∀ j', E a' j' = E a (jm j') ∧ T a' j' = T a (jm j') ∧ N a (jm j') = N a' j' + w) :
    c (st a) (st a') w ✶ gQ c B mem st E N T a' ==>
      ∃✶ j, gChain c (gA c B) [none, some (mem a')] (st a) (E a j) (N a j) ✶ T a j := by
  rw [HProp.hstar_comm]
  show (∃✶ j', gA c B (mem a') (st a') (E a' j') (N a' j') ✶ T a' j') ✶ c (st a) (st a') w ==> _
  rw [HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun j' => HProp.himpl_hexists_r (jm j') ?_)
  obtain ⟨hE, hT, hN⟩ := hr j'
  rw [← hT, HProp.hstar_comm, ← HProp.hstar_assoc]
  refine HProp.himpl_frame_l ?_
  show c (st a) (st a') w ✶ gA c B (mem a') (st a') (E a' j') (N a' j') ==>
    ∃✶ s', ∃✶ w', c (st a) s' w' ✶ (∃✶ s'', ∃✶ m, gA c B (mem a') s' s'' m ✶
      ⌈s'' = E a (jm j') ∧ N a (jm j') - w' - m = 0⌉)
  refine HProp.himpl_hexists_r (st a') (HProp.himpl_hexists_r w (HProp.himpl_frame_r ?_))
  exact HProp.himpl_hexists_r (E a' j') (HProp.himpl_hexists_r (N a' j')
    (pure_r_intro ⟨hE, by omega⟩ (HProp.himpl_refl _)))

def gCons {α : Type} (x : α) (f : Nat → α) : Nat → α := fun i => Nat.casesOn (motive := fun _ => α) i x f

noncomputable def gChainC {ι σ : Type} (cv : σ → σ → Int → HProp) (P : ι → HProp)
    (arg : Nat → Bool → σ → σ → Int → ι) (b : List (Option Nat)) :
    (Nat → σ) → (Nat → Int) → HProp → σ → σ → Int → HProp :=
  List.rec (motive := fun _ => (Nat → σ) → (Nat → Int) → HProp → σ → σ → Int → HProp)
    (fun _ _ TT _ _ _ => TT)
    (fun it r ih f g TT s t n => List.rec (motive := fun _ => HProp)
      (Option.rec (motive := fun _ => HProp) (cv s t n ✶ TT) (fun j => P (arg j true s t n)) it)
      (fun _ _ _ => Option.rec (motive := fun _ => HProp)
        (cv s (f 0) (g 0) ✶ ih (fun i => f (i + 1)) (fun i => g (i + 1)) TT (f 0) t (n - g 0))
        (fun j => P (arg j false s (f 0) (g 0)) ✶
          ih (fun i => f (i + 1)) (fun i => g (i + 1)) TT (f 0) t (n - g 0)) it) r) b

def gChainI {σ : Type} (I : Nat → σ → σ → Int → Prop) (b : List (Option Nat)) :
    (Nat → σ) → (Nat → Int) → (Nat → Nat) → σ → σ → Int → Prop :=
  List.rec (motive := fun _ => (Nat → σ) → (Nat → Int) → (Nat → Nat) → σ → σ → Int → Prop)
    (fun _ _ _ s t n => s = t ∧ n = 0)
    (fun it r ih f g kf s t n => List.rec (motive := fun _ => Prop)
      (Option.rec (motive := fun _ => Prop) True (fun _ => I (kf 0) s t n) it)
      (fun _ _ _ => Option.rec (motive := fun _ => Prop)
        (ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => kf (i + 1)) (f 0) t (n - g 0))
        (fun _ => I (kf 0) s (f 0) (g 0) ∧
          ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => kf (i + 1)) (f 0) t (n - g 0)) it) r) b

def gNL (nl : Nat → Bool) (b : List (Option Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun it r ih => List.rec (motive := fun _ => Bool) true
      (fun _ _ _ => Option.rec (motive := fun _ => Bool) ih (fun j => nl j && ih) it) r) b

def gNLB (nl : Nat → Bool) (B : List (List (List (Option Nat)))) : Bool := B.all (fun bs => bs.all (gNL nl))

omit [Params] in
theorem gNLB_true (B : List (List (List (Option Nat)))) : gNLB (fun _ => true) B = true := by
  have h : ∀ b, gNL (fun _ => true) b = true := by
    intro b
    induction b with
    | nil => rfl
    | cons it r ih =>
      cases r with
      | nil => rfl
      | cons it2 r2 =>
        cases it with
        | none => exact ih
        | some j => exact (Bool.true_and _).trans ih
  simp [gNLB, h]

theorem gConc {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (arg : ι → J → Nat → Bool → σ → σ → Int → ι × J)
    (hmem : ∀ a jj j l s s' m, j < B.length → mem (arg a jj j l s s' m).1 = j)
    (I : Nat → σ → σ → Int → Prop) (hI : ∀ k n s t, holdsP (I k s t n) (wseg c k n s t))
    (nl : Nat → Bool) (hnl : gNLB nl B = true)
    (hf : ∀ a jj j s s' m k, nl j = true → I k s s' m →
      st (arg a jj j false s s' m).1 = s ∧ N (arg a jj j false s s' m).1 (arg a jj j false s s' m).2 = m ∧
      E (arg a jj j false s s' m).1 (arg a jj j false s s' m).2 = s' ∧
      T (arg a jj j false s s' m).1 (arg a jj j false s s' m).2 = emp)
    (ht : ∀ a jj j s m k, I k s (E a jj) m →
      st (arg a jj j true s (E a jj) m).1 = s ∧
      N (arg a jj j true s (E a jj) m).1 (arg a jj j true s (E a jj) m).2 = m ∧
      E (arg a jj j true s (E a jj) m).1 (arg a jj j true s (E a jj) m).2 = E a jj ∧
      T (arg a jj j true s (E a jj) m).1 (arg a jj j true s (E a jj) m).2 = T a jj)
    (cv : σ → σ → Int → HProp) (hcv : ∀ s t n, c s t n ==> cv s t n) (P : ι → HProp)
    (hbr : ∀ a jj, ∀ b ∈ pNthK B (mem a) [], ∀ f g kf, gChainI I b f g kf (st a) (E a jj) (N a jj) →
      gChainC cv P (fun j l s s' m => (arg a jj j l s s' m).1) b f g (T a jj) (st a) (E a jj) (N a jj) ==> P a)
    (k : Nat) (a : ι) (jj : J) (hk : pLen B (mem a) k) :
    wseg c k (N a jj) (st a) (E a jj) ✶ T a jj ==> P a := by
  refine (hk (fun j k => j < B.length ∧
    ∀ a jj, mem a = j → wseg c k (N a jj) (st a) (E a jj) ✶ T a jj ==> P a) ?_).2 a jj rfl
  intro i k ⟨b, hb, hl⟩
  have hi : i < B.length := by
    rw [pNthK_getD] at hb
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hb
    cases hb
  refine ⟨hi, fun a jj hma => ?_⟩
  subst hma
  let S := fun j k => j < B.length ∧
    ∀ a jj, mem a = j → wseg c k (N a jj) (st a) (E a jj) ✶ T a jj ==> P a
  have call : ∀ j k1, S j k1 → ∀ (l : Bool) (s s' : σ) (m : Int) (TT : HProp),
      st (arg a jj j l s s' m).1 = s ∧ N (arg a jj j l s s' m).1 (arg a jj j l s s' m).2 = m ∧
      E (arg a jj j l s s' m).1 (arg a jj j l s s' m).2 = s' ∧
      T (arg a jj j l s s' m).1 (arg a jj j l s s' m).2 = TT →
      wseg c k1 m s s' ✶ TT ==> P (arg a jj j l s s' m).1 := by
    intro j k1 hS l s s' m TT ⟨hs, hn, he, ht⟩
    have := hS.2 (arg a jj j l s s' m).1 (arg a jj j l s s' m).2 (hmem _ _ _ _ _ _ _ hS.1)
    rw [hn, hs, he, ht] at this
    exact this
  let ag := fun j l s s' m => (arg a jj j l s s' m).1
  have chain : ∀ (b : List (Option Nat)) (k : Nat), gNL nl b = true → pLenC S b k → ∀ (s : σ) (n : Int),
      wseg c k n s (E a jj) ✶ T a jj ==>
        ∃✶ f, ∃✶ g, ∃✶ kf, ⌈gChainI I b f g kf s (E a jj) n⌉ ✶
          gChainC cv P ag b f g (T a jj) s (E a jj) n := by
    intro b
    induction b with
    | nil =>
      intro k _ hk s n
      have hk' : k = 0 := hk
      subst hk'
      exact HProp.himpl_hexists_r (fun _ => s) (HProp.himpl_hexists_r (fun _ => 0)
        (HProp.himpl_hexists_r (fun _ => 0) (HProp.himpl_refl _)))
    | cons it r ih =>
      intro k hnb hk s n
      cases r with
      | nil =>
        cases it with
        | none =>
          obtain ⟨k', hk', hr⟩ := hk
          have hk0 : k' = 0 := hr
          subst hk' hk0
          refine HProp.himpl_hexists_r (fun _ => s) (HProp.himpl_hexists_r (fun _ => 0)
            (HProp.himpl_hexists_r (fun _ => 0) ?_))
          refine HProp.himpl_hstar_hpure_r trivial ?_
          exact HProp.himpl_frame_l (HProp.himpl_trans (wseg_uncell c s (E a jj) n) (hcv s (E a jj) n))
        | some j =>
          obtain ⟨k1, k2, hk12, hS, hr⟩ := hk
          have hk2 : k2 = 0 := hr
          subst hk12 hk2
          refine HProp.himpl_hexists_r (fun _ => s) (HProp.himpl_hexists_r (fun _ => 0)
            (HProp.himpl_hexists_r (fun _ => k1) ?_))
          refine himpl_of_holds (holdsP_star_l (hI k1 n s (E a jj))) (fun hi => ?_)
          refine HProp.himpl_hstar_hpure_r hi ?_
          exact call j k1 hS true s (E a jj) n (T a jj) (ht a jj j s n k1 hi)
      | cons it2 r2 =>
        cases it with
        | none =>
          obtain ⟨k', hk', hr⟩ := hk
          subst hk'
          show (∃✶ s', ∃✶ w, c s s' w ✶ wseg c k' (n - w) s' (E a jj)) ✶ T a jj ==> _
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun s' => ?_)
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun w => ?_)
          rw [HProp.hstar_assoc]
          refine HProp.himpl_trans (HProp.himpl_frame_lr (hcv s s' w) (ih k' hnb hr s' (n - w))) ?_
          rw [HProp.hstar_comm, HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun f => HProp.himpl_hexists_r (gCons s' f) ?_)
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun g => HProp.himpl_hexists_r (gCons w g) ?_)
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun kf => HProp.himpl_hexists_r (gCons 0 kf) ?_)
          rw [HProp.hstar_comm]
          exact perm_swap _ _ _
        | some j =>
          obtain ⟨k1, k2, hk12, hS, hr⟩ := hk
          subst hk12
          have hnb' : nl j = true ∧ gNL nl (it2 :: r2) = true := Bool.and_eq_true _ _ ▸ hnb
          refine HProp.himpl_trans (HProp.himpl_frame_l (wseg_split c k1 k2 n s (E a jj))) ?_
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun s' => ?_)
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun m => ?_)
          rw [HProp.hstar_assoc]
          refine himpl_of_holds (holdsP_star_l (hI k1 m s s')) (fun hi => ?_)
          refine HProp.himpl_trans (HProp.himpl_frame_lr (HProp.himpl_trans (star_emp_r _)
            (call j k1 hS false s s' m emp (hf a jj j s s' m k1 hnb'.1 hi)))
            (ih k2 hnb'.2 hr s' (n - m))) ?_
          rw [HProp.hstar_comm, HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun f => HProp.himpl_hexists_r (gCons s' f) ?_)
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun g => HProp.himpl_hexists_r (gCons m g) ?_)
          rw [HProp.hstar_hexists]
          refine HProp.himpl_hexists_l (fun kf => HProp.himpl_hexists_r (gCons k1 kf) ?_)
          rw [HProp.hstar_comm]
          refine HProp.himpl_trans (perm_swap _ _ _) ?_
          refine HProp.himpl_hstar_hpure_l (fun hr' => HProp.himpl_hstar_hpure_r ⟨hi, hr'⟩ ?_)
          exact HProp.himpl_refl _
  have hgb : gNL nl b = true := by
    rw [pNthK_getD, List.getD_eq_getElem?_getD] at hb
    cases hB : B[mem a]? with
    | none => rw [hB] at hb; cases hb
    | some bs =>
      rw [hB] at hb
      exact List.all_eq_true.1 (List.all_eq_true.1 hnl bs (List.mem_of_getElem? hB)) b hb
  refine HProp.himpl_trans (chain b k hgb hl (st a) (N a jj)) ?_
  refine HProp.himpl_hexists_l (fun f => HProp.himpl_hexists_l (fun g => HProp.himpl_hexists_l (fun kf => ?_)))
  exact HProp.himpl_hstar_hpure_l (fun hc => hbr a jj b hb f g kf hc)

omit [Params] in
theorem gPhiA (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m p : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, p, rs))
    (k : Nat) (hk : pLen B j k) : phiI m p rs (k : Int) := by
  rw [pChkAK_eq] at hA
  rw [pNthK_getD] at hpr
  have hs := pChkA_sound B prof hA j k hk
  simp only [pSet, hpr] at hs
  exact phiI_of_inS hs

omit [Params] in
theorem gLeA (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, 1, rs))
    (k : Nat) (hk : pLen B j k) : m ≤ k := by
  rw [pChkAK_eq] at hA
  rw [pNthK_getD] at hpr
  have hs := pChkA_sound B prof hA j k hk
  simp only [pSet, hpr, inS, pble, Bool.and_eq_true, decide_eq_true_eq] at hs
  exact hs.1

omit [Params] in
theorem gPhiC (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (rk : List Nat) (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat))))
    (hC : pChkCK B prof rk N sps cert = true) (j m p : Nat) (rs : List Nat) (hj : Nat.blt j (pLenK B) = true)
    (hpr : pNthK prof j pDflt = (m, p, rs)) (k : Nat) (hk : phiI m p rs (k : Int)) : pLen B j k := by
  rw [pChkCK_eq] at hC
  rw [pNthK_getD] at hpr
  rw [Nat.blt_eq, pLenK_eq] at hj
  have hc' := hC
  simp only [pChkC, pNth_eq, pMemB_eq, pblt, pbeq, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, h1⟩, _⟩, _⟩, _⟩, _⟩ := hc' j (List.mem_range.mpr hj)
  rw [hpr] at h1
  have hin : inS m p rs k = true := inS_of_phiI (fun hp1 => by
    subst hp1
    simpa using h1) hk
  have hin' : inSp prof j k = true := by simp only [inSp, pNth_eq, hpr]; exact hin
  exact pChkC_sound B prof rk N sps cert hC _ j k rfl hj hin'

omit [Params] in
theorem pLenC_rep (S : Nat → Nat → Prop) : ∀ (n k : Nat), pLenC S (List.replicate n none) k ↔ k = n
  | 0, k => Iff.rfl
  | n + 1, k => by
    show (∃ k', k = k' + 1 ∧ pLenC S (List.replicate n none) k') ↔ k = n + 1
    constructor
    · intro ⟨k', hk, hr⟩
      rw [(pLenC_rep S n k').1 hr] at hk
      exact hk
    · intro hk
      exact ⟨n, hk, (pLenC_rep S n n).2 rfl⟩

omit [Params] in
theorem pLen_lin (B : List (List (List (Option Nat)))) (j kmin : Nat)
    (hB : pNthK B j [] = [List.replicate kmin none, [none, some j]]) (k : Nat) :
    pLen B j k ↔ kmin ≤ k := by
  constructor
  · intro hk
    refine hk (fun i k => i = j → kmin ≤ k) ?_ rfl
    intro i k ⟨b, hb, hl⟩ hij
    subst hij
    rw [hB] at hb
    rcases List.mem_cons.1 hb with hb | hb
    · subst hb
      exact Nat.le_of_eq ((pLenC_rep _ kmin k).1 hl).symm
    · rcases List.mem_cons.1 hb with hb | hb
      · subst hb
        obtain ⟨k', hk', k1, k2, hk12, hS, hz⟩ := hl
        have hz' : k2 = 0 := hz
        have := hS rfl
        omega
      · cases hb
  · intro hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction d with
    | zero =>
      refine pLen_intro B j (kmin + 0) ⟨List.replicate kmin none, by rw [hB]; simp, ?_⟩
      exact (pLenC_rep _ kmin _).2 rfl
    | succ d ih =>
      refine pLen_intro B j (kmin + (d + 1)) ⟨[none, some j], by rw [hB]; simp, ?_⟩
      exact ⟨kmin + d, by omega, kmin + d, 0, rfl, ih (by omega), rfl⟩

noncomputable def gChainL {σ : Type} (Lc : σ → σ → HProp) (Lx : Nat → σ → σ → HProp)
    (b : List (Option Nat)) : (Nat → σ) → σ → σ → HProp :=
  List.rec (motive := fun _ => (Nat → σ) → σ → σ → HProp) (fun _ s t => ⌈s = t⌉)
    (fun it r ih f s t => List.rec (motive := fun _ => HProp)
      (Option.rec (motive := fun _ => HProp) (Lc s t) (fun j => Lx j s t) it)
      (fun _ _ _ => Option.rec (motive := fun _ => HProp) (Lc s (f 0)) (fun j => Lx j s (f 0)) it ✶
        ih (fun i => f (i + 1)) (f 0) t) r) b

theorem gChainL_abs {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (Lc : σ → σ → HProp) (arg : Nat → σ → σ → ι) (hc : ∀ s t, Lc s t ==> ∃✶ w, c s t w)
    (hmem : ∀ j s t, mem (arg j s t) = j) (hst : ∀ j s t, st (arg j s t) = s)
    (hE : ∀ j s t jj, E (arg j s t) jj = t) (hT : ∀ j s t jj, T (arg j s t) jj = emp) :
    ∀ (b : List (Option Nat)) (f : Nat → σ) (s t : σ),
      gChainL Lc (fun j s t => gQ c B mem st E N T (arg j s t)) b f s t ==> ∃✶ n, gChain c (gA c B) b s t n := by
  have one : ∀ (it : Option Nat) (s s' t : σ) (r : List (Option Nat)) (R : HProp),
      (R ==> ∃✶ n, gChain c (gA c B) r s' t n) →
      Option.rec (motive := fun _ => HProp) (Lc s s') (fun j => gQ c B mem st E N T (arg j s s')) it ✶ R ==>
        ∃✶ n, gChain c (gA c B) (it :: r) s t n := by
    intro it s s' t r R hR
    refine HProp.himpl_trans (HProp.himpl_frame_r hR) ?_
    rw [HProp.hstar_comm, HProp.hstar_hexists]
    refine HProp.himpl_hexists_l (fun n => ?_)
    cases it with
    | none =>
      show gChain c (gA c B) r s' t n ✶ Lc s s' ==> _
      refine HProp.himpl_trans (HProp.himpl_frame_r (hc s s')) ?_
      rw [HProp.hstar_comm, HProp.hstar_hexists]
      refine HProp.himpl_hexists_l (fun w => HProp.himpl_hexists_r (w + n) ?_)
      show c s s' w ✶ gChain c (gA c B) r s' t n ==>
        ∃✶ s'', ∃✶ w', c s s'' w' ✶ gChain c (gA c B) r s'' t (w + n - w')
      refine HProp.himpl_hexists_r s' (HProp.himpl_hexists_r w ?_)
      rw [show w + n - w = n by omega]
      exact HProp.himpl_refl _
    | some j =>
      show gChain c (gA c B) r s' t n ✶ gQ c B mem st E N T (arg j s s') ==> _
      rw [HProp.hstar_comm]
      show (∃✶ jj, gA c B (mem (arg j s s')) (st (arg j s s')) (E (arg j s s') jj) (N (arg j s s') jj) ✶
        T (arg j s s') jj) ✶ _ ==> _
      rw [HProp.hstar_hexists]
      refine HProp.himpl_hexists_l (fun jj => HProp.himpl_hexists_r (N (arg j s s') jj + n) ?_)
      rw [hT, hE, hmem, hst, HProp.hstar_hempty_r]
      show gA c B j s s' (N (arg j s s') jj) ✶ gChain c (gA c B) r s' t n ==>
        ∃✶ s'', ∃✶ m, gA c B j s s'' m ✶ gChain c (gA c B) r s'' t (N (arg j s s') jj + n - m)
      refine HProp.himpl_hexists_r s' (HProp.himpl_hexists_r (N (arg j s s') jj) ?_)
      rw [show N (arg j s s') jj + n - N (arg j s s') jj = n by omega]
      exact HProp.himpl_refl _
  intro b
  induction b with
  | nil =>
    intro f s t h hh
    obtain ⟨hst, he⟩ := HProp.hpure_elim_hempty hh
    exact HProp.hexists_intro 0 _ (HProp.hpure_intro_hempty he ⟨hst, rfl⟩)
  | cons it r ih =>
    intro f s t
    cases r with
    | nil =>
      refine HProp.himpl_trans (star_emp_r _) (one it s t t [] emp ?_)
      exact HProp.himpl_hexists_r 0 (HProp.himpl_hempty_hpure ⟨rfl, rfl⟩)
    | cons it2 r2 =>
      exact one it s (f 0) t (it2 :: r2) _ (ih (fun i => f (i + 1)) (f 0) t)

theorem gAnyL {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (Lc : σ → σ → HProp) (arg : Nat → σ → σ → ι) (hc : ∀ s t, Lc s t ==> ∃✶ w, c s t w)
    (hmem : ∀ j s t, mem (arg j s t) = j) (hst : ∀ j s t, st (arg j s t) = s)
    (hE : ∀ j s t jj, E (arg j s t) jj = t) (hT : ∀ j s t jj, T (arg j s t) jj = emp)
    {j : Nat} {b : List (Option Nat)} (hb : b ∈ pNthK B j []) (f : Nat → σ) (s t : σ) :
    gChainL Lc (fun j s t => gQ c B mem st E N T (arg j s t)) b f s t ==>
      ∃✶ n, gAny B j (fun b => gChain c (gA c B) b s t n) ✶ emp :=
  HProp.himpl_trans (gChainL_abs c B mem st E N T Lc arg hc hmem hst hE hT b f s t)
    (HProp.himpl_hexists_l (fun n => HProp.himpl_hexists_r n
      (HProp.himpl_trans (gAny_intro (f := fun b => gChain c (gA c B) b s t n) hb) (star_emp_r _))))

omit [Params] in
theorem gAllIdx (B : List (List (List (Option Nat)))) (Q : Nat → List (Option Nat) → Prop)
    (H : pAllIdx (fun j => ∀ b ∈ pNthK B j [], Q j b) 0 (pLenK B)) :
    ∀ j, ∀ b ∈ pNthK B j [], Q j b := by
  intro j b hb
  have hj : j < B.length := by
    rw [pNthK_getD] at hb
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hb
    cases hb
  exact pAllIdx_lt _ 0 (pLenK B) H j (Nat.zero_le _) (by rw [pLenK_eq]; omega) b hb

theorem pCell_intro (C : Nat → Nat → HProp) (s t : Nat) : C s t ==> ∃✶ w, pCell C s t w :=
  HProp.himpl_hexists_r 1 (HProp.himpl_hexists_r t (HProp.himpl_trans (star_emp_r _)
    (HProp.himpl_frame_r (HProp.himpl_hempty_hpure ⟨rfl, rfl⟩))))

theorem pCell_view (C : Nat → Nat → HProp) (s t : Nat) (n : Int) : pCell C s t n ==> C s t :=
  HProp.himpl_hexists_l (fun _ => pure_r_elim (fun ⟨h1, _⟩ => h1 ▸ HProp.himpl_refl _))

theorem gChainC_L (C : Nat → Nat → HProp) (Lx : Nat → Nat → Nat → HProp) :
    ∀ (b : List (Option Nat)) (f : Nat → Nat) (g : Nat → Int) (kf : Nat → Nat) (x y : Nat) (n : Int),
      gChainI (fun _ _ _ _ => True) b f g kf x y n →
      gChainC (fun s t _ => C s t) (fun a : Nat × Nat × Nat => Lx a.1 a.2.1 a.2.2)
        (fun j _ s s' _ => (j, s, s')) b f g emp x y n ==> gChainL C Lx b f x y := by
  intro b
  induction b with
  | nil =>
    intro f g kf x y n hi
    exact HProp.himpl_hempty_hpure hi.1
  | cons it r ih =>
    intro f g kf x y n hi
    cases r with
    | nil =>
      cases it with
      | none => exact star_emp_elim _
      | some j => exact HProp.himpl_refl _
    | cons it2 r2 =>
      cases it with
      | none => exact HProp.himpl_frame_r (ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => kf (i + 1)) _ _ _ hi)
      | some j => exact HProp.himpl_frame_r (ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => kf (i + 1)) _ _ _ hi.2)

theorem gConcPG (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (Lx : Nat → Nat → Nat → HProp)
    (H : pAllIdx (fun j => ∀ b ∈ pNthK B j [], ∀ (f : Nat → Nat) (x y : Nat),
      gChainL C Lx b f x y ==> Lx j x y) 0 (pLenK B))
    (k j x y : Nat) (n : Int) (hk : pLen B j k) : wseg (pCell C) k n x y ==> Lx j x y := by
  refine HProp.himpl_trans (star_emp_r _) ?_
  refine gConc (pCell C) B (fun a : Nat × Nat × Nat => a.1) (fun a => a.2.1) (fun a (_ : Int) => a.2.2)
    (fun _ j => j) (fun _ _ => emp) (fun _ _ j _ s s' m => ((j, s, s'), m)) (fun _ _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ => True) (fun _ _ _ _ => holdsP_true) (fun _ => true) (gNLB_true B)
    (fun _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩) (fun _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩)
    (fun s t _ => C s t) (pCell_view C) (fun a => Lx a.1 a.2.1 a.2.2) ?_ k (j, x, y) n hk
  intro a jj b hb f g kf hi
  exact HProp.himpl_trans (gChainC_L C Lx b f g kf _ _ _ hi)
    (gAllIdx B (fun j b => ∀ (f : Nat → Nat) (x y : Nat), gChainL C Lx b f x y ==> Lx j x y) H a.1 b hb f a.2.1 a.2.2)

def gQP (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (a : Nat × Nat × Nat) : HProp :=
  gQ (pCell C) B (fun a : Nat × Nat × Nat => a.1) (fun a => a.2.1) (fun a (_ : Int) => a.2.2) (fun _ j => j)
    (fun _ _ => emp) a

def gAnyP (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (a : Nat × Nat × Nat) : HProp :=
  ∃✶ n, gAny B a.1 (fun b => gChain (pCell C) (gA (pCell C) B) b a.2.1 a.2.2 n) ✶ emp

theorem gAnyPG (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) {j : Nat} {b : List (Option Nat)}
    (hb : b ∈ pNthK B j []) (f : Nat → Nat) (x y : Nat) :
    gChainL C (fun j s t => gQP C B (j, s, t)) b f x y ==> gAnyP C B (j, x, y) :=
  gAnyL (pCell C) B (fun a : Nat × Nat × Nat => a.1) (fun a => a.2.1) (fun a (_ : Int) => a.2.2) (fun _ j => j)
    (fun _ _ => emp) C (fun j s t => (j, s, t)) (pCell_intro C) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hb f x y

theorem gAbsPG {κ : Type} (P : κ → HProp) (G : (κ → HProp) → κ → HProp)
    (hind : ∀ M : κ → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a) (emb : κ → Nat × Nat × Nat)
    (C : Nat → Nat → HProp) (B : List (List (List (Option Nat))))
    (hstep : ∀ a, G (fun b => gQP C B (emb b)) a ==> gAnyP C B (emb a))
    (a : κ) : P a ==> gQP C B (emb a) :=
  gAbs P G hind emb (pCell C) B (fun a : Nat × Nat × Nat => a.1) (fun a => a.2.1) (fun a (_ : Int) => a.2.2)
    (fun _ j => j) (fun _ _ => emp) hstep a

theorem gAbsPGPhi (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m p : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, p, rs)) (x y : Nat) :
    gQP C B (j, x, y) ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈phiI m p rs (k : Int)⌉ :=
  gAbsP (pCell C) B (fun a : Nat × Nat × Nat => a.1) (fun a => a.2.1) (fun a (_ : Int) => a.2.2) (fun _ j => j)
    (fun _ _ => emp) (j, x, y) (fun k _ => ⌈phiI m p rs (k : Int)⌉)
    (fun k _ hk => HProp.himpl_hempty_hpure (gPhiA B prof hA j m p rs hpr k hk))

theorem gAbsPGLe (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, 1, rs)) (x y : Nat) :
    gQP C B (j, x, y) ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈m ≤ k⌉ :=
  gAbsP (pCell C) B (fun a : Nat × Nat × Nat => a.1) (fun a => a.2.1) (fun a (_ : Int) => a.2.2) (fun _ j => j)
    (fun _ _ => emp) (j, x, y) (fun k _ => ⌈m ≤ k⌉)
    (fun k _ hk => HProp.himpl_hempty_hpure (gLeA B prof hA j m rs hpr k hk))

theorem holdsP_and {P Q : Prop} {H : HProp} (h1 : holdsP P H) (h2 : holdsP Q H) : holdsP (P ∧ Q) H :=
  fun h hh => ⟨h1 h hh, h2 h hh⟩

theorem wseg_cst {σ K : Type} (c : σ → σ → Int → HProp) (p : σ → K)
    (hc : ∀ s s' w, holdsP (p s' = p s) (c s s' w)) (k : Nat) (n : Int) (s t : σ) :
    holdsP (p t = p s) (wseg c k n s t) :=
  wseg_inv c (fun s s' _ => p s' = p s) (fun _ s t _ => p t = p s) (fun s s' w h hh => hc s s' w h hh)
    (fun _ => rfl) (fun _ _ _ _ _ _ h1 h2 => h2.trans h1) k n s t

def gLin (kmin : Nat) : List (List (List (Option Nat))) := [[List.replicate kmin none, [none, some 0]]]

theorem wseg_one {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (n : Int) : c s t n ==> wseg c 1 n s t :=
  HProp.himpl_hexists_r t (HProp.himpl_hexists_r n (HProp.himpl_trans (star_emp_r _)
    (HProp.himpl_frame_r (HProp.himpl_hempty_hpure ⟨rfl, by omega⟩))))

theorem gChainC_rep {ι σ : Type} (c : σ → σ → Int → HProp) (P : ι → HProp)
    (arg : Nat → Bool → σ → σ → Int → ι) (I : Nat → σ → σ → Int → Prop) :
    ∀ (kmin : Nat) (f : Nat → σ) (g : Nat → Int) (kf : Nat → Nat) (TT : HProp) (s t : σ) (n : Int),
      gChainI I (List.replicate kmin none) f g kf s t n →
      gChainC c P arg (List.replicate kmin none) f g TT s t n ==> wseg c kmin n s t ✶ TT := by
  intro kmin
  induction kmin with
  | zero =>
    intro f g kf TT s t n hi
    exact HProp.himpl_hstar_hpure_r hi (HProp.himpl_refl _)
  | succ k ih =>
    intro f g kf TT s t n hi
    cases k with
    | zero => exact HProp.himpl_frame_l (wseg_one c s t n)
    | succ k =>
      refine HProp.himpl_trans (HProp.himpl_frame_r (ih (fun i => f (i + 1)) (fun i => g (i + 1))
        (fun i => kf (i + 1)) TT (f 0) t (n - g 0) hi)) ?_
      rw [← HProp.hstar_assoc]
      refine HProp.himpl_frame_l ?_
      exact HProp.himpl_hexists_r (f 0) (HProp.himpl_hexists_r (g 0) (HProp.himpl_refl _))

noncomputable def gBase {σ : Type} (c : σ → σ → Int → HProp) (k : Nat) : σ → σ → Int → HProp :=
  Nat.rec (motive := fun _ => σ → σ → Int → HProp) (fun s t n => ⌈s = t ∧ n = 0⌉)
    (fun k ih s t n => Nat.rec (motive := fun _ => HProp) (c s t n)
      (fun _ _ => ∃✶ s', ∃✶ w, c s s' w ✶ ih s' t (n - w)) k) k

theorem gBase_chain {σ : Type} (c : σ → σ → Int → HProp) (X : Nat → σ → σ → Int → HProp) :
    ∀ (k : Nat) (s t : σ) (n : Int), gBase c k s t n ==> gChain c X (List.replicate k none) s t n := by
  intro k
  induction k with
  | zero => intro s t n; exact HProp.himpl_refl _
  | succ k ih =>
    intro s t n
    cases k with
    | zero =>
      show c s t n ==> ∃✶ s', ∃✶ w, c s s' w ✶ ⌈s' = t ∧ n - w = 0⌉
      exact HProp.himpl_hexists_r t (HProp.himpl_hexists_r n (HProp.himpl_trans (star_emp_r _)
        (HProp.himpl_frame_r (HProp.himpl_hempty_hpure ⟨rfl, by omega⟩))))
    | succ k =>
      show (∃✶ s', ∃✶ w, c s s' w ✶ gBase c (k + 1) s' t (n - w)) ==>
        ∃✶ s', ∃✶ w, c s s' w ✶ gChain c X (List.replicate (k + 1) none) s' t (n - w)
      exact HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_r s' (HProp.himpl_hexists_l (fun w =>
        HProp.himpl_hexists_r w (HProp.himpl_frame_r (ih s' t (n - w))))))

theorem gAbsG {α σ J : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → J → σ) (N : α → J → Int)
    (T : α → J → HProp) (rel : α → α → Int → Prop) (jm : α → α → Int → J → J)
    (hrel : ∀ a a' w, rel a a' w → ∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
      N a (jm a a' w j') = N a' j' + w) (L : α → HProp)
    (hL : ∀ a, L a ==> gQ c (gLin kmin) (fun _ => 0) st E N T a)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (∃✶ j, gBase c kmin (st a) (E a j) (N a j) ✶ T a j)
        (∃✶ a', ∃✶ w, ⌈rel a a' w⌉ ✶ (c (st a) (st a') w ✶ L a')))
    (a : α) : P a ==> gQ c (gLin kmin) (fun _ => 0) st E N T a := by
  have hb0 : List.replicate kmin none ∈ pNthK (gLin kmin) 0 [] := List.mem_cons_self
  have hb1 : [none, some 0] ∈ pNthK (gLin kmin) 0 [] := List.mem_cons_of_mem _ List.mem_cons_self
  refine gAbs P G hind (fun a => a) c (gLin kmin) (fun _ => 0) st E N T (fun b => ?_) a
  refine HProp.himpl_trans (hstep b) (wor_elim ?_ ?_)
  · refine HProp.himpl_hexists_l (fun j => HProp.himpl_hexists_r j (HProp.himpl_frame_l ?_))
    exact HProp.himpl_trans (gBase_chain c (gA c (gLin kmin)) kmin _ _ _)
      (gAny_intro (f := fun b' => gChain c (gA c (gLin kmin)) b' (st b) (E b j) (N b j)) hb0)
  · refine HProp.himpl_hexists_l (fun a' => HProp.himpl_hexists_l (fun w => HProp.himpl_hstar_hpure_l (fun hr => ?_)))
    refine HProp.himpl_trans (HProp.himpl_frame_r (hL a')) ?_
    refine HProp.himpl_trans (gChain_step c (gLin kmin) (fun _ => 0) st E N T b a' w (jm b a' w) (hrel b a' w hr)) ?_
    refine HProp.himpl_hexists_l (fun j => HProp.himpl_hexists_r j (HProp.himpl_frame_l ?_))
    exact gAny_intro (f := fun b' => gChain c (gA c (gLin kmin)) b' (st b) (E b j) (N b j)) hb1

theorem gAbsGP {α σ J : Type} (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → J → σ)
    (N : α → J → Int) (T : α → J → HProp) (a : α) (R : Nat → J → HProp)
    (hR : ∀ k j, kmin ≤ k → T a j ==> R k j) :
    gQ c (gLin kmin) (fun _ => 0) st E N T a ==> ∃✶ k, ∃✶ j, wseg c k (N a j) (st a) (E a j) ✶ R k j :=
  gAbsP c (gLin kmin) (fun _ => 0) st E N T a R
    (fun k j hk => hR k j ((pLen_lin (gLin kmin) 0 kmin rfl k).1 hk))

theorem gAbsGT {α σ J : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → J → σ) (N : α → J → Int)
    (T : α → J → HProp) (jm : α → α → Int → J → J)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (∃✶ j, gBase c kmin (st a) (E a j) (N a j) ✶ T a j)
        (∃✶ a', ∃✶ w, ⌈∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
          N a (jm a a' w j') = N a' j' + w⌉ ✶ (c (st a) (st a') w ✶ gQ c (gLin kmin) (fun _ => 0) st E N T a')))
    (a : α) (R : Nat → J → HProp) (hR : ∀ k j, kmin ≤ k → T a j ==> R k j) :
    P a ==> ∃✶ k, ∃✶ j, wseg c k (N a j) (st a) (E a j) ✶ R k j :=
  HProp.himpl_trans (gAbsG P G hind c kmin st E N T _ jm (fun _ _ _ h => h) _ (fun _ => HProp.himpl_refl _) hstep a)
    (gAbsGP c kmin st E N T a R hR)

theorem gAbsGTW {α σ J : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → J → σ) (N : α → J → Int)
    (T : α → J → HProp) (jm : α → α → Int → J → J)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (∃✶ j, gBase c kmin (st a) (E a j) (N a j) ✶ T a j)
        (∃✶ a', ∃✶ w, ⌈∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
          N a (jm a a' w j') = N a' j' + w⌉ ✶
            (c (st a) (st a') w ✶ hwith (P a') (gQ c (gLin kmin) (fun _ => 0) st E N T a'))))
    (a : α) (R : Nat → J → HProp) (hR : ∀ k j, kmin ≤ k → T a j ==> R k j) :
    P a ==> ∃✶ k, ∃✶ j, wseg c k (N a j) (st a) (E a j) ✶ R k j :=
  HProp.himpl_trans (gAbsG P G hind c kmin st E N T _ jm (fun _ _ _ h => h) _ (fun _ => hwith_r _ _) hstep a)
    (gAbsGP c kmin st E N T a R hR)

theorem gAbsGTU {α σ : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → Unit → σ) (N : α → Unit → Int)
    (T : α → Unit → HProp) (jm : α → α → Int → Unit → Unit)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (∃✶ j, gBase c kmin (st a) (E a j) (N a j) ✶ T a j)
        (∃✶ a', ∃✶ w, ⌈∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
          N a (jm a a' w j') = N a' j' + w⌉ ✶ (c (st a) (st a') w ✶ gQ c (gLin kmin) (fun _ => 0) st E N T a')))
    (a : α) (R : Nat → HProp) (hR : ∀ k, kmin ≤ k → T a () ==> R k) :
    P a ==> ∃✶ k, wseg c k (N a ()) (st a) (E a ()) ✶ R k :=
  HProp.himpl_trans (HProp.himpl_trans (gAbsG P G hind c kmin st E N T _ jm (fun _ _ _ h => h) _ (fun _ => HProp.himpl_refl _) hstep a)
    (gAbsGP c kmin st E N T a (fun k _ => R k) (fun k _ hk => hR k hk)))
    (HProp.himpl_hexists_l (fun k => HProp.himpl_hexists_r k (HProp.himpl_hexists_l (fun _ => HProp.himpl_refl _))))

theorem gAbsGTWU {α σ : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → Unit → σ) (N : α → Unit → Int)
    (T : α → Unit → HProp) (jm : α → α → Int → Unit → Unit)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (∃✶ j, gBase c kmin (st a) (E a j) (N a j) ✶ T a j)
        (∃✶ a', ∃✶ w, ⌈∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
          N a (jm a a' w j') = N a' j' + w⌉ ✶
            (c (st a) (st a') w ✶ hwith (P a') (gQ c (gLin kmin) (fun _ => 0) st E N T a'))))
    (a : α) (R : Nat → HProp) (hR : ∀ k, kmin ≤ k → T a () ==> R k) :
    P a ==> ∃✶ k, wseg c k (N a ()) (st a) (E a ()) ✶ R k :=
  HProp.himpl_trans (HProp.himpl_trans (gAbsG P G hind c kmin st E N T _ jm (fun _ _ _ h => h) _ (fun _ => hwith_r _ _) hstep a)
    (gAbsGP c kmin st E N T a (fun k _ => R k) (fun k _ hk => hR k hk)))
    (HProp.himpl_hexists_l (fun k => HProp.himpl_hexists_r k (HProp.himpl_hexists_l (fun _ => HProp.himpl_refl _))))

omit [Params] in
theorem gNLB_lin (kmin : Nat) : gNLB (fun _ => false) (gLin kmin) = true := by
  have h : ∀ k, gNL (fun _ => false) (List.replicate k none) = true := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      cases k with
      | zero => rfl
      | succ k => exact ih
  simp [gNLB, gLin, h]
  rfl

theorem gConcG {α σ J : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ)
    (E : α → J → σ) (N : α → J → Int) (T : α → J → HProp) (cal : α → J → σ → Int → α × J)
    (I : Nat → σ → σ → Int → Prop) (hI : ∀ k n s t, holdsP (I k s t n) (wseg c k n s t))
    (ht : ∀ a jj s m k, I k s (E a jj) m → st (cal a jj s m).1 = s ∧ N (cal a jj s m).1 (cal a jj s m).2 = m ∧
      E (cal a jj s m).1 (cal a jj s m).2 = E a jj ∧ T (cal a jj s m).1 (cal a jj s m).2 = T a jj)
    (hb : ∀ a jj, wseg c kmin (N a jj) (st a) (E a jj) ✶ T a jj ==> P a)
    (h1 : ∀ a jj s' w k, I k s' (E a jj) (N a jj - w) → c (st a) s' w ✶ P (cal a jj s' (N a jj - w)).1 ==> P a)
    (k : Nat) (a : α) (jj : J) (hk : kmin ≤ k) : wseg c k (N a jj) (st a) (E a jj) ✶ T a jj ==> P a :=
  gConc c (gLin kmin) (fun _ => 0) st E N T (fun a jj _ _ s _ m => cal a jj s m)
    (fun _ _ _ _ _ _ _ hj => (Nat.lt_one_iff.1 hj).symm) I hI (fun _ => false) (gNLB_lin kmin)
    (fun _ _ _ _ _ _ _ h => absurd h Bool.false_ne_true) (fun a jj _ s m k hi => ht a jj s m k hi)
    c (fun _ _ _ => HProp.himpl_refl _) P
    (fun a jj b hb' f g kf hi => by
      change b ∈ [List.replicate kmin none, [none, some 0]] at hb'
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact HProp.himpl_trans (gChainC_rep c P _ I kmin f g kf (T a jj) _ _ _ hi) (hb a jj)
      · rcases List.mem_cons.1 hb' with rfl | hb'
        · exact h1 a jj (f 0) (g 0) (kf (0 + 1)) hi
        · cases hb')
    k a jj ((pLen_lin (gLin kmin) 0 kmin rfl k).2 hk)

end Sep.Xsearch
