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

theorem wseg_succ_elim {σ : Type} (c : σ → σ → Int → HProp) (k : Nat) (n : Int) (s t : σ) :
    wseg c (k + 1) n s t ==> ∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n - w) s' t := HProp.himpl_refl _

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

end Sep
