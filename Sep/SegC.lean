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

theorem pure_r_elim {P : Prop} {H1 H2 : HProp} (h : P → H1 ==> H2) : H1 ✶ ⌈P⌉ ==> H2 := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_hstar_hpure_l h

theorem wseg_step_cnt {σ : Type} (c : σ → σ → Int → HProp) (kmin : Nat) (hk : kmin ≤ 1)
    (s s' t t' : σ) (n n' w : Int) (he : t' = t) (hn : n = n' + w) :
    c s s' w ✶ (∃✶ k, wseg c k n' s' t' ✶ ⌈kmin ≤ k⌉) ==> ∃✶ k, wseg c k n s t ✶ ⌈kmin ≤ k⌉ := by
  rw [HProp.hstar_comm, HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun k => ?_)
  rw [HProp.hstar_comm, ← HProp.hstar_assoc]
  refine pure_r_elim (fun _ => ?_)
  refine HProp.himpl_hexists_r (k + 1) (pure_r_intro (by omega) ?_)
  show c s s' w ✶ wseg c k n' s' t' ==> ∃✶ s'', ∃✶ w', c s s'' w' ✶ wseg c k (n - w') s'' t
  refine HProp.himpl_hexists_r s' (HProp.himpl_hexists_r w ?_)
  rw [show n - w = n' by omega, ← he]
  exact HProp.himpl_refl _

theorem wseg_step_free {σ : Type} (c : σ → σ → Int → HProp) (kmin : Nat) (hk : kmin ≤ 1)
    (s s' t t' : σ) (w : Int) (he : t' = t) :
    c s s' w ✶ (∃✶ k, ∃✶ n, wseg c k n s' t' ✶ ⌈kmin ≤ k⌉) ==>
      ∃✶ k, ∃✶ n, wseg c k n s t ✶ ⌈kmin ≤ k⌉ := by
  rw [HProp.hstar_comm, HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun k => ?_)
  rw [HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun n => ?_)
  rw [HProp.hstar_comm, ← HProp.hstar_assoc]
  refine pure_r_elim (fun _ => ?_)
  refine HProp.himpl_hexists_r (k + 1) (HProp.himpl_hexists_r (n + w) (pure_r_intro (by omega) ?_))
  show c s s' w ✶ wseg c k n s' t' ==> ∃✶ s'', ∃✶ w', c s s'' w' ✶ wseg c k (n + w - w') s'' t
  refine HProp.himpl_hexists_r s' (HProp.himpl_hexists_r w ?_)
  rw [show n + w - w = n by omega, ← he]
  exact HProp.himpl_refl _

theorem wseg_abs_cnt {α σ : Type} (P : α → HProp) (F : (α → HProp) → α → HProp)
    (hind : ∀ X : α → HProp, (∀ b, F X b ==> X b) → ∀ a, P a ==> X a)
    (c : σ → σ → Int → HProp) (st en : α → σ) (nE : α → Int) (B : α → HProp) (kmin : Nat)
    (hk : kmin ≤ 1)
    (hstep : ∀ X a, F X a ==> wor (B a)
      (∃✶ a', ∃✶ w, ⌈en a' = en a ∧ nE a = nE a' + w⌉ ✶ c (st a) (st a') w ✶ X a'))
    (hbase : ∀ a, B a ==> ∃✶ k, wseg c k (nE a) (st a) (en a) ✶ ⌈kmin ≤ k⌉) (a : α) :
    P a ==> ∃✶ k, wseg c k (nE a) (st a) (en a) ✶ ⌈kmin ≤ k⌉ := by
  refine hind (fun a => ∃✶ k, wseg c k (nE a) (st a) (en a) ✶ ⌈kmin ≤ k⌉) (fun b => ?_) a
  refine HProp.himpl_trans (hstep _ b) (wor_elim (hbase b) ?_)
  refine HProp.himpl_hexists_l (fun a' => HProp.himpl_hexists_l (fun w => ?_))
  refine HProp.himpl_hstar_hpure_l (fun ⟨he, hn⟩ => ?_)
  exact wseg_step_cnt c kmin hk _ _ _ _ _ _ _ he hn

theorem wseg_abs_free {α σ : Type} (P : α → HProp) (F : (α → HProp) → α → HProp)
    (hind : ∀ X : α → HProp, (∀ b, F X b ==> X b) → ∀ a, P a ==> X a)
    (c : σ → σ → Int → HProp) (st en : α → σ) (B : α → HProp) (kmin : Nat) (hk : kmin ≤ 1)
    (hstep : ∀ X a, F X a ==> wor (B a)
      (∃✶ a', ∃✶ w, ⌈en a' = en a⌉ ✶ c (st a) (st a') w ✶ X a'))
    (hbase : ∀ a, B a ==> ∃✶ k, ∃✶ n, wseg c k n (st a) (en a) ✶ ⌈kmin ≤ k⌉) (a : α) :
    P a ==> ∃✶ k, ∃✶ n, wseg c k n (st a) (en a) ✶ ⌈kmin ≤ k⌉ := by
  refine hind (fun a => ∃✶ k, ∃✶ n, wseg c k n (st a) (en a) ✶ ⌈kmin ≤ k⌉) (fun b => ?_) a
  refine HProp.himpl_trans (hstep _ b) (wor_elim (hbase b) ?_)
  refine HProp.himpl_hexists_l (fun a' => HProp.himpl_hexists_l (fun w => ?_))
  refine HProp.himpl_hstar_hpure_l (fun he => ?_)
  exact wseg_step_free c kmin hk _ _ _ _ _ he

theorem wseg_base0_cnt {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (n : Int) :
    ⌈s = t ∧ n = 0⌉ ==> ∃✶ k, wseg c k n s t ✶ ⌈0 ≤ k⌉ :=
  HProp.himpl_hexists_r 0 (pure_r_intro (Nat.le_refl 0) (HProp.himpl_refl _))

theorem wseg_base0_free {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) :
    ⌈s = t⌉ ==> ∃✶ k, ∃✶ n, wseg c k n s t ✶ ⌈0 ≤ k⌉ := by
  refine HProp.himpl_hexists_r 0 (HProp.himpl_hexists_r 0 (pure_r_intro (Nat.le_refl 0) ?_))
  intro h hh
  obtain ⟨hp, he⟩ := HProp.hpure_elim_hempty hh
  exact HProp.hpure_intro_hempty he ⟨hp, rfl⟩

theorem wseg_base1_cnt {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (n : Int) :
    (∃✶ w, ⌈n = w⌉ ✶ c s t w) ==> ∃✶ k, wseg c k n s t ✶ ⌈1 ≤ k⌉ := by
  refine HProp.himpl_hexists_l (fun w => ?_)
  refine HProp.himpl_hstar_hpure_l (fun hn => ?_)
  refine HProp.himpl_hexists_r 1 (pure_r_intro (Nat.le_refl 1) ?_)
  rw [hn]
  exact wseg_cell c s t w

theorem wseg_base1_free {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) :
    (∃✶ w, c s t w) ==> ∃✶ k, ∃✶ n, wseg c k n s t ✶ ⌈1 ≤ k⌉ := by
  refine HProp.himpl_hexists_l (fun w => ?_)
  refine HProp.himpl_hexists_r 1 (HProp.himpl_hexists_r w (pure_r_intro (Nat.le_refl 1) ?_))
  exact wseg_cell c s t w

theorem wseg_abs_cnt_m {α σ M : Type} (P : α → HProp) (F : (α → HProp) → α → HProp)
    (hind : ∀ X : α → HProp, (∀ b, F X b ==> X b) → ∀ a, P a ==> X a)
    (c : σ → σ → Int → HProp) (st : α → σ) (en : α → M → σ) (nE : α → Int) (B : α → HProp)
    (kmin : Nat) (hk : kmin ≤ 1)
    (hstep : ∀ X a, F X a ==> wor (B a)
      (∃✶ a', ∃✶ w, ⌈(∀ m, en a' m = en a m) ∧ nE a = nE a' + w⌉ ✶ c (st a) (st a') w ✶ X a'))
    (hbase : ∀ a, B a ==> ∃✶ k, ∃✶ m, wseg c k (nE a) (st a) (en a m) ✶ ⌈kmin ≤ k⌉) (a : α) :
    P a ==> ∃✶ k, ∃✶ m, wseg c k (nE a) (st a) (en a m) ✶ ⌈kmin ≤ k⌉ := by
  refine hind (fun a => ∃✶ k, ∃✶ m, wseg c k (nE a) (st a) (en a m) ✶ ⌈kmin ≤ k⌉) (fun b => ?_) a
  refine HProp.himpl_trans (hstep _ b) (wor_elim (hbase b) ?_)
  refine HProp.himpl_hexists_l (fun a' => HProp.himpl_hexists_l (fun w => ?_))
  refine HProp.himpl_hstar_hpure_l (fun ⟨he, hn⟩ => ?_)
  rw [HProp.hstar_comm, HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun k => ?_)
  rw [HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun m => ?_)
  rw [HProp.hstar_comm]
  have h := wseg_step_cnt c kmin hk (st b) (st a') (en b m) (en a' m) (nE b) (nE a') w (he m) hn
  refine HProp.himpl_trans (HProp.himpl_frame_r (HProp.himpl_hexists_r k (HProp.himpl_refl _)))
    (HProp.himpl_trans h ?_)
  exact HProp.himpl_hexists_l (fun k' => HProp.himpl_hexists_r k' (HProp.himpl_hexists_r m
    (HProp.himpl_refl _)))

theorem wseg_abs_free_m {α σ M : Type} (P : α → HProp) (F : (α → HProp) → α → HProp)
    (hind : ∀ X : α → HProp, (∀ b, F X b ==> X b) → ∀ a, P a ==> X a)
    (c : σ → σ → Int → HProp) (st : α → σ) (en : α → M → σ) (B : α → HProp) (kmin : Nat)
    (hk : kmin ≤ 1)
    (hstep : ∀ X a, F X a ==> wor (B a)
      (∃✶ a', ∃✶ w, ⌈∀ m, en a' m = en a m⌉ ✶ c (st a) (st a') w ✶ X a'))
    (hbase : ∀ a, B a ==> ∃✶ k, ∃✶ n, ∃✶ m, wseg c k n (st a) (en a m) ✶ ⌈kmin ≤ k⌉) (a : α) :
    P a ==> ∃✶ k, ∃✶ n, ∃✶ m, wseg c k n (st a) (en a m) ✶ ⌈kmin ≤ k⌉ := by
  refine hind (fun a => ∃✶ k, ∃✶ n, ∃✶ m, wseg c k n (st a) (en a m) ✶ ⌈kmin ≤ k⌉) (fun b => ?_) a
  refine HProp.himpl_trans (hstep _ b) (wor_elim (hbase b) ?_)
  refine HProp.himpl_hexists_l (fun a' => HProp.himpl_hexists_l (fun w => ?_))
  refine HProp.himpl_hstar_hpure_l (fun he => ?_)
  rw [HProp.hstar_comm, HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun k => ?_)
  rw [HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun n => ?_)
  rw [HProp.hstar_hexists]
  refine HProp.himpl_hexists_l (fun m => ?_)
  rw [HProp.hstar_comm]
  have h := wseg_step_cnt c kmin hk (st b) (st a') (en b m) (en a' m) (n + w) n w (he m) rfl
  refine HProp.himpl_trans (HProp.himpl_frame_r (HProp.himpl_hexists_r k (HProp.himpl_refl _)))
    (HProp.himpl_trans h ?_)
  exact HProp.himpl_hexists_l (fun k' => HProp.himpl_hexists_r k' (HProp.himpl_hexists_r (n + w)
    (HProp.himpl_hexists_r m (HProp.himpl_refl _))))

theorem wseg_base0_cnt_m {σ M : Type} (c : σ → σ → Int → HProp) (s : σ) (t : M → σ) (n : Int) :
    (∃✶ m, ⌈s = t m ∧ n = 0⌉) ==> ∃✶ k, ∃✶ m, wseg c k n s (t m) ✶ ⌈0 ≤ k⌉ :=
  HProp.himpl_hexists_l (fun m => HProp.himpl_hexists_r 0 (HProp.himpl_hexists_r m
    (pure_r_intro (Nat.le_refl 0) (HProp.himpl_refl _))))

theorem wseg_base0_free_m {σ M : Type} (c : σ → σ → Int → HProp) (s : σ) (t : M → σ) :
    (∃✶ m, ⌈s = t m⌉) ==> ∃✶ k, ∃✶ n, ∃✶ m, wseg c k n s (t m) ✶ ⌈0 ≤ k⌉ :=
  HProp.himpl_hexists_l (fun m => HProp.himpl_trans (wseg_base0_free c s (t m))
    (HProp.himpl_hexists_l (fun k => HProp.himpl_hexists_r k (HProp.himpl_hexists_l (fun n =>
      HProp.himpl_hexists_r n (HProp.himpl_hexists_r m (HProp.himpl_refl _)))))))

theorem wseg_base1_cnt_m {σ M : Type} (c : σ → σ → Int → HProp) (s : σ) (t : M → σ) (n : Int) :
    (∃✶ m, ∃✶ w, ⌈n = w⌉ ✶ c s (t m) w) ==> ∃✶ k, ∃✶ m, wseg c k n s (t m) ✶ ⌈1 ≤ k⌉ :=
  HProp.himpl_hexists_l (fun m => HProp.himpl_trans (wseg_base1_cnt c s (t m) n)
    (HProp.himpl_hexists_l (fun k => HProp.himpl_hexists_r k (HProp.himpl_hexists_r m
      (HProp.himpl_refl _)))))

theorem wseg_base1_free_m {σ M : Type} (c : σ → σ → Int → HProp) (s : σ) (t : M → σ) :
    (∃✶ m, ∃✶ w, c s (t m) w) ==> ∃✶ k, ∃✶ n, ∃✶ m, wseg c k n s (t m) ✶ ⌈1 ≤ k⌉ :=
  HProp.himpl_hexists_l (fun m => HProp.himpl_trans (wseg_base1_free c s (t m))
    (HProp.himpl_hexists_l (fun k => HProp.himpl_hexists_r k (HProp.himpl_hexists_l (fun n =>
      HProp.himpl_hexists_r n (HProp.himpl_hexists_r m (HProp.himpl_refl _)))))))

theorem wseg_conc_cnt {α σ : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (st en : α → σ)
    (nE : α → Int) (nx : α → σ → Int → α) (kmin : Nat)
    (hst : ∀ a s' w, st (nx a s' w) = s') (hen : ∀ a s' w, en (nx a s' w) = en a)
    (hn : ∀ a s' w, nE (nx a s' w) = nE a - w)
    (hb : ∀ a, wseg c kmin (nE a) (st a) (en a) ==> P a)
    (h1 : ∀ a s' w, c (st a) s' w ✶ P (nx a s' w) ==> P a) :
    ∀ k a, kmin ≤ k → wseg c k (nE a) (st a) (en a) ==> P a := by
  intro k
  induction k with
  | zero =>
    intro a hk
    have : kmin = 0 := by omega
    subst this
    exact hb a
  | succ k ih =>
    intro a hk
    rcases Nat.lt_or_ge k kmin with hlt | hge
    · have : kmin = k + 1 := by omega
      subst this
      exact hb a
    · show (∃✶ s', ∃✶ w, c (st a) s' w ✶ wseg c k (nE a - w) s' (en a)) ==> P a
      refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
      have h := ih (nx a s' w) hge
      rw [hst, hen, hn] at h
      exact HProp.himpl_trans (HProp.himpl_frame_r h) (h1 a s' w)

theorem wseg_conc_free {α σ : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (st en : α → σ)
    (nx : α → σ → α) (kmin : Nat)
    (hst : ∀ a s', st (nx a s') = s') (hen : ∀ a s', en (nx a s') = en a)
    (hb : ∀ a n, wseg c kmin n (st a) (en a) ==> P a)
    (h1 : ∀ a s' w, c (st a) s' w ✶ P (nx a s') ==> P a) :
    ∀ k a n, kmin ≤ k → wseg c k n (st a) (en a) ==> P a := by
  intro k
  induction k with
  | zero =>
    intro a n hk
    have : kmin = 0 := by omega
    subst this
    exact hb a n
  | succ k ih =>
    intro a n hk
    rcases Nat.lt_or_ge k kmin with hlt | hge
    · have : kmin = k + 1 := by omega
      subst this
      exact hb a n
    · show (∃✶ s', ∃✶ w, c (st a) s' w ✶ wseg c k (n - w) s' (en a)) ==> P a
      refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
      have h := ih (nx a s') (n - w) hge
      rw [hst, hen] at h
      exact HProp.himpl_trans (HProp.himpl_frame_r h) (h1 a s' w)

theorem wseg_conc_cnt_m {α σ M : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (st : α → σ)
    (en : α → M → σ) (nE : α → Int) (nx : α → σ → Int → α) (kmin : Nat)
    (hst : ∀ a s' w, st (nx a s' w) = s') (hen : ∀ a s' w m, en (nx a s' w) m = en a m)
    (hn : ∀ a s' w, nE (nx a s' w) = nE a - w)
    (hb : ∀ a m, wseg c kmin (nE a) (st a) (en a m) ==> P a)
    (h1 : ∀ a s' w, c (st a) s' w ✶ P (nx a s' w) ==> P a) :
    ∀ k a m, kmin ≤ k → wseg c k (nE a) (st a) (en a m) ==> P a := by
  intro k
  induction k with
  | zero =>
    intro a m hk
    have : kmin = 0 := by omega
    subst this
    exact hb a m
  | succ k ih =>
    intro a m hk
    rcases Nat.lt_or_ge k kmin with hlt | hge
    · have : kmin = k + 1 := by omega
      subst this
      exact hb a m
    · show (∃✶ s', ∃✶ w, c (st a) s' w ✶ wseg c k (nE a - w) s' (en a m)) ==> P a
      refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
      have h := ih (nx a s' w) m hge
      rw [hst, hen, hn] at h
      exact HProp.himpl_trans (HProp.himpl_frame_r h) (h1 a s' w)

theorem wseg_conc_free_m {α σ M : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (st : α → σ)
    (en : α → M → σ) (nx : α → σ → α) (kmin : Nat)
    (hst : ∀ a s', st (nx a s') = s') (hen : ∀ a s' m, en (nx a s') m = en a m)
    (hb : ∀ a n m, wseg c kmin n (st a) (en a m) ==> P a)
    (h1 : ∀ a s' w, c (st a) s' w ✶ P (nx a s') ==> P a) :
    ∀ k a m n, kmin ≤ k → wseg c k n (st a) (en a m) ==> P a := by
  intro k
  induction k with
  | zero =>
    intro a m n hk
    have : kmin = 0 := by omega
    subst this
    exact hb a n m
  | succ k ih =>
    intro a m n hk
    rcases Nat.lt_or_ge k kmin with hlt | hge
    · have : kmin = k + 1 := by omega
      subst this
      exact hb a n m
    · show (∃✶ s', ∃✶ w, c (st a) s' w ✶ wseg c k (n - w) s' (en a m)) ==> P a
      refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
      have h := ih (nx a s') m (n - w) hge
      rw [hst, hen] at h
      exact HProp.himpl_trans (HProp.himpl_frame_r h) (h1 a s' w)

end Sep
