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

theorem pure_l_intro {P : Prop} {H1 H2 : HProp} (hp : P) (h : H1 ==> H2) : H1 ==> ⌈P⌉ ✶ H2 :=
  HProp.himpl_hstar_hpure_r hp h

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

noncomputable def pItem (C : Nat → Nat → HProp) (X : Nat → Nat → Nat → HProp) (it : Option Nat) (x y : Nat) : HProp :=
  Option.rec (motive := fun _ => HProp) (C x y) (fun j => X j x y) it

noncomputable def pChain (C : Nat → Nat → HProp) (X : Nat → Nat → Nat → HProp) (f : Nat → Nat)
    (b : List (Option Nat)) : Nat → Nat → Nat → HProp :=
  List.rec (motive := fun _ => Nat → Nat → Nat → HProp) (fun _ x y => ⌈x = y⌉)
    (fun it r ih i x y => List.rec (motive := fun _ => HProp) (pItem C X it x y)
      (fun _ _ _ => pItem C X it x (f i) ✶ ih (i + 1) (f i) y) r) b

def pF (C : Nat → Nat → HProp) (B : List (List (List (Option Nat))))
    (X : Nat × Nat × Nat → HProp) (a : Nat × Nat × Nat) : HProp :=
  fun h => ∃ b ∈ pNthK B a.1 [], ∃ f : Nat → Nat, pChain C (fun j x y => X (j, x, y)) f b 0 a.2.1 a.2.2 h

def pG (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (a : Nat × Nat × Nat) : HProp :=
  fun h => ∀ X : Nat × Nat × Nat → HProp, (∀ b, pF C B X b ==> X b) → X a h

theorem pItem_mono (C : Nat → Nat → HProp) {X Y : Nat → Nat → Nat → HProp}
    (hXY : ∀ j x y, X j x y ==> Y j x y) : ∀ (it : Option Nat) (x y : Nat), pItem C X it x y ==> pItem C Y it x y
  | none, _, _ => HProp.himpl_refl _
  | some j, x, y => hXY j x y

theorem pChain_mono (C : Nat → Nat → HProp) {X Y : Nat → Nat → Nat → HProp} (f : Nat → Nat)
    (hXY : ∀ j x y, X j x y ==> Y j x y) :
    ∀ (b : List (Option Nat)) (i x y : Nat), pChain C X f b i x y ==> pChain C Y f b i x y
  | [], _, _, _ => HProp.himpl_refl _
  | [it], _, x, y => pItem_mono C hXY it x y
  | it :: it2 :: r, i, x, y =>
    HProp.himpl_frame_lr (pItem_mono C hXY it x (f i)) (pChain_mono C f hXY (it2 :: r) (i + 1) (f i) y)

theorem pF_mono (C : Nat → Nat → HProp) (B : List (List (List (Option Nat))))
    {X Y : Nat × Nat × Nat → HProp} (hXY : ∀ a, X a ==> Y a) (a : Nat × Nat × Nat) :
    pF C B X a ==> pF C B Y a := by
  intro h ⟨b, hb, f, hh⟩
  exact ⟨b, hb, f, pChain_mono C f (fun j x y => hXY (j, x, y)) b 0 a.2.1 a.2.2 h hh⟩

theorem pG_induct (C : Nat → Nat → HProp) (B : List (List (List (Option Nat))))
    (X : Nat × Nat × Nat → HProp) (hX : ∀ b, pF C B X b ==> X b) (a : Nat × Nat × Nat) :
    pG C B a ==> X a := fun _ hh => hh X hX

theorem pG_pre (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (a : Nat × Nat × Nat) :
    pF C B (pG C B) a ==> pG C B a := by
  intro h hh X hX
  exact hX a h (pF_mono C B (fun b => pG_induct C B X hX b) a h hh)

theorem pF_intro {C : Nat → Nat → HProp} {B : List (List (List (Option Nat)))}
    {X : Nat × Nat × Nat → HProp} {j x y : Nat} {b : List (Option Nat)} (hb : b ∈ pNthK B j [])
    (f : Nat → Nat) : pChain C (fun j x y => X (j, x, y)) f b 0 x y ==> pF C B X (j, x, y) :=
  fun _ hh => ⟨b, hb, f, hh⟩

theorem pG_intro {C : Nat → Nat → HProp} {B : List (List (List (Option Nat)))}
    {j x y : Nat} {b : List (Option Nat)} (hb : b ∈ pNthK B j []) (f : Nat → Nat) {H : HProp}
    (h : H ==> pChain C (fun j x y => pG C B (j, x, y)) f b 0 x y) : H ==> pG C B (j, x, y) :=
  HProp.himpl_trans h (HProp.himpl_trans (pF_intro hb f) (pG_pre C B (j, x, y)))

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

theorem pKN_intro {W : Nat → Int → HProp} {P : Nat → Prop} {h : Heap} (k : Nat) (n : Int)
    (hw : W k n h) (hp : P k) : (∃✶ k, ∃✶ n, W k n ✶ ⌈P k⌉) h :=
  HProp.hexists_intro k _ (HProp.hexists_intro n _ ((HProp.hstar_hpure_r (P k) (W k n) h).2 ⟨hw, hp⟩))

theorem pKN_elim {W : Nat → Int → HProp} {P : Nat → Prop} {h : Heap}
    (hh : (∃✶ k, ∃✶ n, W k n ✶ ⌈P k⌉) h) : ∃ k n, W k n h ∧ P k := by
  obtain ⟨k, hh⟩ := HProp.hexists_elim hh
  obtain ⟨n, hh⟩ := HProp.hexists_elim hh
  exact ⟨k, n, (HProp.hstar_hpure_r (P k) (W k n) h).1 hh⟩

theorem pCell_seg (C : Nat → Nat → HProp) (x u : Nat) : C x u ==> wseg (pCell C) 1 1 x u := by
  refine HProp.himpl_trans ?_ (wseg_cell (pCell C) x u 1)
  intro h hh
  exact HProp.hexists_intro u _ ((HProp.hstar_hpure_r _ _ h).2 ⟨hh, rfl, rfl⟩)

theorem pItem_abs (C : Nat → Nat → HProp) (S : Nat → Nat → Prop) (M : Nat → Nat → Nat → HProp)
    (hM : ∀ j x y, M j x y ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈S j k⌉) :
    ∀ (it : Option Nat) (x y : Nat),
      pItem C M it x y ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈pLenC S [it] k⌉
  | none, x, y => by
    intro h hh
    exact pKN_intro 1 1 (pCell_seg C x y h hh) ⟨0, rfl, rfl⟩
  | some j, x, y => by
    intro h hh
    obtain ⟨k, n, hw, hk⟩ := pKN_elim (hM j x y h hh)
    exact pKN_intro k n hw ⟨k, 0, rfl, hk, rfl⟩

omit [Params] in
theorem pLenC_cons (S : Nat → Nat → Prop) (it : Option Nat) (r : List (Option Nat)) (k1 k2 : Nat)
    (h1 : pLenC S [it] k1) (h2 : pLenC S r k2) : pLenC S (it :: r) (k1 + k2) := by
  cases it with
  | none =>
    obtain ⟨k', hk, hz⟩ := h1
    have hz' : k' = 0 := hz
    exact ⟨k2, by omega, h2⟩
  | some j =>
    obtain ⟨a, b, hk, hj, hz⟩ := h1
    have hz' : b = 0 := hz
    exact ⟨a, k2, by omega, hj, h2⟩

theorem pChain_abs (C : Nat → Nat → HProp) (S : Nat → Nat → Prop) (M : Nat → Nat → Nat → HProp)
    (hM : ∀ j x y, M j x y ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈S j k⌉) (f : Nat → Nat) :
    ∀ (b : List (Option Nat)) (i x y : Nat),
      pChain C M f b i x y ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈pLenC S b k⌉
  | [], _, x, y => by
    intro h hh
    obtain ⟨hxy, he⟩ := HProp.hpure_elim_hempty hh
    exact pKN_intro 0 0 (wseg_nil (pCell C) 0 x y hxy rfl h he) (show pLenC S [] 0 from rfl)
  | [it], _, x, y => pItem_abs C S M hM it x y
  | it :: it2 :: r, i, x, y => by
    intro h hh
    obtain ⟨h1, h2, m1, m2, hd, he⟩ := HProp.hstar_elim hh
    obtain ⟨k1, n1, hw1, hk1⟩ := pKN_elim (pItem_abs C S M hM it x (f i) h1 m1)
    obtain ⟨k2, n2, hw2, hk2⟩ := pKN_elim (pChain_abs C S M hM f (it2 :: r) (i + 1) (f i) y h2 m2)
    have := wseg_join (pCell C) k1 k2 n1 n2 x (f i) y h (he ▸ HProp.hstar_intro hw1 hw2 hd)
    exact pKN_intro (k1 + k2) (n1 + n2) this (pLenC_cons S it (it2 :: r) k1 k2 hk1 hk2)

theorem pAbs (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (j x y : Nat) :
    pG C B (j, x, y) ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈pLen B j k⌉ := by
  refine pG_induct C B (fun a => ∃✶ k, ∃✶ n, wseg (pCell C) k n a.2.1 a.2.2 ✶ ⌈pLen B a.1 k⌉) ?_ (j, x, y)
  intro c h ⟨b, hb, f, hh⟩
  obtain ⟨k, n, hw, hk⟩ := pKN_elim (pChain_abs C (pLen B)
    (fun j x y => ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈pLen B j k⌉)
    (fun j x y => HProp.himpl_refl _) f b 0 c.2.1 c.2.2 h hh)
  exact pKN_intro k n hw (pLen_intro B c.1 k ⟨b, hb, hk⟩)

theorem pChain_congr (C : Nat → Nat → HProp) (X : Nat → Nat → Nat → HProp) (f g : Nat → Nat) :
    ∀ (b : List (Option Nat)) (i x y : Nat), (∀ l, i ≤ l → f l = g l) →
      pChain C X f b i x y = pChain C X g b i x y
  | [], _, _, _, _ => rfl
  | [_], _, _, _, _ => rfl
  | it :: it2 :: r, i, x, y, h => by
    show pItem C X it x (f i) ✶ pChain C X f (it2 :: r) (i + 1) (f i) y =
      pItem C X it x (g i) ✶ pChain C X g (it2 :: r) (i + 1) (g i) y
    rw [h i (Nat.le_refl i), pChain_congr C X f g (it2 :: r) (i + 1) (g i) y
      (fun l hl => h l (by omega))]

theorem pItem_conc (C : Nat → Nat → HProp) (S : Nat → Nat → Prop) (M : Nat → Nat → Nat → HProp)
    (hM : ∀ j k, S j k → ∀ n x y, wseg (pCell C) k n x y ==> M j x y) :
    ∀ (it : Option Nat) (k : Nat), pLenC S [it] k → ∀ n x y, wseg (pCell C) k n x y ==> pItem C M it x y
  | none, k, ⟨k', hk, hz⟩, n, x, y => by
    have hz' : k' = 0 := hz
    subst hz' hk
    intro h hh
    obtain ⟨u, hh⟩ := HProp.hexists_elim (wseg_uncell (pCell C) x y n h hh)
    obtain ⟨h1, h2, m1, m2, hd, he⟩ := HProp.hstar_elim hh
    obtain ⟨⟨hyu, _⟩, he2⟩ := HProp.hpure_elim m2
    subst he2 hyu
    rw [he, Finmap.union_empty]
    exact m1
  | some j, k, ⟨k1, k2, hk, hj, hz⟩, n, x, y => by
    have hz' : k2 = 0 := hz
    subst hz'
    rw [Nat.add_zero] at hk
    subst hk
    exact hM j _ hj n x y

theorem pChain_conc (C : Nat → Nat → HProp) (S : Nat → Nat → Prop) (M : Nat → Nat → Nat → HProp)
    (hM : ∀ j k, S j k → ∀ n x y, wseg (pCell C) k n x y ==> M j x y) :
    ∀ (b : List (Option Nat)) (i k : Nat), pLenC S b k → ∀ n x y,
      wseg (pCell C) k n x y ==> fun h => ∃ f : Nat → Nat, pChain C M f b i x y h
  | [], _, k, hk, n, x, y => by
    have hk' : k = 0 := hk
    subst hk'
    intro h hh
    obtain ⟨⟨hxy, _⟩, he⟩ := HProp.hpure_elim_hempty hh
    exact ⟨id, HProp.hpure_intro_hempty he hxy⟩
  | [it], _, k, hk, n, x, y => by
    intro h hh
    exact ⟨id, pItem_conc C S M hM it k hk n x y h hh⟩
  | it :: it2 :: r, i, k, hk, n, x, y => by
    have hsplit : ∃ k1 k2, k = k1 + k2 ∧ pLenC S [it] k1 ∧ pLenC S (it2 :: r) k2 := by
      cases it with
      | none =>
        obtain ⟨k', hk', hr⟩ := hk
        exact ⟨1, k', by omega, ⟨0, rfl, rfl⟩, hr⟩
      | some j =>
        obtain ⟨k1, k2, hk', hj, hr⟩ := hk
        exact ⟨k1, k2, hk', ⟨k1, 0, rfl, hj, rfl⟩, hr⟩
    obtain ⟨k1, k2, hk12, h1, h2⟩ := hsplit
    subst hk12
    intro h hh
    obtain ⟨t, hh⟩ := HProp.hexists_elim (wseg_split (pCell C) k1 k2 n x y h hh)
    obtain ⟨m, hh⟩ := HProp.hexists_elim hh
    obtain ⟨ha, hb, ma, mb, hd, he⟩ := HProp.hstar_elim hh
    obtain ⟨f', hf'⟩ := pChain_conc C S M hM (it2 :: r) (i + 1) k2 h2 (n - m) t y hb mb
    refine ⟨fun l => if l = i then t else f' l, ?_⟩
    show (pItem C M it x (if i = i then t else f' i) ✶
      pChain C M (fun l => if l = i then t else f' l) (it2 :: r) (i + 1) (if i = i then t else f' i) y) h
    rw [ite_eq_left rfl, pChain_congr C M (fun l => if l = i then t else f' l) f' (it2 :: r) (i + 1) t y
      (fun l hl => ite_eq_right (by omega))]
    exact he ▸ HProp.hstar_intro (pItem_conc C S M hM it k1 h1 m x t ha ma) hf' hd

theorem pConc (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (j k : Nat) (hk : pLen B j k)
    (n : Int) (x y : Nat) : wseg (pCell C) k n x y ==> pG C B (j, x, y) := by
  refine hk (fun j k => ∀ n x y, wseg (pCell C) k n x y ==> pG C B (j, x, y)) ?_ n x y
  intro i k ⟨b, hb, hl⟩ n x y h hh
  obtain ⟨f, hf⟩ := pChain_conc C _ (fun j x y => pG C B (j, x, y)) (fun j k hj => hj) b 0 k hl n x y h hh
  exact pG_pre C B (i, x, y) h ⟨b, hb, f, hf⟩

theorem pInv (C : Nat → Nat → HProp) (k : Nat) (n : Int) (s t : Nat) :
    ∀ h, wseg (pCell C) k n s t h → n = (k : Int) ∧ (k = 0 → s = t) := by
  intro h hh
  have := wseg_inv (pCell C) (fun _ _ w => w = 1) (fun k s t n => n = (k : Int) ∧ (k = 0 → s = t))
    (fun s s' w h hc => by
      obtain ⟨u, hc⟩ := HProp.hexists_elim hc
      obtain ⟨_, _, _, m2, _, _⟩ := HProp.hstar_elim hc
      exact (HProp.hpure_elim m2).1.2)
    (fun s => ⟨rfl, fun _ => rfl⟩)
    (fun k s s' t w m hw hi => ⟨by rw [hi.1, hw]; push_cast; rfl, fun h => absurd h (Nat.succ_ne_zero k)⟩)
    k n s t h hh
  exact this

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

def pNone : Nat → Nat → HProp := fun _ _ => ⌈False⌉

theorem pG_conc (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (Ms : List (Nat → Nat → HProp))
    (H : pAllIdx (fun j => ∀ b ∈ pNthK B j [], ∀ (f : Nat → Nat) (x y : Nat),
      pChain C (fun j x y => (pNthK Ms j pNone) x y) f b 0 x y ==> (pNthK Ms j pNone) x y) 0 (pLenK B))
    (j x y : Nat) : pG C B (j, x, y) ==> (pNthK Ms j pNone) x y := by
  refine pG_induct C B (fun a => (pNthK Ms a.1 pNone) a.2.1 a.2.2) ?_ (j, x, y)
  intro c h ⟨b, hb, f, hh⟩
  have hi : c.1 < B.length := by
    by_contra hc
    rw [pNthK_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hb
    cases hb
  exact pAllIdx_lt _ 0 (pLenK B) H c.1 (Nat.zero_le _) (by rw [pLenK_eq]; omega) b hb f c.2.1 c.2.2 h hh

theorem pEqSymm (a b : Nat) : (⌈a = b⌉ : HProp) ==> ⌈b = a⌉ := by
  intro h hh
  obtain ⟨he, hh⟩ := HProp.hpure_elim_hempty hh
  exact HProp.hpure_intro_hempty hh he.symm

theorem pAbsPhi (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m p : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, p, rs)) (x y : Nat) :
    pG C B (j, x, y) ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈phiI m p rs (k : Int)⌉ := by
  rw [pChkAK_eq] at hA
  rw [pNthK_getD] at hpr
  refine HProp.himpl_trans (pAbs C B j x y) ?_
  intro h hh
  obtain ⟨k, n, hw, hk⟩ := pKN_elim hh
  have hs := pChkA_sound B prof hA j k hk
  simp only [pSet, hpr] at hs
  exact pKN_intro k n hw (phiI_of_inS hs)

theorem pConcPhi (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (rk : List Nat) (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat))))
    (hC : pChkCK B prof rk N sps cert = true) (j m p : Nat) (rs : List Nat) (hj : Nat.blt j (pLenK B) = true)
    (hpr : pNthK prof j pDflt = (m, p, rs)) (k : Nat) (n : Int) (x y : Nat) (hk : phiI m p rs (k : Int)) :
    wseg (pCell C) k n x y ==> pG C B (j, x, y) := by
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
  exact pConc C B j k (pChkC_sound B prof rk N sps cert hC _ j k rfl hj hin') n x y

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

theorem pAbsLe (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, 1, rs)) (x y : Nat) :
    pG C B (j, x, y) ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈m ≤ k⌉ := by
  rw [pChkAK_eq] at hA
  rw [pNthK_getD] at hpr
  refine HProp.himpl_trans (pAbs C B j x y) ?_
  intro h hh
  obtain ⟨k, n, hw, hk⟩ := pKN_elim hh
  have hs := pChkA_sound B prof hA j k hk
  simp only [pSet, hpr, inS, pble, Bool.and_eq_true, decide_eq_true_eq] at hs
  exact pKN_intro k n hw hs.1

theorem pConcLe (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (rk : List Nat) (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat))))
    (hC : pChkCK B prof rk N sps cert = true) (j m : Nat) (rs : List Nat) (hj : Nat.blt j (pLenK B) = true)
    (hpr : pNthK prof j pDflt = (m, 1, rs)) (k : Nat) (n : Int) (x y : Nat) (hk : m ≤ k) :
    wseg (pCell C) k n x y ==> pG C B (j, x, y) :=
  pConcPhi C B prof rk N sps cert hC j m 1 rs hj hpr k n x y (Int.ofNat_le.mpr hk)

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

theorem hasLoc_pure_star {p : Loc} {P : Prop} {H : HProp}
    (h : P → hasLoc p H) : hasLoc p (⌈P⌉ ✶ H) := by
  intro hh hj
  rcases (HProp.hstar_hpure_l P H hh).1 hj with ⟨hP, hH⟩
  exact h hP hh hH

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

theorem neLocs_mono {p q : Loc} {F G : HProp} (h : F ==> G) (hg : neLocs p q G) :
    neLocs p q F := fun hh hf => hg hh (h hh hf)

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

theorem wseg_conc_cnt_h {α σ : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (st en : α → σ)
    (nE : α → Int) (nx : α → σ → Int → α) (kmin : Nat)
    (hst : ∀ a s' w, holdsP (st (nx a s' w) = s') (c (st a) s' w))
    (hen : ∀ a s' w, en (nx a s' w) = en a)
    (hn : ∀ a s' w, nE (nx a s' w) = nE a - w)
    (hb : ∀ a, Sep.wseg c kmin (nE a) (st a) (en a) ==> P a)
    (h1 : ∀ a s' w, c (st a) s' w ✶ P (nx a s' w) ==> P a) :
    ∀ k a, kmin ≤ k → Sep.wseg c k (nE a) (st a) (en a) ==> P a := by
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
    · show (∃✶ s', ∃✶ w, c (st a) s' w ✶ Sep.wseg c k (nE a - w) s' (en a)) ==> P a
      refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
      have h := ih (nx a s' w) hge
      rw [hen, hn] at h
      refine HProp.himpl_trans (HProp.himpl_frame_l (himpl_pure_of (hst a s' w))) ?_
      rw [HProp.hstar_assoc]
      refine HProp.himpl_hstar_hpure_l (fun he => ?_)
      rw [he] at h
      exact HProp.himpl_trans (HProp.himpl_frame_r h) (h1 a s' w)

theorem wseg_conc_free_h {α σ : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (st en : α → σ)
    (nx : α → σ → α) (kmin : Nat)
    (hst : ∀ a s' w, holdsP (st (nx a s') = s') (c (st a) s' w))
    (hen : ∀ a s', en (nx a s') = en a)
    (hb : ∀ a n, Sep.wseg c kmin n (st a) (en a) ==> P a)
    (h1 : ∀ a s' w, c (st a) s' w ✶ P (nx a s') ==> P a) :
    ∀ k a n, kmin ≤ k → Sep.wseg c k n (st a) (en a) ==> P a := by
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
    · show (∃✶ s', ∃✶ w, c (st a) s' w ✶ Sep.wseg c k (n - w) s' (en a)) ==> P a
      refine HProp.himpl_hexists_l (fun s' => HProp.himpl_hexists_l (fun w => ?_))
      have h := ih (nx a s') (n - w) hge
      rw [hen] at h
      refine HProp.himpl_trans (HProp.himpl_frame_l (himpl_pure_of (hst a s' w))) ?_
      rw [HProp.hstar_assoc]
      refine HProp.himpl_hstar_hpure_l (fun he => ?_)
      rw [he] at h
      exact HProp.himpl_trans (HProp.himpl_frame_r h) (h1 a s' w)

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

end Sep.Xsearch
