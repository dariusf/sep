import Mathlib.Data.Finmap

namespace Finmap

universe u v

variable {α : Type u} {β : Type v}

attribute [symm] Finmap.Disjoint.symm

@[simp] theorem lookup_singleton_ne [DecidableEq α] {a a1 : α} (b : β) (h : a1 ≠ a) :
    lookup a1 (singleton a b : Finmap fun _ : α => β) = none := by
  rw [show (singleton a b : Finmap fun _ : α => β) = insert a b ∅ from rfl]
  simp [h]

theorem insert_lookup_self [DecidableEq α] {m : Finmap fun _ : α => β} {a : α} {b : β}
    (h : lookup a m = some b) :
    insert a b m = m := by
  apply ext_lookup
  intro a1
  by_cases ha : a1 = a
  · subst ha; simp [h]
  · simp [lookup_insert_of_ne _ ha]

theorem lookup_union_left_of_eq_some [DecidableEq α] {m1 m2 : Finmap fun _ : α => β} {a : α}
    {b : β}
    (h : lookup a m1 = some b) :
    lookup a (m1 ∪ m2) = some b := by
  rw [lookup_union_left (mem_iff.mpr ⟨b, h⟩)]
  exact h

theorem insert_union_right [DecidableEq α] {m1 m2 : Finmap fun _ : α => β} {a : α} (b : β)
    (h : a ∉ m1) :
    insert a b (m1 ∪ m2) = m1 ∪ insert a b m2 := by
  apply ext_lookup
  intro a1
  by_cases ha : a1 = a
  · subst ha
    rw [lookup_insert, lookup_union_right h, lookup_insert]
  · rw [lookup_insert_of_ne _ ha]
    by_cases hm : a1 ∈ m1
    · rw [lookup_union_left (s₂ := m2) hm, lookup_union_left (s₂ := insert a b m2) hm]
    · rw [lookup_union_right hm, lookup_union_right hm, lookup_insert_of_ne _ ha]

theorem insert_eq_singleton_union [DecidableEq α] (m : Finmap fun _ : α => β) (a : α) (b : β) :
    insert a b m = singleton a b ∪ m := by
  apply ext_lookup
  intro a1
  by_cases h : a1 = a
  · subst h
    rw [lookup_insert, lookup_union_left_of_eq_some lookup_singleton_eq]
  · rw [lookup_insert_of_ne _ h, lookup_union_right]
    intro hmem
    exact h ((mem_singleton a1 a b).mp hmem)

theorem disjoint_singleton_left [DecidableEq α] {a : α} {b : β} {m : Finmap fun _ : α => β}
    (h : a ∉ m) :
    Disjoint (singleton a b) m := by
  intro x hx
  rw [(mem_singleton x a b).mp hx]
  exact h

theorem disjoint_insert_left [DecidableEq α] {m1 m2 : Finmap fun _ : α => β} {a : α} {b : β}
    (hd : Disjoint m1 m2)
    (ha : a ∈ m1) :
    Disjoint (insert a b m1) m2 := by
  intro x hx
  rw [mem_insert] at hx
  rcases hx with h | h
  · rw [h]; exact hd a ha
  · exact hd x h

theorem not_disjoint_singleton_singleton [DecidableEq α] {a : α} {b1 b2 : β} :
    ¬ Disjoint (singleton a b1 : Finmap fun _ : α => β) (singleton a b2) := by
  intro h
  have hnm : a ∉ (singleton a b2 : Finmap fun _ : α => β) := h a (by simp)
  simp at hnm

@[simp] theorem disjoint_empty_right (m : Finmap fun _ : α => β) : Disjoint m ∅ :=
  Disjoint.symm _ _ (disjoint_empty m)

theorem union_cancel_right [DecidableEq α] {m1 m2 p : Finmap fun _ : α => β}
    (hd1 : Disjoint m1 p)
    (hd2 : Disjoint m2 p)
    (heq : m1 ∪ p = m2 ∪ p) :
    m1 = m2 :=
  (union_cancel hd1 hd2).mp heq

theorem union_cancel_left [DecidableEq α] {m1 m2 p : Finmap fun _ : α => β}
    (hd1 : Disjoint p m1)
    (hd2 : Disjoint p m2)
    (heq : p ∪ m1 = p ∪ m2) :
    m1 = m2 :=
  union_cancel_right (Disjoint.symm _ _ hd1) (Disjoint.symm _ _ hd2)
    (by rw [union_comm_of_disjoint (Disjoint.symm _ _ hd1),
            union_comm_of_disjoint (Disjoint.symm _ _ hd2), heq])

private theorem lookup_foldl_erase [DecidableEq α]
    (l : List (Sigma fun _ : α => β)) (m : Finmap fun _ : α => β) (a : α) :
    lookup a (l.foldl (fun d s => erase s.1 d) m) =
      if a ∈ l.keys then none else lookup a m := by
  induction l generalizing m with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih]
    by_cases ha : a ∈ tl.keys
    · simp [ha, List.keys_cons]
    · by_cases he : a = hd.1
      · subst he; simp [ha, List.keys_cons]
      · simp [ha, he, List.keys_cons, lookup_erase_ne (a := a) (a' := hd.1) he]

theorem lookup_sdiff [DecidableEq α] (m1 m2 : Finmap fun _ : α => β) (a : α) :
    lookup a (m1 \ m2) = if a ∈ m2 then none else lookup a m1 := by
  induction m2 using Finmap.induction_on with
  | _ l =>
    show lookup a (sdiff m1 (AList.toFinmap l)) = _
    have heq : sdiff m1 (AList.toFinmap l)
        = l.entries.foldl (fun d s => erase s.1 d) m1 := rfl
    rw [heq, lookup_foldl_erase]
    have hmem : (a ∈ AList.toFinmap l) ↔ (a ∈ l.entries.keys) := by
      rw [mem_def, AList.toFinmap_entries]; rfl
    by_cases ha : a ∈ l.entries.keys
    · rw [if_pos ha, if_pos (hmem.mpr ha)]
    · rw [if_neg ha, if_neg (fun h => ha (hmem.mp h))]

theorem lookup_sdiff_of_mem [DecidableEq α] {m1 m2 : Finmap fun _ : α => β} {a : α}
    (h : a ∈ m2) :
    lookup a (m1 \ m2) = none := by
  rw [lookup_sdiff]; simp [h]

theorem lookup_sdiff_of_notMem [DecidableEq α] {m1 m2 : Finmap fun _ : α => β} {a : α}
    (h : a ∉ m2) :
    lookup a (m1 \ m2) = lookup a m1 := by
  rw [lookup_sdiff]; simp [h]

theorem mem_sdiff [DecidableEq α] {m1 m2 : Finmap fun _ : α => β} {a : α} :
    a ∈ m1 \ m2 ↔ a ∈ m1 ∧ a ∉ m2 := by
  rw [mem_iff, mem_iff]
  constructor
  · rintro ⟨b, hb⟩
    by_cases h2 : a ∈ m2
    · rw [lookup_sdiff_of_mem (m1 := m1) h2] at hb; cases hb
    · rw [lookup_sdiff_of_notMem (m1 := m1) h2] at hb
      exact ⟨⟨b, hb⟩, h2⟩
  · rintro ⟨⟨b, hb⟩, h2⟩
    exact ⟨b, by rw [lookup_sdiff_of_notMem (m1 := m1) h2]; exact hb⟩

theorem disjoint_sdiff_self [DecidableEq α] (m1 m2 : Finmap fun _ : α => β) :
    Disjoint (m1 \ m2) m2 :=
  fun _ ha => (mem_sdiff.mp ha).2

theorem disjoint_sdiff_of_disjoint [DecidableEq α] {m1 m2 p : Finmap fun _ : α => β}
    (h : Disjoint m1 p) :
    Disjoint (m1 \ m2) p :=
  fun a ha => h a (mem_sdiff.mp ha).1

theorem sdiff_union_cancel [DecidableEq α] {m1 m2 : Finmap fun _ : α => β}
    (hd : Disjoint m1 m2) :
    (m1 ∪ m2) \ m2 = m1 := by
  apply ext_lookup
  intro a
  by_cases ha : a ∈ m2
  · rw [lookup_sdiff_of_mem ha]
    exact (lookup_eq_none.mpr (fun h => hd a h ha)).symm
  · rw [lookup_sdiff_of_notMem ha]
    exact lookup_union_left_of_not_in ha

theorem union_sdiff_cancel [DecidableEq α] {m1 m2 : Finmap fun _ : α => β}
    (hd : Disjoint m1 m2) :
    ((m1 ∪ m2) \ m2) ∪ m2 = m1 ∪ m2 := by
  rw [sdiff_union_cancel hd]

theorem sdiff_eq_of_union_eq [DecidableEq α] {m1 p q1 q2 : Finmap fun _ : α => β}
    (hdhp : Disjoint m1 p)
    (hd12 : Disjoint q1 q2)
    (hdpq2 : Disjoint p q2)
    (heq : m1 ∪ p = q1 ∪ q2) :
    m1 \ q2 = q1 \ p := by
  apply ext_lookup
  intro a
  have hpoint : lookup a (m1 ∪ p) = lookup a (q1 ∪ q2) := by rw [heq]
  by_cases ha2 : a ∈ q2
  · rw [lookup_sdiff_of_mem (m1 := m1) ha2,
        lookup_sdiff_of_notMem (m1 := q1) (fun h => hdpq2 a h ha2),
        lookup_eq_none.mpr (fun h => hd12 a h ha2)]
  · by_cases hap : a ∈ p
    · rw [lookup_sdiff_of_notMem (m1 := m1) ha2, lookup_sdiff_of_mem (m1 := q1) hap,
          lookup_eq_none.mpr (fun h => hdhp a h hap)]
    · rw [lookup_sdiff_of_notMem (m1 := m1) ha2, lookup_sdiff_of_notMem (m1 := q1) hap,
          ← lookup_union_left_of_not_in (s₁ := m1) hap, hpoint,
          lookup_union_left_of_not_in (s₁ := q1) ha2]

theorem union_sdiff_eq_of_union_eq [DecidableEq α] {m1 p q1 q2 : Finmap fun _ : α => β}
    (hd12 : Disjoint q1 q2)
    (hdpq2 : Disjoint p q2)
    (heq : m1 ∪ p = q1 ∪ q2) :
    (m1 \ q2) ∪ p = q1 := by
  have hsdq2 : Disjoint (m1 \ q2) q2 := disjoint_sdiff_self m1 q2
  have hh : (m1 \ q2) ∪ q2 = m1 := by
    apply ext_lookup
    intro a
    by_cases ha2 : a ∈ q2
    · have hpoint : lookup a (m1 ∪ p) = lookup a (q1 ∪ q2) := by rw [heq]
      rw [lookup_union_right (fun h => hsdq2 a h ha2),
          ← lookup_union_right (fun h => hd12 a h ha2), ← hpoint,
          lookup_union_left_of_not_in (fun h => hdpq2 a h ha2)]
    · rw [lookup_union_left_of_not_in ha2]
      exact lookup_sdiff_of_notMem ha2
  have hkey : ((m1 \ q2) ∪ p) ∪ q2 = q1 ∪ q2 := by
    calc ((m1 \ q2) ∪ p) ∪ q2
        = (m1 \ q2) ∪ (p ∪ q2) := union_assoc
      _ = (m1 \ q2) ∪ (q2 ∪ p) := by rw [union_comm_of_disjoint hdpq2]
      _ = ((m1 \ q2) ∪ q2) ∪ p := union_assoc.symm
      _ = m1 ∪ p := by rw [hh]
      _ = q1 ∪ q2 := heq
  exact union_cancel_right ((disjoint_union_left _ _ _).mpr ⟨hsdq2, hdpq2⟩) hd12 hkey

end Finmap
