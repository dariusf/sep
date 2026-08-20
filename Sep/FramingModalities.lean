import Sep.HProp

/-! Framing modalities: Contains and Missing -/

open HProp Notation

namespace Heifer.Refine

universe u

variable [Params]

/-- "The heap contains at least a H-piece", or "H, weakened so the frame rule can apply trivially". Introduces an existentially quantified frame. -/
def Contains (H : HProp) : HProp :=
  fun h => ∃ h1 hf, H hf ∧ Finmap.Disjoint h1 hf ∧ h = h1 ∪ hf

/-- "The heap has room for a disjoint H-piece". Introduces an existentially quantified disjoint extension/"anti-frame" (instead of hiding external heap from us, as consume would, this hides internal heap from the outside). -/
def Missing (H : HProp) : HProp :=
  fun h => ∃ hf, H hf ∧ Finmap.Disjoint h hf

/-! Contains -/

theorem contains_eq (H : HProp) :
    Contains H = H ✶ htop := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, p, hHp, hd, rfl⟩
    rw [Finmap.union_comm_of_disjoint hd]
    exact HProp.hstar_intro hHp (HProp.htop_intro _) hd.symm
  · intro hh
    obtain ⟨h1, h2, hH, _, hd, rfl⟩ := HProp.hstar_elim hh
    exact ⟨h2, h1, hH, hd.symm, Finmap.union_comm_of_disjoint hd⟩

/-- Every heap contains the empty piece -/
theorem contains_hempty :
    Contains hempty = htop := by
  rw [contains_eq, HProp.hstar_hempty_l]

theorem contains_self (H : HProp) :
    H ==> Contains H := by
  rw [contains_eq]
  conv_lhs => rw [← HProp.hstar_hempty_r H]
  exact HProp.himpl_frame_r (HProp.himpl_htop_r _)

theorem contains_hsingle {x v} :
    x ↦ v ==> Contains (x ↦ v) :=
  contains_self _

theorem contains_himpl {H1 H2 : HProp}
    (himp : H1 ==> H2) :
    Contains H1 ==> Contains H2 := by
  rw [contains_eq, contains_eq]
  exact HProp.himpl_frame_l himp

/-- Contains distributes asymmetrically over separating conjunction -/
theorem contains_hstar (H1 H2 : HProp) :
    Contains (H1 ✶ H2) = H1 ✶ Contains H2 := by
  rw [contains_eq, contains_eq, HProp.hstar_assoc]

theorem contains_idem (H : HProp) :
    Contains (Contains H) = Contains H := by
  rw [contains_eq (Contains H), contains_eq H,
      HProp.hstar_assoc, HProp.hstar_htop_htop]

theorem contains_hstar_symm (H1 H2 : HProp) :
    Contains H1 ✶ Contains H2 = Contains (H1 ✶ H2) := by
  rw [HProp.hstar_comm (Contains H1) (Contains H2),
      ← contains_hstar (Contains H2) H1,
      HProp.hstar_comm (Contains H2) H1,
      ← contains_hstar H1 H2,
      contains_idem]

/-- Contains is preserved by adding more disjoint heaps -/
theorem contains_frame (H H' : HProp) :
    Contains H ✶ H' ==> Contains H := by
  rw [contains_eq, HProp.hstar_assoc]
  exact HProp.himpl_frame_r (fun h _ => HProp.htop_intro h)

theorem contains_hexists {A : Sort _} (J : A → HProp) :
    Contains (∃✶ a, J a) = (∃✶ a, Contains (J a)) := by
  simp only [contains_eq, HProp.hstar_hexists]

/-- A pure piece is contained iff it holds
    (the htop frame absorbs everything). -/
theorem contains_hpure (P : Prop) :
    Contains (hpure P) = hpure P ✶ htop :=
  contains_eq _

/-! Missing -/

theorem missing_eq (H : HProp) :
    Missing H = H -⊛ htop := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hHp, hd⟩
    exact ⟨p, hHp, hd, HProp.htop_intro _⟩
  · rintro ⟨p, hHp, hd, _⟩
    exact ⟨p, hHp, hd⟩

/-- Taking away things from a heap with a missing piece preserves the fact that the piece is missing. Or, `Missing H` is anti-monotone in the heap: shrinking a heap preserves the property that `H` fits as a disjoint extension. -/
theorem missing_subheap {H} {p h1 h2 : Heap}
    (hm : Missing H h1)
    (heq : h2 ∪ p = h1) :
    Missing H h2 := by
  obtain ⟨q, hq, hd⟩ := hm
  subst heq
  exact ⟨q, hq, by fmap_disjoint⟩

/-- emp is missing from every heap (or, every heap can absorb the empty proposition) -/
theorem missing_hempty :
    Missing hempty = htop := by
  rw [missing_eq, HProp.hsept_hempty_l]

/-- Missing is monotonic: a stronger proposition is still missing wherever the weaker one is. -/
theorem missing_himpl {H1 H2 : HProp}
    (himp : H1 ==> H2) :
    Missing H1 ==> Missing H2 := by
  rw [missing_eq, missing_eq]
  exact HProp.hsept_mono himp (HProp.himpl_refl _)

/-- Missing distributes over ✶ as currying; the dual of contains_hstar. -/
theorem missing_hstar (H1 H2 : HProp) :
    Missing (H1 ✶ H2) = H1 -⊛ Missing H2 := by
  rw [missing_eq, missing_eq, hsept_hstar_l]

theorem missing_hexists {A : Sort _} (J : A → HProp) :
    Missing (∃✶ a, J a) = (∃✶ a, Missing (J a)) := by
  simp only [missing_eq, HProp.hsept_hexists_l]

theorem missing_hpure (P : Prop) :
    Missing (HProp.hpure P) = HProp.hpure P ✶ htop := by
  rw [missing_eq, hsept_hpure_l]

/-! Both -/

theorem contains_eq_missing_hstar (H : HProp) :
    Contains H = Missing H ✶ H := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, p, hHp, hd, rfl⟩
    exact HProp.hstar_intro (show Missing H h1 from ⟨p, hHp, hd⟩) hHp hd
  · intro hh
    obtain ⟨k1, k2, ⟨p, hHp, hd1p⟩, hHk2, hd12, rfl⟩ := HProp.hstar_elim hh
    exact ⟨k1, k2, hHk2, hd12, rfl⟩

/-- Layering `Contains` inside `Missing` collapses: only the inner `H`-piece
    contributes to the disjointness check. -/
theorem missing_contains_eq (H : HProp) :
    Missing (Contains H) = Missing H := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, ⟨k1, q, hHq, hdk1q, rfl⟩, hdhp⟩
    exact ⟨q, hHq, by fmap_disjoint⟩
  · rintro ⟨q, hHq, hdhq⟩
    refine ⟨q, ⟨∅, q, hHq, Finmap.disjoint_empty q, ?_⟩, hdhq⟩
    rw [Finmap.empty_union]

/-- Dual to `missing_contains_eq`, but with information loss: layering `Missing`
    inside `Contains` collapses to a satisfiability check on `H`. The empty
    sub-heap always witnesses `Missing H` whenever `H` has any witness, so the
    outer `Contains` becomes trivially true (modulo satisfiability of `H`). -/
theorem contains_missing_eq (H : HProp) :
    Contains (Missing H) = ⌈Sat H⌉ ✶ htop := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, hf, ⟨p, hHp, _⟩, _, rfl⟩
    have : ((⌈Sat H⌉ : HProp) ✶ htop) (∅ ∪ (h1 ∪ hf)) :=
      HProp.hstar_intro
        (HProp.hpure_intro _ ⟨p, hHp⟩) (HProp.htop_intro _)
        (Finmap.disjoint_empty _)
    rw [Finmap.empty_union] at this; exact this
  · intro hh
    obtain ⟨k1, k2, hpure, _, _, rfl⟩ := HProp.hstar_elim hh
    obtain ⟨⟨p, hHp⟩, rfl⟩ := HProp.hpure_elim hpure
    refine ⟨∅ ∪ k2, ∅,
      ⟨p, hHp, Finmap.disjoint_empty _⟩,
      (Finmap.disjoint_empty _).symm, ?_⟩
    rw [Finmap.union_empty]

/-- Missing preserves satisfiability -/
theorem sat_missing {H : HProp} : Sat (Missing H) ↔ Sat H :=
  ⟨fun ⟨_, p, hHp, _⟩ => ⟨p, hHp⟩,
   fun ⟨p, hHp⟩ => ⟨∅, p, hHp, Finmap.disjoint_empty _⟩⟩

/-- Contains preserves satisfiability -/
theorem sat_contains {H : HProp} : Sat (Contains H) ↔ Sat H := by
  rw [contains_eq]
  refine ⟨fun h => HProp.sat_hstar_left h, fun ⟨p, hHp⟩ => ?_⟩
  exact ⟨p ∪ ∅,
    HProp.hstar_intro hHp (HProp.htop_intro _)
      (Finmap.disjoint_empty _).symm⟩

/-- When `H` is precise, any heap satisfying both
    `Missing H` and `Contains H` (the *same* heap, conjoined heap-pointwise via
    `⊓`) forces `H` to hold of the empty heap. The `✶ htop` on the right lifts
    the pure conclusion to hold at any underlying heap. Precision forces the
    missing and contained pieces to coincide; being simultaneously disjoint
    from `h` and a sub-heap of `h` forces it to be empty. -/
theorem missing_contains_himpl_hpure {H : HProp}
    (hprec : Precise H) :
    Missing H ⊓ Contains H ==> ⌈H ∅⌉ ✶ htop := by
  intro h hh
  obtain ⟨hm, hc⟩ := (HProp.hand_eq _ _ h).mp hh
  obtain ⟨p, hHp, hdp⟩ := hm
  obtain ⟨h1, p', hHp', hdp', heq⟩ := hc
  have hpe : p = p' := hprec p p' hHp hHp'
  subst hpe
  have hpempty : p = ∅ := by
    apply Finmap.ext_lookup
    intro a
    rw [Finmap.lookup_empty]
    by_cases hap : a ∈ p
    · exact absurd hap (hdp a (heq ▸ Finmap.mem_union.mpr (Or.inr hap)))
    · exact Finmap.lookup_eq_none.mpr hap
  have : ((⌈H ∅⌉ : HProp) ✶ htop) (∅ ∪ h) :=
    HProp.hstar_intro
      (HProp.hpure_intro _ (hpempty ▸ hHp)) (HProp.htop_intro _)
      (Finmap.disjoint_empty _)
  rw [Finmap.empty_union] at this; exact this

/-- Contrapositive corollary: `Missing H` and `Contains H` cannot both hold of
    the same heap when `H` is precise and does not hold of the empty heap. -/
theorem missing_contains_false {H : HProp}
    (hprec : Precise H) (hne : ¬ H ∅) :
    Missing H ⊓ Contains H ==> ⌈False⌉ := by
  intro h hh
  obtain ⟨k1, k2, hpure, _, _, _⟩ :=
    HProp.hstar_elim (missing_contains_himpl_hpure hprec h hh)
  exact ((hne (HProp.hpure_elim hpure).1)).elim

/-- Concrete extraction with named witness: a heap containing `H` decomposes
    as `(h \ q) ⊕ q` for some `q` satisfying `H`, with the residue disjoint
    from `q`. -/
theorem contains_split (H : HProp) {h : Heap} (hc : Contains H h) :
    ∃ q, H q ∧ Finmap.Disjoint (h \ q) q
      ∧ (h \ q) ∪ q = h := by
  obtain ⟨rest, p, hHp, hd, heq⟩ := hc
  refine ⟨p, hHp, Finmap.disjoint_sdiff_self h p, ?_⟩
  rw [heq]; exact Finmap.union_sdiff_cancel hd
