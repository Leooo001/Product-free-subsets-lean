import RequestProject.IntervalUnion

/-!
# Covering compact sets by finite unions of closed intervals

This file collects the elementary geometric lemmas used both for the outer-fattening proof of
the measurable product-free bound (`RequestProject/Fattening.lean`) and for the measurable key
lemma (`RequestProject/KeyLemma.lean`).

* `union_Icc_aux` / `IsIntervalUnion.union_Icc`: inserting a closed interval into a canonical
  finite union of closed intervals again yields such a union.
* `exists_isIntervalUnion_biUnion`: any finite union of closed intervals is (as a set) an
  `IsIntervalUnion` for a suitable sorted, strictly separated list.
* `exists_intervalUnion_cover`: a compact set `K` is covered by a finite union of closed
  intervals `F` (an `IsIntervalUnion`) contained in the closed `η`-thickening `K + [-η, η]`.
-/

open MeasureTheory Set Metric
open scoped Pointwise

noncomputable section

namespace ProductFree

/-- Auxiliary induction for `IsIntervalUnion.union_Icc`: inserting a closed interval `[a,b]`
into a sorted, strictly separated list of closed intervals again yields such a list (in
canonical form).  Proved by induction on the list, merging `[a,b]` with the overlapping
components (the classic "merge intervals" recursion). -/
theorem union_Icc_aux : ∀ (ivs : List (ℝ × ℝ)) (a b : ℝ),
    (∀ p ∈ ivs, p.1 ≤ p.2) → ivs.IsChain (fun p q => p.2 < q.1) →
    ∃ ivs' : List (ℝ × ℝ),
      IsIntervalUnion ((⋃ p ∈ ivs, Icc p.1 p.2) ∪ Icc a b) ivs' := by
  have hcons : ∀ (P : ℝ × ℝ) (R : List (ℝ × ℝ)),
      (⋃ q ∈ (P :: R), Icc q.1 q.2) = Icc P.1 P.2 ∪ ⋃ q ∈ R, Icc q.1 q.2 := by
    intro P R; simp [List.mem_cons, Set.iUnion_or, Set.iUnion_union_distrib]
  intro ivs
  induction ivs with
  | nil =>
    intro a b _ _
    by_cases hab : a ≤ b
    · exact ⟨[(a, b)], (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact hab),
        (by simp), (by simp)⟩
    · exact ⟨[], (by simp), (by simp), (by simp [Icc_eq_empty hab])⟩
  | cons p rest ih =>
    intro a b hle hchain
    have hp_le : p.1 ≤ p.2 := hle p (List.mem_cons_self ..)
    have hrest_le : ∀ q ∈ rest, q.1 ≤ q.2 := fun q hq => hle q (List.mem_cons_of_mem _ hq)
    obtain ⟨hhead, hrest_chain⟩ := List.isChain_cons.mp hchain
    have hall : ∀ q ∈ rest, p.2 < q.1 := by
      intro q hq
      have hne : rest ≠ [] := by rintro rfl; simp at hq
      have hh : p.2 < (rest.head hne).1 :=
        hhead _ (by rw [List.head?_eq_some_head hne]; exact Option.mem_some_self _)
      have hmono : (rest.head hne).1 ≤ q.1 := by
        have hsub := IsIntervalUnion.subset_Icc (A := ⋃ p ∈ rest, Icc p.1 p.2)
          ⟨hrest_le, hrest_chain, rfl⟩ hne
        exact (hsub (Set.mem_biUnion hq (left_mem_Icc.mpr (hrest_le q hq)))).1
      linarith
    by_cases hab : a ≤ b
    · rcases lt_or_ge b p.1 with hcase1 | hge1
      · -- `[a,b]` lies strictly to the left of the whole union
        refine ⟨(a, b) :: p :: rest, ?_, ?_, ?_⟩
        · intro q hq; rcases List.mem_cons.mp hq with rfl | hq
          · exact hab
          · exact hle q hq
        · rw [List.isChain_cons]
          refine ⟨?_, hchain⟩
          intro y hy
          rw [List.head?_cons, Option.mem_some_iff] at hy
          subst hy; exact hcase1
        · ext x; simp only [hcons, mem_union]; tauto
      · rcases lt_or_ge p.2 a with hcase2 | hge2
        · -- `[a,b]` lies strictly to the right of `p`; recurse on the tail
          obtain ⟨ivs'', h1'', h2'', h3''⟩ := ih a b hrest_le hrest_chain
          refine ⟨p :: ivs'', ?_, ?_, ?_⟩
          · intro q hq; rcases List.mem_cons.mp hq with rfl | hq
            · exact hp_le
            · exact h1'' q hq
          · rw [List.isChain_cons]
            refine ⟨?_, h2''⟩
            intro y hy
            have hymem : y ∈ ivs'' := List.mem_of_mem_head? hy
            have hy0 : y.1 ∈ ⋃ p ∈ ivs'', Icc p.1 p.2 :=
              Set.mem_biUnion hymem (left_mem_Icc.mpr (h1'' y hymem))
            rw [← h3''] at hy0
            rcases hy0 with hy1 | hy1
            · obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp hy1
              exact lt_of_lt_of_le (hall q hq) hyq.1
            · exact lt_of_lt_of_le hcase2 hy1.1
          · rw [hcons p rest, hcons p ivs'', ← h3'', Set.union_assoc]
        · -- `[a,b]` overlaps `p`; merge into `[min p.1 a, max p.2 b]` and recurse
          have hovl : Icc p.1 p.2 ∪ Icc a b = Icc (min p.1 a) (max p.2 b) := by
            ext x
            simp only [mem_union, mem_Icc, min_le_iff, le_max_iff]
            constructor
            · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
              · exact ⟨Or.inl h, Or.inl h'⟩
              · exact ⟨Or.inr h, Or.inr h'⟩
            · rintro ⟨hl, hr⟩
              rcases hl with hl | hl <;> rcases hr with hr | hr
              · exact Or.inl ⟨hl, hr⟩
              · rcases le_total x p.2 with hx | hx
                · exact Or.inl ⟨hl, hx⟩
                · exact Or.inr ⟨by linarith, hr⟩
              · rcases le_total x b with hx | hx
                · exact Or.inr ⟨hl, hx⟩
                · exact Or.inl ⟨by linarith, hr⟩
              · exact Or.inr ⟨hl, hr⟩
          obtain ⟨ivs'', h1'', h2'', h3''⟩ := ih (min p.1 a) (max p.2 b) hrest_le hrest_chain
          refine ⟨ivs'', h1'', h2'', ?_⟩
          rw [hcons p rest, ← h3'', ← hovl]
          ext x; simp only [mem_union]; tauto
    · -- `[a,b]` is empty
      refine ⟨p :: rest, hle, hchain, ?_⟩
      rw [Icc_eq_empty hab, Set.union_empty]

/-- Inserting one closed interval into a finite union of closed intervals again yields a
finite union of closed intervals (in canonical sorted, strictly separated form). -/
lemma IsIntervalUnion.union_Icc {A : Set ℝ} {ivs : List (ℝ × ℝ)}
    (h : IsIntervalUnion A ivs) (a b : ℝ) :
    ∃ ivs' : List (ℝ × ℝ), IsIntervalUnion (A ∪ Icc a b) ivs' := by
  obtain ⟨hle, hchain, hAeq⟩ := h
  rw [hAeq]
  exact union_Icc_aux ivs a b hle hchain

/-- Any finite union of closed intervals (given by an arbitrary list of endpoint pairs) is,
as a set, an `IsIntervalUnion` for a suitable sorted, strictly separated list. -/
lemma exists_isIntervalUnion_biUnion (L : List (ℝ × ℝ)) :
    ∃ ivs : List (ℝ × ℝ), IsIntervalUnion (⋃ p ∈ L, Icc p.1 p.2) ivs := by
  induction L with
  | nil => exact ⟨[], by simp [IsIntervalUnion]⟩
  | cons p L ih =>
    obtain ⟨ivs, hivs⟩ := ih
    obtain ⟨ivs', hivs'⟩ := hivs.union_Icc p.1 p.2
    refine ⟨ivs', ?_⟩
    convert hivs' using 2
    simp [Set.union_comm]

/-- A compact set `K` is covered by a finite union of closed intervals `F` (an
`IsIntervalUnion`) that is contained in the closed `η`-thickening `K + [-η, η]`. -/
lemma exists_intervalUnion_cover {K : Set ℝ} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    ∃ (F : Set ℝ) (ivs : List (ℝ × ℝ)),
      IsIntervalUnion F ivs ∧ K ⊆ F ∧ F ⊆ K + Icc (-η) η := by
  obtain ⟨b', hb'K, hb'fin, hcov⟩ := hK.elim_finite_subcover_image
    (b := K) (c := fun x => Ioo (x - η) (x + η))
    (fun x _ => isOpen_Ioo)
    (fun x hx => Set.mem_biUnion hx ⟨by linarith, by linarith⟩)
  classical
  set ft := hb'fin.toFinset with hft
  have hmem : ∀ k, k ∈ ft ↔ k ∈ b' := fun k => hb'fin.mem_toFinset
  set L := ft.toList.map (fun k => (k - η, k + η)) with hL
  set G := ⋃ p ∈ L, Icc p.1 p.2 with hG
  have hLmem : ∀ p : ℝ × ℝ, p ∈ L ↔ ∃ k ∈ b', (k - η, k + η) = p := by
    intro p
    rw [hL, List.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, (hmem k).mp (Finset.mem_toList.mp hk), rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, Finset.mem_toList.mpr ((hmem k).mpr hk), rfl⟩
  obtain ⟨ivs, hivs⟩ := exists_isIntervalUnion_biUnion L
  refine ⟨G, ivs, hivs, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hkb', hxk⟩ := Set.mem_iUnion₂.mp (hcov hx)
    rw [hG, Set.mem_iUnion₂]
    refine ⟨(k - η, k + η), (hLmem _).mpr ⟨k, hkb', rfl⟩, ?_⟩
    simp only [mem_Ioo] at hxk; exact ⟨le_of_lt hxk.1, le_of_lt hxk.2⟩
  · intro x hx
    rw [hG, Set.mem_iUnion₂] at hx
    obtain ⟨q, hqL, hxq⟩ := hx
    obtain ⟨k, hkb', rfl⟩ := (hLmem q).mp hqL
    simp only [mem_Icc] at hxq
    rw [Set.mem_add]
    exact ⟨k, hb'K hkb', x - k,
      by simp only [mem_Icc]; constructor <;> [linarith [hxq.1]; linarith [hxq.2]], by ring⟩

end ProductFree
