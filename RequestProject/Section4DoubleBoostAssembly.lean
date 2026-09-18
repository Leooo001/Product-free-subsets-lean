import RequestProject.Section4Boost
import RequestProject.Section4MInterv
import RequestProject.Section4ContradictionAux

/-!
# Section 4: a five-piece packing helper for the double boost

This file provides `compact_five_piece_packing`, the five-interval analogue of
`compact_three_piece_packing`, used to assemble the paper's "double boost" difference-set
estimate.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

/-- Five compact pieces occupying consecutive intervals pack into the ambient interval. -/
lemma compact_five_piece_packing {S U₁ U₂ U₃ U₄ U₅ : Set ℝ} {e₁ e₂ e₃ e₄ e₅ e₆ : ℝ}
    (hU₁ : IsCompact U₁) (hU₂ : IsCompact U₂) (hU₃ : IsCompact U₃)
    (hU₄ : IsCompact U₄) (hU₅ : IsCompact U₅)
    (hS₁ : U₁ ⊆ S) (hS₂ : U₂ ⊆ S) (hS₃ : U₃ ⊆ S) (hS₄ : U₄ ⊆ S) (hS₅ : U₅ ⊆ S)
    (hI₁ : U₁ ⊆ Icc e₁ e₂) (hI₂ : U₂ ⊆ Icc e₂ e₃) (hI₃ : U₃ ⊆ Icc e₃ e₄)
    (hI₄ : U₄ ⊆ Icc e₄ e₅) (hI₅ : U₅ ⊆ Icc e₅ e₆)
    (h12 : e₁ ≤ e₂) (h23 : e₂ ≤ e₃) (h34 : e₃ ≤ e₄) (h45 : e₄ ≤ e₅) (h56 : e₅ ≤ e₆) :
    (volume U₁).toReal + (volume U₂).toReal + (volume U₃).toReal
      + (volume U₄).toReal + (volume U₅).toReal ≤ (volume (S ∩ Icc e₁ e₆)).toReal := by
  -- Right-associated partial unions and their ambient intervals.
  -- Measurability.
  have m₁ := hU₁.measurableSet
  have m₂ := hU₂.measurableSet
  have m₃ := hU₃.measurableSet
  have m₄ := hU₄.measurableSet
  have m₅ := hU₅.measurableSet
  -- Finiteness (toReal) helpers: everything lies in `Icc e₁ e₆`.
  have hfinI : volume (Icc e₁ e₆) ≠ ⊤ := by simp [Real.volume_Icc]
  have hsubT4 : U₄ ∪ U₅ ⊆ Icc e₄ e₆ :=
    Set.union_subset (hI₄.trans (Set.Icc_subset_Icc le_rfl (by linarith)))
      (hI₅.trans (Set.Icc_subset_Icc (by linarith) le_rfl))
  have hsubT3 : U₃ ∪ (U₄ ∪ U₅) ⊆ Icc e₃ e₆ :=
    Set.union_subset (hI₃.trans (Set.Icc_subset_Icc le_rfl (by linarith)))
      (hsubT4.trans (Set.Icc_subset_Icc (by linarith) le_rfl))
  have hsubT2 : U₂ ∪ (U₃ ∪ (U₄ ∪ U₅)) ⊆ Icc e₂ e₆ :=
    Set.union_subset (hI₂.trans (Set.Icc_subset_Icc le_rfl (by linarith)))
      (hsubT3.trans (Set.Icc_subset_Icc (by linarith) le_rfl))
  -- Null overlaps.
  have nmT2 : NullMeasurableSet (U₂ ∪ (U₃ ∪ (U₄ ∪ U₅))) :=
    ((m₂.union (m₃.union (m₄.union m₅)))).nullMeasurableSet
  have nmT3 : NullMeasurableSet (U₃ ∪ (U₄ ∪ U₅)) :=
    (m₃.union (m₄.union m₅)).nullMeasurableSet
  have nmT4 : NullMeasurableSet (U₄ ∪ U₅) := (m₄.union m₅).nullMeasurableSet
  have aed4 : AEDisjoint volume U₄ U₅ := by
    refine measure_mono_null (fun z hz => ?_) (measure_singleton e₅)
    have : z ∈ Icc e₄ e₅ ∩ Icc e₅ e₆ := ⟨hI₄ hz.1, hI₅ hz.2⟩
    simp only [mem_singleton_iff]; rw [mem_inter_iff, mem_Icc, mem_Icc] at this; linarith [this.1.2, this.2.1]
  have aed3 : AEDisjoint volume U₃ (U₄ ∪ U₅) := by
    refine measure_mono_null (fun z hz => ?_) (measure_singleton e₄)
    have hz3 := hI₃ hz.1
    have hzr := hsubT4 hz.2
    simp only [mem_singleton_iff]; rw [mem_Icc] at hz3 hzr; linarith [hz3.2, hzr.1]
  have aed2 : AEDisjoint volume U₂ (U₃ ∪ (U₄ ∪ U₅)) := by
    refine measure_mono_null (fun z hz => ?_) (measure_singleton e₃)
    have hz2 := hI₂ hz.1
    have hzr := hsubT3 hz.2
    simp only [mem_singleton_iff]; rw [mem_Icc] at hz2 hzr; linarith [hz2.2, hzr.1]
  have aed1 : AEDisjoint volume U₁ (U₂ ∪ (U₃ ∪ (U₄ ∪ U₅))) := by
    refine measure_mono_null (fun z hz => ?_) (measure_singleton e₂)
    have hz1 := hI₁ hz.1
    have hzr := hsubT2 hz.2
    simp only [mem_singleton_iff]; rw [mem_Icc] at hz1 hzr; linarith [hz1.2, hzr.1]
  -- The union lies in the ambient set.
  have hunion_sub : U₁ ∪ (U₂ ∪ (U₃ ∪ (U₄ ∪ U₅))) ⊆ S ∩ Icc e₁ e₆ := by
    have hSsub : U₁ ∪ (U₂ ∪ (U₃ ∪ (U₄ ∪ U₅))) ⊆ S :=
      Set.union_subset hS₁ (Set.union_subset hS₂ (Set.union_subset hS₃
        (Set.union_subset hS₄ hS₅)))
    have hIsub : U₁ ∪ (U₂ ∪ (U₃ ∪ (U₄ ∪ U₅))) ⊆ Icc e₁ e₆ :=
      Set.union_subset (hI₁.trans (Set.Icc_subset_Icc le_rfl (by linarith)))
        (hsubT2.trans (Set.Icc_subset_Icc (by linarith) le_rfl))
    exact fun z hz => ⟨hSsub hz, hIsub hz⟩
  -- Measure additivity across the four null overlaps.
  have hmeas_eq : volume (U₁ ∪ (U₂ ∪ (U₃ ∪ (U₄ ∪ U₅)))) =
      volume U₁ + volume U₂ + volume U₃ + volume U₄ + volume U₅ := by
    rw [measure_union₀ nmT2 aed1, measure_union₀ nmT3 aed2, measure_union₀ nmT4 aed3,
      measure_union₀ m₅.nullMeasurableSet aed4]
    ring
  have hfin : volume (S ∩ Icc e₁ e₆) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      (lt_top_iff_ne_top.mpr hfinI))
  have hle : volume (U₁ ∪ (U₂ ∪ (U₃ ∪ (U₄ ∪ U₅)))) ≤ volume (S ∩ Icc e₁ e₆) :=
    measure_mono hunion_sub
  rw [hmeas_eq] at hle
  have h1 : volume U₁ ≠ ⊤ := hU₁.measure_lt_top.ne
  have h2 : volume U₂ ≠ ⊤ := hU₂.measure_lt_top.ne
  have h3 : volume U₃ ≠ ⊤ := hU₃.measure_lt_top.ne
  have h4 : volume U₄ ≠ ⊤ := hU₄.measure_lt_top.ne
  have h5 : volume U₅ ≠ ⊤ := hU₅.measure_lt_top.ne
  have hmono := ENNReal.toReal_mono hfin hle
  rwa [ENNReal.toReal_add (by simp [h1, h2, h3, h4]) h5,
    ENNReal.toReal_add (by simp [h1, h2, h3]) h4,
    ENNReal.toReal_add (by simp [h1, h2]) h3,
    ENNReal.toReal_add h1 h2] at hmono

variable {A : Set ℝ}

/-- **The five-piece packing of the paper's `double boost` lemma.**  Given the two extremal
points `u` (around `y-1`) and `u₂` (around `2`) with their gaps and the ordering coming from
`u₂ + s ≤ u` and `u + s ≤ b - 1`, the difference set `(A-A) ∩ [1,b-1]` collects
`2 F(b-1) + |A ∩ [a, b-mᴀ⁻(u)]| + |A ∩ [a, b-mᴀ⁻(u₂)]|`. -/
lemma double_boost_five_piece
    (hIU : IsIntervalUnion A ivs) (hmin : IsLeast A 1)
    {a b s u u₂ : ℝ} (hab : a < b) (hs : s = b - a)
    (hI : IsRightBalanced A a b)
    (huA : u ∈ A) (hu2A : u₂ ∈ A)
    (hu2_ge1 : 1 ≤ u₂)
    (hmb1 : mMinus A (b - 1) = 0)
    (hmu : mMinus A u ≤ s) (hmu2 : mMinus A u₂ ≤ s)
    (hub : u + s ≤ b - 1) (huu2 : u₂ + s ≤ u)
    (hgu : (volume (A ∩ Icc u (u + s))).toReal = 0)
    (hgu2 : (volume (A ∩ Icc u₂ (u₂ + s))).toReal = 0)
    (hdisc1 : disc (A ∩ Icc (u + s) (b - 1)) ≤ discOn A a b)
    (hdisc2 : disc (A ∩ Icc (u₂ + s) u) ≤ discOn A a b)
    (hdisc3 : disc (A ∩ Icc 1 u₂) ≤ discOn A a b) :
    2 * cum A (b - 1) + (volume (A ∩ Icc a (b - mMinus A u))).toReal
        + (volume (A ∩ Icc a (b - mMinus A u₂))).toReal
      ≤ (volume ((A - A) ∩ Icc 1 (b - 1))).toReal := by
  have hAcompact : IsCompact A := hIU.isCompact
  have hAfin : volume A ≠ ⊤ := hAcompact.measure_lt_top.ne
  have hAclosed : IsClosed A := hIU.isClosed
  have hmu_nn : 0 ≤ mMinus A u := mMinus_nonneg hAfin u
  have hmu2_nn : 0 ≤ mMinus A u₂ := mMinus_nonneg hAfin u₂
  have hs0 : 0 < s := by rw [hs]; linarith
  have hu_ge : 1 ≤ u := by linarith
  have hcompactSub : IsCompact (A - A) := by
    simpa only [sub_eq_add_neg] using hAcompact.add hAcompact.neg
  -- Interval-union restrictions.
  obtain ⟨jvs1, hB1⟩ := hIU.inter_Icc_exists (u + s) (b - 1)
  obtain ⟨jvs2, hB2⟩ := hIU.inter_Icc_exists (u₂ + s) u
  obtain ⟨jvs3, hB3⟩ := hIU.inter_Icc_exists 1 u₂
  -- The three `minterv` difference-set bounds, with endpoints normalised.
  have hm1 := minterv_diff hAclosed hAfin hab hI hB1 hdisc1
  have hm2 := minterv_diff hAclosed hAfin hab hI hB2 hdisc2
  have hm3 := minterv_diff hAclosed hAfin hab hI hB3 hdisc3
  rw [hmb1] at hm1
  rw [show b - (b - 1) - 0 = (1 : ℝ) from by ring, show b - (u + s) = b - u - s from by ring]
    at hm1
  rw [show b - (u₂ + s) = b - u₂ - s from by ring] at hm2
  -- Mass identities.
  have hmass1 : (volume (A ∩ Icc (u + s) (b - 1))).toReal = cum A (b - 1) - cum A (u + s) := by
    rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)]
  have hmass2 : (volume (A ∩ Icc (u₂ + s) u)).toReal = cum A u - cum A (u₂ + s) := by
    rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)]
  have hmass3 : (volume (A ∩ Icc 1 u₂)).toReal = cum A u₂ := by
    rw [← cum_sub_cum_eq_mass_Icc (by norm_num) hu2_ge1, cum_one_eq_zero_of_isLeast hmin,
      sub_zero]
  -- Gap equalities `F(u+s)=F(u)` and `F(u₂+s)=F(u₂)`.
  have hgeu : cum A (u + s) = cum A u := by
    have := cum_sub_cum_eq_mass_Icc (A := A) (show (0:ℝ) ≤ u by linarith) (show u ≤ u + s by linarith)
    rw [hgu] at this; linarith
  have hgeu2 : cum A (u₂ + s) = cum A u₂ := by
    have := cum_sub_cum_eq_mass_Icc (A := A) (show (0:ℝ) ≤ u₂ by linarith)
      (show u₂ ≤ u₂ + s by linarith)
    rw [hgu2] at this; linarith
  -- The two translate pieces.
  have ha_eq : a = b - s := by rw [hs]; ring
  have hV2c : IsCompact ((fun z => z - u) '' (A ∩ Icc a (b - mMinus A u))) :=
    isCompact_image_sub_const (hAcompact.inter_right isClosed_Icc) u
  have hV4c : IsCompact ((fun z => z - u₂) '' (A ∩ Icc a (b - mMinus A u₂))) :=
    isCompact_image_sub_const (hAcompact.inter_right isClosed_Icc) u₂
  have hV2vol : (volume ((fun z => z - u) '' (A ∩ Icc a (b - mMinus A u)))).toReal
      = (volume (A ∩ Icc a (b - mMinus A u))).toReal := by rw [volume_image_sub_const]
  have hV4vol : (volume ((fun z => z - u₂) '' (A ∩ Icc a (b - mMinus A u₂)))).toReal
      = (volume (A ∩ Icc a (b - mMinus A u₂))).toReal := by rw [volume_image_sub_const]
  -- Compactness of the three `minterv` pieces.
  have hU1c : IsCompact ((A - A) ∩ Icc 1 (b - u - s)) := hcompactSub.inter_right isClosed_Icc
  have hU3c : IsCompact ((A - A) ∩ Icc (b - u - mMinus A u) (b - u₂ - s)) :=
    hcompactSub.inter_right isClosed_Icc
  have hU5c : IsCompact ((A - A) ∩ Icc (b - u₂ - mMinus A u₂) (b - 1)) :=
    hcompactSub.inter_right isClosed_Icc
  -- Subset facts.
  have hU1S : (A - A) ∩ Icc 1 (b - u - s) ⊆ A - A := Set.inter_subset_left
  have hU3S : (A - A) ∩ Icc (b - u - mMinus A u) (b - u₂ - s) ⊆ A - A := Set.inter_subset_left
  have hU5S : (A - A) ∩ Icc (b - u₂ - mMinus A u₂) (b - 1) ⊆ A - A := Set.inter_subset_left
  have hV2S : (fun z => z - u) '' (A ∩ Icc a (b - mMinus A u)) ⊆ A - A := by
    rintro w ⟨z, hz, rfl⟩; exact Set.sub_mem_sub hz.1 huA
  have hV4S : (fun z => z - u₂) '' (A ∩ Icc a (b - mMinus A u₂)) ⊆ A - A := by
    rintro w ⟨z, hz, rfl⟩; exact Set.sub_mem_sub hz.1 hu2A
  have hU1I : (A - A) ∩ Icc 1 (b - u - s) ⊆ Icc 1 (b - u - s) := Set.inter_subset_right
  have hV2I : (fun z => z - u) '' (A ∩ Icc a (b - mMinus A u))
      ⊆ Icc (b - u - s) (b - u - mMinus A u) := by
    rintro w ⟨z, hz, rfl⟩
    simp only [mem_Icc]
    exact ⟨by linarith [hz.2.1, ha_eq], by linarith [hz.2.2]⟩
  have hU3I : (A - A) ∩ Icc (b - u - mMinus A u) (b - u₂ - s)
      ⊆ Icc (b - u - mMinus A u) (b - u₂ - s) := Set.inter_subset_right
  have hV4I : (fun z => z - u₂) '' (A ∩ Icc a (b - mMinus A u₂))
      ⊆ Icc (b - u₂ - s) (b - u₂ - mMinus A u₂) := by
    rintro w ⟨z, hz, rfl⟩
    simp only [mem_Icc]
    exact ⟨by linarith [hz.2.1, ha_eq], by linarith [hz.2.2]⟩
  have hU5I : (A - A) ∩ Icc (b - u₂ - mMinus A u₂) (b - 1)
      ⊆ Icc (b - u₂ - mMinus A u₂) (b - 1) := Set.inter_subset_right
  -- Apply the five-piece packing.
  have hpack := compact_five_piece_packing hU1c hV2c hU3c hV4c hU5c
    hU1S hV2S hU3S hV4S hU5S hU1I hV2I hU3I hV4I hU5I
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [hV2vol, hV4vol] at hpack
  -- Combine the piece bounds.  `hpack` bounds the sum of the five masses by the ambient
  -- difference-set mass, and the three `minterv` pieces telescope using the gap equalities.
  linarith [hpack, hm1, hm2, hm3, hmass1, hmass2, hmass3, hgeu, hgeu2]

/-- **The `mᴀ⁻(u) ≤ F(u) - F(u₂)` bound.**  If `[u₂,v₂]` is a gap of `A` with
`mᴀ⁻(u₂) ≤ v₂ - u₂` and `u₂ ≤ v₂ ≤ u`, then `mᴀ⁻(u) ≤ F(u) - F(u₂)`.  This is the key
sub-claim of the paper's proof that `mᴀ⁻(u) + mᴀ⁻(u₂) ≤ F(u)`. -/
lemma mMinus_le_cum_sub_of_gap (hAfin : volume A ≠ ⊤)
    {u₂ v₂ u : ℝ} (hu20 : 0 ≤ u₂) (hu2v2 : u₂ ≤ v₂) (hv2u : v₂ ≤ u)
    (hgap : A ∩ Ioo u₂ v₂ = ∅) (hmv : mMinus A u₂ ≤ v₂ - u₂) :
    mMinus A u ≤ cum A u - cum A u₂ := by
  have hMdef : cum A u - cum A u₂ = (volume (A ∩ Icc u₂ u)).toReal :=
    cum_sub_cum_eq_mass_Icc hu20 (le_trans hu2v2 hv2u)
  rw [hMdef]
  refine csSup_le ⟨discOn A u u, u, le_rfl, rfl⟩ ?_
  rintro d ⟨r, hr, rfl⟩
  have hbddM : (volume (A ∩ Icc u₂ u)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp [Real.volume_Icc]))
  rcases le_total u₂ r with hru | hru
  · -- `r ≥ u₂`
    have h1 : (volume (A ∩ Icc r u)).toReal ≤ (volume (A ∩ Icc u₂ u)).toReal :=
      ENNReal.toReal_mono hbddM
        (measure_mono (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc hru le_rfl)))
    have h2 : (volume (A ∩ Icc r u)).toReal ≤ u - r := mass_inter_Icc_le A hr
    unfold discOn; linarith
  · -- `r < u₂`
    have hsub : A ∩ Icc r u ⊆ (A ∩ Icc r u₂) ∪ (A ∩ Icc v₂ u) := by
      rintro z ⟨hzA, hz1, hz2⟩
      by_cases h : u₂ < z
      · by_cases h' : z < v₂
        · have hz : z ∈ A ∩ Ioo u₂ v₂ := ⟨hzA, h, h'⟩
          rw [hgap] at hz; simp at hz
        · exact Or.inr ⟨hzA, not_lt.mp h', hz2⟩
      · exact Or.inl ⟨hzA, hz1, not_lt.mp h⟩
    have hsplit : (volume (A ∩ Icc r u)).toReal
        ≤ (volume (A ∩ Icc r u₂)).toReal + (volume (A ∩ Icc v₂ u)).toReal := by
      have hfin1 : (volume (A ∩ Icc r u₂)) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp [Real.volume_Icc]))
      have hfin2 : (volume (A ∩ Icc v₂ u)) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp [Real.volume_Icc]))
      calc (volume (A ∩ Icc r u)).toReal
            ≤ (volume ((A ∩ Icc r u₂) ∪ (A ∩ Icc v₂ u))).toReal :=
            ENNReal.toReal_mono (by
              refine ne_of_lt (lt_of_le_of_lt (measure_union_le _ _) ?_)
              exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hfin1, lt_of_le_of_ne le_top hfin2⟩)
              (measure_mono hsub)
        _ ≤ (volume (A ∩ Icc r u₂)).toReal + (volume (A ∩ Icc v₂ u)).toReal := by
            rw [← ENNReal.toReal_add hfin1 hfin2]
            exact ENNReal.toReal_mono
              (by exact ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) (measure_union_le _ _)
    have hdr2 : discOn A r u₂ ≤ mMinus A u₂ :=
      le_csSup ⟨disc A, by rintro _ ⟨q, hq, rfl⟩; exact discOn_le_disc hAfin hq⟩
        ⟨r, hru, rfl⟩
    have hdv2 : (volume (A ∩ Icc v₂ u)).toReal ≤ u - v₂ := mass_inter_Icc_le A hv2u
    have hmass_v2u : (volume (A ∩ Icc v₂ u)).toReal ≤ (volume (A ∩ Icc u₂ u)).toReal :=
      ENNReal.toReal_mono hbddM
        (measure_mono (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc hu2v2 le_rfl)))
    unfold discOn at hdr2 ⊢
    linarith [hsplit, hdr2, hdv2, hmv, hmass_v2u]

end ProductFree
