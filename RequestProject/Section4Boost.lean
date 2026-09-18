import RequestProject.Section4PushLeft

/-!
# Section 4: a three-piece difference-set boost

This file formalizes the geometric core of the paper's Lemma `another boost`: two
applications of `minterv_diff`, separated by a translated portion of the maximizing
interval, give a strengthened lower bound for a difference set.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
Three almost-disjoint measurable subsets of a finite-measure ambient set have total
real measure at most the ambient measure.
-/
lemma measure_le_of_three_aedisjoint {S U V W : Set ℝ}
    (hV : MeasurableSet V) (hW : MeasurableSet W)
    (hUS : U ⊆ S) (hVS : V ⊆ S) (hWS : W ⊆ S)
    (hUV : AEDisjoint volume U V) (hUW : AEDisjoint volume U W)
    (hVW : AEDisjoint volume V W) (hSfin : volume S ≠ ⊤) :
    (volume U).toReal + (volume V).toReal + (volume W).toReal ≤
      (volume S).toReal := by
  refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show U ∪ ( V ∪ W ) ⊆ S from by aesop );
  · rw [ MeasureTheory.measure_union₀, MeasureTheory.measure_union₀ ];
    · rw [ ← add_assoc, ENNReal.toReal_add, ENNReal.toReal_add ];
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hUS ) ( lt_top_iff_ne_top.mpr hSfin ) );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hVS ) ( lt_top_iff_ne_top.mpr hSfin ) );
      · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ lt_of_le_of_lt ( MeasureTheory.measure_mono hUS ) ( lt_top_iff_ne_top.mpr hSfin ), lt_of_le_of_lt ( MeasureTheory.measure_mono hVS ) ( lt_top_iff_ne_top.mpr hSfin ) ⟩ );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hWS ) ( lt_top_iff_ne_top.mpr hSfin ) );
    · exact hW.nullMeasurableSet;
    · assumption;
    · exact MeasurableSet.nullMeasurableSet ( hV.union hW );
    · exact AEDisjoint.union_right hUV hUW;
  · assumption

/-
Three compact pieces that occupy consecutive intervals pack into the ambient interval.
-/
lemma compact_three_piece_packing {S U V W : Set ℝ} {l p q r : ℝ}
    (hU : IsCompact U) (hV : IsCompact V) (hW : IsCompact W)
    (hUS : U ⊆ S) (hVS : V ⊆ S) (hWS : W ⊆ S)
    (hUl : U ⊆ Icc l p) (hVl : V ⊆ Icc p q) (hWl : W ⊆ Icc q r)
    (hlp : l ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) :
    (volume U).toReal + (volume V).toReal + (volume W).toReal ≤
      (volume (S ∩ Icc l r)).toReal := by
  refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono _ );
  any_goals exact U ∪ V ∪ W;
  · rw [ MeasureTheory.measure_union₀, MeasureTheory.measure_union₀ ];
    · rw [ ENNReal.toReal_add, ENNReal.toReal_add ] <;> norm_num;
      · exact hU.measure_lt_top.ne;
      · exact ne_of_lt ( hV.measure_lt_top );
      · exact ⟨ hU.measure_lt_top.ne, hV.measure_lt_top.ne ⟩;
      · exact ne_of_lt ( hW.measure_lt_top );
    · exact hV.measurableSet.nullMeasurableSet;
    · exact MeasureTheory.measure_mono_null ( fun x hx => by cases' hx with hxU hxV; exact Set.mem_singleton_iff.mpr <| le_antisymm ( hUl hxU |>.2 ) ( hVl hxV |>.1 ) ) ( MeasureTheory.measure_singleton p );
    · exact hW.measurableSet.nullMeasurableSet;
    · refine' MeasureTheory.measure_mono_null _ _;
      exact { p, q };
      · grind +qlia;
      · rw [ Set.insert_eq, MeasureTheory.measure_union_null ] <;> norm_num;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show S ∩ Icc l r ⊆ Icc l r from fun x hx => hx.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) );
  · grind

/-
Translation to the right by subtraction of a constant preserves compactness.
-/
lemma isCompact_image_sub_const {E : Set ℝ} (hE : IsCompact E) (c : ℝ) :
    IsCompact ((fun z => z - c) '' E) := by
  exact hE.image ( continuous_sub_right c )

/-
Translation to the right by subtraction of a constant preserves Lebesgue measure.
-/
lemma volume_image_sub_const (E : Set ℝ) (c : ℝ) :
    volume ((fun z => z - c) '' E) = volume E := by
  rw [ show ( fun z => z - c ) '' E = ( fun z => -c + z ) '' E by ext; simp +decide [ sub_eq_neg_add ] ];
  rw [ Set.image_add_left, MeasureTheory.measure_preimage_add ]

/-
The three-piece packing at the heart of Lemma `another boost`.

The first and third terms come from `minterv_diff` on `[1,c]` and `[c+s,d]`.
The middle term is the translate `(A ∩ [a,b-mMinus A c]) - c`.  The assumptions
ensure that their three ambient intervals are consecutive and all lie in
`[b-d,b-1]`.
-/
lemma another_boost_packing (hA : IsClosed A) (hAcompact : IsCompact A)
    (hAfin : volume A ≠ ⊤)
    {a b c d s : ℝ} (hab : a < b) (hs : s = b - a)
    (hI : IsRightBalanced A a b)
    (hcA : c ∈ A) (hc : 1 ≤ c) (hcd : c + s ≤ d)
    (hmle : mMinus A c ≤ s) (hmd : mMinus A d = 0)
    {ivs₁ ivs₂ : List (ℝ × ℝ)}
    (hB₁ : IsIntervalUnion (A ∩ Icc 1 c) ivs₁)
    (hB₂ : IsIntervalUnion (A ∩ Icc (c + s) d) ivs₂)
    (hdisc₁ : disc (A ∩ Icc 1 c) ≤ discOn A a b)
    (hdisc₂ : disc (A ∩ Icc (c + s) d) ≤ discOn A a b) :
    2 * (volume (A ∩ Icc 1 c)).toReal
        + (volume (A ∩ Icc a (b - mMinus A c))).toReal
        + 2 * (volume (A ∩ Icc (c + s) d)).toReal
      ≤ (volume ((A - A) ∩ Icc (b - d) (b - 1))).toReal := by
  obtain ⟨U, V, W, hU, hV, hW, hUV, hUW, hVW, hS⟩ : ∃ U V W : Set ℝ, U = (A - A) ∩ Icc (b - d) (b - c - s) ∧ V = ((A ∩ Icc a (b - mMinus A c)) - {c}) ∧ W = (A - A) ∩ Icc (b - c - mMinus A c) (b - 1) ∧ IsCompact U ∧ IsCompact V ∧ IsCompact W ∧ U ⊆ (A - A) ∩ Icc (b - d) (b - 1) ∧ V ⊆ (A - A) ∩ Icc (b - d) (b - 1) ∧ W ⊆ (A - A) ∩ Icc (b - d) (b - 1) ∧ AEDisjoint volume U V ∧ AEDisjoint volume U W ∧ AEDisjoint volume V W := by
    refine' ⟨ _, _, _, rfl, rfl, rfl, _, _, _, _, _ ⟩;
    · refine' IsCompact.inter_right _ ( isClosed_Icc );
      simpa only [ sub_eq_add_neg ] using hAcompact.add hAcompact.neg;
    · simp +zetaDelta at *;
      exact IsCompact.image ( hAcompact.inter_right <| isClosed_Icc ) <| continuous_sub_right _;
    · refine' IsCompact.inter_right _ _;
      · simpa only [ sub_eq_add_neg ] using hAcompact.add ( hAcompact.neg );
      · exact isClosed_Icc;
    · exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc_right ( by linarith ) );
    · refine' ⟨ _, _, _, _, _ ⟩;
      · intro x hx; simp_all +decide [ Set.mem_sub, Set.mem_inter_iff ] ;
        rcases hx with ⟨ y, ⟨ hy₁, hy₂, hy₃ ⟩, rfl ⟩ ; exact ⟨ ⟨ y, hy₁, c, hcA, rfl ⟩, by linarith, by linarith [ show mMinus A c ≥ 0 from mMinus_nonneg hAfin c ] ⟩ ;
      · exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc ( by linarith ) le_rfl );
      · refine' MeasureTheory.measure_mono_null _ _;
        exact { x | x = b - c - s };
        · intro x hx; simp_all +decide [ Set.mem_sub, Set.mem_Icc ] ;
          linarith [ hx.2.choose_spec ];
        · norm_num [ Set.setOf_eq_eq_singleton ];
      · refine' MeasureTheory.measure_mono_null _ _;
        exact { b - c - mMinus A c };
        · grind +qlia;
        · norm_num;
      · refine' MeasureTheory.measure_mono_null _ _;
        exact { b - c - mMinus A c };
        · intro x hx; simp_all +decide [ Set.mem_sub, Set.mem_inter_iff ] ;
          linarith [ hx.1.choose_spec ];
        · norm_num;
  have h_volume_U : (volume U).toReal ≥ 2 * (volume (A ∩ Icc (c + s) d)).toReal := by
    have := minterv_diff hA hAfin hab hI hB₂ hdisc₂; simp_all +decide;
    convert this using 3 ; ring
  have h_volume_W : (volume W).toReal ≥ 2 * (volume (A ∩ Icc 1 c)).toReal := by
    have := @minterv_diff A;
    grind
  have h_volume_V : (volume V).toReal = (volume (A ∩ Icc a (b - mMinus A c))).toReal := by
    rw [ hV, Set.sub_singleton ];
    rw [ volume_image_sub_const ];
  have := measure_le_of_three_aedisjoint ( show MeasurableSet V from hUW.measurableSet ) ( show MeasurableSet W from hVW.measurableSet ) hS.1 hS.2.1 hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2.1 hS.2.2.2.2.2 ( show volume ( ( A - A ) ∩ Icc ( b - d ) ( b - 1 ) ) ≠ ⊤ from ?_ );
  · linarith;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) )

/-
Paper-form consequence of `another_boost_packing`: the two outer masses telescope to
`2 F(d)`, with the mass of `[c,c+s]` subtracted twice.
-/
lemma another_boost (hA : IsClosed A) (hAcompact : IsCompact A)
    (hAfin : volume A ≠ ⊤) (hmin : IsLeast A 1)
    {a b c d s : ℝ} (hab : a < b) (hs : s = b - a)
    (hI : IsRightBalanced A a b)
    (hcA : c ∈ A) (hc : 1 ≤ c) (hcd : c + s ≤ d)
    (hmle : mMinus A c ≤ s) (hmd : mMinus A d = 0)
    {ivs₁ ivs₂ : List (ℝ × ℝ)}
    (hB₁ : IsIntervalUnion (A ∩ Icc 1 c) ivs₁)
    (hB₂ : IsIntervalUnion (A ∩ Icc (c + s) d) ivs₂)
    (hdisc₁ : disc (A ∩ Icc 1 c) ≤ discOn A a b)
    (hdisc₂ : disc (A ∩ Icc (c + s) d) ≤ discOn A a b) :
    2 * cum A d + (volume (A ∩ Icc a (b - mMinus A c))).toReal
        - 2 * (volume (A ∩ Icc c (c + s))).toReal
      ≤ (volume ((A - A) ∩ Icc (b - d) (b - 1))).toReal := by
  have h_volume_Icc : (volume (A ∩ Icc 1 c)).toReal = cum A c ∧ (volume (A ∩ Icc c (c + s))).toReal = cum A (c + s) - cum A c ∧ (volume (A ∩ Icc (c + s) d)).toReal = cum A d - cum A (c + s) := by
    apply And.intro;
    · have h_volume_Icc : (volume (A ∩ Icc 1 c)).toReal = cum A c - cum A 1 := by
        rw [ cum_sub_cum_eq_mass_Icc ] <;> norm_num [ hc ];
      rw [ h_volume_Icc, cum_one_eq_zero_of_isLeast hmin, sub_zero ];
    · constructor <;> rw [ cum_sub_cum_eq_mass_Icc ] <;> linarith;
  linarith [ another_boost_packing hA hAcompact hAfin hab hs hI hcA hc hcd hmle hmd hB₁ hB₂ hdisc₁ hdisc₂ ]

end ProductFree