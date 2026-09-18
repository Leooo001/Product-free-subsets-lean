import RequestProject.Section4LongGap

/-!
# Section 4: the length of the first gap

This file formalizes the geometric conclusion in Lemma `y - 1 gap lem`.  Once the
measure argument has shown that more than `1-s` of `[x,x+1]` is left uncovered
by the two translates `u+[a,b]` and `v+[a,b]`, their endpoint positions force
`v-u ≥ 1`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

/-
Removing two measurable exceptional sets can reduce the real measure of a
finite-measure set by at most the sum of their measures.
-/
lemma measure_diff_union_lower {P U V : Set ℝ}
    (hP : MeasurableSet P) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hPfin : volume P ≠ ⊤) (hUfin : volume U ≠ ⊤) (hVfin : volume V ≠ ⊤) :
    (volume P).toReal - (volume U).toReal - (volume V).toReal ≤
      (volume (P \ (U ∪ V))).toReal := by
  -- By subadditivity, the measure of $P \cap (U \cup V)$ is at most the sum of the measures of $P \cap U$ and $P \cap V$.
  have h_subadd : (volume (P ∩ (U ∪ V))).toReal ≤ (volume (P ∩ U)).toReal + (volume (P ∩ V)).toReal := by
    rw [ ← ENNReal.toReal_add ];
    · gcongr;
      · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hPfin ), lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hPfin ) ⟩ );
      · exact le_trans ( MeasureTheory.measure_mono ( by aesop_cat ) ) ( MeasureTheory.measure_union_le _ _ );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hPfin ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hPfin ) );
  -- By the properties of measures, we have:
  have h_measure : (volume P).toReal = (volume (P ∩ (U ∪ V))).toReal + (volume (P \ (U ∪ V))).toReal := by
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_inter_add_diff P ( hU.union hV ) ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hPfin ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show P \ ( U ∪ V ) ⊆ P from fun x hx => hx.1 ) ) ( lt_top_iff_ne_top.mpr hPfin ) );
  linarith [ show ( volume ( P ∩ U ) |> ENNReal.toReal ) ≤ ( volume U |> ENNReal.toReal ) from ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ), show ( volume ( P ∩ V ) |> ENNReal.toReal ) ≤ ( volume V |> ENNReal.toReal ) from ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ]

/-
Filling each of two translates of `A ∩ [a,b]` up to the whole translated
interval costs at most the total measure of the two translated holes.  Thus the
mass surplus in `[x,x+1]` gives the uncovered-length inequality used by the
geometric argument.
-/
lemma uncovered_translates_gt_one_sub_length
    {A : Set ℝ} (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u v x s t : ℝ} (hab : a ≤ b) (hs : s = b - a)
    (ht : t = discOn A a b) (huA : u ∈ A) (hvA : v ∈ A)
    (hmass : 1 - t < (volume (A ∩ Icc x (x + 1))).toReal) :
    1 - s <
      (volume (Icc x (x + 1) \ (Icc (a + u) (b + u) ∪ Icc (a + v) (b + v)))).toReal := by
  have hP_minus_Hu_Hv : (volume ((A ∩ Icc x (x + 1)) \ ((fun z => z + u) '' (Icc a b \ A) ∪ (fun z => z + v) '' (Icc a b \ A)))).toReal ≥ (volume (A ∩ Icc x (x + 1))).toReal - (volume ((fun z => z + u) '' (Icc a b \ A))).toReal - (volume ((fun z => z + v) '' (Icc a b \ A))).toReal := by
    apply_rules [ measure_diff_union_lower ];
    · exact hA.inter measurableSet_Icc;
    · simp +decide [ Set.image_add_right ];
      exact measurableSet_Icc.diff ( hA.preimage ( measurable_id.add_const _ ) );
    · rw [ Set.image_add_right ];
      exact measurableSet_Icc.diff hA |> MeasurableSet.preimage <| measurable_id.add_const _;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) );
    · rw [Set.image_add_right, MeasureTheory.measure_preimage_add_right];
      exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (Set.diff_subset)) (by simp +decide [Real.volume_Icc]));
    · rw [Set.image_add_right, MeasureTheory.measure_preimage_add_right];
      exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (Set.diff_subset)) (by simp +decide [Real.volume_Icc]));
  have hP_minus_Hu_Hv_subset : (A ∩ Icc x (x + 1)) \ ((fun z => z + u) '' (Icc a b \ A) ∪ (fun z => z + v) '' (Icc a b \ A)) ⊆ Icc x (x + 1) \ (Icc (a + u) (b + u) ∪ Icc (a + v) (b + v)) := by
    simp +contextual [ Set.subset_def ];
    intro y hy hyx hyx' hyu hyv; constructor <;> intro hyu' <;> contrapose! hyu;
    · exact ⟨ hyu', hyu, fun h => hsf ( show y + -u ∈ A from h ) huA ( by ring_nf; aesop ) ⟩;
    · have := hsf ( hyv hyu' hyu ) hvA; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
  have hP_minus_Hu_Hv_subset : (volume ((A ∩ Icc x (x + 1)) \ ((fun z => z + u) '' (Icc a b \ A) ∪ (fun z => z + v) '' (Icc a b \ A)))).toReal ≤ (volume (Icc x (x + 1) \ (Icc (a + u) (b + u) ∪ Icc (a + v) (b + v)))).toReal := by
    apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show Icc x ( x + 1 ) \ ( Icc ( a + u ) ( b + u ) ∪ Icc ( a + v ) ( b + v ) ) ⊆ Icc x ( x + 1 ) from fun y hy => hy.1 ) ) ( by norm_num ) );
  have h_volume_image : (volume ((fun z => z + u) '' (Icc a b \ A))).toReal = (volume (Icc a b \ A)).toReal ∧ (volume ((fun z => z + v) '' (Icc a b \ A))).toReal = (volume (Icc a b \ A)).toReal := by
    constructor <;> rw [ Set.image_add_right ]; all_goals rw [ MeasureTheory.measure_preimage_add_right ];
  have h_volume_Icc : (volume (Icc a b \ A)).toReal = (b - a) - (volume (A ∩ Icc a b)).toReal := by
    rw [ show Icc a b \ A = Icc a b \ ( A ∩ Icc a b ) by ext; aesop, MeasureTheory.measure_diff ] <;> norm_num [ hA, hab ];
    · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ hab ];
      exact le_trans ( MeasureTheory.measure_mono ( show A ∩ Icc a b ⊆ Icc a b from fun x hx => hx.2 ) ) ( by simp +decide [ hab ] );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hab ] ) );
  unfold discOn at * ; linarith

/-
The one-dimensional geometric core of Lemma `y - 1 gap lem`.

The first translated interval crosses `x`, the second crosses `x+1`, and their
uncovered part inside `[x,x+1]` has measure greater than `1-s`.  Therefore the
gap between their inner endpoints has length greater than `1-s`, forcing the
translation parameters to differ by at least one.
-/
lemma long_gap_of_uncovered_translates {a b u v x s : ℝ}
    (hs : s = b - a) (hs1 : s ≤ 1)
    (hau : a + u < x) (hxv : x + 1 < b + v)
    (huncovered : 1 - s <
      (volume (Icc x (x + 1) \ (Icc (a + u) (b + u) ∪ Icc (a + v) (b + v)))).toReal) :
    1 ≤ v - u := by
  contrapose! huncovered;
  refine' le_trans ( ENNReal.toReal_mono _ _ ) _;
  exact ENNReal.ofReal ( Max.max ( a + v - ( b + u ) ) 0 );
  · norm_num;
  · refine' le_trans ( MeasureTheory.measure_mono _ ) _;
    exact Set.Ioo ( b + u ) ( a + v );
    · grind;
    · simp +decide [ Real.volume_Ioo ];
  · cases max_cases ( a + v - ( b + u ) ) 0 <;> simp +decide [ * ] <;> linarith

/-- Lemma `y - 1 gap lem` in a reusable form.  Sum-freeness and the mass
surplus show that the two full translated intervals leave too much of the unit
interval uncovered; their endpoint positions then force a gap of length at
least one between the translating points. -/
lemma first_gap_length_estimate
    {A : Set ℝ} (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u v x s t : ℝ} (hab : a ≤ b) (hs : s = b - a) (hs1 : s ≤ 1)
    (ht : t = discOn A a b) (huA : u ∈ A) (hvA : v ∈ A)
    (hmass : 1 - t < (volume (A ∩ Icc x (x + 1))).toReal)
    (hau : a + u < x) (hxv : x + 1 < b + v) :
    1 ≤ v - u := by
  apply long_gap_of_uncovered_translates hs hs1 hau hxv
  exact uncovered_translates_gt_one_sub_length hA hsf hab hs ht huA hvA hmass

end ProductFree