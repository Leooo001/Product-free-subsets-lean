import RequestProject.Section4FirstGap

/-!
# Section 4: pushing the maximizing interval to the left

This file formalizes the next lemma after the first forced gap: under the setup of the
contradiction argument, the right endpoint `b` of the discrepancy-maximizing interval lies
strictly to the left of `x`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
A difference-set portion and the corresponding portion of a sum-free set pack disjointly
inside their common ambient interval.
-/
lemma diff_mass_add_mass_le_length (hA : MeasurableSet A) (hsf : IsSumFree A)
    {p q : ℝ} (hpq : p ≤ q) :
    (volume ((A - A) ∩ Icc p q)).toReal + (volume (A ∩ Icc p q)).toReal ≤ q - p := by
  rw [ ← ENNReal.toReal_add ];
  · rw [ ← MeasureTheory.measure_union ];
    · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| Set.union_subset ( Set.inter_subset_right ) ( Set.inter_subset_right ) ) _;
      · norm_num;
      · norm_num [ hpq ];
    · simp +contextual [ Set.disjoint_left, Set.mem_sub ];
      rintro _ x hx y hy rfl _ _; exact fun h => hsf hy h ( by aesop ) ;
    · exact hA.inter measurableSet_Icc;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide ) );
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide ) )

/-
If `1` is the least point of `A`, its cumulative mass at `1` vanishes.
-/
lemma cum_one_eq_zero_of_isLeast (hmin : IsLeast A 1) : cum A 1 = 0 := by
  unfold cum;
  rw [ show A ∩ Icc 0 1 = { 1 } from ?_ ] ; norm_num;
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨ ⟨ hmin.1, by norm_num ⟩, fun x hx => le_antisymm hx.2.2 ( hmin.2 hx.1 ) ⟩

/-
A convenient consequence of the one-Lipschitz property of cumulative mass.
-/
lemma cum_le_cum_add_sub {u v : ℝ} (huv : u ≤ v) :
    cum A v ≤ cum A u + (v - u) := by
  -- Apply the Lipschitz condition with constant 1.
  have h_lip : |cum A u - cum A v| ≤ |u - v| := by
    convert lipschitzWith_one_cum A |> fun h => h.dist_le_mul u v using 1 ; norm_num;
    rfl;
  cases abs_cases ( cum A u - cum A v ) <;> cases abs_cases ( u - v ) <;> linarith

/-
The failure inequality is impossible when `x < 2` and `1` is the least point of a
sum-free set.
-/
lemma not_key_fail_of_lt_two (hA : MeasurableSet A) (hsf : IsSumFree A)
    (hmin : IsLeast A 1) {x : ℝ} (hx : 1 ≤ x) (hx2 : x < 2) :
    cum A (x - 1) + cum A x + cum A (x + 1) ≤ x := by
  -- Since x-1<1, cum A (x-1)=0 by cum_eq_zero_of_le with A⊆Ici 1.
  have h_cum_x_minus_1 : cum A (x - 1) = 0 := by
    -- Since $A$ is closed and $1$ is the least point, $A \cap Iic (x - 1) = \emptyset$.
    have h_empty : A ∩ Iic (x - 1) = ∅ := by
      exact Set.eq_empty_of_forall_notMem fun y hy => by linarith [ hy.1, hy.2.out, hmin.2 hy.1 ] ;
    -- Since the volume of the empty set is zero, we have cum A (x - 1) = 0.
    unfold cum
    rw [ show A ∩ Icc 0 ( x - 1 ) = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; intro y hy; exact h_empty.subset ⟨ hy.1, hy.2.2 ⟩ ]
    norm_num
  -- By cum_le_cum_add_sub from 1 to x and cum A 1=0, cum A x≤x-1.
  have h_cum_x : cum A x ≤ x - 1 := by
    convert cum_le_cum_add_sub ( show 1 ≤ x by linarith ) using 1 ; norm_num [ cum_one_eq_zero_of_isLeast hmin ];
  have h_cum_x_plus_1_diff : cum A (x + 1) - cum A 1 ≤ (volume (A ∩ Icc 1 (x + 1))).toReal := by
    convert cum_sub_cum_eq_mass_Icc ( show 0 ≤ 1 by norm_num ) ( show 1 ≤ x + 1 by linarith ) |> le_of_eq;
  linarith [ cum_one_eq_zero_of_isLeast hmin, sumFree_mass_Icc_le_one hA hsf ( hmin.1 ) ( by linarith : x + 1 - 1 ≤ 2 ) ]

/-
The main argument once the alleged right endpoint is at least `2`.
-/
lemma maximizing_right_lt_x_of_two_le (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x : ℝ} (hab : a < b) (hbtop : b ≤ x + 1)
    (hb2 : 2 ≤ b) (hbx : x ≤ b)
    (hI : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion (A ∩ Icc 1 (b - 1)) ivs) :
    cum A (x - 1) + cum A x + cum A (x + 1) ≤ x := by
  -- Apply mzero at z=b-1: hAnonneg from hmin.2; z≤x+1 by hbx/hbtop; endpoint alternative b-(b-1)=1∈A. Obtain mMinus=0.
  have h_mZero : mMinus A (b - 1) = 0 := by
    apply mzero;
    all_goals norm_cast;
    · exact fun x hx => le_trans zero_le_one ( hmin.2 hx );
    · linarith;
    · norm_num [ hmin.1 ];
  -- Apply minterv_diff to restriction B using hI.2.
  have h_minterv_diff : 2 * (volume (A ∩ Icc 1 (b - 1))).toReal ≤ (volume ((A - A) ∩ Icc 1 (b - 1))).toReal := by
    convert minterv_diff hA hAfin hab hI.2 hB _ using 1;
    · norm_num [ h_mZero ];
    · refine' le_trans _ hmax;
      apply disc_mono;
      · exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
  -- Combine diff_mass_add_mass_le_length to get 3 massB≤b-2.
  have h_diff_mass_add_mass : (volume ((A - A) ∩ Icc 1 (b - 1))).toReal + (volume (A ∩ Icc 1 (b - 1))).toReal ≤ (b - 1) - 1 := by
    convert diff_mass_add_mass_le_length ( hA.measurableSet ) hsf ( by linarith : ( 1 : ℝ ) ≤ b - 1 ) using 1;
  -- Convert massB=cum(b-1) using cumulative increment and cum1=0.
  have h_cum_b_minus_1 : (volume (A ∩ Icc 1 (b - 1))).toReal = cum A (b - 1) - cum A 1 := by
    rw [ cum_sub_cum_eq_mass_Icc ] <;> norm_num [ hmin.1 ];
    linarith
  have h_cum_1 : cum A 1 = 0 := by
    convert cum_one_eq_zero_of_isLeast hmin using 1
  simp_all +decide [ cum ];
  -- Mass on [b-1,x+1]≤1 by sumFree_mass_Icc_le_one because length x-b+2≤2 (hbx); convert to cum(x+1)-cum(b-1)≤1.
  have h_mass_b_minus_1_x_plus_1 : (volume (A ∩ Icc (b - 1) (x + 1))).toReal ≤ 1 := by
    apply sumFree_mass_Icc_le_one;
    · exact hA.measurableSet;
    · assumption;
    · exact hmin.1;
    · linarith
  have h_cum_x_plus_1 : (volume (A ∩ Icc 0 (x + 1))).toReal ≤ (volume (A ∩ Icc 0 (b - 1))).toReal + 1 := by
    have h_cum_x_plus_1 : (volume (A ∩ Icc 0 (x + 1))).toReal ≤ (volume (A ∩ Icc 0 (b - 1))).toReal + (volume (A ∩ Icc (b - 1) (x + 1))).toReal := by
      rw [ ← ENNReal.toReal_add ];
      · gcongr;
        · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ), lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) ⟩ );
        · refine' le_trans _ ( MeasureTheory.measure_union_le _ _ );
          exact MeasureTheory.measure_mono fun x hx => by cases le_total x ( b - 1 ) <;> aesop;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
    linarith
  have h_cum_x : (volume (A ∩ Icc 0 x)).toReal ≤ (volume (A ∩ Icc 0 (b - 1))).toReal + (x - (b - 1)) := by
    convert cum_le_cum_add_sub ( show b - 1 ≤ x by linarith ) using 1
  have h_cum_x_minus_1 : (volume (A ∩ Icc 0 (x - 1))).toReal ≤ (volume (A ∩ Icc 0 (b - 1))).toReal := by
    gcongr;
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) )
  linarith

/-
The discrepancy-maximizing interval cannot reach `x`.  This is the paper's inequality
`y > 1 + s`, expressed in its equivalent form `b < x`.

The interval-union hypothesis is required only for the restriction to which `minterv_diff`
is applied.
-/
lemma maximizing_right_lt_x (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x : ℝ} (hx : 1 ≤ x) (hab : a < b) (hbtop : b ≤ x + 1)
    (hI : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion (A ∩ Icc 1 (b - 1)) ivs)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    b < x := by
  by_cases hb2 : 2 ≤ b;
  · exact not_le.mp fun h => hfail.not_ge <| by linarith [ maximizing_right_lt_x_of_two_le hA hAfin hsf hmin hab hbtop hb2 h hI hmax hB ] ;
  · contrapose! hfail;
    apply not_key_fail_of_lt_two hA.measurableSet hsf hmin hx (by linarith)

/-- Rephrasing `maximizing_right_lt_x` in the variables `s = b-a` and `y=x+1-a`
used in the paper. -/
lemma y_gt_one_add_s (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x y s : ℝ} (hx : 1 ≤ x) (hab : a < b) (hbtop : b ≤ x + 1)
    (hs : s = b - a) (hy : y = x + 1 - a)
    (hI : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion (A ∩ Icc 1 (b - 1)) ivs)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    1 + s < y := by
  have := maximizing_right_lt_x hA hAfin hsf hmin hx hab hbtop hI hmax hB hfail
  linarith

end ProductFree