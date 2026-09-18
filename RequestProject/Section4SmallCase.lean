import RequestProject.Section4LongGapEstimate

/-!
# Section 4: the first small-case positional lemma

This file begins the paper's subsection "Pushing the maximizing interval to the
left of `x-1`".  It formalizes Lemma `small case`: while `y < 3+s`, the left
endpoint of the discrepancy-maximizing balanced interval cannot lie before the
first point of `A` following the gap around `y-1`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The maximizing interval cannot straddle both extremal points around a gap of
length at least one.  This is the first geometric step in Lemma `small case`.
-/
lemma balanced_interval_not_straddle_long_gap
    (hA : IsClosed A) {a b u v q s : ℝ}
    (hab : a < b) (hs : s = b - a) (hs1 : s ≤ 1)
    (hbal : IsBalanced A a b) (hdisc : 0 < discOn A a b)
    (huv : 1 ≤ v - u)
    (hu_max : ∀ z ∈ A, z ≤ q → z ≤ u)
    (hv_min : ∀ z ∈ A, q ≤ z → v ≤ z)
    (ha_lt_v : a < v) :
    b ≤ u := by
  by_cases hq_le_a : q ≤ a;
  · linarith [ hv_min a ( by
      exact left_balanced_left_mem hA hbal.1 hab ) ( by linarith ) ];
  · by_cases hq_ge_b : q ≥ b;
    · contrapose! hu_max;
      exact ⟨ b, hbal.2 |> fun h => by
        grind +suggestions, by linarith, by linarith ⟩;
    · -- Since $a \leq u$ and $v \leq b$, we have $b - a \geq v - u \geq 1$ and $b - a = s \leq 1$, so $a = u$ and $b = v$.
      have h_eq : a = u ∧ b = v := by
        constructor <;> linarith [ hu_max a ( left_balanced_left_mem hA hbal.1 hab ) ( by linarith ), hv_min b ( right_balanced_right_mem hA hbal.2 hab ) ( by linarith ) ];
      have h_subset : A ∩ Set.Icc a b ⊆ {a, b} := by
        grind +extAll;
      have h_measure_zero : (volume (A ∩ Set.Icc a b)).toReal = 0 := by
        exact MeasureTheory.measure_mono_null h_subset ( MeasureTheory.measure_union_null ( MeasureTheory.measure_singleton a ) ( MeasureTheory.measure_singleton b ) ) |> fun h => h.symm ▸ by norm_num;
      unfold discOn at hdisc; linarith;

/-
Lemma `small case` from Section 4 of the paper.

Here `u` and `v` are respectively the last and first points of `A` around
`q = y-1`.  The interval `[a,b]` is balanced with positive discrepancy,
`s=b-a≤1`, and the points around the gap satisfy `v-u≥1`.  The neighbourhood
hypothesis records the output of the positive-triple reduction near `x-1`.
Under the temporary regime `y<3+s`, one must have `v≤a`.
-/
lemma small_case_left_endpoint_ge
    (hA : IsClosed A) (hmin : IsLeast A 1)
    {a b u v x y s ε : ℝ}
    (hab : a < b) (hs : s = b - a) (hs1 : s ≤ 1)
    (hy : y = x + 1 - a) (hysmall : y < 3 + s)
    (hbal : IsBalanced A a b) (hdisc : 0 < discOn A a b)
    (huv : 1 ≤ v - u)
    (hu_max : ∀ z ∈ A, z ≤ y - 1 → z ≤ u)
    (hv_min : ∀ z ∈ A, y - 1 ≤ z → v ≤ z)
    (hε : 0 < ε)
    (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    v ≤ a := by
  -- By contradiction, assume $v \leq a$.
  by_contra hv_not_le_a;
  -- By `balanced_interval_not_straddle_long_gap` applied to `[a,b]` with `q=y-1` we have `b≤u`.
  have hb_le_u : b ≤ u := by
    apply balanced_interval_not_straddle_long_gap hA hab hs hs1 hbal hdisc huv hu_max hv_min (by linarith);
  -- Choose $\epsilon' = \min(\epsilon/2, (v - (x - 1))/2) > 0$. Then $x - 1 + \epsilon'$ is in the neighborhood and $A$.
  set ε' := min (ε / 2) ((v - (x - 1)) / 2) with hε'_def
  have hε'_pos : 0 < ε' := by
    exact lt_min ( half_pos hε ) ( by linarith )
  have hx_minus_one_plus_ε'_in_neighborhood : x - 1 + ε' ∈ Set.Icc (x - 1 - ε) (x - 1 + ε) := by
    constructor <;> linarith [ min_le_left ( ε / 2 ) ( ( v - ( x - 1 ) ) / 2 ), min_le_right ( ε / 2 ) ( ( v - ( x - 1 ) ) / 2 ) ]
  have hx_minus_one_plus_ε'_in_A : x - 1 + ε' ∈ A := by
    exact hneigh hx_minus_one_plus_ε'_in_neighborhood;
  -- Since $x - 1 + \epsilon' < v$, by $v$-minimality it cannot be $\geq y - 1$; hence it is $< y - 1$.
  have hx_minus_one_plus_ε'_lt_y_minus_one : x - 1 + ε' < y - 1 := by
    grind;
  linarith [ hmin.2 ( show a ∈ A from by
                        convert left_balanced_left_mem hA hbal.1 hab using 1 ) ]

/-
Removing a terminal subinterval of length `m` decreases the mass by at
most `m`.  This is the measure estimate used immediately after Lemma `small
case` in the paper.
-/
lemma mass_Icc_le_truncated_add {a b m : ℝ}
    (hm : 0 ≤ m) (hmle : m ≤ b - a) :
    (volume (A ∩ Icc a b)).toReal ≤
      (volume (A ∩ Icc a (b - m))).toReal + m := by
  -- By measure subadditivity and monotonicity, mass ≤ truncated mass + volume [b-m,b] = truncated mass + m.
  have h_subadd : (volume (A ∩ Icc a b)).toReal ≤ (volume (A ∩ Icc a (b - m) ∪ Icc (b - m) b)).toReal := by
    refine' ENNReal.toReal_mono _ _;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc a ( b - m ) ∪ Icc ( b - m ) b ⊆ Icc a b from Set.union_subset ( Set.inter_subset_right.trans ( Set.Icc_subset_Icc_right ( by linarith ) ) ) ( Set.Icc_subset_Icc ( by linarith ) le_rfl ) ) ) ( by simp +decide [ Real.volume_Icc ] ) );
    · exact MeasureTheory.measure_mono fun x hx => by cases le_total x ( b - m ) <;> aesop;
  have h_union : volume (A ∩ Icc a (b - m) ∪ Icc (b - m) b) ≤ volume (A ∩ Icc a (b - m)) + volume (Icc (b - m) b) := by
    exact MeasureTheory.measure_union_le _ _;
  refine le_trans h_subadd <| le_trans ( ENNReal.toReal_mono ?_ h_union ) ?_;
  · refine' ne_of_lt ( lt_of_le_of_lt ( add_le_add ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) le_rfl ) _ ) ; aesop;
  · rw [ ENNReal.toReal_add ] <;> norm_num [ hm, hmle ];
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide ) )

/-
Discrepancy-form version of `mass_Icc_le_truncated_add`: the truncated
part of a discrepancy-maximizing interval retains at least
`(s+t)/2-m` mass.
-/
lemma truncated_mass_lower_of_discOn {a b s t m : ℝ}
    (hs : s = b - a) (ht : t = discOn A a b)
    (hm : 0 ≤ m) (hmle : m ≤ s) :
    (s + t) / 2 - m ≤ (volume (A ∩ Icc a (b - m))).toReal := by
  have := @mass_Icc_le_truncated_add A a b m;
  convert sub_le_sub_right ( this hm ( by linarith ) ) m using 1 ; unfold discOn at * ; ring_nf at *;
  · grobner;
  · ring

/-
The improved cumulative-mass estimate immediately following Lemma `small
case` in the paper.  It combines `another_boost_of_long_gap` at `d=b-1`,
the disjoint packing of `A` and `A-A`, and
`truncated_mass_lower_of_discOn`.
-/
lemma cum_b_sub_one_bound_of_small_case
    (hA : IsClosed A) (hAcompact : IsCompact A)
    (hAfin : volume A ≠ ⊤) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b u v q s t : ℝ} (hab : a < b) (hs : s = b - a)
    (hs1 : s ≤ 1) (ht : t = discOn A a b)
    (hI : IsRightBalanced A a b)
    (huA : u ∈ A) (hu : 1 ≤ u) (huv : 1 ≤ v - u) (hva : v ≤ a)
    (hu_max : ∀ z ∈ A, z ≤ q → z ≤ u)
    (hv_min : ∀ z ∈ A, q ≤ z → v ≤ z)
    (hmle : mMinus A u ≤ s) (hmb : mMinus A (b - 1) = 0)
    {ivs₁ ivs₂ : List (ℝ × ℝ)}
    (hB₁ : IsIntervalUnion (A ∩ Icc 1 u) ivs₁)
    (hB₂ : IsIntervalUnion (A ∩ Icc (u + s) (b - 1)) ivs₂)
    (hdisc₁ : disc (A ∩ Icc 1 u) ≤ discOn A a b)
    (hdisc₂ : disc (A ∩ Icc (u + s) (b - 1)) ≤ discOn A a b) :
    3 * cum A (b - 1) ≤ b - 2 - (s + t) / 2 + mMinus A u := by
  -- Apply another_boost_of_long_gap with d=b-1 and the given extremal/interval-union hypotheses.
  have h_boost : 2 * cum A (b - 1) + (volume (A ∩ Icc a (b - mMinus A u))).toReal ≤ (volume ((A - A) ∩ Icc 1 (b - 1))).toReal := by
    have := @another_boost_of_long_gap A hA hAcompact hAfin;
    convert this hmin hab hs hs1 hI huA hu _ huv hu_max hv_min hmle hmb hB₁ hB₂ hdisc₁ hdisc₂ using 1;
    · ring;
    · linarith;
  -- Apply diff_mass_add_mass_le_length hA.measurableSet hsf on [1,b-1], obtaining diffMeasure + mass(A∩[1,b-1])≤b-2.
  have h_diff_mass : (volume ((A - A) ∩ Icc 1 (b - 1))).toReal + (volume (A ∩ Icc 1 (b - 1))).toReal ≤ b - 2 := by
    convert diff_mass_add_mass_le_length hA.measurableSet hsf ( show 1 ≤ b - 1 by linarith [ hmin.1 ] ) using 1 ; ring;
  -- Rewrite mass(A∩[1,b-1])=cum(b-1) using cum_sub_cum_eq_mass_Icc, cum_one_eq_zero_of_isLeast; note b≥2 follows u+s≤b-1, u≥1, and s≥0 (from hab,hs).
  have h_cum : (volume (A ∩ Icc 1 (b - 1))).toReal = cum A (b - 1) := by
    rw [ ← cum_sub_cum_eq_mass_Icc ];
    · rw [ cum_one_eq_zero_of_isLeast hmin, sub_zero ];
    · norm_num;
    · linarith [ hmin.2 huA ]
  have hb_ge_two : 2 ≤ b := by
    linarith;
  linarith [ truncated_mass_lower_of_discOn hs ht ( show 0 ≤ mMinus A u by exact mMinus_nonneg hAfin u ) ( show mMinus A u ≤ s by linarith ) ]

end ProductFree