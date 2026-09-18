import RequestProject.Section4DoubleBoost
import RequestProject.Section4PrepUSmall
import RequestProject.Section4Final
import RequestProject.Section4UGtYMinusTwo
import RequestProject.Section4YThreeGeometry
import RequestProject.Section4YThreeDifference
import RequestProject.Section4YThreeEmpty
import RequestProject.Defs
import RequestProject.Analytic
import RequestProject.Discrepancy
import RequestProject.Balanced
import RequestProject.BalancedMore
import RequestProject.BalancedSum
import RequestProject.EdgeDisc
import RequestProject.IntervalUnion
import RequestProject.LeftBalancedDecomp
import RequestProject.KeyBound
import RequestProject.KeyBoundRight
import RequestProject.OffdiagonalMain
import RequestProject.MaxBalanced
import RequestProject.DiscAttain
import RequestProject.Partition
import RequestProject.OffdiagonalInduction
import RequestProject.Section4Prep
import RequestProject.Section4Rigidity
import RequestProject.Section4MZero
import RequestProject.Section4MZeroExact
import RequestProject.Section4FirstGap
import RequestProject.Section4PushLeft
import RequestProject.Section4Boost
import RequestProject.Section4LongGapEstimate
import RequestProject.Section4SmallCase
import RequestProject.Section4PushLeftFurther
import RequestProject.Section4YBound
import RequestProject.Section4SecondGap
import RequestProject.Section4TGtHalf
import RequestProject.Section4W
import RequestProject.Section4YLessThanThreePlusS
import RequestProject.KeyLemma
import RequestProject.Main1

/-!
# Product-free subsets of `(0,1)` have measure `< 1/3`

This is the aggregating entry point for the formalization of the paper's results on
product-free subsets of the open interval `(0,1)`.

## Main results

* `ProductFree.main1_compact` — a nonempty compact product-free subset of `(0,1)` has Lebesgue
  measure strictly less than `1/3`.
* `ProductFree.main1` — an open product-free subset of `(0,1)` has Lebesgue measure at most `1/3`.
* `ProductFree.sumfree_integral_lt_third` — the analytic reduction: a measurable sum-free set with
  least element `δ > 0` satisfies `∫_{u>0} e^{-u} |A ∩ [0,u]| du < 1/3`.
* `ProductFree.discrepancy_observation`, `ProductFree.discrepancy_observation2` — the elementary
  discrepancy lemmas.

## Section 3 toolbox (fully proved, `RequestProject/Balanced.lean`)

The "balanced interval" toolbox used by the paper to prove `main2` (and `main1`) is fully
formalized and proved in `RequestProject/Balanced.lean`:

* `IsLeftBalanced`, `IsRightBalanced`, `IsBalanced` and the additivity/reflection lemmas for the
  interval discrepancy `d_A`;
* `union_left_balanced` (Lemma "union left balanced");
* the intersection lemmas (`inter_nonempty_of_measure`, `inter_nonempty_of_discOn`,
  `inter_nonempty_of_discOn_pos`) and their difference-set forms (`diff_helper_*`, `diff_mem_*`);
* `main_step` (Lemma "main step") and `main_step_sums_left` / `main_step_sums_right`
  (Corollary "main step sums").

Continued in `RequestProject/BalancedMore.lean`:

* subinterval discrepancy bounds for balanced intervals (`discOn_le_of_balanced`,
  `neg_discOn_le_of_balanced`);
* endpoint membership of balanced intervals of positive length (`left_balanced_left_mem`,
  `right_balanced_right_mem`);
* `union_right_balanced`, `union_balanced`;
* the maximal-balanced-interval notions (`IsMaximalLeftBalanced`, `IsMaximalBalanced`) and
  Corollary "balanced intervals": distinct maximal (left-)balanced intervals are disjoint
  (`maximal_left_balanced_disjoint`, `maximal_balanced_disjoint`).

Continued in `RequestProject/BalancedSum.lean`:

* `inter_Icc_nonempty_of_balanced` — a subinterval of a balanced interval whose length is at
  least the discrepancy meets `A`;
* `intersect_balanced` (Lemma "intersect balanced") — two balanced intervals of equal discrepancy
  that overlap meet inside `A ∩ B`;
* `add_balanced` (Corollary "add balanced") — `(A ∩ I) + (B ∩ J) = I + J` when `d_A(I) = d_B(J)`.

## Section 3, continued: edge discrepancies, interval unions, and `key_bound`

Further Section 3 machinery, fully proved (only the standard axioms):

* `RequestProject/EdgeDisc.lean` — the left/right edge discrepancies `d_L`, `d_R` (`discL`,
  `discR`) and the bounds `discL_le_disc`, `discR_le_disc`, `discL_nonneg`, `discR_nonneg`.
* `RequestProject/IntervalUnion.lean` — the representation `IsIntervalUnion A ivs` of a finite
  union of finite closed intervals by a sorted, strictly separated list, and its basic properties
  (`isClosed`, `finite`, `isCompact`, `nonempty`, `sInf_eq`, `sSup_eq`, `subset_Icc`).
* `RequestProject/LeftBalancedDecomp.lean` — the greedy left-balanced decomposition: continuity of
  the cumulative mass/discrepancy in the endpoint, the maximal left-balanced right endpoint
  (`exists_max_lb`), the clean-cut lemmas (`inter_Ioi_of_clean`, `cleanRight_of_maximal`), and the
  peeling step (`peel`).
* `RequestProject/KeyBound.lean` and `RequestProject/KeyBoundRight.lean` — **Corollary `key_bound`**
  (`key_bound_left` and `key_bound_right`), the central tool for `offdiagonal_main2`: for a
  (left/right) balanced interval `[a,b]` w.r.t. `A` with `d_A([a,b]) ≥ d(B)`, the restricted
  sumset `(A ∩ [a,b]) + B` has measure at least `2|B|`.
* `RequestProject/OffdiagonalMain.lean` — `offdiagonal_case1`, the **generic case** of Theorem
  `offdiagonal_main2`: when `A` and `B` each have an extreme balanced interval of full
  discrepancy, `|A + B| ≥ 2|A| + 2|B| − d(A) − d(B)` follows from the two `key_bound` corollaries
  by inclusion–exclusion.

## Section 4: preparatory rigidity lemmas

The Section 4 development begins in `RequestProject/Section4Prep.lean`:

* `mMinus` and `mPlus`, the discrepancies of intervals constrained to have a prescribed endpoint,
  together with nonnegativity and comparison to the global discrepancy;
* `sumFree_mass_Icc_le_one`, the repeatedly used fact that a sum-free set containing `1` has at
  most one unit of mass in every interval of length at most two;
* `lipschitzWith_one_cum`, continuity of the key-inequality defect, and
  `keyDefect_pos_neighborhood`, the topological first step in the positive-triple reduction.

Continued in `RequestProject/Section4Rigidity.lean`:

* `balanced_length_lt_one_of_unit_separated` (Lemma `s<1`) — every positive-length balanced
  interval in a compact set containing no pair of points at distance one has length less than one;
* `IsSumFree.balanced_length_lt_one`, its sum-free specialization when `1 ∈ A`.

Continued in `RequestProject/Section4MZero.lean`:

* `mzero_sum_membership` and `mzero_diff_membership`, the two interval-containment consequences
  of `main_step` used in the paper's Lemma `mzero`;
* `mzero_core`, the additive-combinatorial core of Lemma `mzero`: a positive-discrepancy
  left-balanced interval ending at `z` forces both `a+z` and `b-z` outside a sum-free set when
  `[a,b]` is discrepancy-maximizing.

Continued in `RequestProject/Section4MZeroExact.lean`:

* `exists_leftBalanced_of_mMinus_pos`, the missing supremum-attainment step: positive `mMinus`
  produces a nondegenerate positive-discrepancy left-balanced interval;
* `mzero`, the paper's full Lemma `mzero` for a closed sum-free subset of the nonnegative reals.

Continued in `RequestProject/Section4MInterv.lean`:

* `discR_le_mMinus_add_gap`, the endpoint-discrepancy estimate at the heart of Lemma `minterv`;
* `minterv_sum` and `minterv_diff`, both sumset and difference-set estimates of Lemma `minterv`
  for a restriction represented as a finite union of closed intervals (with reusable core forms);
* the corresponding zero-`mMinus` specializations.

Continued in `RequestProject/Section4FirstGap.lean`:

* `cum_succ_sub_gt_one_sub_disc`, the numerical conclusion of Lemma `fx+1-fx` from its
  difference-set estimate and failure of the key inequality;
* `cum_sub_cum_eq_mass_Icc`, identifying cumulative increments with interval mass;
* `first_gap` / `first_gap_of_cum` (Lemma `gapy`) — the first forced gap
  `A ∩ [y-1,y-s] = ∅`;
* `y_gt_two_of_first_gap`, the paper's immediate deduction that `y > 2` once `y > 1+s`.

Continued in `RequestProject/Section4PushLeft.lean`:

* `diff_mass_add_mass_le_length`, the packing bound for a difference-set portion and `A`;
* `not_key_fail_of_lt_two`, the boundary case of the key inequality for `1 ≤ x < 2`;
* `maximizing_right_lt_x` / `y_gt_one_add_s`, proving the next paper step that the
  discrepancy-maximizing interval satisfies `b < x`, equivalently `y > 1+s`.

Continued in `RequestProject/Section4Boost.lean`:

* `another_boost_packing` and `another_boost`, the paper's three-piece difference-set
  estimate (Lemma `another boost`), combining two `minterv_diff` bounds with a translated
  portion of the maximizing interval.

Continued in `RequestProject/Section4LongGap.lean`:

* `first_gap_extrema_strict`, locating the extremal points adjacent to the first gap;
* `mass_Icc_eq_zero_of_gap_extrema`, the measure-zero consequence of a gap of length one;
* `another_boost_of_long_gap`, Corollary `another boost cor`, in which the correction term
  in `another_boost` vanishes.

Continued in `RequestProject/Section4Extrema.lean` and `RequestProject/Section4Assembly.lean`:

* `exists_extrema_around_cut` / `exists_extrema_around_y_sub_one`, choosing the last and first
  points of a compact set adjacent to a cut;
* `section4_basic_parameters`, `section4_first_mass_surplus`, and
  `section4_assemble_first_gap`, assembling the selected maximizing interval through the first
  forced gap;
* `section4_assemble_long_gap`, continuing the assembly by choosing its adjacent extrema and
  proving that their separation is at least one;
* `section4_assemble_small_case`, carrying the assembled data through the next positional step:
  under `y < 3+s`, the first point after the gap satisfies `v ≤ a`;
* `section4_assemble_small_case_bound`, discharging the interval-union, discrepancy, and
  one-sided-discrepancy side conditions to obtain the paper's ensuing cumulative bound for
  `3 F(b-1)` directly from the initial maximizing interval;
* `section4_assemble_y_gt_two_add_s`, continuing the assembled chain through the paper's
  conclusion `y > 2+s`.

Continued in `RequestProject/Section4LongGapEstimate.lean`:

* `uncovered_translates_gt_one_sub_length`, the measure estimate obtained by filling the two
  translates of `A ∩ [a,b]` to full intervals;
* `long_gap_of_uncovered_translates`, the geometric uncovered-interval argument;
* `first_gap_length_estimate` (Lemma `y - 1 gap lem`), proving `v-u ≥ 1` from the paper's
  mass-surplus and endpoint hypotheses.

Continued in `RequestProject/Section4SmallCase.lean`:

* `balanced_interval_not_straddle_long_gap`, showing the maximizing interval cannot cross both
  endpoints of the newly established long gap;
* `small_case_left_endpoint_ge` (Lemma `small case`), proving `v ≤ a` in the regime `y < 3+s`;
* `cum_b_sub_one_bound_of_small_case`, the improved bound for `F(b-1)` immediately following
  Lemma `small case`, together with its interval-truncation measure estimates.

Continued in `RequestProject/Section4PushLeftFurther.lean`:

* `cum_increment_le_of_discOn_le` and the two one-unit discrepancy comparisons used in the
  next argument;
* `unit_translate_pair_mass_le` and `cum_b_one_sub_cum_b_one_le`, formalizing the packing of
  an interval with its unit translate and the resulting estimate on `[b-1,b+1]`;
* `cumulative_bound_toward_y_gt_two_add_s`, the combined cumulative estimate reached midway
  through the proof that `y > 2+s`.

The subsequent development proves `y > 2+s`, then develops the two numerical cases for
`y > 3`, and then proves `a > 2` in `Section4YBound.lean`, `Section4YThree.lean`, and
`Section4AGtTwo.lean`.  `Section4YThreeGeometry.lean` now supplies the two reflection/packing
estimates and their assembly for the nonempty geometric branch of `y > 3`.
`Section4YThreeDifference.lean` packages `main2_iu` and symmetry into the cumulative
restricted difference-set estimate used in that branch, and assembles the full nonempty
branch directly from the maximizing interval and a point in `A ∩ [b+1,x]`.

Continued in `RequestProject/Section4UGtYMinusTwo.lean`:

* `exists_direct_packing_deficit`, introducing the paper's nonnegative deficit `g`;
* `mass_near_y_gt_five_quarters`, deriving
  `5/4 (1-t) + g/2 < F(y)-F(y-2)`;
* `reflection_mass_le_interval_complement`, the reflection packing estimate for a sum-free set;
* `mass_near_y_le_half_gap`, giving the contradictory upper bound under `u ≤ y-2`;
* `u_gt_y_sub_two`, the conclusion `u > y-2`.

Continued in `RequestProject/Section4GapAroundX.lean` and
`RequestProject/Section4SecondGap.lean`:

* `local_difference_translate_packing` and `gap_immediately_left_of_x_full`, proving
  the paper's forced gap `A ∩ [u+b-1,x] = ∅` from sum-freeness and the endpoint relations;
* `short_interval_near_x_subset`, showing this gap contains `[x+s-1,x]`;
* `two_difference_intervals_cover_lower`, the interval-measure geometry for the two
  translates `u' - [a,b]` and `v' - [a,b]`;
* `second_gap_strict_upper` and `gap_around_x`, deriving the strict packing upper bound
  from the mass surplus and then proving the paper's conclusion `v' - u' ≥ 1`;
* `section4_assemble_gap_around_x_of_packing`, constructing the extremal points `u',v'`
  adjacent to `x` and assembling all established Section 4 estimates to prove
  `v' - u' ≥ 1` once the remaining two-translate measure-packing estimate is supplied;
* `t_gt_one_half`, the requested corollary `t > 1/2`, obtained by adding the
  difference-set estimate and the two maximal-discrepancy estimates around the gap;
* `section4_assemble_t_gt_one_half` (in `RequestProject/Section4TGtHalf.lean`), the fully
  assembled form of that corollary: starting from the initial Section 4 setup it constructs
  the extremal points `u',v'` around `x`, derives `F(x)=F(u')=F(v')` across the gap and the
  three packing/discrepancy inputs, and concludes `1/2 < d_A[a,b]`.

Continued in `RequestProject/Section4W.lean`:

* `boost_and_interval_around_a`, the numerical mass boost on `[a-2,a]`;
* `left_block_nonempty` and `exists_rightmost_left_block`, constructing the rightmost point
  `a-2+w` of `A ∩ [a-2,a-1]`;
* `w_inequality` and `exists_w_with_inequality`, proving the estimate
  `F(a)-F(a-2) ≤ 1-F(2-w)`.

Continued in `RequestProject/Section4YLessThanThreePlusS.lean`:

* the numerical form of Lemma `c lem` and the measure-truncation, maximal-point,
  translation, and reflection estimates used with it;
* `y_lt_four_sub_w_add_s`, proving the intermediate bound `y < 4-w+s`;
* `y_lt_three_add_s`, proving the requested conclusion `y < 3+s`.

Continued through the requested conclusion in `RequestProject/Section4GapAroundTwo.lean`
and `RequestProject/Section4DoubleBoost.lean`:

* `mass_b_sub_two_gt` and the translation/complement packing lemmas;
* `gap_around_two`, proving the two strict endpoint bounds around `2` and
  `v₂-u₂ ≥ s+g`;
* `double_boost`, assembling the paper's three displayed double-boost bounds;
* `not_two_lt_u_of_double_boost` and `u_lt_two`, formalizing the final numerical
  contradiction and the exclusion of `u=2` by sum-freeness;
* `extrema_around_two_eq`, proving that the extrema around `y-1` and `2` coincide:
  `u=u₂` and `v=v₂`.

Continued in `RequestProject/Section4PrepUSmall.lean` through all three cases of the
paper's final contradiction:

* `prep_u_small_first_case`, proving
  `F(x-1) + F(a-2) + F(x+1) ≤ x+t+F(2)-3` in Case 1 (`v>y`), from the
  difference-set packing and the mass-free gap;
* `prep_u_small_second_case`, proving the same inequality in Case 2
  (`v≤y` and `v+a≥v'`), from the combined difference- and sumset packing estimate;
* `prep_u_small_case_three_gap_numeric` and `prep_u_small_third_case`, proving the
  `y-v≥s` contradiction and the inequality in Case 3 (`v≤y`, `v+a<v'`);
* `prep_u_small_all_cases`, splitting on `v>y` and then on `v+a≥v'`, proving that
  the three cases are exhaustive and establishing the inequality unconditionally
  from the corresponding geometric packing estimates.

Completed the closing calculation in `RequestProject/Section4Final.lean`:

* `section4_final_key_inequality`, combining `prep u small`, `w ineq`, the
  three-piece packing, discrepancy identity, final unit-translate packing, and forced gap to prove
  `F(x-1)+F(x)+F(x+1) ≤ x`;
* `section4_final_contradiction`, showing these estimates contradict the selected counterexample.

The initial reduction in `RequestProject/KeyLemma.lean` has also been strengthened so that
the selected failure point `x` comes with a genuine closed neighborhood of `x-1` contained
in `A`.  This is obtained by avoiding the finitely many component endpoints in the
primitive-crossing argument.  The same file now packages the normalized Section 4 parameters
and the extrema around the first forced gap, and assembles all geometric data through `y > 3`.

The two branches of the lower bound `y > 3` are now completely assembled in
`RequestProject/Section4YThreeEmpty.lean`:

* `section4_y_gt_three_empty_branch`, handling `A ∩ [b+1,x] = ∅` via the earlier
  small-case cumulative estimate and a Brunn--Minkowski packing;
* `section4_assemble_y_gt_three`, splitting on that intersection and combining the
  empty branch with `section4_y_gt_three_nonempty_branch` to prove `y > 3` directly
  from the selected maximizing interval and counterexample neighborhood.

## Status

The whole development is now proved with only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); there are no `sorry`s and no use of `sorryAx`.

* `ProductFree.key_lemma` — the central rigidity lemma (the "bulk of the paper", Section 4) — is
  fully proved: the finite-interval-union form (`key_lemma_intervalUnion`) in Section 4, and the
  measurable-set form (`key_lemma`) via an outer-fattening/inner-regularity transfer in
  `RequestProject/KeyLemma.lean`.
* `ProductFree.offdiagonal_main2_iu` / `ProductFree.main2_iu` — the off-diagonal sumset
  inequality `|A + B| ≥ 2|A| + 2|B| − d(A) − d(B)` and its symmetric corollary
  `|A ± A| ≥ 4|A| − 2 d(A)` for finite unions of closed intervals (Section 3) — are fully proved
  in `RequestProject/OffdiagonalInduction.lean`.
* `ProductFree.main2_measurable` (`RequestProject/MainTwoBorel.lean`) — the symmetric sumset
  inequality for measurable sets of finite measure (with the necessary finiteness hypothesis on
  `A + A` / `A - A`), obtained from `main2_iu` by outer fattening.  See that file's module
  docstring for why the unconditional measurable statement is false and had to be corrected.
-/
