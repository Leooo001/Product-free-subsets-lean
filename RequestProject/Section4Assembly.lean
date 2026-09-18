import RequestProject.Section4Final
import RequestProject.Section4Extrema

/-!
# Section 4: geometric assembly

This file begins the assembly of the individual geometric lemmas into the contradiction used by
`key_lemma_intervalUnion_one`.  It packages the basic consequences of the selected
positive-discrepancy maximizing interval: its discrepancy is exactly the discrepancy of the
truncated set, its length is less than one, and it lies strictly to the left of the counterexample.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
Basic normalized parameters for the Section 4 geometric chain.  This is the first assembly
step after `section4_initial_setup`, expressed without introducing local abbreviations `s`, `t`,
and `y`.
-/
lemma section4_basic_parameters
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b : ℝ} (hx : 1 ≤ x)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    disc (A ∩ Icc 0 (x + 1)) = discOn A a b ∧
      discOn A a b ≤ b - a ∧ b - a < 1 ∧ b < x ∧
      1 + (b - a) < x + 1 - a ∧
      (volume (A ∩ Icc a b)).toReal = (b - a + discOn A a b) / 2 := by
  -- We'll use that discOn A a b = discOn (A ∩ Icc 0 (x + 1)) a b.
  have hdisc_eq : discOn A a b = discOn (A ∩ Icc 0 (x + 1)) a b := by
    have h_subset : A ∩ Icc a b = (A ∩ Icc 0 (x + 1)) ∩ Icc a b := by
      ext; simp [Set.mem_inter_iff, Set.mem_Icc];
      exact fun _ _ _ => ⟨ by linarith [ hmin.2 haA ], by linarith ⟩;
    unfold discOn; aesop;
  obtain ⟨hdisc_eq, hdisc_le⟩ : discOn (A ∩ Icc 0 (x + 1)) a b ≤ b - a ∧ b - a < 1 := by
    apply And.intro;
    · unfold discOn;
      rw [ show A ∩ Icc 0 ( x + 1 ) ∩ Icc a b = A ∩ Icc a b from ?_ ];
      · linarith [ show ( volume ( A ∩ Icc a b ) |> ENNReal.toReal ) ≤ b - a by exact le_trans ( ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( show A ∩ Icc a b ⊆ Icc a b from fun x hx => hx.2 ) ) ) ( by simp +decide [ hab.le ] ) ];
      · ext; simp [Set.mem_inter_iff, Set.mem_Icc];
        exact fun _ _ _ => ⟨ by linarith [ hmin.2 haA ], by linarith ⟩;
    · apply hsf.balanced_length_lt_one hIU.isCompact hmin.1 hab hbal;
  have hb_lt_x : b < x := by
    obtain ⟨c, hc⟩ := hIU.inter_Icc_exists 1 (b - 1);
    apply maximizing_right_lt_x;
    exact hIU.isCompact.isClosed;
    any_goals assumption;
    exact hIU.isCompact.measure_lt_top.ne;
  refine' ⟨ _, _, _, _, _, _ ⟩;
  any_goals linarith;
  · refine' le_antisymm hmax _;
    refine' le_csSup _ _;
    · refine' ⟨ 2 * ( volume ( A ∩ Icc 0 ( x + 1 ) ) |> ENNReal.toReal ) + 1, fun r hr => _ ⟩ ; rcases hr with ⟨ a, b, hab, rfl ⟩ ; linarith [ show ( volume ( A ∩ Icc 0 ( x + 1 ) ∩ Icc a b ) |> ENNReal.toReal ) ≤ ( volume ( A ∩ Icc 0 ( x + 1 ) ) |> ENNReal.toReal ) from ENNReal.toReal_mono ( by
                                                                                                                                                exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc 0 ( x + 1 ) ⊆ Icc 0 ( x + 1 ) from fun y hy => hy.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ];
    · use a, b;
      simp_all +decide [ discOn ];
      linarith;
  · unfold discOn at *;
    ring

/-
A compact centrally symmetric subset of the line has half its mass on the nonnegative
half-line (the origin is null).
-/
lemma compact_symmetric_measure_eq_twice_nonneg
    {S : Set ℝ} (hS : IsCompact S) (hsymm : -S = S) :
    (volume S).toReal = 2 * (volume (S ∩ Ici 0)).toReal := by
  -- By symmetry of $S$, we have $\mu(S \cap (-\infty, 0)) = \mu(S \cap [0, \infty))$.
  have h_symm : MeasureTheory.volume (S ∩ Set.Iio 0) = MeasureTheory.volume (S ∩ Set.Ioi 0) := by
    have h_symm : MeasureTheory.volume (S ∩ Set.Iio 0) = MeasureTheory.volume (Set.image (fun x => -x) (S ∩ Set.Ioi 0)) := by
      congr with x ; simp +decide [ Set.ext_iff ] at * ; aesop;
    -- Since the measure is invariant under the map $x \mapsto -x$, we have $\mu(S \cap (-\infty, 0)) = \mu(S \cap (0, \infty))$.
    have h_inv : ∀ (s : Set ℝ), MeasureTheory.volume (Set.image (fun x => -x) s) = MeasureTheory.volume s := by
      simp +decide [ Set.image_neg ]
    generalize_proofs at *; (
    rw [ h_symm, h_inv ]);
  -- By partitioning $S$ into $S \cap (-\infty, 0)$ and $S \cap [0, \infty)$, we can write the volume of $S$ as the sum of the volumes of these two sets.
  have h_partition : MeasureTheory.volume S = MeasureTheory.volume (S ∩ Set.Iio 0) + MeasureTheory.volume (S ∩ Set.Ici 0) := by
    rw [ ← MeasureTheory.measure_inter_add_diff S ( measurableSet_Iio ), Set.inter_comm ];
    congr ; ext ; aesop;
  rw [ h_partition, h_symm, two_mul ];
  rw [ show S ∩ Ici 0 = ( S ∩ Ioi 0 ) ∪ ( S ∩ { 0 } ) from ?_, MeasureTheory.measure_union ];
  · rw [ ENNReal.toReal_add, ENNReal.toReal_add ] <;> norm_num;
    · exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_singleton 0 ) |> fun h => h.symm ▸ by norm_num;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( hS.measure_lt_top ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( hS.measure_lt_top ) );
    · exact ⟨ ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( hS.measure_lt_top ) ), ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) ) ⟩;
  · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₁.2.out.ne' <| hx₂.2.symm ▸ rfl;
  · exact hS.measurableSet.inter ( MeasurableSingletonClass.measurableSet_singleton _ );
  · grind

/-
The first quantitative bridge in the geometric chain (paper's `fx+1-fx`): the
finite-union difference-set theorem, symmetry of the difference set, and sum-freeness force a
mass surplus in `[x,x+1]`.
-/
lemma section4_first_mass_surplus
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x t : ℝ} (hx : 1 ≤ x)
    (ht : disc (A ∩ Icc 0 (x + 1)) ≤ t)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    1 - t < cum A (x + 1) - cum A x := by
  have hB_IU : ∃ ivsB : List (ℝ × ℝ), IsIntervalUnion (A ∩ Icc 0 x) ivsB := by
    exact hIU.inter_Icc_exists 0 x;
  obtain ⟨ivsB, hB_IU⟩ := hB_IU
  have hB_nonempty : 1 ∈ A ∩ Icc 0 x := by
    exact ⟨ hmin.1, ⟨ by norm_num, hx ⟩ ⟩
  have hB_list_nonempty : ivsB ≠ [] := by
    cases hB_IU ; aesop;
  have hB_diff_bound : 4 * (cum A x) - 2 * disc (A ∩ Icc 0 x) ≤ (volume ((A ∩ Icc 0 x) - (A ∩ Icc 0 x))).toReal := by
    have hB_diff_bound : 4 * (volume (A ∩ Icc 0 x)).toReal - 2 * disc (A ∩ Icc 0 x) ≤ (volume ((A ∩ Icc 0 x) - (A ∩ Icc 0 x))).toReal := by
      have := main2_iu hB_IU
      exact this hB_list_nonempty |>.2;
    convert hB_diff_bound using 1;
  have hB_symm_measure : (volume ((A ∩ Icc 0 x) - (A ∩ Icc 0 x))).toReal = 2 * (volume (((A ∩ Icc 0 x) - (A ∩ Icc 0 x)) ∩ Ici 0)).toReal := by
    apply compact_symmetric_measure_eq_twice_nonneg;
    · have hB_compact : IsCompact (A ∩ Icc 0 x) := by
        have := hB_IU.isClosed;
        exact CompactIccSpace.isCompact_Icc.of_isClosed_subset this fun y hy => hy.2;
      convert hB_compact.prod hB_compact |> IsCompact.image <| show Continuous fun p : ℝ × ℝ => p.1 - p.2 from continuous_fst.sub continuous_snd using 1;
      ext; simp [Set.mem_sub, Set.mem_image];
    · ext; simp [Set.mem_sub, Set.mem_neg];
  have hB_subset : ((A ∩ Icc 0 x) - (A ∩ Icc 0 x)) ∩ Ici 0 ⊆ (A - A) ∩ Icc 0 (x - 1) := by
    intros y hy; simp_all +decide [ Set.mem_sub, Set.mem_Icc ] ;
    exact ⟨ by obtain ⟨ a, ha, b, hb, rfl ⟩ := hy.1; exact ⟨ a, ha.1, b, hb.1, rfl ⟩, by obtain ⟨ a, ha, b, hb, rfl ⟩ := hy.1; linarith [ hmin.2 ha.1, hmin.2 hb.1 ] ⟩;
  have hB_measure_le : (volume (((A ∩ Icc 0 x) - (A ∩ Icc 0 x)) ∩ Ici 0)).toReal ≤ (volume ((A - A) ∩ Icc 0 (x - 1))).toReal := by
    apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( A - A ) ∩ Icc 0 ( x - 1 ) ⊆ Icc 0 ( x - 1 ) from fun y hy => hy.2 ) ) ( by simp +decide [ hx ] ) );
  have hB_disc_le : disc (A ∩ Icc 0 x) ≤ disc (A ∩ Icc 0 (x + 1)) := by
    apply disc_mono;
    · exact Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right <| by linarith;
    · have := hIU.isCompact;
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( this.measure_lt_top ) );
  have := diff_mass_add_mass_le_length hIU.isClosed.measurableSet hsf ( show 0 ≤ x - 1 by linarith );
  linarith! [ show cum A ( x - 1 ) = ( volume ( A ∩ Icc 0 ( x - 1 ) ) |> ENNReal.toReal ) from rfl ]

/-
Assembly through the paper's first forced gap.  Starting directly from the interval selected
by `section4_initial_setup`, this packages the normalized parameters and proves
`A ∩ [y-1,y-s] = ∅` for `s=b-a` and `y=x+1-a`.
-/
lemma section4_assemble_first_gap
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b : ℝ} (hx : 1 ≤ x)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    disc (A ∩ Icc 0 (x + 1)) = discOn A a b ∧
      b - a < 1 ∧ b < x ∧
      1 - discOn A a b < cum A (x + 1) - cum A x ∧
      A ∩ Icc ((x + 1 - a) - 1) ((x + 1 - a) - (b - a)) = ∅ := by
  obtain ⟨h_disc, h_ba, h_bx, h_surplus⟩ := section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax;
  have h_gap : 1 - discOn A a b < cum A (x + 1) - cum A x := by
    grind +suggestions;
  have := @first_gap_of_cum A;
  exact ⟨ h_disc, h_bx, h_surplus.1, h_gap, this ( hIU.isClosed.measurableSet ) hsf ( show 0 ≤ x by linarith ) ( show a ≤ b by linarith ) rfl rfl rfl h_gap ⟩

/-
The first-gap assembly continued through the choice of its neighboring points and the proof
that their separation has length at least one.  This packages the compactness construction
needed by all subsequent Section 4 estimates.
-/
lemma section4_assemble_long_gap
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    let s := b - a
    let t := discOn A a b
    let y := x + 1 - a
    2 < y ∧ ∃ u v : ℝ,
      u ∈ A ∧ u < y - 1 ∧ (∀ z ∈ A, z ≤ y - 1 → z ≤ u) ∧
      v ∈ A ∧ y - s < v ∧ (∀ z ∈ A, y - 1 ≤ z → v ≤ z) ∧
      1 ≤ v - u := by
  obtain ⟨s, t, y, hs, ht, hy, hgap⟩ : ∃ s t y, s = b - a ∧ t = discOn A a b ∧ y = x + 1 - a ∧ 2 < y ∧ A ∩ Icc (y - 1) (y - s) = ∅ := by
    obtain ⟨h_disc, h_s_lt_1, h_b_lt_x, h_surplus, h_gap⟩ := section4_assemble_first_gap hIU hsf hmin hx hfail hab hbtop haA hbal hmax;
    have := y_gt_two_of_first_gap ( show 1 ∈ A from hmin.1 ) ( show 1 + ( b - a ) < x + 1 - a from by linarith ) h_gap; aesop;
  obtain ⟨u, v, hu, hv, hu_max, hv_min⟩ : ∃ u v : ℝ, u ∈ A ∧ u ≤ y - 1 ∧ (∀ z ∈ A, z ≤ y - 1 → z ≤ u) ∧ v ∈ A ∧ y - 1 ≤ v ∧ (∀ z ∈ A, y - 1 ≤ z → v ≤ z) := by
    apply exists_extrema_around_y_sub_one hIU.isCompact;
    exact hmin.1;
    exact hxright;
    · linarith;
    · linarith [ hmin.2 haA ];
  obtain ⟨hu_lt, hv_gt⟩ : u < y - 1 ∧ y - s < v := by
    apply first_gap_extrema_strict;
    any_goals tauto;
    have := section4_assemble_first_gap hIU hsf hmin hx hfail hab hbtop haA hbal hmax; linarith;
  obtain ⟨hmass, hunit⟩ : cum A (x + 1) - cum A x = (volume (A ∩ Icc x (x + 1))).toReal ∧ cum A (x + 1) - cum A x > 1 - t := by
    apply And.intro;
    · rw [ cum_sub_cum_eq_mass_Icc ]; all_goals linarith;
    · apply section4_first_mass_surplus hIU hsf hmin hx (by linarith) hfail;
  have hlength : 1 ≤ v - u := by
    have hmass : (volume (A ∩ Icc x (x + 1))).toReal > 1 - t := by
      linarith
    apply first_gap_length_estimate;
    exact hIU.isClosed.measurableSet;
    exact hsf;
    exact hab.le;
    any_goals tauto;
    · have := section4_assemble_first_gap hIU hsf hmin hx hfail hab hbtop haA hbal hmax; linarith;
    · linarith;
    · linarith;
  grind

/-
The long-gap assembly continued through the paper's `small case` lemma.  Besides constructing
`u` and `v`, this packages the first consequence used to push the maximizing interval left:
whenever `y < 3+s`, the first point after the gap lies at or before `a`.
-/
lemma section4_assemble_small_case
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    let s := b - a
    let t := discOn A a b
    let y := x + 1 - a
    2 < y ∧ ∃ u v : ℝ,
      u ∈ A ∧ u < y - 1 ∧ (∀ z ∈ A, z ≤ y - 1 → z ≤ u) ∧
      v ∈ A ∧ y - s < v ∧ (∀ z ∈ A, y - 1 ≤ z → v ≤ z) ∧
      1 ≤ v - u ∧ (y < 3 + s → v ≤ a) := by
  obtain ⟨ u, v, hu, hv, huv ⟩ := section4_assemble_long_gap hIU hsf hmin hx hxright hfail hab hbtop haA hbal hmax;
  use u, v, hu;
  have h_disc_pos : 0 < discOn A a b := by
    have h_disc_pos : 1 - discOn A a b < cum A (x + 1) - cum A x := by
      apply section4_first_mass_surplus hIU hsf hmin hx hmax hfail;
    linarith [ show cum A ( x + 1 ) - cum A x ≤ 1 from by
                have h_disc_pos : cum A (x + 1) - cum A x ≤ (volume (A ∩ Ioc x (x + 1))).toReal := by
                  rw [ cum, cum ];
                  rw [ show A ∩ Icc 0 ( x + 1 ) = ( A ∩ Icc 0 x ) ∪ ( A ∩ Ioc x ( x + 1 ) ) from ?_, MeasureTheory.measure_union ];
                  · rw [ ENNReal.toReal_add ] <;> norm_num;
                    · have h_finite : MeasureTheory.volume A ≠ ⊤ := by
                        exact hIU.isCompact.measure_lt_top.ne;
                      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr h_finite ) );
                    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Ioc x ( x + 1 ) ⊆ Set.Icc 0 ( x + 1 ) from fun y hy => ⟨ by linarith [ hy.1, hy.2.1, hmin.2 hy.1 ], by linarith [ hy.1, hy.2.2, hmin.2 hy.1 ] ⟩ ) ) ( by simp +decide [ Real.volume_Icc ] ) );
                  · exact Set.disjoint_left.mpr fun y hy₁ hy₂ => by linarith [ hy₁.2.2, hy₂.2.1 ] ;
                  · exact hIU.isClosed.measurableSet.inter measurableSet_Ioc;
                  · grind;
                refine' le_trans h_disc_pos _;
                refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Ioc x ( x + 1 ) ⊆ Ioc x ( x + 1 ) from fun y hy => hy.2 ) _ <;> norm_num ];
  have := @ProductFree.small_case_left_endpoint_ge;
  specialize @this A ( show IsClosed A from ?_ ) hmin a b v hu x ( x + 1 - a ) ( b - a ) ε;
  · exact hIU.isCompact.isClosed;
  · exact ⟨ hv, huv.1, huv.2.1, huv.2.2.1, huv.2.2.2.1, huv.2.2.2.2.1, huv.2.2.2.2.2, fun h => this hab ( by linarith ) ( by linarith [ section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax ] ) ( by linarith ) h hbal h_disc_pos huv.2.2.2.2.2 huv.2.1 huv.2.2.2.2.1 hε hneigh ⟩

end ProductFree
namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
A one-sided discrepancy based before the truncation point is controlled by the
 discrepancy of the truncation.
-/
lemma mMinus_le_disc_truncation
    (hA0 : A ⊆ Ici 0) (hfin : volume (A ∩ Icc 0 x) ≠ ⊤)
    {z : ℝ} (hz : z ≤ x) :
    mMinus A z ≤ disc (A ∩ Icc 0 x) := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ z, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ r, hr, rfl ⟩;
    convert discOn_le_disc hfin ( show r ≤ z by linarith ) using 1;
    unfold discOn;
    rw [ show A ∩ Icc 0 x ∩ Icc r z = A ∩ Icc r z from ?_ ];
    grind +revert

/-
Restrictions contained in the selected truncation inherit its discrepancy bound.
-/
lemma disc_restriction_le_maximizer
    (hA : volume (A ∩ Icc 0 x) ≠ ⊤)
    {p q t : ℝ} (hp : 0 ≤ p) (hq : q ≤ x)
    (hmax : disc (A ∩ Icc 0 x) ≤ t) :
    disc (A ∩ Icc p q) ≤ t := by
  apply le_trans (ProductFree.disc_mono (by
  exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc hp hq )) (by
  assumption)) hmax

/-
The `mzero` specialization needed immediately after the first long gap.
-/
lemma mMinus_b_sub_one_eq_zero
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x : ℝ} (hab : a < b) (hbx : b - 1 ≤ x + 1)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    mMinus A (b - 1) = 0 := by
  have hA_closed : IsClosed A := by
    convert hIU.isCompact.isClosed using 1
  have hA_finite : volume A ≠ ⊤ := by
    exact hIU.isCompact.measure_lt_top.ne;
  apply mzero hA_closed hA_finite hsf;
  any_goals tauto;
  · exact fun x hx => hmin.2 hx |> le_trans zero_le_one;
  · exact Or.inr ( by simpa using hmin.1 )

/-
The small-case assembly continued through the cumulative estimate immediately following
Lemma `small case` in the paper.  All auxiliary hypotheses of
`cum_b_sub_one_bound_of_small_case` are discharged here from interval-union restriction,
maximal discrepancy, `mzero`, and the already assembled long gap.
-/
lemma section4_assemble_small_case_bound
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    (hysmall : x + 1 - a < 3 + (b - a)) :
    ∃ u : ℝ,
      u ∈ A ∧ u < x - a ∧
      3 * cum A (b - 1) ≤
        b - 2 - ((b - a) + discOn A a b) / 2 + mMinus A u := by
  have hsmall := section4_assemble_small_case hIU hsf hmin hx hxright hfail hab hbtop haA
    hbal hmax hε hneigh
  obtain ⟨u, v, huA, huq, hu_max, hvA, hqv, hv_min, huv, hva⟩ := hsmall.2
  have hva : v ≤ a := hva hysmall
  refine ⟨u, huA, by linarith, ?_⟩
  obtain ⟨ivs₁, hB₁⟩ := hIU.inter_Icc_exists 1 u
  obtain ⟨ivs₂, hB₂⟩ := hIU.inter_Icc_exists (u + (b - a)) (b - 1)
  have htruncfin : volume (A ∩ Icc 0 (x + 1)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      hIU.isCompact.measure_lt_top)
  have hs1 : b - a ≤ 1 := by
    linarith [section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax]
  have hmle : mMinus A u ≤ b - a := by
    have hu_top : u ≤ x + 1 := by linarith
    exact le_trans (mMinus_le_disc_truncation (x := x + 1)
      (fun z hz => le_trans zero_le_one (hmin.2 hz)) htruncfin hu_top)
      (le_trans hmax (section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax).2.1)
  have hmb : mMinus A (b - 1) = 0 :=
    mMinus_b_sub_one_eq_zero hIU hsf hmin hab (by linarith) hbal hmax
  have hdisc₁ : disc (A ∩ Icc 1 u) ≤ discOn A a b :=
    disc_restriction_le_maximizer htruncfin (by norm_num) (by linarith) hmax
  have hdisc₂ : disc (A ∩ Icc (u + (b - a)) (b - 1)) ≤ discOn A a b :=
    disc_restriction_le_maximizer htruncfin (by linarith [hmin.2 huA]) (by linarith) hmax
  exact @cum_b_sub_one_bound_of_small_case A hIU.isClosed hIU.isCompact
    hIU.isCompact.measure_lt_top.ne hsf hmin a b u v (x + 1 - a - 1) (b - a) (discOn A a b)
    hab rfl hs1 rfl hbal.2 huA (hmin.2 huA) huv hva hu_max hv_min hmle hmb
    ivs₁ ivs₂ hB₁ hB₂ hdisc₁ hdisc₂

/-- The assembled continuation through the paper's estimate `y > 2+s`. -/
lemma section4_assemble_y_gt_two_add_s
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    2 + (b - a) < x + 1 - a := by
  by_contra hnot
  push_neg at hnot
  have hysmall : x + 1 - a < 3 + (b - a) := by linarith [hab]
  obtain ⟨u, huA, hu_lt, hsmall⟩ :=
    section4_assemble_small_case_bound hIU hsf hmin hx hxright hfail hab hbtop haA
      hbal hmax hε hneigh hysmall
  obtain ⟨hdisc_eq, hts, hslt, hbx, hys, hmass⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  obtain ⟨ivsB, hB⟩ := hIU.inter_Icc_exists 0 (x + 1 - a - 1)
  obtain ⟨ivsC, hC⟩ := hIU.inter_Icc_exists b (a + 1)
  have hBne : ivsB ≠ [] := by
    intro he
    subst ivsB
    have hempty : A ∩ Icc 0 (x + 1 - a - 1) = ∅ := by
      simpa [IsIntervalUnion] using hB.2.2
    have hu0 : 0 ≤ u := le_trans zero_le_one (hmin.2 huA)
    have : u ∈ A ∩ Icc 0 (x + 1 - a - 1) := ⟨huA, hu0, by linarith⟩
    simpa [hempty] using this
  have hCne : ivsC ≠ [] := by
    intro he
    subst ivsC
    have hempty : A ∩ Icc b (a + 1) = ∅ := by
      simpa [IsIntervalUnion] using hC.2.2
    have : b ∈ A ∩ Icc b (a + 1) := ⟨hbA, le_rfl, by linarith⟩
    simpa [hempty] using this
  have htruncfin : volume (A ∩ Icc 0 (x + 1)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      hIU.isCompact.measure_lt_top)
  have hmax_left : discOn A (b - 1) b ≤ discOn A a b := by
    have hinter : A ∩ Icc (b - 1) b = (A ∩ Icc 0 (x + 1)) ∩ Icc (b - 1) b := by
      ext z
      simp only [mem_inter_iff, mem_Icc]
      constructor
      · intro hz
        exact ⟨⟨hz.1, by constructor <;> linarith [hmin.2 hz.1, hz.2.2]⟩, hz.2⟩
      · tauto
    have heq : discOn A (b - 1) b = discOn (A ∩ Icc 0 (x + 1)) (b - 1) b := by
      simp only [discOn, hinter]
    rw [heq]
    exact le_trans (discOn_le_disc htruncfin (by linarith)) hmax
  have hmax_long : discOn A (b - 1) (x - 1) ≤ discOn A a b := by
    have hinter : A ∩ Icc (b - 1) (x - 1) =
        (A ∩ Icc 0 (x + 1)) ∩ Icc (b - 1) (x - 1) := by
      ext z
      simp only [mem_inter_iff, mem_Icc]
      constructor
      · intro hz
        exact ⟨⟨hz.1, by constructor <;> linarith [hmin.2 hz.1, hz.2.2]⟩, hz.2⟩
      · tauto
    have heq : discOn A (b - 1) (x - 1) =
        discOn (A ∩ Icc 0 (x + 1)) (b - 1) (x - 1) := by
      simp only [discOn, hinter]
    rw [heq]
    exact le_trans (discOn_le_disc htruncfin (by linarith)) hmax
  have hmax_unit : discOn A a (a + 1) ≤ discOn A a b := by
    have hinter : A ∩ Icc a (a + 1) = (A ∩ Icc 0 (x + 1)) ∩ Icc a (a + 1) := by
      ext z
      simp only [mem_inter_iff, mem_Icc]
      constructor
      · intro hz
        exact ⟨⟨hz.1, by constructor <;> linarith [hmin.2 hz.1, hz.2.2]⟩, hz.2⟩
      · tauto
    have heq : discOn A a (a + 1) = discOn (A ∩ Icc 0 (x + 1)) a (a + 1) := by
      simp only [discOn, hinter]
    rw [heq]
    exact le_trans (discOn_le_disc htruncfin (by linarith)) hmax
  have hm : mMinus A u ≤ cum A u := by
    exact mMinus_le_cum hIU.isClosed.measurableSet hIU.isCompact.measure_lt_top.ne
      (fun z hz => le_trans zero_le_one (hmin.2 hz)) (le_trans zero_le_one (hmin.2 huA))
  have hygt := y_gt_two_add_s hIU.isClosed.measurableSet hsf hmin
    (a := a) (b := b) (x := x) (y := x + 1 - a) (s := b - a)
    (t := discOn A a b) (m := mMinus A u) (u := u)
    (by linarith [hmin.2 hbA]) hab.le (by linarith) hbx.le rfl rfl rfl hsmall
    hmax_left hmax_long hmax_unit (by linarith) hm hB hC hBne hCne hfail
  linarith

end ProductFree