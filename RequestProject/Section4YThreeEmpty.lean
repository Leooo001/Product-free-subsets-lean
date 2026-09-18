import RequestProject.Section4YThreeDifference
import RequestProject.Section4YBound

/-!
# Section 4: the empty branch of `y > 3`

This file completes the second geometric branch in the paper's proof that `y > 3`.
When `A ∩ [b+1,x]` is empty, the earlier small-case estimate is combined with a
Brunn--Minkowski packing in `[x,x+1]` and three maximal-discrepancy comparisons.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
Any interval contained in the selected truncation has discrepancy at most the
selected maximizing discrepancy.
-/
lemma discOn_le_selected_maximizer
    (hIU : IsIntervalUnion A ivs)
    {x a b p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ x + 1) (hpq : p ≤ q)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    discOn A p q ≤ discOn A a b := by
  obtain ⟨ s, hs ⟩ := hIU;
  refine' le_trans _ hmax;
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume ( A ∩ Icc 0 ( x + 1 ) ) |> ENNReal.toReal ) + ( x + 1 ), fun r hr => _ ⟩ ; rcases hr with ⟨ a, b, hab, rfl ⟩ ; simp_all +decide [ Set.inter_assoc ];
    refine' le_trans ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| Set.inter_subset_inter_right _ <| Set.inter_subset_left ) zero_le_two ) _;
    · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( ⋃ p ∈ ivs, Icc p.1 p.2 ) ∩ Icc 0 ( x + 1 ) ⊆ Icc 0 ( x + 1 ) from fun x hx => hx.2 ) ) _ ) ; norm_num;
    · linarith;
  · use p, q;
    rw [ show A ∩ Icc 0 ( x + 1 ) ∩ Icc p q = A ∩ Icc p q from ?_ ];
    · exact ⟨ hpq, rfl ⟩;
    · grind

/-
An empty interval between `b+1` and `x` makes the corresponding cumulative
masses equal.
-/
lemma cum_eq_of_empty_middle
    {b x : ℝ} (hb : 0 ≤ b + 1) (hbx : b + 1 ≤ x)
    (hempty : A ∩ Icc (b + 1) x = ∅) :
    cum A x = cum A (b + 1) := by
  rw [ ← sub_eq_zero, ProductFree.cum_sub_cum_eq_mass_Icc hb hbx ];
  aesop

/-
Brunn--Minkowski and sum-freeness give the packing estimate used in the
empty branch of `y > 3`.
-/
lemma empty_branch_sumset_packing
    (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a x y : ℝ} (hy : y = x + 1 - a)
    (hx1 : 0 ≤ x - 1) (hxa : x - 1 ≤ a + 1)
    {ivsB ivsC : List (ℝ × ℝ)}
    (hB : IsIntervalUnion (A ∩ Icc 0 (y - 1)) ivsB)
    (hC : IsIntervalUnion (A ∩ Icc (x - 1) (a + 1)) ivsC)
    (hBne : ivsB ≠ []) (hCne : ivsC ≠ []) :
    (cum A (x + 1) - cum A x) + cum A (y - 1) +
      (cum A (a + 1) - cum A (x - 1)) ≤ 1 := by
  convert sumset_packing_cumulative hsf hmin _ _ _ _ hB hC hBne hCne using 1 <;> ring_nf;
  · linarith;
  · linarith;
  · lia;
  · lia

/-
The earlier small-case estimate implies the base cumulative inequality in
the empty branch.
-/
lemma empty_branch_base_estimate
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x u : ℝ} (hab : a < b) (hba : b ≤ a + 1)
    (hbx : b ≤ x) (haA : a ∈ A)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hsmall : 3 * cum A (b - 1) ≤
      b - 2 - ((b - a) + discOn A a b) / 2 + mMinus A u) :
    cum A (x - 1) + 2 * cum A (b + 1) ≤
      x - ((x + 1 - a) + 1) / 2 + mMinus A u + (b - a) +
        2 * (cum A (a + 1) - cum A b) := by
  apply cumulative_bound_toward_y_gt_two_add_s;
  exact hIU.isClosed.measurableSet;
  any_goals tauto;
  · exact hmin.1;
  · linarith [ hmin.2 haA ];
  · linarith;
  · apply discOn_le_selected_maximizer hIU;
    any_goals exact x;
    · linarith [ hmin.2 haA ];
    · linarith;
    · linarith;
    · assumption;
  · apply discOn_le_selected_maximizer hIU (by
    linarith [ hmin.2 haA ]) (by
    linarith) (by
    linarith) hmax

/-
The two direct maximal-discrepancy comparisons needed in the empty branch.
-/
lemma empty_branch_unit_long_bounds
    (hIU : IsIntervalUnion A ivs) (hmin : IsLeast A 1)
    {a b x : ℝ} (hab : a < b) (haA : a ∈ A)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hbx : b ≤ x - 1) :
    cum A (a + 1) - cum A b ≤ (1 - (b - a)) / 2 ∧
    cum A (x - 1) - cum A b ≤ (x - 1 - b) / 2 := by
  revert a b x;
  intro a b x hab haA hmax hbx
  have hDisclosure : discOn A a (a + 1) ≤ discOn A a b ∧ discOn A a (x - 1) ≤ discOn A a b := by
    apply And.intro;
    · apply discOn_le_selected_maximizer hIU <;>
        linarith [hmin.2 haA]
    · apply discOn_le_selected_maximizer hIU (by
      linarith [ hmin.2 haA ]) (by
      linarith) (by
      linarith) hmax;
  constructor;
  · apply cum_a_one_sub_cum_b_le;
    any_goals tauto;
    · linarith [ hmin.2 haA ];
    · linarith;
  · have := cum_increment_le_of_discOn_le ( show 0 ≤ a by
                                              linarith [ hmin.2 haA ] ) ( show a ≤ x - 1 by linarith ) hDisclosure.2
    generalize_proofs at *;
    unfold discOn at *;
    rw [ show cum A b = cum A a + ( volume ( A ∩ Icc a b ) |> ENNReal.toReal ) by
          rw [ ← cum_sub_cum_eq_mass_Icc ];
          · ring;
          · exact le_trans ( by norm_num ) ( hmin.2 haA );
          · linarith ] at * ; linarith

/-
The concrete restrictions in the empty branch are nonempty, so the abstract
sumset packing lemma applies without exposing interval-list witnesses.
-/
lemma empty_branch_sumset_packing_assembled
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a x y ε : ℝ} (hy : y = x + 1 - a) (hy2 : 2 < y)
    (hx : 1 ≤ x) (hε : 0 < ε)
    (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    (hxa : x - 1 ≤ a + 1) :
    (cum A (x + 1) - cum A x) + cum A (y - 1) +
      (cum A (a + 1) - cum A (x - 1)) ≤ 1 := by
  obtain ⟨ ivsB, hB ⟩ := hIU.inter_Icc_exists 0 ( y - 1 );
  obtain ⟨ ivsC, hC ⟩ := hIU.inter_Icc_exists ( x - 1 ) ( a + 1 );
  apply empty_branch_sumset_packing hsf hmin hy (by linarith) (by linarith) hB hC;
  · intro h; simp_all +decide [ IsIntervalUnion ] ;
    exact absurd hB ( Set.Nonempty.ne_empty ⟨ 1, hmin.1, by constructor <;> linarith ⟩ );
  · intro h; have := hC.2.2; simp_all +decide [ IsIntervalUnion ] ;
    exact absurd hC ( Set.Nonempty.ne_empty ⟨ x - 1, hneigh ⟨ by linarith, by linarith ⟩, by constructor <;> linarith ⟩ )

/-
The one-sided discrepancy at the last point before the first gap is bounded
by the cumulative mass at the end of that gap.
-/
lemma mMinus_le_cum_gap_end
    (hmin : IsLeast A 1) {u y : ℝ} (hu : u ≤ y - 1) :
    mMinus A u ≤ cum A (y - 1) := by
  convert Set.inter_subset_inter_left _ ( Set.inter_subset_inter_right _ ( Set.Iic_subset_Iic.mpr hu ) ) using 1;
  any_goals exact Set.Ici 0;
  simp +decide [Set.subset_def];
  constructor <;> intro h <;> simp_all +decide [ mMinus, cum ];
  · exact fun x hx₁ hx₂ => le_trans hx₂ hu;
  · refine' csSup_le _ _ <;> norm_num [ discOn ];
    · exact ⟨ _, ⟨ u, le_rfl, rfl ⟩ ⟩;
    · intro b x hx hb; rw [ hb ] ; refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc x u ⊆ A ∩ Icc 0 ( y - 1 ) from _ ) <;> norm_num;
      · rw [ two_mul ] ; gcongr;
        refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc x u ⊆ Icc x u from fun z hz => hz.2 ) _ <;> norm_num;
        rw [ ENNReal.toReal_ofReal ( sub_nonneg.mpr hx ) ];
      · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
        exact Set.Icc 0 ( y - 1 );
        · exact Set.inter_subset_right;
        · norm_num;
      · exact fun z hz => ⟨ by linarith [ hmin.2 hz.1, hz.2.1 ], by linarith [ hmin.2 hz.1, hz.2.2 ] ⟩

/-
If `A` has no point in `[b+1,x]`, the geometric estimates in the empty
branch force the paper's conclusion `y > 3`.
-/
lemma section4_y_gt_three_empty_branch
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    (hempty : A ∩ Icc (b + 1) x = ∅) :
    3 < x + 1 - a := by
  have := section4_assemble_y_gt_two_add_s hIU hsf hmin hx hxright hfail hab hbtop haA hbA hbal hmax hε hneigh;
  by_contra h_contra;
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u ∈ A ∧ u < x - a ∧ 3 * cum A (b - 1) ≤ b - 2 - ((b - a) + discOn A a b) / 2 + mMinus A u := by
    apply section4_assemble_small_case_bound hIU hsf hmin hx hxright hfail hab hbtop haA hbal hmax hε hneigh (by linarith);
  have hbase : cum A (x - 1) + 2 * cum A (b + 1) ≤ x - ((x + 1 - a) + 1) / 2 + mMinus A u + (b - a) + 2 * (cum A (a + 1) - cum A b) := by
    apply empty_branch_base_estimate hIU hsf hmin hab (by linarith) (by linarith) haA hmax hu.right.right;
  have hpack : (cum A (x + 1) - cum A x) + cum A (x + 1 - a - 1) + (cum A (a + 1) - cum A (x - 1)) ≤ 1 := by
    apply empty_branch_sumset_packing_assembled hIU hsf hmin rfl (by linarith) hx hε hneigh (by linarith);
  have hunit : cum A (a + 1) - cum A b ≤ (1 - (b - a)) / 2 := by
    apply (empty_branch_unit_long_bounds hIU hmin hab haA hmax (by linarith)).left
  have hlong : cum A (x - 1) - cum A b ≤ (x - 1 - b) / 2 := by
    apply empty_branch_unit_long_bounds hIU hmin hab haA hmax (by linarith) |>.2
  have hm : mMinus A u ≤ cum A (x + 1 - a - 1) := by
    apply mMinus_le_cum_gap_end hmin (by linarith);
  linarith [ cum_eq_of_empty_middle ( show 0 ≤ b + 1 by linarith [ hmin.1, hmin.2 haA ] ) ( show b + 1 ≤ x by linarith ) hempty ]

/-
Complete assembly of the paper's lower bound `y > 3`, splitting according
to whether `A` meets `[b+1,x]`.
-/
lemma section4_assemble_y_gt_three
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    3 < x + 1 - a := by
  by_cases hempty : A ∩ Icc ( b + 1 ) x = ∅;
  · apply section4_y_gt_three_empty_branch hIU hsf hmin hx hxright hfail hab hbtop haA hbA hbal hmax hε hneigh hempty;
  · obtain ⟨z, hzA, hzlow, hzhigh⟩ : ∃ z ∈ A, b + 1 ≤ z ∧ z ≤ x := by
      exact Set.nonempty_iff_ne_empty.mpr hempty |> fun ⟨ z, hz ⟩ => ⟨ z, hz.1, hz.2.1, hz.2.2 ⟩;
    obtain ⟨u, v, huA, hu, hu_max, hvA, hv, hv_min, huv⟩ : ∃ u v : ℝ, u ∈ A ∧ u < x + 1 - a - 1 ∧ (∀ r ∈ A, r ≤ x + 1 - a - 1 → r ≤ u) ∧ v ∈ A ∧ x + 1 - a - (b - a) < v ∧ (∀ r ∈ A, x + 1 - a - 1 ≤ r → v ≤ r) ∧ v - u ≥ 1 := by
      have := section4_assemble_long_gap hIU hsf hmin hx hxright hfail hab hbtop haA hbal hmax;
      exact this.2;
    convert section4_y_gt_three_nonempty_branch hIU hsf hmin hx hxright hfail hab hbtop haA hbal hmax _ huA hu hu_max _ hzA hzlow hzhigh using 1; all_goals grind +suggestions

end ProductFree