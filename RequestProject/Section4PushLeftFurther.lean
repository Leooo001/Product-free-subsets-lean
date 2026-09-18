import RequestProject.Section4SmallCase

/-!
# Section 4: cumulative estimates toward `y > 2+s`

This file continues the paper immediately after the small-case estimate.  It
formalizes the discrepancy comparisons and the unit-translate packing estimate
used in the proof that the maximizing interval lies to the left of `x-1`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
A bound on interval discrepancy gives the corresponding bound on an
increment of the cumulative mass.
-/
lemma cum_increment_le_of_discOn_le {p q t : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hdisc : discOn A p q ≤ t) :
    cum A q - cum A p ≤ (q - p + t) / 2 := by
  unfold discOn at hdisc;
  rw [ cum_sub_cum_eq_mass_Icc hp hpq ] ; linarith

/-
Comparison of the maximizing interval `[a,b]` with `[a,a+1]`, in the
cumulative form used twice in the paper.
-/
lemma cum_a_one_sub_cum_b_le {a b s t : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hs : s = b - a) (ht : t = discOn A a b)
    (hmax : discOn A a (a + 1) ≤ t) :
    cum A (a + 1) - cum A b ≤ (1 - s) / 2 := by
  -- Apply the lemma `cum_increment_le_of_discOn_le` with $p = a$ and $q = a + 1$.
  have h1 : cum A (a + 1) - cum A a ≤ ((a + 1 - a + t) / 2) := by
    exact le_trans ( cum_increment_le_of_discOn_le ha ( by linarith ) hmax ) ( by linarith );
  have h2 : cum A b - cum A a = (volume (A ∩ Icc a b)).toReal := by
    exact cum_sub_cum_eq_mass_Icc ha hab;
  unfold discOn at *;
  linarith

/-
Comparison of the maximizing interval `[a,b]` with `[b-1,b]`.
-/
lemma cum_a_sub_cum_b_one_le {a b s t : ℝ}
    (hb1 : 0 ≤ b - 1) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hs : s = b - a) (ht : t = discOn A a b)
    (hmax : discOn A (b - 1) b ≤ t) :
    cum A a - cum A (b - 1) ≤ (1 - s) / 2 := by
  contrapose! hmax;
  unfold discOn at *; simp_all +decide;
  rw [ ← cum_sub_cum_eq_mass_Icc, ← cum_sub_cum_eq_mass_Icc ];
  · linarith;
  · linarith;
  · linarith;
  · grind;
  · linarith

/-
If `1 ∈ A` and `A` is sum-free, the portions of `A` in a length-at-most-one
interval and in its unit translate have total mass at most the interval length.
-/
lemma unit_translate_pair_mass_le (hA : MeasurableSet A) (hsf : IsSumFree A)
    (hone : 1 ∈ A) {a b : ℝ} (hab : a ≤ b) :
    (volume (A ∩ Icc a b)).toReal +
      (volume (A ∩ Icc (a + 1) (b + 1))).toReal ≤ b - a := by
  have h_disjoint : Disjoint (A ∩ Icc a b) ((fun z => z - 1) '' (A ∩ Icc (a + 1) (b + 1))) := by
    simp_all +decide [ Set.disjoint_left, IsSumFree ];
    grind;
  have h_union_le : (volume (A ∩ Icc a b ∪ (fun z => z - 1) '' (A ∩ Icc (a + 1) (b + 1)))).toReal ≤ (volume (Icc a b)).toReal := by
    gcongr;
    · norm_num;
    · grind;
  rw [ MeasureTheory.measure_union ] at h_union_le;
  · rw [ ENNReal.toReal_add ] at h_union_le <;> norm_num at *;
    · convert h_union_le using 1;
      · rw [ volume_image_sub_const ];
      · rw [ ENNReal.toReal_ofReal ( by linarith ) ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide ) );
    · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
      exact Set.Icc a b;
      · exact Set.image_subset_iff.mpr fun x hx => ⟨ by linarith [ hx.2.1 ], by linarith [ hx.2.2 ] ⟩;
      · norm_num;
  · assumption;
  · simp +decide [ sub_eq_add_neg ];
    exact MeasurableSet.inter ( hA.preimage ( measurable_id.add_const _ ) ) measurableSet_Icc

/-
The estimate for the mass in `[b-1,b+1]` appearing in the proof of
`y > 2+s`.  The middle two pieces are controlled by unit-translate packing.
-/
lemma cum_b_one_sub_cum_b_one_le
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    {a b s : ℝ} (hb1 : 0 ≤ b - 1) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hs : s = b - a) :
    cum A (b + 1) - cum A (b - 1) ≤
      s + (cum A a - cum A (b - 1)) + (cum A (a + 1) - cum A b) := by
  have h_unit_translate_pair_mass_le : (volume (A ∩ Icc a b)).toReal + (volume (A ∩ Icc (a + 1) (b + 1))).toReal ≤ s := by
    convert unit_translate_pair_mass_le hA hsf hone hab using 1
  rw [ ← cum_sub_cum_eq_mass_Icc, ← cum_sub_cum_eq_mass_Icc ] at * <;> linarith

/-
The combined cumulative estimate reached midway through the paper's proof
of `y > 2+s`.  It packages the small-case bound, two maximal-discrepancy
comparisons, and the unit-translate estimate above.
-/
lemma cumulative_bound_toward_y_gt_two_add_s
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    {a b x y s t m : ℝ}
    (hb1 : 0 ≤ b - 1) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hbx : b ≤ x) (hs : s = b - a) (hy : y = x + 1 - a)
    (ht : t = discOn A a b)
    (hsmall : 3 * cum A (b - 1) ≤ b - 2 - (s + t) / 2 + m)
    (hmax_left : discOn A (b - 1) b ≤ t)
    (hmax_long : discOn A (b - 1) (x - 1) ≤ t) :
    cum A (x - 1) + 2 * cum A (b + 1) ≤
      x - (y + 1) / 2 + m + s + 2 * (cum A (a + 1) - cum A b) := by
  have h1 := cum_increment_le_of_discOn_le hb1 ( by linarith ) hmax_long
  have h2 := cum_a_sub_cum_b_one_le hb1 hab hba hs ht hmax_left
  have h3 := cum_b_one_sub_cum_b_one_le hA hsf hone hb1 hab hba hs;
  grind

end ProductFree