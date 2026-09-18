import RequestProject.Section4MInterv

/-!
# Section 4: the first mass surplus and gap

This file continues the paper after the preparatory lemmas.  It isolates the numerical end of
Lemma `fx+1-fx` and proves Lemma `gapy`, the first forced gap around `y - 1`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The final numerical step of Lemma `fx+1-fx`: the difference-set estimate gives the first
hypothesis, while failure of the key inequality gives the second.
-/
lemma cum_succ_sub_gt_one_sub_disc {x t : ℝ}
    (hdiff : cum A (x - 1) + 2 * cum A x ≤ x - 1 + t)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    1 - t < cum A (x + 1) - cum A x := by
  grind +splitImp

/-
For nonnegative endpoints, an increment of `cum` is the mass in the corresponding interval
(endpoints have Lebesgue measure zero).
-/
lemma cum_sub_cum_eq_mass_Icc {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    cum A v - cum A u = (volume (A ∩ Icc u v)).toReal := by
  -- Since $0 \leq u \leq v$, we have $Icc 0 v = Icc 0 u ∪ Ioc u v$.
  have h_union : Icc 0 v = Icc 0 u ∪ Ioc u v := by
    grind;
  -- Since $Icc 0 u$ and $Ioc u v$ are disjoint, we can apply the measure union formula.
  have h_union_measure : (volume (A ∩ (Icc 0 u ∪ Ioc u v))) = (volume (A ∩ Icc 0 u)) + (volume (A ∩ Ioc u v)) := by
    rw [ ← MeasureTheory.measure_inter_add_diff _ ( show MeasurableSet ( Icc 0 u ) from measurableSet_Icc ) ];
    congr 2; all_goals grind;
  unfold cum;
  rw [ h_union, h_union_measure, ENNReal.toReal_add ] <;> norm_num;
  · rw [ MeasureTheory.measure_congr ];
    rw [ MeasureTheory.ae_eq_set ];
    constructor <;> rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] <;> norm_num;
    · exact Filter.Eventually.of_forall fun x hx₁ hx₂ hx₃ => ⟨ hx₁, le_of_lt hx₂, hx₃ ⟩;
    · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton u ) ] with x hx using fun hx' hx'' hx''' => ⟨ hx', lt_of_le_of_ne hx'' ( Ne.symm hx ), hx''' ⟩;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc 0 u ⊆ Icc 0 u from fun x hx => hx.2 ) ) ( by simp +decide ) );
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide ) )

/-
Lemma `gapy` of the paper.  If `[a,b]` has discrepancy `t` and the mass in `[x,x+1]` is greater than `1-t`, then sum-freeness forces the interval
`[y-1,y-s]` to be empty, where `s=b-a` and `y=x+1-a`.

The relation `discOn A a b = t` turns the mass of `A ∩ [a,b]` into `(s+t)/2`; its translate
by a hypothetical point of the alleged gap lies in `[x,x+1]` and is disjoint from `A`.
-/
lemma first_gap (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b x y s t : ℝ} (hab : a ≤ b) (hs : s = b - a) (hy : y = x + 1 - a)
    (ht : t = discOn A a b)
    (hmass : 1 - t < (volume (A ∩ Icc x (x + 1))).toReal) :
    A ∩ Icc (y - 1) (y - s) = ∅ := by
  contrapose! hmass; simp_all +decide [ discOn ] ;
  obtain ⟨ r, hr ⟩ := hmass;
  have h_disjoint : Disjoint (A ∩ Icc x (x + 1)) (Set.image (fun u => r + u) (A ∩ Icc a b)) := by
    simp_all +decide [ Set.disjoint_left, IsSumFree ];
    grind;
  have h_measure : (volume (A ∩ Icc x (x + 1))).toReal + (volume (Set.image (fun u => r + u) (A ∩ Icc a b))).toReal ≤ 1 := by
    rw [ ← ENNReal.toReal_add ];
    · rw [ ← MeasureTheory.measure_union ] <;> norm_num [ h_disjoint ];
      · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc x ( x + 1 ) ∪ ( fun x => -r + x ) ⁻¹' A ∩ Icc ( a + r ) ( b + r ) ⊆ Set.Icc x ( x + 1 ) from _ ) _ <;> norm_num;
        grind;
      · convert h_disjoint using 1 ; ext ; aesop;
      · exact MeasurableSet.inter ( hA.preimage ( measurable_const.add measurable_id' ) ) ( measurableSet_Icc );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( fun u => r + u ) '' ( A ∩ Icc a b ) ⊆ Set.Icc ( r + a ) ( r + b ) from Set.image_subset_iff.mpr fun u hu => by constructor <;> linarith [ hu.2.1, hu.2.2 ] ) ) ( by simp +decide [ Real.volume_Icc ] ) );
  have h_measure_image : (volume (Set.image (fun u => r + u) (A ∩ Icc a b))).toReal = (volume (A ∩ Icc a b)).toReal := by
    rw [ Set.image_add_left ];
    rw [ MeasureTheory.measure_preimage_add ];
  linarith [ show ( volume ( A ∩ Icc a b ) |> ENNReal.toReal ) ≤ b - a by exact le_trans ( ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( show A ∩ Icc a b ⊆ Icc a b from fun x hx => hx.2 ) ) ) ( by simp +decide [ hab ] ) ]

/-
`first_gap` with its mass-surplus hypothesis supplied by the conclusion of
`cum_succ_sub_gt_one_sub_disc`.
-/
lemma first_gap_of_cum (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b x y s t : ℝ} (hx : 0 ≤ x) (hab : a ≤ b) (hs : s = b - a)
    (hy : y = x + 1 - a) (ht : t = discOn A a b)
    (hsurplus : 1 - t < cum A (x + 1) - cum A x) :
    A ∩ Icc (y - 1) (y - s) = ∅ := by
  convert first_gap hA hsf hab hs hy ht _ using 1;
  convert hsurplus using 1;
  rw [ cum_sub_cum_eq_mass_Icc hx ( by linarith ) ]

/-
The paper's immediate lemma after the first gap: once `y > 1+s`, the gap
`[y-1,y-s]` and `1 ∈ A` force `y > 2`.
-/
lemma y_gt_two_of_first_gap {y s : ℝ} (hone : 1 ∈ A) (hys : 1 + s < y)
    (hgap : A ∩ Icc (y - 1) (y - s) = ∅) :
    2 < y := by
  contrapose! hgap;
  exact ⟨ 1, hone, by constructor <;> linarith ⟩

end ProductFree