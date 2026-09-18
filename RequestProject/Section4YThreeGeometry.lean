import RequestProject.Section4YThree
import RequestProject.Section4UGtYMinusTwo

/-!
# Section 4: geometric estimates for the proof that `y > 3`

This file supplies the geometric bounds entering the nonempty branch of the paper's
proof of `y > 3`.  They are separated from the final numerical lemma `y_gt_three` so
that the remaining top-level assembly can invoke them directly.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
If a point `z ∈ A` lies far enough to the right of `[a,b]`, then reflection of
`A ∩ [a,b]` through `z` packs with the initial part of `A`.  This is the first
estimate in the nonempty branch of the proof of `y > 3`.
-/
lemma cum_le_of_reflected_maximizing_interval
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b z u y s t : ℝ}
    (hzA : z ∈ A) (hab : a ≤ b)
    (hzlow : 1 ≤ z - b) (hzhigh : z - a ≤ y - 1)
    (hu : u ≤ y - 1)
    (hs : s = b - a) (ht : t = discOn A a b) :
    cum A u ≤ y - 2 - (s + t) / 2 := by
  -- By reflection, we have that the measure of the reflection of $A \cap [a, b]$ through $z$ is equal to the measure of $A \cap [a, b]$.
  have h_reflection : (volume (A ∩ Icc a b)).toReal = (s + t) / 2 := by
    rw [ hs, ht ];
    unfold discOn;
    ring;
  -- By reflection, we have that the measure of the reflection of $A \cap [a, b]$ through $z$ is disjoint from $A$ and lies in $[1, y-1]$.
  have h_reflection_disjoint : (volume ((fun r => z - r) '' (A ∩ Icc a b))).toReal + (volume (A ∩ Icc 0 u)).toReal ≤ (volume (Icc 1 (y - 1))).toReal := by
    have h_reflection_disjoint : (volume ((fun r => z - r) '' (A ∩ Icc a b) ∪ (A ∩ Icc 0 u) \ {1})).toReal ≤ (volume (Icc 1 (y - 1))).toReal := by
      gcongr;
      · norm_num;
      · simp_all +decide [ Set.subset_def ];
        rintro x ( ⟨ x, hx, rfl ⟩ | ⟨ hx, hx' ⟩ ) <;> constructor <;> linarith [ hmin.2 hx.1 ];
    rw [ MeasureTheory.measure_union ] at h_reflection_disjoint;
    · rw [ ENNReal.toReal_add ] at h_reflection_disjoint <;> norm_num at *;
      · rw [ MeasureTheory.measure_diff_null ] at h_reflection_disjoint <;> norm_num at * ; linarith;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( fun r => z - r ) '' ( A ∩ Icc a b ) ⊆ Icc ( z - b ) ( z - a ) from Set.image_subset_iff.mpr fun x hx => ⟨ by linarith [ hx.2.1, hx.2.2 ], by linarith [ hx.2.1, hx.2.2 ] ⟩ ) ) ( by simp +decide [ Real.volume_Icc ] ) );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( A ∩ Icc 0 u ) \ { 1 } ⊆ Icc 0 u from fun x hx => hx.1.2 ) ) ( by simp +decide ) );
    · simp_all +decide [ Set.disjoint_left ];
      rintro _ x hx₁ hx₂ hx₃ rfl hx₄ hx₅ hx₆; have := hsf hx₄ hx₁; simp_all +decide [ IsSumFree ] ;
    · exact MeasurableSet.diff ( hA.inter measurableSet_Icc ) ( MeasurableSingletonClass.measurableSet_singleton _ );
  have h_reflection_measure : (volume ((fun r => z - r) '' (A ∩ Icc a b))).toReal = (volume (A ∩ Icc a b)).toReal := by
    have h_reflection_measure : ∀ (S : Set ℝ), MeasurableSet S → (volume ((fun r => z - r) '' S)).toReal = (volume S).toReal := by
      intro S hS; rw [ show ( fun r => z - r ) '' S = ( fun r => -r ) '' S + { z } by ext; simp +decide [ sub_eq_add_neg, add_comm ] ; aesop ] ;
      simp +decide [ Set.add_singleton ];
    exact h_reflection_measure _ ( hA.inter measurableSet_Icc );
  simp_all +decide [ cum ];
  rw [ ENNReal.toReal_ofReal ] at h_reflection_disjoint <;> linarith

/-
Reflection through `x+1 ∈ A` sends the mass immediately to the left of `y`
into the complement of the maximizing interval.  The forced gap and extremality
of `u` identify this mass with `F(y)-F(u)`.
-/
lemma cum_y_sub_cum_u_le_complement
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u x y s t : ℝ}
    (hxA : x + 1 ∈ A) (hy : y = x + 1 - a)
    (hs : s = b - a) (ht : t = discOn A a b) (hab : a ≤ b)
    (hy0 : 0 ≤ y) (hu0 : 0 ≤ u) (hu : u < y - 1)
    (hu_max : ∀ z ∈ A, z ≤ y - 1 → z ≤ u)
    (hgap : A ∩ Icc (y - 1) (y - s) = ∅) :
    cum A y - cum A u ≤ (s - t) / 2 := by
  rw [ cum_sub_cum_eq_mass_Icc ];
  · have h_reflection : (volume (A ∩ Icc u y)).toReal ≤ (volume (A ∩ Icc (y - s) y)).toReal := by
      have h_reflection : (volume (A ∩ Ioc u y)).toReal ≤ (volume (A ∩ Icc (y - s) y)).toReal := by
        have h_reflection : A ∩ Ioc u y ⊆ A ∩ Icc (y - s) y := by
          intro z hz
          obtain ⟨hzA, hzu, hzy⟩ := hz
          by_cases hzy1 : z ≤ y - 1;
          · linarith [ hu_max z hzA hzy1 ];
          · exact ⟨ hzA, le_of_not_gt fun h => hgap.subset ⟨ hzA, ⟨ by linarith, by linarith ⟩ ⟩, hzy ⟩;
        apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
        exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc ( y - s ) y ⊆ Icc ( y - s ) y from fun x hx => hx.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) );
      convert h_reflection using 1;
      rw [ MeasureTheory.measure_congr ];
      rw [ MeasureTheory.ae_eq_set ];
      constructor <;> rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] <;> norm_num;
      · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton u ) ] with z hz using fun hz' hz'' hz''' => ⟨ hz', lt_of_le_of_ne hz'' ( Ne.symm hz ), hz''' ⟩;
      · exact Filter.Eventually.of_forall fun x hx₁ hx₂ hx₃ => ⟨ hx₁, le_of_lt hx₂, hx₃ ⟩;
    have h_reflection : (volume (A ∩ Icc (y - s) y)).toReal ≤ (y - (y - s)) - (volume (A ∩ Icc a b)).toReal := by
      have := reflection_mass_le_interval_complement hA hsf hxA ( by linarith : y - s ≤ y ) ( by linarith : a = x + 1 - y ) ( by linarith : b = x + 1 - ( y - s ) ) ; aesop;
    unfold discOn at *; linarith;
  · linarith;
  · linarith

/-- Assemble the genuinely geometric parts of the nonempty branch of `y > 3`.
The two remaining hypotheses are respectively the finite-union difference-set estimate
on `[y,x+1]` and maximal discrepancy on `[a,x-1]`. -/
lemma y_gt_three_of_point_right
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x y s t u z : ℝ}
    (hxA : x + 1 ∈ A) (hzA : z ∈ A)
    (hy : y = x + 1 - a) (hs : s = b - a) (ht : t = discOn A a b)
    (hab : a ≤ b) (hys : 2 + s < y) (hts : t ≤ s)
    (hzlow : 1 ≤ z - b) (hzhigh : z - a ≤ y - 1)
    (hu0 : 0 ≤ u) (hu : u < y - 1)
    (hu_max : ∀ r ∈ A, r ≤ y - 1 → r ≤ u)
    (hgap : A ∩ Icc (y - 1) (y - s) = ∅)
    (hdiff : 2 * (cum A (x + 1) - cum A y) + cum A a ≤ a + t)
    (hlong : cum A (x - 1) - cum A a ≤ (x - 1 - a + t) / 2)
    (hsurplus : 1 - t < cum A (x + 1) - cum A x)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    3 < y := by
  apply y_gt_three_nonempty_case hy hys hts
  · exact cum_le_of_reflected_maximizing_interval hA hsf hmin hzA hab hzlow
      hzhigh hu.le hs ht
  · exact cum_y_sub_cum_u_le_complement hA hsf hxA hy hs ht hab
      (by linarith) hu0 hu hu_max hgap
  · exact hdiff
  · exact hlong
  · exact hsurplus
  · exact hfail

end ProductFree