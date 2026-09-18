import RequestProject.Defs

/-!
# The analytic reduction: from the key lemma to the `1/3` bound

This file contains the elementary real-analysis argument (Section 2 of the paper) that
deduces the measure bound from the key inequality `F(u-δ) + F(u) + F(u+δ) ≤ u`.

The main result is `ProductFree.integral_cum_lt_third`: if `A ⊆ [δ,∞)` with `δ > 0` and
`F` satisfies the shifted key inequality, then `∫_{u>0} e^{-u} F(u) du < 1/3`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-- The cumulative measure is nonnegative. -/
lemma cum_nonneg (A : Set ℝ) (x : ℝ) : 0 ≤ cum A x := ENNReal.toReal_nonneg

/-
The cumulative measure is monotone.
-/
lemma cum_mono (A : Set ℝ) : Monotone (cum A) := by
  intros x y hxy
  have h_subset : A ∩ Icc 0 x ⊆ A ∩ Icc 0 y := by
    exact Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right hxy
  have h_volume : volume (A ∩ Icc 0 x) ≤ volume (A ∩ Icc 0 y) := by
    exact MeasureTheory.measure_mono h_subset
  exact ENNReal.toReal_mono (by
  exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) )) h_volume

/-
For `x ≥ 0`, `F(x) = |A ∩ [0,x]| ≤ x`.
-/
lemma cum_le_self {x : ℝ} (hx : 0 ≤ x) : cum A x ≤ x := by
  -- Apply the fact that the volume of a subset is less than or equal to the volume of the superset.
  have h_volume_le : volume (A ∩ Icc 0 x) ≤ volume (Icc 0 x) := by
    exact MeasureTheory.measure_mono <| Set.inter_subset_right;
  convert ENNReal.toReal_mono _ h_volume_le using 1 <;> norm_num [ hx ]

/-
If `A ⊆ [δ,∞)` and `x ≤ δ`, then `A ∩ [0,x]` has measure zero, so `F(x) = 0`.
-/
lemma cum_eq_zero_of_le {δ x : ℝ} (hAδ : A ⊆ Ici δ) (hx : x ≤ δ) : cum A x = 0 := by
  by_contra h_contra;
  -- Since $A \subseteq [δ,∞)$, we have $A ∩ [0,x] \subseteq [δ,x]$.
  have h_subset : A ∩ Icc 0 x ⊆ Icc δ x := by
    exact fun y hy => ⟨ hAδ hy.1, hy.2.2 ⟩;
  exact h_contra <| by rw [ show cum A x = ( volume ( A ∩ Icc 0 x ) |> ENNReal.toReal ) by rfl ] ; rw [ show volume ( A ∩ Icc 0 x ) = 0 by exact MeasureTheory.measure_mono_null h_subset ( by rw [ Real.volume_Icc ] ; aesop ) ] ; norm_num;

/-
The integrand `u ↦ e^{-u} F(u)` is integrable on `(0,∞)`.
-/
lemma cum_integrableOn (A : Set ℝ) :
    IntegrableOn (fun u => Real.exp (-u) * cum A u) (Ioi (0:ℝ)) := by
      -- We can bound the function $u \mapsto e^{-u} F(u)$ by $g(u) = e^{-u} u$, which is integrable on $Ioi 0$.
      have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * u) (Set.Ioi 0) := by
        have h_gamma : ∫ u in Set.Ioi 0, Real.exp (-u) * u = Real.Gamma 2 := by
          rw [ Real.Gamma_eq_integral ] <;> norm_num;
        exact ( by contrapose! h_gamma; rw [ MeasureTheory.integral_undef h_gamma ] ; positivity );
      refine' h_integrable.mono' _ _;
      · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
        · exact Continuous.aestronglyMeasurable ( by continuity );
        · refine' Monotone.measurable ( cum_mono A ) |> fun h => h.aestronglyMeasurable.restrict;
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( cum_nonneg _ _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( cum_le_self hu.out.le ) ( Real.exp_pos _ |> le_of_lt ) ;

/-
`∫_{u>0} u e^{-u} du = 1` (this is `Γ(2) = 1`).
-/
lemma integral_id_mul_exp_neg : ∫ u in Ioi (0:ℝ), Real.exp (-u) * u = 1 := by
  convert integral_rpow_mul_exp_neg_rpow zero_lt_one ( by norm_num : ( -1 : ℝ ) < 1 ) using 1;
  · norm_num [ mul_comm ];
  · norm_num

/-
Shift-by-`(-δ)` identity: `∫_{u>0} e^{-u} F(u-δ) du = e^{-δ} ∫_{u>0} e^{-u} F(u) du`.
-/
lemma integral_cum_shift_left {δ : ℝ} (hδ : 0 < δ) (hAδ : A ⊆ Ici δ) :
    (∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A (u - δ))
      = Real.exp (-δ) * ∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A u := by
        rw [ ← MeasureTheory.integral_const_mul ];
        convert MeasureTheory.integral_indicator ( measurableSet_Ioi ) using 1;
        rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        rw [ ← MeasureTheory.integral_add_right_eq_self _ δ ] ; congr ; ext x ; split_ifs <;> simp_all +decide [ ← mul_assoc, ← Real.exp_add ] ; ring;
        any_goals try infer_instance;
        · exact cum_eq_zero_of_le hAδ ( by linarith );
        · linarith

/-
Shift-by-`(+δ)` identity: `∫_{u>0} e^{-u} F(u+δ) du = e^{δ} ∫_{u>0} e^{-u} F(u) du`.
-/
lemma integral_cum_shift_right {δ : ℝ} (hδ : 0 < δ) (hAδ : A ⊆ Ici δ) :
    (∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A (u + δ))
      = Real.exp δ * ∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A u := by
        have step1 : ∫ u in Ioi 0, Real.exp (-u) * cum A (u + δ) = ∫ v in Ioi δ, Real.exp (-v) * cum A v * Real.exp δ := by
          rw [ ← MeasureTheory.integral_indicator ( measurableSet_Ioi ), ← MeasureTheory.integral_indicator ( measurableSet_Ioi ) ];
          rw [ ← MeasureTheory.integral_sub_right_eq_self _ δ ] ; congr with x ; simp +decide [ Set.indicator ] ; ring;
          rw [ sub_eq_add_neg, Real.exp_add ] ; ring;
        convert step1 using 1;
        rw [ ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        congr with x ; split_ifs <;> ring;
        · rw [ cum_eq_zero_of_le hAδ ( by linarith ), MulZeroClass.mul_zero ];
        · linarith

/-
The core analytic estimate. If `A ⊆ [δ,∞)` with `δ > 0`, and `F` satisfies the shifted
key inequality `F(u-δ) + F(u) + F(u+δ) ≤ u` for all `u ≥ 0`, then
`∫_{u>0} e^{-u} F(u) du < 1/3`.

(Note: the inequality is only required for `u ≥ 0`; for `u < 0` it is false, since the
left-hand side is nonnegative while the right-hand side is negative.)
-/
theorem integral_cum_lt_third {δ : ℝ} (hδ : 0 < δ) (hAδ : A ⊆ Ici δ)
    (hkey : ∀ u : ℝ, 0 ≤ u → cum A (u - δ) + cum A u + cum A (u + δ) ≤ u) :
    (∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A u) < 1/3 := by
      -- By integrable properties, we have:
      have h_integrable : IntegrableOn (fun u => Real.exp (-u) * cum A (u - δ)) (Ioi 0) ∧ IntegrableOn (fun u => Real.exp (-u) * cum A u) (Ioi 0) ∧ IntegrableOn (fun u => Real.exp (-u) * cum A (u + δ)) (Ioi 0) := by
        refine' ⟨ _, _, _ ⟩;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun u => Real.exp ( -u ) * u;
          · have := @integral_id_mul_exp_neg;
            exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num );
          · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
            · exact Continuous.aestronglyMeasurable ( by continuity );
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.ennreal_toReal _;
              convert ( Monotone.measurable ( show Monotone fun u => volume ( A ∩ Icc 0 ( u - δ ) ) from fun u v huv => MeasureTheory.measure_mono <| Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right <| by linarith ) ) using 1;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu;
            rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( cum_nonneg _ _ ) ) ];
            exact mul_le_mul_of_nonneg_left ( le_trans ( le_add_of_nonneg_right <| cum_nonneg _ _ ) <| le_trans ( le_add_of_nonneg_right <| cum_nonneg _ _ ) <| hkey u hu.out.le ) <| Real.exp_pos _ |> le_of_lt;
        · exact ProductFree.cum_integrableOn A;
        · refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun u => Real.exp ( -u ) * ( u + δ );
          · have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.exp (-u) * u) (Set.Ioi 0) := by
              have := @integral_id_mul_exp_neg;
              exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num );
            simp_all +decide [ mul_add ];
            exact MeasureTheory.Integrable.add h_integrable ( MeasureTheory.Integrable.mul_const ( MeasureTheory.integrable_of_integral_eq_one ( by rw [ integral_exp_neg_Ioi ] ; norm_num ) ) _ );
          · refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
            · exact Continuous.aestronglyMeasurable ( by continuity );
            · refine' Measurable.aestronglyMeasurable _;
              refine' Measurable.ennreal_toReal _;
              convert ( Monotone.measurable ( show Monotone fun u => volume ( A ∩ Icc 0 ( u + δ ) ) from fun u v huv => MeasureTheory.measure_mono <| Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right <| by linarith ) ) using 1;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using by rw [ Real.norm_of_nonneg ( mul_nonneg ( Real.exp_pos _ |> le_of_lt ) ( cum_nonneg _ _ ) ) ] ; exact mul_le_mul_of_nonneg_left ( cum_le_self ( by linarith [ hu.out ] ) ) ( Real.exp_pos _ |> le_of_lt ) ;
      -- Applying the linearity of the integral, we have:
      have h_integral_sum : (∫ u in Ioi 0, Real.exp (-u) * cum A (u - δ)) + (∫ u in Ioi 0, Real.exp (-u) * cum A u) + (∫ u in Ioi 0, Real.exp (-u) * cum A (u + δ)) ≤ (∫ u in Ioi 0, Real.exp (-u) * u) := by
        rw [ ← MeasureTheory.integral_add, ← MeasureTheory.integral_add ];
        · refine' MeasureTheory.setIntegral_mono_on _ _ measurableSet_Ioi fun u hu => by nlinarith [ hkey u hu.out.le, Real.exp_pos ( -u ) ] ;
          · exact MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add h_integrable.1 h_integrable.2.1 ) h_integrable.2.2;
          · have := @integral_id_mul_exp_neg;
            exact ( by contrapose! this; rw [ MeasureTheory.integral_undef this ] ; norm_num );
        · exact MeasureTheory.Integrable.add h_integrable.1 h_integrable.2.1;
        · exact h_integrable.2.2;
        · exact h_integrable.1;
        · exact h_integrable.2.1;
      rw [ integral_cum_shift_left hδ hAδ, integral_cum_shift_right hδ hAδ ] at h_integral_sum ; nlinarith [ Real.add_one_lt_exp hδ.ne', Real.add_one_lt_exp ( neg_ne_zero.mpr hδ.ne' ), Real.exp_pos δ, Real.exp_pos ( -δ ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos δ ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( -δ ) ) ), Real.exp_neg δ, integral_id_mul_exp_neg ] ;

end ProductFree