import RequestProject.Section4PushLeftFurther

/-!
# Section 4: pushing the maximizing interval left of `x - 1`

This file completes the paper's proof of the inequality `y > 2 + s`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The one-dimensional Brunn--Minkowski inequality for two nonempty finite unions of
finite closed intervals.
-/
lemma intervalUnion_add_measure_ge
    {B C : Set ℝ} {ivsB ivsC : List (ℝ × ℝ)}
    (hB : IsIntervalUnion B ivsB) (hC : IsIntervalUnion C ivsC)
    (hBne : ivsB ≠ []) (hCne : ivsC ≠ []) :
    (volume B).toReal + (volume C).toReal ≤ (volume (B + C)).toReal := by
  -- Since $B$ and $C$ are compact, we can apply Brunn--Minkowski.
  have h_compact : IsCompact B ∧ IsCompact C := by
    exact ⟨ hB.isCompact, hC.isCompact ⟩;
  -- Since $B$ and $C$ are compact, we can apply the Brunn--Minkowski inequality.
  have h_brunn_minkowski : (volume (B + C)).toReal ≥ (volume B).toReal + (volume C).toReal := by
    have h_compact : IsCompact B ∧ IsCompact C := h_compact
    have h_nonempty : B.Nonempty ∧ C.Nonempty := by
      exact ⟨ hB.nonempty hBne, hC.nonempty hCne ⟩
    have h_brunn_minkowski : ∀ (B C : Set ℝ), IsCompact B → IsCompact C → B.Nonempty → C.Nonempty → (volume (B + C)).toReal ≥ (volume B).toReal + (volume C).toReal := by
      intros B C hB hC hBne hCne
      have h_brunn_minkowski : (volume (B + C)).toReal ≥ (volume B).toReal + (volume C).toReal := by
        have h_compact : IsCompact B ∧ IsCompact C := ⟨hB, hC⟩
        have h_nonempty : B.Nonempty ∧ C.Nonempty := ⟨hBne, hCne⟩
        obtain ⟨a, ha⟩ : ∃ a, IsLeast B a := by
          exact h_compact.1.exists_isLeast h_nonempty.1
        obtain ⟨b, hb⟩ : ∃ b, IsGreatest C b := by
          exact h_compact.2.exists_isGreatest h_nonempty.2;
        have h_brunn_minkowski : (volume (B + C)).toReal ≥ (volume (Set.image (fun x => x + b) B)).toReal + (volume (Set.image (fun x => a + x) C)).toReal := by
          have h_brunn_minkowski : (volume (Set.image (fun x => x + b) B ∪ Set.image (fun x => a + x) C)).toReal ≥ (volume (Set.image (fun x => x + b) B)).toReal + (volume (Set.image (fun x => a + x) C)).toReal := by
            rw [ MeasureTheory.measure_union₀ ];
            · rw [ ENNReal.toReal_add ];
              · exact ne_of_lt ( h_compact.1.image ( continuous_add_right _ ) |> IsCompact.measure_lt_top );
              · exact ne_of_lt ( h_compact.2.image ( continuous_const.add continuous_id' ) |> IsCompact.measure_lt_top );
            · exact IsCompact.nullMeasurableSet ( h_compact.2.image ( continuous_const.add continuous_id' ) );
            · refine' MeasureTheory.measure_mono_null _ _;
              exact { a + b };
              · simp +decide [ Set.subset_def ];
                exact fun x hx₁ hx₂ => by linarith [ ha.2 hx₁, hb.2 hx₂ ] ;
              · norm_num;
          refine' le_trans h_brunn_minkowski ( ENNReal.toReal_mono _ _ );
          · exact ne_of_lt ( IsCompact.measure_lt_top ( h_compact.1.add h_compact.2 ) );
          · refine' MeasureTheory.measure_mono _;
            rintro x ( ⟨ y, hy, rfl ⟩ | ⟨ y, hy, rfl ⟩ ) <;> [ exact Set.add_mem_add hy ( hb.1 ) ; exact Set.add_mem_add ha.1 hy ];
        simp_all +decide [ Set.image_add_right, Set.image_add_left ]
      exact h_brunn_minkowski;
    exact h_brunn_minkowski B C h_compact.1 h_compact.2 h_nonempty.1 h_nonempty.2;
  exact h_brunn_minkowski

/-
Sum-freeness and one-dimensional Brunn--Minkowski give the packing estimate used
in the last part of the proof of `y > 2+s`.
-/
lemma sumset_packing_cumulative
    (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x y : ℝ} (hb0 : 0 ≤ b) (hby : b ≤ a + 1)
    (hy : y = x + 1 - a) (hb1x : b + 1 ≤ x + 1)
    {ivsB ivsC : List (ℝ × ℝ)}
    (hB : IsIntervalUnion (A ∩ Icc 0 (y - 1)) ivsB)
    (hC : IsIntervalUnion (A ∩ Icc b (a + 1)) ivsC)
    (hBne : ivsB ≠ []) (hCne : ivsC ≠ []) :
    cum A (x + 1) - cum A (b + 1) + cum A (y - 1) +
        (cum A (a + 1) - cum A b) ≤ x - b := by
  have h_packing : (volume (A ∩ Icc (b + 1) (x + 1))).toReal + (volume ((A ∩ Icc 0 (y - 1)) + (A ∩ Icc b (a + 1)))).toReal ≤ x - b := by
    have h_packing : (A ∩ Icc (b + 1) (x + 1)) ∪ ((A ∩ Icc 0 (y - 1)) + (A ∩ Icc b (a + 1))) ⊆ Icc (b + 1) (x + 1) := by
      rintro z ( ⟨ hzA, hz ⟩ | ⟨ u, hu, v, hv, rfl ⟩ ) <;> norm_num at *;
      · tauto;
      · constructor <;> linarith [ hmin.2 hu.1, hmin.2 hv.1 ];
    have h_packing : (volume ((A ∩ Icc (b + 1) (x + 1)) ∪ ((A ∩ Icc 0 (y - 1)) + (A ∩ Icc b (a + 1))))).toReal ≤ x - b := by
      refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_packing ) _ <;> norm_num [ hb1x ];
      rw [ ENNReal.toReal_ofReal ( by linarith ) ];
    rw [ MeasureTheory.measure_union₀ ] at h_packing;
    · rwa [ ENNReal.toReal_add ] at h_packing;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc ( b + 1 ) ( x + 1 ) ⊆ Icc ( b + 1 ) ( x + 1 ) from fun x hx => hx.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) );
      · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
        exact Set.Icc ( b + 1 ) ( x + 1 );
        · exact Set.Subset.trans ( Set.subset_union_right ) ‹_›;
        · norm_num;
    · have h_compact : IsCompact (A ∩ Icc 0 (y - 1)) ∧ IsCompact (A ∩ Icc b (a + 1)) := by
        exact ⟨ hB.isCompact, hC.isCompact ⟩;
      exact IsCompact.nullMeasurableSet ( h_compact.1.add h_compact.2 );
    · refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_empty );
      intro z hz; obtain ⟨ hz₁, hz₂ ⟩ := hz; obtain ⟨ u, hu, v, hv, rfl ⟩ := hz₂; simp_all +decide [ IsSumFree ] ;
  have h_packing : (volume ((A ∩ Icc 0 (y - 1)) + (A ∩ Icc b (a + 1)))).toReal ≥ (volume (A ∩ Icc 0 (y - 1))).toReal + (volume (A ∩ Icc b (a + 1))).toReal := by
    apply intervalUnion_add_measure_ge hB hC hBne hCne;
  convert le_trans _ ‹ ( volume ( A ∩ Icc ( b + 1 ) ( x + 1 ) ) |> ENNReal.toReal ) + ( volume ( A ∩ Icc 0 ( y - 1 ) + A ∩ Icc b ( a + 1 ) ) |> ENNReal.toReal ) ≤ x - b › using 1;
  rw [ cum_sub_cum_eq_mass_Icc, cum_sub_cum_eq_mass_Icc ] <;> try linarith;
  convert add_le_add_left h_packing ( volume ( A ∩ Icc ( b + 1 ) ( x + 1 ) ) |> ENNReal.toReal ) using 1 ; ring;
  · unfold cum; ring;
  · ring

/-
The paper's lemma `y > 2+s`: under the cumulative estimates obtained from the
small-case argument, maximal discrepancy, and sumset packing, the maximizing interval
lies strictly to the left of `x-1`.
-/
lemma y_gt_two_add_s
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x y s t m u : ℝ}
    (hb1 : 0 ≤ b - 1) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hbx : b ≤ x) (hs : s = b - a) (hy : y = x + 1 - a)
    (ht : t = discOn A a b)
    (hsmall : 3 * cum A (b - 1) ≤ b - 2 - (s + t) / 2 + m)
    (hmax_left : discOn A (b - 1) b ≤ t)
    (hmax_long : discOn A (b - 1) (x - 1) ≤ t)
    (hmax_unit : discOn A a (a + 1) ≤ t)
    (hu : u ≤ y - 1) (hm : m ≤ cum A u)
    {ivsB ivsC : List (ℝ × ℝ)}
    (hB : IsIntervalUnion (A ∩ Icc 0 (y - 1)) ivsB)
    (hC : IsIntervalUnion (A ∩ Icc b (a + 1)) ivsC)
    (hBne : ivsB ≠ []) (hCne : ivsC ≠ [])
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    2 + s < y := by
  have H2 := sumset_packing_cumulative hsf hmin (by linarith) (by linarith) hy
    (by linarith) hB hC hBne hCne
  generalize_proofs at *;
  -- By assumption, $cum(x) \leq cum(b+1)$.
  have Hcumx_le_cum ebp1 : ∀ z, z ≤ ebp1 → cum A z ≤ cum A ebp1 := by
    intro z hz
    have Hcum_mono : cum A z ≤ cum A ebp1 := by
      apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
      · exact Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right hz
    generalize_proofs at *;
    exact Hcum_mono
  generalize_proofs at *;
  by_cases hy_le_2_s : y ≤ 2 + s;
  · have Hcumx_le_cum : cum A x ≤ cum A (b + 1) := by
      exact Hcumx_le_cum _ _ ( by linarith )
    generalize_proofs at *;
    have Hcum_a_one_sub_cum_b_le : cum A (a + 1) - cum A b ≤ (1 - s) / 2 := by
      grind +suggestions
    generalize_proofs at *;
    have := cumulative_bound_toward_y_gt_two_add_s hA hsf hmin.1 hb1 hab hba hbx hs hy ht hsmall hmax_left hmax_long;
    linarith [ ‹∀ ebp1 z : ℝ, z ≤ ebp1 → cum A z ≤ cum A ebp1› ( y - 1 ) u hu ];
  · linarith

end ProductFree