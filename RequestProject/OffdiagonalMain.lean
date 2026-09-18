import RequestProject.KeyBoundRight

/-!
# The off-diagonal sumset inequality: the generic case

This file assembles the "generic" (first) case of the proof of Theorem `offdiagonal_main2`.

When both `A` and `B` have a *leftmost* balanced interval starting at their minimum and a
*rightmost* balanced interval ending at their maximum, each achieving the full discrepancy, the
inequality `|A + B| ≥ 2|A| + 2|B| - d(A) - d(B)` follows directly from the two `key_bound`
corollaries by inclusion–exclusion.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

/-
Inclusion–exclusion bound: for measurable `X, Y ⊆ W` with `W` of finite measure,
`|X| + |Y| - |X ∩ Y| ≤ |W|`.
-/
lemma measure_two_incl_excl {W X Y : Set ℝ} (hX : MeasurableSet X) (hY : MeasurableSet Y)
    (hXW : X ⊆ W) (hYW : Y ⊆ W) (hWfin : volume W ≠ ⊤) :
    (volume X).toReal + (volume Y).toReal - (volume (X ∩ Y)).toReal ≤ (volume W).toReal := by
  rw [ ← ENNReal.toReal_add, ← ENNReal.toReal_sub_of_le ];
  · rw [ ← MeasureTheory.measure_union_add_inter X hY ];
    rw [ ENNReal.add_sub_cancel_right ];
    · gcongr;
      · assumption;
      · exact Set.union_subset hXW hYW;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr ( ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hXW ) ( lt_top_iff_ne_top.mpr hWfin ) ) ) ) );
  · exact le_add_right ( MeasureTheory.measure_mono ( Set.inter_subset_left ) );
  · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ lt_of_le_of_lt ( MeasureTheory.measure_mono hXW ) ( lt_top_iff_ne_top.mpr hWfin ), lt_of_le_of_lt ( MeasureTheory.measure_mono hYW ) ( lt_top_iff_ne_top.mpr hWfin ) ⟩ );
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hXW ) ( lt_top_iff_ne_top.mpr hWfin ) );
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hYW ) ( lt_top_iff_ne_top.mpr hWfin ) )

/-
**Off-diagonal sumset inequality, generic case.** If `A`, `B` are nonempty finite unions of
finite closed intervals with `d(A) = d(B)`, `A` has a balanced interval `[min A, a₁]` (positive
length) of discrepancy `d(A)`, and `B` has a balanced interval `[b_ℓ, max B]` (positive length) of
discrepancy `d(B)`, then `2|A| + 2|B| - d(A) - d(B) ≤ |A + B|`.
-/
lemma offdiagonal_case1 {A B : Set ℝ} {ivsA ivsB : List (ℝ × ℝ)}
    (hA : IsIntervalUnion A ivsA) (hB : IsIntervalUnion B ivsB)
    (hAne : ivsA ≠ []) (hBne : ivsB ≠ [])
    {a1 : ℝ} (hI1 : IsBalanced A (sInf A) a1) (ha1 : sInf A < a1)
    (hI1disc : discOn A (sInf A) a1 = disc A)
    {bl : ℝ} (hJl : IsBalanced B bl (sSup B)) (hbl : bl < sSup B)
    (hJldisc : discOn B bl (sSup B) = disc B)
    (hdAB : disc A = disc B) :
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal := by
  obtain ⟨X, hX⟩ : ∃ X : Set ℝ, X = ((A ∩ Icc (sInf A) a1) + B) ∩ Icc (sInf A + sInf B) (sInf A + sSup B + discR B) ∧ 2 * (volume B).toReal ≤ (volume X).toReal := by
    refine' ⟨ _, rfl, _ ⟩;
    apply key_bound_left A hA.isClosed hA.finite ha1 hI1.1 hB hBne;
    lia;
  obtain ⟨Y, hY⟩ : ∃ Y : Set ℝ, Y = ((B ∩ Icc bl (sSup B)) + A) ∩ Icc (sSup B + sInf A - discL A) (sSup B + sSup A) ∧ 2 * (volume A).toReal ≤ (volume Y).toReal := by
    convert key_bound_right B hB.isClosed hB.finite hbl hJl.2 hA hAne _ using 1;
    · aesop;
    · linarith;
  -- By `measure_two_incl_excl hX hY (X ⊆ A+B) (Y ⊆ A+B) hABfin`:
  have h_measure : (volume (A + B)).toReal ≥ (volume X).toReal + (volume Y).toReal - (volume (X ∩ Y)).toReal := by
    apply measure_two_incl_excl;
    · rw [ hX.1 ];
      refine' MeasurableSet.inter _ measurableSet_Icc;
      have h_compact : IsCompact (A ∩ Icc (sInf A) a1) ∧ IsCompact B := by
        exact ⟨ hA.isCompact.inter_right isClosed_Icc, hB.isCompact ⟩;
      exact IsCompact.measurableSet ( h_compact.1.add h_compact.2 );
    · have hY_compact : IsCompact (B ∩ Icc bl (sSup B) + A) := by
        apply_rules [ IsCompact.add, hB.isCompact ];
        · exact hB.isCompact.inter_right ( isClosed_Icc );
        · exact hA.isCompact;
      exact hY.1.symm ▸ MeasurableSet.inter ( hY_compact.measurableSet ) ( measurableSet_Icc );
    · simp +decide [ hX.1, Set.subset_def ];
      exact fun x hx₁ hx₂ hx₃ => Set.add_subset_add ( Set.inter_subset_left ) ( Set.Subset.refl _ ) hx₁;
    · simp_all +decide [ Set.subset_def, Set.mem_add ];
      exact fun x y hy₁ hy₂ hy₃ z hz₁ hz₂ hz₃ hz₄ => ⟨ z, hz₁, y, hy₁, by linarith ⟩;
    · have h_compact : IsCompact (A + B) := by
        exact IsCompact.add ( hA.isCompact ) ( hB.isCompact );
      exact h_compact.measure_lt_top.ne;
  -- Bound `(volume (X ∩ Y)).toReal`: `X ⊆ Icc (cA+cB) (cA+MB+discR B)` and `Y ⊆ Icc (MB+cA-discL A) (MB+MA)`, so `X ∩ Y ⊆ Icc (cA+MB - discL A) (cA+MB+discR B)`.
  have h_inter : X ∩ Y ⊆ Icc (sInf A + sSup B - discL A) (sInf A + sSup B + discR B) := by
    grind;
  -- Hence `(volume (X ∩ Y)).toReal ≤ ((cA+MB+discR B) - (cA+MB - discL A)) = discR B + discL A`.
  have h_inter_measure : (volume (X ∩ Y)).toReal ≤ (discR B + discL A) := by
    refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_inter ) _ <;> norm_num;
    rw [ ENNReal.toReal_ofReal ( add_nonneg ( discR_nonneg ( hB.finite ) ) ( discL_nonneg ( hA.finite ) ) ) ];
  linarith [ discR_le_disc hB.finite, discL_le_disc hA.finite ]

end ProductFree