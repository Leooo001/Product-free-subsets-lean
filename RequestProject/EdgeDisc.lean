import RequestProject.BalancedSum

/-!
# Edge discrepancies `d_L` and `d_R`

This file introduces the *left* and *right* edge discrepancies of a set (Definition
"edge discrepancy" in the paper), used in Corollary `key_bound` and the proof of
`offdiagonal_main2`.

For a (compact, nonempty) set `A` with `min A = sInf A` and `max A = sSup A`:

* `discR A = max_{x ≤ max A} d_A([x, max A])`  (right discrepancy);
* `discL A = max_{x ≥ min A} d_A([min A, x])`  (left discrepancy).

Both are nonnegative (take the degenerate interval at the endpoint) and bounded above by `d(A)`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-- Right edge discrepancy `d_R(A) = max_{x ≤ max A} d_A([x, max A])`. -/
noncomputable def discR (A : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x, x ≤ sSup A ∧ r = discOn A x (sSup A)}

/-- Left edge discrepancy `d_L(A) = max_{x ≥ min A} d_A([min A, x])`. -/
noncomputable def discL (A : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x, sInf A ≤ x ∧ r = discOn A (sInf A) x}

/-- The value set defining `disc A` is bounded above (by `2|A|`) when `A` has finite measure. -/
lemma disc_bddAbove (hfin : volume A ≠ ⊤) :
    BddAbove {r : ℝ | ∃ a b : ℝ, a ≤ b ∧ r = 2 * (volume (A ∩ Icc a b)).toReal - (b - a)} := by
  refine ⟨2 * (volume A).toReal, ?_⟩
  rintro r ⟨a, b, hab, rfl⟩
  have : (volume (A ∩ Icc a b)).toReal ≤ (volume A).toReal :=
    ENNReal.toReal_mono hfin (measure_mono (Set.inter_subset_left))
  nlinarith [sub_nonneg.mpr hab]

/-
`d_R(A) ≤ d(A)`.
-/
lemma discR_le_disc (hfin : volume A ≠ ⊤) : discR A ≤ disc A := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ sSup A, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ x, hx, rfl ⟩;
    convert discOn_le_disc hfin hx using 1

/-
`d_L(A) ≤ d(A)`.
-/
lemma discL_le_disc (hfin : volume A ≠ ⊤) : discL A ≤ disc A := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ sInf A, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ x, hx, rfl ⟩;
    convert discOn_le_disc hfin hx using 1

/-
`0 ≤ d_R(A)`.
-/
lemma discR_nonneg (hfin : volume A ≠ ⊤) : 0 ≤ discR A := by
  refine' le_csSup _ _;
  · obtain ⟨ M, hM ⟩ := disc_bddAbove hfin;
    exact ⟨ M, by rintro r ⟨ x, hx, rfl ⟩ ; exact hM ⟨ x, sSup A, hx, rfl ⟩ ⟩;
  · refine' ⟨ sSup A, le_rfl, _ ⟩ ; unfold discOn ; norm_num;
    exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.NoAtoms.measure_singleton ( sSup A ) ) |> fun h => h.symm ▸ by norm_num;

/-
`0 ≤ d_L(A)`.
-/
lemma discL_nonneg (hfin : volume A ≠ ⊤) : 0 ≤ discL A := by
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume A |> ENNReal.toReal ), fun r hr => _ ⟩;
    obtain ⟨ x, hx₁, rfl ⟩ := hr;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc ( sInf A ) x ⊆ A from Set.inter_subset_left ) zero_le_two );
    · exact sub_le_self _ ( by linarith );
    · assumption;
  · refine' ⟨ sInf A, le_rfl, _ ⟩;
    unfold discOn;
    by_cases h : sInf A ∈ A <;> simp +decide [ h ]

end ProductFree