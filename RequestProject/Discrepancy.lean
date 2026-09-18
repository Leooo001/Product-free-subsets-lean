import RequestProject.Balanced

/-!
# Discrepancy and the sumset inequality (Theorem `main2`)

This file records the elementary discrepancy machinery of the paper:

* `ProductFree.discrepancy_observation` (Lemma "discrepancy observation"): if `A ∩ (A - δ) = ∅`
  then `d(A) ≤ δ`.
* `ProductFree.discrepancy_observation2` (Lemma "discrepancy observation2").
* `ProductFree.disc_nonneg`: the discrepancy of a finite-measure set is nonnegative.

These are all proved.  The sumset inequality itself is developed elsewhere: the
finite-interval-union form `offdiagonal_main2_iu` / `main2_iu` in
`RequestProject/OffdiagonalInduction.lean` (Section 3), and the measurable-set form
`main2_measurable` in `RequestProject/MainTwoBorel.lean`.  The measurable statements originally
placed in this file were **false as stated** (they omitted the necessary finiteness of the
sumset); they are commented out below with an explanation.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
**Discrepancy observation** (Lemma of the paper). If `A` is measurable and no two points of
`A` differ by exactly `δ` (i.e. `x ∈ A → x + δ ∉ A`), then `d(A) ≤ δ`.
-/
lemma discrepancy_observation (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ)
    (hdisj : ∀ x ∈ A, x + δ ∉ A) : disc A ≤ δ := by
  have h_disc_le_delta : ∀ a b : ℝ, a ≤ b → 2 * ENNReal.toReal (MeasureTheory.volume (A ∩ Set.Icc a b)) - (b - a) ≤ δ := by
    intro a b hab
    have h_union : MeasureTheory.volume (A ∩ Set.Icc a b) + MeasureTheory.volume ((fun x => x + δ) ⁻¹' (A ∩ Set.Icc a b)) ≤ MeasureTheory.volume (Set.Icc (a - δ) b) := by
      rw [ ← MeasureTheory.measure_union ];
      · refine' MeasureTheory.measure_mono _;
        grind;
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hdisj x hx₁.1 <| by aesop;
      · exact MeasurableSet.preimage ( hA.inter measurableSet_Icc ) ( measurable_id.add_const δ );
    -- Since $A$ is measurable, we have $volume ((fun x => x + δ) ⁻¹' (A ∩ Set.Icc a b)) = volume (A ∩ Set.Icc a b)$.
    have h_volume_eq : MeasureTheory.volume ((fun x => x + δ) ⁻¹' (A ∩ Set.Icc a b)) = MeasureTheory.volume (A ∩ Set.Icc a b) := by
      erw [ MeasureTheory.measure_preimage_add_right ];
    simp_all +decide [ two_mul ];
    convert ENNReal.toReal_mono _ h_union using 1 <;> norm_num [ ENNReal.toReal_ofReal ( by linarith : 0 ≤ b - ( a - δ ) ) ] ; ring;
    · rw [ ENNReal.toReal_mul, ENNReal.toReal_ofNat ];
    · ring;
  exact csSup_le ⟨ _, ⟨ 0, 0, by norm_num, rfl ⟩ ⟩ fun x hx => by rcases hx with ⟨ a, b, hab, rfl ⟩ ; exact h_disc_le_delta a b hab;

/-
**Discrepancy observation 2** (Lemma of the paper). If `A` is measurable and `|A ∩ I| ≤ δ/2`
for every interval `I` of length `δ`, then `d(A) ≤ δ`.
-/
lemma discrepancy_observation2 (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : ∀ a : ℝ, (volume (A ∩ Icc a (a + δ))).toReal ≤ δ / 2) : disc A ≤ δ := by
  by_contra h_contra;
  -- Fix `a ≤ b`. Set `m = ⌈(b - a)/δ⌉₊` (`Nat.ceil`). Cover: `Icc a b ⊆ ⋃ k ∈ Finset.range m, Icc (a + k*δ) (a + (k+1)*δ)`.
  obtain ⟨a, b, hab, h⟩ : ∃ a b : ℝ, a ≤ b ∧ 2 * (volume (A ∩ Icc a b)).toReal - (b - a) > δ := by
    contrapose! h_contra;
    exact csSup_le ⟨ _, ⟨ 0, 0, by norm_num, rfl ⟩ ⟩ fun x hx => by rcases hx with ⟨ a, b, hab, rfl ⟩ ; exact h_contra a b hab;
  set m := Nat.ceil ((b - a) / δ) with hm_def
  have hm : b - a ≤ m * δ := by
    nlinarith [ Nat.le_ceil ( ( b - a ) / δ ), mul_div_cancel₀ ( b - a ) hδ.ne' ]
  have h_cover : Icc a b ⊆ ⋃ k ∈ Finset.range m, Icc (a + k * δ) (a + (k + 1) * δ) := by
    intro x hx; simp_all +decide [ Set.subset_def ] ;
    by_cases hx_eq : x = a + m * δ;
    · use m - 1;
      rcases m with ( _ | m ) <;> norm_num at *;
      · norm_num [ show b = a by nlinarith [ Nat.ceil_eq_zero.mp hm_def.symm, mul_div_cancel₀ ( b - a ) hδ.ne' ] ] at *;
        rw [ MeasureTheory.measure_mono_null ( Set.inter_subset_right ) ( MeasureTheory.measure_singleton a ) ] at h ; norm_num at h ; linarith;
      · exact ⟨ by linarith, by linarith, by linarith ⟩;
    · use Nat.floor ((x - a) / δ);
      exact ⟨ by nlinarith [ Nat.floor_le ( show 0 ≤ ( x - a ) / δ by exact div_nonneg ( by linarith ) hδ.le ), mul_div_cancel₀ ( x - a ) hδ.ne' ], Nat.floor_lt ( div_nonneg ( by linarith ) hδ.le ) |>.2 <| by rw [ div_lt_iff₀ hδ ] ; cases lt_or_gt_of_ne hx_eq <;> nlinarith [ Nat.le_ceil ( ( b - a ) / δ ), mul_div_cancel₀ ( b - a ) hδ.ne' ], by nlinarith [ Nat.lt_floor_add_one ( ( x - a ) / δ ), mul_div_cancel₀ ( x - a ) hδ.ne' ] ⟩
  have h_sum : volume (A ∩ Icc a b) ≤ ∑ k ∈ Finset.range m, volume (A ∩ Icc (a + k * δ) (a + (k + 1) * δ)) := by
    refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_biUnion_finset_le _ _ );
    exact fun x hx => by rcases Set.mem_iUnion₂.mp ( h_cover hx.2 ) with ⟨ k, hk₁, hk₂ ⟩ ; exact Set.mem_iUnion₂.mpr ⟨ k, hk₁, hx.1, hk₂ ⟩ ;
  have h_volume : (volume (A ∩ Icc a b)).toReal ≤ ∑ k ∈ Finset.range m, (volume (A ∩ Icc (a + k * δ) (a + (k + 1) * δ))).toReal := by
    convert ENNReal.toReal_mono _ h_sum using 1 <;> norm_num [ ENNReal.toReal_sum ];
    · rw [ ENNReal.toReal_sum ];
      exact fun k hk => ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hδ ] ) );
    · exact fun x hx => ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hδ ] ) )
  have h_bound : ∑ k ∈ Finset.range m, (volume (A ∩ Icc (a + k * δ) (a + (k + 1) * δ))).toReal ≤ m * (δ / 2) := by
    exact le_trans ( Finset.sum_le_sum fun _ _ => show ( volume ( A ∩ Icc ( a + _ * δ ) ( a + ( _ + 1 ) * δ ) ) |> ENNReal.toReal ) ≤ δ / 2 from by convert hsmall ( a + ↑ ( ‹_› : ℕ ) * δ ) using 1 ; ring ) ( by norm_num )
  have h_final : 2 * (volume (A ∩ Icc a b)).toReal - (b - a) ≤ 2 * (m * (δ / 2)) - (m - 1) * δ := by
    by_cases hm_zero : m = 0;
    · norm_num [ hm_zero ] at * ; linarith;
    · nlinarith [ show ( m : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hm_zero ), Nat.ceil_lt_add_one ( show 0 ≤ ( b - a ) / δ by exact div_nonneg ( sub_nonneg.mpr hab ) hδ.le ), mul_div_cancel₀ ( b - a ) hδ.ne' ];
  linarith

/-
The discrepancy of a finite-measure set is nonnegative: the value set defining `disc`
contains `0` (take the degenerate interval `[0,0]`) and is bounded above by `2|A|`.
-/
lemma disc_nonneg (hfin : volume A ≠ ⊤) : 0 ≤ disc A := by
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume A |> ENNReal.toReal ), fun r hr => _ ⟩ ; rcases hr with ⟨ a, b, hab, rfl ⟩ ; refine' sub_le_iff_le_add.mpr _;
    exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ) zero_le_two ) ( sub_nonneg.mpr hab );
  · refine' ⟨ 0, 0, _, _ ⟩ <;> norm_num;
    exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_singleton 0 ) |> fun h => h.symm ▸ by norm_num;

/-
**Theorems `offdiagonal main2` and `main2` for measurable sets.**

These were originally stated here (for measurable sets of finite measure) as `sorry`, to be
reduced to the finite-interval-union versions.  However, **as stated they are false**: a set `A`
of finite measure can have a sumset `A + B` (or `A + A`, `A - A`) of *infinite* measure -- e.g.
`A = ⋃ₙ [n, n + 2⁻ⁿ]` has `volume A = 2` but `A + A ⊇ [0, ∞)` -- and then
`(volume (A + B)).toReal = 0`, so `2|A| + 2|B| - d(A) - d(B) ≤ 0` fails (here it is `≈ 5 ≤ 0`).
The finite-interval-union versions `offdiagonal_main2_iu` / `main2_iu`
(`RequestProject/OffdiagonalInduction.lean`) are unaffected because such sets are bounded.

The corrected measurable statement, with the necessary finiteness hypothesis on the sumset, is
proved `sorry`-free as `ProductFree.main2_measurable` in `RequestProject/MainTwoBorel.lean`.  The
original (false) statements are kept here, commented out, for the record:

```
theorem offdiagonal_main2 {B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hd : disc A = disc B) :
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B
      ≤ (volume (A + B)).toReal := by
  sorry

theorem main2 (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) :
    4 * (volume A).toReal - 2 * disc A ≤ (volume (A + A)).toReal ∧
    4 * (volume A).toReal - 2 * disc A ≤ (volume (A - A)).toReal := by
  sorry
```
-/

end ProductFree