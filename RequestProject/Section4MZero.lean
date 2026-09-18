import RequestProject.Section4Rigidity

/-!
# Section 4: the core of Lemma `mzero`

This file formalizes the additive-combinatorial heart of the paper's next preparatory lemma.
A positive-discrepancy left-balanced interval ending at `z`, together with a discrepancy-maximizing
balanced interval `[a,b]`, forces both `a+z` and `b-z` to lie outside a sum-free set.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

lemma mzero_sum_membership (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b r z : ℝ} (hab : a < b) (hrz : r < z)
    (hI : IsLeftBalanced A a b) (hJ : IsLeftBalanced A r z)
    (hdisc : disc (A ∩ Icc r z) ≤ discOn A a b) :
    a + z ∈ (A ∩ Icc a b) + (A ∩ Icc r z) := by
  have hmass : 0 ≤ 2 * (volume (A ∩ Icc r z)).toReal - (z - r) := by
    exact hJ.2 z hrz.le le_rfl;
  have := @ProductFree.main_step_sums_left A (A ∩ Icc r z);
  specialize this hA (hA.inter isClosed_Icc) hAfin ( ne_top_of_le_ne_top hAfin <| MeasureTheory.measure_mono <| Set.inter_subset_left ) hab hrz hI (by
  exact restrict_leftBalanced hA.measurableSet hJ) hdisc;
  simp_all +decide [ Set.inter_assoc ];
  exact this ⟨ by linarith, by linarith ⟩

lemma mzero_diff_membership (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b r z : ℝ} (hab : a < b) (hrz : r < z)
    (hI : IsRightBalanced A a b) (hJ : IsLeftBalanced A r z)
    (hdisc : disc (A ∩ Icc r z) ≤ discOn A a b)
    (hpos : 0 < discOn A r z) :
    z - b ∈ (A ∩ Icc r z) - (A ∩ Icc a b) := by
  convert Set.mem_of_subset_of_mem ( main_step hA ( hA.inter isClosed_Icc ) hAfin _ hab ( show r < z from hrz ) hI ( restrict_leftBalanced ( hA.measurableSet ) hJ ) hdisc ) _ using 1;
  · ext; simp [Set.mem_sub, Set.mem_inter_iff];
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
  · simp_all +decide [ Set.inter_assoc, Set.inter_self ];
    unfold discOn at hpos; constructor <;> linarith;

/-
The core contradiction in Lemma `mzero` from the paper.  The hypothesis on the discrepancy
of `A ∩ [r,z]` is exactly what discrepancy-maximality of `[a,b]` supplies in the application.
-/
lemma mzero_core (hA : IsClosed A) (hAfin : volume A ≠ ⊤) (hsf : IsSumFree A)
    {a b r z : ℝ} (hab : a < b) (hrz : r < z)
    (hI : IsBalanced A a b) (hJ : IsLeftBalanced A r z)
    (hdisc : disc (A ∩ Icc r z) ≤ discOn A a b)
    (hpos : 0 < discOn A r z) :
    a + z ∉ A ∧ b - z ∉ A := by
  constructor;
  · obtain ⟨ p, hp, q, hq, hpq ⟩ := mzero_sum_membership hA hAfin hab hrz hI.1 hJ hdisc;
    exact fun h => hsf hp.1 hq.1 ( by simpa [ ← hpq ] using h );
  · intro h;
    obtain ⟨q, hq⟩ : ∃ q ∈ A ∩ Icc r z, ∃ p ∈ A ∩ Icc a b, q - p = z - b := by
      convert mzero_diff_membership hA hAfin hab hrz hI.2 hJ hdisc hpos using 1;
    obtain ⟨ p, hp, hp' ⟩ := hq.2; have := hsf h ( hq.1.1 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact this ( by convert hp.1 using 1; ring )

end ProductFree