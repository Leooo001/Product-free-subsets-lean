import RequestProject.Section4AGtTwoAssembly
import RequestProject.Section4GapAroundX
import RequestProject.Section4MInterv

/-!
# Section 4: assembly immediately after `a > 2`

This file connects the selected maximizing interval to the difference-set and direct
sumset packings used after the proof that `a > 2`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- The two difference-set packing inequalities following the proof of `a > 2`. -/
lemma section4_post_a_difference_bounds
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {x a b : ℝ} (hab : a < b) (hbtop : b ≤ x + 1)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (ha2 : 2 < a) :
    2 * (cum A (x - 1) - cum A (x + 1 - a)) + cum A (a - 2)
        ≤ a - 2 + discOn A a b ∧
      2 * (cum A (x + 1) - cum A (x + 1 - a)) + cum A a
        ≤ a + discOn A a b := by
  have hfin : volume (A ∩ Icc 0 (x + 1)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      hIU.isCompact.measure_lt_top)
  have hy0 : 0 ≤ x + 1 - a := by
    linarith
  constructor
  · apply restricted_difference_packing hIU hsf hy0 (by linarith) (by linarith)
      (by linarith)
    exact disc_restriction_le_maximizer hfin hy0 (by linarith) hmax
  · apply restricted_difference_packing hIU hsf hy0 (by linarith) (by linarith)
      (by linarith)
    exact disc_restriction_le_maximizer hfin hy0 (by linarith) hmax

/-- The direct sumset packing in `[a+1,x-1]` following the proof of `a > 2`. -/
lemma section4_post_a_direct_packing
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b : ℝ} (hxleft : x - 1 ∈ A)
    (hab : a < b)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (ha2 : 2 < a) (hy3 : 3 < x + 1 - a) :
    2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1))
      ≤ x + 1 - a - 3 := by
  let y := x + 1 - a
  have hz1 : 1 ≤ y - 2 := by dsimp [y]; linarith
  have hz_top : y - 2 ≤ x + 1 := by dsimp [y]; linarith
  have hm : mMinus A (y - 2) = 0 := by
    apply mzero hIU.isClosed hIU.isCompact.measure_lt_top.ne hsf
      (fun z hz => le_trans zero_le_one (hmin.2 hz)) hab hz_top hbal hmax
    left
    convert hxleft using 1 <;> dsimp [y] <;> ring
  obtain ⟨jvs, hrestrict⟩ := hIU.inter_Icc_exists 1 (y - 2)
  have hfin : volume (A ∩ Icc 0 (x + 1)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
      hIU.isCompact.measure_lt_top)
  have hdisc : disc (A ∩ Icc 1 (y - 2)) ≤ discOn A a b :=
    disc_restriction_le_maximizer hfin (by norm_num) hz_top hmax
  have hsumlower : 2 * (volume (A ∩ Icc 1 (y - 2))).toReal ≤
      (volume ((A + A) ∩ Icc (a + 1) (x - 1))).toReal := by
    convert minterv_sum hIU.isClosed hIU.isCompact.measure_lt_top.ne hab hbal.1
      hrestrict hdisc using 1 <;> simp [y, hm] <;> ring_nf
  have hdisj : Disjoint ((A + A) ∩ Icc (a + 1) (x - 1))
      (A ∩ Icc (a + 1) (x - 1)) := by
    simp only [Set.disjoint_left, mem_inter_iff]
    rintro z ⟨⟨p, hp, q, hq, rfl⟩, hz⟩ ⟨hzA, -⟩
    exact hsf hp hq hzA
  have hpack : (volume ((A + A) ∩ Icc (a + 1) (x - 1))).toReal +
      (volume (A ∩ Icc (a + 1) (x - 1))).toReal ≤ x - a - 2 := by
    have hsubset : ((A + A) ∩ Icc (a + 1) (x - 1)) ∪
        (A ∩ Icc (a + 1) (x - 1)) ⊆ Icc (a + 1) (x - 1) := by grind
    have hu := ENNReal.toReal_mono
      (ne_of_lt (show volume (Icc (a + 1) (x - 1)) < ⊤ from isCompact_Icc.measure_lt_top))
      (MeasureTheory.measure_mono hsubset)
    rw [MeasureTheory.measure_union₀] at hu
    · rw [ENNReal.toReal_add, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)] at hu
      · linarith
      · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
          isCompact_Icc.measure_lt_top)
      · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
          isCompact_Icc.measure_lt_top)
    · exact (hIU.isClosed.measurableSet.inter measurableSet_Icc).nullMeasurableSet
    · exact MeasureTheory.measure_mono_null
        (fun z hz => Set.disjoint_left.mp hdisj hz.1 hz.2) (MeasureTheory.measure_empty)
  have hfirst : (volume (A ∩ Icc 1 (y - 2))).toReal = cum A (y - 2) := by
    rw [← cum_sub_cum_eq_mass_Icc (show (0 : ℝ) ≤ 1 by norm_num) hz1,
      cum_one_eq_zero_of_isLeast hmin, sub_zero]
  have hsecond : (volume (A ∩ Icc (a + 1) (x - 1))).toReal =
      cum A (x - 1) - cum A (a + 1) := by
    rw [← cum_sub_cum_eq_mass_Icc] <;> linarith
  dsimp [y] at hsumlower hpack hfirst
  rw [hfirst] at hsumlower
  rw [hsecond] at hpack
  linarith

end ProductFree
