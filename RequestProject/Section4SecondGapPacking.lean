import RequestProject.Section4SecondGapAssembly
import RequestProject.Section4SecondGapPackingParts

/-!
# Section 4: the two-translate packing estimate

This file completes the proof that the gap around `x` has length at least one, by
supplying the paper's two-translate measure-packing estimate (proved in
`Section4SecondGapPackingParts.lean` as `section4_two_translate_packing_assembled`) to the
conditional assembly `section4_assemble_gap_around_x_of_packing`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- Unconditional assembly of the gap of length one around `x`. -/
theorem section4_assemble_gap_around_x
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    ∃ u' v' : ℝ,
      u' ∈ A ∧ u' ≤ x ∧ (∀ z ∈ A, z ≤ x → z ≤ u') ∧
      v' ∈ A ∧ x ≤ v' ∧ (∀ z ∈ A, x ≤ z → v' ≤ z) ∧
      1 ≤ v' - u' ∧ (∀ z ∈ Ioo u' v', z ∉ A) := by
  apply section4_assemble_gap_around_x_of_packing hIU hsf hmin hx hxleft hxright
    hfail hab hbtop haA hbA hbal hmax htpos hε hneigh
  intro u v u' v' huA hu_lt hu_gt hu_max _hvA _hv_gt hv_min huv hu'A _hu'lower hu'x
    hv'A hxv' hleftgap hshort
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  have hslt : b - a < 1 :=
    hsf.balanced_length_lt_one hIU.isCompact hmin.1 hab hbal
  have hmass : (volume (A ∩ Icc a b)).toReal = ((b - a) + discOn A a b) / 2 := by
    unfold discOn; ring
  exact section4_two_translate_packing_assembled hIU.isClosed.measurableSet hsf hmin
    hxright hy3 hab hslt hmass huA hu_lt hu_gt hu_max hv_min huv
    hu'A hu'x hv'A hxv' hleftgap hshort

end ProductFree
