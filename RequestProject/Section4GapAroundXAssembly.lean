import RequestProject.Section4PostAMassAssembly
import RequestProject.Section4GapAroundX

/-!
# Section 4: assembling the forced gap immediately to the left of `x`

This file combines the post-`a > 2` mass assembly with the local translate-packing
argument to obtain the paper's next forced empty interval.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- After the mass estimate near `y` and the conclusion `y - 2 < u`, the local
packing argument forces `A ∩ [u+b-1,x]` to be empty.  The theorem retains all
extremal data needed by the subsequent construction of the gap around `x`. -/
theorem section4_assemble_gap_immediately_left_of_x
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    let s := b - a
    let t := discOn A a b
    let y := x + 1 - a
    ∃ u v g : ℝ,
      u ∈ A ∧ u < y - 1 ∧ (∀ z ∈ A, z ≤ y - 1 → z ≤ u) ∧
      v ∈ A ∧ y - s < v ∧ (∀ z ∈ A, y - 1 ≤ z → v ≤ z) ∧
      1 ≤ v - u ∧ 0 ≤ g ∧
      2 * cum A (y - 2) + (cum A (x - 1) - cum A (a + 1)) = y - 3 - g ∧
      5 / 4 * (1 - t) + g / 2 < cum A y - cum A (y - 2) ∧
      y - 2 < u ∧
      cum A y - cum A (y - 1) ≤ (s - t) / 2 ∧
      cum A (y - 1) = cum A u ∧
      A ∩ Icc (u + b - 1) x = ∅ ∧
      A ∩ Icc (x + s - 1) x = ∅ := by
  dsimp only
  obtain ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0,
      hg, hstrong, hu_gt, hreflect, hcum⟩ :=
    section4_assemble_mass_near_y_and_u hIU hsf hmin hx hxleft hxright hfail
      hab hbtop haA hbA hbal hmax htpos hε hneigh
  obtain ⟨_hdiscEq, hts, hs1, _hbx, _hys, _hmass⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have hgap : A ∩ Icc (u + b - 1) x = ∅ := by
    apply gap_immediately_left_of_x_full hIU.isClosed.measurableSet hsf
      (a := a) (b := b) (u := u) (x := x) (y := x + 1 - a)
      (s := b - a) (t := discOn A a b)
    · rfl
    · exact hs1.le
    · exact hts
    · rfl
    · linarith [hmin.2 huA, hu_lt]
    · exact hu_gt.le
    · exact hu_lt.le
    · ring
    · linarith [hg0]
    · exact hreflect
    · exact hcum
  have hshort : A ∩ Icc (x + (b - a) - 1) x = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' : z ∈ A ∩ Icc (u + b - 1) x :=
      ⟨hz.1, short_interval_near_x_subset hu_lt.le (by ring) hz.2⟩
    rw [hgap] at hz'
    exact hz'
  exact ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
    hstrong, hu_gt, hreflect, hcum, hgap, hshort⟩

end ProductFree
