import RequestProject.Section4GapAroundXAssembly
import RequestProject.Section4SecondGap

/-!
# Section 4: assembling the gap of length one around `x`

This file constructs the last point of `A` at or before `x` and the first point at or
after `x`, and packages the final geometric implication needed for the paper's second
long-gap argument.  The remaining measure-packing estimate is made an explicit input.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- Construct the extremal points adjacent to `x` and prove that they are separated by
at least one from the two-translate packing upper estimate.  This isolates exactly the
measure estimate still needed to complete the paper's lemma `v' ≥ u' + 1`. -/
theorem section4_assemble_gap_around_x_of_packing
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    (hpacking : ∀ u v u' v' : ℝ,
      u ∈ A → u < x + 1 - a - 1 → x + 1 - a - 2 < u →
      (∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u) →
      v ∈ A → x + 1 - a - (b - a) < v →
      (∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z) →
      1 ≤ v - u → u' ∈ A → x - 1 ≤ u' → u' < x →
      v' ∈ A → x < v' → A ∩ Icc (u + b - 1) x = ∅ → v' - u' < 1 →
      (volume ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩
        Icc (x + 1 - a - 2) u)).toReal +
          (cum A (x + 1 - a) - cum A (x + 1 - a - 2))
        ≤ u - (x + 1 - a) + 2 + (b - a) - discOn A a b) :
    ∃ u' v' : ℝ,
      u' ∈ A ∧ u' ≤ x ∧ (∀ z ∈ A, z ≤ x → z ≤ u') ∧
      v' ∈ A ∧ x ≤ v' ∧ (∀ z ∈ A, x ≤ z → v' ≤ z) ∧
      1 ≤ v' - u' ∧ (∀ z ∈ Ioo u' v', z ∉ A) := by
  obtain ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
      hstrong, hu_gt, hreflect, hcum, hleftgap, hshortgap⟩ :=
    section4_assemble_gap_immediately_left_of_x hIU hsf hmin hx hxleft hxright
      hfail hab hbtop haA hbA hbal hmax htpos hε hneigh
  obtain ⟨u', v', hu'A, hu'x, hu'_max, hv'A, hxv', hv'_min⟩ :=
    exists_extrema_around_cut hIU.isCompact (p := x - 1) (q := x) (r := x + 1)
      hxleft hxright (by linarith) (by linarith)
  have hxnot : x ∉ A := by
    intro hxA
    exact hsf hxA hmin.1 hxright
  have hu'x_strict : u' < x := lt_of_le_of_ne hu'x (fun h => hxnot (h ▸ hu'A))
  have hxv'_strict : x < v' := lt_of_le_of_ne hxv' (fun h => hxnot (h.symm ▸ hv'A))
  have hs : b - a < 1 :=
    hsf.balanced_length_lt_one hIU.isCompact hmin.1 hab hbal
  have hts : discOn A a b ≤ b - a := discOn_le_sub A hab.le
  have hgaplen : 1 ≤ v' - u' := by
    by_contra hnot
    push_neg at hnot
    have hpack := hpacking u v u' v' huA hu_lt hu_gt hu_max hvA hv_gt hv_min huv hu'A
      (hu'_max _ hxleft (by linarith)) hu'x_strict hv'A hxv'_strict hleftgap hnot
    have hupper := second_gap_strict_upper hs hts
      (lt_of_le_of_lt (by linarith [hg0]) hstrong) hpack
    have hu'_outside : u' < u + b - 1 := by
      by_contra hn
      have hu'in : u' ∈ A ∩ Icc (u + b - 1) x :=
        ⟨hu'A, le_of_not_gt hn, hu'x⟩
      rw [hleftgap] at hu'in
      exact hu'in
    have hlower := two_difference_intervals_cover_lower (a := a) (b := b)
      (u := u) (u' := u') (v' := v') (y := x + 1 - a) (s := b - a)
      rfl hs.le hu_gt.le (by linarith) (by linarith) hnot
    linarith
  refine ⟨u', v', hu'A, hu'x, hu'_max, hv'A, hxv', hv'_min, hgaplen, ?_⟩
  intro z hz hzA
  by_cases hzx : z ≤ x
  · exact (not_lt_of_ge (hu'_max z hzA hzx)) hz.1
  · exact (not_lt_of_ge (hv'_min z hzA (le_of_not_ge hzx))) hz.2

end ProductFree
