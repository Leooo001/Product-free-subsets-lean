import RequestProject.Section4ULtTwo

/-!
# Section 4: `u < 2` together with the full extremal data

`section4_assemble_u_lt_two` only exports the point `u`, the strict inequality `u < 2`, and
the forced gap.  The final contradiction (`section4_fact_hprep`) also needs the remaining
extremal data around `y-1` for the *same* point `u`.  This file repackages
`section4_assemble_gap_immediately_left_of_x` together with the `u < 2` argument so that all
of that data is available at once.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- The extremal point `u` at or before `y-1`, with all its geometric data *and* `u < 2`. -/
lemma section4_assemble_u_lt_two_full
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    ∃ u v g : ℝ,
      u ∈ A ∧ u < x + 1 - a - 1 ∧ (∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u) ∧
      v ∈ A ∧ x + 1 - a - (b - a) < v ∧ (∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z) ∧
      1 ≤ v - u ∧ 0 ≤ g ∧
      2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = x + 1 - a - 3 - g ∧
      5 / 4 * (1 - discOn A a b) + g / 2 < cum A (x + 1 - a) - cum A (x + 1 - a - 2) ∧
      x + 1 - a - 2 < u ∧
      cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2 ∧
      cum A (x + 1 - a - 1) = cum A u ∧
      A ∩ Icc (u + b - 1) x = ∅ ∧ A ∩ Icc (x + (b - a) - 1) x = ∅ ∧
      u < 2 := by
  have hgapdata := section4_assemble_gap_immediately_left_of_x hIU hsf hmin hx hxleft
    hxright hfail hab hbtop haA hbA hbal hmax htpos hε hneigh
  simp only at hgapdata
  obtain ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
      hstrong, hu_gt, hreflect, hcum, hgap, hshort⟩ := hgapdata
  refine ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg, hstrong,
    hu_gt, hreflect, hcum, hgap, hshort, ?_⟩
  -- `u < 2`.
  have hmeas : MeasurableSet A := hIU.isClosed.measurableSet
  have ht : 1 / 2 < discOn A a b :=
    section4_assemble_t_gt_one_half hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh
  obtain ⟨_hdiscEq, hts, hs1, hbx, _hys, _hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  apply u_lt_two hsf hmin.1 huA
  intro h2u
  have hmono : cum A u ≤ cum A (x + 1 - a - 1) := le_of_eq hcum.symm
  have hdiff := section4_ult2_hdiff hmeas hsf hmin (b := b) (by linarith)
  have hunit := section4_ult2_hunit hmeas hsf hmin (b := b) (by linarith)
  have hyltts : x + 1 - a < 3 + (b - a) :=
    section4_ult2_y_lt_three_add_s hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh
  have hleft : cum A (x - 1) ≤ cum A (b + 1) :=
    section4_cum_mono (by linarith) (by linarith)
  have hmassx := section4_ult2_mass_near_x hIU hsf hmin hx hxleft hxright hfail hab
    hbtop haA hbA hbal hmax htpos hε hneigh
  have hright : cum A (x + 1) ≤ cum A (b + 1) + 1 := by linarith
  have hBM := section4_ult2_hBM hIU hsf hmin hx hxleft hxright hfail hab hbtop haA
    hbA hbal hmax htpos hε hneigh huA hu_lt hu_max hvA hv_gt hv_min huv hg0 hg
    hstrong hu_gt hreflect hcum hgap hshort h2u
  have hdouble := section4_ult2_hdouble hIU hsf hmin hx hxleft hxright hfail hab hbtop
    haA hbA hbal hmax htpos hε hneigh huA hu_lt hu_max hvA hv_gt hv_min huv hg0 hg
    hstrong hu_gt hreflect hcum hgap hshort h2u
  exact not_two_lt_u_of_double_boost rfl rfl hts ht hmono hdouble hdiff hunit hBM
    hleft hright hfail h2u

end ProductFree
