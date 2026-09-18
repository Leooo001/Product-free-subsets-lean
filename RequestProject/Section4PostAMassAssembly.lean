import RequestProject.Section4PostAGtTwoAssembly
import RequestProject.Section4UGtYMinusTwo

/-!
# Section 4: mass near the first gap after `a > 2`

This file assembles the two difference-set bounds and the direct sumset packing into
paper's deficit `g`, the large-mass estimate on `[y-2,y]`, and the conclusion that the
last point `u` before the first forced gap satisfies `y-2 < u`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- The reflection through `x+1` bounds the mass in the last part of `[y-1,y]` by
its complementary mass in the selected interval. -/
lemma section4_mass_y_sub_one_reflection_bound
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {x a b : ℝ} (hxright : x + 1 ∈ A) (hab : a < b)
    (hs1 : b - a ≤ 1) (hy3 : 3 < x + 1 - a)
    (hgap : A ∩ Icc ((x + 1 - a) - 1) ((x + 1 - a) - (b - a)) = ∅) :
    cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤
      ((b - a) - discOn A a b) / 2 := by
  let y := x + 1 - a
  let s := b - a
  have hsubset : A ∩ Icc (y - 1) y ⊆ A ∩ Icc (y - s) y := by
    intro z hz
    refine ⟨hz.1, ?_, hz.2.2⟩
    by_contra! h
    have hzGap : z ∈ A ∩ Icc (y - 1) (y - s) :=
      ⟨hz.1, hz.2.1, le_of_lt h⟩
    have hgap' : A ∩ Icc (y - 1) (y - s) = ∅ := by
      convert hgap using 1 <;> dsimp [y, s] <;> ring
    rw [hgap'] at hzGap
    exact hzGap
  have hmass : (volume (A ∩ Icc (y - 1) y)).toReal ≤
      (volume (A ∩ Icc (y - s) y)).toReal := by
    apply ENNReal.toReal_mono
    · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
        isCompact_Icc.measure_lt_top)
    · exact MeasureTheory.measure_mono hsubset
  have href := reflection_mass_le_interval_complement hIU.isClosed.measurableSet hsf hxright
    (show y - s ≤ y by dsimp [s]; linarith)
    (show a = x + 1 - y by dsimp [y]; ring)
    (show b = x + 1 - (y - s) by dsimp [y, s]; ring)
  have hcum : cum A y - cum A (y - 1) =
      (volume (A ∩ Icc (y - 1) y)).toReal := by
    rw [cum_sub_cum_eq_mass_Icc] <;> dsimp [y] <;> linarith
  unfold discOn at *
  dsimp [y, s] at *
  linarith

/-- A greatest point of `A` before a cut carries all cumulative mass up to that cut. -/
lemma cum_eq_cum_of_greatest_before
    (hmin : IsLeast A 1)
    {u q : ℝ} (huA : u ∈ A) (huq : u ≤ q)
    (hu_max : ∀ z ∈ A, z ≤ q → z ≤ u) :
    cum A q = cum A u := by
  have hu0 : 0 ≤ u := le_trans zero_le_one (hmin.2 huA)
  have hzero : volume (A ∩ Icc u q) = 0 := by
    apply MeasureTheory.measure_mono_null (show A ∩ Icc u q ⊆ ({u} : Set ℝ) by
      intro z hz
      exact Set.mem_singleton_iff.mpr
        (le_antisymm (hu_max z hz.1 hz.2.2) hz.2.1))
    exact MeasureTheory.measure_singleton u
  have hmass : (volume (A ∩ Icc u q)).toReal = 0 := by rw [hzero]; rfl
  rw [← cum_sub_cum_eq_mass_Icc hu0 huq] at hmass
  linarith

/-- Assembly of the paragraph after `a > 2`, through the conclusion `u > y-2`. -/
theorem section4_assemble_mass_near_y_and_u
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
      cum A (y - 1) = cum A u := by
  dsimp only
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  obtain ⟨hdiscEq, hts, hs1, hbx, hys, hmass⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  obtain ⟨hy2, u, v, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv⟩ :=
    section4_assemble_long_gap hIU hsf hmin hx hxright hfail hab hbtop haA hbal hmax
  obtain ⟨hshort, hlong⟩ :=
    section4_post_a_difference_bounds hIU hsf hab hbtop hmax ha2
  have hpack := section4_post_a_direct_packing hIU hsf hmin hxleft hab hbal hmax ha2 hy3
  obtain ⟨g, hg0, hg⟩ := exists_direct_packing_deficit hpack
  have hdiscUnit : discOn A a (a + 1) ≤ discOn A a b :=
    discOn_le_selected_maximizer hIU (by linarith [hmin.2 haA]) (by linarith) (by linarith) hmax
  have hunit : cum A (a + 1) - cum A a ≤ (1 + discOn A a b) / 2 := by
    have := cum_increment_le_of_discOn_le (A := A) (p := a) (q := a + 1)
      (by linarith [hmin.2 haA]) (by linarith) hdiscUnit
    linarith
  have hsurplus : 1 - discOn A a b < cum A (x + 1) - cum A x :=
    section4_first_mass_surplus hIU hsf hmin hx hmax hfail
  have hstrong :
      5 / 4 * (1 - discOn A a b) + g / 2 <
        cum A (x + 1 - a) - cum A (x + 1 - a - 2) := by
    apply mass_near_y_gt_five_quarters (A := A) (a := a) (x := x)
      (y := x + 1 - a) (t := discOn A a b) (g := g)
    · ring
    · exact hg
    · exact hlong
    · exact hunit
    · exact hfail
    · exact hsurplus
  have hlower :
      5 / 4 * (1 - discOn A a b) <
        cum A (x + 1 - a) - cum A (x + 1 - a - 2) :=
    mass_near_y_gt_five_quarters_base hg0 hstrong
  have hgap := (section4_assemble_first_gap hIU hsf hmin hx hfail hab hbtop haA hbal hmax).2.2.2.2
  have hu_gt : x + 1 - a - 2 < u := by
    apply u_gt_y_sub_two hIU.isClosed.measurableSet hsf hxright rfl rfl rfl hab.le
      (by linarith) (by linarith) (by linarith) hu_max hgap hlower
  have hreflect :
      cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤
        ((b - a) - discOn A a b) / 2 :=
    section4_mass_y_sub_one_reflection_bound hIU hsf hxright hab (by linarith)
      hy3 hgap
  have hcum : cum A (x + 1 - a - 1) = cum A u :=
    cum_eq_cum_of_greatest_before hmin huA (by linarith) hu_max
  exact ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
    hstrong, hu_gt, hreflect, hcum⟩

end ProductFree
