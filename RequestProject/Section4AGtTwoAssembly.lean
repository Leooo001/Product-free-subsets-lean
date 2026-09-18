import RequestProject.Section4PostYThreeAssembly
import RequestProject.Section4MInterv
import RequestProject.Analytic

/-!
# Section 4: assembling the proof that `a > 2`

This file discharges the cumulative packing hypotheses isolated in
`Section4PostYThreeAssembly.lean` directly from the selected maximizing interval.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

lemma section4_a_gt_two_reflection_bound
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a : ℝ} (hxA : x + 1 ∈ A) (ha : 1 ≤ a) (ha2 : a ≤ 2) (hx : 1 ≤ x) :
    cum A x - cum A (x + 1 - a) + cum A a ≤ a - 1 := by
  have href := reflection_mass_le_interval_complement hIU.isClosed.measurableSet hsf
    (p := 1) (q := a) (c := x + 1) (a := x + 1 - a) (b := x) hxA ha
    (by ring) (by ring)
  rw [← cum_sub_cum_eq_mass_Icc (show 0 ≤ x + 1 - a by linarith) (by linarith),
    ← cum_sub_cum_eq_mass_Icc (show (0 : ℝ) ≤ 1 by norm_num) ha] at href
  rw [cum_one_eq_zero_of_isLeast hmin] at href
  linarith

lemma section4_a_gt_two_mass_bound
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a : ℝ} (ha : 1 ≤ a) (ha2 : a ≤ 2) :
    cum A (2 * a) - cum A a ≤ 1 := by
  rw [cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)]
  apply sumFree_mass_Icc_le_one hIU.isClosed.measurableSet hsf hmin.1
  linarith

lemma section4_a_gt_two_prefix_bound
    (hIU : IsIntervalUnion A ivs) (hmin : IsLeast A 1)
    {x a b : ℝ} (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    cum A a ≤ (a - 1) / 2 := by
  have ha : 1 ≤ a := hmin.2 haA
  have hdisc : discOn A 1 b ≤ discOn A a b :=
    discOn_le_selected_maximizer hIU (by norm_num) hbtop (by linarith) hmax
  unfold discOn at hdisc
  rw [← cum_sub_cum_eq_mass_Icc (show (0 : ℝ) ≤ 1 by norm_num) (by linarith),
    ← cum_sub_cum_eq_mass_Icc (by linarith) hab.le,
    cum_one_eq_zero_of_isLeast hmin] at hdisc
  linarith

lemma section4_a_gt_two_sumset_bound
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b : ℝ} (hxA : x + 1 ∈ A)
    (hab : a < b) (haA : a ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hy_a : a < x + 1 - a) :
    2 * (cum A (x + 1 - a) - cum A a) + cum A (x + 1) - cum A (2 * a)
      ≤ (x + 1 - a) - a := by
  let y := x + 1 - a
  have ha : 1 ≤ a := hmin.2 haA
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy_top : y ≤ x + 1 := by dsimp [y]; linarith
  have hm : mMinus A y = 0 := by
    apply mzero hIU.isClosed hIU.isCompact.measure_lt_top.ne hsf
      (fun z hz => le_trans zero_le_one (hmin.2 hz)) hab hy_top hbal hmax
    left
    simpa [y] using hxA
  obtain ⟨jvs, hrestrict⟩ := hIU.inter_Icc_exists a y
  have hdisc : disc (A ∩ Icc a y) ≤ discOn A a b := by
    exact le_trans (disc_mono (by grind) (by
      exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left)
        hIU.isCompact.measure_lt_top))) hmax
  have hsumlower : 2 * (volume (A ∩ Icc a y)).toReal ≤
      (volume ((A + A) ∩ Icc (2 * a) (x + 1))).toReal := by
    convert minterv_sum hIU.isClosed hIU.isCompact.measure_lt_top.ne hab hbal.1
      hrestrict hdisc using 1 <;> simp [y, hm] <;> ring
  have hdisj : Disjoint ((A + A) ∩ Icc (2 * a) (x + 1))
      (A ∩ Icc (2 * a) (x + 1)) := by
    simp only [Set.disjoint_left, mem_inter_iff]
    rintro z ⟨⟨p, hp, q, hq, rfl⟩, hz⟩ ⟨hzA, -⟩
    exact hsf hp hq hzA
  have hpack : (volume ((A + A) ∩ Icc (2 * a) (x + 1))).toReal +
      (volume (A ∩ Icc (2 * a) (x + 1))).toReal ≤ x + 1 - 2 * a := by
    have hsubset : ((A + A) ∩ Icc (2 * a) (x + 1)) ∪
        (A ∩ Icc (2 * a) (x + 1)) ⊆ Icc (2 * a) (x + 1) := by grind
    have hu : (volume (((A + A) ∩ Icc (2 * a) (x + 1)) ∪
        (A ∩ Icc (2 * a) (x + 1)))).toReal ≤ x + 1 - 2 * a := by
      refine le_trans (ENNReal.toReal_mono (ne_of_lt isCompact_Icc.measure_lt_top)
        (MeasureTheory.measure_mono hsubset)) ?_
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    rw [MeasureTheory.measure_union₀] at hu
    · rwa [ENNReal.toReal_add] at hu
      · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
          isCompact_Icc.measure_lt_top)
      · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
          isCompact_Icc.measure_lt_top)
    · exact (hIU.isClosed.measurableSet.inter measurableSet_Icc).nullMeasurableSet
    · exact MeasureTheory.measure_mono_null
        (fun z hz => Set.disjoint_left.mp hdisj hz.1 hz.2) (MeasureTheory.measure_empty)
  have hmass : cum A (x + 1) - cum A (2 * a) =
      (volume (A ∩ Icc (2 * a) (x + 1))).toReal :=
    cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)
  have hfirst : cum A (x + 1 - a) - cum A a =
      (volume (A ∩ Icc a (x + 1 - a))).toReal :=
    cum_sub_cum_eq_mass_Icc (by linarith) hy_a.le
  dsimp [y] at hsumlower
  calc
    2 * (cum A (x + 1 - a) - cum A a) + cum A (x + 1) - cum A (2 * a) =
        2 * (cum A (x + 1 - a) - cum A a) +
          (cum A (x + 1) - cum A (2 * a)) := by ring
    _ = 2 * (volume (A ∩ Icc a (x + 1 - a))).toReal +
          (volume (A ∩ Icc (2 * a) (x + 1))).toReal := by rw [hfirst, hmass]
    _ ≤ (x + 1 - a) - a := by linarith

/-- The paper's conclusion `a > 2`, fully assembled from the initial Section 4 setup. -/
lemma section4_assemble_a_gt_two
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    2 < a := by
  by_contra! ha2
  have ha : 1 ≤ a := hmin.2 haA
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  have hsum := section4_a_gt_two_sumset_bound hIU hsf hmin hxright hab haA
    hbal hmax (by linarith)
  have hreflect := section4_a_gt_two_reflection_bound hIU hsf hmin hxright ha ha2 hx
  have hmass := section4_a_gt_two_mass_bound hIU hsf hmin ha ha2
  have hprefix := section4_a_gt_two_prefix_bound hIU hmin hab hbtop haA hmax
  have hmono : cum A (x - 1) ≤ cum A (x + 1 - a) :=
    cum_mono A (by linarith)
  have ha_gt := section4_assemble_a_gt_two_of_packing_bounds hIU hsf hmin hx hxright hfail
    hab hbtop haA hbA hbal hmax htpos hε hneigh hsum hreflect hmass hprefix hmono
  linarith

end ProductFree
