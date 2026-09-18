import RequestProject.Section4BoostEq
import RequestProject.Section4DoubleBoost
import RequestProject.Section4GapAroundTwo
import RequestProject.Section4GapAroundXAssembly
import RequestProject.Section4TGtHalf
import RequestProject.Section4Extrema
import RequestProject.Section4Boost
import RequestProject.Section4Assembly
import RequestProject.Section4PushLeft
import RequestProject.Section4PushLeftFurther
import RequestProject.Section4SecondGapPacking
import RequestProject.Section4W
import RequestProject.Section4SmallCase
import RequestProject.Section4LongGap
import RequestProject.Section4YBound
import RequestProject.Section4MInterv
import RequestProject.Section4MZero
import RequestProject.Section4ContradictionAux
import RequestProject.Section4YThreeEmpty
import RequestProject.Section4UGtYMinusTwo
import RequestProject.Section4PostAMassAssembly
import RequestProject.Section4YThreeDifference
import RequestProject.Section4YLessThanThreePlusS
import RequestProject.Section4BMDiff
import RequestProject.Section4CLem
import RequestProject.Section4DoubleBoostAssembly

/-!
# Section 4: forcing `u < 2`

This file assembles the paper's subsection "Forcing `u < 2`".  Starting from the geometric
data around `y-1` (the extremal point `u`) and the gap around `x`, together with the boost
equation (`section4_assemble_boost_eq`), the gap around `2`, and the double-boost estimate,
the argument forces the last point `u` of `A` below `y-1` to satisfy `u < 2`.

The main export is `section4_assemble_u_lt_two`, which also carries the forced gap
`A ∩ [u+b-1,x] = ∅` used by the final contradiction.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- The difference-set packing on `[1,b-1]`: since `(A-A) ∩ [1,b-1]` is disjoint from
`A ∩ [1,b-1]` (sum-freeness) and both lie in `[1,b-1]`, and `F(b-1) = |A ∩ [1,b-1]|`. -/
lemma section4_ult2_hdiff
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {b : ℝ} (hb : 2 ≤ b) :
    (volume ((A - A) ∩ Icc 1 (b - 1))).toReal + cum A (b - 1) ≤ b - 2 := by
  have hpack := diff_mass_add_mass_le_length hA hsf (show (1 : ℝ) ≤ b - 1 by linarith)
  have hcum : (volume (A ∩ Icc 1 (b - 1))).toReal = cum A (b - 1) := by
    rw [← cum_sub_cum_eq_mass_Icc (by norm_num) (by linarith),
      cum_one_eq_zero_of_isLeast hmin, sub_zero]
  linarith [hcum ▸ hpack]

/-- The unit-translate bound: `F(b+1) - F(b-1) ≤ 1`, from the sum-free packing of the two
unit intervals `[b-1,b]` and `[b,b+1]`. -/
lemma section4_ult2_hunit
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {b : ℝ} (hb : 1 ≤ b - 1) :
    cum A (b + 1) - cum A (b - 1) ≤ 1 := by
  have h := unit_translate_pair_mass_le hA hsf hmin.1 (a := b - 1) (b := b)
    (by linarith)
  rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith),
    ← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)] at h
  have e1 : b - 1 + 1 = b := by ring
  rw [e1] at h
  -- h : (F b - F (b-1)) + (F (b+1) - F b) ≤ b - (b-1) = 1
  linarith

/-- **The upper bound `y < 3 + s`.**  In the remaining branch of the argument the interval
`[a,b]` is close enough to `x` that `y = x + 1 - a < 3 + s`, where `s = b - a`. -/
lemma section4_ult2_y_lt_three_add_s
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    x + 1 - a < 3 + (b - a) := by
  obtain ⟨_hdisc, hts, hs1, hbx, _hys, hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  obtain ⟨g, hg0, hgId, hboost⟩ :=
    section4_assemble_boost_eq_with_id hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh
  obtain ⟨w, hw0, hw1, hwmem, _hwgap, hwineq⟩ :=
    exists_w_with_inequality hIU.isCompact hsf hmin ha2 (le_of_lt hab) (by linarith)
      rfl rfl hts hg0 hboost
  have hc_bound := c_lem_bound hIU hsf hmin hab hbal haA hmax hxleft hgId
  exact y_lt_three_add_s hIU.isCompact hsf hmin
    (fun z hz => le_trans zero_le_one (hmin.2 hz)) hIU.isCompact.measure_lt_top.ne
    (le_of_lt hab) (by linarith) rfl rfl hmassIcc hxleft rfl hw0 hw1 hwmem hboost
    hwineq hc_bound

/-- **Mass near `x`.**  The gap of length one around `x` (`section4_assemble_gap_around_x`)
forces `F(x+1) - F(x-1) ≤ 1`. -/
lemma section4_ult2_mass_near_x
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    cum A (x + 1) - cum A (x - 1) ≤ 1 := by
  obtain ⟨u', v', hu'A, hu'x, hu'max, hv'A, hxv', hv'min, huv', hgap'⟩ :=
    section4_assemble_gap_around_x hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  rw [cum_sub_cum_eq_mass_Icc (show (0:ℝ) ≤ x - 1 by linarith) (by linarith)]
  have key : A ∩ Icc (x - 1) (x + 1) ⊆ Icc (x - 1) u' ∪ Icc v' (x + 1) := by
    rintro z ⟨hzA, hz1, hz2⟩
    rcases le_or_gt z u' with h | h
    · exact Or.inl ⟨hz1, h⟩
    · rcases le_or_gt v' z with h' | h'
      · exact Or.inr ⟨h', hz2⟩
      · exact absurd hzA (hgap' z ⟨h, h'⟩)
  have hm : volume (A ∩ Icc (x - 1) (x + 1)) ≤
      volume (Icc (x - 1) u') + volume (Icc v' (x + 1)) :=
    le_trans (measure_mono key) (measure_union_le _ _)
  rw [Real.volume_Icc, Real.volume_Icc] at hm
  have htop : volume (A ∩ Icc (x - 1) (x + 1)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      (by simp [Real.volume_Icc]))
  have h2 : (volume (A ∩ Icc (x - 1) (x + 1))).toReal ≤
      (ENNReal.ofReal (u' - (x - 1))).toReal + (ENNReal.ofReal (x + 1 - v')).toReal := by
    rw [← ENNReal.toReal_add (by simp) (by simp)]
    exact ENNReal.toReal_mono (by simp) hm
  rcases le_or_gt (x - 1) u' with hcu | hcu <;>
    rcases le_or_gt v' (x + 1) with hcv | hcv <;>
    simp_all [ENNReal.toReal_ofReal, le_of_lt] <;> nlinarith [hu'x, hxv', huv']

/-- **The double-boost estimate.**  Assuming `2 < u`, combining the gap around `y-1` with the
gap around `2` yields
`2 F(b-1) + s + t - F(u) ≤ |(A-A) ∩ [1,b-1]|`. -/
lemma section4_ult2_hdouble
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    {u v g : ℝ} (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hvA : v ∈ A) (hv_gt : x + 1 - a - (b - a) < v)
    (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z) (huv : 1 ≤ v - u)
    (hg0 : 0 ≤ g)
    (hg : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = x + 1 - a - 3 - g)
    (hstrong : 5 / 4 * (1 - discOn A a b) + g / 2 < cum A (x + 1 - a) - cum A (x + 1 - a - 2))
    (hu_gt : x + 1 - a - 2 < u)
    (hreflect : cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2)
    (hcum : cum A (x + 1 - a - 1) = cum A u)
    (hgap : A ∩ Icc (u + b - 1) x = ∅) (hshort : A ∩ Icc (x + (b - a) - 1) x = ∅)
    (h2u : 2 < u) :
    2 * cum A (b - 1) + (b - a) + discOn A a b - cum A u ≤
      (volume ((A - A) ∩ Icc 1 (b - 1))).toReal := by
  have hmeas : MeasurableSet A := hIU.isClosed.measurableSet
  have hAfin : volume A ≠ ⊤ := hIU.isCompact.measure_lt_top.ne
  have hAnonneg : A ⊆ Ici 0 := fun z hz => le_trans zero_le_one (hmin.2 hz)
  have ha1 : 1 ≤ a := hmin.2 haA
  obtain ⟨_hdisc, hts, hs1, hbx, _hys, hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  -- The upper bound `y < 3 + s`, and the small-case conclusion `v ≤ a`.
  have hysmall : x + 1 - a < 3 + (b - a) :=
    section4_ult2_y_lt_three_add_s hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh
  have hv_le_a : v ≤ a :=
    small_case_left_endpoint_ge hIU.isClosed hmin hab rfl (by linarith) rfl hysmall
      hbal htpos huv hu_max hv_min hε hneigh
  -- The boost equation (its `g`) drives the gap around `2`.
  obtain ⟨g', hg0', hgId', hboost'⟩ :=
    section4_assemble_boost_eq_with_id hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh
  -- Extremal points of `A` around `2`.
  obtain ⟨u₂, v₂, hu2A, hu2le2, hu2max, hv2A, hv2ge2, hv2min⟩ :=
    exists_extrema_around_cut hIU.isCompact hmin.1 haA (by norm_num) (le_of_lt ha2)
  have hu2_ge1 : 1 ≤ u₂ := hmin.2 hu2A
  have hv2_le_u : v₂ ≤ u := hv2min u huA (by linarith)
  -- The gap `(u₂, v₂)` has length at least `s`.
  have hmass_cum : cum A b - cum A a = ((b - a) + discOn A a b) / 2 := by
    rw [cum_sub_cum_eq_mass_Icc (by linarith) hab.le]; exact hmassIcc
  have hboost_gap : (b - a) - discOn A a b + g'
      < (volume (A ∩ Icc (a - 2) (b - 2))).toReal :=
    boost_transfer_bound hmeas hsf hmin.1 (by linarith) hab.le rfl (by linarith)
      (by linarith) hmass_cum hboost'
  obtain ⟨-, -, hlen⟩ :=
    gap_around_two hmeas hsf hab.le rfl hg0' hmassIcc hboost_gap hu2A hu2le2 hv2A hv2ge2
  have hv2u_ge_s : b - a ≤ v₂ - u₂ := by linarith
  -- The gap `(u₂, v₂)` contains no point of `A`.
  have hgapIoo : A ∩ Ioo u₂ v₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzA, hz1, hz2⟩
    rcases le_total z 2 with hz2' | hz2'
    · linarith [hu2max z hzA hz2']
    · linarith [hv2min z hzA hz2']
  -- The two unit-gap zero-mass facts.
  have hgu : (volume (A ∩ Icc u (u + (b - a)))).toReal = 0 :=
    mass_Icc_eq_zero_of_gap_extrema (by linarith) huv hu_max hv_min
  have hgu2 : (volume (A ∩ Icc u₂ (u₂ + (b - a)))).toReal = 0 := by
    have hsub : A ∩ Icc u₂ (u₂ + (b - a)) ⊆ {u₂} ∪ {v₂} := by
      rintro z ⟨hzA, hz1, hz2⟩
      by_cases h : u₂ < z
      · by_cases h' : z < v₂
        · have hz : z ∈ A ∩ Ioo u₂ v₂ := ⟨hzA, h, h'⟩
          rw [hgapIoo] at hz; simp at hz
        · exact Or.inr (Set.mem_singleton_iff.mpr
            (le_antisymm (by linarith [hv2u_ge_s]) (not_lt.mp h')))
      · exact Or.inl (Set.mem_singleton_iff.mpr (le_antisymm (not_lt.mp h) hz1))
    have hnull : volume (A ∩ Icc u₂ (u₂ + (b - a))) = 0 :=
      measure_mono_null hsub
        (measure_union_null (measure_singleton u₂) (measure_singleton v₂))
    rw [hnull]; simp
  -- `mMinus` facts.
  have hmb1 : mMinus A (b - 1) = 0 :=
    mzero hIU.isClosed hAfin hsf hAnonneg hab (by linarith) hbal hmax
      (Or.inr (by rw [show b - (b - 1) = (1 : ℝ) from by ring]; exact hmin.1))
  have hmu : mMinus A u ≤ b - a :=
    le_trans (mMinus_le_disc_truncation hAnonneg (volume_inter_Icc_ne_top A 0 (x + 1))
      (show u ≤ x + 1 by linarith)) (le_trans hmax (discOn_le_sub A hab.le))
  have hmu2 : mMinus A u₂ ≤ b - a :=
    le_trans (mMinus_le_disc_truncation hAnonneg (volume_inter_Icc_ne_top A 0 (x + 1))
      (show u₂ ≤ x + 1 by linarith)) (le_trans hmax (discOn_le_sub A hab.le))
  -- Orderings.
  have hub : u + (b - a) ≤ b - 1 := by linarith
  have huu2 : u₂ + (b - a) ≤ u := by linarith
  -- Discrepancy bounds for the three restrictions.
  have hdisc1 : disc (A ∩ Icc (u + (b - a)) (b - 1)) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by linarith) (by linarith) hmax
  have hdisc2 : disc (A ∩ Icc (u₂ + (b - a)) u) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by linarith) (by linarith) hmax
  have hdisc3 : disc (A ∩ Icc 1 u₂) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by norm_num) (by linarith) hmax
  -- The five-piece packing.
  have hfirst := double_boost_five_piece hIU hmin hab (rfl : b - a = b - a) hbal.2
    huA hu2A hu2_ge1 hmb1 hmu hmu2 hub huu2 hgu hgu2 hdisc1 hdisc2 hdisc3
  -- The two truncated-mass lower bounds.
  have htu := truncated_mass_lower_of_discOn (A := A) (a := a) (b := b) rfl rfl
    (mMinus_nonneg hAfin u) hmu
  have htu2 := truncated_mass_lower_of_discOn (A := A) (a := a) (b := b) rfl rfl
    (mMinus_nonneg hAfin u₂) hmu2
  -- `m⁻(u) + m⁻(u₂) ≤ F(u)`.
  have hm_u2 : mMinus A u₂ ≤ cum A u₂ := mMinus_le_cum hmeas hAfin hAnonneg (by linarith)
  have hm_u : mMinus A u ≤ cum A u - cum A u₂ :=
    mMinus_le_cum_sub_of_gap hAfin (by linarith) (by linarith) hv2_le_u hgapIoo
      (by linarith)
  linarith [hfirst, htu, htu2, hm_u, hm_u2]

/-- **The Brunn–Minkowski packing.**  Assuming `2 < u`, the set `A ∩ [b+1,x]` is nonempty and
Brunn–Minkowski applied to it and `A ∩ [a,b]` yields
`F(y-1) + (F(x) - F(b+1)) + (s+t)/2 ≤ y - 2`. -/
lemma section4_ult2_hBM
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    {u v g : ℝ} (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hvA : v ∈ A) (hv_gt : x + 1 - a - (b - a) < v)
    (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z) (huv : 1 ≤ v - u)
    (hg0 : 0 ≤ g)
    (hg : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = x + 1 - a - 3 - g)
    (hstrong : 5 / 4 * (1 - discOn A a b) + g / 2 < cum A (x + 1 - a) - cum A (x + 1 - a - 2))
    (hu_gt : x + 1 - a - 2 < u)
    (hreflect : cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2)
    (hcum : cum A (x + 1 - a - 1) = cum A u)
    (hgap : A ∩ Icc (u + b - 1) x = ∅) (hshort : A ∩ Icc (x + (b - a) - 1) x = ∅)
    (h2u : 2 < u) :
    cum A (x + 1 - a - 1) + (cum A x - cum A (b + 1)) + (b - a + discOn A a b) / 2 ≤
      x + 1 - a - 2 := by
  have ha1 : 1 ≤ a := hmin.2 haA
  obtain ⟨_hdisc, hts, hs1, hbx, _hys, hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  by_cases hne : (A ∩ Icc (b + 1) x).Nonempty
  · -- **Nonempty case: Brunn–Minkowski.**
    obtain ⟨ivsD, hD⟩ := hIU.inter_Icc_exists (b + 1) x
    obtain ⟨ivsE, hE⟩ := hIU.inter_Icc_exists a b
    have hDne : ivsD ≠ [] := by
      rintro rfl; exact Set.Nonempty.ne_empty hne (by simpa using hD.2.2)
    have hEne : ivsE ≠ [] := by
      rintro rfl
      exact Set.Nonempty.ne_empty (show (A ∩ Icc a b).Nonempty from ⟨a, haA, le_refl a, hab.le⟩)
        (by simpa using hE.2.2)
    obtain ⟨p0, hp0⟩ := hne
    have hb1x : b + 1 ≤ x := le_trans hp0.2.1 hp0.2.2
    have hBM := intervalUnion_add_measure_ge hD (hE.neg) hDne (neg_ivs_ne_nil hEne)
    -- The difference set lies in `[1, y-1]` and is disjoint from `A` there.
    have hpack : (volume (A ∩ Icc 1 (x + 1 - a - 1))).toReal
        + (volume ((A ∩ Icc (b + 1) x) + -(A ∩ Icc a b))).toReal
        ≤ (x + 1 - a - 1) - 1 := by
      have hsubset : (A ∩ Icc 1 (x + 1 - a - 1))
          ∪ ((A ∩ Icc (b + 1) x) + -(A ∩ Icc a b)) ⊆ Icc 1 (x + 1 - a - 1) := by
        rintro z (⟨hzA, hz⟩ | ⟨d, hdD, e, heE, rfl⟩)
        · exact hz
        · rw [Set.mem_neg] at heE
          simp only [mem_Icc]
          exact ⟨by linarith [hdD.2.1, heE.2.2], by linarith [hdD.2.2, heE.2.1]⟩
      have hdisj : Disjoint (A ∩ Icc 1 (x + 1 - a - 1))
          ((A ∩ Icc (b + 1) x) + -(A ∩ Icc a b)) := by
        rw [Set.disjoint_left]
        rintro z ⟨hzA, _⟩ ⟨d, hdD, e, heE, rfl⟩
        rw [Set.mem_neg] at heE
        exact hsf heE.1 hzA (by rw [show -e + (d + e) = d from by ring]; exact hdD.1)
      have hunionfin : volume (Icc (1 : ℝ) (x + 1 - a - 1)) ≠ ⊤ := by simp [Real.volume_Icc]
      have hDfin : volume ((A ∩ Icc (b + 1) x) + -(A ∩ Icc a b)) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono (by
          exact Set.Subset.trans (Set.subset_union_right) hsubset)) (lt_top_iff_ne_top.mpr hunionfin))
      have hA1fin : volume (A ∩ Icc 1 (x + 1 - a - 1)) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp [Real.volume_Icc]))
      have hunion_le : volume ((A ∩ Icc 1 (x + 1 - a - 1))
          ∪ ((A ∩ Icc (b + 1) x) + -(A ∩ Icc a b))) ≤ volume (Icc (1 : ℝ) (x + 1 - a - 1)) :=
        measure_mono hsubset
      rw [MeasureTheory.measure_union hdisj (by
        exact ((hIU.isCompact.inter_right isClosed_Icc).add
          ((hIU.isCompact.inter_right isClosed_Icc).neg)).measurableSet)] at hunion_le
      have := ENNReal.toReal_mono hunionfin hunion_le
      rw [ENNReal.toReal_add hA1fin hDfin, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)] at this
      linarith
    have hmD : (volume (A ∩ Icc (b + 1) x)).toReal = cum A x - cum A (b + 1) := by
      rw [← cum_sub_cum_eq_mass_Icc (by linarith) hb1x]
    have hm1y : (volume (A ∩ Icc 1 (x + 1 - a - 1))).toReal = cum A (x + 1 - a - 1) := by
      rw [← cum_sub_cum_eq_mass_Icc (by norm_num) (by linarith),
        cum_one_eq_zero_of_isLeast hmin, sub_zero]
    have hmEneg : (volume (-(A ∩ Icc a b))).toReal = (volume (A ∩ Icc a b)).toReal :=
      congr_arg _ (MeasureTheory.Measure.measure_neg _ _)
    rw [hmEneg] at hBM
    linarith [hBM, hpack, hmD, hm1y, hmassIcc]
  · -- **Empty case: contradiction.**
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exfalso
    have hmeas : MeasurableSet A := hIU.isClosed.measurableSet
    have hAfin : volume A ≠ ⊤ := hIU.isCompact.measure_lt_top.ne
    have ha2 : 2 < a :=
      section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
        hbal hmax htpos hε hneigh
    have hysmall : x + 1 - a < 3 + (b - a) :=
      section4_ult2_y_lt_three_add_s hIU hsf hmin hx hxleft hxright hfail hab hbtop
        haA hbA hbal hmax htpos hε hneigh
    have hb2 : 2 ≤ b := by linarith
    have hb1x : b + 1 ≤ x := by linarith
    have hbx1 : x - 1 ≤ b + 1 := by linarith
    -- `F(x) = F(b+1)`, `F(x-1) ≤ F(b+1)`, `F(x+1) ≤ F(b+1)+1`.
    have hcum_x_eq : cum A x - cum A (b + 1) = 0 := by
      have h := cum_sub_cum_eq_mass_Icc (A := A) (show (0:ℝ) ≤ b + 1 by linarith) hb1x
      rw [hne] at h; simpa using h
    have hcum_xm1 : cum A (x - 1) ≤ cum A (b + 1) := cum_mono A hbx1
    have hcum_xp1 : cum A (x + 1) ≤ cum A (b + 1) + 1 := by
      have hmass_ext : cum A (x + 1) - cum A (b + 1)
          = (volume (A ∩ Icc (b + 1) (x + 1))).toReal :=
        cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)
      have hsub2 : A ∩ Icc (b + 1) (x + 1) ⊆ A ∩ Icc x (x + 1) := by
        rintro z ⟨hzA, hz1, hz2⟩
        refine ⟨hzA, ?_, hz2⟩
        by_contra hlt
        push_neg at hlt
        have hz : z ∈ A ∩ Icc (b + 1) x := ⟨hzA, hz1, le_of_lt hlt⟩
        rw [hne] at hz; simp at hz
      have hle1 : (volume (A ∩ Icc (b + 1) (x + 1))).toReal ≤ 1 := by
        refine le_trans (ENNReal.toReal_mono ?_ (measure_mono hsub2)) ?_
        · exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
            (by simp [Real.volume_Icc]))
        · have := mass_inter_Icc_le A (show x ≤ x + 1 by linarith)
          simpa using this
      linarith [hmass_ext, hle1]
    -- The double boost, difference-set packing, unit bound, and `t > 1/2`.
    have hdouble := section4_ult2_hdouble hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh huA hu_lt hu_max hvA hv_gt hv_min huv hg0 hg
      hstrong hu_gt hreflect hcum hgap hshort h2u
    have hdiff := section4_ult2_hdiff hmeas hsf hmin (b := b) hb2
    have hunit := section4_ult2_hunit hmeas hsf hmin (b := b) (by linarith)
    have ht : 1 / 2 < discOn A a b :=
      section4_assemble_t_gt_one_half hIU hsf hmin hx hxleft hxright hfail hab hbtop
        haA hbA hbal hmax htpos hε hneigh
    obtain ⟨_hdiscEq, hts, _hs1, _hbx, _hys, _hmassIcc⟩ :=
      section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
    -- The gap around `2` and the bound `F(u) ≤ y - 2 - s - g`.
    obtain ⟨g', hg0', _hgId', hboost'⟩ :=
      section4_assemble_boost_eq_with_id hIU hsf hmin hx hxleft hxright hfail hab hbtop
        haA hbA hbal hmax htpos hε hneigh
    obtain ⟨u₂, v₂, hu2A, hu2le2, hu2max, hv2A, hv2ge2, hv2min⟩ :=
      exists_extrema_around_cut hIU.isCompact hmin.1 haA (by norm_num) (le_of_lt ha2)
    have hu2_ge1 : 1 ≤ u₂ := hmin.2 hu2A
    have hv2_le_u : v₂ ≤ u := hv2min u huA (by linarith)
    have hmassIcc' : (volume (A ∩ Icc a b)).toReal = ((b - a) + discOn A a b) / 2 := by
      obtain ⟨_, _, _, _, _, h⟩ :=
        section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
      exact h
    have hmass_cum : cum A b - cum A a = ((b - a) + discOn A a b) / 2 := by
      rw [cum_sub_cum_eq_mass_Icc (by linarith) hab.le]; exact hmassIcc'
    have hboost_gap : (b - a) - discOn A a b + g'
        < (volume (A ∩ Icc (a - 2) (b - 2))).toReal :=
      boost_transfer_bound hmeas hsf hmin.1 (by linarith) hab.le rfl (by linarith)
        (by linarith) hmass_cum hboost'
    obtain ⟨-, -, hlen⟩ :=
      gap_around_two hmeas hsf hab.le rfl hg0' hmassIcc' hboost_gap hu2A hu2le2 hv2A hv2ge2
    have hgapIoo : A ∩ Ioo u₂ v₂ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzA, hz1, hz2⟩
      rcases le_total z 2 with hz2' | hz2'
      · linarith [hu2max z hzA hz2']
      · linarith [hv2min z hzA hz2']
    -- `F(u) ≤ (u₂ - 1) + (u - v₂)`.
    have hcumu_le : cum A u ≤ (u₂ - 1) + (u - v₂) := by
      have hsub' : A ∩ Icc 0 u ⊆ (A ∩ Icc 1 u₂) ∪ (A ∩ Icc v₂ u) := by
        rintro z ⟨hzA, _hz0, hzu⟩
        have hz1 : 1 ≤ z := hmin.2 hzA
        by_cases h : z ≤ u₂
        · exact Or.inl ⟨hzA, hz1, h⟩
        · by_cases h' : v₂ ≤ z
          · exact Or.inr ⟨hzA, h', hzu⟩
          · push_neg at h h'
            have hz : z ∈ A ∩ Ioo u₂ v₂ := ⟨hzA, h, h'⟩
            rw [hgapIoo] at hz; simp at hz
      have hfin1 : volume (A ∩ Icc 1 u₂) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp [Real.volume_Icc]))
      have hfin2 : volume (A ∩ Icc v₂ u) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp [Real.volume_Icc]))
      calc cum A u = (volume (A ∩ Icc 0 u)).toReal := rfl
        _ ≤ (volume ((A ∩ Icc 1 u₂) ∪ (A ∩ Icc v₂ u))).toReal :=
            ENNReal.toReal_mono (by
              exact ne_of_lt (lt_of_le_of_lt (measure_union_le _ _)
                (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hfin1,
                  lt_of_le_of_ne le_top hfin2⟩))) (measure_mono hsub')
        _ ≤ (volume (A ∩ Icc 1 u₂)).toReal + (volume (A ∩ Icc v₂ u)).toReal := by
            rw [← ENNReal.toReal_add hfin1 hfin2]
            exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩)
              (measure_union_le _ _)
        _ ≤ (u₂ - 1) + (u - v₂) :=
            add_le_add (mass_inter_Icc_le A hu2_ge1) (mass_inter_Icc_le A hv2_le_u)
    -- The final numerical contradiction.
    linarith [hdouble, hdiff, hunit, hcum_x_eq, hcum_xm1, hcum_xp1, hfail, hcumu_le,
      hlen, ht, hts, hg0', hu_lt]

/-- **Forcing `u < 2`.**  The last point `u` of `A` at or before `y-1` lies below `2`, and
the previously established gap `A ∩ [u+b-1,x] = ∅` holds. -/
lemma section4_assemble_u_lt_two
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    ∃ u : ℝ, u ∈ A ∧ u < 2 ∧ A ∩ Icc (u + b - 1) x = ∅ := by
  have hgapdata := section4_assemble_gap_immediately_left_of_x hIU hsf hmin hx hxleft
    hxright hfail hab hbtop haA hbA hbal hmax htpos hε hneigh
  simp only at hgapdata
  obtain ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
      hstrong, hu_gt, hreflect, hcum, hgap, hshort⟩ := hgapdata
  refine ⟨u, huA, ?_, hgap⟩
  -- Now prove `u < 2`.
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
  -- The seven geometric estimates feeding `not_two_lt_u_of_double_boost`.
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
