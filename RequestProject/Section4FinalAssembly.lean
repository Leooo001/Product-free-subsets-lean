import RequestProject.Section4Assembly
import RequestProject.Section4YThreeEmpty
import RequestProject.Section4AGtTwoAssembly
import RequestProject.Section4PostAGtTwoAssembly
import RequestProject.Section4PostAMassAssembly
import RequestProject.Section4GapAroundXAssembly
import RequestProject.Section4SecondGapAssembly
import RequestProject.Section4SecondGapPacking
import RequestProject.Section4Final
import RequestProject.Section4W
import RequestProject.Section4DoubleBoost
import RequestProject.Section4PrepUSmall
import RequestProject.Section4GapAroundTwo
import RequestProject.Section4Extrema
import RequestProject.Section4Boost
import RequestProject.Section4MInterv
import RequestProject.Section4MZero
import RequestProject.Section4YBound
import RequestProject.Section4PushLeftFurther
import RequestProject.Section4BoostEq
import RequestProject.Section4ULtTwo
import RequestProject.Section4ULtTwoFull
import RequestProject.Section4ContradictionAux
import RequestProject.Section4PrepUSmallAssembly
import RequestProject.OffdiagonalInduction

/-!
# Section 4: assembling the final contradiction

This file assembles the geometric estimates developed in the `Section4*` modules into the
final contradiction of the paper (Lemma "key lemma").  The starting point is a positive
discrepancy-maximizing interval `[a,b]` with `a > 2`, together with the gap of length one
around `x`.  The paper's closing calculation is packaged in
`ProductFree.section4_final_contradiction`; here we produce each of the seven estimates it
consumes:

* `hmass`   : `F(b) - F(a) = (s+t)/2`;
* `hst`     : `s + t ≤ 2`;
* `hunit`   : `F(b+1) - F(a+1) ≤ (s-t)/2`  (the unit-translate packing);
* `hgap`    : `F(x) = F(b+1)`  (the gap immediately to the left of `x`);
* `hw`      : `F(a) - F(a-2) ≤ 1 - F(2-w)`  (equation "w ineq");
* `hthree`  : the three-piece packing in `[a,a+1]`;
* `hprep`   : equation "prep u small".

The parameters are `s = b - a`, `t = disc_A[a,b]`, `y = x + 1 - a`.
-/

open MeasureTheory Set

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
The common geometric data available after the assembled proof of `y > 3`.
-/
lemma section4_after_y_three
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    disc (A ∩ Icc 0 (x + 1)) = discOn A a b ∧
      b - a < 1 ∧ b < x ∧
      1 - discOn A a b < cum A (x + 1) - cum A x ∧
      2 + (b - a) < x + 1 - a ∧ 3 < x + 1 - a ∧
      ∃ u v : ℝ,
        u ∈ A ∧ u < (x + 1 - a) - 1 ∧
        (∀ z ∈ A, z ≤ (x + 1 - a) - 1 → z ≤ u) ∧
        v ∈ A ∧ (x + 1 - a) - (b - a) < v ∧
        (∀ z ∈ A, (x + 1 - a) - 1 ≤ z → v ≤ z) ∧
        1 ≤ v - u := by
  refine' ⟨ _, _, _, _, _, _ ⟩;
  any_goals linarith [ section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax ];
  · exact section4_assemble_first_gap hIU hsf hmin hx hfail hab hbtop haA hbal hmax |>.2.2.2.1;
  · exact section4_assemble_y_gt_two_add_s hIU hsf hmin hx hxright hfail hab hbtop haA hbA hbal hmax hε hneigh;
  · have := section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA hbal hmax hε hneigh;
    exact ⟨ this, by have := section4_assemble_long_gap hIU hsf hmin hx hxright hfail hab hbtop haA hbal hmax; aesop ⟩

/-
Normalized parameter identities and inequalities used by the remainder of Section 4.
-/
lemma section4_normalized_parameters
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    let s := b - a
    let t := discOn A a b
    let y := x + 1 - a
    0 < s ∧ s < 1 ∧ 0 < t ∧ t ≤ s ∧ 3 < y ∧
      (volume (A ∩ Icc a b)).toReal = (s + t) / 2 ∧
      cum A b - cum A a = (s + t) / 2 ∧
      A ∩ Icc (y - 1) (y - s) = ∅ := by
  obtain ⟨ hs₁, hs₂, hs₃, hs₄, hs₅, hs₆ ⟩ := section4_after_y_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA hbal hmax hε hneigh;
  refine' ⟨ by linarith, hs₂, htpos, _, hs₆.1, _, _, _ ⟩;
  · exact discOn_le_sub A ( by linarith [ hmin.1, hmin.2 haA ] );
  · unfold discOn at *; linarith;
  · rw [ cum_sub_cum_eq_mass_Icc ];
    · unfold discOn; ring;
    · linarith [ hmin.2 haA ];
    · linarith;
  · exact section4_assemble_first_gap hIU hsf hmin hx hfail hab hbtop haA hbal hmax |>.2.2.2.2

/-- **The unit-translate packing.**  Since `1 ∈ A`, the translate `1 + (A ∩ [a,b])` lies in
`[a+1,b+1]` and is disjoint from `A`, giving `F(b+1) - F(a+1) ≤ (s-t)/2`. -/
lemma section4_fact_hunit
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    cum A (b + 1) - cum A (a + 1) ≤ (b - a - discOn A a b) / 2 := by
  obtain ⟨hs0, hs1, ht0, hts, hy3, hmassIcc, hmass, hgapmid⟩ :=
    section4_normalized_parameters hIU hsf hmin hx hxright hfail hab hbtop haA hbA hbal hmax htpos hε hneigh
  have hmeas : MeasurableSet A := by
    obtain ⟨_, _, hA⟩ := hIU
    rw [hA]
    exact Set.Finite.measurableSet_biUnion (List.finite_toSet ivs) fun p hp => measurableSet_Icc
  have hone : 1 ∈ A := hmin.1
  have ha1 : 1 ≤ a := hmin.2 haA
  have h_unit_mass := unit_translate_pair_mass_le hmeas hsf hone (by linarith : a ≤ b)
  have hmass2 : cum A (b + 1) - cum A (a + 1) = (volume (A ∩ Icc (a + 1) (b + 1))).toReal :=
    cum_sub_cum_eq_mass_Icc (by linarith : 0 ≤ a + 1) (by linarith : a + 1 ≤ b + 1)
  rw [hmass2]
  rw [hmassIcc] at h_unit_mass
  linarith

/-- **The gap immediately left of `x`.**  Once `u < 2`, the previously established gap
`A ∩ [u+b-1,x] = ∅` contains `[b+1,x]`, so `F(x) = F(b+1)`. -/
lemma section4_fact_hgap
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    cum A x = cum A (b + 1) := by
  have ha1 : 1 ≤ a := hmin.2 haA
  obtain ⟨_hdisc, _hts, hs1, hbx, _hys, _hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  obtain ⟨u, huA, hu2, hgap⟩ :=
    section4_assemble_u_lt_two hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  -- `b + 1 < x` since `x = a + y - 1 > a + 2` and `b = a + s < a + 1`.
  have hbx1 : b + 1 ≤ x := by linarith
  -- The gap `A ∩ [u+b-1, x] = ∅` contains `[b+1, x]` because `u < 2`.
  have hempty : A ∩ Icc (b + 1) x = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have : z ∈ A ∩ Icc (u + b - 1) x :=
      ⟨hz.1, ⟨by linarith [hz.2.1], hz.2.2⟩⟩
    rw [hgap] at this
    exact this
  exact cum_eq_of_empty_middle (by linarith) hbx1 hempty

/-- **Equation "w ineq" together with the three-piece packing in `[a,a+1]`.**  There is a
point `a-2+w ∈ A` (`0 ≤ w ≤ 1`) such that both the `w`-inequality
`F(a) - F(a-2) ≤ 1 - F(2-w)` and the three-piece packing
`F(2) - F(2-w) + (s+t)/2 + (F(a+1) - F(b)) ≤ 1` hold. -/
lemma section4_fact_w
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    ∃ w : ℝ, cum A a - cum A (a - 2) ≤ 1 - cum A (2 - w) ∧
      cum A 2 - cum A (2 - w) + (b - a + discOn A a b) / 2 +
        (cum A (a + 1) - cum A b) ≤ 1 := by
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  obtain ⟨_hdisc, hts, hs1, hbx, _hys, hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  obtain ⟨g, hg0, hboost⟩ :=
    section4_assemble_boost_eq hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  obtain ⟨w, hw0, hw1, hwmem, hwgap, hwineq⟩ :=
    exists_w_with_inequality hIU.isCompact hsf hmin ha2 (le_of_lt hab) (by linarith)
      rfl rfl hts hg0 hboost
  refine ⟨w, hwineq, ?_⟩
  have hmass : cum A b - cum A a = (b - a + discOn A a b) / 2 := by
    rw [cum_sub_cum_eq_mass_Icc (by linarith [hmin.2 haA]) (le_of_lt hab)]; exact hmassIcc
  have h3 := three_piece_packing_a hIU.isClosed.measurableSet hsf hw0 hw1
    (by linarith) hwmem
  linarith [h3, hmass]

/-- **Equation "prep u small".**  `F(x-1) + F(a-2) + F(x+1) ≤ x + t + F(2) - 3`. -/
lemma section4_fact_hprep
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    cum A (x - 1) + cum A (a - 2) + cum A (x + 1) ≤
      x + discOn A a b + cum A 2 - 3 := by
  obtain ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
      hstrong, hu_gt, hreflect, hcum, hgap, hshort, hu2⟩ :=
    section4_assemble_u_lt_two_full hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh
  obtain ⟨u', v', hu'A, hu'x, hu'max, hv'A, hxv', hv'min, huv', hgap'⟩ :=
    section4_assemble_gap_around_x hIU hsf hmin hx hxleft hxright hfail hab hbtop
      haA hbA hbal hmax htpos hε hneigh
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  have hdiffeq := diff_eq_bound hIU hsf (show (2 : ℝ) ≤ a by linarith)
    (show a ≤ x + 1 by linarith) hmax
  apply prep_u_small_all_cases (a := a) (x := x) (y := x + 1 - a)
    (t := discOn A a b) (u' := u') (v' := v') (v := v) (by ring) hy3 hdiffeq
    ?case1 ?case2 ?case3
  case case1 =>
    exact section4_hprep_case1 hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh huA hu_lt hu_max hvA hv_gt hv_min huv hg0 hg hstrong
      hu_gt hreflect hcum hgap hshort hu2 hu'A hu'x hu'max hv'A hxv' hv'min huv' hgap'
      hy3 ha2 hdiffeq
  case case2 =>
    exact section4_hprep_case2 hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh huA hu_lt hu_max hvA hv_gt hv_min huv hg0 hg hstrong
      hu_gt hreflect hcum hgap hshort hu2 hu'A hu'x hu'max hv'A hxv' hv'min huv' hgap'
      hy3 ha2 hdiffeq
  case case3 =>
    exact section4_hprep_case3 hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh huA hu_lt hu_max hvA hv_gt hv_min huv hg0 hg hstrong
      hu_gt hreflect hcum hgap hshort hu2 hu'A hu'x hu'max hv'A hxv' hv'min huv' hgap'
      hy3 ha2 hdiffeq

/-- The geometric Section 4 chain, starting from a positive discrepancy-maximizing interval,
produces the final contradiction. -/
lemma section4_contradiction_from_initial_setup
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    {ε : ℝ} (hε : 0 < ε)
    (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) : False := by
  obtain ⟨hs0, hs1, ht0, hts, hy3, hmassIcc, hmass, hgapmid⟩ :=
    section4_normalized_parameters hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  obtain ⟨w, hw, hthree⟩ :=
    section4_fact_w hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA hbal hmax
      htpos hε hneigh
  refine section4_final_contradiction (a := a) (b := b) (x := x)
    (s := b - a) (t := discOn A a b) (w := w)
    (section4_fact_hprep hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA hbal hmax
      htpos hε hneigh)
    hw hthree hmass
    (section4_fact_hunit hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA hbal hmax
      htpos hε hneigh)
    (by linarith) ?_ hfail
  exact section4_fact_hgap hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA hbal hmax
    htpos hε hneigh

end ProductFree
