import RequestProject.Section4SecondGapPacking
import RequestProject.Section4SecondGap
import RequestProject.Section4PushLeftFurther
import RequestProject.Section4YThreeEmpty
import RequestProject.Section4YThreeDifference
import RequestProject.Section4SecondGapPackingParts
import RequestProject.Section4PostAMassAssembly
import RequestProject.Section4Assembly
import RequestProject.Section4PushLeft
import RequestProject.Section4ContradictionAux

/-!
# Section 4: the inequality `t > 1/2` (Corollary "rough t bound")

Once the gap of length one around `x` has been assembled (`section4_assemble_gap_around_x`),
the paper's Corollary "rough t bound" states that the discrepancy-maximizing interval is
genuinely dense: `t = d_A[a,b] > 1/2`.

The three inputs to the numerical core `t_gt_one_half` are:

* a difference-set packing on `A ∩ [1,u']` (`Theorem offdiagonal main2` applied there,
  combined with sum-freeness), giving `2 F(x) + F(u'-1) ≤ u'-1 + t`;
* two maximal-discrepancy estimates on `[v',x+1]` and `[u'-1,x-1]`, giving
  `F(x+1) - F(x) ≤ (x-u'+t)/2` and `F(x-1) - F(u'-1) ≤ (x-u'+t)/2`.

All three use `F(x) = F(u') = F(v')`, which holds because `(u',v')` is a gap containing `x`.
-/

open MeasureTheory Set

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- **Corollary "rough t bound".**  `t = d_A[a,b] > 1/2`. -/
theorem section4_assemble_t_gt_one_half
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    1 / 2 < discOn A a b := by
  obtain ⟨u', v', hu'A, hu'x, hu'max, hv'A, hxv', hv'min, huv, _hgap⟩ :=
    section4_assemble_gap_around_x hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  -- `u' ≥ 1` and `v' ≤ x + 1`.
  have hu'ge1 : 1 ≤ u' := hmin.2 hu'A
  have hv'le : v' ≤ x + 1 := hv'min (x + 1) hxright (by linarith)
  -- The three cumulative-mass identities across the gap `(u',v')` containing `x`.
  have hFxu' : cum A x = cum A u' :=
    cum_eq_cum_of_greatest_before hmin hu'A hu'x hu'max
  have hFxv' : cum A v' = cum A x :=
    cum_eq_cum_of_least_after (by linarith) hxv' hv'min
  -- Input 1: difference-set packing on `A ∩ [1,u']`.
  have hdisc1 : disc (A ∩ Icc 1 u') ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by norm_num) (by linarith) hmax
  have hpack :=
    restricted_difference_packing hIU hsf (p := 1) (q := u') (r := u' - 1)
      (by norm_num) hu'ge1 (by linarith) (le_refl _) hdisc1
  have hcum1 : cum A 1 = 0 := cum_one_eq_zero_of_isLeast hmin
  have hdiff : 2 * cum A x + cum A (u' - 1) ≤ u' - 1 + discOn A a b := by
    rw [hFxu']; rw [hcum1] at hpack; linarith
  -- Input 2: maximal-discrepancy estimate on `[v',x+1]`.
  have hdon_r : discOn A v' (x + 1) ≤ discOn A a b :=
    discOn_le_selected_maximizer hIU (p := v') (q := x + 1)
      (by linarith) (le_refl _) (by linarith) hmax
  have hincr_r : cum A (x + 1) - cum A v' ≤ (x + 1 - v' + discOn A a b) / 2 :=
    cum_increment_le_of_discOn_le (by linarith) (by linarith) hdon_r
  have hright : cum A (x + 1) - cum A x ≤ (x - u' + discOn A a b) / 2 := by
    rw [hFxv'] at hincr_r; linarith
  -- Input 3: maximal-discrepancy estimate on `[u'-1,x-1]`.
  have hdon_l : discOn A (u' - 1) (x - 1) ≤ discOn A a b :=
    discOn_le_selected_maximizer hIU (p := u' - 1) (q := x - 1)
      (by linarith) (by linarith) (by linarith) hmax
  have hincr_l : cum A (x - 1) - cum A (u' - 1) ≤ (x - 1 - (u' - 1) + discOn A a b) / 2 :=
    cum_increment_le_of_discOn_le (by linarith) (by linarith) hdon_l
  have hleft : cum A (x - 1) - cum A (u' - 1) ≤ (x - u' + discOn A a b) / 2 := by
    linarith
  exact t_gt_one_half hdiff hright hleft hfail

end ProductFree
