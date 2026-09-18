import RequestProject.Section4YBound

/-!
# Section 4: excluding `y ≤ 3`

This file formalizes the two-case numerical contradiction in the paper's proof that
`y > 3`.  The hypotheses of `y_gt_three` are precisely the estimates produced in the
two geometric cases (`A ∩ [b+1,x]` nonempty or empty); packaging the argument this way
keeps the subsequent Section 4 development independent of how interval-union witnesses
for the several restrictions are chosen.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-- The numerical contradiction in the case `A ∩ [b+1,x]` is nonempty. -/
lemma y_gt_three_nonempty_case
    {a x y s t u : ℝ}
    (hy : y = x + 1 - a)
    (hys : 2 + s < y) (hts : t ≤ s)
    (hu : cum A u ≤ y - 2 - (s + t) / 2)
    (hyu : cum A y - cum A u ≤ (s - t) / 2)
    (hdiff : 2 * (cum A (x + 1) - cum A y) + cum A a ≤ a + t)
    (hlong : cum A (x - 1) - cum A a ≤ (x - 1 - a + t) / 2)
    (hsurplus : 1 - t < cum A (x + 1) - cum A x)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    3 < y := by
  by_contra hy3
  have hstrict : 3 * y + t < 10 := by linarith
  have htwo : 2 * cum A (x + 1) + cum A (x - 1) ≤
      x - 4 + (3 * y - t) / 2 := by
    linarith
  linarith

/-- The numerical contradiction in the case `A ∩ [b+1,x]` is empty. -/
lemma y_gt_three_empty_case
    {a b x y s m : ℝ}
    (hy : y = x + 1 - a) (hs : s = b - a)
    (hFx : cum A x = cum A (b + 1))
    (hbase : cum A (x - 1) + 2 * cum A (b + 1) ≤
      x - (y + 1) / 2 + m + s + 2 * (cum A (a + 1) - cum A b))
    (hpack : (cum A (x + 1) - cum A x) + cum A (y - 1) +
      (cum A (a + 1) - cum A (x - 1)) ≤ 1)
    (hm : m ≤ cum A (y - 1))
    (hunit : cum A (a + 1) - cum A b ≤ (1 - s) / 2)
    (hlong : cum A (x - 1) - cum A b ≤ (x - 1 - b) / 2)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    3 < y := by
  by_contra hy3
  have hrel : x - 1 - b = y - s - 2 := by linarith
  linarith

/-- Paper's lemma `y > 3`, assembled from its two geometric cases.

`hcases` records the dichotomy's output.  In the nonempty branch these are the reflection,
difference-set, and maximal-discrepancy bounds; in the empty branch they are the preceding
cumulative estimate, the Brunn--Minkowski packing bound, and the two discrepancy comparisons.
-/
lemma y_gt_three
    {a b x y s t u m : ℝ}
    (hy : y = x + 1 - a) (hs : s = b - a)
    (hys : 2 + s < y) (hts : t ≤ s)
    (hsurplus : 1 - t < cum A (x + 1) - cum A x)
    (hcases :
      (cum A u ≤ y - 2 - (s + t) / 2 ∧
       cum A y - cum A u ≤ (s - t) / 2 ∧
       2 * (cum A (x + 1) - cum A y) + cum A a ≤ a + t ∧
       cum A (x - 1) - cum A a ≤ (x - 1 - a + t) / 2) ∨
      (cum A x = cum A (b + 1) ∧
       cum A (x - 1) + 2 * cum A (b + 1) ≤
         x - (y + 1) / 2 + m + s + 2 * (cum A (a + 1) - cum A b) ∧
       (cum A (x + 1) - cum A x) + cum A (y - 1) +
         (cum A (a + 1) - cum A (x - 1)) ≤ 1 ∧
       m ≤ cum A (y - 1) ∧
       cum A (a + 1) - cum A b ≤ (1 - s) / 2 ∧
       cum A (x - 1) - cum A b ≤ (x - 1 - b) / 2))
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    3 < y := by
  rcases hcases with h | h
  · exact y_gt_three_nonempty_case hy hys hts h.1 h.2.1 h.2.2.1 h.2.2.2 hsurplus hfail
  · exact y_gt_three_empty_case hy hs h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2 hfail

end ProductFree
