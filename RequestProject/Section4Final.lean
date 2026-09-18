import RequestProject.Section4PrepUSmall

/-!
# Section 4: the final contradiction

This file formalizes the last algebraic assembly in the proof of the key lemma.  The hypotheses
are the estimates established in the preceding geometric steps: equation `prep u small`, equation
`w ineq`, the three-piece packing in `[a,a+1]`, the discrepancy identity on `[a,b]`, the final
unit-translate packing, and the equality of cumulative masses across the forced gap to the left
of `x`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The closing calculation of Section 4: all estimates forced by a hypothetical counterexample
combine to prove the key inequality at that same point.
-/
theorem section4_final_key_inequality
    {a b x s t w : ℝ}
    (hprep : cum A (x - 1) + cum A (a - 2) + cum A (x + 1) ≤
      x + t + cum A 2 - 3)
    (hw : cum A a - cum A (a - 2) ≤ 1 - cum A (2 - w))
    (hthree : cum A 2 - cum A (2 - w) + (s + t) / 2 +
      (cum A (a + 1) - cum A b) ≤ 1)
    (hmass : cum A b - cum A a = (s + t) / 2)
    (hunit : cum A (b + 1) - cum A (a + 1) ≤ (s - t) / 2)
    (hst : s + t ≤ 2)
    (hgap : cum A x = cum A (b + 1)) :
    cum A (x - 1) + cum A x + cum A (x + 1) ≤ x := by
  grind +splitIndPred

/-
Consequently the estimates in the final paragraph are incompatible with the point `x`
being a counterexample to the key inequality.
-/
theorem section4_final_contradiction
    {a b x s t w : ℝ}
    (hprep : cum A (x - 1) + cum A (a - 2) + cum A (x + 1) ≤
      x + t + cum A 2 - 3)
    (hw : cum A a - cum A (a - 2) ≤ 1 - cum A (2 - w))
    (hthree : cum A 2 - cum A (2 - w) + (s + t) / 2 +
      (cum A (a + 1) - cum A b) ≤ 1)
    (hmass : cum A b - cum A a = (s + t) / 2)
    (hunit : cum A (b + 1) - cum A (a + 1) ≤ (s - t) / 2)
    (hst : s + t ≤ 2)
    (hgap : cum A x = cum A (b + 1))
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) : False := by
  grind

end ProductFree
