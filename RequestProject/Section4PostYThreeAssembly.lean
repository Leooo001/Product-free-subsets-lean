import RequestProject.Section4YThreeEmpty
import RequestProject.Section4AGtTwo

/-!
# Section 4: assembly after `y > 3`

This file connects the fully assembled first-gap geometry and the established inequality `y > 3`
to the paper's next conclusion `a > 2`.  The remaining inputs are isolated as the five cumulative
packing estimates proved in the `a > 2` paragraph of the paper.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- Once the five cumulative packing estimates in the paper's proof of `a > 2` are available,
all geometric hypotheses needed by `a_gt_two` follow from the initial Section 4 setup. -/
lemma section4_assemble_a_gt_two_of_packing_bounds
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    (hsum : 2 * (cum A (x + 1 - a) - cum A a) + cum A (x + 1) - cum A (2 * a)
      ≤ (x + 1 - a) - a)
    (hreflect : cum A x - cum A (x + 1 - a) + cum A a ≤ a - 1)
    (hmass : cum A (2 * a) - cum A a ≤ 1)
    (hprefix : cum A a ≤ (a - 1) / 2)
    (hmono : cum A (x - 1) ≤ cum A (x + 1 - a)) :
    2 < a := by
  have hslt : b - a < 1 :=
    (section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax).2.2.1
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  obtain ⟨_, u, v, huA, hu, hu_max, hvA, hv, hv_min, hgaplen⟩ :=
    section4_assemble_long_gap hIU hsf hmin hx hxright hfail hab hbtop haA hbal hmax
  have hgap : ∀ z ∈ Ioo u v, z ∉ A := by
    intro z hz hzA
    by_cases hzy : z ≤ x + 1 - a - 1
    · linarith [hu_max z hzA hzy]
    · linarith [hv_min z hzA (by linarith)]
  exact a_gt_two haA hbA hab.le rfl hslt.le rfl htpos (by linarith) hgaplen hgap
    hu.le (by linarith) hy3 rfl hsum hreflect hmass hprefix hfail hmono

end ProductFree
