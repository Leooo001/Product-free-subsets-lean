import RequestProject.Section4YThree

/-!
# Section 4: the left endpoint satisfies `a > 2`

The first lemma isolates the order argument involving the gap `(u,v)`.  The second is the
final cumulative-mass contradiction.  Together they give the paper's next lemma after
`y > 3`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
If a positive-discrepancy interval of length at most one has both endpoints in `A`, it
cannot cross a gap of length at least one.
-/
lemma maximizing_interval_lies_left_of_gap
    {a b u v y s t : ℝ}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≤ b) (hs : s = b - a) (hs1 : s ≤ 1)
    (ht : t = discOn A a b) (ht0 : 0 < t)
    (huv : u < v) (hgaplen : 1 ≤ v - u)
    (hugap : ∀ z ∈ Ioo u v, z ∉ A)
    (hu : u ≤ y - 1) (hv : y - 1 ≤ v)
    (ha2 : a ≤ 2) (hy3 : 3 < y) :
    b ≤ u := by
  simp_all +decide [ discOn ];
  -- By contradiction, assume $b > u$.
  by_contra h_contra
  have hbv : v ≤ b := by
    grind
  have hab_eq : a = u ∧ b = v ∧ b - a = 1 := by
    grind +qlia
  have hA_inter_Icc_zero : (volume (A ∩ Icc a b)).toReal = 0 := by
    have hA_inter_Icc_zero : A ∩ Icc a b ⊆ {a, b} := by
      grind;
    exact MeasureTheory.measure_mono_null hA_inter_Icc_zero ( by exact MeasureTheory.measure_union_null ( MeasureTheory.measure_singleton a ) ( MeasureTheory.measure_singleton b ) ) |> fun h => h.symm ▸ by norm_num;
  linarith [hA_inter_Icc_zero]

/-- The final numerical part of the proof of `a > 2`.

`hsum` is the sumset-packing estimate supplied by `mzero` and `minterv`; `hreflect` is the
reflection-through-`x+1` packing estimate.  The remaining two estimates follow respectively
from the unit translate by `1` and maximality of `[a,b]` against `[1,b]`.
-/
lemma a_gt_two_of_cumulative_bounds
    {a x y : ℝ}
    (hy : y = x + 1 - a)
    (hsum : 2 * (cum A y - cum A a) + cum A (x + 1) - cum A (2 * a) ≤ y - a)
    (hreflect : cum A x - cum A y + cum A a ≤ a - 1)
    (hmass : cum A (2 * a) - cum A a ≤ 1)
    (hprefix : cum A a ≤ (a - 1) / 2)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hmono : cum A (x - 1) ≤ cum A y) :
    2 < a := by
  by_contra ha2
  linarith

/-- Paper's lemma `a > 2`, after the gap-location argument and the two sum-free packing
estimates have been established.  The explicit gap data are retained because they are also
used in the subsequent construction of the gap around `x`. -/
lemma a_gt_two
    {a b u v x y s t : ℝ}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≤ b) (hs : s = b - a) (hs1 : s ≤ 1)
    (ht : t = discOn A a b) (ht0 : 0 < t)
    (huv : u < v) (hgaplen : 1 ≤ v - u)
    (hugap : ∀ z ∈ Ioo u v, z ∉ A)
    (hu : u ≤ y - 1) (hv : y - 1 ≤ v)
    (hy3 : 3 < y)
    (hy : y = x + 1 - a)
    (hsum : 2 * (cum A y - cum A a) + cum A (x + 1) - cum A (2 * a) ≤ y - a)
    (hreflect : cum A x - cum A y + cum A a ≤ a - 1)
    (hmass : cum A (2 * a) - cum A a ≤ 1)
    (hprefix : cum A a ≤ (a - 1) / 2)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hmono : cum A (x - 1) ≤ cum A y) :
    2 < a := by
  by_contra ha2
  have hb_u := maximizing_interval_lies_left_of_gap haA hbA hab hs hs1 ht ht0 huv
    hgaplen hugap hu hv (le_of_not_gt ha2) hy3
  exact ha2 (a_gt_two_of_cumulative_bounds hy hsum hreflect hmass hprefix hfail hmono)

end ProductFree