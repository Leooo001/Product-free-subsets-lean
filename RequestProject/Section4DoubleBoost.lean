import RequestProject.Section4GapAroundTwo

/-!
# Section 4: the double boost and forcing `u < 2`

This file formalizes the algebraic assembly of the paper's five-piece
`double boost` estimate and the contradiction which forces the point `u` to
lie below `2`.  The geometric five-piece packing and the later
Brunn--Minkowski packing are exposed as hypotheses, so the conclusions can be
reused independently of a particular finite-interval representation.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The two truncated copies of the maximizing interval turn the first
five-piece packing estimate into the second line of `double boost`.
-/
lemma double_boost_truncation
    {b u u₂ s t : ℝ}
    (hfirst : 2 * cum A (b - 1) +
        (volume (A ∩ Icc (b - s) (b - mMinus A u))).toReal +
        (volume (A ∩ Icc (b - s) (b - mMinus A u₂))).toReal ≤
        (volume ((A - A) ∩ Icc 1 (b - 1))).toReal)
    (hu : (s + t) / 2 - mMinus A u ≤
        (volume (A ∩ Icc (b - s) (b - mMinus A u))).toReal)
    (hu₂ : (s + t) / 2 - mMinus A u₂ ≤
        (volume (A ∩ Icc (b - s) (b - mMinus A u₂))).toReal) :
    2 * cum A (b - 1) + s + t - mMinus A u - mMinus A u₂ ≤
      (volume ((A - A) ∩ Icc 1 (b - 1))).toReal := by
  linarith

/-
Final line of the paper's `double boost` lemma.
-/
lemma double_boost_finish
    {b u u₂ s t : ℝ}
    (hboost : 2 * cum A (b - 1) + s + t - mMinus A u - mMinus A u₂ ≤
      (volume ((A - A) ∩ Icc 1 (b - 1))).toReal)
    (hm : mMinus A u + mMinus A u₂ ≤ cum A u) :
    2 * cum A (b - 1) + s + t - cum A u ≤
      (volume ((A - A) ∩ Icc 1 (b - 1))).toReal := by
  linarith

/-
Complete algebraic assembly of all three displayed lines of the paper's
`double boost` estimate.
-/
theorem double_boost
    {b u u₂ s t : ℝ}
    (hfirst : 2 * cum A (b - 1) +
        (volume (A ∩ Icc (b - s) (b - mMinus A u))).toReal +
        (volume (A ∩ Icc (b - s) (b - mMinus A u₂))).toReal ≤
        (volume ((A - A) ∩ Icc 1 (b - 1))).toReal)
    (hu : (s + t) / 2 - mMinus A u ≤
        (volume (A ∩ Icc (b - s) (b - mMinus A u))).toReal)
    (hu₂ : (s + t) / 2 - mMinus A u₂ ≤
        (volume (A ∩ Icc (b - s) (b - mMinus A u₂))).toReal)
    (hm : mMinus A u + mMinus A u₂ ≤ cum A u) :
    2 * cum A (b - 1) + s + t - cum A u ≤
      (volume ((A - A) ∩ Icc 1 (b - 1))).toReal := by
  linarith [ double_boost_truncation hfirst hu hu₂, double_boost_finish ( double_boost_truncation hfirst hu hu₂ ) hm ]

/-
Numerical contradiction at the end of the proof that `u<2`.

The hypotheses `hdifferencePacking` and `hBM` are respectively the disjoint
packing of `A-A` with `A`, and the Brunn--Minkowski packing of
`(A∩[b+1,x])-(A∩[a,b])` with `A∩[1,y-1]`.
-/
lemma not_two_lt_u_of_double_boost
    {a b x y u s t : ℝ}
    (hs : s = b - a) (hy : y = x + 1 - a)
    (hsge : t ≤ s) (ht : 1 / 2 < t)
    (hmono : cum A u ≤ cum A (y - 1))
    (hdouble : 2 * cum A (b - 1) + s + t - cum A u ≤
      (volume ((A - A) ∩ Icc 1 (b - 1))).toReal)
    (hdifferencePacking :
      (volume ((A - A) ∩ Icc 1 (b - 1))).toReal + cum A (b - 1) ≤ b - 2)
    (hunit : cum A (b + 1) - cum A (b - 1) ≤ 1)
    (hBM : cum A (y - 1) + (cum A x - cum A (b + 1)) +
      (s + t) / 2 ≤ y - 2)
    (hleft : cum A (x - 1) ≤ cum A (b + 1))
    (hright : cum A (x + 1) ≤ cum A (b + 1) + 1)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    ¬ 2 < u := by
  grind +splitImp

/-
Since `1∈A`, sum-freeness rules out `u=2`; the preceding contradiction
therefore yields the strict inequality in the paper.
-/
theorem u_lt_two
    (hsf : IsSumFree A) (hOne : 1 ∈ A) {u : ℝ} (huA : u ∈ A)
    (hnot : ¬ 2 < u) : u < 2 := by
  cases lt_or_eq_of_le ( le_of_not_gt hnot ) <;> simp_all +decide [ IsSumFree ];
  exact hsf hOne hOne ( by convert huA using 1; ring )

/-
Once `y>3` and `u<2`, the extrema around `y-1` and around `2` coincide.
This is the final sentence requested in the paper.
-/
theorem extrema_around_two_eq
    {u v u₂ v₂ y : ℝ}
    (hy : 3 < y) (huA : u ∈ A) (hu2 : u < 2) (hvA : v ∈ A)
    (huMax : ∀ z ∈ A, z ≤ y - 1 → z ≤ u)
    (hvMin : ∀ z ∈ A, y - 1 ≤ z → v ≤ z)
    (hu₂A : u₂ ∈ A) (hu₂le : u₂ ≤ 2)
    (hu₂Max : ∀ z ∈ A, z ≤ 2 → z ≤ u₂)
    (hv₂A : v₂ ∈ A) (hv₂ge : 2 ≤ v₂)
    (hv₂Min : ∀ z ∈ A, 2 ≤ z → v₂ ≤ z)
    (hq_le_v : y - 1 ≤ v) :
    u = u₂ ∧ v = v₂ := by
  grind

end ProductFree