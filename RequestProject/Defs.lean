import Mathlib

/-!
# Product-free and sum-free sets: basic definitions

This development formalizes results from the paper on product-free subsets of `(0,1)`.

The headline result (`ProductFree.main1`) states that an open product-free subset of the
open interval `(0,1)` has Lebesgue measure less than `1/3`.

The main tool is `ProductFree.key_lemma`: if `A` is a sum-free set with least element `1`,
then for every `x`, `F(x-1) + F(x) + F(x+1) ≤ x`, where `F(x) = |A ∩ [0,x]|`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

/-- A set of reals is *sum-free* if there are no `x, y ∈ A` with `x + y ∈ A`. -/
def IsSumFree (A : Set ℝ) : Prop := ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x + y ∉ A

/-- A set of reals is *product-free* if there are no `x, y ∈ E` with `x * y ∈ E`. -/
def IsProductFree (E : Set ℝ) : Prop := ∀ ⦃x⦄, x ∈ E → ∀ ⦃y⦄, y ∈ E → x * y ∉ E

/-- The cumulative measure function `F(x) = |A ∩ [0,x]|`, as a real number. -/
def cum (A : Set ℝ) (x : ℝ) : ℝ := (volume (A ∩ Icc (0:ℝ) x)).toReal

/-- The *positive interval discrepancy* of a set `A`:
`d(A) = sup_I (2|A ∩ I| - |I|)`, the supremum taken over all closed intervals `I = [a,b]`
with `a ≤ b`. -/
def disc (A : Set ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a b : ℝ, a ≤ b ∧ r = 2 * (volume (A ∩ Icc a b)).toReal - (b - a)}

/-- `d_A(I) = 2|A ∩ I| - |I|` for the interval `I = [a,b]`. -/
def discOn (A : Set ℝ) (a b : ℝ) : ℝ := 2 * (volume (A ∩ Icc a b)).toReal - (b - a)

end ProductFree
