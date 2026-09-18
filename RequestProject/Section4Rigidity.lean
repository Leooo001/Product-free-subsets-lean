import RequestProject.Section4Prep

/-!
# Section 4: first rigidity consequences

This file continues the formalization of the rigidity argument proving the key lemma.  The first
result is Lemma `s<1` from the paper: a positive-length balanced interval in a compact set that is
disjoint from its unit translate has length strictly less than one.  In the eventual application
the compact set is sum-free and contains `1`, so unit-translate disjointness follows immediately.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
Strict unit-translate packing for two nonempty pieces of a compact unit-separated set.  After
translating the second piece left by one, the two pieces are disjoint closed subsets of the same
interval; connectedness forces a genuine gap between them.
-/
lemma strict_unit_translate_packing
    (hA : IsCompact A)
    (hsep : ∀ ⦃u : ℝ⦄, u ∈ A → u + 1 ∉ A)
    {r s : ℝ} (hrs : r < s)
    (hne₁ : (A ∩ Icc r s).Nonempty)
    (hne₂ : (A ∩ Icc (r + 1) (s + 1)).Nonempty) :
    (volume (A ∩ Icc r s)).toReal +
        (volume (A ∩ Icc (r + 1) (s + 1))).toReal < s - r := by
  let B := (fun x => x + 1) ⁻¹' A
  have h_discriminant : ¬(0 ≤ discOn A r s + discOn B r s) := by
    intro h_nonneg
    have hinter := inter_nonempty_of_discOn hA.isClosed
      (hA.isClosed.preimage (continuous_add_right 1)) hrs hne₁ (B := B) ?_ h_nonneg
    · exact hinter.ne_empty (by aesop)
    · obtain ⟨x, hxA, hxI⟩ := hne₂
      exact ⟨x - 1, by aesop, by constructor <;> linarith [hxI.1, hxI.2]⟩
  have h_translation : discOn B r s = discOn A (r + 1) (s + 1) := by
    unfold discOn
    rw [show B ∩ Icc r s = (fun x => x + 1) ⁻¹' (A ∩ Icc (r + 1) (s + 1)) by
      ext
      aesop]
    erw [MeasureTheory.measure_preimage_add_right]
    ring
  unfold discOn at *
  linarith

/-
**Lemma `s<1` (unit-separated balanced intervals).**

If a compact set contains no pair of points at distance one, every positive-length interval that
is balanced for that set has length strictly less than one.  A discrepancy-maximizing interval is
balanced, so this is the form needed in the Section 4 rigidity setup.
-/
theorem balanced_length_lt_one_of_unit_separated
    (hA : IsCompact A)
    (hsep : ∀ ⦃u : ℝ⦄, u ∈ A → u + 1 ∉ A)
    {a b : ℝ} (hab : a < b) (hbal : IsBalanced A a b) :
    b - a < 1 := by
  by_cases hcase : b - a ≤ 1
  · by_contra hnot
    have ha : a ∈ A := left_balanced_left_mem hA.isClosed hbal.1 hab
    have hb : b ∈ A := right_balanced_right_mem hA.isClosed hbal.2 hab
    exact hsep ha (by convert hb using 1; linarith)
  · have ha : a ∈ A := left_balanced_left_mem hA.isClosed hbal.1 hab
    have hb : b ∈ A := right_balanced_right_mem hA.isClosed hbal.2 hab
    have hpack :
        (volume (A ∩ Icc a (b - 1))).toReal +
          (volume (A ∩ Icc (a + 1) b)).toReal < b - a - 1 := by
      convert strict_unit_translate_packing hA hsep (by linarith : a < b - 1)
        ⟨a, ha, by constructor <;> linarith⟩
        ⟨b, hb, by constructor <;> linarith⟩ using 1 <;> ring
    have hdisc : discOn A a (b - 1) + discOn A (a + 1) b < 0 := by
      unfold discOn
      linarith
    have hleft : 0 ≤ discOn A a (b - 1) := hbal.1.2 _ (by linarith) (by linarith)
    have hright : 0 ≤ discOn A (a + 1) b := hbal.2.2 _ (by linarith) (by linarith)
    linarith

/-- Sum-free specialization of `balanced_length_lt_one_of_unit_separated`: if `1 ∈ A`, every
positive-length balanced interval has length less than one. -/
theorem IsSumFree.balanced_length_lt_one
    (hA : IsCompact A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    {a b : ℝ} (hab : a < b) (hbal : IsBalanced A a b) :
    b - a < 1 := by
  exact balanced_length_lt_one_of_unit_separated hA
    (fun {_} hu => hsf hu hone) hab hbal

end ProductFree