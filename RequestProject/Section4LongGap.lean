import RequestProject.Section4Boost

/-!
# Section 4: extremal points around the first gap

This file continues the argument around Lemma `y - 1 gap lem`.  It records the
strict location of the last point `u` before `y-1` and the first point `v` after
`y-1`, and formalizes the measure-zero consequence of the paper's length-one gap
estimate.  The latter feeds directly into Corollary `another boost cor`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The first forced gap places its neighboring extremal points strictly outside it.
-/
lemma first_gap_extrema_strict {y s u v : ℝ}
    (hs1 : s ≤ 1) (hgap : A ∩ Icc (y - 1) (y - s) = ∅)
    (huA : u ∈ A) (hu_le : u ≤ y - 1)
    (hvA : v ∈ A) (hle_v : y - 1 ≤ v) :
    u < y - 1 ∧ y - s < v := by
  constructor <;> contrapose! hgap;
  · exact ⟨ u, huA, by constructor <;> linarith ⟩;
  · exact ⟨ v, hvA, hle_v, hgap ⟩

/-
If consecutive points around a gap are at distance at least one, then every
interval of length at most one starting at the left point has zero `A`-mass.
-/
lemma mass_Icc_eq_zero_of_gap_extrema
    {u v s q : ℝ} (hs1 : s ≤ 1) (huv : 1 ≤ v - u)
    (hu_max : ∀ z ∈ A, z ≤ q → z ≤ u)
    (hv_min : ∀ z ∈ A, q ≤ z → v ≤ z) :
    (volume (A ∩ Icc u (u + s))).toReal = 0 := by
  -- Since $A \cap [u, u + s]$ is a subset of $\{u\}$, its volume is zero.
  have h_subset : A ∩ Icc u (u + s) ⊆ {u} ∪ {v} := by
    grind;
  rw [ MeasureTheory.measure_mono_null h_subset ];
  · norm_num;
  · rw [ MeasureTheory.measure_union_null ] <;> norm_num

/-
Corollary `another boost cor` from the paper, once the length-one gap estimate
`1 ≤ v-u` is available.  The correction term in `another_boost` vanishes because
`A ∩ [u,u+s]` has measure zero.
-/
lemma another_boost_of_long_gap (hA : IsClosed A) (hAcompact : IsCompact A)
    (hAfin : volume A ≠ ⊤) (hmin : IsLeast A 1)
    {a b u v q d s : ℝ} (hab : a < b) (hs : s = b - a)
    (hs1 : s ≤ 1) (hI : IsRightBalanced A a b)
    (huA : u ∈ A) (hu : 1 ≤ u) (hud : u + s ≤ d)
    (huv : 1 ≤ v - u)
    (hu_max : ∀ z ∈ A, z ≤ q → z ≤ u)
    (hv_min : ∀ z ∈ A, q ≤ z → v ≤ z)
    (hmle : mMinus A u ≤ s) (hmd : mMinus A d = 0)
    {ivs₁ ivs₂ : List (ℝ × ℝ)}
    (hB₁ : IsIntervalUnion (A ∩ Icc 1 u) ivs₁)
    (hB₂ : IsIntervalUnion (A ∩ Icc (u + s) d) ivs₂)
    (hdisc₁ : disc (A ∩ Icc 1 u) ≤ discOn A a b)
    (hdisc₂ : disc (A ∩ Icc (u + s) d) ≤ discOn A a b) :
    2 * cum A d + (volume (A ∩ Icc a (b - mMinus A u))).toReal
      ≤ (volume ((A - A) ∩ Icc (b - d) (b - 1))).toReal := by
  convert another_boost hA hAcompact hAfin hmin hab hs hI huA hu hud hmle hmd hB₁ hB₂ hdisc₁ hdisc₂ using 1;
  rw [ show (volume (A ∩ Icc u (u + s))).toReal = 0 from
    mass_Icc_eq_zero_of_gap_extrema hs1 huv hu_max hv_min ]
  ring

end ProductFree