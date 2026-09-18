import RequestProject.Section4Final

/-!
# Section 4: choosing the points adjacent to a cut

This file supplies the compactness bridge needed after the first forced gap.  If a compact
set has points on both sides of a real number `q`, then it has a last point at or before `q`
and a first point at or after `q`.  The conclusion is phrased exactly in the maximality and
minimality form used by the later Section 4 lemmas.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
A compact set with witnesses on both sides of `q` has extremal points adjacent to `q`.
-/
lemma exists_extrema_around_cut
    (hA : IsCompact A) {p q r : ℝ}
    (hpA : p ∈ A) (hrA : r ∈ A) (hpq : p ≤ q) (hqr : q ≤ r) :
    ∃ u v : ℝ,
      u ∈ A ∧ u ≤ q ∧ (∀ z ∈ A, z ≤ q → z ≤ u) ∧
      v ∈ A ∧ q ≤ v ∧ (∀ z ∈ A, q ≤ z → v ≤ z) := by
  -- Let $u$ be the greatest element in $A \cap (-\infty, q]$.
  obtain ⟨u, hu⟩ : ∃ u, u ∈ A ∩ Set.Iic q ∧ ∀ z ∈ A ∩ Set.Iic q, z ≤ u := by
    apply_rules [ IsCompact.exists_isGreatest, hA.inter_right ];
    · exact isClosed_Iic;
    · exact ⟨ p, hpA, hpq ⟩;
  obtain ⟨v, hv⟩ : ∃ v, v ∈ A ∩ Set.Ici q ∧ ∀ z ∈ A ∩ Set.Ici q, v ≤ z := by
    apply_rules [ IsCompact.exists_isLeast, hA ];
    · exact hA.inter_right isClosed_Ici;
    · exact ⟨ r, hrA, hqr ⟩;
  exact ⟨ u, v, hu.1.1, hu.1.2, fun z hz hz' => hu.2 z ⟨ hz, hz' ⟩, hv.1.1, hv.1.2, fun z hz hz' => hv.2 z ⟨ hz, hz' ⟩ ⟩

/-- Specialized form used at the first gap, with the cut at `y-1`. -/
lemma exists_extrema_around_y_sub_one
    (hA : IsCompact A) {p r y : ℝ}
    (hpA : p ∈ A) (hrA : r ∈ A) (hp : p ≤ y - 1) (hr : y - 1 ≤ r) :
    ∃ u v : ℝ,
      u ∈ A ∧ u ≤ y - 1 ∧ (∀ z ∈ A, z ≤ y - 1 → z ≤ u) ∧
      v ∈ A ∧ y - 1 ≤ v ∧ (∀ z ∈ A, y - 1 ≤ z → v ≤ z) := by
  exact exists_extrema_around_cut hA hpA hrA hp hr

end ProductFree