import RequestProject.Section4GapAroundX

/-!
# Section 4: a gap of length one around `x`

This file formalizes the geometric and numerical cores of the next lemma in the paper.
The two intervals are the full translates `u' - [a,b]` and `v' - [a,b]`.  Under the
contrary assumption `v'-u'<1`, their overlap gap has length at most `1-s`, so they cover
at least `u-y+1+s` of `[y-2,u]`.  This contradicts the upper packing estimate obtained
by replacing `A∩[a,b]` with the full maximizing interval.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

/-
The elementary interval geometry in the proof of the gap-around-`x` lemma.
-/
lemma two_difference_intervals_cover_lower
    {a b u u' v' y s : ℝ}
    (hs : s = b - a) (hs1 : s ≤ 1) (hyu : y - 2 ≤ u)
    (hleft : u' - b ≤ y - 2) (hright : u ≤ v' - a)
    (hgap : v' - u' < 1) :
    u - y + 1 + s ≤
      (volume ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩
        Icc (y - 2) u)).toReal := by
  -- The volume of the complement of the union is at most max(v'-u'-s,0).
  have h_complement : (volume (Icc (y - 2) u \ ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩ Icc (y - 2) u))).toReal ≤ max (v' - u' - s) 0 := by
    refine' le_trans ( ENNReal.toReal_mono _ _ ) _;
    exact ENNReal.ofReal ( Max.max ( v' - u' - s ) 0 );
    · norm_num;
    · refine' le_trans ( MeasureTheory.measure_mono _ ) _;
      exact Set.Ioo ( u' - a ) ( v' - b );
      · grind;
      · simp +zetaDelta at *;
        exact ENNReal.ofReal_le_ofReal ( by linarith );
    · rw [ ENNReal.toReal_ofReal ( by positivity ) ];
  rw [ show ( Icc ( y - 2 ) u \ ( ( Icc ( u' - b ) ( u' - a ) ∪ Icc ( v' - b ) ( v' - a ) ) ∩ Icc ( y - 2 ) u ) ) = ( Icc ( y - 2 ) u ) \ ( ( Icc ( u' - b ) ( u' - a ) ∪ Icc ( v' - b ) ( v' - a ) ) ∩ Icc ( y - 2 ) u ) from rfl, MeasureTheory.measure_diff ] at h_complement <;> norm_num at *;
  · rw [ ENNReal.toReal_sub_of_le ] at h_complement;
    · cases h_complement <;> rw [ ENNReal.toReal_ofReal ] at * <;> linarith;
    · exact le_trans ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide );
    · norm_num;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( Icc ( u' - b ) ( u' - a ) ∪ Icc ( v' - b ) ( v' - a ) ) ∩ Icc ( y - 2 ) u ⊆ Icc ( y - 2 ) u from fun x hx => hx.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) )

/-
The paper's mass lower bound turns the translate-packing estimate into the strict
upper bound needed for the geometric contradiction.
-/
lemma second_gap_strict_upper
    {A : Set ℝ} {a b u u' v' y s t : ℝ}
    (hslt : s < 1) (hts : t ≤ s)
    (hlower : 5 / 4 * (1 - t) < cum A y - cum A (y - 2))
    (hpacking :
      (volume ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩
        Icc (y - 2) u)).toReal + (cum A y - cum A (y - 2))
        ≤ u - y + 2 + s - t) :
    (volume ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩
      Icc (y - 2) u)).toReal < u - y + 1 + s := by
  linarith

/-
The paper's lemma `v' ≥ u'+1`, after the preceding packing calculation has
provided the strict upper bound for the same union of two translated intervals.
-/
lemma gap_around_x
    {a b u u' v' y s : ℝ}
    (hs : s = b - a) (hs1 : s ≤ 1) (hyu : y - 2 ≤ u)
    (hleft : u' - b ≤ y - 2) (hright : u ≤ v' - a)
    (hupper : (volume ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩
        Icc (y - 2) u)).toReal < u - y + 1 + s) :
    1 ≤ v' - u' := by
  contrapose! hupper;
  apply_rules [ two_difference_intervals_cover_lower ]

/-
Numerical addition of the three inequalities in the paper's corollary `t > 1/2`.

`hdiff` is the difference-set packing estimate up to `u'-1`; `hright` and `hleft`
are the two maximal-discrepancy estimates on the right and left of the gap.
-/
lemma t_gt_one_half
    {A : Set ℝ} {x u' t : ℝ}
    (hdiff : 2 * cum A x + cum A (u' - 1) ≤ u' - 1 + t)
    (hright : cum A (x + 1) - cum A x ≤ (x - u' + t) / 2)
    (hleft : cum A (x - 1) - cum A (u' - 1) ≤ (x - u' + t) / 2)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    1 / 2 < t := by
  linarith [ show cum A x ≥ 0 by exact ENNReal.toReal_nonneg ]

end ProductFree