import RequestProject.Section4UGtYMinusTwo

/-!
# Section 4: the forced empty interval immediately to the left of `x`

This file continues the paper after `u > y - 2`.  It separates the local packing
argument (available for every hypothetical point of `A ∩ [u+b-1,x]`) from the short
numerical contradiction with the previously established lower bound for the mass near `y`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The local translate-packing estimate used for a hypothetical point near `x`.

The translated copy `z-(A∩[a,b])` is disjoint from `A` by sum-freeness.  The endpoint
assumptions are exactly the two inequalities in the paper showing that this copy and
`A∩[y-2,u]` fit together inside an interval of length one.
-/
lemma local_difference_translate_packing
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u y s t z : ℝ}
    (hs : s = b - a) (hs1 : s ≤ 1)
    (ht : t = discOn A a b) (hzA : z ∈ A)
    (hy2 : 2 ≤ y) (hyu : y - 2 ≤ u) (huy : u ≤ y - 1)
    (hzleft : u - 1 ≤ z - b) (hzright : z - a ≤ y - 1) :
    cum A u - cum A (y - 2) ≤ 1 - (s + t) / 2 := by
  -- By definition of $P$ and $Q$, we know that $P$ and $Q$ are disjoint measurable sets.
  have hPQ_disjoint : Disjoint ((fun r => z - r) '' (A ∩ Icc a b)) (A ∩ Icc (y - 2) u) := by
    rw [ Set.disjoint_left ];
    contrapose! hsf;
    unfold IsSumFree; aesop;
  -- By definition of $P$ and $Q$, we know that $P \cup Q$ is a subset of an interval of length 1.
  have hPQ_subset : (fun r => z - r) '' (A ∩ Icc a b) ∪ (A ∩ Icc (y - 2) u) ⊆ Icc (min (z - b) (y - 2)) (min (z - b) (y - 2) + 1) := by
    grind;
  have hPQ_measure : (volume ((fun r => z - r) '' (A ∩ Icc a b))).toReal + (volume (A ∩ Icc (y - 2) u)).toReal ≤ 1 := by
    rw [ ← ENNReal.toReal_add ];
    · rw [ ← MeasureTheory.measure_union hPQ_disjoint ];
      · exact le_trans ( ENNReal.toReal_mono ( by norm_num ) ( MeasureTheory.measure_mono hPQ_subset ) ) ( by norm_num );
      · exact hA.inter measurableSet_Icc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( fun r => z - r ) '' ( A ∩ Icc a b ) ⊆ Set.Icc ( z - b ) ( z - a ) from Set.image_subset_iff.mpr fun x hx => by constructor <;> linarith [ hx.2.1, hx.2.2 ] ) ) ( by simp +decide [ Real.volume_Icc ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc ( y - 2 ) u ⊆ Icc ( y - 2 ) u from fun x hx => hx.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) );
  have hP_measure : (volume ((fun r => z - r) '' (A ∩ Icc a b))).toReal = (volume (A ∩ Icc a b)).toReal := by
    have hP_measure : ∀ (S : Set ℝ), MeasurableSet S → (volume ((fun r => z - r) '' S)).toReal = (volume S).toReal := by
      intros S hS; exact (by
      rw [ show ( fun r => z - r ) '' S = ( fun r => -r ) '' S + { z } by ext; simp +decide [ sub_eq_add_neg, add_comm ] ; aesop ] ; simp +decide [ *, MeasureTheory.measure_preimage_add_right ] ;);
    exact hP_measure _ ( hA.inter measurableSet_Icc );
  rw [ cum_sub_cum_eq_mass_Icc ];
  · unfold discOn at *;
    linarith;
  · linarith;
  · linarith

/-
The numerical core of the lemma producing the gap immediately to the left of `x`.

For a hypothetical `z ∈ A ∩ [u+b-1,x]`, the first bound is obtained by packing
`z-(A∩[a,b])` together with `A∩[y-2,u]` in an interval of length one.  The second
is the reflection-through-`x+1` estimate, and the equality records that `u` is the
last point of `A` before `y-1`.
-/
lemma no_point_near_x_of_packing
    {u y s t : ℝ}
    (hs1 : s ≤ 1) (hts : t ≤ s)
    (hlower : 5 / 4 * (1 - t) < cum A y - cum A (y - 2))
    (hlocal : cum A u - cum A (y - 2) ≤ 1 - (s + t) / 2)
    (hreflect : cum A y - cum A (y - 1) ≤ (s - t) / 2)
    (hlast : cum A (y - 1) = cum A u) :
    False := by
  linarith

/-
Paper's lemma that `A` is disjoint from `[u+b-1,x]`.

The geometric part of the proof supplies `hlocal` for each hypothetical point in
that interval.  This formulation makes the exact interface explicit and lets the
same packing construction be reused independently of the chosen finite-interval
representation of `A`.
-/
lemma gap_immediately_left_of_x
    {b u x y s t : ℝ}
    (hs1 : s ≤ 1) (hts : t ≤ s)
    (hlower : 5 / 4 * (1 - t) < cum A y - cum A (y - 2))
    (hreflect : cum A y - cum A (y - 1) ≤ (s - t) / 2)
    (hlast : cum A (y - 1) = cum A u)
    (hpointPacking : ∀ z ∈ A ∩ Icc (u + b - 1) x,
      cum A u - cum A (y - 2) ≤ 1 - (s + t) / 2) :
    A ∩ Icc (u + b - 1) x = ∅ := by
  grind

/-
Full paper-form version of the gap lemma, deriving the pointwise packing bound from
sum-freeness and the endpoint relations.
-/
lemma gap_immediately_left_of_x_full
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u x y s t : ℝ}
    (hs : s = b - a) (hs1 : s ≤ 1) (hts : t ≤ s)
    (ht : t = discOn A a b) (hy2 : 2 ≤ y) (hyu : y - 2 ≤ u)
    (huy : u ≤ y - 1) (hxa : x - a = y - 1)
    (hlower : 5 / 4 * (1 - t) < cum A y - cum A (y - 2))
    (hreflect : cum A y - cum A (y - 1) ≤ (s - t) / 2)
    (hlast : cum A (y - 1) = cum A u) :
    A ∩ Icc (u + b - 1) x = ∅ := by
  apply Set.eq_empty_of_forall_notMem;
  intro z hz;
  have hpointPacking : cum A u - cum A (y - 2) ≤ 1 - (s + t) / 2 := by
    apply local_difference_translate_packing hA hsf hs hs1 ht hz.left hy2 hyu huy (by linarith [hz.right.left]) (by linarith [hz.right.right]);
  linarith

/-
The interval forced empty by `gap_immediately_left_of_x` contains the shorter
interval `[x+s-1,x]`, as stated in the paper.
-/
lemma short_interval_near_x_subset
    {b u x y s : ℝ} (hu : u ≤ y - 1) (hrel : y + b = x + 1 + s) :
    Icc (x + s - 1) x ⊆ Icc (u + b - 1) x := by
  exact Set.Icc_subset_Icc ( by linarith ) le_rfl

end ProductFree