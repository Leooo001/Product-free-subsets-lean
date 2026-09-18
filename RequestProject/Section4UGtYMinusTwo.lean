import RequestProject.Section4AGtTwo

/-!
# Section 4: estimates after `a > 2` and the location of `u`

This file formalizes the argument from the paper immediately following the proof that
`a > 2`, through the conclusion `u > y - 2`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The two applications of the difference-set estimate, written in cumulative form.
-/
lemma post_a_gt_two_difference_bounds
    {a x y t : ℝ}
    (hshort : 2 * (cum A (x - 1) - cum A y) + cum A (a - 2) ≤ a - 2 + t)
    (hlong : 2 * (cum A (x + 1) - cum A y) + cum A a ≤ a + t) :
    (2 * (cum A (x - 1) - cum A y) + cum A (a - 2) ≤ a - 2 + t) ∧
    (2 * (cum A (x + 1) - cum A y) + cum A a ≤ a + t) := by
  exact ⟨ hshort, hlong ⟩

/-
Introduce the nonnegative deficit `g` in the direct sumset packing estimate.
-/
lemma exists_direct_packing_deficit
    {a x y : ℝ}
    (hpack : 2 * cum A (y - 2) + (cum A (x - 1) - cum A (a + 1)) ≤ y - 3) :
    ∃ g : ℝ, 0 ≤ g ∧
      2 * cum A (y - 2) + (cum A (x - 1) - cum A (a + 1)) = y - 3 - g := by
  exact ⟨ y - 3 - ( 2 * cum A ( y - 2 ) + ( cum A ( x - 1 ) - cum A ( a + 1 ) ) ), by linarith, by ring ⟩

/-
The numerical combination in the paper giving a large amount of mass in `[y-2,y]`.
-/
lemma mass_near_y_gt_five_quarters
    {a x y t g : ℝ}
    (hy : a + y = x + 1)
    (hg : 2 * cum A (y - 2) + (cum A (x - 1) - cum A (a + 1)) = y - 3 - g)
    (halt : 2 * (cum A (x + 1) - cum A y) + cum A a ≤ a + t)
    (hunit : cum A (a + 1) - cum A a ≤ (1 + t) / 2)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hsurplus : 1 - t < cum A (x + 1) - cum A x) :
    5 / 4 * (1 - t) + g / 2 < cum A y - cum A (y - 2) := by
  grind

/-- Dropping the nonnegative deficit gives the simpler strict estimate used to locate `u`. -/
lemma mass_near_y_gt_five_quarters_base {y t g : ℝ}
    (hg : 0 ≤ g)
    (hstrong : 5 / 4 * (1 - t) + g / 2 < cum A y - cum A (y - 2)) :
    5 / 4 * (1 - t) < cum A y - cum A (y - 2) := by
  linarith

/-
Reflection through a point of a sum-free set bounds the mass in a reflected interval
by the complement of `A` in the target interval.
-/
lemma reflection_mass_le_interval_complement
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b p q c : ℝ} (hc : c ∈ A) (hpq : p ≤ q)
    (ha : a = c - q) (hb : b = c - p) :
    (volume (A ∩ Icc p q)).toReal ≤
      (b - a) - (volume (A ∩ Icc a b)).toReal := by
  -- Show that the image of A ∩ [p, q] under z ↦ c - z is disjoint from A.
  have h_disjoint : Disjoint ((fun z => c - z) '' (A ∩ Icc p q)) A := by
    simp_all +decide [ IsSumFree, Set.disjoint_left ];
    grind;
  -- Show that the image of A ∩ [p, q] under z ↦ c - z is contained in [a, b].
  have h_subset : (fun z => c - z) '' (A ∩ Icc p q) ⊆ Icc a b \ (A ∩ Icc a b) := by
    simp_all +decide [ Set.subset_def, Set.disjoint_left ];
    exact fun x y hy hy' hy'' hx => ⟨ ⟨ by linarith, by linarith ⟩, h_disjoint y hy hy' hy'' hx ⟩;
  -- Use the fact that the image of A ∩ [p, q] under z ↦ c - z has the same volume as A ∩ [p, q].
  have h_volume_eq : (volume ((fun z => c - z) '' (A ∩ Icc p q))).toReal = (volume (A ∩ Icc p q)).toReal := by
    have h_volume_eq : ∀ (S : Set ℝ), MeasurableSet S → (volume ((fun z => c - z) '' S)).toReal = (volume S).toReal := by
      intro S hS; rw [ show ( fun z => c - z ) '' S = ( fun z => -z ) '' S + { c } by ext; simp +decide [ sub_eq_add_neg, add_comm ] ; aesop ] ;
      simp +decide [Set.add_singleton];
    exact h_volume_eq _ ( hA.inter measurableSet_Icc );
  refine' h_volume_eq ▸ le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_subset ) _;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show Icc a b \ ( A ∩ Icc a b ) ⊆ Icc a b from fun x hx => hx.1 ) ) ( by simp +decide [ ha, hb ] ) );
  · rw [ MeasureTheory.measure_diff ] <;> norm_num [ hA, ha, hb ];
    · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ hpq ];
      exact le_trans ( MeasureTheory.measure_mono ( show A ∩ Icc ( c - q ) ( c - p ) ⊆ Icc ( c - q ) ( c - p ) from fun x hx => hx.2 ) ) (by simp +decide);
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc ( c - q ) ( c - p ) ⊆ Icc ( c - q ) ( c - p ) from fun x hx => hx.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) )

/-
If `u` is the last point of `A` at or before `y-1`, and the first forced gap is
empty, then the mass in `[y-2,y]` is bounded by the complement of the maximizing
interval under reflection through `x+1`.
-/
lemma mass_near_y_le_half_gap
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u x y s t : ℝ}
    (hxy : x + 1 ∈ A) (hy : y = x + 1 - a) (hs : s = b - a)
    (ht : t = discOn A a b) (hab : a ≤ b)
    (hy2 : 2 ≤ y) (hsy : s ≤ y)
    (hu : u ≤ y - 2)
    (hu_last : ∀ z ∈ A, z ≤ y - 1 → z ≤ u)
    (hgap : A ∩ Icc (y - 1) (y - s) = ∅) :
    cum A y - cum A (y - 2) ≤ (s - t) / 2 := by
  rw [ cum_sub_cum_eq_mass_Icc ];
  · have h_volume : (volume (A ∩ Icc (y - 2) y)).toReal ≤ (volume (A ∩ Icc (y - s) y)).toReal := by
      have h_mass : A ∩ Icc (y - 2) y ⊆ A ∩ Icc (y - s) y ∪ A ∩ Icc (y - 2) (y - 1) := by
        intro z hz;
        by_cases hz_case : z ≤ y - 1;
        · exact Or.inr ⟨ hz.1, ⟨ by linarith [ hz.2.1 ], hz_case ⟩ ⟩;
        · exact Or.inl ⟨ hz.1, ⟨ le_of_not_gt fun h => hgap.subset ⟨ hz.1, ⟨ by linarith [ hz.2.1 ], by linarith [ hz.2.2 ] ⟩ ⟩, by linarith [ hz.2.2 ] ⟩ ⟩;
      have h_mass : volume (A ∩ Icc (y - 2) (y - 1)) = 0 := by
        have h_mass : A ∩ Icc (y - 2) (y - 1) ⊆ {u} := by
          grind;
        exact MeasureTheory.measure_mono_null h_mass ( by norm_num );
      have h_mass : volume (A ∩ Icc (y - 2) y) ≤ volume (A ∩ Icc (y - s) y) := by
        exact le_trans ( MeasureTheory.measure_mono ‹_› ) ( MeasureTheory.measure_union_le _ _ ) |> le_trans <| by aesop;
      gcongr;
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
    have h_reflect : (volume (A ∩ Icc (y - s) y)).toReal ≤ (s) - (volume (A ∩ Icc a b)).toReal := by
      convert reflection_mass_le_interval_complement hA hsf ( hxy ) ( by linarith : y - s ≤ y ) ( by linarith : a = x + 1 - y ) ( by linarith : b = x + 1 - ( y - s ) ) using 1 ; ring;
      linarith;
    unfold discOn at *;
    linarith;
  · linarith;
  · linarith

/-
Paper's conclusion `u > y - 2`.  The strict lower mass estimate comes from the
preceding difference/sumset estimates; the upper estimate under `u ≤ y-2` comes from the
first gap and reflection through `x+1`.
-/
lemma u_gt_y_sub_two
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u x y s t : ℝ}
    (hxy : x + 1 ∈ A) (hy : y = x + 1 - a) (hs : s = b - a)
    (ht : t = discOn A a b) (hab : a ≤ b)
    (hy2 : 2 ≤ y) (hsy : s ≤ y) (hs1 : s ≤ 1)
    (hu_last : ∀ z ∈ A, z ≤ y - 1 → z ≤ u)
    (hgap : A ∩ Icc (y - 1) (y - s) = ∅)
    (hlower : 5 / 4 * (1 - t) < cum A y - cum A (y - 2)) :
    y - 2 < u := by
  by_contra! h_contra;
  -- From mass_near_y_le_half_gap and h_contra, we have cum A y - cum A (y - 2) ≤ (s - t) / 2.
  have h_upper : cum A y - cum A (y - 2) ≤ (s - t) / 2 := by
    apply mass_near_y_le_half_gap hA hsf hxy hy hs ht hab hy2 hsy h_contra hu_last hgap;
  unfold discOn at *;
  linarith [ show ( volume ( A ∩ Icc a b ) |> ENNReal.toReal ) ≤ b - a by exact le_trans ( ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ) ( by simp +decide [ hab ] ) ]

end ProductFree