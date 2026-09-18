import RequestProject.Section4YLessThanThreePlusS

/-!
# Section 4: the gap around `2`

This file formalizes the next subsection of the paper.  It first extracts the
mass surplus on `[a-2,b-2]`, then uses translations by the nearest points of
`A` on either side of `2` to bound those points and the intervening gap.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
The numerical subtraction which produces the mass surplus immediately
before the points `u''` and `v''` are introduced.
-/
lemma mass_b_sub_two_gt
    {a b s t g : ℝ}
    (hboost : 1 - t + g + (s - t) / 2 < cum A a - cum A (a - 2))
    (hupper : cum A a - cum A (b - 2) ≤ 1 - s + (s - t) / 2) :
    s - t + g < cum A (b - 2) - cum A (a - 2) := by
  linarith

/-
Translating a piece of a sum-free set by one of its points puts it in the
complement of the set.  This is the measure form used for the endpoint bounds
around `2`.
-/
lemma translated_source_complement_bound
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b p l r : ℝ} (hp : p ∈ A) (hlr : l ≤ r)
    (hcontain : (fun z : ℝ => z - p) '' (A ∩ Icc a b) ⊆ Icc l r) :
    (volume (A ∩ Icc l r)).toReal ≤
      (r - l) - (volume (A ∩ Icc a b)).toReal := by
  have h_disjoint : Disjoint (Set.image (fun z => z - p) (A ∩ Set.Icc a b)) (A ∩ Set.Icc l r) := by
    rw [ Set.disjoint_left ];
    simp_all +decide [ IsSumFree ];
    grind
  have h_contained : Set.image (fun z => z - p) (A ∩ Set.Icc a b) ⊆ Set.Icc l r \ (A ∩ Set.Icc l r) := by
    exact fun x hx => ⟨ hcontain hx, fun hx' => h_disjoint.le_bot ⟨ hx, hx' ⟩ ⟩;
  have h_contained : (volume (Set.image (fun z => z - p) (A ∩ Set.Icc a b))).toReal ≤ (volume (Set.Icc l r \ (A ∩ Set.Icc l r))).toReal := by
    apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show Icc l r \ ( A ∩ Icc l r ) ⊆ Icc l r from fun x hx => hx.1 ) ) ( by simp +decide ) );
  convert sub_le_sub_left h_contained ( r - l ) using 1;
  · rw [ MeasureTheory.measure_diff ] <;> norm_num [ hA, hlr ];
    · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ hlr ];
      exact le_trans ( MeasureTheory.measure_mono ( show A ∩ Icc l r ⊆ Icc l r from fun x hx => hx.2 ) ) ( by simp +decide );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc l r ⊆ Icc l r from fun x hx => hx.2 ) ) ( by simp +decide ) );
  · rw [ volume_image_sub_const ]

/-
The reverse translation estimate: mass in a translated copy of `[a,b]`
is at most the complement of `A` inside `[a,b]`.
-/
lemma translated_target_complement_bound
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b p : ℝ} (hp : p ∈ A) (hab : a ≤ b) :
    (volume (A ∩ Icc (a - p) (b - p))).toReal ≤
      (b - a) - (volume (A ∩ Icc a b)).toReal := by
  refine' le_tsub_of_add_le_right _;
  grind +suggestions

/-
Two intervals of equal length, translated to opposite sides of `2`, cover
`[a-2,b-2]` apart from at most their intervening gap.
-/
lemma two_translates_cover_up_to_gap
    {a b u v g : ℝ} (hu : u ≤ 2) (hv : 2 ≤ v)
    (hg : 0 ≤ g) (hgap : v - u - (b - a) ≤ g) :
    (volume (A ∩ Icc (a - 2) (b - 2))).toReal ≤ g +
      (volume (A ∩ Icc (a - u) (b - u))).toReal +
      (volume (A ∩ Icc (a - v) (b - v))).toReal := by
  by_cases h_case : b - v ≤ a - u;
  · have h_cover : A ∩ Icc (a - 2) (b - 2) ⊆ (A ∩ Icc (a - v) (b - v)) ∪ (A ∩ Icc (a - u) (b - u)) ∪ (A ∩ Icc (b - v) (a - u)) := by
      grind;
    refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_cover ) _;
    · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_union_le _ _ ) _ );
      refine' lt_of_le_of_lt ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ) _;
      refine' lt_of_le_of_lt ( add_le_add_three ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ) _ ; norm_num;
    · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_union_le _ _ ) _;
      · refine' ne_of_lt ( lt_of_le_of_lt ( add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ) _ );
        refine' lt_of_le_of_lt ( add_le_add_three ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ) _ ; norm_num;
      · refine' le_trans ( ENNReal.toReal_mono _ <| add_le_add ( MeasureTheory.measure_union_le _ _ ) le_rfl ) _;
        · refine' ne_of_lt ( lt_of_le_of_lt ( add_le_add_three ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ) _ ) ; norm_num;
        · rw [ ENNReal.toReal_add, ENNReal.toReal_add ] <;> norm_num;
          · linarith [ show ( volume ( A ∩ Icc ( b - v ) ( a - u ) ) |> ENNReal.toReal ) ≤ a - u - ( b - v ) by exact le_trans ( ENNReal.toReal_mono ( by norm_num ) <| MeasureTheory.measure_mono <| show A ∩ Icc ( b - v ) ( a - u ) ⊆ Icc ( b - v ) ( a - u ) from fun x hx => hx.2 ) <| by simp +decide [ *, Real.volume_Icc ] ];
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
          · exact ⟨ ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) ), ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) ) ⟩;
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
  · have h_union : A ∩ Icc (a - 2) (b - 2) ⊆ A ∩ Icc (a - u) (b - u) ∪ A ∩ Icc (a - v) (b - v) := by
      grind;
    refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_union ) _;
    · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_union_le _ _ ) _ );
      refine' lt_of_le_of_lt ( add_le_add ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ) _ ; norm_num;
    · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_union_le _ _ ) _;
      · refine' ne_of_lt ( lt_of_le_of_lt ( add_le_add ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ) _ ) ; norm_num;
      · rw [ ENNReal.toReal_add ] <;> norm_num ; linarith; all_goals exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) )

/-
The left endpoint bound around `2`.
-/
lemma gap_around_two_left
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u₂ s t g : ℝ} (hab : a ≤ b) (hs : s = b - a)
    (hmass : (volume (A ∩ Icc a b)).toReal = (s + t) / 2)
    (hboost : s - t + g < (volume (A ∩ Icc (a - 2) (b - 2))).toReal)
    (huA : u₂ ∈ A) (hu₂ : u₂ ≤ 2) :
    u₂ < 2 - g - (s - t) / 2 := by
  contrapose! hboost;
  have h_complement : (volume (A ∩ Icc (a - 2) (b - 2 + g + (s - t) / 2))).toReal ≤ (b - 2 + g + (s - t) / 2 - (a - 2)) - (volume (A ∩ Icc a b)).toReal := by
    apply translated_source_complement_bound hA hsf huA; all_goals grind;
  refine' le_trans _ ( h_complement.trans _ );
  · gcongr;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
    · grind;
  · grind

/-
The right endpoint bound around `2`.
-/
lemma gap_around_two_right
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b v₂ s t g : ℝ} (hab : a ≤ b) (hs : s = b - a)
    (hmass : (volume (A ∩ Icc a b)).toReal = (s + t) / 2)
    (hboost : s - t + g < (volume (A ∩ Icc (a - 2) (b - 2))).toReal)
    (hvA : v₂ ∈ A) (hv₂ : 2 ≤ v₂) :
    2 + g + (s - t) / 2 < v₂ := by
  contrapose! hboost;
  have h_source_le_ba : (volume (A ∩ Icc a b)).toReal ≤ b - a := by
    refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| Set.inter_subset_right ) _ <;> norm_num [ hab ];
  have hcomp := translated_source_complement_bound hA hsf
    (a := a) (b := b) (p := v₂)
    (l := a - 2 - g - (s - t) / 2) (r := b - 2)
    hvA (by linarith) (by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨by linarith [hw.2.1, hw.2.2], by linarith [hw.2.1, hw.2.2]⟩)
  norm_num at hcomp
  refine le_trans ?_ (hcomp.trans ?_)
  · refine' ENNReal.toReal_mono _ _
    · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
        (by simp +decide [Real.volume_Icc]))
    · exact MeasureTheory.measure_mono
        (Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc (by linarith) le_rfl)
  · linarith

/-
The gap-length bound around `2`.
-/
lemma gap_around_two_length
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u₂ v₂ s t g : ℝ} (hab : a ≤ b) (hs : s = b - a) (hg : 0 ≤ g)
    (hmass : (volume (A ∩ Icc a b)).toReal = (s + t) / 2)
    (hboost : s - t + g < (volume (A ∩ Icc (a - 2) (b - 2))).toReal)
    (huA : u₂ ∈ A) (hu₂ : u₂ ≤ 2) (hvA : v₂ ∈ A) (hv₂ : 2 ≤ v₂) :
    s + g ≤ v₂ - u₂ := by
  contrapose! hboost;
  -- Applying the two_translates_cover_up_to_gap lemma.
  have h_cover : (volume (A ∩ Icc (a - 2) (b - 2))).toReal ≤ g + (volume (A ∩ Icc (a - u₂) (b - u₂))).toReal + (volume (A ∩ Icc (a - v₂) (b - v₂))).toReal := by
    apply two_translates_cover_up_to_gap hu₂ hv₂ hg;
    linarith;
  linarith [ translated_target_complement_bound hA hsf huA hab, translated_target_complement_bound hA hsf hvA hab ]

/-
The paper's lemma locating the nearest points of `A` around `2`.
-/
theorem gap_around_two
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u₂ v₂ s t g : ℝ}
    (hab : a ≤ b) (hs : s = b - a) (hg : 0 ≤ g)
    (hmass : (volume (A ∩ Icc a b)).toReal = (s + t) / 2)
    (hboost : s - t + g < (volume (A ∩ Icc (a - 2) (b - 2))).toReal)
    (huA : u₂ ∈ A) (hu₂ : u₂ ≤ 2)
    (hvA : v₂ ∈ A) (hv₂ : 2 ≤ v₂) :
    u₂ < 2 - g - (s - t) / 2 ∧
    2 + g + (s - t) / 2 < v₂ ∧
    s + g ≤ v₂ - u₂ := by
  have := @gap_around_two_left A hA hsf a b u₂ s t g hab hs hmass hboost huA hu₂;
  exact ⟨ this, by linarith [ gap_around_two_right hA hsf hab hs hmass hboost hvA hv₂ ], by linarith [ gap_around_two_length hA hsf hab hs hg hmass hboost huA hu₂ hvA hv₂ ] ⟩

end ProductFree