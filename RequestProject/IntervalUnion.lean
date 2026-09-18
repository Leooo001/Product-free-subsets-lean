import RequestProject.EdgeDisc

/-!
# Finite unions of finite closed intervals

Theorem `offdiagonal_main2` is proved by induction on the number of component intervals of a
finite union of finite closed intervals. This file introduces the representation used for that
induction and its basic properties.

`IsIntervalUnion A ivs` says that `A` is the union of the closed intervals in the sorted,
strictly separated list `ivs : List (ℝ × ℝ)`: each pair `p` satisfies `p.1 ≤ p.2`, consecutive
pairs `p, q` satisfy `p.2 < q.1`, and `A = ⋃ p ∈ ivs, [p.1, p.2]`. The length of `ivs` is then
the number of component intervals of `A`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

/-- `A` is the finite union of the closed intervals in the sorted, strictly separated list
`ivs`. The length of `ivs` is the number of component intervals. -/
def IsIntervalUnion (A : Set ℝ) (ivs : List (ℝ × ℝ)) : Prop :=
  (∀ p ∈ ivs, p.1 ≤ p.2) ∧ ivs.IsChain (fun p q => p.2 < q.1) ∧
    A = ⋃ p ∈ ivs, Set.Icc p.1 p.2

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
A finite union of closed intervals is closed.
-/
lemma IsIntervalUnion.isClosed (h : IsIntervalUnion A ivs) : IsClosed A := by
  obtain ⟨h₁, h₂, h₃⟩ := h;
  convert isClosed_biUnion_finset fun p hp => isClosed_Icc;
  any_goals exact ivs.toFinset;
  rotate_left;
  exacts [ fun _ => inferInstance, fun p => p.1, fun p => p.2, fun p hp => inferInstance, by simpa [ h₃ ] ]

/-
A finite union of finite closed intervals has finite measure.
-/
lemma IsIntervalUnion.finite (h : IsIntervalUnion A ivs) : volume A ≠ ⊤ := by
  obtain ⟨ h1, h2, h3 ⟩ := h;
  refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ⊆ ⋃ p ∈ ivs.toFinset, Icc p.1 p.2 from _ ) ) _ );
  · aesop;
  · refine' lt_of_le_of_lt ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
    simp +zetaDelta at *

/-
A finite union of closed intervals with a nonempty list is nonempty.
-/
lemma IsIntervalUnion.nonempty (h : IsIntervalUnion A ivs) (hne : ivs ≠ []) : A.Nonempty := by
  rcases ivs <;> simp_all +decide [ IsIntervalUnion ]

/-
`A` is contained in `Icc (ivs.head).1 (ivs.getLast).2` (the convex hull of its endpoints).
-/
lemma IsIntervalUnion.subset_Icc (h : IsIntervalUnion A ivs) (hne : ivs ≠ []) :
    A ⊆ Icc ((ivs.head hne).1) ((ivs.getLast hne).2) := by
  rcases h with ⟨ hle, hchain, rfl ⟩;
  -- By definition of `IsChain`, the list `ivs` is sorted, so for any `p ∈ ivs`, we have `(ivs.head hne).1 ≤ p.1` and `p.2 ≤ (ivs.getLast hne).2`.
  have h_sorted : ∀ p ∈ ivs, (ivs.head hne).1 ≤ p.1 ∧ p.2 ≤ (ivs.getLast hne).2 := by
    induction' ivs with p ivs ih <;> simp_all +decide [ List.IsChain ];
    rcases ivs <;> simp_all +decide [ List.IsChain ];
    grind;
  exact Set.iUnion₂_subset fun p hp => Set.Icc_subset_Icc ( h_sorted p hp |>.1 ) ( h_sorted p hp |>.2 )

/-
A finite union of finite closed intervals is compact.
-/
lemma IsIntervalUnion.isCompact (h : IsIntervalUnion A ivs) : IsCompact A := by
  obtain ⟨h₁, h₂, h₃⟩ := h;
  exact h₃ ▸ Set.Finite.isCompact_biUnion ( List.finite_toSet ivs ) fun p hp => CompactIccSpace.isCompact_Icc

/-
The minimum of a nonempty interval-union is the first component's left endpoint.
-/
lemma IsIntervalUnion.sInf_eq (h : IsIntervalUnion A ivs) (hne : ivs ≠ []) :
    sInf A = (ivs.head hne).1 := by
  apply le_antisymm;
  · refine' csInf_le _ _;
    · exact ⟨ _, fun x hx => h.subset_Icc hne hx |>.1 ⟩;
    · exact h.2.2.symm ▸ Set.mem_iUnion₂.mpr ⟨ _, List.head_mem hne, Set.left_mem_Icc.mpr <| h.1 _ <| List.head_mem hne ⟩;
  · refine' le_csInf ( h.nonempty hne ) _;
    exact fun x hx => h.subset_Icc hne hx |>.1

/-
The maximum of a nonempty interval-union is the last component's right endpoint.
-/
lemma IsIntervalUnion.sSup_eq (h : IsIntervalUnion A ivs) (hne : ivs ≠ []) :
    sSup A = (ivs.getLast hne).2 := by
  refine' le_antisymm _ _;
  · refine' csSup_le _ _;
    · exact h.nonempty hne;
    · exact fun x hx => h.subset_Icc hne hx |>.2;
  · refine' le_csSup _ _;
    · exact ⟨ _, fun x hx => h.subset_Icc hne hx |>.2 ⟩;
    · convert Set.mem_iUnion₂.mpr _;
      convert h.2.2;
      exact ⟨ _, List.getLast_mem hne, h.1 _ ( List.getLast_mem hne ) |> fun h => ⟨ by linarith, by linarith ⟩ ⟩

private def clipValid (l r : ℝ) (p : ℝ × ℝ) : Bool :=
  decide (max p.1 l ≤ min p.2 r)

private def clipPair (l r : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (max p.1 l, min p.2 r)

private lemma clipPair_valid {l r : ℝ} {p : ℝ × ℝ}
    (hp : clipValid l r p = true) : (clipPair l r p).1 ≤ (clipPair l r p).2 := by
  simp_all +decide [ clipValid, clipPair ]

private lemma clipPair_separated {l r : ℝ} {p q : ℝ × ℝ}
    (hpq : p.2 < q.1) : (clipPair l r p).2 < (clipPair l r q).1 := by
  exact lt_of_le_of_lt ( min_le_left _ _ ) ( lt_of_lt_of_le hpq ( le_max_left _ _ ) )

private lemma interval_inter_eq_clip {l r : ℝ} {p : ℝ × ℝ} :
    Icc p.1 p.2 ∩ Icc l r =
      if clipValid l r p then Icc (clipPair l r p).1 (clipPair l r p).2 else ∅ := by
  unfold clipValid clipPair;
  grind +revert

/-
Intersecting a finite union of closed intervals with a closed interval again gives a
finite union of closed intervals.  The component list may be empty.
-/
lemma IsIntervalUnion.inter_Icc_exists (h : IsIntervalUnion A ivs) (l r : ℝ) :
    ∃ clipped : List (ℝ × ℝ), IsIntervalUnion (A ∩ Icc l r) clipped := by
  refine' ⟨ ( ivs.filter ( clipValid l r ) |> List.map ( clipPair l r ) ), _, _, _ ⟩ <;> simp_all +decide [ IsIntervalUnion ];
  · grind +locals;
  · rw [ List.isChain_iff_getElem ] at *;
    have := List.pairwise_iff_get.mp ( show List.Pairwise ( fun p q => p.2 < q.1 ) ( List.filter ( clipValid l r ) ivs ) from ?_ ) ; simp_all +decide [ List.pairwise_iff_get ] ;
    · intro i hi; specialize this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self i ) ; simp_all +decide [ clipPair ] ;
    · have h_pairwise : List.Pairwise (fun p q => p.2 < q.1) ivs := by
        rw [ List.pairwise_iff_getElem ];
        intro i j hi hj hij; induction hij <;> simp_all +decide [ List.getElem?_eq_getElem ] ;
        grind +qlia;
      exact h_pairwise.filter _;
  · simp +decide [ Set.ext_iff, clipValid, clipPair ];
    grind

end ProductFree