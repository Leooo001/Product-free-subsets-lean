import RequestProject.Section4SecondGap

/-!
# Section 4: the parameter `w` and its packing inequality

This file continues the rigidity argument through equation `w ineq` of the paper.  It first
records the numerical combination that produces the mass boost on `[a-2,a]`, proves that
`A ∩ [a-2,a-1]` is nonempty, chooses its rightmost point `a-2+w`, and proves

`F(a) - F(a-2) ≤ 1 - F(2-w)`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
Numerical combination of the two estimates immediately preceding equation
`boost and interval around a` in the paper.
-/
lemma boost_and_interval_around_a
    {a b x s t g : ℝ}
    (hmassI : cum A b - cum A a = (s + t) / 2)
    (hupper : 2 * cum A (x + 1) + cum A (x - 1) ≤
      x - s + cum A b - cum A (a - 2) - g)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hsurplus : 1 - t < cum A (x + 1) - cum A x) :
    1 - t + g + (s - t) / 2 < cum A a - cum A (a - 2) := by
  linarith

/-
Translating one interval piece by an element of a sum-free set and packing it with
another piece in the target interval.
-/
lemma sumfree_translate_pair_mass_le
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {c p q r s : ℝ} (hc : c ∈ A) (hrs : r ≤ s)
    (hr : r = c + p) (hs : s = c + q) :
    (volume (A ∩ Icc p q)).toReal + (volume (A ∩ Icc r s)).toReal ≤ s - r := by
  -- The translation $z \mapsto z + c$ maps $A \cap [p, q]$ into $[r, s]$ and is disjoint from $A \cap [r, s]$.
  have h_trans : (A ∩ Icc p q).image (fun z => z + c) ∩ (A ∩ Icc r s) = ∅ := by
    simp_all +decide [ Set.ext_iff, IsSumFree ];
    grind
  -- The image has the same volume as $A \cap [p, q]$.
  have h_image_volume : (volume ((A ∩ Icc p q).image (fun z => z + c))).toReal = (volume (A ∩ Icc p q)).toReal := by
    simp +zetaDelta at *;
    erw [ show ( fun x => x + -c ) ⁻¹' A ∩ Icc ( p + c ) ( q + c ) = ( fun x => x + -c ) ⁻¹' ( A ∩ Icc p q ) by ext; aesop ] ; erw [ MeasureTheory.measure_preimage_add_right ] ;
  rw [ ← h_image_volume, ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
  · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show ( ( fun z => z + c ) '' ( A ∩ Icc p q ) ∪ A ∩ Icc r s ) ⊆ Icc r s from _ ) _;
    · norm_num;
    · grind;
    · norm_num [ hrs ];
  · exact Set.disjoint_iff_inter_eq_empty.mpr h_trans;
  · exact hA.inter measurableSet_Icc;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( fun z => z + c ) '' ( A ∩ Icc p q ) ⊆ Set.Icc ( c + p ) ( c + q ) from by rintro x ⟨ y, hy, rfl ⟩ ; constructor <;> linarith [ hy.2.1, hy.2.2 ] ) ) ( by simp +decide [ *, Real.volume_Icc ] ) );
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ *, Real.volume_Icc ] ) )

/-
The boost forces the part of `A` in `[a-2,a-1]` to be nonempty.
-/
lemma left_block_nonempty
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    {a b s t g : ℝ}
    (ha : 2 < a) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hs : s = b - a) (ht : t = discOn A a b)
    (hts : t ≤ s) (hg : 0 ≤ g)
    (hboost : 1 - t + g + (s - t) / 2 < cum A a - cum A (a - 2)) :
    (A ∩ Icc (a - 2) (a - 1)).Nonempty := by
  contrapose! hboost; simp_all +decide [ discOn ] ;
  -- Since $A \cap [a-2, a-1] = \emptyset$, we have $\text{cum}(A, a-1) = \text{cum}(A, a-2)$.
  have h_cum_eq : cum A (a - 1) = cum A (a - 2) := by
    rw [ cum, cum ];
    rw [ show A ∩ Icc 0 ( a - 1 ) = ( A ∩ Icc 0 ( a - 2 ) ) ∪ ( A ∩ Ioc ( a - 2 ) ( a - 1 ) ) from ?_, MeasureTheory.measure_union ] <;> norm_num [ Set.ext_iff ] at *;
    · rw [ show A ∩ Ioc ( a - 2 ) ( a - 1 ) = ∅ from Set.eq_empty_of_forall_notMem fun x hx => by linarith [ hboost x hx.1 ( by linarith [ hx.2.1 ] ), hx.2.2 ] ] ; norm_num;
    · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.2.2, hx₂.2.1 ] ;
    · exact hA.inter measurableSet_Ioc;
    · grind;
  -- Apply sumfree_translate_pair_mass_le with c=1, source [a-1,b-1], target [a,b].
  have h_source_target : (volume (A ∩ Icc (a - 1) (b - 1))).toReal + (volume (A ∩ Icc a b)).toReal ≤ b - a := by
    convert sumfree_translate_pair_mass_le hA hsf hone
      (p := a - 1) (q := b - 1) (r := a) (s := b) hab (by ring) (by ring) using 1
  -- Apply cum_sub_cum_eq_mass_Icc to the intervals [a-1, b-1] and [b-1, a].
  have h_cum_sub : cum A (b - 1) - cum A (a - 1) = (volume (A ∩ Icc (a - 1) (b - 1))).toReal ∧ cum A a - cum A (b - 1) = (volume (A ∩ Icc (b - 1) a)).toReal := by
    constructor <;> rw [ cum_sub_cum_eq_mass_Icc ] <;> linarith;
  have h_cum_sub : (volume (A ∩ Icc (b - 1) a)).toReal ≤ (a - (b - 1)) := by
    refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| Set.inter_subset_right ) _ <;> norm_num [ hab, hba ];
  linarith

/-
A compact nonempty left block has a rightmost point, written `a-2+w`.
-/
lemma exists_rightmost_left_block
    (hA : IsCompact A) {a : ℝ} (ha : 2 < a)
    (hne : (A ∩ Icc (a - 2) (a - 1)).Nonempty) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ a - 2 + w ∈ A ∧
      A ∩ Ioc (a - 2 + w) (a - 1) = ∅ ∧
      cum A (a - 1) = cum A (a - 2 + w) := by
  -- Set its greatest element c=sSup K using IsCompact.isGreatest_sSup.
  have h_sup : IsCompact (A ∩ Icc (a - 2) (a - 1)) := by
    exact hA.inter_right isClosed_Icc
  obtain ⟨c, hc⟩ : ∃ c, IsGreatest (A ∩ Icc (a - 2) (a - 1)) c := by
    exact h_sup.exists_isGreatest hne;
  refine' ⟨ c - ( a - 2 ), _, _, _, _, _ ⟩ <;> norm_num [ hc.1.1, hc.1.2.1, hc.1.2.2 ];
  · linarith [ hc.1.2.2 ];
  · exact Set.eq_empty_of_forall_notMem fun x hx => hx.2.1.not_ge <| hc.2 ⟨ hx.1, ⟨ by linarith [ hx.2.1, hc.1.2.1 ], by linarith [ hx.2.2, hc.1.2.2 ] ⟩ ⟩;
  · unfold cum;
    rw [ show A ∩ Icc 0 ( a - 1 ) = ( A ∩ Icc 0 c ) ∪ ( A ∩ Ioc c ( a - 1 ) ) from ?_, MeasureTheory.measure_union ];
    · rw [ show A ∩ Ioc c ( a - 1 ) = ∅ from ?_ ] ; norm_num;
      exact Set.eq_empty_of_forall_notMem fun x hx => hx.2.1.not_ge <| hc.2 ⟨ hx.1, ⟨ by linarith [ hx.2.1, hc.1.2.1 ], by linarith [ hx.2.2, hc.1.2.2 ] ⟩ ⟩;
    · grind;
    · exact hA.measurableSet.inter measurableSet_Ioc;
    · ext x; simp;
      exact ⟨ fun hx => if h : x ≤ c then Or.inl ⟨ hx.1, hx.2.1, h ⟩ else Or.inr ⟨ hx.1, not_le.mp h, hx.2.2 ⟩, fun hx => hx.elim ( fun hx => ⟨ hx.1, hx.2.1, hx.2.2.trans ( hc.1.2.2 ) ⟩ ) fun hx => ⟨ hx.1, hx.2.1.le.trans' ( by linarith [ hc.1.2.1 ] ), hx.2.2 ⟩ ⟩

/-
Equation `w ineq`: if `a-2+w` is the rightmost point of the left block, the two
translate packings in the paper bound all the mass in `[a-2,a]`.
-/
lemma w_inequality
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a w : ℝ} (ha : 2 < a) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hc : a - 2 + w ∈ A)
    (hgap : A ∩ Ioc (a - 2 + w) (a - 1) = ∅) :
    cum A a - cum A (a - 2) ≤ 1 - cum A (2 - w) := by
  -- Let $c = a - 2 + w$. Then $A \cap [a-2,c]$ is the left block.
  set c := a - 2 + w
  have hc : c ∈ A := by
    exact hc
  have hcum : cum A (a - 1) = cum A c := by
    rw [ cum, cum ];
    rw [ show A ∩ Icc 0 ( a - 1 ) = A ∩ Icc 0 c from ?_ ];
    ext x; simp [Set.mem_inter_iff, Set.mem_Icc];
    exact fun hx _ => ⟨ fun hx' => le_of_not_gt fun hx'' => hgap.subset ⟨ hx, ⟨ hx'', hx' ⟩ ⟩, fun hx' => hx'.trans <| by linarith ⟩
  have hcum : cum A a - cum A (a - 1) = cum A a - cum A c := by
    rw [hcum];
  -- By sumfree_translate_pair_mass_le with translating point 1=hmin.1, source [a-2,c], target [a-1,a-1+w], giving the first two increments ≤ w.
  have h1 : (volume (A ∩ Icc (a - 2) c)).toReal + (volume (A ∩ Icc (a - 1) (a - 1 + w))).toReal ≤ w := by
    convert sumfree_translate_pair_mass_le hA hsf hmin.1
      (p := a - 2) (q := c) (r := a - 1) (s := a - 1 + w)
      (by linarith) (by ring) (by linarith) using 1 <;> ring
  -- By sumfree_translate_pair_mass_le with translating point c, source [1,2-w], target [a-1+w,a], giving mass(A∩[1,2-w]) plus final increment ≤1-w.
  have h2 : (volume (A ∩ Icc 1 (2 - w))).toReal + (volume (A ∩ Icc (a - 1 + w) a)).toReal ≤ 1 - w := by
    convert sumfree_translate_pair_mass_le hA hsf hc
      (p := 1) (q := 2 - w) (r := a - 1 + w) (s := a)
      (by linarith) (by ring) (by ring) using 1 <;> ring
  -- By cum_sub_cum_eq_mass_Icc and cum_one_eq_zero_of_isLeast hmin, that source mass equals cum(2-w).
  have h3 : (volume (A ∩ Icc 1 (2 - w))).toReal = cum A (2 - w) := by
    rw [ ← cum_sub_cum_eq_mass_Icc ];
    · rw [ cum_one_eq_zero_of_isLeast hmin ] ; norm_num;
    · norm_num;
    · linarith;
  -- By cum_sub_cum_eq_mass_Icc, express each target/source interval mass as cumulative increments.
  have h4 : (volume (A ∩ Icc (a - 2) c)).toReal = cum A c - cum A (a - 2) := by
    rw [ ← cum_sub_cum_eq_mass_Icc ]; all_goals linarith
  have h5 : (volume (A ∩ Icc (a - 1) (a - 1 + w))).toReal = cum A (a - 1 + w) - cum A (a - 1) := by
    rw [ ← cum_sub_cum_eq_mass_Icc ]; all_goals linarith
  have h6 : (volume (A ∩ Icc (a - 1 + w) a)).toReal = cum A a - cum A (a - 1 + w) := by
    rw [ ← cum_sub_cum_eq_mass_Icc ]; all_goals linarith;
  linarith

/-
Paper-form conclusion through equation `w ineq`, including the construction of `w`.
-/
theorem exists_w_with_inequality
    (hA : IsCompact A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b s t g : ℝ}
    (ha : 2 < a) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hs : s = b - a) (ht : t = discOn A a b)
    (hts : t ≤ s) (hg : 0 ≤ g)
    (hboost : 1 - t + g + (s - t) / 2 < cum A a - cum A (a - 2)) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ a - 2 + w ∈ A ∧
      A ∩ Ioc (a - 2 + w) (a - 1) = ∅ ∧
      cum A a - cum A (a - 2) ≤ 1 - cum A (2 - w) := by
  obtain ⟨w, hw0, hw1, hc, hgap, _hcum⟩ : ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ a - 2 + w ∈ A ∧ A ∩ Ioc (a - 2 + w) (a - 1) = ∅ ∧ cum A (a - 1) = cum A (a - 2 + w) := by
    apply exists_rightmost_left_block hA ha;
    apply left_block_nonempty;
    exact hA.measurableSet;
    exact hsf;
    exact hmin.1;
    all_goals tauto;
  use w;
  exact ⟨ hw0, hw1, hc, hgap, w_inequality hA.measurableSet hsf hmin ha hw0 hw1 hc hgap ⟩

end ProductFree