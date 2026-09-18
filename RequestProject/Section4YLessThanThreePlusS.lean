import RequestProject.Section4W

/-!
# Section 4: the upper bound `y < 3 + s`

This file formalizes the two lemmas following equation `w ineq`.  The first auxiliary
estimate is the paper's Lemma `c lem`; the two main conclusions are `y < 4-w+s` and,
finally, `y < 3+s`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-- The algebraic conclusion of Lemma `c lem`, after the three disjoint sumset
contributions have been packed into `[a+1,x-1]`. -/
lemma c_lower_bound_of_sumset_packing
    {a b c s y g : ℝ}
    (hpack : 2 * cum A c + (volume (A ∩ Icc (a + mMinus A c) b)).toReal +
        2 * (cum A (y - 2) - cum A (c + s)) ≤ 2 * cum A (y - 2) + g) :
    g ≥ (volume (A ∩ Icc (a + mMinus A c) b)).toReal -
      2 * (cum A (c + s) - cum A c) := by
  linarith

/-
Removing an initial interval of length `m` from `[a,b]` loses at most `m`
of the mass of `A`.
-/
lemma mass_truncated_from_left
    (hA : MeasurableSet A) {a b m : ℝ} (hab : a ≤ b) (hm0 : 0 ≤ m) :
    (volume (A ∩ Icc a b)).toReal - m ≤
      (volume (A ∩ Icc (a + m) b)).toReal := by
  by_cases hbm : b ≤ a + m <;> simp_all +decide [ Set.inter_assoc, Set.Icc_inter_Icc ];
  · refine' le_trans ( ENNReal.toReal_mono _ _ ) _;
    exact ENNReal.ofReal m;
    · norm_num;
    · exact le_trans ( MeasureTheory.measure_mono ( show A ∩ Icc a b ⊆ Icc a ( a + m ) by exact fun x hx => ⟨ hx.2.1, by linarith [ hx.2.2 ] ⟩ ) ) ( by simp +decide [ hab, hm0 ] );
    · exact le_add_of_nonneg_of_le ( by positivity ) ( by rw [ ENNReal.toReal_ofReal hm0 ] );
  · have h_split : (volume (A ∩ Icc a b)).toReal = (volume (A ∩ Icc a (a + m))).toReal + (volume (A ∩ Ioc (a + m) b)).toReal := by
      rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
      · rw [ ← Set.inter_union_distrib_left, Set.Icc_union_Ioc_eq_Icc ] <;> linarith;
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Set.mem_Icc.mp hx₁.2, Set.mem_Ioc.mp hx₂.2 ] ;
      · exact hA.inter measurableSet_Ioc;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hab, hm0 ] ) );
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hab, hm0, hbm ] ) );
    rw [ h_split, add_comm ];
    gcongr;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hab, hm0 ] ) );
    · exact Set.Ioc_subset_Icc_self;
    · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc a ( a + m ) ⊆ Icc a ( a + m ) from Set.inter_subset_right ) _ <;> norm_num [ hm0 ]

/-
For a nonnegative set, the left endpoint discrepancy at `c` is at most `F(c)`.
-/
lemma mMinus_le_cum
    (hA : MeasurableSet A) (hAfin : volume A ≠ ⊤) (hAnonneg : A ⊆ Ici 0)
    {c : ℝ} (hc : 0 ≤ c) : mMinus A c ≤ cum A c := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ c, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ r, hr, rfl ⟩;
    by_cases hr' : r < 0 <;> simp_all +decide [ discOn ];
    · -- Since $r < 0$, we have $A \cap [r, c] = A \cap [0, c]$.
      have h_inter : A ∩ Icc r c = A ∩ Icc 0 c := by
        grind;
      rw [ h_inter, cum ];
      linarith [ show ( volume ( A ∩ Icc 0 c ) |> ENNReal.toReal ) ≤ c by exact le_trans ( ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( show A ∩ Icc 0 c ⊆ Icc 0 c from fun x hx => hx.2 ) ) ) ( by simp +decide [ hc ] ) ];
    · -- Since $A$ is nonnegative, we have $cum A c \geq volume (A ∩ Icc r c)$.
      have h_cum_ge_volume : cum A c ≥ (volume (A ∩ Icc r c)).toReal := by
        refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc ( 0 : ℝ ) c ⊇ A ∩ Icc r c from fun x hx => ⟨ hx.1, by constructor <;> linarith [ hx.2.1, hx.2.2 ] ⟩ );
        · rfl;
        · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
      linarith [ show ( volume ( A ∩ Icc r c ) |> ENNReal.toReal ) ≤ c - r by exact le_trans ( ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( show A ∩ Icc r c ⊆ Icc r c from fun x hx => hx.2 ) ) ) ( by simp +decide [ hr ] ) ]

/-
Cumulative mass is monotone.
-/
lemma section4_cum_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) : cum A p ≤ cum A q := by
  convert ENNReal.toReal_mono _ ( MeasureTheory.measure_mono ( show A ∩ Icc 0 p ⊆ A ∩ Icc 0 q from Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right hpq ) ) using 1;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hpq ] ) );
  · infer_instance

/-
If `c` is the greatest point of `A` in `[1,d]`, then the mass of `[c,c+s]`
is bounded by the mass in any terminal interval `[d,d+s]`. Endpoints do not affect
Lebesgue measure.
-/
lemma mass_Icc_of_greatest_le_terminal
    (hA : MeasurableSet A) {c d s : ℝ} (hs : 0 ≤ s)
    (hcA : c ∈ A) (hcd : c ≤ d)
    (hgreat : ∀ z ∈ A, z ≤ d → z ≤ c) :
    (volume (A ∩ Icc c (c + s))).toReal ≤
      (volume (A ∩ Icc d (d + s))).toReal := by
  -- In this case, $A \cap [c, c + s]$ is a subset of $A \cap [d, d + s]$ modulo the null set $\{c\}$.
  have h_subset : A ∩ Icc c (c + s) ⊆ (A ∩ Icc d (d + s)) ∪ {c} := by
    grind;
  -- Since the volume of a union is less than or equal to the sum of the volumes, and the volume of {c} is zero, we have:
  have h_volume_union : volume (A ∩ Icc c (c + s)) ≤ volume (A ∩ Icc d (d + s)) + volume ({c} : Set ℝ) := by
    exact le_trans ( MeasureTheory.measure_mono h_subset ) ( MeasureTheory.measure_union_le _ _ );
  convert ENNReal.toReal_mono _ h_volume_union using 1 <;> norm_num;
  exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hs ] ) )

/-
The reflection used in the final argument sends the terminal interval before `y-2`
into the complement of the discrepancy-maximizing interval.
-/
lemma terminal_mass_le_interval_complement
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b x y s t : ℝ}
    (hx : x - 1 ∈ A) (hy : y = x + 1 - a) (hs : s = b - a)
    (ht : t = discOn A a b) (hab : a ≤ b) :
    (volume (A ∩ Icc (y - 2 - s) (y - 2))).toReal ≤ (s - t) / 2 := by
  have h_reflection : (volume (A ∩ Icc (y - 2 - s) (y - 2))).toReal ≤ (b - a) - (volume (A ∩ Icc a b)).toReal := by
    convert ProductFree.reflection_mass_le_interval_complement hA hsf hx _ _ _ using 1; all_goals linarith;
  unfold discOn at *; linarith;

/-
The translate by the rightmost point `a-2+w` gives the analogous estimate used
in the proof of `y < 4-w+s`.
-/
lemma terminal_mass_le_interval_complement_w
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b c s t w : ℝ}
    (hp : a - 2 + w ∈ A) (hc : c ≤ 2 - w)
    (hs : s = b - a) (ht : t = discOn A a b) (hab : a ≤ b) :
    (volume (A ∩ Icc (2 - w) (c + s))).toReal ≤ (s - t) / 2 := by
  -- By definition of $t$, we know that $t = discOn A a b$.
  rw [ht] at *;
  by_contra h_contra; push_neg at h_contra; (
  -- Apply the sumfree_translate_pair_mass_le lemma with translating point a-2+w, source [2-w,c+s], target [a,a-2+w+c+s].
  have h_sumfree_translate : (volume (A ∩ Icc (2 - w) (c + s))).toReal + (volume (A ∩ Icc a (a - 2 + w + c + s))).toReal ≤ (a - 2 + w + c + s) - a := by
    convert sumfree_translate_pair_mass_le hA hsf hp _ _ using 1;
    rotate_left;
    exact 2 - w;
    exact c + s;
    exact a;
    exact a - 2 + w + c + s;
    · contrapose! h_contra;
      rw [ show A ∩ Icc ( 2 - w ) ( c + s ) = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro x ⟨ hx₁, hx₂ ⟩ ; linarith [ hx₂.1, hx₂.2 ] ] ; norm_num;
      unfold discOn;
      linarith [ show ( volume ( A ∩ Icc a b ) |> ENNReal.toReal ) ≤ b - a by exact le_trans ( ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( show A ∩ Icc a b ⊆ Icc a b from fun x hx => hx.2 ) ) ) ( by simp +decide [ hab ] ) ];
    · ring;
    · exact ⟨ fun h => fun _ => h, fun h => h <| by ring ⟩;
  have h_volume_le : (volume (A ∩ Icc a b)).toReal = (volume (A ∩ Icc a (a - 2 + w + c + s))).toReal + (volume (A ∩ Ioc (a - 2 + w + c + s) b)).toReal := by
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
    · rw [ ← Set.inter_union_distrib_left, Set.Icc_union_Ioc_eq_Icc ] <;> try linarith;
      linarith [ show 0 ≤ ( volume ( A ∩ Icc ( 2 - w ) ( c + s ) ) |> ENNReal.toReal ) from ENNReal.toReal_nonneg, show 0 ≤ ( volume ( A ∩ Icc a ( a - 2 + w + c + s ) ) |> ENNReal.toReal ) from ENNReal.toReal_nonneg ];
    · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.2.2, hx₂.2.1 ] ;
    · exact hA.inter measurableSet_Ioc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hs ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Ioc ( a - 2 + w + c + s ) b ⊆ Set.Ioc ( a - 2 + w + c + s ) b from fun x hx => hx.2 ) ) ( by simp +decide [ hab ] ) );
  have h_volume_le : (volume (A ∩ Ioc (a - 2 + w + c + s) b)).toReal ≤ (volume (Ioc (a - 2 + w + c + s) b)).toReal := by
    apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
    · norm_num [ Real.volume_Ioc ];
    · exact Set.inter_subset_right;
  simp_all +decide [ discOn ];
  rw [ ENNReal.toReal_ofReal ] at h_volume_le <;> linarith);

/-
The first of the paper's two upper bounds for `y`.
-/
theorem y_lt_four_sub_w_add_s
    (hA : IsCompact A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    (hAnonneg : A ⊆ Ici 0) (hAfin : volume A ≠ ⊤)
    {a b y s t g w : ℝ}
    (hab : a ≤ b) (hs0 : 0 ≤ s) (hs : s = b - a)
    (ht : t = discOn A a b) (hmass : (volume (A ∩ Icc a b)).toReal = (s + t) / 2)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp : a - 2 + w ∈ A)
    (hboost : 1 - t + g + (s - t) / 2 < cum A a - cum A (a - 2))
    (hwineq : cum A a - cum A (a - 2) ≤ 1 - cum A (2 - w))
    (hc_bound : ∀ c ∈ A, c ≤ y - s - 2 →
      g ≥ (volume (A ∩ Icc (a + mMinus A c) b)).toReal -
        2 * (cum A (c + s) - cum A c)) :
    y < 4 - w + s := by
  by_contra h_contra;
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c ∈ A ∧ 1 ≤ c ∧ c ≤ 2 - w ∧ ∀ z ∈ A, 1 ≤ z → z ≤ 2 - w → z ≤ c := by
    have h_compact : IsCompact (A ∩ Set.Icc 1 (2 - w)) := by
      exact hA.inter ( CompactIccSpace.isCompact_Icc );
    have := h_compact.exists_isGreatest;
    exact Exists.elim ( this ⟨ 1, hmin.1, by norm_num, by linarith ⟩ ) fun x hx => ⟨ x, hx.1.1, hx.1.2.1, hx.1.2.2, fun z hz hz' hz'' => hx.2 ⟨ hz, hz', hz'' ⟩ ⟩;
  have hc_bound : g ≥ (volume (A ∩ Icc (a + mMinus A c) b)).toReal - (s - t) := by
    refine le_trans ?_ ( hc_bound c hc.1 ?_ );
    · gcongr;
      have := mass_Icc_of_greatest_le_terminal ( show MeasurableSet A from hA.measurableSet ) ( show 0 ≤ s from hs0 ) hc.1 ( show c ≤ 2 - w from by linarith ) ( show ∀ z ∈ A, z ≤ 2 - w → z ≤ c from fun z hz hz' => hc.2.2.2 z hz ( by linarith [ hmin.2 hz ] ) hz' );
      convert mul_le_mul_of_nonneg_left ( this.trans ( terminal_mass_le_interval_complement_w ( show MeasurableSet A from hA.measurableSet ) hsf hp ( by linarith ) hs ht hab ) ) zero_le_two using 1;
      · rw [ cum_sub_cum_eq_mass_Icc ]; all_goals linarith;
      · ring;
    · linarith;
  have h_truncated : (volume (A ∩ Icc (a + mMinus A c) b)).toReal ≥ (volume (A ∩ Icc a b)).toReal - mMinus A c := by
    apply mass_truncated_from_left;
    · exact hA.measurableSet;
    · linarith;
    · grind +suggestions;
  have h_cum_le : cum A c ≤ cum A (2 - w) := by
    apply_rules [ section4_cum_mono ];
    · tauto;
    · grind;
  linarith [ mMinus_le_cum ( show MeasurableSet A from hA.measurableSet ) hAfin hAnonneg ( show 0 ≤ c by linarith ) ]

/-
The paper's final conclusion at this stage: `y < 3+s`.
-/
theorem y_lt_three_add_s
    (hA : IsCompact A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    (hAnonneg : A ⊆ Ici 0) (hAfin : volume A ≠ ⊤)
    {a b x y s t g w : ℝ}
    (hab : a ≤ b) (hs0 : 0 ≤ s) (hs : s = b - a)
    (ht : t = discOn A a b) (hmass : (volume (A ∩ Icc a b)).toReal = (s + t) / 2)
    (hx : x - 1 ∈ A) (hy : y = x + 1 - a)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp : a - 2 + w ∈ A)
    (hboost : 1 - t + g + (s - t) / 2 < cum A a - cum A (a - 2))
    (hwineq : cum A a - cum A (a - 2) ≤ 1 - cum A (2 - w))
    (hc_bound : ∀ c ∈ A, c ≤ y - s - 2 →
      g ≥ (volume (A ∩ Icc (a + mMinus A c) b)).toReal -
        2 * (cum A (c + s) - cum A c)) :
    y < 3 + s := by
  by_contra h_contra;
  -- By compactness, there exists a greatest element $c$ in $A \cap [1, y - s - 2]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ A ∩ Icc 1 (y - s - 2), ∀ z ∈ A ∩ Icc 1 (y - s - 2), z ≤ c := by
    apply_rules [ IsCompact.exists_isGreatest, hA ];
    · exact hA.inter_right ( isClosed_Icc );
    · exact ⟨ 1, hmin.1, by norm_num; linarith ⟩;
  -- By greatestness, mass[c,c+s] ≤ mass[y-2-s,y-2] (mass_Icc_of_greatest_le_terminal with d=y-2-s), then terminal_mass_le_interval_complement gives ≤(s-t)/2.
  have h_mass_le : (volume (A ∩ Icc c (c + s))).toReal ≤ (s - t) / 2 := by
    have h_mass_le : (volume (A ∩ Icc c (c + s))).toReal ≤ (volume (A ∩ Icc (y - s - 2) (y - 2))).toReal := by
      convert mass_Icc_of_greatest_le_terminal _ _ _ _ _ using 1;
      any_goals exact hc.1.2.2;
      · ring;
      · exact hA.measurableSet;
      · linarith;
      · exact hc.1.1;
      · exact fun z hz hz' => hc.2 z ⟨ hz, ⟨ by linarith [ hmin.2 hz ], by linarith ⟩ ⟩;
    refine le_trans h_mass_le ?_;
    convert terminal_mass_le_interval_complement hA.measurableSet hsf hx hy hs ht hab using 1;
    ring;
  -- Use mass_truncated_from_left and hmass to lower bound truncated mass by (s+t)/2-mMinus(c).
  have h_truncated_mass : (volume (A ∩ Icc (a + mMinus A c) b)).toReal ≥ (s + t) / 2 - mMinus A c := by
    have h_truncated_mass : (volume (A ∩ Icc a b)).toReal - mMinus A c ≤ (volume (A ∩ Icc (a + mMinus A c) b)).toReal := by
      apply mass_truncated_from_left;
      · exact hA.measurableSet;
      · linarith;
      · grind +suggestions;
    linarith;
  -- Combine hboost to get cum(a)-cum(a-2)>1-mMinus(c).
  have h_cum_gt : cum A a - cum A (a - 2) > 1 - mMinus A c := by
    have h_cum_gt : cum A (c + s) - cum A c ≤ (volume (A ∩ Icc c (c + s))).toReal := by
      rw [ ← ENNReal.toReal_ofReal ( sub_nonneg.mpr <| section4_cum_mono ?_ ?_ ) ];
      · unfold cum;
        rw [ ENNReal.toReal_ofReal ];
        · rw [ ← ENNReal.toReal_sub_of_le ];
          · rw [ ← MeasureTheory.measure_diff ];
            · refine' ENNReal.toReal_mono _ _;
              · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
              · refine' MeasureTheory.measure_mono _;
                grind;
            · exact Set.inter_subset_inter_right _ ( Set.Icc_subset_Icc_right ( by linarith ) );
            · exact hA.measurableSet.nullMeasurableSet.inter ( measurableSet_Icc.nullMeasurableSet );
            · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc 0 c ⊆ A from fun x hx => hx.1 ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
          · exact MeasureTheory.measure_mono ( Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right <| by linarith );
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
        · refine' sub_nonneg_of_le _;
          gcongr;
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
          · linarith;
      · linarith [ hc.1.2.1 ];
      · linarith;
    linarith [ hc_bound c hc.1.1 ( by linarith [ hc.1.2.2 ] ) ];
  -- By mMinus_le_cum, we have mMinus A c ≤ cum A c.
  have h_mMinus_le_cum : mMinus A c ≤ cum A c := by
    apply_rules [ mMinus_le_cum ];
    · exact hA.measurableSet;
    · exact hc.1.1;
  -- By cum monotonicity contraposition, we have c > 2 - w.
  have h_c_gt_2_minus_w : c > 2 - w := by
    contrapose! h_cum_gt;
    exact le_trans hwineq ( by linarith [ show cum A ( 2 - w ) ≥ cum A c from section4_cum_mono ( show 0 ≤ c by linarith [ hc.1.2.1 ] ) ( by linarith ) ] );
  linarith [ hc.1.2.2, y_lt_four_sub_w_add_s hA hsf hmin hAnonneg hAfin hab hs0 hs ht hmass hw0 hw1 hp hboost hwineq hc_bound ]

end ProductFree