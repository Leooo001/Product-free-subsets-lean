import RequestProject.OffdiagonalInduction

/-!
# Section 4: preparatory lemmas

This file begins the formalization of Section 4, the rigidity argument proving the key lemma.
It records the one-sided discrepancy based at a point and the first elementary consequence of
sum-freeness used throughout the section.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-- The largest discrepancy of an interval whose right endpoint is `z`:
`m_A^-(z) = sup_{r ≤ z} d_A([r,z])`. -/
noncomputable def mMinus (A : Set ℝ) (z : ℝ) : ℝ :=
  sSup {d : ℝ | ∃ r, r ≤ z ∧ d = discOn A r z}

/-- The largest discrepancy of an interval whose left endpoint is `z`:
`m_A^+(z) = sup_{r ≥ z} d_A([z,r])`. -/
noncomputable def mPlus (A : Set ℝ) (z : ℝ) : ℝ :=
  sSup {d : ℝ | ∃ r, z ≤ r ∧ d = discOn A z r}

/-
A sum-free set containing `1` cannot contain two points differing by `1`.
-/
lemma IsSumFree.not_mem_add_one (hsf : IsSumFree A) (hone : 1 ∈ A)
    {u : ℝ} (hu : u ∈ A) : u + 1 ∉ A := by
  exact fun h => hsf hu hone h

/-
The one-sided discrepancies are bounded by the global discrepancy.
-/
lemma mMinus_le_disc (hfin : volume A ≠ ⊤) (z : ℝ) : mMinus A z ≤ disc A := by
  refine' csSup_le _ _ <;> norm_num;
  · exact ⟨ _, ⟨ z, le_rfl, rfl ⟩ ⟩;
  · exact fun b x hx hb => hb ▸ ProductFree.discOn_le_disc hfin hx

lemma mPlus_le_disc (hfin : volume A ≠ ⊤) (z : ℝ) : mPlus A z ≤ disc A := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ z, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ r, hr, rfl ⟩ ; exact discOn_le_disc hfin hr;

/-
The one-sided discrepancies are nonnegative (the degenerate interval is admissible).
-/
lemma mMinus_nonneg (hfin : volume A ≠ ⊤) (z : ℝ) : 0 ≤ mMinus A z := by
  -- The value 0 belongs to the mMinus set because discOn A z z = 0 (empty interval).
  have h_zero_in_set : 0 ∈ {d : ℝ | ∃ r, r ≤ z ∧ d = discOn A r z} := by
    use z;
    unfold discOn;
    cases eq_or_ne ( A ∩ { z } ) ∅ <;> simp_all +decide;
  refine' le_csSup _ h_zero_in_set;
  exact ⟨ disc A, by rintro x ⟨ r, hr, rfl ⟩ ; exact discOn_le_disc hfin hr ⟩

lemma mPlus_nonneg (hfin : volume A ≠ ⊤) (z : ℝ) : 0 ≤ mPlus A z := by
  refine' le_csSup _ _;
  · exact ⟨ disc A, by rintro x ⟨ r, hr, rfl ⟩ ; exact discOn_le_disc hfin ( by linarith ) ⟩;
  · unfold discOn;
    refine' ⟨ z, le_rfl, _ ⟩ ; norm_num;
    exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_singleton z ) |> fun h => h.symm ▸ by norm_num;

/-
A basic packing consequence for an interval of length exactly two.
-/
lemma sumFree_mass_Icc_two_le_one (hA : MeasurableSet A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    (r : ℝ) : (volume (A ∩ Icc r (r + 2))).toReal ≤ 1 := by
  -- By definition of $U$ and $V$, we have $A \cap [r, r+2] = U \cup V$.
  have h_union : A ∩ Set.Icc r (r + 2) = (A ∩ Set.Icc r (r + 1)) ∪ (A ∩ Set.Ioc (r + 1) (r + 2)) := by
    grind;
  -- Since $U$ and $(V-1)$ are disjoint subsets of $[r, r+1]$, we have $|U| + |V| \leq 1$.
  have h_disjoint : (volume (A ∩ Set.Icc r (r + 1))).toReal + (volume ((fun x => x + 1) ⁻¹' (A ∩ Set.Ioc (r + 1) (r + 2)))).toReal ≤ 1 := by
    rw [ ← ENNReal.toReal_add ];
    · rw [ ← MeasureTheory.measure_union ];
      · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show A ∩ Icc r ( r + 1 ) ∪ ( fun x => x + 1 ) ⁻¹' ( A ∩ Ioc ( r + 1 ) ( r + 2 ) ) ⊆ Set.Icc r ( r + 1 ) from _ ) _ <;> norm_num;
        grind;
      · simp +contextual [ Set.disjoint_left ];
        exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ => False.elim <| hsf hx₁ hone hx₄;
      · exact measurableSet_preimage ( measurable_id.add_const _ ) ( hA.inter measurableSet_Ioc );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( fun x => x + 1 ) ⁻¹' ( A ∩ Ioc ( r + 1 ) ( r + 2 ) ) ⊆ Set.Icc r ( r + 1 ) from fun x hx => by norm_num at *; constructor <;> linarith ) ) ( by norm_num ) );
  rw [ h_union, MeasureTheory.measure_union ];
  · rw [ ENNReal.toReal_add ];
    · convert h_disjoint using 1;
      rw [ MeasureTheory.measure_preimage_add_right ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) );
  · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Set.mem_Icc.mp hx₁.2, Set.mem_Ioc.mp hx₂.2 ] ;
  · exact hA.inter measurableSet_Ioc

/-
A basic packing consequence of sum-freeness used repeatedly in Section 4: if `1 ∈ A`,
then an interval of length at most two contains at most one unit of `A`-mass.
-/
lemma sumFree_mass_Icc_le_one (hA : MeasurableSet A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    {r s : ℝ} (hlen : s - r ≤ 2) :
    (volume (A ∩ Icc r s)).toReal ≤ 1 := by
  refine' le_trans _ ( sumFree_mass_Icc_two_le_one hA hsf hone r );
  gcongr;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by norm_num ) );
  · linarith

/-
The cumulative mass function is `1`-Lipschitz. This is the regularity input in the
positive-triple reduction at the start of the Section 4 contradiction argument.
-/
lemma lipschitzWith_one_cum (A : Set ℝ) : LipschitzWith 1 (cum A) := by
  have h_lip : ∀ x y : ℝ, x ≤ y → (cum A y - cum A x) ≤ y - x := by
    unfold cum;
    intro x y hxy
    have h_diff : volume (A ∩ Icc 0 y) ≤ volume (A ∩ Icc 0 x) + volume (Ioc x y) := by
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      grind;
    by_cases h : volume ( A ∩ Icc 0 y ) = ⊤ <;> by_cases h' : volume ( A ∩ Icc 0 x ) = ⊤ <;> simp_all +decide;
    · exact False.elim <| h <| top_unique <| h'.symm ▸ MeasureTheory.measure_mono ( Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right hxy );
    · convert ENNReal.toReal_mono _ h_diff using 1 <;> norm_num [ h, h' ];
      rw [ ENNReal.toReal_add ] <;> norm_num [ h', h ];
      rw [ add_comm, ENNReal.toReal_ofReal ( sub_nonneg.mpr hxy ) ];
  have h_lip : ∀ x y : ℝ, x ≤ y → |cum A y - cum A x| ≤ y - x := by
    intro x y hxy
    have h_nonneg : 0 ≤ cum A y - cum A x := by
      exact sub_nonneg_of_le ( ENNReal.toReal_mono ( by
        exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide ) ) ) ( MeasureTheory.measure_mono ( Set.inter_subset_inter ( Set.Subset.refl _ ) ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) ) ) ) );
    rw [ abs_of_nonneg h_nonneg ] ; exact h_lip x y hxy;
  rw [ lipschitzWith_iff_dist_le_mul ];
  intro x y; cases le_total x y <;> simp_all +decide [ dist_eq_norm ] ;
  · simpa only [ abs_sub_comm ] using h_lip x y ‹_› |> le_trans <| by rw [ abs_of_nonpos ] <;> linarith;
  · exact le_trans ( h_lip _ _ ‹_› ) ( by rw [ abs_of_nonneg ] ; linarith )

/-
The defect in the key inequality, `H(x)=F(x-1)+F(x)+F(x+1)-x`, is continuous.
-/
lemma continuous_keyDefect (A : Set ℝ) :
    Continuous (fun x : ℝ => cum A (x - 1) + cum A x + cum A (x + 1) - x) := by
  -- The composition of continuous functions is continuous.
  have h_cont : Continuous (cum A) := by
    exact LipschitzWith.continuous ( lipschitzWith_one_cum A );
  exact Continuous.sub ( Continuous.add ( Continuous.add ( h_cont.comp ( continuous_id.sub continuous_const ) ) ( h_cont.comp continuous_id ) ) ( h_cont.comp ( continuous_id.add continuous_const ) ) ) continuous_id

/-
Consequently, failure of the key inequality persists on a neighbourhood.
-/
lemma keyDefect_pos_neighborhood {x : ℝ}
    (hx : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    ∃ ε > 0, ∀ y ∈ Ioo (x - ε) (x + ε),
      y < cum A (y - 1) + cum A y + cum A (y + 1) := by
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ y, abs (y - x) < ε → cum A (y - 1) + cum A y + cum A (y + 1) - y > 0 := by
    exact Metric.mem_nhds_iff.mp ( continuous_keyDefect A |> Continuous.continuousAt |> fun h => h.eventually ( lt_mem_nhds <| sub_pos.mpr hx ) );
  exact ⟨ ε, hε.1, fun y hy => by linarith [ hε.2 y ( abs_lt.2 ⟨ by linarith [ hy.1 ], by linarith [ hy.2 ] ⟩ ) ] ⟩

/-
Cumulative mass is the interval integral of the indicator of `A`.
-/
lemma cum_eq_intervalIntegral_indicator (hA : MeasurableSet A) {u : ℝ} (hu : 0 ≤ u) :
    cum A u = ∫ v in (0 : ℝ)..u, A.indicator (fun _ => (1 : ℝ)) v := by
  rw [ intervalIntegral.integral_of_le hu, MeasureTheory.integral_indicator hA ];
  simp +decide [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc, cum ];
  rfl

/-
Abstract crossing lemma for a continuous integral primitive.  If a primitive rises from a
nonpositive value to a positive value, then at some positive point its integrand is positive.
-/
lemma exists_integrand_pos_at_primitive_pos {g H : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hH : ∀ y ∈ Icc a b, H y = H a + ∫ v in a..y, g v)
    (hHa : H a ≤ 0) (hHb : 0 < H b) :
    ∃ x ∈ Icc a b, 0 < H x ∧ 0 < g x := by
  contrapose! hHb;
  -- Let $c$ be the last zero of $H$ in $[a, b]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc a b, H c ≤ 0 ∧ ∀ x ∈ Set.Icc a b, c < x → 0 < H x := by
    -- By the properties of the supremum, such a $c$ exists.
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc a b, H c ≤ 0 ∧ ∀ x ∈ Set.Icc a b, H x ≤ 0 → x ≤ c := by
      have h_compact : IsCompact {x ∈ Set.Icc a b | H x ≤ 0} := by
        have h_cont : ContinuousOn H (Set.Icc a b) := by
          refine' ContinuousOn.congr _ fun x hx => hH x hx;
          refine' ContinuousOn.add continuousOn_const _;
          intro x hx;
          refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num;
          simpa [ hab ] using hg;
        exact CompactIccSpace.isCompact_Icc.of_isClosed_subset ( h_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic ) fun x hx => hx.1;
      obtain ⟨ c, hc ⟩ := h_compact.exists_isGreatest ( ⟨ a, ⟨ le_rfl, hab ⟩, hHa ⟩ );
      exact ⟨ c, hc.1.1, hc.1.2, fun x hx hx' => hc.2 ⟨ hx, hx' ⟩ ⟩;
    exact ⟨ c, hc.1, hc.2.1, fun x hx hx' => not_le.1 fun hx'' => hx'.not_ge <| hc.2.2 x hx hx'' ⟩;
  -- Since $g(x) \leq 0$ for all $x \in (c, b]$, we have $\int_c^b g(v) \, dv \leq 0$.
  have h_int_neg : ∫ v in c..b, g v ≤ 0 := by
    rw [ intervalIntegral.integral_of_le hc.1.2 ];
    exact MeasureTheory.setIntegral_nonpos measurableSet_Ioc fun x hx => hHb x ⟨ by linarith [ hx.1, hc.1.1 ], by linarith [ hx.2, hc.1.2 ] ⟩ ( hc.2.2 x ⟨ by linarith [ hx.1, hc.1.1 ], by linarith [ hx.2, hc.1.2 ] ⟩ hx.1 );
  have h_int_split : ∫ v in a..b, g v = (∫ v in a..c, g v) + (∫ v in c..b, g v) := by
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ hg.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hc.1.1, hc.1.2 ];
  linarith [ hH c hc.1, hH b ⟨ by linarith [ hc.1.1 ], by linarith [ hc.1.2 ] ⟩ ]

/-
Positive-triple reduction: a failure of the key inequality for a finite interval union
can be moved to a failure point whose two outer translates belong to the set.
-/
theorem positive_triple_reduction {ivs : List (ℝ × ℝ)}
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {z : ℝ} (hz : 1 ≤ z)
    (hfail : z < cum A (z - 1) + cum A z + cum A (z + 1)) :
    ∃ x : ℝ, 1 ≤ x ∧ x - 1 ∈ A ∧ x + 1 ∈ A ∧
      x < cum A (x - 1) + cum A x + cum A (x + 1) := by
  -- By the properties of the cumulative function and the definition of $H$, we know that $H$ is the integral primitive of $g$.
  have h_integral_primitive : ∀ y ∈ Set.Icc 1 z, cum A (y - 1) + cum A y + cum A (y + 1) - y = (cum A 0 + cum A 1 + cum A 2) - 1 + ∫ v in (1 : ℝ)..y, (A.indicator (fun _ => (1 : ℝ)) (v - 1)) + (A.indicator (fun _ => (1 : ℝ)) v) + (A.indicator (fun _ => (1 : ℝ)) (v + 1)) - 1 := by
    intro y hy
    have h_integral_primitive_step : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ y + 1 → cum A b - cum A a = ∫ v in a..b, A.indicator (fun _ => (1 : ℝ)) v := by
      intros a b ha hb hb_le_y1
      have h_integral_primitive_step : cum A b - cum A a = ∫ v in a..b, A.indicator (fun _ => (1 : ℝ)) v := by
        have hA_meas : MeasurableSet A := by
          exact hIU.isClosed.measurableSet
        rw [ cum_eq_intervalIntegral_indicator hA_meas ( by linarith ), cum_eq_intervalIntegral_indicator hA_meas ( by linarith ) ];
        rw [ sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
        · refine' MeasureTheory.Integrable.indicator _ _;
          · exact Continuous.integrableOn_Icc ( by continuity );
          · exact hA_meas;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · exact Continuous.integrableOn_Icc ( by continuity );
          · exact hA_meas;
      exact h_integral_primitive_step;
    rw [ intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_add ] <;> norm_num;
    grind;
    · rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le hy.1 ];
      refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num;
      · have h_measurable : MeasurableSet A := by
          exact hIU.isClosed.measurableSet;
        exact h_measurable.preimage ( measurable_id.sub measurable_const );
    · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
      refine' MeasureTheory.Integrable.indicator _ _;
      · exact Continuous.integrableOn_Icc ( by continuity );
      · exact hIU.isClosed.measurableSet;
    · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
      refine' MeasureTheory.Integrable.add _ _;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · exact Continuous.integrableOn_Icc ( by continuity );
        · exact hIU.isClosed.measurableSet.preimage ( measurable_id.sub measurable_const );
      · refine' MeasureTheory.Integrable.indicator _ _;
        · exact Continuous.integrableOn_Icc ( by continuity );
        · exact hIU.isClosed.measurableSet;
    · rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le hy.1 ];
      refine' MeasureTheory.Integrable.indicator _ _;
      · norm_num;
      · have h_measurable : MeasurableSet A := by
          exact hIU.isClosed.measurableSet;
        exact h_measurable.preimage ( measurable_id.add_const _ );
    · apply_rules [ MeasureTheory.IntegrableOn.intervalIntegrable ];
      refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · exact Continuous.integrableOn_Icc ( by continuity );
        · exact hIU.isClosed.measurableSet.preimage ( measurable_id.sub measurable_const );
      · refine' MeasureTheory.Integrable.indicator _ _;
        · exact Continuous.integrableOn_Icc ( by continuity );
        · exact hIU.isClosed.measurableSet;
      · refine' MeasureTheory.Integrable.indicator _ _;
        · exact Continuous.integrableOn_Icc ( by continuity );
        · have h_measurable : MeasurableSet A := by
            exact hIU.isClosed.measurableSet;
          exact h_measurable.preimage ( measurable_id.add_const _ );
  obtain ⟨x, hx⟩ : ∃ x ∈ Set.Icc 1 z, 0 < cum A (x - 1) + cum A x + cum A (x + 1) - x ∧ 0 < (A.indicator (fun _ => (1 : ℝ)) (x - 1)) + (A.indicator (fun _ => (1 : ℝ)) x) + (A.indicator (fun _ => (1 : ℝ)) (x + 1)) - 1 := by
    apply exists_integrand_pos_at_primitive_pos (by linarith);
    · rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le hz ];
      refine' MeasureTheory.Integrable.sub _ _;
      · refine' MeasureTheory.Integrable.add ( MeasureTheory.Integrable.add _ _ ) _;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num;
          · exact hIU.isClosed.measurableSet.preimage ( measurable_id.sub measurable_const );
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num;
          · exact hIU.isClosed.measurableSet;
        · refine' MeasureTheory.Integrable.indicator _ _;
          · norm_num;
          · have h_measurable : MeasurableSet A := by
              exact hIU.isClosed.measurableSet;
            exact h_measurable.preimage ( measurable_id.add_const _ );
      · norm_num;
    · grind +qlia;
    · have h_cum_zero : cum A 0 = 0 := by
        unfold cum;
        rw [ show A ∩ Icc 0 0 = ∅ by rw [ Set.eq_empty_iff_forall_notMem ] ; rintro x ⟨ hx₁, hx₂ ⟩ ; linarith [ hmin.2 hx₁, hx₂.1, hx₂.2 ] ] ; norm_num
      have h_cum_one : cum A 1 = 0 := by
        have h_cum_one : A ∩ Set.Icc 0 1 = {1} := by
          exact Set.eq_singleton_iff_unique_mem.mpr ⟨ ⟨ hmin.1, by norm_num ⟩, fun x hx => le_antisymm ( hx.2.2 ) ( hmin.2 hx.1 ) ⟩;
        unfold cum; aesop;
      have h_cum_two : cum A 2 ≤ 1 := by
        convert sumFree_mass_Icc_le_one hIU.isClosed.measurableSet hsf hmin.1 ( by norm_num : ( 2 : ℝ ) - 0 ≤ 2 ) using 1
      simp [h_cum_zero, h_cum_one, h_cum_two];
      exact_mod_cast h_cum_two;
    · linarith;
  by_cases h1 : x - 1 ∈ A <;> by_cases h2 : x ∈ A <;> by_cases h3 : x + 1 ∈ A <;> simp_all +decide [ Set.indicator ];
  · exact ⟨ x, hx.1.1, h1, h3, hx.2 ⟩;
  · exact False.elim <| hsf h1 hmin.1 <| by convert h2 using 1; ring;
  · exact ⟨ x, hx.1.1, h1, h3, hx.2 ⟩;
  · exact False.elim <| hsf h2 hmin.1 <| by ring_nf at *; aesop;
  · linarith

end ProductFree