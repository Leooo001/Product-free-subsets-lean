import RequestProject.Analytic
import RequestProject.Section4Assembly
import RequestProject.Section4YThreeEmpty
import RequestProject.Section4AGtTwoAssembly
import RequestProject.Section4PostAGtTwoAssembly
import RequestProject.Section4PostAMassAssembly
import RequestProject.Section4GapAroundXAssembly
import RequestProject.Section4SecondGapAssembly
import RequestProject.Section4Final
import RequestProject.Section4FinalAssembly
import RequestProject.IntervalCover

/-!
# The key lemma and the sum-free integral bound

`ProductFree.key_lemma` is the central combinatorial result of the paper (Lemma "key lemma",
Section 4). The paper states it for a sum-free finite union of closed intervals with least
element `1`, in the form `F(x-1) + F(x) + F(x+1) ≤ x` for `x ≥ 1`. The paper notes that "after
a simple rescaling" it holds with least element `δ`, giving `F(x-δ) + F(x) + F(x+δ) ≤ x`.
We state that rescaled form directly.

The finite-interval-union proof is developed in the `Section4*` modules.  The remaining
assembly theorem below connects the selected maximizing interval to those geometric estimates.

Combining `key_lemma` with the elementary boundary estimate and the analytic reduction
`integral_cum_lt_third`, we obtain `ProductFree.sumfree_integral_lt_third`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
For `A ⊆ [δ,∞)` and `δ ≤ y`, `F(y) = |A ∩ [0,y]| = |A ∩ [δ,y]| ≤ y - δ`.
-/
lemma cum_le_sub_delta {δ y : ℝ} (hAδ : A ⊆ Ici δ) (hy : δ ≤ y) : cum A y ≤ y - δ := by
  exact le_trans ( ENNReal.toReal_mono ( by aesop ) <| MeasureTheory.measure_mono <| show A ∩ Icc 0 y ⊆ Icc δ y from fun x hx => ⟨ hAδ hx.1, hx.2.2 ⟩ ) ( by rw [ Real.volume_Icc ] ; aesop )

/-
Initial discrepancy-maximizing interval for the Section 4 contradiction.
-/
lemma section4_initial_setup (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    (hmin : IsLeast A 1) {x : ℝ} (hx : 1 ≤ x)
    (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1)) :
    ∃ a b : ℝ, a < b ∧ b ≤ x + 1 ∧ a ∈ A ∧ b ∈ A ∧
      IsBalanced A a b ∧ disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b ∧
      0 < discOn A a b := by
  -- By dis attains, obtain p q balanced and discOn B p q = disc B.
  obtain ⟨p, q, hpq, hB⟩ : ∃ p q : ℝ, p < q ∧ q ≤ x + 1 ∧ IsBalanced (A ∩ Icc 0 (x + 1)) p q ∧ disc (A ∩ Icc 0 (x + 1)) ≤ discOn A p q ∧ 0 < discOn A p q := by
    have := @ProductFree.disc_attained ( A ∩ Icc 0 ( x + 1 ) ) ?_ ?_ ?_;
    rotate_left;
    exact ( hIU.inter_Icc_exists 0 ( x + 1 ) ).choose;
    · exact Exists.choose_spec ( hIU.inter_Icc_exists 0 ( x + 1 ) );
    · intro h; have := Exists.choose_spec ( hIU.inter_Icc_exists 0 ( x + 1 ) ) ; simp_all +decide [ IsIntervalUnion ] ;
      exact absurd this ( Set.Nonempty.ne_empty ⟨ x + 1, hxright, by norm_num; linarith ⟩ );
    · obtain ⟨ p, q, hp, hq, hq', h, h' ⟩ := this; use p, q; simp_all +decide [ IsBalanced, discOn ] ;
      refine' ⟨ lt_of_le_of_ne hq _, _, _, _ ⟩;
      · rintro rfl; simp_all +decide [ IsLeftBalanced, IsRightBalanced ] ;
        have h_disc_pos : 0 < disc (A ∩ Icc 0 (x + 1)) := by
          apply iu_disc_pos;
          exact hIU.inter_Icc_exists 0 ( x + 1 ) |> Classical.choose_spec;
          contrapose! hfail;
          have h_cum_zero : ∀ y : ℝ, 0 ≤ y → y ≤ x + 1 → cum A y = 0 := by
            intros y hy_nonneg hy_le
            have h_cum_zero : cum A y ≤ cum A (x + 1) := by
              apply_rules [ ProductFree.cum_mono ];
            exact le_antisymm ( h_cum_zero.trans ( by simpa [ cum ] using hfail ) ) ( cum_nonneg A y );
          rw [ h_cum_zero ( x - 1 ) ( by linarith ) ( by linarith ), h_cum_zero x ( by linarith ) ( by linarith ), h_cum_zero ( x + 1 ) ( by linarith ) ( by linarith ) ] ; linarith;
        rw [ ← h' ] at h_disc_pos;
        exact h_disc_pos.ne' ( by rw [ MeasureTheory.measure_mono_null ( show A ∩ Icc 0 ( x + 1 ) ∩ { p } ⊆ { p } by aesop_cat ) ( MeasureTheory.measure_singleton p ) ] ; norm_num );
      · exact hq'.trans ( csSup_le ⟨ x + 1, hxright, by norm_num; linarith ⟩ fun y hy => hy.2.2 );
      · rw [ ← h' ];
        gcongr;
        · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
          exact A ∩ Icc 0 ( x + 1 );
          · intro y hy; exact ⟨ hy.1, ⟨ by linarith [ hy.2.1, show 0 ≤ p by exact le_trans ( by exact le_csInf ⟨ x - 1, hxleft, by constructor <;> linarith ⟩ fun z hz => hz.2.1 ) hp ], by linarith [ hy.2.2, show q ≤ x + 1 by exact hq'.trans ( csSup_le ⟨ x + 1, hxright, by constructor <;> linarith ⟩ fun z hz => hz.2.2 ) ] ⟩ ⟩ ;
          · exact lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc 0 ( x + 1 ) ⊆ Icc 0 ( x + 1 ) from fun y hy => hy.2 ) ) ( by simp +decide [ Real.volume_Icc ] );
        · exact Set.inter_subset_left;
      · have := @ProductFree.iu_disc_pos ( A ∩ Icc 0 ( x + 1 ) ) ?_ ?_ ?_;
        any_goals exact ( hIU.inter_Icc_exists 0 ( x + 1 ) ).choose;
        · rw [ show A ∩ Icc 0 ( x + 1 ) ∩ Icc p q = A ∩ Icc p q from ?_ ] at h';
          · linarith;
          · ext; simp [Set.mem_inter_iff, Set.mem_Icc];
            exact fun _ _ _ => ⟨ by linarith [ hmin.2 ‹_› ], by linarith [ hmin.2 ‹_›, show q ≤ x + 1 from hq'.trans ( csSup_le ⟨ _, hxright, by constructor <;> linarith ⟩ fun y hy => hy.2.2 ) ] ⟩;
        · exact Exists.choose_spec ( hIU.inter_Icc_exists 0 ( x + 1 ) );
        · refine' ENNReal.toReal_pos _ _;
          · intro H; simp_all +decide [ cum ] ;
            contrapose! hfail;
            rw [ MeasureTheory.measure_mono_null ( show A ∩ Icc 0 ( x - 1 ) ⊆ A ∩ Icc 0 ( x + 1 ) from fun y hy => ⟨ hy.1, ⟨ hy.2.1, by linarith [ hy.2.2 ] ⟩ ⟩ ) H, MeasureTheory.measure_mono_null ( show A ∩ Icc 0 x ⊆ A ∩ Icc 0 ( x + 1 ) from fun y hy => ⟨ hy.1, ⟨ hy.2.1, by linarith [ hy.2.2 ] ⟩ ⟩ ) H ] ; norm_num ; linarith;
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc 0 ( x + 1 ) ⊆ Icc 0 ( x + 1 ) from fun y hy => hy.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) );
  -- Since $p$ and $q$ are balanced for $B$, they are also balanced for $A$.
  have hpq_balanced : IsBalanced A p q := by
    obtain ⟨hp_left, hp_right⟩ := hB.right.left.left
    obtain ⟨hq_left, hq_right⟩ := hB.right.left.right
    generalize_proofs at *; (
    refine' ⟨ ⟨ _, _ ⟩, ⟨ _, _ ⟩ ⟩ <;> contrapose! hp_right <;> contrapose! hq_right <;> norm_num [ discOn ] at *;
    · linarith;
    · obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := hp_right; use c; simp_all +decide [ Set.inter_assoc, Set.inter_comm, Set.inter_left_comm ] ;
      have h_volume_eq : volume (A ∩ (Icc p c ∩ Icc 0 (x + 1))) = volume (A ∩ Icc p c) := by
        congr 1 with y ; simp +decide [ Set.mem_inter_iff, Set.mem_Icc ] ; ring;
        exact fun _ _ _ => ⟨ by linarith [ hmin.2 ‹_› ], by linarith [ hmin.2 ‹_› ] ⟩
      generalize_proofs at *; (
      grind);
    · linarith;
    · obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := hp_right; use c; simp_all +decide [ Set.inter_assoc ] ;
      refine' lt_of_le_of_lt _ hc₃;
      gcongr;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc c q ⊆ Icc c q from fun x hx => hx.2 ) ) ( by simp +decide [ Real.volume_Icc ] ) );
      · exact Set.inter_subset_right);
  have hpq_in_A : p ∈ A ∧ q ∈ A := by
    have hpq_in_A : ∀ {p q : ℝ}, p < q → IsBalanced (A ∩ Icc 0 (x + 1)) p q → p ∈ A ∧ q ∈ A := by
      intros p q hpq hB_balanced
      have hpq_in_A : p ∈ A ∧ q ∈ A := by
        have h_closed : IsClosed (A ∩ Icc 0 (x + 1)) := by
          exact IsClosed.inter ( hIU.isClosed ) ( isClosed_Icc )
        have := left_balanced_left_mem h_closed hB_balanced.left; have := right_balanced_right_mem h_closed hB_balanced.right; aesop;
      exact hpq_in_A;
    exact hpq_in_A hpq hB.2.1;
  exact ⟨ p, q, hpq, hB.1, hpq_in_A.1, hpq_in_A.2, hpq_balanced, hB.2.2.1, hB.2.2.2 ⟩

/-
A finite exceptional set may be avoided in the primitive-crossing argument.
-/
lemma exists_integrand_pos_at_primitive_pos_avoiding_finset
    {g H : ℝ → ℝ} {a b : ℝ} (S : Finset ℝ)
    (hab : a ≤ b) (hg : IntervalIntegrable g volume a b)
    (hH : ∀ y ∈ Icc a b, H y = H a + ∫ v in a..y, g v)
    (hHa : H a ≤ 0) (hHb : 0 < H b) :
    ∃ x ∈ Icc a b, 0 < H x ∧ 0 < g x ∧ x ∉ S := by
  -- By contradiction, assume that for all $x \in [a, b]$, if $H(x) > 0$, then $g(x) \leq 0$ or $x \in S$.
  by_contra h_contra
  push_neg at h_contra
  have h_zero : ∀ x ∈ Set.Icc a b, H x > 0 → g x ≤ 0 ∨ x ∈ S := by
    exact fun x hx hx' => Classical.or_iff_not_imp_left.2 fun hx'' => h_contra x hx hx' <| lt_of_not_ge hx'';
  -- Choose the last zero $c$ of $H$ in $[a, b]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc a b, H c ≤ 0 ∧ ∀ y ∈ Set.Icc a b, y > c → H y > 0 := by
    have h_compact : IsCompact {x ∈ Set.Icc a b | H x ≤ 0} := by
      have h_cont : ContinuousOn H (Set.Icc a b) := by
        refine' ContinuousOn.congr _ fun x hx => hH x hx;
        refine' ContinuousOn.add continuousOn_const _;
        intro x hx;
        refine' intervalIntegral.continuousWithinAt_primitive _ _ <;> norm_num [ hg ];
        simpa [ hab ] using hg;
      exact CompactIccSpace.isCompact_Icc.of_isClosed_subset ( h_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic ) fun x hx => hx.1;
    obtain ⟨c, hc⟩ : ∃ c ∈ {x ∈ Set.Icc a b | H x ≤ 0}, ∀ y ∈ {x ∈ Set.Icc a b | H x ≤ 0}, y ≤ c := by
      exact h_compact.exists_isGreatest ⟨ a, ⟨ by linarith, by linarith ⟩, hHa ⟩;
    exact ⟨ c, hc.1.1, hc.1.2, fun y hy hy' => not_le.1 fun hy'' => hy'.not_ge <| hc.2 y ⟨ hy, hy'' ⟩ ⟩;
  -- On $(c, b]$, $H > 0$, so $g \leq 0$ almost everywhere.
  have h_g_nonpos_ae : ∀ᵐ x ∂MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc c b), g x ≤ 0 := by
    rw [ MeasureTheory.ae_restrict_iff' ] <;> norm_num [ hc.1.1, hc.1.2 ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( S.countable_toSet.measure_zero MeasureTheory.MeasureSpace.volume ) ] with x hx using fun hx₁ hx₂ => Or.resolve_right ( h_zero x ⟨ by linarith [ hc.1.1 ], by linarith [ hc.1.2 ] ⟩ ( hc.2.2 x ⟨ by linarith [ hc.1.1 ], by linarith [ hc.1.2 ] ⟩ hx₁ ) ) hx;
  -- Since $g \leq 0$ almost everywhere on $(c, b]$, we have $\int_c^b g(v) \, dv \leq 0$.
  have h_integral_nonpos : ∫ v in Set.Ioc c b, g v ≤ 0 := by
    exact MeasureTheory.integral_nonpos_of_ae h_g_nonpos_ae;
  -- By the fundamental theorem of calculus, we have $H(b) - H(c) = \int_c^b g(v) \, dv$.
  have h_ftc : H b - H c = ∫ v in Set.Ioc c b, g v := by
    rw [ ← intervalIntegral.integral_of_le ( by linarith [ hc.1.2 ] ), hH b ( by constructor <;> linarith [ hc.1.1, hc.1.2 ] ), hH c ( by constructor <;> linarith [ hc.1.1, hc.1.2 ] ) ] ; ring;
    rw [ sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ hg.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hc.1.1, hc.1.2 ];
  grind

/-
A point of a finite interval union which is not a component endpoint has a
closed neighborhood contained in the union.
-/
lemma intervalUnion_neighborhood_of_not_endpoint
    (hIU : IsIntervalUnion A ivs) {p : ℝ}
    (hp : p ∈ A)
    (hleft : ∀ q ∈ ivs, p ≠ q.1)
    (hright : ∀ q ∈ ivs, p ≠ q.2) :
    ∃ ε > 0, Icc (p - ε) (p + ε) ⊆ A := by
  obtain ⟨q, hq⟩ : ∃ q ∈ ivs, p ∈ Set.Icc q.1 q.2 := by
    have := hIU.2.2 ▸ hp; simp_all +decide [ Set.ext_iff ] ;
    tauto;
  -- Choose ε = min (p - q.1) (q.2 - p) / 2. It is positive.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε ≤ min (p - q.1) (q.2 - p) := by
    exact ⟨ Min.min ( p - q.1 ) ( q.2 - p ), lt_min ( sub_pos.mpr ( lt_of_le_of_ne hq.2.1 ( Ne.symm ( hleft q hq.1 ) ) ) ) ( sub_pos.mpr ( lt_of_le_of_ne hq.2.2 ( hright q hq.1 ) ) ), le_rfl ⟩;
  refine' ⟨ ε, hε_pos, fun x hx => _ ⟩;
  exact hIU.2.2.symm.subset <| Set.mem_iUnion₂.mpr ⟨ q, hq.1, by constructor <;> linarith [ hx.1, hx.2, hq.2.1, hq.2.2, min_le_left ( p - q.1 ) ( q.2 - p ), min_le_right ( p - q.1 ) ( q.2 - p ) ] ⟩

/-- Strengthened positive-triple reduction: the left outer point can be chosen in the
interior of the finite interval union.  This is the neighborhood form required by the
geometric small-case argument. -/
lemma positive_triple_reduction_with_left_neighborhood
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {z : ℝ} (hz : 1 ≤ z)
    (hfail : z < cum A (z - 1) + cum A z + cum A (z + 1)) :
    ∃ x ε : ℝ, 1 ≤ x ∧ x - 1 ∈ A ∧ x + 1 ∈ A ∧
      x < cum A (x - 1) + cum A x + cum A (x + 1) ∧
      0 < ε ∧ Icc (x - 1 - ε) (x - 1 + ε) ⊆ A := by
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
  let S : Finset ℝ :=
    ivs.toFinset.image (fun q => q.1 + 1) ∪ ivs.toFinset.image (fun q => q.2 + 1)
  obtain ⟨x, hxIcc, hdef, hind, hxavoid⟩ : ∃ x ∈ Set.Icc 1 z,
      0 < cum A (x - 1) + cum A x + cum A (x + 1) - x ∧
      0 < (A.indicator (fun _ => (1 : ℝ)) (x - 1)) +
        (A.indicator (fun _ => (1 : ℝ)) x) +
        (A.indicator (fun _ => (1 : ℝ)) (x + 1)) - 1 ∧ x ∉ S := by
    apply exists_integrand_pos_at_primitive_pos_avoiding_finset S (by linarith);
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
  have hneigh (h1 : x - 1 ∈ A) : ∃ ε > 0, Icc (x - 1 - ε) (x - 1 + ε) ⊆ A := by
    apply intervalUnion_neighborhood_of_not_endpoint hIU h1
    · intro q hq heq
      apply hxavoid
      simp only [S, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
      left
      exact ⟨q, hq, by linarith⟩
    · intro q hq heq
      apply hxavoid
      simp only [S, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
      right
      exact ⟨q, hq, by linarith⟩
  have houter : x - 1 ∈ A ∧ x + 1 ∈ A := by
    by_cases h1 : x - 1 ∈ A <;> by_cases h2 : x ∈ A <;>
        by_cases h3 : x + 1 ∈ A <;> simp_all +decide [Set.indicator]
    · exact False.elim <| hsf h1 hmin.1 <| by convert h2 using 1; ring
    · exact False.elim <| hsf h2 hmin.1 <| by ring_nf at *; aesop
    · linarith
  obtain ⟨ε, hε, hsub⟩ := hneigh houter.1
  exact ⟨x, ε, hxIcc.1, houter.1, houter.2, by linarith, hε, hsub⟩
/-- The normalized (`min A = 1`) form of the key lemma. -/
theorem key_lemma_intervalUnion_one (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    (hmin : IsLeast A 1) :
    ∀ x : ℝ, 1 ≤ x → cum A (x - 1) + cum A x + cum A (x + 1) ≤ x := by
  intro z hz
  by_contra hnot
  have hzfail : z < cum A (z - 1) + cum A z + cum A (z + 1) := lt_of_not_ge hnot
  obtain ⟨x, ε, hx, hxleft, hxright, hfail, hε, hneigh⟩ :=
    positive_triple_reduction_with_left_neighborhood hIU hsf hmin hz hzfail
  obtain ⟨a, b, hab, hbtop, haA, hbA, hbal, hmax, htpos⟩ :=
    section4_initial_setup hIU hsf hmin hx hxleft hxright hfail
  exact section4_contradiction_from_initial_setup hIU hsf hmin hx hxleft hxright hfail
    hab hbtop haA hbA hbal hmax htpos hε hneigh

/-
**The key lemma for finite unions of closed intervals** (Lemma "key lemma" of the
paper, in rescaled form).
-/
theorem key_lemma_intervalUnion (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {δ : ℝ} (hδ : 0 < δ) (hmin : IsLeast A δ) :
    ∀ x : ℝ, δ ≤ x → cum A (x - δ) + cum A x + cum A (x + δ) ≤ x := by
  intro x hx;
  -- Let $B = \{ u \mid \delta u \in A \}$. Because $\delta > 0$, $B$ is the finite interval union obtained by dividing every endpoint in $ivs$ by $\delta$; $B$ is sum-free and has least element $1$.
  set B := {u | δ * u ∈ A} with hB_def
  have hB_intervalUnion : IsIntervalUnion B (List.map (fun (a, b) => (a / δ, b / δ)) ivs) := by
    constructor;
    · intro p hp; obtain ⟨ q, hq, rfl ⟩ := List.mem_map.mp hp; exact div_le_div_of_nonneg_right ( hIU.1 q hq ) hδ.le;
    · convert hIU.2 using 1;
      · simp +decide [ List.isChain_iff_getElem, div_lt_div_iff_of_pos_right hδ ];
      · constructor <;> intro h <;> simp_all +decide [ Set.ext_iff ];
        · convert hIU.1 using 1;
          constructor <;> intro h <;> simp_all +decide [ IsIntervalUnion ];
        · exact fun x => ⟨ fun ⟨ a, ha, b, hb, hab ⟩ => ⟨ a, by rw [ div_le_iff₀ hδ ] ; linarith, b, hb, by rw [ le_div_iff₀ hδ ] ; linarith ⟩, fun ⟨ a, ha, b, hb, hab ⟩ => ⟨ a, by rw [ div_le_iff₀ hδ ] at ha; linarith, b, hb, by rw [ le_div_iff₀ hδ ] at hab; linarith ⟩ ⟩
  have hB_sumFree : IsSumFree B := by
    intro u hu v hv; have := hsf hu hv; simp_all +decide [ mul_add, add_mul, mul_assoc, mul_comm δ ] ;
  have hB_least : IsLeast B 1 := by
    simp_all +decide [ IsLeast, mem_lowerBounds ];
    exact fun x hx => by nlinarith [ hmin.2 _ hx ] ;
  -- Prove that cum B (r/δ) = cum A r / δ using Lebesgue measure scaling.
  have h_cum_B : ∀ r : ℝ, 0 ≤ r → cum B (r / δ) = cum A r / δ := by
    intro r hr
    have h_volume : volume (B ∩ Icc 0 (r / δ)) = volume (A ∩ Icc 0 r) / ENNReal.ofReal δ := by
      convert Real.volume_preimage_mul_left ( show δ ≠ 0 by linarith ) ( A ∩ Icc 0 r ) using 1;
      · congr with x ; simp +decide [ mul_div_cancel₀ _ hδ.ne', hδ.le ];
        exact ⟨ fun hx => ⟨ by nlinarith [ mul_div_cancel₀ r hδ.ne' ], by nlinarith [ mul_div_cancel₀ r hδ.ne' ] ⟩, fun hx => ⟨ by nlinarith [ hx.1, hx.2, mul_div_cancel₀ r hδ.ne' ], by nlinarith [ hx.1, hx.2, mul_div_cancel₀ r hδ.ne' ] ⟩ ⟩;
      · rw [ abs_of_nonneg ( by positivity ), ENNReal.ofReal_inv_of_pos hδ, ENNReal.div_eq_inv_mul ];
    convert congr_arg ENNReal.toReal h_volume using 1;
    rw [ ENNReal.toReal_div, ENNReal.toReal_ofReal hδ.le ] ; rfl;
  -- Apply key_lemma_intervalUnion_one to B at x/δ.
  have h_key_B : cum B (x / δ - 1) + cum B (x / δ) + cum B (x / δ + 1) ≤ x / δ := by
    have := key_lemma_intervalUnion_one hB_intervalUnion hB_sumFree hB_least ( x / δ ) ( by rw [ le_div_iff₀ hδ ] ; linarith ) ; aesop;
  have := h_cum_B ( x - δ ) ( by linarith ) ; have := h_cum_B x ( by linarith ) ; have := h_cum_B ( x + δ ) ( by linarith ) ; simp_all +decide [ sub_div, add_div, hδ.ne' ] ;
  rw [ ← add_div, ← add_div, div_le_div_iff_of_pos_right ] at h_key_B <;> linarith

/-
The finite-interval-union key inequality extended to all nonnegative `x`.
-/
theorem key_ineq_intervalUnion_nonneg (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {δ : ℝ} (hδ : 0 < δ) (hmin : IsLeast A δ) :
    ∀ x : ℝ, 0 ≤ x → cum A (x - δ) + cum A x + cum A (x + δ) ≤ x := by
  intro x hx; by_cases hx' : x ≥ δ <;> simp_all +decide [ key_lemma_intervalUnion ] ;
  · exact key_lemma_intervalUnion hIU hsf hδ hmin x hx';
  · -- Since $x < \delta$, we have $cum A (x - \delta) = 0$ and $cum A x = 0$.
    have h_cum_zero : cum A (x - δ) = 0 ∧ cum A x = 0 := by
      constructor <;> rw [ cum_eq_zero_of_le ];
      exacts [ fun y hy => hmin.2 hy, by linarith, fun y hy => hmin.2 hy, by linarith ];
    have := cum_le_sub_delta ( show A ⊆ Ici δ from fun y hy => hmin.2 hy ) ( show δ ≤ x + δ by linarith ) ; aesop;

/-
The finite-interval-union form of the sum-free integral bound.
-/
theorem sumfree_integral_intervalUnion_lt_third
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) {δ : ℝ}
    (hδ : 0 < δ) (hmin : IsLeast A δ) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-u) * cum A u) < 1 / 3 := by
  convert integral_cum_lt_third hδ ( hmin.1 |> fun h => ?_ ) ( key_ineq_intervalUnion_nonneg hIU hsf hδ hmin ) using 1;
  exact fun x hx => hmin.2 hx

/-- Monotonicity of the cumulative mass in the set: if `A ⊆ B` then `cum A x ≤ cum B x`. -/
lemma cum_le_of_subset {A B : Set ℝ} (hAB : A ⊆ B) (x : ℝ) : cum A x ≤ cum B x := by
  refine ENNReal.toReal_mono ?_ (measure_mono (Set.inter_subset_inter_left _ hAB))
  exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_right)

/-- A subset of a sum-free set is sum-free. -/
lemma IsSumFree.subset {A B : Set ℝ} (hsf : IsSumFree B) (hAB : A ⊆ B) : IsSumFree A :=
  fun _ hx _ hy hxy => hsf (hAB hx) (hAB hy) (hAB hxy)

/-- **Sum-free thickening.** For a compact sum-free set `K`, a small closed thickening
`K + [-η, η]` is still sum-free.  Since `K + K` is compact and disjoint from `K`, it lies at a
positive distance `R` from `K`; any `η` with `3η < R` works, because a sum of two points of the
thickening lands within `3η` of a genuine sum in `K + K`. -/
lemma exists_sumFree_thickening {K : Set ℝ} (hKc : IsCompact K)
    (hsf : IsSumFree K) :
    ∃ η : ℝ, 0 < η ∧ IsSumFree (K + Icc (-η) η) := by
  have hP : IsCompact (K + K) := hKc.add hKc
  have hdisj : Disjoint (K + K) K := by
    rw [Set.disjoint_left]; rintro z ⟨x, hx, y, hy, rfl⟩ hz; exact hsf hx hy hz
  obtain ⟨r, hr, hbd0⟩ := Metric.exists_pos_forall_lt_edist hP hKc.isClosed hdisj
  set R : ℝ := (r : ℝ) with hR
  have hR0 : 0 < R := by rw [hR]; exact_mod_cast hr
  have hbd : ∀ p ∈ K + K, ∀ k ∈ K, R < dist p k := by
    intro p hp k hk
    have h := hbd0 p hp k hk
    rw [edist_nndist, ENNReal.coe_lt_coe] at h
    have h2 : (r : ℝ) < (nndist p k : ℝ) := by exact_mod_cast h
    rwa [coe_nndist] at h2
  refine ⟨R / 4, by positivity, ?_⟩
  intro u hu v hv huv
  rw [Set.mem_add] at hu hv huv
  obtain ⟨k1, hk1, s, hs, rfl⟩ := hu
  obtain ⟨k2, hk2, t, ht, rfl⟩ := hv
  obtain ⟨k3, hk3, w, hw, hw3⟩ := huv
  have hkk : k1 + k2 ∈ K + K := Set.add_mem_add hk1 hk2
  have hsep := hbd (k1 + k2) hkk k3 hk3
  rw [Real.dist_eq] at hsep
  simp only [mem_Icc] at hs ht hw
  have hfin : |k1 + k2 - k3| ≤ 3 * (R / 4) := by
    have heq : k1 + k2 - k3 = w - (s + t) := by linarith [hw3]
    rw [heq, abs_le]
    constructor <;> linarith [hw.1, hw.2, hs.1, hs.2, ht.1, ht.2]
  linarith [hsep, hfin, hR0]

/-- Per-thickening estimate powering `key_lemma_compact`.

Given a thickening radius `η ∈ (0, δ)` such that `K + [-η, η]` is sum-free, cover the compact
set `K` by a finite interval union `F` with `K ⊆ F ⊆ K + [-η, η]` (`exists_intervalUnion_cover`).
Then `F` is sum-free (subset of the sum-free thickening) and nonempty; let `δ_F` be its least
element, so `δ - η ≤ δ_F ≤ δ` and `0 < δ_F`.  The finite-union key lemma
(`key_lemma_intervalUnion`) applied to `F` gives
`cum F (x-δ_F) + cum F x + cum F (x+δ_F) ≤ x`.  Bounding `cum K ≤ cum F` (`cum_le_of_subset`) and
comparing the arguments (`cum_mono`, `cum_le_cum_add_sub`, using `δ - δ_F ≤ η`) yields the claim. -/
lemma key_lemma_compact_aux {K : Set ℝ} (hKc : IsCompact K) {δ : ℝ}
    (hmin : IsLeast K δ) {η : ℝ} (hη : 0 < η) (hηδ : η < δ)
    (hsfη : IsSumFree (K + Icc (-η) η)) :
    ∀ x : ℝ, δ ≤ x → cum K (x - δ) + cum K x + cum K (x + δ) ≤ x + η := by
  intro x hx
  obtain ⟨F, ivs, hIU, hKF, hFsub⟩ := exists_intervalUnion_cover hKc hη
  have hFsf : IsSumFree F := hsfη.subset hFsub
  have hKne : K.Nonempty := ⟨δ, hmin.1⟩
  have hFne : F.Nonempty := hKne.mono hKF
  have hivsne : ivs ≠ [] := by
    rintro rfl
    obtain ⟨z, hz⟩ := hFne
    rw [hIU.2.2] at hz
    simp at hz
  have hFc : IsCompact F := hIU.isCompact
  obtain ⟨δF, hδF⟩ := hFc.exists_isLeast hFne
  have hδδ : δF ≤ δ := hδF.2 (hKF hmin.1)
  have hδFge : δ - η ≤ δF := by
    have hmem : δF ∈ K + Icc (-η) η := hFsub hδF.1
    rw [Set.mem_add] at hmem
    obtain ⟨k, hk, w, hw, hkw⟩ := hmem
    simp only [mem_Icc] at hw
    have hkge : δ ≤ k := hmin.2 hk
    linarith [hkw]
  have hδFpos : 0 < δF := by linarith
  have hKL := key_lemma_intervalUnion hIU hFsf hδFpos hδF x (le_trans hδδ hx)
  have h1 : cum K (x - δ) ≤ cum F (x - δF) :=
    le_trans (cum_le_of_subset hKF (x - δ)) (cum_mono F (by linarith))
  have h2 : cum K x ≤ cum F x := cum_le_of_subset hKF x
  have h3 : cum K (x + δ) ≤ cum F (x + δF) + (δ - δF) := by
    have hsubK := cum_le_of_subset hKF (x + δ)
    have hmono := cum_le_cum_add_sub (A := F) (show x + δF ≤ x + δ by linarith)
    linarith [hmono, hsubK]
  linarith [hKL, h1, h2, h3, hδFge]

/-- **The key lemma for compact sum-free sets** assembled from the per-thickening estimate.
From `exists_sumFree_thickening` obtain a radius `η₀` with `K + [-η₀, η₀]` sum-free.  For each
`ε > 0`, apply `key_lemma_compact_aux` with `η = min η₀ (min ε (δ/2))` (its thickening is a
subset of the `η₀`-thickening, hence sum-free) to get `LHS ≤ x + η ≤ x + ε`; then
`le_of_forall_pos_le_add`. -/
lemma key_lemma_compact {K : Set ℝ} (hKc : IsCompact K) (hsf : IsSumFree K) {δ : ℝ} (hδ : 0 < δ)
    (hmin : IsLeast K δ) :
    ∀ x : ℝ, δ ≤ x → cum K (x - δ) + cum K x + cum K (x + δ) ≤ x := by
  intro x hx
  obtain ⟨η₀, hη₀, hsfη₀⟩ := exists_sumFree_thickening hKc hsf
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set η := min η₀ (min ε (δ / 2)) with hηdef
  have hη0 : 0 < η := lt_min hη₀ (lt_min hε (by linarith))
  have hηε : η ≤ ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηδ : η < δ := by
    have : η ≤ δ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have hIccsub : Icc (-η) η ⊆ Icc (-η₀) η₀ := by
    intro z hz; simp only [mem_Icc] at hz ⊢
    constructor <;> [linarith [hz.1, min_le_left η₀ (min ε (δ/2))];
                     linarith [hz.2, min_le_left η₀ (min ε (δ/2))]]
  have hsub : K + Icc (-η) η ⊆ K + Icc (-η₀) η₀ := Set.add_subset_add (subset_refl K) hIccsub
  have hsfη : IsSumFree (K + Icc (-η) η) := hsfη₀.subset hsub
  have hkey := key_lemma_compact_aux hKc hmin hη0 hηδ hsfη x hx
  linarith [hkey, hηε]

/-- Inner approximation of a measurable set by a compact subset preserving the least element and
controlling the cumulative deficit.  Apply inner regularity of Lebesgue measure to `A ∩ [0, y]`
(finite measure) to get a compact `K₀ ⊆ A ∩ [0, y]` with `|A ∩ [0,y]| - |K₀| < ε`; set
`K = K₀ ∪ {δ}`.  Then `K` is compact, `K ⊆ A`, `IsLeast K δ`, `K` is sum-free (subset of `A`),
and for `z ≤ y`, `cum A z - cum K z = |(A \ K) ∩ [0,z]| ≤ |(A \ K) ∩ [0,y]| < ε`. -/
lemma exists_compact_sumFree_approx (hA : MeasurableSet A) (hsf : IsSumFree A) {δ : ℝ}
    (hmin : IsLeast A δ) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ A ∧ IsLeast K δ ∧ IsSumFree K ∧
      ∀ z : ℝ, z ≤ y → cum A z ≤ cum K z + ε := by
  set s := A ∩ Icc (0 : ℝ) y with hs_def
  have hs_meas : MeasurableSet s := hA.inter measurableSet_Icc
  have hs_fin : volume s ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.inter_subset_right))
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  obtain ⟨K₀, hK₀s, hK₀c, hK₀lt⟩ :=
    hs_meas.exists_isCompact_lt_add hs_fin (ε := ENNReal.ofReal ε)
      (by simp [ENNReal.ofReal_eq_zero, not_le, hε])
  refine ⟨K₀ ∪ {δ}, hK₀c.union (isCompact_singleton), ?_, ?_, ?_, ?_⟩
  · -- K ⊆ A
    rintro w (hw | hw)
    · exact ((hK₀s hw).1)
    · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hmin.1
  · -- IsLeast (K₀ ∪ {δ}) δ
    refine ⟨Or.inr rfl, ?_⟩
    rintro w (hw | hw)
    · exact hmin.2 (hK₀s hw).1
    · rw [Set.mem_singleton_iff] at hw; rw [hw]
  · -- sum-free
    refine hsf.subset ?_
    rintro w (hw | hw)
    · exact (hK₀s hw).1
    · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hmin.1
  · -- cumulative bound
    intro z hz
    have hK₀meas : MeasurableSet K₀ := hK₀c.measurableSet
    -- measure of the leftover s \ K₀ is ≤ ofReal ε
    have hdiff : volume (s \ K₀) ≤ ENNReal.ofReal ε := by
      have hKfin : volume K₀ ≠ ⊤ := ne_top_of_le_ne_top hs_fin (measure_mono hK₀s)
      rw [measure_diff hK₀s hK₀meas.nullMeasurableSet hKfin]
      rw [tsub_le_iff_right]
      exact le_of_lt (by rwa [add_comm] at hK₀lt)
    -- key set inclusion
    have hincl : A ∩ Icc 0 z ⊆ ((K₀ ∪ {δ}) ∩ Icc 0 z) ∪ (s \ K₀) := by
      intro w hw
      by_cases hwK : w ∈ K₀
      · exact Or.inl ⟨Or.inl hwK, hw.2⟩
      · refine Or.inr ⟨⟨hw.1, ?_⟩, hwK⟩
        exact Set.Icc_subset_Icc_right hz hw.2
    have hmono : volume (A ∩ Icc 0 z) ≤ volume ((K₀ ∪ {δ}) ∩ Icc 0 z) + ENNReal.ofReal ε := by
      calc volume (A ∩ Icc 0 z)
            ≤ volume (((K₀ ∪ {δ}) ∩ Icc 0 z) ∪ (s \ K₀)) := measure_mono hincl
        _ ≤ volume ((K₀ ∪ {δ}) ∩ Icc 0 z) + volume (s \ K₀) := measure_union_le _ _
        _ ≤ volume ((K₀ ∪ {δ}) ∩ Icc 0 z) + ENNReal.ofReal ε := by gcongr
    -- convert to reals
    have hKzfin : volume ((K₀ ∪ {δ}) ∩ Icc 0 z) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_right)
    unfold cum
    rw [← ENNReal.toReal_ofReal hε.le]
    rw [← ENNReal.toReal_add hKzfin ENNReal.ofReal_ne_top]
    exact ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.mpr ⟨hKzfin, ENNReal.ofReal_ne_top⟩) hmono

/-- **The key lemma** for measurable sets.  Obtained from `key_lemma_compact` by inner
regularity: for `ε > 0`, `exists_compact_sumFree_approx` (with `y = x + δ`) gives a compact
sum-free `K ⊆ A` with `IsLeast K δ` and `cum A z ≤ cum K z + ε` for `z ≤ x+δ`.  Applying
`key_lemma_compact` to `K` gives `cum A (x-δ)+cum A x+cum A (x+δ) ≤ x + 3ε`; let `ε → 0` via
`le_of_forall_pos_le_add`. -/
theorem key_lemma (hA : MeasurableSet A) (hsf : IsSumFree A) {δ : ℝ} (hδ : 0 < δ)
    (hmin : IsLeast A δ) :
    ∀ x : ℝ, δ ≤ x → cum A (x - δ) + cum A x + cum A (x + δ) ≤ x := by
  intro x hx
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨K, hKc, hKA, hKleast, hKsf, hcum⟩ :=
    exists_compact_sumFree_approx hA hsf hmin (x + δ) (show 0 < ε / 3 by linarith)
  have hcompact := key_lemma_compact hKc hKsf hδ hKleast x hx
  have hz1 := hcum (x - δ) (by linarith)
  have hz2 := hcum x (by linarith)
  have hz3 := hcum (x + δ) (le_refl _)
  linarith [hcompact, hz1, hz2, hz3]

/-- The key inequality extended to all `x ≥ 0`: for `0 ≤ x ≤ δ` it holds by the elementary
boundary estimate, and for `x ≥ δ` it is `key_lemma`. -/
theorem key_ineq_nonneg (hA : MeasurableSet A) (hsf : IsSumFree A) {δ : ℝ} (hδ : 0 < δ)
    (hmin : IsLeast A δ) :
    ∀ x : ℝ, 0 ≤ x → cum A (x - δ) + cum A x + cum A (x + δ) ≤ x := by
  have hAδ : A ⊆ Ici δ := fun a ha => hmin.2 ha
  intro x hx
  by_cases hxδ : δ ≤ x
  · exact key_lemma hA hsf hδ hmin x hxδ
  · push_neg at hxδ
    have h1 : cum A (x - δ) = 0 := cum_eq_zero_of_le hAδ (by linarith)
    have h2 : cum A x = 0 := cum_eq_zero_of_le hAδ (le_of_lt hxδ)
    have h3 : cum A (x + δ) ≤ x := by
      have := cum_le_sub_delta hAδ (y := x + δ) (by linarith)
      linarith
    linarith

/-- **Sum-free integral bound.** If `A` is a measurable sum-free set with least element `δ > 0`,
then `∫_{u>0} e^{-u} F(u) du < 1/3`, where `F(u) = |A ∩ [0,u]|`.

This is the reduction of the main theorem to the key lemma, made rigorous. It is proved modulo
`key_lemma`. -/
theorem sumfree_integral_lt_third (hA : MeasurableSet A) (hsf : IsSumFree A) {δ : ℝ}
    (hδ : 0 < δ) (hmin : IsLeast A δ) :
    (∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A u) < 1/3 := by
  have hAδ : A ⊆ Ici δ := fun a ha => hmin.2 ha
  exact integral_cum_lt_third hδ hAδ (key_ineq_nonneg hA hsf hδ hmin)

end ProductFree