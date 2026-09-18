import RequestProject.KeyLemma

/-!
# Main theorem: product-free sets in `(0,1)` have measure `< 1/3`

We transport the sum-free integral bound (`sumfree_integral_lt_third`) back to the
multiplicative side via the substitution `u = -log x`.

* `ProductFree.main1_compact`: a nonempty compact product-free subset of `(0,1)` has measure
  `< 1/3`.
* `ProductFree.main1`: an open product-free subset of `(0,1)` has measure `≤ 1/3`
  (the open-set version, obtained by approximation).

All results are fully proved: `key_lemma` (on which they rely) is proved `sorry`-free in
`RequestProject/KeyLemma.lean`.
-/

open MeasureTheory Set

noncomputable section

namespace ProductFree

/-- The change of variables map `x ↦ -log x`, a homeomorphism `(0,∞) → ℝ`. -/
def negLog (x : ℝ) : ℝ := -Real.log x

/-
`negLog` is injective on the positive reals.
-/
lemma injOn_negLog {s : Set ℝ} (hs : s ⊆ Ioi 0) : Set.InjOn negLog s := by
  exact fun x hx y hy hxy => Real.log_injOn_pos ( hs hx ) ( hs hy ) ( by unfold negLog at hxy; linarith )

/-
If `E ⊆ (0,1)` is product-free, then `negLog '' E` is sum-free.
-/
lemma isSumFree_image {E : Set ℝ} (hE : E ⊆ Ioo 0 1) (hpf : IsProductFree E) :
    IsSumFree (negLog '' E) := by
  intro p hp q hq hpq;
  obtain ⟨ x, hx, rfl ⟩ := hp
  obtain ⟨ y, hy, rfl ⟩ := hq
  obtain ⟨ z, hz, hpq ⟩ := hpq
  have hxy : x * y = z := by
    unfold negLog at hpq;
    rw [ ← Real.exp_log ( hE hx |>.1 ), ← Real.exp_log ( hE hy |>.1 ), ← Real.exp_log ( hE hz |>.1 ), ← Real.exp_add ] ; norm_num ; linarith;
  exact hpf hx hy ( hxy ▸ hz )

private lemma negLog_image_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    negLog '' Icc a b = Icc (negLog b) (negLog a) := by
  ext x;
  constructor;
  · rintro ⟨ y, ⟨ hy₁, hy₂ ⟩, rfl ⟩;
    exact ⟨ neg_le_neg <| Real.log_le_log ( by linarith ) <| by linarith, neg_le_neg <| Real.log_le_log ( by linarith ) <| by linarith ⟩;
  · apply_rules [ intermediate_value_Icc' ];
    exact ContinuousOn.neg ( continuousOn_of_forall_continuousAt fun x hx => Real.continuousAt_log ( by linarith [ hx.1 ] ) )

private lemma intervalUnion_endpoint_pos {E : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hIU : IsIntervalUnion E ivs) (hE : E ⊆ Ioo 0 1) {p : ℝ × ℝ} (hp : p ∈ ivs) :
    0 < p.1 ∧ 0 < p.2 := by
  -- Both endpoints p.1,p.2 belong to E, so by hE they belong to (0,1), hence are positive.
  have hp1_mem_E : p.1 ∈ E := by
    exact hIU.2.2 ▸ Set.mem_iUnion₂.2 ⟨ p, hp, left_mem_Icc.2 ( hIU.1 p hp ) ⟩
  have hp1_pos : 0 < p.1 := by
    exact hE hp1_mem_E |>.1
  have hp2_mem_E : p.2 ∈ E := by
    obtain ⟨ _, hU, hI, hE ⟩ := hIU;
    exact Set.mem_iUnion₂.mpr ⟨ p, hp, by constructor <;> linarith [ ‹∀ p ∈ ivs, p.1 ≤ p.2› p hp ] ⟩
  have hp2_pos : 0 < p.2 := by
    exact hE hp2_mem_E |>.1
  exact ⟨hp1_pos, hp2_pos⟩

/-
The decreasing homeomorphism `negLog` sends a finite union of closed intervals in
`(0,1)` to a finite union of closed intervals, with the component order reversed.
-/
lemma isIntervalUnion_negLog_image {E : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hIU : IsIntervalUnion E ivs) (hE : E ⊆ Ioo 0 1) :
    IsIntervalUnion (negLog '' E)
      (ivs.reverse.map (fun p => (negLog p.2, negLog p.1))) := by
  constructor;
  · simp +zetaDelta at *;
    intros a b x y hx hy hz; subst_vars; exact (by
    exact neg_le_neg ( Real.log_le_log ( by linarith [ intervalUnion_endpoint_pos hIU hE hx ] ) ( by linarith [ intervalUnion_endpoint_pos hIU hE hx, hIU.1 _ hx ] ) ));
  · constructor;
    · unfold IsIntervalUnion at hIU;
      simp_all +decide [ List.isChain_iff_getElem ];
      intro i hi;
      refine' neg_lt_neg ( Real.log_lt_log _ _ );
      · grind +suggestions;
      · grind;
    · ext x;
      constructor;
      · rintro ⟨ y, hy, rfl ⟩;
        rcases hIU.2.2.subset hy with ⟨ p, hp, hp' ⟩;
        obtain ⟨ q, hq, rfl ⟩ := hp;
        simp_all +decide [ negLog ];
        exact ⟨ q.1, q.2, Real.log_le_log ( by linarith [ Set.mem_Ioo.mp ( hE hy ), Set.mem_Ioo.mp ( hE hy ), show 0 < q.1 from by linarith [ Set.mem_Ioo.mp ( hE hy ), Set.mem_Ioo.mp ( hE hy ), intervalUnion_endpoint_pos hIU hE hp'.2.1 ] ] ) ( by linarith ), hp'.2.1, Real.log_le_log ( by linarith [ Set.mem_Ioo.mp ( hE hy ), Set.mem_Ioo.mp ( hE hy ), show 0 < q.1 from by linarith [ Set.mem_Ioo.mp ( hE hy ), Set.mem_Ioo.mp ( hE hy ), intervalUnion_endpoint_pos hIU hE hp'.2.1 ] ] ) ( by linarith ) ⟩;
      · simp_all +decide [ IsIntervalUnion ];
        intro a b hx₁ hx₂ hx₃;
        -- Since $negLog$ is strictly decreasing, we have $a \leq exp(-x) \leq b$.
        have h_exp : a ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ b := by
          unfold negLog at *;
          exact ⟨ by rw [ ← Real.log_le_log_iff ( by linarith [ Set.mem_Ioo.mp ( hE _ _ hx₂ ( Set.left_mem_Icc.mpr ( hIU.1 _ _ hx₂ ) ) ) ] ) ( by positivity ), Real.log_exp ] ; linarith, by rw [ ← Real.log_le_log_iff ( by positivity ) ( by linarith [ Set.mem_Ioo.mp ( hE _ _ hx₂ ( Set.right_mem_Icc.mpr ( hIU.1 _ _ hx₂ ) ) ) ] ), Real.log_exp ] ; linarith ⟩;
        exact ⟨ Real.exp ( -x ), ⟨ a, h_exp.1, b, hx₂, h_exp.2 ⟩, by unfold negLog; norm_num ⟩

/-
The image of a compact `E ⊆ (0,1)` under `negLog` is measurable.
-/
lemma measurableSet_image_of_compact {E : Set ℝ} (hEc : IsCompact E) (hE : E ⊆ Ioo 0 1) :
    MeasurableSet (negLog '' E) := by
  convert hEc.image_of_continuousOn ( show ContinuousOn negLog E from ?_ ) |> IsCompact.measurableSet;
  exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.neg ( Real.continuousAt_log ( ne_of_gt ( hE hx |>.1 ) ) )

/-
For a nonempty compact `E ⊆ (0,1)`, `negLog '' E` has least element `negLog (sSup E) > 0`.
-/
lemma isLeast_image {E : Set ℝ} (hEc : IsCompact E) (hEne : E.Nonempty) (hE : E ⊆ Ioo 0 1) :
    IsLeast (negLog '' E) (negLog (sSup E)) ∧ 0 < negLog (sSup E) := by
  refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
  · exact ⟨ _, hEc.sSup_mem hEne, rfl ⟩;
  · intro x hx
    obtain ⟨y, hyE, rfl⟩ := hx
    have hy_le : y ≤ sSup E := by
      exact le_csSup ( hEc.bddAbove ) hyE
    have hlog_le : Real.log y ≤ Real.log (sSup E) := by
      exact Real.log_le_log ( hE hyE |>.1 ) hy_le
    have hneglog_le : -Real.log (sSup E) ≤ -Real.log y := by
      linarith
    exact hneglog_le;
  · exact neg_pos_of_neg ( Real.log_neg ( hE ( hEc.sSup_mem hEne ) |>.1 ) ( hE ( hEc.sSup_mem hEne ) |>.2 ) )

/-
**Change of variables.** For measurable `E ⊆ (0,1)`,
`∫_{u ∈ negLog '' E} e^{-u} du = |E|`.
-/
lemma setIntegral_exp_image_eq_volume {E : Set ℝ} (hE : MeasurableSet E) (hE1 : E ⊆ Ioo 0 1) :
    (∫ u in negLog '' E, Real.exp (-u)) = (volume E).toReal := by
  rw [ MeasureTheory.integral_image_eq_integral_abs_deriv_smul ];
  any_goals intro x hx; exact HasDerivAt.hasDerivWithinAt ( by simpa using HasDerivAt.neg ( Real.hasDerivAt_log ( ne_of_gt ( hE1 hx |>.1 ) ) ) );
  · simp +decide [ negLog ];
    rw [ MeasureTheory.setIntegral_congr_fun hE fun x hx => by rw [ Real.exp_log ( hE1 hx |>.1 ), abs_of_pos ( hE1 hx |>.1 ), inv_mul_cancel₀ ( ne_of_gt ( hE1 hx |>.1 ) ) ] ] ; norm_num;
    rfl;
  · grind +qlia;
  · exact injOn_negLog fun x hx => hE1 hx |>.1

/-
**Fubini identity.** For measurable `A ⊆ (0,∞)` of finite measure,
`∫_{u ∈ A} e^{-u} du = ∫_{u>0} e^{-u} F(u) du`, where `F(u) = |A ∩ [0,u]|`.
-/
lemma setIntegral_exp_eq_integral_cum {A : Set ℝ} (hA : MeasurableSet A) (hA0 : A ⊆ Ioi 0) :
    (∫ u in A, Real.exp (-u)) = ∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A u := by
  -- By Fubini's theorem, we can interchange the order of integration.
  have h_fubini : ∫⁻ u in Set.Ioi 0, ENNReal.ofReal (Real.exp (-u)) * (MeasureTheory.volume (A ∩ Set.Icc 0 u)) = ∫⁻ t in A, ENNReal.ofReal (Real.exp (-t)) := by
    have h_fubini : ∫⁻ u in Set.Ioi 0, ENNReal.ofReal (Real.exp (-u)) * (MeasureTheory.volume (A ∩ Set.Icc 0 u)) = ∫⁻ u in Set.Ioi 0, ∫⁻ t in A, (if t ≤ u then ENNReal.ofReal (Real.exp (-u)) else 0) := by
      refine' MeasureTheory.lintegral_congr fun u => _;
      rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
      change ENNReal.ofReal ( Real.exp ( -u ) ) * volume ( A ∩ Icc 0 u ) = ∫⁻ t in A ∩ Icc 0 u, ENNReal.ofReal ( Real.exp ( -u ) ) ∂volume.restrict A;
      · simp +decide [ Set.inter_assoc, hA ];
        exact congr_arg _ ( congr_arg _ ( by ext; aesop ) );
      · exact hA.inter measurableSet_Icc;
      · filter_upwards [ MeasureTheory.ae_restrict_mem hA ] with t ht;
        simp +decide [ Set.indicator, ht, hA0 ht |> Set.mem_Ioi.mp |> le_of_lt ];
    rw [ h_fubini, ← MeasureTheory.lintegral_lintegral_swap ];
    · refine' MeasureTheory.setLIntegral_congr_fun hA _;
      intro x hx; simp +decide [ ← MeasureTheory.lintegral_indicator, Set.indicator_apply ] ;
      rw [ show ( ∫⁻ a : ℝ, if 0 < a then if x ≤ a then ENNReal.ofReal ( Real.exp ( -a ) ) else 0 else 0 ) = ∫⁻ a in Set.Ici x, ENNReal.ofReal ( Real.exp ( -a ) ) from ?_ ];
      · rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · rw [ MeasureTheory.integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi ];
        · exact MeasureTheory.IntegrableOn.mono_set ( by exact MeasureTheory.integrable_of_integral_eq_one ( by simpa using integral_exp_neg_Ioi_zero ) ) ( Set.Ici_subset_Ioi.mpr ( show x > 0 from hA0 hx ) );
        · exact Filter.Eventually.of_forall fun _ => Real.exp_nonneg _;
      · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
        congr with a ; split_ifs <;> norm_num ; linarith [ Set.mem_Ioi.mp ( hA0 hx ) ];
    · exact Measurable.aemeasurable ( by exact Measurable.ite ( measurableSet_le measurable_fst measurable_snd ) ( by exact Measurable.ennreal_ofReal ( by exact Measurable.exp ( measurable_neg.comp measurable_snd ) ) ) measurable_const )
  generalize_proofs at *;
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae, MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · convert congr_arg ENNReal.toReal h_fubini.symm using 1;
    congr! 2;
    ext; rw [ ENNReal.ofReal_mul ( Real.exp_pos _ |> le_of_lt ) ] ;
    exact congrArg _ ( ENNReal.ofReal_toReal <| ne_of_lt <| lt_of_le_of_lt ( MeasureTheory.measure_mono <| Set.inter_subset_right ) <| by simp +decide [ Real.volume_Icc ] );
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with u hu using mul_nonneg ( Real.exp_nonneg _ ) ( cum_nonneg _ _ );
  · refine' Measurable.aestronglyMeasurable _;
    refine' Measurable.mul _ _;
    · exact Measurable.exp ( measurable_id.neg );
    · refine' Monotone.measurable ((ProductFree.cum_mono A) );
  · exact Filter.Eventually.of_forall fun x => Real.exp_nonneg _;
  · exact Continuous.aestronglyMeasurable ( by continuity )

/-- **Main theorem (compact version).** A nonempty compact product-free subset of `(0,1)` has
Lebesgue measure less than `1/3`. -/
theorem main1_compact {E : Set ℝ} (hEc : IsCompact E) (hEne : E.Nonempty) (hE : E ⊆ Ioo 0 1)
    (hpf : IsProductFree E) : (volume E).toReal < 1/3 := by
  set A := negLog '' E with hAdef
  have hAmeas : MeasurableSet A := measurableSet_image_of_compact hEc hE
  have hsf : IsSumFree A := isSumFree_image hE hpf
  obtain ⟨hleast, hδpos⟩ := isLeast_image hEc hEne hE
  have hEmeas : MeasurableSet E := hEc.measurableSet
  have hA0 : A ⊆ Ioi 0 := by
    intro a ha
    exact lt_of_lt_of_le hδpos (hleast.2 ha)
  have h1 : (volume E).toReal = ∫ u in Ioi (0:ℝ), Real.exp (-u) * cum A u := by
    rw [← setIntegral_exp_image_eq_volume hEmeas hE, ← hAdef,
      setIntegral_exp_eq_integral_cum hAmeas hA0]
  rw [h1]
  exact sumfree_integral_lt_third hAmeas hsf hδpos hleast

/-
**Main theorem (finite-union version).** A nonempty product-free finite union of
closed intervals contained in `(0,1)` has Lebesgue measure less than `1/3`.
-/
theorem main1_intervalUnion {E : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hIU : IsIntervalUnion E ivs) (hEne : E.Nonempty) (hE : E ⊆ Ioo 0 1)
    (hpf : IsProductFree E) : (volume E).toReal < 1 / 3 := by
  obtain ⟨ δ, hδ ⟩ := isLeast_image ( hIU.isCompact ) hEne hE;
  convert sumfree_integral_intervalUnion_lt_third ( isIntervalUnion_negLog_image hIU hE ) ( isSumFree_image hE hpf ) hδ δ using 1;
  rw [ ← setIntegral_exp_image_eq_volume, ← setIntegral_exp_eq_integral_cum ];
  · exact measurableSet_image_of_compact hIU.isCompact hE;
  · exact Set.image_subset_iff.mpr fun x hx => show 0 < negLog x from neg_pos_of_neg <| Real.log_neg ( hE hx |>.1 ) ( hE hx |>.2 );
  · exact hIU.isCompact.measurableSet;
  · assumption

/-- Product-freeness is inherited by subsets. -/
lemma IsProductFree.subset {E K : Set ℝ} (hpf : IsProductFree E) (hKE : K ⊆ E) :
    IsProductFree K :=
  fun _ hx _ hy hmem => hpf (hKE hx) (hKE hy) (hKE hmem)

/-- **Main theorem (open version).** An open product-free subset of `(0,1)` has Lebesgue
measure at most `1/3`. Obtained from the compact case by inner regularity of Lebesgue measure. -/
theorem main1 {E : Set ℝ} (hEo : IsOpen E) (hE : E ⊆ Ioo 0 1) (hpf : IsProductFree E) :
    volume E ≤ ENNReal.ofReal (1/3) := by
  have hEmeas : MeasurableSet E := hEo.measurableSet
  have hfin : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hE)
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  rw [hEmeas.measure_eq_iSup_isCompact_of_ne_top hfin]
  refine iSup_le (fun K => iSup_le (fun hKE => iSup_le (fun hKc => ?_)))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · simp [hKe]
  · have hlt : (volume K).toReal < 1/3 :=
      main1_compact hKc hKne (hKE.trans hE) (hpf.subset hKE)
    have hKfin : volume K ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (measure_mono hKE)
    calc volume K = ENNReal.ofReal ((volume K).toReal) := (ENNReal.ofReal_toReal hKfin).symm
      _ ≤ ENNReal.ofReal (1/3) := ENNReal.ofReal_le_ofReal (le_of_lt hlt)

end ProductFree