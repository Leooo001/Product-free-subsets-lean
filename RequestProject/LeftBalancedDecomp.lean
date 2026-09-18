import RequestProject.IntervalUnion

/-!
# Greedy left-balanced decomposition

Corollary `key_bound` and the proof of `offdiagonal_main2` rely on decomposing a finite union
of closed intervals `B` into the (finitely many) maximal left-balanced intervals whose
`B`-intersections partition `B`.

We build this decomposition greedily from the left. The key step (`exists_max_lb`) is that for
each starting point `c` there is a largest right endpoint `d` with `[c,d]` left balanced; the set
of admissible right endpoints is a bounded, down-closed, closed interval.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {B : Set ℝ}

/-
The cumulative mass `x ↦ |A ∩ [c,x]|` is continuous (indeed 1-Lipschitz).
-/
lemma continuous_mass_right (A : Set ℝ) (hfin : volume A ≠ ⊤) (c : ℝ) :
    Continuous (fun x => (volume (A ∩ Icc c x)).toReal) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro x
  have h_lip : ∀ x y : ℝ, x ≤ y → |(volume (A ∩ Icc c y)).toReal - (volume (A ∩ Icc c x)).toReal| ≤ |y - x| := by
    intro x y hxy;
    -- Using the fact that the volume of the intersection of A with an interval is monotone, we have:
    have h_monotone : (volume (A ∩ Icc c y)).toReal ≤ (volume (A ∩ Icc c x)).toReal + (volume (Ioc x y)).toReal := by
      rw [ ← ENNReal.toReal_add ];
      · gcongr;
        · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ), by simp +decide [ hxy ] ⟩ );
        · refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
          exact fun z hz => if h : z ≤ x then Or.inl ⟨ hz.1, ⟨ hz.2.1, h ⟩ ⟩ else Or.inr ⟨ not_le.mp h, hz.2.2 ⟩;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
      · norm_num;
    rw [ abs_of_nonneg ( sub_nonneg_of_le <| ENNReal.toReal_mono ?_ <| MeasureTheory.measure_mono <| Set.inter_subset_inter_right _ <| Set.Icc_subset_Icc_right hxy ) ];
    · simp_all +decide [ Real.volume_Ioc ];
      linarith [ abs_of_nonneg ( sub_nonneg.mpr hxy ) ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
  refine' Metric.continuousAt_iff'.mpr _;
  intro ε hε; filter_upwards [ Metric.ball_mem_nhds x hε ] with y hy; rcases le_total y x with h | h <;> simp_all +decide [ dist_eq_norm ] ;
  · grind +suggestions;
  · exact lt_of_le_of_lt ( h_lip x y h ) hy

/-
`discOn A c ·` is continuous in the right endpoint.
-/
lemma continuous_discOn_right (A : Set ℝ) (hfin : volume A ≠ ⊤) (c : ℝ) :
    Continuous (fun x => discOn A c x) := by
  exact Continuous.sub ( continuous_const.mul ( continuous_mass_right A hfin c ) ) ( continuous_id.sub continuous_const )

/-- `d` is a *clean* cut point for the component list `ivs`: no component straddles it. -/
def CleanRight (ivs : List (ℝ × ℝ)) (d : ℝ) : Prop := ∀ p ∈ ivs, p.2 ≤ d ∨ d < p.1

/-
Intersecting an interval-union with `Ioi d` at a clean cut point gives the interval-union of
the components lying strictly to the right of `d`.
-/
lemma inter_Ioi_of_clean {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs) {d : ℝ}
    (hcl : CleanRight ivs d) :
    IsIntervalUnion (B ∩ Ioi d) (ivs.filter (fun p => decide (d < p.1))) := by
  obtain ⟨hle, hchain, hB⟩ := h;
  constructor;
  · exact fun p hp => hle p <| List.mem_of_mem_filter hp;
  · constructor;
    · rw [ List.isChain_iff_get ] at *;
      have h_filter : ∀ {l : List (ℝ × ℝ)}, List.IsChain (fun p q => p.2 < q.1) l → List.IsChain (fun p q => p.2 < q.1) (List.filter (fun p => d < p.1) l) := by
        intros l hl; induction l <;> simp_all +decide [ List.IsChain ] ;
        rename_i k hk ih; rw [ List.filter_cons ] ; by_cases h : d < k.1 <;> simp_all +decide [ List.isChain_cons_cons ] ;
        · rw [ List.isChain_cons' ] at *;
          cases hk <;> simp_all +decide [ List.IsChain ];
          grind;
        · rw [ if_neg ( not_lt_of_ge h ) ] ; exact ih ( List.isChain_cons'.mp hl |>.2 );
      exact h_filter ( by rw [ List.isChain_iff_get ] ; tauto ) |> fun h => by rw [ List.isChain_iff_getElem ] at h; tauto;
    · ext x;
      simp [hB];
      grind +locals

/-
The maximal left-balanced right endpoint `d` from `sInf B` is a clean cut point: no component
of `B` straddles `d`.
-/
lemma cleanRight_of_maximal {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs)
    (hfin : volume B ≠ ⊤) {d : ℝ}
    (hdd : IsLeftBalanced B (sInf B) d)
    (hmax : ∀ d', IsLeftBalanced B (sInf B) d' → d' ≤ d) :
    CleanRight ivs d := by
  intro p hp;
  contrapose! hmax;
  refine' ⟨ p.2, _, hmax.1 ⟩;
  refine' ⟨ _, _ ⟩;
  · linarith [ hdd.1, show sInf B ≤ d from hdd.1 ];
  · intro c hc₁ hc₂;
    by_cases hc₃ : c ≤ d;
    · exact hdd.2 c hc₁ hc₃;
    · -- Since $c > d$, we have $B \cap Icc (sInf B) c = (B \cap Icc (sInf B) d) \cup Icc d c$.
      have h_union : B ∩ Icc (sInf B) c = (B ∩ Icc (sInf B) d) ∪ Icc d c := by
        have h_union : Icc d c ⊆ B := by
          have h_subset : Icc p.1 p.2 ⊆ B := by
            exact h.2.2.symm ▸ Set.subset_iUnion₂_of_subset p hp ( Set.Subset.refl _ );
          exact Set.Subset.trans ( Set.Icc_subset_Icc ( by linarith ) ( by linarith ) ) h_subset;
        ext x;
        simp +zetaDelta at *;
        exact ⟨ fun hx => if h : x ≤ d then Or.inl ⟨ hx.1, hx.2.1, h ⟩ else Or.inr ⟨ by linarith, hx.2.2 ⟩, fun hx => hx.elim ( fun hx => ⟨ hx.1, hx.2.1, by linarith ⟩ ) fun hx => ⟨ h_union ⟨ by linarith, by linarith ⟩, by linarith [ show sInf B ≤ d from hdd.1.trans' ( by linarith ) ], by linarith ⟩ ⟩;
      -- Since $Icc d c$ is a subset of $B$, we have $volume (B ∩ Icc (sInf B) c) = volume (B ∩ Icc (sInf B) d) + volume (Icc d c)$.
      have h_volume : volume (B ∩ Icc (sInf B) c) = volume (B ∩ Icc (sInf B) d) + volume (Icc d c) := by
        rw [ h_union, MeasureTheory.measure_union₀ ];
        · exact measurableSet_Icc.nullMeasurableSet;
        · refine' MeasureTheory.measure_mono_null _ _;
          exact { d };
          · grind;
          · norm_num;
      have := hdd.2 d ( by linarith [ hdd.1 ] ) ( by linarith [ hdd.1 ] ) ; simp_all +decide [ discOn ];
      rw [ ENNReal.toReal_add ] <;> norm_num;
      · rw [ ENNReal.toReal_ofReal ] <;> linarith;
      · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) )

/-
**Greedy peeling step.** For a closed set `B` of finite measure and a starting point `c`,
there is a largest right endpoint `d ≥ c` with `[c,d]` left balanced w.r.t. `B`.
-/
lemma exists_max_lb (hB : IsClosed B) (hfin : volume B ≠ ⊤) (c : ℝ) :
    ∃ d, c ≤ d ∧ IsLeftBalanced B c d ∧ ∀ d', IsLeftBalanced B c d' → d' ≤ d := by
  -- Let `S = {d | IsLeftBalanced B c d}`.
  set S := {d : ℝ | c ≤ d ∧ IsLeftBalanced B c d} with hS_def;
  obtain ⟨d, hd⟩ : ∃ d, IsLUB S d := by
    refine' ⟨ _, isLUB_csSup _ _ ⟩;
    · refine' ⟨ c, _, _ ⟩ <;> norm_num [ IsLeftBalanced ];
      intro x hx₁ hx₂; rw [ le_antisymm hx₂ hx₁ ] ; unfold discOn; norm_num;
    · refine' ⟨ c + 2 * ( volume B |> ENNReal.toReal ), fun d hd => _ ⟩;
      have := hd.2.2 d hd.1 le_rfl;
      unfold discOn at this;
      linarith [ show ( volume ( B ∩ Icc c d ) |> ENNReal.toReal ) ≤ ( volume B |> ENNReal.toReal ) from ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ];
  refine' ⟨ d, _, _, _ ⟩;
  · exact hd.1 ⟨ le_rfl, ⟨ le_rfl, fun x hx₁ hx₂ => by rw [ show x = c by linarith ] ; simp +decide [ discOn ] ⟩ ⟩;
  · refine' ⟨ _, _ ⟩;
    · exact hd.1 ⟨ le_rfl, ⟨ le_rfl, fun x hx₁ hx₂ => by
        unfold discOn; norm_num [ show x = c by linarith ] ; ⟩ ⟩;
    · intro x hx₁ hx₂; rcases eq_or_lt_of_le hx₂ with rfl | hx₂' <;> simp_all +decide [ IsLeftBalanced ] ;
      · have h_seq : ∃ seq : ℕ → ℝ, (∀ n, seq n ∈ S) ∧ Filter.Tendsto seq Filter.atTop (nhds x) := by
          have h_seq : ∀ ε > 0, ∃ d ∈ S, x - ε < d ∧ d ≤ x := by
            intro ε ε_pos; rcases hd.exists_between ( show x - ε < x by linarith ) with ⟨ d, hd₁, hd₂ ⟩ ; use d; aesop;
          generalize_proofs at *; (
          choose! seq hseq using h_seq;
          exact ⟨ fun n => seq ( 1 / ( n + 1 ) ), fun n => hseq _ ( by positivity ) |>.1, tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ hseq ( 1 / ( n + 1 ) ) ( by positivity ) ], by linarith [ hseq ( 1 / ( n + 1 ) ) ( by positivity ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩)
        generalize_proofs at *; (
        obtain ⟨ seq, hseq₁, hseq₂ ⟩ := h_seq; exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( continuous_discOn_right B hfin c |> Continuous.continuousAt |> fun h => h.tendsto.comp hseq₂ ) fun n => hseq₁ n |>.2 |>.2 _ ( by linarith [ hseq₁ n |>.1 ] ) ( by linarith [ hseq₁ n |>.1 ] ) ;);
      · rcases hd.exists_between hx₂' with ⟨ y, ⟨ hy₁, hy₂ ⟩, hy₃ ⟩ ; linarith [ hy₂ x hx₁ ( by linarith ) ];
  · exact fun d' hd' => hd.1 ⟨ hd'.1, hd' ⟩

/-
**Peeling the leftmost block.** For a nonempty interval-union `B` (list `ivs`), there is a
maximal left-balanced interval `[sInf B, d]` starting at `sInf B`, and `B ∩ Ioi d` is again an
interval-union with strictly fewer components, all lying strictly to the right of `d`.
-/
lemma peel {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs) (hne : ivs ≠ []) (hB : IsClosed B) :
    ∃ (d : ℝ) (ivs' : List (ℝ × ℝ)),
      sInf B ≤ d ∧ IsLeftBalanced B (sInf B) d ∧
      (∀ d', IsLeftBalanced B (sInf B) d' → d' ≤ d) ∧
      IsIntervalUnion (B ∩ Ioi d) ivs' ∧ ivs'.length < ivs.length ∧
      (∀ p ∈ ivs', d < p.1) := by
  have := exists_max_lb hB ?_ ( sInf B );
  · obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := this;
    refine' ⟨ d, ivs.filter ( fun p => decide ( d < p.1 ) ), hd₁, hd₂, hd₃, _, _, _ ⟩;
    · apply inter_Ioi_of_clean h (cleanRight_of_maximal h (h.finite) hd₂ hd₃);
    · have := h.sInf_eq hne;
      refine' lt_of_lt_of_le ( List.length_filter_lt_length_iff_exists.mpr _ ) ( by simpa );
      exact ⟨ _, List.head_mem hne, by aesop ⟩;
    · grind;
  · exact h.finite

end ProductFree