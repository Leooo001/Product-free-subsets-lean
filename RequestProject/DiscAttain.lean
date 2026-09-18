import RequestProject.MaxBalanced

/-!
# Attainment of the discrepancy

The discrepancy `disc B` of a nonempty finite union of finite closed intervals is *attained*:
there is a balanced interval `[p,q] ⊆ [sInf B, sSup B]` with `discOn B p q = disc B`. This is the
statement that a discrepancy-maximizing interval exists and is balanced, used in the induction for
`offdiagonal_main2` to locate the discrepancy of `B` inside a specific component.
-/

open MeasureTheory Set

noncomputable section

namespace ProductFree

variable {B : Set ℝ}

/-- `B` is contained in `[sInf B, sSup B]`. -/
lemma IsIntervalUnion.subset_Icc_infSup {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs)
    (hne : ivs ≠ []) : B ⊆ Icc (sInf B) (sSup B) := by
  rw [hB.sInf_eq hne, hB.sSup_eq hne]; exact hB.subset_Icc hne

/-
For `sInf B ≤ a ≤ b`, the real mass `|B ∩ [a,b]|` telescopes:
`|B ∩ [a,b]| = |B ∩ [sInf B, b]| - |B ∩ [sInf B, a]|`.
-/
lemma mass_inter_sub {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hne : ivs ≠ [])
    {a b : ℝ} (ha : sInf B ≤ a) (hab : a ≤ b) :
    (volume (B ∩ Icc a b)).toReal
      = (volume (B ∩ Icc (sInf B) b)).toReal - (volume (B ∩ Icc (sInf B) a)).toReal := by
  rw [ eq_sub_iff_add_eq', ← ENNReal.toReal_add ];
  · rw [ ← MeasureTheory.measure_union₀ ];
    · rw [ ← Set.inter_union_distrib_left, Set.Icc_union_Icc_eq_Icc ] <;> linarith;
    · exact MeasurableSet.nullMeasurableSet ( hB.isClosed.measurableSet.inter measurableSet_Icc );
    · refine' MeasureTheory.measure_mono_null _ _;
      exact { a };
      · grind;
      · norm_num;
  · have := hB.finite; exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) this.lt_top ) ;
  · have := hB.finite;
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr this ) )

/-
**Discrepancy attainment.** For a nonempty finite union of finite closed intervals `B` there
is a balanced interval `[p,q]` inside `[sInf B, sSup B]` whose discrepancy equals `disc B`.
-/
lemma disc_attained {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hne : ivs ≠ []) :
    ∃ p q, sInf B ≤ p ∧ p ≤ q ∧ q ≤ sSup B ∧ IsBalanced B p q ∧ discOn B p q = disc B := by
  -- By definition of $D$, we know that $D$ is compact.
  have hD_compact : IsCompact {ab : ℝ × ℝ | sInf B ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ sSup B} := by
    refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
    exact ⟨ by exact IsClosed.inter ( isClosed_Ici.preimage continuous_fst ) ( IsClosed.inter ( isClosed_le continuous_fst continuous_snd ) ( isClosed_le continuous_snd continuous_const ) ), by exact isBounded_iff_forall_norm_le.mpr ⟨ |sInf B| + |sSup B| + 1, by rintro ⟨ x, y ⟩ ⟨ hx, hy, hxy ⟩ ; exact max_le ( abs_le.mpr ⟨ by cases abs_cases ( sInf B ) <;> cases abs_cases ( sSup B ) <;> linarith, by cases abs_cases ( sInf B ) <;> cases abs_cases ( sSup B ) <;> linarith ⟩ ) ( abs_le.mpr ⟨ by cases abs_cases ( sInf B ) <;> cases abs_cases ( sSup B ) <;> linarith, by cases abs_cases ( sInf B ) <;> cases abs_cases ( sSup B ) <;> linarith ⟩ ) ⟩ ⟩;
  obtain ⟨pq, hpq⟩ : ∃ pq : ℝ × ℝ, pq ∈ {ab : ℝ × ℝ | sInf B ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ sSup B} ∧ ∀ ab ∈ {ab : ℝ × ℝ | sInf B ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ sSup B}, ProductFree.discOn B ab.1 ab.2 ≤ ProductFree.discOn B pq.1 pq.2 := by
    have h_cont : ContinuousOn (fun ab : ℝ × ℝ => ProductFree.discOn B ab.1 ab.2) {ab : ℝ × ℝ | sInf B ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ sSup B} := by
      have h_cont : ContinuousOn (fun ab : ℝ × ℝ => 2 * ((volume (B ∩ Icc (sInf B) ab.2)).toReal - (volume (B ∩ Icc (sInf B) ab.1)).toReal) - (ab.2 - ab.1)) {ab : ℝ × ℝ | sInf B ≤ ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 ≤ sSup B} := by
        have h_cont : ContinuousOn (fun x => (volume (B ∩ Icc (sInf B) x)).toReal) (Set.Icc (sInf B) (sSup B)) := by
          exact Continuous.continuousOn ( continuous_mass_right B ( hB.finite ) ( sInf B ) );
        exact ContinuousOn.sub ( ContinuousOn.mul continuousOn_const ( ContinuousOn.sub ( h_cont.comp continuousOn_snd fun x hx => ⟨ by linarith [ hx.1, hx.2.1 ], by linarith [ hx.1, hx.2.1, hx.2.2 ] ⟩ ) ( h_cont.comp continuousOn_fst fun x hx => ⟨ by linarith [ hx.1, hx.2.1 ], by linarith [ hx.1, hx.2.1, hx.2.2 ] ⟩ ) ) ) ( ContinuousOn.sub continuousOn_snd continuousOn_fst );
      refine' h_cont.congr fun ab hab => _;
      rw [ ← mass_inter_sub hB hne hab.1 hab.2.1 ];
      rfl;
    exact hD_compact.exists_isMaxOn ⟨ ⟨ sInf B, sInf B ⟩, ⟨ le_rfl, le_rfl, IsIntervalUnion.subset_Icc_infSup hB hne ( show sInf B ∈ B from by
                                                                                                                        convert hB.isClosed.csInf_mem _;
                                                                                                                        · exact ⟨ fun h => fun _ => h, fun h => h <| by exact ⟨ _, fun x hx => hB.subset_Icc_infSup hne hx |>.1 ⟩ ⟩;
                                                                                                                        · exact hB.nonempty hne ) |>.2 ⟩ ⟩ h_cont;
  refine' ⟨ pq.1, pq.2, hpq.1.1, hpq.1.2.1, hpq.1.2.2, _, _ ⟩;
  · refine' ⟨ ⟨ hpq.1.2.1, _ ⟩, ⟨ hpq.1.2.1, _ ⟩ ⟩;
    · intro c hc₁ hc₂; have := hpq.2 ( pq.1, c ) ⟨ by linarith [ hpq.1.1 ], by linarith [ hpq.1.2.1 ], by linarith [ hpq.1.2.2 ] ⟩ ; simp_all +decide [ discOn ] ;
      grind +suggestions;
    · intro c hc₁ hc₂;
      have := hpq.2 ( pq.1, c ) ⟨ by linarith [ hpq.1.1 ], by linarith [ hpq.1.2.1 ], by linarith [ hpq.1.2.2 ] ⟩;
      linarith [ discOn_add ( show MeasurableSet B from hB.isClosed.measurableSet ) ( show pq.1 ≤ c by linarith ) ( show c ≤ pq.2 by linarith ) ];
  · refine' le_antisymm _ _;
    · apply_rules [ ProductFree.discOn_le_disc ];
      · exact hB.finite;
      · linarith [ hpq.1.2.1 ];
    · refine' csSup_le _ _;
      · exact ⟨ _, ⟨ 0, 0, le_rfl, rfl ⟩ ⟩;
      · rintro _ ⟨ a, b, hab, rfl ⟩;
        by_cases h_cases : max a (sInf B) ≤ min b (sSup B);
        · refine' le_trans _ ( hpq.2 ( max a ( sInf B ), min b ( sSup B ) ) ⟨ _, _, _ ⟩ );
          · rw [ show B ∩ Icc a b = B ∩ Icc ( max a ( sInf B ) ) ( min b ( sSup B ) ) from ?_ ];
            · exact sub_le_sub_left ( by cases max_cases a ( sInf B ) <;> cases min_cases b ( sSup B ) <;> linarith ) _;
            · ext x; simp [h_cases];
              exact fun hx => ⟨ fun h => ⟨ ⟨ h.1, by linarith [ show sInf B ≤ x from csInf_le ( show BddBelow B from by
                                                                                                  have := hB.subset_Icc_infSup hne;
                                                                                                  exact ⟨ sInf B, fun x hx => this hx |>.1 ⟩ ) hx ] ⟩, h.2, by linarith [ show x ≤ sSup B from le_csSup ( show BddAbove B from by
                                                                                                                                                                                            exact ⟨ sSup B, fun x hx => le_csSup ( show BddAbove B from by exact IsCompact.bddAbove ( show IsCompact B from by exact hB.isCompact ) ) hx ⟩ ) hx ] ⟩, fun h => ⟨ h.1.1, h.2.1 ⟩ ⟩;
          · exact le_max_right _ _;
          · exact h_cases;
          · exact min_le_right _ _;
        · -- Since $max a (sInf B) > min b (sSup B)$, we have $B \cap Icc a b = \emptyset$.
          have h_empty : B ∩ Icc a b = ∅ := by
            ext x
            simp [h_cases];
            intro hx hx';
            contrapose! h_cases;
            exact le_min ( by linarith ) ( by linarith [ show x ≤ sSup B from le_csSup ( show BddAbove B from by exact ( IsCompact.bddAbove ( ProductFree.IsIntervalUnion.isCompact hB ) ) ) hx ] ) |> le_trans ( max_le ( by linarith ) ( by exact ( csInf_le ( show BddBelow B from by exact ( IsCompact.bddBelow ( ProductFree.IsIntervalUnion.isCompact hB ) ) ) hx ) ) );
          simp_all +decide [ discOn ];
          contrapose! hpq;
          intro h;
          use sInf B, sInf B;
          simp_all +decide [ Set.Icc_self ];
          exact ⟨ by linarith, by linarith [ show ( volume ( B ∩ { sInf B } ) |> ENNReal.toReal ) ≥ 0 by positivity ] ⟩

end ProductFree