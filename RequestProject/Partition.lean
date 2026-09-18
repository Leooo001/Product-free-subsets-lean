import RequestProject.DiscAttain

/-!
# Structural helpers for the off-diagonal induction

This file collects the structural facts used in the recursive (second) case of the induction
proving `offdiagonal_main2`:

* `inter_Iic_of_clean`: intersecting an interval-union with `Iic d` at a clean cut point yields
  the interval-union of the components lying weakly to the left of `d` (companion to the existing
  `inter_Ioi_of_clean`).
* `iu_disc_pos`: an interval-union of positive measure has strictly positive discrepancy.
* `disc_inter_le` (the paper's `partition` monotonicity, in restricted form): the discrepancy of
  the restriction of `B` to a maximal left-balanced interval `[c,d]` is bounded by the discrepancy
  of the leftmost balanced block `[c,a1]`.
-/

open MeasureTheory Set

noncomputable section

namespace ProductFree

variable {B : Set ℝ}

/-
Intersecting an interval-union with `Iic d` at a clean cut point gives the interval-union of
the components lying weakly to the left of `d`.
-/
lemma inter_Iic_of_clean {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs) {d : ℝ}
    (hcl : CleanRight ivs d) :
    IsIntervalUnion (B ∩ Iic d) (ivs.filter (fun p => decide (p.2 ≤ d))) := by
  unfold CleanRight at *; unfold IsIntervalUnion at *; simp_all +decide [ Set.ext_iff ] ;
  refine' ⟨ _, _ ⟩;
  · rw [ List.isChain_iff_getElem ] at *;
    have h_filter : ∀ {l : List (ℝ × ℝ)}, (∀ i (hi : i + 1 < l.length), l[i].2 < l[i + 1].1) → ∀ i (hi : i + 1 < (List.filter (fun p => p.2 ≤ d) l).length), (List.filter (fun p => p.2 ≤ d) l)[i].2 < (List.filter (fun p => p.2 ≤ d) l)[i + 1].1 := by
      intros l hl i hi;
      induction' l with p l ih generalizing i;
      · contradiction;
      · by_cases h : p.2 ≤ d <;> simp_all +decide [ List.filter_cons ];
        · rcases i with ( _ | i ) <;> simp_all +decide [ List.getElem_cons ];
          · grind +qlia;
          · grind;
        · grind;
    exact h_filter h.2.1;
  · grind

/-
An interval-union of positive measure has strictly positive discrepancy: some component has
positive length, and a full component `[p,q] ⊆ S` gives `discOn S p q = q - p > 0`.
-/
lemma iu_disc_pos {S : Set ℝ} {ivs : List (ℝ × ℝ)} (hS : IsIntervalUnion S ivs)
    (h : 0 < (volume S).toReal) : 0 < disc S := by
  -- By definition of $IsIntervalUnion$, there exists a pair $p \in ivs$ such that $p.1 < p.2$.
  obtain ⟨p, hp⟩ : ∃ p ∈ ivs, p.1 < p.2 := by
    contrapose! h;
    -- If all intervals in `ivs` have length zero, then `S` is a finite union of singletons, hence has measure zero.
    have h_finite : S ⊆ ivs.toFinset.image Prod.fst := by
      intro x hx; have := hS.2.2; simp_all +decide [ Set.subset_def ] ;
      grind;
    rw [ MeasureTheory.measure_mono_null h_finite ] ; norm_num;
    rw [ Set.Finite.measure_zero ] ; exact Set.toFinite _;
  refine' lt_of_lt_of_le _ ( le_csSup _ ⟨ p.1, p.2, le_of_lt hp.2, rfl ⟩ );
  · rw [ show S ∩ Icc p.1 p.2 = Icc p.1 p.2 from _ ];
    · norm_num [ hp.2.le ] ; linarith;
    · exact Set.inter_eq_right.mpr ( hS.2.2.symm ▸ Set.subset_iUnion₂_of_subset p hp.1 ( Set.Subset.refl _ ) );
  · exact ProductFree.disc_bddAbove hS.finite

/-- **Partition monotonicity (restricted form).** If `[c,d]` is left balanced w.r.t. `B` and
`[c,a1]` is the leftmost maximal balanced block from `c`, then the discrepancy of the restriction
`B ∩ [c,d]` is at most `d_B([c,a1])`. -/
lemma disc_inter_le (hB : IsClosed B) (hfin : volume B ≠ ⊤) {c d a1 : ℝ}
    (hJ : IsLeftBalanced B c d) (ha1 : IsBalanced B c a1)
    (hmax : ∀ b', IsBalanced B c b' → b' ≤ a1) :
    disc (B ∩ Icc c d) ≤ discOn B c a1 := by
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ c, c, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ a, b, hab, rfl ⟩;
    set a' := max a c
    set b' := min b d;
    by_cases h : a' ≤ b' <;> simp_all +decide [ Set.inter_assoc ];
    · have h_discOn_split : discOn B a' b' = discOn B c b' - discOn B c a' := by
        have h_discOn_split : discOn B c b' = discOn B c a' + discOn B a' b' := by
          apply discOn_add;
          · exact hB.measurableSet;
          · exact le_max_right _ _;
          · exact h;
        linarith;
      have h_discOn_le : discOn B c b' ≤ discOn B c a1 := by
        apply discOn_left_le_of_leftmost hB hfin hJ ha1 hmax;
        · exact le_trans ( le_max_right _ _ ) h;
        · exact min_le_right _ _;
      have h_discOn_nonneg : 0 ≤ discOn B c a' := by
        exact hJ.2 a' ( by aesop ) ( by aesop );
      rw [ show B ∩ ( Icc c d ∩ Icc a b ) = B ∩ Icc a' b' by ext; aesop ] ; linarith [ show discOn B a' b' = 2 * ( volume ( B ∩ Icc a' b' ) |> ENNReal.toReal ) - ( b' - a' ) from rfl, show b' - a' ≤ b - a from by cases max_cases a c <;> cases min_cases b d <;> linarith ] ;
    · rw [ show B ∩ ( Icc c d ∩ Icc a b ) = ∅ from Set.eq_empty_of_forall_notMem fun x hx => by cases max_cases a c <;> cases min_cases b d <;> linarith [ hx.2.1.1, hx.2.1.2, hx.2.2.1, hx.2.2.2 ] ] ; norm_num;
      exact add_nonneg ( by linarith [ ha1.1.2 a1 ( by linarith [ ha1.1.1 ] ) ( by linarith [ ha1.1.1 ] ) ] ) ( by linarith )

/-
**The discrepancy is unchanged by peeling the leftmost maximal left-balanced block**, when
that block has discrepancy strictly below `disc B`. Here `[sInf B, d]` is the maximal
left-balanced interval from `sInf B`, `[sInf B, a1]` its leftmost balanced block, and
`discOn B (sInf B) a1 < disc B`. Then `disc (B ∩ Ioi d) = disc B`.
-/
lemma disc_compl_eq {ivs : List (ℝ × ℝ)} (hBiu : IsIntervalUnion B ivs) (hne : ivs ≠ [])
    {d a1 : ℝ}
    (hJ : IsLeftBalanced B (sInf B) d)
    (hmaxlb : ∀ d', IsLeftBalanced B (sInf B) d' → d' ≤ d)
    (ha1 : IsBalanced B (sInf B) a1)
    (hmaxbal : ∀ b', IsBalanced B (sInf B) b' → b' ≤ a1)
    (hlt : discOn B (sInf B) a1 < disc B) :
    disc (B ∩ Ioi d) = disc B := by
  obtain ⟨ p, q, hp, hq, hsub, hbal, hval ⟩ := disc_attained hBiu hne;
  -- Claim `d < p`.
  have hdp : d < p := by
    by_contra hdp_le
    have hq_le_d : q ≤ d := by
      have h_union : IsLeftBalanced B (sInf B) (max d q) := by
        apply union_left_balanced (hBiu.isClosed.measurableSet) hJ hbal.1 (by
        linarith) (by
        linarith)
      generalize_proofs at *; (
      exact le_trans ( le_max_right _ _ ) ( hmaxlb _ h_union ))
    have h_subset : Icc p q ⊆ Icc (sInf B) d := by
      exact Set.Icc_subset_Icc hp hq_le_d
    have h_disc_le : discOn B p q ≤ discOn B (sInf B) a1 := by
      have h_disc_le : discOn B p q = discOn B (sInf B) q - discOn B (sInf B) p := by
        have h_disc_le : discOn B (sInf B) q = discOn B (sInf B) p + discOn B p q := by
          apply discOn_add;
          · exact hBiu.isClosed.measurableSet;
          · linarith;
          · linarith
        generalize_proofs at *; (
        linarith)
      generalize_proofs at *; (
      linarith [discOn_left_le_of_leftmost hBiu.isClosed hBiu.finite hJ ha1 hmaxbal q (by linarith) (by linarith), show 0 ≤ discOn B (sInf B) p from hJ.2 p (by linarith) (by linarith)])
    linarith [hlt]
  generalize_proofs at *; (
  -- Since `d < p`, `Icc p q ⊆ Ioi d` (any `x ∈ Icc p q` has `x ≥ p > d`). Therefore `B' ∩ Icc p q = (B ∩ Ioi d) ∩ Icc p q = B ∩ (Ioi d ∩ Icc p q) = B ∩ Icc p q` (since `Icc p q ⊆ Ioi d`). Hence `discOn B' p q = discOn B p q = disc B`.
  have h_disc_eq : discOn (B ∩ Ioi d) p q = discOn B p q := by
    have h_disc_eq : B ∩ Ioi d ∩ Icc p q = B ∩ Icc p q := by
      grind;
    unfold discOn; aesop;
  refine' le_antisymm _ _ <;> simp_all +decide [ disc ];
  · refine' csSup_le _ _ <;> norm_num +zetaDelta at *;
    · exact ⟨ _, ⟨ p, q, hq, rfl ⟩ ⟩;
    · rintro b x y hxy rfl;
      refine' le_trans _ ( le_csSup _ ⟨ x, y, hxy, rfl ⟩ );
      · gcongr;
        · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B ∩ Icc x y ⊆ B from Set.inter_subset_left ) ) ( hBiu.finite |> fun h => lt_top_iff_ne_top.mpr h ) );
        · exact Set.inter_subset_left;
      · exact disc_bddAbove ( hBiu.finite );
  · refine' le_csSup _ _;
    · refine' ⟨ 2 * ( volume B ).toReal, fun r hr => _ ⟩ ; rcases hr with ⟨ a, b, hab, rfl ⟩ ; refine' sub_le_iff_le_add'.mpr _ ; ring_nf;
      refine' le_trans ( mul_le_mul_of_nonneg_right ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show B ∩ Ioi d ∩ Icc a b ⊆ B from fun x hx => hx.1.1 ) zero_le_two ) _;
      · exact hBiu.finite;
      · linarith;
    · exact ⟨ p, q, hq, h_disc_eq.symm ⟩)

end ProductFree