import RequestProject.LeftBalancedDecomp

/-!
# Corollary `key_bound`

This file proves the paper's Corollary `key_bound`, the central tool in the proof of
`offdiagonal_main2`. Given a left-balanced interval `[a,b]` w.r.t. a closed set `A` with
`d_A([a,b]) ≥ d(B)`, the sumset `(A ∩ [a,b]) + B`, restricted to
`[a + min B, a + max B + d_R(B)]`, has measure at least `2|B|`.

The proof decomposes `B` greedily into maximal left-balanced blocks (`peel`), applies
`main_step_sums_left` to each block, and combines the resulting intervals, which are disjoint by
maximality.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A B : Set ℝ}

/-
Discrepancy is monotone under inclusion (for finite-measure supersets).
-/
lemma disc_mono {A B : Set ℝ} (hAB : A ⊆ B) (hfin : volume B ≠ ⊤) : disc A ≤ disc B := by
  -- Every $r \in S_A$ satisfies $r \leq disc B$.
  have h_le_discB : ∀ r ∈ {r : ℝ | ∃ a b : ℝ, a ≤ b ∧ r = 2 * (volume (A ∩ Icc a b)).toReal - (b - a)}, r ≤ disc B := by
    intro r hr
    obtain ⟨a, b, hab, hr_eq⟩ := hr
    have h_le_discB : r ≤ 2 * (volume (B ∩ Icc a b)).toReal - (b - a) := by
      rw [ hr_eq ];
      gcongr;
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
    exact le_trans h_le_discB ( le_csSup ( by exact disc_bddAbove hfin ) ⟨ a, b, hab, rfl ⟩ );
  exact csSup_le ⟨ _, ⟨ 0, 0, by norm_num, rfl ⟩ ⟩ h_le_discB

/-
`discOn B x (sSup B) ≤ d_R(B)` for `x ≤ sSup B`.
-/
lemma discOn_le_discR (hfin : volume B ≠ ⊤) {x : ℝ} (hx : x ≤ sSup B) :
    discOn B x (sSup B) ≤ discR B := by
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume B |> ENNReal.toReal ), fun r hr => _ ⟩;
    obtain ⟨ y, hy, rfl ⟩ := hr; exact sub_le_iff_le_add'.mpr ( by linarith [ show ( volume ( B ∩ Icc y ( sSup B ) ) |> ENNReal.toReal ) ≤ ( volume B |> ENNReal.toReal ) from ENNReal.toReal_mono hfin <| MeasureTheory.measure_mono <| Set.inter_subset_left ] ) ;
  · exact ⟨ x, hx, rfl ⟩

/-
`d_R` is monotone under inclusion when the maximum is preserved.
-/
lemma discR_mono {B B' : Set ℝ} (hsub : B' ⊆ B) (hsup : sSup B' = sSup B)
    (hfin : volume B ≠ ⊤) : discR B' ≤ discR B := by
  refine' csSup_le _ _ <;> norm_num;
  · exact ⟨ _, ⟨ sSup B', le_rfl, rfl ⟩ ⟩;
  · intro b x hx hb
    have h_discOn : discOn B' x (sSup B') ≤ discOn B x (sSup B) := by
      simp_all +decide [ discOn ];
      gcongr;
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hfin ) );
    exact hb ▸ h_discOn.trans ( discOn_le_discR hfin ( by linarith ) )

/-
**Disjointness of the greedy blocks.** If `[sInf B, d]` is a maximal left-balanced interval
(so no left-balanced interval from `sInf B` extends past `d`), and `(d, m) ∩ B = ∅` with `d < m`,
then `sInf B + 2|B ∩ [sInf B, d]| < m`.
-/
lemma peel_gap (hfin : volume B ≠ ⊤) {d m : ℝ}
    (hdd : IsLeftBalanced B (sInf B) d)
    (hmax : ∀ d', IsLeftBalanced B (sInf B) d' → d' ≤ d)
    (hgap : B ∩ Ioo d m = ∅) (hm : d < m) :
    sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal < m := by
  contrapose! hmax;
  refine' ⟨ m, ⟨ by linarith [ hdd.1, show sInf B ≤ d from hdd.1 ], _ ⟩, hm ⟩;
  intro c hc₁ hc₂;
  by_cases hc₃ : c ≤ d;
  · exact hdd.2 c hc₁ hc₃;
  · have h_volume_zero : volume (B ∩ Set.Ioc d c) = 0 := by
      have h_volume_zero : B ∩ Set.Ioc d c ⊆ {c} := by
        intro x hx; cases eq_or_lt_of_le hx.2.2 <;> simp_all +decide [ Set.ext_iff ] ;
        linarith [ hgap x hx.1 hx.2.1 ];
      exact MeasureTheory.measure_mono_null h_volume_zero ( by norm_num );
    have h_volume_eq : volume (B ∩ Set.Icc (sInf B) c) = volume (B ∩ Set.Icc (sInf B) d) := by
      rw [ ← MeasureTheory.measure_diff_null h_volume_zero ];
      congr with x ; simp +decide [ Set.mem_diff, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc ];
      grind;
    unfold discOn; norm_num [ h_volume_eq ] ; linarith;

/-
Two disjoint measurable subsets of a finite-measure set have total measure at most that of
the set (real-valued form).
-/
lemma measure_le_of_two_disjoint {S U V : Set ℝ} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUS : U ⊆ S) (hVS : V ⊆ S) (hd : Disjoint U V) (hSfin : volume S ≠ ⊤) :
    (volume U).toReal + (volume V).toReal ≤ (volume S).toReal := by
  rw [ ← ENNReal.toReal_add ];
  · gcongr;
    · assumption;
    · rw [ ← MeasureTheory.measure_union₀ ];
      · exact MeasureTheory.measure_mono ( Set.union_subset hUS hVS );
      · exact hV.nullMeasurableSet;
      · exact hd.aedisjoint;
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hUS ) ( lt_top_iff_ne_top.mpr hSfin ) );
  · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono hVS ) ( lt_top_iff_ne_top.mpr hSfin ) )

/-
**Corollary `key_bound` (left version), inductive step.** Given the statement for all
interval-unions with strictly fewer components (`IH`), it holds for `B`.
-/
set_option maxHeartbeats 1000000 in
lemma key_bound_step (A : Set ℝ) (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsLeftBalanced A a b) {B : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ []) (hdisc : disc B ≤ discOn A a b)
    (IH : ∀ (B' : Set ℝ) (ivs' : List (ℝ × ℝ)), ivs'.length < ivs.length →
      IsIntervalUnion B' ivs' → ivs' ≠ [] → disc B' ≤ discOn A a b →
      2 * (volume B').toReal ≤
        (volume (((A ∩ Icc a b) + B') ∩ Icc (a + sInf B') (a + sSup B' + discR B'))).toReal) :
    2 * (volume B).toReal ≤
      (volume (((A ∩ Icc a b) + B) ∩ Icc (a + sInf B) (a + sSup B + discR B))).toReal := by
  revert hdisc;
  intro hdisc
  set c := sInf B
  set M := sSup B
  set δ := discR B
  set S := ((A ∩ Icc a b) + B) ∩ Icc (a + c) (a + M + δ);
  -- Preliminaries:
  have hBcl := hB.isClosed
  have hBfin := hB.finite
  have hBcpt := hB.isCompact
  have hBnes := hB.nonempty hBne
  have hcM : c ≤ M := by
    exact le_trans ( csInf_le hBcpt.bddBelow hBnes.choose_spec ) ( le_csSup hBcpt.bddAbove hBnes.choose_spec )
  have hMc : M ∈ B := by
    exact hBcpt.sSup_mem hBnes
  have hMc' : c ∈ B := by
    exact hBcpt.sInf_mem hBnes
  have hB_subset_Ici_c : B ⊆ Ici c := by
    exact fun x hx => csInf_le hBcpt.bddBelow hx
  have ha_mem : a ∈ A ∩ Icc a b := by
    exact ⟨ left_balanced_left_mem hA hI hab, ⟨ le_rfl, hab.le ⟩ ⟩
  have hδ_nonneg : 0 ≤ δ := by
    exact discR_nonneg hBfin
  have hSfin : volume S ≠ ⊤ := by
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ Real.volume_Icc ] ) );
  -- Measure partition: $B = B₁ ∪ B'$ (since $B = (B ∩ Iic d) ∪ (B ∩ Ioi d)$ and $B ∩ Iic d = B₁$), the union disjoint ($Iic d$, $Ioi d$ disjoint). So $(volume B).toReal = (volume B₁).toReal + (volume B').toReal$ (both finite; $measure_union$ then $ENNReal.toReal_add$).
  obtain ⟨d, ivs', hd, hJlb, hmax, hB', hlen, hright⟩ := peel hB hBne hBcl
  set B₁ := B ∩ Icc c d
  set B' := B ∩ Ioi d
  have hB_eq : B = B₁ ∪ B' := by
    grind
  have hB_disjoint : Disjoint B₁ B' := by
    grind +splitImp
  have hB₁_finite : volume B₁ ≠ ⊤ := by
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B₁ ⊆ B from fun x hx => hx.1 ) ) ( lt_top_iff_ne_top.mpr hBfin ) )
  have hB'_finite : volume B' ≠ ⊤ := by
    exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B' ⊆ B from fun x hx => hx.1 ) ) ( lt_top_iff_ne_top.mpr hBfin ) )
  have hB_measure : (volume B).toReal = (volume B₁).toReal + (volume B').toReal := by
    rw [ hB_eq, MeasureTheory.measure_union hB_disjoint ];
    · rw [ ENNReal.toReal_add ] <;> norm_num [ hB₁_finite, hB'_finite ];
    · exact hBcl.measurableSet.inter measurableSet_Ioi;
  by_cases hivs' : ivs' = [];
  · -- Since $ivs' = []$, we have $B' = ∅$, so $B ⊆ Iic d$, $M ≤ d$, and $B = B₁$.
    have hB'_empty : B' = ∅ := by
      simpa [ hivs' ] using hB'.2.2
    have hM_le_d : M ≤ d := by
      exact le_of_not_gt fun h => hB'_empty.subset ⟨ hMc, h ⟩
    have hB_eq_B₁ : B = B₁ := by
      simpa [ hB'_empty ] using hB_eq;
    by_cases hcd : c < d;
    · -- By `main_step_sums_left`, $Icc (a+c) (a+c+2*(volume B₁).toReal) ⊆ (A ∩ Icc a b) + B₁$.
      have h_main_step : Icc (a + c) (a + c + 2 * (volume B₁).toReal) ⊆ (A ∩ Icc a b) + B₁ := by
        convert main_step_sums_left hA hBcl hAfin hBfin hab hcd hI hJlb _ using 1;
        exact hdisc;
      -- Since $B₁ = B$, we have $K ⊆ (A ∩ Icc a b) + B$.
      have hK_subset_S : Icc (a + c) (a + c + 2 * (volume B₁).toReal) ⊆ S := by
        have hδ_ge_discOn : δ ≥ discOn B c M := by
          exact discOn_le_discR hBfin hcM;
        have hδ_ge_discOn : δ ≥ 2 * (volume (B ∩ Icc c M)).toReal - (M - c) := by
          exact hδ_ge_discOn;
        rw [ show B ∩ Icc c M = B from ?_ ] at hδ_ge_discOn;
        · grind;
        · exact Set.inter_eq_left.mpr fun x hx => ⟨ hB_subset_Ici_c hx, le_csSup ( hBcpt.bddAbove ) hx ⟩;
      refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono hK_subset_S );
      · norm_num [ hB_measure, hB'_empty ];
      · exact hSfin;
    · -- Since $c = d$, we have $B₁ = B ∩ Icc c c ⊆ {c}$ has volume 0.
      have hB₁_zero : (volume B₁).toReal = 0 := by
        rw [ show B₁ = { c } from _ ];
        · norm_num;
        · grind;
      rw [ hB_eq_B₁, hB₁_zero ] ; norm_num;
  · -- Let $m := sInf B'$. By $hB'.sInf_eq$ and $hright$ (head of $ivs'$ in $ivs'$), $d < m$. Let $M' := sSup B'$.
    set m := sInf B'
    set M' := sSup B'
    have hm : d < m := by
      have := hB'.sInf_eq hivs';
      grind +locals
    have hM' : M' = M := by
      refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _;
      · exact hB'.nonempty hivs';
      · exact fun x hx => le_csSup ( hBcpt.bddAbove ) hx.1;
      · intro w hw;
        contrapose! hw;
        refine' csSup_le _ _;
        · exact hBnes;
        · intro x hx; by_cases hx' : x ≤ d <;> [ exact le_trans ( show x ≤ d by linarith ) ( show d ≤ w by linarith [ hw ( m ) ( show m ∈ B' from by
                                                                                                                                  exact hB'.isCompact.sInf_mem ( hB'.nonempty hivs' ) ) ] ) ; exact hw x ( show x ∈ B' from by
                                                                                                                                                                                  exact ⟨ hx, lt_of_not_ge hx' ⟩ ) ] ;
    have hdiscR_B' : discR B' ≤ δ := by
      apply discR_mono;
      · exact Set.inter_subset_left;
      · exact hM';
      · exact hBfin
    have hgap : B ∩ Ioo d m = ∅ := by
      exact Set.eq_empty_of_forall_notMem fun x hx => not_lt_of_ge ( csInf_le ( show BddBelow B' from hBcpt.bddBelow.mono <| Set.inter_subset_left ) <| show x ∈ B' from ⟨ hx.1, hx.2.1 ⟩ ) hx.2.2
    have hpeel_gap : c + 2 * (volume B₁).toReal < m := by
      apply peel_gap hBfin hJlb hmax hgap hm;
    by_cases hcd : c < d;
    · -- Let $U := Icc (a+c) (a+c+2*(volume B₁).toReal)$. By `main_step_sums_left`, $U ⊆ (A ∩ Icc a b) + B₁ ⊆ (A ∩ Icc a b) + B$. Also $U ⊆ Icc (a+c) (a+M+δ)$: $U$'s right end $a+c+2*(volume B₁).toReal < a+m$ (peel_gap) $≤ a+M+δ$ ($m ≤ M$, $δ ≥ 0$). So $U ⊆ S$.
      set U := Icc (a + c) (a + c + 2 * (volume B₁).toReal)
      have hU_subset_S : U ⊆ S := by
        have hU_subset_S : U ⊆ (A ∩ Icc a b) + B := by
          have hU_subset_S : U ⊆ (A ∩ Icc a b) + B₁ := by
            apply main_step_sums_left hA hBcl hAfin hBfin hab hcd hI hJlb hdisc;
          exact hU_subset_S.trans ( Set.add_subset_add_left <| Set.inter_subset_left );
        exact fun x hx => ⟨ hU_subset_S hx, ⟨ by linarith [ Set.mem_Icc.mp hx ], by linarith [ Set.mem_Icc.mp hx, show m ≤ M from hM'.symm ▸ csInf_le ( show BddBelow B' from hB'.isCompact.bddBelow ) ( show M' ∈ B' from hB'.isCompact.sSup_mem <| hB'.nonempty hivs' ) ] ⟩ ⟩;
      -- Let $V := ((A ∩ Icc a b) + B') ∩ Icc (a+m) (a+M+discR B')$. By IH, $2*(volume B').toReal ≤ (volume V).toReal$.
      set V := ((A ∩ Icc a b) + B') ∩ Icc (a + m) (a + M + discR B')
      have hV_subset_S : V ⊆ S := by
        simp +zetaDelta at *;
        constructor;
        · exact fun x hx => hx.1 |> fun hx' => by rcases hx' with ⟨ y, hy, z, hz, rfl ⟩ ; exact ⟨ y, hy, z, hB_eq.symm.subset <| Or.inr hz, rfl ⟩ ;
        · grind
      have hV_measure : 2 * (volume B').toReal ≤ (volume V).toReal := by
        convert IH B' ivs' hlen hB' hivs' _ using 1;
        · grind;
        · exact le_trans ( disc_mono ( show B' ⊆ B from fun x hx => hx.1 ) hBfin ) hdisc;
      -- $U$ and $V$ are disjoint: $U ⊆ Iic (a+c+2*(volume B₁).toReal)$ and $V ⊆ Ici (a+m)$ with $a+c+2*(volume B₁).toReal < a+m$.
      have hUV_disjoint : Disjoint U V := by
        exact Set.disjoint_left.mpr fun x hxU hxV => by linarith [ Set.mem_Icc.mp hxU, Set.mem_Icc.mp hxV.2 ] ;
      have hUV_measure : (volume U).toReal + (volume V).toReal ≤ (volume S).toReal := by
        apply_rules [ measure_le_of_two_disjoint ];
        · exact measurableSet_Icc;
        · refine' MeasurableSet.inter _ _;
          · have h_compact : IsCompact (A ∩ Icc a b + B') := by
              apply_rules [ IsCompact.add, CompactIccSpace.isCompact_Icc ];
              · exact CompactIccSpace.isCompact_Icc.inter_left hA;
              · exact hB'.isCompact;
            exact h_compact.measurableSet;
          · exact measurableSet_Icc;
      rw [ show volume U = ENNReal.ofReal ( 2 * ( volume B₁ |> ENNReal.toReal ) ) from ?_ ] at hUV_measure;
      · rw [ ENNReal.toReal_ofReal ] at hUV_measure <;> linarith [ show 0 ≤ ( volume B₁ |> ENNReal.toReal ) from ENNReal.toReal_nonneg ];
      · simp +zetaDelta at *;
    · -- Since $c = d$, we have $B₁ = B ∩ Icc c c = {c}$, so $(volume B₁).toReal = 0$.
      have hB₁_zero : (volume B₁).toReal = 0 := by
        rw [ show B₁ = { c } from _ ];
        · norm_num;
        · grind;
      have hIH : 2 * (volume B').toReal ≤ (volume ((A ∩ Icc a b + B') ∩ Icc (a + m) (a + M + discR B'))).toReal := by
        convert IH B' ivs' hlen hB' hivs' _ using 1;
        · grind +splitImp;
        · exact le_trans ( disc_mono ( show B' ⊆ B from fun x hx => hx.1 ) hBfin ) hdisc;
      refine' le_trans _ ( hIH.trans _ );
      · linarith;
      · refine' ENNReal.toReal_mono _ _;
        · exact hSfin;
        · refine' MeasureTheory.measure_mono _;
          simp +zetaDelta at *;
          constructor;
          · exact fun x hx => Set.add_subset_add ( Set.Subset.refl _ ) ( Set.inter_subset_left ) hx.1;
          · grind

/-- **Corollary `key_bound` (left version), auxiliary induction.** -/
lemma key_bound_aux (A : Set ℝ) (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsLeftBalanced A a b) :
    ∀ (n : ℕ) (B : Set ℝ) (ivs : List (ℝ × ℝ)), ivs.length = n → IsIntervalUnion B ivs →
      ivs ≠ [] → disc B ≤ discOn A a b →
      2 * (volume B).toReal ≤
        (volume (((A ∩ Icc a b) + B) ∩ Icc (a + sInf B) (a + sSup B + discR B))).toReal := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B ivs hn hB hBne hdisc
    subst hn
    exact key_bound_step A hA hAfin hab hI hB hBne hdisc
      (fun B' ivs' hlt hB' hne' hd' => ih ivs'.length hlt B' ivs' rfl hB' hne' hd')

/-- **Corollary `key_bound` (left version).** If `[a,b]` is left balanced w.r.t. a closed set `A`
with `a < b`, `B` is a nonempty finite union of finite closed intervals, and `d_A([a,b]) ≥ d(B)`,
then `|((A ∩ [a,b]) + B) ∩ [a + min B, a + max B + d_R(B)]| ≥ 2|B|`. -/
lemma key_bound_left (A : Set ℝ) {B : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsLeftBalanced A a b) (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hdisc : disc B ≤ discOn A a b) :
    2 * (volume B).toReal ≤
      (volume (((A ∩ Icc a b) + B) ∩ Icc (a + sInf B) (a + sSup B + discR B))).toReal :=
  key_bound_aux A hA hAfin hab hI ivs.length B ivs rfl hB hBne hdisc

end ProductFree