import RequestProject.OffdiagonalMain
import RequestProject.Partition
import RequestProject.Discrepancy

/-!
# The off-diagonal sumset inequality: the recursive case and the induction

This file completes the finite-union proof of Theorem `offdiagonal_main2` (the paper's Section 3):
for nonempty finite unions of finite closed intervals `A`, `B` with `d(A) = d(B)`,
`|A+B| ≥ 2|A| + 2|B| - d(A) - d(B)`.

The generic (first) case is `offdiagonal_case1` (in `OffdiagonalMain.lean`). Here we handle the
recursive (second) case (`offdiag_case2_left`) and assemble the induction on the number of
component intervals (`offdiagonal_main2_iu`).
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A B : Set ℝ}

/-
Restricting to a left-balanced interval keeps it left balanced: if `[c,d]` is left balanced
w.r.t. `B`, it is left balanced w.r.t. `B ∩ [c,d]`.
-/
lemma restrict_leftBalanced (hB : MeasurableSet B) {c d : ℝ} (hJ : IsLeftBalanced B c d) :
    IsLeftBalanced (B ∩ Icc c d) c d := by
  refine' ⟨ hJ.1, fun x hx₁ hx₂ => _ ⟩;
  refine' le_trans ( hJ.2 x hx₁ hx₂ ) _;
  unfold discOn; simp +decide [ *, Set.inter_assoc ] ;
  rw [ Set.inter_eq_self_of_subset_right ( Set.Icc_subset_Icc_right hx₂ ) ]

/-
**Off-diagonal sumset inequality, recursive case (peeling `B` from the left).**

Given `A`, `B` nonempty finite unions of finite closed intervals with `d(A) = d(B) > 0`, the
leftmost maximal balanced blocks `[sInf A, a1]` (of `A`) and `[sInf B, b1]` (of `B`), and the
orientation `d_B([sInf B,b1]) ≤ d_A([sInf A,a1])` with `d_B([sInf B,b1]) < d(B)`, the inequality
holds for `(A,B)`, using the inductive hypothesis on `A` together with `B` restricted to fewer
components.
-/
set_option maxHeartbeats 1000000 in
lemma offdiag_case2_left {ivsA ivsB : List (ℝ × ℝ)}
    (IH : ∀ (B' : Set ℝ) (ivsB' : List (ℝ × ℝ)), IsIntervalUnion B' ivsB' → ivsB' ≠ [] →
      ivsB'.length < ivsB.length → disc A = disc B' →
      2 * (volume A).toReal + 2 * (volume B').toReal - disc A - disc B'
        ≤ (volume (A + B')).toReal)
    (hA : IsIntervalUnion A ivsA) (hB : IsIntervalUnion B ivsB) (hAne : ivsA ≠ [])
    (hBne : ivsB ≠ []) (hdAB : disc A = disc B) (hdpos : 0 < disc A)
    {a1 : ℝ} (ha1bal : IsBalanced A (sInf A) a1)
    {b1 : ℝ} (hb1bal : IsBalanced B (sInf B) b1) (hb1max : ∀ b', IsBalanced B (sInf B) b' → b' ≤ b1)
    (horient1 : discOn B (sInf B) b1 ≤ discOn A (sInf A) a1)
    (horient2 : discOn B (sInf B) b1 < disc B) :
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal := by
  -- Peel B from the left: obtain d, ivs' and corresponding properties.
  obtain ⟨d, ivs', hdge, hJlb, hmaxlb, hB'iu, hlen, hcomp⟩ := peel hB hBne hB.isClosed;
  obtain ⟨hJeq, hdiscB', hB'ne⟩ : B ∩ Iic d = B ∩ Icc (sInf B) d ∧ disc (B ∩ Ioi d) = disc B ∧ ivs' ≠ [] := by
    refine' ⟨ _, _, _ ⟩;
    · ext x; simp [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc];
      exact fun hx _ => csInf_le ( hB.isCompact.bddBelow ) hx;
    · apply disc_compl_eq hB hBne hJlb hmaxlb hb1bal hb1max horient2;
    · intro h; simp_all +decide ;
      have hB'_empty : B ∩ Ioi d = ∅ := by
        cases hB'iu ; aesop;
      have := ProductFree.disc_compl_eq hB hBne hJlb hmaxlb ( show IsBalanced B ( sInf B ) b1 from hb1bal ) ( show ∀ b', IsBalanced B ( sInf B ) b' → b' ≤ b1 from hb1max ) ( show discOn B ( sInf B ) b1 < disc B from horient2 ) ; simp_all +decide [ Set.ext_iff ] ;
      rw [ show B ∩ Ioi d = ∅ by ext x; aesop ] at this ; simp_all +decide [ disc ];
      rw [ show { r : ℝ | ∃ a b : ℝ, a ≤ b ∧ r = a - b } = Set.Iic 0 from ?_ ] at this ; norm_num at this ; linarith [ hdpos ] ;
      exact Set.ext fun x => ⟨ fun ⟨ a, b, hab, hx ⟩ => hx ▸ sub_nonpos_of_le hab, fun hx => ⟨ x, 0, by linarith [ Set.mem_Iic.mp hx ], by ring ⟩ ⟩;
  obtain ⟨hsplit, hrec⟩ : (volume B).toReal = (volume (B ∩ Icc (sInf B) d)).toReal + (volume (B ∩ Ioi d)).toReal ∧ 2 * (volume A).toReal + 2 * (volume (B ∩ Ioi d)).toReal - disc A - disc (B ∩ Ioi d) ≤ (volume (A + (B ∩ Ioi d))).toReal := by
    apply And.intro;
    · rw [ ← hJeq, ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
      · rw [ ← Set.inter_union_distrib_left, Set.Iic_union_Ioi, Set.inter_univ ];
      · grind;
      · exact hB'iu.isClosed.measurableSet;
      · have hB_finite : volume B ≠ ⊤ := by
          exact hB.finite;
        exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hB_finite ) );
      · exact hB'iu.finite;
    · exact IH _ _ hB'iu hB'ne hlen ( by linarith );
  by_cases hJpos : 0 < (volume (B ∩ Icc (sInf B) d)).toReal;
  · obtain ⟨hsd, hJiu, hdiscJpos, hdiscJle⟩ : sInf B < d ∧ IsIntervalUnion (B ∩ Icc (sInf B) d) (ivsB.filter (fun p => decide (p.2 ≤ d))) ∧ 0 < disc (B ∩ Icc (sInf B) d) ∧ disc (B ∩ Icc (sInf B) d) ≤ discOn A (sInf A) a1 := by
      refine' ⟨ lt_of_le_of_ne hdge _, _, _, _ ⟩;
      · grind +suggestions;
      · convert inter_Iic_of_clean hB _ using 1;
        · exact hJeq.symm;
        · exact cleanRight_of_maximal hB hB.finite hJlb hmaxlb;
      · apply iu_disc_pos;
        convert inter_Iic_of_clean hB ( cleanRight_of_maximal hB hB.finite hJlb hmaxlb ) using 1;
        · exact hJeq.symm;
        · exact hJpos;
      · refine' le_trans _ horient1;
        apply_rules [ disc_inter_le ];
        · exact hB.isClosed;
        · exact hB.finite;
    obtain ⟨hKsub, hKvol⟩ : Icc (sInf A + sInf B) (sInf A + sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal) ⊆ (A ∩ Icc (sInf A) a1) + (B ∩ Icc (sInf B) d) ∧ (volume (Icc (sInf A + sInf B) (sInf A + sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal))).toReal = 2 * (volume (B ∩ Icc (sInf B) d)).toReal := by
      have := main_step_sums_left ( hA.isClosed ) ( hJiu.isClosed ) ( hA.finite ) ( hJiu.finite ) ( show sInf A < a1 from ?_ ) ( show sInf B < d from hsd ) ( ha1bal.1 ) ( restrict_leftBalanced ( hB.isClosed.measurableSet ) hJlb ) hdiscJle;
      · simp_all +decide [ Set.inter_assoc ];
      · by_cases ha1eq : a1 = sInf A;
        · simp_all +decide [ discOn ];
          rw [ MeasureTheory.measure_mono_null ( show A ∩ { sInf A } ⊆ { sInf A } by aesop_cat ) ( MeasureTheory.measure_singleton _ ) ] at hdiscJle ; norm_num at hdiscJle ; linarith;
        · exact lt_of_le_of_ne ( ha1bal.1.1 ) ( Ne.symm ha1eq );
    obtain ⟨hgapfin, hKsub0⟩ : sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal < sInf (B ∩ Ioi d) ∧ Icc (sInf A + sInf B) (sInf A + sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal) ⊆ A + B := by
      apply And.intro;
      · apply ProductFree.peel_gap hB.finite hJlb hmaxlb;
        · exact Set.eq_empty_of_forall_notMem fun x hx => hx.2.2.not_ge <| csInf_le ( hB'iu.isCompact.bddBelow ) <| by aesop;
        · have := hB'iu.isCompact.sInf_mem ( hB'iu.nonempty hB'ne ) ; simp_all +decide [ Set.subset_def ] ;
      · exact hKsub.trans ( Set.add_subset_add ( Set.inter_subset_left ) ( Set.inter_subset_left ) );
    have hdisjoint : Disjoint (Icc (sInf A + sInf B) (sInf A + sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal)) (A + (B ∩ Ioi d)) := by
      rw [ Set.disjoint_left ];
      simp +zetaDelta at *;
      intro x hx₁ hx₂ hx₃; obtain ⟨ a, ha, b, hb, rfl ⟩ := hx₃; linarith [ show sInf A ≤ a from csInf_le ( show BddBelow A from hA.isCompact.bddBelow ) ha, show sInf ( B ∩ Ioi d ) ≤ b from csInf_le ( show BddBelow ( B ∩ Ioi d ) from hB'iu.isCompact.bddBelow ) hb ] ;
    have hmeasure : (volume (Icc (sInf A + sInf B) (sInf A + sInf B + 2 * (volume (B ∩ Icc (sInf B) d)).toReal))).toReal + (volume (A + (B ∩ Ioi d))).toReal ≤ (volume (A + B)).toReal := by
      convert measure_le_of_two_disjoint _ _ _ _ _ _ using 1;
      any_goals exact hA.isCompact.add hB.isCompact |> IsCompact.measure_lt_top |> ne_of_lt;
      · exact measurableSet_Icc;
      · have h_compact : IsCompact (A + (B ∩ Ioi d)) := by
          exact IsCompact.add ( hA.isCompact ) ( hB'iu.isCompact );
        exact h_compact.measurableSet;
      · exact hKsub0;
      · exact Set.add_subset_add Set.Subset.rfl ( Set.inter_subset_left );
      · exact hdisjoint;
    linarith;
  · have hvolumeB' : (volume (A + (B ∩ Ioi d))).toReal ≤ (volume (A + B)).toReal := by
      gcongr;
      · have h_compact : IsCompact (A + B) := by
          exact IsCompact.add ( hA.isCompact ) ( hB.isCompact );
        exact h_compact.measure_lt_top.ne;
      · exact Set.inter_subset_left;
    linarith

/-
Reflection: the leftmost maximal balanced block of `-A` is the reflection of the rightmost
maximal balanced block `[ak, sSup A]` of `A`, with the same discrepancy.
-/
lemma neg_leftmost {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion A ivs) (hne : ivs ≠ []) {ak : ℝ}
    (hbal : IsBalanced A ak (sSup A)) (hmax : ∀ a', IsBalanced A a' (sSup A) → ak ≤ a') :
    IsBalanced (-A) (sInf (-A)) (-ak) ∧
    (∀ b', IsBalanced (-A) (sInf (-A)) b' → b' ≤ -ak) ∧
    discOn (-A) (sInf (-A)) (-ak) = discOn A ak (sSup A) := by
  -- Apply the reflection lemma to get the balanced property for -A.
  have h_balanced_neg : IsBalanced (-A) (-sSup A) (-ak) := by
    convert isBalanced_reflect_sub (x := 0) hbal using 1;
    · aesop;
    · ring;
    · ring;
  refine' ⟨ _, _, _ ⟩;
  · convert h_balanced_neg using 1;
    norm_num;
  · intro b' hb'
    have hb'_neg : IsBalanced A (-b') (sSup A) := by
      convert isBalanced_reflect_sub 0 hb' using 1 ; ext ; simp +decide [ Set.mem_image ] ; ring;
      simp +decide [ Real.sInf_def, Real.sSup_def ]
    have hb'_le : ak ≤ -b' := by
      exact hmax _ hb'_neg
    linarith [hb'_le];
  · convert discOn_neg A ak ( sSup A ) using 1;
    norm_num

/-
The sumset measure is invariant under reflecting both sets.
-/
lemma sumset_measure_neg (A B : Set ℝ) :
    (volume ((-A) + (-B))).toReal = (volume (A + B)).toReal := by
  rw [ show -A + -B = - ( A + B ) by ext; simp +decide [ add_comm ] ];
  exact congr_arg _ (MeasureTheory.Measure.measure_neg _ _)

/-- The conclusion is invariant under reflecting both sets in the origin. -/
lemma concl_neg_iff (A B : Set ℝ) :
    (2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal) ↔
    (2 * (volume (-A)).toReal + 2 * (volume (-B)).toReal - disc (-A) - disc (-B)
      ≤ (volume ((-A) + (-B))).toReal) := by
  rw [sumset_measure_neg, disc_neg, disc_neg, MeasureTheory.Measure.measure_neg,
    MeasureTheory.Measure.measure_neg]

set_option maxHeartbeats 1000000 in
/-- **Off-diagonal sumset inequality, recursive case (peeling `B` from the right).** The
reflection of `offdiag_case2_left`: peels `B`'s rightmost maximal balanced block. -/
lemma offdiag_case2_right {ivsA ivsB : List (ℝ × ℝ)}
    (IH : ∀ (B' : Set ℝ) (ivsB' : List (ℝ × ℝ)), IsIntervalUnion B' ivsB' → ivsB' ≠ [] →
      ivsB'.length < ivsB.length → disc A = disc B' →
      2 * (volume A).toReal + 2 * (volume B').toReal - disc A - disc B'
        ≤ (volume (A + B')).toReal)
    (hA : IsIntervalUnion A ivsA) (hB : IsIntervalUnion B ivsB) (hAne : ivsA ≠ [])
    (hBne : ivsB ≠ []) (hdAB : disc A = disc B) (hdpos : 0 < disc A)
    {ak : ℝ} (hakbal : IsBalanced A ak (sSup A))
    {bl : ℝ} (hblbal : IsBalanced B bl (sSup B)) (hblmax : ∀ a', IsBalanced B a' (sSup B) → bl ≤ a')
    (horient1 : discOn B bl (sSup B) ≤ discOn A ak (sSup A))
    (horient2 : discOn B bl (sSup B) < disc B) :
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal := by
  have := @offdiag_case2_left;
  contrapose! this;
  refine' ⟨ -A, -B, ivsA.reverse.map fun p => ( -p.2, -p.1 ), ivsB.reverse.map fun p => ( -p.2, -p.1 ), _, _, _, _, _ ⟩ <;> norm_num [ neg_neg ];
  · intro B' ivsB' hB' hB'ne hB'len hB'disc; specialize IH ( -B' ) ( ivsB'.reverse.map fun p => ( -p.2, -p.1 ) ) ; simp_all +decide [ IsIntervalUnion.neg ] ;
    convert IH _ _ using 1;
    · rw [ ← disc_neg, ← sumset_measure_neg ] ; ring;
      rw [ neg_neg, add_comm ];
    · convert hB'.neg using 1;
      rw [ List.map_reverse ];
    · grind +suggestions;
  · convert hA.neg using 1;
    rw [ List.map_reverse ];
  · convert hB.neg using 1;
    rw [ List.map_reverse ];
  · assumption;
  · refine' ⟨ hBne, _, _, _ ⟩;
    · rw [ disc_neg, disc_neg, hdAB ];
    · rw [ disc_neg ] ; linarith;
    · refine' ⟨ -ak, _, -bl, _, _, _, _ ⟩;
      · convert isBalanced_reflect_sub ( 0 : ℝ ) hakbal using 1 ; norm_num; all_goals ring;
      · convert isBalanced_reflect_sub ( 0 : ℝ ) hblbal using 1 ; norm_num; all_goals ring;
      · intro b' hb'bal; have := neg_leftmost hB hBne hblbal hblmax; aesop;
      · convert horient1 using 1;
        · convert discOn_neg B bl ( sSup B ) using 1;
        · convert discOn_neg A ak ( sSup A ) using 1;
      · rw [ discOn_neg, disc_neg, disc_neg ];
        exact ⟨ horient2, by rw [ sumset_measure_neg ] ; linarith ⟩

/-- Swapping the two sets: `conclusion B A → conclusion A B`. -/
lemma conclusion_swap {A B : Set ℝ}
    (h : 2 * (volume B).toReal + 2 * (volume A).toReal - disc B - disc A ≤ (volume (B + A)).toReal) :
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal := by
  rw [show A + B = B + A from add_comm A B]; linarith

/-- **Case-2 dispatch.** Given the leftmost/rightmost maximal balanced data of `A` and `B`, the
inductive hypotheses on each side, and the failure of the "generic" case, one of the four
symmetric recursive cases applies. -/
lemma offdiag_dispatch {A B : Set ℝ} {ivsA ivsB : List (ℝ × ℝ)}
    (ihAB : ∀ (B' : Set ℝ) (ivsB' : List (ℝ × ℝ)), IsIntervalUnion B' ivsB' → ivsB' ≠ [] →
      ivsB'.length < ivsB.length → disc A = disc B' →
      2 * (volume A).toReal + 2 * (volume B').toReal - disc A - disc B' ≤ (volume (A + B')).toReal)
    (ihBA : ∀ (A' : Set ℝ) (ivsA' : List (ℝ × ℝ)), IsIntervalUnion A' ivsA' → ivsA' ≠ [] →
      ivsA'.length < ivsA.length → disc B = disc A' →
      2 * (volume B).toReal + 2 * (volume A').toReal - disc B - disc A' ≤ (volume (B + A')).toReal)
    (hA : IsIntervalUnion A ivsA) (hB : IsIntervalUnion B ivsB) (hAne : ivsA ≠ [])
    (hBne : ivsB ≠ []) (hdAB : disc A = disc B) (hdpos : 0 < disc A)
    {a1 : ℝ} (ha1bal : IsBalanced A (sInf A) a1) (ha1max : ∀ b', IsBalanced A (sInf A) b' → b' ≤ a1)
    {ak : ℝ} (hakbal : IsBalanced A ak (sSup A)) (hakmax : ∀ a', IsBalanced A a' (sSup A) → ak ≤ a')
    {b1 : ℝ} (hb1bal : IsBalanced B (sInf B) b1) (hb1max : ∀ b', IsBalanced B (sInf B) b' → b' ≤ b1)
    {bl : ℝ} (hblbal : IsBalanced B bl (sSup B)) (hblmax : ∀ a', IsBalanced B a' (sSup B) → bl ≤ a')
    (hAl : discOn A (sInf A) a1 ≤ disc A) (hAr : discOn A ak (sSup A) ≤ disc A)
    (hBl : discOn B (sInf B) b1 ≤ disc B) (hBr : discOn B bl (sSup B) ≤ disc B)
    (hnc1 : ¬(discOn A (sInf A) a1 = disc A ∧ discOn A ak (sSup A) = disc A ∧
      discOn B (sInf B) b1 = disc B ∧ discOn B bl (sSup B) = disc B)) :
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal := by
  have LAB : ∀ (_ : discOn B (sInf B) b1 ≤ discOn A (sInf A) a1)
      (_ : discOn B (sInf B) b1 < disc B),
      2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal :=
    fun h1 h2 => offdiag_case2_left ihAB hA hB hAne hBne hdAB hdpos ha1bal hb1bal hb1max h1 h2
  have RAB : ∀ (_ : discOn B bl (sSup B) ≤ discOn A ak (sSup A))
      (_ : discOn B bl (sSup B) < disc B),
      2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal :=
    fun h1 h2 => offdiag_case2_right ihAB hA hB hAne hBne hdAB hdpos hakbal hblbal hblmax h1 h2
  have LBA : ∀ (_ : discOn A (sInf A) a1 ≤ discOn B (sInf B) b1)
      (_ : discOn A (sInf A) a1 < disc A),
      2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal :=
    fun h1 h2 => conclusion_swap
      (offdiag_case2_left ihBA hB hA hBne hAne hdAB.symm (hdAB ▸ hdpos) hb1bal ha1bal ha1max h1 h2)
  have RBA : ∀ (_ : discOn A ak (sSup A) ≤ discOn B bl (sSup B))
      (_ : discOn A ak (sSup A) < disc A),
      2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal :=
    fun h1 h2 => conclusion_swap
      (offdiag_case2_right ihBA hB hA hBne hAne hdAB.symm (hdAB ▸ hdpos) hblbal hakbal hakmax h1 h2)
  rcases le_total (discOn B (sInf B) b1) (discOn A (sInf A) a1) with hL | hL
  · rcases le_total (discOn B bl (sSup B)) (discOn A ak (sSup A)) with hR | hR
    · by_cases h : discOn B (sInf B) b1 < disc B
      · exact LAB hL h
      · push_neg at h
        refine RAB hR ?_
        by_contra hbr; push_neg at hbr
        exact hnc1 ⟨le_antisymm hAl (by linarith), le_antisymm hAr (by linarith),
          le_antisymm hBl (by linarith), le_antisymm hBr hbr⟩
    · by_cases h : discOn B (sInf B) b1 < disc B
      · exact LAB hL h
      · push_neg at h
        refine RBA hR ?_
        by_contra har; push_neg at har
        exact hnc1 ⟨le_antisymm hAl (by linarith), le_antisymm hAr har,
          le_antisymm hBl (by linarith), le_antisymm hBr (by linarith)⟩
  · rcases le_total (discOn B bl (sSup B)) (discOn A ak (sSup A)) with hR | hR
    · by_cases h : discOn A (sInf A) a1 < disc A
      · exact LBA hL h
      · push_neg at h
        refine RAB hR ?_
        by_contra hbr; push_neg at hbr
        exact hnc1 ⟨le_antisymm hAl (by linarith), le_antisymm hAr (by linarith),
          le_antisymm hBl (by linarith), le_antisymm hBr hbr⟩
    · by_cases h : discOn A (sInf A) a1 < disc A
      · exact LBA hL h
      · push_neg at h
        refine RBA hR ?_
        by_contra har; push_neg at har
        exact hnc1 ⟨le_antisymm hAl h, le_antisymm hAr har,
          le_antisymm hBl (by linarith), le_antisymm hBr (by linarith)⟩

/-- Auxiliary strong-induction statement for `offdiagonal_main2_iu`, indexed by the total number
of component intervals. -/
lemma offdiag_aux : ∀ (n : ℕ) (A B : Set ℝ) (ivsA ivsB : List (ℝ × ℝ)),
    IsIntervalUnion A ivsA → IsIntervalUnion B ivsB → ivsA ≠ [] → ivsB ≠ [] →
    disc A = disc B → ivsA.length + ivsB.length = n →
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro A B ivsA ivsB hA hB hAne hBne hdAB hn
  by_cases hd0 : disc A = 0
  · -- degenerate case: both sets have measure zero
    have hdB0 : disc B = 0 := hdAB ▸ hd0
    have hA0 : (volume A).toReal = 0 := by
      by_contra hne
      have := iu_disc_pos hA (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne))
      linarith
    have hB0 : (volume B).toReal = 0 := by
      by_contra hne
      have := iu_disc_pos hB (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne))
      linarith
    rw [hd0, hdB0, hA0, hB0]
    linarith [ENNReal.toReal_nonneg (a := volume (A + B))]
  · obtain ⟨a1, _, ha1bal, _, ha1max⟩ := leftmost_max_balanced hA hAne
    obtain ⟨ak, _, hakbal, _, hakmax⟩ := rightmost_max_balanced hA hAne
    obtain ⟨b1, _, hb1bal, _, hb1max⟩ := leftmost_max_balanced hB hBne
    obtain ⟨bl, _, hblbal, _, hblmax⟩ := rightmost_max_balanced hB hBne
    have hAl : discOn A (sInf A) a1 ≤ disc A := discOn_le_disc hA.finite ha1bal.1.1
    have hAr : discOn A ak (sSup A) ≤ disc A := discOn_le_disc hA.finite hakbal.1.1
    have hBl : discOn B (sInf B) b1 ≤ disc B := discOn_le_disc hB.finite hb1bal.1.1
    have hBr : discOn B bl (sSup B) ≤ disc B := discOn_le_disc hB.finite hblbal.1.1
    by_cases hc1 : discOn A (sInf A) a1 = disc A ∧ discOn A ak (sSup A) = disc A ∧
        discOn B (sInf B) b1 = disc B ∧ discOn B bl (sSup B) = disc B
    · apply offdiagonal_case1 hA hB hAne hBne ha1bal (by
        contrapose! hd0
        rw [← hc1.1, show a1 = sInf A from le_antisymm hd0 ha1bal.1.1]; norm_num [discOn]
        exact MeasureTheory.measure_mono_null (fun x hx => by aesop)
          (MeasureTheory.measure_singleton (sInf A)) |> fun h => h.symm ▸ by norm_num)
        hc1.1 hblbal (by
        refine lt_of_le_of_ne hblbal.1.1 (fun hbl_eq_sSup => hd0 ?_)
        have h0 : discOn B bl (sSup B) = 0 := by
          rw [hbl_eq_sSup]; simp only [discOn, sub_self]
          rw [MeasureTheory.measure_mono_null
            (show B ∩ Icc (sSup B) (sSup B) ⊆ {sSup B} from fun x hx => by aesop)
            (MeasureTheory.measure_singleton _)]; norm_num
        rw [hdAB]; rw [h0] at hc1; exact hc1.2.2.2.symm)
        hc1.2.2.2 hdAB
    · have hdpos : 0 < disc A := lt_of_le_of_ne (disc_nonneg hA.finite) (Ne.symm hd0)
      have ihAB : ∀ (B' : Set ℝ) (ivsB' : List (ℝ × ℝ)), IsIntervalUnion B' ivsB' → ivsB' ≠ [] →
          ivsB'.length < ivsB.length → disc A = disc B' →
          2 * (volume A).toReal + 2 * (volume B').toReal - disc A - disc B'
            ≤ (volume (A + B')).toReal :=
        fun B' ivsB' hB' hB'ne hB'lt hAB' =>
          ih (ivsA.length + ivsB'.length) (by omega) A B' ivsA ivsB' hA hB' hAne hB'ne hAB' rfl
      have ihBA : ∀ (A' : Set ℝ) (ivsA' : List (ℝ × ℝ)), IsIntervalUnion A' ivsA' → ivsA' ≠ [] →
          ivsA'.length < ivsA.length → disc B = disc A' →
          2 * (volume B).toReal + 2 * (volume A').toReal - disc B - disc A'
            ≤ (volume (B + A')).toReal :=
        fun A' ivsA' hA' hA'ne hA'lt hBA' =>
          ih (ivsB.length + ivsA'.length) (by omega) B A' ivsB ivsA' hB hA' hBne hA'ne hBA' rfl
      exact offdiag_dispatch ihAB ihBA hA hB hAne hBne hdAB hdpos ha1bal ha1max hakbal hakmax
        hb1bal hb1max hblbal hblmax hAl hAr hBl hBr hc1

/-- **Theorem `offdiagonal main2` (finite-union version).** For nonempty finite unions of finite
closed intervals `A`, `B` with `d(A) = d(B)`, `|A + B| ≥ 2|A| + 2|B| - d(A) - d(B)`. -/
theorem offdiagonal_main2_iu {A B : Set ℝ} {ivsA ivsB : List (ℝ × ℝ)}
    (hA : IsIntervalUnion A ivsA) (hB : IsIntervalUnion B ivsB)
    (hAne : ivsA ≠ []) (hBne : ivsB ≠ [])
    (hdAB : disc A = disc B) :
    2 * (volume A).toReal + 2 * (volume B).toReal - disc A - disc B ≤ (volume (A + B)).toReal :=
  offdiag_aux _ A B ivsA ivsB hA hB hAne hBne hdAB rfl

/-- **Theorem `main2` (finite-union version).** For a nonempty finite union of finite closed
intervals `A`, both `|A + A|` and `|A - A|` are at least `4|A| - 2 d(A)`. This is the special case
`B = A` (sumset) and `B = -A` (difference set) of `offdiagonal_main2_iu`. -/
theorem main2_iu {A : Set ℝ} {ivsA : List (ℝ × ℝ)} (hA : IsIntervalUnion A ivsA)
    (hAne : ivsA ≠ []) :
    4 * (volume A).toReal - 2 * disc A ≤ (volume (A + A)).toReal ∧
    4 * (volume A).toReal - 2 * disc A ≤ (volume (A - A)).toReal := by
  refine ⟨?_, ?_⟩
  · have h := offdiagonal_main2_iu hA hA hAne hAne rfl
    linarith
  · have h := offdiagonal_main2_iu hA hA.neg hAne (neg_ivs_ne_nil hAne) (disc_neg A).symm
    rw [show A - A = A + (-A) from sub_eq_add_neg A A]
    rw [MeasureTheory.Measure.measure_neg, disc_neg] at h
    linarith

end ProductFree