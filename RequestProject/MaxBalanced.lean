import RequestProject.LeftBalancedDecomp

/-!
# Maximal balanced intervals from a fixed left endpoint

For the induction proving `offdiagonal_main2` we need, for a finite union of finite closed
intervals `A`, the *leftmost* maximal balanced interval (the maximal balanced interval whose left
endpoint is `sInf A`) and, by reflection, the *rightmost* one.

The key existence step (`exists_max_balanced_from`) is the two-sided analogue of `exists_max_lb`:
for a closed set `A` of finite measure and a point `c`, there is a largest right endpoint `d ≥ c`
such that `[c,d]` is balanced with respect to `A`. The admissible right endpoints form a set that
is bounded above (right balancedness bounds `d - c ≤ 2|A|`), closed under binary maximum
(`union_balanced`), and topologically closed (continuity of `discOn` in the right endpoint), so it
attains its supremum.
-/

open MeasureTheory Set

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
**Existence of a largest balanced right endpoint.** For a closed set `A` of finite measure and
a point `c`, there is a largest `d ≥ c` such that `[c,d]` is balanced with respect to `A`.
-/
lemma exists_max_balanced_from (hfin : volume A ≠ ⊤) (c : ℝ) :
    ∃ d, c ≤ d ∧ IsBalanced A c d ∧ ∀ d', IsBalanced A c d' → d' ≤ d := by
  obtain ⟨d, hd⟩ : ∃ d, IsLUB {d' | IsBalanced A c d'} d := by
    refine' ⟨ _, isLUB_csSup _ _ ⟩;
    · refine' ⟨ c, _, _ ⟩;
      · constructor <;> norm_num [ IsLeftBalanced ];
        intro x hx₁ hx₂; rw [ le_antisymm hx₂ hx₁ ] ; unfold discOn; norm_num;
      · constructor <;> norm_num [ IsRightBalanced ];
        intro x hx₁ hx₂; rw [ le_antisymm hx₂ hx₁ ] ; unfold discOn; norm_num;
    · refine' ⟨ c + 2 * ( volume A |> ENNReal.toReal ), fun d' hd' => _ ⟩;
      have := hd'.2.2 c ( by linarith [ hd'.1.1 ] ) ( by linarith [ hd'.1.1 ] ) ; simp_all +decide [ discOn ];
      linarith [ show ( volume ( A ∩ Icc c d' ) |> ENNReal.toReal ) ≤ ( volume A |> ENNReal.toReal ) from ENNReal.toReal_mono ( by aesop ) ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ];
  have h_balanced : IsBalanced A c d := by
    have h_seq : ∃ seq : ℕ → ℝ, (∀ n, IsBalanced A c (seq n)) ∧ Filter.Tendsto seq Filter.atTop (nhds d) := by
      have h_seq : ∀ ε > 0, ∃ d' ∈ {d' | IsBalanced A c d'}, d - ε < d' ∧ d' ≤ d := by
        exact fun ε εpos => by rcases hd.exists_between ( show d - ε < d by linarith ) with ⟨ d', hd', hd'' ⟩ ; exact ⟨ d', hd', by linarith, by linarith ⟩ ;
      choose! seq hseq using h_seq;
      exact ⟨ fun n => seq ( 1 / ( n + 1 ) ), fun n => hseq _ ( by positivity ) |>.1, tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ hseq ( 1 / ( n + 1 ) ) ( by positivity ) ], by linarith [ hseq ( 1 / ( n + 1 ) ) ( by positivity ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
    obtain ⟨seq, hseq_balanced, hseq_tendsto⟩ := h_seq
    have h_left_balanced : ∀ x, c ≤ x → x ≤ d → 0 ≤ discOn A c x := by
      intros x hx_left hx_right
      by_cases hx_eq_d : x = d;
      · have h_left_balanced : Filter.Tendsto (fun n => discOn A c (seq n)) Filter.atTop (nhds (discOn A c d)) := by
          exact Continuous.continuousAt ( continuous_discOn_right A hfin c ) |> fun h => h.tendsto.comp hseq_tendsto;
        exact hx_eq_d.symm ▸ le_of_tendsto_of_tendsto' tendsto_const_nhds h_left_balanced fun n => hseq_balanced n |>.1.2 _ ( by linarith [ hseq_balanced n |>.1.1 ] ) ( by linarith [ hseq_balanced n |>.1.1 ] );
      · have h_seq_ge_x : ∀ᶠ n in Filter.atTop, x ≤ seq n := by
          exact hseq_tendsto.eventually ( le_mem_nhds <| lt_of_le_of_ne hx_right hx_eq_d );
        exact hseq_balanced ( Classical.choose ( Filter.eventually_atTop.mp h_seq_ge_x ) ) |>.1.2 x hx_left ( Classical.choose_spec ( Filter.eventually_atTop.mp h_seq_ge_x ) _ le_rfl )
    have h_right_balanced : ∀ x, c ≤ x → x ≤ d → 0 ≤ discOn A x d := by
      intro x hx₁ hx₂
      have h_seq_right_balanced : ∀ n, x ≤ seq n → 0 ≤ discOn A x (seq n) := by
        exact fun n hn => hseq_balanced n |>.2.2 x hx₁ hn;
      have h_seq_right_balanced : Filter.Tendsto (fun n => discOn A x (seq n)) Filter.atTop (nhds (discOn A x d)) := by
        exact Continuous.continuousAt ( continuous_discOn_right A hfin x ) |> fun h => h.tendsto.comp hseq_tendsto;
      by_cases h : x < d;
      · exact le_of_tendsto_of_tendsto tendsto_const_nhds h_seq_right_balanced ( Filter.eventually_atTop.mpr <| by rcases Metric.tendsto_atTop.mp hseq_tendsto ( d - x ) ( sub_pos.mpr h ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => by linarith [ abs_lt.mp ( hN n hn ), ‹∀ n, x ≤ seq n → 0 ≤ discOn A x ( seq n ) › n ( by linarith [ abs_lt.mp ( hN n hn ) ] ) ] ⟩ );
      · norm_num [ show x = d by linarith, discOn ]
    exact ⟨⟨by
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hseq_tendsto fun n => ( hseq_balanced n ).1.1, h_left_balanced⟩, ⟨by
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hseq_tendsto fun n => ( hseq_balanced n ).1.1, h_right_balanced⟩⟩;
  exact ⟨ d, h_balanced.1.1, h_balanced, fun d' hd' => hd.1 hd' ⟩

/-
**Cumulative discrepancy maximised at the leftmost block.** Let `[c,d]` be left balanced
w.r.t. `B`, and let `a1` be the right endpoint of the maximal balanced interval `[c,a1]` from
`c` (so `IsBalanced B c a1` and every balanced `[c,b']` has `b' ≤ a1`). Then for every
`x ∈ [c,d]`, `discOn B c x ≤ discOn B c a1`.

This is the clean form of the discrepancy monotonicity in the paper's `partition` lemma: the
cumulative discrepancy `x ↦ d_B([c,x])` over the maximal left-balanced interval `[c,d]` is
maximised at `a1`.
-/
lemma discOn_left_le_of_leftmost (hB : IsClosed B) (hfin : volume B ≠ ⊤) {c d a1 : ℝ}
    (hJ : IsLeftBalanced B c d) (ha1 : IsBalanced B c a1)
    (hmax : ∀ b', IsBalanced B c b' → b' ≤ a1) :
    ∀ x, c ≤ x → x ≤ d → discOn B c x ≤ discOn B c a1 := by
  intro x hx₁ hx₂;
  -- By `IsCompact.exists_isMaxOn` (with `isCompact_Icc` and `⟨c, left_mem_Icc.mpr hx₁⟩`) and continuity of `g` on `Icc c x`, obtain `xs ∈ Icc c x` with `hxs_max : ∀ y ∈ Icc c x, discOn B c y ≤ discOn B c xs`.
  obtain ⟨xs, hxs_mem, hxs_max⟩ : ∃ xs ∈ Set.Icc c x, ∀ y ∈ Set.Icc c x, discOn B c y ≤ discOn B c xs := by
    exact ( IsCompact.exists_isMaxOn ( CompactIccSpace.isCompact_Icc ) ⟨ c, Set.left_mem_Icc.mpr hx₁ ⟩ ( ProductFree.continuous_discOn_right B hfin c |> Continuous.continuousOn ) );
  -- By `IsBalanced`, we have `IsBalanced B c xs`.
  have hxs_balanced : IsBalanced B c xs := by
    constructor;
    · exact ⟨ by linarith [ hxs_mem.1 ], fun y hy₁ hy₂ => hJ.2 y ( by linarith [ hxs_mem.1 ] ) ( by linarith [ hxs_mem.2 ] ) ⟩;
    · constructor;
      · linarith [ hxs_mem.1 ];
      · intro y hy₁ hy₂;
        have := discOn_add ( hB.measurableSet ) hy₁ hy₂; linarith [ hxs_max y ⟨ hy₁, by linarith [ hxs_mem.2 ] ⟩ ] ;
  -- By `discOn_add`, we have `discOn B c a1 = discOn B c xs + discOn B xs a1`.
  have h_disc_add : discOn B c a1 = discOn B c xs + discOn B xs a1 := by
    apply discOn_add;
    · exact hB.measurableSet;
    · linarith [ hxs_mem.1 ];
    · exact hmax xs hxs_balanced;
  linarith [ hxs_max x ⟨ hx₁, le_rfl ⟩, ha1.2.2 xs ( by linarith [ hxs_mem.1 ] ) ( by linarith [ hxs_mem.2, hmax xs hxs_balanced ] ) ]

/-
**Leftmost maximal balanced interval.** A nonempty finite union of finite closed intervals
`B` has a maximal balanced interval `[sInf B, a1]` starting at its minimum, and this `a1` is the
largest right endpoint of a balanced interval from `sInf B`.
-/
lemma leftmost_max_balanced {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hne : ivs ≠ []) :
    ∃ a1, sInf B ≤ a1 ∧ IsBalanced B (sInf B) a1 ∧ IsMaximalBalanced B (sInf B) a1 ∧
      (∀ b', IsBalanced B (sInf B) b' → b' ≤ a1) := by
  -- By `exists_max_balanced_from`, there exists `a1` with `sInf B ≤ a1`, `IsBalanced B (sInf B) a1`, and `∀ b', IsBalanced B (sInf B) b' → b' ≤ a1`.
  obtain ⟨a1, ha1⟩ := exists_max_balanced_from (hB.finite) (sInf B)
  use a1
  simp_all +decide [ IsMaximalBalanced ];
  intro a' b' ha' hb' hbal'
  by_cases ha'_eq : a' = b';
  · constructor <;> linarith [ hbal'.1.1 ];
  · have h_a'_in_B : a' ∈ B := by
      apply left_balanced_left_mem (hB.isClosed) hbal'.1 (by
      exact lt_of_le_of_ne ( hbal'.1.1 ) ha'_eq);
    have h_a'_eq_sInf : a' = sInf B := by
      exact le_antisymm ha' ( csInf_le ( show BddBelow B from by
                                          exact ⟨ _, fun x hx => hB.subset_Icc hne hx |>.1 ⟩ ) h_a'_in_B );
    exact ⟨ h_a'_eq_sInf, by linarith [ ha1.2.2 b' ( by simpa only [ h_a'_eq_sInf ] using hbal' ) ] ⟩

/-
**Rightmost maximal balanced interval.** A nonempty finite union of finite closed intervals
`B` has a maximal balanced interval `[ak, sSup B]` ending at its maximum, and this `ak` is the
smallest left endpoint of a balanced interval ending at `sSup B`.
-/
lemma rightmost_max_balanced {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hne : ivs ≠ []) :
    ∃ ak, ak ≤ sSup B ∧ IsBalanced B ak (sSup B) ∧ IsMaximalBalanced B ak (sSup B) ∧
      (∀ a', IsBalanced B a' (sSup B) → ak ≤ a') := by
  have := leftmost_max_balanced ( show IsIntervalUnion ( -B ) ( List.map ( fun p => ( -p.2, -p.1 ) ) ivs.reverse ) from ?_ ) ?_;
  · obtain ⟨ a1, ha1 ⟩ := this;
    refine' ⟨ -a1, _, _, _, _ ⟩;
    · rw [ Real.sInf_neg ] at ha1 ; linarith;
    · convert isBalanced_reflect_sub ( x := 0 ) ha1.2.1 using 1;
      · ext; simp [Set.mem_image];
      · ring;
      · simp +decide [ Real.sInf_def, Real.sSup_def ];
    · constructor;
      · convert isBalanced_reflect_sub ( 0 : ℝ ) ha1.2.1 using 1;
        · ext; simp [Set.mem_image];
        · ring;
        · simp +decide [ Real.sInf_def, Real.sSup_def ];
      · intro a' b' ha' hb' hab'
        have h_neg : IsBalanced (-B) (-b') (-a') := by
          convert isBalanced_reflect_sub 0 hab' using 1;
          · norm_num [ Set.ext_iff ];
          · ring;
          · ring;
        have := ha1.2.2.1.2 ( -b' ) ( -a' ) ?_ ?_ h_neg <;> norm_num at *;
        · constructor <;> linarith;
        · linarith;
        · linarith;
    · intro a' ha'
      have h_neg : IsBalanced (-B) (-sSup B) (-a') := by
        convert isBalanced_reflect_sub 0 ha' using 1;
        · norm_num [ Set.ext_iff ];
        · ring;
        · ring;
      linarith [ ha1.2.2.2 ( -a' ) ( by simpa [ Real.sInf_neg ] using h_neg ) ];
  · obtain ⟨ h₁, h₂, h₃ ⟩ := hB;
    constructor;
    · grind;
    · simp_all +decide [ List.isChain_iff_getElem ];
      refine' ⟨ _, _ ⟩;
      · grind;
      · ext; simp [Set.mem_iUnion];
  · aesop

end ProductFree