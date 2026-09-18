import RequestProject.Section4MZeroExact

/-!
# Section 4: toward Lemma `minterv`

This file develops the endpoint-discrepancy estimate used in both halves of the paper's Lemma
`minterv`.  Restricting `A` to `[α,β]`, its right discrepancy is bounded by `mMinus A β` plus
the distance from the restriction's maximum to `β`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A B : Set ℝ}

/-
The right discrepancy of a nonempty bounded restriction `B ⊆ A ∩ (-∞,β]` is controlled
by `mMinus A β`, with the expected correction for the position of `sSup B`.
-/
lemma discR_le_mMinus_add_gap (hAfin : volume A ≠ ⊤) (hBne : B.Nonempty)
    {β : ℝ} (hBsub : B ⊆ A ∩ Iic β) :
    discR B ≤ mMinus A β + β - sSup B := by
  -- By definition of `discR`, we know that for any $r$, $discOn B r (sSup B) \leq discOn A r β + (β - sSup B)$.
  have h_discR_le_discOn : ∀ r ≤ sSup B, discOn B r (sSup B) ≤ discOn A r β + (β - sSup B) := by
    intro r hr
    have hB_subset : B ∩ Icc r (sSup B) ⊆ A ∩ Icc r β := by
      exact fun x hx => ⟨ hBsub hx.1 |>.1, hx.2.1, hBsub hx.1 |>.2 ⟩
    have hB_subset : (volume (B ∩ Icc r (sSup B))).toReal ≤ (volume (A ∩ Icc r β)).toReal := by
      apply_rules [ ENNReal.toReal_mono, MeasureTheory.measure_mono ];
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
    unfold discOn; linarith;
  have h_discOn_le_mMinus : ∀ r ≤ β, discOn A r β ≤ mMinus A β := by
    intro r hr;
    apply le_csSup;
    · exact ⟨ disc A, by rintro x ⟨ r, hr, rfl ⟩ ; exact discOn_le_disc hAfin hr ⟩;
    · exact ⟨ r, hr, rfl ⟩;
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ sSup B, le_rfl, rfl ⟩ ⟩;
  · rintro _ ⟨ r, hr, rfl ⟩ ; linarith [ h_discR_le_discOn r hr, h_discOn_le_mMinus r ( le_trans hr ( csSup_le hBne fun x hx => hBsub hx |>.2 ) ) ] ;

/-
Sumset half of Lemma `minterv`, stated for the interval-union restriction `B` that is
used in the proof.
-/
lemma minterv_sum_core (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b α β : ℝ} (hab : a < b) (hI : IsLeftBalanced A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hBsub : B ⊆ A ∩ Icc α β) (hdisc : disc B ≤ discOn A a b) :
    2 * (volume B).toReal ≤
      (volume ((A + A) ∩ Icc (a + α) (a + β + mMinus A β))).toReal := by
  refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono _ );
  convert key_bound_left A hA hAfin hab hI hB hBne hdisc using 1;
  · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show ( A + A ) ∩ Icc ( a + α ) ( a + β + mMinus A β ) ⊆ Icc ( a + α ) ( a + β + mMinus A β ) from Set.inter_subset_right ) ) _ );
    simp +zetaDelta at *;
  · intro x hx;
    obtain ⟨ ⟨ y, z, hy, hz, rfl ⟩, hx ⟩ := hx;
    refine' ⟨ _, _, _ ⟩;
    · exact Set.add_mem_add z.1 ( hBsub hz |>.1 );
    · linarith [ Set.mem_Icc.mp z.2, Set.mem_Icc.mp ( hBsub hz |>.2 ) ];
    · linarith [ hx.2, show sSup B ≤ β from csSup_le ( Set.nonempty_of_mem hz ) fun x hx => hBsub hx |>.2.2, show discR B ≤ mMinus A β + β - sSup B from discR_le_mMinus_add_gap hAfin ( Set.nonempty_of_mem hz ) ( show B ⊆ A ∩ Iic β from fun x hx => ⟨ hBsub hx |>.1, hBsub hx |>.2.2 ⟩ ) ]

/-
Difference-set half of Lemma `minterv`, stated for the interval-union restriction `B` that
is used in the proof.
-/
lemma minterv_diff_core (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b α β : ℝ} (hab : a < b) (hI : IsRightBalanced A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hBsub : B ⊆ A ∩ Icc α β) (hdisc : disc B ≤ discOn A a b) :
    2 * (volume B).toReal ≤
      (volume ((A - A) ∩ Icc (b - β - mMinus A β) (b - α))).toReal := by
  refine' le_trans _ ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono _ );
  convert key_bound_right A hA hAfin hab hI ( hB.neg ) ( neg_ivs_ne_nil hBne ) ?_ using 1;
  · rw [ Measure.measure_neg ];
  · rw [ disc_neg ] ; aesop;
  · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
    exact Set.Icc ( b - β - mMinus A β ) ( b - α );
    · exact Set.inter_subset_right;
    · simp +zetaDelta at *;
  · intro x hx; simp_all +decide [ Set.mem_add, Set.mem_sub ] ;
    refine' ⟨ _, _, _ ⟩;
    · rcases hx.1 with ⟨ y, ⟨ hy₁, hy₂, hy₃ ⟩, z, hz₁, rfl ⟩ ; exact ⟨ y, hy₁, z, hBsub.1 hz₁, by ring ⟩;
    · have h_discR_le_mMinus : discR B ≤ mMinus A β + β - sSup B := by
        apply discR_le_mMinus_add_gap hAfin (by
        exact ⟨ _, hx.1.choose_spec.2.choose_spec.1 ⟩) (by
        exact fun x hx => ⟨ hBsub.1 hx, hBsub.2 hx |>.2 ⟩);
      linarith [ show discL ( -B ) = discR B from discR_neg_eq_discL ( -B ) ▸ by simp +decide [ neg_neg ] ];
    · grind +qlia

/-- Sumset half of the paper's Lemma `minterv` for a finite closed-interval restriction. -/
lemma minterv_sum (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b α β : ℝ} (hab : a < b) (hI : IsLeftBalanced A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion (A ∩ Icc α β) ivs)
    (hdisc : disc (A ∩ Icc α β) ≤ discOn A a b) :
    2 * (volume (A ∩ Icc α β)).toReal ≤
      (volume ((A + A) ∩ Icc (a + α) (a + β + mMinus A β))).toReal := by
  by_cases hne : ivs = []
  · subst ivs
    have hempty : A ∩ Icc α β = ∅ := by simpa [IsIntervalUnion] using hB.2.2
    simp [hempty]
  · exact minterv_sum_core hA hAfin hab hI hB hne (fun _ hx => ⟨hx.1, hx.2⟩) hdisc

/-- Difference-set half of the paper's Lemma `minterv` for a finite closed-interval
restriction. -/
lemma minterv_diff (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b α β : ℝ} (hab : a < b) (hI : IsRightBalanced A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion (A ∩ Icc α β) ivs)
    (hdisc : disc (A ∩ Icc α β) ≤ discOn A a b) :
    2 * (volume (A ∩ Icc α β)).toReal ≤
      (volume ((A - A) ∩ Icc (b - β - mMinus A β) (b - α))).toReal := by
  by_cases hne : ivs = []
  · subst ivs
    have hempty : A ∩ Icc α β = ∅ := by simpa [IsIntervalUnion] using hB.2.2
    simp [hempty]
  · exact minterv_diff_core hA hAfin hab hI hB hne (fun _ hx => ⟨hx.1, hx.2⟩) hdisc

/-- The zero-`mMinus` specialization of the sumset estimate. -/
lemma minterv_sum_core_of_mMinus_eq_zero (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b α β : ℝ} (hab : a < b) (hI : IsLeftBalanced A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hBsub : B ⊆ A ∩ Icc α β) (hdisc : disc B ≤ discOn A a b)
    (hm : mMinus A β = 0) :
    2 * (volume B).toReal ≤
      (volume ((A + A) ∩ Icc (a + α) (a + β))).toReal := by
  simpa [hm] using minterv_sum_core hA hAfin hab hI hB hBne hBsub hdisc

/-- The zero-`mMinus` specialization of the difference-set estimate. -/
lemma minterv_diff_core_of_mMinus_eq_zero (hA : IsClosed A) (hAfin : volume A ≠ ⊤)
    {a b α β : ℝ} (hab : a < b) (hI : IsRightBalanced A a b)
    {ivs : List (ℝ × ℝ)} (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hBsub : B ⊆ A ∩ Icc α β) (hdisc : disc B ≤ discOn A a b)
    (hm : mMinus A β = 0) :
    2 * (volume B).toReal ≤
      (volume ((A - A) ∩ Icc (b - β) (b - α))).toReal := by
  simpa [hm] using minterv_diff_core hA hAfin hab hI hB hBne hBsub hdisc

end ProductFree