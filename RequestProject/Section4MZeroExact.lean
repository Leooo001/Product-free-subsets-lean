import RequestProject.Section4MZero

/-!
# Section 4: Lemma `mzero`

This file closes the supremum/attainment step left after `mzero_core` and proves the paper's
Lemma `mzero` in a form suited to later applications.  The key auxiliary result says that
positivity of `mMinus A z` produces a positive-discrepancy left-balanced interval ending at `z`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-
Positivity of `mMinus` is witnessed by an actual interval (not necessarily a
maximizing one).
-/
lemma exists_discOn_pos_of_mMinus_pos {z : ℝ}
    (hpos : 0 < mMinus A z) :
    ∃ c ≤ z, 0 < discOn A c z := by
  contrapose! hpos;
  exact csSup_le ⟨ _, ⟨ z, le_rfl, rfl ⟩ ⟩ fun x hx => by obtain ⟨ c, hc, rfl ⟩ := hx; exact hpos c hc;

/-
If `mMinus A z` is positive, some nondegenerate left-balanced interval ending at `z`
has positive discrepancy.
-/
lemma exists_leftBalanced_of_mMinus_pos (hA : MeasurableSet A) (hfin : volume A ≠ ⊤)
    {z : ℝ} (hpos : 0 < mMinus A z) :
    ∃ r < z, IsLeftBalanced A r z ∧ 0 < discOn A r z := by
  -- By definition of $mMinus$, there exists some $c \leq z$ such that $discOn A c z > 0$.
  obtain ⟨c, hc₁, hc₂⟩ : ∃ c ≤ z, 0 < discOn A c z := by
    exact exists_discOn_pos_of_mMinus_pos hpos;
  -- By the continuity of $discOn A · z$ in its left endpoint, there exists a point $r$ in the interval $[c, z]$ where $discOn A r z$ is maximized.
  obtain ⟨r, hr⟩ : ∃ r ∈ Set.Icc c z, ∀ t ∈ Set.Icc c z, discOn A t z ≤ discOn A r z := by
    have h_cont : ContinuousOn (fun r => discOn A r z) (Set.Icc c z) := by
      have h_cont : ContinuousOn (fun r => discOn (-A) (-z) (-r)) (Set.Icc c z) := by
        have h_cont : ContinuousOn (fun r => discOn (-A) (-z) r) (Set.Icc (-z) (-c)) := by
          apply_rules [ Continuous.continuousOn, continuous_discOn_right ];
          aesop;
        exact h_cont.comp ( continuousOn_id.neg ) fun x hx => ⟨ by linarith [ hx.1, hx.2 ], by linarith [ hx.1, hx.2 ] ⟩;
      convert h_cont using 1;
      ext; rw [ discOn_neg ] ;
    exact ( IsCompact.exists_isMaxOn ( CompactIccSpace.isCompact_Icc ) ⟨ c, Set.left_mem_Icc.mpr hc₁ ⟩ h_cont );
  refine' ⟨ r, lt_of_le_of_ne hr.1.2 _, _, _ ⟩;
  · contrapose! hc₂; have := hr.2 c ⟨ by linarith, by linarith ⟩ ; simp_all +decide [ discOn ] ;
    convert hr c le_rfl hc₁ using 1 ; norm_num [ Set.inter_comm ];
    exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_singleton z ) |> fun h => h.symm ▸ by norm_num;
  · exact ⟨ hr.1.2, fun t ht₁ ht₂ => by linarith [ hr.2 t ⟨ by linarith [ hr.1.1 ], by linarith [ hr.1.2 ] ⟩, discOn_add hA ( by linarith [ hr.1.1, hr.1.2 ] : r ≤ t ) ( by linarith [ hr.1.1, hr.1.2 ] : t ≤ z ) ] ⟩;
  · linarith [ hr.2 c ⟨ le_rfl, hc₁ ⟩ ]

/-
Lemma `mzero` from the paper.  Here discrepancy-maximality is recorded by saying that
`[a,b]` is balanced and its discrepancy dominates the discrepancy of the restriction of `A`
to `[0,x+1]`.
-/
lemma mzero (hA : IsClosed A) (hAfin : volume A ≠ ⊤) (hsf : IsSumFree A)
    (hAnonneg : A ⊆ Ici 0)
    {a b x z : ℝ} (hab : a < b) (hzx : z ≤ x + 1)
    (hI : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hendpoint : a + z ∈ A ∨ b - z ∈ A) :
    mMinus A z = 0 := by
  refine' le_antisymm ( le_of_not_gt fun h => _ ) ( _ );
  · obtain ⟨ r, hr₁, hr₂ ⟩ := exists_leftBalanced_of_mMinus_pos hA.measurableSet hAfin h;
    -- By `mzero_core`, we have `a + z ∉ A` and `b - z ∉ A`.
    have h_core : a + z ∉ A ∧ b - z ∉ A := by
      apply mzero_core hA hAfin hsf hab hr₁ hI ⟨hr₂.1.1, hr₂.1.2⟩;
      · refine' le_trans _ hmax;
        apply disc_mono;
        · grind +qlia;
        · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( lt_top_iff_ne_top.mpr hAfin ) );
      · exact hr₂.2;
    tauto;
  · exact mMinus_nonneg hAfin z

end ProductFree