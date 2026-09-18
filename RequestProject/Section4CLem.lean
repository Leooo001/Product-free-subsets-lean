import RequestProject.Section4ContradictionAux
import RequestProject.Section4MInterv
import RequestProject.Section4MZeroExact
import RequestProject.Section4Boost

/-!
# Section 4: the paper's Lemma `c lem`

This file formalizes the paper's Lemma `c lem`, the key input to the upper bound `y < 3 + s`.
With `y = x + 1 - a` and `s = b - a`, and `g` defined by the direct-discrepancy identity
`2 F(y-2) + (F(x-1) - F(a+1)) = y - 3 - g`, the lemma states that for every `c ∈ A` with
`c ≤ y - s - 2 = x - b - 1`,
`g ≥ |A ∩ [a + m_A^-(c), b]| - 2 (F(c+s) - F(c))`.

The proof packs three sumset pieces inside `[a+1, x-1]`:
* `(A+A) ∩ [a+1, a+c+m_A^-(c)]`  of mass `≥ 2 F(c)`      (Lemma `minterv` on `[1,c]`);
* the translate `c + (A ∩ [a+m_A^-(c), b])` of mass `= |A ∩ [a+m_A^-(c), b]|`;
* `(A+A) ∩ [b+c, x-1]`           of mass `≥ 2(F(y-2)-F(c+s))` (Lemma `minterv` on `[c+s,y-2]`).
These three are pairwise disjoint up to endpoints and disjoint from `A` (sum-freeness), so
their total plus `F(x-1) - F(a+1)` is at most the length `y - 3` of `[a+1,x-1]`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- The three-piece sumset lower bound feeding Lemma `c lem`: inside `[a+1,x-1]` the sumset
`A + A` collects at least `2 F(c) + |A ∩ [a+m_A^-(c),b]| + 2(F(y-2)-F(c+s))`. -/
lemma c_lem_sumset_lower
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x c : ℝ} (hab : a < b)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hx1A : x - 1 ∈ A)
    (haA : a ∈ A) (hcA : c ∈ A) (hc1 : 1 ≤ c) (hcx : c ≤ x - b - 1)
    (hmc : mMinus A c ≤ b - a) :
    2 * cum A c + (volume (A ∩ Icc (a + mMinus A c) b)).toReal
        + 2 * (cum A (x + 1 - a - 2) - cum A (c + (b - a)))
      ≤ (volume ((A + A) ∩ Icc (a + 1) (x - 1))).toReal := by
  have ha1 : 1 ≤ a := hmin.2 haA
  have hAfin : volume A ≠ ⊤ := hIU.isCompact.measure_lt_top.ne
  have hAnonneg : A ⊆ Ici 0 := fun z hz => le_trans zero_le_one (hmin.2 hz)
  have hmnn : 0 ≤ mMinus A c := mMinus_nonneg hAfin c
  have hcxp1 : c ≤ x + 1 := by linarith
  -- `mMinus A (y-2) = 0` since `a + (y-2) = x - 1 ∈ A`.
  have hmz : mMinus A (x + 1 - a - 2) = 0 := by
    refine mzero hIU.isClosed hAfin hsf hAnonneg hab (by linarith) hbal hmax ?_
    exact Or.inl (by rw [show a + (x + 1 - a - 2) = x - 1 from by ring]; exact hx1A)
  -- Interval-union restrictions and their discrepancy bounds.
  obtain ⟨ivs₁, hB₁⟩ := hIU.inter_Icc_exists 1 c
  obtain ⟨ivs₂, hB₂⟩ := hIU.inter_Icc_exists (c + (b - a)) (x + 1 - a - 2)
  have hdisc₁ : disc (A ∩ Icc 1 c) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by norm_num) hcxp1 hmax
  have hdisc₂ : disc (A ∩ Icc (c + (b - a)) (x + 1 - a - 2)) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by linarith) (by linarith) hmax
  -- The two sumset (minterv) lower bounds.
  have hm1 := minterv_sum hIU.isClosed hAfin hab hbal.1 hB₁ hdisc₁
  have hm2 := minterv_sum hIU.isClosed hAfin hab hbal.1 hB₂ hdisc₂
  -- Mass identities.
  have hmassU : (volume (A ∩ Icc 1 c)).toReal = cum A c := by
    rw [← cum_sub_cum_eq_mass_Icc (by norm_num) hc1, cum_one_eq_zero_of_isLeast hmin, sub_zero]
  have hmassW : (volume (A ∩ Icc (c + (b - a)) (x + 1 - a - 2))).toReal
      = cum A (x + 1 - a - 2) - cum A (c + (b - a)) := by
    rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)]
  -- The three compact pieces.
  have hScompact : IsCompact (A + A) := hIU.isCompact.add hIU.isCompact
  have hUc : IsCompact ((A + A) ∩ Icc (a + 1) (a + c + mMinus A c)) :=
    hScompact.inter_right isClosed_Icc
  have hWc : IsCompact ((A + A) ∩ Icc (a + (c + (b - a)))
      (a + (x + 1 - a - 2) + mMinus A (x + 1 - a - 2))) :=
    hScompact.inter_right isClosed_Icc
  have hVc : IsCompact ((fun z => z - (-c)) '' (A ∩ Icc (a + mMinus A c) b)) :=
    isCompact_image_sub_const (hIU.isCompact.inter_right isClosed_Icc) (-c)
  have hUS : (A + A) ∩ Icc (a + 1) (a + c + mMinus A c) ⊆ A + A := Set.inter_subset_left
  have hWS : (A + A) ∩ Icc (a + (c + (b - a)))
      (a + (x + 1 - a - 2) + mMinus A (x + 1 - a - 2)) ⊆ A + A := Set.inter_subset_left
  have hVS : (fun z => z - (-c)) '' (A ∩ Icc (a + mMinus A c) b) ⊆ A + A := by
    rintro v ⟨z, hz, rfl⟩
    simp only [sub_neg_eq_add]; exact Set.add_mem_add hz.1 hcA
  -- Containment of the three pieces in consecutive intervals.
  have hUl : (A + A) ∩ Icc (a + 1) (a + c + mMinus A c)
      ⊆ Icc (a + 1) (a + c + mMinus A c) := Set.inter_subset_right
  have hWl : (A + A) ∩ Icc (a + (c + (b - a)))
      (a + (x + 1 - a - 2) + mMinus A (x + 1 - a - 2)) ⊆ Icc (b + c) (x - 1) := by
    intro w hw
    have hw2 := hw.2
    rw [Set.mem_Icc] at hw2 ⊢
    rw [hmz] at hw2
    constructor <;> [linarith [hw2.1]; linarith [hw2.2]]
  have hVl : (fun z => z - (-c)) '' (A ∩ Icc (a + mMinus A c) b)
      ⊆ Icc (a + c + mMinus A c) (b + c) := by
    rintro v ⟨z, hz, rfl⟩
    simp only [Set.mem_Icc, sub_neg_eq_add]
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  -- Apply the three-piece packing.
  have hpack := compact_three_piece_packing hUc hVc hWc hUS hVS hWS hUl hVl hWl
    (by linarith) (by linarith) (by linarith)
  -- Lower bounds on the three piece masses.
  have hUlow : 2 * cum A c
      ≤ (volume ((A + A) ∩ Icc (a + 1) (a + c + mMinus A c))).toReal := by
    rw [← hmassU]; exact hm1
  have hVeq : (volume ((fun z => z - (-c)) '' (A ∩ Icc (a + mMinus A c) b))).toReal
      = (volume (A ∩ Icc (a + mMinus A c) b)).toReal := by
    rw [volume_image_sub_const]
  have hWlow : 2 * (cum A (x + 1 - a - 2) - cum A (c + (b - a)))
      ≤ (volume ((A + A) ∩ Icc (a + (c + (b - a)))
          (a + (x + 1 - a - 2) + mMinus A (x + 1 - a - 2)))).toReal := by
    rw [← hmassW]; exact hm2
  -- Combine.
  linarith [hpack, hUlow, hWlow, hVeq]

/-- The sum-freeness packing inside `[a+1,x-1]`: the sumset and `A` are disjoint there. -/
lemma c_lem_sumfree_pack
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {a x : ℝ} (ha0 : 0 ≤ a + 1) (hax : a + 1 ≤ x - 1) :
    (volume ((A + A) ∩ Icc (a + 1) (x - 1))).toReal + (cum A (x - 1) - cum A (a + 1))
      ≤ (x - 1) - (a + 1) := by
  have hcum : cum A (x - 1) - cum A (a + 1) = (volume (A ∩ Icc (a + 1) (x - 1))).toReal :=
    cum_sub_cum_eq_mass_Icc ha0 hax
  rw [hcum]
  have hmeas : MeasurableSet A := hIU.isClosed.measurableSet
  have hdisj : Disjoint ((A + A) ∩ Icc (a + 1) (x - 1))
      (A ∩ Icc (a + 1) (x - 1)) := by
    simp only [Set.disjoint_left, mem_inter_iff]
    rintro z ⟨⟨p, hp, q, hq, rfl⟩, hz⟩ ⟨hzA, -⟩
    exact hsf hp hq hzA
  have hsubset : ((A + A) ∩ Icc (a + 1) (x - 1)) ∪
      (A ∩ Icc (a + 1) (x - 1)) ⊆ Icc (a + 1) (x - 1) := by
    exact Set.union_subset Set.inter_subset_right Set.inter_subset_right
  have hu : (volume (((A + A) ∩ Icc (a + 1) (x - 1)) ∪
      (A ∩ Icc (a + 1) (x - 1)))).toReal ≤ (x - 1) - (a + 1) := by
    refine le_trans (ENNReal.toReal_mono (ne_of_lt isCompact_Icc.measure_lt_top)
      (MeasureTheory.measure_mono hsubset)) ?_
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  rw [MeasureTheory.measure_union₀] at hu
  · rwa [ENNReal.toReal_add] at hu
    · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
        isCompact_Icc.measure_lt_top)
    · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
        isCompact_Icc.measure_lt_top)
  · exact (hmeas.inter measurableSet_Icc).nullMeasurableSet
  · exact MeasureTheory.measure_mono_null
      (fun z hz => Set.disjoint_left.mp hdisj hz.1 hz.2) (MeasureTheory.measure_empty)

/-- **Lemma `c lem`.**  For every `c ∈ A` with `c ≤ y - s - 2`,
`g ≥ |A ∩ [a + m_A^-(c), b]| - 2 (F(c+s) - F(c))`. -/
lemma c_lem_bound
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x g : ℝ} (hab : a < b)
    (hbal : IsBalanced A a b) (haA : a ∈ A)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hx1A : x - 1 ∈ A)
    (hgId : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = (x + 1 - a) - 3 - g) :
    ∀ c ∈ A, c ≤ (x + 1 - a) - (b - a) - 2 →
      g ≥ (volume (A ∩ Icc (a + mMinus A c) b)).toReal
        - 2 * (cum A (c + (b - a)) - cum A c) := by
  intro c hcA hcle
  have ha1 : 1 ≤ a := hmin.2 haA
  have hc1 : 1 ≤ c := hmin.2 hcA
  have hcx : c ≤ x - b - 1 := by linarith
  have hax : a + 1 ≤ x - 1 := by linarith
  have hA0 : A ⊆ Ici 0 := fun z hz => le_trans zero_le_one (hmin.2 hz)
  -- `m_A^-(c) ≤ t ≤ s`.
  have hmc : mMinus A c ≤ b - a := by
    refine le_trans (mMinus_le_disc_truncation hA0 (volume_inter_Icc_ne_top A 0 (x + 1))
      (show c ≤ x + 1 by linarith)) ?_
    exact le_trans hmax (discOn_le_sub A hab.le)
  have hlower := c_lem_sumset_lower hIU hsf hmin hab hbal hmax hx1A haA hcA hc1 hcx hmc
  have hpack := c_lem_sumfree_pack hIU hsf (by linarith) hax
  linarith
