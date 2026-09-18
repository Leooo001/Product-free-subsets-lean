import RequestProject.OffdiagonalInduction
import RequestProject.IntervalCover

/-!
# The sumset inequality `main2` for compact and measurable sets

This file extends the finite-interval-union sumset inequality (`main2_iu`, proved `sorry`-free
in `RequestProject/OffdiagonalInduction.lean`) to compact and measurable sets, via an
*outer fattening* argument.  The route parallels `RequestProject/Fattening.lean`:

* `disc_mono`: the interval discrepancy is monotone in the set.
* `disc_thickening_le`: the discrepancy of a closed thickening `K + [-η, η]` exceeds `disc K`
  by at most twice the measure the thickening adds.  This is the elementary replacement for the
  "discrepancy continuity" step: for any interval `I`,
  `2|Kη ∩ I| - |I| = (2|K ∩ I| - |I|) + 2|(Kη \ K) ∩ I| ≤ disc K + 2(|Kη| - |K|)`.
* `tendsto_volume_thickening`: `|S + [-c/(n+1), c/(n+1)]| → |S|` for compact `S`
  (measure continuity from above, since `⋂ₙ (S + [-c/(n+1),c/(n+1)]) = S`).
* `main2_compact`: assembling these with `main2_iu` gives the compact sumset/difference bound.
* `main2_measurable`: inner regularity lifts the compact bound to measurable sets of finite
  measure whose sumset (resp. difference set) has finite measure.

**Note on the statement.** The measurable statement requires the finiteness of `A + A`
(resp. `A - A`): a set of finite measure can have a sumset of infinite measure (e.g. a thin set
spread over `[0,∞)`), in which case `(volume (A+A)).toReal = 0` and the raw inequality
`4|A| - 2 d(A) ≤ (volume (A+A)).toReal` is simply false.  The finite-interval-union version
`main2_iu` does not face this because such sets are bounded.  The earlier measurable statements
in `RequestProject/Discrepancy.lean` (`offdiagonal_main2`, `main2`) omitted this hypothesis and
are therefore not provable as written; they have been commented out there and are superseded by
the corrected statements in this file.
-/

open MeasureTheory Set Metric Filter Topology
open scoped Pointwise

noncomputable section

namespace ProductFree

/-- **Discrepancy of a thickening.**  For a compact set `K` and `η > 0`, the discrepancy of the
closed thickening `K + [-η, η]` exceeds `disc K` by at most twice the measure the thickening
adds.  For each interval `I = [a,b]`,
`2|Kη ∩ I| - |I| = (2|K ∩ I| - |I|) + 2|(Kη \ K) ∩ I| ≤ disc K + 2(|Kη| - |K|)`,
using `K ⊆ Kη`, additivity of measure on the disjoint union `Kη ∩ I = (K ∩ I) ∪ ((Kη \ K) ∩ I)`,
`|(Kη \ K) ∩ I| ≤ |Kη \ K| = |Kη| - |K|`, and `disc_bddAbove` to take the supremum. -/
lemma disc_thickening_le {K : Set ℝ} (hKc : IsCompact K) {η : ℝ} (hη : 0 < η) :
    disc (K + Icc (-η) η) ≤
      disc K + 2 * ((volume (K + Icc (-η) η)).toReal - (volume K).toReal) := by
  set Kη := K + Icc (-η) η with hKη
  have hKηc : IsCompact Kη := hKc.add isCompact_Icc
  have hKmeas : MeasurableSet K := hKc.measurableSet
  have hKfin : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKηfin : volume Kη ≠ ⊤ := hKηc.measure_lt_top.ne
  have hKsub : K ⊆ Kη := by
    intro x hx; rw [hKη, Set.mem_add]
    exact ⟨x, hx, 0, ⟨by linarith, by linarith⟩, by ring⟩
  have hbound : ∀ a b : ℝ, a ≤ b →
      2 * (volume (Kη ∩ Icc a b)).toReal - (b - a)
        ≤ disc K + 2 * ((volume Kη).toReal - (volume K).toReal) := by
    intro a b hab
    have hmeasdiff : MeasurableSet ((Kη \ K) ∩ Icc a b) :=
      ((hKηc.measurableSet.diff hKmeas).inter measurableSet_Icc)
    have hdisj : Disjoint (K ∩ Icc a b) ((Kη \ K) ∩ Icc a b) := by
      rw [Set.disjoint_left]; rintro x ⟨hK, _⟩ ⟨⟨_, hnK⟩, _⟩; exact hnK hK
    have hsplitE : volume (Kη ∩ Icc a b)
        = volume (K ∩ Icc a b) + volume ((Kη \ K) ∩ Icc a b) := by
      rw [← measure_union hdisj hmeasdiff]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_union, mem_diff]
      constructor
      · rintro ⟨hxKη, hxI⟩
        by_cases h : x ∈ K
        · exact Or.inl ⟨h, hxI⟩
        · exact Or.inr ⟨⟨hxKη, h⟩, hxI⟩
      · rintro (⟨hK, hI⟩ | ⟨⟨hKη, _⟩, hI⟩)
        · exact ⟨hKsub hK, hI⟩
        · exact ⟨hKη, hI⟩
    have hKIfin : volume (K ∩ Icc a b) ≠ ⊤ :=
      ne_top_of_le_ne_top hKfin (measure_mono inter_subset_left)
    have hDIfin : volume ((Kη \ K) ∩ Icc a b) ≠ ⊤ :=
      ne_top_of_le_ne_top hKηfin (measure_mono (fun x hx => hx.1.1))
    have hsplit : (volume (Kη ∩ Icc a b)).toReal
        = (volume (K ∩ Icc a b)).toReal + (volume ((Kη \ K) ∩ Icc a b)).toReal := by
      rw [hsplitE, ENNReal.toReal_add hKIfin hDIfin]
    have hdiscK : 2 * (volume (K ∩ Icc a b)).toReal - (b - a) ≤ disc K :=
      le_csSup (disc_bddAbove hKfin) ⟨a, b, hab, rfl⟩
    have hdiff : (volume ((Kη \ K) ∩ Icc a b)).toReal
        ≤ (volume Kη).toReal - (volume K).toReal := by
      have h1 : (volume ((Kη \ K) ∩ Icc a b)).toReal ≤ (volume (Kη \ K)).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top hKηfin (measure_mono diff_subset))
          (measure_mono inter_subset_left)
      have h2 : (volume (Kη \ K)).toReal = (volume Kη).toReal - (volume K).toReal := by
        rw [measure_diff hKsub hKmeas.nullMeasurableSet hKfin,
          ENNReal.toReal_sub_of_le (measure_mono hKsub) hKηfin]
      linarith [h1, h2]
    rw [hsplit]; linarith [hdiscK, hdiff]
  apply csSup_le
  · exact ⟨_, 0, 0, le_rfl, rfl⟩
  · rintro r ⟨a, b, hab, rfl⟩
    exact hbound a b hab

/-- The Minkowski thickenings `S + [-c/(n+1), c/(n+1)]` shrink to `S` as `n → ∞`, for closed `S`. -/
lemma iInter_thickening_eq {S : Set ℝ} (hS : IsClosed S) {c : ℝ} (hc : 0 < c) :
    ⋂ n : ℕ, (S + Icc (-(c / (n + 1))) (c / (n + 1))) = S := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iInter] at hx
    rw [← hS.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (c / ε)
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : c / ((n : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ hnpos]
      have hce : c < ε * (n : ℝ) := by
        rw [← div_lt_iff₀' hε]; exact hn
      nlinarith [hε]
    obtain ⟨k, hk, w, hw, hkw⟩ := Set.mem_add.mp (hx n)
    refine ⟨k, hk, ?_⟩
    rw [Real.dist_eq]
    simp only [mem_Icc] at hw
    have hxk : x - k = w := by linarith [hkw]
    rw [hxk, abs_lt]
    constructor <;> linarith [hw.1, hw.2, hn1]
  · intro x hx
    rw [Set.mem_iInter]; intro n
    rw [Set.mem_add]
    refine ⟨x, hx, 0, ?_, by ring⟩
    rw [mem_Icc]
    exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩

/-- **Measure continuity from above for thickenings.**  For compact `S`,
`|S + [-c/(n+1), c/(n+1)]| → |S|` as `n → ∞`.  Uses `tendsto_measure_iInter_atTop` with the
antitone family `S + [-c/(n+1), c/(n+1)]` (compact, finite measure) whose intersection is `S`
(`iInter_thickening_eq`), then `ENNReal.toReal`. -/
lemma tendsto_volume_thickening {S : Set ℝ} (hS : IsCompact S) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (volume (S + Icc (-(c / (n + 1))) (c / (n + 1)))).toReal)
      atTop (nhds (volume S).toReal) := by
  set T : ℕ → Set ℝ := fun n => S + Icc (-(c / (n + 1))) (c / (n + 1)) with hT
  have hTcompact : ∀ n, IsCompact (T n) := fun n => hS.add isCompact_Icc
  have hmeas : ∀ n, NullMeasurableSet (T n) :=
    fun n => (hTcompact n).measurableSet.nullMeasurableSet
  have hanti : Antitone T := by
    intro n m hnm
    apply add_subset_add_left
    intro z hz; simp only [mem_Icc] at hz ⊢
    have hle : c / ((m : ℝ) + 1) ≤ c / ((n : ℝ) + 1) :=
      div_le_div_of_nonneg_left hc.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    constructor <;> linarith [hz.1, hz.2]
  have hfin : ∃ i, volume (T i) ≠ ⊤ := ⟨0, (hTcompact 0).measure_lt_top.ne⟩
  have hiInter : ⋂ n, T n = S := iInter_thickening_eq hS.isClosed hc
  have htends : Tendsto (fun n => volume (T n)) atTop (nhds (volume (⋂ n, T n))) :=
    tendsto_measure_iInter_atTop hmeas hanti hfin
  rw [hiInter] at htends
  exact (ENNReal.tendsto_toReal hS.measure_lt_top.ne).comp htends

/-- **The sumset inequality for compact sets.**  For a nonempty compact `K`,
`4|K| - 2 d(K) ≤ |K + K|` and `4|K| - 2 d(K) ≤ |K - K|`.

For each `n`, cover `K` by a finite interval union `F` with `K ⊆ F ⊆ Kₙ := K + [-1/(n+1),1/(n+1)]`
(`exists_intervalUnion_cover`).  `main2_iu` applied to `F` gives
`4|F| - 2 d(F) ≤ |F + F|` (and the `-` version).  Then `|K| ≤ |F|`, `|F+F| ≤ |Kₙ+Kₙ|`,
`d(F) ≤ d(Kₙ) ≤ d(K) + 2(|Kₙ| - |K|)` (`disc_mono`, `disc_thickening_le`), so
`4|K| - 2 d(K) ≤ |Kₙ+Kₙ| + 4(|Kₙ| - |K|)`.  As `n → ∞` the right side tends to `|K+K|`
(`tendsto_volume_thickening`, using `Kₙ + Kₙ = (K+K) + [-2/(n+1),2/(n+1)]`); conclude with
`le_of_tendsto'`.  The difference set is identical using the `|F - F|` half of `main2_iu`. -/
lemma main2_compact {K : Set ℝ} (hKc : IsCompact K) (hKne : K.Nonempty) :
    4 * (volume K).toReal - 2 * disc K ≤ (volume (K + K)).toReal ∧
    4 * (volume K).toReal - 2 * disc K ≤ (volume (K - K)).toReal := by
  have hKfin : volume K ≠ ⊤ := hKc.measure_lt_top.ne
  -- abbreviation for the thickened set at step `n`
  set Kt : ℕ → Set ℝ := fun n => K + Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)) with hKt
  have hKtc : ∀ n, IsCompact (Kt n) := fun n => hKc.add isCompact_Icc
  have hη0 : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  -- measure continuity of the thickening
  have hKcont : Tendsto (fun n : ℕ => (volume (Kt n)).toReal) atTop (nhds (volume K).toReal) :=
    tendsto_volume_thickening hKc (by norm_num : (0:ℝ) < 1)
  refine ⟨?_, ?_⟩
  · -- sumset
    have hstepSum : ∀ n : ℕ,
        4 * (volume K).toReal - 2 * disc K ≤
          (volume (Kt n + Kt n)).toReal + 4 * ((volume (Kt n)).toReal - (volume K).toReal) := by
      intro n
      obtain ⟨F, ivs, hIU, hKF, hFsub⟩ := exists_intervalUnion_cover hKc (hη0 n)
      have hFne : F.Nonempty := hKne.mono hKF
      have hivsne : ivs ≠ [] := by
        rintro rfl; obtain ⟨z, hz⟩ := hFne; rw [hIU.2.2] at hz; simp at hz
      have hm2 := (main2_iu hIU hivsne).1
      have hKtfin : volume (Kt n) ≠ ⊤ := (hKtc n).measure_lt_top.ne
      have hFfin : volume F ≠ ⊤ := hIU.finite
      have hvolKF : (volume K).toReal ≤ (volume F).toReal :=
        ENNReal.toReal_mono hFfin (measure_mono hKF)
      have hdF : disc F ≤ disc (Kt n) := disc_mono hFsub hKtfin
      have hdKt : disc (Kt n) ≤ disc K + 2 * ((volume (Kt n)).toReal - (volume K).toReal) :=
        disc_thickening_le hKc (hη0 n)
      have hFFsub : F + F ⊆ Kt n + Kt n := Set.add_subset_add hFsub hFsub
      have hFF : (volume (F + F)).toReal ≤ (volume (Kt n + Kt n)).toReal :=
        ENNReal.toReal_mono ((hKtc n).add (hKtc n)).measure_lt_top.ne (measure_mono hFFsub)
      linarith [hm2, hvolKF, hdF, hdKt, hFF]
    -- limit of the right-hand side
    have hsumcont : Tendsto (fun n : ℕ => (volume (Kt n + Kt n)).toReal) atTop
        (nhds (volume (K + K)).toReal) := by
      have h2 := tendsto_volume_thickening (hKc.add hKc) (by norm_num : (0:ℝ) < 2)
      have hfe : (fun n : ℕ => (volume (Kt n + Kt n)).toReal)
          = fun n : ℕ => (volume ((K + K) + Icc (-(2 / ((n : ℝ) + 1))) (2 / ((n : ℝ) + 1)))).toReal := by
        funext n
        have hicc : Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))
              + Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))
            = Icc (-(2 / ((n : ℝ) + 1))) (2 / ((n : ℝ) + 1)) := by
          rw [Icc_add_Icc (by have := hη0 n; linarith) (by have := hη0 n; linarith)]
          congr 1 <;> ring
        have hset : Kt n + Kt n
            = (K + K) + Icc (-(2 / ((n : ℝ) + 1))) (2 / ((n : ℝ) + 1)) := by
          simp only [hKt]; rw [add_add_add_comm, hicc]
        rw [hset]
      rw [hfe]; exact h2
    have hc0 : Tendsto (fun n : ℕ => (volume (Kt n)).toReal - (volume K).toReal) atTop
        (nhds (0 : ℝ)) := by
      have := hKcont.sub (tendsto_const_nhds (x := (volume K).toReal)); simpa using this
    have hc1 : Tendsto (fun n : ℕ => 4 * ((volume (Kt n)).toReal - (volume K).toReal)) atTop
        (nhds (0 : ℝ)) := by
      have := hc0.const_mul 4; simpa using this
    have hRHS : Tendsto
        (fun n : ℕ => (volume (Kt n + Kt n)).toReal + 4 * ((volume (Kt n)).toReal - (volume K).toReal))
        atTop (nhds (volume (K + K)).toReal) := by
      have := hsumcont.add hc1; simpa using this
    exact ge_of_tendsto' hRHS hstepSum
  · -- difference set
    have hstepDiff : ∀ n : ℕ,
        4 * (volume K).toReal - 2 * disc K ≤
          (volume (Kt n - Kt n)).toReal + 4 * ((volume (Kt n)).toReal - (volume K).toReal) := by
      intro n
      obtain ⟨F, ivs, hIU, hKF, hFsub⟩ := exists_intervalUnion_cover hKc (hη0 n)
      have hFne : F.Nonempty := hKne.mono hKF
      have hivsne : ivs ≠ [] := by
        rintro rfl; obtain ⟨z, hz⟩ := hFne; rw [hIU.2.2] at hz; simp at hz
      have hm2 := (main2_iu hIU hivsne).2
      have hKtfin : volume (Kt n) ≠ ⊤ := (hKtc n).measure_lt_top.ne
      have hFfin : volume F ≠ ⊤ := hIU.finite
      have hvolKF : (volume K).toReal ≤ (volume F).toReal :=
        ENNReal.toReal_mono hFfin (measure_mono hKF)
      have hdF : disc F ≤ disc (Kt n) := disc_mono hFsub hKtfin
      have hdKt : disc (Kt n) ≤ disc K + 2 * ((volume (Kt n)).toReal - (volume K).toReal) :=
        disc_thickening_le hKc (hη0 n)
      have hFFsub : F - F ⊆ Kt n - Kt n := by
        rw [sub_eq_add_neg, sub_eq_add_neg]
        exact Set.add_subset_add hFsub (Set.neg_subset_neg.mpr hFsub)
      have hKtsubc : IsCompact (Kt n - Kt n) := by
        rw [sub_eq_add_neg]; exact (hKtc n).add (hKtc n).neg
      have hFF : (volume (F - F)).toReal ≤ (volume (Kt n - Kt n)).toReal :=
        ENNReal.toReal_mono hKtsubc.measure_lt_top.ne (measure_mono hFFsub)
      linarith [hm2, hvolKF, hdF, hdKt, hFF]
    have hdiffcont : Tendsto (fun n : ℕ => (volume (Kt n - Kt n)).toReal) atTop
        (nhds (volume (K - K)).toReal) := by
      have hKsubc : IsCompact (K - K) := by rw [sub_eq_add_neg]; exact hKc.add hKc.neg
      have h2 := tendsto_volume_thickening hKsubc (by norm_num : (0:ℝ) < 2)
      have hfe : (fun n : ℕ => (volume (Kt n - Kt n)).toReal)
          = fun n : ℕ => (volume ((K - K) + Icc (-(2 / ((n : ℝ) + 1))) (2 / ((n : ℝ) + 1)))).toReal := by
        funext n
        have hicc : Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))
              + Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))
            = Icc (-(2 / ((n : ℝ) + 1))) (2 / ((n : ℝ) + 1)) := by
          rw [Icc_add_Icc (by have := hη0 n; linarith) (by have := hη0 n; linarith)]
          congr 1 <;> ring
        have hset : Kt n - Kt n
            = (K - K) + Icc (-(2 / ((n : ℝ) + 1))) (2 / ((n : ℝ) + 1)) := by
          simp only [hKt, sub_eq_add_neg, neg_add, neg_Icc, neg_neg]
          rw [add_add_add_comm, hicc]
        rw [hset]
      rw [hfe]; exact h2
    have hc0 : Tendsto (fun n : ℕ => (volume (Kt n)).toReal - (volume K).toReal) atTop
        (nhds (0 : ℝ)) := by
      have := hKcont.sub (tendsto_const_nhds (x := (volume K).toReal)); simpa using this
    have hc1 : Tendsto (fun n : ℕ => 4 * ((volume (Kt n)).toReal - (volume K).toReal)) atTop
        (nhds (0 : ℝ)) := by
      have := hc0.const_mul 4; simpa using this
    have hRHS : Tendsto
        (fun n : ℕ => (volume (Kt n - Kt n)).toReal + 4 * ((volume (Kt n)).toReal - (volume K).toReal))
        atTop (nhds (volume (K - K)).toReal) := by
      have := hdiffcont.add hc1; simpa using this
    exact ge_of_tendsto' hRHS hstepDiff

/-- **The sumset inequality for measurable sets** (corrected statement, see the module docstring).
For a measurable `A` of finite measure whose sumset `A + A` also has finite measure,
`4|A| - 2 d(A) ≤ |A + A|`; and the analogous bound for `A - A` when it has finite measure.

Proved from `main2_compact` by inner regularity: for compact `K ⊆ A`,
`4|K| - 2 d(A) ≤ 4|K| - 2 d(K) ≤ |K+K| ≤ |A+A|` (`disc_mono`, `measure_mono`); take the
supremum over `K` using `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`. -/
theorem main2_measurable {A : Set ℝ} (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) :
    (volume (A + A) ≠ ⊤ → 4 * (volume A).toReal - 2 * disc A ≤ (volume (A + A)).toReal) ∧
    (volume (A - A) ≠ ⊤ → 4 * (volume A).toReal - 2 * disc A ≤ (volume (A - A)).toReal) := by
  have hdiscA : 0 ≤ disc A := disc_nonneg hfin
  -- generic reduction to compact subsets
  have core : ∀ G : Set ℝ, volume G ≠ ⊤ →
      (∀ K : Set ℝ, IsCompact K → K ⊆ A → K.Nonempty →
        4 * (volume K).toReal - 2 * disc K ≤ (volume G).toReal) →
      4 * (volume A).toReal - 2 * disc A ≤ (volume G).toReal := by
    intro G hGfin hKG
    have hGnn : (0 : ℝ) ≤ (volume G).toReal := ENNReal.toReal_nonneg
    have hcpt : ∀ K : Set ℝ, IsCompact K → K ⊆ A →
        4 * (volume K).toReal ≤ (volume G).toReal + 2 * disc A := by
      intro K hKc hKA
      rcases K.eq_empty_or_nonempty with rfl | hKne
      · simp only [measure_empty, ENNReal.toReal_zero, mul_zero]; linarith
      · have hdK : disc K ≤ disc A := disc_mono hKA hfin
        have := hKG K hKc hKA hKne
        linarith
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨K, hKA, hKc, hKlt⟩ :=
      hA.exists_isCompact_lt_add hfin (ε := ENNReal.ofReal (ε / 4))
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
    have hKfin : volume K ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hKA)
    have hAK : (volume A).toReal ≤ (volume K).toReal + ε / 4 := by
      calc (volume A).toReal
            ≤ (volume K + ENNReal.ofReal (ε / 4)).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hKfin, ENNReal.ofReal_ne_top⟩)
                (le_of_lt hKlt)
        _ = (volume K).toReal + ε / 4 := by
              rw [ENNReal.toReal_add hKfin ENNReal.ofReal_ne_top,
                ENNReal.toReal_ofReal (by linarith)]
    have hb := hcpt K hKc hKA
    linarith
  refine ⟨fun hAAfin => core (A + A) hAAfin ?_, fun hAAfin => core (A - A) hAAfin ?_⟩
  · intro K hKc hKA hKne
    have hm := (main2_compact hKc hKne).1
    have hsub : K + K ⊆ A + A := Set.add_subset_add hKA hKA
    have hle : (volume (K + K)).toReal ≤ (volume (A + A)).toReal :=
      ENNReal.toReal_mono hAAfin (measure_mono hsub)
    linarith
  · intro K hKc hKA hKne
    have hm := (main2_compact hKc hKne).2
    have hsub : K - K ⊆ A - A := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      exact Set.add_subset_add hKA (Set.neg_subset_neg.mpr hKA)
    have hle : (volume (K - K)).toReal ≤ (volume (A - A)).toReal :=
      ENNReal.toReal_mono hAAfin (measure_mono hsub)
    linarith

end ProductFree
