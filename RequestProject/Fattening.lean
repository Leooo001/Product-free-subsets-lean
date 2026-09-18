import RequestProject.Main1
import RequestProject.IntervalCover

/-!
# Product-free measurable sets in `(0,1)` have measure `≤ 1/3`

This file extends the product-free measure bound from finite unions of closed intervals
(`main1_intervalUnion`, proved `sorry`-free) to arbitrary measurable sets, **without** using
the deep measurable `key_lemma`.

The route is an *outer fattening* argument:

* `exists_isIntervalUnion_biUnion`: any finite union of closed intervals is (as a set) an
  `IsIntervalUnion` for a suitable sorted, strictly separated list.
* `exists_intervalUnion_cover`: a compact set `K` is covered by a finite union of closed
  intervals `F` (an `IsIntervalUnion`) contained in the closed `η`-thickening `K + [-η,η]`.
* `exists_productFree_thickening`: for a compact product-free `K ⊆ (0,1)`, a small closed
  thickening `K + [-δ,δ]` is still product-free and still contained in `(0,1)`.
* `main1_compact'`: assembling these with `main1_intervalUnion` gives the compact bound
  `|K| < 1/3` with **no** dependence on `key_lemma`.
* `main1_measurable`: inner regularity of Lebesgue measure lifts the compact bound to any
  measurable product-free `E ⊆ (0,1)`, giving `|E| ≤ 1/3`.
-/

open MeasureTheory Set Metric
open scoped Pointwise

noncomputable section

namespace ProductFree

/-- For a compact product-free set `K ⊆ (0,1)`, a small closed thickening `K + [-δ, δ]` is
still product-free and still contained in `(0,1)`. -/
lemma exists_productFree_thickening {K : Set ℝ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hK : K ⊆ Ioo 0 1) (hpf : IsProductFree K) :
    ∃ δ : ℝ, 0 < δ ∧ IsProductFree (K + Icc (-δ) δ) ∧ (K + Icc (-δ) δ) ⊆ Ioo 0 1 := by
  have hP : IsCompact (K * K) := hKc.mul hKc
  have hdisj : Disjoint (K * K) K := by
    rw [Set.disjoint_left]; rintro z ⟨x, hx, y, hy, rfl⟩ hz; exact hpf hx hy hz
  obtain ⟨r, hr, hbd0⟩ := Metric.exists_pos_forall_lt_edist hP hKc.isClosed hdisj
  set R : ℝ := (r : ℝ) with hR
  have hR0 : 0 < R := by rw [hR]; exact_mod_cast hr
  have hbd : ∀ p ∈ K * K, ∀ k ∈ K, R < dist p k := by
    intro p hp k hk
    have h := hbd0 p hp k hk
    rw [edist_nndist, ENNReal.coe_lt_coe] at h
    have h2 : (r : ℝ) < (nndist p k : ℝ) := by exact_mod_cast h
    rwa [coe_nndist] at h2
  set a := sInf K with ha
  set b := sSup K with hb
  have haK : a ∈ K := hKc.sInf_mem hKne
  have hbK : b ∈ K := hKc.sSup_mem hKne
  have ha0 : 0 < a := (hK haK).1
  have hb1 : b < 1 := (hK hbK).2
  have hsub : K ⊆ Icc a b := fun x hx =>
    ⟨csInf_le hKc.bddBelow hx, le_csSup hKc.bddAbove hx⟩
  set δ := min (R / 4) (min (a / 2) ((1 - b) / 2)) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by linarith))
  have hδr : δ ≤ R / 4 := min_le_left _ _
  have hδa : δ ≤ a / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδb : δ ≤ (1 - b) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨δ, hδ0, ?_, ?_⟩
  · intro u hu v hv huv
    rw [Set.mem_add] at hu hv huv
    obtain ⟨k1, hk1, s, hs, rfl⟩ := hu
    obtain ⟨k2, hk2, t, ht, rfl⟩ := hv
    obtain ⟨k3, hk3, w, hw, hw3⟩ := huv
    have hk1I := hsub hk1; have hk2I := hsub hk2
    simp only [mem_Icc] at hs ht hw hk1I hk2I
    have hkk : k1 * k2 ∈ K * K := Set.mul_mem_mul hk1 hk2
    have hsep := hbd (k1 * k2) hkk k3 hk3
    rw [Real.dist_eq] at hsep
    have hdiff : |(k1 + s) * (k2 + t) - k1 * k2| ≤ 2 * δ := by
      have expand : (k1 + s) * (k2 + t) - k1 * k2 = (k1 + s) * t + k2 * s := by ring
      rw [expand]
      have h1 : |(k1 + s) * t| ≤ δ := by
        rw [abs_mul]
        calc |k1 + s| * |t| ≤ 1 * δ := by
              apply mul_le_mul
              · rw [abs_le]; constructor <;> linarith [hk1I.1, hk1I.2, hs.1, hs.2]
              · rw [abs_le]; exact ⟨ht.1, ht.2⟩
              · positivity
              · norm_num
          _ = δ := by ring
      have h2 : |k2 * s| ≤ δ := by
        rw [abs_mul]
        calc |k2| * |s| ≤ 1 * δ := by
              apply mul_le_mul
              · rw [abs_le]; constructor <;> linarith [hk2I.1, hk2I.2]
              · rw [abs_le]; exact ⟨hs.1, hs.2⟩
              · positivity
              · norm_num
          _ = δ := by ring
      calc |(k1 + s) * t + k2 * s| ≤ |(k1 + s) * t| + |k2 * s| := abs_add_le _ _
        _ ≤ δ + δ := by linarith
        _ = 2 * δ := by ring
    have hfin : |k1 * k2 - k3| ≤ 3 * δ := by
      have heq : k1 * k2 - k3 = (k1 * k2 - (k1 + s) * (k2 + t)) + w := by rw [← hw3]; ring
      rw [heq]
      calc |(k1 * k2 - (k1 + s) * (k2 + t)) + w|
            ≤ |k1 * k2 - (k1 + s) * (k2 + t)| + |w| := abs_add_le _ _
        _ ≤ 2 * δ + δ := by
            gcongr
            · rw [abs_sub_comm]; exact hdiff
            · rw [abs_le]; exact ⟨hw.1, hw.2⟩
        _ = 3 * δ := by ring
    linarith [hsep, hfin, hδr, hR0]
  · intro x hx
    rw [Set.mem_add] at hx
    obtain ⟨k, hk, w, hw, rfl⟩ := hx
    have hkI := hsub hk; simp only [mem_Icc] at hkI hw
    exact ⟨by linarith [hkI.1, hw.1], by linarith [hkI.2, hw.2]⟩

/-- **Main theorem (compact version, `sorry`-free).** A nonempty compact product-free subset of
`(0,1)` has Lebesgue measure less than `1/3`. Proved by outer fattening and
`main1_intervalUnion`, with **no** dependence on `key_lemma`. -/
theorem main1_compact' {K : Set ℝ} (hKc : IsCompact K) (hKne : K.Nonempty) (hK : K ⊆ Ioo 0 1)
    (hpf : IsProductFree K) : (volume K).toReal < 1 / 3 := by
  obtain ⟨δ, hδ, hpfT, hTsub⟩ := exists_productFree_thickening hKc hKne hK hpf
  obtain ⟨F, ivs, hIU, hKF, hFT⟩ := exists_intervalUnion_cover hKc hδ
  have hFsub : F ⊆ Ioo 0 1 := hFT.trans hTsub
  have hFpf : IsProductFree F := hpfT.subset hFT
  have hFne : F.Nonempty := hKne.mono hKF
  have hFlt : (volume F).toReal < 1 / 3 := main1_intervalUnion hIU hFne hFsub hFpf
  have hFfin : volume F ≠ ⊤ := hIU.finite
  calc (volume K).toReal ≤ (volume F).toReal :=
        ENNReal.toReal_mono hFfin (measure_mono hKF)
    _ < 1 / 3 := hFlt

/-- **Main theorem (measurable version).** A measurable product-free subset of `(0,1)` has
Lebesgue measure at most `1/3`. Obtained from the compact case by inner regularity of Lebesgue
measure. This is `sorry`-free: it does **not** depend on `key_lemma`. -/
theorem main1_measurable {E : Set ℝ} (hEmeas : MeasurableSet E) (hE : E ⊆ Ioo 0 1)
    (hpf : IsProductFree E) : volume E ≤ ENNReal.ofReal (1 / 3) := by
  have hfin : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hE)
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  rw [hEmeas.measure_eq_iSup_isCompact_of_ne_top hfin]
  refine iSup_le (fun K => iSup_le (fun hKE => iSup_le (fun hKc => ?_)))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · simp [hKe]
  · have hlt : (volume K).toReal < 1 / 3 :=
      main1_compact' hKc hKne (hKE.trans hE) (hpf.subset hKE)
    have hKfin : volume K ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (measure_mono hKE)
    calc volume K = ENNReal.ofReal ((volume K).toReal) := (ENNReal.ofReal_toReal hKfin).symm
      _ ≤ ENNReal.ofReal (1 / 3) := ENNReal.ofReal_le_ofReal (le_of_lt hlt)

/-- **Main theorem (open version, `sorry`-free).** An open product-free subset of `(0,1)` has
Lebesgue measure at most `1/3`. This is the paper's headline result; unlike `ProductFree.main1`
in `Main1.lean`, this proof does **not** depend on `key_lemma` (it goes through the outer
fattening argument and `main1_intervalUnion`). -/
theorem main1_open' {E : Set ℝ} (hEo : IsOpen E) (hE : E ⊆ Ioo 0 1) (hpf : IsProductFree E) :
    volume E ≤ ENNReal.ofReal (1 / 3) :=
  main1_measurable hEo.measurableSet hE hpf

end ProductFree
