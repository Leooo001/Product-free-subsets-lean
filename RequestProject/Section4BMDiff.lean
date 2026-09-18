import RequestProject.Section4YBound
import RequestProject.Section4MInterv
import RequestProject.Section4Boost

/-!
# Section 4: Brunn–Minkowski for difference sets

`intervalUnion_add_measure_ge` gives the one-dimensional Brunn–Minkowski inequality for the
*sum* of two nonempty compact sets.  The final-contradiction packings use the *difference*
`B - C` of two different sets, so we record the general compact form of both the sum and the
difference inequality here.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

/-- One-dimensional Brunn–Minkowski for the sum of two nonempty compact sets. -/
lemma compact_add_measure_ge {B C : Set ℝ}
    (hB : IsCompact B) (hC : IsCompact C) (hBne : B.Nonempty) (hCne : C.Nonempty) :
    (volume B).toReal + (volume C).toReal ≤ (volume (B + C)).toReal := by
  obtain ⟨a, ha⟩ : ∃ a, IsLeast B a := hB.exists_isLeast hBne
  obtain ⟨d, hd⟩ : ∃ d, IsGreatest C d := hC.exists_isGreatest hCne
  have hBd : volume ((fun x => x + d) '' B) = volume B := by rw [image_add_right]; simp
  have hCa : volume ((fun x => a + x) '' C) = volume C := by rw [image_add_left]; simp
  have hdisj : AEDisjoint volume ((fun x => x + d) '' B) ((fun x => a + x) '' C) := by
    refine MeasureTheory.measure_mono_null ?_ (by norm_num : volume ({a + d} : Set ℝ) = 0)
    intro z hz
    simp only [Set.mem_inter_iff, Set.mem_image] at hz
    obtain ⟨⟨p, hp, rfl⟩, ⟨q, hq, hq2⟩⟩ := hz
    have hple : a ≤ p := ha.2 hp
    have hqle : q ≤ d := hd.2 hq
    simp only [Set.mem_singleton_iff]; linarith
  have hnull : NullMeasurableSet ((fun x => a + x) '' C) volume :=
    IsCompact.nullMeasurableSet (hC.image (continuous_const.add continuous_id'))
  have hunion := MeasureTheory.measure_union₀ hnull hdisj
  have hsubset : ((fun x => x + d) '' B ∪ (fun x => a + x) '' C) ⊆ B + C := by
    rintro x (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact Set.add_mem_add hy hd.1
    · exact Set.add_mem_add ha.1 hy
  have hmono := MeasureTheory.measure_mono (μ := volume) hsubset
  rw [hunion] at hmono
  have hfin : volume (B + C) ≠ ⊤ := ne_of_lt (IsCompact.measure_lt_top (hB.add hC))
  have hkey := ENNReal.toReal_mono hfin hmono
  rw [ENNReal.toReal_add, hBd, hCa] at hkey
  · exact hkey
  · exact ne_of_lt (hB.image (continuous_add_right _) |>.measure_lt_top)
  · exact ne_of_lt (hC.image (continuous_const.add continuous_id') |>.measure_lt_top)

/-- One-dimensional Brunn–Minkowski for the difference of two nonempty compact sets. -/
lemma compact_sub_measure_ge {B C : Set ℝ}
    (hB : IsCompact B) (hC : IsCompact C) (hBne : B.Nonempty) (hCne : C.Nonempty) :
    (volume B).toReal + (volume C).toReal ≤ (volume (B - C)).toReal := by
  have hadd := compact_add_measure_ge hB hC.neg hBne (hCne.neg)
  rw [sub_eq_add_neg]
  rwa [Measure.measure_neg volume C] at hadd

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- **Reflection difference-set packing.**  For `B = A∩[p,q]` and `C = A∩[r,s]` both nonempty,
Brunn–Minkowski gives `|B - C| ≥ |B| + |C|`; the difference set lies in `[p-s, q-r] ⊆ [L,R]`
and, by sum-freeness, is disjoint from `A`.  Hence the three cumulative masses `|B|`, `|C|`
and `|A∩[L,R]|` pack into `[L,R]`. -/
lemma reflect_diff_packing (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {p q r s L R : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hL : 0 ≤ L) (hLR : L ≤ R)
    {wB wC : ℝ} (hwB : wB ∈ A ∩ Icc p q) (hwC : wC ∈ A ∩ Icc r s)
    (hcontain : Icc (p - s) (q - r) ⊆ Icc L R) :
    (cum A q - cum A p) + (cum A s - cum A r) + (cum A R - cum A L) ≤ R - L := by
  have hmeas : MeasurableSet A := hIU.isClosed.measurableSet
  have hBc : IsCompact (A ∩ Icc p q) := hIU.isCompact.inter_right isClosed_Icc
  have hCc : IsCompact (A ∩ Icc r s) := hIU.isCompact.inter_right isClosed_Icc
  have hbm := compact_sub_measure_ge hBc hCc ⟨wB, hwB⟩ ⟨wC, hwC⟩
  have hDc : IsCompact ((A ∩ Icc p q) - (A ∩ Icc r s)) := by
    rw [sub_eq_add_neg]; exact hBc.add hCc.neg
  have hsub : (A ∩ Icc p q) - (A ∩ Icc r s) ⊆ Icc L R := by
    rintro d ⟨x, hx, y, hy, rfl⟩
    exact hcontain (Set.mem_Icc.mpr ⟨by dsimp; linarith [hx.2.1, hy.2.2],
      by dsimp; linarith [hx.2.2, hy.2.1]⟩)
  have hdisjA : Disjoint ((A ∩ Icc p q) - (A ∩ Icc r s)) A := by
    rw [Set.disjoint_left]
    rintro d ⟨x, hx, y, hy, rfl⟩ hdA
    apply hsf hy.1 hdA
    show y + (x - y) ∈ A
    rw [show y + (x - y) = x from by ring]; exact hx.1
  have hd2 : Disjoint ((A ∩ Icc p q) - (A ∩ Icc r s)) (A ∩ Icc L R) :=
    hdisjA.mono_right Set.inter_subset_left
  have hcover : ((A ∩ Icc p q) - (A ∩ Icc r s)) ∪ (A ∩ Icc L R) ⊆ Icc L R :=
    Set.union_subset hsub Set.inter_subset_right
  have hfinD : volume ((A ∩ Icc p q) - (A ∩ Icc r s)) ≠ ⊤ := hDc.measure_lt_top.ne
  have hfinI : volume (A ∩ Icc L R) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by simp [Real.volume_Icc]))
  have hmono := measure_mono (μ := volume) hcover
  rw [measure_union hd2 (hmeas.inter measurableSet_Icc)] at hmono
  have hkey := ENNReal.toReal_mono (by simp [Real.volume_Icc]) hmono
  rw [ENNReal.toReal_add hfinD hfinI, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)] at hkey
  rw [cum_sub_cum_eq_mass_Icc hp hpq, cum_sub_cum_eq_mass_Icc hr hrs,
    cum_sub_cum_eq_mass_Icc hL hLR]
  linarith

/-- **Sumset packing.**  If `mMinus A β = 0` then `minterv` on `[α,β]` gives a copy of the
sumset `2|A∩[α,β]|` inside `(A+A) ∩ [a+α,a+β]`, which is disjoint from `A`; hence
`2(F(β)-F(α)) + (F(a+β)-F(a+α)) ≤ β - α`. -/
lemma minterv_sumset_packing (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {a b α β : ℝ} (hab : a < b) (hbal : IsBalanced A a b)
    (hmy : mMinus A β = 0) (hα0 : 0 ≤ α) (haα0 : 0 ≤ a + α) (hαβ : α ≤ β)
    (hdisc : disc (A ∩ Icc α β) ≤ discOn A a b) :
    2 * (cum A β - cum A α) + (cum A (a + β) - cum A (a + α)) ≤ β - α := by
  obtain ⟨jvs, hrestrict⟩ := hIU.inter_Icc_exists α β
  have hsumlower : 2 * (volume (A ∩ Icc α β)).toReal ≤
      (volume ((A + A) ∩ Icc (a + α) (a + β))).toReal := by
    have := minterv_sum hIU.isClosed hIU.isCompact.measure_lt_top.ne hab hbal.1 hrestrict hdisc
    rwa [hmy, add_zero] at this
  have hdisj : Disjoint ((A + A) ∩ Icc (a + α) (a + β)) (A ∩ Icc (a + α) (a + β)) := by
    simp only [Set.disjoint_left, mem_inter_iff]
    rintro z ⟨⟨p, hp, q, hq, rfl⟩, hz⟩ ⟨hzA, -⟩
    exact hsf hp hq hzA
  have hpack : (volume ((A + A) ∩ Icc (a + α) (a + β))).toReal +
      (volume (A ∩ Icc (a + α) (a + β))).toReal ≤ (a + β) - (a + α) := by
    have hsubset : ((A + A) ∩ Icc (a + α) (a + β)) ∪
        (A ∩ Icc (a + α) (a + β)) ⊆ Icc (a + α) (a + β) :=
      Set.union_subset Set.inter_subset_right Set.inter_subset_right
    have hu : (volume (((A + A) ∩ Icc (a + α) (a + β)) ∪
        (A ∩ Icc (a + α) (a + β)))).toReal ≤ (a + β) - (a + α) := by
      refine le_trans (ENNReal.toReal_mono (ne_of_lt isCompact_Icc.measure_lt_top)
        (MeasureTheory.measure_mono hsubset)) ?_
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    rw [MeasureTheory.measure_union₀] at hu
    · rwa [ENNReal.toReal_add] at hu
      · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
          isCompact_Icc.measure_lt_top)
      · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
          isCompact_Icc.measure_lt_top)
    · exact (hIU.isClosed.measurableSet.inter measurableSet_Icc).nullMeasurableSet
    · exact MeasureTheory.measure_mono_null
        (fun z hz => Set.disjoint_left.mp hdisj hz.1 hz.2) (MeasureTheory.measure_empty)
  rw [cum_sub_cum_eq_mass_Icc hα0 hαβ, cum_sub_cum_eq_mass_Icc haα0 (by linarith)]
  linarith

/-- **Translate packing.**  For `p ∈ A`, the translate `p + (A∩[l,r])` lies in `[p+l,p+r]` and,
by sum-freeness, is disjoint from `A`; hence `|A∩[l,r]| + |A∩[p+l,p+r]| ≤ r - l`. -/
lemma translate_pair_mass_le (hA : MeasurableSet A) (hsf : IsSumFree A)
    {p l r : ℝ} (hp : p ∈ A) (hlr : l ≤ r) :
    (volume (A ∩ Icc l r)).toReal + (volume (A ∩ Icc (p + l) (p + r))).toReal ≤ r - l := by
  have h_disjoint : Disjoint (A ∩ Icc l r) ((fun z => z - p) '' (A ∩ Icc (p + l) (p + r))) := by
    rw [Set.disjoint_left]
    rintro w hw ⟨z, hz, rfl⟩
    exact hsf hw.1 hp (by rw [sub_add_cancel]; exact hz.1)
  have hsub : (fun z => z - p) '' (A ∩ Icc (p + l) (p + r)) ⊆ Icc l r := by
    rintro w ⟨z, hz, rfl⟩
    exact Set.mem_Icc.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have himg_eq : (fun z => z - p) '' (A ∩ Icc (p + l) (p + r)) =
      (fun w => w + p) ⁻¹' (A ∩ Icc (p + l) (p + r)) := by
    ext w; constructor
    · rintro ⟨z, hz, rfl⟩
      have hzz : z - p + p = z := by ring
      rw [Set.mem_preimage, hzz]; exact hz
    · intro hw; exact ⟨w + p, hw, by ring⟩
  have hmeasimg : MeasurableSet ((fun z => z - p) '' (A ∩ Icc (p + l) (p + r))) := by
    rw [himg_eq]; exact (measurable_add_const p) (hA.inter measurableSet_Icc)
  have hcover : (A ∩ Icc l r) ∪ ((fun z => z - p) '' (A ∩ Icc (p + l) (p + r))) ⊆ Icc l r :=
    Set.union_subset Set.inter_subset_right hsub
  have hu : (volume ((A ∩ Icc l r) ∪
      ((fun z => z - p) '' (A ∩ Icc (p + l) (p + r))))).toReal ≤ r - l := by
    refine le_trans (ENNReal.toReal_mono (ne_of_lt isCompact_Icc.measure_lt_top)
      (measure_mono hcover)) ?_
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  rw [MeasureTheory.measure_union h_disjoint hmeasimg,
    ENNReal.toReal_add, volume_image_sub_const] at hu
  · linarith
  · exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      isCompact_Icc.measure_lt_top)
  · rw [volume_image_sub_const]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      isCompact_Icc.measure_lt_top)

end ProductFree
