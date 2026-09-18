import RequestProject.Section4ContradictionAux
import RequestProject.Section4SecondGapPacking
import RequestProject.Section4GapAroundXAssembly
import RequestProject.Section4AGtTwoAssembly
import RequestProject.Section4TGtHalf
import RequestProject.Section4W

/-!
# Section 4: the boost equation and the pieces feeding `section4_fact_w`

This file assembles the paper's equation `boost and interval around a`
(`1 - t + g + (s-t)/2 < F(a) - F(a-2)`) from the geometric data already produced by the
Section 4 machinery, and provides the two remaining geometric packings needed for the
"w inequality" fact:

* `x_interval_mass_estimate`, the paper's `x interval mass estimate`
  `F(x+1) - F(x-1) ≤ 2 - s - (F(y)-F(y-2)) - (F(a+1)-F(b))`;
* `three_piece_packing_a`, the three-piece packing inside `[a,a+1]`
  `F(2) - F(2-w) + (F(a+1) - F(a)) ≤ 1`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- Brunn--Minkowski piece for the `x interval mass estimate`.  The sumset of `A ∩ [u'-a,u]`
and `A ∩ [b,a+1]` has measure at least `(F(u)-F(u'-a)) + (F(a+1)-F(b))` and is contained in
`[u'-a+b, u+a+1]`. -/
lemma xim_P2_bm
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b u u' : ℝ} (hua : u' - a ≤ u) (hu'a0 : 0 ≤ u' - a)
    (huA : u ∈ A) (hbA : b ∈ A) (hab : a ≤ b) (hba : b ≤ a + 1) :
    (cum A u - cum A (u' - a)) + (cum A (a + 1) - cum A b) ≤
      (volume ((A ∩ Icc (u' - a) u) + (A ∩ Icc b (a + 1)))).toReal ∧
    ((A ∩ Icc (u' - a) u) + (A ∩ Icc b (a + 1))) ⊆ Icc (u' - a + b) (u + a + 1) := by
  constructor
  · -- Measure inequality using Brunn-Minkowski
    have hmass1 : cum A u - cum A (u' - a) = (volume (A ∩ Icc (u' - a) u)).toReal :=
      cum_sub_cum_eq_mass_Icc hu'a0 hua
    have hmass2 : cum A (a + 1) - cum A b = (volume (A ∩ Icc b (a + 1))).toReal :=
      cum_sub_cum_eq_mass_Icc (by linarith [hab, hmin.2 hbA]) hba
    rw [hmass1, hmass2]
    -- Get interval union representations
    obtain ⟨ivsB, hB⟩ := hIU.inter_Icc_exists (u' - a) u
    obtain ⟨ivsC, hC⟩ := hIU.inter_Icc_exists b (a + 1)
    -- Nonemptiness: u ∈ A ∩ Icc (u' - a) u and b ∈ A ∩ Icc b (a + 1)
    have hneB : (A ∩ Icc (u' - a) u).Nonempty := ⟨u, huA, by simp [hua]⟩
    have hneC : (A ∩ Icc b (a + 1)).Nonempty := ⟨b, hbA, by simp [hba]⟩
    -- Nonempty lists
    have hneB' : ivsB ≠ [] := by
      by_contra h
      subst h
      simp [hB.2.2] at hneB
    have hneC' : ivsC ≠ [] := by
      by_contra h
      subst h
      simp [hC.2.2] at hneC
    -- Apply Brunn-Minkowski
    exact intervalUnion_add_measure_ge hB hC hneB' hneC'
  · -- Subset relation
    intro z hz
    rcases Set.mem_add.mp hz with ⟨x, hx, y, hy, rfl⟩
    exact Set.mem_Icc.mpr ⟨by simp_all; linarith, by simp_all; linarith⟩

/-- Translate-by-`a` piece of the `x interval mass estimate`.  For `a ∈ A`, the translate
`a + (A ∩ [p,q])` has the same measure `F(q) - F(p)` as `A ∩ [p,q]`, is contained in
`[a+p, a+q]`, and (by sum-freeness) is disjoint from `A`. -/
lemma xim_translate_piece
    (hsf : IsSumFree A) {a p q : ℝ} (haA : a ∈ A) (hp0 : 0 ≤ p) (hpq : p ≤ q) :
    (volume ((fun z => a + z) '' (A ∩ Icc p q))).toReal = cum A q - cum A p ∧
    (fun z => a + z) '' (A ∩ Icc p q) ⊆ Icc (a + p) (a + q) ∧
    Disjoint ((fun z => a + z) '' (A ∩ Icc p q)) A := by
  refine ⟨?_, ?_, ?_⟩
  · -- Measure equality
    rw [Set.image_add_left]
    rw [MeasureTheory.measure_preimage_add]
    rw [cum_sub_cum_eq_mass_Icc hp0 hpq]
  · -- Subset relation
    intro z hz
    rcases hz with ⟨z, ⟨hzA, hzI⟩, rfl⟩
    exact Set.mem_Icc.mpr ⟨by linarith [hzI.1], by linarith [hzI.2]⟩
  · -- Disjointness
    rw [Set.disjoint_left]
    intro z hz hzA
    rcases hz with ⟨w, ⟨hwA, _⟩, rfl⟩
    exact hsf haA hwA hzA

/-- Generic measure bound: four pairwise a.e.-disjoint measurable subsets of `J`, each
disjoint from `A`, contribute their total measure to `J \ A`. -/
lemma four_disjoint_forbidden {J G S1 S2 S3 : Set ℝ}
    (hGJ : G ⊆ J) (hS1J : S1 ⊆ J) (hS2J : S2 ⊆ J) (hS3J : S3 ⊆ J)
    (hGA : Disjoint G A) (hS1A : Disjoint S1 A) (hS2A : Disjoint S2 A) (hS3A : Disjoint S3 A)
    (hG : MeasurableSet G) (hS1 : MeasurableSet S1) (hS2 : MeasurableSet S2)
    (hS3 : MeasurableSet S3)
    (hJfin : volume J ≠ ⊤)
    (dG1 : AEDisjoint volume G S1) (dG2 : AEDisjoint volume G S2) (dG3 : AEDisjoint volume G S3)
    (d12 : AEDisjoint volume S1 S2) (d13 : AEDisjoint volume S1 S3)
    (d23 : AEDisjoint volume S2 S3) :
    (volume G).toReal + (volume S1).toReal + (volume S2).toReal + (volume S3).toReal ≤
      (volume (J \ A)).toReal := by
  have hsub : G ∪ S1 ∪ S2 ∪ S3 ⊆ J \ A := by
    rw [Set.union_subset_iff, Set.union_subset_iff, Set.union_subset_iff]
    refine ⟨⟨⟨fun z hz => ⟨hGJ hz, fun h => (hGA.le_bot ⟨hz, h⟩)⟩,
      fun z hz => ⟨hS1J hz, fun h => (hS1A.le_bot ⟨hz, h⟩)⟩⟩,
      fun z hz => ⟨hS2J hz, fun h => (hS2A.le_bot ⟨hz, h⟩)⟩⟩,
      fun z hz => ⟨hS3J hz, fun h => (hS3A.le_bot ⟨hz, h⟩)⟩⟩
  have hfin : volume (J \ A) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono (Set.diff_subset)) (lt_top_iff_ne_top.mpr hJfin))
  have fG : volume G ≠ ⊤ := ne_top_of_le_ne_top hJfin (measure_mono hGJ)
  have f1 : volume S1 ≠ ⊤ := ne_top_of_le_ne_top hJfin (measure_mono hS1J)
  have f2 : volume S2 ≠ ⊤ := ne_top_of_le_ne_top hJfin (measure_mono hS2J)
  have f3 : volume S3 ≠ ⊤ := ne_top_of_le_ne_top hJfin (measure_mono hS3J)
  have hunionvol : volume (G ∪ S1 ∪ S2 ∪ S3) =
      volume G + volume S1 + volume S2 + volume S3 := by
    rw [measure_union₀ hS3.nullMeasurableSet ((dG3.union_left d13).union_left d23),
      measure_union₀ hS2.nullMeasurableSet (dG2.union_left d12),
      measure_union₀ hS1.nullMeasurableSet dG1]
  have hle : volume (G ∪ S1 ∪ S2 ∪ S3) ≤ volume (J \ A) := measure_mono hsub
  have key := ENNReal.toReal_mono hfin hle
  rw [hunionvol,
    ENNReal.toReal_add (by finiteness) f3,
    ENNReal.toReal_add (by finiteness) f2,
    ENNReal.toReal_add fG f1] at key
  exact key

/-- **The forbidden-set core of the `x interval mass estimate`.**  Inside `J = [x-1,x+1]`
the complement of `A` has measure at least `s + (F(y)-F(y-2)) + (F(a+1)-F(b))`, coming from
the gap `[u',u'+s]` and the three disjoint sumset pieces described in the paper. -/
lemma xim_forbidden_set
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x u v u' v' : ℝ}
    (hab : a ≤ b) (hs1 : b - a ≤ 1) (ha2 : 2 ≤ a) (hbx : b < x)
    (hy3 : 3 < x + 1 - a)
    (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hvA : v ∈ A) (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z)
    (huv : 1 ≤ v - u)
    (hu'A : u' ∈ A) (hu'x : u' ≤ x) (hu'max : ∀ z ∈ A, z ≤ x → z ≤ u')
    (hv'A : v' ∈ A) (hxv' : x ≤ v') (hv'min : ∀ z ∈ A, x ≤ z → v' ≤ z)
    (huv' : 1 ≤ v' - u')
    (hvy : x + 1 - a - 1 ≤ v) (haA : a ∈ A) (hbA : b ∈ A)
    (hleftgap : A ∩ Icc (u + b - 1) x = ∅) :
    (b - a) + (cum A (x + 1 - a) - cum A (x + 1 - a - 2)) + (cum A (a + 1) - cum A b) ≤
      (volume (Icc (x - 1) (x + 1) \ A)).toReal := by
  have hmeas : MeasurableSet A := hIU.isClosed.measurableSet
  have ha1 : 1 ≤ a := by linarith
  have hone : (1 : ℝ) ∈ A := hmin.1
  -- Ordering facts.
  have hu'ge : x - 1 ≤ u' := hu'max (x - 1) hxleft (by linarith)
  have hu'lt : u' < u + b - 1 := by
    by_contra h; push_neg at h
    have hmem : u' ∈ A ∩ Icc (u + b - 1) x := ⟨hu'A, h, hu'x⟩
    rw [hleftgap] at hmem; exact hmem
  have huau : u' - a ≤ u := by linarith
  have hu'a0 : 0 ≤ u' - a := by linarith
  have hba : b ≤ a + 1 := by linarith
  -- Generic a.e.-disjointness of left/right interval-bounded sets.
  have aedisj : ∀ {P Q : Set ℝ} {c1 d1 c2 d2 : ℝ}, P ⊆ Icc c1 d1 → Q ⊆ Icc c2 d2 →
      d1 ≤ c2 → AEDisjoint volume P Q := by
    intro P Q c1 d1 c2 d2 hP hQ hd
    have hsub : P ∩ Q ⊆ Icc c2 d1 := fun z hz => ⟨(hQ hz.2).1, (hP hz.1).2⟩
    have hz : volume (Icc c2 d1) = 0 := by rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
    show volume (P ∩ Q) = 0
    exact le_antisymm (by rw [← hz]; exact measure_mono hsub) (zero_le _)
  -- The gap `G` around `x`.
  have hGsub : Ioo u' (u' + (b - a)) ⊆ Icc (x - 1) (x + 1) :=
    (Set.Ioo_subset_Icc_self).trans (Set.Icc_subset_Icc (by linarith)
      (by linarith [hv'min (x + 1) hxright (by linarith)]))
  have hv'ge : u' + (b - a) ≤ v' := by linarith
  have hGtight : Ioo u' (u' + (b - a)) ⊆ Icc u' (u' + (b - a)) := Set.Ioo_subset_Icc_self
  have hGA : Disjoint (Ioo u' (u' + (b - a))) A := by
    rw [Set.disjoint_left]; intro z hz hzA
    by_cases hzx : z ≤ x
    · exact absurd (hu'max z hzA hzx) (by linarith [hz.1])
    · push_neg at hzx; exact absurd (hv'min z hzA (le_of_lt hzx)) (by linarith [hz.2])
  have hGvol : (volume (Ioo u' (u' + (b - a)))).toReal = b - a := by
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; ring
  -- Piece `S1`.
  obtain ⟨hS1vol, hS1sub, hS1A⟩ :=
    xim_translate_piece hsf haA (show (0 : ℝ) ≤ x + 1 - a - 2 by linarith)
      (show x + 1 - a - 2 ≤ u' - a by linarith)
  have hS1sub' : (fun z => a + z) '' (A ∩ Icc (x + 1 - a - 2) (u' - a)) ⊆ Icc (x - 1) u' := by
    refine hS1sub.trans (Set.Icc_subset_Icc (by linarith) (by linarith))
  have hS1meas : MeasurableSet ((fun z => a + z) '' (A ∩ Icc (x + 1 - a - 2) (u' - a))) :=
    (measurableEmbedding_addLeft a).measurableSet_image.2 (hmeas.inter measurableSet_Icc)
  -- Piece `S2`.
  obtain ⟨hS2vol, hS2sub⟩ := xim_P2_bm hIU hsf hmin huau hu'a0 huA hbA hab hba
  have hS2sub' : (A ∩ Icc (u' - a) u) + (A ∩ Icc b (a + 1)) ⊆ Icc (u' + (b - a)) (u + a + 1) :=
    hS2sub.trans (Set.Icc_subset_Icc (by linarith) (by linarith))
  have hS2A : Disjoint ((A ∩ Icc (u' - a) u) + (A ∩ Icc b (a + 1))) A := by
    rw [Set.disjoint_left]; rintro z ⟨p, ⟨hpA, _⟩, q, ⟨hqA, _⟩, rfl⟩ hzA; exact hsf hpA hqA hzA
  have hS2meas : MeasurableSet ((A ∩ Icc (u' - a) u) + (A ∩ Icc b (a + 1))) := by
    have c1 : IsCompact (A ∩ Icc (u' - a) u) :=
      isCompact_Icc.of_isClosed_subset (hIU.isClosed.inter isClosed_Icc) inter_subset_right
    have c2 : IsCompact (A ∩ Icc b (a + 1)) :=
      isCompact_Icc.of_isClosed_subset (hIU.isClosed.inter isClosed_Icc) inter_subset_right
    exact (c1.add c2).measurableSet
  have hJfin : volume (Icc (x - 1) (x + 1)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- `cum A v = cum A u` across the gap `(u,v)`.
  have hcumvu : cum A v = cum A u := by
    have h1 : cum A v = cum A (x + 1 - a - 1) :=
      cum_eq_cum_of_least_after (by linarith) hvy hv_min
    have h2 : cum A (x + 1 - a - 1) = cum A u :=
      cum_eq_cum_of_greatest_before hmin huA (le_of_lt hu_lt) hu_max
    rw [h1, h2]
  by_cases hle : v ≤ x + 1 - a
  · -- Case `v ≤ y`: use the third translate piece.
    obtain ⟨hS3vol, hS3sub, hS3A⟩ :=
      xim_translate_piece hsf haA (show (0 : ℝ) ≤ v by linarith) hle
    have hS3sub' : (fun z => a + z) '' (A ∩ Icc v (x + 1 - a)) ⊆ Icc (a + v) (x + 1) :=
      hS3sub.trans (Set.Icc_subset_Icc (le_refl _) (by linarith))
    have hS3meas : MeasurableSet ((fun z => a + z) '' (A ∩ Icc v (x + 1 - a))) :=
      (measurableEmbedding_addLeft a).measurableSet_image.2 (hmeas.inter measurableSet_Icc)
    have hmain := four_disjoint_forbidden (A := A)
      (J := Icc (x - 1) (x + 1))
      (G := Ioo u' (u' + (b - a)))
      (S1 := (fun z => a + z) '' (A ∩ Icc (x + 1 - a - 2) (u' - a)))
      (S2 := (A ∩ Icc (u' - a) u) + (A ∩ Icc b (a + 1)))
      (S3 := (fun z => a + z) '' (A ∩ Icc v (x + 1 - a)))
      hGsub (hS1sub'.trans (Set.Icc_subset_Icc (le_refl _) (by linarith)))
      (hS2sub'.trans (Set.Icc_subset_Icc (by linarith) (by linarith)))
      (hS3sub'.trans (Set.Icc_subset_Icc (by linarith) (le_refl _)))
      hGA hS1A hS2A hS3A
      measurableSet_Ioo hS1meas hS2meas hS3meas hJfin
      ((aedisj hS1sub' hGtight (le_refl u')).symm)
      (aedisj hGtight hS2sub' (le_refl _))
      (aedisj hGtight hS3sub' (by linarith))
      (aedisj hS1sub' hS2sub' (by linarith))
      (aedisj hS1sub' hS3sub' (by linarith))
      (aedisj hS2sub' hS3sub' (by linarith))
    rw [hGvol, hS1vol] at hmain
    have hS3vol' : (volume ((fun z => a + z) '' (A ∩ Icc v (x + 1 - a)))).toReal =
        cum A (x + 1 - a) - cum A u := by rw [hS3vol, hcumvu]
    rw [hS3vol'] at hmain
    linarith [hS2vol]
  · -- Case `y < v`: the third piece is empty.
    push_neg at hle
    have hlt : x + 1 - a < v := hle
    have hcumy : cum A (x + 1 - a) = cum A u := by
      have h1 : cum A (x + 1 - a) = cum A (x + 1 - a - 1) := by
        have hempty : A ∩ Icc (x + 1 - a - 1) (x + 1 - a) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro z ⟨hzA, hz1, hz2⟩
          exact absurd (hv_min z hzA hz1) (by linarith)
        rw [← sub_eq_zero, cum_sub_cum_eq_mass_Icc (by linarith) (by linarith), hempty]
        simp
      rw [h1]
      exact cum_eq_cum_of_greatest_before hmin huA (le_of_lt hu_lt) hu_max
    have hmain := four_disjoint_forbidden (A := A)
      (J := Icc (x - 1) (x + 1))
      (G := Ioo u' (u' + (b - a)))
      (S1 := (fun z => a + z) '' (A ∩ Icc (x + 1 - a - 2) (u' - a)))
      (S2 := (A ∩ Icc (u' - a) u) + (A ∩ Icc b (a + 1)))
      (S3 := (∅ : Set ℝ))
      hGsub (hS1sub'.trans (Set.Icc_subset_Icc (le_refl _) (by linarith)))
      (hS2sub'.trans (Set.Icc_subset_Icc (by linarith) (by linarith)))
      (Set.empty_subset _)
      hGA hS1A hS2A disjoint_bot_left
      measurableSet_Ioo hS1meas hS2meas MeasurableSet.empty hJfin
      ((aedisj hS1sub' hGtight (le_refl u')).symm)
      (aedisj hGtight hS2sub' (le_refl _))
      (by simp [AEDisjoint])
      (aedisj hS1sub' hS2sub' (by linarith))
      (by simp [AEDisjoint])
      (by simp [AEDisjoint])
    rw [hGvol, hS1vol] at hmain
    simp only [measure_empty, ENNReal.toReal_zero] at hmain
    linarith [hS2vol, hcumy]

/-- **The `x interval mass estimate`.**  Inside `[x-1,x+1]` (length `2`) the set `A` misses
the gap `[u',u'+s]` of length `s` around `x`, and also misses a disjoint family of
sumset pieces of total measure at least `(F(y)-F(y-2)) + (F(a+1)-F(b))`, where
`y = x + 1 - a`.  Here `u,v` are the extremal points of `A` around `y-1` and `u',v'`
the extremal points of `A` around `x`. -/
lemma x_interval_mass_estimate
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x u v u' v' : ℝ}
    (hab : a ≤ b) (hs1 : b - a ≤ 1) (ha2 : 2 ≤ a) (hbx : b < x)
    (hy3 : 3 < x + 1 - a)
    (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hvA : v ∈ A) (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z)
    (huv : 1 ≤ v - u)
    (hu'A : u' ∈ A) (hu'x : u' ≤ x) (hu'max : ∀ z ∈ A, z ≤ x → z ≤ u')
    (hv'A : v' ∈ A) (hxv' : x ≤ v') (hv'min : ∀ z ∈ A, x ≤ z → v' ≤ z)
    (huv' : 1 ≤ v' - u')
    (hvy : x + 1 - a - 1 ≤ v) (haA : a ∈ A) (hbA : b ∈ A)
    (hleftgap : A ∩ Icc (u + b - 1) x = ∅) :
    cum A (x + 1) - cum A (x - 1) ≤
      2 - (b - a) - (cum A (x + 1 - a) - cum A (x + 1 - a - 2)) -
        (cum A (a + 1) - cum A b) := by
  have hforbidden := xim_forbidden_set hIU hsf hmin hab hs1 ha2 hbx hy3 hxleft hxright
    huA hu_lt hu_max hvA hv_min huv hu'A hu'x hu'max hv'A hxv' hv'min huv' hvy haA hbA hleftgap
  have hmeas : MeasurableSet A := hIU.isClosed.measurableSet
  have hxx : x - 1 ≤ x + 1 := by linarith
  -- Mass of `A` in `J = [x-1,x+1]`.
  have hAJ : (volume (A ∩ Icc (x - 1) (x + 1))).toReal = cum A (x + 1) - cum A (x - 1) := by
    rw [← cum_sub_cum_eq_mass_Icc (by linarith) hxx]
  -- Partition `J` into `J ∩ A` and `J \ A`.
  have hInterFin : volume (Icc (x - 1) (x + 1) ∩ A) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
  have hDiffFin : volume (Icc (x - 1) (x + 1) \ A) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono (Set.diff_subset))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
  have hpart := MeasureTheory.measure_inter_add_diff (μ := volume) (Icc (x - 1) (x + 1)) hmeas
  have hpartR : (volume (Icc (x - 1) (x + 1) ∩ A)).toReal +
      (volume (Icc (x - 1) (x + 1) \ A)).toReal = 2 := by
    have h := congrArg ENNReal.toReal hpart
    rw [ENNReal.toReal_add hInterFin hDiffFin, Real.volume_Icc] at h
    rw [h]; norm_num
  rw [Set.inter_comm] at hpartR
  linarith [hforbidden, hpartR, hAJ]

/-- **The three-piece packing inside `[a,a+1]`.**  Since `a-2+w ∈ A`, the translate
`(a-2+w) + (A ∩ [2-w,2])` lies in `[a,a+w] ⊆ [a,a+1]` and is disjoint from `A`.  Its
measure `F(2) - F(2-w)`, together with the mass `F(a+1) - F(a)` of `A ∩ [a,a+1]`, cannot
exceed the length `1`. -/
lemma three_piece_packing_a
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha1 : 1 ≤ a)
    (hwmem : a - 2 + w ∈ A) :
    cum A 2 - cum A (2 - w) + (cum A (a + 1) - cum A a) ≤ 1 := by
  have hmeasure_preserved : volume ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2)) =
      volume (A ∩ Icc (2 - w) 2) := by
    rw [show (fun z => a - 2 + w + z) = (fun z => z - (-(a - 2 + w))) from funext fun _ => by ring]
    exact volume_image_sub_const _ _
  have h1' : (volume (A ∩ Icc a (a + 1))).toReal +
      (volume ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2))).toReal ≤ 1 := by
    have hd : (fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2) ⊆ Icc a (a + 1) \ A := by
      rintro _ ⟨y, ⟨hyA, hyI⟩, rfl⟩
      refine ⟨by simp [add_comm, add_left_comm]; constructor <;> linarith [hyI.1, hyI.2], ?_⟩
      intro hz
      have : y + (a - 2 + w) ∈ A := by convert hz using 1; ring
      exact hsf hyA hwmem this
    have hA_sub : A ∩ Icc a (a + 1) ⊆ Icc a (a + 1) := inter_subset_right
    have htrans_sub : (fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2) ⊆ Icc a (a + 1) :=
      hd.trans Set.diff_subset
    have hdisj : (A ∩ Icc a (a + 1)) ∩ ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2)) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hxA, y, ⟨hyA, hyI⟩, hy⟩
      have hxy : a - 2 + w + y = x := hy
      have hxA' : a - 2 + w + y ∈ A := hxy ▸ hxA.1
      exact hd ⟨y, ⟨hyA, hyI⟩, rfl⟩ |>.2 hxA'
    have hunion_sub : (A ∩ Icc a (a + 1)) ∪ ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2)) ⊆ Icc a (a + 1) := by
      apply Set.union_subset hA_sub htrans_sub
    have hmeas_union : MeasureTheory.volume ((A ∩ Icc a (a + 1)) ∪ ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2))) ≤
        MeasureTheory.volume (Icc a (a + 1)) := MeasureTheory.measure_mono hunion_sub
    have hmeas_trans : MeasurableSet ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2)) := by
      have h3 : (fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2) =
          (fun z => z - (a - 2 + w)) ⁻¹' (A ∩ Icc (2 - w) 2) := by
        ext x
        constructor
        · rintro ⟨y, ⟨hyA, hyI⟩, rfl⟩
          show (fun z => z - (a - 2 + w)) (a - 2 + w + y) ∈ A ∩ Icc (2 - w) 2
          simp only [add_sub_cancel_left]
          exact ⟨hyA, hyI⟩
        · intro hx
          exact ⟨x - (a - 2 + w), ⟨hx.1, hx.2⟩, by ring⟩
      rw [h3]
      exact MeasurableSet.preimage (hA.inter measurableSet_Icc) (measurable_id.sub measurable_const)
    have hadd : MeasureTheory.volume ((A ∩ Icc a (a + 1)) ∪ ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2))) =
        MeasureTheory.volume (A ∩ Icc a (a + 1)) + MeasureTheory.volume ((fun z => a - 2 + w + z) '' (A ∩ Icc (2 - w) 2)) := by
      rw [MeasureTheory.measure_union (disjoint_iff.mpr hdisj) hmeas_trans]
    have hfinite1 : volume (A ∩ Icc a (a + 1)) ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (measure_mono hA_sub)
    have hfinite2' : volume (A ∩ Icc (2 - w) 2) ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num) (measure_mono (inter_subset_right))
    have hIcc : volume (Icc a (a + 1)) = 1 := by
      rw [Real.volume_Icc]; norm_num
    rw [hadd, hIcc] at hmeas_union
    simp_rw [hmeasure_preserved] at hmeas_union ⊢
    have hmeas_union' := ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hmeas_union
    rw [ENNReal.toReal_add hfinite1 hfinite2', ENNReal.toReal_one] at hmeas_union'
    linarith
  simp_rw [hmeasure_preserved] at h1'
  have hAacum : (volume (A ∩ Icc a (a + 1))).toReal = cum A (a + 1) - cum A a :=
    (cum_sub_cum_eq_mass_Icc (by linarith : (0 : ℝ) ≤ a) (by linarith : a ≤ a + 1)).symm
  have hBbcum : (volume (A ∩ Icc (2 - w) 2)).toReal = cum A 2 - cum A (2 - w) :=
    (cum_sub_cum_eq_mass_Icc (by linarith : (0 : ℝ) ≤ 2 - w) (by linarith : 2 - w ≤ 2)).symm
  rw [hAacum, hBbcum] at h1'
  linarith

/-- **The boost equation `boost and interval around a`.**  Assembled from the geometric
Section 4 data: `1 - t + g + (s-t)/2 < F(a) - F(a-2)` for some `g ≥ 0`. -/
lemma section4_assemble_boost_eq
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    ∃ g : ℝ, 0 ≤ g ∧
      1 - discOn A a b + g + (b - a - discOn A a b) / 2 < cum A a - cum A (a - 2) := by
  -- Parameters and basic facts.
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  obtain ⟨_hdisc, _hts, hs1, hbx, _hys, hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have ha1 : 1 ≤ a := hmin.2 haA
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  have hmass : cum A b - cum A a = (b - a + discOn A a b) / 2 := by
    rw [cum_sub_cum_eq_mass_Icc (by linarith) (le_of_lt hab)]; exact hmassIcc
  -- The gap immediately to the left of `x`, providing `u, v, g` and the identities.
  obtain ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
      hstrong, hu_gt, hreflect, hcum, hleftgap, hshortgap⟩ :=
    section4_assemble_gap_immediately_left_of_x hIU hsf hmin hx hxleft hxright hfail
      hab hbtop haA hbA hbal hmax htpos hε hneigh
  -- The gap of length one around `x`, providing `u', v'`.
  obtain ⟨u', v', hu'A, hu'x, hu'max, hv'A, hxv', hv'min, huv', hgapx⟩ :=
    section4_assemble_gap_around_x hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  -- The mass surplus in `[x,x+1]`.
  have hsurplus : 1 - discOn A a b < cum A (x + 1) - cum A x :=
    section4_first_mass_surplus hIU hsf hmin hx hmax hfail
  -- The `x interval mass estimate`.
  have hxint := x_interval_mass_estimate hIU hsf hmin (le_of_lt hab) hs1.le
    (le_of_lt ha2) (by linarith [hs1]) hy3 hxleft hxright huA hu_lt hu_max hvA hv_min huv
    hu'A hu'x hu'max hv'A hxv' hv'min huv' (by linarith [hv_gt, hs1]) haA hbA hleftgap
  -- Assemble the boost equation via the algebraic lemma.
  refine ⟨g, hg0, ?_⟩
  have := boost_eq_of_x_interval_mass hIU hsf (by linarith) (by linarith) (by linarith) hmax hfail
    hg hreflect hmass hsurplus hxint
  linarith

/-- The boost equation together with the direct-discrepancy identity `hg` that defines the
same deficit `g`.  This packages `section4_assemble_boost_eq` so that the `g` appearing in the
boost inequality is the *same* `g` satisfying the identity, as required by Lemma `c lem`. -/
lemma section4_assemble_boost_eq_with_id
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A) :
    ∃ g : ℝ, 0 ≤ g ∧
      2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = (x + 1 - a) - 3 - g ∧
      1 - discOn A a b + g + (b - a - discOn A a b) / 2 < cum A a - cum A (a - 2) := by
  have ha2 : 2 < a :=
    section4_assemble_a_gt_two hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  obtain ⟨_hdisc, _hts, hs1, hbx, _hys, hmassIcc⟩ :=
    section4_basic_parameters hIU hsf hmin hx hfail hab hbtop haA hbal hmax
  have ha1 : 1 ≤ a := hmin.2 haA
  have hy3 : 3 < x + 1 - a :=
    section4_assemble_y_gt_three hIU hsf hmin hx hxright hfail hab hbtop haA hbA
      hbal hmax hε hneigh
  have hmass : cum A b - cum A a = (b - a + discOn A a b) / 2 := by
    rw [cum_sub_cum_eq_mass_Icc (by linarith) (le_of_lt hab)]; exact hmassIcc
  obtain ⟨u, v, g, huA, hu_lt, hu_max, hvA, hv_gt, hv_min, huv, hg0, hg,
      hstrong, hu_gt, hreflect, hcum, hleftgap, hshortgap⟩ :=
    section4_assemble_gap_immediately_left_of_x hIU hsf hmin hx hxleft hxright hfail
      hab hbtop haA hbA hbal hmax htpos hε hneigh
  obtain ⟨u', v', hu'A, hu'x, hu'max, hv'A, hxv', hv'min, huv', hgapx⟩ :=
    section4_assemble_gap_around_x hIU hsf hmin hx hxleft hxright hfail hab hbtop haA hbA
      hbal hmax htpos hε hneigh
  have hsurplus : 1 - discOn A a b < cum A (x + 1) - cum A x :=
    section4_first_mass_surplus hIU hsf hmin hx hmax hfail
  have hxint := x_interval_mass_estimate hIU hsf hmin (le_of_lt hab) hs1.le
    (le_of_lt ha2) (by linarith [hs1]) hy3 hxleft hxright huA hu_lt hu_max hvA hv_min huv
    hu'A hu'x hu'max hv'A hxv' hv'min huv' (by linarith [hv_gt, hs1]) haA hbA hleftgap
  refine ⟨g, hg0, hg, ?_⟩
  have := boost_eq_of_x_interval_mass hIU hsf (by linarith) (by linarith) (by linarith) hmax hfail
    hg hreflect hmass hsurplus hxint
  linarith

end ProductFree
