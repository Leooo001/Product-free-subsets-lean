import RequestProject.Section4SecondGapAssembly

/-!
# Section 4: pieces of the two-translate packing estimate

This file decomposes the paper's two-translate measure-packing estimate into small,
independently provable measure-geometry lemmas, and assembles them into the estimate
`section4_two_translate_packing_assembled`.

Throughout, `I = [a,b]`, `y = x+1-a`, `s = b-a`, `t = discOn A a b`, and
`|I \ A| = (s-t)/2`.  The two "translated copies" are `u' - I` and `v' - I`, which as
sets equal `Icc (u'-b) (u'-a)` and `Icc (v'-b) (v'-a)`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ}

/-- Measure of an interval minus a measurable set, as a real number. -/
lemma volume_Icc_diff_toReal (E : Set ℝ) (hE : MeasurableSet E) (p q : ℝ) (hpq : p ≤ q) :
    (volume (Icc p q \ E)).toReal = (q - p) - (volume (E ∩ Icc p q)).toReal := by
  have hsub : E ∩ Icc p q ⊆ Icc p q := Set.inter_subset_right
  have hfin : volume (Icc p q) ≠ ⊤ := by simp [Real.volume_Icc]
  rw [show Icc p q \ E = Icc p q \ (E ∩ Icc p q) by ext z; simp]
  rw [MeasureTheory.measure_diff hsub (hE.inter measurableSet_Icc).nullMeasurableSet
    (ne_top_of_le_ne_top hfin (measure_mono hsub))]
  rw [ENNReal.toReal_sub_of_le (measure_mono hsub) hfin]
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- Reflection of a set through a point preserves Lebesgue measure. -/
lemma volume_image_const_sub (E : Set ℝ) (c : ℝ) :
    volume ((fun z => c - z) '' E) = volume E := by
  rw [show (fun z => c - z) '' E = (fun z => -z) '' E + ({c} : Set ℝ) by
    ext z; simp +decide [sub_eq_add_neg, add_comm]; aesop]
  simp +decide [Set.add_singleton]

/-- `Icc (c-b) (c-a)` is the reflection of `Icc a b` through `c`. -/
lemma Icc_eq_const_sub_image (a b c : ℝ) :
    Icc (c - b) (c - a) = (fun z => c - z) '' (Icc a b) := by
  rw [Set.image_const_sub_Icc]

/-- A least point of `A` at or after `q` carries no extra cumulative mass beyond `q`. -/
lemma cum_eq_cum_of_least_after
    {v q : ℝ} (hq0 : 0 ≤ q) (hqv : q ≤ v)
    (hv_least : ∀ z ∈ A, q ≤ z → v ≤ z) :
    cum A v = cum A q := by
  have hzero : volume (A ∩ Icc q v) = 0 := by
    apply MeasureTheory.measure_mono_null (show A ∩ Icc q v ⊆ ({v} : Set ℝ) by
      intro z hz
      exact Set.mem_singleton_iff.mpr (le_antisymm hz.2.2 (hv_least z hz.1 hz.2.1)))
    exact MeasureTheory.measure_singleton v
  have hmass : (volume (A ∩ Icc q v)).toReal = 0 := by rw [hzero]; rfl
  rw [← cum_sub_cum_eq_mass_Icc hq0 hqv] at hmass
  linarith

/-- If `A` has no mass strictly between `y-1` and `y`, the cumulative function is constant there. -/
lemma cum_y_eq_cum_y_sub_one_of_gap
    {y : ℝ} (h01 : 0 ≤ y - 1)
    (hgap : A ∩ Ioo (y - 1) y = ∅) :
    cum A y = cum A (y - 1) := by
  have hzero : volume (A ∩ Icc (y - 1) y) = 0 := by
    apply MeasureTheory.measure_mono_null
      (show A ∩ Icc (y - 1) y ⊆ ({y - 1, y} : Set ℝ) by
        intro z hz
        obtain ⟨hzA, hz1, hz2⟩ := hz
        rcases eq_or_lt_of_le hz1 with h | h
        · exact Or.inl h.symm
        rcases eq_or_lt_of_le hz2 with h2 | h2
        · exact Or.inr h2
        · exact absurd (Set.mem_inter hzA (Set.mem_Ioo.mpr ⟨h, h2⟩))
            (by rw [hgap]; exact Set.notMem_empty z))
    exact measure_union_null (measure_singleton _) (measure_singleton _)
  have hmass : (volume (A ∩ Icc (y - 1) y)).toReal = 0 := by rw [hzero]; rfl
  rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)] at hmass
  linarith

/-- **H1 — base packing with `A`-translates.**  The two translated copies of `A ∩ I`
are disjoint from `A`, so together with `A ∩ [y-2,u]` they pack into `[y-2,u]`. -/
lemma packing_base_A_translates
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a b u u' v' y : ℝ}
    (hu'A : u' ∈ A) (hv'A : v' ∈ A)
    (hy2 : 0 ≤ y - 2) (hyu : y - 2 ≤ u) :
    (volume ((((fun z => u' - z) '' (A ∩ Icc a b)) ∪
        ((fun z => v' - z) '' (A ∩ Icc a b))) ∩ Icc (y - 2) u)).toReal
      + (cum A u - cum A (y - 2)) ≤ u - y + 2 := by
  have hcum : cum A u - cum A (y - 2) = (volume (A ∩ Icc (y - 2) u)).toReal :=
    cum_sub_cum_eq_mass_Icc hy2 hyu
  have hTsub : ((((fun z => u' - z) '' (A ∩ Icc a b)) ∪
      ((fun z => v' - z) '' (A ∩ Icc a b))) ∩ Icc (y - 2) u) ⊆ Icc (y - 2) u \ A := by
    rintro w ⟨hwU, hwI⟩
    refine ⟨hwI, ?_⟩
    intro hwA
    rcases hwU with ⟨z, ⟨hzA, _⟩, rfl⟩ | ⟨z, ⟨hzA, _⟩, rfl⟩
    · exact hsf hzA hwA (by rw [show z + (u' - z) = u' from by ring]; exact hu'A)
    · exact hsf hzA hwA (by rw [show z + (v' - z) = v' from by ring]; exact hv'A)
  have hfin : volume (Icc (y - 2) u \ A) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.diff_subset)
  have hmono := ENNReal.toReal_mono hfin (measure_mono hTsub)
  rw [volume_Icc_diff_toReal A hA (y - 2) u (by linarith)] at hmono
  rw [hcum]
  linarith [hmono]

/-- **H2 — passing from `A`-translates to the full intervals.**  Enlarging `A ∩ I`
to `I` adds at most `|I \ A|` from the `u'` copy and at most `|[v'-u,b] \ A|` from the
`v'` copy (inside `[y-2,u]`). -/
lemma packing_full_le_A_translates
    (hA : MeasurableSet A)
    {a b u u' v' y t : ℝ} (hab : a ≤ b)
    (hmass : (volume (A ∩ Icc a b)).toReal = ((b - a) + t) / 2) :
    (volume ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩
        Icc (y - 2) u)).toReal
      ≤ (volume ((((fun z => u' - z) '' (A ∩ Icc a b)) ∪
          ((fun z => v' - z) '' (A ∩ Icc a b))) ∩ Icc (y - 2) u)).toReal
        + (b - a - t) / 2
        + (volume (Icc (v' - u) b \ A)).toReal := by
  set Au := (fun z => u' - z) '' (A ∩ Icc a b) with hAu
  set Av := (fun z => v' - z) '' (A ∩ Icc a b) with hAv
  set S := Icc (y - 2) u with hS
  set P1 := (Au ∪ Av) ∩ S with hP1
  set P2 := Icc (u' - b) (u' - a) \ Au with hP2
  set P3 := (Icc (v' - b) (v' - a) \ Av) ∩ S with hP3
  have hincl : (Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩ S ⊆ P1 ∪ P2 ∪ P3 := by
    rintro w ⟨hwF, hwS⟩
    rcases hwF with hwFu | hwFv
    · by_cases hwAu : w ∈ Au
      · exact Or.inl (Or.inl ⟨Or.inl hwAu, hwS⟩)
      · exact Or.inl (Or.inr ⟨hwFu, hwAu⟩)
    · by_cases hwAv : w ∈ Av
      · exact Or.inl (Or.inl ⟨Or.inr hwAv, hwS⟩)
      · exact Or.inr ⟨⟨hwFv, hwAv⟩, hwS⟩
  -- P2 lies in the reflected copy of `[a,b] \ A` through `u'`
  have hP2sub : P2 ⊆ (fun z => u' - z) '' (Icc a b \ A) := by
    rintro w ⟨hwF, hwAu⟩
    have hz : u' - w ∈ Icc a b := by
      rcases hwF with ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    refine ⟨u' - w, ⟨hz, ?_⟩, by ring⟩
    intro hmem
    exact hwAu ⟨u' - w, ⟨hmem, hz⟩, by ring⟩
  -- P3 lies in the reflected copy of `[v'-u,b] \ A` through `v'`
  have hP3sub : P3 ⊆ (fun z => v' - z) '' (Icc (v' - u) b \ A) := by
    rintro w ⟨⟨hwF, hwAv⟩, hwS⟩
    have hz : v' - w ∈ Icc a b := by
      rcases hwF with ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    have hzu : v' - u ≤ v' - w := by rcases hwS with ⟨_, h2⟩; linarith
    refine ⟨v' - w, ⟨⟨hzu, hz.2⟩, ?_⟩, by ring⟩
    intro hmem
    exact hwAv ⟨v' - w, ⟨hmem, hz⟩, by ring⟩
  -- measure of the `u'` copy correction is exactly `(b-a-t)/2`
  have himgU : volume ((fun z => u' - z) '' (Icc a b \ A)) = volume (Icc a b \ A) :=
    volume_image_const_sub _ _
  have hP2fin : volume ((fun z => u' - z) '' (Icc a b \ A)) ≠ ⊤ := by
    rw [himgU]; exact ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.diff_subset)
  have hvP2 : (volume P2).toReal ≤ (b - a - t) / 2 := by
    have hle := ENNReal.toReal_mono hP2fin (measure_mono hP2sub)
    rw [himgU, volume_Icc_diff_toReal A hA a b hab, hmass] at hle
    linarith [hle]
  -- measure of the `v'` copy correction is at most `|[v'-u,b] \ A|`
  have himgV : volume ((fun z => v' - z) '' (Icc (v' - u) b \ A)) = volume (Icc (v' - u) b \ A) :=
    volume_image_const_sub _ _
  have hP3fin : volume ((fun z => v' - z) '' (Icc (v' - u) b \ A)) ≠ ⊤ := by
    rw [himgV]; exact ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.diff_subset)
  have hvP3 : (volume P3).toReal ≤ (volume (Icc (v' - u) b \ A)).toReal := by
    have hle := ENNReal.toReal_mono hP3fin (measure_mono hP3sub)
    rwa [himgV] at hle
  -- finiteness of the three packing pieces
  have hfinP1 : volume P1 ≠ ⊤ :=
    ne_top_of_le_ne_top (show volume S ≠ ⊤ by rw [hS]; simp [Real.volume_Icc])
      (by rw [hP1]; exact measure_mono Set.inter_subset_right)
  have hfinP2 : volume P2 ≠ ⊤ :=
    ne_top_of_le_ne_top (show volume (Icc (u' - b) (u' - a)) ≠ ⊤ by simp [Real.volume_Icc])
      (by rw [hP2]; exact measure_mono Set.diff_subset)
  have hfinP3 : volume P3 ≠ ⊤ :=
    ne_top_of_le_ne_top (show volume S ≠ ⊤ by rw [hS]; simp [Real.volume_Icc])
      (by rw [hP3]; exact measure_mono Set.inter_subset_right)
  -- subadditive packing bound
  have h2 : volume (P1 ∪ P2 ∪ P3) ≤ volume P1 + volume P2 + volume P3 :=
    le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _)
  have hfinsum : volume P1 + volume P2 + volume P3 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfinP1, hfinP2⟩, hfinP3⟩
  have hLHS := ENNReal.toReal_mono hfinsum (le_trans (measure_mono hincl) h2)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinP1, hfinP2⟩) hfinP3,
      ENNReal.toReal_add hfinP1 hfinP2] at hLHS
  linarith [hLHS, hvP2, hvP3]

/-- The single complement term `C1 = |[v'-u,b] \ A|` is at most `|I \ A| = (s-t)/2`
when `[v'-u,b] ⊆ [a,b]`. -/
lemma packing_C1_le
    (hA : MeasurableSet A) {a b u v' t : ℝ} (hab : a ≤ b)
    (hmass : (volume (A ∩ Icc a b)).toReal = ((b - a) + t) / 2)
    (hva : a ≤ v' - u) :
    (volume (Icc (v' - u) b \ A)).toReal ≤ (b - a - t) / 2 := by
  have hsub : Icc (v' - u) b \ A ⊆ Icc a b \ A :=
    Set.diff_subset_diff_left (Set.Icc_subset_Icc hva le_rfl)
  have hfin : volume (Icc a b \ A) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.diff_subset)
  have hmono := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [volume_Icc_diff_toReal A hA a b hab, hmass] at hmono
  linarith

/-- The two complement terms `C1 = |[v'-u,b] \ A|` and `C2 = |[a,a+y-v] \ A|` are
disjoint subintervals of `I`, so together they are at most `|I \ A| = (s-t)/2`. -/
lemma packing_C1_C2_le
    (hA : MeasurableSet A) {a b u v v' y t : ℝ} (hab : a ≤ b)
    (hmass : (volume (A ∩ Icc a b)).toReal = ((b - a) + t) / 2)
    (hc2a : a ≤ a + y - v) (hc2b : a + y - v ≤ b)
    (hdisj : a + y - v ≤ v' - u) :
    (volume (Icc (v' - u) b \ A)).toReal
        + (volume (Icc a (a + y - v) \ A)).toReal ≤ (b - a - t) / 2 := by
  set X := Icc (v' - u) b \ A with hX
  set Y := Icc a (a + y - v) \ A with hY
  have hYm : MeasurableSet Y := measurableSet_Icc.diff hA
  have hXsub : X ⊆ Icc a b \ A :=
    Set.diff_subset_diff_left (Set.Icc_subset_Icc (le_trans hc2a hdisj) le_rfl)
  have hYsub : Y ⊆ Icc a b \ A :=
    Set.diff_subset_diff_left (Set.Icc_subset_Icc le_rfl hc2b)
  have hinter0 : volume (X ∩ Y) = 0 := by
    apply measure_mono_null (show X ∩ Y ⊆ ({v' - u} : Set ℝ) by
      rintro z ⟨⟨hzX, _⟩, ⟨hzY, _⟩⟩
      exact Set.mem_singleton_iff.mpr (le_antisymm (le_trans hzY.2 hdisj) hzX.1))
    exact measure_singleton _
  have hfin : volume (Icc a b \ A) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.diff_subset)
  have hXfin : volume X ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono hXsub)
  have hYfin : volume Y ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono hYsub)
  have hadd := MeasureTheory.measure_union_add_inter (μ := volume) X hYm
  rw [hinter0, add_zero] at hadd
  have hunion : volume (X ∪ Y) ≤ volume (Icc a b \ A) :=
    measure_mono (Set.union_subset hXsub hYsub)
  have hsum : volume X + volume Y ≤ volume (Icc a b \ A) := hadd ▸ hunion
  have hgoal : (volume X).toReal + (volume Y).toReal ≤ (volume (Icc a b \ A)).toReal := by
    rw [← ENNReal.toReal_add hXfin hYfin]
    exact ENNReal.toReal_mono hfin hsum
  rw [volume_Icc_diff_toReal A hA a b hab, hmass] at hgoal
  linarith [hgoal]

/-- The reflection through `x+1` bounds `F(y) - F(v)` by `C2 = |[a,a+y-v] \ A|`. -/
lemma packing_reflection_C2
    (hA : MeasurableSet A) (hsf : IsSumFree A)
    {a x v y : ℝ} (hxA : x + 1 ∈ A) (ha : a = x + 1 - y)
    (hv0 : 0 ≤ v) (hvy : v ≤ y) :
    cum A y - cum A v ≤ (volume (Icc a (a + y - v) \ A)).toReal := by
  rw [cum_sub_cum_eq_mass_Icc hv0 hvy]
  have hrefl := reflection_mass_le_interval_complement hA hsf hxA hvy
    (show a = (x + 1) - y by linarith) (show a + y - v = (x + 1) - v by linarith)
  rw [volume_Icc_diff_toReal A hA a (a + y - v) (by linarith)]
  linarith [hrefl]

/-- **Assembled two-translate packing estimate.**  This matches the statement needed by
`section4_assemble_gap_around_x_of_packing`. -/
lemma section4_two_translate_packing_assembled
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b u v u' v' : ℝ}
    (hxright : x + 1 ∈ A) (hy3 : 3 < x + 1 - a)
    (hab : a < b) (hslt : b - a < 1)
    (hmass : (volume (A ∩ Icc a b)).toReal = ((b - a) + discOn A a b) / 2)
    (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1) (hu_gt : x + 1 - a - 2 < u)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z)
    (huv : 1 ≤ v - u)
    (hu'A : u' ∈ A) (hu'x : u' < x)
    (hv'A : v' ∈ A) (hxv' : x < v')
    (hleftgap : A ∩ Icc (u + b - 1) x = ∅)
    (hshort : v' - u' < 1) :
    (volume ((Icc (u' - b) (u' - a) ∪ Icc (v' - b) (v' - a)) ∩
      Icc (x + 1 - a - 2) u)).toReal +
        (cum A (x + 1 - a) - cum A (x + 1 - a - 2))
      ≤ u - (x + 1 - a) + 2 + (b - a) - discOn A a b := by
  set y := x + 1 - a with hy
  set t := discOn A a b with ht
  -- base packing (H1) and the passage to full intervals (H2)
  have H1 := packing_base_A_translates (A := A) hA hsf (a := a) (b := b) (u := u)
    (u' := u') (v' := v') (y := y) hu'A hv'A (by linarith) (by linarith)
  have H2 := packing_full_le_A_translates (A := A) hA (a := a) (b := b) (u := u)
    (u' := u') (v' := v') (y := y) (t := t) hab.le hmass
  -- `u` carries all mass up to `y-1`
  have hFu : cum A (y - 1) = cum A u :=
    cum_eq_cum_of_greatest_before hmin huA (by linarith) hu_max
  -- geometric facts placing `u'` and `v'` relative to `u+b`
  have hu'ub : u' < u + b - 1 := by
    by_contra h; push_neg at h
    have hmem : u' ∈ A ∩ Icc (u + b - 1) x := ⟨hu'A, h, le_of_lt hu'x⟩
    rw [hleftgap] at hmem; exact hmem
  have hav : a ≤ v' - u := by
    have : a = x + 1 - y := by rw [hy]; ring
    linarith [hu_lt, hxv']
  have hvb : v' - u ≤ b := by linarith [hu'ub, hshort]
  rcases le_or_gt y v with hvcase | hvcase
  · -- Case `v ≥ y`: no mass in `(y-1,y)` and `C1 ≤ (s-t)/2`
    have hgap : A ∩ Ioo (y - 1) y = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzA, hz1, hz2⟩
      have := hv_min z hzA (by linarith)
      linarith
    have hgapeq : cum A y = cum A (y - 1) :=
      cum_y_eq_cum_y_sub_one_of_gap (by linarith) hgap
    have hC1 := packing_C1_le (A := A) hA (a := a) (b := b) (u := u)
      (v' := v') (t := t) hab.le hmass hav
    linarith [H1, H2, hFu, hgapeq, hC1]
  · -- Case `v < y`: reflection bound and `C1 + C2 ≤ (s-t)/2`
    have hFv : cum A v = cum A (y - 1) :=
      cum_eq_cum_of_least_after (by linarith) (by linarith) hv_min
    have hrefl := packing_reflection_C2 (A := A) hA hsf (a := a) (x := x) (v := v)
      (y := y) hxright (by rw [hy]; ring) (by linarith) (le_of_lt hvcase)
    have hC1C2 := packing_C1_C2_le (A := A) hA (a := a) (b := b) (u := u) (v := v)
      (v' := v') (y := y) (t := t) hab.le hmass (by linarith) (by linarith)
      (by
        have : a = x + 1 - y := by rw [hy]; ring
        linarith [huv, hxv'])
    linarith [H1, H2, hFu, hFv, hrefl, hC1C2]

end ProductFree
