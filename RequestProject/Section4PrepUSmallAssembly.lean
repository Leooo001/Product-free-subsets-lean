import RequestProject.Section4ULtTwoFull
import RequestProject.Section4ContradictionAux
import RequestProject.Section4GapAroundXAssembly
import RequestProject.Section4SecondGapPacking
import RequestProject.Section4MInterv
import RequestProject.Section4MZero
import RequestProject.Section4YBound
import RequestProject.Section4BoostEq
import RequestProject.Section4BMDiff

/-!
# Section 4: the three cases of equation "prep u small"

This file discharges the three geometric case hypotheses fed to `prep_u_small_all_cases`
in the proof of `section4_fact_hprep`.  All of the extremal data around `y-1` (the point
`u < 2`) and the gap around `x` (the points `u', v'`) is passed in explicitly; each lemma
proves the packing conjunction relevant to one of the paper's three order alternatives.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- **Case 1** (`y < v`).  The reflection `(A∩[v',x+1]) - (A∩[x-1,u'])` lies in `[1,2]` and is
disjoint from `A`, giving the packing inequality; `F(y) = F(2)` because there is no mass in
`(u,v)` and `2 < y < v`. -/
lemma section4_hprep_case1
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    {u v g u' v' : ℝ} (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hvA : v ∈ A) (hv_gt : x + 1 - a - (b - a) < v)
    (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z) (huv : 1 ≤ v - u) (hg0 : 0 ≤ g)
    (hg : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = x + 1 - a - 3 - g)
    (hstrong : 5 / 4 * (1 - discOn A a b) + g / 2 < cum A (x + 1 - a) - cum A (x + 1 - a - 2))
    (hu_gt : x + 1 - a - 2 < u)
    (hreflect : cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2)
    (hcum : cum A (x + 1 - a - 1) = cum A u)
    (hgap : A ∩ Icc (u + b - 1) x = ∅) (hshort : A ∩ Icc (x + (b - a) - 1) x = ∅)
    (hu2 : u < 2)
    (hu'A : u' ∈ A) (hu'x : u' ≤ x) (hu'max : ∀ z ∈ A, z ≤ x → z ≤ u')
    (hv'A : v' ∈ A) (hxv' : x ≤ v') (hv'min : ∀ z ∈ A, x ≤ z → v' ≤ z)
    (huv' : 1 ≤ v' - u') (hgap' : ∀ z ∈ Ioo u' v', z ∉ A)
    (hy3 : 3 < x + 1 - a) (ha2 : 2 < a)
    (hdiffeq : 2 * cum A (x - 1) + cum A (a - 2) ≤ a - 2 + discOn A a b + 2 * cum A (x + 1 - a)) :
    x + 1 - a < v →
      cum A (x + 1 - a) = cum A 2 ∧
      cum A (x + 1) - cum A v' + (cum A u' - cum A (x - 1)) + cum A 2 ≤ 1 ∧
      cum A u' = cum A v' := by
  intro hyv
  have hu'ge1 : 1 ≤ u' := hmin.2 hu'A
  have hu'0 : 0 ≤ u' := by linarith
  have hv'x1 : v' ≤ x + 1 := hv'min (x + 1) hxright (by linarith)
  have hx1u' : x - 1 ≤ u' := hu'max (x - 1) hxleft (by linarith)
  -- (iii) `F(u') = F(v')`.
  have huv'le : u' ≤ v' := by linarith [huv']
  have hu'v' : cum A u' = cum A v' := by
    have hmass : cum A v' - cum A u' = (volume (A ∩ Icc u' v')).toReal :=
      cum_sub_cum_eq_mass_Icc (by linarith) huv'le
    have hz : A ∩ Icc u' v' ⊆ {u', v'} := by
      rintro z ⟨hzA, hz1, hz2⟩
      rcases eq_or_lt_of_le hz1 with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h.symm)
      · rcases eq_or_lt_of_le hz2 with h' | h'
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h'))
        · exact absurd hzA (hgap' z ⟨h, h'⟩)
    have hpair : volume ({u', v'} : Set ℝ) = 0 :=
      ((Set.finite_singleton v').insert u').countable.measure_zero volume
    have : volume (A ∩ Icc u' v') = 0 := measure_mono_null hz hpair
    rw [this] at hmass; simp at hmass; linarith
  -- (i) `F(y) = F(2)`.
  have hFy2 : cum A (x + 1 - a) = cum A 2 := by
    have hmass : cum A (x + 1 - a) - cum A 2 = (volume (A ∩ Icc 2 (x + 1 - a))).toReal :=
      cum_sub_cum_eq_mass_Icc (by norm_num) (by linarith)
    have hempty : A ∩ Icc 2 (x + 1 - a) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzA, hz1, hz2⟩
      rcases le_or_gt z (x + 1 - a - 1) with h | h
      · have := hu_max z hzA h; linarith
      · have := hv_min z hzA (by linarith); linarith
    rw [hempty] at hmass; simp at hmass; linarith
  refine ⟨hFy2, ?_, hu'v'⟩
  -- (ii) reflection packing.
  have hpack := reflect_diff_packing hIU hsf (p := v') (q := x + 1) (r := x - 1)
    (s := u') (L := 1) (R := 2) (by linarith) hv'x1 (by linarith) hx1u'
    (by norm_num) (by norm_num) (wB := x + 1) (wC := x - 1)
    ⟨hxright, by simp; linarith⟩ ⟨hxleft, by simp; linarith⟩
    (Set.Icc_subset_Icc (by linarith [huv']) (by norm_num))
  rw [cum_one_eq_zero_of_isLeast hmin] at hpack
  linarith

/-- **Case 2** (`v ≤ y` and `v' ≤ v + a`).  Combines the reflection packing of
`(A∩[v',v+a]) - (A∩[x-1,u'])` with the `minterv` sumset estimate on `[v,y]`, using
`F(v) = F(2)` and the lower bound `F(v-y+2) ≥ F(2)-(y-3)`. -/
lemma section4_hprep_case2
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    {u v g u' v' : ℝ} (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hvA : v ∈ A) (hv_gt : x + 1 - a - (b - a) < v)
    (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z) (huv : 1 ≤ v - u) (hg0 : 0 ≤ g)
    (hg : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = x + 1 - a - 3 - g)
    (hstrong : 5 / 4 * (1 - discOn A a b) + g / 2 < cum A (x + 1 - a) - cum A (x + 1 - a - 2))
    (hu_gt : x + 1 - a - 2 < u)
    (hreflect : cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2)
    (hcum : cum A (x + 1 - a - 1) = cum A u)
    (hgap : A ∩ Icc (u + b - 1) x = ∅) (hshort : A ∩ Icc (x + (b - a) - 1) x = ∅)
    (hu2 : u < 2)
    (hu'A : u' ∈ A) (hu'x : u' ≤ x) (hu'max : ∀ z ∈ A, z ≤ x → z ≤ u')
    (hv'A : v' ∈ A) (hxv' : x ≤ v') (hv'min : ∀ z ∈ A, x ≤ z → v' ≤ z)
    (huv' : 1 ≤ v' - u') (hgap' : ∀ z ∈ Ioo u' v', z ∉ A)
    (hy3 : 3 < x + 1 - a) (ha2 : 2 < a)
    (hdiffeq : 2 * cum A (x - 1) + cum A (a - 2) ≤ a - 2 + discOn A a b + 2 * cum A (x + 1 - a)) :
    v ≤ x + 1 - a →
      v' ≤ v + a →
        cum A (x + 1) - cum A (x - 1) + cum A (v - (x + 1 - a) + 2) +
            2 * (cum A (x + 1 - a) - cum A v) ≤ 1 ∧
          cum A v = cum A 2 ∧ cum A 2 - (x + 1 - a - 3) ≤ cum A (v - (x + 1 - a) + 2) := by
  intro hvy hv'le
  have hs1 : b - a < 1 := hsf.balanced_length_lt_one hIU.isCompact hmin.1 hab hbal
  have hvge1 : x + 1 - a - 1 < v := by linarith [hv_gt]
  have hu1 : 1 ≤ u := hmin.2 huA
  have hu'ge1 : 1 ≤ u' := hmin.2 hu'A
  have hx1u' : x - 1 ≤ u' := hu'max (x - 1) hxleft (by linarith)
  have hv'0 : 0 ≤ v' := by linarith
  -- `F(u) = F(2)`.
  have hFu2 : cum A u = cum A 2 := by
    have hmass : cum A 2 - cum A u = (volume (A ∩ Icc u 2)).toReal :=
      cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)
    have hz : A ∩ Icc u 2 ⊆ {u} := by
      rintro z ⟨hzA, hz1, hz2⟩
      rcases eq_or_lt_of_le hz1 with h | h
      · exact Set.mem_singleton_iff.mpr h.symm
      · exact absurd (hu_max z hzA (by linarith)) (by linarith)
    have : volume (A ∩ Icc u 2) = 0 := measure_mono_null hz (measure_singleton u)
    rw [this] at hmass; simp at hmass; linarith
  -- `F(v) = F(2)`.
  have hFv2 : cum A v = cum A 2 := by
    have hmass : cum A v - cum A 2 = (volume (A ∩ Icc 2 v)).toReal :=
      cum_sub_cum_eq_mass_Icc (by norm_num) (by linarith)
    have hz : A ∩ Icc 2 v ⊆ {v} := by
      rintro z ⟨hzA, hz1, hz2⟩
      rcases eq_or_lt_of_le hz2 with h | h
      · exact Set.mem_singleton_iff.mpr h
      · rcases le_or_gt z (x + 1 - a - 1) with h' | h'
        · exact absurd (hu_max z hzA h') (by linarith)
        · exact absurd (hv_min z hzA (le_of_lt h')) (by linarith)
    have : volume (A ∩ Icc 2 v) = 0 := measure_mono_null hz (measure_singleton v)
    rw [this] at hmass; simp at hmass; linarith
  -- `(C)` lower bound on `F(v-y+2)`.
  have hmono1 : cum A (u - (x + 1 - a) + 3) ≤ cum A (v - (x + 1 - a) + 2) :=
    section4_cum_mono (by linarith) (by linarith [huv])
  have hlen : cum A u - cum A (u - (x + 1 - a) + 3) ≤ (x + 1 - a) - 3 := by
    have hm : cum A u - cum A (u - (x + 1 - a) + 3) =
        (volume (A ∩ Icc (u - (x + 1 - a) + 3) u)).toReal :=
      cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)
    rw [hm]
    refine le_trans (ENNReal.toReal_mono (ne_of_lt isCompact_Icc.measure_lt_top)
      (measure_mono Set.inter_subset_right)) ?_
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; linarith
  have hClow : cum A 2 - (x + 1 - a - 3) ≤ cum A (v - (x + 1 - a) + 2) := by
    rw [← hFu2]; linarith
  refine ⟨?_, hFv2, hClow⟩
  -- `(A)`: reflection packing + sumset packing.
  have hmy : mMinus A (x + 1 - a) = 0 := by
    apply mzero hIU.isClosed hIU.isCompact.measure_lt_top.ne hsf
      (fun z hz => le_trans zero_le_one (hmin.2 hz)) hab (by linarith) hbal hmax
    left; rw [show a + (x + 1 - a) = x + 1 from by ring]; exact hxright
  have hdiscvy : disc (A ∩ Icc v (x + 1 - a)) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by linarith) (by linarith) hmax
  have hsum := minterv_sumset_packing hIU hsf hab hbal hmy (α := v) (β := x + 1 - a)
    (by linarith) (by linarith) hvy hdiscvy
  rw [show a + (x + 1 - a) = x + 1 from by ring, show a + v = v + a from by ring] at hsum
  have hu'v' : cum A u' = cum A v' := by
    have hmass : cum A v' - cum A u' = (volume (A ∩ Icc u' v')).toReal :=
      cum_sub_cum_eq_mass_Icc (by linarith) (by linarith [huv'])
    have hz : A ∩ Icc u' v' ⊆ {u', v'} := by
      rintro z ⟨hzA, hz1, hz2⟩
      rcases eq_or_lt_of_le hz1 with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h.symm)
      · rcases eq_or_lt_of_le hz2 with h' | h'
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h'))
        · exact absurd hzA (hgap' z ⟨h, h'⟩)
    have hpair : volume ({u', v'} : Set ℝ) = 0 :=
      ((Set.finite_singleton v').insert u').countable.measure_zero volume
    have : volume (A ∩ Icc u' v') = 0 := measure_mono_null hz hpair
    rw [this] at hmass; simp at hmass; linarith
  have hrefl := reflect_diff_packing hIU hsf (p := v') (q := v + a) (r := x - 1)
    (s := u') (L := 1) (R := v - (x + 1 - a) + 2) hv'0 hv'le (by linarith) hx1u'
    (by norm_num) (by linarith) (wB := v') (wC := x - 1)
    ⟨hv'A, Set.mem_Icc.mpr ⟨le_refl _, hv'le⟩⟩
    ⟨hxleft, Set.mem_Icc.mpr ⟨le_refl _, hx1u'⟩⟩
    (Set.Icc_subset_Icc (by linarith [huv']) (by linarith))
  rw [cum_one_eq_zero_of_isLeast hmin] at hrefl
  linarith

/-- **Case 3** (`v ≤ y` and `v + a < v'`).  Here `y - v ≥ s`, `A` has no mass in `[x,v+a]`, so
`F(v+a) = F(x) = F(x-1)`; the reflection and `minterv` sumset packings then give both
estimates. -/
lemma section4_hprep_case3
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {x a b ε : ℝ} (hx : 1 ≤ x) (hxleft : x - 1 ∈ A) (hxright : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A) (hbA : b ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (htpos : 0 < discOn A a b)
    (hε : 0 < ε) (hneigh : Icc (x - 1 - ε) (x - 1 + ε) ⊆ A)
    {u v g u' v' : ℝ} (huA : u ∈ A) (hu_lt : u < x + 1 - a - 1)
    (hu_max : ∀ z ∈ A, z ≤ x + 1 - a - 1 → z ≤ u)
    (hvA : v ∈ A) (hv_gt : x + 1 - a - (b - a) < v)
    (hv_min : ∀ z ∈ A, x + 1 - a - 1 ≤ z → v ≤ z) (huv : 1 ≤ v - u) (hg0 : 0 ≤ g)
    (hg : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = x + 1 - a - 3 - g)
    (hstrong : 5 / 4 * (1 - discOn A a b) + g / 2 < cum A (x + 1 - a) - cum A (x + 1 - a - 2))
    (hu_gt : x + 1 - a - 2 < u)
    (hreflect : cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2)
    (hcum : cum A (x + 1 - a - 1) = cum A u)
    (hgap : A ∩ Icc (u + b - 1) x = ∅) (hshort : A ∩ Icc (x + (b - a) - 1) x = ∅)
    (hu2 : u < 2)
    (hu'A : u' ∈ A) (hu'x : u' ≤ x) (hu'max : ∀ z ∈ A, z ≤ x → z ≤ u')
    (hv'A : v' ∈ A) (hxv' : x ≤ v') (hv'min : ∀ z ∈ A, x ≤ z → v' ≤ z)
    (huv' : 1 ≤ v' - u') (hgap' : ∀ z ∈ Ioo u' v', z ∉ A)
    (hy3 : 3 < x + 1 - a) (ha2 : 2 < a)
    (hdiffeq : 2 * cum A (x - 1) + cum A (a - 2) ≤ a - 2 + discOn A a b + 2 * cum A (x + 1 - a)) :
    v ≤ x + 1 - a →
      v + a < v' →
        cum A (v + a) - cum A (x - 1) + cum A (v - (x + 1 - a) + 2) ≤ v + a - x ∧
          2 * (cum A (x + 1 - a) - cum A v) + (cum A (x + 1) - cum A (v + a)) ≤
              x + 1 - (v + a) ∧
            cum A v = cum A 2 ∧ cum A 2 - (x + 1 - a - 3) ≤ cum A (v - (x + 1 - a) + 2) := by
  intro hvy hv'gt
  -- The premises of Case 3 are contradictory: the gap around `x` together with `v - u ≥ 1`
  -- forces `y - v < s`, which the translate packing then refutes.
  exfalso
  have ha1 : 1 ≤ a := hmin.2 haA
  have hu1 : 1 ≤ u := hmin.2 huA
  have hs1 : b - a < 1 := hsf.balanced_length_lt_one hIU.isCompact hmin.1 hab hbal
  -- `x - 1 < u + b - 1` (else `x-1` lies in the forced gap `[u+b-1,x]`).
  have hstar : x - 1 < u + b - 1 := by
    by_contra h; push_neg at h
    have hmem : x - 1 ∈ A ∩ Icc (u + b - 1) x := ⟨hxleft, h, by linarith⟩
    rw [hgap] at hmem; exact hmem
  -- Hence `y - v < s`.
  have hvax : x < v + a := by
    have hvv : x + 1 - a - 1 < v := by linarith [hv_gt]
    linarith
  set d := (x + 1 - a) - v with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  have hva_eq : v + a = x + 1 - d := by rw [hd]; ring
  have hdlt : d < b - a := by rw [hd]; linarith [huv]
  -- `F(v+a) = F(x)`.
  have hFva : cum A (v + a) = cum A x := by
    have hmass : cum A (v + a) - cum A x = (volume (A ∩ Icc x (v + a))).toReal :=
      cum_sub_cum_eq_mass_Icc (by linarith) (le_of_lt hvax)
    have hz : A ∩ Icc x (v + a) ⊆ {x} := by
      rintro z ⟨hzA, hz1, hz2⟩
      rcases eq_or_lt_of_le hz1 with h | h
      · exact Set.mem_singleton_iff.mpr h.symm
      · exact absurd (hv'min z hzA (le_of_lt h)) (by linarith [hv'gt])
    have : volume (A ∩ Icc x (v + a)) = 0 := measure_mono_null hz (measure_singleton x)
    rw [this] at hmass; simp at hmass; linarith
  -- Translate packing on `[a, a+d]` by `v`.
  have htp := translate_pair_mass_le hIU.isClosed.measurableSet hsf hvA (l := a) (r := a + d)
    (by linarith)
  have he : v + (a + d) = x + 1 := by rw [hd]; ring
  rw [he] at htp
  have hm1 : (volume (A ∩ Icc a (a + d))).toReal = cum A (a + d) - cum A a :=
    (cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)).symm
  have hm2 : (volume (A ∩ Icc (v + a) (x + 1))).toReal = cum A (x + 1) - cum A (v + a) :=
    (cum_sub_cum_eq_mass_Icc (by linarith [hva_eq]) (by linarith [hva_eq])).symm
  rw [hm1, hm2, hFva] at htp
  have hsurp := section4_first_mass_surplus hIU hsf hmin hx hmax hfail
  have hmassab : cum A b - cum A a = (b - a + discOn A a b) / 2 := by
    rw [cum_sub_cum_eq_mass_Icc (by linarith) hab.le]; unfold discOn; ring
  have hmassad : cum A b - cum A (a + d) = (volume (A ∩ Icc (a + d) b)).toReal :=
    cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)
  have hlen2 : (volume (A ∩ Icc (a + d) b)).toReal ≤ (b - a) - d := by
    refine le_trans (ENNReal.toReal_mono (ne_of_lt isCompact_Icc.measure_lt_top)
      (measure_mono Set.inter_subset_right)) ?_
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; linarith
  have ht_le : discOn A a b ≤ b - a := discOn_le_sub A hab.le
  nlinarith [htp, hsurp, hmassab, hmassad, hlen2, ht_le, hs1, hd0]

end ProductFree
