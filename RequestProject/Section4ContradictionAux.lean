import RequestProject.Analytic
import RequestProject.Section4PushLeftFurther
import RequestProject.Section4YThreeDifference
import RequestProject.Section4W

/-!
# Section 4: auxiliary estimates for the final contradiction

This file collects a few reusable geometric estimates used in the assembly of the final
contradiction (`Section4FinalAssembly`).  They isolate short, self-contained packing
arguments from the larger case analysis.
-/

open MeasureTheory Set

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-- Finiteness of the truncated mass, used repeatedly below. -/
lemma volume_inter_Icc_ne_top (A : Set ℝ) (p q : ℝ) :
    volume (A ∩ Icc p q) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (Set.inter_subset_right)) ?_)
  rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top

/-- **Equation `diff eq`.**  Applying Theorem `offdiagonal_main2` (finite-union form) to
`A ∩ [y, x-1]` (where `y = x+1-a`) and packing the nonnegative half of its difference set
with `A ∩ [0, a-2]` gives `2 F(x-1) + F(a-2) ≤ a-2 + t + 2 F(y)`. -/
lemma diff_eq_bound (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {x a b : ℝ} (ha2 : 2 ≤ a) (hax1 : a ≤ x + 1)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    2 * cum A (x - 1) + cum A (a - 2) ≤ (a - 2) + discOn A a b + 2 * cum A (x + 1 - a) := by
  have hdisc : disc (A ∩ Icc (x + 1 - a) (x - 1)) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by linarith) (by linarith) hmax
  have := restricted_difference_packing hIU hsf (p := x + 1 - a) (q := x - 1) (r := a - 2)
    (by linarith) (by linarith) (by linarith) (by linarith) hdisc
  linarith

/-- **Equation `alt diff eq`.**  Applying the same argument to `A ∩ [y, x+1]` gives
`2 F(x+1) + F(a) ≤ a + t + 2 F(y)`. -/
lemma alt_diff_eq_bound (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {x a b : ℝ} (ha0 : 0 ≤ a) (hax1 : a ≤ x + 1)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b) :
    2 * cum A (x + 1) + cum A a ≤ a + discOn A a b + 2 * cum A (x + 1 - a) := by
  have hdisc : disc (A ∩ Icc (x + 1 - a) (x + 1)) ≤ discOn A a b :=
    disc_restriction_le_maximizer (volume_inter_Icc_ne_top A 0 (x + 1))
      (by linarith) (by linarith) hmax
  have := restricted_difference_packing hIU hsf (p := x + 1 - a) (q := x + 1) (r := a)
    (by linarith) (by linarith) (by linarith) (by linarith) hdisc
  linarith

/-- **The `three Fxminus estimate`.**  Purely algebraic combination of `diff eq`
(`diff_eq_bound`), the direct-discrepancy equation `hgId`
(`2 F(y-2) + (F(x-1) - F(a+1)) = y-3-g`), and the reflection bound `hreflect`
(`F(y) - F(y-1) ≤ (s-t)/2`), using `a + y = x + 1`. -/
lemma three_Fxminus_estimate (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {x a b g : ℝ} (ha2 : 2 ≤ a) (hax1 : a ≤ x + 1)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hgId : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = (x + 1 - a) - 3 - g)
    (hreflect : cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2) :
    3 * cum A (x - 1) ≤ x - 4 + (b - a) +
      2 * (cum A (x + 1 - a - 1) - cum A (x + 1 - a - 2)) + cum A (a + 1) - cum A (a - 2) - g := by
  have hdiff := diff_eq_bound hIU hsf ha2 hax1 hmax
  linarith

/-- **The boost equation `boost and interval around a`.**  Packages the algebraic part of
the paper's derivation: given the geometric `x interval mass estimate` `hxint`
(`F(x+1) - F(x-1) ≤ 2 - s - (F(y)-F(y-2)) - (F(a+1)-F(b))`), together with `diff eq`,
the direct-discrepancy equation `hgId`, the reflection bound `hreflect`, the mass identity
`hmassI` and the surplus `hsurplus`, we obtain
`1 - t + g + (s-t)/2 < F(a) - F(a-2)`. -/
lemma boost_eq_of_x_interval_mass (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {x a b g : ℝ} (ha2 : 2 ≤ a) (hax1 : a ≤ x + 1) (hba : b ≤ a + 1)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hgId : 2 * cum A (x + 1 - a - 2) + (cum A (x - 1) - cum A (a + 1)) = (x + 1 - a) - 3 - g)
    (hreflect : cum A (x + 1 - a) - cum A (x + 1 - a - 1) ≤ (b - a - discOn A a b) / 2)
    (hmassI : cum A b - cum A a = (b - a + discOn A a b) / 2)
    (hsurplus : 1 - discOn A a b < cum A (x + 1) - cum A x)
    (hxint : cum A (x + 1) - cum A (x - 1) ≤
      2 - (b - a) - (cum A (x + 1 - a) - cum A (x + 1 - a - 2)) - (cum A (a + 1) - cum A b)) :
    1 - discOn A a b + g + (b - a - discOn A a b) / 2 < cum A a - cum A (a - 2) := by
  have h3 := three_Fxminus_estimate hIU hsf ha2 hax1 hmax hgId hreflect
  have hymono : cum A (x + 1 - a - 1) ≤ cum A (x + 1 - a) := cum_mono A (by linarith)
  have hbmono : cum A b ≤ cum A (a + 1) := cum_mono A (by linarith)
  have hupper : 2 * cum A (x + 1) + cum A (x - 1) ≤
      x - (b - a) + cum A b - cum A (a - 2) - g := by linarith
  exact boost_and_interval_around_a hmassI hupper hfail hsurplus

/-- **The interval around `a`.**  Combining two unit translates by `1 ∈ A`, the mass of `A`
between `b-2` and `a` is bounded by `1 - s + (s-t)/2`, where `s = b - a` and `F(b)-F(a) =
(s+t)/2`.  This is the estimate `F(a) - F(b-2) ≤ 1 - s + (s-t)/2` from the paper's subsection
"The gap around 2". -/
lemma interval_around_a
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    {a b s t : ℝ} (ha1 : 1 ≤ a) (hab : a ≤ b) (hs : s = b - a) (hb2 : 0 ≤ b - 2)
    (hs1 : s < 1) (hmass : cum A b - cum A a = (s + t) / 2) :
    cum A a - cum A (b - 2) ≤ 1 - s + (s - t) / 2 := by
  have h1 : cum A (b - 1) - cum A (a - 1) ≤ (s - t) / 2 := by
    have := unit_translate_pair_mass_le hA hsf hone (a := a - 1) (b := b - 1) (by linarith)
    rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith),
        ← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)] at this
    have e1 : a - 1 + 1 = a := by ring
    have e2 : b - 1 + 1 = b := by ring
    rw [e1, e2] at this
    linarith
  have h2 : (cum A (a - 1) - cum A (b - 2)) + (cum A a - cum A (b - 1)) ≤ 1 - s := by
    have := unit_translate_pair_mass_le hA hsf hone (a := b - 2) (b := a - 1) (by linarith)
    rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith),
        ← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)] at this
    have e1 : b - 2 + 1 = b - 1 := by ring
    have e2 : a - 1 + 1 = a := by ring
    rw [e1, e2] at this
    linarith
  linarith

/-- **Boost transfer to the region around `2`.**  Combining the boost equation `hboost`
with `interval_around_a`, the mass of `A` in `[a-2,b-2]` exceeds `s - t + g`.  This is the
hypothesis `hboost` required by `gap_around_two`. -/
lemma boost_transfer_bound
    (hA : MeasurableSet A) (hsf : IsSumFree A) (hone : 1 ∈ A)
    {a b s t g : ℝ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hs : s = b - a) (hb2 : 0 ≤ b - 2)
    (hs1 : s < 1) (hmass : cum A b - cum A a = (s + t) / 2)
    (hboost : 1 - t + g + (s - t) / 2 < cum A a - cum A (a - 2)) :
    s - t + g < (volume (A ∩ Icc (a - 2) (b - 2))).toReal := by
  have hint := interval_around_a hA hsf hone (by linarith) hab hs hb2 hs1 hmass
  have hmassbd : (volume (A ∩ Icc (a - 2) (b - 2))).toReal = cum A (b - 2) - cum A (a - 2) := by
    rw [← cum_sub_cum_eq_mass_Icc (by linarith) (by linarith)]
  rw [hmassbd]; linarith

end ProductFree
