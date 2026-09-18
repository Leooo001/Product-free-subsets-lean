import RequestProject.Balanced

/-!
# Balanced intervals, continued: subinterval bounds, endpoints, and maximality

This file continues the balanced-interval toolbox of `Balanced.lean` with the results needed
for the proof of `offdiagonal_main2` (Section 3 of the paper):

* subinterval discrepancy bounds for balanced intervals (`discOn_le_of_balanced`,
  `neg_discOn_le_of_balanced`);
* endpoint membership of balanced intervals of positive length
  (`left_balanced_left_mem`, `right_balanced_right_mem`);
* the notion of a *maximal* left-balanced / balanced interval, and the fact that distinct
  maximal such intervals are disjoint (`maximal_left_balanced_disjoint`,
  `maximal_balanced_disjoint`).
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A B : Set ℝ}

/-
If `[a,b]` is balanced and `[p,q] ⊆ [a,b]`, then `d_A([p,q]) ≤ d_A([a,b])`.
(The discrepancy of any subinterval of a balanced interval is at most that of the whole.)
-/
lemma discOn_le_of_balanced (hA : MeasurableSet A) {a b p q : ℝ}
    (hbal : IsBalanced A a b) (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    discOn A p q ≤ discOn A a b := by
  obtain ⟨h_left, h_right⟩ := hbal;
  have h_add : discOn A a b = discOn A a p + discOn A p q + discOn A q b := by
    grind +suggestions;
  linarith [ h_left.2 p hap ( by linarith ), h_right.2 q ( by linarith ) ( by linarith ) ]

/-
If `[a,b]` is balanced and `[p,q] ⊆ [a,b]`, then `-d_A([a,b]) ≤ d_A([p,q])`.
-/
lemma neg_discOn_le_of_balanced (hA : MeasurableSet A) {a b p q : ℝ}
    (hbal : IsBalanced A a b) (hap : a ≤ p) (hpq : p ≤ q) (hqb : q ≤ b) :
    -(discOn A a b) ≤ discOn A p q := by
  obtain ⟨h_left, h_right⟩ := hbal;
  obtain ⟨h_left, h_right⟩ := h_left;
  obtain ⟨h_left, h_right⟩ := ‹IsRightBalanced A a b›;
  grind +suggestions

/-
If `[a,b]` is left balanced w.r.t. a closed set `A` and `a < b`, then `a ∈ A`.
-/
lemma left_balanced_left_mem (hA : IsClosed A) {a b : ℝ}
    (hbal : IsLeftBalanced A a b) (hab : a < b) : a ∈ A := by
  by_contra h;
  -- Since $a \notin A$ and $A$ is closed, there exists $\delta > 0$ such that $(a - \delta, a + \delta) \cap A = \emptyset$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, Metric.ball a δ ∩ A = ∅ := by
    exact Metric.mem_nhds_iff.mp ( hA.isOpen_compl.mem_nhds h ) |> fun ⟨ δ, δ_pos, hδ ⟩ => ⟨ δ, δ_pos, Set.eq_empty_iff_forall_notMem.mpr fun x hx => hδ hx.1 hx.2 ⟩;
  -- Choose $\epsilon = \min(\delta/2, (b-a)/2) > 0$ so that $a + \epsilon \leq b$.
  obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, ε ≤ δ / 2 ∧ ε ≤ (b - a) / 2 := by
    exact ⟨ Min.min ( δ / 2 ) ( ( b - a ) / 2 ), lt_min ( half_pos hδ_pos ) ( half_pos ( sub_pos.mpr hab ) ), min_le_left _ _, min_le_right _ _ ⟩;
  -- Since $A \cap [a, a+\epsilon] = \emptyset$, we have $discOn A a (a+\epsilon) = 2*0 - \epsilon = -\epsilon < 0$.
  have h_disc_neg : discOn A a (a + ε) < 0 := by
    have h_empty : A ∩ Icc a (a + ε) = ∅ := by
      simp_all +decide [ Set.ext_iff ];
      exact fun x hx hx' => not_le.1 fun hx'' => hδ x ( abs_lt.2 ⟨ by linarith, by linarith ⟩ ) hx;
    unfold discOn; aesop;
  exact h_disc_neg.not_ge ( hbal.2 _ ( by linarith ) ( by linarith ) )

/-
If `[a,b]` is right balanced w.r.t. a closed set `A` and `a < b`, then `b ∈ A`.
-/
lemma right_balanced_right_mem (hA : IsClosed A) {a b : ℝ}
    (hbal : IsRightBalanced A a b) (hab : a < b) : b ∈ A := by
  have h_left_balanced_neg : IsLeftBalanced (-A) (-b) (-a) := by
    refine' ⟨ by linarith, fun c hc₁ hc₂ => _ ⟩;
    convert hbal.2 ( -c ) ( by linarith ) ( by linarith ) using 1;
    convert discOn_neg A ( -c ) b using 1 ; ring;
  have := left_balanced_left_mem ( show IsClosed ( -A ) from hA.neg ) h_left_balanced_neg ( by linarith ) ; aesop;

/-
Right-balanced analogue of `union_left_balanced`: two overlapping right-balanced intervals
unite to a right-balanced interval.
-/
lemma union_right_balanced (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsRightBalanced A a b) (hJ : IsRightBalanced A c d) (hcb : c ≤ b) :
    IsRightBalanced A a (max b d) := by
  cases max_cases b d <;> simp_all +decide [ IsRightBalanced ];
  grind +suggestions

/-
If `[a,b]` and `[c,d]` are both balanced w.r.t. `A` and they overlap (`a ≤ c ≤ b ≤ d`), then
their union `[a,d]` is balanced.
-/
lemma union_balanced (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsBalanced A a b) (hJ : IsBalanced A c d) (hac : a ≤ c) (hcb : c ≤ b) (hbd : b ≤ d) :
    IsBalanced A a d := by
  constructor;
  · simpa [ hbd ] using union_left_balanced hA hI.1 hJ.1 hac hcb;
  · convert union_right_balanced hA hI.2 hJ.2 hcb using 1 ; aesop

/-- `[a,b]` is a *maximal left-balanced* interval w.r.t. `A`: it is left balanced, and no strictly
larger interval containing it is left balanced. -/
def IsMaximalLeftBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  IsLeftBalanced A a b ∧ ∀ a' b', a' ≤ a → b ≤ b' → IsLeftBalanced A a' b' → a' = a ∧ b' = b

/-- `[a,b]` is a *maximal balanced* interval w.r.t. `A`. -/
def IsMaximalBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  IsBalanced A a b ∧ ∀ a' b', a' ≤ a → b ≤ b' → IsBalanced A a' b' → a' = a ∧ b' = b

/-
**Corollary "balanced intervals" (left version).** Two distinct maximal left-balanced
intervals are disjoint.
-/
lemma maximal_left_balanced_disjoint (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsMaximalLeftBalanced A a b) (hJ : IsMaximalLeftBalanced A c d)
    (hne : (a, b) ≠ (c, d)) : Disjoint (Icc a b) (Icc c d) := by
  by_contra h_not_disjoint;
  -- Without loss of generality, assume $a \leq c$.
  wlog hac : a ≤ c generalizing a b c d;
  · exact this hJ hI ( Ne.symm hne ) ( Set.not_disjoint_iff.mpr <| by obtain ⟨ x, hx₁, hx₂ ⟩ := Set.not_disjoint_iff.mp h_not_disjoint; exact ⟨ x, hx₂, hx₁ ⟩ ) ( le_of_not_ge hac );
  · obtain ⟨x, hx⟩ : ∃ x, x ∈ Set.Icc a b ∧ x ∈ Set.Icc c d := by
      exact Set.not_disjoint_iff.mp h_not_disjoint;
    obtain ⟨hI_balanced, hI_max⟩ := hI
    obtain ⟨hJ_balanced, hJ_max⟩ := hJ
    have h_union_balanced : IsLeftBalanced A a (max b d) := by
      apply union_left_balanced hA hI_balanced hJ_balanced hac (by
      linarith [ hx.1.2, hx.2.1 ]);
    grind

/-
**Corollary "balanced intervals".** Two distinct maximal balanced intervals are disjoint.
-/
lemma maximal_balanced_disjoint (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsMaximalBalanced A a b) (hJ : IsMaximalBalanced A c d)
    (hne : (a, b) ≠ (c, d)) : Disjoint (Icc a b) (Icc c d) := by
  by_contra hnot;
  -- WLOG `a ≤ c` (symmetric otherwise, swapping the two intervals).
  wlog hac : a ≤ c generalizing a b c d;
  · grind;
  · rw [ Set.not_disjoint_iff ] at hnot;
    -- Then `c ≤ b` (from the common point).
    have hcb : c ≤ b := by
      linarith [ hnot.choose_spec.1.1, hnot.choose_spec.1.2, hnot.choose_spec.2.1, hnot.choose_spec.2.2 ];
    -- Split on whether `b ≤ d` or `d ≤ b`.
    by_cases hbd : b ≤ d;
    · -- Apply `union_balanced hA hI.1 hJ.1 hac hcb hbd : IsBalanced A a d`.
      have h_union : IsBalanced A a d := by
        exact union_balanced hA hI.1 hJ.1 hac hcb hbd;
      have := hI.2 a d ( by linarith ) ( by linarith ) h_union; simp_all +decide ;
      have := hJ.2 a b ( by linarith ) ( by linarith ) h_union; simp_all +decide ;
    · have := hJ.2 a b hac ( by linarith ) hI.1; aesop;

end ProductFree