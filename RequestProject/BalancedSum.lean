import RequestProject.BalancedMore

/-!
# Intersecting balanced intervals (Lemma "intersect balanced" and Corollary "add balanced")

This file continues the Section 3 toolbox with the intersection results:

* `ProductFree.inter_Icc_nonempty_of_balanced`: if `[a,b]` is balanced w.r.t. a closed `A`,
  `[c,d] ⊆ [a,b]` has positive length, and `d_A([a,b]) ≤ d - c`, then `A ∩ [c,d] ≠ ∅`.
* `ProductFree.intersect_balanced` (Lemma "intersect balanced"): if `[a,b]` is balanced w.r.t. `A`,
  `[c,d]` is balanced w.r.t. `B`, both of positive length, they intersect, and
  `d_A([a,b]) = d_B([c,d])`, then `(A ∩ [a,b]) ∩ (B ∩ [c,d]) ≠ ∅`.
* `ProductFree.add_balanced` (Corollary "add balanced"): under the same balance/discrepancy
  hypotheses, `(A ∩ [a,b]) + (B ∩ [c,d]) = [a,b] + [c,d]`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A B : Set ℝ}

/-
If a closed set `A` meets every interval `[d, d+ε]` (`ε > 0`), then `d ∈ A`
(`d` is a right limit point of `A`, and `A` is closed).
-/
lemma mem_of_forall_Icc_right (hA : IsClosed A) {d : ℝ}
    (h : ∀ ε > 0, (A ∩ Icc d (d + ε)).Nonempty) : d ∈ A := by
  have h_seq : ∀ n : ℕ, ∃ x_n ∈ A, d ≤ x_n ∧ x_n ≤ d + 1 / (n + 1) := by
    exact fun n => by obtain ⟨ x, hx₁, hx₂ ⟩ := h ( 1 / ( n + 1 ) ) ( by positivity ) ; exact ⟨ x, hx₁, hx₂.1, hx₂.2 ⟩ ;
  choose f hf using h_seq;
  exact hA.mem_of_tendsto ( tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ hf n ], by linarith [ hf n ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ) ( Filter.Eventually.of_forall fun n => hf n |>.1 )

/-
**Key nonemptiness lemma.** If `[a,b]` is balanced w.r.t. a closed set `A`, the subinterval
`[c,d] ⊆ [a,b]` has positive length, and `d_A([a,b]) ≤ d - c`, then `A ∩ [c,d]` is nonempty.

(The hypothesis `d_A([a,b]) ≤ d - c` is essential: a wide balanced interval can have a subinterval
disjoint from `A`, but then its discrepancy exceeds `d - c`.)
-/
lemma inter_Icc_nonempty_of_balanced (hA : IsClosed A) {a b c d : ℝ}
    (hbal : IsBalanced A a b) (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hsmall : discOn A a b ≤ d - c) :
    (A ∩ Icc c d).Nonempty := by
  by_contra h_empty_inter; have h_measurable : MeasurableSet A := hA.measurableSet; simp_all +decide [ IsBalanced ] ; (
  have h_discOn_cd : discOn A c d = -(d - c) := by
    unfold discOn; simp_all +decide [ Set.not_nonempty_iff_eq_empty ] ;
  have h_discOn_ad : discOn A a d = 0 := by
    have h_discOn_ad : discOn A a d ≥ 0 := by
      exact hbal.1.2 d ( by linarith ) ( by linarith )
    have h_discOn_ab : discOn A a b = discOn A a d + discOn A d b := by
      exact discOn_add h_measurable ( by linarith ) ( by linarith )
    have h_discOn_db : discOn A d b ≥ d - c := by
      have h_discOn_db : discOn A c b ≥ 0 := by
        exact hbal.2.2 c hac ( by linarith ) |> fun h => by linarith;
      have h_discOn_cb : discOn A c b = discOn A c d + discOn A d b := by
        exact discOn_add h_measurable ( by linarith ) ( by linarith )
      linarith [h_discOn_cb, h_discOn_db]
    linarith [h_discOn_ab, h_discOn_db]
  have h_discOn_db : discOn A d b = d - c := by
    have h_discOn_ab : discOn A a b = discOn A a d + discOn A d b := by
      exact discOn_add h_measurable ( by linarith ) ( by linarith )
    have h_discOn_ab_le : discOn A a b ≤ d - c := by
      linarith [hsmall]
    have h_discOn_ab_ge : discOn A a b ≥ d - c := by
      have h_discOn_ac : discOn A a c ≥ d - c := by
        grind +suggestions
      have h_discOn_ab_ge : discOn A a b ≥ d - c := by
        have h_discOn_ab_ge : discOn A a b = discOn A a c + discOn A c b := by
          exact discOn_add h_measurable hac ( by linarith )
        linarith [hbal.2.2 c (by linarith) (by linarith)]
      linarith [h_discOn_ab_ge]
    linarith [h_discOn_ab, h_discOn_ab_le, h_discOn_ab_ge]
  have h_discOn_ab : discOn A a b = d - c := by
    linarith [ discOn_add h_measurable ( by linarith : a ≤ d ) ( by linarith : d ≤ b ) ]
  have h_discOn_ac : discOn A a c = d - c := by
    linarith [ discOn_add h_measurable hac ( by linarith : c ≤ d ), discOn_add h_measurable ( by linarith : a ≤ d ) ( by linarith : d ≤ b ) ];
  -- For every `ε > 0`, show `(A ∩ Icc d (d+ε)).Nonempty`. Let `x = min (d+ε) b` (so `d ≤ x ≤ b`, and `x > d` since `d < b` because `c < d ≤ b`).
  have h_forall_ε : ∀ ε > 0, (A ∩ Icc d (min (d + ε) b)).Nonempty := by
    intros ε hε_pos
    set x := min (d + ε) b with hx_def
    have hx_bounds : d ≤ x ∧ x ≤ b := by
      exact ⟨ le_min ( by linarith ) ( by linarith ), min_le_right _ _ ⟩
    have hx_gt_d : d < x := by
      cases min_cases ( d + ε ) b <;> linarith [ show d < b from lt_of_le_of_ne hdb ( by rintro rfl; exact h_empty_inter <| by have := right_balanced_right_mem hA hbal.2 ( by linarith ) ; exact ⟨ _, this, by constructor <;> linarith ⟩ ) ] ;
    have h_discOn_dx : discOn A d x ≥ 0 := by
      have h_discOn_dx : discOn A a x ≥ 0 := by
        exact hbal.1.2 x ( by linarith ) ( by linarith ) |> fun h => by linarith;
      generalize_proofs at *; (
      linarith [ discOn_add h_measurable ( show a ≤ d by linarith ) ( show d ≤ x by linarith ) ])
    have h_discOn_dx_pos : (volume (A ∩ Icc d x)).toReal ≥ (x - d) / 2 := by
      unfold discOn at h_discOn_dx; linarith;
    have h_nonempty : (A ∩ Icc d x).Nonempty := by
      exact Set.nonempty_iff_ne_empty.mpr ( by rintro h; norm_num [ h ] at h_discOn_dx_pos; linarith ) ;
    exact h_nonempty.mono (by
    exact Set.Subset.rfl)
  generalize_proofs at *; (
  -- Therefore `d ∈ A` by `mem_of_forall_Icc_right`, contradiction.
  have h_d_in_A : d ∈ A := by
    apply mem_of_forall_Icc_right hA; intro ε hε; exact (by
    exact Exists.elim ( h_forall_ε ε hε ) fun x hx => ⟨ x, hx.1, hx.2.1, hx.2.2.trans ( min_le_left _ _ ) ⟩);
  generalize_proofs at *; (
  exact h_empty_inter ⟨ d, h_d_in_A, ⟨ by linarith, by linarith ⟩ ⟩)));

/-
Version of Lemma "intersect balanced" with the ordering hypothesis `a ≤ c` (and `c ≤ b`,
which follows from the intervals intersecting).
-/
lemma intersect_balanced_of_le (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hI : IsBalanced A a b) (hJ : IsBalanced B c d)
    (hac : a ≤ c) (hcb : c ≤ b) (hdisc : discOn A a b = discOn B c d) :
    (A ∩ Icc a b ∩ (B ∩ Icc c d)).Nonempty := by
  by_cases hbd : b ≤ d <;> simp_all +decide [ IsBalanced ];
  · by_cases hcb' : c < b;
    · obtain ⟨x, hx⟩ : (A ∩ B ∩ Icc c b).Nonempty := by
        apply inter_nonempty_of_measure hA hB hcb';
        · have := hI.2.2 c hac hcb; unfold discOn at this; linarith;
        · have := hJ.1.2 b ( by linarith ) ( by linarith ) ; unfold discOn at this; linarith;
      exact ⟨ x, ⟨ ⟨ hx.1.1, by constructor <;> linarith [ hx.2.1, hx.2.2 ] ⟩, ⟨ hx.1.2, by constructor <;> linarith [ hx.2.1, hx.2.2 ] ⟩ ⟩ ⟩;
    · -- Since $c = b$, we have $b \in A$ and $c \in B$.
      have hbA : b ∈ A := by
        exact right_balanced_right_mem hA hI.2 hab
      have hcB : c ∈ B := by
        exact left_balanced_left_mem hB hJ.1 ( by linarith )
      use b
      simp [hbA];
      exact ⟨ by linarith, by convert hcB using 1; linarith, by linarith, by linarith ⟩;
  · obtain ⟨x, hx⟩ : (A ∩ Icc c d).Nonempty ∧ (B ∩ Icc c d).Nonempty ∧ 0 ≤ discOn A c d + discOn B c d := by
      refine' ⟨ _, _, _ ⟩;
      · apply inter_Icc_nonempty_of_balanced hA hI;
        · linarith;
        · linarith;
        · linarith;
        · rw [ hdisc ];
          exact discOn_le_sub B hcd.le;
      · exact ⟨ c, left_balanced_left_mem hB hJ.1 hcd, ⟨ by linarith, by linarith ⟩ ⟩;
      · have h_subinterval : discOn A a d ≥ 0 ∧ discOn A c b ≥ 0 := by
          exact ⟨ hI.1.2 d ( by linarith ) ( by linarith ), hI.2.2 c ( by linarith ) ( by linarith ) ⟩;
        have h_subinterval : discOn A a b = discOn A a d + discOn A d b ∧ discOn A c b = discOn A c d + discOn A d b := by
          exact ⟨ discOn_add ( hA.measurableSet ) ( by linarith ) ( by linarith ), discOn_add ( hA.measurableSet ) ( by linarith ) ( by linarith ) ⟩;
        linarith;
    have := inter_nonempty_of_discOn hA hB hcd x hx.1 hx.2;
    exact this.imp fun x hx => ⟨ ⟨ hx.1.1, ⟨ by linarith [ hx.2.1 ], by linarith [ hx.2.2 ] ⟩ ⟩, ⟨ hx.1.2, hx.2 ⟩ ⟩

/-
**Lemma "intersect balanced".** If `[a,b]` is balanced w.r.t. `A`, `[c,d]` is balanced w.r.t.
`B`, both of positive length, `[a,b] ∩ [c,d] ≠ ∅`, and `d_A([a,b]) = d_B([c,d])`, then
`(A ∩ [a,b]) ∩ (B ∩ [c,d]) ≠ ∅`.
-/
lemma intersect_balanced (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hI : IsBalanced A a b) (hJ : IsBalanced B c d)
    (hinter : (Icc a b ∩ Icc c d).Nonempty) (hdisc : discOn A a b = discOn B c d) :
    (A ∩ Icc a b ∩ (B ∩ Icc c d)).Nonempty := by
  by_cases hac : a ≤ c;
  · obtain ⟨ x, hx ⟩ := hinter;
    apply intersect_balanced_of_le hA hB hab hcd hI hJ hac (by linarith [hx.1.2, hx.2.1]) hdisc;
  · have := intersect_balanced_of_le hB hA hcd hab hJ hI ( by linarith ) ( by linarith [ Set.mem_Icc.mp ( hinter.choose_spec.1 ), Set.mem_Icc.mp ( hinter.choose_spec.2 ) ] ) hdisc.symm; simp_all +decide [ Set.inter_comm ];

/-
Reflection `y ↦ x - y` of a closed set is closed.
-/
lemma isClosed_reflect_sub {B : Set ℝ} (x : ℝ) (h : IsClosed B) :
    IsClosed ((fun y => x - y) '' B) := by
  convert h.preimage ( show Continuous fun y => x - y from continuous_const.sub continuous_id' ) using 1;
  ext y; aesop

/-
Reflection `y ↦ x - y` preserves the interval discrepancy:
`d_{x-B}([x-d, x-c]) = d_B([c,d])`.
-/
lemma discOn_reflect_sub (B : Set ℝ) (x c d : ℝ) :
    discOn ((fun y => x - y) '' B) (x - d) (x - c) = discOn B c d := by
  by_contra h_contra;
  -- Let's simplify the expression using the fact that multiplication by a constant $k$ and addition are compatible with the volume measure.
  have h_volume : volume ((fun y => x - y) '' B ∩ Icc (x - d) (x - c)) = volume (B ∩ Icc c d) := by
    rw [ show ( fun y => x - y ) '' B ∩ Icc ( x - d ) ( x - c ) = ( fun y => x - y ) '' ( B ∩ Icc c d ) from ?_ ];
    · have h_volume : ∀ (S : Set ℝ), volume ((fun y => x - y) '' S) = volume S := by
        intro S;
        rw [ show ( fun y => x - y ) '' S = ( fun y => -y ) '' S + { x } by ext; simp +decide [ sub_eq_add_neg, add_comm ] ; aesop ];
        simp +decide [ Set.image_neg, Set.add_singleton ];
      exact h_volume _;
    · ext; simp [Set.mem_image, Set.mem_inter_iff];
      grind +splitIndPred;
  exact h_contra ( by unfold discOn; aesop )

/-
Reflection `y ↦ x - y` preserves balancedness.
-/
lemma isBalanced_reflect_sub {B : Set ℝ} {c d : ℝ} (x : ℝ) (h : IsBalanced B c d) :
    IsBalanced ((fun y => x - y) '' B) (x - d) (x - c) := by
  constructor;
  · constructor;
    · linarith [ h.1.1 ];
    · intro e he₁ he₂;
      have := discOn_reflect_sub B x ( x - e ) d; simp_all +decide [ IsBalanced ] ;
      exact h.2.2 _ ( by linarith ) ( by linarith );
  · constructor;
    · linarith [ h.1.1 ];
    · intro y hy₁ hy₂; have := h.1.2 ( x - y ) ?_ ?_ <;> simp_all +decide ;
      · convert this using 1;
        convert discOn_reflect_sub B x c ( x - y ) using 1 ; ring;
      · linarith;
      · linarith

/-
**Corollary "add balanced".** If `[a,b]` is balanced w.r.t. `A`, `[c,d]` is balanced w.r.t.
`B`, both of positive length, and `d_A([a,b]) = d_B([c,d])`, then
`(A ∩ [a,b]) + (B ∩ [c,d]) = [a,b] + [c,d]`.
-/
lemma add_balanced (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hI : IsBalanced A a b) (hJ : IsBalanced B c d)
    (hdisc : discOn A a b = discOn B c d) :
    (A ∩ Icc a b) + (B ∩ Icc c d) = Icc a b + Icc c d := by
  ext z;
  constructor <;> intro hz;
  · exact Set.add_subset_add ( Set.inter_subset_right ) ( Set.inter_subset_right ) hz;
  · -- Set `B' := (fun y => z - y) '' B` and consider the interval `[z-d, z-c]`.
    set B' := (fun y => z - y) '' B
    set p := max a (z - d)
    set q := min b (z - c);
    -- By `intersect_balanced`, there exists `p ∈ A ∩ Icc a b ∩ (B' ∩ Icc (z-d) (z-c))`.
    obtain ⟨p, hp⟩ : ∃ p, p ∈ A ∩ Icc a b ∩ (B' ∩ Icc (z - d) (z - c)) := by
      apply intersect_balanced hA (isClosed_reflect_sub z hB) hab (by
      linarith) hI (by
      exact isBalanced_reflect_sub z hJ) (by
      exact ⟨ hz.choose, hz.choose_spec.1, ⟨ by linarith [ hz.choose_spec.2.choose_spec.1.1, hz.choose_spec.2.choose_spec.1.2, hz.choose_spec.2.choose_spec.2 ], by linarith [ hz.choose_spec.2.choose_spec.1.1, hz.choose_spec.2.choose_spec.1.2, hz.choose_spec.2.choose_spec.2 ] ⟩ ⟩) (by
      rw [ hdisc, discOn_reflect_sub ]);
    simp +zetaDelta at *;
    exact ⟨ p, ⟨ hp.1.1, hp.1.2.1, hp.1.2.2 ⟩, hp.2.1.choose, ⟨ hp.2.1.choose_spec.1, by linarith [ hp.2.1.choose_spec.2 ], by linarith [ hp.2.1.choose_spec.2 ] ⟩, by linarith [ hp.2.1.choose_spec.2 ] ⟩

end ProductFree