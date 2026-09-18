import RequestProject.Defs

/-!
# Balanced intervals: the toolbox for Theorem `main2`

This file develops the "balanced interval" machinery of Section 3 of the paper, the toolbox used
to prove the sumset inequality `offdiagonal_main2` / `main2`.

For a set `A` and an interval `I = [a,b]`, recall `d_A(I) = 2|A ∩ I| - |I|` (`discOn A a b`).

* An interval `[a,b]` is **left balanced** w.r.t. `A` if `d_A([a,c]) ≥ 0` for every `c ∈ [a,b]`.
* It is **right balanced** if `d_A([c,b]) ≥ 0` for every `c ∈ [a,b]`.
* It is **balanced** if it is both.

The main lemmas proved here (all for closed sets of finite measure) are:

* `discOn_add` — additivity of `d_A` over a split of an interval;
* `discOn_neg` — reflection invariance;
* `inter_nonempty_of_measure` — two closed sets whose masses on `[c,b]` sum to at least `|[c,b]|`
  meet inside `[c,b]`;
* `union_left_balanced` (Lemma "union left balanced");
* `main_step` (Lemma "main step") and `main_step_sums` (Corollary "main step sums").
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A B : Set ℝ}

/-- `[a,b]` is *left balanced* w.r.t. `A`: `d_A([a,c]) ≥ 0` for every `c ∈ [a,b]`. -/
def IsLeftBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → 0 ≤ discOn A a c

/-- `[a,b]` is *right balanced* w.r.t. `A`: `d_A([c,b]) ≥ 0` for every `c ∈ [a,b]`. -/
def IsRightBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∀ c, a ≤ c → c ≤ b → 0 ≤ discOn A c b

/-- `[a,b]` is *balanced* w.r.t. `A` if it is both left and right balanced. -/
def IsBalanced (A : Set ℝ) (a b : ℝ) : Prop :=
  IsLeftBalanced A a b ∧ IsRightBalanced A a b

/-
Additivity of `d_A` over a split: for `a ≤ c ≤ b`, `d_A([a,b]) = d_A([a,c]) + d_A([c,b])`.
-/
lemma discOn_add (hA : MeasurableSet A) {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    discOn A a b = discOn A a c + discOn A c b := by
  have h_volume : (volume (A ∩ Icc a b)).toReal = (volume (A ∩ Icc a c)).toReal + (volume (A ∩ Ioc c b)).toReal := by
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
    · rw [ ← Set.inter_union_distrib_left, Set.Icc_union_Ioc_eq_Icc hac hcb ];
    · grind;
    · exact hA.inter measurableSet_Ioc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hac, hcb ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hac, hcb ] ) );
  unfold discOn; simp_all +decide [ add_sub_add_comm ] ;
  rw [ show ( volume ( A ∩ Ioc c b ) ).toReal = ( volume ( A ∩ Icc c b ) ).toReal from ?_ ] ; ring;
  rw [ show A ∩ Icc c b = ( A ∩ Ioc c b ) ∪ ( A ∩ { c } ) from ?_, MeasureTheory.measure_union ] <;> norm_num [ hA, hac, hcb ];
  · exact Eq.symm ( by rw [ show volume ( A ∩ { c } ) = 0 from by exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( MeasureTheory.measure_singleton c ) ] ; norm_num );
  · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ hx₁.2.1, hx₂.2.symm ] ;
  · grind

/-
The mass `|A ∩ [a,b]|` is monotone in the interval (with `a` fixed on the left).
-/
lemma discOn_le_disc (hfin : volume A ≠ ⊤) {a b : ℝ} (hab : a ≤ b) :
    discOn A a b ≤ disc A := by
  refine' le_csSup _ _;
  · refine' ⟨ 2 * ( volume A |> ENNReal.toReal ), fun r hr => _ ⟩;
    obtain ⟨ a, b, hab, rfl ⟩ := hr;
    exact le_trans ( sub_le_self _ <| sub_nonneg.mpr hab ) ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono ( by aesop ) <| MeasureTheory.measure_mono <| Set.inter_subset_left ) zero_le_two );
  · exact ⟨ a, b, hab, rfl ⟩

/-
Reflection: `d_{-A}([-b,-a]) = d_A([a,b])`.
-/
lemma discOn_neg (A : Set ℝ) (a b : ℝ) : discOn (-A) (-b) (-a) = discOn A a b := by
  unfold discOn; by_cases h : 0 ≤ -a - -b <;> simp_all +decide [ neg_sub, sub_eq_add_neg ] ;
  · erw [ ← MeasureTheory.measure_preimage_add_right ] ; norm_num ; ring;
    rw [ show ( fun h => h + b ) ⁻¹' ( -A ) ∩ Icc ( - ( b * 2 ) ) ( -b - a ) = ( fun h => -h - b ) '' ( A ∩ Icc a b ) from ?_ ];
    · -- The volume of a set is invariant under translation and reflection.
      have h_volume_invariant : ∀ (S : Set ℝ), volume (Set.image (fun h => -h - b) S) = volume S := by
        intro S; rw [ show ( fun h => -h - b ) '' S = ( fun h => -h ) '' S - { b } by ext; simp +decide [ sub_eq_add_neg, Set.mem_add ] ; aesop ] ; simp +decide [ sub_eq_add_neg, Set.image_add_right ] ;
      rw [ h_volume_invariant ];
    · norm_num [ Set.ext_iff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc ];
      exact fun x => ⟨ fun hx => ⟨ -b + -x, ⟨ hx.1, by linarith, by linarith ⟩, by ring ⟩, by rintro ⟨ y, ⟨ hy₁, hy₂, hy₃ ⟩, rfl ⟩ ; exact ⟨ by simpa using hy₁, by linarith, by linarith ⟩ ⟩;
  · ring

/-
`disc` is reflection invariant.
-/
lemma disc_neg (A : Set ℝ) : disc (-A) = disc A := by
  unfold disc;
  congr! 3;
  constructor <;> rintro ⟨ a, b, hab, rfl ⟩ <;> use -b, -a <;> norm_num [ hab ];
  · convert discOn_neg A ( -b ) ( -a ) using 1 ; ring; all_goals unfold discOn; ring;
  · convert discOn_neg A a b |> Eq.symm using 1;
    unfold discOn; ring;

/-
**Intersection lemma.** If `A` and `B` are closed and their masses on `[c,b]` (with `c < b`)
each are at least `|[c,b]|/2`, then `A ∩ B ∩ [c,b]` is nonempty.
-/
lemma inter_nonempty_of_measure (hA : IsClosed A) (hB : IsClosed B) {c b : ℝ} (hcb : c < b)
    (hA' : (b - c) / 2 ≤ (volume (A ∩ Icc c b)).toReal)
    (hB' : (b - c) / 2 ≤ (volume (B ∩ Icc c b)).toReal) :
    (A ∩ B ∩ Icc c b).Nonempty := by
  by_contra h;
  -- Set `A' = A ∩ Icc c b`, `B' = B ∩ Icc c b`. These are closed and disjoint.
  set A' := A ∩ Icc c b
  set B' := B ∩ Icc c b
  have hA' : IsClosed A' := by
    exact hA.inter isClosed_Icc
  have hB' : IsClosed B' := by
    exact hB.inter isClosed_Icc
  have h_disjoint : Disjoint A' B' := by
    exact Set.disjoint_left.mpr fun x hx hx' => h ⟨ x, by aesop ⟩;
  -- Since $A'$ and $B'$ are closed and disjoint, and their union is $Icc c b$, they form a separation of $Icc c b$.
  have h_separation : A' ∪ B' = Icc c b := by
    have h_union : volume (Icc c b \ (A' ∪ B')) = 0 := by
      have h_union : volume (A' ∪ B') = volume A' + volume B' := by
        rw [ MeasureTheory.measure_union ];
        · assumption;
        · exact hB'.measurableSet;
      have h_union : volume (A' ∪ B') ≥ ENNReal.ofReal (b - c) := by
        rw [ h_union, ge_iff_le, ENNReal.ofReal_le_iff_le_toReal ] <;> norm_num;
        · rw [ ENNReal.toReal_add ];
          · linarith;
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
          · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
        · exact ⟨ ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A' ⊆ Set.Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) ), ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B' ⊆ Set.Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) ) ⟩;
      have h_union : volume (Icc c b \ (A' ∪ B')) = volume (Icc c b) - volume (A' ∪ B') := by
        rw [ MeasureTheory.measure_diff ];
        · grind +splitImp;
        · exact MeasurableSet.nullMeasurableSet ( hA'.measurableSet.union hB'.measurableSet );
        · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.union_subset ( Set.inter_subset_right ) ( Set.inter_subset_right ) ) ) ( by simp +decide [ hcb.le ] ) );
      simp_all +decide [ Real.volume_Icc ];
      exact tsub_eq_zero_of_le ‹_›;
    contrapose! h_union;
    -- Since $A'$ and $B'$ are closed and disjoint, and their union is not $Icc c b$, there exists an open interval $(x, y)$ in $Icc c b$ that is disjoint from $A' \cup B'$.
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℝ, c ≤ x ∧ x < y ∧ y ≤ b ∧ ∀ z ∈ Set.Ioo x y, z ∉ A' ∪ B' := by
      obtain ⟨z, hz⟩ : ∃ z ∈ Set.Icc c b, z ∉ A' ∪ B' := by
        exact Set.exists_of_ssubset ( lt_of_le_of_ne ( Set.union_subset ( Set.inter_subset_right ) ( Set.inter_subset_right ) ) h_union );
      obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ w, abs (w - z) < ε → w ∉ A' ∪ B' := by
        exact Metric.mem_nhds_iff.mp ( IsOpen.mem_nhds ( isOpen_compl_iff.mpr ( hA'.union hB' ) ) hz.2 );
      simp +zetaDelta at *;
      exact ⟨ Max.max c ( z - ε / 2 ), by norm_num, Min.min b ( z + ε / 2 ), by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, fun w hw₁ hw₂ => hε.2 w <| abs_lt.2 ⟨ by cases max_cases c ( z - ε / 2 ) <;> linarith, by cases min_cases b ( z + ε / 2 ) <;> linarith ⟩ ⟩;
    exact ne_of_gt ( lt_of_lt_of_le ( by simp [ hxy ] ) ( MeasureTheory.measure_mono ( show Set.Ioo x y ⊆ Icc c b \ ( A' ∪ B' ) from fun z hz => ⟨ ⟨ by linarith [ hz.1 ], by linarith [ hz.2 ] ⟩, hxy.2.2.2 z hz ⟩ ) ) );
  have h_nonempty : A'.Nonempty ∧ B'.Nonempty := by
    constructor <;> contrapose! h <;> simp_all +decide [ Set.not_nonempty_iff_eq_empty ]; all_goals linarith;
  have h_preconnected : IsPreconnected (Icc c b) := by
    exact isPreconnected_Icc;
  specialize h_preconnected ( B'ᶜ ) ( A'ᶜ ) ; simp_all +decide [ Set.subset_def, Set.Nonempty ];
  grind

/-
A convenient reformulation of `inter_nonempty_of_measure` in terms of `discOn`:
if `A`, `B` are closed, `c < b`, both meet `[c,b]`, and `d_A([c,b]) + d_B([c,b]) ≥ 0`, then
`A ∩ B ∩ [c,b] ≠ ∅`. (Both-nonempty is needed: otherwise one set could be all of `[c,b]` and the
other empty.)
-/
lemma inter_nonempty_of_discOn (hA : IsClosed A) (hB : IsClosed B) {c b : ℝ} (hcb : c < b)
    (hAne : (A ∩ Icc c b).Nonempty) (hBne : (B ∩ Icc c b).Nonempty)
    (h : 0 ≤ discOn A c b + discOn B c b) :
    (A ∩ B ∩ Icc c b).Nonempty := by
  contrapose! h;
  -- Since $A$ and $B$ are closed and disjoint, their union $A \cup B$ is also closed.
  have h_union_closed : IsClosed (A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b) := by
    exact IsClosed.union ( hA.inter isClosed_Icc ) ( hB.inter isClosed_Icc );
  -- Since $A \cup B$ is closed and $A \cap B = \emptyset$, it follows that $A \cup B$ is a proper subset of $[c, b]$.
  have h_union_proper : A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b ≠ Set.Icc c b := by
    intro H;
    have h_preconnected : IsPreconnected (Set.Icc c b) := by
      exact isPreconnected_Icc;
    simp_all +decide [ IsPreconnected, Set.ext_iff ];
    specialize h_preconnected ( Set.univ \ B ) ( Set.univ \ A ) ; simp_all +decide [ Set.diff_eq ];
    simp_all +decide [ Set.subset_def, Set.Nonempty ];
    grind;
  -- Since $A \cup B$ is closed and a proper subset of $[c, b]$, there exists an open interval $(x, y) \subset [c, b]$ such that $(x, y) \cap (A \cup B) = \emptyset$.
  obtain ⟨x, y, hx, hy, hxy⟩ : ∃ x y : ℝ, c ≤ x ∧ x < y ∧ y ≤ b ∧ ∀ z ∈ Set.Ioo x y, z ∉ A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b := by
    obtain ⟨z, hz⟩ : ∃ z ∈ Set.Icc c b, z ∉ A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b := by
      exact Set.exists_of_ssubset ( lt_of_le_of_ne ( Set.union_subset ( Set.inter_subset_right ) ( Set.inter_subset_right ) ) h_union_proper );
    obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ w, abs (w - z) < ε → w ∉ A ∩ Set.Icc c b ∪ B ∩ Set.Icc c b := by
      exact Metric.mem_nhds_iff.mp ( h_union_closed.isOpen_compl.mem_nhds hz.2 );
    simp +zetaDelta at *;
    exact ⟨ Max.max c ( z - ε / 2 ), by norm_num, Min.min b ( z + ε / 2 ), by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, by cases max_cases c ( z - ε / 2 ) <;> cases min_cases b ( z + ε / 2 ) <;> linarith, fun w hw₁ hw₂ => hε.2 w <| abs_lt.2 ⟨ by cases max_cases c ( z - ε / 2 ) <;> linarith, by cases min_cases b ( z + ε / 2 ) <;> linarith ⟩ ⟩;
  -- Since $(x, y) \cap (A \cup B) = \emptyset$, we have $|A \cap [c, b]| + |B \cap [c, b]| \leq |[c, b] \setminus (x, y)|$.
  have h_measure : (volume (A ∩ Set.Icc c b)).toReal + (volume (B ∩ Set.Icc c b)).toReal ≤ (volume (Set.Icc c b \ Set.Ioo x y)).toReal := by
    rw [ ← ENNReal.toReal_add ];
    · rw [ ← MeasureTheory.measure_union ];
      · gcongr;
        · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show Icc c b \ Ioo x y ⊆ Icc c b from fun z hz => hz.1 ) ) ( by simp +decide [ hcb.le ] ) );
        · grind;
      · exact Set.disjoint_left.mpr fun z hzA hzB => h.subset ⟨ ⟨ hzA.1, hzB.1 ⟩, hzA.2 ⟩;
      · exact hB.measurableSet.inter measurableSet_Icc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show A ∩ Icc c b ⊆ Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( show B ∩ Icc c b ⊆ Icc c b from fun x hx => hx.2 ) ) ( by simp +decide [ hcb.le ] ) );
  -- Since $|[c, b] \setminus (x, y)| = |[c, b]| - |(x, y)|$, we have $|A \cap [c, b]| + |B \cap [c, b]| \leq |[c, b]| - |(x, y)|$.
  have h_measure_simplified : (volume (A ∩ Set.Icc c b)).toReal + (volume (B ∩ Set.Icc c b)).toReal ≤ (b - c) - (y - x) := by
    convert h_measure using 1;
    rw [ MeasureTheory.measure_diff ] <;> norm_num [ hx, hy.le, hxy.1 ];
    · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num [ hcb.le, hy.le ];
      linarith;
    · exact fun z hz => ⟨ by linarith [ hz.1 ], by linarith [ hz.2 ] ⟩;
  unfold discOn; linarith;

/-
**Strict intersection lemma.** If `A`, `B` are measurable, `c < b`, and
`d_A([c,b]) + d_B([c,b]) > 0`, then `A ∩ B ∩ [c,b]` has positive measure, hence is nonempty.
-/
lemma inter_nonempty_of_discOn_pos (hA : MeasurableSet A) (hB : MeasurableSet B) {c b : ℝ}
    (hcb : c < b) (h : 0 < discOn A c b + discOn B c b) :
    (A ∩ B ∩ Icc c b).Nonempty := by
  contrapose! h;
  -- By inclusion–exclusion, we have `volume ((A ∩ Icc c b) ∪ (B ∩ Icc c b)) + volume ((A ∩ Icc c b) ∩ (B ∩ Icc c b)) = volume (A ∩ Icc c b) + volume (B ∩ Icc c b)`.
  have h_incl_excl : (volume (A ∩ Icc c b)).toReal + (volume (B ∩ Icc c b)).toReal ≤ (volume (Icc c b)).toReal := by
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union_add_inter ];
    · gcongr;
      · norm_num;
      · simp_all +decide [ Set.inter_assoc, Set.inter_comm, Set.inter_left_comm ];
        exact le_trans ( MeasureTheory.measure_mono ( show A ∩ Icc c b ∪ B ∩ Icc c b ⊆ Icc c b from fun x hx => by aesop ) ) ( by simp +decide [ hcb.le ] );
    · exact hB.inter measurableSet_Icc;
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide [ hcb.le ] ) );
  unfold discOn; norm_num [ hcb.le ] at *; linarith;

/-
**Lemma "union left balanced".** If `[a,b]` and `[c,d]` are both left balanced w.r.t. `A` and
they intersect (`c ≤ b`, assuming `a ≤ c`), then their union `[a,d]` is left balanced.
-/
lemma union_left_balanced (hA : MeasurableSet A) {a b c d : ℝ}
    (hI : IsLeftBalanced A a b) (hJ : IsLeftBalanced A c d) (hac : a ≤ c) (hcb : c ≤ b) :
    IsLeftBalanced A a (max b d) := by
  refine' ⟨ by cases max_cases b d <;> linarith, _ ⟩;
  intro x hx₁ hx₂; cases le_total x b <;> cases le_total x d <;> simp_all +decide [ IsLeftBalanced ] ;
  · rw [ show discOn A a x = discOn A a c + discOn A c x from discOn_add hA ( by linarith ) ( by linarith ) ] ; linarith [ hI.2 c ( by linarith ) ( by linarith ), hJ.2 x ( by linarith ) ( by linarith ) ];
  · cases hx₂ <;> simp_all +decide [ le_antisymm ‹_› ‹_› ];
    rw [ show discOn A a d = discOn A a c + discOn A c d by exact discOn_add hA ( by linarith ) ( by linarith ) ] ; linarith [ hI.2 c ( by linarith ) ( by linarith ), hJ.2 d ( by linarith ) ( by linarith ) ]

/-
If `[c,e]` (a left subinterval) attains the discrepancy `disc B` with a strictly positive
value, then its right endpoint `e` belongs to the closed set `B`. (Otherwise a small leftward
shrink would strictly increase the discrepancy, exceeding `disc B`.)
-/
lemma right_endpoint_mem_of_disc (hB : IsClosed B) (hfin : volume B ≠ ⊤) {c e : ℝ}
    (hce : c ≤ e) (hmax : disc B ≤ discOn B c e) (hpos : 0 < discOn B c e) : e ∈ B := by
  contrapose! hmax;
  -- Since $e \notin B$, there exists $\delta > 0$ such that $(e - \delta, e) \cap B = \emptyset$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ y, abs (y - e) < δ → y ∉ B := by
    exact Metric.mem_nhds_iff.mp ( hB.isOpen_compl.mem_nhds hmax );
  -- Choose $\delta'$ such that $0 < \delta' \leq \min(\delta, e - c)$.
  obtain ⟨δ', hδ'_pos, hδ'_le⟩ : ∃ δ' > 0, δ' ≤ min δ (e - c) := by
    exact ⟨ Min.min δ ( e - c ), lt_min hδ_pos ( sub_pos.mpr ( lt_of_le_of_ne hce ( by rintro rfl; exact hpos.ne' ( by unfold discOn; aesop ) ) ) ), le_rfl ⟩;
  -- Then $B \cap [c, e] = B \cap [c, e - \delta']$.
  have h_eq : B ∩ Set.Icc c e = B ∩ Set.Icc c (e - δ') := by
    grind;
  -- Therefore, `discOn B c (e - δ') = discOn B c e + δ'`.
  have h_discOn_eq : discOn B c (e - δ') = discOn B c e + δ' := by
    unfold discOn at *;
    rw [ h_eq ] ; ring;
  linarith [ discOn_le_disc hfin ( show c ≤ e - δ' by linarith [ min_le_right δ ( e - c ) ] ) ]

/-
If `[e,d]` (a right subinterval) attains the discrepancy `disc B` with a strictly positive
value, then its left endpoint `e` belongs to the closed set `B`.
-/
lemma left_endpoint_mem_of_disc (hB : IsClosed B) (hfin : volume B ≠ ⊤) {e d : ℝ}
    (hed : e ≤ d) (hmax : disc B ≤ discOn B e d) (hpos : 0 < discOn B e d) : e ∈ B := by
  revert e d;
  intro e d hed hmax hpos
  by_contra h_contra
  have h_not_in_B : e ∉ B := by
    assumption;
  -- By definition of `discOn`, we know that `discOn (-B) (-d) (-e) = discOn B e d`.
  have h_discOn_symm : discOn (-B) (-d) (-e) = discOn B e d := by
    convert discOn_neg B e d using 1;
  convert right_endpoint_mem_of_disc ( show IsClosed ( -B ) from hB.neg ) ?_ ( show -d ≤ -e by linarith ) ?_ ?_ using 1 <;> norm_num [ h_discOn_symm ];
  · assumption;
  · exact hfin;
  · rw [ disc_neg ] ; linarith;
  · linarith

/-
Difference-set membership from mass bounds (each `≥ half`). If `A`, `B` are closed, `p < q`,
and `A` has mass `≥ (q-p)/2` on `[p-x, q-x]` while `B` has mass `≥ (q-p)/2` on `[p, q]`, then
`x ∈ (B ∩ [p,q]) - (A ∩ [p-x, q-x])`. (Proof: translate `A` by `x`; the two translated masses
sit on `[p,q]` and meet by `inter_nonempty_of_measure`.)
-/
lemma diff_helper_measure (hA : IsClosed A) (hB : IsClosed B) {p q x : ℝ} (hpq : p < q)
    (hAm : (q - p) / 2 ≤ (volume (A ∩ Icc (p - x) (q - x))).toReal)
    (hBm : (q - p) / 2 ≤ (volume (B ∩ Icc p q)).toReal) :
    x ∈ (B ∩ Icc p q) - (A ∩ Icc (p - x) (q - x)) := by
  obtain ⟨ w, hw ⟩ := inter_nonempty_of_measure ( show IsClosed ( ( fun t => t + x ) '' A ) from by
                                                    convert hA.preimage ( show Continuous fun t => t - x from continuous_id.sub continuous_const ) using 1 ; ext ; aesop ) hB hpq ( show ( q - p ) / 2 ≤ ( MeasureTheory.volume ( ( fun t => t + x ) '' A ∩ Icc p q ) |> ENNReal.toReal ) from by
                                                                                                                      convert hAm using 1;
                                                                                                                      rw [ show ( fun t => t + x ) '' A ∩ Icc p q = ( fun t => t + x ) '' ( A ∩ Icc ( p - x ) ( q - x ) ) from ?_ ];
                                                                                                                      · rw [ Set.image_add_right ];
                                                                                                                        rw [ MeasureTheory.measure_preimage_add_right ];
                                                                                                                      · ext ; aesop ) hBm;
  rcases hw with ⟨ ⟨ ⟨ y, hy, rfl ⟩, hy' ⟩, hy'' ⟩ ; exact ⟨ _, ⟨ hy', hy'' ⟩, _, ⟨ hy, ⟨ by linarith [ hy''.1 ], by linarith [ hy''.2 ] ⟩ ⟩, by ring ⟩ ;

/-
Difference-set membership from a discrepancy-sum bound (both sets nonempty). If `A`, `B` are
closed, `p < q`, both `A ∩ [p-x, q-x]` and `B ∩ [p, q]` are nonempty, and
`d_A([p-x,q-x]) + d_B([p,q]) ≥ 0`, then `x ∈ (B ∩ [p,q]) - (A ∩ [p-x, q-x])`.
-/
lemma diff_helper_discOn (hA : IsClosed A) (hB : IsClosed B) {p q x : ℝ} (hpq : p < q)
    (hAne : (A ∩ Icc (p - x) (q - x)).Nonempty) (hBne : (B ∩ Icc p q).Nonempty)
    (h : 0 ≤ discOn A (p - x) (q - x) + discOn B p q) :
    x ∈ (B ∩ Icc p q) - (A ∩ Icc (p - x) (q - x)) := by
  -- Let `A' := (fun t => t + x) '' A`, closed (translation homeomorphism).
  set A' : Set ℝ := (fun t => t + x) '' A;
  -- Then `0 ≤ discOn A' p q + discOn B p q` from `h`, and both `A' ∩ Icc p q`, `B ∩ Icc p q` are nonempty.
  have h_disc : 0 ≤ discOn A' p q + discOn B p q := by
    refine le_trans h ?_;
    unfold discOn A'; simp +decide [ *, Set.image_add_right ] ;
    rw [ show ( fun t => t + -x ) ⁻¹' A ∩ Icc p q = ( fun t => t + -x ) ⁻¹' ( A ∩ Icc ( p - x ) ( q - x ) ) by ext; aesop ] ; rw [ MeasureTheory.measure_preimage_add_right ] ;
  have hA'_nonempty : (A' ∩ Icc p q).Nonempty := by
    exact hAne.elim fun y hy => ⟨ y + x, Set.mem_image_of_mem _ hy.1, by constructor <;> linarith [ hy.2.1, hy.2.2 ] ⟩
  have hB_nonempty : (B ∩ Icc p q).Nonempty := by
    assumption;
  obtain ⟨ w, hw₁, hw₂ ⟩ := inter_nonempty_of_discOn ( show IsClosed A' from by
                                                        convert hA.preimage ( show Continuous fun t => t - x from continuous_id.sub continuous_const ) using 1 ; aesop ) hB hpq hA'_nonempty hB_nonempty h_disc;
  simp +zetaDelta at *;
  exact ⟨ w, ⟨ hw₁.2, hw₂ ⟩, w + -x, ⟨ hw₁.1, by constructor <;> linarith ⟩, by ring ⟩

/-
Difference-set membership from a *strict* discrepancy-sum bound (no nonemptiness needed).
If `A`, `B` are measurable, `p < q`, and `d_A([p-x,q-x]) + d_B([p,q]) > 0`, then
`x ∈ (B ∩ [p,q]) - (A ∩ [p-x, q-x])`.
-/
lemma diff_helper_pos (hA : MeasurableSet A) (hB : MeasurableSet B) {p q x : ℝ} (hpq : p < q)
    (h : 0 < discOn A (p - x) (q - x) + discOn B p q) :
    x ∈ (B ∩ Icc p q) - (A ∩ Icc (p - x) (q - x)) := by
  have := inter_nonempty_of_discOn_pos (by
  convert hA.preimage ( show Measurable ( fun t => t - x ) from measurable_id.sub measurable_const ) using 1 ; ext ; aesop : MeasurableSet ((fun t => t + x) '' A)) hB hpq (by
  unfold discOn at *;
  rw [ show ( fun t => t + x ) '' A ∩ Icc p q = ( fun t => t + x ) '' ( A ∩ Icc ( p - x ) ( q - x ) ) from ?_ ];
  · rw [ Set.image_add_right ];
    rw [ MeasureTheory.measure_preimage_add_right ] ; linarith;
  · ext ; aesop : 0 < discOn ((fun t => t + x) '' A) p q + discOn B p q);
  exact this.imp fun w hw => by aesop;

/-- The mass of `A` on `[a,b]` is at most the length `b - a` (for `a ≤ b`). -/
lemma mass_inter_Icc_le (A : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    (volume (A ∩ Icc a b)).toReal ≤ b - a := by
  refine le_trans (ENNReal.toReal_mono ?_ (measure_mono Set.inter_subset_right)) ?_
  · simp [Real.volume_Icc]
  · simp [Real.volume_Icc, hab]

/-- `discOn A a b ≤ b - a` for `a ≤ b`. -/
lemma discOn_le_sub (A : Set ℝ) {a b : ℝ} (hab : a ≤ b) : discOn A a b ≤ b - a := by
  have := mass_inter_Icc_le A hab
  unfold discOn; linarith

/-- Shifted form of `diff_helper_measure`: `A`-interval `[a',b']`, `B`-interval `[a'+x,b'+x]`. -/
lemma diff_mem_measure (hA : IsClosed A) (hB : IsClosed B) {a' b' x : ℝ} (hab' : a' < b')
    (hAm : (b' - a') / 2 ≤ (volume (A ∩ Icc a' b')).toReal)
    (hBm : (b' - a') / 2 ≤ (volume (B ∩ Icc (a' + x) (b' + x))).toReal) :
    x ∈ (B ∩ Icc (a' + x) (b' + x)) - (A ∩ Icc a' b') := by
  have h := diff_helper_measure (p := a' + x) (q := b' + x) (x := x) hA hB (by linarith)
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using hAm)
    (by simpa using hBm)
  simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h

/-- Shifted form of `diff_helper_discOn`. -/
lemma diff_mem_discOn (hA : IsClosed A) (hB : IsClosed B) {a' b' x : ℝ} (hab' : a' < b')
    (hAne : (A ∩ Icc a' b').Nonempty) (hBne : (B ∩ Icc (a' + x) (b' + x)).Nonempty)
    (h : 0 ≤ discOn A a' b' + discOn B (a' + x) (b' + x)) :
    x ∈ (B ∩ Icc (a' + x) (b' + x)) - (A ∩ Icc a' b') := by
  have h2 := diff_helper_discOn (p := a' + x) (q := b' + x) (x := x) hA hB (by linarith)
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using hAne)
    hBne
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h)
  simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h2

/-- Shifted form of `diff_helper_pos`. -/
lemma diff_mem_pos (hA : IsClosed A) (hB : IsClosed B) {a' b' x : ℝ} (hab' : a' < b')
    (h : 0 < discOn A a' b' + discOn B (a' + x) (b' + x)) :
    x ∈ (B ∩ Icc (a' + x) (b' + x)) - (A ∩ Icc a' b') := by
  have h2 := diff_helper_pos (p := a' + x) (q := b' + x) (x := x) hA.measurableSet hB.measurableSet
    (by linarith)
    (by simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h)
  simpa [show a' + x - x = a' from by ring, show b' + x - x = b' from by ring] using h2

/-- Pointwise core of `main_step`: for `x` in the *open* interval, `x` lies in the difference set.
This is the four-case analysis; `main_step` follows by a closure argument. -/
lemma main_step_mem (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsRightBalanced A a b) (hJ : IsLeftBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) {x : ℝ}
    (hx1 : c - b < x) (hx2 : x < c - b + 2 * (volume (B ∩ Icc c d)).toReal) :
    x ∈ (B ∩ Icc c d) - (A ∩ Icc a b) := by
  have hAab_le : discOn A a b ≤ b - a := discOn_le_sub A hab.le
  have hBcd_le : discOn B c d ≤ disc B := discOn_le_disc hBfin hcd.le
  have hBcd_gt : x - d + b < discOn B c d := by unfold discOn; linarith
  have hxda : x < d - a := by unfold discOn at hBcd_le; linarith
  rcases le_or_gt x (d - b) with hdb | hdb
  · rcases le_or_gt x (c - a) with hca | hca
    · -- CASE 1
      have hA0 : 0 ≤ discOn A (c - x) b := hI.2 _ (by linarith) (by linarith)
      have hB0 : 0 ≤ discOn B c (b + x) := hJ.2 _ (by linarith) (by linarith)
      have hmem := diff_mem_measure (a' := c - x) (b' := b) (x := x) hA hB (by linarith)
        (by unfold discOn at hA0; linarith)
        (by
          have hcx : c - x + x = c := by ring
          rw [hcx]; unfold discOn at hB0; linarith)
      have hcx : c - x + x = c := by ring
      rw [hcx] at hmem
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl c) (by linarith)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (le_refl b))) hmem
    · -- CASE 2
      have hA0 : 0 ≤ discOn A a b := hI.2 _ (le_refl a) hab.le
      have hApos : 0 < (volume (A ∩ Icc a b)).toReal := by unfold discOn at hA0; linarith
      have hAne : (A ∩ Icc a b).Nonempty := by
        rcases Set.eq_empty_or_nonempty (A ∩ Icc a b) with h | h
        · rw [h] at hApos; simp at hApos
        · exact h
      have hadd : discOn B c (b + x) = discOn B c (a + x) + discOn B (a + x) (b + x) :=
        discOn_add hB.measurableSet (by linarith) (by linarith)
      have hBb : 0 ≤ discOn B c (b + x) := hJ.2 _ (by linarith) (by linarith)
      have hcax_le : discOn B c (a + x) ≤ disc B := discOn_le_disc hBfin (by linarith)
      have hBne : (B ∩ Icc (a + x) (b + x)).Nonempty := by
        rcases Set.eq_empty_or_nonempty (B ∩ Icc (a + x) (b + x)) with hEmp | h
        · exfalso
          have hde : discOn B (a + x) (b + x) = -(b - a) := by
            unfold discOn; rw [hEmp]; simp
          have hcax_eq : discOn B c (a + x) = b - a := by linarith
          have hmemB : a + x ∈ B :=
            right_endpoint_mem_of_disc (c := c) (e := a + x) hB hBfin
              (by linarith) (by linarith) (by linarith)
          exact absurd (⟨a + x, hmemB, by constructor <;> linarith⟩ :
              (B ∩ Icc (a + x) (b + x)).Nonempty)
            (Set.not_nonempty_iff_eq_empty.mpr hEmp)
        · exact h
      have hsum : 0 ≤ discOn A a b + discOn B (a + x) (b + x) := by linarith
      have hmem := diff_mem_discOn (a' := a) (b' := b) (x := x) hA hB hab hAne hBne hsum
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (by linarith)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl a) (le_refl b))) hmem
  · rcases le_or_gt x (c - a) with hca | hca
    · -- CASE 3a
      have hA0 : 0 ≤ discOn A (c - x) b := hI.2 _ (by linarith) (by linarith)
      have hadd : discOn A (c - x) b = discOn A (c - x) (d - x) + discOn A (d - x) b :=
        discOn_add hA.measurableSet (by linarith) (by linarith)
      have hAdxb : discOn A (d - x) b ≤ b - (d - x) := discOn_le_sub A (by linarith)
      have hpos : 0 < discOn A (c - x) (d - x) + discOn B c d := by linarith
      have hmem := diff_mem_pos (a' := c - x) (b' := d - x) (x := x) hA hB (by linarith)
        (by
          have h1 : c - x + x = c := by ring
          have h2 : d - x + x = d := by ring
          rw [h1, h2]; exact hpos)
      have h1 : c - x + x = c := by ring
      have h2 : d - x + x = d := by ring
      rw [h1, h2] at hmem
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl c) (le_refl d)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (by linarith))) hmem
    · -- CASE 3b
      have hadd_A : discOn A a b = discOn A a (d - x) + discOn A (d - x) b :=
        discOn_add hA.measurableSet (by linarith) (by linarith)
      have hAdxb : discOn A (d - x) b ≤ b - (d - x) := discOn_le_sub A (by linarith)
      have hadd_B : discOn B c d = discOn B c (a + x) + discOn B (a + x) d :=
        discOn_add hB.measurableSet (by linarith) (by linarith)
      have hcax_le : discOn B c (a + x) ≤ disc B := discOn_le_disc hBfin (by linarith)
      have hpos : 0 < discOn A a (d - x) + discOn B (a + x) d := by linarith
      have hmem := diff_mem_pos (a' := a) (b' := d - x) (x := x) hA hB (by linarith)
        (by
          have h2 : d - x + x = d := by ring
          rw [h2]; exact hpos)
      have h2 : d - x + x = d := by ring
      rw [h2] at hmem
      exact Set.sub_subset_sub
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (by linarith) (le_refl d)))
        (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc (le_refl a) (by linarith))) hmem

/-
**Lemma "main step".** Let `I = [a,b]` be right balanced w.r.t. `A` and `J = [c,d]` left
balanced w.r.t. `B`, with `d_A(I) ≥ d(B)` and both intervals nondegenerate. Then
`(B ∩ J) - (A ∩ I) ⊇ [c-b, c-b + 2|B ∩ J|]`.
-/
lemma main_step (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsRightBalanced A a b) (hJ : IsLeftBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) :
    Icc (c - b) (c - b + 2 * (volume (B ∩ Icc c d)).toReal) ⊆
      (B ∩ Icc c d) - (A ∩ Icc a b) := by
  -- By `main_step_mem`, `Set.Ioo (c-b) (c-b+2*m) ⊆ D`.
  have h_open : Set.Ioo (c - b) (c - b + 2 * (volume (B ∩ Icc c d)).toReal) ⊆ (B ∩ Icc c d) - (A ∩ Icc a b) := by
    intro x hx; exact main_step_mem hA hB hAfin hBfin hab hcd hI hJ hdisc hx.1 hx.2;
  -- Therefore `closure (Set.Ioo (c-b) (c-b+2*m)) ⊆ D` by `closure_minimal` (D closed).
  have h_closure : closure (Set.Ioo (c - b) (c - b + 2 * (volume (B ∩ Icc c d)).toReal)) ⊆ (B ∩ Icc c d) - (A ∩ Icc a b) := by
    refine' closure_minimal h_open _;
    have h_compact : IsCompact (B ∩ Icc c d) ∧ IsCompact (A ∩ Icc a b) := by
      exact ⟨ CompactIccSpace.isCompact_Icc.of_isClosed_subset ( hB.inter isClosed_Icc ) fun x hx => hx.2, CompactIccSpace.isCompact_Icc.of_isClosed_subset ( hA.inter isClosed_Icc ) fun x hx => hx.2 ⟩;
    have h_compact_diff : IsCompact ((B ∩ Icc c d) - (A ∩ Icc a b)) := by
      convert h_compact.1.add h_compact.2.neg using 1 ; ext ; simp +decide [ sub_eq_add_neg ];
    exact h_compact_diff.isClosed;
  refine' Set.Subset.trans _ h_closure;
  rw [ closure_Ioo ];
  have := hJ.2 d ( by linarith ) ( by linarith ) ; norm_num [ discOn ] at this ; linarith

/-
**Corollary "main step sums", first part.** If `I = [a,b]` is left balanced w.r.t. `A`,
`J = [c,d]` left balanced w.r.t. `B`, both nondegenerate, and `d_A(I) ≥ d(B)`, then
`(A ∩ I) + (B ∩ J) ⊇ [a+c, a+c + 2|B ∩ J|]`.
-/
lemma main_step_sums_left (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsLeftBalanced A a b) (hJ : IsLeftBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) :
    Icc (a + c) (a + c + 2 * (volume (B ∩ Icc c d)).toReal) ⊆
      (A ∩ Icc a b) + (B ∩ Icc c d) := by
  -- By Lemma `main_step`, we have
  have h_main_step : Icc (c - (-a)) (c - (-a) + 2 * (volume (B ∩ Icc c d)).toReal) ⊆ (B ∩ Icc c d) - ((-A) ∩ Icc (-b) (-a)) := by
    apply main_step;
    any_goals assumption;
    · exact hA.neg;
    · aesop;
    · linarith;
    · constructor;
      · linarith;
      · intro c hc₁ hc₂;
        convert hI.2 ( -c ) ( by linarith ) ( by linarith ) using 1;
        convert discOn_neg A a ( -c ) using 1 ; ring;
    · rwa [ discOn_neg ];
  convert h_main_step using 1 ; ring;
  ext ; simp +decide [ Set.mem_add, Set.mem_sub ] ; ring;
  exact ⟨ fun ⟨ x, hx, y, hy, hxy ⟩ => ⟨ y, hy, -x, ⟨ by simpa using hx.1, by linarith, by linarith ⟩, by linarith ⟩, fun ⟨ x, hx, y, hy, hxy ⟩ => ⟨ -y, ⟨ by simpa using hy.1, by linarith, by linarith ⟩, x, hx, by linarith ⟩ ⟩

/-
**Corollary "main step sums", second part.** If `I = [a,b]` is right balanced w.r.t. `A`,
`J = [c,d]` right balanced w.r.t. `B`, both nondegenerate, and `d_A(I) ≥ d(B)`, then
`(A ∩ I) + (B ∩ J) ⊇ [b+d - 2|B ∩ J|, b+d]`.
-/
lemma main_step_sums_right (hA : IsClosed A) (hB : IsClosed B) (hAfin : volume A ≠ ⊤)
    (hBfin : volume B ≠ ⊤) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hI : IsRightBalanced A a b) (hJ : IsRightBalanced B c d)
    (hdisc : disc B ≤ discOn A a b) :
    Icc (b + d - 2 * (volume (B ∩ Icc c d)).toReal) (b + d) ⊆
      (A ∩ Icc a b) + (B ∩ Icc c d) := by
  -- Reflect the intervals and apply `main_step_sums_left`.
  have h_reflect : IsLeftBalanced (-A) (-b) (-a) ∧ IsLeftBalanced (-B) (-d) (-c) := by
    constructor <;> constructor <;> try linarith;
    · intro x hx₁ hx₂; have := hI.2 ( -x ) ( by linarith ) ( by linarith ) ; simp_all +decide [ discOn_neg ] ;
      convert this using 1;
      convert discOn_neg A ( -x ) b using 1 ; ring;
    · intro x hx₁ hx₂; convert hJ.2 ( -x ) ( by linarith ) ( by linarith ) using 1;
      convert discOn_neg B ( -x ) d using 1 ; ring;
  have h_reflect : Icc (-b + -d) (-b + -d + 2 * (volume (-B ∩ Icc (-d) (-c))).toReal) ⊆ (-A ∩ Icc (-b) (-a)) + (-B ∩ Icc (-d) (-c)) := by
    apply_rules [ main_step_sums_left ] <;> try linarith;
    any_goals tauto;
    · exact hA.neg;
    · exact hB.neg;
    · simp_all +decide [ MeasureTheory.measureReal_def ];
    · aesop;
    · grind +suggestions;
  intro x hx; specialize h_reflect ( show -x ∈ Icc ( -b + -d ) ( -b + -d + 2 * ( volume ( -B ∩ Icc ( -d ) ( -c ) ) |> ENNReal.toReal ) ) from ?_ ) ; simp_all +decide [ Set.mem_add ] ;
  · rw [ show -B ∩ Icc ( -d ) ( -c ) = - ( B ∩ Icc c d ) by ext; aesop ] ; rw [ MeasureTheory.Measure.measure_neg ] ; constructor <;> linarith;
  · obtain ⟨ y, hy, z, hz, hyz ⟩ := h_reflect;
    exact ⟨ -y, ⟨ by simpa using hy.1, by constructor <;> linarith [ hy.2.1, hy.2.2 ] ⟩, -z, ⟨ by simpa using hz.1, by constructor <;> linarith [ hz.2.1, hz.2.2 ] ⟩, by norm_num; linarith ⟩

end ProductFree