import RequestProject.KeyBound

/-!
# Corollary `key_bound`, right version

The right-hand version of `key_bound`, obtained from `key_bound_left` by reflecting in the origin.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A B : Set ℝ}

/-
The reflection `-B` of an interval-union is an interval-union (reverse the list and negate
each interval).
-/
lemma IsIntervalUnion.neg {ivs : List (ℝ × ℝ)} (h : IsIntervalUnion B ivs) :
    IsIntervalUnion (-B) (ivs.reverse.map (fun p => (-p.2, -p.1))) := by
  constructor <;> norm_num [ Set.ext_iff ] at *;
  · rintro a b x y hx rfl rfl; linarith [ h.1 ( x, y ) hx ] ;
  · constructor;
    · have h_chain : List.IsChain (fun p q => p.2 < q.1) ivs := by
        exact h.2.1;
      simp_all +decide [ List.isChain_iff_getElem ];
      grind;
    · intro x; rw [ h.2.2 ] ; simp +decide [ Set.mem_iUnion ] ;
      grind

/-- The list `ivs.reverse.map (fun p => (-p.2, -p.1))` is empty iff `ivs` is. -/
lemma neg_ivs_ne_nil {ivs : List (ℝ × ℝ)} (hne : ivs ≠ []) :
    (ivs.reverse.map (fun p => (-p.2, -p.1))) ≠ [] := by
  simp [hne]

/-
Reflection swaps the two edge discrepancies: `d_R(-B) = d_L(B)`.
-/
lemma discR_neg_eq_discL (B : Set ℝ) : discR (-B) = discL B := by
  by_contra h_contra';
  contrapose! h_contra' ; ( unfold discR discL ; simp +decide [ discOn_neg ] ; );
  congr with r;
  constructor <;> rintro ⟨ x, hx, rfl ⟩ <;> use -x <;> simp_all +decide [ discOn_neg ];
  exact ⟨ by linarith, by simpa using discOn_neg B ( sInf B ) ( -x ) ⟩

/-
If `[a,b]` is right balanced w.r.t. `A`, then `[-b,-a]` is left balanced w.r.t. `-A`.
-/
lemma IsRightBalanced.neg_left {a b : ℝ} (h : IsRightBalanced A a b) :
    IsLeftBalanced (-A) (-b) (-a) := by
  cases h;
  unfold IsLeftBalanced; norm_num;
  refine' ⟨ by assumption, fun c hc₁ hc₂ => _ ⟩;
  convert ‹∀ c : ℝ, a ≤ c → c ≤ b → 0 ≤ discOn A c b› ( -c ) ( by linarith ) ( by linarith ) using 1;
  convert discOn_reflect_sub A _ _ _ using 2 ; ring;
  rotate_right;
  exacts [ 0, by ext; simp +decide [ neg_eq_iff_eq_neg ], by ring, by ring ]

/-
**Corollary `key_bound` (right version).** If `[a,b]` is right balanced w.r.t. a closed set
`A` with `a < b`, `B` is a nonempty finite union of finite closed intervals, and
`d_A([a,b]) ≥ d(B)`, then
`|((A ∩ [a,b]) + B) ∩ [b + min B - d_L(B), b + max B]| ≥ 2|B|`.
-/
lemma key_bound_right (A : Set ℝ) {B : Set ℝ} {ivs : List (ℝ × ℝ)}
    (hA : IsClosed A) (hAfin : volume A ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hI : IsRightBalanced A a b) (hB : IsIntervalUnion B ivs) (hBne : ivs ≠ [])
    (hdisc : disc B ≤ discOn A a b) :
    2 * (volume B).toReal ≤
      (volume (((A ∩ Icc a b) + B) ∩ Icc (b + sInf B - discL B) (b + sSup B))).toReal := by
  have h_key_left : 2 * (volume (-B)).toReal ≤ (volume (((-A ∩ Icc (-b) (-a)) + (-B)) ∩ Icc ((-b) + sInf (-B)) ((-b) + sSup (-B) + discR (-B)))).toReal := by
    apply key_bound_left;
    any_goals exact hB.neg;
    any_goals rw [ neg_lt_neg_iff ] ; linarith;
    · exact hA.neg;
    · convert hAfin using 1;
      norm_num [ MeasureTheory.measureReal_def ];
    · convert IsRightBalanced.neg_left hI using 1;
    · aesop;
    · rw [ discOn_neg, disc_neg ] ; linarith!;
  convert h_key_left using 1;
  · simp +zetaDelta at *;
  · have h_neg : -A ∩ Icc (-b) (-a) = -(A ∩ Icc a b) := by
      ext; simp [Set.mem_neg, Set.mem_Icc];
    rw [ h_neg, show ( - ( A ∩ Icc a b ) + -B ) = - ( ( A ∩ Icc a b ) + B ) from ?_, show ( -b + sInf ( -B ) ) = - ( b + sSup B ) from ?_, show ( -b + sSup ( -B ) + discR ( -B ) ) = - ( b + sInf B - discL B ) from ?_ ];
    · rw [ show ( - ( A ∩ Icc a b + B ) ∩ Icc ( - ( b + sSup B ) ) ( - ( b + sInf B - discL B ) ) ) = - ( ( A ∩ Icc a b + B ) ∩ Icc ( b + sInf B - discL B ) ( b + sSup B ) ) from ?_ ];
      · rw [ MeasureTheory.Measure.measure_neg ];
      · ext; simp [Set.mem_neg, Set.mem_add, Set.mem_Icc];
    · rw [ discR_neg_eq_discL, Real.sSup_neg ] ; ring;
    · norm_num [ neg_add_eq_sub ];
      ring;
    · ext; simp [Set.mem_add, Set.mem_neg];
      exact ⟨ fun ⟨ x, hx, y, hy, hxy ⟩ => ⟨ y, hy, x, hx, by linarith ⟩, fun ⟨ y, hy, x, hx, hxy ⟩ => ⟨ x, hx, y, hy, by linarith ⟩ ⟩

end ProductFree