import RequestProject.Section4Assembly
import RequestProject.Section4YThreeGeometry

/-!
# Section 4: difference-set estimate for `y > 3`

This file packages the finite-interval-union difference-set theorem into the exact
cumulative packing estimate used in the nonempty branch of the proof of `y > 3`.
-/

open MeasureTheory Set
open scoped Pointwise

noncomputable section

namespace ProductFree

variable {A : Set ℝ} {ivs : List (ℝ × ℝ)}

/-
The nonnegative half of the difference set of a finite interval union has the
lower bound supplied by `main2_iu` and symmetry.
-/
lemma intervalUnion_diff_nonneg_lower
    (hIU : IsIntervalUnion A ivs) {t : ℝ} (hdisc : disc A ≤ t) :
    2 * (volume A).toReal - t ≤ (volume ((A - A) ∩ Ici 0)).toReal := by
  by_cases h : ivs = [] <;> simp_all +decide [ disc ];
  · simp_all +decide [ IsIntervalUnion ];
    contrapose! hdisc;
    exact hdisc.trans_le ( le_csSup ⟨ 0, by rintro x ⟨ a, b, hab, rfl ⟩ ; linarith ⟩ ⟨ 0, 0, by norm_num, by norm_num ⟩ );
  · have h_compact : IsCompact (A - A) := by
      have h_compact : IsCompact A := by
        exact hIU.isCompact;
      simpa only [ sub_eq_add_neg ] using h_compact.add h_compact.neg;
    have h_symm : - (A - A) = A - A := by
      ext; simp [Set.mem_sub];
    have h_volume : (volume (A - A)).toReal = 2 * (volume ((A - A) ∩ Ici 0)).toReal := by
      convert compact_symmetric_measure_eq_twice_nonneg h_compact h_symm using 1;
    have := ProductFree.main2_iu hIU (by
    assumption);
    linarith [ show disc A ≤ t from hdisc ]

/-- Apply `main2_iu` to a restriction `A ∩ [p,q]`, retain the nonnegative half of
its symmetric difference set, and pack it with `A ∩ [0,r]` using sum-freeness. -/
lemma restricted_difference_packing
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A)
    {p q r t : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 ≤ r)
    (hlen : q - p ≤ r)
    (hdisc : disc (A ∩ Icc p q) ≤ t) :
    2 * (cum A q - cum A p) + cum A r ≤ r + t := by
  obtain ⟨ivsB, hB⟩ := hIU.inter_Icc_exists p q
  have hlower := intervalUnion_diff_nonneg_lower hB hdisc
  have hsubset : ((A ∩ Icc p q) - (A ∩ Icc p q)) ∩ Ici 0 ⊆
      (A - A) ∩ Icc 0 r := by
    rintro d ⟨⟨u, hu, v, hv, rfl⟩, hd⟩
    exact ⟨⟨u, hu.1, v, hv.1, rfl⟩, hd, by linarith [hu.2.2, hv.2.1]⟩
  have hmono : (volume (((A ∩ Icc p q) - (A ∩ Icc p q)) ∩ Ici 0)).toReal ≤
      (volume ((A - A) ∩ Icc 0 r)).toReal := by
    apply ENNReal.toReal_mono
    · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
        (by simp +decide))
    · exact MeasureTheory.measure_mono hsubset
  have hpack := diff_mass_add_mass_le_length hIU.isClosed.measurableSet hsf hr
  rw [cum_sub_cum_eq_mass_Icc hp hpq]
  have hcumr : cum A r = (volume (A ∩ Icc 0 r)).toReal := rfl
  linarith

/-
Assemble the nonempty case of the paper's proof that `y > 3` directly from the
selected maximizing interval, a point `z ∈ A ∩ [b+1,x]`, and the extrema around the
first forced gap.
-/
lemma section4_y_gt_three_nonempty_branch
    (hIU : IsIntervalUnion A ivs) (hsf : IsSumFree A) (hmin : IsLeast A 1)
    {a b x u z : ℝ} (hx : 1 ≤ x) (hxA : x + 1 ∈ A)
    (hfail : x < cum A (x - 1) + cum A x + cum A (x + 1))
    (hab : a < b) (hbtop : b ≤ x + 1) (haA : a ∈ A)
    (hbal : IsBalanced A a b)
    (hmax : disc (A ∩ Icc 0 (x + 1)) ≤ discOn A a b)
    (hys : 2 + (b - a) < x + 1 - a)
    (huA : u ∈ A) (hu : u < x + 1 - a - 1)
    (hu_max : ∀ r ∈ A, r ≤ x + 1 - a - 1 → r ≤ u)
    (hgap : A ∩ Icc (x + 1 - a - 1) (x + 1 - a - (b - a)) = ∅)
    (hzA : z ∈ A) (hzlow : b + 1 ≤ z) (hzhigh : z ≤ x) :
    3 < x + 1 - a := by
  have := @restricted_difference_packing A ivs hIU hsf;
  have hdiff : 2 * (cum A (x + 1) - cum A (x + 1 - a)) + cum A a ≤ a + discOn A a b := by
    apply this;
    · linarith [ hmin.2 haA ];
    · linarith [ hmin.2 haA ];
    · linarith [ hmin.2 haA ];
    · linarith;
    · apply disc_restriction_le_maximizer;
      any_goals exact hmax;
      · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
        exact Set.Icc 0 ( x + 1 );
        · exact Set.inter_subset_right;
        · norm_num;
      · linarith [ hmin.2 haA ];
      · linarith;
  have hlong : cum A (x - 1) - cum A a ≤ (x - 1 - a + discOn A a b) / 2 := by
    apply cum_increment_le_of_discOn_le;
    · linarith [ hmin.2 haA ];
    · linarith [ hmin.2 haA ];
    · refine' le_trans _ hmax;
      refine' le_csSup _ _;
      · refine' ⟨ 2 * ( volume ( A ∩ Icc 0 ( x + 1 ) ) |> ENNReal.toReal ) + ( x + 1 ), fun r hr => _ ⟩ ; rcases hr with ⟨ a, b, hab, rfl ⟩ ; norm_num;
        refine' le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| Set.inter_subset_left ) zero_le_two ) <| by positivity ) <| by linarith;
        refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) _ );
        exact Set.Icc 0 ( x + 1 );
        · exact Set.inter_subset_right;
        · norm_num;
      · use a, x - 1;
        constructor;
        · linarith [ hmin.2 haA ];
        · rw [ show A ∩ Icc 0 ( x + 1 ) ∩ Icc a ( x - 1 ) = A ∩ Icc a ( x - 1 ) from ?_ ];
          · unfold discOn; ring;
          · ext; simp [Set.mem_inter_iff, Set.mem_Icc];
            exact fun _ _ _ => ⟨ by linarith [ hmin.2 haA ], by linarith ⟩;
  have hsurplus : 1 - discOn A a b < cum A (x + 1) - cum A x := by
    apply section4_first_mass_surplus hIU hsf hmin hx hmax hfail;
  have := @y_gt_three_of_point_right A;
  contrapose! this;
  refine' ⟨ _, hsf, hmin, a, b, x, x + 1 - a, b - a, discOn A a b, u, z, hxA, hzA, rfl, rfl, rfl, hab.le, _, _, _, _ ⟩ <;> try linarith;
  · have h_measurable : ∀ p ∈ ivs, MeasurableSet (Set.Icc p.1 p.2) := by
      exact fun p hp => measurableSet_Icc;
    convert MeasurableSet.iUnion fun p : { p : ℝ × ℝ // p ∈ ivs } => h_measurable p p.2 using 1;
    convert hIU.2 using 1;
    simp +decide [ Set.ext_iff ];
    intro h; exact hIU.2.1;
  · have := @section4_basic_parameters A ivs hIU hsf hmin x a b hx hfail hab hbtop haA hbal hmax; linarith;
  · exact ⟨ by linarith, by linarith [ hmin.2 huA ], hu, hu_max, hgap, hdiff, hlong, hsurplus, hfail, this ⟩

end ProductFree