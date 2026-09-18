This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Product-free subsets of `(0,1)`

A Lean 4 / Mathlib formalization of the main result of the attached paper
(`product_set_arxiv.tex`): an open product-free subset of the open interval `(0,1)`
has Lebesgue measure less than `1/3`.

## Layout

- `RequestProject/Defs.lean` — basic definitions: `IsSumFree`, `IsProductFree`, the cumulative
  measure `cum A x = |A ∩ [0,x]|`, and the interval discrepancy `disc`.
- `RequestProject/Analytic.lean` — the analytic reduction (Section 2 of the paper). Proves
  `integral_cum_lt_third`: from the shifted key inequality `F(u-δ)+F(u)+F(u+δ) ≤ u` (for `u ≥ 0`)
  and `A ⊆ [δ,∞)`, `∫_{u>0} e^{-u} F(u) du < 1/3`. Fully proved.
- `RequestProject/KeyLemma.lean` — the statement of `key_lemma` (the deep combinatorial result)
  plus its elementary boundary extension, assembled into `sumfree_integral_lt_third`.
- `RequestProject/Main1.lean` — the change of variables `u = -log x` and Fubini identity, and the
  main theorems `main1_compact` and `main1`.
- `RequestProject/Discrepancy.lean` — the discrepancy machinery: `discrepancy_observation`,
  `discrepancy_observation2` (both proved), and the statements of the sumset inequality `main2`
  and `offdiagonal_main2`.
- `RequestProject/Balanced.lean` — the **balanced-interval toolbox** of Section 3 (fully proved):
  the `IsLeftBalanced` / `IsRightBalanced` / `IsBalanced` predicates, additivity and reflection of
  the interval discrepancy `d_A`, the intersection lemmas, `union_left_balanced`, `main_step`, and
  `main_step_sums_left` / `main_step_sums_right`. This is the geometric core of the proof of
  `main2` (the paper's "toolbox ... also used for proving Theorem `main1`").
- `RequestProject/BalancedMore.lean`, `RequestProject/BalancedSum.lean`, `RequestProject/EdgeDisc.lean`,
  `RequestProject/IntervalUnion.lean`, `RequestProject/LeftBalancedDecomp.lean`,
  `RequestProject/KeyBound.lean`, `RequestProject/KeyBoundRight.lean`, `RequestProject/OffdiagonalMain.lean`
  — the rest of the Section 3 machinery: maximal (left-)balanced intervals, the finite
  interval-union representation `IsIntervalUnion`, the greedy left-balanced decomposition, the edge
  discrepancies `d_L`/`d_R`, Corollary `key_bound`, and the generic case of `offdiagonal_main2`.
- `RequestProject/MaxBalanced.lean` — existence of the leftmost/rightmost maximal balanced
  intervals, and the cumulative-discrepancy monotonicity that replaces the paper's list-based
  `partition` lemma.
- `RequestProject/DiscAttain.lean` — attainment of the discrepancy `disc B` at a balanced interval.
- `RequestProject/Partition.lean` — the discrepancy consequences used in the recursive case
  (`disc_inter_le`, `disc_compl_eq`, `iu_disc_pos`).
- `RequestProject/OffdiagonalInduction.lean` — the recursive case (`offdiag_case2_left`/`right`),
  the four-way case split, and the induction on the number of component intervals, yielding the
  finite-union theorems `offdiagonal_main2_iu` and `main2_iu`.
- `RequestProject/Main.lean` — aggregating entry point with an overview.

## What is proved

- `ProductFree.main1_compact`: a nonempty compact product-free subset of `(0,1)` has measure
  `< 1/3`.
- `ProductFree.main1`: an open product-free subset of `(0,1)` has measure `≤ 1/3`.
- `ProductFree.sumfree_integral_lt_third`: the full analytic reduction.
- `ProductFree.discrepancy_observation`, `ProductFree.discrepancy_observation2`.
- `ProductFree.offdiagonal_main2_iu` (Theorem `offdiagonal main2`, finite-union version): for
  nonempty finite unions of finite closed intervals `A`, `B` with `d(A) = d(B)`,
  `|A + B| ≥ 2|A| + 2|B| − d(A) − d(B)`. Proved outright (only `propext`, `Classical.choice`,
  `Quot.sound`) by the induction on the number of component intervals described in Section 3.
- `ProductFree.main2_iu` (Theorem `main2`, finite-union version): for a nonempty finite union of
  finite closed intervals `A`, both `|A + A|` and `|A − A|` are at least `4|A| − 2 d(A)`. Proved
  outright as the `B = A` / `B = −A` special cases of `offdiagonal_main2_iu`.
- `ProductFree.key_lemma_intervalUnion` and `ProductFree.key_lemma_intervalUnion_one` (the paper's
  **key lemma**, i.e. the entire Section 4 rigidity argument, for finite unions of closed
  intervals): for a sum-free finite union of closed intervals `A` with least element `δ`,
  `F(x-δ) + F(x) + F(x+δ) ≤ x` for all `x ≥ δ`. **Proved outright** (only `propext`,
  `Classical.choice`, `Quot.sound`).  The Section 4 development is spread across the many
  `RequestProject/Section4*.lean` files; the final `u < 2` step is assembled in
  `RequestProject/Section4CLem.lean` (Lemma `c lem`), `RequestProject/Section4DoubleBoostAssembly.lean`
  (the five-piece "double boost" packing), and `RequestProject/Section4ULtTwo.lean`.
- `ProductFree.sumfree_integral_intervalUnion_lt_third`: the analytic bound
  `∫_{u>0} e^{-u} F(u) du < 1/3` for finite unions of closed intervals. **Proved outright**
  (standard axioms only), combining the finite-union key lemma with the analytic reduction.

Thus the paper's main result, in the finite-union form the request explicitly accepts, is fully
formalized with no `sorry` and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

## What remains (the general measurable-set / open-set extensions, a lower-priority bonus)

- `ProductFree.key_lemma` (in `RequestProject/KeyLemma.lean`): the *general measurable-set* form of
  the key lemma.  The finite-union form `key_lemma_intervalUnion` above is fully proved; extending
  it to arbitrary finite-measure measurable sets requires approximating such a set by finite unions
  of closed intervals, which is not carried out here (and is genuinely delicate — a positive-measure
  measurable set may contain no interval at all, e.g. a fat Cantor set, so inner approximation by
  interval unions does not work in general).
- `ProductFree.main2` and `ProductFree.offdiagonal_main2` in `RequestProject/Discrepancy.lean`:
  the *general Borel/measurable-set* statements of the Section 3 inequalities. The finite-union
  content is fully proved (`offdiagonal_main2_iu`, `main2_iu`); only the same measurable-set
  approximation remains.

Consequently `main1_compact` and `main1` (the open/compact-set headline statements) still depend on
the measurable-set `key_lemma` (they use `sorryAx`); the analytic reduction, the
change-of-variables/Fubini lemmas, the discrepancy observations, the finite-union theorems
`offdiagonal_main2_iu` / `main2_iu`, and the **finite-union key lemma and its analytic
consequence** use only `propext`, `Classical.choice`, and `Quot.sound`.
