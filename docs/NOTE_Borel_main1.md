# Progress note: the Borel/measurable product-free bound (`main1`)

This note records the work done on the "final subproject" (extending the paper's results
from finite unions of closed intervals to Borel/measurable and open sets). It complements
`ASSESSMENT_Borel.md`, which scoped the work in advance.

## What is now done (all `sorry`-free)

The **primary** Borel target from the assessment — the product-free *measure bound* for
general sets — is now fully formalized in `RequestProject/Fattening.lean`, using only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and, crucially, **without**
depending on the deep measurable `key_lemma`:

- `ProductFree.main1_measurable`: a **measurable** product-free `E ⊆ (0,1)` has
  `volume E ≤ 1/3`.
- `ProductFree.main1_open'`: an **open** product-free `E ⊆ (0,1)` has `volume E ≤ 1/3`
  (the paper's headline statement), obtained as a corollary of the measurable version.
- `ProductFree.main1_compact'`: a nonempty **compact** product-free `K ⊆ (0,1)` has
  `(volume K).toReal < 1/3`.

These are proved by the *outer fattening* route anticipated in `ASSESSMENT_Borel.md §2a`,
transferring the already-proved finite-interval-union bound `main1_intervalUnion`:

1. `union_Icc_aux` / `IsIntervalUnion.union_Icc` / `exists_isIntervalUnion_biUnion` —
   normalization: any finite union of closed intervals is an `IsIntervalUnion` for a
   canonical sorted, strictly separated list (the "merge intervals" recursion).
2. `exists_intervalUnion_cover` — a compact set is covered by a finite union of closed
   intervals contained in its closed `η`-thickening `K + [-η, η]` (finite subcover).
3. `exists_productFree_thickening` — for compact product-free `K ⊆ (0,1)`, a small closed
   thickening `K + [-δ, δ]` is still product-free and still inside `(0,1)` (positive
   separation of the disjoint compact sets `K·K` and `K`, plus an elementary bound
   `|uv − k₁k₂| ≤ 2δ`).
4. Assembly: fatten `K`, cover by an interval union `F` with `K ⊆ F ⊆ K + [-δ,δ] ⊆ (0,1)`,
   apply `main1_intervalUnion` to `F`, and use inner regularity of Lebesgue measure to lift
   from compact `K` to measurable `E`.

Note: the pre-existing `ProductFree.main1` in `Main1.lean` (open sets) is unchanged and still
routes through `key_lemma`; the new `main1_open'` in `Fattening.lean` is the `sorry`-free
replacement for the same statement.

## What remains

The two pre-existing `sorry`s are untouched (both are the deep cores flagged in `Main.lean`):

- `ProductFree.key_lemma` (`KeyLemma.lean`) — the measurable Section-4 rigidity lemma. It is
  **no longer needed** for the product-free measure bound (that now goes through fattening),
  so it is only relevant as a standalone statement.
- `ProductFree.offdiagonal_main2` / `ProductFree.main2` (`Discrepancy.lean`) — the Borel
  **sumset inequality**. This is the larger second Borel target (`ASSESSMENT_Borel.md §2b`):
  it genuinely needs the "`A+B ≈ A'+B'`" outer-thickening continuity fact together with
  discrepancy continuity `d(Kη) → d(K)`, feeding the proved `offdiagonal_main2_iu` in the
  `η → 0` limit. It has not been started here.
