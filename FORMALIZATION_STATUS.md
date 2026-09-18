# Formalization status and correspondence with the paper

This note records the correspondence between the paper *Product-free subsets of (0,1)* and the
Lean 4 development in this repository.

## Main theorem on product-free sets

The paper states:

> Let `A` be an open product-free subset of `(0,1)`. Then `|A| < 1/3`.

The Lean development contains:

- `ProductFree.main1_compact`: for a nonempty **compact** product-free subset of `(0,1)`,
  `(volume E).toReal < 1/3`.
- `ProductFree.main1`: for an **open** product-free subset of `(0,1)`,
  `volume E ≤ ENNReal.ofReal (1/3)`.
- `ProductFree.main1_intervalUnion`: the strict `< 1/3` statement for a finite union of closed
  intervals.
- `ProductFree.main1_open'` in `RequestProject/Fattening.lean`: an independent, `sorry`-free
  outer-fattening proof of the open-set `≤ 1/3` statement.

Thus the current Lean statement for arbitrary open sets is non-strict, while the displayed theorem
in the paper is strict. This distinction should be kept visible in any claim about exact theorem
correspondence.

## Key lemma

The paper's key lemma is represented by `ProductFree.key_lemma` in
`RequestProject/KeyLemma.lean`. The Lean statement is given in a rescaled form with a least element
`δ > 0`, matching the paper's observation that the normalized `min A = 1` version rescales to an
arbitrary positive minimum.

The finite-interval-union version is `ProductFree.key_lemma_intervalUnion`.

## Sumset / difference-set theorem

For finite unions of closed intervals, the formalization proves the paper's Section 3 inequality in
`ProductFree.main2_iu`.

For measurable sets, `ProductFree.main2_measurable` adds a finiteness hypothesis on the relevant
sumset or difference set. The reason is representational: the theorem is written using
`(volume S).toReal`, and `ENNReal.toReal ⊤ = 0`. A finite-measure set can have an infinite-measure
sumset, so the naive real-valued statement without a finiteness hypothesis is not faithful in that
case. A formulation directly in `ENNReal` would be the natural route to an unconditional statement
closer to the paper's wording.

## Proof completeness

A source scan of the provided project finds no active `sorry`, `admit`, or `axiom` declarations;
occurrences of `sorry` in `RequestProject/Discrepancy.lean` and documentation are inside comments
recording earlier/inadmissible statements.

The final Aristotle summary reports that the project builds with no `sorry` and that the main
results depend only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

For archival publication, the recommended final check is to confirm a clean `lake build` in GitHub
Actions and preserve the green CI run together with the release tag.
