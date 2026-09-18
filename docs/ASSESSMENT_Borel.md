# Assessment: extending the results from finite unions of closed intervals to Borel sets

This note assesses how large a project it would be to obtain the Borel/measurable-set
versions of the paper's results from the finite-interval-union versions that are already
fully proved in this repository. It responds to the request:

> I believe that the results for Borel-measurable sets follow from the results for unions
> of closed intervals. Could you assess how large a project it would be to prove this?
> I think the main fact needed is that if A and B are Borel sets of finite measure, then
> they can be approximated by finite unions A' and B' of closed intervals in such a way
> that A+B is approximated by A'+B'.

**Nothing below has been formalized yet** — this is a scoping analysis. Line/lemma counts
are estimates calibrated against the existing files in this project.

## 1. Current state

The project has exactly two remaining `sorry`s, both of them the general
measurable-set statements (the "much lower priority" bonus of the original task):

- `ProductFree.offdiagonal_main2` in `RequestProject/Discrepancy.lean` — Theorem `main2`
  (the sumset/difference-set inequality `|A+B| ≥ 2|A|+2|B|−d(A)−d(B)`) for measurable sets
  of finite measure.
- `ProductFree.key_lemma` in `RequestProject/KeyLemma.lean` — the key lemma
  `F(x−δ)+F(x)+F(x+δ) ≤ x` for measurable sum-free sets.

The corresponding **finite-interval-union statements are fully proved** (`sorry`-free, only
standard axioms):

- `offdiagonal_main2_iu` and `main2_iu` in `RequestProject/OffdiagonalInduction.lean`,
- `key_lemma_intervalUnion` / `sumfree_integral_intervalUnion_lt_third` in `RequestProject/KeyLemma.lean`,
- `main1_intervalUnion` in `RequestProject/Main1.lean` (product-free **finite union of
  closed intervals** in `(0,1)` has measure `< 1/3`).

The open-set theorem `main1` in `Main1.lean` is already assembled, but it currently routes
through `main1_compact → sumfree_integral_lt_third → key_lemma` (the measurable key lemma),
so it is proved *modulo* that one `sorry`.

## 2. The two headline Borel results are of very different difficulty

It is important to separate the two, because they are reached by different routes.

### 2a. The product-free measure bound for Borel sets (`main1`) — SMALL–MODERATE

**Key observation:** the measurable/open product-free bound does **not** need the measurable
`key_lemma` at all. It follows from the already-proved `main1_intervalUnion` by an *outer
fattening* argument, and the delicate "A+B ≈ A'+B'" approximation is **not** required here.

Route:
1. Any measurable product-free `E ⊆ (0,1)` has `vol E = sup { vol K : K ⊆ E compact }` by
   inner regularity of Lebesgue measure (`MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`,
   already used in the current `main1`).
2. Each compact `K ⊆ E` is product-free (subsets of product-free sets are product-free —
   `IsProductFree.subset` already exists).
3. For a compact product-free `K ⊆ (0,1)`, its closed `η`-neighborhood `Kη` is, for small
   `η`, **still product-free** and is a **finite union of closed intervals** with `K ⊆ Kη ⊆ (0,1)`.
   Hence `main1_intervalUnion` gives `vol Kη < 1/3`, so `vol K ≤ vol Kη < 1/3`.
4. Taking the supremum, `vol E ≤ 1/3`.

Why fattening preserves product-freeness: in log coordinates (`A = −log K`, sum-free and
compact), `A+A` is compact and disjoint from `A`, so `dist(A+A, A) = 2d > 0`. For
`η < 2d/3`, points of the `η`-neighborhood `Aη` sum into the `2η`-neighborhood of `A+A`,
which stays at distance `> η` from `A`, hence outside `Aη`. Everything is bounded, so the
same holds back in `(0,1)`. This is elementary and clean.

Why the neighborhood is a **finite** union of intervals: the closed `η`-neighborhood of a
compact set has, inside its convex hull, only finitely many complementary gaps (each gap of
`K` longer than `2η` survives, and there are at most `diam(K)/(2η)` of those). So `Kη` is a
genuine finite union of closed intervals — no dependence on `K` having nonempty interior.

Estimated work (3–6 subagent lemmas, ~350–650 lines total):
- `compact_neighborhood_isIntervalUnion` (produce the `ivs` list; the chain/ordering
  bookkeeping is the bulk): moderate–hard, ~150–300 lines.
- `productFree_neighborhood` (compactness + positive distance + continuity of `·`): moderate,
  ~100–200 lines.
- `main1_measurable` assembly (inner regularity → fatten → `main1_intervalUnion` → sup):
  small–moderate, ~80–150 lines.

**Confidence: high.** This closes the primary Borel/open result and lets `main1` be
re-routed to no longer depend on the `key_lemma` `sorry`.

**Note on `key_lemma` (measurable) itself.** Proving the measurable key lemma *directly*
from `key_lemma_intervalUnion` is the wrong tool: interval-union approximation does **not**
preserve sum-freeness, which the whole of Section 4 relies on, so there is no cheap transfer.
Once `main1` is routed through fattening (2a), the measurable `key_lemma` is no longer needed
for the product-free theorem and can be left as an (optional) stand-alone curiosity.

### 2b. The sumset inequality for Borel sets (`offdiagonal_main2` / `main2`) — MODERATE–LARGE

This is where the approximation you describe ("A+B approximated by A'+B'") is genuinely
required, and where the difficulty you anticipated (a positive-measure set may contain no
interval, e.g. a fat Cantor set) really bites.

The naive idea — approximate `A` *from inside* by a finite union of intervals `A' ⊆ A` —
**fails**, because such `A'` need not exist. The correct route uses **outer** `η`-thickening
plus measure continuity *from above*:

1. Reduce to compact `A, B` by inner regularity (`vol A = sup vol K`, `A+B ⊇ K+L`).
2. For compact `K, L`, thicken to finite interval unions `Kη ⊇ K`, `Lη ⊇ L`.
3. Apply the proved `offdiagonal_main2_iu` to `Kη, Lη`, then let `η ↓ 0`, using:
   - `vol Kη ↓ vol K` (measure continuity from above; `K = ⋂η Kη`),
   - `vol(Kη+Lη) ↓ vol(K+L)` — **this is exactly your "A+B ≈ A'+B'" fact**, and it holds
     precisely because `K+L = ⋂η (Kη+Lη)` with everything compact (continuity from above,
     `tendsto_measure_iInter`),
   - `d(Kη) → d(K)` (continuity of the discrepancy under thickening).

The interesting subtleties:
- `offdiagonal_main2_iu` carries the hypothesis `d(A) = d(B)`. For the **symmetric** cases
  actually used by `main2` (`B = A` for `|A+A|`, `B = −A` for `|A−A|`) this is automatic, so
  the symmetric `main2` for Borel sets is the easier target. For the **general** off-diagonal
  `d(A)=d(B)` one additionally needs a discrepancy-matching device (the paper's "reduce d"
  Lemma), which is extra work.
- Discrepancy continuity `d(Kη) → d(K)` is a custom analytic lemma (the discrepancy is a
  `sSup` over intervals of `2|A∩I|−|I|`); it is the most delicate single piece.

Estimated work (6–10 subagent lemmas, ~800–1400 lines total):
- neighborhood-is-interval-union (shared with 2a),
- `vol Kη ↓ vol K` via `tendsto_measure_iInter`: moderate, ~80 lines,
- `vol(Kη+Lη) ↓ vol(K+L)` (prove `⋂η(Kη+Lη)=K+L`, compactness/nesting): moderate–hard,
  ~150–250 lines — **the core of your suggested fact**,
- discrepancy continuity `d(Kη)→d(K)`: moderate–hard, ~150–300 lines,
- compact `main2` from `offdiagonal_main2_iu` by the `η→0` limit: moderate–hard, ~150–300 lines,
- Borel from compact (inner regularity + `d` matching): moderate, ~150 lines.

**Confidence: medium–high** for the symmetric `main2` (`|A+A|`, `|A−A|`), which is what the
paper's Theorem `main2` asserts and what `ProductFree.main2` in `Discrepancy.lean` needs;
**medium** for the fully general `offdiagonal_main2` with arbitrary `B` and `d(A)=d(B)`,
because of the discrepancy-matching step.

## 3. Bottom line

- Your intuition is correct: the Borel results do follow from the interval-union results by
  approximation, and the "A+B ≈ A'+B'" fact is the right central lemma — but only for the
  sumset theorem (`main2`), and in the form **outer thickening + measure continuity from
  above**, not inner approximation (which is impossible for empty-interior sets).
- The **primary** Borel/open product-free bound (`main1`) is the smaller project and does
  **not** need that fact at all: an outer *fattening* argument transfers `main1_intervalUnion`
  directly, bypassing the measurable `key_lemma`. Estimate: **~350–650 lines, a few lemmas,
  high confidence** — a genuinely small project.
- The Borel **sumset inequality** (`main2`) is the larger project and is where "A+B ≈ A'+B'"
  is needed. Estimate: **~800–1400 lines, several nontrivial lemmas, medium(-high)
  confidence**; the symmetric case (`|A+A|`, `|A−A|`) is easier than the general
  off-diagonal.
- Shared infrastructure (the "closed `η`-neighborhood of a compact set is a finite union of
  closed intervals" lemma) is reusable across both and is the main new building block.

Neither project requires new deep mathematics; both are elementary but involve a fair amount
of measure-theoretic bookkeeping. The recommended order is: (1) neighborhood-is-interval-union,
(2) `main1` for Borel sets via fattening (removing the `key_lemma` dependency), (3) the
`A+B ≈ A'+B'` continuity fact and the symmetric Borel `main2`, (4) if desired, the general
off-diagonal `d(A)=d(B)` case.
