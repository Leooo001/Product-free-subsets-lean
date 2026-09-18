# Lean formalization of *Product-free subsets of (0,1)*

This repository contains a Lean 4 / Mathlib formalization accompanying the paper
**“Product-free subsets of $(0,1)$”** by **Leonardo Franchi, W. T. Gowers, and Fredy Yip**.

The formalization was developed with the assistance of **Aristotle (Harmonic)**.

## Build

The project is pinned to:

- Lean: `v4.28.0`
- Mathlib: `v4.28.0`

With Lean/Elan installed, run from the repository root:

```bash
lake exe cache get
lake build
```

The GitHub Actions workflow in `.github/workflows/lean.yml` also runs the Lean build automatically
on pushes and pull requests.

## Main files and results

| Paper item | Lean declaration | File |
|---|---|---|
| Product-free / sum-free definitions | `ProductFree.IsProductFree`, `ProductFree.IsSumFree` | `RequestProject/Defs.lean` |
| Discrepancy | `ProductFree.disc` | `RequestProject/Defs.lean` |
| Key lemma | `ProductFree.key_lemma` | `RequestProject/KeyLemma.lean` |
| Key lemma for finite interval unions | `ProductFree.key_lemma_intervalUnion` | `RequestProject/KeyLemma.lean` |
| Theorem 1, compact version | `ProductFree.main1_compact` | `RequestProject/Main1.lean` |
| Theorem 1, open version | `ProductFree.main1` | `RequestProject/Main1.lean` |
| Theorem 1 via outer fattening | `ProductFree.main1_open'` | `RequestProject/Fattening.lean` |
| Theorem 2, finite interval-union version | `ProductFree.main2_iu` | `RequestProject/OffdiagonalInduction.lean` |
| Theorem 2, measurable version | `ProductFree.main2_measurable` | `RequestProject/MainTwoBorel.lean` |

The long Section 4 rigidity argument is split across the `RequestProject/Section4*.lean` files.

## Formalization status

The source contains no active `sorry`/`admit` placeholders; historical `sorry` examples remain only
inside comments. Aristotle's final run reports that the full project builds and uses only the standard
axioms `propext`, `Classical.choice`, and `Quot.sound`.

There are two statement-level points worth recording explicitly:

1. The paper states Theorem 1 with the strict bound `|A| < 1/3`. The Lean theorem
   `ProductFree.main1` for open sets currently states the non-strict bound `≤ 1/3`; the compact
   theorem `ProductFree.main1_compact` is strict.
2. `ProductFree.main2_measurable` uses explicit finiteness hypotheses on the relevant sumset or
   difference set because its real-valued formulation uses `ENNReal.toReal`. See
   `FORMALIZATION_STATUS.md` for details.

Accordingly, this repository should be described as a machine-checked formalization accompanying the
paper, with the exact statement correspondence documented in `FORMALIZATION_STATUS.md`.

## Repository layout

```text
.
├── RequestProject/              # Lean source files
├── paper/
│   └── product_set_arxiv.tex    # paper source used for the formalization
├── docs/
│   ├── ARISTOTLE_SUMMARY.md     # Aristotle run history / final summary
│   └── ...                      # additional generation notes
├── .github/workflows/lean.yml   # automated Lean build on GitHub
├── CITATION.cff                 # citation metadata
├── FORMALIZATION_STATUS.md      # paper ↔ Lean correspondence and caveats
├── lakefile.toml
├── lake-manifest.json
└── lean-toolchain
```

## Attribution

The mathematical results and paper are by Leonardo Franchi, W. T. Gowers, and Fredy Yip.
The Lean formalization was produced with assistance from Aristotle by Harmonic. The original
Aristotle-generated README and run summary are retained in `docs/` for provenance.

## License

No license has been selected in this repository template. Before making the repository public, the
copyright holders should choose an appropriate license for the Lean source (for example, a standard
open-source license) and, separately if needed, specify the terms for the paper source.
