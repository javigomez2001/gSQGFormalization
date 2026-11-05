# gSQGFormalization

A complete Lean 4 formalization of

> **Javier Gómez-Serrano and Marcus Pasquariello**,
> *Self-Similar Solutions for the gSQG patch equations* (manuscript: [`paper/gsqg_Nov26.tex`](paper/gsqg_Nov26.tex)).

The formalization proves the paper's main theorem — the existence of self-similar solutions of the
generalized SQG front equation that form a corner in finite time — together with every numbered
result it depends on. It also formalizes two results the paper uses without proving them in this
form: the interior fractional Schauder estimate and the derivation of the front equation from the
two-dimensional patch system.

Every proof is checked by Lean's kernel using only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). There is no `sorry` and no custom axiom.

## Main results

| Paper | Lean | File |
|---|---|---|
| **Theorem 1.1** — self-similar solutions forming a corner, for 3/4 < p < 1 (7/4 < α < 2) | `GSQG.main` | [Sec3_FixedPoint/MainTheorem.lean](GSQG/Sec3_FixedPoint/MainTheorem.lean) |
| Equation (1.2), in the paper's geometric form | `GSQG.c01_front_equation_paper` | [Sec1_Introduction/GeometricFrontEquation.lean](GSQG/Sec1_Introduction/GeometricFrontEquation.lean) |
| Interior fractional Schauder estimate (cited in §4 as Ros-Oton–Serra, Cor. 2.4; formalized as Prop. 2.2 of the arXiv version with n = 1, for smooth w and β, β+p ∉ ℕ) | `GSQG.c03_schauder_RS` | [Sec4_Analysis/Smoothness.lean](GSQG/Sec4_Analysis/Smoothness.lean) |
| Weak 2D patch equation ⇔ front equation | `GSQG.c13_patch_front_equivalence` | [PatchEquation/Equivalence.lean](GSQG/PatchEquation/Equivalence.lean) |
| Theorem 1.1 for canonical 2D gSQG patches | `GSQG.c13_patch_main` | [PatchEquation/MainTheorem.lean](GSQG/PatchEquation/MainTheorem.lean) |

The main Lean theorem makes the uniform constants and the joint C^∞ regularity of the profiles
explicit.

**[docs/PAPER_MAP.md](docs/PAPER_MAP.md)** accounts for all 57 numbered environments of the paper:
44 theorems, lemmas and propositions, six definitions, and seven remarks. It identifies the Lean
counterparts and distinguishes explanatory remarks from separate formal results.

## How the formalization follows the paper

The Lean modules are organized by the sections of the paper:

```
GSQG/
├── Definitions/               the equation, |D|^p, Fourier conventions, X_γ / Y_γ, the approximate family
├── Sec1_Introduction/         §1–2   self-similar reduction; the geometric front equation (1.2)
├── Sec3_FixedPoint/           §3     Theorems 3.1–3.4 and the proof of Theorem 1.1
├── Sec4_Analysis/             §4     Proposition 4.1, Lemma 4.3, Theorem 3.5 (smoothness)
├── Sec5_ApproximateSolution/  §5     linear solution and family, ℰ₁–ℰ₉, residual bounds (Lemma 5.1–Prop. 5.18)
├── Sec6_LinearInverse/        §6     conjugation, ℓ, low and high frequency (Lemma 6.1–Prop. 6.14)
├── Sec7_NonlinearEstimates/   §7     Definition 7.1–Proposition 7.5
├── AppendixAB/                App. A–B   Propositions A.1–A.2, Lemmas B.1–B.5
├── SchauderEstimate/          beyond the paper: proof of the fractional Schauder estimate
├── PatchEquation/             beyond the paper: from the 2D patch system to the front equation
└── Auxiliary/                 special integrals used throughout
```

Lean declaration names follow the blueprint (e.g. `approx_E6`, `linear_low_frequency`). Helper lemmas
carry a prefix and `aux` (e.g. `c05_aux_…`). The theorem behind each paper statement is listed in
[PAPER_MAP.md](docs/PAPER_MAP.md); [GSQG/README.md](GSQG/README.md) is a guide to the source tree.

## Verification

* `lake build GSQG` checks the whole formalization.
* `#print axioms GSQG.main` reports exactly `propext`, `Classical.choice` and `Quot.sound`.
* [`blueprint/tools/AllAxioms.lean`](blueprint/tools/AllAxioms.lean) checks the axioms of every
  declaration in the project, including private helpers, and rejects custom axioms and opaque
  declarations.
* No proof uses `sorry`.
* The build and the all-declaration axiom check run in [CI](.github/workflows/check.yml) on every
  push to `main` and on every pull request.

## Blueprint

The [blueprint](blueprint/) gives the informal proof structure, chapter by chapter, with each node
linked to its Lean declaration:

* the [PDF](blueprint/site/blueprint.pdf);
* the [HTML version](blueprint/site/blueprint/index.html);
* a [dashboard](blueprint/site/index.html) with the dependency graph and the proof status of all
  553 nodes.

Each chapter title gives the paper section it covers.

## Building

Lean `v4.36.0-rc2` and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get        # download the prebuilt Mathlib
lake build GSQG           # check the whole formalization
lake env lean --run blueprint/tools/AllAxioms.lean GSQG /tmp/axioms.json   # axioms of every declaration
```

To check a single statement, open a file importing `GSQG` and run `#print axioms GSQG.main`. Rebuilding
the blueprint and dashboard is described in [blueprint/README.md](blueprint/README.md).

## Repository layout

| Path | Contents |
|---|---|
| `GSQG/`, `GSQG.lean` | the Lean formalization |
| `paper/` | the manuscript and bibliography |
| `docs/` | [paper map](docs/PAPER_MAP.md), [conventions](docs/CONVENTIONS.md), [contributing](docs/CONTRIBUTING.md) |
| `blueprint/` | blueprint sources, generated website and PDF, reporting tools |

## License and citation

The Lean code, tools and documentation are under the Apache License 2.0. The manuscript and
bibliography in `paper/` are excluded; see [LICENSING.md](LICENSING.md). To cite this work, please
cite the paper and the repository revision used ([CITATION.cff](CITATION.cff)).
