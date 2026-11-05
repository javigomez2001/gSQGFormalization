# Reading the Lean development

`import GSQG` loads everything. The folders follow the sections of the paper. For a given numbered
statement, [docs/PAPER_MAP.md](../docs/PAPER_MAP.md) gives the exact declaration and file.

With a few exceptions, a blueprint node and its main Lean declaration share a name, with `GSQG.` in
place of the node's `thm:`, `prop:` or `lem:` prefix: for example `prop:approx_E6` is
`GSQG.approx_E6`. (Exceptions include `lem:c01_paper_front_equation`, whose declaration is
`c01_front_equation_paper`; each node's `\lean{…}` field gives the exact names.) Supporting lemmas
carry their blueprint chapter's prefix (`c05_…`), and pure helpers add `aux`, possibly after a file
letter (`c05_aux_…`, `c13b_aux_…`).

## Where to start

* **Theorem 1.1**: [`Sec3_FixedPoint/MainTheorem.lean`](Sec3_FixedPoint/MainTheorem.lean), declaration
  `main`. The same file states Theorems 3.1–3.4 (`fixed_point_approximation`,
  `fixed_point_linear_inverse`, `fixed_point_nonlinear_estimates`, `fixed_point_correction`) and derives
  Theorem 1.1 from them, as in §3.
* **The equation**: [`Definitions/`](Definitions/) defines the front equation (`gsqg_front_equation`),
  `|D|^p` (`fracD`, with constant `calpha`), the Fourier convention, the spaces `X_γ` and `Y_γ`, and
  the self-similar ansatz. [`Sec1_Introduction/GeometricFrontEquation.lean`](Sec1_Introduction/GeometricFrontEquation.lean)
  proves that the formal operator is the paper's geometric integral (1.2).

## By section

| Folder | Paper | Contents |
|---|---|---|
| `Definitions/` | §§1–3, 5.2, 6 | operators, spaces, approximate family (Definition 5.3), backbone statements |
| `Sec1_Introduction/` | §§1–2 | self-similar reduction, profile properties, corner and curvature, equation (1.2) |
| `Sec3_FixedPoint/` | §3 | fixed-point argument (Banach contraction and Brouwer); Theorems 3.1–3.4 and 1.1 |
| `Sec4_Analysis/` | §4 | Proposition 4.1, Lemma 4.3, Hölder calculus; `Smoothness.lean` proves Theorem 3.5 |
| `Sec5_ApproximateSolution/` | §5 | `OscillatoryIntegrals` (the oscillatory integrals used in §5.1; blueprint notation `Osc[a]`); `FamilyAndE1toE4` (§§5.1–5.2, 5.4–5.7); `E5` (§5.8); `E6toE9` (§§5.9–5.12); `ResidualBounds` (§§5.3, 5.13–5.15) |
| `Sec6_LinearInverse/` | §6 | `ConjugationAndLowFrequency` (§§6.1–6.3); `HighFrequency` (§6.4) |
| `Sec7_NonlinearEstimates/` | §7 | Definition 7.1, Lemmas 7.2–7.4, Proposition 7.5 |
| `AppendixAB/` | App. A–B | `Statements` holds Propositions A.1–A.2 and Lemmas B.1–B.5. The other files are the supporting toolbox: Fresnel and van der Corput estimates, symbol calculus and repeated integration by parts, stationary phase, oscillatory multipliers |
| `SchauderEstimate/` | cited in §4 | proof of the interior fractional Schauder estimate (`c03_schauder_RS`, stated for smooth `w`; the paper's footnote handles mollification): dyadic blocks, kernel moments, Taylor cancellation, reconstruction, cutoff commutator |
| `PatchEquation/` | beyond §1 | derivation of the front equation from the 2D patch system (below) |
| `Auxiliary/` | — | special integrals (Dirichlet, `|D|^p` symbol, Laplace transforms) |

## The 2D derivation (`PatchEquation/`)

* **`Setup`** fixes the Euclidean plane, the rotation, the kernels `P` and `K = −J∇P`, the graph class and
  the contour velocity.
* **`CancellationOperator`** constructs the 2D operator through cancellation and a renormalized potential.
* **`FourierNormalization`** identifies its Fourier multiplier, so that the coefficient is that of
  `−∇^⊥(−Δ)^{−1+α/2}`.
* **`GraphFlux`** proves the graph geometry and the finite-domain flux identities.
* **`Velocity`** proves the contour velocity converges, is locally integrable and is spatially regular.
* **`BulkToContour`** derives the contour formula from the bulk operator.
* **`NormalTrace`** proves the finite normal trace. Its flat-graph example shows why the full velocity has
  no boundary trace.
* **`WeakFormulation`** states the weak patch system.
* **`Equivalence`** proves weak patch equation ⇔ front equation.
* **`MainTheorem`** applies Theorem 1.1 to canonical patches, with the explicit time change `t ↦ t/κ`.

The weak equation is defined from the bulk operator. The contour law is never assumed: it is a theorem.
