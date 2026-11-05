# Blueprint conventions (gSQG self-similar corner paper)

Source paper: `../paper/gsqg_Nov26.tex`. Bibliography: `../paper/ref.bib`.
Format: **leanblueprint** (LaTeX, compiled by plasTeX for the web and pdflatex for print).
Macros available: everything in `src/macros/common.tex` (the paper's `\R, \C, \mc, \ov, \sq, \ang, \p, ...`).
Chapter files do not define new macros; they write the expanded form instead.

## Chapter files

Each chapter is `src/chapters/NN_name.tex`, included by `src/content.tex` (which provides the
`\chapter{}` heading; chapter files use `\section`/`\subsection` only).

| # | file | paper | contents |
|---|------|-------|----------|
| 01 | 01_setup.tex | §§1–2 | front equation, Fourier conventions, `\|D\|^s`, self-similar ansatz, $A_\epsilon$, $\sq{\mc J}_\epsilon$, profile equation, residual $\mc E_\epsilon$, `thm:main` and its proof |
| 02 | 02_fixed_point.tex | §3 | parameters $p,\beta,\gamma_1,\gamma_2$, $X_\gamma$, $Y_\gamma$, $\ell$, $G_\pm$, $\Pi$, $\mc L_\epsilon$, $\mc N_{\epsilon,\ov f}$; statements of `thm:fixed_point_approximation`, `thm:fixed_point_linear_inverse`, `thm:fixed_point_nonlinear_estimates`; `thm:fixed_point_correction` with fully decomposed proof (Banach + Brouwer) |
| 03 | 03_analysis_appendix.tex | §4, App. A–B | `prop:analysis_semilinear_kernel`, `lem:analysis_coefficient`, `thm:fixed_point_smoothness` (statement and proof), all appendix lemmas (`prop:appendix_*`, `lem:van_der_Corput`, `lem:appendix_*`) |
| 04 | 04_approx_family.tex | §§5.1–5.2, 5.4–5.7 | `lem:approx_linear_seed`, `def:approximate_solution_family`, $\mu_*$, `lem:approx_phase_differences`, `prop:approx_profile_bounds`, the decomposition of the residual into $\mc E_1,\dots,\mc E_9$, `prop:approx_residual_positive` (its proof `\uses` the E1–E9 results), `prop:approx_E1`–`prop:approx_E4` |
| 05 | 05_E5.tex | §5.8 | `prop:approx_E5_linear`, `prop:approx_E5_cubic` |
| 06 | 06_E6_E9.tex | §§5.9–5.12 | `prop:approx_E6`, `lem:approx_E7`, `lem:approx_E8`, `lem:approx_E9` |
| 07 | 07_residual_rest.tex | §§5.3, 5.13–5.15 | `prop:approx_residual_negative`, `prop:approx_residual_compact`, `lem:approx_assembly` (the subsection "The Proof of Theorem 3.1") |
| 08 | 08_linear_low.tex | §§6.1–6.3 | `lem:linear_conjugation` and the operators $\mc R_\epsilon,\mc U_\epsilon,\mc V_\epsilon$, the free inverse $\mc T_0$ and the projected space, `prop:linear_ell_continuity`, `prop:linear_low_frequency` |
| 09 | 09_linear_high.tex | §6.4 | the high-frequency kernel definitions, `prop:linear_stationary`, `lem:linear_nonstationary_*`, `prop:linear_high_frequency`, `lem:linear_inverse_assembly` (conjugation, low and high frequency combined into the proof of `thm:fixed_point_linear_inverse`) |
| 10 | 10_nonlinear.tex | §7 | `def:nonlinear_admissible_profile`, `lem:N1`, `lem:N2`, `lem:N3`, `prop:nonlinear_continuity`, `lem:nonlinear_assembly` (proof of `thm:fixed_point_nonlinear_estimates`) |
| 12 | 12_schauder.tex | cited in §4 | the proof of the interior fractional Schauder estimate `lem:c03_schauder_RS` (stated in chapter 03) |
| 13 | 13_patch_equation.tex | beyond §1 | derivation of the front equation from the 2D patch system; `thm:c13_patch_main` |

Chapter 02's proofs of the three big theorems are one-liners `\uses{lem:approx_assembly}`,
`\uses{lem:linear_inverse_assembly}`, `\uses{lem:nonlinear_assembly}` respectively.

## Labels

* **Results that exist in the paper keep the paper's label exactly.** Example: `prop:approx_E6`.
* **Shared definitions** use these labels both where they are defined and where they are referenced:
  - ch01: `def:fourier_convention`, `def:frac_multiplier` ($|D|^s$, $|D|^s\p_y$ incl. action on non-decaying functions), `def:gsqg_front_equation`, `def:self_similar_ansatz`, `def:A_eps`, `def:J_eps` ($\sq{\mc J}_\epsilon$), `def:profile_equation`, `def:residual` ($\mc E_\epsilon$), `lem:self_similar_reduction` (profile solves profile eq ⇒ $F$ solves front eq), `thm:main`.
  - ch02: `def:parameters`, `def:X_gamma`, `def:Y_gamma`, `def:ell`, `def:G_pm`, `def:Pi_projection`, `def:L_eps`, `def:N_eps`, `def:G_mu`, `thm:fixed_point_approximation`, `thm:fixed_point_linear_inverse`, `thm:fixed_point_nonlinear_estimates`, `thm:fixed_point_correction`.
  - ch04: `def:approximate_solution_family`, `def:mu_star`, `def:residual_decomposition` ($\mc E_1,\dots,\mc E_9$).
  - ch08: `def:R_eps`, `def:U_eps`, `def:V_eps`, `def:T_0`.
* **Auxiliary nodes** (sub-lemmas split out of a long proof, supporting definitions) carry their
  chapter number as a prefix: `lem:c05_phase_bound`, `def:c09_kernel_K1`, etc. This guarantees
  global uniqueness.
* New equation labels inside statements are chapter-prefixed (`eq:c05_...`) unless they are the
  paper's equation labels.

## Node format

```latex
\begin{lemma}[Short name]
  \label{lem:c05_phase_bound}
  \lean{GSQG.c05_phase_bound}
  \uses{def:X_gamma, lem:approx_phase_differences}
  Precise statement.
\end{lemma}
\begin{proof}
  \uses{lem:van_der_Corput, lem:c05_other}
  Proof sketch detailed enough that a formalizer can follow it step by step.
\end{proof}
```

* `\uses` in the statement = what is needed to *state* it (definitions). `\uses` in the proof = what is needed to *prove* it.
* The Lean name is `GSQG.` + the label without the `lem:/prop:/thm:/def:` prefix where practical. Existing declaration names are preserved when a node is split. Every Lean name has exactly one owning node; other nodes reference it through `\uses`.
* Pure definitions and statement predicates are kept separate from theorems proving their properties. In particular, an assembly does not depend on a predicate grouped with the theorem that the assembly proves.
* Maintained sources contain no `\leanok`: the build inserts verified status into staged copies. “Locally proved” and “fully proved” differ; see `README.md` and `../docs/CONVENTIONS.md`.
* For Mathlib nodes, the exact `\lean{}` declaration must exist. If a needed result is unavailable in Mathlib, it is an ordinary node with a precise statement and proof or reference, marked by a `% MATHLIB-GAP` comment above it.

## Quality requirements

1. **Every statement is precise enough to formalize**: all quantifiers, all hypotheses (ranges of $p,\gamma,\epsilon,\mu$, regularity), and every $\lesssim$ replaced by "there exists $C$ depending only on ... such that ...". The function spaces of all inputs are stated.
2. **Granularity**: a node is a result that can be proved in Lean in a single file of moderate size. Long paper proofs (multi-page estimates) are split into a chain of lemmas; a paper proposition with a 3-page proof typically becomes 4–10 nodes.
3. Proofs keep the paper's argument but make implicit steps explicit (integration by parts boundary terms, convergence/justification of interchanges, case splits $y\ge0$ / $y\le0$, dyadic sums).
4. After a change, run the full site build and the declaration-ownership and cycle checks described in `README.md`.
