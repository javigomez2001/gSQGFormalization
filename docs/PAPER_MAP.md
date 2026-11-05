# Paper ↔ Lean correspondence

All 57 numbered environments of [`paper/gsqg_Nov26.tex`](../paper/gsqg_Nov26.tex): 44 theorems,
lemmas and propositions, six definitions, and seven remarks. Each row gives the Lean counterpart or
an explanatory note. Names omit the `GSQG.` prefix. Listed results are proved and definitions checked
using only `propext`, `Classical.choice` and `Quot.sound`; explanatory remarks are not counted as
additional formal theorems.

Notes on the encoding:

* The smallness thresholds of the §5 standing assumptions (`ε₀ ≤ ε₀*(δ)`, `δ ≤ |μ*|/2`) are explicit
  in Lean. They enter Propositions 5.11–5.12 through `c05_standing` and Lemmas 5.14–5.16 through the
  hypothesis `ε₀ ≤ c06_eps0_star P δ`; this is the paper's "for ε₀ sufficiently small".
* Several results are also proved in a more general form. The bounds behind Proposition 5.13 hold
  for `y > 2R` (`c06_aux_E6_bounds_gt2R`), which contains the range `y ≥ 8R` of `approx_E6`. Lemma
  B.3 is proved for every symbol order `m < p` (`c03f_appendix_homogeneous_stationary_phase`), which
  contains the range `m ≤ 0` of `appendix_homogeneous_stationary_phase`. Besides the continuity into
  `Y_γ` of Theorem 3.1(4), continuity of the residual into `C¹_loc` is proved
  (`c07_residual_continuity_C1loc`).

## §1 Introduction

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.1 — Self-similar corner formation | `main` | [Sec3_FixedPoint/MainTheorem.lean](../GSQG/Sec3_FixedPoint/MainTheorem.lean) |
| Remark 1.2 — Desingularization by space-time reflection | `c01_desingularization` | [Sec3_FixedPoint/MainTheorem.lean](../GSQG/Sec3_FixedPoint/MainTheorem.lean) |
| Remark 1.3 — Origin of the parameter restriction | Explanatory discussion; `admissibleGamma` records the chosen weight range `β + 1/p < γ < 2p + 1`. The remark writes `γ ≤ 2α − 1`; the theorems of §3 and the Lean statements use the strict bound (`2α − 1 = 2p + 1`). No optimality claim is formalized. | [Definitions/Spaces.lean](../GSQG/Definitions/Spaces.lean) |
| Remark 1.4 — A general strategy for corner-type self-similar solutions | Informal discussion and outlook; no formal counterpart | [Manuscript](../paper/gsqg_Nov26.tex) |

## §3 Fixed point argument

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 3.1 — Existence of approximate solutions | `fixed_point_approximation`. The clause "G_μ is Schwartz" is `c02_G_pm_properties` (for G±; G_μ is a real combination of them by definition), and G_{μ*} = 0 holds by definition | [Sec3_FixedPoint/MainTheorem.lean](../GSQG/Sec3_FixedPoint/MainTheorem.lean), [Sec3_FixedPoint/FixedPointArgument.lean](../GSQG/Sec3_FixedPoint/FixedPointArgument.lean) |
| Theorem 3.2 — Linear inverse | `fixed_point_linear_inverse` | [Sec3_FixedPoint/MainTheorem.lean](../GSQG/Sec3_FixedPoint/MainTheorem.lean) |
| Theorem 3.3 — Nonlinear estimates | `fixed_point_nonlinear_estimates` | [Sec3_FixedPoint/MainTheorem.lean](../GSQG/Sec3_FixedPoint/MainTheorem.lean) |
| Theorem 3.4 — Existence of the correction | `fixed_point_correction` | [Sec3_FixedPoint/MainTheorem.lean](../GSQG/Sec3_FixedPoint/MainTheorem.lean) |
| Theorem 3.5 — Smoothness of profiles | `fixed_point_smoothness` | [Sec4_Analysis/Smoothness.lean](../GSQG/Sec4_Analysis/Smoothness.lean) |

## §4 Analysis of the equation

| Paper | Lean declaration | File |
|---|---|---|
| Proposition 4.1 — Semilinear kernel form | `analysis_semilinear_kernel` | [Sec4_Analysis/Equation.lean](../GSQG/Sec4_Analysis/Equation.lean) |
| Remark 4.2 — Vanishing on the diagonal | `c03_Gamma_quadratic_factor` (Γ_ε = (u−v)² Γ̃_ε), `c03_Gamma_eps_smooth` (Γ̃_ε smooth), `analysis_vanishing_diagonal` (the bounds on Γ̃_ε) | [Sec4_Analysis/Equation.lean](../GSQG/Sec4_Analysis/Equation.lean) |
| Lemma 4.3 — The nonperturbative coefficient | `analysis_coefficient` | [Sec4_Analysis/Equation.lean](../GSQG/Sec4_Analysis/Equation.lean) |
| Remark 4.4 — Why the coefficient belongs in the linear inverse | Informal motivation; no separate formal theorem | [Manuscript](../paper/gsqg_Nov26.tex) |

## §5 Construction of the approximate solution

| Paper | Lean declaration | File |
|---|---|---|
| Lemma 5.1 — The linear solution | `approx_linear_seed` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Lemma 5.2 — Cubic response to the sine profile | `c04_cubic_sine_response` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Definition 5.3 — The approximate solution family | `approximate_solution_family` | [Definitions/Family.lean](../GSQG/Definitions/Family.lean) |
| Lemma 5.4 — Approximate phase differences | `approx_phase_differences` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Proposition 5.5 — Profile bounds | `approx_profile_bounds` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Proposition 5.6 — Residual bound for y ≥ 8R | `approx_residual_positive` | [Sec5_ApproximateSolution/ResidualBounds.lean](../GSQG/Sec5_ApproximateSolution/ResidualBounds.lean) |
| Proposition 5.7 — Control of ℰ₁ | `approx_E1` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Proposition 5.8 — Control of ℰ₂ | `approx_E2` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Proposition 5.9 — Control of ℰ₃ | `approx_E3` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Proposition 5.10 — Control of ℰ₄ | `approx_E4` | [Sec5_ApproximateSolution/FamilyAndE1toE4.lean](../GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean) |
| Proposition 5.11 — Linear remainder of ℰ₅ | `approx_E5_linear` | [Sec5_ApproximateSolution/E5.lean](../GSQG/Sec5_ApproximateSolution/E5.lean) |
| Proposition 5.12 — Cubic remainder of ℰ₅ | `approx_E5_cubic` | [Sec5_ApproximateSolution/E5.lean](../GSQG/Sec5_ApproximateSolution/E5.lean) |
| Proposition 5.13 — Control of ℰ₆ | `approx_E6` | [Sec5_ApproximateSolution/E6toE9.lean](../GSQG/Sec5_ApproximateSolution/E6toE9.lean) |
| Lemma 5.14 — Control of ℰ₇ | `approx_E7` | [Sec5_ApproximateSolution/E6toE9.lean](../GSQG/Sec5_ApproximateSolution/E6toE9.lean) |
| Lemma 5.15 — Control of ℰ₈ | `approx_E8` | [Sec5_ApproximateSolution/E6toE9.lean](../GSQG/Sec5_ApproximateSolution/E6toE9.lean) |
| Lemma 5.16 — Control of ℰ₉ | `approx_E9` | [Sec5_ApproximateSolution/E6toE9.lean](../GSQG/Sec5_ApproximateSolution/E6toE9.lean) |
| Proposition 5.17 — Residual bound for y ≤ −8R | `approx_residual_negative` | [Sec5_ApproximateSolution/ResidualBounds.lean](../GSQG/Sec5_ApproximateSolution/ResidualBounds.lean) |
| Proposition 5.18 — Residual bound for \|y\| ≤ 8R | `approx_residual_compact` | [Sec5_ApproximateSolution/ResidualBounds.lean](../GSQG/Sec5_ApproximateSolution/ResidualBounds.lean) |

## §6 Linear inverse

| Paper | Lean declaration | File |
|---|---|---|
| Lemma 6.1 — Conjugation of the linear operator | `linear_conjugation` | [Sec6_LinearInverse/ConjugationAndLowFrequency.lean](../GSQG/Sec6_LinearInverse/ConjugationAndLowFrequency.lean) |
| Definition 6.2 — The projected space and free inverse | `Y_gamma_tilde`, `T_0_symbol`, `T_0` | [Definitions/Spaces.lean](../GSQG/Definitions/Spaces.lean), [Definitions/Linear.lean](../GSQG/Definitions/Linear.lean) |
| Proposition 6.3 — Continuity of ℓ | `linear_ell_continuity` | [Sec6_LinearInverse/ConjugationAndLowFrequency.lean](../GSQG/Sec6_LinearInverse/ConjugationAndLowFrequency.lean) |
| Proposition 6.4 — Low-frequency estimate | `linear_low_frequency` | [Sec6_LinearInverse/ConjugationAndLowFrequency.lean](../GSQG/Sec6_LinearInverse/ConjugationAndLowFrequency.lean) |
| Remark 6.5 — No projection condition for the low-frequency estimate | Included in the hypotheses and range of `linear_low_frequency`; no separate theorem | [Sec6_LinearInverse/ConjugationAndLowFrequency.lean](../GSQG/Sec6_LinearInverse/ConjugationAndLowFrequency.lean) |
| Definition 6.6 — Positive high-frequency part | `c09_T_plus_hat`, `c09_T_plus` | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Remark 6.7 — Projected tail representation | `c08_T0_tail` (the projected-tail identity), used in `c09_tail_formula` | [Sec6_LinearInverse/ConjugationAndLowFrequency.lean](../GSQG/Sec6_LinearInverse/ConjugationAndLowFrequency.lean), [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Definition 6.8 — Positive-frequency kernel | `c09_positive_kernel_amp`, `c09_positive_kernel` (cutoff-regularized form) | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Definition 6.9 — Stationary/nonstationary kernel decomposition | `c09_stationary_split`, `c09_stationary_split_chi_ns` and the associated amplitude, kernel and operator definitions | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Proposition 6.10 — Stationary estimate | `linear_stationary` | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Lemma 6.11 — Nonstationary symbol expansion | `linear_nonstationary_symbol_expansion` | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Lemma 6.12 — Symbol bounds | `linear_nonstationary_leading_kernels` | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Lemma 6.13 — Remainder kernel | `linear_nonstationary_remainder` | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |
| Proposition 6.14 — High-frequency estimate | `linear_high_frequency` | [Sec6_LinearInverse/HighFrequency.lean](../GSQG/Sec6_LinearInverse/HighFrequency.lean) |

The kernel definitions in 6.8–6.9 carry a finite cutoff parameter `R` in Lean. Proposition 6.10 and
Lemmas 6.11–6.13 are stated for these `R`-truncated kernels, with bounds uniform in `R ≥ 2` (in the
`k = 0` case of Lemma 6.12, uniform in `R ≥ max{2, ⟨y⟩^{1/p}}`), while the paper writes them for the
untruncated kernels. The high-frequency construction proves the convergence and reconstruction
statements that remove the cutoff, and Proposition 6.14 is stated without it.
The definitions do not assert that the untruncated double integrals converge absolutely.

## §7 Nonlinear estimates

| Paper | Lean declaration | File |
|---|---|---|
| Definition 7.1 — Admissible profile | `nonlinear_admissible_profile` | [Sec7_NonlinearEstimates/NonlinearEstimates.lean](../GSQG/Sec7_NonlinearEstimates/NonlinearEstimates.lean) |
| Lemma 7.2 — Lipschitz bound for 𝒩₁ | `N1` | [Sec7_NonlinearEstimates/NonlinearEstimates.lean](../GSQG/Sec7_NonlinearEstimates/NonlinearEstimates.lean) |
| Lemma 7.3 — Lipschitz bound for 𝒩₂ | `N2` | [Sec7_NonlinearEstimates/NonlinearEstimates.lean](../GSQG/Sec7_NonlinearEstimates/NonlinearEstimates.lean) |
| Lemma 7.4 — Lipschitz bound for 𝒩₃ | `N3` | [Sec7_NonlinearEstimates/NonlinearEstimates.lean](../GSQG/Sec7_NonlinearEstimates/NonlinearEstimates.lean) |
| Proposition 7.5 — Continuity in the profile | `nonlinear_continuity` | [Sec7_NonlinearEstimates/NonlinearEstimates.lean](../GSQG/Sec7_NonlinearEstimates/NonlinearEstimates.lean) |

## Appendix A — elementary estimates

| Paper | Lean declaration | File |
|---|---|---|
| Proposition A.1 — Non-smooth Fourier inverse | `appendix_nonsmooth_fourier_inverse` | [AppendixAB/Statements.lean](../GSQG/AppendixAB/Statements.lean) |
| Proposition A.2 — Convergence in weighted spaces | `appendix_convergence` | [AppendixAB/Statements.lean](../GSQG/AppendixAB/Statements.lean) |

## Appendix B — stationary and nonstationary phase

| Paper | Lean declaration | File |
|---|---|---|
| Lemma B.1 — Van der Corput, paper form | `van_der_Corput` | [AppendixAB/Statements.lean](../GSQG/AppendixAB/Statements.lean) |
| Lemma B.2 — Uniform bound for the tail integrals | `appendix_stationary` | [AppendixAB/Statements.lean](../GSQG/AppendixAB/Statements.lean) |
| Lemma B.3 — Homogeneous stationary phase | `appendix_homogeneous_stationary_phase` | [AppendixAB/Statements.lean](../GSQG/AppendixAB/Statements.lean) |
| Lemma B.4 — Stationary phase against a tail integral | `appendix_triangle` | [AppendixAB/Statements.lean](../GSQG/AppendixAB/Statements.lean) |
| Lemma B.5 — Oscillatory multiplier expansion | `appendix_oscillatory_multiplier` | [AppendixAB/Statements.lean](../GSQG/AppendixAB/Statements.lean) |

## Beyond the paper

| Result | Lean declaration | File |
|---|---|---|
| Equation (1.2) in its literal geometric form, with absolute convergence | `c01_front_equation_paper` | [Sec1_Introduction/GeometricFrontEquation.lean](../GSQG/Sec1_Introduction/GeometricFrontEquation.lean) |
| Interior fractional Schauder estimate, cited in §4 as Ros-Oton–Serra, Cor. 2.4; formalized as Prop. 2.2 of the arXiv version with n = 1, for smooth `w` and β, β + p ∉ ℕ | `c03_schauder_RS` | [Sec4_Analysis/Smoothness.lean](../GSQG/Sec4_Analysis/Smoothness.lean); proof in [SchauderEstimate/](../GSQG/SchauderEstimate/) |
| Weak 2D patch equation ⇔ pointwise front equation | `c13_patch_front_equivalence` | [PatchEquation/Equivalence.lean](../GSQG/PatchEquation/Equivalence.lean) |
| Theorem 1.1 for canonical 2D gSQG patches | `c13_patch_main` | [PatchEquation/MainTheorem.lean](../GSQG/PatchEquation/MainTheorem.lean) |
