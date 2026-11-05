import GSQG.Definitions.Family
import GSQG.Definitions.Linear

/-!
# The conclusions of the three backbone theorems, as predicates

`fixed_point_approximation_statement`, `fixed_point_linear_inverse_statement` and
`fixed_point_nonlinear_estimates_statement` are the conclusions of thm:fixed_point_approximation,
thm:fixed_point_linear_inverse and thm:fixed_point_nonlinear_estimates (chapter 02). They live in
`GSQG/Definitions` so that the assembly lemmas `approx_assembly`, `linear_inverse_assembly` and
`nonlinear_assembly` can conclude exactly these predicates.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology

noncomputable section

namespace GSQG

/-- Blueprint: def:c02_approximation_statement (its conclusion, for the family of
def:approximate_solution_family with cutoff scale `R`, on `ε ∈ [0,ε₀]`, `μ ∈ B̄ = Bbar p δ`).
(0) `μ_* ≠ 0` and every `f̄_{ε,μ}` is `C^∞`;
(1) `f̄ + y → 0` at `-∞`, `f̄ → 0` at `+∞`;
(2) uniform symbol bounds (constants uniform in `ε, μ`);
(3) `ℰ_ε(f̄_{ε,μ}) ∈ Y_γ` and `‖ℰ_ε(f̄_{ε,μ}) - G_μ‖_{Y_γ} ≤ C_γ ε` (uniform in `ε, μ`);
(4) for fixed `ε`: `μ ↦ f̄_{ε,μ}` is continuous into `C²_loc`, and `μ ↦ ℰ_ε(f̄_{ε,μ})` into `Y_γ`
(continuity on `B̄` expressed with `𝓝[B̄] μ`; `C²_loc` convergence as uniform convergence of the
derivatives of order `≤ 2` on compact sets). This is item (4) of Theorem 3.1 of the paper. -/
def fixed_point_approximation_statement (P : parameters) (R δ ε₀ : ℝ) : Prop :=
  -- (0)
  mu_star P.p ≠ 0 ∧
  (∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
    ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family P.p R ε μ)) ∧
  -- (1)
  (∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
    Tendsto (fun y => approximate_solution_family P.p R ε μ y + y) atBot (𝓝 0) ∧
    Tendsto (approximate_solution_family P.p R ε μ) atTop (𝓝 0)) ∧
  -- (2)
  (∀ j : ℕ, ∃ C > 0, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
    (∀ y, 0 ≤ y →
      |approximate_solution_family P.p R ε μ y| ≤ C * jb y ^ (-P.p) ∧
      |iteratedDeriv (j + 1) (approximate_solution_family P.p R ε μ) y| ≤
        C * jb y ^ (-beta P.p + j / P.p)) ∧
    (∀ y, y ≤ 0 →
      |iteratedDeriv j (fun x => approximate_solution_family P.p R ε μ x + x) y| ≤
        C * jb y ^ (-P.p - j))) ∧
  -- (3)
  (∀ γ, P.admissible γ → ∃ C > 0, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
    residual P.p ε (approximate_solution_family P.p R ε μ) ∈ Y_gamma P.p γ ∧
    yNorm P.p γ (residual P.p ε (approximate_solution_family P.p R ε μ) - G_mu P.p μ) ≤ C * ε) ∧
  -- (4)
  (∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
    (∀ K : Set ℝ, IsCompact K → ∀ k ≤ 2,
      TendstoUniformlyOn (fun ν => iteratedDeriv k (approximate_solution_family P.p R ε ν))
        (iteratedDeriv k (approximate_solution_family P.p R ε μ)) (𝓝[Bbar P.p δ] μ) K) ∧
    (∀ γ, P.admissible γ →
      Tendsto (fun ν => yNorm P.p γ (residual P.p ε (approximate_solution_family P.p R ε ν) -
          residual P.p ε (approximate_solution_family P.p R ε μ))) (𝓝[Bbar P.p δ] μ) (𝓝 0)))

-- Encoding: "there exist ε₀, δ > 0 and the family of def:approximate_solution_family" (any
-- `δ ∈ (0, |μ_*|/2]`, any `R ≥ R₀`) is stated as: there are `R₀, δ₀ > 0` such that for all
-- `R ≥ R₀`, `δ ∈ (0, δ₀]` there is `ε₀ > 0` with all conclusions (the form in which it is combined
-- with the other backbone theorems).

/-- Blueprint: def:c02_linear_inverse_statement (its conclusion on `ε ∈ [0,ε₀]`, `μ ∈ Bbar p δ`).
(1) for admissible `γ`, `ℓ` is well defined on `Y_γ` (the limit exists) and `|ℓ(G)| ≤ C_ℓ ‖G‖_{Y_γ}`;
(2) `𝒯₀` (= `T_0`, a `γ`-independent formula) is linear on `Ỹ_γ`, maps `Ỹ_γ` into `X_γ` (and
`T_0 G` is the inverse Fourier transform of `m_G`), `‖𝒯₀ G‖_{X_γ} ≤ C_T ‖G‖_{Y_γ}` and
`ℒ₀(𝒯₀ G) = G` pointwise;
(3) `𝒰_ε, 𝒱_ε` are bijections of all functions `ℝ → ℝ` with inverses `U_eps_inv`, `V_eps_inv`,
preserving `X_γ` resp. `Y_γ` with operator norms (and those of the inverses) `≤ C_UV(γ)` uniformly in
`ε`, and `ℒ_ε r = 𝒱_ε(ℒ₀(𝒰_ε r))` pointwise for `r ∈ X_γ` (`𝒱_ε` acts on all
functions);
(4) `‖(𝒱_ε⁻¹ - I) G_μ‖_{Y_γ} ≤ C_G(γ) ε` uniformly in `ε` and `μ ∈ B̄`. -/
def fixed_point_linear_inverse_statement (P : parameters) (δ ε₀ : ℝ) : Prop :=
  -- (1)
  (∀ γ, P.admissible γ → ∃ Cℓ > 0, ∀ G ∈ Y_gamma P.p γ,
    Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
      (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 P.p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ)
      atTop (𝓝 (ell P.p G)) ∧
    ‖ell P.p G‖ ≤ Cℓ * yNorm P.p γ G) ∧
  -- (2)
  (∀ γ, P.admissible γ → ∃ CT > 0,
    (∀ G ∈ Y_gamma_tilde P.p γ,
      T_0 P.p G ∈ X_gamma P.p γ ∧
      HasDistFourier (fun x => (T_0 P.p G x : ℂ)) (T_0_symbol P.p G) ∧
      xNorm P.p γ (T_0 P.p G) ≤ CT * yNorm P.p γ G ∧
      ∀ y, L0 P.p (T_0 P.p G) y = G y) ∧
    (∀ G ∈ Y_gamma_tilde P.p γ, ∀ H ∈ Y_gamma_tilde P.p γ, ∀ a b : ℝ,
      T_0 P.p (a • G + b • H) = a • T_0 P.p G + b • T_0 P.p H)) ∧
  -- (3)
  (∀ ε ∈ Icc 0 ε₀,
    Function.LeftInverse (U_eps_inv P.p ε) (U_eps P.p ε) ∧
    Function.RightInverse (U_eps_inv P.p ε) (U_eps P.p ε) ∧
    Function.LeftInverse (V_eps_inv P.p ε) (V_eps P.p ε) ∧
    Function.RightInverse (V_eps_inv P.p ε) (V_eps P.p ε)) ∧
  (∀ γ, P.admissible γ → ∃ CUV > 0, ∀ ε ∈ Icc 0 ε₀,
    (∀ r ∈ X_gamma P.p γ,
      U_eps P.p ε r ∈ X_gamma P.p γ ∧ xNorm P.p γ (U_eps P.p ε r) ≤ CUV * xNorm P.p γ r ∧
      U_eps_inv P.p ε r ∈ X_gamma P.p γ ∧ xNorm P.p γ (U_eps_inv P.p ε r) ≤ CUV * xNorm P.p γ r) ∧
    (∀ G ∈ Y_gamma P.p γ,
      V_eps P.p ε G ∈ Y_gamma P.p γ ∧ yNorm P.p γ (V_eps P.p ε G) ≤ CUV * yNorm P.p γ G ∧
      V_eps_inv P.p ε G ∈ Y_gamma P.p γ ∧ yNorm P.p γ (V_eps_inv P.p ε G) ≤ CUV * yNorm P.p γ G) ∧
    (∀ r ∈ X_gamma P.p γ, ∀ y, L_eps P.p ε r y = V_eps P.p ε (L0 P.p (U_eps P.p ε r)) y)) ∧
  -- (4)
  (∀ γ, P.admissible γ → ∃ CG > 0, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
    yNorm P.p γ (V_eps_inv P.p ε (G_mu P.p μ) - G_mu P.p μ) ≤ CG * ε)

-- Encoding: "ε₀, δ as in thm:fixed_point_approximation": the threshold ε₀ of the linear
-- theory (ε₀ ≤ ε_c of lem:linear_conjugation) is existential here and independent of δ; item (4) is stated for every δ > 0 (constant C_G
-- depending on δ).  Combined with thm:fixed_point_approximation by taking the minimum of the ε₀'s.

/-- Blueprint: def:c02_nonlinear_estimates_statement (its conclusion, for the family with cutoff
scale `R` on `ε ∈ [0,ε₀]`, `μ ∈ Bbar p δ`).
(1)–(2) for admissible `γ` and `N > 0` there is `C_𝒩(γ,N)`, uniform in `ε, μ`, with
`𝒩_{ε,f̄}(r) ∈ Y_γ`, `‖𝒩(r)‖_{Y_γ} ≤ C ε ‖r‖_{X_γ}`, `‖𝒩(r₁)-𝒩(r₂)‖_{Y_γ} ≤ C ε ‖r₁-r₂‖_{X_γ}`
for `‖r‖, ‖r₁‖, ‖r₂‖ ≤ N`;
(3) for fixed `ε` and `r ∈ X_{γ₂}`, `μ ↦ 𝒩_{ε,f̄_{ε,μ}}(r)` is continuous `B̄ → Y_{γ₁}`. -/
def fixed_point_nonlinear_estimates_statement (P : parameters) (R δ ε₀ : ℝ) : Prop :=
  (∀ γ, P.admissible γ → ∀ N > 0, ∃ C > 0, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
    (∀ r ∈ X_gamma P.p γ, xNorm P.p γ r ≤ N →
      N_eps P.p ε (approximate_solution_family P.p R ε μ) r ∈ Y_gamma P.p γ ∧
      yNorm P.p γ (N_eps P.p ε (approximate_solution_family P.p R ε μ) r) ≤
        C * ε * xNorm P.p γ r) ∧
    (∀ r₁ ∈ X_gamma P.p γ, ∀ r₂ ∈ X_gamma P.p γ, xNorm P.p γ r₁ ≤ N → xNorm P.p γ r₂ ≤ N →
      yNorm P.p γ (N_eps P.p ε (approximate_solution_family P.p R ε μ) r₁ -
          N_eps P.p ε (approximate_solution_family P.p R ε μ) r₂) ≤
        C * ε * xNorm P.p γ (r₁ - r₂))) ∧
  (∀ ε ∈ Icc 0 ε₀, ∀ r ∈ X_gamma P.p P.γ₂, ∀ μ ∈ Bbar P.p δ,
    Tendsto (fun ν => yNorm P.p P.γ₁ (N_eps P.p ε (approximate_solution_family P.p R ε ν) r -
        N_eps P.p ε (approximate_solution_family P.p R ε μ) r)) (𝓝[Bbar P.p δ] μ) (𝓝 0))

-- Encoding: as for thm:fixed_point_approximation, "ε₀, B̄, f̄ as in
-- thm:fixed_point_approximation" is encoded as: for all `R ≥ R₀`, `δ ∈ (0,δ₀]` there is `ε₀ > 0`.
-- "𝒩(r) is defined" (convergence of the integrals) is not stated separately: the operators are
-- total in Lean, and membership in `Y_γ` is the substantive content.

end GSQG
