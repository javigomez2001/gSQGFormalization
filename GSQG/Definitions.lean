import GSQG.Definitions.Basic
import GSQG.Definitions.Operators
import GSQG.Definitions.Spaces
import GSQG.Definitions.Linear
import GSQG.Definitions.Family
import GSQG.Definitions.Statements

/-!
# GSQG.Definitions — API guide for the modules

Every module imports `GSQG.Definitions` (directly or through another module) and works in
`namespace GSQG`.
Recommended header:
```
import GSQG.Definitions
open MeasureTheory Set Filter Real
open scoped ENNReal
noncomputable section
namespace GSQG
```

## Design choices

* **Parameters are explicit reals**, in the fixed order `p R ε μ Y y`
  (`p` = α-1, `R` the cutoff scale of the family, `ε ≥ 0`, `μ : ℂ`, `Y` the localisation scale,
  `y` the point).  `α` is always written `p + 1`, `β` is `beta p = (p+1)/(2p)`.
  Ranges (`3/4 < p < 1`, `0 ≤ ε ≤ ε₀`, `μ ∈ Bbar p δ`, `R ≥ R₀`, `Y ≥ 8R`, admissible `γ`) are
  **hypotheses of statements**, never baked into definitions.
* The fixed parameters of def:parameters are the structure `GSQG.parameters`
  (fields `p γ₁ γ₂` and the hypotheses `hp_lo : 3/4 < p`, `hp_hi : p < 1`,
  `hγ₁ : beta p + 1/p < γ₁`, `hγ₁₂ : γ₁ < γ₂`, `hγ₂ : γ₂ < 2*p+1`; derived `P.α`, `P.β`,
  `P.admissible γ`).  Use `(P : parameters)` and write `P.p`, `P.γ₁` in statements that need
  the fixed parameters; use a bare `(p : ℝ)` with hypotheses such as `(hp : 0 < p) (hp1 : p < 1)`
  for results valid for general `p` (chapters 01, 03).  `admissibleGamma p γ` means
  `β + 1/p < γ < 2p+1`.
* **Operators act on all functions `ℝ → ℝ`** by their pointwise formulas (Bochner integrals,
  `deriv`), so e.g. `residual p ε f y`, `L_eps p ε r y`, `N_eps p ε fbar r y` always typecheck;
  hypotheses like `f ∈ c01_admissible_class`, `r ∈ X_gamma p γ` and integrability conclusions
  belong to statements.  Operators return functions: `L0 p f : ℝ → ℝ`, so `L0 p f ∈ Y_gamma p γ`
  is a valid statement.
* **Spaces are sets** `X_gamma p γ, Y_gamma p γ : Set (ℝ → ℝ)`; norms are `ℝ≥0∞`-valued essential
  suprema `X_gamma_norm p γ r`, `Y_gamma_norm p γ G` (generic in the codomain: they work for
  `ℝ → ℂ` too), with real versions `xNorm p γ r = (X_gamma_norm p γ r).toReal`, `yNorm`.
  Typical statement:
  `r ∈ X_gamma p γ → R_eps p ε r ∈ Y_gamma p γ ∧ yNorm p γ (R_eps p ε r) ≤ C * ε * xNorm p γ r`.
  Complex versions of the spaces: `X_gammaC`, `Y_gammaC`.
* Cutoffs are explicit functions (no choice): `chiPlus` (χ₊), `rho` (ρ of def:c04_osc_integral,
  also the χ of def:c08_frequency_split), `chiAnnulus` (χ of def:residual_decomposition).
* Fourier: `fourierT f ξ = ∫ f(x) e^{-ixξ} dx` and `invFourierT g x = (2π)⁻¹ ∫ g(ξ) e^{ixξ} dξ`
  on `ℝ → ℂ` (coerce real functions with `fun x => (f x : ℂ)`); `fourierMultiplier m f`;
  distributional transforms `HasDistFourier u m` (`û = m` in `𝒮'`) and `distFourierInv m`.
  (Mathlib's `Real.fourierIntegral` uses `e^{-2πixξ}`; do not mix.)

## Name table (blueprint → Lean)

Basic: `⟨y⟩` `jb y`; `W` `corner`; `c_α` `calpha p`; `Φ₀` `Phi0 p ξ`; `χ₊` `chiPlus`;
  `S_f(y,z)` `c01_secant f y z` (complex: `c01_secantC`); `𝒜` `c01_admissible_class`;
  `IsPolyBounded u`; `W2inftyLoc r`, `W1inftyLoc G`.
Operators (ch01): `|D|^p g` `fracD p g y` (complex `fracDC`); `|D|^p ∂_y f` `fracDdy p f y`;
  `A_ε(u)` `A_eps p ε u` (`B_ε` = `A_eps_B`); `𝒥_ε` `c01_Jfull_eps p ε f y` (`𝒥 = 𝒥₁`);
  `𝒥̃_ε` `J_eps`; `𝒬_ε` `c01_Q_eps`; `ℰ_ε` `residual p ε f y`; `ℒ₀` `L0 p f y`;
  `ℰ̃_ε` `c01_quasilinear_residual`; `profile_equation p ε f : Prop`;
  `gsqg_front_equation p I F : Prop` (`F x t`, e.g. `I = Set.Iio T`);
  `L_T(t)` `self_similar_ansatz_L p T t`; `F_{ε,T,f}(x,t)` `self_similar_ansatz p ε T f x t`.
Spaces (ch02): `parameters`, `beta`, `admissibleGamma`; `X_gamma`, `Y_gamma`, norms as above;
  `ℓ(G)` `ell p G : ℂ`; `Ỹ_γ` `Y_gamma_tilde p γ`; `μ_*` `mu_star p`; `G₊` `G_plus p`,
  `G₋` `G_minus p`, `G_μ` `G_mu p μ` (all real-valued `ℝ → ℝ`; symbols `G_pm_hat p s`,
  `G_pm_of p s` = real part of the inverse transform of `G_pm_hat p s`); `Π G` `Pi_projection p G`.
Linear (ch02/08): `c_ε` `c_eps p ε`; `b_c` `c08_phi_b p c`, `b_ε` `b_eps p ε`;
  `φ_c` `c08_phi p c`, `ψ_c` `c08_phi_inv p c`, `φ_ε` `phi_eps p ε`, `ψ_ε` `psi_eps p ε`;
  `𝒰_ε` `U_eps p ε u`, `𝒰_ε⁻¹` `U_eps_inv`, `𝒱_ε` `V_eps`, `𝒱_ε⁻¹` `V_eps_inv`;
  `K_ε` `R_eps_kernel`, `ℛ_{1,ε}` `R_eps_one`, `ℛ_{2,ε}` `R_eps_two`, `ℛ_ε` `R_eps`;
  `ℒ_ε` `L_eps p ε r y`; `𝒩_{ε,f̄}(r)` `N_eps p ε fbar r y`;
  `m_G` `T_0_symbol p G ξ`; `𝒯₀ G` `T_0 p G`; `𝒯_l G` `T_low p G`, `𝒯_h G` `T_high p G`.
Family (ch04): `S^m_+` `c04_osc_symbol m`; `Osc[a]` `c04_osc_integral p a y`;
  `f₀` `c04_linear_seed p`, `f_{0,+}` `c04_linear_seed_plus p` (ℂ-valued),
  `f_{0,high}` `c04_linear_seed_high`, `f_{0,low}` `c04_linear_seed_low`,
  `Γ₊` `c04_linear_seed_Gamma_plus`, `λ₀` `lambda0 p y`, `Ψ₀` `Psi0 p y`, `a_*` `astar p y`,
  `f_{0,μ}` `c04_linear_seed_mu p μ`;
  `𝒬_{ε,3}` `c04_cubic_part p ε v` (complex: `c04_cubic_part_complex`; `T(u,v,w)`
  `c04_cubic_part_trilinear`, `κ_ε` `c04_cubic_part_kappa`);
  `c₁(ε), c₂(ε)` `cubic_c1, cubic_c2`; `n_ε` `n_eps`, `c_cubic` `c_cubic p ε`,
  `c_log(μ)` `c_log p ε μ`, `c_power` `c_power`, `c₊` `c_plus`, `c₋` `c_minus`,
  `λ̃_{ε,μ}` `lambda_tilde p ε μ y`;
  `B̄(μ_*,δ)` `Bbar p δ`; `χ_R` `fam_chiR R`; `λ_{ε,μ}` `fam_lambda p ε μ`;
  `Ψ_{ε,μ}` `fam_Psi p R ε μ`; `Z_{ε,μ}` `fam_Z p R ε μ`; `Z₀` `fam_Z0 p R`;
  `f_slow` `fam_slow p R ε`; `f_osc` `fam_osc p R ε μ`;
  `f̄_{ε,μ}` `approximate_solution_family p R ε μ`;
  `χ_Y` `res_chiY Y`; `v_Y` `res_vY p R ε μ Y`; `D𝒬_ε(W)[h]` `res_DQW p ε h`;
  `ℰ₁…ℰ₉` `residual_decomposition_E1 p R ε y`, `_E2/_E3/_E4/_E6 p R ε μ y`,
  `_E5/_E7/_E8/_E9 p R ε μ Y y`; their sum `residual_decomposition p R ε μ Y y`.

## Notes
* `deriv` of a non-differentiable function is `0` in Mathlib; second derivatives of `X_γ`
  elements are `deriv (deriv r)`, meaningful a.e. (that is why the norms are essential suprema).
* `ell`, `c04_osc_integral` use `Filter.limUnder` (junk value if the limit does not exist);
  existence of the limit must be part of statements when needed.
* `T_0`, `T_high` use `distFourierInv` (junk `0` if no continuous polynomially bounded
  representative exists).
* No definition depends on `sorryAx`.
-/
