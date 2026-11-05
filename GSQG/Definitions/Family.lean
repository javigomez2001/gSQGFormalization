import GSQG.Definitions.Linear

/-!
# GSQG.Definitions.Family

Chapter 04 objects: the oscillatory integral `Osc` (`c04_osc_integral`) and symbol classes, the
linear seed `f₀` and its pieces, the cubic part `𝒬_{ε,3}`, the correction constants, the
approximate family `f̄_{ε,μ}` (with its ingredients `χ_R`, `λ_{ε,μ}`, `Ψ_{ε,μ}`, `Z_{ε,μ}`,
`f_slow`, `f_osc`) and the residual decomposition `ℰ₁,…,ℰ₉`.

Conventions: the family depends on the explicit parameters `p R ε μ` in this order
(`R` the fixed cutoff scale `R ≥ R₀`, `ε ∈ [0,ε₀]`, `μ ∈ Bbar p δ`).  The residual pieces
additionally take the localisation scale `Y` (`Y ≥ 8R`) and are defined for all `y`
(statements restrict to `y > R`, resp. `y ≥ 8R`).
-/

open MeasureTheory Set Filter Real

noncomputable section

namespace GSQG

/-! ### Oscillatory integrals -/

/-- Blueprint: def:c04_osc_integral.  The symbol class `S^m_+`: smooth `a : ℝ → ℂ`, `a = 0` on
`(-∞,1]`, `|∂^l a(ξ)| ≤ C_l ξ^{m-l}` for `ξ ≥ 1`. -/
def c04_osc_symbol (m : ℝ) : Set (ℝ → ℂ) :=
  {a | ContDiff ℝ (⊤ : ℕ∞) a ∧ (∀ ξ ≤ 1, a ξ = 0) ∧
    ∀ l : ℕ, ∃ C : ℝ, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l a ξ‖ ≤ C * ξ ^ (m - l)}

/-- Blueprint: def:c04_osc_integral.
`Osc[a](y) = lim_{M→∞} ∫₀^∞ ρ(ξ/M) a(ξ) e^{i(yξ - Φ₀(ξ))} dξ` (`ρ = GSQG.rho`). -/
def c04_osc_integral (p : ℝ) (a : ℝ → ℂ) (y : ℝ) : ℂ :=
  limUnder atTop (fun M : ℝ => ∫ ξ in Ioi (0 : ℝ),
    (rho (ξ / M) : ℂ) * a ξ * Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)))

/-! ### The linear seed -/

/-- Blueprint: def:c04_linear_seed.
`f₀(y) = -y/2 + π⁻¹ ∫₀^∞ (1 - cos(yξ - Φ₀(ξ)))/ξ² dξ`. -/
def c04_linear_seed (p : ℝ) (y : ℝ) : ℝ :=
  -y / 2 + π⁻¹ * ∫ ξ in Ioi (0 : ℝ), (1 - Real.cos (y * ξ - Phi0 p ξ)) / ξ ^ 2

/-- Blueprint: def:c04_linear_seed.
`f_{0,+}(y) = -(2π)⁻¹ ∫₀^∞ χ₊(ξ)/ξ² · e^{i(yξ-Φ₀(ξ))} dξ`. -/
def c04_linear_seed_plus (p : ℝ) (y : ℝ) : ℂ :=
  -((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ in Ioi (0 : ℝ),
    ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ))

/-- Blueprint: def:c04_linear_seed.  `f_{0,high} = 2 Re f_{0,+}`. -/
def c04_linear_seed_high (p : ℝ) (y : ℝ) : ℝ := 2 * (c04_linear_seed_plus p y).re

/-- Blueprint: def:c04_linear_seed.  `f_{0,low} = f₀ - f_{0,high}`. -/
def c04_linear_seed_low (p : ℝ) (y : ℝ) : ℝ := c04_linear_seed p y - c04_linear_seed_high p y

/-- Blueprint: def:c04_linear_seed.
`Γ₊(y) = (2π)⁻¹ ∫₀^∞ χ₊'(ξ)/ξ · e^{i(yξ-Φ₀(ξ))} dξ`. -/
def c04_linear_seed_Gamma_plus (p : ℝ) (y : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ in Ioi (0 : ℝ),
    ((deriv chiPlus ξ / ξ : ℝ) : ℂ) * Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ))

/-- Blueprint: def:c04_linear_seed.  `λ₀(y) = y^{1/p}` (used for `y > 0`). -/
def lambda0 (p y : ℝ) : ℝ := y ^ (1 / p)

/-- Blueprint: def:c04_linear_seed.  `Ψ₀(y) = p/(p+1) · y^{1+1/p}` (used for `y > 0`). -/
def Psi0 (p y : ℝ) : ℝ := p / (p + 1) * y ^ (1 + 1 / p)

/-- Blueprint: def:c04_linear_seed.
`a_*(y) = e^{-i(Ψ₀(y)-π/4)} f_{0,+}'(y) / (μ_* λ₀(y)^{-(p+1)/2})` (used for `y > 0`). -/
def astar (p y : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ))) /
    (mu_star p * ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ)) * deriv (c04_linear_seed_plus p) y

/-- Blueprint: def:c04_linear_seed.  `f_{0,μ} = f₀ + 2 Re[(μ/μ_* - 1) f_{0,+}]`. -/
def c04_linear_seed_mu (p : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  c04_linear_seed p y + 2 * ((μ / mu_star p - 1) * c04_linear_seed_plus p y).re

/-! ### Cubic part -/

/-- Blueprint: def:c04_cubic_part.  The trilinear form
`T(u,v,w)(y) = ∫ (u'(y)-u'(z))/|y-z|^α · S_v(y,z) S_w(y,z) dz` (complex-valued). -/
def c04_cubic_part_trilinear (p : ℝ) (u v w : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ z, (deriv u y - deriv u z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ) * c01_secantC v y z * c01_secantC w y z

/-- Blueprint: def:c04_cubic_part.  `κ_ε = -(p+1) ε c_α / 2`. -/
def c04_cubic_part_kappa (p ε : ℝ) : ℝ := -((p + 1) * ε * calpha p) / 2

/-- Blueprint: def:c04_cubic_part.  Real `v`:
`𝒬_{ε,3}(v)(y) = -(p+1)εc_α/2 · ∫ (v'(y)-v'(z))/|y-z|^α · S_v(y,z)² dz`. -/
def c04_cubic_part (p ε : ℝ) (v : ℝ → ℝ) (y : ℝ) : ℝ :=
  c04_cubic_part_kappa p ε *
    ∫ z, (deriv v y - deriv v z) / |y - z| ^ (p + 1) * c01_secant v y z ^ 2

/-- Blueprint: def:c04_cubic_part.  Complex `v`: `𝒬_{ε,3}(v) = κ_ε T(v,v,v)`. -/
def c04_cubic_part_complex (p ε : ℝ) (v : ℝ → ℂ) (y : ℝ) : ℂ :=
  (c04_cubic_part_kappa p ε : ℂ) * c04_cubic_part_trilinear p v v v y

/-! ### Correction constants -/

/-- Blueprint: def:c04_correction_constants (via lem:c04_cubic_sine_response).  `c₁(ε)`, the
coefficient of `cos y` in `𝒬_{ε,3}(sin)`.
Encoding: `c₁, c₂` are the unique reals with `𝒬_{ε,3}(sin) = c₁ cos y + c₂ cos 3y`; they are
defined here by the orthogonality formulas
`c₁ = π⁻¹ ∫₀^{2π} 𝒬_{ε,3}(sin) cos y dy`, `c₂ = π⁻¹ ∫₀^{2π} 𝒬_{ε,3}(sin) cos 3y dy`, which give the
same numbers whenever that representation holds (lem:c04_cubic_sine_response). -/
def cubic_c1 (p ε : ℝ) : ℝ :=
  π⁻¹ * ∫ y in (0 : ℝ)..(2 * π), c04_cubic_part p ε Real.sin y * Real.cos y

/-- Blueprint: def:c04_correction_constants.  `c₂(ε)`, the coefficient of `cos 3y` in
`𝒬_{ε,3}(sin)` (see the docstring of `cubic_c1`). -/
def cubic_c2 (p ε : ℝ) : ℝ :=
  π⁻¹ * ∫ y in (0 : ℝ)..(2 * π), c04_cubic_part p ε Real.sin y * Real.cos (3 * y)

/-- Blueprint: def:c04_correction_constants.  `n_ε = 4 c₁(ε)`. -/
def n_eps (p ε : ℝ) : ℝ := 4 * cubic_c1 p ε

/-- Blueprint: def:c04_correction_constants.  `c_cubic = -4c₂(ε)/(3^p - 1)`. -/
def c_cubic (p ε : ℝ) : ℝ := -4 * cubic_c2 p ε / ((3 : ℝ) ^ p - 1)

/-- Blueprint: def:c04_correction_constants.  `c_log(μ) = -n_ε |μ|²/p`. -/
def c_log (p ε : ℝ) (μ : ℂ) : ℝ := -(n_eps p ε * ‖μ‖ ^ 2) / p

/-- Blueprint: def:c04_correction_constants.  `c_power = -c_ε/(1-p²)`. -/
def c_power (p ε : ℝ) : ℝ := -c_eps p ε / (1 - p ^ 2)

/-- Blueprint: def:c04_correction_constants.  `c₊ = -c_ε/(p+1)`. -/
def c_plus (p ε : ℝ) : ℝ := -c_eps p ε / (p + 1)

/-- Blueprint: def:c04_correction_constants.  `c₋ = c_α/(p+1) ∫₀¹ (A_ε(t)-1) t^{p-1} dt`. -/
def c_minus (p ε : ℝ) : ℝ :=
  calpha p / (p + 1) * ∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * t ^ (p - 1)

/-- Blueprint: def:c04_correction_constants.
`λ̃_{ε,μ}(y) = -(c_ε/p) y^{-p-1} + c_log(μ) y^{-1-1/p}` (used for `y > 0`). -/
def lambda_tilde (p ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  -(c_eps p ε / p) * y ^ (-p - 1) + c_log p ε μ * y ^ (-1 - 1 / p)

/-! ### The approximate solution family -/

/-- Blueprint: def:approximate_solution_family.  `B̄ = {μ : |μ - μ_*| ≤ δ}`. -/
def Bbar (p δ : ℝ) : Set ℂ := Metric.closedBall (mu_star p) δ

/-- Blueprint: def:approximate_solution_family.  `χ_R(y) = χ₊(y/R)`. -/
def fam_chiR (R y : ℝ) : ℝ := chiPlus (y / R)

/-- Blueprint: def:approximate_solution_family.  The modified frequency
`λ_{ε,μ}(y) = y^{1/p} + c_power (1-p²)/p · y^{1/p-p-1} + c_log(μ)/y` (used for `y > R/2`). -/
def fam_lambda (p ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  y ^ (1 / p) + c_power p ε * ((1 - p ^ 2) / p) * y ^ (1 / p - p - 1) + c_log p ε μ / y

/-- Blueprint: def:approximate_solution_family.  The modified phase, `Ψ' = λ_{ε,μ}`,
`Ψ(R) = Ψ₀(R)`: `Ψ_{ε,μ}(y) = Ψ₀(R) + ∫_R^y λ_{ε,μ}` (used for `y > R/2`). -/
def fam_Psi (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  Psi0 p R + ∫ t in R..y, fam_lambda p ε μ t

/-- Blueprint: def:approximate_solution_family.
`Z_{ε,μ}(y) = μ a_*(y) λ_{ε,μ}(y)^{-(p+1)/2} e^{i(Ψ_{ε,μ}(y) - π/4)}`. -/
def fam_Z (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℂ :=
  μ * astar p y * ((fam_lambda p ε μ y ^ (-(p + 1) / 2) : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((fam_Psi p R ε μ y - π / 4 : ℝ) : ℂ))

/-- Blueprint: def:approximate_solution_family.  `Z₀ = Z_{0,μ_*}`. -/
def fam_Z0 (p R : ℝ) (y : ℝ) : ℂ := fam_Z p R 0 (mu_star p) y

/-- Blueprint: def:approximate_solution_family.
`f_slow(y) = c₊ y^{-p} χ_R(y) + c₋ |y|^{-p} χ_R(-y)`. -/
def fam_slow (p R ε : ℝ) (y : ℝ) : ℝ :=
  c_plus p ε * y ^ (-p) * fam_chiR R y + c_minus p ε * |y| ^ (-p) * fam_chiR R (-y)

/-- Blueprint: def:approximate_solution_family.
`f_osc(y) = -2 χ_R(y) Re ∫_y^∞ (Z + c_cubic Z³ - (μ/μ_*) Z₀) dt` for `y > R`, `0` for `y ≤ R`. -/
def fam_osc (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  if R < y then
    -2 * fam_chiR R y * (∫ t in Ioi y, (fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3 -
      μ / mu_star p * fam_Z0 p R t)).re
  else 0

/-- Blueprint: def:approximate_solution_family.  `f̄_{ε,μ} = f_{0,μ} + f_slow + f_osc`
(for the fixed cutoff scale `R`). -/
def approximate_solution_family (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  c04_linear_seed_mu p μ y + fam_slow p R ε y + fam_osc p R ε μ y

/-! ### Residual decomposition (`y ≥ 8R`) -/

/-- Blueprint: def:residual_decomposition.  `χ_Y(z) = χ(z/Y)` (`χ = GSQG.chiAnnulus`). -/
def res_chiY (Y z : ℝ) : ℝ := chiAnnulus (z / Y)

/-- Blueprint: def:residual_decomposition.  The local oscillatory front
`v_Y(z) = -2 χ_Y(z) Re ∫_z^∞ (Z + c_cubic Z³) dt` for `z > R`, `0` for `z ≤ R`. -/
def res_vY (p R ε : ℝ) (μ : ℂ) (Y z : ℝ) : ℝ :=
  if R < z then
    -2 * res_chiY Y z * (∫ t in Ioi z, (fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3)).re
  else 0

/-- Blueprint: def:residual_decomposition.  The Gateaux derivative of `𝒬_ε` at the corner:
`D𝒬_ε(W)[h](y) = c_α ∫_{-∞}^0 [(h'(y)-h'(z))(A_ε(z/(y-z)) - 1) + A_ε'(z/(y-z)) S_h(y,z)] dz/(y-z)^α`
(used for `y > 0`). -/
def res_DQW (p ε : ℝ) (h : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z in Iio (0 : ℝ),
    ((deriv h y - deriv h z) * (A_eps p ε (z / (y - z)) - 1) +
      deriv (A_eps p ε) (z / (y - z)) * c01_secant h y z) / (y - z) ^ (p + 1)

/-- Blueprint: def:residual_decomposition.  `ℰ₁ = ℒ₀(f_slow) + 𝒬_ε(W)`. -/
def residual_decomposition_E1 (p R ε : ℝ) (y : ℝ) : ℝ :=
  L0 p (fam_slow p R ε) y + c01_Q_eps p ε corner y

/-- Blueprint: def:residual_decomposition.
`ℰ₂ = 2(λ^p - y - pλ₀^{p-1} c_log(μ)/y + c_ε y^{-p}) Re Z`. -/
def residual_decomposition_E2 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  2 * (fam_lambda p ε μ y ^ p - y - p * lambda0 p y ^ (p - 1) * c_log p ε μ / y +
    c_eps p ε * y ^ (-p)) * (fam_Z p R ε μ y).re

/-- Blueprint: def:residual_decomposition.
`ℰ₃ = 2(pλ₀^{p-1} c_log(μ)/y + n_ε λ^p |Z|²) Re Z`. -/
def residual_decomposition_E3 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  2 * (p * lambda0 p y ^ (p - 1) * c_log p ε μ / y +
    n_eps p ε * fam_lambda p ε μ y ^ p * ‖fam_Z p R ε μ y‖ ^ 2) * (fam_Z p R ε μ y).re

/-- Blueprint: def:residual_decomposition.  `ℰ₄ = 2c_cubic(λ^p - y + c_ε y^{-p}) Re(Z³)`. -/
def residual_decomposition_E4 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  2 * c_cubic p ε * (fam_lambda p ε μ y ^ p - y + c_eps p ε * y ^ (-p)) *
    (fam_Z p R ε μ y ^ 3).re

/-- Blueprint: def:residual_decomposition.  `ℰ₅^Y = ℒ₀(f_osc) + 𝒬_{ε,3}(v_Y)
 - 2(λ^p - y + n_ε λ^p|Z|²) Re Z - 2c_cubic(λ^p - y) Re(Z³)`. -/
def residual_decomposition_E5 (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℝ :=
  L0 p (fam_osc p R ε μ) y + c04_cubic_part p ε (res_vY p R ε μ Y) y -
    2 * (fam_lambda p ε μ y ^ p - y + n_eps p ε * fam_lambda p ε μ y ^ p * ‖fam_Z p R ε μ y‖ ^ 2) *
      (fam_Z p R ε μ y).re -
    2 * c_cubic p ε * (fam_lambda p ε μ y ^ p - y) * (fam_Z p R ε μ y ^ 3).re

/-- Blueprint: def:residual_decomposition.  `ℰ₆ = D𝒬_ε(W)[f - W] - 2c_ε y^{-p} Re(Z + c_cubic Z³)`. -/
def residual_decomposition_E6 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  res_DQW p ε (fun z => approximate_solution_family p R ε μ z - corner z) y -
    2 * c_eps p ε * y ^ (-p) *
      (fam_Z p R ε μ y + (c_cubic p ε : ℂ) * fam_Z p R ε μ y ^ 3).re

/-- Blueprint: def:residual_decomposition.  `ℰ₇^Y = 𝒬_{ε,3}(χ_Y f) - 𝒬_{ε,3}(v_Y)`. -/
def residual_decomposition_E7 (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℝ :=
  c04_cubic_part p ε (fun z => res_chiY Y z * approximate_solution_family p R ε μ z) y -
    c04_cubic_part p ε (res_vY p R ε μ Y) y

/-- Blueprint: def:residual_decomposition.  `ℰ₈^Y = 𝒬_ε(χ_Y f) - 𝒬_{ε,3}(χ_Y f)`. -/
def residual_decomposition_E8 (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℝ :=
  c01_Q_eps p ε (fun z => res_chiY Y z * approximate_solution_family p R ε μ z) y -
    c04_cubic_part p ε (fun z => res_chiY Y z * approximate_solution_family p R ε μ z) y

/-- Blueprint: def:residual_decomposition.
`ℰ₉^Y = 𝒬_ε(f) - 𝒬_ε(W) - D𝒬_ε(W)[f - W] - 𝒬_ε(χ_Y f)`. -/
def residual_decomposition_E9 (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℝ :=
  c01_Q_eps p ε (approximate_solution_family p R ε μ) y - c01_Q_eps p ε corner y -
    res_DQW p ε (fun z => approximate_solution_family p R ε μ z - corner z) y -
    c01_Q_eps p ε (fun z => res_chiY Y z * approximate_solution_family p R ε μ z) y

/-- Blueprint: def:residual_decomposition.  The sum `ℰ₁ + ⋯ + ℰ₉^Y` (which equals
`ℰ̃_ε(f̄_{ε,μ}) - G_μ` on `(R,∞)` by lem:c04_residual_identity). -/
def residual_decomposition (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℝ :=
  residual_decomposition_E1 p R ε y + residual_decomposition_E2 p R ε μ y +
    residual_decomposition_E3 p R ε μ y + residual_decomposition_E4 p R ε μ y +
    residual_decomposition_E5 p R ε μ Y y + residual_decomposition_E6 p R ε μ y +
    residual_decomposition_E7 p R ε μ Y y + residual_decomposition_E8 p R ε μ Y y +
    residual_decomposition_E9 p R ε μ Y y

end GSQG
