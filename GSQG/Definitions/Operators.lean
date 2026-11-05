import GSQG.Definitions.Basic

/-!
# GSQG.Definitions.Operators

The operators of chapter 01: `|D|^p` (`fracD`, `fracDC`, `fracDdy`), `A_ε` (`A_eps`), the full
nonlinearity `𝒥_ε` (`c01_Jfull_eps`), `𝒥̃_ε` (`J_eps`), `𝒬_ε` (`c01_Q_eps`), the residual
`ℰ_ε` (`residual`), `ℒ₀` (`L0`), the quasilinear residual `ℰ̃_ε`, the profile equation, the front
equation and the self-similar ansatz.

All parameters are explicit reals: `p` (with `α = p+1`), `ε`.  All operators are defined for
*every* function `ℝ → ℝ` by the pointwise formula (Bochner integrals, which are `0` when the
integrand is not integrable); hypotheses such as `f ∈ c01_admissible_class` belong to statements.
Derivatives are Mathlib's `deriv`.
-/

open MeasureTheory Set Filter Real

noncomputable section

namespace GSQG

/-! ### The fractional multiplier -/

/-- Blueprint: def:frac_multiplier (1).  `|D|^p g(y) = c_α ∫ (g(y)-g(z)) / |y-z|^{α} dz`, `α = p+1`. -/
def fracD (p : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, (g y - g z) / |y - z| ^ (p + 1)

/-- Blueprint: def:frac_multiplier (1), complex-valued `g` (real and imaginary parts separately). -/
def fracDC (p : ℝ) (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  (calpha p : ℂ) * ∫ z, (g y - g z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)

/-- Blueprint: def:frac_multiplier (2).  `|D|^p ∂_y f := |D|^p (f')`. -/
def fracDdy (p : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := fracD p (deriv f) y

/-- Blueprint: def:frac_multiplier (name of the node).  Same as `fracD`.
(The Fourier-side description (3) is `fourierMultiplier (fun ξ => |ξ|^p)`.) -/
abbrev frac_multiplier : ℝ → (ℝ → ℝ) → ℝ → ℝ := fracD

/-! ### The front nonlinearity -/

/-- Blueprint: def:A_eps.  `A_ε(u) = (1+εu²)^{-α/2}`. -/
def A_eps (p ε u : ℝ) : ℝ := (1 + ε * u ^ 2) ^ (-(p + 1) / 2)

/-- Blueprint: def:A_eps.  `B_ε(u) = A_ε(u)⁻¹ = (1+εu²)^{α/2}`. -/
def A_eps_B (p ε u : ℝ) : ℝ := (1 + ε * u ^ 2) ^ ((p + 1) / 2)

/-- Blueprint: def:c01_Jfull_eps.  `𝒥_ε(f)(y) = c_α ∫ (f'(y)-f'(z))/|y-z|^α · A_ε(S_f(y,z)) dz`
(the second form in the blueprint; `𝒥 = 𝒥₁`). -/
def c01_Jfull_eps (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, (deriv f y - deriv f z) / |y - z| ^ (p + 1) * A_eps p ε (c01_secant f y z)

/-- Blueprint: def:J_eps.
`𝒥̃_ε(f)(y) = c_α ∫ (f'(y)-f'(z))/|y-z|^α · (A_ε(S_f(y,z)) - A_ε(f'(y))) dz`. -/
def J_eps (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
    (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))

/-- Blueprint: def:c01_Q_eps.  `𝒬_ε(f)(y) = c_α ∫ (f'(y)-f'(z))/|y-z|^α · (A_ε(S_f(y,z)) - 1) dz`. -/
def c01_Q_eps (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, (deriv f y - deriv f z) / |y - z| ^ (p + 1) * (A_eps p ε (c01_secant f y z) - 1)

/-- Blueprint: def:residual.
`ℰ_ε(f)(y) = |D|^p ∂_y f(y) + (f(y) - y f'(y) + 𝒥̃_ε(f)(y)) / A_ε(f'(y))`. -/
def residual (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  fracDdy p f y + (f y - y * deriv f y + J_eps p ε f y) / A_eps p ε (deriv f y)

/-- Blueprint: def:c01_quasilinear_residual and def:L_eps.  `ℒ₀ f = |D|^p f' + f - y f'`. -/
def L0 (p : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := fracDdy p f y + f y - y * deriv f y

/-- Blueprint: def:c01_quasilinear_residual.  `ℰ̃_ε(f) = ℒ₀ f + 𝒬_ε(f)`. -/
def c01_quasilinear_residual (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ := L0 p f y + c01_Q_eps p ε f y

/-- Blueprint: def:profile_equation.  `f ∈ 𝒜`, `ℰ_ε(f) ≡ 0`, `f' → -1` at `-∞`, `f → 0` at `+∞`. -/
def profile_equation (p ε : ℝ) (f : ℝ → ℝ) : Prop :=
  f ∈ c01_admissible_class ∧ (∀ y, residual p ε f y = 0) ∧
    Tendsto (deriv f) atBot (nhds (-1)) ∧ Tendsto f atTop (nhds 0)

/-- Blueprint: def:gsqg_front_equation.  `F : ℝ → ℝ → ℝ` (arguments `x t`) is a classical solution
of the gSQG front equation on `ℝ × I` (`I` an open interval, e.g. `Set.Iio T`):
(1) `F ∈ C¹(ℝ×I)`, `F(·,t) ∈ C²` and `∂ₓ²F` continuous on `ℝ×I`; (2) `∂ₓF(·,t)` bounded;
(3) `∂ₜF(x,t) = 𝒥(F(·,t))(x)` with `𝒥 = 𝒥₁`. -/
def gsqg_front_equation (p : ℝ) (I : Set ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I) ∧
  (∀ t ∈ I, ContDiff ℝ 2 (fun x => F x t)) ∧
  ContinuousOn (fun q : ℝ × ℝ => iteratedDeriv 2 (fun x => F x q.2) q.1) (univ ×ˢ I) ∧
  (∀ t ∈ I, ∃ M : ℝ, ∀ x, |deriv (fun x => F x t) x| ≤ M) ∧
  (∀ t ∈ I, ∀ x, deriv (fun s => F x s) t = c01_Jfull_eps p 1 (fun x' => F x' t) x)

/-- Blueprint: def:self_similar_ansatz.  `L_T(t) = (α(T-t))^{1/α}`, `α = p+1`. -/
def self_similar_ansatz_L (p T t : ℝ) : ℝ := ((p + 1) * (T - t)) ^ (1 / (p + 1))

/-- Blueprint: def:self_similar_ansatz.  `F_{ε,T,f}(x,t) = √ε L_T(t) f(x/L_T(t))`. -/
def self_similar_ansatz (p ε T : ℝ) (f : ℝ → ℝ) (x t : ℝ) : ℝ :=
  Real.sqrt ε * self_similar_ansatz_L p T t * f (x / self_similar_ansatz_L p T t)

end GSQG
