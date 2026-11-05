import GSQG.Definitions.Spaces

/-!
# GSQG.Definitions.Linear

The linear operators: `c_ε` (`c_eps`, lem:analysis_coefficient), the coefficient `b_ε`, the
conjugating diffeomorphism `φ_c` (`c08_phi`) and its inverse, `𝒰_ε`, `𝒱_ε` and their inverses,
the remainder `ℛ_ε = ℛ_{1,ε} + ℛ_{2,ε}`, `ℒ_ε`, `𝒩_{ε,f̄}`, the free inverse `𝒯₀` with its symbol
`m_G`, and the low/high frequency splitting `𝒯_l`, `𝒯_h`.

All maps act on *all* functions `ℝ → ℝ` (as in the blueprint, `𝒰_ε, 𝒱_ε` are bijections of the
space of all functions); mapping properties between `X_γ`, `Y_γ` are theorems.
-/

open MeasureTheory Set Filter Real

noncomputable section

namespace GSQG

/-- Blueprint: def:c03_coefficient (the explicit constant).
`c_ε = c_α ∫₀¹ ((1+εt²)^{-α/2} - 1)(1-t)^{p-1} dt`. -/
def c_eps (p ε : ℝ) : ℝ :=
  calpha p * ∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * (1 - t) ^ (p - 1)

/-! ### The conjugating diffeomorphism -/

/-- Blueprint: def:c08_phi.  `b_c(y) = c χ₊(y) y^{-p}` (it vanishes for `y ≤ 1`). -/
def c08_phi_b (p c : ℝ) (y : ℝ) : ℝ := if 1 < y then c * chiPlus y * y ^ (-p) else 0

/-- Blueprint: def:L_eps.  `b_ε = b_{c_ε}`, i.e. `b_ε(y) = c_ε χ₊(y) y^{-p}`. -/
def b_eps (p ε : ℝ) : ℝ → ℝ := c08_phi_b p (c_eps p ε)

/-- Blueprint: def:c08_phi.  `φ_c(y) = y` for `y ≤ 1`,
`φ_c(y) = [1 + (p+1)/p ∫₁^y (t - b_c(t))^{1/p} dt]^{p/(p+1)}` for `y > 1`. -/
def c08_phi (p c : ℝ) (y : ℝ) : ℝ :=
  if y ≤ 1 then y
  else (1 + (p + 1) / p * ∫ t in (1 : ℝ)..y, (t - c08_phi_b p c t) ^ (1 / p)) ^ (p / (p + 1))

/-- Blueprint: def:c08_phi.  `ψ_c = φ_c⁻¹` (`Function.invFun`; the true inverse since `φ_c` is a
bijection for `|c| ≤ 1/2`, lem:c08_phi_diffeo). -/
def c08_phi_inv (p c : ℝ) : ℝ → ℝ := Function.invFun (c08_phi p c)

/-- Blueprint: def:c08_phi.  `φ_ε = φ_{c_ε}`. -/
def phi_eps (p ε : ℝ) : ℝ → ℝ := c08_phi p (c_eps p ε)

/-- Blueprint: def:c08_phi.  `ψ_ε = ψ_{c_ε}`. -/
def psi_eps (p ε : ℝ) : ℝ → ℝ := c08_phi_inv p (c_eps p ε)

/-! ### `𝒰_ε`, `𝒱_ε` -/

/-- Blueprint: def:U_eps.  `𝒰_ε u = u ∘ ψ_ε`. -/
def U_eps (p ε : ℝ) (u : ℝ → ℝ) : ℝ → ℝ := fun y => u (psi_eps p ε y)

/-- Blueprint: def:U_eps.  `𝒰_ε⁻¹ u = u ∘ φ_ε`. -/
def U_eps_inv (p ε : ℝ) (u : ℝ → ℝ) : ℝ → ℝ := fun y => u (phi_eps p ε y)

/-- Blueprint: def:V_eps.  `(𝒱_ε u)(y) = φ_ε'(y)^{p+1} u(φ_ε(y))`. -/
def V_eps (p ε : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun y => deriv (phi_eps p ε) y ^ (p + 1) * u (phi_eps p ε y)

/-- Blueprint: def:V_eps.  `(𝒱_ε⁻¹ u)(y) = ψ_ε'(y)^{p+1} u(ψ_ε(y))`. -/
def V_eps_inv (p ε : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun y => deriv (psi_eps p ε) y ^ (p + 1) * u (psi_eps p ε y)

/-! ### The remainder `ℛ_ε` -/

/-- Blueprint: def:R_eps.  `K_ε(y,z) = c_α [1 - (φ_ε'(y)/S_{φ_ε}(y,z))^{p+1}] / |y-z|^{1+p}`. -/
def R_eps_kernel (p ε : ℝ) (y z : ℝ) : ℝ :=
  calpha p * (1 - (deriv (phi_eps p ε) y / c01_secant (phi_eps p ε) y z) ^ (p + 1)) /
    |y - z| ^ (1 + p)

/-- Blueprint: def:R_eps.  `ℛ_{1,ε} r = ((φ_ε')^{p+1} - 1) r`. -/
def R_eps_one (p ε : ℝ) (r : ℝ → ℝ) (y : ℝ) : ℝ :=
  (deriv (phi_eps p ε) y ^ (p + 1) - 1) * r y

/-- Blueprint: def:R_eps.  `ℛ_{2,ε} r(y) = ∫ K_ε(y,z) r'(z) dz`. -/
def R_eps_two (p ε : ℝ) (r : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, R_eps_kernel p ε y z * deriv r z

/-- Blueprint: def:R_eps.  `ℛ_ε = ℛ_{1,ε} + ℛ_{2,ε}`. -/
def R_eps (p ε : ℝ) (r : ℝ → ℝ) (y : ℝ) : ℝ := R_eps_one p ε r y + R_eps_two p ε r y

/-! ### `ℒ_ε`, `𝒩_{ε,f̄}` -/

/-- Blueprint: def:L_eps.  `ℒ_ε r = ℒ₀ r + b_ε r' + ℛ_ε r` (`ℒ₀ = GSQG.L0`). -/
def L_eps (p ε : ℝ) (r : ℝ → ℝ) (y : ℝ) : ℝ :=
  L0 p r y + b_eps p ε y * deriv r y + R_eps p ε r y

/-- Blueprint: def:N_eps.  `𝒩_{ε,f̄}(r) = ℰ_ε(f̄ + r) - ℰ_ε(f̄) - ℒ_ε(r)`. -/
def N_eps (p ε : ℝ) (fbar r : ℝ → ℝ) (y : ℝ) : ℝ :=
  residual p ε (fbar + r) y - residual p ε fbar y - L_eps p ε r y

/-! ### The free inverse `𝒯₀` -/

/-- Blueprint: def:T_0.  The symbol `m_G(ξ) = ∫₀¹ t e^{-i(1-t^{p+1})Φ₀(ξ)} Ĝ(tξ) dt`. -/
def T_0_symbol (p : ℝ) (G : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ) * Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) *
    fourierT (fun x => (G x : ℂ)) (t * ξ)

/-- Blueprint: def:T_0.  `𝒯₀ G = (m_G)^∨`, realised as the (unique) continuous, polynomially
bounded real function `r` with `r̂ = m_G` in `𝒮'` (`GSQG.distFourierInv`), and `0` if there is
none.  In particular "`𝒯₀ G ∈ X_γ`" in the blueprint's sense (some `r ∈ X_γ` has `r̂ = m_G`)
is equivalent to `T_0 p G ∈ X_gamma p γ` together with `HasDistFourier (T_0 p G) (T_0_symbol p G)`.
Encoding: `(m_G)^∨` is realised only when it is a continuous polynomially bounded function, which
is the only case used. -/
def T_0 (p : ℝ) (G : ℝ → ℝ) : ℝ → ℝ := distFourierInv (T_0_symbol p G)

/-- Blueprint: def:c08_frequency_split.  `𝒯_l G = (χ m_G)^∨` (`χ = GSQG.rho`), a real function
(real part taken; it is real since `χ m_G` is Hermitian). -/
def T_low (p : ℝ) (G : ℝ → ℝ) (y : ℝ) : ℝ :=
  (invFourierT (fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ) y).re

/-- Blueprint: def:c08_frequency_split.  `𝒯_h G = ((1-χ) m_G)^∨`, realised as in `T_0`. -/
def T_high (p : ℝ) (G : ℝ → ℝ) : ℝ → ℝ :=
  distFourierInv (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ)

end GSQG
