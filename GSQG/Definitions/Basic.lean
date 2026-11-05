import Mathlib

/-!
# GSQG.Definitions.Basic

Elementary objects shared by all chapters: the Japanese bracket `jb`, the corner `corner` (= `W`),
the fixed cutoff functions (`chiPlus`, `rho`, `chiAnnulus`), the constant `calpha` (= `c_α`),
the dispersive phase `Phi0` (= `Φ₀`), the Fourier convention (`fourierT`, `invFourierT`,
`fourierMultiplier`, distributional Fourier transforms `HasDistFourier`, `distFourierInv`),
the secant `c01_secant` and the admissible profile class `c01_admissible_class`.
-/

open MeasureTheory Set Filter Real

noncomputable section

namespace GSQG

/-! ### Japanese bracket, corner, constants -/

/-- The Japanese bracket `⟨y⟩ = √(1+y²)`. -/
def jb (y : ℝ) : ℝ := Real.sqrt (1 + y ^ 2)

/-- Blueprint: def:c01_corner. The model corner `W(y) = y₋ = max(-y, 0)`.  Note that Mathlib's `deriv corner` is
`-𝟙_{(-∞,0)}` (it is `0` at the non-differentiability point `0`), exactly the convention
`W' = -𝟙_{(-∞,0)}` of chapter 04. -/
def corner (y : ℝ) : ℝ := max (-y) 0

/-- `c_α = Γ(1+p) sin(πp/2)/π` (with `α = p+1`), the normalising constant of `|D|^p`. -/
def calpha (p : ℝ) : ℝ := Real.Gamma (1 + p) * Real.sin (π * p / 2) / π

/-- Blueprint: def:parameters (the phase).  `Φ₀(ξ) = ξ|ξ|^p/(p+1)`. -/
def Phi0 (p ξ : ℝ) : ℝ := ξ * |ξ| ^ p / (p + 1)

/-! ### Fixed cutoff functions (built explicitly from `Real.smoothTransition`) -/

/-- Blueprint: def:parameters (the cutoff `χ₊`).  `χ₊ ∈ C^∞(ℝ;[0,1])`, nondecreasing,
`χ₊ = 0` on `(-∞,1]`, `χ₊ = 1` on `[2,∞)`.  Explicitly `χ₊(ξ) = smoothTransition(ξ-1)`. -/
def chiPlus (ξ : ℝ) : ℝ := Real.smoothTransition (ξ - 1)

/-- Blueprint: def:c04_osc_integral (the truncation `ρ`) and def:c08_frequency_split (the cutoff `χ`).
`ρ ∈ C_c^∞(ℝ;[0,1])`, even, `ρ = 1` on `[-1,1]`, `supp ρ ⊆ [-2,2]`.
Explicitly `ρ(ξ) = smoothTransition(2-|ξ|)` (smooth since it is constant near `0`). -/
def rho (ξ : ℝ) : ℝ := Real.smoothTransition (2 - |ξ|)

/-- Blueprint: def:residual_decomposition (the cutoff `χ`).  `χ ∈ C_c^∞((1/4,4);[0,1])` with
`χ = 1` on `[1/2,3]`; explicitly its support is contained in `[3/10, 7/2]`. -/
def chiAnnulus (z : ℝ) : ℝ :=
  Real.smoothTransition ((z - 3 / 10) / (1 / 5)) * Real.smoothTransition ((7 / 2 - z) / (1 / 2))

/-! ### Fourier convention -/

/-- Blueprint: def:fourier_convention.  `f̂(ξ) = ∫ f(x) e^{-ixξ} dx` (Bochner integral; it is the
Fourier transform for `f ∈ L¹`, and `0` by Bochner convention when `f` is not integrable). -/
def fourierT (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))

/-- Blueprint: def:fourier_convention.  Inverse transform `ǧ(x) = (2π)⁻¹ ∫ g(ξ) e^{ixξ} dξ`. -/
def invFourierT (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, g ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))

/-- Blueprint: def:fourier_convention (the name of the node).  Same as `fourierT`. -/
abbrev fourier_convention : (ℝ → ℂ) → ℝ → ℂ := fourierT

/-- Blueprint: def:fourier_convention.  Fourier multiplier `m(D)f = (m f̂)^∨`. -/
def fourierMultiplier (m : ℝ → ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  invFourierT (fun ξ => m ξ * fourierT f ξ)

/-- Polynomially bounded functions: `‖u x‖ ≤ C ⟨x⟩^N`. -/
def IsPolyBounded {E : Type*} [Norm E] (u : ℝ → E) : Prop :=
  ∃ C N : ℝ, ∀ x, ‖u x‖ ≤ C * jb x ^ N

/-- Blueprint: def:fourier_convention (extension to `𝒮'` by duality).
`HasDistFourier u m` means `û = m` in `𝒮'(ℝ)`, i.e. `⟨u, φ̂⟩ = ⟨m, φ⟩` for every Schwartz `φ`:
`∫ u(x) φ̂(x) dx = ∫ m(ξ) φ(ξ) dξ`.  (Meaningful when `u` and `m` are locally integrable and
polynomially bounded.) -/
def HasDistFourier (u : ℝ → ℂ) (m : ℝ → ℂ) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ, ∫ x, u x * fourierT (⇑φ) x = ∫ ξ, m ξ * φ ξ

open scoped Classical in
/-- The real, continuous, polynomially bounded function whose distributional Fourier transform is
`m`, if it exists (it is then unique); `0` otherwise.  Used to realise `𝒯₀ G = (m_G)^∨`. -/
def distFourierInv (m : ℝ → ℂ) : ℝ → ℝ :=
  if h : ∃ r : ℝ → ℝ, Continuous r ∧ IsPolyBounded r ∧ HasDistFourier (fun x => (r x : ℂ)) m then
    Classical.choose h
  else 0

/-! ### Secant and admissible profiles -/

/-- Blueprint: def:c01_secant.  `S_f(y,z) = (f(y)-f(z))/(y-z)` for `y ≠ z`, `S_f(y,y) = f'(y)`. -/
def c01_secant (f : ℝ → ℝ) (y z : ℝ) : ℝ :=
  if y = z then deriv f y else (f y - f z) / (y - z)

/-- Blueprint: def:c01_secant (complex-valued version, used for `𝒬_{ε,3}` of complex `v`). -/
def c01_secantC (f : ℝ → ℂ) (y z : ℝ) : ℂ :=
  if y = z then deriv f y else (f y - f z) / ((y - z : ℝ) : ℂ)

/-- Blueprint: def:c01_admissible_class.  `𝒜 = {f ∈ C¹ : f' ∈ L^∞, f' locally Lipschitz}`. -/
def c01_admissible_class : Set (ℝ → ℝ) :=
  {f | ContDiff ℝ 1 f ∧ (∃ M : ℝ, ∀ y, |deriv f y| ≤ M) ∧ LocallyLipschitz (deriv f)}

end GSQG
