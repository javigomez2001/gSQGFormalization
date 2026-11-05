import GSQG.Definitions.Operators

/-!
# GSQG.Definitions.Spaces

Chapter 02 objects: the fixed parameters (`parameters`, `beta`, `admissibleGamma`), the weighted
spaces `X_γ`, `Y_γ` (ℝ≥0∞-valued norms `X_gamma_norm`, `Y_gamma_norm` defined with essential
suprema; real-valued `xNorm`, `yNorm`; spaces as `Set (ℝ → ℝ)`), the obstruction functional
`ell`, `Ỹ_γ = ker ℓ` (`Y_gamma_tilde`), `μ_*` (`mu_star`), the functions `G_±`, `G_μ` and the
projection `Π`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal

noncomputable section

namespace GSQG

/-! ### Parameters -/

/-- `β = (p+1)/(2p)`. -/
def beta (p : ℝ) : ℝ := (p + 1) / (2 * p)

/-- Blueprint: def:parameters.  `γ` is admissible if `β + 1/p < γ < 2p+1`. -/
def admissibleGamma (p γ : ℝ) : Prop := beta p + 1 / p < γ ∧ γ < 2 * p + 1

/-- Blueprint: def:parameters.  The fixed parameters `3/4 < p < 1`,
`β + 1/p < γ₁ < γ₂ < 2p+1` (with `α = p+1`, `β = (p+1)/(2p)`).  The cutoff `χ₊` is the fixed
function `GSQG.chiPlus` and the phase is `GSQG.Phi0 p`. -/
structure parameters where
  /-- `p = α - 1`. -/
  p : ℝ
  /-- the weaker decay exponent. -/
  γ₁ : ℝ
  /-- the stronger decay exponent. -/
  γ₂ : ℝ
  hp_lo : 3 / 4 < p
  hp_hi : p < 1
  hγ₁ : beta p + 1 / p < γ₁
  hγ₁₂ : γ₁ < γ₂
  hγ₂ : γ₂ < 2 * p + 1

namespace parameters

/-- `α = p + 1`. -/
def α (P : parameters) : ℝ := P.p + 1

/-- `β = (p+1)/(2p)`. -/
def β (P : parameters) : ℝ := beta P.p

/-- admissibility of `γ` for the parameters `P`. -/
def admissible (P : parameters) (γ : ℝ) : Prop := admissibleGamma P.p γ

end parameters

/-! ### Regularity classes -/

/-- `W^{2,∞}_loc`: `C¹` with locally Lipschitz derivative (then `r'' = deriv (deriv r)` a.e.). -/
def W2inftyLoc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℝ → E) : Prop :=
  ContDiff ℝ 1 r ∧ LocallyLipschitz (deriv r)

/-- `W^{1,∞}_loc`: locally Lipschitz (then `G' = deriv G` a.e.). -/
def W1inftyLoc {E : Type*} [NormedAddCommGroup E] (G : ℝ → E) : Prop := LocallyLipschitz G

/-! ### The spaces `X_γ`, `Y_γ` -/

/-- Blueprint: def:X_gamma.  The `X_γ` norm (in `[0,∞]`):
`ess sup_{y≥0} ⟨y⟩^γ(|r| + ⟨y⟩^{-1/p}|r'| + ⟨y⟩^{-2/p}|r''|)
 + ess sup_{y≤0} ⟨y⟩^γ(|r| + ⟨y⟩|r'| + ⟨y⟩²|r''|)`, with `r' = deriv r`, `r'' = deriv (deriv r)`.
Defined for functions with values in any real normed space (`ℝ` or `ℂ`). -/
def X_gamma_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p γ : ℝ) (r : ℝ → E) :
    ℝ≥0∞ :=
  essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv r) y‖))) (volume.restrict (Ici 0)) +
  essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0))

/-- Blueprint: def:X_gamma.  `X_γ = {r ∈ W^{2,∞}_loc : ‖r‖_{X_γ} < ∞}` (real-valued). -/
def X_gamma (p γ : ℝ) : Set (ℝ → ℝ) := {r | W2inftyLoc r ∧ X_gamma_norm p γ r < ⊤}

/-- Blueprint: def:X_gamma.  Complex-valued version `X_γ^ℂ` (chapter 08). -/
def X_gammaC (p γ : ℝ) : Set (ℝ → ℂ) := {r | W2inftyLoc r ∧ X_gamma_norm p γ r < ⊤}

/-- Blueprint: def:X_gamma.  Real-valued `X_γ` norm (`= ‖r‖_{X_γ}` when `r ∈ X_γ`). -/
def xNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p γ : ℝ) (r : ℝ → E) : ℝ :=
  (X_gamma_norm p γ r).toReal

/-- Blueprint: def:Y_gamma.  The `Y_γ` norm (in `[0,∞]`):
`ess sup_{y≥0} ⟨y⟩^γ(|G| + ⟨y⟩^{-1/p}|G'|) + ess sup_{y≤0} ⟨y⟩^γ(|G| + ⟨y⟩|G'|)`. -/
def Y_gamma_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p γ : ℝ) (G : ℝ → E) :
    ℝ≥0∞ :=
  essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖)))
      (volume.restrict (Ici 0)) +
  essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖)))
      (volume.restrict (Iic 0))

/-- Blueprint: def:Y_gamma.  `Y_γ = {G ∈ W^{1,∞}_loc : ‖G‖_{Y_γ} < ∞}` (real-valued). -/
def Y_gamma (p γ : ℝ) : Set (ℝ → ℝ) := {G | W1inftyLoc G ∧ Y_gamma_norm p γ G < ⊤}

/-- Blueprint: def:Y_gamma.  Complex-valued version `Y_γ^ℂ` (chapter 08). -/
def Y_gammaC (p γ : ℝ) : Set (ℝ → ℂ) := {G | W1inftyLoc G ∧ Y_gamma_norm p γ G < ⊤}

/-- Blueprint: def:Y_gamma.  Real-valued `Y_γ` norm. -/
def yNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p γ : ℝ) (G : ℝ → E) : ℝ :=
  (Y_gamma_norm p γ G).toReal

/-! ### The functional `ℓ` -/

/-- Blueprint: def:ell.  `ℓ(G) = lim_{R→∞} ∫₀^R ξ e^{iΦ₀(ξ)} Ĝ(ξ) dξ` (Mathlib `limUnder`; a junk
value if the limit does not exist — existence is prop:linear_ell_continuity). -/
def ell (p : ℝ) (G : ℝ → ℝ) : ℂ :=
  limUnder atTop (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
    (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ)

/-- Blueprint: def:ell (and def:T_0).  `Ỹ_γ = {G ∈ Y_γ : ℓ(G) = 0}`. -/
def Y_gamma_tilde (p γ : ℝ) : Set (ℝ → ℝ) := {G | G ∈ Y_gamma p γ ∧ ell p G = 0}

/-! ### `μ_*`, `G_±`, `G_μ`, `Π` -/

/-- Blueprint: def:mu_star.  `μ_* = -i/√(2πp)`. -/
def mu_star (p : ℝ) : ℂ := -Complex.I / ((Real.sqrt (2 * π * p) : ℝ) : ℂ)

/-- Blueprint: def:G_pm, def:G_mu.  For `s ∈ ℂ`, the Hermitian symbol
`ĝ_s(ξ) = s χ₊'(ξ)/ξ · e^{-iΦ₀(ξ)}` for `ξ ≥ 0`, `ĝ_s(ξ) = conj(ĝ_s(-ξ))` for `ξ < 0`. -/
def G_pm_hat (p : ℝ) (s : ℂ) (ξ : ℝ) : ℂ :=
  if 0 ≤ ξ then s * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))
  else (starRingEnd ℂ) (s * ((deriv chiPlus (-ξ) / (-ξ) : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (Phi0 p (-ξ) : ℂ))))

/-- Blueprint: def:G_pm, def:G_mu.  The (real) inverse Fourier transform of `G_pm_hat p s`.
Encoding: `G_±, G_μ` are real-valued (lem:c02_G_pm_properties); the real part is taken directly,
which is the same function by that lemma, so that `G_±, G_μ` live in the real spaces `Y_γ`. -/
def G_pm_of (p : ℝ) (s : ℂ) (y : ℝ) : ℝ := (invFourierT (G_pm_hat p s) y).re

/-- Blueprint: def:G_pm.  `G₊` (symbol `χ₊'(ξ)/ξ · e^{-iΦ₀(ξ)}` on `ξ ≥ 0`). -/
def G_plus (p : ℝ) : ℝ → ℝ := G_pm_of p 1

/-- Blueprint: def:G_pm.  `G₋` (symbol `i χ₊'(ξ)/ξ · e^{-iΦ₀(ξ)}` on `ξ ≥ 0`). -/
def G_minus (p : ℝ) : ℝ → ℝ := G_pm_of p Complex.I

/-- Blueprint: def:G_mu.  `G_μ` (symbol `(1 - μ/μ_*) χ₊'(ξ)/ξ · e^{-iΦ₀(ξ)}` on `ξ ≥ 0`). -/
def G_mu (p : ℝ) (μ : ℂ) : ℝ → ℝ := G_pm_of p (1 - μ / mu_star p)

/-- Blueprint: def:Pi_projection.  `Π G = G - Re ℓ(G) G₊ - Im ℓ(G) G₋`. -/
def Pi_projection (p : ℝ) (G : ℝ → ℝ) (y : ℝ) : ℝ :=
  G y - (ell p G).re * G_plus p y - (ell p G).im * G_minus p y

end GSQG
