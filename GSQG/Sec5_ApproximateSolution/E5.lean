import GSQG.Definitions
import GSQG.Sec1_Introduction.SelfSimilarReduction
import GSQG.Sec4_Analysis.Equation
import GSQG.AppendixAB.Statements
import GSQG.Sec5_ApproximateSolution.FamilyAndE1toE4

/-!
# §5.8: control of `ℰ₅` (blueprint ch. 05)

Statements and proofs of every node of `blueprint/src/chapters/05_E5.tex` (fully proved; no `sorry`).

Conventions specific to this chapter.
* The standing data `(p, ε₀, δ)` of def:c05_standing are the structure `c05_standing`; a
  *parameter tuple* `(ε, μ, R, Y)` is `c05_standing_tuple S R₀ ε μ R Y`.
* The threshold `R₀` of def:c05_standing ("so large that (R1)–(R3) hold") refers to estimates of
  other chapters (lem:approx_linear_seed, lem:approx_phase_differences).  It is not a field of
  `c05_standing`: every statement begins with `∃ R₀ ≥ 1` (depending only on the standing data,
  since it is chosen before `ε, μ, R, Y, y`), followed by the admissible constant `∃ C > 0`.
  As all statements are monotone in `R₀`, a common `R₀` for the chapter is the maximum.
* Admissible constants depend only on `S` (i.e. on `p, ε₀, δ`; `c_α = calpha p`, `χ₊`, `χ_R`,
  `χ_Y` and hence the `K_j` are fixed functions of `GSQG/Definitions`) and, where indicated, on `k`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal

noncomputable section

namespace GSQG

/-! ### Standing hypotheses and notation (def:c05_standing) -/

/-- Helper: the smallness threshold
`ε₀*(δ)` for `ε`: the minimum of the `ε₀`'s provided (for the given `δ ≤ |μ_*|/2`) by the chapter 04
results used in this chapter (lem:c04_lambda_psi_difference, lem:c04_Z_bounds,
lem:c04_Z_difference_products, lem:c04_Z_difference, lem:c04_lambda_taylor, lem:c04_Z_primitive,
lem:c04_phase_exponential_difference, lem:approx_phase_differences); `1` if the data are out of
range (never used). -/
def c05_eps0_star (p δ : ℝ) : ℝ :=
  if h : 3 / 4 < p ∧ p < 1 ∧ 0 < δ ∧ δ ≤ ‖mu_star p‖ / 2 then
    min (Classical.choose (c04_lambda_psi_difference p h.1 h.2.1 δ h.2.2.1 h.2.2.2))
    (min (Classical.choose (c04_Z_bounds p h.1 h.2.1 δ h.2.2.1 h.2.2.2))
    (min (Classical.choose (c04_Z_difference_products p h.1 h.2.1 δ h.2.2.1 h.2.2.2))
    (min (Classical.choose (c04_Z_difference p h.1 h.2.1 δ h.2.2.1 h.2.2.2))
    (min (Classical.choose (c04_lambda_taylor p h.1 h.2.1 δ h.2.2.1 h.2.2.2))
    (min (Classical.choose (c04_Z_primitive p h.1 h.2.1 δ h.2.2.1 h.2.2.2))
    (min (Classical.choose (c04_phase_exponential_difference p h.1 h.2.1 δ h.2.2.1 h.2.2.2))
      (Classical.choose (approx_phase_differences p h.1 h.2.1 δ h.2.2.1 h.2.2.2))))))))
  else 1

-- The fields `hδ_le : δ ≤ ‖μ_*‖/2` and `hε₀_small : ε₀ ≤ c05_eps0_star p δ` are the ranges in
-- which the chapter 04 results used here (lem:c04_Z_difference, lem:c04_Z_bounds, ...,
-- lem:approx_phase_differences) hold: `δ ≤ |μ_*|/2` and `ε ∈ [0, ε₀(δ)]` with a small `ε₀(δ)`
-- (as for `c06_eps0_star` in §§5.9–5.12).
/-- Blueprint: def:c05_standing.  The standing data of the chapter: `p ∈ (3/4,1)`,
`ε₀ ∈ (0,1]`, `δ > 0` (`μ_* = mu_star p`, `B̄ = Bbar p δ`, the cutoffs `χ₊`, `χ_R`, `χ_Y` are the
fixed functions of `GSQG/Definitions`).
The threshold `R₀` is not a field (see the module docstring): each statement
of the chapter asserts the existence of a suitable `R₀`. -/
structure c05_standing where
  /-- `p = α - 1`. -/
  p : ℝ
  /-- the maximal `ε`. -/
  ε₀ : ℝ
  /-- the radius of `B̄(μ_*, δ)`. -/
  δ : ℝ
  hp_lo : 3 / 4 < p
  hp_hi : p < 1
  hε₀_pos : 0 < ε₀
  hε₀_le : ε₀ ≤ 1
  hδ : 0 < δ
  /-- `δ ≤ |μ_*|/2` (as in chapter 04). -/
  hδ_le : δ ≤ ‖mu_star p‖ / 2
  /-- `ε₀ ≤ ε₀*(δ)`, the smallness threshold of chapter 04. -/
  hε₀_small : ε₀ ≤ c05_eps0_star p δ

/-- Blueprint: def:c05_standing.  A parameter tuple `(ε, μ, R, Y)` (for the threshold `R₀`):
`ε ∈ [0, ε₀]`, `μ ∈ B̄`, `R ≥ R₀`, `Y ≥ 8R`. -/
def c05_standing_tuple (S : c05_standing) (R₀ ε : ℝ) (μ : ℂ) (R Y : ℝ) : Prop :=
  0 ≤ ε ∧ ε ≤ S.ε₀ ∧ μ ∈ Bbar S.p S.δ ∧ R₀ ≤ R ∧ 8 * R ≤ Y

/-- Blueprint: def:c05_standing.  `Φ = Ψ_{ε,μ} - π/4`. -/
def c05_standing_Phi (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ := fam_Psi p R ε μ y - π / 4

/-- Blueprint: def:c05_standing.  `Φ₀ = Ψ₀ - π/4` (not to be confused with the shared `Phi0`). -/
def c05_standing_Phi_zero (p y : ℝ) : ℝ := Psi0 p y - π / 4

/-- Blueprint: def:c05_standing.  `A = μ a_* λ^{-(p+1)/2}`, so that `Z = A e^{iΦ}`. -/
def c05_standing_A (p ε : ℝ) (μ : ℂ) (y : ℝ) : ℂ :=
  μ * astar p y * ((fam_lambda p ε μ y ^ (-(p + 1) / 2) : ℝ) : ℂ)

/-- Blueprint: def:c05_standing.  `A₀ = μ a_* λ₀^{-(p+1)/2}`, so that `(μ/μ_*) Z₀ = A₀ e^{iΦ₀}`. -/
def c05_standing_A_zero (p : ℝ) (μ : ℂ) (y : ℝ) : ℂ :=
  μ * astar p y * ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ)

/-- Blueprint: def:c05_standing.  The function `(μ/μ_*) Z₀`. -/
def c05_standing_Zmu0 (p R : ℝ) (μ : ℂ) (y : ℝ) : ℂ := μ / mu_star p * fam_Z0 p R y

/-! ### Chapter-local definitions -/

/-- Blueprint: def:c05_E5_remainders.  The fundamental part
`f_{osc,1}(y) = -2χ_R(y) Re ∫_y^∞ (Z - (μ/μ_*)Z₀) dt` for `y > R`, `0` for `y ≤ R`. -/
def c05_E5_remainders_fosc1 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  if R < y then
    -2 * fam_chiR R y * (∫ t in Ioi y, (fam_Z p R ε μ t - c05_standing_Zmu0 p R μ t)).re
  else 0

/-- Blueprint: def:c05_E5_remainders.  The third-harmonic part
`f_{osc,3}(y) = -2c_cubic χ_R(y) Re ∫_y^∞ Z³ dt` for `y > R`, `0` for `y ≤ R`. -/
def c05_E5_remainders_fosc3 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  if R < y then
    -2 * c_cubic p ε * fam_chiR R y * (∫ t in Ioi y, fam_Z p R ε μ t ^ 3).re
  else 0

/-- Blueprint: def:c05_E5_remainders.
`ℛ_lin = ℒ₀(f_osc) - 2(λ^p - y) Re Z - 2c_cubic(3^p λ^p - y) Re(Z³)` (used for `y > 2R`). -/
def c05_E5_remainders_Rlin (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  L0 p (fam_osc p R ε μ) y - 2 * (fam_lambda p ε μ y ^ p - y) * (fam_Z p R ε μ y).re -
    2 * c_cubic p ε * ((3 : ℝ) ^ p * fam_lambda p ε μ y ^ p - y) * (fam_Z p R ε μ y ^ 3).re

/-- Blueprint: def:c05_E5_remainders.
`ℛ_cub = 𝒬_{ε,3}(v_Y) - 2n_ε λ^p |Z|² Re Z + 2c_cubic(3^p - 1) λ^p Re(Z³)` (used for `y > 2R`). -/
def c05_E5_remainders_Rcub (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℝ :=
  c04_cubic_part p ε (res_vY p R ε μ Y) y -
    2 * n_eps p ε * fam_lambda p ε μ y ^ p * ‖fam_Z p R ε μ y‖ ^ 2 * (fam_Z p R ε μ y).re +
    2 * c_cubic p ε * ((3 : ℝ) ^ p - 1) * fam_lambda p ε μ y ^ p * (fam_Z p R ε μ y ^ 3).re

/-- Blueprint: def:c05_E5_remainders.
`ℛ_{lin,1} = |D|^p f_{osc,1}' + f_{osc,1} - 2λ^p Re Z + 2y Re((μ/μ_*)Z₀)`. -/
def c05_E5_remainders_Rlin1 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  fracDdy p (c05_E5_remainders_fosc1 p R ε μ) y + c05_E5_remainders_fosc1 p R ε μ y -
    2 * fam_lambda p ε μ y ^ p * (fam_Z p R ε μ y).re + 2 * y * (c05_standing_Zmu0 p R μ y).re

/-- Blueprint: def:c05_E5_remainders.
`ℛ_{lin,3} = |D|^p f_{osc,3}' + f_{osc,3} - 2c_cubic 3^p λ^p Re(Z³)`. -/
def c05_E5_remainders_Rlin3 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  fracDdy p (c05_E5_remainders_fosc3 p R ε μ) y + c05_E5_remainders_fosc3 p R ε μ y -
    2 * c_cubic p ε * (3 : ℝ) ^ p * fam_lambda p ε μ y ^ p * (fam_Z p R ε μ y ^ 3).re

/-- Blueprint: def:c05_E5_remainders.  The two components `(ℛ_lin(y), ℛ_cub(y))` of `ℰ₅`
(the individual pieces are `c05_E5_remainders_fosc1/_fosc3/_Rlin/_Rcub/_Rlin1/_Rlin3`). -/
def c05_E5_remainders (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℝ × ℝ :=
  (c05_E5_remainders_Rlin p R ε μ y, c05_E5_remainders_Rcub p R ε μ Y y)

/-- Blueprint: def:c05_auxiliary_remainders.  The far remainder
`ℛ_{far,Y}[g](y) = c_α ∫ g(z) ∂_z[(1-χ_Y(z))/|y-z|^{1+p}] dz` (used for `y ∈ (Y/2,3Y)`). -/
def c05_auxiliary_remainders_Rfar (p Y : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, g z * deriv (fun z' => (1 - res_chiY Y z') / |y - z'| ^ (1 + p)) z

/-- Blueprint: def:c05_auxiliary_remainders.
`ℰ_mult = |D|^p(χ_Y Z) - [λ^p Z + i (λ^p)'/λ · Z - ipμ a_*' λ^{(p-3)/2} e^{iΦ}]`
(used for `y ∈ (Y/2,3Y)`). -/
def c05_auxiliary_remainders_Emult (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℂ :=
  fracDC p (fun z => (res_chiY Y z : ℂ) * fam_Z p R ε μ z) y -
    (((fam_lambda p ε μ y ^ p : ℝ) : ℂ) * fam_Z p R ε μ y +
      Complex.I * ((deriv (fun t => fam_lambda p ε μ t ^ p) y / fam_lambda p ε μ y : ℝ) : ℂ) *
        fam_Z p R ε μ y -
      Complex.I * p * μ * deriv (astar p) y * ((fam_lambda p ε μ y ^ ((p - 3) / 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c05_standing_Phi p R ε μ y : ℂ)))

/-- Blueprint: def:c05_auxiliary_remainders.
`ℰ_{mult,0} = |D|^p(χ_Y (μ/μ_*)Z₀) - [y (μ/μ_*)Z₀ + (i/λ₀)(μ/μ_*)Z₀ - ipμ a_*' λ₀^{(p-3)/2} e^{iΦ₀}]`. -/
def c05_auxiliary_remainders_Emult0 (p R : ℝ) (μ : ℂ) (Y y : ℝ) : ℂ :=
  fracDC p (fun z => (res_chiY Y z : ℂ) * c05_standing_Zmu0 p R μ z) y -
    ((y : ℂ) * c05_standing_Zmu0 p R μ y +
      Complex.I / (lambda0 p y : ℂ) * c05_standing_Zmu0 p R μ y -
      Complex.I * p * μ * deriv (astar p) y * ((lambda0 p y ^ ((p - 3) / 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c05_standing_Phi_zero p y : ℂ)))

/-- Blueprint: def:c05_auxiliary_remainders.  The primitive remainder
`ℛ_prim(y) = 2 Re ∫_y^∞ [e^{iΦ} ∂_s(A/(iλ)) - e^{iΦ₀} ∂_s(A₀/(iλ₀))] ds` (used for `y ≥ R`). -/
def c05_auxiliary_remainders_Rprim (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  2 * (∫ s in Ioi y,
    (Complex.exp (Complex.I * (c05_standing_Phi p R ε μ s : ℂ)) *
        deriv (fun t => c05_standing_A p ε μ t / (Complex.I * (fam_lambda p ε μ t : ℂ))) s -
      Complex.exp (Complex.I * (c05_standing_Phi_zero p s : ℂ)) *
        deriv (fun t => c05_standing_A_zero p μ t / (Complex.I * (lambda0 p t : ℂ))) s)).re

/-- Blueprint: def:c05_auxiliary_remainders.  The triple `(ℰ_mult(y), ℰ_{mult,0}(y), ℛ_prim(y))`
(with `ℛ_{far,Y}` = `c05_auxiliary_remainders_Rfar`). -/
def c05_auxiliary_remainders (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) : ℂ × ℂ × ℝ :=
  (c05_auxiliary_remainders_Emult p R ε μ Y y, c05_auxiliary_remainders_Emult0 p R μ Y y,
    c05_auxiliary_remainders_Rprim p R ε μ y)

/-- Blueprint: def:c05_plane_wave.  The frozen plane wave
`P_y(z) = 2 Re[Z(y)/(iλ) e^{iλ(z-y)}]`, `λ = λ(y)` (used for `y ≥ R`). -/
def c05_plane_wave (p R ε : ℝ) (μ : ℂ) (y z : ℝ) : ℝ :=
  2 * (fam_Z p R ε μ y / (Complex.I * (fam_lambda p ε μ y : ℂ)) *
    Complex.exp (Complex.I * ((fam_lambda p ε μ y * (z - y) : ℝ) : ℂ))).re

/-- Blueprint: def:c05_plane_wave.  The increment `Δh(y,s) = h(y) - h(y-s)`. -/
def c05_plane_wave_Delta (h : ℝ → ℝ) (y s : ℝ) : ℝ := h y - h (y - s)

/-- Blueprint: def:c05_plane_wave.  `K_ε = -(p+1)εc_α/2`. -/
def c05_plane_wave_K (p ε : ℝ) : ℝ := -((p + 1) * ε * calpha p) / 2

/-- Blueprint: def:c05_plane_wave.
`N₀(y,s) = Δv_Y'(Δv_Y)² - ΔP_y'(ΔP_y)²` (increments at the base point `y`). -/
def c05_plane_wave_N0 (p R ε : ℝ) (μ : ℂ) (Y y s : ℝ) : ℝ :=
  c05_plane_wave_Delta (deriv (res_vY p R ε μ Y)) y s *
      c05_plane_wave_Delta (res_vY p R ε μ Y) y s ^ 2 -
    c05_plane_wave_Delta (deriv (c05_plane_wave p R ε μ y)) y s *
      c05_plane_wave_Delta (c05_plane_wave p R ε μ y) y s ^ 2

/-- Blueprint: def:c05_plane_wave.
`N₁(y,s) = [Δv_Y''(Δv_Y)² - ΔP_y''(ΔP_y)²] + 2[(Δv_Y')²Δv_Y - (ΔP_y')²ΔP_y]`. -/
def c05_plane_wave_N1 (p R ε : ℝ) (μ : ℂ) (Y y s : ℝ) : ℝ :=
  (c05_plane_wave_Delta (deriv (deriv (res_vY p R ε μ Y))) y s *
      c05_plane_wave_Delta (res_vY p R ε μ Y) y s ^ 2 -
    c05_plane_wave_Delta (deriv (deriv (c05_plane_wave p R ε μ y))) y s *
      c05_plane_wave_Delta (c05_plane_wave p R ε μ y) y s ^ 2) +
  2 * (c05_plane_wave_Delta (deriv (res_vY p R ε μ Y)) y s ^ 2 *
      c05_plane_wave_Delta (res_vY p R ε μ Y) y s -
    c05_plane_wave_Delta (deriv (c05_plane_wave p R ε μ y)) y s ^ 2 *
      c05_plane_wave_Delta (c05_plane_wave p R ε μ y) y s)

/-- Blueprint: def:c05_plane_wave.
`G(y) = 2n_ε λ^p |Z|² Re Z - 2c_cubic(3^p - 1) λ^p Re(Z³)`. -/
def c05_plane_wave_G (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  2 * n_eps p ε * fam_lambda p ε μ y ^ p * ‖fam_Z p R ε μ y‖ ^ 2 * (fam_Z p R ε μ y).re -
    2 * c_cubic p ε * ((3 : ℝ) ^ p - 1) * fam_lambda p ε μ y ^ p * (fam_Z p R ε μ y ^ 3).re

/-- Blueprint: def:c05_plane_wave.  `T_P(y) = ∂_z[𝒬_{ε,3}(P_y)(z)]_{z=y}` (`y` fixed in `P_y`). -/
def c05_plane_wave_TP (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  deriv (fun z => c04_cubic_part p ε (c05_plane_wave p R ε μ y) z) y

/-- Helper for lem:c05_multiplier_fundamental (the remainder `ℛ̃_{mult,2}[a,Ψ]` of
eqn:appendix_oscillatory_multiplier_two_term_expansion, chapter 03), defined by that expansion:
`ℛ̃ = e^{-iΨ}|D|^p(a e^{iΨ}) - [λ^p a - ipλ^{p-1}a' - (ip(p-1)/2) λ^{p-2} λ' a]`, `λ = Ψ'`.
It is expressed here through its defining identity. -/
def c05_multiplier_fundamental_Rtilde (p : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (y : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (Ψ y : ℂ))) * fracDC p (fun z => a z * Complex.exp (Complex.I * (Ψ z : ℂ))) y -
    (((deriv Ψ y ^ p : ℝ) : ℂ) * a y - Complex.I * p * ((deriv Ψ y ^ (p - 1) : ℝ) : ℂ) * deriv a y -
      Complex.I * (p * (p - 1) / 2 : ℝ) * ((deriv Ψ y ^ (p - 2) : ℝ) : ℂ) *
        ((deriv (deriv Ψ) y : ℝ) : ℂ) * a y)

/-- Helper for lem:c05_fundamental_explicit.  `T₁ = i((λ^p)' - 1) Z/λ`. -/
def c05_fundamental_explicit_T1 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℂ :=
  Complex.I * ((deriv (fun t => fam_lambda p ε μ t ^ p) y - 1 : ℝ) : ℂ) * fam_Z p R ε μ y /
    (fam_lambda p ε μ y : ℂ)

/-- Helper for lem:c05_fundamental_explicit.
`T₂ = -ipμ a_*' (λ^{(p-3)/2} e^{iΦ} - λ₀^{(p-3)/2} e^{iΦ₀})`. -/
def c05_fundamental_explicit_T2 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℂ :=
  -(Complex.I * p * μ * deriv (astar p) y *
    (((fam_lambda p ε μ y ^ ((p - 3) / 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c05_standing_Phi p R ε μ y : ℂ)) -
      ((lambda0 p y ^ ((p - 3) / 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c05_standing_Phi_zero p y : ℂ))))

/-! ### Elementary helpers -/

/-- Helper: parameter tuples are monotone in the threshold `R₀`. -/
theorem c05_aux_tuple_mono {S : c05_standing} {R₁ R₂ ε : ℝ} {μ : ℂ} {R Y : ℝ} (h : R₁ ≤ R₂)
    (ht : c05_standing_tuple S R₂ ε μ R Y) : c05_standing_tuple S R₁ ε μ R Y :=
  ⟨ht.1, ht.2.1, ht.2.2.1, h.trans ht.2.2.2.1, ht.2.2.2.2⟩

/-- Helper: `Y ≤ ⟨y⟩ ≤ 3Y` for `y ∈ [Y,2Y]`, `Y ≥ 1`. -/
theorem c05_aux_jb_bounds {Y y : ℝ} (hY : 1 ≤ Y) (hy : y ∈ Icc Y (2 * Y)) :
    Y ≤ jb y ∧ jb y ≤ 3 * Y := by
  obtain ⟨h1, h2⟩ := hy
  have hy0 : 0 ≤ y := by linarith
  constructor
  · unfold jb
    calc Y ≤ y := h1
      _ = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy0).symm
      _ ≤ Real.sqrt (1 + y ^ 2) := Real.sqrt_le_sqrt (by linarith)
  · unfold jb
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith

/-- Helper: `Y^θ ≤ 3^T ⟨y⟩^θ` for `y ∈ [Y,2Y]`, `Y ≥ 1`, `|θ| ≤ T`. -/
theorem c05_aux_rpow_Y_jb {Y y θ T : ℝ} (hY : 1 ≤ Y) (hy : y ∈ Icc Y (2 * Y)) (hθ : |θ| ≤ T) :
    Y ^ θ ≤ 3 ^ T * jb y ^ θ := by
  obtain ⟨hj1, hj2⟩ := c05_aux_jb_bounds hY hy
  have hY0 : 0 < Y := by linarith
  have hjb0 : 0 < jb y := by linarith
  rcases le_or_gt 0 θ with h | h
  · calc Y ^ θ ≤ jb y ^ θ := Real.rpow_le_rpow hY0.le hj1 h
      _ = 1 * jb y ^ θ := (one_mul _).symm
      _ ≤ 3 ^ T * jb y ^ θ := by
        gcongr
        exact Real.one_le_rpow (by norm_num) ((abs_nonneg θ).trans hθ)
  · have h3 : jb y / 3 ≤ Y := by linarith
    calc Y ^ θ ≤ (jb y / 3) ^ θ := Real.rpow_le_rpow_of_nonpos (by positivity) h3 h.le
      _ = 3 ^ (-θ) * jb y ^ θ := by
        rw [Real.div_rpow hjb0.le (by norm_num), Real.rpow_neg (by norm_num)]
        ring
      _ ≤ 3 ^ T * jb y ^ θ := by
        gcongr
        · norm_num
        · rw [abs_of_neg h] at hθ; exact hθ

/-- Helper: splitting a nonnegative integral at `|s| = L` (the two regions overlap). -/
theorem c05_aux_integral_split (g : ℝ → ℝ) (hg : Integrable g) (hg0 : ∀ s, 0 ≤ g s) (L : ℝ) :
    ∫ s, g s ≤ (∫ s in {s : ℝ | |s| ≤ L}, g s) + ∫ s in {s : ℝ | L ≤ |s|}, g s := by
  have hmeas : MeasurableSet {s : ℝ | |s| ≤ L} :=
    measurableSet_le continuous_abs.measurable measurable_const
  rw [← integral_add_compl hmeas hg]
  refine add_le_add le_rfl (setIntegral_mono_set hg.integrableOn
    (Filter.Eventually.of_forall hg0) ?_)
  refine Filter.Eventually.of_forall fun s hs => ?_
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hs
  exact (le_of_lt hs : L ≤ |s|)

/-- Helper: `|K ∫ |s|^r N| ≤ |K| (∫_{|s|≤L} |s|^r |N| + ∫_{|s|≥L} |s|^r |N|)`. -/
theorem c05_aux_kernel_split (K r L : ℝ) (N : ℝ → ℝ) (hN : Integrable (fun s => |s| ^ r * N s)) :
    |K * ∫ s, |s| ^ r * N s| ≤
      |K| * (∫ s in {s : ℝ | |s| ≤ L}, |s| ^ r * |N s|) +
        |K| * ∫ s in {s : ℝ | L ≤ |s|}, |s| ^ r * |N s| := by
  have heq : (fun s => |s| ^ r * |N s|) = fun s => |(|s| ^ r * N s)| := by
    funext s; rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg s) r)]
  have hint : Integrable (fun s => |s| ^ r * |N s|) := by rw [heq]; exact hN.abs
  rw [abs_mul, ← mul_add]
  gcongr
  calc |∫ s, |s| ^ r * N s| ≤ ∫ s, |(|s| ^ r * N s)| := abs_integral_le_integral_abs
    _ = ∫ s, |s| ^ r * |N s| := by rw [heq]
    _ ≤ _ := c05_aux_integral_split _ hint
          (fun s => mul_nonneg (Real.rpow_nonneg (abs_nonneg s) r) (abs_nonneg _)) L

/-- Helper: `2 + 2p ≤ 5β` for `p ∈ (0,1)`, i.e. `1 - 5β ≤ -2p - 1`. -/
theorem c05_aux_five_beta (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : 2 + 2 * p ≤ 5 * beta p := by
  unfold beta
  rw [show 5 * ((p + 1) / (2 * p)) = 5 * (p + 1) / (2 * p) by ring, le_div_iff₀ (by linarith)]
  nlinarith

/-- Projection (integrability part) of chapter 01's lem:c01_frac_well_defined
(`GSQG.c01_frac_well_defined`): for `g` bounded and Lipschitz on `[y-1,y+1]` the integrand of
`|D|^p g(y)` is integrable.  Proved from the chapter-01 result. -/
theorem c05_aux_frac_well_defined (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ)
    (hgm : AEStronglyMeasurable g volume) (M : ℝ) (hM : ∀ᵐ z, |g z| ≤ M) (y Λ : ℝ)
    (hΛ : 0 ≤ Λ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1), |g z - g w| ≤ Λ * |z - w|) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) :=
  (c01_frac_well_defined p hp hp1 g hgm M hM y Λ hΛ hLip).1

/-- Helper: for a bounded `C¹` function the integrand of `|D|^p g(y)` is integrable. -/
theorem c05_aux_fracD_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ)
    (hg : ContDiff ℝ 1 g) (hb : ∃ M : ℝ, ∀ x, |g x| ≤ M) (y : ℝ) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) := by
  obtain ⟨M, hM⟩ := hb
  have hcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  obtain ⟨Λ, hΛ⟩ := (isCompact_Icc (a := y - 1) (b := y + 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine c05_aux_frac_well_defined p hp hp1 g hg.continuous.aestronglyMeasurable M
    (Filter.Eventually.of_forall hM) y (max Λ 0) (le_max_right _ _) ?_
  intro z hz w hw
  have := (convex_Icc (y - 1) (y + 1)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hdiff x) (fun x hx => (hΛ x hx).trans (le_max_left Λ 0)) hw hz
  simpa [Real.norm_eq_abs] using this

/-- Helper: additivity of `|D|^p` on bounded `C¹` functions. -/
theorem c05_aux_fracD_add (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g₁ g₂ : ℝ → ℝ)
    (h1 : ContDiff ℝ 1 g₁) (h2 : ContDiff ℝ 1 g₂) (hb1 : ∃ M : ℝ, ∀ x, |g₁ x| ≤ M)
    (hb2 : ∃ M : ℝ, ∀ x, |g₂ x| ≤ M) (y : ℝ) :
    fracD p (fun z => g₁ z + g₂ z) y = fracD p g₁ y + fracD p g₂ y := by
  unfold fracD
  rw [← mul_add, ← integral_add (c05_aux_fracD_integrable p hp hp1 g₁ h1 hb1 y)
    (c05_aux_fracD_integrable p hp hp1 g₂ h2 hb2 y)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

/-! ### Regularity helpers -/

/-- Projection (part) of chapter 04's lem:c04_seed_decomposition
(`GSQG.c04_seed_decomposition`): `f_{0,+}` is smooth.  Proved from the chapter-04 result. -/
theorem c05_aux_seed_plus_smooth (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p) :=
  (c04_seed_decomposition p hp hp1).2.2.1

/-- Helper: smoothness of the complexification of a real function. -/
theorem c05_aux_ofReal {f : ℝ → ℝ} {y : ℝ} {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f y) :
    ContDiffAt ℝ n (fun t => (f t : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y hf

/-- Helper: `t ↦ t^r` is smooth at `y > 0`. -/
theorem c05_aux_rpow_at {r y : ℝ} {n : WithTop ℕ∞} (hy : 0 < y) :
    ContDiffAt ℝ n (fun t : ℝ => t ^ r) y :=
  contDiffAt_rpow_const_of_ne hy.ne'

/-- Helper: `μ_* ≠ 0`. -/
theorem c05_aux_mu_star_ne (p : ℝ) (hp : 0 < p) : mu_star p ≠ 0 := by
  unfold mu_star
  apply div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
  exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'

/-- Helper: `λ_{ε,μ}` is smooth on `(0,∞)`. -/
theorem c05_aux_lambda_smooth (p ε : ℝ) (μ : ℂ) {y : ℝ} (hy : 0 < y) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fam_lambda p ε μ) y := by
  unfold fam_lambda
  exact ((c05_aux_rpow_at hy).add (contDiffAt_const.mul (c05_aux_rpow_at hy))).add
    (contDiffAt_const.div contDiffAt_id hy.ne')

/-- Helper: `λ_{ε,μ}` is continuous on `(0,∞)`. -/
theorem c05_aux_lambda_cont (p ε : ℝ) (μ : ℂ) : ContinuousOn (fam_lambda p ε μ) (Ioi 0) :=
  fun _ hy => (c05_aux_lambda_smooth p ε μ (n := 0) hy).continuousAt.continuousWithinAt

/-- Helper: `Ψ_{ε,μ}' = λ_{ε,μ}` on `(0,∞)` (for `R > 0`). -/
theorem c05_aux_Psi_hasDeriv (p R ε : ℝ) (μ : ℂ) (hR : 0 < R) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fam_Psi p R ε μ) (fam_lambda p ε μ y) y := by
  unfold fam_Psi
  have hsub : uIcc R y ⊆ Ioi 0 := by
    intro t ht
    rcases ht with ⟨h1, -⟩
    exact lt_of_lt_of_le (lt_min hR hy) h1
  have hii : IntervalIntegrable (fam_lambda p ε μ) volume R y :=
    ((c05_aux_lambda_cont p ε μ).mono hsub).intervalIntegrable
  have := intervalIntegral.integral_hasDerivAt_right hii
    ((c05_aux_lambda_cont p ε μ).stronglyMeasurableAtFilter isOpen_Ioi y hy)
    (c05_aux_lambda_smooth p ε μ (n := 0) hy).continuousAt
  exact this.const_add _

/-- Helper: `Ψ_{ε,μ}` is smooth on `(0,∞)` (for `R > 0`). -/
theorem c05_aux_Psi_smooth (p R ε : ℝ) (μ : ℂ) (hR : 0 < R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fam_Psi p R ε μ) (Ioi 0) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun y hy => (c05_aux_Psi_hasDeriv p R ε μ hR hy).differentiableAt.differentiableWithinAt,
    ?_⟩
  refine ContDiffOn.congr (f := fam_lambda p ε μ) (fun y hy => ?_) (fun y hy => ?_)
  · exact (c05_aux_lambda_smooth p ε μ hy).contDiffWithinAt
  · exact (c05_aux_Psi_hasDeriv p R ε μ hR hy).deriv

/-- Helper: `a_*` is smooth on `(0,∞)`. -/
theorem c05_aux_astar_smooth (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) {y : ℝ} (hy : 0 < y)
    {n : ℕ∞} : ContDiffAt ℝ n (astar p) y := by
  have hp0 : 0 < p := by linarith
  have hseed := c05_aux_seed_plus_smooth p hp hp1
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv (c04_linear_seed_plus p)) :=
    (contDiff_infty_iff_deriv.mp hseed).2
  unfold astar
  have hPsi0 : ContDiffAt ℝ n (fun t => Psi0 p t - π / 4) y := by
    unfold Psi0
    exact (contDiffAt_const.mul (c05_aux_rpow_at hy)).sub contDiffAt_const
  have hl : ContDiffAt ℝ n (fun t => lambda0 p t ^ (-(p + 1) / 2)) y := by
    unfold lambda0
    exact (c05_aux_rpow_at hy).rpow_const_of_ne (Real.rpow_pos_of_pos hy _).ne'
  simp only [div_eq_mul_inv]
  refine ContDiffAt.mul (ContDiffAt.mul ?_ (ContDiffAt.inv ?_ ?_)) ?_
  · exact Complex.contDiff_exp.contDiffAt.comp y
      ((contDiffAt_const.mul (c05_aux_ofReal hPsi0)).neg)
  · exact contDiffAt_const.mul (c05_aux_ofReal hl)
  · refine mul_ne_zero (c05_aux_mu_star_ne p hp0) ?_
    exact_mod_cast (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hy _) _).ne'
  · exact (hd.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt

/-- Helper: `Z_{ε,μ}` is smooth at every `y > 0` where `λ_{ε,μ}(y) ≠ 0`. -/
theorem c05_aux_Z_smooth (p R ε : ℝ) (μ : ℂ) (hp : 3 / 4 < p) (hp1 : p < 1) (hR : 0 < R)
    {y : ℝ} (hy : 0 < y) (hl : fam_lambda p ε μ y ≠ 0) {n : ℕ∞} :
    ContDiffAt ℝ n (fam_Z p R ε μ) y := by
  unfold fam_Z
  refine ContDiffAt.mul (ContDiffAt.mul (contDiffAt_const.mul (c05_aux_astar_smooth p hp hp1 hy))
    (c05_aux_ofReal ((c05_aux_lambda_smooth p ε μ hy).rpow_const_of_ne hl))) ?_
  have hPsi : ContDiffAt ℝ n (fun t => fam_Psi p R ε μ t - π / 4) y :=
    ((((c05_aux_Psi_smooth p R ε μ hR).contDiffAt (isOpen_Ioi.mem_nhds hy)).of_le
      (WithTop.coe_le_coe.mpr le_top)).sub contDiffAt_const)
  exact Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul (c05_aux_ofReal hPsi))

/-- Helper: `λ_{0,μ} = λ₀` (all correction constants vanish at `ε = 0`). -/
theorem c05_aux_lambda_zero (p : ℝ) (μ : ℂ) (y : ℝ) : fam_lambda p 0 μ y = y ^ (1 / p) := by
  have hce : c_eps p 0 = 0 := by
    unfold c_eps A_eps; simp
  have hn : n_eps p 0 = 0 := by
    unfold n_eps cubic_c1 c04_cubic_part c04_cubic_part_kappa; simp
  unfold fam_lambda c_power c_log
  rw [hce, hn]; simp

/-- Helper: `(μ/μ_*) Z₀` is smooth on `(0,∞)` (for `R > 0`). -/
theorem c05_aux_Zmu0_smooth (p R : ℝ) (μ : ℂ) (hp : 3 / 4 < p) (hp1 : p < 1) (hR : 0 < R)
    {y : ℝ} (hy : 0 < y) {n : ℕ∞} : ContDiffAt ℝ n (c05_standing_Zmu0 p R μ) y := by
  unfold c05_standing_Zmu0 fam_Z0
  refine contDiffAt_const.mul (c05_aux_Z_smooth p R 0 (mu_star p) hp hp1 hR hy ?_)
  rw [c05_aux_lambda_zero]; exact (Real.rpow_pos_of_pos hy _).ne'

/-- Helper: the smoothness package of the family on `(R,∞)` (given `λ > 0` there). -/
theorem c05_aux_family_smooth (p R ε : ℝ) (μ : ℂ) (hp : 3 / 4 < p) (hp1 : p < 1) (hR : 0 < R)
    (hpos : ∀ t, R < t → 0 < fam_lambda p ε μ t) {y : ℝ} (hy : R < y) :
    (∀ q : ℝ, ContDiffAt ℝ 2 (fun t => fam_lambda p ε μ t ^ q) y) ∧
    ContDiffAt ℝ 2 (fam_Z p R ε μ) y ∧
    ContDiffAt ℝ 2 (c05_standing_Zmu0 p R μ) y ∧
    ContDiffAt ℝ 1 (deriv (astar p)) y ∧
    ContDiffAt ℝ 1 (deriv (fun t => fam_lambda p ε μ t ^ p)) y ∧
    ContDiffAt ℝ 2 (c05_standing_Phi p R ε μ) y ∧
    ContDiffAt ℝ 2 (c05_standing_Phi_zero p) y ∧
    ContDiffAt ℝ 2 (fam_lambda p ε μ) y ∧
    (∀ q : ℝ, ContDiffAt ℝ 2 (fun t => lambda0 p t ^ q) y) := by
  have hy0 : 0 < y := hR.trans hy
  have hlamq : ∀ q : ℝ, ∀ t, R < t → ContDiffAt ℝ (⊤ : ℕ∞) (fun t => fam_lambda p ε μ t ^ q) t :=
    fun q t ht => (c05_aux_lambda_smooth p ε μ (hR.trans ht)).rpow_const_of_ne (hpos t ht).ne'
  have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun q => (hlamq q y hy).of_le h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact c05_aux_Z_smooth p R ε μ hp hp1 hR hy0 (hpos y hy).ne'
  · exact c05_aux_Zmu0_smooth p R μ hp hp1 hR hy0
  · have hon : ContDiffOn ℝ (⊤ : ℕ∞) (astar p) (Ioi 0) :=
      fun t ht => (c05_aux_astar_smooth p hp hp1 ht).contDiffWithinAt
    have := hon.deriv_of_isOpen isOpen_Ioi (m := (⊤ : ℕ∞)) (by simp)
    exact (this.contDiffAt (Ioi_mem_nhds hy0)).of_le (WithTop.coe_le_coe.mpr le_top)
  · have hon : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => fam_lambda p ε μ t ^ p) (Ioi R) :=
      fun t ht => (hlamq p t ht).contDiffWithinAt
    have := hon.deriv_of_isOpen isOpen_Ioi (m := (⊤ : ℕ∞)) (by simp)
    exact (this.contDiffAt (Ioi_mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  · unfold c05_standing_Phi
    exact ((((c05_aux_Psi_smooth p R ε μ hR).contDiffAt (Ioi_mem_nhds hy0)).of_le h2).sub
      contDiffAt_const)
  · unfold c05_standing_Phi_zero Psi0
    exact (contDiffAt_const.mul (c05_aux_rpow_at hy0)).sub contDiffAt_const
  · exact c05_aux_lambda_smooth p ε μ hy0
  · intro q
    unfold lambda0
    exact (c05_aux_rpow_at hy0).rpow_const_of_ne (Real.rpow_pos_of_pos hy0 _).ne'

/-- Helper: smoothness of the real part. -/
theorem c05_aux_re {f : ℝ → ℂ} {y : ℝ} {n : WithTop ℕ∞} (hf : ContDiffAt ℝ n f y) :
    ContDiffAt ℝ n (fun t => (f t).re) y :=
  Complex.reCLM.contDiff.contDiffAt.comp y hf

/-- Helper: polar form `Z^k e^{ikφ} = |Z|^k e^{i(k arg Z + kφ)}`. -/
theorem c05_aux_polar_exp (Z : ℂ) (k : ℕ) (φ : ℝ) :
    Z ^ k * Complex.exp (k * Complex.I * (φ : ℂ)) =
      ((‖Z‖ ^ k : ℝ) : ℂ) * Complex.exp (((k * Complex.arg Z + k * φ : ℝ)) * Complex.I) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I Z]
  rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-- Helper: `Re(Z^k e^{ikφ}) = |Z|^k cos(k arg Z + kφ)`. -/
theorem c05_aux_polar_re (Z : ℂ) (k : ℕ) (φ : ℝ) :
    (Z ^ k * Complex.exp (k * Complex.I * (φ : ℂ))).re =
      ‖Z‖ ^ k * Real.cos (k * Complex.arg Z + k * φ) := by
  rw [c05_aux_polar_exp, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- Helper: `Im(Z^k) = |Z|^k sin(k arg Z)`. -/
theorem c05_aux_polar_im (Z : ℂ) (k : ℕ) :
    (Z ^ k).im = ‖Z‖ ^ k * Real.sin (k * Complex.arg Z) := by
  have := c05_aux_polar_exp Z k 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, add_zero] at this
  rw [this, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-- Helper: the frozen plane wave is a rescaled sine:
`2Re[Z/(iλ) e^{iλ(z-y)}] = (2|Z|/λ) sin(λz + arg Z - λy)`. -/
theorem c05_aux_plane_wave_sin (Z : ℂ) (lam y z : ℝ) (hl : 0 < lam) :
    2 * (Z / (Complex.I * (lam : ℂ)) * Complex.exp (Complex.I * ((lam * (z - y) : ℝ) : ℂ))).re =
      2 * ‖Z‖ / lam * Real.sin (lam * z + (Complex.arg Z - lam * y)) := by
  have h := c05_aux_polar_exp Z 1 (lam * (z - y))
  simp only [pow_one, Nat.cast_one, one_mul] at h
  have hl' : (lam : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have : Z / (Complex.I * (lam : ℂ)) * Complex.exp (Complex.I * ((lam * (z - y) : ℝ) : ℂ)) =
      -Complex.I * ((lam⁻¹ : ℝ) : ℂ) * (Z * Complex.exp (Complex.I * ((lam * (z - y) : ℝ) : ℂ))) := by
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
  rw [this, h]
  set ψ := Complex.arg Z + lam * (z - y)
  rw [Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_re, Complex.mul_im]
  have : lam * z + (Complex.arg Z - lam * y) = ψ := by simp only [ψ]; ring
  rw [this]
  field_simp
  rw [Complex.sin_ofReal_re]

/-- Helper: `∂_z cos(a + b(z-y))` at `z = y`. -/
theorem c05_aux_hasDerivAt_cos (a b y : ℝ) :
    HasDerivAt (fun z => Real.cos (a + b * (z - y))) (-Real.sin a * b) y := by
  have hlin : HasDerivAt (fun z => a + b * (z - y)) b y := by
    simpa using (((hasDerivAt_id y).sub_const y).const_mul b).const_add a
  have := hlin.cos
  simpa using this

/-- Helper: the annulus cutoff is smooth. -/
theorem c05_aux_chiAnnulus_smooth : ContDiff ℝ (⊤ : ℕ∞) chiAnnulus := by
  unfold chiAnnulus
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

/-- Helper: `χ_Y` is smooth. -/
theorem c05_aux_chiY_smooth (Y : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (res_chiY Y) :=
  c05_aux_chiAnnulus_smooth.comp (contDiff_id.div_const Y)

/-- Helper: `χ_Y = 0` outside `(3Y/10, 7Y/2)`. -/
theorem c05_aux_chiY_zero {Y z : ℝ} (hY : 0 < Y) (hz : z ≤ 3 * Y / 10 ∨ 7 * Y / 2 ≤ z) :
    res_chiY Y z = 0 := by
  unfold res_chiY chiAnnulus
  rcases hz with hz | hz
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    rw [div_nonpos_iff]; right
    refine ⟨?_, by norm_num⟩
    rw [sub_nonpos, div_le_iff₀ hY]; linarith
  · rw [Real.smoothTransition.zero_of_nonpos (x := (7 / 2 - z / Y) / (1 / 2)), mul_zero]
    rw [div_nonpos_iff]; right
    refine ⟨?_, by norm_num⟩
    rw [sub_nonpos, le_div_iff₀ hY]; linarith

/-- Helper: `χ_Y = 1` on `[Y/2, 3Y]`. -/
theorem c05_aux_chiY_one {Y z : ℝ} (hY : 0 < Y) (hz : z ∈ Icc (Y / 2) (3 * Y)) :
    res_chiY Y z = 1 := by
  unfold res_chiY chiAnnulus
  have h1 : Y / 2 / Y ≤ z / Y := div_le_div_of_nonneg_right hz.1 hY.le
  have h2 : z / Y ≤ 3 * Y / Y := div_le_div_of_nonneg_right hz.2 hY.le
  rw [show Y / 2 / Y = 1 / 2 by field_simp] at h1
  rw [show 3 * Y / Y = 3 by field_simp] at h2
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [le_div_iff₀ (by norm_num)]; linarith

/-- Helper: `χ_Y f` is smooth with compact support when `f` is smooth on `(R,∞)`,
`R < 3Y/10`. -/
theorem c05_aux_cutoff_mul {f : ℝ → ℂ} {Y R : ℝ} {n : ℕ∞} (hY : 0 < Y) (hRY : R < 3 * Y / 10)
    (hf : ∀ t, R < t → ContDiffAt ℝ n f t) :
    ContDiff ℝ n (fun z => (res_chiY Y z : ℂ) * f z) ∧
      HasCompactSupport (fun z => (res_chiY Y z : ℂ) * f z) := by
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge R t with h | h
    · refine ContDiffAt.mul ?_ (hf t h)
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp t
        ((c05_aux_chiY_smooth Y).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (show t < 3 * Y / 10 by linarith)] with z hz
      rw [c05_aux_chiY_zero hY (Or.inl (le_of_lt hz))]; simp
  · refine HasCompactSupport.intro (isCompact_Icc (a := 3 * Y / 10) (b := 7 * Y / 2)) ?_
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rw [c05_aux_chiY_zero hY (hx.imp le_of_lt le_of_lt)]; simp

/-- Helper: `|D|^p (Re h) = Re |D|^p h` for bounded `C¹` complex `h`. -/
theorem c05_aux_fracD_re (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (h : ℝ → ℂ) (hh : ContDiff ℝ 1 h)
    (hb : ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M) (y : ℝ) :
    fracD p (fun z => (h z).re) y = (fracDC p h y).re := by
  obtain ⟨M, hM⟩ := hb
  have hre := c05_aux_fracD_integrable p hp hp1 (fun z => (h z).re)
    (Complex.reCLM.contDiff.comp hh) ⟨M, fun x => (Complex.abs_re_le_norm _).trans (hM x)⟩ y
  have him := c05_aux_fracD_integrable p hp hp1 (fun z => (h z).im)
    (Complex.imCLM.contDiff.comp hh) ⟨M, fun x => (Complex.abs_im_le_norm _).trans (hM x)⟩ y
  have hint : Integrable (fun z => (h y - h z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) := by
    rw [← Integrable.re_im_iff]
    constructor
    · refine hre.congr (Filter.Eventually.of_forall fun z => ?_)
      simp [Complex.div_ofReal_re]
    · refine him.congr (Filter.Eventually.of_forall fun z => ?_)
      simp [Complex.div_ofReal_im]
  unfold fracD fracDC
  rw [Complex.re_ofReal_mul]
  congr 1
  rw [← RCLike.re_eq_complex_re, ← integral_re hint]
  congr 1; funext z
  simp [Complex.div_ofReal_re]

/-- Wrapper for chapter 04's lem:c04_frac_derivative (`GSQG.c04_frac_derivative`): for
`g ∈ C²(ℝ;ℂ)` with `g, g'` bounded, `|D|^p g ∈ C¹` and `(|D|^p g)' = |D|^p g'`.
Proved from the chapter-04 result. -/
theorem c05_aux_frac_derivative (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (g : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hg0 : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M) (hg1 : ∃ M : ℝ, ∀ y, ‖deriv g y‖ ≤ M) :
    ContDiff ℝ 1 (fracDC p g) ∧ ∀ y, deriv (fracDC p g) y = fracDC p (deriv g) y :=
  c04_frac_derivative p hp hp1 g hg hg0 hg1

/-- Helper: `|D|^p(χ_Y f)` is `C¹` when `f` is `C²` on `(R,∞)`, `R < 3Y/10`. -/
theorem c05_aux_fracDC_cutoff (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) {f : ℝ → ℂ} {Y R : ℝ}
    (hY : 0 < Y) (hRY : R < 3 * Y / 10) (hf : ∀ t, R < t → ContDiffAt ℝ 2 f t) :
    ContDiff ℝ 1 (fracDC p (fun z => (res_chiY Y z : ℂ) * f z)) := by
  obtain ⟨hc, hs⟩ := c05_aux_cutoff_mul (n := 2) hY hRY hf
  refine (c05_aux_frac_derivative p hp hp1 _ hc ?_ ?_).1
  · exact hc.continuous.bounded_above_of_compact_support hs
  · exact (hc.continuous_deriv (by norm_num)).bounded_above_of_compact_support hs.deriv

/-- Helper: `HasDerivAt` of the real part. -/
theorem c05_aux_hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {y : ℝ} (hf : HasDerivAt f f' y) :
    HasDerivAt (fun t => (f t).re) f'.re y := by
  have := (Complex.reCLM.hasFDerivAt (x := f y)).comp_hasDerivAt y hf
  exact this

/-- Helper: differentiability of the complexification of a real function. -/
theorem c05_aux_ofReal_diff {f : ℝ → ℝ} {y : ℝ} (hf : DifferentiableAt ℝ f y) :
    DifferentiableAt ℝ (fun t => (f t : ℂ)) y := by
  have := (Complex.ofRealCLM.differentiableAt (x := f y)).comp y hf
  exact this

/-- Helper: exponent facts, `p ∈ (0,1)`: `-p-3β+1/p < 0`, `-p-3β+j/p ≤ -2p-1+j/p`,
`-p-2-j ≤ -2p-1+j/p` (`j ∈ {0,1}`). -/
theorem c05_aux_exponents (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    -p - 3 * beta p + 1 / p < 0 ∧ -p - 3 * beta p ≤ -2 * p - 1 ∧
      -p - 2 ≤ -2 * p - 1 ∧ -p - 2 - 1 ≤ -2 * p - 1 + 1 / p := by
  have hb : 3 * beta p = 3 / 2 + 3 / (2 * p) := by unfold beta; field_simp
  have h1p : 1 < 1 / p := by rw [lt_div_iff₀ hp]; linarith
  have hq : 0 < 1 / p := by positivity
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · rw [hb]
    have : 3 / (2 * p) = 3 / 2 * (1 / p) := by field_simp
    rw [this]; linarith
  · rw [hb]
    have : 3 / (2 * p) = 3 / 2 * (1 / p) := by field_simp
    rw [this]; nlinarith

/-- Helper: `|D|^p (a g) = a |D|^p g` for a complex constant `a`. -/
theorem c05_aux_fracDC_const_mul (p : ℝ) (a : ℂ) (g : ℝ → ℂ) (t : ℝ) :
    fracDC p (fun z => a * g z) t = a * fracDC p g t := by
  unfold fracDC
  rw [show (fun z => (a * g t - a * g z) / ((|t - z| ^ (p + 1) : ℝ) : ℂ)) =
      fun z => a * ((g t - g z) / ((|t - z| ^ (p + 1) : ℝ) : ℂ)) by funext z; ring,
    integral_const_mul]
  ring

/-- Helper: `2β = 1 + 1/p`. -/
theorem c05_aux_two_beta (p : ℝ) (hp : 0 < p) : 2 * beta p = 1 + 1 / p := by
  unfold beta; field_simp

/-- Helper: the integrand of `|D|^p h(y)` is integrable for bounded `C¹` complex `h`. -/
theorem c05_aux_fracDC_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (h : ℝ → ℂ)
    (hh : ContDiff ℝ 1 h) (hb : ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M) (y : ℝ) :
    Integrable (fun z => (h y - h z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) := by
  obtain ⟨M, hM⟩ := hb
  have hre := c05_aux_fracD_integrable p hp hp1 (fun z => (h z).re)
    (Complex.reCLM.contDiff.comp hh) ⟨M, fun x => (Complex.abs_re_le_norm _).trans (hM x)⟩ y
  have him := c05_aux_fracD_integrable p hp hp1 (fun z => (h z).im)
    (Complex.imCLM.contDiff.comp hh) ⟨M, fun x => (Complex.abs_im_le_norm _).trans (hM x)⟩ y
  rw [← Integrable.re_im_iff]
  constructor
  · refine hre.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.div_ofReal_re]
  · refine him.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.div_ofReal_im]

/-- Helper: `|D|^p (g₁ - g₂) = |D|^p g₁ - |D|^p g₂` for bounded `C¹` complex `g₁, g₂`. -/
theorem c05_aux_fracDC_sub (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g₁ g₂ : ℝ → ℂ)
    (h1 : ContDiff ℝ 1 g₁) (h2 : ContDiff ℝ 1 g₂) (hb1 : ∃ M : ℝ, ∀ x, ‖g₁ x‖ ≤ M)
    (hb2 : ∃ M : ℝ, ∀ x, ‖g₂ x‖ ≤ M) (y : ℝ) :
    fracDC p (fun z => g₁ z - g₂ z) y = fracDC p g₁ y - fracDC p g₂ y := by
  unfold fracDC
  rw [← mul_sub, ← integral_sub (c05_aux_fracDC_integrable p hp hp1 g₁ h1 hb1 y)
    (c05_aux_fracDC_integrable p hp hp1 g₂ h2 hb2 y)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

/-- Helper: `s ↦ φ(|s|)` is integrable when `φ` is integrable on `(0,∞)`. -/
theorem c05_aux_integrable_comp_abs (φ : ℝ → ℝ) (h : IntegrableOn φ (Ioi 0)) :
    Integrable (fun s => φ |s|) := by
  have hf : IntegrableOn (fun x => φ |x|) (Ioi 0) := by
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos (show (0:ℝ) < x from hx)]
  have int_Iic : IntegrableOn (fun x ↦ φ |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  have := int_Iic.union hf
  rw [Iic_union_Ioi, integrableOn_univ] at this
  exact this

/-- Helper: integrability and an upper bound for a nonnegative integral over `(0,∞)`
split at `a`. -/
theorem c05_aux_Ioi_split_bound (f g1 g2 : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (h1 : ∀ t ∈ Ioc 0 a, 0 ≤ f t ∧ f t ≤ g1 t) (h2 : ∀ t ∈ Ioi a, 0 ≤ f t ∧ f t ≤ g2 t)
    (hg1 : IntegrableOn g1 (Ioc 0 a)) (hg2 : IntegrableOn g2 (Ioi a)) :
    IntegrableOn f (Ioi 0) ∧ ∫ t in Ioi 0, f t ≤ (∫ t in Ioc 0 a, g1 t) + ∫ t in Ioi a, g2 t := by
  have hsub1 : Ioc 0 a ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hsub2 : Ioi a ⊆ Ioi 0 := Ioi_subset_Ioi ha.le
  have hf1 : IntegrableOn f (Ioc 0 a) := by
    refine Integrable.mono' hg1 (hf.mono_set hsub1) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h1 t ht).1]; exact (h1 t ht).2
  have hf2 : IntegrableOn f (Ioi a) := by
    refine Integrable.mono' hg2 (hf.mono_set hsub2) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h2 t ht).1]; exact (h2 t ht).2
  have hU : Ioc 0 a ∪ Ioi a = Ioi 0 := Ioc_union_Ioi_eq_Ioi ha.le
  refine ⟨hU ▸ hf1.union hf2, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hf1 hf2]
  exact add_le_add (setIntegral_mono_on hf1 hg1 measurableSet_Ioc (fun t ht => (h1 t ht).2))
    (setIntegral_mono_on hf2 hg2 measurableSet_Ioi (fun t ht => (h2 t ht).2))

/-- Helper: `∫_0^a c t^r = c a^{r+1}/(r+1)` for `r > -1`. -/
theorem c05_aux_int_Ioc_rpow (c r a : ℝ) (hr : -1 < r) (ha : 0 < a) :
    IntegrableOn (fun t => c * t ^ r) (Ioc 0 a) ∧
      ∫ t in Ioc 0 a, c * t ^ r = c * (a ^ (r + 1) / (r + 1)) := by
  have hii : IntervalIntegrable (fun t : ℝ => t ^ r) volume 0 a :=
    intervalIntegral.intervalIntegrable_rpow' hr
  refine ⟨(hii.const_mul c).1, ?_⟩
  rw [← intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hr), Real.zero_rpow (by linarith), sub_zero]

/-- Helper: `∫_a^∞ c t^r = -c a^{r+1}/(r+1)` for `r < -1`, `a > 0`. -/
theorem c05_aux_int_Ioi_rpow (c r a : ℝ) (hr : r < -1) (ha : 0 < a) :
    IntegrableOn (fun t => c * t ^ r) (Ioi a) ∧
      ∫ t in Ioi a, c * t ^ r = c * (-a ^ (r + 1) / (r + 1)) := by
  refine ⟨(integrableOn_Ioi_rpow_of_lt hr ha).const_mul c, ?_⟩
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hr ha]

/-- Helper: `t^n t^r = t^{n+r}` for `t > 0`. -/
theorem c05_aux_rpow_mul_npow {t : ℝ} (ht : 0 < t) (n : ℕ) (r : ℝ) :
    t ^ n * t ^ r = t ^ ((n : ℝ) + r) := by
  rw [Real.rpow_add ht, Real.rpow_natCast]

/-- Helper: `∫_z^∞ F = ∫_R^∞ F - ∫_R^z 𝟙_{(R,∞)}F` for `z ≥ R`. -/
theorem c05_aux_tail_eq (F : ℝ → ℂ) (R z : ℝ) (hF : IntegrableOn F (Ioi R)) (hz : R ≤ z) :
    ∫ t in Ioi z, F t = (∫ t in Ioi R, F t) - ∫ t in R..z, (Ioi R).indicator F t := by
  have hU : Ioc R z ∪ Ioi z = Ioi R := Ioc_union_Ioi_eq_Ioi hz
  have h1 : IntegrableOn F (Ioc R z) := hF.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn F (Ioi z) := hF.mono_set (Ioi_subset_Ioi hz)
  rw [intervalIntegral.integral_of_le hz,
    setIntegral_congr_fun measurableSet_Ioc (g := F) (fun t ht => indicator_of_mem
    (Ioc_subset_Ioi_self ht) F)]
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2]
  ring

/-- Helper: `∂_z ∫_z^∞ F = -F(z)` for `z > R` (`F` integrable, continuous on `(R,∞)`). -/
theorem c05_aux_tail_hasDeriv (F : ℝ → ℂ) (R : ℝ) (hF : IntegrableOn F (Ioi R))
    (hc : ContinuousOn F (Ioi R)) {z : ℝ} (hz : R < z) :
    HasDerivAt (fun w => ∫ t in Ioi w, F t) (-F z) z := by
  set G := (Ioi R).indicator F with hG
  have hGi : Integrable G := (integrable_indicator_iff measurableSet_Ioi).mpr hF
  have hGc : ContinuousOn G (Ioi R) := hc.congr (fun t ht => indicator_of_mem ht F)
  have hd := intervalIntegral.integral_hasDerivAt_right (hGi.intervalIntegrable (a := R) (b := z))
    (hGc.stronglyMeasurableAtFilter isOpen_Ioi z hz)
    (hGc.continuousAt (isOpen_Ioi.mem_nhds hz))
  rw [show G z = F z from indicator_of_mem (show z ∈ Ioi R from hz) F] at hd
  have := hd.const_sub (∫ t in Ioi R, F t)
  refine this.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
  exact c05_aux_tail_eq F R w hF (le_of_lt hw)

/-- Helper: the pointwise bounds `|N₀| ≤ 2BA²`, `|N₁| ≤ 2DA² + 4B²A` from sup bounds of the
increments. -/
theorem c05_aux_N_bounds {dv v dP P d2v d2P A B D : ℝ} (hv : |v| ≤ A) (hP : |P| ≤ A)
    (hdv : |dv| ≤ B) (hdP : |dP| ≤ B) (hd2v : |d2v| ≤ D) (hd2P : |d2P| ≤ D) :
    |dv * v ^ 2 - dP * P ^ 2| ≤ 2 * B * A ^ 2 ∧
      |(d2v * v ^ 2 - d2P * P ^ 2) + 2 * (dv ^ 2 * v - dP ^ 2 * P)| ≤
        2 * D * A ^ 2 + 4 * B ^ 2 * A := by
  have hA : 0 ≤ A := (abs_nonneg _).trans hv
  have hB : 0 ≤ B := (abs_nonneg _).trans hdv
  have hD : 0 ≤ D := (abs_nonneg _).trans hd2v
  have k : ∀ x w X W : ℝ, |x| ≤ X → |w| ≤ W → 0 ≤ W → |x * w ^ 2| ≤ X * W ^ 2 := by
    intro x w X W hx hw hW
    rw [abs_mul, abs_pow]
    exact mul_le_mul hx (pow_le_pow_left₀ (abs_nonneg _) hw 2) (by positivity)
      ((abs_nonneg _).trans hx)
  have k2 : ∀ x w X W : ℝ, |x| ≤ X → |w| ≤ W → 0 ≤ X → |x ^ 2 * w| ≤ X ^ 2 * W := by
    intro x w X W hx hw hX
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx 2) hw (abs_nonneg _) (by positivity)
  constructor
  · calc _ ≤ |dv * v ^ 2| + |dP * P ^ 2| := abs_sub _ _
      _ ≤ B * A ^ 2 + B * A ^ 2 := add_le_add (k _ _ _ _ hdv hv hA) (k _ _ _ _ hdP hP hA)
      _ = _ := by ring
  · calc _ ≤ |d2v * v ^ 2 - d2P * P ^ 2| + |2 * (dv ^ 2 * v - dP ^ 2 * P)| := abs_add_le _ _
      _ ≤ (|d2v * v ^ 2| + |d2P * P ^ 2|) + 2 * (|dv ^ 2 * v| + |dP ^ 2 * P|) := by
          gcongr
          · exact abs_sub _ _
          · rw [abs_mul, abs_two]; gcongr; exact abs_sub _ _
      _ ≤ (D * A ^ 2 + D * A ^ 2) + 2 * (B ^ 2 * A + B ^ 2 * A) := by
          gcongr
          · exact k _ _ _ _ hd2v hv hA
          · exact k _ _ _ _ hd2P hP hA
          · exact k2 _ _ _ _ hdv hv hB
          · exact k2 _ _ _ _ hdP hP hB
      _ = _ := by ring

/-- Helper: integral of `|s|^{-p-3}|N|` over `{|s| ≥ L}` for bounded measurable `N`. -/
theorem c05_aux_far_integral (p L B : ℝ) (N : ℝ → ℝ)
    (hN : Measurable N) (hB : ∀ s, |N s| ≤ B)
    (hI : IntegrableOn (fun s : ℝ => |s| ^ (-p - 3)) {s | L ≤ |s|})
    (hV : (∫ s in {s : ℝ | L ≤ |s|}, |s| ^ (-p - 3)) = 2 / (p + 2) * L ^ (-p - 2)) :
    IntegrableOn (fun s => |s| ^ (-p - 3) * |N s|) {s | L ≤ |s|} ∧
      (∫ s in {s : ℝ | L ≤ |s|}, |s| ^ (-p - 3) * |N s|) ≤ B * (2 / (p + 2) * L ^ (-p - 2)) := by
  have hmeas : MeasurableSet {s : ℝ | L ≤ |s|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hm : Measurable (fun s => |s| ^ (-p - 3) * |N s|) := by fun_prop
  have hle : ∀ s, |s| ^ (-p - 3) * |N s| ≤ B * |s| ^ (-p - 3) := by
    intro s
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hB s) (Real.rpow_nonneg (abs_nonneg s) _)
  have hint : IntegrableOn (fun s => |s| ^ (-p - 3) * |N s|) {s | L ≤ |s|} := by
    refine Integrable.mono' (hI.const_mul B) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg s) _)
      (abs_nonneg _))]
    exact hle s
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ s in {s : ℝ | L ≤ |s|}, B * |s| ^ (-p - 3) :=
        setIntegral_mono_on hint (hI.const_mul B) hmeas (fun s _ => hle s)
    _ = _ := by rw [integral_const_mul, hV]

/-- Helper: measurability of increments. -/
theorem c05_aux_Delta_meas (h : ℝ → ℝ) (hh : Measurable h) (y : ℝ) :
    Measurable (fun s => c05_plane_wave_Delta h y s) :=
  measurable_const.sub (hh.comp (measurable_const.sub measurable_id))

/-- Helper: the frozen plane wave is continuous. -/
theorem c05_aux_plane_wave_cont (p R ε : ℝ) (μ : ℂ) (y : ℝ) :
    Continuous (c05_plane_wave p R ε μ y) := by
  unfold c05_plane_wave
  fun_prop

/-- Helper: measurability of the cubic integrands `N₀, N₁` (generic form). -/
theorem c05_aux_N_meas (v P : ℝ → ℝ) (hv : Measurable v) (hP : Measurable P) (y : ℝ) :
    Measurable (fun s => c05_plane_wave_Delta (deriv v) y s * c05_plane_wave_Delta v y s ^ 2 -
      c05_plane_wave_Delta (deriv P) y s * c05_plane_wave_Delta P y s ^ 2) ∧
    Measurable (fun s =>
      (c05_plane_wave_Delta (deriv (deriv v)) y s * c05_plane_wave_Delta v y s ^ 2 -
        c05_plane_wave_Delta (deriv (deriv P)) y s * c05_plane_wave_Delta P y s ^ 2) +
      2 * (c05_plane_wave_Delta (deriv v) y s ^ 2 * c05_plane_wave_Delta v y s -
        c05_plane_wave_Delta (deriv P) y s ^ 2 * c05_plane_wave_Delta P y s)) := by
  have m1 := c05_aux_Delta_meas _ hv y
  have m2 := c05_aux_Delta_meas _ (measurable_deriv v) y
  have m3 := c05_aux_Delta_meas _ (measurable_deriv (deriv v)) y
  have m4 := c05_aux_Delta_meas _ hP y
  have m5 := c05_aux_Delta_meas _ (measurable_deriv P) y
  have m6 := c05_aux_Delta_meas _ (measurable_deriv (deriv P)) y
  exact ⟨(m2.mul (m1.pow_const 2)).sub (m5.mul (m4.pow_const 2)),
    ((m3.mul (m1.pow_const 2)).sub (m6.mul (m4.pow_const 2))).add
      ((((m2.pow_const 2).mul m1).sub ((m5.pow_const 2).mul m4)).const_mul 2)⟩

/-- Helper: `|xyz| ≤ XYZ`. -/
theorem c05_aux_abs3 {x y z X Y Z : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |x * y * z| ≤ X * Y * Z := by
  rw [abs_mul, abs_mul]
  have hX : 0 ≤ X := (abs_nonneg _).trans hx
  have hY : 0 ≤ Y := (abs_nonneg _).trans hy
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hX) hz (abs_nonneg _) (by positivity)

/-- Helper: the near-region pointwise bounds for `N₀`, `N₁` (blueprint lem:c05_cubic_near). -/
theorem c05_aux_N_near_bounds {a1 b1 a2 b2 d1 d2 c Cc lam m0 m1 X0 X1 : ℝ} (hm1 : m1 = lam * m0)
    (hb1 : |b1| ≤ c * m0) (hb2 : |b2| ≤ c * m0) (ha1 : |a1| ≤ c * m1) (ha2 : |a2| ≤ c * m1)
    (hd2 : |d2| ≤ c * lam * m1)
    (hab : |a1 - a2| ≤ Cc * X1) (hbb : |b1 - b2| ≤ Cc * X0) (hdd : |d1 - d2| ≤ Cc * lam * X1) :
    |a1 * b1 ^ 2 - a2 * b2 ^ 2| ≤ Cc * c ^ 2 * m0 ^ 2 * (X1 + 2 * lam * X0) ∧
    |(d1 * b1 ^ 2 - d2 * b2 ^ 2) + 2 * (a1 ^ 2 * b1 - a2 ^ 2 * b2)| ≤
      Cc * c ^ 2 * lam * m0 ^ 2 * (5 * X1 + 4 * lam * X0) := by
  have hbs : |b1 + b2| ≤ 2 * (c * m0) := by
    calc |b1 + b2| ≤ |b1| + |b2| := abs_add_le _ _
      _ ≤ _ := by linarith
  have has : |a1 + a2| ≤ 2 * (c * m1) := by
    calc |a1 + a2| ≤ |a1| + |a2| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hb1' : |b1 * 1| ≤ c * m0 := by rwa [mul_one]
  have hone : |(1 : ℝ)| ≤ 1 := by simp
  have e0 : a1 * b1 ^ 2 - a2 * b2 ^ 2 = (a1 - a2) * b1 * b1 + a2 * (b1 - b2) * (b1 + b2) := by ring
  have t1 := c05_aux_abs3 hab hb1 hb1
  have t2 := c05_aux_abs3 ha2 hbb hbs
  constructor
  · rw [e0]
    calc _ ≤ |(a1 - a2) * b1 * b1| + |a2 * (b1 - b2) * (b1 + b2)| := abs_add_le _ _
      _ ≤ Cc * X1 * (c * m0) * (c * m0) + c * m1 * (Cc * X0) * (2 * (c * m0)) := add_le_add t1 t2
      _ = _ := by rw [hm1]; ring
  · have e1 : (d1 * b1 ^ 2 - d2 * b2 ^ 2) + 2 * (a1 ^ 2 * b1 - a2 ^ 2 * b2) =
        ((d1 - d2) * b1 * b1 + d2 * (b1 - b2) * (b1 + b2)) +
          2 * ((a1 - a2) * (a1 + a2) * b1 + a2 * a2 * (b1 - b2)) := by ring
    have t3 := c05_aux_abs3 hdd hb1 hb1
    have t4 := c05_aux_abs3 hd2 hbb hbs
    have t5 := c05_aux_abs3 hab has hb1
    have t6 := c05_aux_abs3 ha2 ha2 hbb
    rw [e1]
    calc _ ≤ (|(d1 - d2) * b1 * b1| + |d2 * (b1 - b2) * (b1 + b2)|) +
          2 * (|(a1 - a2) * (a1 + a2) * b1| + |a2 * a2 * (b1 - b2)|) := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) ?_)
          rw [abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
      _ ≤ (Cc * lam * X1 * (c * m0) * (c * m0) + c * lam * m1 * (Cc * X0) * (2 * (c * m0))) +
          2 * (Cc * X1 * (2 * (c * m1)) * (c * m0) + c * m1 * (c * m1) * (Cc * X0)) := by
          gcongr
      _ = _ := by rw [hm1]; ring

/-- Helper: integral of `|s|^r|N|` over `{|s| ≤ L}` dominated by an integrable `g`. -/
theorem c05_aux_near_integral (r L : ℝ) (N g : ℝ → ℝ) (hN : Measurable N) (hg : Integrable g)
    (hg0 : ∀ s, 0 ≤ g s) (hb : ∀ s, |s| ≤ L → |s| ^ r * |N s| ≤ g s) :
    IntegrableOn (fun s => |s| ^ r * |N s|) {s | |s| ≤ L} ∧
      (∫ s in {s : ℝ | |s| ≤ L}, |s| ^ r * |N s|) ≤ ∫ s, g s := by
  have hmeas : MeasurableSet {s : ℝ | |s| ≤ L} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hm : Measurable (fun s => |s| ^ r * |N s|) := by fun_prop
  have hint : IntegrableOn (fun s => |s| ^ r * |N s|) {s | |s| ≤ L} := by
    refine Integrable.mono' hg.integrableOn hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg s) _)
      (abs_nonneg _))]
    exact hb s hs
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ s in {s : ℝ | |s| ≤ L}, g s :=
        setIntegral_mono_on hint hg.integrableOn hmeas (fun s hs => hb s hs)
    _ ≤ ∫ s, g s := setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)

/-! ### Setting and the decomposition of `ℰ₅` -/

/-- Projection (part) of chapter 03's lem:analysis_coefficient (`GSQG.analysis_coefficient`):
`|c_ε| ≤ c_α α ε/(2p)`.  Proved from the chapter-03 result. -/
theorem c05_aux_analysis_coefficient_bound (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) : |c_eps p ε| ≤ calpha p * (p + 1) / (2 * p) * ε :=
  (analysis_coefficient p ε hp hp1 hε hε1).2.2.1

/-- Projection (part) of chapter 04's lem:c04_cubic_sine_response
(`GSQG.c04_cubic_sine_response`): `𝒬_{ε,3}(sin) = c₁ cos + c₂ cos 3·`, `|c_i(ε)| ≤ C₃ ε`.
Proved from the chapter-04 result. -/
theorem c05_aux_cubic_sine_response (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C₃ > (0 : ℝ), ∀ ε : ℝ, 0 ≤ ε →
      (∀ y, c04_cubic_part p ε Real.sin y =
        cubic_c1 p ε * Real.cos y + cubic_c2 p ε * Real.cos (3 * y)) ∧
      |cubic_c1 p ε| ≤ C₃ * ε ∧ |cubic_c2 p ε| ≤ C₃ * ε := by
  obtain ⟨C₃, hC₃, h⟩ := c04_cubic_sine_response p hp hp1
  refine ⟨C₃, hC₃, fun ε hε => ?_⟩
  obtain ⟨h1, -, -, -, h2, h3⟩ := h ε hε
  exact ⟨h1, h2, h3⟩

/-- Blueprint: lem:c05_small_constants.
`|c_ε| + |n_ε| + |c_cubic| + |c_log(μ)| ≤ C₀ ε` for `ε ∈ [0,ε₀]`, `μ ∈ B̄`. -/
theorem c05_small_constants (S : c05_standing) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, 0 ≤ ε → ε ≤ S.ε₀ → μ ∈ Bbar S.p S.δ →
      |c_eps S.p ε| + |n_eps S.p ε| + |c_cubic S.p ε| + |c_log S.p ε μ| ≤ C₀ * ε := by
  obtain ⟨C₃, hC₃, hsine⟩ := c05_aux_cubic_sine_response S.p S.hp_lo S.hp_hi
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have h3 : 0 < (3 : ℝ) ^ S.p - 1 := by
    have : (1 : ℝ) < 3 ^ S.p := Real.one_lt_rpow (by norm_num) hp0
    linarith
  set K : ℝ := ‖mu_star S.p‖ + S.δ
  have hδ := S.hδ
  refine ⟨|calpha S.p * (S.p + 1) / (2 * S.p)| + 4 * C₃ + 4 * C₃ / ((3 : ℝ) ^ S.p - 1) +
    4 * C₃ * K ^ 2 / S.p + 1, by positivity, ?_⟩
  intro ε μ hε hε0 hμ
  obtain ⟨-, h1, h2⟩ := hsine ε hε
  have hce := c05_aux_analysis_coefficient_bound S.p ε hp0 S.hp_hi hε (hε0.trans S.hε₀_le)
  have hμK : ‖μ‖ ≤ K := by
    have : dist μ (mu_star S.p) ≤ S.δ := hμ
    have := norm_le_norm_add_norm_sub' μ (mu_star S.p)
    rw [dist_eq_norm] at *
    simp only [K]; linarith
  have hn : |n_eps S.p ε| ≤ 4 * C₃ * ε := by
    unfold n_eps; rw [abs_mul]; norm_num; linarith
  have hc : |c_cubic S.p ε| ≤ 4 * C₃ / ((3 : ℝ) ^ S.p - 1) * ε := by
    unfold c_cubic
    rw [abs_div, abs_mul, abs_of_pos h3]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right h3]
    norm_num; nlinarith
  have hl : |c_log S.p ε μ| ≤ 4 * C₃ * K ^ 2 / S.p * ε := by
    unfold c_log
    rw [abs_div, abs_neg, abs_mul, abs_of_pos hp0,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖μ‖ ^ 2)]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp0]
    have hμ2 : ‖μ‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hμK 2
    calc |n_eps S.p ε| * ‖μ‖ ^ 2 ≤ (4 * C₃ * ε) * K ^ 2 :=
          mul_le_mul hn hμ2 (by positivity) (by positivity)
      _ = 4 * C₃ * K ^ 2 * ε := by ring
  have hce' : |c_eps S.p ε| ≤ |calpha S.p * (S.p + 1) / (2 * S.p)| * ε :=
    hce.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
  nlinarith

/-! ### Symbol bounds and primitives -/

/-- Helper: `ε ∈ [0, ε₀]` lies below each of the chapter 04 thresholds in `c05_eps0_star`. -/
theorem c05_aux_eps_le (S : c05_standing) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ S.ε₀) :
    ε ∈ Icc 0 (Classical.choose (c04_lambda_psi_difference S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) ∧
    ε ∈ Icc 0 (Classical.choose (c04_Z_bounds S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) ∧
    ε ∈ Icc 0 (Classical.choose (c04_Z_difference_products S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) ∧
    ε ∈ Icc 0 (Classical.choose (c04_Z_difference S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) ∧
    ε ∈ Icc 0 (Classical.choose (c04_lambda_taylor S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) ∧
    ε ∈ Icc 0 (Classical.choose (c04_Z_primitive S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) ∧
    ε ∈ Icc 0 (Classical.choose
      (c04_phase_exponential_difference S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) ∧
    ε ∈ Icc 0 (Classical.choose (approx_phase_differences S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)) := by
  have hst := S.hε₀_small
  have h : 3 / 4 < S.p ∧ S.p < 1 ∧ 0 < S.δ ∧ S.δ ≤ ‖mu_star S.p‖ / 2 :=
    ⟨S.hp_lo, S.hp_hi, S.hδ, S.hδ_le⟩
  rw [c05_eps0_star, dite_cond_eq_true (eq_true h)] at hst
  have he := h1.trans hst
  refine ⟨⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩⟩ <;>
  · refine he.trans ?_
    simp only [min_le_iff, le_refl, true_or, or_true]

/-- Helper: `|(1+x)^p - 1| ≤ |x|`, `(1+x)^{p-1} ≤ 2`, `(1+x)^{p-2} ≤ 4` for `|x| ≤ 1/2`, `0 < p < 1`. -/
theorem c05_aux_one_add_rpow (p x : ℝ) (hp : 0 < p) (hp1 : p < 1) (hx : |x| ≤ 1 / 2) :
    |(1 + x) ^ p - 1| ≤ |x| ∧ 0 < (1 + x) ^ (p - 1) ∧ (1 + x) ^ (p - 1) ≤ 2 ∧
      0 < (1 + x) ^ (p - 2) ∧ (1 + x) ^ (p - 2) ≤ 4 := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  have hb : 0 < 1 + x := by linarith
  have hb2 : (1 / 2 : ℝ) ≤ 1 + x := by linarith
  refine ⟨?_, Real.rpow_pos_of_pos hb _, ?_, Real.rpow_pos_of_pos hb _, ?_⟩
  · rcases le_total 0 x with h | h
    · have h1 : 1 ≤ (1 + x) ^ p := Real.one_le_rpow (by linarith) hp.le
      have h2 : (1 + x) ^ p ≤ (1 + x) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hp1.le
      rw [Real.rpow_one] at h2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg h]; linarith
    · have h1 : (1 + x) ^ p ≤ 1 := Real.rpow_le_one hb.le (by linarith) hp.le
      have h2 : (1 + x) ^ (1 : ℝ) ≤ (1 + x) ^ p :=
        Real.rpow_le_rpow_of_exponent_ge hb (by linarith) hp1.le
      rw [Real.rpow_one] at h2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos h]; linarith
  · calc (1 + x) ^ (p - 1) ≤ (1 / 2 : ℝ) ^ (p - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hb2 (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 2 := by norm_num
  · calc (1 + x) ^ (p - 2) ≤ (1 / 2 : ℝ) ^ (p - 2) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hb2 (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = 4 := by norm_num

/-- Helper: `y · y^r = y^{r+1}` for `y > 0`. -/
theorem c05_aux_mul_rpow (y r : ℝ) (hy : 0 < y) : y * y ^ r = y ^ (r + 1) := by
  rw [Real.rpow_add hy, Real.rpow_one]; ring

/-- Helper: the explicit correction `λ̃ = a y^{-p-1} + b y^{-1-1/p}` and its first two derivatives,
with bounds `|∂^j λ̃| ≤ K ε y^{-p-1-j}` (`j ≤ 2`, `y ≥ 1`) when `|a|, |b| ≤ C₀ ε / p`, `C₀ ε`. -/
theorem c05_aux_ltilde (p a b K ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (hab : (|a| + |b|) * (3 + 1 / p) ^ 2 ≤ K * ε) :
    let L : ℝ → ℝ := fun t => a * t ^ (-p - 1) + b * t ^ (-1 - 1 / p)
    let L1 : ℝ → ℝ := fun t => a * (-p - 1) * t ^ (-p - 1 - 1) + b * (-1 - 1 / p) * t ^ (-1 - 1 / p - 1)
    let L2 : ℝ → ℝ := fun t => a * (-p - 1) * (-p - 1 - 1) * t ^ (-p - 1 - 1 - 1) +
      b * (-1 - 1 / p) * (-1 - 1 / p - 1) * t ^ (-1 - 1 / p - 1 - 1)
    (∀ t, 0 < t → HasDerivAt L (L1 t) t ∧ HasDerivAt L1 (L2 t) t) ∧
    ∀ t, 1 ≤ t → |L t| ≤ K * ε * t ^ (-p - 1) ∧ |L1 t| ≤ K * ε * t ^ (-p - 2) ∧
      |L2 t| ≤ K * ε * t ^ (-p - 3) := by
  intro L L1 L2
  have hpinv : 1 < 1 / p := by rw [lt_div_iff₀ hp]; linarith
  refine ⟨fun t ht => ⟨?_, ?_⟩, fun t ht => ?_⟩
  · have h1 := (Real.hasDerivAt_rpow_const (x := t) (p := -p - 1) (Or.inl ht.ne')).const_mul a
    have h2 := (Real.hasDerivAt_rpow_const (x := t) (p := -1 - 1 / p) (Or.inl ht.ne')).const_mul b
    exact (h1.add h2).congr_deriv (by simp only [L1]; ring)
  · have h1 := (Real.hasDerivAt_rpow_const (x := t) (p := -p - 1 - 1) (Or.inl ht.ne')).const_mul
      (a * (-p - 1))
    have h2 := (Real.hasDerivAt_rpow_const (x := t) (p := -1 - 1 / p - 1) (Or.inl ht.ne')).const_mul
      (b * (-1 - 1 / p))
    exact (h1.add h2).congr_deriv (by simp only [L2]; ring)
  · have ht0 : 0 < t := by linarith
    have hm : ∀ e₁ e₂ : ℝ, e₁ ≤ e₂ → t ^ e₁ ≤ t ^ e₂ := fun e₁ e₂ h =>
      Real.rpow_le_rpow_of_exponent_le ht h
    have hpos : ∀ e : ℝ, 0 ≤ t ^ e := fun e => Real.rpow_nonneg ht0.le e
    have ha := abs_nonneg a
    have hb := abs_nonneg b
    have hs : 1 ≤ (3 + 1 / p) := by linarith
    have hs2 : (3 + 1 / p) ≤ (3 + 1 / p) ^ 2 := by nlinarith
    have hab1 : |a| + |b| ≤ K * ε := by nlinarith
    have hab2 : (|a| + |b|) * (3 + 1 / p) ≤ K * ε := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · simp only [L]
      have e1 := hm (-1 - 1 / p) (-p - 1) (by linarith)
      calc |a * t ^ (-p - 1) + b * t ^ (-1 - 1 / p)|
          ≤ |a| * t ^ (-p - 1) + |b| * t ^ (-1 - 1 / p) := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg (hpos _), abs_of_nonneg (hpos _)]
        _ ≤ |a| * t ^ (-p - 1) + |b| * t ^ (-p - 1) := by gcongr
        _ = (|a| + |b|) * t ^ (-p - 1) := by ring
        _ ≤ K * ε * t ^ (-p - 1) := by gcongr
    · simp only [L1]
      have e1 := hm (-1 - 1 / p - 1) (-p - 2) (by linarith)
      rw [show -p - 1 - 1 = -p - 2 by ring]
      calc |a * (-p - 1) * t ^ (-p - 2) + b * (-1 - 1 / p) * t ^ (-1 - 1 / p - 1)|
          ≤ |a| * (p + 1) * t ^ (-p - 2) + |b| * (1 + 1 / p) * t ^ (-1 - 1 / p - 1) := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hpos _), abs_of_nonneg (hpos _),
              abs_of_nonpos (show -p - 1 ≤ 0 by linarith),
              abs_of_nonpos (show -1 - 1 / p ≤ 0 by linarith)]
            apply le_of_eq; ring
        _ ≤ |a| * (3 + 1 / p) * t ^ (-p - 2) + |b| * (3 + 1 / p) * t ^ (-p - 2) := by
            gcongr
            · linarith
            · linarith
        _ = (|a| + |b|) * (3 + 1 / p) * t ^ (-p - 2) := by ring
        _ ≤ K * ε * t ^ (-p - 2) := by gcongr
    · simp only [L2]
      have e1 := hm (-1 - 1 / p - 1 - 1) (-p - 3) (by linarith)
      rw [show -p - 1 - 1 - 1 = -p - 3 by ring]
      have hc1 : (p + 1) * (p + 2) ≤ (3 + 1 / p) ^ 2 := by nlinarith
      have hc2 : (1 + 1 / p) * (2 + 1 / p) ≤ (3 + 1 / p) ^ 2 := by nlinarith
      calc |a * (-p - 1) * (-p - 1 - 1) * t ^ (-p - 3) +
              b * (-1 - 1 / p) * (-1 - 1 / p - 1) * t ^ (-1 - 1 / p - 1 - 1)|
          ≤ |a| * ((p + 1) * (p + 2)) * t ^ (-p - 3) +
              |b| * ((1 + 1 / p) * (2 + 1 / p)) * t ^ (-1 - 1 / p - 1 - 1) := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hpos _),
              abs_of_nonneg (hpos _), abs_of_nonpos (show -p - 1 ≤ 0 by linarith),
              abs_of_nonpos (show -p - 1 - 1 ≤ 0 by linarith),
              abs_of_nonpos (show -1 - 1 / p ≤ 0 by linarith),
              abs_of_nonpos (show -1 - 1 / p - 1 ≤ 0 by linarith)]
            apply le_of_eq; ring
        _ ≤ |a| * (3 + 1 / p) ^ 2 * t ^ (-p - 3) + |b| * (3 + 1 / p) ^ 2 * t ^ (-p - 3) := by
            gcongr
        _ = (|a| + |b|) * (3 + 1 / p) ^ 2 * t ^ (-p - 3) := by ring
        _ ≤ K * ε * t ^ (-p - 3) := by gcongr

/-- Helper for lem:c05_symbol_bounds (4): `|∂^j((λ^p)' - 1)(y)| ≤ C ε y^{-p-1-j}`, `j ≤ 1`. -/
theorem c05_aux_item4 (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ μ : ℂ, 0 ≤ ε → ε ≤ S.ε₀ →
      μ ∈ Bbar S.p S.δ → ∀ y : ℝ, R₀ ≤ y → ∀ j : ℕ, j ≤ 1 →
        |iteratedDeriv j (fun t => deriv (fun u => fam_lambda S.p ε μ u ^ S.p) t - 1) y| ≤
          C * ε * y ^ (-S.p - 1 - j) := by
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hp1 := S.hp_hi
  set p := S.p with hpdef
  obtain ⟨C₀, hC₀, hsc⟩ := c05_small_constants S
  set K : ℝ := C₀ * (1 / p + 1) * (3 + 1 / p) ^ 2 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨4 * K + 2, by linarith, (1 + 2 * p) * K + 4 * p * K + 4 * p * K ^ 2 + 2 * p * K + 1,
    by positivity, fun ε μ hε0 hε1 hμ y hy j hj => ?_⟩
  have hε1' : ε ≤ 1 := hε1.trans S.hε₀_le
  -- the coefficients
  set a : ℝ := -(c_eps p ε / p) with ha
  set b : ℝ := c_log p ε μ with hb
  have hsc' := hsc ε μ hε0 hε1 hμ
  have habs : (|a| + |b|) * (3 + 1 / p) ^ 2 ≤ K * ε := by
    have h1 : |a| ≤ C₀ * ε / p := by
      rw [ha, abs_neg, abs_div, abs_of_pos hp0]
      have hn1 := abs_nonneg (n_eps p ε)
      have hn2 := abs_nonneg (c_cubic p ε)
      have hn3 := abs_nonneg (c_log p ε μ)
      have hce : |c_eps p ε| ≤ C₀ * ε := by linarith
      exact div_le_div_of_nonneg_right hce hp0.le
    have h2 : |b| ≤ C₀ * ε := by
      linarith [abs_nonneg (n_eps p ε), abs_nonneg (c_cubic p ε), abs_nonneg (c_eps p ε)]
    have : |a| + |b| ≤ C₀ * (1 / p + 1) * ε := by
      have e : C₀ * ε / p = C₀ * (1 / p) * ε := by ring
      rw [e] at h1; nlinarith
    calc (|a| + |b|) * (3 + 1 / p) ^ 2 ≤ C₀ * (1 / p + 1) * ε * (3 + 1 / p) ^ 2 := by gcongr
      _ = K * ε := by rw [hK]; ring
  obtain ⟨hLd, hLb⟩ := c05_aux_ltilde p a b K ε hp0 hp1 hε0 habs
  set L : ℝ → ℝ := fun t => a * t ^ (-p - 1) + b * t ^ (-1 - 1 / p) with hL
  set L1 : ℝ → ℝ := fun t => a * (-p - 1) * t ^ (-p - 1 - 1) + b * (-1 - 1 / p) * t ^ (-1 - 1 / p - 1)
    with hL1
  set L2 : ℝ → ℝ := fun t => a * (-p - 1) * (-p - 1 - 1) * t ^ (-p - 1 - 1 - 1) +
      b * (-1 - 1 / p) * (-1 - 1 / p - 1) * t ^ (-1 - 1 / p - 1 - 1) with hL2
  -- smallness of `λ̃` on `(2K+1, ∞)`
  have hsmall : ∀ t, 2 * K + 1 < t → |L t| ≤ 1 / 2 := by
    intro t ht
    have ht1 : 1 ≤ t := by linarith
    have h := (hLb t ht1).1
    have h2 : t ^ (-p - 1) ≤ t ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    rw [Real.rpow_neg_one] at h2
    have h3 : K * ε * t ^ (-p - 1) ≤ K * t⁻¹ := by
      calc K * ε * t ^ (-p - 1) ≤ K * 1 * t⁻¹ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hε1' hK0.le) h2 (by positivity) (by positivity)
        _ = K * t⁻¹ := by ring
    have h4 : K * t⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith
    linarith
  -- `λ = t^{1/p}(1+λ̃)` and `λ^p = t(1+λ̃)^p` for `t > 0` with `1 + λ̃ > 0`
  have hlam : ∀ t, 0 < t → fam_lambda p ε μ t = t ^ (1 / p) * (1 + L t) := by
    intro t ht
    have h1p : (1 - p ^ 2) ≠ 0 := by nlinarith
    simp only [fam_lambda, c_power, hL, ha, hb]
    rw [mul_add, mul_add, mul_one, ← mul_assoc, ← mul_assoc]
    rw [mul_comm (t ^ (1 / p)) a, mul_assoc a, ← Real.rpow_add ht, mul_comm (t ^ (1 / p)) b,
      mul_assoc b, ← Real.rpow_add ht]
    rw [show 1 / p + (-1 - 1 / p) = -1 by ring, Real.rpow_neg_one,
      show 1 / p + (-p - 1) = 1 / p - p - 1 by ring]
    rw [ha, hb]
    field_simp
    ring
  have hpow : ∀ t, 0 < t → 0 < 1 + L t → fam_lambda p ε μ t ^ p = t * (1 + L t) ^ p := by
    intro t ht hpos
    rw [hlam t ht, Real.mul_rpow (Real.rpow_nonneg ht.le _) hpos.le, ← Real.rpow_mul ht.le,
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  -- the open set `U = (2K+1, ∞)`
  have hU : ∀ t, 2 * K + 1 < t → 0 < t ∧ 0 < 1 + L t := by
    intro t ht
    have := hsmall t ht
    exact ⟨by linarith, by linarith [(abs_le.1 this).1]⟩
  set h : ℝ → ℝ := fun t => (1 + L t) ^ p + p * t * (1 + L t) ^ (p - 1) * L1 t with hh
  set h1 : ℝ → ℝ := fun t => L1 t * p * (1 + L t) ^ (p - 1) +
      (p * (1 + L t) ^ (p - 1) * L1 t + p * t * (L1 t * (p - 1) * (1 + L t) ^ (p - 1 - 1)) * L1 t +
        p * t * (1 + L t) ^ (p - 1) * L2 t) with hh1
  have hHd : ∀ t, 2 * K + 1 < t → HasDerivAt (fun u => u * (1 + L u) ^ p) (h t) t := by
    intro t ht
    obtain ⟨ht0, hpos⟩ := hU t ht
    have d1 := ((hLd t ht0).1.const_add 1).rpow_const (p := p) (Or.inl hpos.ne')
    exact ((hasDerivAt_id t).mul d1).congr_deriv (by simp only [hh, id_eq]; ring)
  have hhd : ∀ t, 2 * K + 1 < t → HasDerivAt h (h1 t) t := by
    intro t ht
    obtain ⟨ht0, hpos⟩ := hU t ht
    have d0 := (hLd t ht0).1.const_add 1
    have d1 := d0.rpow_const (p := p) (Or.inl hpos.ne')
    have d2 := d0.rpow_const (p := p - 1) (Or.inl hpos.ne')
    have d3 := (hLd t ht0).2
    have := d1.add ((((hasDerivAt_id t).const_mul p).mul d2).mul d3)
    exact this.congr_deriv (by simp only [hh1, id_eq, Pi.mul_apply, Pi.add_apply]; ring)
  -- `deriv (λ^p) = h` near `y`
  have hy0 : 2 * K + 1 < y := by linarith
  have hnhds : Ioi (2 * K + 1) ∈ nhds y := isOpen_Ioi.mem_nhds hy0
  have hev : (fun u => fam_lambda p ε μ u ^ p) =ᶠ[nhds y] (fun u => u * (1 + L u) ^ p) :=
    Filter.eventually_of_mem hnhds fun t ht => hpow t (hU t ht).1 (hU t ht).2
  have hev2 : (fun t => deriv (fun u => fam_lambda p ε μ u ^ p) t - 1) =ᶠ[nhds y]
      (fun t => h t - 1) := by
    filter_upwards [hev.deriv, hnhds] with t ht ht'
    rw [ht, (hHd t ht').deriv]
  -- bounds at `y`
  have hy1 : 1 ≤ y := by linarith
  have hyp : 0 < y := by linarith
  obtain ⟨bL, bL1, bL2⟩ := hLb y hy1
  have hLs := hsmall y hy0
  obtain ⟨r0, r1p, r1, r2p, r2⟩ := c05_aux_one_add_rpow p (L y) hp0 hp1 hLs
  have hεε : ε * ε ≤ ε := by nlinarith
  have hKε : 0 ≤ K * ε := by positivity
  have hypos : ∀ e : ℝ, 0 < y ^ e := fun e => Real.rpow_pos_of_pos hyp e
  have hmy : ∀ e₁ e₂ : ℝ, e₁ ≤ e₂ → y ^ e₁ ≤ y ^ e₂ := fun e₁ e₂ hle =>
    Real.rpow_le_rpow_of_exponent_le hy1 hle
  interval_cases j
  · rw [iteratedDeriv_zero, hev2.eq_of_nhds]
    simp only [hh]
    -- `|h y - 1| ≤ |λ̃| + p y 2 |λ̃'|`
    have e1 : y * y ^ (-p - 2) = y ^ (-p - 1) := by
      rw [c05_aux_mul_rpow y _ hyp]; ring_nf
    have t1 : |p * y * (1 + L y) ^ (p - 1) * L1 y| ≤ 2 * p * K * ε * y ^ (-p - 1) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp0, abs_of_pos hyp, abs_of_pos r1p]
      calc p * y * (1 + L y) ^ (p - 1) * |L1 y| ≤ p * y * 2 * (K * ε * y ^ (-p - 2)) := by gcongr
        _ = 2 * p * K * ε * (y * y ^ (-p - 2)) := by ring
        _ = _ := by rw [e1]
    have t0 : |(1 + L y) ^ p - 1| ≤ K * ε * y ^ (-p - 1) := r0.trans bL
    calc |(1 + L y) ^ p + p * y * (1 + L y) ^ (p - 1) * L1 y - 1|
        = |((1 + L y) ^ p - 1) + p * y * (1 + L y) ^ (p - 1) * L1 y| := by ring_nf
      _ ≤ |(1 + L y) ^ p - 1| + |p * y * (1 + L y) ^ (p - 1) * L1 y| := abs_add_le _ _
      _ ≤ K * ε * y ^ (-p - 1) + 2 * p * K * ε * y ^ (-p - 1) := add_le_add t0 t1
      _ = (1 + 2 * p) * K * ε * y ^ (-p - 1) := by ring
      _ ≤ ((1 + 2 * p) * K + 4 * p * K + 4 * p * K ^ 2 + 2 * p * K + 1) * ε *
            y ^ (-p - 1 - ((0 : ℕ) : ℝ)) := by
          rw [Nat.cast_zero, sub_zero]
          have hd : 0 ≤ (4 * p * K + 4 * p * K ^ 2 + 2 * p * K + 1) * (ε * y ^ (-p - 1)) := by
            positivity
          linarith [hd, show ((1 + 2 * p) * K + 4 * p * K + 4 * p * K ^ 2 + 2 * p * K + 1) * ε *
            y ^ (-p - 1) = (1 + 2 * p) * K * ε * y ^ (-p - 1) +
              (4 * p * K + 4 * p * K ^ 2 + 2 * p * K + 1) * (ε * y ^ (-p - 1)) by ring]
  · rw [iteratedDeriv_one, hev2.deriv_eq, ((hhd y hy0).sub_const 1).deriv]
    simp only [hh1]
    have e2 : y * y ^ (-p - 3) = y ^ (-p - 2) := by
      rw [c05_aux_mul_rpow y _ hyp]; ring_nf
    have e3 : y * (y ^ (-p - 2) * y ^ (-p - 2)) ≤ y ^ (-p - 2) := by
      rw [← mul_assoc, c05_aux_mul_rpow y _ hyp, ← Real.rpow_add hyp]
      exact hmy _ _ (by linarith)
    have hp1' : |p - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have bL1' : |L1 y| ≤ K * ε * y ^ (-p - 2) := bL1
    have hL1sq : |L1 y| * |L1 y| ≤ (K * ε) ^ 2 * (y ^ (-p - 2) * y ^ (-p - 2)) := by
      calc |L1 y| * |L1 y| ≤ (K * ε * y ^ (-p - 2)) * (K * ε * y ^ (-p - 2)) :=
            mul_le_mul bL1' bL1' (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hKεsq : (K * ε) ^ 2 ≤ K ^ 2 * ε := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by rw [sq]; exact hεε) (sq_nonneg _)
    have T1 : |L1 y * p * (1 + L y) ^ (p - 1)| ≤ 2 * p * K * ε * y ^ (-p - 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hp0, abs_of_pos r1p]
      calc |L1 y| * p * (1 + L y) ^ (p - 1) ≤ K * ε * y ^ (-p - 2) * p * 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_right bL1' hp0.le) r1 r1p.le (by positivity)
        _ = _ := by ring
    have T2 : |p * (1 + L y) ^ (p - 1) * L1 y| ≤ 2 * p * K * ε * y ^ (-p - 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hp0, abs_of_pos r1p]
      calc p * (1 + L y) ^ (p - 1) * |L1 y| ≤ p * 2 * (K * ε * y ^ (-p - 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left r1 hp0.le) bL1' (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have T3 : |p * y * (L1 y * (p - 1) * (1 + L y) ^ (p - 1 - 1)) * L1 y| ≤
        4 * p * K ^ 2 * ε * y ^ (-p - 2) := by
      rw [show p - 1 - 1 = p - 2 by ring]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hp0, abs_of_pos hyp,
        abs_of_pos r2p]
      calc p * y * (|L1 y| * |p - 1| * (1 + L y) ^ (p - 2)) * |L1 y|
          = p * |p - 1| * (1 + L y) ^ (p - 2) * (y * (|L1 y| * |L1 y|)) := by ring
        _ ≤ p * 1 * 4 * (y * ((K * ε) ^ 2 * (y ^ (-p - 2) * y ^ (-p - 2)))) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hp1' hp0.le) r2 r2p.le
              (by positivity)) (mul_le_mul_of_nonneg_left hL1sq hyp.le) (by positivity) (by positivity)
        _ = 4 * p * (K * ε) ^ 2 * (y * (y ^ (-p - 2) * y ^ (-p - 2))) := by ring
        _ ≤ 4 * p * (K ^ 2 * ε) * y ^ (-p - 2) := by
            have := mul_le_mul hKεsq e3 (by positivity) (by positivity)
            calc 4 * p * (K * ε) ^ 2 * (y * (y ^ (-p - 2) * y ^ (-p - 2)))
                = 4 * p * ((K * ε) ^ 2 * (y * (y ^ (-p - 2) * y ^ (-p - 2)))) := by ring
              _ ≤ 4 * p * (K ^ 2 * ε * y ^ (-p - 2)) := mul_le_mul_of_nonneg_left this (by positivity)
              _ = _ := by ring
        _ = _ := by ring
    have T4 : |p * y * (1 + L y) ^ (p - 1) * L2 y| ≤ 2 * p * K * ε * y ^ (-p - 2) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp0, abs_of_pos hyp, abs_of_pos r1p]
      calc p * y * (1 + L y) ^ (p - 1) * |L2 y| ≤ p * y * 2 * (K * ε * y ^ (-p - 3)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left r1 (by positivity)) bL2 (abs_nonneg _) (by positivity)
        _ = 2 * p * K * ε * (y * y ^ (-p - 3)) := by ring
        _ = _ := by rw [e2]
    have hsum := (abs_add_le _ _).trans (add_le_add T1 ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add T2 T3)) T4)))
    refine hsum.trans ?_
    rw [Nat.cast_one, show -p - 1 - 1 = -p - 2 by ring]
    have hd : 0 ≤ ((1 + 2 * p) * K + 1) * (ε * y ^ (-p - 2)) := by positivity
    linarith [hd, show ((1 + 2 * p) * K + 4 * p * K + 4 * p * K ^ 2 + 2 * p * K + 1) * ε *
      y ^ (-p - 2) = 2 * p * K * ε * y ^ (-p - 2) + (2 * p * K * ε * y ^ (-p - 2) +
        4 * p * K ^ 2 * ε * y ^ (-p - 2)) + 2 * p * K * ε * y ^ (-p - 2) +
        ((1 + 2 * p) * K + 1) * (ε * y ^ (-p - 2)) by ring]

/-- Helper: `|∂^k t^r| = |(r)_k| y^{r-k}` at `y > 0`. -/
theorem c05_aux_iter_rpow (r y : ℝ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => t ^ r) y = (descPochhammer ℝ k).eval r * y ^ (r - k) := by
  rw [iteratedDeriv_eq_iterate]; exact Real.iter_deriv_rpow_const r y k

/-- Helper: the chapter 04 bounds on `λ - λ₀`, `Ψ - Ψ₀` hold for every `y ≥ R₁` and every
admissible `(ε, μ)` (taking `R := y`). -/
theorem c05_aux_lp (S : c05_standing) :
    ∃ R₁ : ℝ, 2 ≤ R₁ ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ μ : ℂ, 0 ≤ ε → ε ≤ S.ε₀ →
      μ ∈ Bbar S.p S.δ → ∀ R y : ℝ, R₁ ≤ R → R ≤ y →
        |iteratedDeriv j (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) y| ≤
          C * ε * y ^ (1 / S.p - S.p - 1 - j) ∧
        |iteratedDeriv j (fun t => fam_Psi S.p R ε μ t - Psi0 S.p t) y| ≤
          C * ε * y ^ (1 / S.p - S.p - j) := by
  obtain ⟨-, R₁, hR₁, H⟩ :=
    Classical.choose_spec (c04_lambda_psi_difference S.p S.hp_lo S.hp_hi S.δ S.hδ S.hδ_le)
  refine ⟨R₁, hR₁, fun j => ?_⟩
  obtain ⟨C, hC, HC⟩ := H j
  exact ⟨C, hC, fun ε μ h0 h1 hμ R y hR hy =>
    HC R hR ε (c05_aux_eps_le S h0 h1).1 μ hμ y hy⟩

/-- Helper: `λ` is within `λ₀/10` of `λ₀` for `y ≥ R₂`, and `|∂^k λ| ≤ c_k y^{1/p-k}`. -/
theorem c05_aux_lam (S : c05_standing) :
    ∃ R₂ : ℝ, 2 ≤ R₂ ∧
      (∀ ε : ℝ, ∀ μ : ℂ, 0 ≤ ε → ε ≤ S.ε₀ → μ ∈ Bbar S.p S.δ → ∀ y : ℝ, R₂ ≤ y →
        |fam_lambda S.p ε μ y - y ^ (1 / S.p)| ≤ y ^ (1 / S.p) / 10) ∧
      ∀ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, ∀ μ : ℂ, 0 ≤ ε → ε ≤ S.ε₀ → μ ∈ Bbar S.p S.δ →
        ∀ y : ℝ, R₂ ≤ y → |iteratedDeriv k (fam_lambda S.p ε μ) y| ≤ c * y ^ (1 / S.p - k) := by
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  obtain ⟨R₁, hR₁, H⟩ := c05_aux_lp S
  obtain ⟨C0, hC0, H0⟩ := H 0
  refine ⟨max R₁ (10 * C0 + 2), le_trans hR₁ (le_max_left _ _), fun ε μ h0 h1 hμ y hy => ?_,
    fun k => ?_⟩
  · have hy1 : R₁ ≤ y := le_trans (le_max_left _ _) hy
    have hy2 : 10 * C0 + 2 ≤ y := le_trans (le_max_right _ _) hy
    have hyp : 0 < y := by linarith
    have h := (H0 ε μ h0 h1 hμ y y hy1 le_rfl).1
    rw [iteratedDeriv_zero] at h
    simp only [lambda0, Nat.cast_zero, sub_zero] at h
    have hε1 : ε ≤ 1 := h1.trans S.hε₀_le
    have e : y ^ (1 / S.p - S.p - 1) = y ^ (1 / S.p) * y ^ (-S.p - 1) := by
      rw [← Real.rpow_add hyp]; ring_nf
    have h2 : y ^ (-S.p - 1) ≤ y ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h2
    have h3 : C0 * y⁻¹ ≤ 1 / 10 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hyp]; linarith
    have hyq : 0 ≤ y ^ (1 / S.p) := Real.rpow_nonneg hyp.le _
    calc |fam_lambda S.p ε μ y - y ^ (1 / S.p)| ≤ C0 * ε * y ^ (1 / S.p - S.p - 1) := h
      _ ≤ C0 * 1 * (y ^ (1 / S.p) * y⁻¹) := by
          rw [e]; gcongr
      _ = y ^ (1 / S.p) * (C0 * y⁻¹) := by ring
      _ ≤ y ^ (1 / S.p) * (1 / 10) := mul_le_mul_of_nonneg_left h3 hyq
      _ = y ^ (1 / S.p) / 10 := by ring
  · obtain ⟨Ck, hCk, Hk⟩ := H k
    refine ⟨|(descPochhammer ℝ k).eval (1 / S.p)| + Ck, by positivity,
      fun ε μ h0 h1 hμ y hy => ?_⟩
    have hy1 : R₁ ≤ y := le_trans (le_max_left _ _) hy
    have hyp : 0 < y := by linarith
    have hε1 : ε ≤ 1 := h1.trans S.hε₀_le
    have h := (Hk ε μ h0 h1 hμ y y hy1 le_rfl).1
    have hsplit : fam_lambda S.p ε μ = (fun t : ℝ => t ^ (1 / S.p)) +
        (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) := by
      funext t; simp [lambda0]
    have hf1 : ContDiffAt ℝ k (fun t : ℝ => t ^ (1 / S.p)) y := c05_aux_rpow_at hyp
    have hf2 : ContDiffAt ℝ k (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) y :=
      (c05_aux_lambda_smooth S.p ε μ hyp).sub (c05_aux_rpow_at hyp)
    rw [hsplit, iteratedDeriv_add hf1 hf2, c05_aux_iter_rpow]
    have hm : y ^ (1 / S.p - S.p - 1 - k) ≤ y ^ (1 / S.p - k) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hyk : 0 ≤ y ^ (1 / S.p - k) := Real.rpow_nonneg hyp.le _
    calc |(descPochhammer ℝ k).eval (1 / S.p) * y ^ (1 / S.p - k) +
          iteratedDeriv k (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) y|
        ≤ |(descPochhammer ℝ k).eval (1 / S.p)| * y ^ (1 / S.p - k) +
          Ck * ε * y ^ (1 / S.p - S.p - 1 - k) := by
          refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) h)
          rw [abs_mul, abs_of_nonneg hyk]
      _ ≤ |(descPochhammer ℝ k).eval (1 / S.p)| * y ^ (1 / S.p - k) +
          Ck * 1 * y ^ (1 / S.p - k) := by gcongr
      _ = _ := by ring

/-- Helper: `2^{1/p} ≤ 3` and `(3/2)^{1/p} ≤ 9/4` for `3/4 < p < 1`. -/
theorem c05_aux_two_pow (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (2 : ℝ) ^ (1 / p) ≤ 3 ∧ (3 / 2 : ℝ) ^ (1 / p) ≤ 9 / 4 := by
  have hp0 : 0 < p := by linarith
  have hq : 1 / p ≤ 4 / 3 := by rw [div_le_iff₀ hp0]; linarith
  have hq2 : 1 / p ≤ 2 := by linarith
  constructor
  · have h1 : (2 : ℝ) ^ (1 / p) ≤ 2 ^ ((4 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
    have h2 : ((2 : ℝ) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h3 : (2 : ℝ) ^ ((4 : ℝ) / 3) ≤ 3 := by
      by_contra hc
      push_neg at hc
      have := pow_lt_pow_left₀ hc (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
      rw [h2] at this; norm_num at this
    linarith
  · calc (3 / 2 : ℝ) ^ (1 / p) ≤ (3 / 2) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
      _ = 9 / 4 := by norm_num

/-- Helper for lem:c05_symbol_bounds (6). -/
theorem c05_aux_item6 (S : c05_standing) :
    ∃ R₂ : ℝ, 2 ≤ R₂ ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ μ : ℂ, 0 ≤ ε → ε ≤ S.ε₀ →
      μ ∈ Bbar S.p S.δ → ∀ R y t : ℝ, R₂ ≤ R → R ≤ y → R ≤ t → |t - y| ≤ y / 2 →
        fam_lambda S.p ε μ y / 4 ≤ fam_lambda S.p ε μ t ∧
          fam_lambda S.p ε μ t ≤ 4 * fam_lambda S.p ε μ y ∧
          |fam_lambda S.p ε μ t - fam_lambda S.p ε μ y| ≤
            C * fam_lambda S.p ε μ y * |t - y| / y := by
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  obtain ⟨h2p, h32⟩ := c05_aux_two_pow S.p S.hp_lo S.hp_hi
  obtain ⟨R₂, hR₂, happ, hder⟩ := c05_aux_lam S
  obtain ⟨c1, hc1, H1⟩ := hder 1
  refine ⟨R₂, hR₂, 2 * c1, by positivity, fun ε μ h0 h1 hμ R y t hR hy ht hty => ?_⟩
  have hyR : R₂ ≤ y := hR.trans hy
  have htR : R₂ ≤ t := hR.trans ht
  have hyp : 0 < y := by linarith
  have htp : 0 < t := by linarith
  obtain ⟨hty1, hty2⟩ := abs_le.1 hty
  have ay := abs_le.1 (happ ε μ h0 h1 hμ y hyR)
  have at' := abs_le.1 (happ ε μ h0 h1 hμ t htR)
  set Y := y ^ (1 / S.p) with hY
  set T := t ^ (1 / S.p) with hT
  have hYp : 0 < Y := Real.rpow_pos_of_pos hyp _
  have hTl : Y / 3 ≤ T := by
    have h1' : (y / 2) ^ (1 / S.p) ≤ T := Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    rw [Real.div_rpow hyp.le (by norm_num)] at h1'
    have : Y / 3 ≤ Y / 2 ^ (1 / S.p) :=
      div_le_div_of_nonneg_left hYp.le (by positivity) h2p
    linarith
  have hTu : T ≤ 9 / 4 * Y := by
    have h1' : T ≤ (3 / 2 * y) ^ (1 / S.p) := Real.rpow_le_rpow htp.le (by linarith) (by positivity)
    rw [Real.mul_rpow (by norm_num) hyp.le] at h1'
    have := mul_le_mul_of_nonneg_right h32 hYp.le
    linarith
  have hlamy : 0 < fam_lambda S.p ε μ y := by linarith
  refine ⟨by linarith, by linarith, ?_⟩
  -- mean value theorem on `[min t y, max t y] ⊆ [R₂, 3y/2]`
  have hbound : ∀ τ ∈ uIcc t y, ‖deriv (fam_lambda S.p ε μ) τ‖ ≤ c1 * (3 / 2) * y ^ (1 / S.p - 1) := by
    intro τ hτ
    have hτ1 : min t y ≤ τ := (Set.mem_uIcc.1 hτ).elim (fun h => (min_le_left _ _).trans h.1)
      (fun h => (min_le_right _ _).trans h.1)
    have hτ2 : τ ≤ max t y := (Set.mem_uIcc.1 hτ).elim (fun h => h.2.trans (le_max_right _ _))
      (fun h => h.2.trans (le_max_left _ _))
    have hτR : R₂ ≤ τ := le_trans (le_min htR hyR) hτ1
    have hτp : 0 < τ := by linarith
    have hτu : τ ≤ 3 / 2 * y := hτ2.trans (max_le (by linarith) (by linarith))
    have h := H1 ε μ h0 h1 hμ τ hτR
    rw [iteratedDeriv_one, Nat.cast_one] at h
    rw [Real.norm_eq_abs]
    have he : 0 ≤ 1 / S.p - 1 := by rw [sub_nonneg, le_div_iff₀ hp0]; linarith [S.hp_hi]
    have he1 : 1 / S.p - 1 ≤ 1 := by
      have : 1 / S.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith [S.hp_lo]
      linarith
    have h2 : τ ^ (1 / S.p - 1) ≤ (3 / 2 * y) ^ (1 / S.p - 1) := Real.rpow_le_rpow hτp.le hτu he
    rw [Real.mul_rpow (by norm_num) hyp.le] at h2
    have h3 : (3 / 2 : ℝ) ^ (1 / S.p - 1) ≤ 3 / 2 := by
      calc (3 / 2 : ℝ) ^ (1 / S.p - 1) ≤ (3 / 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
        _ = 3 / 2 := Real.rpow_one _
    have hyq : 0 ≤ y ^ (1 / S.p - 1) := Real.rpow_nonneg hyp.le _
    calc |deriv (fam_lambda S.p ε μ) τ| ≤ c1 * τ ^ (1 / S.p - 1) := h
      _ ≤ c1 * ((3 / 2) * y ^ (1 / S.p - 1)) := by
          gcongr; exact h2.trans (mul_le_mul_of_nonneg_right h3 hyq)
      _ = _ := by ring
  have hdiff : ∀ τ ∈ uIcc t y, DifferentiableAt ℝ (fam_lambda S.p ε μ) τ := by
    intro τ hτ
    have hτ1 : min t y ≤ τ := (Set.mem_uIcc.1 hτ).elim (fun h => (min_le_left _ _).trans h.1)
      (fun h => (min_le_right _ _).trans h.1)
    have hτp : 0 < τ := lt_of_lt_of_le (lt_min htp hyp) hτ1
    exact (c05_aux_lambda_smooth S.p ε μ hτp (n := 1)).differentiableAt (by norm_num)
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (fun τ hτ => hdiff τ hτ) hbound
    (convex_uIcc t y) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm y t] at hmvt
  have hyq : y ^ (1 / S.p - 1) = Y / y := by
    rw [Real.rpow_sub_one hyp.ne', hY]
  rw [hyq] at hmvt
  have hYlam : Y ≤ 10 / 9 * fam_lambda S.p ε μ y := by linarith
  have hty0 : 0 ≤ |t - y| := abs_nonneg _
  calc |fam_lambda S.p ε μ t - fam_lambda S.p ε μ y| ≤ c1 * (3 / 2) * (Y / y) * |t - y| := by rw [abs_sub_comm]; exact hmvt
    _ = c1 * (3 / 2) * Y * |t - y| / y := by ring
    _ ≤ c1 * (3 / 2) * (10 / 9 * fam_lambda S.p ε μ y) * |t - y| / y := by gcongr
    _ ≤ 2 * c1 * fam_lambda S.p ε μ y * |t - y| / y := by
        apply div_le_div_of_nonneg_right _ hyp.le
        have : 0 ≤ c1 * fam_lambda S.p ε μ y * |t - y| := by positivity
        nlinarith

/-- Blueprint: lem:c05_symbol_bounds.  Symbol bounds for `λ`, `Ψ`, `A`, `A₀`, `a_*'`, `Z`,
`(μ/μ_*)Z₀`, `Z³`, `(λ^p)'`, `e^{i(Ψ-Ψ₀)}` on `[R,∞)` (items (1)–(6)); the constant may depend
on `k`. -/
theorem c05_symbol_bounds (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y → ∀ y : ℝ, R ≤ y →
        -- (1)
        (y ^ (1 / S.p) / 2 ≤ fam_lambda S.p ε μ y ∧ fam_lambda S.p ε μ y ≤ 2 * y ^ (1 / S.p) ∧
          |iteratedDeriv k (fam_lambda S.p ε μ) y| ≤ C * y ^ (1 / S.p - k) ∧
          |iteratedDeriv k (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) y| ≤
            C * ε * y ^ (1 / S.p - S.p - 1 - k) ∧
          |iteratedDeriv k (fun t => fam_Psi S.p R ε μ t - Psi0 S.p t) y| ≤
            C * ε * y ^ (1 / S.p - S.p - k)) ∧
        -- (2)
        (‖iteratedDeriv k (c05_standing_A S.p ε μ) y‖ +
              ‖iteratedDeriv k (c05_standing_A_zero S.p μ) y‖ ≤ C * y ^ (-beta S.p - k) ∧
          ‖iteratedDeriv k (fun t => c05_standing_A S.p ε μ t - c05_standing_A_zero S.p μ t) y‖ ≤
            C * ε * y ^ (-beta S.p - S.p - 1 - k) ∧
          ‖iteratedDeriv k (deriv (astar S.p)) y‖ ≤ C * y ^ (-2 * beta S.p - 1 - k)) ∧
        -- (3)
        (‖iteratedDeriv k (fam_Z S.p R ε μ) y‖ + ‖iteratedDeriv k (c05_standing_Zmu0 S.p R μ) y‖ ≤
            C * y ^ (-beta S.p + k / S.p) ∧
          ‖iteratedDeriv k (fun t => fam_Z S.p R ε μ t ^ 3) y‖ ≤ C * y ^ (-3 * beta S.p + k / S.p) ∧
          deriv (fam_Z S.p R ε μ) y - Complex.I * (fam_lambda S.p ε μ y : ℂ) * fam_Z S.p R ε μ y =
            deriv (c05_standing_A S.p ε μ) y *
              Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ y : ℂ)) ∧
          ‖deriv (fam_Z S.p R ε μ) y - Complex.I * (fam_lambda S.p ε μ y : ℂ) * fam_Z S.p R ε μ y‖ ≤
            C * y ^ (-beta S.p - 1)) ∧
        -- (4)
        (∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (fun t => deriv (fun u => fam_lambda S.p ε μ u ^ S.p) t - 1) y| ≤
            C * ε * y ^ (-S.p - 1 - j)) ∧
        -- (5)
        ‖Complex.exp (Complex.I * ((fam_Psi S.p R ε μ y - Psi0 S.p y : ℝ) : ℂ)) - 1‖ ≤
          C * ε * y ^ (1 / S.p - S.p) ∧
        -- (6)
        (∀ t : ℝ, R ≤ t → |t - y| ≤ y / 2 →
          fam_lambda S.p ε μ y / 4 ≤ fam_lambda S.p ε μ t ∧
            fam_lambda S.p ε μ t ≤ 4 * fam_lambda S.p ε μ y ∧
            |fam_lambda S.p ε μ t - fam_lambda S.p ε μ y| ≤ C * fam_lambda S.p ε μ y * |t - y| / y) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hδ := S.hδ
  have hδμ := S.hδ_le
  set q : ℝ := (S.p + 1) / 2 with hq
  have hq0 : 0 < q := by positivity
  have hqβ : ∀ k : ℝ, -q / S.p - k = -beta S.p - k := by
    intro k; rw [hq]; unfold beta; field_simp
  obtain ⟨R1, hR1, HLP⟩ := c05_aux_lp S
  obtain ⟨R2, hR2, happ, hlamder⟩ := c05_aux_lam S
  obtain ⟨R4, hR4, C4, hC4, H4⟩ := c05_aux_item4 S
  obtain ⟨R6, hR6, C6, hC6, H6⟩ := c05_aux_item6 S
  obtain ⟨-, RZ, hRZ, HZB, -⟩ := Classical.choose_spec (c04_Z_bounds S.p hp hp1 S.δ hδ hδμ)
  obtain ⟨-, RP, hRP, HZDP⟩ :=
    Classical.choose_spec (c04_Z_difference_products S.p hp hp1 S.δ hδ hδμ)
  obtain ⟨-, RD, hRD, HZD⟩ := Classical.choose_spec (c04_Z_difference S.p hp hp1 S.δ hδ hδμ)
  obtain ⟨-, -, -, -, -, ⟨y₀, hy₀, HAS⟩, -⟩ := approx_linear_seed S.p hp hp1
  set R₀ := max (max (max R1 R2) (max R4 R6)) (max (max RZ RP) (max RD y₀)) with hR₀
  have hR₀1 : 1 ≤ R₀ := by
    have : R1 ≤ R₀ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    linarith
  refine ⟨R₀, hR₀1, fun k => ?_⟩
  obtain ⟨Ck, hCk, Hk⟩ := HLP k
  obtain ⟨C0, hC0, H0⟩ := HLP 0
  obtain ⟨ck, hck, Hlk⟩ := hlamder k
  obtain ⟨CZ, hCZ, HZk⟩ := HZB k q hq0
  obtain ⟨CZ1, hCZ1, HZ1⟩ := HZB 1 q hq0
  obtain ⟨CP, hCP, HPk⟩ := HZDP 0 q hq0
  obtain ⟨CD, hCD, HDk⟩ := HZD (k - 1) q hq0
  obtain ⟨CA, hCA, HAk⟩ := HAS (k + 1)
  have hμs : 0 < ‖mu_star S.p‖ := norm_pos_iff.2 (c05_aux_mu_star_ne S.p hp0)
  set Mμ := ‖mu_star S.p‖ + S.δ with hMμ
  set Mq := Mμ / ‖mu_star S.p‖ with hMq
  have hMμ0 : 0 ≤ Mμ := by positivity
  have hMq0 : 0 ≤ Mq := by positivity
  set C := 1 + Ck + ck + C0 + C4 + C6 + 2 * Mμ * CZ + Mμ * CP + Mμ * CD + CA + CZ + Mq * CZ +
    Mμ * CZ1 + CP + CD with hC
  have n1 := mul_nonneg hMμ0 hCZ.le
  have n2 := mul_nonneg hMμ0 hCP.le
  have n3 := mul_nonneg hMμ0 hCD.le
  have n4 := mul_nonneg hMq0 hCZ.le
  have n5 := mul_nonneg hMμ0 hCZ1.le
  refine ⟨C, by positivity, fun ε μ R Y htup y hy => ?_⟩
  obtain ⟨hε0, hε1, hμ, hR0, -⟩ := htup
  have hRR : R1 ≤ R ∧ R2 ≤ R ∧ R4 ≤ R ∧ R6 ≤ R ∧ RZ ≤ R ∧ RP ≤ R ∧ RD ≤ R ∧ y₀ ≤ R := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine le_trans ?_ hR0 <;> simp [hR₀]
  obtain ⟨hR1R, hR2R, hR4R, hR6R, hRZR, hRPR, hRDR, hy₀R⟩ := hRR
  have hyp : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hyR2 : R2 ≤ y := hR2R.trans hy
  have hε := c05_aux_eps_le S hε0 hε1
  have hε00 := c05_aux_eps_le S le_rfl S.hε₀_pos.le
  have hμn : ‖μ‖ ≤ Mμ := by
    have h : dist μ (mu_star S.p) ≤ S.δ := hμ
    rw [dist_eq_norm] at h
    have := norm_le_norm_add_norm_sub' μ (mu_star S.p)
    rw [hMμ]; linarith
  have hμs_mem : mu_star S.p ∈ Bbar S.p S.δ := by
    show dist (mu_star S.p) (mu_star S.p) ≤ S.δ; rw [dist_self]; exact hδ.le
  have hypos : ∀ e : ℝ, 0 ≤ y ^ e := fun e => Real.rpow_nonneg hyp.le e
  have bump : ∀ (c X e : ℝ), c ≤ C → X ≤ c * y ^ e → X ≤ C * y ^ e := fun c X e hc h =>
    h.trans (mul_le_mul_of_nonneg_right hc (hypos e))
  have bumpε : ∀ (c X e : ℝ), c ≤ C → X ≤ c * ε * y ^ e → X ≤ C * ε * y ^ e := fun c X e hc h =>
    h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hε0) (hypos e))
  have hlampos : 0 < fam_lambda S.p ε μ y := by
    have := abs_le.1 (happ ε μ hε0 hε1 hμ y hyR2)
    have : 0 < y ^ (1 / S.p) := Real.rpow_pos_of_pos hyp _
    linarith
  -- the amplitudes as constant multiples
  have hexp : -(S.p + 1) / 2 = -q := by rw [hq]; ring
  have hA : c05_standing_A S.p ε μ =
      fun t => μ * (astar S.p t * ((fam_lambda S.p ε μ t ^ (-q) : ℝ) : ℂ)) := by
    funext t; simp only [c05_standing_A, hexp]; ring
  have hA0 : c05_standing_A_zero S.p μ =
      fun t => μ * (astar S.p t * ((fam_lambda S.p 0 μ t ^ (-q) : ℝ) : ℂ)) := by
    funext t; simp only [c05_standing_A_zero, lambda0, c05_aux_lambda_zero, hexp]; ring
  have hAd : (fun t => c05_standing_A S.p ε μ t - c05_standing_A_zero S.p μ t) =
      fun t => μ * (astar S.p t * ((fam_lambda S.p ε μ t ^ (-q) : ℝ) : ℂ) -
        astar S.p t * ((lambda0 S.p t ^ (-q) : ℝ) : ℂ)) := by
    funext t; simp only [c05_standing_A, c05_standing_A_zero, hexp]; ring
  have hZ0 : c05_standing_Zmu0 S.p R μ = fun t => μ / mu_star S.p * fam_Z S.p R 0 (mu_star S.p) t :=
    rfl
  have hμq : ‖μ / mu_star S.p‖ ≤ Mq := by
    rw [norm_div, hMq]; exact div_le_div_of_nonneg_right hμn hμs.le
  have hRpos : 0 < R := by linarith
  have hAdiff : DifferentiableAt ℝ (c05_standing_A S.p ε μ) y := by
    have : ContDiffAt ℝ 1 (c05_standing_A S.p ε μ) y := by
      unfold c05_standing_A
      exact (contDiffAt_const.mul (c05_aux_astar_smooth S.p hp hp1 hyp)).mul
        (c05_aux_ofReal ((c05_aux_lambda_smooth S.p ε μ hyp).rpow_const_of_ne hlampos.ne'))
    exact this.differentiableAt (by norm_num)
  have hΦ : HasDerivAt (fun t => ((c05_standing_Phi S.p R ε μ t : ℝ) : ℂ))
      (fam_lambda S.p ε μ y : ℂ) y :=
    ((c05_aux_Psi_hasDeriv S.p R ε μ hRpos hyp).sub_const (π / 4)).ofReal_comp
  have hE := (hΦ.const_mul Complex.I).cexp
  have hZeq : fam_Z S.p R ε μ = fun t => c05_standing_A S.p ε μ t *
      Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) := rfl
  have hid : deriv (fam_Z S.p R ε μ) y - Complex.I * (fam_lambda S.p ε μ y : ℂ) *
      fam_Z S.p R ε μ y = deriv (c05_standing_A S.p ε μ) y *
        Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ y : ℂ)) := by
    have hd : HasDerivAt (fun t => c05_standing_A S.p ε μ t *
        Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)))
        (deriv (c05_standing_A S.p ε μ) y *
            Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ y : ℂ)) +
          c05_standing_A S.p ε μ y * (Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ y : ℂ)) *
            (Complex.I * (fam_lambda S.p ε μ y : ℂ)))) y := hAdiff.hasDerivAt.mul hE
    rw [hZeq, hd.deriv]; ring
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, hid, ?_⟩, ?_, ?_, ?_⟩
  -- (1)
  · have := abs_le.1 (happ ε μ hε0 hε1 hμ y hyR2)
    have : 0 ≤ y ^ (1 / S.p) := hypos _
    linarith
  · have := abs_le.1 (happ ε μ hε0 hε1 hμ y hyR2)
    have : 0 ≤ y ^ (1 / S.p) := hypos _
    linarith
  · exact bump ck _ _ (by linarith) (Hlk ε μ hε0 hε1 hμ y hyR2)
  · exact bumpε Ck _ _ (by linarith) (Hk ε μ hε0 hε1 hμ R y hR1R hy).1
  · exact bumpε Ck _ _ (by linarith) (Hk ε μ hε0 hε1 hμ R y hR1R hy).2
  -- (2)
  · rw [hA, hA0, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, norm_mul, norm_mul]
    have h1 := (HZk R hRZR ε hε.2.1 μ hμ y hy).2.2.2
    have h2 := (HZk R hRZR 0 hε00.2.1 μ hμ y hy).2.2.2
    rw [hqβ] at h1 h2
    have e1 := mul_le_mul hμn h1 (norm_nonneg _) hMμ0
    have e2 := mul_le_mul hμn h2 (norm_nonneg _) hMμ0
    refine bump (2 * Mμ * CZ) _ _ (by linarith) ?_
    linarith
  · rw [hAd]
    cases k with
    | zero =>
      have h := ((HPk R hRPR ε hε.2.2.1 μ hμ).2.2.2.2 y hy).1
      rw [iteratedDeriv_zero] at h ⊢
      rw [norm_mul, c04_aux_norm_exp_I, mul_one] at h
      rw [show -q / S.p - S.p - 1 + ((0 : ℕ) : ℝ) / S.p = -beta S.p - S.p - 1 - ((0 : ℕ) : ℝ) by
        rw [Nat.cast_zero, zero_div, add_zero, sub_zero]
        have := hqβ (S.p + 1); linarith] at h
      exact bumpε CP _ _ (by linarith) h
    | succ j =>
      have h := (HDk R hRDR ε hε.2.2.2.1 μ hμ y hy).2.1
      simp only [Nat.add_sub_cancel] at h
      rw [show -q / S.p - S.p - 2 - (j : ℝ) = -beta S.p - S.p - 1 - ((j + 1 : ℕ) : ℝ) by
        have := hqβ (S.p + 2 + j); push_cast; linarith] at h
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_succ', norm_mul]
      refine bumpε (Mμ * CD) _ _ (by linarith) ?_
      calc ‖μ‖ * ‖iteratedDeriv j (deriv fun t => astar S.p t *
            ((fam_lambda S.p ε μ t ^ (-q) : ℝ) : ℂ) - astar S.p t * ((lambda0 S.p t ^ (-q) : ℝ) : ℂ)) y‖
          ≤ Mμ * (CD * ε * y ^ (-beta S.p - S.p - 1 - ((j + 1 : ℕ) : ℝ))) :=
            mul_le_mul hμn h (norm_nonneg _) hMμ0
        _ = _ := by ring
  · have hd : iteratedDeriv k (deriv (astar S.p)) = iteratedDeriv (k + 1) (fun t => astar S.p t - 1) := by
      rw [iteratedDeriv_succ']; congr 1; funext t; rw [deriv_sub_const]
    rw [hd]
    have h := (HAk).1 y (hy₀R.trans hy)
    rw [show -2 * beta S.p - ((k + 1 : ℕ) : ℝ) = -2 * beta S.p - 1 - (k : ℝ) by push_cast; ring] at h
    exact bump CA _ _ (by linarith) h
  -- (3)
  · rw [hZ0, iteratedDeriv_const_mul_field, norm_mul]
    have h1 := (HZk R hRZR ε hε.2.1 μ hμ y hy).1
    have h2 := (HZk R hRZR 0 hε00.2.1 (mu_star S.p) hμs_mem y hy).1
    have e2 := mul_le_mul hμq h2 (norm_nonneg _) hMq0
    refine bump (CZ + Mq * CZ) _ _ (by linarith) ?_
    linarith
  · exact bump CZ _ _ (by linarith) (HZk R hRZR ε hε.2.1 μ hμ y hy).2.1
  · rw [hid, norm_mul, c04_aux_norm_exp_I, mul_one]
    have hdA : deriv (c05_standing_A S.p ε μ) y =
        μ * iteratedDeriv 1 (fun t => astar S.p t * ((fam_lambda S.p ε μ t ^ (-q) : ℝ) : ℂ)) y := by
      rw [hA, ← iteratedDeriv_one, iteratedDeriv_const_mul_field]
    rw [hdA, norm_mul]
    have h := (HZ1 R hRZR ε hε.2.1 μ hμ y hy).2.2.2
    rw [Nat.cast_one, hqβ] at h
    refine bump (Mμ * CZ1) _ _ (by linarith) ?_
    calc ‖μ‖ * ‖iteratedDeriv 1 (fun t => astar S.p t * ((fam_lambda S.p ε μ t ^ (-q) : ℝ) : ℂ)) y‖
        ≤ Mμ * (CZ1 * y ^ (-beta S.p - 1)) := mul_le_mul hμn h (norm_nonneg _) hMμ0
      _ = _ := by ring
  -- (4)
  · intro j hj
    exact (H4 ε μ hε0 hε1 hμ y (hR4R.trans hy) j hj).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε0) (hypos _))
  -- (5)
  · refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs]
    have h := (H0 ε μ hε0 hε1 hμ R y hR1R hy).2
    rw [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
    exact bumpε C0 _ _ (by linarith) h
  -- (6)
  · intro t ht hty
    obtain ⟨h1, h2, h3⟩ := H6 ε μ hε0 hε1 hμ R y t hR6R hy ht hty
    refine ⟨h1, h2, h3.trans ?_⟩
    apply div_le_div_of_nonneg_right _ hyp.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hlampos.le)
      (abs_nonneg _)

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_ibp_Ioi {f a e : ℝ → ℂ} {z K r : ℝ} (hz : 0 < z) (hr : 0 < r)
    (hd : ∀ t, z ≤ t → HasDerivAt (fun s => a s * e s) (f t + e t * deriv a t) t)
    (hf : IntegrableOn f (Ioi z)) (he : ∀ t, ‖e t‖ = 1)
    (ha : ∀ t, z ≤ t → ‖a t‖ ≤ K * t ^ (-r))
    (ha' : ∀ t, z ≤ t → ‖deriv a t‖ ≤ K * t ^ (-r - 1)) :
    IntegrableOn (fun t => e t * deriv a t) (Ioi z) ∧
      ∫ t in Ioi z, f t = -(a z * e z) - ∫ t in Ioi z, e t * deriv a t ∧
      ‖∫ t in Ioi z, f t‖ ≤ K * (1 + 1 / r) * z ^ (-r) := by
  set G := fun s => a s * e s with hG
  have hr1 : -r - 1 < -1 := by linarith
  obtain ⟨hbi, hbint⟩ := c05_aux_int_Ioi_rpow K (-r - 1) z hr1 hz
  have hmeas : AEStronglyMeasurable (fun t => e t * deriv a t) (volume.restrict (Ioi z)) := by
    have h1 : AEStronglyMeasurable (fun t => deriv G t - f t) (volume.restrict (Ioi z)) :=
      (measurable_deriv G).aestronglyMeasurable.sub hf.aestronglyMeasurable
    refine h1.congr ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    simp only
    rw [(hd t (le_of_lt ht)).deriv]; ring
  have hgi : IntegrableOn (fun t => e t * deriv a t) (Ioi z) := by
    refine Integrable.mono' hbi hmeas ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    rw [norm_mul, he, one_mul]; exact ha' t (le_of_lt ht)
  have hlim : Tendsto G atTop (nhds 0) := by
    have h0 : Tendsto (fun t : ℝ => K * t ^ (-r)) atTop (nhds (K * 0)) :=
      (tendsto_rpow_neg_atTop hr).const_mul K
    rw [mul_zero] at h0
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop z] with t ht
    simp only [hG, norm_mul, he, mul_one]; exact ha t ht
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto
    (hd z le_rfl).continuousAt.continuousWithinAt (fun t ht => hd t (le_of_lt ht))
    (hf.add hgi) hlim
  rw [integral_add hf hgi, zero_sub] at hint
  have hid : ∫ t in Ioi z, f t = -(a z * e z) - ∫ t in Ioi z, e t * deriv a t := by
    rw [eq_sub_iff_add_eq, hint]
  refine ⟨hgi, hid, ?_⟩
  have hgn : ‖∫ t in Ioi z, e t * deriv a t‖ ≤ K * (-z ^ (-r - 1 + 1) / (-r - 1 + 1)) := by
    rw [← hbint]
    refine norm_integral_le_of_norm_le hbi ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    rw [norm_mul, he, one_mul]; exact ha' t (le_of_lt ht)
  have hz0 : -r - 1 + 1 = -r := by ring
  rw [hz0] at hgn
  have hzr : 0 < z ^ (-r) := Real.rpow_pos_of_pos hz _
  rw [hid]
  calc ‖-(a z * e z) - ∫ t in Ioi z, e t * deriv a t‖
      ≤ ‖a z * e z‖ + ‖∫ t in Ioi z, e t * deriv a t‖ := by
        rw [sub_eq_add_neg]; refine (norm_add_le _ _).trans ?_; rw [norm_neg, norm_neg]
    _ ≤ K * z ^ (-r) + K * (-z ^ (-r) / -r) := by
        rw [norm_mul, he, mul_one]; exact add_le_add (ha z le_rfl) hgn
    _ = K * (1 + 1 / r) * z ^ (-r) := by field_simp
/-- Helper for lem:c05_primitive. -/
theorem c05_aux_quot_bound {B : ℝ → ℂ} {l : ℝ → ℝ} {B' : ℂ} {l' c : ℂ} {t p K r : ℝ}
    (hB : HasDerivAt B B' t) (hl : HasDerivAt l l'.re t) (hl'r : l' = (l'.re : ℂ))
    (hc : 1 ≤ ‖c‖) (ht : 0 < t) (hK : 0 ≤ K)
    (hlow : t ^ (1 / p) / 2 ≤ l t) (hBn : ‖B t‖ ≤ K * t ^ (-r)) (hB'n : ‖B'‖ ≤ K * t ^ (-r - 1))
    (hl'n : ‖l'‖ ≤ K * t ^ (1 / p - 1)) :
    ‖B t / (c * (l t : ℂ))‖ ≤ 2 * K * t ^ (-(r + 1 / p)) ∧
      HasDerivAt (fun s => B s / (c * (l s : ℂ)))
        ((B' * (c * (l t : ℂ)) - B t * (c * l')) / (c * (l t : ℂ)) ^ 2) t ∧
      ‖(B' * (c * (l t : ℂ)) - B t * (c * l')) / (c * (l t : ℂ)) ^ 2‖ ≤
        (2 * K + 4 * K ^ 2) * t ^ (-(r + 1 / p) - 1) := by
  set u := t ^ (1 / p) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht _
  have hlpos : 0 < l t := by linarith [half_pos hu0]
  have hc0 : 0 < ‖c‖ := by linarith
  have hil : (l t)⁻¹ ≤ 2 / u := by
    rw [inv_le_comm₀ hlpos (by positivity)]; rw [inv_div]; linarith
  have hil0 : 0 ≤ (l t)⁻¹ := by positivity
  have e1 : t ^ (-(r + 1 / p)) = t ^ (-r) / u := by
    rw [hu, neg_add, Real.rpow_add ht, Real.rpow_neg ht.le (1 / p), ← div_eq_mul_inv]
  have e2 : t ^ (-(r + 1 / p) - 1) = t ^ (-r - 1) / u := by
    rw [hu, show -(r + 1 / p) - 1 = (-r - 1) + -(1 / p) by ring, Real.rpow_add ht,
      Real.rpow_neg ht.le (1 / p), ← div_eq_mul_inv]
  have e3 : t ^ (1 / p - 1) * t ^ (-r) = u * t ^ (-r - 1) := by
    rw [hu, ← Real.rpow_add ht, ← Real.rpow_add ht]; ring_nf
  have hX : 0 ≤ t ^ (-r) := (Real.rpow_pos_of_pos ht _).le
  have hX1 : 0 ≤ t ^ (-r - 1) := (Real.rpow_pos_of_pos ht _).le
  have hcl : c * (l t : ℂ) ≠ 0 := mul_ne_zero (norm_pos_iff.mp hc0) (by exact_mod_cast hlpos.ne')
  have hncl : ‖c * (l t : ℂ)‖ = ‖c‖ * l t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlpos]
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_div, hncl, e1, div_eq_mul_inv, mul_inv]
    have : ‖c‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
    calc ‖B t‖ * (‖c‖⁻¹ * (l t)⁻¹) ≤ (K * t ^ (-r)) * (1 * (2 / u)) := by
          gcongr
      _ = 2 * K * (t ^ (-r) / u) := by ring
  · have hl2 : HasDerivAt (fun s => c * (l s : ℂ)) (c * l') t := by
      have := (hl.ofReal_comp).const_mul c
      rw [hl'r]; simpa using this
    exact hB.div hl2 hcl
  · rw [norm_div, norm_pow, hncl, e2]
    have hnum : ‖B' * (c * (l t : ℂ)) - B t * (c * l')‖ ≤ ‖c‖ * (‖B'‖ * l t + ‖B t‖ * ‖l'‖) := by
      calc _ ≤ ‖B' * (c * (l t : ℂ))‖ + ‖B t * (c * l')‖ := norm_sub_le _ _
        _ = ‖c‖ * (‖B'‖ * l t + ‖B t‖ * ‖l'‖) := by
          rw [norm_mul B', hncl, norm_mul, norm_mul]; ring
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ ‖c‖ * (‖B'‖ * l t + ‖B t‖ * ‖l'‖) := hnum
      _ ≤ ‖c‖ ^ 2 * (‖B'‖ * l t + ‖B t‖ * ‖l'‖) := by
          gcongr; nlinarith
      _ ≤ ‖c‖ ^ 2 * ((2 * K + 4 * K ^ 2) * (t ^ (-r - 1) / u) * l t ^ 2) := by
          gcongr
          -- ‖B'‖ l + ‖B‖‖l'‖ ≤ (2K+4K²) X1/u · l²
          have hA : ‖B'‖ * l t ≤ 2 * K * (t ^ (-r - 1) / u) * l t ^ 2 := by
            have : 1 ≤ 2 / u * l t := by
              rw [div_mul_eq_mul_div, le_div_iff₀ hu0]; linarith
            calc ‖B'‖ * l t ≤ K * t ^ (-r - 1) * l t := by gcongr
              _ = K * t ^ (-r - 1) * l t * 1 := by ring
              _ ≤ K * t ^ (-r - 1) * l t * (2 / u * l t) := by gcongr
              _ = _ := by ring
          have hB2 : ‖B t‖ * ‖l'‖ ≤ 4 * K ^ 2 * (t ^ (-r - 1) / u) * l t ^ 2 := by
            have h4 : 1 ≤ (2 / u * l t) ^ 2 := by
              have : 1 ≤ 2 / u * l t := by
                rw [div_mul_eq_mul_div, le_div_iff₀ hu0]; linarith
              nlinarith
            calc ‖B t‖ * ‖l'‖ ≤ (K * t ^ (-r)) * (K * t ^ (1 / p - 1)) := by gcongr
              _ = K ^ 2 * (u * t ^ (-r - 1)) := by rw [← e3]; ring
              _ = K ^ 2 * (u * t ^ (-r - 1)) * 1 := by ring
              _ ≤ K ^ 2 * (u * t ^ (-r - 1)) * (2 / u * l t) ^ 2 := by gcongr
              _ = 4 * K ^ 2 * (t ^ (-r - 1) / u) * l t ^ 2 := by field_simp; ring
          linarith
      _ = _ := by ring

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_norm_exp_re0 {c : ℂ} (hc : c.re = 0) (x : ℝ) : ‖Complex.exp (c * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp [Complex.mul_re, hc]

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_prim_generic {B : ℝ → ℂ} {l Φ : ℝ → ℝ} {c : ℂ} {z p K r : ℝ}
    (hc : c.re = 0) (hc1 : 1 ≤ ‖c‖) (hz : 0 < z) (hK : 0 ≤ K) (hr : 1 < r) (hp : 0 < p)
    (hB : ∀ t, z ≤ t → HasDerivAt B (deriv B t) t)
    (hl : ∀ t, z ≤ t → HasDerivAt l (deriv l t) t)
    (hΦ : ∀ t, z ≤ t → HasDerivAt Φ (l t) t)
    (hlow : ∀ t, z ≤ t → t ^ (1 / p) / 2 ≤ l t)
    (hBn : ∀ t, z ≤ t → ‖B t‖ ≤ K * t ^ (-r))
    (hB'n : ∀ t, z ≤ t → ‖deriv B t‖ ≤ K * t ^ (-r - 1))
    (hl'n : ∀ t, z ≤ t → |deriv l t| ≤ K * t ^ (1 / p - 1)) :
    IntegrableOn (fun t => B t * Complex.exp (c * (Φ t : ℂ))) (Ioi z) ∧
    IntegrableOn (fun t => Complex.exp (c * (Φ t : ℂ)) *
      deriv (fun s => B s / (c * (l s : ℂ))) t) (Ioi z) ∧
    ∫ t in Ioi z, B t * Complex.exp (c * (Φ t : ℂ)) =
      -(B z * Complex.exp (c * (Φ z : ℂ)) / (c * (l z : ℂ))) -
        ∫ t in Ioi z, Complex.exp (c * (Φ t : ℂ)) * deriv (fun s => B s / (c * (l s : ℂ))) t ∧
    ‖∫ t in Ioi z, B t * Complex.exp (c * (Φ t : ℂ))‖ ≤
      (2 * K + 4 * K ^ 2) * (1 + 1 / (r + 1 / p)) * z ^ (-(r + 1 / p)) := by
  set e : ℝ → ℂ := fun t => Complex.exp (c * (Φ t : ℂ)) with he
  set a : ℝ → ℂ := fun s => B s / (c * (l s : ℂ)) with ha
  have hen : ∀ t, ‖e t‖ = 1 := fun t => c05_aux_norm_exp_re0 hc (Φ t)
  have hQ : ∀ t, z ≤ t → ‖a t‖ ≤ 2 * K * t ^ (-(r + 1 / p)) ∧
      HasDerivAt a (deriv a t) t ∧ ‖deriv a t‖ ≤ (2 * K + 4 * K ^ 2) * t ^ (-(r + 1 / p) - 1) := by
    intro t ht
    have ht0 : 0 < t := hz.trans_le ht
    have hl' := hl t ht
    have := c05_aux_quot_bound (c := c) (l' := ((deriv l t : ℝ) : ℂ)) (hB t ht)
      (by simpa using hl') (by simp) hc1 ht0 hK (hlow t ht) (hBn t ht) (hB'n t ht)
      (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hl'n t ht)
    obtain ⟨h1, h2, h3⟩ := this
    refine ⟨h1, ?_, ?_⟩
    · rw [h2.deriv]; exact h2
    · rw [h2.deriv]; exact h3
  have hcont : ∀ t, z ≤ t → ContinuousAt (fun t => B t * e t) t := by
    intro t ht
    exact (hB t ht).continuousAt.mul
      (((hΦ t ht).ofReal_comp.continuousAt.const_mul c).cexp)
  have hfi : IntegrableOn (fun t => B t * e t) (Ioi z) := by
    have hbi := (c05_aux_int_Ioi_rpow K (-r) z (by linarith) hz).1
    refine Integrable.mono' hbi ?_ ?_
    · exact (ContinuousOn.aestronglyMeasurable (fun t ht => (hcont t (le_of_lt ht)).continuousWithinAt)
        measurableSet_Ioi)
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      rw [norm_mul, hen, mul_one]; exact hBn t (le_of_lt ht)
  have hK' : 2 * K ≤ 2 * K + 4 * K ^ 2 := by nlinarith
  have hd : ∀ t, z ≤ t → HasDerivAt (fun s => a s * e s) (B t * e t + e t * deriv a t) t := by
    intro t ht
    have ht0 : 0 < t := hz.trans_le ht
    have hlpos : 0 < l t := by
      have := hlow t ht; have : 0 < t ^ (1 / p) / 2 := by positivity
      linarith
    have hed : HasDerivAt e (e t * (c * (l t : ℂ))) t := by
      have := ((hΦ t ht).ofReal_comp.const_mul c).cexp
      simpa [he] using this
    have := (hQ t ht).2.1.mul hed
    convert this using 1
    have hne : c * (l t : ℂ) ≠ 0 :=
      mul_ne_zero (by intro h; rw [h, norm_zero] at hc1; linarith) (by exact_mod_cast hlpos.ne')
    have key : a t * (c * (l t : ℂ)) = B t := div_mul_cancel₀ _ hne
    rw [show a t * (e t * (c * ↑(l t))) = B t * e t by rw [← key]; ring]; ring
  obtain ⟨h1, h2, h3⟩ := c05_aux_ibp_Ioi (f := fun t => B t * e t) (a := a) (e := e)
    (K := 2 * K + 4 * K ^ 2) (r := r + 1 / p) hz (by have := one_div_pos.mpr hp; linarith) hd hfi hen
    (fun t ht => (hQ t ht).1.trans (mul_le_mul_of_nonneg_right hK' (Real.rpow_pos_of_pos (hz.trans_le ht) _).le))
    (fun t ht => (hQ t ht).2.2)
  refine ⟨hfi, h1, ?_, h3⟩
  rw [h2]; congr 1; simp only [ha]; ring

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_Psi_zero (p R : ℝ) (μ : ℂ) (hp : 0 < p) (t : ℝ) :
    fam_Psi p R 0 μ t = Psi0 p t := by
  unfold fam_Psi
  simp_rw [c05_aux_lambda_zero]
  rw [integral_rpow (Or.inl (by have := one_div_pos.mpr hp; linarith))]
  unfold Psi0
  rw [show (1 : ℝ) + 1 / p = 1 / p + 1 by ring]
  have : 1 / p + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_Zmu0_eq (p R : ℝ) (μ : ℂ) (hp : 0 < p) (t : ℝ) :
    c05_standing_Zmu0 p R μ t =
      c05_standing_A_zero p μ t * Complex.exp (Complex.I * (c05_standing_Phi_zero p t : ℂ)) := by
  unfold c05_standing_Zmu0 fam_Z0 fam_Z c05_standing_A_zero c05_standing_Phi_zero
  rw [c05_aux_lambda_zero, c05_aux_Psi_zero p R _ hp]
  have := c05_aux_mu_star_ne p hp
  unfold lambda0
  field_simp

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_A_diff (p ε : ℝ) (μ : ℂ) (hp : 3 / 4 < p) (hp1 : p < 1) {t : ℝ} (ht : 0 < t)
    (hl : 0 < fam_lambda p ε μ t) : DifferentiableAt ℝ (c05_standing_A p ε μ) t := by
  have : ContDiffAt ℝ 1 (c05_standing_A p ε μ) t := by
    unfold c05_standing_A
    exact (contDiffAt_const.mul (c05_aux_astar_smooth p hp hp1 ht)).mul
      (c05_aux_ofReal ((c05_aux_lambda_smooth p ε μ ht).rpow_const_of_ne hl.ne'))
  exact this.differentiableAt one_ne_zero

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_A0_diff (p : ℝ) (μ : ℂ) (hp : 3 / 4 < p) (hp1 : p < 1) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (c05_standing_A_zero p μ) t := by
  have : ContDiffAt ℝ 1 (c05_standing_A_zero p μ) t := by
    unfold c05_standing_A_zero lambda0
    exact (contDiffAt_const.mul (c05_aux_astar_smooth p hp hp1 ht)).mul
      (c05_aux_ofReal ((c05_aux_rpow_at ht).rpow_const_of_ne (Real.rpow_pos_of_pos ht _).ne'))
  exact this.differentiableAt one_ne_zero

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_lambda0_hasDeriv (p : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (lambda0 p) ((1 / p) * t ^ (1 / p - 1)) t := by
  unfold lambda0
  exact Real.hasDerivAt_rpow_const (Or.inl ht.ne')

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_Phi0_hasDeriv (p : ℝ) (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (c05_standing_Phi_zero p) (lambda0 p t) t := by
  unfold c05_standing_Phi_zero Psi0 lambda0
  have := ((Real.hasDerivAt_rpow_const (p := 1 + 1 / p) (Or.inl ht.ne')).const_mul (p / (p + 1))).sub_const (π / 4)
  convert this using 1
  rw [show 1 + 1 / p - 1 = 1 / p by ring]
  field_simp

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_prim_const {K r p X : ℝ} (hK : 0 ≤ K) (hr : 1 ≤ r) (hp : 0 < p) (hX : 0 ≤ X) :
    (2 * K + 4 * K ^ 2) * (1 + 1 / (r + 1 / p)) * X ≤ (2 * (2 * K + 4 * K ^ 2) + 1) * X := by
  have h1 : 1 / (r + 1 / p) ≤ 1 := by
    rw [div_le_one (by positivity)]; have := one_div_pos.mpr hp; linarith
  have h2 : 0 ≤ 2 * K + 4 * K ^ 2 := by positivity
  have : (2 * K + 4 * K ^ 2) * (1 + 1 / (r + 1 / p)) ≤ 2 * (2 * K + 4 * K ^ 2) + 1 := by
    nlinarith
  exact mul_le_mul_of_nonneg_right this hX

/-- Helper for lem:c05_primitive. -/
theorem c05_aux_cube_bounds {A : ℝ → ℂ} {t C0 C1 b : ℝ} (ht : 0 < t) (hA : DifferentiableAt ℝ A t)
    (hA0 : ‖A t‖ ≤ C0 * t ^ (-b)) (hA1 : ‖deriv A t‖ ≤ C1 * t ^ (-b - 1)) (hC0 : 0 ≤ C0) :
    HasDerivAt (fun s => A s ^ 3) (deriv (fun s => A s ^ 3) t) t ∧
    ‖A t ^ 3‖ ≤ C0 ^ 3 * t ^ (-(3 * b)) ∧
    ‖deriv (fun s => A s ^ 3) t‖ ≤ 3 * C0 ^ 2 * C1 * t ^ (-(3 * b) - 1) := by
  have hd := hA.hasDerivAt.fun_pow 3
  have hX : 0 ≤ t ^ (-b) := (Real.rpow_pos_of_pos ht _).le
  have e1 : (t ^ (-b)) ^ 3 = t ^ (-(3 * b)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; push_cast; ring_nf
  have e2 : (t ^ (-b)) ^ 2 * t ^ (-b - 1) = t ^ (-(3 * b) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]; push_cast; ring_nf
  refine ⟨by rw [hd.deriv]; exact hd, ?_, ?_⟩
  · rw [norm_pow, ← e1, ← mul_pow]; gcongr
  · rw [hd.deriv, norm_mul, norm_mul, norm_pow]
    have h3 : ‖((3 : ℕ) : ℂ)‖ = 3 := by simp
    rw [h3, show 3 - 1 = 2 by rfl, ← e2]
    have h4 : ‖A t‖ ^ 2 ≤ (C0 * t ^ (-b)) ^ 2 := by gcongr
    calc 3 * ‖A t‖ ^ 2 * ‖deriv A t‖ ≤ 3 * (C0 * t ^ (-b)) ^ 2 * (C1 * t ^ (-b - 1)) := by gcongr
      _ = _ := by ring

/-- Blueprint: lem:c05_primitive.  Convergence (absolute) of `∫_z^∞ Z`, `∫_z^∞ Z³`, the
integration-by-parts identities and the bounds `|∫_z^∞ Z| ≤ C z^{-β-1/p}`,
`|∫_z^∞ Z³| ≤ C z^{-3β-1/p}`; the same for `((μ/μ_*)Z₀, A₀, Φ₀, λ₀)`. -/
theorem c05_primitive (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y → ∀ z : ℝ, R ≤ z →
        -- the quantities `(Z, A, Φ, λ)`
        (IntegrableOn (fam_Z S.p R ε μ) (Ioi z) ∧
          IntegrableOn (fun t => fam_Z S.p R ε μ t ^ 3) (Ioi z) ∧
          IntegrableOn (fun t => Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) *
            deriv (fun s => c05_standing_A S.p ε μ s / (Complex.I * (fam_lambda S.p ε μ s : ℂ))) t)
            (Ioi z) ∧
          IntegrableOn (fun t => Complex.exp (3 * Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) *
            deriv (fun s => c05_standing_A S.p ε μ s ^ 3 /
              (3 * Complex.I * (fam_lambda S.p ε μ s : ℂ))) t) (Ioi z) ∧
          ∫ t in Ioi z, fam_Z S.p R ε μ t =
            -(fam_Z S.p R ε μ z / (Complex.I * (fam_lambda S.p ε μ z : ℂ))) -
              ∫ t in Ioi z, Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) *
                deriv (fun s => c05_standing_A S.p ε μ s /
                  (Complex.I * (fam_lambda S.p ε μ s : ℂ))) t ∧
          ∫ t in Ioi z, fam_Z S.p R ε μ t ^ 3 =
            -(fam_Z S.p R ε μ z ^ 3 / (3 * Complex.I * (fam_lambda S.p ε μ z : ℂ))) -
              ∫ t in Ioi z, Complex.exp (3 * Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) *
                deriv (fun s => c05_standing_A S.p ε μ s ^ 3 /
                  (3 * Complex.I * (fam_lambda S.p ε μ s : ℂ))) t ∧
          ‖∫ t in Ioi z, fam_Z S.p R ε μ t‖ ≤ C * z ^ (-beta S.p - 1 / S.p) ∧
          ‖∫ t in Ioi z, fam_Z S.p R ε μ t ^ 3‖ ≤ C * z ^ (-3 * beta S.p - 1 / S.p)) ∧
        -- the quantities `((μ/μ_*)Z₀, A₀, Φ₀, λ₀)`
        (IntegrableOn (c05_standing_Zmu0 S.p R μ) (Ioi z) ∧
          IntegrableOn (fun t => c05_standing_Zmu0 S.p R μ t ^ 3) (Ioi z) ∧
          IntegrableOn (fun t => Complex.exp (Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) *
            deriv (fun s => c05_standing_A_zero S.p μ s / (Complex.I * (lambda0 S.p s : ℂ))) t)
            (Ioi z) ∧
          IntegrableOn (fun t => Complex.exp (3 * Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) *
            deriv (fun s => c05_standing_A_zero S.p μ s ^ 3 /
              (3 * Complex.I * (lambda0 S.p s : ℂ))) t) (Ioi z) ∧
          ∫ t in Ioi z, c05_standing_Zmu0 S.p R μ t =
            -(c05_standing_Zmu0 S.p R μ z / (Complex.I * (lambda0 S.p z : ℂ))) -
              ∫ t in Ioi z, Complex.exp (Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) *
                deriv (fun s => c05_standing_A_zero S.p μ s /
                  (Complex.I * (lambda0 S.p s : ℂ))) t ∧
          ∫ t in Ioi z, c05_standing_Zmu0 S.p R μ t ^ 3 =
            -(c05_standing_Zmu0 S.p R μ z ^ 3 / (3 * Complex.I * (lambda0 S.p z : ℂ))) -
              ∫ t in Ioi z, Complex.exp (3 * Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) *
                deriv (fun s => c05_standing_A_zero S.p μ s ^ 3 /
                  (3 * Complex.I * (lambda0 S.p s : ℂ))) t ∧
          ‖∫ t in Ioi z, c05_standing_Zmu0 S.p R μ t‖ ≤ C * z ^ (-beta S.p - 1 / S.p) ∧
          ‖∫ t in Ioi z, c05_standing_Zmu0 S.p R μ t ^ 3‖ ≤ C * z ^ (-3 * beta S.p - 1 / S.p)) := by
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C0, hC0, hs0⟩ := hsym 0
  obtain ⟨C1, hC1, hs1⟩ := hsym 1
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hip2 : 1 / S.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  set K : ℝ := C0 ^ 3 + 3 * C0 ^ 2 * C1 + C0 + C1 + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hC0K : C0 ≤ K := by rw [hK]; nlinarith [pow_nonneg hC0.le 3, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sq_nonneg C0)) hC1.le]
  have hC1K : C1 ≤ K := by rw [hK]; nlinarith [pow_nonneg hC0.le 3, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sq_nonneg C0)) hC1.le]
  have hC3K : C0 ^ 3 ≤ K := by rw [hK]; nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sq_nonneg C0)) hC1.le]
  have hC3K' : 3 * C0 ^ 2 * C1 ≤ K := by rw [hK]; nlinarith [pow_nonneg hC0.le 3]
  have h2K : 2 ≤ K := by rw [hK]; nlinarith [pow_nonneg hC0.le 3, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (sq_nonneg C0)) hC1.le]
  refine ⟨Rs, hRs, 2 * (2 * K + 4 * K ^ 2) + 1, by positivity, ?_⟩
  intro ε μ R Y ht z hz
  have hR : 1 ≤ R := hRs.trans ht.2.2.2.1
  have hR0 : 0 < R := by linarith
  have hz0 : 0 < z := by linarith
  have hdat : ∀ t, z ≤ t →
      t ^ (1 / S.p) / 2 ≤ fam_lambda S.p ε μ t ∧
      |deriv (fam_lambda S.p ε μ) t| ≤ K * t ^ (1 / S.p - 1) ∧
      ‖c05_standing_A S.p ε μ t‖ ≤ C0 * t ^ (-beta S.p) ∧
      ‖c05_standing_A_zero S.p μ t‖ ≤ C0 * t ^ (-beta S.p) ∧
      ‖deriv (c05_standing_A S.p ε μ) t‖ ≤ C1 * t ^ (-beta S.p - 1) ∧
      ‖deriv (c05_standing_A_zero S.p μ) t‖ ≤ C1 * t ^ (-beta S.p - 1) := by
    intro t htz
    obtain ⟨⟨hl1, -, -, -, -⟩, ⟨hA0, -, -⟩, -⟩ := hs0 ε μ R Y ht t (hz.trans htz)
    obtain ⟨⟨-, -, hl1', -, -⟩, ⟨hA1, -, -⟩, -⟩ := hs1 ε μ R Y ht t (hz.trans htz)
    simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one, sub_zero]
      at hA0 hA1 hl1'
    have ht0 : 0 < t := by linarith
    have hX : 0 ≤ t ^ (1 / S.p - 1) := (Real.rpow_pos_of_pos ht0 _).le
    refine ⟨hl1, hl1'.trans (by gcongr), ?_, ?_, ?_, ?_⟩
    · linarith [norm_nonneg (c05_standing_A_zero S.p μ t)]
    · linarith [norm_nonneg (c05_standing_A S.p ε μ t)]
    · linarith [norm_nonneg (deriv (c05_standing_A_zero S.p μ) t)]
    · linarith [norm_nonneg (deriv (c05_standing_A S.p ε μ) t)]
  have hlpos : ∀ t, z ≤ t → 0 < fam_lambda S.p ε μ t := by
    intro t htz
    have := (hdat t htz).1
    have : 0 < t ^ (1 / S.p) / 2 := by have : 0 < t := by linarith
                                       positivity
    linarith
  -- common hypotheses
  have hAd : ∀ t, z ≤ t → HasDerivAt (c05_standing_A S.p ε μ) (deriv (c05_standing_A S.p ε μ) t) t :=
    fun t htz => (c05_aux_A_diff S.p ε μ hp hp1 (by linarith) (hlpos t htz)).hasDerivAt
  have hA0d : ∀ t, z ≤ t → HasDerivAt (c05_standing_A_zero S.p μ) (deriv (c05_standing_A_zero S.p μ) t) t :=
    fun t htz => (c05_aux_A0_diff S.p μ hp hp1 (by linarith)).hasDerivAt
  have hld : ∀ t, z ≤ t → HasDerivAt (fam_lambda S.p ε μ) (deriv (fam_lambda S.p ε μ) t) t :=
    fun t htz => ((c05_aux_lambda_smooth S.p ε μ (n := 1) (by linarith : (0:ℝ) < t)).differentiableAt
      one_ne_zero).hasDerivAt
  have hl0d : ∀ t, z ≤ t → HasDerivAt (lambda0 S.p) (deriv (lambda0 S.p) t) t :=
    fun t htz => (c05_aux_lambda0_hasDeriv S.p (by linarith : (0:ℝ) < t)).differentiableAt.hasDerivAt
  have hΦd : ∀ t, z ≤ t → HasDerivAt (c05_standing_Phi S.p R ε μ) (fam_lambda S.p ε μ t) t :=
    fun t htz => (c05_aux_Psi_hasDeriv S.p R ε μ hR0 (by linarith : (0:ℝ) < t)).sub_const (π / 4)
  have hΦ0d : ∀ t, z ≤ t → HasDerivAt (c05_standing_Phi_zero S.p) (lambda0 S.p t) t :=
    fun t htz => c05_aux_Phi0_hasDeriv S.p hp0 (by linarith : (0:ℝ) < t)
  have hl0low : ∀ t, z ≤ t → t ^ (1 / S.p) / 2 ≤ lambda0 S.p t := by
    intro t htz; unfold lambda0
    have : 0 < t ^ (1 / S.p) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  have hl0der : ∀ t, z ≤ t → |deriv (lambda0 S.p) t| ≤ K * t ^ (1 / S.p - 1) := by
    intro t htz
    have ht0 : 0 < t := by linarith
    rw [(c05_aux_lambda0_hasDeriv S.p ht0).deriv, abs_mul, abs_of_pos hip,
      abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    have : 0 < t ^ (1 / S.p - 1) := Real.rpow_pos_of_pos ht0 _
    gcongr; linarith
  have hcube : ∀ (A : ℝ → ℂ), (∀ t, z ≤ t → HasDerivAt A (deriv A t) t) →
      (∀ t, z ≤ t → ‖A t‖ ≤ C0 * t ^ (-beta S.p)) →
      (∀ t, z ≤ t → ‖deriv A t‖ ≤ C1 * t ^ (-beta S.p - 1)) →
      (∀ t, z ≤ t → HasDerivAt (fun s => A s ^ 3) (deriv (fun s => A s ^ 3) t) t) ∧
      (∀ t, z ≤ t → ‖A t ^ 3‖ ≤ K * t ^ (-(3 * beta S.p))) ∧
      (∀ t, z ≤ t → ‖deriv (fun s => A s ^ 3) t‖ ≤ K * t ^ (-(3 * beta S.p) - 1)) := by
    intro A hd h0 h1
    have H := fun t (htz : z ≤ t) => c05_aux_cube_bounds (by linarith : (0:ℝ) < t)
      (hd t htz).differentiableAt (h0 t htz) (h1 t htz) hC0.le
    refine ⟨fun t htz => (H t htz).1, fun t htz => (H t htz).2.1.trans ?_,
      fun t htz => (H t htz).2.2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right hC3K (Real.rpow_pos_of_pos (by linarith) _).le
    · exact mul_le_mul_of_nonneg_right hC3K' (Real.rpow_pos_of_pos (by linarith) _).le
  have hlo : ∀ (A : ℝ → ℂ), (∀ t, z ≤ t → ‖A t‖ ≤ C0 * t ^ (-beta S.p)) →
      (∀ t, z ≤ t → ‖deriv A t‖ ≤ C1 * t ^ (-beta S.p - 1)) →
      (∀ t, z ≤ t → ‖A t‖ ≤ K * t ^ (-beta S.p)) ∧
      (∀ t, z ≤ t → ‖deriv A t‖ ≤ K * t ^ (-beta S.p - 1)) := by
    intro A h0 h1
    exact ⟨fun t htz => (h0 t htz).trans (mul_le_mul_of_nonneg_right hC0K
      (Real.rpow_pos_of_pos (by linarith) _).le), fun t htz => (h1 t htz).trans
      (mul_le_mul_of_nonneg_right hC1K (Real.rpow_pos_of_pos (by linarith) _).le)⟩
  have hI : (Complex.I).re = 0 := by simp
  have hI1 : 1 ≤ ‖Complex.I‖ := by simp
  have h3I : (3 * Complex.I).re = 0 := by simp
  have h3I1 : 1 ≤ ‖3 * Complex.I‖ := by simp
  have e1 : -(beta S.p + 1 / S.p) = -beta S.p - 1 / S.p := by ring
  have e3 : -(3 * beta S.p + 1 / S.p) = -3 * beta S.p - 1 / S.p := by ring
  have hβ3 : 1 < 3 * beta S.p := by linarith
  have hzX : ∀ r : ℝ, 0 ≤ z ^ r := fun r => (Real.rpow_pos_of_pos hz0 _).le
  have hA := hlo _ (fun t h => (hdat t h).2.2.1) (fun t h => (hdat t h).2.2.2.2.1)
  have hA0 := hlo _ (fun t h => (hdat t h).2.2.2.1) (fun t h => (hdat t h).2.2.2.2.2)
  have hA3 := hcube _ hAd (fun t h => (hdat t h).2.2.1) (fun t h => (hdat t h).2.2.2.2.1)
  have hA03 := hcube _ hA0d (fun t h => (hdat t h).2.2.2.1) (fun t h => (hdat t h).2.2.2.2.2)
  obtain ⟨i1, i2, q1, b1⟩ := c05_aux_prim_generic (B := c05_standing_A S.p ε μ)
    (l := fam_lambda S.p ε μ) (Φ := c05_standing_Phi S.p R ε μ) (c := Complex.I) (z := z) (p := S.p)
    (K := K) (r := beta S.p) hI hI1 hz0 hK0 hβ1 hp0 hAd hld hΦd (fun t h => (hdat t h).1) hA.1 hA.2
    (fun t h => (hdat t h).2.1)
  obtain ⟨i3, i4, q3, b3⟩ := c05_aux_prim_generic (B := fun s => c05_standing_A S.p ε μ s ^ 3)
    (l := fam_lambda S.p ε μ) (Φ := c05_standing_Phi S.p R ε μ) (c := 3 * Complex.I) (z := z)
    (p := S.p) (K := K) (r := 3 * beta S.p) h3I h3I1 hz0 hK0 hβ3 hp0 hA3.1 hld hΦd
    (fun t h => (hdat t h).1) hA3.2.1 hA3.2.2 (fun t h => (hdat t h).2.1)
  obtain ⟨j1, j2, r1, c1⟩ := c05_aux_prim_generic (B := c05_standing_A_zero S.p μ)
    (l := lambda0 S.p) (Φ := c05_standing_Phi_zero S.p) (c := Complex.I) (z := z) (p := S.p)
    (K := K) (r := beta S.p) hI hI1 hz0 hK0 hβ1 hp0 hA0d hl0d hΦ0d hl0low hA0.1 hA0.2 hl0der
  obtain ⟨j3, j4, r3, c3⟩ := c05_aux_prim_generic (B := fun s => c05_standing_A_zero S.p μ s ^ 3)
    (l := lambda0 S.p) (Φ := c05_standing_Phi_zero S.p) (c := 3 * Complex.I) (z := z)
    (p := S.p) (K := K) (r := 3 * beta S.p) h3I h3I1 hz0 hK0 hβ3 hp0 hA03.1 hl0d hΦ0d
    hl0low hA03.2.1 hA03.2.2 hl0der
  rw [e1] at b1 c1
  rw [e3] at b3 c3
  have hZeq : fam_Z S.p R ε μ = fun t => c05_standing_A S.p ε μ t *
      Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) := rfl
  have hZ0eq : c05_standing_Zmu0 S.p R μ = fun t => c05_standing_A_zero S.p μ t *
      Complex.exp (Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) :=
    funext (c05_aux_Zmu0_eq S.p R μ hp0)
  have hcub : ∀ (a : ℂ) (x : ℝ), (a * Complex.exp (Complex.I * (x : ℂ))) ^ 3 =
      a ^ 3 * Complex.exp (3 * Complex.I * (x : ℂ)) := by
    intro a x
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hZ3eq : (fun t => fam_Z S.p R ε μ t ^ 3) = fun t => c05_standing_A S.p ε μ t ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) := by
    funext t; rw [hZeq]; exact hcub _ _
  have hZ03eq : (fun t => c05_standing_Zmu0 S.p R μ t ^ 3) = fun t => c05_standing_A_zero S.p μ t ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) := by
    funext t; rw [hZ0eq]; exact hcub _ _
  have hZ3z : fam_Z S.p R ε μ z ^ 3 = c05_standing_A S.p ε μ z ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi S.p R ε μ z : ℂ)) := congrFun hZ3eq z
  have hZ03z : c05_standing_Zmu0 S.p R μ z ^ 3 = c05_standing_A_zero S.p μ z ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi_zero S.p z : ℂ)) := congrFun hZ03eq z
  have hcst := fun r X (hr : 1 ≤ r) (hX : 0 ≤ X) => c05_aux_prim_const (K := K) (r := r) (X := X) hK0 hr hp0 hX
  refine ⟨⟨i1, ?_, i2, i4, q1, ?_, b1.trans (hcst _ _ hβ1.le (hzX _)), ?_⟩,
    ⟨?_, ?_, j2, j4, ?_, ?_, ?_, ?_⟩⟩
  · rw [hZ3eq]; exact i3
  · rw [hZ3z, show (∫ t in Ioi z, fam_Z S.p R ε μ t ^ 3) = ∫ t in Ioi z, c05_standing_A S.p ε μ t ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) by rw [hZ3eq]]
    exact q3
  · rw [show (∫ t in Ioi z, fam_Z S.p R ε μ t ^ 3) = ∫ t in Ioi z, c05_standing_A S.p ε μ t ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) by rw [hZ3eq]]
    exact b3.trans (hcst _ _ hβ3.le (hzX _))
  · rw [hZ0eq]; exact j1
  · rw [hZ03eq]; exact j3
  · rw [hZ0eq]; exact r1
  · rw [hZ03z, show (∫ t in Ioi z, c05_standing_Zmu0 S.p R μ t ^ 3) = ∫ t in Ioi z,
      c05_standing_A_zero S.p μ t ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) by rw [hZ03eq]]
    exact r3
  · rw [hZ0eq]; exact c1.trans (hcst _ _ hβ1.le (hzX _))
  · rw [show (∫ t in Ioi z, c05_standing_Zmu0 S.p R μ t ^ 3) = ∫ t in Ioi z,
      c05_standing_A_zero S.p μ t ^ 3 *
      Complex.exp (3 * Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) by rw [hZ03eq]]
    exact c3.trans (hcst _ _ hβ3.le (hzX _))

/-- Helper for lem:c05_osc_split_bounds. -/
theorem c05_aux_lambda_pos (S : c05_standing) :
    ∃ R₁ : ℝ, 1 ≤ R₁ ∧ ∀ ε : ℝ, ∀ μ : ℂ, 0 ≤ ε → ε ≤ S.ε₀ → μ ∈ Bbar S.p S.δ →
      ∀ y : ℝ, R₁ ≤ y → 0 < fam_lambda S.p ε μ y := by
  obtain ⟨C₀, hC₀, hsc⟩ := c05_small_constants S
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hp1 := S.hp_hi
  refine ⟨max 1 (2 * C₀ * (1 / S.p + 1)), le_max_left _ _, ?_⟩
  intro ε μ hε0 hε1 hμ y hy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy2 : 2 * C₀ * (1 / S.p + 1) ≤ y := (le_max_right _ _).trans hy
  have hy0 : 0 < y := by linarith
  have hsm := hsc ε μ hε0 hε1 hμ
  have hεle : C₀ * ε ≤ C₀ := by
    have := hε1.trans S.hε₀_le; nlinarith
  have hce : |c_eps S.p ε| ≤ C₀ := by
    have := abs_nonneg (n_eps S.p ε); have := abs_nonneg (c_cubic S.p ε)
    have := abs_nonneg (c_log S.p ε μ); linarith
  have hcl : |c_log S.p ε μ| ≤ C₀ := by
    have := abs_nonneg (n_eps S.p ε); have := abs_nonneg (c_cubic S.p ε)
    have := abs_nonneg (c_eps S.p ε); linarith
  set u := y ^ (1 / S.p) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hy1 (by positivity)
  have hcp : c_power S.p ε * ((1 - S.p ^ 2) / S.p) = -(c_eps S.p ε / S.p) := by
    unfold c_power
    have : 1 - S.p ^ 2 ≠ 0 := by nlinarith
    field_simp
  have h2 : |c_power S.p ε * ((1 - S.p ^ 2) / S.p) * y ^ (1 / S.p - S.p - 1)| ≤ C₀ / S.p * (u / y) := by
    rw [hcp, abs_mul, abs_neg, abs_div, abs_of_pos hp0, abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
    have e : y ^ (1 / S.p - S.p - 1) = u * y ^ (-S.p - 1) := by
      rw [hu, ← Real.rpow_add hy0]; ring_nf
    have hle : y ^ (-S.p - 1) ≤ y⁻¹ := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
    rw [e, div_eq_mul_inv u]
    have : 0 ≤ y ^ (-S.p - 1) := (Real.rpow_pos_of_pos hy0 _).le
    calc |c_eps S.p ε| / S.p * (u * y ^ (-S.p - 1)) ≤ C₀ / S.p * (u * y⁻¹) := by gcongr
      _ = _ := rfl
  have h3 : |c_log S.p ε μ / y| ≤ C₀ * (u / y) := by
    rw [abs_div, abs_of_pos hy0]
    calc |c_log S.p ε μ| / y ≤ C₀ / y := by gcongr
      _ ≤ C₀ * (u / y) := by rw [mul_div_assoc']; gcongr; nlinarith
  have hkey : (C₀ / S.p + C₀) * (u / y) ≤ u / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hy0 (by norm_num)]
    have : (C₀ / S.p + C₀) * 2 ≤ y := by
      have : C₀ / S.p + C₀ = C₀ * (1 / S.p + 1) := by ring
      nlinarith
    nlinarith
  unfold fam_lambda
  have := neg_abs_le (c_power S.p ε * ((1 - S.p ^ 2) / S.p) * y ^ (1 / S.p - S.p - 1))
  have := neg_abs_le (c_log S.p ε μ / y)
  have : 0 < u := by linarith
  nlinarith
/-- Helper for lem:c05_osc_split_bounds. -/
theorem c05_aux_osc_generic {R c M1 M2 : ℝ} {G : ℝ → ℂ} {f : ℝ → ℝ} (hR : 1 ≤ R)
    (hf : ∀ y, f y = if R < y then c * fam_chiR R y * (∫ t in Ioi y, G t).re else 0)
    (hGs : ∀ t, R / 2 < t → ContDiffAt ℝ (⊤ : ℕ∞) G t)
    (hGi : IntegrableOn G (Ioi R))
    (hT : ∀ t, R ≤ t → ‖∫ s in Ioi t, G s‖ ≤ M1)
    (hG : ∀ t, R ≤ t → ‖G t‖ ≤ M2) :
    ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ y, y ≤ R → f y = 0) ∧
      (∃ M : ℝ, ∀ y, |f y| ≤ M ∧ |deriv f y| ≤ M) ∧
      (∀ y, 2 * R ≤ y → deriv f y = -c * (G y).re) ∧
      (∀ y, R ≤ y → |f y| ≤ |c| * ‖∫ t in Ioi y, G t‖) := by
  have hR0 : 0 < R := by linarith
  set R' := 3 * R / 4 with hR'
  have hR'R : R' < R := by rw [hR']; linarith
  have hR'2 : R / 2 < R' := by rw [hR']; linarith
  set T : ℝ → ℂ := fun y => ∫ t in Ioi y, G t with hTdef
  set g : ℝ → ℝ := fun y => c * fam_chiR R y * (T y).re with hg
  have hfg : f = g := by
    funext y; rw [hf]; split_ifs with h
    · rfl
    · simp only [hg]; rw [c04_aux_chiR_zero R y hR0 (not_lt.mp h)]; ring
  have hGc : ContinuousOn G (Ioi R') := fun t ht =>
    (hGs t (hR'2.trans ht)).continuousAt.continuousWithinAt
  have hGi' : IntegrableOn G (Ioi R') := by
    rw [← Ioc_union_Ioi_eq_Ioi hR'R.le]
    refine IntegrableOn.union ?_ hGi
    have : ContinuousOn G (Icc R' R) := fun t ht =>
      (hGs t (hR'2.trans_le ht.1)).continuousAt.continuousWithinAt
    exact (this.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hTd : ∀ y, R' < y → HasDerivAt T (-G y) y := fun y hy =>
    c05_aux_tail_hasDeriv G R' hGi' hGc hy
  have hTs : ContDiffOn ℝ (⊤ : ℕ∞) T (Ioi R') := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz => (hTd z hz).differentiableAt.differentiableWithinAt, ?_⟩
    refine ContDiffOn.congr (f := fun z => -G z)
      (fun z hz => (hGs z (hR'2.trans hz)).neg.contDiffWithinAt) (fun z hz => (hTd z hz).deriv)
  have hχs := c04_aux_chiR_smooth R
  have hzero : ∀ x, x < R → g =ᶠ[nhds x] fun _ => 0 := by
    intro x hx
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp only [hg]; rw [c04_aux_chiR_zero R y hR0 (le_of_lt hy)]; ring
  have hcd : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : R' < x
    · exact (contDiffAt_const.mul hχs.contDiffAt).mul
        (c05_aux_re (hTs.contDiffAt (Ioi_mem_nhds hx)))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x (by push_neg at hx; linarith))
  have hderiv : ∀ y, R' < y → HasDerivAt g
      (c * deriv (fam_chiR R) y * (T y).re + c * fam_chiR R y * (-G y).re) y := by
    intro y hy
    have hχ : HasDerivAt (fam_chiR R) (deriv (fam_chiR R) y) y :=
      (hχs.differentiable (by simp)).differentiableAt.hasDerivAt
    exact (hχ.const_mul c).mul (c05_aux_hasDerivAt_re (hTd y hy))
  obtain ⟨B, hB0, hB⟩ := c04_aux_chiR_iter 1
  have hχm : ∀ y, 0 ≤ fam_chiR R y ∧ fam_chiR R y ≤ 1 := fun y =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans (hT R le_rfl)
  have hM2 : 0 ≤ M2 := (norm_nonneg _).trans (hG R le_rfl)
  have hgb : ∀ y, R ≤ y → |g y| ≤ |c| * ‖T y‖ := by
    intro y hy
    simp only [hg]
    rw [abs_mul, abs_mul, abs_of_nonneg (hχm y).1]
    have := Complex.abs_re_le_norm (T y)
    have := (hχm y).2
    calc |c| * fam_chiR R y * |(T y).re| ≤ |c| * 1 * ‖T y‖ := by gcongr
      _ = _ := by ring
  rw [hfg]
  refine ⟨hcd, fun y hy => ?_, ⟨|c| * (B * M1 + M1 + M2), fun y => ?_⟩, fun y hy => ?_, hgb⟩
  · simp only [hg]; rw [c04_aux_chiR_zero R y hR0 hy]; ring
  · by_cases hy : R ≤ y
    · refine ⟨(hgb y hy).trans ?_, ?_⟩
      · have := hT y hy
        have : 0 ≤ B * M1 := by positivity
        nlinarith [abs_nonneg c]
      · rw [(hderiv y (hR'R.trans_le hy)).deriv]
        have h1 : |deriv (fam_chiR R) y| ≤ B := by
          have := hB R hR y; rwa [iteratedDeriv_one] at this
        have h2 : |(T y).re| ≤ M1 := (Complex.abs_re_le_norm _).trans (hT y hy)
        have h3 : |(-G y).re| ≤ M2 := (Complex.abs_re_le_norm _).trans (by rw [norm_neg]; exact hG y hy)
        calc |c * deriv (fam_chiR R) y * (T y).re + c * fam_chiR R y * (-G y).re|
            ≤ |c| * |deriv (fam_chiR R) y| * |(T y).re| + |c| * fam_chiR R y * |(-G y).re| := by
              refine (abs_add_le _ _).trans (le_of_eq ?_)
              rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hχm y).1]
          _ ≤ |c| * B * M1 + |c| * 1 * M2 := by
              gcongr
              exact (hχm y).2
          _ ≤ |c| * (B * M1 + M1 + M2) := by nlinarith [abs_nonneg c]
    · push_neg at hy
      have he := hzero y hy
      rw [he.deriv_eq, he.eq_of_nhds]
      refine ⟨by rw [abs_zero]; positivity, by rw [deriv_const, abs_zero]; positivity⟩
  · rw [(hderiv y (by linarith)).deriv, c04_aux_deriv_chiR_top R y hR0 hy,
      c04_aux_chiR_one R y hR0 hy]
    simp
/-- Helper for lem:c05_osc_split_bounds. -/
theorem c05_aux_L1_tail {f : ℝ → ℝ} {R D a : ℝ} (hf : Continuous f) (hR : 1 ≤ R) (ha : 1 < a)
    (hD : 0 ≤ D) (hz : ∀ y, y ≤ R → f y = 0) (hb : ∀ y, R ≤ y → |f y| ≤ D * y ^ (-a)) :
    Integrable f ∧ ∫ y, |f y| ≤ D / (a - 1) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hbi, hbint⟩ := c05_aux_int_Ioi_rpow D (-a) R (by linarith) hR0
  have hind : ∀ g : ℝ → ℝ, (∀ y, y ≤ R → g y = 0) → (Ioi R).indicator g = g := by
    intro g hg; funext y
    by_cases hy : R < y
    · exact indicator_of_mem hy g
    · rw [indicator_of_notMem hy g, hg y (not_lt.mp hy)]
  have hfi : IntegrableOn f (Ioi R) := by
    refine Integrable.mono' hbi hf.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    rw [Real.norm_eq_abs]; exact hb t (le_of_lt ht)
  have hI : Integrable f := by
    rw [← hind f hz]; exact (integrable_indicator_iff measurableSet_Ioi).mpr hfi
  refine ⟨hI, ?_⟩
  have habs : (fun y => |f y|) = (Ioi R).indicator (fun y => |f y|) :=
    (hind _ (fun y hy => by rw [hz y hy, abs_zero])).symm
  rw [habs, integral_indicator measurableSet_Ioi]
  calc ∫ y in Ioi R, |f y| ≤ ∫ y in Ioi R, D * y ^ (-a) := by
        refine setIntegral_mono_on hfi.abs hbi measurableSet_Ioi fun y hy => hb y (le_of_lt hy)
    _ = D * (-R ^ (-a + 1) / (-a + 1)) := hbint
    _ = D * R ^ (1 - a) / (a - 1) := by
        rw [show -a + 1 = 1 - a by ring, show (1 : ℝ) - a = -(a - 1) by ring, div_neg]; ring
    _ ≤ D * 1 / (a - 1) := by
        gcongr
        exact Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)
    _ = D / (a - 1) := by ring

/-- Blueprint: lem:c05_osc_split_bounds.  Regularity, support, boundedness, derivatives and
size bounds of `f_{osc,1}`, `f_{osc,3}`; `f_osc = f_{osc,1} + f_{osc,3}`. -/
theorem c05_osc_split_bounds (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ContDiff ℝ (⊤ : ℕ∞) (c05_E5_remainders_fosc1 S.p R ε μ) ∧
        ContDiff ℝ (⊤ : ℕ∞) (c05_E5_remainders_fosc3 S.p R ε μ) ∧
        (∀ y, y ≤ R → c05_E5_remainders_fosc1 S.p R ε μ y = 0 ∧
          c05_E5_remainders_fosc3 S.p R ε μ y = 0) ∧
        (∃ M : ℝ, ∀ y, |c05_E5_remainders_fosc1 S.p R ε μ y| ≤ M ∧
          |deriv (c05_E5_remainders_fosc1 S.p R ε μ) y| ≤ M ∧
          |c05_E5_remainders_fosc3 S.p R ε μ y| ≤ M ∧
          |deriv (c05_E5_remainders_fosc3 S.p R ε μ) y| ≤ M) ∧
        (∀ y, fam_osc S.p R ε μ y =
          c05_E5_remainders_fosc1 S.p R ε μ y + c05_E5_remainders_fosc3 S.p R ε μ y) ∧
        (∀ y, 2 * R ≤ y →
          deriv (c05_E5_remainders_fosc1 S.p R ε μ) y =
              2 * (fam_Z S.p R ε μ y - c05_standing_Zmu0 S.p R μ y).re ∧
            deriv (c05_E5_remainders_fosc3 S.p R ε μ) y =
              2 * c_cubic S.p ε * (fam_Z S.p R ε μ y ^ 3).re) ∧
        (∀ y, R ≤ y →
          |c05_E5_remainders_fosc3 S.p R ε μ y| ≤ C * ε * y ^ (-3 * beta S.p - 1 / S.p) ∧
            |c05_E5_remainders_fosc1 S.p R ε μ y| ≤ C * ε * y ^ (-S.p - beta S.p)) ∧
        Integrable (c05_E5_remainders_fosc1 S.p R ε μ) ∧
        Integrable (c05_E5_remainders_fosc3 S.p R ε μ) ∧
        (∫ y, |c05_E5_remainders_fosc1 S.p R ε μ y|) +
            (∫ y, |c05_E5_remainders_fosc3 S.p R ε μ y|) ≤ C * ε := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  have h2β : 2 * beta S.p = 1 + 1 / S.p := c05_aux_two_beta S.p hp0
  have hexp : -3 * beta S.p - 1 / S.p ≤ -S.p - beta S.p := by
    have : S.p ≤ 1 + 2 / S.p := by
      have : 1 ≤ 1 / S.p := by rw [le_div_iff₀ hp0]; linarith
      have : 2 / S.p = 2 * (1 / S.p) := by ring
      linarith
    have : 2 / S.p = 2 * (1 / S.p) := by ring
    linarith
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C0, hC0, hs0⟩ := hsym 0
  obtain ⟨Cc, hCc, hsc⟩ := c05_small_constants S
  obtain ⟨R1, hR1, hlpos⟩ := c05_aux_lambda_pos S
  obtain ⟨-, RA, hRA, HA, -⟩ :=
    Classical.choose_spec (approx_phase_differences S.p hp hp1 S.δ S.hδ S.hδ_le)
  obtain ⟨CA, hCA, HA0⟩ := HA 0
  set R₀ := max (max Rp Rs) (max (2 * R1) RA) with hR₀
  have hR₀1 : 1 ≤ R₀ := hRp.trans ((le_max_left _ _).trans (le_max_left _ _))
  set K1 := CA + 2 * Cc * Cp with hK1
  set K3 := 2 * Cc * Cp with hK3
  have hK10 : 0 ≤ K1 := by positivity
  have hK30 : 0 ≤ K3 := by positivity
  have ha1 : 1 < S.p + beta S.p := by linarith
  have ha3 : 1 < 3 * beta S.p + 1 / S.p := by linarith
  refine ⟨R₀, hR₀1, K1 + K3 + K1 / (S.p + beta S.p - 1) + K3 / (3 * beta S.p + 1 / S.p - 1) + 1,
    by have : 0 < S.p + beta S.p - 1 := by linarith
       have : 0 < 3 * beta S.p + 1 / S.p - 1 := by linarith
       positivity, ?_⟩
  intro ε μ R Y ht
  have htp := c05_aux_tuple_mono (show Rp ≤ R₀ by simp [hR₀]) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ R₀ by simp [hR₀]) ht
  have hR : 1 ≤ R := hRp.trans htp.2.2.2.1
  have hR0 : 0 < R := by linarith
  have hR1R : 2 * R1 ≤ R := le_trans (by simp [hR₀]) ht.2.2.2.1
  have hRAR : RA ≤ R := le_trans (by simp [hR₀]) ht.2.2.2.1
  obtain ⟨hε0, hε1, hμ, -, -⟩ := ht
  have hεA := (c05_aux_eps_le S hε0 hε1).2.2.2.2.2.2.2
  have hcc : |c_cubic S.p ε| ≤ Cc * ε := by
    have := hsc ε μ hε0 hε1 hμ
    have := abs_nonneg (c_eps S.p ε); have := abs_nonneg (n_eps S.p ε)
    have := abs_nonneg (c_log S.p ε μ); linarith
  -- smoothness of the integrands on `(R/2, ∞)`
  have hpos : ∀ t, R / 2 < t → 0 < fam_lambda S.p ε μ t := fun t ht' =>
    hlpos ε μ hε0 hε1 hμ t (by linarith)
  have hZs : ∀ t, R / 2 < t → ContDiffAt ℝ (⊤ : ℕ∞) (fam_Z S.p R ε μ) t := fun t ht' =>
    c05_aux_Z_smooth S.p R ε μ hp hp1 hR0 (by linarith) (hpos t ht').ne'
  have hZ0s : ∀ t, R / 2 < t → ContDiffAt ℝ (⊤ : ℕ∞) (c05_standing_Zmu0 S.p R μ) t := fun t ht' =>
    c05_aux_Zmu0_smooth S.p R μ hp hp1 hR0 (by linarith)
  have hP := fun z (hz : R ≤ z) => hprim ε μ R Y htp z hz
  have hyr : ∀ t r : ℝ, R ≤ t → r ≤ 0 → t ^ r ≤ 1 := fun t r ht hr =>
    Real.rpow_le_one_of_one_le_of_nonpos (hR.trans ht) hr
  -- fosc1
  have G1 := c05_aux_osc_generic (c := -2) (M1 := 2 * Cp) (M2 := C0)
    (G := fun t => fam_Z S.p R ε μ t - c05_standing_Zmu0 S.p R μ t)
    (f := c05_E5_remainders_fosc1 S.p R ε μ) hR (fun y => rfl)
    (fun t ht' => (hZs t ht').sub (hZ0s t ht'))
    ((hP R le_rfl).1.1.sub (hP R le_rfl).2.1)
    (fun t ht' => by
      obtain ⟨⟨hi, -, -, -, -, -, hb, -⟩, ⟨hi0, -, -, -, -, -, hb0, -⟩⟩ := hP t ht'
      rw [integral_sub hi hi0]
      have h1 := hyr t (-beta S.p - 1 / S.p) ht' (by linarith)
      calc _ ≤ ‖∫ s in Ioi t, fam_Z S.p R ε μ s‖ + ‖∫ s in Ioi t, c05_standing_Zmu0 S.p R μ s‖ :=
            norm_sub_le _ _
        _ ≤ Cp * 1 + Cp * 1 := by gcongr <;> linarith [mul_le_mul_of_nonneg_left h1 hCp.le]
        _ = 2 * Cp := by ring)
    (fun t ht' => by
      obtain ⟨-, -, ⟨hz, -⟩, -⟩ := hs0 ε μ R Y hts t ht'
      simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at hz
      have h1 := hyr t (-beta S.p) ht' (by linarith)
      calc _ ≤ ‖fam_Z S.p R ε μ t‖ + ‖c05_standing_Zmu0 S.p R μ t‖ := norm_sub_le _ _
        _ ≤ C0 * t ^ (-beta S.p) := hz
        _ ≤ C0 * 1 := by gcongr
        _ = C0 := mul_one _)
  have G3 := c05_aux_osc_generic (c := -2 * c_cubic S.p ε) (M1 := Cp) (M2 := C0)
    (G := fun t => fam_Z S.p R ε μ t ^ 3)
    (f := c05_E5_remainders_fosc3 S.p R ε μ) hR (fun y => rfl)
    (fun t ht' => (hZs t ht').pow 3)
    (hP R le_rfl).1.2.1
    (fun t ht' => by
      obtain ⟨⟨-, -, -, -, -, -, -, hb⟩, -⟩ := hP t ht'
      have h1 := hyr t (-3 * beta S.p - 1 / S.p) ht' (by linarith)
      exact hb.trans (by nlinarith))
    (fun t ht' => by
      obtain ⟨-, -, ⟨-, hz, -⟩, -⟩ := hs0 ε μ R Y hts t ht'
      simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at hz
      have h1 := hyr t (-3 * beta S.p) ht' (by linarith)
      exact hz.trans (by nlinarith))
  obtain ⟨c1, z1, ⟨M1, hM1⟩, d1, b1⟩ := G1
  obtain ⟨c3, z3, ⟨M3, hM3⟩, d3, b3⟩ := G3
  -- sum identity
  have hsum : ∀ y, fam_osc S.p R ε μ y =
      c05_E5_remainders_fosc1 S.p R ε μ y + c05_E5_remainders_fosc3 S.p R ε μ y := by
    intro y
    by_cases hy : R < y
    · obtain ⟨⟨hi, hi3, -⟩, ⟨hi0, -⟩⟩ := hP y hy.le
      unfold fam_osc c05_E5_remainders_fosc1 c05_E5_remainders_fosc3
      rw [if_pos hy, if_pos hy, if_pos hy]
      have : (∫ t in Ioi y, (fam_Z S.p R ε μ t + (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ t ^ 3 -
          μ / mu_star S.p * fam_Z0 S.p R t)) =
          (∫ t in Ioi y, (fam_Z S.p R ε μ t - c05_standing_Zmu0 S.p R μ t)) +
            (c_cubic S.p ε : ℂ) * ∫ t in Ioi y, fam_Z S.p R ε μ t ^ 3 := by
        have hfe : (fun t => fam_Z S.p R ε μ t + (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ t ^ 3 -
            μ / mu_star S.p * fam_Z0 S.p R t) = fun t => (fam_Z S.p R ε μ t -
              c05_standing_Zmu0 S.p R μ t) + (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ t ^ 3 := by
          funext t; unfold c05_standing_Zmu0; ring
        have hs1 : IntegrableOn (fun t => fam_Z S.p R ε μ t - c05_standing_Zmu0 S.p R μ t) (Ioi y) :=
          hi.sub hi0
        have hs3 : IntegrableOn (fun t => (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ t ^ 3) (Ioi y) :=
          hi3.const_mul _
        rw [hfe, integral_add hs1 hs3, integral_const_mul]
      rw [this, Complex.add_re, Complex.re_ofReal_mul]; ring
    · have hy' := not_lt.mp hy
      unfold fam_osc
      rw [if_neg hy, (z1 y hy'), (z3 y hy')]; ring
  -- pointwise bounds
  have hb3 : ∀ y, R ≤ y → |c05_E5_remainders_fosc3 S.p R ε μ y| ≤ K3 * ε * y ^ (-3 * beta S.p - 1 / S.p) := by
    intro y hy
    obtain ⟨⟨-, -, -, -, -, -, -, hb⟩, -⟩ := hP y hy
    refine (b3 y hy).trans ?_
    rw [abs_mul, abs_neg, abs_two]
    have : 0 ≤ y ^ (-3 * beta S.p - 1 / S.p) := (Real.rpow_pos_of_pos (by linarith) _).le
    calc 2 * |c_cubic S.p ε| * ‖∫ t in Ioi y, fam_Z S.p R ε μ t ^ 3‖
        ≤ 2 * (Cc * ε) * (Cp * y ^ (-3 * beta S.p - 1 / S.p)) := by gcongr
      _ = K3 * ε * y ^ (-3 * beta S.p - 1 / S.p) := by rw [hK3]; ring
  have hb1 : ∀ y, R ≤ y → |c05_E5_remainders_fosc1 S.p R ε μ y| ≤ K1 * ε * y ^ (-S.p - beta S.p) := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hA := (HA0 R hRAR ε hεA μ hμ y hy).2.2.2
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at hA
    have hjb : jb y ^ (-S.p - beta S.p) ≤ y ^ (-S.p - beta S.p) := by
      refine Real.rpow_le_rpow_of_nonpos hy0 ?_ (by linarith)
      unfold jb; rw [Real.le_sqrt hy0.le (by positivity)]; linarith
    have hosc : |fam_osc S.p R ε μ y| ≤ CA * ε * y ^ (-S.p - beta S.p) := by
      refine hA.trans ?_
      calc CA * min (ε * jb y ^ (-S.p - beta S.p)) _ ≤ CA * (ε * jb y ^ (-S.p - beta S.p)) := by
            gcongr; exact min_le_left _ _
        _ ≤ CA * (ε * y ^ (-S.p - beta S.p)) := by gcongr
        _ = _ := by ring
    have h3 := hb3 y hy
    have hmono : y ^ (-3 * beta S.p - 1 / S.p) ≤ y ^ (-S.p - beta S.p) :=
      Real.rpow_le_rpow_of_exponent_le (hR.trans hy) hexp
    have heq : c05_E5_remainders_fosc1 S.p R ε μ y = fam_osc S.p R ε μ y - c05_E5_remainders_fosc3 S.p R ε μ y := by
      rw [hsum y]; ring
    rw [heq]
    calc _ ≤ |fam_osc S.p R ε μ y| + |c05_E5_remainders_fosc3 S.p R ε μ y| := abs_sub _ _
      _ ≤ CA * ε * y ^ (-S.p - beta S.p) + K3 * ε * y ^ (-S.p - beta S.p) := by
          gcongr
          exact h3.trans (by gcongr)
      _ = K1 * ε * y ^ (-S.p - beta S.p) := by rw [hK1, hK3]; ring
  have hL1 := c05_aux_L1_tail (D := K1 * ε) (a := S.p + beta S.p) c1.continuous hR ha1 (by positivity)
    z1 (fun y hy => by rw [show -(S.p + beta S.p) = -S.p - beta S.p by ring]; exact hb1 y hy)
  have hL3 := c05_aux_L1_tail (D := K3 * ε) (a := 3 * beta S.p + 1 / S.p) c3.continuous hR ha3
    (by positivity) z3
    (fun y hy => by rw [show -(3 * beta S.p + 1 / S.p) = -3 * beta S.p - 1 / S.p by ring]; exact hb3 y hy)
  refine ⟨c1, c3, fun y hy => ⟨z1 y hy, z3 y hy⟩, ⟨max M1 M3, fun y => ?_⟩, hsum,
    fun y hy => ⟨?_, ?_⟩, fun y hy => ⟨?_, ?_⟩, hL1.1, hL3.1, ?_⟩
  · obtain ⟨a1, a2⟩ := hM1 y; obtain ⟨a3, a4⟩ := hM3 y
    exact ⟨a1.trans (le_max_left _ _), a2.trans (le_max_left _ _), a3.trans (le_max_right _ _),
      a4.trans (le_max_right _ _)⟩
  · rw [d1 y hy]; ring
  · rw [d3 y hy]; ring
  · refine (hb3 y hy).trans ?_
    have : 0 ≤ ε * y ^ (-3 * beta S.p - 1 / S.p) := by
      have := Real.rpow_pos_of_pos (show (0:ℝ) < y by linarith) (-3 * beta S.p - 1 / S.p); positivity
    have : 0 ≤ K1 / (S.p + beta S.p - 1) := by
      have : 0 < S.p + beta S.p - 1 := by linarith
      positivity
    have : 0 ≤ K3 / (3 * beta S.p + 1 / S.p - 1) := by
      have : 0 < 3 * beta S.p + 1 / S.p - 1 := by linarith
      positivity
    nlinarith
  · refine (hb1 y hy).trans ?_
    have : 0 ≤ ε * y ^ (-S.p - beta S.p) := by
      have := Real.rpow_pos_of_pos (show (0:ℝ) < y by linarith) (-S.p - beta S.p); positivity
    have : 0 ≤ K1 / (S.p + beta S.p - 1) := by
      have : 0 < S.p + beta S.p - 1 := by linarith
      positivity
    have : 0 ≤ K3 / (3 * beta S.p + 1 / S.p - 1) := by
      have : 0 < 3 * beta S.p + 1 / S.p - 1 := by linarith
      positivity
    nlinarith
  · calc _ ≤ K1 * ε / (S.p + beta S.p - 1) + K3 * ε / (3 * beta S.p + 1 / S.p - 1) :=
          add_le_add hL1.2 hL3.2
      _ = (K1 / (S.p + beta S.p - 1) + K3 / (3 * beta S.p + 1 / S.p - 1)) * ε := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hε0

/-- Blueprint: lem:c05_E5_split.  For `y > 2R`: `ℰ₅ = ℛ_lin + ℛ_cub` and
`ℛ_lin = ℛ_{lin,1} + ℛ_{lin,3}`. -/
theorem c05_E5_split (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ∀ y : ℝ, 2 * R < y →
        residual_decomposition_E5 S.p R ε μ Y y =
            c05_E5_remainders_Rlin S.p R ε μ y + c05_E5_remainders_Rcub S.p R ε μ Y y ∧
          c05_E5_remainders_Rlin S.p R ε μ y =
            c05_E5_remainders_Rlin1 S.p R ε μ y + c05_E5_remainders_Rlin3 S.p R ε μ y := by
  obtain ⟨R₀, hR₀, C, hC, hosc⟩ := c05_osc_split_bounds S
  refine ⟨R₀, hR₀, fun ε μ R Y ht y hy => ⟨?_, ?_⟩⟩
  · unfold residual_decomposition_E5 c05_E5_remainders_Rlin c05_E5_remainders_Rcub
    ring
  obtain ⟨hs1, hs3, -, ⟨M, hM⟩, hsum, hder, -⟩ := hosc ε μ R Y ht
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hfun : fam_osc S.p R ε μ =
      fun z => c05_E5_remainders_fosc1 S.p R ε μ z + c05_E5_remainders_fosc3 S.p R ε μ z :=
    funext hsum
  have hd1 : Differentiable ℝ (c05_E5_remainders_fosc1 S.p R ε μ) :=
    hs1.differentiable (by simp)
  have hd3 : Differentiable ℝ (c05_E5_remainders_fosc3 S.p R ε μ) :=
    hs3.differentiable (by simp)
  have hderiv : deriv (fam_osc S.p R ε μ) = fun z =>
      deriv (c05_E5_remainders_fosc1 S.p R ε μ) z + deriv (c05_E5_remainders_fosc3 S.p R ε μ) z := by
    rw [hfun]; funext z; exact deriv_add (hd1 z) (hd3 z)
  have hC1 : ContDiff ℝ 1 (deriv (c05_E5_remainders_fosc1 S.p R ε μ)) :=
    (contDiff_infty_iff_deriv.mp hs1).2.of_le (WithTop.coe_le_coe.mpr le_top)
  have hC3 : ContDiff ℝ 1 (deriv (c05_E5_remainders_fosc3 S.p R ε μ)) :=
    (contDiff_infty_iff_deriv.mp hs3).2.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfrac : fracDdy S.p (fam_osc S.p R ε μ) y =
      fracDdy S.p (c05_E5_remainders_fosc1 S.p R ε μ) y +
        fracDdy S.p (c05_E5_remainders_fosc3 S.p R ε μ) y := by
    unfold fracDdy
    rw [hderiv]
    exact c05_aux_fracD_add S.p hp0 S.hp_hi _ _ hC1 hC3 ⟨M, fun x => (hM x).2.1⟩
      ⟨M, fun x => (hM x).2.2.2⟩ y
  obtain ⟨e1, e3⟩ := hder y hy.le
  have hdy : deriv (fam_osc S.p R ε μ) y =
      2 * (fam_Z S.p R ε μ y - c05_standing_Zmu0 S.p R μ y).re +
        2 * c_cubic S.p ε * (fam_Z S.p R ε μ y ^ 3).re := by
    rw [hderiv]; simp only [e1, e3]
  unfold c05_E5_remainders_Rlin c05_E5_remainders_Rlin1 c05_E5_remainders_Rlin3 L0
  rw [hfrac, hdy, hsum y, Complex.sub_re]
  ring

/-- Helper: `0 ≤ χ_Y ≤ 1`. -/
theorem c05_aux_chiY_mem (Y z : ℝ) : 0 ≤ res_chiY Y z ∧ res_chiY Y z ≤ 1 := by
  unfold res_chiY chiAnnulus
  have h1 := Real.smoothTransition.nonneg ((z / Y - 3 / 10) / (1 / 5))
  have h2 := Real.smoothTransition.le_one ((z / Y - 3 / 10) / (1 / 5))
  have h3 := Real.smoothTransition.nonneg ((7 / 2 - z / Y) / (1 / 2))
  have h4 := Real.smoothTransition.le_one ((7 / 2 - z / Y) / (1 / 2))
  exact ⟨mul_nonneg h1 h3, by nlinarith⟩

/-- Helper: `|χ_Y'| ≤ K₁/Y` with `K₁` independent of `Y`. -/
theorem c05_aux_chiY_deriv_bound : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ Y : ℝ, 0 < Y → ∀ z : ℝ,
    HasDerivAt (res_chiY Y) (deriv chiAnnulus (z / Y) / Y) z ∧
      |deriv (res_chiY Y) z| ≤ K₁ / Y := by
  have hcs : HasCompactSupport chiAnnulus := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 3 / 10) (b := 7 / 2)) ?_
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    have := c05_aux_chiY_zero (Y := 1) (z := x) one_pos (by rcases hx with h | h <;> [left; right] <;> linarith)
    simpa [res_chiY] using this
  obtain ⟨K, hK⟩ := (c05_aux_chiAnnulus_smooth.continuous_deriv (by simp)).bounded_above_of_compact_support
    hcs.deriv
  refine ⟨max K 0, le_max_right _ _, fun Y hY z => ?_⟩
  have hd : HasDerivAt (res_chiY Y) (deriv chiAnnulus (z / Y) / Y) z := by
    have h1 : HasDerivAt (fun z : ℝ => z / Y) (1 / Y) z := (hasDerivAt_id z).div_const Y
    have h2 := ((c05_aux_chiAnnulus_smooth.differentiable (by simp)) (z / Y)).hasDerivAt.comp z h1
    show HasDerivAt (chiAnnulus ∘ fun z : ℝ => z / Y) _ z
    convert h2 using 1; ring
  refine ⟨hd, ?_⟩
  rw [hd.deriv, abs_div, abs_of_pos hY]
  exact div_le_div_of_nonneg_right ((show |deriv chiAnnulus (z / Y)| ≤ K by
    simpa [Real.norm_eq_abs] using hK (z / Y)).trans (le_max_left _ _)) hY.le

/-- Helper: `χ_Y' = 0` on `(Y/2, 3Y)`. -/
theorem c05_aux_chiY_deriv_zero {Y z : ℝ} (hY : 0 < Y) (hz : z ∈ Ioo (Y / 2) (3 * Y)) :
    deriv (res_chiY Y) z = 0 := by
  have : res_chiY Y =ᶠ[nhds z] fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact c05_aux_chiY_one hY ⟨hw.1.le, hw.2.le⟩
  rw [this.deriv_eq]; simp

/-- Helper: `(a²)^r = |a|^{2r}`. -/
theorem c05_aux_sq_rpow (a r : ℝ) : (a ^ 2) ^ r = |a| ^ (2 * r) := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg a)]; norm_num

/-- Helper: `(a²)^{-s/2} = (|a|^s)⁻¹`. -/
theorem c05_aux_sq_rpow_inv (a s : ℝ) : (a ^ 2) ^ (-s / 2) = (|a| ^ s)⁻¹ := by
  rw [c05_aux_sq_rpow, show 2 * (-s / 2) = -s by ring, Real.rpow_neg (abs_nonneg a)]

/-- Helper: `|a|^n (a²)^r = |a|^{n+2r}` for `a ≠ 0`. -/
theorem c05_aux_abs_mul_sq_rpow {a : ℝ} (ha : a ≠ 0) (n : ℕ) (r : ℝ) :
    |a| ^ n * (a ^ 2) ^ r = |a| ^ ((n : ℝ) + 2 * r) := by
  rw [c05_aux_sq_rpow, Real.rpow_add (abs_pos.mpr ha), Real.rpow_natCast]

/-- Helper: the `z`-derivative of the far kernel `(1-χ_Y(z))|y-z|^{-1-p}` (closed form). -/
def c05_aux_fk (p Y y z : ℝ) : ℝ :=
  -deriv (res_chiY Y) z * ((y - z) ^ 2) ^ (-(1 + p) / 2) +
    (1 - res_chiY Y z) * (1 + p) * (y - z) * ((y - z) ^ 2) ^ (-(3 + p) / 2)

/-- Helper: the `y`-derivative of `c05_aux_fk`. -/
def c05_aux_fk' (p Y y z : ℝ) : ℝ :=
  deriv (res_chiY Y) z * (1 + p) * (y - z) * ((y - z) ^ 2) ^ (-(3 + p) / 2) +
    (1 - res_chiY Y z) * (1 + p) *
      (((y - z) ^ 2) ^ (-(3 + p) / 2) - (3 + p) * (y - z) ^ 2 * ((y - z) ^ 2) ^ (-(5 + p) / 2))

/-- Helper: `∂_y ((y-z)²)^r = 2r(y-z)((y-z)²)^{r-1}` for `y ≠ z`. -/
theorem c05_aux_hasDerivAt_sq_rpow {y z : ℝ} (hyz : y ≠ z) (r : ℝ) :
    HasDerivAt (fun y' => ((y' - z) ^ 2) ^ r) (2 * r * (y - z) * ((y - z) ^ 2) ^ (r - 1)) y := by
  have h1 : HasDerivAt (fun y' => (y' - z) ^ 2) (2 * (y - z)) y := by
    have h := ((hasDerivAt_id' y).sub_const z).pow 2
    convert h using 1; simp
  have := h1.rpow_const (p := r) (Or.inl (pow_ne_zero 2 (sub_ne_zero.mpr hyz)))
  convert this using 1; ring

/-- Helper: `∂_z ((y-z)²)^r = -2r(y-z)((y-z)²)^{r-1}` for `z ≠ y`. -/
theorem c05_aux_hasDerivAt_sq_rpow' {y z : ℝ} (hyz : z ≠ y) (r : ℝ) :
    HasDerivAt (fun z' => ((y - z') ^ 2) ^ r) (-(2 * r * (y - z) * ((y - z) ^ 2) ^ (r - 1))) z := by
  have h1 : HasDerivAt (fun z' => (y - z') ^ 2) (-(2 * (y - z))) z := by
    have h := ((hasDerivAt_id' z).const_sub y).pow 2
    convert h using 1; simp
  have := h1.rpow_const (p := r) (Or.inl (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hyz))))
  convert this using 1; ring

/-- Helper: the far kernel, `(1-χ)/|y-z|^{1+p} = (1-χ)((y-z)²)^{-(1+p)/2}`. -/
theorem c05_aux_fker_eq (p Y y : ℝ) :
    (fun z' => (1 - res_chiY Y z') / |y - z'| ^ (1 + p)) =
      fun z' => (1 - res_chiY Y z') * ((y - z') ^ 2) ^ (-(1 + p) / 2) := by
  funext z'
  rw [c05_aux_sq_rpow_inv, div_eq_mul_inv]

/-- Helper: for `y ∈ (Y/2,3Y)`, `∂_z[(1-χ_Y)|y-z|^{-1-p}] = c05_aux_fk`. -/
theorem c05_aux_fk_hasDeriv_z (p Y : ℝ) (hY : 0 < Y) {y : ℝ} (hy : y ∈ Ioo (Y / 2) (3 * Y))
    (z : ℝ) : HasDerivAt (fun z' => (1 - res_chiY Y z') / |y - z'| ^ (1 + p)) (c05_aux_fk p Y y z) z := by
  rw [c05_aux_fker_eq]
  by_cases hz : z ∈ Ioo (Y / 2) (3 * Y)
  · have hev : (fun _ => (0 : ℝ)) =ᶠ[nhds z]
        (fun z' => (1 - res_chiY Y z') * ((y - z') ^ 2) ^ (-(1 + p) / 2)) := by
      filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
      rw [c05_aux_chiY_one hY ⟨hw.1.le, hw.2.le⟩]; ring
    have h0 : c05_aux_fk p Y y z = 0 := by
      unfold c05_aux_fk
      rw [c05_aux_chiY_deriv_zero hY hz, c05_aux_chiY_one hY ⟨hz.1.le, hz.2.le⟩]; ring
    rw [h0]
    exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq hev.symm
  · have hzy : z ≠ y := fun h => hz (h ▸ hy)
    obtain ⟨K₁, -, hK⟩ := c05_aux_chiY_deriv_bound
    have hχ := (hK Y hY z).1
    have hd := (hχ.const_sub 1).mul (c05_aux_hasDerivAt_sq_rpow' hzy (-(1 + p) / 2))
    convert hd using 1
    unfold c05_aux_fk
    rw [← hχ.deriv, show -(1 + p) / 2 - 1 = -(3 + p) / 2 by ring]
    ring

/-- Helper: `∂_y c05_aux_fk = c05_aux_fk'` for `y ≠ z`. -/
theorem c05_aux_fk_hasDeriv (p Y : ℝ) {y z : ℝ} (hyz : y ≠ z) :
    HasDerivAt (fun y' => c05_aux_fk p Y y' z) (c05_aux_fk' p Y y z) y := by
  unfold c05_aux_fk
  have h1 := c05_aux_hasDerivAt_sq_rpow hyz (-(1 + p) / 2)
  have h3 := c05_aux_hasDerivAt_sq_rpow hyz (-(3 + p) / 2)
  have hl : HasDerivAt (fun y' : ℝ => y' - z) 1 y := (hasDerivAt_id y).sub_const z
  have := (h1.const_mul (-deriv (res_chiY Y) z)).add
    ((hl.mul h3).const_mul ((1 - res_chiY Y z) * (1 + p)))
  convert this using 1
  · funext y'; simp only [Pi.add_apply, Pi.mul_apply]; ring
  · unfold c05_aux_fk'
    rw [show -(1 + p) / 2 - 1 = -(3 + p) / 2 by ring, show -(3 + p) / 2 - 1 = -(5 + p) / 2 by ring]
    ring

/-- Helper: `c05_aux_fk`, `c05_aux_fk'` vanish for `z ∈ (Y/2,3Y)`. -/
theorem c05_aux_fk_zero (p Y : ℝ) (hY : 0 < Y) {z : ℝ} (hz : z ∈ Ioo (Y / 2) (3 * Y)) (y : ℝ) :
    c05_aux_fk p Y y z = 0 ∧ c05_aux_fk' p Y y z = 0 := by
  unfold c05_aux_fk c05_aux_fk'
  rw [c05_aux_chiY_deriv_zero hY hz, c05_aux_chiY_one hY ⟨hz.1.le, hz.2.le⟩]
  constructor <;> ring

/-- Helper: bounds for the far kernels when `|y - z| ≥ D > 0`. -/
theorem c05_aux_fk_bound (p Y K₁ : ℝ) (hp : 0 < p)
    (hK : ∀ z, |deriv (res_chiY Y) z| ≤ K₁ / Y) {D y z : ℝ} (hD : 0 < D) (hyz : D ≤ |y - z|) :
    |c05_aux_fk p Y y z| ≤ K₁ / Y * D ^ (-(1 + p)) + (1 + p) * D ^ (-(2 + p)) ∧
    |c05_aux_fk' p Y y z| ≤ K₁ / Y * (1 + p) * D ^ (-(2 + p)) + (1 + p) * (4 + p) * D ^ (-(3 + p)) := by
  have ha : 0 < |y - z| := lt_of_lt_of_le hD hyz
  have hne : y - z ≠ 0 := abs_pos.mp ha
  have hχ := c05_aux_chiY_mem Y z
  have h1χ : |1 - res_chiY Y z| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hχ.1, hχ.2]
  have k1 : ((y - z) ^ 2) ^ (-(1 + p) / 2) ≤ D ^ (-(1 + p)) := by
    rw [c05_aux_sq_rpow, show 2 * (-(1 + p) / 2) = -(1 + p) by ring]
    exact Real.rpow_le_rpow_of_nonpos hD hyz (by linarith)
  have k2 : |y - z| * ((y - z) ^ 2) ^ (-(3 + p) / 2) ≤ D ^ (-(2 + p)) := by
    have := c05_aux_abs_mul_sq_rpow hne 1 (-(3 + p) / 2)
    rw [pow_one] at this
    rw [this, show ((1 : ℕ) : ℝ) + 2 * (-(3 + p) / 2) = -(2 + p) by push_cast; ring]
    exact Real.rpow_le_rpow_of_nonpos hD hyz (by linarith)
  have k3 : ((y - z) ^ 2) ^ (-(3 + p) / 2) ≤ D ^ (-(3 + p)) := by
    rw [c05_aux_sq_rpow, show 2 * (-(3 + p) / 2) = -(3 + p) by ring]
    exact Real.rpow_le_rpow_of_nonpos hD hyz (by linarith)
  have k5 : |y - z| ^ 2 * ((y - z) ^ 2) ^ (-(5 + p) / 2) ≤ D ^ (-(3 + p)) := by
    rw [c05_aux_abs_mul_sq_rpow hne 2 (-(5 + p) / 2),
      show ((2 : ℕ) : ℝ) + 2 * (-(5 + p) / 2) = -(3 + p) by push_cast; ring]
    exact Real.rpow_le_rpow_of_nonpos hD hyz (by linarith)
  have p1 : 0 ≤ ((y - z) ^ 2) ^ (-(1 + p) / 2) := Real.rpow_nonneg (sq_nonneg _) _
  have p3 : 0 ≤ ((y - z) ^ 2) ^ (-(3 + p) / 2) := Real.rpow_nonneg (sq_nonneg _) _
  have p5 : 0 ≤ ((y - z) ^ 2) ^ (-(5 + p) / 2) := Real.rpow_nonneg (sq_nonneg _) _
  have hK0 : 0 ≤ K₁ / Y := (abs_nonneg _).trans (hK z)
  constructor
  · unfold c05_aux_fk
    calc _ ≤ |deriv (res_chiY Y) z| * ((y - z) ^ 2) ^ (-(1 + p) / 2) +
          |1 - res_chiY Y z| * (1 + p) * (|y - z| * ((y - z) ^ 2) ^ (-(3 + p) / 2)) := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_neg, abs_of_nonneg p1, abs_mul, abs_mul, abs_mul, abs_of_nonneg p3,
            abs_of_pos (by linarith : (0:ℝ) < 1 + p)]; ring
      _ ≤ K₁ / Y * D ^ (-(1 + p)) + 1 * (1 + p) * D ^ (-(2 + p)) := by
          gcongr
          exact hK z
      _ = _ := by ring
  · unfold c05_aux_fk'
    have hsq : (y - z) ^ 2 = |y - z| ^ 2 := (sq_abs _).symm
    calc _ ≤ |deriv (res_chiY Y) z| * (1 + p) * (|y - z| * ((y - z) ^ 2) ^ (-(3 + p) / 2)) +
          |1 - res_chiY Y z| * (1 + p) * (((y - z) ^ 2) ^ (-(3 + p) / 2) +
            (3 + p) * (|y - z| ^ 2 * ((y - z) ^ 2) ^ (-(5 + p) / 2))) := by
          refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
          · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg p3, abs_of_pos (by linarith : (0:ℝ) < 1 + p)]
            ring
          · rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 + p)]
            gcongr
            refine (abs_sub _ _).trans (le_of_eq ?_)
            rw [abs_of_nonneg p3, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 3 + p),
              abs_of_nonneg p5, abs_pow]
            ring
      _ ≤ K₁ / Y * (1 + p) * D ^ (-(2 + p)) + 1 * (1 + p) * (D ^ (-(3 + p)) + (3 + p) * D ^ (-(3 + p))) := by
          gcongr
          exact hK z
      _ = _ := by ring

/-- Blueprint: lem:c05_far_localization.  For smooth `g` with `g, g'` bounded, `g ∈ L¹`,
`g = 0` on `(-∞,R]`: `|D|^p g' = |D|^p(χ_Y g') + ℛ_{far,Y}[g]` on `(Y/2,3Y)`, both terms `C¹`
there, and `|∂_y^j ℛ_{far,Y}[g](y)| ≤ C Y^{-p-2-j} ‖g‖_{L¹}` on `[Y,2Y]`, `j = 0,1`. -/
theorem c05_far_localization (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → (∃ M : ℝ, ∀ x, |g x| ≤ M ∧ |deriv g x| ≤ M) →
          Integrable g → (∀ x, x ≤ R → g x = 0) →
          (∀ y ∈ Ioo (Y / 2) (3 * Y),
            fracDdy S.p g y = fracD S.p (fun z => res_chiY Y z * deriv g z) y +
              c05_auxiliary_remainders_Rfar S.p Y g y) ∧
          ContDiffOn ℝ 1 (fracD S.p (fun z => res_chiY Y z * deriv g z)) (Ioo (Y / 2) (3 * Y)) ∧
          ContDiffOn ℝ 1 (c05_auxiliary_remainders_Rfar S.p Y g) (Ioo (Y / 2) (3 * Y)) ∧
          ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
            |iteratedDeriv j (c05_auxiliary_remainders_Rfar S.p Y g) y| ≤
              C * Y ^ (-S.p - 2 - j) * ∫ x, |g x| := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := c05_aux_chiY_deriv_bound
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hp1 := S.hp_hi
  have hc0 : 0 ≤ calpha S.p := c01_aux_calpha_nonneg S.p hp0 hp1
  set B0c : ℝ := K₁ * 2 ^ (1 + S.p) + (1 + S.p) * 2 ^ (2 + S.p) with hB0c
  set B1c : ℝ := K₁ * (1 + S.p) * 2 ^ (2 + S.p) + (1 + S.p) * (4 + S.p) * 2 ^ (3 + S.p) with hB1c
  have hB0c0 : 0 ≤ B0c := by positivity
  have hB1c0 : 0 ≤ B1c := by positivity
  refine ⟨1, le_rfl, calpha S.p * (B0c + B1c) + 1, by positivity, ?_⟩
  intro ε μ R Y ht g hg ⟨M, hM⟩ hgi hg0
  have hR : 1 ≤ R := ht.2.2.2.1
  have hY : 0 < Y := by linarith [ht.2.2.2.2]
  have hK : ∀ z, |deriv (res_chiY Y) z| ≤ K₁ / Y := fun z => (hK₁ Y hY z).2
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hg1 : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hχs := c05_aux_chiY_smooth Y
  set B0 : ℝ → ℝ := fun D => K₁ / Y * D ^ (-(1 + S.p)) + (1 + S.p) * D ^ (-(2 + S.p)) with hB0
  set B1 : ℝ → ℝ := fun D => K₁ / Y * (1 + S.p) * D ^ (-(2 + S.p)) +
    (1 + S.p) * (4 + S.p) * D ^ (-(3 + S.p)) with hB1
  have hB00 : ∀ D, 0 < D → 0 ≤ B0 D := fun D hD => by simp only [hB0]; positivity
  have hB10 : ∀ D, 0 < D → 0 ≤ B1 D := fun D hD => by simp only [hB1]; positivity
  -- separation and kernel bounds
  have hsep : ∀ y z D, Y / 2 + D ≤ y → y ≤ 3 * Y - D → z ∉ Ioo (Y / 2) (3 * Y) → D ≤ |y - z| := by
    intro y z D h1 h2 hz
    simp only [mem_Ioo, not_and_or, not_lt] at hz
    rcases hz with hz | hz
    · exact (by linarith : D ≤ y - z).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (by linarith : D ≤ z - y).trans (le_abs_self _)
  have hFb : ∀ y z D, 0 < D → Y / 2 + D ≤ y → y ≤ 3 * Y - D →
      |c05_aux_fk S.p Y y z| ≤ B0 D ∧ |c05_aux_fk' S.p Y y z| ≤ B1 D := by
    intro y z D hD h1 h2
    by_cases hz : z ∈ Ioo (Y / 2) (3 * Y)
    · obtain ⟨e1, e2⟩ := c05_aux_fk_zero S.p Y hY hz y
      rw [e1, e2, abs_zero]; exact ⟨hB00 D hD, hB10 D hD⟩
    · exact c05_aux_fk_bound S.p Y K₁ hp0 hK hD (hsep y z D h1 h2 hz)
  have hχm : Measurable (res_chiY Y) := hχs.continuous.measurable
  have hdχm : Measurable (deriv (res_chiY Y)) := measurable_deriv _
  have hfkm : ∀ y, Measurable (fun z => c05_aux_fk S.p Y y z) := by
    intro y; unfold c05_aux_fk; fun_prop
  have hfkm' : ∀ y, Measurable (fun z => c05_aux_fk' S.p Y y z) := by
    intro y; unfold c05_aux_fk'; fun_prop
  -- `ℛ_far` through the closed-form kernel
  have hRfar : ∀ y ∈ Ioo (Y / 2) (3 * Y), c05_auxiliary_remainders_Rfar S.p Y g y =
      calpha S.p * ∫ z, g z * c05_aux_fk S.p Y y z := by
    intro y hy
    unfold c05_auxiliary_remainders_Rfar
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [(c05_aux_fk_hasDeriv_z S.p Y hY hy z).deriv]
  have hDpos : ∀ y ∈ Ioo (Y / 2) (3 * Y), 0 < min (y - Y / 2) (3 * Y - y) :=
    fun y hy => lt_min (by linarith [hy.1]) (by linarith [hy.2])
  -- (a) the localisation identity
  have hid : ∀ y ∈ Ioo (Y / 2) (3 * Y),
      fracDdy S.p g y = fracD S.p (fun z => res_chiY Y z * deriv g z) y +
        c05_auxiliary_remainders_Rfar S.p Y g y := by
    intro y hy
    set D := min (y - Y / 2) (3 * Y - y) with hD
    have hD0 := hDpos y hy
    have h1 : Y / 2 + D ≤ y := by have := min_le_left (y - Y / 2) (3 * Y - y); linarith
    have h2 : y ≤ 3 * Y - D := by have := min_le_right (y - Y / 2) (3 * Y - y); linarith
    set k : ℝ → ℝ := fun z' => (1 - res_chiY Y z') / |y - z'| ^ (1 + S.p) with hk
    have hkm : Measurable k := by
      simp only [hk]
      exact ((measurable_const.sub hχs.continuous.measurable).div
        ((measurable_const.sub measurable_id).abs.pow_const _))
    have hkb : ∀ z, 0 ≤ k z ∧ k z ≤ (if D ≤ |y - z| then |y - z| ^ (-(1 + S.p)) else 0) := by
      intro z
      have hχ := c05_aux_chiY_mem Y z
      have hk0 : 0 ≤ k z := div_nonneg (by linarith [hχ.2]) (Real.rpow_nonneg (abs_nonneg _) _)
      refine ⟨hk0, ?_⟩
      by_cases hz : z ∈ Ioo (Y / 2) (3 * Y)
      · have : k z = 0 := by
          simp only [hk]; rw [c05_aux_chiY_one hY ⟨hz.1.le, hz.2.le⟩]; simp
        rw [this]; split_ifs <;> [exact Real.rpow_nonneg (abs_nonneg _) _; exact le_rfl]
      · have hs := hsep y z D h1 h2 hz
        simp only [hs, ↓reduceIte]
        rw [Real.rpow_neg (abs_nonneg _)]
        simp only [hk]
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_nonneg.mpr (Real.rpow_nonneg (abs_nonneg _) _))
          (by linarith [hχ.1])
    have hGi : Integrable (fun z => if D ≤ |y - z| then |y - z| ^ (-(1 + S.p)) else 0) := by
      have hφ : IntegrableOn (fun t : ℝ => if D ≤ t then t ^ (-(1 + S.p)) else 0) (Ioi 0) := by
        rw [← Ioo_union_Ici_eq_Ioi hD0]
        refine IntegrableOn.union ?_ ?_
        · refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioo
          simp [not_le.mpr (show t < D from ht.2)]
        · refine ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
            (integrableOn_Ioi_rpow_of_lt (a := -(1 + S.p)) (by linarith) hD0)).congr_fun
            (fun t ht => ?_) measurableSet_Ici
          simp [show D ≤ t from ht]
      have := (c04_aux_c01_integrable_comp_abs hφ).comp_sub_left y
      exact this
    have hki : Integrable k := Integrable.mono' hGi hkm.aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hkb z).1]; exact (hkb z).2)
    have hkbd : ∀ z, |k z| ≤ D ^ (-(1 + S.p)) := by
      intro z
      rw [abs_of_nonneg (hkb z).1]
      refine (hkb z).2.trans ?_
      split_ifs with h
      · exact Real.rpow_le_rpow_of_nonpos hD0 h (by linarith)
      · exact Real.rpow_nonneg hD0.le _
    have hkd : ∀ z, HasDerivAt k (c05_aux_fk S.p Y y z) z := c05_aux_fk_hasDeriv_z S.p Y hY hy
    have hgk : Integrable (fun z => deriv g z * k z) :=
      hki.bdd_mul (c := M) (measurable_deriv g).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hM z).2)
    have hibp : ∫ z, g z * c05_aux_fk S.p Y y z = -∫ z, deriv g z * k z :=
      integral_mul_deriv_eq_deriv_mul_of_integrable (u := g) (v := k) (u' := deriv g)
        (v' := fun z => c05_aux_fk S.p Y y z)
        (fun x _ => (hgd x).hasDerivAt) (fun x _ => hkd x)
        (hgi.mul_bdd (hfkm y).aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact (hFb y z D hD0 h1 h2).1)) hgk
        (hgi.mul_bdd hkm.aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact hkbd z))
    have hu1 : ContDiff ℝ 1 (deriv g) := hg1.of_le (WithTop.coe_le_coe.mpr le_top)
    have hcg : ContDiff ℝ 1 (fun z => res_chiY Y z * deriv g z) :=
      (hχs.mul hg1).of_le (WithTop.coe_le_coe.mpr le_top)
    have hI2 := c05_aux_fracD_integrable S.p hp0 hp1 _ hcg ⟨M, fun x => by
      rw [abs_mul]
      have := c05_aux_chiY_mem Y x
      calc |res_chiY Y x| * |deriv g x| ≤ 1 * M := by
            gcongr
            · rw [abs_of_nonneg this.1]; exact this.2
            · exact (hM x).2
        _ = M := one_mul M⟩ y
    have hχy : res_chiY Y y = 1 := c05_aux_chiY_one hY ⟨hy.1.le, hy.2.le⟩
    rw [hRfar y hy, hibp]
    unfold fracDdy fracD
    have hsplit : ∫ z, (deriv g y - deriv g z) / |y - z| ^ (S.p + 1) =
        (∫ z, (res_chiY Y y * deriv g y - res_chiY Y z * deriv g z) / |y - z| ^ (S.p + 1)) +
          ∫ z, -(deriv g z * k z) := by
      have hgkn : Integrable (fun z => -(deriv g z * k z)) := hgk.neg
      rw [← integral_add hI2 hgkn]
      congr 1; funext z; simp only [hk]; rw [hχy, add_comm 1 S.p]; ring
    rw [hsplit, integral_neg]; ring
  -- the derivative of `ℛ_far`
  have hderR : ∀ y₀ ∈ Ioo (Y / 2) (3 * Y), HasDerivAt (c05_auxiliary_remainders_Rfar S.p Y g)
      (calpha S.p * ∫ z, g z * c05_aux_fk' S.p Y y₀ z) y₀ ∧
      ContinuousAt (fun y => ∫ z, g z * c05_aux_fk' S.p Y y z) y₀ := by
    intro y₀ hy₀
    set D := min (y₀ - Y / 2) (3 * Y - y₀) / 2 with hD
    have hD0 : 0 < D := by have := hDpos y₀ hy₀; rw [hD]; linarith
    have hball : ∀ y ∈ Metric.ball y₀ D, Y / 2 + D ≤ y ∧ y ≤ 3 * Y - D := by
      intro y hyb
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyb
      have h1 := min_le_left (y₀ - Y / 2) (3 * Y - y₀)
      have h2 := min_le_right (y₀ - Y / 2) (3 * Y - y₀)
      exact ⟨by linarith, by linarith⟩
    have hbi : Integrable (fun z => |g z| * B1 D) := hgi.abs.mul_const _
    have hFm : ∀ y, AEStronglyMeasurable (fun z => g z * c05_aux_fk S.p Y y z) volume :=
      fun y => (hgd.continuous.measurable.mul (hfkm y)).aestronglyMeasurable
    have hF'm : ∀ y, AEStronglyMeasurable (fun z => g z * c05_aux_fk' S.p Y y z) volume :=
      fun y => (hgd.continuous.measurable.mul (hfkm' y)).aestronglyMeasurable
    have hb : ∀ z, ∀ y ∈ Metric.ball y₀ D, ‖g z * c05_aux_fk' S.p Y y z‖ ≤ |g z| * B1 D := by
      intro z y hyb
      obtain ⟨h1, h2⟩ := hball y hyb
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hFb y z D hD0 h1 h2).2 (abs_nonneg _)
    have hdiff : ∀ z, ∀ y ∈ Metric.ball y₀ D,
        HasDerivAt (fun y => g z * c05_aux_fk S.p Y y z) (g z * c05_aux_fk' S.p Y y z) y := by
      intro z y hyb
      by_cases hz : z ∈ Ioo (Y / 2) (3 * Y)
      · have e : (fun y => g z * c05_aux_fk S.p Y y z) = fun _ => 0 := by
          funext y'; rw [(c05_aux_fk_zero S.p Y hY hz y').1, mul_zero]
        rw [e, (c05_aux_fk_zero S.p Y hY hz y).2, mul_zero]
        exact hasDerivAt_const _ _
      · obtain ⟨h1, h2⟩ := hball y hyb
        have hs := hsep y z D h1 h2 hz
        have hyz : y ≠ z := fun h => by rw [h, sub_self, abs_zero] at hs; linarith
        exact (c05_aux_fk_hasDeriv S.p Y hyz).const_mul (g z)
    have hy₀b : y₀ ∈ Metric.ball y₀ D := Metric.mem_ball_self hD0
    have hFi : Integrable (fun z => g z * c05_aux_fk S.p Y y₀ z) :=
      hgi.mul_bdd (hfkm y₀).aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact (hFb y₀ z D hD0 (hball y₀ hy₀b).1 (hball y₀ hy₀b).2).1)
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := y₀)
      (F := fun y z => g z * c05_aux_fk S.p Y y z) (F' := fun y z => g z * c05_aux_fk' S.p Y y z)
      (bound := fun z => |g z| * B1 D) (Metric.ball_mem_nhds y₀ hD0)
      (Eventually.of_forall hFm) hFi (hF'm y₀) (Eventually.of_forall hb) hbi
      (Eventually.of_forall hdiff)
    refine ⟨(hmain.2.const_mul (calpha S.p)).congr_of_eventuallyEq ?_, ?_⟩
    · filter_upwards [Ioo_mem_nhds hy₀.1 hy₀.2] with y hy
      exact hRfar y hy
    · refine continuousAt_of_dominated (Eventually.of_forall hF'm) ?_ hbi
        (Eventually.of_forall fun z => ?_)
      · filter_upwards [Metric.ball_mem_nhds y₀ hD0] with y hy
        exact Eventually.of_forall fun z => hb z y hy
      · by_cases hz : z ∈ Ioo (Y / 2) (3 * Y)
        · have e : (fun y => g z * c05_aux_fk' S.p Y y z) = fun _ => 0 := by
            funext y'; rw [(c05_aux_fk_zero S.p Y hY hz y').2, mul_zero]
          rw [e]; exact continuousAt_const
        · obtain ⟨h1, h2⟩ := hball y₀ hy₀b
          have hs := hsep y₀ z D h1 h2 hz
          have hne : (y₀ - z) ^ 2 ≠ 0 := by
            apply pow_ne_zero; intro h; rw [h, abs_zero] at hs; linarith
          have hq : ContinuousAt (fun y => (y - z) ^ 2) y₀ := by fun_prop
          have h3 := hq.rpow_const (p := -(3 + S.p) / 2) (Or.inl hne)
          have h5 := hq.rpow_const (p := -(5 + S.p) / 2) (Or.inl hne)
          unfold c05_aux_fk'
          exact continuousAt_const.mul ((((continuousAt_const.mul
            ((continuousAt_id.sub continuousAt_const))).mul h3)).add
            (continuousAt_const.mul (h3.sub (((continuousAt_const.mul hq)).mul h5))))
  refine ⟨hid, ?_, ?_, ?_⟩
  · -- (b) regularity of `|D|^p(χ_Y g')`
    have hu : ContDiff ℝ (⊤ : ℕ∞) (fun z => res_chiY Y z * deriv g z) := hχs.mul hg1
    have hχc : HasCompactSupport (res_chiY Y) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := 3 * Y / 10) (b := 7 * Y / 2)) ?_
      intro x hx
      simp only [mem_Icc, not_and_or, not_le] at hx
      exact c05_aux_chiY_zero hY (hx.imp le_of_lt le_of_lt)
    have hucs : HasCompactSupport (fun z => res_chiY Y z * deriv g z) := hχc.mul_right
    obtain ⟨M0, hM0⟩ := hu.continuous.bounded_above_of_compact_support hucs
    obtain ⟨M1, hM1⟩ := (hu.continuous_deriv (by simp)).bounded_above_of_compact_support hucs.deriv
    exact (c04_aux_fracD_C1 S.p S.hp_lo S.hp_hi _ (hu.of_le (WithTop.coe_le_coe.mpr le_top)) M0 M1
      (fun x => by simpa [Real.norm_eq_abs] using hM0 x)
      (fun x => by simpa [Real.norm_eq_abs] using hM1 x)).contDiffOn
  · -- (c) regularity of `ℛ_far`
    have := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 0)
      (f := c05_auxiliary_remainders_Rfar S.p Y g) isOpen_Ioo).mpr
      ⟨fun y hy => (hderR y hy).1.differentiableAt.differentiableWithinAt, by simp, ?_⟩
    · simpa using this
    rw [contDiffOn_zero]
    refine ContinuousOn.congr (f := fun y => calpha S.p * ∫ z, g z * c05_aux_fk' S.p Y y z) ?_ ?_
    · exact fun y hy => (continuousAt_const.mul (hderR y hy).2).continuousWithinAt
    · exact fun y hy => (hderR y hy).1.deriv
  · -- (d) the bounds on `[Y,2Y]`
    intro y hy j hj
    have hy' : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h1 : Y / 2 + Y / 2 ≤ y := by linarith [hy.1]
    have h2 : y ≤ 3 * Y - Y / 2 := by linarith [hy.2]
    have hY2 : 0 < Y / 2 := by linarith
    have hpw : ∀ a : ℝ, (Y / 2) ^ (-a) = 2 ^ a * Y ^ (-a) := fun a => by
      rw [Real.div_rpow hY.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    have hYm : ∀ a : ℝ, Y⁻¹ * Y ^ (-a) = Y ^ (-a - 1) := fun a => by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hY]; ring_nf
    have hgabs : 0 ≤ ∫ x, |g x| := integral_nonneg (fun _ => abs_nonneg _)
    have hint : ∀ (B : ℝ) (f : ℝ → ℝ), Measurable f → (∀ z, |f z| ≤ B) →
        |∫ z, g z * f z| ≤ (∫ x, |g x|) * B := by
      intro B f hf hfb
      rw [← integral_mul_const, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (hgi.abs.mul_const _) (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hfb z) (abs_nonneg _)
    have hC : calpha S.p * B0c ≤ calpha S.p * (B0c + B1c) + 1 ∧
        calpha S.p * B1c ≤ calpha S.p * (B0c + B1c) + 1 := by
      constructor <;> nlinarith [mul_nonneg hc0 hB0c0, mul_nonneg hc0 hB1c0]
    have hYp : ∀ a : ℝ, 0 ≤ Y ^ a := fun a => Real.rpow_nonneg hY.le a
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      rw [hRfar y hy', abs_mul, abs_of_nonneg hc0]
      have hb := hint (B0 (Y / 2)) _ (hfkm y) (fun z => (hFb y z (Y / 2) hY2 h1 h2).1)
      have hB0e : B0 (Y / 2) = B0c * Y ^ (-S.p - 2) := by
        simp only [hB0, hB0c]
        rw [hpw, hpw, div_eq_mul_inv]
        have := hYm (1 + S.p)
        rw [show -(2 + S.p) = -S.p - 2 by ring, show -(1 + S.p) - 1 = -S.p - 2 by ring] at *
        calc K₁ * Y⁻¹ * (2 ^ (1 + S.p) * Y ^ (-(1 + S.p))) + (1 + S.p) * (2 ^ (2 + S.p) * Y ^ (-S.p - 2))
            = K₁ * 2 ^ (1 + S.p) * (Y⁻¹ * Y ^ (-(1 + S.p))) +
              (1 + S.p) * 2 ^ (2 + S.p) * Y ^ (-S.p - 2) := by ring
          _ = _ := by rw [this]; ring
      rw [hB0e] at hb
      calc calpha S.p * |∫ z, g z * c05_aux_fk S.p Y y z| ≤
          calpha S.p * ((∫ x, |g x|) * (B0c * Y ^ (-S.p - 2))) := mul_le_mul_of_nonneg_left hb hc0
        _ = (calpha S.p * B0c) * Y ^ (-S.p - 2) * ∫ x, |g x| := by ring
        _ ≤ (calpha S.p * (B0c + B1c) + 1) * Y ^ (-S.p - 2) * ∫ x, |g x| := by
            gcongr; exact hC.1
    · simp only [iteratedDeriv_one, Nat.cast_one]
      rw [(hderR y hy').1.deriv, abs_mul, abs_of_nonneg hc0]
      have hb := hint (B1 (Y / 2)) _ (hfkm' y) (fun z => (hFb y z (Y / 2) hY2 h1 h2).2)
      have hB1e : B1 (Y / 2) = B1c * Y ^ (-S.p - 2 - 1) := by
        simp only [hB1, hB1c]
        rw [hpw, hpw, div_eq_mul_inv]
        have := hYm (2 + S.p)
        rw [show -(3 + S.p) = -S.p - 2 - 1 by ring, show -(2 + S.p) - 1 = -S.p - 2 - 1 by ring] at *
        calc K₁ * Y⁻¹ * (1 + S.p) * (2 ^ (2 + S.p) * Y ^ (-(2 + S.p))) +
              (1 + S.p) * (4 + S.p) * (2 ^ (3 + S.p) * Y ^ (-S.p - 2 - 1))
            = K₁ * (1 + S.p) * 2 ^ (2 + S.p) * (Y⁻¹ * Y ^ (-(2 + S.p))) +
              (1 + S.p) * (4 + S.p) * 2 ^ (3 + S.p) * Y ^ (-S.p - 2 - 1) := by ring
          _ = _ := by rw [this]; ring
      rw [hB1e] at hb
      calc calpha S.p * |∫ z, g z * c05_aux_fk' S.p Y y z| ≤
          calpha S.p * ((∫ x, |g x|) * (B1c * Y ^ (-S.p - 2 - 1))) := mul_le_mul_of_nonneg_left hb hc0
        _ = (calpha S.p * B1c) * Y ^ (-S.p - 2 - 1) * ∫ x, |g x| := by ring
        _ ≤ (calpha S.p * (B0c + B1c) + 1) * Y ^ (-S.p - 2 - 1) * ∫ x, |g x| := by
            gcongr; exact hC.2


/-! ### The linear remainder `ℛ_lin` -/

/-- Helper: `y^θ ≤ 4^{|θ|} Y^θ` for `y ∈ (Y/4, 4Y)`. -/
theorem c05_aux_yY_rpow {Y y : ℝ} (hY : 0 < Y) (hy : y ∈ Ioo (Y / 4) (4 * Y)) (θ : ℝ) :
    y ^ θ ≤ 4 ^ |θ| * Y ^ θ := by
  have hy0 : 0 < y := lt_trans (by positivity) hy.1
  rcases le_or_gt 0 θ with h | h
  · calc y ^ θ ≤ (4 * Y) ^ θ := Real.rpow_le_rpow hy0.le hy.2.le h
      _ = 4 ^ |θ| * Y ^ θ := by rw [abs_of_nonneg h, Real.mul_rpow (by norm_num) hY.le]
  · calc y ^ θ ≤ (Y / 4) ^ θ := Real.rpow_le_rpow_of_nonpos (by positivity) hy.1.le h.le
      _ = 4 ^ |θ| * Y ^ θ := by
        rw [abs_of_neg h, Real.div_rpow hY.le (by norm_num), Real.rpow_neg (by norm_num)]
        field_simp

/-- Helper: bounds for the iterated derivatives of `χ`. -/
theorem c05_aux_chiAnnulus_iter (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |iteratedDeriv m chiAnnulus x| ≤ B := by
  have hcs0 : HasCompactSupport chiAnnulus := by
    refine HasCompactSupport.intro (isCompact_Icc (a := 3 / 10) (b := 7 / 2)) ?_
    intro x hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    have := c05_aux_chiY_zero (Y := 1) (z := x) one_pos (hx.imp (fun h => by linarith) (fun h => by linarith))
    simpa [res_chiY] using this
  have hcs : ∀ n : ℕ, HasCompactSupport (deriv^[n] chiAnnulus) := by
    intro n
    induction n with
    | zero => simpa using hcs0
    | succ n ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  have hc := c05_aux_chiAnnulus_smooth.continuous_iteratedDeriv m (by exact_mod_cast le_top)
  rw [iteratedDeriv_eq_iterate] at hc ⊢
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (hcs m)
  exact ⟨max B 0, le_max_right _ _, fun x => (by simpa [Real.norm_eq_abs] using hB x : _ ≤ B).trans
    (le_max_left _ _)⟩

/-- Helper: `|∂^i χ_Y| ≤ B_i Y^{-i}`. -/
theorem c05_aux_chiY_iter (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ Y : ℝ, 0 < Y → ∀ x,
    |iteratedDeriv m (res_chiY Y) x| ≤ B * Y⁻¹ ^ m := by
  obtain ⟨B, hB0, hB⟩ := c05_aux_chiAnnulus_iter m
  refine ⟨B, hB0, fun Y hY x => ?_⟩
  have e : res_chiY Y = fun z => chiAnnulus (Y⁻¹ * z) := by
    funext z; simp [res_chiY, div_eq_inv_mul]
  rw [e, iteratedDeriv_comp_const_mul (c05_aux_chiAnnulus_smooth.of_le (by exact_mod_cast le_top))]
  rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hY), mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _) (by positivity)

/-- Helper: Leibniz with the cutoff `χ_Y` on `(Y/4,4Y)`. -/
theorem c05_aux_cutoff_leibniz (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ (f : ℝ → ℂ) (y Af a : ℝ),
    y ∈ Ioo (Y / 4) (4 * Y) → ContDiffAt ℝ k f y → 0 ≤ Af →
    (∀ i, i ≤ k → ‖iteratedDeriv i f y‖ ≤ Af * y ^ (a + (i : ℝ) * (-1))) →
    ‖iteratedDeriv k (fun z => (res_chiY Y z : ℂ) * f z) y‖ ≤ K * 4 ^ (|a| + k) * Af * Y ^ (a - k) := by
  choose B hB0 hB using c05_aux_chiY_iter
  set Kχ := ∑ i ∈ Finset.range (k + 1), B i * 4 ^ i with hKχ
  have hKχ0 : 0 ≤ Kχ := Finset.sum_nonneg (fun i _ => by have := hB0 i; positivity)
  refine ⟨2 ^ k * Kχ, by positivity, fun Y hY f y Af a hy hf hAf hfb => ?_⟩
  have hy0 : 0 < y := lt_trans (by positivity) hy.1
  have hχc : ContDiffAt ℝ k (fun z => (res_chiY Y z : ℂ)) y :=
    c05_aux_ofReal (((c05_aux_chiY_smooth Y).of_le (by exact_mod_cast le_top)).contDiffAt)
  have hχb : ∀ i, i ≤ k → ‖iteratedDeriv i (fun z => (res_chiY Y z : ℂ)) y‖ ≤ Kχ * y ^ (0 + (i : ℝ) * (-1)) := by
    intro i hi
    rw [c04_aux_iteratedDeriv_ofReal _ y i ((c05_aux_chiY_smooth Y).of_le
      (by exact_mod_cast le_top)).contDiffAt, Complex.norm_real, Real.norm_eq_abs]
    refine (hB i Y hY y).trans ?_
    have hyi : Y⁻¹ ≤ 4 * y⁻¹ := by
      rw [inv_le_comm₀ hY (by positivity), mul_inv, inv_inv]
      have := hy.2; linarith
    have hBi : B i * 4 ^ i ≤ Kχ :=
      Finset.single_le_sum (f := fun i => B i * 4 ^ i) (fun j _ => by have := hB0 j; positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    calc B i * Y⁻¹ ^ i ≤ B i * (4 * y⁻¹) ^ i := by
          have := hB0 i
          gcongr
      _ = (B i * 4 ^ i) * y ^ (0 + (i : ℝ) * (-1)) := by
          rw [mul_pow, zero_add, show (i : ℝ) * (-1) = -(i : ℝ) by ring, Real.rpow_neg hy0.le,
            Real.rpow_natCast, inv_pow]; ring
      _ ≤ Kχ * y ^ (0 + (i : ℝ) * (-1)) := mul_le_mul_of_nonneg_right hBi (by positivity)
  have hL := c04_aux_leibniz_all (fun z => (res_chiY Y z : ℂ)) f y hy0 k hχc hf Kχ Af 0 a (-1)
    hKχ0 hAf hχb hfb k le_rfl
  have hcv := c05_aux_yY_rpow hY hy (a - k)
  have h4 : (4 : ℝ) ^ |a - k| ≤ 4 ^ (|a| + k) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := abs_sub a (k : ℝ)
    rwa [Nat.abs_cast] at this
  calc ‖iteratedDeriv k (fun z => (res_chiY Y z : ℂ) * f z) y‖ ≤ 2 ^ k * (Kχ * Af) * y ^ (0 + a + k * (-1)) := hL
    _ = 2 ^ k * (Kχ * Af) * y ^ (a - k) := by congr 2; ring
    _ ≤ 2 ^ k * (Kχ * Af) * (4 ^ (|a| + k) * Y ^ (a - k)) := by
        gcongr
        exact hcv.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
    _ = _ := by ring

/-- Blueprint: lem:c05_multiplier_hypotheses.  On `I_Y = (Y/4,4Y)`, with `Λ = Y^{1/p}`,
`δ_Y = εY^{1/p-p}`, `a₁ = χ_Y A`, `a₀ = χ_Y A₀`, `a₃ = χ_Y A³` (smooth, supported in `I_Y`):
(1) `(a₁,Φ)`, `(a₀,Φ₀)` satisfy the hypotheses of the oscillatory multiplier lemma with amplitude
size `Y^{-β}` and frequency size `Λ`; (2) the difference hypotheses with `δ = δ_Y`;
(3) `(a₃, 3Φ)` satisfies them with amplitude size `Y^{-3β}`.  (`c_*` uniform, `C_k` depends on `k`.) -/
theorem c05_multiplier_hypotheses (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ cstar : ℝ, 0 < cstar ∧ ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        let IY := Ioo (Y / 4) (4 * Y)
        let Λ := Y ^ (1 / S.p)
        let δY := ε * Y ^ (1 / S.p - S.p)
        let Φ := c05_standing_Phi S.p R ε μ
        let Φ₀ := c05_standing_Phi_zero S.p
        let a₁ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A S.p ε μ z
        let a₀ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A_zero S.p μ z
        let a₃ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A S.p ε μ z ^ 3
        (ContDiff ℝ (⊤ : ℕ∞) a₁ ∧ ContDiff ℝ (⊤ : ℕ∞) a₀ ∧ ContDiff ℝ (⊤ : ℕ∞) a₃ ∧
          tsupport a₁ ⊆ IY ∧ tsupport a₀ ⊆ IY ∧ tsupport a₃ ⊆ IY ∧
          ContDiffOn ℝ (⊤ : ℕ∞) Φ IY ∧ ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ IY) ∧
        ∀ y ∈ IY,
          -- (1)
          (cstar * Λ ≤ deriv Φ y ∧ deriv Φ y ≤ cstar⁻¹ * Λ ∧
            cstar * Λ ≤ deriv Φ₀ y ∧ deriv Φ₀ y ≤ cstar⁻¹ * Λ ∧
            |iteratedDeriv k (deriv Φ) y| ≤ C * Λ * Y ^ (-(k : ℝ)) ∧
            |iteratedDeriv k (deriv Φ₀) y| ≤ C * Λ * Y ^ (-(k : ℝ)) ∧
            ‖iteratedDeriv k a₁ y‖ ≤ C * Y ^ (-beta S.p - k) ∧
            ‖iteratedDeriv k a₀ y‖ ≤ C * Y ^ (-beta S.p - k)) ∧
          -- (2)
          (‖iteratedDeriv k (fun z => a₁ z - a₀ z) y‖ ≤ C * δY * Y ^ (-beta S.p) * Y ^ (-(k : ℝ)) ∧
            |iteratedDeriv k (fun z => Φ z - Φ₀ z) y| ≤ C * δY * Y ^ (-(k : ℝ))) ∧
          -- (3)
          (cstar * Λ ≤ deriv (fun z => 3 * Φ z) y ∧ deriv (fun z => 3 * Φ z) y ≤ cstar⁻¹ * Λ ∧
            |iteratedDeriv k (deriv (fun z => 3 * Φ z)) y| ≤ C * Λ * Y ^ (-(k : ℝ)) ∧
            ‖iteratedDeriv k a₃ y‖ ≤ C * Y ^ (-3 * beta S.p - k)) := by
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  choose Cs hCs hsb using hsym
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hp1 := S.hp_hi
  have hβ0 : 0 ≤ beta S.p := by unfold beta; positivity
  have hip : 1 / S.p ≤ 3 / 2 := by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith [S.hp_lo]
  have h48 : (4 : ℝ) ^ (1 / S.p) ≤ 8 := by
    calc (4 : ℝ) ^ (1 / S.p) ≤ 4 ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hip
      _ = 8 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  refine ⟨Rs, hRs, 1 / 48, by norm_num, fun k => ?_⟩
  obtain ⟨KL, hKL0, hKL⟩ := c05_aux_cutoff_leibniz k
  set Ck : ℝ := ∑ i ∈ Finset.range (k + 1), Cs i with hCk
  have hCk0 : 0 ≤ Ck := Finset.sum_nonneg fun i _ => (hCs i).le
  have hCsk : ∀ i, i ≤ k → Cs i ≤ Ck := fun i hi =>
    Finset.single_le_sum (f := Cs) (fun j _ => (hCs j).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  set C3 : ℝ := 2 ^ k * (Ck * (2 ^ k * (Ck * Ck))) with hC3
  have hC30 : 0 ≤ C3 := by positivity
  set Cl : ℝ := 6 * Ck * 4 ^ (1 / S.p + k) with hCl
  set Ca : ℝ := KL * 4 ^ (beta S.p + k) * Ck with hCa
  set Cd : ℝ := KL * 4 ^ (beta S.p + S.p + 1 + k) * Ck with hCd
  set Cf : ℝ := Ck * 4 ^ (|1 / S.p - S.p| + k) with hCf
  set Ca3 : ℝ := KL * 4 ^ (3 * beta S.p + k) * C3 with hCa3
  have hCl0 : 0 ≤ Cl := by positivity
  have hCa0 : 0 ≤ Ca := by positivity
  have hCd0 : 0 ≤ Cd := by positivity
  have hCf0 : 0 ≤ Cf := by positivity
  have hCa30 : 0 ≤ Ca3 := by positivity
  set C := Cl + Ca + Cd + Cf + Ca3 + 1 with hC
  have hle : ∀ x, 0 ≤ x → x ≤ Cl ∨ x ≤ Ca ∨ x ≤ Cd ∨ x ≤ Cf ∨ x ≤ Ca3 → x ≤ C := by
    intro x _ h; rw [hC]; rcases h with h | h | h | h | h <;> linarith
  refine ⟨C, by positivity, ?_⟩
  intro ε μ R Y ht
  intro IY Λ δY Φ Φ₀ a₁ a₀ a₃
  have hR : 1 ≤ R := hRs.trans ht.2.2.2.1
  have hY8 : 8 * R ≤ Y := ht.2.2.2.2
  have hY : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hRY : R < 3 * Y / 10 := by linarith
  have hε0 : 0 ≤ ε := ht.1
  have hε1 : ε ≤ 1 := ht.2.1.trans S.hε₀_le
  have hlpos : ∀ t, R ≤ t → 0 < fam_lambda S.p ε μ t := by
    intro t htt
    have h1 := ((hsb 0) ε μ R Y ht t htt).1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  -- smoothness of the amplitudes
  have hAs : ∀ t, R < t → ∀ n : ℕ∞, ContDiffAt ℝ n (c05_standing_A S.p ε μ) t := by
    intro t htt n
    have ht0 : 0 < t := by linarith
    unfold c05_standing_A
    exact (contDiffAt_const.mul (c05_aux_astar_smooth S.p S.hp_lo S.hp_hi ht0)).mul
      (c05_aux_ofReal ((c05_aux_lambda_smooth S.p ε μ ht0).rpow_const_of_ne (hlpos t htt.le).ne'))
  have hA0s : ∀ t, 0 < t → ∀ n : ℕ∞, ContDiffAt ℝ n (c05_standing_A_zero S.p μ) t := by
    intro t ht0 n
    unfold c05_standing_A_zero lambda0
    exact (contDiffAt_const.mul (c05_aux_astar_smooth S.p S.hp_lo S.hp_hi ht0)).mul
      (c05_aux_ofReal ((c05_aux_rpow_at ht0).rpow_const_of_ne (Real.rpow_pos_of_pos ht0 _).ne'))
  have hχsub : tsupport (fun z => (res_chiY Y z : ℂ)) ⊆ IY := by
    refine (closure_minimal (s := Function.support fun z => (res_chiY Y z : ℂ))
      (t := Icc (3 * Y / 10) (7 * Y / 2)) ?_ isClosed_Icc).trans ?_
    · intro x hx
      by_contra hn
      simp only [mem_Icc, not_and_or, not_le] at hn
      apply hx
      simp [c05_aux_chiY_zero hY (hn.imp le_of_lt le_of_lt)]
    · intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hΦs : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Ioi 0) :=
    (c05_aux_Psi_smooth S.p R ε μ (by linarith)).sub contDiffOn_const
  have hΦ₀s : ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ (Ioi 0) := fun t ht =>
    ((contDiffAt_const.mul (c05_aux_rpow_at (ht : (0:ℝ) < t))).sub contDiffAt_const).contDiffWithinAt
  have hIY : IY ⊆ Ioi 0 := fun t ht => lt_trans (by positivity) ht.1
  refine ⟨⟨(c05_aux_cutoff_mul hY hRY (fun t ht => hAs t ht _)).1,
    (c05_aux_cutoff_mul hY hRY (fun t ht => hA0s t (by linarith) _)).1,
    (c05_aux_cutoff_mul hY hRY (fun t ht => (hAs t ht _).pow 3)).1,
    tsupport_mul_subset_left.trans hχsub, tsupport_mul_subset_left.trans hχsub,
    tsupport_mul_subset_left.trans hχsub, hΦs.mono hIY, hΦ₀s.mono hIY⟩, ?_⟩
  intro y hy
  have hy0 : 0 < y := hIY hy
  have hRy : R ≤ y := by have := hy.1; linarith
  have hy1 : 1 ≤ y := hR.trans hRy
  have hb := fun i => (hsb i) ε μ R Y ht y hRy
  -- `y^{1/p}` versus `Λ`
  have hyΛ1 : y ^ (1 / S.p) ≤ 8 * Λ := by
    calc y ^ (1 / S.p) ≤ (4 * Y) ^ (1 / S.p) := Real.rpow_le_rpow hy0.le hy.2.le (by positivity)
      _ = 4 ^ (1 / S.p) * Λ := Real.mul_rpow (by norm_num) hY.le
      _ ≤ 8 * Λ := mul_le_mul_of_nonneg_right h48 (by positivity)
  have hyΛ2 : Λ ≤ 8 * y ^ (1 / S.p) := by
    calc Λ = 4 ^ (1 / S.p) * (Y / 4) ^ (1 / S.p) := by
          show Y ^ (1 / S.p) = _
          rw [← Real.mul_rpow (by norm_num) (by positivity)]; congr 1; ring
      _ ≤ 8 * y ^ (1 / S.p) := mul_le_mul h48 (Real.rpow_le_rpow (by positivity) hy.1.le (by positivity))
          (by positivity) (by norm_num)
  have hΛ0 : 0 < Λ := by positivity
  -- derivatives of the phases
  have hdΦ : deriv Φ =ᶠ[nhds y] fam_lambda S.p ε μ := by
    filter_upwards [Ioi_mem_nhds hy0] with t ht
    exact ((c05_aux_Psi_hasDeriv S.p R ε μ (by linarith) ht).sub_const _).deriv
  have hdΦ₀ : deriv Φ₀ =ᶠ[nhds y] lambda0 S.p := by
    filter_upwards [Ioi_mem_nhds hy0] with t ht
    exact ((c04_aux_Psi0_hasDeriv S.p hp0 t ht).sub_const _).deriv
  have hd3Φ : deriv (fun z => 3 * Φ z) =ᶠ[nhds y] fun z => 3 * fam_lambda S.p ε μ z := by
    filter_upwards [Ioi_mem_nhds hy0] with t ht
    exact (((c05_aux_Psi_hasDeriv S.p R ε μ (by linarith) ht).sub_const _).const_mul 3).deriv
  have hLs : ContDiffAt ℝ k (fam_lambda S.p ε μ) y := c05_aux_lambda_smooth S.p ε μ hy0
  have hL0s : ContDiffAt ℝ k (lambda0 S.p) y := c05_aux_rpow_at hy0
  have hl := (hb 0).1
  obtain ⟨hl1, hl2, -, -, -⟩ := hl
  have hlk := (hb k).1.2.2.1
  have hdlk := (hb k).1.2.2.2.1
  have hdpk := (hb k).1.2.2.2.2
  -- `|∂^k λ| ≤ Ck y^{1/p-k} ≤ (Cl/6) Λ Y^{-k}`
  have hconv : ∀ c : ℝ, 0 ≤ c → c * y ^ (1 / S.p - k) ≤ c * 4 ^ (1 / S.p + k) * (Λ * Y ^ (-(k : ℝ))) := by
    intro c hc
    have h1 := c05_aux_yY_rpow hY hy (1 / S.p - k)
    have h2 : (4 : ℝ) ^ |1 / S.p - k| ≤ 4 ^ (1 / S.p + k) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have := abs_sub (1 / S.p) (k : ℝ)
      rwa [Nat.abs_cast, abs_of_pos (by positivity : (0:ℝ) < 1 / S.p)] at this
    have h3 : Y ^ (1 / S.p - k) = Λ * Y ^ (-(k : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hY]
    calc c * y ^ (1 / S.p - k) ≤ c * (4 ^ |1 / S.p - k| * Y ^ (1 / S.p - k)) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ ≤ c * (4 ^ (1 / S.p + k) * Y ^ (1 / S.p - k)) := by gcongr
      _ = _ := by rw [h3]; ring
  have hΛY : 0 ≤ Λ * Y ^ (-(k : ℝ)) := by positivity
  have hlamk : |iteratedDeriv k (fam_lambda S.p ε μ) y| ≤ Ck * y ^ (1 / S.p - k) :=
    hlk.trans (mul_le_mul_of_nonneg_right (hCsk k le_rfl) (by positivity))
  have hlam0k : |iteratedDeriv k (lambda0 S.p) y| ≤ 2 * Ck * y ^ (1 / S.p - k) := by
    have e : iteratedDeriv k (lambda0 S.p) y = iteratedDeriv k (fam_lambda S.p ε μ) y -
        iteratedDeriv k (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) y := by
      rw [iteratedDeriv_fun_sub hLs hL0s]; ring
    have hyp : y ^ (1 / S.p - S.p - 1 - k) ≤ y ^ (1 / S.p - k) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
    have hd' : |iteratedDeriv k (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) y| ≤
        Ck * y ^ (1 / S.p - k) := by
      refine hdlk.trans ?_
      calc Cs k * ε * y ^ (1 / S.p - S.p - 1 - k) ≤ Ck * 1 * y ^ (1 / S.p - k) :=
            mul_le_mul (mul_le_mul (hCsk k le_rfl) hε1 hε0 hCk0) hyp (by positivity) (by positivity)
        _ = Ck * y ^ (1 / S.p - k) := by ring
    rw [e]
    calc _ ≤ |iteratedDeriv k (fam_lambda S.p ε μ) y| +
          |iteratedDeriv k (fun t => fam_lambda S.p ε μ t - lambda0 S.p t) y| := abs_sub _ _
      _ ≤ Ck * y ^ (1 / S.p - k) + Ck * y ^ (1 / S.p - k) := add_le_add hlamk hd'
      _ = 2 * Ck * y ^ (1 / S.p - k) := by ring
  have hClb : ∀ m : ℝ, 0 ≤ m → m ≤ 6 * Ck → m * 4 ^ (1 / S.p + k) * (Λ * Y ^ (-(k : ℝ))) ≤
      C * Λ * Y ^ (-(k : ℝ)) := by
    intro m hm hm6
    have : m * 4 ^ (1 / S.p + k) ≤ Cl := by rw [hCl]; gcongr
    have := hle _ (by positivity) (Or.inl this)
    calc m * 4 ^ (1 / S.p + k) * (Λ * Y ^ (-(k : ℝ))) ≤ C * (Λ * Y ^ (-(k : ℝ))) :=
          mul_le_mul_of_nonneg_right this hΛY
      _ = _ := by ring
  -- amplitude bounds
  have hAb : ∀ i, i ≤ k → ‖iteratedDeriv i (c05_standing_A S.p ε μ) y‖ ≤
      Ck * y ^ (-beta S.p + (i : ℝ) * (-1)) := by
    intro i hi
    have := ((hb i).2.1.1)
    rw [show -beta S.p + (i : ℝ) * (-1) = -beta S.p - i by ring]
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (this.trans
      (mul_le_mul_of_nonneg_right (hCsk i hi) (by positivity)))
  have hA0b : ∀ i, i ≤ k → ‖iteratedDeriv i (c05_standing_A_zero S.p μ) y‖ ≤
      Ck * y ^ (-beta S.p + (i : ℝ) * (-1)) := by
    intro i hi
    have := ((hb i).2.1.1)
    rw [show -beta S.p + (i : ℝ) * (-1) = -beta S.p - i by ring]
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans (this.trans
      (mul_le_mul_of_nonneg_right (hCsk i hi) (by positivity)))
  have hdAb : ∀ i, i ≤ k → ‖iteratedDeriv i
      (fun t => c05_standing_A S.p ε μ t - c05_standing_A_zero S.p μ t) y‖ ≤
      (Ck * ε) * y ^ (-beta S.p - S.p - 1 + (i : ℝ) * (-1)) := by
    intro i hi
    have := ((hb i).2.1.2.1)
    rw [show -beta S.p - S.p - 1 + (i : ℝ) * (-1) = -beta S.p - S.p - 1 - i by ring]
    refine this.trans ?_
    gcongr
    exact hCsk i hi
  have hAy : R < y := by have := hy.1; linarith
  have hAk : ContDiffAt ℝ k (c05_standing_A S.p ε μ) y := hAs y hAy k
  have hA0k : ContDiffAt ℝ k (c05_standing_A_zero S.p μ) y := hA0s y hy0 k
  -- `A³`
  have hAA := c04_aux_leibniz_all _ _ y hy0 k hAk hAk Ck Ck (-beta S.p) (-beta S.p) (-1)
    hCk0 hCk0 hAb hAb
  have hAAA := c04_aux_leibniz_all _ _ y hy0 k hAk (hAk.mul hAk) Ck (2 ^ k * (Ck * Ck))
    (-beta S.p) (-beta S.p + -beta S.p) (-1) hCk0 (by positivity) hAb hAA
  have hA3e : (fun z => c05_standing_A S.p ε μ z ^ 3) =
      c05_standing_A S.p ε μ * (c05_standing_A S.p ε μ * c05_standing_A S.p ε μ) := by
    funext z; simp only [Pi.mul_apply]; ring
  have hA3b : ∀ i, i ≤ k → ‖iteratedDeriv i (fun z => c05_standing_A S.p ε μ z ^ 3) y‖ ≤
      C3 * y ^ (-3 * beta S.p + (i : ℝ) * (-1)) := by
    intro i hi
    rw [hA3e]
    refine (hAAA i hi).trans (le_of_eq ?_)
    rw [hC3]; congr 2; ring
  have hβabs : |-beta S.p| = beta S.p := by rw [abs_neg, abs_of_nonneg hβ0]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hdΦ.eq_of_nhds]
    have : Λ / 16 ≤ fam_lambda S.p ε μ y := by linarith
    linarith [show 1 / 48 * Λ ≤ Λ / 16 by linarith]
  · rw [hdΦ.eq_of_nhds]; norm_num; linarith
  · rw [hdΦ₀.eq_of_nhds]; show 1 / 48 * Λ ≤ y ^ (1 / S.p); linarith
  · rw [hdΦ₀.eq_of_nhds]; show y ^ (1 / S.p) ≤ (1 / 48)⁻¹ * Λ
    rw [show ((1 : ℝ) / 48)⁻¹ = 48 by norm_num]; linarith
  · rw [hdΦ.iteratedDeriv_eq]
    exact (hlamk.trans (hconv Ck hCk0)).trans (hClb Ck hCk0 (by linarith))
  · rw [hdΦ₀.iteratedDeriv_eq]
    refine (hlam0k.trans (hconv (2 * Ck) (by positivity))).trans (hClb (2 * Ck) (by positivity)
      (by linarith))
  · refine (hKL Y hY _ y Ck (-beta S.p) hy hAk hCk0 hAb).trans ?_
    rw [hβabs, show -beta S.p - (k : ℝ) = -beta S.p - k from rfl]
    exact mul_le_mul_of_nonneg_right (hle _ (by positivity) (Or.inr (Or.inl le_rfl))) (by positivity)
  · refine (hKL Y hY _ y Ck (-beta S.p) hy hA0k hCk0 hA0b).trans ?_
    rw [hβabs]
    exact mul_le_mul_of_nonneg_right (hle _ (by positivity) (Or.inr (Or.inl le_rfl))) (by positivity)
  · have e : (fun z => a₁ z - a₀ z) = fun z => (res_chiY Y z : ℂ) *
        (c05_standing_A S.p ε μ z - c05_standing_A_zero S.p μ z) := by
      funext z; simp only [a₁, a₀]; ring
    rw [e]
    refine (hKL Y hY _ y (Ck * ε) (-beta S.p - S.p - 1) hy (hAk.sub hA0k) (by positivity)
      hdAb).trans ?_
    have habs : |-beta S.p - S.p - 1| = beta S.p + S.p + 1 := by
      rw [abs_of_neg (by linarith)]; ring
    rw [habs]
    have hYe : Y ^ (-beta S.p - S.p - 1 - k) ≤ Y ^ (1 / S.p - S.p) * Y ^ (-beta S.p) * Y ^ (-(k : ℝ)) := by
      rw [← Real.rpow_add hY, ← Real.rpow_add hY]
      have h := (show (0:ℝ) < 1 / S.p by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have hKd : KL * 4 ^ (beta S.p + S.p + 1 + k) * Ck ≤ C := hle _ (by positivity) (Or.inr (Or.inr (Or.inl le_rfl)))
    calc KL * 4 ^ (beta S.p + S.p + 1 + k) * (Ck * ε) * Y ^ (-beta S.p - S.p - 1 - k)
        ≤ KL * 4 ^ (beta S.p + S.p + 1 + k) * (Ck * ε) *
          (Y ^ (1 / S.p - S.p) * Y ^ (-beta S.p) * Y ^ (-(k : ℝ))) := by gcongr
      _ = (KL * 4 ^ (beta S.p + S.p + 1 + k) * Ck) *
          (ε * Y ^ (1 / S.p - S.p) * Y ^ (-beta S.p) * Y ^ (-(k : ℝ))) := by ring
      _ ≤ C * (ε * Y ^ (1 / S.p - S.p) * Y ^ (-beta S.p) * Y ^ (-(k : ℝ))) :=
          mul_le_mul_of_nonneg_right hKd (by positivity)
      _ = _ := by simp only [δY]; ring
  · have e : (fun z => Φ z - Φ₀ z) = fun t => fam_Psi S.p R ε μ t - Psi0 S.p t := by
      funext z; simp only [Φ, Φ₀, c05_standing_Phi, c05_standing_Phi_zero]; ring
    rw [e]
    have h1 := c05_aux_yY_rpow hY hy (1 / S.p - S.p - k)
    have h2 : (4 : ℝ) ^ |1 / S.p - S.p - k| ≤ 4 ^ (|1 / S.p - S.p| + k) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have := abs_sub (1 / S.p - S.p) (k : ℝ)
      rwa [Nat.abs_cast] at this
    have hKf : Ck * 4 ^ (|1 / S.p - S.p| + k) ≤ C :=
      hle _ (by positivity) (Or.inr (Or.inr (Or.inr (Or.inl le_rfl))))
    calc _ ≤ Cs k * ε * y ^ (1 / S.p - S.p - k) := hdpk
      _ ≤ Ck * ε * (4 ^ (|1 / S.p - S.p| + k) * Y ^ (1 / S.p - S.p - k)) := by
          gcongr
          · exact hCsk k le_rfl
          · exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
      _ = (Ck * 4 ^ (|1 / S.p - S.p| + k)) * (ε * Y ^ (1 / S.p - S.p) * Y ^ (-(k : ℝ))) := by
          rw [sub_eq_add_neg (1 / S.p - S.p), Real.rpow_add hY]; ring
      _ ≤ C * (ε * Y ^ (1 / S.p - S.p) * Y ^ (-(k : ℝ))) :=
          mul_le_mul_of_nonneg_right hKf (by positivity)
      _ = _ := by simp only [δY]; ring
  · rw [hd3Φ.eq_of_nhds]; linarith
  · rw [hd3Φ.eq_of_nhds]; norm_num; linarith
  · rw [hd3Φ.iteratedDeriv_eq, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    calc 3 * |iteratedDeriv k (fam_lambda S.p ε μ) y| ≤ 3 * (Ck * y ^ (1 / S.p - k)) := by gcongr
      _ = (3 * Ck) * y ^ (1 / S.p - k) := by ring
      _ ≤ _ := (hconv (3 * Ck) (by positivity)).trans (hClb (3 * Ck) (by positivity) (by linarith))
  · refine (hKL Y hY _ y C3 (-3 * beta S.p) hy (hAk.pow 3) hC30 hA3b).trans ?_
    rw [show |-3 * beta S.p| = 3 * beta S.p by rw [abs_of_nonpos (by linarith)]; ring]
    exact mul_le_mul_of_nonneg_right (hle _ (by positivity) (Or.inr (Or.inr (Or.inr (Or.inr le_rfl)))))
      (by positivity)


/-- Helper for lem:c05_fundamental_primitive. -/
theorem c05_aux_exp_phase (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ =
      ‖Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1‖ := by
  have : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, mul_comm (Complex.I) (b : ℂ), Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Helper: `|a^r - b^r| ≤ |r| m^{r-1} |a-b|` for `a, b ≥ m > 0`, `r ≤ 1`. -/
theorem c05_aux_rpow_sub_le {a b m r : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) (hr : r ≤ 1) :
    |a ^ r - b ^ r| ≤ |r| * m ^ (r - 1) * |a - b| := by
  have hd : ∀ t ∈ Ici m, HasDerivWithinAt (fun t : ℝ => t ^ r) (r * t ^ (r - 1)) (Ici m) t :=
    fun t ht => (Real.hasDerivAt_rpow_const (Or.inl (by linarith [mem_Ici.mp ht]))).hasDerivWithinAt
  have hbd : ∀ t ∈ Ici m, ‖r * t ^ (r - 1)‖ ≤ |r| * m ^ (r - 1) := by
    intro t ht
    have ht' : m ≤ t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm ht' (by linarith))
      (abs_nonneg r)
  have := (convex_Ici m).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd hb ha
  simpa [Real.norm_eq_abs] using this

/-- Helper for lem:c05_multiplier_fundamental: the first three Taylor coefficients of the
localized phase-amplitude `F_y(z) = a(y+z)e^{iΘ_y(z)}` (`Θ_y'(0) = 0`). -/
theorem c05_aux_mf_F_derivs (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ 2 a)
    (hΨ : ContDiffOn ℝ 2 Ψ (Ioo (Y / 4) (4 * Y))) {y : ℝ} (hy : y ∈ Ioo (Y / 4) (4 * Y)) :
    iteratedDeriv 0 (c03_mult_F Y a Ψ y) 0 = a y ∧
    iteratedDeriv 1 (c03_mult_F Y a Ψ y) 0 = deriv a y ∧
    iteratedDeriv 2 (c03_mult_F Y a Ψ y) 0 =
      deriv (deriv a) y + Complex.I * ((deriv (deriv Ψ) y : ℝ) : ℂ) * a y := by
  have hU : Ioo (Y / 4) (4 * Y) ∈ nhds y := Ioo_mem_nhds hy.1 hy.2
  set Θ : ℝ → ℝ := c03_mult_Theta Ψ y with hΘ
  set E : ℝ → ℂ := fun z => Complex.exp (Complex.I * (Θ z : ℂ)) with hE
  set g : ℝ → ℂ := fun z => a (y + z) * E z with hg
  have hnear : ∀ᶠ z in nhds (0:ℝ), y + z ∈ Ioo (Y / 4) (4 * Y) := by
    have hc : Continuous (fun z : ℝ => y + z) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  have hFg : c03_mult_F Y a Ψ y =ᶠ[nhds 0] g := by
    filter_upwards [hnear] with z hz
    simp only [c03_mult_F, hz, ite_true, hg, hE, hΘ]
  have hΨ1 := hΨ.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hΨd : ∀ x ∈ Ioo (Y / 4) (4 * Y), HasDerivAt Ψ (deriv Ψ x) x := fun x hx =>
    ((hΨ.contDiffAt (Ioo_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num)).hasDerivAt
  have hΨ2 : HasDerivAt (deriv Ψ) (deriv (deriv Ψ) y) y :=
    ((hΨ1.contDiffAt hU).differentiableAt (by norm_num)).hasDerivAt
  have ha1 : ∀ x, HasDerivAt a (deriv a x) x := fun x =>
    ((ha.differentiable (by norm_num)) x).hasDerivAt
  have ha2 : ∀ x, HasDerivAt (deriv a) (deriv (deriv a) x) x := fun x =>
    (((ha.iterate_deriv' 1 1).differentiable (by norm_num)) x).hasDerivAt
  -- derivative of `Θ` and `E`
  set θ' : ℝ → ℝ := fun z => deriv Ψ (y + z) - deriv Ψ y with hθ'
  have hΘd : ∀ z, y + z ∈ Ioo (Y / 4) (4 * Y) → HasDerivAt Θ (θ' z) z := by
    intro z hz
    have h1 := (hΨd (y + z) hz).comp_const_add y z
    have h2 := ((hasDerivAt_id z).const_mul (deriv Ψ y))
    have := (h1.sub_const (Ψ y)).sub h2
    simp only [hΘ, hθ']
    convert this using 1
    · funext x; simp [c03_mult_Theta]
    · simp
  have hEd : ∀ z, y + z ∈ Ioo (Y / 4) (4 * Y) →
      HasDerivAt E (Complex.I * (θ' z : ℂ) * E z) z := by
    intro z hz
    have := ((hΘd z hz).ofReal_comp.const_mul Complex.I).cexp
    simp only [hE]; convert this using 1; ring
  set g' : ℝ → ℂ := fun z => deriv a (y + z) * E z + a (y + z) * (Complex.I * (θ' z : ℂ) * E z)
    with hg'
  have hgd : ∀ z, y + z ∈ Ioo (Y / 4) (4 * Y) → HasDerivAt g (g' z) z := by
    intro z hz
    exact ((ha1 (y + z)).comp_const_add y z).mul (hEd z hz)
  have hdg : deriv g =ᶠ[nhds 0] g' := by
    filter_upwards [hnear] with z hz using (hgd z hz).deriv
  have h0 : y + 0 ∈ Ioo (Y / 4) (4 * Y) := by simpa using hy
  have hE0 : E 0 = 1 := by simp [hE, hΘ, c03_mult_Theta]
  have hθ0 : θ' 0 = 0 := by simp [hθ']
  -- derivative of `g'` at 0
  have hθd : HasDerivAt θ' (deriv (deriv Ψ) y) 0 := by
    have hΨ2' : HasDerivAt (deriv Ψ) (deriv (deriv Ψ) y) (y + 0) := by rwa [add_zero]
    have := (hΨ2'.comp_const_add y 0).sub_const (deriv Ψ y)
    exact this
  have hg'd : HasDerivAt g' (deriv (deriv a) y + Complex.I * ((deriv (deriv Ψ) y : ℝ) : ℂ) * a y) 0 := by
    have hA1 := (ha2 (y + 0)).comp_const_add y 0
    have hA0 := (ha1 (y + 0)).comp_const_add y 0
    have hE' := hEd 0 h0
    have hθc := ((hθd.ofReal_comp).const_mul Complex.I).mul hE'
    have := (hA1.mul hE').add (hA0.mul hθc)
    convert this using 1
    simp only [Pi.mul_apply, hE0, hθ0, add_zero, Complex.ofReal_zero, mul_zero, zero_mul, mul_one, add_zero]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hFg.iteratedDeriv_eq 0, iteratedDeriv_zero]
    simp [hg, hE0]
  · rw [hFg.iteratedDeriv_eq 1, iteratedDeriv_one, (hgd 0 h0).deriv]
    simp [hg', hE0, hθ0]
  · rw [hFg.iteratedDeriv_eq 2, iteratedDeriv_succ, iteratedDeriv_one, hdg.deriv_eq, hg'd.deriv]

/-- Helper for lem:c05_multiplier_fundamental: on `I_Y`, the chapter-5 remainder
`c05_multiplier_fundamental_Rtilde` is chapter 3's `ℛ̃_{mult,2}` (computation of `B₀,B₁,B₂`). -/
theorem c05_aux_mf_Rtilde_eq (p Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ 2 a)
    (hΨ : ContDiffOn ℝ 2 Ψ (Ioo (Y / 4) (4 * Y))) {y : ℝ} (hy : y ∈ Ioo (Y / 4) (4 * Y)) :
    c05_multiplier_fundamental_Rtilde p a Ψ y = c03_mult_R2tilde p Y a Ψ y := by
  obtain ⟨h0, h1, h2⟩ := c05_aux_mf_F_derivs Y a Ψ ha hΨ hy
  unfold c05_multiplier_fundamental_Rtilde c03_mult_R2tilde c03_mult_R
  rw [show 2 * 2 - 1 = 3 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c03_mult_B, h0, h1, h2,
    c05_aux_iter_rpow]
  simp [descPochhammer_succ_right]
  ring

/-- Helper for lem:c05_multiplier_fundamental: the algebra of the identity part
(`A = μ s L^{-(p+1)/2}`, `A' = μ s' L^{-(p+1)/2} - (p+1)/2 μ s L^{-(p+3)/2} L'`). -/
theorem c05_aux_mf_alg (p L L' : ℝ) (hL : 0 < L) (μ s s' e : ℂ) :
    e * (((L ^ p : ℝ) : ℂ) * (μ * s * ((L ^ (-(p + 1) / 2) : ℝ) : ℂ)) -
      Complex.I * p * ((L ^ (p - 1) : ℝ) : ℂ) *
        (μ * s' * ((L ^ (-(p + 1) / 2) : ℝ) : ℂ) +
          μ * s * ((L' * (-(p + 1) / 2) * L ^ (-(p + 1) / 2 - 1) : ℝ) : ℂ)) -
      Complex.I * ((p * (p - 1) / 2 : ℝ) : ℂ) * ((L ^ (p - 2) : ℝ) : ℂ) * (L' : ℂ) *
        (μ * s * ((L ^ (-(p + 1) / 2) : ℝ) : ℂ))) =
    ((L ^ p : ℝ) : ℂ) * (μ * s * ((L ^ (-(p + 1) / 2) : ℝ) : ℂ) * e) +
      Complex.I * ((p * L ^ (p - 1) * L' / L : ℝ) : ℂ) * (μ * s * ((L ^ (-(p + 1) / 2) : ℝ) : ℂ) * e) -
      Complex.I * p * μ * s' * ((L ^ ((p - 3) / 2) : ℝ) : ℂ) * e := by
  have h1 : L ^ (p - 1) = L ^ (p - 2) * L := by
    rw [← Real.rpow_add_one hL.ne']; ring_nf
  have h2 : L ^ ((p - 3) / 2) = L ^ (p - 1) * L ^ (-(p + 1) / 2) := by
    rw [← Real.rpow_add hL]; ring_nf
  have h3 : L ^ (-(p + 1) / 2 - 1) * L = L ^ (-(p + 1) / 2) := by
    rw [← Real.rpow_add_one hL.ne']; ring_nf
  have h3' : L ^ (-(p + 1) / 2 - 1) = L ^ (-(p + 1) / 2) / L := by
    rw [← h3]; field_simp
  rw [h2, h3', h1]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  push_cast
  field_simp
  ring

/-- Helper for lem:c05_multiplier_fundamental: generic identity part
`e^{iΦ} ℛ̃[χ_Y A, Φ] = |D|^p(χ_Y A e^{iΦ}) - [L^p Z + i(pL^{p-1}L'/L)Z - ipμ s' L^{(p-3)/2}e^{iΦ}]`
near a point where `χ_Y ≡ 1`, `Φ' = L`, `A = μ s L^{-(p+1)/2}`. -/
theorem c05_aux_mf_id_generic (p Y : ℝ) (μ : ℂ) (Φ L : ℝ → ℝ) (s : ℝ → ℂ) {y L' : ℝ} {s' : ℂ}
    (hΦ : ∀ᶠ t in nhds y, HasDerivAt Φ (L t) t) (hL : HasDerivAt L L' y) (hL0 : 0 < L y)
    (hs : HasDerivAt s s' y) (hχ : ∀ᶠ t in nhds y, res_chiY Y t = 1) :
    Complex.exp (Complex.I * (Φ y : ℂ)) *
        c05_multiplier_fundamental_Rtilde p
          (fun z => (res_chiY Y z : ℂ) * (μ * s z * ((L z ^ (-(p + 1) / 2) : ℝ) : ℂ))) Φ y =
      fracDC p (fun z => (res_chiY Y z : ℂ) * (μ * s z * ((L z ^ (-(p + 1) / 2) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (Φ z : ℂ))) y -
        (((L y ^ p : ℝ) : ℂ) * (μ * s y * ((L y ^ (-(p + 1) / 2) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (Φ y : ℂ))) +
          Complex.I * ((p * L y ^ (p - 1) * L' / L y : ℝ) : ℂ) *
            (μ * s y * ((L y ^ (-(p + 1) / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ y : ℂ))) -
          Complex.I * p * μ * s' * ((L y ^ ((p - 3) / 2) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (Φ y : ℂ))) := by
  have hdΦ : deriv Φ =ᶠ[nhds y] L := by
    filter_upwards [hΦ] with t ht using ht.deriv
  have hΦy : deriv Φ y = L y := hdΦ.eq_of_nhds
  have hΦ2 : deriv (deriv Φ) y = L' := by rw [hdΦ.deriv_eq, hL.deriv]
  have hAd : HasDerivAt (fun z => μ * s z * ((L z ^ (-(p + 1) / 2) : ℝ) : ℂ))
      (μ * s' * ((L y ^ (-(p + 1) / 2) : ℝ) : ℂ) +
      μ * s y * ((L' * (-(p + 1) / 2) * L y ^ (-(p + 1) / 2 - 1) : ℝ) : ℂ)) y := by
    have := (hs.const_mul μ).mul ((hL.rpow_const (p := -(p + 1) / 2) (Or.inl hL0.ne')).ofReal_comp)
    convert this using 1
  have haA : (fun z => (res_chiY Y z : ℂ) * (μ * s z * ((L z ^ (-(p + 1) / 2) : ℝ) : ℂ))) =ᶠ[nhds y]
      (fun z => μ * s z * ((L z ^ (-(p + 1) / 2) : ℝ) : ℂ)) := by
    filter_upwards [hχ] with t ht
    rw [ht]; simp
  have ha0 := haA.eq_of_nhds
  have ha1 := haA.deriv_eq
  rw [hAd.deriv] at ha1

  unfold c05_multiplier_fundamental_Rtilde
  beta_reduce
  rw [ha0, ha1, hΦy, hΦ2, mul_sub, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]
  rw [c05_aux_mf_alg p (L y) L' hL0 μ (s y) s' (Complex.exp (Complex.I * (Φ y : ℂ)))]

/-- Helper for lem:c05_multiplier_fundamental: the identity part (eqn:approx_E5_multiplier_expansions). -/
theorem c05_aux_mf_identity (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ∀ y ∈ Ioo (Y / 2) (3 * Y),
        c05_auxiliary_remainders_Emult S.p R ε μ Y y =
            Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ y : ℂ)) *
              c05_multiplier_fundamental_Rtilde S.p
                (fun z => (res_chiY Y z : ℂ) * c05_standing_A S.p ε μ z)
                (c05_standing_Phi S.p R ε μ) y ∧
          c05_auxiliary_remainders_Emult0 S.p R μ Y y =
            Complex.exp (Complex.I * (c05_standing_Phi_zero S.p y : ℂ)) *
              c05_multiplier_fundamental_Rtilde S.p
                (fun z => (res_chiY Y z : ℂ) * c05_standing_A_zero S.p μ z)
                (c05_standing_Phi_zero S.p) y := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  refine ⟨Rs, hRs, ?_⟩
  intro ε μ R Y ht y hy
  have hR : 1 ≤ R := hRs.trans ht.2.2.2.1
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith [hy.1]
  have hRy : R ≤ y := by linarith [hy.1]
  have hnhds : Ioo (Y / 2) (3 * Y) ∈ nhds y := Ioo_mem_nhds hy.1 hy.2
  have hχ : ∀ᶠ t in nhds y, res_chiY Y t = 1 := by
    filter_upwards [hnhds] with t ht' using c05_aux_chiY_one hY0 ⟨ht'.1.le, ht'.2.le⟩
  have hpos : ∀ᶠ t in nhds y, 0 < t := Ioi_mem_nhds hy0
  have hs : HasDerivAt (astar S.p) (deriv (astar S.p) y) y :=
    ((c05_aux_astar_smooth S.p hp hp1 hy0 (n := 1)).differentiableAt one_ne_zero).hasDerivAt
  constructor
  · obtain ⟨⟨hl1, -⟩, -⟩ := hs0 ε μ R Y ht y hRy
    have hL0 : 0 < fam_lambda S.p ε μ y := lt_of_lt_of_le (by positivity) hl1
    have hL : HasDerivAt (fam_lambda S.p ε μ) (deriv (fam_lambda S.p ε μ) y) y :=
      ((c05_aux_lambda_smooth S.p ε μ hy0 (n := 1)).differentiableAt one_ne_zero).hasDerivAt
    have hΦ : ∀ᶠ t in nhds y, HasDerivAt (c05_standing_Phi S.p R ε μ) (fam_lambda S.p ε μ t) t := by
      filter_upwards [hpos] with t ht'
      exact (c05_aux_Psi_hasDeriv S.p R ε μ (by linarith) ht').sub_const (π / 4)
    have hg := c05_aux_mf_id_generic S.p Y μ (c05_standing_Phi S.p R ε μ) (fam_lambda S.p ε μ)
      (astar S.p) hΦ hL hL0 hs hχ
    have hlp : deriv (fun t => fam_lambda S.p ε μ t ^ S.p) y =
        deriv (fam_lambda S.p ε μ) y * S.p * fam_lambda S.p ε μ y ^ (S.p - 1) :=
      (hL.rpow_const (p := S.p) (Or.inl hL0.ne')).deriv
    unfold c05_standing_A
    rw [hg]
    unfold c05_auxiliary_remainders_Emult fam_Z c05_standing_Phi
    rw [hlp]
    have hfun : (fun z => (res_chiY Y z : ℂ) * (μ * astar S.p z *
        ((fam_lambda S.p ε μ z ^ (-(S.p + 1) / 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((fam_Psi S.p R ε μ z - π / 4 : ℝ) : ℂ)))) =
        (fun z => (res_chiY Y z : ℂ) * (μ * astar S.p z *
        ((fam_lambda S.p ε μ z ^ (-(S.p + 1) / 2) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((fam_Psi S.p R ε μ z - π / 4 : ℝ) : ℂ))) := by
      funext z; ring
    rw [hfun]
    rw [sub_right_inj]
    push_cast
    ring
  · have hL0 : 0 < lambda0 S.p y := Real.rpow_pos_of_pos hy0 _
    have hL := c05_aux_lambda0_hasDeriv S.p hy0
    have hΦ : ∀ᶠ t in nhds y, HasDerivAt (c05_standing_Phi_zero S.p) (lambda0 S.p t) t := by
      filter_upwards [hpos] with t ht' using c05_aux_Phi0_hasDeriv S.p hp0 ht'
    have hg := c05_aux_mf_id_generic S.p Y μ (c05_standing_Phi_zero S.p) (lambda0 S.p)
      (astar S.p) hΦ hL hL0 hs hχ
    have hLp : lambda0 S.p y ^ S.p = y := by
      unfold lambda0; rw [← Real.rpow_mul hy0.le, one_div_mul_cancel hp0.ne', Real.rpow_one]
    have hLd : S.p * lambda0 S.p y ^ (S.p - 1) * (1 / S.p * y ^ (1 / S.p - 1)) / lambda0 S.p y =
        1 / lambda0 S.p y := by
      congr 1
      unfold lambda0
      rw [← Real.rpow_mul hy0.le]
      have : S.p * y ^ (1 / S.p * (S.p - 1)) * (1 / S.p * y ^ (1 / S.p - 1)) =
          y ^ (1 / S.p * (S.p - 1)) * y ^ (1 / S.p - 1) := by field_simp
      rw [this, ← Real.rpow_add hy0]
      rw [show 1 / S.p * (S.p - 1) + (1 / S.p - 1) = 0 by field_simp; ring, Real.rpow_zero]
    unfold c05_standing_A_zero
    rw [hg, hLp, hLd]
    unfold c05_auxiliary_remainders_Emult0
    have hZ := c05_aux_Zmu0_eq S.p R μ hp0
    unfold c05_standing_A_zero at hZ
    have hfun : (fun z => (res_chiY Y z : ℂ) * c05_standing_Zmu0 S.p R μ z) =
        (fun z => (res_chiY Y z : ℂ) * (μ * astar S.p z *
        ((lambda0 S.p z ^ (-(S.p + 1) / 2) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (c05_standing_Phi_zero S.p z : ℂ))) := by
      funext z; rw [hZ]; ring
    rw [hfun, hZ]
    rw [sub_right_inj]
    push_cast
    ring


/-- Helper for lem:c05_multiplier_fundamental: `‖α₁β₁ - α₀β₀‖ ≤ |α₁|‖β₁-β₀‖ + |α₁-α₀|‖β₀‖`. -/
theorem c05_aux_mf_prod (α₁ α₀ : ℝ) (β₁ β₀ : ℂ) :
    ‖(α₁ : ℂ) * β₁ - (α₀ : ℂ) * β₀‖ ≤ |α₁| * ‖β₁ - β₀‖ + |α₁ - α₀| * ‖β₀‖ := by
  calc ‖(α₁ : ℂ) * β₁ - (α₀ : ℂ) * β₀‖ = ‖(α₁ : ℂ) * (β₁ - β₀) + ((α₁ - α₀ : ℝ) : ℂ) * β₀‖ := by
        push_cast; ring_nf
    _ ≤ ‖(α₁ : ℂ) * (β₁ - β₀)‖ + ‖((α₁ - α₀ : ℝ) : ℂ) * β₀‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]; rfl

/-- Helper for lem:c05_multiplier_fundamental: the correction term `λ^{q} a''` (`q = p-2 ≤ 0`)
and its derivative have differences of size `δ A Y^{-2-j} Λ^q` (pointwise data, `u = Y⁻¹`). -/
theorem c05_aux_mf_Qdiff (q c K : ℝ) (hq : q ≤ 0) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Λ u δ A x₁ x₀ d₁ d₀ : ℝ) (b₁ b₀ e₁ e₀ : ℂ), 1 ≤ Λ → 0 ≤ u → u ≤ 1 →
      0 ≤ δ → 0 ≤ A → c * Λ ≤ x₁ → c * Λ ≤ x₀ → |d₁| ≤ K * Λ * u → |d₀| ≤ K * Λ * u →
      |x₁ - x₀| ≤ K * δ * u → |d₁ - d₀| ≤ K * δ * u ^ 2 →
      ‖b₀‖ ≤ K * A * u ^ 2 → ‖e₀‖ ≤ K * A * u ^ 3 →
      ‖b₁ - b₀‖ ≤ K * δ * A * u ^ 2 → ‖e₁ - e₀‖ ≤ K * δ * A * u ^ 3 →
      ‖((x₁ ^ q : ℝ) : ℂ) * b₁ - ((x₀ ^ q : ℝ) : ℂ) * b₀‖ ≤ M * δ * A * u ^ 2 * Λ ^ q ∧
      ‖(((q * x₁ ^ (q - 1) * d₁ : ℝ) : ℂ) * b₁ + ((x₁ ^ q : ℝ) : ℂ) * e₁) -
          (((q * x₀ ^ (q - 1) * d₀ : ℝ) : ℂ) * b₀ + ((x₀ ^ q : ℝ) : ℂ) * e₀)‖ ≤
        M * δ * A * u ^ 3 * Λ ^ q := by
  set M1 : ℝ := c ^ q * K + |q| * c ^ (q - 1) * K * K with hM1
  set M2' : ℝ := c ^ (q - 1) * K * K + (|q - 1| * c ^ (q - 2) * K * K + c ^ (q - 1) * K) * K
    with hM2'
  set M2 : ℝ := |q| * M2' with hM2
  have hM10 : 0 ≤ M1 := by positivity
  have hM20 : 0 ≤ M2 := by positivity
  refine ⟨M1 + M2, by positivity, ?_⟩
  intro Λ u δ A x₁ x₀ d₁ d₀ b₁ b₀ e₁ e₀ hΛ hu0 hu1 hδ hA hx₁ hx₀ hd₁ hd₀ hx hd hb₀ he₀ hb he
  have hΛ0 : 0 < Λ := by linarith
  have hcΛ : 0 < c * Λ := by positivity
  have hx₁0 : 0 < x₁ := by linarith
  have hx₀0 : 0 < x₀ := by linarith
  set P := Λ ^ q with hP
  set P' := Λ ^ (q - 1) with hP'
  have hP0 : 0 < P := Real.rpow_pos_of_pos hΛ0 _
  have hP'0 : 0 < P' := Real.rpow_pos_of_pos hΛ0 _
  have hPP' : P' * Λ = P := by rw [hP', hP, ← Real.rpow_add_one hΛ0.ne']; ring_nf
  have hP'P : P' ≤ P := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
  have hcq : ∀ r : ℝ, r ≤ 0 → ∀ x : ℝ, c * Λ ≤ x → x ^ r ≤ c ^ r * Λ ^ r := fun r hr x hx' => by
    rw [← Real.mul_rpow hc.le hΛ0.le]; exact Real.rpow_le_rpow_of_nonpos hcΛ hx' hr
  -- basic power bounds
  have f1 : ∀ x, c * Λ ≤ x → |x ^ q| ≤ c ^ q * P := fun x hx' => by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]; exact hcq q hq x hx'
  have f2 : ∀ x, c * Λ ≤ x → |x ^ (q - 1)| ≤ c ^ (q - 1) * P' := fun x hx' => by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]; exact hcq (q - 1) (by linarith) x hx'
  have f3 : |x₁ ^ q - x₀ ^ q| ≤ |q| * c ^ (q - 1) * P * (K * δ * u) := by
    refine (c05_aux_rpow_sub_le hcΛ hx₁ hx₀ (by linarith)).trans ?_
    rw [Real.mul_rpow hc.le hΛ0.le]
    have : Λ ^ (q - 1) ≤ P := hP'P
    calc |q| * (c ^ (q - 1) * Λ ^ (q - 1)) * |x₁ - x₀| ≤ |q| * (c ^ (q - 1) * P) * (K * δ * u) := by
          gcongr
      _ = _ := by ring
  have f4 : |x₁ ^ (q - 1) - x₀ ^ (q - 1)| ≤ |q - 1| * c ^ (q - 2) * P' * (K * δ * u) := by
    refine (c05_aux_rpow_sub_le hcΛ hx₁ hx₀ (by linarith)).trans ?_
    rw [Real.mul_rpow hc.le hΛ0.le, show q - 1 - 1 = q - 2 by ring]
    have : Λ ^ (q - 2) ≤ P' := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
    calc |q - 1| * (c ^ (q - 2) * Λ ^ (q - 2)) * |x₁ - x₀| ≤ |q - 1| * (c ^ (q - 2) * P') * (K * δ * u) := by
          gcongr
      _ = _ := by ring
  have hu2 : u ^ 3 ≤ u ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have hu4 : u ^ 4 ≤ u ^ 3 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  -- the generic value bound
  have hval : ∀ (β₁ β₀ : ℂ) (n : ℕ), ‖β₀‖ ≤ K * A * u ^ n → ‖β₁ - β₀‖ ≤ K * δ * A * u ^ n →
      ‖((x₁ ^ q : ℝ) : ℂ) * β₁ - ((x₀ ^ q : ℝ) : ℂ) * β₀‖ ≤ M1 * δ * A * u ^ n * P := by
    intro β₁ β₀ n h0 h1
    refine (c05_aux_mf_prod _ _ β₁ β₀).trans ?_
    have hun : u * u ^ n ≤ u ^ n := by
      calc u * u ^ n ≤ 1 * u ^ n := by gcongr
        _ = u ^ n := one_mul _
    calc |x₁ ^ q| * ‖β₁ - β₀‖ + |x₁ ^ q - x₀ ^ q| * ‖β₀‖
        ≤ (c ^ q * P) * (K * δ * A * u ^ n) +
          (|q| * c ^ (q - 1) * P * (K * δ * u)) * (K * A * u ^ n) := by
          gcongr
          exact f1 x₁ hx₁
      _ = c ^ q * K * δ * A * u ^ n * P + |q| * c ^ (q - 1) * K * K * δ * A * (u * u ^ n) * P := by
          ring
      _ ≤ c ^ q * K * δ * A * u ^ n * P + |q| * c ^ (q - 1) * K * K * δ * A * u ^ n * P := by
          have : 0 ≤ |q| * c ^ (q - 1) * K * K * δ * A := by positivity
          have := mul_le_mul_of_nonneg_left hun this
          nlinarith
      _ = M1 * δ * A * u ^ n * P := by rw [hM1]; ring
  refine ⟨?_, ?_⟩
  · have := hval b₁ b₀ 2 hb₀ hb
    calc _ ≤ M1 * δ * A * u ^ 2 * P := this
      _ ≤ (M1 + M2) * δ * A * u ^ 2 * P := by gcongr; linarith
  · -- derivative
    set α₁ := x₁ ^ (q - 1) * d₁ with hα₁
    set α₀ := x₀ ^ (q - 1) * d₀ with hα₀
    have hα₁b : |α₁| ≤ c ^ (q - 1) * K * P * u := by
      rw [hα₁, abs_mul]
      calc |x₁ ^ (q - 1)| * |d₁| ≤ (c ^ (q - 1) * P') * (K * Λ * u) := by
            gcongr
            exact f2 x₁ hx₁
        _ = c ^ (q - 1) * K * (P' * Λ) * u := by ring
        _ = _ := by rw [hPP']
    have hαd : |α₁ - α₀| ≤ (|q - 1| * c ^ (q - 2) * K * K + c ^ (q - 1) * K) * δ * P * u ^ 2 := by
      have e : α₁ - α₀ = (x₁ ^ (q - 1) - x₀ ^ (q - 1)) * d₁ + x₀ ^ (q - 1) * (d₁ - d₀) := by
        rw [hα₁, hα₀]; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |x₁ ^ (q - 1) - x₀ ^ (q - 1)| * |d₁| + |x₀ ^ (q - 1)| * |d₁ - d₀|
          ≤ (|q - 1| * c ^ (q - 2) * P' * (K * δ * u)) * (K * Λ * u) +
            (c ^ (q - 1) * P') * (K * δ * u ^ 2) := by
            gcongr
            exact f2 x₀ hx₀
        _ = |q - 1| * c ^ (q - 2) * K * K * δ * (P' * Λ) * u ^ 2 +
            c ^ (q - 1) * K * δ * P' * u ^ 2 := by ring
        _ ≤ |q - 1| * c ^ (q - 2) * K * K * δ * P * u ^ 2 + c ^ (q - 1) * K * δ * P * u ^ 2 := by
            rw [hPP']; gcongr
        _ = _ := by ring
    have hpart1 : ‖(α₁ : ℂ) * b₁ - (α₀ : ℂ) * b₀‖ ≤ M2' * δ * A * u ^ 3 * P := by
      refine (c05_aux_mf_prod _ _ b₁ b₀).trans ?_
      calc |α₁| * ‖b₁ - b₀‖ + |α₁ - α₀| * ‖b₀‖
          ≤ (c ^ (q - 1) * K * P * u) * (K * δ * A * u ^ 2) +
            ((|q - 1| * c ^ (q - 2) * K * K + c ^ (q - 1) * K) * δ * P * u ^ 2) * (K * A * u ^ 2) := by
            gcongr
        _ = c ^ (q - 1) * K * K * δ * A * u ^ 3 * P +
            (|q - 1| * c ^ (q - 2) * K * K + c ^ (q - 1) * K) * K * δ * A * u ^ 4 * P := by ring
        _ ≤ c ^ (q - 1) * K * K * δ * A * u ^ 3 * P +
            (|q - 1| * c ^ (q - 2) * K * K + c ^ (q - 1) * K) * K * δ * A * u ^ 3 * P := by gcongr
        _ = M2' * δ * A * u ^ 3 * P := by rw [hM2']; ring
    have hpart2 := hval e₁ e₀ 3 he₀ he
    have e : (((q * x₁ ^ (q - 1) * d₁ : ℝ) : ℂ) * b₁ + ((x₁ ^ q : ℝ) : ℂ) * e₁) -
        (((q * x₀ ^ (q - 1) * d₀ : ℝ) : ℂ) * b₀ + ((x₀ ^ q : ℝ) : ℂ) * e₀) =
        (q : ℂ) * ((α₁ : ℂ) * b₁ - (α₀ : ℂ) * b₀) +
          (((x₁ ^ q : ℝ) : ℂ) * e₁ - ((x₀ ^ q : ℝ) : ℂ) * e₀) := by
      rw [hα₁, hα₀]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |q| * ‖(α₁ : ℂ) * b₁ - (α₀ : ℂ) * b₀‖ + ‖((x₁ ^ q : ℝ) : ℂ) * e₁ - ((x₀ ^ q : ℝ) : ℂ) * e₀‖
        ≤ |q| * (M2' * δ * A * u ^ 3 * P) + M1 * δ * A * u ^ 3 * P := by gcongr
      _ = (M1 + M2) * δ * A * u ^ 3 * P := by rw [hM2]; ring

/-- Helper for lem:c05_multiplier_fundamental: `ℛ̃[a,Ψ]` is differentiable at `y` when
`|D|^p(ae^{iΨ})` is and `a`, `Ψ` are `C³` (near `y`), `Ψ'(y) > 0`. -/
theorem c05_aux_mf_Rt_diff (p : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U) {y : ℝ}
    (hy : y ∈ U) (ha : ContDiff ℝ 3 a) (hΨ : ContDiffOn ℝ 3 Ψ U) (hl : 0 < deriv Ψ y)
    (hf : DifferentiableAt ℝ (fracDC p (fun z => a z * Complex.exp (Complex.I * (Ψ z : ℂ)))) y) :
    DifferentiableAt ℝ (c05_multiplier_fundamental_Rtilde p a Ψ) y := by
  have hΨ1 := hΨ.deriv_of_isOpen hU (m := 2) (by norm_num)
  have hΨ2 := hΨ1.deriv_of_isOpen hU (m := 1) (by norm_num)
  have dΨ : DifferentiableAt ℝ Ψ y := (hΨ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have dΨ1 : DifferentiableAt ℝ (deriv Ψ) y :=
    (hΨ1.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have dΨ2 : DifferentiableAt ℝ (deriv (deriv Ψ)) y :=
    (hΨ2.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have da : DifferentiableAt ℝ a y := (ha.differentiable (by norm_num)) y
  have da1 : DifferentiableAt ℝ (deriv a) y := ((ha.iterate_deriv' 2 1).differentiable (by norm_num)) y
  have hne : deriv Ψ y ≠ 0 := hl.ne'
  unfold c05_multiplier_fundamental_Rtilde
  have r1 : DifferentiableAt ℝ (fun t => ((deriv Ψ t ^ p : ℝ) : ℂ)) y :=
    c05_aux_ofReal_diff (dΨ1.rpow_const (Or.inl hne))
  have r2 : DifferentiableAt ℝ (fun t => ((deriv Ψ t ^ (p - 1) : ℝ) : ℂ)) y :=
    c05_aux_ofReal_diff (dΨ1.rpow_const (Or.inl hne))
  have r3 : DifferentiableAt ℝ (fun t => ((deriv Ψ t ^ (p - 2) : ℝ) : ℂ)) y :=
    c05_aux_ofReal_diff (dΨ1.rpow_const (Or.inl hne))
  have r4 : DifferentiableAt ℝ (fun t => ((deriv (deriv Ψ) t : ℝ) : ℂ)) y := c05_aux_ofReal_diff dΨ2
  have r5 : DifferentiableAt ℝ (fun t => Complex.exp (-(Complex.I * (Ψ t : ℂ)))) y :=
    (((c05_aux_ofReal_diff dΨ).const_mul Complex.I).neg).cexp
  exact (r5.mul hf).sub (((r1.mul da).sub (((differentiableAt_const _).mul r2).mul da1)).sub
    ((((differentiableAt_const _).mul r3).mul r4).mul da))

/-- Helper for lem:c05_multiplier_fundamental: Leibniz bookkeeping for
`G = uW + (u-v)T₀` and `G' = u'W + uW' + (u'-v')T₀ + (u-v)T₀'`. -/
theorem c05_aux_mf_combine {u0 u1 v0 v1 W0 W1 T0 T1 : ℂ} {K Λ δ X w : ℝ} (hK : 0 ≤ K)
    (hΛ : 1 ≤ Λ) (hw : w ≤ 1) (hδ : 0 ≤ δ) (hX : 0 ≤ X)
    (hu0 : ‖u0‖ = 1) (hu1 : ‖u1‖ ≤ K * Λ) (huv0 : ‖u0 - v0‖ ≤ K * δ) (huv1 : ‖u1 - v1‖ ≤ K * δ * Λ)
    (hW0 : ‖W0‖ ≤ K * δ * X) (hW1 : ‖W1‖ ≤ K * δ * X * w) (hT0 : ‖T0‖ ≤ K * X)
    (hT1 : ‖T1‖ ≤ K * X * w) :
    ‖u0 * W0 + (u0 - v0) * T0‖ ≤ 4 * (K * K + K) * δ * X ∧
      ‖u1 * W0 + u0 * W1 + ((u1 - v1) * T0 + (u0 - v0) * T1)‖ ≤ 4 * (K * K + K) * δ * X * Λ := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hwΛ : w ≤ Λ := hw.trans hΛ
  constructor
  · calc ‖u0 * W0 + (u0 - v0) * T0‖ ≤ ‖u0‖ * ‖W0‖ + ‖u0 - v0‖ * ‖T0‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ 1 * (K * δ * X) + (K * δ) * (K * X) := by rw [hu0]; gcongr
      _ = (K * K + K) * δ * X := by ring
      _ ≤ 4 * (K * K + K) * δ * X := by
          have : 0 ≤ (K * K + K) * δ * X := by positivity
          linarith
  · calc ‖u1 * W0 + u0 * W1 + ((u1 - v1) * T0 + (u0 - v0) * T1)‖
        ≤ ‖u1‖ * ‖W0‖ + ‖u0‖ * ‖W1‖ + (‖u1 - v1‖ * ‖T0‖ + ‖u0 - v0‖ * ‖T1‖) := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_)
            ((norm_add_le _ _).trans ?_)) <;> rw [norm_mul, norm_mul]
      _ ≤ (K * Λ) * (K * δ * X) + 1 * (K * δ * X * w) + ((K * δ * Λ) * (K * X) +
          (K * δ) * (K * X * w)) := by rw [hu0]; gcongr
      _ ≤ (K * Λ) * (K * δ * X) + 1 * (K * δ * X * Λ) + ((K * δ * Λ) * (K * X) +
          (K * δ) * (K * X * Λ)) := by gcongr
      _ = 3 * (K * K) * δ * X * Λ + K * δ * X * Λ := by ring
      _ ≤ 4 * (K * K + K) * δ * X * Λ := by
          have : 0 ≤ K * K * δ * X * Λ := by positivity
          have : 0 ≤ K * δ * X * Λ := by positivity
          nlinarith

/-- Helper: `Y^{-k} = (Y⁻¹)^k`. -/
theorem c05_aux_mf_Yk {Y : ℝ} (hY : 0 < Y) (k : ℕ) : Y ^ (-(k : ℝ)) = Y⁻¹ ^ k := by
  rw [Real.rpow_neg hY.le, Real.rpow_natCast, inv_pow]

/-- Helper: `iteratedDeriv 2 f = f''`, `iteratedDeriv 3 f = f'''`. -/
theorem c05_aux_mf_iter23 (f : ℝ → ℂ) (x : ℝ) :
    iteratedDeriv 2 f x = deriv (deriv f) x ∧ iteratedDeriv 3 f x = deriv (deriv (deriv f)) x := by
  constructor
  · rw [iteratedDeriv_succ, iteratedDeriv_one]
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]

/-- Helper: `iteratedDeriv 2 f = f''` (real). -/
theorem c05_aux_mf_iter2r (f : ℝ → ℝ) (x : ℝ) : iteratedDeriv 2 f x = deriv (deriv f) x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

set_option maxHeartbeats 800000 in
/-- Helper for lem:c05_multiplier_fundamental: bounds for `T₀ = ℛ̃_{mult,2}[a₀,Φ₀]` and
`W = ℛ̃_{mult,2}[a₁,Φ] - ℛ̃_{mult,2}[a₀,Φ₀]` (appendix two-term bound, appendix difference bound with
`N = 2`, and the explicit `λ^{p-2}a''` correction). Here `X = Y^{-β}Y^{-2}Λ^{p-2}`. -/
theorem c05_aux_mf_WT (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y → ∀ y ∈ Icc Y (2 * Y),
        let Λ := Y ^ (1 / S.p)
        let δ := ε * Y ^ (1 / S.p - S.p)
        let X := Y ^ (-beta S.p) * Y⁻¹ ^ 2 * Λ ^ (S.p - 2)
        let a₁ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A S.p ε μ z
        let a₀ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A_zero S.p μ z
        let T : ℝ → ℂ := c03_mult_R2tilde S.p Y a₀ (c05_standing_Phi_zero S.p)
        let W : ℝ → ℂ := fun t => c03_mult_R2tilde S.p Y a₁ (c05_standing_Phi S.p R ε μ) t -
          c03_mult_R2tilde S.p Y a₀ (c05_standing_Phi_zero S.p) t
        DifferentiableAt ℝ W y ∧ DifferentiableAt ℝ T y ∧
          ‖W y‖ ≤ K * δ * X ∧ ‖deriv W y‖ ≤ K * δ * X * Y⁻¹ ∧
          ‖T y‖ ≤ K * X ∧ ‖deriv T y‖ ≤ K * X * Y⁻¹ := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  obtain ⟨Rh, hRh, cs, hcs, hyp⟩ := c05_multiplier_hypotheses S
  choose Ck hCk hCkb using hyp
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  obtain ⟨-, H2, H3⟩ := appendix_oscillatory_multiplier S.p hp0 hp1 cs⁻¹ (inv_pos.mpr hcs)
  obtain ⟨k20, hk20⟩ := H2 0 (Nat.zero_le 1)
  obtain ⟨k21, hk21⟩ := H2 1 le_rfl
  obtain ⟨k30, hk30⟩ := H3 2 (by norm_num) 0
  obtain ⟨k31, hk31⟩ := H3 2 (by norm_num) 1
  obtain ⟨C20, hC20, HC20⟩ := hk20 Ck
  obtain ⟨C21, hC21, HC21⟩ := hk21 Ck
  obtain ⟨C30, hC30, HC30⟩ := hk30 Ck
  obtain ⟨C31, hC31, HC31⟩ := hk31 Ck
  set K₁ : ℝ := Ck 1 + Ck 2 + Ck 3 with hK₁
  have hK₁0 : 0 ≤ K₁ := by have := hCk 1; have := hCk 2; have := hCk 3; positivity
  have hK1 : Ck 1 ≤ K₁ := by have := hCk 2; have := hCk 3; linarith
  have hK2 : Ck 2 ≤ K₁ := by have := hCk 1; have := hCk 3; linarith
  have hK3 : Ck 3 ≤ K₁ := by have := hCk 1; have := hCk 2; linarith
  obtain ⟨MQ, hMQ, HQ⟩ := c05_aux_mf_Qdiff (S.p - 2) cs K₁ (by linarith) hcs hK₁0
  refine ⟨max Rh Rs, hRh.trans (le_max_left _ _), C20 + C21 + C30 + C31 + MQ, by positivity, ?_⟩
  intro ε μ R Y ht y hy Λ δ X a₁ a₀ T W
  have htH := c05_aux_tuple_mono (le_max_left Rh Rs) ht
  have htS := c05_aux_tuple_mono (le_max_right Rh Rs) ht
  have hR : 1 ≤ R := hRh.trans htH.2.2.2.1
  have hY8 : 8 * R ≤ Y := ht.2.2.2.2
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hRY : R < 3 * Y / 10 := by linarith
  have hε0 : 0 ≤ ε := ht.1
  set A := Y ^ (-beta S.p) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos hY0 _
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow hY1 (by positivity)
  have hδ0 : 0 ≤ δ := by positivity
  set u : ℝ := Y⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := inv_le_one_of_one_le₀ hY1
  set Φ := c05_standing_Phi S.p R ε μ with hΦ
  set Φ₀ := c05_standing_Phi_zero S.p with hΦ₀
  set IY := Ioo (Y / 4) (4 * Y) with hIY
  have hyI : y ∈ IY := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hIYn : IY ∈ nhds y := Ioo_mem_nhds hyI.1 hyI.2
  have hH := fun k => hCkb k ε μ R Y htH
  obtain ⟨⟨ha₁s, ha₀s, -, -, -, -, hΦs, hΦ₀s⟩, -⟩ := hH 0
  -- appendix hypotheses
  have hYk : ∀ k : ℕ, Y ^ (-beta S.p - k) = A * Y ^ (-(k : ℝ)) := fun k => by
    rw [hA, ← Real.rpow_add hY0]; ring_nf
  have hhyp1 : ∀ k₀ : ℕ, c03_mult_hyp Y Λ A cs⁻¹ Ck k₀ a₁ Φ := by
    intro k₀
    refine ⟨ha₁s, (hH 0).1.2.2.2.1, hΦs, fun x hx => ?_⟩
    obtain ⟨⟨h1, h2, -⟩, -⟩ := (hH 0).2 x hx
    refine ⟨by rw [inv_inv]; exact h1, h2, fun k _ => ?_⟩
    obtain ⟨⟨-, -, -, -, h5, -, h7, -⟩, -⟩ := (hH k).2 x hx
    refine ⟨h5, ?_⟩
    calc _ ≤ Ck k * Y ^ (-beta S.p - k) := h7
      _ = _ := by rw [hYk]; ring
  have hhyp0 : ∀ k₀ : ℕ, c03_mult_hyp Y Λ A cs⁻¹ Ck k₀ a₀ Φ₀ := by
    intro k₀
    refine ⟨ha₀s, (hH 0).1.2.2.2.2.1, hΦ₀s, fun x hx => ?_⟩
    obtain ⟨⟨-, -, h3, h4, -⟩, -⟩ := (hH 0).2 x hx
    refine ⟨by rw [inv_inv]; exact h3, h4, fun k _ => ?_⟩
    obtain ⟨⟨-, -, -, -, -, h6, -, h8⟩, -⟩ := (hH k).2 x hx
    refine ⟨h6, ?_⟩
    calc _ ≤ Ck k * Y ^ (-beta S.p - k) := h8
      _ = _ := by rw [hYk]; ring
  have hdh : ∀ k₀ : ℕ, ∀ x ∈ IY, ∀ k ≤ k₀,
      ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
      |iteratedDeriv k (fun x => Φ x - Φ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ)) := by
    intro k₀ x hx k _
    obtain ⟨-, ⟨h1, h2⟩, -⟩ := (hH k).2 x hx
    exact ⟨by calc _ ≤ _ := h1
                _ = _ := by ring, h2⟩
  have hT0 := (HC20 Y Λ A a₀ Φ₀ hY1 hΛ1 hA0 (hhyp0 k20) y hy).2
  have hT1 := (HC21 Y Λ A a₀ Φ₀ hY1 hΛ1 hA0 (hhyp0 k21) y hy).2
  have hD0 := HC30 Y Λ A δ a₀ a₁ Φ₀ Φ hY1 hΛ1 hA0 hδ0 (hhyp0 k30) (hhyp1 k30) (hdh k30) y hy
  have hD1 := HC31 Y Λ A δ a₀ a₁ Φ₀ Φ hY1 hΛ1 hA0 hδ0 (hhyp0 k31) (hhyp1 k31) (hdh k31) y hy
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, iteratedDeriv_zero, iteratedDeriv_one,
    sub_zero, add_zero] at hT0 hT1 hD0 hD1
  have hY2 : Y ^ (-2 : ℝ) = u ^ 2 := by
    have := c05_aux_mf_Yk hY0 2; rw [hu, ← this]; norm_num
  have hY3 : Y ^ (-2 - 1 : ℝ) = u ^ 3 := by
    have := c05_aux_mf_Yk hY0 3; rw [hu, ← this]; norm_num
  have hY3' : Y ^ (-(2 + 1) : ℝ) = u ^ 3 := by
    have := c05_aux_mf_Yk hY0 3; rw [hu, ← this]; norm_num
  rw [hY2] at hT0 hD0
  rw [hY3] at hT1
  rw [hY3'] at hD1
  -- pointwise data for the  correction
  have hΦc : ContDiffAt ℝ 3 Φ y := (hΦs.contDiffAt hIYn).of_le (WithTop.coe_le_coe.mpr le_top)
  have hΦ₀c : ContDiffAt ℝ 3 Φ₀ y := (hΦ₀s.contDiffAt hIYn).of_le (WithTop.coe_le_coe.mpr le_top)
  have ha₁c : ContDiffAt ℝ 3 a₁ y := (ha₁s.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have ha₀c : ContDiffAt ℝ 3 a₀ y := (ha₀s.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨⟨hx₁, -, hx₀, -⟩, -⟩ := (hH 0).2 y hyI
  obtain ⟨⟨-, -, -, -, hd₁, hd₀, -⟩, -⟩ := (hH 1).2 y hyI
  obtain ⟨-, ⟨-, hx⟩, -⟩ := (hH 1).2 y hyI
  obtain ⟨⟨-, -, -, -, -, -, -, hb₀⟩, ⟨hb, hd⟩, -⟩ := (hH 2).2 y hyI
  obtain ⟨⟨-, -, -, -, -, -, -, he₀⟩, ⟨he, -⟩, -⟩ := (hH 3).2 y hyI
  rw [iteratedDeriv_one] at hd₁ hd₀
  rw [iteratedDeriv_fun_sub (hΦc.of_le (by norm_num)) (hΦ₀c.of_le (by norm_num)),
    iteratedDeriv_one, iteratedDeriv_one] at hx
  rw [iteratedDeriv_fun_sub (hΦc.of_le (by norm_num)) (hΦ₀c.of_le (by norm_num)),
    c05_aux_mf_iter2r, c05_aux_mf_iter2r] at hd
  rw [iteratedDeriv_fun_sub (ha₁c.of_le (by norm_num)) (ha₀c.of_le (by norm_num)),
    (c05_aux_mf_iter23 a₁ y).1, (c05_aux_mf_iter23 a₀ y).1] at hb
  rw [iteratedDeriv_fun_sub ha₁c ha₀c,
    (c05_aux_mf_iter23 a₁ y).2, (c05_aux_mf_iter23 a₀ y).2] at he
  rw [(c05_aux_mf_iter23 a₀ y).1] at hb₀
  rw [(c05_aux_mf_iter23 a₀ y).2] at he₀
  rw [hYk, c05_aux_mf_Yk hY0] at hb₀ he₀
  rw [c05_aux_mf_Yk hY0] at hd₁ hd₀ hx hd hb he
  have hQ := HQ Λ u δ A (deriv Φ y) (deriv Φ₀ y) (deriv (deriv Φ) y) (deriv (deriv Φ₀) y)
    (deriv (deriv a₁) y) (deriv (deriv a₀) y) (deriv (deriv (deriv a₁)) y)
    (deriv (deriv (deriv a₀)) y) hΛ1 hu0 hu1 hδ0 hA0.le hx₁ hx₀
    (hd₁.trans (by rw [pow_one]; gcongr)) (hd₀.trans (by rw [pow_one]; gcongr)) (hx.trans (by rw [pow_one]; gcongr))
    (hd.trans (by gcongr)) (hb₀.trans (by rw [mul_assoc]; gcongr)) (he₀.trans (by rw [mul_assoc]; gcongr))
    (hb.trans (by gcongr)) (he.trans (by gcongr))
  -- derivatives of the corrections `Q_ν = λ_ν^{p-2} a_ν''`
  have hl₁ : 0 < deriv Φ y := lt_of_lt_of_le (by positivity) hx₁
  have hl₀ : 0 < deriv Φ₀ y := lt_of_lt_of_le (by positivity) hx₀
  have hQd : ∀ (Ψ : ℝ → ℝ) (a : ℝ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) Ψ IY → ContDiff ℝ (⊤ : ℕ∞) a →
      0 < deriv Ψ y →
      HasDerivAt (fun t => ((deriv Ψ t ^ (S.p - 2) : ℝ) : ℂ) * deriv (deriv a) t)
        (((S.p - 2) * deriv Ψ y ^ (S.p - 2 - 1) * deriv (deriv Ψ) y : ℝ) * deriv (deriv a) y +
          ((deriv Ψ y ^ (S.p - 2) : ℝ) : ℂ) * deriv (deriv (deriv a)) y) y := by
    intro Ψ a hΨs has hl
    have hΨ1 := hΨs.deriv_of_isOpen isOpen_Ioo (m := 1) (by simp)
    have h1 : HasDerivAt (deriv Ψ) (deriv (deriv Ψ) y) y :=
      ((hΨ1.contDiffAt hIYn).differentiableAt (by norm_num)).hasDerivAt
    have h2 := (h1.rpow_const (p := S.p - 2) (Or.inl hl.ne')).ofReal_comp
    have h3 : HasDerivAt (deriv (deriv a)) (deriv (deriv (deriv a)) y) y :=
      ((((has.of_le (WithTop.coe_le_coe.mpr le_top)).iterate_deriv' 1 2).differentiable (by simp)) y).hasDerivAt
    convert h2.mul h3 using 1
    push_cast; ring
  have hQ₁ := hQd Φ a₁ hΦs ha₁s hl₁
  have hQ₀ := hQd Φ₀ a₀ hΦ₀s ha₀s hl₀
  set κ : ℝ := S.p * (S.p - 1) / 2 with hκ
  have hκ1 : |κ| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  -- `ℛ̃ = ℛ̃_{mult,2}` near `y` and differentiability
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have := (hs0 ε μ R Y htS t ht'.le).1.1
    have : 0 < t ^ (1 / S.p) / 2 := by
      have : 0 < t := by linarith
      positivity
    linarith
  have hf₁ : DifferentiableAt ℝ (fracDC S.p (fun z => a₁ z * Complex.exp (Complex.I * (Φ z : ℂ)))) y := by
    have e : (fun z => a₁ z * Complex.exp (Complex.I * (Φ z : ℂ))) =
        fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z := by
      funext z; simp only [a₁, hΦ, fam_Z, c05_standing_A, c05_standing_Phi]; ring
    rw [e]
    exact (c05_aux_fracDC_cutoff S.p hp hp1 hY0 hRY (fun t ht' =>
      (c05_aux_family_smooth S.p R ε μ hp hp1 (by linarith) hpos ht').2.1)).differentiable
      one_ne_zero y
  have hf₀ : DifferentiableAt ℝ (fracDC S.p (fun z => a₀ z * Complex.exp (Complex.I * (Φ₀ z : ℂ)))) y := by
    have e : (fun z => a₀ z * Complex.exp (Complex.I * (Φ₀ z : ℂ))) =
        fun z => (res_chiY Y z : ℂ) * c05_standing_Zmu0 S.p R μ z := by
      funext z; rw [c05_aux_Zmu0_eq S.p R μ hp0]; simp only [a₀, hΦ₀]; ring
    rw [e]
    exact (c05_aux_fracDC_cutoff S.p hp hp1 hY0 hRY (fun t ht' =>
      (c05_aux_family_smooth S.p R ε μ hp hp1 (by linarith) hpos ht').2.2.1)).differentiable
      one_ne_zero y
  have dR₁ := c05_aux_mf_Rt_diff S.p a₁ Φ isOpen_Ioo hyI (ha₁s.of_le (WithTop.coe_le_coe.mpr le_top))
    (hΦs.of_le (WithTop.coe_le_coe.mpr le_top)) hl₁ hf₁
  have dR₀ := c05_aux_mf_Rt_diff S.p a₀ Φ₀ isOpen_Ioo hyI (ha₀s.of_le (WithTop.coe_le_coe.mpr le_top))
    (hΦ₀s.of_le (WithTop.coe_le_coe.mpr le_top)) hl₀ hf₀
  have hev₁ : c05_multiplier_fundamental_Rtilde S.p a₁ Φ =ᶠ[nhds y] c03_mult_R2tilde S.p Y a₁ Φ := by
    filter_upwards [hIYn] with t ht'
    exact c05_aux_mf_Rtilde_eq S.p Y a₁ Φ (ha₁s.of_le (WithTop.coe_le_coe.mpr le_top))
      (hΦs.of_le (WithTop.coe_le_coe.mpr le_top)) ht'
  have hev₀ : c05_multiplier_fundamental_Rtilde S.p a₀ Φ₀ =ᶠ[nhds y] c03_mult_R2tilde S.p Y a₀ Φ₀ := by
    filter_upwards [hIYn] with t ht'
    exact c05_aux_mf_Rtilde_eq S.p Y a₀ Φ₀ (ha₀s.of_le (WithTop.coe_le_coe.mpr le_top))
      (hΦ₀s.of_le (WithTop.coe_le_coe.mpr le_top)) ht'
  have dT : DifferentiableAt ℝ T y := dR₀.congr_of_eventuallyEq hev₀.symm
  have dW : DifferentiableAt ℝ W y :=
    ((dR₁.congr_of_eventuallyEq hev₁.symm).sub dT)
  -- `W = D - κ(Q₁ - Q₀)`
  set Q₁ : ℝ → ℂ := fun t => ((deriv Φ t ^ (S.p - 2) : ℝ) : ℂ) * deriv (deriv a₁) t with hQ₁def
  set Q₀ : ℝ → ℂ := fun t => ((deriv Φ₀ t ^ (S.p - 2) : ℝ) : ℂ) * deriv (deriv a₀) t with hQ₀def
  have hDW : (fun y' => c03_mult_R S.p Y a₁ Φ 2 y' - c03_mult_R S.p Y a₀ Φ₀ 2 y') =
      fun t => W t + (κ : ℂ) * (Q₁ t - Q₀ t) := by
    funext t
    simp only [W, Q₁, Q₀, c03_mult_R2tilde, hκ]
    push_cast; ring
  have hDd : HasDerivAt (fun t => W t + (κ : ℂ) * (Q₁ t - Q₀ t)) _ y :=
    dW.hasDerivAt.add ((hQ₁.sub hQ₀).const_mul (κ : ℂ))
  rw [← hDW] at hDd
  rw [hDd.deriv] at hD1
  have hWy : W y = (c03_mult_R S.p Y a₁ Φ 2 y - c03_mult_R S.p Y a₀ Φ₀ 2 y) -
      (κ : ℂ) * (Q₁ y - Q₀ y) := by
    have := congrFun hDW y
    rw [this]; ring
  have hmin : min 1 δ ≤ δ := min_le_right _ _
  have hXe : A * u ^ 2 * Λ ^ (S.p - 2) = X := by simp only [X, hA, hu]
  have hκn : ‖(κ : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hκ1
  have hX0 : 0 ≤ X := by positivity
  set K := C20 + C21 + C30 + C31 + MQ with hK
  refine ⟨dW, dT, ?_, ?_, ?_, ?_⟩
  · rw [hWy]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    calc _ ≤ C30 * min 1 δ * A * u ^ 2 * Λ ^ (S.p - 2) + 1 * (MQ * δ * A * u ^ 2 * Λ ^ (S.p - 2)) := by
          gcongr
          exact hQ.1
      _ ≤ C30 * δ * A * u ^ 2 * Λ ^ (S.p - 2) + 1 * (MQ * δ * A * u ^ 2 * Λ ^ (S.p - 2)) := by
          gcongr
      _ = (C30 + MQ) * δ * (A * u ^ 2 * Λ ^ (S.p - 2)) := by ring
      _ ≤ K * δ * X := by
          rw [hXe]; gcongr; linarith
  · have e : deriv W y = (deriv W y + (κ : ℂ) * ((((S.p - 2) * deriv Φ y ^ (S.p - 2 - 1) *
        deriv (deriv Φ) y : ℝ) : ℂ) * deriv (deriv a₁) y + ((deriv Φ y ^ (S.p - 2) : ℝ) : ℂ) *
        deriv (deriv (deriv a₁)) y - ((((S.p - 2) * deriv Φ₀ y ^ (S.p - 2 - 1) *
        deriv (deriv Φ₀) y : ℝ) : ℂ) * deriv (deriv a₀) y + ((deriv Φ₀ y ^ (S.p - 2) : ℝ) : ℂ) *
        deriv (deriv (deriv a₀)) y))) - (κ : ℂ) * ((((S.p - 2) * deriv Φ y ^ (S.p - 2 - 1) *
        deriv (deriv Φ) y : ℝ) : ℂ) * deriv (deriv a₁) y + ((deriv Φ y ^ (S.p - 2) : ℝ) : ℂ) *
        deriv (deriv (deriv a₁)) y - ((((S.p - 2) * deriv Φ₀ y ^ (S.p - 2 - 1) *
        deriv (deriv Φ₀) y : ℝ) : ℂ) * deriv (deriv a₀) y + ((deriv Φ₀ y ^ (S.p - 2) : ℝ) : ℂ) *
        deriv (deriv (deriv a₀)) y)) := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    calc _ ≤ C31 * min 1 δ * A * u ^ 3 * Λ ^ (S.p - 2) + 1 * (MQ * δ * A * u ^ 3 * Λ ^ (S.p - 2)) := by
          gcongr
          exact hQ.2
      _ ≤ C31 * δ * A * u ^ 3 * Λ ^ (S.p - 2) + 1 * (MQ * δ * A * u ^ 3 * Λ ^ (S.p - 2)) := by
          gcongr
      _ = (C31 + MQ) * δ * (A * u ^ 2 * Λ ^ (S.p - 2)) * u := by ring
      _ ≤ K * δ * X * u := by
          rw [hXe]; gcongr; linarith
  · calc ‖T y‖ ≤ C20 * A * u ^ 2 * Λ ^ (S.p - 2) := hT0
      _ = C20 * X := by rw [← hXe]; ring
      _ ≤ K * X := by gcongr; linarith
  · calc ‖deriv T y‖ ≤ C21 * A * u ^ 3 * Λ ^ (S.p - 2) := hT1
      _ = C21 * X * u := by rw [← hXe]; ring
      _ ≤ K * X * u := by gcongr; linarith

/-- Helper for lem:c05_multiplier_fundamental: `δ_Y Y^{-β-2} Λ^{p-2} = εY^{-p-3β}` (exponents). -/
theorem c05_aux_mf_exp (p Y : ℝ) (hY : 0 < Y) (hp : 0 < p) :
    Y ^ (1 / p - p) * (Y ^ (-beta p) * Y⁻¹ ^ 2 * (Y ^ (1 / p)) ^ (p - 2)) = Y ^ (-p - 3 * beta p) := by
  have h2β := c05_aux_two_beta p hp
  rw [← Real.rpow_mul hY.le, ← c05_aux_mf_Yk hY 2, ← Real.rpow_add hY, ← Real.rpow_add hY,
    ← Real.rpow_add hY]
  congr 1
  have : beta p = (1 + 1 / p) / 2 := by linarith
  rw [this]
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- Helper for lem:c05_multiplier_fundamental: the difference bound
(eqn:approx_E5_multiplier_difference_bound). -/
theorem c05_aux_mf_diffbound (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          ‖iteratedDeriv j (fun t => c05_auxiliary_remainders_Emult S.p R ε μ Y t -
              c05_auxiliary_remainders_Emult0 S.p R μ Y t) y‖ ≤
            C * ε * Y ^ (-S.p - 3 * beta S.p + j / S.p) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  obtain ⟨Rh, hRh, cs, hcs, hyp⟩ := c05_multiplier_hypotheses S
  choose Ck hCk hCkb using hyp
  obtain ⟨Ri, hRi, hid⟩ := c05_aux_mf_identity S
  obtain ⟨Rw, hRw, KW, hKW, hWT⟩ := c05_aux_mf_WT S
  set K : ℝ := KW + (Ck 0 + Ck 1) * (1 + cs⁻¹) + cs⁻¹ + 1 with hK
  have hC0 := hCk 0
  have hC1 := hCk 1
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max (max Rh Ri) Rw, hRh.trans (by simp), 4 * (K * K + K) + 1, by positivity, ?_⟩
  intro ε μ R Y ht y hy j hj
  have htH := c05_aux_tuple_mono (show Rh ≤ max (max Rh Ri) Rw by simp) ht
  have htI := c05_aux_tuple_mono (show Ri ≤ max (max Rh Ri) Rw by simp) ht
  have htW := c05_aux_tuple_mono (show Rw ≤ max (max Rh Ri) Rw by simp) ht
  have hR : 1 ≤ R := hRh.trans htH.2.2.2.1
  have hY8 : 8 * R ≤ Y := ht.2.2.2.2
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := ht.1
  obtain ⟨dW, dT, hW0, hW1, hT0, hT1⟩ := hWT ε μ R Y htW y hy
  set Λ := Y ^ (1 / S.p) with hΛ
  set δ := ε * Y ^ (1 / S.p - S.p) with hδ
  set X := Y ^ (-beta S.p) * Y⁻¹ ^ 2 * Λ ^ (S.p - 2) with hX
  set a₁ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A S.p ε μ z with ha₁
  set a₀ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A_zero S.p μ z with ha₀
  set Φ := c05_standing_Phi S.p R ε μ with hΦ
  set Φ₀ := c05_standing_Phi_zero S.p with hΦ₀
  set T : ℝ → ℂ := c03_mult_R2tilde S.p Y a₀ Φ₀ with hT
  set W : ℝ → ℂ := fun t => c03_mult_R2tilde S.p Y a₁ Φ t - c03_mult_R2tilde S.p Y a₀ Φ₀ t with hW
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow hY1 (by positivity)
  have hδ0 : 0 ≤ δ := by positivity
  have hX0 : 0 ≤ X := by positivity
  have hw1 : Y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hY1
  set IY := Ioo (Y / 4) (4 * Y) with hIY
  have hyI : y ∈ IY := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hIYn : IY ∈ nhds y := Ioo_mem_nhds hyI.1 hyI.2
  have hH := fun k => hCkb k ε μ R Y htH
  obtain ⟨⟨ha₁s, ha₀s, -, -, -, -, hΦs, hΦ₀s⟩, -⟩ := hH 0
  -- the identity near `y`
  set u : ℝ → ℂ := fun t => Complex.exp (Complex.I * (Φ t : ℂ)) with hu
  set v : ℝ → ℂ := fun t => Complex.exp (Complex.I * (Φ₀ t : ℂ)) with hv
  have hy2 : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hev : (fun t => c05_auxiliary_remainders_Emult S.p R ε μ Y t -
      c05_auxiliary_remainders_Emult0 S.p R μ Y t) =ᶠ[nhds y]
      fun t => u t * W t + (u t - v t) * T t := by
    filter_upwards [Ioo_mem_nhds hy2.1 hy2.2] with t ht'
    have htI' : t ∈ IY := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    obtain ⟨e1, e0⟩ := hid ε μ R Y htI t ht'
    rw [e1, e0, c05_aux_mf_Rtilde_eq S.p Y a₁ Φ (ha₁s.of_le (WithTop.coe_le_coe.mpr le_top))
      (hΦs.of_le (WithTop.coe_le_coe.mpr le_top)) htI',
      c05_aux_mf_Rtilde_eq S.p Y a₀ Φ₀ (ha₀s.of_le (WithTop.coe_le_coe.mpr le_top))
      (hΦ₀s.of_le (WithTop.coe_le_coe.mpr le_top)) htI']
    simp only [hu, hv, hW, hT]
    ring
  -- phase data
  obtain ⟨⟨hx₁, hx₁', hx₀, -⟩, -⟩ := (hH 0).2 y hyI
  obtain ⟨-, ⟨-, hΦd0⟩, -⟩ := (hH 0).2 y hyI
  obtain ⟨-, ⟨-, hΦd1⟩, -⟩ := (hH 1).2 y hyI
  have hΦc : ContDiffAt ℝ 1 Φ y := (hΦs.contDiffAt hIYn).of_le (WithTop.coe_le_coe.mpr le_top)
  have hΦ₀c : ContDiffAt ℝ 1 Φ₀ y := (hΦ₀s.contDiffAt hIYn).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_zero] at hΦd0
  rw [iteratedDeriv_fun_sub hΦc hΦ₀c, iteratedDeriv_one, iteratedDeriv_one] at hΦd1
  simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, Nat.cast_one] at hΦd0 hΦd1
  rw [Real.rpow_neg_one] at hΦd1
  have hl₁ : 0 < deriv Φ y := lt_of_lt_of_le (by positivity) hx₁
  have hud : HasDerivAt u (Complex.I * ((deriv Φ y : ℝ) : ℂ) * u y) y := by
    have := ((hΦc.differentiableAt one_ne_zero).hasDerivAt.ofReal_comp.const_mul Complex.I).cexp
    simp only [hu]; convert this using 1; ring
  have hvd : HasDerivAt v (Complex.I * ((deriv Φ₀ y : ℝ) : ℂ) * v y) y := by
    have := ((hΦ₀c.differentiableAt one_ne_zero).hasDerivAt.ofReal_comp.const_mul Complex.I).cexp
    simp only [hv]; convert this using 1; ring
  have hun : ∀ t, ‖u t‖ = 1 := fun t => by
    simp only [hu]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hvn : ∀ t, ‖v t‖ = 1 := fun t => by
    simp only [hv]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have huv0 : ‖u y - v y‖ ≤ Ck 0 * δ := by
    simp only [hu, hv]
    rw [c05_aux_exp_phase]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
    rw [Real.norm_eq_abs]; exact hΦd0
  have hu1 : ‖Complex.I * ((deriv Φ y : ℝ) : ℂ) * u y‖ ≤ K * Λ := by
    rw [norm_mul, norm_mul, hun, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hl₁, one_mul, mul_one]
    refine hx₁'.trans ?_
    gcongr
    have : 0 ≤ (Ck 0 + Ck 1) * (1 + cs⁻¹) := by positivity
    linarith
  have huv1 : ‖Complex.I * ((deriv Φ y : ℝ) : ℂ) * u y - Complex.I * ((deriv Φ₀ y : ℝ) : ℂ) * v y‖ ≤ K * δ * Λ := by
    have e : Complex.I * ((deriv Φ y : ℝ) : ℂ) * u y - Complex.I * ((deriv Φ₀ y : ℝ) : ℂ) * v y =
        Complex.I * (((deriv Φ y : ℝ) : ℂ) * (u y - v y) + ((deriv Φ y - deriv Φ₀ y : ℝ) : ℂ) * v y) := by
      push_cast; ring
    rw [e, norm_mul, Complex.norm_I, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hvn, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hl₁]
    have hYi : Y⁻¹ ≤ Λ := hw1.trans hΛ1
    calc deriv Φ y * ‖u y - v y‖ + |deriv Φ y - deriv Φ₀ y|
        ≤ (cs⁻¹ * Λ) * (Ck 0 * δ) + Ck 1 * δ * Y⁻¹ := by gcongr
      _ ≤ (cs⁻¹ * Λ) * (Ck 0 * δ) + Ck 1 * δ * Λ := by gcongr
      _ = (cs⁻¹ * Ck 0 + Ck 1) * δ * Λ := by ring
      _ ≤ K * δ * Λ := by
          gcongr
          have : 0 ≤ Ck 0 + Ck 1 := by positivity
          nlinarith [inv_pos.mpr hcs]
  have hKW' : KW ≤ K := by
    have : 0 ≤ (Ck 0 + Ck 1) * (1 + cs⁻¹) := by positivity
    have : 0 ≤ cs⁻¹ := by positivity
    linarith
  have hC0K : Ck 0 ≤ K := by
    have : 0 ≤ Ck 0 * cs⁻¹ + Ck 1 * (1 + cs⁻¹) := by positivity
    nlinarith
  obtain ⟨hc0, hc1⟩ := c05_aux_mf_combine (u0 := u y) (u1 := Complex.I * ((deriv Φ y : ℝ) : ℂ) * u y)
    (v0 := v y) (v1 := Complex.I * ((deriv Φ₀ y : ℝ) : ℂ) * v y) (W0 := W y) (W1 := deriv W y)
    (T0 := T y) (T1 := deriv T y) hK0 hΛ1 hw1 hδ0 hX0 (hun y) hu1
    (huv0.trans (by gcongr)) huv1
    (hW0.trans (by gcongr)) (hW1.trans (by gcongr)) (hT0.trans (by gcongr)) (hT1.trans (by gcongr))
  have hexp := c05_aux_mf_exp S.p Y hY0 hp0
  have hδX : δ * X = ε * Y ^ (-S.p - 3 * beta S.p) := by
    rw [hδ, hX, hΛ, mul_assoc, hexp]
  interval_cases j
  · rw [iteratedDeriv_zero, hev.eq_of_nhds]
    simp only [Nat.cast_zero, zero_div, add_zero]
    calc _ ≤ 4 * (K * K + K) * δ * X := hc0
      _ = 4 * (K * K + K) * (ε * Y ^ (-S.p - 3 * beta S.p)) := by rw [← hδX]; ring
      _ ≤ (4 * (K * K + K) + 1) * ε * Y ^ (-S.p - 3 * beta S.p) := by
          have : 0 ≤ ε * Y ^ (-S.p - 3 * beta S.p) := by positivity
          nlinarith
  · rw [iteratedDeriv_one, hev.deriv_eq]
    have hG : HasDerivAt (fun t => u t * W t + (u t - v t) * T t) _ y :=
      (hud.mul dW.hasDerivAt).add ((hud.sub hvd).mul dT.hasDerivAt)
    rw [hG.deriv]
    simp only [Nat.cast_one]
    have hYe : Y ^ (-S.p - 3 * beta S.p + 1 / S.p) = Y ^ (-S.p - 3 * beta S.p) * Λ := by
      rw [hΛ, ← Real.rpow_add hY0]
    rw [hYe]
    calc _ ≤ 4 * (K * K + K) * δ * X * Λ := hc1
      _ = 4 * (K * K + K) * (ε * Y ^ (-S.p - 3 * beta S.p) * Λ) := by rw [← hδX]; ring
      _ ≤ (4 * (K * K + K) + 1) * ε * (Y ^ (-S.p - 3 * beta S.p) * Λ) := by
          have : 0 ≤ ε * Y ^ (-S.p - 3 * beta S.p) * Λ := by positivity
          nlinarith

/-- Blueprint: lem:c05_multiplier_fundamental.  On `(Y/2,3Y)`:
`ℰ_mult = e^{iΦ} ℛ̃_{mult,2}[a₁,Φ]`, `ℰ_{mult,0} = e^{iΦ₀} ℛ̃_{mult,2}[a₀,Φ₀]`; and on `[Y,2Y]`,
`|∂_y^j(ℰ_mult - ℰ_{mult,0})| ≤ C ε Y^{-p-3β+j/p}`, `j = 0,1`. -/
theorem c05_multiplier_fundamental (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        (∀ y ∈ Ioo (Y / 2) (3 * Y),
          c05_auxiliary_remainders_Emult S.p R ε μ Y y =
              Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ y : ℂ)) *
                c05_multiplier_fundamental_Rtilde S.p
                  (fun z => (res_chiY Y z : ℂ) * c05_standing_A S.p ε μ z)
                  (c05_standing_Phi S.p R ε μ) y ∧
            c05_auxiliary_remainders_Emult0 S.p R μ Y y =
              Complex.exp (Complex.I * (c05_standing_Phi_zero S.p y : ℂ)) *
                c05_multiplier_fundamental_Rtilde S.p
                  (fun z => (res_chiY Y z : ℂ) * c05_standing_A_zero S.p μ z)
                  (c05_standing_Phi_zero S.p) y) ∧
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          ‖iteratedDeriv j (fun t => c05_auxiliary_remainders_Emult S.p R ε μ Y t -
              c05_auxiliary_remainders_Emult0 S.p R μ Y t) y‖ ≤
            C * ε * Y ^ (-S.p - 3 * beta S.p + j / S.p) := by
  obtain ⟨Ri, hRi, hid⟩ := c05_aux_mf_identity S
  obtain ⟨Rd, hRd, Cd, hCd, hbd⟩ := c05_aux_mf_diffbound S
  refine ⟨max Ri Rd, hRi.trans (le_max_left _ _), Cd, hCd, fun ε μ R Y ht => ⟨fun y hy =>
    hid ε μ R Y (c05_aux_tuple_mono (le_max_left _ _) ht) y hy, fun y hy j hj =>
    hbd ε μ R Y (c05_aux_tuple_mono (le_max_right _ _) ht) y hy j hj⟩⟩

/-- Helper for lem:c05_fundamental_primitive: pair bounds (value, derivative, difference) at a point. -/
def c05_aux_PB (u u' u0 u0' : ℂ) (K X e σ : ℝ) : Prop :=
  ‖u‖ ≤ K * X ∧ ‖u'‖ ≤ K * X * σ ∧ ‖u0‖ ≤ K * X ∧ ‖u0'‖ ≤ K * X * σ ∧
    ‖u - u0‖ ≤ K * e * X ∧ ‖u' - u0'‖ ≤ K * e * X * σ

/-- Helper for lem:c05_fundamental_primitive. -/
theorem c05_aux_PB_mono {u u' u0 u0' : ℂ} {K K' X e σ : ℝ} (h : c05_aux_PB u u' u0 u0' K X e σ)
    (hK : K ≤ K') (hX : 0 ≤ X) (he : 0 ≤ e) (hσ : 0 ≤ σ) : c05_aux_PB u u' u0 u0' K' X e σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_, h4.trans ?_, h5.trans ?_, h6.trans ?_⟩ <;> gcongr

/-- Helper for lem:c05_fundamental_primitive. -/
theorem c05_aux_PB_mul {u u' u0 u0' v v' v0 v0' : ℂ} {K1 K2 X1 X2 e σ : ℝ}
    (hu : c05_aux_PB u u' u0 u0' K1 X1 e σ) (hv : c05_aux_PB v v' v0 v0' K2 X2 e σ)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hX1 : 0 ≤ X1) (hX2 : 0 ≤ X2) (he : 0 ≤ e) (hσ : 0 ≤ σ) :
    c05_aux_PB (u * v) (u' * v + u * v') (u0 * v0) (u0' * v0 + u0 * v0') (4 * K1 * K2) (X1 * X2) e σ := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hu
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hv
  have P : 0 ≤ K1 * K2 * X1 * X2 := by positivity
  have Pσ : 0 ≤ K1 * K2 * X1 * X2 * σ := by positivity
  have Pe : 0 ≤ K1 * K2 * e * X1 * X2 := by positivity
  have Peσ : 0 ≤ K1 * K2 * e * X1 * X2 * σ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc ‖u * v‖ ≤ (K1 * X1) * (K2 * X2) := norm_mul_le_of_le a1 b1
      _ ≤ _ := by nlinarith
  · calc ‖u' * v + u * v'‖ ≤ ‖u' * v‖ + ‖u * v'‖ := norm_add_le _ _
      _ ≤ (K1 * X1 * σ) * (K2 * X2) + (K1 * X1) * (K2 * X2 * σ) :=
          add_le_add (norm_mul_le_of_le a2 b1) (norm_mul_le_of_le a1 b2)
      _ ≤ _ := by nlinarith
  · calc ‖u0 * v0‖ ≤ (K1 * X1) * (K2 * X2) := norm_mul_le_of_le a3 b3
      _ ≤ _ := by nlinarith
  · calc ‖u0' * v0 + u0 * v0'‖ ≤ ‖u0' * v0‖ + ‖u0 * v0'‖ := norm_add_le _ _
      _ ≤ (K1 * X1 * σ) * (K2 * X2) + (K1 * X1) * (K2 * X2 * σ) :=
          add_le_add (norm_mul_le_of_le a4 b3) (norm_mul_le_of_le a3 b4)
      _ ≤ _ := by nlinarith
  · calc ‖u * v - u0 * v0‖ = ‖(u - u0) * v + u0 * (v - v0)‖ := by ring_nf
      _ ≤ ‖(u - u0) * v‖ + ‖u0 * (v - v0)‖ := norm_add_le _ _
      _ ≤ (K1 * e * X1) * (K2 * X2) + (K1 * X1) * (K2 * e * X2) :=
          add_le_add (norm_mul_le_of_le a5 b1) (norm_mul_le_of_le a3 b5)
      _ ≤ _ := by nlinarith
  · calc ‖u' * v + u * v' - (u0' * v0 + u0 * v0')‖ =
          ‖((u' - u0') * v + u0' * (v - v0)) + ((u - u0) * v' + u0 * (v' - v0'))‖ := by ring_nf
      _ ≤ (‖(u' - u0') * v‖ + ‖u0' * (v - v0)‖) + (‖(u - u0) * v'‖ + ‖u0 * (v' - v0')‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ ((K1 * e * X1 * σ) * (K2 * X2) + (K1 * X1 * σ) * (K2 * e * X2)) +
          ((K1 * e * X1) * (K2 * X2 * σ) + (K1 * X1) * (K2 * e * X2 * σ)) :=
          add_le_add (add_le_add (norm_mul_le_of_le a6 b1) (norm_mul_le_of_le a4 b5))
            (add_le_add (norm_mul_le_of_le a5 b2) (norm_mul_le_of_le a3 b6))
      _ ≤ _ := by nlinarith

/-- Helper for lem:c05_fundamental_primitive: `(iλ)⁻¹` pair bounds from the `λ` pair data. -/
theorem c05_aux_PB_inv {l l' l0 l0' K L e σ : ℝ} (hL : 0 < L) (hK : 0 ≤ K) (he : 0 ≤ e) (hσ : 0 ≤ σ)
    (hl : L / 2 ≤ l) (hl2 : l ≤ 2 * L) (hl0 : L / 2 ≤ l0) (hl02 : l0 ≤ 2 * L)
    (hl' : |l'| ≤ K * L * σ) (hl0' : |l0'| ≤ K * L * σ) (hd : |l - l0| ≤ K * e * L)
    (hd' : |l' - l0'| ≤ K * e * L * σ) :
    c05_aux_PB (Complex.I * (l : ℂ))⁻¹ (-(Complex.I * (l' : ℂ)) / (Complex.I * (l : ℂ)) ^ 2)
      (Complex.I * (l0 : ℂ))⁻¹ (-(Complex.I * (l0' : ℂ)) / (Complex.I * (l0 : ℂ)) ^ 2)
      (2 + 4 * K + 64 * K ^ 2) L⁻¹ e σ := by
  have hlp : 0 < l := by linarith
  have hl0p : 0 < l0 := by linarith
  have e1 : ∀ x : ℝ, 0 < x → ‖(Complex.I * (x : ℂ))⁻¹‖ = x⁻¹ := by
    intro x hx; rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
  have e2 : ∀ x y : ℝ, 0 < x → -(Complex.I * (y : ℂ)) / (Complex.I * (x : ℂ)) ^ 2 =
      Complex.I * ((y / x ^ 2 : ℝ) : ℂ) := by
    intro x y hx
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast; field_simp; rw [Complex.I_sq]; ring
  have e3 : ∀ y : ℝ, ‖Complex.I * (y : ℂ)‖ = |y| := by
    intro y; rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hiL : l⁻¹ ≤ 2 * L⁻¹ := by
    rw [inv_le_comm₀ hlp (by positivity)]; rw [mul_inv, inv_inv]; linarith
  have hiL0 : l0⁻¹ ≤ 2 * L⁻¹ := by
    rw [inv_le_comm₀ hl0p (by positivity)]; rw [mul_inv, inv_inv]; linarith
  have hiLp : 0 ≤ L⁻¹ := by positivity
  set M := 2 + 4 * K + 64 * K ^ 2 with hM
  have hM2 : 2 ≤ M := by nlinarith
  have hM4 : 4 * K ≤ M := by nlinarith
  have hM64 : 4 * K + 64 * K ^ 2 ≤ M := by nlinarith
  -- `|y|/x² ≤ 4K σ/L` for derivative terms
  have hq : ∀ K' x y : ℝ, 0 ≤ K' → L / 2 ≤ x → |y| ≤ K' * L * σ → |y / x ^ 2| ≤ 4 * K' * L⁻¹ * σ := by
    intro K x y hK hx hy
    have hx0 : 0 < x := by linarith
    rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 2), div_le_iff₀ (by positivity)]
    have : L ^ 2 ≤ 4 * x ^ 2 := by nlinarith
    calc |y| ≤ K * L * σ := hy
      _ = K * L⁻¹ * σ * L ^ 2 := by field_simp
      _ ≤ K * L⁻¹ * σ * (4 * x ^ 2) := by gcongr
      _ = 4 * K * L⁻¹ * σ * x ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1 l hlp]; nlinarith
  · rw [e2 l l' hlp, e3]
    calc _ ≤ 4 * K * L⁻¹ * σ := hq K l l' hK hl hl'
      _ ≤ M * L⁻¹ * σ := by gcongr
  · rw [e1 l0 hl0p]; nlinarith
  · rw [e2 l0 l0' hl0p, e3]
    calc _ ≤ 4 * K * L⁻¹ * σ := hq K l0 l0' hK hl0 hl0'
      _ ≤ M * L⁻¹ * σ := by gcongr
  · have : (Complex.I * (l : ℂ))⁻¹ - (Complex.I * (l0 : ℂ))⁻¹ =
        (Complex.I * ((l0 - l : ℝ) : ℂ)) * ((l : ℂ)⁻¹ * (l0 : ℂ)⁻¹) * (-1) := by
      have : (l : ℂ) ≠ 0 := by exact_mod_cast hlp.ne'
      have : (l0 : ℂ) ≠ 0 := by exact_mod_cast hl0p.ne'
      push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [this, norm_mul, norm_neg, norm_one, mul_one, norm_mul, e3, norm_mul, norm_inv, norm_inv,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlp,
      abs_of_pos hl0p, abs_sub_comm]
    calc |l - l0| * (l⁻¹ * l0⁻¹) ≤ (K * e * L) * ((2 * L⁻¹) * (2 * L⁻¹)) := by
          gcongr
      _ = 4 * K * e * L⁻¹ := by field_simp; ring
      _ ≤ M * e * L⁻¹ := by gcongr
  · rw [e2 l l' hlp, e2 l0 l0' hl0p, ← mul_sub, ← Complex.ofReal_sub, e3]
    have hsplit : l' / l ^ 2 - l0' / l0 ^ 2 =
        (l' - l0') / l ^ 2 + l0' * ((l0 - l) * (l0 + l)) / (l ^ 2 * l0 ^ 2) := by
      field_simp; ring
    rw [hsplit]
    have t1 : |(l' - l0') / l ^ 2| ≤ 4 * K * e * L⁻¹ * σ := by
      have := hq (K * e) l (l' - l0') (by positivity) hl hd'
      calc _ ≤ 4 * (K * e) * L⁻¹ * σ := this
        _ = _ := by ring
    have t2 : |l0' * ((l0 - l) * (l0 + l)) / (l ^ 2 * l0 ^ 2)| ≤ 64 * K ^ 2 * e * L⁻¹ * σ := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < l ^ 2 * l0 ^ 2),
        abs_of_pos (by linarith : 0 < l0 + l), abs_sub_comm, div_le_iff₀ (by positivity)]
      have hL4 : L ^ 4 ≤ 16 * (l ^ 2 * l0 ^ 2) := by
        have a : L ^ 2 ≤ 4 * l ^ 2 := by nlinarith
        have b : L ^ 2 ≤ 4 * l0 ^ 2 := by nlinarith
        have : L ^ 4 = L ^ 2 * L ^ 2 := by ring
        rw [this]; nlinarith [sq_nonneg L]
      calc |l0'| * (|l - l0| * (l0 + l)) ≤ (K * L * σ) * ((K * e * L) * (4 * L)) := by
            gcongr; linarith
        _ = 4 * K ^ 2 * e * σ * L ^ 3 := by ring
        _ = 4 * K ^ 2 * e * σ * L⁻¹ * L ^ 4 := by field_simp
        _ ≤ 4 * K ^ 2 * e * σ * L⁻¹ * (16 * (l ^ 2 * l0 ^ 2)) := by gcongr
        _ = _ := by ring
    calc _ ≤ |(l' - l0') / l ^ 2| + |l0' * ((l0 - l) * (l0 + l)) / (l ^ 2 * l0 ^ 2)| := abs_add_le _ _
      _ ≤ 4 * K * e * L⁻¹ * σ + 64 * K ^ 2 * e * L⁻¹ * σ := add_le_add t1 t2
      _ = (4 * K + 64 * K ^ 2) * e * L⁻¹ * σ := by ring
      _ ≤ M * e * L⁻¹ * σ := by gcongr

/-- Helper for lem:c05_fundamental_primitive. -/
theorem c05_aux_exp_diff (u u0 e1 e0 : ℂ) (h1 : ‖e1‖ = 1) :
    ‖u * e1 - u0 * e0‖ ≤ ‖u - u0‖ + ‖u0‖ * ‖e1 - e0‖ := by
  calc ‖u * e1 - u0 * e0‖ = ‖(u - u0) * e1 + u0 * (e1 - e0)‖ := by ring_nf
    _ ≤ ‖(u - u0) * e1‖ + ‖u0 * (e1 - e0)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul, h1, mul_one]


/-- Helper for lem:c05_fundamental_primitive. -/
theorem c05_aux_cmul_le {c x : ℂ} {M A B K : ℝ} (hc : ‖c‖ ≤ M) (hx : ‖x‖ ≤ A * B)
    (hMA : M * A ≤ K) (hB : 0 ≤ B) : ‖c * x‖ ≤ K * B := by
  rw [norm_mul]
  have hM : 0 ≤ M := (norm_nonneg _).trans hc
  calc ‖c‖ * ‖x‖ ≤ M * (A * B) := mul_le_mul hc hx (norm_nonneg _) hM
    _ = (M * A) * B := by ring
    _ ≤ K * B := by gcongr

/-- Helper for lem:c05_fundamental_primitive. -/
theorem c05_aux_q_form (p : ℝ) (μ a : ℂ) {l : ℝ} (hl : 0 < l) :
    μ * a * ((l ^ (-(p + 1) / 2) : ℝ) : ℂ) / (Complex.I * (l : ℂ)) =
      -Complex.I * μ * (a * ((l ^ (-((p + 3) / 2)) : ℝ) : ℂ)) := by
  rw [show -((p + 3) / 2) = -(p + 1) / 2 - 1 by ring, Real.rpow_sub_one hl.ne']
  have : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  field_simp
  rw [Complex.I_sq]; ring

/-- Helper for lem:c05_fundamental_primitive (data). -/
theorem c05_aux_fp_data (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ContDiffOn ℝ (⊤ : ℕ∞) (fun t => c05_standing_A S.p ε μ t /
          (Complex.I * (fam_lambda S.p ε μ t : ℂ))) (Ioi (R / 2)) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun t => c05_standing_A_zero S.p μ t /
          (Complex.I * (lambda0 S.p t : ℂ))) (Ioi (R / 2)) ∧
        (∀ t, R / 2 < t → 0 < fam_lambda S.p ε μ t) ∧
        ∀ s : ℝ, R ≤ s →
          c05_aux_PB
            (deriv (fun t => c05_standing_A S.p ε μ t / (Complex.I * (fam_lambda S.p ε μ t : ℂ))) s)
            (deriv (deriv (fun t => c05_standing_A S.p ε μ t /
              (Complex.I * (fam_lambda S.p ε μ t : ℂ)))) s)
            (deriv (fun t => c05_standing_A_zero S.p μ t / (Complex.I * (lambda0 S.p t : ℂ))) s)
            (deriv (deriv (fun t => c05_standing_A_zero S.p μ t /
              (Complex.I * (lambda0 S.p t : ℂ)))) s)
            K (s ^ (-beta S.p - 1 / S.p - 1)) (ε * s ^ (-S.p - 1)) (s ^ (-1 : ℝ)) ∧
          s ^ (1 / S.p) / 2 ≤ fam_lambda S.p ε μ s ∧ fam_lambda S.p ε μ s ≤ 2 * s ^ (1 / S.p) ∧
          |deriv (fam_lambda S.p ε μ) s| ≤ K * s ^ (1 / S.p) * s ^ (-1 : ℝ) ∧
          |deriv (lambda0 S.p) s| ≤ K * s ^ (1 / S.p) * s ^ (-1 : ℝ) ∧
          |fam_lambda S.p ε μ s - lambda0 S.p s| ≤ K * (ε * s ^ (-S.p - 1)) * s ^ (1 / S.p) ∧
          |deriv (fam_lambda S.p ε μ) s - deriv (lambda0 S.p) s| ≤
            K * (ε * s ^ (-S.p - 1)) * s ^ (1 / S.p) * s ^ (-1 : ℝ) ∧
          ‖Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ s : ℂ)) -
            Complex.exp (Complex.I * (c05_standing_Phi_zero S.p s : ℂ))‖ ≤
              K * ε * s ^ (1 / S.p - S.p) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  set q₁ : ℝ := (S.p + 3) / 2 with hq₁
  have hq₁0 : 0 < q₁ := by positivity
  have hqβ : -q₁ / S.p = -beta S.p - 1 / S.p := by rw [hq₁]; unfold beta; field_simp; ring
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs0, hCs0, hsy0⟩ := hsym 0
  obtain ⟨Cs1, hCs1, hsy1⟩ := hsym 1
  obtain ⟨R1, hR1, hlpos⟩ := c05_aux_lambda_pos S
  obtain ⟨-, RZ, hRZ, HZB, -⟩ := Classical.choose_spec (c04_Z_bounds S.p hp hp1 S.δ S.hδ S.hδ_le)
  obtain ⟨-, RD, hRD, HZD⟩ := Classical.choose_spec (c04_Z_difference S.p hp hp1 S.δ S.hδ S.hδ_le)
  obtain ⟨CZ1, hCZ1, HZ1⟩ := HZB 1 q₁ hq₁0
  obtain ⟨CZ2, hCZ2, HZ2⟩ := HZB 2 q₁ hq₁0
  obtain ⟨CD0, hCD0, HD0⟩ := HZD 0 q₁ hq₁0
  obtain ⟨CD1, hCD1, HD1⟩ := HZD 1 q₁ hq₁0
  set Mμ := ‖mu_star S.p‖ + S.δ with hMμ
  have hMμ0 : 0 ≤ Mμ := by have := S.hδ; positivity
  set R₀ := max (max Rs (2 * R1)) (max RZ RD) with hR₀
  set K := Mμ * (CZ1 + CZ2 + CD0 + CD1) + Cs0 + Cs1 + 3 with hK
  have hKa : Mμ * CZ1 ≤ K ∧ Mμ * CZ2 ≤ K ∧ Mμ * CD0 ≤ K ∧ Mμ * CD1 ≤ K ∧ Cs0 ≤ K ∧ Cs1 ≤ K ∧ 2 ≤ K := by
    have := mul_nonneg hMμ0 hCZ1.le; have := mul_nonneg hMμ0 hCZ2.le
    have := mul_nonneg hMμ0 hCD0.le; have := mul_nonneg hMμ0 hCD1.le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
  refine ⟨R₀, hRs.trans (by simp [hR₀]), K, by positivity, ?_⟩
  intro ε μ R Y ht
  have hts := c05_aux_tuple_mono (show Rs ≤ R₀ by simp [hR₀]) ht
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hR0 : 0 < R := by linarith
  have hR1R : 2 * R1 ≤ R := le_trans (by simp [hR₀]) ht.2.2.2.1
  have hRZR : RZ ≤ R := le_trans (by simp [hR₀]) ht.2.2.2.1
  have hRDR : RD ≤ R := le_trans (by simp [hR₀]) ht.2.2.2.1
  obtain ⟨hε0, hε1, hμ, -, -⟩ := ht
  have hεZ := (c05_aux_eps_le S hε0 hε1).2.1
  have hεD := (c05_aux_eps_le S hε0 hε1).2.2.2.1
  have h0Z := (c05_aux_eps_le S le_rfl S.hε₀_pos.le).2.1
  have hμK : ‖μ‖ ≤ Mμ := by
    have h1 : dist μ (mu_star S.p) ≤ S.δ := hμ
    have h2 := norm_le_norm_add_norm_sub' μ (mu_star S.p)
    rw [dist_eq_norm] at h1
    rw [hMμ]; linarith
  have hpos : ∀ t, R / 2 < t → 0 < fam_lambda S.p ε μ t := fun t ht' =>
    hlpos ε μ hε0 hε1 hμ t (by linarith)
  set c : ℂ := -Complex.I * μ with hc
  have hcn : ‖c‖ ≤ Mμ := by rw [hc, norm_mul, norm_neg, Complex.norm_I, one_mul]; exact hμK
  set h : ℝ → ℂ := fun t => astar S.p t * ((fam_lambda S.p ε μ t ^ (-q₁) : ℝ) : ℂ) with hh
  set h0 : ℝ → ℂ := fun t => astar S.p t * ((lambda0 S.p t ^ (-q₁) : ℝ) : ℂ) with hh0
  set U : Set ℝ := Ioi (R / 2) with hU
  have hUo : IsOpen U := isOpen_Ioi
  have hU0 : ∀ t ∈ U, 0 < t := fun t ht' => lt_trans (half_pos hR0) ht'
  have hhs : ContDiffOn ℝ (⊤ : ℕ∞) h U := fun t ht' =>
    ((c05_aux_astar_smooth S.p hp hp1 (hU0 t ht')).mul (c05_aux_ofReal
      ((c05_aux_lambda_smooth S.p ε μ (hU0 t ht')).rpow_const_of_ne (hpos t ht').ne'))).contDiffWithinAt
  have hh0s : ContDiffOn ℝ (⊤ : ℕ∞) h0 U := fun t ht' =>
    ((c05_aux_astar_smooth S.p hp hp1 (hU0 t ht')).mul (c05_aux_ofReal
      ((c05_aux_rpow_at (hU0 t ht')).rpow_const_of_ne
        (Real.rpow_pos_of_pos (hU0 t ht') _).ne'))).contDiffWithinAt
  have hqeq : ∀ t ∈ U, c05_standing_A S.p ε μ t / (Complex.I * (fam_lambda S.p ε μ t : ℂ)) = c * h t :=
    fun t ht' => c05_aux_q_form S.p μ (astar S.p t) (hpos t ht')
  have hq0eq : ∀ t ∈ U, c05_standing_A_zero S.p μ t / (Complex.I * (lambda0 S.p t : ℂ)) = c * h0 t :=
    fun t ht' => c05_aux_q_form S.p μ (astar S.p t) (Real.rpow_pos_of_pos (hU0 t ht') _)
  have hqs : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => c05_standing_A S.p ε μ t /
      (Complex.I * (fam_lambda S.p ε μ t : ℂ))) U := (contDiffOn_const.mul hhs).congr hqeq
  have hq0s : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => c05_standing_A_zero S.p μ t /
      (Complex.I * (lambda0 S.p t : ℂ))) U := (contDiffOn_const.mul hh0s).congr hq0eq
  have hdh : ContDiffOn ℝ (⊤ : ℕ∞) (deriv h) U := hhs.deriv_of_isOpen hUo (m := (⊤ : ℕ∞)) (by simp)
  have hdh0 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv h0) U := hh0s.deriv_of_isOpen hUo (m := (⊤ : ℕ∞)) (by simp)
  have hdiff : ∀ {f : ℝ → ℂ}, ContDiffOn ℝ (⊤ : ℕ∞) f U → ∀ t ∈ U, DifferentiableAt ℝ f t :=
    fun hf t ht' => (hf.contDiffAt (hUo.mem_nhds ht')).differentiableAt (by simp)
  refine ⟨hqs, hq0s, hpos, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := hR.trans hs
  have hs0 : 0 < s := by linarith
  have hsU : s ∈ U := by show R / 2 < s; linarith
  -- the derivatives `g, g'` via `h`
  have hEq : (fun t => c05_standing_A S.p ε μ t / (Complex.I * (fam_lambda S.p ε μ t : ℂ))) =ᶠ[nhds s]
      fun t => c * h t := Filter.eventuallyEq_of_mem (hUo.mem_nhds hsU) hqeq
  have hEq0 : (fun t => c05_standing_A_zero S.p μ t / (Complex.I * (lambda0 S.p t : ℂ))) =ᶠ[nhds s]
      fun t => c * h0 t := Filter.eventuallyEq_of_mem (hUo.mem_nhds hsU) hq0eq
  have hg := hEq.deriv
  have hg0 := hEq0.deriv
  rw [deriv_const_mul_field'] at hg hg0
  have e1 : deriv (fun t => c05_standing_A S.p ε μ t / (Complex.I * (fam_lambda S.p ε μ t : ℂ))) s =
      c * deriv h s := hg.eq_of_nhds
  have e2 : deriv (deriv (fun t => c05_standing_A S.p ε μ t /
      (Complex.I * (fam_lambda S.p ε μ t : ℂ)))) s = c * deriv (deriv h) s := by
    rw [hg.deriv_eq, deriv_const_mul_field']
  have e3 : deriv (fun t => c05_standing_A_zero S.p μ t / (Complex.I * (lambda0 S.p t : ℂ))) s =
      c * deriv h0 s := hg0.eq_of_nhds
  have e4 : deriv (deriv (fun t => c05_standing_A_zero S.p μ t /
      (Complex.I * (lambda0 S.p t : ℂ)))) s = c * deriv (deriv h0) s := by
    rw [hg0.deriv_eq, deriv_const_mul_field']
  -- the `c04` bounds
  have hl0f : (fun t => astar S.p t * ((fam_lambda S.p 0 μ t ^ (-q₁) : ℝ) : ℂ)) = h0 := by
    funext t; simp only [hh0]; rw [c05_aux_lambda_zero]; rfl
  have B1 := (HZ1 R hRZR ε hεZ μ hμ s hs).2.2.2
  have B2 := (HZ2 R hRZR ε hεZ μ hμ s hs).2.2.2
  have B01 := (HZ1 R hRZR 0 h0Z μ hμ s hs).2.2.2
  have B02 := (HZ2 R hRZR 0 h0Z μ hμ s hs).2.2.2
  rw [hl0f] at B01 B02
  have D0 := (HD0 R hRDR ε hεD μ hμ s hs).2.1
  have D1 := (HD1 R hRDR ε hεD μ hμ s hs).2.1
  simp only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_zero, sub_zero] at B1 B2 B01 B02 D0 D1
  have hdh1 := hdiff hhs s hsU
  have hdh01 := hdiff hh0s s hsU
  have ed0 : deriv (fun t => h t - h0 t) s = deriv h s - deriv h0 s := deriv_sub hdh1 hdh01
  have ed1 : deriv (deriv (fun t => h t - h0 t)) s = deriv (deriv h) s - deriv (deriv h0) s := by
    have : deriv (fun t => h t - h0 t) =ᶠ[nhds s] fun t => deriv h t - deriv h0 t :=
      Filter.eventuallyEq_of_mem (hUo.mem_nhds hsU) fun t ht' =>
        deriv_sub (hdiff hhs t ht') (hdiff hh0s t ht')
    rw [this.deriv_eq]; exact deriv_sub (hdiff hdh s hsU) (hdiff hdh0 s hsU)
  have D0' : ‖deriv h s - deriv h0 s‖ ≤ CD0 * ε * s ^ (-q₁ / S.p - S.p - 2) := by
    rw [← ed0]; exact D0
  have D1' : ‖deriv (deriv h) s - deriv (deriv h0) s‖ ≤ CD1 * ε * s ^ (-q₁ / S.p - S.p - 2 - 1) := by
    rw [← ed1]; exact D1
  set X := s ^ (-beta S.p - 1 / S.p - 1) with hX
  set e := ε * s ^ (-S.p - 1) with he
  set σ := s ^ (-1 : ℝ) with hσ
  have hX0 : 0 ≤ X := (Real.rpow_pos_of_pos hs0 _).le
  have he0 : 0 ≤ e := mul_nonneg hε0 (Real.rpow_pos_of_pos hs0 _).le
  have hσ0 : 0 ≤ σ := (Real.rpow_pos_of_pos hs0 _).le
  have x1 : s ^ (-q₁ / S.p - 1) = X := by rw [hqβ]
  have x2 : s ^ (-q₁ / S.p - 2) = X * σ := by
    rw [hX, hσ, ← Real.rpow_add hs0, hqβ]; congr 1; ring
  have x3 : ε * s ^ (-q₁ / S.p - S.p - 2) = e * X := by
    rw [he, hX, mul_assoc, ← Real.rpow_add hs0, hqβ]; congr 2; ring
  have x4 : ε * s ^ (-q₁ / S.p - S.p - 2 - 1) = e * X * σ := by
    rw [he, hX, hσ, mul_assoc, mul_assoc, ← Real.rpow_add hs0, ← Real.rpow_add hs0, hqβ]; congr 2; ring
  rw [x1] at B1 B01
  rw [x2] at B2 B02
  rw [mul_assoc, x3] at D0'
  rw [mul_assoc, x4] at D1'
  obtain ⟨hK1, hK2, hK3, hK4, hK5, hK6, hK7⟩ := hKa
  have hPB : c05_aux_PB (c * deriv h s) (c * deriv (deriv h) s) (c * deriv h0 s)
      (c * deriv (deriv h0) s) K X e σ := by
    refine ⟨c05_aux_cmul_le hcn B1 hK1 hX0, ?_, c05_aux_cmul_le hcn B01 hK1 hX0, ?_, ?_, ?_⟩
    · exact (c05_aux_cmul_le hcn B2 hK2 (mul_nonneg hX0 hσ0)).trans_eq (by ring)
    · exact (c05_aux_cmul_le hcn B02 hK2 (mul_nonneg hX0 hσ0)).trans_eq (by ring)
    · rw [← mul_sub]; exact (c05_aux_cmul_le hcn D0' hK3 (mul_nonneg he0 hX0)).trans_eq (by ring)
    · rw [← mul_sub]
      exact (c05_aux_cmul_le hcn D1' hK4 (by positivity)).trans_eq (by ring)
  rw [e1, e2, e3, e4]
  refine ⟨hPB, ?_⟩
  -- the `λ` data
  obtain ⟨⟨hl1, hl2, -, hdl0, -⟩, -, -, -, h5, -⟩ := hsy0 ε μ R Y hts s hs
  obtain ⟨⟨-, -, hlk1, hdl1, -⟩, -⟩ := hsy1 ε μ R Y hts s hs
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one, sub_zero]
    at hdl0 hlk1 hdl1
  have hlamd : DifferentiableAt ℝ (fam_lambda S.p ε μ) s :=
    (c05_aux_lambda_smooth S.p ε μ (n := 1) hs0).differentiableAt one_ne_zero
  have hlam0 := c05_aux_lambda0_hasDeriv S.p hs0
  rw [deriv_fun_sub hlamd hlam0.differentiableAt] at hdl1
  have y1 : s ^ (1 / S.p - 1) = s ^ (1 / S.p) * σ := by rw [hσ, ← Real.rpow_add hs0]; congr 1
  have y2 : ε * s ^ (1 / S.p - S.p - 1) = e * s ^ (1 / S.p) := by
    rw [he, mul_assoc, ← Real.rpow_add hs0]; congr 2; ring
  have y3 : ε * s ^ (1 / S.p - S.p - 1 - 1) = e * s ^ (1 / S.p) * σ := by
    rw [he, hσ, mul_assoc, mul_assoc, ← Real.rpow_add hs0, ← Real.rpow_add hs0]; congr 2; ring
  have hL0 : 0 ≤ s ^ (1 / S.p) := (Real.rpow_pos_of_pos hs0 _).le
  have hip2 : 1 / S.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  refine ⟨hl1, hl2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [y1] at hlk1; refine hlk1.trans ?_; rw [mul_assoc]; gcongr
  · rw [hlam0.deriv, abs_of_pos (by positivity), y1, mul_assoc]; gcongr; linarith
  · rw [mul_assoc, y2] at hdl0
    refine hdl0.trans ?_
    calc Cs0 * (e * s ^ (1 / S.p)) ≤ K * (e * s ^ (1 / S.p)) :=
          mul_le_mul_of_nonneg_right hK5 (by positivity)
      _ = _ := by ring
  · rw [mul_assoc, y3] at hdl1
    refine hdl1.trans ?_
    calc Cs1 * (e * s ^ (1 / S.p) * σ) ≤ K * (e * s ^ (1 / S.p) * σ) :=
          mul_le_mul_of_nonneg_right hK6 (by positivity)
      _ = _ := by ring
  · rw [c05_aux_exp_phase]
    have : c05_standing_Phi S.p R ε μ s - c05_standing_Phi_zero S.p s =
        fam_Psi S.p R ε μ s - Psi0 S.p s := by
      unfold c05_standing_Phi c05_standing_Phi_zero; ring
    rw [this]; refine h5.trans ?_; gcongr

/-- Helper for lem:c05_fundamental_primitive. -/
theorem c05_aux_pair_exp_bound {u u0 E E0 : ℂ} {K1 K W ε t p : ℝ} (ht : 1 ≤ t) (hp : 0 < p)
    (hE : ‖E‖ = 1) (hK1 : 0 ≤ K1) (hK : 0 ≤ K) (hW : 0 ≤ W) (hε : 0 ≤ ε)
    (h1 : ‖u - u0‖ ≤ K1 * (ε * t ^ (-p - 1)) * W) (h2 : ‖u0‖ ≤ K1 * W)
    (h3 : ‖E - E0‖ ≤ K * ε * t ^ (1 / p - p)) :
    ‖u * E - u0 * E0‖ ≤ K1 * (1 + K) * ε * (W * t ^ (1 / p - p)) := by
  have hm : t ^ (-p - 1) ≤ t ^ (1 / p - p) :=
    Real.rpow_le_rpow_of_exponent_le ht (by have := one_div_pos.mpr hp; linarith)
  have h0 : 0 ≤ t ^ (-p - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h4 : 0 ≤ t ^ (1 / p - p) := (Real.rpow_pos_of_pos (by linarith) _).le
  refine (c05_aux_exp_diff u u0 E E0 hE).trans ?_
  calc ‖u - u0‖ + ‖u0‖ * ‖E - E0‖ ≤ K1 * (ε * t ^ (-p - 1)) * W + (K1 * W) * (K * ε * t ^ (1 / p - p)) :=
        add_le_add h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
    _ ≤ K1 * (ε * t ^ (1 / p - p)) * W + (K1 * W) * (K * ε * t ^ (1 / p - p)) := by gcongr
    _ = _ := by ring

/-- Blueprint: lem:c05_fundamental_primitive.  For `y ≥ 2R`,
`f_{osc,1} = -2 Re[i(Z/λ - (μ/μ_*)Z₀/λ₀)] + ℛ_prim`; `ℛ_prim ∈ C¹([R,∞))` with the stated
derivative, `|ℛ_prim| ≤ Cεy^{-p-3β}`, `|ℛ_prim'| ≤ Cεy^{-p-3β+1/p}` on `[R,∞)`. -/
theorem c05_fundamental_primitive (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        let F : ℝ → ℂ := fun s =>
          Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ s : ℂ)) *
              deriv (fun t => c05_standing_A S.p ε μ t / (Complex.I * (fam_lambda S.p ε μ t : ℂ))) s -
            Complex.exp (Complex.I * (c05_standing_Phi_zero S.p s : ℂ)) *
              deriv (fun t => c05_standing_A_zero S.p μ t / (Complex.I * (lambda0 S.p t : ℂ))) s
        (∀ y, 2 * R ≤ y →
          c05_E5_remainders_fosc1 S.p R ε μ y =
            -2 * (Complex.I * (fam_Z S.p R ε μ y / (fam_lambda S.p ε μ y : ℂ) -
                c05_standing_Zmu0 S.p R μ y / (lambda0 S.p y : ℂ))).re +
              c05_auxiliary_remainders_Rprim S.p R ε μ y) ∧
        ContDiffOn ℝ 1 (c05_auxiliary_remainders_Rprim S.p R ε μ) (Ici R) ∧
        (∀ y ∈ Ici R, HasDerivWithinAt (c05_auxiliary_remainders_Rprim S.p R ε μ)
          (-2 * (F y).re) (Ici R) y) ∧
        ∀ y, R ≤ y →
          |c05_auxiliary_remainders_Rprim S.p R ε μ y| ≤ C * ε * y ^ (-S.p - 3 * beta S.p) ∧
            |-2 * (F y).re| ≤ C * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have h2β : 2 * beta S.p = 1 + 1 / S.p := c05_aux_two_beta S.p hp0
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rd, hRd, K, hK, hdat⟩ := c05_aux_fp_data S
  set Kb : ℝ := 4 * K * (2 + 4 * K + 64 * K ^ 2) with hKb
  have hKb0 : 0 ≤ Kb := by positivity
  set a3 : ℝ := S.p + 3 * beta S.p with ha3
  have ha30 : 0 < a3 := by rw [ha3]; linarith
  refine ⟨max Rp Rd, hRp.trans (le_max_left _ _),
    2 * (K * (1 + K)) + 2 * (Kb * (1 + K) + Kb * (1 + K) / a3) + 1, by positivity, ?_⟩
  intro ε μ R Y ht F
  have htp := c05_aux_tuple_mono (le_max_left Rp Rd) ht
  have htd := c05_aux_tuple_mono (le_max_right Rp Rd) ht
  have hR : 1 ≤ R := hRp.trans htp.2.2.2.1
  have hR0 : 0 < R := by linarith
  have hε0 : 0 ≤ ε := ht.1
  obtain ⟨hqs, hq0s, hpos, hpt⟩ := hdat ε μ R Y htd
  set q : ℝ → ℂ := fun t => c05_standing_A S.p ε μ t / (Complex.I * (fam_lambda S.p ε μ t : ℂ))
    with hq
  set q0 : ℝ → ℂ := fun t => c05_standing_A_zero S.p μ t / (Complex.I * (lambda0 S.p t : ℂ))
    with hq0
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) with hE
  set E0 : ℝ → ℂ := fun t => Complex.exp (Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) with hE0
  have hFdef : ∀ s, F s = E s * deriv q s - E0 s * deriv q0 s := fun s => rfl
  have hEn : ∀ t, ‖E t‖ = 1 := fun t => by
    simp only [hE]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hE0n : ∀ t, ‖E0 t‖ = 1 := fun t => by
    simp only [hE0]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  set U : Set ℝ := Ioi (R / 2) with hU
  have hU0 : ∀ t ∈ U, 0 < t := fun t ht' => lt_trans (half_pos hR0) ht'
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (deriv q) U := hqs.deriv_of_isOpen isOpen_Ioi (m := (⊤ : ℕ∞)) (by simp)
  have hg0 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv q0) U :=
    hq0s.deriv_of_isOpen isOpen_Ioi (m := (⊤ : ℕ∞)) (by simp)
  have hΦd : ∀ t, 0 < t → HasDerivAt (c05_standing_Phi S.p R ε μ) (fam_lambda S.p ε μ t) t :=
    fun t ht' => (c05_aux_Psi_hasDeriv S.p R ε μ hR0 ht').sub_const (π / 4)
  have hΦ0d : ∀ t, 0 < t → HasDerivAt (c05_standing_Phi_zero S.p) (lambda0 S.p t) t :=
    fun t ht' => c05_aux_Phi0_hasDeriv S.p hp0 ht'
  have hexpc : ∀ (φ : ℝ → ℝ) (t : ℝ), ContinuousAt φ t →
      ContinuousAt (fun t => Complex.exp (Complex.I * (φ t : ℂ))) t := fun φ t h =>
    Complex.continuous_exp.continuousAt.comp
      ((continuous_const.mul Complex.continuous_ofReal).continuousAt.comp h)
  have hEc : ContinuousOn E U := fun t ht' =>
    (hexpc _ t (hΦd t (hU0 t ht')).continuousAt).continuousWithinAt
  have hE0c : ContinuousOn E0 U := fun t ht' =>
    (hexpc _ t (hΦ0d t (hU0 t ht')).continuousAt).continuousWithinAt
  have hFc : ContinuousOn F U := (hEc.mul hg.continuousOn).sub (hE0c.mul hg0.continuousOn)
  have hdiff : ∀ {f : ℝ → ℂ}, ContDiffOn ℝ (⊤ : ℕ∞) f U → ∀ t ∈ U, DifferentiableAt ℝ f t :=
    fun hf t ht' => (hf.contDiffAt (isOpen_Ioi.mem_nhds ht')).differentiableAt (by simp)
  have hIdiv : ∀ w x : ℂ, w / (Complex.I * x) = -(Complex.I * (w / x)) := by
    intro w x; rw [mul_comm Complex.I x, ← div_div, Complex.div_I]; ring
  -- integrability of `F`
  have hFi : IntegrableOn F (Ioi R) := by
    obtain ⟨⟨-, -, hEgi, -⟩, ⟨-, -, hE0gi, -⟩⟩ := hprim ε μ R Y htp R le_rfl
    exact hEgi.sub hE0gi
  set R' := 3 * R / 4 with hR'
  have hR'R : R' < R := by rw [hR']; linarith
  have hR'U : Ioi R' ⊆ U := Ioi_subset_Ioi (by rw [hR']; linarith)
  have hFi' : IntegrableOn F (Ioi R') := by
    rw [← Ioc_union_Ioi_eq_Ioi hR'R.le]
    refine IntegrableOn.union ?_ hFi
    have : ContinuousOn F (Icc R' R) := hFc.mono fun t ht' => by
      show R / 2 < t
      have := ht'.1; linarith
    exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  -- pointwise estimates
  have hP : ∀ t, R ≤ t →
      HasDerivAt (fun s => deriv q s / (Complex.I * (fam_lambda S.p ε μ s : ℂ)))
        (deriv (deriv q) t * (Complex.I * (fam_lambda S.p ε μ t : ℂ))⁻¹ + deriv q t *
          (-(Complex.I * ((deriv (fam_lambda S.p ε μ) t : ℝ) : ℂ)) / (Complex.I * (fam_lambda S.p ε μ t : ℂ)) ^ 2)) t ∧
      HasDerivAt (fun s => deriv q0 s / (Complex.I * (lambda0 S.p s : ℂ)))
        (deriv (deriv q0) t * (Complex.I * (lambda0 S.p t : ℂ))⁻¹ + deriv q0 t *
          (-(Complex.I * ((deriv (lambda0 S.p) t : ℝ) : ℂ)) / (Complex.I * (lambda0 S.p t : ℂ)) ^ 2)) t ∧
      ‖F t‖ ≤ K * (1 + K) * ε * t ^ (-S.p - 3 * beta S.p + 1 / S.p) ∧
      ‖deriv q t / (Complex.I * (fam_lambda S.p ε μ t : ℂ)) * E t -
          deriv q0 t / (Complex.I * (lambda0 S.p t : ℂ)) * E0 t‖ ≤
        Kb * (1 + K) * ε * t ^ (-S.p - 3 * beta S.p) ∧
      ‖E t * deriv (fun s => deriv q s / (Complex.I * (fam_lambda S.p ε μ s : ℂ))) t -
          E0 t * deriv (fun s => deriv q0 s / (Complex.I * (lambda0 S.p s : ℂ))) t‖ ≤
        Kb * (1 + K) * ε * t ^ (-S.p - 3 * beta S.p - 1) := by
    intro t ht
    have ht1 : 1 ≤ t := hR.trans ht
    have ht0 : 0 < t := by linarith
    have htU : t ∈ U := show R / 2 < t by linarith
    obtain ⟨PBg, hl1, hl2, hld, hl0d, hdl, hdl', hph⟩ := hpt t ht
    have hL : 0 < t ^ (1 / S.p) := Real.rpow_pos_of_pos ht0 _
    have hX0 : 0 ≤ t ^ (-beta S.p - 1 / S.p - 1) := (Real.rpow_pos_of_pos ht0 _).le
    have he0 : 0 ≤ ε * t ^ (-S.p - 1) := mul_nonneg hε0 (Real.rpow_pos_of_pos ht0 _).le
    have hσ0 : 0 ≤ t ^ (-1 : ℝ) := (Real.rpow_pos_of_pos ht0 _).le
    have hl0e : lambda0 S.p t = t ^ (1 / S.p) := rfl
    have PBi := c05_aux_PB_inv (l0 := lambda0 S.p t) hL hK.le he0 hσ0 hl1 hl2
      (by rw [hl0e]; linarith) (by rw [hl0e]; linarith) hld hl0d hdl hdl'
    have PBb := c05_aux_PB_mul PBg PBi hK.le (by positivity) hX0 (inv_nonneg.mpr hL.le) he0 hσ0
    have hlpos : 0 < fam_lambda S.p ε μ t := hpos t htU
    have hl0pos : 0 < lambda0 S.p t := by rw [hl0e]; exact hL
    have hbd : HasDerivAt (fun s => deriv q s / (Complex.I * (fam_lambda S.p ε μ s : ℂ)))
        (deriv (deriv q) t * (Complex.I * (fam_lambda S.p ε μ t : ℂ))⁻¹ + deriv q t *
          (-(Complex.I * ((deriv (fam_lambda S.p ε μ) t : ℝ) : ℂ)) /
            (Complex.I * (fam_lambda S.p ε μ t : ℂ)) ^ 2)) t := by
      have h1 : HasDerivAt (deriv q) (deriv (deriv q) t) t := (hdiff hg t htU).hasDerivAt
      have h2 : HasDerivAt (fun s => Complex.I * (fam_lambda S.p ε μ s : ℂ))
          (Complex.I * ((deriv (fam_lambda S.p ε μ) t : ℝ) : ℂ)) t :=
        ((c05_aux_lambda_smooth S.p ε μ (n := 1) ht0).differentiableAt
          one_ne_zero).hasDerivAt.ofReal_comp.const_mul Complex.I
      have h3 := h2.inv (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hlpos.ne'))
      have : (fun s => deriv q s / (Complex.I * (fam_lambda S.p ε μ s : ℂ))) =
          fun s => deriv q s * (Complex.I * (fam_lambda S.p ε μ s : ℂ))⁻¹ :=
        funext fun s => div_eq_mul_inv _ _
      rw [this]; exact h1.mul h3
    have hb0d : HasDerivAt (fun s => deriv q0 s / (Complex.I * (lambda0 S.p s : ℂ)))
        (deriv (deriv q0) t * (Complex.I * (lambda0 S.p t : ℂ))⁻¹ + deriv q0 t *
          (-(Complex.I * ((deriv (lambda0 S.p) t : ℝ) : ℂ)) / (Complex.I * (lambda0 S.p t : ℂ)) ^ 2)) t := by
      have h1 : HasDerivAt (deriv q0) (deriv (deriv q0) t) t := (hdiff hg0 t htU).hasDerivAt
      have h2 : HasDerivAt (fun s => Complex.I * (lambda0 S.p s : ℂ))
          (Complex.I * ((deriv (lambda0 S.p) t : ℝ) : ℂ)) t :=
        (c05_aux_lambda0_hasDeriv S.p ht0).differentiableAt.hasDerivAt.ofReal_comp.const_mul Complex.I
      have h3 := h2.inv (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hl0pos.ne'))
      have : (fun s => deriv q0 s / (Complex.I * (lambda0 S.p s : ℂ))) =
          fun s => deriv q0 s * (Complex.I * (lambda0 S.p s : ℂ))⁻¹ :=
        funext fun s => div_eq_mul_inv _ _
      rw [this]; exact h1.mul h3
    have i1 : t ^ (-beta S.p - 1 / S.p - 1) * t ^ (1 / S.p - S.p) =
        t ^ (-S.p - 3 * beta S.p + 1 / S.p) := by
      rw [← Real.rpow_add ht0]; congr 1; linarith
    have i2 : t ^ (-beta S.p - 1 / S.p - 1) * (t ^ (1 / S.p))⁻¹ * t ^ (1 / S.p - S.p) =
        t ^ (-S.p - 3 * beta S.p) := by
      rw [← Real.rpow_neg ht0.le, ← Real.rpow_add ht0, ← Real.rpow_add ht0]; congr 1; linarith
    have i3 : t ^ (-beta S.p - 1 / S.p - 1) * (t ^ (1 / S.p))⁻¹ * t ^ (-1 : ℝ) * t ^ (1 / S.p - S.p) =
        t ^ (-S.p - 3 * beta S.p - 1) := by
      rw [← Real.rpow_neg ht0.le, ← Real.rpow_add ht0, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
      congr 1; linarith
    have hW2 : 0 ≤ t ^ (-beta S.p - 1 / S.p - 1) * (t ^ (1 / S.p))⁻¹ := by positivity
    refine ⟨hbd, hb0d, ?_, ?_, ?_⟩
    · rw [hFdef, mul_comm (E t), mul_comm (E0 t)]
      exact (c05_aux_pair_exp_bound ht1 hp0 (hEn t) hK.le hK.le hX0 hε0 PBg.2.2.2.2.1 PBg.2.2.1
        hph).trans_eq (by rw [i1])
    · rw [div_eq_mul_inv, div_eq_mul_inv]
      exact (c05_aux_pair_exp_bound (K1 := Kb) ht1 hp0 (hEn t) hKb0 hK.le hW2 hε0
        (PBb.2.2.2.2.1.trans_eq (by rw [hKb])) (PBb.2.2.1.trans_eq (by rw [hKb])) hph).trans_eq
        (by rw [i2])
    · rw [hbd.deriv, hb0d.deriv, mul_comm (E t), mul_comm (E0 t)]
      exact (c05_aux_pair_exp_bound (K1 := Kb)
        (W := t ^ (-beta S.p - 1 / S.p - 1) * (t ^ (1 / S.p))⁻¹ * t ^ (-1 : ℝ))
        ht1 hp0 (hEn t) hKb0 hK.le (by positivity) hε0
        (PBb.2.2.2.2.2.trans_eq (by rw [hKb]; ring)) (PBb.2.2.2.1.trans_eq (by rw [hKb]; ring))
        hph).trans_eq (by rw [i3])
  -- the derivative of `ℛ_prim`
  have hFc' : ContinuousOn F (Ioi R') := hFc.mono hR'U
  have hTd : ∀ y, R' < y → HasDerivAt (fun w => ∫ t in Ioi w, F t) (-F y) y := fun y hy =>
    c05_aux_tail_hasDeriv F R' hFi' hFc' hy
  have hRpeq : c05_auxiliary_remainders_Rprim S.p R ε μ = fun y => 2 * (∫ t in Ioi y, F t).re := rfl
  have hRd : ∀ y, R' < y →
      HasDerivAt (c05_auxiliary_remainders_Rprim S.p R ε μ) (-2 * (F y).re) y := by
    intro y hy
    rw [hRpeq]
    have := (c05_aux_hasDerivAt_re (hTd y hy)).const_mul 2
    convert this using 1
    rw [Complex.neg_re]; ring
  have hCs : 0 ≤ K * (1 + K) := by positivity
  have hCb : 0 ≤ Kb * (1 + K) := by positivity
  refine ⟨fun y hy => ?_, ?_, fun y hy => (hRd y (lt_of_lt_of_le hR'R hy)).hasDerivWithinAt,
    fun y hy => ⟨?_, ?_⟩⟩
  · -- the identity
    have hRy : R < y := by linarith
    obtain ⟨⟨hZi, -, hEgi, -, hZid, -⟩, ⟨hZ0i, -, hE0gi, -, hZ0id, -⟩⟩ :=
      hprim ε μ R Y htp y (by linarith)
    unfold c05_E5_remainders_fosc1 c05_auxiliary_remainders_Rprim
    rw [if_pos hRy, c04_aux_chiR_one R y hR0 hy, integral_sub hZi hZ0i, hZid, hZ0id,
      integral_sub hEgi hE0gi, hIdiv, hIdiv]
    simp only [neg_neg, Complex.sub_re, mul_sub]
    ring
  · -- `C¹` on `[R, ∞)`
    have h1 : ContDiffOn ℝ (0 + 1) (c05_auxiliary_remainders_Rprim S.p R ε μ) (Ioi R') := by
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun y hy => (hRd y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      rw [contDiffOn_zero]
      refine ContinuousOn.congr (f := fun y => -2 * (F y).re) ?_ (fun y hy => (hRd y hy).deriv)
      exact continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hFc')
    rw [zero_add] at h1
    exact h1.mono fun y hy => lt_of_lt_of_le hR'R hy
  · -- the bound on `ℛ_prim`
    have hy1 : 1 ≤ y := hR.trans hy
    have hy0 : 0 < y := by linarith
    obtain ⟨⟨-, -, hEgi, -⟩, ⟨-, -, hE0gi, -⟩⟩ := hprim ε μ R Y htp y hy
    have er : -(beta S.p + 1 / S.p + 1) = -beta S.p - 1 / S.p - 1 := by ring
    have er1 : ∀ t : ℝ, 0 < t → t ^ (-beta S.p - 1 / S.p - 1) * t ^ (-1 : ℝ) =
        t ^ (-(beta S.p + 1 / S.p + 1) - 1) := fun t ht' => by
      rw [← Real.rpow_add ht']; congr 1; ring
    have er2 : ∀ t : ℝ, 0 < t → t ^ (1 / S.p) * t ^ (-1 : ℝ) = t ^ (1 / S.p - 1) := fun t ht' => by
      rw [← Real.rpow_add ht']; congr 1
    have hr1 : 1 < beta S.p + 1 / S.p + 1 := by linarith
    obtain ⟨-, Gi, Geq, -⟩ := c05_aux_prim_generic (B := deriv q) (l := fam_lambda S.p ε μ)
      (Φ := c05_standing_Phi S.p R ε μ) (c := Complex.I) (z := y) (p := S.p) (K := K)
      (r := beta S.p + 1 / S.p + 1) (by simp) (by simp) hy0 hK.le hr1 hp0
      (fun t ht => (hdiff hg t (show R / 2 < t by linarith)).hasDerivAt)
      (fun t ht => ((c05_aux_lambda_smooth S.p ε μ (n := 1) (by linarith : (0 : ℝ) < t)).differentiableAt
        one_ne_zero).hasDerivAt)
      (fun t ht => hΦd t (by linarith)) (fun t ht => (hpt t (hy.trans ht)).2.1)
      (fun t ht => by rw [er]; exact (hpt t (hy.trans ht)).1.1)
      (fun t ht => by rw [← er1 t (by linarith), ← mul_assoc]; exact (hpt t (hy.trans ht)).1.2.1)
      (fun t ht => by rw [← er2 t (by linarith), ← mul_assoc]; exact (hpt t (hy.trans ht)).2.2.2.1)
    obtain ⟨-, G0i, G0eq, -⟩ := c05_aux_prim_generic (B := deriv q0) (l := lambda0 S.p)
      (Φ := c05_standing_Phi_zero S.p) (c := Complex.I) (z := y) (p := S.p) (K := K)
      (r := beta S.p + 1 / S.p + 1) (by simp) (by simp) hy0 hK.le hr1 hp0
      (fun t ht => (hdiff hg0 t (show R / 2 < t by linarith)).hasDerivAt)
      (fun t ht => (c05_aux_lambda0_hasDeriv S.p (by linarith : (0 : ℝ) < t)).differentiableAt.hasDerivAt)
      (fun t ht => hΦ0d t (by linarith))
      (fun t ht => by
        show t ^ (1 / S.p) / 2 ≤ t ^ (1 / S.p)
        have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < t) (1 / S.p); linarith)
      (fun t ht => by rw [er]; exact (hpt t (hy.trans ht)).1.2.2.1)
      (fun t ht => by rw [← er1 t (by linarith), ← mul_assoc]; exact (hpt t (hy.trans ht)).1.2.2.2.1)
      (fun t ht => by rw [← er2 t (by linarith), ← mul_assoc]; exact (hpt t (hy.trans ht)).2.2.2.2.1)
    have hc1 : ∫ t in Ioi y, E t * deriv q t = ∫ t in Ioi y, deriv q t *
        Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => mul_comm _ _)
    have hc0 : ∫ t in Ioi y, E0 t * deriv q0 t = ∫ t in Ioi y, deriv q0 t *
        Complex.exp (Complex.I * (c05_standing_Phi_zero S.p t : ℂ)) := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => mul_comm _ _)
    have hIF : ∫ t in Ioi y, F t =
        -(deriv q y / (Complex.I * (fam_lambda S.p ε μ y : ℂ)) * E y -
          deriv q0 y / (Complex.I * (lambda0 S.p y : ℂ)) * E0 y) -
        ∫ t in Ioi y, (E t * deriv (fun s => deriv q s / (Complex.I * (fam_lambda S.p ε μ s : ℂ))) t -
          E0 t * deriv (fun s => deriv q0 s / (Complex.I * (lambda0 S.p s : ℂ))) t) := by
      rw [show (∫ t in Ioi y, F t) = (∫ t in Ioi y, E t * deriv q t) -
          ∫ t in Ioi y, E0 t * deriv q0 t from integral_sub hEgi hE0gi, hc1, hc0, Geq, G0eq,
        integral_sub Gi G0i]
      ring
    obtain ⟨hmi, hmint⟩ := c05_aux_int_Ioi_rpow (Kb * (1 + K) * ε) (-S.p - 3 * beta S.p - 1) y
      (by linarith) hy0
    have hint : ‖∫ t in Ioi y, (E t * deriv (fun s => deriv q s /
          (Complex.I * (fam_lambda S.p ε μ s : ℂ))) t -
        E0 t * deriv (fun s => deriv q0 s / (Complex.I * (lambda0 S.p s : ℂ))) t)‖ ≤
        Kb * (1 + K) * ε * (y ^ (-S.p - 3 * beta S.p) / a3) := by
      refine (norm_integral_le_of_norm_le hmi ?_).trans (le_of_eq ?_)
      · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
        exact (hP t (hy.trans (le_of_lt ht))).2.2.2.2
      · rw [hmint, show -S.p - 3 * beta S.p - 1 + 1 = -a3 by rw [ha3]; ring]
        rw [neg_div, div_neg, neg_neg, ha3]; ring_nf
    have hbd := (hP y hy).2.2.2.1
    have hYa : 0 ≤ y ^ (-S.p - 3 * beta S.p) := (Real.rpow_pos_of_pos hy0 _).le
    calc |c05_auxiliary_remainders_Rprim S.p R ε μ y| = |2 * (∫ t in Ioi y, F t).re| := rfl
      _ ≤ 2 * ‖∫ t in Ioi y, F t‖ := by
          rw [abs_mul, abs_two]; gcongr; exact Complex.abs_re_le_norm _
      _ ≤ 2 * (Kb * (1 + K) * ε * y ^ (-S.p - 3 * beta S.p) +
            Kb * (1 + K) * ε * (y ^ (-S.p - 3 * beta S.p) / a3)) := by
          gcongr
          rw [hIF]
          refine (norm_sub_le _ _).trans (add_le_add ?_ hint)
          rw [norm_neg]; exact hbd
      _ = (2 * (Kb * (1 + K) + Kb * (1 + K) / a3)) * ε * y ^ (-S.p - 3 * beta S.p) := by ring
      _ ≤ _ := by
          gcongr
          linarith
  · -- the bound on `ℛ_prim'`
    have hF := (hP y hy).2.2.1
    have hYa : 0 ≤ y ^ (-S.p - 3 * beta S.p + 1 / S.p) := (Real.rpow_pos_of_pos (by linarith) _).le
    have h2 : 0 ≤ 2 * (Kb * (1 + K) + Kb * (1 + K) / a3) := by positivity
    calc |-2 * (F y).re| ≤ 2 * ‖F y‖ := by
          rw [abs_mul, abs_neg, abs_two]; gcongr; exact Complex.abs_re_le_norm _
      _ ≤ 2 * (K * (1 + K) * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p)) := by gcongr
      _ = (2 * (K * (1 + K))) * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) := by ring
      _ ≤ _ := by gcongr; linarith

/-- Blueprint: lem:c05_fundamental_identity.  On `(Y/2,3Y)`:
`ℛ_{lin,1} = 2Re[T₁ + T₂] + 2Re(ℰ_mult - ℰ_{mult,0}) + ℛ_prim + ℛ_{far,Y}[f_{osc,1}]`, where
`T₁ = i((λ^p)'-1)Z/λ`, `T₂ = -ipμa_*'(λ^{(p-3)/2}e^{iΦ} - λ₀^{(p-3)/2}e^{iΦ₀})`. -/
theorem c05_fundamental_identity (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ∀ y ∈ Ioo (Y / 2) (3 * Y),
        c05_E5_remainders_Rlin1 S.p R ε μ y =
          2 * (c05_fundamental_explicit_T1 S.p R ε μ y + c05_fundamental_explicit_T2 S.p R ε μ y).re +
            2 * (c05_auxiliary_remainders_Emult S.p R ε μ Y y -
              c05_auxiliary_remainders_Emult0 S.p R μ Y y).re +
            c05_auxiliary_remainders_Rprim S.p R ε μ y +
            c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc1 S.p R ε μ) y := by
  obtain ⟨Ra, hRa, Ca, hCa, hosc⟩ := c05_osc_split_bounds S
  obtain ⟨Rb, hRb, Cb, hCb, hfar⟩ := c05_far_localization S
  obtain ⟨Rc, hRc, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Rd, hRd, Cd, hCd, hprim⟩ := c05_fundamental_primitive S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  set R₀ := max (max Ra Rb) (max Rc Rd) with hR₀
  refine ⟨R₀, hRa.trans (by simp [hR₀]), ?_⟩
  intro ε μ R Y ht t htI
  have hta := c05_aux_tuple_mono (show Ra ≤ R₀ by simp [hR₀]) ht
  have htb := c05_aux_tuple_mono (show Rb ≤ R₀ by simp [hR₀]) ht
  have htc := c05_aux_tuple_mono (show Rc ≤ R₀ by simp [hR₀]) ht
  have htd := c05_aux_tuple_mono (show Rd ≤ R₀ by simp [hR₀]) ht
  have hR : 1 ≤ R := hRc.trans htc.2.2.2.1
  have hY8 : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsym0 ε μ R Y htc t ht'.le).1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  obtain ⟨hs1, -, hz, ⟨M, hM⟩, -, hder, -, hi1, -, -⟩ := hosc ε μ R Y hta
  obtain ⟨hid, -, -, -⟩ := hfar ε μ R Y htb _ hs1 ⟨M, fun x => ⟨(hM x).1, (hM x).2.1⟩⟩ hi1
    (fun x hx => (hz x hx).1)
  obtain ⟨hpid, -, -, -⟩ := hprim ε μ R Y htd
  have hRY : R < 3 * Y / 10 := by linarith
  obtain ⟨hcZ, hsZ⟩ := c05_aux_cutoff_mul (n := 1) (f := fam_Z S.p R ε μ) hY0 hRY
    (fun t ht' => ((c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos ht').2.1).of_le
      (by norm_num))
  obtain ⟨hcZ0, hsZ0⟩ := c05_aux_cutoff_mul (n := 1) (f := c05_standing_Zmu0 S.p R μ) hY0 hRY
    (fun t ht' => ((c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos
      ht').2.2.1).of_le (by norm_num))
  set g1 : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z with hg1
  set g0 : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_Zmu0 S.p R μ z with hg0
  have hb1 : ∃ M : ℝ, ∀ x, ‖g1 x‖ ≤ M := hcZ.continuous.bounded_above_of_compact_support hsZ
  have hb0 : ∃ M : ℝ, ∀ x, ‖g0 x‖ ≤ M := hcZ0.continuous.bounded_above_of_compact_support hsZ0
  set h : ℝ → ℂ := fun z => ((2 : ℝ) : ℂ) * (g1 z - g0 z) with hh
  have hhC : ContDiff ℝ 1 h := contDiff_const.mul (hcZ.sub hcZ0)
  have hhb : ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M :=
    hhC.continuous.bounded_above_of_compact_support ((hsZ.sub hsZ0).mul_left)
  have hfun : (fun z => res_chiY Y z * deriv (c05_E5_remainders_fosc1 S.p R ε μ) z) =
      fun z => (h z).re := by
    funext z
    simp only [hh, hg1, hg0]
    rcases le_or_gt z (3 * Y / 10) with hz' | hz'
    · rw [c05_aux_chiY_zero hY0 (Or.inl hz')]; simp
    · rw [(hder z (by linarith)).1]
      simp [Complex.mul_re, Complex.sub_re]
      ring
  have hfr : fracDdy S.p (c05_E5_remainders_fosc1 S.p R ε μ) t =
      2 * (fracDC S.p g1 t).re - 2 * (fracDC S.p g0 t).re +
        c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc1 S.p R ε μ) t := by
    rw [hid t htI, hfun, c05_aux_fracD_re S.p hp0 S.hp_hi h hhC hhb t, hh,
      c05_aux_fracDC_const_mul, c05_aux_fracDC_sub S.p hp0 S.hp_hi g1 g0 hcZ hcZ0 hb1 hb0,
      Complex.re_ofReal_mul, Complex.sub_re]
    ring
  have htR : 2 * R ≤ t := by linarith [htI.1]
  unfold c05_E5_remainders_Rlin1
  rw [hfr, hpid t htR]
  unfold c05_fundamental_explicit_T1 c05_fundamental_explicit_T2 c05_auxiliary_remainders_Emult
    c05_auxiliary_remainders_Emult0
  rw [← hg1, ← hg0]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
    Complex.sub_im, Complex.div_re, Complex.div_im, Complex.normSq_ofReal]
  have hl : fam_lambda S.p ε μ t ≠ 0 := (hpos t (by linarith)).ne'
  have hl0 : lambda0 S.p t ≠ 0 := by
    unfold lambda0; exact (Real.rpow_pos_of_pos (by linarith) _).ne'
  field_simp
  ring

/-- Helper: `l^r ≤ 2^{-r} y^{r/p}` for `l ≥ y^{1/p}/2`, `r ≤ 0`. -/
theorem c05_aux_lam_rpow_le {l y p r : ℝ} (hy : 0 < y) (hl : y ^ (1 / p) / 2 ≤ l) (hr : r ≤ 0) :
    l ^ r ≤ 2 ^ (-r) * y ^ (r / p) := by
  have h0 : 0 < y ^ (1 / p) / 2 := by positivity
  calc l ^ r ≤ (y ^ (1 / p) / 2) ^ r := Real.rpow_le_rpow_of_nonpos h0 hl hr
    _ = 2 ^ (-r) * y ^ (r / p) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hy.le, Real.rpow_neg (by norm_num)]
      rw [show 1 / p * r = r / p by ring]; field_simp

/-- Helper: `(y^{1/p}/2)^{r} = 2^{-r} y^{r/p}`. -/
theorem c05_aux_half_rpow {y p r : ℝ} (hy : 0 < y) :
    (y ^ (1 / p) / 2) ^ r = 2 ^ (-r) * y ^ (r / p) := by
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hy.le, Real.rpow_neg (by norm_num)]
  rw [show 1 / p * r = r / p by ring]; field_simp

/-- Helper: derivative bound for a product. -/
theorem c05_aux_deriv_mul_le {f g : ℝ → ℂ} {y : ℝ} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) :
    ‖deriv (fun t => f t * g t) y‖ ≤ ‖deriv f y‖ * ‖g y‖ + ‖f y‖ * ‖deriv g y‖ := by
  rw [deriv_fun_mul hf hg]
  calc ‖deriv f y * g y + f y * deriv g y‖ ≤ ‖deriv f y * g y‖ + ‖f y * deriv g y‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_mul]

/-- Helper: `‖a^r e^{iθ} - b^r‖ ≤ a^r |e^{iθ}-1| + |a^r - b^r|`. -/
theorem c05_aux_phase_diff (a b : ℝ) (e : ℂ) :
    ‖(a : ℂ) * e - (b : ℂ)‖ ≤ |a| * ‖e - 1‖ + |a - b| := by
  calc ‖(a : ℂ) * e - (b : ℂ)‖ = ‖(a : ℂ) * (e - 1) + ((a - b : ℝ) : ℂ)‖ := by push_cast; ring_nf
    _ ≤ ‖(a : ℂ) * (e - 1)‖ + ‖((a - b : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |a| * ‖e - 1‖ + |a - b| := by rw [norm_mul, Complex.norm_real, Complex.norm_real]; rfl

/-- Helper: `y^a y^b = y^c` when `a + b = c`, `y > 0`. -/
theorem c05_aux_ymul {y a b c : ℝ} (hy : 0 < y) (h : a + b = c) : y ^ a * y ^ b = y ^ c := by
  rw [← Real.rpow_add hy, h]

/-- Helper: `y^a ≤ y^b` for `y ≥ 1`, `a ≤ b`. -/
theorem c05_aux_ymono {y a b : ℝ} (hy : 1 ≤ y) (h : a ≤ b) : y ^ a ≤ y ^ b :=
  Real.rpow_le_rpow_of_exponent_le hy h

/-- Helper: the phase-difference bound
`‖l^r e^{iθ} - l₀^r‖ ≤ (2^{-r} + |r| 2^{1-r}) C ε y^{(r+1)/p - p}` (`r ≤ 0`). -/
theorem c05_aux_D_bound {y p ε C l l0 r : ℝ} (e : ℂ) (hy : 1 ≤ y) (hp : 0 < p)
    (hl : y ^ (1 / p) / 2 ≤ l) (hl0 : y ^ (1 / p) / 2 ≤ l0) (hr : r ≤ 0) (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hdl : |l - l0| ≤ C * ε * y ^ (1 / p - p - 1))
    (hth : ‖e - 1‖ ≤ C * ε * y ^ (1 / p - p)) :
    ‖((l ^ r : ℝ) : ℂ) * e - ((l0 ^ r : ℝ) : ℂ)‖ ≤
      (2 ^ (-r) + |r| * 2 ^ (1 - r)) * C * ε * y ^ ((r + 1) / p - p) := by
  have hy0 : 0 < y := by linarith
  have hm : 0 < y ^ (1 / p) / 2 := by positivity
  have hlp : 0 < l := lt_of_lt_of_le hm hl
  refine (c05_aux_phase_diff _ _ e).trans ?_
  rw [abs_of_pos (Real.rpow_pos_of_pos hlp r)]
  have h1 : l ^ r * ‖e - 1‖ ≤ 2 ^ (-r) * C * ε * y ^ ((r + 1) / p - p) := by
    calc l ^ r * ‖e - 1‖ ≤ (2 ^ (-r) * y ^ (r / p)) * (C * ε * y ^ (1 / p - p)) :=
          mul_le_mul (c05_aux_lam_rpow_le hy0 hl hr) hth (norm_nonneg _) (by positivity)
      _ = 2 ^ (-r) * C * ε * (y ^ (r / p) * y ^ (1 / p - p)) := by ring
      _ = _ := by rw [c05_aux_ymul hy0 (c := (r + 1) / p - p) (by ring)]
  have h2 : |l ^ r - l0 ^ r| ≤ |r| * 2 ^ (1 - r) * C * ε * y ^ ((r + 1) / p - p) := by
    refine (c05_aux_rpow_sub_le hm hl hl0 (by linarith)).trans ?_
    rw [c05_aux_half_rpow hy0, show -(r - 1) = 1 - r by ring]
    have hexp : (r - 1) / p + (1 / p - p - 1) ≤ (r + 1) / p - p := by
      have : (r - 1) / p + (1 / p - p - 1) = (r + 1) / p - p - 1 - 1 / p := by ring
      have : 0 < 1 / p := by positivity
      linarith
    calc |r| * (2 ^ (1 - r) * y ^ ((r - 1) / p)) * |l - l0| ≤
        |r| * (2 ^ (1 - r) * y ^ ((r - 1) / p)) * (C * ε * y ^ (1 / p - p - 1)) :=
          mul_le_mul_of_nonneg_left hdl (by positivity)
      _ = |r| * 2 ^ (1 - r) * C * ε * (y ^ ((r - 1) / p) * y ^ (1 / p - p - 1)) := by ring
      _ ≤ |r| * 2 ^ (1 - r) * C * ε * y ^ ((r + 1) / p - p) := by
          rw [c05_aux_ymul hy0 rfl]
          exact mul_le_mul_of_nonneg_left (c05_aux_ymono hy hexp) (by positivity)
  calc l ^ r * ‖e - 1‖ + |l ^ r - l0 ^ r| ≤ 2 ^ (-r) * C * ε * y ^ ((r + 1) / p - p) +
      |r| * 2 ^ (1 - r) * C * ε * y ^ ((r + 1) / p - p) := add_le_add h1 h2
    _ = _ := by ring

/-- Blueprint: lem:c05_fundamental_explicit.
`|∂^j T₁(y)| + |∂^j T₂(y)| ≤ C ε y^{-p-3β+j/p}` for `y ≥ R`, `j = 0,1`. -/
theorem c05_fundamental_explicit (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y : ℝ, R ≤ y → ∀ j : ℕ, j ≤ 1 →
          ‖iteratedDeriv j (c05_fundamental_explicit_T1 S.p R ε μ) y‖ +
              ‖iteratedDeriv j (c05_fundamental_explicit_T2 S.p R ε μ) y‖ ≤
            C * ε * y ^ (-S.p - 3 * beta S.p + j / S.p) := by
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C0, hC0, hs0⟩ := hsym 0
  obtain ⟨C1, hC1, hs1⟩ := hsym 1
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hp1 := S.hp_hi
  have hip : 0 < 1 / S.p := by positivity
  have hβ : 3 * beta S.p = beta S.p + 1 + 1 / S.p := by
    have := c05_aux_two_beta S.p hp0; linarith
  set Kμ : ℝ := ‖mu_star S.p‖ + S.δ with hKμ
  have hKμ0 : 0 ≤ Kμ := by have := S.hδ; positivity
  set q : ℝ := (S.p - 3) / 2 with hq
  have hq0 : q ≤ 0 := by rw [hq]; linarith
  have hq1 : q + 1 ≤ 0 := by rw [hq]; linarith
  have hqm : q - 1 ≤ 0 := by linarith
  have hqexp : -2 * beta S.p - 1 + ((q + 1) / S.p - S.p) = -S.p - 3 * beta S.p := by
    rw [hq]; unfold beta; field_simp; ring
  set KD : ℝ := (2 ^ (-q) + |q| * 2 ^ (1 - q)) * C0 with hKD
  set KD1 : ℝ := (2 ^ (-(q + 1)) + |q + 1| * 2 ^ (1 - (q + 1))) * C0 with hKD1
  set KF : ℝ := 2 ^ (1 - q) * C1 * C0 + |q - 1| * 2 ^ (1 - (q - 1)) * C0 * C1 + C1 with hKF
  set KDd : ℝ := |q| * KF + KD1 with hKDd
  set KT1 : ℝ := 2 * C0 ^ 2 + C0 * (2 * C1 + 4 * C0 * C1) with hKT1
  set KT2 : ℝ := S.p * Kμ * (C1 * KD + C0 * KDd + C0 * KD) with hKT2
  have hKD0 : 0 ≤ KD := by positivity
  have hKD10 : 0 ≤ KD1 := by positivity
  have hKF0 : 0 ≤ KF := by positivity
  have hKDd0 : 0 ≤ KDd := by positivity
  have hKT10 : 0 ≤ KT1 := by positivity
  have hKT20 : 0 ≤ KT2 := by positivity
  refine ⟨Rs, hRs, KT1 + KT2 + 1, by positivity, ?_⟩
  intro ε μ R Y ht y hy j hj
  have hR : 1 ≤ R := hRs.trans ht.2.2.2.1
  have hy1 : 1 ≤ y := hR.trans hy
  have hy0 : 0 < y := by linarith
  have hR0 : 0 < R := by linarith
  have hε0 : 0 ≤ ε := ht.1
  have hμK : ‖μ‖ ≤ Kμ := by
    have h1 : dist μ (mu_star S.p) ≤ S.δ := ht.2.2.1
    have h2 := norm_le_norm_add_norm_sub' μ (mu_star S.p)
    rw [dist_eq_norm] at h1
    rw [hKμ]; linarith
  obtain ⟨⟨hl1, -, -, hdl0, -⟩, ⟨-, -, ha1⟩, ⟨hZ0, -, -, -⟩, h4, h5, -⟩ := hs0 ε μ R Y ht y hy
  obtain ⟨⟨-, -, hlam1, hdl1, -⟩, ⟨-, -, ha2⟩, ⟨hZ1, -, -, -⟩, -, -, -⟩ := hs1 ε μ R Y ht y hy
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one, sub_zero,
    zero_div, add_zero] at hdl0 ha1 hZ0 hlam1 hdl1 ha2 hZ1
  have hm0 := h4 0 (Nat.zero_le 1)
  have hm1 := h4 1 le_rfl
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one, sub_zero]
    at hm0 hm1
  set L := fam_lambda S.p ε μ with hLdef
  set Z := fam_Z S.p R ε μ with hZdef
  have hlpos : 0 < L y := by
    have : 0 < y ^ (1 / S.p) / 2 := by positivity
    linarith
  have hl0 : lambda0 S.p y = y ^ (1 / S.p) := rfl
  have hl0pos : 0 < lambda0 S.p y := by rw [hl0]; positivity
  have hl0ge : y ^ (1 / S.p) / 2 ≤ lambda0 S.p y := by rw [hl0]; linarith
  have hZn : ‖Z y‖ ≤ C0 * y ^ (-beta S.p) := by linarith [norm_nonneg (c05_standing_Zmu0 S.p R μ y)]
  have hZ'n : ‖deriv Z y‖ ≤ C1 * y ^ (-beta S.p + 1 / S.p) := by
    linarith [norm_nonneg (deriv (c05_standing_Zmu0 S.p R μ) y)]
  have hil : (L y)⁻¹ ≤ 2 * y ^ (-1 / S.p) := by
    have := c05_aux_lam_rpow_le (r := -1) hy0 hl1 (by norm_num)
    rwa [Real.rpow_neg_one, neg_neg, Real.rpow_one] at this
  have hil0 : 0 ≤ (L y)⁻¹ := inv_nonneg.mpr hlpos.le
  -- smoothness at `y`
  have hLs : ContDiffAt ℝ 2 L y := c05_aux_lambda_smooth S.p ε μ hy0
  have hLd : HasDerivAt L (deriv L y) y := (hLs.differentiableAt (by norm_num)).hasDerivAt
  have hZd : HasDerivAt Z (deriv Z y) y :=
    ((c05_aux_Z_smooth S.p R ε μ S.hp_lo S.hp_hi hR0 hy0 hlpos.ne' (n := 1)).differentiableAt
      one_ne_zero).hasDerivAt
  -- `T₁ = (i m) · (Z/λ)`
  set m : ℝ → ℝ := fun t => deriv (fun u => L u ^ S.p) t - 1 with hmdef
  have hmd : DifferentiableAt ℝ m y :=
    (((hLs.rpow_const_of_ne hlpos.ne').derivWithin (m := 1) (by norm_num)).differentiableAt
      one_ne_zero).sub_const 1
  have hT1eq : c05_fundamental_explicit_T1 S.p R ε μ =
      fun t => (Complex.I * ((m t : ℝ) : ℂ)) * (Z t / (L t : ℂ)) := by
    funext t; unfold c05_fundamental_explicit_T1; simp only [hmdef]; ring
  have hgd : HasDerivAt (fun t => Z t / (L t : ℂ))
      ((deriv Z y * (L y : ℂ) - Z y * ((deriv L y : ℝ) : ℂ)) / (L y : ℂ) ^ 2) y :=
    hZd.div hLd.ofReal_comp (by exact_mod_cast hlpos.ne')
  have hfd : HasDerivAt (fun t => Complex.I * ((m t : ℝ) : ℂ))
      (Complex.I * ((deriv m y : ℝ) : ℂ)) y := hmd.hasDerivAt.ofReal_comp.const_mul _
  have hgn : ‖Z y / (L y : ℂ)‖ ≤ 2 * C0 * y ^ (-beta S.p - 1 / S.p) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlpos, div_eq_mul_inv]
    calc ‖Z y‖ * (L y)⁻¹ ≤ (C0 * y ^ (-beta S.p)) * (2 * y ^ (-1 / S.p)) :=
          mul_le_mul hZn hil hil0 (by positivity)
      _ = 2 * C0 * (y ^ (-beta S.p) * y ^ (-1 / S.p)) := by ring
      _ = _ := by rw [c05_aux_ymul hy0 (c := -beta S.p - 1 / S.p) (by ring)]
  have hg'n : ‖(deriv Z y * (L y : ℂ) - Z y * ((deriv L y : ℝ) : ℂ)) / (L y : ℂ) ^ 2‖ ≤
      (2 * C1 + 4 * C0 * C1) * y ^ (-beta S.p) := by
    have e : (deriv Z y * (L y : ℂ) - Z y * ((deriv L y : ℝ) : ℂ)) / (L y : ℂ) ^ 2 =
        deriv Z y * (((L y)⁻¹ : ℝ) : ℂ) - Z y * ((deriv L y * ((L y)⁻¹) ^ 2 : ℝ) : ℂ) := by
      have : (L y : ℂ) ≠ 0 := by exact_mod_cast hlpos.ne'
      push_cast; field_simp
    rw [e]
    have hil2 : ((L y)⁻¹) ^ 2 ≤ 4 * y ^ (-2 / S.p) := by
      calc ((L y)⁻¹) ^ 2 ≤ (2 * y ^ (-1 / S.p)) ^ 2 := pow_le_pow_left₀ hil0 hil 2
        _ = 4 * (y ^ (-1 / S.p) * y ^ (-1 / S.p)) := by ring
        _ = 4 * y ^ (-2 / S.p) := by rw [c05_aux_ymul hy0 (c := -2 / S.p) (by ring)]
    have t1 : ‖deriv Z y * (((L y)⁻¹ : ℝ) : ℂ)‖ ≤ 2 * C1 * y ^ (-beta S.p) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hil0]
      calc ‖deriv Z y‖ * (L y)⁻¹ ≤ (C1 * y ^ (-beta S.p + 1 / S.p)) * (2 * y ^ (-1 / S.p)) :=
            mul_le_mul hZ'n hil hil0 (by positivity)
        _ = 2 * C1 * (y ^ (-beta S.p + 1 / S.p) * y ^ (-1 / S.p)) := by ring
        _ = _ := by rw [c05_aux_ymul hy0 (c := -beta S.p) (by ring)]
    have t2 : ‖Z y * ((deriv L y * ((L y)⁻¹) ^ 2 : ℝ) : ℂ)‖ ≤ 4 * C0 * C1 * y ^ (-beta S.p) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
        (0:ℝ) ≤ ((L y)⁻¹) ^ 2)]
      have hexp : -beta S.p + ((1 / S.p - 1) + -2 / S.p) ≤ -beta S.p := by
        have : (1 / S.p - 1) + -2 / S.p = -1 - 1 / S.p := by ring
        linarith
      calc ‖Z y‖ * (|deriv L y| * ((L y)⁻¹) ^ 2) ≤
          (C0 * y ^ (-beta S.p)) * ((C1 * y ^ (1 / S.p - 1)) * (4 * y ^ (-2 / S.p))) :=
            mul_le_mul hZn (mul_le_mul hlam1 hil2 (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = 4 * C0 * C1 * (y ^ (-beta S.p) * (y ^ (1 / S.p - 1) * y ^ (-2 / S.p))) := by ring
        _ ≤ 4 * C0 * C1 * y ^ (-beta S.p) := by
            rw [c05_aux_ymul hy0 rfl, c05_aux_ymul hy0 rfl]
            exact mul_le_mul_of_nonneg_left (c05_aux_ymono hy1 hexp) (by positivity)
    calc _ ≤ ‖deriv Z y * (((L y)⁻¹ : ℝ) : ℂ)‖ + ‖Z y * ((deriv L y * ((L y)⁻¹) ^ 2 : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * C1 * y ^ (-beta S.p) + 4 * C0 * C1 * y ^ (-beta S.p) := add_le_add t1 t2
      _ = _ := by ring
  have hT1 : ‖iteratedDeriv j (c05_fundamental_explicit_T1 S.p R ε μ) y‖ ≤
      KT1 * ε * y ^ (-S.p - 3 * beta S.p + j / S.p) := by
    rw [hT1eq]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |m y| * ‖Z y / (L y : ℂ)‖ ≤ (C0 * ε * y ^ (-S.p - 1)) *
            (2 * C0 * y ^ (-beta S.p - 1 / S.p)) := mul_le_mul hm0 hgn (norm_nonneg _) (by positivity)
        _ = 2 * C0 ^ 2 * ε * (y ^ (-S.p - 1) * y ^ (-beta S.p - 1 / S.p)) := by ring
        _ = 2 * C0 ^ 2 * ε * y ^ (-S.p - 3 * beta S.p) := by
            rw [c05_aux_ymul hy0 (c := -S.p - 3 * beta S.p) (by linarith)]
        _ ≤ KT1 * ε * y ^ (-S.p - 3 * beta S.p) := by
            have h2 : 0 ≤ C0 * (2 * C1 + 4 * C0 * C1) := by positivity
            have : 2 * C0 ^ 2 ≤ KT1 := by rw [hKT1]; linarith
            gcongr
    · simp only [iteratedDeriv_one, Nat.cast_one]
      have hd := c05_aux_deriv_mul_le hfd.differentiableAt hgd.differentiableAt
      rw [hfd.deriv, hgd.deriv] at hd
      refine hd.trans ?_
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have hexp1 : -S.p - 3 * beta S.p + 1 / S.p = -S.p - 1 - beta S.p := by linarith
      have e1 : -S.p - 1 - 1 + (-beta S.p - 1 / S.p) ≤ -S.p - 3 * beta S.p + 1 / S.p := by linarith
      have e2 : -S.p - 1 + -beta S.p = -S.p - 3 * beta S.p + 1 / S.p := by linarith
      calc |deriv m y| * ‖Z y / (L y : ℂ)‖ + |m y| *
            ‖(deriv Z y * (L y : ℂ) - Z y * ((deriv L y : ℝ) : ℂ)) / (L y : ℂ) ^ 2‖ ≤
          (C0 * ε * y ^ (-S.p - 1 - 1)) * (2 * C0 * y ^ (-beta S.p - 1 / S.p)) +
            (C0 * ε * y ^ (-S.p - 1)) * ((2 * C1 + 4 * C0 * C1) * y ^ (-beta S.p)) :=
          add_le_add (mul_le_mul hm1 hgn (norm_nonneg _) (by positivity))
            (mul_le_mul hm0 hg'n (norm_nonneg _) (by positivity))
        _ = 2 * C0 ^ 2 * ε * (y ^ (-S.p - 1 - 1) * y ^ (-beta S.p - 1 / S.p)) +
            C0 * (2 * C1 + 4 * C0 * C1) * ε * (y ^ (-S.p - 1) * y ^ (-beta S.p)) := by ring
        _ ≤ 2 * C0 ^ 2 * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) +
            C0 * (2 * C1 + 4 * C0 * C1) * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) := by
            rw [c05_aux_ymul hy0 rfl, c05_aux_ymul hy0 e2]
            gcongr <;> exact c05_aux_ymono hy1 e1
        _ = KT1 * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) := by rw [hKT1]; ring
  -- `T₂ = c · (a_*' · D)`
  set Φ := c05_standing_Phi S.p R ε μ with hΦdef
  set Φ₀ := c05_standing_Phi_zero S.p with hΦ₀def
  set Dfun : ℝ → ℂ := fun t => ((L t ^ q : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ t : ℂ)) -
      ((lambda0 S.p t ^ q : ℝ) : ℂ) * Complex.exp (Complex.I * (Φ₀ t : ℂ)) with hDdef
  have hT2eq : c05_fundamental_explicit_T2 S.p R ε μ =
      fun t => (-(Complex.I * S.p * μ)) * (deriv (astar S.p) t * Dfun t) := by
    funext t; unfold c05_fundamental_explicit_T2; simp only [hDdef]; ring
  have hcn : ‖-(Complex.I * (S.p : ℂ) * μ)‖ ≤ S.p * Kμ := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp0]
    exact mul_le_mul_of_nonneg_left hμK hp0.le
  set θ : ℝ := fam_Psi S.p R ε μ y - Psi0 S.p y with hθ
  have hexpΦ : ∀ x : ℝ, Complex.exp (Complex.I * (Φ y : ℂ)) * ((x : ℝ) : ℂ) =
      Complex.exp (Complex.I * (Φ₀ y : ℂ)) * (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
    intro x
    have : Complex.I * (Φ y : ℂ) = Complex.I * (Φ₀ y : ℂ) + Complex.I * (θ : ℂ) := by
      simp only [hΦdef, hΦ₀def, hθ, c05_standing_Phi, c05_standing_Phi_zero]; push_cast; ring
    rw [this, Complex.exp_add]; ring
  have hn0 : ‖Complex.exp (Complex.I * (Φ₀ y : ℂ))‖ = 1 := c04_aux_norm_exp_I _
  have hDn : ‖Dfun y‖ ≤ KD * ε * y ^ ((q + 1) / S.p - S.p) := by
    have e : Dfun y = Complex.exp (Complex.I * (Φ₀ y : ℂ)) *
        (((L y ^ q : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) - ((lambda0 S.p y ^ q : ℝ) : ℂ)) := by
      simp only [hDdef]
      rw [mul_comm (((L y ^ q : ℝ) : ℂ)), hexpΦ]; ring
    rw [e, norm_mul, hn0, one_mul, hKD]
    exact c05_aux_D_bound _ hy1 hp0 hl1 hl0ge hq0 hC0.le hε0 hdl0 h5
  -- derivative of `D`
  have hl0d : HasDerivAt (lambda0 S.p) (deriv (lambda0 S.p) y) y :=
    ((c05_aux_rpow_at (r := 1 / S.p) (n := 1) hy0).differentiableAt one_ne_zero).hasDerivAt
  have hΦd : HasDerivAt Φ (L y) y := (c05_aux_Psi_hasDeriv S.p R ε μ hR0 hy0).sub_const _
  have hΦ₀d : HasDerivAt Φ₀ (lambda0 S.p y) y := (c04_aux_Psi0_hasDeriv S.p hp0 y hy0).sub_const _
  have hE1 := ((hΦd.ofReal_comp).const_mul Complex.I).cexp
  have hE0 := ((hΦ₀d.ofReal_comp).const_mul Complex.I).cexp
  have hLq := (hLd.rpow_const (p := q) (Or.inl hlpos.ne')).ofReal_comp
  have hL0q := (hl0d.rpow_const (p := q) (Or.inl hl0pos.ne')).ofReal_comp
  have hDd := (hLq.mul hE1).sub (hL0q.mul hE0)
  set L' := deriv L y with hL'
  set L0' := deriv (lambda0 S.p) y with hL0'
  have hdl1' : |L' - L0'| ≤ C1 * ε * y ^ (1 / S.p - S.p - 1 - 1) := by
    rw [hL', hL0', ← deriv_fun_sub hLd.differentiableAt hl0d.differentiableAt]; exact hdl1
  have hD'eq : deriv Dfun y = Complex.exp (Complex.I * (Φ₀ y : ℂ)) *
      ((q : ℂ) * (((L y ^ (q - 1) * L' : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
          ((lambda0 S.p y ^ (q - 1) * L0' : ℝ) : ℂ)) +
        Complex.I * (((L y ^ (q + 1) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
          ((lambda0 S.p y ^ (q + 1) : ℝ) : ℂ))) := by
    rw [HasDerivAt.deriv (f := Dfun) hDd, Real.rpow_add_one hlpos.ne', Real.rpow_add_one hl0pos.ne']
    have h1 := hexpΦ (L' * q * L y ^ (q - 1))
    have h2 := hexpΦ (L y ^ q * L y)
    push_cast at h1 h2 ⊢
    linear_combination h1 + Complex.I * h2
  have hD'n : ‖deriv Dfun y‖ ≤ KDd * ε * y ^ ((q + 2) / S.p - S.p) := by
    rw [hD'eq, norm_mul, hn0, one_mul]
    have hF2 := c05_aux_D_bound (Complex.exp (Complex.I * (θ : ℂ))) hy1 hp0 hl1 hl0ge hq1 hC0.le
      hε0 hdl0 h5
    rw [show (q + 1 + 1) / S.p - S.p = (q + 2) / S.p - S.p by ring] at hF2
    have hF1 : ‖((L y ^ (q - 1) * L' : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
        ((lambda0 S.p y ^ (q - 1) * L0' : ℝ) : ℂ)‖ ≤ KF * ε * y ^ ((q + 2) / S.p - S.p) := by
      refine (c05_aux_phase_diff _ _ _).trans ?_
      have hLq1 : L y ^ (q - 1) ≤ 2 ^ (-(q - 1)) * y ^ ((q - 1) / S.p) :=
        c05_aux_lam_rpow_le hy0 hl1 hqm
      have hLq1' : 0 ≤ L y ^ (q - 1) := Real.rpow_nonneg hlpos.le _
      have ha : |L y ^ (q - 1) * L'| ≤ 2 ^ (1 - q) * C1 * y ^ (q / S.p - 1) := by
        rw [abs_mul, abs_of_nonneg hLq1', show -(q - 1) = 1 - q by ring] at *
        calc L y ^ (q - 1) * |L'| ≤ (2 ^ (1 - q) * y ^ ((q - 1) / S.p)) * (C1 * y ^ (1 / S.p - 1)) :=
              mul_le_mul hLq1 hlam1 (abs_nonneg _) (by positivity)
          _ = 2 ^ (1 - q) * C1 * (y ^ ((q - 1) / S.p) * y ^ (1 / S.p - 1)) := by ring
          _ = _ := by rw [c05_aux_ymul hy0 (c := q / S.p - 1) (by ring)]
      have hsub : |L y ^ (q - 1) - lambda0 S.p y ^ (q - 1)| ≤
          |q - 1| * 2 ^ (1 - (q - 1)) * C0 * ε * y ^ ((q - 2) / S.p + (1 / S.p - S.p - 1)) := by
        have hm : 0 < y ^ (1 / S.p) / 2 := by positivity
        refine (c05_aux_rpow_sub_le hm hl1 hl0ge (by linarith)).trans ?_
        rw [c05_aux_half_rpow hy0, show -(q - 1 - 1) = 1 - (q - 1) by ring]
        calc |q - 1| * (2 ^ (1 - (q - 1)) * y ^ ((q - 1 - 1) / S.p)) * |L y - lambda0 S.p y| ≤
            |q - 1| * (2 ^ (1 - (q - 1)) * y ^ ((q - 1 - 1) / S.p)) * (C0 * ε * y ^ (1 / S.p - S.p - 1)) :=
              mul_le_mul_of_nonneg_left hdl0 (by positivity)
          _ = |q - 1| * 2 ^ (1 - (q - 1)) * C0 * ε *
              (y ^ ((q - 1 - 1) / S.p) * y ^ (1 / S.p - S.p - 1)) := by ring
          _ = _ := by rw [c05_aux_ymul hy0 (c := (q - 2) / S.p + (1 / S.p - S.p - 1)) (by ring)]
      have hl0q : lambda0 S.p y ^ (q - 1) = y ^ ((q - 1) / S.p) := by
        rw [hl0, ← Real.rpow_mul hy0.le]; congr 1; ring
      have hab : |L y ^ (q - 1) * L' - lambda0 S.p y ^ (q - 1) * L0'| ≤
          (|q - 1| * 2 ^ (1 - (q - 1)) * C0 * C1 + C1) * ε * y ^ ((q + 2) / S.p - S.p) := by
        have e : L y ^ (q - 1) * L' - lambda0 S.p y ^ (q - 1) * L0' =
            (L y ^ (q - 1) - lambda0 S.p y ^ (q - 1)) * L' + lambda0 S.p y ^ (q - 1) * (L' - L0') := by
          ring
        rw [e]
        have hx1 : (q - 2) / S.p + (1 / S.p - S.p - 1) + (1 / S.p - 1) ≤ (q + 2) / S.p - S.p := by
          have : (q - 2) / S.p + (1 / S.p - S.p - 1) + (1 / S.p - 1) =
              (q + 2) / S.p - S.p - 2 - 2 / S.p := by ring
          have : 0 < 2 / S.p := by positivity
          linarith
        have hx2 : (q - 1) / S.p + (1 / S.p - S.p - 1 - 1) ≤ (q + 2) / S.p - S.p := by
          have : (q - 1) / S.p + (1 / S.p - S.p - 1 - 1) = (q + 2) / S.p - S.p - 2 - 2 / S.p := by
            ring
          have : 0 < 2 / S.p := by positivity
          linarith
        calc |(L y ^ (q - 1) - lambda0 S.p y ^ (q - 1)) * L' +
              lambda0 S.p y ^ (q - 1) * (L' - L0')| ≤
            |L y ^ (q - 1) - lambda0 S.p y ^ (q - 1)| * |L'| +
              lambda0 S.p y ^ (q - 1) * |L' - L0'| := by
              refine (abs_add_le _ _).trans (le_of_eq ?_)
              rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl0pos _)]
          _ ≤ (|q - 1| * 2 ^ (1 - (q - 1)) * C0 * ε *
                y ^ ((q - 2) / S.p + (1 / S.p - S.p - 1))) * (C1 * y ^ (1 / S.p - 1)) +
              y ^ ((q - 1) / S.p) * (C1 * ε * y ^ (1 / S.p - S.p - 1 - 1)) := by
              rw [hl0q] at hsub ⊢
              exact add_le_add (mul_le_mul hsub hlam1 (abs_nonneg _) (by positivity))
                (mul_le_mul_of_nonneg_left hdl1' (by positivity))
          _ = |q - 1| * 2 ^ (1 - (q - 1)) * C0 * C1 * ε *
                (y ^ ((q - 2) / S.p + (1 / S.p - S.p - 1)) * y ^ (1 / S.p - 1)) +
              C1 * ε * (y ^ ((q - 1) / S.p) * y ^ (1 / S.p - S.p - 1 - 1)) := by ring
          _ ≤ |q - 1| * 2 ^ (1 - (q - 1)) * C0 * C1 * ε * y ^ ((q + 2) / S.p - S.p) +
              C1 * ε * y ^ ((q + 2) / S.p - S.p) := by
              rw [c05_aux_ymul hy0 rfl, c05_aux_ymul hy0 rfl]
              gcongr <;> first | exact c05_aux_ymono hy1 hx1 | exact c05_aux_ymono hy1 hx2
          _ = _ := by ring
      have hx3 : q / S.p - 1 + (1 / S.p - S.p) ≤ (q + 2) / S.p - S.p := by
        have : q / S.p - 1 + (1 / S.p - S.p) = (q + 2) / S.p - S.p - 1 - 1 / S.p := by ring
        linarith
      calc |L y ^ (q - 1) * L'| * ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ +
            |L y ^ (q - 1) * L' - lambda0 S.p y ^ (q - 1) * L0'| ≤
          (2 ^ (1 - q) * C1 * y ^ (q / S.p - 1)) * (C0 * ε * y ^ (1 / S.p - S.p)) +
            (|q - 1| * 2 ^ (1 - (q - 1)) * C0 * C1 + C1) * ε * y ^ ((q + 2) / S.p - S.p) :=
          add_le_add (mul_le_mul ha h5 (norm_nonneg _) (by positivity)) hab
        _ = 2 ^ (1 - q) * C1 * C0 * ε * (y ^ (q / S.p - 1) * y ^ (1 / S.p - S.p)) +
            (|q - 1| * 2 ^ (1 - (q - 1)) * C0 * C1 + C1) * ε * y ^ ((q + 2) / S.p - S.p) := by ring
        _ ≤ 2 ^ (1 - q) * C1 * C0 * ε * y ^ ((q + 2) / S.p - S.p) +
            (|q - 1| * 2 ^ (1 - (q - 1)) * C0 * C1 + C1) * ε * y ^ ((q + 2) / S.p - S.p) := by
            rw [c05_aux_ymul hy0 rfl]
            gcongr <;> exact c05_aux_ymono hy1 hx3
        _ = KF * ε * y ^ ((q + 2) / S.p - S.p) := by rw [hKF]; ring
    calc ‖(q : ℂ) * (((L y ^ (q - 1) * L' : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
          ((lambda0 S.p y ^ (q - 1) * L0' : ℝ) : ℂ)) +
        Complex.I * (((L y ^ (q + 1) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) -
          ((lambda0 S.p y ^ (q + 1) : ℝ) : ℂ))‖ ≤
        |q| * (KF * ε * y ^ ((q + 2) / S.p - S.p)) + KD1 * ε * y ^ ((q + 2) / S.p - S.p) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hF1 (abs_nonneg _)
          · rw [norm_mul, Complex.norm_I, one_mul, hKD1]; exact hF2
      _ = KDd * ε * y ^ ((q + 2) / S.p - S.p) := by rw [hKDd]; ring
  -- the bound for `T₂`
  have hAs : ContDiffAt ℝ 2 (astar S.p) y := c05_aux_astar_smooth S.p S.hp_lo S.hp_hi hy0
  have had : DifferentiableAt ℝ (deriv (astar S.p)) y :=
    (hAs.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDdiff : DifferentiableAt ℝ Dfun y := hDd.differentiableAt
  have hT2 : ‖iteratedDeriv j (c05_fundamental_explicit_T2 S.p R ε μ) y‖ ≤
      KT2 * ε * y ^ (-S.p - 3 * beta S.p + j / S.p) := by
    rw [hT2eq]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
      rw [norm_mul, norm_mul]
      calc ‖-(Complex.I * (S.p : ℂ) * μ)‖ * (‖deriv (astar S.p) y‖ * ‖Dfun y‖) ≤
          (S.p * Kμ) * ((C0 * y ^ (-2 * beta S.p - 1)) * (KD * ε * y ^ ((q + 1) / S.p - S.p))) :=
            mul_le_mul hcn (mul_le_mul ha1 hDn (norm_nonneg _) (by positivity)) (by positivity)
              (by positivity)
        _ = S.p * Kμ * C0 * KD * ε * (y ^ (-2 * beta S.p - 1) * y ^ ((q + 1) / S.p - S.p)) := by ring
        _ = S.p * Kμ * C0 * KD * ε * y ^ (-S.p - 3 * beta S.p) := by rw [c05_aux_ymul hy0 hqexp]
        _ ≤ KT2 * ε * y ^ (-S.p - 3 * beta S.p) := by
            have e : KT2 = S.p * Kμ * C0 * KD + S.p * Kμ * (C1 * KD + C0 * KDd) := by rw [hKT2]; ring
            have : 0 ≤ S.p * Kμ * (C1 * KD + C0 * KDd) := by positivity
            have : S.p * Kμ * C0 * KD ≤ KT2 := by
              rw [e]; exact le_add_of_nonneg_right this
            gcongr
    · simp only [iteratedDeriv_one, Nat.cast_one]
      rw [deriv_const_mul _ (show DifferentiableAt ℝ (fun t => deriv (astar S.p) t * Dfun t) y from
        had.mul hDdiff), norm_mul]
      have hd := c05_aux_deriv_mul_le had hDdiff
      have e1 : -2 * beta S.p - 1 - 1 + ((q + 1) / S.p - S.p) ≤ -S.p - 3 * beta S.p + 1 / S.p := by
        linarith
      have e2 : -2 * beta S.p - 1 + ((q + 2) / S.p - S.p) = -S.p - 3 * beta S.p + 1 / S.p := by
        calc -2 * beta S.p - 1 + ((q + 2) / S.p - S.p) =
            (-2 * beta S.p - 1 + ((q + 1) / S.p - S.p)) + 1 / S.p := by ring
          _ = -S.p - 3 * beta S.p + 1 / S.p := by rw [hqexp]
      calc ‖-(Complex.I * (S.p : ℂ) * μ)‖ * ‖deriv (fun t => deriv (astar S.p) t * Dfun t) y‖ ≤
          (S.p * Kμ) * ((C1 * y ^ (-2 * beta S.p - 1 - 1)) * (KD * ε * y ^ ((q + 1) / S.p - S.p)) +
            (C0 * y ^ (-2 * beta S.p - 1)) * (KDd * ε * y ^ ((q + 2) / S.p - S.p))) := by
            refine mul_le_mul hcn (hd.trans (add_le_add ?_ ?_)) (norm_nonneg _) (by positivity)
            · exact mul_le_mul ha2 hDn (norm_nonneg _) (by positivity)
            · exact mul_le_mul ha1 hD'n (norm_nonneg _) (by positivity)
        _ = S.p * Kμ * C1 * KD * ε * (y ^ (-2 * beta S.p - 1 - 1) * y ^ ((q + 1) / S.p - S.p)) +
            S.p * Kμ * C0 * KDd * ε * (y ^ (-2 * beta S.p - 1) * y ^ ((q + 2) / S.p - S.p)) := by ring
        _ ≤ S.p * Kμ * C1 * KD * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) +
            S.p * Kμ * C0 * KDd * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) := by
            rw [c05_aux_ymul hy0 rfl, c05_aux_ymul hy0 e2]
            have hc : 0 ≤ S.p * Kμ * C1 * KD * ε :=
              mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hp0.le hKμ0) hC1.le) hKD0) hε0
            exact add_le_add (mul_le_mul_of_nonneg_left (c05_aux_ymono hy1 e1) hc) le_rfl
        _ ≤ KT2 * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) := by
            have h0 : 0 ≤ ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) :=
              mul_nonneg hε0 (Real.rpow_nonneg hy0.le _)
            have e : KT2 = S.p * Kμ * C1 * KD + S.p * Kμ * C0 * KDd + S.p * Kμ * (C0 * KD) := by
              rw [hKT2]; ring
            have : 0 ≤ S.p * Kμ * (C0 * KD) :=
              mul_nonneg (mul_nonneg hp0.le hKμ0) (mul_nonneg hC0.le hKD0)
            have h3 : S.p * Kμ * C1 * KD + S.p * Kμ * C0 * KDd ≤ KT2 := by
              rw [e]; exact le_add_of_nonneg_right this
            calc S.p * Kμ * C1 * KD * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) +
                S.p * Kμ * C0 * KDd * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) =
                (S.p * Kμ * C1 * KD + S.p * Kμ * C0 * KDd) * (ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p)) := by
                  ring
              _ ≤ KT2 * (ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p)) := mul_le_mul_of_nonneg_right h3 h0
              _ = _ := by ring
  have h0 : 0 ≤ ε * y ^ (-S.p - 3 * beta S.p + j / S.p) := mul_nonneg hε0 (Real.rpow_nonneg hy0.le _)
  calc _ ≤ KT1 * ε * y ^ (-S.p - 3 * beta S.p + j / S.p) +
      KT2 * ε * y ^ (-S.p - 3 * beta S.p + j / S.p) := add_le_add hT1 hT2
    _ = (KT1 + KT2) * (ε * y ^ (-S.p - 3 * beta S.p + j / S.p)) := by ring
    _ ≤ (KT1 + KT2 + 1) * (ε * y ^ (-S.p - 3 * beta S.p + j / S.p)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) h0
    _ = _ := by ring

/-- Blueprint: lem:c05_fundamental_bound.  On `[Y,2Y]`, `j = 0,1`:
`|∂^j ℛ_{lin,1}| ≤ Cε(Y^{-p-3β+j/p} + Y^{-p-2-j}) ≤ CεY^{-2p-1+j/p}`. -/
theorem c05_fundamental_bound (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (c05_E5_remainders_Rlin1 S.p R ε μ) y| ≤
              C * ε * (Y ^ (-S.p - 3 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j)) ∧
            |iteratedDeriv j (c05_E5_remainders_Rlin1 S.p R ε μ) y| ≤
              C * ε * Y ^ (-2 * S.p - 1 + j / S.p) := by
  obtain ⟨Ri, hRi, hid⟩ := c05_fundamental_identity S
  obtain ⟨Re, hRe, CE, hCE, hexp⟩ := c05_fundamental_explicit S
  obtain ⟨Rm, hRm, CM, hCM, hmult⟩ := c05_multiplier_fundamental S
  obtain ⟨Rp, hRp, CP, hCP, hprim⟩ := c05_fundamental_primitive S
  obtain ⟨Rf, hRf, CF, hCF, hfar⟩ := c05_far_localization S
  obtain ⟨Ro, hRo, CO, hCO, hosc⟩ := c05_osc_split_bounds S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  obtain ⟨hneg1, hcmp0, hcmpb0, hcmpb1⟩ := c05_aux_exponents S.p hp0 S.hp_hi
  set R₀ := max (max (max Ri Re) (max Rm Rp)) (max (max Rf Ro) Rs) with hR₀
  have hi : Ri ≤ R₀ := by simp [hR₀]
  have he : Re ≤ R₀ := by simp [hR₀]
  have hm : Rm ≤ R₀ := by simp [hR₀]
  have hp : Rp ≤ R₀ := by simp [hR₀]
  have hf : Rf ≤ R₀ := by simp [hR₀]
  have ho : Ro ≤ R₀ := by simp [hR₀]
  have hs : Rs ≤ R₀ := by simp [hR₀]
  set C₁ := 2 * CE + 2 * CM + CP + CF * CO with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨R₀, hRi.trans hi, 2 * C₁, by positivity, ?_⟩
  intro ε μ R Y ht y hy j hj
  have hε : 0 ≤ ε := ht.1
  have hR : 1 ≤ R := (hRi.trans hi).trans ht.2.2.2.1
  have hY8 : 8 * R ≤ Y := ht.2.2.2.2
  have hY : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hyY : Y ≤ y := hy.1
  have hyR : R < y := by linarith
  have hy0 : 0 < y := by linarith
  have hyI : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hI : Ioo (Y / 2) (3 * Y) ∈ nhds y := isOpen_Ioo.mem_nhds hyI
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsym0 ε μ R Y (c05_aux_tuple_mono hs ht) t ht'.le).1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  have hidy := hid ε μ R Y (c05_aux_tuple_mono hi ht)
  obtain ⟨-, hmb⟩ := hmult ε μ R Y (c05_aux_tuple_mono hm ht)
  obtain ⟨-, -, hpd, hpb⟩ := hprim ε μ R Y (c05_aux_tuple_mono hp ht)
  obtain ⟨hs1, -, hz, ⟨M, hM⟩, -, -, -, hi1, -, hL1⟩ := hosc ε μ R Y (c05_aux_tuple_mono ho ht)
  obtain ⟨-, -, hfC1, hfb⟩ := hfar ε μ R Y (c05_aux_tuple_mono hf ht) _ hs1
    ⟨M, fun x => ⟨(hM x).1, (hM x).2.1⟩⟩ hi1 (fun x hx => (hz x hx).1)
  have hL1' : ∫ x, |c05_E5_remainders_fosc1 S.p R ε μ x| ≤ CO * ε := by
    have : 0 ≤ ∫ x, |c05_E5_remainders_fosc3 S.p R ε μ x| :=
      integral_nonneg (fun _ => abs_nonneg _)
    linarith
  have hYpow : ∀ a : ℝ, a ≤ 0 → y ^ a ≤ Y ^ a := fun a ha =>
    Real.rpow_le_rpow_of_nonpos hY0 hyY ha
  -- the main bound, in terms of `Y`
  have hmain : |iteratedDeriv j (c05_E5_remainders_Rlin1 S.p R ε μ) y| ≤
      C₁ * ε * (Y ^ (-S.p - 3 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j)) := by
    have hYa : 0 ≤ Y ^ (-S.p - 3 * beta S.p + j / S.p) := by positivity
    have hYb : 0 ≤ Y ^ (-S.p - 2 - j) := by positivity
    have hFb : CF * Y ^ (-S.p - 2 - j) * ∫ x, |c05_E5_remainders_fosc1 S.p R ε μ x| ≤
        CF * CO * ε * Y ^ (-S.p - 2 - j) := by
      calc _ ≤ CF * Y ^ (-S.p - 2 - j) * (CO * ε) := by gcongr
        _ = _ := by ring
    have hfbj := hfb y ⟨hy.1, hy.2⟩ j hj
    have hexpj := hexp ε μ R Y (c05_aux_tuple_mono he ht) y hyR.le j hj
    have hmbj := hmb y hy j hj
    have hpby := hpb y hyR.le
    have hCMn : 0 ≤ CM * ε * Y ^ (-S.p - 3 * beta S.p + j / S.p) := by positivity
    interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero, sub_zero] at hfbj hexpj hmbj hFb hYa hCMn ⊢
      rw [hidy y hyI]
      have e1 : |2 * (c05_fundamental_explicit_T1 S.p R ε μ y +
          c05_fundamental_explicit_T2 S.p R ε μ y).re| ≤
          2 * (CE * ε * Y ^ (-S.p - 3 * beta S.p)) := by
        rw [abs_mul, abs_two]
        gcongr
        refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (hexpj.trans ?_))
        have := hYpow (-S.p - 3 * beta S.p) (by linarith only [hcmp0, hp0])
        gcongr
      have e2 : |2 * (c05_auxiliary_remainders_Emult S.p R ε μ Y y -
          c05_auxiliary_remainders_Emult0 S.p R μ Y y).re| ≤
          2 * (CM * ε * Y ^ (-S.p - 3 * beta S.p)) := by
        rw [abs_mul, abs_two]
        gcongr
        exact (Complex.abs_re_le_norm _).trans hmbj
      have e3 : |c05_auxiliary_remainders_Rprim S.p R ε μ y| ≤
          CP * ε * Y ^ (-S.p - 3 * beta S.p) :=
        have h' := hYpow (-S.p - 3 * beta S.p) (by linarith only [hcmp0, hp0])
        calc _ ≤ CP * ε * y ^ (-S.p - 3 * beta S.p) := hpby.1
          _ ≤ _ := by gcongr
      set u1 := 2 * (c05_fundamental_explicit_T1 S.p R ε μ y +
          c05_fundamental_explicit_T2 S.p R ε μ y).re
      set u2 := 2 * (c05_auxiliary_remainders_Emult S.p R ε μ Y y -
            c05_auxiliary_remainders_Emult0 S.p R μ Y y).re
      set u3 := c05_auxiliary_remainders_Rprim S.p R ε μ y
      set u4 := c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc1 S.p R ε μ) y
      have a1 := abs_add_le (u1 + u2 + u3) u4
      have a2 := abs_add_le (u1 + u2) u3
      have a3 := abs_add_le u1 u2
      have hdiff : C₁ * ε * (Y ^ (-S.p - 3 * beta S.p) + Y ^ (-S.p - 2)) -
          ((2 * CE + 2 * CM + CP) * ε * Y ^ (-S.p - 3 * beta S.p) +
            CF * CO * ε * Y ^ (-S.p - 2)) =
          CF * CO * ε * Y ^ (-S.p - 3 * beta S.p) + (2 * CE + 2 * CM + CP) * ε * Y ^ (-S.p - 2) := by
        rw [hC₁]; ring
      have hd1 : 0 ≤ CF * CO * ε * Y ^ (-S.p - 3 * beta S.p) := by positivity
      have hd2 : 0 ≤ (2 * CE + 2 * CM + CP) * ε * Y ^ (-S.p - 2) := by positivity
      linarith only [e1, e2, e3, hfbj, hFb, a1, a2, a3, hdiff, hd1, hd2]
    · simp only [iteratedDeriv_one, Nat.cast_one] at hfbj hexpj hmbj hFb hYa hCMn ⊢
      -- regularity of the four terms at `y`
      obtain ⟨hlq, hZ2, hZ02, hda, hdl, hPhi, hPhi0, hlam2, -⟩ :=
        c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos hyR
      have hlne : (fam_lambda S.p ε μ y : ℂ) ≠ 0 := by exact_mod_cast (hpos y hyR).ne'
      have hl0ne : (lambda0 S.p y : ℂ) ≠ 0 := by
        unfold lambda0; exact_mod_cast (Real.rpow_pos_of_pos hy0 _).ne'
      have dZ := hZ2.differentiableAt (by norm_num)
      have dZ0 := hZ02.differentiableAt (by norm_num)
      have dda := hda.differentiableAt one_ne_zero
      have ddl := hdl.differentiableAt one_ne_zero
      have dPhi := hPhi.differentiableAt (by norm_num)
      have dPhi0 := hPhi0.differentiableAt (by norm_num)
      have dlam := hlam2.differentiableAt (by norm_num)
      have dlq : ∀ q : ℝ, DifferentiableAt ℝ (fun t => fam_lambda S.p ε μ t ^ q) y :=
        fun q => (hlq q).differentiableAt (by norm_num)
      have dl0 : DifferentiableAt ℝ (lambda0 S.p) y := by
        unfold lambda0; exact (c05_aux_rpow_at hy0 (n := 1)).differentiableAt one_ne_zero
      have dl0q : DifferentiableAt ℝ (fun t => lambda0 S.p t ^ ((S.p - 3) / 2)) y := by
        unfold lambda0
        exact ((c05_aux_rpow_at hy0 (n := 1)).rpow_const_of_ne
          (Real.rpow_pos_of_pos hy0 _).ne').differentiableAt one_ne_zero
      have dT1 : DifferentiableAt ℝ (c05_fundamental_explicit_T1 S.p R ε μ) y := by
        unfold c05_fundamental_explicit_T1
        exact (((differentiableAt_const _).mul (c05_aux_ofReal_diff (ddl.sub_const 1))).mul
          dZ).div (c05_aux_ofReal_diff dlam) hlne
      have dT2 : DifferentiableAt ℝ (c05_fundamental_explicit_T2 S.p R ε μ) y := by
        unfold c05_fundamental_explicit_T2
        refine (((differentiableAt_const _).mul dda).mul ?_).neg
        refine ((c05_aux_ofReal_diff (dlq _)).mul ?_).sub ((c05_aux_ofReal_diff dl0q).mul ?_)
        · exact ((differentiableAt_const _).mul (c05_aux_ofReal_diff dPhi)).cexp
        · exact ((differentiableAt_const _).mul (c05_aux_ofReal_diff dPhi0)).cexp
      have hRY : R < 3 * Y / 10 := by linarith
      have dfZ : DifferentiableAt ℝ
          (fracDC S.p (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z)) y :=
        (c05_aux_fracDC_cutoff S.p S.hp_lo S.hp_hi hY0 hRY (fun t ht' =>
          (c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos ht').2.1)).differentiable
          one_ne_zero y
      have dfZ0 : DifferentiableAt ℝ
          (fracDC S.p (fun z => (res_chiY Y z : ℂ) * c05_standing_Zmu0 S.p R μ z)) y :=
        (c05_aux_fracDC_cutoff S.p S.hp_lo S.hp_hi hY0 hRY (fun t ht' =>
          (c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos ht').2.2.1)).differentiable
          one_ne_zero y
      have dE : DifferentiableAt ℝ (c05_auxiliary_remainders_Emult S.p R ε μ Y) y := by
        unfold c05_auxiliary_remainders_Emult
        refine dfZ.sub (((c05_aux_ofReal_diff (dlq S.p)).mul dZ).add ?_ |>.sub ?_)
        · exact ((differentiableAt_const _).mul (c05_aux_ofReal_diff (ddl.div dlam
            (hpos y hyR).ne'))).mul dZ
        · exact (((differentiableAt_const _).mul dda).mul (c05_aux_ofReal_diff (dlq _))).mul
            ((differentiableAt_const _).mul (c05_aux_ofReal_diff dPhi)).cexp
      have dE0 : DifferentiableAt ℝ (c05_auxiliary_remainders_Emult0 S.p R μ Y) y := by
        unfold c05_auxiliary_remainders_Emult0
        refine dfZ0.sub (((c05_aux_ofReal_diff differentiableAt_id).mul dZ0).add ?_ |>.sub ?_)
        · exact ((differentiableAt_const _).div (c05_aux_ofReal_diff dl0) hl0ne).mul dZ0
        · exact (((differentiableAt_const _).mul dda).mul (c05_aux_ofReal_diff dl0q)).mul
            ((differentiableAt_const _).mul (c05_aux_ofReal_diff dPhi0)).cexp
      have dH : DifferentiableAt ℝ (fun t => c05_auxiliary_remainders_Emult S.p R ε μ Y t -
          c05_auxiliary_remainders_Emult0 S.p R μ Y t) y := dE.sub dE0
      have hRp : HasDerivAt (c05_auxiliary_remainders_Rprim S.p R ε μ) _ y :=
        (hpd y (le_of_lt hyR)).hasDerivAt (Ici_mem_nhds hyR)
      have dRf : DifferentiableAt ℝ
          (c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc1 S.p R ε μ)) y :=
        (hfC1.contDiffAt hI).differentiableAt one_ne_zero
      have hG := ((((c05_aux_hasDerivAt_re (dT1.hasDerivAt.add dT2.hasDerivAt)).const_mul 2).add
        ((c05_aux_hasDerivAt_re dH.hasDerivAt).const_mul 2)).add hRp).add dRf.hasDerivAt
      have hev : c05_E5_remainders_Rlin1 S.p R ε μ =ᶠ[nhds y] fun t =>
          2 * (c05_fundamental_explicit_T1 S.p R ε μ t + c05_fundamental_explicit_T2 S.p R ε μ t).re +
            2 * (c05_auxiliary_remainders_Emult S.p R ε μ Y t -
              c05_auxiliary_remainders_Emult0 S.p R μ Y t).re +
            c05_auxiliary_remainders_Rprim S.p R ε μ t +
            c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc1 S.p R ε μ) t := by
        filter_upwards [hI] with t ht' using hidy t ht'
      have hG' := hG.congr_of_eventuallyEq hev
      rw [hG'.deriv]
      have hya := hYpow (-S.p - 3 * beta S.p + 1 / S.p) hneg1.le
      have b1 : |2 * (deriv (c05_fundamental_explicit_T1 S.p R ε μ) y +
          deriv (c05_fundamental_explicit_T2 S.p R ε μ) y).re| ≤
          2 * (CE * ε * Y ^ (-S.p - 3 * beta S.p + 1 / S.p)) := by
        rw [abs_mul, abs_two]
        gcongr
        refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (hexpj.trans ?_))
        gcongr
      have b2 : |2 * (deriv (fun t => c05_auxiliary_remainders_Emult S.p R ε μ Y t -
            c05_auxiliary_remainders_Emult0 S.p R μ Y t) y).re| ≤
          2 * (CM * ε * Y ^ (-S.p - 3 * beta S.p + 1 / S.p)) := by
        rw [abs_mul, abs_two]
        gcongr
        exact (Complex.abs_re_le_norm _).trans hmbj
      have b3 := hpby.2.trans (show CP * ε * y ^ (-S.p - 3 * beta S.p + 1 / S.p) ≤
          CP * ε * Y ^ (-S.p - 3 * beta S.p + 1 / S.p) by gcongr)
      refine (abs_add_le _ _).trans ?_
      refine (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl).trans ?_
      have hdiff : C₁ * ε * (Y ^ (-S.p - 3 * beta S.p + 1 / S.p) + Y ^ (-S.p - 2 - 1)) -
          ((2 * CE + 2 * CM + CP) * ε * Y ^ (-S.p - 3 * beta S.p + 1 / S.p) +
            CF * CO * ε * Y ^ (-S.p - 2 - 1)) =
          CF * CO * ε * Y ^ (-S.p - 3 * beta S.p + 1 / S.p) +
            (2 * CE + 2 * CM + CP) * ε * Y ^ (-S.p - 2 - 1) := by
        rw [hC₁]; ring
      have hd1 : 0 ≤ CF * CO * ε * Y ^ (-S.p - 3 * beta S.p + 1 / S.p) := by positivity
      have hd2 : 0 ≤ (2 * CE + 2 * CM + CP) * ε * Y ^ (-S.p - 2 - 1) := by positivity
      linarith only [b1, b2, b3, hfbj, hFb, hdiff, hd1, hd2]
  refine ⟨hmain.trans ?_, hmain.trans ?_⟩
  · have : 0 ≤ C₁ * ε * (Y ^ (-S.p - 3 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j)) := by
      positivity
    linarith
  · have ha : Y ^ (-S.p - 3 * beta S.p + j / S.p) ≤ Y ^ (-2 * S.p - 1 + j / S.p) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    have hb : Y ^ (-S.p - 2 - j) ≤ Y ^ (-2 * S.p - 1 + j / S.p) := by
      refine Real.rpow_le_rpow_of_exponent_le hY ?_
      interval_cases j
      · simp only [Nat.cast_zero, sub_zero, zero_div, add_zero]; linarith
      · simp only [Nat.cast_one]; linarith
    calc C₁ * ε * (Y ^ (-S.p - 3 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j))
        ≤ C₁ * ε * (Y ^ (-2 * S.p - 1 + j / S.p) + Y ^ (-2 * S.p - 1 + j / S.p)) := by
          gcongr
      _ = 2 * C₁ * ε * Y ^ (-2 * S.p - 1 + j / S.p) := by ring



/-- Blueprint: lem:c05_multiplier_third.
`|∂^j[|D|^p(χ_Y Z³) - 3^p λ^p Z³](y)| ≤ C Y^{1-5β+j/p}` on `[Y,2Y]`, `j = 0,1`. -/
theorem c05_multiplier_third (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          ‖iteratedDeriv j (fun t =>
              fracDC S.p (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3) t -
                (((3 : ℝ) ^ S.p * fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * fam_Z S.p R ε μ t ^ 3) y‖ ≤
            C * Y ^ (1 - 5 * beta S.p + j / S.p) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have h2β : 2 * beta S.p = 1 + 1 / S.p := c05_aux_two_beta S.p hp0
  obtain ⟨Rh, hRh, cs, hcs, hyp⟩ := c05_multiplier_hypotheses S
  choose Ck hCk hCkb using hyp
  obtain ⟨H1, -, -⟩ := appendix_oscillatory_multiplier S.p hp0 hp1 cs⁻¹ (inv_pos.mpr hcs)
  obtain ⟨k0, hk0⟩ := H1 1 le_rfl 0 (Nat.zero_le 1)
  obtain ⟨k1, hk1⟩ := H1 1 le_rfl 1 le_rfl
  obtain ⟨C0, hC0, HC0⟩ := hk0 Ck
  obtain ⟨C1, hC1, HC1⟩ := hk1 Ck
  refine ⟨Rh, hRh, C0 + 3 * cs⁻¹ * C0 + C1, by positivity, ?_⟩
  intro ε μ R Y ht y hy j hj
  have hR : 1 ≤ R := hRh.trans ht.2.2.2.1
  have hY1 : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hY0 : 0 < Y := by linarith
  set Λ := Y ^ (1 / S.p) with hΛ
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow hY1 (by positivity)
  set A := Y ^ (-3 * beta S.p) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos hY0 _
  set Φ := c05_standing_Phi S.p R ε μ with hΦ
  set Ψ : ℝ → ℝ := fun z => 3 * Φ z with hΨ
  set a₃ : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * c05_standing_A S.p ε μ z ^ 3 with ha₃
  have hH := fun k => hCkb k ε μ R Y ht
  -- the hypotheses of the appendix lemma
  have hhyp : ∀ k₀ : ℕ, c03_mult_hyp Y Λ A cs⁻¹ Ck k₀ a₃ Ψ := by
    intro k₀
    obtain ⟨⟨-, -, hs3, -, -, hsupp, hΦs, -⟩, -⟩ := hH 0
    refine ⟨hs3, hsupp, contDiffOn_const.mul hΦs, fun x hx => ?_⟩
    obtain ⟨-, -, ⟨h31, h32, -, -⟩⟩ := (hH 0).2 x hx
    refine ⟨by rw [inv_inv]; exact h31, h32, fun k _ => ?_⟩
    obtain ⟨-, -, ⟨-, -, h33, h34⟩⟩ := (hH k).2 x hx
    refine ⟨h33, ?_⟩
    rw [hA, mul_assoc, ← Real.rpow_add hY0]
    convert h34 using 3
  have hYy : 0 < y := by linarith [hy.1]
  obtain ⟨-, hR0b⟩ := HC0 Y Λ A a₃ Ψ hY1 hΛ1 hA0 (hhyp k0) y hy
  obtain ⟨-, hR1b⟩ := HC1 Y Λ A a₃ Ψ hY1 hΛ1 hA0 (hhyp k1) y hy
  simp only [Nat.cast_one, Nat.cast_zero, add_zero, iteratedDeriv_zero, iteratedDeriv_one]
    at hR0b hR1b
  set R1 := c03_mult_R S.p Y a₃ Ψ 1 with hR1
  set G : ℝ → ℂ := fun t => Complex.exp (Complex.I * (Ψ t : ℂ)) * R1 t with hG
  have hΦd : ∀ t, 0 < t → HasDerivAt Φ (fam_lambda S.p ε μ t) t := fun t ht' =>
    (c05_aux_Psi_hasDeriv S.p R ε μ (by linarith) ht').sub_const (π / 4)
  have hΨd : ∀ t, 0 < t → HasDerivAt Ψ (3 * fam_lambda S.p ε μ t) t := fun t ht' =>
    (hΦd t ht').const_mul 3
  have heq : ∀ t ∈ Ioo (Y / 2) (3 * Y),
      fracDC S.p (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3) t -
        (((3 : ℝ) ^ S.p * fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * fam_Z S.p R ε μ t ^ 3 = G t := by
    intro t ht'
    have ht0 : 0 < t := by linarith [ht'.1]
    have hχ : res_chiY Y t = 1 := c05_aux_chiY_one hY0 ⟨ht'.1.le, ht'.2.le⟩
    have hZ3 : ∀ z, fam_Z S.p R ε μ z ^ 3 =
        c05_standing_A S.p ε μ z ^ 3 * Complex.exp (Complex.I * (Ψ z : ℂ)) := by
      intro z
      show (c05_standing_A S.p ε μ z * Complex.exp (Complex.I * (Φ z : ℂ))) ^ 3 = _
      rw [mul_pow, ← Complex.exp_nat_mul]; simp only [hΨ]; push_cast; ring_nf
    have hfun : (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3) =
        fun x => a₃ x * Complex.exp (Complex.I * (Ψ x : ℂ)) := by
      funext z; rw [hZ3]; simp only [ha₃]; ring
    have hmem : t + 0 ∈ Ioo (Y / 4) (4 * Y) := by
      rw [add_zero]; constructor <;> linarith [ht'.1, ht'.2]
    have hB : c03_mult_B S.p Y a₃ Ψ 0 t = ((3 : ℝ) ^ S.p * fam_lambda S.p ε μ t ^ S.p : ℝ) *
        c05_standing_A S.p ε μ t ^ 3 := by
      unfold c03_mult_B c03_mult_F
      simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      rw [if_pos hmem]
      have hlt : 0 ≤ fam_lambda S.p ε μ t := by
        have h := ((hH 0).2 t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩).1.1
        rw [(hΦd t ht0).deriv] at h
        exact le_trans (by positivity) h
      rw [(hΨd t ht0).deriv, Real.mul_rpow (by norm_num) hlt]
      unfold c03_mult_Theta
      simp only [ha₃, hχ, add_zero, sub_self, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
        mul_one, Complex.ofReal_one, one_mul]
      try (push_cast; ring)
    simp only [hG, hR1]
    unfold c03_mult_R
    rw [show 2 * 1 - 1 = 1 from rfl, Finset.sum_range_one, hB, ← hfun, mul_sub, ← mul_assoc,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul, hZ3]
    push_cast; ring
  have hyI : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hev : (fun t => fracDC S.p (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3) t -
      (((3 : ℝ) ^ S.p * fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * fam_Z S.p R ε μ t ^ 3) =ᶠ[nhds y] G :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hyI.1 hyI.2) heq
  -- exponent bookkeeping
  have hΛp : Λ ^ (S.p - 1) = Y ^ (1 - 1 / S.p) := by
    rw [hΛ, ← Real.rpow_mul hY0.le]; congr 1; field_simp
  have hX0 : A * Y ^ (-(1 : ℝ)) * Λ ^ (S.p - 1) = Y ^ (1 - 5 * beta S.p) := by
    rw [hΛp, hA, ← Real.rpow_add hY0, ← Real.rpow_add hY0]; congr 1; linarith
  have hX1 : A * Y ^ (-(1 + 1 : ℝ)) * Λ ^ (S.p - 1) ≤ Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
    rw [hΛp, hA, ← Real.rpow_add hY0, ← Real.rpow_add hY0]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by have := one_div_pos.mpr hp0; linarith)
  have hX2 : Λ * Y ^ (1 - 5 * beta S.p) = Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
    rw [hΛ, ← Real.rpow_add hY0]; ring_nf
  have hEn : ‖Complex.exp (Complex.I * (Ψ y : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hlam : fam_lambda S.p ε μ y ≤ cs⁻¹ * Λ := by
    have h := ((hH 0).2 y ⟨by linarith [hy.1], by linarith [hy.2]⟩).1.2.1
    rwa [(hΦd y hYy).deriv] at h
  have hlam0 : 0 ≤ fam_lambda S.p ε μ y := by
    have h := ((hH 0).2 y ⟨by linarith [hy.1], by linarith [hy.2]⟩).1.1
    rw [(hΦd y hYy).deriv] at h
    exact le_trans (by positivity) h
  have hYb : 0 ≤ Y ^ (1 - 5 * beta S.p + 1 / S.p) := (Real.rpow_pos_of_pos hY0 _).le
  have hYa : 0 ≤ Y ^ (1 - 5 * beta S.p) := (Real.rpow_pos_of_pos hY0 _).le
  interval_cases j
  · rw [iteratedDeriv_zero, hev.eq_of_nhds]
    simp only [hG, norm_mul, hEn, one_mul, Nat.cast_zero, zero_div, add_zero]
    rw [← hX0]
    calc ‖R1 y‖ ≤ C0 * A * Y ^ (-(1 : ℝ)) * Λ ^ (S.p - 1) := hR0b
      _ = C0 * (A * Y ^ (-(1 : ℝ)) * Λ ^ (S.p - 1)) := by ring
      _ ≤ (C0 + 3 * cs⁻¹ * C0 + C1) * (A * Y ^ (-(1 : ℝ)) * Λ ^ (S.p - 1)) := by
          gcongr
          have : 0 ≤ 3 * cs⁻¹ * C0 := by positivity
          linarith
  · rw [iteratedDeriv_one, hev.deriv_eq]
    simp only [Nat.cast_one]
    have hR0b' : ‖R1 y‖ ≤ C0 * Y ^ (1 - 5 * beta S.p) := by
      rw [← hX0]; calc _ ≤ _ := hR0b
        _ = _ := by ring
    have hR1b' : ‖deriv R1 y‖ ≤ C1 * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
      calc _ ≤ _ := hR1b
        _ = C1 * (A * Y ^ (-(1 + 1 : ℝ)) * Λ ^ (S.p - 1)) := by ring
        _ ≤ _ := by gcongr
    by_cases hd : DifferentiableAt ℝ R1 y
    · have he : HasDerivAt (fun t => Complex.exp (Complex.I * (Ψ t : ℂ)))
          (Complex.exp (Complex.I * (Ψ y : ℂ)) * (Complex.I * ((3 * fam_lambda S.p ε μ y : ℝ) : ℂ))) y :=
        ((hΨd y hYy).ofReal_comp.const_mul Complex.I).cexp
      have hGd : HasDerivAt G (Complex.exp (Complex.I * (Ψ y : ℂ)) *
          (Complex.I * ((3 * fam_lambda S.p ε μ y : ℝ) : ℂ)) * R1 y +
          Complex.exp (Complex.I * (Ψ y : ℂ)) * deriv R1 y) y := he.mul hd.hasDerivAt
      rw [hGd.deriv]
      calc ‖Complex.exp (Complex.I * (Ψ y : ℂ)) * (Complex.I * ((3 * fam_lambda S.p ε μ y : ℝ) : ℂ)) *
            R1 y + Complex.exp (Complex.I * (Ψ y : ℂ)) * deriv R1 y‖
          ≤ (3 * fam_lambda S.p ε μ y) * ‖R1 y‖ + ‖deriv R1 y‖ := by
            refine (norm_add_le _ _).trans (le_of_eq ?_)
            have h3 : 0 ≤ 3 * fam_lambda S.p ε μ y := by positivity
            simp only [norm_mul, hEn, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg h3, abs_of_nonneg hlam0]; ring
        _ ≤ (3 * (cs⁻¹ * Λ)) * (C0 * Y ^ (1 - 5 * beta S.p)) +
            C1 * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by gcongr
        _ = (3 * cs⁻¹ * C0) * Y ^ (1 - 5 * beta S.p + 1 / S.p) +
            C1 * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by rw [← hX2]; ring
        _ ≤ _ := by nlinarith
    · have hGd : ¬ DifferentiableAt ℝ G y := by
        intro hG'
        apply hd
        have : R1 = fun t => Complex.exp (-(Complex.I * (Ψ t : ℂ))) * G t := by
          funext t; simp only [hG]; rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel,
            Complex.exp_zero, one_mul]
        rw [this]
        exact ((((hΨd y hYy).ofReal_comp.const_mul Complex.I).neg.cexp).differentiableAt).mul hG'
      rw [deriv_zero_of_not_differentiableAt hGd, norm_zero]
      positivity

/-- Helper (from lem:c05_far_localization, lem:c05_osc_split_bounds, lem:c05_symbol_bounds):
on `(Y/2,3Y)`, `ℛ_{lin,3} = 2c_cubic Re[|D|^p(χ_Y Z³) - 3^p λ^p Z³] + f_{osc,3} + ℛ_{far,Y}[f_{osc,3}]`. -/
theorem c05_aux_Rlin3_identity (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ∀ t ∈ Ioo (Y / 2) (3 * Y),
        c05_E5_remainders_Rlin3 S.p R ε μ t =
          2 * c_cubic S.p ε *
              (fracDC S.p (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3) t -
                (((3 : ℝ) ^ S.p * fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * fam_Z S.p R ε μ t ^ 3).re +
            c05_E5_remainders_fosc3 S.p R ε μ t +
            c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc3 S.p R ε μ) t := by
  obtain ⟨Ra, hRa, Ca, hCa, hosc⟩ := c05_osc_split_bounds S
  obtain ⟨Rb, hRb, Cb, hCb, hfar⟩ := c05_far_localization S
  obtain ⟨Rc, hRc, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  refine ⟨max (max Ra Rb) Rc, le_max_of_le_right hRc, ?_⟩
  intro ε μ R Y ht t htI
  have hta := c05_aux_tuple_mono (show Ra ≤ max (max Ra Rb) Rc by simp) ht
  have htb := c05_aux_tuple_mono (show Rb ≤ max (max Ra Rb) Rc by simp) ht
  have htc := c05_aux_tuple_mono (show Rc ≤ max (max Ra Rb) Rc by simp) ht
  have hR : 1 ≤ R := hRc.trans htc.2.2.2.1
  have hY8 : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsym0 ε μ R Y htc t ht'.le).1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  obtain ⟨-, hs3, hz, ⟨M, hM⟩, -, hder, -, -, hi3, -⟩ := hosc ε μ R Y hta
  obtain ⟨hid, -, -, -⟩ := hfar ε μ R Y htb _ hs3 ⟨M, fun x => ⟨(hM x).2.2.1, (hM x).2.2.2⟩⟩ hi3
    (fun x hx => (hz x hx).2)
  have hRY : R < 3 * Y / 10 := by linarith
  obtain ⟨hcm, hcs⟩ := c05_aux_cutoff_mul (n := 1) (f := fun z => fam_Z S.p R ε μ z ^ 3) hY0 hRY
    (fun t ht' => ((c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos ht').2.1.pow
      3).of_le (by norm_num))
  set g : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3 with hg
  set h : ℝ → ℂ := fun z => ((2 * c_cubic S.p ε : ℝ) : ℂ) * g z with hh
  have hhC : ContDiff ℝ 1 h := contDiff_const.mul hcm
  have hhb : ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M :=
    hhC.continuous.bounded_above_of_compact_support (hcs.mul_left)
  have hfun : (fun z => res_chiY Y z * deriv (c05_E5_remainders_fosc3 S.p R ε μ) z) =
      fun z => (h z).re := by
    funext z
    simp only [hh, hg]
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    rcases le_or_gt z (3 * Y / 10) with hz' | hz'
    · rw [c05_aux_chiY_zero hY0 (Or.inl hz')]; ring
    · rw [(hder z (by linarith)).2]; ring
  unfold c05_E5_remainders_Rlin3 fracDdy
  rw [show fracD S.p (deriv (c05_E5_remainders_fosc3 S.p R ε μ)) t =
      fracDdy S.p (c05_E5_remainders_fosc3 S.p R ε μ) t from rfl, hid t htI, hfun,
    c05_aux_fracD_re S.p hp0 S.hp_hi h hhC hhb t, hh, c05_aux_fracDC_const_mul,
    Complex.re_ofReal_mul, Complex.sub_re, Complex.re_ofReal_mul]
  ring

/-- Blueprint: lem:c05_third_harmonic_bound.  On `[Y,2Y]`, `j = 0,1`:
`|∂^j ℛ_{lin,3}| ≤ Cε(Y^{1-5β+j/p} + Y^{-p-2-j}) ≤ CεY^{-2p-1+j/p}`. -/
theorem c05_third_harmonic_bound (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (c05_E5_remainders_Rlin3 S.p R ε μ) y| ≤
              C * ε * (Y ^ (1 - 5 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j)) ∧
            |iteratedDeriv j (c05_E5_remainders_Rlin3 S.p R ε μ) y| ≤
              C * ε * Y ^ (-2 * S.p - 1 + j / S.p) := by
  obtain ⟨Ri, hRi, hid⟩ := c05_aux_Rlin3_identity S
  obtain ⟨Rm, hRm, CM, hCM, hmult⟩ := c05_multiplier_third S
  obtain ⟨C0, hC0, hsmall⟩ := c05_small_constants S
  obtain ⟨Rf, hRf, CF, hCF, hfar⟩ := c05_far_localization S
  obtain ⟨Ro, hRo, CO, hCO, hosc⟩ := c05_osc_split_bounds S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, hCs, hsym0⟩ := hsym 0
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have h2β := c05_aux_two_beta S.p hp0
  have h5β := c05_aux_five_beta S.p hp0 S.hp_hi
  have hβ0 : 0 < beta S.p := by unfold beta; positivity
  obtain ⟨-, -, hcmpb0, hcmpb1⟩ := c05_aux_exponents S.p hp0 S.hp_hi
  set R₀ := max (max Ri Rm) (max (max Rf Ro) Rs) with hR₀
  have hi : Ri ≤ R₀ := by simp [hR₀]
  have hm : Rm ≤ R₀ := by simp [hR₀]
  have hf : Rf ≤ R₀ := by simp [hR₀]
  have ho : Ro ≤ R₀ := by simp [hR₀]
  have hs : Rs ≤ R₀ := by simp [hR₀]
  set C₁ := 2 * C0 * CM + CO + CF * CO + 2 * C0 * Cs with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨R₀, hRi.trans hi, 2 * C₁, by positivity, ?_⟩
  intro ε μ R Y ht y hy j hj
  have hε : 0 ≤ ε := ht.1
  have hR : 1 ≤ R := (hRi.trans hi).trans ht.2.2.2.1
  have hY8 : 8 * R ≤ Y := ht.2.2.2.2
  have hY : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hyY : Y ≤ y := hy.1
  have hyR : R < y := by linarith
  have hy0 : 0 < y := by linarith
  have hyI : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hI : Ioo (Y / 2) (3 * Y) ∈ nhds y := isOpen_Ioo.mem_nhds hyI
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsym0 ε μ R Y (c05_aux_tuple_mono hs ht) t ht'.le).1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  have hidy := hid ε μ R Y (c05_aux_tuple_mono hi ht)
  have hmb := hmult ε μ R Y (c05_aux_tuple_mono hm ht) y hy j hj
  have hc : |c_cubic S.p ε| ≤ C0 * ε := by
    have := hsmall ε μ hε ht.2.1 ht.2.2.1
    linarith [abs_nonneg (c_eps S.p ε), abs_nonneg (n_eps S.p ε), abs_nonneg (c_log S.p ε μ)]
  obtain ⟨-, hs3, hz, ⟨M, hM⟩, -, hder, hsz, -, hi3, hL1⟩ :=
    hosc ε μ R Y (c05_aux_tuple_mono ho ht)
  obtain ⟨-, -, hfC1, hfb⟩ := hfar ε μ R Y (c05_aux_tuple_mono hf ht) _ hs3
    ⟨M, fun x => ⟨(hM x).2.2.1, (hM x).2.2.2⟩⟩ hi3 (fun x hx => (hz x hx).2)
  have hL1' : ∫ x, |c05_E5_remainders_fosc3 S.p R ε μ x| ≤ CO * ε := by
    have : 0 ≤ ∫ x, |c05_E5_remainders_fosc1 S.p R ε μ x| :=
      integral_nonneg (fun _ => abs_nonneg _)
    linarith
  have hYpow : ∀ a : ℝ, a ≤ 0 → y ^ a ≤ Y ^ a := fun a ha =>
    Real.rpow_le_rpow_of_nonpos hY0 hyY ha
  have hfbj := hfb y ⟨hy.1, hy.2⟩ j hj
  have hFb : CF * Y ^ (-S.p - 2 - j) * ∫ x, |c05_E5_remainders_fosc3 S.p R ε μ x| ≤
      CF * CO * ε * Y ^ (-S.p - 2 - j) := by
    calc _ ≤ CF * Y ^ (-S.p - 2 - j) * (CO * ε) := by gcongr
      _ = _ := by ring
  set Mf : ℝ → ℂ := fun t => fracDC S.p (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3) t -
    (((3 : ℝ) ^ S.p * fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * fam_Z S.p R ε μ t ^ 3 with hMf
  have hcM : |2 * c_cubic S.p ε| * ‖iteratedDeriv j Mf y‖ ≤
      2 * C0 * CM * ε * Y ^ (1 - 5 * beta S.p + j / S.p) := by
    rw [abs_mul, abs_two]
    calc 2 * |c_cubic S.p ε| * ‖iteratedDeriv j Mf y‖ ≤
        2 * (C0 * ε) * (CM * Y ^ (1 - 5 * beta S.p + j / S.p)) := by gcongr
      _ = _ := by ring
  have hmain : |iteratedDeriv j (c05_E5_remainders_Rlin3 S.p R ε μ) y| ≤
      C₁ * ε * (Y ^ (1 - 5 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j)) := by
    have hYa : 0 ≤ Y ^ (1 - 5 * beta S.p + j / S.p) := by positivity
    have hYb : 0 ≤ Y ^ (-S.p - 2 - j) := by positivity
    interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero, sub_zero] at hfbj hFb hcM hYa hYb ⊢
      rw [hidy y hyI]
      have e1 : |2 * c_cubic S.p ε * (Mf y).re| ≤ 2 * C0 * CM * ε * Y ^ (1 - 5 * beta S.p) := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)).trans hcM
      have e2 : |c05_E5_remainders_fosc3 S.p R ε μ y| ≤ CO * ε * Y ^ (1 - 5 * beta S.p) := by
        have h1 := (hsz y hyR.le).1
        rw [show -3 * beta S.p - 1 / S.p = 1 - 5 * beta S.p by linarith] at h1
        have h2 := hYpow (1 - 5 * beta S.p) (by linarith)
        calc _ ≤ CO * ε * y ^ (1 - 5 * beta S.p) := h1
          _ ≤ _ := by gcongr
      have a1 := abs_add_le (2 * c_cubic S.p ε * (Mf y).re + c05_E5_remainders_fosc3 S.p R ε μ y)
        (c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc3 S.p R ε μ) y)
      have a2 := abs_add_le (2 * c_cubic S.p ε * (Mf y).re) (c05_E5_remainders_fosc3 S.p R ε μ y)
      have hdiff : C₁ * ε * (Y ^ (1 - 5 * beta S.p) + Y ^ (-S.p - 2)) -
          ((2 * C0 * CM + CO) * ε * Y ^ (1 - 5 * beta S.p) + CF * CO * ε * Y ^ (-S.p - 2)) =
          (CF * CO + 2 * C0 * Cs) * ε * Y ^ (1 - 5 * beta S.p) +
            (2 * C0 * CM + CO + 2 * C0 * Cs) * ε * Y ^ (-S.p - 2) := by
        rw [hC₁]; ring
      have hd1 : 0 ≤ (CF * CO + 2 * C0 * Cs) * ε * Y ^ (1 - 5 * beta S.p) := by positivity
      have hd2 : 0 ≤ (2 * C0 * CM + CO + 2 * C0 * Cs) * ε * Y ^ (-S.p - 2) := by positivity
      linarith only [e1, e2, a1, a2, hfbj, hFb, hdiff, hd1, hd2]
    · simp only [iteratedDeriv_one, Nat.cast_one] at hfbj hFb hcM hYa hYb ⊢
      obtain ⟨hlq, hZ2, -, -, -, -, -, -, -⟩ :=
        c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos hyR
      have dZ := hZ2.differentiableAt (by norm_num)
      have hRY : R < 3 * Y / 10 := by linarith
      have dfZ : DifferentiableAt ℝ
          (fracDC S.p (fun z => (res_chiY Y z : ℂ) * fam_Z S.p R ε μ z ^ 3)) y :=
        (c05_aux_fracDC_cutoff S.p S.hp_lo S.hp_hi hY0 hRY (fun t ht' =>
          (c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos ht').2.1.pow
            3)).differentiable one_ne_zero y
      have dMf : DifferentiableAt ℝ Mf y := by
        simp only [hMf]
        exact dfZ.sub ((c05_aux_ofReal_diff ((differentiableAt_const _).mul
          ((hlq S.p).differentiableAt (by norm_num)))).mul (dZ.pow 3))
      have d3 : DifferentiableAt ℝ (c05_E5_remainders_fosc3 S.p R ε μ) y :=
        hs3.differentiable (by simp) y
      have dRf : DifferentiableAt ℝ
          (c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc3 S.p R ε μ)) y :=
        (hfC1.contDiffAt hI).differentiableAt one_ne_zero
      have hG := (((c05_aux_hasDerivAt_re dMf.hasDerivAt).const_mul (2 * c_cubic S.p ε)).add
        d3.hasDerivAt).add dRf.hasDerivAt
      have hev : c05_E5_remainders_Rlin3 S.p R ε μ =ᶠ[nhds y] fun t =>
          2 * c_cubic S.p ε * (Mf t).re + c05_E5_remainders_fosc3 S.p R ε μ t +
            c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc3 S.p R ε μ) t := by
        filter_upwards [hI] with t ht' using hidy t ht'
      have hG' := hG.congr_of_eventuallyEq hev
      rw [hG'.deriv, (hder y (by linarith)).2]
      have e1 : |2 * c_cubic S.p ε * (deriv Mf y).re| ≤
          2 * C0 * CM * ε * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)).trans hcM
      have e2 : |2 * c_cubic S.p ε * (fam_Z S.p R ε μ y ^ 3).re| ≤
          2 * C0 * Cs * ε * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
        have h1 := (hsym0 ε μ R Y (c05_aux_tuple_mono hs ht) y hyR.le).2.2.1.2.1
        simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at h1
        rw [show -3 * beta S.p = 1 - 5 * beta S.p + 1 / S.p by linarith] at h1
        have h2 := hYpow (1 - 5 * beta S.p + 1 / S.p) (by linarith)
        rw [abs_mul, abs_mul, abs_two]
        calc 2 * |c_cubic S.p ε| * |(fam_Z S.p R ε μ y ^ 3).re| ≤
            2 * (C0 * ε) * (Cs * Y ^ (1 - 5 * beta S.p + 1 / S.p)) := by
              gcongr
              exact (Complex.abs_re_le_norm _).trans (h1.trans (by gcongr))
          _ = _ := by ring
      have a1 := abs_add_le (2 * c_cubic S.p ε * (deriv Mf y).re +
          2 * c_cubic S.p ε * (fam_Z S.p R ε μ y ^ 3).re)
        (deriv (c05_auxiliary_remainders_Rfar S.p Y (c05_E5_remainders_fosc3 S.p R ε μ)) y)
      have a2 := abs_add_le (2 * c_cubic S.p ε * (deriv Mf y).re)
        (2 * c_cubic S.p ε * (fam_Z S.p R ε μ y ^ 3).re)
      have hdiff : C₁ * ε * (Y ^ (1 - 5 * beta S.p + 1 / S.p) + Y ^ (-S.p - 2 - 1)) -
          ((2 * C0 * CM + 2 * C0 * Cs) * ε * Y ^ (1 - 5 * beta S.p + 1 / S.p) +
            CF * CO * ε * Y ^ (-S.p - 2 - 1)) =
          (CO + CF * CO) * ε * Y ^ (1 - 5 * beta S.p + 1 / S.p) +
            (2 * C0 * CM + CO + 2 * C0 * Cs) * ε * Y ^ (-S.p - 2 - 1) := by
        rw [hC₁]; ring
      have hd1 : 0 ≤ (CO + CF * CO) * ε * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by positivity
      have hd2 : 0 ≤ (2 * C0 * CM + CO + 2 * C0 * Cs) * ε * Y ^ (-S.p - 2 - 1) := by positivity
      linarith only [e1, e2, a1, a2, hfbj, hFb, hdiff, hd1, hd2]
  refine ⟨hmain.trans ?_, hmain.trans ?_⟩
  · have : 0 ≤ C₁ * ε * (Y ^ (1 - 5 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j)) := by
      positivity
    linarith
  · have ha : Y ^ (1 - 5 * beta S.p + j / S.p) ≤ Y ^ (-2 * S.p - 1 + j / S.p) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    have hb : Y ^ (-S.p - 2 - j) ≤ Y ^ (-2 * S.p - 1 + j / S.p) := by
      refine Real.rpow_le_rpow_of_exponent_le hY ?_
      interval_cases j
      · simp only [Nat.cast_zero, sub_zero, zero_div, add_zero]; linarith
      · simp only [Nat.cast_one]; linarith
    calc C₁ * ε * (Y ^ (1 - 5 * beta S.p + j / S.p) + Y ^ (-S.p - 2 - j))
        ≤ C₁ * ε * (Y ^ (-2 * S.p - 1 + j / S.p) + Y ^ (-2 * S.p - 1 + j / S.p)) := by
          gcongr
      _ = 2 * C₁ * ε * Y ^ (-2 * S.p - 1 + j / S.p) := by ring

/-- Helper (regularity, from lem:c05_osc_split_bounds, lem:c05_far_localization,
lem:c05_symbol_bounds): `|D|^p f_{osc,ν}'` is `C¹` on `(Y/2,3Y)` and `ℛ_{lin,1}`, `ℛ_{lin,3}` are
`C¹` near every `y ∈ (Y/2,3Y)`. -/
theorem c05_aux_Rlin_parts_C1 (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ∀ y ∈ Ioo (Y / 2) (3 * Y),
        ContDiffAt ℝ 1 (fracDdy S.p (c05_E5_remainders_fosc1 S.p R ε μ)) y ∧
        ContDiffAt ℝ 1 (fracDdy S.p (c05_E5_remainders_fosc3 S.p R ε μ)) y ∧
        ContDiffAt ℝ 1 (c05_E5_remainders_Rlin1 S.p R ε μ) y ∧
        ContDiffAt ℝ 1 (c05_E5_remainders_Rlin3 S.p R ε μ) y := by
  obtain ⟨Ra, hRa, Ca, hCa, hosc⟩ := c05_osc_split_bounds S
  obtain ⟨Rb, hRb, Cb, hCb, hfar⟩ := c05_far_localization S
  obtain ⟨Rc, hRc, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, hCs, hsym0⟩ := hsym 0
  refine ⟨max (max Ra Rb) Rc, le_max_of_le_right hRc, ?_⟩
  intro ε μ R Y ht y hy
  have hta := c05_aux_tuple_mono (show Ra ≤ max (max Ra Rb) Rc by simp) ht
  have htb := c05_aux_tuple_mono (show Rb ≤ max (max Ra Rb) Rc by simp) ht
  have htc := c05_aux_tuple_mono (show Rc ≤ max (max Ra Rb) Rc by simp) ht
  have hR : 1 ≤ R := hRc.trans htc.2.2.2.1
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hyR : R ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  have hR0 : 0 < R := by linarith
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  obtain ⟨hs1, hs3, hz, ⟨M, hM⟩, -, -, -, hi1, hi3, -⟩ := hosc ε μ R Y hta
  have hlam : fam_lambda S.p ε μ y ≠ 0 := by
    have := (hsym0 ε μ R Y htc y hyR).1.1
    have : 0 < y ^ (1 / S.p) / 2 := by positivity
    linarith
  have hopen : Ioo (Y / 2) (3 * Y) ∈ nhds y := isOpen_Ioo.mem_nhds hy
  have hfrac : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → (∃ M : ℝ, ∀ x, |g x| ≤ M ∧ |deriv g x| ≤ M) →
      Integrable g → (∀ x, x ≤ R → g x = 0) → ContDiffAt ℝ 1 (fracDdy S.p g) y := by
    intro g hg hgM hgi hg0
    obtain ⟨hid, hc1, hc2, -⟩ := hfar ε μ R Y htb g hg hgM hgi hg0
    have := ((hc1.contDiffAt hopen).add (hc2.contDiffAt hopen))
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hopen] with t ht' using hid t ht'
  have hf1 := hfrac _ hs1 ⟨M, fun x => ⟨(hM x).1, (hM x).2.1⟩⟩ hi1 (fun x hx => (hz x hx).1)
  have hf3 := hfrac _ hs3 ⟨M, fun x => ⟨(hM x).2.2.1, (hM x).2.2.2⟩⟩ hi3 (fun x hx => (hz x hx).2)
  have hlp : ContDiffAt ℝ 1 (fun t => fam_lambda S.p ε μ t ^ S.p) y :=
    (c05_aux_lambda_smooth S.p ε μ hy0).rpow_const_of_ne hlam
  have hZ : ContDiffAt ℝ 1 (fam_Z S.p R ε μ) y :=
    c05_aux_Z_smooth S.p R ε μ S.hp_lo S.hp_hi hR0 hy0 hlam (n := 1)
  have hZ0 : ContDiffAt ℝ 1 (c05_standing_Zmu0 S.p R μ) y :=
    c05_aux_Zmu0_smooth S.p R μ S.hp_lo S.hp_hi hR0 hy0 (n := 1)
  refine ⟨hf1, hf3, ?_, ?_⟩
  · unfold c05_E5_remainders_Rlin1
    exact ((hf1.add (hs1.contDiffAt.of_le (by exact_mod_cast le_top))).sub
      ((contDiffAt_const.mul hlp).mul (c05_aux_re hZ))).add
      ((contDiffAt_const.mul contDiffAt_id).mul (c05_aux_re hZ0))
  · unfold c05_E5_remainders_Rlin3
    exact (hf3.add (hs3.contDiffAt.of_le (by exact_mod_cast le_top))).sub
      ((contDiffAt_const.mul hlp).mul (c05_aux_re (hZ.pow 3)))

/-- Blueprint: prop:approx_E5_linear.  For `y ∈ [Y,2Y]`: `ℛ_lin` is `C¹` near `y` and
`|∂_y^j ℛ_lin(y)| ≤ C ε ⟨y⟩^{-2p-1+j/p}`, `j = 0,1`. -/
theorem approx_E5_linear (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y),
          ContDiffAt ℝ 1 (c05_E5_remainders_Rlin S.p R ε μ) y ∧
          ∀ j : ℕ, j ≤ 1 →
            |iteratedDeriv j (c05_E5_remainders_Rlin S.p R ε μ) y| ≤
              C * ε * jb y ^ (-2 * S.p - 1 + j / S.p) := by
  obtain ⟨Ra, hRa, Ca, hCa, hfund⟩ := c05_fundamental_bound S
  obtain ⟨Rb, hRb, Cb, hCb, hthird⟩ := c05_third_harmonic_bound S
  obtain ⟨Rc, hRc, hreg⟩ := c05_aux_Rlin_parts_C1 S
  obtain ⟨Rd, hRd, hsplit⟩ := c05_E5_split S
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  set R₀ := max (max Ra Rb) (max Rc Rd) with hR₀
  have ha : Ra ≤ R₀ := by simp [hR₀]
  have hb : Rb ≤ R₀ := by simp [hR₀]
  have hc : Rc ≤ R₀ := by simp [hR₀]
  have hd : Rd ≤ R₀ := by simp [hR₀]
  set T := 2 * S.p + 1 + 1 / S.p
  refine ⟨R₀, hRa.trans ha, 3 ^ T * (Ca + Cb), by positivity, ?_⟩
  intro ε μ R Y ht y hy
  have hε : 0 ≤ ε := ht.1
  have hR : 1 ≤ R := (hRa.trans ha).trans ht.2.2.2.1
  have hY : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hy2R : 2 * R < y := by linarith [ht.2.2.2.2, hy.1]
  have hyI : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨-, -, hC1, hC3⟩ := hreg ε μ R Y (c05_aux_tuple_mono hc ht) y hyI
  have hev : c05_E5_remainders_Rlin S.p R ε μ =ᶠ[nhds y]
      fun t => c05_E5_remainders_Rlin1 S.p R ε μ t + c05_E5_remainders_Rlin3 S.p R ε μ t := by
    filter_upwards [isOpen_Ioi.mem_nhds (show y ∈ Ioi (2 * R) from hy2R)] with t ht'
    exact (hsplit ε μ R Y (c05_aux_tuple_mono hd ht) t ht').2
  refine ⟨(hC1.add hC3).congr_of_eventuallyEq hev, fun j hj => ?_⟩
  have hsum : iteratedDeriv j (c05_E5_remainders_Rlin S.p R ε μ) y =
      iteratedDeriv j (c05_E5_remainders_Rlin1 S.p R ε μ) y +
        iteratedDeriv j (c05_E5_remainders_Rlin3 S.p R ε μ) y := by
    interval_cases j
    · simp only [iteratedDeriv_zero]; exact hev.eq_of_nhds
    · simp only [iteratedDeriv_one]
      rw [hev.deriv_eq]
      exact deriv_add (hC1.differentiableAt one_ne_zero) (hC3.differentiableAt one_ne_zero)
  have h1 := (hfund ε μ R Y (c05_aux_tuple_mono ha ht) y hy j hj).2
  have h3 := (hthird ε μ R Y (c05_aux_tuple_mono hb ht) y hy j hj).2
  have hθ : |-2 * S.p - 1 + j / S.p| ≤ T := by
    have hj' : (j : ℝ) / S.p ≤ 1 / S.p := by
      gcongr; exact_mod_cast hj
    have hj0 : 0 ≤ (j : ℝ) / S.p := by positivity
    rw [abs_le]; constructor <;> linarith
  have hconv := c05_aux_rpow_Y_jb hY hy hθ
  rw [hsum]
  calc _ ≤ |iteratedDeriv j (c05_E5_remainders_Rlin1 S.p R ε μ) y| +
        |iteratedDeriv j (c05_E5_remainders_Rlin3 S.p R ε μ) y| := abs_add_le _ _
    _ ≤ Ca * ε * Y ^ (-2 * S.p - 1 + j / S.p) + Cb * ε * Y ^ (-2 * S.p - 1 + j / S.p) :=
        add_le_add h1 h3
    _ = (Ca + Cb) * ε * Y ^ (-2 * S.p - 1 + j / S.p) := by ring
    _ ≤ (Ca + Cb) * ε * (3 ^ T * jb y ^ (-2 * S.p - 1 + j / S.p)) := by gcongr
    _ = _ := by ring

/-! ### The cubic remainder `ℛ_cub` -/

/-- Helper: `|f a - f b| ≤ M |a - b|` when `|f'| ≤ M`. -/
theorem c05_aux_incr_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ}
    (hM : ∀ x, |deriv f x| ≤ M) (a b : ℝ) : |f a - f b| ≤ M * |a - b| := by
  have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hf x) (fun x _ => by rw [Real.norm_eq_abs]; exact hM x) (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using this

/-- Helper: the kernel `k_p(s) = |s|^{-p}` (`|s| ≤ 1`), `|s|^{-p-1}` (`|s| > 1`). -/
def c05_aux_kp (p s : ℝ) : ℝ := if |s| ≤ 1 then |s| ^ (-p) else |s| ^ (-p - 1)

theorem c05_aux_kp_nonneg (p s : ℝ) : 0 ≤ c05_aux_kp p s := by
  unfold c05_aux_kp; split_ifs <;> exact Real.rpow_nonneg (abs_nonneg s) _

theorem c05_aux_kp_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Integrable (c05_aux_kp p) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith : -1 < -p)).1
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hφ : IntegrableOn (fun t : ℝ => if t ≤ 1 then t ^ (-p) else t ^ (-p - 1)) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    refine IntegrableOn.union ?_ ?_
    · refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioc
      simp only
      simp only [ht.2, ↓reduceIte]
    · refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
      simp only
      simp only [not_le.mpr (show (1:ℝ) < t from ht), ↓reduceIte]
  refine (c04_aux_c01_integrable_comp_abs hφ).congr (Eventually.of_forall fun s => ?_)
  simp only [c05_aux_kp]

theorem c05_aux_kp_bound (p K X s : ℝ) (hp : 0 < p) (hK : 0 ≤ K)
    (h1 : |s| ≤ 1 → X ≤ K * |s| ^ 3) (h2 : X ≤ K) :
    |s| ^ (-p - 3) * X ≤ K * c05_aux_kp p s := by
  unfold c05_aux_kp
  split_ifs with hs
  · rcases eq_or_ne s 0 with rfl | hs0
    · simp only [abs_zero]; rw [Real.zero_rpow (by linarith), zero_mul]
      exact mul_nonneg hK (Real.rpow_nonneg le_rfl _)
    · have ha : 0 < |s| := abs_pos.mpr hs0
      calc |s| ^ (-p - 3) * X ≤ |s| ^ (-p - 3) * (K * |s| ^ 3) :=
            mul_le_mul_of_nonneg_left (h1 hs) (Real.rpow_nonneg ha.le _)
        _ = K * (|s| ^ (3:ℕ) * |s| ^ (-p - 3)) := by ring
        _ = K * |s| ^ (-p) := by rw [c05_aux_rpow_mul_npow ha]; congr 2; push_cast; ring
  · have ha : 1 ≤ |s| := (not_le.mp hs).le
    calc |s| ^ (-p - 3) * X ≤ |s| ^ (-p - 3) * K :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ |s| ^ (-p - 1) * K := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le ha (by linarith)) hK
      _ = K * |s| ^ (-p - 1) := mul_comm _ _

/-- Helper: increment bounds `|Δh(y,s)| ≤ min(M|s|, 2M)` for `|h| ≤ M`, `|h'| ≤ M`. -/
theorem c05_aux_Delta_bounds {h : ℝ → ℝ} (hd : Differentiable ℝ h) {M : ℝ}
    (h0 : ∀ x, |h x| ≤ M) (h1 : ∀ x, |deriv h x| ≤ M) (y s : ℝ) :
    |c05_plane_wave_Delta h y s| ≤ M * |s| ∧ |c05_plane_wave_Delta h y s| ≤ 2 * M := by
  unfold c05_plane_wave_Delta
  refine ⟨?_, ?_⟩
  · have := c05_aux_incr_le hd h1 y (y - s)
    rwa [show y - (y - s) = s by ring] at this
  · calc |h y - h (y - s)| ≤ |h y| + |h (y - s)| := abs_sub _ _
      _ ≤ 2 * M := by linarith [h0 y, h0 (y - s)]

/-- Helper: `|d|^{-p-3} = 1/(|d|^{p+1} d²)` for `d ≠ 0`. -/
theorem c05_aux_rpow_p3 (p d : ℝ) (hd : d ≠ 0) :
    |d| ^ (-p - 3) = 1 / (|d| ^ (p + 1) * d ^ 2) := by
  have ha : 0 < |d| := abs_pos.mpr hd
  rw [show -p - 3 = -(p + 1) - 2 by ring, Real.rpow_sub ha, Real.rpow_neg ha.le,
    show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  field_simp


/-- Helper: the `s`-form integrand of `𝒬_{ε,3}(v)(y)` is dominated by `8M³ k_p`. -/
theorem c05_aux_Q3_dom (p : ℝ) (hp : 0 < p) (v : ℝ → ℝ) (hd : Differentiable ℝ v)
    (hd' : Differentiable ℝ (deriv v)) (M : ℝ)
    (hM : ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M) (y s : ℝ) :
    ‖|s| ^ (-p - 3) * c05_plane_wave_Delta (deriv v) y s * c05_plane_wave_Delta v y s ^ 2‖ ≤
      8 * M ^ 3 * c05_aux_kp p s := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0).1
  obtain ⟨a1, a2⟩ := c05_aux_Delta_bounds hd (fun x => (hM x).1) (fun x => (hM x).2.1) y s
  obtain ⟨b1, b2⟩ := c05_aux_Delta_bounds hd' (fun x => (hM x).2.1) (fun x => (hM x).2.2) y s
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg s) _),
    abs_pow, mul_assoc]
  apply c05_aux_kp_bound p _ _ s hp (by positivity)
  · intro _
    calc |c05_plane_wave_Delta (deriv v) y s| * |c05_plane_wave_Delta v y s| ^ 2
        ≤ (M * |s|) * (M * |s|) ^ 2 := by gcongr
      _ ≤ 8 * M ^ 3 * |s| ^ 3 := by
          have : 0 ≤ M ^ 3 * |s| ^ 3 := by positivity
          nlinarith
  · calc |c05_plane_wave_Delta (deriv v) y s| * |c05_plane_wave_Delta v y s| ^ 2
        ≤ (2 * M) * (2 * M) ^ 2 := by gcongr
      _ = 8 * M ^ 3 := by ring

/-- Helper: the `z`-form integrand of `𝒬_{ε,3}(v)(y)` equals the `s`-form at `s = y - z`
(for `z ≠ y`). -/
theorem c05_aux_Q3_pointwise (p : ℝ) (v : ℝ → ℝ) (y z : ℝ) (hz : z ≠ y) :
    (deriv v y - deriv v z) / |y - z| ^ (p + 1) * c01_secant v y z ^ 2 =
      |y - z| ^ (-p - 3) * c05_plane_wave_Delta (deriv v) y (y - z) *
        c05_plane_wave_Delta v y (y - z) ^ 2 := by
  have hd : y - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have ha : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.mpr hd) _
  unfold c05_plane_wave_Delta c01_secant
  have hz' : ¬ y = z := Ne.symm hz
  simp only [hz', ↓reduceIte]
  rw [c05_aux_rpow_p3 p _ hd, show y - (y - z) = z by ring]
  field_simp

/-- Part 1 of lem:c05_Q3_basic. -/
theorem c05_aux_Q3_part1 (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (M : ℝ) (hM : ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M) (y : ℝ) :
    Integrable (fun s => |s| ^ (-p - 3) * c05_plane_wave_Delta (deriv v) y s *
        c05_plane_wave_Delta v y s ^ 2) ∧
    Integrable (fun z => (deriv v y - deriv v z) / |y - z| ^ (p + 1) * c01_secant v y z ^ 2) ∧
      c04_cubic_part p ε v y = c05_plane_wave_K p ε *
        ∫ s, |s| ^ (-p - 3) * c05_plane_wave_Delta (deriv v) y s * c05_plane_wave_Delta v y s ^ 2 := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hv1 : ContDiff ℝ 1 (deriv v) := hv.iterate_deriv' 1 1
  have hd' : Differentiable ℝ (deriv v) := hv1.differentiable one_ne_zero
  set G : ℝ → ℝ := fun s => |s| ^ (-p - 3) * c05_plane_wave_Delta (deriv v) y s *
        c05_plane_wave_Delta v y s ^ 2 with hG
  have hGm : Measurable G := by
    have m1 : Measurable (fun s => c05_plane_wave_Delta (deriv v) y s) :=
      measurable_const.sub ((measurable_deriv v).comp (measurable_const.sub measurable_id))
    have m2 : Measurable (fun s => c05_plane_wave_Delta v y s) :=
      measurable_const.sub (hd.continuous.measurable.comp (measurable_const.sub measurable_id))
    exact ((measurable_id.abs.pow_const _).mul m1).mul (m2.pow_const 2)
  have hGi : Integrable G :=
    Integrable.mono' ((c05_aux_kp_integrable p hp hp1).const_mul (8 * M ^ 3))
      hGm.aestronglyMeasurable (Eventually.of_forall fun s => c05_aux_Q3_dom p hp v hd hd' M hM y s)
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ y := by
    have : ({y}ᶜ : Set ℝ) ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton y)
    filter_upwards [this] with z hz
    exact hz
  have hae : (fun z => (deriv v y - deriv v z) / |y - z| ^ (p + 1) * c01_secant v y z ^ 2) =ᵐ[volume]
      fun z => G (y - z) := by
    filter_upwards [hne] with z hz
    exact c05_aux_Q3_pointwise p v y z hz
  refine ⟨hGi, (hGi.comp_sub_left y).congr hae.symm, ?_⟩
  unfold c04_cubic_part
  rw [integral_congr_ae hae, integral_sub_left_eq_self G volume y]
  rfl

/-- Helper: the differentiated `s`-integrand of `𝒬_{ε,3}(v)` is dominated by `24M³ k_p`. -/
theorem c05_aux_Q3_dom' (p : ℝ) (hp : 0 < p) (v : ℝ → ℝ) (hd : Differentiable ℝ v)
    (hd' : Differentiable ℝ (deriv v)) (hd'' : Differentiable ℝ (deriv (deriv v))) (M : ℝ)
    (hM : ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M ∧
      |deriv (deriv (deriv v)) x| ≤ M) (y s : ℝ) :
    ‖|s| ^ (-p - 3) *
        (c05_plane_wave_Delta (deriv (deriv v)) y s * c05_plane_wave_Delta v y s ^ 2 +
          2 * c05_plane_wave_Delta (deriv v) y s ^ 2 * c05_plane_wave_Delta v y s)‖ ≤
      24 * M ^ 3 * c05_aux_kp p s := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0).1
  obtain ⟨a1, a2⟩ := c05_aux_Delta_bounds hd (fun x => (hM x).1) (fun x => (hM x).2.1) y s
  obtain ⟨b1, b2⟩ := c05_aux_Delta_bounds hd' (fun x => (hM x).2.1) (fun x => (hM x).2.2.1) y s
  obtain ⟨c1, c2⟩ := c05_aux_Delta_bounds hd'' (fun x => (hM x).2.2.1) (fun x => (hM x).2.2.2) y s
  set A := c05_plane_wave_Delta v y s
  set B := c05_plane_wave_Delta (deriv v) y s
  set D := c05_plane_wave_Delta (deriv (deriv v)) y s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg s) _)]
  have htri : |D * A ^ 2 + 2 * B ^ 2 * A| ≤ |D| * |A| ^ 2 + 2 * |B| ^ 2 * |A| := by
    calc _ ≤ |D * A ^ 2| + |2 * B ^ 2 * A| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_two]
  refine (mul_le_mul_of_nonneg_left htri (Real.rpow_nonneg (abs_nonneg s) _)).trans ?_
  apply c05_aux_kp_bound p _ _ s hp (by positivity)
  · intro _
    calc |D| * |A| ^ 2 + 2 * |B| ^ 2 * |A|
        ≤ (M * |s|) * (M * |s|) ^ 2 + 2 * (M * |s|) ^ 2 * (M * |s|) := by gcongr
      _ ≤ 24 * M ^ 3 * |s| ^ 3 := by
          have : 0 ≤ M ^ 3 * |s| ^ 3 := by positivity
          nlinarith
  · calc |D| * |A| ^ 2 + 2 * |B| ^ 2 * |A| ≤ (2 * M) * (2 * M) ^ 2 + 2 * (2 * M) ^ 2 * (2 * M) := by
          gcongr
      _ = 24 * M ^ 3 := by ring

/-- Part 2 of lem:c05_Q3_basic. -/
theorem c05_aux_Q3_part2 (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (v : ℝ → ℝ) (hv : ContDiff ℝ 3 v)
    (M : ℝ) (hM : ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M ∧
        |deriv (deriv (deriv v)) x| ≤ M) :
    ContDiff ℝ 1 (c04_cubic_part p ε v) ∧
      ∀ y : ℝ, deriv (c04_cubic_part p ε v) y = c05_plane_wave_K p ε *
        ∫ s, |s| ^ (-p - 3) *
          (c05_plane_wave_Delta (deriv (deriv v)) y s * c05_plane_wave_Delta v y s ^ 2 +
            2 * c05_plane_wave_Delta (deriv v) y s ^ 2 * c05_plane_wave_Delta v y s) := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hv1 : ContDiff ℝ 2 (deriv v) := hv.iterate_deriv' 2 1
  have hv2 : ContDiff ℝ 1 (deriv (deriv v)) := hv.iterate_deriv' 1 2
  have hd' : Differentiable ℝ (deriv v) := hv1.differentiable (by norm_num)
  have hd'' : Differentiable ℝ (deriv (deriv v)) := hv2.differentiable one_ne_zero
  have hM' : ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M :=
    fun x => ⟨(hM x).1, (hM x).2.1, (hM x).2.2.1⟩
  set G : ℝ → ℝ → ℝ := fun x s => |s| ^ (-p - 3) * c05_plane_wave_Delta (deriv v) x s *
        c05_plane_wave_Delta v x s ^ 2 with hG
  set G' : ℝ → ℝ → ℝ := fun x s => |s| ^ (-p - 3) *
      (c05_plane_wave_Delta (deriv (deriv v)) x s * c05_plane_wave_Delta v x s ^ 2 +
        2 * c05_plane_wave_Delta (deriv v) x s ^ 2 * c05_plane_wave_Delta v x s) with hG'
  have hQ : c04_cubic_part p ε v = fun x => c05_plane_wave_K p ε * ∫ s, G x s := by
    funext x
    exact (c05_aux_Q3_part1 p ε hp hp1 v (hv.of_le (by norm_num)) M hM' x).2.2
  have cv := hd.continuous
  have cv1 := hd'.continuous
  have cv2 := hd''.continuous
  have hG'c : ∀ s, Continuous fun x => G' x s := by
    intro s
    simp only [hG', c05_plane_wave_Delta]
    fun_prop
  have hG'm : ∀ x, AEStronglyMeasurable (G' x) volume := by
    intro x
    have m1 : Measurable (fun s => c05_plane_wave_Delta v x s) :=
      measurable_const.sub (cv.measurable.comp (measurable_const.sub measurable_id))
    have m2 : Measurable (fun s => c05_plane_wave_Delta (deriv v) x s) :=
      measurable_const.sub (cv1.measurable.comp (measurable_const.sub measurable_id))
    have m3 : Measurable (fun s => c05_plane_wave_Delta (deriv (deriv v)) x s) :=
      measurable_const.sub (cv2.measurable.comp (measurable_const.sub measurable_id))
    exact ((measurable_id.abs.pow_const _).mul ((m3.mul (m1.pow_const 2)).add
      (((m2.pow_const 2).const_mul 2).mul m1))).aestronglyMeasurable
  have hbi := (c05_aux_kp_integrable p hp hp1).const_mul (24 * M ^ 3)
  have hderiv : ∀ y, HasDerivAt (c04_cubic_part p ε v)
      (c05_plane_wave_K p ε * ∫ s, G' y s) y := by
    intro y
    rw [hQ]
    refine HasDerivAt.const_mul _ ?_
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := G) (F' := G') (x₀ := y)
      (bound := fun s => 24 * M ^ 3 * c05_aux_kp p s) univ_mem
      (Eventually.of_forall fun x =>
        (c05_aux_Q3_part1 p ε hp hp1 v (hv.of_le (by norm_num)) M hM' x).1.aestronglyMeasurable)
      (c05_aux_Q3_part1 p ε hp hp1 v (hv.of_le (by norm_num)) M hM' y).1 (hG'm y)
      (Eventually.of_forall fun s x _ => c05_aux_Q3_dom' p hp v hd hd' hd'' M hM x s) hbi
      (Eventually.of_forall fun s x _ => ?_)
    · exact h.2
    · have e1 : ∀ f : ℝ → ℝ, Differentiable ℝ f →
          HasDerivAt (fun x => c05_plane_wave_Delta f x s) (c05_plane_wave_Delta (deriv f) x s) x := by
        intro f hf
        unfold c05_plane_wave_Delta
        exact (hf x).hasDerivAt.sub ((hf (x - s)).hasDerivAt.comp_sub_const x s)
      have := ((e1 _ hd').mul ((e1 _ hd).pow 2)).const_mul (|s| ^ (-p - 3))
      convert this using 1
      · funext x; simp only [hG, Pi.mul_apply, Pi.pow_apply]; ring

      · simp only [hG', Pi.pow_apply]; push_cast; ring
  have hdf : deriv (c04_cubic_part p ε v) = fun y => c05_plane_wave_K p ε * ∫ s, G' y s :=
    funext fun y => (hderiv y).deriv
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun y => (hderiv y).differentiableAt, ?_⟩,
    fun y => (hderiv y).deriv⟩
  rw [hdf]
  exact continuous_const.mul (continuous_of_dominated hG'm
    (fun x => Eventually.of_forall fun s => c05_aux_Q3_dom' p hp v hd hd' hd'' M hM x s) hbi
    (Eventually.of_forall hG'c))

/-- Part 3 of lem:c05_Q3_basic (scaling law; holds for every differentiable `g`). -/
theorem c05_aux_Q3_part3 (p ε c κ x₀ : ℝ) (g : ℝ → ℝ) (hp : 0 < p) (hκ : 0 < κ)
    (hg : Differentiable ℝ g) (z : ℝ) :
    c04_cubic_part p ε (fun w => c * g (κ * w + x₀)) z =
      c ^ 3 * κ ^ (p + 3) * c04_cubic_part p ε g (κ * z + x₀) := by
  set h : ℝ → ℝ := fun w => c * g (κ * w + x₀) with hh
  have hdh : deriv h = fun w => c * κ * deriv g (κ * w + x₀) := by
    funext w
    have h1 : HasDerivAt (fun w : ℝ => κ * w + x₀) κ w := by
      simpa using ((hasDerivAt_id w).const_mul κ).add_const x₀
    have := ((hg (κ * w + x₀)).hasDerivAt.comp w h1).const_mul c
    exact this.deriv.trans (by ring)
  set u := κ * z + x₀
  set F : ℝ → ℝ := fun u' => (deriv g u - deriv g u') / |u - u'| ^ (p + 1) *
    c01_secant g u u' ^ 2 with hF
  have hpt : ∀ w, (deriv h z - deriv h w) / |z - w| ^ (p + 1) * c01_secant h z w ^ 2 =
      c ^ 3 * κ ^ (p + 1) * κ ^ 3 * F (κ * w + x₀) := by
    intro w
    simp only [hF, hdh, c01_secant, u]
    rcases eq_or_ne z w with rfl | hzw
    · simp [Real.zero_rpow (show p + 1 ≠ 0 by linarith)]
    · have hzw' : ¬ z = w := hzw
      have huw : ¬ κ * z + x₀ = κ * w + x₀ := by
        intro e; apply hzw; have := mul_left_cancel₀ hκ.ne' (add_right_cancel e); exact this
      simp only [hzw', huw, ↓reduceIte]
      have e1 : κ * z + x₀ - (κ * w + x₀) = κ * (z - w) := by ring
      have hd : z - w ≠ 0 := sub_ne_zero.mpr hzw
      rw [e1, abs_mul, abs_of_pos hκ, Real.mul_rpow hκ.le (abs_nonneg _)]
      have ha : 0 < |z - w| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.mpr hd) _
      have hk : 0 < κ ^ (p + 1) := Real.rpow_pos_of_pos hκ _
      simp only [hh]
      field_simp
  have hint : ∫ w, F (κ * w + x₀) = κ⁻¹ * ∫ u', F u' := by
    have := Measure.integral_comp_mul_left (fun x => F (x + x₀)) κ
    rw [this, integral_add_right_eq_self F x₀, abs_of_pos (inv_pos.mpr hκ), smul_eq_mul]
  have hQg : c04_cubic_part p ε g u = c04_cubic_part_kappa p ε * ∫ u', F u' := rfl
  rw [hQg]
  unfold c04_cubic_part
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, hint]
  have e : κ ^ (p + 3) = κ ^ (p + 1) * κ ^ 2 := by
    rw [show p + 3 = (p + 1) + (2 : ℕ) by push_cast; ring, Real.rpow_add hκ, Real.rpow_natCast]
  rw [e]
  field_simp


/-- Blueprint: lem:c05_Q3_basic.  For `v ∈ C²` with `v, v', v''` bounded the integral defining
`𝒬_{ε,3}(v)` converges absolutely and `𝒬_{ε,3}(v)(y) = K_ε ∫ |s|^{-p-3} Δv'(Δv)² ds`; for
`v ∈ C³` with `v'''` also bounded, `𝒬_{ε,3}(v) ∈ C¹` with the differentiated formula; and the
scaling law `𝒬_{ε,3}(c g(κ· + x₀))(z) = c³κ^{p+3} 𝒬_{ε,3}(g)(κz + x₀)` for `g ∈ C²_b`, `κ > 0`. -/
theorem c05_Q3_basic (S : c05_standing) (ε : ℝ) :
    (∀ v : ℝ → ℝ, ContDiff ℝ 2 v →
      (∃ M : ℝ, ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M) →
      ∀ y : ℝ,
        Integrable (fun z => (deriv v y - deriv v z) / |y - z| ^ (S.p + 1) * c01_secant v y z ^ 2) ∧
        c04_cubic_part S.p ε v y = c05_plane_wave_K S.p ε *
          ∫ s, |s| ^ (-S.p - 3) * c05_plane_wave_Delta (deriv v) y s *
            c05_plane_wave_Delta v y s ^ 2) ∧
    (∀ v : ℝ → ℝ, ContDiff ℝ 3 v →
      (∃ M : ℝ, ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M ∧
        |deriv (deriv (deriv v)) x| ≤ M) →
      ContDiff ℝ 1 (c04_cubic_part S.p ε v) ∧
      ∀ y : ℝ, deriv (c04_cubic_part S.p ε v) y = c05_plane_wave_K S.p ε *
        ∫ s, |s| ^ (-S.p - 3) *
          (c05_plane_wave_Delta (deriv (deriv v)) y s * c05_plane_wave_Delta v y s ^ 2 +
            2 * c05_plane_wave_Delta (deriv v) y s ^ 2 * c05_plane_wave_Delta v y s)) ∧
    (∀ (c κ x₀ : ℝ) (g : ℝ → ℝ), 0 < κ → ContDiff ℝ 2 g →
      (∃ M : ℝ, ∀ x, |g x| ≤ M ∧ |deriv g x| ≤ M ∧ |deriv (deriv g) x| ≤ M) →
      ∀ z : ℝ, c04_cubic_part S.p ε (fun w => c * g (κ * w + x₀)) z =
        c ^ 3 * κ ^ (S.p + 3) * c04_cubic_part S.p ε g (κ * z + x₀)) := by
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  refine ⟨fun v hv ⟨M, hM⟩ y => ?_, fun v hv ⟨M, hM⟩ => c05_aux_Q3_part2 S.p ε hp0 S.hp_hi v hv M hM,
    fun c κ x₀ g hκ hg _ z =>
      c05_aux_Q3_part3 S.p ε c κ x₀ g hp0 hκ (hg.differentiable (by norm_num)) z⟩
  obtain ⟨-, h2, h3⟩ := c05_aux_Q3_part1 S.p ε hp0 S.hp_hi v hv M hM y
  exact ⟨h2, h3⟩

/-- Blueprint: lem:c05_plane_wave_response.  For `y ≥ R`, `λ = λ(y)`, all `z`:
`𝒬_{ε,3}(P_y)(z) = 2n_ε λ^p|Z(y)|² Re(Z(y)e^{iλ(z-y)}) - 2(3^p-1)c_cubic λ^p Re(Z(y)³e^{3iλ(z-y)})`;
in particular `𝒬_{ε,3}(P_y)(y) = G(y)` and
`T_P(y) = -2n_ε λ^{p+1}|Z|² Im Z + 6(3^p-1)c_cubic λ^{p+1} Im(Z³)`. -/
theorem c05_plane_wave_response (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ∀ y : ℝ, R ≤ y →
        (∀ z : ℝ, c04_cubic_part S.p ε (c05_plane_wave S.p R ε μ y) z =
          2 * n_eps S.p ε * fam_lambda S.p ε μ y ^ S.p * ‖fam_Z S.p R ε μ y‖ ^ 2 *
              (fam_Z S.p R ε μ y *
                Complex.exp (Complex.I * ((fam_lambda S.p ε μ y * (z - y) : ℝ) : ℂ))).re -
            2 * ((3 : ℝ) ^ S.p - 1) * c_cubic S.p ε * fam_lambda S.p ε μ y ^ S.p *
              (fam_Z S.p R ε μ y ^ 3 *
                Complex.exp (3 * Complex.I * ((fam_lambda S.p ε μ y * (z - y) : ℝ) : ℂ))).re) ∧
        c04_cubic_part S.p ε (c05_plane_wave S.p R ε μ y) y = c05_plane_wave_G S.p R ε μ y ∧
        c05_plane_wave_TP S.p R ε μ y =
          -2 * n_eps S.p ε * fam_lambda S.p ε μ y ^ (S.p + 1) * ‖fam_Z S.p R ε μ y‖ ^ 2 *
              (fam_Z S.p R ε μ y).im +
            6 * ((3 : ℝ) ^ S.p - 1) * c_cubic S.p ε * fam_lambda S.p ε μ y ^ (S.p + 1) *
              (fam_Z S.p R ε μ y ^ 3).im := by
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  obtain ⟨C₃, -, hsine⟩ := c05_aux_cubic_sine_response S.p S.hp_lo S.hp_hi
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have h3 : (3 : ℝ) ^ S.p - 1 ≠ 0 := by
    have : (1 : ℝ) < 3 ^ S.p := Real.one_lt_rpow (by norm_num) hp0
    linarith
  refine ⟨Rs, hRs, fun ε μ R Y ht y hy => ?_⟩
  have hR : 1 ≤ R := hRs.trans ht.2.2.2.1
  have hy0 : 0 < y := by linarith
  set lam := fam_lambda S.p ε μ y with hlam
  have hl : 0 < lam := by
    have := (hsym0 ε μ R Y ht y hy).1.1
    have : 0 < y ^ (1 / S.p) / 2 := by positivity
    linarith
  set Z := fam_Z S.p R ε μ y with hZ
  set r := ‖Z‖
  set θ := Complex.arg Z
  have hP : c05_plane_wave S.p R ε μ y =
      fun w => (2 * r / lam) * Real.sin (lam * w + (θ - lam * y)) := by
    funext w
    unfold c05_plane_wave
    rw [c05_aux_plane_wave_sin Z lam y w hl]
  have hsin2 : ContDiff ℝ 2 Real.sin := Real.contDiff_sin.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsinb : ∃ M : ℝ, ∀ x, |Real.sin x| ≤ M ∧ |deriv Real.sin x| ≤ M ∧
      |deriv (deriv Real.sin) x| ≤ M := by
    refine ⟨1, fun x => ⟨Real.abs_sin_le_one x, ?_, ?_⟩⟩
    · rw [Real.deriv_sin]; exact Real.abs_cos_le_one x
    · rw [Real.deriv_sin, Real.deriv_cos']; simp [Real.abs_sin_le_one]
  obtain ⟨hsinf, -, -⟩ := hsine ε ht.1
  have hQ := (c05_Q3_basic S ε).2.2 (2 * r / lam) lam (θ - lam * y) Real.sin hl hsin2 hsinb
  have e1 : ∀ φ : ℝ, (Z * Complex.exp (Complex.I * (φ : ℂ))).re = r * Real.cos (θ + φ) := by
    intro φ; simpa using c05_aux_polar_re Z 1 φ
  have e3 : ∀ φ : ℝ, (Z ^ 3 * Complex.exp (3 * Complex.I * (φ : ℂ))).re =
      r ^ 3 * Real.cos (3 * θ + 3 * φ) := by
    intro φ; simpa using c05_aux_polar_re Z 3 φ
  have hpow : lam ^ (S.p + 3) = lam ^ S.p * lam ^ 3 := by
    rw [Real.rpow_add hl]; norm_num
  have hform : ∀ z : ℝ, c04_cubic_part S.p ε (c05_plane_wave S.p R ε μ y) z =
      2 * n_eps S.p ε * lam ^ S.p * r ^ 2 * (r * Real.cos (θ + lam * (z - y))) -
        2 * ((3 : ℝ) ^ S.p - 1) * c_cubic S.p ε * lam ^ S.p *
          (r ^ 3 * Real.cos (3 * θ + 3 * (lam * (z - y)))) := by
    intro z
    rw [hP, hQ z, hsinf, hpow]
    have ha : lam * z + (θ - lam * y) = θ + lam * (z - y) := by ring
    have hb : 3 * (θ + lam * (z - y)) = 3 * θ + 3 * (lam * (z - y)) := by ring
    rw [ha, hb]
    unfold n_eps c_cubic
    field_simp
    ring
  refine ⟨fun z => ?_, ?_, ?_⟩
  · rw [hform z, e1, e3]
  · rw [hform y]
    unfold c05_plane_wave_G
    rw [← hZ, ← hlam]
    have g1 : Z.re = r * Real.cos θ := by simpa using e1 0
    have g3 : (Z ^ 3).re = r ^ 3 * Real.cos (3 * θ) := by simpa using e3 0
    rw [g1, g3]
    simp only [sub_self, mul_zero, add_zero]
    ring
  · unfold c05_plane_wave_TP
    rw [show (fun z => c04_cubic_part S.p ε (c05_plane_wave S.p R ε μ y) z) =
        fun z => 2 * n_eps S.p ε * lam ^ S.p * r ^ 2 * (r * Real.cos (θ + lam * (z - y))) -
          2 * ((3 : ℝ) ^ S.p - 1) * c_cubic S.p ε * lam ^ S.p *
            (r ^ 3 * Real.cos (3 * θ + 3 * lam * (z - y))) from by
      funext z; rw [hform z]; ring_nf]
    have hd := (((c05_aux_hasDerivAt_cos θ lam y).const_mul r).const_mul
      (2 * n_eps S.p ε * lam ^ S.p * r ^ 2)).sub
      (((c05_aux_hasDerivAt_cos (3 * θ) (3 * lam) y).const_mul (r ^ 3)).const_mul
        (2 * ((3 : ℝ) ^ S.p - 1) * c_cubic S.p ε * lam ^ S.p))
    refine hd.deriv.trans ?_
    have i1 : Z.im = r * Real.sin θ := by
      have := c05_aux_polar_im Z 1
      simp only [pow_one, Nat.cast_one, one_mul] at this
      exact this
    have i3 : (Z ^ 3).im = r ^ 3 * Real.sin (3 * θ) := by simpa using c05_aux_polar_im Z 3
    rw [i1, i3, Real.rpow_add_one hl.ne']
    ring

/-- Helper: `‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖`. -/
theorem c05_aux_norm3 (x y z : ℂ) : ‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ :=
  (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- Helper: `|a| X + |b| X ≤ A T + B T` from `|a| ≤ A`, `|b| ≤ B`, `X ≤ T`. -/
theorem c05_aux_lin2 {a b A B X T : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hX : X ≤ T) (hX0 : 0 ≤ X)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : |a| * X + |b| * X ≤ A * T + B * T :=
  add_le_add (mul_le_mul ha hX hX0 hA) (mul_le_mul hb hX hX0 hB)

/-- Blueprint: lem:c05_plane_wave_parameter.  `G ∈ C¹([R,∞))` and
`|T_P(y) - G'(y)| ≤ CεY^{-3β} = CεY^{1-5β+1/p}` on `[Y,2Y]`. -/
theorem c05_plane_wave_parameter (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ContDiffOn ℝ 1 (c05_plane_wave_G S.p R ε μ) (Ici R) ∧
        ∀ y ∈ Icc Y (2 * Y),
          |c05_plane_wave_TP S.p R ε μ y - deriv (c05_plane_wave_G S.p R ε μ) y| ≤
              C * ε * Y ^ (-3 * beta S.p) ∧
            Y ^ (-3 * beta S.p) = Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, hCs, hsym0⟩ := hsym 0
  obtain ⟨Rr, hRr, hresp⟩ := c05_plane_wave_response S
  obtain ⟨C₀, hC₀, hsmall⟩ := c05_small_constants S
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hp1 := S.hp_hi
  set K3 : ℝ := (3 : ℝ) ^ S.p - 1 with hK3def
  have hK3 : 0 ≤ K3 := by
    have : (1 : ℝ) ≤ 3 ^ S.p := Real.one_le_rpow (by norm_num) hp0.le
    linarith
  set B : ℝ := (1 + Cs) * Cs ^ 3 + 6 * Cs ^ 3 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨max Rs Rr, le_max_of_le_left hRs, 2 * C₀ * (1 + K3) * B + 1, by positivity, ?_⟩
  intro ε μ R Y ht
  have hts := c05_aux_tuple_mono (show Rs ≤ max Rs Rr by simp) ht
  have htr := c05_aux_tuple_mono (show Rr ≤ max Rs Rr by simp) ht
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hε0 : 0 ≤ ε := ht.1
  have hε1 : ε ≤ 1 := ht.2.1.trans S.hε₀_le
  have hlpos : ∀ t, R ≤ t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsym0 ε μ R Y hts t ht').1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  set Z := fam_Z S.p R ε μ with hZdef
  set L : ℝ → ℂ := fun t => ((fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) with hLdef
  set a : ℝ := 2 * n_eps S.p ε with ha
  set b : ℝ := 2 * c_cubic S.p ε * K3 with hb
  set H : ℝ → ℂ := fun t => (a : ℂ) * L t * (star (Z t) * Z t ^ 2) - (b : ℂ) * L t * Z t ^ 3
    with hHdef
  have hconj : ∀ z : ℂ, star z * z ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) * z := by
    intro z; rw [Complex.star_def, sq, ← mul_assoc, Complex.conj_mul']; push_cast; ring
  have hGH : c05_plane_wave_G S.p R ε μ = fun t => (H t).re := by
    funext t
    simp only [hHdef, hLdef, hconj, Complex.sub_re]
    unfold c05_plane_wave_G
    rw [show (a : ℂ) * ((fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * (((‖Z t‖ ^ 2 : ℝ) : ℂ) * Z t) =
        ((a * fam_lambda S.p ε μ t ^ S.p * ‖Z t‖ ^ 2 : ℝ) : ℂ) * Z t by push_cast; ring,
      show (b : ℂ) * ((fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * Z t ^ 3 =
        ((b * fam_lambda S.p ε μ t ^ S.p : ℝ) : ℂ) * Z t ^ 3 by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, ha, hb, hK3def]
  -- smoothness of the ingredients at `t ≥ R`
  have hZs : ∀ t, R ≤ t → ContDiffAt ℝ 1 Z t := fun t ht' =>
    c05_aux_Z_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) (by linarith) (hlpos t ht').ne'
  have hLs : ∀ t, R ≤ t → ContDiffAt ℝ 1 (fun t => fam_lambda S.p ε μ t ^ S.p) t := fun t ht' =>
    (c05_aux_lambda_smooth S.p ε μ (by linarith)).rpow_const_of_ne (hlpos t ht').ne'
  have hstarZ : ∀ t, R ≤ t → ContDiffAt ℝ 1 (fun t => star (Z t)) t := by
    intro t ht'
    have := (Complex.conjCLE.contDiff (n := 1)).contDiffAt.comp t (hZs t ht')
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun u => ?_)
    simp
  have hHs : ∀ t, R ≤ t → ContDiffAt ℝ 1 H t := by
    intro t ht'
    exact ((contDiffAt_const.mul (c05_aux_ofReal (hLs t ht'))).mul
      ((hstarZ t ht').mul ((hZs t ht').pow 2))).sub
      ((contDiffAt_const.mul (c05_aux_ofReal (hLs t ht'))).mul ((hZs t ht').pow 3))
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hGH]
    exact fun t ht' => (c05_aux_re (hHs t ht')).contDiffWithinAt
  have hY1 : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hRy : R ≤ y := by linarith [hy.1, ht.2.2.2.2]
  have hy0 : 0 < y := by linarith
  have hYy : Y ≤ y := hy.1
  obtain ⟨⟨-, hl2, -⟩, -, ⟨hZb, -, -, hwb⟩, h4, -⟩ := hsym0 ε μ R Y hts y hRy
  have hl := hlpos y hRy
  set lam := fam_lambda S.p ε μ y with hlam
  -- derivative of `H` at `y`
  have hZd : HasDerivAt Z (deriv Z y) y :=
    ((hZs y hRy).differentiableAt one_ne_zero).hasDerivAt
  have hLd0 : HasDerivAt (fun t => fam_lambda S.p ε μ t ^ S.p)
      (deriv (fun t => fam_lambda S.p ε μ t ^ S.p) y) y :=
    ((hLs y hRy).differentiableAt one_ne_zero).hasDerivAt
  set L' := deriv (fun t => fam_lambda S.p ε μ t ^ S.p) y with hL'
  have hLd : HasDerivAt L (L' : ℂ) y := hLd0.ofReal_comp
  have hHd := ((hLd.const_mul (a : ℂ)).mul (hZd.star.mul (hZd.pow 2))).sub
    ((hLd.const_mul (b : ℂ)).mul (hZd.pow 3))
  have hGd : deriv (c05_plane_wave_G S.p R ε μ) y =
      ((a : ℂ) * (L' : ℂ) * (star (Z y) * Z y ^ 2) +
        (a : ℂ) * L y * (star (deriv Z y) * Z y ^ 2 +
          star (Z y) * (((2 : ℕ) : ℂ) * Z y ^ (2 - 1) * deriv Z y)) -
        ((b : ℂ) * (L' : ℂ) * Z y ^ 3 + (b : ℂ) * L y * (((3 : ℕ) : ℂ) * Z y ^ (3 - 1) * deriv Z y))).re := by
    rw [hGH]
    exact (c05_aux_hasDerivAt_re hHd).deriv
  -- the plane-wave formula for `T_P`
  obtain ⟨-, -, hTP⟩ := hresp ε μ R Y htr y hRy
  -- the main identity: `G' - T_P = Re E`
  set w := deriv Z y - Complex.I * (lam : ℂ) * Z y with hw
  have hZ' : deriv Z y = Complex.I * (lam : ℂ) * Z y + w := by rw [hw]; ring
  have hstar' : star (deriv Z y) = -(Complex.I * (lam : ℂ)) * star (Z y) + star w := by
    rw [hZ']
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  obtain ⟨E, hE⟩ : ∃ E : ℂ, E = (a : ℂ) * (L' : ℂ) * (star (Z y) * Z y ^ 2) +
      (a : ℂ) * L y * (star w * Z y ^ 2 + 2 * star (Z y) * Z y * w) -
      (b : ℂ) * ((L' : ℂ) * Z y ^ 3 + 3 * L y * Z y ^ 2 * w) := ⟨_, rfl⟩
  have hLy : L y = ((lam ^ S.p : ℝ) : ℂ) := rfl
  have hlp1 : lam ^ (S.p + 1) = lam ^ S.p * lam := Real.rpow_add_one hl.ne' S.p
  have hdiff : deriv (c05_plane_wave_G S.p R ε μ) y - c05_plane_wave_TP S.p R ε μ y = E.re := by
    rw [hGd, hTP, hstar', hZ']
    have e1 : star (Z y) * Z y = ((‖Z y‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
    have key : ((a : ℂ) * (L' : ℂ) * (star (Z y) * Z y ^ 2) +
        (a : ℂ) * L y * ((-(Complex.I * (lam : ℂ)) * star (Z y) + star w) * Z y ^ 2 +
          star (Z y) * (((2 : ℕ) : ℂ) * Z y ^ (2 - 1) * (Complex.I * (lam : ℂ) * Z y + w))) -
        ((b : ℂ) * (L' : ℂ) * Z y ^ 3 + (b : ℂ) * L y * (((3 : ℕ) : ℂ) * Z y ^ (3 - 1) *
          (Complex.I * (lam : ℂ) * Z y + w)))) =
        E + (((a * lam ^ S.p * lam * ‖Z y‖ ^ 2 : ℝ) : ℂ) * (Complex.I * Z y) -
          ((3 * b * lam ^ S.p * lam : ℝ) : ℂ) * (Complex.I * Z y ^ 3)) := by
      rw [hE, hLy]
      have e2 : star (Z y) * Z y ^ 2 = ((‖Z y‖ ^ 2 : ℝ) : ℂ) * Z y := hconj _
      push_cast at e2 ⊢
      linear_combination (((a : ℂ) * ((lam ^ S.p : ℝ) : ℂ)) * (Complex.I * (lam : ℂ))) * e2
    have hX : ((((a * lam ^ S.p * lam * ‖Z y‖ ^ 2 : ℝ) : ℂ) * (Complex.I * Z y) -
          ((3 * b * lam ^ S.p * lam : ℝ) : ℂ) * (Complex.I * Z y ^ 3))).re =
        -2 * n_eps S.p ε * fam_lambda S.p ε μ y ^ (S.p + 1) * ‖fam_Z S.p R ε μ y‖ ^ 2 *
            (fam_Z S.p R ε μ y).im +
          6 * K3 * c_cubic S.p ε * fam_lambda S.p ε μ y ^ (S.p + 1) * (fam_Z S.p R ε μ y ^ 3).im := by
      rw [Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.I_mul_re,
        Complex.I_mul_re, ← hlam, hlp1, ha, hb]
      ring
    rw [key, Complex.add_re, hX]
    ring
  -- bounds
  have hnc := hsmall ε μ hε0 ht.2.1 ht.2.2.1
  have hn : |n_eps S.p ε| ≤ C₀ * ε := by
    have := abs_nonneg (c_eps S.p ε); have := abs_nonneg (c_cubic S.p ε)
    have := abs_nonneg (c_log S.p ε μ); linarith
  have hc : |c_cubic S.p ε| ≤ C₀ * ε := by
    have := abs_nonneg (c_eps S.p ε); have := abs_nonneg (n_eps S.p ε)
    have := abs_nonneg (c_log S.p ε μ); linarith
  have hZn : ‖Z y‖ ≤ Cs * y ^ (-beta S.p) := by
    have := hZb; simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at this
    linarith [norm_nonneg (c05_standing_Zmu0 S.p R μ y)]
  have hwn : ‖w‖ ≤ Cs * y ^ (-beta S.p - 1) := hwb
  have hL'b : |L'| ≤ 1 + Cs := by
    have := h4 0 (Nat.zero_le 1)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at this
    have hyp : y ^ (-S.p - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have : |L' - 1| ≤ Cs := by
      refine this.trans ?_
      calc Cs * ε * y ^ (-S.p - 1) ≤ Cs * 1 * 1 := by gcongr
        _ = Cs := by ring
    calc |L'| = |(L' - 1) + 1| := by ring_nf
      _ ≤ |L' - 1| + |1| := abs_add_le _ _
      _ ≤ 1 + Cs := by rw [abs_one]; linarith
  have hlamp : lam ^ S.p ≤ 2 * y := by
    calc lam ^ S.p ≤ (2 * y ^ (1 / S.p)) ^ S.p := Real.rpow_le_rpow hl.le hl2 hp0.le
      _ = 2 ^ S.p * y := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hy0.le,
            one_div_mul_cancel hp0.ne', Real.rpow_one]
      _ ≤ 2 * y := by
          gcongr
          calc (2 : ℝ) ^ S.p ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
            _ = 2 := Real.rpow_one 2
  have hLyn : ‖L y‖ = lam ^ S.p := by
    rw [hLy, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hl.le _)]
  have hyb : 0 < y ^ (-beta S.p) := Real.rpow_pos_of_pos hy0 _
  have hpow3 : (y ^ (-beta S.p)) ^ 3 = y ^ (-3 * beta S.p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; congr 1; push_cast; ring
  have hpowm : y * (y ^ (-beta S.p)) ^ 2 * y ^ (-beta S.p - 1) = y ^ (-3 * beta S.p) := by
    calc y * (y ^ (-beta S.p)) ^ 2 * y ^ (-beta S.p - 1) =
        y ^ (1 : ℝ) * y ^ (-beta S.p) * y ^ (-beta S.p) * y ^ (-beta S.p - 1) := by
          rw [Real.rpow_one]; ring
      _ = y ^ ((1 : ℝ) + -beta S.p + -beta S.p + (-beta S.p - 1)) := by
          rw [Real.rpow_add hy0, Real.rpow_add hy0, Real.rpow_add hy0]
      _ = y ^ (-3 * beta S.p) := by congr 1; ring
  -- `‖Z‖³ ≤ Cs³ y^{-3β}`, `L ‖Z‖² ‖w‖ ≤ 2 Cs³ y^{-3β}`
  have hZ3 : ‖Z y‖ ^ 3 ≤ Cs ^ 3 * y ^ (-3 * beta S.p) := by
    rw [← hpow3, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hZn 3
  have hZZw : lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖ ≤ 2 * Cs ^ 3 * y ^ (-3 * beta S.p) := by
    rw [← hpowm]
    calc lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖ ≤ (2 * y) * (Cs * y ^ (-beta S.p)) ^ 2 *
          (Cs * y ^ (-beta S.p - 1)) := by gcongr
      _ = _ := by ring
  have hEb : ‖E‖ ≤ 2 * C₀ * (1 + K3) * B * ε * y ^ (-3 * beta S.p) := by
    have hy3 : 0 ≤ y ^ (-3 * beta S.p) := (Real.rpow_pos_of_pos hy0 _).le
    have ha' : |a| ≤ 2 * C₀ * ε := by rw [ha, abs_mul, abs_two]; linarith
    have hb' : |b| ≤ 2 * C₀ * ε * K3 := by
      rw [hb, abs_mul, abs_mul, abs_two, abs_of_nonneg hK3]
      exact mul_le_mul_of_nonneg_right (by linarith) hK3
    have n1 : ‖star (Z y) * Z y ^ 2‖ = ‖Z y‖ ^ 3 := by
      rw [norm_mul, norm_star, norm_pow]; ring
    have n2 : ‖star w * Z y ^ 2 + 2 * star (Z y) * Z y * w‖ ≤ 3 * (‖Z y‖ ^ 2 * ‖w‖) := by
      calc _ ≤ ‖star w * Z y ^ 2‖ + ‖2 * star (Z y) * Z y * w‖ := norm_add_le _ _
        _ = 3 * (‖Z y‖ ^ 2 * ‖w‖) := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star, norm_pow,
            Complex.norm_two]; ring
    have n3 : ‖(L' : ℂ) * Z y ^ 3 + 3 * L y * Z y ^ 2 * w‖ ≤
        |L'| * ‖Z y‖ ^ 3 + 3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖) := by
      calc _ ≤ ‖(L' : ℂ) * Z y ^ 3‖ + ‖3 * L y * Z y ^ 2 * w‖ := norm_add_le _ _
        _ = _ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, hLyn, Complex.norm_real, Real.norm_eq_abs,
            norm_pow, norm_pow, show ‖(3 : ℂ)‖ = 3 by simp]; ring
    have hL'0 : 0 ≤ |L'| := abs_nonneg _
    have hZ30 : 0 ≤ ‖Z y‖ ^ 3 := by positivity
    have hZZw0 : 0 ≤ lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖ := by positivity
    have t1 : |L'| * ‖Z y‖ ^ 3 ≤ (1 + Cs) * (Cs ^ 3 * y ^ (-3 * beta S.p)) :=
      mul_le_mul hL'b hZ3 hZ30 (by positivity)
    have hX : |L'| * ‖Z y‖ ^ 3 + 3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖) ≤ B * y ^ (-3 * beta S.p) := by
      calc |L'| * ‖Z y‖ ^ 3 + 3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖) ≤
          (1 + Cs) * (Cs ^ 3 * y ^ (-3 * beta S.p)) + 3 * (2 * Cs ^ 3 * y ^ (-3 * beta S.p)) :=
            add_le_add t1 (by linarith [hZZw])
        _ = B * y ^ (-3 * beta S.p) := by rw [hB]; ring
    have hlp0 : 0 ≤ lam ^ S.p := Real.rpow_nonneg hl.le _
    have m1 : ‖(a : ℂ) * (L' : ℂ) * (star (Z y) * Z y ^ 2)‖ = |a| * (|L'| * ‖Z y‖ ^ 3) := by
      rw [norm_mul, norm_mul, n1, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]; ring
    have m2 : ‖(a : ℂ) * L y * (star w * Z y ^ 2 + 2 * star (Z y) * Z y * w)‖ ≤
        |a| * (3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖)) := by
      rw [norm_mul, norm_mul, hLyn, Complex.norm_real, Real.norm_eq_abs]
      calc |a| * lam ^ S.p * ‖star w * Z y ^ 2 + 2 * star (Z y) * Z y * w‖ ≤
          |a| * lam ^ S.p * (3 * (‖Z y‖ ^ 2 * ‖w‖)) :=
            mul_le_mul_of_nonneg_left n2 (mul_nonneg (abs_nonneg _) hlp0)
        _ = _ := by ring
    have m3 : ‖(b : ℂ) * ((L' : ℂ) * Z y ^ 3 + 3 * L y * Z y ^ 2 * w)‖ ≤
        |b| * (|L'| * ‖Z y‖ ^ 3 + 3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left n3 (abs_nonneg _)
    have hXa : |L'| * ‖Z y‖ ^ 3 + 3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖) ≥ 0 := by positivity
    calc ‖E‖ ≤ ‖(a : ℂ) * (L' : ℂ) * (star (Z y) * Z y ^ 2)‖ +
          ‖(a : ℂ) * L y * (star w * Z y ^ 2 + 2 * star (Z y) * Z y * w)‖ +
          ‖(b : ℂ) * ((L' : ℂ) * Z y ^ 3 + 3 * L y * Z y ^ 2 * w)‖ := by
          rw [hE]; exact c05_aux_norm3 _ _ _
      _ ≤ |a| * (|L'| * ‖Z y‖ ^ 3 + 3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖)) +
          |b| * (|L'| * ‖Z y‖ ^ 3 + 3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖)) := by
          rw [m1]
          have e := mul_add |a| (|L'| * ‖Z y‖ ^ 3) (3 * (lam ^ S.p * ‖Z y‖ ^ 2 * ‖w‖))
          linarith [m2, m3]
      _ ≤ (2 * C₀ * ε) * (B * y ^ (-3 * beta S.p)) +
          (2 * C₀ * ε * K3) * (B * y ^ (-3 * beta S.p)) :=
          c05_aux_lin2 ha' hb' hX hXa (by positivity) (by positivity)
      _ = 2 * C₀ * (1 + K3) * B * ε * y ^ (-3 * beta S.p) := by ring
  have hyY : y ^ (-3 * beta S.p) ≤ Y ^ (-3 * beta S.p) := by
    have hbeta : 0 ≤ beta S.p := by unfold beta; positivity
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hYy (by linarith)
  refine ⟨?_, ?_⟩
  · rw [abs_sub_comm, hdiff]
    calc |E.re| ≤ ‖E‖ := Complex.abs_re_le_norm E
      _ ≤ 2 * C₀ * (1 + K3) * B * ε * y ^ (-3 * beta S.p) := hEb
      _ ≤ (2 * C₀ * (1 + K3) * B + 1) * ε * Y ^ (-3 * beta S.p) := by
          have : 0 ≤ ε * Y ^ (-3 * beta S.p) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hyY (show 0 ≤ 2 * C₀ * (1 + K3) * B * ε by positivity)]
  · congr 1
    have := c05_aux_two_beta S.p hp0
    linarith

/-- Helper: `z ↦ A sin(lz+b)` is smooth with `|∂^k| ≤ |A|(1+|l|)³`, `k ≤ 3`. -/
theorem c05_aux_sin_bounds (A l b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => A * Real.sin (l * z + b)) ∧
    ∀ x, |A * Real.sin (l * x + b)| ≤ |A| * (1 + |l|) ^ 3 ∧
      |deriv (fun z => A * Real.sin (l * z + b)) x| ≤ |A| * (1 + |l|) ^ 3 ∧
      |deriv (deriv (fun z => A * Real.sin (l * z + b))) x| ≤ |A| * (1 + |l|) ^ 3 ∧
      |deriv (deriv (deriv (fun z => A * Real.sin (l * z + b)))) x| ≤ |A| * (1 + |l|) ^ 3 := by
  have hlin : ∀ z, HasDerivAt (fun z => l * z + b) l z := fun z => by
    simpa using ((hasDerivAt_id z).const_mul l).add_const b
  have d1 : deriv (fun z => A * Real.sin (l * z + b)) = fun z => A * l * Real.cos (l * z + b) := by
    funext z
    have := ((hlin z).sin).const_mul A
    rw [this.deriv]; ring
  have d2 : deriv (fun z => A * l * Real.cos (l * z + b)) =
      fun z => -(A * l * l) * Real.sin (l * z + b) := by
    funext z
    have := ((hlin z).cos).const_mul (A * l)
    rw [this.deriv]; ring
  have d3 : deriv (fun z => -(A * l * l) * Real.sin (l * z + b)) =
      fun z => -(A * l * l * l) * Real.cos (l * z + b) := by
    funext z
    have := ((hlin z).sin).const_mul (-(A * l * l))
    rw [this.deriv]; ring
  refine ⟨by fun_prop, fun x => ?_⟩
  rw [d1, d2, d3]
  have hl : 0 ≤ |l| := abs_nonneg l
  have h1 : 1 ≤ (1 + |l|) ^ 3 := one_le_pow₀ (by linarith)
  have hA := abs_nonneg A
  have ex : (1 + |l|) ^ 3 = 1 + 3 * |l| + 3 * (|l| * |l|) + |l| * |l| * |l| := by ring
  have q2 : 0 ≤ |l| * |l| := mul_nonneg hl hl
  have q3 : 0 ≤ |l| * |l| * |l| := mul_nonneg q2 hl
  have e1 : |l| ≤ (1 + |l|) ^ 3 := by rw [ex]; linarith
  have e2 : |l| * |l| ≤ (1 + |l|) ^ 3 := by rw [ex]; linarith
  have e3 : |l| * |l| * |l| ≤ (1 + |l|) ^ 3 := by rw [ex]; linarith
  have s1 := Real.abs_sin_le_one (l * x + b)
  have c1 := Real.abs_cos_le_one (l * x + b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_mul]
    calc |A| * |Real.sin (l * x + b)| ≤ |A| * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; exact le_mul_of_one_le_right hA h1
  · rw [abs_mul, abs_mul]
    calc |A| * |l| * |Real.cos (l * x + b)| ≤ |A| * |l| * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left e1 hA
  · rw [abs_mul, abs_neg, abs_mul, abs_mul]
    calc |A| * |l| * |l| * |Real.sin (l * x + b)| ≤ |A| * |l| * |l| * 1 := by gcongr
      _ ≤ _ := by rw [mul_one, mul_assoc]; exact mul_le_mul_of_nonneg_left e2 hA
  · rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul]
    calc |A| * |l| * |l| * |l| * |Real.cos (l * x + b)| ≤ |A| * |l| * |l| * |l| * 1 := by gcongr
      _ ≤ _ := by rw [mul_one, mul_assoc, mul_assoc]; rw [← mul_assoc |l|]; exact mul_le_mul_of_nonneg_left e3 hA

/-- Helper: a smooth compactly supported function has bounded derivatives up to order 3. -/
theorem c05_aux_cs_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ∃ M : ℝ, ∀ x, |f x| ≤ M ∧ |deriv f x| ≤ M ∧ |deriv (deriv f) x| ≤ M ∧
      |deriv (deriv (deriv f)) x| ≤ M := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp h1).2
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (deriv f))) := (contDiff_infty_iff_deriv.mp h2).2
  obtain ⟨M0, hM0⟩ := hf.continuous.bounded_above_of_compact_support hs
  obtain ⟨M1, hM1⟩ := h1.continuous.bounded_above_of_compact_support hs.deriv
  obtain ⟨M2, hM2⟩ := h2.continuous.bounded_above_of_compact_support hs.deriv.deriv
  obtain ⟨M3, hM3⟩ := h3.continuous.bounded_above_of_compact_support hs.deriv.deriv.deriv
  refine ⟨max (max M0 M1) (max M2 M3), fun x => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (hM0 x).trans (by simp)
  · exact (hM1 x).trans (by simp)
  · exact (hM2 x).trans (by simp)
  · exact (hM3 x).trans (by simp)

/-- Helper (from lem:c05_primitive, lem:c05_symbol_bounds): `v_Y` is smooth with compact
support; on `(R,∞)` it is `-2χ_Y Re ∫_z^∞ (Z + c_cubic Z³)`. -/
theorem c05_aux_vY_smooth (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ContDiff ℝ (⊤ : ℕ∞) (res_vY S.p R ε μ Y) ∧ HasCompactSupport (res_vY S.p R ε μ Y) := by
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  refine ⟨max Rp Rs, le_max_of_le_left hRp, ?_⟩
  intro ε μ R Y ht
  have htp := c05_aux_tuple_mono (show Rp ≤ max Rp Rs by simp) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ max Rp Rs by simp) ht
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hY : 0 < Y := by linarith [ht.2.2.2.2]
  have hRY : R < 3 * Y / 10 := by linarith [ht.2.2.2.2]
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsym0 ε μ R Y hts t ht'.le).1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  obtain ⟨⟨hZi, hZ3i, -⟩, -⟩ := hprim ε μ R Y htp R le_rfl
  set F : ℝ → ℂ := fun t => fam_Z S.p R ε μ t + (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ t ^ 3
    with hF
  have hFi : IntegrableOn F (Ioi R) := hZi.add (hZ3i.const_mul _)
  have hZs : ∀ t, R < t → ContDiffAt ℝ (⊤ : ℕ∞) (fam_Z S.p R ε μ) t := fun t ht' =>
    c05_aux_Z_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) (by linarith) (hpos t ht').ne'
  have hFs : ∀ t, R < t → ContDiffAt ℝ (⊤ : ℕ∞) F t := fun t ht' =>
    (hZs t ht').add (contDiffAt_const.mul ((hZs t ht').pow 3))
  have hFc : ContinuousOn F (Ioi R) := fun t ht' => (hFs t ht').continuousAt.continuousWithinAt
  set T : ℝ → ℂ := fun z => ∫ t in Ioi z, F t with hT
  have hTd : ∀ z, R < z → HasDerivAt T (-F z) z := fun z hz =>
    c05_aux_tail_hasDeriv F R hFi hFc hz
  have hTs : ContDiffOn ℝ (⊤ : ℕ∞) T (Ioi R) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz => (hTd z hz).differentiableAt.differentiableWithinAt, ?_⟩
    refine ContDiffOn.congr (f := fun z => -F z) (fun z hz => (hFs z hz).neg.contDiffWithinAt)
      (fun z hz => (hTd z hz).deriv)
  obtain ⟨hc, hcs⟩ := c05_aux_cutoff_mul (n := (⊤ : ℕ∞)) hY hRY
    (fun t ht' => hTs.contDiffAt (Ioi_mem_nhds ht'))
  have heq : res_vY S.p R ε μ Y = (fun w : ℂ => -2 * w.re) ∘
      (fun z => (res_chiY Y z : ℂ) * T z) := by
    funext z
    simp only [res_vY, Function.comp_apply, hT, hF]
    split_ifs with h
    · rw [Complex.re_ofReal_mul]; ring
    · rw [c05_aux_chiY_zero hY (Or.inl (by linarith [not_lt.mp h]))]; simp
  rw [heq]
  exact ⟨(contDiff_const.mul Complex.reCLM.contDiff).comp hc, hcs.comp_left (by simp)⟩

/-- Helper: the `s`-form integrand of `∂_y 𝒬_{ε,3}(v)(y)` is integrable (`v ∈ C³_b`). -/
theorem c05_aux_Q3_int' (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (v : ℝ → ℝ) (hv : ContDiff ℝ 3 v)
    (M : ℝ) (hM : ∀ x, |v x| ≤ M ∧ |deriv v x| ≤ M ∧ |deriv (deriv v) x| ≤ M ∧
        |deriv (deriv (deriv v)) x| ≤ M) (y : ℝ) :
    Integrable (fun s => |s| ^ (-p - 3) *
      (c05_plane_wave_Delta (deriv (deriv v)) y s * c05_plane_wave_Delta v y s ^ 2 +
        2 * c05_plane_wave_Delta (deriv v) y s ^ 2 * c05_plane_wave_Delta v y s)) := by
  have hd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hv1 : ContDiff ℝ 2 (deriv v) := hv.iterate_deriv' 2 1
  have hv2 : ContDiff ℝ 1 (deriv (deriv v)) := hv.iterate_deriv' 1 2
  have hd' : Differentiable ℝ (deriv v) := hv1.differentiable (by norm_num)
  have hd'' : Differentiable ℝ (deriv (deriv v)) := hv2.differentiable one_ne_zero
  have m1 : Measurable (fun s => c05_plane_wave_Delta v y s) :=
    measurable_const.sub (hd.continuous.measurable.comp (measurable_const.sub measurable_id))
  have m2 : Measurable (fun s => c05_plane_wave_Delta (deriv v) y s) :=
    measurable_const.sub (hd'.continuous.measurable.comp (measurable_const.sub measurable_id))
  have m3 : Measurable (fun s => c05_plane_wave_Delta (deriv (deriv v)) y s) :=
    measurable_const.sub (hd''.continuous.measurable.comp (measurable_const.sub measurable_id))
  exact Integrable.mono' ((c05_aux_kp_integrable p hp hp1).const_mul (24 * M ^ 3))
    ((measurable_id.abs.pow_const _).mul ((m3.mul (m1.pow_const 2)).add
      (((m2.pow_const 2).const_mul 2).mul m1))).aestronglyMeasurable
    (Eventually.of_forall fun s => c05_aux_Q3_dom' p hp v hd hd' hd'' M hM y s)

/-- Blueprint: lem:c05_cubic_remainder_representation.  `ℛ_cub ∈ C¹((R,∞))` and on `[Y,2Y]`:
`ℛ_cub = 𝒬_{ε,3}(v_Y)(y) - 𝒬_{ε,3}(P_y)(y) = K_ε ∫ |s|^{-p-3} N₀(y,s) ds`,
`ℛ_cub' = K_ε ∫ |s|^{-p-3} N₁(y,s) ds + (T_P - G')(y)`. -/
theorem c05_cubic_remainder_representation (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ContDiffOn ℝ 1 (c05_E5_remainders_Rcub S.p R ε μ Y) (Ioi R) ∧
      ∀ y ∈ Icc Y (2 * Y),
        Integrable (fun s => |s| ^ (-S.p - 3) * c05_plane_wave_N0 S.p R ε μ Y y s) ∧
        Integrable (fun s => |s| ^ (-S.p - 3) * c05_plane_wave_N1 S.p R ε μ Y y s) ∧
        c05_E5_remainders_Rcub S.p R ε μ Y y =
          c04_cubic_part S.p ε (res_vY S.p R ε μ Y) y -
            c04_cubic_part S.p ε (c05_plane_wave S.p R ε μ y) y ∧
        c04_cubic_part S.p ε (res_vY S.p R ε μ Y) y -
            c04_cubic_part S.p ε (c05_plane_wave S.p R ε μ y) y =
          c05_plane_wave_K S.p ε * ∫ s, |s| ^ (-S.p - 3) * c05_plane_wave_N0 S.p R ε μ Y y s ∧
        deriv (c05_E5_remainders_Rcub S.p R ε μ Y) y =
          c05_plane_wave_K S.p ε * (∫ s, |s| ^ (-S.p - 3) * c05_plane_wave_N1 S.p R ε μ Y y s) +
            (c05_plane_wave_TP S.p R ε μ y - deriv (c05_plane_wave_G S.p R ε μ) y) := by
  obtain ⟨Rv, hRv, hvY⟩ := c05_aux_vY_smooth S
  obtain ⟨Rq, hRq, Cq, -, hpar⟩ := c05_plane_wave_parameter S
  obtain ⟨Rr, hRr, hresp⟩ := c05_plane_wave_response S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hp1 := S.hp_hi
  refine ⟨max (max Rv Rq) (max Rr Rs), le_max_of_le_left (le_max_of_le_left hRv), ?_⟩
  intro ε μ R Y ht
  have htv := c05_aux_tuple_mono (show Rv ≤ max (max Rv Rq) (max Rr Rs) by simp) ht
  have htq := c05_aux_tuple_mono (show Rq ≤ max (max Rv Rq) (max Rr Rs) by simp) ht
  have htr := c05_aux_tuple_mono (show Rr ≤ max (max Rv Rq) (max Rr Rs) by simp) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ max (max Rv Rq) (max Rr Rs) by simp) ht
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  obtain ⟨hvs, hvc⟩ := hvY ε μ R Y htv
  obtain ⟨Mv, hMv⟩ := c05_aux_cs_bounds hvs hvc
  set v := res_vY S.p R ε μ Y with hv
  have hv3 : ContDiff ℝ 3 v := hvs.of_le (WithTop.coe_le_coe.mpr le_top)
  have hv2 : ContDiff ℝ 2 v := hvs.of_le (WithTop.coe_le_coe.mpr le_top)
  have hMv' : ∀ x, |v x| ≤ Mv ∧ |deriv v x| ≤ Mv ∧ |deriv (deriv v) x| ≤ Mv :=
    fun x => ⟨(hMv x).1, (hMv x).2.1, (hMv x).2.2.1⟩
  obtain ⟨hGc, -⟩ := hpar ε μ R Y htq
  have hQv := c05_aux_Q3_part2 S.p ε hp0 hp1 v hv3 Mv hMv
  have hRcub : c05_E5_remainders_Rcub S.p R ε μ Y =
      fun x => c04_cubic_part S.p ε v x - c05_plane_wave_G S.p R ε μ x := by
    funext x
    unfold c05_E5_remainders_Rcub c05_plane_wave_G
    ring
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hRcub]
    exact hQv.1.contDiffOn.sub (hGc.mono Ioi_subset_Ici_self)
  have hY1 : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hRy : R ≤ y := by linarith [hy.1, ht.2.2.2.2]
  have hRy' : R < y := by linarith [hy.1, ht.2.2.2.2]
  have hy0 : 0 < y := by linarith
  have hl : 0 < fam_lambda S.p ε μ y := by
    have := (hsym0 ε μ R Y hts y hRy).1.1
    have : 0 < y ^ (1 / S.p) / 2 := by positivity
    linarith
  -- the plane wave is a smooth bounded sine
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * ‖fam_Z S.p R ε μ y‖ / fam_lambda S.p ε μ y := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = Complex.arg (fam_Z S.p R ε μ y) - fam_lambda S.p ε μ y * y :=
    ⟨_, rfl⟩
  have hPsin : c05_plane_wave S.p R ε μ y =
      fun z => A * Real.sin (fam_lambda S.p ε μ y * z + b) := by
    funext z
    rw [hA, hb]
    exact c05_aux_plane_wave_sin _ _ _ _ hl
  obtain ⟨hPs, hPb⟩ := c05_aux_sin_bounds A (fam_lambda S.p ε μ y) b
  rw [← hPsin] at hPs
  have hPb' : ∀ x, |c05_plane_wave S.p R ε μ y x| ≤ |A| * (1 + |fam_lambda S.p ε μ y|) ^ 3 ∧
      |deriv (c05_plane_wave S.p R ε μ y) x| ≤ |A| * (1 + |fam_lambda S.p ε μ y|) ^ 3 ∧
      |deriv (deriv (c05_plane_wave S.p R ε μ y)) x| ≤ |A| * (1 + |fam_lambda S.p ε μ y|) ^ 3 ∧
      |deriv (deriv (deriv (c05_plane_wave S.p R ε μ y))) x| ≤
        |A| * (1 + |fam_lambda S.p ε μ y|) ^ 3 := by
    intro x; rw [hPsin]; exact hPb x
  clear hPb
  generalize hP : c05_plane_wave S.p R ε μ y = P at hPs hPb'
  have hP3 : ContDiff ℝ 3 P := hPs.of_le (WithTop.coe_le_coe.mpr le_top)
  have hP2 : ContDiff ℝ 2 P := hPs.of_le (WithTop.coe_le_coe.mpr le_top)
  have hMP' : ∀ x, |P x| ≤ |A| * (1 + |fam_lambda S.p ε μ y|) ^ 3 ∧
      |deriv P x| ≤ |A| * (1 + |fam_lambda S.p ε μ y|) ^ 3 ∧
      |deriv (deriv P) x| ≤ |A| * (1 + |fam_lambda S.p ε μ y|) ^ 3 :=
    fun x => ⟨(hPb' x).1, (hPb' x).2.1, (hPb' x).2.2.1⟩
  have hQP := c05_aux_Q3_part2 S.p ε hp0 hp1 P hP3 _ hPb'
  obtain ⟨iv0, -, ev0⟩ := c05_aux_Q3_part1 S.p ε hp0 hp1 v hv2 Mv hMv' y
  obtain ⟨iP0, -, eP0⟩ := c05_aux_Q3_part1 S.p ε hp0 hp1 P hP2 _ hMP' y
  have iv1 := c05_aux_Q3_int' S.p hp0 hp1 v hv3 Mv hMv y
  have iP1 := c05_aux_Q3_int' S.p hp0 hp1 P hP3 _ hPb' y
  obtain ⟨-, hGy, -⟩ := hresp ε μ R Y htr y hRy
  have eN0 : (fun s => |s| ^ (-S.p - 3) * c05_plane_wave_N0 S.p R ε μ Y y s) =
      fun s => |s| ^ (-S.p - 3) * c05_plane_wave_Delta (deriv v) y s *
          c05_plane_wave_Delta v y s ^ 2 -
        |s| ^ (-S.p - 3) * c05_plane_wave_Delta (deriv P) y s * c05_plane_wave_Delta P y s ^ 2 := by
    funext s; unfold c05_plane_wave_N0; rw [← hv, hP]; ring
  have eN1 : (fun s => |s| ^ (-S.p - 3) * c05_plane_wave_N1 S.p R ε μ Y y s) =
      fun s => |s| ^ (-S.p - 3) *
          (c05_plane_wave_Delta (deriv (deriv v)) y s * c05_plane_wave_Delta v y s ^ 2 +
            2 * c05_plane_wave_Delta (deriv v) y s ^ 2 * c05_plane_wave_Delta v y s) -
        |s| ^ (-S.p - 3) *
          (c05_plane_wave_Delta (deriv (deriv P)) y s * c05_plane_wave_Delta P y s ^ 2 +
            2 * c05_plane_wave_Delta (deriv P) y s ^ 2 * c05_plane_wave_Delta P y s) := by
    funext s; unfold c05_plane_wave_N1; rw [← hv, hP]; ring
  have hGd : DifferentiableAt ℝ (c05_plane_wave_G S.p R ε μ) y :=
    ((hGc.contDiffAt (Ici_mem_nhds hRy')).differentiableAt one_ne_zero)
  have hTP : c05_plane_wave_TP S.p R ε μ y = deriv (c04_cubic_part S.p ε P) y := by
    rw [← hP]; rfl
  refine ⟨by rw [eN0]; exact iv0.sub iP0, by rw [eN1]; exact iv1.sub iP1, ?_, ?_, ?_⟩
  · rw [hRcub]; beta_reduce; rw [← hGy, hP]
  · rw [eN0, integral_sub iv0 iP0, mul_sub, ← ev0, ← eP0]
  · rw [hRcub, deriv_fun_sub (hQv.1.differentiable one_ne_zero y) hGd, hTP, hQv.2 y, hQP.2 y, eN1,
      integral_sub iv1 iP1]
    ring

/-- Helper for lem:c05_vY_bounds. -/
theorem c05_aux_eq_of_cont_left {f h : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousAt f a)
    (hh : ContinuousAt h a) (he : ∀ x ∈ Ioo a b, f x = h x) : f a = h a := by
  have h1 : Tendsto f (nhdsWithin a (Ioi a)) (nhds (h a)) := by
    refine (hh.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx using (he x hx).symm
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds) h1

/-- Helper for lem:c05_vY_bounds. -/
theorem c05_aux_eq_of_cont_right {f h : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ContinuousAt f b)
    (hh : ContinuousAt h b) (he : ∀ x ∈ Ioo a b, f x = h x) : f b = h b := by
  have h1 : Tendsto f (nhdsWithin b (Iio b)) (nhds (h b)) := by
    refine (hh.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx using (he x hx).symm
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds) h1

/-- Helper for lem:c05_vY_bounds. -/
theorem c05_aux_iteratedDeriv_re {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun z => c * (g z).re) = fun z => c * (iteratedDeriv k g z).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext z
    have hd : DifferentiableAt ℝ (iteratedDeriv k g) z :=
      (hg.differentiable_iteratedDeriv k (by exact_mod_cast WithTop.coe_lt_top _)) z
    exact ((c05_aux_hasDerivAt_re hd.hasDerivAt).const_mul c).deriv

set_option maxHeartbeats 800000 in
/-- Data for lem:c05_vY_bounds (bounds). -/
theorem c05_aux_vY_data1 (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        (∀ k : ℕ, k ≤ 3 → ∀ z, |iteratedDeriv k (res_vY S.p R ε μ Y) z| ≤
          K * Y ^ (-beta S.p + ((k : ℝ) - 1) / S.p)) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  choose Cs hCs hsb using hsym
  obtain ⟨Cc, hCc, hsc⟩ := c05_small_constants S
  choose KL hKL0 hKL using c05_aux_cutoff_leibniz
  set Af : ℝ := (1 + Cc) * (Cp + Cs 0 + Cs 1 + Cs 2) with hAf
  have hAf0 : 0 ≤ Af := by have := hCs 0; have := hCs 1; have := hCs 2; positivity
  set K : ℝ := 2 * ∑ k ∈ Finset.range 4, KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af + 1
    with hK
  have hKk : ∀ k, k ≤ 3 → 2 * (KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af) ≤ K := by
    intro k hk
    have : KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af ≤
        ∑ k ∈ Finset.range 4, KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af :=
      Finset.single_le_sum (f := fun k => KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af)
        (fun j _ => by have := hKL0 j; positivity) (Finset.mem_range.mpr (by omega))
    rw [hK]; linarith
  refine ⟨max Rp Rs, hRp.trans (le_max_left _ _), K, by
    have : 0 ≤ ∑ k ∈ Finset.range 4, KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af :=
      Finset.sum_nonneg fun j _ => by have := hKL0 j; positivity
    positivity, ?_⟩
  intro ε μ R Y ht
  have htp := c05_aux_tuple_mono (le_max_left Rp Rs) ht
  have hts := c05_aux_tuple_mono (le_max_right Rp Rs) ht
  have hR : 1 ≤ R := hRp.trans htp.2.2.2.1
  have hR0 : 0 < R := by linarith
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hRY : R < 3 * Y / 10 := by linarith
  have hcc : |c_cubic S.p ε| ≤ Cc := by
    have := hsc ε μ ht.1 ht.2.1 ht.2.2.1
    have := abs_nonneg (c_eps S.p ε); have := abs_nonneg (n_eps S.p ε)
    have := abs_nonneg (c_log S.p ε μ)
    have : Cc * ε ≤ Cc := by nlinarith [ht.2.1, S.hε₀_le]
    linarith
  set c : ℂ := (c_cubic S.p ε : ℂ) with hc
  have hcn : ‖c‖ ≤ Cc := by rw [hc, Complex.norm_real, Real.norm_eq_abs]; exact hcc
  set Z := fam_Z S.p R ε μ with hZ
  set G : ℝ → ℂ := fun t => Z t + c * Z t ^ 3 with hG
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsb 0 ε μ R Y hts t ht'.le).1.1
    have : 0 < t ^ (1 / S.p) / 2 := by have : 0 < t := by linarith
                                       positivity
    linarith
  obtain ⟨⟨hZi, hZ3i, -⟩, -⟩ := hprim ε μ R Y htp R le_rfl
  have hGi : IntegrableOn G (Ioi R) := hZi.add (hZ3i.const_mul _)
  have hZs : ∀ t, R < t → ContDiffAt ℝ (⊤ : ℕ∞) Z t := fun t ht' =>
    c05_aux_Z_smooth S.p R ε μ hp hp1 hR0 (by linarith) (hpos t ht').ne'
  have hGs : ∀ t, R < t → ContDiffAt ℝ (⊤ : ℕ∞) G t := fun t ht' =>
    (hZs t ht').add (contDiffAt_const.mul ((hZs t ht').pow 3))
  have hGc : ContinuousOn G (Ioi R) := fun t ht' => (hGs t ht').continuousAt.continuousWithinAt
  set T : ℝ → ℂ := fun z => ∫ t in Ioi z, G t with hT
  have hTd : ∀ z, R < z → HasDerivAt T (-G z) z := fun z hz =>
    c05_aux_tail_hasDeriv G R hGi hGc hz
  have hTs : ContDiffOn ℝ (⊤ : ℕ∞) T (Ioi R) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz => (hTd z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact ContDiffOn.congr (f := fun z => -G z) (fun z hz => (hGs z hz).neg.contDiffWithinAt)
      (fun z hz => (hTd z hz).deriv)
  obtain ⟨hgs, -⟩ := c05_aux_cutoff_mul (n := (⊤ : ℕ∞)) hY0 hRY
    (fun t ht' => hTs.contDiffAt (Ioi_mem_nhds ht'))
  set g : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * T z with hg
  have hv : res_vY S.p R ε μ Y = fun z => -2 * (g z).re := by
    funext z
    simp only [res_vY, hg, hT, hG]
    split_ifs with h
    · rw [Complex.re_ofReal_mul]; ring
    · rw [c05_aux_chiY_zero hY0 (Or.inl (by linarith [not_lt.mp h]))]; simp
  have hvs : ContDiff ℝ (⊤ : ℕ∞) (res_vY S.p R ε μ Y) := by
    rw [hv]; exact contDiff_const.mul (Complex.reCLM.contDiff.comp hgs)
  have hvk : ∀ k, iteratedDeriv k (res_vY S.p R ε μ Y) = fun z => -2 * (iteratedDeriv k g z).re := by
    intro k; rw [hv]; exact c05_aux_iteratedDeriv_re hgs (-2) k
  have hTi : ∀ z, R < z → ∀ i : ℕ, iteratedDeriv (i + 1) T z = -(iteratedDeriv i G z) := by
    intro z hz i
    rw [iteratedDeriv_succ']
    have : deriv T =ᶠ[nhds z] fun w => -G w := by
      filter_upwards [Ioi_mem_nhds hz] with w hw using (hTd w hw).deriv
    rw [this.iteratedDeriv_eq, iteratedDeriv_fun_neg]
  have hGb : ∀ z, R < z → ∀ i : ℕ, i ≤ 2 →
      ‖iteratedDeriv i G z‖ ≤ (1 + Cc) * Cs i * z ^ (-beta S.p + i / S.p) := by
    intro z hz i hi
    have hz1 : 1 ≤ z := by linarith
    have heq : G = Z + fun w => c * (fun u => Z u ^ 3) w := rfl
    rw [heq, iteratedDeriv_add ((hZs z hz).of_le (by exact_mod_cast le_top))
      (contDiffAt_const.mul ((hZs z hz).pow 3) |>.of_le (by exact_mod_cast le_top)),
      iteratedDeriv_const_mul_field]
    obtain ⟨-, -, ⟨hZ, hZ3, -⟩, -⟩ := hsb i ε μ R Y hts z hz.le
    have h1 : ‖iteratedDeriv i Z z‖ ≤ Cs i * z ^ (-beta S.p + i / S.p) := by
      linarith [norm_nonneg (iteratedDeriv i (c05_standing_Zmu0 S.p R μ) z)]
    have h3 : ‖iteratedDeriv i (fun u => Z u ^ 3) z‖ ≤ Cs i * z ^ (-beta S.p + i / S.p) :=
      hZ3.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (hCs i).le)
    have hX : 0 ≤ Cs i * z ^ (-beta S.p + i / S.p) := by
      have := hCs i; have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < z) (-beta S.p + i / S.p)
      positivity
    calc _ ≤ ‖iteratedDeriv i Z z‖ + ‖c‖ * ‖iteratedDeriv i (fun u => Z u ^ 3) z‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ Cs i * z ^ (-beta S.p + i / S.p) + Cc * (Cs i * z ^ (-beta S.p + i / S.p)) := by
          gcongr
      _ = _ := by ring
  have hT0 : ∀ z, R ≤ z → ‖T z‖ ≤ (1 + Cc) * Cp * z ^ (-beta S.p - 1 / S.p) := by
    intro z hz
    have hz1 : 1 ≤ z := by linarith
    obtain ⟨⟨hi, hi3, -, -, -, -, hb, hb3⟩, -⟩ := hprim ε μ R Y htp z hz
    have : T z = (∫ t in Ioi z, Z t) + c * ∫ t in Ioi z, Z t ^ 3 := by
      simp only [hT, hG]; rw [integral_add hi (hi3.const_mul _), integral_const_mul]
    rw [this]
    have hb3' : ‖∫ t in Ioi z, Z t ^ 3‖ ≤ Cp * z ^ (-beta S.p - 1 / S.p) :=
      hb3.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) hCp.le)
    have hX : 0 ≤ Cp * z ^ (-beta S.p - 1 / S.p) := by
      have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < z) (-beta S.p - 1 / S.p); positivity
    calc _ ≤ ‖∫ t in Ioi z, Z t‖ + ‖c‖ * ‖∫ t in Ioi z, Z t ^ 3‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ Cp * z ^ (-beta S.p - 1 / S.p) + Cc * (Cp * z ^ (-beta S.p - 1 / S.p)) := by gcongr
      _ = _ := by ring
  have hgk : ∀ k : ℕ, k ≤ 3 → ∀ z, ‖iteratedDeriv k g z‖ ≤
      KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af *
        Y ^ (-beta S.p + ((k : ℝ) - 1) / S.p) := by
    intro k hk z
    by_cases hz : z ∈ Ioo (Y / 4) (4 * Y)
    · have hzR : R < z := by linarith [hz.1]
      have hz1 : 1 ≤ z := by linarith
      have := hKL k Y hY0 T z Af (-beta S.p + ((k : ℝ) - 1) / S.p + k) hz
        ((hTs.contDiffAt (Ioi_mem_nhds hzR)).of_le (by exact_mod_cast le_top)) hAf0 ?_
      · convert this using 2; ring_nf
      intro i hi
      have hzp : ∀ θ : ℝ, 0 < z ^ θ := fun θ => Real.rpow_pos_of_pos (by linarith) θ
      rcases i with _ | j
      · rw [iteratedDeriv_zero]
        refine (hT0 z hzR.le).trans ?_
        have : z ^ (-beta S.p - 1 / S.p) ≤ z ^ (-beta S.p + ((k : ℝ) - 1) / S.p + k + (0 : ℕ) * (-1)) :=
          Real.rpow_le_rpow_of_exponent_le hz1 (by
            have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            have : 0 ≤ (k : ℝ) / S.p := by positivity
            have : ((k : ℝ) - 1) / S.p = (k : ℝ) / S.p - 1 / S.p := by ring
            rw [Nat.cast_zero, zero_mul, add_zero]; linarith)
        have : (1 + Cc) * Cp ≤ Af := by
          rw [hAf]; have := hCs 0; have := hCs 1; have := hCs 2
          gcongr; linarith
        calc _ ≤ Af * z ^ (-beta S.p - 1 / S.p) := by gcongr
          _ ≤ _ := by gcongr
      · rw [hTi z hzR j, norm_neg]
        have hj : j ≤ 2 := by omega
        refine (hGb z hzR j hj).trans ?_
        have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hi
        have : z ^ (-beta S.p + j / S.p) ≤ z ^ (-beta S.p + ((k : ℝ) - 1) / S.p + k + ((j + 1 : ℕ) : ℝ) * (-1)) :=
          Real.rpow_le_rpow_of_exponent_le hz1 (by
            have : (j : ℝ) / S.p ≤ ((k : ℝ) - 1) / S.p :=
              div_le_div_of_nonneg_right (by linarith) hp0.le
            push_cast; linarith)
        have : (1 + Cc) * Cs j ≤ Af := by
          rw [hAf]; have := hCs 0; have := hCs 1; have := hCs 2
          gcongr
          interval_cases j <;> linarith
        calc _ ≤ Af * z ^ (-beta S.p + j / S.p) := by gcongr
          _ ≤ _ := by gcongr
    · have hev : g =ᶠ[nhds z] fun _ => 0 := by
        simp only [mem_Ioo, not_and_or, not_lt] at hz
        rcases hz with hz | hz
        · filter_upwards [Iio_mem_nhds (show z < 3 * Y / 10 by linarith)] with w hw
          simp only [hg]; rw [c05_aux_chiY_zero hY0 (Or.inl (le_of_lt hw))]; simp
        · filter_upwards [Ioi_mem_nhds (show 7 * Y / 2 < z by linarith)] with w hw
          simp only [hg]; rw [c05_aux_chiY_zero hY0 (Or.inr (le_of_lt hw))]; simp
      rw [hev.iteratedDeriv_eq, iteratedDeriv_const, ite_self, norm_zero]
      · have := hKL0 k; have := Real.rpow_pos_of_pos hY0 (-beta S.p + ((k : ℝ) - 1) / S.p)
        positivity
  intro k hk z
  rw [hvk k]
  simp only
  rw [abs_mul, abs_neg, abs_two]
  calc 2 * |(iteratedDeriv k g z).re| ≤ 2 * ‖iteratedDeriv k g z‖ := by
        gcongr; exact Complex.abs_re_le_norm _
    _ ≤ 2 * (KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af *
        Y ^ (-beta S.p + ((k : ℝ) - 1) / S.p)) := by gcongr; exact hgk k hk z
    _ ≤ K * Y ^ (-beta S.p + ((k : ℝ) - 1) / S.p) := by
        rw [← mul_assoc]; gcongr; exact hKk k hk

set_option maxHeartbeats 800000 in
/-- Data for lem:c05_vY_bounds (formulas). -/
theorem c05_aux_vY_data2 (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ContDiff ℝ (⊤ : ℕ∞) (res_vY S.p R ε μ Y) ∧
        (∀ z ∈ Icc (Y / 2) (3 * Y),
          deriv (res_vY S.p R ε μ Y) z =
            2 * (fam_Z S.p R ε μ z + (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ z ^ 3).re ∧
          deriv (deriv (res_vY S.p R ε μ Y)) z = 2 * (deriv (fam_Z S.p R ε μ) z +
            3 * (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ z ^ 2 * deriv (fam_Z S.p R ε μ) z).re) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  choose Cs hCs hsb using hsym
  obtain ⟨Cc, hCc, hsc⟩ := c05_small_constants S
  choose KL hKL0 hKL using c05_aux_cutoff_leibniz
  set Af : ℝ := (1 + Cc) * (Cp + Cs 0 + Cs 1 + Cs 2) with hAf
  have hAf0 : 0 ≤ Af := by have := hCs 0; have := hCs 1; have := hCs 2; positivity
  set K : ℝ := 2 * ∑ k ∈ Finset.range 4, KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af + 1
    with hK
  have hKk : ∀ k, k ≤ 3 → 2 * (KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af) ≤ K := by
    intro k hk
    have : KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af ≤
        ∑ k ∈ Finset.range 4, KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af :=
      Finset.single_le_sum (f := fun k => KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af)
        (fun j _ => by have := hKL0 j; positivity) (Finset.mem_range.mpr (by omega))
    rw [hK]; linarith
  refine ⟨max Rp Rs, hRp.trans (le_max_left _ _), K, by
    have : 0 ≤ ∑ k ∈ Finset.range 4, KL k * 4 ^ (|-beta S.p + ((k : ℝ) - 1) / S.p + k| + k) * Af :=
      Finset.sum_nonneg fun j _ => by have := hKL0 j; positivity
    positivity, ?_⟩
  intro ε μ R Y ht
  have htp := c05_aux_tuple_mono (le_max_left Rp Rs) ht
  have hts := c05_aux_tuple_mono (le_max_right Rp Rs) ht
  have hR : 1 ≤ R := hRp.trans htp.2.2.2.1
  have hR0 : 0 < R := by linarith
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hRY : R < 3 * Y / 10 := by linarith
  have hcc : |c_cubic S.p ε| ≤ Cc := by
    have := hsc ε μ ht.1 ht.2.1 ht.2.2.1
    have := abs_nonneg (c_eps S.p ε); have := abs_nonneg (n_eps S.p ε)
    have := abs_nonneg (c_log S.p ε μ)
    have : Cc * ε ≤ Cc := by nlinarith [ht.2.1, S.hε₀_le]
    linarith
  set c : ℂ := (c_cubic S.p ε : ℂ) with hc
  have hcn : ‖c‖ ≤ Cc := by rw [hc, Complex.norm_real, Real.norm_eq_abs]; exact hcc
  set Z := fam_Z S.p R ε μ with hZ
  set G : ℝ → ℂ := fun t => Z t + c * Z t ^ 3 with hG
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsb 0 ε μ R Y hts t ht'.le).1.1
    have : 0 < t ^ (1 / S.p) / 2 := by have : 0 < t := by linarith
                                       positivity
    linarith
  obtain ⟨⟨hZi, hZ3i, -⟩, -⟩ := hprim ε μ R Y htp R le_rfl
  have hGi : IntegrableOn G (Ioi R) := hZi.add (hZ3i.const_mul _)
  have hZs : ∀ t, R < t → ContDiffAt ℝ (⊤ : ℕ∞) Z t := fun t ht' =>
    c05_aux_Z_smooth S.p R ε μ hp hp1 hR0 (by linarith) (hpos t ht').ne'
  have hGs : ∀ t, R < t → ContDiffAt ℝ (⊤ : ℕ∞) G t := fun t ht' =>
    (hZs t ht').add (contDiffAt_const.mul ((hZs t ht').pow 3))
  have hGc : ContinuousOn G (Ioi R) := fun t ht' => (hGs t ht').continuousAt.continuousWithinAt
  set T : ℝ → ℂ := fun z => ∫ t in Ioi z, G t with hT
  have hTd : ∀ z, R < z → HasDerivAt T (-G z) z := fun z hz =>
    c05_aux_tail_hasDeriv G R hGi hGc hz
  have hTs : ContDiffOn ℝ (⊤ : ℕ∞) T (Ioi R) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz => (hTd z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact ContDiffOn.congr (f := fun z => -G z) (fun z hz => (hGs z hz).neg.contDiffWithinAt)
      (fun z hz => (hTd z hz).deriv)
  obtain ⟨hgs, -⟩ := c05_aux_cutoff_mul (n := (⊤ : ℕ∞)) hY0 hRY
    (fun t ht' => hTs.contDiffAt (Ioi_mem_nhds ht'))
  set g : ℝ → ℂ := fun z => (res_chiY Y z : ℂ) * T z with hg
  have hv : res_vY S.p R ε μ Y = fun z => -2 * (g z).re := by
    funext z
    simp only [res_vY, hg, hT, hG]
    split_ifs with h
    · rw [Complex.re_ofReal_mul]; ring
    · rw [c05_aux_chiY_zero hY0 (Or.inl (by linarith [not_lt.mp h]))]; simp
  have hvs : ContDiff ℝ (⊤ : ℕ∞) (res_vY S.p R ε μ Y) := by
    rw [hv]; exact contDiff_const.mul (Complex.reCLM.contDiff.comp hgs)
  have hvk : ∀ k, iteratedDeriv k (res_vY S.p R ε μ Y) = fun z => -2 * (iteratedDeriv k g z).re := by
    intro k; rw [hv]; exact c05_aux_iteratedDeriv_re hgs (-2) k
  have hTi : ∀ z, R < z → ∀ i : ℕ, iteratedDeriv (i + 1) T z = -(iteratedDeriv i G z) := by
    intro z hz i
    rw [iteratedDeriv_succ']
    have : deriv T =ᶠ[nhds z] fun w => -G w := by
      filter_upwards [Ioi_mem_nhds hz] with w hw using (hTd w hw).deriv
    rw [this.iteratedDeriv_eq, iteratedDeriv_fun_neg]
  have hZon : ContDiffOn ℝ (⊤ : ℕ∞) Z (Ioi R) := fun t ht' => (hZs t ht').contDiffWithinAt
  have hZ'on := hZon.deriv_of_isOpen isOpen_Ioi (m := (⊤ : ℕ∞)) (by simp)
  have hZd : ∀ z, R < z → HasDerivAt Z (deriv Z z) z := fun z hz =>
    ((hZs z hz).differentiableAt (by simp)).hasDerivAt
  have e1v : deriv (res_vY S.p R ε μ Y) = iteratedDeriv 1 (res_vY S.p R ε μ Y) :=
    iteratedDeriv_one.symm
  have e2v : deriv (deriv (res_vY S.p R ε μ Y)) = iteratedDeriv 2 (res_vY S.p R ε μ Y) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hint : ∀ z ∈ Ioo (Y / 2) (3 * Y),
      iteratedDeriv 1 (res_vY S.p R ε μ Y) z = 2 * (Z z + c * Z z ^ 3).re ∧
      iteratedDeriv 2 (res_vY S.p R ε μ Y) z =
        2 * (deriv Z z + 3 * c * Z z ^ 2 * deriv Z z).re := by
    intro z hz
    have hzR : R < z := by linarith [hz.1]
    have hev : g =ᶠ[nhds z] T := by
      filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
      show (res_chiY Y w : ℂ) * T w = T w
      rw [c05_aux_chiY_one hY0 ⟨hw.1.le, hw.2.le⟩, Complex.ofReal_one, one_mul]
    have hGd : HasDerivAt G (deriv Z z + c * ((3 : ℕ) * Z z ^ 2 * deriv Z z)) z := by
      have := (hZd z hzR).add (((hZd z hzR).fun_pow 3).const_mul c)
      convert this using 1
    rw [hvk, hvk]
    simp only
    rw [hev.iteratedDeriv_eq, hev.iteratedDeriv_eq, hTi z hzR 0, hTi z hzR 1, iteratedDeriv_zero,
      iteratedDeriv_one, hGd.deriv]
    constructor
    · rw [Complex.neg_re]; ring
    · rw [Complex.neg_re]; push_cast; ring_nf
  have hvc : ∀ k : ℕ, Continuous (iteratedDeriv k (res_vY S.p R ε μ Y)) := fun k =>
    hvs.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr le_top)
  have hY2R : R < Y / 2 := by linarith
  have hYlt : Y / 2 < 3 * Y := by linarith
  have hGcz : ∀ z, R < z → ContinuousAt (fun z => 2 * (Z z + c * Z z ^ 3).re) z := fun z hz => by
    show ContinuousAt ((fun w : ℂ => 2 * w.re) ∘ G) z
    exact ((continuous_const.mul Complex.continuous_re).continuousAt).comp (hGs z hz).continuousAt
  have hG'cz : ∀ z, R < z →
      ContinuousAt (fun z => 2 * (deriv Z z + 3 * c * Z z ^ 2 * deriv Z z).re) z := by
    intro z hz
    have h1 : ContinuousAt (deriv Z) z := (hZ'on.continuousOn.continuousAt (Ioi_mem_nhds hz))
    have h2 : ContinuousAt Z z := (hZs z hz).continuousAt
    show ContinuousAt ((fun w : ℂ => 2 * w.re) ∘ (fun z => deriv Z z + 3 * c * Z z ^ 2 * deriv Z z)) z
    exact ((continuous_const.mul Complex.continuous_re).continuousAt).comp
      (h1.add (((continuous_const.continuousAt.mul (h2.pow 2))).mul h1))
  clear_value g T G Z c
  refine ⟨hvs, fun z hz => ?_⟩
  · rw [e2v, e1v]
    have hsub : Ioo (Y / 2) (3 * Y) ⊆ Icc (Y / 2) (3 * Y) := Ioo_subset_Icc_self
    have hcl : Icc (Y / 2) (3 * Y) ⊆ closure (Ioo (Y / 2) (3 * Y)) := by
      rw [closure_Ioo hYlt.ne]
    have hRI : ∀ x ∈ Icc (Y / 2) (3 * Y), R < x := fun x hx => by linarith [hx.1]
    have Q1 : EqOn (iteratedDeriv 1 (res_vY S.p R ε μ Y)) (fun z => 2 * (Z z + c * Z z ^ 3).re)
        (Icc (Y / 2) (3 * Y)) :=
      Set.EqOn.of_subset_closure (fun x hx => (hint x hx).1) (hvc 1).continuousOn
        (fun x hx => (hGcz x (hRI x hx)).continuousWithinAt) hsub hcl
    have Q2 : EqOn (iteratedDeriv 2 (res_vY S.p R ε μ Y))
        (fun z => 2 * (deriv Z z + 3 * c * Z z ^ 2 * deriv Z z).re) (Icc (Y / 2) (3 * Y)) :=
      Set.EqOn.of_subset_closure (fun x hx => (hint x hx).2) (hvc 2).continuousOn
        (fun x hx => (hG'cz x (hRI x hx)).continuousWithinAt) hsub hcl
    exact ⟨Q1 hz, Q2 hz⟩

/-- Helper for lem:c05_vY_bounds. -/
theorem c05_aux_Delta_min {h : ℝ → ℝ} (hd : Differentiable ℝ h) {a b : ℝ}
    (h0 : ∀ x, |h x| ≤ a) (h1 : ∀ x, |deriv h x| ≤ b) (y s : ℝ) :
    |c05_plane_wave_Delta h y s| ≤ min (b * |s|) (2 * a) := by
  unfold c05_plane_wave_Delta
  refine le_min ?_ ?_
  · have := c05_aux_incr_le hd h1 y (y - s)
    rwa [show y - (y - s) = s by ring] at this
  · calc |h y - h (y - s)| ≤ |h y| + |h (y - s)| := abs_sub _ _
      _ ≤ 2 * a := by linarith [h0 y, h0 (y - s)]

/-- Helper for lem:c05_vY_bounds. -/
theorem c05_aux_sin_derivs (A L b : ℝ) :
    deriv (fun z => A * Real.sin (L * z + b)) = (fun z => A * L * Real.cos (L * z + b)) ∧
    deriv (fun z => A * L * Real.cos (L * z + b)) = (fun z => -(A * L * L) * Real.sin (L * z + b)) ∧
    deriv (fun z => -(A * L * L) * Real.sin (L * z + b)) =
      (fun z => -(A * L * L * L) * Real.cos (L * z + b)) := by
  have hlin : ∀ z, HasDerivAt (fun z => L * z + b) L z := fun z => by
    simpa using ((hasDerivAt_id z).const_mul L).add_const b
  refine ⟨funext fun z => ?_, funext fun z => ?_, funext fun z => ?_⟩
  · rw [((hlin z).sin.const_mul A).deriv]; ring
  · rw [((hlin z).cos.const_mul (A * L)).deriv]; ring
  · rw [((hlin z).sin.const_mul (-(A * L * L))).deriv]; ring

/-- Blueprint: lem:c05_vY_bounds.  For `y ∈ [Y,2Y]`, `λ = λ(y)`: (1) the formulas for `v_Y'`,
`v_Y''` on `[Y/2,3Y]`; (2) sup bounds for `v_Y, v_Y', v_Y''` and `P_y, P_y', P_y''`;
(3) increment bounds for `h ∈ {v_Y, P_y}`. -/
theorem c05_vY_bounds (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y),
          let lam := fam_lambda S.p ε μ y
          let v := res_vY S.p R ε μ Y
          let P := c05_plane_wave S.p R ε μ y
          -- (1)
          (∀ z ∈ Icc (Y / 2) (3 * Y),
            deriv v z = 2 * (fam_Z S.p R ε μ z + (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ z ^ 3).re ∧
            deriv (deriv v) z = 2 * (deriv (fam_Z S.p R ε μ) z +
              3 * (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ z ^ 2 * deriv (fam_Z S.p R ε μ) z).re) ∧
          -- (2)
          (∀ z : ℝ, |v z| ≤ C * Y ^ (-beta S.p) * lam⁻¹ ∧ |deriv v z| ≤ C * Y ^ (-beta S.p) ∧
            |deriv (deriv v) z| ≤ C * Y ^ (-beta S.p) * lam) ∧
          (∀ k : ℕ, k ≤ 2 → ∀ z : ℝ,
            |iteratedDeriv k P z| ≤ 2 * ‖fam_Z S.p R ε μ y‖ * lam ^ ((k : ℝ) - 1) ∧
            2 * ‖fam_Z S.p R ε μ y‖ * lam ^ ((k : ℝ) - 1) ≤ C * Y ^ (-beta S.p) * lam ^ ((k : ℝ) - 1)) ∧
          -- (3)
          (∀ h ∈ ({v, P} : Set (ℝ → ℝ)), ∀ s : ℝ,
            |c05_plane_wave_Delta h y s| ≤ C * Y ^ (-beta S.p) * min |s| lam⁻¹ ∧
            |c05_plane_wave_Delta (deriv h) y s| ≤ C * Y ^ (-beta S.p) * min 1 (lam * |s|) ∧
            |c05_plane_wave_Delta (deriv (deriv h)) y s| ≤
              C * Y ^ (-beta S.p) * lam * min 1 (lam * |s|)) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hip2 : 1 / S.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have hβ0 : 0 ≤ beta S.p := by unfold beta; positivity
  obtain ⟨R1, hR1, K, hK, hd1⟩ := c05_aux_vY_data1 S
  obtain ⟨R2, hR2, -, -, hd2⟩ := c05_aux_vY_data2 S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  set C1 : ℝ := 8 * K + 2 * C₀ with hC1
  refine ⟨max (max R1 R2) Rs, hR1.trans ((le_max_left _ _).trans (le_max_left _ _)), 2 * C1,
    by positivity, ?_⟩
  intro ε μ R Y ht y hy lam v P
  have ht1 := c05_aux_tuple_mono ((le_max_left R1 R2).trans (le_max_left _ Rs)) ht
  have ht2 := c05_aux_tuple_mono ((le_max_right R1 R2).trans (le_max_left _ Rs)) ht
  have hts := c05_aux_tuple_mono (le_max_right (max R1 R2) Rs) ht
  have hR : 1 ≤ R := hR1.trans ht1.2.2.2.1
  have hY1 : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith [hy.1]
  obtain ⟨⟨hl1, hl2, -⟩, -, ⟨hZ0, -⟩, -⟩ := hs0 ε μ R Y hts y (by linarith [hy.1, ht.2.2.2.2])
  simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at hZ0
  set u := Y ^ (1 / S.p) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hY0 _
  have hlam1 : u / 2 ≤ lam := le_trans (by
    have : u ≤ y ^ (1 / S.p) := Real.rpow_le_rpow hY0.le hy.1 hip.le
    linarith) hl1
  have hlam2 : lam ≤ 8 * u := by
    refine hl2.trans ?_
    have : y ^ (1 / S.p) ≤ (2 * Y) ^ (1 / S.p) := Real.rpow_le_rpow hy0.le hy.2 hip.le
    rw [Real.mul_rpow (by norm_num) hY0.le] at this
    have h2 : (2 : ℝ) ^ (1 / S.p) ≤ 4 := by
      calc (2 : ℝ) ^ (1 / S.p) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hip2
        _ = 4 := by norm_num
    nlinarith
  have hlam0 : 0 < lam := by linarith
  have hYb : 0 ≤ Y ^ (-beta S.p) := (Real.rpow_pos_of_pos hY0 _).le
  have hZy : 2 * ‖fam_Z S.p R ε μ y‖ ≤ 2 * C₀ * Y ^ (-beta S.p) := by
    have : ‖fam_Z S.p R ε μ y‖ ≤ C₀ * y ^ (-beta S.p) := by
      linarith [norm_nonneg (c05_standing_Zmu0 S.p R μ y)]
    have : y ^ (-beta S.p) ≤ Y ^ (-beta S.p) :=
      Real.rpow_le_rpow_of_nonpos hY0 hy.1 (by linarith)
    nlinarith
  -- scale facts
  have e0 : Y ^ (-beta S.p + (((0 : ℕ) : ℝ) - 1) / S.p) = Y ^ (-beta S.p) * u⁻¹ := by
    rw [hu, ← Real.rpow_neg hY0.le, ← Real.rpow_add hY0]; congr 1; push_cast; ring
  have e1 : Y ^ (-beta S.p + (((1 : ℕ) : ℝ) - 1) / S.p) = Y ^ (-beta S.p) := by
    congr 1; push_cast; ring
  have e2 : Y ^ (-beta S.p + (((2 : ℕ) : ℝ) - 1) / S.p) = Y ^ (-beta S.p) * u := by
    rw [hu, ← Real.rpow_add hY0]; congr 1; push_cast; ring
  have e3 : Y ^ (-beta S.p + (((3 : ℕ) : ℝ) - 1) / S.p) = Y ^ (-beta S.p) * u * u := by
    rw [hu, ← Real.rpow_add hY0, ← Real.rpow_add hY0]; congr 1; push_cast; ring
  have hui : u⁻¹ ≤ 8 * lam⁻¹ := by
    rw [show 8 * lam⁻¹ = (lam / 8)⁻¹ by field_simp]
    exact inv_anti₀ (by positivity) (by linarith)
  have hC10 : 0 ≤ C1 := by positivity
  have hKC : 8 * K ≤ C1 := by rw [hC1]; linarith
  have hCC : 2 * C₀ ≤ C1 := by rw [hC1]; linarith
  -- sup bounds for `v`
  obtain ⟨hvs, hform⟩ := hd2 ε μ R Y ht2
  have hvb := hd1 ε μ R Y ht1
  have v0 : ∀ z, |v z| ≤ C1 * Y ^ (-beta S.p) * lam⁻¹ := by
    intro z
    have := hvb 0 (by norm_num) z
    rw [iteratedDeriv_zero, e0] at this
    refine this.trans ?_
    calc K * (Y ^ (-beta S.p) * u⁻¹) ≤ K * (Y ^ (-beta S.p) * (8 * lam⁻¹)) := by gcongr
      _ = (8 * K) * Y ^ (-beta S.p) * lam⁻¹ := by ring
      _ ≤ _ := by gcongr
  have v1 : ∀ z, |deriv v z| ≤ C1 * Y ^ (-beta S.p) := by
    intro z
    have := hvb 1 (by norm_num) z
    rw [iteratedDeriv_one, e1] at this
    refine this.trans (mul_le_mul_of_nonneg_right (by linarith) hYb)
  have v2 : ∀ z, |deriv (deriv v) z| ≤ C1 * Y ^ (-beta S.p) * lam := by
    intro z
    have := hvb 2 (by norm_num) z
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, e2] at this
    refine this.trans ?_
    calc K * (Y ^ (-beta S.p) * u) ≤ K * (Y ^ (-beta S.p) * (2 * lam)) := by gcongr; linarith
      _ = (2 * K) * Y ^ (-beta S.p) * lam := by ring
      _ ≤ _ := by gcongr; linarith
  have v3 : ∀ z, |deriv (deriv (deriv v)) z| ≤ C1 * Y ^ (-beta S.p) * lam * lam := by
    intro z
    have := hvb 3 (by norm_num) z
    rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
      e3] at this
    refine this.trans ?_
    have hu2 : u ≤ 2 * lam := by linarith
    calc K * (Y ^ (-beta S.p) * u * u) ≤ K * (Y ^ (-beta S.p) * (2 * lam) * (2 * lam)) := by gcongr
      _ = (4 * K) * Y ^ (-beta S.p) * lam * lam := by ring
      _ ≤ _ := by gcongr; linarith
  -- the plane wave
  set A := 2 * ‖fam_Z S.p R ε μ y‖ / lam with hA
  set b := Complex.arg (fam_Z S.p R ε μ y) - lam * y with hb
  have hP : P = fun z => A * Real.sin (lam * z + b) := by
    funext z; exact c05_aux_plane_wave_sin _ lam y z hlam0
  obtain ⟨d1, d2, d3⟩ := c05_aux_sin_derivs A lam b
  have hPd1 : deriv P = fun z => A * lam * Real.cos (lam * z + b) := by rw [hP, d1]
  have hPd2 : deriv (deriv P) = fun z => -(A * lam * lam) * Real.sin (lam * z + b) := by
    rw [hPd1, d2]
  have hPd3 : deriv (deriv (deriv P)) = fun z => -(A * lam * lam * lam) * Real.cos (lam * z + b) := by
    rw [hPd2, d3]
  have hA0 : 0 ≤ A := by positivity
  have hAl : A * lam = 2 * ‖fam_Z S.p R ε μ y‖ := by rw [hA]; field_simp
  have sinb : ∀ x, |Real.sin x| ≤ 1 := Real.abs_sin_le_one
  have cosb : ∀ x, |Real.cos x| ≤ 1 := Real.abs_cos_le_one
  have P0 : ∀ z, |P z| ≤ 2 * ‖fam_Z S.p R ε μ y‖ * lam⁻¹ := by
    intro z; rw [hP]; simp only
    rw [abs_mul, abs_of_nonneg hA0]
    calc A * |Real.sin (lam * z + b)| ≤ A * 1 := by gcongr; exact sinb _
      _ = _ := by rw [hA]; ring
  have P1 : ∀ z, |deriv P z| ≤ 2 * ‖fam_Z S.p R ε μ y‖ := by
    intro z; rw [hPd1]; simp only
    rw [abs_mul, abs_of_nonneg (by positivity), hAl]
    calc _ ≤ 2 * ‖fam_Z S.p R ε μ y‖ * 1 := by gcongr; exact cosb _
      _ = _ := by ring
  have P2 : ∀ z, |deriv (deriv P) z| ≤ 2 * ‖fam_Z S.p R ε μ y‖ * lam := by
    intro z; rw [hPd2]; simp only
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity), hAl]
    calc _ ≤ 2 * ‖fam_Z S.p R ε μ y‖ * lam * 1 := by gcongr; exact sinb _
      _ = _ := by ring
  have P3 : ∀ z, |deriv (deriv (deriv P)) z| ≤ 2 * ‖fam_Z S.p R ε μ y‖ * lam * lam := by
    intro z; rw [hPd3]; simp only
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity), hAl]
    calc _ ≤ 2 * ‖fam_Z S.p R ε μ y‖ * lam * lam * 1 := by gcongr; exact cosb _
      _ = _ := by ring
  have hZC : 2 * ‖fam_Z S.p R ε μ y‖ ≤ C1 * Y ^ (-beta S.p) :=
    hZy.trans (mul_le_mul_of_nonneg_right hCC hYb)
  have hPs : ContDiff ℝ (⊤ : ℕ∞) P := by
    rw [hP]; exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id |>.add contDiff_const))
  -- generic Δ bounds
  have hDelta : ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ z, |h z| ≤ C1 * Y ^ (-beta S.p) * lam⁻¹) → (∀ z, |deriv h z| ≤ C1 * Y ^ (-beta S.p)) →
      (∀ z, |deriv (deriv h) z| ≤ C1 * Y ^ (-beta S.p) * lam) →
      (∀ z, |deriv (deriv (deriv h)) z| ≤ C1 * Y ^ (-beta S.p) * lam * lam) → ∀ s : ℝ,
      |c05_plane_wave_Delta h y s| ≤ 2 * C1 * Y ^ (-beta S.p) * min |s| lam⁻¹ ∧
      |c05_plane_wave_Delta (deriv h) y s| ≤ 2 * C1 * Y ^ (-beta S.p) * min 1 (lam * |s|) ∧
      |c05_plane_wave_Delta (deriv (deriv h)) y s| ≤
        2 * C1 * Y ^ (-beta S.p) * lam * min 1 (lam * |s|) := by
    intro h hh b0 b1 b2 b3 s
    have dh : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n h) := fun n =>
      hh.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)
    have dh0 : Differentiable ℝ h := by simpa using dh 0
    have dh1 : Differentiable ℝ (deriv h) := by simpa using dh 1
    have dh2 : Differentiable ℝ (deriv (deriv h)) := by
      have := dh 2; rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at this
    have hX : 0 ≤ C1 * Y ^ (-beta S.p) := by positivity
    refine ⟨(c05_aux_Delta_min dh0 b0 b1 y s).trans ?_, (c05_aux_Delta_min dh1 b1 b2 y s).trans ?_,
      (c05_aux_Delta_min dh2 b2 b3 y s).trans ?_⟩
    · rw [mul_min_of_nonneg _ _ (by positivity)]
      have := mul_nonneg hX (abs_nonneg s)
      exact min_le_min (by linarith [show 2 * C1 * Y ^ (-beta S.p) * |s| =
        2 * (C1 * Y ^ (-beta S.p) * |s|) by ring]) (le_of_eq (by ring))
    · rw [mul_min_of_nonneg _ _ (by positivity), min_comm]
      have := mul_nonneg (mul_nonneg hX hlam0.le) (abs_nonneg s)
      exact min_le_min (le_of_eq (by ring)) (by linarith [show 2 * C1 * Y ^ (-beta S.p) * (lam * |s|) =
        2 * (C1 * Y ^ (-beta S.p) * lam * |s|) by ring])
    · rw [mul_min_of_nonneg _ _ (by positivity), min_comm]
      have := mul_nonneg (mul_nonneg (mul_nonneg hX hlam0.le) hlam0.le) (abs_nonneg s)
      exact min_le_min (le_of_eq (by ring)) (by linarith [show 2 * C1 * Y ^ (-beta S.p) * lam * (lam * |s|) =
        2 * (C1 * Y ^ (-beta S.p) * lam * lam * |s|) by ring])
  have hZC2 : 2 * ‖fam_Z S.p R ε μ y‖ ≤ 2 * C1 * Y ^ (-beta S.p) :=
    hZC.trans (by gcongr; linarith)
  refine ⟨fun z hz => hform z hz, fun z => ⟨(v0 z).trans (by gcongr; linarith),
    (v1 z).trans (by gcongr; linarith), (v2 z).trans (by gcongr; linarith)⟩, fun k hk z => ?_, ?_⟩
  · interval_cases k
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_sub, Real.rpow_neg_one]
      exact ⟨P0 z, mul_le_mul_of_nonneg_right hZC2 (inv_nonneg.mpr hlam0.le)⟩
    · simp only [iteratedDeriv_one, Nat.cast_one, sub_self, Real.rpow_zero, mul_one]
      exact ⟨P1 z, hZC2⟩
    · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      simp only [Nat.cast_add, Nat.cast_one, show (1 : ℝ) + 1 - 1 = 1 by norm_num, Real.rpow_one]
      exact ⟨P2 z, mul_le_mul_of_nonneg_right hZC2 hlam0.le⟩
  · intro h hh s
    rcases hh with rfl | rfl
    · exact hDelta _ hvs v0 v1 v2 v3 s
    · exact hDelta _ hPs (fun z => (P0 z).trans (mul_le_mul_of_nonneg_right hZC (inv_nonneg.mpr hlam0.le)))
        (fun z => (P1 z).trans hZC)
        (fun z => (P2 z).trans (mul_le_mul_of_nonneg_right hZC hlam0.le))
        (fun z => (P3 z).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZC hlam0.le)
          hlam0.le)) s

/-- Helper for lem:c05_frozen_frequency. -/
theorem c05_aux_tY {Y t θ : ℝ} (hY : 0 < Y) (ht : t ∈ Ioo (Y / 4) (4 * Y)) (hθ : |θ| ≤ 6) :
    t ^ θ ≤ (4 : ℝ) ^ (6 : ℝ) * Y ^ θ :=
  (c05_aux_yY_rpow hY ht θ).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ) (Real.rpow_pos_of_pos hY _).le)

/-- Helper for lem:c05_frozen_frequency. -/
theorem c05_aux_norm4 (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  linarith

set_option maxHeartbeats 800000 in
/-- Data for lem:c05_frozen_frequency. -/
theorem c05_aux_ff_data (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ t : ℝ, |t - y| ≤ Y / 4 →
          let L := fam_lambda S.p ε μ y
          let Z := fam_Z S.p R ε μ
          0 ≤ L ∧ HasDerivAt Z (deriv Z t) t ∧ HasDerivAt (deriv Z) (deriv (deriv Z) t) t ∧
          ‖deriv Z t - Complex.I * (L : ℂ) * Z t‖ ≤
            K * Y ^ (-beta S.p - 1) * (1 + L * |t - y|) ∧
          ‖deriv (deriv Z) t - Complex.I * (L : ℂ) * deriv Z t‖ ≤
            K * Y ^ (-beta S.p - 1) * L * (1 + L * |t - y|) ∧
          ‖Z t ^ 3‖ ≤ K * Y ^ (-3 * beta S.p) ∧
          ‖deriv (fun u => Z u ^ 3) t‖ ≤ K * Y ^ (-3 * beta S.p) * L ∧
          HasDerivAt (fun u => Z u ^ 3) (deriv (fun u => Z u ^ 3) t) t ∧
          ‖Z t ^ 2 * deriv Z t‖ ≤ K * Y ^ (-3 * beta S.p) * L ∧
          ‖2 * Z t * deriv Z t * deriv Z t + Z t ^ 2 * deriv (deriv Z) t‖ ≤
            K * Y ^ (-3 * beta S.p) * L ^ 2 := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hip2 : 1 / S.p ≤ 4 / 3 := by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  have hβ2 : beta S.p ≤ 7 / 6 := by
    unfold beta; rw [div_le_iff₀ (by positivity)]; linarith
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  choose Cs hCs hsb using hsym
  set M : ℝ := (4 : ℝ) ^ (6 : ℝ) with hM
  have hM1 : 1 ≤ M := Real.one_le_rpow (by norm_num) (by norm_num)
  set C₀ := Cs 0
  set C₁ := Cs 1
  set C₂ := Cs 2
  have h0 := (hCs 0).le
  have h1 := (hCs 1).le
  have h2 := (hCs 2).le
  set K : ℝ := C₁ * M + C₀ ^ 2 * M + 2 * C₂ * M + 4 * C₁ * M + 2 * C₀ * C₁ * M ^ 2 +
    2 * C₀ * C₁ * M + C₀ * M + 2 * C₁ * M + 2 * C₀ ^ 2 * C₁ * M ^ 3 +
    4 * (2 * C₀ * C₁ ^ 2 * M ^ 3 + C₀ ^ 2 * C₂ * M ^ 3) + 1 with hK
  refine ⟨Rs, hRs, K, by positivity, ?_⟩
  intro ε μ R Y ht y hy t hty L Z
  have hR : 1 ≤ R := hRs.trans ht.2.2.2.1
  have hR0 : 0 < R := by linarith
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith [hy.1]
  have hta := abs_le.mp hty
  have htI : t ∈ Ioo (Y / 4) (4 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hRt : R ≤ t := by linarith [hy.1]
  have ht0 : 0 < t := by linarith
  have hty2 : |t - y| ≤ y / 2 := by linarith [hy.1]
  -- the symbol bounds at `t` and `y`
  obtain ⟨⟨hl1, -, -, -, -⟩, -, -, -, -, h6⟩ := hsb 0 ε μ R Y ht y (by linarith [hy.1])
  obtain ⟨⟨hlt1, hlt2, -, -, -⟩, -, ⟨hZ0, hZ30, hid, -⟩, -, -, -⟩ := hsb 0 ε μ R Y ht t hRt
  obtain ⟨⟨-, -, hlk1, -, -⟩, ⟨hA1, -, -⟩, ⟨hZ1, hZ31, -, -⟩, -, -, -⟩ := hsb 1 ε μ R Y ht t hRt
  obtain ⟨-, ⟨hA2, -, -⟩, ⟨hZ2, -, -, -⟩, -, -, -⟩ := hsb 2 ε μ R Y ht t hRt
  obtain ⟨h61, h62, h63⟩ := h6 t hRt hty2
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    zero_div, add_zero] at hZ0 hZ30 hlk1 hA1 hZ1 hZ31 hA2 hZ2
  have e2 : ∀ f : ℝ → ℂ, iteratedDeriv 2 f = deriv (deriv f) := fun f => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [e2, e2] at hA2 hZ2
  -- smoothness on `(R, ∞)`
  have hpos : ∀ u, R < u → 0 < fam_lambda S.p ε μ u := by
    intro u hu
    have := (hsb 0 ε μ R Y ht u hu.le).1.1
    have : 0 < u ^ (1 / S.p) / 2 := by have : 0 < u := by linarith
                                       positivity
    linarith
  have hU : IsOpen (Ioi R) := isOpen_Ioi
  have hZs : ContDiffOn ℝ (⊤ : ℕ∞) Z (Ioi R) := fun u hu =>
    (c05_aux_Z_smooth S.p R ε μ hp hp1 hR0 (by linarith [show R < u from hu])
      (hpos u hu).ne').contDiffWithinAt
  have hAs : ContDiffOn ℝ (⊤ : ℕ∞) (c05_standing_A S.p ε μ) (Ioi R) := fun u hu =>
    ((contDiffAt_const.mul (c05_aux_astar_smooth S.p hp hp1 (by linarith [show R < u from hu]))).mul
      (c05_aux_ofReal ((c05_aux_lambda_smooth S.p ε μ (by linarith [show R < u from hu])).rpow_const_of_ne
        (hpos u hu).ne'))).contDiffWithinAt
  have hZ's := hZs.deriv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)
  have hA's := hAs.deriv_of_isOpen hU (m := (⊤ : ℕ∞)) (by simp)
  have hdiff : ∀ {f : ℝ → ℂ}, ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi R) → ∀ u, R < u → DifferentiableAt ℝ f u :=
    fun hf u hu => (hf.contDiffAt (hU.mem_nhds hu)).differentiableAt (by simp)
  have hRt' : R < t := by linarith [hy.1]
  have hZd : HasDerivAt Z (deriv Z t) t := (hdiff hZs t hRt').hasDerivAt
  have hZ'd : HasDerivAt (deriv Z) (deriv (deriv Z) t) t := (hdiff hZ's t hRt').hasDerivAt
  have hA'd : HasDerivAt (deriv (c05_standing_A S.p ε μ)) (deriv (deriv (c05_standing_A S.p ε μ)) t) t :=
    (hdiff hA's t hRt').hasDerivAt
  have hld : HasDerivAt (fam_lambda S.p ε μ) (deriv (fam_lambda S.p ε μ) t) t :=
    ((c05_aux_lambda_smooth S.p ε μ (n := 1) ht0).differentiableAt one_ne_zero).hasDerivAt
  have hΦd : HasDerivAt (c05_standing_Phi S.p R ε μ) (fam_lambda S.p ε μ t) t :=
    (c05_aux_Psi_hasDeriv S.p R ε μ hR0 ht0).sub_const (π / 4)
  set E := Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ t : ℂ)) with hE
  have hEn : ‖E‖ = 1 := by rw [hE, mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  -- the second derivative identity
  have hZ2id : deriv (deriv Z) t = Complex.I * ((deriv (fam_lambda S.p ε μ) t : ℝ) : ℂ) * Z t +
      Complex.I * (fam_lambda S.p ε μ t : ℂ) * deriv Z t +
      deriv (deriv (c05_standing_A S.p ε μ)) t * E +
      Complex.I * (fam_lambda S.p ε μ t : ℂ) * deriv (c05_standing_A S.p ε μ) t * E := by
    have h1 : HasDerivAt (fun u => deriv Z u - Complex.I * (fam_lambda S.p ε μ u : ℂ) * Z u)
        (deriv (deriv Z) t - (Complex.I * ((deriv (fam_lambda S.p ε μ) t : ℝ) : ℂ) * Z t +
          Complex.I * (fam_lambda S.p ε μ t : ℂ) * deriv Z t)) t := by
      have := hZ'd.sub ((hld.ofReal_comp.const_mul Complex.I).mul hZd)
      convert this using 1
    have h2 : HasDerivAt (fun u => deriv (c05_standing_A S.p ε μ) u *
        Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ u : ℂ)))
        (deriv (deriv (c05_standing_A S.p ε μ)) t * E +
          deriv (c05_standing_A S.p ε μ) t * (E * (Complex.I * (fam_lambda S.p ε μ t : ℂ)))) t :=
      hA'd.mul (hΦd.ofReal_comp.const_mul Complex.I).cexp
    have hev : (fun u => deriv Z u - Complex.I * (fam_lambda S.p ε μ u : ℂ) * Z u) =ᶠ[nhds t]
        fun u => deriv (c05_standing_A S.p ε μ) u *
          Complex.exp (Complex.I * (c05_standing_Phi S.p R ε μ u : ℂ)) := by
      filter_upwards [hU.mem_nhds hRt'] with u hu
      exact (hsb 0 ε μ R Y ht u (le_of_lt hu)).2.2.1.2.2.1
    have := (h1.congr_of_eventuallyEq hev.symm).unique h2
    linear_combination this
  -- scale bookkeeping
  set a := Y ^ (-beta S.p) with ha
  set v := Y ^ (1 / S.p) with hv
  set i := Y ^ (-1 : ℝ) with hi
  have ha0 : 0 ≤ a := (Real.rpow_pos_of_pos hY0 _).le
  have hv0 : 0 ≤ v := (Real.rpow_pos_of_pos hY0 _).le
  have hi0 : 0 ≤ i := (Real.rpow_pos_of_pos hY0 _).le
  have hrp : ∀ x z : ℝ, Y ^ x * Y ^ z = Y ^ (x + z) := fun x z => (Real.rpow_add hY0 x z).symm
  have hiv : i ≤ v := (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
  have hL0 : 0 ≤ L := le_trans (by positivity) hl1
  have hvL : v ≤ 2 * L := by
    have : Y ^ (1 / S.p) ≤ y ^ (1 / S.p) := Real.rpow_le_rpow hY0.le hy.1 hip.le
    show Y ^ (1 / S.p) ≤ 2 * fam_lambda S.p ε μ y; linarith
  have tb : ∀ θ : ℝ, |θ| ≤ 6 → t ^ θ ≤ M * Y ^ θ := fun θ hθ => c05_aux_tY hY0 htI hθ
  have tb' : ∀ θ c : ℝ, |θ| ≤ 6 → 0 ≤ c → Y ^ θ = c → t ^ θ ≤ M * c := fun θ c hθ _ he => by
    rw [← he]; exact tb θ hθ
  have ab : ∀ θ : ℝ, -6 ≤ θ → θ ≤ 6 → |θ| ≤ 6 := fun θ h1 h2 => abs_le.mpr ⟨h1, h2⟩
  have h2p : 2 / S.p = 2 * (1 / S.p) := by ring
  have i1 : Y ^ (-beta S.p + 1 / S.p) = a * v := by rw [ha, hv, hrp]
  have i2 : Y ^ (-beta S.p + 2 / S.p) = a * v * v := by
    rw [ha, hv, hrp, hrp]; ring_nf
  have i3 : Y ^ (-beta S.p - 1) = a * i := by rw [ha, hi, hrp]; ring_nf
  have i4 : Y ^ (-beta S.p - 2) = a * i * i := by rw [ha, hi, hrp, hrp]; ring_nf
  have i5 : Y ^ (1 / S.p - 1) = v * i := by rw [hv, hi, hrp]; ring_nf
  have i6 : Y ^ (-3 * beta S.p) = a * a * a := by rw [ha, hrp, hrp]; ring_nf
  have i7 : Y ^ (-3 * beta S.p + 1 / S.p) = a * a * a * v := by
    rw [ha, hv, hrp, hrp, hrp]; ring_nf
  have eZ : ‖Z t‖ ≤ C₀ * (M * a) := by
    refine le_trans (by linarith [norm_nonneg (c05_standing_Zmu0 S.p R μ t)]) (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) ha0 rfl) h0)
  have eZ1 : ‖deriv Z t‖ ≤ C₁ * (M * (a * v)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) (by positivity) i1) h1)
    linarith [norm_nonneg (deriv (c05_standing_Zmu0 S.p R μ) t)]
  have eZ2 : ‖deriv (deriv Z) t‖ ≤ C₂ * (M * (a * v * v)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) (by positivity) i2) h2)
    linarith [norm_nonneg (deriv (deriv (c05_standing_Zmu0 S.p R μ)) t)]
  have eA1 : ‖deriv (c05_standing_A S.p ε μ) t‖ ≤ C₁ * (M * (a * i)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) (by positivity) i3) h1)
    linarith [norm_nonneg (deriv (c05_standing_A_zero S.p μ) t)]
  have eA2 : ‖deriv (deriv (c05_standing_A S.p ε μ)) t‖ ≤ C₂ * (M * (a * i * i)) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) (by positivity) i4) h2)
    linarith [norm_nonneg (deriv (deriv (c05_standing_A_zero S.p μ)) t)]
  have el1 : |deriv (fam_lambda S.p ε μ) t| ≤ C₁ * (M * (v * i)) :=
    hlk1.trans (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) (by positivity) i5) h1)
  have eZ3 : ‖Z t ^ 3‖ ≤ C₀ * (M * (a * a * a)) :=
    hZ30.trans (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) (by positivity) i6) h0)
  have eZ31 : ‖deriv (fun u => Z u ^ 3) t‖ ≤ C₁ * (M * (a * a * a * v)) :=
    hZ31.trans (mul_le_mul_of_nonneg_left
      (tb' _ _ (ab _ (by linarith) (by linarith)) (by positivity) i7) h1)
  have hd63 : |fam_lambda S.p ε μ t - L| ≤ C₀ * L * |t - y| * i := by
    refine h63.trans ?_
    rw [hi, Real.rpow_neg_one, div_eq_mul_inv]
    gcongr
    exact hy.1
  have hlt4 : fam_lambda S.p ε μ t ≤ 4 * L := h62
  rw [i3, i6]
  have hK0 : 0 ≤ K := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hKge : ∀ x : ℝ, 0 ≤ x → (x = C₁ * M ∨ x = C₀ ^ 2 * M ∨ x = 2 * C₂ * M + 4 * C₁ * M + 2 * C₀ * C₁ * M ^ 2 ∨
      x = 2 * C₀ * C₁ * M ∨ x = C₀ * M ∨ x = 2 * C₁ * M ∨ x = 2 * C₀ ^ 2 * C₁ * M ^ 3 ∨
      x = 4 * (2 * C₀ * C₁ ^ 2 * M ^ 3 + C₀ ^ 2 * C₂ * M ^ 3)) → x ≤ K := by
    intro x _ hx
    have := mul_nonneg (mul_nonneg h0 h1) (sq_nonneg M)
    have := mul_nonneg (mul_nonneg h0 h1) hM0
    have := mul_nonneg (mul_nonneg (sq_nonneg C₀) h1) (pow_nonneg hM0 3)
    have := mul_nonneg (mul_nonneg h0 (sq_nonneg C₁)) (pow_nonneg hM0 3)
    have := mul_nonneg (mul_nonneg (sq_nonneg C₀) h2) (pow_nonneg hM0 3)
    have := mul_nonneg h0 hM0; have := mul_nonneg h1 hM0; have := mul_nonneg h2 hM0
    have := mul_nonneg (sq_nonneg C₀) hM0
    have := mul_nonneg (mul_nonneg h0 h1) (pow_nonneg hM0 2)
    rw [hK]
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;> linarith
  have hai : 0 ≤ a * i := by positivity
  have hLt : 0 ≤ L * |t - y| := by positivity
  have hnI : ∀ (x : ℝ) (w : ℂ), ‖Complex.I * (x : ℂ) * w‖ = |x| * ‖w‖ := by
    intro x w; rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hlt0 : 0 ≤ fam_lambda S.p ε μ t := by linarith [show 0 ≤ L / 4 by positivity]
  refine ⟨hL0, hZd, hZ'd, ?_, ?_, ?_, ?_, ((hZd.pow 3).differentiableAt).hasDerivAt, ?_, ?_⟩
  · -- `w`
    have hw : deriv Z t - Complex.I * (L : ℂ) * Z t = deriv (c05_standing_A S.p ε μ) t * E +
        Complex.I * ((fam_lambda S.p ε μ t - L : ℝ) : ℂ) * Z t := by
      rw [← hid]; push_cast; ring
    rw [hw]
    calc _ ≤ ‖deriv (c05_standing_A S.p ε μ) t * E‖ +
          ‖Complex.I * ((fam_lambda S.p ε μ t - L : ℝ) : ℂ) * Z t‖ := norm_add_le _ _
      _ = ‖deriv (c05_standing_A S.p ε μ) t‖ + |fam_lambda S.p ε μ t - L| * ‖Z t‖ := by
          rw [norm_mul, hEn, mul_one, hnI]
      _ ≤ C₁ * (M * (a * i)) + (C₀ * L * |t - y| * i) * (C₀ * (M * a)) := by
          gcongr
      _ = (C₁ * M) * (a * i) + (C₀ ^ 2 * M) * ((a * i) * (L * |t - y|)) := by ring
      _ ≤ K * (a * i) + K * ((a * i) * (L * |t - y|)) := by
          gcongr
          · exact hKge _ (by positivity) (Or.inl rfl)
          · exact hKge _ (by positivity) (Or.inr (Or.inl rfl))
      _ = K * (a * i) * (1 + L * |t - y|) := by ring
  · -- `w'`
    have hw : deriv (deriv Z) t - Complex.I * (L : ℂ) * deriv Z t =
        Complex.I * ((deriv (fam_lambda S.p ε μ) t : ℝ) : ℂ) * Z t +
        Complex.I * ((fam_lambda S.p ε μ t - L : ℝ) : ℂ) * deriv Z t +
        deriv (deriv (c05_standing_A S.p ε μ)) t * E +
        Complex.I * ((fam_lambda S.p ε μ t : ℝ) : ℂ) * deriv (c05_standing_A S.p ε μ) t * E := by
      rw [hZ2id]; push_cast; ring
    rw [hw]
    have T1 : |deriv (fam_lambda S.p ε μ) t| * ‖Z t‖ ≤ (2 * C₀ * C₁ * M ^ 2) * ((a * i) * L) := by
      calc _ ≤ (C₁ * (M * (v * i))) * (C₀ * (M * a)) := mul_le_mul el1 eZ (norm_nonneg _) (by positivity)
        _ = (C₀ * C₁ * M ^ 2) * (a * i) * v := by ring
        _ ≤ (C₀ * C₁ * M ^ 2) * (a * i) * (2 * L) := by gcongr
        _ = _ := by ring
    have T2 : |fam_lambda S.p ε μ t - L| * ‖deriv Z t‖ ≤
        (2 * C₀ * C₁ * M) * ((a * i) * L * (L * |t - y|)) := by
      calc _ ≤ (C₀ * L * |t - y| * i) * (C₁ * (M * (a * v))) :=
            mul_le_mul hd63 eZ1 (norm_nonneg _) (by positivity)
        _ = (C₀ * C₁ * M) * (a * i) * (L * |t - y|) * v := by ring
        _ ≤ (C₀ * C₁ * M) * (a * i) * (L * |t - y|) * (2 * L) := by gcongr
        _ = _ := by ring
    have T3 : ‖deriv (deriv (c05_standing_A S.p ε μ)) t‖ ≤ (2 * C₂ * M) * ((a * i) * L) := by
      calc _ ≤ C₂ * (M * (a * i * i)) := eA2
        _ = (C₂ * M) * (a * i) * i := by ring
        _ ≤ (C₂ * M) * (a * i) * (2 * L) := by gcongr; linarith
        _ = _ := by ring
    have T4 : |fam_lambda S.p ε μ t| * ‖deriv (c05_standing_A S.p ε μ) t‖ ≤
        (4 * C₁ * M) * ((a * i) * L) := by
      rw [abs_of_nonneg hlt0]
      calc _ ≤ (4 * L) * (C₁ * (M * (a * i))) := mul_le_mul hlt4 eA1 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hP : 0 ≤ (a * i) * L := by positivity
    have hQ : 0 ≤ (a * i) * L * (L * |t - y|) := by positivity
    calc _ ≤ ‖Complex.I * ((deriv (fam_lambda S.p ε μ) t : ℝ) : ℂ) * Z t‖ +
          ‖Complex.I * ((fam_lambda S.p ε μ t - L : ℝ) : ℂ) * deriv Z t‖ +
          ‖deriv (deriv (c05_standing_A S.p ε μ)) t * E‖ +
          ‖Complex.I * ((fam_lambda S.p ε μ t : ℝ) : ℂ) * deriv (c05_standing_A S.p ε μ) t * E‖ :=
          c05_aux_norm4 _ _ _ _
      _ = |deriv (fam_lambda S.p ε μ) t| * ‖Z t‖ + |fam_lambda S.p ε μ t - L| * ‖deriv Z t‖ +
          ‖deriv (deriv (c05_standing_A S.p ε μ)) t‖ +
          |fam_lambda S.p ε μ t| * ‖deriv (c05_standing_A S.p ε μ) t‖ := by
          rw [hnI, hnI, norm_mul, hEn, mul_one, norm_mul, hEn, mul_one, hnI]
      _ ≤ (2 * C₂ * M + 4 * C₁ * M + 2 * C₀ * C₁ * M ^ 2) * ((a * i) * L) +
          (2 * C₀ * C₁ * M) * ((a * i) * L * (L * |t - y|)) := by linarith
      _ ≤ K * ((a * i) * L) + K * ((a * i) * L * (L * |t - y|)) := by
          gcongr
          · exact hKge _ (by positivity) (Or.inr (Or.inr (Or.inl rfl)))
          · exact hKge _ (by positivity) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      _ = _ := by ring
  · calc _ ≤ C₀ * (M * (a * a * a)) := eZ3
      _ = (C₀ * M) * (a * a * a) := by ring
      _ ≤ K * (a * a * a) := by
          gcongr; exact hKge _ (by positivity) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · calc _ ≤ C₁ * (M * (a * a * a * v)) := eZ31
      _ ≤ C₁ * (M * (a * a * a * (2 * L))) := by gcongr
      _ = (2 * C₁ * M) * (a * a * a) * L := by ring
      _ ≤ K * (a * a * a) * L := by
          gcongr
          exact hKge _ (by positivity) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · calc ‖Z t ^ 2 * deriv Z t‖ = ‖Z t‖ ^ 2 * ‖deriv Z t‖ := by rw [norm_mul, norm_pow]
      _ ≤ (C₀ * (M * a)) ^ 2 * (C₁ * (M * (a * v))) := by gcongr
      _ = (C₀ ^ 2 * C₁ * M ^ 3) * (a * a * a) * v := by ring
      _ ≤ (C₀ ^ 2 * C₁ * M ^ 3) * (a * a * a) * (2 * L) := by gcongr
      _ = (2 * C₀ ^ 2 * C₁ * M ^ 3) * (a * a * a) * L := by ring
      _ ≤ K * (a * a * a) * L := by
          gcongr
          exact hKge _ (by positivity)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · calc _ ≤ ‖2 * Z t * deriv Z t * deriv Z t‖ + ‖Z t ^ 2 * deriv (deriv Z) t‖ := norm_add_le _ _
      _ = 2 * ‖Z t‖ * ‖deriv Z t‖ ^ 2 + ‖Z t‖ ^ 2 * ‖deriv (deriv Z) t‖ := by
          simp only [norm_mul, norm_pow, Complex.norm_ofNat]; ring
      _ ≤ 2 * (C₀ * (M * a)) * (C₁ * (M * (a * v))) ^ 2 +
          (C₀ * (M * a)) ^ 2 * (C₂ * (M * (a * v * v))) := by gcongr
      _ = (2 * C₀ * C₁ ^ 2 * M ^ 3 + C₀ ^ 2 * C₂ * M ^ 3) * (a * a * a) * (v * v) := by ring
      _ ≤ (2 * C₀ * C₁ ^ 2 * M ^ 3 + C₀ ^ 2 * C₂ * M ^ 3) * (a * a * a) * ((2 * L) * (2 * L)) := by
          gcongr
      _ = (4 * (2 * C₀ * C₁ ^ 2 * M ^ 3 + C₀ ^ 2 * C₂ * M ^ 3)) * (a * a * a) * L ^ 2 := by ring
      _ ≤ K * (a * a * a) * L ^ 2 := by
          gcongr
          exact hKge _ (by positivity)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

/-- Blueprint: lem:c05_frozen_frequency.  For `y ∈ [Y,2Y]`, `λ = λ(y)`, `w = Z' - iλZ`,
`|s| ≤ Y/4`: (1) `Z(y)e^{-iλs} - Z(y-s) = ∫_{y-s}^y e^{-iλ(t-y+s)} w(t) dt`; (2) bounds on `w, w'`
between `y-s` and `y`; (3) the plane-wave comparison bounds; (4) increment bounds for `Z³`, `Z²Z'`. -/
theorem c05_frozen_frequency (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y),
          let lam := fam_lambda S.p ε μ y
          let Z := fam_Z S.p R ε μ
          let w : ℝ → ℂ := fun t => deriv Z t - Complex.I * (lam : ℂ) * Z t
          ∀ s : ℝ, |s| ≤ Y / 4 →
            -- (1)
            Z y * Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) - Z (y - s) =
              (∫ t in (y - s)..y,
                Complex.exp (-(Complex.I * ((lam * (t - y + s) : ℝ) : ℂ))) * w t) ∧
            -- (2)
            (∀ t ∈ uIcc (y - s) y,
              ‖w t‖ ≤ C * Y ^ (-beta S.p - 1) * (1 + lam * |t - y|) ∧
              ‖deriv w t‖ ≤ C * Y ^ (-beta S.p - 1) * lam * (1 + lam * |t - y|)) ∧
            -- (3)
            ‖Z y * Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) - Z (y - s)‖ ≤
              C * Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2) ∧
            ‖w y - w (y - s)‖ ≤ C * Y ^ (-beta S.p - 1) * lam * (|s| + lam * s ^ 2) ∧
            -- (4)
            ‖Z y ^ 3 - Z (y - s) ^ 3‖ ≤ C * Y ^ (-3 * beta S.p) * min 1 (lam * |s|) ∧
            ‖Z y ^ 2 * deriv Z y - Z (y - s) ^ 2 * deriv Z (y - s)‖ ≤
              C * Y ^ (-3 * beta S.p) * lam * min 1 (lam * |s|) := by
  obtain ⟨Rd, hRd, K, hK, hdat⟩ := c05_aux_ff_data S
  refine ⟨Rd, hRd, 2 * K, by positivity, ?_⟩
  intro ε μ R Y ht y hy lam Z w s hs
  have hR : 1 ≤ R := hRd.trans ht.2.2.2.1
  have hY0 : 0 < Y := by linarith [ht.2.2.2.2]
  have hD := hdat ε μ R Y ht y hy
  have hseg : ∀ t ∈ uIcc (y - s) y, |t - y| ≤ |s| := by
    intro t ht'
    rw [mem_uIcc] at ht'
    have h1 := neg_abs_le s
    have h2 := le_abs_self s
    rw [abs_le]
    rcases ht' with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> linarith
  have hsY : ∀ t ∈ uIcc (y - s) y, |t - y| ≤ Y / 4 := fun t ht' => (hseg t ht').trans hs
  have hlam0 : 0 ≤ lam := (hD y (by simp; positivity)).1
  have hab : |s| ≤ Y / 4 := hs
  have hYb : 0 ≤ Y ^ (-beta S.p - 1) := (Real.rpow_pos_of_pos hY0 _).le
  have hY3 : 0 ≤ Y ^ (-3 * beta S.p) := (Real.rpow_pos_of_pos hY0 _).le
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hD' : ∀ t ∈ uIcc (y - s) y, _ := fun t ht' => hD t (hsY t ht')
  -- derivative of `w`
  have hwd : ∀ t ∈ uIcc (y - s) y, HasDerivAt w
      (deriv (deriv Z) t - Complex.I * (lam : ℂ) * deriv Z t) t := by
    intro t ht'
    obtain ⟨-, hZd, hZ'd, -⟩ := hD' t ht'
    exact hZ'd.sub (hZd.const_mul _)
  -- (2)
  have h2 : ∀ t ∈ uIcc (y - s) y,
      ‖w t‖ ≤ 2 * K * Y ^ (-beta S.p - 1) * (1 + lam * |t - y|) ∧
      ‖deriv w t‖ ≤ 2 * K * Y ^ (-beta S.p - 1) * lam * (1 + lam * |t - y|) := by
    intro t ht'
    obtain ⟨-, -, -, hw, hw', -⟩ := hD' t ht'
    have hP : 0 ≤ Y ^ (-beta S.p - 1) * (1 + lam * |t - y|) := by positivity
    refine ⟨hw.trans (by nlinarith), ?_⟩
    rw [(hwd t ht').deriv]
    have hP' : 0 ≤ Y ^ (-beta S.p - 1) * lam * (1 + lam * |t - y|) := by positivity
    exact hw'.trans (by nlinarith)
  -- uniform bounds on the segment
  have hwB : ∀ t ∈ uIcc (y - s) y, ‖w t‖ ≤ 2 * K * Y ^ (-beta S.p - 1) * (1 + lam * |s|) := by
    intro t ht'
    refine (h2 t ht').1.trans (mul_le_mul_of_nonneg_left
      (by linarith [mul_le_mul_of_nonneg_left (hseg t ht') hlam0]) (by positivity))
  have hw'B : ∀ t ∈ uIcc (y - s) y,
      ‖deriv (deriv Z) t - Complex.I * (lam : ℂ) * deriv Z t‖ ≤
        2 * K * Y ^ (-beta S.p - 1) * lam * (1 + lam * |s|) := by
    intro t ht'
    have := (h2 t ht').2
    rw [(hwd t ht').deriv] at this
    refine this.trans (mul_le_mul_of_nonneg_left
      (by linarith [mul_le_mul_of_nonneg_left (hseg t ht') hlam0]) (by positivity))
  have hy_mem : y ∈ uIcc (y - s) y := right_mem_uIcc
  have hys_mem : y - s ∈ uIcc (y - s) y := left_mem_uIcc
  -- (1)
  have h1 : Z y * Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) - Z (y - s) =
      ∫ t in (y - s)..y, Complex.exp (-(Complex.I * ((lam * (t - y + s) : ℝ) : ℂ))) * w t := by
    have hder : ∀ t ∈ uIcc (y - s) y, HasDerivAt
        (fun u => Z u * Complex.exp (-(Complex.I * ((lam * (u - y + s) : ℝ) : ℂ))))
        (Complex.exp (-(Complex.I * ((lam * (t - y + s) : ℝ) : ℂ))) * w t) t := by
      intro t ht'
      obtain ⟨-, hZd, -⟩ := hD' t ht'
      have hlin : HasDerivAt (fun u : ℝ => lam * (u - y + s)) lam t := by
        simpa using (((hasDerivAt_id t).sub_const y).add_const s).const_mul lam
      have he := ((hlin.ofReal_comp.const_mul Complex.I).neg).cexp
      convert hZd.mul he using 1
      simp only [Pi.neg_apply]
      show _ * (deriv Z t - Complex.I * (lam : ℂ) * Z t) = _
      ring
    have hcont : ContinuousOn (fun t => Complex.exp (-(Complex.I * ((lam * (t - y + s) : ℝ) : ℂ))) * w t)
        (uIcc (y - s) y) := by
      intro t ht'
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul ?_ (hwd t ht').continuousAt
      exact (Complex.continuous_exp.comp (by fun_prop)).continuousAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable)]
    rw [show y - y + s = s by ring, show y - s - y + s = 0 by ring]
    simp
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · rw [h1]
    calc _ ≤ (2 * K * Y ^ (-beta S.p - 1) * (1 + lam * |s|)) * |y - (y - s)| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht' => ?_
          have ht'' : t ∈ uIcc (y - s) y := uIoc_subset_uIcc ht'
          rw [norm_mul, show -(Complex.I * ((lam * (t - y + s) : ℝ) : ℂ)) =
            ((-(lam * (t - y + s)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, one_mul]
          exact hwB t ht''
      _ = _ := by rw [show y - (y - s) = s by ring, ← sq_abs s]; ring
  · have := (convex_uIcc (y - s) y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht' => (hwd t ht').hasDerivWithinAt) hw'B hys_mem hy_mem
    rw [Real.norm_eq_abs, show y - (y - s) = s by ring] at this
    refine this.trans (le_of_eq ?_)
    rw [← sq_abs s]; ring
  · have hd : ∀ t ∈ uIcc (y - s) y, HasDerivWithinAt (fun u => Z u ^ 3)
        (deriv (fun u => Z u ^ 3) t) (uIcc (y - s) y) t :=
      fun t ht' => (hD' t ht').2.2.2.2.2.2.2.1.hasDerivWithinAt
    have hb : ∀ t ∈ uIcc (y - s) y, ‖deriv (fun u => Z u ^ 3) t‖ ≤ K * Y ^ (-3 * beta S.p) * lam :=
      fun t ht' => (hD' t ht').2.2.2.2.2.2.1
    have hm := (convex_uIcc (y - s) y).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hys_mem hy_mem
    rw [Real.norm_eq_abs, show y - (y - s) = s by ring] at hm
    have hs1 := (hD' y hy_mem).2.2.2.2.2.1
    have hs2 := (hD' (y - s) hys_mem).2.2.2.2.2.1
    rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
    refine le_min ?_ ?_
    · calc _ ≤ ‖Z y ^ 3‖ + ‖Z (y - s) ^ 3‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    · calc _ ≤ K * Y ^ (-3 * beta S.p) * lam * |s| := hm
        _ ≤ _ := by
          have : 0 ≤ K * Y ^ (-3 * beta S.p) * (lam * |s|) := by positivity
          nlinarith
  · have hd : ∀ t ∈ uIcc (y - s) y, HasDerivWithinAt (fun u => Z u ^ 2 * deriv Z u)
        (2 * Z t * deriv Z t * deriv Z t + Z t ^ 2 * deriv (deriv Z) t) (uIcc (y - s) y) t := by
      intro t ht'
      obtain ⟨-, hZd, hZ'd, -⟩ := hD' t ht'
      have := (hZd.pow 2).mul hZ'd
      refine HasDerivAt.hasDerivWithinAt ?_
      convert this using 1
      simp only [Pi.pow_apply]; push_cast; ring
    have hb : ∀ t ∈ uIcc (y - s) y,
        ‖2 * Z t * deriv Z t * deriv Z t + Z t ^ 2 * deriv (deriv Z) t‖ ≤
          K * Y ^ (-3 * beta S.p) * lam ^ 2 :=
      fun t ht' => (hD' t ht').2.2.2.2.2.2.2.2.2
    have hm := (convex_uIcc (y - s) y).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hys_mem hy_mem
    rw [Real.norm_eq_abs, show y - (y - s) = s by ring] at hm
    have hs1 := (hD' y hy_mem).2.2.2.2.2.2.2.2.1
    have hs2 := (hD' (y - s) hys_mem).2.2.2.2.2.2.2.2.1
    rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
    refine le_min ?_ ?_
    · calc _ ≤ ‖Z y ^ 2 * deriv Z y‖ + ‖Z (y - s) ^ 2 * deriv Z (y - s)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    · calc _ ≤ K * Y ^ (-3 * beta S.p) * lam ^ 2 * |s| := hm
        _ ≤ _ := by
          have : 0 ≤ K * Y ^ (-3 * beta S.p) * lam * (lam * |s|) := by positivity
          nlinarith

/-- Helper for lem:c05_plane_wave_comparison. -/
theorem c05_aux_P_derivs (Zy : ℂ) (L y : ℝ) (hL : L ≠ 0) :
    let e : ℝ → ℂ := fun z => Complex.exp (Complex.I * ((L * (z - y) : ℝ) : ℂ))
    (∀ z, HasDerivAt e (Complex.I * (L : ℂ) * e z) z) ∧
    deriv (fun z => 2 * (Zy / (Complex.I * (L : ℂ)) * e z).re) = (fun z => 2 * (Zy * e z).re) ∧
    deriv (fun z => 2 * (Zy * e z).re) = (fun z => 2 * (Complex.I * (L : ℂ) * Zy * e z).re) ∧
    Differentiable ℝ (fun z => 2 * (Zy / (Complex.I * (L : ℂ)) * e z).re) ∧
    Differentiable ℝ (fun z => 2 * (Zy * e z).re) := by
  intro e
  have he : ∀ z, HasDerivAt e (Complex.I * (L : ℂ) * e z) z := by
    intro z
    have h1 : HasDerivAt (fun z : ℝ => L * (z - y)) L z := by
      simpa using ((hasDerivAt_id z).sub_const y).const_mul L
    have := (h1.ofReal_comp.const_mul Complex.I).cexp
    convert this using 1; simp only [e]; ring
  have hIL : Complex.I * (L : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hL)
  have d1 : ∀ z, HasDerivAt (fun z => 2 * (Zy / (Complex.I * (L : ℂ)) * e z).re)
      (2 * (Zy * e z).re) z := by
    intro z
    have := (c05_aux_hasDerivAt_re ((he z).const_mul (Zy / (Complex.I * (L : ℂ))))).const_mul 2
    convert this using 2
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    field_simp
  have d2 : ∀ z, HasDerivAt (fun z => 2 * (Zy * e z).re) (2 * (Complex.I * (L : ℂ) * Zy * e z).re) z := by
    intro z
    have := (c05_aux_hasDerivAt_re ((he z).const_mul Zy)).const_mul 2
    convert this using 2; ring
  exact ⟨he, funext fun z => (d1 z).deriv, funext fun z => (d2 z).deriv,
    fun z => (d1 z).differentiableAt, fun z => (d2 z).differentiableAt⟩


/-- Helper for lem:c05_plane_wave_comparison: `∫_{y-s}^y [Z(t) - Z(y)e^{iλ(t-y)}] dt`. -/
theorem c05_aux_pw_I1 {Z : ℝ → ℂ} {L y s B : ℝ} (hL : 0 < L) (hB : 0 ≤ B)
    (hZd : ∀ t ∈ uIcc (y - s) y, HasDerivAt Z (deriv Z t) t)
    (hZc : ContinuousOn Z (uIcc (y - s) y)) (hZ'c : ContinuousOn (deriv Z) (uIcc (y - s) y))
    (F1 : Z y * Complex.exp (-(Complex.I * ((L * s : ℝ) : ℂ))) - Z (y - s) =
      ∫ t in (y - s)..y, Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ))) *
        (deriv Z t - Complex.I * (L : ℂ) * Z t))
    (hw : ∀ t ∈ uIcc (y - s) y, ‖deriv Z t - Complex.I * (L : ℂ) * Z t‖ ≤ B * (1 + L * |s|)) :
    ‖∫ t in (y - s)..y, (Z t - Z y * Complex.exp (Complex.I * ((L * (t - y) : ℝ) : ℂ)))‖ ≤
      4 * B * s ^ 2 := by
  set e : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((L * (t - y) : ℝ) : ℂ)) with hedef
  set w : ℝ → ℂ := fun t => deriv Z t - Complex.I * (L : ℂ) * Z t with hw'
  have hec : Continuous e := by simp only [hedef]; fun_prop
  have he : ∀ t, HasDerivAt e (Complex.I * (L : ℂ) * e t) t := (c05_aux_P_derivs 0 L y hL.ne').1
  have hwc : ContinuousOn w (uIcc (y - s) y) := hZ'c.sub (continuousOn_const.mul hZc)
  have hZi : IntervalIntegrable Z volume (y - s) y := hZc.intervalIntegrable
  have hei : IntervalIntegrable e volume (y - s) y := hec.intervalIntegrable _ _
  have hwi : IntervalIntegrable w volume (y - s) y := hwc.intervalIntegrable
  have hZftc : ∫ t in (y - s)..y, deriv Z t = Z y - Z (y - s) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hZd (hZ'c.intervalIntegrable)
  have heftc : ∫ t in (y - s)..y, Complex.I * (L : ℂ) * e t = e y - e (y - s) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => he t)
      ((continuous_const.mul hec).intervalIntegrable _ _)
  have hdecomp : ∫ t in (y - s)..y, deriv Z t =
      (∫ t in (y - s)..y, w t) + Complex.I * (L : ℂ) * ∫ t in (y - s)..y, Z t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hwi (hZi.const_mul _)]
    congr 1; funext t; simp only [hw']; ring
  have he'c : Continuous (fun t : ℝ => Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ)))) := by
    fun_prop
  have he'i : IntervalIntegrable
      (fun t => Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ))) * w t) volume (y - s) y :=
    (he'c.continuousOn.mul hwc).intervalIntegrable
  have hey : e y = 1 := by simp [hedef]
  have hea : e (y - s) = Complex.exp (-(Complex.I * ((L * s : ℝ) : ℂ))) := by
    simp only [hedef]; congr 1; push_cast; ring
  have h2 : ∫ t in (y - s)..y, Complex.I * (L : ℂ) * e t =
      Complex.I * (L : ℂ) * ∫ t in (y - s)..y, e t := intervalIntegral.integral_const_mul _ _
  have hI1 : ∫ t in (y - s)..y, (Z t - Z y * e t) =
      (∫ t in (y - s)..y, Z t) - Z y * ∫ t in (y - s)..y, e t := by
    rw [intervalIntegral.integral_sub hZi (hei.const_mul _), intervalIntegral.integral_const_mul]
  have h3 : ∫ t in (y - s)..y,
      (Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ))) - 1) * w t =
      (∫ t in (y - s)..y, Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ))) * w t) -
        ∫ t in (y - s)..y, w t := by
    rw [← intervalIntegral.integral_sub he'i hwi]; congr 1; funext t; ring
  have hkey : Complex.I * (L : ℂ) * ∫ t in (y - s)..y, (Z t - Z y * e t) = ∫ t in (y - s)..y,
      (Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ))) - 1) * w t := by
    rw [h3, ← F1, hI1, ← hea]
    rw [heftc, hey] at h2
    rw [hZftc] at hdecomp
    linear_combination (-1 : ℂ) * hdecomp + Z y * h2
  -- the bound
  have hILn : ‖Complex.I * (L : ℂ)‖ = L := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  have hpt : ∀ t ∈ Set.uIoc (y - s) y,
      ‖(Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ))) - 1) * w t‖ ≤
        min (L * |s|) 2 * (B * (1 + L * |s|)) := by
    intro t ht'
    have htI := uIoc_subset_uIcc ht'
    have hts : |t - y + s| ≤ |s| := by
      rw [mem_uIcc] at htI
      have h1 := neg_abs_le s
      have h2 := le_abs_self s
      rcases htI with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [norm_mul]
    refine mul_le_mul (le_min ?_ ?_) (hw t htI) (norm_nonneg _) (by positivity)
    · have := norm_exp_I_mul_ofReal_sub_one_le (x := -(L * (t - y + s)))
      rw [show Complex.I * ((-(L * (t - y + s)) : ℝ) : ℂ) = -(Complex.I * ((L * (t - y + s) : ℝ) : ℂ))
        by push_cast; ring, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hL] at this
      exact this.trans (by gcongr)
    · calc _ ≤ ‖Complex.exp (-(Complex.I * ((L * (t - y + s) : ℝ) : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          rw [show -(Complex.I * ((L * (t - y + s) : ℝ) : ℂ)) = ((-(L * (t - y + s)) : ℝ) : ℂ) * Complex.I
            by push_cast; ring, Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [show y - (y - s) = s by ring] at hbd
  have hnorm : ‖∫ t in (y - s)..y, (Z t - Z y * e t)‖ * L ≤
      min (L * |s|) 2 * (B * (1 + L * |s|)) * |s| := by
    have : ‖∫ t in (y - s)..y, (Z t - Z y * e t)‖ * L =
        ‖Complex.I * (L : ℂ) * ∫ t in (y - s)..y, (Z t - Z y * e t)‖ := by
      rw [norm_mul, hILn, mul_comm]
    rw [this, hkey]; exact hbd
  have hs0 := abs_nonneg s
  have hsq : s ^ 2 = |s| * |s| := by rw [← sq_abs]; ring
  rw [hsq]
  rcases le_or_gt (L * |s|) 1 with h | h
  · have hm : min (L * |s|) 2 ≤ L * |s| := min_le_left _ _
    have : ‖∫ t in (y - s)..y, (Z t - Z y * e t)‖ * L ≤ L * (B * (1 + L * |s|) * |s| * |s|) := by
      refine hnorm.trans ?_
      calc _ ≤ (L * |s|) * (B * (1 + L * |s|)) * |s| := by gcongr
        _ = _ := by ring
    have h' := le_of_mul_le_mul_left (by linarith [mul_comm L ‖∫ t in (y - s)..y, (Z t - Z y * e t)‖]
      : L * ‖∫ t in (y - s)..y, (Z t - Z y * e t)‖ ≤ L * (B * (1 + L * |s|) * |s| * |s|)) hL
    refine h'.trans ?_
    have : B * (1 + L * |s|) ≤ B * 2 := by gcongr; linarith
    nlinarith [mul_nonneg hs0 hs0]
  · have hm : min (L * |s|) 2 ≤ 2 := min_le_right _ _
    have : ‖∫ t in (y - s)..y, (Z t - Z y * e t)‖ * L ≤ L * (4 * B * (|s| * |s|)) := by
      refine hnorm.trans ?_
      calc _ ≤ 2 * (B * (1 + L * |s|)) * |s| := by gcongr
        _ = 2 * B * |s| + 2 * B * (L * |s|) * |s| := by ring
        _ ≤ 2 * B * |s| * (L * |s|) + 2 * B * (L * |s|) * |s| := by
            have : 0 ≤ 2 * B * |s| := by positivity
            nlinarith
        _ = L * (4 * B * (|s| * |s|)) := by ring
    exact le_of_mul_le_mul_left (by linarith [mul_comm L ‖∫ t in (y - s)..y, (Z t - Z y * e t)‖]) hL

/-- Helper for lem:c05_plane_wave_comparison. -/
theorem c05_aux_fin2 {A X1 X2 K C : ℝ} (hX1 : 0 ≤ X1) (hX2 : 0 ≤ X2) (h1 : 2 * A ≤ C)
    (h2 : 2 * K ≤ C) : 2 * (A * X1 + K * X2) ≤ C * (X1 + X2) := by
  have := mul_le_mul_of_nonneg_right h1 hX1
  have := mul_le_mul_of_nonneg_right h2 hX2
  nlinarith


/-- Helper for lem:c05_plane_wave_comparison: FTC splitting of `Δv - ΔP` (generic). -/
theorem c05_aux_pw_ftc {v P : ℝ → ℝ} {Z e : ℝ → ℂ} {c Zy : ℂ} {a b : ℝ}
    (hvd : Differentiable ℝ v) (hvc : Continuous (deriv v)) (hPd : Differentiable ℝ P)
    (hPc : Continuous (deriv P))
    (hform : ∀ t ∈ uIcc a b, deriv v t - deriv P t = 2 * (Z t - Zy * e t + c * Z t ^ 3).re)
    (hZc : ContinuousOn Z (uIcc a b)) (hec : Continuous e) :
    (v b - v a) - (P b - P a) =
      2 * ((∫ t in a..b, (Z t - Zy * e t)) + c * ∫ t in a..b, Z t ^ 3).re := by
  have hD : (v b - v a) - (P b - P a) = ∫ t in a..b, (deriv v t - deriv P t) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => v t - P t)
      (fun t _ => ((hvd t).hasDerivAt.sub (hPd t).hasDerivAt))
      ((hvc.sub hPc).intervalIntegrable _ _)]
    ring
  have hGc : ContinuousOn (fun t => Z t - Zy * e t + c * Z t ^ 3) (uIcc a b) :=
    (hZc.sub (continuousOn_const.mul hec.continuousOn)).add (continuousOn_const.mul (hZc.pow 3))
  rw [hD, intervalIntegral.integral_congr hform, intervalIntegral.integral_const_mul]
  have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (μ := volume) hGc.intervalIntegrable
  simp only [RCLike.re_to_complex] at this
  rw [this]
  congr 2
  have hZi : IntervalIntegrable Z volume a b := hZc.intervalIntegrable
  have hA : IntervalIntegrable (fun t => Z t - Zy * e t) volume a b :=
    hZi.sub ((hec.intervalIntegrable _ _).const_mul _)
  have hB : IntervalIntegrable (fun t => c * Z t ^ 3) volume a b :=
    (hZc.pow 3).intervalIntegrable.const_mul _
  rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul]

/-- Helper for lem:c05_plane_wave_comparison: `‖∫_{y-s}^y Z³‖ ≤ K Y^{-3β} min(|s|, λ⁻¹)`
(from symbol bounds (3) and `c05_primitive`). -/
theorem c05_aux_pw_cubic (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ s : ℝ, |s| ≤ Y / 4 →
          ‖∫ t in (y - s)..y, fam_Z S.p R ε μ t ^ 3‖ ≤
            K * Y ^ (-3 * beta S.p) * min |s| (fam_lambda S.p ε μ y)⁻¹ := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hip2 : 1 / S.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  have hβ2 : beta S.p ≤ 4 / 3 := by
    unfold beta; rw [div_le_iff₀ (by positivity)]; linarith
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  set M : ℝ := (4 : ℝ) ^ (6 : ℝ) with hM
  have hM1 : 1 ≤ M := Real.one_le_rpow (by norm_num) (by norm_num)
  refine ⟨max Rp Rs, hRp.trans (le_max_left _ _), C₀ * M + 16 * Cp * M, by positivity, ?_⟩
  intro ε μ R Y ht y hy s hs
  have htp := c05_aux_tuple_mono (le_max_left Rp Rs) ht
  have hts := c05_aux_tuple_mono (le_max_right Rp Rs) ht
  set lam := fam_lambda S.p ε μ y with hlamdef
  set Z := fam_Z S.p R ε μ with hZ
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hs' := abs_le.mp hs
  have hy1 := hy.1
  have hy2 := hy.2
  have hy0 : 0 < y := by linarith
  obtain ⟨⟨hl1, hl2, -⟩, -⟩ := hs0 ε μ R Y hts y (by linarith)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hl1
  have hX3 : 0 ≤ Y ^ (-3 * beta S.p) := (Real.rpow_pos_of_pos hY0 _).le
  have hseg : ∀ t ∈ uIcc (y - s) y, R < t ∧ t ∈ Ioo (Y / 4) (4 * Y) := by
    intro t ht'
    rw [mem_uIcc] at ht'
    rcases ht' with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;>
      exact ⟨by linarith, ⟨by linarith, by linarith⟩⟩
  have hZ3pt : ∀ t ∈ uIcc (y - s) y, ‖Z t ^ 3‖ ≤ C₀ * M * Y ^ (-3 * beta S.p) := by
    intro t ht'
    obtain ⟨-, -, ⟨-, h3, -⟩, -⟩ := hs0 ε μ R Y hts t (hseg t ht').1.le
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at h3
    refine h3.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (c05_aux_tY hY0 (hseg t ht').2
      (abs_le.mpr ⟨by linarith, by linarith⟩)) hC₀.le
  have hI3a : ‖∫ t in (y - s)..y, Z t ^ 3‖ ≤ C₀ * M * Y ^ (-3 * beta S.p) * |s| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y - s) (b := y)
      (f := fun t => Z t ^ 3) (C := C₀ * M * Y ^ (-3 * beta S.p))
      (fun t ht' => hZ3pt t (uIoc_subset_uIcc ht'))
    rwa [show y - (y - s) = s by ring] at this
  have hlamY : lam ≤ 8 * Y ^ (1 / S.p) := by
    refine hl2.trans ?_
    have : y ^ (1 / S.p) ≤ (2 * Y) ^ (1 / S.p) := Real.rpow_le_rpow hy0.le hy2 hip.le
    rw [Real.mul_rpow (by norm_num) hY0.le] at this
    have h2 : (2 : ℝ) ^ (1 / S.p) ≤ 4 := by
      calc (2 : ℝ) ^ (1 / S.p) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hip2
        _ = 4 := by norm_num
    nlinarith [Real.rpow_pos_of_pos hY0 (1 / S.p)]
  have hI3b : ‖∫ t in (y - s)..y, Z t ^ 3‖ ≤ 16 * Cp * M * Y ^ (-3 * beta S.p) * lam⁻¹ := by
    obtain ⟨⟨-, hi1, -, -, -, -, -, hb1⟩, -⟩ := hprim ε μ R Y htp (y - s) (by linarith)
    obtain ⟨⟨-, hi2, -, -, -, -, -, hb2⟩, -⟩ := hprim ε μ R Y htp y (by linarith)
    have hdiff := intervalIntegral.integral_Ioi_sub_Ioi' hi1 hi2
    rw [← hdiff]
    have hYp : Y ^ (-3 * beta S.p - 1 / S.p) = Y ^ (-3 * beta S.p) * (Y ^ (1 / S.p))⁻¹ := by
      rw [← Real.rpow_neg hY0.le, ← Real.rpow_add hY0]; ring_nf
    have hb : ∀ z ∈ Ioo (Y / 4) (4 * Y), Cp * z ^ (-3 * beta S.p - 1 / S.p) ≤
        Cp * M * (Y ^ (-3 * beta S.p) * (Y ^ (1 / S.p))⁻¹) := by
      intro z hz
      rw [mul_assoc, ← hYp]
      exact mul_le_mul_of_nonneg_left (c05_aux_tY hY0 hz (abs_le.mpr ⟨by linarith, by linarith⟩)) hCp.le
    have hinv : (Y ^ (1 / S.p))⁻¹ ≤ 8 * lam⁻¹ := by
      rw [show 8 * lam⁻¹ = (lam / 8)⁻¹ by field_simp]
      exact inv_anti₀ (by positivity) (by linarith)
    have hX : 0 ≤ Cp * M * Y ^ (-3 * beta S.p) := by positivity
    calc _ ≤ ‖∫ t in Ioi (y - s), Z t ^ 3‖ + ‖∫ t in Ioi y, Z t ^ 3‖ := norm_sub_le _ _
      _ ≤ 2 * (Cp * M * (Y ^ (-3 * beta S.p) * (Y ^ (1 / S.p))⁻¹)) := by
          have := hb (y - s) ⟨by linarith, by linarith⟩
          have := hb y ⟨by linarith, by linarith⟩
          linarith
      _ ≤ 2 * (Cp * M * (Y ^ (-3 * beta S.p) * (8 * lam⁻¹))) := by gcongr
      _ = _ := by ring
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min (hI3a.trans ?_) (hI3b.trans ?_)
  · have : C₀ * M * Y ^ (-3 * beta S.p) ≤ (C₀ * M + 16 * Cp * M) * Y ^ (-3 * beta S.p) := by
      have := mul_nonneg (mul_nonneg hCp.le (by linarith : (0:ℝ) ≤ M)) hX3; nlinarith
    gcongr
  · have : 16 * Cp * M * Y ^ (-3 * beta S.p) ≤ (C₀ * M + 16 * Cp * M) * Y ^ (-3 * beta S.p) := by
      have := mul_nonneg (mul_nonneg hC₀.le (by linarith : (0:ℝ) ≤ M)) hX3; nlinarith
    gcongr

/-- Helper for lem:c05_plane_wave_comparison: `Z` is `C¹` on segments in `(R,∞)`. -/
theorem c05_aux_pw_Zreg (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      ∀ a b : ℝ, R < a → R < b →
        (∀ t ∈ uIcc a b, HasDerivAt (fam_Z S.p R ε μ) (deriv (fam_Z S.p R ε μ) t) t) ∧
        ContinuousOn (fam_Z S.p R ε μ) (uIcc a b) ∧
        ContinuousOn (deriv (fam_Z S.p R ε μ)) (uIcc a b) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  refine ⟨Rs, hRs, ?_⟩
  intro ε μ R Y hts a b ha hb
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have := (hs0 ε μ R Y hts t ht'.le).1.1
    have : 0 < t ^ (1 / S.p) / 2 := by
      have : 0 < t := by linarith
      positivity
    linarith
  have hZon : ContDiffOn ℝ (⊤ : ℕ∞) (fam_Z S.p R ε μ) (Ioi R) := fun t ht' =>
    (c05_aux_Z_smooth S.p R ε μ hp hp1 (by linarith) (by linarith [show R < t from ht'])
      (hpos t ht').ne').contDiffWithinAt
  have hZ'on := hZon.deriv_of_isOpen isOpen_Ioi (m := (⊤ : ℕ∞)) (by simp)
  have hsub : uIcc a b ⊆ Ioi R := by
    intro t ht'
    rw [mem_uIcc] at ht'
    show R < t
    rcases ht' with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> linarith
  refine ⟨fun t ht' => ?_, hZon.continuousOn.mono hsub, hZ'on.continuousOn.mono hsub⟩
  exact ((hZon.contDiffAt (Ioi_mem_nhds (hsub ht'))).differentiableAt (by simp)).hasDerivAt

/-- Helper for lem:c05_plane_wave_comparison: the fundamental part
`‖∫_{y-s}^y [Z(t) - Z(y)e^{iλ(t-y)}] dt‖ ≤ C Y^{-β-1} s²`. -/
theorem c05_aux_pw_fund (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ s : ℝ, |s| ≤ Y / 4 →
          ‖∫ t in (y - s)..y, (fam_Z S.p R ε μ t - fam_Z S.p R ε μ y *
              Complex.exp (Complex.I * ((fam_lambda S.p ε μ y * (t - y) : ℝ) : ℂ)))‖ ≤
            C * Y ^ (-beta S.p - 1) * s ^ 2 := by
  obtain ⟨Rf, hRf, Cf, hCf, hff⟩ := c05_frozen_frequency S
  obtain ⟨Rz, hRz, hzr⟩ := c05_aux_pw_Zreg S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  refine ⟨max (max Rf Rz) Rs, hRf.trans (by simp), 4 * Cf, by positivity, ?_⟩
  intro ε μ R Y ht y hy s hs
  have htf := c05_aux_tuple_mono (show Rf ≤ max (max Rf Rz) Rs by simp) ht
  have htz := c05_aux_tuple_mono (show Rz ≤ max (max Rf Rz) Rs by simp) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ max (max Rf Rz) Rs by simp) ht
  have hR : 1 ≤ R := hRf.trans htf.2.2.2.1
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hs' := abs_le.mp hs
  have hy1 := hy.1
  have hy2 := hy.2
  have hy0 : 0 < y := by linarith
  obtain ⟨⟨hl1, -⟩, -⟩ := hs0 ε μ R Y hts y (by linarith)
  have hlam0 : 0 < fam_lambda S.p ε μ y := lt_of_lt_of_le (by positivity) hl1
  obtain ⟨hZd, hZc, hZ'c⟩ := hzr ε μ R Y htz (y - s) y (by linarith) (by linarith)
  have hF := hff ε μ R Y htf y hy s hs
  dsimp only at hF
  obtain ⟨F1, F2, -⟩ := hF
  have hX : 0 ≤ Cf * Y ^ (-beta S.p - 1) := by positivity
  have h := c05_aux_pw_I1 hlam0 hX hZd hZc hZ'c F1 (fun t ht' => by
    refine (F2 t ht').1.trans (mul_le_mul_of_nonneg_left ?_ hX)
    have : |t - y| ≤ |s| := by
      rw [mem_uIcc] at ht'
      have h1 := neg_abs_le s
      have h2 := le_abs_self s
      rcases ht' with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
    have := mul_le_mul_of_nonneg_left this hlam0.le
    linarith)
  calc _ ≤ 4 * (Cf * Y ^ (-beta S.p - 1)) * s ^ 2 := h
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Helper for lem:c05_plane_wave_comparison: the value comparison
`|Δv_Y - ΔP_y| ≤ C[Y^{-β-1}s² + εY^{-3β}min(|s|,λ⁻¹)]` (first estimate of
eqn:approx_vY_plane_wave_comparison). Route: FTC for `v_Y - P_y` on `[y-s,y]` (`c05_aux_pw_ftc`),
`c05_aux_pw_fund` for the fundamental part, `c05_aux_pw_cubic` for `∫Z³`. -/
theorem c05_aux_pw_value (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ s : ℝ, |s| ≤ Y / 4 →
          |c05_plane_wave_Delta (res_vY S.p R ε μ Y) y s -
              c05_plane_wave_Delta (c05_plane_wave S.p R ε μ y) y s| ≤
            C * (Y ^ (-beta S.p - 1) * s ^ 2 +
              ε * Y ^ (-3 * beta S.p) * min |s| (fam_lambda S.p ε μ y)⁻¹) := by
  obtain ⟨Rv, hRv, Cv, hCv, hvb⟩ := c05_vY_bounds S
  obtain ⟨Rsm, hRsm, hvsm⟩ := c05_aux_vY_smooth S
  obtain ⟨Rz, hRz, hzr⟩ := c05_aux_pw_Zreg S
  obtain ⟨Rf, hRf, Cf, hCf, hfund⟩ := c05_aux_pw_fund S
  obtain ⟨Rc, hRc, K, hK, hcub⟩ := c05_aux_pw_cubic S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  obtain ⟨Cc, hCc, hsc⟩ := c05_small_constants S
  set R₁ := max (max (max Rv Rsm) (max Rz Rf)) (max Rc Rs) with hR₁
  refine ⟨R₁, hRv.trans (by simp [hR₁]), 2 * Cf + 2 * Cc * K + 1, by positivity, ?_⟩
  intro ε μ R Y ht y hy s hs
  have htv := c05_aux_tuple_mono (show Rv ≤ R₁ by simp [hR₁]) ht
  have htsm := c05_aux_tuple_mono (show Rsm ≤ R₁ by simp [hR₁]) ht
  have htz := c05_aux_tuple_mono (show Rz ≤ R₁ by simp [hR₁]) ht
  have htf := c05_aux_tuple_mono (show Rf ≤ R₁ by simp [hR₁]) ht
  have htc := c05_aux_tuple_mono (show Rc ≤ R₁ by simp [hR₁]) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ R₁ by simp [hR₁]) ht
  have hR : 1 ≤ R := hRv.trans htv.2.2.2.1
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY0 : 0 < Y := by linarith
  have hs' := abs_le.mp hs
  have hy1 := hy.1
  have hy2 := hy.2
  have hy0 : 0 < y := by linarith
  have hε0 : 0 ≤ ε := ht.1
  have hεC : |c_cubic S.p ε| ≤ Cc * ε := by
    have := hsc ε μ ht.1 ht.2.1 ht.2.2.1
    have := abs_nonneg (c_eps S.p ε); have := abs_nonneg (n_eps S.p ε)
    have := abs_nonneg (c_log S.p ε μ); linarith
  obtain ⟨⟨hl1, -⟩, -⟩ := hs0 ε μ R Y hts y (by linarith)
  have hlam0 : 0 < fam_lambda S.p ε μ y := lt_of_lt_of_le (by positivity) hl1
  obtain ⟨-, dP1, -, dPd, -⟩ := c05_aux_P_derivs (fam_Z S.p R ε μ y) (fam_lambda S.p ε μ y) y
    hlam0.ne'
  have hform := (hvb ε μ R Y htv y hy).1
  have hvs := (hvsm ε μ R Y htsm).1
  obtain ⟨-, hZc, -⟩ := hzr ε μ R Y htz (y - s) y (by linarith) (by linarith)
  have hI1 := hfund ε μ R Y htf y hy s hs
  have hI3 := hcub ε μ R Y htc y hy s hs
  set lam := fam_lambda S.p ε μ y with hlamdef
  set Z := fam_Z S.p R ε μ with hZ
  set m₀ := min |s| lam⁻¹ with hm₀
  set e : ℝ → ℂ := fun z => Complex.exp (Complex.I * ((lam * (z - y) : ℝ) : ℂ)) with hedef
  have hPeq : c05_plane_wave S.p R ε μ y = fun z => 2 * (Z y / (Complex.I * (lam : ℂ)) * e z).re :=
    rfl
  have hec : Continuous e := by simp only [hedef]; fun_prop
  have hD := c05_aux_pw_ftc (v := res_vY S.p R ε μ Y) (P := c05_plane_wave S.p R ε μ y)
    (Z := Z) (e := e) (c := (c_cubic S.p ε : ℂ)) (Zy := Z y) (a := y - s) (b := y)
    (hvs.differentiable (by simp)) (hvs.continuous_deriv (by simp)) (by rw [hPeq]; exact dPd)
    (by rw [hPeq, dP1]; fun_prop) (fun t ht' => by
      have hmem : t ∈ Icc (Y / 2) (3 * Y) := by
        rw [mem_uIcc] at ht'
        rcases ht' with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> exact ⟨by linarith, by linarith⟩
      rw [(hform t hmem).1, hPeq, dP1]
      simp only [Complex.add_re, Complex.sub_re]; ring) hZc hec
  have hre : ∀ x : ℂ, |2 * x.re| ≤ 2 * ‖x‖ := fun x => by
    rw [abs_mul, abs_two]; gcongr; exact Complex.abs_re_le_norm _
  have hcn : ‖(c_cubic S.p ε : ℂ)‖ ≤ Cc * ε := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hεC
  have hX3 : 0 ≤ Y ^ (-3 * beta S.p) := (Real.rpow_pos_of_pos hY0 _).le
  have hm0 : 0 ≤ m₀ := le_min (abs_nonneg s) (by positivity)
  have hY1s : 0 ≤ Y ^ (-beta S.p - 1) * s ^ 2 := by positivity
  have hX2 : 0 ≤ ε * Y ^ (-3 * beta S.p) * m₀ := by positivity
  unfold c05_plane_wave_Delta
  rw [hD]
  refine (hre _).trans ?_
  calc 2 * ‖(∫ t in (y - s)..y, (Z t - Z y * e t)) + (c_cubic S.p ε : ℂ) * ∫ t in (y - s)..y, Z t ^ 3‖
      ≤ 2 * (Cf * Y ^ (-beta S.p - 1) * s ^ 2 + (Cc * ε) * (K * Y ^ (-3 * beta S.p) * m₀)) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add hI1 ?_)
        rw [norm_mul]; exact mul_le_mul hcn hI3 (norm_nonneg _) (by positivity)
    _ = 2 * (Cf * (Y ^ (-beta S.p - 1) * s ^ 2) + (Cc * K) * (ε * Y ^ (-3 * beta S.p) * m₀)) := by
        ring
    _ ≤ _ := c05_aux_fin2 hY1s hX2 (by nlinarith [mul_pos hCc hK]) (by nlinarith [mul_pos hCc hK])

set_option maxHeartbeats 800000 in

/-- Blueprint: lem:c05_plane_wave_comparison.  For `y ∈ [Y,2Y]`, `λ = λ(y)`, `|s| ≤ Y/4`,
`m₀ = min{|s|, λ⁻¹}`, `m₁ = min{1, λ|s|}`: the comparison bounds for `Δv_Y - ΔP_y` and its first
two derivatives. -/
theorem c05_plane_wave_comparison (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ s : ℝ, |s| ≤ Y / 4 →
          let lam := fam_lambda S.p ε μ y
          let v := res_vY S.p R ε μ Y
          let P := c05_plane_wave S.p R ε μ y
          let m₀ := min |s| lam⁻¹
          let m₁ := min 1 (lam * |s|)
          |c05_plane_wave_Delta v y s - c05_plane_wave_Delta P y s| ≤
              C * (Y ^ (-beta S.p - 1) * s ^ 2 + ε * Y ^ (-3 * beta S.p) * m₀) ∧
            |c05_plane_wave_Delta (deriv v) y s - c05_plane_wave_Delta (deriv P) y s| ≤
              C * (Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2) + ε * Y ^ (-3 * beta S.p) * m₁) ∧
            |c05_plane_wave_Delta (deriv (deriv v)) y s -
                c05_plane_wave_Delta (deriv (deriv P)) y s| ≤
              C * lam * (Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2) + ε * Y ^ (-3 * beta S.p) * m₁) := by
  have hp := S.hp_lo
  have hp1 := S.hp_hi
  have hp0 : 0 < S.p := by linarith
  have hip : 0 < 1 / S.p := by positivity
  have hip2 : 1 / S.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have hβ1 : 1 < beta S.p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨Rf, hRf, Cf, hCf, hff⟩ := c05_frozen_frequency S
  obtain ⟨Rv, hRv, Cv, hCv, hvb⟩ := c05_vY_bounds S
  obtain ⟨Rsm, hRsm, hvsm⟩ := c05_aux_vY_smooth S
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨C₀, hC₀, hs0⟩ := hsym 0
  obtain ⟨Cc, hCc, hsc⟩ := c05_small_constants S
  obtain ⟨Ra, hRa, Ca, hCa, hpwa⟩ := c05_aux_pw_value S
  set M : ℝ := (4 : ℝ) ^ (6 : ℝ) with hM
  have hM1 : 1 ≤ M := Real.one_le_rpow (by norm_num) (by norm_num)
  set K3 : ℝ := C₀ * M + 16 * Cp * M with hK3
  have hK30 : 0 ≤ K3 := by positivity
  refine ⟨max (max (max Rf Rv) (max Rsm Rp)) (max Rs Ra), hRf.trans (by simp), 8 * Cf + 2 * Cc * K3 + 6 * Cc * Cf + 1 + Ca,
    by positivity, ?_⟩
  intro ε μ R Y ht y hy s hs lam v P m₀ m₁
  have htf := c05_aux_tuple_mono (show Rf ≤ max (max (max Rf Rv) (max Rsm Rp)) (max Rs Ra) by simp) ht
  have htv := c05_aux_tuple_mono (show Rv ≤ max (max (max Rf Rv) (max Rsm Rp)) (max Rs Ra) by simp) ht
  have htsm := c05_aux_tuple_mono (show Rsm ≤ max (max (max Rf Rv) (max Rsm Rp)) (max Rs Ra) by simp) ht
  have htp := c05_aux_tuple_mono (show Rp ≤ max (max (max Rf Rv) (max Rsm Rp)) (max Rs Ra) by simp) ht
  have hta := c05_aux_tuple_mono (show Ra ≤ max (max (max Rf Rv) (max Rsm Rp)) (max Rs Ra) by simp) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ max (max (max Rf Rv) (max Rsm Rp)) (max Rs Ra) by simp) ht
  have hR : 1 ≤ R := hRf.trans htf.2.2.2.1
  have hY : 8 * R ≤ Y := ht.2.2.2.2
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hs' := abs_le.mp hs
  have hy1 := hy.1
  have hy2 := hy.2
  have hεC : |c_cubic S.p ε| ≤ Cc * ε := by
    have := hsc ε μ ht.1 ht.2.1 ht.2.2.1
    have := abs_nonneg (c_eps S.p ε); have := abs_nonneg (n_eps S.p ε)
    have := abs_nonneg (c_log S.p ε μ); linarith
  have hε0 : 0 ≤ ε := ht.1
  -- frozen frequency data
  have hF := hff ε μ R Y htf y hy s hs
  dsimp only at hF
  obtain ⟨F1, F2, F3, F4, F5, F6⟩ := hF
  -- vY data
  have hV := hvb ε μ R Y htv y hy
  dsimp only at hV
  have hform := hV.1
  have hvs := (hvsm ε μ R Y htsm).1
  set Z := fam_Z S.p R ε μ with hZ
  set c : ℂ := (c_cubic S.p ε : ℂ) with hc
  have hcn : ‖c‖ ≤ Cc * ε := by rw [hc, Complex.norm_real, Real.norm_eq_abs]; exact hεC
  -- the plane wave
  obtain ⟨⟨hl1, hl2, -⟩, -, ⟨hZ0, hZ30, -⟩, -⟩ := hs0 ε μ R Y hts y (by linarith)
  have hy0 : 0 < y := by linarith
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hl1
  obtain ⟨he, dP1, dP2, dPd, dP1d⟩ := c05_aux_P_derivs (Z y) lam y hlam0.ne'
  set e : ℝ → ℂ := fun z => Complex.exp (Complex.I * ((lam * (z - y) : ℝ) : ℂ)) with hedef
  have hPdef : P = fun z => 2 * (Z y / (Complex.I * (lam : ℂ)) * e z).re := rfl
  have hPd1 : deriv P = fun z => 2 * (Z y * e z).re := by rw [hPdef, dP1]
  have hPd2 : deriv (deriv P) = fun z => 2 * (Complex.I * (lam : ℂ) * Z y * e z).re := by
    rw [hPd1, dP2]
  have hey : e y = 1 := by simp [hedef]
  have hea : e (y - s) = Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) := by
    simp only [hedef]; congr 1; push_cast; ring
  have hyI : y ∈ Icc (Y / 2) (3 * Y) := ⟨by linarith, by linarith⟩
  have haI : y - s ∈ Icc (Y / 2) (3 * Y) := ⟨by linarith, by linarith⟩
  have hX1 : 0 ≤ Y ^ (-beta S.p - 1) := (Real.rpow_pos_of_pos hY0 _).le
  have hX3 : 0 ≤ Y ^ (-3 * beta S.p) := (Real.rpow_pos_of_pos hY0 _).le
  have hm1 : 0 ≤ m₁ := le_min zero_le_one (by positivity)
  have hm0 : 0 ≤ m₀ := le_min (abs_nonneg s) (by positivity)
  have hQ : 0 ≤ |s| + lam * s ^ 2 := by positivity
  have hre : ∀ x : ℂ, |2 * x.re| ≤ 2 * ‖x‖ := fun x => by
    rw [abs_mul, abs_two]; gcongr; exact Complex.abs_re_le_norm _
  have hCK := mul_nonneg hCc.le hK30
  have hCF := mul_nonneg hCc.le hCf.le
  refine ⟨?_, ?_, ?_⟩
  · -- values
    refine (hpwa ε μ R Y hta y hy s hs).trans ?_
    have hX : 0 ≤ Y ^ (-beta S.p - 1) * s ^ 2 + ε * Y ^ (-3 * beta S.p) * m₀ := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith [hCK, hCF, hCa.le]) hX
  · -- first derivatives
    have hid : c05_plane_wave_Delta (deriv v) y s - c05_plane_wave_Delta (deriv P) y s =
        2 * (Z y * Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) - Z (y - s) +
          c * (Z y ^ 3 - Z (y - s) ^ 3)).re := by
      unfold c05_plane_wave_Delta
      have hea' : e (y - s) = Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) := hea
      rw [(hform y hyI).1, (hform (y - s) haI).1, hPd1]
      simp only
      rw [hey, hea']
      simp only [mul_one, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.sub_im]
      push_cast
      ring
    rw [hid]
    refine (hre _).trans ?_
    calc 2 * ‖Z y * Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) - Z (y - s) + c * (Z y ^ 3 - Z (y - s) ^ 3)‖
        ≤ 2 * (Cf * Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2) +
          (Cc * ε) * (Cf * Y ^ (-3 * beta S.p) * m₁)) := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add F3 ?_)
          rw [norm_mul]; exact mul_le_mul hcn F5 (norm_nonneg _) (by positivity)
      _ = 2 * (Cf * (Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2)) +
          (Cc * Cf) * (ε * Y ^ (-3 * beta S.p) * m₁)) := by ring
      _ ≤ _ := c05_aux_fin2 (by positivity) (by positivity) (by linarith [hCK, hCF, hCa.le])
          (by linarith [hCK, hCF, hCa.le])
  · -- second derivatives
    have hea' : e (y - s) = Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) := hea
    have hid : c05_plane_wave_Delta (deriv (deriv v)) y s -
        c05_plane_wave_Delta (deriv (deriv P)) y s =
        2 * ((deriv Z y - Complex.I * (lam : ℂ) * Z y - (deriv Z (y - s) -
            Complex.I * (lam : ℂ) * Z (y - s))) +
          Complex.I * (lam : ℂ) * (Z y * Complex.exp (-(Complex.I * ((lam * s : ℝ) : ℂ))) - Z (y - s)) +
          3 * c * (Z y ^ 2 * deriv Z y - Z (y - s) ^ 2 * deriv Z (y - s))).re := by
      unfold c05_plane_wave_Delta
      rw [(hform y hyI).2, (hform (y - s) haI).2, hPd2]
      simp only
      rw [hey, hea']
      rw [show ∀ A1 A2 B1 B2 : ℂ, 2 * A1.re - 2 * A2.re - (2 * B1.re - 2 * B2.re) =
        2 * (A1 - A2 - (B1 - B2)).re from fun A1 A2 B1 B2 => by simp only [Complex.sub_re]; ring]
      exact congrArg (fun x : ℂ => 2 * x.re) (by ring)
    rw [hid]
    refine (hre _).trans ?_
    have hX : 0 ≤ Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2) := by positivity
    have hX2 : 0 ≤ ε * Y ^ (-3 * beta S.p) * m₁ := by positivity
    calc _ ≤ 2 * (Cf * Y ^ (-beta S.p - 1) * lam * (|s| + lam * s ^ 2) +
          lam * (Cf * Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2)) +
          3 * (Cc * ε) * (Cf * Y ^ (-3 * beta S.p) * lam * m₁)) := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add F4 ?_)) ?_)
          · rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hlam0]
            exact mul_le_mul_of_nonneg_left F3 hlam0.le
          · rw [norm_mul, norm_mul, show ‖(3 : ℂ)‖ = 3 by simp]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hcn (by norm_num)) F6 (norm_nonneg _)
              (by positivity)
      _ = lam * (2 * ((2 * Cf) * (Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2)) +
          (3 * Cc * Cf) * (ε * Y ^ (-3 * beta S.p) * m₁))) := by ring
      _ ≤ lam * ((8 * Cf + 2 * Cc * K3 + 6 * Cc * Cf + 1 + Ca) *
          (Y ^ (-beta S.p - 1) * (|s| + lam * s ^ 2) + ε * Y ^ (-3 * beta S.p) * m₁)) :=
          mul_le_mul_of_nonneg_left (c05_aux_fin2 hX hX2 (by linarith [hCK, hCF, hCa.le])
            (by linarith [hCK, hCF, hCa.le])) hlam0.le
      _ = _ := by ring

/-- Blueprint: lem:c05_cubic_kernel_integrals.  For `p ∈ (0,1)`, `λ > 0`, `L > 0`:
`∫ (|s| + λs²) m₀² |s|^{-p-3} ≤ (4/(1-p) + 4/p) λ^{p-1}`,
`∫ m₁ m₀² |s|^{-p-3} ≤ (2/(1-p) + 2/(p+2)) λ^p`, `∫_{|s|≥L} |s|^{-p-3} = 2/(p+2) L^{-p-2}`
(all integrals convergent). -/
theorem c05_cubic_kernel_integrals (p lam L : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hlam : 0 < lam)
    (hL : 0 < L) :
    Integrable (fun s : ℝ => (|s| + lam * s ^ 2) * min |s| lam⁻¹ ^ 2 * |s| ^ (-p - 3)) ∧
    (∫ s : ℝ, (|s| + lam * s ^ 2) * min |s| lam⁻¹ ^ 2 * |s| ^ (-p - 3)) ≤
      (4 / (1 - p) + 4 / p) * lam ^ (p - 1) ∧
    Integrable (fun s : ℝ => min 1 (lam * |s|) * min |s| lam⁻¹ ^ 2 * |s| ^ (-p - 3)) ∧
    (∫ s : ℝ, min 1 (lam * |s|) * min |s| lam⁻¹ ^ 2 * |s| ^ (-p - 3)) ≤
      (2 / (1 - p) + 2 / (p + 2)) * lam ^ p ∧
    IntegrableOn (fun s : ℝ => |s| ^ (-p - 3)) {s | L ≤ |s|} ∧
    (∫ s in {s : ℝ | L ≤ |s|}, |s| ^ (-p - 3)) = 2 / (p + 2) * L ^ (-p - 2) := by
  set a := lam⁻¹ with ha_def
  have ha : 0 < a := inv_pos.mpr hlam
  have hla : lam * a = 1 := mul_inv_cancel₀ hlam.ne'
  have hapow : a ^ (1 - p) = lam ^ (p - 1) := by
    rw [ha_def, Real.inv_rpow hlam.le, ← Real.rpow_neg hlam.le]; ring_nf
  have hapow2 : a ^ (-p) = lam ^ p := by
    rw [ha_def, Real.inv_rpow hlam.le, ← Real.rpow_neg hlam.le]; ring_nf
  -- part (i)
  set φ1 : ℝ → ℝ := fun t => (t + lam * t ^ 2) * min t a ^ 2 * t ^ (-p - 3) with hφ1
  have hφ1m : Measurable φ1 := by fun_prop
  obtain ⟨hI1, hB1⟩ := c05_aux_Ioi_split_bound φ1 (fun t => 2 * t ^ (-p))
    (fun t => (2 * a) * t ^ (-p - 1)) a ha hφ1m.aestronglyMeasurable
    (by
      intro t ⟨ht0, hta⟩
      have hm : min t a = t := min_eq_left hta
      have hu : 0 < t ^ (-p - 3) := Real.rpow_pos_of_pos ht0 _
      have hlt : lam * t ≤ 1 := by
        calc lam * t ≤ lam * a := by gcongr
          _ = 1 := hla
      have h3 : t ^ 3 * t ^ (-p - 3) = t ^ (-p) := by
        rw [c05_aux_rpow_mul_npow ht0]; norm_num
      simp only [hφ1, hm]
      constructor
      · positivity
      · calc (t + lam * t ^ 2) * t ^ 2 * t ^ (-p - 3) ≤ (2 * t) * t ^ 2 * t ^ (-p - 3) := by
              gcongr; nlinarith
          _ = 2 * (t ^ 3 * t ^ (-p - 3)) := by ring
          _ = 2 * t ^ (-p) := by rw [h3])
    (by
      intro t ht
      have hat : a < t := ht
      have ht0 : 0 < t := ha.trans hat
      have hm : min t a = a := min_eq_right hat.le
      have hu : 0 < t ^ (-p - 3) := Real.rpow_pos_of_pos ht0 _
      have hlt : 1 ≤ lam * t := by
        calc 1 = lam * a := hla.symm
          _ ≤ lam * t := by gcongr
      have h2 : t ^ 2 * t ^ (-p - 3) = t ^ (-p - 1) := by
        rw [c05_aux_rpow_mul_npow ht0]; norm_num; ring_nf
      simp only [hφ1, hm]
      constructor
      · positivity
      · calc (t + lam * t ^ 2) * a ^ 2 * t ^ (-p - 3) ≤ (2 * lam * t ^ 2) * a ^ 2 * t ^ (-p - 3) := by
              gcongr; nlinarith
          _ = 2 * (lam * a) * a * (t ^ 2 * t ^ (-p - 3)) := by ring
          _ = 2 * a * t ^ (-p - 1) := by rw [h2, hla]; ring)
    (c05_aux_int_Ioc_rpow 2 (-p) a (by linarith) ha).1
    (c05_aux_int_Ioi_rpow (2 * a) (-p - 1) a (by linarith) ha).1
  rw [(c05_aux_int_Ioc_rpow 2 (-p) a (by linarith) ha).2,
    (c05_aux_int_Ioi_rpow (2 * a) (-p - 1) a (by linarith) ha).2] at hB1
  have hf1 : (fun s : ℝ => (|s| + lam * s ^ 2) * min |s| lam⁻¹ ^ 2 * |s| ^ (-p - 3)) =
      fun s => φ1 |s| := by
    funext s; simp only [hφ1, sq_abs]; rfl
  -- part (ii)
  set φ2 : ℝ → ℝ := fun t => min 1 (lam * t) * min t a ^ 2 * t ^ (-p - 3) with hφ2
  have hφ2m : Measurable φ2 := by fun_prop
  obtain ⟨hI2, hB2⟩ := c05_aux_Ioi_split_bound φ2 (fun t => lam * t ^ (-p))
    (fun t => a ^ 2 * t ^ (-p - 3)) a ha hφ2m.aestronglyMeasurable
    (by
      intro t ⟨ht0, hta⟩
      have hm : min t a = t := min_eq_left hta
      have hlt : lam * t ≤ 1 := by
        calc lam * t ≤ lam * a := by gcongr
          _ = 1 := hla
      have hm1 : min 1 (lam * t) = lam * t := min_eq_right hlt
      have h3 : t ^ 3 * t ^ (-p - 3) = t ^ (-p) := by
        rw [c05_aux_rpow_mul_npow ht0]; norm_num
      simp only [hφ2, hm, hm1]
      constructor
      · positivity
      · rw [show lam * t * t ^ 2 * t ^ (-p - 3) = lam * (t ^ 3 * t ^ (-p - 3)) by ring, h3])
    (by
      intro t ht
      have hat : a < t := ht
      have ht0 : 0 < t := ha.trans hat
      have hm : min t a = a := min_eq_right hat.le
      have hlt : 1 ≤ lam * t := by
        calc 1 = lam * a := hla.symm
          _ ≤ lam * t := by gcongr
      have hm1 : min 1 (lam * t) = 1 := min_eq_left hlt
      simp only [hφ2, hm, hm1, one_mul]
      exact ⟨by positivity, le_rfl⟩)
    (c05_aux_int_Ioc_rpow lam (-p) a (by linarith) ha).1
    (c05_aux_int_Ioi_rpow (a ^ 2) (-p - 3) a (by linarith) ha).1
  rw [(c05_aux_int_Ioc_rpow lam (-p) a (by linarith) ha).2,
    (c05_aux_int_Ioi_rpow (a ^ 2) (-p - 3) a (by linarith) ha).2] at hB2
  have hf2 : (fun s : ℝ => min 1 (lam * |s|) * min |s| lam⁻¹ ^ 2 * |s| ^ (-p - 3)) =
      fun s => φ2 |s| := rfl
  -- part (iii)
  set φ3 : ℝ → ℝ := (Ici L).indicator (fun t => t ^ (-p - 3)) with hφ3
  have hI3' : IntegrableOn (fun t : ℝ => t ^ (-p - 3)) (Ici L) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_Ioi_rpow_of_lt (by linarith) hL)
  have hI3 : IntegrableOn φ3 (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ici).mpr hI3').integrableOn
  have hf3 : {s : ℝ | L ≤ |s|}.indicator (fun s : ℝ => |s| ^ (-p - 3)) = fun s => φ3 |s| := by
    funext s
    simp only [hφ3, indicator, mem_ofPred_eq, mem_Ici]
  have hmeas3 : MeasurableSet {s : ℝ | L ≤ |s|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf1]; exact c05_aux_integrable_comp_abs φ1 hI1
  · rw [hf1, integral_comp_abs]
    have : 2 * (2 * (a ^ (-p + 1) / (-p + 1)) + 2 * a * (-a ^ (-p - 1 + 1) / (-p - 1 + 1))) =
        (4 / (1 - p) + 4 / p) * lam ^ (p - 1) := by
      rw [show -p + 1 = 1 - p by ring, show -p - 1 + 1 = -p by ring, hapow,
        show 2 * a * (-a ^ (-p) / -p) = 2 * (a * a ^ (-p)) / p by
          field_simp]
      rw [show a * a ^ (-p) = a ^ (1 - p) by
        rw [show (1 : ℝ) - p = 1 + -p by ring, Real.rpow_add ha, Real.rpow_one], hapow]
      have : (1 : ℝ) - p ≠ 0 := by linarith
      field_simp
      ring
    linarith
  · rw [hf2]; exact c05_aux_integrable_comp_abs φ2 hI2
  · rw [hf2, integral_comp_abs]
    have : 2 * (lam * (a ^ (-p + 1) / (-p + 1)) + a ^ 2 * (-a ^ (-p - 3 + 1) / (-p - 3 + 1))) =
        (2 / (1 - p) + 2 / (p + 2)) * lam ^ p := by
      rw [show -p + 1 = 1 - p by ring, show -p - 3 + 1 = -(p + 2) by ring, hapow]
      rw [show a ^ 2 * (-a ^ (-(p + 2)) / -(p + 2)) = a ^ (-p) / (p + 2) by
        rw [neg_div_neg_eq, ← mul_div_assoc, c05_aux_rpow_mul_npow ha 2,
          show ((2 : ℕ) : ℝ) + -(p + 2) = -p by push_cast; ring], hapow2]
      have hll : lam * lam ^ (p - 1) = lam ^ p := by
        rw [mul_comm, ← Real.rpow_add_one hlam.ne']; ring_nf
      rw [show 2 * (lam * (lam ^ (p - 1) / (1 - p)) + lam ^ p / (p + 2)) =
        2 * ((lam * lam ^ (p - 1)) / (1 - p) + lam ^ p / (p + 2)) by ring, hll]
      have : (1 : ℝ) - p ≠ 0 := by linarith
      have : p + 2 ≠ 0 := by linarith
      field_simp
    linarith
  · refine (integrable_indicator_iff hmeas3).mp ?_
    rw [hf3]
    exact c05_aux_integrable_comp_abs φ3 hI3
  · rw [← integral_indicator hmeas3, hf3, integral_comp_abs, hφ3,
      setIntegral_indicator measurableSet_Ici,
      Set.inter_eq_right.mpr (Ici_subset_Ioi.mpr hL), integral_Ici_eq_integral_Ioi,
      integral_Ioi_rpow_of_lt (by linarith) hL]
    rw [show -p - 3 + 1 = -(p + 2) by ring, neg_div_neg_eq, show -(p + 2) = -p - 2 by ring]
    ring


/-- Helper (from lem:c05_primitive, lem:c05_symbol_bounds): `v_Y` is measurable and continuous on
`(R,∞)`. -/
theorem c05_aux_vY_measurable (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
      Measurable (res_vY S.p R ε μ Y) ∧ ContinuousOn (res_vY S.p R ε μ Y) (Ioi R) := by
  obtain ⟨Rp, hRp, Cp, hCp, hprim⟩ := c05_primitive S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  refine ⟨max Rp Rs, le_max_of_le_left hRp, ?_⟩
  intro ε μ R Y ht
  have htp := c05_aux_tuple_mono (show Rp ≤ max Rp Rs by simp) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ max Rp Rs by simp) ht
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have hpos : ∀ t, R < t → 0 < fam_lambda S.p ε μ t := by
    intro t ht'
    have h1 := (hsym0 ε μ R Y hts t ht'.le).1.1
    have : 0 < t := by linarith
    have : 0 < t ^ (1 / S.p) / 2 := by positivity
    linarith
  obtain ⟨⟨hZi, hZ3i, -⟩, -⟩ := hprim ε μ R Y htp R le_rfl
  set F : ℝ → ℂ := fun t => fam_Z S.p R ε μ t + (c_cubic S.p ε : ℂ) * fam_Z S.p R ε μ t ^ 3
    with hF
  have hFi : IntegrableOn F (Ioi R) := hZi.add (hZ3i.const_mul _)
  have hZc : ∀ t, R < t → ContinuousAt (fam_Z S.p R ε μ) t := fun t ht' =>
    (c05_aux_family_smooth S.p R ε μ S.hp_lo S.hp_hi (by linarith) hpos ht').2.1.continuousAt
  have hFc : ContinuousOn F (Ioi R) := fun t ht' =>
    ((hZc t ht').add (continuousAt_const.mul ((hZc t ht').pow 3))).continuousWithinAt
  set f : ℝ → ℝ := fun z => -2 * res_chiY Y z * (∫ t in Ioi z, F t).re with hf
  have hfc : ContinuousOn f (Ioi R) := by
    intro z hz
    have hT := (c05_aux_tail_hasDeriv F R hFi hFc hz).continuousAt
    exact ((continuousAt_const.mul (c05_aux_chiY_smooth Y).continuous.continuousAt).mul
      (Complex.continuous_re.continuousAt.comp hT)).continuousWithinAt
  have heq : res_vY S.p R ε μ Y = (Ioi R).piecewise f (fun _ => 0) := by
    funext z
    simp only [res_vY, Set.piecewise, mem_Ioi, hf, hF]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hfc.measurable_piecewise continuousOn_const measurableSet_Ioi
  · refine hfc.congr (fun z hz => ?_)
    rw [heq]; exact piecewise_eq_of_mem _ _ _ hz

/-- Blueprint: lem:c05_cubic_near.  Near region:
`|K_ε| ∫_{|s|≤Y/4} |s|^{-p-3} |N_j(y,s)| ds ≤ C ε Y^{1-5β+j/p}` on `[Y,2Y]`, `j = 0,1`
(the integrals converge). -/
theorem c05_cubic_near (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y),
          IntegrableOn (fun s => |s| ^ (-S.p - 3) * |c05_plane_wave_N0 S.p R ε μ Y y s|)
            {s | |s| ≤ Y / 4} ∧
          |c05_plane_wave_K S.p ε| *
              (∫ s in {s : ℝ | |s| ≤ Y / 4}, |s| ^ (-S.p - 3) * |c05_plane_wave_N0 S.p R ε μ Y y s|) ≤
            C * ε * Y ^ (1 - 5 * beta S.p) ∧
          IntegrableOn (fun s => |s| ^ (-S.p - 3) * |c05_plane_wave_N1 S.p R ε μ Y y s|)
            {s | |s| ≤ Y / 4} ∧
          |c05_plane_wave_K S.p ε| *
              (∫ s in {s : ℝ | |s| ≤ Y / 4}, |s| ^ (-S.p - 3) * |c05_plane_wave_N1 S.p R ε μ Y y s|) ≤
            C * ε * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
  obtain ⟨Rv, hRv, Cv, hCv, hvb⟩ := c05_vY_bounds S
  obtain ⟨Rc, hRc, Cc, hCc, hcmp⟩ := c05_plane_wave_comparison S
  obtain ⟨Rm, hRm, hmeas⟩ := c05_aux_vY_measurable S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have h2β := c05_aux_two_beta S.p hp0
  set q := 1 / S.p with hq
  have hq0 : 0 < q := by positivity
  have hqp : q * S.p = 1 := by rw [hq]; field_simp
  set k1 := 4 / (1 - S.p) + 4 / S.p with hk1
  set k2 := 2 / (1 - S.p) + 2 / (S.p + 2) with hk2
  have hk10 : 0 ≤ k1 := by
    have : 0 < 1 - S.p := by linarith [S.hp_hi]
    positivity
  have hk20 : 0 ≤ k2 := by
    have : 0 < 1 - S.p := by linarith [S.hp_hi]
    positivity
  set Kc := (S.p + 1) * |calpha S.p| / 2 with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set D := Kc * Cc * Cv ^ 2 * (k1 * 2 ^ (1 - S.p) + k2 * 2 ^ (S.p + 1)) with hD
  have hD0 : 0 ≤ D := by positivity
  set R₀ := max (max Rv Rc) (max Rm Rs) with hR₀
  refine ⟨R₀, hRv.trans (by simp [hR₀]), 3 * D + 9 * D * (2 * 2 ^ q) + 1, by positivity, ?_⟩
  intro ε μ R Y ht y hy
  have htv := c05_aux_tuple_mono (show Rv ≤ R₀ by simp [hR₀]) ht
  have htc := c05_aux_tuple_mono (show Rc ≤ R₀ by simp [hR₀]) ht
  have htm := c05_aux_tuple_mono (show Rm ≤ R₀ by simp [hR₀]) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ R₀ by simp [hR₀]) ht
  have hε : 0 ≤ ε := ht.1
  have hε1 : ε ≤ 1 := ht.2.1.trans S.hε₀_le
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hY : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hY0 : 0 < Y := by linarith
  have hyR : R ≤ y := by linarith [hy.1, ht.2.2.2.2]
  have hy0 : 0 < y := by linarith
  set lam := fam_lambda S.p ε μ y with hlam
  have hsy := (hsym0 ε μ R Y hts y hyR).1
  have hlamY : Y ^ q / 2 ≤ lam := by
    have h2 : Y ^ q ≤ y ^ q := Real.rpow_le_rpow hY0.le hy.1 hq0.le
    linarith [hsy.1]
  have hYq : 0 < Y ^ q := Real.rpow_pos_of_pos hY0 q
  have hlam0 : 0 < lam := by linarith
  have hlamU : lam ≤ 2 * 2 ^ q * Y ^ q := by
    have h2 : y ^ q ≤ (2 * Y) ^ q := Real.rpow_le_rpow hy0.le hy.2 hq0.le
    rw [Real.mul_rpow (by norm_num) hY0.le] at h2
    linarith [hsy.2.1]
  set c := Cv * Y ^ (-beta S.p) with hc
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨-, -, -, h3⟩ := hvb ε μ R Y htv y hy
  have hv3 := h3 (res_vY S.p R ε μ Y) (by simp)
  have hP3 := h3 (c05_plane_wave S.p R ε μ y) (by simp)
  set u := Y ^ (-beta S.p - 1) with hu
  set e := ε * Y ^ (-3 * beta S.p) with he
  have hu0 : 0 ≤ u := by positivity
  have he0 : 0 ≤ e := by positivity
  set f1 : ℝ → ℝ := fun s => (|s| + lam * s ^ 2) * min |s| lam⁻¹ ^ 2 * |s| ^ (-S.p - 3) with hf1
  set f2 : ℝ → ℝ := fun s => min 1 (lam * |s|) * min |s| lam⁻¹ ^ 2 * |s| ^ (-S.p - 3) with hf2
  obtain ⟨hI1, hB1, hI2, hB2, -, -⟩ := c05_cubic_kernel_integrals S.p lam 1 hp0 S.hp_hi hlam0 one_pos
  -- the pointwise bounds
  have hpt : ∀ s : ℝ, |s| ≤ Y / 4 →
      |c05_plane_wave_N0 S.p R ε μ Y y s| ≤
          3 * Cc * c ^ 2 * (min |s| lam⁻¹ ^ 2 * (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|))) ∧
        |c05_plane_wave_N1 S.p R ε μ Y y s| ≤
          9 * Cc * c ^ 2 * lam *
            (min |s| lam⁻¹ ^ 2 * (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|))) := by
    intro s hs
    obtain ⟨c1, c2, c3⟩ := hcmp ε μ R Y htc y hy s hs
    obtain ⟨v1, v2, v3⟩ := hv3 s
    obtain ⟨p1, p2, p3⟩ := hP3 s
    have hm1 : min 1 (lam * |s|) = lam * min |s| lam⁻¹ := by
      rw [mul_min_of_nonneg _ _ hlam0.le, mul_inv_cancel₀ hlam0.ne', min_comm]
    have hm0 : 0 ≤ min |s| lam⁻¹ := le_min (abs_nonneg s) (inv_pos.mpr hlam0).le
    obtain ⟨n0, n1⟩ := c05_aux_N_near_bounds (Cc := Cc) hm1 v1 p1 v2 p2 p3 c2 c1 c3
    have hus := mul_nonneg hu0 (abs_nonneg s)
    have hX : ∀ k : ℝ, k = 2 → (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|)) +
        k * lam * (u * s ^ 2 + e * min |s| lam⁻¹) ≤
          (1 + k) * (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|)) := by
      intro k hk
      subst hk
      rw [hm1, ← sub_nonneg]
      ring_nf
      linarith
    have hCc2 : 0 ≤ Cc * c ^ 2 * min |s| lam⁻¹ ^ 2 := by positivity
    constructor
    · refine n0.trans ?_
      have := mul_le_mul_of_nonneg_left (hX 2 rfl) hCc2
      calc _ = Cc * c ^ 2 * min |s| lam⁻¹ ^ 2 *
            ((u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|)) +
              2 * lam * (u * s ^ 2 + e * min |s| lam⁻¹)) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    · refine n1.trans ?_
      have h5 : 5 * (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|)) +
          4 * lam * (u * s ^ 2 + e * min |s| lam⁻¹) ≤
            9 * (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|)) := by
        rw [hm1, ← sub_nonneg]
        ring_nf
        linarith
      have := mul_le_mul_of_nonneg_left h5 (mul_nonneg hCc2 hlam0.le)
      calc _ = Cc * c ^ 2 * min |s| lam⁻¹ ^ 2 * lam *
            (5 * (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|)) +
              4 * lam * (u * s ^ 2 + e * min |s| lam⁻¹)) := by ring
        _ ≤ _ := this
        _ = _ := by ring
  -- dominating functions
  set g0 : ℝ → ℝ := fun s => 3 * Cc * c ^ 2 * (u * f1 s + e * f2 s) with hg0
  have hf10 : ∀ s, 0 ≤ f1 s := fun s => by simp only [hf1]; positivity
  have hf20 : ∀ s, 0 ≤ f2 s := fun s => by
    simp only [hf2]
    have : 0 ≤ min 1 (lam * |s|) := le_min zero_le_one (by positivity)
    positivity
  have hg0i : Integrable g0 := ((hI1.const_mul u).add (hI2.const_mul e)).const_mul _
  have hg00 : ∀ s, 0 ≤ g0 s := fun s => by
    simp only [hg0]; have := hf10 s; have := hf20 s; positivity
  have hg0int : ∫ s, g0 s ≤ 3 * Cc * c ^ 2 * (u * (k1 * lam ^ (S.p - 1)) + e * (k2 * lam ^ S.p)) := by
    simp only [hg0]
    rw [integral_const_mul, integral_add (hI1.const_mul u) (hI2.const_mul e), integral_const_mul,
      integral_const_mul]
    gcongr
  have hdom : ∀ s, |s| ^ (-S.p - 3) *
      (min |s| lam⁻¹ ^ 2 * (u * (|s| + lam * s ^ 2) + e * min 1 (lam * |s|))) = u * f1 s + e * f2 s :=
    fun s => by simp only [hf1, hf2]; ring
  have hvm : Measurable (res_vY S.p R ε μ Y) := (hmeas ε μ R Y htm).1
  have hPm : Measurable (c05_plane_wave S.p R ε μ y) := (c05_aux_plane_wave_cont _ _ _ _ _).measurable
  obtain ⟨hJ0, hJ0b⟩ := c05_aux_near_integral (-S.p - 3) (Y / 4) _ g0
    (c05_aux_N_meas _ _ hvm hPm y).1 hg0i hg00 (fun s hs => by
      simp only [hg0]
      rw [← hdom s]
      have := mul_le_mul_of_nonneg_left (hpt s hs).1 (Real.rpow_nonneg (abs_nonneg s) (-S.p - 3))
      calc _ ≤ _ := this
        _ = _ := by ring)
  set g1 : ℝ → ℝ := fun s => lam * g0 s * 3 with hg1
  have hg1i : Integrable g1 := (hg0i.const_mul lam).mul_const 3
  have hg10 : ∀ s, 0 ≤ g1 s := fun s => by simp only [hg1]; have := hg00 s; positivity
  obtain ⟨hJ1, hJ1b⟩ := c05_aux_near_integral (-S.p - 3) (Y / 4) _ g1
    (c05_aux_N_meas _ _ hvm hPm y).2 hg1i hg10 (fun s hs => by
      simp only [hg1, hg0]
      rw [← hdom s]
      have := mul_le_mul_of_nonneg_left (hpt s hs).2 (Real.rpow_nonneg (abs_nonneg s) (-S.p - 3))
      calc _ ≤ _ := this
        _ = _ := by ring)
  have hg1int : ∫ s, g1 s = lam * (∫ s, g0 s) * 3 := by
    simp only [hg1]; rw [integral_mul_const, integral_const_mul]
  -- numerics
  have hK : |c05_plane_wave_K S.p ε| = Kc * ε := by
    unfold c05_plane_wave_K
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < S.p + 1),
      abs_of_nonneg hε, abs_two]
    ring
  have hc2 : c ^ 2 = Cv ^ 2 * Y ^ (-beta S.p * 2) := by
    rw [hc, mul_pow, ← Real.rpow_mul_natCast hY0.le]; norm_num
  have hlp1 : lam ^ (S.p - 1) ≤ 2 ^ (1 - S.p) * Y ^ (1 - q) := by
    calc lam ^ (S.p - 1) ≤ (Y ^ q / 2) ^ (S.p - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlamY (by linarith [S.hp_hi])
      _ = 2 ^ (1 - S.p) * Y ^ (1 - q) := by
          rw [Real.div_rpow hYq.le (by norm_num), ← Real.rpow_mul hY0.le,
            show q * (S.p - 1) = 1 - q by rw [mul_sub, hqp]; ring,
            show (1 : ℝ) - S.p = -(S.p - 1) by ring, Real.rpow_neg (by norm_num)]
          ring
  have hlp : lam ^ S.p ≤ 2 ^ (S.p + 1) * Y := by
    calc lam ^ S.p ≤ (2 * 2 ^ q * Y ^ q) ^ S.p := Real.rpow_le_rpow hlam0.le hlamU hp0.le
      _ = 2 ^ (S.p + 1) * Y := by
          rw [Real.mul_rpow (by positivity) hYq.le, Real.mul_rpow (by norm_num) (by positivity),
            ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hY0.le, hqp, Real.rpow_one,
            Real.rpow_one, Real.rpow_add (by norm_num), Real.rpow_one]
  have hcore : Kc * ε * (3 * Cc * c ^ 2 * (u * (k1 * lam ^ (S.p - 1)) + e * (k2 * lam ^ S.p))) ≤
      3 * D * ε * Y ^ (1 - 5 * beta S.p) := by
    have hA : Y ^ (-beta S.p * 2) * u * Y ^ (1 - q) = Y ^ (1 - 5 * beta S.p) := by
      rw [hu, ← Real.rpow_add hY0, ← Real.rpow_add hY0]
      congr 1; linarith only [h2β]
    have hB : Y ^ (-beta S.p * 2) * Y ^ (-3 * beta S.p) * Y = Y ^ (1 - 5 * beta S.p) := by
      rw [← Real.rpow_add hY0]
      conv_lhs => rw [show Y ^ (-beta S.p * 2 + -3 * beta S.p) * Y =
        Y ^ (-beta S.p * 2 + -3 * beta S.p) * Y ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hY0]
      congr 1; ring
    have hYb : 0 ≤ Y ^ (-beta S.p * 2) := by positivity
    have hYt : 0 ≤ Y ^ (1 - 5 * beta S.p) := by positivity
    have hεε : ε * ε ≤ ε := mul_le_of_le_one_right hε hε1
    calc Kc * ε * (3 * Cc * c ^ 2 * (u * (k1 * lam ^ (S.p - 1)) + e * (k2 * lam ^ S.p)))
        ≤ Kc * ε * (3 * Cc * (Cv ^ 2 * Y ^ (-beta S.p * 2)) *
            (u * (k1 * (2 ^ (1 - S.p) * Y ^ (1 - q))) +
              e * (k2 * (2 ^ (S.p + 1) * Y)))) := by
          rw [hc2]; gcongr
      _ = 3 * Kc * Cc * Cv ^ 2 * (k1 * 2 ^ (1 - S.p) * ε * (Y ^ (-beta S.p * 2) * u * Y ^ (1 - q)) +
            k2 * 2 ^ (S.p + 1) * (ε * ε) * (Y ^ (-beta S.p * 2) * Y ^ (-3 * beta S.p) * Y)) := by
          rw [he]; ring
      _ ≤ 3 * Kc * Cc * Cv ^ 2 * (k1 * 2 ^ (1 - S.p) * ε * Y ^ (1 - 5 * beta S.p) +
            k2 * 2 ^ (S.p + 1) * ε * Y ^ (1 - 5 * beta S.p)) := by
          rw [hA, hB]; gcongr
      _ = 3 * D * ε * Y ^ (1 - 5 * beta S.p) := by rw [hD]; ring
  have hYt0 : 0 ≤ Y ^ (1 - 5 * beta S.p) := by positivity
  have hJ0' : 0 ≤ ∫ s in {s : ℝ | |s| ≤ Y / 4}, |s| ^ (-S.p - 3) *
      |c05_plane_wave_N0 S.p R ε μ Y y s| :=
    setIntegral_nonneg (measurableSet_le continuous_abs.measurable measurable_const)
      (fun s _ => mul_nonneg (Real.rpow_nonneg (abs_nonneg s) _) (abs_nonneg _))
  refine ⟨hJ0, ?_, hJ1, ?_⟩
  · rw [hK]
    calc Kc * ε * _ ≤ Kc * ε * (3 * Cc * c ^ 2 * (u * (k1 * lam ^ (S.p - 1)) +
          e * (k2 * lam ^ S.p))) := by gcongr; exact hJ0b.trans hg0int
      _ ≤ 3 * D * ε * Y ^ (1 - 5 * beta S.p) := hcore
      _ ≤ _ := by
          gcongr
          have : 0 ≤ 9 * D * (2 * 2 ^ q) := by positivity
          linarith
  · rw [hK]
    have hYqt : Y ^ (1 - 5 * beta S.p) * Y ^ q = Y ^ (1 - 5 * beta S.p + q) := by
      rw [← Real.rpow_add hY0]
    have hg0n : 0 ≤ ∫ s, g0 s := integral_nonneg hg00
    calc Kc * ε * _ ≤ Kc * ε * (lam * (∫ s, g0 s) * 3) := by
          gcongr; rw [← hg1int]; exact hJ1b
      _ ≤ Kc * ε * (lam * (3 * Cc * c ^ 2 * (u * (k1 * lam ^ (S.p - 1)) +
          e * (k2 * lam ^ S.p))) * 3) := by gcongr
      _ = 3 * lam * (Kc * ε * (3 * Cc * c ^ 2 * (u * (k1 * lam ^ (S.p - 1)) +
          e * (k2 * lam ^ S.p)))) := by ring
      _ ≤ 3 * (2 * 2 ^ q * Y ^ q) * (3 * D * ε * Y ^ (1 - 5 * beta S.p)) := by
          gcongr
      _ = 9 * D * (2 * 2 ^ q) * ε * (Y ^ (1 - 5 * beta S.p) * Y ^ q) := by ring
      _ ≤ (3 * D + 9 * D * (2 * 2 ^ q) + 1) * ε * Y ^ (1 - 5 * beta S.p + q) := by
          rw [hYqt]
          have : 0 ≤ Y ^ (1 - 5 * beta S.p + q) := by positivity
          gcongr
          linarith

/-- Blueprint: lem:c05_cubic_far.  Far region:
`|K_ε| ∫_{|s|≥Y/4} |s|^{-p-3} |N_j(y,s)| ds ≤ C ε Y^{1-5β+j/p}` on `[Y,2Y]`, `j = 0,1`
(the integrals converge). -/
theorem c05_cubic_far (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y),
          IntegrableOn (fun s => |s| ^ (-S.p - 3) * |c05_plane_wave_N0 S.p R ε μ Y y s|)
            {s | Y / 4 ≤ |s|} ∧
          |c05_plane_wave_K S.p ε| *
              (∫ s in {s : ℝ | Y / 4 ≤ |s|}, |s| ^ (-S.p - 3) * |c05_plane_wave_N0 S.p R ε μ Y y s|) ≤
            C * ε * Y ^ (1 - 5 * beta S.p) ∧
          IntegrableOn (fun s => |s| ^ (-S.p - 3) * |c05_plane_wave_N1 S.p R ε μ Y y s|)
            {s | Y / 4 ≤ |s|} ∧
          |c05_plane_wave_K S.p ε| *
              (∫ s in {s : ℝ | Y / 4 ≤ |s|}, |s| ^ (-S.p - 3) * |c05_plane_wave_N1 S.p R ε μ Y y s|) ≤
            C * ε * Y ^ (1 - 5 * beta S.p + 1 / S.p) := by
  obtain ⟨Rv, hRv, Cv, hCv, hvb⟩ := c05_vY_bounds S
  obtain ⟨Rm, hRm, hmeas⟩ := c05_aux_vY_measurable S
  obtain ⟨Rs, hRs, hsym⟩ := c05_symbol_bounds S
  obtain ⟨Cs, -, hsym0⟩ := hsym 0
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  have h2β := c05_aux_two_beta S.p hp0
  set q := 1 / S.p with hq
  have hq0 : 0 < q := by positivity
  set Kc := (S.p + 1) * |calpha S.p| / 2 with hKc
  set C0f := Kc * (2 * Cv ^ 3 * 4) * (2 / (S.p + 2)) * 4 ^ (S.p + 2) with hC0f
  set C1f := Kc * (6 * Cv ^ 3 * 2) * (2 / (S.p + 2)) * 4 ^ (S.p + 2) with hC1f
  have hKc0 : 0 ≤ Kc := by positivity
  have hC0f0 : 0 ≤ C0f := by positivity
  have hC1f0 : 0 ≤ C1f := by positivity
  set R₀ := max (max Rv Rm) Rs with hR₀
  refine ⟨R₀, hRv.trans (by simp [hR₀]), C0f + C1f + 1, by positivity, ?_⟩
  intro ε μ R Y ht y hy
  have htv := c05_aux_tuple_mono (show Rv ≤ R₀ by simp [hR₀]) ht
  have htm := c05_aux_tuple_mono (show Rm ≤ R₀ by simp [hR₀]) ht
  have hts := c05_aux_tuple_mono (show Rs ≤ R₀ by simp [hR₀]) ht
  have hε : 0 ≤ ε := ht.1
  have hR : 1 ≤ R := hRs.trans hts.2.2.2.1
  have hY : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hY0 : 0 < Y := by linarith
  have hyR : R ≤ y := by linarith [hy.1, ht.2.2.2.2]
  have hy0 : 0 < y := by linarith
  set lam := fam_lambda S.p ε μ y with hlam
  have hlamY : Y ^ q / 2 ≤ lam := by
    have h1 := (hsym0 ε μ R Y hts y hyR).1.1
    have h2 : Y ^ q ≤ y ^ q := Real.rpow_le_rpow hY0.le hy.1 hq0.le
    linarith
  have hYq : 0 < Y ^ q := Real.rpow_pos_of_pos hY0 q
  have hlam0 : 0 < lam := by linarith
  have hlinv : lam⁻¹ ≤ 2 * Y ^ (-q) := by
    rw [Real.rpow_neg hY0.le]
    calc lam⁻¹ ≤ (Y ^ q / 2)⁻¹ := inv_anti₀ (by positivity) hlamY
      _ = 2 * (Y ^ q)⁻¹ := by field_simp
  have hlinv0 : 0 ≤ lam⁻¹ := (inv_pos.mpr hlam0).le
  set b := Cv * Y ^ (-beta S.p) with hb
  have hb0 : 0 ≤ b := by positivity
  obtain ⟨-, -, -, h3⟩ := hvb ε μ R Y htv y hy
  have hv3 := h3 (res_vY S.p R ε μ Y) (by simp)
  have hP3 := h3 (c05_plane_wave S.p R ε μ y) (by simp)
  have hbd : ∀ h : ℝ → ℝ, (∀ s : ℝ,
      |c05_plane_wave_Delta h y s| ≤ Cv * Y ^ (-beta S.p) * min |s| lam⁻¹ ∧
      |c05_plane_wave_Delta (deriv h) y s| ≤ Cv * Y ^ (-beta S.p) * min 1 (lam * |s|) ∧
      |c05_plane_wave_Delta (deriv (deriv h)) y s| ≤
        Cv * Y ^ (-beta S.p) * lam * min 1 (lam * |s|)) → ∀ s : ℝ,
      |c05_plane_wave_Delta h y s| ≤ b * lam⁻¹ ∧ |c05_plane_wave_Delta (deriv h) y s| ≤ b ∧
      |c05_plane_wave_Delta (deriv (deriv h)) y s| ≤ b * lam := by
    intro h hh s
    obtain ⟨e1, e2, e3⟩ := hh s
    refine ⟨e1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hb0), ?_, ?_⟩
    · exact e2.trans (by
        calc b * min 1 (lam * |s|) ≤ b * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hb0
          _ = b := mul_one b)
    · exact e3.trans (by
        calc b * lam * min 1 (lam * |s|) ≤ b * lam * 1 :=
              mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
          _ = b * lam := mul_one _)
  have hvB := hbd _ hv3
  have hPB := hbd _ hP3
  have hNb : ∀ s, |c05_plane_wave_N0 S.p R ε μ Y y s| ≤ 2 * b * (b * lam⁻¹) ^ 2 ∧
      |c05_plane_wave_N1 S.p R ε μ Y y s| ≤
        2 * (b * lam) * (b * lam⁻¹) ^ 2 + 4 * b ^ 2 * (b * lam⁻¹) := fun s =>
    c05_aux_N_bounds (hvB s).1 (hPB s).1 (hvB s).2.1 (hPB s).2.1 (hvB s).2.2 (hPB s).2.2
  -- measurability
  have hvm : Measurable (res_vY S.p R ε μ Y) := (hmeas ε μ R Y htm).1
  have hPm : Measurable (c05_plane_wave S.p R ε μ y) := (c05_aux_plane_wave_cont _ _ _ _ _).measurable
  have hN0m : Measurable (c05_plane_wave_N0 S.p R ε μ Y y) :=
    (c05_aux_N_meas _ _ hvm hPm y).1
  have hN1m : Measurable (c05_plane_wave_N1 S.p R ε μ Y y) :=
    (c05_aux_N_meas _ _ hvm hPm y).2
  -- the kernel integral
  obtain ⟨-, -, -, -, hI, hV⟩ := c05_cubic_kernel_integrals S.p 1 (Y / 4) hp0 S.hp_hi one_pos
    (by positivity)
  obtain ⟨hI0, hB0⟩ := c05_aux_far_integral S.p (Y / 4) _ _ hN0m (fun s => (hNb s).1) hI hV
  obtain ⟨hI1, hB1⟩ := c05_aux_far_integral S.p (Y / 4) _ _ hN1m (fun s => (hNb s).2) hI hV
  -- numerics
  have hK : |c05_plane_wave_K S.p ε| = Kc * ε := by
    unfold c05_plane_wave_K
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < S.p + 1),
      abs_of_nonneg hε, abs_two]
    ring
  have hb3 : b ^ 3 = Cv ^ 3 * Y ^ (-beta S.p * 3) := by
    rw [hb, mul_pow, ← Real.rpow_mul_natCast hY0.le]; norm_num
  have hY4 : (Y / 4) ^ (-S.p - 2) = 4 ^ (S.p + 2) * Y ^ (-S.p - 2) := by
    rw [Real.div_rpow hY0.le (by norm_num), show -S.p - 2 = -(S.p + 2) by ring,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    field_simp
  have hl2 : lam⁻¹ ^ 2 ≤ 4 * Y ^ (-q * 2) := by
    rw [show -q * 2 = -q * ((2 : ℕ) : ℝ) by norm_num, Real.rpow_mul_natCast hY0.le]
    calc lam⁻¹ ^ 2 ≤ (2 * Y ^ (-q)) ^ 2 := pow_le_pow_left₀ hlinv0 hlinv 2
      _ = 4 * (Y ^ (-q)) ^ 2 := by ring
  have hYn : 0 ≤ Y ^ (-S.p - 2) := by positivity
  have hYb : 0 ≤ Y ^ (-beta S.p * 3) := by positivity
  have hYe0 : Y ^ (-beta S.p * 3) * Y ^ (-q * 2) * Y ^ (-S.p - 2) ≤ Y ^ (1 - 5 * beta S.p) := by
    rw [← Real.rpow_add hY0, ← Real.rpow_add hY0]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith only [h2β, hq0, hp0])
  have hYe1 : Y ^ (-beta S.p * 3) * Y ^ (-q) * Y ^ (-S.p - 2) ≤ Y ^ (1 - 5 * beta S.p + q) := by
    rw [← Real.rpow_add hY0, ← Real.rpow_add hY0]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith only [h2β, hq0, hp0])
  have hYt0 : 0 ≤ Y ^ (1 - 5 * beta S.p) := by positivity
  have hYt1 : 0 ≤ Y ^ (1 - 5 * beta S.p + q) := by positivity
  refine ⟨hI0, ?_, hI1, ?_⟩
  · rw [hK]
    calc Kc * ε * (∫ s in {s : ℝ | Y / 4 ≤ |s|}, |s| ^ (-S.p - 3) *
          |c05_plane_wave_N0 S.p R ε μ Y y s|)
        ≤ Kc * ε * (2 * b * (b * lam⁻¹) ^ 2 * (2 / (S.p + 2) * (Y / 4) ^ (-S.p - 2))) := by
          gcongr
      _ = Kc * ε * 2 * b ^ 3 * lam⁻¹ ^ 2 * (2 / (S.p + 2)) * (Y / 4) ^ (-S.p - 2) := by ring
      _ ≤ Kc * ε * 2 * (Cv ^ 3 * Y ^ (-beta S.p * 3)) * (4 * Y ^ (-q * 2)) * (2 / (S.p + 2)) *
            (4 ^ (S.p + 2) * Y ^ (-S.p - 2)) := by
          rw [hb3, hY4]; gcongr
      _ = C0f * ε * (Y ^ (-beta S.p * 3) * Y ^ (-q * 2) * Y ^ (-S.p - 2)) := by
          rw [hC0f]; ring
      _ ≤ C0f * ε * Y ^ (1 - 5 * beta S.p) := by gcongr
      _ ≤ (C0f + C1f + 1) * ε * Y ^ (1 - 5 * beta S.p) := by
          gcongr; linarith
  · rw [hK]
    have hB1' : 2 * (b * lam) * (b * lam⁻¹) ^ 2 + 4 * b ^ 2 * (b * lam⁻¹) = 6 * b ^ 3 * lam⁻¹ := by
      field_simp; ring
    calc Kc * ε * (∫ s in {s : ℝ | Y / 4 ≤ |s|}, |s| ^ (-S.p - 3) *
          |c05_plane_wave_N1 S.p R ε μ Y y s|)
        ≤ Kc * ε * ((2 * (b * lam) * (b * lam⁻¹) ^ 2 + 4 * b ^ 2 * (b * lam⁻¹)) *
            (2 / (S.p + 2) * (Y / 4) ^ (-S.p - 2))) := by
          gcongr
      _ = Kc * ε * 6 * b ^ 3 * lam⁻¹ * (2 / (S.p + 2)) * (Y / 4) ^ (-S.p - 2) := by
          rw [hB1']; ring
      _ ≤ Kc * ε * 6 * (Cv ^ 3 * Y ^ (-beta S.p * 3)) * (2 * Y ^ (-q)) * (2 / (S.p + 2)) *
            (4 ^ (S.p + 2) * Y ^ (-S.p - 2)) := by
          rw [hb3, hY4]; gcongr
      _ = C1f * ε * (Y ^ (-beta S.p * 3) * Y ^ (-q) * Y ^ (-S.p - 2)) := by
          rw [hC1f]; ring
      _ ≤ C1f * ε * Y ^ (1 - 5 * beta S.p + q) := by gcongr
      _ ≤ (C0f + C1f + 1) * ε * Y ^ (1 - 5 * beta S.p + q) := by
          gcongr; linarith

/-- Blueprint: prop:approx_E5_cubic.  On `[Y,2Y]`, `j = 0,1`:
`|∂_y^j ℛ_cub(y)| ≤ Cε⟨y⟩^{1-5β+j/p}` and `|∂_y^j ℰ₅(y)| ≤ Cε⟨y⟩^{-2p-1+j/p}`. -/
theorem approx_E5_cubic (S : c05_standing) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, ∀ μ : ℂ, ∀ R Y : ℝ, c05_standing_tuple S R₀ ε μ R Y →
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (c05_E5_remainders_Rcub S.p R ε μ Y) y| ≤
              C * ε * jb y ^ (1 - 5 * beta S.p + j / S.p) ∧
            |iteratedDeriv j (fun t => residual_decomposition_E5 S.p R ε μ Y t) y| ≤
              C * ε * jb y ^ (-2 * S.p - 1 + j / S.p) := by
  obtain ⟨R1, hR1, hrep⟩ := c05_cubic_remainder_representation S
  obtain ⟨R2, hR2, C2, hC2, hnear⟩ := c05_cubic_near S
  obtain ⟨R3, hR3, C3, hC3, hfar⟩ := c05_cubic_far S
  obtain ⟨R4, hR4, C4, hC4, hpar⟩ := c05_plane_wave_parameter S
  obtain ⟨R5, hR5, hsplit⟩ := c05_E5_split S
  obtain ⟨R6, hR6, C6, hC6, hlin⟩ := approx_E5_linear S
  have hp0 : 0 < S.p := by linarith [S.hp_lo]
  set R₀ := max (max (max R1 R2) (max R3 R4)) (max R5 R6) with hR₀
  have h1 : R1 ≤ R₀ := by simp [hR₀]
  have h2 : R2 ≤ R₀ := by simp [hR₀]
  have h3 : R3 ≤ R₀ := by simp [hR₀]
  have h4 : R4 ≤ R₀ := by simp [hR₀]
  have h5 : R5 ≤ R₀ := by simp [hR₀]
  have h6 : R6 ≤ R₀ := by simp [hR₀]
  set T := |1 - 5 * beta S.p| + 1 / S.p
  refine ⟨R₀, hR1.trans h1, 3 ^ T * (C2 + C3 + C4) + C6, by positivity, ?_⟩
  intro ε μ R Y ht y hy j hj
  have hε : 0 ≤ ε := ht.1
  have hR : 1 ≤ R := (hR1.trans h1).trans ht.2.2.2.1
  have hY : 1 ≤ Y := by linarith [ht.2.2.2.2]
  have hyY : Y ≤ y := hy.1
  have hy2R : 2 * R < y := by linarith [ht.2.2.2.2]
  obtain ⟨hRC1, hrepy⟩ := hrep ε μ R Y (c05_aux_tuple_mono h1 ht)
  obtain ⟨hi0, hi1, hval, hval', hder⟩ := hrepy y hy
  obtain ⟨-, hn0, -, hn1⟩ := hnear ε μ R Y (c05_aux_tuple_mono h2 ht) y hy
  obtain ⟨-, hf0, -, hf1⟩ := hfar ε μ R Y (c05_aux_tuple_mono h3 ht) y hy
  obtain ⟨-, hpar'⟩ := hpar ε μ R Y (c05_aux_tuple_mono h4 ht)
  obtain ⟨hTG, hexp⟩ := hpar' y hy
  have hjb1 : 1 ≤ jb y := by linarith [(c05_aux_jb_bounds hY hy).1]
  -- the bound on `ℛ_cub` in terms of `Y`
  have hcubY : |iteratedDeriv j (c05_E5_remainders_Rcub S.p R ε μ Y) y| ≤
      (C2 + C3 + C4) * ε * Y ^ (1 - 5 * beta S.p + j / S.p) := by
    have hYpos : 0 ≤ Y ^ (1 - 5 * beta S.p + j / S.p) := Real.rpow_nonneg (by linarith) _
    interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at hn0 hf0 hYpos ⊢
      rw [hval, hval']
      have := c05_aux_kernel_split (c05_plane_wave_K S.p ε) (-S.p - 3) (Y / 4) _ hi0
      have hC4e : 0 ≤ C4 * ε * Y ^ (1 - 5 * beta S.p) := by positivity
      linarith only [this, hn0, hf0, hC4e]
    · simp only [iteratedDeriv_one, Nat.cast_one] at hn1 hf1 hYpos ⊢
      rw [hder]
      have := c05_aux_kernel_split (c05_plane_wave_K S.p ε) (-S.p - 3) (Y / 4) _ hi1
      rw [hexp] at hTG
      have := abs_add_le (c05_plane_wave_K S.p ε *
          ∫ s, |s| ^ (-S.p - 3) * c05_plane_wave_N1 S.p R ε μ Y y s)
        (c05_plane_wave_TP S.p R ε μ y - deriv (c05_plane_wave_G S.p R ε μ) y)
      linarith only [this, ‹|c05_plane_wave_K S.p ε * _| ≤ _›, hn1, hf1, hTG]
  have hcub : |iteratedDeriv j (c05_E5_remainders_Rcub S.p R ε μ Y) y| ≤
      3 ^ T * (C2 + C3 + C4) * ε * jb y ^ (1 - 5 * beta S.p + j / S.p) := by
    have hθ : |1 - 5 * beta S.p + j / S.p| ≤ T := by
      have hj' : (j : ℝ) / S.p ≤ 1 / S.p := by
        gcongr; exact_mod_cast hj
      have hj0 : 0 ≤ (j : ℝ) / S.p := by positivity
      calc |1 - 5 * beta S.p + j / S.p| ≤ |1 - 5 * beta S.p| + |(j : ℝ) / S.p| := abs_add_le _ _
        _ ≤ T := by rw [abs_of_nonneg hj0]; linarith
    have := c05_aux_rpow_Y_jb hY hy hθ
    calc _ ≤ (C2 + C3 + C4) * ε * Y ^ (1 - 5 * beta S.p + j / S.p) := hcubY
      _ ≤ (C2 + C3 + C4) * ε * (3 ^ T * jb y ^ (1 - 5 * beta S.p + j / S.p)) := by gcongr
      _ = _ := by ring
  have hjbnn : 0 ≤ jb y ^ (1 - 5 * beta S.p + j / S.p) := Real.rpow_nonneg (by linarith) _
  have hjbnn' : 0 ≤ jb y ^ (-2 * S.p - 1 + j / S.p) := Real.rpow_nonneg (by linarith) _
  have h5β : 1 - 5 * beta S.p + j / S.p ≤ -2 * S.p - 1 + j / S.p := by
    have : 2 + 2 * S.p ≤ 5 * beta S.p := c05_aux_five_beta S.p hp0 S.hp_hi
    linarith
  have hjbmono : jb y ^ (1 - 5 * beta S.p + j / S.p) ≤ jb y ^ (-2 * S.p - 1 + j / S.p) :=
    Real.rpow_le_rpow_of_exponent_le hjb1 h5β
  have hCc : 0 ≤ 3 ^ T * (C2 + C3 + C4) := by positivity
  refine ⟨?_, ?_⟩
  · calc _ ≤ 3 ^ T * (C2 + C3 + C4) * ε * jb y ^ (1 - 5 * beta S.p + j / S.p) := hcub
      _ ≤ (3 ^ T * (C2 + C3 + C4) + C6) * ε * jb y ^ (1 - 5 * beta S.p + j / S.p) := by
        gcongr; linarith
  -- `ℰ₅ = ℛ_lin + ℛ_cub` near `y`
  obtain ⟨hlinC, hlinb⟩ := hlin ε μ R Y (c05_aux_tuple_mono h6 ht) y hy
  have hev : (fun t => residual_decomposition_E5 S.p R ε μ Y t) =ᶠ[nhds y]
      fun t => c05_E5_remainders_Rlin S.p R ε μ t + c05_E5_remainders_Rcub S.p R ε μ Y t := by
    filter_upwards [isOpen_Ioi.mem_nhds (show y ∈ Ioi (2 * R) from hy2R)] with t ht'
    exact (hsplit ε μ R Y (c05_aux_tuple_mono h5 ht) t ht').1
  have hsum : iteratedDeriv j (fun t => residual_decomposition_E5 S.p R ε μ Y t) y =
      iteratedDeriv j (c05_E5_remainders_Rlin S.p R ε μ) y +
        iteratedDeriv j (c05_E5_remainders_Rcub S.p R ε μ Y) y := by
    interval_cases j
    · simp only [iteratedDeriv_zero]; exact hev.eq_of_nhds
    · simp only [iteratedDeriv_one]
      rw [hev.deriv_eq]
      have hdl : DifferentiableAt ℝ (c05_E5_remainders_Rlin S.p R ε μ) y :=
        hlinC.differentiableAt one_ne_zero
      have hdc : DifferentiableAt ℝ (c05_E5_remainders_Rcub S.p R ε μ Y) y :=
        ((hRC1.contDiffAt (isOpen_Ioi.mem_nhds (show y ∈ Ioi R by
          simp only [mem_Ioi]; linarith))).differentiableAt one_ne_zero)
      exact deriv_add hdl hdc
  rw [hsum]
  have hl := hlinb j hj
  calc _ ≤ |iteratedDeriv j (c05_E5_remainders_Rlin S.p R ε μ) y| +
        |iteratedDeriv j (c05_E5_remainders_Rcub S.p R ε μ Y) y| := abs_add_le _ _
    _ ≤ C6 * ε * jb y ^ (-2 * S.p - 1 + j / S.p) +
        3 ^ T * (C2 + C3 + C4) * ε * jb y ^ (-2 * S.p - 1 + j / S.p) := by
      gcongr
      exact hcub.trans (by gcongr)
    _ = _ := by ring

end GSQG
