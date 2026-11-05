import GSQG.Definitions

/-!
# Beyond the paper (2D patch derivation): fixed data for the 2D patch equation (blueprint ch. 13)

Blueprint `13_patch_equation.tex`: def:c13_kernel_data, def:c13_normalization, def:c13_graph_data.
The plane is `E = EuclideanSpace ℝ (Fin 2)` with its Euclidean norm and standard volume; points
are built with `c13_pt x y = !₂[x, y]` (coordinate `0` is `x`, coordinate `1` is `y`).
These are total formulas; convergence and analytic meaning are separate lemmas. In particular the
unsubtracted integral `P * θ` is never asserted to converge for an infinite patch.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-- The Euclidean plane used in chapter 13. -/
abbrev c13_E := EuclideanSpace ℝ (Fin 2)

/-- Chapter 13 (local).  The point `(x, y)` of the Euclidean plane. -/
def c13_pt (x y : ℝ) : c13_E := !₂[x, y]

/-! ### def:c13_kernel_data -/

/-- Blueprint: def:c13_kernel_data.  The rotation `J(x, y) = (-y, x)`. -/
def c13_rotation (z : c13_E) : c13_E := !₂[-(z 1), z 0]

/-- Blueprint: def:c13_kernel_data.  `P_{α,c}(z) = c|z|^{-α}` for `z ≠ 0`, and `0` at `z = 0`. -/
def c13_potential_kernel (α c : ℝ) (z : c13_E) : ℝ :=
  if z = 0 then 0 else c * ‖z‖ ^ (-α)

/-- Blueprint: def:c13_kernel_data.  `K_{α,c}(z) = α c J z |z|^{-α-2} = -J∇P_{α,c}(z)` for
`z ≠ 0`, and `0` at `z = 0`. -/
def c13_velocity_kernel (α c : ℝ) (z : c13_E) : c13_E :=
  if z = 0 then 0 else (α * c * ‖z‖ ^ (-α - 2)) • c13_rotation z

/-- Blueprint: def:c13_kernel_data.  The cancellation (adjoint) operator on vector tests,
`B*_{α,c}Φ(Y) = ∫ K_{α,c}(z) · (Φ(Y+z) - Φ(Y)) dz`. -/
def c13_adjoint (α c : ℝ) (Φ : c13_E → c13_E) (Y : c13_E) : ℝ :=
  ∫ z, inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y)

/-- Blueprint: def:c13_kernel_data.  The renormalized potential
`V_{α,c}[θ](X) = ∫ [P_{α,c}(X-Y) - 1_{|Y|>1} P_{α,c}(-Y)] θ(Y) dY`. -/
def c13_renormalized_potential (α c : ℝ) (θ : c13_E → ℝ) (X : c13_E) : ℝ :=
  ∫ Y, (c13_potential_kernel α c (X - Y) -
      (if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y

/-! ### def:c13_normalization -/

/-- Blueprint: def:c13_normalization.  `A_α = 2^{2-α} π Γ(1-α/2) / Γ(α/2)`. -/
def c13_riesz_factor (α : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 - α) * π * Real.Gamma (1 - α / 2) / Real.Gamma (α / 2)

/-- Blueprint: def:c13_normalization.  The canonical coefficient `c_std = A_α⁻¹`. -/
def c13_standard_coefficient (α : ℝ) : ℝ := (c13_riesz_factor α)⁻¹

/-- Blueprint: def:c13_normalization.  `κ_α = c_front / c_std` with `c_front = calpha (α - 1)`,
the coefficient of the existing front equation. -/
def c13_time_ratio (α : ℝ) : ℝ := calpha (α - 1) / c13_standard_coefficient α

/-! ### def:c13_graph_data -/

/-- Blueprint: def:c13_graph_data.  `F : ℝ → I → ℝ` (written `F x t`) is admissible on the
nonempty open time interval `I`: jointly smooth, with `F_x` bounded on `ℝ × J₀` for every compact
`J₀ ⊆ I`. No bound on `F`, `F_xx` or time derivatives at spatial infinity is assumed. -/
def c13_graph_class (I : Set ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  -- Joint smoothness is required only on `ℝ × I` (the self-similar family has curvature blowing
  -- up at the end of `I`); `univ ×ˢ I` is open.
  IsOpen I ∧ I.Nonempty ∧ ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I) ∧
    ∀ J₀ ⊆ I, IsCompact J₀ → ∃ M, 0 ≤ M ∧ ∀ x, ∀ t ∈ J₀, |deriv (fun x => F x t) x| ≤ M

/-- Blueprint: def:c13_graph_data.  The lower patch `Ω_t = {(x, y) : y < F(x, t)}`; its indicator
is `θ_F`. -/
def c13_patch (F : ℝ → ℝ → ℝ) (t : ℝ) : Set c13_E := {X | X 1 < F (X 0) t}

/-- Blueprint: def:c13_graph_data.  The candidate contour velocity
`U_{α,c}[F](X, t) = -c ∫ τ_t(s) |X - γ_t(s)|^{-α} ds` off the graph, with `γ_t(s) = (s, F(s,t))`
and `τ_t(s) = (1, F_x(s,t))`; value `0` on the graph. Not assumed to satisfy the 2D velocity law. -/
def c13_graph_velocity (α c : ℝ) (F : ℝ → ℝ → ℝ) (X : c13_E) (t : ℝ) : c13_E :=
  if X 1 = F (X 0) t then 0 else
    (-c) • ∫ s : ℝ, (‖X - c13_pt s (F s t)‖ ^ (-α)) •
      c13_pt 1 (deriv (fun x => F x t) s)

/-- Blueprint: def:c13_graph_data.  `W_{α,c}[F](x, t) = c ∫ [F_x(x,t) - F_x(s,t)] |γ_t(x) - γ_t(s)|^{-α} ds`,
the normal velocity times `√(1 + F_x²)`. -/
def c13_normal_speed (α c : ℝ) (F : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  c * ∫ s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) *
    ‖c13_pt x (F x t) - c13_pt s (F s t)‖ ^ (-α)

end GSQG
