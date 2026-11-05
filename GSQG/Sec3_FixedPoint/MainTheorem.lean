import GSQG.Sec1_Introduction.SelfSimilarReduction
import GSQG.Sec3_FixedPoint.FixedPointArgument
import GSQG.Sec4_Analysis.Equation
import GSQG.AppendixAB.Statements
import GSQG.Sec4_Analysis.Smoothness
import GSQG.Sec5_ApproximateSolution.FamilyAndE1toE4
import GSQG.Sec5_ApproximateSolution.E5
import GSQG.Sec5_ApproximateSolution.E6toE9
import GSQG.Sec5_ApproximateSolution.ResidualBounds
import GSQG.Sec6_LinearInverse.ConjugationAndLowFrequency
import GSQG.Sec6_LinearInverse.HighFrequency
import GSQG.Sec7_NonlinearEstimates.NonlinearEstimates

/-!
# Final assembly

Declarations that depend on several chapters and therefore come last in the import graph:

* chapter 02: the three backbone theorems `fixed_point_approximation`,
  `fixed_point_linear_inverse`, `fixed_point_nonlinear_estimates`, proved by the chapter
  assemblies `approx_assembly` (ch07), `linear_inverse_assembly` (ch09) and
  `nonlinear_assembly` (ch10); and `fixed_point_correction`, assembled from them;
* chapter 01: the tail `c01_profile_from_correction`, `c01_profile_smooth`,
  `c01_profile_bounds`, `c01_aux_main_allT`, `main`, `c01_desingularization`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology NNReal Interval FourierTransform ComplexConjugate

noncomputable section

namespace GSQG

/-! ### The three main theorems -/

/-- Blueprint: thm:fixed_point_approximation.  Existence of approximate solutions: the family
`f̄_{ε,μ} = approximate_solution_family p R ε μ` satisfies items (0)–(4) of
`fixed_point_approximation_statement`, with constants uniform in `ε ∈ [0,ε₀]`, `μ ∈ B̄`. -/
theorem fixed_point_approximation (P : parameters) :
    ∃ R₀ > 0, ∃ δ₀ > 0, ∀ R ≥ R₀, ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ ε₀ > 0, fixed_point_approximation_statement P R δ ε₀ :=
  approx_assembly P

/-- Blueprint: thm:fixed_point_linear_inverse.  The linear inverse theorem: items (1)–(4) of
`fixed_point_linear_inverse_statement` for the shared objects `ell`, `T_0`, `U_eps`, `V_eps`. -/
theorem fixed_point_linear_inverse (P : parameters) :
    ∃ ε₀ > 0, ∀ δ > 0, fixed_point_linear_inverse_statement P δ ε₀ :=
  linear_inverse_assembly P

/-- Blueprint: thm:fixed_point_nonlinear_estimates.  Nonlinear estimates for `𝒩_{ε,f̄_{ε,μ}}`
(items of `fixed_point_nonlinear_estimates_statement`), uniform in `ε, μ`. -/
theorem fixed_point_nonlinear_estimates (P : parameters) :
    ∃ R₀ > 0, ∃ δ₀ > 0, ∀ R ≥ R₀, ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ ε₀ > 0, fixed_point_nonlinear_estimates_statement P R δ ε₀ :=
  nonlinear_assembly P


/-! ### Existence of the correction (assembly) -/

/-- Blueprint: thm:fixed_point_correction.  Existence of the correction: (for all `R ≥ R₀`,
`δ ∈ (0,δ₀]`) there are `ε₁ > 0` (in the range of thm:fixed_point_approximation) and `C > 0` such
that for every `ε ∈ [0,ε₁]` there are `μ_ε ∈ B̄` and `r_ε ∈ X_{γ₂}` with
`ℒ_ε(r_ε) = -ℰ_ε(f̄_{ε,μ_ε}) - 𝒩_{ε,f̄_{ε,μ_ε}}(r_ε)` on `ℝ` and `|μ_ε - μ_*| + ‖r_ε‖_{X_{γ₂}} ≤ C ε`. -/
theorem fixed_point_correction (P : parameters) :
    ∃ R₀ > 0, ∃ δ₀ > 0, ∀ R ≥ R₀, ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ ε₁ > 0, fixed_point_approximation_statement P R δ ε₁ ∧
        ∃ C > 0, ∀ ε ∈ Icc 0 ε₁, ∃ μ ∈ Bbar P.p δ, ∃ r ∈ X_gamma P.p P.γ₂,
          (∀ y, L_eps P.p ε r y = -residual P.p ε (approximate_solution_family P.p R ε μ) y -
            N_eps P.p ε (approximate_solution_family P.p R ε μ) r y) ∧
          ‖μ - mu_star P.p‖ + xNorm P.p P.γ₂ r ≤ C * ε := by
  obtain ⟨R₁, hR₁, δ₁, hδ₁, hA⟩ := fixed_point_approximation P
  obtain ⟨εL, hεL, hL⟩ := fixed_point_linear_inverse P
  obtain ⟨R₂, -, δ₂, hδ₂, hN⟩ := fixed_point_nonlinear_estimates P
  refine ⟨max R₁ R₂, lt_max_of_lt_left hR₁, min δ₁ δ₂, lt_min hδ₁ hδ₂,
    fun R hR δ hδ hδle => ?_⟩
  obtain ⟨εA, hεA, hAs⟩ := hA R (le_of_max_le_left hR) δ hδ (hδle.trans (min_le_left _ _))
  obtain ⟨εN, hεN, hNs⟩ := hN R (le_of_max_le_right hR) δ hδ (hδle.trans (min_le_right _ _))
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ, ε₀ = min εA (min εL εN) := ⟨_, rfl⟩
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; exact lt_min hεA (lt_min hεL hεN)
  have hS : c02_forcing_map_setting P R δ ε₀ :=
    ⟨hδ, hε₀, c02_aux_approx_mono hAs (by rw [hε₀def]; exact min_le_left _ _),
      c02_aux_linear_mono (hL δ hδ)
        (by rw [hε₀def]; exact (min_le_right _ _).trans (min_le_left _ _)),
      c02_aux_nonlinear_mono hNs
        (by rw [hε₀def]; exact (min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨CR, -, C₀, hC₀, ε₂, hε₂, hε₂le, hH⟩ := c02_H_contraction P hS
  obtain ⟨Cs, hCs, hK1, hK2⟩ := c02_K_self_map P hS hC₀ hε₂le hH
  obtain ⟨CUV, hCUV, hUVb⟩ := hS.2.2.2.1.2.2.2.1 P.γ₂ (c02_aux_adm₂ P)
  refine ⟨min ε₂ (δ / Cs), lt_min hε₂ (div_pos hδ hCs),
    c02_aux_approx_mono hS.2.2.1 ((min_le_left _ _).trans hε₂le), Cs + CUV * C₀, by positivity,
    fun ε hε => ?_⟩
  have hε2 : ε ∈ Icc 0 ε₂ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεε₀ : ε ∈ Icc 0 ε₀ := ⟨hε.1, hε2.2.trans hε₂le⟩
  obtain ⟨-, hKc⟩ := c02_K_continuity P hS hC₀ hε₂le hH hε2
  obtain ⟨μ, hμ, hfix⟩ := c02_brouwer_disc (mu_star P.p) hδ _ hKc (hK2 ε hε)
  have hℓ := (c02_K_map_fixed_iff P R ε μ (C₀ * ε)).1 hfix
  obtain ⟨-, hwB, hwH, hwn⟩ := c02_w_exists P hS hC₀ hε₂le hH hε2 hμ
  obtain ⟨hr, heq⟩ := c02_system_implies_correction P hS hεε₀ hμ (c02_aux_adm₂ P) hwB.1
    hwH.symm hℓ
  refine ⟨μ, hμ, U_eps_inv P.p ε (c02_K_map_w P R ε μ (C₀ * ε)), hr, heq, ?_⟩
  have h1 := (hK1 ε hε2 μ hμ).2
  rw [hfix] at h1
  have h2 := ((hUVb ε hεε₀).1 _ hwB.1).2.2.2
  have h3 := mul_le_mul_of_nonneg_left hwn hCUV.le
  nlinarith


/-! ### Chapter 01: from the correction to the main theorem -/

-- Encoding: "μ_ε, r_ε given by thm:fixed_point_correction" and "f̄ by
-- thm:fixed_point_approximation" are chapter-02 objects; we existentially fix the parameters
-- `R, δ, ε₁` of the family (with the properties of thm:fixed_point_approximation, packaged as
-- `c01_approx_family_good`) and the constant `C₀` of the correction bound, assert existence of
-- the correction data `(μ_ε, r_ε)` (`c01_correction_data`) for `0 < ε < ε₁`, and prove the
-- conclusions for every such data.
/-- Blueprint: lem:c01_profile_from_correction.  For `0 < ε < ε₁`, `f_ε = f̄_{ε,μ_ε} + r_ε` lies
in `𝒜`, satisfies `ℰ_ε(f_ε) ≡ 0`, `|f_ε''| ≤ C⟨y⟩^{1/p}` a.e. (`C` independent of `ε`),
`f_ε' → -1` at `-∞`, `f_ε → 0` at `+∞`; so it solves the profile equation. -/
theorem c01_profile_from_correction (P : parameters) :
    ∃ R δ ε₁ C₀ : ℝ, 0 < C₀ ∧ c01_approx_family_good P.p R δ ε₁ ∧
      (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ (μ : ℂ) (r : ℝ → ℝ), c01_correction_data P R δ C₀ ε μ r) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ (μ : ℂ) (r : ℝ → ℝ),
        c01_correction_data P R δ C₀ ε μ r →
        let f := approximate_solution_family P.p R ε μ + r
        f ∈ c01_admissible_class ∧ (∀ y, residual P.p ε f y = 0) ∧
        (∀ᵐ y, |deriv (deriv f) y| ≤ C * jb y ^ (1 / P.p)) ∧
        Tendsto (deriv f) atBot (𝓝 (-1)) ∧ Tendsto f atTop (𝓝 0) ∧
        profile_equation P.p ε f := by
  obtain ⟨R₀, _, δ₀, hδ₀, h⟩ := fixed_point_correction P
  obtain ⟨ε₁, hε₁, hstmt, C₀, hC₀, hex⟩ := h R₀ le_rfl δ₀ hδ₀ le_rfl
  have hgood : c01_approx_family_good P.p R₀ δ₀ ε₁ := by
    obtain ⟨-, h0, h1, h2, -⟩ := hstmt
    refine ⟨hδ₀, hε₁, fun ε hε μ hμ => ⟨h0 ε hε μ hμ, (h1 ε hε μ hμ).1, (h1 ε hε μ hμ).2⟩,
      fun j => ?_⟩
    obtain ⟨C, -, hC⟩ := h2 j
    exact ⟨C, fun ε hε μ hμ y => ⟨fun hy => (hC ε hε μ hμ).1 y hy, fun hy => (hC ε hε μ hμ).2 y hy⟩⟩
  refine ⟨R₀, δ₀, ε₁, C₀, hC₀, hgood, fun ε hε hε1 => ?_,
    c01_aux_profile_props P R₀ δ₀ ε₁ C₀ hgood⟩
  obtain ⟨μ, hμ, r, hr, heq, hb⟩ := hex ε ⟨hε.le, hε1.le⟩
  exact ⟨μ, r, hμ, hr, heq, hb⟩

-- Encoding: stated for every family satisfying `c01_approx_family_good` and every
-- correction data (see the note on `c01_profile_from_correction`).  "The a.e. bounds on `r''`
-- coming from `X_{γ₂}` hold everywhere" is stated as: the `X_{γ₂}` weights (`y ≥ 0` and `y ≤ 0`
-- parts) are bounded by `‖r‖_{X_{γ₂}}` at every point.
/-- Blueprint: lem:c01_profile_smooth.  The profile `f_ε = f̄_{ε,μ_ε} + r_ε` is `C^∞`; hence
`r_ε ∈ C^∞` and the `X_{γ₂}` bounds on `r_ε''` hold everywhere. -/
theorem c01_profile_smooth (P : parameters) (R δ ε₁ C₀ : ℝ)
    (hgood : c01_approx_family_good P.p R δ ε₁) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < ε₁)
    (μ : ℂ) (r : ℝ → ℝ) (hdata : c01_correction_data P R δ C₀ ε μ r) :
    ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family P.p R ε μ + r) ∧
    ContDiff ℝ (⊤ : ℕ∞) r ∧
    ∀ y : ℝ,
      (0 ≤ y → jb y ^ P.γ₂ * (|r y| + jb y ^ (-1 / P.p) * |deriv r y| +
          jb y ^ (-2 / P.p) * |deriv (deriv r) y|) ≤ xNorm P.p P.γ₂ r) ∧
      (y ≤ 0 → jb y ^ P.γ₂ * (|r y| + jb y * |deriv r y| +
          jb y ^ (2 : ℕ) * |deriv (deriv r) y|) ≤ xNorm P.p P.γ₂ r) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hβ0 : 0 < beta P.p := by unfold beta; positivity
  have hγ := P.hγ₁
  have hγ12 := P.hγ₁₂
  have hεI : ε ∈ Icc 0 ε₁ := ⟨hε.le, hε₁.le⟩
  obtain ⟨Mb, -, hMb⟩ := c01_aux_good_deriv_bound P.p R δ ε₁ hp0 hgood
  have hfb := (hgood.2.2.1 ε hεI μ hdata.1).1
  have hr := hdata.2.1
  obtain ⟨hfs, hrs⟩ := (fixed_point_smoothness P.p hp0 P.hp_hi).2 ε P.γ₂ hε.le
    (by linarith) _ r hfb ⟨Mb, hMb ε hεI μ hdata.1⟩ hr
    (fun y => by have := hdata.2.2.1 y; linarith)
  refine ⟨hfs, hrs, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · have hJ0 : ∀ y, 0 < jb y := fun y => by linarith [c01_aux_one_le_jb y]
    have hJc : ∀ e : ℝ, Continuous (fun y => jb y ^ e) := fun e =>
      c01_aux_jb_cont.rpow_const (fun y => Or.inl (hJ0 y).ne')
    have h1 : Continuous (deriv r) := hrs.continuous_deriv (by simp)
    have h2 : Continuous (deriv (deriv r)) := (hrs.iterate_deriv 2).continuous
    exact c01_aux_ae_to_all _ ((hJc _).mul ((hrs.continuous.abs.add ((hJc _).mul h1.abs)).add
      ((hJc _).mul h2.abs))) _ (Ici 0) (Or.inl rfl) (c01_aux_X_ae_pos P.p P.γ₂ r hr.2) y hy
  · have hJ0 : ∀ y, 0 < jb y := fun y => by linarith [c01_aux_one_le_jb y]
    have hJc : ∀ e : ℝ, Continuous (fun y => jb y ^ e) := fun e =>
      c01_aux_jb_cont.rpow_const (fun y => Or.inl (hJ0 y).ne')
    have h1 : Continuous (deriv r) := hrs.continuous_deriv (by simp)
    have h2 : Continuous (deriv (deriv r)) := (hrs.iterate_deriv 2).continuous
    exact c01_aux_ae_to_all _ ((hJc _).mul ((hrs.continuous.abs.add (c01_aux_jb_cont.mul h1.abs)).add
      ((c01_aux_jb_cont.pow 2).mul h2.abs))) _ (Iic 0) (Or.inr rfl)
      (c01_aux_X_ae_neg P.p P.γ₂ r hr.2) y hy

-- Encoding: as for `c01_profile_smooth` (any family with `c01_approx_family_good`, any
-- correction data with constant `C₀`); `C` depends on the family and `C₀`, not on `ε, μ, r`.
/-- Blueprint: lem:c01_profile_bounds.  There is `C > 0`, independent of `ε ∈ (0,ε₁)`, such that
`f_ε` satisfies the bounds of item (1) of thm:main. -/
theorem c01_profile_bounds (P : parameters) (R δ ε₁ C₀ : ℝ)
    (hgood : c01_approx_family_good P.p R δ ε₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ (μ : ℂ) (r : ℝ → ℝ),
      c01_correction_data P R δ C₀ ε μ r →
      c01_profile_bounds_hold P.p C (approximate_solution_family P.p R ε μ + r) := by
  obtain ⟨_, hε₁, hreg, hC⟩ := id hgood
  obtain ⟨C0, hC0⟩ := hC 0
  obtain ⟨C1, hC1⟩ := hC 1
  obtain ⟨C2, hC2⟩ := hC 2
  set ρm := |C₀| * ε₁ with hρm
  have hρm0 : 0 ≤ ρm := by positivity
  refine ⟨|C0| + |C1| + |C2| + ρm + 1, by positivity, fun ε hε hε1 μ r hdata => ?_⟩
  obtain ⟨-, hrs, hw⟩ := c01_profile_smooth P R δ ε₁ C₀ hgood ε hε hε1 μ r hdata
  have hεI : ε ∈ Icc 0 ε₁ := ⟨hε.le, hε1.le⟩
  have hfb : ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family P.p R ε μ) :=
    (hreg ε hεI μ hdata.1).1
  have hC0 := hC0 ε hεI μ hdata.1
  have hC1 := hC1 ε hεI μ hdata.1
  have hC2 := hC2 ε hεI μ hdata.1
  set fb := approximate_solution_family P.p R ε μ with hfbdef
  set ρ := xNorm P.p P.γ₂ r with hρdef
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hρ : ρ ≤ ρm := by
    have h := hdata.2.2.2
    have h1 : ρ ≤ C₀ * ε := by linarith [norm_nonneg (μ - mu_star P.p)]
    calc ρ ≤ C₀ * ε := h1
      _ ≤ |C₀| * ε := mul_le_mul_of_nonneg_right (le_abs_self _) hε.le
      _ ≤ |C₀| * ε₁ := mul_le_mul_of_nonneg_left hε1.le (abs_nonneg _)
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hβ0 : 0 < beta P.p := by unfold beta; positivity
  have hinvp : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith [P.hp_hi]
  have hγ := P.hγ₁
  have hγ12 := P.hγ₁₂
  have hp1 := P.hp_hi
  have hJ1 : ∀ y, 1 ≤ jb y := c01_aux_one_le_jb
  have hX : ∀ y (a : ℝ), 0 ≤ jb y ^ a := fun y a => Real.rpow_nonneg (by linarith [hJ1 y]) a
  have hd0 : iteratedDeriv 0 r = r := iteratedDeriv_zero
  have hd1 : iteratedDeriv 1 r = deriv r := iteratedDeriv_one
  have hd2 : iteratedDeriv 2 r = deriv (deriv r) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  -- pointwise bounds on `r` for `y ≤ 0`
  have hrneg : ∀ y, y ≤ 0 → ∀ j : ℕ, j ≤ 2 →
      |iteratedDeriv j r y| ≤ ρ * jb y ^ (-P.p - (j : ℝ)) := by
    intro y hy j hj
    have hW := (hw y).2 hy
    have hJγ : 0 ≤ jb y ^ P.γ₂ := hX y _
    have hJ0 : 0 < jb y := by linarith [hJ1 y]
    have t0 : 0 ≤ |r y| := abs_nonneg _
    have t1 : 0 ≤ jb y * |deriv r y| := by positivity
    have t2 : 0 ≤ jb y ^ (2 : ℕ) * |deriv (deriv r) y| := by positivity
    interval_cases j
    · rw [hd0]
      refine c01_aux_wb (jb y) P.γ₂ 0 _ _ ρ (hJ1 y) hρ0 (by push_cast; linarith) ?_
      rw [Real.rpow_zero, one_mul]
      exact (mul_le_mul_of_nonneg_left (by linarith) hJγ).trans hW
    · rw [hd1]
      refine c01_aux_wb (jb y) P.γ₂ 1 _ _ ρ (hJ1 y) hρ0 (by push_cast; linarith) ?_
      rw [Real.rpow_one]
      exact (mul_le_mul_of_nonneg_left (by linarith) hJγ).trans hW
    · rw [hd2]
      refine c01_aux_wb (jb y) P.γ₂ 2 _ _ ρ (hJ1 y) hρ0 (by push_cast; linarith) ?_
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact (mul_le_mul_of_nonneg_left (by linarith) hJγ).trans hW
  -- pointwise bounds on `r` for `y ≥ 0`
  have hrpos0 : ∀ y, 0 ≤ y → |r y| ≤ ρ * jb y ^ (-P.p) := by
    intro y hy
    have hW := (hw y).1 hy
    have hJγ : 0 ≤ jb y ^ P.γ₂ := hX y _
    have t1 : 0 ≤ jb y ^ (-1 / P.p) * |deriv r y| := mul_nonneg (hX y _) (abs_nonneg _)
    have t2 : 0 ≤ jb y ^ (-2 / P.p) * |deriv (deriv r) y| := mul_nonneg (hX y _) (abs_nonneg _)
    refine c01_aux_wb (jb y) P.γ₂ 0 _ _ ρ (hJ1 y) hρ0 (by linarith) ?_
    rw [Real.rpow_zero, one_mul]
    exact (mul_le_mul_of_nonneg_left (by linarith) hJγ).trans hW
  have hrpos : ∀ y, 0 ≤ y → ∀ j : ℕ, j ≤ 1 →
      |iteratedDeriv (j + 1) r y| ≤ ρ * jb y ^ (-beta P.p + (j : ℝ) / P.p) := by
    intro y hy j hj
    have hW := (hw y).1 hy
    have hJγ : 0 ≤ jb y ^ P.γ₂ := hX y _
    have t0 : 0 ≤ |r y| := abs_nonneg _
    have t1 : 0 ≤ jb y ^ (-1 / P.p) * |deriv r y| := mul_nonneg (hX y _) (abs_nonneg _)
    have t2 : 0 ≤ jb y ^ (-2 / P.p) * |deriv (deriv r) y| := mul_nonneg (hX y _) (abs_nonneg _)
    have e1 : -1 / P.p = -(1 / P.p) := by ring
    have e2 : -2 / P.p = -(2 * (1 / P.p)) := by ring
    interval_cases j
    · rw [zero_add, hd1]
      refine c01_aux_wb (jb y) P.γ₂ (-1 / P.p) _ _ ρ (hJ1 y) hρ0 ?_ ?_
      · simp only [Nat.cast_zero, zero_div, add_zero]
        linarith [show -P.γ₂ - (-1 / P.p) = -P.γ₂ + 1 / P.p by ring]
      · exact (mul_le_mul_of_nonneg_left (by linarith) hJγ).trans hW
    · rw [show 1 + 1 = 2 from rfl, hd2]
      refine c01_aux_wb (jb y) P.γ₂ (-2 / P.p) _ _ ρ (hJ1 y) hρ0 ?_ ?_
      · simp only [Nat.cast_one]
        linarith [show -P.γ₂ - (-2 / P.p) = -P.γ₂ + 2 * (1 / P.p) by ring]
      · exact (mul_le_mul_of_nonneg_left (by linarith) hJγ).trans hW
  have hcd : ∀ (j : ℕ) y, ContDiffAt ℝ j r y := fun j y =>
    (hrs.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hcdb : ∀ (j : ℕ) y, ContDiffAt ℝ j fb y := fun j y =>
    (hfb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hcdb' : ∀ (j : ℕ) y, ContDiffAt ℝ j (fun y' => fb y' + y') y := fun j y =>
    ((hfb.of_le (WithTop.coe_le_coe.mpr le_top)).add contDiff_id).contDiffAt
  have hCC : ∀ Cj : ℝ, |Cj| ≤ |C0| + |C1| + |C2| → Cj + ρ ≤ |C0| + |C1| + |C2| + ρm + 1 := by
    intro Cj h; linarith [le_abs_self Cj]
  refine ⟨fun y hy j hj => ?_, fun y hy => ?_, fun y hy j hj => ?_⟩
  · have e : (fun y' => (fb + r) y' + y') = (fun y' => fb y' + y') + r := by
      funext y'; simp only [Pi.add_apply]; ring
    rw [e, iteratedDeriv_add (hcdb' j y) (hcd j y)]
    have hb := hrneg y hy j hj
    have hX' := hX y (-P.p - (j : ℝ))
    interval_cases j
    · exact c01_aux_sum_bound _ _ C0 ρ _ _ ((hC0 y).2 hy) hb hX'
        (hCC C0 (by linarith [abs_nonneg C1, abs_nonneg C2]))
    · exact c01_aux_sum_bound _ _ C1 ρ _ _ ((hC1 y).2 hy) hb hX'
        (hCC C1 (by linarith [abs_nonneg C0, abs_nonneg C2]))
    · exact c01_aux_sum_bound _ _ C2 ρ _ _ ((hC2 y).2 hy) hb hX'
        (hCC C2 (by linarith [abs_nonneg C0, abs_nonneg C1]))
  · exact c01_aux_sum_bound _ _ C0 ρ _ _ ((hC0 y).1 hy).1 (hrpos0 y hy) (hX y _)
      (hCC C0 (by linarith [abs_nonneg C1, abs_nonneg C2]))
  · rw [iteratedDeriv_add (hcdb (j + 1) y) (hcd (j + 1) y)]
    have hb := hrpos y hy j hj
    have hX' := hX y (-beta P.p + (j : ℝ) / P.p)
    interval_cases j
    · exact c01_aux_sum_bound _ _ C0 ρ _ _ ((hC0 y).1 hy).2 hb hX'
        (hCC C0 (by linarith [abs_nonneg C1, abs_nonneg C2]))
    · exact c01_aux_sum_bound _ _ C1 ρ _ _ ((hC1 y).1 hy).2 hb hX'
        (hCC C1 (by linarith [abs_nonneg C0, abs_nonneg C2]))


/-! ### The main theorem -/

/-- thm:main for every `T ∈ ℝ` (not only `T > 0`); used for `main` and
`c01_desingularization` (which needs `T = 0`).  Proof of blueprint thm:main. -/
theorem c01_aux_main_allT (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
          c01_profile_bounds_hold p C f ∧
          (∀ T : ℝ, gsqg_front_equation p (Iio T) (self_similar_ansatz p ε T f) ∧
              ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => self_similar_ansatz p ε T f q.1 q.2)
                (univ ×ˢ Iio T)) ∧
          (∀ T : ℝ, ∀ t : ℝ, t < T → ∀ x : ℝ,
              |self_similar_ansatz p ε T f x t - Real.sqrt ε * corner x| ≤
                C * Real.sqrt ε * (T - t) ^ (1 / (p + 1))) ∧
          (∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, ∀ δ : ℝ, 0 < δ →
              ∃ tδ : ℝ, tδ < T ∧ ∀ t : ℝ, tδ < t → t < T →
                ENNReal.ofReal (c * (T - t) ^ (-1 / (p + 1))) ≤
                  ⨆ x ∈ Ioo (-δ) δ,
                    ENNReal.ofReal
                      |iteratedDeriv 2 (fun x' => self_similar_ansatz p ε T f x' t) x|) := by
  have hp0 : 0 < p := by linarith
  have hβ : beta p + 1 / p < 2 * p + 1 := by
    have e : beta p + 1 / p = (p + 3) / (2 * p) := by unfold beta; field_simp; ring
    rw [e, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨P, hPp⟩ : ∃ P : parameters, P.p = p :=
    ⟨{ p := p, γ₁ := (2 * (beta p + 1 / p) + (2 * p + 1)) / 3,
       γ₂ := ((beta p + 1 / p) + 2 * (2 * p + 1)) / 3, hp_lo := hp, hp_hi := hp1,
       hγ₁ := by linarith, hγ₁₂ := by linarith, hγ₂ := by linarith }, rfl⟩
  subst hPp
  obtain ⟨R, δ, ε₁, C₀, _, hgood, hex, C', _, hprop⟩ := c01_profile_from_correction P
  obtain ⟨Cb, hCb, hbounds⟩ := c01_profile_bounds P R δ ε₁ C₀ hgood
  refine ⟨ε₁, hgood.2.1, 2 * Cb, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨μ, r, hdata⟩ := hex ε hε hε1
  obtain ⟨hfA, hres, -, hlimd, -, -⟩ := hprop ε hε hε1 μ r hdata
  have hsm := (c01_profile_smooth P R δ ε₁ C₀ hgood ε hε hε1 μ r hdata).1
  obtain ⟨b1, b2, b3⟩ := hbounds ε hε hε1 μ r hdata
  set f := approximate_solution_family P.p R ε μ + r with hfdef
  have hf2 : ContDiff ℝ 2 f := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf1 : ContDiff ℝ 1 f := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hjb : ∀ y a : ℝ, 0 ≤ jb y ^ a := fun y a => Real.rpow_nonneg (Real.sqrt_nonneg _) a
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hneg : ∀ y : ℝ, y ≤ 0 → |f y + y| ≤ Cb * jb y ^ (-P.p) := by
    intro y hy
    have := b1 y hy 0 (by norm_num)
    simpa using this
  refine ⟨f, hsm, ⟨fun y hy j hj => (b1 y hy j hj).trans ?_, fun y hy => (b2 y hy).trans ?_,
    fun y hy j hj => (b3 y hy j hj).trans ?_⟩, fun T => ⟨?_, ?_⟩, fun T t ht x => ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (hjb _ _)
  · exact mul_le_mul_of_nonneg_right (by linarith) (hjb _ _)
  · exact mul_le_mul_of_nonneg_right (by linarith) (hjb _ _)
  · exact (self_similar_reduction P.p hp0 hp1 ε T hε f hf2 hfA.2.1).2.mpr hres
  · exact contDiffOn_infty.mpr fun k =>
      ((c01_ansatz_time_derivative P.p hp0 hp1 ε T hε f hf1).2.2 k
        (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1
  · obtain ⟨h1, h2⟩ := (c01_corner_convergence P.p hp0 hp1 ε T hε f).2 Cb hCb hneg b2 t ht x
    have hTt : 0 ≤ Real.sqrt ε * (T - t) ^ (1 / (P.p + 1)) :=
      mul_nonneg hsε.le (Real.rpow_nonneg (by linarith) _)
    calc |self_similar_ansatz P.p ε T f x t - Real.sqrt ε * corner x|
        ≤ (P.p + 1) ^ (1 / (P.p + 1)) * Cb * (Real.sqrt ε * (T - t) ^ (1 / (P.p + 1))) := by
          linarith
      _ ≤ 2 * Cb * (Real.sqrt ε * (T - t) ^ (1 / (P.p + 1))) :=
          mul_le_mul_of_nonneg_right h2 hTt
      _ = 2 * Cb * Real.sqrt ε * (T - t) ^ (1 / (P.p + 1)) := by ring
  · obtain ⟨y₀, hy₀⟩ := c01_profile_not_affine f hf2 hlimd
      ⟨Cb, fun y hy => (b2 y hy).trans
        (mul_le_of_le_one_right hCb.le (c01_aux_jb_rpow_neg_le_one y P.p hp0.le))⟩
    obtain ⟨hc, hT⟩ := c01_curvature_blowup P.p hp0 hp1 ε hε f hf2 y₀ hy₀
    refine ⟨_, hc, fun T δ hδ => ⟨if y₀ ≠ 0 then T - 1 / (P.p + 1) * (δ / |y₀|) ^ (P.p + 1)
      else T - 1, ?_, (hT T δ hδ).1⟩⟩
    split_ifs with hy0
    · have : 0 < 1 / (P.p + 1) * (δ / |y₀|) ^ (P.p + 1) := by
        have : 0 < |y₀| := abs_pos.mpr hy0
        have : 0 < P.p + 1 := by linarith
        positivity
      linarith
    · linarith

-- Encoding: (4) the supremum over `(-δ,δ)` is taken in `ℝ≥0∞` (`⨆` of `ENNReal.ofReal`),
-- which is exactly `sup_{|x|<δ} |∂ₓ²F(x,t)|` (possibly `∞`); the `L^∞(ℝ)` norm in (3) is written
-- as a pointwise bound for all `x` (equivalent since `F(·,t)` is continuous).
/-- Blueprint: thm:main (self-similar corner formation).  Let `α = p+1 ∈ (7/4,2)`,
`β = α/(2(α-1))`.  There are `ε₀ > 0`, `C > 0` such that for every `0 < ε < ε₀` there is a profile
`f_ε ∈ C^∞(ℝ)` with
(1) profile bounds: `|∂ʲ(f_ε(y)+y)| ≤ C⟨y⟩^{-p-j}` for `y ≤ 0`, `j ≤ 2`; `|f_ε(y)| ≤ C⟨y⟩^{-p}` and
    `|∂^{j+1}f_ε(y)| ≤ C⟨y⟩^{-β+j/p}` (`j ∈ {0,1}`) for `y ≥ 0`;
(2) for every `T > 0`, `F(x,t) = √ε L(t) f_ε(x/L(t))` is a classical solution of the front
    equation on `ℝ × (-∞,T)` and `F ∈ C^∞(ℝ × (-∞,T))`;
(3) corner convergence `‖F(·,t) - √ε x₋‖_∞ ≤ C√ε (T-t)^{1/α}`;
(4) curvature blow-up: there is `c = c(ε) > 0` such that for all `T > 0`, `δ > 0` there is
    `t_δ < T` with `sup_{|x|<δ} |∂ₓ²F(x,t)| ≥ c (T-t)^{-1/α}` for `t_δ < t < T`. -/
theorem main (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
          -- (1) profile bounds
          (∀ y : ℝ, y ≤ 0 → ∀ j : ℕ, j ≤ 2 →
              |iteratedDeriv j (fun y' => f y' + y') y| ≤ C * jb y ^ (-p - (j : ℝ))) ∧
          (∀ y : ℝ, 0 ≤ y → |f y| ≤ C * jb y ^ (-p)) ∧
          (∀ y : ℝ, 0 ≤ y → ∀ j : ℕ, j ≤ 1 →
              |iteratedDeriv (j + 1) f y| ≤ C * jb y ^ (-beta p + (j : ℝ) / p)) ∧
          -- (2) classical, smooth solution of the front equation
          (∀ T : ℝ, 0 < T →
              gsqg_front_equation p (Iio T) (self_similar_ansatz p ε T f) ∧
              ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => self_similar_ansatz p ε T f q.1 q.2)
                (univ ×ˢ Iio T)) ∧
          -- (3) corner convergence
          (∀ T : ℝ, 0 < T → ∀ t : ℝ, t < T → ∀ x : ℝ,
              |self_similar_ansatz p ε T f x t - Real.sqrt ε * corner x| ≤
                C * Real.sqrt ε * (T - t) ^ (1 / (p + 1))) ∧
          -- (4) curvature blow-up
          (∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
              ∃ tδ : ℝ, tδ < T ∧ ∀ t : ℝ, tδ < t → t < T →
                ENNReal.ofReal (c * (T - t) ^ (-1 / (p + 1))) ≤
                  ⨆ x ∈ Ioo (-δ) δ,
                    ENNReal.ofReal |iteratedDeriv 2 (fun x' => self_similar_ansatz p ε T f x' t) x|) := by
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := c01_aux_main_allT p hp hp1
  refine ⟨ε₀, hε₀, C, hC, fun ε hε hε0 => ?_⟩
  obtain ⟨f, hf, ⟨b1, b2, b3⟩, h2, h3, c, hc, h4⟩ := h ε hε hε0
  exact ⟨f, hf, b1, b2, b3, fun T _ => h2 T, fun T _ => h3 T, c, hc, fun T _ => h4 T⟩

-- Encoding: "F the solution of thm:main with T = 0" is rendered by restating the existence
-- part of thm:main for T = 0 (same ε₀, C, profile bounds) together with the conclusions for
-- the reflected solution `F̃(x,t) = F(-x,-t)`.
/-- Blueprint: cor:c01_desingularization.  For `α ∈ (7/4,2)` and `0 < ε < ε₀`, with `F` the
solution of thm:main for `T = 0`, `F̃(x,t) = F(-x,-t)` is a smooth classical solution on
`ℝ × (0,∞)` with `‖F̃(·,t) - √ε x₊‖_∞ ≤ C√ε t^{1/α} → 0` as `t ↓ 0`. -/
theorem c01_desingularization (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ c01_profile_bounds_hold p C f ∧
          gsqg_front_equation p (Iio 0) (self_similar_ansatz p ε 0 f) ∧
          gsqg_front_equation p (Ioi 0) (fun x t => self_similar_ansatz p ε 0 f (-x) (-t)) ∧
          ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => self_similar_ansatz p ε 0 f (-q.1) (-q.2))
            (univ ×ˢ Ioi 0) ∧
          (∀ t : ℝ, 0 < t → ∀ x : ℝ,
            |self_similar_ansatz p ε 0 f (-x) (-t) - Real.sqrt ε * max x 0| ≤
              C * Real.sqrt ε * t ^ (1 / (p + 1))) ∧
          TendstoUniformly (fun t x => self_similar_ansatz p ε 0 f (-x) (-t))
            (fun x => Real.sqrt ε * max x 0) (𝓝[>] 0) := by
  obtain ⟨ε₀, hε₀, C, hC, h⟩ := c01_aux_main_allT p hp hp1
  refine ⟨ε₀, hε₀, C, hC, fun ε hε hε0 => ?_⟩
  obtain ⟨f, hf, hb, h2, h3, -⟩ := h ε hε hε0
  obtain ⟨hfront, hsm⟩ := h2 0
  have hpre : (fun t : ℝ => -t) ⁻¹' Iio 0 = Ioi 0 := by ext t; simp
  have hsym := (c01_front_symmetries p (by linarith) hp1 (Iio 0) isOpen_Iio _ hfront).2.2
  rw [hpre] at hsym
  have hbound : ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      |self_similar_ansatz p ε 0 f (-x) (-t) - Real.sqrt ε * max x 0| ≤
        C * Real.sqrt ε * t ^ (1 / (p + 1)) := by
    intro t ht x
    have := h3 0 (-t) (by linarith) (-x)
    have hc : corner (-x) = max x 0 := by simp [corner]
    rw [hc, show (0 : ℝ) - -t = t by ring] at this
    exact this
  refine ⟨f, hf, hb, hfront, hsym, ?_, hbound, ?_⟩
  · show ContDiffOn ℝ _ ((fun q : ℝ × ℝ => self_similar_ansatz p ε 0 f q.1 q.2) ∘
      (fun q : ℝ × ℝ => -q)) _
    exact hsm.comp contDiff_neg.contDiffOn
      (fun q hq => ⟨mem_univ _, show -q.2 < 0 from neg_lt_zero.mpr hq.2⟩)
  · rw [Metric.tendstoUniformly_iff]
    intro e he
    have hp0 : 0 < p + 1 := by linarith
    have ht0 : Tendsto (fun t : ℝ => C * Real.sqrt ε * t ^ (1 / (p + 1))) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => t ^ (1 / (p + 1))) :=
        continuous_id.rpow_const (fun _ => Or.inr (by positivity))
      have := (hc.tendsto 0).const_mul (C * Real.sqrt ε)
      rw [Real.zero_rpow (by positivity), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [ht0.eventually (gt_mem_nhds he), self_mem_nhdsWithin] with t h1 ht x
    rw [dist_comm, Real.dist_eq]
    exact (hbound t ht x).trans_lt h1

end GSQG
