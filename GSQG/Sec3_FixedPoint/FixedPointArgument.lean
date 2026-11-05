import GSQG.Definitions

/-!
# §3: the fixed point argument (blueprint ch. 02)

Statements and proofs of the nodes of `blueprint/src/chapters/02_fixed_point.tex`. The three
backbone theorems `fixed_point_approximation`, `fixed_point_linear_inverse` and
`fixed_point_nonlinear_estimates` are proved in `Sec3_FixedPoint/MainTheorem.lean` from
`approx_assembly`, `linear_inverse_assembly` and `nonlinear_assembly`.

## How "ε₀, δ, B̄, f̄ as in thm:fixed_point_approximation" is encoded

The family `f̄_{ε,μ} = approximate_solution_family p R ε μ` of def:approximate_solution_family depends on
the cutoff scale `R ≥ R₀` and on the radius `δ` of `B̄ = Bbar p δ`; later chapters shrink `ε₀`
(and may enlarge `R₀`).  We therefore package the conclusions of the three backbone theorems as
predicates in the parameters (`R`, `δ`, `ε₀`):

* `fixed_point_approximation_statement P R δ ε₀`,
* `fixed_point_linear_inverse_statement P δ ε₀`,
* `fixed_point_nonlinear_estimates_statement P R δ ε₀`,

each of which is downward closed in `ε₀`.  The theorems assert that the predicates hold for all
`R ≥ R₀`, `0 < δ ≤ δ₀` and *some* `ε₀ > 0` (depending on `R`, `δ`).  The lemmas of the reduction
section assume `c02_forcing_map_setting P R δ ε₀` (the conjunction of the three predicates), which
is exactly "`ε₀, δ, B̄, f̄` as in thm:fixed_point_approximation and `𝒯₀, 𝒰_ε, 𝒱_ε` as in
thm:fixed_point_linear_inverse".
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology NNReal Interval FourierTransform ComplexConjugate

noncomputable section

namespace GSQG

/-! ### Parameters and function spaces -/

/-- Blueprint: lem:c02_parameter_range_nonempty.  For `3/4 < p < 1`: `β + 1/p < 2p+1`, so
admissible `γ₁ < γ₂` exist, and `γ - 1/p > β > 1` for every admissible `γ`. -/
theorem c02_parameter_range_nonempty (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    beta p + 1 / p < 2 * p + 1 ∧
    (∃ γ₁ γ₂ : ℝ, beta p + 1 / p < γ₁ ∧ γ₁ < γ₂ ∧ γ₂ < 2 * p + 1) ∧
    (∀ γ, admissibleGamma p γ → beta p < γ - 1 / p) ∧ 1 < beta p := by
  have hp0 : 0 < p := by linarith
  have h1 : beta p + 1 / p < 2 * p + 1 := by
    have : beta p + 1 / p = (p + 3) / (2 * p) := by unfold beta; field_simp; ring
    rw [this, div_lt_iff₀ (by positivity)]; nlinarith
  refine ⟨h1, ⟨(2 * (beta p + 1 / p) + (2 * p + 1)) / 3, ((beta p + 1 / p) + 2 * (2 * p + 1)) / 3,
    by linarith, by linarith, by linarith⟩, fun γ hγ => by linarith [hγ.1], ?_⟩
  unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith

/-- Admissible exponents satisfy `γ > 1`. -/
theorem c02_aux_one_lt_of_admissible (P : parameters) {γ : ℝ} (hγ : P.admissible γ) : 1 < γ := by
  obtain ⟨-, -, h3, h4⟩ := c02_parameter_range_nonempty P.p P.hp_lo P.hp_hi
  have := h3 γ hγ
  have : 0 < 1 / P.p := by have := P.hp_lo; positivity
  linarith

/-- `γ₁` is admissible. -/
theorem c02_aux_adm₁ (P : parameters) : P.admissible P.γ₁ :=
  ⟨P.hγ₁, by linarith [P.hγ₁₂, P.hγ₂]⟩

/-- `γ₂` is admissible. -/
theorem c02_aux_adm₂ (P : parameters) : P.admissible P.γ₂ :=
  ⟨by linarith [P.hγ₁₂, P.hγ₁], P.hγ₂⟩

/-- `μ_* ≠ 0` (since `p > 0`). -/
theorem c02_aux_mu_star_ne (P : parameters) : mu_star P.p ≠ 0 := by
  unfold mu_star
  have hp : 0 < P.p := by linarith [P.hp_lo]
  exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')

/-! ### Auxiliary analytic facts -/

/-- `⟨y⟩ > 0`. -/
theorem c02_aux_jb_pos (y : ℝ) : 0 < jb y := Real.sqrt_pos.mpr (by positivity)

/-- `⟨y⟩ ≥ 1`. -/
theorem c02_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg y])

/-- Pointwise a.e. bound from a finite essential supremum of `ofReal ∘ g`. -/
theorem c02_aux_ae_le_of_essSup {μ : Measure ℝ} {g : ℝ → ℝ}
    (h : essSup (fun y => ENNReal.ofReal (g y)) μ < ⊤) :
    ∃ M : ℝ, ∀ᵐ y ∂μ, g y ≤ M := by
  refine ⟨(essSup (fun y => ENNReal.ofReal (g y)) μ).toReal, ?_⟩
  filter_upwards [ae_le_essSup (f := fun y => ENNReal.ofReal (g y)) (μ := μ)] with y hy
  exact (ENNReal.ofReal_le_iff_le_toReal h.ne).1 hy

/-- Elements of `Y_γ` satisfy `⟨y⟩^γ |G y| ≤ M` a.e. -/
theorem c02_aux_Y_ae_bound {p γ : ℝ} {G : ℝ → ℝ} (hG : G ∈ Y_gamma p γ) :
    ∃ M : ℝ, ∀ᵐ y, jb y ^ γ * |G y| ≤ M := by
  obtain ⟨_, hfin⟩ := hG
  unfold Y_gamma_norm at hfin
  obtain ⟨M1, h1⟩ := c02_aux_ae_le_of_essSup (lt_of_le_of_lt le_self_add hfin)
  obtain ⟨M2, h2⟩ := c02_aux_ae_le_of_essSup (lt_of_le_of_lt le_add_self hfin)
  refine ⟨max M1 M2, ?_⟩
  have hu : (univ : Set ℝ) = Ici 0 ∪ Iic 0 := by
    ext y; simp only [mem_univ, mem_union, mem_Ici, mem_Iic, true_iff]; exact le_total 0 y
  suffices h : ∀ᵐ y ∂(volume.restrict (univ : Set ℝ)), jb y ^ γ * |G y| ≤ max M1 M2 by
    simpa using h
  rw [hu, ae_restrict_union_iff]
  constructor
  · filter_upwards [h1] with y hy
    have h0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c02_aux_jb_pos y) γ).le
    have : 0 ≤ jb y ^ (-1 / p) * ‖deriv G y‖ :=
      mul_nonneg (Real.rpow_pos_of_pos (c02_aux_jb_pos y) _).le (norm_nonneg _)
    simp only [Real.norm_eq_abs] at hy this
    nlinarith [le_max_left M1 M2, mul_nonneg h0 this]
  · filter_upwards [h2] with y hy
    have h0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c02_aux_jb_pos y) γ).le
    have : 0 ≤ jb y * ‖deriv G y‖ := mul_nonneg (c02_aux_jb_pos y).le (norm_nonneg _)
    simp only [Real.norm_eq_abs] at hy this
    nlinarith [le_max_right M1 M2, mul_nonneg h0 this]

/-- `⟨y⟩^{-γ} ∈ L¹` for `γ > 1`. -/
theorem c02_aux_jb_rpow_integrable {γ : ℝ} (hγ : 1 < γ) : Integrable (fun y => jb y ^ (-γ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := γ)
    (by simpa using hγ)
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Real.norm_eq_abs, sq_abs, jb]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- `Y_γ ⊆ L¹` for `γ > 1`. -/
theorem c02_aux_Y_integrable {p γ : ℝ} (hγ : 1 < γ) {G : ℝ → ℝ} (hG : G ∈ Y_gamma p γ) :
    Integrable G := by
  obtain ⟨M, hM⟩ := c02_aux_Y_ae_bound hG
  refine ((c02_aux_jb_rpow_integrable hγ).const_mul M).mono'
    hG.1.continuous.aestronglyMeasurable ?_
  filter_upwards [hM] with y hy
  have hj := Real.rpow_pos_of_pos (c02_aux_jb_pos y) γ
  rw [Real.norm_eq_abs, Real.rpow_neg (c02_aux_jb_pos y).le, ← div_eq_mul_inv, le_div_iff₀ hj]
  linarith [mul_comm (jb y ^ γ) |G y|]

/-- `|e^{-ixξ}| = 1`. -/
theorem c02_aux_norm_exp (x ξ : ℝ) : ‖Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- The Fourier integrand of an integrable continuous function is integrable. -/
theorem c02_aux_fourier_integrand_integrable {G : ℝ → ℝ} (hG : Integrable G)
    (hc : Continuous G) (ξ : ℝ) :
    Integrable (fun x => (G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) := by
  have hcont : Continuous (fun x : ℝ => (G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) :=
    (Complex.continuous_ofReal.comp hc).mul (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const).neg)
  refine Integrable.mono' hG.norm hcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [norm_mul, c02_aux_norm_exp, mul_one, Complex.norm_real]

/-- `ℝ`-linearity of `fourierT` on integrable continuous functions. -/
theorem c02_aux_fourierT_lin {G H : ℝ → ℝ} (hG : Integrable G) (hGc : Continuous G)
    (hH : Integrable H) (hHc : Continuous H) (a b : ℝ) (ξ : ℝ) :
    fourierT (fun x => ((a * G x + b * H x : ℝ) : ℂ)) ξ =
      a * fourierT (fun x => (G x : ℂ)) ξ + b * fourierT (fun x => (H x : ℂ)) ξ := by
  unfold fourierT
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · congr 1; ext x; push_cast; ring
  · exact (c02_aux_fourier_integrand_integrable hG hGc ξ).const_mul _
  · exact (c02_aux_fourier_integrand_integrable hH hHc ξ).const_mul _

/-- `fourierT` of an integrable continuous function is continuous. -/
theorem c02_aux_fourierT_continuous {G : ℝ → ℝ} (hG : Integrable G) (hc : Continuous G) :
    Continuous (fourierT (fun x => (G x : ℂ))) := by
  unfold fourierT
  have hcx : ∀ x : ℝ, Continuous fun ξ : ℝ =>
      (G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) := fun x =>
    continuous_const.mul (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg))
  refine continuous_of_dominated (bound := fun x => ‖G x‖) (fun ξ => ?_) (fun ξ => ae_of_all _
    fun x => ?_) hG.norm (ae_of_all _ hcx)
  · exact (c02_aux_fourier_integrand_integrable hG hc ξ).aestronglyMeasurable
  · rw [norm_mul, c02_aux_norm_exp, mul_one, Complex.norm_real]

/-- `Φ₀` is continuous for `p > 0`. -/
theorem c02_aux_Phi0_continuous {p : ℝ} (hp : 0 < p) : Continuous (Phi0 p) := by
  unfold Phi0
  exact (continuous_id.mul (continuous_abs.rpow_const fun _ => Or.inr hp.le)).div_const _

/-- The truncated `ℓ` integrals (as functions of the cutoff `R`). -/
theorem c02_aux_ell_integrand_continuous {p : ℝ} (hp : 0 < p) {G : ℝ → ℝ} (hG : Integrable G)
    (hc : Continuous G) :
    Continuous fun ξ : ℝ => (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      fourierT (fun x => (G x : ℂ)) ξ :=
  (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (c02_aux_Phi0_continuous hp))))).mul
    (c02_aux_fourierT_continuous hG hc)

/-- `ℝ`-linearity of `ℓ` (and of the defining limit) on integrable continuous functions for which
the defining limits exist. -/
theorem c02_aux_ell_lin {p : ℝ} (hp : 0 < p) {G H : ℝ → ℝ} (hG : Integrable G)
    (hGc : Continuous G) (hH : Integrable H) (hHc : Continuous H) {LG LH : ℂ}
    (hLG : Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      fourierT (fun x => (G x : ℂ)) ξ) atTop (𝓝 LG))
    (hLH : Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      fourierT (fun x => (H x : ℂ)) ξ) atTop (𝓝 LH)) (a b : ℝ) :
    Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      fourierT (fun x => ((a * G x + b * H x : ℝ) : ℂ)) ξ) atTop (𝓝 (a * LG + b * LH)) ∧
    ell p (fun x => a * G x + b * H x) = a * ell p G + b * ell p H := by
  have heq : (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      fourierT (fun x => ((a * G x + b * H x : ℝ) : ℂ)) ξ) = fun R =>
      (a : ℂ) * (∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
        fourierT (fun x => (G x : ℂ)) ξ) +
      (b : ℂ) * (∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
        fourierT (fun x => (H x : ℂ)) ξ) := by
    funext R
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add]
    · congr 1; funext ξ; rw [c02_aux_fourierT_lin hG hGc hH hHc]; ring
    · exact ((c02_aux_ell_integrand_continuous hp hG hGc).const_mul _).intervalIntegrable _ _
    · exact ((c02_aux_ell_integrand_continuous hp hH hHc).const_mul _).intervalIntegrable _ _
  have ht : Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      fourierT (fun x => ((a * G x + b * H x : ℝ) : ℂ)) ξ) atTop (𝓝 (a * LG + b * LH)) := by
    rw [heq]; exact (hLG.const_mul _).add (hLH.const_mul _)
  refine ⟨ht, ?_⟩
  unfold ell
  rw [ht.limUnder_eq, hLG.limUnder_eq, hLH.limUnder_eq]

/-! ### Banach space structure of `X_γ`, `Y_γ` -/

/-- Rademacher for locally Lipschitz functions `ℝ → ℝ`. -/
theorem c02_aux_ae_diff {f : ℝ → ℝ} (hf : LocallyLipschitz f) : ∀ᵐ x, DifferentiableAt ℝ f x := by
  choose K t ht hL using hf
  obtain ⟨s, hs, hcov⟩ := TopologicalSpace.countable_cover_nhds (f := fun x => interior (t x))
    (fun x => interior_mem_nhds.2 (ht x))
  have h : ∀ᵐ y, ∀ x ∈ s, y ∈ t x → DifferentiableWithinAt ℝ f (t x) y :=
    (ae_ball_iff hs).2 fun x _ => (hL x).ae_differentiableWithinAt_of_mem
  filter_upwards [h] with y hy
  have : y ∈ ⋃ x ∈ s, interior (t x) := by rw [hcov]; trivial
  simp only [mem_iUnion] at this
  obtain ⟨x, hx, hyx⟩ := this
  exact (hy x hx (interior_subset hyx)).differentiableAt (mem_interior_iff_mem_nhds.1 hyx)

/-- Triangle inequality for one `Y`-type essential supremum. -/
theorem c02_aux_essSup_Y_add {μ : Measure ℝ} (a b : ℝ → ℝ) (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y)
    {G H : ℝ → ℝ} (hd : ∀ᵐ y ∂μ, deriv (G + H) y = deriv G y + deriv H y) :
    essSup (fun y => ENNReal.ofReal (a y * (‖(G + H) y‖ + b y * ‖deriv (G + H) y‖))) μ ≤
      essSup (fun y => ENNReal.ofReal (a y * (‖G y‖ + b y * ‖deriv G y‖))) μ +
      essSup (fun y => ENNReal.ofReal (a y * (‖H y‖ + b y * ‖deriv H y‖))) μ := by
  refine le_trans (essSup_mono_ae ?_) (ENNReal.essSup_add_le _ _)
  filter_upwards [hd] with y hy
  simp only [Pi.add_apply]
  rw [← ENNReal.ofReal_add (by have := ha y; have := hb y; positivity)
    (by have := ha y; have := hb y; positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hy]
  have h1 := norm_add_le (G y) (H y)
  have h2 := norm_add_le (deriv G y) (deriv H y)
  have := mul_le_mul_of_nonneg_left h2 (hb y)
  have := mul_le_mul_of_nonneg_left (show ‖G y + H y‖ + b y * ‖deriv G y + deriv H y‖ ≤
    (‖G y‖ + b y * ‖deriv G y‖) + (‖H y‖ + b y * ‖deriv H y‖) by linarith) (ha y)
  linarith

/-- Scaling of one `Y`-type essential supremum. -/
theorem c02_aux_essSup_Y_smul {μ : Measure ℝ} (a b : ℝ → ℝ) (c : ℝ) (G : ℝ → ℝ) :
    essSup (fun y => ENNReal.ofReal (a y * (‖(c • G) y‖ + b y * ‖deriv (c • G) y‖))) μ =
      ENNReal.ofReal |c| * essSup (fun y => ENNReal.ofReal (a y * (‖G y‖ + b y * ‖deriv G y‖))) μ := by
  rw [← ENNReal.essSup_const_mul]
  congr 1; funext y
  have e : c • G = fun x => c * G x := rfl
  rw [e, deriv_const_mul_field', ← ENNReal.ofReal_mul (abs_nonneg c)]
  congr 1
  simp only [norm_mul, Real.norm_eq_abs]
  ring

/-- Vanishing of one `Y`-type essential supremum gives `G = 0` a.e. -/
theorem c02_aux_essSup_zero {μ : Measure ℝ} (a : ℝ → ℝ) (ha : ∀ y, 0 < a y) (F : ℝ → ℝ)
    (hF : ∀ y, 0 ≤ F y) (G : ℝ → ℝ)
    (h : essSup (fun y => ENNReal.ofReal (a y * (‖G y‖ + F y))) μ = 0) : ∀ᵐ y ∂μ, G y = 0 := by
  rw [ENNReal.essSup_eq_zero_iff] at h
  filter_upwards [h] with y hy
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hy
  have h1 := ha y
  have h2 := hF y
  have : ‖G y‖ ≤ 0 := by nlinarith [norm_nonneg (G y)]
  exact norm_le_zero_iff.1 this

/-- The norm axioms of `Y_γ`. -/
theorem c02_aux_Y_axioms (P : parameters) (γ : ℝ) :
    (0 : ℝ → ℝ) ∈ Y_gamma P.p γ ∧
    (∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ,
      G + H ∈ Y_gamma P.p γ ∧ yNorm P.p γ (G + H) ≤ yNorm P.p γ G + yNorm P.p γ H) ∧
    (∀ c : ℝ, ∀ G ∈ Y_gamma P.p γ, c • G ∈ Y_gamma P.p γ ∧ yNorm P.p γ (c • G) = |c| * yNorm P.p γ G) ∧
    (∀ G ∈ Y_gamma P.p γ, yNorm P.p γ G = 0 → G = 0) := by
  have ha : ∀ y, 0 ≤ jb y ^ γ := fun y => (Real.rpow_pos_of_pos (c02_aux_jb_pos y) _).le
  have hb1 : ∀ y, 0 ≤ jb y ^ (-1 / P.p) := fun y => (Real.rpow_pos_of_pos (c02_aux_jb_pos y) _).le
  have hb2 : ∀ y, 0 ≤ jb y := fun y => (c02_aux_jb_pos y).le
  have hzero : Y_gamma_norm P.p γ (0 : ℝ → ℝ) = 0 := by
    unfold Y_gamma_norm
    simp [ENNReal.essSup_eq_zero_iff]
    exact ⟨Eventually.of_forall fun _ => rfl, Eventually.of_forall fun _ => rfl⟩
  have hadd : ∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ,
      Y_gamma_norm P.p γ (G + H) ≤ Y_gamma_norm P.p γ G + Y_gamma_norm P.p γ H := by
    intro G hG H hH
    have hd : ∀ᵐ y, deriv (G + H) y = deriv G y + deriv H y := by
      filter_upwards [c02_aux_ae_diff hG.1, c02_aux_ae_diff hH.1] with y h1 h2
      exact deriv_add h1 h2
    unfold Y_gamma_norm
    calc _ ≤ (essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / P.p) * ‖deriv G y‖)))
            (volume.restrict (Ici 0)) +
          essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖H y‖ + jb y ^ (-1 / P.p) * ‖deriv H y‖)))
            (volume.restrict (Ici 0))) +
          (essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖)))
            (volume.restrict (Iic 0)) +
          essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖H y‖ + jb y * ‖deriv H y‖)))
            (volume.restrict (Iic 0))) :=
          add_le_add (c02_aux_essSup_Y_add _ _ ha hb1 (ae_restrict_of_ae hd))
            (c02_aux_essSup_Y_add _ _ ha hb2 (ae_restrict_of_ae hd))
      _ = _ := by ring
  refine ⟨⟨LocallyLipschitz.const 0, by rw [hzero]; simp⟩, fun G hG H hH => ?_, fun c G hG => ?_,
    fun G hG h => ?_⟩
  · have hl := hadd G hG H hH
    have hfin : Y_gamma_norm P.p γ G + Y_gamma_norm P.p γ H < ⊤ := ENNReal.add_lt_top.2 ⟨hG.2, hH.2⟩
    refine ⟨⟨hG.1.add hH.1, lt_of_le_of_lt hl hfin⟩, ?_⟩
    unfold yNorm
    rw [← ENNReal.toReal_add hG.2.ne hH.2.ne]
    exact ENNReal.toReal_mono hfin.ne hl
  · have hs : Y_gamma_norm P.p γ (c • G) = ENNReal.ofReal |c| * Y_gamma_norm P.p γ G := by
      unfold Y_gamma_norm
      rw [c02_aux_essSup_Y_smul, c02_aux_essSup_Y_smul, mul_add]
    have hll : LocallyLipschitz (c • G) :=
      (lipschitzWith_smul c).locallyLipschitz.comp hG.1
    refine ⟨⟨hll, ?_⟩, ?_⟩
    · rw [hs]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.2
    · unfold yNorm; rw [hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg c)]
  · have h0 : Y_gamma_norm P.p γ G = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
      · exact h
      · exact absurd h hG.2.ne
    unfold Y_gamma_norm at h0
    rw [add_eq_zero] at h0
    have h1 := c02_aux_essSup_zero _ (fun y => Real.rpow_pos_of_pos (c02_aux_jb_pos y) γ) _
      (fun y => mul_nonneg (hb1 y) (norm_nonneg _)) G h0.1
    have h2 := c02_aux_essSup_zero _ (fun y => Real.rpow_pos_of_pos (c02_aux_jb_pos y) γ) _
      (fun y => mul_nonneg (hb2 y) (norm_nonneg _)) G h0.2
    have hu : (univ : Set ℝ) = Ici 0 ∪ Iic 0 := by
      ext y; simp only [mem_univ, mem_union, mem_Ici, mem_Iic, true_iff]; exact le_total 0 y
    have hae : ∀ᵐ y ∂(volume.restrict (univ : Set ℝ)), G y = 0 := by
      rw [hu, ae_restrict_union_iff]; exact ⟨h1, h2⟩
    rw [Measure.restrict_univ] at hae
    exact (Continuous.ae_eq_iff_eq volume hG.1.continuous continuous_const).1 hae
/-- Derivatives of locally Lipschitz functions are bounded on compact intervals. -/
theorem c02_aux_deriv_bdd {f : ℝ → ℝ} (hf : LocallyLipschitz f) (a b : ℝ) :
    ∃ K, ∀ y ∈ Icc a b, |deriv f y| ≤ K := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc (a := a - 1) (b := b + 1)) hf.locallyLipschitzOn
  refine ⟨K, fun y hy => ?_⟩
  have := norm_deriv_le_of_lipschitzOn (x₀ := y) (Icc_mem_nhds (by linarith [hy.1]) (by linarith [hy.2])) hK
  simpa using this

/-- FTC for locally Lipschitz functions. -/
theorem c02_aux_ftc {f : ℝ → ℝ} (hf : LocallyLipschitz f) (a b : ℝ) :
    ∫ x in a..b, deriv f x = f b - f a ∧ IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_uIcc (a := a) (b := b)) hf.locallyLipschitzOn
  have hac := hK.absolutelyContinuousOnInterval
  exact ⟨hac.integral_deriv_eq_sub, hac.intervalIntegrable_deriv⟩

/-- Positive lower bound of a continuous positive function on a compact interval. -/
theorem c02_aux_pos_lower {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ y, 0 < v y) (a b : ℝ) :
    ∃ c > 0, ∀ y ∈ Icc a b, c ≤ v y := by
  rcases (Icc a b).eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  obtain ⟨y₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn h hv.continuousOn
  exact ⟨v y₀, hpos y₀, fun y hy => hmin hy⟩

/-- A continuous function which is a.e. `≤ η` is everywhere `≤ η`. -/
theorem c02_aux_le_of_ae {φ : ℝ → ℝ} (hφ : Continuous φ) {η : ℝ} (h : ∀ᵐ y, φ y ≤ η) :
    ∀ y, φ y ≤ η := by
  intro y
  by_contra hy
  rw [not_le] at hy
  have hU : IsOpen {x | η < φ x} := isOpen_lt continuous_const hφ
  have hpos := hU.measure_pos volume ⟨y, hy⟩
  have h0 : volume {x | η < φ x} = 0 := by
    rw [ae_iff] at h; simpa [not_le] using h
  exact hpos.ne' h0

/-- Completeness of a weighted `W^{1,∞}_loc` space: a Cauchy sequence of locally Lipschitz
functions for `ess sup (w₀|f| + w₁|f'|)` (weights with continuous positive minorants) converges. -/
theorem c02_aux_W1_complete (w0 w1 v0 v1 : ℝ → ℝ) (hv0c : Continuous v0) (hv1c : Continuous v1)
    (hv0 : ∀ y, 0 < v0 y) (hv1 : ∀ y, 0 < v1 y) (h0 : ∀ y, v0 y ≤ w0 y) (h1 : ∀ y, v1 y ≤ w1 y)
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, LocallyLipschitz (f n))
    (hC : ∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ᵐ y,
      w0 y * |f m y - f n y| + w1 y * |deriv (f m) y - deriv (f n) y| ≤ η) :
    ∃ g : ℝ → ℝ, LocallyLipschitz g ∧
      (∀ η > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ᵐ y,
        w0 y * |f n y - g y| + w1 y * |deriv (f n) y - deriv g y| ≤ η) ∧
      (∀ η > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y, v0 y * |f n y - g y| ≤ η) := by
  choose N hN using fun k : ℕ => hC (1 / ((k : ℝ) + 1)) (by positivity)
  have hw1 : ∀ y, 0 < w1 y := fun y => (hv1 y).trans_le (h1 y)
  -- everywhere bound with the weight `v₀`
  have hev : ∀ k, ∀ m ≥ N k, ∀ n ≥ N k, ∀ y, v0 y * |f m y - f n y| ≤ 1 / ((k : ℝ) + 1) := by
    intro k m hm n hn
    refine c02_aux_le_of_ae (φ := fun y => v0 y * |f m y - f n y|)
      (hv0c.mul ((hf m).continuous.sub (hf n).continuous).abs) ?_
    filter_upwards [hN k m hm n hn] with y hy
    have := mul_le_mul_of_nonneg_right (h0 y) (abs_nonneg (f m y - f n y))
    have : 0 ≤ w1 y * |deriv (f m) y - deriv (f n) y| := mul_nonneg (hw1 y).le (abs_nonneg _)
    linarith
  -- pointwise limit
  have hsmall : ∀ {A B : ℝ} {ε : ℝ}, 0 < A → 0 < ε → ∀ k : ℕ, 1 / ((k : ℝ) + 1) < ε * A →
      A * B ≤ 1 / ((k : ℝ) + 1) → B < ε := by
    intro A B ε hA hε k hk hAB
    by_contra hc; rw [not_lt] at hc
    nlinarith
  have hcauchy : ∀ y, CauchySeq fun n => f n y := by
    intro y
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε * v0 y by have := hv0 y; positivity)
    refine ⟨N k, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact hsmall (hv0 y) hε k hk (hev k n hn (N k) le_rfl y)
  choose g hg using fun y => cauchySeq_tendsto_of_complete (hcauchy y)
  have hgb : ∀ k, ∀ n ≥ N k, ∀ y, v0 y * |f n y - g y| ≤ 1 / ((k : ℝ) + 1) := by
    intro k n hn y
    have ht : Tendsto (fun m => v0 y * |f n y - f m y|) atTop (𝓝 (v0 y * |f n y - g y|)) :=
      ((tendsto_const_nhds.sub (hg y)).abs).const_mul _
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N k, fun m hm => hev k n hn m hm y⟩)
  -- a.e. limit of derivatives
  have hae0 : ∀ k m n, ∀ᵐ y, m ≥ N k → n ≥ N k →
      w0 y * |f m y - f n y| + w1 y * |deriv (f m) y - deriv (f n) y| ≤ 1 / ((k : ℝ) + 1) := by
    intro k m n
    by_cases hm : m ≥ N k
    · by_cases hn : n ≥ N k
      · filter_upwards [hN k m hm n hn] with y hy; exact fun _ _ => hy
      · exact Eventually.of_forall fun y _ hn' => absurd hn' hn
    · exact Eventually.of_forall fun y hm' => absurd hm' hm
  have hae : ∀ᵐ y, ∀ k m n, m ≥ N k → n ≥ N k →
      w0 y * |f m y - f n y| + w1 y * |deriv (f m) y - deriv (f n) y| ≤ 1 / ((k : ℝ) + 1) :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun m => ae_all_iff.2 fun n => hae0 k m n
  set d : ℝ → ℝ := fun y => limUnder atTop fun n => deriv (f n) y with hd
  have hdlim : ∀ᵐ y, Tendsto (fun n => deriv (f n) y) atTop (𝓝 (d y)) := by
    filter_upwards [hae] with y hy
    have hc : CauchySeq fun n => deriv (f n) y := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε * w1 y by have := hw1 y; positivity)
      refine ⟨N k, fun n hn => ?_⟩
      rw [Real.dist_eq]
      have := hy k n (N k) hn le_rfl
      have : 0 ≤ w0 y * |f n y - f (N k) y| :=
        mul_nonneg ((hv0 y).le.trans (h0 y)) (abs_nonneg _)
      exact hsmall (hw1 y) hε k hk (by linarith)
    exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)
  have hdb : ∀ᵐ y, ∀ k, ∀ n ≥ N k,
      w0 y * |f n y - g y| + w1 y * |deriv (f n) y - d y| ≤ 1 / ((k : ℝ) + 1) := by
    filter_upwards [hae, hdlim] with y hy hyd
    intro k n hn
    have ht : Tendsto (fun m => w0 y * |f n y - f m y| + w1 y * |deriv (f n) y - deriv (f m) y|)
        atTop (𝓝 (w0 y * |f n y - g y| + w1 y * |deriv (f n) y - d y|)) :=
      (((tendsto_const_nhds.sub (hg y)).abs).const_mul _).add
        (((tendsto_const_nhds.sub hyd).abs).const_mul _)
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N k, fun m hm => hy k n m hn hm⟩)
  have hdm : AEStronglyMeasurable d volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (measurable_deriv (f n)).aestronglyMeasurable) hdlim
  -- local bounds for `d`
  have hdloc : ∀ a b : ℝ, ∃ M, ∀ᵐ y, y ∈ Icc a b → |d y| ≤ M := by
    intro a b
    obtain ⟨K, hK⟩ := c02_aux_deriv_bdd (hf (N 0)) a b
    obtain ⟨c, hc, hcv⟩ := c02_aux_pos_lower hv1c hv1 a b
    refine ⟨K + 1 / c, ?_⟩
    filter_upwards [hdb] with y hy hyab
    have h1' := hy 0 (N 0) le_rfl
    simp only [Nat.cast_zero, zero_add, div_one] at h1'
    have h2 : 0 ≤ w0 y * |f (N 0) y - g y| := mul_nonneg ((hv0 y).le.trans (h0 y)) (abs_nonneg _)
    have h3 : c * |deriv (f (N 0)) y - d y| ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ((hcv y hyab).trans (h1 y)) (abs_nonneg (deriv (f (N 0)) y - d y))
      linarith
    have h4 : |deriv (f (N 0)) y - d y| ≤ 1 / c := by rw [le_div_iff₀ hc]; linarith
    have h5 := hK y hyab
    have : |d y| ≤ |deriv (f (N 0)) y| + |deriv (f (N 0)) y - d y| := by
      have := abs_sub_abs_le_abs_sub (deriv (f (N 0)) y) (d y)
      have := abs_sub_comm (deriv (f (N 0)) y) (d y)
      linarith [abs_sub_abs_le_abs_sub (d y) (deriv (f (N 0)) y)]
    linarith
  have hdint : ∀ a b : ℝ, IntervalIntegrable d volume a b := by
    intro a b
    obtain ⟨M, hM⟩ := hdloc (min a b) (max a b)
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := M) (measure_mono uIoc_subset_uIcc |>.trans_lt
      (by rw [uIcc, Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne hdm ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hM] with y hy hyI
    exact hy (uIoc_subset_uIcc hyI)
  -- `g(y) - g(a) = ∫_a^y d`
  have hgint : ∀ a y : ℝ, g y - g a = ∫ x in a..y, d x := by
    intro a y
    obtain ⟨c, hc, hcv⟩ := c02_aux_pos_lower hv1c hv1 (min a y) (max a y)
    have hlim1 : Tendsto (fun n => f n y - f n a) atTop (𝓝 (g y - g a)) := (hg y).sub (hg a)
    have hlim2 : Tendsto (fun n => f n y - f n a) atTop (𝓝 (∫ x in a..y, d x)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε * c / (|y - a| + 1) by positivity)
      refine ⟨N k, fun n hn => ?_⟩
      rw [← (c02_aux_ftc (hf n) a y).1, Real.dist_eq, ← intervalIntegral.integral_sub
        (c02_aux_ftc (hf n) a y).2 (hdint a y)]
      have hb : ∀ᵐ x, x ∈ Ι a y → ‖deriv (f n) x - d x‖ ≤ 1 / ((k : ℝ) + 1) / c := by
        filter_upwards [hdb] with x hx hxI
        have hxI' : x ∈ Icc (min a y) (max a y) := uIoc_subset_uIcc hxI
        have h1' := hx k n hn
        have h2 : 0 ≤ w0 x * |f n x - g x| := mul_nonneg ((hv0 x).le.trans (h0 x)) (abs_nonneg _)
        have h3 := mul_le_mul_of_nonneg_right ((hcv x hxI').trans (h1 x))
          (abs_nonneg (deriv (f n) x - d x))
        rw [Real.norm_eq_abs, le_div_iff₀ hc]
        linarith
      have := intervalIntegral.norm_integral_le_of_norm_le_const_ae hb
      rw [← Real.norm_eq_abs]
      calc _ ≤ 1 / ((k : ℝ) + 1) / c * |y - a| := this
        _ ≤ 1 / ((k : ℝ) + 1) / c * (|y - a| + 1) := by gcongr; linarith
        _ < ε * c / (|y - a| + 1) / c * (|y - a| + 1) := by gcongr
        _ = ε := by field_simp
    exact tendsto_nhds_unique hlim1 hlim2
  -- `g` is locally Lipschitz
  have hgll : LocallyLipschitz g := by
    intro x
    obtain ⟨M, hM⟩ := hdloc (x - 1) (x + 1)
    refine ⟨M.toNNReal, Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [Real.dist_eq, Real.dist_eq, hgint z y]
    have hb : ∀ᵐ t, t ∈ Ι z y → ‖d t‖ ≤ M := by
      filter_upwards [hM] with t ht htI
      have : t ∈ Icc (x - 1) (x + 1) := by
        have := uIoc_subset_uIcc htI
        rw [uIcc, mem_Icc] at this
        constructor
        · exact le_trans (le_min hz.1 hy.1) this.1
        · exact le_trans this.2 (max_le hz.2 hy.2)
      rw [Real.norm_eq_abs]; exact ht this
    have := intervalIntegral.norm_integral_le_of_norm_le_const_ae hb
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal M) (abs_nonneg _))
  -- `g' = d` a.e.
  have hgd : ∀ᵐ y, deriv g y = d y := by
    have h := fun n : ℕ => (hdint (-(n : ℝ)) n).ae_hasDerivAt_integral
    filter_upwards [ae_all_iff.2 h] with y hy
    obtain ⟨n, hn⟩ := exists_nat_ge |y|
    have hyI : y ∈ uIcc (-(n : ℝ)) n := by
      rw [uIcc_of_le (by linarith [abs_nonneg y])]
      exact ⟨by linarith [neg_abs_le y], le_trans (le_abs_self y) hn⟩
    have h0I : (0 : ℝ) ∈ uIcc (-(n : ℝ)) n := by
      rw [uIcc_of_le (by linarith [abs_nonneg y])]
      exact ⟨by linarith [abs_nonneg y], by linarith [abs_nonneg y]⟩
    have hD := hy n hyI 0 h0I
    have he : g = fun x => g 0 + ∫ t in (0 : ℝ)..x, d t := by
      funext x; rw [← hgint 0 x]; ring
    rw [he]
    exact ((hasDerivAt_const y (g 0)).add hD).deriv.trans (zero_add _)
  refine ⟨g, hgll, fun η hη => ?_, fun η hη => ?_⟩
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
    refine ⟨N k, fun n hn => ?_⟩
    filter_upwards [hdb, hgd] with y hy hy'
    rw [hy']
    exact (hy k n hn).trans hk.le
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
    exact ⟨N k, fun n hn y => (hgb k n hn y).trans hk.le⟩


/-- The weight of `G'` in the `Y_γ` norm (both half-lines combined). -/
def c02_aux_WY (p γ : ℝ) (y : ℝ) : ℝ :=
  if 0 ≤ y then jb y ^ γ * jb y ^ (-1 / p) else jb y ^ γ * jb y

/-- `⟨0⟩ = 1`. -/
theorem c02_aux_jb_zero : jb 0 = 1 := by simp [jb]

/-- `W_Y` on `y ≤ 0`. -/
theorem c02_aux_WY_Iic {p γ y : ℝ} (hy : y ≤ 0) : c02_aux_WY p γ y = jb y ^ γ * jb y := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp [c02_aux_WY, c02_aux_jb_zero]
  · simp [c02_aux_WY, not_le.2 h]

/-- `W_Y` on `y ≥ 0`. -/
theorem c02_aux_WY_Ici {p γ y : ℝ} (hy : 0 ≤ y) :
    c02_aux_WY p γ y = jb y ^ γ * jb y ^ (-1 / p) := by
  simp [c02_aux_WY, hy]

/-- `‖G‖_{Y_γ} < η` gives the pointwise a.e. bound. -/
theorem c02_aux_Y_ae_of_lt {p γ : ℝ} {G : ℝ → ℝ} {η : ℝ} (hfin : Y_gamma_norm p γ G < ⊤)
    (h : yNorm p γ G < η) :
    ∀ᵐ y, jb y ^ γ * |G y| + c02_aux_WY p γ y * |deriv G y| ≤ η := by
  have hη : 0 < η := lt_of_le_of_lt ENNReal.toReal_nonneg h
  have hlt : Y_gamma_norm p γ G < ENNReal.ofReal η :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin.ne).2 h
  unfold Y_gamma_norm at hlt
  have h1 := lt_of_le_of_lt le_self_add hlt
  have h2 := lt_of_le_of_lt le_add_self hlt
  have hu : (univ : Set ℝ) = Ici 0 ∪ Iic 0 := by
    ext y; simp only [mem_univ, mem_union, mem_Ici, mem_Iic, true_iff]; exact le_total 0 y
  suffices hs : ∀ᵐ y ∂(volume.restrict (univ : Set ℝ)),
      jb y ^ γ * |G y| + c02_aux_WY p γ y * |deriv G y| ≤ η by simpa using hs
  rw [hu, ae_restrict_union_iff]
  constructor
  · filter_upwards [ae_le_essSup (μ := volume.restrict (Ici 0)) (f := fun y => ENNReal.ofReal
      (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖))), ae_restrict_mem measurableSet_Ici]
      with y hy hy0
    have := (ENNReal.ofReal_le_ofReal_iff hη.le).1 (hy.trans h1.le)
    rw [c02_aux_WY_Ici hy0]
    simp only [Real.norm_eq_abs] at this
    linarith
  · filter_upwards [ae_le_essSup (μ := volume.restrict (Iic 0)) (f := fun y => ENNReal.ofReal
      (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖))), ae_restrict_mem measurableSet_Iic]
      with y hy hy0
    have := (ENNReal.ofReal_le_ofReal_iff hη.le).1 (hy.trans h2.le)
    rw [c02_aux_WY_Iic hy0]
    simp only [Real.norm_eq_abs] at this
    linarith

/-- The pointwise a.e. bound gives `‖G‖_{Y_γ} ≤ 2η`. -/
theorem c02_aux_Y_norm_le_of_ae {p γ : ℝ} {G : ℝ → ℝ} {η : ℝ}
    (h : ∀ᵐ y, jb y ^ γ * |G y| + c02_aux_WY p γ y * |deriv G y| ≤ η) :
    Y_gamma_norm p γ G ≤ ENNReal.ofReal η + ENNReal.ofReal η := by
  unfold Y_gamma_norm
  gcongr
  · refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ici] with y hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    rw [c02_aux_WY_Ici hy0] at hy
    simp only [Real.norm_eq_abs]
    linarith
  · refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Iic] with y hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    rw [c02_aux_WY_Iic hy0] at hy
    simp only [Real.norm_eq_abs]
    linarith

/-- `⟨·⟩` is continuous. -/
theorem c02_aux_jb_continuous : Continuous jb := by
  unfold jb; fun_prop

/-- `⟨·⟩^a` is continuous. -/
theorem c02_aux_jb_rpow_continuous (a : ℝ) : Continuous fun y => jb y ^ a :=
  c02_aux_jb_continuous.rpow_const fun y => Or.inl (c02_aux_jb_pos y).ne'

/-- Completeness of `Y_γ` (sequential Cauchy criterion). -/
theorem c02_aux_Y_complete (P : parameters) (γ : ℝ) :
    ∀ u : ℕ → ℝ → ℝ, (∀ n, u n ∈ Y_gamma P.p γ) →
      (∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, yNorm P.p γ (u m - u n) < η) →
      ∃ G ∈ Y_gamma P.p γ, Tendsto (fun n => yNorm P.p γ (u n - G)) atTop (𝓝 0) := by
  have hax := c02_aux_Y_axioms P γ
  have hp : 0 < P.p := by linarith [P.hp_lo]
  intro u hu hC
  have hjp := fun y => c02_aux_jb_pos y
  have hj1 : ∀ y, 1 ≤ jb y := fun y => Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg y])
  obtain ⟨g, hgll, hgae, -⟩ := c02_aux_W1_complete (fun y => jb y ^ γ) (c02_aux_WY P.p γ)
    (fun y => jb y ^ γ) (fun y => jb y ^ γ * jb y ^ (-1 / P.p)) (c02_aux_jb_rpow_continuous γ)
    ((c02_aux_jb_rpow_continuous γ).mul (c02_aux_jb_rpow_continuous _))
    (fun y => Real.rpow_pos_of_pos (hjp y) _)
    (fun y => mul_pos (Real.rpow_pos_of_pos (hjp y) _) (Real.rpow_pos_of_pos (hjp y) _))
    (fun y => le_rfl) (fun y => by
      by_cases hy : 0 ≤ y
      · rw [c02_aux_WY_Ici hy]
      · rw [c02_aux_WY_Iic (le_of_lt (not_le.1 hy))]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (hjp y) _).le
        exact (Real.rpow_le_one_of_one_le_of_nonpos (hj1 y)
          (by rw [neg_div]; linarith [one_div_pos.2 hp])).trans (hj1 y))
    u (fun n => (hu n).1) (by
      intro η hη
      obtain ⟨N, hN⟩ := hC η hη
      refine ⟨N, fun m hm n hn => ?_⟩
      have hd := (hax.2.1 (u m) (hu m) _ (hax.2.2.1 (-1) (u n) (hu n)).1).1
      have hmn : u m + (-1 : ℝ) • u n = u m - u n := by simp [sub_eq_add_neg]
      rw [hmn] at hd
      filter_upwards [c02_aux_Y_ae_of_lt hd.2 (hN m hm n hn), c02_aux_ae_diff (hu m).1,
        c02_aux_ae_diff (hu n).1] with y hy h1 h2
      rw [show deriv (u m - u n) y = deriv (u m) y - deriv (u n) y from deriv_sub h1 h2] at hy
      simpa using hy)
  -- `u n - g` has small norm
  have hbound : ∀ η > 0, ∃ N : ℕ, ∀ n ≥ N, (u n - g) ∈ Y_gamma P.p γ ∧
      yNorm P.p γ (u n - g) ≤ 2 * η := by
    intro η hη
    obtain ⟨N, hN⟩ := hgae η hη
    refine ⟨N, fun n hn => ?_⟩
    have hle : Y_gamma_norm P.p γ (u n - g) ≤ ENNReal.ofReal η + ENNReal.ofReal η := by
      refine c02_aux_Y_norm_le_of_ae ?_
      filter_upwards [hN n hn, c02_aux_ae_diff (hu n).1, c02_aux_ae_diff hgll] with y hy h1 h2
      rw [show deriv (u n - g) y = deriv (u n) y - deriv g y from deriv_sub h1 h2]
      simpa using hy
    have hfin : ENNReal.ofReal η + ENNReal.ofReal η < ⊤ := by simp
    refine ⟨⟨(hu n).1.sub hgll, lt_of_le_of_lt hle hfin⟩, ?_⟩
    have := ENNReal.toReal_mono hfin.ne hle
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal hη.le] at this
    unfold yNorm; linarith
  obtain ⟨N₁, hN₁⟩ := hbound 1 one_pos
  have hgY : g ∈ Y_gamma P.p γ := by
    have h := (hax.2.1 (u N₁) (hu N₁) _ (hax.2.2.1 (-1) _ (hN₁ N₁ le_rfl).1).1).1
    have e : u N₁ + (-1 : ℝ) • (u N₁ - g) = g := by simp
    rwa [e] at h
  refine ⟨g, hgY, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hbound (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  simp only [Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (show 0 ≤ yNorm P.p γ (u n - g) from ENNReal.toReal_nonneg)]
  linarith [(hN n hn).2]

/-- Triangle inequality for one `X`-type essential supremum. -/
theorem c02_aux_essSup_X_add {μ : Measure ℝ} (a b c : ℝ → ℝ) (ha : ∀ y, 0 ≤ a y)
    (hb : ∀ y, 0 ≤ b y) (hc : ∀ y, 0 ≤ c y) {r s : ℝ → ℝ}
    (hd : ∀ᵐ y ∂μ, deriv (r + s) y = deriv r y + deriv s y ∧
      deriv (deriv (r + s)) y = deriv (deriv r) y + deriv (deriv s) y) :
    essSup (fun y => ENNReal.ofReal (a y * (‖(r + s) y‖ + b y * ‖deriv (r + s) y‖ +
        c y * ‖deriv (deriv (r + s)) y‖))) μ ≤
      essSup (fun y => ENNReal.ofReal (a y * (‖r y‖ + b y * ‖deriv r y‖ +
        c y * ‖deriv (deriv r) y‖))) μ +
      essSup (fun y => ENNReal.ofReal (a y * (‖s y‖ + b y * ‖deriv s y‖ +
        c y * ‖deriv (deriv s) y‖))) μ := by
  refine le_trans (essSup_mono_ae ?_) (ENNReal.essSup_add_le _ _)
  filter_upwards [hd] with y hy
  simp only [Pi.add_apply]
  have := ha y; have := hb y; have := hc y
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hy.1, hy.2]
  have h1 := norm_add_le (r y) (s y)
  have h2 := mul_le_mul_of_nonneg_left (norm_add_le (deriv r y) (deriv s y)) (hb y)
  have h3 := mul_le_mul_of_nonneg_left
    (norm_add_le (deriv (deriv r) y) (deriv (deriv s) y)) (hc y)
  have := mul_le_mul_of_nonneg_left (show ‖r y + s y‖ + b y * ‖deriv r y + deriv s y‖ +
    c y * ‖deriv (deriv r) y + deriv (deriv s) y‖ ≤
    (‖r y‖ + b y * ‖deriv r y‖ + c y * ‖deriv (deriv r) y‖) +
      (‖s y‖ + b y * ‖deriv s y‖ + c y * ‖deriv (deriv s) y‖) by linarith) (ha y)
  linarith

/-- Scaling of one `X`-type essential supremum. -/
theorem c02_aux_essSup_X_smul {μ : Measure ℝ} (a b c : ℝ → ℝ) (k : ℝ) (r : ℝ → ℝ) :
    essSup (fun y => ENNReal.ofReal (a y * (‖(k • r) y‖ + b y * ‖deriv (k • r) y‖ +
        c y * ‖deriv (deriv (k • r)) y‖))) μ =
      ENNReal.ofReal |k| * essSup (fun y => ENNReal.ofReal (a y * (‖r y‖ + b y * ‖deriv r y‖ +
        c y * ‖deriv (deriv r) y‖))) μ := by
  rw [← ENNReal.essSup_const_mul]
  congr 1; funext y
  have e : k • r = fun x => k * r x := rfl
  rw [e, deriv_const_mul_field', deriv_const_mul_field', ← ENNReal.ofReal_mul (abs_nonneg k)]
  congr 1
  simp only [norm_mul, Real.norm_eq_abs]
  ring

/-- `deriv (k • r) = k • deriv r`. -/
theorem c02_aux_deriv_smul (k : ℝ) (r : ℝ → ℝ) : deriv (k • r) = k • deriv r := by
  have e : k • r = fun x => k * r x := rfl
  rw [e, deriv_const_mul_field']; rfl

/-- The norm axioms of `X_γ`. -/
theorem c02_aux_X_axioms (P : parameters) (γ : ℝ) :
    (0 : ℝ → ℝ) ∈ X_gamma P.p γ ∧
    (∀ r ∈ X_gamma P.p γ, ∀ s ∈ X_gamma P.p γ,
      r + s ∈ X_gamma P.p γ ∧ xNorm P.p γ (r + s) ≤ xNorm P.p γ r + xNorm P.p γ s) ∧
    (∀ c : ℝ, ∀ r ∈ X_gamma P.p γ, c • r ∈ X_gamma P.p γ ∧ xNorm P.p γ (c • r) = |c| * xNorm P.p γ r) ∧
    (∀ r ∈ X_gamma P.p γ, xNorm P.p γ r = 0 → r = 0) := by
  have ha : ∀ y, 0 ≤ jb y ^ γ := fun y => (Real.rpow_pos_of_pos (c02_aux_jb_pos y) _).le
  have hb1 : ∀ y, 0 ≤ jb y ^ (-1 / P.p) := fun y => (Real.rpow_pos_of_pos (c02_aux_jb_pos y) _).le
  have hc1 : ∀ y, 0 ≤ jb y ^ (-2 / P.p) := fun y => (Real.rpow_pos_of_pos (c02_aux_jb_pos y) _).le
  have hb2 : ∀ y, 0 ≤ jb y := fun y => (c02_aux_jb_pos y).le
  have hc2 : ∀ y, 0 ≤ jb y ^ (2 : ℕ) := fun y => by positivity
  have hzero : X_gamma_norm P.p γ (0 : ℝ → ℝ) = 0 := by
    unfold X_gamma_norm
    simp [ENNReal.essSup_eq_zero_iff]
    exact ⟨Eventually.of_forall fun _ => rfl, Eventually.of_forall fun _ => rfl⟩
  have hdadd : ∀ r ∈ X_gamma P.p γ, ∀ s ∈ X_gamma P.p γ,
      deriv (r + s) = deriv r + deriv s := by
    intro r hr s hs
    funext y
    exact deriv_add ((hr.1.1.differentiable one_ne_zero) y) ((hs.1.1.differentiable one_ne_zero) y)
  have hadd : ∀ r ∈ X_gamma P.p γ, ∀ s ∈ X_gamma P.p γ,
      X_gamma_norm P.p γ (r + s) ≤ X_gamma_norm P.p γ r + X_gamma_norm P.p γ s := by
    intro r hr s hs
    have hd : ∀ᵐ y, deriv (r + s) y = deriv r y + deriv s y ∧
        deriv (deriv (r + s)) y = deriv (deriv r) y + deriv (deriv s) y := by
      filter_upwards [c02_aux_ae_diff hr.1.2, c02_aux_ae_diff hs.1.2] with y h1 h2
      rw [hdadd r hr s hs]
      exact ⟨rfl, deriv_add h1 h2⟩
    unfold X_gamma_norm
    calc _ ≤ (essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / P.p) *
              ‖deriv r y‖ + jb y ^ (-2 / P.p) * ‖deriv (deriv r) y‖))) (volume.restrict (Ici 0)) +
          essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖s y‖ + jb y ^ (-1 / P.p) *
              ‖deriv s y‖ + jb y ^ (-2 / P.p) * ‖deriv (deriv s) y‖))) (volume.restrict (Ici 0))) +
          (essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
              jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0)) +
          essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖s y‖ + jb y * ‖deriv s y‖ +
              jb y ^ (2 : ℕ) * ‖deriv (deriv s) y‖))) (volume.restrict (Iic 0))) :=
          add_le_add (c02_aux_essSup_X_add _ _ _ ha hb1 hc1 (ae_restrict_of_ae hd))
            (c02_aux_essSup_X_add _ _ _ ha hb2 hc2 (ae_restrict_of_ae hd))
      _ = _ := by ring
  have hd0 : deriv (0 : ℝ → ℝ) = fun _ => 0 := by funext y; simp
  refine ⟨⟨⟨contDiff_const, by rw [hd0]; exact LocallyLipschitz.const 0⟩, by rw [hzero]; simp⟩,
    fun r hr s hs => ?_, fun c r hr => ?_, fun r hr h => ?_⟩
  · have hl := hadd r hr s hs
    have hfin : X_gamma_norm P.p γ r + X_gamma_norm P.p γ s < ⊤ :=
      ENNReal.add_lt_top.2 ⟨hr.2, hs.2⟩
    refine ⟨⟨⟨hr.1.1.add hs.1.1, by rw [hdadd r hr s hs]; exact hr.1.2.add hs.1.2⟩,
      lt_of_le_of_lt hl hfin⟩, ?_⟩
    unfold xNorm
    rw [← ENNReal.toReal_add hr.2.ne hs.2.ne]
    exact ENNReal.toReal_mono hfin.ne hl
  · have hs : X_gamma_norm P.p γ (c • r) = ENNReal.ofReal |c| * X_gamma_norm P.p γ r := by
      unfold X_gamma_norm
      rw [c02_aux_essSup_X_smul, c02_aux_essSup_X_smul, mul_add]
    refine ⟨⟨⟨hr.1.1.const_smul c, by
      rw [c02_aux_deriv_smul]; exact (lipschitzWith_smul c).locallyLipschitz.comp hr.1.2⟩, ?_⟩, ?_⟩
    · rw [hs]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hr.2
    · unfold xNorm; rw [hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg c)]
  · have h0 : X_gamma_norm P.p γ r = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
      · exact h
      · exact absurd h hr.2.ne
    unfold X_gamma_norm at h0
    rw [add_eq_zero] at h0
    have h1 := c02_aux_essSup_zero _ (fun y => Real.rpow_pos_of_pos (c02_aux_jb_pos y) γ) _
      (fun y => add_nonneg (mul_nonneg (hb1 y) (norm_nonneg _)) (mul_nonneg (hc1 y) (norm_nonneg _)))
      r (by simpa only [add_assoc] using h0.1)
    have h2 := c02_aux_essSup_zero _ (fun y => Real.rpow_pos_of_pos (c02_aux_jb_pos y) γ) _
      (fun y => add_nonneg (mul_nonneg (hb2 y) (norm_nonneg _)) (mul_nonneg (hc2 y) (norm_nonneg _)))
      r (by simpa only [add_assoc] using h0.2)
    have hu : (univ : Set ℝ) = Ici 0 ∪ Iic 0 := by
      ext y; simp only [mem_univ, mem_union, mem_Ici, mem_Iic, true_iff]; exact le_total 0 y
    have hae : ∀ᵐ y ∂(volume.restrict (univ : Set ℝ)), r y = 0 := by
      rw [hu, ae_restrict_union_iff]; exact ⟨h1, h2⟩
    rw [Measure.restrict_univ] at hae
    exact (Continuous.ae_eq_iff_eq volume hr.1.1.continuous continuous_const).1 hae

/-- The weight of `r''` in the `X_γ` norm (both half-lines combined). -/
def c02_aux_WX (p γ : ℝ) (y : ℝ) : ℝ :=
  if 0 ≤ y then jb y ^ γ * jb y ^ (-2 / p) else jb y ^ γ * jb y ^ (2 : ℕ)

/-- `W_X` on `y ≤ 0`. -/
theorem c02_aux_WX_Iic {p γ y : ℝ} (hy : y ≤ 0) :
    c02_aux_WX p γ y = jb y ^ γ * jb y ^ (2 : ℕ) := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp [c02_aux_WX, c02_aux_jb_zero]
  · simp [c02_aux_WX, not_le.2 h]

/-- `W_X` on `y ≥ 0`. -/
theorem c02_aux_WX_Ici {p γ y : ℝ} (hy : 0 ≤ y) :
    c02_aux_WX p γ y = jb y ^ γ * jb y ^ (-2 / p) := by
  simp [c02_aux_WX, hy]

/-- `‖r‖_{X_γ} < η` gives the pointwise a.e. bound. -/
theorem c02_aux_X_ae_of_lt {p γ : ℝ} {r : ℝ → ℝ} {η : ℝ} (hfin : X_gamma_norm p γ r < ⊤)
    (h : xNorm p γ r < η) :
    ∀ᵐ y, jb y ^ γ * |r y| + c02_aux_WY p γ y * |deriv r y| +
      c02_aux_WX p γ y * |deriv (deriv r) y| ≤ η := by
  have hη : 0 < η := lt_of_le_of_lt ENNReal.toReal_nonneg h
  have hlt : X_gamma_norm p γ r < ENNReal.ofReal η :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin.ne).2 h
  unfold X_gamma_norm at hlt
  have h1 := lt_of_le_of_lt le_self_add hlt
  have h2 := lt_of_le_of_lt le_add_self hlt
  have hu : (univ : Set ℝ) = Ici 0 ∪ Iic 0 := by
    ext y; simp only [mem_univ, mem_union, mem_Ici, mem_Iic, true_iff]; exact le_total 0 y
  suffices hs : ∀ᵐ y ∂(volume.restrict (univ : Set ℝ)), jb y ^ γ * |r y| +
      c02_aux_WY p γ y * |deriv r y| + c02_aux_WX p γ y * |deriv (deriv r) y| ≤ η by
    simpa using hs
  rw [hu, ae_restrict_union_iff]
  constructor
  · filter_upwards [ae_le_essSup (μ := volume.restrict (Ici 0)) (f := fun y => ENNReal.ofReal
      (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ + jb y ^ (-2 / p) *
        ‖deriv (deriv r) y‖))), ae_restrict_mem measurableSet_Ici] with y hy hy0
    have := (ENNReal.ofReal_le_ofReal_iff hη.le).1 (hy.trans h1.le)
    rw [c02_aux_WY_Ici hy0, c02_aux_WX_Ici hy0]
    simp only [Real.norm_eq_abs] at this
    linarith
  · filter_upwards [ae_le_essSup (μ := volume.restrict (Iic 0)) (f := fun y => ENNReal.ofReal
      (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))),
      ae_restrict_mem measurableSet_Iic] with y hy hy0
    have := (ENNReal.ofReal_le_ofReal_iff hη.le).1 (hy.trans h2.le)
    rw [c02_aux_WY_Iic hy0, c02_aux_WX_Iic hy0]
    simp only [Real.norm_eq_abs] at this
    linarith

/-- The pointwise a.e. bound gives `‖r‖_{X_γ} ≤ 2η`. -/
theorem c02_aux_X_norm_le_of_ae {p γ : ℝ} {r : ℝ → ℝ} {η : ℝ}
    (h : ∀ᵐ y, jb y ^ γ * |r y| + c02_aux_WY p γ y * |deriv r y| +
      c02_aux_WX p γ y * |deriv (deriv r) y| ≤ η) :
    X_gamma_norm p γ r ≤ ENNReal.ofReal η + ENNReal.ofReal η := by
  unfold X_gamma_norm
  gcongr
  · refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ici] with y hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    rw [c02_aux_WY_Ici hy0, c02_aux_WX_Ici hy0] at hy
    simp only [Real.norm_eq_abs]
    linarith
  · refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Iic] with y hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    rw [c02_aux_WY_Iic hy0, c02_aux_WX_Iic hy0] at hy
    simp only [Real.norm_eq_abs]
    linarith

/-- Completeness of `X_γ` (sequential Cauchy criterion). -/
theorem c02_aux_X_complete (P : parameters) (γ : ℝ) :
    ∀ u : ℕ → ℝ → ℝ, (∀ n, u n ∈ X_gamma P.p γ) →
      (∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, xNorm P.p γ (u m - u n) < η) →
      ∃ r ∈ X_gamma P.p γ, Tendsto (fun n => xNorm P.p γ (u n - r)) atTop (𝓝 0) := by
  have hax := c02_aux_X_axioms P γ
  have hp : 0 < P.p := by linarith [P.hp_lo]
  intro u hu hC
  have hjp := fun y => c02_aux_jb_pos y
  have hj1 : ∀ y, 1 ≤ jb y := fun y => Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg y])
  have hdiff : ∀ n, Differentiable ℝ (u n) := fun n => (hu n).1.1.differentiable one_ne_zero
  have hsub : ∀ m n, u m - u n ∈ X_gamma P.p γ := by
    intro m n
    have hd := (hax.2.1 (u m) (hu m) _ (hax.2.2.1 (-1) (u n) (hu n)).1).1
    have hmn : u m + (-1 : ℝ) • u n = u m - u n := by simp [sub_eq_add_neg]
    rwa [hmn] at hd
  have hCa : ∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ᵐ y, jb y ^ γ * |u m y - u n y| +
      c02_aux_WY P.p γ y * |deriv (u m) y - deriv (u n) y| +
      c02_aux_WX P.p γ y * |deriv (deriv (u m)) y - deriv (deriv (u n)) y| ≤ η := by
    intro η hη
    obtain ⟨N, hN⟩ := hC η hη
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdf : deriv (u m - u n) = deriv (u m) - deriv (u n) := by
      funext y; exact deriv_sub (hdiff m y) (hdiff n y)
    filter_upwards [c02_aux_X_ae_of_lt (hsub m n).2 (hN m hm n hn), c02_aux_ae_diff (hu m).1.2,
      c02_aux_ae_diff (hu n).1.2] with y hy h1 h2
    rw [hdf, show deriv (deriv (u m) - deriv (u n)) y = deriv (deriv (u m)) y -
      deriv (deriv (u n)) y from deriv_sub h1 h2] at hy
    simpa using hy
  have hWYn : ∀ y, 0 ≤ c02_aux_WY P.p γ y := fun y => by
    unfold c02_aux_WY; split_ifs <;> have := hjp y <;> positivity
  have hWXn : ∀ y, 0 ≤ c02_aux_WX P.p γ y := fun y => by
    unfold c02_aux_WX; split_ifs <;> have := hjp y <;> positivity
  have hrp : ∀ y (a : ℝ), 0 < jb y ^ a := fun y a => Real.rpow_pos_of_pos (hjp y) a
  obtain ⟨h, hll, hhae, hhev⟩ := c02_aux_W1_complete (c02_aux_WY P.p γ) (c02_aux_WX P.p γ)
    (fun y => jb y ^ γ * jb y ^ (-1 / P.p)) (fun y => jb y ^ γ * jb y ^ (-2 / P.p))
    ((c02_aux_jb_rpow_continuous γ).mul (c02_aux_jb_rpow_continuous _))
    ((c02_aux_jb_rpow_continuous γ).mul (c02_aux_jb_rpow_continuous _))
    (fun y => mul_pos (hrp y _) (hrp y _)) (fun y => mul_pos (hrp y _) (hrp y _))
    (fun y => by
      by_cases hy : 0 ≤ y
      · rw [c02_aux_WY_Ici hy]
      · rw [c02_aux_WY_Iic (le_of_lt (not_le.1 hy))]
        refine mul_le_mul_of_nonneg_left ?_ (hrp y _).le
        exact (Real.rpow_le_one_of_one_le_of_nonpos (hj1 y)
          (by rw [neg_div]; linarith [one_div_pos.2 hp])).trans (hj1 y))
    (fun y => by
      by_cases hy : 0 ≤ y
      · rw [c02_aux_WX_Ici hy]
      · rw [c02_aux_WX_Iic (le_of_lt (not_le.1 hy))]
        refine mul_le_mul_of_nonneg_left ?_ (hrp y _).le
        exact (Real.rpow_le_one_of_one_le_of_nonpos (hj1 y)
          (by rw [neg_div]; linarith [div_pos (two_pos : (0 : ℝ) < 2) hp])).trans
          (one_le_pow₀ (hj1 y)))
    (fun n => deriv (u n)) (fun n => (hu n).1.2) (by
      intro η hη
      obtain ⟨N, hN⟩ := hCa η hη
      refine ⟨N, fun m hm n hn => ?_⟩
      filter_upwards [hN m hm n hn] with y hy
      have := mul_nonneg (hrp y γ).le (abs_nonneg (u m y - u n y))
      linarith)
  -- pointwise convergence of `u n`
  have hev : ∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ y, jb y ^ γ * |u m y - u n y| ≤ η := by
    intro η hη
    obtain ⟨N, hN⟩ := hCa η hη
    refine ⟨N, fun m hm n hn => c02_aux_le_of_ae (φ := fun y => jb y ^ γ * |u m y - u n y|)
      ((c02_aux_jb_rpow_continuous γ).mul (((hu m).1.1.continuous.sub
        (hu n).1.1.continuous).abs)) ?_⟩
    filter_upwards [hN m hm n hn] with y hy
    have := mul_nonneg (hWYn y) (abs_nonneg (deriv (u m) y - deriv (u n) y))
    have := mul_nonneg (hWXn y) (abs_nonneg (deriv (deriv (u m)) y - deriv (deriv (u n)) y))
    linarith
  have hcauchy : ∀ y, CauchySeq fun n => u n y := by
    intro y
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hev (ε * jb y ^ γ / 2) (by have := hrp y γ; positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have := hN n hn N le_rfl y
    have hj := hrp y γ
    by_contra hc; rw [not_lt] at hc
    nlinarith
  choose g hg using fun y => cauchySeq_tendsto_of_complete (hcauchy y)
  have hgb : ∀ η > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ y, jb y ^ γ * |u n y - g y| ≤ η := by
    intro η hη
    obtain ⟨N, hN⟩ := hev η hη
    refine ⟨N, fun n hn y => ?_⟩
    have ht : Tendsto (fun m => jb y ^ γ * |u n y - u m y|) atTop (𝓝 (jb y ^ γ * |u n y - g y|)) :=
      ((tendsto_const_nhds.sub (hg y)).abs).const_mul _
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N, fun m hm => hN n hn m hm y⟩)
  -- `g(y) - g(0) = ∫_0^y h`
  have hgint : ∀ y, g y - g 0 = ∫ x in (0 : ℝ)..y, h x := by
    intro y
    obtain ⟨c, hc, hcv⟩ := c02_aux_pos_lower ((c02_aux_jb_rpow_continuous γ).mul
      (c02_aux_jb_rpow_continuous (-1 / P.p))) (fun y => mul_pos (hrp y _) (hrp y _))
      (min 0 y) (max 0 y)
    have hlim1 : Tendsto (fun n => u n y - u n 0) atTop (𝓝 (g y - g 0)) := (hg y).sub (hg 0)
    have hlim2 : Tendsto (fun n => u n y - u n 0) atTop (𝓝 (∫ x in (0 : ℝ)..y, h x)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := hhev (ε * c / (|y| + 1) / 2) (by positivity)
      refine ⟨N, fun n hn => ?_⟩
      have hftc := c02_aux_ftc ((hu n).1.1.locallyLipschitz) 0 y
      rw [← hftc.1, Real.dist_eq, ← intervalIntegral.integral_sub hftc.2
        (hll.continuous.intervalIntegrable _ _)]
      have hb : ∀ᵐ x, x ∈ Ι (0 : ℝ) y → ‖deriv (u n) x - h x‖ ≤ ε * c / (|y| + 1) / 2 / c := by
        refine Eventually.of_forall fun x hxI => ?_
        have hxI' : x ∈ Icc (min 0 y) (max 0 y) := uIoc_subset_uIcc hxI
        have h1 := hN n hn x
        have h3 := mul_le_mul_of_nonneg_right (hcv x hxI') (abs_nonneg (deriv (u n) x - h x))
        simp only [Pi.mul_apply] at h1 h3
        rw [Real.norm_eq_abs, le_div_iff₀ hc]
        linarith
      have := intervalIntegral.norm_integral_le_of_norm_le_const_ae hb
      rw [← Real.norm_eq_abs]
      have hy0 : |y - 0| = |y| := by rw [sub_zero]
      rw [hy0] at this
      calc _ ≤ ε * c / (|y| + 1) / 2 / c * |y| := this
        _ ≤ ε * c / (|y| + 1) / 2 / c * (|y| + 1) := by gcongr; linarith
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    exact tendsto_nhds_unique hlim1 hlim2
  have hgd : ∀ y, HasDerivAt g (h y) y := by
    intro y
    have he : g = fun x => g 0 + ∫ t in (0 : ℝ)..x, h t := by
      funext x; rw [← hgint x]; ring
    rw [he]
    exact ((hasDerivAt_const y (g 0)).add (hll.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt).congr_deriv
      (zero_add _)
  have hderiv : deriv g = h := funext fun y => (hgd y).deriv
  have hgdiff : Differentiable ℝ g := fun y => (hgd y).differentiableAt
  have hgW : W2inftyLoc g :=
    ⟨contDiff_one_iff_deriv.2 ⟨hgdiff, by rw [hderiv]; exact hll.continuous⟩,
      by rw [hderiv]; exact hll⟩
  have hbound : ∀ η > 0, ∃ N : ℕ, ∀ n ≥ N, (u n - g) ∈ X_gamma P.p γ ∧
      xNorm P.p γ (u n - g) ≤ 2 * (2 * η) := by
    intro η hη
    obtain ⟨N₁, hN₁⟩ := hhae η hη
    obtain ⟨N₂, hN₂⟩ := hgb η hη
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hdf : deriv (u n - g) = deriv (u n) - h := by
      funext y; rw [← hderiv]; exact deriv_sub (hdiff n y) (hgdiff y)
    have hle : X_gamma_norm P.p γ (u n - g) ≤ ENNReal.ofReal (2 * η) + ENNReal.ofReal (2 * η) := by
      refine c02_aux_X_norm_le_of_ae ?_
      filter_upwards [hN₁ n (le_of_max_le_left hn), c02_aux_ae_diff (hu n).1.2,
        c02_aux_ae_diff hll] with y hy h1 h2
      rw [hdf, show deriv (deriv (u n) - h) y = deriv (deriv (u n)) y - deriv h y from
        deriv_sub h1 h2]
      have := hN₂ n (le_of_max_le_right hn) y
      simp only [Pi.sub_apply]
      linarith
    have hfin : ENNReal.ofReal (2 * η) + ENNReal.ofReal (2 * η) < ⊤ :=
      ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
    refine ⟨⟨⟨(hu n).1.1.sub hgW.1, by rw [hdf]; exact (hu n).1.2.sub hll⟩,
      lt_of_le_of_lt hle hfin⟩, ?_⟩
    have := ENNReal.toReal_mono hfin.ne hle
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
    unfold xNorm; linarith
  obtain ⟨N₁, hN₁⟩ := hbound 1 one_pos
  have hgX : g ∈ X_gamma P.p γ := by
    have h' := (hax.2.1 (u N₁) (hu N₁) _ (hax.2.2.1 (-1) _ (hN₁ N₁ le_rfl).1).1).1
    have e : u N₁ + (-1 : ℝ) • (u N₁ - g) = g := by simp
    rwa [e] at h'
  refine ⟨g, hgX, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hbound (ε / 5) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  simp only [Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (show 0 ≤ xNorm P.p γ (u n - g) from ENNReal.toReal_nonneg)]
  linarith [(hN n hn).2]
/-- Blueprint: lem:c02_X_gamma_banach.  `(X_γ, ‖·‖_{X_γ})` is a real Banach space: a linear
subspace of `ℝ → ℝ` on which `xNorm` is a norm, and complete (every Cauchy sequence converges). -/
theorem c02_X_gamma_banach (P : parameters) (γ : ℝ) :
    (0 : ℝ → ℝ) ∈ X_gamma P.p γ ∧
    (∀ r ∈ X_gamma P.p γ, ∀ s ∈ X_gamma P.p γ,
      r + s ∈ X_gamma P.p γ ∧ xNorm P.p γ (r + s) ≤ xNorm P.p γ r + xNorm P.p γ s) ∧
    (∀ c : ℝ, ∀ r ∈ X_gamma P.p γ, c • r ∈ X_gamma P.p γ ∧ xNorm P.p γ (c • r) = |c| * xNorm P.p γ r) ∧
    (∀ r ∈ X_gamma P.p γ, xNorm P.p γ r = 0 → r = 0) ∧
    (∀ u : ℕ → ℝ → ℝ, (∀ n, u n ∈ X_gamma P.p γ) →
      (∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, xNorm P.p γ (u m - u n) < η) →
      ∃ r ∈ X_gamma P.p γ, Tendsto (fun n => xNorm P.p γ (u n - r)) atTop (𝓝 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := c02_aux_X_axioms P γ
  exact ⟨h1, h2, h3, h4, c02_aux_X_complete P γ⟩

/-- Blueprint: lem:c02_Y_gamma_banach.  `(Y_γ, ‖·‖_{Y_γ})` is a real Banach space. -/
theorem c02_Y_gamma_banach (P : parameters) (γ : ℝ) :
    (0 : ℝ → ℝ) ∈ Y_gamma P.p γ ∧
    (∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ,
      G + H ∈ Y_gamma P.p γ ∧ yNorm P.p γ (G + H) ≤ yNorm P.p γ G + yNorm P.p γ H) ∧
    (∀ c : ℝ, ∀ G ∈ Y_gamma P.p γ, c • G ∈ Y_gamma P.p γ ∧ yNorm P.p γ (c • G) = |c| * yNorm P.p γ G) ∧
    (∀ G ∈ Y_gamma P.p γ, yNorm P.p γ G = 0 → G = 0) ∧
    (∀ u : ℕ → ℝ → ℝ, (∀ n, u n ∈ Y_gamma P.p γ) →
      (∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, yNorm P.p γ (u m - u n) < η) →
      ∃ G ∈ Y_gamma P.p γ, Tendsto (fun n => yNorm P.p γ (u n - G)) atTop (𝓝 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := c02_aux_Y_axioms P γ
  exact ⟨h1, h2, h3, h4, c02_aux_Y_complete P γ⟩

/-! ### Norm algebra in `X_γ`, `Y_γ` (consequences of lem:c02_X_gamma_banach, lem:c02_Y_gamma_banach) -/

section NormAlgebra

variable (P : parameters) {γ : ℝ}

/-- `‖·‖_{Y_γ} ≥ 0`. -/
theorem c02_aux_yNorm_nonneg (G : ℝ → ℝ) : 0 ≤ yNorm P.p γ G := ENNReal.toReal_nonneg

/-- `‖·‖_{X_γ} ≥ 0`. -/
theorem c02_aux_xNorm_nonneg (r : ℝ → ℝ) : 0 ≤ xNorm P.p γ r := ENNReal.toReal_nonneg

/-- `0 ∈ Y_γ`. -/
theorem c02_aux_Y_zero : (0 : ℝ → ℝ) ∈ Y_gamma P.p γ := (c02_Y_gamma_banach P γ).1

/-- `0 ∈ X_γ`. -/
theorem c02_aux_X_zero : (0 : ℝ → ℝ) ∈ X_gamma P.p γ := (c02_X_gamma_banach P γ).1

/-- Sums in `Y_γ`. -/
theorem c02_aux_Y_add {G H : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) (hH : H ∈ Y_gamma P.p γ) :
    G + H ∈ Y_gamma P.p γ ∧ yNorm P.p γ (G + H) ≤ yNorm P.p γ G + yNorm P.p γ H :=
  (c02_Y_gamma_banach P γ).2.1 G hG H hH

/-- Sums in `X_γ`. -/
theorem c02_aux_X_add {G H : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) (hH : H ∈ X_gamma P.p γ) :
    G + H ∈ X_gamma P.p γ ∧ xNorm P.p γ (G + H) ≤ xNorm P.p γ G + xNorm P.p γ H :=
  (c02_X_gamma_banach P γ).2.1 G hG H hH

/-- Scalar multiples in `Y_γ`. -/
theorem c02_aux_Y_smul (c : ℝ) {G : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) :
    c • G ∈ Y_gamma P.p γ ∧ yNorm P.p γ (c • G) = |c| * yNorm P.p γ G :=
  (c02_Y_gamma_banach P γ).2.2.1 c G hG

/-- Scalar multiples in `X_γ`. -/
theorem c02_aux_X_smul (c : ℝ) {G : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) :
    c • G ∈ X_gamma P.p γ ∧ xNorm P.p γ (c • G) = |c| * xNorm P.p γ G :=
  (c02_X_gamma_banach P γ).2.2.1 c G hG

/-- Negation in `Y_γ`. -/
theorem c02_aux_Y_neg {G : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) :
    -G ∈ Y_gamma P.p γ ∧ yNorm P.p γ (-G) = yNorm P.p γ G := by
  have := c02_aux_Y_smul P (-1) hG
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using this

/-- Negation in `X_γ`. -/
theorem c02_aux_X_neg {G : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) :
    -G ∈ X_gamma P.p γ ∧ xNorm P.p γ (-G) = xNorm P.p γ G := by
  have := c02_aux_X_smul P (-1) hG
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using this

/-- Differences in `Y_γ`. -/
theorem c02_aux_Y_sub {G H : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) (hH : H ∈ Y_gamma P.p γ) :
    G - H ∈ Y_gamma P.p γ ∧ yNorm P.p γ (G - H) ≤ yNorm P.p γ G + yNorm P.p γ H := by
  rw [sub_eq_add_neg]
  obtain ⟨h1, h2⟩ := c02_aux_Y_neg P hH
  obtain ⟨h3, h4⟩ := c02_aux_Y_add P hG h1
  exact ⟨h3, h4.trans (by rw [h2])⟩

/-- Differences in `X_γ`. -/
theorem c02_aux_X_sub {G H : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) (hH : H ∈ X_gamma P.p γ) :
    G - H ∈ X_gamma P.p γ ∧ xNorm P.p γ (G - H) ≤ xNorm P.p γ G + xNorm P.p γ H := by
  rw [sub_eq_add_neg]
  obtain ⟨h1, h2⟩ := c02_aux_X_neg P hH
  obtain ⟨h3, h4⟩ := c02_aux_X_add P hG h1
  exact ⟨h3, h4.trans (by rw [h2])⟩

/-- Symmetry of the `Y_γ` distance. -/
theorem c02_aux_Y_sub_comm {G H : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) (hH : H ∈ Y_gamma P.p γ) :
    yNorm P.p γ (G - H) = yNorm P.p γ (H - G) := by
  rw [← neg_sub]; exact (c02_aux_Y_neg P (c02_aux_Y_sub P hH hG).1).2

/-- Symmetry of the `X_γ` distance. -/
theorem c02_aux_X_sub_comm {G H : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) (hH : H ∈ X_gamma P.p γ) :
    xNorm P.p γ (G - H) = xNorm P.p γ (H - G) := by
  rw [← neg_sub]; exact (c02_aux_X_neg P (c02_aux_X_sub P hH hG).1).2

/-- Triangle inequality for the `Y_γ` distance. -/
theorem c02_aux_Y_tri {G H K : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) (hH : H ∈ Y_gamma P.p γ)
    (hK : K ∈ Y_gamma P.p γ) :
    yNorm P.p γ (G - K) ≤ yNorm P.p γ (G - H) + yNorm P.p γ (H - K) := by
  have := (c02_aux_Y_add P (c02_aux_Y_sub P hG hH).1 (c02_aux_Y_sub P hH hK).1).2
  rwa [sub_add_sub_cancel] at this

/-- Triangle inequality for the `X_γ` distance. -/
theorem c02_aux_X_tri {G H K : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) (hH : H ∈ X_gamma P.p γ)
    (hK : K ∈ X_gamma P.p γ) :
    xNorm P.p γ (G - K) ≤ xNorm P.p γ (G - H) + xNorm P.p γ (H - K) := by
  have := (c02_aux_X_add P (c02_aux_X_sub P hG hH).1 (c02_aux_X_sub P hH hK).1).2
  rwa [sub_add_sub_cancel] at this

/-- Reverse triangle inequality in `Y_γ`: `‖G‖ ≤ ‖G - H‖ + ‖H‖`. -/
theorem c02_aux_Y_le_sub_add {G H : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) (hH : H ∈ Y_gamma P.p γ) :
    yNorm P.p γ G ≤ yNorm P.p γ (G - H) + yNorm P.p γ H := by
  have := (c02_aux_Y_add P (c02_aux_Y_sub P hG hH).1 hH).2
  rwa [sub_add_cancel] at this

/-- Reverse triangle inequality in `X_γ`: `‖G‖ ≤ ‖G - H‖ + ‖H‖`. -/
theorem c02_aux_X_le_sub_add {G H : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) (hH : H ∈ X_gamma P.p γ) :
    xNorm P.p γ G ≤ xNorm P.p γ (G - H) + xNorm P.p γ H := by
  have := (c02_aux_X_add P (c02_aux_X_sub P hG hH).1 hH).2
  rwa [sub_add_cancel] at this

/-- `‖0‖_{X_γ} = 0`. -/
theorem c02_aux_xNorm_zero : xNorm P.p γ (0 : ℝ → ℝ) = 0 := by
  have := (c02_aux_X_smul P 0 (c02_aux_X_zero P (γ := γ))).2
  simpa using this

/-- Definiteness of the `X_γ` distance. -/
theorem c02_aux_X_eq_of_dist {G H : ℝ → ℝ} (hG : G ∈ X_gamma P.p γ) (hH : H ∈ X_gamma P.p γ)
    (h : xNorm P.p γ (G - H) = 0) : G = H :=
  sub_eq_zero.1 ((c02_X_gamma_banach P γ).2.2.2.1 _ (c02_aux_X_sub P hG hH).1 h)

/-- Definiteness of the `Y_γ` distance. -/
theorem c02_aux_Y_eq_of_dist {G H : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) (hH : H ∈ Y_gamma P.p γ)
    (h : yNorm P.p γ (G - H) = 0) : G = H :=
  sub_eq_zero.1 ((c02_Y_gamma_banach P γ).2.2.2.1 _ (c02_aux_Y_sub P hG hH).1 h)

/-- Linear combinations in `Y_γ`. -/
theorem c02_aux_Y_lin (a b : ℝ) {G H : ℝ → ℝ} (hG : G ∈ Y_gamma P.p γ) (hH : H ∈ Y_gamma P.p γ) :
    (fun x => a * G x + b * H x) ∈ Y_gamma P.p γ ∧
      yNorm P.p γ (fun x => a * G x + b * H x) ≤ |a| * yNorm P.p γ G + |b| * yNorm P.p γ H := by
  obtain ⟨h1, h2⟩ := c02_aux_Y_smul P a hG
  obtain ⟨h3, h4⟩ := c02_aux_Y_smul P b hH
  obtain ⟨h5, h6⟩ := c02_aux_Y_add P h1 h3
  exact ⟨h5, h6.trans (by rw [h2, h4])⟩

end NormAlgebra

/-- Blueprint: lem:c02_X_inclusion.  `γ ≤ γ'` ⟹ `X_{γ'} ⊆ X_γ` with `‖r‖_{X_γ} ≤ ‖r‖_{X_{γ'}}`. -/
theorem c02_X_inclusion (P : parameters) {γ γ' : ℝ} (h : γ ≤ γ') :
    X_gamma P.p γ' ⊆ X_gamma P.p γ ∧ ∀ r ∈ X_gamma P.p γ', xNorm P.p γ r ≤ xNorm P.p γ' r := by
  have key : ∀ r : ℝ → ℝ, X_gamma_norm P.p γ r ≤ X_gamma_norm P.p γ' r := by
    intro r
    unfold X_gamma_norm
    gcongr ?_ + ?_ <;> refine essSup_mono_ae (ae_of_all _ fun y => ENNReal.ofReal_le_ofReal ?_) <;>
      have := c02_aux_jb_pos y <;>
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (c02_aux_one_le_jb y) h)
        (by positivity)
  exact ⟨fun r hr => ⟨hr.1, lt_of_le_of_lt (key r) hr.2⟩,
    fun r hr => ENNReal.toReal_mono hr.2.ne (key r)⟩

/-- Blueprint: lem:c02_Y_inclusion.  `γ ≤ γ'` ⟹ `Y_{γ'} ⊆ Y_γ` with `‖G‖_{Y_γ} ≤ ‖G‖_{Y_{γ'}}`. -/
theorem c02_Y_inclusion (P : parameters) {γ γ' : ℝ} (h : γ ≤ γ') :
    Y_gamma P.p γ' ⊆ Y_gamma P.p γ ∧ ∀ G ∈ Y_gamma P.p γ', yNorm P.p γ G ≤ yNorm P.p γ' G := by
  have key : ∀ G : ℝ → ℝ, Y_gamma_norm P.p γ G ≤ Y_gamma_norm P.p γ' G := by
    intro G
    unfold Y_gamma_norm
    gcongr ?_ + ?_ <;> refine essSup_mono_ae (ae_of_all _ fun y => ENNReal.ofReal_le_ofReal ?_) <;>
      have := c02_aux_jb_pos y <;>
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (c02_aux_one_le_jb y) h)
        (by positivity)
  exact ⟨fun G hG => ⟨hG.1, lt_of_le_of_lt (key G) hG.2⟩,
    fun G hG => ENNReal.toReal_mono hG.2.ne (key G)⟩

/-- `⟨y⟩ ≤ 1 + |y|`. -/
theorem c02_aux_jb_le (y : ℝ) : jb y ≤ 1 + |y| := by
  unfold jb
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg y, sq_abs y]

/-- Schwartz decay in the form used for `Y_γ`. -/
theorem c02_aux_schwartz_bound (G : SchwartzMap ℝ ℝ) (a : ℝ) :
    ∃ K, ∀ y, jb y ^ a * (|G y| + |deriv (⇑G) y|) ≤ K := by
  set k := ⌈a⌉₊
  set K0 := 2 ^ (k, 1).1 * (Finset.Iic (k, 1)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) G
  refine ⟨2 * K0, fun y => ?_⟩
  have h0 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 1)) (k := k) (n := 0)
    le_rfl (by norm_num) G y
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 1)) (k := k) (n := 1)
    le_rfl le_rfl G y
  rw [norm_iteratedFDeriv_zero] at h0
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] at h1
  simp only [Real.norm_eq_abs] at h0 h1
  have hj : jb y ^ a ≤ (1 + |y|) ^ k := by
    calc jb y ^ a ≤ jb y ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (c02_aux_one_le_jb y) (Nat.le_ceil a)
      _ = jb y ^ k := Real.rpow_natCast _ _
      _ ≤ (1 + |y|) ^ k := pow_le_pow_left₀ (c02_aux_jb_pos y).le (c02_aux_jb_le y) k
  have hn : 0 ≤ |G y| + |deriv (⇑G) y| := by positivity
  calc jb y ^ a * (|G y| + |deriv (⇑G) y|) ≤ (1 + |y|) ^ k * (|G y| + |deriv (⇑G) y|) :=
        mul_le_mul_of_nonneg_right hj hn
    _ = (1 + |y|) ^ k * |G y| + (1 + |y|) ^ k * |deriv (⇑G) y| := by ring
    _ ≤ 2 * K0 := by linarith

/-- Blueprint: lem:c02_schwartz_in_Y.  A real Schwartz function lies in every `Y_γ`, with
`‖G‖_{Y_γ} ≤ 2 sup_y ⟨y⟩^{|γ|+2}(|G|+|G'|) < ∞`. -/
theorem c02_schwartz_in_Y (P : parameters) (G : SchwartzMap ℝ ℝ) (γ : ℝ) :
    (⇑G : ℝ → ℝ) ∈ Y_gamma P.p γ ∧
    BddAbove (Set.range fun y => jb y ^ (|γ| + 2) * (|G y| + |deriv (⇑G) y|)) ∧
    yNorm P.p γ (⇑G : ℝ → ℝ) ≤ 2 * ⨆ y, jb y ^ (|γ| + 2) * (|G y| + |deriv (⇑G) y|) := by
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨K, hK⟩ := c02_aux_schwartz_bound G (|γ| + 2)
  have hbdd : BddAbove (Set.range fun y => jb y ^ (|γ| + 2) * (|G y| + |deriv (⇑G) y|)) :=
    ⟨K, by rintro _ ⟨y, rfl⟩; exact hK y⟩
  set S := ⨆ y, jb y ^ (|γ| + 2) * (|G y| + |deriv (⇑G) y|) with hS
  have hle : ∀ y, jb y ^ (|γ| + 2) * (|G y| + |deriv (⇑G) y|) ≤ S := fun y => le_ciSup hbdd y
  have hS0 : 0 ≤ S := le_trans (by have := c02_aux_jb_pos 0; positivity) (hle 0)
  have hp1 : ∀ y, jb y ^ γ * (‖G y‖ + jb y ^ (-1 / P.p) * ‖deriv (⇑G) y‖) ≤ S := by
    intro y
    have hj := c02_aux_one_le_jb y
    have hjp := c02_aux_jb_pos y
    have e1 : jb y ^ γ ≤ jb y ^ (|γ| + 2) :=
      Real.rpow_le_rpow_of_exponent_le hj (by linarith [le_abs_self γ])
    have e2 : jb y ^ (-1 / P.p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hj (by rw [neg_div]; linarith [one_div_pos.2 hp])
    simp only [Real.norm_eq_abs]
    refine le_trans ?_ (hle y)
    have : |G y| + jb y ^ (-1 / P.p) * |deriv (⇑G) y| ≤ |G y| + |deriv (⇑G) y| := by
      have := mul_le_mul_of_nonneg_right e2 (abs_nonneg (deriv (⇑G) y)); linarith
    exact mul_le_mul e1 this (by positivity) (by positivity)
  have hp2 : ∀ y, jb y ^ γ * (‖G y‖ + jb y * ‖deriv (⇑G) y‖) ≤ S := by
    intro y
    have hj := c02_aux_one_le_jb y
    have hjp := c02_aux_jb_pos y
    have e1 : jb y ^ γ * jb y ≤ jb y ^ (|γ| + 2) := by
      rw [← Real.rpow_add_one hjp.ne']
      exact Real.rpow_le_rpow_of_exponent_le hj (by linarith [le_abs_self γ])
    simp only [Real.norm_eq_abs]
    refine le_trans ?_ (hle y)
    have hγp : 0 ≤ jb y ^ γ := by positivity
    have : jb y ^ γ * (|G y| + jb y * |deriv (⇑G) y|) ≤
        jb y ^ γ * jb y * (|G y| + |deriv (⇑G) y|) := by
      have := mul_le_mul_of_nonneg_left (show |G y| ≤ jb y * |G y| by nlinarith [abs_nonneg (G y)]) hγp
      nlinarith [abs_nonneg (deriv (⇑G) y)]
    exact this.trans (mul_le_mul_of_nonneg_right e1 (by positivity))
  have hn : Y_gamma_norm P.p γ (⇑G) ≤ ENNReal.ofReal S + ENNReal.ofReal S := by
    unfold Y_gamma_norm
    gcongr
    · exact essSup_le_of_ae_le _ (ae_of_all _ fun y => ENNReal.ofReal_le_ofReal (hp1 y))
    · exact essSup_le_of_ae_le _ (ae_of_all _ fun y => ENNReal.ofReal_le_ofReal (hp2 y))
  have hfin : ENNReal.ofReal S + ENNReal.ofReal S < ⊤ := by simp
  refine ⟨⟨?_, lt_of_le_of_lt hn hfin⟩, hbdd, ?_⟩
  · have hd : Differentiable ℝ (⇑G) := G.differentiable
    refine (lipschitzWith_of_nnnorm_deriv_le (C := (SchwartzMap.seminorm ℝ 0 1 G).toNNReal) hd
      fun x => ?_).locallyLipschitz
    have := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ G 1 x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] at this
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    exact this
  · unfold yNorm
    have := ENNReal.toReal_mono hfin.ne hn
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal hS0] at this
    linarith

/-! ### `ℓ`, `G_±`, `G_μ`, `Π` -/

/-! ### The symbols `ĝ_s` and the functions `G_±` -/

/-- `χ₊` is smooth. -/
theorem c02_aux_chiPlus_contDiff : ContDiff ℝ (⊤ : ℕ∞) chiPlus := by
  unfold chiPlus
  exact Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

/-- `χ₊' = 0` on `(-∞,1)`. -/
theorem c02_aux_deriv_chiPlus_lt {ξ : ℝ} (h : ξ < 1) : deriv chiPlus ξ = 0 := by
  have : chiPlus =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with x hx
    unfold chiPlus
    exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Iio.1 hx])
  rw [this.deriv_eq]; simp

/-- `χ₊' = 0` on `(2,∞)`. -/
theorem c02_aux_deriv_chiPlus_gt {ξ : ℝ} (h : 2 < ξ) : deriv chiPlus ξ = 0 := by
  have : chiPlus =ᶠ[𝓝 ξ] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with x hx
    unfold chiPlus
    exact Real.smoothTransition.one_of_one_le (by linarith [mem_Ioi.1 hx])
  rw [this.deriv_eq]; simp

/-- `g(ξ) = χ₊'(ξ)/ξ` is continuous. -/
theorem c02_aux_g_continuous : Continuous fun ξ : ℝ => deriv chiPlus ξ / ξ := by
  have hd : Continuous (deriv chiPlus) :=
    c02_aux_chiPlus_contDiff.continuous_deriv (by norm_num)
  rw [continuous_iff_continuousAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst hξ
    have : (fun ξ : ℝ => deriv chiPlus ξ / ξ) =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
      rw [c02_aux_deriv_chiPlus_lt hx, zero_div]
    exact (continuousAt_congr this).2 continuousAt_const
  · exact hd.continuousAt.div continuousAt_id hξ

/-- `g = 0` outside `[1,2]`. -/
theorem c02_aux_g_zero {ξ : ℝ} (h : ξ ∉ Icc (1 : ℝ) 2) : deriv chiPlus ξ / ξ = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · rw [c02_aux_deriv_chiPlus_lt h, zero_div]
  · rw [c02_aux_deriv_chiPlus_gt h, zero_div]

/-- Splitting of the Hermitian symbol `ĝ_s` into its positive and negative frequency parts. -/
theorem c02_aux_G_pm_hat_split (p : ℝ) (s : ℂ) : G_pm_hat p s = fun ξ =>
    s * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) +
    (starRingEnd ℂ) (s * ((deriv chiPlus (-ξ) / (-ξ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (Phi0 p (-ξ) : ℂ)))) := by
  funext ξ
  unfold G_pm_hat
  split_ifs with h
  · have : deriv chiPlus (-ξ) / (-ξ) = 0 := c02_aux_g_zero (by
      simp only [mem_Icc, not_and_or, not_le]; left; linarith)
    simp [this]
  · have : deriv chiPlus ξ / ξ = 0 := c02_aux_g_zero (by
      simp only [mem_Icc, not_and_or, not_le]; left; linarith)
    simp [this]

/-- `ĝ_s` is continuous with compact support. -/
theorem c02_aux_G_pm_hat_cont {p : ℝ} (hp : 0 < p) (s : ℂ) :
    Continuous (G_pm_hat p s) ∧ HasCompactSupport (G_pm_hat p s) := by
  rw [c02_aux_G_pm_hat_split]
  have hΦ : Continuous (Phi0 p) := by
    unfold Phi0
    exact (continuous_id.mul (continuous_abs.rpow_const fun _ => Or.inr hp.le)).div_const _
  have hg := c02_aux_g_continuous
  refine ⟨?_, ?_⟩
  · refine Continuous.add ?_ ?_
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp hg)).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hΦ)).neg)
    · refine Complex.continuous_conj.comp ?_
      exact (continuous_const.mul (Complex.continuous_ofReal.comp (hg.comp continuous_neg))).mul
        (Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (hΦ.comp continuous_neg))).neg)
  · refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun ξ hξ => ?_
    simp only [mem_Icc, not_and_or, not_le] at hξ
    have h1 : deriv chiPlus ξ / ξ = 0 := c02_aux_g_zero (by
      simp only [mem_Icc, not_and_or, not_le]; rcases hξ with h | h
      · left; linarith
      · right; linarith)
    have h2 : deriv chiPlus (-ξ) / (-ξ) = 0 := c02_aux_g_zero (by
      simp only [mem_Icc, not_and_or, not_le]; rcases hξ with h | h
      · right; linarith
      · left; linarith)
    simp [h1, h2]

/-- `ℝ`-linearity of `s ↦ ĝ_s`. -/
theorem c02_aux_G_pm_hat_lin (p : ℝ) (s : ℂ) (ξ : ℝ) :
    G_pm_hat p s ξ = (s.re : ℂ) * G_pm_hat p 1 ξ + (s.im : ℂ) * G_pm_hat p Complex.I ξ := by
  unfold G_pm_hat
  split_ifs with h
  · conv_lhs => rw [← Complex.re_add_im s]
    ring
  · simp only [map_mul, Complex.conj_I, one_mul]
    conv_lhs => rw [← Complex.re_add_im s]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring

/-- `ℝ`-linearity of `s ↦ (ĝ_s)^∨`. -/
theorem c02_aux_invF_G_pm_lin {p : ℝ} (hp : 0 < p) (s : ℂ) (y : ℝ) :
    invFourierT (G_pm_hat p s) y = (s.re : ℂ) * invFourierT (G_pm_hat p 1) y +
      (s.im : ℂ) * invFourierT (G_pm_hat p Complex.I) y := by
  have hint : ∀ t : ℂ, Integrable fun ξ : ℝ =>
      G_pm_hat p t ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
    intro t
    obtain ⟨hc, hs⟩ := c02_aux_G_pm_hat_cont hp t
    refine Continuous.integrable_of_hasCompactSupport ?_ (hs.mul_right)
    exact hc.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  unfold invFourierT
  have e : (fun ξ : ℝ => G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) =
      fun ξ => (s.re : ℂ) * (G_pm_hat p 1 ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) +
        (s.im : ℂ) * (G_pm_hat p Complex.I ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := by
    funext ξ; rw [c02_aux_G_pm_hat_lin]; ring
  rw [e, integral_add ((hint 1).const_mul _) ((hint _).const_mul _), integral_const_mul,
    integral_const_mul]
  ring

/-- The positive-frequency part `A_s(ξ) = s χ₊'(ξ)/ξ e^{-iΦ₀(ξ)}` of `ĝ_s`. -/
def c02_aux_Apart (p : ℝ) (s : ℂ) (ξ : ℝ) : ℂ :=
  s * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))

/-- `ĝ_s(ξ) = A_s(ξ) + conj A_s(-ξ)`. -/
theorem c02_aux_G_pm_hat_eq_A (p : ℝ) (s : ℂ) :
    G_pm_hat p s = fun ξ => c02_aux_Apart p s ξ + conj (c02_aux_Apart p s (-ξ)) := by
  rw [c02_aux_G_pm_hat_split]; rfl

/-- Hermitian symmetry `ĝ_s(-ξ) = conj ĝ_s(ξ)`. -/
theorem c02_aux_G_pm_hat_herm (p : ℝ) (s : ℂ) (ξ : ℝ) :
    G_pm_hat p s (-ξ) = conj (G_pm_hat p s ξ) := by
  rw [c02_aux_G_pm_hat_eq_A]
  simp only [neg_neg, map_add, Complex.conj_conj]
  ring

/-- The inverse transform of `ĝ_s` is real. -/
theorem c02_aux_invF_real {p : ℝ} (s : ℂ) (y : ℝ) : (invFourierT (G_pm_hat p s) y).im = 0 := by
  have hJ : conj (∫ ξ, G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) =
      ∫ ξ, G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
    rw [← integral_conj]
    have e : (fun ξ : ℝ => conj (G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))) =
        fun ξ => (fun η : ℝ => G_pm_hat p s η * Complex.exp (Complex.I * (y : ℂ) * (η : ℂ))) (-ξ) := by
      funext ξ
      simp only [map_mul, ← Complex.exp_conj, c02_aux_G_pm_hat_herm, Complex.conj_I,
        Complex.conj_ofReal, Complex.ofReal_neg]
      ring_nf
    rw [e]
    exact integral_neg_eq_self (fun η : ℝ => G_pm_hat p s η * Complex.exp (Complex.I * (y : ℂ) * (η : ℂ))) volume
  unfold invFourierT
  rw [Complex.mul_im, Complex.inv_im, Complex.ofReal_im, neg_zero, zero_div, zero_mul, add_zero,
    (Complex.conj_eq_iff_im).1 hJ, mul_zero]

/-- `A_s` is smooth (it vanishes for `ξ < 1`, and `Φ₀` is smooth on `(0,∞)`). -/
theorem c02_aux_Apart_smooth {p : ℝ} (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (c02_aux_Apart p s) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv chiPlus) := (contDiff_infty_iff_deriv.mp c02_aux_chiPlus_contDiff).2
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < 1
  · have : c02_aux_Apart p s =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [c02_aux_Apart, c02_aux_deriv_chiPlus_lt hy]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have hx0 : 0 < x := by linarith [not_lt.1 hx]
    have heq : c02_aux_Apart p s =ᶠ[𝓝 x] fun ξ => s * ((deriv chiPlus ξ * ξ⁻¹ : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((ξ * ξ ^ p / (p + 1) : ℝ) : ℂ))) := by
      filter_upwards [Ioi_mem_nhds hx0] with y hy
      simp only [c02_aux_Apart, Phi0, abs_of_pos (mem_Ioi.1 hy), div_eq_mul_inv]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => deriv chiPlus ξ * ξ⁻¹) x :=
      hd.contDiffAt.mul (contDiffAt_inv ℝ hx0.ne')
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ξ * ξ ^ p / (p + 1)) x :=
      (contDiffAt_id.mul (Real.contDiffAt_rpow_const_of_ne hx0.ne')).div_const _
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
    exact (contDiffAt_const.mul (hc.contDiffAt.comp x h1)).mul
      (Complex.contDiff_exp.contDiffAt.comp x
        ((contDiffAt_const.mul (hc.contDiffAt.comp x h2)).neg))

/-- `ĝ_s` is smooth. -/
theorem c02_aux_G_pm_hat_smooth {p : ℝ} (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (G_pm_hat p s) := by
  rw [c02_aux_G_pm_hat_eq_A]
  exact (c02_aux_Apart_smooth s).add
    (Complex.conjCLE.contDiff.comp ((c02_aux_Apart_smooth s).comp contDiff_neg))


/-- `ĝ_s` vanishes outside `[-2,2]`. -/
theorem c02_aux_G_pm_hat_zero (p : ℝ) (s : ℂ) {ξ : ℝ} (hξ : ξ ∉ Icc (-2 : ℝ) 2) :
    G_pm_hat p s ξ = 0 := by
  rw [c02_aux_G_pm_hat_split]
  simp only [mem_Icc, not_and_or, not_le] at hξ
  have h1 : deriv chiPlus ξ / ξ = 0 := c02_aux_g_zero (by
    simp only [mem_Icc, not_and_or, not_le]; rcases hξ with h | h
    · left; linarith
    · right; linarith)
  have h2 : deriv chiPlus (-ξ) / (-ξ) = 0 := c02_aux_g_zero (by
    simp only [mem_Icc, not_and_or, not_le]; rcases hξ with h | h
    · right; linarith
    · left; linarith)
  simp [h1, h2]

/-- `φ_s(η) = ĝ_s(2πη)` (the symbol in Mathlib's normalisation of the Fourier transform). -/
def c02_aux_phi (p : ℝ) (s : ℂ) (η : ℝ) : ℂ := G_pm_hat p s (2 * π * η)

/-- `φ_s` has compact support. -/
theorem c02_aux_phi_supp (p : ℝ) (s : ℂ) : HasCompactSupport (c02_aux_phi p s) :=
  HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) fun η hη =>
    c02_aux_G_pm_hat_zero p s (by
      simp only [mem_Icc, not_and_or, not_le] at hη ⊢
      have := Real.pi_gt_three
      rcases hη with h | h
      · left; nlinarith
      · right; nlinarith)

/-- `φ_s` is smooth. -/
theorem c02_aux_phi_smooth (p : ℝ) (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (c02_aux_phi p s) :=
  (c02_aux_G_pm_hat_smooth s).comp (contDiff_const.mul contDiff_id)

/-- `φ_s` as a Schwartz function. -/
def c02_aux_phiS (p : ℝ) (s : ℂ) : SchwartzMap ℝ ℂ :=
  (c02_aux_phi_supp p s).toSchwartzMap (c02_aux_phi_smooth p s)

/-- `⇑φ_s^𝓢 = φ_s`. -/
theorem c02_aux_phiS_apply (p : ℝ) (s : ℂ) (v : ℝ) : c02_aux_phiS p s v = c02_aux_phi p s v := rfl

/-- `T_s = 𝓕⁻ φ_s`, a Schwartz function. -/
def c02_aux_T (p : ℝ) (s : ℂ) : SchwartzMap ℝ ℂ := 𝓕⁻ (c02_aux_phiS p s)

/-- `(ĝ_s)^∨ = T_s` (change of normalisation). -/
theorem c02_aux_invF_eq_T (p : ℝ) (s : ℂ) (y : ℝ) :
    invFourierT (G_pm_hat p s) y = c02_aux_T p s y := by
  unfold c02_aux_T
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  simp only [c02_aux_phiS_apply, c02_aux_phi, smul_eq_mul]
  unfold invFourierT
  have h := Measure.integral_comp_mul_left
    (fun ξ : ℝ => G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) (2 * π)
  have e : (fun v : ℝ => Complex.exp (((2 * π * inner ℝ v y : ℝ) : ℂ) * Complex.I) *
      G_pm_hat p s (2 * π * v)) = fun v =>
      (fun ξ : ℝ => G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) (2 * π * v) := by
    funext v
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast; ring_nf
  rw [e, h, abs_of_pos (by positivity), Complex.real_smul]
  push_cast; ring


/-- `T_s` is real. -/
theorem c02_aux_T_real (p : ℝ) (s : ℂ) (y : ℝ) : (c02_aux_T p s y).im = 0 := by
  rw [← c02_aux_invF_eq_T]; exact c02_aux_invF_real s y

/-- `(G_s : ℂ) = T_s`. -/
theorem c02_aux_G_pm_of_eq (p : ℝ) (s : ℂ) (y : ℝ) : ((G_pm_of p s y : ℝ) : ℂ) = c02_aux_T p s y := by
  unfold G_pm_of
  rw [c02_aux_invF_eq_T]
  exact Complex.ext (by simp) (by simp [c02_aux_T_real])

/-- Fourier inversion: `Ĝ_s = ĝ_s`. -/
theorem c02_aux_fourierT_G_pm (p : ℝ) (s : ℂ) (ξ : ℝ) :
    fourierT (fun x => (G_pm_of p s x : ℂ)) ξ = G_pm_hat p s ξ := by
  have key : (𝓕 (𝓕⁻ (c02_aux_phiS p s))) (ξ / (2 * π)) = c02_aux_phiS p s (ξ / (2 * π)) := by
    rw [FourierInvPair.fourier_fourierInv_eq]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, c02_aux_phiS_apply,
    c02_aux_phi, show 2 * π * (ξ / (2 * π)) = ξ by field_simp] at key
  rw [← key]
  unfold fourierT
  congr 1; funext x
  beta_reduce
  rw [c02_aux_G_pm_of_eq, smul_eq_mul, mul_comm]
  unfold c02_aux_T
  congr 1
  congr 1
  push_cast
  field_simp

/-- `∫₀^R ξ e^{iΦ₀} Ĝ_s → s`. -/
theorem c02_aux_ell_G_pm (p : ℝ) (s : ℂ) :
    Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      fourierT (fun x => (G_pm_of p s x : ℂ)) ξ) atTop (𝓝 s) := by
  simp_rw [c02_aux_fourierT_G_pm]
  have hd : ContDiff ℝ (⊤ : ℕ∞) chiPlus := c02_aux_chiPlus_contDiff
  have hdc : Continuous (deriv chiPlus) := hd.continuous_deriv (by norm_num)
  refine tendsto_const_nhds.congr' (EventuallyEq.symm ?_)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  have h1 : ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
      G_pm_hat p s ξ = ∫ ξ in (0 : ℝ)..R, s * ((deriv chiPlus ξ : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    rw [uIcc_of_le (by linarith)] at hξ
    simp only [G_pm_hat, hξ.1, ↓reduceIte]
    have hexp : Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
        Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) = 1 := by
      rw [← Complex.exp_add]; simp
    rcases hξ.1.eq_or_lt with h0 | h0
    · subst h0; simp [c02_aux_deriv_chiPlus_lt (show (0 : ℝ) < 1 by norm_num)]
    · have : (ξ : ℂ) * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) = ((deriv chiPlus ξ : ℝ) : ℂ) := by
        have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
        push_cast; field_simp
      calc (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
            (s * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))))
          = s * ((ξ : ℂ) * ((deriv chiPlus ξ / ξ : ℝ) : ℂ)) *
            (Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
              Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) := by ring
        _ = _ := by rw [this, hexp, mul_one]
  rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_deriv_eq_sub (fun x _ => (hd.differentiable (by simp)) x)
      (hdc.intervalIntegrable _ _)]
  have hR1 : chiPlus R = 1 := Real.smoothTransition.one_of_one_le (by unfold chiPlus at *; linarith)
  have hR0 : chiPlus 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  rw [hR1, hR0]; simp

/-- Blueprint: lem:c02_G_pm_properties.  `G_±` are real-valued Schwartz functions (the inverse
transforms of `Ĝ_±` are real, and `G_± = ` their real parts are Schwartz), `G_± ∈ Y_γ` for every
`γ`, and `ℓ(G₊) = 1`, `ℓ(G₋) = i` (the defining limits exist). -/
theorem c02_G_pm_properties (P : parameters) :
    (∀ y, (invFourierT (G_pm_hat P.p 1) y).im = 0) ∧
    (∀ y, (invFourierT (G_pm_hat P.p Complex.I) y).im = 0) ∧
    (∃ S : SchwartzMap ℝ ℝ, (⇑S : ℝ → ℝ) = G_plus P.p) ∧
    (∃ S : SchwartzMap ℝ ℝ, (⇑S : ℝ → ℝ) = G_minus P.p) ∧
    (∀ γ, G_plus P.p ∈ Y_gamma P.p γ ∧ G_minus P.p ∈ Y_gamma P.p γ) ∧
    Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 P.p ξ : ℂ)) *
      fourierT (fun x => (G_plus P.p x : ℂ)) ξ) atTop (𝓝 1) ∧
    Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 P.p ξ : ℂ)) *
      fourierT (fun x => (G_minus P.p x : ℂ)) ξ) atTop (𝓝 Complex.I) ∧
    ell P.p (G_plus P.p) = 1 ∧ ell P.p (G_minus P.p) = Complex.I := by
  have hS : ∀ s : ℂ, ∃ S : SchwartzMap ℝ ℝ, (⇑S : ℝ → ℝ) = G_pm_of P.p s := fun s =>
    ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM (c02_aux_T P.p s), by
      funext y
      rw [SchwartzMap.postcompCLM_apply, Complex.reCLM_apply, ← c02_aux_invF_eq_T]
      rfl⟩
  obtain ⟨Sp, hSp⟩ := hS 1
  obtain ⟨Sm, hSm⟩ := hS Complex.I
  have hT1 := c02_aux_ell_G_pm P.p 1
  have hT2 := c02_aux_ell_G_pm P.p Complex.I
  refine ⟨c02_aux_invF_real 1, c02_aux_invF_real Complex.I, ⟨Sp, hSp⟩, ⟨Sm, hSm⟩,
    fun γ => ⟨?_, ?_⟩, hT1, hT2, hT1.limUnder_eq, hT2.limUnder_eq⟩
  · have := (c02_schwartz_in_Y P Sp γ).1
    rwa [hSp] at this
  · have := (c02_schwartz_in_Y P Sm γ).1
    rwa [hSm] at this

/-- Blueprint: lem:c02_G_mu_decomposition.  With `z(μ) = 1 - μ/μ_*`:
(1) `G_μ = Re z · G₊ + Im z · G₋`, `G_μ` is a real Schwartz function, `G_{μ_*} = 0`;
(2) `ℓ(G_μ) = z(μ)`;
(3) `μ ↦ G_μ` is continuous `ℂ → Y_γ` and `‖G_μ‖_{Y_γ} ≤ δ/|μ_*| (‖G₊‖ + ‖G₋‖)` on `B̄(μ_*,δ)`. -/
theorem c02_G_mu_decomposition (P : parameters) :
    (∀ μ : ℂ, G_mu P.p μ = fun y => (1 - μ / mu_star P.p).re * G_plus P.p y +
        (1 - μ / mu_star P.p).im * G_minus P.p y) ∧
    (∀ μ : ℂ, (∃ S : SchwartzMap ℝ ℝ, (⇑S : ℝ → ℝ) = G_mu P.p μ) ∧
      ∀ y, (invFourierT (G_pm_hat P.p (1 - μ / mu_star P.p)) y).im = 0) ∧
    G_mu P.p (mu_star P.p) = 0 ∧
    (∀ μ : ℂ, ell P.p (G_mu P.p μ) = 1 - μ / mu_star P.p) ∧
    (∀ γ : ℝ, (∀ μ : ℂ, G_mu P.p μ ∈ Y_gamma P.p γ) ∧
      (∀ μ : ℂ, Tendsto (fun ν => yNorm P.p γ (G_mu P.p ν - G_mu P.p μ)) (𝓝 μ) (𝓝 0)) ∧
      ∀ δ > 0, ∀ μ ∈ Bbar P.p δ, yNorm P.p γ (G_mu P.p μ) ≤
        δ / ‖mu_star P.p‖ * (yNorm P.p γ (G_plus P.p) + yNorm P.p γ (G_minus P.p))) := by
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨him1, him2, ⟨Sp, hSp⟩, ⟨Sm, hSm⟩, hGY, hT1, hT2, hℓ1, hℓ2⟩ := c02_G_pm_properties P
  have hdec : ∀ μ : ℂ, G_mu P.p μ = fun y => (1 - μ / mu_star P.p).re * G_plus P.p y +
      (1 - μ / mu_star P.p).im * G_minus P.p y := by
    intro μ; funext y
    simp only [G_mu, G_pm_of, G_plus, G_minus]
    rw [c02_aux_invF_G_pm_lin hp]
    simp [Complex.add_re]
  have hz0 : 1 - mu_star P.p / mu_star P.p = 0 := by
    rw [div_self (c02_aux_mu_star_ne P)]; ring
  have hGpi : Integrable (G_plus P.p) := by rw [← hSp]; exact Sp.integrable
  have hGmi : Integrable (G_minus P.p) := by rw [← hSm]; exact Sm.integrable
  have hGpc : Continuous (G_plus P.p) := by rw [← hSp]; exact Sp.continuous
  have hGmc : Continuous (G_minus P.p) := by rw [← hSm]; exact Sm.continuous
  refine ⟨hdec, fun μ => ⟨?_, fun y => ?_⟩, ?_, fun μ => ?_, fun γ => ?_⟩
  · refine ⟨(1 - μ / mu_star P.p).re • Sp + (1 - μ / mu_star P.p).im • Sm, ?_⟩
    rw [hdec μ]; funext y
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [show Sp y = G_plus P.p y from congrFun hSp y, show Sm y = G_minus P.p y from congrFun hSm y]
  · rw [c02_aux_invF_G_pm_lin hp]
    simp [Complex.add_im, him1 y, him2 y]
  · rw [hdec, hz0]; funext y; simp
  · rw [hdec μ]
    have := (c02_aux_ell_lin hp hGpi hGpc hGmi hGmc hT1 hT2 (1 - μ / mu_star P.p).re
      (1 - μ / mu_star P.p).im).2
    rw [this, hℓ1, hℓ2, mul_one]
    exact Complex.re_add_im _
  · have hYp := (hGY γ).1
    have hYm := (hGY γ).2
    have np := c02_aux_yNorm_nonneg P (γ := γ) (G_plus P.p)
    have nm := c02_aux_yNorm_nonneg P (γ := γ) (G_minus P.p)
    refine ⟨fun μ => by rw [hdec μ]; exact (c02_aux_Y_lin P _ _ hYp hYm).1, fun μ => ?_,
      fun δ hδ μ hμ => ?_⟩
    · have e : ∀ ν, G_mu P.p ν - G_mu P.p μ = fun y =>
          ((1 - ν / mu_star P.p).re - (1 - μ / mu_star P.p).re) * G_plus P.p y +
          ((1 - ν / mu_star P.p).im - (1 - μ / mu_star P.p).im) * G_minus P.p y := by
        intro ν; rw [hdec, hdec]; funext y; simp only [Pi.sub_apply]; ring
      set f : ℂ → ℝ := fun ν =>
        |(1 - ν / mu_star P.p).re - (1 - μ / mu_star P.p).re| * yNorm P.p γ (G_plus P.p) +
        |(1 - ν / mu_star P.p).im - (1 - μ / mu_star P.p).im| * yNorm P.p γ (G_minus P.p) with hf
      have hfc : Continuous f := by rw [hf]; fun_prop
      have hf0 : f μ = 0 := by simp [hf]
      have ht := hfc.tendsto μ
      rw [hf0] at ht
      refine squeeze_zero (fun ν => c02_aux_yNorm_nonneg P _) (fun ν => ?_) ht
      rw [e ν]
      exact (c02_aux_Y_lin P _ _ hYp hYm).2
    · rw [hdec μ]
      have hb := (c02_aux_Y_lin P (1 - μ / mu_star P.p).re (1 - μ / mu_star P.p).im hYp hYm).2
      have hz : ‖1 - μ / mu_star P.p‖ ≤ δ / ‖mu_star P.p‖ := by
        have h0 := c02_aux_mu_star_ne P
        have : 1 - μ / mu_star P.p = (mu_star P.p - μ) / mu_star P.p := by field_simp
        rw [this, norm_div, norm_sub_rev]
        have hμ' : dist μ (mu_star P.p) ≤ δ := hμ
        rw [dist_eq_norm] at hμ'
        gcongr
      have h1 := Complex.abs_re_le_norm (1 - μ / mu_star P.p)
      have h2 := Complex.abs_im_le_norm (1 - μ / mu_star P.p)
      calc _ ≤ |(1 - μ / mu_star P.p).re| * yNorm P.p γ (G_plus P.p) +
            |(1 - μ / mu_star P.p).im| * yNorm P.p γ (G_minus P.p) := hb
        _ ≤ δ / ‖mu_star P.p‖ * yNorm P.p γ (G_plus P.p) +
            δ / ‖mu_star P.p‖ * yNorm P.p γ (G_minus P.p) := by
          gcongr
          · exact h1.trans hz
          · exact h2.trans hz
        _ = _ := by ring

/-- Blueprint: lem:c02_Pi_bounded_projection.  Let `γ` be admissible, assume `ℓ` is well defined
on `Y_γ` (the defining limit exists) and `|ℓ(G)| ≤ C_ℓ ‖G‖_{Y_γ}`.  Then
(1) `Ỹ_γ` is a closed linear subspace of `Y_γ`;
(2) `Π` is linear `Y_γ → Y_γ` with `‖Π G‖ ≤ (1 + C_ℓ(‖G₊‖+‖G₋‖))‖G‖`;
(3) `ℓ(Π G) = 0`, `Π G = G` on `Ỹ_γ`, `Π² = Π`;
(4) `Π G_μ = 0`, and `Π G = G - G_μ` whenever `ℓ(G) = 1 - μ/μ_*`. -/
theorem c02_Pi_bounded_projection (P : parameters) {γ : ℝ} (hγ : P.admissible γ) (Cℓ : ℝ)
    (hlim : ∀ G ∈ Y_gamma P.p γ, ∃ L : ℂ, Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
      (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 P.p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ)
      atTop (𝓝 L))
    (hCℓ : ∀ G ∈ Y_gamma P.p γ, ‖ell P.p G‖ ≤ Cℓ * yNorm P.p γ G) :
    -- (1)
    ((0 : ℝ → ℝ) ∈ Y_gamma_tilde P.p γ ∧
      (∀ G ∈ Y_gamma_tilde P.p γ, ∀ H ∈ Y_gamma_tilde P.p γ, G + H ∈ Y_gamma_tilde P.p γ) ∧
      (∀ c : ℝ, ∀ G ∈ Y_gamma_tilde P.p γ, c • G ∈ Y_gamma_tilde P.p γ) ∧
      (∀ (u : ℕ → ℝ → ℝ) (G : ℝ → ℝ), (∀ n, u n ∈ Y_gamma_tilde P.p γ) → G ∈ Y_gamma P.p γ →
        Tendsto (fun n => yNorm P.p γ (u n - G)) atTop (𝓝 0) → G ∈ Y_gamma_tilde P.p γ)) ∧
    -- (2)
    (∀ G ∈ Y_gamma P.p γ, Pi_projection P.p G ∈ Y_gamma P.p γ ∧
      yNorm P.p γ (Pi_projection P.p G) ≤
        (1 + Cℓ * (yNorm P.p γ (G_plus P.p) + yNorm P.p γ (G_minus P.p))) * yNorm P.p γ G) ∧
    (∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ, ∀ a b : ℝ,
      Pi_projection P.p (a • G + b • H) = a • Pi_projection P.p G + b • Pi_projection P.p H) ∧
    -- (3)
    (∀ G ∈ Y_gamma P.p γ, ell P.p (Pi_projection P.p G) = 0 ∧
      Pi_projection P.p G ∈ Y_gamma_tilde P.p γ) ∧
    (∀ G ∈ Y_gamma_tilde P.p γ, Pi_projection P.p G = G) ∧
    (∀ G ∈ Y_gamma P.p γ, Pi_projection P.p (Pi_projection P.p G) = Pi_projection P.p G) ∧
    -- (4)
    (∀ μ : ℂ, Pi_projection P.p (G_mu P.p μ) = 0) ∧
    (∀ G ∈ Y_gamma P.p γ, ∀ μ : ℂ, ell P.p G = 1 - μ / mu_star P.p →
      Pi_projection P.p G = G - G_mu P.p μ) := by
  have hγ1 := c02_aux_one_lt_of_admissible P hγ
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨-, -, -, -, hGY, -, -, hℓ1, hℓ2⟩ := c02_G_pm_properties P
  obtain ⟨hdec, -, -, hellmu, -⟩ := c02_G_mu_decomposition P
  have hYp := (hGY γ).1
  have hYm := (hGY γ).2
  have hlin : ∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ, ∀ a b : ℝ,
      (fun x => a * G x + b * H x) ∈ Y_gamma P.p γ ∧
      ell P.p (fun x => a * G x + b * H x) = a * ell P.p G + b * ell P.p H := by
    intro G hG H hH a b
    obtain ⟨LG, hLG⟩ := hlim G hG
    obtain ⟨LH, hLH⟩ := hlim H hH
    exact ⟨(c02_aux_Y_lin P a b hG hH).1, (c02_aux_ell_lin hp (c02_aux_Y_integrable hγ1 hG)
      hG.1.continuous (c02_aux_Y_integrable hγ1 hH) hH.1.continuous hLG hLH a b).2⟩
  -- `Π G` as a two-step linear combination
  have hPiA : ∀ G ∈ Y_gamma P.p γ,
      (fun x => 1 * G x + (-(ell P.p G).re) * G_plus P.p x) ∈ Y_gamma P.p γ ∧
      ell P.p (fun x => 1 * G x + (-(ell P.p G).re) * G_plus P.p x) =
        ell P.p G - (ell P.p G).re := by
    intro G hG
    obtain ⟨h1, h2⟩ := hlin G hG _ hYp 1 (-(ell P.p G).re)
    refine ⟨h1, ?_⟩
    rw [h2, hℓ1]; push_cast; ring
  have hPiEq : ∀ G, Pi_projection P.p G = fun x =>
      1 * (fun x => 1 * G x + (-(ell P.p G).re) * G_plus P.p x) x +
        (-(ell P.p G).im) * G_minus P.p x := by
    intro G; funext x; simp only [Pi_projection]; ring
  have hPimem : ∀ G ∈ Y_gamma P.p γ, Pi_projection P.p G ∈ Y_gamma P.p γ ∧
      ell P.p (Pi_projection P.p G) = 0 := by
    intro G hG
    obtain ⟨h1, h2⟩ := hPiA G hG
    obtain ⟨h3, h4⟩ := hlin _ h1 _ hYm 1 (-(ell P.p G).im)
    rw [hPiEq]
    refine ⟨h3, ?_⟩
    rw [h4, h2, hℓ2]
    apply Complex.ext <;> simp
  have hfix : ∀ G ∈ Y_gamma_tilde P.p γ, Pi_projection P.p G = G := by
    intro G hG
    funext x
    simp [Pi_projection, hG.2]
  refine ⟨⟨⟨c02_aux_Y_zero P, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, fun G hG => ⟨(hPimem G hG).2,
    ⟨(hPimem G hG).1, (hPimem G hG).2⟩⟩, hfix,
    fun G hG => hfix _ ⟨(hPimem G hG).1, (hPimem G hG).2⟩, ?_, ?_⟩
  · -- `ℓ(0) = 0`
    have := (hlin 0 (c02_aux_Y_zero P) 0 (c02_aux_Y_zero P) 0 0).2
    have e : (fun x : ℝ => (0 : ℝ) * (0 : ℝ → ℝ) x + 0 * (0 : ℝ → ℝ) x) = 0 := by
      funext x; simp
    rw [e] at this; rw [this]; simp
  · intro G hG H hH
    obtain ⟨h1, h2⟩ := hlin G hG.1 H hH.1 1 1
    have e : (fun x => (1 : ℝ) * G x + 1 * H x) = G + H := by funext x; simp
    rw [e] at h1 h2
    exact ⟨h1, by rw [h2, hG.2, hH.2]; simp⟩
  · intro c G hG
    obtain ⟨h1, h2⟩ := hlin G hG.1 G hG.1 c 0
    have e : (fun x => c * G x + 0 * G x) = c • G := by funext x; simp
    rw [e] at h1 h2
    exact ⟨h1, by rw [h2, hG.2]; simp⟩
  · intro u G hu hG hconv
    refine ⟨hG, ?_⟩
    have hb : ∀ n, ‖ell P.p G‖ ≤ Cℓ * yNorm P.p γ (u n - G) := by
      intro n
      obtain ⟨h1, h2⟩ := hlin (u n) (hu n).1 G hG 1 (-1)
      have e : (fun x => (1 : ℝ) * u n x + (-1) * G x) = u n - G := by
        funext x; simp; ring
      rw [e] at h1 h2
      rw [(hu n).2] at h2
      have := hCℓ _ h1
      rw [h2] at this
      simpa using this
    have := ge_of_tendsto' (hconv.const_mul Cℓ) hb
    rw [mul_zero] at this
    exact norm_le_zero_iff.1 this
  · intro G hG
    refine ⟨(hPimem G hG).1, ?_⟩
    obtain ⟨h1, h2⟩ := hPiA G hG
    have hA := (c02_aux_Y_lin P 1 (-(ell P.p G).im) h1 hYm).2
    have hA' := (c02_aux_Y_lin P 1 (-(ell P.p G).re) hG hYp).2
    rw [← hPiEq] at hA
    have hre := Complex.abs_re_le_norm (ell P.p G)
    have him := Complex.abs_im_le_norm (ell P.p G)
    have hC := hCℓ G hG
    have n1 := c02_aux_yNorm_nonneg P (γ := γ) (G_plus P.p)
    have n2 := c02_aux_yNorm_nonneg P (γ := γ) (G_minus P.p)
    simp only [abs_one, one_mul, abs_neg] at hA hA'
    calc yNorm P.p γ (Pi_projection P.p G)
        ≤ yNorm P.p γ G + |(ell P.p G).re| * yNorm P.p γ (G_plus P.p) +
          |(ell P.p G).im| * yNorm P.p γ (G_minus P.p) := by linarith
      _ ≤ yNorm P.p γ G + ‖ell P.p G‖ * yNorm P.p γ (G_plus P.p) +
          ‖ell P.p G‖ * yNorm P.p γ (G_minus P.p) := by gcongr
      _ = yNorm P.p γ G + ‖ell P.p G‖ * (yNorm P.p γ (G_plus P.p) + yNorm P.p γ (G_minus P.p)) := by
          ring
      _ ≤ yNorm P.p γ G + Cℓ * yNorm P.p γ G * (yNorm P.p γ (G_plus P.p) +
          yNorm P.p γ (G_minus P.p)) := by gcongr
      _ = _ := by ring
  · intro G hG H hH a b
    have e : a • G + b • H = fun x => a * G x + b * H x := by funext x; simp
    have hl := (hlin G hG H hH a b).2
    rw [e, hPiEq, hPiEq, hPiEq, hl]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.add_im,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    ring
  · intro μ
    rw [hdec μ]
    funext x
    have := hellmu μ
    rw [hdec μ] at this
    simp only [Pi_projection, this, Pi.zero_apply]
    ring
  · intro G hG μ h
    funext x
    simp only [Pi_projection, h, Pi.sub_apply, hdec μ]
    ring

/-! ### Existence of the correction -/

/-- The conclusion of thm:fixed_point_approximation is downward closed in `ε₀`. -/
theorem c02_aux_approx_mono {P : parameters} {R δ ε₀ ε₀' : ℝ}
    (h : fixed_point_approximation_statement P R δ ε₀) (hle : ε₀' ≤ ε₀) :
    fixed_point_approximation_statement P R δ ε₀' := by
  have hs : Icc 0 ε₀' ⊆ Icc 0 ε₀ := Icc_subset_Icc_right hle
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨h0, fun ε hε => h1 ε (hs hε), fun ε hε => h2 ε (hs hε), fun j => ?_, fun γ hγ => ?_,
    fun ε hε => h5 ε (hs hε)⟩
  · obtain ⟨C, hC, hC'⟩ := h3 j; exact ⟨C, hC, fun ε hε => hC' ε (hs hε)⟩
  · obtain ⟨C, hC, hC'⟩ := h4 γ hγ; exact ⟨C, hC, fun ε hε => hC' ε (hs hε)⟩

/-- The conclusion of thm:fixed_point_linear_inverse is downward closed in `ε₀`. -/
theorem c02_aux_linear_mono {P : parameters} {δ ε₀ ε₀' : ℝ}
    (h : fixed_point_linear_inverse_statement P δ ε₀) (hle : ε₀' ≤ ε₀) :
    fixed_point_linear_inverse_statement P δ ε₀' := by
  have hs : Icc 0 ε₀' ⊆ Icc 0 ε₀ := Icc_subset_Icc_right hle
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, fun ε hε => h3 ε (hs hε), fun γ hγ => ?_, fun γ hγ => ?_⟩
  · obtain ⟨C, hC, hC'⟩ := h4 γ hγ; exact ⟨C, hC, fun ε hε => hC' ε (hs hε)⟩
  · obtain ⟨C, hC, hC'⟩ := h5 γ hγ; exact ⟨C, hC, fun ε hε => hC' ε (hs hε)⟩

/-- The conclusion of thm:fixed_point_nonlinear_estimates is downward closed in `ε₀`. -/
theorem c02_aux_nonlinear_mono {P : parameters} {R δ ε₀ ε₀' : ℝ}
    (h : fixed_point_nonlinear_estimates_statement P R δ ε₀) (hle : ε₀' ≤ ε₀) :
    fixed_point_nonlinear_estimates_statement P R δ ε₀' := by
  have hs : Icc 0 ε₀' ⊆ Icc 0 ε₀ := Icc_subset_Icc_right hle
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun γ hγ N hN => ?_, fun ε hε => h2 ε (hs hε)⟩
  obtain ⟨C, hC, hC'⟩ := h1 γ hγ N hN; exact ⟨C, hC, fun ε hε => hC' ε (hs hε)⟩

/-- Blueprint: lem:c02_profile_solves.  If `(μ, r)` solves the correction equation then
`f = f̄_{ε,μ} + r` satisfies `ℰ_ε(f) = 0` on `ℝ`. -/
theorem c02_profile_solves (P : parameters) (R ε : ℝ) (μ : ℂ) (r : ℝ → ℝ)
    (h : ∀ y, L_eps P.p ε r y = -residual P.p ε (approximate_solution_family P.p R ε μ) y -
      N_eps P.p ε (approximate_solution_family P.p R ε μ) r y) :
    ∀ y, residual P.p ε (approximate_solution_family P.p R ε μ + r) y = 0 := by
  intro y
  have := h y
  unfold N_eps at this
  linarith

/-! ### Reduction to a fixed point system -/

/-- Blueprint: def:c02_forcing_map.  The forcing map
`𝒢_{ε,μ}(w) = -[𝒱_ε⁻¹ ℰ_ε(f̄_{ε,μ}) - G_μ] - 𝒱_ε⁻¹ 𝒩_{ε,f̄_{ε,μ}}(𝒰_ε⁻¹ w)`
(a `γ`-independent formula, defined for every function `w`). -/
def c02_forcing_map (p R ε : ℝ) (μ : ℂ) (w : ℝ → ℝ) : ℝ → ℝ := fun y =>
  -(V_eps_inv p ε (residual p ε (approximate_solution_family p R ε μ)) y - G_mu p μ y) -
    V_eps_inv p ε (N_eps p ε (approximate_solution_family p R ε μ) (U_eps_inv p ε w)) y

/-- Blueprint: def:c02_forcing_map.  The fixed point map `ℋ_{ε,μ}(w) = 𝒯₀ Π 𝒢_{ε,μ}(w)`. -/
def c02_forcing_map_H (p R ε : ℝ) (μ : ℂ) (w : ℝ → ℝ) : ℝ → ℝ :=
  T_0 p (Pi_projection p (c02_forcing_map p R ε μ w))

/-- Blueprint: def:c02_forcing_map (context).  "`ε₀, δ, B̄, f̄` as in thm:fixed_point_approximation
and `𝒯₀, 𝒰_ε, 𝒱_ε` as in thm:fixed_point_linear_inverse": `δ, ε₀ > 0` and the conclusions of the
three backbone theorems hold for `(R, δ, ε₀)`. -/
def c02_forcing_map_setting (P : parameters) (R δ ε₀ : ℝ) : Prop :=
  0 < δ ∧ 0 < ε₀ ∧ fixed_point_approximation_statement P R δ ε₀ ∧
    fixed_point_linear_inverse_statement P δ ε₀ ∧ fixed_point_nonlinear_estimates_statement P R δ ε₀

/-- Blueprint: def:c02_forcing_map (well-definedness).  For `ε ∈ [0,ε₀]`, `μ ∈ B̄`, admissible `γ`
and `w ∈ X_γ`: `𝒢_{ε,μ}(w) ∈ Y_γ` and `ℋ_{ε,μ}(w) ∈ X_γ`. -/
theorem c02_forcing_map_mem (P : parameters) {R δ ε₀ : ℝ} (hS : c02_forcing_map_setting P R δ ε₀)
    {ε : ℝ} (hε : ε ∈ Icc 0 ε₀) {μ : ℂ} (hμ : μ ∈ Bbar P.p δ) {γ : ℝ} (hγ : P.admissible γ)
    {w : ℝ → ℝ} (hw : w ∈ X_gamma P.p γ) :
    c02_forcing_map P.p R ε μ w ∈ Y_gamma P.p γ ∧ c02_forcing_map_H P.p R ε μ w ∈ X_gamma P.p γ := by
  obtain ⟨-, -, hA, hL, hN⟩ := hS
  obtain ⟨-, -, -, -, hres, -⟩ := hA
  obtain ⟨hℓ, hT, -, hUV, -⟩ := hL
  obtain ⟨hN12, -⟩ := hN
  obtain ⟨C, -, hC⟩ := hres γ hγ
  obtain ⟨CUV, -, hCUV⟩ := hUV γ hγ
  obtain ⟨hU, hV, -⟩ := hCUV ε hε
  have hE := (hC ε hε μ hμ).1
  have hw' := (hU w hw).2.2.1
  obtain ⟨CN, -, hCN⟩ := hN12 γ hγ (xNorm P.p γ (U_eps_inv P.p ε w) + 1)
    (by linarith [c02_aux_xNorm_nonneg P (γ := γ) (U_eps_inv P.p ε w)])
  have hNm := ((hCN ε hε μ hμ).1 _ hw' (by linarith)).1
  have hVE := (hV _ hE).2.2.1
  have hVN := (hV _ hNm).2.2.1
  have hGmu := ((c02_G_mu_decomposition P).2.2.2.2 γ).1 μ
  have hF : c02_forcing_map P.p R ε μ w ∈ Y_gamma P.p γ :=
    (c02_aux_Y_sub P (c02_aux_Y_neg P (c02_aux_Y_sub P hVE hGmu).1).1 hVN).1
  refine ⟨hF, ?_⟩
  obtain ⟨Cℓ, -, hCℓ⟩ := hℓ γ hγ
  obtain ⟨-, -, -, hP3, -⟩ := c02_Pi_bounded_projection P hγ Cℓ
    (fun G hG => ⟨_, (hCℓ G hG).1⟩) (fun G hG => (hCℓ G hG).2)
  obtain ⟨CT, -, hT1, -⟩ := hT γ hγ
  exact (hT1 _ (hP3 _ hF).2).1

/-- Consequences of thm:fixed_point_linear_inverse (1),(2) and lem:c02_Pi_bounded_projection
for one admissible `γ`: bounds for `ℓ`, and `𝒯₀ Π` is a bounded linear map `Y_γ → X_γ`
inverting `ℒ₀` on `Ỹ_γ`. -/
theorem c02_aux_TPi (P : parameters) {δ ε₀ : ℝ} (hL : fixed_point_linear_inverse_statement P δ ε₀)
    {γ : ℝ} (hγ : P.admissible γ) :
    ∃ Cℓ > 0, ∃ M > 0,
      (∀ G ∈ Y_gamma P.p γ, ‖ell P.p G‖ ≤ Cℓ * yNorm P.p γ G) ∧
      (∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ,
        ‖ell P.p G - ell P.p H‖ ≤ Cℓ * yNorm P.p γ (G - H)) ∧
      (∀ G ∈ Y_gamma P.p γ, Pi_projection P.p G ∈ Y_gamma_tilde P.p γ ∧
        T_0 P.p (Pi_projection P.p G) ∈ X_gamma P.p γ ∧
        xNorm P.p γ (T_0 P.p (Pi_projection P.p G)) ≤ M * yNorm P.p γ G ∧
        ∀ y, L0 P.p (T_0 P.p (Pi_projection P.p G)) y = Pi_projection P.p G y) ∧
      (∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ,
        T_0 P.p (Pi_projection P.p G) - T_0 P.p (Pi_projection P.p H) =
          T_0 P.p (Pi_projection P.p (G - H))) ∧
      (∀ G ∈ Y_gamma P.p γ, ∀ μ : ℂ, ell P.p G = 1 - μ / mu_star P.p →
        Pi_projection P.p G = G - G_mu P.p μ) := by
  obtain ⟨hℓ, hT, -, -, -⟩ := hL
  obtain ⟨Cℓ, hCℓ0, hCℓ⟩ := hℓ γ hγ
  obtain ⟨CT, hCT0, hT1, hTlin⟩ := hT γ hγ
  obtain ⟨-, hP2, hPlin, hP3, -, -, -, hP4⟩ := c02_Pi_bounded_projection P hγ Cℓ
    (fun G hG => ⟨_, (hCℓ G hG).1⟩) (fun G hG => (hCℓ G hG).2)
  have hγ1 := c02_aux_one_lt_of_admissible P hγ
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have n1 := c02_aux_yNorm_nonneg P (γ := γ) (G_plus P.p)
  have n2 := c02_aux_yNorm_nonneg P (γ := γ) (G_minus P.p)
  refine ⟨Cℓ, hCℓ0, CT * (1 + Cℓ * (yNorm P.p γ (G_plus P.p) + yNorm P.p γ (G_minus P.p))),
    by positivity, fun G hG => (hCℓ G hG).2, ?_, ?_, ?_, hP4⟩
  · intro G hG H hH
    have h := (c02_aux_ell_lin hp (c02_aux_Y_integrable hγ1 hG) hG.1.continuous
      (c02_aux_Y_integrable hγ1 hH) hH.1.continuous (hCℓ G hG).1 (hCℓ H hH).1 1 (-1)).2
    have e : (fun x => (1 : ℝ) * G x + (-1) * H x) = G - H := by funext x; simp; ring
    rw [e] at h
    have := (hCℓ _ (c02_aux_Y_sub P hG hH).1).2
    rw [h] at this
    simpa [sub_eq_add_neg] using this
  · intro G hG
    obtain ⟨hPm, hPb⟩ := hP2 G hG
    have hPt := (hP3 G hG).2
    obtain ⟨hT1m, -, hT1b, hT1L⟩ := hT1 _ hPt
    refine ⟨hPt, hT1m, ?_, hT1L⟩
    calc xNorm P.p γ (T_0 P.p (Pi_projection P.p G)) ≤ CT * yNorm P.p γ (Pi_projection P.p G) :=
          hT1b
      _ ≤ CT * ((1 + Cℓ * (yNorm P.p γ (G_plus P.p) + yNorm P.p γ (G_minus P.p))) *
          yNorm P.p γ G) := by gcongr
      _ = _ := by ring
  · intro G hG H hH
    have e : G - H = (1 : ℝ) • G + (-1 : ℝ) • H := by funext x; simp; ring
    rw [e, hPlin G hG H hH, hTlin _ (hP3 G hG).2 _ (hP3 H hH).2]
    simp [sub_eq_add_neg]

/-- Blueprint: lem:c02_system_implies_correction.  If `w ∈ X_γ` solves
`w = 𝒯₀ Π 𝒢_{ε,μ}(w)`, `ℓ(𝒢_{ε,μ}(w)) = 1 - μ/μ_*`, then `r = 𝒰_ε⁻¹ w ∈ X_γ` satisfies
`ℒ_ε(r) = -ℰ_ε(f̄_{ε,μ}) - 𝒩_{ε,f̄_{ε,μ}}(r)` on `ℝ`. -/
theorem c02_system_implies_correction (P : parameters) {R δ ε₀ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) {ε : ℝ} (hε : ε ∈ Icc 0 ε₀) {μ : ℂ}
    (hμ : μ ∈ Bbar P.p δ) {γ : ℝ} (hγ : P.admissible γ) {w : ℝ → ℝ} (hw : w ∈ X_gamma P.p γ)
    (h1 : w = c02_forcing_map_H P.p R ε μ w)
    (h2 : ell P.p (c02_forcing_map P.p R ε μ w) = 1 - μ / mu_star P.p) :
    U_eps_inv P.p ε w ∈ X_gamma P.p γ ∧
    ∀ y, L_eps P.p ε (U_eps_inv P.p ε w) y =
      -residual P.p ε (approximate_solution_family P.p R ε μ) y -
        N_eps P.p ε (approximate_solution_family P.p R ε μ) (U_eps_inv P.p ε w) y := by
  have hS' := hS
  obtain ⟨-, -, -, hL, -⟩ := hS
  obtain ⟨Cℓ, -, M, -, -, -, hTP, -, hP4⟩ := c02_aux_TPi P hL hγ
  obtain ⟨-, -, hinv, hUV, -⟩ := hL
  obtain ⟨CUV, -, hCUV⟩ := hUV γ hγ
  obtain ⟨hU, -, hLV⟩ := hCUV ε hε
  obtain ⟨-, hUr, -, hVr⟩ := hinv ε hε
  have hF := (c02_forcing_map_mem P hS' hε hμ hγ hw).1
  have hL0 := (hTP _ hF).2.2.2
  have hPi := hP4 _ hF μ h2
  have hr := (hU w hw).2.2.1
  refine ⟨hr, fun y => ?_⟩
  rw [hLV _ hr y, hUr w]
  have hL0w : ∀ z, L0 P.p w z =
      -(V_eps_inv P.p ε (residual P.p ε (approximate_solution_family P.p R ε μ)) z) -
        V_eps_inv P.p ε (N_eps P.p ε (approximate_solution_family P.p R ε μ)
          (U_eps_inv P.p ε w)) z := by
    intro z
    have e1 : L0 P.p w z = L0 P.p (c02_forcing_map_H P.p R ε μ w) z :=
      congrArg (fun f => L0 P.p f z) h1
    rw [e1]
    unfold c02_forcing_map_H
    rw [hL0 z, hPi]
    simp only [Pi.sub_apply, c02_forcing_map]
    ring
  have e1 := congrFun (hVr (residual P.p ε (approximate_solution_family P.p R ε μ))) y
  have e2 := congrFun (hVr (N_eps P.p ε (approximate_solution_family P.p R ε μ)
    (U_eps_inv P.p ε w))) y
  simp only [V_eps] at e1 e2 ⊢
  rw [hL0w, mul_sub, mul_neg, e1, e2]

/-! ### Contraction for `ℋ` -/

-- Encoding: the constant `C_R(γ) := C_UV(γ) C_γ + C_G(γ)` is existential here (its value is a
-- proof detail).
/-- Blueprint: lem:c02_conjugated_residual.  `‖𝒱_ε⁻¹ ℰ_ε(f̄_{ε,μ}) - G_μ‖_{Y_γ} ≤ C_R(γ) ε`
uniformly in `ε ∈ [0,ε₀]`, `μ ∈ B̄`. -/
theorem c02_conjugated_residual (P : parameters) {R δ ε₀ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) {γ : ℝ} (hγ : P.admissible γ) :
    ∃ CR > 0, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
      V_eps_inv P.p ε (residual P.p ε (approximate_solution_family P.p R ε μ)) - G_mu P.p μ ∈
        Y_gamma P.p γ ∧
      yNorm P.p γ (V_eps_inv P.p ε (residual P.p ε (approximate_solution_family P.p R ε μ)) -
        G_mu P.p μ) ≤ CR * ε := by
  obtain ⟨-, -, hA, hL, -⟩ := hS
  obtain ⟨-, -, -, -, hres, -⟩ := hA
  obtain ⟨-, -, -, hUV, hGc⟩ := hL
  obtain ⟨C, hC0, hC⟩ := hres γ hγ
  obtain ⟨CUV, hCUV0, hCUV⟩ := hUV γ hγ
  obtain ⟨CG, hCG0, hCG⟩ := hGc γ hγ
  refine ⟨CUV * C + CG, by positivity, fun ε hε μ hμ => ?_⟩
  obtain ⟨hE, hEb⟩ := hC ε hε μ hμ
  have hGmu := ((c02_G_mu_decomposition P).2.2.2.2 γ).1 μ
  obtain ⟨-, hV, -⟩ := hCUV ε hε
  have hEG := (c02_aux_Y_sub P hE hGmu).1
  obtain ⟨-, -, hV1, hV1b⟩ := hV _ hEG
  obtain ⟨-, -, hV2, -⟩ := hV _ hGmu
  have e : V_eps_inv P.p ε (residual P.p ε (approximate_solution_family P.p R ε μ)) - G_mu P.p μ =
      V_eps_inv P.p ε (residual P.p ε (approximate_solution_family P.p R ε μ) - G_mu P.p μ) +
        (V_eps_inv P.p ε (G_mu P.p μ) - G_mu P.p μ) := by
    funext y; simp only [V_eps_inv, Pi.add_apply, Pi.sub_apply]; ring
  rw [e]
  have hs := c02_aux_Y_add P hV1 (c02_aux_Y_sub P hV2 hGmu).1
  refine ⟨hs.1, hs.2.trans ?_⟩
  have h1 := hCG ε hε μ hμ
  have h2 := mul_le_mul_of_nonneg_left hEb hCUV0.le
  nlinarith

/-- Consequences of thm:fixed_point_linear_inverse (3) and thm:fixed_point_nonlinear_estimates
(1)-(2) with radius `N`: bounds for `𝒱_ε⁻¹ 𝒩(𝒰_ε⁻¹ w)` and the Lipschitz bound for `𝒢_{ε,μ}`
on `{C_UV ‖w‖ ≤ N}`. -/
theorem c02_aux_forcing_core (P : parameters) {R δ ε₀ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) {γ : ℝ} (hγ : P.admissible γ) :
    ∃ CUV > 0, ∀ N > 0, ∃ CN > 0, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
      (∀ w ∈ X_gamma P.p γ, CUV * xNorm P.p γ w ≤ N →
        V_eps_inv P.p ε (N_eps P.p ε (approximate_solution_family P.p R ε μ) (U_eps_inv P.p ε w)) ∈
          Y_gamma P.p γ ∧
        yNorm P.p γ (V_eps_inv P.p ε (N_eps P.p ε (approximate_solution_family P.p R ε μ)
          (U_eps_inv P.p ε w))) ≤ CUV ^ 2 * CN * ε * xNorm P.p γ w) ∧
      (∀ w₁ ∈ X_gamma P.p γ, ∀ w₂ ∈ X_gamma P.p γ, CUV * xNorm P.p γ w₁ ≤ N →
        CUV * xNorm P.p γ w₂ ≤ N →
        yNorm P.p γ (c02_forcing_map P.p R ε μ w₁ - c02_forcing_map P.p R ε μ w₂) ≤
          CUV ^ 2 * CN * ε * xNorm P.p γ (w₁ - w₂)) := by
  obtain ⟨-, -, -, hL, hN'⟩ := hS
  obtain ⟨-, -, -, hUV, -⟩ := hL
  obtain ⟨CUV, hCUV0, hCUV⟩ := hUV γ hγ
  obtain ⟨hN12, -⟩ := hN'
  refine ⟨CUV, hCUV0, fun N hN => ?_⟩
  obtain ⟨CN, hCN0, hCN⟩ := hN12 γ hγ N hN
  refine ⟨CN, hCN0, fun ε hε μ hμ => ⟨?_, ?_⟩⟩
  · obtain ⟨hU, hV, -⟩ := hCUV ε hε
    obtain ⟨hNb, -⟩ := hCN ε hε μ hμ
    intro w hw hwN
    obtain ⟨-, -, hr, hrN⟩ := hU w hw
    obtain ⟨hNm, hNbd⟩ := hNb _ hr (hrN.trans hwN)
    obtain ⟨-, -, hVm, hVbd⟩ := hV _ hNm
    refine ⟨hVm, ?_⟩
    have hε0 := hε.1
    calc _ ≤ CUV * yNorm P.p γ (N_eps P.p ε (approximate_solution_family P.p R ε μ)
          (U_eps_inv P.p ε w)) := hVbd
      _ ≤ CUV * (CN * ε * (CUV * xNorm P.p γ w)) := by
          gcongr; exact hNbd.trans (by gcongr)
      _ = _ := by ring
  · obtain ⟨hU, hV, -⟩ := hCUV ε hε
    obtain ⟨hNb, hNl⟩ := hCN ε hε μ hμ
    intro w₁ hw₁ w₂ hw₂ h₁ h₂
    obtain ⟨-, -, hr₁, hr₁N⟩ := hU w₁ hw₁
    obtain ⟨-, -, hr₂, hr₂N⟩ := hU w₂ hw₂
    have hN1 := (hNb _ hr₁ (hr₁N.trans h₁)).1
    have hN2 := (hNb _ hr₂ (hr₂N.trans h₂)).1
    have hd := (c02_aux_Y_sub P hN1 hN2).1
    obtain ⟨-, -, hVm, hVbd⟩ := hV _ hd
    have e : c02_forcing_map P.p R ε μ w₁ - c02_forcing_map P.p R ε μ w₂ =
        -V_eps_inv P.p ε (N_eps P.p ε (approximate_solution_family P.p R ε μ) (U_eps_inv P.p ε w₁) -
          N_eps P.p ε (approximate_solution_family P.p R ε μ) (U_eps_inv P.p ε w₂)) := by
      funext y; simp only [c02_forcing_map, V_eps_inv, Pi.sub_apply, Pi.neg_apply]; ring
    rw [e, (c02_aux_Y_neg P hVm).2]
    have hl := hNl _ hr₁ _ hr₂ (hr₁N.trans h₁) (hr₂N.trans h₂)
    have hUd : U_eps_inv P.p ε w₁ - U_eps_inv P.p ε w₂ = U_eps_inv P.p ε (w₁ - w₂) := rfl
    rw [hUd] at hl
    have hUb := (hU _ (c02_aux_X_sub P hw₁ hw₂).1).2.2.2
    have hε0 := hε.1
    calc _ ≤ CUV * yNorm P.p γ (N_eps P.p ε (approximate_solution_family P.p R ε μ)
          (U_eps_inv P.p ε w₁) - N_eps P.p ε (approximate_solution_family P.p R ε μ)
          (U_eps_inv P.p ε w₂)) := hVbd
      _ ≤ CUV * (CN * ε * (CUV * xNorm P.p γ (w₁ - w₂))) := by
          gcongr; exact hl.trans (by gcongr)
      _ = _ := by ring

-- Encoding: the constants `C_UV(γ)`, `C_R(γ)`, `C_𝒩(γ,1)`, `M(γ)` are
-- existential here (all uniform in `ε, μ`, quantified before them).
/-- Blueprint: lem:c02_forcing_bounds.  For admissible `γ`, `ε ∈ [0,ε₀]`, `μ ∈ B̄` and
`w, w₁, w₂ ∈ X_γ` with `C_UV ‖w‖, C_UV ‖wᵢ‖ ≤ 1`:
`‖𝒢(w)‖_{Y_γ} ≤ C_R ε + C_UV² C_𝒩 ε ‖w‖`, `‖𝒢(w₁)-𝒢(w₂)‖_{Y_γ} ≤ C_UV² C_𝒩 ε ‖w₁-w₂‖`, and the
same for `ℋ` in `X_γ` with an extra factor `M(γ)`. -/
theorem c02_forcing_bounds (P : parameters) {R δ ε₀ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) {γ : ℝ} (hγ : P.admissible γ) :
    ∃ CUV > 0, ∃ CR > 0, ∃ CN > 0, ∃ M > 0, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar P.p δ,
      (∀ w ∈ X_gamma P.p γ, CUV * xNorm P.p γ w ≤ 1 →
        c02_forcing_map P.p R ε μ w ∈ Y_gamma P.p γ ∧
        yNorm P.p γ (c02_forcing_map P.p R ε μ w) ≤ CR * ε + CUV ^ 2 * CN * ε * xNorm P.p γ w ∧
        c02_forcing_map_H P.p R ε μ w ∈ X_gamma P.p γ ∧
        xNorm P.p γ (c02_forcing_map_H P.p R ε μ w) ≤
          M * CR * ε + M * CUV ^ 2 * CN * ε * xNorm P.p γ w) ∧
      (∀ w₁ ∈ X_gamma P.p γ, ∀ w₂ ∈ X_gamma P.p γ, CUV * xNorm P.p γ w₁ ≤ 1 →
        CUV * xNorm P.p γ w₂ ≤ 1 →
        yNorm P.p γ (c02_forcing_map P.p R ε μ w₁ - c02_forcing_map P.p R ε μ w₂) ≤
          CUV ^ 2 * CN * ε * xNorm P.p γ (w₁ - w₂) ∧
        xNorm P.p γ (c02_forcing_map_H P.p R ε μ w₁ - c02_forcing_map_H P.p R ε μ w₂) ≤
          M * CUV ^ 2 * CN * ε * xNorm P.p γ (w₁ - w₂)) := by
  have hS' := hS
  obtain ⟨CR, hCR0, hCR⟩ := c02_conjugated_residual P hS hγ
  obtain ⟨CUV, hCUV0, hcore'⟩ := c02_aux_forcing_core P hS hγ
  obtain ⟨CN, hCN0, hcore⟩ := hcore' 1 one_pos
  have hL := hS.2.2.2.1
  obtain ⟨Cℓ, -, M, hM0, -, -, hTP, hTlin, -⟩ := c02_aux_TPi P hL hγ
  refine ⟨CUV, hCUV0, CR, hCR0, CN, hCN0, M, hM0, fun ε hε μ hμ => ⟨fun w hw hwN => ?_,
    fun w₁ hw₁ w₂ hw₂ h₁ h₂ => ?_⟩⟩
  · obtain ⟨hA, hAb⟩ := hCR ε hε μ hμ
    obtain ⟨hB, hBb⟩ := (hcore ε hε μ hμ).1 w hw hwN
    have hF : c02_forcing_map P.p R ε μ w ∈ Y_gamma P.p γ ∧
        yNorm P.p γ (c02_forcing_map P.p R ε μ w) ≤ CR * ε + CUV ^ 2 * CN * ε * xNorm P.p γ w := by
      obtain ⟨hnA, hnAb⟩ := c02_aux_Y_neg P hA
      obtain ⟨h1, h2⟩ := c02_aux_Y_sub P hnA hB
      refine ⟨h1, h2.trans ?_⟩
      rw [hnAb]; linarith
    obtain ⟨-, hHm, hHb, -⟩ := hTP _ hF.1
    refine ⟨hF.1, hF.2, hHm, ?_⟩
    calc xNorm P.p γ (c02_forcing_map_H P.p R ε μ w) ≤ M * yNorm P.p γ (c02_forcing_map P.p R ε μ w) :=
          hHb
      _ ≤ M * (CR * ε + CUV ^ 2 * CN * ε * xNorm P.p γ w) := by gcongr; exact hF.2
      _ = _ := by ring
  · have hlip := (hcore ε hε μ hμ).2 w₁ hw₁ w₂ hw₂ h₁ h₂
    refine ⟨hlip, ?_⟩
    have hF1 := (c02_forcing_map_mem P hS' hε hμ hγ hw₁).1
    have hF2 := (c02_forcing_map_mem P hS' hε hμ hγ hw₂).1
    unfold c02_forcing_map_H
    rw [hTlin _ hF1 _ hF2]
    calc xNorm P.p γ (T_0 P.p (Pi_projection P.p (c02_forcing_map P.p R ε μ w₁ -
          c02_forcing_map P.p R ε μ w₂))) ≤
          M * yNorm P.p γ (c02_forcing_map P.p R ε μ w₁ - c02_forcing_map P.p R ε μ w₂) :=
          (hTP _ (c02_aux_Y_sub P hF1 hF2).1).2.2.1
      _ ≤ M * (CUV ^ 2 * CN * ε * xNorm P.p γ (w₁ - w₂)) := by gcongr
      _ = _ := by ring

/-- Blueprint: lem:c02_H_contraction.  The ball `ℬ_ε = {w ∈ X_{γ₂} : ‖w‖_{X_{γ₂}} ≤ C₀ ε}`. -/
def c02_H_contraction_ball (P : parameters) (C₀ ε : ℝ) : Set (ℝ → ℝ) :=
  {w | w ∈ X_gamma P.p P.γ₂ ∧ xNorm P.p P.γ₂ w ≤ C₀ * ε}

/-- Blueprint: lem:c02_H_contraction.  The conclusion of the lemma for constants `C₀`, `C_R` and
threshold `ε₂`: for `ε ∈ [0,ε₂]`, `μ ∈ B̄`:
(1) `ℋ_{ε,μ}(ℬ_ε) ⊆ ℬ_ε`; (2) `ℋ_{ε,μ}` is `1/2`-Lipschitz on `ℬ_ε` in `X_{γ₂}`;
(3) and in `X_{γ₁}`; (4) `‖𝒢_{ε,μ}(w)‖_{Y_{γ₂}} ≤ 2 C_R ε` on `ℬ_ε`. -/
def c02_H_contraction_conclusion (P : parameters) (R δ C₀ CR ε₂ : ℝ) : Prop :=
  ∀ ε ∈ Icc 0 ε₂, ∀ μ ∈ Bbar P.p δ,
    (∀ w ∈ c02_H_contraction_ball P C₀ ε,
      c02_forcing_map_H P.p R ε μ w ∈ c02_H_contraction_ball P C₀ ε) ∧
    (∀ w₁ ∈ c02_H_contraction_ball P C₀ ε, ∀ w₂ ∈ c02_H_contraction_ball P C₀ ε,
      xNorm P.p P.γ₂ (c02_forcing_map_H P.p R ε μ w₁ - c02_forcing_map_H P.p R ε μ w₂) ≤
        1 / 2 * xNorm P.p P.γ₂ (w₁ - w₂)) ∧
    (∀ w₁ ∈ c02_H_contraction_ball P C₀ ε, ∀ w₂ ∈ c02_H_contraction_ball P C₀ ε,
      xNorm P.p P.γ₁ (c02_forcing_map_H P.p R ε μ w₁ - c02_forcing_map_H P.p R ε μ w₂) ≤
        1 / 2 * xNorm P.p P.γ₁ (w₁ - w₂)) ∧
    (∀ w ∈ c02_H_contraction_ball P C₀ ε,
      c02_forcing_map P.p R ε μ w ∈ Y_gamma P.p P.γ₂ ∧
      yNorm P.p P.γ₂ (c02_forcing_map P.p R ε μ w) ≤ 2 * CR * ε)

-- Encoding: `C_R = C_R(γ₂)` and `C₀ = 2 M(γ₂) C_R(γ₂)` are existential here.
/-- Blueprint: lem:c02_H_contraction.  There are `C_R, C₀ > 0` and `ε₂ ∈ (0,ε₀]` such that `ℋ`
is a self-map and a `1/2`-contraction (in both `X_{γ₂}` and `X_{γ₁}`) of `ℬ_ε`, and
`‖𝒢(w)‖_{Y_{γ₂}} ≤ 2 C_R ε` on `ℬ_ε`, for all `ε ∈ [0,ε₂]`, `μ ∈ B̄`. -/
theorem c02_H_contraction (P : parameters) {R δ ε₀ : ℝ} (hS : c02_forcing_map_setting P R δ ε₀) :
    ∃ CR > 0, ∃ C₀ > 0, ∃ ε₂ > 0, ε₂ ≤ ε₀ ∧ c02_H_contraction_conclusion P R δ C₀ CR ε₂ := by
  obtain ⟨CUV₁, hU₁, CR₁, hR₁, CN₁, hN₁, M₁, hM₁, hB₁⟩ := c02_forcing_bounds P hS (c02_aux_adm₁ P)
  obtain ⟨CUV₂, hU₂, CR₂, hR₂, CN₂, hN₂, M₂, hM₂, hB₂⟩ := c02_forcing_bounds P hS (c02_aux_adm₂ P)
  have hε₀ := hS.2.1
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, C₀ = 2 * M₂ * CR₂ := ⟨_, rfl⟩
  have hC₀p : 0 < C₀ := by rw [hC₀]; positivity
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = min ε₀ (min (1 / (CUV₁ * C₀)) (min (1 / (CUV₂ * C₀))
    (min (1 / (2 * (M₁ * CUV₁ ^ 2 * CN₁))) (min (1 / (2 * (M₂ * CUV₂ ^ 2 * CN₂)))
      (CR₂ / (CUV₂ ^ 2 * CN₂ * C₀)))))) := ⟨_, rfl⟩
  have hε₂p : 0 < ε₂ := by
    simp only [hε₂, lt_min_iff]; refine ⟨hε₀, ?_, ?_, ?_, ?_, ?_⟩ <;> positivity
  refine ⟨CR₂, hR₂, C₀, hC₀p, ε₂, hε₂p, by rw [hε₂]; exact min_le_left _ _,
    fun ε hε μ hμ => ?_⟩
  have hε0 : 0 ≤ ε := hε.1
  have hεε₂ : ε ≤ ε₂ := hε.2
  have hεε₀ : ε ∈ Icc 0 ε₀ := ⟨hε0, hεε₂.trans (by rw [hε₂]; exact min_le_left _ _)⟩
  simp only [hε₂, le_min_iff] at hεε₂
  obtain ⟨-, ha₁, ha₂, hb₁, hb₂, hc⟩ := hεε₂
  rw [le_div_iff₀ (by positivity)] at ha₁ ha₂ hb₁ hb₂ hc
  -- membership of the ball in both spaces
  have hball : ∀ w ∈ c02_H_contraction_ball P C₀ ε,
      w ∈ X_gamma P.p P.γ₂ ∧ CUV₂ * xNorm P.p P.γ₂ w ≤ 1 ∧
      w ∈ X_gamma P.p P.γ₁ ∧ CUV₁ * xNorm P.p P.γ₁ w ≤ 1 := by
    intro w hw
    have hw2 : w ∈ X_gamma P.p P.γ₂ := hw.1
    have hwn : xNorm P.p P.γ₂ w ≤ C₀ * ε := hw.2
    have hinc := c02_X_inclusion P P.hγ₁₂.le
    have h1 := hinc.2 w hw2
    refine ⟨hw2, ?_, hinc.1 hw2, ?_⟩
    · have := mul_le_mul_of_nonneg_left hwn hU₂.le
      linarith
    · have := mul_le_mul_of_nonneg_left (h1.trans hwn) hU₁.le
      linarith
  refine ⟨fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ => ?_, fun w₁ hw₁ w₂ hw₂ => ?_, fun w hw => ?_⟩
  · obtain ⟨hw2, hwN, -, -⟩ := hball w hw
    obtain ⟨-, -, hHm, hHb⟩ := (hB₂ ε hεε₀ μ hμ).1 w hw2 hwN
    refine ⟨hHm, hHb.trans ?_⟩
    have hn := c02_aux_xNorm_nonneg P (γ := P.γ₂) w
    have h1 := mul_le_mul_of_nonneg_right (by linarith : M₂ * CUV₂ ^ 2 * CN₂ * ε ≤ 1 / 2) hn
    have h2 : xNorm P.p P.γ₂ w ≤ C₀ * ε := hw.2
    nlinarith
  · obtain ⟨h1, h1N, -, -⟩ := hball w₁ hw₁
    obtain ⟨h2, h2N, -, -⟩ := hball w₂ hw₂
    refine ((hB₂ ε hεε₀ μ hμ).2 w₁ h1 w₂ h2 h1N h2N).2.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (c02_aux_xNorm_nonneg P _)
  · obtain ⟨-, -, h1, h1N⟩ := hball w₁ hw₁
    obtain ⟨-, -, h2, h2N⟩ := hball w₂ hw₂
    refine ((hB₁ ε hεε₀ μ hμ).2 w₁ h1 w₂ h2 h1N h2N).2.trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (c02_aux_xNorm_nonneg P _)
  · obtain ⟨hw2, hwN, -, -⟩ := hball w hw
    obtain ⟨hGm, hGb, -, -⟩ := (hB₂ ε hεε₀ μ hμ).1 w hw2 hwN
    refine ⟨hGm, hGb.trans ?_⟩
    have h2 : xNorm P.p P.γ₂ w ≤ C₀ * ε := hw.2
    have h3 : CUV₂ ^ 2 * CN₂ * ε * xNorm P.p P.γ₂ w ≤ CUV₂ ^ 2 * CN₂ * ε * (C₀ * ε) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (CUV₂ ^ 2 * CN₂ * C₀ * ε) * ε ≤ CR₂ * ε :=
      mul_le_mul_of_nonneg_right (by linarith) hε0
    nlinarith

/-- Banach's fixed point theorem in a closed subset `B` of `X_γ` for a `1/2`-contraction
(Picard iteration; completeness from lem:c02_X_gamma_banach). -/
theorem c02_aux_contraction_fixed (P : parameters) {γ : ℝ} (B : Set (ℝ → ℝ))
    (hB : ∀ w ∈ B, w ∈ X_gamma P.p γ)
    (hBc : ∀ (u : ℕ → ℝ → ℝ) (r : ℝ → ℝ), (∀ n, u n ∈ B) → r ∈ X_gamma P.p γ →
      Tendsto (fun n => xNorm P.p γ (u n - r)) atTop (𝓝 0) → r ∈ B)
    (T : (ℝ → ℝ) → (ℝ → ℝ)) (hT : ∀ w ∈ B, T w ∈ B)
    (hL : ∀ w₁ ∈ B, ∀ w₂ ∈ B, xNorm P.p γ (T w₁ - T w₂) ≤ 1 / 2 * xNorm P.p γ (w₁ - w₂))
    (w₀ : ℝ → ℝ) (hw₀ : w₀ ∈ B) : ∃ w ∈ B, T w = w := by
  set u : ℕ → ℝ → ℝ := fun n => T^[n] w₀ with hu
  have huB : ∀ n, u n ∈ B := by
    intro n; induction n with
    | zero => simpa [hu] using hw₀
    | succ n ih =>
      have : u (n + 1) = T (u n) := by simp only [hu]; rw [Function.iterate_succ_apply']
      rw [this]; exact hT _ ih
  have hus : ∀ n, u (n + 1) = T (u n) := by
    intro n; simp only [hu]; rw [Function.iterate_succ_apply']
  have huX : ∀ n, u n ∈ X_gamma P.p γ := fun n => hB _ (huB n)
  set d₀ := xNorm P.p γ (u 1 - u 0) with hd₀
  have hd₀n : 0 ≤ d₀ := c02_aux_xNorm_nonneg P _
  have hstep : ∀ n, xNorm P.p γ (u (n + 1) - u n) ≤ (1 / 2) ^ n * d₀ := by
    intro n; induction n with
    | zero => simp [hd₀]
    | succ n ih =>
      have e : u (n + 1 + 1) - u (n + 1) = T (u (n + 1)) - T (u n) := by
        rw [hus (n + 1), hus n]
      rw [e]
      calc xNorm P.p γ (T (u (n + 1)) - T (u n)) ≤ 1 / 2 * xNorm P.p γ (u (n + 1) - u n) :=
            hL _ (huB _) _ (huB _)
        _ ≤ 1 / 2 * ((1 / 2) ^ n * d₀) := by gcongr
        _ = (1 / 2) ^ (n + 1) * d₀ := by ring
  have hcauchy : ∀ n k, xNorm P.p γ (u (n + k) - u n) ≤ 2 * d₀ * ((1 / 2) ^ n - (1 / 2) ^ (n + k)) := by
    intro n k; induction k with
    | zero => simp [c02_aux_xNorm_zero]
    | succ k ih =>
      have := c02_aux_X_tri P (huX (n + (k + 1))) (huX (n + k)) (huX n)
      have h2 := hstep (n + k)
      rw [show n + k + 1 = n + (k + 1) by ring] at h2
      calc xNorm P.p γ (u (n + (k + 1)) - u n) ≤ xNorm P.p γ (u (n + (k + 1)) - u (n + k)) +
            xNorm P.p γ (u (n + k) - u n) := this
        _ ≤ (1 / 2) ^ (n + k) * d₀ + 2 * d₀ * ((1 / 2) ^ n - (1 / 2) ^ (n + k)) := add_le_add h2 ih
        _ = _ := by rw [← add_assoc, pow_succ]; ring
  have hle : ∀ n k, xNorm P.p γ (u (n + k) - u n) ≤ 2 * d₀ * (1 / 2) ^ n := by
    intro n k
    have := hcauchy n k
    have : 0 ≤ (1 / 2 : ℝ) ^ (n + k) := by positivity
    nlinarith
  have hCa : ∀ η > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, xNorm P.p γ (u m - u n) < η := by
    intro η hη
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < η / (2 * d₀ + 1) by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hpow : (1 / 2 : ℝ) ^ (min m n) ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_min hm hn)
    have key : xNorm P.p γ (u m - u n) ≤ 2 * d₀ * (1 / 2) ^ (min m n) := by
      rcases le_total n m with h | h
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [min_eq_right h]; exact hle n k
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [min_eq_left h, c02_aux_X_sub_comm P (huX _) (huX _)]; exact hle m k
    have h3 : (2 * d₀ + 1) * (1 / 2 : ℝ) ^ N < η := by
      rw [lt_div_iff₀ (by positivity)] at hN; linarith
    have h4 : 0 ≤ (1 / 2 : ℝ) ^ (min m n) := by positivity
    nlinarith
  obtain ⟨r, hrX, hr⟩ := (c02_X_gamma_banach P γ).2.2.2.2 u huX hCa
  have hrB := hBc u r huB hrX hr
  refine ⟨r, hrB, ?_⟩
  have hTr := hB _ (hT r hrB)
  have hb : ∀ n, xNorm P.p γ (T r - r) ≤
      1 / 2 * xNorm P.p γ (u n - r) + xNorm P.p γ (u (n + 1) - r) := by
    intro n
    have h1 := c02_aux_X_tri P hTr (huX (n + 1)) hrX
    rw [hus n] at h1 ⊢
    have h2 := hL r hrB (u n) (huB n)
    rw [c02_aux_X_sub_comm P hrX (huX n)] at h2
    rw [c02_aux_X_sub_comm P hTr (hB _ (hT _ (huB n)))] at h1
    rw [← hus n] at h1 ⊢
    rw [c02_aux_X_sub_comm P (huX (n + 1)) hTr] at h1
    rw [hus n] at h1 ⊢
    linarith
  have hlim : Tendsto (fun n => 1 / 2 * xNorm P.p γ (u n - r) + xNorm P.p γ (u (n + 1) - r))
      atTop (𝓝 0) := by
    have := (hr.const_mul (1 / 2)).add (hr.comp (tendsto_add_atTop_nat 1))
    simpa using this
  have h0 := ge_of_tendsto' hlim hb
  have hn := c02_aux_xNorm_nonneg P (γ := γ) (T r - r)
  exact c02_aux_X_eq_of_dist P hTr hrX (le_antisymm h0 hn)

/-- Blueprint: def:c02_fixed_point_selection (the fixed point `w_{ε,μ}` of lem:c02_w_exists).  A fixed point of
`ℋ_{ε,μ}` in the ball `{w ∈ X_{γ₂} : ‖w‖_{X_{γ₂}} ≤ ρ}` if one exists (it is unique for
`ρ = C₀ ε`, `ε ≤ ε₂`, by lem:c02_w_exists), `0` otherwise. -/
def c02_K_map_w (P : parameters) (R ε : ℝ) (μ : ℂ) (ρ : ℝ) : ℝ → ℝ :=
  open scoped Classical in
  if h : ∃ w : ℝ → ℝ, (w ∈ X_gamma P.p P.γ₂ ∧ xNorm P.p P.γ₂ w ≤ ρ) ∧
      c02_forcing_map_H P.p R ε μ w = w then Classical.choose h else 0

/-- Blueprint: def:c02_K_map.  The obstruction map `𝒦_ε(μ) = μ_*[1 - ℓ(𝒢_{ε,μ}(w_{ε,μ}))]`, where
`w_{ε,μ} = c02_K_map_w P R ε μ ρ` with the radius `ρ = C₀ ε` of `ℬ_ε`. -/
def c02_K_map (P : parameters) (R ε : ℝ) (μ : ℂ) (ρ : ℝ) : ℂ :=
  mu_star P.p * (1 - ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ ρ)))

/-- Blueprint: lem:c02_K_map_fixed_iff.  `𝒦_ε(μ) = μ` iff `ℓ(𝒢_{ε,μ}(w_{ε,μ})) = 1 - μ/μ_*`. -/
theorem c02_K_map_fixed_iff (P : parameters) (R ε : ℝ) (μ : ℂ) (ρ : ℝ) :
    c02_K_map P R ε μ ρ = μ ↔
      ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ ρ)) = 1 - μ / mu_star P.p := by
  have h0 := c02_aux_mu_star_ne P
  unfold c02_K_map
  generalize ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ ρ)) = L
  constructor
  · intro h; rw [← h, mul_div_cancel_left₀ _ h0]; ring
  · intro h; rw [h, sub_sub_cancel, mul_div_cancel₀ _ h0]

/-- Blueprint: lem:c02_w_exists.  For `ε ∈ [0,ε₂]`, `μ ∈ B̄` there is a unique
`w_{ε,μ} ∈ ℬ_ε` with `w_{ε,μ} = ℋ_{ε,μ}(w_{ε,μ})` (so `‖w_{ε,μ}‖_{X_{γ₂}} ≤ C₀ ε`), and it is
`c02_K_map_w P R ε μ (C₀ ε)`. -/
theorem c02_w_exists (P : parameters) {R δ ε₀ C₀ CR ε₂ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) (hC₀ : 0 < C₀) (hε₂ : ε₂ ≤ ε₀)
    (hH : c02_H_contraction_conclusion P R δ C₀ CR ε₂) {ε : ℝ} (hε : ε ∈ Icc 0 ε₂) {μ : ℂ}
    (hμ : μ ∈ Bbar P.p δ) :
    (∃! w : ℝ → ℝ, w ∈ c02_H_contraction_ball P C₀ ε ∧ c02_forcing_map_H P.p R ε μ w = w) ∧
    c02_K_map_w P R ε μ (C₀ * ε) ∈ c02_H_contraction_ball P C₀ ε ∧
    c02_forcing_map_H P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)) = c02_K_map_w P R ε μ (C₀ * ε) ∧
    xNorm P.p P.γ₂ (c02_K_map_w P R ε μ (C₀ * ε)) ≤ C₀ * ε := by
  obtain ⟨hself, hlip, -, -⟩ := hH ε hε μ hμ
  have hε0 : 0 ≤ ε := hε.1
  have hX0 := c02_aux_X_zero P (γ := P.γ₂)
  have hn0 : xNorm P.p P.γ₂ (0 : ℝ → ℝ) = 0 := by
    have := (c02_aux_X_smul P 0 hX0).2
    simpa using this
  have h0 : (0 : ℝ → ℝ) ∈ c02_H_contraction_ball P C₀ ε :=
    ⟨hX0, by rw [hn0]; positivity⟩
  have hclosed : ∀ (u : ℕ → ℝ → ℝ) (r : ℝ → ℝ), (∀ n, u n ∈ c02_H_contraction_ball P C₀ ε) →
      r ∈ X_gamma P.p P.γ₂ → Tendsto (fun n => xNorm P.p P.γ₂ (u n - r)) atTop (𝓝 0) →
      r ∈ c02_H_contraction_ball P C₀ ε := by
    intro u r hu hr ht
    refine ⟨hr, ?_⟩
    have hb : ∀ n, xNorm P.p P.γ₂ r ≤ xNorm P.p P.γ₂ (u n - r) + C₀ * ε := by
      intro n
      have := c02_aux_X_le_sub_add P hr (hu n).1
      rw [c02_aux_X_sub_comm P hr (hu n).1] at this
      linarith [(hu n).2]
    have := ge_of_tendsto' (ht.add_const (C₀ * ε)) hb
    simpa using this
  obtain ⟨w, hwB, hwfix⟩ := c02_aux_contraction_fixed P _
    (fun w (hw : w ∈ c02_H_contraction_ball P C₀ ε) => hw.1) hclosed _ hself hlip
    0 h0
  have hex : ∃ w : ℝ → ℝ, (w ∈ X_gamma P.p P.γ₂ ∧ xNorm P.p P.γ₂ w ≤ C₀ * ε) ∧
      c02_forcing_map_H P.p R ε μ w = w := ⟨w, hwB, hwfix⟩
  have huniq : ∀ w₁ w₂, w₁ ∈ c02_H_contraction_ball P C₀ ε →
      c02_forcing_map_H P.p R ε μ w₁ = w₁ → w₂ ∈ c02_H_contraction_ball P C₀ ε →
      c02_forcing_map_H P.p R ε μ w₂ = w₂ → w₁ = w₂ := by
    intro w₁ w₂ h₁ f₁ h₂ f₂
    have := hlip w₁ h₁ w₂ h₂
    rw [f₁, f₂] at this
    have hn := c02_aux_xNorm_nonneg P (γ := P.γ₂) (w₁ - w₂)
    exact c02_aux_X_eq_of_dist P h₁.1 h₂.1 (by linarith)
  have hK : c02_K_map_w P R ε μ (C₀ * ε) ∈ c02_H_contraction_ball P C₀ ε ∧
      c02_forcing_map_H P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)) =
        c02_K_map_w P R ε μ (C₀ * ε) := by
    unfold c02_K_map_w
    simp only [hex, ↓reduceDIte]
    exact ⟨(Classical.choose_spec hex).1, (Classical.choose_spec hex).2⟩
  exact ⟨⟨w, ⟨hwB, hwfix⟩, fun v hv => huniq v w hv.1 hv.2 hwB hwfix⟩, hK.1, hK.2, hK.1.2⟩

/-! ### Continuity in `μ` and the scalar equation -/

/-- Blueprint: lem:c02_forcing_continuity.  For fixed `ε ∈ [0,ε₀]` and `w ∈ X_{γ₂}`,
`μ ↦ 𝒢_{ε,μ}(w)` is continuous `B̄ → Y_{γ₁}` and `μ ↦ ℋ_{ε,μ}(w)` is continuous `B̄ → X_{γ₁}`. -/
theorem c02_forcing_continuity (P : parameters) {R δ ε₀ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) {ε : ℝ} (hε : ε ∈ Icc 0 ε₀) {w : ℝ → ℝ}
    (hw : w ∈ X_gamma P.p P.γ₂) :
    ∀ μ ∈ Bbar P.p δ,
      c02_forcing_map P.p R ε μ w ∈ Y_gamma P.p P.γ₁ ∧
      Tendsto (fun ν => yNorm P.p P.γ₁ (c02_forcing_map P.p R ε ν w - c02_forcing_map P.p R ε μ w))
        (𝓝[Bbar P.p δ] μ) (𝓝 0) ∧
      c02_forcing_map_H P.p R ε μ w ∈ X_gamma P.p P.γ₁ ∧
      Tendsto (fun ν => xNorm P.p P.γ₁
          (c02_forcing_map_H P.p R ε ν w - c02_forcing_map_H P.p R ε μ w))
        (𝓝[Bbar P.p δ] μ) (𝓝 0) := by
  intro μ hμ
  have hadm := c02_aux_adm₁ P
  have hw1 := (c02_X_inclusion P P.hγ₁₂.le).1 hw
  have hmem : ∀ ν ∈ Bbar P.p δ, c02_forcing_map P.p R ε ν w ∈ Y_gamma P.p P.γ₁ ∧
      c02_forcing_map_H P.p R ε ν w ∈ X_gamma P.p P.γ₁ := fun ν hν =>
    c02_forcing_map_mem P hS hε hν hadm hw1
  obtain ⟨Cℓ, -, M, hM0, -, -, hTP, hTlin, -⟩ := c02_aux_TPi P hS.2.2.2.1 hadm
  obtain ⟨-, -, hA, hL, hN⟩ := hS
  obtain ⟨-, -, -, -, hres, hcont⟩ := hA
  obtain ⟨-, -, -, hUV, -⟩ := hL
  obtain ⟨hN12, hN3⟩ := hN
  obtain ⟨C, -, hC⟩ := hres _ hadm
  obtain ⟨CUV, hCUV0, hCUV⟩ := hUV _ hadm
  obtain ⟨CUV₂, -, hCUV₂⟩ := hUV _ (c02_aux_adm₂ P)
  obtain ⟨hU, hV, -⟩ := hCUV ε hε
  set r := U_eps_inv P.p ε w with hr
  have hr2 : r ∈ X_gamma P.p P.γ₂ := ((hCUV₂ ε hε).1 w hw).2.2.1
  have hr1 : r ∈ X_gamma P.p P.γ₁ := (hU w hw1).2.2.1
  obtain ⟨CN, -, hCN⟩ := hN12 _ hadm (xNorm P.p P.γ₁ r + 1)
    (by linarith [c02_aux_xNorm_nonneg P (γ := P.γ₁) r])
  have hNm : ∀ ν ∈ Bbar P.p δ, N_eps P.p ε (approximate_solution_family P.p R ε ν) r ∈
      Y_gamma P.p P.γ₁ := fun ν hν => ((hCN ε hε ν hν).1 r hr1 (by linarith)).1
  have hGmu := (c02_G_mu_decomposition P).2.2.2.2 P.γ₁
  -- the difference identity and bound
  have hbound : ∀ ν ∈ Bbar P.p δ,
      yNorm P.p P.γ₁ (c02_forcing_map P.p R ε ν w - c02_forcing_map P.p R ε μ w) ≤
        CUV * yNorm P.p P.γ₁ (residual P.p ε (approximate_solution_family P.p R ε ν) -
          residual P.p ε (approximate_solution_family P.p R ε μ)) +
        yNorm P.p P.γ₁ (G_mu P.p ν - G_mu P.p μ) +
        CUV * yNorm P.p P.γ₁ (N_eps P.p ε (approximate_solution_family P.p R ε ν) r -
          N_eps P.p ε (approximate_solution_family P.p R ε μ) r) := by
    intro ν hν
    have hE := (c02_aux_Y_sub P (hC ε hε ν hν).1 (hC ε hε μ hμ).1).1
    have hG := (c02_aux_Y_sub P (hGmu.1 ν) (hGmu.1 μ)).1
    have hNd := (c02_aux_Y_sub P (hNm ν hν) (hNm μ hμ)).1
    obtain ⟨-, -, hVE, hVEb⟩ := hV _ hE
    obtain ⟨-, -, hVN, hVNb⟩ := hV _ hNd
    have e : c02_forcing_map P.p R ε ν w - c02_forcing_map P.p R ε μ w =
        (-V_eps_inv P.p ε (residual P.p ε (approximate_solution_family P.p R ε ν) -
          residual P.p ε (approximate_solution_family P.p R ε μ)) +
          (G_mu P.p ν - G_mu P.p μ)) -
        V_eps_inv P.p ε (N_eps P.p ε (approximate_solution_family P.p R ε ν) r -
          N_eps P.p ε (approximate_solution_family P.p R ε μ) r) := by
      funext y
      simp only [c02_forcing_map, V_eps_inv, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, hr]
      ring
    rw [e]
    obtain ⟨hn1, hn1b⟩ := c02_aux_Y_neg P hVE
    obtain ⟨hs1, hs1b⟩ := c02_aux_Y_add P hn1 hG
    obtain ⟨-, hs2b⟩ := c02_aux_Y_sub P hs1 hVN
    linarith
  have hlimG : Tendsto (fun ν => yNorm P.p P.γ₁ (c02_forcing_map P.p R ε ν w -
      c02_forcing_map P.p R ε μ w)) (𝓝[Bbar P.p δ] μ) (𝓝 0) := by
    have h1 := (hcont ε hε μ hμ).2 _ hadm
    have h2 := ((hGmu.2.1 μ).mono_left nhdsWithin_le_nhds :
      Tendsto (fun ν => yNorm P.p P.γ₁ (G_mu P.p ν - G_mu P.p μ)) (𝓝[Bbar P.p δ] μ) (𝓝 0))
    have h3 := hN3 ε hε r hr2 μ hμ
    have hsum := ((h1.const_mul CUV).add h2).add (h3.const_mul CUV)
    simp only [mul_zero, add_zero] at hsum
    refine squeeze_zero' (Eventually.of_forall fun ν => c02_aux_yNorm_nonneg P _) ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with ν hν
    exact hbound ν hν
  refine ⟨(hmem μ hμ).1, hlimG, (hmem μ hμ).2, ?_⟩
  have hsum := hlimG.const_mul M
  rw [mul_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun ν => c02_aux_xNorm_nonneg P _) ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with ν hν
  unfold c02_forcing_map_H
  rw [hTlin _ (hmem ν hν).1 _ (hmem μ hμ).1]
  exact (hTP _ (c02_aux_Y_sub P (hmem ν hν).1 (hmem μ hμ).1).1).2.2.1

/-- Blueprint: lem:c02_w_continuity.  For `ε ∈ [0,ε₂]`, `μ ↦ w_{ε,μ}` is continuous
`B̄ → X_{γ₁}`. -/
theorem c02_w_continuity (P : parameters) {R δ ε₀ C₀ CR ε₂ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) (hC₀ : 0 < C₀) (hε₂ : ε₂ ≤ ε₀)
    (hH : c02_H_contraction_conclusion P R δ C₀ CR ε₂) {ε : ℝ} (hε : ε ∈ Icc 0 ε₂) :
    ∀ μ ∈ Bbar P.p δ,
      Tendsto (fun ν => xNorm P.p P.γ₁ (c02_K_map_w P R ε ν (C₀ * ε) - c02_K_map_w P R ε μ (C₀ * ε)))
        (𝓝[Bbar P.p δ] μ) (𝓝 0) := by
  intro μ hμ
  have hεε₀ : ε ∈ Icc 0 ε₀ := ⟨hε.1, hε.2.trans hε₂⟩
  have hinc := c02_X_inclusion P P.hγ₁₂.le
  obtain ⟨-, hwμB, hwμH, -⟩ := c02_w_exists P hS hC₀ hε₂ hH hε hμ
  have hcont := c02_forcing_continuity P hS hεε₀ hwμB.1 μ hμ
  have hlim := hcont.2.2.2.const_mul 2
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun ν => c02_aux_xNorm_nonneg P _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ν hν
  obtain ⟨-, hwνB, hwνH, -⟩ := c02_w_exists P hS hC₀ hε₂ hH hε hν
  have hcont' := c02_forcing_continuity P hS hεε₀ hwμB.1 ν hν
  set wν := c02_K_map_w P R ε ν (C₀ * ε)
  set wμ := c02_K_map_w P R ε μ (C₀ * ε)
  have hwν1 := hinc.1 hwνB.1
  have hwμ1 := hinc.1 hwμB.1
  have hc := (hH ε hε ν hν).2.2.1 wν hwνB wμ hwμB
  have htri := c02_aux_X_tri P (γ := P.γ₁) (G := c02_forcing_map_H P.p R ε ν wν)
    (H := c02_forcing_map_H P.p R ε ν wμ) (K := c02_forcing_map_H P.p R ε μ wμ)
    (by rw [hwνH]; exact hwν1) hcont'.2.2.1 hcont.2.2.1
  rw [hwνH, hwμH] at htri
  rw [hwνH] at hc
  rw [hwμH]
  linarith

/-- Blueprint: lem:c02_K_continuity.  For `ε ∈ [0,ε₂]`, `μ ↦ 𝒢_{ε,μ}(w_{ε,μ})` is continuous
`B̄ → Y_{γ₁}` and `𝒦_ε : B̄ → ℂ` is continuous. -/
theorem c02_K_continuity (P : parameters) {R δ ε₀ C₀ CR ε₂ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) (hC₀ : 0 < C₀) (hε₂ : ε₂ ≤ ε₀)
    (hH : c02_H_contraction_conclusion P R δ C₀ CR ε₂) {ε : ℝ} (hε : ε ∈ Icc 0 ε₂) :
    (∀ μ ∈ Bbar P.p δ,
      c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)) ∈ Y_gamma P.p P.γ₁ ∧
      Tendsto (fun ν => yNorm P.p P.γ₁
          (c02_forcing_map P.p R ε ν (c02_K_map_w P R ε ν (C₀ * ε)) -
            c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε))))
        (𝓝[Bbar P.p δ] μ) (𝓝 0)) ∧
    ContinuousOn (fun μ => c02_K_map P R ε μ (C₀ * ε)) (Bbar P.p δ) := by
  have hεε₀ : ε ∈ Icc 0 ε₀ := ⟨hε.1, hε.2.trans hε₂⟩
  have hinc := c02_X_inclusion P P.hγ₁₂.le
  have hadm := c02_aux_adm₁ P
  obtain ⟨CUV, hCUV0, hcore'⟩ := c02_aux_forcing_core P hS hadm
  obtain ⟨CN, hCN0, hcore⟩ := hcore' (CUV * (C₀ * ε) + 1) (by
    have := hε.1; positivity)
  obtain ⟨Cℓ, hCℓ0, M, -, -, hℓd, -, -, -⟩ := c02_aux_TPi P hS.2.2.2.1 hadm
  -- the ball lies in `{C_UV ‖w‖_{X_{γ₁}} ≤ N}`
  have hballN : ∀ w ∈ c02_H_contraction_ball P C₀ ε,
      w ∈ X_gamma P.p P.γ₁ ∧ CUV * xNorm P.p P.γ₁ w ≤ CUV * (C₀ * ε) + 1 := by
    intro w hw
    refine ⟨hinc.1 hw.1, ?_⟩
    have := mul_le_mul_of_nonneg_left ((hinc.2 w hw.1).trans hw.2) hCUV0.le
    linarith
  have hGmem : ∀ μ ∈ Bbar P.p δ,
      c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)) ∈ Y_gamma P.p P.γ₁ := by
    intro μ hμ
    obtain ⟨-, hwB, -, -⟩ := c02_w_exists P hS hC₀ hε₂ hH hε hμ
    exact (c02_forcing_map_mem P hS hεε₀ hμ hadm (hinc.1 hwB.1)).1
  have hGlim : ∀ μ ∈ Bbar P.p δ, Tendsto (fun ν => yNorm P.p P.γ₁
      (c02_forcing_map P.p R ε ν (c02_K_map_w P R ε ν (C₀ * ε)) -
        c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)))) (𝓝[Bbar P.p δ] μ) (𝓝 0) := by
    intro μ hμ
    obtain ⟨-, hwμB, -, -⟩ := c02_w_exists P hS hC₀ hε₂ hH hε hμ
    have hcont := c02_forcing_continuity P hS hεε₀ hwμB.1 μ hμ
    have hwc := c02_w_continuity P hS hC₀ hε₂ hH hε μ hμ
    have hsum := (hwc.const_mul (CUV ^ 2 * CN * ε)).add hcont.2.1
    simp only [mul_zero, add_zero] at hsum
    refine squeeze_zero' (Eventually.of_forall fun ν => c02_aux_yNorm_nonneg P _) ?_ hsum
    filter_upwards [self_mem_nhdsWithin] with ν hν
    obtain ⟨-, hwνB, -, -⟩ := c02_w_exists P hS hC₀ hε₂ hH hε hν
    have hcont' := c02_forcing_continuity P hS hεε₀ hwμB.1 ν hν
    obtain ⟨hwν1, hwνN⟩ := hballN _ hwνB
    obtain ⟨hwμ1, hwμN⟩ := hballN _ hwμB
    have hlip := (hcore ε hεε₀ ν hν).2 _ hwν1 _ hwμ1 hwνN hwμN
    have htri := c02_aux_Y_tri P (hGmem ν hν) hcont'.1 hcont.1
    linarith
  refine ⟨fun μ hμ => ⟨hGmem μ hμ, hGlim μ hμ⟩, fun μ hμ => ?_⟩
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsum := (hGlim μ hμ).const_mul (‖mu_star P.p‖ * Cℓ)
  rw [mul_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun ν => norm_nonneg _) ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with ν hν
  have e : c02_K_map P R ε ν (C₀ * ε) - c02_K_map P R ε μ (C₀ * ε) =
      -(mu_star P.p * (ell P.p (c02_forcing_map P.p R ε ν (c02_K_map_w P R ε ν (C₀ * ε))) -
        ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε))))) := by
    unfold c02_K_map; ring
  rw [e, norm_neg, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hℓd _ (hGmem ν hν) _ (hGmem μ hμ)) (norm_nonneg _)

-- Encoding: the constant `C_* = 2|μ_*| C_ℓ(γ₂) C_R(γ₂)` is existential here.
/-- Blueprint: lem:c02_K_self_map.  There is `C_* > 0` with
`|𝒦_ε(μ) - μ_*| = |μ_*| |ℓ(𝒢_{ε,μ}(w_{ε,μ}))| ≤ C_* ε` for `ε ∈ [0,ε₂]`, `μ ∈ B̄`, and
`𝒦_ε(B̄) ⊆ B̄` for `ε ∈ [0,ε₁]`, `ε₁ = min(ε₂, δ/C_*)`. -/
theorem c02_K_self_map (P : parameters) {R δ ε₀ C₀ CR ε₂ : ℝ}
    (hS : c02_forcing_map_setting P R δ ε₀) (hC₀ : 0 < C₀) (hε₂ : ε₂ ≤ ε₀)
    (hH : c02_H_contraction_conclusion P R δ C₀ CR ε₂) :
    ∃ Cs > 0,
      (∀ ε ∈ Icc 0 ε₂, ∀ μ ∈ Bbar P.p δ,
        ‖c02_K_map P R ε μ (C₀ * ε) - mu_star P.p‖ =
          ‖mu_star P.p‖ * ‖ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)))‖ ∧
        ‖c02_K_map P R ε μ (C₀ * ε) - mu_star P.p‖ ≤ Cs * ε) ∧
      (∀ ε ∈ Icc 0 (min ε₂ (δ / Cs)),
        MapsTo (fun μ => c02_K_map P R ε μ (C₀ * ε)) (Bbar P.p δ) (Bbar P.p δ)) := by
  obtain ⟨Cℓ, hCℓ0, M, -, hℓb, -, -, -, -⟩ := c02_aux_TPi P hS.2.2.2.1 (c02_aux_adm₂ P)
  have hμ0 := norm_pos_iff.2 (c02_aux_mu_star_ne P)
  have key : ∀ ε ∈ Icc 0 ε₂, ∀ μ ∈ Bbar P.p δ,
      ‖c02_K_map P R ε μ (C₀ * ε) - mu_star P.p‖ =
        ‖mu_star P.p‖ * ‖ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)))‖ ∧
      ‖c02_K_map P R ε μ (C₀ * ε) - mu_star P.p‖ ≤ ‖mu_star P.p‖ * Cℓ * (2 * |CR| + 1) * ε := by
    intro ε hε μ hμ
    obtain ⟨-, hwB, -, -⟩ := c02_w_exists P hS hC₀ hε₂ hH hε hμ
    obtain ⟨hGm, hGb⟩ := (hH ε hε μ hμ).2.2.2 _ hwB
    have e : c02_K_map P R ε μ (C₀ * ε) - mu_star P.p =
        -(mu_star P.p * ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)))) := by
      unfold c02_K_map; ring
    have he : ‖c02_K_map P R ε μ (C₀ * ε) - mu_star P.p‖ =
        ‖mu_star P.p‖ * ‖ell P.p (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε)))‖ := by
      rw [e, norm_neg, norm_mul]
    refine ⟨he, ?_⟩
    rw [he, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := hℓb _ hGm
    have hε0 := hε.1
    have h2 : 2 * CR * ε ≤ (2 * |CR| + 1) * ε :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self CR]) hε0
    calc _ ≤ Cℓ * yNorm P.p P.γ₂ (c02_forcing_map P.p R ε μ (c02_K_map_w P R ε μ (C₀ * ε))) := h1
      _ ≤ Cℓ * ((2 * |CR| + 1) * ε) := by gcongr; linarith
  refine ⟨‖mu_star P.p‖ * Cℓ * (2 * |CR| + 1), by positivity, fun ε hε μ hμ => key ε hε μ hμ,
    fun ε hε μ hμ => ?_⟩
  have hε' : ε ∈ Icc 0 ε₂ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have h1 := (key ε hε' μ hμ).2
  have hCs : 0 < ‖mu_star P.p‖ * Cℓ * (2 * |CR| + 1) := by positivity
  have h2 : ε ≤ δ / (‖mu_star P.p‖ * Cℓ * (2 * |CR| + 1)) := hε.2.trans (min_le_right _ _)
  rw [le_div_iff₀ hCs] at h2
  show c02_K_map P R ε μ (C₀ * ε) ∈ Metric.closedBall (mu_star P.p) δ
  rw [Metric.mem_closedBall, dist_eq_norm]
  linarith

/-- A continuous `F : [0,1] → ℂ` with `exp ∘ F = 1` is constant. -/
theorem c02_aux_exp_one_const {F : unitInterval → ℂ} (hF : Continuous F)
    (h1 : ∀ t, Complex.exp (F t) = 1) (t : unitInterval) : F t = F 0 := by
  have hS : IsClopen {t | F t = F 0} := by
    refine ⟨isClosed_eq hF continuous_const, ?_⟩
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    have hev : ∀ᶠ t in 𝓝 t₀, ‖F t - F t₀‖ < 2 * π :=
      ((Metric.tendsto_nhds.1 (hF.continuousAt (x := t₀))) (2 * π) (by positivity)).mono
        fun t ht => by rwa [dist_eq_norm] at ht
    filter_upwards [hev] with t ht
    show F t = F 0
    rw [← (show F t₀ = F 0 from ht₀)]
    have he : Complex.exp (F t - F t₀) = 1 := by rw [Complex.exp_sub, h1, h1, div_one]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he
    have hn0 : n = 0 := by
      rw [hn] at ht
      have hnorm : ‖(n : ℂ) * (2 * π * Complex.I)‖ = |(n : ℝ)| * (2 * π) := by
        rw [norm_mul, Complex.norm_intCast, norm_mul, Complex.norm_I, mul_one, norm_mul,
          Complex.norm_real, Complex.norm_two, Real.norm_eq_abs, abs_of_pos pi_pos]
      rw [hnorm] at ht
      have : |(n : ℝ)| < 1 := by
        have := pi_pos
        by_contra hc; rw [not_lt] at hc; nlinarith
      rw [← Int.cast_abs, ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at this
      exact this
    rw [hn0] at hn
    simpa [sub_eq_zero] using hn
  have huniv := hS.eq_univ ⟨0, rfl⟩
  have ht : t ∈ {t | F t = F 0} := by rw [huniv]; trivial
  exact ht

/-- Two continuous logarithms of the same loop have the same increment. -/
theorem c02_aux_lift_incr {F G : unitInterval → ℂ} (hF : Continuous F) (hG : Continuous G)
    (h : ∀ t, Complex.exp (F t) = Complex.exp (G t)) : F 1 - F 0 = G 1 - G 0 := by
  have := c02_aux_exp_one_const (F := fun t => F t - G t) (hF.sub hG)
    (fun t => by rw [Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]) 1
  linear_combination this

/-- Homotopy invariance of the increment of a continuous logarithm along a homotopy of
nonvanishing loops (homotopy lifting for `exp : ℂ → ℂ \ {0}`). -/
theorem c02_aux_winding_homotopy (K : unitInterval × unitInterval → ℂ) (hK : Continuous K)
    (hK0 : ∀ x, K x ≠ 0) (hloop : ∀ u, K (u, 0) = K (u, 1)) (F0 : unitInterval → ℂ)
    (hF0 : Continuous F0) (hF0l : ∀ t, Complex.exp (F0 t) = K (0, t)) :
    ∃ F1 : unitInterval → ℂ, Continuous F1 ∧ (∀ t, Complex.exp (F1 t) = K (1, t)) ∧
      F1 1 - F1 0 = F0 1 - F0 0 := by
  let H : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun x => ⟨K x, hK0 x⟩, hK.subtype_mk _⟩
  let f : C(unitInterval, ℂ) := ⟨F0, hF0⟩
  have H_0 : ∀ a, H (0, a) =
      (fun z : ℂ => (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0})) (f a) :=
    fun a => Subtype.ext (hF0l a).symm
  set L := Complex.isCoveringMap_exp.liftHomotopy H f H_0 with hLdef
  have hL : ∀ x, Complex.exp (L x) = K x := fun x =>
    congrArg Subtype.val (congrFun (Complex.isCoveringMap_exp.liftHomotopy_lifts H f H_0) x)
  have hL0 : ∀ t, L (0, t) = F0 t := Complex.isCoveringMap_exp.liftHomotopy_zero H f H_0
  have hD := c02_aux_exp_one_const (F := fun u => L (u, 1) - L (u, 0))
    ((L.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (L.continuous.comp (continuous_id.prodMk continuous_const)))
    (fun u => by rw [Complex.exp_sub, hL, hL, hloop, div_self (hK0 _)]) 1
  refine ⟨fun t => L (1, t), L.continuous.comp (continuous_const.prodMk continuous_id),
    fun t => hL _, ?_⟩
  rw [hD, hL0, hL0]

/-- Blueprint: lem:c02_brouwer_disc.  Brouwer's fixed point theorem for a closed disc in `ℂ`:
a continuous self-map of `B̄(c,δ)` has a fixed point. -/
theorem c02_brouwer_disc (c : ℂ) {δ : ℝ} (hδ : 0 < δ) (g : ℂ → ℂ)
    (hg : ContinuousOn g (Metric.closedBall c δ))
    (hgm : MapsTo g (Metric.closedBall c δ) (Metric.closedBall c δ)) :
    ∃ μ ∈ Metric.closedBall c δ, g μ = μ := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  set h : ℂ → ℂ := fun x => (g (c + δ * x) - c) / δ with hdef
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hmem : ∀ x : ℂ, ‖x‖ ≤ 1 → c + δ * x ∈ Metric.closedBall c δ := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ]
    nlinarith [norm_nonneg x]
  have hh1 : ∀ x : ℂ, ‖x‖ ≤ 1 → ‖h x‖ ≤ 1 := by
    intro x hx
    have := hgm (hmem x hx)
    rw [Metric.mem_closedBall, dist_eq_norm] at this
    rw [hdef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, div_le_one hδ]
    exact this
  have hhfix : ∀ x : ℂ, ‖x‖ ≤ 1 → h x ≠ x := by
    intro x hx hfix
    apply hno _ (hmem x hx)
    rw [hdef] at hfix; simp only at hfix
    rw [div_eq_iff hδc] at hfix
    linear_combination hfix
  have hhc : ContinuousOn h (Metric.closedBall 0 1) := by
    refine ContinuousOn.div_const (ContinuousOn.sub ?_ continuousOn_const) _
    refine hg.comp (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hmem x hx
  set γ : unitInterval → ℂ := fun t => Complex.exp (2 * π * Complex.I * ((t : ℝ) : ℂ)) with hγ
  have hγc : Continuous γ := Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val))
  have hγn : ∀ t, ‖γ t‖ = 1 := by
    intro t; rw [hγ]; simp only
    rw [Complex.norm_exp]; simp
  have hγ01 : γ 0 = γ 1 := by
    rw [hγ]; simp only [Set.Icc.coe_zero, Set.Icc.coe_one, Complex.ofReal_zero,
      Complex.ofReal_one, mul_zero, mul_one, Complex.exp_zero]
    exact (Complex.exp_two_pi_mul_I).symm
  have hball : ∀ (u t : unitInterval), ‖((u : ℝ) : ℂ) * γ t‖ ≤ 1 := by
    intro u t
    rw [norm_mul, hγn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg u.2.1]
    exact u.2.2
  -- first homotopy: `u γ - h(u γ)`
  set K1 : unitInterval × unitInterval → ℂ := fun x =>
    ((x.1 : ℝ) : ℂ) * γ x.2 - h (((x.1 : ℝ) : ℂ) * γ x.2) with hK1
  have hK1c : Continuous K1 := by
    have hc : Continuous fun x : unitInterval × unitInterval => ((x.1 : ℝ) : ℂ) * γ x.2 :=
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        (hγc.comp continuous_snd)
    refine hc.sub (hhc.comp_continuous hc fun x => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]; exact hball x.1 x.2
  have hK10 : ∀ x, K1 x ≠ 0 := by
    intro x hx
    exact hhfix _ (hball x.1 x.2) (sub_eq_zero.1 hx).symm
  have hh0 : h 0 ≠ 0 := by
    have := hhfix 0 (by simp); exact this
  obtain ⟨F1, hF1c, hF1l, hF1i⟩ := c02_aux_winding_homotopy K1 hK1c hK10
    (fun u => by simp only [hK1, hγ01]) (fun _ => Complex.log (-h 0)) continuous_const
    (fun t => by
      rw [Complex.exp_log (neg_ne_zero.2 hh0)]
      simp [hK1])
  -- second homotopy: `γ - u h(γ)`
  set K2 : unitInterval × unitInterval → ℂ := fun x => γ x.2 - ((x.1 : ℝ) : ℂ) * h (γ x.2)
    with hK2
  have hK2c : Continuous K2 := by
    refine (hγc.comp continuous_snd).sub ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst)).mul (hhc.comp_continuous
        (hγc.comp continuous_snd) fun x => ?_))
    rw [Metric.mem_closedBall, dist_zero_right, hγn]
  have hK20 : ∀ x, K2 x ≠ 0 := by
    intro x hx
    have he : γ x.2 = ((x.1 : ℝ) : ℂ) * h (γ x.2) := sub_eq_zero.1 hx
    have hn := congrArg norm he
    rw [hγn, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg x.1.2.1] at hn
    have hu := x.1.2.2
    have hhn := hh1 (γ x.2) (hγn _).le
    have hu1 : (x.1 : ℝ) = 1 := by nlinarith [norm_nonneg (h (γ x.2)), x.1.2.1]
    rw [hu1, Complex.ofReal_one, one_mul] at he
    exact hhfix _ (hγn _).le he.symm
  obtain ⟨F2, hF2c, hF2l, hF2i⟩ := c02_aux_winding_homotopy K2 hK2c hK20
    (fun u => by simp only [hK2, hγ01])
    (fun t => 2 * π * Complex.I * ((t : ℝ) : ℂ))
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val))
    (fun t => by simp [hK2, hγ])
  have hsame := c02_aux_lift_incr hF1c hF2c (fun t => by
    rw [hF1l, hF2l]; simp [hK1, hK2])
  rw [hF1i, hF2i] at hsame
  simp only [sub_self, Set.Icc.coe_one, Set.Icc.coe_zero, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, mul_zero, sub_zero] at hsame
  have : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  exact this hsame.symm


end GSQG
