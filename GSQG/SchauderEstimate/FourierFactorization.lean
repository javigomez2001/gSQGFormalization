import GSQG.SchauderEstimate.Kernels

/-!
# Beyond the paper (Schauder estimate cited in §4): compact Fourier bridge and block
factorization `Δ_j v = K_{p,j} * |D|^p v` (blueprint ch. 12). Helpers `c12f_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

namespace GSQG

/-- Helper: integrability, weighted integrability and continuity of the transform of a Schwartz function. -/
theorem c12f_aux_fourier_weighted (g : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => fourierT (⇑g) ξ) ∧
    Integrable (fun ξ : ℝ => |ξ| * ‖fourierT (⇑g) ξ‖) ∧ Continuous (fourierT (⇑g)) := by
  have hGf : fourierT (⇑g) = fun ξ => 𝓕 (⇑g) (ξ / (2 * π)) := by
    funext ξ; exact Lib.integral_mul_exp_neg_I_eq_fourier _ ξ
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  refine ⟨(Lib.schwartz_fourier_inversion g).1, ?_, ?_⟩
  · have h1 := ((𝓕 g).integrable_pow_mul volume 1).comp_div h2π
    have h2 := h1.const_mul (2 * π)
    refine h2.congr (Eventually.of_forall fun ξ => ?_)
    simp only [hGf, ← SchwartzMap.fourier_coe, pow_one, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    field_simp
  · rw [hGf, ← SchwartzMap.fourier_coe]
    exact (𝓕 g).continuous.comp (continuous_id.div_const _)

/-- Helper: `|ξ|^p ĝ` is integrable for Schwartz `g`. -/
theorem c12f_aux_mult_integrable {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT (⇑g) ξ) := by
  obtain ⟨hG, hGξ, hGc⟩ := c12f_aux_fourier_weighted g
  have hc : Continuous (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT (⇑g) ξ) :=
    (Complex.continuous_ofReal.comp (continuous_abs.rpow_const fun _ => Or.inr hp.le)).mul hGc
  refine (hG.norm.add hGξ).mono' hc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.add_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : |ξ| ^ p ≤ 1 + |ξ| := by
    rcases le_or_gt |ξ| 1 with h | h
    · have := Real.rpow_le_one (abs_nonneg ξ) h hp.le; linarith [abs_nonneg ξ]
    · have := Real.rpow_le_rpow_of_exponent_le h.le hp1.le; rw [Real.rpow_one] at this; linarith
  nlinarith [norm_nonneg (fourierT (⇑g) ξ)]

/-- Blueprint: lem:c12_compact_fourier_bridge.  For `0 < p < 1` and real `v ∈ C_c^∞`, the
multiplier `m(ξ) = |ξ|^p v̂(ξ)` is integrable (so is `m(ξ) e^{ixξ}` for every `x`), the singular
integral defining `|D|^p v(x)` (the shared `fracD`) converges absolutely, and `|D|^p v(x) = m^∨(x)`. -/
theorem c12_compact_fourier_bridge {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {v : ℝ → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v) :
    Integrable (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT (fun y => (v y : ℂ)) ξ) ∧
    ∀ x : ℝ,
      Integrable (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT (fun y => (v y : ℂ)) ξ *
        Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) ∧
      Integrable (fun z : ℝ => (v x - v z) / |x - z| ^ (p + 1)) ∧
      ((fracD p v x : ℝ) : ℂ) =
        invFourierT (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT (fun y => (v y : ℂ)) ξ) x := by
  have hvC : ContDiff ℝ (⊤ : ℕ∞) (fun y => (v y : ℂ)) := Complex.ofRealCLM.contDiff.comp hv
  have hvcC : HasCompactSupport (fun y => (v y : ℂ)) := hvc.comp_left Complex.ofReal_zero
  set g : SchwartzMap ℝ ℂ := hvcC.toSchwartzMap hvC with hgdef
  have hg : (⇑g : ℝ → ℂ) = fun y => (v y : ℂ) := rfl
  have hm := c12f_aux_mult_integrable hp hp1 g
  rw [hg] at hm
  refine ⟨hm, fun x => ⟨?_, ?_⟩⟩
  · refine hm.norm.mono' (hm.aestronglyMeasurable.mul (by fun_prop))
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul (_ * _), Complex.norm_exp]; simp
  obtain ⟨-, -, -, hKs, -, hKf⟩ := c03c_c03_frac_kernel_formula p hp hp1
  have hb : ∃ M, ∀ y, |v y| ≤ M := by
    obtain ⟨M, hM⟩ := hv.continuous.bounded_above_of_compact_support hvc
    exact ⟨M, fun y => by simpa using hM y⟩
  have hdb : ∃ M, ∀ y, |deriv v y| ≤ M := by
    obtain ⟨M, hM⟩ := (hv.continuous_deriv (by simp)).bounded_above_of_compact_support hvc.deriv
    exact ⟨M, fun y => by simpa using hM y⟩
  obtain ⟨hI, hF⟩ := hKf v (hv.of_le (by simp)) hb hdb x
  refine ⟨?_, ?_⟩
  · have := hI.comp_sub_right x
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [add_sub_cancel, abs_sub_comm z x, add_comm 1 p]
  · have h := hKs g x
    rw [hg] at h
    rw [fourierMultiplier] at h
    rw [h, hF]
    push_cast
    congr 1
    rw [← integral_complex_ofReal]
    push_cast
    rfl

/-- Helper: `|ξ|^p · (φ(2^{-j}ξ)|ξ|^{-p}, zero at `0`) = φ(2^{-j}ξ)`, also at `ξ = 0`. -/
theorem c12f_aux_symbol_mul {p : ℝ} (_hp : 0 < p) (j : ℕ) (ξ : ℝ) :
    ((|ξ| ^ p : ℝ) : ℂ) * ((if ξ = 0 then 0 else c12_annulus (ξ / (2 : ℝ) ^ j) * |ξ| ^ (-p) : ℝ) : ℂ)
      = (c12_annulus (ξ / (2 : ℝ) ^ j) : ℂ) := by
  by_cases hξ : ξ = 0
  · subst hξ; simp [c12_annulus]
  · simp only [hξ, ↓reduceIte]
    rw [← Complex.ofReal_mul]
    congr 1
    have h0 : 0 < |ξ| := abs_pos.mpr hξ
    rw [Real.rpow_neg h0.le, mul_left_comm, mul_inv_cancel₀ (Real.rpow_pos_of_pos h0 p).ne', mul_one]

/-- Blueprint: lem:c12_block_factorization.  For `0 < p < 1`, real `v ∈ C_c^∞`, `h = |D|^p v`
and `j ∈ ℕ`: `Δ_j v(x) = (K_{p,j} * h)(x) = ∫ K_{p,j}(z) h(x - z) dz`; the convolution and the
double integral `∫∫ K_{p,j}(z) |ξ|^p v̂(ξ) e^{i(x-z)ξ} dξ dz` used in the identity converge
absolutely. -/
theorem c12_block_factorization {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {v : ℝ → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v) (j : ℕ) (x : ℝ) :
    Integrable (fun z : ℝ => c12_scaled_kernel p j z * fracD p v (x - z)) ∧
    Integrable (Function.uncurry fun (z ξ : ℝ) => (c12_scaled_kernel p j z : ℂ) *
        (((|ξ| ^ p : ℝ) : ℂ) * fourierT (fun y => (v y : ℂ)) ξ *
          Complex.exp (Complex.I * ((x - z : ℝ) : ℂ) * (ξ : ℂ)))) (volume.prod volume) ∧
    c12_block j v x = ∫ z, c12_scaled_kernel p j z * fracD p v (x - z) := by
  set K := c12_scaled_kernel p j with hKdef
  set m : ℝ → ℂ := fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT (fun y => (v y : ℂ)) ξ with hmdef
  obtain ⟨hm, hbr⟩ := c12_compact_fourier_bridge hp hp1 hv hvc
  obtain ⟨hKc, -, hKF, hKw, -⟩ := c12_kernel_scaling p hp hp1 j
  have hK : Integrable K := by
    have h1 : Integrable (fun z => ‖K z‖) := by
      simpa [Real.rpow_zero, Real.norm_eq_abs] using (hKw 0 0 le_rfl).1
    exact (integrable_norm_iff hKc.continuous.aestronglyMeasurable).1 h1
  -- continuity of `m`
  have hvC : ContDiff ℝ (⊤ : ℕ∞) (fun y => (v y : ℂ)) := Complex.ofRealCLM.contDiff.comp hv
  have hvcC : HasCompactSupport (fun y => (v y : ℂ)) := hvc.comp_left Complex.ofReal_zero
  have hmc : Continuous m := by
    have := (c12f_aux_fourier_weighted (hvcC.toSchwartzMap hvC)).2.2
    exact (Complex.continuous_ofReal.comp (continuous_abs.rpow_const fun _ => Or.inr hp.le)).mul
      this
  set F : ℝ × ℝ → ℂ := Function.uncurry fun (z ξ : ℝ) => (K z : ℂ) *
        (m ξ * Complex.exp (Complex.I * ((x - z : ℝ) : ℂ) * (ξ : ℂ))) with hFdef
  have hFc : Continuous F := by
    simp only [hFdef, Function.uncurry_def]
    have hKc' : Continuous K := hKc.continuous
    fun_prop
  have hF : Integrable F (volume.prod volume) := by
    refine (hK.norm.mul_prod hm.norm).mono' hFc.aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    simp only [hFdef, Function.uncurry_def, norm_mul]
    have : ‖Complex.exp (Complex.I * ((x - q.1 : ℝ) : ℂ) * (q.2 : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, mul_one, Complex.norm_real, hmdef, norm_mul]
  -- the inner `ξ` integral is `2π K(z) h(x-z)`
  have hinner : ∀ z : ℝ, ((K z * fracD p v (x - z) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, F (z, ξ) := by
    intro z
    rw [Complex.ofReal_mul, (hbr (x - z)).2.2, invFourierT]
    simp only [hFdef, Function.uncurry_apply_pair]
    rw [integral_const_mul]; ring
  have hI1 : Integrable (fun z : ℝ => K z * fracD p v (x - z)) := by
    have := (hF.integral_prod_left.const_mul ((2 * π : ℝ) : ℂ)⁻¹).re
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [← hinner z]; simp
  refine ⟨hI1, hF, ?_⟩
  -- swap the order of integration
  have hswap : ∀ ξ : ℝ, ∫ z, F (z, ξ) = m ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) *
      fourierT (fun y => (K y : ℂ)) ξ := by
    intro ξ
    rw [fourierT, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hFdef, Function.uncurry_apply_pair]
    rw [show Complex.I * ((x - z : ℝ) : ℂ) * (ξ : ℂ) = Complex.I * (x : ℂ) * (ξ : ℂ) +
      -(Complex.I * (z : ℂ) * (ξ : ℂ)) by push_cast; ring, Complex.exp_add]
    ring
  have hmain : ((∫ z, K z * fracD p v (x - z) : ℝ) : ℂ) =
      invFourierT (fun ξ => (c12_annulus (ξ / (2 : ℝ) ^ j) : ℂ) *
        fourierT (fun y => (v y : ℂ)) ξ) x := by
    rw [← integral_complex_ofReal]
    simp_rw [hinner]
    rw [integral_const_mul, integral_integral_swap (f := fun z ξ => F (z, ξ)) hF, invFourierT]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [hswap ξ, hKF ξ, hmdef]
    simp only
    rw [← c12f_aux_symbol_mul hp j ξ]
    ring
  rw [c12_block, ← hmain, Complex.ofReal_re]


end GSQG
