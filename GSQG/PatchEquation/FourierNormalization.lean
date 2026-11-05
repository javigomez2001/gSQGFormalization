import GSQG.PatchEquation.CancellationOperator

/-!
# Beyond the paper (2D patch derivation): Gamma layers, Gaussian moment, inverse-Gamma integral, kernel
symbol, Fourier identification (blueprint ch. 13)

Helpers are named `c13k_aux_*`.

Fourier convention (def:c13_normalization): `f̂(ξ) = ∫ f(X) e^{-i X·ξ} dX`, inverse factor
`(2π)^{-2}`. Vector identities are stated componentwise (`j : Fin 2`) after complexification.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

namespace GSQG

theorem c13k_aux_gauss_int {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : c13_E => Real.exp (-b * ‖z‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := c13_E) (b := (b:ℂ))
    (by simpa using hb) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  norm_cast

theorem c13k_aux_norm_gauss_int {s : ℝ} (hs : 0 < s) :
    Integrable (fun z : c13_E => ‖z‖ * Real.exp (-s * ‖z‖ ^ 2)) := by
  refine ((c13k_aux_gauss_int (b := s / 2) (by positivity)).const_mul (1 + 2 / s)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  have hx := norm_nonneg z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e1 : Real.exp (-s * ‖z‖ ^ 2) = Real.exp (-(s/2) * ‖z‖ ^ 2) * Real.exp (-(s/2) * ‖z‖ ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : 1 + (s/2) * ‖z‖^2 ≤ Real.exp ((s/2) * ‖z‖ ^ 2) := by
    have := Real.add_one_le_exp ((s/2) * ‖z‖ ^ 2); linarith
  have e3 : Real.exp (-(s/2) * ‖z‖ ^ 2) * Real.exp ((s/2) * ‖z‖ ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp (-(s/2) * ‖z‖ ^ 2) := Real.exp_pos _
  have h1 : ‖z‖ ≤ (1 + 2/s) * (1 + (s/2) * ‖z‖^2) := by
    have : ‖z‖ ≤ 1 + ‖z‖^2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    have : (1 + 2/s) * (1 + (s/2) * ‖z‖^2) = 1 + ‖z‖^2 + 2/s + (s/2)*‖z‖^2 := by
      field_simp; ring
    nlinarith [sq_nonneg ‖z‖, div_pos two_pos hs]
  rw [e1]
  calc ‖z‖ * (Real.exp (-(s/2) * ‖z‖ ^ 2) * Real.exp (-(s/2) * ‖z‖ ^ 2))
      ≤ ((1 + 2/s) * Real.exp ((s/2) * ‖z‖ ^ 2)) *
          (Real.exp (-(s/2) * ‖z‖ ^ 2) * Real.exp (-(s/2) * ‖z‖ ^ 2)) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = (1 + 2/s) * Real.exp (-(s/2) * ‖z‖ ^ 2) := by
        rw [show ((1 + 2/s) * Real.exp ((s/2) * ‖z‖ ^ 2)) *
          (Real.exp (-(s/2) * ‖z‖ ^ 2) * Real.exp (-(s/2) * ‖z‖ ^ 2)) =
          (1 + 2/s) * Real.exp (-(s/2) * ‖z‖ ^ 2) *
            (Real.exp (-(s/2) * ‖z‖ ^ 2) * Real.exp ((s/2) * ‖z‖ ^ 2)) by ring, e3, mul_one]

theorem c13k_aux_gauss_ft {s : ℝ} (hs : 0 < s) (ξ : c13_E) :
    Integrable (fun z : c13_E =>
      Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ))) ∧
    ∫ z : c13_E, Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)) =
      ((π / s : ℝ) : ℂ) * ((Real.exp (-(‖ξ‖ ^ 2 / (4 * s))) : ℝ) : ℂ) := by
  have hb : 0 < (s:ℂ).re := by simpa using hs
  have hf : (fun z : c13_E => Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ))) =
      fun z => Complex.exp (-(s:ℂ) * ‖z‖ ^ 2 + (-Complex.I) * (inner ℝ ξ z : ℝ)) := by
    funext z; rw [real_inner_comm]; ring_nf
  rw [hf]
  refine ⟨GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb _ _, ?_⟩
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, finrank_euclideanSpace_fin]
  have : ((2:ℕ) / 2 : ℂ) = 1 := by norm_num
  rw [this, Complex.cpow_one]
  push_cast
  congr 2
  ring_nf
  simp [Complex.I_sq]
  ring

theorem c13k_aux_moment {s : ℝ} (hs : 0 < s) (ξ : c13_E) (j : Fin 2) :
      Integrable (fun z : c13_E =>
        (z j : ℂ) * Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ))) ∧
      ∫ z : c13_E, (z j : ℂ) * Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)) =
        -(Complex.I * ((π / (2 * s ^ 2) * ξ j * Real.exp (-(‖ξ‖ ^ 2 / (4 * s))) : ℝ) : ℂ)) := by
  set e : c13_E := EuclideanSpace.single j 1
  have hinn : ∀ (z : c13_E) (t : ℝ), inner ℝ z (ξ + t • e) = inner ℝ z ξ + t * z j := by
    intro z t
    rw [inner_add_right, inner_smul_right]
    simp [e, EuclideanSpace.inner_single_right]
  have hnorm : ∀ t : ℝ, ‖ξ + t • e‖ ^ 2 = ‖ξ‖ ^ 2 + 2 * t * ξ j + t ^ 2 := by
    intro t
    rw [norm_add_sq_real, inner_smul_right, norm_smul]
    simp [e, EuclideanSpace.inner_single_right]
    ring
  let F : ℝ → c13_E → ℂ := fun t z =>
    Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * ((inner ℝ z ξ : ℝ) + t * z j))
  let F' : ℝ → c13_E → ℂ := fun t z => (-Complex.I * (z j : ℂ)) * F t z
  have hFe : ∀ t, F t = fun z : c13_E =>
      Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z (ξ + t • e) : ℝ)) := by
    intro t; funext z
    simp only [F]
    rw [hinn]; push_cast; rfl
  have hG : ∀ t, ∫ z, F t z =
      ((π / s : ℝ) : ℂ) * ((Real.exp (-((‖ξ‖ ^ 2 + 2 * t * ξ j + t ^ 2) / (4 * s))) : ℝ) : ℂ) := by
    intro t
    rw [← hnorm, ← (c13k_aux_gauss_ft hs (ξ + t • e)).2, hFe t]
  have hFint : ∀ t, Integrable (F t) := by
    intro t
    rw [hFe t]; exact (c13k_aux_gauss_ft hs (ξ + t • e)).1
  have hnF : ∀ t z, ‖F t z‖ = Real.exp (-s * ‖z‖ ^ 2) := by
    intro t z
    simp only [F, Complex.norm_exp]
    congr 1
    simp [Complex.sub_re, Complex.mul_re]
    norm_cast
    simp
  have hmeas : ∀ t, AEStronglyMeasurable (F t) volume := fun t => (hFint t).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0:ℝ))
    (F := F) (F' := F') (s := univ) (bound := fun z => ‖z‖ * Real.exp (-s * ‖z‖ ^ 2))
    Filter.univ_mem (Filter.Eventually.of_forall hmeas) (hFint 0)
    (by
      refine AEStronglyMeasurable.mul ?_ (hmeas 0)
      exact (Continuous.aestronglyMeasurable (by fun_prop)))
    (Filter.Eventually.of_forall fun z t _ => by
      simp only [F', norm_mul, hnF, norm_neg, Complex.norm_I, one_mul, Complex.norm_real]
      gcongr
      simpa using PiLp.norm_apply_le z j)
    (c13k_aux_norm_gauss_int hs)
    (Filter.Eventually.of_forall fun z t _ => by
      simp only [F, F']
      have h1 : HasDerivAt (fun t : ℝ => -(s : ℂ) * ‖z‖ ^ 2 - Complex.I * ((inner ℝ z ξ : ℝ) + t * z j))
          (-Complex.I * (z j : ℂ)) t := by
        have := ((hasDerivAt_id (t:ℂ)).mul_const (z j : ℂ)).const_add ((inner ℝ z ξ : ℝ) : ℂ)
          |>.const_mul Complex.I |>.const_sub (-(s : ℂ) * ‖z‖ ^ 2)
        have := this.comp_ofReal (z := t)
        simp only [id] at this
        convert this using 1
        ring
      exact (mul_comm _ _ : _ = (-Complex.I * (z j : ℂ)) * _) ▸ h1.cexp)
  -- closed form derivative
  have hc : HasDerivAt (fun t : ℝ => ((π / s : ℝ) : ℂ) *
      ((Real.exp (-((‖ξ‖ ^ 2 + 2 * t * ξ j + t ^ 2) / (4 * s))) : ℝ) : ℂ))
      (((π / s : ℝ) : ℂ) * ((Real.exp (-(‖ξ‖ ^ 2 / (4 * s))) * (-(2 * ξ j) / (4 * s)) : ℝ) : ℂ)) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => -((‖ξ‖ ^ 2 + 2 * t * ξ j + t ^ 2) / (4 * s)))
        (-(2 * ξ j) / (4 * s)) 0 := by
      have := (((hasDerivAt_id (0:ℝ)).const_mul (2 * ξ j)).const_add (‖ξ‖ ^ 2)).add
        ((hasDerivAt_id (0:ℝ)).pow 2)
      have := (this.div_const (4 * s)).neg
      convert this using 1
      · funext t; simp; ring
      · simp; ring
    have := (h0.exp.ofReal_comp).const_mul ((π / s : ℝ) : ℂ)
    convert this using 2
    simp
  have hfun : (fun t => ∫ z, F t z) = (fun t : ℝ => ((π / s : ℝ) : ℂ) *
      ((Real.exp (-((‖ξ‖ ^ 2 + 2 * t * ξ j + t ^ 2) / (4 * s))) : ℝ) : ℂ)) := funext hG
  rw [hfun] at hd
  have heq := hd.2.unique hc
  have hF0 : ∀ z, F 0 z = Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)) := by
    intro z; simp [F]
  refine ⟨?_, ?_⟩
  · have := hd.1.const_mul Complex.I
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [F', hF0]
    ring_nf; simp [Complex.I_sq]
  · have h2 : ∫ z, F' 0 z = -Complex.I * ∫ z : c13_E, (z j : ℂ) *
        Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)) := by
      rw [← integral_const_mul]; congr 1; funext z; simp only [F', hF0]; ring
    rw [h2] at heq
    have h3 : ∫ z : c13_E, (z j : ℂ) *
        Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)) =
        Complex.I * (-Complex.I * ∫ z : c13_E, (z j : ℂ) *
        Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ))) := by
      rw [← mul_assoc]; simp
    rw [h3, heq]
    push_cast
    field_simp
    ring

theorem c13k_aux_odd {s : ℝ} (hs : 0 < s) (j : Fin 2) :
      Integrable (fun z : c13_E => z j * Real.exp (-s * ‖z‖ ^ 2)) ∧
      ∫ z : c13_E, z j * Real.exp (-s * ‖z‖ ^ 2) = 0 := by
  refine ⟨(c13k_aux_norm_gauss_int hs).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_), ?_⟩
  · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    gcongr
    exact PiLp.norm_apply_le z j
  · have h := integral_neg_eq_self (fun z : c13_E => z j * Real.exp (-s * ‖z‖ ^ 2)) volume
    simp only [PiLp.neg_apply, norm_neg, neg_mul, integral_neg] at h ⊢
    linarith

theorem c13k_aux_layer {a : ℝ} (ha : 0 < a) {z : c13_E} (hz : z ≠ 0) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1) * Real.exp (-s * ‖z‖ ^ 2)) (Ioi 0) ∧
    ∫ s in Ioi (0 : ℝ), s ^ (a - 1) * Real.exp (-s * ‖z‖ ^ 2) = ‖z‖ ^ (-(2 * a)) * Real.Gamma a := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hr : 0 < ‖z‖ ^ 2 := by positivity
  have hfe : (fun s : ℝ => s ^ (a - 1) * Real.exp (-s * ‖z‖ ^ 2)) =
      fun s => s ^ (a - 1) * Real.exp (-(‖z‖ ^ 2 * s)) := by
    funext s; ring_nf
  rw [hfe]
  refine ⟨?_, ?_⟩
  · have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := ‖z‖ ^ 2)
      (by linarith) one_pos hr
    simpa [Real.rpow_one, neg_mul] using this
  · rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr, one_div, Real.inv_rpow hr.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hn.le, Real.rpow_neg hn.le]
    norm_num

theorem c13k_aux_double_gen {a : ℝ} (ha : 0 < a) (C : c13_E → ℂ) (hCc : Continuous C)
    (hC0 : C 0 = 0) (hi : Integrable (fun z : c13_E => ‖z‖ ^ (-(2 * a)) * ‖C z‖)) :
    Integrable (fun p : ℝ × c13_E =>
        ((p.1 ^ (a - 1) * Real.exp (-p.1 * ‖p.2‖ ^ 2) : ℝ) : ℂ) * C p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure c13_E)) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × c13_E =>
      ((p.1 ^ (a - 1) * Real.exp (-p.1 * ‖p.2‖ ^ 2) : ℝ) : ℂ) * C p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure c13_E)) := by
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul ?_ (hCc.measurable.comp measurable_snd)
    refine Complex.measurable_ofReal.comp ?_
    fun_prop
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
  · by_cases hz : z = 0
    · subst hz; simp [hC0]
    · have h1 : Integrable (fun s : ℝ => ((s ^ (a - 1) * Real.exp (-s * ‖z‖ ^ 2) : ℝ) : ℂ))
          (volume.restrict (Ioi 0)) := (c13k_aux_layer ha hz).1.ofReal
      exact h1.mul_const (C z)
  · refine (hi.const_mul (Real.Gamma a)).congr (Eventually.of_forall fun z => ?_)
    simp only
    by_cases hz : z = 0
    · subst hz; simp [hC0]
    · have hnn : ∀ s ∈ Ioi (0:ℝ), ‖((s ^ (a - 1) * Real.exp (-s * ‖z‖ ^ 2) : ℝ) : ℂ) * C z‖ =
          (s ^ (a - 1) * Real.exp (-s * ‖z‖ ^ 2)) * ‖C z‖ := by
        intro s hs
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
        have : (0:ℝ) < s := hs
        positivity
      rw [setIntegral_congr_fun measurableSet_Ioi hnn, integral_mul_const, (c13k_aux_layer ha hz).2]
      ring

theorem c13k_aux_rot_cont (j : Fin 2) : Continuous fun z : c13_E => c13_rotation z j := by
  unfold c13_rotation; fin_cases j <;> simp <;> fun_prop

theorem c13k_aux_norm_rot (z : c13_E) : ‖c13_rotation z‖ = ‖z‖ := by
  simp only [c13_rotation, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [add_comm]

theorem c13k_aux_kernel_norm {α c : ℝ} (z : c13_E) :
    ‖c13_velocity_kernel α c z‖ = |α * c| * ‖z‖ ^ (-α - 2) * ‖z‖ := by
  unfold c13_velocity_kernel
  split_ifs with hz
  · subst hz; simp
  · rw [norm_smul, c13k_aux_norm_rot, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem c13k_aux_double {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (ξ : c13_E) (j : Fin 2) :
      Integrable (fun p : ℝ × c13_E =>
        ((p.1 ^ (α / 2) * Real.exp (-p.1 * ‖p.2‖ ^ 2) * c13_rotation p.2 j : ℝ) : ℂ) *
          (Complex.exp (-Complex.I * (inner ℝ p.2 ξ : ℝ)) - 1))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure c13_E)) := by
  have ha : 0 < α / 2 + 1 := by linarith
  have hCc : Continuous fun z : c13_E =>
      (c13_rotation z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1) := by
    have h1 : Continuous fun z : c13_E => (inner ℝ z ξ : ℝ) := continuous_id.inner continuous_const
    exact (Complex.continuous_ofReal.comp (c13k_aux_rot_cont j)).mul
      ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp h1))).sub
        continuous_const)
  have hC0 : (fun z : c13_E =>
      (c13_rotation z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1)) 0 = 0 := by
    simp [c13_rotation]
  obtain ⟨K0, -, hK⟩ := (c13_radial_majorants hα1 hα2 1).2.2.2.2
  have hint := (hK ξ).1
  simp only [← neg_mul] at hint
  have hi : Integrable (fun z : c13_E => ‖z‖ ^ (-(2 * (α / 2 + 1))) *
      ‖(c13_rotation z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1)‖) := by
    refine (hint.const_mul (1 / α)).mono' ?_ (Eventually.of_forall fun z => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact (by fun_prop : Measurable fun z : c13_E => ‖z‖ ^ (-(2 * (α / 2 + 1)))).mul
        hCc.norm.measurable
    · rw [Real.norm_of_nonneg (by positivity), c13k_aux_kernel_norm, norm_mul, Complex.norm_real]
      have e1 : -(2 * (α / 2 + 1)) = -α - 2 := by ring
      rw [e1]
      have hj : ‖c13_rotation z j‖ ≤ ‖z‖ := by
        rw [← c13k_aux_norm_rot z]; exact PiLp.norm_apply_le _ j
      have hα0 : 0 < α := by linarith
      rw [mul_one, abs_of_pos hα0]
      calc ‖z‖ ^ (-α - 2) * (‖c13_rotation z j‖ *
            ‖Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1‖)
          ≤ ‖z‖ ^ (-α - 2) * (‖z‖ * ‖Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1‖) := by
            gcongr
        _ = 1 / α * (α * ‖z‖ ^ (-α - 2) * ‖z‖ *
            ‖Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1‖) := by
            field_simp
  have := c13k_aux_double_gen ha _ hCc hC0 hi
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp only [add_sub_cancel_right]
  push_cast; ring

/-- Blueprint: lem:c13_gamma_kernel_layers.  Gamma-layer representations of `|z|^{-α}` and of
`K_{α,c}(z)` for `z ≠ 0`, with absolutely convergent scalar parameter integrals, and absolute
integrability of the layered double integrand `(s,z) ↦ s^{α/2} e^{-s|z|²} (e^{-iz·ξ} - 1) (Jz)_j`
on `(0,∞) × E`. -/
theorem c13_gamma_kernel_layers {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    (∀ z : c13_E, z ≠ 0 →
      IntegrableOn (fun s : ℝ => s ^ (α / 2 - 1) * Real.exp (-s * ‖z‖ ^ 2)) (Ioi 0) ∧
      ‖z‖ ^ (-α) = (Real.Gamma (α / 2))⁻¹ *
        ∫ s in Ioi (0 : ℝ), s ^ (α / 2 - 1) * Real.exp (-s * ‖z‖ ^ 2) ∧
      IntegrableOn (fun s : ℝ => s ^ (α / 2) * Real.exp (-s * ‖z‖ ^ 2)) (Ioi 0) ∧
      c13_velocity_kernel α c z =
        (2 * c / Real.Gamma (α / 2) *
          ∫ s in Ioi (0 : ℝ), s ^ (α / 2) * Real.exp (-s * ‖z‖ ^ 2)) • c13_rotation z) ∧
    (∀ (ξ : c13_E) (j : Fin 2),
      Integrable (fun p : ℝ × c13_E =>
        ((p.1 ^ (α / 2) * Real.exp (-p.1 * ‖p.2‖ ^ 2) * c13_rotation p.2 j : ℝ) : ℂ) *
          (Complex.exp (-Complex.I * (inner ℝ p.2 ξ : ℝ)) - 1))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure c13_E))) := by
  refine ⟨fun z hz => ?_, c13k_aux_double hα1 hα2⟩
  have ha : 0 < α / 2 := by linarith
  have hb : 0 < α / 2 + 1 := by linarith
  have hG := Real.Gamma_pos_of_pos ha
  obtain ⟨i1, v1⟩ := c13k_aux_layer ha hz
  obtain ⟨i2, v2⟩ := c13k_aux_layer hb hz
  simp only [add_sub_cancel_right] at i2 v2
  refine ⟨i1, ?_, i2, ?_⟩
  · rw [v1, show -(2 * (α / 2)) = -α by ring]; field_simp
  · rw [v2, Real.Gamma_add_one ha.ne', show -(2 * (α / 2 + 1)) = -α - 2 by ring]
    unfold c13_velocity_kernel
    simp only [hz, ↓reduceIte]
    congr 1
    field_simp

/-- Blueprint: lem:c13_gaussian_first_moment.  For `s > 0` and `ξ ∈ E`: the 2D Gaussian
transform, its first moment (componentwise), and the vanishing of the unmodulated first moment,
all absolutely convergent. -/
theorem c13_gaussian_first_moment {s : ℝ} (hs : 0 < s) (ξ : c13_E) :
    Integrable (fun z : c13_E =>
      Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ))) ∧
    ∫ z : c13_E, Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)) =
      ((π / s : ℝ) : ℂ) * ((Real.exp (-(‖ξ‖ ^ 2 / (4 * s))) : ℝ) : ℂ) ∧
    (∀ j : Fin 2,
      Integrable (fun z : c13_E =>
        (z j : ℂ) * Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ))) ∧
      ∫ z : c13_E, (z j : ℂ) * Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)) =
        -(Complex.I * ((π / (2 * s ^ 2) * ξ j * Real.exp (-(‖ξ‖ ^ 2 / (4 * s))) : ℝ) : ℂ))) ∧
    (∀ j : Fin 2,
      Integrable (fun z : c13_E => z j * Real.exp (-s * ‖z‖ ^ 2)) ∧
      ∫ z : c13_E, z j * Real.exp (-s * ‖z‖ ^ 2) = 0) := by
  exact ⟨(c13k_aux_gauss_ft hs ξ).1, (c13k_aux_gauss_ft hs ξ).2, c13k_aux_moment hs ξ,
    fun j => c13k_aux_odd hs j⟩

/-- Blueprint: lem:c13_inverse_gamma_integral.  `∫₀^∞ s^{-1-a} e^{-b/s} ds = b^{-a} Γ(a)`. -/
theorem c13_inverse_gamma_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s ^ (-1 - a) * Real.exp (-b / s)) (Ioi 0) ∧
    ∫ s in Ioi (0 : ℝ), s ^ (-1 - a) * Real.exp (-b / s) = b ^ (-a) * Real.Gamma a := by
  set g : ℝ → ℝ := fun y => y ^ (a - 1) * Real.exp (-(b * y)) with hg
  have key : ∀ x ∈ Ioi (0:ℝ), (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) • g (x ^ (-1:ℝ)) =
      x ^ (-1 - a) * Real.exp (-b / x) := by
    intro x hx
    have hx : 0 < x := hx
    simp only [hg, smul_eq_mul, abs_neg, abs_one, one_mul]
    rw [← Real.rpow_mul hx.le, Real.rpow_neg_one, ← mul_assoc, ← Real.rpow_add hx]
    congr 2
    · ring
    · field_simp
  have hgi : IntegrableOn g (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := b)
      (by linarith) one_pos hb
    simpa [hg, neg_mul] using this
  constructor
  · rw [← integrableOn_Ioi_comp_rpow_iff g (p := -1) (by norm_num)] at hgi
    exact hgi.congr_fun key measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi key, integral_comp_rpow_Ioi g (by norm_num),
      hg, Real.integral_rpow_mul_exp_neg_mul_Ioi ha hb, one_div, Real.inv_rpow hb.le,
      Real.rpow_neg hb.le]

theorem c13k_aux_gauss_split (s : ℝ) (z : c13_E) (x : ℝ) :
    ((Real.exp (-s * ‖z‖ ^ 2) : ℝ) : ℂ) * Complex.exp (-Complex.I * (x : ℂ)) =
      Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (x : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem c13k_aux_inner_z {s : ℝ} (hs : 0 < s) (a : ℝ) (ξ : c13_E) (j : Fin 2) :
    ∫ z : c13_E, ((s ^ a * Real.exp (-s * ‖z‖ ^ 2) * c13_rotation z j : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1) =
      -Complex.I * ((s ^ a * (π / (2 * s ^ 2)) * c13_rotation ξ j *
        Real.exp (-(‖ξ‖ ^ 2 / (4 * s))) : ℝ) : ℂ) := by
  -- (J z)_j = σ * z k
  obtain ⟨k, σ, hσ⟩ : ∃ k : Fin 2, ∃ σ : ℝ, ∀ w : c13_E, c13_rotation w j = σ * w k := by
    fin_cases j
    · exact ⟨1, -1, fun w => by simp [c13_rotation]⟩
    · exact ⟨0, 1, fun w => by simp [c13_rotation]⟩
  obtain ⟨hm1, hm2⟩ := c13k_aux_moment hs ξ k
  obtain ⟨ho1, ho2⟩ := c13k_aux_odd hs k
  have hpt : ∀ z : c13_E, ((s ^ a * Real.exp (-s * ‖z‖ ^ 2) * c13_rotation z j : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1) =
      ((s ^ a * σ : ℝ) : ℂ) * ((z k : ℂ) * Complex.exp (-(s : ℂ) * ‖z‖ ^ 2 - Complex.I * (inner ℝ z ξ : ℝ)))
        - ((s ^ a * σ : ℝ) : ℂ) * (((z k * Real.exp (-s * ‖z‖ ^ 2)) : ℝ) : ℂ) := by
    intro z
    rw [← c13k_aux_gauss_split, hσ]
    push_cast; ring
  have hsub := integral_sub (hm1.const_mul ((s ^ a * σ : ℝ) : ℂ))
    ((ho1.ofReal (𝕜 := ℂ)).const_mul ((s ^ a * σ : ℝ) : ℂ))
  refine (integral_congr_ae (Eventually.of_forall hpt)).trans (hsub.trans ?_)
  rw [integral_const_mul, integral_const_mul, integral_ofReal, ho2, hm2, hσ]
  push_cast; ring

theorem c13k_aux_kernel_meas (α c : ℝ) : Measurable (c13_velocity_kernel α c) := by
  have h : Measurable fun z : c13_E => (α * c * ‖z‖ ^ (-α - 2)) • c13_rotation z := by
    have : Continuous c13_rotation := by
      unfold c13_rotation
      exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop)
    exact (by fun_prop : Measurable fun z : c13_E => α * c * ‖z‖ ^ (-α - 2)).smul this.measurable
  unfold c13_velocity_kernel
  exact Measurable.ite (measurableSet_singleton 0) measurable_const h

theorem c13k_aux_symbol_int {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (ξ : c13_E) (j : Fin 2) :
    Integrable (fun z : c13_E =>
      (c13_velocity_kernel α c z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1)) := by
  obtain ⟨K0, -, hK⟩ := (c13_radial_majorants hα1 hα2 c).2.2.2.2
  have hint := (hK ξ).1
  simp only [← neg_mul] at hint
  refine hint.mono' ?_ (Eventually.of_forall fun z => ?_)
  · have h1 : Continuous fun z : c13_E => (inner ℝ z ξ : ℝ) := continuous_id.inner continuous_const
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · exact Complex.measurable_ofReal.comp
        ((PiLp.continuous_apply 2 _ j).measurable.comp (c13k_aux_kernel_meas α c))
    · exact ((Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp h1))).sub continuous_const).measurable
  · rw [norm_mul, Complex.norm_real]
    gcongr
    exact PiLp.norm_apply_le _ j

theorem c13k_aux_four_rpow {ξ : c13_E} (hξ : ξ ≠ 0) (α : ℝ) :
    (‖ξ‖ ^ 2 / 4) ^ (-(1 - α / 2)) = (2 : ℝ) ^ (2 - α) * ‖ξ‖ ^ (α - 2) := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [Real.div_rpow (by positivity) (by norm_num), show (4:ℝ) = 2 ^ (2:ℝ) by norm_num,
    ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  push_cast
  rw [mul_comm]
  congr 2 <;> ring

/-- Blueprint: lem:c13_kernel_symbol.  For every `ξ`, componentwise,
`∫ K_{α,c}(z) (e^{-iz·ξ} - 1) dz = -i c A_α (Jξ) |ξ|^{α-2}` (absolutely convergent; the right
side is zero at `ξ = 0` since `J0 = 0`), and `A_α, c_std, κ_α > 0`. -/
theorem c13_kernel_symbol {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    (∀ (ξ : c13_E) (j : Fin 2),
      Integrable (fun z : c13_E =>
        (c13_velocity_kernel α c z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1)) ∧
      ∫ z : c13_E,
          (c13_velocity_kernel α c z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1) =
        -Complex.I * ((c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2) : ℝ) : ℂ)) ∧
    0 < c13_riesz_factor α ∧ 0 < c13_standard_coefficient α ∧ 0 < c13_time_ratio α := by
  have ha : 0 < α / 2 := by linarith
  have ha' : 0 < 1 - α / 2 := by linarith
  have hG := Real.Gamma_pos_of_pos ha
  have hG' := Real.Gamma_pos_of_pos ha'
  have hA : 0 < c13_riesz_factor α := by unfold c13_riesz_factor; positivity
  refine ⟨fun ξ j => ⟨c13k_aux_symbol_int hα1 hα2 ξ j, ?_⟩, hA, ?_, ?_⟩
  rotate_left
  · unfold c13_standard_coefficient; positivity
  · unfold c13_time_ratio c13_standard_coefficient calpha
    have hp : 0 < α - 1 := by linarith
    have hs : 0 < Real.sin (π * (α - 1) / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · nlinarith [Real.pi_pos]
    have := Real.Gamma_pos_of_pos (by linarith : (0:ℝ) < 1 + (α - 1))
    positivity
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 : c13_rotation (0:c13_E) j = 0 := by fin_cases j <;> simp [c13_rotation]
    simp [h0]
  -- Gamma layers
  have hL := (c13_gamma_kernel_layers (c := c) hα1 hα2)
  set g : ℝ × c13_E → ℂ := fun p =>
    ((p.1 ^ (α / 2) * Real.exp (-p.1 * ‖p.2‖ ^ 2) * c13_rotation p.2 j : ℝ) : ℂ) *
      (Complex.exp (-Complex.I * (inner ℝ p.2 ξ : ℝ)) - 1) with hg
  have hgi : Integrable g ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure c13_E)) :=
    hL.2 ξ j
  have hpt : ∀ z : c13_E,
      (c13_velocity_kernel α c z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1) =
        ((2 * c / Real.Gamma (α / 2) : ℝ) : ℂ) * ∫ s in Ioi (0:ℝ), g (s, z) := by
    intro z
    by_cases hz : z = 0
    · subst hz; simp [hg, c13_velocity_kernel, c13_rotation]
    · rw [(hL.1 z hz).2.2.2]
      have : ∫ s in Ioi (0:ℝ), g (s, z) =
          ((∫ s in Ioi (0 : ℝ), s ^ (α / 2) * Real.exp (-s * ‖z‖ ^ 2) : ℝ) : ℂ) *
            ((c13_rotation z j : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1)) := by
        rw [← integral_complex_ofReal, ← integral_mul_const]
        congr 1; funext s; simp only [hg]; push_cast; ring
      rw [this]
      simp only [PiLp.smul_apply, smul_eq_mul]
      push_cast; ring
  have hinner : ∀ s ∈ Ioi (0:ℝ), ∫ z, g (s, z) =
      ((-Complex.I * ((π / 2 * c13_rotation ξ j) : ℝ)) : ℂ) *
        ((s ^ (-1 - (1 - α / 2)) * Real.exp (-(‖ξ‖ ^ 2 / 4) / s) : ℝ) : ℂ) := by
    intro s hs
    have hs' : (0:ℝ) < s := hs
    simp only [hg]
    rw [c13k_aux_inner_z hs' (α / 2) ξ j]
    have e1 : s ^ (α / 2) * (π / (2 * s ^ 2)) =
        π / 2 * s ^ (-1 - (1 - α / 2)) := by
      rw [show (-1 - (1 - α / 2)) = α / 2 - 2 by ring, Real.rpow_sub hs', Real.rpow_two]
      field_simp
    have e2 : -(‖ξ‖ ^ 2 / (4 * s)) = -(‖ξ‖ ^ 2 / 4) / s := by
      field_simp
    rw [e2]
    rw [show s ^ (α / 2) * (π / (2 * s ^ 2)) * c13_rotation ξ j *
        Real.exp (-(‖ξ‖ ^ 2 / 4) / s) =
        (s ^ (α / 2) * (π / (2 * s ^ 2))) * c13_rotation ξ j *
        Real.exp (-(‖ξ‖ ^ 2 / 4) / s) by ring, e1]
    push_cast; ring
  have hb : 0 < ‖ξ‖ ^ 2 / 4 := by have := norm_pos_iff.2 hξ; positivity
  obtain ⟨-, hIG⟩ := c13_inverse_gamma_integral ha' hb
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    ← integral_integral_swap hgi, setIntegral_congr_fun measurableSet_Ioi hinner,
    integral_const_mul, integral_complex_ofReal, hIG, c13k_aux_four_rpow hξ]
  unfold c13_riesz_factor
  push_cast
  field_simp

theorem c13k_aux_schwartz_bounds (f : SchwartzMap c13_E ℝ) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ (∀ x, |f x| ≤ C0) ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ C1) ∧
      (∀ x y, |f x - f y| ≤ C1 * ‖x - y‖) := by
  set g := SchwartzMap.fderivCLM ℝ c13_E ℝ f
  refine ⟨SchwartzMap.seminorm ℝ 0 0 f, SchwartzMap.seminorm ℝ 0 0 g, by positivity,
    by positivity, fun x => ?_, fun x => ?_, fun x y => ?_⟩
  · simpa using SchwartzMap.norm_le_seminorm ℝ f x
  · have := SchwartzMap.norm_le_seminorm ℝ g x
    simpa [g, SchwartzMap.fderivCLM_apply] using this
  · have hb : ∀ x ∈ (univ : Set c13_E), ‖fderiv ℝ f x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
      intro x _
      have := SchwartzMap.norm_le_seminorm ℝ g x
      simpa [g, SchwartzMap.fderivCLM_apply] using this
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => f.differentiableAt) hb (mem_univ y) (mem_univ x)
    simpa [Real.norm_eq_abs] using this

theorem c13k_aux_translation_pointwise (f : c13_E → ℝ) (hf : ContDiff ℝ 1 f) (Y w : c13_E) :
    |f (Y + w) - f Y| ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ f (Y + t • w)‖ * ‖w‖ := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (Y + t • w)) (fderiv ℝ f (Y + t • w) w) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Y + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add Y
    exact ((hf.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous (fun t : ℝ => fderiv ℝ f (Y + t • w) w) := by
    have := hf.continuous_fderiv one_ne_zero
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at hftc
  rw [← Real.norm_eq_abs, ← hftc]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall fun t _ => (fderiv ℝ f (Y + t • w)).le_opNorm w) ?_
  have := hf.continuous_fderiv one_ne_zero
  exact (by fun_prop : Continuous fun t : ℝ => ‖fderiv ℝ f (Y + t • w)‖ * ‖w‖).intervalIntegrable 0 1

theorem c13k_aux_translation_lintegral (f : c13_E → ℝ) (hf : ContDiff ℝ 1 f) (w : c13_E) :
    ∫⁻ Y, ENNReal.ofReal |f (Y + w) - f Y| ≤ ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ f Y‖ * ‖w‖) := by
  have hc := hf.continuous_fderiv one_ne_zero
  have step1 : ∀ Y, ENNReal.ofReal |f (Y + w) - f Y| ≤
      ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (‖fderiv ℝ f (Y + t • w)‖ * ‖w‖) := by
    intro Y
    refine (ENNReal.ofReal_le_ofReal (c13k_aux_translation_pointwise f hf Y w)).trans_eq ?_
    rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal]
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    · exact Eventually.of_forall fun t => by positivity
  calc ∫⁻ Y, ENNReal.ofReal |f (Y + w) - f Y|
      ≤ ∫⁻ Y, ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (‖fderiv ℝ f (Y + t • w)‖ * ‖w‖) :=
        lintegral_mono step1
    _ = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ f (Y + t • w)‖ * ‖w‖) := by
        apply lintegral_lintegral_swap
        apply Measurable.aemeasurable
        apply ENNReal.measurable_ofReal.comp
        apply Continuous.measurable
        change Continuous fun p : c13_E × ℝ => ‖fderiv ℝ f (p.1 + p.2 • w)‖ * ‖w‖
        fun_prop
    _ = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ f Y‖ * ‖w‖) := by
        congr 1; ext t
        exact lintegral_add_right_eq_self (fun Y => ENNReal.ofReal (‖fderiv ℝ f Y‖ * ‖w‖)) (t • w)
    _ = ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ f Y‖ * ‖w‖) := by
        rw [setLIntegral_const, Real.volume_Ioc]; simp

/-- L¹ translation estimate for a real Schwartz function. -/
theorem c13k_aux_schwartz_translation (f : SchwartzMap c13_E ℝ) (z : c13_E) :
    Integrable (fun X => |f (X - z) - f X|) ∧
    (∫ X, |f (X - z) - f X|) ≤ min (‖z‖ * ∫ X, ‖fderiv ℝ f X‖) (2 * ∫ X, |f X|) := by
  have hf1 : ContDiff ℝ 1 f := f.smooth 1
  have iF : Integrable (fun X => f X) := f.integrable
  have iD : Integrable (fun X => ‖fderiv ℝ f X‖) := by
    have := (SchwartzMap.fderivCLM ℝ c13_E ℝ f).integrable (μ := volume)
    simpa [SchwartzMap.fderivCLM_apply] using this.norm
  have iT : Integrable (fun X => f (X - z)) := iF.comp_sub_right z
  have iS : Integrable (fun X => f (X - z) - f X) := iT.sub iF
  refine ⟨iS.abs, le_min ?_ ?_⟩
  · have hl := c13k_aux_translation_lintegral f hf1 (-z)
    simp only [← sub_eq_add_neg, norm_neg] at hl
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => abs_nonneg _)
        iS.abs.aestronglyMeasurable, ← integral_const_mul,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
        (iD.const_mul _).aestronglyMeasurable]
    refine ENNReal.toReal_mono ?_ ?_
    · exact (iD.const_mul ‖z‖).lintegral_lt_top.ne
    · simpa [mul_comm] using hl
  · calc (∫ X, |f (X - z) - f X|) ≤ ∫ X, (|f (X - z)| + |f X|) :=
          integral_mono iS.abs (iT.abs.add iF.abs) fun X => abs_sub _ _
      _ = 2 * ∫ X, |f X| := by
          rw [integral_add iT.abs iF.abs, integral_sub_right_eq_self (fun X => |f X|) z]; ring
theorem c13k_aux_kernel_norm' {α c : ℝ} (z : c13_E) (hz : z ≠ 0) :
    ‖c13_velocity_kernel α c z‖ = |α * c| * ‖z‖ ^ (-α - 1) := by
  have hr : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  rw [c13k_aux_kernel_norm, mul_assoc, ← Real.rpow_add_one hr]
  ring_nf

theorem c13k_aux_major {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    Integrable (fun z : c13_E => ‖c13_velocity_kernel α c z‖ * min (A * ‖z‖) B) := by
  have hR := c13_radial_majorants hα1 hα2 c
  have i1 := (hR.2.2.1 1 one_pos).1
  have i2 := (hR.2.2.2.1 (1/2) (by norm_num)).1
  have hs1 : MeasurableSet (Metric.ball (0 : c13_E) 1) := measurableSet_ball
  have hs2 : MeasurableSet {z : c13_E | 1/2 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hg := ((i1.integrable_indicator hs1).const_mul (|α * c| * A)).add
    ((i2.integrable_indicator hs2).const_mul (|α * c| * B))
  refine hg.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((measurable_norm.comp (c13k_aux_kernel_meas α c)).mul
      ((measurable_const.mul measurable_norm).min measurable_const)).aestronglyMeasurable
  · have hI1 : 0 ≤ (Metric.ball (0 : c13_E) 1).indicator (fun z => ‖z‖ ^ (-α)) z :=
      indicator_nonneg (fun _ _ => by positivity) _
    have hI2 : 0 ≤ {z : c13_E | 1/2 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-α - 1)) z :=
      indicator_nonneg (fun _ _ => by positivity) _
    have hab := abs_nonneg (α * c)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hz : z = 0
    · have h0 : c13_velocity_kernel α c z = 0 := by simp [c13_velocity_kernel, hz]
      rw [h0, norm_zero, zero_mul]
      exact add_nonneg (mul_nonneg (mul_nonneg hab hA) hI1) (mul_nonneg (mul_nonneg hab hB) hI2)
    have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [c13k_aux_kernel_norm' z hz]
    by_cases h1 : ‖z‖ < 1
    · have hm : z ∈ Metric.ball (0 : c13_E) 1 := by simpa using h1
      rw [indicator_of_mem hm]
      have : ‖z‖ ^ (-α - 1) * ‖z‖ = ‖z‖ ^ (-α) := by
        rw [← Real.rpow_add_one hr.ne']; ring_nf
      calc |α * c| * ‖z‖ ^ (-α - 1) * min (A * ‖z‖) B
          ≤ |α * c| * ‖z‖ ^ (-α - 1) * (A * ‖z‖) := by gcongr; exact min_le_left _ _
        _ = |α * c| * A * ‖z‖ ^ (-α) := by rw [← this]; ring
        _ ≤ _ := by
          have := mul_nonneg (mul_nonneg hab hB) hI2
          linarith
    · have hm : z ∈ {z : c13_E | 1/2 < ‖z‖} := by show (1:ℝ)/2 < ‖z‖; linarith
      rw [indicator_of_mem hm]
      calc |α * c| * ‖z‖ ^ (-α - 1) * min (A * ‖z‖) B
          ≤ |α * c| * ‖z‖ ^ (-α - 1) * B := by gcongr; exact min_le_right _ _
        _ = |α * c| * B * ‖z‖ ^ (-α - 1) := by ring
        _ ≤ _ := by
          have := mul_nonneg (mul_nonneg hab hA) hI1
          linarith
theorem c13k_aux_F_meas (α c : ℝ) (f : SchwartzMap c13_E ℝ) :
    Measurable (fun p : c13_E × c13_E => (f (p.1 - p.2) - f p.1) • c13_velocity_kernel α c p.2) :=
  ((f.continuous.comp (continuous_fst.sub continuous_snd)).sub
    (f.continuous.comp continuous_fst)).measurable.smul ((c13k_aux_kernel_meas α c).comp measurable_snd)

theorem c13k_aux_joint {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (f : SchwartzMap c13_E ℝ) :
    Integrable (fun p : c13_E × c13_E => (f (p.1 - p.2) - f p.1) • c13_velocity_kernel α c p.2)
      (volume.prod volume) := by
  have hm := c13k_aux_F_meas α c f
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
  · have h : Integrable (fun X : c13_E => (f (X - z) - f X) • c13_velocity_kernel α c z) volume :=
      (((f.integrable (μ := volume)).comp_sub_right z).sub
        (f.integrable (μ := volume))).smul_const (c13_velocity_kernel α c z)
    exact h
  · have D0 : 0 ≤ ∫ X, |f X| := integral_nonneg fun _ => abs_nonneg _
    have D1 : 0 ≤ ∫ X, ‖fderiv ℝ f X‖ := integral_nonneg fun _ => norm_nonneg _
    refine (c13k_aux_major hα1 hα2 c D1 (by positivity : (0:ℝ) ≤ 2 * ∫ X, |f X|)).mono'
      hm.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    simp only [norm_smul, Real.norm_eq_abs]
    rw [integral_mul_const, abs_of_nonneg (by positivity), mul_comm]
    gcongr
    obtain ⟨-, h⟩ := c13k_aux_schwartz_translation f z
    simpa [mul_comm] using h

theorem c13k_aux_B_basic {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (f : SchwartzMap c13_E ℝ) :
    (∀ X : c13_E, Integrable (fun z : c13_E => (f (X - z) - f X) • c13_velocity_kernel α c z)) ∧
    Continuous (fun X : c13_E => ∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) ∧
    Integrable (fun X : c13_E => ∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) := by
  obtain ⟨C0, C1, hC0, hC1, hb0, -, hL⟩ := c13k_aux_schwartz_bounds f
  have hmaj := c13k_aux_major hα1 hα2 c hC1 (by positivity : (0:ℝ) ≤ 2 * C0)
  have hpt : ∀ X z, ‖(f (X - z) - f X) • c13_velocity_kernel α c z‖ ≤
      ‖c13_velocity_kernel α c z‖ * min (C1 * ‖z‖) (2 * C0) := by
    intro X z
    rw [norm_smul, mul_comm, Real.norm_eq_abs]
    gcongr
    refine le_min ?_ ?_
    · simpa using hL (X - z) X
    · calc |f (X - z) - f X| ≤ |f (X - z)| + |f X| := abs_sub _ _
        _ ≤ 2 * C0 := by linarith [hb0 (X - z), hb0 X]
  have hmeasX : ∀ X, AEStronglyMeasurable
      (fun z : c13_E => (f (X - z) - f X) • c13_velocity_kernel α c z) volume := fun X =>
    (((f.continuous.comp (continuous_const.sub continuous_id)).sub continuous_const).measurable.smul
      (c13k_aux_kernel_meas α c)).aestronglyMeasurable
  refine ⟨fun X => hmaj.mono' (hmeasX X) (Eventually.of_forall (hpt X)), ?_, ?_⟩
  · refine continuous_of_dominated hmeasX (fun X => Eventually.of_forall (hpt X)) hmaj
      (Eventually.of_forall fun z => ?_)
    exact ((f.continuous.comp (continuous_id.sub continuous_const)).sub f.continuous).smul
      continuous_const
  · exact (c13k_aux_joint hα1 hα2 c f).integral_prod_left

theorem c13k_aux_phase_cont (ξ : c13_E) :
    Continuous fun X : c13_E => Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) := by
  have h1 : Continuous fun z : c13_E => (inner ℝ z ξ : ℝ) := continuous_id.inner continuous_const
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp h1))

theorem c13k_aux_phase_norm (X ξ : c13_E) : ‖Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem c13k_aux_phase_add (X Y ξ : c13_E) :
    Complex.exp (-Complex.I * (inner ℝ (X + Y) ξ : ℝ)) =
      Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * Complex.exp (-Complex.I * (inner ℝ Y ξ : ℝ)) := by
  rw [← Complex.exp_add, inner_add_left]; push_cast; ring_nf

theorem c13k_aux_hat_int (f : SchwartzMap c13_E ℝ) (ξ : c13_E) (z : c13_E) :
    Integrable (fun X : c13_E => Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f (X - z) : ℂ)) := by
  have hi := ((f.integrable (μ := volume)).comp_sub_right z).norm
  refine hi.mono' ?_ (Eventually.of_forall fun X => ?_)
  · exact ((c13k_aux_phase_cont ξ).mul (Complex.continuous_ofReal.comp
      (f.continuous.comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
  · rw [norm_mul, c13k_aux_phase_norm, one_mul, Complex.norm_real]

theorem c13k_aux_hat_shift (f : SchwartzMap c13_E ℝ) (ξ z : c13_E) :
    ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f (X - z) : ℂ) =
      Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) *
        ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ) := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure c13_E))
    (fun X : c13_E => Complex.exp (-Complex.I * (inner ℝ (X + z) ξ : ℝ)) * (f X : ℂ)) z
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only
  rw [c13k_aux_phase_add]; ring

theorem c13k_aux_integral_apply {F : c13_E → c13_E} (hF : Integrable F) (j : Fin 2) :
    (∫ z, F z) j = ∫ z, F z j := by
  have := ContinuousLinearMap.integral_comp_comm (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) j) hF
  exact this.symm

theorem c13k_aux_inner_X (α c : ℝ) (f : SchwartzMap c13_E ℝ) (ξ z : c13_E) (j : Fin 2) :
    ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
        (((f (X - z) - f X) * c13_velocity_kernel α c z j : ℝ) : ℂ) =
      ((c13_velocity_kernel α c z j : ℝ) : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1) *
        ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ) := by
  have hpt : (fun X : c13_E => Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
        (((f (X - z) - f X) * c13_velocity_kernel α c z j : ℝ) : ℂ)) =
      fun X => ((c13_velocity_kernel α c z j : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f (X - z) : ℂ) -
          Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ)) := by
    funext X; push_cast; ring
  have h0 := c13k_aux_hat_int f ξ 0
  simp only [sub_zero] at h0
  rw [hpt, integral_const_mul, integral_sub (c13k_aux_hat_int f ξ z) h0, c13k_aux_hat_shift]
  ring

theorem c13k_aux_B_fourier {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (f : SchwartzMap c13_E ℝ)
    (ξ : c13_E) (j : Fin 2) :
    ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
        (((∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) j : ℝ) : ℂ) =
      (-Complex.I * ((c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2) : ℝ) : ℂ)) *
        ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ) := by
  obtain ⟨h1, -, -⟩ := c13k_aux_B_basic hα1 hα2 c f
  have hJ := c13k_aux_joint hα1 hα2 c f
  have hcomp : (fun X : c13_E => Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
        (((∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) j : ℝ) : ℂ)) =
      fun X => ∫ z : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
        (((f (X - z) - f X) * c13_velocity_kernel α c z j : ℝ) : ℂ) := by
    funext X
    rw [c13k_aux_integral_apply (h1 X), ← integral_complex_ofReal, ← integral_const_mul]
    simp only [PiLp.smul_apply, smul_eq_mul]
  have hGi : Integrable (fun p : c13_E × c13_E => Complex.exp (-Complex.I * (inner ℝ p.1 ξ : ℝ)) *
        (((f (p.1 - p.2) - f p.1) * c13_velocity_kernel α c p.2 j : ℝ) : ℂ)) (volume.prod volume) := by
    refine hJ.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine (((c13k_aux_phase_cont ξ).comp continuous_fst).measurable.mul
        (Complex.measurable_ofReal.comp ?_)).aestronglyMeasurable
      exact (((f.continuous.comp (continuous_fst.sub continuous_snd)).sub
        (f.continuous.comp continuous_fst)).measurable.mul
        ((PiLp.continuous_apply 2 _ j).measurable.comp ((c13k_aux_kernel_meas α c).comp measurable_snd)))
    · rw [norm_mul, c13k_aux_phase_norm, one_mul, Complex.norm_real, norm_mul, norm_smul]
      gcongr
      exact PiLp.norm_apply_le _ j
  rw [hcomp, integral_integral_swap hGi]
  have hin : (fun z : c13_E => ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
        (((f (X - z) - f X) * c13_velocity_kernel α c z j : ℝ) : ℂ)) =
      fun z => ((c13_velocity_kernel α c z j : ℝ) : ℂ) * (Complex.exp (-Complex.I * (inner ℝ z ξ : ℝ)) - 1) *
        ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ) :=
    funext fun z => c13k_aux_inner_X α c f ξ z j
  rw [hin, integral_mul_const, ((c13_kernel_symbol (c := c) hα1 hα2).1 ξ j).2]
theorem c13k_aux_hat_eq (f : SchwartzMap c13_E ℝ) (ξ : c13_E) :
    ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ) =
      𝓕 (fun X : c13_E => (f X : ℂ)) ((2 * π)⁻¹ • ξ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [smul_eq_mul, inner_smul_right]
  congr 2
  have : (2 * π) ≠ 0 := by positivity
  push_cast
  field_simp

theorem c13k_aux_hat_schwartz (f : SchwartzMap c13_E ℝ) :
    ∃ g : SchwartzMap c13_E ℂ, ∀ w, 𝓕 (fun X : c13_E => (f X : ℂ)) w = g w := by
  refine ⟨𝓕 (f.postcompCLM (Complex.ofRealCLM)), fun w => ?_⟩
  rw [SchwartzMap.fourier_coe]
  rfl

theorem c13k_aux_mult_int {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (f : SchwartzMap c13_E ℝ)
    (j : Fin 2) :
    Integrable (fun ξ : c13_E =>
        (-Complex.I * ((c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2) : ℝ) : ℂ)) *
          ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ)) := by
  obtain ⟨g, hg⟩ := c13k_aux_hat_schwartz f
  have hfe : ∀ ξ : c13_E, ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ) =
      g ((2 * π)⁻¹ • ξ) := fun ξ => by rw [c13k_aux_hat_eq, hg]
  simp_rw [hfe]
  set A := |c * c13_riesz_factor α|
  have h2π : (2 * π)⁻¹ ≠ 0 := by positivity
  have hb : Integrable (fun w : c13_E => A * (‖g w‖ + 2 * π * (‖w‖ ^ 1 * ‖g w‖))) :=
    (((g.integrable (μ := volume)).norm).add
      ((g.integrable_pow_mul volume 1).const_mul (2 * π))).const_mul A
  have hb' := hb.comp_smul h2π
  refine hb'.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
    · refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
      have := (c13k_aux_rot_cont j).measurable
      exact ((measurable_const.mul this).mul (by fun_prop))
    · exact (g.continuous.comp (continuous_const_smul _)).measurable
  · rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0:ℝ) < 2 * π),
      pow_one]
    have hξ : |c13_rotation ξ j| ≤ ‖ξ‖ := by
      rw [← Real.norm_eq_abs, ← c13k_aux_norm_rot ξ]; exact PiLp.norm_apply_le _ j
    have hr : |c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2)| ≤ A * (1 + ‖ξ‖) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      by_cases h0 : ξ = 0
      · subst h0
        have : c13_rotation (0 : c13_E) j = 0 := by fin_cases j <;> simp [c13_rotation]
        rw [this]; simp; positivity
      have hn : 0 < ‖ξ‖ := norm_pos_iff.2 h0
      have : |c13_rotation ξ j| * ‖ξ‖ ^ (α - 2) ≤ 1 + ‖ξ‖ := by
        calc |c13_rotation ξ j| * ‖ξ‖ ^ (α - 2) ≤ ‖ξ‖ * ‖ξ‖ ^ (α - 2) := by gcongr
          _ = ‖ξ‖ ^ (α - 1) := by
              rw [← Real.rpow_one_add' hn.le (by linarith)]; ring_nf
          _ ≤ 1 + ‖ξ‖ := by
              rcases le_or_gt ‖ξ‖ 1 with h | h
              · have := Real.rpow_le_one hn.le h (by linarith : 0 ≤ α - 1); linarith
              · have := Real.rpow_le_self_of_one_le h.le (by linarith : α - 1 ≤ 1); linarith
      calc A * |c13_rotation ξ j| * ‖ξ‖ ^ (α - 2)
          = A * (|c13_rotation ξ j| * ‖ξ‖ ^ (α - 2)) := by ring
        _ ≤ A * (1 + ‖ξ‖) := by gcongr
    calc |c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2)| * ‖g ((2 * π)⁻¹ • ξ)‖
        ≤ A * (1 + ‖ξ‖) * ‖g ((2 * π)⁻¹ • ξ)‖ := by gcongr
      _ = A * (‖g ((2 * π)⁻¹ • ξ)‖ + 2 * π * ((2 * π)⁻¹ * ‖ξ‖ * ‖g ((2 * π)⁻¹ • ξ)‖)) := by
        field_simp
theorem c13k_aux_inversion {g M : c13_E → ℂ} (hc : Continuous g) (hi : Integrable g)
    (hM : ∀ ξ, ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * g X = M ξ)
    (hMi : Integrable M) (X : c13_E) :
    g X = ((2 * π) ^ 2 : ℂ)⁻¹ * ∫ ξ : c13_E, Complex.exp (Complex.I * (inner ℝ X ξ : ℝ)) * M ξ := by
  have h2π : (2 * π) ≠ 0 := by positivity
  have hF : ∀ w, 𝓕 g w = M ((2 * π) • w) := by
    intro w
    rw [Real.fourier_eq', ← hM]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, inner_smul_right]
    congr 2
    push_cast; ring
  have hFi : Integrable (𝓕 g) := by
    have : 𝓕 g = fun w => M ((2 * π) • w) := funext hF
    rw [this]; exact hMi.comp_smul h2π
  have hinv := hi.fourierInv_fourier_eq hFi hc.continuousAt (v := X)
  rw [← hinv, Real.fourierInv_eq']
  have hsub := Measure.integral_comp_smul (μ := (volume : Measure c13_E))
    (fun ξ : c13_E => Complex.exp (Complex.I * (inner ℝ X ξ : ℝ)) * M ξ) (2 * π)
  rw [finrank_euclideanSpace_fin] at hsub
  have hl : ∫ w : c13_E, Complex.exp (↑(2 * π * inner ℝ w X) * Complex.I) • 𝓕 g w =
      ∫ w : c13_E, Complex.exp (Complex.I * (inner ℝ X ((2 * π) • w) : ℝ)) * M ((2 * π) • w) := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [smul_eq_mul, hF, inner_smul_right, real_inner_comm w X]
    congr 2
    push_cast; ring
  rw [hl, hsub, Complex.real_smul]
  congr 1
  rw [abs_of_pos (by positivity)]
  push_cast; ring
theorem c13k_aux_duality {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (f : SchwartzMap c13_E ℝ)
    (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    Integrable (fun X : c13_E =>
      inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X)) ∧
    ∫ X : c13_E, inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X) =
        ∫ Y : c13_E, f Y * c13_adjoint α c Φ Y := by
  obtain ⟨h1, hcB, hiB⟩ := c13k_aux_B_basic hα1 hα2 c f
  have hJ := c13k_aux_joint hα1 hα2 c f
  obtain ⟨C0, -, hC0, -, hb0, -, -⟩ := c13k_aux_schwartz_bounds f
  obtain ⟨MΦ, hMΦ⟩ := hΦ.continuous.bounded_above_of_compact_support hΦc
  have hMΦ0 : 0 ≤ MΦ := (norm_nonneg _).trans (hMΦ 0)
  obtain ⟨Cadj, -, hadj⟩ := c13_adjoint_integrable (α := α) hα1 hα2 c
  obtain ⟨hQ0, hpt0, -, -, -⟩ := hadj Φ hΦ hΦc
  have hKm := c13k_aux_kernel_meas α c
  have hΦm : Measurable Φ := hΦ.continuous.measurable
  have hfc := f.continuous
  -- integrability of the pairing
  have hI : Integrable (fun X : c13_E =>
      inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X)) := by
    refine (hiB.norm.mul_const MΦ).mono' ?_ (Eventually.of_forall fun X => ?_)
    · exact (hcB.inner hΦ.continuous).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hMΦ X)
  refine ⟨hI, ?_⟩
  -- Step 1: move the inner product inside
  have hstep1 : ∀ X : c13_E,
      inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X) =
        ∫ z : c13_E, (f (X - z) - f X) * inner ℝ (c13_velocity_kernel α c z) (Φ X) := by
    intro X
    rw [real_inner_comm, ← integral_inner (h1 X)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [real_inner_comm, real_inner_smul_left]
  have hP : Integrable (fun p : c13_E × c13_E =>
      (f (p.1 - p.2) - f p.1) * inner ℝ (c13_velocity_kernel α c p.2) (Φ p.1)) (volume.prod volume) := by
    refine (hJ.norm.mul_const MΦ).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hfc.comp (continuous_fst.sub continuous_snd)).sub
        (hfc.comp continuous_fst)).measurable.mul
        ((hKm.comp measurable_snd).inner (hΦm.comp measurable_fst))).aestronglyMeasurable
    · rw [norm_mul, norm_smul, mul_assoc]
      gcongr
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hMΦ _)
  have hQ : Integrable (fun p : c13_E × c13_E =>
      f p.1 * inner ℝ (c13_velocity_kernel α c p.2) (Φ (p.1 + p.2) - Φ p.1)) (volume.prod volume) := by
    refine (hQ0.norm.const_mul C0).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hfc.comp continuous_fst).measurable.mul
        ((hKm.comp measurable_snd).inner
          ((hΦm.comp (measurable_fst.add measurable_snd)).sub (hΦm.comp measurable_fst)))).aestronglyMeasurable
    · rw [norm_mul]
      gcongr
      rw [Real.norm_eq_abs]; exact hb0 _
  -- Step 2: for fixed z, translate
  have hstep2 : ∀ z : c13_E,
      ∫ X : c13_E, (f (X - z) - f X) * inner ℝ (c13_velocity_kernel α c z) (Φ X) =
        ∫ Y : c13_E, f Y * inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y) := by
    intro z
    have hb : ∀ W : c13_E, ‖inner ℝ (c13_velocity_kernel α c z) (Φ W)‖ ≤
        ‖c13_velocity_kernel α c z‖ * MΦ := fun W => by
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hMΦ _)
    have hcI : Continuous fun W : c13_E => inner ℝ (c13_velocity_kernel α c z) (Φ W) :=
      continuous_const.inner hΦ.continuous
    have hfi : Integrable (fun X : c13_E => f X) := f.integrable
    have i1 : Integrable (fun X : c13_E => f (X - z) * inner ℝ (c13_velocity_kernel α c z) (Φ X)) :=
      ((hfi.comp_sub_right z).norm.mul_const _).mono'
        (((hfc.comp (continuous_id.sub continuous_const)).mul hcI).aestronglyMeasurable)
        (Eventually.of_forall fun X => by rw [norm_mul]; gcongr; exact hb X)
    have i2 : Integrable (fun X : c13_E => f X * inner ℝ (c13_velocity_kernel α c z) (Φ X)) :=
      (hfi.norm.mul_const _).mono' ((hfc.mul hcI).aestronglyMeasurable)
        (Eventually.of_forall fun X => by rw [norm_mul]; gcongr; exact hb X)
    have i3 : Integrable (fun X : c13_E => f X * inner ℝ (c13_velocity_kernel α c z) (Φ (X + z))) :=
      (hfi.norm.mul_const _).mono'
        ((hfc.mul (continuous_const.inner (hΦ.continuous.comp (continuous_id.add continuous_const)))).aestronglyMeasurable)
        (Eventually.of_forall fun X => by rw [norm_mul]; gcongr; exact hb _)
    have htr := integral_sub_right_eq_self (μ := (volume : Measure c13_E))
      (fun X : c13_E => f X * inner ℝ (c13_velocity_kernel α c z) (Φ (X + z))) z
    simp only [sub_add_cancel] at htr
    have e1 : (fun X : c13_E => (f (X - z) - f X) * inner ℝ (c13_velocity_kernel α c z) (Φ X)) =
        fun X => f (X - z) * inner ℝ (c13_velocity_kernel α c z) (Φ X) -
          f X * inner ℝ (c13_velocity_kernel α c z) (Φ X) := by funext X; ring
    have e2 : (fun Y : c13_E => f Y * inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y)) =
        fun Y => f Y * inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z)) -
          f Y * inner ℝ (c13_velocity_kernel α c z) (Φ Y) := by
      funext Y; rw [inner_sub_right]; ring
    rw [e1, e2, integral_sub i1 i2, integral_sub i3 i2, htr]
  have hfun1 : (fun X : c13_E =>
      inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X)) =
      fun X => ∫ z : c13_E, (f (X - z) - f X) * inner ℝ (c13_velocity_kernel α c z) (Φ X) :=
    funext hstep1
  have hfun2 : (fun z : c13_E => ∫ X : c13_E,
      (f (X - z) - f X) * inner ℝ (c13_velocity_kernel α c z) (Φ X)) =
      fun z => ∫ Y : c13_E, f Y * inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y) :=
    funext hstep2
  have hfun3 : (fun Y : c13_E => ∫ z : c13_E,
      f Y * inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y)) =
      fun Y => f Y * c13_adjoint α c Φ Y := by
    funext Y; rw [integral_const_mul]; rfl
  rw [hfun1, integral_integral_swap hP, hfun2, ← integral_integral_swap hQ, hfun3]
/-- Blueprint: lem:c13_fourier_identification.  For a real Schwartz function `f`, the
cancellation integral `B f(X) = ∫ K(z) (f(X-z) - f(X)) dz` converges absolutely for every `X`,
is continuous and in `L¹(E;E)`; its Fourier transform (convention `e^{-iX·ξ}`) is
`-i c A_α (Jξ)_j |ξ|^{α-2} f̂(ξ)` componentwise; this product is integrable and inverts with
the factor `(2π)^{-2}` (i.e. `B f = -c A_α ∇^⊥(-Δ)^{-1+α/2} f`); and `B f` pairs with vector
tests through the adjoint `B*` of def:c13_kernel_data. -/
theorem c13_fourier_identification {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (f : SchwartzMap c13_E ℝ) :
    (∀ X : c13_E, Integrable (fun z : c13_E => (f (X - z) - f X) • c13_velocity_kernel α c z)) ∧
    Continuous (fun X : c13_E => ∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) ∧
    Integrable (fun X : c13_E => ∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) ∧
    (∀ (ξ : c13_E) (j : Fin 2),
      ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
          (((∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) j : ℝ) : ℂ) =
        (-Complex.I * ((c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2) : ℝ) : ℂ)) *
          ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ)) ∧
    (∀ j : Fin 2,
      Integrable (fun ξ : c13_E =>
        (-Complex.I * ((c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2) : ℝ) : ℂ)) *
          ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (f X : ℂ))) ∧
    (∀ (X : c13_E) (j : Fin 2),
      (((∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) j : ℝ) : ℂ) =
        ((2 * π) ^ 2 : ℂ)⁻¹ * ∫ ξ : c13_E, Complex.exp (Complex.I * (inner ℝ X ξ : ℝ)) *
          ((-Complex.I * ((c * c13_riesz_factor α * c13_rotation ξ j * ‖ξ‖ ^ (α - 2) : ℝ) : ℂ)) *
            ∫ Y : c13_E, Complex.exp (-Complex.I * (inner ℝ Y ξ : ℝ)) * (f Y : ℂ))) ∧
    (∀ Φ : c13_E → c13_E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      Integrable (fun X : c13_E =>
        inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X)) ∧
      Integrable (fun Y : c13_E => f Y * c13_adjoint α c Φ Y) ∧
      ∫ X : c13_E, inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X) =
        ∫ Y : c13_E, f Y * c13_adjoint α c Φ Y ∧
      ∫ X : c13_E, inner ℝ (∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) (Φ X) =
        -∫ X : c13_E, c13_renormalized_potential α c (fun Y => f Y) X *
          (fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
            fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1)) := by
  obtain ⟨h1, hc, hi⟩ := c13k_aux_B_basic hα1 hα2 c f
  refine ⟨h1, hc, hi, fun ξ j => c13k_aux_B_fourier hα1 hα2 c f ξ j,
    fun j => c13k_aux_mult_int hα1 hα2 c f j, fun X j => ?_, fun Φ hΦ hΦc => ?_⟩
  · refine c13k_aux_inversion
      (g := fun X => (((∫ z : c13_E, (f (X - z) - f X) • c13_velocity_kernel α c z) j : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp hc)) ?_
      (fun ξ => c13k_aux_B_fourier hα1 hα2 c f ξ j) (c13k_aux_mult_int hα1 hα2 c f j) X
    refine hi.norm.mono' (Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 _ j).comp hc)).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    rw [Complex.norm_real]
    exact PiLp.norm_apply_le _ j
  · obtain ⟨hI, hEq⟩ := c13k_aux_duality hα1 hα2 c f Φ hΦ hΦc
    obtain ⟨C0, -, -, -, hb0, -, -⟩ := c13k_aux_schwartz_bounds f
    obtain ⟨-, -, -, hV, -⟩ := c13_renormalized_potential_properties hα1 hα2 c
      (fun Y => f Y) f.continuous.measurable C0 hb0
    obtain ⟨hfB, -, hVeq⟩ := hV Φ hΦ hΦc
    exact ⟨hI, hfB, hEq, hEq.trans hVeq⟩

end GSQG
