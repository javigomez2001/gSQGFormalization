import GSQG.PatchEquation.Setup

/-!
# Beyond the paper (2D patch derivation): radial majorants, cancellation operator, test potential,
renormalized potential (blueprint ch. 13)

Helpers are named `c13b_aux_*`.

Conventions used in the statements below.
* A (vector or scalar) test function is `ContDiff ℝ (⊤ : ℕ∞)` with `HasCompactSupport`.
* `D Φ` is the Fréchet derivative `fderiv ℝ Φ`, with its operator norm.
* For a vector field `G : c13_E → c13_E`, its divergence at `Y` is written explicitly as
  `fderiv ℝ G Y (EuclideanSpace.single 0 1) 0 + fderiv ℝ G Y (EuclideanSpace.single 1 1) 1`
  (`∂₁ G₁ + ∂₂ G₂`); `div (J Φ)` is this with `G = c13_rotation ∘ Φ`.
* A bounded measurable density is `θ : c13_E → ℝ` with `Measurable θ` and `∀ Y, |θ Y| ≤ M`.
* The Fourier phase `e^{-i z·ξ}` is `Complex.exp (-(Complex.I * (inner ℝ z ξ : ℝ)))`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### lem:c13_radial_majorants -/

theorem c13b_aux_finrank : Module.finrank ℝ c13_E = 2 := by simp

theorem c13b_aux_vol_ball_one : volume.real (Metric.ball (0 : c13_E) 1) = π := by
  rw [Measure.real, EuclideanSpace.volume_ball_fin_two]; simp [Real.pi_pos.le]

theorem c13b_aux_radial_integral (f : ℝ → ℝ) :
    ∫ z : c13_E, f ‖z‖ = 2 * π * ∫ y in Ioi (0 : ℝ), y * f y := by
  rw [integral_fun_norm_addHaar volume f, c13b_aux_finrank, c13b_aux_vol_ball_one]
  simp [smul_eq_mul, mul_assoc]

theorem c13b_aux_radial_integrable (f : ℝ → ℝ) :
    Integrable (fun z : c13_E => f ‖z‖) ↔ IntegrableOn (fun y => y * f y) (Ioi (0 : ℝ)) := by
  rw [integrable_fun_norm_addHaar volume (f := f), c13b_aux_finrank]
  simp [smul_eq_mul]


theorem c13b_aux_ball_indicator (g : ℝ → ℝ) (r : ℝ) :
    (Metric.ball (0 : c13_E) r).indicator (fun z => g ‖z‖) = fun z => (Iio r).indicator g ‖z‖ := by
  ext z; simp [indicator]

theorem c13b_aux_ext_indicator (g : ℝ → ℝ) (r : ℝ) :
    {z : c13_E | r < ‖z‖}.indicator (fun z => g ‖z‖) = fun z => (Ioi r).indicator g ‖z‖ := by
  ext z; simp [indicator]

theorem c13b_aux_ball_rpow {α : ℝ} (hα2 : α < 2) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α)) (Metric.ball 0 r) ∧
      ∫ z in Metric.ball (0 : c13_E) r, ‖z‖ ^ (-α) = 2 * π / (2 - α) * r ^ (2 - α) := by
  have hcongr : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ c13_E - 1) • y ^ (-α))
      (fun y => y ^ (1 - α)) (Ioo 0 r) := by
    intro y hy
    simp only [c13b_aux_finrank, smul_eq_mul]
    rw [show (1 - α) = 1 + (-α) by ring, Real.rpow_add hy.1, Real.rpow_one]; norm_num
  have hii : IntegrableOn (fun y : ℝ => y ^ (1 - α)) (Ioo 0 r) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) (by linarith : -1 < 1 - α))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le] at this
    exact this.mono_set Ioo_subset_Ioc_self
  refine ⟨(integrableOn_fun_norm_addHaar volume (f := fun t => t ^ (-α))).2
    ((integrableOn_congr_fun hcongr measurableSet_Ioo).2 hii), ?_⟩
  have hind := c13b_aux_ball_indicator (fun t : ℝ => t ^ (-α)) r
  rw [← integral_indicator measurableSet_ball, hind, c13b_aux_radial_integral]
  have : ∫ y in Ioi (0 : ℝ), y * (Iio r).indicator (fun t => t ^ (-α)) y =
      ∫ y in Ioo 0 r, y ^ (1 - α) := by
    have h1 : (fun y => y * (Iio r).indicator (fun t : ℝ => t ^ (-α)) y) =
        (Iio r).indicator (fun y => y * y ^ (-α)) := by
      ext y; by_cases hy : y < r <;> simp [indicator, hy]
    rw [h1, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
    refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [show (1 - α) = 1 + (-α) by ring, Real.rpow_add hy.1, Real.rpow_one]
  rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by linarith))]
  rw [show 1 - α + 1 = 2 - α by ring, Real.zero_rpow (by linarith), sub_zero]
  field_simp

theorem c13b_aux_ext_rpow {α : ℝ} (hα1 : 1 < α) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α - 1)) {z | r < ‖z‖} ∧
      ∫ z in {z : c13_E | r < ‖z‖}, ‖z‖ ^ (-α - 1) = 2 * π / (α - 1) * r ^ (1 - α) := by
  have hms : MeasurableSet {z : c13_E | r < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have h1 : (fun y => y * (Ioi r).indicator (fun t : ℝ => t ^ (-α - 1)) y) =
      (Ioi r).indicator (fun y => y ^ (-α)) := by
    ext y; by_cases hy : r < y
    · simp only [indicator, mem_Ioi, hy, ite_true]
      have hy0 : 0 < y := hr.trans hy
      rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
    · simp [indicator, hy]
  have hind := c13b_aux_ext_indicator (fun t : ℝ => t ^ (-α - 1)) r
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff hms, hind, c13b_aux_radial_integrable, h1]
    exact ((integrable_indicator_iff measurableSet_Ioi).2
      (integrableOn_Ioi_rpow_of_lt (by linarith) hr)).integrableOn
  · rw [← integral_indicator hms, hind, c13b_aux_radial_integral, h1,
      setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hr.le,
      integral_Ioi_rpow_of_lt (by linarith) hr]
    rw [show -α + 1 = 1 - α by ring]
    have : α - 1 ≠ 0 := by linarith
    have : 1 - α ≠ 0 := by linarith
    field_simp
    ring


theorem c13b_aux_norm_sq (z : c13_E) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

theorem c13b_aux_rotation_apply (z : c13_E) :
    c13_rotation z 0 = -(z 1) ∧ c13_rotation z 1 = z 0 := by
  simp [c13_rotation]

theorem c13b_aux_norm_rotation (z : c13_E) : ‖c13_rotation z‖ = ‖z‖ := by
  have h := c13b_aux_norm_sq (c13_rotation z)
  rw [(c13b_aux_rotation_apply z).1, (c13b_aux_rotation_apply z).2] at h
  have : ‖c13_rotation z‖ ^ 2 = ‖z‖ ^ 2 := by rw [h, c13b_aux_norm_sq z]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem c13b_aux_continuous_rotation : Continuous c13_rotation := by
  unfold c13_rotation
  fun_prop

theorem c13b_aux_norm_kernel {α : ℝ} (hα : 0 < α) (c : ℝ) (z : c13_E) :
    ‖c13_velocity_kernel α c z‖ = |α * c| * ‖z‖ ^ (-α - 1) := by
  unfold c13_velocity_kernel
  split_ifs with hz
  · subst hz; simp [Real.zero_rpow (by linarith : -α - 1 ≠ 0)]
  · have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [norm_smul, c13b_aux_norm_rotation, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hp _), mul_assoc]
    congr 1
    rw [show -α - 1 = (-α - 2) + 1 by ring, Real.rpow_add hp, Real.rpow_one]

theorem c13b_aux_measurable_kernel (α c : ℝ) : Measurable (c13_velocity_kernel α c) := by
  unfold c13_velocity_kernel
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  have := c13b_aux_continuous_rotation.measurable
  fun_prop

theorem c13b_aux_coord_preserving :
    MeasurePreserving (fun z : c13_E => (z 0, z 1)) volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))


theorem c13b_aux_phase_le (s : ℝ) :
    ‖Complex.exp (-(Complex.I * (s : ℂ))) - 1‖ ≤ |s| ∧
      ‖Complex.exp (-(Complex.I * (s : ℂ))) - 1‖ ≤ 2 := by
  have e : -(Complex.I * (s : ℂ)) = Complex.I * ((-s : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  refine ⟨?_, ?_⟩
  · simpa [Real.norm_eq_abs, abs_neg] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -s))
  · calc _ ≤ ‖Complex.exp (Complex.I * ((-s : ℝ) : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal]; norm_num

theorem c13b_aux_symbol_bound {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : c13_E,
      Integrable (fun z : c13_E => ‖c13_velocity_kernel α c z‖ *
        ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) ∧
      (∫ z : c13_E, ‖c13_velocity_kernel α c z‖ *
        ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) ≤ C * ‖ξ‖ ^ (α - 1) ∧
      (ξ = 0 → (∫ z : c13_E, ‖c13_velocity_kernel α c z‖ *
        ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) = 0) := by
  set A := |α * c|
  have hA : 0 ≤ A := abs_nonneg _
  set D := 2 * π / (2 - α) + 2 * (2 * π / (α - 1))
  have hD : 0 ≤ D := by
    have : 0 < 2 - α := by linarith
    have : 0 < α - 1 := by linarith
    positivity
  refine ⟨A * D + 1, by positivity, fun ξ => ?_⟩
  have hmeas : AEStronglyMeasurable (fun z : c13_E => ‖c13_velocity_kernel α c z‖ *
      ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) volume := by
    have := c13b_aux_measurable_kernel α c
    apply Measurable.aestronglyMeasurable
    fun_prop
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 : (fun z : c13_E => ‖c13_velocity_kernel α c z‖ *
        ‖Complex.exp (-(Complex.I * ((inner ℝ z (0 : c13_E) : ℝ) : ℂ))) - 1‖) = fun _ => 0 := by
      ext z; simp
    rw [h0]
    refine ⟨integrable_zero _ _ _, ?_, fun _ => by simp⟩
    rw [integral_zero, norm_zero, Real.zero_rpow (by linarith), mul_zero]
  have hξp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set ρ := ‖ξ‖⁻¹ with hρ
  have hρp : 0 < ρ := inv_pos.2 hξp
  obtain ⟨iB, eB⟩ := c13b_aux_ball_rpow hα2 hρp
  obtain ⟨iX, eX⟩ := c13b_aux_ext_rpow hα1 hρp
  have hms : MeasurableSet {z : c13_E | ρ < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  set H : c13_E → ℝ := fun z => A * (‖ξ‖ * (Metric.ball (0 : c13_E) ρ).indicator
      (fun z => ‖z‖ ^ (-α)) z + 2 * {z : c13_E | ρ < ‖z‖}.indicator (fun z => ‖z‖ ^ (-α - 1)) z)
  have iH : Integrable H :=
    (((integrable_indicator_iff measurableSet_ball).2 iB).const_mul _ |>.add
      (((integrable_indicator_iff hms).2 iX).const_mul _)).const_mul _
  have hsph : ∀ᵐ z : c13_E ∂volume, z ∉ Metric.sphere (0 : c13_E) ρ := by
    have h := Measure.addHaar_sphere (volume : Measure c13_E) (0 : c13_E) ρ
    rw [ae_iff]; convert h using 2; ext z; simp
  have hbd : ∀ᵐ z : c13_E ∂volume, ‖‖c13_velocity_kernel α c z‖ *
      ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖‖ ≤ H z := by
    filter_upwards [hsph] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), c13b_aux_norm_kernel (by linarith)]
    have hH0 : 0 ≤ ‖ξ‖ * (Metric.ball (0 : c13_E) ρ).indicator (fun z => ‖z‖ ^ (-α)) z +
        2 * {z : c13_E | ρ < ‖z‖}.indicator (fun z => ‖z‖ ^ (-α - 1)) z := by
      have h1 : 0 ≤ (Metric.ball (0 : c13_E) ρ).indicator (fun z => ‖z‖ ^ (-α)) z :=
        indicator_nonneg (fun _ _ => by positivity) _
      have h2 : 0 ≤ {z : c13_E | ρ < ‖z‖}.indicator (fun z => ‖z‖ ^ (-α - 1)) z :=
        indicator_nonneg (fun _ _ => by positivity) _
      positivity
    by_cases hz0 : z = 0
    · subst hz0
      rw [norm_zero, Real.zero_rpow (by linarith), mul_zero, zero_mul]
      exact mul_nonneg hA hH0
    have ht : 0 < ‖z‖ := norm_pos_iff.2 hz0
    obtain ⟨p1, p2⟩ := c13b_aux_phase_le (inner ℝ z ξ)
    simp only [H, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hA
    rcases lt_or_gt_of_ne (show ‖z‖ ≠ ρ from fun h => hz (by simpa using h)) with hlt | hgt
    · have hin : z ∈ Metric.ball (0 : c13_E) ρ := by simpa using hlt
      have hout : z ∉ {z : c13_E | ρ < ‖z‖} := by simp [hlt.le]
      rw [indicator_of_mem hin, indicator_of_notMem hout, mul_zero, add_zero]
      calc ‖z‖ ^ (-α - 1) * ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖
          ≤ ‖z‖ ^ (-α - 1) * (‖z‖ * ‖ξ‖) :=
            mul_le_mul_of_nonneg_left (p1.trans (abs_real_inner_le_norm z ξ)) (by positivity)
        _ = ‖ξ‖ * ‖z‖ ^ (-α) := by
            rw [Real.rpow_sub_one ht.ne']; field_simp
    · have hin : z ∈ {z : c13_E | ρ < ‖z‖} := hgt
      have hout : z ∉ Metric.ball (0 : c13_E) ρ := by simp [hgt.le]
      rw [indicator_of_mem hin, indicator_of_notMem hout, mul_zero, zero_add]
      calc ‖z‖ ^ (-α - 1) * ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖
          ≤ ‖z‖ ^ (-α - 1) * 2 := mul_le_mul_of_nonneg_left p2 (by positivity)
        _ = 2 * ‖z‖ ^ (-α - 1) := by ring
  have hint : Integrable (fun z : c13_E => ‖c13_velocity_kernel α c z‖ *
      ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) := iH.mono' hmeas hbd
  refine ⟨hint, ?_, fun h => absurd h hξ⟩
  have hIH : ∫ z, H z = A * D * ‖ξ‖ ^ (α - 1) := by
    simp only [H]
    rw [integral_const_mul, integral_add (((integrable_indicator_iff measurableSet_ball).2 iB).const_mul _)
      (((integrable_indicator_iff hms).2 iX).const_mul _), integral_const_mul, integral_const_mul,
      integral_indicator measurableSet_ball, integral_indicator hms, eB, eX]
    have e1 : ρ ^ (2 - α) = ‖ξ‖ ^ (α - 1) * ‖ξ‖⁻¹ := by
      rw [hρ, Real.inv_rpow hξp.le, ← Real.rpow_neg hξp.le, ← Real.rpow_neg_one,
        ← Real.rpow_add hξp]; ring_nf
    have e2 : ρ ^ (1 - α) = ‖ξ‖ ^ (α - 1) := by
      rw [hρ, Real.inv_rpow hξp.le, ← Real.rpow_neg hξp.le]; ring_nf
    rw [e1, e2]; simp only [D]; field_simp
  calc _ ≤ ∫ z, H z := integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) iH
          (hbd.mono fun z hz => (Real.le_norm_self _).trans hz)
    _ = A * D * ‖ξ‖ ^ (α - 1) := hIH
    _ ≤ (A * D + 1) * ‖ξ‖ ^ (α - 1) := by nlinarith [Real.rpow_nonneg hξp.le (α - 1)]


/-- Blueprint: lem:c13_radial_majorants.  The coordinate map `E → ℝ × ℝ` preserves Lebesgue
measure, `|z|² = z₁² + z₂²`, the two radial integrals (with integrability), and the uniform bound
`∫ |K(z)| |e^{-iz·ξ} - 1| dz ≤ C |ξ|^{α-1}` (the integrand is integrable, and the integral vanishes
at `ξ = 0`). -/
theorem c13_radial_majorants {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) :
    MeasurePreserving (fun z : c13_E => (z 0, z 1)) volume volume ∧
    (∀ z : c13_E, ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2) ∧
    (∀ r : ℝ, 0 < r →
      IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α)) (Metric.ball 0 r) ∧
      ∫ z in Metric.ball (0 : c13_E) r, ‖z‖ ^ (-α) = 2 * π / (2 - α) * r ^ (2 - α)) ∧
    (∀ r : ℝ, 0 < r →
      IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α - 1)) {z | r < ‖z‖} ∧
      ∫ z in {z : c13_E | r < ‖z‖}, ‖z‖ ^ (-α - 1) = 2 * π / (α - 1) * r ^ (1 - α)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : c13_E,
      Integrable (fun z : c13_E => ‖c13_velocity_kernel α c z‖ *
        ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) ∧
      (∫ z : c13_E, ‖c13_velocity_kernel α c z‖ *
        ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) ≤ C * ‖ξ‖ ^ (α - 1) ∧
      (ξ = 0 → (∫ z : c13_E, ‖c13_velocity_kernel α c z‖ *
        ‖Complex.exp (-(Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))) - 1‖) = 0) :=
  ⟨c13b_aux_coord_preserving, c13b_aux_norm_sq, fun _ hr => c13b_aux_ball_rpow hα2 hr,
    fun _ hr => c13b_aux_ext_rpow hα1 hr, c13b_aux_symbol_bound hα1 hα2 c⟩

/-! ### lem:c13_test_translation -/

theorem c13b_aux_translation_pointwise (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ 1 Φ) (Y z : c13_E) :
    ‖Φ (Y + z) - Φ Y‖ ≤ ∫ t in (0:ℝ)..1, ‖fderiv ℝ Φ (Y + t • z)‖ * ‖z‖ := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Φ (Y + t • z)) (fderiv ℝ Φ (Y + t • z) z) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Y + t • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add Y
    exact ((hΦ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous (fun t : ℝ => fderiv ℝ Φ (Y + t • z) z) := by
    have := hΦ.continuous_fderiv one_ne_zero
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at hftc
  rw [← hftc]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall fun t _ => (fderiv ℝ Φ (Y + t • z)).le_opNorm z) ?_
  have := hΦ.continuous_fderiv one_ne_zero
  exact (by fun_prop : Continuous fun t : ℝ => ‖fderiv ℝ Φ (Y + t • z)‖ * ‖z‖).intervalIntegrable 0 1


theorem c13b_aux_translation_lintegral (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ 1 Φ) (z : c13_E) :
    ∫⁻ Y, ENNReal.ofReal ‖Φ (Y + z) - Φ Y‖ ≤ ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ Φ Y‖ * ‖z‖) := by
  have hc := hΦ.continuous_fderiv one_ne_zero
  have step1 : ∀ Y, ENNReal.ofReal ‖Φ (Y + z) - Φ Y‖ ≤
      ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (‖fderiv ℝ Φ (Y + t • z)‖ * ‖z‖) := by
    intro Y
    refine (ENNReal.ofReal_le_ofReal (c13b_aux_translation_pointwise Φ hΦ Y z)).trans_eq ?_
    rw [intervalIntegral.integral_of_le zero_le_one, ofReal_integral_eq_lintegral_ofReal]
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    · exact Eventually.of_forall fun t => by positivity
  calc ∫⁻ Y, ENNReal.ofReal ‖Φ (Y + z) - Φ Y‖
      ≤ ∫⁻ Y, ∫⁻ t in Ioc (0:ℝ) 1, ENNReal.ofReal (‖fderiv ℝ Φ (Y + t • z)‖ * ‖z‖) :=
        lintegral_mono step1
    _ = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ Φ (Y + t • z)‖ * ‖z‖) := by
        apply lintegral_lintegral_swap
        apply Measurable.aemeasurable
        apply ENNReal.measurable_ofReal.comp
        apply Continuous.measurable
        change Continuous fun p : c13_E × ℝ => ‖fderiv ℝ Φ (p.1 + p.2 • z)‖ * ‖z‖
        fun_prop
    _ = ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ Φ Y‖ * ‖z‖) := by
        congr 1; ext t
        exact lintegral_add_right_eq_self (fun Y => ENNReal.ofReal (‖fderiv ℝ Φ Y‖ * ‖z‖)) (t • z)
    _ = ∫⁻ Y, ENNReal.ofReal (‖fderiv ℝ Φ Y‖ * ‖z‖) := by
        rw [setLIntegral_const, Real.volume_Ioc]; simp

/-- Blueprint: lem:c13_test_translation.  For a vector test field `Φ` and `z ∈ E`,
`∫ |Φ(Y+z) - Φ(Y)| dY ≤ min (|z| ∫ ‖DΦ‖, 2 ∫ |Φ|)`, all integrals finite. -/
theorem c13_test_translation (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hsupp : HasCompactSupport Φ) (z : c13_E) :
    Integrable (fun Y => ‖Φ (Y + z) - Φ Y‖) ∧ Integrable (fun Y => ‖fderiv ℝ Φ Y‖) ∧
    Integrable (fun Y => ‖Φ Y‖) ∧
    (∫ Y, ‖Φ (Y + z) - Φ Y‖) ≤
      min (‖z‖ * ∫ Y, ‖fderiv ℝ Φ Y‖) (2 * ∫ Y, ‖Φ Y‖) := by
  have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
  have hcΦ : Continuous Φ := hΦ.continuous
  have hcD : Continuous (fderiv ℝ Φ) := h1.continuous_fderiv one_ne_zero
  have iΦ : Integrable Φ := hcΦ.integrable_of_hasCompactSupport hsupp
  have iD : Integrable (fderiv ℝ Φ) := hcD.integrable_of_hasCompactSupport (hsupp.fderiv (𝕜 := ℝ))
  have iT : Integrable (fun Y => Φ (Y + z)) := iΦ.comp_add_right z
  have iS : Integrable (fun Y => Φ (Y + z) - Φ Y) := iT.sub iΦ
  refine ⟨iS.norm, iD.norm, iΦ.norm, le_min ?_ ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
        iS.norm.aestronglyMeasurable, ← integral_const_mul,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => by positivity)
        (iD.norm.const_mul _).aestronglyMeasurable]
    refine ENNReal.toReal_mono ?_ ?_
    · exact ((iD.norm.const_mul ‖z‖).lintegral_lt_top).ne
    · refine (c13b_aux_translation_lintegral Φ h1 z).trans_eq ?_
      congr 1; ext Y; rw [mul_comm]
  · calc (∫ Y, ‖Φ (Y + z) - Φ Y‖) ≤ ∫ Y, (‖Φ (Y + z)‖ + ‖Φ Y‖) :=
          integral_mono iS.norm (iT.norm.add iΦ.norm) fun Y => norm_sub_le _ _
      _ = 2 * ∫ Y, ‖Φ Y‖ := by
          rw [integral_add iT.norm iΦ.norm,
            integral_add_right_eq_self (fun Y => ‖Φ Y‖) z]; ring

/-! ### lem:c13_adjoint_integrable -/

/-- The radial majorant `G_{a,b}(z) = |αc| (a 1_{|z|<1} |z|^{-α} + b 1_{|z|>1} |z|^{-α-1})`. -/
def c13b_aux_G (α c a b : ℝ) (z : c13_E) : ℝ :=
  |α * c| * (a * (Metric.ball (0 : c13_E) 1).indicator (fun z => ‖z‖ ^ (-α)) z +
    b * {z : c13_E | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-α - 1)) z)

theorem c13b_aux_G_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c a b : ℝ) :
    Integrable (c13b_aux_G α c a b) ∧
      ∫ z, c13b_aux_G α c a b z = |α * c| * (a * (2 * π / (2 - α)) + b * (2 * π / (α - 1))) := by
  obtain ⟨iB, eB⟩ := (c13_radial_majorants hα1 hα2 c).2.2.1 1 one_pos
  obtain ⟨iX, eX⟩ := (c13_radial_majorants hα1 hα2 c).2.2.2.1 1 one_pos
  have hms : MeasurableSet {z : c13_E | 1 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have i1 := ((integrable_indicator_iff measurableSet_ball).2 iB).const_mul a
  have i2 := ((integrable_indicator_iff hms).2 iX).const_mul b
  refine ⟨(i1.add i2).const_mul _, ?_⟩
  unfold c13b_aux_G
  rw [integral_const_mul, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_indicator measurableSet_ball, integral_indicator hms, eB, eX]
  simp

theorem c13b_aux_G_nonneg (α c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : c13_E) :
    0 ≤ c13b_aux_G α c a b z := by
  unfold c13b_aux_G
  have h1 : 0 ≤ (Metric.ball (0 : c13_E) 1).indicator (fun z => ‖z‖ ^ (-α)) z :=
    indicator_nonneg (fun _ _ => by positivity) _
  have h2 : 0 ≤ {z : c13_E | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-α - 1)) z :=
    indicator_nonneg (fun _ _ => by positivity) _
  positivity

/-- A.e. domination of `|K(z)| h(z)` by `G_{a,b}` when `0 ≤ h(z) ≤ min(a|z|, b)`. -/
theorem c13b_aux_kernel_dom {α : ℝ} (hα1 : 1 < α) (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : c13_E → ℝ) (hh : ∀ z, 0 ≤ h z ∧ h z ≤ a * ‖z‖ ∧ h z ≤ b) :
    ∀ᵐ z : c13_E ∂volume, ‖c13_velocity_kernel α c z‖ * h z ≤ c13b_aux_G α c a b z := by
  have hsph : ∀ᵐ z : c13_E ∂volume, z ∉ Metric.sphere (0 : c13_E) 1 := by
    have h := Measure.addHaar_sphere (volume : Measure c13_E) (0 : c13_E) 1
    rw [ae_iff]; convert h using 2; ext z; simp
  filter_upwards [hsph] with z hz
  rw [c13b_aux_norm_kernel (by linarith)]
  by_cases hz0 : z = 0
  · subst hz0
    rw [norm_zero, Real.zero_rpow (by linarith), mul_zero, zero_mul]
    exact c13b_aux_G_nonneg α c ha hb _
  have ht : 0 < ‖z‖ := norm_pos_iff.2 hz0
  obtain ⟨h0, h1, h2⟩ := hh z
  unfold c13b_aux_G
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases lt_or_gt_of_ne (show ‖z‖ ≠ 1 from fun h => hz (by simpa using h)) with hlt | hgt
  · have hin : z ∈ Metric.ball (0 : c13_E) 1 := by simpa using hlt
    have hout : z ∉ {z : c13_E | 1 < ‖z‖} := by simp [hlt.le]
    rw [indicator_of_mem hin, indicator_of_notMem hout, mul_zero, add_zero]
    calc ‖z‖ ^ (-α - 1) * h z ≤ ‖z‖ ^ (-α - 1) * (a * ‖z‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = a * ‖z‖ ^ (-α) := by
          rw [Real.rpow_sub_one ht.ne']; field_simp
  · have hin : z ∈ {z : c13_E | 1 < ‖z‖} := hgt
    have hout : z ∉ Metric.ball (0 : c13_E) 1 := by simp [hgt.le]
    rw [indicator_of_mem hin, indicator_of_notMem hout, mul_zero, zero_add]
    calc ‖z‖ ^ (-α - 1) * h z ≤ ‖z‖ ^ (-α - 1) * b := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = b * ‖z‖ ^ (-α - 1) := by ring


theorem c13b_aux_test_bounds (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hsupp : HasCompactSupport Φ) :
    ∃ L S : ℝ, 0 ≤ L ∧ 0 ≤ S ∧ ∀ Y z : c13_E,
      ‖Φ (Y + z) - Φ Y‖ ≤ L * ‖z‖ ∧ ‖Φ (Y + z) - Φ Y‖ ≤ 2 * S := by
  have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
  obtain ⟨L, hL⟩ := (h1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hsupp.fderiv (𝕜 := ℝ))
  obtain ⟨S, hS⟩ := hΦ.continuous.bounded_above_of_compact_support hsupp
  refine ⟨max L 0, max S 0, le_max_right _ _, le_max_right _ _, fun Y z => ⟨?_, ?_⟩⟩
  · have := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (f := Φ)
      (fun x _ => (h1.differentiable one_ne_zero) x) (fun x _ => (hL x).trans (le_max_left L 0))
      convex_univ (mem_univ Y) (mem_univ (Y + z))
    simpa using this
  · calc ‖Φ (Y + z) - Φ Y‖ ≤ ‖Φ (Y + z)‖ + ‖Φ Y‖ := norm_sub_le _ _
      _ ≤ max S 0 + max S 0 := add_le_add ((hS _).trans (le_max_left _ _))
          ((hS _).trans (le_max_left _ _))
      _ = 2 * max S 0 := by ring

theorem c13b_aux_adjoint_meas (α c : ℝ) (Φ : c13_E → c13_E) (hΦ : Continuous Φ) :
    Measurable (fun p : c13_E × c13_E =>
      inner ℝ (c13_velocity_kernel α c p.2) (Φ (p.1 + p.2) - Φ p.1)) := by
  have hK := c13b_aux_measurable_kernel α c
  have h2 : Measurable (fun p : c13_E × c13_E => Φ (p.1 + p.2) - Φ p.1) :=
    (by fun_prop : Continuous fun p : c13_E × c13_E => Φ (p.1 + p.2) - Φ p.1).measurable
  exact (hK.comp measurable_snd).inner h2

/-- Blueprint: lem:c13_adjoint_integrable.  With `C` chosen before the test field: the integrand
`(Y, z) ↦ K(z) · (Φ(Y+z) - Φ(Y))` is integrable on `E × E`, every inner integral converges
absolutely, `B*Φ ∈ L¹` with `‖B*Φ‖₁ ≤ C (‖Φ‖₁ + ‖DΦ‖₁)`, and `θ B*Φ` is integrable for every
bounded measurable `θ`. -/
theorem c13_adjoint_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Φ : c13_E → c13_E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      Integrable (fun p : c13_E × c13_E =>
        inner ℝ (c13_velocity_kernel α c p.2) (Φ (p.1 + p.2) - Φ p.1)) ∧
      (∀ Y : c13_E, Integrable (fun z : c13_E =>
        inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y))) ∧
      Integrable (c13_adjoint α c Φ) ∧
      (∫ Y, |c13_adjoint α c Φ Y|) ≤ C * ((∫ Y, ‖Φ Y‖) + ∫ Y, ‖fderiv ℝ Φ Y‖) ∧
      ∀ θ : c13_E → ℝ, Measurable θ → ∀ M : ℝ, (∀ Y, |θ Y| ≤ M) →
        Integrable (fun Y => θ Y * c13_adjoint α c Φ Y) := by
  set D := |α * c| * (2 * π / (2 - α) + 2 * (2 * π / (α - 1)))
  have hD : 0 ≤ D := by
    have : 0 < 2 - α := by linarith
    have : 0 < α - 1 := by linarith
    positivity
  refine ⟨D + 1, by positivity, fun Φ hΦ hsupp => ?_⟩
  set f : c13_E × c13_E → ℝ := fun p =>
    inner ℝ (c13_velocity_kernel α c p.2) (Φ (p.1 + p.2) - Φ p.1) with hf
  have hfM : Measurable f := c13b_aux_adjoint_meas α c Φ hΦ.continuous
  have hfm : AEStronglyMeasurable f (volume.prod volume) := hfM.aestronglyMeasurable
  have hfabs : ∀ Y z, ‖f (Y, z)‖ ≤ ‖c13_velocity_kernel α c z‖ * ‖Φ (Y + z) - Φ Y‖ := by
    intro Y z
    simpa [hf, Real.norm_eq_abs] using abs_real_inner_le_norm (c13_velocity_kernel α c z)
      (Φ (Y + z) - Φ Y)
  -- pointwise integrability in `z`
  obtain ⟨L, S, hL, hS, hLS⟩ := c13b_aux_test_bounds Φ hΦ hsupp
  have hpt : ∀ Y : c13_E, Integrable (fun z => f (Y, z)) := by
    intro Y
    refine (c13b_aux_G_integrable hα1 hα2 c L (2 * S)).1.mono' ?_ ?_
    · exact (hfM.comp measurable_prodMk_left).aestronglyMeasurable
    · filter_upwards [c13b_aux_kernel_dom hα1 c hL (by positivity)
        (fun z => ‖Φ (Y + z) - Φ Y‖) (fun z => ⟨norm_nonneg _, (hLS Y z).1, (hLS Y z).2⟩)] with z hz
      exact (hfabs Y z).trans hz
  -- the translation integrals
  set a := ∫ Y, ‖fderiv ℝ Φ Y‖
  set b := ∫ Y, ‖Φ Y‖
  have ha : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hb : 0 ≤ b := integral_nonneg fun _ => norm_nonneg _
  have hT := fun z => c13_test_translation Φ hΦ hsupp z
  have hinner : ∀ z, ∫ Y, ‖f (Y, z)‖ ≤ ‖c13_velocity_kernel α c z‖ * ∫ Y, ‖Φ (Y + z) - Φ Y‖ := by
    intro z
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((hT z).1.const_mul _) (Eventually.of_forall fun Y => hfabs Y z)
  have hdom : ∀ᵐ z : c13_E ∂volume, ∫ Y, ‖f (Y, z)‖ ≤ c13b_aux_G α c a (2 * b) z := by
    filter_upwards [c13b_aux_kernel_dom hα1 c ha (by positivity)
      (fun z => ∫ Y, ‖Φ (Y + z) - Φ Y‖)
      (fun z => ⟨integral_nonneg fun _ => norm_nonneg _,
        ((hT z).2.2.2.trans (min_le_left _ _)).trans_eq (mul_comm _ _),
        (hT z).2.2.2.trans (min_le_right _ _)⟩)] with z hz
    exact (hinner z).trans hz
  obtain ⟨iG, eG⟩ := c13b_aux_G_integrable hα1 hα2 c a (2 * b)
  have hnm : AEStronglyMeasurable (fun z => ∫ Y, ‖f (Y, z)‖) volume :=
    hfm.norm.prod_swap.integral_prod_right'
  have hprod : Integrable f (volume.prod volume) := by
    rw [integrable_prod_iff' hfm]
    refine ⟨Eventually.of_forall fun z => ?_, iG.mono' hnm ?_⟩
    · refine ((hT z).1.const_mul ‖c13_velocity_kernel α c z‖).mono' (hfM.comp measurable_prodMk_right).aestronglyMeasurable ?_
      exact Eventually.of_forall fun Y => hfabs Y z
    · filter_upwards [hdom] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hz
  have hB : Integrable (c13_adjoint α c Φ) := hprod.integral_prod_left
  refine ⟨hprod, hpt, hB, ?_, ?_⟩
  · calc (∫ Y, |c13_adjoint α c Φ Y|) ≤ ∫ Y, ∫ z, ‖f (Y, z)‖ := by
          refine integral_mono hB.abs hprod.norm.integral_prod_left fun Y => ?_
          change |∫ z, f (Y, z)| ≤ _
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => f (Y, z))
      _ = ∫ z, ∫ Y, ‖f (Y, z)‖ := integral_integral_swap (f := fun Y z => ‖f (Y, z)‖) hprod.norm
      _ ≤ ∫ z, c13b_aux_G α c a (2 * b) z :=
          integral_mono_ae hprod.norm.integral_prod_right iG hdom
      _ = |α * c| * (a * (2 * π / (2 - α)) + 2 * b * (2 * π / (α - 1))) := eG
      _ ≤ (D + 1) * (b + a) := by
          have : 0 < 2 - α := by linarith
          have : 0 < α - 1 := by linarith
          have h1 : a * (2 * π / (2 - α)) + 2 * b * (2 * π / (α - 1)) ≤
              (2 * π / (2 - α) + 2 * (2 * π / (α - 1))) * (b + a) := by
            have : 0 ≤ 2 * π / (2 - α) := by positivity
            have : 0 ≤ 2 * π / (α - 1) := by positivity
            nlinarith
          calc _ ≤ |α * c| * ((2 * π / (2 - α) + 2 * (2 * π / (α - 1))) * (b + a)) :=
                mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
            _ = D * (b + a) := by simp only [D]; ring
            _ ≤ (D + 1) * (b + a) := by nlinarith
  · intro θ hθ M hM
    exact hB.bdd_mul hθ.aestronglyMeasurable (Eventually.of_forall fun Y => by
      simpa [Real.norm_eq_abs] using hM Y)

/-! ### lem:c13_potential_convergence -/

theorem c13b_aux_P_abs {α : ℝ} (hα : 0 < α) (c : ℝ) (z : c13_E) :
    |c13_potential_kernel α c z| = |c| * ‖z‖ ^ (-α) := by
  unfold c13_potential_kernel
  split_ifs with hz
  · subst hz; simp [Real.zero_rpow (by linarith : -α ≠ 0)]
  · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]

theorem c13b_aux_P_of_ne {α c : ℝ} {z : c13_E} (hz : z ≠ 0) :
    c13_potential_kernel α c z = c * ‖z‖ ^ (-α) := by
  simp [c13_potential_kernel, hz]

theorem c13b_aux_measurable_P (α c : ℝ) : Measurable (c13_potential_kernel α c) := by
  unfold c13_potential_kernel
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

/-- One-dimensional mean-value bound for `t ↦ t^{-α}` on `[m, ∞)`. -/
theorem c13b_aux_rpow_mvt {α : ℝ} (hα : 0 < α) {m s t : ℝ} (hm : 0 < m) (hs : m ≤ s) (ht : m ≤ t) :
    |t ^ (-α) - s ^ (-α)| ≤ α * m ^ (-α - 1) * |t - s| := by
  have hd : ∀ x ∈ Ici m, HasDerivWithinAt (fun x : ℝ => x ^ (-α)) (-α * x ^ (-α - 1)) (Ici m) x :=
    fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (hm.trans_le hx).ne')).hasDerivWithinAt
  have hb : ∀ x ∈ Ici m, ‖-α * x ^ (-α - 1)‖ ≤ α * m ^ (-α - 1) := by
    intro x hx
    have hx0 : 0 < x := hm.trans_le hx
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hα, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm hx (by linarith)) hα.le
  have := (convex_Ici m).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hs ht
  simpa [Real.norm_eq_abs] using this

/-- Far-field mean-value bound: for `|X| ≤ R` and `|Y| ≥ 2R`, `Y ≠ 0`,
`||X - Y|^{-α} - |Y|^{-α}| ≤ α 2^{α+1} R |Y|^{-α-1}`. -/
theorem c13b_aux_far_mvt {α : ℝ} (hα : 0 < α) {R : ℝ} {X Y : c13_E} (hX : ‖X‖ ≤ R)
    (hY : 2 * R ≤ ‖Y‖) (hY0 : 0 < ‖Y‖) :
    |‖X - Y‖ ^ (-α) - ‖Y‖ ^ (-α)| ≤ α * 2 ^ (α + 1) * R * ‖Y‖ ^ (-α - 1) := by
  have hm : 0 < ‖Y‖ / 2 := by positivity
  have h1 : ‖Y‖ / 2 ≤ ‖X - Y‖ := by
    have := norm_sub_norm_le Y X
    rw [norm_sub_rev] at this
    linarith
  have h2 : ‖Y‖ / 2 ≤ ‖Y‖ := by linarith
  have := c13b_aux_rpow_mvt hα hm h2 h1
  have h3 : |‖X - Y‖ - ‖Y‖| ≤ R := by
    have := abs_norm_sub_norm_le (X - Y) (-Y)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
    linarith
  have h4 : (‖Y‖ / 2) ^ (-α - 1) = 2 ^ (α + 1) * ‖Y‖ ^ (-α - 1) := by
    rw [Real.div_rpow hY0.le zero_le_two, show -α - 1 = -(α + 1) by ring, Real.rpow_neg zero_le_two]
    field_simp
  calc _ ≤ α * (‖Y‖ / 2) ^ (-α - 1) * |‖X - Y‖ - ‖Y‖| := this
    _ ≤ α * (‖Y‖ / 2) ^ (-α - 1) * R := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by rw [h4]; ring


/-- The subtracted kernel `P(X - Y) - 1_{|Y|>ρ} P(-Y)`. -/
def c13b_aux_k (α c ρ : ℝ) (X Y : c13_E) : ℝ :=
  c13_potential_kernel α c (X - Y) - (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)

theorem c13b_aux_measurable_k (α c ρ : ℝ) :
    Measurable (fun p : c13_E × c13_E => c13b_aux_k α c ρ p.1 p.2) := by
  unfold c13b_aux_k
  have hP := c13b_aux_measurable_P α c
  refine (hP.comp (measurable_fst.sub measurable_snd)).sub ?_
  refine Measurable.ite ?_ (hP.comp measurable_snd.neg) measurable_const
  exact measurableSet_lt measurable_const (measurable_norm.comp measurable_snd)

theorem c13b_aux_measurable_k_slice (α c ρ : ℝ) (X : c13_E) :
    Measurable (fun Y => c13b_aux_k α c ρ X Y) := by
  unfold c13b_aux_k
  have hP := c13b_aux_measurable_P α c
  refine (hP.comp (measurable_const.sub measurable_id)).sub ?_
  refine Measurable.ite ?_ (hP.comp measurable_id.neg) measurable_const
  exact measurableSet_lt measurable_const measurable_norm

/-- The majorant of the subtracted kernel for `|X| ≤ R`. -/
def c13b_aux_m (α c R : ℝ) (X Y : c13_E) : ℝ :=
  |c| * (Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α)) (X - Y) +
    |c| * (Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator (fun _ => (1 : ℝ)) Y +
    (|c| * α * 2 ^ (α + 1) * R) *
      {w : c13_E | 2 * R + 2 < ‖w‖}.indicator (fun w => ‖w‖ ^ (-α - 1)) Y

theorem c13b_aux_k_le_m {α : ℝ} (hα1 : 1 < α) (c : ℝ) {R : ℝ} (hR : 0 ≤ R) {X : c13_E}
    (hX : ‖X‖ ≤ R) (Y : c13_E) : |c13b_aux_k α c 1 X Y| ≤ c13b_aux_m α c R X Y := by
  have hα : 0 < α := by linarith
  have t1 : 0 ≤ (Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α)) (X - Y) :=
    indicator_nonneg (fun _ _ => by positivity) _
  have t2 : 0 ≤ (Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator (fun _ => (1 : ℝ)) Y :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  have t3 : 0 ≤ {w : c13_E | 2 * R + 2 < ‖w‖}.indicator (fun w => ‖w‖ ^ (-α - 1)) Y :=
    indicator_nonneg (fun _ _ => by positivity) _
  unfold c13b_aux_k c13b_aux_m
  by_cases hY : ‖Y‖ ≤ 2 * R + 2
  · have hXY : ‖X - Y‖ < 3 * R + 3 := by
      have := norm_sub_le X Y; linarith
    rw [indicator_of_mem (by simpa using hXY : X - Y ∈ Metric.ball (0 : c13_E) (3 * R + 3)),
      indicator_of_mem (by simpa using hY : Y ∈ Metric.closedBall (0 : c13_E) (2 * R + 2))]
    have hite : |(if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)| ≤ |c| := by
      split_ifs with h1
      · rw [c13b_aux_P_abs hα, norm_neg]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith))
      · simp
    calc _ ≤ |c13_potential_kernel α c (X - Y)| +
          |(if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)| := abs_sub _ _
      _ ≤ |c| * ‖X - Y‖ ^ (-α) + |c| * 1 := by
          rw [c13b_aux_P_abs hα]; linarith
      _ ≤ _ := by
          have : 0 ≤ (|c| * α * 2 ^ (α + 1) * R) *
            {w : c13_E | 2 * R + 2 < ‖w‖}.indicator (fun w => ‖w‖ ^ (-α - 1)) Y := by positivity
          linarith
  · push Not at hY
    have hY0 : 0 < ‖Y‖ := by linarith
    have hXY : X - Y ≠ 0 := by
      intro h
      have : X = Y := sub_eq_zero.1 h
      rw [this] at hX; linarith
    have h1 : 1 < ‖Y‖ := by linarith
    rw [ite_eq_left_iff.mpr (fun h => absurd h1 h), c13b_aux_P_of_ne hXY, c13b_aux_P_of_ne (neg_ne_zero.2 (norm_pos_iff.1 hY0)),
      norm_neg, indicator_of_mem (show Y ∈ {w : c13_E | 2 * R + 2 < ‖w‖} from hY), ← mul_sub,
      abs_mul]
    have := c13b_aux_far_mvt hα hX (by linarith) hY0
    calc |c| * |‖X - Y‖ ^ (-α) - ‖Y‖ ^ (-α)| ≤ |c| * (α * 2 ^ (α + 1) * R * ‖Y‖ ^ (-α - 1)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ _ := by
          have : 0 ≤ |c| * (Metric.ball (0 : c13_E) (3 * R + 3)).indicator
            (fun w => ‖w‖ ^ (-α)) (X - Y) := by positivity
          have : 0 ≤ |c| * (Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator
            (fun _ => (1 : ℝ)) Y := by positivity
          have : |c| * (α * 2 ^ (α + 1) * R * ‖Y‖ ^ (-α - 1)) =
            |c| * α * 2 ^ (α + 1) * R * ‖Y‖ ^ (-α - 1) := by ring
          linarith

/-- The `X`-independent value of the majorant integral. -/
def c13b_aux_mint (α c R : ℝ) : ℝ :=
  |c| * (∫ w, (Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α)) w) +
    |c| * (∫ Y, (Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator (fun _ => (1 : ℝ)) Y) +
    (|c| * α * 2 ^ (α + 1) * R) *
      ∫ Y, {w : c13_E | 2 * R + 2 < ‖w‖}.indicator (fun w => ‖w‖ ^ (-α - 1)) Y

theorem c13b_aux_m_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (X : c13_E) :
    Integrable (c13b_aux_m α c R X) ∧ ∫ Y, c13b_aux_m α c R X Y = c13b_aux_mint α c R := by
  obtain ⟨iB, -⟩ := (c13_radial_majorants hα1 hα2 c).2.2.1 (3 * R + 3) (by linarith)
  obtain ⟨iX, -⟩ := (c13_radial_majorants hα1 hα2 c).2.2.2.1 (2 * R + 2) (by linarith)
  have hms : MeasurableSet {z : c13_E | 2 * R + 2 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have g1 : Integrable ((Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α))) :=
    (integrable_indicator_iff measurableSet_ball).2 iB
  have i1 : Integrable (fun Y => |c| *
      (Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α)) (X - Y)) :=
    (g1.comp_sub_left X).const_mul |c|
  have g2 : Integrable ((Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  have i2 : Integrable (fun Y => |c| *
      (Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator (fun _ => (1 : ℝ)) Y) := g2.const_mul _
  have i3 : Integrable (fun Y => (|c| * α * 2 ^ (α + 1) * R) *
      {w : c13_E | 2 * R + 2 < ‖w‖}.indicator (fun w => ‖w‖ ^ (-α - 1)) Y) :=
    ((integrable_indicator_iff hms).2 iX).const_mul _
  have i12 : Integrable (fun Y => |c| *
      (Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α)) (X - Y) + |c| *
      (Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator (fun _ => (1 : ℝ)) Y) := i1.add i2
  refine ⟨i12.add i3, ?_⟩
  unfold c13b_aux_m c13b_aux_mint
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_sub_left_eq_self
      (fun w => (Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α)) w) volume X]


theorem c13b_aux_mint_nonneg {α : ℝ} (hα1 : 1 < α) (c : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ c13b_aux_mint α c R := by
  unfold c13b_aux_mint
  have h1 : 0 ≤ ∫ w, (Metric.ball (0 : c13_E) (3 * R + 3)).indicator (fun w => ‖w‖ ^ (-α)) w :=
    integral_nonneg fun _ => indicator_nonneg (fun _ _ => by positivity) _
  have h2 : 0 ≤ ∫ Y, (Metric.closedBall (0 : c13_E) (2 * R + 2)).indicator (fun _ => (1 : ℝ)) Y :=
    integral_nonneg fun _ => indicator_nonneg (fun _ _ => zero_le_one) _
  have h3 : 0 ≤ ∫ Y, {w : c13_E | 2 * R + 2 < ‖w‖}.indicator (fun w => ‖w‖ ^ (-α - 1)) Y :=
    integral_nonneg fun _ => indicator_nonneg (fun _ _ => by positivity) _
  have : 0 ≤ α := by linarith
  positivity

/-- Quantitative bound (i) of lem:c13_potential_convergence, in terms of `c13b_aux_k`. -/
theorem c13b_aux_k_bound {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (θ : c13_E → ℝ) (hθ : Measurable θ) (M : ℝ) (hM : ∀ Y, |θ Y| ≤ M) (X : c13_E) (hX : ‖X‖ ≤ R) :
    Integrable (fun Y => |c13b_aux_k α c 1 X Y| * |θ Y|) ∧
      (∫ Y, |c13b_aux_k α c 1 X Y| * |θ Y|) ≤ c13b_aux_mint α c R * M := by
  obtain ⟨im, em⟩ := c13b_aux_m_integrable hα1 hα2 c hR X
  have hkm : Measurable (fun Y => c13b_aux_k α c 1 X Y) := c13b_aux_measurable_k_slice α c 1 X
  have hbd : ∀ Y, |c13b_aux_k α c 1 X Y| * |θ Y| ≤ c13b_aux_m α c R X Y * M := fun Y =>
    mul_le_mul (c13b_aux_k_le_m hα1 c hR hX Y) (hM Y) (abs_nonneg _)
      ((abs_nonneg _).trans (c13b_aux_k_le_m hα1 c hR hX Y))
  have hint : Integrable (fun Y => |c13b_aux_k α c 1 X Y| * |θ Y|) := by
    refine (im.mul_const M).mono' (hkm.abs.mul hθ.abs).aestronglyMeasurable
      (Eventually.of_forall fun Y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbd Y
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ Y, c13b_aux_m α c R X Y * M := integral_mono hint (im.mul_const M) hbd
    _ = _ := by rw [integral_mul_const, em]

theorem c13b_aux_measurable_V (α c ρ : ℝ) (θ : c13_E → ℝ) (hθ : Measurable θ) :
    Measurable (fun X => ∫ Y, c13b_aux_k α c ρ X Y * θ Y) := by
  have h : StronglyMeasurable (fun p : c13_E × c13_E => c13b_aux_k α c ρ p.1 p.2 * θ p.2) :=
    ((c13b_aux_measurable_k α c ρ).mul (hθ.comp measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).measurable

/-- Change of subtraction radius: the difference kernel. -/
theorem c13b_aux_radius_change {α : ℝ} (hα1 : 1 < α) (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (θ : c13_E → ℝ) (hθ : Measurable θ) (M : ℝ) (hM : ∀ Y, |θ Y| ≤ M) :
    Integrable (fun Y => (c13b_aux_k α c ρ 0 Y - c13b_aux_k α c 1 0 Y) * θ Y) ∧
      ∀ X Y, c13b_aux_k α c ρ X Y = c13b_aux_k α c 1 X Y + (c13b_aux_k α c ρ 0 Y - c13b_aux_k α c 1 0 Y) := by
  have hα : 0 < α := by linarith
  refine ⟨?_, fun X Y => by unfold c13b_aux_k; ring⟩
  set m0 := min 1 ρ
  have hm0 : 0 < m0 := lt_min one_pos hρ
  set B := |c| * m0 ^ (-α)
  have hd : ∀ Y, |c13b_aux_k α c ρ 0 Y - c13b_aux_k α c 1 0 Y| ≤
      B * (Metric.closedBall (0 : c13_E) (max 1 ρ)).indicator (fun _ => (1 : ℝ)) Y := by
    intro Y
    have hB0 : 0 ≤ B * (Metric.closedBall (0 : c13_E) (max 1 ρ)).indicator (fun _ => (1 : ℝ)) Y :=
      mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => zero_le_one) _)
    have key : ∀ a b : ℝ, m0 ≤ b → a ≤ max 1 ρ → b < ‖Y‖ → ‖Y‖ ≤ a →
        |c13_potential_kernel α c (-Y)| ≤ B * (Metric.closedBall (0 : c13_E) (max 1 ρ)).indicator
          (fun _ => (1 : ℝ)) Y := by
      intro a b hb ha hbY hYa
      rw [indicator_of_mem (by simpa using hYa.trans ha), mul_one, c13b_aux_P_abs hα, norm_neg]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hm0 (by linarith)
        (by linarith)) (abs_nonneg _)
    have e : c13b_aux_k α c ρ 0 Y - c13b_aux_k α c 1 0 Y =
        (if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0) -
          (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0) := by
      unfold c13b_aux_k; ring
    rw [e]
    split_ifs with h1 h2 h2
    · simpa using hB0
    · rw [sub_zero]; exact key ρ 1 (min_le_left _ _) (le_max_right _ _) h1 (not_lt.1 h2)
    · rw [zero_sub, abs_neg]; exact key 1 ρ (min_le_right _ _) (le_max_left _ _) h2 (not_lt.1 h1)
    · simpa using hB0
  have hmeas : Measurable (fun Y => (c13b_aux_k α c ρ 0 Y - c13b_aux_k α c 1 0 Y) * θ Y) :=
    ((c13b_aux_measurable_k_slice α c ρ 0).sub (c13b_aux_measurable_k_slice α c 1 0)).mul hθ
  have g2 : Integrable ((Metric.closedBall (0 : c13_E) (max 1 ρ)).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  refine ((g2.const_mul B).mul_const M).mono' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun Y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hd Y) (hM Y) (abs_nonneg _) ((abs_nonneg _).trans (hd Y))


theorem c13b_aux_M_nonneg {θ : c13_E → ℝ} {M : ℝ} (hM : ∀ Y, |θ Y| ≤ M) : 0 ≤ M :=
  (abs_nonneg _).trans (hM 0)

/-- Absolute convergence, measurability and local bounds of `∫ k_1(X, ·) θ`. -/
theorem c13b_aux_V_basic {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ)
    (θ : c13_E → ℝ) (hθ : Measurable θ) (M : ℝ) (hM : ∀ Y, |θ Y| ≤ M) :
    (∀ X : c13_E, Integrable (fun Y => c13b_aux_k α c 1 X Y * θ Y)) ∧
      Measurable (c13_renormalized_potential α c θ) ∧
      ∀ R : ℝ, ∃ B : ℝ, ∀ X : c13_E, ‖X‖ ≤ R → |c13_renormalized_potential α c θ X| ≤ B := by
  have hint : ∀ X : c13_E, Integrable (fun Y => c13b_aux_k α c 1 X Y * θ Y) := by
    intro X
    have := (c13b_aux_k_bound hα1 hα2 c (norm_nonneg X) θ hθ M hM X le_rfl).1
    refine this.mono' ((c13b_aux_measurable_k_slice α c 1 X).mul hθ).aestronglyMeasurable
      (Eventually.of_forall fun Y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
  refine ⟨hint, c13b_aux_measurable_V α c 1 θ hθ, fun R => ?_⟩
  refine ⟨c13b_aux_mint α c (max R 0) * M, fun X hX => ?_⟩
  have hX' : ‖X‖ ≤ max R 0 := hX.trans (le_max_left _ _)
  obtain ⟨i, e⟩ := c13b_aux_k_bound hα1 hα2 c (le_max_right R 0) θ hθ M hM X hX'
  calc |c13_renormalized_potential α c θ X| = |∫ Y, c13b_aux_k α c 1 X Y * θ Y| := rfl
    _ ≤ ∫ Y, |c13b_aux_k α c 1 X Y * θ Y| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun Y => c13b_aux_k α c 1 X Y * θ Y)
    _ = ∫ Y, |c13b_aux_k α c 1 X Y| * |θ Y| := by simp_rw [abs_mul]
    _ ≤ _ := e

theorem c13b_aux_V_radius {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (θ : c13_E → ℝ) (hθ : Measurable θ) (M : ℝ) (hM : ∀ Y, |θ Y| ≤ M) :
    (∀ X : c13_E, Integrable (fun Y => c13b_aux_k α c ρ X Y * θ Y)) ∧
      ∃ k : ℝ, ∀ X : c13_E,
        (∫ Y, c13b_aux_k α c ρ X Y * θ Y) = c13_renormalized_potential α c θ X + k := by
  obtain ⟨hint, -, -⟩ := c13b_aux_V_basic hα1 hα2 c θ hθ M hM
  obtain ⟨id, hk⟩ := c13b_aux_radius_change hα1 c hρ θ hθ M hM
  have e : ∀ X, (fun Y => c13b_aux_k α c ρ X Y * θ Y) = fun Y => c13b_aux_k α c 1 X Y * θ Y +
      (c13b_aux_k α c ρ 0 Y - c13b_aux_k α c 1 0 Y) * θ Y := by
    intro X; ext Y; rw [hk X Y]; ring
  refine ⟨fun X => by rw [e X]; exact (hint X).add id, ∫ Y, (c13b_aux_k α c ρ 0 Y - c13b_aux_k α c 1 0 Y) * θ Y,
    fun X => ?_⟩
  rw [e X, integral_add (hint X) id]
  rfl

/-- Blueprint: lem:c13_potential_convergence.  (i) For `R ≥ 1` a constant `C_R` (chosen before
`θ`, `M`, `X`) bounds `∫ |P(X-Y) - 1_{|Y|>1} P(-Y)| |θ(Y)| dY ≤ C_R M` for `|X| ≤ R` (with
integrability).  (ii) Hence for bounded measurable `θ` the defining integral of `V[θ]` converges
absolutely at every `X`, and `V[θ]` is measurable and locally bounded.  (iii) Replacing the
subtraction radius `1` by any `ρ > 0` gives an absolutely convergent integral differing from
`V[θ]` by a constant independent of `X`. -/
theorem c13_potential_convergence {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) :
    (∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ θ : c13_E → ℝ, Measurable θ → ∀ M : ℝ, 0 ≤ M → (∀ Y, |θ Y| ≤ M) →
        ∀ X : c13_E, ‖X‖ ≤ R →
          Integrable (fun Y => |c13_potential_kernel α c (X - Y) -
              (if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)| * |θ Y|) ∧
          (∫ Y, |c13_potential_kernel α c (X - Y) -
              (if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)| * |θ Y|) ≤ C * M) ∧
    (∀ θ : c13_E → ℝ, Measurable θ → ∀ M : ℝ, (∀ Y, |θ Y| ≤ M) →
      (∀ X : c13_E, Integrable (fun Y => (c13_potential_kernel α c (X - Y) -
          (if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y)) ∧
      Measurable (c13_renormalized_potential α c θ) ∧
      ∀ R : ℝ, ∃ B : ℝ, ∀ X : c13_E, ‖X‖ ≤ R → |c13_renormalized_potential α c θ X| ≤ B) ∧
    (∀ ρ : ℝ, 0 < ρ → ∀ θ : c13_E → ℝ, Measurable θ → ∀ M : ℝ, (∀ Y, |θ Y| ≤ M) →
      (∀ X : c13_E, Integrable (fun Y => (c13_potential_kernel α c (X - Y) -
          (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y)) ∧
      ∃ k : ℝ, ∀ X : c13_E,
        (∫ Y, (c13_potential_kernel α c (X - Y) -
          (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y) =
          c13_renormalized_potential α c θ X + k) := by
  refine ⟨fun R hR => ⟨c13b_aux_mint α c R + 1,
      by linarith [c13b_aux_mint_nonneg hα1 c (by linarith : (0 : ℝ) ≤ R)], ?_⟩,
    fun θ hθ M hM => c13b_aux_V_basic hα1 hα2 c θ hθ M hM,
    fun ρ hρ θ hθ M hM => c13b_aux_V_radius hα1 hα2 c hρ θ hθ M hM⟩
  intro θ hθ M hM0 hMθ X hX
  obtain ⟨i, e⟩ := c13b_aux_k_bound hα1 hα2 c (by linarith) θ hθ M hMθ X hX
  exact ⟨i, e.trans (by nlinarith)⟩

/-! ### lem:c13_test_potential -/

/-- `δ`-regularized potential kernel `c (|z|² + δ²)^{-α/2}`. -/
def c13b_aux_Pd (α c δ : ℝ) (z : c13_E) : ℝ := c * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2)

/-- `δ`-regularized velocity kernel `α c (|z|² + δ²)^{-α/2-1} J z`. -/
def c13b_aux_Kd (α c δ : ℝ) (z : c13_E) : c13_E :=
  (α * c * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1)) • c13_rotation z

theorem c13b_aux_Pd_hasFDerivAt (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) (z : c13_E) :
    HasFDerivAt (c13b_aux_Pd α c δ)
      (c • (((-α / 2) * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1)) • (2 • innerSL ℝ z))) z := by
  have h1 : HasFDerivAt (fun z : c13_E => ‖z‖ ^ 2 + δ ^ 2) (2 • innerSL ℝ z) z := by
    have := (hasFDerivAt_id z).norm_sq
    simpa using this.add_const (δ ^ 2)
  have h2 := h1.rpow_const (p := -α / 2) (Or.inl (by positivity))
  exact h2.const_mul c

theorem c13b_aux_Pd_fderiv_apply (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) (z v : c13_E) :
    fderiv ℝ (c13b_aux_Pd α c δ) z v =
      -(α * c * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1)) * inner ℝ z v := by
  rw [(c13b_aux_Pd_hasFDerivAt α c hδ z).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast; ring

theorem c13b_aux_inner_single (z : c13_E) (i : Fin 2) :
    inner ℝ z (EuclideanSpace.single i 1) = z i := by
  rw [EuclideanSpace.inner_single_right]; simp

theorem c13b_aux_inner_eq (v w : c13_E) : inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]; simp [mul_comm]

theorem c13b_aux_Kd_inner (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) (z w : c13_E) :
    inner ℝ (c13b_aux_Kd α c δ z) w =
      fderiv ℝ (c13b_aux_Pd α c δ) z (EuclideanSpace.single 1 1) * w 0 -
        fderiv ℝ (c13b_aux_Pd α c δ) z (EuclideanSpace.single 0 1) * w 1 := by
  rw [c13b_aux_Pd_fderiv_apply α c hδ, c13b_aux_Pd_fderiv_apply α c hδ, c13b_aux_inner_single,
    c13b_aux_inner_single, c13b_aux_Kd, real_inner_smul_left, c13b_aux_inner_eq,
    (c13b_aux_rotation_apply z).1, (c13b_aux_rotation_apply z).2]
  ring

theorem c13b_aux_continuous_Pd (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) : Continuous (c13b_aux_Pd α c δ) := by
  unfold c13b_aux_Pd
  refine continuous_const.mul ((continuous_norm.pow 2).add continuous_const |>.rpow_const ?_)
  intro z; left; exact (by positivity : (0:ℝ) < ‖z‖ ^ 2 + δ ^ 2).ne'

theorem c13b_aux_continuous_Kd (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) : Continuous (c13b_aux_Kd α c δ) := by
  unfold c13b_aux_Kd
  refine Continuous.smul (continuous_const.mul ((continuous_norm.pow 2).add continuous_const
    |>.rpow_const ?_)) c13b_aux_continuous_rotation
  intro z; left; exact (by positivity : (0:ℝ) < ‖z‖ ^ 2 + δ ^ 2).ne'

theorem c13b_aux_continuous_Pd_fderiv (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) (v : c13_E) :
    Continuous (fun z => fderiv ℝ (c13b_aux_Pd α c δ) z v) := by
  have : (fun z => fderiv ℝ (c13b_aux_Pd α c δ) z v) = fun z =>
      -(α * c * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1)) * inner ℝ z v := by
    ext z; exact c13b_aux_Pd_fderiv_apply α c hδ z v
  rw [this]
  refine ((continuous_const.mul ((continuous_norm.pow 2).add continuous_const
    |>.rpow_const ?_)).neg).mul (continuous_id.inner continuous_const)
  intro z; left; exact (by positivity : (0:ℝ) < ‖z‖ ^ 2 + δ ^ 2).ne'


/-- Scalar curl `∂₁Φ₂ - ∂₂Φ₁ = -div(JΦ)` of a vector field. -/
def c13b_aux_curl (Φ : c13_E → c13_E) (W : c13_E) : ℝ :=
  fderiv ℝ Φ W (EuclideanSpace.single 0 1) 1 - fderiv ℝ Φ W (EuclideanSpace.single 1 1) 0

theorem c13b_aux_shift_coord_hasFDerivAt (Φ : c13_E → c13_E) (hΦ : Differentiable ℝ Φ)
    (Y : c13_E) (i : Fin 2) (z : c13_E) :
    HasFDerivAt (fun z => Φ (Y + z) i)
      ((EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).comp (fderiv ℝ Φ (Y + z))) z := by
  have h1 : HasFDerivAt (fun z : c13_E => Y + z) (ContinuousLinearMap.id ℝ c13_E) z :=
    (hasFDerivAt_id z).const_add Y
  have h2 := (hΦ (Y + z)).hasFDerivAt.comp z h1
  have h3 := (EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).hasFDerivAt.comp z h2
  rw [ContinuousLinearMap.comp_id] at h3
  exact h3

theorem c13b_aux_shift_coord_fderiv (Φ : c13_E → c13_E) (hΦ : Differentiable ℝ Φ)
    (Y : c13_E) (i : Fin 2) (z v : c13_E) :
    fderiv ℝ (fun z => Φ (Y + z) i) z v = fderiv ℝ Φ (Y + z) v i := by
  rw [(c13b_aux_shift_coord_hasFDerivAt Φ hΦ Y i z).fderiv]
  simp

theorem c13b_aux_shift_support {F : Type*} [Zero F] (Φ : c13_E → F) (hsupp : HasCompactSupport Φ)
    (Y : c13_E) :
    HasCompactSupport (fun z => Φ (Y + z)) := by
  have := hsupp.comp_homeomorph (Homeomorph.addLeft Y)
  exact this

theorem c13b_aux_ibp_one (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ 1 Φ) (hsupp : HasCompactSupport Φ) (Y : c13_E) (i : Fin 2) (v : c13_E) :
    ∫ z, Φ (Y + z) i * fderiv ℝ (c13b_aux_Pd α c δ) z v =
      -∫ z, fderiv ℝ Φ (Y + z) v i * c13b_aux_Pd α c δ z := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable one_ne_zero
  have hcD : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  have hsY := c13b_aux_shift_support Φ hsupp Y
  have hsD : HasCompactSupport (fun z => fderiv ℝ Φ (Y + z)) :=
    c13b_aux_shift_support _ (hsupp.fderiv (𝕜 := ℝ)) Y
  have hPc := c13b_aux_continuous_Pd α c hδ
  have hfi : HasCompactSupport (fun z => Φ (Y + z) i) :=
    hsY.comp_left (g := fun w : c13_E => w i) (by simp)
  have hfd : HasCompactSupport (fun z => fderiv ℝ Φ (Y + z) v i) :=
    hsD.comp_left (g := fun L : c13_E →L[ℝ] c13_E => L v i) (by simp)
  have cfi : Continuous (fun z => Φ (Y + z) i) := by
    have := hΦ.continuous; fun_prop
  have cfd : Continuous (fun z => fderiv ℝ Φ (Y + z) v i) := by fun_prop
  have hfe : (fun z => fderiv ℝ (fun z => Φ (Y + z) i) z v) = fun z => fderiv ℝ Φ (Y + z) v i := by
    ext z; exact c13b_aux_shift_coord_fderiv Φ hd Y i z v
  have i1 : Integrable (fun z => fderiv ℝ (fun z => Φ (Y + z) i) z v * c13b_aux_Pd α c δ z) := by
    simp_rw [c13b_aux_shift_coord_fderiv Φ hd Y i _ v]
    exact (cfd.mul hPc).integrable_of_hasCompactSupport hfd.mul_right
  have i2 : Integrable (fun z => Φ (Y + z) i * fderiv ℝ (c13b_aux_Pd α c δ) z v) :=
    (cfi.mul (c13b_aux_continuous_Pd_fderiv α c hδ v)).integrable_of_hasCompactSupport
      hfi.mul_right
  have i3 : Integrable (fun z => Φ (Y + z) i * c13b_aux_Pd α c δ z) :=
    (cfi.mul hPc).integrable_of_hasCompactSupport hfi.mul_right
  have e := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun z => Φ (Y + z) i) (g := c13b_aux_Pd α c δ) (v := v) i1 i2 i3
    (fun z _ => (c13b_aux_shift_coord_hasFDerivAt Φ hd Y i z).differentiableAt)
    (fun z _ => (c13b_aux_Pd_hasFDerivAt α c hδ z).differentiableAt)
  rw [e]
  have : (fun z => fderiv ℝ (fun z => Φ (Y + z) i) z v * c13b_aux_Pd α c δ z) =
      fun z => fderiv ℝ Φ (Y + z) v i * c13b_aux_Pd α c δ z := by
    simp_rw [c13b_aux_shift_coord_fderiv Φ hd Y i _ v]
  rw [this]


theorem c13b_aux_ibp_integrable (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ 1 Φ) (hsupp : HasCompactSupport Φ) (Y : c13_E) (i : Fin 2) (v : c13_E) :
    Integrable (fun z => Φ (Y + z) i * fderiv ℝ (c13b_aux_Pd α c δ) z v) ∧
      Integrable (fun z => fderiv ℝ Φ (Y + z) v i * c13b_aux_Pd α c δ z) := by
  have hcD : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  have hsY := c13b_aux_shift_support Φ hsupp Y
  have hsD : HasCompactSupport (fun z => fderiv ℝ Φ (Y + z)) :=
    c13b_aux_shift_support _ (hsupp.fderiv (𝕜 := ℝ)) Y
  have hfi : HasCompactSupport (fun z => Φ (Y + z) i) :=
    hsY.comp_left (g := fun w : c13_E => w i) (by simp)
  have hfd : HasCompactSupport (fun z => fderiv ℝ Φ (Y + z) v i) :=
    hsD.comp_left (g := fun L : c13_E →L[ℝ] c13_E => L v i) (by simp)
  have cfi : Continuous (fun z => Φ (Y + z) i) := by
    have := hΦ.continuous; fun_prop
  have cfd : Continuous (fun z => fderiv ℝ Φ (Y + z) v i) := by fun_prop
  exact ⟨(cfi.mul (c13b_aux_continuous_Pd_fderiv α c hδ v)).integrable_of_hasCompactSupport
      hfi.mul_right, (cfd.mul (c13b_aux_continuous_Pd α c hδ)).integrable_of_hasCompactSupport
      hfd.mul_right⟩

theorem c13b_aux_IBP_delta (α c : ℝ) {δ : ℝ} (hδ : 0 < δ) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ 1 Φ) (hsupp : HasCompactSupport Φ) (Y : c13_E) :
    ∫ z, inner ℝ (c13b_aux_Kd α c δ z) (Φ (Y + z)) =
      ∫ z, c13b_aux_Pd α c δ z * c13b_aux_curl Φ (Y + z) := by
  set e0 : c13_E := EuclideanSpace.single 0 1
  set e1 : c13_E := EuclideanSpace.single 1 1
  obtain ⟨a0, b0⟩ := c13b_aux_ibp_integrable α c hδ Φ hΦ hsupp Y 0 e1
  obtain ⟨a1, b1⟩ := c13b_aux_ibp_integrable α c hδ Φ hΦ hsupp Y 1 e0
  have l : (fun z => inner ℝ (c13b_aux_Kd α c δ z) (Φ (Y + z))) = fun z =>
      Φ (Y + z) 0 * fderiv ℝ (c13b_aux_Pd α c δ) z e1 -
        Φ (Y + z) 1 * fderiv ℝ (c13b_aux_Pd α c δ) z e0 := by
    ext z; rw [c13b_aux_Kd_inner α c hδ]; ring
  have r : (fun z => c13b_aux_Pd α c δ z * c13b_aux_curl Φ (Y + z)) = fun z =>
      fderiv ℝ Φ (Y + z) e0 1 * c13b_aux_Pd α c δ z -
        fderiv ℝ Φ (Y + z) e1 0 * c13b_aux_Pd α c δ z := by
    ext z; unfold c13b_aux_curl; ring
  rw [l, r, integral_sub a0 a1, integral_sub b1 b0, c13b_aux_ibp_one α c hδ Φ hΦ hsupp Y 0 e1,
    c13b_aux_ibp_one α c hδ Φ hΦ hsupp Y 1 e0]
  ring


theorem c13b_aux_rotation_neg (z : c13_E) : c13_rotation (-z) = -c13_rotation z := by
  ext i; fin_cases i <;> simp [c13_rotation]

theorem c13b_aux_Kd_neg (α c δ : ℝ) (z : c13_E) : c13b_aux_Kd α c δ (-z) = -c13b_aux_Kd α c δ z := by
  simp [c13b_aux_Kd, c13b_aux_rotation_neg]

theorem c13b_aux_Kd_odd_integral (α c δ : ℝ) (w : c13_E) :
    ∫ z, inner ℝ (c13b_aux_Kd α c δ z) w = 0 := by
  have h := integral_neg_eq_self (fun z => inner ℝ (c13b_aux_Kd α c δ z) w) (volume : Measure c13_E)
  simp only [c13b_aux_Kd_neg, inner_neg_left, integral_neg] at h
  linarith

theorem c13b_aux_norm_Kd (α c δ : ℝ) (z : c13_E) :
    ‖c13b_aux_Kd α c δ z‖ = |α * c| * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1) * ‖z‖ := by
  rw [c13b_aux_Kd, norm_smul, c13b_aux_norm_rotation, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

theorem c13b_aux_sq_rpow (z : c13_E) (p : ℝ) : (‖z‖ ^ 2) ^ p = ‖z‖ ^ (2 * p) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]

theorem c13b_aux_Kd_le_K {α : ℝ} (hα : 0 < α) (c δ : ℝ) (z : c13_E) :
    ‖c13b_aux_Kd α c δ z‖ ≤ ‖c13_velocity_kernel α c z‖ := by
  rw [c13b_aux_norm_Kd, c13b_aux_norm_kernel hα]
  by_cases hz : z = 0
  · subst hz; simp; positivity
  have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 : (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1) ≤ (‖z‖ ^ 2) ^ (-α / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
  rw [c13b_aux_sq_rpow] at h1
  calc |α * c| * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1) * ‖z‖
      ≤ |α * c| * ‖z‖ ^ (2 * (-α / 2 - 1)) * ‖z‖ := by gcongr
    _ = |α * c| * ‖z‖ ^ (-α - 1) := by
        rw [mul_assoc, show 2 * (-α / 2 - 1) = (-α - 1) - 1 by ring, Real.rpow_sub_one ht.ne']
        field_simp

theorem c13b_aux_Pd_le {α : ℝ} (hα : 0 < α) (c δ : ℝ) {z : c13_E} (hz : z ≠ 0) :
    ‖c13b_aux_Pd α c δ z‖ ≤ |c| * ‖z‖ ^ (-α) := by
  have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [c13b_aux_Pd, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have h1 : (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2) ≤ (‖z‖ ^ 2) ^ (-α / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
  rw [c13b_aux_sq_rpow, show 2 * (-α / 2) = -α by ring] at h1
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem c13b_aux_rpow_lim {a : ℝ} (ha : 0 < a) (p : ℝ) :
    Tendsto (fun n : ℕ => (a + (1 / ((n : ℝ) + 1)) ^ 2) ^ p) atTop (𝓝 (a ^ p)) := by
  have h0 : Tendsto (fun n : ℕ => a + (1 / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 a) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    simpa using this.const_add a
  exact (Real.continuousAt_rpow_const a p (Or.inl ha.ne')).tendsto.comp h0

theorem c13b_aux_Kd_lim {α : ℝ} (_hα : 0 < α) (c : ℝ) (z : c13_E) :
    Tendsto (fun n : ℕ => c13b_aux_Kd α c (1 / ((n : ℝ) + 1)) z) atTop
      (𝓝 (c13_velocity_kernel α c z)) := by
  by_cases hz : z = 0
  · subst hz
    have : c13_rotation 0 = 0 := by ext i; fin_cases i <;> simp [c13_rotation]
    simp [c13b_aux_Kd, c13_velocity_kernel, this]
  have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hl := c13b_aux_rpow_lim (by positivity : (0 : ℝ) < ‖z‖ ^ 2) (-α / 2 - 1)
  rw [c13b_aux_sq_rpow, show 2 * (-α / 2 - 1) = -α - 2 by ring] at hl
  simp only [c13b_aux_Kd, c13_velocity_kernel, hz, ite_false]
  exact ((hl.const_mul (α * c)).smul_const (c13_rotation z))

theorem c13b_aux_Pd_lim {α : ℝ} (_hα : 0 < α) (c : ℝ) {z : c13_E} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => c13b_aux_Pd α c (1 / ((n : ℝ) + 1)) z) atTop
      (𝓝 (c13_potential_kernel α c z)) := by
  have hl := c13b_aux_rpow_lim (by positivity : (0 : ℝ) < ‖z‖ ^ 2) (-α / 2)
  rw [c13b_aux_sq_rpow, show 2 * (-α / 2) = -α by ring] at hl
  simp only [c13b_aux_Pd, c13_potential_kernel, hz, ite_false]
  exact hl.const_mul c


theorem c13b_aux_P_locInt {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) :
    LocallyIntegrable (c13_potential_kernel α c) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := |c|) (α := α) (by simp) (by simpa using hα2)
    (Eventually.of_forall fun z => ?_) (c13b_aux_measurable_P α c).aestronglyMeasurable
  rw [Real.norm_eq_abs, c13b_aux_P_abs (by linarith)]

theorem c13b_aux_rpow_locInt {α : ℝ} (hα2 : α < 2) (C : ℝ) :
    LocallyIntegrable (fun z : c13_E => C * ‖z‖ ^ (-α)) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := |C|) (α := α) (by simp) (by simpa using hα2)
    (Eventually.of_forall fun z => ?_)
    (by fun_prop : Measurable fun z : c13_E => C * ‖z‖ ^ (-α)).aestronglyMeasurable
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

theorem c13b_aux_Kd_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (w : c13_E) : Integrable (fun z => inner ℝ (c13b_aux_Kd α c δ z) w) := by
  have hα : 0 < α := by linarith
  obtain ⟨iX, -⟩ := (c13_radial_majorants hα1 hα2 c).2.2.2.1 1 one_pos
  have hms : MeasurableSet {z : c13_E | 1 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  have g2 : Integrable ((Metric.closedBall (0 : c13_E) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)
  have g3 := (integrable_indicator_iff hms).2 iX
  have hmaj : Integrable (fun z => (|α * c| * (δ ^ (-α - 2) *
      (Metric.closedBall (0 : c13_E) 1).indicator (fun _ => (1 : ℝ)) z +
      {z : c13_E | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-α - 1)) z)) * ‖w‖) :=
    (((g2.const_mul _).add g3).const_mul _).mul_const _
  refine hmaj.mono' ((c13b_aux_continuous_Kd α c hδ).inner continuous_const).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  by_cases hz : ‖z‖ ≤ 1
  · rw [indicator_of_mem (by simpa using hz), indicator_of_notMem (by simpa using hz), add_zero,
      mul_one, c13b_aux_norm_Kd]
    have h1 : (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1) ≤ (δ ^ 2) ^ (-α / 2 - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
    have h2 : (δ ^ 2) ^ (-α / 2 - 1) = δ ^ (-α - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hδ.le]; ring_nf
    rw [h2] at h1
    calc |α * c| * (‖z‖ ^ 2 + δ ^ 2) ^ (-α / 2 - 1) * ‖z‖ ≤ |α * c| * δ ^ (-α - 2) * 1 := by
          gcongr
      _ = _ := by ring
  · push Not at hz
    rw [indicator_of_notMem (by simpa using hz), indicator_of_mem (show z ∈ {z : c13_E | 1 < ‖z‖} from hz),
      mul_zero, zero_add, ← c13b_aux_norm_kernel hα]
    exact c13b_aux_Kd_le_K hα c δ z


theorem c13b_aux_ae_ne_zero : ∀ᵐ z : c13_E ∂volume, z ≠ 0 := by
  rw [ae_iff]; simp [measure_singleton]

theorem c13b_aux_curl_continuous (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ 1 Φ) :
    Continuous (c13b_aux_curl Φ) := by
  have := hΦ.continuous_fderiv one_ne_zero
  unfold c13b_aux_curl; fun_prop

theorem c13b_aux_curl_support (Φ : c13_E → c13_E) (hsupp : HasCompactSupport Φ) :
    HasCompactSupport (c13b_aux_curl Φ) :=
  (hsupp.fderiv (𝕜 := ℝ)).comp_left
    (g := fun L : c13_E →L[ℝ] c13_E => L (EuclideanSpace.single 0 1) 1 - L (EuclideanSpace.single 1 1) 0)
    (by simp)

/-- Core identity: `B*Φ(Y) = ∫ P(z) curl Φ(Y + z) dz`, by `δ`-regularization of the kernel,
whole-space integration by parts, and dominated convergence (the cancellation `Φ(Y+z) - Φ(Y)`
is kept until the limit). -/
theorem c13b_aux_adjoint_curl {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsupp : HasCompactSupport Φ) (Y : c13_E) :
    c13_adjoint α c Φ Y = ∫ z, c13_potential_kernel α c z * c13b_aux_curl Φ (Y + z) := by
  have hα : 0 < α := by linarith
  have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  have hδ : ∀ n, 0 < δ n := fun n => by simp only [hδdef]; positivity
  have hsY := c13b_aux_shift_support Φ hsupp Y
  have cY : Continuous (fun z => Φ (Y + z)) := by have := hΦ.continuous; fun_prop
  -- the regularized identity
  have seq : ∀ n, ∫ z, inner ℝ (c13b_aux_Kd α c (δ n) z) (Φ (Y + z) - Φ Y) =
      ∫ z, c13b_aux_Pd α c (δ n) z * c13b_aux_curl Φ (Y + z) := by
    intro n
    have iA : Integrable (fun z => inner ℝ (c13b_aux_Kd α c (δ n) z) (Φ (Y + z))) := by
      refine ((c13b_aux_continuous_Kd α c (hδ n)).inner cY).integrable_of_hasCompactSupport ?_
      exact hsY.mono (fun z hz => by
        simp only [Function.mem_support] at hz ⊢
        intro h; apply hz; rw [h, inner_zero_right])
    simp_rw [inner_sub_right]
    rw [integral_sub iA (c13b_aux_Kd_integrable hα1 hα2 c (hδ n) (Φ Y)),
      c13b_aux_Kd_odd_integral, sub_zero, c13b_aux_IBP_delta α c (hδ n) Φ h1 hsupp Y]
  -- limit of the left side
  obtain ⟨L, S, hL, hS, hLS⟩ := c13b_aux_test_bounds Φ hΦ hsupp
  have limL : Tendsto (fun n => ∫ z, inner ℝ (c13b_aux_Kd α c (δ n) z) (Φ (Y + z) - Φ Y))
      atTop (𝓝 (c13_adjoint α c Φ Y)) := by
    refine tendsto_integral_of_dominated_convergence (c13b_aux_G α c L (2 * S))
      (fun n => ((c13b_aux_continuous_Kd α c (hδ n)).inner
        (cY.sub continuous_const)).aestronglyMeasurable)
      (c13b_aux_G_integrable hα1 hα2 c L (2 * S)).1 (fun n => ?_) ?_
    · filter_upwards [c13b_aux_kernel_dom hα1 c hL (by positivity)
        (fun z => ‖Φ (Y + z) - Φ Y‖) (fun z => ⟨norm_nonneg _, (hLS Y z).1, (hLS Y z).2⟩)] with z hz
      refine (norm_inner_le_norm _ _).trans (le_trans ?_ hz)
      exact mul_le_mul_of_nonneg_right (c13b_aux_Kd_le_K hα c _ z) (norm_nonneg _)
    · exact Eventually.of_forall fun z => (c13b_aux_Kd_lim hα c z).inner tendsto_const_nhds
  -- limit of the right side
  have hcc := c13b_aux_curl_continuous Φ h1
  have hcs : HasCompactSupport (fun z => c13b_aux_curl Φ (Y + z)) :=
    c13b_aux_shift_support _ (c13b_aux_curl_support Φ hsupp) Y
  have hcY : Continuous (fun z => c13b_aux_curl Φ (Y + z)) := by fun_prop
  have ib : Integrable (fun z => |c13b_aux_curl Φ (Y + z)| • (|c| * ‖z‖ ^ (-α))) :=
    (c13b_aux_rpow_locInt hα2 |c|).integrable_smul_left_of_hasCompactSupport
      hcY.abs hcs.abs
  have limR : Tendsto (fun n => ∫ z, c13b_aux_Pd α c (δ n) z * c13b_aux_curl Φ (Y + z))
      atTop (𝓝 (∫ z, c13_potential_kernel α c z * c13b_aux_curl Φ (Y + z))) := by
    refine tendsto_integral_of_dominated_convergence _
      (fun n => ((c13b_aux_continuous_Pd α c (hδ n)).mul hcY).aestronglyMeasurable) ib
      (fun n => ?_) ?_
    · filter_upwards [c13b_aux_ae_ne_zero] with z hz
      rw [norm_mul, smul_eq_mul, mul_comm |c13b_aux_curl Φ (Y + z)|, Real.norm_eq_abs (c13b_aux_curl _ _)]
      exact mul_le_mul_of_nonneg_right (c13b_aux_Pd_le hα c _ hz) (abs_nonneg _)
    · filter_upwards [c13b_aux_ae_ne_zero] with z hz
      exact (c13b_aux_Pd_lim hα c hz).mul_const _
  have := tendsto_nhds_unique (limL.congr seq) limR
  exact this


theorem c13b_aux_P_neg (α c : ℝ) (z : c13_E) : c13_potential_kernel α c (-z) = c13_potential_kernel α c z := by
  simp [c13_potential_kernel]

/-- The rotation as a continuous linear map. -/
def c13b_aux_rotL : c13_E →L[ℝ] c13_E :=
  LinearMap.toContinuousLinearMap
    { toFun := c13_rotation
      map_add' := fun x y => by ext i; fin_cases i <;> simp [c13_rotation]; ring
      map_smul' := fun a x => by ext i; fin_cases i <;> simp [c13_rotation] }

theorem c13b_aux_rotL_apply (z : c13_E) : c13b_aux_rotL z = c13_rotation z := rfl

theorem c13b_aux_conv_eq (α c : ℝ) (Φ : c13_E → c13_E) (Y : c13_E) :
    (∫ X, c13_potential_kernel α c (X - Y) • Φ X) =
      convolution (c13_potential_kernel α c) Φ (ContinuousLinearMap.lsmul ℝ ℝ) volume Y := by
  rw [convolution_def, ← integral_sub_left_eq_self (fun X => c13_potential_kernel α c (X - Y) • Φ X)
    volume Y]
  congr 1; ext t
  simp only [ContinuousLinearMap.lsmul_apply, sub_sub_cancel_left, c13b_aux_P_neg]

theorem c13b_aux_conv_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ)
    (Φ : c13_E → c13_E) (hΦ : Continuous Φ) (hsupp : HasCompactSupport Φ) (Y : c13_E) :
    Integrable (fun X => c13_potential_kernel α c (X - Y) • Φ X) := by
  have h := hsupp.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (c13b_aux_P_locInt hα1 hα2 c) hΦ Y
  have h2 := h.comp_sub_left Y
  refine h2.congr (Eventually.of_forall fun X => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, sub_sub_cancel]
  rw [← c13b_aux_P_neg, neg_sub]


theorem c13b_aux_A_eq (α c : ℝ) (Φ : c13_E → c13_E) :
    (fun W => ∫ X, c13_potential_kernel α c (X - W) • Φ X) =
      convolution (c13_potential_kernel α c) Φ (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext W; exact c13b_aux_conv_eq α c Φ W

theorem c13b_aux_A_partial {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ 1 Φ) (hsupp : HasCompactSupport Φ) (Y v : c13_E) (i : Fin 2) :
    HasFDerivAt (fun W => ∫ X, c13_potential_kernel α c (X - W) • Φ X)
      (convolution (c13_potential_kernel α c) (fderiv ℝ Φ)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR c13_E) volume Y) Y ∧
    Integrable (fun t => c13_potential_kernel α c t * fderiv ℝ Φ (Y - t) v i) ∧
    fderiv ℝ (fun W => ∫ X, c13_potential_kernel α c (X - W) • Φ X) Y v i =
      ∫ t, c13_potential_kernel α c t * fderiv ℝ Φ (Y - t) v i := by
  have hloc := c13b_aux_P_locInt hα1 hα2 c
  have hcD : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  have hsD : HasCompactSupport (fderiv ℝ Φ) := hsupp.fderiv (𝕜 := ℝ)
  have hD : HasFDerivAt (fun W => ∫ X, c13_potential_kernel α c (X - W) • Φ X)
      (convolution (c13_potential_kernel α c) (fderiv ℝ Φ)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR c13_E) volume Y) Y := by
    rw [c13b_aux_A_eq]
    exact hsupp.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hloc hΦ Y
  have hgv : Continuous (fun a => fderiv ℝ Φ a v) := by fun_prop
  have hgs : HasCompactSupport (fun a => fderiv ℝ Φ a v) :=
    hsD.comp_left (g := fun L : c13_E →L[ℝ] c13_E => L v) (by simp)
  have hex := hgs.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hloc hgv Y
  have hex' : Integrable (fun t => c13_potential_kernel α c t • fderiv ℝ Φ (Y - t) v) := hex
  have hint : Integrable (fun t => c13_potential_kernel α c t * fderiv ℝ Φ (Y - t) v i) := by
    have := (EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).integrable_comp hex'
    simpa using this
  refine ⟨hD, hint, ?_⟩
  rw [hD.fderiv, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hloc hsD hcD Y v,
    convolution_def]
  have := (EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).integral_comp_comm hex'
  simp only [ContinuousLinearMap.lsmul_apply]
  simp only [map_smul, smul_eq_mul] at this
  exact this.symm


theorem c13b_aux_divJA {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ 1 Φ) (hsupp : HasCompactSupport Φ) (Y : c13_E) :
    -(fderiv ℝ (fun W : c13_E => c13_rotation (∫ X, c13_potential_kernel α c (X - W) • Φ X))
          Y (EuclideanSpace.single 0 1) 0 +
        fderiv ℝ (fun W : c13_E => c13_rotation (∫ X, c13_potential_kernel α c (X - W) • Φ X))
          Y (EuclideanSpace.single 1 1) 1) =
      ∫ z, c13_potential_kernel α c z * c13b_aux_curl Φ (Y + z) := by
  set e0 : c13_E := EuclideanSpace.single 0 1
  set e1 : c13_E := EuclideanSpace.single 1 1
  obtain ⟨hD, i0, v0⟩ := c13b_aux_A_partial hα1 hα2 c Φ hΦ hsupp Y e0 1
  obtain ⟨-, i1, v1⟩ := c13b_aux_A_partial hα1 hα2 c Φ hΦ hsupp Y e1 0
  have hJ : ∀ v, fderiv ℝ (fun W : c13_E => c13_rotation (∫ X, c13_potential_kernel α c (X - W) • Φ X))
      Y v = c13_rotation (fderiv ℝ (fun W => ∫ X, c13_potential_kernel α c (X - W) • Φ X) Y v) := by
    intro v
    have := (c13b_aux_rotL.hasFDerivAt.comp Y hD)
    rw [show (fun W : c13_E => c13_rotation (∫ X, c13_potential_kernel α c (X - W) • Φ X)) =
      c13b_aux_rotL ∘ (fun W => ∫ X, c13_potential_kernel α c (X - W) • Φ X) from rfl, this.fderiv,
      hD.fderiv]
    rfl
  rw [hJ, hJ, (c13b_aux_rotation_apply _).1, (c13b_aux_rotation_apply _).2, v0, v1]
  have e : -(-(∫ t, c13_potential_kernel α c t * fderiv ℝ Φ (Y - t) e0 1) +
      ∫ t, c13_potential_kernel α c t * fderiv ℝ Φ (Y - t) e1 0) =
      ∫ t, c13_potential_kernel α c t * c13b_aux_curl Φ (Y - t) := by
    rw [neg_add, neg_neg, ← sub_eq_add_neg, ← integral_sub i0 i1]
    congr 1; ext t; unfold c13b_aux_curl; ring
  rw [e, ← integral_neg_eq_self]
  congr 1; ext z
  rw [c13b_aux_P_neg, sub_neg_eq_add]


theorem c13b_aux_A_decay {α : ℝ} (hα1 : 1 < α) (c : ℝ) (Φ : c13_E → c13_E)
    (hΦ : Continuous Φ) (hsupp : HasCompactSupport Φ) (L : ℝ) (hL : 0 ≤ L)
    (hsL : tsupport Φ ⊆ Metric.closedBall 0 L) (Y : c13_E) (hY : 2 * L + 1 < ‖Y‖) :
    ‖∫ X, c13_potential_kernel α c (X - Y) • Φ X‖ ≤
      (|c| * 2 ^ α + 1) * ‖Y‖ ^ (-α) * ∫ X, ‖Φ X‖ := by
  have hα : 0 < α := by linarith
  have hY0 : 0 < ‖Y‖ := by linarith
  have iΦ : Integrable (fun X => ‖Φ X‖) := (hΦ.integrable_of_hasCompactSupport hsupp).norm
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (iΦ.const_mul _) (Eventually.of_forall fun X => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hX : X ∈ tsupport Φ
  · have hXL : ‖X‖ ≤ L := by simpa using hsL hX
    have h1 : ‖Y‖ / 2 ≤ ‖X - Y‖ := by
      have := norm_sub_norm_le Y X
      rw [norm_sub_rev] at this
      linarith
    have h2 : ‖X - Y‖ ^ (-α) ≤ (‖Y‖ / 2) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    have h3 : (‖Y‖ / 2) ^ (-α) = 2 ^ α * ‖Y‖ ^ (-α) := by
      rw [Real.div_rpow hY0.le zero_le_two, Real.rpow_neg zero_le_two]; field_simp
    rw [c13b_aux_P_abs hα]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc |c| * ‖X - Y‖ ^ (-α) ≤ |c| * (2 ^ α * ‖Y‖ ^ (-α)) :=
          mul_le_mul_of_nonneg_left (h2.trans_eq h3) (abs_nonneg _)
      _ ≤ (|c| * 2 ^ α + 1) * ‖Y‖ ^ (-α) := by
          have : 0 ≤ ‖Y‖ ^ (-α) := Real.rpow_nonneg hY0.le _
          nlinarith
  · rw [image_eq_zero_of_notMem_tsupport hX, norm_zero, mul_zero, mul_zero]

theorem c13b_aux_grad_coord (ζ : c13_E → ℝ) (W : c13_E) (i : Fin 2) :
    gradient ζ W i = fderiv ℝ ζ W (EuclideanSpace.single i 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := c13_E) (x := EuclideanSpace.single i 1)
    (y := fderiv ℝ ζ W)
  rw [real_inner_comm, EuclideanSpace.inner_single_left] at h
  simpa [gradient] using h

theorem c13b_aux_dual_coord (φ : StrongDual ℝ c13_E) (i : Fin 2) :
    (InnerProductSpace.toDual ℝ c13_E).symm φ i = φ (EuclideanSpace.single i 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := c13_E) (x := EuclideanSpace.single i 1)
    (y := φ)
  rw [real_inner_comm, EuclideanSpace.inner_single_left] at h
  simpa using h

theorem c13b_aux_grad_smooth (ζ : c13_E → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hs : HasCompactSupport ζ) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient ζ) ∧ HasCompactSupport (gradient ζ) := by
  set T : StrongDual ℝ c13_E →L[ℝ] c13_E :=
    (InnerProductSpace.toDual ℝ c13_E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg : gradient ζ = fun W => T (fderiv ℝ ζ W) := rfl
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact T.contDiff.comp (hζ.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
  · rw [hg]
    exact (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun φ => T φ) (by simp)

theorem c13b_aux_curl_grad (ζ : c13_E → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (W : c13_E) :
    c13b_aux_curl (gradient ζ) W = 0 := by
  set T : StrongDual ℝ c13_E →L[ℝ] c13_E :=
    (InnerProductSpace.toDual ℝ c13_E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg : gradient ζ = fun W => T (fderiv ℝ ζ W) := rfl
  have hd : Differentiable ℝ (fderiv ℝ ζ) :=
    (hζ.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  have hD : ∀ v, fderiv ℝ (gradient ζ) W v = T (fderiv ℝ (fderiv ℝ ζ) W v) := by
    intro v
    have h := (T.hasFDerivAt.comp W (hd W).hasFDerivAt)
    rw [hg]
    change fderiv ℝ (T ∘ fderiv ℝ ζ) W v = _
    rw [h.fderiv]; rfl
  have hsym := (hζ.contDiffAt (x := W)).isSymmSndFDerivAt (by simp)
  unfold c13b_aux_curl
  rw [hD, hD]
  change (InnerProductSpace.toDual ℝ c13_E).symm _ 1 - (InnerProductSpace.toDual ℝ c13_E).symm _ 0 = 0
  rw [c13b_aux_dual_coord, c13b_aux_dual_coord, hsym]
  ring


/-- Blueprint: lem:c13_test_potential.  The test potential `A_Φ(Y) = ∫ P(X - Y) Φ(X) dX`
converges absolutely, is `C¹`, satisfies `B*Φ = -div(J A_Φ)` pointwise, and decays like
`C |Y|^{-α} ‖Φ‖₁` for `|Y| > 2L + 1` when `supp Φ ⊆ {|X| ≤ L}` (`C` chosen before `Φ` and `L`).
Moreover `B*(∇ζ) = 0` for every scalar test `ζ`. -/
theorem c13_test_potential {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    (∀ Φ : c13_E → c13_E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      (∀ Y : c13_E, Integrable (fun X : c13_E => c13_potential_kernel α c (X - Y) • Φ X)) ∧
      ContDiff ℝ 1 (fun Y : c13_E => ∫ X, c13_potential_kernel α c (X - Y) • Φ X) ∧
      (∀ Y : c13_E, c13_adjoint α c Φ Y =
        -(fderiv ℝ (fun W : c13_E => c13_rotation (∫ X, c13_potential_kernel α c (X - W) • Φ X))
              Y (EuclideanSpace.single 0 1) 0 +
          fderiv ℝ (fun W : c13_E => c13_rotation (∫ X, c13_potential_kernel α c (X - W) • Φ X))
              Y (EuclideanSpace.single 1 1) 1)) ∧
      ∀ L : ℝ, 0 ≤ L → tsupport Φ ⊆ Metric.closedBall 0 L →
        ∀ Y : c13_E, 2 * L + 1 < ‖Y‖ →
          ‖∫ X, c13_potential_kernel α c (X - Y) • Φ X‖ ≤ C * ‖Y‖ ^ (-α) * ∫ X, ‖Φ X‖) ∧
    (∀ ζ : c13_E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      ∀ Y : c13_E, c13_adjoint α c (gradient ζ) Y = 0) := by
  refine ⟨|c| * 2 ^ α + 1, by positivity, fun Φ hΦ hsupp => ?_, fun ζ hζ hs Y => ?_⟩
  · have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
    refine ⟨c13b_aux_conv_integrable hα1 hα2 c Φ hΦ.continuous hsupp, ?_, fun Y => ?_,
      fun L hL hsL Y hY => c13b_aux_A_decay hα1 c Φ hΦ.continuous hsupp L hL hsL Y hY⟩
    · rw [c13b_aux_A_eq]
      exact hsupp.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
        (c13b_aux_P_locInt hα1 hα2 c) h1
    · rw [c13b_aux_divJA hα1 hα2 c Φ h1 hsupp Y, c13b_aux_adjoint_curl hα1 hα2 c Φ hΦ hsupp Y]
  · obtain ⟨hg, hgs⟩ := c13b_aux_grad_smooth ζ hζ hs
    rw [c13b_aux_adjoint_curl hα1 hα2 c _ hg hgs Y]
    simp [c13b_aux_curl_grad ζ hζ]

/-! ### lem:c13_renormalized_potential -/

theorem c13b_aux_integral_partial_zero (g : c13_E → ℝ) (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (v : c13_E) : ∫ X, fderiv ℝ g X v = 0 := by
  have hc := hg.continuous_fderiv one_ne_zero
  have hgv : Continuous (fun X => fderiv ℝ g X v) := by fun_prop
  have hsv : HasCompactSupport (fun X => fderiv ℝ g X v) :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : c13_E →L[ℝ] ℝ => L v) (by simp)
  have e := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : c13_E => (1 : ℝ)) (g := g) (v := v) (by simp)
    (by simpa using hgv.integrable_of_hasCompactSupport hsv)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ => differentiableAt_const _) (fun x _ => (hg.differentiable one_ne_zero) x)
  simpa using e

theorem c13b_aux_coord_fderiv (Φ : c13_E → c13_E) (hd : Differentiable ℝ Φ) (i : Fin 2)
    (X v : c13_E) : fderiv ℝ (fun W => Φ W i) X v = fderiv ℝ Φ X v i := by
  have h := (EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).hasFDerivAt.comp X (hd X).hasFDerivAt
  change fderiv ℝ ((EuclideanSpace.proj i : c13_E →L[ℝ] ℝ) ∘ Φ) X v = _
  rw [h.fderiv]; simp

theorem c13b_aux_integral_curl_zero (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ 1 Φ)
    (hsupp : HasCompactSupport Φ) : ∫ X, c13b_aux_curl Φ X = 0 := by
  have hd := hΦ.differentiable one_ne_zero
  have hc := hΦ.continuous_fderiv one_ne_zero
  have gi : ∀ i : Fin 2, ContDiff ℝ 1 (fun W => Φ W i) ∧ HasCompactSupport (fun W => Φ W i) :=
    fun i => ⟨(EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).contDiff.comp hΦ,
      hsupp.comp_left (g := fun w : c13_E => w i) (by simp)⟩
  have z1 := c13b_aux_integral_partial_zero _ (gi 1).1 (gi 1).2 (EuclideanSpace.single 0 1)
  have z0 := c13b_aux_integral_partial_zero _ (gi 0).1 (gi 0).2 (EuclideanSpace.single 1 1)
  simp_rw [c13b_aux_coord_fderiv Φ hd] at z0 z1
  have hs := c13b_aux_curl_support Φ hsupp
  have i1 : Integrable (fun X => fderiv ℝ Φ X (EuclideanSpace.single 0 1) 1) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : c13_E →L[ℝ] c13_E => L _ 1) (by simp)
  have i0 : Integrable (fun X => fderiv ℝ Φ X (EuclideanSpace.single 1 1) 0) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : c13_E →L[ℝ] c13_E => L _ 0) (by simp)
  unfold c13b_aux_curl
  rw [integral_sub i1 i0, z1, z0, sub_zero]

theorem c13b_aux_divJ_eq (Φ : c13_E → c13_E) (hd : Differentiable ℝ Φ) (X : c13_E) :
    fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
        fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1 =
      -c13b_aux_curl Φ X := by
  have hJ : ∀ v, fderiv ℝ (fun W => c13_rotation (Φ W)) X v = c13_rotation (fderiv ℝ Φ X v) := by
    intro v
    have h := c13b_aux_rotL.hasFDerivAt.comp X (hd X).hasFDerivAt
    change fderiv ℝ (c13b_aux_rotL ∘ Φ) X v = _
    rw [h.fderiv]; rfl
  rw [hJ, hJ, (c13b_aux_rotation_apply _).1, (c13b_aux_rotation_apply _).2]
  unfold c13b_aux_curl; ring


theorem c13b_aux_adjoint_translate {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ)
    (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsupp : HasCompactSupport Φ) (Y : c13_E) :
    Integrable (fun X => c13_potential_kernel α c (X - Y) * c13b_aux_curl Φ X) ∧
      c13_adjoint α c Φ Y = ∫ X, c13_potential_kernel α c (X - Y) * c13b_aux_curl Φ X := by
  have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
  have hcc := c13b_aux_curl_continuous Φ h1
  have hcs : HasCompactSupport (fun z => c13b_aux_curl Φ (Y + z)) :=
    c13b_aux_shift_support _ (c13b_aux_curl_support Φ hsupp) Y
  have hcY : Continuous (fun z => c13b_aux_curl Φ (Y + z)) := by fun_prop
  have ig : Integrable (fun z => c13b_aux_curl Φ (Y + z) • c13_potential_kernel α c z) :=
    (c13b_aux_P_locInt hα1 hα2 c).integrable_smul_left_of_hasCompactSupport hcY hcs
  refine ⟨(ig.comp_sub_right Y).congr (Eventually.of_forall fun X => ?_), ?_⟩
  · simp only [smul_eq_mul, add_sub_cancel]; ring
  · rw [c13b_aux_adjoint_curl hα1 hα2 c Φ hΦ hsupp Y,
      ← integral_add_left_eq_self (fun X => c13_potential_kernel α c (X - Y) * c13b_aux_curl Φ X) Y]
    simp only [add_sub_cancel_left]

/-- The Fubini step, with the renormalization subtraction kept inside the double integral. -/
theorem c13b_aux_pairing {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ)
    (θ : c13_E → ℝ) (hθ : Measurable θ) (M : ℝ) (hM : ∀ Y, |θ Y| ≤ M)
    (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hsupp : HasCompactSupport Φ) :
    Integrable (fun X => c13_renormalized_potential α c θ X * c13b_aux_curl Φ X) ∧
      (∫ Y, θ Y * c13_adjoint α c Φ Y) =
        ∫ X, c13_renormalized_potential α c θ X * c13b_aux_curl Φ X := by
  have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
  have hcc := c13b_aux_curl_continuous Φ h1
  have hcs := c13b_aux_curl_support Φ hsupp
  have hci : Integrable (c13b_aux_curl Φ) := hcc.integrable_of_hasCompactSupport hcs
  obtain ⟨R0, hR0⟩ := (hcs.isCompact.isBounded).subset_closedBall (0 : c13_E)
  set R := max R0 1
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hout : ∀ X : c13_E, R < ‖X‖ → c13b_aux_curl Φ X = 0 := by
    intro X hX
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have := hR0 h
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R0 1]
  obtain ⟨hint, -, -⟩ := c13b_aux_V_basic hα1 hα2 c θ hθ M hM
  set F : c13_E × c13_E → ℝ := fun p => c13b_aux_k α c 1 p.1 p.2 * θ p.2 * c13b_aux_curl Φ p.1
  have hFm : Measurable F :=
    ((c13b_aux_measurable_k α c 1).mul (hθ.comp measurable_snd)).mul
      (hcc.measurable.comp measurable_fst)
  have hF : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun X => ?_, ?_⟩
    · show Integrable (fun Y => c13b_aux_k α c 1 X Y * θ Y * c13b_aux_curl Φ X)
      exact (hint X).mul_const _
    refine (hci.norm.const_mul (c13b_aux_mint α c R * M)).mono'
      hFm.norm.aestronglyMeasurable.integral_prod_right' (Eventually.of_forall fun X => ?_)
    have e : ∫ Y, ‖F (X, Y)‖ = (∫ Y, |c13b_aux_k α c 1 X Y| * |θ Y|) * |c13b_aux_curl Φ X| := by
      rw [← integral_mul_const]; congr 1; ext Y
      simp only [F, Real.norm_eq_abs, abs_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e,
      Real.norm_eq_abs]
    by_cases hX : ‖X‖ ≤ R
    · exact mul_le_mul_of_nonneg_right
        (c13b_aux_k_bound hα1 hα2 c hR θ hθ M hM X hX).2 (abs_nonneg _)
    · rw [hout X (not_le.1 hX), abs_zero, mul_zero, mul_zero]
  have inner : ∀ Y, ∫ X, F (X, Y) = θ Y * c13_adjoint α c Φ Y := by
    intro Y
    obtain ⟨iP, eP⟩ := c13b_aux_adjoint_translate hα1 hα2 c Φ hΦ hsupp Y
    have e : (fun X => F (X, Y)) = fun X => θ Y * (c13_potential_kernel α c (X - Y) *
        c13b_aux_curl Φ X - (if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0) *
          c13b_aux_curl Φ X) := by
      ext X; simp only [F, c13b_aux_k]; ring
    rw [e, integral_const_mul, integral_sub iP (hci.const_mul _), integral_const_mul,
      c13b_aux_integral_curl_zero Φ h1 hsupp, mul_zero, sub_zero, ← eP]
  have hVc : ∀ X, ∫ Y, F (X, Y) = c13_renormalized_potential α c θ X * c13b_aux_curl Φ X := by
    intro X
    simp only [F]; rw [integral_mul_const]; rfl
  refine ⟨hF.integral_prod_left.congr (Eventually.of_forall hVc), ?_⟩
  calc (∫ Y, θ Y * c13_adjoint α c Φ Y) = ∫ Y, ∫ X, F (X, Y) := by simp_rw [inner]
    _ = ∫ X, ∫ Y, F (X, Y) := (integral_integral_swap (f := fun X Y => F (X, Y)) hF).symm
    _ = _ := by simp_rw [hVc]


/-- Blueprint: lem:c13_renormalized_potential.  For bounded measurable `θ`: the defining integral
of `V[θ]` converges absolutely everywhere, `V[θ]` is measurable and locally bounded; for every
vector test `Φ`, `∫ θ B*Φ = -∫ V[θ] div(JΦ)` with both integrands integrable (the distributional
identity `Bθ = -J∇V[θ]`); and for every subtraction radius `ρ > 0` the modified potential
converges absolutely, differs from `V[θ]` by a constant, and has the same pairing with every
`div(JΦ)` (the velocity is unchanged). -/
theorem c13_renormalized_potential_properties {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ)
    (θ : c13_E → ℝ) (hθ : Measurable θ) (M : ℝ) (hM : ∀ Y, |θ Y| ≤ M) :
    (∀ X : c13_E, Integrable (fun Y => (c13_potential_kernel α c (X - Y) -
        (if 1 < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y)) ∧
    Measurable (c13_renormalized_potential α c θ) ∧
    (∀ R : ℝ, ∃ B : ℝ, ∀ X : c13_E, ‖X‖ ≤ R → |c13_renormalized_potential α c θ X| ≤ B) ∧
    (∀ Φ : c13_E → c13_E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      Integrable (fun Y => θ Y * c13_adjoint α c Φ Y) ∧
      Integrable (fun X => c13_renormalized_potential α c θ X *
        (fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
          fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1)) ∧
      (∫ Y, θ Y * c13_adjoint α c Φ Y) =
        -∫ X, c13_renormalized_potential α c θ X *
          (fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
            fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1)) ∧
    (∀ ρ : ℝ, 0 < ρ →
      (∀ X : c13_E, Integrable (fun Y => (c13_potential_kernel α c (X - Y) -
          (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y)) ∧
      ∃ k : ℝ,
        (∀ X : c13_E, (∫ Y, (c13_potential_kernel α c (X - Y) -
          (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y) =
          c13_renormalized_potential α c θ X + k) ∧
        ∀ Φ : c13_E → c13_E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
          (∫ X, (∫ Y, (c13_potential_kernel α c (X - Y) -
              (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y) *
            (fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
              fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1)) =
          ∫ X, c13_renormalized_potential α c θ X *
            (fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
              fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1)) := by
  obtain ⟨hint, hmeas, hloc⟩ := c13b_aux_V_basic hα1 hα2 c θ hθ M hM
  -- the pairing with `div (J Φ) = -curl Φ`
  have pair : ∀ Φ : c13_E → c13_E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      Integrable (fun Y => θ Y * c13_adjoint α c Φ Y) ∧
      Integrable (fun X => c13_renormalized_potential α c θ X *
        (fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
          fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1)) ∧
      (∫ Y, θ Y * c13_adjoint α c Φ Y) =
        -∫ X, c13_renormalized_potential α c θ X *
          (fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 0 1) 0 +
            fderiv ℝ (fun W => c13_rotation (Φ W)) X (EuclideanSpace.single 1 1) 1) := by
    intro Φ hΦ hsupp
    have hd : Differentiable ℝ Φ := (hΦ.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 Φ).differentiable one_ne_zero
    obtain ⟨C, -, hC⟩ := c13_adjoint_integrable hα1 hα2 c
    obtain ⟨iV, eV⟩ := c13b_aux_pairing hα1 hα2 c θ hθ M hM Φ hΦ hsupp
    simp_rw [c13b_aux_divJ_eq Φ hd]
    refine ⟨(hC Φ hΦ hsupp).2.2.2.2 θ hθ M hM, ?_, ?_⟩
    · simpa [mul_neg] using iV.neg
    · simp_rw [mul_neg]; rw [integral_neg, neg_neg, eV]
  refine ⟨hint, hmeas, hloc, pair, fun ρ hρ => ?_⟩
  obtain ⟨hintρ, k, hk⟩ := c13b_aux_V_radius hα1 hα2 c hρ θ hθ M hM
  refine ⟨hintρ, k, hk, fun Φ hΦ hsupp => ?_⟩
  have h1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast le_top)
  have hd : Differentiable ℝ Φ := h1.differentiable one_ne_zero
  obtain ⟨-, iV, -⟩ := pair Φ hΦ hsupp
  have hk' : ∀ X, (∫ Y, (c13_potential_kernel α c (X - Y) -
      (if ρ < ‖Y‖ then c13_potential_kernel α c (-Y) else 0)) * θ Y) =
      c13_renormalized_potential α c θ X + k := hk
  simp_rw [hk']
  simp_rw [c13b_aux_divJ_eq Φ hd] at iV ⊢
  have ic : Integrable (fun X => k * -c13b_aux_curl Φ X) :=
    ((c13b_aux_curl_continuous Φ h1).integrable_of_hasCompactSupport
      (c13b_aux_curl_support Φ hsupp)).neg.const_mul k
  simp_rw [add_mul]
  rw [integral_add iV ic, integral_const_mul, integral_neg, c13b_aux_integral_curl_zero Φ h1 hsupp]
  simp

end GSQG
