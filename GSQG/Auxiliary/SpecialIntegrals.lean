import Mathlib

/-!
# Special integrals not (yet) in Mathlib

Reusable, project-independent results (namespace `GSQG.Lib`, imports only Mathlib):

* Laplace transforms `∫_0^∞ e^{-ts}`, `∫_0^∞ cos s e^{-ts}`, `∫_0^∞ (1-cos s) e^{-ts}`.
* `integral_rpow_div_one_add_sq`: `∫_0^∞ t^{p-1}/(1+t²) dt = π/(2 sin(πp/2))`, `0<p<2`.
* `integral_one_sub_cos_mul_rpow`: `∫_0^∞ (1-cos s) s^{-1-p} ds = π/(2Γ(1+p) sin(πp/2))`, `0<p<2`,
  and `integral_one_sub_cos_mul_rpow_eq_Gamma_cos` (`= Γ(1-p)cos(πp/2)/p` for `0<p<1`).
* Scaled / whole-line versions `integral_one_sub_cos_mul_rpow_scale`,
  `integral_one_sub_cos_mul_abs_rpow` (the symbol `|ξ|^p` of `|D|^p`).
* `integral_one_sub_cos_div_sq`, `integral_sin_sq_div_sq` (`= π/2`), and the Dirichlet integral
  `tendsto_integral_sin_div` (`∫_0^R sin x/x → π/2`).
* Fourier transform with the convention `ĝ(ξ) = ∫ g(x) e^{-ixξ} dx`:
  `integral_mul_exp_neg_I_eq_fourier` (link to Mathlib's `𝓕`), `schwartz_fourier_inversion`,
  `integral_deriv_mul_exp_neg_I` (`(g')^ = iξ ĝ`).
* `integral_corr_symm`: `∫ u(y) ∫ κ(h) v(y+h) dh dy = ∫ v(y) ∫ κ(h) u(y+h) dh dy` for even `κ ∈ L¹`
  (used for the duality of `|D|^p`), with the Fubini helper `integrable_corr_aux`.

Method: write `s^{-1-p}` and `1/(1+t²)` as Laplace/Gamma integrals and apply Tonelli on `(0,∞)²`.
-/
open MeasureTheory Set Filter Real
open scoped Topology FourierTransform
noncomputable section
namespace GSQG.Lib

theorem integrableOn_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => Real.exp (-(t * s))) (Ioi 0) := by
  have := integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0
  simpa [neg_mul] using this

theorem integral_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0:ℝ), Real.exp (-(t * s)) = 1 / t := by
  have := integral_exp_mul_Ioi (a := -t) (by linarith) 0
  simp only [neg_mul, mul_zero, Real.exp_zero] at this
  rw [this]; field_simp

theorem integrableOn_cos_mul_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => Real.cos s * Real.exp (-(t * s))) (Ioi 0) := by
  refine (integrableOn_exp_neg_mul_Ioi ht).mono' (by fun_prop) ?_
  refine Eventually.of_forall fun s => ?_
  rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (by simpa using Real.abs_cos_le_one s)

theorem integral_cos_mul_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0:ℝ), Real.cos s * Real.exp (-(t * s)) = t / (1 + t ^ 2) := by
  set a : ℂ := -t + Complex.I
  have ha : a.re < 0 := by simp [a]; linarith
  have hI := integrableOn_exp_mul_complex_Ioi ha 0
  have hE := integral_exp_mul_complex_Ioi ha 0
  have hre : ∀ s : ℝ, (Complex.exp (a * s)).re = Real.cos s * Real.exp (-(t * s)) := by
    intro s
    have : a * s = ((-(t * s) : ℝ) : ℂ) + (s : ℂ) * Complex.I := by
      simp [a]; ring
    rw [this, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have h1 : ∫ s in Ioi (0:ℝ), Real.cos s * Real.exp (-(t * s)) =
      (∫ s in Ioi (0:ℝ), Complex.exp (a * s)).re := by
    have := integral_re hI
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    simp_rw [hre]
  rw [h1, hE]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hden : (t:ℂ) ^ 2 + 1 ≠ 0 := by
    have : ((t ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : t ^ 2 + 1 ≠ 0)
    simpa using this
  have : -1 / a = ((t : ℂ) + Complex.I) / ((t : ℂ) ^ 2 + 1) := by
    have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
    field_simp
    simp only [a]
    ring_nf
    rw [Complex.I_sq]; ring
  rw [this, Complex.div_re]
  simp [Complex.normSq_apply]
  rw [show ((t:ℂ)^2) = ((t^2:ℝ):ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  have : (0:ℝ) < t^2 + 1 := by positivity
  field_simp
  ring


theorem integrableOn_one_sub_cos_mul_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => (1 - Real.cos s) * Real.exp (-(t * s))) (Ioi 0) := by
  simp_rw [sub_mul, one_mul]
  exact (integrableOn_exp_neg_mul_Ioi ht).sub (integrableOn_cos_mul_exp_neg_mul_Ioi ht)

theorem integral_one_sub_cos_mul_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0:ℝ), (1 - Real.cos s) * Real.exp (-(t * s)) = 1 / (t * (1 + t ^ 2)) := by
  simp_rw [sub_mul, one_mul]
  rw [integral_sub (integrableOn_exp_neg_mul_Ioi ht) (integrableOn_cos_mul_exp_neg_mul_Ioi ht),
    integral_exp_neg_mul_Ioi ht, integral_cos_mul_exp_neg_mul_Ioi ht]
  have : (0:ℝ) < 1 + t ^ 2 := by positivity
  field_simp
  ring

/-- Tonelli on the open quadrant: for a nonnegative function whose iterated integral (inner
variable `y`) is finite, the function is integrable on `(0,∞)²`. -/
theorem integrable_prod_Ioi_of_nonneg {F : ℝ × ℝ → ℝ}
    (hm : AEStronglyMeasurable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))))
    (h0 : ∀ x y : ℝ, 0 < x → 0 < y → 0 ≤ F (x, y))
    (h1 : ∀ x : ℝ, 0 < x → IntegrableOn (fun y => F (x, y)) (Ioi 0))
    (h2 : IntegrableOn (fun x => ∫ y in Ioi (0:ℝ), F (x, y)) (Ioi 0)) :
    Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))) := by
  rw [integrable_prod_iff hm]
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx using h1 x hx
  · refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    simp only [Real.norm_eq_abs]
    exact (abs_of_nonneg (h0 x y hx hy)).symm

/-- Swap of iterated integrals over `(0,∞)²` for a nonnegative function. -/
theorem integral_Ioi_swap_of_nonneg {F : ℝ → ℝ → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))))
    (h0 : ∀ x y : ℝ, 0 < x → 0 < y → 0 ≤ F x y)
    (h1 : ∀ x : ℝ, 0 < x → IntegrableOn (fun y => F x y) (Ioi 0))
    (h2 : IntegrableOn (fun x => ∫ y in Ioi (0:ℝ), F x y) (Ioi 0)) :
    Integrable (Function.uncurry F)
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))) ∧
      ∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), F x y = ∫ y in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ), F x y := by
  have hI := integrable_prod_Ioi_of_nonneg (F := Function.uncurry F) hm
    (fun x y hx hy => h0 x y hx hy) h1 h2
  exact ⟨hI, integral_integral_swap hI⟩


/-- `∫_0^∞ t^(a-1) e^{-rt} dt` is finite (`a, r > 0`). -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r) (by linarith)
    one_pos hr
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

/-- The Mellin transform of `1/(1+t²)`: for `0 < p < 2`,
`∫_0^∞ t^{p-1}/(1+t²) dt = π / (2 sin(πp/2))`. -/
theorem integral_rpow_div_one_add_sq {p : ℝ} (hp : 0 < p) (hp2 : p < 2) :
    IntegrableOn (fun t : ℝ => t ^ (p - 1) / (1 + t ^ 2)) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), t ^ (p - 1) / (1 + t ^ 2) = π / (2 * Real.sin (π * p / 2)) := by
  set F : ℝ → ℝ → ℝ := fun v t => Real.exp (-v) * (t ^ (p - 1) * Real.exp (-v * t ^ (2:ℝ)))
  have hm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    simp only [F, Function.uncurry_def]
    fun_prop
  have h0 : ∀ v t : ℝ, 0 < v → 0 < t → 0 ≤ F v t := fun v t _ ht => by
    simp only [F]; have := Real.rpow_nonneg ht.le (p - 1); positivity
  have hinner : ∀ v : ℝ, 0 < v → ∫ t in Ioi (0:ℝ), F v t =
      Real.exp (-v) * (v ^ ((1 - p / 2) - 1) * (1 / 2) * Real.Gamma (p / 2)) := by
    intro v hv
    simp only [F]
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) hv]
    rw [show -(p - 1 + 1) / 2 = 1 - p / 2 - 1 by ring, show (p - 1 + 1) / 2 = p / 2 by ring]
  have h1 : ∀ v : ℝ, 0 < v → IntegrableOn (fun t => F v t) (Ioi 0) := fun v hv =>
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hv).const_mul _
  have hG : IntegrableOn (fun v : ℝ => v ^ ((1 - p / 2) - 1) * Real.exp (-(1 * v))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) one_pos
  have h2 : IntegrableOn (fun v => ∫ t in Ioi (0:ℝ), F v t) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hG.mul_const ((1 / 2) * Real.Gamma (p / 2))) (fun v hv => ?_)
      measurableSet_Ioi
    rw [hinner v hv]; simp only [one_mul]; ring
  obtain ⟨hI, hswap⟩ := integral_Ioi_swap_of_nonneg hm h0 h1 h2
  have hother : ∀ t : ℝ, 0 < t → ∫ v in Ioi (0:ℝ), F v t = t ^ (p - 1) / (1 + t ^ 2) := by
    intro t ht
    simp only [F]
    have h2t : t ^ (2:ℝ) = t ^ 2 := by norm_cast
    have : ∀ v : ℝ, Real.exp (-v) * (t ^ (p - 1) * Real.exp (-v * t ^ (2:ℝ))) =
        t ^ (p - 1) * Real.exp (-((1 + t ^ 2) * v)) := by
      intro v; rw [h2t, ← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; ring_nf
    simp_rw [this]
    rw [integral_const_mul, integral_exp_neg_mul_Ioi (by positivity)]
    field_simp
  have hint : IntegrableOn (fun t : ℝ => t ^ (p - 1) / (1 + t ^ 2)) (Ioi 0) := by
    have := hI.integral_prod_right
    refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
    exact hother t ht
  refine ⟨hint, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t (ht : t ∈ Ioi (0:ℝ)) => hother t ht),
    ← hswap, setIntegral_congr_fun measurableSet_Ioi (fun v (hv : v ∈ Ioi (0:ℝ)) => hinner v hv)]
  have hΓ := integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - p / 2) (r := 1) (by linarith) one_pos
  simp only [one_mul, div_one, Real.one_rpow] at hΓ
  have : ∀ v : ℝ, Real.exp (-v) * (v ^ ((1 - p / 2) - 1) * (1 / 2) * Real.Gamma (p / 2)) =
      ((1 / 2) * Real.Gamma (p / 2)) * (v ^ ((1 - p / 2) - 1) * Real.exp (-v)) := fun v => by ring
  simp_rw [this]
  rw [integral_const_mul, hΓ, mul_assoc, Real.Gamma_mul_Gamma_one_sub]
  rw [show π * (p / 2) = π * p / 2 by ring]
  field_simp


/-- For `0 < p < 2`: `∫_0^∞ (1 - cos s) s^{-1-p} ds = π / (2 Γ(1+p) sin(πp/2))`
(the integrand is nonnegative and integrable). -/
theorem integral_one_sub_cos_mul_rpow {p : ℝ} (hp : 0 < p) (hp2 : p < 2) :
    IntegrableOn (fun s : ℝ => (1 - Real.cos s) * s ^ (-1 - p)) (Ioi 0) ∧
      ∫ s in Ioi (0:ℝ), (1 - Real.cos s) * s ^ (-1 - p) =
        π / (2 * Real.Gamma (1 + p) * Real.sin (π * p / 2)) := by
  obtain ⟨hJi, hJ⟩ := integral_rpow_div_one_add_sq hp hp2
  set G : ℝ → ℝ → ℝ := fun t s => t ^ p * ((1 - Real.cos s) * Real.exp (-(t * s)))
  have hm : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    simp only [G, Function.uncurry_def]
    fun_prop
  have h0 : ∀ t s : ℝ, 0 < t → 0 < s → 0 ≤ G t s := fun t s ht _ => by
    simp only [G]
    have := Real.rpow_nonneg ht.le p
    have := Real.cos_le_one s
    have : 0 ≤ 1 - Real.cos s := by linarith
    positivity
  have hinner : ∀ t : ℝ, 0 < t → ∫ s in Ioi (0:ℝ), G t s = t ^ (p - 1) / (1 + t ^ 2) := by
    intro t ht
    simp only [G]
    rw [integral_const_mul, integral_one_sub_cos_mul_exp_neg_mul_Ioi ht, Real.rpow_sub_one ht.ne']
    field_simp
  have h1 : ∀ t : ℝ, 0 < t → IntegrableOn (fun s => G t s) (Ioi 0) := fun t ht =>
    (integrableOn_one_sub_cos_mul_exp_neg_mul_Ioi ht).const_mul _
  have h2 : IntegrableOn (fun t => ∫ s in Ioi (0:ℝ), G t s) (Ioi 0) :=
    IntegrableOn.congr_fun hJi (fun t ht => (hinner t ht).symm) measurableSet_Ioi
  obtain ⟨hI, hswap⟩ := integral_Ioi_swap_of_nonneg hm h0 h1 h2
  have hΓ0 : 0 < Real.Gamma (1 + p) := Real.Gamma_pos_of_pos (by linarith)
  have hother : ∀ s : ℝ, 0 < s → ∫ t in Ioi (0:ℝ), G t s =
      Real.Gamma (1 + p) * ((1 - Real.cos s) * s ^ (-1 - p)) := by
    intro s hs
    simp only [G]
    have : ∀ t : ℝ, t ^ p * ((1 - Real.cos s) * Real.exp (-(t * s))) =
        (1 - Real.cos s) * (t ^ ((1 + p) - 1) * Real.exp (-(s * t))) := fun t => by
      rw [show 1 + p - 1 = p by ring, mul_comm t s]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hs,
      one_div, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, show -(1 + p) = -1 - p by ring]
    ring
  have hint : IntegrableOn (fun s : ℝ => (1 - Real.cos s) * s ^ (-1 - p)) (Ioi 0) := by
    have := (hI.integral_prod_right).const_mul (Real.Gamma (1 + p))⁻¹
    refine IntegrableOn.congr_fun this (fun s hs => ?_) measurableSet_Ioi
    simp only [Function.uncurry_apply_pair]
    rw [hother s hs]
    field_simp
  refine ⟨hint, ?_⟩
  have key : ∫ s in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), G t s =
      Real.Gamma (1 + p) * ∫ s in Ioi (0:ℝ), (1 - Real.cos s) * s ^ (-1 - p) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun s (hs : s ∈ Ioi (0:ℝ)) => hother s hs)
  rw [← hswap, setIntegral_congr_fun measurableSet_Ioi
    (fun t (ht : t ∈ Ioi (0:ℝ)) => hinner t ht), hJ] at key
  have hsin : 0 < Real.sin (π * p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [eq_div_iff (by positivity)]
  rw [div_eq_iff (by positivity)] at key
  linear_combination -key


/-- The classical form: for `0 < p < 1`,
`∫_0^∞ (1 - cos s) s^{-1-p} ds = Γ(1-p) cos(πp/2) / p`. -/
theorem integral_one_sub_cos_mul_rpow_eq_Gamma_cos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∫ s in Ioi (0:ℝ), (1 - Real.cos s) * s ^ (-1 - p) =
      Real.Gamma (1 - p) * Real.cos (π * p / 2) / p := by
  rw [(integral_one_sub_cos_mul_rpow hp (by linarith)).2]
  have hsin : 0 < Real.sin (π * p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hsin2 : 0 < Real.sin (π * p) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hΓp : 0 < Real.Gamma p := Real.Gamma_pos_of_pos hp
  have hrefl := Real.Gamma_mul_Gamma_one_sub p
  have h1p : Real.Gamma (1 + p) = p * Real.Gamma p := by
    rw [add_comm]; exact Real.Gamma_add_one hp.ne'
  have hdouble : Real.sin (π * p) = 2 * Real.sin (π * p / 2) * Real.cos (π * p / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [h1p]
  rw [eq_div_iff hsin2.ne', hdouble] at hrefl
  field_simp
  linear_combination -hrefl

/-- If `f` is integrable on `(0,∞)` then `x ↦ f |x|` is integrable on `ℝ`. -/
theorem integrable_comp_abs_of_integrableOn_Ioi {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : IntegrableOn f (Ioi 0)) : Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) := by
    refine hf.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  have := int_Iic.union hf'
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- Scaled half-line version: for `0 < p < 2` and `b > 0`,
`∫_0^∞ (1 - cos(b t)) t^{-1-p} dt = b^p ∫_0^∞ (1 - cos s) s^{-1-p} ds`. -/
theorem integral_one_sub_cos_mul_rpow_scale {p b : ℝ} (hp : 0 < p) (hp2 : p < 2) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (1 - Real.cos (b * t)) * t ^ (-1 - p)) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), (1 - Real.cos (b * t)) * t ^ (-1 - p) =
        b ^ p * (π / (2 * Real.Gamma (1 + p) * Real.sin (π * p / 2))) := by
  obtain ⟨hI, hV⟩ := integral_one_sub_cos_mul_rpow hp hp2
  set g : ℝ → ℝ := fun s => b ^ (1 + p) * ((1 - Real.cos s) * s ^ (-1 - p))
  have hg : ∀ t : ℝ, 0 < t → (1 - Real.cos (b * t)) * t ^ (-1 - p) = g (b * t) := by
    intro t ht
    simp only [g]
    rw [Real.mul_rpow hb.le ht.le]
    have : b ^ (1 + p) * b ^ (-1 - p) = 1 := by
      rw [← Real.rpow_add hb]; simp
    linear_combination (-(1 - Real.cos (b * t)) * t ^ (-1 - p)) * this
  have hgi : IntegrableOn g (Ioi 0) := hI.const_mul _
  constructor
  · have : IntegrableOn (fun t => g (b * t)) (Ioi 0) := by
      have := (integrableOn_Ioi_comp_mul_left_iff g 0 hb).mpr (by simpa using hgi)
      exact this
    exact this.congr_fun (fun t ht => (hg t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi (fun t (ht : t ∈ Ioi (0:ℝ)) => hg t ht),
      integral_comp_mul_left_Ioi g 0 hb, mul_zero, smul_eq_mul]
    simp only [g]
    rw [integral_const_mul, hV, ← mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hb]
    congr 2; ring

/-- Whole-line version: for `0 < p < 2` and every `ξ`,
`∫_ℝ (1 - cos(hξ)) |h|^{-1-p} dh = π |ξ|^p / (Γ(1+p) sin(πp/2))`, the integrand being integrable. -/
theorem integral_one_sub_cos_mul_abs_rpow {p : ℝ} (hp : 0 < p) (hp2 : p < 2) (ξ : ℝ) :
    Integrable (fun h : ℝ => (1 - Real.cos (h * ξ)) * |h| ^ (-1 - p)) ∧
      ∫ h, (1 - Real.cos (h * ξ)) * |h| ^ (-1 - p) =
        |ξ| ^ p * (π / (Real.Gamma (1 + p) * Real.sin (π * p / 2))) := by
  set f : ℝ → ℝ := fun t => (1 - Real.cos (|ξ| * t)) * t ^ (-1 - p)
  have hf : ∀ h : ℝ, (1 - Real.cos (h * ξ)) * |h| ^ (-1 - p) = f |h| := by
    intro h; simp only [f]
    rw [← abs_mul, mul_comm ξ h, Real.cos_abs]
  simp_rw [hf]
  rcases eq_or_lt_of_le (abs_nonneg ξ) with hξ | hξ
  · have : f = fun _ => 0 := by funext t; simp [f, ← hξ]
    rw [this]; simp [← hξ, Real.zero_rpow hp.ne']
  obtain ⟨hI, hV⟩ := integral_one_sub_cos_mul_rpow_scale hp hp2 hξ
  refine ⟨integrable_comp_abs_of_integrableOn_Ioi hI, ?_⟩
  rw [integral_comp_abs (f := f), hV]
  have hsin : 0 < Real.sin (π * p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have := Real.Gamma_pos_of_pos (show 0 < 1 + p by linarith)
  field_simp


/-- `∫_0^∞ (1 - cos s)/s² ds = π/2`. -/
theorem integral_one_sub_cos_div_sq :
    IntegrableOn (fun s : ℝ => (1 - Real.cos s) / s ^ 2) (Ioi 0) ∧
      ∫ s in Ioi (0:ℝ), (1 - Real.cos s) / s ^ 2 = π / 2 := by
  obtain ⟨hI, hV⟩ := integral_one_sub_cos_mul_rpow (p := 1) one_pos one_lt_two
  have he : ∀ s : ℝ, 0 < s → (1 - Real.cos s) * s ^ (-1 - 1 : ℝ) = (1 - Real.cos s) / s ^ 2 := by
    intro s hs
    rw [show (-1 - 1 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, div_eq_mul_inv]
    norm_cast
  refine ⟨hI.congr_fun (fun s hs => he s hs) measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun s (hs : s ∈ Ioi (0:ℝ)) => he s hs), hV]
  rw [show (1:ℝ) + 1 = 2 by norm_num, Real.Gamma_two, show π * 1 / 2 = π / 2 by ring,
    Real.sin_pi_div_two]
  ring

/-- `∫_0^∞ sin² x / x² dx = π/2`. -/
theorem integral_sin_sq_div_sq :
    IntegrableOn (fun x : ℝ => Real.sin x ^ 2 / x ^ 2) (Ioi 0) ∧
      ∫ x in Ioi (0:ℝ), Real.sin x ^ 2 / x ^ 2 = π / 2 := by
  obtain ⟨hI, hV⟩ := integral_one_sub_cos_div_sq
  set g : ℝ → ℝ := fun s => 2 * ((1 - Real.cos s) / s ^ 2)
  have hg : ∀ x : ℝ, Real.sin x ^ 2 / x ^ 2 = g (2 * x) := by
    intro x
    simp only [g]
    rw [Real.cos_two_mul, Real.cos_sq']
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · field_simp; ring
  have hgi : IntegrableOn g (Ioi 0) := Integrable.const_mul hI 2
  simp_rw [hg]
  refine ⟨(integrableOn_Ioi_comp_mul_left_iff g 0 two_pos).mpr (by simpa using hgi), ?_⟩
  rw [integral_comp_mul_left_Ioi g 0 two_pos, mul_zero, smul_eq_mul]
  simp only [g]
  rw [integral_const_mul, hV]; ring

/-- The function `x ↦ (1 - cos x)/x`, written in a form that is visibly continuous
(`sin(x/2) sinc(x/2)`). -/
theorem one_sub_cos_div_eq (x : ℝ) :
    (1 - Real.cos x) / x = Real.sin (x / 2) * Real.sinc (x / 2) := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · rw [Real.sinc_of_ne_zero (by simpa using hx)]
    have : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      conv_lhs => rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    rw [this]
    field_simp
    ring


/-- `x ↦ sin x / x` is interval integrable on every `[0, R]`. -/
theorem intervalIntegrable_sin_div {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume 0 R := by
  have := Real.continuous_sinc.intervalIntegrable (μ := volume) 0 R
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR] at this ⊢
  exact this.congr_fun (fun x hx => Real.sinc_of_ne_zero hx.1.ne') measurableSet_Ioc

/-- **Dirichlet integral**: `∫_0^R sin x / x dx → π/2` as `R → ∞`. -/
theorem tendsto_integral_sin_div :
    Tendsto (fun R : ℝ => ∫ x in (0:ℝ)..R, Real.sin x / x) atTop (𝓝 (π / 2)) := by
  obtain ⟨hI, hV⟩ := integral_one_sub_cos_div_sq
  set F : ℝ → ℝ := fun x => Real.sin (x / 2) * Real.sinc (x / 2)
  have hF : ∀ x, F x = (1 - Real.cos x) / x := fun x => (one_sub_cos_div_eq x).symm
  have hFc : Continuous F := by simp only [F]; fun_prop
  have key : ∀ R : ℝ, 0 < R → ∫ x in (0:ℝ)..R, Real.sin x / x =
      (1 - Real.cos R) / R + ∫ x in (0:ℝ)..R, (1 - Real.cos x) / x ^ 2 := by
    intro R hR
    have hJ : IntervalIntegrable (fun x : ℝ => (1 - Real.cos x) / x ^ 2) volume 0 R := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
      exact hI.mono_set Ioc_subset_Ioi_self
    have hderiv : ∀ x ∈ Ioo (0:ℝ) R,
        HasDerivAt F (Real.sin x / x - (1 - Real.cos x) / x ^ 2) x := by
      intro x hx
      have hx0 : x ≠ 0 := hx.1.ne'
      have h1 : HasDerivAt (fun x => (1 - Real.cos x) / x)
          ((Real.sin x * x - (1 - Real.cos x) * 1) / x ^ 2) x := by
        have := ((hasDerivAt_const x (1:ℝ)).sub (Real.hasDerivAt_cos x)).div (hasDerivAt_id x) hx0
        convert this using 1
        · funext y; simp
        · simp
      have h2 : (Real.sin x * x - (1 - Real.cos x) * 1) / x ^ 2 =
          Real.sin x / x - (1 - Real.cos x) / x ^ 2 := by field_simp
      rw [← h2]
      exact h1.congr_of_eventuallyEq (Eventually.of_forall hF)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hFc.continuousOn hderiv
      ((intervalIntegrable_sin_div hR.le).sub hJ)
    rw [intervalIntegral.integral_sub (intervalIntegrable_sin_div hR.le) hJ, hF, hF] at this
    simp only [div_zero, sub_zero] at this
    linarith
  have hlim1 : Tendsto (fun R : ℝ => (1 - Real.cos R) / R) atTop (𝓝 0) := by
    have hb : Tendsto (fun R : ℝ => 2 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_gt_atTop 0] with R h
      exact div_nonneg (by linarith [Real.cos_le_one R]) h.le
    · filter_upwards [eventually_gt_atTop 0] with R hR
      exact div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos R]) hR.le
  have hlim2 := intervalIntegral_tendsto_integral_Ioi 0 hI tendsto_id
  rw [hV] at hlim2
  have := hlim1.add hlim2
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact (key R hR).symm

/-! ### Fourier transform with the `e^{-ixξ}` convention -/

/-- The `e^{-ixξ}` Fourier transform in terms of Mathlib's `𝓕` (`e^{-2πixw}` convention). -/
theorem integral_mul_exp_neg_I_eq_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    ∫ x, f x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) = 𝓕 f (ξ / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp


/-- Fourier inversion for Schwartz functions with the convention
`ĝ(ξ) = ∫ g(x) e^{-ixξ} dx`, `g(x) = (2π)⁻¹ ∫ ĝ(ξ) e^{ixξ} dξ`; `ĝ` is integrable. -/
theorem schwartz_fourier_inversion (g : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ => ∫ x, g x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) ∧
    ∀ y : ℝ, ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ, (∫ x, g x * Complex.exp (-(Complex.I * (x : ℂ) *
        (ξ : ℂ)))) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) = g y := by
  simp_rw [integral_mul_exp_neg_I_eq_fourier]
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  refine ⟨?_, fun y => ?_⟩
  · rw [← SchwartzMap.fourier_coe]
    exact (𝓕 g).integrable.comp_div h2π
  set H : ℝ → ℂ := fun w => 𝓕 (⇑g) w * Complex.exp (Complex.I * (y : ℂ) * ((2 * π * w : ℝ) : ℂ))
  have hH : ∀ ξ : ℝ, 𝓕 (⇑g) (ξ / (2 * π)) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
      H (ξ / (2 * π)) := by
    intro ξ; simp only [H]; congr 4; field_simp
  simp_rw [hH]
  rw [Measure.integral_comp_div H (2 * π), abs_of_pos (by positivity), Complex.real_smul,
    ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast h2π), one_mul]
  have hinv : 𝓕⁻ (𝓕 (⇑g)) y = g y := by
    rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe, FourierPair.fourierInv_fourier_eq]
  rw [← hinv, Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [H, smul_eq_mul, RCLike.inner_apply]
  rw [mul_comm]
  congr 2
  simp
  ring

/-- Fourier transform of a derivative with the `e^{-ixξ}` convention: `(g')^(ξ) = iξ ĝ(ξ)`. -/
theorem integral_deriv_mul_exp_neg_I {g : ℝ → ℂ} (hg : Integrable g) (hd : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) (ξ : ℝ) :
    ∫ x, deriv g x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) =
      Complex.I * ξ * ∫ x, g x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) := by
  rw [integral_mul_exp_neg_I_eq_fourier, integral_mul_exp_neg_I_eq_fourier,
    Real.fourier_deriv hg hd hg']
  simp only [smul_eq_mul]
  have h2π : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-! ### Correlation pairings -/

/-- Fubini/integrability for `(y,h) ↦ κ(h) u(y+c₁h) w(y+c₂h)`-type products: here
`(y,h) ↦ κ(h) * (U (y + a*h) * V (y + b*h))` with `κ ∈ L¹`, and for each `h`,
`y ↦ U(y+ah) V(y+bh)` dominated by `M |W(y + c h)|`, `W ∈ L¹`. -/
theorem integrable_corr_aux {F : ℝ × ℝ → ℝ} {κ W : ℝ → ℝ} (hF : AEStronglyMeasurable F
    (volume.prod volume)) (hκ : Integrable κ) (hW : Integrable W) (M : ℝ) (c : ℝ)
    (hint : ∀ h, Integrable (fun y => F (y, h)))
    (hb : ∀ y h, |F (y, h)| ≤ M * |κ h| * |W (y + c * h)|) :
    Integrable F (volume.prod volume) := by
  rw [integrable_prod_iff' hF]
  refine ⟨Eventually.of_forall hint, ?_⟩
  have hmeas : AEStronglyMeasurable (fun h => ∫ y, ‖F (y, h)‖) volume := by
    have := (hF.norm.prod_swap).integral_prod_right'
    simpa using this
  refine Integrable.mono' ((hκ.norm.mul_const (M * ∫ y, |W y|))) hmeas
    (Eventually.of_forall fun h => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hWi : Integrable (fun y => M * |κ h| * |W (y + c * h)|) :=
    (hW.comp_add_right (c * h)).abs.const_mul _
  have h1 : ∫ y, ‖F (y, h)‖ ≤ ∫ y, M * |κ h| * |W (y + c * h)| :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hWi
      (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs]; exact hb y h)
  have h2 : ∫ y, M * |κ h| * |W (y + c * h)| = ‖κ h‖ * (M * ∫ y, |W y|) := by
    rw [integral_const_mul, integral_add_right_eq_self (fun y => |W y|) (c * h),
      Real.norm_eq_abs]; ring
  linarith

/-- Symmetry of the correlation pairing: for even `κ ∈ L¹`, `u ∈ L¹`, continuous `u`, and
continuous bounded `v`, `∫ u(y) ∫ κ(h) v(y+h) dh dy = ∫ v(y) ∫ κ(h) u(y+h) dh dy`. -/
theorem integral_corr_symm {κ u v : ℝ → ℝ} (hκ : Integrable κ) (heven : ∀ h, κ (-h) = κ h)
    (hu : Integrable u) (hum : Continuous u) (hvm : Continuous v) (M : ℝ)
    (hv : ∀ x, |v x| ≤ M) :
    ∫ y, u y * ∫ h, κ h * v (y + h) = ∫ y, v y * ∫ h, κ h * u (y + h) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hv 0)
  have hmeas1 : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.2 * u z.1 * v (z.1 + z.2))
      (volume.prod volume) :=
    ((hκ.aestronglyMeasurable.comp_snd).mul hum.aestronglyMeasurable.comp_fst).mul
      (hvm.comp continuous_add).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.2 * v z.1 * u (z.1 + z.2))
      (volume.prod volume) :=
    ((hκ.aestronglyMeasurable.comp_snd).mul hvm.aestronglyMeasurable.comp_fst).mul
      (hum.comp continuous_add).aestronglyMeasurable
  have I1 : Integrable (fun z : ℝ × ℝ => κ z.2 * u z.1 * v (z.1 + z.2)) (volume.prod volume) := by
    refine integrable_corr_aux hmeas1 hκ hu M 0 (fun h => ?_) (fun y h => ?_)
    · have : Integrable (fun y => (κ h * u y) * v (y + h)) :=
        (hu.const_mul (κ h)).mul_bdd (hvm.comp (continuous_id.add continuous_const)).aestronglyMeasurable
          (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hv _)
      exact this
    · simp only [zero_mul, add_zero, abs_mul]
      have := hv (y + h); have := abs_nonneg (κ h); have := abs_nonneg (u y)
      nlinarith [mul_nonneg (abs_nonneg (κ h)) (abs_nonneg (u y))]
  have I2 : Integrable (fun z : ℝ × ℝ => κ z.2 * v z.1 * u (z.1 + z.2)) (volume.prod volume) := by
    refine integrable_corr_aux hmeas2 hκ hu M 1 (fun h => ?_) (fun y h => ?_)
    · have : Integrable (fun y => κ h * (u (y + h) * v y)) :=
        ((hu.comp_add_right h).mul_bdd hvm.aestronglyMeasurable
          (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hv _)).const_mul _
      refine this.congr (Eventually.of_forall fun y => ?_); simp only; ring
    · simp only [one_mul, abs_mul]
      have := hv y; have := abs_nonneg (κ h); have := abs_nonneg (u (y + h))
      nlinarith [mul_nonneg (abs_nonneg (κ h)) (abs_nonneg (u (y + h)))]
  have lhs : ∫ y, u y * ∫ h, κ h * v (y + h) = ∫ h, κ h * ∫ y, u y * v (y + h) := by
    have := integral_integral_swap (f := fun y h => κ h * u y * v (y + h)) I1
    have e1 : ∀ y, u y * ∫ h, κ h * v (y + h) = ∫ h, κ h * u y * v (y + h) := fun y => by
      rw [← integral_const_mul]; congr 1; funext h; ring
    have e2 : ∀ h, κ h * ∫ y, u y * v (y + h) = ∫ y, κ h * u y * v (y + h) := fun h => by
      rw [← integral_const_mul]; congr 1; funext y; ring
    simp_rw [e1, e2]; exact this
  have rhs : ∫ y, v y * ∫ h, κ h * u (y + h) = ∫ h, κ h * ∫ y, v y * u (y + h) := by
    have := integral_integral_swap (f := fun y h => κ h * v y * u (y + h)) I2
    have e1 : ∀ y, v y * ∫ h, κ h * u (y + h) = ∫ h, κ h * v y * u (y + h) := fun y => by
      rw [← integral_const_mul]; congr 1; funext h; ring
    have e2 : ∀ h, κ h * ∫ y, v y * u (y + h) = ∫ y, κ h * v y * u (y + h) := fun h => by
      rw [← integral_const_mul]; congr 1; funext y; ring
    simp_rw [e1, e2]; exact this
  rw [lhs, rhs, ← integral_neg_eq_self (fun h => κ h * ∫ y, v y * u (y + h))]
  congr 1; funext h
  rw [heven]
  congr 1
  rw [← integral_add_right_eq_self (fun y => u y * v (y + h)) (-h)]
  congr 1; funext y
  simp only [neg_add_cancel_right]
  rw [mul_comm, show y + -h = y + (-h) from rfl]

end GSQG.Lib
