import GSQG.Definitions
import GSQG.Auxiliary.SpecialIntegrals

/-!
# §§1–2: setup and self-similar reduction (blueprint ch. 01)

Statements and proofs of the nodes of `blueprint/src/chapters/01_setup.tex`.  No `sorry` remains
(`c01_frac_singular_integral` and `c01_frac_duality` are proved using `GSQG/Auxiliary/SpecialIntegrals`).
The tail of the chapter (`c01_profile_from_correction`, `c01_profile_smooth`,
`c01_profile_bounds`, `c01_aux_main_allT`, `main`, `c01_desingularization`), which uses
`fixed_point_correction` (§3) and `fixed_point_smoothness` (Theorem 3.5), lives in
`GSQG/Sec3_FixedPoint/MainTheorem.lean`.
All definition nodes of this chapter live in `GSQG.Definitions` (`fracD`, `A_eps`, `c01_Jfull_eps`,
`J_eps`, `c01_Q_eps`, `residual`, `L0`, `profile_equation`, `gsqg_front_equation`,
`self_similar_ansatz`, ...).  The chapter-local definitions below
(`c01_approx_family_good`, `c01_correction_data`, `c01_profile_bounds_hold`) only package the
objects of `thm:fixed_point_approximation` / `thm:fixed_point_correction` (chapter 02) that the
statements of `lem:c01_profile_from_correction`, `lem:c01_profile_smooth`, `lem:c01_profile_bounds`
refer to, and the bounds of item (1) of `thm:main`.

Throughout, `α = p + 1`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace GSQG

/-! ### Chapter-local auxiliary lemmas -/

/-- `c_α ≥ 0` for `0 < p < 1`. -/
theorem c01_aux_calpha_nonneg (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : 0 ≤ calpha p := by
  unfold calpha
  have h1 : 0 < Real.Gamma (1 + p) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.sin (π * p / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  positivity

/-- If `f` is integrable on `(0,∞)` then `x ↦ f |x|` is integrable on `ℝ`. -/
theorem c01_aux_integrable_comp_abs {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
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

/-- The radial dominating function of the singular integral. -/
def c01_aux_psi (p Λ M t : ℝ) : ℝ :=
  if t ≤ 1 then Λ * t ^ (-p) else 2 * M * t ^ (-(p + 1))

/-- Integrability and integral of the radial dominating function. -/
theorem c01_aux_psi_integral (p Λ M : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (c01_aux_psi p Λ M) (Ioi 0) ∧
      ∫ t in Ioi 0, c01_aux_psi p Λ M t = Λ / (1 - p) + 2 * M / p := by
  have hIoc : IntegrableOn (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -p) (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul Λ
  have hIoi : IntegrableOn (fun t : ℝ => 2 * M * t ^ (-(p + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have e1 : EqOn (c01_aux_psi p Λ M) (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 1) := by
    intro t ht; simp [c01_aux_psi, ht.2]
  have e2 : EqOn (c01_aux_psi p Λ M) (fun t : ℝ => 2 * M * t ^ (-(p + 1))) (Ioi 1) := by
    intro t ht; simp [c01_aux_psi, not_le.mpr (show (1:ℝ) < t from ht)]
  have i1 : IntegrableOn (c01_aux_psi p Λ M) (Ioc 0 1) := hIoc.congr_fun e1.symm measurableSet_Ioc
  have i2 : IntegrableOn (c01_aux_psi p Λ M) (Ioi 1) := hIoi.congr_fun e2.symm measurableSet_Ioi
  have hU : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  refine ⟨hU ▸ i1.union i2, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
    setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have hp0 : p ≠ 0 := hp.ne'
  have h0 : (0 : ℝ) ^ (-p + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, Real.one_rpow, Real.one_rpow, show -p + 1 = 1 - p by ring,
    show -(p + 1) + 1 = -p by ring]
  field_simp
  ring

/-- From an a.e. bound and a Lipschitz bound near `y`, the value at `y` is bounded. -/
theorem c01_aux_point_bound (g : ℝ → ℝ) (M : ℝ) (hM : ∀ᵐ z, |g z| ≤ M) (y Λ : ℝ)
    (hΛ : 0 ≤ Λ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1), |g z - g w| ≤ Λ * |z - w|) :
    |g y| ≤ M ∧ 0 ≤ M := by
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ z ∈ Ioo (y - δ) (y + δ), |g z| ≤ M := by
    intro δ hδ _
    by_contra h
    push Not at h
    have hsub : Ioo (y - δ) (y + δ) ⊆ {z | ¬ |g z| ≤ M} := fun z hz => not_le.mpr (h z hz)
    have h0 : volume {z | ¬ |g z| ≤ M} = 0 := by
      rw [ae_iff] at hM; exact hM
    have := measure_mono_null hsub h0
    rw [Real.volume_Ioo] at this
    simp at this
    linarith
  have hb : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → |g y| ≤ M + Λ * δ := by
    intro δ hδ hδ1
    obtain ⟨z, hz, hgz⟩ := key δ hδ hδ1
    have hz' : z ∈ Icc (y - 1) (y + 1) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hy' : y ∈ Icc (y - 1) (y + 1) := ⟨by linarith, by linarith⟩
    have := hLip y hy' z hz'
    have hd : |y - z| ≤ δ := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    calc |g y| ≤ |g z| + |g y - g z| := by
          have := abs_sub_abs_le_abs_sub (g y) (g z); linarith
      _ ≤ M + Λ * δ := by nlinarith
  obtain ⟨z, -, hz⟩ := key 1 one_pos le_rfl
  refine ⟨?_, (abs_nonneg _).trans hz⟩
  refine le_of_forall_pos_le_add fun e he => ?_
  set δ := min 1 (e / (Λ + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have h1 := hb δ hδ (min_le_left _ _)
  have h2 : Λ * δ ≤ e := by
    calc Λ * δ ≤ (Λ + 1) * (e / (Λ + 1)) :=
          mul_le_mul (by linarith) (min_le_right _ _) hδ.le (by linarith)
      _ = e := by field_simp
  linarith

/-- The singular integral kernel estimate behind lem:c01_frac_well_defined: integrability and the
bound `∫ |(g(y)-g(z))/|y-z|^α| dz ≤ 2Λ/(2-α) + 4M/(α-1)`. -/
theorem c01_aux_frac_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ)
    (hgm : AEStronglyMeasurable g volume) (M : ℝ) (hM : ∀ᵐ z, |g z| ≤ M) (y Λ : ℝ)
    (hΛ : 0 ≤ Λ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1), |g z - g w| ≤ Λ * |z - w|) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) ∧
      ∫ z, |(g y - g z) / |y - z| ^ (p + 1)| ≤
        2 * Λ / (2 - (p + 1)) + 4 * M / ((p + 1) - 1) := by
  obtain ⟨hgy, hM0⟩ := c01_aux_point_bound g M hM y Λ hΛ hLip
  obtain ⟨hψi, hψ⟩ := c01_aux_psi_integral p Λ M hp hp1
  set D : ℝ → ℝ := fun z => c01_aux_psi p Λ M |y - z|
  have hDi : Integrable D :=
    (c01_aux_integrable_comp_abs hψi).comp_sub_left y
  have hDint : ∫ z, D z = 2 * Λ / (2 - (p + 1)) + 4 * M / ((p + 1) - 1) := by
    simp only [D]
    rw [integral_sub_left_eq_self (fun z => c01_aux_psi p Λ M |z|) volume y,
      integral_comp_abs (f := c01_aux_psi p Λ M), hψ]
    have h1p : (1 : ℝ) - p ≠ 0 := by linarith
    have : (2 : ℝ) - (p + 1) = 1 - p := by ring
    rw [this, show p + 1 - 1 = p by ring]
    field_simp
    ring
  have hmeas : AEStronglyMeasurable (fun z => (g y - g z) / |y - z| ^ (p + 1)) volume := by
    have h2 : Measurable (fun z : ℝ => (|y - z| ^ (p + 1))⁻¹) := by
      have : Continuous (fun z : ℝ => |y - z| ^ (p + 1)) :=
        (continuous_const.sub continuous_id).abs.rpow_const (fun _ => Or.inr (by linarith))
      exact this.measurable.inv
    have := (aestronglyMeasurable_const (b := g y)).sub hgm |>.mul h2.aestronglyMeasurable
    simp only [div_eq_mul_inv]
    exact this
  have hbound : ∀ᵐ z, ‖(g y - g z) / |y - z| ^ (p + 1)‖ ≤ D z := by
    filter_upwards [hM] with z hz
    rw [Real.norm_eq_abs]
    by_cases hzy : z = y
    · subst hzy
      simp only [sub_self, zero_div, abs_zero, D, c01_aux_psi]
      simp only [zero_le_one, ite_true]
      rw [Real.zero_rpow (by linarith)]; simp
    have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hzy))
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    simp only [D, c01_aux_psi]
    split_ifs with h1
    · have hz' : z ∈ Icc (y - 1) (y + 1) := by
        rw [abs_le] at h1; exact ⟨by linarith [h1.2], by linarith [h1.1]⟩
      have hy' : y ∈ Icc (y - 1) (y + 1) := ⟨by linarith, by linarith⟩
      have hl := hLip y hy' z hz'
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
      calc |g y - g z| ≤ Λ * |y - z| := hl
        _ = Λ * |y - z| ^ (-p) * |y - z| ^ (p + 1) := by
          rw [mul_assoc, ← Real.rpow_add hpos]; simp
    · rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
      calc |g y - g z| ≤ |g y| + |g z| := abs_sub _ _
        _ ≤ 2 * M := by linarith
        _ = 2 * M * |y - z| ^ (-(p + 1)) * |y - z| ^ (p + 1) := by
          rw [mul_assoc, ← Real.rpow_add hpos]; simp
  have hInt : Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) :=
    Integrable.mono' hDi hmeas hbound
  refine ⟨hInt, ?_⟩
  rw [← hDint]
  apply integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hDi
  filter_upwards [hbound] with z hz
  rw [Real.norm_eq_abs] at hz; exact hz

/-- `|D|^p` does not see additive constants. -/
theorem c01_aux_fracD_add_const (p : ℝ) (g : ℝ → ℝ) (c y : ℝ) :
    fracD p (fun z => g z + c) y = fracD p g y := by
  unfold fracD; simp only [add_sub_add_right_eq_sub]

/-- A Lipschitz constant of `f'` on `[y-1,y+1]` for `f ∈ 𝒜`. -/
theorem c01_aux_lip (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) (y : ℝ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1),
      |deriv f z - deriv f w| ≤ Λ * |z - w| := by
  obtain ⟨K, hK⟩ := (hf.2.2.locallyLipschitzOn (s := Icc (y - 1) (y + 1))).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  refine ⟨K, K.2, fun z hz w hw => ?_⟩
  have := hK.dist_le_mul z hz w hw
  simpa [Real.dist_eq] using this

/-- `0 < A_ε(u) ≤ 1` for `ε ≥ 0`. -/
theorem c01_aux_A_bounds (p ε u : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) :
    0 < A_eps p ε u ∧ A_eps p ε u ≤ 1 := by
  unfold A_eps
  have h1 : 1 ≤ 1 + ε * u ^ 2 := by nlinarith [sq_nonneg u]
  exact ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)⟩

/-- Measurability of `z ↦ S_f(y,z)` for continuous `f`. -/
theorem c01_aux_secant_measurable (f : ℝ → ℝ) (hf : Continuous f) (y : ℝ) :
    Measurable (c01_secant f y) := by
  unfold c01_secant
  refine Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const ?_
  exact (measurable_const.sub hf.measurable).div (measurable_const.sub measurable_id)

/-- Measurability of `A_ε`. -/
theorem c01_aux_A_measurable (p ε : ℝ) : Measurable (A_eps p ε) := by
  unfold A_eps
  fun_prop

/-- `jb y ≥ 1`. -/
theorem c01_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := by
  unfold jb
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + y ^ 2 by nlinarith [sq_nonneg y])
  simpa using this

/-- `jb y ^ (-a) ≤ 1` for `a ≥ 0`. -/
theorem c01_aux_jb_rpow_neg_le_one (y a : ℝ) (ha : 0 ≤ a) : jb y ^ (-a) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (c01_aux_one_le_jb y) (by linarith)

/-! ### End of auxiliary lemmas -/

/-! ### Fourier conventions and the fractional multiplier -/

/-- Blueprint: lem:c01_frac_well_defined.  For `g ∈ L^∞` Lipschitz (constant `Λ`) on `[y-1,y+1]`,
the integrand of `|D|^p g(y)` is integrable and
`||D|^p g(y)| ≤ c_α (2Λ/(2-α) + 4‖g‖_∞/(α-1))`. -/
theorem c01_frac_well_defined (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ)
    (hgm : AEStronglyMeasurable g volume) (M : ℝ) (hM : ∀ᵐ z, |g z| ≤ M) (y Λ : ℝ)
    (hΛ : 0 ≤ Λ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1), |g z - g w| ≤ Λ * |z - w|) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) ∧
      |fracD p g y| ≤ calpha p * (2 * Λ / (2 - (p + 1)) + 4 * M / ((p + 1) - 1)) := by
  obtain ⟨hI, hB⟩ := c01_aux_frac_integrable p hp hp1 g hgm M hM y Λ hΛ hLip
  refine ⟨hI, ?_⟩
  have hc := c01_aux_calpha_nonneg p hp hp1
  unfold fracD
  rw [abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  exact (abs_integral_le_integral_abs).trans hB

/-- Blueprint: lem:c01_frac_affine.  `|D|^p ∂_y` only sees `f'` up to constants: if `f₁ - f₂` is
affine then `|D|^p∂_y f₁ = |D|^p∂_y f₂`; in particular `|D|^p∂_y f = |D|^p∂_y (f + y)
= |D|^p (f' + 1)`. -/
theorem c01_frac_affine (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ f₁ f₂ : ℝ → ℝ, f₁ ∈ c01_admissible_class → f₂ ∈ c01_admissible_class →
        (∃ a b : ℝ, ∀ y, f₁ y - f₂ y = a * y + b) →
        ∀ y, fracDdy p f₁ y = fracDdy p f₂ y) ∧
    (∀ f : ℝ → ℝ, f ∈ c01_admissible_class → ∀ y,
        fracDdy p f y = fracDdy p (fun z => f z + z) y ∧
        fracDdy p f y = fracD p (fun z => deriv f z + 1) y) := by
  refine ⟨fun f₁ f₂ _ h₂ ⟨a, b, hab⟩ y => ?_, fun f hf y => ?_⟩
  · have hf : f₁ = fun z => f₂ z + (a * z + b) := by
      funext z; linarith [hab z]
    have hd : deriv f₁ = fun z => deriv f₂ z + a := by
      funext z
      rw [hf]
      have h : HasDerivAt (fun z => f₂ z + (a * z + b)) (deriv f₂ z + a * 1) z :=
        (h₂.1.differentiable one_ne_zero z).hasDerivAt.add
          (((hasDerivAt_id z).const_mul a).add_const b)
      rw [h.deriv, mul_one]
    unfold fracDdy; rw [hd, c01_aux_fracD_add_const]
  · have hd : deriv (fun z => f z + z) = fun z => deriv f z + 1 := by
      funext z
      have h : HasDerivAt (fun z => f z + z) (deriv f z + 1) z :=
        (hf.1.differentiable one_ne_zero z).hasDerivAt.add (hasDerivAt_id z)
      exact h.deriv
    refine ⟨?_, ?_⟩ <;> simp only [fracDdy, hd, c01_aux_fracD_add_const]

/-! ### Auxiliary lemmas for lem:c01_frac_singular_integral -/

/-- A real Schwartz function is bounded and globally Lipschitz. -/
theorem c01_aux_schwartz_bdd_lip (g : SchwartzMap ℝ ℝ) :
    ∃ M Λ : ℝ, 0 ≤ Λ ∧ (∀ x, |g x| ≤ M) ∧ ∀ z w, |g z - g w| ≤ Λ * |z - w| := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 g, SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ g),
    apply_nonneg _ _, fun x => ?_, fun z w => ?_⟩
  · simpa using SchwartzMap.norm_le_seminorm ℝ g x
  · set L : NNReal := ⟨_, apply_nonneg (SchwartzMap.seminorm ℝ 0 0)
      (SchwartzMap.derivCLM ℝ ℝ g)⟩ with hLdef
    have hL : LipschitzWith L g := by
      refine lipschitzWith_of_nnnorm_deriv_le g.differentiable (fun x => ?_)
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      change ‖deriv g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ g)
      rw [← SchwartzMap.derivCLM_apply ℝ]
      exact SchwartzMap.norm_le_seminorm ℝ _ x
    have := hL.dist_le_mul z w
    have hc : (L : ℝ) = SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ g) := rfl
    rw [hc] at this
    simpa [Real.dist_eq] using this

/-- For real Schwartz `g` and `0<p<1`, the singular integrand is integrable. -/
theorem c01_aux_schwartz_frac_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : SchwartzMap ℝ ℝ)
    (y : ℝ) : Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) := by
  obtain ⟨M, Λ, hΛ, hM, hL⟩ := c01_aux_schwartz_bdd_lip g
  exact (c01_aux_frac_integrable p hp hp1 g g.continuous.aestronglyMeasurable M
    (Eventually.of_forall hM) y Λ hΛ (fun z _ w _ => hL z w)).1

/-- Symmetrization of the singular integral. -/
theorem c01_aux_symmetrize (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : SchwartzMap ℝ ℝ) (y : ℝ) :
    Integrable (fun h : ℝ => (2 * g y - g (y + h) - g (y - h)) / |h| ^ (p + 1)) ∧
    2 * ∫ z, (g y - g z) / |y - z| ^ (p + 1) =
      ∫ h, (2 * g y - g (y + h) - g (y - h)) / |h| ^ (p + 1) := by
  set φ : ℝ → ℝ := fun z => (g y - g z) / |y - z| ^ (p + 1)
  have hφ := c01_aux_schwartz_frac_integrable p hp hp1 g y
  have e1 : ∀ h, φ (y + h) = (g y - g (y + h)) / |h| ^ (p + 1) := fun h => by
    simp [φ, abs_neg]
  have e2 : ∀ h, φ (y - h) = (g y - g (y - h)) / |h| ^ (p + 1) := fun h => by
    simp [φ]
  have i1 : Integrable (fun h => φ (y + h)) := hφ.comp_add_left y
  have i2 : Integrable (fun h => φ (y - h)) := hφ.comp_sub_left y
  have hsum : ∀ h, (2 * g y - g (y + h) - g (y - h)) / |h| ^ (p + 1) = φ (y + h) + φ (y - h) := by
    intro h; rw [e1, e2]; ring
  simp_rw [hsum]
  refine ⟨i1.add i2, ?_⟩
  rw [integral_add i1 i2, integral_add_left_eq_self φ y, integral_sub_left_eq_self φ volume y]
  ring

/-- `‖e^{i x ξ}‖ = 1`. -/
theorem c01_aux_norm_exp_I (x ξ : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))‖ = 1 := by
  rw [show Complex.I * (x : ℂ) * (ξ : ℂ) = ((x * ξ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Properties of the Fourier transform of a real Schwartz function (`GSQG.Definitions` convention). -/
theorem c01_aux_hat (g : SchwartzMap ℝ ℝ) :
    Continuous (fourierT (fun x => ((g x : ℝ) : ℂ))) ∧
    Integrable (fourierT (fun x => ((g x : ℝ) : ℂ))) ∧
    Integrable (fun ξ => |ξ| * ‖fourierT (fun x => ((g x : ℝ) : ℂ)) ξ‖) ∧
    ∀ x, invFourierT (fourierT (fun x => ((g x : ℝ) : ℂ))) x = ((g x : ℝ) : ℂ) := by
  set gc : SchwartzMap ℝ ℂ := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM g
  have hgc : (fun x => ((g x : ℝ) : ℂ)) = ⇑gc := by
    funext x; simp [gc]
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hhat : fourierT (fun x => ((g x : ℝ) : ℂ)) = fun ξ => (𝓕 gc) (ξ / (2 * π)) := by
    funext ξ
    rw [hgc, fourierT, Lib.integral_mul_exp_neg_I_eq_fourier, SchwartzMap.fourier_coe]
  obtain ⟨hI, hinv⟩ := Lib.schwartz_fourier_inversion gc
  refine ⟨?_, ?_, ?_, fun x => ?_⟩
  · rw [hhat]; exact (𝓕 gc).continuous.comp (continuous_id.div_const _)
  · rw [hgc]; exact hI
  · rw [hhat]
    have := (SchwartzMap.integrable_pow_mul volume (𝓕 gc) 1).comp_div h2π
    refine (this.const_mul (2 * π)).congr (Eventually.of_forall fun ξ => ?_)
    simp only [pow_one, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    field_simp
  · rw [hgc]; unfold invFourierT fourierT
    exact hinv x

/-- Second difference via Fourier inversion:
`2g(y) - g(y+h) - g(y-h) = (2π)⁻¹ ∫ ĝ(ξ) e^{iyξ} 2(1 - cos hξ) dξ`. -/
theorem c01_aux_second_diff (g : SchwartzMap ℝ ℝ) (y h : ℝ) :
    ((2 * g y - g (y + h) - g (y - h) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ, fourierT (fun x => ((g x : ℝ) : ℂ)) ξ *
        Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) * ((2 * (1 - Real.cos (h * ξ)) : ℝ) : ℂ) := by
  obtain ⟨hc, hI, -, hinv⟩ := c01_aux_hat g
  set G := fourierT (fun x => ((g x : ℝ) : ℂ))
  have hint : ∀ x : ℝ, Integrable (fun ξ : ℝ => G ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) :=
    fun x => hI.mul_bdd (by fun_prop) (Eventually.of_forall fun ξ => (c01_aux_norm_exp_I x ξ).le)
  have e : ∀ x, ((g x : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, G ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) := fun x => (hinv x).symm
  rw [Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [e y, e (y + h), e (y - h)]
  rw [show ∀ a b c : ℂ, 2 * (((2 * π : ℝ) : ℂ)⁻¹ * a) - ((2 * π : ℝ) : ℂ)⁻¹ * b -
      ((2 * π : ℝ) : ℂ)⁻¹ * c = ((2 * π : ℝ) : ℂ)⁻¹ * (2 * a - b - c) by intros; ring]
  congr 1
  have i3 : Integrable (fun ξ : ℝ => 2 * (G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) -
      G ξ * Complex.exp (Complex.I * ((y + h : ℝ) : ℂ) * (ξ : ℂ))) :=
    ((hint y).const_mul 2).sub (hint (y + h))
  rw [← integral_const_mul, ← integral_sub ((hint y).const_mul 2) (hint (y + h)),
    ← integral_sub i3 (hint (y - h))]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have hcos := Complex.two_cos ((h : ℂ) * (ξ : ℂ))
  have h1 : Complex.exp (Complex.I * ((y + h : ℝ) : ℂ) * (ξ : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) * Complex.exp ((h : ℂ) * (ξ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have h2 : Complex.exp (Complex.I * ((y - h : ℝ) : ℂ) * (ξ : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) * Complex.exp (-((h : ℂ) * (ξ : ℂ)) * Complex.I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  push_cast at h1 h2 ⊢
  rw [h1, h2]
  linear_combination (G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) * hcos

/-- `c_α · π/(Γ(1+p) sin(πp/2)) = 1`. -/
theorem c01_aux_calpha_mul (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    calpha p * (π / (Real.Gamma (1 + p) * Real.sin (π * p / 2))) = 1 := by
  have hsin : 0 < Real.sin (π * p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have := Real.Gamma_pos_of_pos (show 0 < 1 + p by linarith)
  unfold calpha
  field_simp
  rw [div_self (by rw [show p * π / 2 = π * p / 2 by ring]; exact hsin.ne')]

/-- The singular-integral representation of `(|ξ|^p ĝ)^∨` for real Schwartz `g`
(first half of lem:c01_frac_singular_integral). -/
theorem c01_aux_frac_fourier (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : SchwartzMap ℝ ℝ) (y : ℝ) :
    fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (fun x => ((g x : ℝ) : ℂ)) y =
      ((fracD p (⇑g) y : ℝ) : ℂ) := by
  obtain ⟨hc, hI, hI1, -⟩ := c01_aux_hat g
  set G := fourierT (fun x => ((g x : ℝ) : ℂ))
  set K : ℝ := π / (Real.Gamma (1 + p) * Real.sin (π * p / 2))
  have hK : 0 ≤ K := by
    have hsin : 0 < Real.sin (π * p / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    have := Real.Gamma_pos_of_pos (show 0 < 1 + p by linarith)
    positivity
  set E : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))
  set k : ℝ → ℝ → ℝ := fun h ξ => 2 * (1 - Real.cos (h * ξ)) * |h| ^ (-1 - p)
  have hk0 : ∀ h ξ, 0 ≤ k h ξ := fun h ξ => by
    simp only [k]; have := Real.cos_le_one (h * ξ)
    have := Real.rpow_nonneg (abs_nonneg h) (-1 - p); nlinarith
  set f : ℝ → ℝ → ℂ := fun h ξ => G ξ * E ξ * ((k h ξ : ℝ) : ℂ)
  have hlib := Lib.integral_one_sub_cos_mul_abs_rpow hp (by linarith)
  -- inner integrals
  have hk_int : ∀ ξ, Integrable (fun h => k h ξ) ∧ ∫ h, k h ξ = 2 * |ξ| ^ p * K := by
    intro ξ
    obtain ⟨hi, hv⟩ := hlib ξ
    refine ⟨?_, ?_⟩
    · have := hi.const_mul 2
      refine this.congr (Eventually.of_forall fun h => ?_)
      simp only [k]; ring
    · simp only [k]
      simp_rw [mul_assoc]
      rw [integral_const_mul, hv]
  have hnormf : ∀ h ξ, ‖f h ξ‖ = ‖G ξ‖ * k h ξ := fun h ξ => by
    simp only [f, E, norm_mul, c01_aux_norm_exp_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hk0 h ξ)]
  have hGm : Measurable G := hc.measurable
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    simp only [f, E, k, Function.uncurry_def]
    fun_prop
  have hpow : Continuous (fun ξ : ℝ => |ξ| ^ p) :=
    continuous_abs.rpow_const (fun _ => Or.inr hp.le)
  have hbound : Integrable (fun ξ => ‖G ξ‖ * (2 * |ξ| ^ p * K)) := by
    refine Integrable.mono' ((hI.norm.add hI1).const_mul (2 * K)) (by fun_prop)
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := Real.rpow_nonneg (abs_nonneg ξ) p; positivity)]
    have hle : |ξ| ^ p ≤ 1 + |ξ| := by
      rcases le_total |ξ| 1 with h1 | h1
      · have := Real.rpow_le_one (abs_nonneg ξ) h1 hp.le; linarith [abs_nonneg ξ]
      · have := Real.rpow_le_rpow_of_exponent_le h1 hp1.le
        rw [Real.rpow_one] at this; linarith
    have := norm_nonneg (G ξ)
    calc ‖G ξ‖ * (2 * |ξ| ^ p * K) = 2 * K * (‖G ξ‖ * |ξ| ^ p) := by ring
      _ ≤ 2 * K * (‖G ξ‖ * (1 + |ξ|)) := by gcongr
      _ = 2 * K * (‖G ξ‖ + |ξ| * ‖G ξ‖) := by ring
  have hfI : Integrable (Function.uncurry f) (volume.prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair, f]
      exact (hk_int ξ).1.ofReal.const_mul _
    · refine hbound.congr (Eventually.of_forall fun ξ => ?_)
      simp only [Function.uncurry_apply_pair, hnormf]
      rw [integral_const_mul, (hk_int ξ).2]
  -- pointwise representation of the symmetrized integrand
  have hA : ∀ h : ℝ, (((2 * g y - g (y + h) - g (y - h)) / |h| ^ (p + 1) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, f h ξ := by
    intro h
    have hr : |h| ^ (-1 - p) = (|h| ^ (p + 1))⁻¹ := by
      rw [show -1 - p = -(p + 1) by ring, Real.rpow_neg (abs_nonneg h)]
    rw [div_eq_mul_inv, Complex.ofReal_mul, c01_aux_second_diff g y h, ← hr, mul_assoc,
      ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [f, k, E]
    push_cast; ring
  obtain ⟨hsymI, hsym⟩ := c01_aux_symmetrize p hp hp1 g y
  have hD : ((2 * ∫ z, (g y - g z) / |y - z| ^ (p + 1) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ((2 * K : ℝ) : ℂ) * ∫ ξ, ((|ξ| ^ p : ℝ) : ℂ) * G ξ * E ξ := by
    rw [hsym, ← integral_complex_ofReal]
    simp_rw [hA]
    rw [integral_const_mul, integral_integral_swap hfI, mul_assoc]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [f]
    rw [integral_const_mul, integral_complex_ofReal, (hk_int ξ).2]
    push_cast; ring
  unfold fourierMultiplier invFourierT fracD
  have hcK := c01_aux_calpha_mul p hp hp1
  have : ((calpha p * ∫ z, (g y - g z) / |y - z| ^ (p + 1) : ℝ) : ℂ) =
      ((calpha p / 2 : ℝ) : ℂ) * ((2 * ∫ z, (g y - g z) / |y - z| ^ (p + 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, hD]
  have h1 : ((calpha p / 2 : ℝ) : ℂ) * ((2 * K : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, show calpha p / 2 * (2 * K) = calpha p * K by ring, hcK]; simp
  linear_combination (-(((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, ((|ξ| ^ p : ℝ) : ℂ) * G ξ * E ξ)) * h1

/-- `(f')^(ξ) = iξ f̂(ξ)` for real Schwartz `f` (`GSQG.Definitions` convention). -/
theorem c01_aux_hat_deriv (f : SchwartzMap ℝ ℝ) (ξ : ℝ) :
    fourierT (fun x => ((deriv f x : ℝ) : ℂ)) ξ =
      Complex.I * ξ * fourierT (fun x => ((f x : ℝ) : ℂ)) ξ := by
  have hd : ∀ x, HasDerivAt (fun x => ((f x : ℝ) : ℂ)) ((deriv f x : ℝ) : ℂ) x := fun x =>
    (f.differentiableAt.hasDerivAt).ofReal_comp
  have hderiv : deriv (fun x => ((f x : ℝ) : ℂ)) = fun x => ((deriv f x : ℝ) : ℂ) := by
    funext x; exact (hd x).deriv
  have h1 : Integrable (fun x => ((f x : ℝ) : ℂ)) := (f.integrable (μ := volume)).ofReal (𝕜 := ℂ)
  have h2 : Integrable (fun x => ((deriv f x : ℝ) : ℂ)) := by
    have := ((SchwartzMap.derivCLM ℝ ℝ f).integrable (μ := volume)).ofReal (𝕜 := ℂ)
    simpa [SchwartzMap.derivCLM_apply] using this
  have := Lib.integral_deriv_mul_exp_neg_I h1 (fun x => (hd x).differentiableAt)
    (by rw [hderiv]; exact h2) ξ
  rw [hderiv] at this
  unfold fourierT
  exact this

/-- Second half of lem:c01_frac_singular_integral. -/
theorem c01_aux_frac_fourier_dy (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : SchwartzMap ℝ ℝ)
    (y : ℝ) :
    fourierMultiplier (fun ξ => Complex.I * (ξ : ℂ) * ((|ξ| ^ p : ℝ) : ℂ))
        (fun x => ((f x : ℝ) : ℂ)) y = ((fracDdy p (⇑f) y : ℝ) : ℂ) := by
  have h := c01_aux_frac_fourier p hp hp1 (SchwartzMap.derivCLM ℝ ℝ f) y
  have hfun : ⇑(SchwartzMap.derivCLM ℝ ℝ f) = deriv ⇑f := by
    funext x; exact SchwartzMap.derivCLM_apply ℝ f x
  rw [hfun] at h
  unfold fracDdy
  rw [← h]
  unfold fourierMultiplier
  congr 1
  funext ξ
  rw [c01_aux_hat_deriv]
  ring

-- Not in Mathlib; proved in this file.
/-- Blueprint: lem:c01_frac_singular_integral.  For `g ∈ 𝒮(ℝ)`,
`(|ξ|^p ĝ)^∨(y) = c_α ∫ (g(y)-g(z))/|y-z|^α dz` (with `c_α = calpha p`); consequently for
`f ∈ 𝒮(ℝ)`, `|D|^p∂_y f = (iξ|ξ|^p f̂)^∨`. -/
theorem c01_frac_singular_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ (g : SchwartzMap ℝ ℝ) (y : ℝ),
        fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (fun x => ((g x : ℝ) : ℂ)) y =
          ((fracD p (⇑g) y : ℝ) : ℂ)) ∧
    (∀ (f : SchwartzMap ℝ ℝ) (y : ℝ),
        fourierMultiplier (fun ξ => Complex.I * (ξ : ℂ) * ((|ξ| ^ p : ℝ) : ℂ))
            (fun x => ((f x : ℝ) : ℂ)) y =
          ((fracDdy p (⇑f) y : ℝ) : ℂ)) :=
  ⟨fun g y => c01_aux_frac_fourier p hp hp1 g y, fun f y => c01_aux_frac_fourier_dy p hp hp1 f y⟩

/-! ### Auxiliary lemmas for lem:c01_frac_duality -/

/-- `⟨·⟩` is 1-Lipschitz: `⟨t⟩ ≤ ⟨y⟩ + |t - y|`. -/
theorem c01_aux_jb_le (t y : ℝ) : jb t ≤ jb y + |t - y| := by
  unfold jb
  have h1 : 0 ≤ Real.sqrt (1 + y ^ 2) := Real.sqrt_nonneg _
  have hy : |y| ≤ Real.sqrt (1 + y ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_le_left (by positivity)]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 1 + y ^ 2 by positivity)
  have ht : t ^ 2 ≤ y ^ 2 + 2 * |y| * |t - y| + |t - y| ^ 2 := by
    have : t = y + (t - y) := by ring
    have e : t ^ 2 = y ^ 2 + 2 * y * (t - y) + (t - y) ^ 2 := by ring
    rw [e, sq_abs]
    have : y * (t - y) ≤ |y| * |t - y| := by rw [← abs_mul]; exact le_abs_self _
    linarith
  nlinarith [abs_nonneg (t - y)]

/-- A locally Lipschitz `g` with `|g'| ≤ C⟨·⟩^N` a.e. is Lipschitz on `[y-r, y+r]` with constant
`C (⟨y⟩ + r)^N`. -/
theorem c01_aux_lip_of_deriv (g : ℝ → ℝ) (hg : LocallyLipschitz g) (C N : ℝ) (hC : 0 ≤ C)
    (hN : 0 ≤ N) (hd : ∀ᵐ y, |deriv g y| ≤ C * jb y ^ N) (y r : ℝ) :
    ∀ z ∈ Icc (y - r) (y + r), ∀ w ∈ Icc (y - r) (y + r),
      |g z - g w| ≤ C * (jb y + r) ^ N * |z - w| := by
  have key : ∀ z ∈ Icc (y - r) (y + r), ∀ w ∈ Icc (y - r) (y + r), z ≤ w →
      |g z - g w| ≤ C * (jb y + r) ^ N * |z - w| := by
    intro z hz w hw hzw
    obtain ⟨K, hK⟩ := (hg.locallyLipschitzOn (s := uIcc z w)).exists_lipschitzOnWith_of_compact
      isCompact_uIcc
    have hac := hK.absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_eq_sub
    have hb : ∀ᵐ t, t ∈ Ioc z w → ‖deriv g t‖ ≤ C * (jb y + r) ^ N := by
      filter_upwards [hd] with t ht htI
      rw [Real.norm_eq_abs]
      refine ht.trans (mul_le_mul_of_nonneg_left ?_ hC)
      apply Real.rpow_le_rpow (by unfold jb; positivity) _ hN
      have := c01_aux_jb_le t y
      have : |t - y| ≤ r := by
        rw [abs_le]; constructor <;> linarith [htI.1, htI.2, hz.1, hz.2, hw.1, hw.2]
      linarith
    have := intervalIntegral.norm_integral_le_of_norm_le hzw hb intervalIntegrable_const
    rw [hftc, intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs] at this
    rw [abs_sub_comm, abs_sub_comm z w, abs_of_nonneg (by linarith : 0 ≤ w - z)]
    linarith
  intro z hz w hw
  rcases le_total z w with h | h
  · exact key z hz w hw h
  · rw [abs_sub_comm, abs_sub_comm z w]; exact key w hw z hz h

/-- Under the hypotheses of lem:c01_frac_duality: `|g| ≤ M` everywhere, and the singular
integrand at `y` is integrable with `∫ |…| ≤ B ⟨y⟩^N`. -/
theorem c01_aux_duality_kernel_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (M C N : ℝ)
    (hM : ∀ᵐ z, |g z| ≤ M) (hg : LocallyLipschitz g) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hd : ∀ᵐ y, |deriv g y| ≤ C * jb y ^ N) :
    0 ≤ M ∧ (∀ y, |g y| ≤ M) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
      Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) ∧
      ∫ z, |(g y - g z) / |y - z| ^ (p + 1)| ≤ B * jb y ^ N := by
  have hgm : AEStronglyMeasurable g volume := hg.continuous.aestronglyMeasurable
  have hLip := c01_aux_lip_of_deriv g hg C N hC hN hd
  have hpt : ∀ y, |g y| ≤ M ∧ 0 ≤ M := fun y =>
    c01_aux_point_bound g M hM y (C * (jb y + 1) ^ N)
      (by have : 0 ≤ jb y + 1 := by unfold jb; positivity
          positivity) (hLip y 1)
  have hM0 := (hpt 0).2
  refine ⟨hM0, fun y => (hpt y).1, 2 * C * 2 ^ N / (1 - p) + 4 * M / p, by
    have : 0 < 1 - p := by linarith
    positivity, fun y => ?_⟩
  have hjb := c01_aux_one_le_jb y
  have hΛ0 : 0 ≤ C * (jb y + 1) ^ N := by positivity
  obtain ⟨hI, hB⟩ := c01_aux_frac_integrable p hp hp1 g hgm M hM y _ hΛ0 (hLip y 1)
  refine ⟨hI, hB.trans ?_⟩
  have h1 : (jb y + 1) ^ N ≤ 2 ^ N * jb y ^ N := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hN
  have h2 : 1 ≤ jb y ^ N := Real.one_le_rpow hjb hN
  have e1 : (2 : ℝ) - (p + 1) = 1 - p := by ring
  have e2 : (p + 1 : ℝ) - 1 = p := by ring
  rw [e1, e2]
  have h1p : 0 < 1 - p := by linarith
  have hA : 2 * (C * (jb y + 1) ^ N) / (1 - p) ≤ 2 * C * 2 ^ N / (1 - p) * jb y ^ N := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ h1p.le
    nlinarith
  have hB' : 4 * M / p ≤ 4 * M / p * jb y ^ N := by
    have : 0 ≤ 4 * M / p := by positivity
    nlinarith
  nlinarith

/-- Pointwise domination of the translated singular integrand by the radial function `ψ`. -/
theorem c01_aux_psi_dom (p : ℝ) (hp : 0 < p) (g : ℝ → ℝ) (M : ℝ) (hM : ∀ z, |g z| ≤ M)
    (y Λ : ℝ) (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1),
      |g z - g w| ≤ Λ * |z - w|) (h : ℝ) :
    |(g y - g (y + h)) / |h| ^ (p + 1)| ≤ c01_aux_psi p Λ M |h| := by
  rcases eq_or_ne h 0 with h0 | h0
  · subst h0
    simp only [add_zero, sub_self, zero_div, abs_zero, c01_aux_psi, zero_le_one, ite_true]
    rw [Real.zero_rpow (by linarith)]; simp
  have hpos : 0 < |h| := abs_pos.mpr h0
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hpos _), div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
  simp only [c01_aux_psi]
  split_ifs with h1
  · have hz' : y + h ∈ Icc (y - 1) (y + 1) := by
      rw [abs_le] at h1; exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hy' : y ∈ Icc (y - 1) (y + 1) := ⟨by linarith, by linarith⟩
    have hl := hLip y hy' (y + h) hz'
    rw [show y - (y + h) = -h by ring, abs_neg] at hl
    calc |g y - g (y + h)| ≤ Λ * |h| := hl
      _ = Λ * |h| ^ (-p) * |h| ^ (p + 1) := by
        rw [mul_assoc, ← Real.rpow_add hpos]; simp
  · calc |g y - g (y + h)| ≤ |g y| + |g (y + h)| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM y, hM (y + h)]
      _ = 2 * M * |h| ^ (-(p + 1)) * |h| ^ (p + 1) := by
        rw [mul_assoc, ← Real.rpow_add hpos]; simp

/-- `|D|^p g` written with `z = y + h`. -/
theorem c01_aux_fracD_shift (p : ℝ) (g : ℝ → ℝ) (y : ℝ) :
    fracD p g y = calpha p * ∫ h, (g y - g (y + h)) / |h| ^ (p + 1) := by
  unfold fracD
  congr 1
  rw [← integral_add_left_eq_self (fun z => (g y - g z) / |y - z| ^ (p + 1)) y]
  congr 1; funext h; simp [abs_neg]

/-- Continuity of `|D|^p g` for bounded locally Lipschitz `g`. -/
theorem c01_aux_fracD_continuous (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (M : ℝ)
    (hM : ∀ z, |g z| ≤ M) (hg : LocallyLipschitz g) : Continuous (fracD p g) := by
  have hgc := hg.continuous
  rw [continuous_iff_continuousAt]
  intro y0
  obtain ⟨K, hK⟩ := (hg.locallyLipschitzOn (s := Icc (y0 - 2) (y0 + 2))).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  have hLip : ∀ y ∈ Ioo (y0 - 1) (y0 + 1), ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1),
      |g z - g w| ≤ (K : ℝ) * |z - w| := by
    intro y hy z hz w hw
    have hz' : z ∈ Icc (y0 - 2) (y0 + 2) := ⟨by linarith [hy.1, hz.1], by linarith [hy.2, hz.2]⟩
    have hw' : w ∈ Icc (y0 - 2) (y0 + 2) := ⟨by linarith [hy.1, hw.1], by linarith [hy.2, hw.2]⟩
    have := hK.dist_le_mul z hz' w hw'
    simpa [Real.dist_eq] using this
  have hfun : fracD p g = fun y => calpha p * ∫ h, (g y - g (y + h)) / |h| ^ (p + 1) := by
    funext y; exact c01_aux_fracD_shift p g y
  rw [hfun]
  apply ContinuousAt.mul continuousAt_const
  obtain ⟨hψi, -⟩ := c01_aux_psi_integral p K M hp hp1
  have hψ := c01_aux_integrable_comp_abs hψi
  have hnhds : Ioo (y0 - 1) (y0 + 1) ∈ 𝓝 y0 := Ioo_mem_nhds (by linarith) (by linarith)
  apply continuousAt_of_dominated (bound := fun h => c01_aux_psi p K M |h|)
  · refine Eventually.of_forall fun y => ?_
    have : Measurable (fun h : ℝ => (|h| ^ (p + 1))⁻¹) := by fun_prop
    simp only [div_eq_mul_inv]
    exact ((continuous_const.sub (hgc.comp (continuous_const.add continuous_id))).measurable.mul
      this).aestronglyMeasurable
  · filter_upwards [hnhds] with y hy
    exact Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs]; exact c01_aux_psi_dom p hp g M hM y K (hLip y hy) h
  · exact hψ
  · refine Eventually.of_forall fun h => ?_
    apply Continuous.continuousAt
    exact ((hgc.sub (hgc.comp (continuous_id.add continuous_const))).div_const _)

/-- The radial dominating function with threshold `R`. -/
def c01_aux_psiR (p a b R t : ℝ) : ℝ :=
  if t ≤ R then a * t ^ (-p) else b * t ^ (-(p + 1))

/-- Integral of `c01_aux_psiR` over `(0,∞)`. -/
theorem c01_aux_psiR_integral (p a b R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 0 < R) :
    IntegrableOn (c01_aux_psiR p a b R) (Ioi 0) ∧
      ∫ t in Ioi 0, c01_aux_psiR p a b R t = a * R ^ (1 - p) / (1 - p) + b * R ^ (-p) / p := by
  have hIoc : IntegrableOn (fun t : ℝ => a * t ^ (-p)) (Ioc 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (r := -p) (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le] at this
    exact this.const_mul a
  have hIoi : IntegrableOn (fun t : ℝ => b * t ^ (-(p + 1))) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hR).const_mul _
  have e1 : EqOn (c01_aux_psiR p a b R) (fun t : ℝ => a * t ^ (-p)) (Ioc 0 R) := by
    intro t ht; simp [c01_aux_psiR, ht.2]
  have e2 : EqOn (c01_aux_psiR p a b R) (fun t : ℝ => b * t ^ (-(p + 1))) (Ioi R) := by
    intro t ht; simp [c01_aux_psiR, not_le.mpr (show R < t from ht)]
  have i1 : IntegrableOn (c01_aux_psiR p a b R) (Ioc 0 R) :=
    hIoc.congr_fun e1.symm measurableSet_Ioc
  have i2 : IntegrableOn (c01_aux_psiR p a b R) (Ioi R) :=
    hIoi.congr_fun e2.symm measurableSet_Ioi
  have hU : Ioc (0:ℝ) R ∪ Ioi R = Ioi 0 := Ioc_union_Ioi_eq_Ioi hR.le
  refine ⟨hU ▸ i1.union i2, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
    setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hR,
    ← intervalIntegral.integral_of_le hR.le, integral_rpow (Or.inl (by linarith))]
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have hp0 : p ≠ 0 := hp.ne'
  have h0 : (0 : ℝ) ^ (-p + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, show -p + 1 = 1 - p by ring, show -(p + 1) + 1 = -p by ring]
  field_simp
  ring

/-- `⟨w⟩² = 1 + w²`. -/
theorem c01_aux_jb_sq (w : ℝ) : jb w ^ 2 = 1 + w ^ 2 := by
  unfold jb; rw [Real.sq_sqrt (by positivity)]

/-- Decay of a real Schwartz function and its derivative: `|φ|, |φ'| ≤ A ⟨w⟩^{-2}`. -/
theorem c01_aux_schwartz_decay (φ : SchwartzMap ℝ ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w, |φ w| ≤ A / jb w ^ 2 ∧ |deriv φ w| ≤ A / jb w ^ 2 := by
  set A := SchwartzMap.seminorm ℝ 0 0 φ + SchwartzMap.seminorm ℝ 2 0 φ +
    SchwartzMap.seminorm ℝ 0 1 φ + SchwartzMap.seminorm ℝ 2 1 φ
  have h00 := SchwartzMap.le_seminorm' ℝ 0 0 φ
  have h20 := SchwartzMap.le_seminorm' ℝ 2 0 φ
  have h01 := SchwartzMap.le_seminorm' ℝ 0 1 φ
  have h21 := SchwartzMap.le_seminorm' ℝ 2 1 φ
  simp only [iteratedDeriv_zero, iteratedDeriv_one, pow_zero, one_mul, Real.norm_eq_abs,
    sq_abs] at h00 h20 h01 h21
  have n1 := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) φ
  have n2 := apply_nonneg (SchwartzMap.seminorm ℝ 2 0) φ
  have n3 := apply_nonneg (SchwartzMap.seminorm ℝ 0 1) φ
  have n4 := apply_nonneg (SchwartzMap.seminorm ℝ 2 1) φ
  refine ⟨A, by positivity, fun w => ⟨?_, ?_⟩⟩
  · rw [c01_aux_jb_sq, le_div_iff₀ (by positivity)]
    have := h00 w; have := h20 w
    nlinarith
  · rw [c01_aux_jb_sq, le_div_iff₀ (by positivity)]
    have := h01 w; have := h21 w
    nlinarith

/-- Power bookkeeping for `J = ⟨y⟩ ≥ 1`, `X = J^{-(p+1)}`. -/
theorem c01_aux_J_powers (p J : ℝ) (hp : 0 < p) (hp1 : p < 1) (hJ : 1 ≤ J) :
    (J / 2) ^ (1 - p) / J ^ 2 ≤ J ^ (-(p + 1)) ∧
    (J / 2) ^ (-p) / J ^ 2 ≤ 2 * J ^ (-(p + 1)) ∧
    (J / 2) ^ (-(p + 1)) ≤ 4 * J ^ (-(p + 1)) := by
  have hJ0 : 0 < J := by linarith
  have hJ2 : (0:ℝ) < J ^ 2 := by positivity
  have hsq : J ^ 2 = J ^ (2:ℝ) := by norm_cast
  have hdiv : ∀ r : ℝ, (J / 2) ^ r = J ^ r * (2:ℝ) ^ (-r) := fun r => by
    rw [Real.div_rpow hJ0.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hJ2, hsq, ← Real.rpow_add hJ0]
    calc (J / 2) ^ (1 - p) ≤ J ^ (1 - p) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = J ^ (-(p + 1) + 2) := by ring_nf
  · rw [div_le_iff₀ hJ2, hsq, hdiv, mul_assoc, ← Real.rpow_add hJ0]
    have h2 : (2:ℝ) ^ (-(-p)) ≤ 2 := by
      rw [neg_neg]
      calc (2:ℝ) ^ p ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
        _ = 2 := by simp
    have h3 : J ^ (-p) ≤ J ^ (-(p + 1) + 2) :=
      Real.rpow_le_rpow_of_exponent_le hJ (by linarith)
    have := Real.rpow_nonneg hJ0.le (-p)
    have := Real.rpow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (-(-p))
    nlinarith
  · rw [hdiv]
    have h2 : (2:ℝ) ^ (-(-(p + 1))) ≤ 4 := by
      rw [neg_neg]
      calc (2:ℝ) ^ (p + 1) ≤ 2 ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have := Real.rpow_nonneg hJ0.le (-(p + 1))
    nlinarith

/-- Decay of the singular integrand of `|D|^p φ` for Schwartz `φ`:
`∫ |(φ(y) - φ(y+h))/|h|^α| dh ≤ C_φ ⟨y⟩^{-α}`. -/
theorem c01_aux_schwartz_kernel_decay (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (φ : SchwartzMap ℝ ℝ) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ y, Integrable (fun h => (φ y - φ (y + h)) / |h| ^ (p + 1)) ∧
      ∫ h, |(φ y - φ (y + h)) / |h| ^ (p + 1)| ≤ Cφ * jb y ^ (-(p + 1)) := by
  obtain ⟨A, hA, hdec⟩ := c01_aux_schwartz_decay φ
  set L1 := ∫ x, |φ x|
  have hL1 : 0 ≤ L1 := integral_nonneg fun _ => abs_nonneg _
  have hφi : Integrable (fun x => |φ x|) := φ.integrable.abs
  have h1p : 0 < 1 - p := by linarith
  refine ⟨2 * (4 * A / (1 - p) + 2 * A / p) + 4 * L1, by positivity, fun y => ?_⟩
  set J := jb y
  have hJ : 1 ≤ J := c01_aux_one_le_jb y
  have hJ0 : 0 < J := by linarith
  set R := J / 2
  have hR : 0 < R := by positivity
  set a := 4 * A / J ^ 2
  set b := |φ y|
  have hb : b ≤ A / J ^ 2 := (hdec y).1
  have ha : 0 ≤ a := by positivity
  set D : ℝ → ℝ := fun h => c01_aux_psiR p a b R |h| + R ^ (-(p + 1)) * |φ (y + h)|
  obtain ⟨hψi, hψ⟩ := c01_aux_psiR_integral p a b R hp hp1 hR
  have hDi : Integrable D :=
    (c01_aux_integrable_comp_abs hψi).add ((hφi.comp_add_left y).const_mul _)
  have hDint : ∫ h, D h = 2 * (a * R ^ (1 - p) / (1 - p) + b * R ^ (-p) / p) +
      R ^ (-(p + 1)) * L1 := by
    simp only [D]
    rw [integral_add (c01_aux_integrable_comp_abs hψi) ((hφi.comp_add_left y).const_mul _),
      integral_comp_abs (f := c01_aux_psiR p a b R), hψ, integral_const_mul,
      integral_add_left_eq_self (fun x => |φ x|) y]
  -- the derivative bound near `y`
  have hnear : ∀ w ∈ Icc (y - R) (y + R), ‖deriv φ w‖ ≤ a := by
    intro w hw
    have hjw : J / 2 ≤ jb w := by
      have := c01_aux_jb_le y w
      have : |y - w| ≤ R := by rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
      simp only [R] at this; linarith
    rw [Real.norm_eq_abs]
    refine (hdec w).2.trans ?_
    simp only [a]
    rw [div_le_div_iff₀ (by have := c01_aux_one_le_jb w; positivity) (by positivity)]
    have : J ^ 2 ≤ 4 * jb w ^ 2 := by nlinarith
    nlinarith
  have hbound : ∀ h, |(φ y - φ (y + h)) / |h| ^ (p + 1)| ≤ D h := by
    intro h
    have hextra : 0 ≤ R ^ (-(p + 1)) * |φ (y + h)| := by positivity
    rcases eq_or_ne h 0 with h0 | h0
    · subst h0
      have : 0 ≤ c01_aux_psiR p a b R |0| := by
        simp only [c01_aux_psiR, abs_zero]; split_ifs
        · rw [Real.zero_rpow (by linarith)]; simp
        · linarith
      simp only [D, add_zero, sub_self, zero_div, abs_zero]
      simp only [abs_zero] at this; simp only [add_zero] at hextra; linarith
    have hpos : 0 < |h| := abs_pos.mpr h0
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    simp only [D, c01_aux_psiR]
    split_ifs with h1
    · have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun x _ => φ.differentiableAt) hnear (convex_Icc (y - R) (y + R))
        (show y + h ∈ Icc (y - R) (y + R) by
          rw [abs_le] at h1; exact ⟨by linarith [h1.1], by linarith [h1.2]⟩)
        (show y ∈ Icc (y - R) (y + R) by constructor <;> linarith)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, show y - (y + h) = -h by ring, abs_neg] at hmv
      have : |φ y - φ (y + h)| / |h| ^ (p + 1) ≤ a * |h| ^ (-p) := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _), mul_assoc, ← Real.rpow_add hpos,
          show -p + (p + 1) = 1 by ring, Real.rpow_one]
        exact hmv
      linarith
    · have hRh : R < |h| := not_le.mp h1
      have hle : |h| ^ (-(p + 1)) ≤ R ^ (-(p + 1)) :=
        Real.rpow_le_rpow_of_nonpos hR hRh.le (by linarith)
      have e : |φ y - φ (y + h)| / |h| ^ (p + 1) ≤
          b * |h| ^ (-(p + 1)) + |φ (y + h)| * |h| ^ (-(p + 1)) := by
        rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, ← div_eq_mul_inv, ← add_div]
        exact div_le_div_of_nonneg_right (abs_sub _ _) (by positivity)
      have : |φ (y + h)| * |h| ^ (-(p + 1)) ≤ R ^ (-(p + 1)) * |φ (y + h)| := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      linarith
  have hmeas : AEStronglyMeasurable (fun h => (φ y - φ (y + h)) / |h| ^ (p + 1)) volume := by
    have : Measurable (fun h : ℝ => (|h| ^ (p + 1))⁻¹) := by fun_prop
    simp only [div_eq_mul_inv]
    exact ((continuous_const.sub (φ.continuous.comp (continuous_const.add continuous_id))).measurable.mul
      this).aestronglyMeasurable
  have hFi : Integrable (fun h => (φ y - φ (y + h)) / |h| ^ (p + 1)) :=
    Integrable.mono' hDi hmeas (Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs]; exact hbound h)
  refine ⟨hFi, ?_⟩
  have hle := integral_mono hFi.abs hDi hbound
  refine hle.trans ?_
  rw [hDint]
  obtain ⟨f1, f2, f3⟩ := c01_aux_J_powers p J hp hp1 hJ
  set X := J ^ (-(p + 1))
  have hX : 0 ≤ X := Real.rpow_nonneg hJ0.le _
  have T1 : a * R ^ (1 - p) ≤ 4 * A * X := by
    simp only [a, R]
    calc 4 * A / J ^ 2 * (J / 2) ^ (1 - p) = 4 * A * ((J / 2) ^ (1 - p) / J ^ 2) := by ring
      _ ≤ 4 * A * X := by gcongr
  have T2 : b * R ^ (-p) ≤ 2 * A * X := by
    have hRp : 0 ≤ R ^ (-p) := Real.rpow_nonneg hR.le _
    calc b * R ^ (-p) ≤ A / J ^ 2 * R ^ (-p) := by gcongr
      _ = A * ((J / 2) ^ (-p) / J ^ 2) := by simp only [R]; ring
      _ ≤ A * (2 * X) := by gcongr
      _ = 2 * A * X := by ring
  have T3 : R ^ (-(p + 1)) * L1 ≤ 4 * X * L1 := by
    gcongr
  have : 2 * (a * R ^ (1 - p) / (1 - p) + b * R ^ (-p) / p) ≤
      2 * (4 * A * X / (1 - p) + 2 * A * X / p) := by
    gcongr
  calc 2 * (a * R ^ (1 - p) / (1 - p) + b * R ^ (-p) / p) + R ^ (-(p + 1)) * L1
      ≤ 2 * (4 * A * X / (1 - p) + 2 * A * X / p) + 4 * X * L1 := by linarith
    _ = (2 * (4 * A / (1 - p) + 2 * A / p) + 4 * L1) * X := by ring

/-- The truncated kernel `κ_δ(h) = 𝟙_{δ<|h|} |h|^{-α}`. -/
def c01_aux_kappa (p δ h : ℝ) : ℝ := (Ioi δ).indicator (fun t : ℝ => t ^ (-(p + 1))) |h|

theorem c01_aux_kappa_props (p δ : ℝ) (hp : 0 < p) (hδ : 0 < δ) :
    Integrable (c01_aux_kappa p δ) ∧ (∀ h, c01_aux_kappa p δ (-h) = c01_aux_kappa p δ h) ∧
    Measurable (c01_aux_kappa p δ) ∧ ∀ h, 0 ≤ c01_aux_kappa p δ h ∧
      c01_aux_kappa p δ h ≤ |h| ^ (-(p + 1)) := by
  refine ⟨?_, fun h => by simp [c01_aux_kappa], ?_, fun h => ⟨?_, ?_⟩⟩
  · have hi : IntegrableOn ((Ioi δ).indicator (fun t : ℝ => t ^ (-(p + 1)))) (Ioi 0) := by
      have := (integrableOn_Ioi_rpow_of_lt (show -(p + 1) < -1 by linarith) hδ).integrable_indicator
        measurableSet_Ioi
      exact this.integrableOn
    exact c01_aux_integrable_comp_abs hi
  · unfold c01_aux_kappa
    exact (Measurable.indicator (by fun_prop) measurableSet_Ioi).comp measurable_abs
  · unfold c01_aux_kappa
    exact Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (by
      have := (show t ∈ Ioi δ from by assumption); exact le_of_lt (lt_trans hδ this)) _) _
  · unfold c01_aux_kappa
    by_cases hh : |h| ∈ Ioi δ
    · rw [Set.indicator_of_mem hh]
    · rw [Set.indicator_of_notMem hh]; exact Real.rpow_nonneg (abs_nonneg _) _

/-- The truncated duality identity: for an even integrable kernel `κ`, bounded continuous `g`
and Schwartz `φ`,
`∫ (∫ κ(h)(g(y)-g(y+h)) dh) φ(y) dy = ∫ g(y) ∫ κ(h)(φ(y)-φ(y+h)) dh dy`. -/
theorem c01_aux_trunc_identity {κ : ℝ → ℝ} (hκ : Integrable κ) (heven : ∀ h, κ (-h) = κ h)
    (g : ℝ → ℝ) (hgc : Continuous g) (M : ℝ) (hM : ∀ y, |g y| ≤ M) (φ : SchwartzMap ℝ ℝ) :
    ∫ y, (∫ h, κ h * (g y - g (y + h))) * φ y = ∫ y, g y * ∫ h, κ h * (φ y - φ (y + h)) := by
  set c := ∫ h, κ h
  have hφi : Integrable (⇑φ) := φ.integrable
  obtain ⟨Mφ, -, -, hMφ, -⟩ := c01_aux_schwartz_bdd_lip φ
  have hsplit : ∀ (w : ℝ → ℝ), Continuous w → ∀ Mw, (∀ y, |w y| ≤ Mw) → ∀ y,
      ∫ h, κ h * (w y - w (y + h)) = w y * c - ∫ h, κ h * w (y + h) := by
    intro w hw Mw hMw y
    have i1 : Integrable (fun h => κ h * w y) := hκ.mul_const _
    have i2 : Integrable (fun h => κ h * w (y + h)) :=
      hκ.mul_bdd (hw.comp (continuous_const.add continuous_id)).aestronglyMeasurable
        (Eventually.of_forall fun h => by rw [Real.norm_eq_abs]; exact hMw _)
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, mul_comm]
  set Gκ : ℝ → ℝ := fun y => ∫ h, κ h * g (y + h)
  set Φκ : ℝ → ℝ := fun y => ∫ h, κ h * φ (y + h)
  have hGm : AEStronglyMeasurable Gκ volume := by
    have : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.2 * g (z.1 + z.2)) (volume.prod volume) :=
      (hκ.aestronglyMeasurable.comp_snd).mul (hgc.comp continuous_add).aestronglyMeasurable
    exact this.integral_prod_right'
  have hGb : ∀ y, ‖Gκ y‖ ≤ ∫ h, ‖κ h‖ * M := by
    intro y
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _) (hκ.norm.mul_const _)
      (Eventually.of_forall fun h => ?_))
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  have hΦi : Integrable Φκ := by
    have hF : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.2 * φ (z.1 + z.2)) (volume.prod volume) :=
      (hκ.aestronglyMeasurable.comp_snd).mul (φ.continuous.comp continuous_add).aestronglyMeasurable
    have hint : ∀ h, Integrable (fun y => (fun z : ℝ × ℝ => κ z.2 * φ (z.1 + z.2)) (y, h)) :=
      fun h => (hφi.comp_add_right h).const_mul (κ h)
    have hb : ∀ y h, |(fun z : ℝ × ℝ => κ z.2 * φ (z.1 + z.2)) (y, h)| ≤
        1 * |κ h| * |φ (y + 1 * h)| := fun y h => by
      simp only [one_mul, abs_mul, le_refl]
    have := Lib.integrable_corr_aux hF hκ hφi 1 1 hint hb
    exact this.integral_prod_left
  have i1 : Integrable (fun y => φ y * Gκ y) :=
    hφi.mul_bdd hGm (Eventually.of_forall hGb)
  have i2 : Integrable (fun y => g y * Φκ y) :=
    hΦi.bdd_mul hgc.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hM y)
  have i0 : Integrable (fun y => g y * φ y) :=
    hφi.bdd_mul hgc.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hM y)
  have eL : ∀ y, (∫ h, κ h * (g y - g (y + h))) * φ y = c * (g y * φ y) - φ y * Gκ y := by
    intro y; rw [hsplit g hgc M hM y]; ring
  have eR : ∀ y, g y * ∫ h, κ h * (φ y - φ (y + h)) = c * (g y * φ y) - g y * Φκ y := by
    intro y; rw [hsplit φ φ.continuous Mφ hMφ y]; ring
  simp_rw [eL, eR]
  rw [integral_sub (i0.const_mul c) i1, integral_sub (i0.const_mul c) i2]
  congr 1
  exact Lib.integral_corr_symm hκ heven hφi φ.continuous hgc M hM

/-- Removing the truncation: `∫ κ_{1/(n+1)}(h)(w(y)-w(y+h)) dh → ∫ (w(y)-w(y+h))/|h|^α dh`,
with the bound `|∫ κ_δ(…)| ≤ ∫ |(w(y)-w(y+h))/|h|^α|`. -/
theorem c01_aux_untruncate (p : ℝ) (hp : 0 < p) (w : ℝ → ℝ) (hw : Continuous w) (y : ℝ)
    (hI : Integrable (fun h => (w y - w (y + h)) / |h| ^ (p + 1))) :
    Tendsto (fun n : ℕ => ∫ h, c01_aux_kappa p (1 / ((n : ℝ) + 1)) h * (w y - w (y + h)))
      atTop (𝓝 (∫ h, (w y - w (y + h)) / |h| ^ (p + 1))) ∧
    ∀ n : ℕ, |∫ h, c01_aux_kappa p (1 / ((n : ℝ) + 1)) h * (w y - w (y + h))| ≤
      ∫ h, |(w y - w (y + h)) / |h| ^ (p + 1)| := by
  have hδ : ∀ n : ℕ, (0:ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hbd : ∀ (n : ℕ) h, |c01_aux_kappa p (1 / ((n : ℝ) + 1)) h * (w y - w (y + h))| ≤
      |(w y - w (y + h)) / |h| ^ (p + 1)| := by
    intro n h
    obtain ⟨-, -, -, hk⟩ := c01_aux_kappa_props p _ hp (hδ n)
    obtain ⟨hk0, hk1⟩ := hk h
    rw [abs_mul, abs_of_nonneg hk0, div_eq_mul_inv (w y - w (y + h)), abs_mul, mul_comm,
      ← Real.rpow_neg (abs_nonneg h), abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
    exact mul_le_mul_of_nonneg_left hk1 (abs_nonneg _)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun h => c01_aux_kappa p (1 / ((n : ℝ) + 1)) h * (w y - w (y + h))) volume := by
    intro n
    obtain ⟨-, -, hm, -⟩ := c01_aux_kappa_props p _ hp (hδ n)
    exact hm.aestronglyMeasurable.mul
      ((continuous_const.sub (hw.comp (continuous_const.add continuous_id))).aestronglyMeasurable)
  refine ⟨?_, fun n => ?_⟩
  · refine tendsto_integral_of_dominated_convergence (fun h => |(w y - w (y + h)) / |h| ^ (p + 1)|)
      hmeas hI.abs (fun n => Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs]; exact hbd n h) (Eventually.of_forall fun h => ?_)
    rcases eq_or_ne h 0 with h0 | h0
    · subst h0; simp
    · obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt (abs_pos.mpr h0)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n0] with n hn
      have hlt : 1 / ((n : ℝ) + 1) < |h| := by
        refine lt_of_le_of_lt ?_ hn0
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hn 1
      unfold c01_aux_kappa
      rw [Set.indicator_of_mem (show |h| ∈ Ioi (1 / ((n : ℝ) + 1)) from hlt),
        Real.rpow_neg (abs_nonneg h), div_eq_mul_inv, mul_comm]
  · exact (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) hI.abs (Eventually.of_forall (hbd n)))

/-- The duality identity (real form) for the translated singular integrals. -/
theorem c01_aux_duality_real (p : ℝ) (hp : 0 < p) (g : ℝ → ℝ) (hgc : Continuous g)
    (M : ℝ) (hM : ∀ y, |g y| ≤ M) (B N : ℝ)
    (hFb : ∀ y, Integrable (fun h => (g y - g (y + h)) / |h| ^ (p + 1)) ∧
      ∫ h, |(g y - g (y + h)) / |h| ^ (p + 1)| ≤ B * jb y ^ N)
    (φ : SchwartzMap ℝ ℝ) (Cφ : ℝ)
    (hΦb : ∀ y, Integrable (fun h => (φ y - φ (y + h)) / |h| ^ (p + 1)) ∧
      ∫ h, |(φ y - φ (y + h)) / |h| ^ (p + 1)| ≤ Cφ * jb y ^ (-(p + 1)))
    (hw1 : Integrable (fun y => jb y ^ N * |φ y|)) (hw2 : Integrable (fun y => jb y ^ (-(p + 1)))) :
    ∫ y, (∫ h, (g y - g (y + h)) / |h| ^ (p + 1)) * φ y =
      ∫ y, g y * ∫ h, (φ y - φ (y + h)) / |h| ^ (p + 1) := by
  have hδ : ∀ n : ℕ, (0:ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  set κ : ℕ → ℝ → ℝ := fun n => c01_aux_kappa p (1 / ((n : ℝ) + 1))
  have hmeasL : ∀ (w : ℝ → ℝ), Continuous w → ∀ n,
      AEStronglyMeasurable (fun y => ∫ h, κ n h * (w y - w (y + h))) volume := by
    intro w hw n
    obtain ⟨-, -, hm, -⟩ := c01_aux_kappa_props p _ hp (hδ n)
    have : AEStronglyMeasurable (fun z : ℝ × ℝ => κ n z.2 * (w z.1 - w (z.1 + z.2)))
        (volume.prod volume) :=
      (hm.aestronglyMeasurable.comp_snd).mul ((hw.comp continuous_fst).sub
        (hw.comp continuous_add)).aestronglyMeasurable
    exact this.integral_prod_right'
  have hL : Tendsto (fun n : ℕ => ∫ y, (∫ h, κ n h * (g y - g (y + h))) * φ y) atTop
      (𝓝 (∫ y, (∫ h, (g y - g (y + h)) / |h| ^ (p + 1)) * φ y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => B * (jb y ^ N * |φ y|))
      (fun n => (hmeasL g hgc n).mul φ.continuous.aestronglyMeasurable) (hw1.const_mul B)
      (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · obtain ⟨hI, hb⟩ := hFb y
      have := (c01_aux_untruncate p hp g hgc y hI).2 n
      rw [Real.norm_eq_abs, abs_mul]
      calc |∫ h, κ n h * (g y - g (y + h))| * |φ y| ≤ (B * jb y ^ N) * |φ y| :=
            mul_le_mul_of_nonneg_right (this.trans hb) (abs_nonneg _)
        _ = B * (jb y ^ N * |φ y|) := by ring
    · exact ((c01_aux_untruncate p hp g hgc y (hFb y).1).1).mul_const _
  have hR : Tendsto (fun n : ℕ => ∫ y, g y * ∫ h, κ n h * (φ y - φ (y + h))) atTop
      (𝓝 (∫ y, g y * ∫ h, (φ y - φ (y + h)) / |h| ^ (p + 1))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => M * Cφ * jb y ^ (-(p + 1)))
      (fun n => hgc.aestronglyMeasurable.mul (hmeasL φ φ.continuous n)) (hw2.const_mul _)
      (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · obtain ⟨hI, hb⟩ := hΦb y
      have := (c01_aux_untruncate p hp φ φ.continuous y hI).2 n
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM y)
      rw [Real.norm_eq_abs, abs_mul]
      calc |g y| * |∫ h, κ n h * (φ y - φ (y + h))| ≤ M * (Cφ * jb y ^ (-(p + 1))) :=
            mul_le_mul (hM y) (this.trans hb) (abs_nonneg _) hM0
        _ = M * Cφ * jb y ^ (-(p + 1)) := by ring
    · exact ((c01_aux_untruncate p hp φ φ.continuous y (hΦb y).1).1).const_mul _
  have heq : ∀ n : ℕ, ∫ y, (∫ h, κ n h * (g y - g (y + h))) * φ y =
      ∫ y, g y * ∫ h, κ n h * (φ y - φ (y + h)) := by
    intro n
    obtain ⟨hi, he, -, -⟩ := c01_aux_kappa_props p _ hp (hδ n)
    exact c01_aux_trunc_identity hi he g hgc M hM φ
  simp_rw [heq] at hL
  exact tendsto_nhds_unique hL hR

/-- `⟨y⟩^N |φ(y)|` is integrable for Schwartz `φ` and `N ≥ 0`. -/
theorem c01_aux_integrable_jb_pow_mul (φ : SchwartzMap ℝ ℝ) (N : ℝ) (hN : 0 ≤ N) :
    Integrable (fun y => jb y ^ N * |φ y|) := by
  set k := ⌈N⌉₊
  have hint : Integrable (fun y => 2 ^ k * (|φ y| + ‖y‖ ^ k * ‖φ y‖)) :=
    ((φ.integrable.abs).add (SchwartzMap.integrable_pow_mul volume φ k)).const_mul _
  refine Integrable.mono' hint (by
    have : Continuous (fun y => jb y ^ N) := by
      unfold jb
      exact (Real.continuous_sqrt.comp (by fun_prop)).rpow_const (fun _ => Or.inr hN)
    exact (this.mul φ.continuous.abs).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  have hjb1 := c01_aux_one_le_jb y
  have hjb : jb y ≤ 1 + |y| := by
    have := c01_aux_jb_le y 0
    simp only [sub_zero] at this
    have h0 : jb 0 = 1 := by simp [jb]
    linarith
  have h1 : jb y ^ N ≤ jb y ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hjb1 (Nat.le_ceil N)
  have h2 : jb y ^ k ≤ 2 ^ k * (1 + |y| ^ k) := by
    rcases le_total |y| 1 with hy | hy
    · calc jb y ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
        _ ≤ 2 ^ k * (1 + |y| ^ k) := by
          have : 0 ≤ |y| ^ k := by positivity
          nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k]
    · calc jb y ^ k ≤ (2 * |y|) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
        _ = 2 ^ k * |y| ^ k := mul_pow _ _ _
        _ ≤ 2 ^ k * (1 + |y| ^ k) := by
          nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_nonneg (φ y)
  calc jb y ^ N * |φ y| ≤ (2 ^ k * (1 + |y| ^ k)) * |φ y| := by gcongr; linarith
    _ = 2 ^ k * (|φ y| + |y| ^ k * |φ y|) := by ring

/-- `⟨y⟩^{-α}` is integrable for `α > 1`. -/
theorem c01_aux_integrable_jb_neg (p : ℝ) (hp : 0 < p) :
    Integrable (fun y => jb y ^ (-(p + 1))) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := p + 1)
    (by simp; linarith)
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, sq_abs, jb]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- Shift-form of the kernel bound. -/
theorem c01_aux_shift_bound (p : ℝ) (g : ℝ → ℝ) (y K : ℝ)
    (hI : Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)))
    (hK : ∫ z, |(g y - g z) / |y - z| ^ (p + 1)| ≤ K) :
    Integrable (fun h => (g y - g (y + h)) / |h| ^ (p + 1)) ∧
      ∫ h, |(g y - g (y + h)) / |h| ^ (p + 1)| ≤ K := by
  have e : ∀ h, (g y - g (y + h)) / |h| ^ (p + 1) =
      (fun z => (g y - g z) / |y - z| ^ (p + 1)) (y + h) := fun h => by simp [abs_neg]
  simp_rw [e]
  refine ⟨hI.comp_add_left y, ?_⟩
  rw [integral_add_left_eq_self (fun z => |(g y - g z) / |y - z| ^ (p + 1)|) y]
  exact hK

/-- First half of lem:c01_frac_duality. -/
theorem c01_aux_duality_main (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (g : ℝ → ℝ) (M C N : ℝ), (∀ᵐ z, |g z| ≤ M) → W1inftyLoc g → 0 ≤ C → 0 ≤ N →
        (∀ᵐ y, |deriv g y| ≤ C * jb y ^ N) →
        Continuous (fracD p g) ∧
        (∃ C' : ℝ, ∀ y, |fracD p g y| ≤ C' * jb y ^ N) ∧
        ∀ φ : SchwartzMap ℝ ℝ,
          (∃ Cφ : ℝ, ∀ y, ‖fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y‖ ≤ Cφ * jb y ^ (-(p + 1))) ∧
          Integrable (fun y => fracD p g y * φ y) ∧
          Integrable (fun y => (g y : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y) ∧
          ∫ y, ((fracD p g y * φ y : ℝ) : ℂ) =
            ∫ y, (g y : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y := by
  intro g M C N hM hW hC hN hd
  obtain ⟨hM0, hMall, B, hB0, hFb⟩ := c01_aux_duality_kernel_bound p hp hp1 g M C N hM hW hC hN hd
  have hgc : Continuous g := hW.continuous
  have hcal := c01_aux_calpha_nonneg p hp hp1
  have hcont : Continuous (fracD p g) := c01_aux_fracD_continuous p hp hp1 g M hMall hW
  have hbound : ∀ y, |fracD p g y| ≤ calpha p * B * jb y ^ N := by
    intro y
    unfold fracD
    rw [abs_mul, abs_of_nonneg hcal, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans (hFb y).2) hcal
  refine ⟨hcont, ⟨_, hbound⟩, fun φ => ?_⟩
  obtain ⟨Cφ, hCφ0, hΦb⟩ := c01_aux_schwartz_kernel_decay p hp hp1 φ
  have hmult : ∀ y, fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
      (fun x => ((φ x : ℝ) : ℂ)) y = ((fracD p φ y : ℝ) : ℂ) :=
    fun y => (c01_frac_singular_integral p hp hp1).1 φ y
  have hφbound : ∀ y, |fracD p φ y| ≤ calpha p * Cφ * jb y ^ (-(p + 1)) := by
    intro y
    rw [c01_aux_fracD_shift, abs_mul, abs_of_nonneg hcal, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans (hΦb y).2) hcal
  obtain ⟨Mφ, -, -, hMφ, -⟩ := c01_aux_schwartz_bdd_lip φ
  have hφcont : Continuous (fracD p φ) :=
    c01_aux_fracD_continuous p hp hp1 φ Mφ hMφ ((φ.smooth 1).locallyLipschitz)
  have hw1 := c01_aux_integrable_jb_pow_mul φ N hN
  have hw2 := c01_aux_integrable_jb_neg p hp
  have hI1 : Integrable (fun y => fracD p g y * φ y) := by
    refine Integrable.mono' (hw1.const_mul (calpha p * B))
      (hcont.mul φ.continuous).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |fracD p g y| * |φ y| ≤ (calpha p * B * jb y ^ N) * |φ y| :=
          mul_le_mul_of_nonneg_right (hbound y) (abs_nonneg _)
      _ = calpha p * B * (jb y ^ N * |φ y|) := by ring
  have hI2r : Integrable (fun y => g y * fracD p φ y) := by
    refine Integrable.mono' (hw2.const_mul (M * (calpha p * Cφ)))
      (hgc.mul hφcont).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |fracD p φ y| ≤ M * (calpha p * Cφ * jb y ^ (-(p + 1))) :=
          mul_le_mul (hMall y) (hφbound y) (abs_nonneg _) hM0
      _ = M * (calpha p * Cφ) * jb y ^ (-(p + 1)) := by ring
  have hcast : ∀ y, (g y : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
      (fun x => ((φ x : ℝ) : ℂ)) y = ((g y * fracD p φ y : ℝ) : ℂ) := by
    intro y; rw [hmult]; push_cast; ring
  simp_rw [hcast]
  refine ⟨⟨calpha p * Cφ, fun y => ?_⟩, hI1, hI2r.ofReal, ?_⟩
  · rw [hmult, Complex.norm_real, Real.norm_eq_abs]; exact hφbound y
  rw [integral_complex_ofReal, integral_complex_ofReal]
  congr 1
  have hFb' : ∀ y, Integrable (fun h => (g y - g (y + h)) / |h| ^ (p + 1)) ∧
      ∫ h, |(g y - g (y + h)) / |h| ^ (p + 1)| ≤ B * jb y ^ N := fun y =>
    c01_aux_shift_bound p g y _ (hFb y).1 (hFb y).2
  have key := c01_aux_duality_real p hp g hgc M hMall B N hFb' φ Cφ hΦb hw1 hw2
  have e1 : ∀ y, fracD p g y * φ y = calpha p * ((∫ h, (g y - g (y + h)) / |h| ^ (p + 1)) * φ y) :=
    fun y => by rw [c01_aux_fracD_shift]; ring
  have e2 : ∀ y, g y * fracD p φ y = calpha p * (g y * ∫ h, (φ y - φ (y + h)) / |h| ^ (p + 1)) :=
    fun y => by rw [c01_aux_fracD_shift]; ring
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul, key]

/-- Blueprint: lem:c01_frac_duality.  For `g ∈ L^∞ ∩ W^{1,∞}_loc` with `|g'| ≤ C⟨y⟩^N` a.e.:
`|D|^p g` is continuous, `||D|^p g(y)| ≤ C'⟨y⟩^N`, and for `φ ∈ 𝒮`,
`∫ |D|^p g · φ = ∫ g · |D|^p φ` with `|D|^p φ = (|ξ|^p φ̂)^∨ = O(⟨y⟩^{-α})`.
In particular, if `f ∈ 𝒜` with `f''` polynomially bounded and `ℰ_ε(f) = 0` pointwise, then
`ℰ_ε(f) = 0` in `𝒟'(ℝ)` (the term `|D|^p f'` being the distribution `φ ↦ ⟨f', |D|^p φ⟩`). -/
theorem c01_frac_duality (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ (g : ℝ → ℝ) (M C N : ℝ), (∀ᵐ z, |g z| ≤ M) → W1inftyLoc g → 0 ≤ C → 0 ≤ N →
        (∀ᵐ y, |deriv g y| ≤ C * jb y ^ N) →
        Continuous (fracD p g) ∧
        (∃ C' : ℝ, ∀ y, |fracD p g y| ≤ C' * jb y ^ N) ∧
        ∀ φ : SchwartzMap ℝ ℝ,
          (∃ Cφ : ℝ, ∀ y, ‖fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y‖ ≤ Cφ * jb y ^ (-(p + 1))) ∧
          Integrable (fun y => fracD p g y * φ y) ∧
          Integrable (fun y => (g y : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y) ∧
          ∫ y, ((fracD p g y * φ y : ℝ) : ℂ) =
            ∫ y, (g y : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y) ∧
    (∀ (ε : ℝ) (f : ℝ → ℝ), 0 ≤ ε → f ∈ c01_admissible_class →
        (∃ C N : ℝ, ∀ᵐ y, |deriv (deriv f) y| ≤ C * jb y ^ N) →
        (∀ y, residual p ε f y = 0) →
        ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ y, ((deriv f y : ℝ) : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y) +
            ((∫ y, (f y - y * deriv f y + J_eps p ε f y) / A_eps p ε (deriv f y) * φ y : ℝ) :
              ℂ) = 0) := by
  have hA := c01_aux_duality_main p hp hp1
  refine ⟨hA, fun ε f _ hf ⟨C, N, hCN⟩ hres φ hφ hcs => ?_⟩
  obtain ⟨M, hM⟩ := hf.2.1
  set Φ : SchwartzMap ℝ ℝ := hcs.toSchwartzMap hφ
  have hΦ : ⇑Φ = φ := rfl
  have hd' : ∀ᵐ y, |deriv (deriv f) y| ≤ max C 0 * jb y ^ max N 0 := by
    filter_upwards [hCN] with y hy
    have h1 := c01_aux_one_le_jb y
    have h2 : jb y ^ N ≤ jb y ^ max N 0 := Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
    have h3 : 0 ≤ jb y ^ N := Real.rpow_nonneg (by linarith) _
    calc |deriv (deriv f) y| ≤ C * jb y ^ N := hy
      _ ≤ max C 0 * jb y ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max C 0 * jb y ^ max N 0 := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  obtain ⟨-, -, hφpart⟩ := hA (deriv f) M (max C 0) (max N 0) (Eventually.of_forall hM) hf.2.2
    (le_max_right _ _) (le_max_right _ _) hd'
  obtain ⟨-, -, -, hid⟩ := hφpart Φ
  rw [hΦ] at hid
  rw [← hid, integral_complex_ofReal]
  have hrest : ∀ y, (f y - y * deriv f y + J_eps p ε f y) / A_eps p ε (deriv f y) * φ y =
      -(fracD p (deriv f) y * φ y) := by
    intro y
    have := hres y
    unfold residual fracDdy at this
    have : (f y - y * deriv f y + J_eps p ε f y) / A_eps p ε (deriv f y) =
        -fracD p (deriv f) y := by linarith
    rw [this]; ring
  simp_rw [hrest]
  rw [integral_neg]
  push_cast
  ring

/-! ### The gSQG front equation -/

/-- Blueprint: lem:c01_J_well_defined.  For `ε ≥ 0`, `f ∈ 𝒜`, the integrand of `𝒥_ε(f)(y)` is
integrable and `|𝒥_ε(f)(y)| ≤ c_α (2Λ_y/(2-α) + 4‖f'‖_∞/(α-1))`, `Λ_y` a Lipschitz constant of
`f'` on `[y-1,y+1]`. -/
theorem c01_J_well_defined (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) (M : ℝ) (hM : ∀ z, |deriv f z| ≤ M)
    (y Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1),
      |deriv f z - deriv f w| ≤ Λ * |z - w|) :
    Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
        A_eps p ε (c01_secant f y z)) ∧
      |c01_Jfull_eps p ε f y| ≤ calpha p * (2 * Λ / (2 - (p + 1)) + 4 * M / ((p + 1) - 1)) := by
  have hcont : Continuous (deriv f) := hf.1.continuous_deriv le_rfl
  obtain ⟨hI, hB⟩ := c01_aux_frac_integrable p hp hp1 (deriv f) hcont.aestronglyMeasurable M
    (Eventually.of_forall hM) y Λ hΛ hLip
  have hAm : AEStronglyMeasurable (fun z => A_eps p ε (c01_secant f y z)) volume :=
    ((c01_aux_A_measurable p ε).comp (c01_aux_secant_measurable f hf.1.continuous y)).aestronglyMeasurable
  have hI2 : Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
      A_eps p ε (c01_secant f y z)) := by
    refine hI.mul_bdd (c := 1) hAm (Eventually.of_forall fun z => ?_)
    obtain ⟨h1, h2⟩ := c01_aux_A_bounds p ε (c01_secant f y z) hp hε
    rw [Real.norm_eq_abs, abs_of_pos h1]; exact h2
  refine ⟨hI2, ?_⟩
  have hc := c01_aux_calpha_nonneg p hp hp1
  unfold c01_Jfull_eps
  rw [abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  refine (abs_integral_le_integral_abs).trans (le_trans ?_ hB)
  apply integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hI.abs
  refine Eventually.of_forall fun z => ?_
  obtain ⟨h1, h2⟩ := c01_aux_A_bounds p ε (c01_secant f y z) hp hε
  simp only
  rw [abs_mul, abs_of_pos h1]
  exact mul_le_of_le_one_right (abs_nonneg _) h2

/-- Algebraic part of lem:c01_linearization: `𝒥(sF) = s 𝒥_{s²}(F)` (no hypotheses needed). -/
theorem c01_aux_J_homog (p : ℝ) (F : ℝ → ℝ) (s x : ℝ) :
    c01_Jfull_eps p 1 (fun z => s * F z) x = s * c01_Jfull_eps p (s ^ 2) F x := by
  have hd : deriv (fun z => s * F z) = fun z => s * deriv F z := by
    exact deriv_const_mul_field' (v := F) s
  have hS : ∀ z, c01_secant (fun z => s * F z) x z = s * c01_secant F x z := by
    intro z; unfold c01_secant
    split_ifs
    · rw [hd]
    · ring
  have hA : ∀ v, A_eps p 1 (s * v) = A_eps p (s ^ 2) v := by
    intro v; unfold A_eps; congr 1; ring
  unfold c01_Jfull_eps
  rw [hd]
  simp_rw [hS, hA]
  have : ∀ z, (s * deriv F x - s * deriv F z) / |x - z| ^ (p + 1) * A_eps p (s ^ 2) (c01_secant F x z)
      = s * ((deriv F x - deriv F z) / |x - z| ^ (p + 1) * A_eps p (s ^ 2) (c01_secant F x z)) := by
    intro z; ring
  simp_rw [this]
  rw [integral_const_mul]; ring

/-- Blueprint: lem:c01_linearization.  `𝒥₀(F) = |D|^p∂_x F`, `s⁻¹𝒥(sF)(x) → |D|^p∂_x F(x)` as
`s → 0`, and `𝒥(sF) = s 𝒥_{s²}(F)`. -/
theorem c01_linearization (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (F : ℝ → ℝ)
    (hF : F ∈ c01_admissible_class) :
    (∀ x, c01_Jfull_eps p 0 F x = fracDdy p F x) ∧
    (∀ x, Tendsto (fun s : ℝ => s⁻¹ * c01_Jfull_eps p 1 (fun z => s * F z) x) (𝓝[≠] 0)
        (𝓝 (fracDdy p F x))) ∧
    (∀ s x : ℝ, c01_Jfull_eps p 1 (fun z => s * F z) x = s * c01_Jfull_eps p (s ^ 2) F x) := by
  have hJ0 : ∀ x, c01_Jfull_eps p 0 F x = fracDdy p F x := by
    intro x
    unfold c01_Jfull_eps fracDdy fracD A_eps
    simp
  refine ⟨hJ0, ?_, c01_aux_J_homog p F⟩
  intro x
  rw [← hJ0 x]
  have hev : (fun s : ℝ => c01_Jfull_eps p (s ^ 2) F x) =ᶠ[𝓝[≠] 0]
      (fun s : ℝ => s⁻¹ * c01_Jfull_eps p 1 (fun z => s * F z) x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [c01_aux_J_homog, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  refine Tendsto.congr' hev ?_
  have h0 : c01_Jfull_eps p 0 F x = c01_Jfull_eps p ((0:ℝ) ^ 2) F x := by norm_num
  rw [h0]
  refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
  unfold c01_Jfull_eps
  apply Tendsto.const_mul
  obtain ⟨Λ, hΛ, hLip⟩ := c01_aux_lip F hF x
  obtain ⟨M, hM⟩ := hF.2.1
  have hcont : Continuous (deriv F) := hF.1.continuous_deriv le_rfl
  have hI := (c01_frac_well_defined p hp hp1 (deriv F) hcont.aestronglyMeasurable M
    (Eventually.of_forall hM) x Λ hΛ hLip).1
  apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖(deriv F x - deriv F z) / |x - z| ^ (p + 1)‖)
  · refine Eventually.of_forall fun s => ?_
    exact hI.aestronglyMeasurable.mul ((c01_aux_A_measurable p _).comp
      (c01_aux_secant_measurable F hF.1.continuous x)).aestronglyMeasurable
  · refine Eventually.of_forall fun s => Eventually.of_forall fun z => ?_
    obtain ⟨h1, h2⟩ := c01_aux_A_bounds p (s ^ 2) (c01_secant F x z) hp (sq_nonneg s)
    rw [norm_mul, Real.norm_eq_abs (A_eps _ _ _), abs_of_pos h1]
    exact mul_le_of_le_one_right (norm_nonneg _) h2
  · exact hI.norm
  · refine Eventually.of_forall fun z => ?_
    apply Tendsto.const_mul
    unfold A_eps
    have hc : ContinuousAt (fun s : ℝ => (1 + s ^ 2 * c01_secant F x z ^ 2) ^ (-(p + 1) / 2)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop)
      left; norm_num
    exact hc.tendsto

/-- Derivative of `x ↦ a g(bx+β) + h`. -/
theorem c01_aux_hasDerivAt_affine (g : ℝ → ℝ) (a b β h x : ℝ) (hg : DifferentiableAt ℝ g (b * x + β)) :
    HasDerivAt (fun x => a * g (b * x + β) + h) (a * b * deriv g (b * x + β)) x := by
  have h1 : HasDerivAt (fun x : ℝ => b * x + β) b x := by
    simpa using ((hasDerivAt_id x).const_mul b).add_const β
  have h2 : HasDerivAt (fun x => a * g (b * x + β) + h) (a * (deriv g (b * x + β) * b)) x :=
    ((hg.hasDerivAt.comp x h1).const_mul a).add_const h
  convert h2 using 1
  ring

/-- `(a g(b·+β) + h)'' = a b² g''(b·+β)` for `g ∈ C²`. -/
theorem c01_aux_iter2_affine (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (a b β h x : ℝ) :
    iteratedDeriv 2 (fun x => a * g (b * x + β) + h) x = a * b ^ 2 * iteratedDeriv 2 g (b * x + β) := by
  have h2 : ContDiff ℝ (1 + 1) g := hg
  obtain ⟨hgd, -, hg1⟩ := contDiff_succ_iff_deriv.mp h2
  have hd1 : deriv (fun x => a * g (b * x + β) + h) = fun x => a * b * deriv g (b * x + β) := by
    funext x; exact (c01_aux_hasDerivAt_affine g a b β h x (hgd _)).deriv
  have hd2 : deriv (fun x => a * b * deriv g (b * x + β)) x =
      a * b * b * deriv (deriv g) (b * x + β) := by
    have := (c01_aux_hasDerivAt_affine (deriv g) (a * b) b β 0 x
      ((hg1.differentiable one_ne_zero) _)).deriv
    simpa using this
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, hd2, iteratedDeriv_succ, iteratedDeriv_one]
  ring

/-- Affine covariance of `𝒥 = 𝒥₁`: if `(ab)² = 1` then
`𝒥(a g(b·+β) + h)(x) = a b |b|^p 𝒥(g)(bx+β)`. -/
theorem c01_aux_J_affine (p : ℝ) (g : ℝ → ℝ) (hg : Differentiable ℝ g) (a b β h : ℝ) (hb : b ≠ 0)
    (hab : (a * b) ^ 2 = 1) (x : ℝ) :
    c01_Jfull_eps p 1 (fun x' => a * g (b * x' + β) + h) x =
      a * b * |b| ^ p * c01_Jfull_eps p 1 g (b * x + β) := by
  set G : ℝ → ℝ := fun x' => a * g (b * x' + β) + h with hGdef
  set u := b * x + β with hu
  have hGd : deriv G = fun x' => a * b * deriv g (b * x' + β) := by
    funext x'; exact (c01_aux_hasDerivAt_affine g a b β h x' (hg _)).deriv
  have hbx : ∀ z, b * ((z - β) / b) + β = z := fun z => by field_simp; ring
  have hS : ∀ z, c01_secant G x ((z - β) / b) = a * b * c01_secant g u z := by
    intro z
    unfold c01_secant
    by_cases hxz : x = (z - β) / b
    · have huz : u = z := by rw [hu, hxz, hbx]
      rw [if_pos hxz, if_pos huz, hGd]
    · have huz : u ≠ z := by
        intro h'; apply hxz; rw [← h', hu]; field_simp; ring
      rw [if_neg hxz, if_neg huz]
      simp only [hGdef]
      rw [hbx, ← hu]
      have h1 : x - (z - β) / b = (u - z) / b := by rw [hu]; field_simp; ring
      have h2 : u - z ≠ 0 := sub_ne_zero.mpr huz
      rw [h1]; field_simp; ring
  have hA : ∀ v, A_eps p 1 (a * b * v) = A_eps p 1 v := by
    intro v; unfold A_eps; rw [mul_pow, hab, one_mul]
  have hbpos : 0 < |b| := abs_pos.mpr hb
  have hpt : ∀ z, (deriv G x - deriv G ((z - β) / b)) / |x - (z - β) / b| ^ (p + 1) *
      A_eps p 1 (c01_secant G x ((z - β) / b)) =
      (a * b * |b| ^ (p + 1)) * ((deriv g u - deriv g z) / |u - z| ^ (p + 1) *
        A_eps p 1 (c01_secant g u z)) := by
    intro z
    rw [hS, hA, hGd]
    simp only
    rw [hbx, ← hu]
    have h1 : |x - (z - β) / b| = |u - z| / |b| := by
      rw [show x - (z - β) / b = (u - z) / b by rw [hu]; field_simp; ring, abs_div]
    rw [h1, Real.div_rpow (abs_nonneg _) hbpos.le]
    have hb' : 0 < |b| ^ (p + 1) := Real.rpow_pos_of_pos hbpos _
    by_cases huz : |u - z| ^ (p + 1) = 0
    · rw [huz]; simp
    · field_simp
  have hsub : ∫ x', (deriv G x - deriv G x') / |x - x'| ^ (p + 1) * A_eps p 1 (c01_secant G x x')
      = |b|⁻¹ * ∫ z, (deriv G x - deriv G ((z - β) / b)) / |x - (z - β) / b| ^ (p + 1) *
          A_eps p 1 (c01_secant G x ((z - β) / b)) := by
    set Ψ : ℝ → ℝ := fun x' => (deriv G x - deriv G x') / |x - x'| ^ (p + 1) *
      A_eps p 1 (c01_secant G x x') with hΨ
    change ∫ x', Ψ x' = |b|⁻¹ * ∫ z, Ψ ((z - β) / b)
    have e1 : ∫ z, Ψ ((z - β) / b) = ∫ z, Ψ (z / b) :=
      integral_sub_right_eq_self (fun z => Ψ (z / b)) β
    rw [e1, Measure.integral_comp_div Ψ b, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hbpos.ne',
      one_mul]
  unfold c01_Jfull_eps
  rw [hsub]
  simp_rw [hpt]
  rw [integral_const_mul]
  have : |b|⁻¹ * |b| ^ (p + 1) = |b| ^ p := by
    rw [Real.rpow_add_one hbpos.ne', mul_comm (|b| ^ p), ← mul_assoc, inv_mul_cancel₀ hbpos.ne',
      one_mul]
  calc calpha p * (|b|⁻¹ * (a * b * |b| ^ (p + 1) * ∫ z, (deriv g u - deriv g z) /
        |u - z| ^ (p + 1) * A_eps p 1 (c01_secant g u z)))
      = a * b * (|b|⁻¹ * |b| ^ (p + 1)) * (calpha p * ∫ z, (deriv g u - deriv g z) /
        |u - z| ^ (p + 1) * A_eps p 1 (c01_secant g u z)) := by ring
    _ = _ := by rw [this]

/-- Classical solutions are preserved by `G(x,t) = a F(bx+β, dt+τ) + h` when `(ab)² = 1` and
`d = b|b|^p` (common core of the three symmetries of lem:c01_front_symmetries). -/
theorem c01_aux_front_affine (p : ℝ) (I J : Set ℝ) (hI : IsOpen I)
    (F : ℝ → ℝ → ℝ) (hF : gsqg_front_equation p I F) (a b d β τ h : ℝ) (hb : b ≠ 0)
    (hab : (a * b) ^ 2 = 1) (hdb : d = b * |b| ^ p) (hJ : J = (fun t => d * t + τ) ⁻¹' I) :
    gsqg_front_equation p J (fun x t => a * F (b * x + β) (d * t + τ) + h) := by
  obtain ⟨hC1, hC2, hCt, hBd, hEq⟩ := hF
  set φ : ℝ × ℝ → ℝ × ℝ := fun q => (b * q.1 + β, d * q.2 + τ) with hφ
  have hφc : ContDiff ℝ 1 φ :=
    ((contDiff_const.mul contDiff_fst).add contDiff_const).prodMk
      ((contDiff_const.mul contDiff_snd).add contDiff_const)
  have hmaps : MapsTo φ (univ ×ˢ J) (univ ×ˢ I) := by
    intro q hq
    refine ⟨mem_univ _, ?_⟩
    have := hq.2; rw [hJ] at this; exact this
  have hJI : ∀ t ∈ J, d * t + τ ∈ I := by intro t ht; rw [hJ] at ht; exact ht
  have hSo : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hI
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ContDiffOn ℝ 1 (fun q : ℝ × ℝ => a * (fun q : ℝ × ℝ => F q.1 q.2) (φ q) + h) (univ ×ˢ J)
    exact (contDiffOn_const.mul (hC1.comp hφc.contDiffOn hmaps)).add contDiffOn_const
  · intro t ht
    exact (contDiff_const.mul ((hC2 _ (hJI t ht)).comp
      ((contDiff_const.mul contDiff_id).add contDiff_const))).add contDiff_const
  · have hc : ContinuousOn (fun q : ℝ × ℝ => a * b ^ 2 *
        (fun q : ℝ × ℝ => iteratedDeriv 2 (fun x => F x q.2) q.1) (φ q)) (univ ×ˢ J) :=
      continuousOn_const.mul (hCt.comp hφc.continuous.continuousOn hmaps)
    refine hc.congr fun q hq => ?_
    exact c01_aux_iter2_affine _ (hC2 _ (hJI q.2 hq.2)) a b β h q.1
  · intro t ht
    obtain ⟨M, hM⟩ := hBd _ (hJI t ht)
    refine ⟨|a * b| * M, fun x => ?_⟩
    have hd := (hC2 _ (hJI t ht)).differentiable two_ne_zero
    rw [(c01_aux_hasDerivAt_affine _ a b β h x (hd _)).deriv, abs_mul (a * b)]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  · intro t ht x
    have hd := (hC2 _ (hJI t ht)).differentiable two_ne_zero
    rw [c01_aux_J_affine p _ hd a b β h hb hab x]
    -- time derivative by the chain rule
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => F q.1 q.2) (b * x + β, d * t + τ) :=
      (hC1.differentiableOn one_ne_zero).differentiableAt
        (hSo.mem_nhds ⟨mem_univ _, hJI t ht⟩)
    have hs : DifferentiableAt ℝ (fun s => F (b * x + β) s) (d * t + τ) := by
      have := hdiff.comp (d * t + τ) ((differentiableAt_const (b * x + β)).prodMk
        differentiableAt_id)
      exact this
    have h1 : HasDerivAt (fun s : ℝ => d * s + τ) d t := by
      simpa using ((hasDerivAt_id t).const_mul d).add_const τ
    have h2 := ((hs.hasDerivAt.comp t h1).const_mul a).add_const h
    have e : (fun s => a * F (b * x + β) (d * s + τ) + h) =
        fun s => a * ((fun s => F (b * x + β) s) ∘ fun s => d * s + τ) s + h := rfl
    rw [e, h2.deriv, hEq _ (hJI t ht), hdb]
    ring

-- Encoding: for `I = (a,b)` (endpoints possibly infinite); stated for
-- an arbitrary open set `I` with the transformed time sets written as preimages
-- (`{t | t - t₀ ∈ I} = (a+t₀,b+t₀)`, `{t | c^α t ∈ I} = (c^{-α}a, c^{-α}b)`, `{t | -t ∈ I} = (-b,-a)`).
/-- Blueprint: lem:c01_front_symmetries.  Classical solutions are preserved by
(1) translations `F(x-x₀,t-t₀)+h₀`, (2) the scaling `c⁻¹F(cx, c^α t)` (`c > 0`), and
(3) the reflection `F(-x,-t)`. -/
theorem c01_front_symmetries (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (I : Set ℝ) (hI : IsOpen I)
    (F : ℝ → ℝ → ℝ) (hF : gsqg_front_equation p I F) :
    (∀ x₀ t₀ h₀ : ℝ, gsqg_front_equation p ((fun t => t - t₀) ⁻¹' I)
        (fun x t => F (x - x₀) (t - t₀) + h₀)) ∧
    (∀ c : ℝ, 0 < c → gsqg_front_equation p ((fun t => c ^ (p + 1) * t) ⁻¹' I)
        (fun x t => c⁻¹ * F (c * x) (c ^ (p + 1) * t))) ∧
    gsqg_front_equation p ((fun t => -t) ⁻¹' I) (fun x t => F (-x) (-t)) := by
  refine ⟨fun x₀ t₀ h₀ => ?_, fun c hc => ?_, ?_⟩
  · have := c01_aux_front_affine p I _ hI F hF 1 1 1 (-x₀) (-t₀) h₀ one_ne_zero (by norm_num)
      (by simp) rfl
    convert this using 1
    · ext t; simp [sub_eq_add_neg]
    · funext x t; simp [sub_eq_add_neg]
  · have hcp : c ^ (p + 1) = c * |c| ^ p := by
      rw [abs_of_pos hc, Real.rpow_add_one hc.ne']; ring
    have := c01_aux_front_affine p I _ hI F hF c⁻¹ c (c ^ (p + 1)) 0 0 0 hc.ne'
      (by rw [inv_mul_cancel₀ hc.ne']; norm_num) hcp rfl
    convert this using 1
    · ext t; simp
    · funext x t; simp
  · have := c01_aux_front_affine p I _ hI F hF 1 (-1) (-1) 0 0 0 (by norm_num) (by norm_num)
      (by simp) rfl
    convert this using 1
    · ext t; simp
    · funext x t; simp

/-! ### The self-similar ansatz and the profile equation -/

/-- Blueprint: lem:c01_L_properties.  `L = L_T ∈ C^∞((-∞,T))`, `L > 0`, `L(t) → 0` as `t ↑ T`, and
`L'(t) = -L(t)^{1-α}`. -/
theorem c01_L_properties (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (T : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (self_similar_ansatz_L p T) (Iio T) ∧
    (∀ t, t < T → 0 < self_similar_ansatz_L p T t) ∧
    Tendsto (self_similar_ansatz_L p T) (𝓝[<] T) (𝓝 0) ∧
    (∀ t, t < T → HasDerivAt (self_similar_ansatz_L p T)
        (-(self_similar_ansatz_L p T t ^ (1 - (p + 1)))) t) := by
  have hbase : ∀ t, t < T → 0 < (p + 1) * (T - t) := fun t ht => by
    have : 0 < T - t := by linarith
    positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    apply ContDiffAt.contDiffWithinAt
    unfold self_similar_ansatz_L
    show ContDiffAt ℝ _ ((fun x : ℝ => x ^ (1 / (p + 1))) ∘ (fun s => (p + 1) * (T - s))) t
    exact (Real.contDiffAt_rpow_const_of_ne (hbase t ht).ne').comp t
      (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id))
  · intro t ht; unfold self_similar_ansatz_L; exact Real.rpow_pos_of_pos (hbase t ht) _
  · have hc : Continuous (self_similar_ansatz_L p T) := by
      unfold self_similar_ansatz_L
      exact (by fun_prop : Continuous fun t : ℝ => (p + 1) * (T - t)).rpow_const
        (fun _ => Or.inr (by positivity))
    have h0 : self_similar_ansatz_L p T T = 0 := by
      unfold self_similar_ansatz_L; simp only [sub_self, mul_zero]
      exact Real.zero_rpow (by positivity)
    have := hc.tendsto T
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  · intro t ht
    have hd : HasDerivAt (fun s => (p + 1) * (T - s)) (-(p + 1)) t := by
      have := ((hasDerivAt_id t).const_sub T).const_mul (p + 1)
      simpa using this
    have := hd.rpow_const (p := 1 / (p + 1)) (Or.inl (hbase t ht).ne')
    unfold self_similar_ansatz_L
    convert this using 1
    rw [← Real.rpow_mul (hbase t ht).le]
    have hp1' : p + 1 ≠ 0 := by linarith
    rw [show 1 / (p + 1) * (1 - (p + 1)) = 1 / (p + 1) - 1 by field_simp]
    field_simp

/-- Blueprint: lem:c01_ansatz_time_derivative.  For `f ∈ C¹`, `F = F_{ε,T,f} ∈ C¹(ℝ×(-∞,T))`,
`∂ₓF = √ε f'(y)`, `∂ₜF = -√ε L^{1-α}(f(y) - y f'(y))` with `y = x/L(t)`; if `f ∈ C^k` then
`∂ₓʲF = √ε L^{1-j} f^{(j)}(y)` for `j ≤ k` and `F ∈ C^k(ℝ×(-∞,T))`. -/
theorem c01_ansatz_time_derivative (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε T : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ContDiffOn ℝ 1 (fun q : ℝ × ℝ => self_similar_ansatz p ε T f q.1 q.2) (univ ×ˢ Iio T) ∧
    (∀ x t : ℝ, t < T →
      let L := self_similar_ansatz_L p T t
      let y := x / L
      deriv (fun x' => self_similar_ansatz p ε T f x' t) x = Real.sqrt ε * deriv f y ∧
      deriv (fun s => self_similar_ansatz p ε T f x s) t =
        -(Real.sqrt ε * L ^ (1 - (p + 1)) * (f y - y * deriv f y))) ∧
    (∀ k : ℕ, ContDiff ℝ k f →
      ContDiffOn ℝ k (fun q : ℝ × ℝ => self_similar_ansatz p ε T f q.1 q.2) (univ ×ˢ Iio T) ∧
      ∀ j : ℕ, j ≤ k → ∀ x t : ℝ, t < T →
        let L := self_similar_ansatz_L p T t
        iteratedDeriv j (fun x' => self_similar_ansatz p ε T f x' t) x =
          Real.sqrt ε * L ^ (1 - (j : ℝ)) * iteratedDeriv j f (x / L)) := by
  have hLp := c01_L_properties p hp hp1 T
  set S : Set (ℝ × ℝ) := univ ×ˢ Iio T with hS
  have hLne : ∀ q ∈ S, self_similar_ansatz_L p T q.2 ≠ 0 := fun q hq => (hLp.2.1 q.2 hq.2).ne'
  have hk : ∀ k : ℕ, ContDiff ℝ k f →
      ContDiffOn ℝ k (fun q : ℝ × ℝ => self_similar_ansatz p ε T f q.1 q.2) S ∧
      ∀ j : ℕ, j ≤ k → ∀ x t : ℝ, t < T →
        let L := self_similar_ansatz_L p T t
        iteratedDeriv j (fun x' => self_similar_ansatz p ε T f x' t) x =
          Real.sqrt ε * L ^ (1 - (j : ℝ)) * iteratedDeriv j f (x / L) := by
    intro k hfk
    refine ⟨?_, ?_⟩
    · have hL : ContDiffOn ℝ k (fun q : ℝ × ℝ => self_similar_ansatz_L p T q.2) S :=
        (hLp.1.of_le (WithTop.coe_le_coe.mpr le_top)).comp contDiff_snd.contDiffOn
          (fun q hq => hq.2)
      show ContDiffOn ℝ k (fun q : ℝ × ℝ => Real.sqrt ε * self_similar_ansatz_L p T q.2 *
        f (q.1 / self_similar_ansatz_L p T q.2)) S
      exact (contDiffOn_const.mul hL).mul
        (hfk.comp_contDiffOn (contDiff_fst.contDiffOn.div hL hLne))
    · intro j hj x t ht L
      have hfj : ContDiff ℝ j f := hfk.of_le (by exact_mod_cast hj)
      have hL0 : 0 < L := hLp.2.1 t ht
      show iteratedDeriv j (fun x' => Real.sqrt ε * L * f (x' / L)) x = _
      rw [iteratedDeriv_const_mul_field]
      have e : (fun x' => f (x' / L)) = fun x' => f (L⁻¹ * x') := by
        funext x'; rw [div_eq_inv_mul]
      rw [e, iteratedDeriv_comp_const_mul hfj]
      simp only
      rw [← div_eq_inv_mul, sub_eq_add_neg, Real.rpow_add hL0, Real.rpow_one, Real.rpow_neg hL0.le,
        Real.rpow_natCast, inv_pow]
      ring
  have hk1 := hk 1 hf
  refine ⟨hk1.1, ?_, hk⟩
  intro x t ht L y
  have hL0 : 0 < L := hLp.2.1 t ht
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  refine ⟨?_, ?_⟩
  · have := hk1.2 1 le_rfl x t ht
    simp only [iteratedDeriv_one, Nat.cast_one, sub_self, Real.rpow_zero, mul_one] at this
    exact this
  · have hLd := hLp.2.2.2 t ht
    have h1 : HasDerivAt (fun s => x / self_similar_ansatz_L p T s)
        ((0 * L - x * (-(L ^ (1 - (p + 1))))) / L ^ 2) t :=
      (hasDerivAt_const t x).div hLd hL0.ne'
    have h2 := (hfd (x / L)).hasDerivAt.comp t h1
    have h3 : HasDerivAt (fun s => Real.sqrt ε * self_similar_ansatz_L p T s *
        f (x / self_similar_ansatz_L p T s))
        (Real.sqrt ε * -(L ^ (1 - (p + 1))) * f (x / L) +
          Real.sqrt ε * L * (deriv f (x / L) * ((0 * L - x * -(L ^ (1 - (p + 1)))) / L ^ 2))) t :=
      (hLd.const_mul (Real.sqrt ε)).mul h2
    have e : (fun s => self_similar_ansatz p ε T f x s) =
        fun s => Real.sqrt ε * self_similar_ansatz_L p T s *
          f (x / self_similar_ansatz_L p T s) := rfl
    rw [e, h3.deriv]
    have hy : y = x / L := rfl
    rw [hy]
    field_simp
    ring

/-- Derivative of `x ↦ √ε λ f(x/λ)`. -/
theorem c01_aux_scaled_hasDerivAt (ε lam : ℝ) (hlam : 0 < lam) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (fun x' => Real.sqrt ε * lam * f (x' / lam)) (Real.sqrt ε * deriv f (x / lam)) x := by
  have h1 : HasDerivAt (fun x' : ℝ => x' / lam) (1 / lam) x := by
    simpa using (hasDerivAt_id x).div_const lam
  have h2 : HasDerivAt (fun x' => Real.sqrt ε * lam * f (x' / lam))
      (Real.sqrt ε * lam * (deriv f (x / lam) * (1 / lam))) x :=
    ((hf (x / lam)).hasDerivAt.comp x h1).const_mul (Real.sqrt ε * lam)
  convert h2 using 1
  field_simp

/-- `LocallyLipschitz` is preserved by multiplication by a constant. -/
theorem c01_aux_locLip_const_mul (c : ℝ) (h : ℝ → ℝ) (hh : LocallyLipschitz h) :
    LocallyLipschitz (fun x => c * h x) := by
  have : LocallyLipschitz (fun u : ℝ => c * u) := by
    have := (lipschitzWith_smul (β := ℝ) c).locallyLipschitz
    simpa [smul_eq_mul] using this
  exact this.comp hh

/-- Blueprint: lem:c01_J_scaling.  For `ε, λ > 0`, `f ∈ 𝒜`, `G(x) = √ε λ f(x/λ)`:
`G ∈ 𝒜` and `𝒥(G)(x) = √ε λ^{1-α} 𝒥_ε(f)(x/λ)`. -/
theorem c01_J_scaling (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε lam : ℝ) (hε : 0 < ε)
    (hlam : 0 < lam) (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) :
    (fun x => Real.sqrt ε * lam * f (x / lam)) ∈ c01_admissible_class ∧
    ∀ x, c01_Jfull_eps p 1 (fun x' => Real.sqrt ε * lam * f (x' / lam)) x =
      Real.sqrt ε * lam ^ (1 - (p + 1)) * c01_Jfull_eps p ε f (x / lam) := by
  set G : ℝ → ℝ := fun x => Real.sqrt ε * lam * f (x / lam) with hGdef
  have hfd : Differentiable ℝ f := hf.1.differentiable one_ne_zero
  have hGd : deriv G = fun x => Real.sqrt ε * deriv f (x / lam) := by
    funext x; exact (c01_aux_scaled_hasDerivAt ε lam hlam f hfd x).deriv
  have hdiv : LocallyLipschitz (fun x : ℝ => x / lam) := by
    have := (lipschitzWith_smul (β := ℝ) lam⁻¹).locallyLipschitz
    simpa [smul_eq_mul, div_eq_inv_mul] using this
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact contDiff_const.mul (hf.1.comp (contDiff_id.div_const lam))
  · obtain ⟨M, hM⟩ := hf.2.1
    refine ⟨Real.sqrt ε * M, fun y => ?_⟩
    rw [hGd]
    simp only
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg ε)]
    exact mul_le_mul_of_nonneg_left (hM _) (Real.sqrt_nonneg ε)
  · rw [hGd]
    exact c01_aux_locLip_const_mul _ _ (hf.2.2.comp hdiv)
  · intro x
    set y := x / lam with hy
    have hlam0 : lam ≠ 0 := hlam.ne'
    have hS : ∀ z, c01_secant G x (lam * z) = Real.sqrt ε * c01_secant f y z := by
      intro z
      unfold c01_secant
      by_cases hxz : x = lam * z
      · have hyz : y = z := by rw [hy, hxz]; field_simp
        rw [if_pos hxz, if_pos hyz, hGd]
      · have hyz : y ≠ z := by
          intro h; apply hxz; rw [← h, hy]; field_simp
        rw [if_neg hxz, if_neg hyz]
        simp only [hGdef]
        rw [show lam * z / lam = z by field_simp, ← hy]
        have h1 : x - lam * z = lam * (y - z) := by rw [hy]; field_simp
        have h2 : y - z ≠ 0 := sub_ne_zero.mpr hyz
        rw [h1]; field_simp
    have hA : ∀ v, A_eps p 1 (Real.sqrt ε * v) = A_eps p ε v := by
      intro v; unfold A_eps
      rw [mul_pow, Real.sq_sqrt hε.le]; ring_nf
    have hpt : ∀ z, (deriv G x - deriv G (lam * z)) / |x - lam * z| ^ (p + 1) *
        A_eps p 1 (c01_secant G x (lam * z)) =
        (Real.sqrt ε * lam ^ (-(p + 1))) * ((deriv f y - deriv f z) / |y - z| ^ (p + 1) *
          A_eps p ε (c01_secant f y z)) := by
      intro z
      rw [hS, hA, hGd]
      simp only
      rw [show lam * z / lam = z by field_simp, ← hy]
      have h1 : |x - lam * z| = lam * |y - z| := by
        rw [show x - lam * z = lam * (y - z) by rw [hy]; field_simp, abs_mul, abs_of_pos hlam]
      rw [h1, Real.mul_rpow hlam.le (abs_nonneg _), Real.rpow_neg hlam.le]
      field_simp
    unfold c01_Jfull_eps
    have hsub : ∫ x', (deriv G x - deriv G x') / |x - x'| ^ (p + 1) * A_eps p 1 (c01_secant G x x')
        = lam * ∫ z, (deriv G x - deriv G (lam * z)) / |x - lam * z| ^ (p + 1) *
            A_eps p 1 (c01_secant G x (lam * z)) := by
      rw [Measure.integral_comp_mul_left (fun x' => (deriv G x - deriv G x') / |x - x'| ^ (p + 1) *
        A_eps p 1 (c01_secant G x x')) lam, smul_eq_mul, abs_of_pos (inv_pos.mpr hlam), ← mul_assoc,
        mul_inv_cancel₀ hlam0, one_mul]
    rw [hsub]
    simp_rw [hpt]
    rw [integral_const_mul]
    have : lam ^ (1 - (p + 1)) = lam * lam ^ (-(p + 1)) := by
      rw [sub_eq_add_neg, Real.rpow_add hlam, Real.rpow_one]
    rw [this]; ring

/-- Continuous partial derivatives give a Fréchet derivative of `(y,τ) ↦ f y τ`. -/
theorem c01_aux_partials_hasFDerivAt (f : ℝ → ℝ → ℝ)
    (hf_y : ∀ τ, Differentiable ℝ (fun y => f y τ))
    (hf_τ : ∀ y, Differentiable ℝ (fun τ => f y τ))
    (hfy_c : Continuous (fun q : ℝ × ℝ => deriv (fun y => f y q.2) q.1))
    (hfτ_c : Continuous (fun q : ℝ × ℝ => deriv (fun τ => f q.1 τ) q.2)) (u : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => f q.1 q.2)
      (deriv (fun y => f y u.2) u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
        deriv (fun τ => f u.1 τ) u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) u := by
  have hsr : Continuous (fun c : ℝ => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous
  have h := hasStrictFDerivAt_uncurry_coprod (u := u) (f := f)
    (f₁ := fun v w => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv (fun y => f y w) v))
    (f₂ := fun v w => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv (fun τ => f v τ) w))
    (Eventually.of_forall fun v => ((hf_y v.2) v.1).hasDerivAt.hasFDerivAt)
    (Eventually.of_forall fun v => ((hf_τ v.1) v.2).hasDerivAt.hasFDerivAt)
    (hsr.comp hfy_c).continuousAt (hsr.comp hfτ_c).continuousAt
  refine h.hasFDerivAt.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun z => ?_
  simp [Function.HasUncurry.uncurry, mul_comm]

/-- Continuous partial derivatives give joint `C¹` regularity. -/
theorem c01_aux_partials_contDiff (f : ℝ → ℝ → ℝ)
    (hf_y : ∀ τ, Differentiable ℝ (fun y => f y τ))
    (hf_τ : ∀ y, Differentiable ℝ (fun τ => f y τ))
    (hfy_c : Continuous (fun q : ℝ × ℝ => deriv (fun y => f y q.2) q.1))
    (hfτ_c : Continuous (fun q : ℝ × ℝ => deriv (fun τ => f q.1 τ) q.2)) :
    ContDiff ℝ 1 (fun q : ℝ × ℝ => f q.1 q.2) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨fun u => deriv (fun y => f y u.2) u.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      deriv (fun τ => f u.1 τ) u.2 • ContinuousLinearMap.snd ℝ ℝ ℝ,
    (hfy_c.smul continuous_const).add (hfτ_c.smul continuous_const),
    fun u => c01_aux_partials_hasFDerivAt f hf_y hf_τ hfy_c hfτ_c u⟩

/-- `(x ↦ c g(x/L))'' = c L⁻² g''(x/L)`. -/
theorem c01_aux_iter2_scale (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (c L x : ℝ) :
    iteratedDeriv 2 (fun x => c * g (x / L)) x = c * (L⁻¹) ^ 2 * iteratedDeriv 2 g (x / L) := by
  rw [iteratedDeriv_const_mul_field]
  have e : (fun x' => g (x' / L)) = fun x' => g (L⁻¹ * x') := by
    funext x'; rw [div_eq_inv_mul]
  rw [e, iteratedDeriv_comp_const_mul (n := 2) (by exact_mod_cast hg)]
  simp only
  rw [← div_eq_inv_mul]; ring

/-- Blueprint: lem:c01_self_similar_evolution.  For `f(y,τ)` with `f, ∂_y f, ∂_y² f, ∂_τ f`
continuous and `∂_y f(·,τ)` bounded, `F(x,t) = √ε L(t) f(x/L(t), -log L(t))` is a classical
solution on `ℝ × (-∞,T)` iff `∂_τ f = f - y ∂_y f + 𝒥_ε(f(·,τ))` for all `(y,τ)`. -/
theorem c01_self_similar_evolution (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε T : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ → ℝ)
    (hf_y : ∀ τ, ContDiff ℝ 2 (fun y => f y τ))
    (hf_τ : ∀ y, Differentiable ℝ (fun τ => f y τ))
    (hf_c : Continuous (fun q : ℝ × ℝ => f q.1 q.2))
    (hfy_c : Continuous (fun q : ℝ × ℝ => deriv (fun y => f y q.2) q.1))
    (hfyy_c : Continuous (fun q : ℝ × ℝ => iteratedDeriv 2 (fun y => f y q.2) q.1))
    (hfτ_c : Continuous (fun q : ℝ × ℝ => deriv (fun τ => f q.1 τ) q.2))
    (hbdd : ∀ τ, ∃ M : ℝ, ∀ y, |deriv (fun y' => f y' τ) y| ≤ M) :
    gsqg_front_equation p (Iio T)
        (fun x t => Real.sqrt ε * self_similar_ansatz_L p T t *
          f (x / self_similar_ansatz_L p T t) (-Real.log (self_similar_ansatz_L p T t))) ↔
      ∀ y τ : ℝ, deriv (fun τ' => f y τ') τ =
        f y τ - y * deriv (fun y' => f y' τ) y + c01_Jfull_eps p ε (fun y' => f y' τ) y := by
  have hLp := c01_L_properties p hp hp1 T
  set L := self_similar_ansatz_L p T with hLdef
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  set S : Set (ℝ × ℝ) := univ ×ˢ Iio T with hS
  have hfyd : ∀ τ, Differentiable ℝ (fun y => f y τ) := fun τ => (hf_y τ).differentiable two_ne_zero
  have hFd := c01_aux_partials_hasFDerivAt f hfyd hf_τ hfy_c hfτ_c
  have hFc1 := c01_aux_partials_contDiff f hfyd hf_τ hfy_c hfτ_c
  have hA : ∀ τ, (fun y => f y τ) ∈ c01_admissible_class := fun τ =>
    ⟨(hf_y τ).of_le (by norm_num), hbdd τ,
      (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) (fun y => f y τ) from hf_y τ)).2.2.locallyLipschitz⟩
  have heq : ∀ x t, t < T →
      (deriv (fun s => Real.sqrt ε * L s * f (x / L s) (-Real.log (L s))) t =
        c01_Jfull_eps p 1 (fun x' => Real.sqrt ε * L t * f (x' / L t) (-Real.log (L t))) x ↔
      deriv (fun τ' => f (x / L t) τ') (-Real.log (L t)) =
        f (x / L t) (-Real.log (L t)) - x / L t * deriv (fun y' => f y' (-Real.log (L t))) (x / L t) +
          c01_Jfull_eps p ε (fun y' => f y' (-Real.log (L t))) (x / L t)) := by
    intro x t ht
    have hL0 : 0 < L t := hLp.2.1 t ht
    have hLd : HasDerivAt L (-(L t ^ (1 - (p + 1)))) t := hLp.2.2.2 t ht
    have hd1 : HasDerivAt (fun s => x / L s) ((0 * L t - x * -(L t ^ (1 - (p + 1)))) / L t ^ 2) t :=
      (hasDerivAt_const t x).div hLd hL0.ne'
    have hd2 : HasDerivAt (fun s => -Real.log (L s)) (-(-(L t ^ (1 - (p + 1))) / L t)) t :=
      (hLd.log hL0.ne').neg
    have hcomp : HasDerivAt (fun s => f (x / L s) (-Real.log (L s)))
        (deriv (fun y => f y (-Real.log (L t))) (x / L t) *
            ((0 * L t - x * -(L t ^ (1 - (p + 1)))) / L t ^ 2) +
          deriv (fun τ => f (x / L t) τ) (-Real.log (L t)) * (-(-(L t ^ (1 - (p + 1))) / L t))) t := by
      have := (hFd (x / L t, -Real.log (L t))).comp_hasDerivAt t (hd1.prodMk hd2)
      refine this.congr_deriv ?_
      simp [mul_comm]
    have hfull : HasDerivAt (fun s => Real.sqrt ε * L s * f (x / L s) (-Real.log (L s)))
        (Real.sqrt ε * -(L t ^ (1 - (p + 1))) * f (x / L t) (-Real.log (L t)) +
          Real.sqrt ε * L t * (deriv (fun y => f y (-Real.log (L t))) (x / L t) *
            ((0 * L t - x * -(L t ^ (1 - (p + 1)))) / L t ^ 2) +
          deriv (fun τ => f (x / L t) τ) (-Real.log (L t)) * (-(-(L t ^ (1 - (p + 1))) / L t)))) t :=
      (hLd.const_mul (Real.sqrt ε)).mul hcomp
    have hJ : c01_Jfull_eps p 1 (fun x' => Real.sqrt ε * L t * f (x' / L t) (-Real.log (L t))) x =
        Real.sqrt ε * L t ^ (1 - (p + 1)) *
          c01_Jfull_eps p ε (fun y' => f y' (-Real.log (L t))) (x / L t) :=
      (c01_J_scaling p hp hp1 ε (L t) hε hL0 _ (hA (-Real.log (L t)))).2 x
    rw [hfull.deriv, hJ]
    have hKpos : 0 < Real.sqrt ε * L t ^ (1 - (p + 1)) := mul_pos hsε (Real.rpow_pos_of_pos hL0 _)
    have hLne : L t ≠ 0 := hL0.ne'
    set K := L t ^ (1 - (p + 1))
    set fy := deriv (fun y => f y (-Real.log (L t))) (x / L t)
    set fτ := deriv (fun τ => f (x / L t) τ) (-Real.log (L t))
    set J := c01_Jfull_eps p ε (fun y' => f y' (-Real.log (L t))) (x / L t)
    have e : Real.sqrt ε * -K * f (x / L t) (-Real.log (L t)) +
        Real.sqrt ε * L t * (fy * ((0 * L t - x * -K) / L t ^ 2) + fτ * (-(-K / L t))) =
        Real.sqrt ε * K * (fτ - f (x / L t) (-Real.log (L t)) + x / L t * fy) := by
      field_simp; ring
    rw [e]
    constructor
    · intro h
      have h' := mul_left_cancel₀ hKpos.ne' h
      linarith
    · intro h
      rw [show fτ - f (x / L t) (-Real.log (L t)) + x / L t * fy = J by linarith]
  have hLc : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => L q.2) S :=
    (hLp.1.of_le (WithTop.coe_le_coe.mpr le_top)).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  have hne : ∀ q ∈ S, L q.2 ≠ 0 := fun q hq => (hLp.2.1 q.2 hq.2).ne'
  have hΦc : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => (q.1 / L q.2, -Real.log (L q.2))) S :=
    (contDiff_fst.contDiffOn.div hLc hne).prodMk (hLc.log hne).neg
  have ha : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Real.sqrt ε * L q.2 *
      f (q.1 / L q.2) (-Real.log (L q.2))) S := by
    show ContDiffOn ℝ 1 (fun q : ℝ × ℝ => Real.sqrt ε * L q.2 *
      (fun q : ℝ × ℝ => f q.1 q.2) (q.1 / L q.2, -Real.log (L q.2))) S
    exact (contDiffOn_const.mul hLc).mul (hFc1.comp_contDiffOn hΦc)
  have hb : ∀ t ∈ Iio T, ContDiff ℝ 2 (fun x => Real.sqrt ε * L t *
      f (x / L t) (-Real.log (L t))) := fun t _ =>
    contDiff_const.mul ((hf_y _).comp (contDiff_id.div_const _))
  have hc : ContinuousOn (fun q : ℝ × ℝ => iteratedDeriv 2 (fun x => Real.sqrt ε * L q.2 *
      f (x / L q.2) (-Real.log (L q.2))) q.1) S := by
    have h1 : ContinuousOn (fun q : ℝ × ℝ => Real.sqrt ε * L q.2 * (L q.2)⁻¹ ^ 2 *
        (fun q : ℝ × ℝ => iteratedDeriv 2 (fun y => f y q.2) q.1)
          (q.1 / L q.2, -Real.log (L q.2))) S :=
      ((continuousOn_const.mul hLc.continuousOn).mul ((hLc.continuousOn.inv₀ hne).pow 2)).mul
        (hfyy_c.comp_continuousOn hΦc.continuousOn)
    refine h1.congr fun q _ => ?_
    exact c01_aux_iter2_scale (fun y => f y (-Real.log (L q.2))) (hf_y _) _ _ _
  have hd : ∀ t ∈ Iio T, ∃ M : ℝ, ∀ x, |deriv (fun x => Real.sqrt ε * L t *
      f (x / L t) (-Real.log (L t))) x| ≤ M := by
    intro t ht
    obtain ⟨M, hM⟩ := hbdd (-Real.log (L t))
    refine ⟨Real.sqrt ε * M, fun x => ?_⟩
    rw [(c01_aux_scaled_hasDerivAt ε (L t) (hLp.2.1 t ht) (fun y => f y (-Real.log (L t)))
      (hfyd _) x).deriv, abs_mul, abs_of_pos hsε]
    exact mul_le_mul_of_nonneg_left (hM _) hsε.le
  constructor
  · intro h y τ
    have hp0 : 0 < p + 1 := by linarith
    set t := T - Real.exp (-(p + 1) * τ) / (p + 1) with htdef
    have ht : t < T := by
      have : 0 < Real.exp (-(p + 1) * τ) / (p + 1) := div_pos (Real.exp_pos _) hp0
      linarith
    have hLt : L t = Real.exp (-τ) := by
      simp only [hLdef, self_similar_ansatz_L]
      rw [show (p + 1) * (T - t) = Real.exp (-(p + 1) * τ) by rw [htdef]; field_simp; ring,
        ← Real.exp_mul]
      congr 1; field_simp
    have hτ : -Real.log (L t) = τ := by rw [hLt, Real.log_exp, neg_neg]
    have hx : y * L t / L t = y := mul_div_cancel_right₀ y (hLp.2.1 t ht).ne'
    have := (heq (y * L t) t ht).mp (h.2.2.2.2 t ht (y * L t))
    rw [hx, hτ] at this
    exact this
  · intro h
    exact ⟨ha, hb, hc, hd, fun t ht x => (heq x t ht).mpr (h _ _)⟩

/-- Blueprint: lem:c01_J_decomposition.  For `ε ≥ 0`, `f ∈ 𝒜`, the integrals defining
`𝒥̃_ε(f)(y)` and `𝒬_ε(f)(y)` converge absolutely and
`𝒥_ε(f) = |D|^p∂_y f + 𝒬_ε(f) = A_ε(f') |D|^p∂_y f + 𝒥̃_ε(f)` pointwise. -/
theorem c01_J_decomposition (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) (y : ℝ) :
    Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
        (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))) ∧
    Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
        (A_eps p ε (c01_secant f y z) - 1)) ∧
    c01_Jfull_eps p ε f y = fracDdy p f y + c01_Q_eps p ε f y ∧
    c01_Jfull_eps p ε f y = A_eps p ε (deriv f y) * fracDdy p f y + J_eps p ε f y := by
  obtain ⟨Λ, hΛ, hLip⟩ := c01_aux_lip f hf y
  obtain ⟨M, hM⟩ := hf.2.1
  have hcont : Continuous (deriv f) := hf.1.continuous_deriv le_rfl
  have hI := (c01_frac_well_defined p hp hp1 (deriv f) hcont.aestronglyMeasurable M
    (Eventually.of_forall hM) y Λ hΛ hLip).1
  have hJ := (c01_J_well_defined p hp hp1 ε hε f hf M hM y Λ hΛ hLip).1
  set F := fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1)
  have e1 : (fun z => F z * (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))) =
      fun z => F z * A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y) * F z := by
    funext z; ring
  have e2 : (fun z => F z * (A_eps p ε (c01_secant f y z) - 1)) =
      fun z => F z * A_eps p ε (c01_secant f y z) - F z := by
    funext z; ring
  have i1 : Integrable (fun z => F z * (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))) := by
    rw [e1]; exact hJ.sub (hI.const_mul _)
  have i2 : Integrable (fun z => F z * (A_eps p ε (c01_secant f y z) - 1)) := by
    rw [e2]; exact hJ.sub hI
  refine ⟨i1, i2, ?_, ?_⟩
  · unfold c01_Jfull_eps fracDdy fracD c01_Q_eps
    change calpha p * ∫ z, F z * A_eps p ε (c01_secant f y z) =
      (calpha p * ∫ z, F z) + calpha p * ∫ z, F z * (A_eps p ε (c01_secant f y z) - 1)
    rw [e2, integral_sub hJ hI]; ring
  · unfold c01_Jfull_eps fracDdy fracD J_eps
    change calpha p * ∫ z, F z * A_eps p ε (c01_secant f y z) =
      A_eps p ε (deriv f y) * (calpha p * ∫ z, F z) +
        calpha p * ∫ z, F z * (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))
    rw [e1, integral_sub hJ (hI.const_mul _), integral_const_mul]; ring

/-- `∫_a^b (x - c) dx = ((b-c)² - (a-c)²)/2`. -/
theorem c01_aux_integral_sub_lin (a b c : ℝ) :
    ∫ x in a..b, (x - c) = ((b - c) ^ 2 - (a - c) ^ 2) / 2 := by
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => (x - c) ^ 2 / 2) (x - c) x := by
    intro x _
    have := (((hasDerivAt_id x).sub_const c).pow 2).div_const 2
    refine this.congr_deriv ?_
    norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.sub continuous_const).intervalIntegrable _ _)]
  ring

/-- Second-order secant estimate: `|S_f(y,z) - f'(y)| ≤ Λ|y-z|/2` when `f'` is `Λ`-Lipschitz on
`[y-1,y+1]` and `|z-y| ≤ 1`. -/
theorem c01_aux_secant_dev (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (y z Λ : ℝ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1),
      |deriv f z - deriv f w| ≤ Λ * |z - w|) (hz : |z - y| ≤ 1) :
    |c01_secant f y z - deriv f y| ≤ Λ * |y - z| / 2 := by
  by_cases hzy : y = z
  · subst hzy; simp [c01_secant]
  have hcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  set h : ℝ → ℝ := fun w => f w - w * deriv f y with hh
  have hderiv : ∀ w, HasDerivAt h (deriv f w - deriv f y) w := by
    intro w
    have := (hfd w).hasDerivAt.sub ((hasDerivAt_id' w).mul_const (deriv f y))
    rw [one_mul] at this; exact this
  have hint : IntervalIntegrable (fun w => deriv f w - deriv f y) volume z y :=
    (hcont.sub continuous_const).intervalIntegrable _ _
  have hftc : ∫ w in z..y, (deriv f w - deriv f y) = h y - h z :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hderiv w) hint
  have hsec : c01_secant f y z - deriv f y = (h y - h z) / (y - z) := by
    unfold c01_secant; rw [if_neg hzy]
    have : y - z ≠ 0 := sub_ne_zero.mpr hzy
    simp only [hh]; field_simp; ring
  have hmem : ∀ w ∈ uIcc z y, w ∈ Icc (y - 1) (y + 1) := by
    intro w hw
    rw [abs_le] at hz
    rcases le_total z y with h1 | h1
    · rw [uIcc_of_le h1] at hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
    · rw [uIcc_of_ge h1] at hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hy' : y ∈ Icc (y - 1) (y + 1) := ⟨by linarith, by linarith⟩
  have hbound : |h y - h z| ≤ Λ * (y - z) ^ 2 / 2 := by
    rw [← hftc]
    rcases lt_or_gt_of_ne hzy with h1 | h1
    · -- y < z
      rw [intervalIntegral.integral_symm, abs_neg]
      have hle := intervalIntegral.norm_integral_le_of_norm_le h1.le
        (g := fun w => Λ * (w - y)) (f := fun w => deriv f w - deriv f y)
        (Eventually.of_forall fun w hw => by
          have hw' : w ∈ uIcc z y := by rw [uIcc_of_ge h1.le]; exact Ioc_subset_Icc_self hw
          have := hLip w (hmem w hw') y hy'
          rw [Real.norm_eq_abs]
          rwa [abs_of_nonneg (by linarith [hw.1] : (0:ℝ) ≤ w - y)] at this)
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable (μ := volume) _ _)
      rw [Real.norm_eq_abs] at hle
      refine hle.trans (le_of_eq ?_)
      simp only [intervalIntegral.integral_const_mul]
      rw [c01_aux_integral_sub_lin]; ring
    · -- z < y
      have hle := intervalIntegral.norm_integral_le_of_norm_le h1.le
        (g := fun w => Λ * (y - w)) (f := fun w => deriv f w - deriv f y)
        (Eventually.of_forall fun w hw => by
          have hw' : w ∈ uIcc z y := by rw [uIcc_of_le h1.le]; exact Ioc_subset_Icc_self hw
          have := hLip w (hmem w hw') y hy'
          rw [Real.norm_eq_abs]
          rwa [abs_sub_comm w y, abs_of_nonneg (by linarith [hw.2] : (0:ℝ) ≤ y - w)] at this)
        ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable (μ := volume) _ _)
      rw [Real.norm_eq_abs] at hle
      refine hle.trans (le_of_eq ?_)
      simp only [intervalIntegral.integral_const_mul]
      rw [show (∫ x in z..y, y - x) = -(∫ x in z..y, x - y) by
        rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring]
      rw [c01_aux_integral_sub_lin]; ring
  rw [hsec, abs_div]
  have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr hzy)
  rw [div_le_iff₀ hpos]
  calc |h y - h z| ≤ Λ * (y - z) ^ 2 / 2 := hbound
    _ = Λ * |y - z| / 2 * |y - z| := by rw [← sq_abs (y - z)]; ring

/-- Lipschitz bound for `A_ε` on `[-M, M]`: `|A_ε(u) - A_ε(v)| ≤ αεM|u-v|`. -/
theorem c01_aux_A_lip (p ε M : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (u v : ℝ) (hu : |u| ≤ M)
    (hv : |v| ≤ M) : |A_eps p ε u - A_eps p ε v| ≤ (p + 1) * ε * M * |u - v| := by
  have hd : ∀ w, HasDerivAt (A_eps p ε)
      (2 * ε * w * (-(p + 1) / 2) * (1 + ε * w ^ 2) ^ (-(p + 1) / 2 - 1)) w := by
    intro w
    have h1 : HasDerivAt (fun w : ℝ => 1 + ε * w ^ 2) (2 * ε * w) w := by
      have := (hasDerivAt_const w (1:ℝ)).add ((hasDerivAt_pow 2 w).const_mul ε)
      convert this using 1; simp; ring
    have hpos : 0 < 1 + ε * w ^ 2 := by positivity
    exact h1.rpow_const (Or.inl hpos.ne')
  have hbd : ∀ w ∈ Icc (-M) M, ‖2 * ε * w * (-(p + 1) / 2) *
      (1 + ε * w ^ 2) ^ (-(p + 1) / 2 - 1)‖ ≤ (p + 1) * ε * M := by
    intro w hw
    have hw' : |w| ≤ M := abs_le.mpr hw
    have h1 : 1 ≤ 1 + ε * w ^ 2 := by nlinarith [sq_nonneg w]
    have h2 : (1 + ε * w ^ 2) ^ (-(p + 1) / 2 - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have h3 : 0 ≤ (1 + ε * w ^ 2) ^ (-(p + 1) / 2 - 1) := Real.rpow_nonneg (by linarith) _
    have e : ‖2 * ε * w * (-(p + 1) / 2) * (1 + ε * w ^ 2) ^ (-(p + 1) / 2 - 1)‖ =
        (p + 1) * ε * |w| * (1 + ε * w ^ 2) ^ (-(p + 1) / 2 - 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg hε,
        abs_of_neg (by linarith : -(p + 1) / 2 < 0)]
      norm_num; ring
    rw [e]
    have h4 : (p + 1) * ε * |w| ≤ (p + 1) * ε * M :=
      mul_le_mul_of_nonneg_left hw' (by positivity)
    calc (p + 1) * ε * |w| * (1 + ε * w ^ 2) ^ (-(p + 1) / 2 - 1) ≤ (p + 1) * ε * |w| * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (p + 1) * ε * M := by rw [mul_one]; exact h4
  have := (convex_Icc (-M) M).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (hd w).hasDerivWithinAt) hbd (abs_le.mp hv) (abs_le.mp hu)
  simpa [Real.norm_eq_abs] using this

/-- Blueprint: lem:c01_Jtilde_vanishing.  For `|z - y| ≤ 1` the integrand of `𝒥̃_ε(f)(y)` is
bounded by `c_α α ε ‖f'‖_∞ Λ² |y-z|^{2-α} / 2`, `Λ` a Lipschitz constant of `f'` on `[y-1,y+1]`. -/
theorem c01_Jtilde_vanishing (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) (M : ℝ) (hM : ∀ z, |deriv f z| ≤ M)
    (y Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1),
      |deriv f z - deriv f w| ≤ Λ * |z - w|) :
    ∀ z, |z - y| ≤ 1 →
      |calpha p * ((deriv f y - deriv f z) / |y - z| ^ (p + 1) *
          (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y)))| ≤
        calpha p * (p + 1) * ε * M * Λ ^ 2 * |y - z| ^ (2 - (p + 1)) / 2 := by
  intro z hz
  have hc := c01_aux_calpha_nonneg p hp hp1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfd : Differentiable ℝ f := hf.1.differentiable one_ne_zero
  by_cases hzy : y = z
  · subst hzy
    simp only [sub_self, zero_div, zero_mul, mul_zero, abs_zero]
    have : 0 ≤ |y - y| ^ (2 - (p + 1)) := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr hzy)
  have hS : |c01_secant f y z| ≤ M := by
    unfold c01_secant; rw [if_neg hzy, abs_div, div_le_iff₀ hpos]
    have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun w _ => hfd w) (fun w _ => by rw [Real.norm_eq_abs]; exact hM w) (mem_univ z) (mem_univ y)
    simpa [Real.norm_eq_abs, abs_sub_comm] using this
  have hA := c01_aux_A_lip p ε M hp hε _ _ hS (hM y)
  have hdev := c01_aux_secant_dev f hf.1 y z Λ hLip hz
  have hy' : y ∈ Icc (y - 1) (y + 1) := ⟨by linarith, by linarith⟩
  have hz' : z ∈ Icc (y - 1) (y + 1) := by
    rw [abs_le] at hz; exact ⟨by linarith, by linarith⟩
  have hF := hLip y hy' z hz'
  rw [abs_mul, abs_of_nonneg hc, abs_mul, abs_div, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  have e : |y - z| ^ (2 - (p + 1)) = |y - z| ^ 2 / |y - z| ^ (p + 1) := by
    rw [Real.rpow_sub hpos, Real.rpow_two]
  rw [e]
  have hq : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos hpos _
  have key : |deriv f y - deriv f z| * |A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y)| ≤
      (p + 1) * ε * M * Λ ^ 2 * |y - z| ^ 2 / 2 := by
    calc |deriv f y - deriv f z| * |A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y)|
        ≤ (Λ * |y - z|) * ((p + 1) * ε * M * (Λ * |y - z| / 2)) := by
          apply mul_le_mul hF (hA.trans (mul_le_mul_of_nonneg_left hdev (by positivity)))
            (abs_nonneg _) (by positivity)
      _ = (p + 1) * ε * M * Λ ^ 2 * |y - z| ^ 2 / 2 := by ring
  calc calpha p * (|deriv f y - deriv f z| / |y - z| ^ (p + 1) *
        |A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y)|)
      = calpha p * ((|deriv f y - deriv f z| *
        |A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y)|) / |y - z| ^ (p + 1)) := by ring
    _ ≤ calpha p * (((p + 1) * ε * M * Λ ^ 2 * |y - z| ^ 2 / 2) / |y - z| ^ (p + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact div_le_div_of_nonneg_right key hq.le
    _ = calpha p * (p + 1) * ε * M * Λ ^ 2 * (|y - z| ^ 2 / |y - z| ^ (p + 1)) / 2 := by ring

/-- Blueprint: lem:c01_residual_identity.  For `ε ≥ 0`, `f ∈ 𝒜`:
`ℰ̃_ε(f) = f - y f' + 𝒥_ε(f) = A_ε(f') ℰ_ε(f)` pointwise, hence
`ℰ_ε(f)(y) = 0 ↔ f(y) - y f'(y) + 𝒥_ε(f)(y) = 0`. -/
theorem c01_residual_identity (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) (y : ℝ) :
    c01_quasilinear_residual p ε f y = f y - y * deriv f y + c01_Jfull_eps p ε f y ∧
    f y - y * deriv f y + c01_Jfull_eps p ε f y = A_eps p ε (deriv f y) * residual p ε f y ∧
    (residual p ε f y = 0 ↔ f y - y * deriv f y + c01_Jfull_eps p ε f y = 0) := by
  obtain ⟨-, -, h1, h2⟩ := c01_J_decomposition p hp hp1 ε hε f hf y
  have hA := (c01_aux_A_bounds p ε (deriv f y) hp hε).1
  have e2 : f y - y * deriv f y + c01_Jfull_eps p ε f y = A_eps p ε (deriv f y) * residual p ε f y := by
    unfold residual; rw [h2]; field_simp; ring
  refine ⟨?_, e2, ?_⟩
  · unfold c01_quasilinear_residual L0; rw [h1]; ring
  · rw [e2]; constructor
    · intro h; rw [h, mul_zero]
    · intro h; exact (mul_eq_zero.mp h).resolve_left hA.ne'

/-- Blueprint: lem:self_similar_reduction.  For `ε > 0` and `f ∈ C²` with `f'` bounded (so
`f ∈ 𝒜`), `F_{ε,T,f}` is a classical solution of the front equation on `ℝ × (-∞,T)` iff
`ℰ_ε(f) ≡ 0`. -/
theorem self_similar_reduction (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε T : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hbdd : ∃ M : ℝ, ∀ y, |deriv f y| ≤ M) :
    f ∈ c01_admissible_class ∧
    (gsqg_front_equation p (Iio T) (self_similar_ansatz p ε T f) ↔
      ∀ y, residual p ε f y = 0) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfA : f ∈ c01_admissible_class := by
    refine ⟨hf1, hbdd, ?_⟩
    have h2 : ContDiff ℝ (1 + 1) f := hf
    exact (contDiff_succ_iff_deriv.mp h2).2.2.locallyLipschitz
  refine ⟨hfA, ?_⟩
  obtain ⟨M, hM⟩ := hbdd
  have hLp := c01_L_properties p hp hp1 T
  have AT := c01_ansatz_time_derivative p hp hp1 ε T hε f hf1
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have heq : ∀ t, t < T → ∀ x, (deriv (fun s => self_similar_ansatz p ε T f x s) t =
      c01_Jfull_eps p 1 (fun x' => self_similar_ansatz p ε T f x' t) x ↔
      residual p ε f (x / self_similar_ansatz_L p T t) = 0) := by
    intro t ht x
    have hL := hLp.2.1 t ht
    have h1 := (AT.2.1 x t ht).2
    have h2 := (c01_J_scaling p hp hp1 ε (self_similar_ansatz_L p T t) hε hL f hfA).2 x
    have h3 := (c01_residual_identity p hp hp1 ε hε.le f hfA (x / self_similar_ansatz_L p T t)).2.2
    rw [h3]
    have e : (fun x' => self_similar_ansatz p ε T f x' t) =
        fun x' => Real.sqrt ε * self_similar_ansatz_L p T t * f (x' / self_similar_ansatz_L p T t) :=
      rfl
    rw [h1, e, h2]
    have hk : 0 < Real.sqrt ε * self_similar_ansatz_L p T t ^ (1 - (p + 1)) :=
      mul_pos hsε (Real.rpow_pos_of_pos hL _)
    constructor
    · intro h
      have h' : Real.sqrt ε * self_similar_ansatz_L p T t ^ (1 - (p + 1)) *
          (f (x / self_similar_ansatz_L p T t) -
            x / self_similar_ansatz_L p T t * deriv f (x / self_similar_ansatz_L p T t) +
            c01_Jfull_eps p ε f (x / self_similar_ansatz_L p T t)) = 0 := by
        rw [mul_add]; linarith
      exact (mul_eq_zero.mp h').resolve_left hk.ne'
    · intro h
      have h' : f (x / self_similar_ansatz_L p T t) -
            x / self_similar_ansatz_L p T t * deriv f (x / self_similar_ansatz_L p T t) =
          -c01_Jfull_eps p ε f (x / self_similar_ansatz_L p T t) := by linarith
      rw [h']; ring
  have hLc : ContinuousOn (fun q : ℝ × ℝ => self_similar_ansatz_L p T q.2) (univ ×ˢ Iio T) :=
    hLp.1.continuousOn.comp continuous_snd.continuousOn (fun q hq => hq.2)
  have hLne : ∀ q ∈ (univ ×ˢ Iio T : Set (ℝ × ℝ)), self_similar_ansatz_L p T q.2 ≠ 0 :=
    fun q hq => (hLp.2.1 q.2 hq.2).ne'
  have hc : ContinuousOn (fun q : ℝ × ℝ => Real.sqrt ε * self_similar_ansatz_L p T q.2 ^
      (1 - ((2 : ℕ) : ℝ)) * iteratedDeriv 2 f (q.1 / self_similar_ansatz_L p T q.2))
      (univ ×ˢ Iio T) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.mul (hLc.rpow_const (fun q hq => Or.inl (hLne q hq)))
    · exact (hf.continuous_iteratedDeriv 2 le_rfl).comp_continuousOn
        (continuous_fst.continuousOn.div hLc hLne)
  have hreg : ContinuousOn (fun q : ℝ × ℝ =>
      iteratedDeriv 2 (fun x => self_similar_ansatz p ε T f x q.2) q.1) (univ ×ˢ Iio T) :=
    hc.congr (fun q hq => (AT.2.2 2 hf).2 2 le_rfl q.1 q.2 hq.2)
  have hC2 : ∀ t ∈ Iio T, ContDiff ℝ 2 (fun x => self_similar_ansatz p ε T f x t) := by
    intro t _
    show ContDiff ℝ 2 (fun x => Real.sqrt ε * self_similar_ansatz_L p T t *
      f (x / self_similar_ansatz_L p T t))
    exact contDiff_const.mul (hf.comp (contDiff_id.div_const _))
  have hbd : ∀ t ∈ Iio T, ∃ M : ℝ, ∀ x, |deriv (fun x => self_similar_ansatz p ε T f x t) x| ≤ M := by
    intro t ht
    refine ⟨Real.sqrt ε * M, fun x => ?_⟩
    rw [(AT.2.1 x t ht).1, abs_mul, abs_of_pos hsε]
    exact mul_le_mul_of_nonneg_left (hM _) hsε.le
  constructor
  · intro h y
    have ht : T - 1 < T := by linarith
    have hL := hLp.2.1 (T - 1) ht
    have := (heq (T - 1) ht (y * self_similar_ansatz_L p T (T - 1))).mp
      (h.2.2.2.2 (T - 1) ht (y * self_similar_ansatz_L p T (T - 1)))
    rwa [mul_div_cancel_right₀ _ hL.ne'] at this
  · intro h
    exact ⟨AT.1, hC2, hreg, hbd, fun t ht x => (heq t ht x).mpr (h _)⟩

/-! ### The profile (objects of chapter 02 packaged locally) -/

/-- Chapter-local: items (1)–(2) of thm:fixed_point_approximation for the family
`f̄_{ε,μ} = approximate_solution_family p R ε μ`, `0 ≤ ε ≤ ε₀`, `μ ∈ B̄(μ_*,δ)`: smoothness, the
limits at `±∞`, and the derivative bounds with constants `C_j` uniform in `ε, μ`. -/
def c01_approx_family_good (p R δ ε₀ : ℝ) : Prop :=
  0 < δ ∧ 0 < ε₀ ∧
  (∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar p δ,
    ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family p R ε μ) ∧
    Tendsto (fun y => approximate_solution_family p R ε μ y + y) atBot (𝓝 0) ∧
    Tendsto (approximate_solution_family p R ε μ) atTop (𝓝 0)) ∧
  ∀ j : ℕ, ∃ Cj : ℝ, ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar p δ, ∀ y : ℝ,
    (0 ≤ y → |approximate_solution_family p R ε μ y| ≤ Cj * jb y ^ (-p) ∧
      |iteratedDeriv (j + 1) (approximate_solution_family p R ε μ) y| ≤
        Cj * jb y ^ (-beta p + (j : ℝ) / p)) ∧
    (y ≤ 0 → |iteratedDeriv j (fun y' => approximate_solution_family p R ε μ y' + y') y| ≤
      Cj * jb y ^ (-p - (j : ℝ)))

/-- Chapter-local: `(μ, r)` is a solution of the correction problem of thm:fixed_point_correction
for the family `f̄ = approximate_solution_family P.p R ε ·`: `μ ∈ B̄`, `r ∈ X_{γ₂}`,
`ℒ_ε(r) = -ℰ_ε(f̄_{ε,μ}) - 𝒩_{ε,f̄_{ε,μ}}(r)` on `ℝ`, and `|μ - μ_*| + ‖r‖_{X_{γ₂}} ≤ C₀ ε`. -/
def c01_correction_data (P : parameters) (R δ C₀ ε : ℝ) (μ : ℂ) (r : ℝ → ℝ) : Prop :=
  μ ∈ Bbar P.p δ ∧ r ∈ X_gamma P.p P.γ₂ ∧
  (∀ y, L_eps P.p ε r y = -residual P.p ε (approximate_solution_family P.p R ε μ) y -
    N_eps P.p ε (approximate_solution_family P.p R ε μ) r y) ∧
  ‖μ - mu_star P.p‖ + xNorm P.p P.γ₂ r ≤ C₀ * ε

/-- Chapter-local: the profile bounds of item (1) of thm:main with constant `C`. -/
def c01_profile_bounds_hold (p C : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ y : ℝ, y ≤ 0 → ∀ j : ℕ, j ≤ 2 →
      |iteratedDeriv j (fun y' => f y' + y') y| ≤ C * jb y ^ (-p - (j : ℝ))) ∧
  (∀ y : ℝ, 0 ≤ y → |f y| ≤ C * jb y ^ (-p)) ∧
  (∀ y : ℝ, 0 ≤ y → ∀ j : ℕ, j ≤ 1 →
      |iteratedDeriv (j + 1) f y| ≤ C * jb y ^ (-beta p + (j : ℝ) / p))

/-- Weighted-bound extraction: from `J^γ (J^e a) ≤ ρ` (`J ≥ 1`) get `a ≤ ρ J^s` for `s ≥ -γ-e`. -/
theorem c01_aux_wb (J γ e s a ρ : ℝ) (hJ : 1 ≤ J) (hρ : 0 ≤ ρ) (hs : -γ - e ≤ s)
    (h : J ^ γ * (J ^ e * a) ≤ ρ) : a ≤ ρ * J ^ s := by
  have hJ0 : 0 < J := by linarith
  have h1 : a = J ^ (-γ - e) * (J ^ γ * (J ^ e * a)) := by
    rw [show J ^ (-γ - e) * (J ^ γ * (J ^ e * a)) = J ^ (-γ - e + γ + e) * a by
      rw [Real.rpow_add hJ0, Real.rpow_add hJ0]; ring]
    rw [show -γ - e + γ + e = 0 by ring, Real.rpow_zero, one_mul]
  rw [h1]
  calc J ^ (-γ - e) * (J ^ γ * (J ^ e * a)) ≤ J ^ (-γ - e) * ρ :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hJ0.le _)
    _ ≤ J ^ s * ρ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hJ hs) hρ
    _ = ρ * J ^ s := by ring

/-- `|a + b| ≤ C X` from `|a| ≤ C₁ X`, `|b| ≤ ρ X`, `C₁ + ρ ≤ C`. -/
theorem c01_aux_sum_bound (a b C₁ ρ C X : ℝ) (ha : |a| ≤ C₁ * X) (hb : |b| ≤ ρ * X)
    (hX : 0 ≤ X) (hC : C₁ + ρ ≤ C) : |a + b| ≤ C * X := by
  calc |a + b| ≤ |a| + |b| := abs_add_le _ _
    _ ≤ C₁ * X + ρ * X := add_le_add ha hb
    _ = (C₁ + ρ) * X := by ring
    _ ≤ C * X := mul_le_mul_of_nonneg_right hC hX

/-- An a.e. bound (on a half-line) of a continuous function holds everywhere on the half-line. -/
theorem c01_aux_ae_to_all (g : ℝ → ℝ) (hg : Continuous g) (c : ℝ) (s : Set ℝ)
    (hs : s = Ici 0 ∨ s = Iic 0) (h : ∀ᵐ y ∂(volume.restrict s), g y ≤ c) :
    ∀ y ∈ s, g y ≤ c := by
  have hsm : MeasurableSet s := by rcases hs with rfl | rfl <;> measurability
  intro y0 hy0
  by_contra hlt
  push Not at hlt
  have hopen : IsOpen {y | c < g y} := isOpen_lt continuous_const hg
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen y0 hlt
  have hnull : volume ({y | ¬ g y ≤ c} ∩ s) = 0 := by
    rw [ae_iff, Measure.restrict_apply' hsm] at h; exact h
  have hsub : ∀ a b, a < b → Ioo a b ⊆ Metric.ball y0 δ → Ioo a b ⊆ s →
      Ioo a b ⊆ {y | ¬ g y ≤ c} ∩ s := by
    intro a b _ h1 h2 y hy
    exact ⟨not_le.mpr (hball (h1 hy)), h2 hy⟩
  have hpos : ∃ a b, a < b ∧ Ioo a b ⊆ Metric.ball y0 δ ∧ Ioo a b ⊆ s := by
    rcases hs with rfl | rfl
    · refine ⟨y0, y0 + δ, by linarith, fun y hy => ?_, fun y hy => ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
      · exact le_of_lt (lt_of_le_of_lt (mem_Ici.mp hy0) hy.1)
    · refine ⟨y0 - δ, y0, by linarith, fun y hy => ?_, fun y hy => ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
      · exact le_of_lt (lt_of_lt_of_le hy.2 (mem_Iic.mp hy0))
  obtain ⟨a, b, hab, h1, h2⟩ := hpos
  have := measure_mono_null (hsub a b hab h1 h2) hnull
  rw [Real.volume_Ioo] at this
  simp at this
  linarith

/-- The weights of `X_γ` are a.e. bounded by `‖r‖_{X_γ}` (on `y ≥ 0`). -/
theorem c01_aux_X_ae_pos (p γ : ℝ) (r : ℝ → ℝ) (hr : X_gamma_norm p γ r < ⊤) :
    ∀ᵐ y ∂(volume.restrict (Ici 0)), jb y ^ γ * (|r y| + jb y ^ (-1 / p) * |deriv r y| +
      jb y ^ (-2 / p) * |deriv (deriv r) y|) ≤ xNorm p γ r := by
  filter_upwards [ENNReal.ae_le_essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ +
    jb y ^ (-1 / p) * ‖deriv r y‖ + jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)))
    (μ := volume.restrict (Ici 0))] with y hy
  have h2 : ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)) ≤ X_gamma_norm p γ r :=
    hy.trans le_self_add
  rw [ENNReal.ofReal_le_iff_le_toReal hr.ne] at h2
  simpa [Real.norm_eq_abs, xNorm] using h2

/-- The weights of `X_γ` are a.e. bounded by `‖r‖_{X_γ}` (on `y ≤ 0`). -/
theorem c01_aux_X_ae_neg (p γ : ℝ) (r : ℝ → ℝ) (hr : X_gamma_norm p γ r < ⊤) :
    ∀ᵐ y ∂(volume.restrict (Iic 0)), jb y ^ γ * (|r y| + jb y * |deriv r y| +
      jb y ^ (2 : ℕ) * |deriv (deriv r) y|) ≤ xNorm p γ r := by
  filter_upwards [ENNReal.ae_le_essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ +
    jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖)))
    (μ := volume.restrict (Iic 0))] with y hy
  have h2 : ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖)) ≤ X_gamma_norm p γ r :=
    hy.trans le_add_self
  rw [ENNReal.ofReal_le_iff_le_toReal hr.ne] at h2
  simpa [Real.norm_eq_abs, xNorm] using h2

/-- `jb` is continuous and positive. -/
theorem c01_aux_jb_cont : Continuous jb := by
  unfold jb; fun_prop

/-- `⟨y⟩^{-a} → 0` at `±∞` for `a > 0`. -/
theorem c01_aux_jb_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun y => jb y ^ (-a)) atTop (𝓝 0) ∧ Tendsto (fun y => jb y ^ (-a)) atBot (𝓝 0) := by
  have hge : ∀ y, |y| ≤ jb y := fun y => by
    unfold jb
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have h1 : Tendsto jb atTop atTop :=
    tendsto_atTop_mono (fun y => (le_abs_self y).trans (hge y)) tendsto_id
  have h2 : Tendsto jb atBot atTop :=
    tendsto_atTop_mono (fun y => (neg_le_abs y).trans (hge y)) tendsto_neg_atBot_atTop
  exact ⟨(tendsto_rpow_neg_atTop ha).comp h1, (tendsto_rpow_neg_atTop ha).comp h2⟩

/-- Squeeze: `|u - L| ≤ g` eventually and `g → 0` give `u → L`. -/
theorem c01_aux_squeeze {l : Filter ℝ} (u g : ℝ → ℝ) (L : ℝ) (hg : Tendsto g l (𝓝 0))
    (h : ∀ᶠ y in l, |u y - L| ≤ g y) : Tendsto u l (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (h.mono fun y hy => by rw [Real.norm_eq_abs]; exact hy) hg

/-- Pointwise bounds for `r ∈ X_γ` (`r`, `r'` everywhere by continuity; `r''` a.e.). -/
theorem c01_aux_X_pointwise (p γ : ℝ) (r : ℝ → ℝ) (hr : r ∈ X_gamma p γ) :
    (∀ y, jb y ^ γ * |r y| ≤ xNorm p γ r) ∧
    (∀ y, 0 ≤ y → jb y ^ γ * (jb y ^ (-1 / p) * |deriv r y|) ≤ xNorm p γ r) ∧
    (∀ y, y ≤ 0 → jb y ^ γ * (jb y ^ (1 : ℝ) * |deriv r y|) ≤ xNorm p γ r) ∧
    (∀ᵐ y ∂(volume.restrict (Ici 0)),
      jb y ^ γ * (jb y ^ (-2 / p) * |deriv (deriv r) y|) ≤ xNorm p γ r) ∧
    (∀ᵐ y ∂(volume.restrict (Iic 0)),
      jb y ^ γ * (jb y ^ (2 : ℝ) * |deriv (deriv r) y|) ≤ xNorm p γ r) := by
  have hP := c01_aux_X_ae_pos p γ r hr.2
  have hN := c01_aux_X_ae_neg p γ r hr.2
  have hrc : Continuous r := hr.1.1.continuous
  have hdc : Continuous (deriv r) := hr.1.1.continuous_deriv le_rfl
  have hJ0 : ∀ y, 0 < jb y := fun y => by linarith [c01_aux_one_le_jb y]
  have hJc : ∀ e : ℝ, Continuous (fun y => jb y ^ e) := fun e =>
    c01_aux_jb_cont.rpow_const (fun y => Or.inl (hJ0 y).ne')
  have hX : ∀ y (a : ℝ), 0 ≤ jb y ^ a := fun y a => Real.rpow_nonneg (hJ0 y).le a
  have hJγ : ∀ y, 0 ≤ jb y ^ γ := fun y => hX y γ
  refine ⟨fun y => ?_, ?_, ?_, ?_, ?_⟩
  · rcases le_total 0 y with hy | hy
    · refine c01_aux_ae_to_all (fun y => jb y ^ γ * |r y|) ((hJc γ).mul hrc.abs) _ (Ici 0)
        (Or.inl rfl) ?_ y hy
      filter_upwards [hP] with y hy
      refine (mul_le_mul_of_nonneg_left ?_ (hJγ y)).trans hy
      have := mul_nonneg (hX y (-1 / p)) (abs_nonneg (deriv r y))
      have := mul_nonneg (hX y (-2 / p)) (abs_nonneg (deriv (deriv r) y))
      linarith
    · refine c01_aux_ae_to_all (fun y => jb y ^ γ * |r y|) ((hJc γ).mul hrc.abs) _ (Iic 0)
        (Or.inr rfl) ?_ y hy
      filter_upwards [hN] with y hy
      refine (mul_le_mul_of_nonneg_left ?_ (hJγ y)).trans hy
      have := mul_nonneg (hJ0 y).le (abs_nonneg (deriv r y))
      have := mul_nonneg (pow_nonneg (hJ0 y).le 2) (abs_nonneg (deriv (deriv r) y))
      linarith
  · refine c01_aux_ae_to_all (fun y => jb y ^ γ * (jb y ^ (-1 / p) * |deriv r y|))
      ((hJc γ).mul ((hJc _).mul hdc.abs)) _ (Ici 0) (Or.inl rfl) ?_
    filter_upwards [hP] with y hy
    refine (mul_le_mul_of_nonneg_left ?_ (hJγ y)).trans hy
    have := abs_nonneg (r y)
    have := mul_nonneg (hX y (-2 / p)) (abs_nonneg (deriv (deriv r) y))
    linarith
  · refine c01_aux_ae_to_all (fun y => jb y ^ γ * (jb y ^ (1 : ℝ) * |deriv r y|))
      ((hJc γ).mul ((hJc _).mul hdc.abs)) _ (Iic 0) (Or.inr rfl) ?_
    filter_upwards [hN] with y hy
    refine (mul_le_mul_of_nonneg_left ?_ (hJγ y)).trans hy
    rw [Real.rpow_one]
    have := abs_nonneg (r y)
    have := mul_nonneg (pow_nonneg (hJ0 y).le 2) (abs_nonneg (deriv (deriv r) y))
    linarith
  · filter_upwards [hP] with y hy
    refine (mul_le_mul_of_nonneg_left ?_ (hJγ y)).trans hy
    have := abs_nonneg (r y)
    have := mul_nonneg (hX y (-1 / p)) (abs_nonneg (deriv r y))
    linarith
  · filter_upwards [hN] with y hy
    refine (mul_le_mul_of_nonneg_left ?_ (hJγ y)).trans hy
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have := abs_nonneg (r y)
    have := mul_nonneg (hJ0 y).le (abs_nonneg (deriv r y))
    linarith

/-- A uniform bound for `f̄'` from `c01_approx_family_good`. -/
theorem c01_aux_good_deriv_bound (p R δ ε₀ : ℝ) (hp : 0 < p)
    (hgood : c01_approx_family_good p R δ ε₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε ∈ Icc 0 ε₀, ∀ μ ∈ Bbar p δ, ∀ y,
      |deriv (approximate_solution_family p R ε μ) y| ≤ M := by
  obtain ⟨-, -, hreg, hC⟩ := hgood
  obtain ⟨C0, hC0⟩ := hC 0
  obtain ⟨C1, hC1⟩ := hC 1
  refine ⟨|C0| + |C1| + 1, by positivity, fun ε hε μ hμ y => ?_⟩
  have hβ : 0 ≤ beta p := by unfold beta; positivity
  have hfb := (hreg ε hε μ hμ).1
  rcases le_total 0 y with hy | hy
  · have h := ((hC0 ε hε μ hμ y).1 hy).2
    rw [zero_add, iteratedDeriv_one] at h
    have : jb y ^ (-beta p + ((0 : ℕ) : ℝ) / p) ≤ 1 := by
      simp only [Nat.cast_zero, zero_div, add_zero]
      exact c01_aux_jb_rpow_neg_le_one y _ hβ
    have hX : 0 ≤ jb y ^ (-beta p + ((0 : ℕ) : ℝ) / p) := Real.rpow_nonneg (by
      linarith [c01_aux_one_le_jb y]) _
    calc |deriv (approximate_solution_family p R ε μ) y| ≤ C0 * jb y ^ (-beta p + ((0 : ℕ) : ℝ) / p) := h
      _ ≤ |C0| * jb y ^ (-beta p + ((0 : ℕ) : ℝ) / p) := mul_le_mul_of_nonneg_right (le_abs_self _) hX
      _ ≤ |C0| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ |C0| + |C1| + 1 := by linarith [abs_nonneg C1]
  · have h := (hC1 ε hε μ hμ y).2 hy
    rw [iteratedDeriv_one] at h
    have hd : deriv (fun y' => approximate_solution_family p R ε μ y' + y') y =
        deriv (approximate_solution_family p R ε μ) y + 1 := by
      have := ((hfb.differentiable (by simp)) y).hasDerivAt.add (hasDerivAt_id' y)
      exact this.deriv
    rw [hd] at h
    have : jb y ^ (-p - ((1 : ℕ) : ℝ)) ≤ 1 := by
      rw [show -p - ((1 : ℕ) : ℝ) = -(p + 1) by push_cast; ring]
      exact c01_aux_jb_rpow_neg_le_one y _ (by linarith)
    have hX : 0 ≤ jb y ^ (-p - ((1 : ℕ) : ℝ)) := Real.rpow_nonneg (by
      linarith [c01_aux_one_le_jb y]) _
    have h2 : |deriv (approximate_solution_family p R ε μ) y + 1| ≤ |C1| :=
      h.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) hX).trans
        (by have := mul_le_mul_of_nonneg_left this (abs_nonneg C1); linarith))
    have := abs_sub_abs_le_abs_sub (deriv (approximate_solution_family p R ε μ) y) (-1)
    rw [sub_neg_eq_add] at this
    have h1 : |(-1 : ℝ)| = 1 := by norm_num
    linarith [abs_nonneg C0]

/-- The substance of lem:c01_profile_from_correction: for every correction data, `f̄ + r` lies in
`𝒜`, solves `ℰ_ε = 0`, has `|f''| ≤ C⟨y⟩^{1/p}` a.e. and the boundary behaviour. -/
theorem c01_aux_profile_props (P : parameters) (R δ ε₁ C₀ : ℝ)
    (hgood : c01_approx_family_good P.p R δ ε₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ (μ : ℂ) (r : ℝ → ℝ),
        c01_correction_data P R δ C₀ ε μ r →
        let f := approximate_solution_family P.p R ε μ + r
        f ∈ c01_admissible_class ∧ (∀ y, residual P.p ε f y = 0) ∧
        (∀ᵐ y, |deriv (deriv f) y| ≤ C * jb y ^ (1 / P.p)) ∧
        Tendsto (deriv f) atBot (𝓝 (-1)) ∧ Tendsto f atTop (𝓝 0) ∧
        profile_equation P.p ε f := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hβ0 : 0 < beta P.p := by unfold beta; positivity
  have hinvp : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hγ := P.hγ₁
  have hγ12 := P.hγ₁₂
  obtain ⟨Mb, hMb0, hMb⟩ := c01_aux_good_deriv_bound P.p R δ ε₁ hp0 hgood
  obtain ⟨-, -, hreg, hC⟩ := id hgood
  obtain ⟨C1, hC1⟩ := hC 1
  obtain ⟨C2, hC2⟩ := hC 2
  refine ⟨|C1| + |C2| + |C₀| * ε₁ + 1, by
    have : 0 ≤ ε₁ := hgood.2.1.le
    positivity, fun ε hε hε1 μ r hdata => ?_⟩
  intro f
  have hεI : ε ∈ Icc 0 ε₁ := ⟨hε.le, hε1.le⟩
  have hfb : ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family P.p R ε μ) :=
    (hreg ε hεI μ hdata.1).1
  have hlim0 := (hreg ε hεI μ hdata.1).2.2
  have hC1 := hC1 ε hεI μ hdata.1
  have hC2 := hC2 ε hεI μ hdata.1
  have hMb := hMb ε hεI μ hdata.1
  set fb := approximate_solution_family P.p R ε μ with hfbdef
  have hr := hdata.2.1
  set ρ := xNorm P.p P.γ₂ r with hρdef
  have hρ0 : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hρ : ρ ≤ |C₀| * ε₁ := by
    have h := hdata.2.2.2
    have h1 : ρ ≤ C₀ * ε := by linarith [norm_nonneg (μ - mu_star P.p)]
    calc ρ ≤ C₀ * ε := h1
      _ ≤ |C₀| * ε := mul_le_mul_of_nonneg_right (le_abs_self _) hε.le
      _ ≤ |C₀| * ε₁ := mul_le_mul_of_nonneg_left hε1.le (abs_nonneg _)
  obtain ⟨hr0, hr1p, hr1n, hr2p, hr2n⟩ := c01_aux_X_pointwise P.p P.γ₂ r hr
  have hJ1 : ∀ y, 1 ≤ jb y := c01_aux_one_le_jb
  have hX : ∀ y (a : ℝ), 0 ≤ jb y ^ a := fun y a => Real.rpow_nonneg (by linarith [hJ1 y]) a
  have hJmono : ∀ y (a b : ℝ), a ≤ b → jb y ^ a ≤ jb y ^ b := fun y a b h =>
    Real.rpow_le_rpow_of_exponent_le (hJ1 y) h
  -- pointwise bounds on `r` and `r'`
  have hrb : ∀ y, |r y| ≤ ρ * jb y ^ (-P.γ₂) := fun y =>
    c01_aux_wb (jb y) P.γ₂ 0 _ _ ρ (hJ1 y) hρ0 (by linarith) (by rw [Real.rpow_zero, one_mul]; exact hr0 y)
  have hr1 : ∀ y, |deriv r y| ≤ ρ * jb y ^ (-P.γ₂ + 1 / P.p) := by
    intro y
    rcases le_total 0 y with hy | hy
    · exact c01_aux_wb (jb y) P.γ₂ (-1 / P.p) _ _ ρ (hJ1 y) hρ0
        (by linarith [show -P.γ₂ - (-1 / P.p) = -P.γ₂ + 1 / P.p by ring]) (hr1p y hy)
    · exact c01_aux_wb (jb y) P.γ₂ 1 _ _ ρ (hJ1 y) hρ0 (by linarith) (hr1n y hy)
  have hr1' : ∀ y, y ≤ 0 → |deriv r y| ≤ ρ * jb y ^ (-(P.γ₂ + 1)) := fun y hy =>
    c01_aux_wb (jb y) P.γ₂ 1 _ _ ρ (hJ1 y) hρ0 (by linarith) (hr1n y hy)
  have hr1b : ∀ y, |deriv r y| ≤ ρ := fun y =>
    (hr1 y).trans (by
      have := c01_aux_jb_rpow_neg_le_one y (P.γ₂ - 1 / P.p) (by linarith)
      rw [show -(P.γ₂ - 1 / P.p) = -P.γ₂ + 1 / P.p by ring] at this
      exact mul_le_of_le_one_right hρ0 this)
  -- differentiability facts
  have hfbd : Differentiable ℝ fb := hfb.differentiable (by simp)
  have hrd : Differentiable ℝ r := hr.1.1.differentiable one_ne_zero
  have hdf : deriv f = fun y => deriv fb y + deriv r y := by
    funext y; exact ((hfbd y).hasDerivAt.add (hrd y).hasDerivAt).deriv
  have hfb1 : ContDiff ℝ 1 (deriv fb) := by
    have h2 : ContDiff ℝ (1 + 1) fb := hfb.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (contDiff_succ_iff_deriv.mp h2).2.2
  -- membership in `𝒜`
  have hfA : f ∈ c01_admissible_class := by
    refine ⟨(hfb.of_le (WithTop.coe_le_coe.mpr le_top)).add hr.1.1, ⟨Mb + ρ, fun y => ?_⟩, ?_⟩
    · rw [hdf]
      exact (abs_add_le _ _).trans (add_le_add (hMb y) (hr1b y))
    · rw [hdf]
      exact hfb1.locallyLipschitz.add hr.1.2
  -- the equation
  have hres : ∀ y, residual P.p ε f y = 0 := by
    intro y
    have h := hdata.2.2.1 y
    unfold N_eps at h
    have : residual P.p ε (fb + r) y = 0 := by linarith
    exact this
  -- second derivative bound
  have hf2 : ∀ y, |deriv (deriv f) y| ≤ |deriv (deriv fb) y| + |deriv (deriv r) y| := by
    intro y
    by_cases hdr : DifferentiableAt ℝ (deriv r) y
    · rw [hdf]
      have : HasDerivAt (fun y => deriv fb y + deriv r y)
          (deriv (deriv fb) y + deriv (deriv r) y) y :=
        (hfb1.differentiable one_ne_zero y).hasDerivAt.add hdr.hasDerivAt
      rw [this.deriv]; exact abs_add_le _ _
    · have hnd : ¬ DifferentiableAt ℝ (deriv f) y := by
        intro hd
        apply hdr
        have : deriv r = fun y => deriv f y - deriv fb y := by rw [hdf]; funext y; ring
        rw [this]; exact hd.sub (hfb1.differentiable one_ne_zero y)
      rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]; positivity
  have hfb2 : ∀ y, |deriv (deriv fb) y| ≤ (|C1| + |C2|) * jb y ^ (1 / P.p) := by
    intro y
    have e2 : iteratedDeriv 2 fb = deriv (deriv fb) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    rcases le_total 0 y with hy | hy
    · have h := ((hC1 y).1 hy).2
      rw [show (1 : ℕ) + 1 = 2 from rfl, e2] at h
      refine h.trans ?_
      calc C1 * jb y ^ (-beta P.p + ((1 : ℕ) : ℝ) / P.p) ≤ |C1| * jb y ^ (1 / P.p) := by
            apply mul_le_mul (le_abs_self _) (hJmono y _ _ (by push_cast; linarith)) (hX _ _)
              (abs_nonneg _)
        _ ≤ (|C1| + |C2|) * jb y ^ (1 / P.p) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C2]) (hX _ _)
    · have h := (hC2 y).2 hy
      have hid : iteratedDeriv 2 (fun y' => fb y' + y') y = iteratedDeriv 2 fb y := by
        rw [iteratedDeriv_fun_add ((hfb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
          (show ContDiffAt ℝ (2 : ℕ) (fun y : ℝ => y) y from contDiff_id.contDiffAt),
          iteratedDeriv_fun_id]
        simp
      rw [hid, e2] at h
      refine h.trans ?_
      calc C2 * jb y ^ (-P.p - ((2 : ℕ) : ℝ)) ≤ |C2| * jb y ^ (1 / P.p) := by
            apply mul_le_mul (le_abs_self _) (hJmono y _ _ (by push_cast; linarith)) (hX _ _)
              (abs_nonneg _)
        _ ≤ (|C1| + |C2|) * jb y ^ (1 / P.p) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) (hX _ _)
  have hr2 : ∀ᵐ y, |deriv (deriv r) y| ≤ ρ * jb y ^ (1 / P.p) := by
    have hP' := (ae_restrict_iff' measurableSet_Ici).mp hr2p
    have hN' := (ae_restrict_iff' measurableSet_Iic).mp hr2n
    filter_upwards [hP', hN'] with y h1 h2
    rcases le_total 0 y with hy | hy
    · exact c01_aux_wb (jb y) P.γ₂ (-2 / P.p) _ _ ρ (hJ1 y) hρ0
        (by linarith [show -P.γ₂ - (-2 / P.p) = -P.γ₂ + 2 * (1 / P.p) by ring]) (h1 hy)
    · exact c01_aux_wb (jb y) P.γ₂ 2 _ _ ρ (hJ1 y) hρ0 (by linarith) (h2 hy)
  have hae : ∀ᵐ y, |deriv (deriv f) y| ≤ (|C1| + |C2| + |C₀| * ε₁ + 1) * jb y ^ (1 / P.p) := by
    filter_upwards [hr2] with y hy
    calc |deriv (deriv f) y| ≤ |deriv (deriv fb) y| + |deriv (deriv r) y| := hf2 y
      _ ≤ (|C1| + |C2|) * jb y ^ (1 / P.p) + ρ * jb y ^ (1 / P.p) := add_le_add (hfb2 y) hy
      _ = (|C1| + |C2| + ρ) * jb y ^ (1 / P.p) := by ring
      _ ≤ (|C1| + |C2| + |C₀| * ε₁ + 1) * jb y ^ (1 / P.p) :=
          mul_le_mul_of_nonneg_right (by linarith) (hX _ _)
  -- boundary behaviour
  have hlimd : Tendsto (deriv f) atBot (𝓝 (-1)) := by
    rw [hdf]
    have hfbl : Tendsto (deriv fb) atBot (𝓝 (-1)) := by
      refine c01_aux_squeeze _ (fun y => |C1| * jb y ^ (-(P.p + 1))) _ ?_ ?_
      · simpa using ((c01_aux_jb_tendsto (P.p + 1) (by linarith)).2.const_mul |C1|)
      · filter_upwards [eventually_le_atBot 0] with y hy
        have h := (hC1 y).2 hy
        rw [iteratedDeriv_one] at h
        have hd : deriv (fun y' => fb y' + y') y = deriv fb y + 1 :=
          ((hfbd y).hasDerivAt.add (hasDerivAt_id' y)).deriv
        rw [hd] at h
        rw [sub_neg_eq_add]
        refine h.trans ?_
        rw [show -P.p - ((1 : ℕ) : ℝ) = -(P.p + 1) by push_cast; ring]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (hX _ _)
    have hrl : Tendsto (deriv r) atBot (𝓝 0) := by
      refine c01_aux_squeeze _ (fun y => ρ * jb y ^ (-(P.γ₂ + 1))) _ ?_ ?_
      · simpa using ((c01_aux_jb_tendsto (P.γ₂ + 1) (by linarith)).2.const_mul ρ)
      · filter_upwards [eventually_le_atBot 0] with y hy
        rw [sub_zero]; exact hr1' y hy
    simpa using hfbl.add hrl
  have hlimf : Tendsto f atTop (𝓝 0) := by
    have hrl : Tendsto r atTop (𝓝 0) := by
      refine c01_aux_squeeze _ (fun y => ρ * jb y ^ (-P.γ₂)) _ ?_ ?_
      · simpa using ((c01_aux_jb_tendsto P.γ₂ (by linarith)).1.const_mul ρ)
      · exact Eventually.of_forall fun y => by rw [sub_zero]; exact hrb y
    have h := hlim0.add hrl
    rw [add_zero] at h
    exact h
  refine ⟨hfA, hres, hae, hlimd, hlimf, ?_⟩
  unfold profile_equation
  exact ⟨hfA, hres, hlimd, hlimf⟩

/-- Blueprint: lem:c01_profile_minus_corner.  If `|f(y)+y| ≤ C⟨y⟩^{-p}` for `y ≤ 0` and
`|f(y)| ≤ C⟨y⟩^{-p}` for `y ≥ 0` then `sup |f - W| ≤ C`. -/
theorem c01_profile_minus_corner (p C : ℝ) (hp : 0 < p) (hC : 0 < C) (f : ℝ → ℝ)
    (hneg : ∀ y : ℝ, y ≤ 0 → |f y + y| ≤ C * jb y ^ (-p))
    (hpos : ∀ y : ℝ, 0 ≤ y → |f y| ≤ C * jb y ^ (-p)) :
    ∀ y : ℝ, |f y - corner y| ≤ C := by
  intro y
  have hj := c01_aux_jb_rpow_neg_le_one y p hp.le
  rcases le_total y 0 with hy | hy
  · have : corner y = -y := by unfold corner; exact max_eq_left (by linarith)
    rw [this, sub_neg_eq_add]
    exact (hneg y hy).trans (mul_le_of_le_one_right hC.le hj)
  · have : corner y = 0 := by unfold corner; exact max_eq_right (by linarith)
    rw [this, sub_zero]
    exact (hpos y hy).trans (mul_le_of_le_one_right hC.le hj)

/-- `F_{ε,T,f}(x,t) - √ε W(x) = √ε L (f(x/L) - W(x/L))`, by homogeneity of the corner. -/
theorem c01_aux_ansatz_sub_corner (p ε T : ℝ) (f : ℝ → ℝ) (x t : ℝ)
    (hL : 0 < self_similar_ansatz_L p T t) :
    self_similar_ansatz p ε T f x t - Real.sqrt ε * corner x =
      Real.sqrt ε * self_similar_ansatz_L p T t *
        (f (x / self_similar_ansatz_L p T t) - corner (x / self_similar_ansatz_L p T t)) := by
  set L := self_similar_ansatz_L p T t
  have hW : corner x = L * corner (x / L) := by
    unfold corner
    rw [mul_max_of_nonneg _ _ hL.le, mul_zero]
    congr 1; field_simp
  unfold self_similar_ansatz
  rw [hW]; ring

/-- `L_T(t) = α^{1/α} (T-t)^{1/α}`. -/
theorem c01_aux_L_eq (p T t : ℝ) (hp : 0 < p) (ht : t < T) :
    self_similar_ansatz_L p T t = (p + 1) ^ (1 / (p + 1)) * (T - t) ^ (1 / (p + 1)) := by
  unfold self_similar_ansatz_L
  exact Real.mul_rpow (by linarith) (by linarith)

/-- Blueprint: lem:c01_corner_convergence.  If `M = sup |f - W| < ∞` then for `t < T`,
`sup_x |F_{ε,T,f}(x,t) - √ε x₋| = √ε α^{1/α} M (T-t)^{1/α}`; in particular under the bounds of
thm:main (1) the corner bound holds with constant `α^{1/α} C ≤ 2C`, and
`F(·,t) → √ε x₋` uniformly as `t ↑ T`. -/
theorem c01_corner_convergence (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε T : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) :
    (BddAbove (range fun y => |f y - corner y|) →
      (∀ t : ℝ, t < T →
        BddAbove (range fun x => |self_similar_ansatz p ε T f x t - Real.sqrt ε * corner x|) ∧
        (⨆ x, |self_similar_ansatz p ε T f x t - Real.sqrt ε * corner x|) =
          Real.sqrt ε * (p + 1) ^ (1 / (p + 1)) * (⨆ y, |f y - corner y|) *
            (T - t) ^ (1 / (p + 1))) ∧
      TendstoUniformly (fun t x => self_similar_ansatz p ε T f x t)
        (fun x => Real.sqrt ε * corner x) (𝓝[<] T)) ∧
    (∀ C : ℝ, 0 < C → (∀ y : ℝ, y ≤ 0 → |f y + y| ≤ C * jb y ^ (-p)) →
      (∀ y : ℝ, 0 ≤ y → |f y| ≤ C * jb y ^ (-p)) →
      ∀ t : ℝ, t < T → ∀ x : ℝ,
        |self_similar_ansatz p ε T f x t - Real.sqrt ε * corner x| ≤
          (p + 1) ^ (1 / (p + 1)) * C * Real.sqrt ε * (T - t) ^ (1 / (p + 1)) ∧
        (p + 1) ^ (1 / (p + 1)) * C ≤ 2 * C) := by
  have hLpos : ∀ t, t < T → 0 < self_similar_ansatz_L p T t := (c01_L_properties p hp hp1 T).2.1
  have hseq : ∀ t, t < T → ∀ x, |self_similar_ansatz p ε T f x t - Real.sqrt ε * corner x| =
      Real.sqrt ε * self_similar_ansatz_L p T t *
        |f (x / self_similar_ansatz_L p T t) - corner (x / self_similar_ansatz_L p T t)| := by
    intro t ht x
    rw [c01_aux_ansatz_sub_corner p ε T f x t (hLpos t ht), abs_mul,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg ε) (hLpos t ht).le)]
  refine ⟨fun hb => ⟨fun t ht => ?_, ?_⟩, fun C hC hneg hpos t ht x => ?_⟩
  · set L := self_similar_ansatz_L p T t
    have hL := hLpos t ht
    have hsurj : Function.Surjective (fun x : ℝ => x / L) := fun y => ⟨y * L, mul_div_cancel_right₀ y hL.ne'⟩
    obtain ⟨B, hB⟩ := hb
    refine ⟨?_, ?_⟩
    · refine ⟨Real.sqrt ε * L * B, ?_⟩
      rintro _ ⟨x, rfl⟩
      simp only
      rw [hseq t ht x]
      exact mul_le_mul_of_nonneg_left (hB ⟨x / L, rfl⟩) (by positivity)
    · simp_rw [hseq t ht]
      rw [← Real.mul_iSup_of_nonneg (by positivity),
        hsurj.iSup_comp (fun y => |f y - corner y|), c01_aux_L_eq p T t hp ht]
      ring
  · obtain ⟨B, hB⟩ := hb
    have hB' : ∀ y, |f y - corner y| ≤ |B| := fun y => (hB ⟨y, rfl⟩).trans (le_abs_self B)
    have hLt := (c01_L_properties p hp hp1 T).2.2.1
    rw [Metric.tendstoUniformly_iff]
    intro e he
    have hK : 0 < Real.sqrt ε * (|B| + 1) := by
      have := Real.sqrt_pos.mpr hε; positivity
    have h1 : ∀ᶠ t in 𝓝[<] T, self_similar_ansatz_L p T t < e / (Real.sqrt ε * (|B| + 1)) :=
      hLt.eventually (gt_mem_nhds (by positivity))
    filter_upwards [h1, self_mem_nhdsWithin] with t h1 ht x
    rw [Real.dist_eq, abs_sub_comm, hseq t ht x]
    have hL := hLpos t ht
    calc Real.sqrt ε * self_similar_ansatz_L p T t *
          |f (x / self_similar_ansatz_L p T t) - corner (x / self_similar_ansatz_L p T t)|
        ≤ Real.sqrt ε * self_similar_ansatz_L p T t * (|B| + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hB' (x / self_similar_ansatz_L p T t)]
      _ = self_similar_ansatz_L p T t * (Real.sqrt ε * (|B| + 1)) := by ring
      _ < e / (Real.sqrt ε * (|B| + 1)) * (Real.sqrt ε * (|B| + 1)) :=
          mul_lt_mul_of_pos_right h1 hK
      _ = e := by field_simp
  · have hL := hLpos t ht
    have hc := c01_profile_minus_corner p C hp hC f hneg hpos (x / self_similar_ansatz_L p T t)
    have h2 : (p + 1) ^ (1 / (p + 1)) ≤ (2 : ℝ) := by
      calc (p + 1) ^ (1 / (p + 1)) ≤ (p + 1) ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            rw [div_le_one (by linarith)]; linarith
        _ ≤ 2 := by rw [Real.rpow_one]; linarith
    refine ⟨?_, by nlinarith⟩
    rw [hseq t ht x]
    calc Real.sqrt ε * self_similar_ansatz_L p T t *
          |f (x / self_similar_ansatz_L p T t) - corner (x / self_similar_ansatz_L p T t)|
        ≤ Real.sqrt ε * self_similar_ansatz_L p T t * C :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = (p + 1) ^ (1 / (p + 1)) * C * Real.sqrt ε * (T - t) ^ (1 / (p + 1)) := by
          rw [c01_aux_L_eq p T t hp ht]; ring

/-- Blueprint: lem:c01_profile_not_affine.  If `f ∈ C²`, `f' → -1` at `-∞` and `f` is bounded on
`[0,∞)`, then `f''(y₀) ≠ 0` for some `y₀`. -/
theorem c01_profile_not_affine (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hlim : Tendsto (deriv f) atBot (𝓝 (-1))) (hbdd : ∃ B : ℝ, ∀ y : ℝ, 0 ≤ y → |f y| ≤ B) :
    ∃ y₀ : ℝ, iteratedDeriv 2 f y₀ ≠ 0 := by
  by_contra h
  push Not at h
  have h2 : ContDiff ℝ (1 + 1) f := hf
  rw [contDiff_succ_iff_deriv] at h2
  obtain ⟨hd, -, hd1⟩ := h2
  have hdd : ∀ y, deriv (deriv f) y = 0 := by
    intro y; have := h y
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  have hc : ∀ y, deriv f y = deriv f 0 := fun y =>
    is_const_of_deriv_eq_zero (hd1.differentiable one_ne_zero) hdd y 0
  have hlim' : Tendsto (deriv f) atBot (𝓝 (deriv f 0)) := by
    have : deriv f = fun _ => deriv f 0 := funext hc
    rw [this]; exact tendsto_const_nhds
  have hm1 : deriv f 0 = -1 := tendsto_nhds_unique hlim' hlim
  have hg : ∀ y, f y + y = f 0 + 0 := by
    intro y
    refine is_const_of_deriv_eq_zero (f := fun y => f y + y) (hd.add differentiable_id) ?_ y 0
    intro x
    have h : HasDerivAt (fun y => f y + y) (deriv f x + 1) x := (hd x).hasDerivAt.add (hasDerivAt_id x)
    rw [h.deriv, hc x, hm1]; norm_num
  obtain ⟨B, hB⟩ := hbdd
  have hy : (0:ℝ) ≤ |f 0| + |B| + 1 := by positivity
  have := hB _ hy
  have e : f (|f 0| + |B| + 1) = f 0 - (|f 0| + |B| + 1) := by linarith [hg (|f 0| + |B| + 1)]
  rw [e] at this
  have h3 := abs_le.mp this
  have h4 := le_abs_self (f 0)
  have h5 := le_abs_self B
  linarith [h3.1]

/-- Blueprint: lem:c01_curvature_blowup.  If `f ∈ C²` and `f''(y₀) ≠ 0`, with
`c = √ε α^{-1/α} |f''(y₀)|` and `t_δ = T - (δ/|y₀|)^α/α` (`y₀ ≠ 0`), `t_δ = T - 1` (`y₀ = 0`):
`sup_{|x|<δ} |∂ₓ²F_{ε,T,f}(x,t)| ≥ c (T-t)^{-1/α}` for `t_δ < t < T`; and if `|f'| ≤ M` the
curvature `κ = ∂ₓ²F/(1+(∂ₓF)²)^{3/2}` satisfies
`sup_{|x|<δ} |κ(x,t)| ≥ c (1+εM²)^{-3/2} (T-t)^{-1/α}`. -/
theorem c01_curvature_blowup (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (y₀ : ℝ) (hy₀ : iteratedDeriv 2 f y₀ ≠ 0) :
    let c := Real.sqrt ε * (p + 1) ^ (-1 / (p + 1)) * |iteratedDeriv 2 f y₀|
    0 < c ∧
    ∀ T δ : ℝ, 0 < δ →
      let tδ := if y₀ ≠ 0 then T - 1 / (p + 1) * (δ / |y₀|) ^ (p + 1) else T - 1
      (∀ t : ℝ, tδ < t → t < T →
        ENNReal.ofReal (c * (T - t) ^ (-1 / (p + 1))) ≤
          ⨆ x ∈ Ioo (-δ) δ,
            ENNReal.ofReal |iteratedDeriv 2 (fun x' => self_similar_ansatz p ε T f x' t) x|) ∧
      (∀ M : ℝ, (∀ y, |deriv f y| ≤ M) → ∀ t : ℝ, tδ < t → t < T →
        ENNReal.ofReal (c * (1 + ε * M ^ 2) ^ (-(3 : ℝ) / 2) * (T - t) ^ (-1 / (p + 1))) ≤
          ⨆ x ∈ Ioo (-δ) δ,
            ENNReal.ofReal |iteratedDeriv 2 (fun x' => self_similar_ansatz p ε T f x' t) x /
              (1 + deriv (fun x' => self_similar_ansatz p ε T f x' t) x ^ 2) ^ ((3 : ℝ) / 2)|) := by
  intro c
  have hLp := c01_L_properties p hp hp1
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hcpos : 0 < c := by
    have h1 : 0 < |iteratedDeriv 2 f y₀| := abs_pos.mpr hy₀
    have h2 : 0 < (p + 1) ^ (-1 / (p + 1)) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  refine ⟨hcpos, fun T δ hδ => ?_⟩
  intro tδ
  have AT := c01_ansatz_time_derivative p hp hp1 ε T hε f hf1
  have key : ∀ t, tδ < t → t < T →
      self_similar_ansatz_L p T t * y₀ ∈ Ioo (-δ) δ ∧
      |iteratedDeriv 2 (fun x' => self_similar_ansatz p ε T f x' t)
          (self_similar_ansatz_L p T t * y₀)| = c * (T - t) ^ (-1 / (p + 1)) ∧
      deriv (fun x' => self_similar_ansatz p ε T f x' t) (self_similar_ansatz_L p T t * y₀) =
          Real.sqrt ε * deriv f y₀ := by
    intro t htd ht
    have hL := (hLp T).2.1 t ht
    have hbase : 0 < (p + 1) * (T - t) := by
      have : 0 < T - t := by linarith
      positivity
    have hxy : self_similar_ansatz_L p T t * y₀ / self_similar_ansatz_L p T t = y₀ :=
      mul_div_cancel_left₀ y₀ hL.ne'
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_Ioo, ← abs_lt, abs_mul, abs_of_pos hL]
      by_cases hy0 : y₀ = 0
      · rw [hy0, abs_zero, mul_zero]; exact hδ
      · have hay : 0 < |y₀| := abs_pos.mpr hy0
        have htd' : tδ = T - 1 / (p + 1) * (δ / |y₀|) ^ (p + 1) := by
          show (if y₀ ≠ 0 then _ else _) = _
          rw [if_pos hy0]
        rw [htd'] at htd
        have h1 : (p + 1) * (T - t) < (δ / |y₀|) ^ (p + 1) := by
          have hp1' : 0 < p + 1 := by linarith
          have : T - t < 1 / (p + 1) * (δ / |y₀|) ^ (p + 1) := by linarith
          rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ hp1'] at this
          linarith
        have h2 : self_similar_ansatz_L p T t < δ / |y₀| := by
          unfold self_similar_ansatz_L
          calc ((p + 1) * (T - t)) ^ (1 / (p + 1)) < ((δ / |y₀|) ^ (p + 1)) ^ (1 / (p + 1)) :=
                Real.rpow_lt_rpow hbase.le h1 (div_pos one_pos (by linarith))
            _ = δ / |y₀| := by
                rw [one_div, Real.rpow_rpow_inv (by positivity) (by linarith)]
        rw [lt_div_iff₀ hay] at h2
        exact h2
    · have h := (AT.2.2 2 hf).2 2 le_rfl (self_similar_ansatz_L p T t * y₀) t ht
      rw [h, hxy]
      have e1 : self_similar_ansatz_L p T t ^ (1 - ((2 : ℕ) : ℝ)) =
          (p + 1) ^ (-1 / (p + 1)) * (T - t) ^ (-1 / (p + 1)) := by
        unfold self_similar_ansatz_L
        rw [← Real.rpow_mul hbase.le, Real.mul_rpow (by linarith) (by linarith)]
        congr 2 <;> push_cast <;> ring
      rw [e1, abs_mul, abs_mul, abs_of_pos hsε,
        abs_of_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _))]
      ring
    · have h := (AT.2.1 (self_similar_ansatz_L p T t * y₀) t ht).1
      rw [h, hxy]
  have htdT : tδ < T := by
    show (if y₀ ≠ 0 then _ else _) < T
    split_ifs with hy0
    · have : 0 < 1 / (p + 1) * (δ / |y₀|) ^ (p + 1) := by
        have : 0 < |y₀| := abs_pos.mpr hy0
        have : 0 < p + 1 := by linarith
        positivity
      linarith
    · linarith
  refine ⟨fun t htd ht => ?_, fun M hM t htd ht => ?_⟩
  · obtain ⟨hmem, hval, -⟩ := key t htd ht
    exact le_iSup₂_of_le (f := fun x _ => ENNReal.ofReal
      |iteratedDeriv 2 (fun x' => self_similar_ansatz p ε T f x' t) x|) _ hmem
      (le_of_eq (by rw [hval]))
  · obtain ⟨hmem, hval, hder⟩ := key t htd ht
    refine le_iSup₂_of_le (f := fun x _ => ENNReal.ofReal
      |iteratedDeriv 2 (fun x' => self_similar_ansatz p ε T f x' t) x /
        (1 + deriv (fun x' => self_similar_ansatz p ε T f x' t) x ^ 2) ^ ((3 : ℝ) / 2)|) _ hmem ?_
    apply ENNReal.ofReal_le_ofReal
    rw [hder]
    have hM0 : |deriv f y₀| ≤ M := hM y₀
    have hb1 : (1 + (Real.sqrt ε * deriv f y₀) ^ 2) ≤ 1 + ε * M ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hε.le]
      have : deriv f y₀ ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM0 2
      nlinarith
    have hpos1 : 0 < (1 + (Real.sqrt ε * deriv f y₀) ^ 2) ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hpos2 : 0 < (1 + ε * M ^ 2) := by positivity
    rw [abs_div, abs_of_pos hpos1, hval]
    rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hpos2.le]
    have hT : 0 ≤ c * (T - t) ^ (-1 / (p + 1)) := by
      have : 0 < T - t := by linarith
      have := Real.rpow_pos_of_pos this (-1 / (p + 1))
      positivity
    rw [show c * ((1 + ε * M ^ 2) ^ ((3 : ℝ) / 2))⁻¹ * (T - t) ^ (-1 / (p + 1)) =
      c * (T - t) ^ (-1 / (p + 1)) / (1 + ε * M ^ 2) ^ ((3 : ℝ) / 2) by ring]
    apply div_le_div_of_nonneg_left hT hpos1
    exact Real.rpow_le_rpow (by positivity) hb1 (by norm_num)

end GSQG
