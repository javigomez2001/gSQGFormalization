import GSQG.Definitions
import GSQG.Auxiliary.SpecialIntegrals
import GSQG.Sec1_Introduction.SelfSimilarReduction
import GSQG.Sec5_ApproximateSolution.OscillatoryIntegrals
import GSQG.AppendixAB.StationaryPhaseHomogeneous

/-!
# §5: the approximate solution (blueprint ch. 04): linear seed, family, residual decomposition, `ℰ₁`–`ℰ₄`

Statements and proofs of every node of `blueprint/src/chapters/04_approx_family.tex` that is
not a shared definition.  The shared objects are in `GSQG.Definitions.Family`.

Conventions for the standing choices of the chapter (def:approximate_solution_family):
* the standing hypotheses `3/4 < p < 1` are hypotheses `hp hp1`;
* `δ ∈ (0, |μ_*|/2]` is universally quantified; the thresholds `ε₀ ∈ (0,1]` and `R₀ ≥ 2` (which the
  blueprint fixes once and later chapters may decrease/enlarge) are *existentially* quantified right
  after `δ` in each statement (any statement remains true after decreasing `ε₀`/enlarging `R₀`, so
  the statements can be combined by taking `min`/`max`);
* "admissible" constants depend only on `p, δ, ε₀` and the derivative order, hence are placed
  before `∀ R ≥ R₀, ∀ ε ∈ [0,ε₀], ∀ μ ∈ B̄, ∀ y` (except in prop:approx_residual_positive, where
  the blueprint allows a dependence on `R`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology ComplexConjugate

noncomputable section

namespace GSQG

/-! ### Chapter-local definitions -/

/-- Chapter 04 (local).  `ℒ₀ g = |D|^p g' + g - y g'` for complex-valued `g`. -/
def c04_L0C (p : ℝ) (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  fracDC p (deriv g) y + g y - (y : ℂ) * deriv g y

/-- Chapter 04 (local, lem:c04_seed_decomposition (3)).
`b(ξ) = (1-χ₊(ξ)) (1 - e^{-iΦ₀(ξ)})/ξ²`. -/
def c04_I1_symbol (p ξ : ℝ) : ℂ :=
  ((1 - chiPlus ξ : ℝ) : ℂ) * (1 - Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) / ((ξ ^ 2 : ℝ) : ℂ)

/-- Chapter 04 (local, lem:c04_seed_decomposition (3)).
`𝓘₁(y) = π⁻¹ Re ∫₀^∞ e^{iyξ} b(ξ) dξ`. -/
def c04_I1 (p y : ℝ) : ℝ :=
  π⁻¹ * (∫ ξ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ).re

/-- Chapter 04 (local, lem:c04_seed_decomposition (3)).
`𝓘₂(y) = π⁻¹ Re ∫₀^∞ e^{iyξ} χ₊(ξ) ξ⁻² dξ`. -/
def c04_I2 (y : ℝ) : ℝ :=
  π⁻¹ * (∫ ξ in Ioi (0 : ℝ),
    Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)).re

/-- Chapter 04 (local, lem:c04_seed_decomposition (2)).
`m_low(ξ) = (1 - χ₊(|ξ|)) e^{-iΦ₀(ξ)}`. -/
def c04_m_low (p ξ : ℝ) : ℂ :=
  ((1 - chiPlus |ξ| : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))

/-- Chapter 04 (local, lem:c04_Z_difference).
`D_q = μ a_* [λ^{-q} e^{iΨ} - λ₀^{-q} e^{iΨ₀}]`. -/
def c04_Dq (p R ε : ℝ) (μ : ℂ) (q y : ℝ) : ℂ :=
  μ * astar p y *
    (((fam_lambda p ε μ y ^ (-q) : ℝ) : ℂ) * Complex.exp (Complex.I * (fam_Psi p R ε μ y : ℂ)) -
      ((lambda0 p y ^ (-q) : ℝ) : ℂ) * Complex.exp (Complex.I * (Psi0 p y : ℂ)))

/-- Chapter 04 (local, lem:c04_lambda_taylor).  `g(x) = (1+x)^p - 1 - px`. -/
def c04_taylor_g (p x : ℝ) : ℝ := (1 + x) ^ p - 1 - p * x

/-- Chapter 04 (local, lem:c04_frac_decay_near).  `χ♭ ∈ C_c^∞((-1/2,1/2);[0,1])` with
`χ♭ = 1` on `[-1/4,1/4]`. -/
def c04_IsFlatCutoff (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo (-1 / 2) (1 / 2) ∧
    (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ ∀ x ∈ Icc (-1 / 4 : ℝ) (1 / 4), χ x = 1

/-! ### Standing auxiliary facts -/

/-- If `f` is integrable on `(0,∞)` then `x ↦ f |x|` is integrable on `ℝ`. -/
theorem c04_aux_c01_integrable_comp_abs {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
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
def c04_aux_c01_psi (p Λ M t : ℝ) : ℝ :=
  if t ≤ 1 then Λ * t ^ (-p) else 2 * M * t ^ (-(p + 1))

/-- Integrability and integral of the radial dominating function. -/
theorem c04_aux_c01_psi_integral (p Λ M : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (c04_aux_c01_psi p Λ M) (Ioi 0) ∧
      ∫ t in Ioi 0, c04_aux_c01_psi p Λ M t = Λ / (1 - p) + 2 * M / p := by
  have hIoc : IntegrableOn (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -p) (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul Λ
  have hIoi : IntegrableOn (fun t : ℝ => 2 * M * t ^ (-(p + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have e1 : EqOn (c04_aux_c01_psi p Λ M) (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 1) := by
    intro t ht; simp [c04_aux_c01_psi, ht.2]
  have e2 : EqOn (c04_aux_c01_psi p Λ M) (fun t : ℝ => 2 * M * t ^ (-(p + 1))) (Ioi 1) := by
    intro t ht; simp [c04_aux_c01_psi, not_le.mpr (show (1:ℝ) < t from ht)]
  have i1 : IntegrableOn (c04_aux_c01_psi p Λ M) (Ioc 0 1) := hIoc.congr_fun e1.symm measurableSet_Ioc
  have i2 : IntegrableOn (c04_aux_c01_psi p Λ M) (Ioi 1) := hIoi.congr_fun e2.symm measurableSet_Ioi
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
theorem c04_aux_c01_point_bound (g : ℝ → ℝ) (M : ℝ) (hM : ∀ᵐ z, |g z| ≤ M) (y Λ : ℝ)
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

/-- (Copy of chapter 01's auxiliary lemma.) The singular integral kernel estimate behind lem:c01_frac_well_defined: integrability and the
bound `∫ |(g(y)-g(z))/|y-z|^α| dz ≤ 2Λ/(2-α) + 4M/(α-1)`. -/
theorem c04_aux_c01_frac_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ)
    (hgm : AEStronglyMeasurable g volume) (M : ℝ) (hM : ∀ᵐ z, |g z| ≤ M) (y Λ : ℝ)
    (hΛ : 0 ≤ Λ)
    (hLip : ∀ z ∈ Icc (y - 1) (y + 1), ∀ w ∈ Icc (y - 1) (y + 1), |g z - g w| ≤ Λ * |z - w|) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) ∧
      ∫ z, |(g y - g z) / |y - z| ^ (p + 1)| ≤
        2 * Λ / (2 - (p + 1)) + 4 * M / ((p + 1) - 1) := by
  obtain ⟨hgy, hM0⟩ := c04_aux_c01_point_bound g M hM y Λ hΛ hLip
  obtain ⟨hψi, hψ⟩ := c04_aux_c01_psi_integral p Λ M hp hp1
  set D : ℝ → ℝ := fun z => c04_aux_c01_psi p Λ M |y - z|
  have hDi : Integrable D :=
    (c04_aux_c01_integrable_comp_abs hψi).comp_sub_left y
  have hDint : ∫ z, D z = 2 * Λ / (2 - (p + 1)) + 4 * M / ((p + 1) - 1) := by
    simp only [D]
    rw [integral_sub_left_eq_self (fun z => c04_aux_c01_psi p Λ M |z|) volume y,
      integral_comp_abs (f := c04_aux_c01_psi p Λ M), hψ]
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
      simp only [sub_self, zero_div, abs_zero, D, c04_aux_c01_psi]
      simp only [zero_le_one, ite_true]
      rw [Real.zero_rpow (by linarith)]; simp
    have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hzy))
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    simp only [D, c04_aux_c01_psi]
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



/-- The radial dominating function at scale `R`. -/
def c04_aux_psiR (p Λ M R t : ℝ) : ℝ :=
  if t ≤ R then Λ * t ^ (-p) else 2 * M * t ^ (-(p + 1))

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_psiR_integral (p Λ M R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 0 < R) :
    IntegrableOn (c04_aux_psiR p Λ M R) (Ioi 0) ∧
      ∫ t in Ioi 0, c04_aux_psiR p Λ M R t = Λ * R ^ (1 - p) / (1 - p) + 2 * M * R ^ (-p) / p := by
  have hIoc : IntegrableOn (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (r := -p) (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le] at this
    exact this.const_mul Λ
  have hIoi : IntegrableOn (fun t : ℝ => 2 * M * t ^ (-(p + 1))) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hR).const_mul _
  have e1 : EqOn (c04_aux_psiR p Λ M R) (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 R) := by
    intro t ht; simp [c04_aux_psiR, ht.2]
  have e2 : EqOn (c04_aux_psiR p Λ M R) (fun t : ℝ => 2 * M * t ^ (-(p + 1))) (Ioi R) := by
    intro t ht; simp [c04_aux_psiR, not_le.mpr (show R < t from ht)]
  have i1 : IntegrableOn (c04_aux_psiR p Λ M R) (Ioc 0 R) := hIoc.congr_fun e1.symm measurableSet_Ioc
  have i2 : IntegrableOn (c04_aux_psiR p Λ M R) (Ioi R) := hIoi.congr_fun e2.symm measurableSet_Ioi
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

/-- Translated form of the `|D|^p` integral. -/
theorem c04_aux_fracDC_shift (p : ℝ) (φ : ℝ → ℂ) (y : ℝ) :
    fracDC p φ y = (calpha p : ℂ) * ∫ h, (φ y - φ (y - h)) / ((|h| ^ (p + 1) : ℝ) : ℂ) := by
  unfold fracDC
  congr 1
  rw [← integral_sub_left_eq_self (fun z => (φ y - φ z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) volume y]
  simp only [sub_sub_cancel]

/-- Measurability of the translated integrand. -/
theorem c04_aux_shift_meas (p : ℝ) (hp : 0 < p) (φ : ℝ → ℂ) (hφ : Continuous φ) (y : ℝ) :
    AEStronglyMeasurable (fun h => (φ y - φ (y - h)) / ((|h| ^ (p + 1) : ℝ) : ℂ)) volume := by
  have hK : Continuous (fun h : ℝ => |h| ^ (p + 1)) :=
    continuous_abs.rpow_const (fun _ => Or.inr (by linarith))
  exact ((continuous_const.sub (hφ.comp (continuous_const.sub continuous_id))).measurable.div
    (Complex.measurable_ofReal.comp hK.measurable)).aestronglyMeasurable

/-- Pointwise domination of the translated integrand near `y₀`. -/
theorem c04_aux_shift_bound (p : ℝ) (hp : 0 < p) (φ : ℝ → ℂ) (hφ : Differentiable ℝ φ) (y₀ Λ M : ℝ)
    (hΛ : ∀ w ∈ Icc (y₀ - 2) (y₀ + 2), ‖deriv φ w‖ ≤ Λ) (hM : ∀ w, ‖φ w‖ ≤ M) :
    ∀ y ∈ Metric.ball y₀ 1, ∀ h, ‖(φ y - φ (y - h)) / ((|h| ^ (p + 1) : ℝ) : ℂ)‖ ≤
      c04_aux_psiR p Λ M 1 |h| := by
  intro y hy h
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
  simp only [c04_aux_psiR]
  by_cases h0 : h = 0
  · subst h0; simp only [sub_zero, sub_self, zero_div, norm_zero, abs_zero, zero_le_one, ite_true]
    rw [Real.zero_rpow (by linarith)]; simp
  have hpos : 0 < |h| := abs_pos.mpr h0
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hpos _),
    div_le_iff₀ (rpow_pos_of_pos hpos _)]
  split_ifs with h1
  · have hs : Convex ℝ (Icc (y₀ - 2) (y₀ + 2)) := convex_Icc _ _
    have hyI : y ∈ Icc (y₀ - 2) (y₀ + 2) := ⟨by linarith, by linarith⟩
    have hyh : y - h ∈ Icc (y₀ - 2) (y₀ + 2) := by
      have := abs_le.mp h1; exact ⟨by linarith, by linarith⟩
    have := hs.norm_image_sub_le_of_norm_deriv_le (fun w _ => hφ w) hΛ hyh hyI
    rw [show y - (y - h) = h by ring, Real.norm_eq_abs] at this
    calc ‖φ y - φ (y - h)‖ ≤ Λ * |h| := this
      _ = Λ * |h| ^ (-p) * |h| ^ (p + 1) := by
          rw [mul_assoc, ← rpow_add hpos]; simp
  · calc ‖φ y - φ (y - h)‖ ≤ ‖φ y‖ + ‖φ (y - h)‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM y, hM (y - h)]
      _ = 2 * M * |h| ^ (-(p + 1)) * |h| ^ (p + 1) := by
          rw [mul_assoc, ← rpow_add hpos]; simp

/-- Blueprint: lem:c04_frac_derivative.  For `g ∈ C²(ℝ;ℂ)` with `g, g'` bounded,
`|D|^p g ∈ C¹` and `(|D|^p g)' = |D|^p (g')`. (`g''` locally bounded is automatic.) -/
theorem c04_frac_derivative (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (g : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hg0 : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M) (hg1 : ∃ M : ℝ, ∀ y, ‖deriv g y‖ ≤ M) :
    ContDiff ℝ 1 (fracDC p g) ∧ ∀ y, deriv (fracDC p g) y = fracDC p (deriv g) y := by
  have hp0 : 0 < p := by linarith
  obtain ⟨M0, hM0⟩ := hg0
  obtain ⟨M1, hM1⟩ := hg1
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hg' : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hg'd : Differentiable ℝ (deriv g) := hg'.differentiable (by simp)
  have hg''c : Continuous (deriv (deriv g)) := hg'.continuous_deriv le_rfl
  set K : ℝ → ℂ := fun h => ((|h| ^ (p + 1) : ℝ) : ℂ) with hKdef
  set F : ℝ → ℝ → ℂ := fun y h => (g y - g (y - h)) / K h with hFdef
  set F' : ℝ → ℝ → ℂ := fun y h => (deriv g y - deriv g (y - h)) / K h with hF'def
  have hψint : ∀ Λ M : ℝ, Integrable (fun h : ℝ => c04_aux_psiR p Λ M 1 |h|) := fun Λ M =>
    c04_aux_c01_integrable_comp_abs (c04_aux_psiR_integral p Λ M 1 hp0 hp1 one_pos).1
  -- local bound for `g''`
  have hloc : ∀ y₀ : ℝ, ∃ Λ, ∀ w ∈ Icc (y₀ - 2) (y₀ + 2), ‖deriv (deriv g) w‖ ≤ Λ := fun y₀ =>
    isCompact_Icc.exists_bound_of_continuousOn hg''c.continuousOn
  have hderiv : ∀ y₀, HasDerivAt (fracDC p g) (fracDC p (deriv g) y₀) y₀ := by
    intro y₀
    obtain ⟨Λ, hΛ⟩ := hloc y₀
    have hb := c04_aux_shift_bound p hp0 (deriv g) hg'd y₀ Λ M1 hΛ hM1
    have hb0 := c04_aux_shift_bound p hp0 g hgd y₀ M1 M0 (fun w _ => hM1 w) hM0
    have hint : Integrable (F y₀) :=
      Integrable.mono' (hψint M1 M0) (c04_aux_shift_meas p hp0 g hgd.continuous y₀)
        (Eventually.of_forall fun h => hb0 y₀ (Metric.mem_ball_self one_pos) h)
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
      (x₀ := y₀) (bound := fun h => c04_aux_psiR p Λ M1 1 |h|)
      (Metric.ball_mem_nhds y₀ one_pos)
      (Eventually.of_forall fun y => c04_aux_shift_meas p hp0 g hgd.continuous y) hint
      (c04_aux_shift_meas p hp0 (deriv g) hg'.continuous y₀)
      (Eventually.of_forall fun h y hy => hb y hy h) (hψint Λ M1)
      (Eventually.of_forall fun h y _ => by
        have := ((hgd y).hasDerivAt.sub ((hgd (y - h)).hasDerivAt.scomp y
          ((hasDerivAt_id' y).sub_const h))).div_const (K h)
        simpa using this)
    have e1 : fracDC p g = fun y => (calpha p : ℂ) * ∫ h, F y h := funext (c04_aux_fracDC_shift p g)
    rw [e1, c04_aux_fracDC_shift p (deriv g) y₀]
    exact this.2.const_mul _
  refine ⟨?_, fun y => (hderiv y).deriv⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun y => (hderiv y).differentiableAt, ?_⟩
  have e2 : deriv (fracDC p g) = fun y => (calpha p : ℂ) * ∫ h, F' y h := by
    funext y; rw [(hderiv y).deriv, c04_aux_fracDC_shift]
  rw [e2]
  refine continuous_const.mul (continuous_iff_continuousAt.mpr fun y₀ => ?_)
  obtain ⟨Λ, hΛ⟩ := hloc y₀
  have hb := c04_aux_shift_bound p hp0 (deriv g) hg'd y₀ Λ M1 hΛ hM1
  refine continuousAt_of_dominated (bound := fun h => c04_aux_psiR p Λ M1 1 |h|)
    (Eventually.of_forall fun y => c04_aux_shift_meas p hp0 (deriv g) hg'.continuous y) ?_
    (hψint Λ M1) (Eventually.of_forall fun h => ?_)
  · filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
    exact Eventually.of_forall fun h => hb y hy h
  · exact ((hg'.continuous.sub (hg'.continuous.comp (continuous_id.sub continuous_const))).div_const
      (K h)).continuousAt

open scoped FourierTransform

/-- `⟨y⟩^N ‖S y‖` is integrable for complex Schwartz `S`, `N ≥ 0`. -/
theorem c04_aux_wL0_jb_pow_mul (S : SchwartzMap ℝ ℂ) (N : ℝ) (hN : 0 ≤ N) :
    Integrable (fun y => jb y ^ N * ‖S y‖) := by
  set k := ⌈N⌉₊
  have hint : Integrable (fun y => 2 ^ k * (‖S y‖ + ‖y‖ ^ k * ‖S y‖)) :=
    ((S.integrable.norm).add (SchwartzMap.integrable_pow_mul volume S k)).const_mul _
  refine Integrable.mono' hint (by
    have : Continuous (fun y => jb y ^ N) := by
      unfold jb
      exact (Real.continuous_sqrt.comp (by fun_prop)).rpow_const (fun _ => Or.inr hN)
    exact (this.mul S.continuous.norm).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
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
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
  have := norm_nonneg (S y)
  calc jb y ^ N * ‖S y‖ ≤ (2 ^ k * (1 + |y| ^ k)) * ‖S y‖ := by gcongr; linarith
    _ = 2 ^ k * (‖S y‖ + |y| ^ k * ‖S y‖) := by ring

/-- A polynomially bounded measurable function times a Schwartz function is integrable. -/
theorem c04_aux_wL0_int_mul (S : SchwartzMap ℝ ℂ) (a : ℝ → ℂ) (ha : AEStronglyMeasurable a)
    (K N : ℝ) (hb : ∀ ξ, ‖a ξ‖ ≤ K * jb ξ ^ N) : Integrable (fun ξ => a ξ * S ξ) := by
  refine Integrable.mono' ((c04_aux_wL0_jb_pow_mul S (max N 0) (le_max_right _ _)).const_mul
    (max K 0)) (ha.mul S.continuous.aestronglyMeasurable) (Eventually.of_forall fun ξ => ?_)
  have h1 := c01_aux_one_le_jb ξ
  have h2 : jb ξ ^ N ≤ jb ξ ^ max N 0 := Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
  have h3 : 0 ≤ jb ξ ^ N := Real.rpow_nonneg (by linarith) _
  rw [norm_mul]
  calc ‖a ξ‖ * ‖S ξ‖ ≤ (max K 0 * jb ξ ^ max N 0) * ‖S ξ‖ := by
        gcongr
        calc ‖a ξ‖ ≤ K * jb ξ ^ N := hb ξ
          _ ≤ max K 0 * jb ξ ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
          _ ≤ max K 0 * jb ξ ^ max N 0 := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max K 0 * (jb ξ ^ max N 0 * ‖S ξ‖) := by ring

theorem c04_aux_wL0_norm_exp (x ξ : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))‖ = 1 :=
  c01_aux_norm_exp_I x ξ

/-- Fubini pairing: `∫ f · m̌ = (2π)⁻¹ ∫ m(ξ) ∫ f(y) e^{iyξ} dy dξ`. -/
theorem c04_aux_wL0_fubini (m f : ℝ → ℂ) (hm : Integrable m) (hf : Integrable f) :
    ∫ y, f y * invFourierT m y = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ, m ξ * ∫ y, f y * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
  unfold invFourierT
  have hF : Integrable (Function.uncurry fun (y ξ : ℝ) =>
      f y * (m ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))) (volume.prod volume) := by
    refine Integrable.mono' (hf.norm.mul_prod hm.norm) ?_ (Eventually.of_forall fun q => ?_)
    · exact (hf.aestronglyMeasurable.comp_fst).mul ((hm.aestronglyMeasurable.comp_snd).mul
        (Continuous.aestronglyMeasurable (by fun_prop)))
    · simp [Function.uncurry, norm_mul, c04_aux_wL0_norm_exp]
  have e1 : ∀ y, f y * (((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, m ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))
      = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, f y * (m ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := by
    intro y; rw [integral_const_mul]; ring
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap hF]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [← integral_const_mul]
  congr 1; funext y; ring

/-- `m̌` is continuous for integrable `m`. -/
theorem c04_aux_wL0_cont (h : ℝ → ℂ) (hh : Integrable h) : Continuous (invFourierT h) := by
  unfold invFourierT
  refine continuous_const.mul (continuous_of_dominated (bound := fun ξ => ‖h ξ‖) (fun y => ?_)
    (fun y => Eventually.of_forall fun ξ => ?_) hh.norm (Eventually.of_forall fun ξ => ?_))
  · exact hh.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · rw [norm_mul, c04_aux_wL0_norm_exp, mul_one]
  · exact continuous_const.mul (by fun_prop)

/-- Derivative of `ȟ` when `h, ξh ∈ L¹`. -/
theorem c04_aux_wL0_hasDeriv (h : ℝ → ℂ) (hh : Integrable h)
    (hh1 : Integrable (fun ξ : ℝ => (ξ : ℂ) * h ξ)) (y : ℝ) :
    HasDerivAt (invFourierT h) (invFourierT (fun ξ : ℝ => Complex.I * (ξ : ℂ) * h ξ) y) y := by
  unfold invFourierT
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (x ξ : ℝ) => h ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)))
    (F' := fun (x ξ : ℝ) => Complex.I * (ξ : ℂ) * h ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)))
    (x₀ := y) (bound := fun (ξ : ℝ) => ‖(ξ : ℂ) * h ξ‖) (Metric.ball_mem_nhds y one_pos)
    (Eventually.of_forall fun (x : ℝ) => hh.aestronglyMeasurable.mul
      (Continuous.aestronglyMeasurable (by fun_prop)))
    (hh.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun (ξ : ℝ) => (c04_aux_wL0_norm_exp y ξ).le))
    (((Continuous.aestronglyMeasurable (by fun_prop)).mul hh.aestronglyMeasurable).mul
      (Continuous.aestronglyMeasurable (by fun_prop)))
    (Eventually.of_forall fun (ξ : ℝ) (x : ℝ) _ => by
      rw [norm_mul, c04_aux_wL0_norm_exp, mul_one, norm_mul, norm_mul, Complex.norm_I, one_mul,
        norm_mul])
    hh1.norm
    (Eventually.of_forall fun (ξ : ℝ) (x : ℝ) _ => by
      have := ((((hasDerivAt_id (x : ℂ)).const_mul Complex.I).mul_const (ξ : ℂ)).cexp).comp_ofReal
      simp only [id, mul_one] at this
      convert this.const_mul (h ξ) using 1
      ring)
  exact this.2.const_mul _

/-- Fundamental lemma: a continuous `F` orthogonal to all real test functions vanishes. -/
theorem c04_aux_wL0_fl (F : ℝ → ℂ) (hF : Continuous F)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ x, φ x • F x = 0) :
    ∀ y, F y = 0 := by
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    hF.locallyIntegrable (fun g hg hgc => h g (hg.of_le (by exact_mod_cast le_top)) hgc)
  have : F = fun _ => 0 := (hF.ae_eq_iff_eq volume continuous_const).mp hae
  exact fun y => congr_fun this y




theorem c04_aux_wL0_inv (k : ℝ → ℂ) (hc : Continuous k) (hk : Integrable k)
    (hψ : Integrable (invFourierT k)) (ξ : ℝ) :
    ∫ y, invFourierT k y * Complex.exp (-(Complex.I * (y : ℂ) * (ξ : ℂ))) = k ξ := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  set k2 : ℝ → ℂ := fun w => k (2 * π * w) with hk2def
  have hrep : invFourierT k = 𝓕⁻ k2 := by
    funext y
    unfold invFourierT
    set H : ℝ → ℂ := fun w => k2 w * Complex.exp (Complex.I * (y : ℂ) * ((2 * π * w : ℝ) : ℂ))
    have hH : ∀ ξ : ℝ, k ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) = H (ξ / (2 * π)) := by
      intro ξ; simp only [H, k2]; congr 3 <;> [skip; congr 2] <;> field_simp
    simp_rw [hH]
    rw [Measure.integral_comp_div H (2 * π), abs_of_pos (by positivity), Complex.real_smul,
      ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast h2π), one_mul, Real.fourierInv_eq']
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [H, smul_eq_mul, RCLike.inner_apply]
    rw [mul_comm]
    congr 2
    simp
    ring
  have hc2 : Continuous k2 := hc.comp (continuous_const.mul continuous_id)
  have hk2 : Integrable k2 := hk.comp_mul_left' h2π
  have hF : 𝓕 k2 = fun w => invFourierT k (-w) := by
    funext w; rw [hrep, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hF' : Integrable (𝓕 k2) := by rw [hF]; exact hψ.comp_neg
  rw [Lib.integral_mul_exp_neg_I_eq_fourier, hrep, hc2.fourier_fourierInv_eq hk2 hF']
  simp only [k2]
  congr 1; field_simp

theorem c04_aux_wL0_phiS (φ : SchwartzMap ℝ ℝ) :
    ∃ S : SchwartzMap ℝ ℂ, ∀ ξ : ℝ,
      S ξ = ∫ y, ((φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hne : (-(2 * π)⁻¹ : ℝ) ≠ 0 := by
    rw [neg_ne_zero]; exact inv_ne_zero h2π
  obtain ⟨φc, hφc⟩ : ∃ φc : SchwartzMap ℝ ℂ, ∀ x, φc x = ((φ x : ℝ) : ℂ) :=
    ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ, fun x => by simp⟩
  obtain ⟨T, hT⟩ : ∃ T : SchwartzMap ℝ ℂ, ∀ w, T w = 𝓕 (⇑φc) w := ⟨𝓕 φc, fun w => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ ≃L[ℝ] ℝ, ∀ x, e x = x * (-(2 * π)⁻¹) :=
    ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hne), fun x => rfl⟩
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e T, fun ξ => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT, he]
  have := Lib.integral_mul_exp_neg_I_eq_fourier (⇑φc) (-ξ)
  simp_rw [hφc] at this
  have e1 : ∀ y : ℝ, ((φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
      ((φ y : ℝ) : ℂ) * Complex.exp (-(Complex.I * (y : ℂ) * ((-ξ : ℝ) : ℂ))) := by
    intro y; push_cast; ring_nf
  simp_rw [e1, this]
  rw [show ξ * -(2 * π)⁻¹ = -ξ / (2 * π) by ring]

theorem c04_aux_wL0_phi_deriv (φ : ℝ → ℝ) (hc : Continuous φ) (hi : Integrable φ)
    (hi1 : Integrable (fun y => y * φ y)) (ξ : ℝ) :
    HasDerivAt (fun ξ : ℝ => ∫ y, ((φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))
      (Complex.I * ∫ y, ((y * φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) ξ := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (x y : ℝ) => ((φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (x : ℂ)))
    (F' := fun (x y : ℝ) => Complex.I * (((y * φ y : ℝ) : ℂ) *
      Complex.exp (Complex.I * (y : ℂ) * (x : ℂ))))
    (x₀ := ξ) (bound := fun (y : ℝ) => ‖y * φ y‖) (Metric.ball_mem_nhds ξ one_pos)
    (Eventually.of_forall fun (x : ℝ) => Continuous.aestronglyMeasurable (by fun_prop))
    (hi.ofReal.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun (y : ℝ) => (c01_aux_norm_exp_I y ξ).le))
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun (y : ℝ) (x : ℝ) _ => by
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, c01_aux_norm_exp_I, mul_one,
        Complex.norm_real])
    hi1.norm
    (Eventually.of_forall fun (y : ℝ) (x : ℝ) _ => by
      have := ((((hasDerivAt_id (x : ℂ)).const_mul (Complex.I * (y : ℂ)))).cexp).comp_ofReal
      simp only [id, mul_one] at this
      convert this.const_mul ((φ y : ℝ) : ℂ) using 1
      push_cast; ring)
  rw [← integral_const_mul]
  exact this.2




/-- Real-part/imaginary-part data for the complex duality. -/
theorem c04_aux_wL0_part (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℂ) (L : ℂ →L[ℝ] ℝ)
    (hg : ContDiff ℝ 1 g)
    (M : ℝ) (hM : ∀ y, ‖g y‖ ≤ M) (K N : ℝ) (hd : ∀ y, ‖deriv g y‖ ≤ K * jb y ^ N)
    (hL : ∀ z, |L z| ≤ ‖z‖) :
    let u := fun y => L (g y)
    (∀ y, Integrable (fun z => (u y - u z) / |y - z| ^ (p + 1))) ∧
    Continuous (fracD p u) ∧
        ∀ φ : SchwartzMap ℝ ℝ,
          (∃ Cφ : ℝ, ∀ y, ‖fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y‖ ≤ Cφ * jb y ^ (-(p + 1))) ∧
          Integrable (fun y => fracD p u y * φ y) ∧
          Integrable (fun y => (u y : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y) ∧
          ∫ y, ((fracD p u y * φ y : ℝ) : ℂ) =
            ∫ y, (u y : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y := by
  intro u
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hu : ContDiff ℝ 1 u := L.contDiff.comp hg
  have hdu : ∀ y, deriv u y = L (deriv g y) := fun y =>
    (L.hasFDerivAt.comp_hasDerivAt y (hgd y).hasDerivAt).deriv
  have hM' : ∀ᵐ z, |u z| ≤ M := Eventually.of_forall fun z => (hL _).trans (hM z)
  have hd' : ∀ᵐ y, |deriv u y| ≤ max K 0 * jb y ^ max N 0 := by
    refine Eventually.of_forall fun y => ?_
    have h1 := c01_aux_one_le_jb y
    have h2 : jb y ^ N ≤ jb y ^ max N 0 := Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
    have h3 : 0 ≤ jb y ^ N := Real.rpow_nonneg (by linarith) _
    rw [hdu]
    calc |L (deriv g y)| ≤ K * jb y ^ N := (hL _).trans (hd y)
      _ ≤ max K 0 * jb y ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max K 0 * jb y ^ max N 0 := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  have hLL : LocallyLipschitz u := hu.locallyLipschitz
  obtain ⟨-, -, B, -, hB⟩ := c01_aux_duality_kernel_bound p hp hp1 u M (max K 0) (max N 0) hM'
    hLL (le_max_right _ _) (le_max_right _ _) hd'
  obtain ⟨hc, -, hφ⟩ := (c01_frac_duality p hp hp1).1 u M (max K 0) (max N 0) hM' hLL
    (le_max_right _ _) (le_max_right _ _) hd'
  exact ⟨fun y => (hB y).1, hc, hφ⟩

/-- `fracDC` of a complex function in terms of `fracD` of its real and imaginary parts. -/
theorem c04_aux_wL0_split (p : ℝ) (g : ℝ → ℂ) (y : ℝ)
    (hu : Integrable (fun z => ((g y).re - (g z).re) / |y - z| ^ (p + 1)))
    (hv : Integrable (fun z => ((g y).im - (g z).im) / |y - z| ^ (p + 1))) :
    fracDC p g y = ((fracD p (fun y => (g y).re) y : ℝ) : ℂ) +
      Complex.I * ((fracD p (fun y => (g y).im) y : ℝ) : ℂ) := by
  unfold fracDC fracD
  have e : ∀ z, (g y - g z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ) =
      ((((g y).re - (g z).re) / |y - z| ^ (p + 1) : ℝ) : ℂ) +
        Complex.I * ((((g y).im - (g z).im) / |y - z| ^ (p + 1) : ℝ) : ℂ) := by
    intro z
    apply Complex.ext <;> simp [Complex.div_ofReal_re, Complex.div_ofReal_im]
  simp_rw [e]
  have i1 : Integrable (fun z => ((((g y).re - (g z).re) / |y - z| ^ (p + 1) : ℝ) : ℂ)) :=
    hu.ofReal
  have i2 : Integrable (fun z => Complex.I *
      ((((g y).im - (g z).im) / |y - z| ^ (p + 1) : ℝ) : ℂ)) := hv.ofReal.const_mul _
  rw [integral_add i1 i2, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal]
  push_cast; ring

/-- Complex duality: `∫ φ |D|^p g = ∫ (|D|^p φ) g` and continuity of `|D|^p g`. -/
theorem c04_aux_wL0_dual (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (M : ℝ) (hM : ∀ y, ‖g y‖ ≤ M) (K N : ℝ) (hd : ∀ y, ‖deriv g y‖ ≤ K * jb y ^ N) :
    Continuous (fracDC p g) ∧ ∀ φ : SchwartzMap ℝ ℝ,
      (∃ Cφ : ℝ, ∀ y, ‖fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y‖ ≤ Cφ * jb y ^ (-(p + 1))) ∧
      Integrable (fun y => φ y • fracDC p g y) ∧
      ∫ y, φ y • fracDC p g y = ∫ y, fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
              (fun x => ((φ x : ℝ) : ℂ)) y * g y := by
  obtain ⟨hIu, hcu, hφu⟩ := c04_aux_wL0_part p hp hp1 g Complex.reCLM hg M hM K N hd
    (fun z => by simpa using Complex.abs_re_le_norm z)
  obtain ⟨hIv, hcv, hφv⟩ := c04_aux_wL0_part p hp hp1 g Complex.imCLM hg M hM K N hd
    (fun z => by simpa using Complex.abs_im_le_norm z)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hIu hcu hφu hIv hcv hφv
  have hsplit : fracDC p g = fun y => ((fracD p (fun y => (g y).re) y : ℝ) : ℂ) +
      Complex.I * ((fracD p (fun y => (g y).im) y : ℝ) : ℂ) :=
    funext fun y => c04_aux_wL0_split p g y (hIu y) (hIv y)
  refine ⟨?_, fun φ => ?_⟩
  · rw [hsplit]; fun_prop
  obtain ⟨hC, hi1u, hi2u, hidu⟩ := hφu φ
  obtain ⟨-, hi1v, hi2v, hidv⟩ := hφv φ
  have e : ∀ y, φ y • fracDC p g y = ((fracD p (fun y => (g y).re) y * φ y : ℝ) : ℂ) +
      Complex.I * ((fracD p (fun y => (g y).im) y * φ y : ℝ) : ℂ) := by
    intro y; rw [hsplit, Complex.real_smul]; push_cast; ring
  have e2 : ∀ y, fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
      (fun x => ((φ x : ℝ) : ℂ)) y * g y =
      ((g y).re : ℂ) * fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ))
        (fun x => ((φ x : ℝ) : ℂ)) y + Complex.I * (((g y).im : ℂ) *
        fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (fun x => ((φ x : ℝ) : ℂ)) y) := by
    intro y
    conv_lhs => rw [← Complex.re_add_im (g y)]
    ring
  have j1 : Integrable (fun y => ((fracD p (fun y => (g y).re) y * φ y : ℝ) : ℂ)) := hi1u.ofReal
  have j2 : Integrable (fun y => Complex.I * ((fracD p (fun y => (g y).im) y * φ y : ℝ) : ℂ)) :=
    hi1v.ofReal.const_mul _
  have j3 : Integrable (fun y => Complex.I * (((g y).im : ℂ) *
        fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (fun x => ((φ x : ℝ) : ℂ)) y)) :=
    hi2v.const_mul _
  refine ⟨hC, (j1.add j2).congr (Eventually.of_forall fun y => (e y).symm), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall e), integral_congr_ae (Eventually.of_forall e2),
    integral_add j1 j2, integral_add hi2u j3, integral_const_mul, integral_const_mul, hidu, hidv]


/-- `|ξ|^p ≤ ⟨ξ⟩` for `0 < p ≤ 1`. -/
theorem c04_aux_wL0_rpow_le_jb (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (ξ : ℝ) : |ξ| ^ p ≤ jb ξ := by
  have hj : |ξ| ≤ jb ξ := by
    unfold jb; rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h1 := c01_aux_one_le_jb ξ
  rcases le_total |ξ| 1 with h | h
  · exact (Real.rpow_le_one (abs_nonneg _) h hp.le).trans h1
  · calc |ξ| ^ p ≤ |ξ| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hp1
      _ = |ξ| := Real.rpow_one _
      _ ≤ jb ξ := hj

/-- General form of part (2): `(|D|^p - y) m̌ = (|ξ|^p m - i m')^∨`. -/
theorem c04_aux_wL0_P2 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℝ → ℂ) (hm1 : ContDiff ℝ 1 m)
    (hmi : Integrable m) (hmb : ∃ K N : ℝ, ∀ ξ, ‖m ξ‖ + ‖deriv m ξ‖ ≤ K * jb ξ ^ N)
    (hhi : Integrable (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * m ξ - Complex.I * deriv m ξ))
    (hg1 : ContDiff ℝ 1 (invFourierT m)) (hg0 : ∃ M : ℝ, ∀ y, ‖invFourierT m y‖ ≤ M)
    (hg2 : ∃ K N : ℝ, ∀ y, ‖deriv (invFourierT m) y‖ ≤ K * jb y ^ N) :
    ∀ y, fracDC p (invFourierT m) y - (y : ℂ) * invFourierT m y =
      invFourierT (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * m ξ - Complex.I * deriv m ξ) y := by
  obtain ⟨M, hM⟩ := hg0
  obtain ⟨K, N, hKN⟩ := hg2
  obtain ⟨Km, Nm, hKm⟩ := hmb
  have hm0 : ∀ ξ, ‖m ξ‖ ≤ Km * jb ξ ^ Nm := fun ξ =>
    le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hKm ξ)
  have hm1' : ∀ ξ, ‖deriv m ξ‖ ≤ Km * jb ξ ^ Nm := fun ξ =>
    le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hKm ξ)
  have hmc : Continuous m := hm1.continuous
  have hmd : Differentiable ℝ m := hm1.differentiable (by simp)
  have hm'c : Continuous (deriv m) := hm1.continuous_deriv le_rfl
  have hrp : Continuous (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr hp.le))
  set h : ℝ → ℂ := fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * m ξ - Complex.I * deriv m ξ with hhdef
  set g : ℝ → ℂ := invFourierT m with hgdef
  obtain ⟨hcont, hdual⟩ := c04_aux_wL0_dual p hp hp1 g hg1 M hM K N hKN
  have hgc : Continuous g := hg1.continuous
  have hhc : Continuous (invFourierT h) := c04_aux_wL0_cont h hhi
  suffices H : ∀ y, (fracDC p g y - (y : ℂ) * g y) - invFourierT h y = 0 from
    fun y => sub_eq_zero.mp (H y)
  refine c04_aux_wL0_fl _ ((hcont.sub ((Complex.continuous_ofReal).mul hgc)).sub hhc) ?_
  intro φ hφ hcs
  set φs : SchwartzMap ℝ ℝ := hcs.toSchwartzMap hφ with hφsdef
  have hφs : ∀ x, φs x = φ x := fun x => rfl
  obtain ⟨⟨Cφ, hCφ⟩, hI, hid⟩ := hdual φs
  simp only [hφs] at hCφ hI hid
  set ψ : ℝ → ℂ := fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (fun x => ((φ x : ℝ) : ℂ))
    with hψdef
  set k : ℝ → ℂ := fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT (fun x => ((φ x : ℝ) : ℂ)) ξ with hkdef
  have hψk : ψ = invFourierT k := rfl
  obtain ⟨hhatc, hhati, hhati1, -⟩ := c01_aux_hat φs
  simp only [hφs] at hhatc hhati hhati1
  have hkc : Continuous k := hrp.mul hhatc
  have hki : Integrable k := by
    refine Integrable.mono' (hhati.norm.add hhati1) hkc.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    simp only [hkdef, Pi.add_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) p)]
    have hn := norm_nonneg (fourierT (fun x => ((φ x : ℝ) : ℂ)) ξ)
    rcases le_total |ξ| 1 with h1 | h1
    · have := Real.rpow_le_one (abs_nonneg ξ) h1 hp.le
      nlinarith [abs_nonneg ξ]
    · have : |ξ| ^ p ≤ |ξ| := by
        calc |ξ| ^ p ≤ |ξ| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hp1.le
          _ = |ξ| := Real.rpow_one _
      nlinarith
  have hψc : Continuous ψ := by rw [hψk]; exact c04_aux_wL0_cont k hki
  have hψi : Integrable ψ := by
    refine Integrable.mono' ((c01_aux_integrable_jb_neg p hp).const_mul Cφ)
      hψc.aestronglyMeasurable (Eventually.of_forall hCφ)
  -- the Schwartz function `Φ(ξ) = ∫ φ(y) e^{iyξ} dy`
  obtain ⟨S, hS⟩ := c04_aux_wL0_phiS φs
  simp only [hφs] at hS
  have hφc : Continuous φ := hφ.continuous
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hcs
  have hyφi : Integrable (fun y => y * φ y) :=
    (continuous_id.mul hφc).integrable_of_hasCompactSupport hcs.mul_left
  set Φ1 : ℝ → ℂ := fun ξ => ∫ y, ((y * φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))
    with hΦ1def
  have hSd : ∀ ξ, HasDerivAt S (Complex.I * Φ1 ξ) ξ := by
    intro ξ
    have := c04_aux_wL0_phi_deriv φ hφc hφi hyφi ξ
    have e : (⇑S) = fun ξ : ℝ => ∫ y, ((φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) :=
      funext hS
    rw [e]; exact this
  have hΦ1 : ∀ ξ, Φ1 ξ = -Complex.I * deriv S ξ := by
    intro ξ; rw [(hSd ξ).deriv, ← mul_assoc, show -Complex.I * Complex.I = 1 by
      rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
  -- the Fourier side of `|D|^p φ`
  have hψhat : ∀ ξ : ℝ, ∫ y, ψ y * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
      ((|ξ| ^ p : ℝ) : ℂ) * S ξ := by
    intro ξ
    have := c04_aux_wL0_inv k hkc hki (hψk ▸ hψi) (-ξ)
    rw [← hψk] at this
    have e1 : ∀ y : ℝ, ψ y * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
        ψ y * Complex.exp (-(Complex.I * (y : ℂ) * ((-ξ : ℝ) : ℂ))) := by
      intro y; push_cast; ring_nf
    have e2 : fourierT (fun x => ((φ x : ℝ) : ℂ)) (-ξ) =
        ∫ y, ((φ y : ℝ) : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
      unfold fourierT
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      push_cast; ring_nf
    simp_rw [e1]
    rw [this, hS]
    show ((|-ξ| ^ p : ℝ) : ℂ) * fourierT (fun x => ((φ x : ℝ) : ℂ)) (-ξ) = _
    rw [abs_neg, e2]
  -- integrability on the Fourier side
  have hjb : ∀ ξ, ‖((|ξ| ^ p : ℝ) : ℂ) * m ξ‖ ≤ Km * jb ξ ^ (Nm + 1) := by
    intro ξ
    have h1 := c01_aux_one_le_jb ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
      (abs_nonneg ξ) p), Real.rpow_add (by linarith), Real.rpow_one]
    have := c04_aux_wL0_rpow_le_jb p hp hp1.le ξ
    have h0 : 0 ≤ Km * jb ξ ^ Nm := (norm_nonneg _).trans (hm0 ξ)
    calc |ξ| ^ p * ‖m ξ‖ ≤ jb ξ * (Km * jb ξ ^ Nm) :=
          mul_le_mul this (hm0 ξ) (norm_nonneg _) (by linarith)
      _ = Km * (jb ξ ^ Nm * jb ξ) := by ring
  have iA : Integrable (fun ξ => (((|ξ| ^ p : ℝ) : ℂ) * m ξ) * S ξ) :=
    c04_aux_wL0_int_mul S _ (hrp.mul hmc).aestronglyMeasurable _ _ hjb
  have iB : Integrable (fun ξ => deriv m ξ * S ξ) :=
    c04_aux_wL0_int_mul S _ hm'c.aestronglyMeasurable _ _ hm1'
  have iC : Integrable (fun ξ => m ξ * (SchwartzMap.derivCLM ℝ ℂ S) ξ) :=
    c04_aux_wL0_int_mul _ _ hmc.aestronglyMeasurable _ _ hm0
  have iD : Integrable (fun ξ => m ξ * S ξ) :=
    c04_aux_wL0_int_mul S _ hmc.aestronglyMeasurable _ _ hm0
  have hdS : ∀ ξ, (SchwartzMap.derivCLM ℝ ℂ S) ξ = deriv S ξ := fun ξ =>
    SchwartzMap.derivCLM_apply ℝ S ξ
  simp only [hdS] at iC
  have hIBP : ∫ ξ, m ξ * deriv S ξ = -∫ ξ, deriv m ξ * S ξ :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => (hmd x).hasDerivAt)
      (fun x _ => (hSd x).differentiableAt.hasDerivAt) iC iB iD
  -- the three pairings
  have P1 : ∫ y, φ y • fracDC p g y = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ, (((|ξ| ^ p : ℝ) : ℂ) * m ξ) * S ξ := by
    rw [hid, hgdef, c04_aux_wL0_fubini m ψ hmi hψi]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [hψhat]; ring
  have P2 : ∫ y, φ y • ((y : ℂ) * g y) = ((2 * π : ℝ) : ℂ)⁻¹ *
      (Complex.I * ∫ ξ, deriv m ξ * S ξ) := by
    have e : ∀ y, φ y • ((y : ℂ) * g y) = ((y * φ y : ℝ) : ℂ) * g y := by
      intro y; rw [Complex.real_smul]; push_cast; ring
    rw [integral_congr_ae (Eventually.of_forall e), hgdef]
    refine (c04_aux_wL0_fubini m (fun y => ((y * φ y : ℝ) : ℂ)) hmi hyφi.ofReal).trans ?_
    congr 1
    have e2 : ∀ ξ, m ξ * Φ1 ξ = -Complex.I * (m ξ * deriv S ξ) := by
      intro ξ; rw [hΦ1]; ring
    rw [integral_congr_ae (Eventually.of_forall e2), integral_const_mul, hIBP]
    ring
  have P3 : ∫ y, φ y • invFourierT h y = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ, h ξ * S ξ := by
    have e : ∀ y, φ y • invFourierT h y = ((φ y : ℝ) : ℂ) * invFourierT h y := fun y =>
      Complex.real_smul
    rw [integral_congr_ae (Eventually.of_forall e)]
    refine (c04_aux_wL0_fubini h (fun y => ((φ y : ℝ) : ℂ)) hhi hφi.ofReal).trans ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [hS]
  have P4 : ∫ ξ, h ξ * S ξ = (∫ ξ, (((|ξ| ^ p : ℝ) : ℂ) * m ξ) * S ξ) -
      Complex.I * ∫ ξ, deriv m ξ * S ξ := by
    have i2 : Integrable (fun ξ => Complex.I * (deriv m ξ * S ξ)) := iB.const_mul Complex.I
    calc ∫ ξ, h ξ * S ξ = ∫ ξ, ((((|ξ| ^ p : ℝ) : ℂ) * m ξ) * S ξ - Complex.I * (deriv m ξ * S ξ)) :=
          integral_congr_ae (Eventually.of_forall fun ξ => by simp only [hhdef]; ring)
      _ = (∫ ξ, (((|ξ| ^ p : ℝ) : ℂ) * m ξ) * S ξ) - ∫ ξ, Complex.I * (deriv m ξ * S ξ) :=
          integral_sub iA i2
      _ = _ := by rw [integral_const_mul]
  -- integrability on the physical side
  have j2 : Integrable (fun y => φ y • ((y : ℂ) * g y)) :=
    (hφc.smul ((Complex.continuous_ofReal).mul hgc)).integrable_of_hasCompactSupport
      hcs.smul_right
  have j3 : Integrable (fun y => φ y • invFourierT h y) :=
    (hφc.smul hhc).integrable_of_hasCompactSupport hcs.smul_right
  have e : ∀ y, φ y • ((fracDC p g y - (y : ℂ) * g y) - invFourierT h y) =
      φ y • fracDC p g y - φ y • ((y : ℂ) * g y) - φ y • invFourierT h y := by
    intro y; rw [smul_sub, smul_sub]
  have j12 : Integrable (fun y => φ y • fracDC p g y - φ y • ((y : ℂ) * g y)) := hI.sub j2
  rw [integral_congr_ae (Eventually.of_forall e), integral_sub j12 j3,
    integral_sub hI j2, P1, P2, P3, P4]
  ring


/-- Linearity of `invFourierT` used in part (1). -/
theorem c04_aux_wL0_lin (a b : ℝ → ℂ) (ha : Integrable a) (hb : Integrable b) (c : ℂ) (y : ℝ) :
    invFourierT (fun ξ => a ξ + c * b ξ) y = invFourierT a y + c * invFourierT b y := by
  unfold invFourierT
  have i1 : Integrable (fun ξ : ℝ => a ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) :=
    ha.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun (ξ : ℝ) => (c04_aux_wL0_norm_exp y ξ).le)
  have i2 : Integrable (fun ξ : ℝ => c * (b ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))) :=
    (hb.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun (ξ : ℝ) => (c04_aux_wL0_norm_exp y ξ).le)).const_mul c
  have e : ∀ ξ : ℝ, (a ξ + c * b ξ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
      a ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) +
        c * (b ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := fun ξ => by ring
  rw [integral_congr_ae (Eventually.of_forall e), integral_add i1 i2, integral_const_mul]
  ring

/-- `m = 0` near the origin forces `m' = 0` there. -/
theorem c04_aux_wL0_deriv_zero (m : ℝ → ℂ) (η : ℝ) (hη0 : ∀ ξ, |ξ| < η → m ξ = 0) (ξ : ℝ)
    (hξ : |ξ| < η) : deriv m ξ = 0 := by
  have hopen : IsOpen {x : ℝ | |x| < η} := isOpen_lt continuous_abs continuous_const
  have hev : m =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hξ) (fun x hx => hη0 x hx)
  rw [hev.deriv_eq]; simp

/-- Blueprint: lem:c04_weak_L0.  Weak Fourier computation of `ℒ₀` and of `|D|^p - y`:
(1) `ℒ₀ m̌ = ň` with `n = ξ m' + (2 + iξ|ξ|^p) m`; (2) `(|D|^p - y) m̌ = (|ξ|^p m - i m')^∨`. -/
theorem c04_weak_L0 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ m : ℝ → ℂ, ContDiff ℝ 1 m → Integrable m → (∃ η > (0 : ℝ), ∀ ξ, |ξ| < η → m ξ = 0) →
      (∃ K N : ℝ, ∀ ξ, ‖m ξ‖ + ‖deriv m ξ‖ ≤ K * jb ξ ^ N) →
      Integrable (fun ξ : ℝ => (ξ : ℂ) * deriv m ξ +
        (2 + Complex.I * ((ξ * |ξ| ^ p : ℝ) : ℂ)) * m ξ) →
      ContDiff ℝ 2 (invFourierT m) →
      (∃ M : ℝ, ∀ y, ‖invFourierT m y‖ ≤ M) →
      (∃ M : ℝ, ∀ y, ‖deriv (invFourierT m) y‖ ≤ M) →
      (∃ K N : ℝ, ∀ y, ‖iteratedDeriv 2 (invFourierT m) y‖ ≤ K * jb y ^ N) →
      ∀ y, c04_L0C p (invFourierT m) y =
        invFourierT (fun ξ : ℝ => (ξ : ℂ) * deriv m ξ +
          (2 + Complex.I * ((ξ * |ξ| ^ p : ℝ) : ℂ)) * m ξ) y) ∧
    (∀ m : ℝ → ℂ, ContDiff ℝ 1 m → HasCompactSupport m →
      ContDiff ℝ 1 (invFourierT m) →
      (∃ M : ℝ, ∀ y, ‖invFourierT m y‖ ≤ M) →
      (∃ K N : ℝ, ∀ y, ‖deriv (invFourierT m) y‖ ≤ K * jb y ^ N) →
      ∀ y, fracDC p (invFourierT m) y - (y : ℂ) * invFourierT m y =
        invFourierT (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * m ξ - Complex.I * deriv m ξ) y) := by
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_⟩
  · intro m hm1 hmi ⟨η, hη, hη0⟩ hmb hni hg2 hg0 hg1b _ y
    have hmc : Continuous m := hm1.continuous
    have hm'c : Continuous (deriv m) := hm1.continuous_deriv le_rfl
    have hrp : Continuous (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr hp0.le))
    set n : ℝ → ℂ := fun ξ : ℝ => (ξ : ℂ) * deriv m ξ +
      (2 + Complex.I * ((ξ * |ξ| ^ p : ℝ) : ℂ)) * m ξ with hndef
    set h : ℝ → ℂ := fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * m ξ - Complex.I * deriv m ξ with hhdef
    have hrel : ∀ ξ : ℝ, (ξ : ℂ) * h ξ = -Complex.I * (n ξ - 2 * m ξ) := by
      intro ξ
      simp only [hhdef, hndef]
      rw [Complex.ofReal_mul]
      linear_combination ((ξ : ℂ) * ((|ξ| ^ p : ℝ) : ℂ) * m ξ) * Complex.I_sq
    have hnm : Integrable (fun ξ => n ξ - 2 * m ξ) := hni.sub (hmi.const_mul 2)
    have hhc : Continuous h := (hrp.mul hmc).sub (continuous_const.mul hm'c)
    have hhi : Integrable h := by
      refine Integrable.mono' (hnm.norm.const_mul η⁻¹) hhc.aestronglyMeasurable
        (Eventually.of_forall fun ξ => ?_)
      rcases lt_or_ge |ξ| η with hξ | hξ
      · have h0 : h ξ = 0 := by
          simp only [hhdef, hη0 ξ hξ, c04_aux_wL0_deriv_zero m η hη0 ξ hξ]; ring
        rw [h0, norm_zero]; positivity
      · have hξ0 : 0 < |ξ| := lt_of_lt_of_le hη hξ
        have := congrArg norm (hrel ξ)
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs] at this
        rw [le_inv_mul_iff₀ hη]
        calc η * ‖h ξ‖ ≤ |ξ| * ‖h ξ‖ := mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
          _ = ‖n ξ - 2 * m ξ‖ := this
    have hhi1 : Integrable (fun ξ : ℝ => (ξ : ℂ) * h ξ) := by
      refine (hnm.const_mul (-Complex.I)).congr (Eventually.of_forall fun ξ => ?_)
      simp only; rw [hrel]
    have hg1 : ContDiff ℝ 1 (invFourierT m) := hg2.of_le (by norm_num)
    obtain ⟨M1, hM1⟩ := hg1b
    have hP := c04_aux_wL0_P2 p hp0 hp1 m hm1 hmi hmb hhi hg1 hg0
      ⟨M1, 0, fun y => by rw [Real.rpow_zero, mul_one]; exact hM1 y⟩
    obtain ⟨hC1, hDer⟩ := c04_frac_derivative p hp hp1 (invFourierT m) hg2 hg0 ⟨M1, hM1⟩
    have hgd : Differentiable ℝ (invFourierT m) := hg1.differentiable (by simp)
    have hd1 : HasDerivAt (fun y => fracDC p (invFourierT m) y - (y : ℂ) * invFourierT m y)
        (fracDC p (deriv (invFourierT m)) y -
          (1 * invFourierT m y + (y : ℂ) * deriv (invFourierT m) y)) y := by
      have a1 : HasDerivAt (fracDC p (invFourierT m)) (fracDC p (deriv (invFourierT m)) y) y := by
        rw [← hDer y]; exact (hC1.differentiable (by simp) y).hasDerivAt
      have a2 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      exact a1.sub (a2.mul (hgd y).hasDerivAt)
    have hd2 := c04_aux_wL0_hasDeriv h hhi hhi1 y
    have hfun : (fun y => fracDC p (invFourierT m) y - (y : ℂ) * invFourierT m y) =
        invFourierT h := funext hP
    rw [hfun] at hd1
    have hu := hd1.unique hd2
    have hn : n = fun ξ : ℝ => Complex.I * (ξ : ℂ) * h ξ + 2 * m ξ := by
      funext ξ
      have := hrel ξ
      linear_combination (-Complex.I) * this + (n ξ - 2 * m ξ) * Complex.I_sq
    have hlin := c04_aux_wL0_lin (fun ξ : ℝ => Complex.I * (ξ : ℂ) * h ξ) m
      (by simpa [mul_assoc] using hhi1.const_mul Complex.I) hmi 2 y
    rw [hn, hlin, ← hu]
    unfold c04_L0C
    ring
  · intro m hm1 hcs hg1 hg0 hg2 y
    have hmc : Continuous m := hm1.continuous
    have hm'c : Continuous (deriv m) := hm1.continuous_deriv le_rfl
    have hcs' : HasCompactSupport (deriv m) := hcs.deriv
    obtain ⟨C1, hC1⟩ := hmc.bounded_above_of_compact_support hcs
    obtain ⟨C2, hC2⟩ := hm'c.bounded_above_of_compact_support hcs'
    have hmb : ∃ K N : ℝ, ∀ ξ, ‖m ξ‖ + ‖deriv m ξ‖ ≤ K * jb ξ ^ N :=
      ⟨C1 + C2, 0, fun ξ => by rw [Real.rpow_zero, mul_one]; linarith [hC1 ξ, hC2 ξ]⟩
    have hrp : Continuous (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr hp0.le))
    have hhi : Integrable (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * m ξ - Complex.I * deriv m ξ) :=
      ((hrp.mul hmc).sub (continuous_const.mul hm'c)).integrable_of_hasCompactSupport
        (hcs.mul_left.sub hcs'.mul_left)
    exact c04_aux_wL0_P2 p hp0 hp1 m hm1 (hmc.integrable_of_hasCompactSupport hcs) hmb hhi
      hg1 hg0 hg2 y


/-- Blueprint: lem:c04_dirichlet.  `∫₀^∞ (1-cos(yξ))/ξ² dξ = π|y|/2` (absolutely convergent), hence
`W(y) = -y/2 + π⁻¹ ∫₀^∞ (1-cos(yξ))/ξ² dξ`. -/
theorem c04_dirichlet (y : ℝ) :
    IntegrableOn (fun ξ : ℝ => (1 - Real.cos (y * ξ)) / ξ ^ 2) (Ioi 0) ∧
    ∫ ξ in Ioi (0 : ℝ), (1 - Real.cos (y * ξ)) / ξ ^ 2 = π / 2 * |y| ∧
    corner y = -y / 2 + π⁻¹ * ∫ ξ in Ioi (0 : ℝ), (1 - Real.cos (y * ξ)) / ξ ^ 2 := by
  have key : IntegrableOn (fun ξ : ℝ => (1 - Real.cos (y * ξ)) / ξ ^ 2) (Ioi 0) ∧
      ∫ ξ in Ioi (0 : ℝ), (1 - Real.cos (y * ξ)) / ξ ^ 2 = π / 2 * |y| := by
    rcases eq_or_ne y 0 with hy | hy
    · subst hy; simp
    have hb : 0 < |y| := abs_pos.mpr hy
    obtain ⟨hI, hV⟩ := GSQG.Lib.integral_one_sub_cos_div_sq
    set F : ℝ → ℝ := fun s => (1 - Real.cos s) / s ^ 2
    have hcos : ∀ ξ : ℝ, Real.cos (y * ξ) = Real.cos (|y| * ξ) := by
      intro ξ
      rcases abs_choice y with h | h <;> rw [h]
      rw [neg_mul, Real.cos_neg]
    have hg : ∀ ξ : ℝ, (1 - Real.cos (y * ξ)) / ξ ^ 2 = |y| ^ 2 * F (|y| * ξ) := by
      intro ξ
      simp only [F]
      rw [hcos]
      rcases eq_or_ne ξ 0 with hξ | hξ
      · simp [hξ]
      · field_simp
    simp_rw [hg]
    refine ⟨?_, ?_⟩
    · have := (integrableOn_Ioi_comp_mul_left_iff F 0 hb).mpr (by simpa using hI)
      exact this.const_mul _
    · rw [integral_const_mul, integral_comp_mul_left_Ioi F 0 hb, mul_zero, smul_eq_mul, hV]
      field_simp
  refine ⟨key.1, key.2, ?_⟩
  rw [key.2, corner]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith)]; field_simp; ring
  · rw [abs_of_nonpos h, max_eq_left (by linarith)]; field_simp; ring

/-! ### Seed sublemmas -/

theorem c04_aux_seed_chi_mem (ξ : ℝ) : 0 ≤ chiPlus ξ ∧ chiPlus ξ ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem c04_aux_seed_chi_zero {ξ : ℝ} (h : ξ ≤ 1) : chiPlus ξ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem c04_aux_seed_chi_one {ξ : ℝ} (h : 2 ≤ ξ) : chiPlus ξ = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem c04_aux_seed_chi_smooth : ContDiff ℝ (⊤ : ℕ∞) chiPlus :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem c04_aux_seed_ofReal_iter (f : ℝ → ℝ) (y : ℝ) (k : ℕ) (hf : ContDiffAt ℝ k f y) :
    iteratedDeriv k (fun t => ((f t : ℝ) : ℂ)) y = ((iteratedDeriv k f y : ℝ) : ℂ) := by
  have : (fun t => ((f t : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    Complex.ofRealCLM.iteratedFDeriv_comp_left hf le_rfl]
  simp

/-- `|Φ₀(ξ)| ≤ ξ` on `(0,1]`. -/
theorem c04_aux_seed_Phi0_le (p : ℝ) (hp : 0 < p) {ξ : ℝ} (h0 : 0 < ξ) (h1 : ξ ≤ 1) :
    0 ≤ Phi0 p ξ ∧ Phi0 p ξ ≤ ξ := by
  unfold Phi0
  rw [abs_of_pos h0]
  have hle : ξ ^ p ≤ 1 := Real.rpow_le_one h0.le h1 hp.le
  have hnn : 0 ≤ ξ ^ p := Real.rpow_nonneg h0.le _
  constructor
  · positivity
  · rw [div_le_iff₀ (by linarith)]; nlinarith

/-- The smooth symbol `a_{-2} = χ₊/ξ²` (real). -/
theorem c04_aux_seed_a2_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => chiPlus ξ / ξ ^ 2) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x 1 with hx | hx
  · have : (fun ξ : ℝ => chiPlus ξ / ξ ^ 2) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with t ht
      rw [c04_aux_seed_chi_zero (le_of_lt ht), zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact (c04_aux_seed_chi_smooth.contDiffAt).div (contDiffAt_id.pow 2)
      (by positivity)

theorem c04_aux_seed_a2_iter (l : ℕ) : ∃ C > (0 : ℝ), ∀ ξ : ℝ, 1 ≤ ξ →
    |iteratedDeriv l (fun ξ : ℝ => chiPlus ξ / ξ ^ 2) ξ| ≤ C * ξ ^ (-2 - (l : ℝ)) := by
  have hc : Continuous (iteratedDeriv l (fun ξ : ℝ => chiPlus ξ / ξ ^ 2)) :=
    c04_aux_seed_a2_smooth.continuous_iteratedDeriv l (by exact_mod_cast le_top)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hc.continuousOn
  set P : ℝ := |∏ i ∈ Finset.range l, ((-2 : ℤ) - (i : ℝ))|
  refine ⟨(|K| + 1) * 3 ^ (2 + (l : ℝ)) + P + 1, by positivity, fun ξ hξ => ?_⟩
  have hξ0 : 0 < ξ := by linarith
  have hpos : 0 < ξ ^ (-2 - (l : ℝ)) := rpow_pos_of_pos hξ0 _
  rcases le_or_gt ξ 3 with h3 | h3
  · have h1 := hK ξ ⟨hξ, h3⟩
    rw [Real.norm_eq_abs] at h1
    have hlow : 3 ^ (-2 - (l : ℝ)) ≤ ξ ^ (-2 - (l : ℝ)) :=
      rpow_le_rpow_of_nonpos hξ0 h3 (by linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)])
    have h33 : (3 : ℝ) ^ (2 + (l : ℝ)) * 3 ^ (-2 - (l : ℝ)) = 1 := by
      rw [← rpow_add (by norm_num)]; simp
    calc |iteratedDeriv l (fun ξ : ℝ => chiPlus ξ / ξ ^ 2) ξ| ≤ |K| + 1 := by
          linarith [le_abs_self K]
      _ = (|K| + 1) * 3 ^ (2 + (l : ℝ)) * 3 ^ (-2 - (l : ℝ)) := by rw [mul_assoc, h33, mul_one]
      _ ≤ (|K| + 1) * 3 ^ (2 + (l : ℝ)) * ξ ^ (-2 - (l : ℝ)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by have : 0 ≤ P := abs_nonneg _; linarith) hpos.le
  · have hev : (fun ξ : ℝ => chiPlus ξ / ξ ^ 2) =ᶠ[𝓝 ξ] fun t => t ^ (-2 : ℤ) := by
      filter_upwards [Ioi_mem_nhds (by linarith : (2 : ℝ) < ξ)] with t ht
      rw [c04_aux_seed_chi_one (le_of_lt ht), zpow_neg, zpow_ofNat, one_div]
    rw [hev.iteratedDeriv_eq, iteratedDeriv_eq_iterate, iter_deriv_zpow, abs_mul]
    have hz : |ξ ^ ((-2 : ℤ) - (l : ℤ))| = ξ ^ (-2 - (l : ℝ)) := by
      rw [abs_of_pos (zpow_pos hξ0 _), ← rpow_intCast]; push_cast; rfl
    rw [hz]
    have : |∏ i ∈ Finset.range l, (((-2 : ℤ) : ℝ) - (i : ℝ))| ≤ P := le_rfl
    calc _ ≤ P * ξ ^ (-2 - (l : ℝ)) := mul_le_mul_of_nonneg_right this hpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
          have : 0 ≤ (|K| + 1) * 3 ^ (2 + (l : ℝ)) := by positivity
          linarith) hpos.le


theorem c04_aux_seed_inv_sq_int (c : ℝ) :
    Integrable ((Ioi (1 : ℝ)).indicator (fun ξ : ℝ => c / ξ ^ 2)) := by
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul c
  refine IntegrableOn.congr_fun h (fun ξ hξ => ?_) measurableSet_Ioi
  have hξ0 : 0 < ξ := lt_trans one_pos hξ
  show c * ξ ^ (-2 : ℝ) = c / ξ ^ 2
  rw [rpow_neg hξ0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast, div_eq_mul_inv]

theorem c04_aux_seed_cos_bound (p : ℝ) (hp : 0 < p) (Y y : ℝ) (hy : |y| ≤ Y) (ξ : ℝ) (hξ : 0 < ξ) :
    |(1 - Real.cos (y * ξ - Phi0 p ξ)) / ξ ^ 2| ≤
      (Ioc (0 : ℝ) 1).indicator (fun _ => (Y + 1) ^ 2 / 2) ξ +
        (Ioi (1 : ℝ)).indicator (fun ξ => 2 / ξ ^ 2) ξ := by
  have hc0 : 0 ≤ 1 - Real.cos (y * ξ - Phi0 p ξ) := by linarith [Real.cos_le_one (y * ξ - Phi0 p ξ)]
  have hξ2 : 0 < ξ ^ 2 := by positivity
  rw [abs_of_nonneg (div_nonneg hc0 hξ2.le)]
  rcases le_or_gt ξ 1 with h1 | h1
  · rw [indicator_of_mem (show ξ ∈ Ioc (0 : ℝ) 1 from ⟨hξ, h1⟩),
      indicator_of_notMem (show ξ ∉ Ioi (1 : ℝ) from fun h => absurd h (not_lt.mpr h1)), add_zero]
    obtain ⟨hΦ0, hΦ1⟩ := c04_aux_seed_Phi0_le p hp hξ h1
    have hu : |y * ξ - Phi0 p ξ| ≤ (Y + 1) * ξ := by
      rw [abs_le]; constructor <;>
      nlinarith [abs_le.mp hy, abs_nonneg y]
    have hcos := Real.one_sub_sq_div_two_le_cos (x := y * ξ - Phi0 p ξ)
    have hsq : (y * ξ - Phi0 p ξ) ^ 2 ≤ ((Y + 1) * ξ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    rw [div_le_iff₀ hξ2]
    nlinarith
  · rw [indicator_of_notMem (show ξ ∉ Ioc (0 : ℝ) 1 from fun h => absurd h.2 (not_le.mpr h1)),
      indicator_of_mem (show ξ ∈ Ioi (1 : ℝ) from h1), zero_add]
    exact div_le_div_of_nonneg_right (by linarith [Real.neg_one_le_cos (y * ξ - Phi0 p ξ)]) hξ2.le

theorem c04_aux_seed_a2_bound (ξ : ℝ) :
    |chiPlus ξ / ξ ^ 2| ≤ (Ioi (1 : ℝ)).indicator (fun ξ => 1 / ξ ^ 2) ξ := by
  rcases le_or_gt ξ 1 with h1 | h1
  · rw [c04_aux_seed_chi_zero h1, zero_div, abs_zero]
    exact indicator_nonneg (fun _ _ => by positivity) _
  · rw [indicator_of_mem (show ξ ∈ Ioi (1 : ℝ) from h1)]
    have hξ2 : 0 < ξ ^ 2 := by positivity
    rw [abs_div, abs_of_nonneg (c04_aux_seed_chi_mem ξ).1, abs_of_pos hξ2]
    exact div_le_div_of_nonneg_right (c04_aux_seed_chi_mem ξ).2 hξ2.le

theorem c04_aux_seed_norm_eiphase (p y ξ : ℝ) : ‖c04_eiphase p y ξ‖ = 1 := by
  unfold c04_eiphase; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _

theorem c04_aux_seed_Phi0_cont (p : ℝ) (hp : 0 < p) : Continuous (Phi0 p) := by
  unfold Phi0
  exact ((continuous_id.mul (continuous_abs.rpow_const (fun _ => Or.inr hp.le)))).div_const _

/-- Blueprint: lem:c04_seed_integrable.  Absolute convergence of the integrands of `f₀` and
`f_{0,+}`; `a_{-2} = χ₊/ξ²` (automatically `0` on `(-∞,1]`) is in `L¹(ℝ) ∩ S^{-2}_+` with
`|a_{-2}^{(l)}(ξ)| ≤ C_l ξ^{-2-l}` on `ξ ≥ 1`; explicit majorants, uniform in `|y| ≤ Y`. -/
theorem c04_seed_integrable (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ y, IntegrableOn (fun ξ : ℝ => (1 - Real.cos (y * ξ - Phi0 p ξ)) / ξ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * c04_eiphase p y ξ) (Ioi 0)) ∧
    Integrable (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) ∧
    (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) ∈ c04_osc_symbol (-2) ∧
    (∀ l : ℕ, ∃ C > (0 : ℝ), ∀ ξ : ℝ, 1 ≤ ξ →
      ‖iteratedDeriv l (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) ξ‖ ≤ C * ξ ^ (-2 - (l : ℝ))) ∧
    (∀ Y : ℝ, 1 ≤ Y → ∀ y : ℝ, |y| ≤ Y → ∀ ξ ∈ Ioi (0 : ℝ),
      |(1 - Real.cos (y * ξ - Phi0 p ξ)) / ξ ^ 2| ≤
        (Ioc (0 : ℝ) 1).indicator (fun _ => (Y + 1) ^ 2 / 2) ξ +
          (Ioi (1 : ℝ)).indicator (fun ξ => 2 / ξ ^ 2) ξ) ∧
    (∀ y : ℝ, ∀ ξ ∈ Ioi (0 : ℝ),
      ‖((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * c04_eiphase p y ξ‖ ≤ (Ioi (1 : ℝ)).indicator (fun ξ => 1 / ξ ^ 2) ξ) := by
  have hp0 : 0 < p := by linarith
  have hb2 : ∀ y : ℝ, ∀ ξ ∈ Ioi (0 : ℝ),
      ‖((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * c04_eiphase p y ξ‖ ≤
        (Ioi (1 : ℝ)).indicator (fun ξ => 1 / ξ ^ 2) ξ := fun y ξ _ => by
    rw [norm_mul, c04_aux_seed_norm_eiphase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact c04_aux_seed_a2_bound ξ
  have hb1 : ∀ Y : ℝ, 1 ≤ Y → ∀ y : ℝ, |y| ≤ Y → ∀ ξ ∈ Ioi (0 : ℝ),
      |(1 - Real.cos (y * ξ - Phi0 p ξ)) / ξ ^ 2| ≤
        (Ioc (0 : ℝ) 1).indicator (fun _ => (Y + 1) ^ 2 / 2) ξ +
          (Ioi (1 : ℝ)).indicator (fun ξ => 2 / ξ ^ 2) ξ := fun Y _ y hy ξ hξ =>
    c04_aux_seed_cos_bound p hp0 Y y hy ξ hξ
  have hΦ := c04_aux_seed_Phi0_cont p hp0
  have hacont : Continuous (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp c04_aux_seed_a2_smooth.continuous
  have hasmooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp c04_aux_seed_a2_smooth
  have hder : ∀ l : ℕ, ∃ C > (0 : ℝ), ∀ ξ : ℝ, 1 ≤ ξ →
      ‖iteratedDeriv l (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) ξ‖ ≤ C * ξ ^ (-2 - (l : ℝ)) := by
    intro l
    obtain ⟨C, hC, h⟩ := c04_aux_seed_a2_iter l
    refine ⟨C, hC, fun ξ hξ => ?_⟩
    rw [c04_aux_seed_ofReal_iter _ _ _ (c04_aux_seed_a2_smooth.contDiffAt.of_le
      (by exact_mod_cast le_top)), Complex.norm_real, Real.norm_eq_abs]
    exact h ξ hξ
  refine ⟨fun y => ⟨?_, ?_⟩, ?_, ⟨hasmooth, fun ξ hξ => ?_, fun l => ?_⟩, hder, hb1, hb2⟩
  · set Y := |y| + 1
    have hmaj : IntegrableOn (fun ξ => (Ioc (0 : ℝ) 1).indicator (fun _ => (Y + 1) ^ 2 / 2) ξ +
        (Ioi (1 : ℝ)).indicator (fun ξ => 2 / ξ ^ 2) ξ) (Ioi 0) := by
      refine Integrable.integrableOn (Integrable.add (f := (Ioc (0 : ℝ) 1).indicator (fun _ => (Y + 1) ^ 2 / 2)) ?_ (c04_aux_seed_inv_sq_int 2))
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (by simp) (by simp)
    refine hmaj.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => ?_)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro ξ hξ
      refine ContinuousAt.continuousWithinAt ?_
      have hξ0 : (ξ : ℝ) ^ 2 ≠ 0 := by have : 0 < ξ := hξ; positivity
      exact ((continuous_const.sub (Real.continuous_cos.comp ((continuous_const.mul continuous_id).sub
        hΦ))).continuousAt).div (continuous_pow 2).continuousAt hξ0
    · rw [Real.norm_eq_abs]
      exact hb1 Y (by linarith [abs_nonneg y]) y (by linarith) ξ hξ
  · refine (c04_aux_seed_inv_sq_int 1).integrableOn.mono' ?_
      (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => hb2 y ξ hξ)
    refine Continuous.aestronglyMeasurable (hacont.mul ?_)
    unfold c04_eiphase
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).sub hΦ)))
  · refine (c04_aux_seed_inv_sq_int 1).mono' hacont.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact c04_aux_seed_a2_bound ξ
  · simp [c04_aux_seed_chi_zero hξ]
  · obtain ⟨C, -, h⟩ := hder l
    exact ⟨C, h⟩


theorem c04_aux_seed_eiphase_re (p y ξ : ℝ) :
    (c04_eiphase p y ξ).re = Real.cos (y * ξ - Phi0 p ξ) := by
  unfold c04_eiphase; rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re _

theorem c04_aux_seed_cplx_integral_re {f : ℝ → ℂ} {s : Set ℝ} (hf : IntegrableOn f s) :
    ∫ x in s, (f x).re = (∫ x in s, f x).re :=
  integral_re hf

/-- `H₀ = (1 - cos)/ξ² + Re(a_{-2} e^{i(yξ-Φ₀)})`. -/
theorem c04_aux_seed_H0_split (p y ξ : ℝ) :
    (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2 =
      (1 - Real.cos (y * ξ - Phi0 p ξ)) / ξ ^ 2 +
        (((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * c04_eiphase p y ξ).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    c04_aux_seed_eiphase_re]
  ring

/-- Blueprint: lem:c04_seed_low_representation.  With
`H₀(y,ξ) = Re[1 - (1-χ₊(ξ)) e^{i(yξ-Φ₀(ξ))}]/ξ²`: `H₀(y,·) ∈ L¹(0,∞)`,
`f_{0,low}(y) = -y/2 + π⁻¹ ∫₀^∞ H₀(y,ξ) dξ`, `f₀ = f_{0,low} + 2 Re f_{0,+}`, and `H₀` has an
integrable majorant uniform in `|y| ≤ Y`. -/
theorem c04_seed_low_representation (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ y, IntegrableOn (fun ξ : ℝ =>
        (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2) (Ioi 0) ∧
      c04_linear_seed_low p y = -y / 2 + π⁻¹ * ∫ ξ in Ioi (0 : ℝ),
        (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2) ∧
    (∀ y, c04_linear_seed p y = c04_linear_seed_low p y + 2 * (c04_linear_seed_plus p y).re) ∧
    (∀ Y : ℝ, 1 ≤ Y → ∃ B : ℝ → ℝ, IntegrableOn B (Ioi 0) ∧ (∀ ξ, 0 ≤ B ξ) ∧
      ∀ y : ℝ, |y| ≤ Y → ∀ ξ ∈ Ioi (0 : ℝ),
        |(1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2| ≤ B ξ) := by
  obtain ⟨hint, -, -, -, hb1, hb2⟩ := c04_seed_integrable p hp hp1
  have hre : ∀ y, IntegrableOn (fun ξ : ℝ =>
      (((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * c04_eiphase p y ξ).re) (Ioi 0) := fun y => (hint y).2.re
  simp_rw [c04_aux_seed_H0_split]
  refine ⟨fun y => ⟨(hint y).1.add (hre y), ?_⟩, fun y => ?_, fun Y hY => ?_⟩
  · rw [integral_add (hint y).1 (hre y), c04_aux_seed_cplx_integral_re (hint y).2]
    unfold c04_linear_seed_low c04_linear_seed_high c04_linear_seed c04_linear_seed_plus
    simp only [c04_eiphase]
    rw [show -((2 * π : ℝ) : ℂ)⁻¹ = (((-(2 * π)⁻¹ : ℝ)) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  · unfold c04_linear_seed_low c04_linear_seed_high; ring
  · refine ⟨fun ξ => (Ioc (0 : ℝ) 1).indicator (fun _ => (Y + 1) ^ 2 / 2) ξ +
        (Ioi (1 : ℝ)).indicator (fun ξ => 2 / ξ ^ 2) ξ +
        (Ioi (1 : ℝ)).indicator (fun ξ => 1 / ξ ^ 2) ξ, ?_, fun ξ => ?_, fun y hy ξ hξ => ?_⟩
    · refine Integrable.integrableOn (Integrable.add (Integrable.add
        (f := (Ioc (0 : ℝ) 1).indicator (fun _ => (Y + 1) ^ 2 / 2)) ?_ (c04_aux_seed_inv_sq_int 2))
        (c04_aux_seed_inv_sq_int 1))
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const (by simp) (by simp)
    · refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
        exact indicator_nonneg (fun _ _ => by positivity) _
    · refine (abs_add_le _ _).trans (add_le_add (hb1 Y hY y hy ξ hξ) ?_)
      exact (Complex.abs_re_le_norm _).trans (hb2 y ξ hξ)


theorem c04_aux_seed_b_bound (p : ℝ) (hp : 0 < p) (ξ : ℝ) (hξ : 0 < ξ) :
    ‖c04_I1_symbol p ξ‖ ≤ (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (p - 1)) ξ := by
  unfold c04_I1_symbol
  rcases le_or_gt ξ 2 with h2 | h2
  · rw [indicator_of_mem (show ξ ∈ Ioc (0 : ℝ) 2 from ⟨hξ, h2⟩)]
    have hξ2 : 0 < ξ ^ 2 := by positivity
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hξ2,
      abs_of_nonneg (by linarith [(c04_aux_seed_chi_mem ξ).2] : (0 : ℝ) ≤ 1 - chiPlus ξ)]
    have hE : ‖1 - Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))‖ ≤ Phi0 p ξ := by
      rw [norm_sub_rev, show -(Complex.I * (Phi0 p ξ : ℂ)) = Complex.I * ((-Phi0 p ξ : ℝ) : ℂ) by
        push_cast; ring]
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg]
      unfold Phi0; positivity
    have hΦ : Phi0 p ξ ≤ ξ ^ (p - 1) * ξ ^ 2 := by
      unfold Phi0
      rw [abs_of_pos hξ, show ξ ^ (p - 1) * ξ ^ 2 = ξ * ξ ^ p by
        rw [rpow_sub hξ, rpow_one]; field_simp]
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ ξ * ξ ^ p := by positivity
      nlinarith
    rw [div_le_iff₀ hξ2]
    have h1c : 1 - chiPlus ξ ≤ 1 := by linarith [(c04_aux_seed_chi_mem ξ).1]
    calc (1 - chiPlus ξ) * ‖1 - Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))‖
        ≤ 1 * ‖1 - Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))‖ :=
          mul_le_mul_of_nonneg_right h1c (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hE.trans hΦ
  · rw [indicator_of_notMem (show ξ ∉ Ioc (0 : ℝ) 2 from fun h => absurd h.2 (not_le.mpr h2)),
      c04_aux_seed_chi_one h2.le]
    simp

/-- Blueprint: lem:c04_seed_corner_decomposition.  `b` and `a_{-2}` are integrable on `(0,∞)`,
`|b(ξ)| ≤ ξ^{p-1} 𝟙_{(0,2]}(ξ)`, and `f_{0,low} - W = 𝓘₁ + 𝓘₂` (absolutely convergent). -/
theorem c04_seed_corner_decomposition (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    IntegrableOn (c04_I1_symbol p) (Ioi 0) ∧
    IntegrableOn (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) (Ioi 0) ∧
    (∀ ξ ∈ Ioi (0 : ℝ), ‖c04_I1_symbol p ξ‖ ≤ (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (p - 1)) ξ) ∧
    (∀ y, IntegrableOn (fun ξ : ℝ =>
        Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ) (Ioi 0) ∧
      IntegrableOn (fun ξ : ℝ =>
        Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) (Ioi 0) ∧
      c04_linear_seed_low p y - corner y = c04_I1 p y + c04_I2 y) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, haint, -⟩ := c04_seed_integrable p hp hp1
  obtain ⟨hrep, -, -⟩ := c04_seed_low_representation p hp hp1
  have hbb := c04_aux_seed_b_bound p hp0
  have hΦ := c04_aux_seed_Phi0_cont p hp0
  have hmaj : IntegrableOn (fun ξ => (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (p - 1)) ξ) (Ioi 0) := by
    refine Integrable.integrableOn ?_
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p - 1)).1
  have hbcont : ContinuousOn (c04_I1_symbol p) (Ioi 0) := by
    intro ξ hξ
    have hξ0 : ((ξ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ξ := hξ; exact_mod_cast (by positivity : ξ ^ 2 ≠ 0)
    have hc : Continuous chiPlus := c04_aux_seed_chi_smooth.continuous
    have hn : Continuous (fun ξ : ℝ => ((1 - chiPlus ξ : ℝ) : ℂ) *
        (1 - Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))))) := by fun_prop
    have hd : Continuous (fun ξ : ℝ => ((ξ ^ 2 : ℝ) : ℂ)) := by fun_prop
    exact (hn.continuousAt.div hd.continuousAt hξ0).continuousWithinAt
  have hbint : IntegrableOn (c04_I1_symbol p) (Ioi 0) :=
    hmaj.mono' (hbcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => hbb ξ hξ)
  have hE1 : ∀ y ξ : ℝ, ‖Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ))‖ = 1 := fun y ξ => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hEc : ∀ y : ℝ, Continuous (fun ξ : ℝ => Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ))) :=
    fun y => Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hEb : ∀ y, IntegrableOn (fun ξ : ℝ =>
      Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ) (Ioi 0) := fun y =>
    hbint.norm.mono' (((hEc y).continuousOn.mul hbcont).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun ξ => by rw [norm_mul, hE1, one_mul])
  have hEa : ∀ y, IntegrableOn (fun ξ : ℝ =>
      Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) (Ioi 0) := fun y =>
    haint.integrableOn.norm.mono'
      (((hEc y).mul (Complex.continuous_ofReal.comp
        c04_aux_seed_a2_smooth.continuous)).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => by rw [norm_mul, hE1, one_mul])
  refine ⟨hbint, haint.integrableOn, hbb, fun y => ⟨hEb y, hEa y, ?_⟩⟩
  obtain ⟨hHint, hlow⟩ := hrep y
  obtain ⟨hgint, -, hcorner⟩ := c04_dirichlet y
  have hpt : ∀ ξ ∈ Ioi (0 : ℝ),
      (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2 -
        (1 - Real.cos (y * ξ)) / ξ ^ 2 =
      (Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ).re +
        (Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)).re := by
    intro ξ hξ
    have hξ0 : (ξ : ℝ) ^ 2 ≠ 0 := by have : 0 < ξ := hξ; positivity
    have hcos : Real.cos (y * ξ) = (Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ))).re := by
      rw [mul_comm Complex.I]; exact (Complex.exp_ofReal_mul_I_re _).symm
    have heip : c04_eiphase p y ξ = Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) := by
      unfold c04_eiphase; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hξc : (ξ : ℂ) ≠ 0 := by have : 0 < ξ := hξ; exact_mod_cast this.ne'
    have key : Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ +
        Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) =
        ((1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ) -
          (1 - Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)))) / ((ξ ^ 2 : ℝ) : ℂ) := by
      unfold c04_I1_symbol; rw [heip]; push_cast; field_simp; ring
    rw [hcos, ← Complex.add_re, key, Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  have hdiff : ∫ ξ in Ioi (0 : ℝ), ((1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2 -
        (1 - Real.cos (y * ξ)) / ξ ^ 2) =
      (∫ ξ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ).re +
      (∫ ξ in Ioi (0 : ℝ), Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) *
        ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)).re := by
    have h1 : IntegrableOn (fun ξ : ℝ =>
        (Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ).re) (Ioi 0) := (hEb y).re
    have h2 : IntegrableOn (fun ξ : ℝ => (Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) *
        ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)).re) (Ioi 0) := (hEa y).re
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add h1 h2,
      c04_aux_seed_cplx_integral_re (hEb y), c04_aux_seed_cplx_integral_re (hEa y)]
  rw [integral_sub hHint hgint] at hdiff
  rw [hlow, hcorner]
  unfold c04_I1 c04_I2
  rw [← mul_add, ← hdiff]
  ring


theorem c04_aux_seed_eiphase_im (p y ξ : ℝ) :
    (c04_eiphase p y ξ).im = Real.sin (y * ξ - Phi0 p ξ) := by
  unfold c04_eiphase; rw [mul_comm]; exact Complex.exp_ofReal_mul_I_im _

theorem c04_aux_seed_eiphase_hasDeriv (p y ξ : ℝ) :
    HasDerivAt (fun y => c04_eiphase p y ξ) (Complex.I * ξ * c04_eiphase p y ξ) y := by
  unfold c04_eiphase
  have h1 : HasDerivAt (fun y : ℝ => ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) ((ξ : ℝ) : ℂ) y := by
    have := ((hasDerivAt_id y).mul_const ξ).sub_const (Phi0 p ξ)
    simpa using this.ofReal_comp
  have := (h1.const_mul Complex.I).cexp
  convert this using 1; ring

theorem c04_aux_seed_continuous_eiphase (p : ℝ) (hp : 0 < p) (y : ℝ) :
    Continuous (fun ξ => c04_eiphase p y ξ) := by
  have hΦ := c04_aux_seed_Phi0_cont p hp
  unfold c04_eiphase; fun_prop

/-- The integrand `(1-χ₊) Re[(iξ)^k e^{i(yξ-Φ₀)}]/ξ²`. -/
def c04_aux_seed_F (p : ℝ) (k : ℕ) (y ξ : ℝ) : ℝ :=
  (1 - chiPlus ξ) * ((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re / ξ ^ 2

theorem c04_aux_seed_F_hasDeriv (p : ℝ) (k : ℕ) (y ξ : ℝ) :
    HasDerivAt (fun y => c04_aux_seed_F p k y ξ) (c04_aux_seed_F p (k + 1) y ξ) y := by
  have h := (c04_aux_seed_eiphase_hasDeriv p y ξ).const_mul ((Complex.I * (ξ : ℂ)) ^ k)
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h
  have h3 := (h2.const_mul (1 - chiPlus ξ)).div_const (ξ ^ 2)
  unfold c04_aux_seed_F
  convert h3 using 1
  simp only [Complex.reCLM_apply, Function.comp_apply]
  congr 3
  ring

theorem c04_aux_seed_F_meas (p : ℝ) (hp : 0 < p) (k : ℕ) (y : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (c04_aux_seed_F p k y) μ := by
  have hc : Continuous chiPlus := c04_aux_seed_chi_smooth.continuous
  have he := c04_aux_seed_continuous_eiphase p hp y
  have hN : Continuous (fun ξ : ℝ =>
      (1 - chiPlus ξ) * ((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re) := by fun_prop
  exact (hN.measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable

theorem c04_aux_seed_F_bound (p : ℝ) (k : ℕ) (hk : 2 ≤ k) (y ξ : ℝ) (hξ : 0 < ξ) :
    |c04_aux_seed_F p k y ξ| ≤ (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (k - 2)) ξ := by
  unfold c04_aux_seed_F
  rcases le_or_gt ξ 2 with h2 | h2
  · rw [indicator_of_mem (show ξ ∈ Ioc (0 : ℝ) 2 from ⟨hξ, h2⟩)]
    have hξ2 : 0 < ξ ^ 2 := by positivity
    rw [abs_div, abs_mul, abs_of_pos hξ2,
      abs_of_nonneg (by linarith [(c04_aux_seed_chi_mem ξ).2] : (0 : ℝ) ≤ 1 - chiPlus ξ)]
    have hre : |((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re| ≤ ξ ^ k := by
      refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
      rw [norm_mul, c04_aux_seed_norm_eiphase, mul_one, norm_pow, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
    rw [div_le_iff₀ hξ2, ← pow_add, Nat.sub_add_cancel hk]
    have h1c : 1 - chiPlus ξ ≤ 1 := by linarith [(c04_aux_seed_chi_mem ξ).1]
    calc (1 - chiPlus ξ) * |((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re|
        ≤ 1 * ξ ^ k := mul_le_mul h1c hre (abs_nonneg _) zero_le_one
      _ = ξ ^ k := one_mul _
  · rw [indicator_of_notMem (show ξ ∉ Ioc (0 : ℝ) 2 from fun h => absurd h.2 (not_le.mpr h2)),
      c04_aux_seed_chi_one h2.le]
    simp

theorem c04_aux_seed_F1_eq (p y ξ : ℝ) (hξ : ξ ≠ 0) :
    c04_aux_seed_F p 1 y ξ = -((1 - chiPlus ξ) * Real.sin (y * ξ - Phi0 p ξ) / ξ) := by
  unfold c04_aux_seed_F
  rw [pow_one, Complex.mul_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, c04_aux_seed_eiphase_im]
  field_simp
  ring

theorem c04_aux_seed_F1_bound (p : ℝ) (hp : 0 < p) (Y y : ℝ) (hy : |y| ≤ Y) (ξ : ℝ) (hξ : 0 < ξ) :
    |(1 - chiPlus ξ) * Real.sin (y * ξ - Phi0 p ξ) / ξ| ≤
      (Ioc (0 : ℝ) 2).indicator (fun ξ => Y + ξ ^ p) ξ := by
  rcases le_or_gt ξ 2 with h2 | h2
  · rw [indicator_of_mem (show ξ ∈ Ioc (0 : ℝ) 2 from ⟨hξ, h2⟩)]
    rw [abs_div, abs_mul, abs_of_pos hξ,
      abs_of_nonneg (by linarith [(c04_aux_seed_chi_mem ξ).2] : (0 : ℝ) ≤ 1 - chiPlus ξ)]
    have hΦ0 : 0 ≤ Phi0 p ξ := by unfold Phi0; positivity
    have hΦ1 : Phi0 p ξ ≤ ξ * ξ ^ p := by
      unfold Phi0; rw [abs_of_pos hξ, div_le_iff₀ (by linarith)]
      have : 0 ≤ ξ * ξ ^ p := by positivity
      nlinarith
    have hs : |Real.sin (y * ξ - Phi0 p ξ)| ≤ ξ * (Y + ξ ^ p) := by
      refine (Real.abs_sin_le_abs).trans ?_
      rw [abs_le]; constructor <;> nlinarith [abs_le.mp hy, abs_nonneg y]
    rw [div_le_iff₀ hξ]
    have h1c : 1 - chiPlus ξ ≤ 1 := by linarith [(c04_aux_seed_chi_mem ξ).1]
    calc (1 - chiPlus ξ) * |Real.sin (y * ξ - Phi0 p ξ)| ≤ 1 * (ξ * (Y + ξ ^ p)) :=
          mul_le_mul h1c hs (abs_nonneg _) zero_le_one
      _ = _ := by ring
  · rw [indicator_of_notMem (show ξ ∉ Ioc (0 : ℝ) 2 from fun h => absurd h.2 (not_le.mpr h2)),
      c04_aux_seed_chi_one h2.le]
    simp


theorem c04_aux_seed_ind_int {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 2)) :
    IntegrableOn (fun ξ => (Ioc (0 : ℝ) 2).indicator g ξ) (Ioi 0) := by
  refine Integrable.integrableOn ?_
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem c04_aux_seed_re_hasDeriv {g : ℝ → ℂ} {g' : ℂ} {y : ℝ} (h : HasDerivAt g g' y) :
    HasDerivAt (fun t => (g t).re) g'.re y := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h

theorem c04_aux_seed_H0_hasDeriv (p y ξ : ℝ) :
    HasDerivAt (fun y => (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2)
      (-c04_aux_seed_F p 1 y ξ) y := by
  have h : HasDerivAt (fun y => 1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ)
      (0 - ((1 - chiPlus ξ : ℝ) : ℂ) * (Complex.I * ξ * c04_eiphase p y ξ)) y :=
    (hasDerivAt_const y (1 : ℂ)).sub
      ((c04_aux_seed_eiphase_hasDeriv p y ξ).const_mul ((1 - chiPlus ξ : ℝ) : ℂ))
  convert (c04_aux_seed_re_hasDeriv h).div_const (ξ ^ 2) using 1
  simp only [c04_aux_seed_F, zero_sub, Complex.neg_re, Complex.re_ofReal_mul, pow_one]
  ring_nf

/-- Blueprint: lem:c04_seed_low_derivatives.  `f_{0,low} ∈ C^∞`, the formulas for `f_{0,low}'` and
`f_{0,low}^{(k)}` (`k ≥ 2`) with absolutely convergent integrals, the stated majorants, and
boundedness of `f_{0,low}^{(k)}` for `k ≥ 2`. -/
theorem c04_seed_low_derivatives (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_low p) ∧
    (∀ y, IntegrableOn (fun ξ : ℝ => (1 - chiPlus ξ) * Real.sin (y * ξ - Phi0 p ξ) / ξ) (Ioi 0) ∧
      deriv (c04_linear_seed_low p) y = -1 / 2 + π⁻¹ * ∫ ξ in Ioi (0 : ℝ),
        (1 - chiPlus ξ) * Real.sin (y * ξ - Phi0 p ξ) / ξ) ∧
    (∀ (k : ℕ), 2 ≤ k → ∀ y,
      IntegrableOn (fun ξ : ℝ =>
        (1 - chiPlus ξ) * ((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re / ξ ^ 2) (Ioi 0) ∧
      iteratedDeriv k (c04_linear_seed_low p) y = -π⁻¹ * ∫ ξ in Ioi (0 : ℝ),
        (1 - chiPlus ξ) * ((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re / ξ ^ 2) ∧
    (∀ Y : ℝ, 1 ≤ Y → ∀ y : ℝ, |y| ≤ Y → ∀ ξ ∈ Ioi (0 : ℝ),
      |(1 - chiPlus ξ) * Real.sin (y * ξ - Phi0 p ξ) / ξ| ≤
        (Ioc (0 : ℝ) 2).indicator (fun ξ => Y + ξ ^ p) ξ) ∧
    (∀ (k : ℕ), 2 ≤ k → ∀ y : ℝ, ∀ ξ ∈ Ioi (0 : ℝ),
      |(1 - chiPlus ξ) * ((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re / ξ ^ 2| ≤
        (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (k - 2)) ξ) ∧
    (∀ (k : ℕ), 2 ≤ k → ∃ C > (0 : ℝ), ∀ y, |iteratedDeriv k (c04_linear_seed_low p) y| ≤ C) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hrep, -, -⟩ := c04_seed_low_representation p hp hp1
  set F := c04_aux_seed_F p with hFdef
  set g : ℕ → ℝ → ℝ := fun k y => ∫ ξ in Ioi (0 : ℝ), F k y ξ with hgdef
  have hmajk : ∀ k : ℕ, IntegrableOn (fun ξ => (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (k - 2)) ξ)
      (Ioi 0) := fun k => c04_aux_seed_ind_int (continuous_pow _).continuousOn
  have hmaj1 : ∀ Y : ℝ, IntegrableOn (fun ξ => (Ioc (0 : ℝ) 2).indicator (fun ξ => Y + ξ ^ p) ξ)
      (Ioi 0) := fun Y => c04_aux_seed_ind_int
        (continuous_const.add (continuous_id.rpow_const fun _ => Or.inr hp0.le)).continuousOn
  have hF1b : ∀ Y y : ℝ, |y| ≤ Y → ∀ ξ ∈ Ioi (0 : ℝ),
      |F 1 y ξ| ≤ (Ioc (0 : ℝ) 2).indicator (fun ξ => Y + ξ ^ p) ξ := by
    intro Y y hy ξ hξ
    rw [hFdef, c04_aux_seed_F1_eq p y ξ (ne_of_gt hξ), abs_neg]
    exact c04_aux_seed_F1_bound p hp0 Y y hy ξ hξ
  have hFint : ∀ k : ℕ, 1 ≤ k → ∀ y, IntegrableOn (F k y) (Ioi 0) := by
    intro k hk y
    rcases eq_or_lt_of_le hk with h | h
    · subst h
      exact (hmaj1 |y|).mono' (c04_aux_seed_F_meas p hp0 1 y _)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => hF1b |y| y le_rfl ξ hξ)
    · exact (hmajk k).mono' (c04_aux_seed_F_meas p hp0 k y _)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ =>
          c04_aux_seed_F_bound p k (by omega) y ξ hξ)
  have hgd : ∀ k : ℕ, 1 ≤ k → ∀ y₀, HasDerivAt (g k) (g (k + 1) y₀) y₀ := by
    intro k hk y₀
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun y ξ => F k y ξ)
      (F' := fun y ξ => F (k + 1) y ξ) (x₀ := y₀)
      (bound := fun ξ => (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (k + 1 - 2)) ξ) (s := univ)
      univ_mem (Eventually.of_forall fun y => c04_aux_seed_F_meas p hp0 k y _) (hFint k hk y₀)
      (c04_aux_seed_F_meas p hp0 (k + 1) y₀ _)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ y _ => by
        rw [Real.norm_eq_abs]; exact c04_aux_seed_F_bound p (k + 1) (by omega) y ξ hξ)
      (hmajk (k + 1)) (Eventually.of_forall fun ξ y _ => c04_aux_seed_F_hasDeriv p k y ξ)
    exact this.2
  -- the derivative of `f_{0,low}`
  set H : ℝ → ℝ → ℝ := fun y ξ => (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2
    with hHdef
  have hflow : c04_linear_seed_low p = fun y => -y / 2 + π⁻¹ * ∫ ξ in Ioi (0 : ℝ), H y ξ :=
    funext fun y => (hrep y).2
  have hHmeas : ∀ y, AEStronglyMeasurable (H y) (volume.restrict (Ioi (0 : ℝ))) := by
    intro y
    have hc : Continuous chiPlus := c04_aux_seed_chi_smooth.continuous
    have he := c04_aux_seed_continuous_eiphase p hp0 y
    have hN : Continuous (fun ξ : ℝ => (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re) := by
      fun_prop
    exact (hN.measurable.div (measurable_id.pow_const 2)).aestronglyMeasurable
  have hfd : ∀ y₀, HasDerivAt (c04_linear_seed_low p) (-1 / 2 + π⁻¹ * -g 1 y₀) y₀ := by
    intro y₀
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ))) (F := H)
      (F' := fun y ξ => -F 1 y ξ) (x₀ := y₀)
      (bound := fun ξ => (Ioc (0 : ℝ) 2).indicator (fun ξ => (|y₀| + 1) + ξ ^ p) ξ)
      (s := Metric.ball y₀ 1)
      (Metric.ball_mem_nhds y₀ one_pos) (Eventually.of_forall hHmeas) (hrep y₀).1
      (c04_aux_seed_F_meas p hp0 1 y₀ _).neg
      (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ y hy => by
        rw [Real.norm_eq_abs, abs_neg]
        refine hF1b _ y ?_ ξ hξ
        have := Metric.mem_ball.mp hy
        rw [Real.dist_eq] at this
        have := abs_sub_abs_le_abs_sub y y₀
        linarith)
      (hmaj1 _) (Eventually.of_forall fun ξ y _ => c04_aux_seed_H0_hasDeriv p y ξ)
    rw [hflow]
    have h2 := ((hasDerivAt_id y₀).div_const 2).neg.add (this.2.const_mul π⁻¹)
    convert h2 using 1
    · funext y; simp [neg_div]
    · rw [integral_neg]; norm_num [g]
  set G : ℝ → ℝ := fun y => -1 / 2 + π⁻¹ * -g 1 y with hGdef
  have hdf : deriv (c04_linear_seed_low p) = G := funext fun y => (hfd y).deriv
  have hiter : ∀ m : ℕ, iteratedDeriv (m + 1) G = fun y => -π⁻¹ * g (m + 2) y := by
    intro m
    induction m with
    | zero =>
      rw [zero_add, iteratedDeriv_one]
      funext y
      have := ((hgd 1 le_rfl y).neg.const_mul π⁻¹).const_add (-1 / 2)
      rw [show deriv G y = π⁻¹ * -g (1 + 1) y from this.deriv]; ring
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      rw [((hgd (n + 2) (by omega) y).const_mul (-π⁻¹)).deriv]
  have hfk : ∀ k : ℕ, 2 ≤ k → iteratedDeriv k (c04_linear_seed_low p) = fun y => -π⁻¹ * g k y := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show m + 2 = (m + 1) + 1 by ring, iteratedDeriv_succ', hdf, hiter m]
  refine ⟨?_, fun y => ⟨?_, ?_⟩, fun k hk y => ⟨hFint k (by omega) y, by rw [hfk k hk]; rfl⟩,
    fun Y _ y hy ξ hξ => c04_aux_seed_F1_bound p hp0 Y y hy ξ hξ,
    fun k hk y ξ hξ => c04_aux_seed_F_bound p k hk y ξ hξ, fun k hk => ?_⟩
  · refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
    rcases m with _ | n
    · rw [iteratedDeriv_zero]; exact fun y => (hfd y).differentiableAt
    · rw [iteratedDeriv_succ', hdf]
      rcases n with _ | n
      · rw [iteratedDeriv_zero]
        exact fun y => (((hgd 1 le_rfl y).neg.const_mul π⁻¹).const_add (-1 / 2)).differentiableAt
      · rw [hiter n]
        exact fun y => ((hgd (n + 2) (by omega) y).const_mul (-π⁻¹)).differentiableAt
  · refine ((hFint 1 le_rfl y).neg).congr_fun (fun ξ hξ => ?_) measurableSet_Ioi
    rw [Pi.neg_apply, hFdef, c04_aux_seed_F1_eq p y ξ (ne_of_gt (show (0 : ℝ) < ξ from hξ)), neg_neg]
  · rw [(hfd y).deriv]
    congr 1
    rw [← integral_neg]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ (hξ : ξ ∈ Ioi (0 : ℝ)) => ?_
    simp only [hFdef, c04_aux_seed_F1_eq p y ξ (ne_of_gt (show (0 : ℝ) < ξ from hξ)), neg_neg]
  · set I := ∫ ξ in Ioi (0 : ℝ), (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (k - 2)) ξ
    refine ⟨π⁻¹ * I + 1, ?_, fun y => ?_⟩
    · have : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun ξ _ =>
        indicator_nonneg (fun ξ (hξ : ξ ∈ Ioc (0 : ℝ) 2) => pow_nonneg hξ.1.le _) _
      positivity
    · rw [hfk k hk, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr Real.pi_pos)]
      have : |g k y| ≤ I := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (hmajk k) (ae_restrict_of_forall_mem measurableSet_Ioi
          fun ξ hξ => by rw [Real.norm_eq_abs]; exact c04_aux_seed_F_bound p k hk y ξ hξ)
      have hπ : 0 < π⁻¹ := inv_pos.mpr Real.pi_pos
      nlinarith


theorem c04_aux_seed_Phi0_hasDeriv (p : ℝ) (hp : 0 < p) (ξ : ℝ) :
    HasDerivAt (Phi0 p) (|ξ| ^ p) ξ := by
  have hp1 : p + 1 ≠ 0 := by linarith
  rcases lt_trichotomy ξ 0 with h | h | h
  · have hev : Phi0 p =ᶠ[𝓝 ξ] fun t => -((-t) ^ (p + 1)) / (p + 1) := by
      filter_upwards [Iio_mem_nhds h] with t ht
      have ht' : 0 < -t := by linarith [mem_Iio.mp ht]
      unfold Phi0
      rw [abs_of_neg (mem_Iio.mp ht), rpow_add ht', rpow_one]; ring
    have hd := (((hasDerivAt_id ξ).neg.rpow_const (p := p + 1) (Or.inr (by linarith))).neg).div_const
      (p + 1)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_neg h]; simp only [Pi.neg_apply, id_eq]; field_simp; ring_nf
  · subst h
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hc : Tendsto (fun t : ℝ => |t| ^ p / (p + 1)) (𝓝[≠] 0) (𝓝 (|(0 : ℝ)| ^ p)) := by
      have : Continuous (fun t : ℝ => |t| ^ p / (p + 1)) :=
        (continuous_abs.rpow_const fun _ => Or.inr hp.le).div_const _
      have h0 := this.tendsto 0
      rw [abs_zero, zero_rpow hp.ne', zero_div] at h0
      rw [abs_zero, zero_rpow hp.ne']
      exact h0.mono_left nhdsWithin_le_nhds
    refine hc.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    have ht0 : t ≠ 0 := ht
    unfold Phi0
    simp only [zero_add, abs_zero, zero_rpow hp.ne', mul_zero, zero_div, sub_zero, smul_eq_mul]
    field_simp
  · have hev : Phi0 p =ᶠ[𝓝 ξ] fun t => t ^ (p + 1) / (p + 1) := by
      filter_upwards [Ioi_mem_nhds h] with t ht
      have ht' : 0 < t := ht
      unfold Phi0
      rw [abs_of_pos ht', rpow_add ht', rpow_one]; ring
    have hd := ((hasDerivAt_id ξ).rpow_const (p := p + 1) (Or.inr (by linarith))).div_const (p + 1)
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_pos h]; simp only [id_eq]; field_simp; ring_nf

theorem c04_aux_seed_Phi0_C1 (p : ℝ) (hp : 0 < p) : ContDiff ℝ 1 (Phi0 p) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun ξ => (c04_aux_seed_Phi0_hasDeriv p hp ξ).differentiableAt, ?_⟩
  rw [show deriv (Phi0 p) = fun ξ => |ξ| ^ p from
    funext fun ξ => (c04_aux_seed_Phi0_hasDeriv p hp ξ).deriv]
  exact continuous_abs.rpow_const fun _ => Or.inr hp.le

theorem c04_aux_seed_Phi0_neg (p ξ : ℝ) : Phi0 p (-ξ) = -Phi0 p ξ := by
  unfold Phi0; rw [abs_neg]; ring

theorem c04_aux_seed_cut_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => 1 - chiPlus |ξ|) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge |x| 1 with hx | hx
  · have : (fun ξ : ℝ => 1 - chiPlus |ξ|) =ᶠ[𝓝 x] fun _ => 1 := by
      have : {ξ : ℝ | |ξ| < 1} ∈ 𝓝 x :=
        (isOpen_lt continuous_abs continuous_const).mem_nhds hx
      filter_upwards [this] with t ht
      rw [c04_aux_seed_chi_zero (le_of_lt ht), sub_zero]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have hx0 : x ≠ 0 := by intro h; rw [h, abs_zero] at hx; linarith
    exact contDiffAt_const.sub (c04_aux_seed_chi_smooth.contDiffAt.comp x (contDiffAt_abs hx0))

theorem c04_aux_seed_mlow_zero (p ξ : ℝ) (h : 2 ≤ |ξ|) : c04_m_low p ξ = 0 := by
  unfold c04_m_low; rw [c04_aux_seed_chi_one h]; simp

/-- Blueprint: lem:c04_seed_low_fourier.  `m_low = (1-χ₊(|ξ|)) e^{-iΦ₀(ξ)} ∈ C¹_c` with support in
`[-2,2]`, Hermitian, and `f_{0,low}'' = m_low^∨` (absolutely convergent, real-valued). -/
theorem c04_seed_low_fourier (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ContDiff ℝ 1 (c04_m_low p) ∧ HasCompactSupport (c04_m_low p) ∧
    tsupport (c04_m_low p) ⊆ Icc (-2) 2 ∧
    (∀ ξ, c04_m_low p (-ξ) = conj (c04_m_low p ξ)) ∧
    (∀ y : ℝ, Integrable (fun ξ : ℝ => c04_m_low p ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))) ∧
    (∀ y, ((iteratedDeriv 2 (c04_linear_seed_low p) y : ℝ) : ℂ) = invFourierT (c04_m_low p) y) ∧
    (∀ y, (invFourierT (c04_m_low p) y).im = 0) := by
  have hp0 : 0 < p := by linarith
  have hC1 : ContDiff ℝ 1 (c04_m_low p) := by
    unfold c04_m_low
    have h1 : ContDiff ℝ 1 (fun ξ : ℝ => ((1 - chiPlus |ξ| : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (c04_aux_seed_cut_smooth.of_le (by exact_mod_cast le_top))
    have h2 : ContDiff ℝ 1 (fun ξ : ℝ => Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) :=
      Complex.contDiff_exp.comp ((contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (c04_aux_seed_Phi0_C1 p hp0))).neg)
    exact h1.mul h2
  have hsupp : Function.support (c04_m_low p) ⊆ Icc (-2) 2 := by
    intro ξ hξ
    by_contra h
    apply hξ
    apply c04_aux_seed_mlow_zero
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hts : tsupport (c04_m_low p) ⊆ Icc (-2) 2 := closure_minimal hsupp isClosed_Icc
  have hcs : HasCompactSupport (c04_m_low p) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hherm : ∀ ξ, c04_m_low p (-ξ) = conj (c04_m_low p ξ) := by
    intro ξ
    unfold c04_m_low
    rw [abs_neg, c04_aux_seed_Phi0_neg, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  have hEc : ∀ y : ℝ, Continuous (fun ξ : ℝ => Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) :=
    fun y => by fun_prop
  have hint : ∀ y : ℝ, Integrable (fun ξ : ℝ =>
      c04_m_low p ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := fun y =>
    (hC1.continuous.mul (hEc y)).integrable_of_hasCompactSupport (hcs.mul_right)
  obtain ⟨-, -, hk, -, -, -⟩ := c04_seed_low_derivatives p hp hp1
  have hmain : ∀ y : ℝ, invFourierT (c04_m_low p) y =
      ((π⁻¹ * (∫ ξ in Ioi (0 : ℝ), ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re : ℝ) : ℂ) ∧
      iteratedDeriv 2 (c04_linear_seed_low p) y =
      π⁻¹ * (∫ ξ in Ioi (0 : ℝ), ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re := by
    intro y
    set f : ℝ → ℂ := fun ξ => c04_m_low p ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) with hf
    have hpos : ∀ ξ ∈ Ioi (0 : ℝ), f ξ = ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ := by
      intro ξ hξ
      simp only [hf, c04_m_low, c04_eiphase, abs_of_pos (show (0 : ℝ) < ξ from hξ)]
      rw [mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    have hneg : ∀ ξ, f (-ξ) = conj (f ξ) := by
      intro ξ
      simp only [hf, hherm, map_mul, ← Complex.exp_conj]
      congr 2
      simp [Complex.conj_ofReal]
    set J := ∫ ξ in Ioi (0 : ℝ), ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ with hJ
    have hJ' : ∫ ξ in Ioi (0 : ℝ), f ξ = J := setIntegral_congr_fun measurableSet_Ioi hpos
    have hleft : ∫ ξ in Iic (0 : ℝ), f ξ = conj J := by
      have e1 : ∫ ξ in Iic (0 : ℝ), f ξ = ∫ ξ in Iic (0 : ℝ), (fun x => conj (f x)) (-ξ) :=
        setIntegral_congr_fun measurableSet_Iic (fun ξ _ => by
          show f ξ = conj (f (-ξ)); rw [← hneg, neg_neg])
      rw [e1, integral_comp_neg_Iic (0 : ℝ) (fun x => conj (f x)), neg_zero, ← hJ']
      exact integral_conj
    have hfull : ∫ ξ, f ξ = J + conj J := by
      rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) (hint y).integrableOn
        (hint y).integrableOn, hleft, hJ', add_comm]
    refine ⟨?_, ?_⟩
    · show ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, f ξ = _
      rw [hfull, Complex.add_conj, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
      congr 1
      field_simp
    · have hint2 : IntegrableOn (fun ξ : ℝ => ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ)
          (Ioi 0) := ((hint y).integrableOn (s := Ioi 0)).congr_fun hpos measurableSet_Ioi
      have hpt : ∀ ξ ∈ Ioi (0 : ℝ), (1 - chiPlus ξ) *
          ((Complex.I * (ξ : ℂ)) ^ 2 * c04_eiphase p y ξ).re / ξ ^ 2 =
          -(((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re := by
        intro ξ hξ
        have hξ0 : ξ ≠ 0 := ne_of_gt hξ
        rw [show (Complex.I * (ξ : ℂ)) ^ 2 = ((-ξ ^ 2 : ℝ) : ℂ) by
          push_cast; rw [mul_pow, Complex.I_sq]; ring, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
        field_simp
      rw [(hk 2 le_rfl y).2, setIntegral_congr_fun measurableSet_Ioi hpt, integral_neg,
        ← c04_aux_seed_cplx_integral_re hint2]
      ring
  refine ⟨hC1, hcs, hts, hherm, hint, fun y => ?_, fun y => ?_⟩
  · rw [(hmain y).1, (hmain y).2]
  · rw [(hmain y).1, Complex.ofReal_im]

/-- Blueprint: lem:c04_seed_high_regular.  `f_{0,+} = -(2π)⁻¹ Osc[a_{-2}]` is `C^∞`,
`∂^j f_{0,+} = -(2π)⁻¹ Osc[(iξ)^j a_{-2}]`, and `f_{0,+} → 0` at infinity. -/
theorem c04_seed_high_regular (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p) ∧
    (∀ y, c04_linear_seed_plus p y =
      -((2 * π : ℝ) : ℂ)⁻¹ * c04_osc_integral p (fun ξ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) y) ∧
    (∀ (j : ℕ) (y : ℝ), iteratedDeriv j (c04_linear_seed_plus p) y =
      -((2 * π : ℝ) : ℂ)⁻¹ *
        c04_osc_integral p (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) y) ∧
    Tendsto (c04_linear_seed_plus p) (cocompact ℝ) (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, haint, hsym, -, -, -⟩ := c04_seed_integrable p hp hp1
  obtain ⟨hord, -⟩ := c04_osc_ordinary_integrals p hp0 hp1 (-2) _ hsym
  obtain ⟨-, -, hsm, hiter, -, -⟩ := c04_osc_parameter_derivatives p hp0 hp1 (-2) _ hsym
  have hf : c04_linear_seed_plus p = fun y => -((2 * π : ℝ) : ℂ)⁻¹ *
      c04_osc_integral p (fun ξ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) y := by
    funext y
    rw [(hord haint.integrableOn y).2]
    rfl
  refine ⟨?_, fun y => by rw [hf], fun j y => ?_, ?_⟩
  · rw [hf]; exact contDiff_const.mul hsm
  · rw [hf, iteratedDeriv_const_mul_field, hiter]
  · -- Riemann–Lebesgue
    set g : ℝ → ℂ := (Ioi (0 : ℝ)).indicator
      (fun ξ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) with hg
    have hRL := Real.tendsto_integral_exp_smul_cocompact g
    have hc : -(2 * π)⁻¹ ≠ (0 : ℝ) := by
      have : 0 < 2 * π := by positivity
      exact neg_ne_zero.mpr (inv_ne_zero this.ne')
    have hmap : Tendsto (fun y : ℝ => y * (-(2 * π)⁻¹)) (cocompact ℝ) (cocompact ℝ) :=
      (Homeomorph.mulRight₀ _ hc).isClosedEmbedding.tendsto_cocompact
    have h2 := (hRL.comp hmap).const_mul (-((2 * π : ℝ) : ℂ)⁻¹)
    rw [mul_zero] at h2
    refine h2.congr fun y => ?_
    simp only [Function.comp_apply]
    unfold c04_linear_seed_plus
    congr 1
    rw [hg, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext v
    simp only [indicator]
    split_ifs with hv
    · rw [Circle.smul_def, fourierChar_apply, smul_eq_mul, mul_comm, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      field_simp
      ring
    · simp

/-! ### The linear solution -/

/-- Blueprint: lem:c04_seed_decomposition.  Well-posedness and smoothness of the seed:
(1) convergence, `f_{0,+} = -(2π)⁻¹ Osc[χ₊ξ⁻²]`, smoothness, derivatives, `f_{0,+} → 0`;
(2) the formulas for `f_{0,low}` and its derivatives, `f_{0,low}'' = m_low^∨`;
(3) `f_{0,low} - W = 𝓘₁ + 𝓘₂`; (4) `f₀ = f_{0,low} + 2 Re f_{0,+}` is smooth. -/
theorem c04_seed_decomposition (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    -- (1)
    (∀ y, IntegrableOn (fun ξ : ℝ => (1 - Real.cos (y * ξ - Phi0 p ξ)) / ξ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun ξ : ℝ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * c04_eiphase p y ξ) (Ioi 0)) ∧
    (∀ y, c04_linear_seed_plus p y =
      -((2 * π : ℝ) : ℂ)⁻¹ * c04_osc_integral p (fun ξ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) y) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p) ∧
    (∀ (j : ℕ) (y : ℝ), iteratedDeriv j (c04_linear_seed_plus p) y =
      -((2 * π : ℝ) : ℂ)⁻¹ *
        c04_osc_integral p (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) y) ∧
    Tendsto (c04_linear_seed_plus p) (cocompact ℝ) (𝓝 0) ∧
    -- (2)
    (∀ y, IntegrableOn (fun ξ : ℝ =>
        (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2) (Ioi 0) ∧
      c04_linear_seed_low p y = -y / 2 + π⁻¹ * ∫ ξ in Ioi (0 : ℝ),
        (1 - ((1 - chiPlus ξ : ℝ) : ℂ) * c04_eiphase p y ξ).re / ξ ^ 2) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_low p) ∧
    (∀ y, IntegrableOn (fun ξ : ℝ => (1 - chiPlus ξ) * Real.sin (y * ξ - Phi0 p ξ) / ξ) (Ioi 0) ∧
      deriv (c04_linear_seed_low p) y = -1 / 2 + π⁻¹ * ∫ ξ in Ioi (0 : ℝ),
        (1 - chiPlus ξ) * Real.sin (y * ξ - Phi0 p ξ) / ξ) ∧
    (∀ (k : ℕ), 2 ≤ k → ∀ y,
      IntegrableOn (fun ξ : ℝ =>
        (1 - chiPlus ξ) * ((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re / ξ ^ 2) (Ioi 0) ∧
      iteratedDeriv k (c04_linear_seed_low p) y = -π⁻¹ * ∫ ξ in Ioi (0 : ℝ),
        (1 - chiPlus ξ) * ((Complex.I * (ξ : ℂ)) ^ k * c04_eiphase p y ξ).re / ξ ^ 2) ∧
    ContDiff ℝ 1 (c04_m_low p) ∧ HasCompactSupport (c04_m_low p) ∧
    (∀ y, ((iteratedDeriv 2 (c04_linear_seed_low p) y : ℝ) : ℂ) = invFourierT (c04_m_low p) y) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ M : ℝ, ∀ y, |iteratedDeriv k (c04_linear_seed_low p) y| ≤ M) ∧
    -- (3)
    (∀ y, IntegrableOn (fun ξ : ℝ =>
        Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_I1_symbol p ξ) (Ioi 0) ∧
      IntegrableOn (fun ξ : ℝ =>
        Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) (Ioi 0) ∧
      c04_linear_seed_low p y - corner y = c04_I1 p y + c04_I2 y) ∧
    -- (4)
    (∀ y, c04_linear_seed p y = c04_linear_seed_low p y + 2 * (c04_linear_seed_plus p y).re) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed p) := by
  obtain ⟨hint, -, -, -, -, -⟩ := c04_seed_integrable p hp hp1
  obtain ⟨hpsm, hposc, hpder, hptend⟩ := c04_seed_high_regular p hp hp1
  obtain ⟨hrep, hsum, -⟩ := c04_seed_low_representation p hp hp1
  obtain ⟨hlsm, hld1, hldk, -, -, hlbd⟩ := c04_seed_low_derivatives p hp hp1
  obtain ⟨hmC1, hmcs, -, -, -, hmF, -⟩ := c04_seed_low_fourier p hp hp1
  obtain ⟨-, -, -, hcorner⟩ := c04_seed_corner_decomposition p hp hp1
  have hf0 : c04_linear_seed p = fun y => c04_linear_seed_low p y + 2 * (c04_linear_seed_plus p y).re :=
    funext hsum
  refine ⟨hint, hposc, hpsm, hpder, hptend, hrep, hlsm, hld1, hldk, hmC1, hmcs, hmF,
    fun k hk => (hlbd k hk).elim fun C hC => ⟨C, hC.2⟩, hcorner,
    hsum, ?_⟩
  rw [hf0]
  exact hlsm.add (contDiff_const.mul (Complex.reCLM.contDiff.comp hpsm))

/-! ### Local copies of helpers (declared later in this file) -/

theorem c04_aux_I12_leibniz {𝔸 : Type*} [NormedCommRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] (f g : ℝ → 𝔸) (y : ℝ)
    (hy : 0 < y) (k : ℕ) (hf : ContDiffAt ℝ k f y) (hg : ContDiffAt ℝ k g y) (A B a b σ : ℝ)
    (hA : ∀ i, i ≤ k → ‖iteratedDeriv i f y‖ ≤ A * y ^ (a + i * σ))
    (hB : ∀ i, i ≤ k → ‖iteratedDeriv i g y‖ ≤ B * y ^ (b + i * σ)) :
    ‖iteratedDeriv k (f * g) y‖ ≤ 2 ^ k * (A * B) * y ^ (a + b + k * σ) := by
  rw [iteratedDeriv_mul hf hg]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ‖(k.choose i : 𝔸) * iteratedDeriv i f y * iteratedDeriv (k - i) g y‖ ≤
        (k.choose i : ℝ) * (A * B * y ^ (a + b + k * σ)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : y ^ (a + i * σ) * y ^ (b + ((k - i : ℕ) : ℝ) * σ) = y ^ (a + b + k * σ) := by
      rw [← rpow_add hy, Nat.cast_sub hik]; ring_nf
    calc ‖(k.choose i : 𝔸) * iteratedDeriv i f y * iteratedDeriv (k - i) g y‖
        ≤ ‖(k.choose i : 𝔸)‖ * ‖iteratedDeriv i f y‖ * ‖iteratedDeriv (k - i) g y‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (k.choose i : ℝ) * (A * y ^ (a + i * σ)) * (B * y ^ (b + ((k - i : ℕ) : ℝ) * σ)) := by
          have h1 : ‖(k.choose i : 𝔸)‖ ≤ (k.choose i : ℝ) := by
            have := Nat.norm_cast_le (α := 𝔸) (k.choose i); rwa [norm_one, mul_one] at this
          have h2 := hA i hik
          have h3 := hB (k - i) (Nat.sub_le k i)
          have hA0 : 0 ≤ A * y ^ (a + i * σ) := le_trans (norm_nonneg _) h2
          gcongr
      _ = (k.choose i : ℝ) * (A * B * y ^ (a + b + k * σ)) := by rw [← e]; ring
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), ‖(k.choose i : 𝔸) * iteratedDeriv i f y * iteratedDeriv (k - i) g y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (A * B * y ^ (a + b + k * σ)) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ k * (A * B) * y ^ (a + b + k * σ) := by
        rw [← Finset.sum_mul]
        have := Nat.sum_range_choose k
        have h : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by exact_mod_cast this
        rw [h]; ring

theorem c04_aux_I12_rpow_iter (r : ℝ) (k : ℕ) (y : ℝ) (hy : 0 < y) :
    |iteratedDeriv k (fun t : ℝ => t ^ r) y| = |(descPochhammer ℝ k).eval r| * y ^ (r - k) := by
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, abs_mul, abs_of_pos (rpow_pos_of_pos hy _)]

theorem c04_aux_I12_iteratedDeriv_re (F : ℝ → ℂ) (y : ℝ) (j : ℕ) (hF : ContDiffAt ℝ j F y) :
    iteratedDeriv j (fun t => (F t).re) y = (iteratedDeriv j F y).re := by
  have : (fun t => (F t).re) = Complex.reCLM ∘ F := rfl
  rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    Complex.reCLM.iteratedFDeriv_comp_left hF le_rfl]
  simp

/-- Kernel `(iξ)^k e^{iyξ} g(ξ)`. -/
def c04_aux_I12_K (g : ℝ → ℂ) (k : ℕ) (y ξ : ℝ) : ℂ :=
  (Complex.I * (ξ : ℂ)) ^ k * Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * g ξ

/-- `G_k(y) = ∫₀^∞ (iξ)^k e^{iyξ} g(ξ) dξ`. -/
def c04_aux_I12_G (g : ℝ → ℂ) (k : ℕ) (y : ℝ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), c04_aux_I12_K g k y ξ

theorem c04_aux_I12_K_hasDeriv (g : ℝ → ℂ) (k : ℕ) (y ξ : ℝ) :
    HasDerivAt (fun y => c04_aux_I12_K g k y ξ) (c04_aux_I12_K g (k + 1) y ξ) y := by
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * ((y * ξ : ℝ) : ℂ)) (Complex.I * (ξ : ℂ)) y := by
    have := ((hasDerivAt_id y).mul_const ξ).ofReal_comp
    simpa using this.const_mul Complex.I
  have h2 := ((h1.cexp).const_mul ((Complex.I * (ξ : ℂ)) ^ k)).mul_const (g ξ)
  unfold c04_aux_I12_K
  convert h2 using 1
  ring

theorem c04_aux_I12_K_norm (g : ℝ → ℂ) (k : ℕ) (y ξ : ℝ) (hξ : 0 < ξ) :
    ‖c04_aux_I12_K g k y ξ‖ = ξ ^ k * ‖g ξ‖ := by
  unfold c04_aux_I12_K
  rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hξ, mul_comm (Complex.I) _, Complex.norm_exp_ofReal_mul_I,
    mul_one]

theorem c04_aux_I12_K_meas (g : ℝ → ℂ) (hg : ContinuousOn g (Ioi 0)) (k : ℕ) (y : ℝ) :
    AEStronglyMeasurable (c04_aux_I12_K g k y) (volume.restrict (Ioi (0 : ℝ))) := by
  have hc : Continuous (fun ξ : ℝ =>
      (Complex.I * (ξ : ℂ)) ^ k * Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ))) := by fun_prop
  exact (hc.continuousOn.mul hg).aestronglyMeasurable measurableSet_Ioi

theorem c04_aux_I12_K_int (g : ℝ → ℂ) (hg : ContinuousOn g (Ioi 0)) (k : ℕ)
    (hk : IntegrableOn (fun ξ => ξ ^ k * ‖g ξ‖) (Ioi 0)) (y : ℝ) :
    IntegrableOn (c04_aux_I12_K g k y) (Ioi 0) :=
  hk.mono' (c04_aux_I12_K_meas g hg k y) (ae_restrict_of_forall_mem measurableSet_Ioi
    fun ξ hξ => (c04_aux_I12_K_norm g k y ξ hξ).le)

theorem c04_aux_I12_G_hasDeriv (g : ℝ → ℂ) (hg : ContinuousOn g (Ioi 0)) (k : ℕ)
    (h0 : IntegrableOn (fun ξ => ξ ^ k * ‖g ξ‖) (Ioi 0))
    (h1 : IntegrableOn (fun ξ => ξ ^ (k + 1) * ‖g ξ‖) (Ioi 0)) (y₀ : ℝ) :
    HasDerivAt (c04_aux_I12_G g k) (c04_aux_I12_G g (k + 1) y₀) y₀ := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun y ξ => c04_aux_I12_K g k y ξ) (F' := fun y ξ => c04_aux_I12_K g (k + 1) y ξ)
    (x₀ := y₀) (bound := fun ξ => ξ ^ (k + 1) * ‖g ξ‖) (s := univ)
    univ_mem (Eventually.of_forall fun y => c04_aux_I12_K_meas g hg k y)
    (c04_aux_I12_K_int g hg k h0 y₀) (c04_aux_I12_K_meas g hg (k + 1) y₀)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ y _ =>
      (c04_aux_I12_K_norm g (k + 1) y ξ hξ).le) h1
    (Eventually.of_forall fun ξ y _ => c04_aux_I12_K_hasDeriv g k y ξ)
  exact this.2

theorem c04_aux_I12_G_norm (g : ℝ → ℂ) (k : ℕ)
    (h0 : IntegrableOn (fun ξ => ξ ^ k * ‖g ξ‖) (Ioi 0)) (y : ℝ) :
    ‖c04_aux_I12_G g k y‖ ≤ ∫ ξ in Ioi (0 : ℝ), ξ ^ k * ‖g ξ‖ :=
  norm_integral_le_of_norm_le h0 (ae_restrict_of_forall_mem measurableSet_Ioi
    fun ξ hξ => (c04_aux_I12_K_norm g k y ξ hξ).le)

/-- Iterated derivatives of `G_0` given moments up to order `N`. -/
theorem c04_aux_I12_G_iter (g : ℝ → ℂ) (hg : ContinuousOn g (Ioi 0)) (N : ℕ)
    (hN : ∀ k ≤ N, IntegrableOn (fun ξ => ξ ^ k * ‖g ξ‖) (Ioi 0)) :
    ∀ k ≤ N, iteratedDeriv k (c04_aux_I12_G g 0) = c04_aux_I12_G g k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [iteratedDeriv_succ, ih (by omega)]
    funext y
    exact (c04_aux_I12_G_hasDeriv g hg k (hN k (by omega)) (hN (k + 1) hk) y).deriv

theorem c04_aux_I12_G_contDiff (g : ℝ → ℂ) (hg : ContinuousOn g (Ioi 0)) (N : ℕ)
    (hN : ∀ k ≤ N + 1, IntegrableOn (fun ξ => ξ ^ k * ‖g ξ‖) (Ioi 0)) :
    ContDiff ℝ N (c04_aux_I12_G g 0) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m hm => ?_
  have hm' : m ≤ N := by exact_mod_cast hm
  rw [c04_aux_I12_G_iter g hg (N + 1) hN m (by omega)]
  exact fun y => (c04_aux_I12_G_hasDeriv g hg m (hN m (by omega)) (hN (m + 1) (by omega))
    y).differentiableAt

theorem c04_aux_I12_G_contDiff_top (g : ℝ → ℂ) (hg : ContinuousOn g (Ioi 0))
    (hN : ∀ k : ℕ, IntegrableOn (fun ξ => ξ ^ k * ‖g ξ‖) (Ioi 0)) :
    ContDiff ℝ (⊤ : ℕ∞) (c04_aux_I12_G g 0) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [c04_aux_I12_G_iter g hg m (fun k _ => hN k) m le_rfl]
  exact fun y => (c04_aux_I12_G_hasDeriv g hg m (hN m) (hN (m + 1)) y).differentiableAt


/-! ### `𝓘₂` -/

/-- `c_L = ∂^L (χ₊/ξ²)` as a complex function. -/
def c04_aux_I12_cL (L : ℕ) (ξ : ℝ) : ℂ :=
  ((iteratedDeriv L (fun ξ : ℝ => chiPlus ξ / ξ ^ 2) ξ : ℝ) : ℂ)

theorem c04_aux_I12_cL_zero (L : ℕ) {ξ : ℝ} (hξ : ξ < 1) : c04_aux_I12_cL L ξ = 0 := by
  unfold c04_aux_I12_cL
  have hev : (fun ξ : ℝ => chiPlus ξ / ξ ^ 2) =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hξ] with t ht
    rw [c04_aux_seed_chi_zero (le_of_lt ht), zero_div]
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
  split_ifs <;> simp

theorem c04_aux_I12_cL_hasDeriv (L : ℕ) (ξ : ℝ) :
    HasDerivAt (c04_aux_I12_cL L) (c04_aux_I12_cL (L + 1) ξ) ξ := by
  have h := (c04_aux_seed_a2_smooth.differentiable_iteratedDeriv L
    (by exact_mod_cast ENat.natCast_lt_top L)) ξ
  have h2 := h.hasDerivAt.ofReal_comp
  unfold c04_aux_I12_cL
  rw [iteratedDeriv_succ]
  exact h2

theorem c04_aux_I12_cL_cont (L : ℕ) : Continuous (c04_aux_I12_cL L) :=
  continuous_iff_continuousAt.mpr fun ξ => (c04_aux_I12_cL_hasDeriv L ξ).continuousAt

theorem c04_aux_I12_cL_bound (L : ℕ) : ∃ C > (0 : ℝ), ∀ ξ : ℝ, 1 ≤ ξ →
    ‖c04_aux_I12_cL L ξ‖ ≤ C * ξ ^ (-2 - (L : ℝ)) := by
  obtain ⟨C, hC, h⟩ := c04_aux_seed_a2_iter L
  exact ⟨C, hC, fun ξ hξ => by
    unfold c04_aux_I12_cL; rw [Complex.norm_real, Real.norm_eq_abs]; exact h ξ hξ⟩

theorem c04_aux_I12_cL_moment (L : ℕ) : ∀ k ≤ L,
    IntegrableOn (fun ξ => ξ ^ k * ‖c04_aux_I12_cL L ξ‖) (Ioi 0) := by
  intro k hk
  obtain ⟨C, hC, h⟩ := c04_aux_I12_cL_bound L
  have hmaj : IntegrableOn (fun ξ : ℝ => C * (Ici (1 : ℝ)).indicator (fun ξ => ξ ^ (-2 : ℝ)) ξ)
      (Ioi 0) := by
    refine Integrable.integrableOn (Integrable.const_mul ?_ C)
    rw [integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  refine hmaj.mono' (by
    have : Continuous (fun ξ => ξ ^ k * ‖c04_aux_I12_cL L ξ‖) :=
      (continuous_pow k).mul (c04_aux_I12_cL_cont L).norm
    exact this.aestronglyMeasurable) (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ hξ => ?_)
  have hξ0 : (0 : ℝ) < ξ := hξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hξ0.le _) (norm_nonneg _))]
  rcases lt_or_ge ξ 1 with h1 | h1
  · rw [c04_aux_I12_cL_zero L h1, norm_zero, mul_zero]
    exact mul_nonneg hC.le (indicator_nonneg (fun x (hx : x ∈ Ici (1 : ℝ)) => rpow_nonneg (le_trans zero_le_one hx) _) _)
  · rw [indicator_of_mem (show ξ ∈ Ici (1 : ℝ) from h1)]
    calc ξ ^ k * ‖c04_aux_I12_cL L ξ‖ ≤ ξ ^ k * (C * ξ ^ (-2 - (L : ℝ))) :=
          mul_le_mul_of_nonneg_left (h ξ h1) (by positivity)
      _ = C * ξ ^ ((k : ℝ) + (-2 - (L : ℝ))) := by
          rw [rpow_add hξ0, rpow_natCast]; ring
      _ ≤ C * ξ ^ (-2 : ℝ) := by
          refine mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le h1 ?_) hC.le
          have : (k : ℝ) ≤ L := by exact_mod_cast hk
          linarith

theorem c04_aux_I12_G_cL_ibp (L : ℕ) (y : ℝ) (hy : y ≠ 0) :
    c04_aux_I12_G (c04_aux_I12_cL L) 0 y =
      (Complex.I / (y : ℂ)) * c04_aux_I12_G (c04_aux_I12_cL (L + 1)) 0 y := by
  set e : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) with he
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hIy : Complex.I * (y : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hyc
  set v : ℝ → ℂ := fun ξ => e ξ / (Complex.I * (y : ℂ)) with hv
  have hed : ∀ ξ : ℝ, HasDerivAt e (Complex.I * y * e ξ) ξ := by
    intro ξ
    have h1 : HasDerivAt (fun ξ : ℝ => Complex.I * ((y * ξ : ℝ) : ℂ)) (Complex.I * (y : ℂ)) ξ := by
      have := ((hasDerivAt_id ξ).const_mul y).ofReal_comp
      simpa using this.const_mul Complex.I
    exact h1.cexp.congr_deriv (by ring)
  have hvd : ∀ ξ : ℝ, HasDerivAt v (e ξ) ξ := by
    intro ξ
    have := (hed ξ).div_const (Complex.I * (y : ℂ))
    exact this.congr_deriv (by field_simp)
  have hne : ∀ ξ, ‖e ξ‖ = 1 := fun ξ => by
    simp only [he]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hnv : ∀ ξ, ‖v ξ‖ = |y|⁻¹ := fun ξ => by
    simp only [hv]; rw [norm_div, hne, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, one_div]
  have hK0 : ∀ (g : ℝ → ℂ) (ξ : ℝ), c04_aux_I12_K g 0 y ξ = g ξ * e ξ := fun g ξ => by
    simp [c04_aux_I12_K, he, mul_comm]
  have hint : ∀ L', IntegrableOn (fun ξ => c04_aux_I12_cL L' ξ * e ξ) (Ioi 0) := fun L' => by
    have := c04_aux_I12_K_int (c04_aux_I12_cL L') (c04_aux_I12_cL_cont L').continuousOn 0
      (c04_aux_I12_cL_moment L' 0 (Nat.zero_le _)) y
    refine this.congr_fun (fun ξ _ => hK0 _ ξ) measurableSet_Ioi
  obtain ⟨C, hC, hb⟩ := c04_aux_I12_cL_bound L
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := c04_aux_I12_cL L) (u' := c04_aux_I12_cL (L + 1)) (v := v) (v' := e)
    (fun ξ _ => c04_aux_I12_cL_hasDeriv L ξ) (fun ξ _ => hvd ξ) (hint L)
    (by
      have := (hint (L + 1)).div_const (Complex.I * (y : ℂ))
      refine IntegrableOn.congr_fun this (fun ξ _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply, hv]; ring)
    (by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ξ hξ
      simp [c04_aux_I12_cL_zero L hξ.2])
    (by
      have ht : Tendsto (fun ξ : ℝ => C * |y|⁻¹ * ξ ^ (-(2 + (L : ℝ)))) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (y := 2 + (L : ℝ)) (by positivity)).const_mul (C * |y|⁻¹)
        simpa using this
      refine squeeze_zero_norm' ?_ ht
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with ξ hξ
      rw [Pi.mul_apply, norm_mul, hnv, neg_add']
      have := hb ξ hξ
      calc ‖c04_aux_I12_cL L ξ‖ * |y|⁻¹ ≤ (C * ξ ^ (-2 - (L : ℝ))) * |y|⁻¹ :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring)
  unfold c04_aux_I12_G
  simp_rw [hK0]
  rw [key]
  have : ∫ ξ in Ioi (0 : ℝ), c04_aux_I12_cL (L + 1) ξ * v ξ =
      (Complex.I * (y : ℂ))⁻¹ * ∫ ξ in Ioi (0 : ℝ), c04_aux_I12_cL (L + 1) ξ * e ξ := by
    rw [← integral_const_mul]
    congr 1; funext ξ; simp only [hv]; ring
  rw [this]
  field_simp
  rw [Complex.I_sq]; ring


theorem c04_aux_I12_G_cL_rep (L : ℕ) (y : ℝ) (hy : y ≠ 0) :
    c04_aux_I12_G (c04_aux_I12_cL 0) 0 y =
      (Complex.I / (y : ℂ)) ^ L * c04_aux_I12_G (c04_aux_I12_cL L) 0 y := by
  induction L with
  | zero => simp
  | succ L ih => rw [ih, c04_aux_I12_G_cL_ibp L y hy, pow_succ]; ring

theorem c04_aux_I12_I2_eq : c04_I2 = fun y => π⁻¹ * (c04_aux_I12_G (c04_aux_I12_cL 0) 0 y).re := by
  funext y
  unfold c04_I2 c04_aux_I12_G
  congr 3
  funext ξ
  simp only [c04_aux_I12_K, c04_aux_I12_cL, iteratedDeriv_zero, pow_zero, one_mul]

theorem c04_aux_I12_I2_even (y : ℝ) : c04_I2 (-y) = c04_I2 y := by
  have h : (∫ ξ in Ioi (0 : ℝ), Complex.exp (Complex.I * (((-y) * ξ : ℝ) : ℂ)) *
      ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) = conj (∫ ξ in Ioi (0 : ℝ),
        Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) := by
    rw [← integral_conj]
    congr 1
    funext ξ
    rw [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    congr 2
    push_cast; ring
  unfold c04_I2
  rw [h, Complex.conj_re]

theorem c04_aux_I12_I2_contDiffAt (n : ℕ) (y : ℝ) (hy : y ≠ 0) : ContDiffAt ℝ n c04_I2 y := by
  have hev : c04_I2 =ᶠ[𝓝 y] fun t => π⁻¹ * ((Complex.I / (t : ℂ)) ^ (n + 1) *
      c04_aux_I12_G (c04_aux_I12_cL (n + 1)) 0 t).re := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show y ∈ ({0} : Set ℝ)ᶜ from hy)] with t ht
    simp only [c04_aux_I12_I2_eq]
    rw [c04_aux_I12_G_cL_rep (n + 1) t ht]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hG := (c04_aux_I12_G_contDiff (c04_aux_I12_cL (n + 1)) (c04_aux_I12_cL_cont _).continuousOn n
    (c04_aux_I12_cL_moment (n + 1))).contDiffAt (x := y)
  have hd : ContDiffAt ℝ n (fun t : ℝ => (t : ℂ)) y := Complex.ofRealCLM.contDiff.contDiffAt
  have hf : ContDiffAt ℝ n (fun t : ℝ => (Complex.I / (t : ℂ)) ^ (n + 1)) y :=
    by
      have h0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy
      have := ((contDiffAt_const (c := Complex.I)).mul (hd.inv h0)).pow (n + 1)
      convert this using 2 with t
      simp [div_eq_mul_inv]
  exact contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp y (hf.mul hG))

theorem c04_aux_I12_I2_pos_bound (j : ℕ) (N : ℝ) (_hN : 0 ≤ N) : ∃ C > (0 : ℝ), ∀ y : ℝ, 1 ≤ y →
    |iteratedDeriv j c04_I2 y| ≤ C * y ^ (-N) := by
  set L : ℕ := j + ⌈N⌉₊ + 1 with hL
  set G := c04_aux_I12_G (c04_aux_I12_cL L) 0 with hG
  set r : ℝ := -(L : ℝ) with hr
  set f : ℝ → ℂ := fun t => ((π⁻¹ : ℝ) : ℂ) * (Complex.I ^ L * ((t ^ r : ℝ) : ℂ)) with hf
  have hmom := c04_aux_I12_cL_moment L
  have hGc : ContDiff ℝ (L - 1 : ℕ) G :=
    c04_aux_I12_G_contDiff _ (c04_aux_I12_cL_cont L).continuousOn (L - 1)
      (fun k hk => hmom k (by omega))
  have hGi : ∀ i ≤ L, iteratedDeriv i G = c04_aux_I12_G (c04_aux_I12_cL L) i :=
    c04_aux_I12_G_iter _ (c04_aux_I12_cL_cont L).continuousOn L hmom
  set M : ℕ → ℝ := fun i => ∫ ξ in Ioi (0 : ℝ), ξ ^ i * ‖c04_aux_I12_cL L ξ‖ with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => setIntegral_nonneg measurableSet_Ioi
    fun ξ (hξ : 0 < ξ) => mul_nonneg (pow_nonneg hξ.le _) (norm_nonneg _)
  set B : ℝ := ∑ i ∈ Finset.range (j + 1), M i with hB
  set P : ℕ → ℝ := fun i => |(descPochhammer ℝ i).eval r| with hP
  set A : ℝ := π⁻¹ * ∑ i ∈ Finset.range (j + 1), P i with hA
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => hM0 i
  have hA0 : 0 ≤ A := mul_nonneg (inv_nonneg.mpr pi_pos.le)
    (Finset.sum_nonneg fun i _ => abs_nonneg _)
  refine ⟨2 ^ j * (A * B) + 1, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hev : c04_I2 =ᶠ[𝓝 y] fun t => ((f * G) t).re := by
    filter_upwards [Ioi_mem_nhds hy0] with t (ht : 0 < t)
    rw [c04_aux_I12_I2_eq]
    simp only [c04_aux_I12_G_cL_rep L t ht.ne', Pi.mul_apply, hf]
    rw [show ((t ^ r : ℝ) : ℂ) = ((t : ℂ) ^ L)⁻¹ by
      rw [hr, rpow_neg ht.le, rpow_natCast]; push_cast; rfl]
    rw [← Complex.re_ofReal_mul, div_pow]
    congr 1; ring
  have hfc : ∀ i : ℕ, ContDiffAt ℝ i (fun t : ℝ => t ^ r) y := fun i =>
    contDiffAt_rpow_const_of_ne hy0.ne'
  have hfC : ContDiffAt ℝ j f y := by
    have := (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hfc j))
    exact contDiffAt_const.mul (contDiffAt_const.mul this)
  have hGC : ContDiffAt ℝ j G y := (hGc.of_le (by exact_mod_cast (show j ≤ L - 1 by omega))).contDiffAt
  rw [hev.iteratedDeriv_eq, c04_aux_I12_iteratedDeriv_re (f * G) y j (hfC.mul hGC)]
  have hlb := c04_aux_I12_leibniz f G y hy0 j hfC hGC A B r 0 0 (fun i hi => ?_) (fun i hi => ?_)
  · simp only [mul_zero, add_zero] at hlb
    refine (Complex.abs_re_le_norm _).trans (hlb.trans ?_)
    have h1 : y ^ r ≤ y ^ (-N) := by
      refine rpow_le_rpow_of_exponent_le hy ?_
      have : N ≤ (⌈N⌉₊ : ℝ) := Nat.le_ceil N
      rw [hr, hL]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have : 0 ≤ 2 ^ j * (A * B) := by positivity
    calc 2 ^ j * (A * B) * y ^ r ≤ 2 ^ j * (A * B) * y ^ (-N) := mul_le_mul_of_nonneg_left h1 this
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · rw [mul_zero, add_zero]
    have e1 : iteratedDeriv i f y = ((π⁻¹ : ℝ) : ℂ) * (Complex.I ^ L *
        ((iteratedDeriv i (fun t : ℝ => t ^ r) y : ℝ) : ℂ)) := by
      rw [hf, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
        c04_aux_seed_ofReal_iter _ _ _ (hfc i)]
    rw [e1, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr pi_pos),
      c04_aux_I12_rpow_iter r i y hy0, hA, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr pi_pos.le)
    have hPi : P i ≤ ∑ i ∈ Finset.range (j + 1), P i :=
      Finset.single_le_sum (f := P) (fun k _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    have hyr : y ^ (r - i) ≤ y ^ r := rpow_le_rpow_of_exponent_le hy (by
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    exact mul_le_mul hPi hyr (by positivity) (le_trans (abs_nonneg _) hPi)
  · rw [mul_zero, add_zero, rpow_zero, mul_one, hGi i (by omega)]
    refine (c04_aux_I12_G_norm _ i (hmom i (by omega)) y).trans ?_
    exact Finset.single_le_sum (f := M) (fun k _ => hM0 k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

/-- Blueprint: lem:c04_I2_bound.  `𝓘₂ ∈ C^∞(ℝ∖{0})` and `|∂^j 𝓘₂(y)| ≤ C_{j,N} |y|^{-N}` for
`|y| ≥ 1`. -/
theorem c04_I2_bound :
    ContDiffOn ℝ (⊤ : ℕ∞) c04_I2 {0}ᶜ ∧
    ∀ (j : ℕ) (N : ℝ), 0 ≤ N → ∃ C > (0 : ℝ), ∀ y : ℝ, 1 ≤ |y| →
      |iteratedDeriv j c04_I2 y| ≤ C * |y| ^ (-N) := by
  refine ⟨?_, fun j N hN => ?_⟩
  · refine contDiffOn_infty.mpr fun n y hy => ?_
    exact (c04_aux_I12_I2_contDiffAt n y hy).contDiffWithinAt
  · obtain ⟨C, hC, h⟩ := c04_aux_I12_I2_pos_bound j N hN
    refine ⟨C, hC, fun y hy => ?_⟩
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0] at hy ⊢; exact h y hy
    · rw [abs_of_neg h0] at hy ⊢
      have hc := iteratedDeriv_comp_neg j c04_I2 y
      rw [show (fun x => c04_I2 (-x)) = c04_I2 from funext c04_aux_I12_I2_even] at hc
      rw [hc, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact h (-y) hy


/-- Repeated integration by parts on `[ρ,3]` plus a direct bound on `(0,ρ]`, `ρ = 1/|y|`. -/
theorem c04_aux_I12_ibp_bound (H : ℕ → ℝ → ℂ) (m : ℕ) (a : ℝ) (A : ℕ → ℝ)
    (ha : 0 < a) (ham : a < m) (hA : ∀ k, 0 ≤ A k)
    (hd : ∀ k < m, ∀ ξ ∈ Ioo (0 : ℝ) 4, HasDerivAt (H k) (H (k + 1) ξ) ξ)
    (hcm : ContinuousOn (H m) (Ioo 0 4))
    (h3 : ∀ k < m, H k 3 = 0)
    (hb : ∀ k ≤ m, ∀ ξ ∈ Ioc (0 : ℝ) 3, ‖H k ξ‖ ≤ A k * ξ ^ (a - 1 - k)) :
    ∃ C > (0 : ℝ), ∀ y : ℝ, 1 ≤ |y| →
      ‖∫ ξ in (0 : ℝ)..3, Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * H 0 ξ‖ ≤
        C * |y| ^ (-a) := by
  have hcont : ∀ k ≤ m, ContinuousOn (H k) (Ioo 0 4) := by
    intro k hk
    rcases eq_or_lt_of_le hk with h | h
    · rw [h]; exact hcm
    · exact fun ξ hξ => (hd k h ξ hξ).continuousAt.continuousWithinAt
  set S : ℝ := ∑ k ∈ Finset.range (m + 1), A k with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => hA k
  have hAS : ∀ k ≤ m, A k ≤ S := fun k hk =>
    Finset.single_le_sum (f := A) (fun k _ => hA k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hma : 0 < (m : ℝ) - a := by linarith
  set D : ℕ → ℝ := fun n => n * S + A m / ((m : ℝ) - a) with hD
  refine ⟨A 0 / a + D m + 1, by
    have : 0 ≤ D m := by simp only [hD]; have := hA m; positivity
    have := hA 0; positivity, fun y hy => ?_⟩
  set Y : ℝ := |y| with hYdef
  have hY0 : 0 < Y := by linarith
  have hy0 : y ≠ 0 := by intro h; rw [hYdef, h, abs_zero] at hy; linarith
  set ρ : ℝ := Y⁻¹ with hρ
  have hρ0 : 0 < ρ := inv_pos.mpr hY0
  have hρ1 : ρ ≤ 1 := inv_le_one_of_one_le₀ hy
  have hρpow : ∀ s : ℝ, ρ ^ s = Y ^ (-s) := fun s => by
    rw [hρ, inv_rpow hY0.le, rpow_neg hY0.le]
  set e : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) with he
  have hne : ∀ ξ, ‖e ξ‖ = 1 := fun ξ => by
    simp only [he]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hec : Continuous e := by simp only [he]; fun_prop
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
  set v : ℝ → ℂ := fun ξ => e ξ / (Complex.I * (y : ℂ)) with hv
  have hvd : ∀ ξ : ℝ, HasDerivAt v (e ξ) ξ := by
    intro ξ
    have h1 : HasDerivAt (fun ξ : ℝ => Complex.I * ((y * ξ : ℝ) : ℂ)) (Complex.I * (y : ℂ)) ξ := by
      have := ((hasDerivAt_id ξ).const_mul y).ofReal_comp
      simpa using this.const_mul Complex.I
    have := (h1.cexp.congr_deriv (by ring : _ = Complex.I * y * e ξ)).div_const
      (Complex.I * (y : ℂ))
    exact this.congr_deriv (by field_simp)
  have hnv : ∀ ξ, ‖v ξ‖ = Y⁻¹ := fun ξ => by
    simp only [hv]; rw [norm_div, hne, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, one_div]
  have hsub : ∀ ξ ∈ uIcc ρ 3, ξ ∈ Ioo (0 : ℝ) 4 := fun ξ hξ => by
    rw [uIcc_of_le (by linarith)] at hξ; exact ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  set J : ℕ → ℂ := fun k => ∫ ξ in ρ..3, e ξ * H k ξ with hJ
  -- base case
  have hbase : ‖J m‖ ≤ D 0 * Y ^ ((m : ℝ) - a) := by
    have hint : IntervalIntegrable (fun ξ : ℝ => A m * ξ ^ (a - 1 - m)) volume ρ 3 := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.mul (fun ξ hξ => ?_)
      exact (continuousAt_rpow_const _ _ (Or.inl (hsub ξ hξ).1.ne')).continuousWithinAt
    refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun ξ hξ => ?_) hint).trans ?_
    · rw [norm_mul, hne, one_mul]
      exact hb m le_rfl ξ ⟨lt_trans hρ0 hξ.1, hξ.2⟩
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le (by linarith)]; exact fun h => by linarith [h.1]⟩)]
      have e1 : a - 1 - (m : ℝ) + 1 = -((m : ℝ) - a) := by ring
      rw [e1, hρpow, neg_neg]
      simp only [hD, Nat.cast_zero, zero_mul, zero_add]
      have h3p : 0 ≤ (3 : ℝ) ^ (-((m : ℝ) - a)) := by positivity
      have key : ∀ x z : ℝ, 0 ≤ x →
          A m * ((x - z) / -((m : ℝ) - a)) ≤ A m / ((m : ℝ) - a) * z := by
        intro x z hx
        calc A m * ((x - z) / -((m : ℝ) - a)) = A m * (z - x) / ((m : ℝ) - a) := by
              rw [div_neg, ← neg_div, neg_sub, mul_div_assoc]
          _ ≤ A m * z / ((m : ℝ) - a) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (hA m)) hma.le
          _ = _ := by ring
      exact key _ _ h3p
  have hstep : ∀ k < m, ‖J k‖ ≤ A k * Y ^ ((k : ℝ) - a) + Y⁻¹ * ‖J (k + 1)‖ := by
    intro k hk
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ρ) (b := 3)
      (u := H k) (u' := H (k + 1)) (v := v) (v' := e)
      (fun ξ hξ => hd k hk ξ (hsub ξ hξ)) (fun ξ _ => hvd ξ)
      (((hcont (k + 1) (by omega)).mono (fun ξ hξ => hsub ξ hξ)).intervalIntegrable)
      (hec.intervalIntegrable _ _)
    have eJ : J k = -(H k ρ * v ρ) - (Complex.I * (y : ℂ))⁻¹ * J (k + 1) := by
      simp only [hJ]
      rw [show (∫ ξ in ρ..3, e ξ * H k ξ) = ∫ ξ in ρ..3, H k ξ * e ξ by
        congr 1; funext ξ; ring, hibp, h3 k hk, zero_mul, zero_sub,
        ← intervalIntegral.integral_const_mul]
      congr 2; funext ξ; simp only [hv]; ring
    rw [eJ]
    have hnI : ‖(Complex.I * (y : ℂ))⁻¹‖ = Y⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, hnv, hnI]
    refine add_le_add ?_ le_rfl
    have hH := hb k hk.le ρ ⟨hρ0, by linarith⟩
    rw [hρpow] at hH
    calc ‖H k ρ‖ * Y⁻¹ ≤ A k * Y ^ (-(a - 1 - k)) * Y⁻¹ :=
          mul_le_mul_of_nonneg_right hH (inv_nonneg.mpr hY0.le)
      _ = A k * Y ^ ((k : ℝ) - a) := by
          rw [show -(a - 1 - (k : ℝ)) = ((k : ℝ) - a) + 1 by ring, rpow_add_one hY0.ne']
          field_simp
  have hdown : ∀ n ≤ m, ‖J (m - n)‖ ≤ D n * Y ^ (((m - n : ℕ) : ℝ) - a) := by
    intro n
    induction n with
    | zero => intro _; simpa using hbase
    | succ n ih =>
      intro hn
      have hk : m - (n + 1) < m := by omega
      have hk1 : m - (n + 1) + 1 = m - n := by omega
      have h1 := hstep _ hk
      rw [hk1] at h1
      have h2 := ih (by omega)
      set k := m - (n + 1) with hkdef
      have ecast : (((m - n : ℕ) : ℝ) - a) = ((k : ℝ) - a) + 1 := by
        rw [← hk1]; push_cast; ring
      rw [ecast, rpow_add_one hY0.ne'] at h2
      have hYk : 0 ≤ Y ^ ((k : ℝ) - a) := by positivity
      have hAk := hAS k (by omega)
      calc ‖J k‖ ≤ A k * Y ^ ((k : ℝ) - a) + Y⁻¹ * ‖J (m - n)‖ := h1
        _ ≤ A k * Y ^ ((k : ℝ) - a) + Y⁻¹ * (D n * (Y ^ ((k : ℝ) - a) * Y)) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hY0.le))
        _ = (A k + D n) * Y ^ ((k : ℝ) - a) := by field_simp
        _ ≤ D (n + 1) * Y ^ ((k : ℝ) - a) := by
            refine mul_le_mul_of_nonneg_right ?_ hYk
            simp only [hD]; push_cast; linarith
  have hJ0 : ‖J 0‖ ≤ D m * Y ^ (-a) := by
    have := hdown m le_rfl
    simpa using this
  -- the piece near `0`
  have hg0 : IntervalIntegrable (fun ξ : ℝ => A 0 * ξ ^ (a - 1)) volume 0 ρ :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < a - 1)).const_mul (A 0)
  have hsub0 : uIoc (0 : ℝ) ρ ⊆ Ioo 0 4 := by
    rw [uIoc_of_le hρ0.le]; exact fun ξ hξ => ⟨hξ.1, by linarith [hξ.2]⟩
  have hb0 : ∀ ξ ∈ uIoc (0 : ℝ) ρ, ‖e ξ * H 0 ξ‖ ≤ A 0 * ξ ^ (a - 1) := by
    intro ξ hξ
    rw [uIoc_of_le hρ0.le] at hξ
    rw [norm_mul, hne, one_mul]
    have := hb 0 (Nat.zero_le _) ξ ⟨hξ.1, by linarith [hξ.2]⟩
    simpa using this
  have hI0 : IntervalIntegrable (fun ξ => e ξ * H 0 ξ) volume 0 ρ := by
    refine hg0.mono_fun' ?_ (ae_restrict_of_forall_mem measurableSet_uIoc hb0)
    exact (hec.continuousOn.mul ((hcont 0 (Nat.zero_le _)).mono hsub0)).aestronglyMeasurable
      measurableSet_uIoc
  have hIJ : IntervalIntegrable (fun ξ => e ξ * H 0 ξ) volume ρ 3 :=
    ContinuousOn.intervalIntegrable (hec.continuousOn.mul
      ((hcont 0 (Nat.zero_le _)).mono (fun ξ hξ => hsub ξ hξ)))
  have hnear : ‖∫ ξ in (0 : ℝ)..ρ, e ξ * H 0 ξ‖ ≤ A 0 / a * Y ^ (-a) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hρ0.le
      (Eventually.of_forall fun ξ hξ => hb0 ξ (by rw [uIoc_of_le hρ0.le]; exact hξ)) hg0).trans
      (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      sub_add_cancel, zero_rpow ha.ne', sub_zero, hρpow]
    ring
  show ‖∫ ξ in (0 : ℝ)..3, e ξ * H 0 ξ‖ ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hIJ]
  refine (norm_add_le _ _).trans ?_
  have hYa : 0 ≤ Y ^ (-a) := by positivity
  calc _ ≤ A 0 / a * Y ^ (-a) + D m * Y ^ (-a) := add_le_add hnear hJ0
    _ ≤ (A 0 / a + D m + 1) * Y ^ (-a) := by nlinarith


theorem c04_aux_I12_Phi0_contDiffAt (p : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Phi0 p) ξ := by
  have hev : Phi0 p =ᶠ[𝓝 ξ] fun t => t * t ^ p / (p + 1) := by
    filter_upwards [Ioi_mem_nhds hξ] with t (ht : 0 < t)
    unfold Phi0; rw [abs_of_pos ht]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (contDiffAt_id.mul (contDiffAt_rpow_const_of_ne hξ.ne')).div_const _

/-- `E(ξ) = e^{-iΦ₀(ξ)}`. -/
def c04_aux_I12_E (p ξ : ℝ) : ℂ := Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))

/-- `Q(ξ) = -i|ξ|^p`, so that `E' = Q E`. -/
def c04_aux_I12_Q (p ξ : ℝ) : ℂ := -(Complex.I * ((|ξ| ^ p : ℝ) : ℂ))

theorem c04_aux_I12_E_contDiffAt (p : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (c04_aux_I12_E p) ξ := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => ((Phi0 p t : ℝ) : ℂ)) ξ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ξ (c04_aux_I12_Phi0_contDiffAt p hξ)
  exact Complex.contDiff_exp.contDiffAt.comp ξ (contDiffAt_const.mul h1).neg

theorem c04_aux_I12_E_norm (p ξ : ℝ) : ‖c04_aux_I12_E p ξ‖ = 1 := by
  unfold c04_aux_I12_E
  rw [show -(Complex.I * (Phi0 p ξ : ℂ)) = ((-Phi0 p ξ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem c04_aux_I12_E_deriv (p : ℝ) (hp : 0 < p) :
    deriv (c04_aux_I12_E p) = c04_aux_I12_Q p * c04_aux_I12_E p := by
  funext ξ
  have h : HasDerivAt (c04_aux_I12_E p) (Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) *
      -(Complex.I * ((|ξ| ^ p : ℝ) : ℂ))) ξ :=
    ((c04_aux_seed_Phi0_hasDeriv p hp ξ).ofReal_comp.const_mul Complex.I).neg.cexp
  rw [Pi.mul_apply, h.deriv]
  unfold c04_aux_I12_E c04_aux_I12_Q; ring

theorem c04_aux_I12_Q_contDiffAt (p : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (c04_aux_I12_Q p) ξ := by
  have hev : c04_aux_I12_Q p =ᶠ[𝓝 ξ] fun t => -Complex.I * ((t ^ p : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hξ] with t (ht : 0 < t)
    unfold c04_aux_I12_Q; rw [abs_of_pos ht]; ring
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact contDiffAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ (contDiffAt_rpow_const_of_ne hξ.ne'))

/-- Derivative bounds for `c t^r` (complex constant `c`). -/
theorem c04_aux_I12_rpow_bd (c : ℂ) (r : ℝ) (n : ℕ) : ∃ A ≥ (0 : ℝ), ∀ i ≤ n, ∀ ξ : ℝ, 0 < ξ →
    ‖iteratedDeriv i (fun t : ℝ => c * ((t ^ r : ℝ) : ℂ)) ξ‖ ≤ A * ξ ^ (r + i * (-1)) := by
  set P : ℕ → ℝ := fun i => |(descPochhammer ℝ i).eval r| with hP
  refine ⟨‖c‖ * ∑ i ∈ Finset.range (n + 1), P i,
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _), fun i hi ξ hξ => ?_⟩
  rw [iteratedDeriv_const_mul_field, c04_aux_seed_ofReal_iter _ _ _
    (contDiffAt_rpow_const_of_ne hξ.ne'), norm_mul, Complex.norm_real, Real.norm_eq_abs,
    c04_aux_I12_rpow_iter r i ξ hξ, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hPi : P i ≤ ∑ i ∈ Finset.range (n + 1), P i :=
    Finset.single_le_sum (f := P) (fun k _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  rw [show r + (i : ℝ) * (-1) = r - i by ring]
  exact mul_le_mul_of_nonneg_right hPi (rpow_nonneg hξ.le _)

theorem c04_aux_I12_Q_bd (p : ℝ) (n : ℕ) : ∃ A ≥ (0 : ℝ), ∀ i ≤ n, ∀ ξ : ℝ, 0 < ξ →
    ‖iteratedDeriv i (c04_aux_I12_Q p) ξ‖ ≤ A * ξ ^ (p + i * (-1)) := by
  obtain ⟨A, hA0, hA⟩ := c04_aux_I12_rpow_bd (-Complex.I) p n
  refine ⟨A, hA0, fun i hi ξ hξ => ?_⟩
  have hev : c04_aux_I12_Q p =ᶠ[𝓝 ξ] fun t => -Complex.I * ((t ^ p : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hξ] with t (ht : 0 < t)
    unfold c04_aux_I12_Q; rw [abs_of_pos ht]; ring
  rw [hev.iteratedDeriv_eq]
  exact hA i hi ξ hξ

/-- One Leibniz step: bounds on `∂^i E`, `i ≤ n` (weak form) give the sharp bound on `∂^{n+1} E`. -/
theorem c04_aux_I12_E_step (p : ℝ) (hp : 0 < p) (n : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i ≤ n, ∀ ξ ∈ Ioo (0 : ℝ) 1,
      ‖iteratedDeriv i (c04_aux_I12_E p) ξ‖ ≤ B * ξ ^ ((0 : ℝ) + i * (-1))) :
    ∃ B' ≥ (0 : ℝ), ∀ ξ ∈ Ioo (0 : ℝ) 1,
      ‖iteratedDeriv (n + 1) (c04_aux_I12_E p) ξ‖ ≤ B' * ξ ^ ((p + 1) + ((n + 1 : ℕ) : ℝ) * (-1)) := by
  obtain ⟨A, hA0, hA⟩ := c04_aux_I12_Q_bd p n
  refine ⟨2 ^ n * (A * B), by positivity, fun ξ hξ => ?_⟩
  rw [iteratedDeriv_succ', c04_aux_I12_E_deriv p hp]
  have := c04_aux_I12_leibniz (c04_aux_I12_Q p) (c04_aux_I12_E p) ξ hξ.1 n
    ((c04_aux_I12_Q_contDiffAt p hξ.1).of_le (by exact_mod_cast le_top))
    ((c04_aux_I12_E_contDiffAt p hξ.1).of_le (by exact_mod_cast le_top)) A B p 0 (-1)
    (fun i hi => hA i hi ξ hξ.1) (fun i hi => hB i hi ξ hξ)
  convert this using 2
  push_cast; ring_nf

theorem c04_aux_I12_E_weak (p : ℝ) (hp : 0 < p) (n : ℕ) : ∃ B ≥ (0 : ℝ), ∀ i ≤ n,
    ∀ ξ ∈ Ioo (0 : ℝ) 1, ‖iteratedDeriv i (c04_aux_I12_E p) ξ‖ ≤ B * ξ ^ ((0 : ℝ) + i * (-1)) := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun i hi ξ _ => ?_⟩
    have : i = 0 := by omega
    subst this
    simp [c04_aux_I12_E_norm]
  | succ n ih =>
    obtain ⟨B, hB0, hB⟩ := ih
    obtain ⟨B', hB'0, hB'⟩ := c04_aux_I12_E_step p hp n B hB0 hB
    refine ⟨B + B', by positivity, fun i hi ξ hξ => ?_⟩
    have hpos : 0 < ξ ^ ((0 : ℝ) + i * (-1)) := rpow_pos_of_pos hξ.1 _
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (hB i (by omega) ξ hξ).trans
        (mul_le_mul_of_nonneg_right (by linarith) hpos.le)
    · have hi' : i = n + 1 := by omega
      subst hi'
      refine (hB' ξ hξ).trans ?_
      have : ξ ^ ((p + 1) + ((n + 1 : ℕ) : ℝ) * (-1)) ≤ ξ ^ ((0 : ℝ) + ((n + 1 : ℕ) : ℝ) * (-1)) :=
        rpow_le_rpow_of_exponent_ge hξ.1 hξ.2.le (by linarith)
      calc B' * ξ ^ ((p + 1) + ((n + 1 : ℕ) : ℝ) * (-1))
          ≤ B' * ξ ^ ((0 : ℝ) + ((n + 1 : ℕ) : ℝ) * (-1)) := mul_le_mul_of_nonneg_left this hB'0
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos.le

/-- `|∂^i (1 - E)| ≤ B ξ^{p+1-i}` on `(0,1)`. -/
theorem c04_aux_I12_oneSubE_bd (p : ℝ) (hp : 0 < p) (n : ℕ) : ∃ B ≥ (0 : ℝ), ∀ i ≤ n,
    ∀ ξ ∈ Ioo (0 : ℝ) 1, ‖iteratedDeriv i (fun t => 1 - c04_aux_I12_E p t) ξ‖ ≤
      B * ξ ^ ((p + 1) + i * (-1)) := by
  have hs : ∀ k : ℕ, ∃ B ≥ (0 : ℝ), ∀ ξ ∈ Ioo (0 : ℝ) 1,
      ‖iteratedDeriv (k + 1) (c04_aux_I12_E p) ξ‖ ≤ B * ξ ^ ((p + 1) + ((k + 1 : ℕ) : ℝ) * (-1)) :=
    fun k => by
      obtain ⟨B, hB0, hB⟩ := c04_aux_I12_E_weak p hp k
      exact c04_aux_I12_E_step p hp k B hB0 hB
  choose Bs hBs0 hBs using hs
  refine ⟨1 + ∑ k ∈ Finset.range (n + 1), Bs k,
    by have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range (n + 1)) => hBs0 k; linarith,
    fun i hi ξ hξ => ?_⟩
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), Bs k := Finset.sum_nonneg fun k _ => hBs0 k
  have hpos : 0 < ξ ^ ((p + 1) + i * (-1)) := rpow_pos_of_pos hξ.1 _
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero]
    have hE : ‖1 - c04_aux_I12_E p ξ‖ ≤ Phi0 p ξ := by
      unfold c04_aux_I12_E
      rw [norm_sub_rev, show -(Complex.I * (Phi0 p ξ : ℂ)) = Complex.I * ((-Phi0 p ξ : ℝ) : ℂ) by
        push_cast; ring]
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg]
      unfold Phi0; have := hξ.1; positivity
    have hΦ : Phi0 p ξ ≤ ξ ^ (p + 1) := by
      unfold Phi0
      rw [abs_of_pos hξ.1, rpow_add hξ.1, rpow_one, div_le_iff₀ (by linarith)]
      have : 0 ≤ ξ * ξ ^ p := mul_nonneg hξ.1.le (rpow_nonneg hξ.1.le _)
      nlinarith
    calc _ ≤ ξ ^ (p + 1) := hE.trans hΦ
      _ ≤ _ := le_mul_of_one_le_left (rpow_nonneg hξ.1.le _) (by linarith)
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [iteratedDeriv_const_sub h0, iteratedDeriv_neg, norm_neg]
    refine (hBs k ξ hξ).trans (mul_le_mul_of_nonneg_right ?_ hpos.le)
    have := Finset.single_le_sum (f := Bs) (fun k _ => hBs0 k)
      (Finset.mem_range.mpr (show k < n + 1 by omega))
    linarith


/-! ### `𝓘₁` -/

/-- Local copy of `c04_aux_iter_hasDeriv`. -/
theorem c04_aux_I12_iter_hasDeriv {f : ℝ → ℂ} {V : Set ℝ} (hV : IsOpen V)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (m : ℕ) (x : ℝ) (hx : x ∈ V) :
    HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
  have h1 := hf.differentiableOn_iteratedDerivWithin (m := m)
    (by exact_mod_cast ENat.natCast_lt_top m) hV.uniqueDiffOn
  have h2 : DifferentiableAt ℝ (iteratedDeriv m f) x :=
    ((h1 x hx).differentiableAt (hV.mem_nhds hx)).congr_of_eventuallyEq (by
      filter_upwards [hV.mem_nhds hx] with w hw
      exact (iteratedDerivWithin_of_isOpen hV hw).symm)
  rw [iteratedDeriv_succ]
  exact h2.hasDerivAt

/-- `h(ξ) = (iξ)^j b(ξ)`. -/
def c04_aux_I12_h (p : ℝ) (j : ℕ) (ξ : ℝ) : ℂ := (Complex.I * (ξ : ℂ)) ^ j * c04_I1_symbol p ξ

theorem c04_aux_I12_b_eq (p : ℝ) : c04_I1_symbol p =
    fun ξ => ((((1 - chiPlus ξ) / ξ ^ 2 : ℝ)) : ℂ) * (1 - c04_aux_I12_E p ξ) := by
  funext ξ
  unfold c04_I1_symbol c04_aux_I12_E
  push_cast; ring

theorem c04_aux_I12_b_contDiffAt (p : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (c04_I1_symbol p) ξ := by
  rw [c04_aux_I12_b_eq]
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (1 - chiPlus ξ) / ξ ^ 2) ξ :=
    (contDiffAt_const.sub c04_aux_seed_chi_smooth.contDiffAt).div (contDiffAt_id.pow 2)
      (by positivity)
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ h1).mul
    (contDiffAt_const.sub (c04_aux_I12_E_contDiffAt p hξ))

theorem c04_aux_I12_h_contDiffOn (p : ℝ) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c04_aux_I12_h p j) (Ioi 0) := fun ξ (hξ : 0 < ξ) => by
  have : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => (Complex.I * (t : ℂ)) ^ j) ξ :=
    (contDiffAt_const.mul Complex.ofRealCLM.contDiff.contDiffAt).pow j
  exact (this.mul (c04_aux_I12_b_contDiffAt p hξ)).contDiffWithinAt

theorem c04_aux_I12_h_zero (p : ℝ) (j : ℕ) {ξ : ℝ} (hξ : 2 ≤ ξ) : c04_aux_I12_h p j ξ = 0 := by
  unfold c04_aux_I12_h
  rw [c04_aux_I12_b_eq]
  simp [c04_aux_seed_chi_one hξ]

theorem c04_aux_I12_h_iter_zero (p : ℝ) (j k : ℕ) {ξ : ℝ} (hξ : 2 < ξ) :
    iteratedDeriv k (c04_aux_I12_h p j) ξ = 0 := by
  have hev : c04_aux_I12_h p j =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hξ] with t (ht : 2 < t)
    exact c04_aux_I12_h_zero p j ht.le
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
  split_ifs <;> rfl

/-- Bound of `∂^k h` on `(0,1)`. -/
theorem c04_aux_I12_h_bd_small (p : ℝ) (hp : 0 < p) (j k : ℕ) (hk : k ≤ j + 1) :
    ∃ A ≥ (0 : ℝ), ∀ ξ ∈ Ioo (0 : ℝ) 1,
      ‖iteratedDeriv k (c04_aux_I12_h p j) ξ‖ ≤ A * ξ ^ ((p + j) - 1 - (k : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := c04_aux_I12_rpow_bd (Complex.I ^ j) ((j : ℝ) - 2) (j + 1)
  obtain ⟨B, hB0, hB⟩ := c04_aux_I12_oneSubE_bd p hp (j + 1)
  refine ⟨2 ^ k * (A * B), by positivity, fun ξ hξ => ?_⟩
  set f : ℝ → ℂ := fun t => Complex.I ^ j * ((t ^ ((j : ℝ) - 2) : ℝ) : ℂ) with hf
  set g : ℝ → ℂ := fun t => 1 - c04_aux_I12_E p t with hg
  have hev : c04_aux_I12_h p j =ᶠ[𝓝 ξ] f * g := by
    filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with t ht
    have ht0 : 0 < t := ht.1
    unfold c04_aux_I12_h
    rw [c04_aux_I12_b_eq, Pi.mul_apply]
    simp only [hf, hg]
    rw [c04_aux_seed_chi_zero ht.2.le]
    rw [rpow_sub ht0, rpow_natCast, rpow_two]
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    push_cast
    field_simp
    ring
  rw [hev.iteratedDeriv_eq]
  have hfc : ContDiffAt ℝ k f ξ := contDiffAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ (contDiffAt_rpow_const_of_ne hξ.1.ne'))
  have hgc : ContDiffAt ℝ k g ξ :=
    (contDiffAt_const.sub (c04_aux_I12_E_contDiffAt p hξ.1)).of_le (by exact_mod_cast le_top)
  have := c04_aux_I12_leibniz f g ξ hξ.1 k hfc hgc A B ((j : ℝ) - 2) (p + 1) (-1)
    (fun i hi => hA i (by omega) ξ hξ.1) (fun i hi => hB i (by omega) ξ hξ)
  convert this using 2
  ring_nf

/-- Bound of `∂^k h` on `[1,3]`. -/
theorem c04_aux_I12_h_bd_mid (p : ℝ) (j k : ℕ) :
    ∃ K ≥ (0 : ℝ), ∀ ξ ∈ Icc (1 : ℝ) 3, ‖iteratedDeriv k (c04_aux_I12_h p j) ξ‖ ≤ K := by
  have hc : ContinuousOn (iteratedDeriv k (c04_aux_I12_h p j)) (Icc 1 3) := fun ξ hξ =>
    (c04_aux_I12_iter_hasDeriv isOpen_Ioi (c04_aux_I12_h_contDiffOn p j) k ξ
      (show (0 : ℝ) < ξ by linarith [hξ.1])).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨|K|, abs_nonneg _, fun ξ hξ => (hK ξ hξ).trans (le_abs_self K)⟩

theorem c04_aux_I12_h_bd (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j k : ℕ) (hk : k ≤ j + 1) :
    ∃ A ≥ (0 : ℝ), ∀ ξ ∈ Ioc (0 : ℝ) 3,
      ‖iteratedDeriv k (c04_aux_I12_h p j) ξ‖ ≤ A * ξ ^ ((p + j) - 1 - (k : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := c04_aux_I12_h_bd_small p hp j k hk
  obtain ⟨K, hK0, hK⟩ := c04_aux_I12_h_bd_mid p j k
  refine ⟨A + 9 * K, by positivity, fun ξ hξ => ?_⟩
  have hpos : 0 < ξ ^ ((p + j) - 1 - (k : ℝ)) := rpow_pos_of_pos hξ.1 _
  rcases lt_or_ge ξ 1 with h1 | h1
  · exact (hA ξ ⟨hξ.1, h1⟩).trans (mul_le_mul_of_nonneg_right (by linarith) hpos.le)
  · have hlow : (1 : ℝ) / 9 ≤ ξ ^ ((p + j) - 1 - (k : ℝ)) := by
      have hk' : (k : ℝ) ≤ j + 1 := by exact_mod_cast hk
      calc (1 : ℝ) / 9 = (3 : ℝ) ^ (-2 : ℝ) := by
            rw [rpow_neg (by norm_num)]; norm_num
        _ ≤ ξ ^ (-2 : ℝ) := rpow_le_rpow_of_nonpos (by linarith) hξ.2 (by norm_num)
        _ ≤ _ := rpow_le_rpow_of_exponent_le h1 (by linarith)
    calc _ ≤ K := hK ξ ⟨h1, hξ.2⟩
      _ ≤ 9 * K * ξ ^ ((p + j) - 1 - (k : ℝ)) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos.le

theorem c04_aux_I12_b_moment (p : ℝ) (hp : 3 / 4 < p) (k : ℕ) :
    IntegrableOn (fun ξ => ξ ^ k * ‖c04_I1_symbol p ξ‖) (Ioi 0) := by
  have hp0 : 0 < p := by linarith
  have hmaj : IntegrableOn (fun ξ => 2 ^ k * (Ioc (0 : ℝ) 2).indicator (fun ξ => ξ ^ (p - 1)) ξ)
      (Ioi 0) := by
    refine Integrable.integrableOn (Integrable.const_mul ?_ _)
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p - 1)).1
  have hbc : ContinuousOn (c04_I1_symbol p) (Ioi 0) := fun ξ (hξ : 0 < ξ) =>
    (c04_aux_I12_b_contDiffAt p hξ).continuousAt.continuousWithinAt
  refine hmaj.mono' (((continuous_pow k).continuousOn.mul hbc.norm).aestronglyMeasurable
    measurableSet_Ioi) (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ (hξ : 0 < ξ) => ?_)
  have hbb := c04_aux_seed_b_bound p hp0 ξ hξ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hξ.le _) (norm_nonneg _))]
  rcases le_or_gt ξ 2 with h2 | h2
  · rw [indicator_of_mem (show ξ ∈ Ioc (0 : ℝ) 2 from ⟨hξ, h2⟩)] at hbb ⊢
    exact mul_le_mul (pow_le_pow_left₀ hξ.le h2 k) hbb (norm_nonneg _) (by positivity)
  · rw [indicator_of_notMem (show ξ ∉ Ioc (0 : ℝ) 2 from fun h => absurd h.2 (not_le.mpr h2))]
      at hbb ⊢
    have : ‖c04_I1_symbol p ξ‖ = 0 := le_antisymm hbb (norm_nonneg _)
    rw [this, mul_zero, mul_zero]

theorem c04_aux_I12_I1_eq (p : ℝ) :
    c04_I1 p = fun y => π⁻¹ * (c04_aux_I12_G (c04_I1_symbol p) 0 y).re := by
  funext y
  unfold c04_I1 c04_aux_I12_G
  congr 3
  funext ξ
  simp only [c04_aux_I12_K, pow_zero, one_mul]

theorem c04_aux_I12_G_b_eq (p : ℝ) (j : ℕ) (y : ℝ) :
    c04_aux_I12_G (c04_I1_symbol p) j y = ∫ ξ in (0 : ℝ)..3,
      Complex.exp (Complex.I * ((y * ξ : ℝ) : ℂ)) * c04_aux_I12_h p j ξ := by
  unfold c04_aux_I12_G
  rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    (fun ξ hξ => ?_)]
  · congr 1; funext ξ
    unfold c04_aux_I12_K c04_aux_I12_h; ring
  · have h3 : 3 < ξ := by
      by_contra h
      exact hξ.2 ⟨hξ.1, not_lt.mp h⟩
    have := c04_aux_I12_h_zero p j (show 2 ≤ ξ by linarith)
    unfold c04_aux_I12_h at this
    unfold c04_aux_I12_K
    rw [mul_comm ((Complex.I * (ξ : ℂ)) ^ j), mul_assoc, this, mul_zero]

/-- Blueprint: lem:c04_I1_bound.  `𝓘₁ ∈ C^∞` and `|∂^j 𝓘₁(y)| ≤ C_j |y|^{-p-j}` for `|y| ≥ 1`. -/
theorem c04_I1_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c04_I1 p) ∧
    ∀ j : ℕ, ∃ C > (0 : ℝ), ∀ y : ℝ, 1 ≤ |y| →
      |iteratedDeriv j (c04_I1 p) y| ≤ C * |y| ^ (-p - j) := by
  have hp0 : 0 < p := by linarith
  have hbc : ContinuousOn (c04_I1_symbol p) (Ioi 0) := fun ξ (hξ : 0 < ξ) =>
    (c04_aux_I12_b_contDiffAt p hξ).continuousAt.continuousWithinAt
  have hmom := c04_aux_I12_b_moment p hp
  have hG := c04_aux_I12_G_contDiff_top (c04_I1_symbol p) hbc hmom
  rw [c04_aux_I12_I1_eq]
  refine ⟨contDiff_const.mul (Complex.reCLM.contDiff.comp hG), fun j => ?_⟩
  -- the oscillatory bound
  have hA : ∀ k : ℕ, ∃ A ≥ (0 : ℝ), k ≤ j + 1 → ∀ ξ ∈ Ioc (0 : ℝ) 3,
      ‖iteratedDeriv k (c04_aux_I12_h p j) ξ‖ ≤ A * ξ ^ ((p + j) - 1 - (k : ℝ)) := by
    intro k
    by_cases hk : k ≤ j + 1
    · obtain ⟨A, hA0, h⟩ := c04_aux_I12_h_bd p hp0 hp1 j k hk
      exact ⟨A, hA0, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose A hA0 hAb using hA
  have hhs := c04_aux_I12_h_contDiffOn p j
  obtain ⟨C, hC, hCb⟩ := c04_aux_I12_ibp_bound (fun k => iteratedDeriv k (c04_aux_I12_h p j))
    (j + 1) (p + j) A (by positivity) (by push_cast; linarith) hA0
    (fun k _ ξ hξ => c04_aux_I12_iter_hasDeriv isOpen_Ioi hhs k ξ hξ.1)
    (fun ξ hξ => (c04_aux_I12_iter_hasDeriv isOpen_Ioi hhs (j + 1) ξ
      hξ.1).continuousAt.continuousWithinAt)
    (fun k _ => c04_aux_I12_h_iter_zero p j k (by norm_num))
    (fun k hk ξ hξ => hAb k hk ξ hξ)
  refine ⟨π⁻¹ * C, by positivity, fun y hy => ?_⟩
  rw [iteratedDeriv_const_mul_field,
    c04_aux_I12_iteratedDeriv_re _ _ _ (hG.contDiffAt.of_le (by exact_mod_cast le_top)),
    c04_aux_I12_G_iter _ hbc j (fun k _ => hmom k) j le_rfl, c04_aux_I12_G_b_eq,
    abs_mul, abs_of_pos (inv_pos.mpr pi_pos), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr pi_pos.le)
  refine (Complex.abs_re_le_norm _).trans ?_
  have := hCb y hy
  simp only [iteratedDeriv_zero] at this
  rw [show -p - (j : ℝ) = -(p + j) by ring]
  exact this


/-- Blueprint: lem:c04_f0plus_negative.  `|∂^j f_{0,+}(y)| ≤ C_{j,N} |y|^{-N}` for `y ≤ -1`. -/
theorem c04_f0plus_negative (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ (j : ℕ) (N : ℝ), 0 ≤ N → ∃ C > (0 : ℝ), ∀ y ≤ (-1 : ℝ),
      ‖iteratedDeriv j (c04_linear_seed_plus p) y‖ ≤ C * |y| ^ (-N) := by
  intro j N hN
  obtain ⟨-, -, hsym, -, -, -⟩ := c04_seed_integrable p hp hp1
  obtain ⟨-, -, hpder, -⟩ := c04_seed_high_regular p hp hp1
  have hb : ∀ n : ℕ, (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ n * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) ∈
      c04_osc_symbol (-2 + n) := by
    intro n
    induction n with
    | zero => simpa using hsym
    | succ n ih =>
      have h := (c04_osc_integral_properties p hp hp1 _ _ ih).2.2.2.2.1
      have e : (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ (n + 1) * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) =
          fun ξ : ℝ => Complex.I * (ξ : ℂ) *
            ((Complex.I * (ξ : ℂ)) ^ n * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) := by
        funext ξ; ring
      rw [e]; convert h using 2; push_cast; ring
  obtain ⟨C, hC, hdec⟩ := (c04_osc_integral_properties p hp hp1 _ _ (hb j)).2.2.2.2.2.2.2 N hN
  refine ⟨(2 * π)⁻¹ * C, by positivity, fun y hy => ?_⟩
  rw [hpder j y, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π), mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdec y hy) (by positivity)

/-! ### Generic calculus helpers (used in lem:c04_seed_amplitude) -/

/-- Faà di Bruno type bound (wrapper of `norm_iteratedFDerivWithin_comp_le`) for real-variable
compositions on open sets. -/
theorem c04_aux_fdb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) (f : ℝ → ℝ)
    (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) (n : ℕ) (hg : ContDiffOn ℝ n g t)
    (hf : ContDiffOn ℝ n f s) (hst : MapsTo f s t) (x : ℝ) (hx : x ∈ s) (C D : ℝ)
    (hC : ∀ i, i ≤ n → ‖iteratedDeriv i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i f x| ≤ D ^ i) :
    ‖iteratedDeriv n (g ∘ f) x‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  have hcomp : ContDiffOn ℝ n (g ∘ f) s := hg.comp hf hst
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le hg hf le_rfl ht.uniqueDiffOn hs.uniqueDiffOn hst hx
    (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx), norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC i hi
  · rw [iteratedFDerivWithin_of_isOpen i hs hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs]
    exact hD i hi1 hi

/-- `∂^n e^{ix} = i^n e^{ix}`, so `‖∂^n e^{ix}‖ = 1`. -/
theorem c04_aux_norm_iter_expI (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) x‖ = 1 := by
  have key : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) =
      fun x : ℝ => Complex.I ^ n * Complex.exp (Complex.I * (x : ℂ)) := by
    intro n
    induction n with
    | zero => funext x; simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have h1 : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ)) (Complex.I * 1) x :=
        (Complex.ofRealCLM.hasDerivAt.const_mul Complex.I)
      have h2 := (h1.cexp).const_mul (Complex.I ^ n)
      rw [h2.deriv]; ring
  rw [key, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

/-- Leibniz bound with "symbol" growth: if `‖∂^i f‖ ≤ A y^{a+iσ}`, `‖∂^i g‖ ≤ B y^{b+iσ}` for
`i ≤ k`, then `‖∂^k(fg)‖ ≤ 2^k A B y^{a+b+kσ}`. -/
theorem c04_aux_leibniz {𝔸 : Type*} [NormedCommRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] (f g : ℝ → 𝔸) (y : ℝ)
    (hy : 0 < y) (k : ℕ) (hf : ContDiffAt ℝ k f y) (hg : ContDiffAt ℝ k g y) (A B a b σ : ℝ)
    (hA : ∀ i, i ≤ k → ‖iteratedDeriv i f y‖ ≤ A * y ^ (a + i * σ))
    (hB : ∀ i, i ≤ k → ‖iteratedDeriv i g y‖ ≤ B * y ^ (b + i * σ)) :
    ‖iteratedDeriv k (f * g) y‖ ≤ 2 ^ k * (A * B) * y ^ (a + b + k * σ) := by
  rw [iteratedDeriv_mul hf hg]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ‖(k.choose i : 𝔸) * iteratedDeriv i f y * iteratedDeriv (k - i) g y‖ ≤
        (k.choose i : ℝ) * (A * B * y ^ (a + b + k * σ)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : y ^ (a + i * σ) * y ^ (b + ((k - i : ℕ) : ℝ) * σ) = y ^ (a + b + k * σ) := by
      rw [← rpow_add hy, Nat.cast_sub hik]; ring_nf
    calc ‖(k.choose i : 𝔸) * iteratedDeriv i f y * iteratedDeriv (k - i) g y‖
        ≤ ‖(k.choose i : 𝔸)‖ * ‖iteratedDeriv i f y‖ * ‖iteratedDeriv (k - i) g y‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (k.choose i : ℝ) * (A * y ^ (a + i * σ)) * (B * y ^ (b + ((k - i : ℕ) : ℝ) * σ)) := by
          have h1 : ‖(k.choose i : 𝔸)‖ ≤ (k.choose i : ℝ) := by
            have := Nat.norm_cast_le (α := 𝔸) (k.choose i); rwa [norm_one, mul_one] at this
          have h2 := hA i hik
          have h3 := hB (k - i) (Nat.sub_le k i)
          have hA0 : 0 ≤ A * y ^ (a + i * σ) := le_trans (norm_nonneg _) h2
          gcongr
      _ = (k.choose i : ℝ) * (A * B * y ^ (a + b + k * σ)) := by rw [← e]; ring
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), ‖(k.choose i : 𝔸) * iteratedDeriv i f y * iteratedDeriv (k - i) g y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (A * B * y ^ (a + b + k * σ)) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ k * (A * B) * y ^ (a + b + k * σ) := by
        rw [← Finset.sum_mul]
        have := Nat.sum_range_choose k
        have h : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by exact_mod_cast this
        rw [h]; ring


/-- `Ψ₀' = λ₀` on `(0,∞)`. -/
theorem c04_aux_Psi0_hasDeriv (p : ℝ) (hp0 : 0 < p) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (Psi0 p) (lambda0 p t) t := by
  have h := ((hasDerivAt_rpow_const (p := 1 + 1 / p) (Or.inl ht.ne')).const_mul (p / (p + 1)))
  have e : p / (p + 1) * ((1 + 1 / p) * t ^ (1 + 1 / p - 1)) = lambda0 p t := by
    rw [show 1 + 1 / p - 1 = 1 / p by ring]
    simp only [lambda0]
    field_simp
  show HasDerivAt (fun y => p / (p + 1) * y ^ (1 + 1 / p)) (lambda0 p t) t
  exact h.congr_deriv e

/-- All-orders version of `c04_aux_leibniz`. -/
theorem c04_aux_leibniz_all {𝔸 : Type*} [NormedCommRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸]
    (f g : ℝ → 𝔸) (y : ℝ) (hy : 0 < y) (k : ℕ) (hf : ContDiffAt ℝ k f y) (hg : ContDiffAt ℝ k g y)
    (A B a b σ : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ i, i ≤ k → ‖iteratedDeriv i f y‖ ≤ A * y ^ (a + i * σ))
    (hB : ∀ i, i ≤ k → ‖iteratedDeriv i g y‖ ≤ B * y ^ (b + i * σ)) :
    ∀ i, i ≤ k → ‖iteratedDeriv i (f * g) y‖ ≤ 2 ^ k * (A * B) * y ^ (a + b + i * σ) := by
  intro i hi
  have hfi : ContDiffAt ℝ i f y := hf.of_le (by exact_mod_cast hi)
  have hgi : ContDiffAt ℝ i g y := hg.of_le (by exact_mod_cast hi)
  refine (c04_aux_leibniz f g y hy i hfi hgi A B a b σ (fun j hj => hA j (hj.trans hi))
    (fun j hj => hB j (hj.trans hi))).trans ?_
  apply mul_le_mul_of_nonneg_right _ (rpow_pos_of_pos hy _).le
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA0 hB0)
  exact pow_le_pow_right₀ (by norm_num) hi

/-- `∂^k ↑f = ↑(∂^k f)`. -/
theorem c04_aux_iteratedDeriv_ofReal (f : ℝ → ℝ) (y : ℝ) (k : ℕ) (hf : ContDiffAt ℝ k f y) :
    iteratedDeriv k (fun t => ((f t : ℝ) : ℂ)) y = ((iteratedDeriv k f y : ℝ) : ℂ) := by
  have : (fun t => ((f t : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    Complex.ofRealCLM.iteratedFDeriv_comp_left hf le_rfl]
  simp

/-- `a_*` is smooth on `(0,∞)`. -/
theorem c04_aux_astar_contDiffAt (p : ℝ) (hplus : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p))
    (hμs : mu_star p ≠ 0) (k : ℕ) (y : ℝ) (hy : 0 < y) : ContDiffAt ℝ k (astar p) y := by
  have hl0 : 0 < lambda0 p y := rpow_pos_of_pos hy _
  have hd1 : ContDiffAt ℝ k (fun t => Psi0 p t - π / 4) y := by
    unfold Psi0
    exact (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hy.ne')).sub contDiffAt_const
  have hd2 : ContDiffAt ℝ k (fun t => lambda0 p t ^ (-(p + 1) / 2)) y := by
    unfold lambda0
    exact (contDiffAt_rpow_const_of_ne hy.ne').rpow_const_of_ne (rpow_pos_of_pos hy _).ne'
  have hE : ContDiffAt ℝ k (fun t => Complex.exp (-(Complex.I * ((Psi0 p t - π / 4 : ℝ) : ℂ)))) y :=
    Complex.contDiff_exp.contDiffAt.comp y
      ((contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y hd1)).neg)
  have hD : ContDiffAt ℝ k (fun t => mu_star p * ((lambda0 p t ^ (-(p + 1) / 2) : ℝ) : ℂ)) y :=
    contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y hd2)
  have hD0 : mu_star p * ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hμs (Complex.ofReal_ne_zero.mpr (rpow_pos_of_pos hl0 _).ne')
  have hF : ContDiffAt ℝ k (deriv (c04_linear_seed_plus p)) y :=
    ((contDiff_infty_iff_deriv.mp hplus).2.contDiffAt).of_le (by exact_mod_cast le_top)
  have e : astar p = fun t => (Complex.exp (-(Complex.I * ((Psi0 p t - π / 4 : ℝ) : ℂ))) *
      (mu_star p * ((lambda0 p t ^ (-(p + 1) / 2) : ℝ) : ℂ))⁻¹) * deriv (c04_linear_seed_plus p) t := by
    funext t; simp only [astar, div_eq_mul_inv]
  rw [e]
  exact (hE.mul (hD.inv hD0)).mul hF

/-- Bounds `∀ k ≤ i` with a common constant, from per-order constants. -/
theorem c04_aux_sum_const (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (i : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (i + 1), C k ∧ ∀ k, k ≤ i → C k ≤ ∑ k ∈ Finset.range (i + 1), C k :=
  ⟨Finset.sum_nonneg fun k _ => hC k, fun k hk => Finset.single_le_sum (f := C) (fun k _ => hC k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))⟩

/-- `∂^k t^r = (r)_k t^{r-k}`, hence `|∂^k t^r| ≤ |(r)_k| y^{r-k}` for `y > 0`. -/
theorem c04_aux_rpow_iter (r : ℝ) (k : ℕ) (y : ℝ) (hy : 0 < y) :
    |iteratedDeriv k (fun t : ℝ => t ^ r) y| = |(descPochhammer ℝ k).eval r| * y ^ (r - k) := by
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, abs_mul, abs_of_pos (rpow_pos_of_pos hy _)]

/-- `χ₊/ξ` is smooth. -/
theorem c04_aux_seed_a1_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => chiPlus ξ / ξ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x 1 with hx | hx
  · have : (fun ξ : ℝ => chiPlus ξ / ξ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with t ht
      rw [c04_aux_seed_chi_zero (le_of_lt ht), zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact (c04_aux_seed_chi_smooth.contDiffAt).div contDiffAt_id (by positivity)

theorem c04_aux_seed_a1_iter (l : ℕ) : ∃ C > (0 : ℝ), ∀ ξ : ℝ, 1 ≤ ξ →
    |iteratedDeriv l (fun ξ : ℝ => chiPlus ξ / ξ) ξ| ≤ C * ξ ^ (-1 - (l : ℝ)) := by
  have hc : Continuous (iteratedDeriv l (fun ξ : ℝ => chiPlus ξ / ξ)) :=
    c04_aux_seed_a1_smooth.continuous_iteratedDeriv l (by exact_mod_cast le_top)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hc.continuousOn
  set P : ℝ := |∏ i ∈ Finset.range l, ((-1 : ℤ) - (i : ℝ))|
  have hP0 : 0 ≤ P := abs_nonneg _
  refine ⟨(|K| + 1) * 3 ^ (1 + (l : ℝ)) + P + 1, by positivity, fun ξ hξ => ?_⟩
  have hξ0 : 0 < ξ := by linarith
  have hpos : 0 < ξ ^ (-1 - (l : ℝ)) := rpow_pos_of_pos hξ0 _
  rcases le_or_gt ξ 3 with h3 | h3
  · have h1 := hK ξ ⟨hξ, h3⟩
    rw [Real.norm_eq_abs] at h1
    have hlow : 3 ^ (-1 - (l : ℝ)) ≤ ξ ^ (-1 - (l : ℝ)) :=
      rpow_le_rpow_of_nonpos hξ0 h3 (by linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)])
    have h33 : (3 : ℝ) ^ (1 + (l : ℝ)) * 3 ^ (-1 - (l : ℝ)) = 1 := by
      rw [← rpow_add (by norm_num)]; simp
    calc |iteratedDeriv l (fun ξ : ℝ => chiPlus ξ / ξ) ξ| ≤ |K| + 1 := by
          linarith [le_abs_self K]
      _ = (|K| + 1) * 3 ^ (1 + (l : ℝ)) * 3 ^ (-1 - (l : ℝ)) := by rw [mul_assoc, h33, mul_one]
      _ ≤ (|K| + 1) * 3 ^ (1 + (l : ℝ)) * ξ ^ (-1 - (l : ℝ)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos.le
  · have hev : (fun ξ : ℝ => chiPlus ξ / ξ) =ᶠ[𝓝 ξ] fun t => t ^ (-1 : ℤ) := by
      filter_upwards [Ioi_mem_nhds (by linarith : (2 : ℝ) < ξ)] with t ht
      rw [c04_aux_seed_chi_one (le_of_lt ht), zpow_neg_one, one_div]
    rw [hev.iteratedDeriv_eq, iteratedDeriv_eq_iterate, iter_deriv_zpow, abs_mul]
    have hz : |ξ ^ ((-1 : ℤ) - (l : ℤ))| = ξ ^ (-1 - (l : ℝ)) := by
      rw [abs_of_pos (zpow_pos hξ0 _), ← rpow_intCast]; push_cast; rfl
    rw [hz]
    calc _ ≤ P * ξ ^ (-1 - (l : ℝ)) := mul_le_mul_of_nonneg_right le_rfl hpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
          have : 0 ≤ (|K| + 1) * 3 ^ (1 + (l : ℝ)) := by positivity
          linarith) hpos.le

/-- `‖∂^n e^{iΨ₀}‖ ≤ C y^{n/p}` for `y ≥ 1`. -/
theorem c04_aux_expPsi0_bound (p : ℝ) (hp0 : 0 < p) (n : ℕ) : ∃ C ≥ (0 : ℝ), ∀ y ≥ (1 : ℝ),
    ‖iteratedDeriv n (fun t => Complex.exp (Complex.I * (Psi0 p t : ℂ))) y‖ ≤ C * y ^ ((n : ℝ) / p) := by
  set K := 1 + ∑ i ∈ Finset.range (n + 1), |(descPochhammer ℝ i).eval (1 / p)| with hK
  have hS := c04_aux_sum_const (fun i => |(descPochhammer ℝ i).eval (1 / p)|) (fun i => abs_nonneg _) n
  have hK1 : 1 ≤ K := by linarith [hS.1]
  refine ⟨(n.factorial : ℝ) * K ^ n, by positivity, fun y hy1 => ?_⟩
  have hy0 : 0 < y := by linarith
  have hPsi0C : ContDiffOn ℝ n (Psi0 p) (Ioi 0) := fun t ht => by
    unfold Psi0
    exact (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne (ne_of_gt ht))).contDiffWithinAt
  have hfun : (fun t => Complex.exp (Complex.I * (Psi0 p t : ℂ))) =
      (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) ∘ Psi0 p := rfl
  rw [hfun]
  have hg : ContDiffOn ℝ n (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) univ :=
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).contDiffOn
  have h := c04_aux_fdb (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) (Psi0 p)
    (Ioi 0) univ isOpen_Ioi isOpen_univ n hg hPsi0C (mapsTo_univ _ _) y hy0
    1 (K * y ^ (1 / p)) (fun i _ => le_of_eq (c04_aux_norm_iter_expI i _)) ?_
  · refine h.trans (le_of_eq ?_)
    rw [mul_one, mul_pow, ← rpow_natCast (y ^ (1 / p)), ← rpow_mul hy0.le]
    ring_nf
  · intro i hi1 hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hev : deriv (Psi0 p) =ᶠ[𝓝 y] fun t => t ^ (1 / p) := by
      filter_upwards [Ioi_mem_nhds hy0] with t ht
      exact (c04_aux_Psi0_hasDeriv p hp0 t ht).deriv
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, c04_aux_rpow_iter _ _ _ hy0]
    have hClK : |(descPochhammer ℝ j).eval (1 / p)| ≤ K := by linarith [hS.2 j (by omega)]
    have hKj : K ≤ K ^ (j + 1) := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ (j + 1) := pow_le_pow_right₀ hK1 (by omega)
    have hyexp : y ^ (1 / p - (j : ℝ)) ≤ (y ^ (1 / p)) ^ (j + 1) := by
      rw [← rpow_natCast (y ^ (1 / p)), ← rpow_mul hy0.le]
      apply rpow_le_rpow_of_exponent_le hy1
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have : 0 ≤ (j : ℝ) / p := by positivity
      push_cast
      have e : 1 / p * ((j : ℝ) + 1) = 1 / p + j / p := by ring
      rw [e]; linarith
    rw [mul_pow]
    exact mul_le_mul (hClK.trans hKj) hyexp (rpow_pos_of_pos hy0 _).le (by positivity)

/-- The constant in the stationary-phase form of `a_*`. -/
theorem c04_aux_astar_const (p L : ℝ) (hp : 0 < p) (hL : 0 < L) :
    (2 * π)⁻¹ * (Real.sqrt (2 * π * p) * Real.sqrt (2 * π / (p * L ^ (p - 1)))) =
      L * L ^ (-(p + 1) / 2) := by
  have hπ : 0 < π := Real.pi_pos
  rw [← Real.sqrt_mul (by positivity)]
  have e1 : 2 * π * p * (2 * π / (p * L ^ (p - 1))) = (2 * π) ^ 2 * L ^ (1 - p) := by
    rw [show (1 : ℝ) - p = -(p - 1) by ring, rpow_neg hL.le]
    field_simp
  rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow,
    ← rpow_mul hL.le]
  rw [show L * L ^ (-(p + 1) / 2) = L ^ ((1 - p) * (1 / 2)) by
    calc L * L ^ (-(p + 1) / 2) = L ^ (1 : ℝ) * L ^ (-(p + 1) / 2) := by rw [rpow_one]
      _ = L ^ ((1 : ℝ) + -(p + 1) / 2) := (rpow_add hL _ _).symm
      _ = _ := by congr 1; ring]
  field_simp

theorem c04_aux_astar_formula (p y : ℝ) (hp0 : 0 < p) (hy : 0 < y) (A r : ℂ)
    (hd : deriv (c04_linear_seed_plus p) y = -((2 * π : ℝ) : ℂ)⁻¹ * (Complex.I * (c03_sp_P p y * (A + r)))) :
    astar p y = (lambda0 p y : ℂ) * (A + r) := by
  have hπ : 0 < π := Real.pi_pos
  have hL : 0 < lambda0 p y := rpow_pos_of_pos hy _
  have hs0 : 0 < Real.sqrt (2 * π * p) := Real.sqrt_pos.mpr (by positivity)
  have hLq : 0 < lambda0 p y ^ (-(p + 1) / 2) := rpow_pos_of_pos hL _
  have key := c04_aux_astar_const p (lambda0 p y) hp0 hL
  have key' : ((2 * π : ℝ) : ℂ)⁻¹ * ((Real.sqrt (2 * π * p) : ℂ) *
      (Real.sqrt (2 * π / (p * lambda0 p y ^ (p - 1))) : ℂ)) =
      (lambda0 p y : ℂ) * ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ) := by
    exact_mod_cast key
  have hE : Complex.exp (-(Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ))) *
      Complex.exp (Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  unfold astar
  rw [hd]
  unfold c03_sp_P mu_star
  have h1 : (Real.sqrt (2 * π * p) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have h2 : ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hLq.ne'
  have h3 : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  set Em := Complex.exp (-(Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ)))
  set Ep := Complex.exp (Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ))
  set s0 : ℂ := (Real.sqrt (2 * π * p) : ℂ)
  set S : ℂ := (Real.sqrt (2 * π / (p * lambda0 p y ^ (p - 1))) : ℂ)
  set Lq : ℂ := ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ)
  set c : ℂ := ((2 * π : ℝ) : ℂ)
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  calc Em / (-Complex.I / s0 * Lq) * (-c⁻¹ * (Complex.I * (Ep * S * (A + r))))
      = Em * Ep * (c⁻¹ * (s0 * S)) * Lq⁻¹ * (A + r) * (Complex.I * Complex.I⁻¹) := by
        field_simp
    _ = 1 * ((lambda0 p y : ℂ) * Lq) * Lq⁻¹ * (A + r) * 1 := by
        rw [hE, key', mul_inv_cancel₀ hI]
    _ = (lambda0 p y : ℂ) * (A + r) := by field_simp

/-- Blueprint: lem:c04_seed_amplitude.  There is `y₀ ≥ 2` with `|∂^j(a_*-1)| ≤ C_j y^{-2β-j}`,
`|a_*| ≤ 2`, `|∂^j a_*| ≤ C_j y^{-j}` and `|∂^j f_{0,+}'| ≤ C_j y^{-β+j/p}` on `[y₀,∞)`. -/
theorem c04_seed_amplitude (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ y₀ ≥ (2 : ℝ), (∀ y ≥ y₀, ‖astar p y‖ ≤ 2) ∧
      ∀ j : ℕ, ∃ C > (0 : ℝ), ∀ y ≥ y₀,
        ‖iteratedDeriv j (fun t => astar p t - 1) y‖ ≤ C * y ^ (-2 * beta p - j) ∧
        ‖iteratedDeriv j (astar p) y‖ ≤ C * y ^ (-(j : ℝ)) ∧
        ‖iteratedDeriv j (deriv (c04_linear_seed_plus p)) y‖ ≤ C * y ^ (-beta p + j / p) := by
  have hp0 : 0 < p := by linarith
  have hπ : 0 < π := Real.pi_pos
  have hs0 : 0 < Real.sqrt (2 * π * p) := Real.sqrt_pos.mpr (by positivity)
  have hμs : mu_star p ≠ 0 := by
    unfold mu_star
    exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hs0.ne')
  obtain ⟨hplus, -, hpder, -⟩ := c04_seed_high_regular p hp hp1
  obtain ⟨-, -, hsym2, -, -, -⟩ := c04_seed_integrable p hp hp1
  set a : ℝ → ℂ := fun ξ => ((chiPlus ξ / ξ : ℝ) : ℂ) with ha
  have haC : ContDiff ℝ (⊤ : ℕ∞) a := Complex.ofRealCLM.contDiff.comp c04_aux_seed_a1_smooth
  choose Ca hCa0 hCa using c04_aux_seed_a1_iter
  have ha_sp : a ∈ c03_sp_symbol (-1) := by
    refine ⟨haC.contDiffOn, fun ξ hξ => ?_, fun k => ⟨Ca k, fun ξ hξ => ?_⟩⟩
    · simp [ha, c04_aux_seed_chi_zero hξ.2]
    · rw [c04_aux_iteratedDeriv_ofReal _ _ _ (c04_aux_seed_a1_smooth.contDiffAt.of_le
        (by exact_mod_cast le_top)), Complex.norm_real, Real.norm_eq_abs]
      exact hCa k ξ hξ
  obtain ⟨hsp1, hsp2⟩ := c03f_appendix_homogeneous_stationary_phase p (-1) hp0 hp1 (by linarith)
  obtain ⟨hlim, hrep, hrsm⟩ := hsp1 a ha_sp
  set r := c03_hsp_r p a with hr
  have hb : (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ 1 * ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)) ∈
      c04_osc_symbol (-1) := by
    have := (c04_osc_parameter_derivatives p hp0 hp1 (-2) _ hsym2).2.2.2.2.1
    rw [show (-2 : ℝ) + 1 = -1 by norm_num] at this
    convert this using 2 with ξ
    ring
  obtain ⟨-, himp⟩ := c04_osc_ordinary_integrals p hp0 hp1 (-1) _ hb
  have hderiv : ∀ y > 0, deriv (c04_linear_seed_plus p) y =
      -((2 * π : ℝ) : ℂ)⁻¹ * (Complex.I * c03_hsp_I p a y) := by
    intro y hy
    rw [← iteratedDeriv_one, hpder 1 y]
    congr 1
    refine tendsto_nhds_unique (himp (by linarith) y) ?_
    have := (hlim y hy).const_mul Complex.I
    refine this.congr fun M => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    by_cases hξ : 1 < ξ
    · have hξ0 : 0 < ξ := by linarith
      simp only [ha, c04_eiphase, c03_sp_phi, Phi0, abs_of_pos hξ0, pow_one]
      rw [show ξ * ξ ^ p = ξ ^ (p + 1) by rw [rpow_add hξ0, rpow_one]; ring]
      have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ0.ne'
      push_cast
      field_simp
    · simp [ha, c04_aux_seed_chi_zero (not_lt.mp hξ)]
  -- `a_* = λ₀ (a(λ₀) + r)` and `a_* - 1 = λ₀ r` for `y > 2^p`
  have hast : ∀ y > 0, astar p y = (lambda0 p y : ℂ) * (a (lambda0 p y) + r y) := by
    intro y hy
    refine c04_aux_astar_formula p y hp0 hy _ _ ?_
    rw [hderiv y hy, hrep y hy]
  have hast1 : ∀ y > (2 : ℝ) ^ p, astar p y - 1 = (lambda0 p y : ℂ) * r y := by
    intro y hy
    have hy0 : 0 < y := lt_trans (by positivity) hy
    have hL2 : 2 ≤ lambda0 p y := by
      unfold lambda0
      calc (2 : ℝ) = ((2 : ℝ) ^ p) ^ (1 / p) := by
            rw [← rpow_mul (by norm_num), mul_one_div_cancel hp0.ne', rpow_one]
        _ ≤ y ^ (1 / p) := rpow_le_rpow (by positivity) hy.le (by positivity)
    have hL0 : (lambda0 p y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    rw [hast y hy0]
    simp only [ha, c04_aux_seed_chi_one hL2]
    push_cast
    field_simp
    ring
  have hβ : 0 < beta p := by unfold beta; positivity
  have h2β : -2 * beta p = 1 / p - (p + 2) / p := by unfold beta; field_simp; ring
  -- bounds for the remainder `r`
  have hrb : ∀ i : ℕ, ∃ C > (0 : ℝ), ∀ y ≥ (1 : ℝ),
      ‖iteratedDeriv i r y‖ ≤ C * y ^ (-(p + 2) / p + (i : ℝ) * (-1)) := by
    intro i
    obtain ⟨k₀, hk⟩ := hsp2 i
    obtain ⟨C, hC, h⟩ := hk Ca
    refine ⟨C, hC, fun y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    have := h a ha_sp (fun k _ ξ hξ => by
      rw [c04_aux_iteratedDeriv_ofReal _ _ _ (c04_aux_seed_a1_smooth.contDiffAt.of_le
        (by exact_mod_cast le_top)), Complex.norm_real, Real.norm_eq_abs]
      exact hCa k ξ hξ) y hy
    refine this.trans (le_of_eq ?_)
    unfold lambda0
    rw [← rpow_mul hy0.le, mul_assoc, ← rpow_add hy0]
    congr 2; field_simp; ring
  choose Cr hCr0 hCr using hrb
  -- bounds for `∂^i λ₀`
  have hlb : ∀ (i : ℕ) (y : ℝ), 0 < y →
      ‖iteratedDeriv i (fun t => (lambda0 p t : ℂ)) y‖ =
        |(descPochhammer ℝ i).eval (1 / p)| * y ^ (1 / p - i) := by
    intro i y hy
    rw [c04_aux_iteratedDeriv_ofReal _ _ _ (by unfold lambda0; exact contDiffAt_rpow_const_of_ne hy.ne'),
      Complex.norm_real, Real.norm_eq_abs]
    exact c04_aux_rpow_iter (1 / p) i y hy
  set y₁ : ℝ := max 2 (2 ^ p + 1) with hy₁
  have hy₁2 : 2 ≤ y₁ := le_max_left _ _
  -- (1) the bound for `a_* - 1`
  have hbd1 : ∀ j : ℕ, ∃ K ≥ (0 : ℝ), ∀ y ≥ y₁,
      ‖iteratedDeriv j (fun t => astar p t - 1) y‖ ≤ K * y ^ (-2 * beta p - j) := by
    intro j
    obtain ⟨hAl0, hAl⟩ := c04_aux_sum_const (fun i => |(descPochhammer ℝ i).eval (1 / p)|)
      (fun i => abs_nonneg _) j
    obtain ⟨hAr0, hAr⟩ := c04_aux_sum_const Cr (fun i => (hCr0 i).le) j
    set Al := ∑ i ∈ Finset.range (j + 1), |(descPochhammer ℝ i).eval (1 / p)|
    set Ar := ∑ i ∈ Finset.range (j + 1), Cr i
    refine ⟨2 ^ j * (Al * Ar), by positivity, fun y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hyp : (2 : ℝ) ^ p < y := by linarith [le_max_right 2 ((2 : ℝ) ^ p + 1)]
    have hev : (fun t => astar p t - 1) =ᶠ[𝓝 y] fun t => (lambda0 p t : ℂ) * r t := by
      filter_upwards [Ioi_mem_nhds hyp] with t ht using hast1 t ht
    rw [hev.iteratedDeriv_eq]
    have b := c04_aux_leibniz (fun t => (lambda0 p t : ℂ)) r y hy0 j
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (by exact contDiffAt_rpow_const_of_ne hy0.ne'))
      ((hrsm.contDiffAt (Ioi_mem_nhds hy0)).of_le (by exact_mod_cast le_top))
      Al Ar (1 / p) (-(p + 2) / p) (-1)
      (fun i hi => by
        rw [hlb i y hy0]
        exact mul_le_mul (hAl i hi) (le_of_eq (by congr 1; ring)) (rpow_pos_of_pos hy0 _).le hAl0)
      (fun i hi => (hCr i y hy1).trans (mul_le_mul_of_nonneg_right (hAr i hi)
        (rpow_pos_of_pos hy0 _).le))
    refine b.trans (le_of_eq ?_)
    congr 1; congr 1; rw [h2β]; ring
  choose K1 hK10 hK1 using hbd1
  set y₀ : ℝ := max y₁ ((K1 0 + 1) ^ (1 / (2 * beta p))) with hy₀
  have hy₀1 : y₁ ≤ y₀ := le_max_left _ _
  have hsmall : ∀ y ≥ y₀, K1 0 * y ^ (-2 * beta p) ≤ 1 := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have h1 : (K1 0 + 1) ^ (1 / (2 * beta p)) ≤ y := le_trans (le_max_right _ _) hy
    have h2 : K1 0 + 1 ≤ y ^ (2 * beta p) := by
      calc K1 0 + 1 = ((K1 0 + 1) ^ (1 / (2 * beta p))) ^ (2 * beta p) := by
            rw [← rpow_mul (by linarith [hK10 0]), one_div_mul_cancel (by linarith), rpow_one]
        _ ≤ y ^ (2 * beta p) := rpow_le_rpow (rpow_nonneg (by linarith [hK10 0]) _) h1 (by linarith)
    rw [show -2 * beta p = -(2 * beta p) by ring, rpow_neg hy0.le, ← div_eq_mul_inv,
      div_le_one (rpow_pos_of_pos hy0 _)]
    linarith
  have hnorm2 : ∀ y ≥ y₀, ‖astar p y‖ ≤ 2 := by
    intro y hy
    have h := hK1 0 y (le_trans hy₀1 hy)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
    calc ‖astar p y‖ = ‖(astar p y - 1) + 1‖ := by ring_nf
      _ ≤ ‖astar p y - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith [hsmall y hy]
      _ = 2 := by norm_num
  -- (ii) derivatives of `a_*`
  have hbd2 : ∀ j : ℕ, ∀ y ≥ y₀, ‖iteratedDeriv j (astar p) y‖ ≤ (K1 j + 2) * y ^ (-(j : ℝ)) := by
    intro j y hy
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, rpow_zero, mul_one]
      linarith [hnorm2 y hy, hK10 0]
    · have e : iteratedDeriv j (astar p) y = iteratedDeriv j (fun t => astar p t - 1) y := by
        rw [show (fun t => astar p t - 1) = fun t => (-1 : ℂ) + astar p t by funext t; ring,
          iteratedDeriv_const_add hj]
      rw [e]
      refine (hK1 j y (le_trans hy₀1 hy)).trans ?_
      have : y ^ (-2 * beta p - j) ≤ y ^ (-(j : ℝ)) :=
        rpow_le_rpow_of_exponent_le hy1 (by linarith)
      have h0 : 0 ≤ y ^ (-(j : ℝ)) := (rpow_pos_of_pos hy0 _).le
      nlinarith [hK10 j]
  -- (iii) derivatives of `f_{0,+}'`
  choose Ce hCe0 hCe using c04_aux_expPsi0_bound p hp0
  set c₀ : ℂ := mu_star p * Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) with hc₀
  set u : ℝ → ℂ := fun t => ((t ^ (-beta p) : ℝ) : ℂ) with hu
  set v : ℝ → ℂ := fun t => Complex.exp (Complex.I * (Psi0 p t : ℂ)) with hv
  have hfeq : ∀ t > (0 : ℝ), deriv (c04_linear_seed_plus p) t = astar p t * (c₀ * (u * v) t) := by
    intro t ht
    have hL : 0 < lambda0 p t := rpow_pos_of_pos ht _
    have hLq : lambda0 p t ^ (-(p + 1) / 2) = t ^ (-beta p) := by
      unfold lambda0 beta; rw [← rpow_mul ht.le]; congr 1; field_simp
    have hD : mu_star p * ((lambda0 p t ^ (-(p + 1) / 2) : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero hμs (Complex.ofReal_ne_zero.mpr (rpow_pos_of_pos hL _).ne')
    have hE : Complex.exp (-(Complex.I * ((Psi0 p t - π / 4 : ℝ) : ℂ))) *
        (Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) * Complex.exp (Complex.I * (Psi0 p t : ℂ))) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add]; push_cast; ring_nf; simp
    unfold astar
    simp only [hc₀, hu, hv, Pi.mul_apply]
    rw [← hLq]
    calc deriv (c04_linear_seed_plus p) t = deriv (c04_linear_seed_plus p) t *
          (Complex.exp (-(Complex.I * ((Psi0 p t - π / 4 : ℝ) : ℂ))) *
            (Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) * Complex.exp (Complex.I * (Psi0 p t : ℂ)))) *
          ((mu_star p * ((lambda0 p t ^ (-(p + 1) / 2) : ℝ) : ℂ)) *
            (mu_star p * ((lambda0 p t ^ (-(p + 1) / 2) : ℝ) : ℂ))⁻¹) := by
          rw [hE, mul_inv_cancel₀ hD]; ring
      _ = _ := by ring
  have huC : ∀ (n : ℕ) (y : ℝ), 0 < y → ContDiffAt ℝ n u y := fun n y hy =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp y (contDiffAt_rpow_const_of_ne hy.ne')
  have hvC : ∀ (n : ℕ) (y : ℝ), 0 < y → ContDiffAt ℝ n v y := fun n y hy =>
    Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (by exact contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hy.ne'))))
  have hGb : ∀ k : ℕ, ∃ B ≥ (0 : ℝ), ∀ y ≥ (1 : ℝ),
      ‖iteratedDeriv k (fun t => c₀ * (u * v) t) y‖ ≤ B * y ^ (-beta p + k * (1 / p)) := by
    intro k
    obtain ⟨hDu0, hDu⟩ := c04_aux_sum_const (fun i => |(descPochhammer ℝ i).eval (-beta p)|)
      (fun i => abs_nonneg _) k
    obtain ⟨hEv0, hEv⟩ := c04_aux_sum_const Ce hCe0 k
    set Du := ∑ i ∈ Finset.range (k + 1), |(descPochhammer ℝ i).eval (-beta p)|
    set Ev := ∑ i ∈ Finset.range (k + 1), Ce i
    refine ⟨‖c₀‖ * (2 ^ k * (Du * Ev)), by positivity, fun y hy1 => ?_⟩
    have hy0 : 0 < y := by linarith
    rw [iteratedDeriv_const_mul_field, norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have b := c04_aux_leibniz u v y hy0 k (huC k y hy0) (hvC k y hy0) Du Ev (-beta p) 0 (1 / p)
      (fun i hi => by
        rw [hu, c04_aux_iteratedDeriv_ofReal _ _ _ (contDiffAt_rpow_const_of_ne hy0.ne'),
          Complex.norm_real, Real.norm_eq_abs, c04_aux_rpow_iter _ _ _ hy0]
        have hi' : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        have : (0 : ℝ) ≤ i * (1 / p) := by positivity
        exact mul_le_mul (hDu i hi) (rpow_le_rpow_of_exponent_le hy1 (by linarith))
          (rpow_pos_of_pos hy0 _).le hDu0)
      (fun i hi => by
        refine (hCe i y hy1).trans (mul_le_mul (hEv i hi) (le_of_eq ?_) (rpow_pos_of_pos hy0 _).le hEv0)
        congr 1; ring)
    have e : -beta p + 0 + (k : ℝ) * (1 / p) = -beta p + k * (1 / p) := by ring
    rw [e] at b
    exact b
  choose BG hBG0 hBG using hGb
  refine ⟨y₀, le_trans hy₁2 hy₀1, hnorm2, fun j => ?_⟩
  obtain ⟨hAa0, hAa⟩ := c04_aux_sum_const (fun k => K1 k + 2) (fun k => by linarith [hK10 k]) j
  obtain ⟨hB0, hB⟩ := c04_aux_sum_const BG hBG0 j
  set Aa := ∑ k ∈ Finset.range (j + 1), (K1 k + 2)
  set Bs := ∑ k ∈ Finset.range (j + 1), BG k
  refine ⟨K1 j + 2 + 2 ^ j * (Aa * Bs), by linarith [hK10 j, show 0 ≤ 2 ^ j * (Aa * Bs) by positivity],
    fun y hy => ?_⟩
  have hy1' : y₁ ≤ y := le_trans hy₀1 hy
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hP : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
  have hX : 0 ≤ 2 ^ j * (Aa * Bs) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (hK1 j y hy1').trans (mul_le_mul_of_nonneg_right ?_ (hP _))
    linarith
  · refine (hbd2 j y hy).trans (mul_le_mul_of_nonneg_right ?_ (hP _))
    linarith
  · have hev : deriv (c04_linear_seed_plus p) =ᶠ[𝓝 y] fun t => astar p t * (c₀ * (u * v) t) := by
      filter_upwards [Ioi_mem_nhds hy0] with t ht using hfeq t ht
    rw [hev.iteratedDeriv_eq]
    have b := c04_aux_leibniz (astar p) (fun t => c₀ * (u * v) t) y hy0 j
      (c04_aux_astar_contDiffAt p hplus hμs j y hy0)
      (contDiffAt_const.mul ((huC j y hy0).mul (hvC j y hy0)))
      Aa Bs 0 (-beta p) (1 / p)
      (fun k hk => by
        refine (hbd2 k y hy).trans (mul_le_mul (hAa k hk) (rpow_le_rpow_of_exponent_le hy1 ?_)
          (hP _) hAa0)
        have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have : (0 : ℝ) ≤ k * (1 / p) := by positivity
        linarith)
      (fun k hk => (hBG k y hy1).trans (mul_le_mul_of_nonneg_right (hB k hk) (hP _)))
    have e : (0 : ℝ) + -beta p + (j : ℝ) * (1 / p) = -beta p + j / p := by ring
    rw [e] at b
    refine b.trans (mul_le_mul_of_nonneg_right ?_ (hP _))
    linarith [hK10 j]

/-- Blueprint: lem:c04_f0plus_global.  `|f_{0,+}| + |f_{0,+}'| ≤ C` and
`|f_{0,+}''| + |f_{0,+}'''| ≤ C ⟨y⟩^{2/p}` on `ℝ`. -/
theorem c04_f0plus_global (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C > (0 : ℝ), ∀ y : ℝ,
      ‖c04_linear_seed_plus p y‖ + ‖deriv (c04_linear_seed_plus p) y‖ ≤ C ∧
      ‖iteratedDeriv 2 (c04_linear_seed_plus p) y‖ + ‖iteratedDeriv 3 (c04_linear_seed_plus p) y‖ ≤
        C * jb y ^ (2 / p) := by
  have hp0 : 0 < p := by linarith
  have hβ : 0 < beta p := by unfold beta; positivity
  obtain ⟨-, -, hs, -, ht, -⟩ := c04_seed_decomposition p hp hp1
  let F : ZeroAtInftyContinuousMap ℝ ℂ :=
    { toFun := c04_linear_seed_plus p, continuous_toFun := hs.continuous, zero_at_infty' := ht }
  obtain ⟨C₀, hC₀, h₀⟩ := F.isBounded_range.exists_pos_norm_le
  have h₀' : ∀ y, ‖c04_linear_seed_plus p y‖ ≤ C₀ := fun y => h₀ _ ⟨y, rfl⟩
  obtain ⟨y₀, hy₀, -, hamp⟩ := c04_seed_amplitude p hp hp1
  have hJ : ∀ y : ℝ, 1 ≤ jb y := fun y => by
    unfold jb
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg y])
  have hb : ∀ (k : ℕ) (a : ℝ), 0 ≤ a → -beta p + (k : ℝ) / p ≤ a →
      ∃ C > (0 : ℝ), ∀ y, ‖iteratedDeriv (k + 1) (c04_linear_seed_plus p) y‖ ≤ C * jb y ^ a := by
    intro k a ha hka
    obtain ⟨Cpos, hCpos, hpos⟩ := hamp k
    obtain ⟨Cneg, hCneg, hneg⟩ := c04_f0plus_negative p hp hp1 (k + 1) 0 le_rfl
    obtain ⟨Cmid, hmid⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) y₀)).exists_bound_of_continuousOn
      (hs.continuous_iteratedDeriv (k + 1) (by exact_mod_cast le_top)).continuousOn
    refine ⟨Cpos + Cneg + |Cmid| + 1, by positivity, fun y => ?_⟩
    have hj : 1 ≤ jb y ^ a := Real.one_le_rpow (hJ y) ha
    have hconst : ∀ C : ℝ, 0 ≤ C → C ≤ C * jb y ^ a := fun C hC => by nlinarith
    by_cases hlarge : y₀ ≤ y
    · have hy : 1 ≤ y := by linarith
      have hyj : y ≤ jb y := by
        unfold jb
        calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq (by linarith)).symm
             _ ≤ Real.sqrt (1 + y ^ 2) := Real.sqrt_le_sqrt (by linarith)
      have he : y ^ (-beta p + (k : ℝ) / p) ≤ jb y ^ a :=
        (Real.rpow_le_rpow_of_exponent_le hy hka).trans (Real.rpow_le_rpow (by linarith) hyj ha)
      have h := (hpos y hlarge).2.2
      rw [← iteratedDeriv_succ'] at h
      exact (h.trans (mul_le_mul_of_nonneg_left he hCpos.le)).trans
        (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Cmid]) (le_trans zero_le_one hj))
    · by_cases hsmall : y ≤ -1
      · have h := hneg y hsmall
        simp only [neg_zero, Real.rpow_zero, mul_one] at h
        exact h.trans ((hconst Cneg hCneg.le).trans
          (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Cmid]) (le_trans zero_le_one hj)))
      · have h := hmid y ⟨by linarith, by linarith⟩
        exact h.trans ((le_abs_self Cmid).trans ((hconst |Cmid| (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (by linarith) (le_trans zero_le_one hj))))
  obtain ⟨C₁, hC₁, h₁⟩ := hb 0 0 le_rfl (by simp; linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := hb 1 (2 / p) (by positivity) (by
    have hdiv : 0 < 1 / p := one_div_pos.mpr hp0
    norm_num only [Nat.cast_one]
    rw [show 2 / p = 2 * (1 / p) by ring]
    linarith)
  obtain ⟨C₃, hC₃, h₃⟩ := hb 2 (2 / p) (by positivity) (by simp; linarith)
  refine ⟨C₀ + C₁ + C₂ + C₃, by positivity, fun y => ⟨?_, ?_⟩⟩
  · have h1 := h₁ y
    simp only [zero_add, iteratedDeriv_one, Real.rpow_zero, mul_one] at h1
    linarith [h₀' y]
  · have h2 := h₂ y
    have h3 := h₃ y
    have hj : 0 ≤ jb y ^ (2 / p) := Real.rpow_nonneg (by linarith [hJ y]) _
    have hc : 0 ≤ (C₀ + C₁) * jb y ^ (2 / p) := mul_nonneg (by linarith) hj
    norm_num only [Nat.reduceAdd] at h2 h3
    nlinarith

/-- `χ₊` is smooth. -/
theorem c04_aux_chiPlus_smooth : ContDiff ℝ (⊤ : ℕ∞) chiPlus :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

/-- `χ₊' = 0` outside `[1,2]`. -/
theorem c04_aux_dchi_zero (ξ : ℝ) (h : ξ < 1 ∨ 2 < ξ) : deriv chiPlus ξ = 0 := by
  rcases h with h | h
  · have : chiPlus =ᶠ[𝓝 ξ] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with x hx
      exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Iio.mp hx])
    rw [this.deriv_eq]; simp
  · have : chiPlus =ᶠ[𝓝 ξ] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      exact Real.smoothTransition.one_of_one_le (by linarith [mem_Ioi.mp hx])
    rw [this.deriv_eq]; simp

/-- `|χ₊'(ξ)/ξ| ≤ K` and it vanishes outside `[1,2]`. -/
theorem c04_aux_dchi_div_bound : ∃ K ≥ (0 : ℝ), ∀ ξ : ℝ,
    |deriv chiPlus ξ / ξ| ≤ K ∧ (ξ ∉ Icc (1 : ℝ) 2 → deriv chiPlus ξ / ξ = 0) := by
  have hc : Continuous (deriv chiPlus) :=
    c04_aux_chiPlus_smooth.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun ξ => ?_⟩
  have hz : ξ ∉ Icc (1 : ℝ) 2 → deriv chiPlus ξ / ξ = 0 := by
    intro h
    rw [c04_aux_dchi_zero ξ (by
      simp only [mem_Icc, not_and_or, not_le] at h; exact h), zero_div]
  refine ⟨?_, hz⟩
  by_cases h : ξ ∈ Icc (1 : ℝ) 2
  · have h1 := hK ξ h
    rw [Real.norm_eq_abs] at h1
    rw [abs_div, abs_of_pos (by linarith [h.1] : (0:ℝ) < ξ)]
    calc |deriv chiPlus ξ| / ξ ≤ |deriv chiPlus ξ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos h.1
      _ ≤ max K 0 := by rw [div_one]; exact h1.trans (le_max_left _ _)
  · rw [hz h, abs_zero]; exact le_max_right _ _

/-- The symbol `m = -a_{-2} e^{-iΦ₀}` of `f_{0,+}`. -/
def c04_aux_mplus (p ξ : ℝ) : ℂ :=
  -(((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))))

theorem c04_aux_mplus_zero (p : ℝ) {ξ : ℝ} (h : ξ ≤ 1) : c04_aux_mplus p ξ = 0 := by
  unfold c04_aux_mplus; rw [c04_aux_seed_chi_zero h]; simp

theorem c04_aux_E_hasDeriv (p : ℝ) (hp : 0 < p) (ξ : ℝ) :
    HasDerivAt (fun ξ : ℝ => Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))))
      (-(Complex.I * ((|ξ| ^ p : ℝ) : ℂ)) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) ξ := by
  have h1 : HasDerivAt (fun ξ : ℝ => -(Complex.I * (Phi0 p ξ : ℂ))) (-(Complex.I * ((|ξ| ^ p : ℝ) : ℂ))) ξ :=
    ((c04_aux_seed_Phi0_hasDeriv p hp ξ).ofReal_comp.const_mul Complex.I).neg
  convert h1.cexp using 1; ring

theorem c04_aux_mplus_hasDeriv (p : ℝ) (hp : 0 < p) (ξ : ℝ) (hξ : 0 < ξ) :
    HasDerivAt (c04_aux_mplus p)
      (-((((deriv chiPlus ξ / ξ ^ 2 - 2 * chiPlus ξ / ξ ^ 3) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) +
        ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * (-(Complex.I * ((|ξ| ^ p : ℝ) : ℂ)) *
          Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))))) ξ := by
  have hc := (c04_aux_seed_chi_smooth.differentiable (by simp) ξ).hasDerivAt
  have ha : HasDerivAt (fun ξ : ℝ => chiPlus ξ / ξ ^ 2)
      (deriv chiPlus ξ / ξ ^ 2 - 2 * chiPlus ξ / ξ ^ 3) ξ := by
    have hp2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ξ) ξ := by simpa using hasDerivAt_pow 2 ξ
    have := hc.div hp2 (pow_ne_zero 2 hξ.ne')
    convert this using 1
    field_simp
  exact ((ha.ofReal_comp).mul (c04_aux_E_hasDeriv p hp ξ)).neg

theorem c04_aux_mplus_deriv (p : ℝ) (hp : 0 < p) (ξ : ℝ) :
    deriv (c04_aux_mplus p) ξ = if 0 < ξ then
      -((((deriv chiPlus ξ / ξ ^ 2 - 2 * chiPlus ξ / ξ ^ 3) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) +
        ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * (-(Complex.I * ((|ξ| ^ p : ℝ) : ℂ)) *
          Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))))) else 0 := by
  split_ifs with h
  · exact (c04_aux_mplus_hasDeriv p hp ξ h).deriv
  · have : c04_aux_mplus p =ᶠ[𝓝 ξ] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show ξ < 1 by linarith [not_lt.mp h])] with t ht
      exact c04_aux_mplus_zero p (le_of_lt ht)
    rw [this.deriv_eq, deriv_const]

/-- `n = ξ m' + (2 + iξ|ξ|^p) m = -χ₊'(ξ)/ξ · e^{-iΦ₀}`. -/
theorem c04_aux_mplus_n (p : ℝ) (hp : 0 < p) (ξ : ℝ) :
    (ξ : ℂ) * deriv (c04_aux_mplus p) ξ + (2 + Complex.I * ((ξ * |ξ| ^ p : ℝ) : ℂ)) * c04_aux_mplus p ξ =
      -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) := by
  rw [c04_aux_mplus_deriv p hp ξ]
  split_ifs with h
  · unfold c04_aux_mplus
    have hξ : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
    rw [abs_of_pos h]
    push_cast
    field_simp
    ring
  · have h1 : ξ < 1 := by linarith [not_lt.mp h]
    rw [c04_aux_mplus_zero p h1.le, c04_aux_dchi_zero ξ (Or.inl h1)]
    simp

/-- Blueprint: lem:c04_L0_f0plus.  `ℒ₀ f_{0,+} = -Γ₊` pointwise on `ℝ`. -/
theorem c04_L0_f0plus (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ y, c04_L0C p (c04_linear_seed_plus p) y = -c04_linear_seed_Gamma_plus p y := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hw, -⟩ := c04_weak_L0 p hp hp1
  obtain ⟨-, haint, -, -, -, -⟩ := c04_seed_integrable p hp hp1
  obtain ⟨-, -, hsm, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨Cg, hCg, hglob⟩ := c04_f0plus_global p hp hp1
  set m := c04_aux_mplus p with hm
  set E : ℝ → ℂ := fun ξ => Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) with hE
  have hEn : ∀ ξ, ‖E ξ‖ = 1 := fun ξ => by
    simp only [hE]
    rw [show -(Complex.I * (Phi0 p ξ : ℂ)) = ((-Phi0 p ξ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hEC : ContDiff ℝ 1 E :=
    Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (c04_aux_seed_Phi0_C1 p hp0))).neg
  have hmC : ContDiff ℝ 1 m := by
    have : m = fun ξ => -(((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * E ξ) := rfl
    rw [this]
    exact ((Complex.ofRealCLM.contDiff.comp (c04_aux_seed_a2_smooth.of_le
      (by exact_mod_cast le_top))).mul hEC).neg
  have hmint : Integrable m := by
    refine haint.norm.mono' hmC.continuous.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    simp only [hm, c04_aux_mplus, norm_neg, norm_mul]
    rw [show Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) = E ξ from rfl, hEn, mul_one]
  -- boundedness of `m`, `m'`
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (c04_aux_seed_chi_smooth.continuous_deriv (by exact_mod_cast le_top)).continuousOn
  have hdchi : ∀ ξ, |deriv chiPlus ξ| ≤ |B| := by
    intro ξ
    by_cases h : ξ ∈ Icc (1 : ℝ) 2
    · exact (Real.norm_eq_abs _ ▸ hB ξ h).trans (le_abs_self B)
    · rw [c04_aux_dchi_zero ξ (by
        simp only [mem_Icc, not_and_or, not_le] at h; exact h), abs_zero]
      exact abs_nonneg _
  have hmb : ∀ ξ, ‖m ξ‖ + ‖deriv m ξ‖ ≤ (|B| + 4) * jb ξ ^ (0 : ℝ) := by
    intro ξ
    rw [rpow_zero, mul_one]
    by_cases h1 : 1 ≤ ξ
    · have h0 : 0 < ξ := by linarith
      rw [c04_aux_mplus_deriv p hp0 ξ, ite_cond_eq_true _ _ (eq_true h0)]
      simp only [hm, c04_aux_mplus, norm_neg, norm_mul, norm_add_le]
      rw [show Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) = E ξ from rfl, hEn, mul_one]
      have hξ2 : 1 ≤ ξ ^ 2 := by nlinarith
      have hξ3 : 1 ≤ ξ ^ 3 := by nlinarith
      have hc := c04_aux_seed_chi_mem ξ
      have ha : ‖((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg hc.1,
          abs_of_pos (by positivity)]
        exact div_le_one_of_le₀ (hc.2.trans hξ2) (by positivity)
      have hd : ‖((deriv chiPlus ξ / ξ ^ 2 - 2 * chiPlus ξ / ξ ^ 3 : ℝ) : ℂ)‖ ≤ |B| + 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ξ ^ 2)]
          exact (div_le_self (abs_nonneg _) hξ2).trans (hdchi ξ)
        · rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ξ ^ 3), abs_mul, abs_two,
            abs_of_nonneg hc.1]
          exact (div_le_self (by linarith [hc.1]) hξ3).trans (by linarith [hc.2])
      have hI : ‖-(Complex.I * ((|ξ| ^ p : ℝ) : ℂ))‖ * ‖((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
        rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0, abs_of_pos (rpow_pos_of_pos h0 _),
          abs_div, abs_of_nonneg hc.1, abs_of_pos (by positivity : (0:ℝ) < ξ ^ 2)]
        rw [mul_div_assoc', div_le_one (by positivity)]
        have : ξ ^ p ≤ ξ ^ (2 : ℝ) := rpow_le_rpow_of_exponent_le h1 (by linarith)
        rw [rpow_two] at this
        nlinarith [hc.1, hc.2, rpow_pos_of_pos h0 p]
      calc ‖((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ)‖ + ‖((deriv chiPlus ξ / ξ ^ 2 - 2 * chiPlus ξ / ξ ^ 3 : ℝ) : ℂ) * E ξ +
            ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) * (-(Complex.I * ((|ξ| ^ p : ℝ) : ℂ)) * E ξ)‖
          ≤ 1 + ((|B| + 2) + 1) := by
            refine add_le_add ha ((norm_add_le _ _).trans (add_le_add ?_ ?_))
            · rw [norm_mul, hEn, mul_one]; exact hd
            · rw [norm_mul, norm_mul, hEn, mul_one, mul_comm]; exact hI
        _ = |B| + 4 := by ring
    · have h1' : ξ < 1 := not_le.mp h1
      have hm0 : m ξ = 0 := c04_aux_mplus_zero p h1'.le
      have hd0 : deriv m ξ = 0 := by
        have : m =ᶠ[𝓝 ξ] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds h1'] with t ht
          exact c04_aux_mplus_zero p (le_of_lt ht)
        rw [this.deriv_eq, deriv_const]
      rw [hm0, hd0, norm_zero, add_zero]
      positivity
  -- the function `n`
  have hn : (fun ξ : ℝ => (ξ : ℂ) * deriv m ξ + (2 + Complex.I * ((ξ * |ξ| ^ p : ℝ) : ℂ)) * m ξ) =
      fun ξ => -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) * E ξ) := funext (c04_aux_mplus_n p hp0)
  have hdc : Continuous (fun ξ : ℝ => deriv chiPlus ξ / ξ) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases lt_or_ge x (1 / 2) with hx | hx
    · have : (fun ξ : ℝ => deriv chiPlus ξ / ξ) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with t ht
        rw [c04_aux_dchi_zero t (Or.inl (by linarith [mem_Iio.mp ht])), zero_div]
      exact continuousAt_const.congr this.symm
    · exact ((c04_aux_seed_chi_smooth.continuous_deriv (by exact_mod_cast le_top)).continuousAt).div
        continuousAt_id (by simp; linarith)
  have hncs : HasCompactSupport (fun ξ : ℝ => -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) * E ξ)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro ξ hξ
    by_contra h
    apply hξ
    show -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) * E ξ) = 0
    rw [c04_aux_dchi_zero ξ (by simp only [mem_Icc, not_and_or, not_le] at h; exact h)]
    simp
  have hnint : Integrable (fun ξ : ℝ => -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) * E ξ)) :=
    ((Complex.continuous_ofReal.comp hdc).mul hEC.continuous).neg.integrable_of_hasCompactSupport hncs
  -- `m̌ = f_{0,+}` and `ň = -Γ₊`
  have hvan : ∀ (g : ℝ → ℂ), (∀ ξ, ξ ≤ 0 → g ξ = 0) → ∀ y : ℝ,
      ∫ ξ, g ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
        ∫ ξ in Ioi (0 : ℝ), g ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
    intro g hg y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_).symm
    rw [hg ξ (not_lt.mp hξ), zero_mul]
  have hexp : ∀ y ξ : ℝ, E ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
      Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) := by
    intro y ξ; simp only [hE]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hinv : invFourierT m = c04_linear_seed_plus p := by
    funext y
    unfold invFourierT c04_linear_seed_plus
    rw [hvan m (fun ξ hξ => c04_aux_mplus_zero p (by linarith)) y]
    have : ∫ ξ in Ioi (0 : ℝ), m ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
        ∫ ξ in Ioi (0 : ℝ), -(((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ))) := by
      congr 1; funext ξ
      simp only [hm, c04_aux_mplus]
      rw [neg_mul, mul_assoc, show Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) = E ξ from rfl, hexp]
    rw [this, integral_neg]; ring
  have hinvn : invFourierT (fun ξ : ℝ => -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) * E ξ)) =
      fun y => -c04_linear_seed_Gamma_plus p y := by
    funext y
    unfold invFourierT c04_linear_seed_Gamma_plus
    rw [hvan _ (fun ξ hξ => by
      rw [c04_aux_dchi_zero ξ (Or.inl (by linarith))]; simp) y]
    have : ∫ ξ in Ioi (0 : ℝ), -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) * E ξ) *
          Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
        ∫ ξ in Ioi (0 : ℝ), -(((deriv chiPlus ξ / ξ : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ))) := by
      congr 1; funext ξ
      rw [neg_mul, mul_assoc, hexp]
    rw [this, integral_neg]; ring
  intro y
  have key := hw m hmC hmint ⟨1, one_pos, fun ξ hξ => c04_aux_mplus_zero p
      (by linarith [(abs_lt.mp hξ).2])⟩ ⟨|B| + 4, 0, hmb⟩ (by rw [hn]; exact hnint)
    (by rw [hinv]; exact hsm.of_le (by norm_cast))
    ⟨Cg, fun y => by rw [hinv]; linarith [(hglob y).1, norm_nonneg (deriv (c04_linear_seed_plus p) y)]⟩
    ⟨Cg, fun y => by rw [hinv]; linarith [(hglob y).1, norm_nonneg (c04_linear_seed_plus p y)]⟩
    ⟨Cg, 2 / p, fun y => by
      rw [hinv]; linarith [(hglob y).2, norm_nonneg (iteratedDeriv 3 (c04_linear_seed_plus p) y)]⟩ y
  rw [hinv, hn, hinvn] at key
  exact key

/-- Integrability of the `|D|^p` integrand for a bounded `C¹` real function. -/
theorem c04_aux_frac_int_C1 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (M : ℝ) (hM : ∀ z, |g z| ≤ M) (y : ℝ) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) := by
  obtain ⟨K, hK⟩ := (hg.locallyLipschitz.locallyLipschitzOn (s := Icc (y - 1) (y + 1))).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  refine c04_aux_c01_frac_integrable p hp hp1 g hg.continuous.aestronglyMeasurable M
    (Filter.Eventually.of_forall hM) y K K.2 (fun z hz w hw => ?_) |>.1
  have := hK.dist_le_mul z hz w hw
  simpa [Real.dist_eq] using this

/-- Integrability of the complex `|D|^p` integrand for a bounded `C¹` complex function. -/
theorem c04_aux_fracC_int_C1 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (M : ℝ) (hM : ∀ z, ‖g z‖ ≤ M) (y : ℝ) :
    Integrable (fun z => (g y - g z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) := by
  refine Integrable.re_im_iff.mp ⟨?_, ?_⟩
  · have := c04_aux_frac_int_C1 p hp hp1 (fun t => (g t).re) (Complex.reCLM.contDiff.comp hg) M
      (fun z => (Complex.abs_re_le_norm _).trans (hM z)) y
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.div_ofReal_re]
  · have := c04_aux_frac_int_C1 p hp hp1 (fun t => (g t).im) (Complex.imCLM.contDiff.comp hg) M
      (fun z => (Complex.abs_im_le_norm _).trans (hM z)) y
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.div_ofReal_im]

/-- `ℒ₀(f + Re G) = ℒ₀ f + Re ℒ₀ G` for `f ∈ 𝒜 ∩ C²`, `G ∈ C²` with `G'` bounded. -/
theorem c04_aux_L0_add_re (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : ℝ → ℝ)
    (hf : f ∈ c01_admissible_class) (hf2 : ContDiff ℝ 2 f) (G : ℝ → ℂ) (hG : ContDiff ℝ 2 G)
    (M : ℝ) (hGb : ∀ y, ‖deriv G y‖ ≤ M) (y : ℝ) :
    L0 p (fun t => f t + (G t).re) y = L0 p f y + (c04_L0C p G y).re := by
  have hfd : Differentiable ℝ f := hf2.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hder : deriv (fun t => f t + (G t).re) = fun t => deriv f t + (deriv G t).re := by
    funext t
    have h2 : HasDerivAt (fun t => (G t).re) (deriv G t).re t :=
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hGd t).hasDerivAt)
    exact ((hfd t).hasDerivAt.add h2).deriv
  obtain ⟨Mf, hMf⟩ := hf.2.1
  have hf'1 : ContDiff ℝ 1 (deriv f) := hf2.deriv'
  have hG'1 : ContDiff ℝ 1 (deriv G) := hG.deriv'
  have hi1 := c04_aux_frac_int_C1 p hp hp1 (deriv f) hf'1 Mf hMf y
  have hi2 := c04_aux_frac_int_C1 p hp hp1 (fun t => (deriv G t).re)
    (Complex.reCLM.contDiff.comp hG'1) M (fun z => (Complex.abs_re_le_norm _).trans (hGb z)) y
  have hiC := c04_aux_fracC_int_C1 p hp hp1 (deriv G) hG'1 M hGb y
  unfold L0 fracDdy c04_L0C fracD fracDC
  rw [hder]
  have hsplit : (fun z => (deriv f y + (deriv G y).re - (deriv f z + (deriv G z).re)) /
      |y - z| ^ (p + 1)) = fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) +
        ((deriv G y).re - (deriv G z).re) / |y - z| ^ (p + 1) := by
    funext z; ring
  rw [hsplit, integral_add hi1 hi2]
  have hre : ∫ z, ((deriv G y).re - (deriv G z).re) / |y - z| ^ (p + 1) =
      (∫ z, (deriv G y - deriv G z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)).re := by
    rw [show (∫ z, (deriv G y - deriv G z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)).re =
      RCLike.re (∫ z, (deriv G y - deriv G z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) from rfl,
      ← integral_re hiC]
    congr 1; funext z
    simp [Complex.div_ofReal_re]
  rw [hre]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `|D|^p` commutes with the embedding `ℝ → ℂ`. -/
theorem c04_aux_fracD_ofReal (p : ℝ) (u : ℝ → ℝ) (y : ℝ) :
    fracDC p (fun t => (u t : ℂ)) y = ((fracD p u y : ℝ) : ℂ) := by
  unfold fracDC fracD
  rw [Complex.ofReal_mul, ← integral_complex_ofReal]
  refine congrArg (fun I => (calpha p : ℂ) * I) (integral_congr_ae (Eventually.of_forall fun z => ?_))
  simp only []; push_cast; rfl

/-- Real version of lem:c04_frac_derivative: `(|D|^p u)' = |D|^p u'`. -/
theorem c04_aux_fracD_deriv (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (M0 M1 : ℝ) (h0 : ∀ y, |u y| ≤ M0) (h1 : ∀ y, |deriv u y| ≤ M1)
    (y : ℝ) : deriv (fracD p u) y = fracD p (deriv u) y := by
  set g : ℝ → ℂ := fun t => (u t : ℂ) with hgdef
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hu
  have hdg : deriv g = fun t => ((deriv u t : ℝ) : ℂ) := by
    funext t; exact ((hu.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv
  obtain ⟨hC1, hD⟩ := c04_frac_derivative p hp hp1 g hg ⟨M0, fun y => by simpa [hgdef] using h0 y⟩
    ⟨M1, fun y => by rw [hdg]; simpa using h1 y⟩
  have hfun : fracDC p g = fun y => ((fracD p u y : ℝ) : ℂ) := funext (c04_aux_fracD_ofReal p u)
  have hFd : DifferentiableAt ℝ (fracD p u) y := by
    have e : fracD p u = fun y => (fracDC p g y).re := by funext y; rw [hfun]; simp
    rw [e]
    exact (Complex.reCLM.differentiableAt.comp y ((hC1.differentiable (by simp)) y))
  have := hD y
  rw [hfun, hdg, c04_aux_fracD_ofReal, hFd.hasDerivAt.ofReal_comp.deriv] at this
  exact_mod_cast this

/-- `y^{-a} ≤ 16 ⟨y⟩^{-a}` for `y ≥ 1`, `0 ≤ a ≤ 4`. -/
theorem c04_aux_rpow_le_jb (y a : ℝ) (hy : 1 ≤ y) (_ha0 : 0 ≤ a) (ha : a ≤ 4) :
    y ^ (-a) ≤ 16 * jb y ^ (-a) := by
  have hjb : 0 < jb y := Real.sqrt_pos.mpr (by positivity)
  have hjb2 : jb y / 2 ≤ y := by
    unfold jb
    rw [div_le_iff₀ two_pos, Real.sqrt_le_left (by linarith)]
    nlinarith
  have h1 : y ^ (-a) ≤ (jb y / 2) ^ (-a) := rpow_le_rpow_of_nonpos (by positivity) hjb2 (by linarith)
  rw [div_rpow hjb.le (by norm_num)] at h1
  have h2 : (2 : ℝ) ^ (-(4 : ℝ)) ≤ 2 ^ (-a) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
    rw [rpow_neg (by norm_num), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
  have h4 : 0 < (2 : ℝ) ^ (-a) := by positivity
  have h5 : 0 ≤ jb y ^ (-a) := by positivity
  calc y ^ (-a) ≤ jb y ^ (-a) / 2 ^ (-a) := h1
    _ ≤ jb y ^ (-a) / (1 / 16) := by
        rw [h3] at h2
        exact div_le_div_of_nonneg_left h5 (by norm_num) h2
    _ = 16 * jb y ^ (-a) := by ring

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := by
  unfold jb
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + y ^ 2 by nlinarith [sq_nonneg y])
  simpa using this

/-- `C¹` regularity of `|D|^p u` (real version of lem:c04_frac_derivative). -/
theorem c04_aux_fracD_C1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (M0 M1 : ℝ) (h0 : ∀ y, |u y| ≤ M0) (h1 : ∀ y, |deriv u y| ≤ M1) :
    ContDiff ℝ 1 (fracD p u) := by
  set g : ℝ → ℂ := fun t => (u t : ℂ) with hgdef
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hu
  have hdg : deriv g = fun t => ((deriv u t : ℝ) : ℂ) := by
    funext t; exact ((hu.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv
  obtain ⟨hC1, -⟩ := c04_frac_derivative p hp hp1 g hg ⟨M0, fun y => by simpa [hgdef] using h0 y⟩
    ⟨M1, fun y => by rw [hdg]; simpa using h1 y⟩
  have hfun : fracDC p g = fun y => ((fracD p u y : ℝ) : ℂ) := funext (c04_aux_fracD_ofReal p u)
  have e : fracD p u = fun y => (fracDC p g y).re := by funext y; rw [hfun]; simp
  rw [e]
  exact Complex.reCLM.contDiff.comp hC1

/-- `f_{0,low}'` is bounded. -/
theorem c04_aux_flow_deriv_bdd (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ M : ℝ, ∀ y, |deriv (c04_linear_seed_low p) y| ≤ M := by
  obtain ⟨hlsm, -, -, -, -, -⟩ := c04_seed_low_derivatives p hp hp1
  obtain ⟨-, -, -, hcd⟩ := c04_seed_corner_decomposition p hp hp1
  obtain ⟨hI1s, hI1b⟩ := c04_I1_bound p hp hp1
  obtain ⟨hI2s, hI2b⟩ := c04_I2_bound
  obtain ⟨C1, hC1, h1⟩ := hI1b 1
  obtain ⟨C2, hC2, h2⟩ := hI2b 1 0 le_rfl
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hlsm.continuous_deriv (by exact_mod_cast le_top)).continuousOn
  have hfeq : c04_linear_seed_low p = fun t => corner t + c04_I1 p t + c04_I2 t := by
    funext t; have := (hcd t).2.2; linarith
  refine ⟨|K| + 1 + C1 + C2, fun y => ?_⟩
  by_cases hy : |y| ≤ 1
  · have := hK y (abs_le.mp hy)
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self K]
  · push_neg at hy
    have hy0 : y ≠ 0 := by intro h; rw [h, abs_zero] at hy; linarith
    have hW : HasDerivAt corner (if y < 0 then -1 else 0) y := by
      rcases lt_or_gt_of_ne hy0 with h | h
      · have : corner =ᶠ[𝓝 y] fun x => -x := by
          filter_upwards [Iio_mem_nhds h] with x hx
          unfold corner; rw [max_eq_left (by linarith [mem_Iio.mp hx])]
        rw [ite_cond_eq_true _ _ (eq_true h)]
        exact (hasDerivAt_neg y).congr_of_eventuallyEq this
      · have : corner =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [Ioi_mem_nhds h] with x hx
          unfold corner; rw [max_eq_right (by linarith [mem_Ioi.mp hx])]
        rw [ite_cond_eq_false _ _ (eq_false (not_lt.mpr h.le))]
        exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq this
    have hd1 : DifferentiableAt ℝ (c04_I1 p) y := hI1s.differentiable (by simp) y
    have hd2 : DifferentiableAt ℝ c04_I2 y :=
      ((hI2s.contDiffAt (isOpen_compl_singleton.mem_nhds hy0)).differentiableAt (by simp))
    have hD : HasDerivAt (fun t => corner t + c04_I1 p t + c04_I2 t) _ y :=
      (hW.add hd1.hasDerivAt).add hd2.hasDerivAt
    rw [hfeq, hD.deriv]
    have e1 := h1 y hy.le
    have e2 := h2 y hy.le
    simp only [iteratedDeriv_one, neg_zero, rpow_zero, mul_one, Nat.cast_one] at e1 e2
    have hy1 : |y| ^ (-p - 1) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hy.le (by linarith)
    have e1' : |deriv (c04_I1 p) y| ≤ C1 := e1.trans (by nlinarith)
    have hc : |(if y < 0 then (-1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc _ ≤ |(if y < 0 then (-1 : ℝ) else 0) + deriv (c04_I1 p) y| + |deriv c04_I2 y| := abs_add_le _ _
      _ ≤ 1 + C1 + C2 := by linarith [abs_add_le (if y < 0 then (-1 : ℝ) else 0) (deriv (c04_I1 p) y)]
      _ ≤ _ := by linarith [abs_nonneg K]

/-- Integral of a Hermitian integrand: `∫ f = 2 Re ∫₀^∞ f`. -/
theorem c04_aux_herm_integral (f : ℝ → ℂ) (hf : Integrable f) (hneg : ∀ ξ, f (-ξ) = conj (f ξ)) :
    ∫ ξ, f ξ = ((2 * (∫ ξ in Ioi (0 : ℝ), f ξ).re : ℝ) : ℂ) := by
  have hleft : ∫ ξ in Iic (0 : ℝ), f ξ = conj (∫ ξ in Ioi (0 : ℝ), f ξ) := by
    have e1 : ∫ ξ in Iic (0 : ℝ), f ξ = ∫ ξ in Iic (0 : ℝ), (fun x => conj (f x)) (-ξ) :=
      setIntegral_congr_fun measurableSet_Iic (fun ξ _ => by
        show f ξ = conj (f (-ξ)); rw [hneg, Complex.conj_conj])
    rw [e1, integral_comp_neg_Iic (0 : ℝ) (fun x => conj (f x)), neg_zero]
    exact integral_conj
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hf.integrableOn hf.integrableOn, hleft,
    add_comm, Complex.add_conj]

/-- The even cutoff `1 - χ₊(|ξ|)`. -/
theorem c04_aux_cut_deriv_pos (ξ : ℝ) (hξ : 0 < ξ) :
    deriv (fun t : ℝ => 1 - chiPlus |t|) ξ = -deriv chiPlus ξ := by
  have hev : (fun t : ℝ => 1 - chiPlus |t|) =ᶠ[𝓝 ξ] fun t => 1 - chiPlus t := by
    filter_upwards [Ioi_mem_nhds hξ] with t ht
    rw [abs_of_pos (mem_Ioi.mp ht)]
  rw [hev.deriv_eq, deriv_const_sub]

theorem c04_aux_cut_deriv_neg (ξ : ℝ) :
    deriv (fun t : ℝ => 1 - chiPlus |t|) (-ξ) = -deriv (fun t : ℝ => 1 - chiPlus |t|) ξ := by
  have hd := ((c04_aux_seed_cut_smooth.differentiable (by simp) (-ξ)).hasDerivAt).comp ξ
    (hasDerivAt_neg ξ)
  have heq : ((fun t : ℝ => 1 - chiPlus |t|) ∘ fun t => -t) = fun t => 1 - chiPlus |t| := by
    funext t; simp [abs_neg]
  rw [heq] at hd
  have := hd.deriv
  linarith

/-- `n_b = |ξ|^p m_low - i m_low' = -i (1-χ₊(|·|))' e^{-iΦ₀}`. -/
theorem c04_aux_nb_eq (p : ℝ) (hp : 0 < p) (ξ : ℝ) :
    ((|ξ| ^ p : ℝ) : ℂ) * c04_m_low p ξ - Complex.I * deriv (c04_m_low p) ξ =
      -(Complex.I * ((deriv (fun t : ℝ => 1 - chiPlus |t|) ξ : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) := by
  have hc : HasDerivAt (fun t : ℝ => ((1 - chiPlus |t| : ℝ) : ℂ))
      ((deriv (fun t : ℝ => 1 - chiPlus |t|) ξ : ℝ) : ℂ) ξ :=
    ((c04_aux_seed_cut_smooth.differentiable (by simp) ξ).hasDerivAt).ofReal_comp
  have hm : HasDerivAt (c04_m_low p) _ ξ := hc.mul (c04_aux_E_hasDeriv p hp ξ)
  rw [hm.deriv]
  unfold c04_m_low
  ring_nf
  rw [Complex.I_sq]
  ring

theorem c04_aux_L0C_two (p : ℝ) (g : ℝ → ℂ) (hg : Differentiable ℝ g) (y : ℝ) :
    c04_L0C p (fun t => 2 * g t) y = 2 * c04_L0C p g y := by
  unfold c04_L0C fracDC
  have hd : deriv (fun t => 2 * g t) = fun t => 2 * deriv g t :=
    funext fun t => ((hg t).hasDerivAt.const_mul (2 : ℂ)).deriv
  rw [hd]
  have : (fun z => (2 * deriv g y - 2 * deriv g z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) =
      fun z => 2 * ((deriv g y - deriv g z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) := by
    funext z; ring
  rw [this, integral_const_mul]
  ring

/-- Blueprint: lem:c04_L0_f0_constant.  `f₀ ∈ 𝒜`, `ℒ₀ f₀ ∈ C¹` and `(ℒ₀ f₀)' ≡ 0`. -/
theorem c04_L0_f0_constant (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    c04_linear_seed p ∈ c01_admissible_class ∧ ContDiff ℝ 1 (L0 p (c04_linear_seed p)) ∧
      ∀ y, deriv (L0 p (c04_linear_seed p)) y = 0 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, hw2⟩ := c04_weak_L0 p hp hp1
  obtain ⟨-, -, hpsm, -, -, -, -, -, -, -, -, -, -, -, hsum, hf0sm⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨hlsm, -, -, -, -, hlbd⟩ := c04_seed_low_derivatives p hp hp1
  obtain ⟨hmC1, hmcs, -, hmherm, -, hmF, -⟩ := c04_seed_low_fourier p hp hp1
  obtain ⟨Cg, hCg, hglob⟩ := c04_f0plus_global p hp hp1
  obtain ⟨M1, hM1⟩ := c04_aux_flow_deriv_bdd p hp hp1
  obtain ⟨M2, hM2pos, hM2⟩ := hlbd 2 le_rfl
  obtain ⟨M3, hM3pos, hM3⟩ := hlbd 3 (by norm_num)
  set fl := c04_linear_seed_low p with hfl
  set fp := c04_linear_seed_plus p with hfp
  have hfl2 : ContDiff ℝ 2 fl := hlsm.of_le (by norm_cast)
  have hfl1 : ContDiff ℝ 1 (deriv fl) := (contDiff_infty_iff_deriv.mp hlsm).2.of_le (by norm_cast)
  have hfladm : fl ∈ c01_admissible_class :=
    ⟨hlsm.of_le (by norm_cast), ⟨M1, hM1⟩, hfl1.locallyLipschitz⟩
  have hdd : deriv (deriv fl) = iteratedDeriv 2 fl := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hddd : deriv (iteratedDeriv 2 fl) = iteratedDeriv 3 fl := (iteratedDeriv_succ).symm
  -- the decomposition `L0 f0 = L0 f_low - 2 Re Γ₊`
  have hf0eq : c04_linear_seed p = fun t => fl t + ((fun t => 2 * fp t) t).re := by
    funext t; rw [hsum t]; simp
  have hG2 : ContDiff ℝ 2 (fun t => 2 * fp t) := contDiff_const.mul (hpsm.of_le (by norm_cast))
  have hGb : ∀ y, ‖deriv (fun t => 2 * fp t) y‖ ≤ 2 * Cg := by
    intro y
    rw [((hpsm.differentiable (by simp) y).hasDerivAt.const_mul (2 : ℂ)).deriv, norm_mul]
    have := (hglob y).1
    rw [show ‖(2 : ℂ)‖ = 2 by simp]
    linarith [norm_nonneg (fp y)]
  have hL0eq : L0 p (c04_linear_seed p) = fun y => L0 p fl y - 2 * (c04_linear_seed_Gamma_plus p y).re := by
    funext y
    rw [hf0eq, c04_aux_L0_add_re p hp0 hp1 fl hfladm hfl2 _ hG2 (2 * Cg) hGb y,
      c04_aux_L0C_two p fp (hpsm.differentiable (by simp)) y, c04_L0_f0plus p hp hp1 y]
    simp; ring
  -- derivative of `L0 f_low`
  have hu0 : ∀ y, |deriv fl y| ≤ M1 := hM1
  have hu1 : ∀ y, |deriv (deriv fl) y| ≤ M2 := fun y => by rw [hdd]; exact hM2 y
  have hu2 : ContDiff ℝ 2 (deriv fl) := (contDiff_infty_iff_deriv.mp hlsm).2.of_le (by norm_cast)
  have hfrC := c04_aux_fracD_C1 p hp hp1 (deriv fl) hu2 M1 M2 hu0 hu1
  have hL0fl : ∀ y, HasDerivAt (L0 p fl)
      (fracD p (iteratedDeriv 2 fl) y - y * iteratedDeriv 2 fl y) y := by
    intro y
    have h1 : HasDerivAt (fracD p (deriv fl)) (fracD p (iteratedDeriv 2 fl) y) y := by
      have := (hfrC.differentiable (by norm_num) y).hasDerivAt
      rwa [c04_aux_fracD_deriv p hp hp1 (deriv fl) hu2 M1 M2 hu0 hu1 y, hdd] at this
    have h2 : HasDerivAt fl (deriv fl y) y := (hlsm.differentiable (by simp) y).hasDerivAt
    have h3 : HasDerivAt (deriv fl) (iteratedDeriv 2 fl y) y := by
      have := (hfl1.differentiable (by norm_num) y).hasDerivAt; rwa [hdd] at this
    have h4 := (h1.add h2).sub ((hasDerivAt_id y).mul h3)
    have e : L0 p fl = fun y => fracD p (deriv fl) y + fl y - id y * deriv fl y := by
      funext t; unfold L0 fracDdy; rfl
    rw [e]
    convert h4 using 1
    simp only [id]; ring
  -- `(|D|^p - y) f_low'' = Re ň_b`
  set nb : ℝ → ℂ := fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * c04_m_low p ξ - Complex.I * deriv (c04_m_low p) ξ
    with hnb
  have hinvm : invFourierT (c04_m_low p) = fun t => ((iteratedDeriv 2 fl t : ℝ) : ℂ) :=
    funext fun t => (hmF t).symm
  have hf2sm : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 fl) := by
    rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv 2 hlsm
  have hE1 : ∀ y, fracD p (iteratedDeriv 2 fl) y - y * iteratedDeriv 2 fl y = (invFourierT nb y).re := by
    intro y
    have h := hw2 (c04_m_low p) hmC1 hmcs
      (by rw [hinvm]; exact Complex.ofRealCLM.contDiff.comp (hf2sm.of_le (by norm_cast)))
      ⟨M2, fun t => by rw [hinvm]; simp only [Complex.norm_real, Real.norm_eq_abs]; exact hM2 t⟩
      ⟨M3, 0, fun t => by
        rw [hinvm, rpow_zero, mul_one]
        have := ((hf2sm.differentiable (by simp) t).hasDerivAt.ofReal_comp).deriv
        rw [this, hddd, Complex.norm_real, Real.norm_eq_abs]; exact hM3 t⟩ y
    rw [hinvm, c04_aux_fracD_ofReal] at h
    have := congrArg Complex.re h
    simpa using this
  -- `Γ₊` and its derivative
  set g : ℝ → ℂ := fun ξ => ((deriv chiPlus ξ / ξ : ℝ) : ℂ) with hg
  have hdc : Continuous (fun ξ : ℝ => deriv chiPlus ξ / ξ) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases lt_or_ge x (1 / 2) with hx | hx
    · have : (fun ξ : ℝ => deriv chiPlus ξ / ξ) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with t ht
        rw [c04_aux_dchi_zero t (Or.inl (by linarith [mem_Iio.mp ht])), zero_div]
      exact continuousAt_const.congr this.symm
    · exact ((c04_aux_seed_chi_smooth.continuous_deriv (by exact_mod_cast le_top)).continuousAt).div
        continuousAt_id (by simp; linarith)
  have hgc : Continuous g := Complex.continuous_ofReal.comp hdc
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro ξ hξ
    by_contra h
    apply hξ
    show ((deriv chiPlus ξ / ξ : ℝ) : ℂ) = 0
    rw [c04_aux_dchi_zero ξ (by simp only [mem_Icc, not_and_or, not_le] at h; exact h)]
    simp
  have hGam : c04_linear_seed_Gamma_plus p =
      fun y => ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ in Ioi (0 : ℝ), g ξ * c04_eiphase p y ξ := rfl
  set J : ℝ → ℂ := fun y => ∫ ξ in Ioi (0 : ℝ), (Complex.I * (ξ : ℂ) * g ξ) * c04_eiphase p y ξ
    with hJ
  have hGd : ∀ y, HasDerivAt (c04_linear_seed_Gamma_plus p) (((2 * π : ℝ) : ℂ)⁻¹ * J y) y := by
    intro y; rw [hGam]; exact (c04o_aux_param_hasDeriv p hp0 hgc hgcs y).const_mul _
  -- `ň_b = π⁻¹ Re J`
  have hnbF : ∀ y, invFourierT nb y = ((2 * π : ℝ) : ℂ)⁻¹ * ((2 * (J y).re : ℝ) : ℂ) := by
    intro y
    have hnbe : ∀ ξ, nb ξ = -(Complex.I * ((deriv (fun t : ℝ => 1 - chiPlus |t|) ξ : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) := fun ξ => c04_aux_nb_eq p hp0 ξ
    have hcutd : Continuous (deriv (fun t : ℝ => 1 - chiPlus |t|)) :=
      c04_aux_seed_cut_smooth.continuous_deriv (by exact_mod_cast le_top)
    have hcont : Continuous (fun ξ : ℝ => nb ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := by
      have hΦ := c04_aux_seed_Phi0_cont p hp0
      have : (fun ξ : ℝ => nb ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) =
          fun ξ => -(Complex.I * ((deriv (fun t : ℝ => 1 - chiPlus |t|) ξ : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
        funext ξ; rw [hnbe]
      rw [this]; fun_prop
    have hcs : HasCompactSupport (fun ξ : ℝ => nb ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) ?_
      intro ξ hξ
      by_contra h
      apply hξ
      have h2 : 2 < |ξ| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at h
        rcases h with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hz : deriv (fun t : ℝ => 1 - chiPlus |t|) ξ = 0 := by
        have : (fun t : ℝ => 1 - chiPlus |t|) =ᶠ[𝓝 ξ] fun _ => 0 := by
          have hmem : {t : ℝ | 2 < |t|} ∈ 𝓝 ξ := (isOpen_lt continuous_const continuous_abs).mem_nhds h2
          filter_upwards [hmem] with t ht
          rw [c04_aux_seed_chi_one (le_of_lt ht)]; ring
        rw [this.deriv_eq, deriv_const]
      show nb ξ * _ = 0
      rw [hnbe, hz]; simp
    have hint : Integrable (fun ξ : ℝ => nb ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) :=
      hcont.integrable_of_hasCompactSupport hcs
    have hneg : ∀ ξ, nb (-ξ) * Complex.exp (Complex.I * (y : ℂ) * ((-ξ : ℝ) : ℂ)) =
        conj (nb ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := by
      intro ξ
      rw [hnbe, hnbe, c04_aux_cut_deriv_neg, c04_aux_seed_Phi0_neg, map_mul, map_neg, map_mul, map_mul,
        Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_conj, ← Complex.exp_conj]
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring_nf
    have hpos : ∫ ξ in Ioi (0 : ℝ), nb ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) = J y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun ξ (hξ : ξ ∈ Ioi (0 : ℝ)) => ?_
      have hξ0 : (0 : ℝ) < ξ := hξ
      rw [hnbe, c04_aux_cut_deriv_pos ξ hξ0]
      simp only [hg, c04_eiphase]
      have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ0.ne'
      have he : Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) =
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      calc _ = Complex.I * ((deriv chiPlus ξ : ℝ) : ℂ) * (Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) *
            Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := by push_cast; ring
        _ = _ := by rw [he]; push_cast; field_simp
    unfold invFourierT
    rw [c04_aux_herm_integral _ hint hneg, hpos]
  -- assembly
  have hf0d : ∀ y, HasDerivAt (c04_linear_seed p) (deriv fl y + 2 * (deriv fp y).re) y := by
    intro y
    rw [hf0eq]
    have h1 := (hlsm.differentiable (by simp) y).hasDerivAt
    have h2 := c04_aux_seed_re_hasDeriv
      ((hpsm.differentiable (by simp) y).hasDerivAt.const_mul (2 : ℂ))
    convert h1.add h2 using 1
    simp
  have hGsm : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_Gamma_plus p) := by
    rw [hGam]; exact contDiff_const.mul (c04o_aux_param_smooth p hp0 hgc hgcs)
  refine ⟨⟨hf0sm.of_le (by norm_cast), ⟨M1 + 2 * Cg, fun y => ?_⟩,
    ((contDiff_infty_iff_deriv.mp hf0sm).2.of_le (by norm_cast) :
      ContDiff ℝ 1 (deriv (c04_linear_seed p))).locallyLipschitz⟩, ?_, fun y => ?_⟩
  · rw [(hf0d y).deriv]
    have h1 := hM1 y
    have h2 : |(deriv fp y).re| ≤ Cg :=
      (Complex.abs_re_le_norm _).trans (by linarith [(hglob y).1, norm_nonneg (fp y)])
    calc |deriv fl y + 2 * (deriv fp y).re| ≤ |deriv fl y| + |2 * (deriv fp y).re| := abs_add_le _ _
      _ ≤ M1 + 2 * Cg := by rw [abs_mul, abs_two]; linarith
  · rw [hL0eq]
    have e : L0 p fl = fun y => fracD p (deriv fl) y + fl y - y * deriv fl y := by
      funext t; unfold L0 fracDdy; rfl
    rw [e]
    exact ((hfrC.add (hlsm.of_le (by norm_cast))).sub (contDiff_id.mul hfl1)).sub
      (contDiff_const.mul (Complex.reCLM.contDiff.comp (hGsm.of_le (by norm_cast))))
  · rw [hL0eq]
    have hd2 : HasDerivAt (fun y => 2 * (c04_linear_seed_Gamma_plus p y).re)
        (2 * (((2 * π : ℝ) : ℂ)⁻¹ * J y).re) y :=
      (c04_aux_seed_re_hasDeriv (hGd y)).const_mul 2
    have hD : HasDerivAt (fun y => L0 p fl y - 2 * (c04_linear_seed_Gamma_plus p y).re) _ y :=
      (hL0fl y).sub hd2
    rw [hD.deriv, hE1 y, hnbF y, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul, Complex.ofReal_re]
    ring

open MeasureTheory Set Filter Real

/-- `∂^j Re F = Re ∂^j F` for `F` of class `C^j` at `y`. -/
theorem c04_aux_iteratedDeriv_re (F : ℝ → ℂ) (y : ℝ) (j : ℕ) (hF : ContDiffAt ℝ j F y) :
    iteratedDeriv j (fun t => (F t).re) y = (iteratedDeriv j F y).re := by
  have : (fun t => (F t).re) = Complex.reCLM ∘ F := rfl
  rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    Complex.reCLM.iteratedFDeriv_comp_left hF le_rfl]
  simp

/-- A smooth function is `C^j` at every point. -/
theorem c04_aux_smooth_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : ℕ) (y : ℝ) : ContDiffAt ℝ j f y :=
  hf.contDiffAt.of_le (by exact_mod_cast le_top)

/-- Blueprint: lem:c04_seed_tails.  `|∂^j(f_{0,low} - W)(y)| ≤ C_j|y|^{-p-j}` for `|y| ≥ 1` and
`|∂^j(f₀(y) + y)| ≤ C_j|y|^{-p-j}` for `y ≤ -1`. -/
theorem c04_seed_tails (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ j : ℕ, ∃ C > (0 : ℝ),
      (∀ y : ℝ, 1 ≤ |y| →
        |iteratedDeriv j (fun t => c04_linear_seed_low p t - corner t) y| ≤ C * |y| ^ (-p - j)) ∧
      (∀ y ≤ (-1 : ℝ),
        |iteratedDeriv j (fun t => c04_linear_seed p t + t) y| ≤ C * |y| ^ (-p - j)) := by
  obtain ⟨-, -, hplus, -, -, -, -, -, -, -, -, -, -, h3, h4, -⟩ :=
    c04_seed_decomposition p hp hp1
  obtain ⟨hI1s, hI1b⟩ := c04_I1_bound p hp hp1
  obtain ⟨hI2s, hI2b⟩ := c04_I2_bound
  intro j
  obtain ⟨C1, hC1, hC1b⟩ := hI1b j
  obtain ⟨C2, hC2, hC2b⟩ := hI2b j (p + j) (by positivity)
  obtain ⟨C3, hC3, hC3b⟩ := c04_f0plus_negative p hp hp1 j (p + j) (by positivity)
  have hexp : ∀ y : ℝ, |y| ^ (-(p + j)) = |y| ^ (-p - (j : ℝ)) := fun y => by ring_nf
  have hI2at : ∀ y : ℝ, y ≠ 0 → ContDiffAt ℝ j c04_I2 y := fun y hy =>
    (hI2s.contDiffAt (isOpen_compl_singleton.mem_nhds hy)).of_le (by exact_mod_cast le_top)
  have hsplit : ∀ y : ℝ, y ≠ 0 → iteratedDeriv j (fun t => c04_I1 p t + c04_I2 t) y =
      iteratedDeriv j (c04_I1 p) y + iteratedDeriv j c04_I2 y := fun y hy =>
    iteratedDeriv_fun_add (c04_aux_smooth_at hI1s j y) (hI2at y hy)
  refine ⟨C1 + C2 + 2 * C3, by positivity, fun y hy => ?_, fun y hy => ?_⟩
  · have hy0 : y ≠ 0 := by intro h; rw [h] at hy; norm_num at hy
    have hfun : (fun t => c04_linear_seed_low p t - corner t) = fun t => c04_I1 p t + c04_I2 t :=
      funext fun t => (h3 t).2.2
    rw [hfun, hsplit y hy0]
    have := hC1b y hy
    have h2 := hC2b y hy
    rw [hexp] at h2
    have hpos : 0 ≤ |y| ^ (-p - (j : ℝ)) := by positivity
    calc _ ≤ |iteratedDeriv j (c04_I1 p) y| + |iteratedDeriv j c04_I2 y| := abs_add_le _ _
      _ ≤ C1 * |y| ^ (-p - (j : ℝ)) + C2 * |y| ^ (-p - (j : ℝ)) := add_le_add this h2
      _ ≤ _ := by
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) hpos
  · have hy0 : y < 0 := by linarith
    have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; linarith
    have hev : (fun t => c04_linear_seed p t + t) =ᶠ[𝓝 y]
        fun t => (c04_I1 p t + c04_I2 t) + 2 * (c04_linear_seed_plus p t).re := by
      filter_upwards [Iio_mem_nhds hy0] with t ht
      rw [h4 t, ← (h3 t).2.2]
      simp only [corner, max_eq_left (show (0:ℝ) ≤ -t by linarith [mem_Iio.mp ht])]
      ring
    rw [hev.iteratedDeriv_eq]
    have hre : ContDiffAt ℝ j (fun t => 2 * (c04_linear_seed_plus p t).re) y := by
      have : ContDiff ℝ (⊤ : ℕ∞) (fun t => 2 * (c04_linear_seed_plus p t).re) :=
        contDiff_const.mul (Complex.reCLM.contDiff.comp hplus)
      exact c04_aux_smooth_at this j y
    have hsum : ContDiffAt ℝ j (fun t => c04_I1 p t + c04_I2 t) y :=
      (c04_aux_smooth_at hI1s j y).add (hI2at y hy0.ne)
    rw [iteratedDeriv_fun_add hsum hre, hsplit y hy0.ne, iteratedDeriv_const_mul_field,
      c04_aux_iteratedDeriv_re _ _ _ (c04_aux_smooth_at hplus j y)]
    have h1 := hC1b y hy1
    have h2 := hC2b y hy1
    have h3' := hC3b y hy
    rw [hexp] at h2 h3'
    have hre_le : |(iteratedDeriv j (c04_linear_seed_plus p) y).re| ≤
        ‖iteratedDeriv j (c04_linear_seed_plus p) y‖ := Complex.abs_re_le_norm _
    have hpos : 0 ≤ |y| ^ (-p - (j : ℝ)) := by positivity
    calc _ ≤ |iteratedDeriv j (c04_I1 p) y| + |iteratedDeriv j c04_I2 y| +
          2 * |(iteratedDeriv j (c04_linear_seed_plus p) y).re| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_two]
          gcongr
          exact abs_add_le _ _
      _ ≤ C1 * |y| ^ (-p - (j : ℝ)) + C2 * |y| ^ (-p - (j : ℝ)) +
          2 * (C3 * |y| ^ (-p - (j : ℝ))) := by linarith
      _ = _ := by ring

/-- Bound of the `|D|^p` integrand with a Lipschitz bound at scale `R` around `y`. -/
theorem c04_aux_frac_bound_R (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (hg : Continuous g)
    (M : ℝ) (hM : ∀ z, |g z| ≤ M) (y R Λ : ℝ) (hR : 0 < R) (_hΛ : 0 ≤ Λ)
    (hLip : ∀ z, |y - z| ≤ R → |g y - g z| ≤ Λ * |y - z|) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) ∧
      ∫ z, |(g y - g z) / |y - z| ^ (p + 1)| ≤
        2 * (Λ * R ^ (1 - p) / (1 - p) + 2 * M * R ^ (-p) / p) := by
  obtain ⟨hψi, hψ⟩ := c04_aux_psiR_integral p Λ M R hp hp1 hR
  set D : ℝ → ℝ := fun z => c04_aux_psiR p Λ M R |y - z|
  have hDi : Integrable D :=
    (c04_aux_c01_integrable_comp_abs hψi).comp_sub_left y
  have hDint : ∫ z, D z = 2 * (Λ * R ^ (1 - p) / (1 - p) + 2 * M * R ^ (-p) / p) := by
    simp only [D]
    rw [integral_sub_left_eq_self (fun z => c04_aux_psiR p Λ M R |z|) volume y,
      integral_comp_abs (f := c04_aux_psiR p Λ M R), hψ]
  have hmeas : AEStronglyMeasurable (fun z => (g y - g z) / |y - z| ^ (p + 1)) volume := by
    have h2 : Measurable (fun z : ℝ => (|y - z| ^ (p + 1))⁻¹) := by
      have : Continuous (fun z : ℝ => |y - z| ^ (p + 1)) :=
        (continuous_const.sub continuous_id).abs.rpow_const (fun _ => Or.inr (by linarith))
      exact this.measurable.inv
    have := (aestronglyMeasurable_const (b := g y) (μ := volume)).sub hg.aestronglyMeasurable
      |>.mul h2.aestronglyMeasurable
    simp only [div_eq_mul_inv]
    exact this
  have hbound : ∀ z, ‖(g y - g z) / |y - z| ^ (p + 1)‖ ≤ D z := by
    intro z
    rw [Real.norm_eq_abs]
    by_cases hzy : z = y
    · subst hzy
      simp only [sub_self, zero_div, abs_zero, D, c04_aux_psiR]
      simp only [hR.le, ite_true]
      rw [Real.zero_rpow (by linarith)]; simp
    have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hzy))
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    simp only [D, c04_aux_psiR]
    split_ifs with h1
    · rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
      calc |g y - g z| ≤ Λ * |y - z| := hLip z h1
        _ = Λ * |y - z| ^ (-p) * |y - z| ^ (p + 1) := by
          rw [mul_assoc, ← Real.rpow_add hpos]; simp
    · rw [div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
      calc |g y - g z| ≤ |g y| + |g z| := abs_sub _ _
        _ ≤ 2 * M := by linarith [hM y, hM z]
        _ = 2 * M * |y - z| ^ (-(p + 1)) * |y - z| ^ (p + 1) := by
          rw [mul_assoc, ← Real.rpow_add hpos]; simp
  have hInt : Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) :=
    Integrable.mono' hDi hmeas (Eventually.of_forall hbound)
  refine ⟨hInt, ?_⟩
  rw [← hDint]
  apply integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hDi
  exact Eventually.of_forall fun z => by have := hbound z; rwa [Real.norm_eq_abs] at this

/-- Blueprint: lem:c04_L0_f0.  `ℒ₀ f₀ ≡ 0`. -/
theorem c04_L0_f0 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ y, L0 p (c04_linear_seed p) y = 0 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hA, hC1, hD0⟩ := c04_L0_f0_constant p hp hp1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hf0⟩ := c04_seed_decomposition p hp hp1
  have hconst := is_const_of_deriv_eq_zero (hC1.differentiable (by simp)) hD0
  obtain ⟨C0, hC0, -, ht0⟩ := c04_seed_tails p hp hp1 0
  obtain ⟨C1, hC1', -, ht1⟩ := c04_seed_tails p hp hp1 1
  obtain ⟨C2, hC2, -, ht2⟩ := c04_seed_tails p hp hp1 2
  obtain ⟨Mf, hMf⟩ := hA.2.1
  set f0 := c04_linear_seed p with hf0def
  set u : ℝ → ℝ := fun t => deriv f0 t + 1 with hu
  have hf0d : Differentiable ℝ f0 := hf0.differentiable (by simp)
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun t => f0 t + t) := hf0.add contDiff_id
  have hu_eq : deriv (fun t => f0 t + t) = u := by
    funext t; exact ((hf0d t).hasDerivAt.add (hasDerivAt_id' t)).deriv
  have hu_c : ContDiff ℝ (⊤ : ℕ∞) u := by
    rw [← hu_eq]; exact (contDiff_infty_iff_deriv.mp hF).2
  have hud : Differentiable ℝ u := hu_c.differentiable (by simp)
  have hdu : ∀ w ≤ (-1 : ℝ), |deriv u w| ≤ C2 * |w| ^ (-p - 2) := by
    intro w hw
    have := ht2 w hw
    rw [iteratedDeriv_succ, iteratedDeriv_one, hu_eq] at this
    convert this using 3
  -- the bound for `y ≤ -2`
  set X : ℝ → ℝ := fun y => |y| / 2 with hX
  set B : ℝ → ℝ := fun y => |calpha p| * (2 * (C2 * X y ^ (-(2 * p + 1)) / (1 - p) +
      2 * (Mf + 1) * X y ^ (-p) / p)) + (C0 * 2 ^ (-p)) * X y ^ (-p) +
      (C1 * 2 ^ (-p)) * X y ^ (-p) with hB
  have key : ∀ y ≤ (-2 : ℝ), |L0 p f0 y| ≤ B y := by
    intro y hy
    have hy0 : y < 0 := by linarith
    have hXp : 0 < X y := by simp only [hX]; exact div_pos (abs_pos.mpr hy0.ne) two_pos
    have habs : |y| = 2 * X y := by simp only [hX]; ring
    have hL : L0 p f0 y = fracD p u y + (f0 y + y) - y * u y := by
      unfold L0 fracDdy fracD; simp only [hu, add_sub_add_right_eq_sub]; ring
    -- fractional part
    have hLip : ∀ z, |y - z| ≤ X y → |u y - u z| ≤ C2 * X y ^ (-p - 2) * |y - z| := by
      intro z hz
      have hzle : z ≤ y / 2 := by
        have := (abs_le.mp hz).1
        simp only [hX, abs_of_neg hy0] at this; linarith
      have hmem : ∀ w ∈ Iic (y / 2), ‖deriv u w‖ ≤ C2 * X y ^ (-p - 2) := by
        intro w hw
        have hw' : w ≤ -1 := by linarith [mem_Iic.mp hw]
        rw [Real.norm_eq_abs]
        refine (hdu w hw').trans ?_
        have hle : X y ≤ |w| := by
          simp only [hX, abs_of_neg hy0, abs_of_neg (by linarith : w < 0)]
          linarith [mem_Iic.mp hw]
        exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hXp hle (by linarith)) hC2.le
      have := (convex_Iic (y / 2)).norm_image_sub_le_of_norm_deriv_le
        (fun w _ => hud w) hmem (mem_Iic.mpr hzle) (mem_Iic.mpr (show y ≤ y / 2 by linarith))
      simpa [Real.norm_eq_abs] using this
    obtain ⟨-, hfb⟩ := c04_aux_frac_bound_R p hp0 hp1 u hu_c.continuous (Mf + 1)
      (fun z => by
        simp only [hu]
        exact (abs_add_le _ _).trans (by rw [abs_one]; linarith [hMf z])) y (X y)
      (C2 * X y ^ (-p - 2)) hXp (mul_nonneg hC2.le (rpow_nonneg hXp.le _)) hLip
    have hfrac : |fracD p u y| ≤ |calpha p| * (2 * (C2 * X y ^ (-(2 * p + 1)) / (1 - p) +
        2 * (Mf + 1) * X y ^ (-p) / p)) := by
      unfold fracD
      rw [abs_mul]
      gcongr
      refine (abs_integral_le_integral_abs).trans (hfb.trans (le_of_eq ?_))
      have e : C2 * X y ^ (-p - 2) * X y ^ (1 - p) = C2 * X y ^ (-(2 * p + 1)) := by
        rw [mul_assoc, ← rpow_add hXp]; ring_nf
      rw [e]
    -- the other two terms
    have h0 := ht0 y (by linarith)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h0
    have h1 := ht1 y (by linarith)
    rw [iteratedDeriv_one, hu_eq] at h1
    have hpw : |y| ^ (-p) = 2 ^ (-p) * X y ^ (-p) := by
      rw [habs, mul_rpow (by norm_num) hXp.le]
    have h1' : |y * u y| ≤ C1 * |y| ^ (-p) := by
      rw [abs_mul]
      have hyp : 0 < |y| := abs_pos.mpr hy0.ne
      calc |y| * |u y| ≤ |y| * (C1 * |y| ^ (-p - ((1 : ℕ) : ℝ))) := by gcongr
        _ = C1 * |y| ^ (-p) := by
          rw [show -p - ((1 : ℕ) : ℝ) = -p + (-1) by push_cast; ring, rpow_add hyp, rpow_neg_one]
          field_simp
    rw [hL]
    calc |fracD p u y + (f0 y + y) - y * u y| ≤ |fracD p u y| + |f0 y + y| + |y * u y| := by
          refine (abs_sub _ _).trans ?_
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by
          simp only [hB]
          rw [hpw] at h0 h1'
          linarith
  -- `B → 0` at `-∞`
  have hXt : Tendsto X atBot atTop := tendsto_abs_atBot_atTop.atTop_div_const two_pos
  have hBt : Tendsto B atBot (𝓝 0) := by
    have t1 := (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * p + 1)).comp hXt
    have t2 := (tendsto_rpow_neg_atTop hp0).comp hXt
    have := ((((t1.const_mul C2).div_const (1 - p)).add
      (((t2.const_mul (2 * (Mf + 1))).div_const p))).const_mul 2 |>.const_mul (|calpha p|)).add
      (t2.const_mul (C0 * 2 ^ (-p))) |>.add (t2.const_mul (C1 * 2 ^ (-p)))
    simp only [mul_zero, zero_div, add_zero] at this
    convert this using 1
    funext y; simp only [hB, Function.comp]
  intro y
  have hle : |L0 p f0 y| ≤ 0 := by
    refine ge_of_tendsto hBt ?_
    filter_upwards [eventually_le_atBot (-2 : ℝ)] with y' hy'
    rw [hconst y y']; exact key y' hy'
  exact abs_nonpos_iff.mp hle

/-- `G_μ = 2 Re[(1 - μ/μ_*) Γ₊]` (Fourier inversion of the Hermitian symbol). -/
theorem c04_aux_G_pm_of_eq (p : ℝ) (s : ℂ) (y : ℝ) :
    G_pm_of p s y = 2 * (s * c04_linear_seed_Gamma_plus p y).re := by
  obtain ⟨K, hK0, hK⟩ := c04_aux_dchi_div_bound
  set h : ℝ → ℂ := fun ξ => s * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) with hh
  set F : ℝ → ℂ := fun ξ => G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) with hF
  have hnorm_exp : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hh_norm : ∀ ξ, ‖h ξ‖ = ‖s‖ * |deriv chiPlus ξ / ξ| := fun ξ => by
    simp only [hh, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show -(Complex.I * (Phi0 p ξ : ℂ)) = Complex.I * ((-Phi0 p ξ : ℝ) : ℂ) by push_cast; ring,
      hnorm_exp, mul_one]
  have hmeas_h : Measurable h := by
    have : Measurable (deriv chiPlus) := measurable_deriv chiPlus
    have hP : Measurable (Phi0 p) := by unfold Phi0; fun_prop
    simp only [hh]; fun_prop
  have hGeq : ∀ ξ, G_pm_hat p s ξ = if 0 ≤ ξ then h ξ else conj (h (-ξ)) := fun ξ => rfl
  have hFint : Integrable F := by
    refine Integrable.mono' (g := (Icc (-2:ℝ) 2).indicator (fun _ => ‖s‖ * K)) ?_ ?_ ?_
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · have : Measurable (fun ξ => G_pm_hat p s ξ) := by
        rw [show (fun ξ => G_pm_hat p s ξ) = fun ξ => if 0 ≤ ξ then h ξ else conj (h (-ξ)) from
          funext hGeq]
        exact Measurable.ite (p := fun ξ : ℝ => 0 ≤ ξ) measurableSet_Ici hmeas_h
          ((Complex.continuous_conj.measurable).comp (hmeas_h.comp measurable_neg))
      simp only [hF]
      exact (this.mul (by fun_prop)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ξ => ?_)
      simp only [hF, norm_mul]
      rw [show Complex.I * (y : ℂ) * (ξ : ℂ) = Complex.I * ((y * ξ : ℝ) : ℂ) by push_cast; ring,
        hnorm_exp, mul_one, hGeq]
      have key : ∀ t, 0 ≤ t → ‖h t‖ ≤ (Icc (-2:ℝ) 2).indicator (fun _ => ‖s‖ * K) t := by
        intro t ht
        rw [hh_norm]
        by_cases ht2 : t ∈ Icc (1:ℝ) 2
        · rw [indicator_of_mem (show t ∈ Icc (-2:ℝ) 2 from ⟨by linarith [ht2.1], ht2.2⟩)]
          exact mul_le_mul_of_nonneg_left (hK t).1 (norm_nonneg _)
        · rw [(hK t).2 ht2, abs_zero, mul_zero]
          exact indicator_nonneg (fun _ _ => by positivity) _
      split_ifs with h0
      · exact key ξ h0
      · rw [Complex.norm_conj]
        refine (key (-ξ) (by linarith)).trans (le_of_eq ?_)
        by_cases hm : ξ ∈ Icc (-2:ℝ) 2
        · rw [indicator_of_mem hm, indicator_of_mem (show -ξ ∈ Icc (-2:ℝ) 2 from ⟨by linarith [hm.2], by linarith [hm.1]⟩)]
        · rw [indicator_of_notMem hm, indicator_of_notMem]
          intro h'; exact hm ⟨by linarith [h'.2], by linarith [h'.1]⟩
  set e : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) with he
  set A := ∫ ξ in Ioi (0:ℝ), h ξ * e ξ with hA
  set I0 := ∫ ξ in Ioi (0 : ℝ), ((deriv chiPlus ξ / ξ : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) with hI0
  have hAI : A = s * I0 := by
    rw [hA, hI0, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hh, he]
    rw [mul_assoc s, mul_assoc s, mul_assoc, ← Complex.exp_add]
    have : -(Complex.I * (Phi0 p ξ : ℂ)) + Complex.I * (y : ℂ) * (ξ : ℂ) =
        Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ) := by push_cast; ring
    rw [this]
  have hpos : ∫ ξ in Ici (0:ℝ), F ξ = A := by
    rw [integral_Ici_eq_integral_Ioi, hA]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
    simp only [hF, he, hGeq, le_of_lt (mem_Ioi.mp hξ), ↓reduceIte]
  have hneg : ∫ ξ in Iio (0:ℝ), F ξ = conj A := by
    rw [← integral_Iic_eq_integral_Iio, hA, ← integral_conj]
    have := integral_comp_neg_Ioi (0:ℝ) F
    rw [neg_zero] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
    have hξ' : ¬ (0 ≤ -ξ) := by linarith [mem_Ioi.mp hξ]
    simp only [hF, he, hGeq, hξ', ↓reduceIte, neg_neg, map_mul, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  have htot : ∫ ξ, F ξ = A + conj A := by
    rw [← integral_add_compl measurableSet_Ici hFint, compl_Ici, hpos, hneg]
  unfold G_pm_of invFourierT c04_linear_seed_Gamma_plus
  rw [show (∫ ξ, G_pm_hat p s ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) = ∫ ξ, F ξ from rfl,
    htot, ← hI0, hAI, ← Complex.ofReal_inv]
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Blueprint: lem:approx_linear_seed.  The linear solution: `f₀ ∈ C^∞ ∩ 𝒜`, `ℒ₀ f₀ = 0`,
`f₀' → -1` at `-∞`, `f₀' → 0` at `+∞`, the bounds (1), (2), and (3) `ℒ₀ f_{0,μ} = G_μ`. -/
theorem approx_linear_seed (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed p) ∧ c04_linear_seed p ∈ c01_admissible_class ∧
    (∀ y, L0 p (c04_linear_seed p) y = 0) ∧
    Tendsto (deriv (c04_linear_seed p)) atBot (𝓝 (-1)) ∧
    Tendsto (deriv (c04_linear_seed p)) atTop (𝓝 0) ∧
    (∃ y₀ ≥ (2 : ℝ), ∀ j : ℕ, ∃ C > (0 : ℝ),
      -- (1)
      (∀ y ≥ y₀, ‖iteratedDeriv j (fun t => astar p t - 1) y‖ ≤ C * y ^ (-2 * beta p - j)) ∧
      -- (2)
      (∀ y : ℝ, 1 ≤ |y| →
        |iteratedDeriv j (fun t => c04_linear_seed_low p t - corner t) y| ≤ C * |y| ^ (-p - j)) ∧
      (∀ y ≤ (-1 : ℝ),
        |iteratedDeriv j (fun t => c04_linear_seed p t + t) y| ≤ C * |y| ^ (-p - j))) ∧
    -- (3)
    (∀ μ : ℂ, ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_mu p μ) ∧
      c04_linear_seed_mu p μ ∈ c01_admissible_class ∧
      ∀ y, L0 p (c04_linear_seed_mu p μ) y = G_mu p μ y) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, hplus, -, -, -, hlow, -, -, -, -, -, -, h3, h4, hf0⟩ :=
    c04_seed_decomposition p hp hp1
  obtain ⟨hA, -, -⟩ := c04_L0_f0_constant p hp hp1
  obtain ⟨y₀, hy₀, -, hamp⟩ := c04_seed_amplitude p hp hp1
  have htails := c04_seed_tails p hp hp1
  obtain ⟨Cg, hCg, hglob⟩ := c04_f0plus_global p hp hp1
  have hf0d : Differentiable ℝ (c04_linear_seed p) :=
    hf0.differentiable (by simp)
  have hplusd : Differentiable ℝ (c04_linear_seed_plus p) :=
    hplus.differentiable (by simp)
  have hlowd : Differentiable ℝ (c04_linear_seed_low p) :=
    hlow.differentiable (by simp)
  -- limits of `f₀'`
  have hbot : Tendsto (deriv (c04_linear_seed p)) atBot (𝓝 (-1)) := by
    obtain ⟨C, hC, -, hneg⟩ := htails 1
    have h0 : Tendsto (fun y : ℝ => C * |y| ^ (-(p + 1))) atBot (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by linarith : 0 < p + 1)).comp
        tendsto_abs_atBot_atTop).const_mul C
      simpa using this
    have h1 : Tendsto (fun y => deriv (c04_linear_seed p) y + 1) atBot (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [eventually_le_atBot (-1 : ℝ)] with y hy
      have := hneg y hy
      rw [iteratedDeriv_one] at this
      have hd : deriv (fun t => c04_linear_seed p t + t) y = deriv (c04_linear_seed p) y + 1 :=
        ((hf0d y).hasDerivAt.add (hasDerivAt_id' y)).deriv
      rw [hd] at this
      rw [Real.norm_eq_abs]
      convert this using 3; push_cast; ring
    have := h1.add_const (-1)
    simpa using this
  have htop : Tendsto (deriv (c04_linear_seed p)) atTop (𝓝 0) := by
    obtain ⟨C, hC, hpos, -⟩ := htails 1
    obtain ⟨C', hC', hb'⟩ := hamp 0
    have hbeta : 0 < beta p := by unfold beta; positivity
    have h0 : Tendsto (fun y : ℝ => C * y ^ (-(p + 1)) + 2 * (C' * y ^ (-beta p))) atTop (𝓝 0) := by
      have a1 := (tendsto_rpow_neg_atTop (by linarith : 0 < p + 1)).const_mul C
      have a2 := ((tendsto_rpow_neg_atTop hbeta).const_mul C').const_mul 2
      simpa using a1.add a2
    have hdf : ∀ y, deriv (c04_linear_seed p) y =
        deriv (c04_linear_seed_low p) y + 2 * (deriv (c04_linear_seed_plus p) y).re := by
      intro y
      have hfun : c04_linear_seed p = fun t => c04_linear_seed_low p t +
          2 * (c04_linear_seed_plus p t).re := funext h4
      rw [hfun]
      have h2 : HasDerivAt (fun t => (c04_linear_seed_plus p t).re)
          (deriv (c04_linear_seed_plus p) y).re y :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hplusd y).hasDerivAt
      exact ((hlowd y).hasDerivAt.add (h2.const_mul 2)).deriv
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop (max 1 y₀)] with y hy
    have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
    have hyy : y₀ ≤ y := le_trans (le_max_right _ _) hy
    have hy0 : 0 < y := by linarith
    have e1 := hpos y (by rw [abs_of_pos hy0]; exact hy1)
    rw [iteratedDeriv_one, abs_of_pos hy0] at e1
    have hev : (fun t => c04_linear_seed_low p t - corner t) =ᶠ[𝓝 y] c04_linear_seed_low p := by
      filter_upwards [Ioi_mem_nhds hy0] with t ht
      simp [corner, max_eq_right (show -t ≤ 0 by linarith [mem_Ioi.mp ht])]
    rw [hev.deriv_eq] at e1
    have e2 := (hb' y hyy).2.2
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at e2
    rw [hdf, Real.norm_eq_abs]
    have hre := Complex.abs_re_le_norm (deriv (c04_linear_seed_plus p) y)
    calc _ ≤ |deriv (c04_linear_seed_low p) y| + 2 * |(deriv (c04_linear_seed_plus p) y).re| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_two]
      _ ≤ _ := by
          have : y ^ (-p - ((1:ℕ):ℝ)) = y ^ (-(p + 1)) := by push_cast; ring_nf
          rw [this] at e1
          linarith
  refine ⟨hf0, hA, c04_L0_f0 p hp hp1, hbot, htop, ⟨y₀, hy₀, fun j => ?_⟩, fun μ => ?_⟩
  · obtain ⟨C1, hC1, hb⟩ := hamp j
    obtain ⟨C2, hC2, ht1, ht2⟩ := htails j
    refine ⟨C1 + C2, by positivity, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
    · have hnn : 0 ≤ y ^ (-2 * beta p - j) := rpow_nonneg (by linarith) _
      exact le_trans (hb y hy).1 (mul_le_mul_of_nonneg_right (by linarith) hnn)
    · have hnn : 0 ≤ |y| ^ (-p - j) := rpow_nonneg (abs_nonneg _) _
      exact le_trans (ht1 y hy) (mul_le_mul_of_nonneg_right (by linarith) hnn)
    · have hnn : 0 ≤ |y| ^ (-p - j) := rpow_nonneg (abs_nonneg _) _
      exact le_trans (ht2 y hy) (mul_le_mul_of_nonneg_right (by linarith) hnn)
  · set c : ℂ := μ / mu_star p - 1 with hc
    set G : ℝ → ℂ := fun t => ((2 : ℝ) : ℂ) * c * c04_linear_seed_plus p t with hGdef
    have hfun : c04_linear_seed_mu p μ = fun t => c04_linear_seed p t + (G t).re := by
      funext t
      simp only [c04_linear_seed_mu, hGdef, hc, mul_assoc, Complex.re_ofReal_mul]
    have hGs : ContDiff ℝ (⊤ : ℕ∞) G := contDiff_const.mul hplus
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_mu p μ) := by
      rw [hfun]; exact hf0.add (Complex.reCLM.contDiff.comp hGs)
    have hdG : deriv G = fun t => ((2 : ℝ) : ℂ) * c * deriv (c04_linear_seed_plus p) t := by
      funext t; exact ((hplusd t).hasDerivAt.const_mul _).deriv
    have hGb : ∀ y, ‖deriv G y‖ ≤ 2 * ‖c‖ * Cg := by
      intro y; rw [hdG]
      simp only [norm_mul, Complex.norm_real, Real.norm_two]
      have := (hglob y).1
      have : ‖deriv (c04_linear_seed_plus p) y‖ ≤ Cg := by
        linarith [norm_nonneg (c04_linear_seed_plus p y)]
      gcongr
    have hderμ : ∀ t, deriv (c04_linear_seed_mu p μ) t =
        deriv (c04_linear_seed p) t + (deriv G t).re := by
      intro t; rw [hfun]
      have h2 : HasDerivAt (fun t => (G t).re) (deriv G t).re t :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
          ((hGs.differentiable (by simp)) t).hasDerivAt
      exact ((hf0d t).hasDerivAt.add h2).deriv
    refine ⟨hsm, ⟨hsm.of_le (by exact_mod_cast le_top), ?_, ?_⟩, fun y => ?_⟩
    · obtain ⟨Mf, hMf⟩ := hA.2.1
      refine ⟨Mf + 2 * ‖c‖ * Cg, fun y => ?_⟩
      rw [hderμ]
      have := Complex.abs_re_le_norm (deriv G y)
      have := hGb y
      have := hMf y
      calc _ ≤ |deriv (c04_linear_seed p) y| + |(deriv G y).re| := abs_add_le _ _
        _ ≤ _ := by linarith
    · have : ContDiff ℝ (⊤ : ℕ∞) (deriv (c04_linear_seed_mu p μ)) :=
        (contDiff_infty_iff_deriv.mp hsm).2
      exact (this.of_le (by exact_mod_cast le_top)).locallyLipschitz
    · rw [hfun, c04_aux_L0_add_re p hp0 hp1 _ hA (hf0.of_le (by simp)) G
        (hGs.of_le (by simp)) _ hGb y, c04_L0_f0 p hp hp1 y]
      have hL : c04_L0C p G y = ((2 : ℝ) : ℂ) * c * c04_L0C p (c04_linear_seed_plus p) y := by
        unfold c04_L0C fracDC
        rw [hdG]
        have : (fun z => (((2 : ℝ) : ℂ) * c * deriv (c04_linear_seed_plus p) y -
            ((2 : ℝ) : ℂ) * c * deriv (c04_linear_seed_plus p) z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) =
            fun z => ((2 : ℝ) : ℂ) * c * ((deriv (c04_linear_seed_plus p) y -
              deriv (c04_linear_seed_plus p) z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) := by
          funext z; ring
        rw [this, integral_const_mul]
        simp only [hGdef]; ring
      rw [hL, c04_L0_f0plus p hp hp1 y, G_mu, c04_aux_G_pm_of_eq]
      have : ((2 : ℝ) : ℂ) * c * -c04_linear_seed_Gamma_plus p y =
          ((2 : ℝ) : ℂ) * ((1 - μ / mu_star p) * c04_linear_seed_Gamma_plus p y) := by
        rw [hc]; ring
      rw [this, Complex.re_ofReal_mul]; ring

/-! ### Cubic part and correction constants -/


/-- `κ_ε = ε κ₁`. -/
private theorem c04_aux_kappa_eq (p ε : ℝ) : c04_cubic_part_kappa p ε = ε * c04_cubic_part_kappa p 1 := by
  unfold c04_cubic_part_kappa; ring

/-- `c₁(ε) = ε c₁(1)` (pure algebra). -/
theorem c04_aux_c1_lin (p ε : ℝ) : cubic_c1 p ε = ε * cubic_c1 p 1 := by
  unfold cubic_c1 c04_cubic_part
  rw [c04_aux_kappa_eq p ε]
  simp_rw [mul_assoc ε]
  rw [intervalIntegral.integral_const_mul]; ring

/-- `c₂(ε) = ε c₂(1)` (pure algebra). -/
theorem c04_aux_c2_lin (p ε : ℝ) : cubic_c2 p ε = ε * cubic_c2 p 1 := by
  unfold cubic_c2 c04_cubic_part
  rw [c04_aux_kappa_eq p ε]
  simp_rw [mul_assoc ε]
  rw [intervalIntegral.integral_const_mul]; ring

/-- The weight `w(h) = 1/(|h|^{p+1} h²)`. -/
def c04_aux_wt (p h : ℝ) : ℝ := 1 / (|h| ^ (p + 1) * h ^ 2)

/-- Integrability of `A^m B^n w` (`m+n = 3`, `A = 1 - cos h`, `B = sin h`). -/
theorem c04_aux_trig_int (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m n : ℕ) (hmn : m + n = 3) :
    Integrable (fun h : ℝ => (1 - Real.cos h) ^ m * Real.sin h ^ n * c04_aux_wt p h) := by
  have hψ := c04_aux_c01_integrable_comp_abs (c04_aux_c01_psi_integral p 1 4 hp hp1).1
  refine Integrable.mono' hψ ?_ (Eventually.of_forall fun h => ?_)
  · unfold c04_aux_wt
    apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [Real.norm_eq_abs]
    simp only [c04_aux_c01_psi]
    by_cases h0 : h = 0
    · subst h0; simp [c04_aux_wt]; exact rpow_nonneg le_rfl _
    have hpos : 0 < |h| := abs_pos.mpr h0
    have hA0 : 0 ≤ 1 - Real.cos h := by linarith [Real.cos_le_one h]
    have hA2 : 1 - Real.cos h ≤ 2 := by linarith [Real.neg_one_le_cos h]
    have hAh : 1 - Real.cos h ≤ h ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := h)]
    have hB1 : |Real.sin h| ≤ 1 := Real.abs_sin_le_one h
    have hBh : |Real.sin h| ≤ |h| := Real.abs_sin_le_abs
    have hw : c04_aux_wt p h = |h| ^ (-(p + 3)) := by
      unfold c04_aux_wt
      rw [← sq_abs h, show (|h| ^ 2 : ℝ) = |h| ^ (2 : ℝ) by norm_cast, ← rpow_add hpos, rpow_neg hpos.le,
        one_div]; ring_nf
    rw [hw, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hA0,
      abs_of_pos (rpow_pos_of_pos hpos _)]
    split_ifs with h1
    · -- near `0`: `|A^m B^n| ≤ |h|^3`
      have hA : 1 - Real.cos h ≤ |h| := by
        have : h ^ 2 / 2 ≤ |h| := by
          rw [← sq_abs]; nlinarith [abs_nonneg h]
        linarith
      have hmB : (1 - Real.cos h) ^ m * |Real.sin h| ^ n ≤ |h| ^ m * |h| ^ n :=
        mul_le_mul (pow_le_pow_left₀ hA0 hA m) (pow_le_pow_left₀ (abs_nonneg _) hBh n)
          (by positivity) (by positivity)
      rw [← pow_add, hmn] at hmB
      have e : |h| ^ 3 * |h| ^ (-(p + 3)) = 1 * |h| ^ (-p) := by
        rw [show (|h| ^ 3 : ℝ) = |h| ^ (3 : ℝ) by norm_cast, ← rpow_add hpos]; ring_nf
      calc (1 - Real.cos h) ^ m * |Real.sin h| ^ n * |h| ^ (-(p + 3))
          ≤ |h| ^ 3 * |h| ^ (-(p + 3)) := mul_le_mul_of_nonneg_right hmB (by positivity)
        _ = _ := e
    · push Not at h1
      have hmB : (1 - Real.cos h) ^ m * |Real.sin h| ^ n ≤ 2 ^ m * 2 ^ n :=
        mul_le_mul (pow_le_pow_left₀ hA0 hA2 m) (pow_le_pow_left₀ (abs_nonneg _) (hB1.trans one_le_two) n)
          (by positivity) (by positivity)
      rw [← pow_add, hmn] at hmB
      have hr : |h| ^ (-(p + 3)) ≤ |h| ^ (-(p + 1)) :=
        rpow_le_rpow_of_exponent_le h1.le (by linarith)
      calc (1 - Real.cos h) ^ m * |Real.sin h| ^ n * |h| ^ (-(p + 3))
          ≤ 2 ^ 3 * |h| ^ (-(p + 1)) :=
            mul_le_mul hmB hr (by positivity) (by positivity)
        _ = 2 * 4 * |h| ^ (-(p + 1)) := by norm_num


/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_orth1 (a b : ℝ) :
    π⁻¹ * ∫ y in (0 : ℝ)..(2 * π), (a * Real.cos y + b * Real.cos (3 * y)) * Real.cos y = a := by
  have hF : ∀ y, HasDerivAt (fun y => a * (y / 2 + Real.sin (2 * y) / 4) +
      b * (Real.sin (4 * y) / 8 + Real.sin (2 * y) / 4))
      ((a * Real.cos y + b * Real.cos (3 * y)) * Real.cos y) y := by
    intro y
    have h2 := ((hasDerivAt_id y).const_mul 2).sin
    have h4 := ((hasDerivAt_id y).const_mul 4).sin
    have := (((hasDerivAt_id y).div_const 2).add (h2.div_const 4)).const_mul a |>.add
      (((h4.div_const 8).add (h2.div_const 4)).const_mul b)
    refine this.congr_deriv ?_
    simp only [id]
    have e4 : Real.cos (4 * y) = 2 * Real.cos (2 * y) ^ 2 - 1 := by
      rw [show 4 * y = 2 * (2 * y) by ring, Real.cos_two_mul]
    rw [e4, Real.cos_two_mul, Real.cos_three_mul]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have s4 : Real.sin (4 * (2 * π)) = 0 := by
    rw [show 4 * (2 * π) = ((8 : ℕ) : ℝ) * π by push_cast; ring]; exact Real.sin_nat_mul_pi 8
  have s2 : Real.sin (2 * (2 * π)) = 0 := by
    rw [show 2 * (2 * π) = ((4 : ℕ) : ℝ) * π by push_cast; ring]; exact Real.sin_nat_mul_pi 4
  simp only [s4, s2, mul_zero, Real.sin_zero, zero_div, add_zero]
  field_simp
  simp

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_orth3 (a b : ℝ) :
    π⁻¹ * ∫ y in (0 : ℝ)..(2 * π), (a * Real.cos y + b * Real.cos (3 * y)) * Real.cos (3 * y) = b := by
  have hF : ∀ y, HasDerivAt (fun y => a * (Real.sin (4 * y) / 8 + Real.sin (2 * y) / 4) +
      b * (y / 2 + Real.sin (6 * y) / 12))
      ((a * Real.cos y + b * Real.cos (3 * y)) * Real.cos (3 * y)) y := by
    intro y
    have h2 := ((hasDerivAt_id y).const_mul 2).sin
    have h4 := ((hasDerivAt_id y).const_mul 4).sin
    have h6 := ((hasDerivAt_id y).const_mul 6).sin
    have := (((h4.div_const 8).add (h2.div_const 4)).const_mul a).add
      ((((hasDerivAt_id y).div_const 2).add (h6.div_const 12)).const_mul b)
    refine this.congr_deriv ?_
    simp only [id]
    have e4 : Real.cos (4 * y) = 2 * Real.cos (2 * y) ^ 2 - 1 := by
      rw [show 4 * y = 2 * (2 * y) by ring, Real.cos_two_mul]
    have e6 : Real.cos (6 * y) = 2 * Real.cos (3 * y) ^ 2 - 1 := by
      rw [show 6 * y = 2 * (3 * y) by ring, Real.cos_two_mul]
    rw [e4, e6, Real.cos_two_mul, Real.cos_three_mul]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hF y)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have s4 : Real.sin (4 * (2 * π)) = 0 := by
    rw [show 4 * (2 * π) = ((8 : ℕ) : ℝ) * π by push_cast; ring]; exact Real.sin_nat_mul_pi 8
  have s2 : Real.sin (2 * (2 * π)) = 0 := by
    rw [show 2 * (2 * π) = ((4 : ℕ) : ℝ) * π by push_cast; ring]; exact Real.sin_nat_mul_pi 4
  have s6 : Real.sin (6 * (2 * π)) = 0 := by
    rw [show 6 * (2 * π) = ((12 : ℕ) : ℝ) * π by push_cast; ring]; exact Real.sin_nat_mul_pi 12
  simp only [s4, s2, s6, mul_zero, Real.sin_zero, zero_div, add_zero]
  field_simp
  simp

/-- Odd terms integrate to `0`. -/
theorem c04_aux_trig_odd (p : ℝ) (m n : ℕ) (hn : Odd n) :
    ∫ h : ℝ, (1 - Real.cos h) ^ m * Real.sin h ^ n * c04_aux_wt p h = 0 := by
  have h := integral_neg_eq_self (fun h : ℝ => (1 - Real.cos h) ^ m * Real.sin h ^ n * c04_aux_wt p h) volume
  have e : (fun h : ℝ => (1 - Real.cos (-h)) ^ m * Real.sin (-h) ^ n * c04_aux_wt p (-h)) =
      fun h => -((1 - Real.cos h) ^ m * Real.sin h ^ n * c04_aux_wt p h) := by
    funext h
    simp only [Real.cos_neg, Real.sin_neg, c04_aux_wt, abs_neg, neg_sq, hn.neg_pow]; ring
  rw [e, integral_neg] at h
  linarith

/-- The explicit form of `𝒬_{ε,3}(sin)`. -/
theorem c04_aux_Qsin (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε y : ℝ) :
    c04_cubic_part p ε Real.sin y =
      c04_cubic_part_kappa p ε * ((∫ h, (1 - Real.cos h) ^ 3 * Real.sin h ^ 0 * c04_aux_wt p h) +
          ∫ h, (1 - Real.cos h) ^ 1 * Real.sin h ^ 2 * c04_aux_wt p h) / 4 * Real.cos y +
      c04_cubic_part_kappa p ε * (3 * (∫ h, (1 - Real.cos h) ^ 1 * Real.sin h ^ 2 * c04_aux_wt p h) -
          ∫ h, (1 - Real.cos h) ^ 3 * Real.sin h ^ 0 * c04_aux_wt p h) / 4 * Real.cos (3 * y) := by
  set g : ℕ → ℕ → ℝ → ℝ := fun m n h => (1 - Real.cos h) ^ m * Real.sin h ^ n * c04_aux_wt p h with hg
  set c := Real.cos y
  set s := Real.sin y
  unfold c04_cubic_part
  rw [← integral_sub_left_eq_self _ volume y]
  have hpt : ∀ h : ℝ, (deriv Real.sin y - deriv Real.sin (y - h)) / |y - (y - h)| ^ (p + 1) *
      c01_secant Real.sin y (y - h) ^ 2 =
      c * s ^ 2 * g 3 0 h + (c ^ 3 - 2 * s ^ 2 * c) * g 1 2 h + (2 * s * c ^ 2 - s ^ 3) * g 2 1 h -
        s * c ^ 2 * g 0 3 h := by
    intro h
    simp only [hg, Real.deriv_sin, c04_aux_wt, sub_sub_cancel, Real.cos_sub, Real.sin_sub]
    by_cases h0 : h = 0
    · subst h0; simp [c01_secant]
    have hne : y ≠ y - h := by intro e; apply h0; linarith
    simp only [c01_secant, hne, if_false, sub_sub_cancel, Real.sin_sub]
    have hh : |h| ^ (p + 1) ≠ 0 := (rpow_pos_of_pos (abs_pos.mpr h0) _).ne'
    field_simp
    ring
  simp_rw [hpt]
  have i30 : Integrable (fun h => g 3 0 h) := c04_aux_trig_int p hp hp1 3 0 rfl
  have i12 : Integrable (fun h => g 1 2 h) := c04_aux_trig_int p hp hp1 1 2 rfl
  have i21 : Integrable (fun h => g 2 1 h) := c04_aux_trig_int p hp hp1 2 1 rfl
  have i03 : Integrable (fun h => g 0 3 h) := c04_aux_trig_int p hp hp1 0 3 rfl
  have o21 : ∫ h, g 2 1 h = 0 := c04_aux_trig_odd p 2 1 odd_one
  have o03 : ∫ h, g 0 3 h = 0 := c04_aux_trig_odd p 0 3 (by decide)
  have hsum : ∫ x, (c * s ^ 2 * g 3 0 x + (c ^ 3 - 2 * s ^ 2 * c) * g 1 2 x +
      (2 * s * c ^ 2 - s ^ 3) * g 2 1 x - s * c ^ 2 * g 0 3 x) =
      c * s ^ 2 * (∫ x, g 3 0 x) + (c ^ 3 - 2 * s ^ 2 * c) * (∫ x, g 1 2 x) := by
    have j2 : Integrable (fun x => c * s ^ 2 * g 3 0 x + (c ^ 3 - 2 * s ^ 2 * c) * g 1 2 x) :=
      (i30.const_mul _).add (i12.const_mul _)
    have j1 : Integrable (fun x => c * s ^ 2 * g 3 0 x + (c ^ 3 - 2 * s ^ 2 * c) * g 1 2 x +
        (2 * s * c ^ 2 - s ^ 3) * g 2 1 x) := j2.add (i21.const_mul _)
    rw [integral_sub j1 (i03.const_mul _), integral_add j2 (i21.const_mul _),
      integral_add (i30.const_mul _) (i12.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, o21, o03]
    ring
  rw [hsum, Real.cos_three_mul]
  have hs : s ^ 2 = 1 - c ^ 2 := by rw [← Real.sin_sq_add_cos_sq y]; ring
  rw [hs]
  simp only [hg]
  ring


/-- Blueprint: lem:c04_cubic_sine_response.  `𝒬_{ε,3}(sin) = c₁(ε) cos y + c₂(ε) cos 3y` with
the (shared, Fourier-coefficient) constants `cubic_c1, cubic_c2`, which are the unique such reals;
`c_i(ε) = ε c_i(1)` and `|c_i(ε)| ≤ C₃ ε`. -/
theorem c04_cubic_sine_response (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C₃ > (0 : ℝ), ∀ ε : ℝ, 0 ≤ ε →
      (∀ y, c04_cubic_part p ε Real.sin y = cubic_c1 p ε * Real.cos y + cubic_c2 p ε * Real.cos (3 * y)) ∧
      (∀ a b : ℝ, (∀ y, c04_cubic_part p ε Real.sin y = a * Real.cos y + b * Real.cos (3 * y)) →
        a = cubic_c1 p ε ∧ b = cubic_c2 p ε) ∧
      cubic_c1 p ε = ε * cubic_c1 p 1 ∧ cubic_c2 p ε = ε * cubic_c2 p 1 ∧
      |cubic_c1 p ε| ≤ C₃ * ε ∧ |cubic_c2 p ε| ≤ C₃ * ε := by
  have hp0 : 0 < p := by linarith
  set I1 := ∫ h, (1 - Real.cos h) ^ 3 * Real.sin h ^ 0 * c04_aux_wt p h with hI1
  set I2 := ∫ h, (1 - Real.cos h) ^ 1 * Real.sin h ^ 2 * c04_aux_wt p h with hI2
  have hc : ∀ ε a b : ℝ, (∀ y, c04_cubic_part p ε Real.sin y = a * Real.cos y + b * Real.cos (3 * y)) →
      cubic_c1 p ε = a ∧ cubic_c2 p ε = b := by
    intro ε a b h
    constructor
    · unfold cubic_c1; simp_rw [h]; exact c04_aux_orth1 a b
    · unfold cubic_c2; simp_rw [h]; exact c04_aux_orth3 a b
  refine ⟨(p + 1) * |calpha p| * (3 * (|I1| + |I2|)) / 8 + 1, by positivity, fun ε hε => ?_⟩
  have hQ := c04_aux_Qsin p hp0 hp1 ε
  obtain ⟨h1, h2⟩ := hc ε _ _ hQ
  have hκ : |c04_cubic_part_kappa p ε| = (p + 1) * ε * |calpha p| / 2 := by
    unfold c04_cubic_part_kappa
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < p + 1),
      abs_of_nonneg hε, abs_two]
  have hK0 : 0 ≤ (p + 1) * ε * |calpha p| / 2 := by positivity
  refine ⟨fun y => by rw [h1, h2]; exact hQ y, fun a b hab => ?_, c04_aux_c1_lin p ε,
    c04_aux_c2_lin p ε, ?_, ?_⟩
  · obtain ⟨g1, g2⟩ := hc ε a b hab; exact ⟨g1.symm, g2.symm⟩
  · rw [h1, ← hI1, ← hI2, abs_div, abs_mul, hκ, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have ha := abs_add_le I1 I2
    have : (p + 1) * ε * |calpha p| / 2 * |I1 + I2| / 4 ≤
        (p + 1) * |calpha p| * (3 * (|I1| + |I2|)) / 8 * ε := by
      have := mul_le_mul_of_nonneg_left ha hK0
      nlinarith [abs_nonneg I1, abs_nonneg I2]
    have h0 : 0 ≤ ε := hε
    nlinarith [abs_nonneg (Real.cos 0)]
  · rw [h2, ← hI1, ← hI2, abs_div, abs_mul, hκ, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have ha : |3 * I2 - I1| ≤ 3 * (|I1| + |I2|) := by
      have := abs_sub (3 * I2) I1
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)] at this
      linarith [abs_nonneg I1]
    have : (p + 1) * ε * |calpha p| / 2 * |3 * I2 - I1| / 4 ≤
        (p + 1) * |calpha p| * (3 * (|I1| + |I2|)) / 8 * ε := by
      have := mul_le_mul_of_nonneg_left ha hK0
      nlinarith [abs_nonneg I1, abs_nonneg I2]
    nlinarith

/-- `|A_ε(t) - 1| ≤ ε` for `|t| ≤ 1`, `ε ≥ 0`, `0 < p ≤ 1`. -/
theorem c04_aux_A_sub_one (p ε t : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (ht : |t| ≤ 1) : |A_eps p ε t - 1| ≤ ε := by
  unfold A_eps
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  set x := ε * t ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ ε := by nlinarith
  set a := (p + 1) / 2
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by simp only [a]; linarith
  have h1 : (1 + x) ^ a ≤ 1 + a * x := rpow_one_add_le_one_add_mul_self (by linarith) ha0 ha1
  have h2 : 1 ≤ (1 + x) ^ a := one_le_rpow (by linarith) ha0
  have hneg : (1 + x) ^ (-(p + 1) / 2) = ((1 + x) ^ a)⁻¹ := by
    rw [show -(p + 1) / 2 = -a by simp only [a]; ring, rpow_neg (by linarith)]
  rw [hneg]
  have hpos : 0 < (1 + x) ^ a := by linarith
  have h3 : ((1 + x) ^ a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
  have h4 : 1 - a * x ≤ ((1 + x) ^ a)⁻¹ := by
    rw [← one_div, le_div_iff₀ hpos]
    have : 0 ≤ a * x := by positivity
    rcases le_or_gt (1 - a * x) 0 with h | h
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left h1 h.le]
  have : a * x ≤ x := by nlinarith
  rw [abs_le]; constructor <;> nlinarith

/-- `|∫₀¹ (A_ε(t)-1) w(t) dt| ≤ ε ∫₀¹ w` for a nonnegative weight `w`. -/
theorem c04_aux_int_A_bound (p ε : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hε : 0 ≤ ε) (w : ℝ → ℝ)
    (hw : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ w t) (hwi : IntervalIntegrable w volume 0 1) :
    |∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * w t| ≤ ε * ∫ t in (0 : ℝ)..1, w t := by
  rw [← intervalIntegral.integral_const_mul]
  have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := 1)
    (f := fun t => (A_eps p ε t - 1) * w t) (g := fun t => ε * w t) zero_le_one ?_ (hwi.const_mul ε)
  · simpa using this
  · refine Filter.Eventually.of_forall (fun t ht => ?_)
    have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw t htI)]
    have ht' : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    exact mul_le_mul_of_nonneg_right (c04_aux_A_sub_one p ε t hp0 hp1 hε ht') (hw t htI)

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_rpow_ii (p : ℝ) (hp : 0 < p) :
    IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith)

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_rpow_ii' (p : ℝ) (hp : 0 < p) :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (p - 1)) volume 0 1 := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (p - 1)) volume (1 - 1) (1 - 0) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  simpa using (hi.comp_sub_left 1).symm

/-- `|c_ε| ≤ C ε`. -/
theorem c04_aux_c_eps_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ C ≥ (0 : ℝ), ∀ ε, 0 ≤ ε → |c_eps p ε| ≤ C * ε := by
  refine ⟨|calpha p| * ∫ t in (0 : ℝ)..1, (1 - t) ^ (p - 1), ?_, fun ε hε => ?_⟩
  · apply mul_nonneg (abs_nonneg _)
    exact intervalIntegral.integral_nonneg zero_le_one (fun t ht => rpow_nonneg (by linarith [ht.2]) _)
  unfold c_eps
  rw [abs_mul, mul_comm (|calpha p|), mul_assoc, mul_comm]
  gcongr
  rw [mul_comm]
  exact c04_aux_int_A_bound p ε hp0 hp1 hε _ (fun t ht => rpow_nonneg (by linarith [ht.2]) _)
    (c04_aux_rpow_ii' p hp0)

/-- `|∫₀¹ (A_ε-1) t^{p-1}| ≤ C ε`. -/
theorem c04_aux_c_minus_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ C ≥ (0 : ℝ), ∀ ε, 0 ≤ ε → |c_minus p ε| ≤ C * ε := by
  refine ⟨|calpha p / (p + 1)| * ∫ t in (0 : ℝ)..1, t ^ (p - 1), ?_, fun ε hε => ?_⟩
  · apply mul_nonneg (abs_nonneg _)
    exact intervalIntegral.integral_nonneg zero_le_one (fun t ht => rpow_nonneg ht.1 _)
  unfold c_minus
  rw [abs_mul, mul_comm (|calpha p / (p + 1)|), mul_assoc, mul_comm]
  gcongr
  rw [mul_comm]
  exact c04_aux_int_A_bound p ε hp0 hp1 hε _ (fun t ht => rpow_nonneg ht.1 _)
    (c04_aux_rpow_ii p hp0)


/-- `∂^k(a t^r + b t^s) = a P_k(r) y^{r-k} + b P_k(s) y^{s-k}` at `y > 0`. -/
theorem c04_aux_iter_two_rpow (a b r s : ℝ) (k : ℕ) (y : ℝ) (hy : 0 < y) :
    iteratedDeriv k (fun t => a * t ^ r + b * t ^ s) y =
      a * (descPochhammer ℝ k).eval r * y ^ (r - k) + b * (descPochhammer ℝ k).eval s * y ^ (s - k) := by
  have h1 : ContDiffAt ℝ k (fun t : ℝ => t ^ r) y := contDiffAt_rpow_const_of_ne hy.ne'
  have h2 : ContDiffAt ℝ k (fun t : ℝ => t ^ s) y := contDiffAt_rpow_const_of_ne hy.ne'
  rw [iteratedDeriv_fun_add (contDiffAt_const.mul h1) (contDiffAt_const.mul h2)]
  rw [iteratedDeriv_const_mul a h1, iteratedDeriv_const_mul b h2]
  simp only [iteratedDeriv_eq_iterate, iter_deriv_rpow_const]
  ring

/-- Bound of the scalar constants (part 1 of lem:c04_constants_small). -/
theorem c04_aux_constants_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (Kμ : ℝ) (hK : 0 < Kμ) :
    ∃ C > (0 : ℝ), ∀ ε ∈ Icc (0 : ℝ) 1, ∀ μ : ℂ, ‖μ‖ ≤ Kμ →
      |c_eps p ε| ≤ C * ε ∧ |n_eps p ε| ≤ C * ε ∧ |c_cubic p ε| ≤ C * ε ∧
      |c_log p ε μ| ≤ C * ε ∧ |c_power p ε| ≤ C * ε ∧ |c_plus p ε| ≤ C * ε ∧
      |c_minus p ε| ≤ C * ε := by
  obtain ⟨Ce, hCe0, hCe⟩ := c04_aux_c_eps_bound p (by linarith) hp1.le
  obtain ⟨Cm, hCm0, hCm⟩ := c04_aux_c_minus_bound p (by linarith) hp1.le
  have hp0 : 0 < p := by linarith
  have h3 : 0 < (3 : ℝ) ^ p - 1 := by
    have : (1 : ℝ) < 3 ^ p := one_lt_rpow (by norm_num) hp0
    linarith
  have h1p : 0 < 1 - p ^ 2 := by nlinarith
  set c1 := |cubic_c1 p 1|
  set c2 := |cubic_c2 p 1|
  have hc1 : 0 ≤ c1 := abs_nonneg _
  have hc2 : 0 ≤ c2 := abs_nonneg _
  set K1 := 4 * c1
  set K2 := 4 * c2 / ((3 : ℝ) ^ p - 1)
  set K3 := 4 * c1 * Kμ ^ 2 / p
  set K4 := Ce / (1 - p ^ 2)
  set K5 := Ce / (p + 1)
  have hK1 : 0 ≤ K1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  have hK3 : 0 ≤ K3 := by positivity
  have hK4 : 0 ≤ K4 := by positivity
  have hK5 : 0 ≤ K5 := by positivity
  refine ⟨Ce + K1 + K2 + K3 + K4 + K5 + Cm + 1, by positivity, fun ε hε μ hμ => ?_⟩
  have hε0 := hε.1
  have hce := hCe ε hε0
  have hc1ε : |cubic_c1 p ε| = c1 * ε := by
    rw [c04_aux_c1_lin, abs_mul, abs_of_nonneg hε0, mul_comm]
  have hc2ε : |cubic_c2 p ε| = c2 * ε := by
    rw [c04_aux_c2_lin, abs_mul, abs_of_nonneg hε0, mul_comm]
  have hn : |n_eps p ε| ≤ K1 * ε := by
    unfold n_eps; rw [abs_mul, hc1ε]; simp only [K1]; norm_num; linarith
  have hcub : |c_cubic p ε| ≤ K2 * ε := by
    unfold c_cubic; rw [abs_div, abs_mul, hc2ε, abs_of_pos h3]; simp only [K2]
    apply le_of_eq; norm_num; ring
  have hlog : |c_log p ε μ| ≤ K3 * ε := by
    unfold c_log
    rw [abs_div, abs_neg, abs_mul, abs_of_pos hp0, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖μ‖ ^ 2)]
    have hμ2 : ‖μ‖ ^ 2 ≤ Kμ ^ 2 := by gcongr
    have : |n_eps p ε| * ‖μ‖ ^ 2 ≤ K1 * ε * Kμ ^ 2 :=
      mul_le_mul hn hμ2 (by positivity) (by positivity)
    calc |n_eps p ε| * ‖μ‖ ^ 2 / p ≤ K1 * ε * Kμ ^ 2 / p := by gcongr
      _ = K3 * ε := by simp only [K3, K1]; ring
  have hpow : |c_power p ε| ≤ K4 * ε := by
    unfold c_power; rw [abs_div, abs_neg, abs_of_pos h1p]; simp only [K4]
    rw [div_mul_eq_mul_div]; gcongr
  have hplus : |c_plus p ε| ≤ K5 * ε := by
    unfold c_plus; rw [abs_div, abs_neg, abs_of_pos (by linarith : 0 < p + 1)]; simp only [K5]
    rw [div_mul_eq_mul_div]; gcongr
  have hcm := hCm ε hε0
  have bnd : ∀ x K : ℝ, |x| ≤ K * ε → K ≤ Ce + K1 + K2 + K3 + K4 + K5 + Cm + 1 →
      |x| ≤ (Ce + K1 + K2 + K3 + K4 + K5 + Cm + 1) * ε :=
    fun x K hx hK => le_trans hx (mul_le_mul_of_nonneg_right hK hε0)
  exact ⟨bnd _ _ hce (by linarith), bnd _ _ hn (by linarith), bnd _ _ hcub (by linarith),
    bnd _ _ hlog (by linarith), bnd _ _ hpow (by linarith), bnd _ _ hplus (by linarith),
    bnd _ _ hcm (by linarith)⟩

/-- Blueprint: lem:c04_constants_small.  For `|μ| ≤ K_μ`, `ε ∈ [0,1]`: all correction constants
are `O(ε)`, vanish at `ε = 0`, `c_log` is continuous in `μ`, and
`|∂^k λ̃_{ε,μ}(y)| ≤ C_k ε y^{-p-1-k}` for `y ≥ 1`. -/
theorem c04_constants_small (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (Kμ : ℝ) (hK : 0 < Kμ) :
    (∃ C > (0 : ℝ), ∀ ε ∈ Icc (0 : ℝ) 1, ∀ μ : ℂ, ‖μ‖ ≤ Kμ →
      |c_eps p ε| ≤ C * ε ∧ |n_eps p ε| ≤ C * ε ∧ |c_cubic p ε| ≤ C * ε ∧
      |c_log p ε μ| ≤ C * ε ∧ |c_power p ε| ≤ C * ε ∧ |c_plus p ε| ≤ C * ε ∧
      |c_minus p ε| ≤ C * ε) ∧
    (c_eps p 0 = 0 ∧ n_eps p 0 = 0 ∧ c_cubic p 0 = 0 ∧ (∀ μ : ℂ, c_log p 0 μ = 0) ∧
      c_power p 0 = 0 ∧ c_plus p 0 = 0 ∧ c_minus p 0 = 0) ∧
    (∀ ε : ℝ, Continuous (c_log p ε)) ∧
    (∀ k : ℕ, ∃ C > (0 : ℝ), ∀ ε ∈ Icc (0 : ℝ) 1, ∀ μ : ℂ, ‖μ‖ ≤ Kμ → ∀ y ≥ (1 : ℝ),
      |iteratedDeriv k (lambda_tilde p ε μ) y| ≤ C * ε * y ^ (-p - 1 - k)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C0, hC0, hC⟩ := c04_aux_constants_bound p hp hp1 Kμ hK
  have he0 : c_eps p 0 = 0 := by simp [c_eps, A_eps]
  have hn0 : n_eps p 0 = 0 := by simp [n_eps, c04_aux_c1_lin p 0]
  refine ⟨⟨C0, hC0, hC⟩, ⟨he0, hn0, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [c_cubic, c04_aux_c2_lin p 0]
  · intro μ; simp [c_log, hn0]
  · simp [c_power, he0]
  · simp [c_plus, he0]
  · simp [c_minus, A_eps]
  · intro ε; unfold c_log; fun_prop
  · intro k
    set P := |(descPochhammer ℝ k).eval (-p - 1)|
    set Q := |(descPochhammer ℝ k).eval (-1 - 1 / p)|
    refine ⟨C0 / p * P + C0 * Q + 1, by positivity, fun ε hε μ hμ y hy => ?_⟩
    obtain ⟨hce, -, -, hcl, -⟩ := hC ε hε μ hμ
    have hy0 : 0 < y := by linarith
    have hfun : lambda_tilde p ε μ =
        fun t => (-(c_eps p ε / p)) * t ^ (-p - 1) + c_log p ε μ * t ^ (-1 - 1 / p) := rfl
    rw [hfun, c04_aux_iter_two_rpow _ _ _ _ k y hy0]
    have hexp : y ^ (-1 - 1 / p - k) ≤ y ^ (-p - 1 - k) := by
      apply rpow_le_rpow_of_exponent_le hy
      have : p ≤ 1 / p := by rw [le_div_iff₀ hp0]; nlinarith
      linarith
    have hpos1 : 0 ≤ y ^ (-p - 1 - (k : ℝ)) := rpow_nonneg hy0.le _
    have hpos2 : 0 ≤ y ^ (-1 - 1 / p - (k : ℝ)) := rpow_nonneg hy0.le _
    have ha : |(-(c_eps p ε / p))| ≤ C0 / p * ε := by
      rw [abs_neg, abs_div, abs_of_pos hp0, div_mul_eq_mul_div, mul_comm C0 ε]
      gcongr; linarith
    calc |(-(c_eps p ε / p)) * (descPochhammer ℝ k).eval (-p - 1) * y ^ (-p - 1 - (k : ℝ)) +
          c_log p ε μ * (descPochhammer ℝ k).eval (-1 - 1 / p) * y ^ (-1 - 1 / p - (k : ℝ))|
        ≤ |(-(c_eps p ε / p))| * P * y ^ (-p - 1 - (k : ℝ)) +
          |c_log p ε μ| * Q * y ^ (-1 - 1 / p - (k : ℝ)) := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hpos1, abs_of_nonneg hpos2]
      _ ≤ (C0 / p * ε) * P * y ^ (-p - 1 - (k : ℝ)) + (C0 * ε) * Q * y ^ (-p - 1 - (k : ℝ)) := by
          have hε0 := hε.1
          have : 0 ≤ C0 * ε * Q := by positivity
          gcongr
      _ ≤ (C0 / p * P + C0 * Q + 1) * ε * y ^ (-p - 1 - k) := by
          have hε0 := hε.1
          have : 0 ≤ ε * y ^ (-p - 1 - (k : ℝ)) := mul_nonneg hε0 hpos1
          have e : (C0 / p * ε) * P * y ^ (-p - 1 - (k : ℝ)) + (C0 * ε) * Q * y ^ (-p - 1 - (k : ℝ))
              = (C0 / p * P + C0 * Q) * (ε * y ^ (-p - 1 - (k : ℝ))) := by ring
          rw [e, mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) this

/-! ### The approximate solution family -/

/-- `λ_{ε,μ}` is differentiable on `(0,∞)`. -/
theorem c04_aux_lambda_diff (p ε : ℝ) (μ : ℂ) (y : ℝ) (hy : 0 < y) :
    DifferentiableAt ℝ (fam_lambda p ε μ) y := by
  unfold fam_lambda
  exact ((differentiableAt_id.rpow_const (Or.inl hy.ne')).add
    ((differentiableAt_id.rpow_const (Or.inl hy.ne')).const_mul _)).add
    ((differentiableAt_const _).div differentiableAt_id hy.ne')

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_lambda_contOn (p ε : ℝ) (μ : ℂ) : ContinuousOn (fam_lambda p ε μ) (Ioi 0) :=
  fun y hy => (c04_aux_lambda_diff p ε μ y hy).continuousAt.continuousWithinAt

/-- `Ψ' = λ` on `(0,∞)` (fundamental theorem of calculus). -/
theorem c04_aux_Psi_hasDeriv (p R ε : ℝ) (μ : ℂ) (hR : 0 < R) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fam_Psi p R ε μ) (fam_lambda p ε μ y) y := by
  unfold fam_Psi
  have hsub : uIcc R y ⊆ Ioi 0 := by
    intro t ht; rcases mem_uIcc.mp ht with h | h
    · exact lt_of_lt_of_le hR h.1
    · exact lt_of_lt_of_le hy h.1
  have hII : IntervalIntegrable (fam_lambda p ε μ) volume R y :=
    ((c04_aux_lambda_contOn p ε μ).mono hsub).intervalIntegrable
  have := intervalIntegral.integral_hasDerivAt_right hII
    ((c04_aux_lambda_contOn p ε μ).stronglyMeasurableAtFilter isOpen_Ioi y hy)
    (c04_aux_lambda_diff p ε μ y hy).continuousAt
  exact this.const_add _

/-- `a_*` is differentiable on `(0,∞)` (given smoothness of `f_{0,+}` and `μ_* ≠ 0`). -/
theorem c04_aux_astar_diff (p : ℝ) (_hp0 : 0 < p) (hplus : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p))
    (hμs : mu_star p ≠ 0) (y : ℝ) (hy : 0 < y) : DifferentiableAt ℝ (astar p) y := by
  have hl0 : 0 < lambda0 p y := rpow_pos_of_pos hy _
  have hd1 : DifferentiableAt ℝ (fun t => Psi0 p t - π / 4) y := by
    unfold Psi0
    exact ((differentiableAt_id.rpow_const (Or.inl hy.ne')).const_mul _).sub_const _
  have hd2 : DifferentiableAt ℝ (fun t => lambda0 p t ^ (-(p + 1) / 2)) y := by
    unfold lambda0
    exact (differentiableAt_id.rpow_const (Or.inl hy.ne')).rpow_const
      (Or.inl (rpow_pos_of_pos hy _).ne')
  have hE : DifferentiableAt ℝ (fun t => Complex.exp (-(Complex.I * ((Psi0 p t - π / 4 : ℝ) : ℂ)))) y :=
    ((hd1.hasDerivAt.ofReal_comp.const_mul Complex.I).neg.differentiableAt).cexp
  have hD : DifferentiableAt ℝ (fun t => mu_star p * ((lambda0 p t ^ (-(p + 1) / 2) : ℝ) : ℂ)) y :=
    (hd2.hasDerivAt.ofReal_comp.const_mul _).differentiableAt
  have hD0 : mu_star p * ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hμs (Complex.ofReal_ne_zero.mpr (rpow_pos_of_pos hl0 _).ne')
  have hF : DifferentiableAt ℝ (deriv (c04_linear_seed_plus p)) y :=
    ((contDiff_infty_iff_deriv.mp hplus).2.differentiable (by simp)) y
  unfold astar
  exact (hE.div hD hD0).mul hF

/-- `Z_{ε,μ}` is differentiable at `y > 0` with `λ(y) > 0`. -/
theorem c04_aux_famZ_diff (p R ε : ℝ) (μ : ℂ) (hp0 : 0 < p) (hR : 0 < R)
    (hplus : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p)) (hμs : mu_star p ≠ 0) (y : ℝ) (hy : 0 < y)
    (hlam : 0 < fam_lambda p ε μ y) : DifferentiableAt ℝ (fam_Z p R ε μ) y := by
  have h1 := c04_aux_astar_diff p hp0 hplus hμs y hy
  have h2 : DifferentiableAt ℝ (fun t => fam_lambda p ε μ t ^ (-(p + 1) / 2)) y :=
    (c04_aux_lambda_diff p ε μ y hy).rpow_const (Or.inl hlam.ne')
  have h3 : DifferentiableAt ℝ (fun t => fam_Psi p R ε μ t - π / 4) y :=
    (c04_aux_Psi_hasDeriv p R ε μ hR y hy).differentiableAt.sub_const _
  have hE : DifferentiableAt ℝ (fun t => Complex.exp (Complex.I * ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ))) y :=
    ((h3.hasDerivAt.ofReal_comp.const_mul Complex.I).differentiableAt).cexp
  unfold fam_Z
  exact (((differentiableAt_const μ).mul h1).mul h2.hasDerivAt.ofReal_comp.differentiableAt).mul hE


/-- The explicit primitive of `λ_{ε,μ}`. -/
theorem c04_aux_Fpsi_hasDeriv (p R ε : ℝ) (μ : ℂ) (hp0 : 0 < p) (hp1 : p < 1) (hR : 0 < R)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t => Psi0 p t + c_power p ε * (t ^ (1 / p - p) - R ^ (1 / p - p)) +
      c_log p ε μ * Real.log (t / R)) (fam_lambda p ε μ t) t := by
  have h1 := c04_aux_Psi0_hasDeriv p hp0 t ht
  have h2 := (((hasDerivAt_rpow_const (p := 1 / p - p) (Or.inl ht.ne')).sub_const
    (R ^ (1 / p - p))).const_mul (c_power p ε))
  have h3 := ((((hasDerivAt_id' t).div_const R).log (div_pos ht hR).ne').const_mul (c_log p ε μ))
  convert (h1.add h2).add h3 using 1
  simp only [fam_lambda, lambda0]
  field_simp

/-- Derivative bounds for `λ_{ε,μ}`: `|∂^k λ| ≤ C_k y^{1/p-k}` for `y ≥ 1`. -/
theorem c04_aux_lam_iter_bound (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (Cc : ℝ) (hCc : 0 ≤ Cc) (k : ℕ)
    (ε : ℝ) (μ : ℂ) (hcp : |c_power p ε| ≤ Cc) (hcl : |c_log p ε μ| ≤ Cc) (y : ℝ) (hy : 1 ≤ y) :
    |iteratedDeriv k (fam_lambda p ε μ) y| ≤
      (|(descPochhammer ℝ k).eval (1 / p)| + Cc * ((1 - p ^ 2) / p) *
        |(descPochhammer ℝ k).eval (1 / p - p - 1)| + Cc * |(descPochhammer ℝ k).eval (-1)|) *
        y ^ (1 / p - k) := by
  have hy0 : 0 < y := by linarith
  have h1p' : 0 < 1 - p ^ 2 := by nlinarith
  have h1p : 0 < (1 - p ^ 2) / p := by positivity
  have hev : fam_lambda p ε μ =ᶠ[𝓝 y] fun t => (1 * t ^ (1 / p) +
      (c_power p ε * ((1 - p ^ 2) / p)) * t ^ (1 / p - p - 1)) + c_log p ε μ * t ^ (-1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hy0] with t ht
    simp only [fam_lambda, rpow_neg_one, one_mul]
    ring
  have hA : ContDiffAt ℝ k (fun t : ℝ => 1 * t ^ (1 / p) +
      (c_power p ε * ((1 - p ^ 2) / p)) * t ^ (1 / p - p - 1)) y :=
    (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hy0.ne')).add
      (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hy0.ne'))
  have hB : ContDiffAt ℝ k (fun t : ℝ => c_log p ε μ * t ^ (-1 : ℝ)) y :=
    contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hy0.ne')
  rw [hev.iteratedDeriv_eq, iteratedDeriv_fun_add hA hB, c04_aux_iter_two_rpow _ _ _ _ k y hy0,
    iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_rpow_const]
  have e1 : y ^ (1 / p - p - 1 - (k : ℝ)) ≤ y ^ (1 / p - k) :=
    rpow_le_rpow_of_exponent_le hy (by linarith)
  have hip : 0 < 1 / p := by positivity
  have e2 : y ^ ((-1 : ℝ) - k) ≤ y ^ (1 / p - k) :=
    rpow_le_rpow_of_exponent_le hy (by linarith)
  have p1 : 0 ≤ y ^ (1 / p - (k : ℝ)) := (rpow_pos_of_pos hy0 _).le
  have p2 : 0 ≤ y ^ (1 / p - p - 1 - (k : ℝ)) := (rpow_pos_of_pos hy0 _).le
  have p3 : 0 ≤ y ^ ((-1 : ℝ) - (k : ℝ)) := (rpow_pos_of_pos hy0 _).le
  have ha : |c_power p ε * ((1 - p ^ 2) / p)| ≤ Cc * ((1 - p ^ 2) / p) := by
    rw [abs_mul, abs_of_pos h1p]; exact mul_le_mul_of_nonneg_right hcp h1p.le
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
  simp only [abs_mul, one_mul, abs_one, abs_of_nonneg p1, abs_of_nonneg p2, abs_of_nonneg p3]
  have q1 := abs_nonneg ((descPochhammer ℝ k).eval (1 / p - p - 1))
  have q2 := abs_nonneg ((descPochhammer ℝ k).eval (-1))
  calc |(descPochhammer ℝ k).eval (1 / p)| * y ^ (1 / p - (k : ℝ)) +
        |c_power p ε| * |(1 - p ^ 2) / p| * |(descPochhammer ℝ k).eval (1 / p - p - 1)| *
          y ^ (1 / p - p - 1 - (k : ℝ)) +
        |c_log p ε μ| * (|(descPochhammer ℝ k).eval (-1)| * y ^ ((-1 : ℝ) - (k : ℝ)))
      ≤ |(descPochhammer ℝ k).eval (1 / p)| * y ^ (1 / p - (k : ℝ)) +
        Cc * ((1 - p ^ 2) / p) * |(descPochhammer ℝ k).eval (1 / p - p - 1)| * y ^ (1 / p - (k : ℝ)) +
        Cc * (|(descPochhammer ℝ k).eval (-1)| * y ^ (1 / p - (k : ℝ))) := by
        rw [← abs_mul (c_power p ε)]
        gcongr
    _ = _ := by ring

/-- `|∂^k λ^{-q}| ≤ C y^{-q/p-k}` (Faà di Bruno + Leibniz), uniformly. -/
theorem c04_aux_lamq_bound (p q : ℝ) (hp0 : 0 < p) (hq : 0 < q) (k : ℕ) (Cl : ℕ → ℝ)
    (hCl : ∀ i, 0 ≤ Cl i) : ∃ C ≥ (0 : ℝ), ∀ (ε : ℝ) (μ : ℂ) (R : ℝ), 2 ≤ R →
      (∀ t ≥ (1 : ℝ), |lambda_tilde p ε μ t| ≤ 1 / 2) →
      (∀ i : ℕ, ∀ t ≥ (1 : ℝ), |iteratedDeriv i (lambda_tilde p ε μ) t| ≤ Cl i * t ^ (-p - 1 - i)) →
      (∀ t > (0 : ℝ), fam_lambda p ε μ t = lambda0 p t * (1 + lambda_tilde p ε μ t)) →
      ∀ y > R / 2, |iteratedDeriv k (fun t => fam_lambda p ε μ t ^ (-q)) y| ≤ C * y ^ (-q / p - k) := by
  set K := 1 + ∑ i ∈ Finset.range (k + 1), Cl i with hKdef
  set Cg := ∑ i ∈ Finset.range (k + 1), |(descPochhammer ℝ i).eval (-q)| * 2 ^ (q + i) with hCgdef
  set A := ∑ i ∈ Finset.range (k + 1), |(descPochhammer ℝ i).eval (-q / p)| with hAdef
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), Cl i := Finset.sum_nonneg (fun i _ => hCl i)
    linarith
  have hCg0 : 0 ≤ Cg := Finset.sum_nonneg (fun i _ => by positivity)
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set B := (k.factorial : ℝ) * Cg * K ^ k with hBdef
  have hB0 : 0 ≤ B := by positivity
  refine ⟨2 ^ k * (A * B), by positivity, fun ε μ R hR hLt hLd hid y hy => ?_⟩
  have hy1 : 1 < y := by linarith
  have hy0 : 0 < y := by linarith
  set L := lambda_tilde p ε μ with hLdef
  set u : ℝ → ℝ := fun t => 1 + L t with hudef
  have hLsm : ∀ t > (0 : ℝ), ContDiffAt ℝ k L t := fun t ht => by
    simp only [hLdef, lambda_tilde]
    exact (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne ht.ne')).add
      (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne ht.ne'))
  have hupos : ∀ t ≥ (1 : ℝ), 1 / 2 ≤ u t ∧ u t ≤ 3 / 2 := fun t ht => by
    have := abs_le.mp (hLt t ht); simp only [hudef]; constructor <;> linarith
  -- `λ^{-q} = t^{-q/p} u^{-q}` near `y`
  have hev : (fun t => fam_lambda p ε μ t ^ (-q)) =ᶠ[𝓝 y]
      (fun t : ℝ => t ^ (-q / p)) * (fun t => u t ^ (-q)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    have ht1 : 1 ≤ t := by linarith [mem_Ioi.mp ht]
    have ht0 : 0 < t := by linarith
    simp only [Pi.mul_apply]
    have hl : lambda0 p t = t ^ (1 / p) := rfl
    rw [hid t ht0, hl, mul_rpow (rpow_pos_of_pos ht0 _).le (by linarith [(hupos t ht1).1]),
      ← rpow_mul ht0.le]
    simp only [hudef]; ring_nf
  rw [hev.iteratedDeriv_eq]
  have hfC : ContDiffAt ℝ k (fun t : ℝ => t ^ (-q / p)) y := contDiffAt_rpow_const_of_ne hy0.ne'
  have hgC : ContDiffAt ℝ k (fun t => u t ^ (-q)) y := by
    have hu := (contDiffAt_const (c := (1:ℝ))).add (hLsm y hy0)
    exact hu.rpow_const_of_ne (by linarith [(hupos y hy1.le).1])
  have hres := c04_aux_leibniz (fun t : ℝ => t ^ (-q / p)) (fun t => u t ^ (-q)) y hy0 k hfC hgC
    A B (-q / p) 0 (-1) ?_ ?_
  · rw [Real.norm_eq_abs] at hres
    refine hres.trans (le_of_eq ?_)
    congr 1; ring_nf
  · intro i hi
    rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, Real.norm_eq_abs, abs_mul,
      abs_of_pos (rpow_pos_of_pos hy0 _)]
    have : |(descPochhammer ℝ i).eval (-q / p)| ≤ A :=
      Finset.single_le_sum (f := fun i => |(descPochhammer ℝ i).eval (-q / p)|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    refine (mul_le_mul_of_nonneg_right this (rpow_pos_of_pos hy0 _).le).trans (le_of_eq ?_)
    congr 2; ring
  · intro i hi
    have hT : IsOpen (Ioo (1 / 4 : ℝ) 2) := isOpen_Ioo
    have hS : IsOpen (Ioi (R / 2)) := isOpen_Ioi
    have hgo : ContDiffOn ℝ i (fun x : ℝ => x ^ (-q)) (Ioo (1 / 4 : ℝ) 2) := fun x hx =>
      (contDiffAt_rpow_const_of_ne (by linarith [hx.1] : x ≠ 0)).contDiffWithinAt
    have huo : ContDiffOn ℝ i u (Ioi (R / 2)) := fun t ht => by
      have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
      have : ContDiffAt ℝ i L t := by
        simp only [hLdef, lambda_tilde]
        exact (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne ht0.ne')).add
          (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne ht0.ne'))
      exact (contDiffAt_const.add this).contDiffWithinAt
    have hmap : MapsTo u (Ioi (R / 2)) (Ioo (1 / 4 : ℝ) 2) := fun t ht => by
      have := hupos t (by linarith [mem_Ioi.mp ht]); exact ⟨by linarith, by linarith⟩
    have hfdb := c04_aux_fdb (fun x : ℝ => x ^ (-q)) u (Ioi (R / 2)) (Ioo (1 / 4 : ℝ) 2) hS hT i
      hgo huo hmap y hy Cg (K * y⁻¹) ?_ ?_
    · have hyi : 0 < y⁻¹ := inv_pos.mpr hy0
      refine hfdb.trans ?_
      have hfac : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
      have hKi : K ^ i ≤ K ^ k := pow_le_pow_right₀ hK1 hi
      have e : (K * y⁻¹) ^ i = K ^ i * y ^ (0 + (i : ℝ) * (-1)) := by
        rw [mul_pow, zero_add, show (i : ℝ) * (-1) = -(i : ℝ) by ring, rpow_neg hy0.le,
          rpow_natCast, inv_pow]
      rw [e, hBdef]
      have hY : 0 ≤ y ^ (0 + (i : ℝ) * (-1)) := (rpow_pos_of_pos hy0 _).le
      calc (i.factorial : ℝ) * Cg * (K ^ i * y ^ (0 + (i : ℝ) * (-1)))
          ≤ (k.factorial : ℝ) * Cg * (K ^ k * y ^ (0 + (i : ℝ) * (-1))) := by gcongr
        _ = _ := by ring
    · intro j hj
      have hj' : j ≤ k := le_trans hj hi
      rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hu1 := hupos y hy1.le
      have hpow : |u y ^ (-q - j)| ≤ 2 ^ (q + j) := by
        rw [abs_of_pos (rpow_pos_of_pos (by linarith) _)]
        have := rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1 / 2) hu1.1
          (show -q - (j : ℝ) ≤ 0 by have : (0:ℝ) ≤ j := Nat.cast_nonneg j
                                    linarith)
        refine this.trans (le_of_eq ?_)
        rw [one_div, inv_rpow (by norm_num), ← rpow_neg (by norm_num)]; ring_nf
      have hmem : |(descPochhammer ℝ j).eval (-q)| * 2 ^ (q + j) ≤ Cg :=
        Finset.single_le_sum (f := fun i => |(descPochhammer ℝ i).eval (-q)| * 2 ^ (q + i))
          (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj'))
      calc |(descPochhammer ℝ j).eval (-q)| * |u y ^ (-q - j)|
          ≤ |(descPochhammer ℝ j).eval (-q)| * 2 ^ (q + j) := by gcongr
        _ ≤ Cg := hmem
    · intro j hj1 hj
      have hj' : j ≤ k := le_trans hj hi
      have hder : iteratedDeriv j u y = iteratedDeriv j L y := by
        simp only [hudef]; exact iteratedDeriv_const_add (by omega) 1
      rw [hder]
      refine (hLd j y hy1.le).trans ?_
      have hClK : Cl j ≤ K := by
        have : Cl j ≤ ∑ i ∈ Finset.range (k + 1), Cl i :=
          Finset.single_le_sum (fun i _ => hCl i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj'))
        linarith
      have hKj : K ≤ K ^ j := by
        calc K = K ^ 1 := (pow_one K).symm
          _ ≤ K ^ j := pow_le_pow_right₀ hK1 hj1
      have hyexp : y ^ (-p - 1 - (j : ℝ)) ≤ (y⁻¹) ^ j := by
        rw [inv_pow, ← rpow_natCast, ← rpow_neg hy0.le]
        exact rpow_le_rpow_of_exponent_le hy1.le (by linarith)
      rw [mul_pow]
      exact mul_le_mul (hClK.trans hKj) hyexp (rpow_pos_of_pos hy0 _).le (by positivity)

/-- `λ_{ε,μ}` is smooth on `(0,∞)`. -/
theorem c04_aux_lambda_contDiffOn (p ε : ℝ) (μ : ℂ) (n : ℕ) :
    ContDiffOn ℝ n (fam_lambda p ε μ) (Ioi 0) := fun t ht => by
  have ht0 : 0 < t := ht
  unfold fam_lambda
  exact (((contDiffAt_rpow_const_of_ne ht0.ne').add (contDiffAt_const.mul
    (contDiffAt_rpow_const_of_ne ht0.ne'))).add (contDiffAt_const.div contDiffAt_id ht0.ne')).contDiffWithinAt

/-- `Ψ_{ε,μ}` is smooth on `(0,∞)`. -/
theorem c04_aux_Psi_contDiffOn (p R ε : ℝ) (μ : ℂ) (hR : 0 < R) (n : ℕ) :
    ContDiffOn ℝ n (fam_Psi p R ε μ) (Ioi 0) := by
  cases n with
  | zero =>
    exact contDiffOn_zero.mpr (fun t ht => (c04_aux_Psi_hasDeriv p R ε μ hR t ht).continuousAt.continuousWithinAt)
  | succ m =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun t ht => (c04_aux_Psi_hasDeriv p R ε μ hR t ht).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (c04_aux_lambda_contDiffOn p ε μ m).congr
      (fun t ht => (c04_aux_Psi_hasDeriv p R ε μ hR t ht).deriv)

/-- `‖∂^k e^{iΨ}‖ ≤ C y^{k/p}` given `|∂^i λ| ≤ C_i y^{1/p-i}`. -/
theorem c04_aux_expPsi_bound (p : ℝ) (hp0 : 0 < p) (k : ℕ) (Cl : ℕ → ℝ) (hCl : ∀ i, 0 ≤ Cl i) :
    ∃ C ≥ (0 : ℝ), ∀ (ε : ℝ) (μ : ℂ) (R : ℝ), 2 ≤ R →
      (∀ i : ℕ, ∀ t ≥ (1 : ℝ), |iteratedDeriv i (fam_lambda p ε μ) t| ≤ Cl i * t ^ (1 / p - i)) →
      ∀ y > R / 2, ‖iteratedDeriv k (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) y‖ ≤
        C * y ^ ((k : ℝ) / p) := by
  set K := 1 + ∑ i ∈ Finset.range (k + 1), Cl i with hKdef
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), Cl i := Finset.sum_nonneg (fun i _ => hCl i)
    linarith
  refine ⟨(k.factorial : ℝ) * K ^ k, by positivity, fun ε μ R hR hLb y hy => ?_⟩
  have hR0 : 0 < R := by linarith
  have hy1 : 1 < y := by linarith
  have hy0 : 0 < y := by linarith
  have hS : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hfun : (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) =
      (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) ∘ fam_Psi p R ε μ := rfl
  rw [hfun]
  have hg : ContDiffOn ℝ k (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) univ :=
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).contDiffOn
  have h := c04_aux_fdb (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) (fam_Psi p R ε μ)
    (Ioi 0) univ hS isOpen_univ k hg (c04_aux_Psi_contDiffOn p R ε μ hR0 k) (mapsTo_univ _ _) y hy0
    1 (K * y ^ (1 / p)) (fun i _ => le_of_eq (c04_aux_norm_iter_expI i _)) ?_
  · refine h.trans (le_of_eq ?_)
    rw [mul_one, mul_pow, ← rpow_natCast (y ^ (1 / p)), ← rpow_mul hy0.le]
    ring_nf
  · intro i hi1 hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hev : deriv (fam_Psi p R ε μ) =ᶠ[𝓝 y] fam_lambda p ε μ := by
      filter_upwards [Ioi_mem_nhds hy0] with t ht
      exact (c04_aux_Psi_hasDeriv p R ε μ hR0 t ht).deriv
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
    refine (hLb j y hy1.le).trans ?_
    have hClK : Cl j ≤ K := by
      have : Cl j ≤ ∑ i ∈ Finset.range (k + 1), Cl i :=
        Finset.single_le_sum (fun i _ => hCl i) (Finset.mem_range.mpr (by omega))
      linarith
    have hKj : K ≤ K ^ (j + 1) := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ (j + 1) := pow_le_pow_right₀ hK1 (by omega)
    have hyexp : y ^ (1 / p - (j : ℝ)) ≤ (y ^ (1 / p)) ^ (j + 1) := by
      rw [← rpow_natCast (y ^ (1 / p)), ← rpow_mul hy0.le]
      apply rpow_le_rpow_of_exponent_le hy1.le
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have : 0 ≤ (j : ℝ) / p := by positivity
      push_cast
      have e : 1 / p * ((j : ℝ) + 1) = 1 / p + j / p := by ring
      rw [e]; linarith
    rw [mul_pow]
    exact mul_le_mul (hClK.trans hKj) hyexp (rpow_pos_of_pos hy0 _).le (by positivity)

/-- Blueprint: lem:c04_phase_basic.  For `y > R/2`: (1) `λ = λ₀(1+λ̃)`, `y^{1/p}/2 ≤ λ ≤ 3y^{1/p}/2`,
derivative bounds for `λ` and `λ^{-q}`; (2) the explicit formula for `Ψ` and
`|∂^k e^{iΨ}| ≤ C_k y^{k/p}`; (3) the `ε = 0` identities and `Z₀ = f_{0,+}'`. -/
theorem c04_phase_basic (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      -- identities and two-sided bound
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y > R / 2,
        fam_lambda p ε μ y = lambda0 p y * (1 + lambda_tilde p ε μ y) ∧
        y ^ (1 / p) / 2 ≤ fam_lambda p ε μ y ∧ fam_lambda p ε μ y ≤ 3 / 2 * y ^ (1 / p) ∧
        fam_Psi p R ε μ y = Psi0 p y + c_power p ε * (y ^ (1 / p - p) - R ^ (1 / p - p)) +
          c_log p ε μ * Real.log (y / R)) ∧
      -- derivative bounds (admissible constants)
      (∀ (k : ℕ) (q : ℝ), 0 < q → ∃ C > (0 : ℝ),
        ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y > R / 2,
          |iteratedDeriv k (fam_lambda p ε μ) y| ≤ C * y ^ (1 / p - k) ∧
          |iteratedDeriv k (fun t => fam_lambda p ε μ t ^ (-q)) y| ≤ C * y ^ (-q / p - k) ∧
          ‖iteratedDeriv k (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) y‖ ≤
            C * y ^ ((k : ℝ) / p)) ∧
      -- (3) the case ε = 0
      (c_cubic p 0 = 0 ∧ c_plus p 0 = 0 ∧ c_minus p 0 = 0) ∧
      (∀ R ≥ R₀, ∀ μ ∈ Bbar p δ, ∀ y > R / 2,
        fam_lambda p 0 μ y = lambda0 p y ∧ fam_Psi p R 0 μ y = Psi0 p y ∧
        fam_Z p R 0 μ y = μ / mu_star p * fam_Z0 p R y ∧
        fam_Z0 p R y = deriv (c04_linear_seed_plus p) y) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs' : 0 < ‖mu_star p‖ := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp hμs'
  obtain ⟨⟨Cc, hCc, hcs⟩, ⟨-, -, hcc0, hcl0, hcp0, hcplus0, hcm0⟩, -, hcs4⟩ :=
    c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)
  obtain ⟨C0, hC0, hl0⟩ := hcs4 0
  have hμK : ∀ μ ∈ Bbar p δ, ‖μ‖ ≤ 2 * ‖mu_star p‖ := fun μ hμ => by
    have := norm_le_of_mem_closedBall hμ; linarith
  have hε₀ : min 1 (1 / (2 * C0)) ∈ Ioc (0 : ℝ) 1 := ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  -- `|λ̃| ≤ 1/2` for `t ≥ 1`
  have hLt : ∀ ε ∈ Icc (0 : ℝ) (min 1 (1 / (2 * C0))), ∀ μ ∈ Bbar p δ, ∀ t ≥ (1 : ℝ),
      |lambda_tilde p ε μ t| ≤ 1 / 2 := by
    intro ε hε μ hμ t ht
    have h := hl0 ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩ μ (hμK μ hμ) t ht
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
    have h1 : t ^ (-p - 1) ≤ 1 := rpow_le_one_of_one_le_of_nonpos ht (by linarith)
    have h2 : C0 * ε ≤ 1 / 2 := by
      have := hε.2.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at this; linarith
    have h3 : C0 * ε * t ^ (-p - 1) ≤ C0 * ε := by
      have : 0 ≤ C0 * ε := mul_nonneg hC0.le hε.1
      nlinarith [rpow_nonneg (show (0:ℝ) ≤ t by linarith) (-p - 1)]
    linarith
  -- `λ = λ₀ (1 + λ̃)`
  have hid : ∀ ε (μ : ℂ), ∀ t > (0 : ℝ), fam_lambda p ε μ t = lambda0 p t * (1 + lambda_tilde p ε μ t) := by
    intro ε μ t ht
    have e1 : t ^ (1 / p) * t ^ (-p - 1) = t ^ (1 / p - p - 1) := by rw [← rpow_add ht]; ring_nf
    have e2 : t ^ (1 / p) * t ^ (-1 - 1 / p) = t⁻¹ := by
      rw [← rpow_add ht, show 1 / p + (-1 - 1 / p) = -1 by ring, rpow_neg_one]
    have h1p : 1 - p ^ 2 ≠ 0 := by nlinarith
    simp only [fam_lambda, lambda0, lambda_tilde, c_power]
    rw [show t ^ (1 / p) * (1 + (-(c_eps p ε / p) * t ^ (-p - 1) + c_log p ε μ * t ^ (-1 - 1 / p))) =
      t ^ (1 / p) - c_eps p ε / p * (t ^ (1 / p) * t ^ (-p - 1)) +
        c_log p ε μ * (t ^ (1 / p) * t ^ (-1 - 1 / p)) by ring, e1, e2]
    field_simp
    ring
  -- the formula for `Ψ`
  have hPsi : ∀ R ≥ (2 : ℝ), ∀ ε (μ : ℂ), ∀ y > (0 : ℝ), fam_Psi p R ε μ y =
      Psi0 p y + c_power p ε * (y ^ (1 / p - p) - R ^ (1 / p - p)) + c_log p ε μ * Real.log (y / R) := by
    intro R hR ε μ y hy
    have hR0 : 0 < R := by linarith
    have hsub : uIcc R y ⊆ Ioi 0 := by
      intro t ht; rcases mem_uIcc.mp ht with h | h
      · exact lt_of_lt_of_le hR0 h.1
      · exact lt_of_lt_of_le hy h.1
    have hI : IntervalIntegrable (fam_lambda p ε μ) volume R y :=
      ((c04_aux_lambda_contOn p ε μ).mono hsub).intervalIntegrable
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => c04_aux_Fpsi_hasDeriv p R ε μ hp0 hp1 hR0 t (hsub ht)) hI
    unfold fam_Psi
    rw [this, div_self hR0.ne', Real.log_one]
    ring
  refine ⟨min 1 (1 / (2 * C0)), hε₀, 2, le_rfl, ?_, ?_, ⟨hcc0, hcplus0, hcm0⟩, ?_⟩
  · intro R hR ε hε μ hμ y hy
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hl := abs_le.mp (hLt ε hε μ hμ y hy1)
    have hl0p : 0 < lambda0 p y := rpow_pos_of_pos hy0 _
    have hl0e : lambda0 p y = y ^ (1 / p) := rfl
    refine ⟨hid ε μ y hy0, ?_, ?_, hPsi R hR ε μ y hy0⟩
    · rw [hid ε μ y hy0, ← hl0e]; nlinarith
    · rw [hid ε μ y hy0, ← hl0e]; nlinarith
  · intro k q hq
    obtain ⟨Cc, hCc, hcs1⟩ := (c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)).1
    choose Ct hCt0 hCt using hcs4
    set Cl : ℕ → ℝ := fun i => |(descPochhammer ℝ i).eval (1 / p)| + Cc * ((1 - p ^ 2) / p) *
        |(descPochhammer ℝ i).eval (1 / p - p - 1)| + Cc * |(descPochhammer ℝ i).eval (-1)| with hCldef
    have h1p : 0 < 1 - p ^ 2 := by nlinarith
    have hCl0 : ∀ i, 0 ≤ Cl i := fun i => by simp only [hCldef]; positivity
    obtain ⟨Cq, hCq0, hqb⟩ := c04_aux_lamq_bound p q hp0 hq k Ct (fun i => (hCt0 i).le)
    obtain ⟨Ce, hCe0, heb⟩ := c04_aux_expPsi_bound p hp0 k Cl hCl0
    refine ⟨Cl k + Cq + Ce + 1, by have := hCl0 k; linarith, fun R hR ε hε μ hμ y hy => ?_⟩
    have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
    have hμK' := hμK μ hμ
    obtain ⟨-, -, -, hcl, hcp, -, -⟩ := hcs1 ε hε1 μ hμK'
    have hcp' : |c_power p ε| ≤ Cc := hcp.trans (by nlinarith [hε1.1, hε1.2])
    have hcl' : |c_log p ε μ| ≤ Cc := hcl.trans (by nlinarith [hε1.1, hε1.2])
    have hLam : ∀ i : ℕ, ∀ t ≥ (1 : ℝ), |iteratedDeriv i (fam_lambda p ε μ) t| ≤ Cl i * t ^ (1 / p - i) :=
      fun i t ht => c04_aux_lam_iter_bound p hp0 hp1 Cc hCc.le i ε μ hcp' hcl' t ht
    have hy1 : 1 ≤ y := by linarith
    have hy0 : 0 < y := by linarith
    refine ⟨?_, ?_, ?_⟩
    · refine (hLam k y hy1).trans (mul_le_mul_of_nonneg_right ?_ (rpow_pos_of_pos hy0 _).le)
      linarith
    · refine (hqb ε μ R hR (hLt ε hε μ hμ) (fun i t ht => ?_) (hid ε μ) y hy).trans
        (mul_le_mul_of_nonneg_right (by linarith [hCl0 k]) (rpow_pos_of_pos hy0 _).le)
      refine (hCt i ε hε1 μ hμK' t ht).trans ?_
      have ht0 : 0 ≤ t ^ (-p - 1 - (i : ℝ)) := (rpow_pos_of_pos (by linarith) _).le
      have := (hCt0 i).le
      calc Ct i * ε * t ^ (-p - 1 - (i : ℝ)) ≤ Ct i * 1 * t ^ (-p - 1 - (i : ℝ)) := by
            gcongr; exact hε1.2
        _ = _ := by ring
    · refine (heb ε μ R hR hLam y hy).trans
        (mul_le_mul_of_nonneg_right (by linarith [hCl0 k]) (rpow_pos_of_pos hy0 _).le)
  · intro R hR μ hμ y hy
    have hy0 : 0 < y := by linarith
    have hlam0 : ∀ ν : ℂ, ∀ t : ℝ, fam_lambda p 0 ν t = lambda0 p t := by
      intro ν t; simp [fam_lambda, lambda0, hcp0, hcl0]
    have hpsi0 : ∀ ν : ℂ, fam_Psi p R 0 ν y = Psi0 p y := by
      intro ν; rw [hPsi R hR 0 ν y hy0, hcp0, hcl0]; ring
    have hZ0eq : fam_Z0 p R y = deriv (c04_linear_seed_plus p) y := by
      unfold fam_Z0 fam_Z astar
      rw [hlam0, hpsi0]
      have hE : Complex.exp (Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      have hL : ((lambda0 p y ^ (-(p + 1) / 2) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (rpow_pos_of_pos (rpow_pos_of_pos hy0 _) _).ne'
      rw [Complex.exp_neg]
      field_simp
      exact mul_div_cancel_left₀ _
        (Complex.ofReal_ne_zero.mpr (rpow_pos_of_pos (rpow_pos_of_pos hy0 _) _).ne')
    refine ⟨hlam0 μ y, hpsi0 μ, ?_, hZ0eq⟩
    unfold fam_Z0 fam_Z
    rw [hlam0 μ, hlam0 (mu_star p), hpsi0 μ, hpsi0 (mu_star p)]
    field_simp

/-- Pointwise data on `(R/2,∞)` from lem:c04_phase_basic: `1+λ̃ > 0` and `λ > 0`. -/
theorem c04_aux_lam_pos (p ε : ℝ) (μ : ℂ) (y : ℝ) (hy : 0 < y)
    (h1 : fam_lambda p ε μ y = lambda0 p y * (1 + lambda_tilde p ε μ y))
    (h2 : y ^ (1 / p) / 2 ≤ fam_lambda p ε μ y) :
    0 < fam_lambda p ε μ y ∧ 0 < 1 + lambda_tilde p ε μ y := by
  have hl : 0 < lambda0 p y := rpow_pos_of_pos hy _
  have hl' : lambda0 p y = y ^ (1 / p) := rfl
  have hpos : 0 < fam_lambda p ε μ y := lt_of_lt_of_le (by rw [← hl']; positivity) h2
  refine ⟨hpos, ?_⟩
  rw [h1] at hpos
  exact pos_of_mul_pos_right hpos hl.le


/-- `‖e^{ix}‖ = 1`. -/
theorem c04_aux_norm_exp_I (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x


/-- Blueprint: lem:c04_Z_bounds.  For `y ≥ R`: `|∂^j Z| ≤ C y^{-β+j/p}`,
`|∂^j Z³| ≤ C y^{-3β+j/p}`, `|∂^j(Z/λ)| ≤ C y^{-β-1/p+j/p}`, `|∂^j(a_*λ^{-q})| ≤ C y^{-q/p-j}`,
and `∫_y^∞ |Z| ≤ C y^{1-β}`. -/
theorem c04_Z_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ (j : ℕ) (q : ℝ), 0 < q → ∃ C > (0 : ℝ),
        ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
          ‖iteratedDeriv j (fam_Z p R ε μ) y‖ ≤ C * y ^ (-beta p + j / p) ∧
          ‖iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y‖ ≤ C * y ^ (-3 * beta p + j / p) ∧
          ‖iteratedDeriv j (fun t => fam_Z p R ε μ t / (fam_lambda p ε μ t : ℂ)) y‖ ≤
            C * y ^ (-beta p - 1 / p + j / p) ∧
          ‖iteratedDeriv j (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ)) y‖ ≤
            C * y ^ (-q / p - j)) ∧
      (∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        IntegrableOn (fun t => ‖fam_Z p R ε μ t‖) (Ioi y) ∧
        ∫ t in Ioi y, ‖fam_Z p R ε μ t‖ ≤ C * y ^ (1 - beta p)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hbasic, hder, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨y₀, hy₀, -, hamp⟩ := c04_seed_amplitude p hp hp1
  choose Ca hCa0 hCa using hamp
  choose Cpb hCpb0 hCpb using hder
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  have hβq : (p + 1) / 2 / p = beta p := by unfold beta; field_simp
  have hq1 : (0 : ℝ) < (p + 1) / 2 := by positivity
  have hR₀ : max R₁ y₀ ≥ 2 := le_trans hR₁ (le_max_left _ _)
  -- the main pointwise derivative bounds
  have hpart1 : ∀ (j : ℕ) (q : ℝ), 0 < q → ∃ C > (0 : ℝ),
      ∀ R ≥ max R₁ y₀, ∀ ε ∈ Icc (0 : ℝ) ε₁, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        (∀ i, i ≤ j → ‖iteratedDeriv i (fam_Z p R ε μ) y‖ ≤ C * y ^ (-beta p + i / p)) ∧
        ‖iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y‖ ≤ C * y ^ (-3 * beta p + j / p) ∧
        ‖iteratedDeriv j (fun t => fam_Z p R ε μ t / (fam_lambda p ε μ t : ℂ)) y‖ ≤
          C * y ^ (-beta p - 1 / p + j / p) ∧
        ‖iteratedDeriv j (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ)) y‖ ≤
          C * y ^ (-q / p - j) := by
    intro j q hq
    set Aa := ∑ i ∈ Finset.range (j + 1), Ca i with hAa
    set AL := ∑ i ∈ Finset.range (j + 1), Cpb i ((p + 1) / 2) hq1 with hAL
    set A1 := ∑ i ∈ Finset.range (j + 1), Cpb i 1 one_pos with hA1
    set Aq := ∑ i ∈ Finset.range (j + 1), Cpb i q hq with hAq
    have hAa0 : 0 ≤ Aa := Finset.sum_nonneg (fun i _ => (hCa0 i).le)
    have hAL0 : 0 ≤ AL := Finset.sum_nonneg (fun i _ => (hCpb0 i _ _).le)
    have hA10 : 0 ≤ A1 := Finset.sum_nonneg (fun i _ => (hCpb0 i _ _).le)
    have hAq0 : 0 ≤ Aq := Finset.sum_nonneg (fun i _ => (hCpb0 i _ _).le)
    have hmem : ∀ i, i ≤ j → i ∈ Finset.range (j + 1) := fun i hi =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    set M := 2 * ‖mu_star p‖ with hM
    set CZ := M * (2 ^ j * (Aa * (2 ^ j * (AL * A1)))) with hCZ
    have hCZ0 : 0 ≤ CZ := by positivity
    set C3 := 2 ^ j * (CZ * (2 ^ j * (CZ * CZ))) with hC3
    set Cd := 2 ^ j * (CZ * A1) with hCd
    set Cq := 2 ^ j * (Aa * Aq) with hCq
    have haI : ∀ i, i ≤ j → Ca i ≤ Aa := fun i hi =>
      Finset.single_le_sum (f := Ca) (fun i _ => (hCa0 i).le) (hmem i hi)
    have hLI : ∀ i, i ≤ j → Cpb i ((p + 1) / 2) hq1 ≤ AL := fun i hi =>
      Finset.single_le_sum (f := fun i => Cpb i ((p + 1) / 2) hq1) (fun i _ => (hCpb0 i _ _).le) (hmem i hi)
    have h1I : ∀ i, i ≤ j → Cpb i 1 one_pos ≤ A1 := fun i hi =>
      Finset.single_le_sum (f := fun i => Cpb i 1 one_pos) (fun i _ => (hCpb0 i _ _).le) (hmem i hi)
    have hqI : ∀ i, i ≤ j → Cpb i q hq ≤ Aq := fun i hi =>
      Finset.single_le_sum (f := fun i => Cpb i q hq) (fun i _ => (hCpb0 i _ _).le) (hmem i hi)
    have hM0 : 0 ≤ M := by rw [hM]; positivity
    have hC3n : 0 ≤ C3 := by rw [hC3]; positivity
    have hCdn : 0 ≤ Cd := by rw [hCd]; positivity
    have hCqn : 0 ≤ Cq := by rw [hCq]; positivity
    have hpos2 : 0 ≤ 2 ^ j * (AL * A1) := by positivity
    clear_value Aa AL A1 Aq M CZ C3 Cd Cq
    refine ⟨CZ + C3 + Cd + Cq + 1, by linarith, fun R hR ε hε μ hμ y hy => ?_⟩
    have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
    have hyy0 : y ≥ y₀ := le_trans (le_trans (le_max_right _ _) hR) hy
    have hR2 : 2 ≤ R := le_trans hR₁ hR1
    have hR0 : 0 < R := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hy0 : 0 < y := by linarith
    have hyR2 : y > R / 2 := by linarith
    have hμn : ‖μ‖ ≤ M := by have := norm_le_of_mem_closedBall hμ; rw [hM]; linarith
    obtain ⟨h1, h2, -, -⟩ := hbasic R hR1 ε hε μ hμ y hyR2
    obtain ⟨hlpos, -⟩ := c04_aux_lam_pos p ε μ y hy0 h1 h2
    -- smoothness of the factors at `y`
    have haC : ContDiffAt ℝ j (astar p) y := c04_aux_astar_contDiffAt p hplus hμs j y hy0
    have hlamC : ContDiffAt ℝ j (fam_lambda p ε μ) y :=
      (c04_aux_lambda_contDiffOn p ε μ j).contDiffAt (Ioi_mem_nhds hy0)
    have hLC : ∀ q' : ℝ, ContDiffAt ℝ j (fun t => ((fam_lambda p ε μ t ^ (-q') : ℝ) : ℂ)) y := fun q' =>
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (hlamC.rpow_const_of_ne hlpos.ne')
    have hPsiC : ContDiffAt ℝ j (fam_Psi p R ε μ) y :=
      (c04_aux_Psi_contDiffOn p R ε μ hR0 j).contDiffAt (Ioi_mem_nhds hy0)
    have hEC : ContDiffAt ℝ j (fun t => Complex.exp (Complex.I * ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ))) y :=
      Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hPsiC.sub contDiffAt_const)))
    -- bounds for the factors
    have hYp : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
    have ba : ∀ i, i ≤ j → ‖iteratedDeriv i (astar p) y‖ ≤ Aa * y ^ (0 + i * (1 / p)) := by
      intro i hi
      refine ((hCa i y hyy0).2.1).trans ?_
      apply mul_le_mul (haI i hi) (rpow_le_rpow_of_exponent_le hy1 ?_) (hYp _) hAa0
      have : (0 : ℝ) ≤ i * (1 / p) := by positivity
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have ba' : ∀ i, i ≤ j → ‖iteratedDeriv i (astar p) y‖ ≤ Aa * y ^ (0 + (i : ℝ) * (-1)) := by
      intro i hi
      refine ((hCa i y hyy0).2.1).trans ?_
      apply mul_le_mul (haI i hi) (le_of_eq (by ring_nf)) (hYp _) hAa0
    have bL : ∀ (q' : ℝ) (hq' : 0 < q') (A : ℝ),
        (∀ i, i ≤ j → Cpb i q' hq' ≤ A) → ∀ i, i ≤ j →
        ‖iteratedDeriv i (fun t => ((fam_lambda p ε μ t ^ (-q') : ℝ) : ℂ)) y‖ ≤
          A * y ^ (-q' / p + (i : ℝ) * (-1)) := by
      intro q' hq' A hA i hi
      rw [c04_aux_iteratedDeriv_ofReal _ y i ((hlamC.rpow_const_of_ne hlpos.ne').of_le
        (by exact_mod_cast hi)), Complex.norm_real, Real.norm_eq_abs]
      refine ((hCpb i q' hq' R hR1 ε hε μ hμ y hyR2).2.1).trans ?_
      exact mul_le_mul (hA i hi) (le_of_eq (by ring_nf)) (hYp _) (le_trans (hCpb0 i q' hq').le (hA i hi))
    have bL' : ∀ (q' : ℝ) (hq' : 0 < q') (A : ℝ),
        (∀ i, i ≤ j → Cpb i q' hq' ≤ A) → ∀ i, i ≤ j →
        ‖iteratedDeriv i (fun t => ((fam_lambda p ε μ t ^ (-q') : ℝ) : ℂ)) y‖ ≤
          A * y ^ (-q' / p + i * (1 / p)) := by
      intro q' hq' A hA i hi
      refine (bL q' hq' A hA i hi).trans (mul_le_mul_of_nonneg_left ?_ (le_trans (hCpb0 0 q' hq').le
        (hA 0 (Nat.zero_le _))))
      apply rpow_le_rpow_of_exponent_le hy1
      have : (0 : ℝ) ≤ i * (1 / p) := by positivity
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have hEeq : (fun t => Complex.exp (Complex.I * ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ))) =
        fun t => Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) *
          Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) := by
      funext t; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have bE : ∀ i, i ≤ j → ‖iteratedDeriv i (fun t => Complex.exp (Complex.I *
        ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ))) y‖ ≤ A1 * y ^ (0 + i * (1 / p)) := by
      intro i hi
      have hC' : ContDiffAt ℝ i (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) y :=
        Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hPsiC.of_le (by exact_mod_cast hi))))
      have hn1 : ‖Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ)))‖ = 1 := by
        rw [show -(Complex.I * ((π / 4 : ℝ) : ℂ)) = Complex.I * ((-(π / 4) : ℝ) : ℂ) by push_cast; ring]
        exact c04_aux_norm_exp_I _
      rw [hEeq, iteratedDeriv_const_mul _ hC', norm_mul, hn1, one_mul]
      refine ((hCpb i 1 one_pos R hR1 ε hε μ hμ y hyR2).2.2).trans ?_
      apply mul_le_mul (h1I i hi) (le_of_eq (by ring_nf)) (hYp _) hA10
    -- `Z = μ (a (Λ E))`
    have hZeq : fam_Z p R ε μ = fun t => μ * ((astar p * ((fun t => ((fam_lambda p ε μ t ^
        (-((p + 1) / 2)) : ℝ) : ℂ)) * (fun t => Complex.exp (Complex.I *
        ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ))))) t) := by
      funext t; simp only [fam_Z, Pi.mul_apply, show -(p + 1) / 2 = -((p + 1) / 2) by ring]; ring
    have hLE := c04_aux_leibniz_all _ _ y hy0 j (hLC ((p + 1) / 2)) hEC AL A1 (-((p + 1) / 2) / p) 0 (1 / p)
      hAL0 hA10 (bL' ((p + 1) / 2) hq1 AL hLI) bE
    have hLEC : ContDiffAt ℝ j ((fun t => ((fam_lambda p ε μ t ^ (-((p + 1) / 2)) : ℝ) : ℂ)) *
        (fun t => Complex.exp (Complex.I * ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ)))) y :=
      (hLC ((p + 1) / 2)).mul hEC
    have haLE := c04_aux_leibniz_all (astar p) _ y hy0 j haC hLEC Aa (2 ^ j * (AL * A1)) 0
      (-((p + 1) / 2) / p + 0) (1 / p) hAa0 hpos2 ba hLE
    obtain ⟨Pf, hPf⟩ : ∃ Pf : ℝ → ℂ, Pf = astar p * ((fun t => ((fam_lambda p ε μ t ^ (-((p + 1) / 2)) : ℝ) : ℂ)) *
        (fun t => Complex.exp (Complex.I * ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ)))) := ⟨_, rfl⟩
    have hprodC : ContDiffAt ℝ j Pf y := by rw [hPf]; exact haC.mul hLEC
    rw [← hPf] at haLE
    have hZeq' : fam_Z p R ε μ = fun t => μ * Pf t := by rw [hPf]; exact hZeq
    have hZC : ContDiffAt ℝ j (fam_Z p R ε μ) y := by
      rw [hZeq']; exact contDiffAt_const.mul hprodC
    have hZb : ∀ i, i ≤ j → ‖iteratedDeriv i (fam_Z p R ε μ) y‖ ≤ CZ * y ^ (-beta p + i / p) := by
      intro i hi
      rw [hZeq', iteratedDeriv_const_mul μ (hprodC.of_le (by exact_mod_cast hi)), norm_mul]
      have h := haLE i hi
      have e : (0 : ℝ) + (-((p + 1) / 2) / p + 0) + i * (1 / p) = -beta p + i / p := by
        rw [← hβq]; ring
      rw [e] at h
      calc ‖μ‖ * ‖iteratedDeriv i Pf y‖ ≤ M * (2 ^ j * (Aa * (2 ^ j * (AL * A1))) * y ^ (-beta p + i / p)) :=
            mul_le_mul hμn h (norm_nonneg _) hM0
        _ = CZ * y ^ (-beta p + i / p) := by rw [hCZ]; ring
    have hZb' : ∀ i, i ≤ j → ‖iteratedDeriv i (fam_Z p R ε μ) y‖ ≤ CZ * y ^ (-beta p + i * (1 / p)) :=
      fun i hi => by have := hZb i hi; rwa [show (i : ℝ) / p = i * (1 / p) by ring] at this
    -- cube
    have hZZ := c04_aux_leibniz_all (fam_Z p R ε μ) (fam_Z p R ε μ) y hy0 j hZC hZC CZ CZ
      (-beta p) (-beta p) (1 / p) hCZ0 hCZ0 hZb' hZb'
    have hZ3 := c04_aux_leibniz (fam_Z p R ε μ) (fam_Z p R ε μ * fam_Z p R ε μ) y hy0 j hZC
      (hZC.mul hZC) CZ (2 ^ j * (CZ * CZ)) (-beta p) (-beta p + -beta p) (1 / p) hZb' hZZ
    have e3 : (fun t => fam_Z p R ε μ t ^ 3) = fam_Z p R ε μ * (fam_Z p R ε μ * fam_Z p R ε μ) := by
      funext t; simp only [Pi.mul_apply]; ring
    -- division by `λ`
    have edv : (fun t => fam_Z p R ε μ t / (fam_lambda p ε μ t : ℂ)) =
        fam_Z p R ε μ * (fun t => ((fam_lambda p ε μ t ^ (-(1 : ℝ)) : ℝ) : ℂ)) := by
      funext t; simp only [Pi.mul_apply, rpow_neg_one, Complex.ofReal_inv, div_eq_mul_inv]
    have hZd := c04_aux_leibniz (fam_Z p R ε μ) _ y hy0 j hZC (hLC 1) CZ A1 (-beta p) (-1 / p) (1 / p)
      hZb' (bL' 1 one_pos A1 h1I)
    -- `a λ^{-q}`
    have haq := c04_aux_leibniz (astar p) (fun t => ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ)) y hy0 j
      haC (hLC q) Aa Aq 0 (-q / p) (-1) ba' (bL q hq Aq hqI)
    refine ⟨fun i hi => (hZb i hi).trans (mul_le_mul_of_nonneg_right (by linarith) (hYp _)),
      ?_, ?_, ?_⟩
    · rw [e3]
      refine hZ3.trans ?_
      rw [show -beta p + (-beta p + -beta p) + j * (1 / p) = -3 * beta p + j / p by ring]
      exact mul_le_mul_of_nonneg_right (by rw [hC3]; linarith) (hYp _)
    · rw [edv]
      refine hZd.trans ?_
      rw [show -beta p + -1 / p + j * (1 / p) = -beta p - 1 / p + j / p by ring]
      exact mul_le_mul_of_nonneg_right (by rw [hCd]; linarith) (hYp _)
    · refine haq.trans ?_
      rw [show (0 : ℝ) + -q / p + j * (-1) = -q / p - j by ring]
      exact mul_le_mul_of_nonneg_right (by rw [hCq]; linarith) (hYp _)
  obtain ⟨C, hC, hb⟩ := hpart1 0 1 one_pos
  have hβ0 : 0 < beta p - 1 := by linarith
  refine ⟨ε₁, hε₁, max R₁ y₀, hR₀, fun j q hq => ?_, C / (beta p - 1) + 1, by positivity,
    fun R hR ε hε μ hμ y hy => ?_⟩
  · obtain ⟨C', hC', hb'⟩ := hpart1 j q hq
    exact ⟨C', hC', fun R hR ε hε μ hμ y hy =>
      let h := hb' R hR ε hε μ hμ y hy
      ⟨h.1 j le_rfl, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
  have hR2 : 2 ≤ R := le_trans hR₁ hR1
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < y := by linarith
  have hbd : ∀ t ∈ Ioi y, ‖fam_Z p R ε μ t‖ ≤ C * t ^ (-beta p) := by
    intro t ht
    have := (hb R hR ε hε μ hμ t (le_trans hy (le_of_lt ht))).1 0 le_rfl
    simpa using this
  have hg : IntegrableOn (fun t => C * t ^ (-beta p)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hy0).const_mul C
  have hcont : ContinuousOn (fun t => ‖fam_Z p R ε μ t‖) (Ioi y) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hy0 ht
    obtain ⟨g1, g2, -, -⟩ := hbasic R hR1 ε hε μ hμ t (by linarith [mem_Ioi.mp ht])
    have := c04_aux_famZ_diff p R ε μ hp0 hR0 hplus hμs t ht0 (c04_aux_lam_pos p ε μ t ht0 g1 g2).1
    exact this.continuousAt.norm.continuousWithinAt
  have hint : IntegrableOn (fun t => ‖fam_Z p R ε μ t‖) (Ioi y) := by
    refine Integrable.mono' hg (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hbd t ht
  refine ⟨hint, ?_⟩
  calc ∫ t in Ioi y, ‖fam_Z p R ε μ t‖ ≤ ∫ t in Ioi y, C * t ^ (-beta p) :=
        setIntegral_mono_on hint hg measurableSet_Ioi hbd
    _ = C / (beta p - 1) * y ^ (1 - beta p) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hy0]
        rw [show -beta p + 1 = 1 - beta p by ring]
        have hne : (1 - beta p) ≠ 0 := by linarith
        have hne' : (beta p - 1) ≠ 0 := by linarith
        field_simp
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (by linarith) (rpow_pos_of_pos hy0 _).le

/-- Blueprint: lem:c04_lambda_psi_difference.  For `y ≥ R`:
`|∂^j(λ - λ₀)| ≤ C_j ε y^{1/p-p-1-j}` and `|∂^j(Ψ - Ψ₀)| ≤ C_j ε y^{1/p-p-j}`. -/
theorem c04_lambda_psi_difference (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ j : ℕ, ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        |iteratedDeriv j (fun t => fam_lambda p ε μ t - lambda0 p t) y| ≤
          C * ε * y ^ (1 / p - p - 1 - j) ∧
        |iteratedDeriv j (fun t => fam_Psi p R ε μ t - Psi0 p t) y| ≤
          C * ε * y ^ (1 / p - p - j) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : 0 < ‖mu_star p‖ := by linarith
  obtain ⟨⟨Cc, hCc, hcs⟩, -, -, -⟩ := c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / p - p - 1 := ⟨_, rfl⟩
  have hr1 : -1 < r := by
    have : p < 1 / p := by rw [lt_div_iff₀ hp0]; nlinarith
    linarith
  have h1p : 0 < 1 - p ^ 2 := by nlinarith
  set K : ℕ → ℝ := fun j => Cc * ((1 - p ^ 2) / p * |(descPochhammer ℝ j).eval r| +
    |(descPochhammer ℝ j).eval (-1)|) with hKdef
  have hK0 : ∀ j, 0 ≤ K j := fun j => by simp only [hKdef]; positivity
  -- the bound for `λ - λ₀`
  have hlam : ∀ j : ℕ, ∀ R ≥ (2 : ℝ), ∀ ε ∈ Icc (0 : ℝ) 1, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
      |iteratedDeriv j (fun t => fam_lambda p ε μ t - lambda0 p t) y| ≤ K j * ε * y ^ (r - j) := by
    intro j R hR ε hε μ hμ y hy
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    obtain ⟨-, -, -, hcl, hcp, -, -⟩ := hcs ε hε μ (by have := norm_le_of_mem_closedBall hμ; linarith)
    have hev : (fun t => fam_lambda p ε μ t - lambda0 p t) =ᶠ[𝓝 y]
        fun t => (c_power p ε * ((1 - p ^ 2) / p)) * t ^ r + c_log p ε μ * t ^ (-1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hy0] with t ht
      simp only [fam_lambda, lambda0, rpow_neg_one, hr]
      ring
    rw [hev.iteratedDeriv_eq, c04_aux_iter_two_rpow _ _ _ _ j y hy0]
    have hexp : y ^ ((-1 : ℝ) - j) ≤ y ^ (r - j) := rpow_le_rpow_of_exponent_le hy1 (by linarith)
    have hpos1 : 0 ≤ y ^ (r - (j : ℝ)) := (rpow_pos_of_pos hy0 _).le
    have hpos2 : 0 ≤ y ^ ((-1 : ℝ) - (j : ℝ)) := (rpow_pos_of_pos hy0 _).le
    have hq : 0 < (1 - p ^ 2) / p := by positivity
    have ha : |c_power p ε| * |(1 - p ^ 2) / p| ≤ Cc * ε * ((1 - p ^ 2) / p) := by
      rw [abs_of_pos hq]; exact mul_le_mul_of_nonneg_right hcp hq.le
    have hε0 := hε.1
    have hP1 := abs_nonneg ((descPochhammer ℝ j).eval r)
    have hP2 := abs_nonneg ((descPochhammer ℝ j).eval (-1))
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_of_nonneg hpos1, abs_of_nonneg hpos2]
    calc |c_power p ε| * |(1 - p ^ 2) / p| * |(descPochhammer ℝ j).eval r| * y ^ (r - j) +
          |c_log p ε μ| * |(descPochhammer ℝ j).eval (-1)| * y ^ ((-1 : ℝ) - j)
        ≤ (Cc * ε * ((1 - p ^ 2) / p)) * |(descPochhammer ℝ j).eval r| * y ^ (r - j) +
          (Cc * ε) * |(descPochhammer ℝ j).eval (-1)| * y ^ (r - j) := by
          gcongr
      _ = K j * ε * y ^ (r - j) := by simp only [hKdef]; ring
  -- derivative of `Ψ - Ψ₀`
  have hPsi0 : ∀ t > (0 : ℝ), HasDerivAt (Psi0 p) (lambda0 p t) t := by
    intro t ht
    have h := ((hasDerivAt_rpow_const (p := 1 + 1 / p) (Or.inl ht.ne')).const_mul (p / (p + 1)))
    have e : p / (p + 1) * ((1 + 1 / p) * t ^ (1 + 1 / p - 1)) = lambda0 p t := by
      rw [show 1 + 1 / p - 1 = 1 / p by ring]
      simp only [lambda0]
      field_simp
    show HasDerivAt (fun y => p / (p + 1) * y ^ (1 + 1 / p)) (lambda0 p t) t
    exact h.congr_deriv e
  refine ⟨1, ⟨one_pos, le_rfl⟩, 2, le_rfl, fun j => ?_⟩
  refine ⟨K j + K (j - 1) + K 0 / (r + 1) + 1, by
    have := hK0 j; have := hK0 (j - 1); have := hK0 0
    have : 0 ≤ K 0 / (r + 1) := div_nonneg (hK0 0) (by linarith)
    linarith, fun R hR ε hε μ hμ y hy => ?_⟩
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < y := by linarith
  have hε0 := hε.1
  have hpos : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
  have hεY : ∀ e : ℝ, 0 ≤ ε * y ^ e := fun e => mul_nonneg hε0 (hpos e)
  have hKr : 0 ≤ K 0 / (r + 1) := div_nonneg (hK0 0) (by linarith)
  constructor
  · refine (hlam j R hR ε hε μ hμ y hy).trans ?_
    rw [show r - (j : ℝ) = 1 / p - p - 1 - j by rw [hr]]
    have hle : K j ≤ K j + K (j - 1) + K 0 / (r + 1) + 1 := by have := hK0 (j - 1); linarith
    have h := mul_le_mul_of_nonneg_right hle (hεY (1 / p - p - 1 - j))
    simpa only [mul_assoc] using h
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- `Ψ - Ψ₀ = ∫_R^y (λ - λ₀)`
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      have hsub : uIcc R y ⊆ Ioi 0 := by
        intro t ht; rcases mem_uIcc.mp ht with h | h
        · exact lt_of_lt_of_le hR0 h.1
        · exact lt_of_lt_of_le hy0 h.1
      have hl0c : ContinuousOn (lambda0 p) (Ioi 0) := fun t ht =>
        (continuousAt_id.rpow_const (Or.inl (ne_of_gt ht))).continuousWithinAt
      have hI1 : IntervalIntegrable (fam_lambda p ε μ) volume R y :=
        ((c04_aux_lambda_contOn p ε μ).mono hsub).intervalIntegrable
      have hI2 : IntervalIntegrable (lambda0 p) volume R y := (hl0c.mono hsub).intervalIntegrable
      have hFTC : ∫ t in R..y, lambda0 p t = Psi0 p y - Psi0 p R :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hPsi0 t (hsub ht)) hI2
      have hdiff : fam_Psi p R ε μ y - Psi0 p y = ∫ t in R..y, (fam_lambda p ε μ t - lambda0 p t) := by
        rw [intervalIntegral.integral_sub hI1 hI2, hFTC]; unfold fam_Psi; ring
      rw [hdiff]
      have hb : ∀ t ∈ Ioc R y, ‖fam_lambda p ε μ t - lambda0 p t‖ ≤ K 0 * ε * t ^ r := by
        intro t ht
        have := hlam 0 R hR ε hε μ hμ t ht.1.le
        simpa using this
      have hgI : IntervalIntegrable (fun t => K 0 * ε * t ^ r) volume R y :=
        (intervalIntegral.intervalIntegrable_rpow' hr1).const_mul _
      have := intervalIntegral.norm_integral_le_of_norm_le (hy.le.trans' le_rfl |> fun _ => (by linarith : R ≤ y))
        (Filter.Eventually.of_forall (fun t ht => hb t ht)) hgI
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr1)]
      have hRr : 0 ≤ R ^ (r + 1) := (rpow_pos_of_pos hR0 _).le
      have e : r + 1 = 1 / p - p := by rw [hr]; ring
      rw [e]
      have hrp : 0 < 1 / p - p := by rw [← e]; linarith
      calc K 0 * ε * ((y ^ (1 / p - p) - R ^ (1 / p - p)) / (1 / p - p))
          ≤ K 0 * ε * (y ^ (1 / p - p) / (1 / p - p)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hK0 0) hε0)
            apply div_le_div_of_nonneg_right _ hrp.le
            have : 0 ≤ R ^ (1 / p - p) := (rpow_pos_of_pos hR0 _).le
            linarith
        _ = K 0 / (1 / p - p) * (ε * y ^ (1 / p - p)) := by ring
        _ ≤ (K 0 + K (0 - 1) + K 0 / (r + 1) + 1) * (ε * y ^ (1 / p - p)) := by
            apply mul_le_mul_of_nonneg_right _ (hεY _)
            rw [← e]; have := hK0 0; have := hK0 (0 - 1); linarith
        _ = _ := by rw [e]; ring
    · -- higher derivatives: reduce to `λ - λ₀`
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hev : deriv (fun t => fam_Psi p R ε μ t - Psi0 p t) =ᶠ[𝓝 y]
          fun t => fam_lambda p ε μ t - lambda0 p t := by
        filter_upwards [Ioi_mem_nhds hy0] with t ht
        exact ((c04_aux_Psi_hasDeriv p R ε μ hR0 t ht).sub (hPsi0 t ht)).deriv
      rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
      refine (hlam k R hR ε hε μ hμ y hy).trans ?_
      rw [show r - (k : ℝ) = 1 / p - p - ((k + 1 : ℕ) : ℝ) by rw [hr]; push_cast; ring]
      have hle : K k ≤ K (k + 1) + K (k + 1 - 1) + K 0 / (r + 1) + 1 := by
        simp only [Nat.add_sub_cancel]; have := hK0 (k + 1); linarith
      have h := mul_le_mul_of_nonneg_right hle (hεY (1 / p - p - ((k + 1 : ℕ) : ℝ)))
      simpa only [mul_assoc] using h

/-- `t`-derivatives of a jointly smooth function of `(s,t)` are jointly continuous. -/
theorem c04_aux_param_iter_eq {H : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U) (i : ℕ) :
    ∀ z ∈ U, iteratedDeriv i (fun τ => H (z.1, τ)) z.2 =
      iteratedFDeriv ℝ i H z (fun _ => ((0 : ℝ), (1 : ℝ))) := by
  induction i with
  | zero => intro z hz; simp
  | succ i ih =>
    intro z hz
    have hev : ∀ᶠ τ in 𝓝 z.2, (z.1, τ) ∈ U := by
      have hc : Continuous (fun τ : ℝ => (z.1, τ)) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv i (fun τ => H (z.1, τ)) =ᶠ[𝓝 z.2]
        fun τ => iteratedFDeriv ℝ i H (z.1, τ) (fun _ => ((0 : ℝ), (1 : ℝ))) := by
      filter_upwards [hev] with τ hτ using ih (z.1, τ) hτ
    rw [heq.deriv_eq]
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ i H) z := by
      have h1 := hH.differentiableOn_iteratedFDerivWithin (m := i)
        (by exact_mod_cast ENat.natCast_lt_top i) hU.uniqueDiffOn
      have h2 : DifferentiableAt ℝ (iteratedFDerivWithin ℝ i H U) z :=
        (h1 z hz).differentiableAt (hU.mem_nhds hz)
      exact h2.congr_of_eventuallyEq (by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact (iteratedFDerivWithin_of_isOpen i hU hw).symm)
    have hpath : HasDerivAt (fun τ : ℝ => (z.1, τ)) ((0 : ℝ), (1 : ℝ)) z.2 :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt z.2 hpath
    have happ := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => ℝ × ℝ) ℂ
      (fun _ => ((0 : ℝ), (1 : ℝ)))).hasFDerivAt.comp_hasDerivAt z.2 hcomp
    simp only [Function.comp_def] at happ
    refine happ.deriv.trans ?_
    rw [iteratedFDeriv_succ_apply_left]
    simp only [ContinuousMultilinearMap.apply_apply]
    rfl

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_param_iter_cont {H : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H U) (i : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => iteratedDeriv i (fun τ => H (z.1, τ)) z.2) U := by
  have hc : ContinuousOn (iteratedFDeriv ℝ i H) U := by
    have h1 := hH.continuousOn_iteratedFDerivWithin (m := i)
      (by exact_mod_cast le_top) hU.uniqueDiffOn
    exact h1.congr (fun w hw => (iteratedFDerivWithin_of_isOpen i hU hw).symm)
  have hc2 : ContinuousOn (fun z => iteratedFDeriv ℝ i H z (fun _ => ((0 : ℝ), (1 : ℝ)))) U :=
    (continuous_eval_const _).comp_continuousOn hc
  exact hc2.congr (fun z hz => c04_aux_param_iter_eq hU hH i z hz)


/-- Lipschitz bound for `t ↦ t^{-q}` on `[m,∞)`. -/
theorem c04_aux_rpow_neg_lip (q m a b : ℝ) (hq : 0 < q) (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |a ^ (-q) - b ^ (-q)| ≤ q * m ^ (-q - 1) * |a - b| := by
  have hd : ∀ x ∈ Ici m, HasDerivWithinAt (fun t : ℝ => t ^ (-q)) (-q * x ^ (-q - 1)) (Ici m) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hm hx
    exact (Real.hasDerivAt_rpow_const (Or.inl hx0.ne')).hasDerivWithinAt
  have hbd : ∀ x ∈ Ici m, ‖-q * x ^ (-q - 1)‖ ≤ q * m ^ (-q - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hm hx
    rw [norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq,
      abs_of_pos (rpow_pos_of_pos hx0 _)]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hm hx (by linarith)) hq.le
  have := (convex_Ici m).norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd (show b ∈ Ici m from hb)
    (show a ∈ Ici m from ha)
  simpa [Real.norm_eq_abs] using this

/-- `(y^{1/p}/2)^{-q-1} = 2^{q+1} y^{-(q+1)/p}`. -/
theorem c04_aux_half_pow (p q y : ℝ) (hy : 0 < y) :
    (y ^ (1 / p) / 2) ^ (-q - 1) = 2 ^ (q + 1) * y ^ (-(q + 1) / p) := by
  rw [div_rpow (rpow_nonneg hy.le _) (by norm_num), ← rpow_mul hy.le, show -q - 1 = -(q + 1) by ring,
    rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  congr 1; ring

/-- The core estimate: `|∂^k(λ^{-q} - λ₀^{-q})| ≤ C ε y^{-q/p-p-1-k}` for `y ≥ R`. -/
theorem c04_aux_lamq_diff (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (δ : ℝ) (hδ : 0 < δ)
    (hδμ : δ ≤ ‖mu_star p‖ / 2) :
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ (i : ℕ) (q : ℝ), 0 < q → ∃ C ≥ (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R, ∀ k, k ≤ i →
        |iteratedDeriv k (fun t => fam_lambda p ε μ t ^ (-q) - lambda0 p t ^ (-q)) y| ≤
          C * ε * y ^ (-q / p - p - 1 - k) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨ε₁, hε₁, R₁, hR₁, hbasic, hder, -, hzero⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hdiff⟩ := c04_lambda_psi_difference p hp hp1 δ hδ hδμ
  choose Cb hCb0 hCb using hder
  choose Cd hCd0 hCd using hdiff
  have hμmem : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), ?_⟩
  -- abbreviations
  set L : ℝ → ℂ → ℝ → ℝ := fun ε μ => fam_lambda p ε μ with hL
  -- smoothness facts
  have hLC : ∀ (n : ℕ) ε μ t, 0 < t → ContDiffAt ℝ n (L ε μ) t := fun n ε μ t ht =>
    (c04_aux_lambda_contDiffOn p ε μ n).contDiffAt (Ioi_mem_nhds ht)
  have hl0C : ∀ (n : ℕ) t, 0 < t → ContDiffAt ℝ n (lambda0 p) t := fun n t ht => by
    unfold lambda0; exact contDiffAt_rpow_const_of_ne ht.ne'
  -- positivity of `λ` on `(R/2,∞)`
  have hLpos : ∀ R ≥ max R₁ R₂, ∀ ε ∈ Icc (0 : ℝ) (min ε₁ ε₂), ∀ μ ∈ Bbar p δ, ∀ t > R / 2,
      t ^ (1 / p) / 2 ≤ L ε μ t := fun R hR ε hε μ hμ t ht =>
    (hbasic R (le_trans (le_max_left _ _) hR) ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩ μ hμ t ht).2.1
  intro i
  induction i with
  | zero =>
    intro q hq
    refine ⟨q * 2 ^ (q + 1) * Cd 0, by have := hCd0 0; positivity, ?_⟩
    intro R hR ε hε μ hμ y hy k hk
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    have hR2 : 2 ≤ R := le_trans hR₁ (le_trans (le_max_left _ _) hR)
    have hy0 : 0 < y := by linarith
    have hm : 0 < y ^ (1 / p) / 2 := by positivity
    have h1 := hLpos R hR ε hε μ hμ y (by linarith)
    have h2 : y ^ (1 / p) / 2 ≤ lambda0 p y := by unfold lambda0; linarith
    have hlip := c04_aux_rpow_neg_lip q _ _ _ hq hm h1 h2
    have hd := (hCd 0 R (le_trans (le_max_right _ _) hR) ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
      μ hμ y hy).1
    simp only [iteratedDeriv_zero] at hd ⊢
    rw [c04_aux_half_pow p q y hy0] at hlip
    calc |fam_lambda p ε μ y ^ (-q) - lambda0 p y ^ (-q)|
        ≤ q * (2 ^ (q + 1) * y ^ (-(q + 1) / p)) * (Cd 0 * ε * y ^ (1 / p - p - 1 - (0 : ℕ))) :=
          hlip.trans (mul_le_mul_of_nonneg_left hd (by positivity))
      _ = q * 2 ^ (q + 1) * Cd 0 * ε * (y ^ (-(q + 1) / p) * y ^ (1 / p - p - 1 - (0 : ℕ))) := by ring
      _ = _ := by
          rw [← rpow_add hy0]; congr 2; push_cast; field_simp; ring
  | succ i ih =>
    intro q hq
    obtain ⟨C1, hC10, hC1⟩ := ih (q + 1) (by linarith)
    obtain ⟨C0, hC00, hC0⟩ := ih q hq
    -- per-order constants summed
    obtain ⟨hAL0, hAL⟩ := c04_aux_sum_const (fun k => Cb (k + 1) 1 one_pos)
      (fun k => (hCb0 _ _ _).le) i
    obtain ⟨hAq0, hAq⟩ := c04_aux_sum_const (fun k => Cb k (q + 1) (by linarith))
      (fun k => (hCb0 _ _ _).le) i
    obtain ⟨hAd0, hAd⟩ := c04_aux_sum_const (fun k => Cd (k + 1)) (fun k => (hCd0 _).le) i
    set AL := ∑ k ∈ Finset.range (i + 1), Cb (k + 1) 1 one_pos
    set Aq := ∑ k ∈ Finset.range (i + 1), Cb k (q + 1) (by linarith)
    set Ad := ∑ k ∈ Finset.range (i + 1), Cd (k + 1)
    refine ⟨C0 + q * 2 ^ i * (C1 * AL + Aq * Ad), by positivity, ?_⟩
    intro R hR ε hε μ hμ y hy k hk
    rcases Nat.lt_or_ge k (i + 1) with hki | hki
    · refine (hC0 R hR ε hε μ hμ y hy k (Nat.lt_succ_iff.mp hki)).trans ?_
      have hR2 : 2 ≤ R := le_trans hR₁ (le_trans (le_max_left _ _) hR)
      have : 0 ≤ ε * y ^ (-q / p - p - 1 - k) := mul_nonneg hε.1 (rpow_pos_of_pos (by linarith) _).le
      have hnn : 0 ≤ q * 2 ^ i * (C1 * AL + Aq * Ad) := by positivity
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) this
    have hki' : k = i + 1 := le_antisymm hk hki
    subst hki'
    have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
    have hR2' : R ≥ R₂ := le_trans (le_max_right _ _) hR
    have hR2 : 2 ≤ R := le_trans hR₁ hR1
    have hR0 : 0 < R := by linarith
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
    have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
    -- the derivative identity on `(R/2,∞)`
    set G : ℝ → ℝ := fun t => -q * ((fam_lambda p ε μ t ^ (-(q + 1)) - lambda0 p t ^ (-(q + 1))) *
        deriv (fam_lambda p ε μ) t +
      lambda0 p t ^ (-(q + 1)) * deriv (fun s => fam_lambda p ε μ s - lambda0 p s) t) with hG
    have hderiv : deriv (fun t => fam_lambda p ε μ t ^ (-q) - lambda0 p t ^ (-q)) =ᶠ[𝓝 y] G := by
      filter_upwards [Ioi_mem_nhds (show R / 2 < y by linarith)] with t ht
      have ht0 : 0 < t := lt_trans (by linarith : (0:ℝ) < R / 2) ht
      have hLt : 0 < fam_lambda p ε μ t :=
        lt_of_lt_of_le (by positivity) (hLpos R hR ε hε μ hμ t ht)
      have hl0t : 0 < lambda0 p t := rpow_pos_of_pos ht0 _
      have dL := ((hLC 1 ε μ t ht0).differentiableAt (by norm_num)).hasDerivAt
      have dl0 := ((hl0C 1 t ht0).differentiableAt (by norm_num)).hasDerivAt
      have h := (dL.rpow_const (p := -q) (Or.inl hLt.ne')).sub (dl0.rpow_const (p := -q) (Or.inl hl0t.ne'))
      have h' : HasDerivAt (fun t => fam_lambda p ε μ t ^ (-q) - lambda0 p t ^ (-q)) _ t := h
      rw [h'.deriv, hG]
      simp only
      have hds : deriv (fun s => fam_lambda p ε μ s - lambda0 p s) t =
          deriv (L ε μ) t - deriv (lambda0 p) t := (dL.sub dl0).deriv
      rw [hds]
      rw [show -q - 1 = -(q + 1) by ring]
      ring
    rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq]
    -- smoothness of the pieces
    have hLy : 0 < fam_lambda p ε μ y := lt_of_lt_of_le (by positivity) (hLpos R hR ε hε μ hμ y
      (by linarith))
    have hDC : ContDiffAt ℝ i (fun t => fam_lambda p ε μ t ^ (-(q + 1)) - lambda0 p t ^ (-(q + 1))) y :=
      ((hLC i ε μ y hy0).rpow_const_of_ne hLy.ne').sub
        ((hl0C i y hy0).rpow_const_of_ne (rpow_pos_of_pos hy0 _).ne')
    have hdLC : ContDiffAt ℝ i (deriv (fam_lambda p ε μ)) y :=
      ((c04_aux_lambda_contDiffOn p ε μ (i + 1)).deriv_of_isOpen isOpen_Ioi
        (by push_cast; exact le_rfl)).contDiffAt (Ioi_mem_nhds hy0)
    have hl0qC : ContDiffAt ℝ i (fun t => lambda0 p t ^ (-(q + 1))) y :=
      (hl0C i y hy0).rpow_const_of_ne (rpow_pos_of_pos hy0 _).ne'
    have hdDC : ContDiffAt ℝ i (deriv (fun s => fam_lambda p ε μ s - lambda0 p s)) y := by
      have : ContDiffOn ℝ (i + 1 : ℕ) (fun s => fam_lambda p ε μ s - lambda0 p s) (Ioi 0) :=
        (c04_aux_lambda_contDiffOn p ε μ (i + 1)).sub fun t ht =>
          (hl0C (i + 1) t ht).contDiffWithinAt
      exact (this.deriv_of_isOpen isOpen_Ioi (by push_cast; exact le_rfl)).contDiffAt
        (Ioi_mem_nhds hy0)
    have e1 : G = fun t => -q * (((fun t => fam_lambda p ε μ t ^ (-(q + 1)) -
        lambda0 p t ^ (-(q + 1))) * deriv (fam_lambda p ε μ) +
        (fun t => lambda0 p t ^ (-(q + 1))) * deriv (fun s => fam_lambda p ε μ s - lambda0 p s)) t) :=
      rfl
    rw [e1, iteratedDeriv_const_mul (f := ((fun t => fam_lambda p ε μ t ^ (-(q + 1)) -
        lambda0 p t ^ (-(q + 1))) * deriv (fam_lambda p ε μ) +
        (fun t => lambda0 p t ^ (-(q + 1))) * deriv (fun s => fam_lambda p ε μ s - lambda0 p s)))
        _ ((hDC.mul hdLC).add (hl0qC.mul hdDC)),
      iteratedDeriv_add (f := (fun t => fam_lambda p ε μ t ^ (-(q + 1)) -
        lambda0 p t ^ (-(q + 1))) * deriv (fam_lambda p ε μ))
        (g := (fun t => lambda0 p t ^ (-(q + 1))) * deriv (fun s => fam_lambda p ε μ s - lambda0 p s))
        (hDC.mul hdLC) (hl0qC.mul hdDC)]
    -- Leibniz bounds
    have hY : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
    have b1 := c04_aux_leibniz _ _ y hy0 i hDC hdLC (C1 * ε) AL (-(q + 1) / p - p - 1) (1 / p - 1) (-1)
      (fun k hk => by
        rw [Real.norm_eq_abs]
        refine (hC1 R hR ε hε μ hμ y hy k hk).trans (le_of_eq ?_)
        congr 1; ring_nf)
      (fun k hk => by
        rw [Real.norm_eq_abs, ← iteratedDeriv_succ']
        refine ((hCb (k + 1) 1 one_pos R hR1 ε hε1 μ hμ y (by linarith)).1).trans ?_
        refine mul_le_mul (hAL k hk) (le_of_eq ?_) (hY _) hAL0
        congr 1; push_cast; ring)
    have b2 := c04_aux_leibniz _ _ y hy0 i hl0qC hdDC Aq (Ad * ε) (-(q + 1) / p) (1 / p - p - 2) (-1)
      (fun k hk => by
        rw [Real.norm_eq_abs]
        have h := (hCb k (q + 1) (by linarith) R hR1 0 ⟨le_rfl, hε₁.1.le⟩ (mu_star p) hμmem y
          (by linarith)).2.1
        have e : (fun t => fam_lambda p 0 (mu_star p) t ^ (-(q + 1))) =ᶠ[𝓝 y]
            fun t => lambda0 p t ^ (-(q + 1)) := by
          filter_upwards [Ioi_mem_nhds (show R / 2 < y by linarith)] with t ht
          rw [(hzero R hR1 (mu_star p) hμmem t ht).1]
        rw [e.iteratedDeriv_eq] at h
        refine h.trans (mul_le_mul (hAq k hk) (le_of_eq ?_) (hY _) hAq0)
        congr 1; ring)
      (fun k hk => by
        rw [Real.norm_eq_abs, ← iteratedDeriv_succ']
        refine ((hCd (k + 1) R hR2' ε hε2 μ hμ y hy).1).trans ?_
        rw [show Ad * ε * y ^ (1 / p - p - 2 + (k : ℝ) * (-1)) =
          Ad * (ε * y ^ (1 / p - p - 1 - ((k + 1 : ℕ) : ℝ))) by push_cast; ring_nf]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (hAd k hk) (mul_nonneg hε.1 (hY _)))
    rw [Real.norm_eq_abs] at b1 b2
    rw [abs_mul, abs_neg, abs_of_pos hq]
    have e2 : y ^ (-(q + 1) / p - p - 1 + (1 / p - 1) + (i : ℝ) * (-1)) =
        y ^ (-q / p - p - 1 - ((i + 1 : ℕ) : ℝ)) := by congr 1; push_cast; field_simp; ring
    have e3 : y ^ (-(q + 1) / p + (1 / p - p - 2) + (i : ℝ) * (-1)) =
        y ^ (-q / p - p - 1 - ((i + 1 : ℕ) : ℝ)) := by congr 1; push_cast; field_simp; ring
    rw [e2] at b1; rw [e3] at b2
    have hsum := (abs_add_le _ _).trans (add_le_add b1 b2)
    have hP : 0 ≤ ε * y ^ (-q / p - p - 1 - ((i + 1 : ℕ) : ℝ)) := mul_nonneg hε.1 (hY _)
    calc q * |iteratedDeriv i ((fun t => fam_lambda p ε μ t ^ (-(q + 1)) - lambda0 p t ^ (-(q + 1))) *
            deriv (fam_lambda p ε μ)) y + iteratedDeriv i ((fun t => lambda0 p t ^ (-(q + 1))) *
            deriv (fun s => fam_lambda p ε μ s - lambda0 p s)) y|
        ≤ q * (2 ^ i * (C1 * ε * AL) * y ^ (-q / p - p - 1 - ((i + 1 : ℕ) : ℝ)) +
            2 ^ i * (Aq * (Ad * ε)) * y ^ (-q / p - p - 1 - ((i + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum hq.le
      _ = q * 2 ^ i * (C1 * AL + Aq * Ad) * (ε * y ^ (-q / p - p - 1 - ((i + 1 : ℕ) : ℝ))) := by ring
      _ ≤ (C0 + q * 2 ^ i * (C1 * AL + Aq * Ad)) * (ε * y ^ (-q / p - p - 1 - ((i + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hP
      _ = _ := by ring

/-- Blueprint: lem:c04_reciprocal_amplitude_difference.  `F_q = a_*λ^{-q}`, `F_{q,0} = a_*λ₀^{-q}`
are smooth on `(R/2,∞)`, `|∂^j F_q| + |∂^j F_{q,0}| ≤ C y^{-q/p-j}` and
`|∂^j(F_q - F_{q,0})| ≤ C ε y^{-q/p-p-1-j}` for `y ≥ R`. -/
theorem c04_reciprocal_amplitude_difference (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ (j : ℕ) (q : ℝ), 0 < q → ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        ContDiffOn ℝ (⊤ : ℕ∞) (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ))
          (Ioi (R / 2)) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun t => astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) (Ioi (R / 2)) ∧
        ∀ y ≥ R,
          ‖iteratedDeriv j (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ)) y‖ +
              ‖iteratedDeriv j (fun t => astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) y‖ ≤
            C * y ^ (-q / p - j) ∧
          ‖iteratedDeriv j (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
              astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) y‖ ≤
            C * ε * y ^ (-q / p - p - 1 - j) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  have hμmem : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hbasic, -, -, hzero⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hdq⟩ := c04_aux_lamq_diff p hp hp1 δ hδ hδμ
  obtain ⟨ε₃, hε₃, R₃, hR₃, hZb, -⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨y₀, hy₀, -, hamp⟩ := c04_seed_amplitude p hp hp1
  choose Ca hCa0 hCa using hamp
  set ε₀ := min ε₁ (min ε₂ ε₃) with hε₀
  set R₀ := max (max R₁ R₂) (max R₃ y₀) with hR₀
  have hε0pos : 0 < ε₀ := lt_min hε₁.1 (lt_min hε₂.1 hε₃.1)
  have hε01 : ε₀ ≤ 1 := (min_le_left _ _).trans hε₁.2
  refine ⟨ε₀, ⟨hε0pos, hε01⟩, R₀, le_trans hR₁ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro j q hq
  obtain ⟨Cq, hCq0, hCq⟩ := hdq j q hq
  obtain ⟨CZ, hCZ0, hCZ⟩ := hZb j q hq
  obtain ⟨hAa0, hAa⟩ := c04_aux_sum_const Ca (fun k => (hCa0 k).le) j
  set Aa0 := ∑ k ∈ Finset.range (j + 1), Ca k
  refine ⟨2 * CZ + 2 ^ j * (Aa0 * Cq) + 1, by positivity, ?_⟩
  intro R hR ε hε μ hμ
  have hR1 : R ≥ R₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR2 : R ≥ R₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR3 : R ≥ R₃ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRy : R ≥ y₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hRtwo : 2 ≤ R := le_trans hR₁ hR1
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ :=
    ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε3 : ε ∈ Icc (0 : ℝ) ε₃ :=
    ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hε03 : (0 : ℝ) ∈ Icc (0 : ℝ) ε₃ := ⟨le_rfl, hε₃.1.le⟩
  -- smoothness
  have hsm : ∀ (L : ℝ → ℝ), (∀ n : ℕ, ∀ t > R / 2, ContDiffAt ℝ n L t ∧ 0 < L t) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun t => astar p t * ((L t ^ (-q) : ℝ) : ℂ)) (Ioi (R / 2)) := by
    intro L hL
    refine contDiffOn_infty.mpr fun n t ht => ?_
    have ht0 : 0 < t := lt_trans (by linarith : (0 : ℝ) < R / 2) ht
    obtain ⟨hLc, hLp⟩ := hL n t ht
    exact ((c04_aux_astar_contDiffAt p hplus hμs n t ht0).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp t (hLc.rpow_const_of_ne hLp.ne'))).contDiffWithinAt
  have hLpos : ∀ t > R / 2, 0 < fam_lambda p ε μ t := fun t ht =>
    lt_of_lt_of_le (by have : 0 < t := lt_trans (by linarith : (0 : ℝ) < R / 2) ht; positivity)
      (hbasic R hR1 ε hε1 μ hμ t ht).2.1
  have hsm1 := hsm (fam_lambda p ε μ) fun n t ht =>
    ⟨(c04_aux_lambda_contDiffOn p ε μ n).contDiffAt
      (Ioi_mem_nhds (lt_trans (by linarith : (0 : ℝ) < R / 2) ht)), hLpos t ht⟩
  have hsm0 := hsm (lambda0 p) fun n t ht =>
    have ht0 : 0 < t := lt_trans (by linarith : (0 : ℝ) < R / 2) ht
    ⟨by unfold lambda0; exact contDiffAt_rpow_const_of_ne ht0.ne', rpow_pos_of_pos ht0 _⟩
  refine ⟨hsm1, hsm0, fun y hy => ⟨?_, ?_⟩⟩
  · have hy0 : 0 < y := by linarith
    have h1 := (hCZ R hR3 ε hε3 μ hμ y hy).2.2.2
    have h2 := (hCZ R hR3 0 hε03 (mu_star p) hμmem y hy).2.2.2
    have e : (fun t => astar p t * ((fam_lambda p 0 (mu_star p) t ^ (-q) : ℝ) : ℂ)) =ᶠ[𝓝 y]
        fun t => astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds (show R / 2 < y by linarith)] with t ht
      rw [(hzero R hR1 (mu_star p) hμmem t ht).1]
    rw [e.iteratedDeriv_eq] at h2
    have hY : 0 ≤ y ^ (-q / p - j) := (rpow_pos_of_pos hy0 _).le
    have hc : 0 ≤ 2 ^ j * (Aa0 * Cq) + 1 := by positivity
    calc _ ≤ CZ * y ^ (-q / p - j) + CZ * y ^ (-q / p - j) := add_le_add h1 h2
      _ ≤ _ := by nlinarith [mul_nonneg hc hY]
  · have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have heq : (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
        astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) =
        astar p * fun t => (((fam_lambda p ε μ t ^ (-q) - lambda0 p t ^ (-q)) : ℝ) : ℂ) := by
      funext t; simp only [Pi.mul_apply]; push_cast; ring
    have hDC : ContDiffAt ℝ j (fun t => fam_lambda p ε μ t ^ (-q) - lambda0 p t ^ (-q)) y :=
      (((c04_aux_lambda_contDiffOn p ε μ j).contDiffAt (Ioi_mem_nhds hy0)).rpow_const_of_ne
        (hLpos y (by linarith)).ne').sub
        ((by unfold lambda0; exact contDiffAt_rpow_const_of_ne hy0.ne' :
          ContDiffAt ℝ j (lambda0 p) y).rpow_const_of_ne (rpow_pos_of_pos hy0 _).ne')
    rw [heq]
    have b := c04_aux_leibniz (astar p) (fun t => (((fam_lambda p ε μ t ^ (-q) -
        lambda0 p t ^ (-q)) : ℝ) : ℂ)) y hy0 j
      (c04_aux_astar_contDiffAt p hplus hμs j y hy0)
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y hDC) Aa0 (Cq * ε) 0 (-q / p - p - 1) (-1)
      (fun k hk => by
        refine ((hCa k y (le_trans hRy hy)).2.1).trans ?_
        refine mul_le_mul (hAa k hk) (le_of_eq ?_) (rpow_pos_of_pos hy0 _).le hAa0
        congr 1; ring)
      (fun k hk => by
        rw [c04_aux_iteratedDeriv_ofReal _ y k (hDC.of_le (by exact_mod_cast hk)), Complex.norm_real,
          Real.norm_eq_abs]
        refine (hCq R hR2 ε hε2 μ hμ y hy k hk).trans (le_of_eq ?_)
        congr 1; ring)
    have e : (0 : ℝ) + (-q / p - p - 1) + (j : ℝ) * (-1) = -q / p - p - 1 - j := by ring
    rw [e] at b
    refine b.trans ?_
    have hP : 0 ≤ ε * y ^ (-q / p - p - 1 - j) := mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le
    calc 2 ^ j * (Aa0 * (Cq * ε)) * y ^ (-q / p - p - 1 - j)
        = 2 ^ j * (Aa0 * Cq) * (ε * y ^ (-q / p - p - 1 - j)) := by ring
      _ ≤ (2 * CZ + 2 ^ j * (Aa0 * Cq) + 1) * (ε * y ^ (-q / p - p - 1 - j)) :=
          mul_le_mul_of_nonneg_right (by linarith) hP
      _ = _ := by ring



/-- A smooth function on an open set has differentiable iterated derivatives there. -/
theorem c04_aux_iter_hasDeriv {f : ℝ → ℂ} {V : Set ℝ} (hV : IsOpen V)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (m : ℕ) (x : ℝ) (hx : x ∈ V) :
    HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
  have h1 := hf.differentiableOn_iteratedDerivWithin (m := m)
    (by exact_mod_cast ENat.natCast_lt_top m) hV.uniqueDiffOn
  have h2 : DifferentiableAt ℝ (iteratedDeriv m f) x :=
    ((h1 x hx).differentiableAt (hV.mem_nhds hx)).congr_of_eventuallyEq (by
      filter_upwards [hV.mem_nhds hx] with w hw
      exact (iteratedDerivWithin_of_isOpen hV hw).symm)
  rw [iteratedDeriv_succ]
  exact h2.hasDerivAt

/-- Differentiation under `∫₀¹ ds` of a jointly smooth function, one step. -/
theorem c04_aux_param_hasDeriv {H : ℝ × ℝ → ℂ} {V : Set ℝ} (hV : IsOpen V)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (univ ×ˢ V)) (m : ℕ) (x₀ : ℝ) (hx₀ : x₀ ∈ V) :
    HasDerivAt (fun x => ∫ s in (0 : ℝ)..1, iteratedDeriv m (fun τ => H (s, τ)) x)
      (∫ s in (0 : ℝ)..1, iteratedDeriv (m + 1) (fun τ => H (s, τ)) x₀) x₀ := by
  have hU : IsOpen ((univ : Set ℝ) ×ˢ V) := isOpen_univ.prod hV
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV x₀ hx₀
  have hcb : Metric.closedBall x₀ (r / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x₀ (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKU : Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x₀ (r / 2) ⊆ (univ : Set ℝ) ×ˢ V :=
    prod_mono (subset_univ _) hcb
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (fun τ => H (z.1, τ)) z.2) ((univ : Set ℝ) ×ˢ V) :=
    fun k => c04_aux_param_iter_cont hU hH k
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((hcont (m + 1)).mono hKU)
  have hsec : ∀ k : ℕ, ∀ x ∈ V, Continuous (fun s : ℝ => iteratedDeriv k (fun τ => H (s, τ)) x) := by
    intro k x hx
    have hc : Continuous (fun s : ℝ => (s, x)) := by fun_prop
    exact (hcont k).comp_continuous hc (fun s => ⟨mem_univ _, hx⟩)
  have hslice : ∀ s : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (fun τ => H (s, τ)) V := by
    intro s
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => (s, τ)) := by fun_prop
    exact hH.comp hc.contDiffOn (fun τ hτ => ⟨mem_univ _, hτ⟩)
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun x s => iteratedDeriv m (fun τ => H (s, τ)) x)
    (F' := fun x s => iteratedDeriv (m + 1) (fun τ => H (s, τ)) x) (x₀ := x₀)
    (s := Metric.ball x₀ (r / 2)) (bound := fun _ => B)
    (Metric.ball_mem_nhds x₀ (by linarith))
    (by filter_upwards [hV.mem_nhds hx₀] with x hx
        exact (hsec m x hx).aestronglyMeasurable)
    ((hsec m x₀ hx₀).intervalIntegrable _ _)
    ((hsec (m + 1) x₀ hx₀).aestronglyMeasurable)
    (Eventually.of_forall fun t ht x hx => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
      exact hB (t, x) ⟨ht', Metric.ball_subset_closedBall hx⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ x hx =>
      c04_aux_iter_hasDeriv hV (hslice t) m x (hcb (Metric.ball_subset_closedBall hx)))
  exact this.2

/-- `∂_t^j ∫₀¹ H(s,t) ds = ∫₀¹ ∂_t^j H(s,t) ds` on `V`. -/
theorem c04_aux_param_iter {H : ℝ × ℝ → ℂ} {V : Set ℝ} (hV : IsOpen V)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (univ ×ˢ V)) (j : ℕ) (y : ℝ) (hy : y ∈ V) :
    iteratedDeriv j (fun t => ∫ s in (0 : ℝ)..1, H (s, t)) y =
      ∫ s in (0 : ℝ)..1, iteratedDeriv j (fun τ => H (s, τ)) y := by
  have key : ∀ j : ℕ, EqOn (iteratedDeriv j (fun t => ∫ s in (0 : ℝ)..1, H (s, t)))
      (fun x => ∫ s in (0 : ℝ)..1, iteratedDeriv j (fun τ => H (s, τ)) x) V := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun t => ∫ s in (0 : ℝ)..1, H (s, t)) =ᶠ[𝓝 x]
          fun x => ∫ s in (0 : ℝ)..1, iteratedDeriv j (fun τ => H (s, τ)) x := by
        filter_upwards [hV.mem_nhds hx] with w hw using ih hw
      rw [hev.deriv_eq]
      exact (c04_aux_param_hasDeriv hV hH j x hx).deriv
  exact key j hy

theorem c04_aux_expI_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem c04_aux_Psi0_contDiffOn (p : ℝ) (n : ℕ) : ContDiffOn ℝ n (Psi0 p) (Ioi 0) := fun t ht => by
  unfold Psi0
  exact (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne (ne_of_gt ht))).contDiffWithinAt

/-- Blueprint: lem:c04_phase_exponential_difference.  With `Ψ_s = Ψ₀ + s(Ψ - Ψ₀)`:
smoothness on `(R/2,∞)`, `e^{iΨ} - e^{iΨ₀} = i ∫₀¹ ΔΨ e^{iΨ_s} ds` (also after `∂^j`), and for
`y ≥ R`: `sup_s |∂^j e^{iΨ_s}| ≤ C y^{j/p}`, `|∂^j(e^{iΨ} - e^{iΨ₀})| ≤ C ε y^{1/p-p+j/p}`. -/
theorem c04_phase_exponential_difference (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ j : ℕ, ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        (∀ s ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ (⊤ : ℕ∞) (fun t => Complex.exp (Complex.I *
          ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) (Ioi (R / 2))) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
          Complex.exp (Complex.I * (Psi0 p t : ℂ))) (Ioi (R / 2)) ∧
        (∀ y > R / 2,
          iteratedDeriv j (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
            Complex.exp (Complex.I * (Psi0 p t : ℂ))) y =
          Complex.I * ∫ s in (0 : ℝ)..1, iteratedDeriv j (fun t =>
            ((fam_Psi p R ε μ t - Psi0 p t : ℝ) : ℂ) * Complex.exp (Complex.I *
              ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) y) ∧
        ∀ y ≥ R,
          (∀ s ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv j (fun t => Complex.exp (Complex.I *
            ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) y‖ ≤ C * y ^ ((j : ℝ) / p)) ∧
          ‖iteratedDeriv j (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
            Complex.exp (Complex.I * (Psi0 p t : ℂ))) y‖ ≤ C * ε * y ^ (1 / p - p + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμmem : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  obtain ⟨ε₁, hε₁, R₁, hR₁, -, hder, -, hzero⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hdiff⟩ := c04_lambda_psi_difference p hp hp1 δ hδ hδμ
  choose Cb hCb0 hCb using hder
  choose Cd hCd0 hCd using hdiff
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), ?_⟩
  -- smoothness of the interpolated phases
  have hgexp : ∀ n : ℕ, ContDiffOn ℝ n (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) univ :=
    fun n => (c04_aux_expI_smooth.of_le (by exact_mod_cast le_top)).contDiffOn
  have hPsC : ∀ (R ε : ℝ) (μ : ℂ) (s : ℝ), 0 < R → ∀ n : ℕ,
      ContDiffOn ℝ n (fun t => Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t)) (Ioi 0) :=
    fun R ε μ s hR n => (c04_aux_Psi0_contDiffOn p n).add (contDiffOn_const.mul
      ((c04_aux_Psi_contDiffOn p R ε μ hR n).sub (c04_aux_Psi0_contDiffOn p n)))
  have hEC : ∀ (R ε : ℝ) (μ : ℂ) (s : ℝ), 0 < R →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun t => Complex.exp (Complex.I *
        ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) (Ioi 0) :=
    fun R ε μ s hR => contDiffOn_infty.mpr fun n =>
      (hgexp n).comp (hPsC R ε μ s hR n) (mapsTo_univ _ _)
  -- uniform bounds for `∂^n e^{iΨ_s}`
  have hexpb : ∀ n : ℕ, ∃ C ≥ (0 : ℝ), ∀ R ≥ max R₁ R₂, ∀ ε ∈ Icc (0 : ℝ) (min ε₁ ε₂),
      ∀ μ ∈ Bbar p δ, ∀ y ≥ R, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv n (fun t => Complex.exp (Complex.I *
          ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) y‖ ≤ C * y ^ ((n : ℝ) / p) := by
    intro n
    obtain ⟨hS0, hS⟩ := c04_aux_sum_const (fun i => Cb i 1 one_pos) (fun i => (hCb0 _ _ _).le) n
    set K := 1 + ∑ i ∈ Finset.range (n + 1), Cb i 1 one_pos with hK
    have hK1 : 1 ≤ K := by linarith
    refine ⟨(n.factorial : ℝ) * K ^ n, by positivity, fun R hR ε hε μ hμ y hy s hs => ?_⟩
    have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
    have hR2 : 2 ≤ R := le_trans hR₁ hR1
    have hR0 : 0 < R := by linarith
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
    have hfun : (fun t => Complex.exp (Complex.I *
        ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) =
        (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ))) ∘
          (fun t => Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t)) := rfl
    rw [hfun]
    have h := c04_aux_fdb (fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)))
      (fun t => Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t))
      (Ioi 0) univ isOpen_Ioi isOpen_univ n (hgexp n) (hPsC R ε μ s hR0 n) (mapsTo_univ _ _) y hy0
      1 (K * y ^ (1 / p)) (fun i _ => le_of_eq (c04_aux_norm_iter_expI i _)) ?_
    · refine h.trans (le_of_eq ?_)
      rw [mul_one, mul_pow, ← rpow_natCast (y ^ (1 / p)), ← rpow_mul hy0.le]
      ring_nf
    · intro i hi1 hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hev : deriv (fun t => Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t)) =ᶠ[𝓝 y]
          fun t => (1 - s) * lambda0 p t + s * fam_lambda p ε μ t := by
        filter_upwards [Ioi_mem_nhds hy0] with t ht
        have h0 := c04_aux_Psi0_hasDeriv p hp0 t ht
        have h1 := c04_aux_Psi_hasDeriv p R ε μ hR0 t ht
        have hd : HasDerivAt (fun t => Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t)) _ t :=
          h0.add ((h1.sub h0).const_mul s)
        rw [hd.deriv]; ring
      rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
      have hl0C : ContDiffAt ℝ j (lambda0 p) y := by
        unfold lambda0; exact contDiffAt_rpow_const_of_ne hy0.ne'
      have hLC : ContDiffAt ℝ j (fam_lambda p ε μ) y :=
        (c04_aux_lambda_contDiffOn p ε μ j).contDiffAt (Ioi_mem_nhds hy0)
      show |iteratedDeriv j ((fun t => (1 - s) * lambda0 p t) + fun t => s * fam_lambda p ε μ t) y| ≤ _
      rw [iteratedDeriv_add (f := fun t => (1 - s) * lambda0 p t) (g := fun t => s * fam_lambda p ε μ t)
        (hl0C.const_smul (1 - s)) (hLC.const_smul s), iteratedDeriv_const_mul_field,
        iteratedDeriv_const_mul_field]
      have b1 := (hCb j 1 one_pos R hR1 ε hε1 μ hμ y (by linarith)).1
      have b0 := (hCb j 1 one_pos R hR1 0 ⟨le_rfl, hε₁.1.le⟩ (mu_star p) hμmem y (by linarith)).1
      have e : fam_lambda p 0 (mu_star p) =ᶠ[𝓝 y] lambda0 p := by
        filter_upwards [Ioi_mem_nhds (show R / 2 < y by linarith)] with t ht
        exact (hzero R hR1 (mu_star p) hμmem t ht).1
      rw [e.iteratedDeriv_eq] at b0
      have hCj : Cb j 1 one_pos ≤ K := by linarith [hS j (by omega)]
      have hKj : K ≤ K ^ (j + 1) := by
        calc K = K ^ 1 := (pow_one K).symm
          _ ≤ K ^ (j + 1) := pow_le_pow_right₀ hK1 (by omega)
      have hyexp : y ^ (1 / p - (j : ℝ)) ≤ (y ^ (1 / p)) ^ (j + 1) := by
        rw [← rpow_natCast (y ^ (1 / p)), ← rpow_mul hy0.le]
        apply rpow_le_rpow_of_exponent_le hy1
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have : 0 ≤ (j : ℝ) / p := by positivity
        push_cast
        have e : 1 / p * ((j : ℝ) + 1) = 1 / p + j / p := by ring
        rw [e]; linarith
      have hs0 : 0 ≤ 1 - s := by linarith [hs.2]
      have hY : 0 ≤ y ^ (1 / p - (j : ℝ)) := (rpow_pos_of_pos hy0 _).le
      calc |(1 - s) * iteratedDeriv j (lambda0 p) y + s * iteratedDeriv j (fam_lambda p ε μ) y|
          ≤ (1 - s) * |iteratedDeriv j (lambda0 p) y| + s * |iteratedDeriv j (fam_lambda p ε μ) y| := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg hs.1]
        _ ≤ (1 - s) * (Cb j 1 one_pos * y ^ (1 / p - (j : ℝ))) +
              s * (Cb j 1 one_pos * y ^ (1 / p - (j : ℝ))) :=
            add_le_add (mul_le_mul_of_nonneg_left b0 hs0) (mul_le_mul_of_nonneg_left b1 hs.1)
        _ = Cb j 1 one_pos * y ^ (1 / p - (j : ℝ)) := by ring
        _ ≤ K ^ (j + 1) * (y ^ (1 / p)) ^ (j + 1) :=
            mul_le_mul (hCj.trans hKj) hyexp hY (by positivity)
        _ = (K * y ^ (1 / p)) ^ (j + 1) := by rw [mul_pow]
  choose Ce hCe0 hCe using hexpb
  intro j
  obtain ⟨hCe0', hCeS⟩ := c04_aux_sum_const Ce hCe0 j
  obtain ⟨hCd0', hCdS⟩ := c04_aux_sum_const Cd (fun k => (hCd0 k).le) j
  set Aexp := ∑ k ∈ Finset.range (j + 1), Ce k
  set Adiff := ∑ k ∈ Finset.range (j + 1), Cd k
  refine ⟨Ce j + 2 ^ j * (Adiff * Aexp) + 1, by have := hCe0 j; positivity, ?_⟩
  intro R hR ε hε μ hμ
  have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
  have hR2' : R ≥ R₂ := le_trans (le_max_right _ _) hR
  have hR2 : 2 ≤ R := le_trans hR₁ hR1
  have hR0 : 0 < R := by linarith
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hsub : Ioi (R / 2) ⊆ Ioi 0 := Ioi_subset_Ioi (by linarith)
  -- smoothness on the open set
  have hE1 : (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) =
      fun t => Complex.exp (Complex.I * ((Psi0 p t + 1 * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ)) := by
    funext t; congr 3; ring
  have hE0 : (fun t => Complex.exp (Complex.I * (Psi0 p t : ℂ))) =
      fun t => Complex.exp (Complex.I * ((Psi0 p t + 0 * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ)) := by
    funext t; congr 3; ring
  have hdC : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
      Complex.exp (Complex.I * (Psi0 p t : ℂ))) (Ioi 0) := by
    refine ((hEC R ε μ 1 hR0).sub (hEC R ε μ 0 hR0)).congr fun t _ => ?_
    simp only [one_mul, zero_mul, add_zero, add_sub_cancel]
  -- the jointly smooth integrand
  set H : ℝ × ℝ → ℂ := fun z => ((fam_Psi p R ε μ z.2 - Psi0 p z.2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((Psi0 p z.2 + z.1 * (fam_Psi p R ε μ z.2 - Psi0 p z.2) : ℝ) : ℂ)) with hH
  have hHC : ContDiffOn ℝ (⊤ : ℕ∞) H ((univ : Set ℝ) ×ˢ Ioi (R / 2)) := by
    refine contDiffOn_infty.mpr fun n => ?_
    have hmaps : MapsTo (fun z : ℝ × ℝ => z.2) ((univ : Set ℝ) ×ˢ Ioi (R / 2)) (Ioi 0) :=
      fun z hz => hsub hz.2
    have hΨ : ContDiffOn ℝ n (fun z : ℝ × ℝ => fam_Psi p R ε μ z.2) ((univ : Set ℝ) ×ˢ Ioi (R / 2)) :=
      (c04_aux_Psi_contDiffOn p R ε μ hR0 n).comp contDiff_snd.contDiffOn hmaps
    have hΨ0 : ContDiffOn ℝ n (fun z : ℝ × ℝ => Psi0 p z.2) ((univ : Set ℝ) ×ˢ Ioi (R / 2)) :=
      (c04_aux_Psi0_contDiffOn p n).comp contDiff_snd.contDiffOn hmaps
    have hΔ := hΨ.sub hΨ0
    have hph : ContDiffOn ℝ n (fun z : ℝ × ℝ =>
        Psi0 p z.2 + z.1 * (fam_Psi p R ε μ z.2 - Psi0 p z.2)) ((univ : Set ℝ) ×ˢ Ioi (R / 2)) :=
      hΨ0.add (contDiff_fst.contDiffOn.mul hΔ)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hΔ).mul ((hgexp n).comp hph (mapsTo_univ _ _))
  -- the identity at order 0
  have hid : ∀ t > R / 2, Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
      Complex.exp (Complex.I * (Psi0 p t : ℂ)) = Complex.I * ∫ s in (0 : ℝ)..1, H (s, t) := by
    intro t _
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => Complex.exp (Complex.I *
        ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ)))
        (Complex.I * H (s, t)) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))
          (((fam_Psi p R ε μ t - Psi0 p t : ℝ)) : ℂ) s := by
        have := ((hasDerivAt_id s).mul_const (fam_Psi p R ε μ t - Psi0 p t)).const_add (Psi0 p t)
        simpa using this.ofReal_comp
      have := (h1.const_mul Complex.I).cexp
      convert this using 1
      simp only [hH]; ring
    have hc : Continuous (fun s : ℝ => Complex.I * H (s, t)) := by simp only [hH]; fun_prop
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hc.intervalIntegrable _ _)]
    congr 3 <;> push_cast <;> ring
  have hiter : ∀ y > R / 2,
      iteratedDeriv j (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
        Complex.exp (Complex.I * (Psi0 p t : ℂ))) y =
      Complex.I * ∫ s in (0 : ℝ)..1, iteratedDeriv j (fun t =>
        ((fam_Psi p R ε μ t - Psi0 p t : ℝ) : ℂ) * Complex.exp (Complex.I *
          ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) y := by
    intro y hy
    have hev : (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
        Complex.exp (Complex.I * (Psi0 p t : ℂ))) =ᶠ[𝓝 y]
        fun t => Complex.I * ∫ s in (0 : ℝ)..1, H (s, t) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht using hid t ht
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const_mul_field,
      c04_aux_param_iter isOpen_Ioi hHC j y hy]
  refine ⟨fun s _ => (hEC R ε μ s hR0).mono hsub, hdC.mono hsub, hiter, fun y hy => ⟨?_, ?_⟩⟩
  · intro s hs
    refine (hCe j R hR ε hε μ hμ y hy s hs).trans ?_
    have : 0 ≤ y ^ ((j : ℝ) / p) := (rpow_pos_of_pos (by linarith) _).le
    have : 0 ≤ 2 ^ j * (Adiff * Aexp) + 1 := by positivity
    nlinarith
  · have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    rw [hiter y (by linarith), norm_mul, Complex.norm_I, one_mul]
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ‖iteratedDeriv j (fun t =>
        ((fam_Psi p R ε μ t - Psi0 p t : ℝ) : ℂ) * Complex.exp (Complex.I *
          ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) y‖ ≤
        2 ^ j * ((Adiff * ε) * Aexp) * y ^ (1 / p - p + 0 + j * (1 / p)) := by
      intro s hs
      rw [uIoc_of_le zero_le_one] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
      have hΔC : ContDiffAt ℝ j (fun t => fam_Psi p R ε μ t - Psi0 p t) y :=
        (((c04_aux_Psi_contDiffOn p R ε μ hR0 j).sub (c04_aux_Psi0_contDiffOn p j)).contDiffAt
          (Ioi_mem_nhds hy0))
      have hEsC : ContDiffAt ℝ j (fun t => Complex.exp (Complex.I *
          ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ))) y :=
        ((hEC R ε μ s hR0).contDiffAt (Ioi_mem_nhds hy0)).of_le (by exact_mod_cast le_top)
      exact c04_aux_leibniz (fun t => ((fam_Psi p R ε μ t - Psi0 p t : ℝ) : ℂ))
        (fun t => Complex.exp (Complex.I * ((Psi0 p t + s * (fam_Psi p R ε μ t - Psi0 p t) : ℝ) : ℂ)))
        y hy0 j (Complex.ofRealCLM.contDiff.contDiffAt.comp y hΔC) hEsC
        (Adiff * ε) Aexp (1 / p - p) 0 (1 / p)
        (fun k hk => by
          rw [c04_aux_iteratedDeriv_ofReal _ y k (hΔC.of_le (by exact_mod_cast hk)), Complex.norm_real,
            Real.norm_eq_abs]
          refine ((hCd k R hR2' ε hε2 μ hμ y hy).2).trans ?_
          have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have : (0 : ℝ) ≤ k * (1 / p) := by positivity
          calc Cd k * ε * y ^ (1 / p - p - k) ≤ Adiff * ε * y ^ (1 / p - p + k * (1 / p)) :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hCdS k hk) hε.1)
                  (rpow_le_rpow_of_exponent_le hy1 (by linarith)) (rpow_pos_of_pos hy0 _).le
                  (mul_nonneg hCd0' hε.1))
        (fun k hk => by
          refine (hCe k R hR ε hε μ hμ y hy s hs').trans ?_
          refine mul_le_mul (hCeS k hk) (le_of_eq ?_) (rpow_pos_of_pos hy0 _).le hCe0'
          congr 1; ring)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans ?_
    rw [show (1 : ℝ) - 0 = 1 by ring, abs_one, mul_one]
    have e : (1 / p - p + 0 + (j : ℝ) * (1 / p)) = 1 / p - p + j / p := by ring
    rw [e]
    have hP : 0 ≤ ε * y ^ (1 / p - p + j / p) := mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le
    calc 2 ^ j * ((Adiff * ε) * Aexp) * y ^ (1 / p - p + j / p)
        = 2 ^ j * (Adiff * Aexp) * (ε * y ^ (1 / p - p + j / p)) := by ring
      _ ≤ (Ce j + 2 ^ j * (Adiff * Aexp) + 1) * (ε * y ^ (1 / p - p + j / p)) :=
          mul_le_mul_of_nonneg_right (by linarith [hCe0 j]) hP
      _ = _ := by ring

/-- Blueprint: lem:c04_Z_difference_products.  `B_q = μ(F_q - F_{q,0})e^{iΨ}`,
`P_q = μ F_{q,0}(e^{iΨ} - e^{iΨ₀})` are smooth on `(R/2,∞)`, `D_q = B_q + P_q`,
`Z - (μ/μ_*)Z₀ = e^{-iπ/4} D_{(p+1)/2}` on `(R/2,∞)`, and for `y ≥ R`:
`|∂^j B_q| ≤ C ε y^{-q/p-p-1+j/p}`, `|∂^j P_q| ≤ C ε y^{1/p-p-q/p+j/p}`. -/
theorem c04_Z_difference_products (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ (j : ℕ) (q : ℝ), 0 < q → ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        ContDiffOn ℝ (⊤ : ℕ∞) (fun t => μ * (astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
          astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) (Ioi (R / 2)) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (fun t => μ * (astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
          (Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
            Complex.exp (Complex.I * (Psi0 p t : ℂ)))) (Ioi (R / 2)) ∧
        (∀ y, c04_Dq p R ε μ q y =
          μ * (astar p y * ((fam_lambda p ε μ y ^ (-q) : ℝ) : ℂ) -
            astar p y * ((lambda0 p y ^ (-q) : ℝ) : ℂ)) *
              Complex.exp (Complex.I * (fam_Psi p R ε μ y : ℂ)) +
          μ * (astar p y * ((lambda0 p y ^ (-q) : ℝ) : ℂ)) *
            (Complex.exp (Complex.I * (fam_Psi p R ε μ y : ℂ)) -
              Complex.exp (Complex.I * (Psi0 p y : ℂ)))) ∧
        (∀ y > R / 2, fam_Z p R ε μ y - μ / mu_star p * fam_Z0 p R y =
          Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) * c04_Dq p R ε μ ((p + 1) / 2) y) ∧
        ∀ y ≥ R,
          ‖iteratedDeriv j (fun t => μ * (astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
            astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
              Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) y‖ ≤
            C * ε * y ^ (-q / p - p - 1 + j / p) ∧
          ‖iteratedDeriv j (fun t => μ * (astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
            (Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
              Complex.exp (Complex.I * (Psi0 p t : ℂ)))) y‖ ≤
            C * ε * y ^ (1 / p - p - q / p + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨εa, hεa, Ra, hRa, hrec⟩ := c04_reciprocal_amplitude_difference p hp hp1 δ hδ hδμ
  obtain ⟨εb, hεb, Rb, hRb, hexp⟩ := c04_phase_exponential_difference p hp hp1 δ hδ hδμ
  obtain ⟨ε₁, hε₁, R₁, hR₁, -, hder, -, hzero⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  set ε₀ := min εa (min εb ε₁)
  set R₀ := max Ra (max Rb R₁)
  have hε0 : 0 < ε₀ := lt_min hεa.1 (lt_min hεb.1 hε₁.1)
  refine ⟨ε₀, ⟨hε0, (min_le_left _ _).trans hεa.2⟩, R₀, le_trans hRa (le_max_left _ _), ?_⟩
  intro j q hq
  choose Ca hCa0 hCa using fun k : ℕ => hrec k q hq
  choose Cx hCx0 hCx using fun k : ℕ => hexp k
  choose Cb hCb0 hCb using fun k : ℕ => hder k 1 one_pos
  obtain ⟨hA0, hA⟩ := c04_aux_sum_const Ca (fun k => (hCa0 k).le) j
  obtain ⟨hX0, hX⟩ := c04_aux_sum_const Cx (fun k => (hCx0 k).le) j
  obtain ⟨hB0, hB⟩ := c04_aux_sum_const Cb (fun k => (hCb0 k).le) j
  set A := ∑ k ∈ Finset.range (j + 1), Ca k
  set X := ∑ k ∈ Finset.range (j + 1), Cx k
  set B := ∑ k ∈ Finset.range (j + 1), Cb k
  set M := ‖mu_star p‖ + δ
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M * 2 ^ j * (A * B + A * X) + 1, by positivity, ?_⟩
  intro R hR ε hε μ hμ
  have hRa' : R ≥ Ra := le_trans (le_max_left _ _) hR
  have hRb' : R ≥ Rb := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hR
  have hR1' : R ≥ R₁ := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hR
  have hR2 : 2 ≤ R := le_trans hRa hRa'
  have hR0 : 0 < R := by linarith
  have hεa' : ε ∈ Icc (0 : ℝ) εa := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεb' : ε ∈ Icc (0 : ℝ) εb :=
    ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε1' : ε ∈ Icc (0 : ℝ) ε₁ :=
    ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hμn : ‖μ‖ ≤ M := by
    have := norm_le_of_mem_closedBall hμ; linarith
  obtain ⟨hF1, hF0, -⟩ := hCa j R hRa' ε hεa' μ hμ
  obtain ⟨-, hdC, -, -⟩ := hCx j R hRb' ε hεb' μ hμ
  have hEC : ContDiffOn ℝ (⊤ : ℕ∞) (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)))
      (Ioi (R / 2)) := by
    refine contDiffOn_infty.mpr fun n => ?_
    exact ((c04_aux_expI_smooth.of_le (by exact_mod_cast le_top)).contDiffOn.comp
      (c04_aux_Psi_contDiffOn p R ε μ hR0 n) (mapsTo_univ _ _)).mono (Ioi_subset_Ioi (by linarith))
  refine ⟨?_, ?_, fun y => ?_, fun y hy => ?_, fun y hy => ⟨?_, ?_⟩⟩
  · have := (contDiffOn_const (c := μ)).mul ((hF1.sub hF0).mul hEC)
    refine this.congr fun t _ => ?_
    ring
  · have := (contDiffOn_const (c := μ)).mul (hF0.mul hdC)
    refine this.congr fun t _ => ?_
    ring
  · unfold c04_Dq; ring
  · have hy0 : 0 < y := lt_trans (by linarith : (0 : ℝ) < R / 2) hy
    obtain ⟨hl, hΨ, -, -⟩ := hzero R hR1' (mu_star p) (Metric.mem_closedBall_self hδ.le) y hy
    unfold fam_Z0 fam_Z c04_Dq
    rw [hl, hΨ, show -(p + 1) / 2 = -((p + 1) / 2) by ring]
    have e1 : ∀ x : ℝ, Complex.exp (Complex.I * ((x - π / 4 : ℝ) : ℂ)) =
        Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) * Complex.exp (Complex.I * (x : ℂ)) := by
      intro x; rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1, e1]
    field_simp
  · have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hfe : (fun t => μ * (astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
        astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) =
        fun t => μ * ((fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
          astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
          fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) t := by
      funext t; simp only [Pi.mul_apply]; ring
    rw [hfe, iteratedDeriv_const_mul_field, norm_mul]
    have hyR : y ∈ Ioi (R / 2) := show R / 2 < y by linarith
    have b := c04_aux_leibniz (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
          astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ))
        (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) y hy0 j
        (((hF1.sub hF0).contDiffAt (Ioi_mem_nhds hyR)).of_le (by exact_mod_cast le_top))
        ((hEC.contDiffAt (Ioi_mem_nhds hyR)).of_le (by exact_mod_cast le_top))
        (A * ε) B (-q / p - p - 1) 0 (1 / p)
        (fun k hk => by
          refine (((hCa k R hRa' ε hεa' μ hμ).2.2 y hy).2).trans ?_
          have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have : (0 : ℝ) ≤ k * (1 / p) := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hA k hk) hε.1)
            (rpow_le_rpow_of_exponent_le hy1 (by linarith)) (rpow_pos_of_pos hy0 _).le
            (mul_nonneg hA0 hε.1))
        (fun k hk => by
          refine ((hCb k R hR1' ε hε1' μ hμ y hyR).2.2).trans ?_
          refine mul_le_mul (hB k hk) (le_of_eq ?_) (rpow_pos_of_pos hy0 _).le hB0
          congr 1; ring)
    have e : -q / p - p - 1 + 0 + (j : ℝ) * (1 / p) = -q / p - p - 1 + j / p := by ring
    rw [e] at b
    have hP : 0 ≤ ε * y ^ (-q / p - p - 1 + j / p) := mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le
    calc ‖μ‖ * ‖iteratedDeriv j ((fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
          astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
          fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) y‖
        ≤ M * (2 ^ j * (A * ε * B) * y ^ (-q / p - p - 1 + j / p)) :=
          mul_le_mul hμn b (norm_nonneg _) hM0
      _ = M * 2 ^ j * (A * B) * (ε * y ^ (-q / p - p - 1 + j / p)) := by ring
      _ ≤ (M * 2 ^ j * (A * B + A * X) + 1) * (ε * y ^ (-q / p - p - 1 + j / p)) := by
          apply mul_le_mul_of_nonneg_right _ hP
          have : 0 ≤ M * 2 ^ j * (A * X) := by positivity
          nlinarith
      _ = _ := by ring
  · have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hfe : (fun t => μ * (astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
          Complex.exp (Complex.I * (Psi0 p t : ℂ)))) =
        fun t => μ * ((fun t => astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
          fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
          Complex.exp (Complex.I * (Psi0 p t : ℂ))) t := by
      funext t; simp only [Pi.mul_apply]; ring
    rw [hfe, iteratedDeriv_const_mul_field, norm_mul]
    have hyR : y ∈ Ioi (R / 2) := show R / 2 < y by linarith
    have b := c04_aux_leibniz (fun t => astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ))
        (fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
          Complex.exp (Complex.I * (Psi0 p t : ℂ))) y hy0 j
        ((hF0.contDiffAt (Ioi_mem_nhds hyR)).of_le (by exact_mod_cast le_top))
        ((hdC.contDiffAt (Ioi_mem_nhds hyR)).of_le (by exact_mod_cast le_top))
        A (X * ε) (-q / p) (1 / p - p) (1 / p)
        (fun k hk => by
          have h := ((hCa k R hRa' ε hεa' μ hμ).2.2 y hy).1
          have h' : ‖iteratedDeriv k (fun t => astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) y‖ ≤
              Ca k * y ^ (-q / p - k) := by linarith [norm_nonneg (iteratedDeriv k
                (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ)) y)]
          refine h'.trans ?_
          have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have : (0 : ℝ) ≤ k * (1 / p) := by positivity
          exact mul_le_mul (hA k hk) (rpow_le_rpow_of_exponent_le hy1 (by linarith))
            (rpow_pos_of_pos hy0 _).le hA0)
        (fun k hk => by
          refine (((hCx k R hRb' ε hεb' μ hμ).2.2.2 y hy).2).trans ?_
          rw [show X * ε * y ^ (1 / p - p + (k : ℝ) * (1 / p)) =
            X * (ε * y ^ (1 / p - p + k / p)) by ring_nf, mul_assoc]
          exact mul_le_mul_of_nonneg_right (hX k hk) (mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le))
    have e : -q / p + (1 / p - p) + (j : ℝ) * (1 / p) = 1 / p - p - q / p + j / p := by ring
    rw [e] at b
    have hP : 0 ≤ ε * y ^ (1 / p - p - q / p + j / p) := mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le
    calc _ ≤ M * (2 ^ j * (A * (X * ε)) * y ^ (1 / p - p - q / p + j / p)) :=
          mul_le_mul hμn b (norm_nonneg _) hM0
      _ = M * 2 ^ j * (A * X) * (ε * y ^ (1 / p - p - q / p + j / p)) := by ring
      _ ≤ (M * 2 ^ j * (A * B + A * X) + 1) * (ε * y ^ (1 / p - p - q / p + j / p)) := by
          apply mul_le_mul_of_nonneg_right _ hP
          have : 0 ≤ M * 2 ^ j * (A * B) := by positivity
          nlinarith
      _ = _ := by ring

/-- Blueprint: lem:c04_Z_difference.  `|∂^j D_q| ≤ C ε y^{1/p-p-q/p+j/p}`,
`|∂^j ∂[a_*λ^{-q} - a_*λ₀^{-q}]| ≤ C ε y^{-q/p-p-2-j}`, and
`|∂^j(Z - (μ/μ_*)Z₀)| ≤ C ε y^{1/p-p-β+j/p}`, for `y ≥ R`. -/
theorem c04_Z_difference (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ (j : ℕ) (q : ℝ), 0 < q → ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        ‖iteratedDeriv j (c04_Dq p R ε μ q) y‖ ≤ C * ε * y ^ (1 / p - p - q / p + j / p) ∧
        ‖iteratedDeriv j (deriv (fun t => astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
            astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ))) y‖ ≤ C * ε * y ^ (-q / p - p - 2 - j) ∧
        ‖iteratedDeriv j (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) y‖ ≤
          C * ε * y ^ (1 / p - p - beta p + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  obtain ⟨εa, hεa, Ra, hRa, hrec⟩ := c04_reciprocal_amplitude_difference p hp hp1 δ hδ hδμ
  obtain ⟨εc, hεc, Rc, hRc, hprod⟩ := c04_Z_difference_products p hp hp1 δ hδ hδμ
  refine ⟨min εa εc, ⟨lt_min hεa.1 hεc.1, (min_le_left _ _).trans hεa.2⟩, max Ra Rc,
    le_trans hRa (le_max_left _ _), ?_⟩
  -- the bound for `D_q`, uniform for each `(j,q)`
  have hD : ∀ (j : ℕ) (q : ℝ), 0 < q → ∃ C > (0 : ℝ), ∀ R ≥ max Ra Rc,
      ∀ ε ∈ Icc (0 : ℝ) (min εa εc), ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        ‖iteratedDeriv j (c04_Dq p R ε μ q) y‖ ≤ C * ε * y ^ (1 / p - p - q / p + j / p) := by
    intro j q hq
    obtain ⟨C, hC, h⟩ := hprod j q hq
    refine ⟨2 * C, by positivity, fun R hR ε hε μ hμ y hy => ?_⟩
    have hRc' : R ≥ Rc := le_trans (le_max_right _ _) hR
    have hR2 : 2 ≤ R := le_trans hRc hRc'
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hεc' : ε ∈ Icc (0 : ℝ) εc := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
    obtain ⟨hBC, hPC, hDeq, -, hb⟩ := h R hRc' ε hεc' μ hμ
    have hyR : y ∈ Ioi (R / 2) := show R / 2 < y by linarith
    rw [show c04_Dq p R ε μ q = (fun t => μ * (astar p t * ((fam_lambda p ε μ t ^ (-q) : ℝ) : ℂ) -
          astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) +
        (fun t => μ * (astar p t * ((lambda0 p t ^ (-q) : ℝ) : ℂ)) *
          (Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) -
            Complex.exp (Complex.I * (Psi0 p t : ℂ)))) from funext hDeq,
      iteratedDeriv_add ((hBC.contDiffAt (Ioi_mem_nhds hyR)).of_le (by exact_mod_cast le_top))
        ((hPC.contDiffAt (Ioi_mem_nhds hyR)).of_le (by exact_mod_cast le_top))]
    obtain ⟨b1, b2⟩ := hb y hy
    have hexp : y ^ (-q / p - p - 1 + j / p) ≤ y ^ (1 / p - p - q / p + j / p) :=
      rpow_le_rpow_of_exponent_le hy1 (by
        have : 0 < 1 / p := by positivity
        have e : (1 / p - p - q / p + j / p) - (-q / p - p - 1 + j / p) = 1 / p + 1 := by ring
        linarith)
    have hP : 0 ≤ C * ε := mul_nonneg hC.le hε.1
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ C * ε * y ^ (-q / p - p - 1 + j / p) + C * ε * y ^ (1 / p - p - q / p + j / p) :=
          add_le_add b1 b2
      _ ≤ C * ε * y ^ (1 / p - p - q / p + j / p) + C * ε * y ^ (1 / p - p - q / p + j / p) :=
          add_le_add (mul_le_mul_of_nonneg_left hexp hP) le_rfl
      _ = _ := by ring
  have hβ : (p + 1) / 2 / p = beta p := by unfold beta; field_simp
  intro j q hq
  obtain ⟨C1, hC1, h1⟩ := hD j q hq
  obtain ⟨C2, hC2, h2⟩ := hrec (j + 1) q hq
  obtain ⟨C3, hC3, h3⟩ := hD j ((p + 1) / 2) (by positivity)
  refine ⟨C1 + C2 + C3, by positivity, fun R hR ε hε μ hμ y hy => ⟨?_, ?_, ?_⟩⟩
  · have hy0 : 0 < y := by linarith [le_trans hRa (le_trans (le_max_left _ _) hR)]
    have hP : 0 ≤ ε * y ^ (1 / p - p - q / p + j / p) := mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le
    refine (h1 R hR ε hε μ hμ y hy).trans ?_
    have : C1 ≤ C1 + C2 + C3 := by linarith
    calc C1 * ε * y ^ (1 / p - p - q / p + j / p) = C1 * (ε * y ^ (1 / p - p - q / p + j / p)) := by
          ring
      _ ≤ (C1 + C2 + C3) * (ε * y ^ (1 / p - p - q / p + j / p)) := mul_le_mul_of_nonneg_right this hP
      _ = _ := by ring
  · have hRa' : R ≥ Ra := le_trans (le_max_left _ _) hR
    have hy0 : 0 < y := by linarith [le_trans hRa hRa']
    have hεa' : ε ∈ Icc (0 : ℝ) εa := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
    rw [← iteratedDeriv_succ']
    have hb := ((h2 R hRa' ε hεa' μ hμ).2.2 y hy).2
    have e : -q / p - p - 1 - ((j + 1 : ℕ) : ℝ) = -q / p - p - 2 - j := by push_cast; ring
    rw [e] at hb
    refine hb.trans ?_
    have hP : 0 ≤ ε * y ^ (-q / p - p - 2 - j) := mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le
    have : C2 ≤ C1 + C2 + C3 := by linarith
    calc C2 * ε * y ^ (-q / p - p - 2 - j) = C2 * (ε * y ^ (-q / p - p - 2 - j)) := by ring
      _ ≤ (C1 + C2 + C3) * (ε * y ^ (-q / p - p - 2 - j)) := mul_le_mul_of_nonneg_right this hP
      _ = _ := by ring
  · have hRc' : R ≥ Rc := le_trans (le_max_right _ _) hR
    have hR2 : 2 ≤ R := le_trans hRc hRc'
    have hy0 : 0 < y := by linarith
    have hεc' : ε ∈ Icc (0 : ℝ) εc := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
    obtain ⟨C4, -, h4⟩ := hprod j ((p + 1) / 2) (by positivity)
    obtain ⟨-, -, -, hZ, -⟩ := h4 R hRc' ε hεc' μ hμ
    have hev : (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) =ᶠ[𝓝 y]
        fun t => Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) * c04_Dq p R ε μ ((p + 1) / 2) t := by
      filter_upwards [Ioi_mem_nhds (show R / 2 < y by linarith)] with t ht using hZ t ht
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const_mul_field, norm_mul]
    have hn1 : ‖Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ)))‖ = 1 := by
      rw [show -(Complex.I * ((π / 4 : ℝ) : ℂ)) = ((-(π / 4) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hn1, one_mul]
    have hb := h3 R hR ε hε μ hμ y hy
    rw [hβ] at hb
    refine hb.trans ?_
    have hP : 0 ≤ ε * y ^ (1 / p - p - beta p + j / p) := mul_nonneg hε.1 (rpow_pos_of_pos hy0 _).le
    have : C3 ≤ C1 + C2 + C3 := by linarith
    calc C3 * ε * y ^ (1 / p - p - beta p + j / p) = C3 * (ε * y ^ (1 / p - p - beta p + j / p)) := by
          ring
      _ ≤ (C1 + C2 + C3) * (ε * y ^ (1 / p - p - beta p + j / p)) := mul_le_mul_of_nonneg_right this hP
      _ = _ := by ring


/-! ### Decomposition of the residual for `y ≥ 8R` -/

/-- `W'(z) = -𝟙_{z<0}` away from `0`. -/
theorem c04_aux_deriv_corner (z : ℝ) (hz : z ≠ 0) : deriv corner z = if z < 0 then -1 else 0 := by
  rcases lt_or_gt_of_ne hz with h | h
  · simp only [h, ite_true]
    have : corner =ᶠ[𝓝 z] fun x => -x := by
      filter_upwards [Iio_mem_nhds h] with x hx
      simp only [corner]; exact max_eq_left (by linarith [mem_Iio.mp hx])
    rw [this.deriv_eq]; simp
  · simp only [show ¬ z < 0 by linarith, ite_false]
    have : corner =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp only [corner]; exact max_eq_right (by linarith [mem_Ioi.mp hx])
    rw [this.deriv_eq]; simp

/-- `A_ε` is even. -/
theorem c04_aux_A_even (p ε u : ℝ) : A_eps p ε (-u) = A_eps p ε u := by
  simp [A_eps]

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_A_cont (p ε : ℝ) (hε : 0 ≤ ε) : Continuous (A_eps p ε) := by
  unfold A_eps
  exact Continuous.rpow_const (by fun_prop) (fun u => Or.inl (by positivity))

/-- Blueprint: lem:c04_QW.  For `ε ≥ 0`, `y > 0`, the integral defining `𝒬_ε(W)(y)` converges
absolutely and `𝒬_ε(W)(y) = c_ε y^{-p}`. -/
theorem c04_QW (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 ≤ ε) (y : ℝ) (hy : 0 < y) :
    Integrable (fun z => (deriv corner y - deriv corner z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant corner y z) - 1)) ∧
    c01_Q_eps p ε corner y = c_eps p ε * y ^ (-p) := by
  have hp0 : 0 < p := by linarith
  set G : ℝ → ℝ := fun t => (A_eps p ε t - 1) * (1 - t) ^ (p - 1) with hG
  set g : ℝ → ℝ := fun z => (A_eps p ε (z / (y - z)) - 1) / (y - z) ^ (p + 1) with hg
  set ψ : ℝ → ℝ := fun z => -z / (y - z) with hψ
  set ψ' : ℝ → ℝ := fun z => -y / (y - z) ^ 2 with hψ'
  -- the integrand is `𝟙_{z<0} g`
  have hae : (fun z => (deriv corner y - deriv corner z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant corner y z) - 1)) =ᵐ[volume] (Iio (0:ℝ)).indicator g := by
    have hfin : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 ∧ z ≠ y := by
      have h1 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
        exact compl_mem_ae_iff.mpr (measure_singleton _)
      have h2 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ y := by
        exact compl_mem_ae_iff.mpr (measure_singleton _)
      filter_upwards [h1, h2] with z h1 h2 using ⟨h1, h2⟩
    filter_upwards [hfin] with z ⟨hz0, hzy⟩
    rw [c04_aux_deriv_corner y hy.ne', c04_aux_deriv_corner z hz0]
    simp only [show ¬ y < 0 by linarith, ite_false]
    by_cases hz : z < 0
    · simp only [hz, ite_true]
      rw [indicator_of_mem (mem_Iio.mpr hz)]
      have hyz : 0 < y - z := by linarith
      simp only [hg, c01_secant, show ¬ (y = z) from Ne.symm hzy, ite_false, corner, abs_of_pos hyz]
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring_nf
    · simp only [hz, ite_false]
      rw [indicator_of_notMem (by simpa using hz)]
      simp
  have himg : ψ '' Iio 0 = Ioo 0 1 := by
    ext t; simp only [mem_image, mem_Iio, mem_Ioo, hψ]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hyz : 0 < y - z := by linarith
      refine ⟨div_pos (by linarith) hyz, (div_lt_one hyz).mpr (by linarith)⟩
    · rintro ⟨h0, h1⟩
      refine ⟨-(t * y) / (1 - t), div_neg_of_neg_of_pos (by nlinarith) (by linarith), ?_⟩
      have h1t : (1 - t) ≠ 0 := by linarith
      field_simp
      ring
  have hder : ∀ z ∈ Iio (0:ℝ), HasDerivWithinAt ψ (ψ' z) (Iio 0) z := by
    intro z hz
    have hyz : y - z ≠ 0 := by linarith [mem_Iio.mp hz]
    have := ((hasDerivAt_id' z).neg.div ((hasDerivAt_const z y).sub (hasDerivAt_id' z)) hyz)
    refine HasDerivWithinAt.congr_deriv (this.hasDerivWithinAt) ?_
    show _ = -y / (y - z) ^ 2
    simp only [Pi.sub_apply, Pi.neg_apply]
    field_simp; ring
  have hinj : InjOn ψ (Iio 0) := by
    intro a ha b hb hab
    have hya : y - a ≠ 0 := by linarith [mem_Iio.mp ha]
    have hyb : y - b ≠ 0 := by linarith [mem_Iio.mp hb]
    simp only [hψ] at hab
    field_simp at hab
    have : y * (a - b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have e1 : y ^ (-p) * y * y ^ (p - 1) = 1 := by
    have : y ^ (-p) * y ^ (1:ℝ) * y ^ (p - 1) = y ^ ((-p) + 1 + (p - 1)) := by
      rw [rpow_add hy, rpow_add hy]
    rw [rpow_one] at this; rw [this]; norm_num
  have hpt : ∀ z ∈ Iio (0:ℝ), g z = y ^ (-p) * (|ψ' z| • G (ψ z)) := by
    intro z hz
    have hz' : z < 0 := hz
    have hu0 : 0 < y - z := by linarith
    have e2 : (y - z) ^ (2:ℕ) * (y - z) ^ (p - 1) = (y - z) ^ (p + 1) := by
      rw [← rpow_natCast, ← rpow_add hu0]; norm_num; ring_nf
    have h1 : 1 - -z / (y - z) = y / (y - z) := by field_simp; ring
    have h2 : |-y / (y - z) ^ 2| = y / (y - z) ^ 2 := by
      rw [abs_div, abs_neg, abs_of_pos hy, abs_of_pos (by positivity)]
    have h3 : A_eps p ε (-z / (y - z)) = A_eps p ε (z / (y - z)) := by
      rw [neg_div, c04_aux_A_even]
    simp only [hg, smul_eq_mul, hG, hψ, hψ']
    rw [h1, h2, h3, div_rpow hy.le hu0.le]
    calc (A_eps p ε (z / (y - z)) - 1) / (y - z) ^ (p + 1)
        = (A_eps p ε (z / (y - z)) - 1) * (y ^ (-p) * y * y ^ (p - 1)) /
            ((y - z) ^ (2:ℕ) * (y - z) ^ (p - 1)) := by rw [e1, e2, mul_one]
      _ = _ := by
        generalize (y - z) ^ (2:ℕ) = U2
        generalize (y - z) ^ (p - 1) = U3
        generalize A_eps p ε (z / (y - z)) = a
        ring
  have hw : IntegrableOn (fun t : ℝ => (1 - t) ^ (p - 1)) (Ioo 0 1) := by
    have hi : IntervalIntegrable (fun x : ℝ => x ^ (p - 1)) volume (1 - 1) (1 - 0) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (p - 1)) volume 0 1 := by
      simpa using (hi.comp_sub_left 1).symm
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp this
  have hGint : IntegrableOn G (Ioo 0 1) := by
    refine Integrable.mono' (hw.const_mul ε) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((c04_aux_A_cont p ε hε).continuousOn.sub continuousOn_const).mul ?_
      exact ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (by linarith [ht.2]))
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
      have hpos : 0 ≤ (1 - t) ^ (p - 1) := rpow_nonneg (by linarith [ht.2]) _
      simp only [hG, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
      have ht' : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      exact mul_le_mul_of_nonneg_right (c04_aux_A_sub_one p ε t hp0 hp1.le hε ht') hpos
  have hint2 : IntegrableOn (fun z => |ψ' z| • G (ψ z)) (Iio 0) := by
    rw [← integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iio hder hinj, himg]
    exact hGint
  have hgint : IntegrableOn g (Iio 0) := by
    exact IntegrableOn.congr_fun (Integrable.const_mul hint2 (y ^ (-p)))
      (fun z hz => (hpt z hz).symm) measurableSet_Iio
  have hgval : ∫ z in Iio 0, g z = y ^ (-p) * ∫ t in (0:ℝ)..1, G t := by
    rw [setIntegral_congr_fun measurableSet_Iio hpt, integral_const_mul,
      ← integral_image_eq_integral_abs_deriv_smul measurableSet_Iio hder hinj, himg,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine ⟨(integrable_congr hae).mpr ((integrable_indicator_iff measurableSet_Iio).mpr hgint), ?_⟩
  unfold c01_Q_eps
  rw [integral_congr_ae hae, integral_indicator measurableSet_Iio, hgval]
  unfold c_eps
  simp only [hG]; ring

/-! `prop:approx_residual_positive` (`GSQG.approx_residual_positive`) is stated (and to be proved) in
`GSQG/Sec5_ApproximateSolution/ResidualBounds.lean`: its proof combines the bounds on `ℰ₅`–`ℰ₉` of chapters 05 and 06, which this file
cannot import. -/

/-! ### Control of `ℰ₁` -/

/-- An explicit flat cutoff: `χ♭(x) = smoothTransition((9/64 - x²)/(5/64))`. -/
def c04_aux_flat (x : ℝ) : ℝ := Real.smoothTransition ((9 / 64 - x ^ 2) / (5 / 64))

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_flat_support (x : ℝ) (hx : x ∉ Icc (-3 / 8 : ℝ) (3 / 8)) : c04_aux_flat x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : 9 / 64 ≤ x ^ 2 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h <;> nlinarith
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_flat_isFlat : c04_IsFlatCutoff c04_aux_flat := by
  have hsub : tsupport c04_aux_flat ⊆ Icc (-3 / 8 : ℝ) (3 / 8) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    exact hx (c04_aux_flat_support x h)
  refine ⟨?_, ?_, ?_, fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact HasCompactSupport.intro isCompact_Icc (fun x hx => c04_aux_flat_support x hx)
  · refine hsub.trans ?_
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hx.1, hx.2]

/-- `χ_R(t) = 0` for `t ≤ R`. -/
theorem c04_aux_chiR_zero (R t : ℝ) (hR : 0 < R) (ht : t ≤ R) : fam_chiR R t = 0 := by
  unfold fam_chiR chiPlus
  apply Real.smoothTransition.zero_of_nonpos
  have : t / R ≤ 1 := by rw [div_le_one hR]; exact ht
  linarith

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_chiR_smooth (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fam_chiR R) := by
  unfold fam_chiR chiPlus
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- `f_slow` is smooth. -/
theorem c04_aux_fam_slow_smooth (p R ε : ℝ) (hR : 0 < R) : ContDiff ℝ (⊤ : ℕ∞) (fam_slow p R ε) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => c_plus p ε * y ^ (-p) * fam_chiR R y) := by
    rw [contDiff_iff_contDiffAt]; intro y
    rcases lt_or_ge 0 y with hy | hy
    · exact (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hy.ne')).mul
        (c04_aux_chiR_smooth R).contDiffAt
    · have : (fun y => c_plus p ε * y ^ (-p) * fam_chiR R y) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (show y < R by linarith)] with t ht
        rw [c04_aux_chiR_zero R t hR (le_of_lt ht), mul_zero]
      exact (contDiffAt_const).congr_of_eventuallyEq this
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => c_minus p ε * |y| ^ (-p) * fam_chiR R (-y)) := by
    rw [contDiff_iff_contDiffAt]; intro y
    rcases lt_or_ge y 0 with hy | hy
    · have : (fun y => c_minus p ε * |y| ^ (-p) * fam_chiR R (-y)) =ᶠ[𝓝 y]
          fun y => c_minus p ε * (-y) ^ (-p) * fam_chiR R (-y) := by
        filter_upwards [Iio_mem_nhds hy] with t ht
        rw [abs_of_neg ht]
      refine ContDiffAt.congr_of_eventuallyEq ?_ this
      exact (contDiffAt_const.mul ((contDiffAt_rpow_const_of_ne (by linarith : -y ≠ 0)).comp y
        contDiffAt_id.neg)).mul ((c04_aux_chiR_smooth R).contDiffAt.comp y contDiffAt_id.neg)
    · have : (fun y => c_minus p ε * |y| ^ (-p) * fam_chiR R (-y)) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds (show -R < y by linarith)] with t ht
        rw [c04_aux_chiR_zero R (-t) hR (by linarith [mem_Ioi.mp ht]), mul_zero]
      exact (contDiffAt_const).congr_of_eventuallyEq this
  exact h1.add h2


/-- Splitting the `|D|^p` integral with a flat cutoff. -/
theorem c04_aux_frac_split (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ) (hχ : c04_IsFlatCutoff χ)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (M : ℝ) (hM : ∀ z, |g z| ≤ M) (y : ℝ) :
    fracD p g y = calpha p * (∫ z, χ ((y - z) / y) * (g y - g z) / |y - z| ^ (1 + p)) +
      calpha p * (∫ z, (1 - χ ((y - z) / y)) * (g y - g z) / |y - z| ^ (1 + p)) := by
  have hF := c04_aux_frac_int_C1 p hp hp1 g hg M hM y
  have hχc : Continuous (fun z : ℝ => χ ((y - z) / y)) := hχ.1.continuous.comp (by fun_prop)
  have hb : ∀ z, ‖χ ((y - z) / y)‖ ≤ 1 := fun z => by
    have := hχ.2.2.2.1 ((y - z) / y)
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have hb' : ∀ z, ‖1 - χ ((y - z) / y)‖ ≤ 1 := fun z => by
    have := hχ.2.2.2.1 ((y - z) / y)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have i1 := hF.bdd_mul hχc.aestronglyMeasurable (Eventually.of_forall hb)
  have i2 := hF.bdd_mul (continuous_const.sub hχc).aestronglyMeasurable (Eventually.of_forall hb')
  have e1 : (fun z => χ ((y - z) / y) * (g y - g z) / |y - z| ^ (1 + p)) =
      fun z => χ ((y - z) / y) * ((g y - g z) / |y - z| ^ (p + 1)) := by
    funext z; rw [add_comm 1 p, mul_div_assoc]
  have e2 : (fun z => (1 - χ ((y - z) / y)) * (g y - g z) / |y - z| ^ (1 + p)) =
      fun z => (1 - χ ((y - z) / y)) * ((g y - g z) / |y - z| ^ (p + 1)) := by
    funext z; rw [add_comm 1 p, mul_div_assoc]
  have i2' : Integrable (fun x => (1 - χ ((y - x) / y)) * ((g y - g x) / |y - x| ^ (p + 1))) := i2
  rw [e1, e2, ← mul_add, ← integral_add i1 i2']
  unfold fracD
  refine congrArg (fun I => calpha p * I) (integral_congr_ae (Eventually.of_forall fun z => ?_))
  simp only []; ring

/-- Global bounds on the derivatives of `χ₊`; for positive order they vanish off `[1,2]`. -/
theorem c04_aux_chiPlus_iter (m : ℕ) : ∃ B ≥ (0 : ℝ), ∀ x, |iteratedDeriv m chiPlus x| ≤ B ∧
    (1 ≤ m → x ∉ Icc (1 : ℝ) 2 → iteratedDeriv m chiPlus x = 0) := by
  have hc : Continuous (iteratedDeriv m chiPlus) :=
    c04_aux_chiPlus_smooth.continuous_iteratedDeriv m (by exact_mod_cast le_top)
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  have hz : ∀ x, 1 ≤ m → x ∉ Icc (1 : ℝ) 2 → iteratedDeriv m chiPlus x = 0 := by
    intro x hm hx
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · have : chiPlus =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with t ht
        exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Iio.mp ht])
      rw [this.iteratedDeriv_eq, iteratedDeriv_const]; simp
    · have : chiPlus =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        exact Real.smoothTransition.one_of_one_le (by linarith [mem_Ioi.mp ht])
      rw [this.iteratedDeriv_eq, iteratedDeriv_const]; simp [show m ≠ 0 by omega]
  refine ⟨max B1 1, by positivity, fun x => ⟨?_, hz x⟩⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · have := hB1 x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [iteratedDeriv_zero, chiPlus]
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact (Real.smoothTransition.le_one _).trans (le_max_right _ _)
    · rw [hz x hm hx, abs_zero]; positivity

/-- `T(t) = t^{-p} χ₊(t/R)` is smooth. -/
theorem c04_aux_T_smooth (p R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ (-p) * chiPlus (t / R)) := by
  rw [contDiff_iff_contDiffAt]; intro y
  rcases lt_or_ge 0 y with hy | hy
  · exact (contDiffAt_rpow_const_of_ne hy.ne').mul
      ((c04_aux_chiPlus_smooth.comp (contDiff_id.div_const R)).contDiffAt)
  · have : (fun t : ℝ => t ^ (-p) * chiPlus (t / R)) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show y < R by linarith)] with t ht
      have := c04_aux_chiR_zero R t hR (le_of_lt ht)
      simp only [fam_chiR] at this
      rw [this, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- `t^{-a} ≤ 2^a ⟨t⟩^{-a}` for `t ≥ 1`, `a ≥ 0`. -/
theorem c04_aux_rpow_le_jb' (y a : ℝ) (hy : 1 ≤ y) (ha0 : 0 ≤ a) :
    y ^ (-a) ≤ 2 ^ a * jb y ^ (-a) := by
  have hjb : 0 < jb y := Real.sqrt_pos.mpr (by positivity)
  have hjb2 : jb y / 2 ≤ y := by
    unfold jb
    rw [div_le_iff₀ two_pos, Real.sqrt_le_left (by linarith)]
    nlinarith
  have h1 : y ^ (-a) ≤ (jb y / 2) ^ (-a) := rpow_le_rpow_of_nonpos (by positivity) hjb2 (by linarith)
  refine h1.trans (le_of_eq ?_)
  rw [div_rpow hjb.le (by norm_num), rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

/-- Leibniz bound: `|∂^k T(t)| ≤ A_k ⟨t⟩^{-p-k}`, uniformly in `R ≥ 2`. -/
theorem c04_aux_T_bound (p : ℝ) (hp0 : 0 < p) (k : ℕ) : ∃ A ≥ (0 : ℝ), ∀ R ≥ (2 : ℝ), ∀ t,
    |iteratedDeriv k (fun t : ℝ => t ^ (-p) * chiPlus (t / R)) t| ≤ A * jb t ^ (-p - k) := by
  choose B hB0 hB using c04_aux_chiPlus_iter
  set A := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |(descPochhammer ℝ i).eval (-p)| *
    (2 ^ (k - i) * B (k - i)) with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => by have := hB0 (k - i); positivity)
  refine ⟨A * 2 ^ (p + k), by positivity, fun R hR t => ?_⟩
  have hR0 : 0 < R := by linarith
  set T := fun t : ℝ => t ^ (-p) * chiPlus (t / R) with hTdef
  have hsm := c04_aux_T_smooth p R hR0
  have hjbpos : 0 ≤ jb t ^ (-p - (k : ℝ)) := (rpow_pos_of_pos (Real.sqrt_pos.mpr (by positivity)) _).le
  by_cases ht : t ≤ R
  · have hzero : ∀ s < R, iteratedDeriv k T s = 0 := by
      intro s hs
      have : T =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hs] with u hu
        have := c04_aux_chiR_zero R u hR0 (le_of_lt hu)
        simp only [fam_chiR] at this
        simp only [hTdef, this, mul_zero]
      rw [this.iteratedDeriv_eq, iteratedDeriv_const]; simp
    have hcont : Continuous (iteratedDeriv k T) :=
      hsm.continuous_iteratedDeriv k (by exact_mod_cast le_top)
    have h0 : iteratedDeriv k T t = 0 := by
      rcases lt_or_eq_of_le ht with h | h
      · exact hzero t h
      · have h1 := (hcont.continuousAt (x := t)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Iio t))
        have h2 : Tendsto (iteratedDeriv k T) (𝓝[<] t) (𝓝 0) :=
          tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall
            (fun s hs => (hzero s (h ▸ hs)).symm))
        exact tendsto_nhds_unique h1 h2
    rw [h0, abs_zero]; positivity
  · push Not at ht
    have ht0 : 0 < t := by linarith
    have ht1 : 1 ≤ t := by linarith
    have hf : ContDiffAt ℝ k (fun t : ℝ => t ^ (-p)) t := contDiffAt_rpow_const_of_ne ht0.ne'
    have hg : ContDiffAt ℝ k (fun t : ℝ => chiPlus (t / R)) t :=
      ((c04_aux_chiPlus_smooth.comp (contDiff_id.div_const R)).contDiffAt).of_le
        (by exact_mod_cast le_top)
    have hT : T = (fun t : ℝ => t ^ (-p)) * (fun t => chiPlus (t / R)) := rfl
    rw [hT, iteratedDeriv_mul hf hg]
    have hgder : ∀ m, iteratedDeriv m (fun t => chiPlus (t / R)) t =
        R⁻¹ ^ m * iteratedDeriv m chiPlus (R⁻¹ * t) := by
      intro m
      have : (fun t => chiPlus (t / R)) = fun t => chiPlus (R⁻¹ * t) := by
        funext u; rw [div_eq_inv_mul]
      rw [this, iteratedDeriv_comp_const_mul (c04_aux_chiPlus_smooth.of_le (by exact_mod_cast le_top)) R⁻¹]
    have hfder : ∀ i, iteratedDeriv i (fun t : ℝ => t ^ (-p)) t =
        (descPochhammer ℝ i).eval (-p) * t ^ (-p - i) := by
      intro i; rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const]
    have key : ∀ m : ℕ, |R⁻¹ ^ m * iteratedDeriv m chiPlus (R⁻¹ * t)| ≤ 2 ^ m * B m * t⁻¹ ^ m := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [pow_zero, one_mul, mul_one]; exact (hB 0 _).1
      · by_cases hx : R⁻¹ * t ∈ Icc (1 : ℝ) 2
        · have htR : t ≤ 2 * R := by
            have := hx.2; rw [inv_mul_le_iff₀ hR0] at this; linarith
          have hRi : R⁻¹ ≤ 2 * t⁻¹ := by
            rw [inv_le_comm₀ hR0 (by positivity), mul_inv, inv_inv]
            linarith
          rw [abs_mul, abs_of_nonneg (by positivity)]
          calc R⁻¹ ^ m * |iteratedDeriv m chiPlus (R⁻¹ * t)| ≤ (2 * t⁻¹) ^ m * B m :=
                mul_le_mul (pow_le_pow_left₀ (by positivity) hRi m) (hB m _).1 (abs_nonneg _)
                  (by positivity)
            _ = 2 ^ m * B m * t⁻¹ ^ m := by rw [mul_pow]; ring
        · rw [(hB m _).2 hm hx, mul_zero, abs_zero]; have := hB0 m; positivity
    have hterm : ∀ i ∈ Finset.range (k + 1),
        |(k.choose i : ℝ) * iteratedDeriv i (fun t : ℝ => t ^ (-p)) t *
          iteratedDeriv (k - i) (fun t => chiPlus (t / R)) t| ≤
        (k.choose i : ℝ) * |(descPochhammer ℝ i).eval (-p)| * (2 ^ (k - i) * B (k - i)) *
          t ^ (-p - (k : ℝ)) := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [hfder, hgder]
      have hpow : t ^ (-p - (i : ℝ)) * t⁻¹ ^ (k - i) = t ^ (-p - (k : ℝ)) := by
        rw [inv_pow, ← rpow_natCast, ← rpow_neg ht0.le, ← rpow_add ht0, Nat.cast_sub hik]
        ring_nf
      have e : (k.choose i : ℝ) * ((descPochhammer ℝ i).eval (-p) * t ^ (-p - (i : ℝ))) *
          (R⁻¹ ^ (k - i) * iteratedDeriv (k - i) chiPlus (R⁻¹ * t)) =
          ((k.choose i : ℝ) * (descPochhammer ℝ i).eval (-p) * t ^ (-p - (i : ℝ))) *
          (R⁻¹ ^ (k - i) * iteratedDeriv (k - i) chiPlus (R⁻¹ * t)) := by ring
      rw [e, abs_mul (_ * _ * _), abs_mul (_ * _), abs_mul, Nat.abs_cast,
        abs_of_pos (rpow_pos_of_pos ht0 _)]
      calc (k.choose i : ℝ) * |(descPochhammer ℝ i).eval (-p)| * t ^ (-p - (i : ℝ)) *
            |R⁻¹ ^ (k - i) * iteratedDeriv (k - i) chiPlus (R⁻¹ * t)|
          ≤ (k.choose i : ℝ) * |(descPochhammer ℝ i).eval (-p)| * t ^ (-p - (i : ℝ)) *
            (2 ^ (k - i) * B (k - i) * t⁻¹ ^ (k - i)) :=
            mul_le_mul_of_nonneg_left (key _) (by positivity)
        _ = (k.choose i : ℝ) * |(descPochhammer ℝ i).eval (-p)| * (2 ^ (k - i) * B (k - i)) *
            (t ^ (-p - (i : ℝ)) * t⁻¹ ^ (k - i)) := by ring
        _ = _ := by rw [hpow]
    have hjb := c04_aux_rpow_le_jb' t (p + k) ht1 (by positivity)
    rw [show -(p + (k : ℝ)) = -p - k by ring] at hjb
    calc _ ≤ ∑ i ∈ Finset.range (k + 1), |(k.choose i : ℝ) * iteratedDeriv i (fun t : ℝ => t ^ (-p)) t *
          iteratedDeriv (k - i) (fun t => chiPlus (t / R)) t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |(descPochhammer ℝ i).eval (-p)| *
          (2 ^ (k - i) * B (k - i)) * t ^ (-p - (k : ℝ)) := Finset.sum_le_sum hterm
      _ = A * t ^ (-p - (k : ℝ)) := by rw [hAdef, Finset.sum_mul]
      _ ≤ A * (2 ^ (p + k) * jb t ^ (-p - (k : ℝ))) := mul_le_mul_of_nonneg_left hjb hA0
      _ = _ := by ring

/-- `|∂^k f_slow| ≤ C ε ⟨y⟩^{-p-k}` uniformly in `R ≥ 2`, `ε ∈ [0,1]`. -/
theorem c04_aux_fslow_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ R ≥ (2 : ℝ), ∀ ε ∈ Icc (0 : ℝ) 1, ∀ y,
      |iteratedDeriv k (fam_slow p R ε) y| ≤ C * ε * jb y ^ (-p - k) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨A, hA0, hA⟩ := c04_aux_T_bound p hp0 k
  obtain ⟨Cc, hCc, hcs⟩ := (c04_constants_small p hp hp1 1 one_pos).1
  refine ⟨2 * Cc * A + 1, by positivity, fun R hR ε hε y => ?_⟩
  have hR0 : 0 < R := by linarith
  obtain ⟨-, -, -, -, -, hcp, hcm⟩ := hcs ε hε 0 (by simp)
  set T := fun t : ℝ => t ^ (-p) * chiPlus (t / R) with hTdef
  have hfun : fam_slow p R ε = fun t => c_plus p ε * T t + c_minus p ε * T (-t) := by
    funext t
    simp only [fam_slow, fam_chiR, hTdef]
    by_cases ht : -t ≤ R
    · have := c04_aux_chiR_zero R (-t) hR0 ht
      simp only [fam_chiR] at this
      rw [this]; ring
    · push Not at ht
      rw [abs_of_neg (by linarith : t < 0)]; ring
  have hTs := c04_aux_T_smooth p R hR0
  have h1 : ContDiffAt ℝ k (fun t => c_plus p ε * T t) y :=
    contDiffAt_const.mul ((hTs.contDiffAt).of_le (by exact_mod_cast le_top))
  have h2 : ContDiffAt ℝ k (fun t => c_minus p ε * T (-t)) y :=
    contDiffAt_const.mul (((hTs.comp contDiff_neg).contDiffAt).of_le (by exact_mod_cast le_top))
  rw [hfun, iteratedDeriv_fun_add h1 h2, iteratedDeriv_const_mul_field,
    iteratedDeriv_const_mul_field (f := fun t => T (-t)), iteratedDeriv_comp_neg]
  have hjbneg : jb (-y) = jb y := by unfold jb; rw [neg_sq]
  have e1 := hA R hR y
  have e2 := hA R hR (-y)
  rw [hjbneg] at e2
  have hJ : 0 ≤ jb y ^ (-p - (k : ℝ)) := (rpow_pos_of_pos (Real.sqrt_pos.mpr (by positivity)) _).le
  have hsgn : |(-1 : ℝ) ^ k • iteratedDeriv k T (-y)| = |iteratedDeriv k T (-y)| := by
    rw [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  calc _ ≤ |c_plus p ε * iteratedDeriv k T y| + |c_minus p ε * ((-1 : ℝ) ^ k • iteratedDeriv k T (-y))| :=
        abs_add_le _ _
    _ = |c_plus p ε| * |iteratedDeriv k T y| + |c_minus p ε| * |iteratedDeriv k T (-y)| := by
        rw [abs_mul, abs_mul, hsgn]
    _ ≤ (Cc * ε) * (A * jb y ^ (-p - (k : ℝ))) + (Cc * ε) * (A * jb y ^ (-p - (k : ℝ))) := by
        have : 0 ≤ Cc * ε := mul_nonneg hCc.le hε.1
        gcongr
    _ = (2 * Cc * A) * ε * jb y ^ (-p - (k : ℝ)) := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hJ
        apply mul_le_mul_of_nonneg_right _ hε.1
        linarith

/-- Blueprint: lem:c04_E1_formula.  For `y ≥ 2R`, `ℰ₁(y) = |D|^p f_slow'(y)`, both sides are `C¹`
on `(R,∞)` with equal derivatives on `[2R,∞)`; and `|∂^k f_slow| ≤ C_k ε ⟨y⟩^{-p-k}` on `ℝ`. -/
theorem c04_E1_formula (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀,
        (∀ y ≥ 2 * R, residual_decomposition_E1 p R ε y = fracD p (deriv (fam_slow p R ε)) y) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E1 p R ε) (Ioi R) ∧
        ContDiffOn ℝ 1 (fracD p (deriv (fam_slow p R ε))) (Ioi R) ∧
        (∀ y ≥ 2 * R, deriv (residual_decomposition_E1 p R ε) y =
          deriv (fracD p (deriv (fam_slow p R ε))) y)) ∧
      (∀ k : ℕ, ∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ y : ℝ,
        |iteratedDeriv k (fam_slow p R ε) y| ≤ C * ε * jb y ^ (-p - k)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  refine ⟨1, ⟨one_pos, le_rfl⟩, 2, le_rfl, fun R hR ε hε => ?_, fun k => ?_⟩
  swap
  · obtain ⟨C, hC, hb⟩ := c04_aux_fslow_bound p hp hp1 k
    exact ⟨C, hC, fun R hR ε hε y => hb R hR ε hε y⟩
  have hR0 : 0 < R := by linarith
  have hε0 := hε.1
  set h := fam_slow p R ε with hhdef
  set u := deriv h with hudef
  have hsm : ContDiff ℝ (⊤ : ℕ∞) h := c04_aux_fam_slow_smooth p R ε hR0
  have hhd : Differentiable ℝ h := hsm.differentiable (by simp)
  obtain ⟨C1, hC1, hb1⟩ := c04_aux_fslow_bound p hp hp1 1
  obtain ⟨C2, hC2, hb2⟩ := c04_aux_fslow_bound p hp hp1 2
  have hjb1 : ∀ (z a : ℝ), 0 ≤ a → jb z ^ (-a) ≤ 1 := fun z a ha =>
    rpow_le_one_of_one_le_of_nonpos (c04_aux_one_le_jb z) (by linarith)
  have hu0 : ∀ z, |u z| ≤ C1 * ε := fun z => by
    have := hb1 R hR ε hε z
    rw [iteratedDeriv_one] at this
    refine this.trans ?_
    have h' := hjb1 z (p + 1) (by linarith)
    rw [show -(p + 1) = -p - ((1 : ℕ) : ℝ) by push_cast; ring] at h'
    have : 0 ≤ C1 * ε := by positivity
    nlinarith
  have hu1 : ∀ z, |deriv u z| ≤ C2 * ε := fun z => by
    have := hb2 R hR ε hε z
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    refine this.trans ?_
    have h' := hjb1 z (p + 2) (by linarith)
    rw [show -(p + 2) = -p - ((2 : ℕ) : ℝ) by push_cast; ring] at h'
    have : 0 ≤ C2 * ε := by positivity
    nlinarith
  have hu2 : ContDiff ℝ 2 u := by
    rw [hudef]; exact (contDiff_infty_iff_deriv.mp hsm).2.of_le (by simp)
  have hFC1 := c04_aux_fracD_C1 p hp hp1 u hu2 (C1 * ε) (C2 * ε) hu0 hu1
  set G : ℝ → ℝ := fun t => h t - t * u t + c_eps p ε * t ^ (-p) with hGdef
  have hE1eq : ∀ t > 0, residual_decomposition_E1 p R ε t = fracD p u t + G t := by
    intro t ht
    unfold residual_decomposition_E1 L0 fracDdy
    rw [(c04_QW p hp hp1 ε hε0 t ht).2]
    simp only [hGdef, hudef, hhdef]; ring
  -- on `[2R,∞)`, `f_slow = c₊ t^{-p}`
  have hheq : ∀ s ≥ 2 * R, h s = c_plus p ε * s ^ (-p) := by
    intro s hs
    have h1 : fam_chiR R s = 1 := by
      unfold fam_chiR chiPlus
      apply Real.smoothTransition.one_of_one_le
      rw [le_sub_iff_add_le, le_div_iff₀ hR0]; linarith
    have h2 : fam_chiR R (-s) = 0 := c04_aux_chiR_zero R (-s) hR0 (by linarith)
    simp only [hhdef, fam_slow, h1, h2]; ring
  have hueq : ∀ t ≥ 2 * R, u t = c_plus p ε * (-p * t ^ (-p - 1)) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hw : HasDerivWithinAt (fun s => c_plus p ε * s ^ (-p)) (c_plus p ε * (-p * t ^ (-p - 1)))
        (Ici t) t := ((hasDerivAt_rpow_const (Or.inl ht0.ne')).const_mul _).hasDerivWithinAt
    have hw' : HasDerivWithinAt h (c_plus p ε * (-p * t ^ (-p - 1))) (Ici t) t :=
      hw.congr (fun s hs => hheq s (le_trans ht hs)) (hheq t ht)
    exact (uniqueDiffWithinAt_Ici t).eq_deriv _ (hhd t).hasDerivAt.hasDerivWithinAt hw'
  have hG0 : ∀ t ≥ 2 * R, G t = 0 := by
    intro t ht
    have ht0 : 0 < t := by linarith
    simp only [hGdef]
    rw [hheq t ht, hueq t ht]
    have e : t * t ^ (-p - 1) = t ^ (-p) := by
      rw [show -p = (-p - 1) + 1 by ring, rpow_add_one ht0.ne']; ring_nf
    have hcp : c_plus p ε * (p + 1) = -c_eps p ε := by
      unfold c_plus; field_simp
    calc c_plus p ε * t ^ (-p) - t * (c_plus p ε * (-p * t ^ (-p - 1))) + c_eps p ε * t ^ (-p)
        = (c_plus p ε * (p + 1) + c_eps p ε) * t ^ (-p) := by rw [← e]; ring
      _ = 0 := by rw [hcp]; ring
  have hGsm : ∀ t > 0, ContDiffAt ℝ 1 G t := by
    intro t ht
    have a1 : ContDiffAt ℝ 1 h t := (hsm.contDiffAt).of_le (by exact_mod_cast le_top)
    have a2 : ContDiffAt ℝ 1 u t := (hu2.contDiffAt).of_le (by norm_num)
    exact (a1.sub (contDiffAt_id.mul a2)).add (contDiffAt_const.mul
      (contDiffAt_rpow_const_of_ne ht.ne'))
  refine ⟨fun y hy => ?_, ?_, hFC1.contDiffOn, fun y hy => ?_⟩
  · rw [hE1eq y (by linarith), hG0 y hy, add_zero]
  · intro t ht
    have ht0 : 0 < t := lt_trans hR0 ht
    refine ((hFC1.contDiffAt.add (hGsm t ht0)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [Ioi_mem_nhds ht0] with s hs
    exact hE1eq s hs
  · have hy0 : 0 < y := by linarith
    have hev : residual_decomposition_E1 p R ε =ᶠ[𝓝 y] fun t => fracD p u t + G t := by
      filter_upwards [Ioi_mem_nhds hy0] with s hs
      exact hE1eq s hs
    have hGd : DifferentiableAt ℝ G y := (hGsm y hy0).differentiableAt (by norm_num)
    have hFd : DifferentiableAt ℝ (fracD p u) y := (hFC1.differentiable (by norm_num)) y
    have hdG : deriv G y = 0 := by
      have hw : HasDerivWithinAt G 0 (Ici y) y :=
        (hasDerivWithinAt_const y (Ici y) (0 : ℝ)).congr (fun s hs => hG0 s (le_trans hy hs))
          (hG0 y hy)
      exact (uniqueDiffWithinAt_Ici y).eq_deriv _ hGd.hasDerivAt.hasDerivWithinAt hw
    rw [hev.deriv_eq, deriv_fun_add hFd hGd, hdG, add_zero]

/-- `|w| ≤ ⟨w⟩`. -/
theorem c04_aux_abs_le_jb (w : ℝ) : |w| ≤ jb w := by
  unfold jb
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- `(y/2)^{-a} ≤ 16 y^{-a}` for `y > 0`, `0 ≤ a ≤ 4`. -/
theorem c04_aux_half_rpow (y a : ℝ) (hy : 0 < y) (ha0 : 0 ≤ a) (ha : a ≤ 4) :
    (y / 2) ^ (-a) ≤ 16 * y ^ (-a) := by
  rw [div_rpow hy.le (by norm_num)]
  have h2 : (2 : ℝ) ^ (-(4 : ℝ)) ≤ 2 ^ (-a) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
    rw [rpow_neg (by norm_num), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
  rw [h3] at h2
  have h5 : 0 ≤ y ^ (-a) := by positivity
  calc y ^ (-a) / 2 ^ (-a) ≤ y ^ (-a) / (1 / 16) := div_le_div_of_nonneg_left h5 (by norm_num) h2
    _ = 16 * y ^ (-a) := by ring

/-- Blueprint: lem:c04_frac_decay_near.  Near-diagonal part of `|D|^p` on decaying functions:
`|c_α ∫ χ♭((y-z)/y)(h^{(k+1)}(y) - h^{(k+1)}(z))|y-z|^{-1-p} dz| ≤ C(p) K y^{-2p-1-k}`
for `y ≥ 2`, `k ∈ {0,1}`, `|∂^l h| ≤ K⟨z⟩^{-p-l}` (`l ≤ 3`). -/
theorem c04_frac_decay_near (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C > (0 : ℝ), ∀ χ : ℝ → ℝ, c04_IsFlatCutoff χ →
      ∀ (k : ℕ), k ≤ 1 → ∀ (K : ℝ), 0 < K → ∀ h : ℝ → ℝ, ContDiff ℝ 3 h →
        (∀ l : ℕ, l ≤ 3 → ∀ z, |iteratedDeriv l h z| ≤ K * jb z ^ (-p - l)) →
        ∀ y ≥ (2 : ℝ),
          |calpha p * ∫ z, χ ((y - z) / y) *
              (iteratedDeriv (k + 1) h y - iteratedDeriv (k + 1) h z) / |y - z| ^ (1 + p)| ≤
            C * K * y ^ (-2 * p - 1 - k) := by
  have hp0 : 0 < p := by linarith
  refine ⟨|calpha p| * 2 * 16 / (1 - p) + 1, by
    have : 0 < 1 - p := by linarith
    positivity, fun χ hχ k hk K hK h hh hb y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set Y := y / 2 with hYdef
  have hY : 0 < Y := by positivity
  have hY1 : 1 ≤ Y := by linarith
  set g := iteratedDeriv (k + 1) h with hgdef
  set Λ := K * Y ^ (-p - 2 - (k : ℝ)) with hΛdef
  have hΛ : 0 ≤ Λ := by positivity
  have hgd : Differentiable ℝ g := hh.differentiable_iteratedDeriv (k + 1) (by norm_cast; omega)
  have hdg : ∀ w, deriv g w = iteratedDeriv (k + 2) h w := fun w => by
    rw [hgdef, show k + 2 = k + 1 + 1 from rfl, iteratedDeriv_succ (n := k + 1)]
  have hLip : ∀ z, |y - z| ≤ Y → |g y - g z| ≤ Λ * |y - z| := by
    intro z hz
    have hz' := abs_le.mp hz
    have hs : Convex ℝ (Icc Y (3 * Y)) := convex_Icc _ _
    have hzI : z ∈ Icc Y (3 * Y) := ⟨by linarith [hz'.2], by linarith [hz'.1]⟩
    have hyI : y ∈ Icc Y (3 * Y) := ⟨by linarith, by linarith⟩
    have hbd : ∀ w ∈ Icc Y (3 * Y), ‖deriv g w‖ ≤ Λ := by
      intro w hw
      rw [hdg, Real.norm_eq_abs]
      have hwk := hb (k + 2) (by omega) w
      refine hwk.trans ?_
      apply mul_le_mul_of_nonneg_left _ hK.le
      have hwj : Y ≤ jb w := le_trans hw.1 ((le_abs_self w).trans (c04_aux_abs_le_jb w))
      have := rpow_le_rpow_of_nonpos hY hwj (show -p - ((k + 2 : ℕ) : ℝ) ≤ 0 by
        push_cast; linarith)
      refine this.trans (le_of_eq ?_)
      congr 1; push_cast; ring
    have := hs.norm_image_sub_le_of_norm_deriv_le (fun w _ => hgd w) hbd hzI hyI
    simpa [Real.norm_eq_abs] using this
  set D : ℝ → ℝ := fun z => c04_aux_psiR p Λ 0 Y |y - z| with hD
  obtain ⟨hψi, hψ⟩ := c04_aux_psiR_integral p Λ 0 Y hp0 hp1 hY
  have hDi : Integrable D := (c04_aux_c01_integrable_comp_abs hψi).comp_sub_left y
  have hDint : ∫ z, D z = 2 * (Λ * Y ^ (1 - p) / (1 - p)) := by
    simp only [hD]
    rw [integral_sub_left_eq_self (fun z => c04_aux_psiR p Λ 0 Y |z|) volume y,
      integral_comp_abs (f := c04_aux_psiR p Λ 0 Y), hψ]
    ring
  have hpt : ∀ z, ‖χ ((y - z) / y) * (g y - g z) / |y - z| ^ (1 + p)‖ ≤ D z := by
    intro z
    rw [Real.norm_eq_abs]
    simp only [hD, c04_aux_psiR]
    by_cases hzy : z = y
    · subst hzy; simp only [sub_self, mul_zero, zero_div, abs_zero, hY.le, ite_true]
      rw [Real.zero_rpow (by linarith)]; simp
    have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hzy))
    split_ifs with h1
    · have hχb := hχ.2.2.2.1 ((y - z) / y)
      rw [abs_div, abs_mul, abs_of_pos (rpow_pos_of_pos hpos _), abs_of_nonneg hχb.1,
        div_le_iff₀ (rpow_pos_of_pos hpos _)]
      calc χ ((y - z) / y) * |g y - g z| ≤ 1 * (Λ * |y - z|) :=
            mul_le_mul hχb.2 (hLip z h1) (abs_nonneg _) zero_le_one
        _ = Λ * |y - z| ^ (-p) * |y - z| ^ (1 + p) := by
            rw [one_mul, mul_assoc Λ (|y - z| ^ (-p)), ← rpow_add hpos]; simp
    · have h0 : χ ((y - z) / y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        have := hχ.2.2.1 hm
        have h2 : |(y - z) / y| < 1 / 2 := abs_lt.mpr ⟨by linarith [this.1], this.2⟩
        rw [abs_div, abs_of_pos hy0, div_lt_iff₀ hy0] at h2
        exact h1 (by simp only [hYdef]; linarith)
      rw [h0]; simp
  have hint : |∫ z, χ ((y - z) / y) * (g y - g z) / |y - z| ^ (1 + p)| ≤
      2 * (Λ * Y ^ (1 - p) / (1 - p)) := by
    rw [← hDint, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hDi (Eventually.of_forall hpt)
  have hΛY : Λ * Y ^ (1 - p) ≤ 16 * K * y ^ (-2 * p - 1 - (k : ℝ)) := by
    simp only [hΛdef]
    rw [mul_assoc, ← rpow_add hY]
    have hk1 : (k : ℝ) ≤ 1 := by exact_mod_cast hk
    have := c04_aux_half_rpow y (2 * p + 1 + k) hy0 (by positivity) (by linarith)
    rw [show -p - 2 - (k : ℝ) + (1 - p) = -(2 * p + 1 + k) by ring]
    rw [show -2 * p - 1 - (k : ℝ) = -(2 * p + 1 + k) by ring]
    calc K * Y ^ (-(2 * p + 1 + (k : ℝ))) ≤ K * (16 * y ^ (-(2 * p + 1 + (k : ℝ)))) :=
          mul_le_mul_of_nonneg_left this hK.le
      _ = _ := by ring
  have h1p : 0 < 1 - p := by linarith
  have hypos : 0 ≤ K * y ^ (-2 * p - 1 - (k : ℝ)) := by positivity
  rw [abs_mul]
  calc |calpha p| * |∫ z, χ ((y - z) / y) * (g y - g z) / |y - z| ^ (1 + p)|
      ≤ |calpha p| * (2 * (Λ * Y ^ (1 - p) / (1 - p))) := mul_le_mul_of_nonneg_left hint (abs_nonneg _)
    _ ≤ |calpha p| * (2 * (16 * K * y ^ (-2 * p - 1 - (k : ℝ)) / (1 - p))) := by
        gcongr
    _ = (|calpha p| * 2 * 16 / (1 - p)) * (K * y ^ (-2 * p - 1 - (k : ℝ))) := by
        field_simp
    _ ≤ (|calpha p| * 2 * 16 / (1 - p) + 1) * (K * y ^ (-2 * p - 1 - (k : ℝ))) := by
        linarith
    _ = _ := by ring

/-- Flat cutoffs reflected. -/
theorem c04_aux_flat_neg (χ : ℝ → ℝ) (hχ : c04_IsFlatCutoff χ) : c04_IsFlatCutoff (fun x => χ (-x)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hχ
  refine ⟨h1.comp contDiff_neg, h2.comp_homeomorph (Homeomorph.neg ℝ), ?_, fun x => h4 _,
    fun x hx => h5 _ ⟨by linarith [hx.2], by linarith [hx.1]⟩⟩
  intro x hx
  have : -x ∈ tsupport χ := by
    have e : (fun x => χ (-x)) = χ ∘ (Homeomorph.neg ℝ) := rfl
    rw [e, tsupport_comp_eq_preimage] at hx
    exact hx
  have := h3 this
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

/-- Derivatives of a flat cutoff vanish outside `(-1/2,1/2)` and are bounded. -/
theorem c04_aux_flat_iter (χ : ℝ → ℝ) (hχ : c04_IsFlatCutoff χ) (i : ℕ) :
    ∃ B ≥ (0 : ℝ), ∀ x, |iteratedDeriv i χ x| ≤ B ∧ (1 / 2 ≤ |x| → iteratedDeriv i χ x = 0) := by
  obtain ⟨h1, -, h3, -, -⟩ := hχ
  have hc : Continuous (iteratedDeriv i χ) := h1.continuous_iteratedDeriv i (by exact_mod_cast le_top)
  have hz : ∀ x, 1 / 2 ≤ |x| → iteratedDeriv i χ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport χ := fun h => by
      have := h3 h
      rcases le_abs'.mp hx with h' | h' <;> linarith [this.1, this.2]
    have hev : χ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · simp [hi.ne']
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ⟨?_, hz x⟩⟩
  by_cases hx : 1 / 2 ≤ |x|
  · rw [hz x hx, abs_zero]; exact le_max_right _ _
  · push Not at hx
    have := hB x ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)


/-- Kernel bound on `w > 0`: `|∂^m[(1-χ(w/y))|w|^{-(1+p)}]| ≤ B w^{-(1+p)-m}`. -/
theorem c04_aux_kernel_pos (p : ℝ) (χ : ℝ → ℝ) (hχ : c04_IsFlatCutoff χ) (m : ℕ) :
    ∃ B ≥ (0 : ℝ), ∀ y > (0 : ℝ), ∀ w > (0 : ℝ),
      |iteratedDeriv m (fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p))) w| ≤ B * w ^ (-(1 + p) - m) := by
  choose Bχ hBχ0 hBχ using c04_aux_flat_iter χ hχ
  set A := 1 + ∑ i ∈ Finset.range (m + 1), Bχ i with hA
  set Ag := ∑ i ∈ Finset.range (m + 1), |(descPochhammer ℝ i).eval (-(1 + p))| with hAg
  have hA0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), Bχ i := Finset.sum_nonneg (fun i _ => hBχ0 i)
  have hAg0 : 0 ≤ Ag := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨2 ^ m * (A * Ag), by positivity, fun y hy w hw => ?_⟩
  have hsm := hχ.1
  have hev : (fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p))) =ᶠ[𝓝 w]
      (fun w => 1 - χ (y⁻¹ * w)) * (fun w : ℝ => w ^ (-(1 + p))) := by
    filter_upwards [Ioi_mem_nhds hw] with t ht
    simp only [Pi.mul_apply, abs_of_pos (mem_Ioi.mp ht), div_eq_inv_mul]
  rw [hev.iteratedDeriv_eq]
  have hfC : ContDiffAt ℝ m (fun w => 1 - χ (y⁻¹ * w)) w :=
    (contDiffAt_const.sub ((hsm.comp (contDiff_const.mul contDiff_id)).contDiffAt)).of_le
      (by exact_mod_cast le_top)
  have hgC : ContDiffAt ℝ m (fun w : ℝ => w ^ (-(1 + p))) w := contDiffAt_rpow_const_of_ne hw.ne'
  have h := c04_aux_leibniz _ _ w hw m hfC hgC A Ag 0 (-(1 + p)) (-1) ?_ ?_
  · rw [Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    congr 1; ring_nf
  · intro i hi
    have hBi : Bχ i ≤ ∑ i ∈ Finset.range (m + 1), Bχ i :=
      Finset.single_le_sum (f := Bχ) (fun i _ => hBχ0 i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, zero_mul, add_zero, rpow_zero, mul_one]
      have := hχ.2.2.2.1 (y⁻¹ * w)
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · rw [iteratedDeriv_const_sub hi0, iteratedDeriv_neg, iteratedDeriv_comp_const_mul (hsm.of_le (by exact_mod_cast le_top)),
        abs_neg, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hy)]
      have hpow : w ^ ((0 : ℝ) + i * (-1)) = (w⁻¹) ^ i := by
        rw [zero_add, show (i : ℝ) * (-1) = -(i : ℝ) by ring, rpow_neg hw.le, rpow_natCast, inv_pow]
      rw [hpow]
      by_cases hx : 1 / 2 ≤ |y⁻¹ * w|
      · rw [(hBχ i _).2 hx, abs_zero, mul_zero]; positivity
      · push Not at hx
        have hyw : y⁻¹ ≤ w⁻¹ := by
          rw [abs_of_pos (by positivity)] at hx
          rw [inv_le_inv₀ hy hw]
          have := (inv_mul_lt_iff₀ hy).mp hx
          linarith
        calc _ ≤ w⁻¹ ^ i * A := mul_le_mul (pow_le_pow_left₀ (by positivity) hyw i)
              ((hBχ i _).1.trans (by linarith)) (abs_nonneg _) (by positivity)
          _ = A * w⁻¹ ^ i := mul_comm _ _
  · intro i hi
    rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, Real.norm_eq_abs, abs_mul,
      abs_of_pos (rpow_pos_of_pos hw _)]
    have : |(descPochhammer ℝ i).eval (-(1 + p))| ≤ Ag :=
      Finset.single_le_sum (f := fun i => |(descPochhammer ℝ i).eval (-(1 + p))|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    refine (mul_le_mul_of_nonneg_right this (rpow_pos_of_pos hw _).le).trans (le_of_eq ?_)
    congr 2; ring


/-- The far kernel `ψ_y(w) = (1-χ(w/y))|w|^{-(1+p)}` vanishes near `|w| < y/4`. -/
theorem c04_aux_kernel_zero (p : ℝ) (χ : ℝ → ℝ) (hχ : c04_IsFlatCutoff χ) (y : ℝ) (hy : 0 < y) (w : ℝ)
    (hw : |w| < y / 4) :
    (fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p))) =ᶠ[𝓝 w] fun _ => 0 := by
  have hU : IsOpen {t : ℝ | |t| < y / 4} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hU.mem_nhds hw] with t ht
  have ht' : t / y ∈ Icc (-1 / 4 : ℝ) (1 / 4) := by
    rw [abs_lt] at ht
    constructor
    · rw [le_div_iff₀ hy]; linarith
    · rw [div_le_iff₀ hy]; linarith
  rw [hχ.2.2.2.2 _ ht']; ring

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_kernel_smooth (p : ℝ) (χ : ℝ → ℝ) (hχ : c04_IsFlatCutoff χ) (y : ℝ) (hy : 0 < y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p))) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    exact contDiffAt_const.congr_of_eventuallyEq
      (c04_aux_kernel_zero p χ hχ y hy 0 (by rw [abs_zero]; positivity))
  · exact (contDiffAt_const.sub ((hχ.1.comp (contDiff_id.div_const y)).contDiffAt)).mul
      ((contDiffAt_abs hw).rpow_const_of_ne (abs_pos.mpr hw).ne')

/-- Bound for all `w`: `|ψ_y^{(m)}(w)| ≤ B |w|^{-(1+p)-m}`, and `0` for `|w| < y/4`. -/
theorem c04_aux_kernel_bound (p : ℝ) (χ : ℝ → ℝ) (hχ : c04_IsFlatCutoff χ) (m : ℕ) :
    ∃ B ≥ (0 : ℝ), ∀ y > (0 : ℝ), ∀ w : ℝ,
      (|w| < y / 4 → iteratedDeriv m (fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p))) w = 0) ∧
      |iteratedDeriv m (fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p))) w| ≤ B * |w| ^ (-(1 + p) - m) := by
  obtain ⟨B1, hB1, h1⟩ := c04_aux_kernel_pos p χ hχ m
  obtain ⟨B2, hB2, h2⟩ := c04_aux_kernel_pos p (fun x => χ (-x)) (c04_aux_flat_neg χ hχ) m
  refine ⟨max B1 B2, le_max_of_le_left hB1, fun y hy w => ⟨fun hw => ?_, ?_⟩⟩
  · rw [(c04_aux_kernel_zero p χ hχ y hy w hw).iteratedDeriv_eq, iteratedDeriv_const]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [hm.ne']
  rcases lt_trichotomy w 0 with hw | hw | hw
  · have e : (fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p))) =
        fun t => (fun v => (1 - χ (-(v / y))) * |v| ^ (-(1 + p))) (-t) := by
      funext t; simp only [abs_neg, neg_div, neg_neg]
    rw [e, iteratedDeriv_comp_neg m (fun v => (1 - χ (-(v / y))) * |v| ^ (-(1 + p))) w, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have := h2 y hy (-w) (by linarith)
    rw [abs_of_neg hw]
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (rpow_nonneg (by linarith) _))
  · subst hw
    have := (c04_aux_kernel_zero p χ hχ y hy 0 (by rw [abs_zero]; positivity)).iteratedDeriv_eq m
    rw [this, iteratedDeriv_const]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp; positivity
    · simp [hm.ne']; positivity
  · rw [abs_of_pos hw]
    exact (h1 y hy w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))


/-- `T_a(z) = 𝟙_{|y-z| ≥ c} |y-z|^{-a}` is integrable with integral `2c^{1-a}/(a-1)`. -/
theorem c04_aux_Ta (a c y : ℝ) (ha : 1 < a) (hc : 0 < c) :
    Integrable (fun z => {z : ℝ | c ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z) ∧
    ∫ z, {z : ℝ | c ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z = 2 * (c ^ (1 - a) / (a - 1)) := by
  set f : ℝ → ℝ := (Ici c).indicator (fun t => t ^ (-a)) with hf
  have hfi : IntegrableOn f (Ioi 0) := by
    have h' : IntegrableOn (fun t : ℝ => t ^ (-a)) (Ici c) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_Ioi_rpow_of_lt (by linarith) hc)
    exact ((integrable_indicator_iff measurableSet_Ici).mpr h').integrableOn
  have e : (fun z => {z : ℝ | c ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z) =
      fun z => f |y - z| := by
    funext z; simp only [hf, indicator, mem_setOf_eq, mem_Ici]
  rw [e]
  refine ⟨(c04_aux_c01_integrable_comp_abs hfi).comp_sub_left y, ?_⟩
  rw [integral_sub_left_eq_self (fun z => f |z|) volume y, integral_comp_abs (f := f)]
  congr 1
  rw [hf, setIntegral_indicator measurableSet_Ici,
    show Ioi (0 : ℝ) ∩ Ici c = Ici c from inter_eq_right.mpr (Ici_subset_Ioi.mpr hc),
    integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hc]
  have : a - 1 ≠ 0 := by linarith
  rw [show -a + 1 = 1 - a by ring, neg_div, ← div_neg, neg_sub]

/-- The two-regime radial majorant on `(0,∞)`. -/
theorem c04_aux_psiG_integral (p b Λ M R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hb : 1 < b) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => if t ≤ R then Λ * t ^ (-p) else M * t ^ (-b)) (Ioi 0) ∧
      ∫ t in Ioi 0, (if t ≤ R then Λ * t ^ (-p) else M * t ^ (-b)) =
        Λ * R ^ (1 - p) / (1 - p) + M * R ^ (1 - b) / (b - 1) := by
  set F : ℝ → ℝ := fun t => if t ≤ R then Λ * t ^ (-p) else M * t ^ (-b) with hF
  have hIoc : IntegrableOn (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 R) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (r := -p) (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le] at this
    exact this.const_mul Λ
  have hIoi : IntegrableOn (fun t : ℝ => M * t ^ (-b)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hR).const_mul _
  have e1 : EqOn F (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 R) := by
    intro t ht; simp [hF, ht.2]
  have e2 : EqOn F (fun t : ℝ => M * t ^ (-b)) (Ioi R) := by
    intro t ht; simp [hF, not_le.mpr (show R < t from ht)]
  have i1 : IntegrableOn F (Ioc 0 R) := hIoc.congr_fun e1.symm measurableSet_Ioc
  have i2 : IntegrableOn F (Ioi R) := hIoi.congr_fun e2.symm measurableSet_Ioi
  have hU : Ioc (0:ℝ) R ∪ Ioi R = Ioi 0 := Ioc_union_Ioi_eq_Ioi hR.le
  refine ⟨hU ▸ i1.union i2, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
    setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hR,
    ← intervalIntegral.integral_of_le hR.le, integral_rpow (Or.inl (by linarith))]
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  have hb1' : 1 - b ≠ 0 := by linarith
  have h0 : (0 : ℝ) ^ (-p + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, show -p + 1 = 1 - p by ring, show -b + 1 = 1 - b by ring]
  field_simp
  ring

/-- `∫ 𝟙_{|y-z| ≥ y/4} |y-z|^{-a} ⟨z⟩^{-p} dz ≤ c_a y^{1-a-p}` for `y > 0`. -/
theorem c04_aux_Ta_jb (p a : ℝ) (hp : 0 < p) (hp1 : p < 1) (ha : 1 < a) :
    ∃ c ≥ (0 : ℝ), ∀ y > (0 : ℝ),
      Integrable (fun z => {z : ℝ | y / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z *
        jb z ^ (-p)) ∧
      ∫ z, {z : ℝ | y / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z * jb z ^ (-p) ≤
        c * y ^ (1 - a - p) := by
  refine ⟨2 * ((4 : ℝ) ^ a * 2 ^ (1 - p) / (1 - p) + 2 ^ a * 2 ^ (1 - (a + p)) / (a + p - 1)),
    by have : 0 < a + p - 1 := by linarith
       have : 0 < 1 - p := by linarith
       positivity, fun y hy => ?_⟩
  set G : ℝ → ℝ := fun t => if t ≤ 2 * y then (y / 4) ^ (-a) * t ^ (-p) else 2 ^ a * t ^ (-(a + p))
    with hG
  obtain ⟨hGi, hGv⟩ := c04_aux_psiG_integral p (a + p) ((y / 4) ^ (-a)) (2 ^ a) (2 * y) hp hp1
    (by linarith) (by positivity)
  have hGi' : Integrable (fun z => G |z|) := c04_aux_c01_integrable_comp_abs hGi
  have hjb : ∀ z, 0 < jb z := fun z => lt_of_lt_of_le one_pos (c04_aux_one_le_jb z)
  have hmeas : AEStronglyMeasurable
      (fun z => {z : ℝ | y / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z * jb z ^ (-p)) volume := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ ?_
    · refine Measurable.indicator (by fun_prop) ?_
      exact measurableSet_le measurable_const (by fun_prop)
    · unfold jb; fun_prop
  have hbd : ∀ᵐ z ∂(volume : Measure ℝ),
      ‖{z : ℝ | y / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z * jb z ^ (-p)‖ ≤ G |z| := by
    have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with z hz
    have hzp : 0 < |z| := abs_pos.mpr hz
    have hjz : jb z ^ (-p) ≤ |z| ^ (-p) :=
      rpow_le_rpow_of_nonpos hzp (c04_aux_abs_le_jb z) (by linarith)
    have hG0 : 0 ≤ G |z| := by
      simp only [hG]; split_ifs <;> positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos (hjb z) _)]
    by_cases hin : y / 4 ≤ |y - z|
    · rw [indicator_of_mem (show z ∈ {z : ℝ | y / 4 ≤ |y - z|} from hin), abs_of_nonneg (by positivity)]
      have hyz : 0 < |y - z| := by linarith [show 0 < y / 4 by positivity]
      simp only [hG]
      split_ifs with h2
      · have h1 : |y - z| ^ (-a) ≤ (y / 4) ^ (-a) := rpow_le_rpow_of_nonpos (by positivity) hin (by linarith)
        exact mul_le_mul h1 hjz (rpow_pos_of_pos (hjb z) _).le (by positivity)
      · push Not at h2
        have hyz2 : |z| / 2 ≤ |y - z| := by
          have := abs_sub_abs_le_abs_sub z y
          rw [abs_sub_comm z y, abs_of_pos hy] at this
          linarith
        have h1 : |y - z| ^ (-a) ≤ (|z| / 2) ^ (-a) :=
          rpow_le_rpow_of_nonpos (by positivity) hyz2 (by linarith)
        have h3 : (|z| / 2) ^ (-a) * |z| ^ (-p) = 2 ^ a * |z| ^ (-(a + p)) := by
          rw [div_rpow hzp.le (by norm_num), rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul,
            show -(a + p) = -a + -p by ring, rpow_add hzp]
          ring
        calc |y - z| ^ (-a) * jb z ^ (-p) ≤ (|z| / 2) ^ (-a) * |z| ^ (-p) :=
              mul_le_mul h1 hjz (rpow_pos_of_pos (hjb z) _).le (by positivity)
          _ = _ := h3
    · rw [indicator_of_notMem (show z ∉ {z : ℝ | y / 4 ≤ |y - z|} from hin), abs_zero, zero_mul]
      exact hG0
  refine ⟨Integrable.mono' hGi' hmeas hbd, ?_⟩
  refine (integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) hGi' (hbd.mono fun z hz =>
    (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at hz))).trans (le_of_eq ?_)
  · apply mul_nonneg _ (rpow_pos_of_pos (hjb z) _).le
    by_cases hin : y / 4 ≤ |y - z|
    · rw [indicator_of_mem (show z ∈ {z : ℝ | y / 4 ≤ |y - z|} from hin)]; positivity
    · rw [indicator_of_notMem (show z ∉ {z : ℝ | y / 4 ≤ |y - z|} from hin)]
  · rw [integral_comp_abs (f := G), hGv]
    have k1 : (y / 4) ^ (-a) * (2 * y) ^ (1 - p) = (4 : ℝ) ^ a * 2 ^ (1 - p) * y ^ (1 - a - p) := by
      rw [div_rpow hy.le (by norm_num), mul_rpow (by norm_num) hy.le, rpow_neg (by norm_num : (0:ℝ) ≤ 4),
        div_inv_eq_mul, show 1 - a - p = -a + (1 - p) by ring, rpow_add hy]
      ring
    have k2 : (2 * y) ^ (1 - (a + p)) = (2 : ℝ) ^ (1 - (a + p)) * y ^ (1 - a - p) := by
      rw [mul_rpow (by norm_num) hy.le, show 1 - (a + p) = 1 - a - p by ring]
    rw [k1, k2]
    ring


/-- Blueprint: lem:c04_frac_decay_far.  Far part of `|D|^p` on decaying functions:
`|c_α ∫ (1-χ♭((y-z)/y))(h^{(k+1)}(y) - h^{(k+1)}(z))|y-z|^{-1-p} dz| ≤ C(p,χ♭) K y^{-2p-1-k}`. -/
theorem c04_frac_decay_far (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ χ : ℝ → ℝ, c04_IsFlatCutoff χ → ∃ C > (0 : ℝ),
      ∀ (k : ℕ), k ≤ 1 → ∀ (K : ℝ), 0 < K → ∀ h : ℝ → ℝ, ContDiff ℝ 3 h →
        (∀ l : ℕ, l ≤ 3 → ∀ z, |iteratedDeriv l h z| ≤ K * jb z ^ (-p - l)) →
        ∀ y ≥ (2 : ℝ),
          |calpha p * ∫ z, (1 - χ ((y - z) / y)) *
              (iteratedDeriv (k + 1) h y - iteratedDeriv (k + 1) h z) / |y - z| ^ (1 + p)| ≤
            C * K * y ^ (-2 * p - 1 - k) := by
  intro χ hχ
  have hp0 : 0 < p := by linarith
  choose B hB0 hB using c04_aux_kernel_bound p χ hχ
  choose c hc0 hc using fun m : ℕ => c04_aux_Ta_jb p (1 + p + (m : ℝ)) hp0 hp1
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  set C0 := |calpha p| * (B 0 * (2 * (4 : ℝ) ^ p / p) + B 1 * c 1 + B 2 * c 2) with hC0
  have hC0n : 0 ≤ C0 := by
    rw [hC0]; apply mul_nonneg (abs_nonneg _)
    have : 0 ≤ 2 * (4 : ℝ) ^ p / p := by positivity
    nlinarith [mul_nonneg (hB0 0) this, mul_nonneg (hB0 1) (hc0 1), mul_nonneg (hB0 2) (hc0 2)]
  refine ⟨C0 + 1, by linarith, fun k hk K hK h hh hhb y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hy4 : 0 < y / 4 := by positivity
  set ψ : ℝ → ℝ := fun w => (1 - χ (w / y)) * |w| ^ (-(1 + p)) with hψ
  set φ : ℝ → ℝ := fun z => ψ (y - z) with hφ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := c04_aux_kernel_smooth p χ hχ y hy0
  have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := hψs.comp (contDiff_const.sub contDiff_id)
  set T : ℝ → ℝ → ℝ := fun a z => {z : ℝ | y / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-a)) z
    with hT
  have hT0 : ∀ a z, 0 ≤ T a z := fun a z => by
    simp only [hT]; by_cases hz : y / 4 ≤ |y - z|
    · rw [indicator_of_mem (show z ∈ {z : ℝ | y / 4 ≤ |y - z|} from hz)]; positivity
    · rw [indicator_of_notMem (show z ∉ {z : ℝ | y / 4 ≤ |y - z|} from hz)]
  -- kernel bounds
  have hφb : ∀ (m : ℕ) (z : ℝ), |iteratedDeriv m φ z| ≤ B m * T (1 + p + m) z := by
    intro m z
    have e : iteratedDeriv m φ z = (-1 : ℝ) ^ m • iteratedDeriv m ψ (y - z) := by
      rw [hφ, iteratedDeriv_comp_const_sub]
    rw [e, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    obtain ⟨hz0, hzb⟩ := hB m y hy0 (y - z)
    simp only [hT]
    by_cases hz : y / 4 ≤ |y - z|
    · rw [indicator_of_mem (show z ∈ {z : ℝ | y / 4 ≤ |y - z|} from hz)]
      refine hzb.trans (le_of_eq ?_); congr 2; ring
    · rw [indicator_of_notMem (show z ∉ {z : ℝ | y / 4 ≤ |y - z|} from hz), hz0 (not_le.mp hz),
        abs_zero, mul_zero]
  have hjbn : ∀ z, 0 < jb z := fun z => lt_of_lt_of_le one_pos (c04_aux_one_le_jb z)
  have hhb' : ∀ l : ℕ, l ≤ 3 → ∀ z, |iteratedDeriv l h z| ≤ K * jb z ^ (-p) := by
    intro l hl z
    refine (hhb l hl z).trans (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le
      (c04_aux_one_le_jb z) (by have : (0 : ℝ) ≤ l := Nat.cast_nonneg l; linarith)) hK.le)
  have hhc : ∀ l : ℕ, l ≤ 3 → Continuous (iteratedDeriv l h) := fun l hl =>
    hh.continuous_iteratedDeriv l (by exact_mod_cast hl)
  -- integrability and bounds for `φ^{(m)} g`
  have hI : ∀ (m : ℕ) (g : ℝ → ℝ), Continuous g → (∀ z, |g z| ≤ K * jb z ^ (-p)) →
      Integrable (fun z => iteratedDeriv m φ z * g z) ∧
      |∫ z, iteratedDeriv m φ z * g z| ≤ B m * K * c m * y ^ (1 - (1 + p + m) - p) := by
    intro m g hg hgb
    obtain ⟨hTi, hTb⟩ := hc m y hy0
    have hmeas : AEStronglyMeasurable (fun z => iteratedDeriv m φ z * g z) volume :=
      ((hφs.continuous_iteratedDeriv m (by exact_mod_cast le_top)).mul hg).aestronglyMeasurable
    have hdom : ∀ z, ‖iteratedDeriv m φ z * g z‖ ≤ B m * K * (T (1 + p + m) z * jb z ^ (-p)) := by
      intro z
      rw [Real.norm_eq_abs, abs_mul]
      calc |iteratedDeriv m φ z| * |g z| ≤ (B m * T (1 + p + m) z) * (K * jb z ^ (-p)) :=
            mul_le_mul (hφb m z) (hgb z) (abs_nonneg _) (mul_nonneg (hB0 m) (hT0 _ _))
        _ = _ := by ring
    have hdi : Integrable (fun z => B m * K * (T (1 + p + m) z * jb z ^ (-p))) := hTi.const_mul _
    refine ⟨Integrable.mono' hdi hmeas (Eventually.of_forall hdom), ?_⟩
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hdi (Eventually.of_forall hdom)).trans ?_
    rw [integral_const_mul]
    have := mul_le_mul_of_nonneg_left hTb (mul_nonneg (hB0 m) hK.le)
    linarith
  -- the integrand
  set D := iteratedDeriv (k + 1) h with hD
  have hDc : Continuous D := hhc (k + 1) (by omega)
  have hDb : ∀ z, |D z| ≤ K * jb z ^ (-p) := hhb' (k + 1) (by omega)
  obtain ⟨hTi0, hTv0⟩ := c04_aux_Ta (1 + p) (y / 4) y (by linarith) hy4
  have hφb0 : ∀ z, ‖φ z‖ ≤ B 0 * T (1 + p) z := fun z => by
    have := hφb 0 z; simp only [iteratedDeriv_zero, CharP.cast_eq_zero, add_zero] at this
    rwa [Real.norm_eq_abs]
  have hφi : Integrable φ :=
    Integrable.mono' (hTi0.const_mul (B 0)) hφs.continuous.aestronglyMeasurable
      (Eventually.of_forall hφb0)
  have hφint : |∫ z, φ z| ≤ B 0 * (2 * (4 : ℝ) ^ p / p) * y ^ (-p) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hTi0.const_mul (B 0)) (Eventually.of_forall hφb0)).trans
      (le_of_eq ?_)
    rw [integral_const_mul]
    have hTv0' : ∫ z, T (1 + p) z = 2 * ((y / 4) ^ (1 - (1 + p)) / (1 + p - 1)) := hTv0
    rw [hTv0', show 1 - (1 + p) = -p by ring, show 1 + p - 1 = p by ring,
      div_rpow hy0.le (by norm_num), rpow_neg (by norm_num : (0:ℝ) ≤ 4), div_inv_eq_mul]
    ring
  obtain ⟨hφDi, -⟩ := hI 0 D hDc hDb
  simp only [iteratedDeriv_zero] at hφDi
  have heq : (fun z => (1 - χ ((y - z) / y)) * (D y - D z) / |y - z| ^ (1 + p)) =
      fun z => D y * φ z - φ z * D z := by
    funext z
    simp only [hφ, hψ, rpow_neg (abs_nonneg _)]
    ring
  rw [heq, integral_sub (hφi.const_mul _) hφDi, integral_const_mul]
  -- the term `∫ φ D` after integration by parts
  have hφd : ∀ x, HasDerivAt φ (iteratedDeriv 1 φ x) x := fun x => by
    rw [iteratedDeriv_one]; exact ((hφs.differentiable (by simp)) x).hasDerivAt
  have hφdd : ∀ x, HasDerivAt (iteratedDeriv 1 φ) (iteratedDeriv 2 φ x) x := fun x => by
    have := ((hφs.differentiable_iteratedDeriv 1 (by exact_mod_cast WithTop.coe_lt_top _)) x).hasDerivAt
    rwa [← iteratedDeriv_succ] at this
  have hhd : ∀ l : ℕ, l ≤ 2 → ∀ x, HasDerivAt (iteratedDeriv l h) (iteratedDeriv (l + 1) h x) x := by
    intro l hl x
    have := ((hh.differentiable_iteratedDeriv l (by exact_mod_cast (by omega : l < 3))) x).hasDerivAt
    rwa [← iteratedDeriv_succ] at this
  have hI' : ∀ (m l : ℕ), l ≤ 3 → Integrable (iteratedDeriv m φ * iteratedDeriv l h) ∧
      |∫ z, iteratedDeriv m φ z * iteratedDeriv l h z| ≤ B m * K * c m * y ^ (1 - (1 + p + m) - p) :=
    fun m l hl => hI m _ (hhc l hl) (hhb' l hl)
  have e0 : iteratedDeriv 0 φ = φ := iteratedDeriv_zero
  have h0 : iteratedDeriv 0 h = h := iteratedDeriv_zero
  have hB1 : 0 ≤ B 1 * c 1 * K * y ^ (-2 * p - 1 - k) := by
    have := hB0 1; have := hc0 1; positivity
  have hB2 : 0 ≤ B 2 * c 2 * K * y ^ (-2 * p - 1 - k) := by
    have := hB0 2; have := hc0 2; positivity
  have hmain : |∫ z, φ z * D z| ≤ (B 1 * c 1 + B 2 * c 2) * K * y ^ (-2 * p - 1 - k) := by
    interval_cases k
    · have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := φ) (u' := iteratedDeriv 1 φ)
        (v := h) (v' := iteratedDeriv 1 h) (fun x _ => hφd x)
        (fun x _ => by simpa [h0] using hhd 0 (by norm_num) x)
        (by simpa [e0] using (hI' 0 1 (by norm_num)).1) (by simpa [h0] using (hI' 1 0 (by norm_num)).1)
        (by simpa [e0, h0] using (hI' 0 0 (by norm_num)).1)
      rw [hD, ibp, abs_neg]
      have := (hI' 1 0 (by norm_num)).2
      rw [h0] at this
      have hexp : y ^ (1 - (1 + p + ((1 : ℕ) : ℝ)) - p) = y ^ (-2 * p - 1 - ((0 : ℕ) : ℝ)) := by
        congr 1; push_cast; ring
      rw [hexp] at this
      linarith
    · have ibp1 := integral_mul_deriv_eq_deriv_mul_of_integrable (u := φ) (u' := iteratedDeriv 1 φ)
        (v := iteratedDeriv 1 h) (v' := iteratedDeriv 2 h) (fun x _ => hφd x)
        (fun x _ => hhd 1 (by norm_num) x)
        (by simpa [e0] using (hI' 0 2 (by norm_num)).1) (hI' 1 1 (by norm_num)).1
        (by simpa [e0] using (hI' 0 1 (by norm_num)).1)
      have ibp2 := integral_mul_deriv_eq_deriv_mul_of_integrable (u := iteratedDeriv 1 φ)
        (u' := iteratedDeriv 2 φ) (v := h) (v' := iteratedDeriv 1 h) (fun x _ => hφdd x)
        (fun x _ => by simpa [h0] using hhd 0 (by norm_num) x)
        (hI' 1 1 (by norm_num)).1 (by simpa [h0] using (hI' 2 0 (by norm_num)).1)
        (by simpa [h0] using (hI' 1 0 (by norm_num)).1)
      rw [hD, ibp1, ibp2, neg_neg]
      have := (hI' 2 0 (by norm_num)).2
      rw [h0] at this
      have hexp : y ^ (1 - (1 + p + ((2 : ℕ) : ℝ)) - p) = y ^ (-2 * p - 1 - ((1 : ℕ) : ℝ)) := by
        congr 1; push_cast; ring
      rw [hexp] at this
      linarith
  have hDy : |D y| ≤ K * y ^ (-p - (k + 1 : ℕ)) := by
    refine (hhb (k + 1) (by omega) y).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos hy0 ((le_abs_self y).trans (c04_aux_abs_le_jb y)) ?_) hK.le)
    have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hprod : |D y| * |∫ z, φ z| ≤ B 0 * (2 * (4 : ℝ) ^ p / p) * K * y ^ (-2 * p - 1 - k) := by
    have h1 := mul_le_mul hDy hφint (abs_nonneg _) (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [show B 0 * (2 * (4 : ℝ) ^ p / p) * K * y ^ (-2 * p - 1 - k) =
      K * (B 0 * (2 * (4 : ℝ) ^ p / p)) * (y ^ (-p - (k + 1 : ℕ)) * y ^ (-p)) by
        rw [← rpow_add hy0]; push_cast; ring_nf]
    ring
  rw [abs_mul]
  have hfin : |D y * (∫ z, φ z) - ∫ z, φ z * D z| ≤
      (B 0 * (2 * (4 : ℝ) ^ p / p) + B 1 * c 1 + B 2 * c 2) * K * y ^ (-2 * p - 1 - k) := by
    have := abs_add_le (D y * ∫ z, φ z) (-(∫ z, φ z * D z))
    rw [abs_neg, ← sub_eq_add_neg, abs_mul] at this
    linarith
  have hY : 0 ≤ K * y ^ (-2 * p - 1 - (k : ℝ)) := by positivity
  calc |calpha p| * |D y * (∫ z, φ z) - ∫ z, φ z * D z|
      ≤ |calpha p| * ((B 0 * (2 * (4 : ℝ) ^ p / p) + B 1 * c 1 + B 2 * c 2) * K * y ^ (-2 * p - 1 - k)) :=
        mul_le_mul_of_nonneg_left hfin (abs_nonneg _)
    _ = C0 * (K * y ^ (-2 * p - 1 - k)) := by rw [hC0]; ring_nf
    _ ≤ (C0 + 1) * K * y ^ (-2 * p - 1 - k) := by nlinarith


/-- Blueprint: prop:approx_E1.  `|∂^j ℰ₁(y)| ≤ C ε ⟨y⟩^{-2p-1-j}` for `y ≥ 2R`, `j = 0,1`, hence
`≤ C ε ⟨y⟩^{-γ+j/p}` for every `γ ≤ 2p+1`. -/
theorem approx_E1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ y ≥ 2 * R, ∀ j : ℕ, j ≤ 1 →
        |iteratedDeriv j (residual_decomposition_E1 p R ε) y| ≤ C * ε * jb y ^ (-2 * p - 1 - j) ∧
        ∀ γ : ℝ, γ ≤ 2 * p + 1 →
          |iteratedDeriv j (residual_decomposition_E1 p R ε) y| ≤ C * ε * jb y ^ (-γ + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  obtain ⟨ε₀, hε₀, R₀, hR₀, hform, hslow⟩ := c04_E1_formula p hp hp1 δ hδ hδμ
  obtain ⟨Cn, hCn, hnear⟩ := c04_frac_decay_near p hp hp1
  obtain ⟨Cf, hCf, hfar⟩ := c04_frac_decay_far p hp hp1 c04_aux_flat c04_aux_flat_isFlat
  obtain ⟨S0, hS0, hs0⟩ := hslow 0
  obtain ⟨S1, hS1, hs1⟩ := hslow 1
  obtain ⟨S2, hS2, hs2⟩ := hslow 2
  obtain ⟨S3, hS3, hs3⟩ := hslow 3
  set K₀ := S0 + S1 + S2 + S3 with hK₀
  refine ⟨ε₀, hε₀, R₀, hR₀, 16 * (Cn + Cf) * K₀ + 1, by positivity,
    fun R hR ε hε y hy j hj => ?_⟩
  have hR2 : 2 ≤ R := le_trans hR₀ hR
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hε0 := hε.1
  obtain ⟨hE, -, -, hdE⟩ := hform R hR ε hε
  set h := fam_slow p R ε with hhdef
  have hsm : ContDiff ℝ (⊤ : ℕ∞) h := c04_aux_fam_slow_smooth p R ε (by linarith)
  have hjbn : ∀ (z a : ℝ), 0 ≤ a → jb z ^ (-a) ≤ 1 := fun z a ha =>
    rpow_le_one_of_one_le_of_nonpos (c04_aux_one_le_jb z) (by linarith)
  -- bounds on the derivatives of `f_slow`
  have hbl : ∀ l : ℕ, l ≤ 3 → ∀ z, |iteratedDeriv l h z| ≤ K₀ * ε * jb z ^ (-p - l) := by
    intro l hl z
    have hpos : 0 ≤ ε * jb z ^ (-p - l) := by
      have : 0 < jb z := lt_of_lt_of_le one_pos (c04_aux_one_le_jb z)
      positivity
    have key : ∀ S : ℝ, S ≤ K₀ → |iteratedDeriv l h z| ≤ S * ε * jb z ^ (-p - l) →
        |iteratedDeriv l h z| ≤ K₀ * ε * jb z ^ (-p - l) := fun S hS hb => by
      refine hb.trans ?_
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hS hpos
    interval_cases l
    · exact key S0 (by linarith) (hs0 R hR ε hε z)
    · exact key S1 (by linarith) (hs1 R hR ε hε z)
    · exact key S2 (by linarith) (hs2 R hR ε hε z)
    · exact key S3 (by linarith) (hs3 R hR ε hε z)
  have hbnd : ∀ l : ℕ, l ≤ 3 → ∀ z, |iteratedDeriv l h z| ≤ K₀ * ε := fun l hl z => by
    refine (hbl l hl z).trans ?_
    have := hjbn z (p + l) (by positivity)
    rw [show -p - (l : ℝ) = -(p + l) by ring]
    have : 0 ≤ K₀ * ε := by positivity
    nlinarith
  have hsmk : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n h) := fun n => by
    rw [iteratedDeriv_eq_iterate]; exact hsm.iterate_deriv n
  -- representation of `∂^k ℰ₁` as `|D|^p` of `h^{(k+1)}`
  have hrep : ∀ k : ℕ, k ≤ 1 → iteratedDeriv k (residual_decomposition_E1 p R ε) y =
      fracD p (iteratedDeriv (k + 1) h) y := by
    intro k hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · rw [iteratedDeriv_zero, hE y hy, zero_add, iteratedDeriv_one]
    · rw [iteratedDeriv_one, hdE y hy]
      have h2 : iteratedDeriv (1 + 1) h = deriv (deriv h) := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [h2]
      refine c04_aux_fracD_deriv p hp hp1 (deriv h) ?_ (K₀ * ε) (K₀ * ε) ?_ ?_ y
      · rw [← iteratedDeriv_one]; exact (hsmk 1).of_le (by simp)
      · intro z; rw [← iteratedDeriv_one]; exact hbnd 1 (by norm_num) z
      · intro z
        have := hbnd 2 (by norm_num) z
        rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  -- the core bound
  have hcore : ∀ k : ℕ, k ≤ 1 → |iteratedDeriv k (residual_decomposition_E1 p R ε) y| ≤
      (Cn + Cf) * (K₀ * ε) * y ^ (-2 * p - 1 - k) := by
    intro k hk
    rw [hrep k hk, c04_aux_frac_split p hp0 hp1 c04_aux_flat c04_aux_flat_isFlat
      (iteratedDeriv (k + 1) h) ((hsmk (k + 1)).of_le (by simp)) (K₀ * ε)
      (hbnd (k + 1) (by omega)) y]
    have hY : 0 ≤ y ^ (-2 * p - 1 - (k : ℝ)) := (rpow_pos_of_pos hy0 _).le
    have hsm3 : ContDiff ℝ 3 h := hsm.of_le (by simp)
    apply le_of_forall_pos_le_add
    intro η hη
    set K := K₀ * ε + η / ((Cn + Cf) * y ^ (-2 * p - 1 - (k : ℝ)) + 1) with hKdef
    have hKpos : 0 < K := by positivity
    have hKge : K₀ * ε ≤ K := by
      have : 0 ≤ η / ((Cn + Cf) * y ^ (-2 * p - 1 - (k : ℝ)) + 1) := by positivity
      simp only [hKdef]; linarith
    have hbK : ∀ l : ℕ, l ≤ 3 → ∀ z, |iteratedDeriv l h z| ≤ K * jb z ^ (-p - l) := by
      intro l hl z
      refine (hbl l hl z).trans ?_
      have : 0 ≤ jb z ^ (-p - (l : ℝ)) :=
        (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb z)) _).le
      exact mul_le_mul_of_nonneg_right hKge this
    have b1 := hnear c04_aux_flat c04_aux_flat_isFlat k hk K hKpos h hsm3 hbK y hy2
    have b2 := hfar k hk K hKpos h hsm3 hbK y hy2
    have hfrac : (Cn + Cf) * K * y ^ (-2 * p - 1 - (k : ℝ)) ≤
        (Cn + Cf) * (K₀ * ε) * y ^ (-2 * p - 1 - (k : ℝ)) + η := by
      set Y := y ^ (-2 * p - 1 - (k : ℝ)) with hYdef
      have hD : 0 < (Cn + Cf) * Y + 1 := by positivity
      have h1 : (Cn + Cf) * (η / ((Cn + Cf) * Y + 1)) * Y ≤ η := by
        have : (Cn + Cf) * (η / ((Cn + Cf) * Y + 1)) * Y = η * ((Cn + Cf) * Y / ((Cn + Cf) * Y + 1)) := by
          field_simp
        rw [this]
        have : (Cn + Cf) * Y / ((Cn + Cf) * Y + 1) ≤ 1 := by
          rw [div_le_one hD]; linarith
        calc η * ((Cn + Cf) * Y / ((Cn + Cf) * Y + 1)) ≤ η * 1 := by gcongr
          _ = η := mul_one η
      calc (Cn + Cf) * K * Y = (Cn + Cf) * (K₀ * ε) * Y + (Cn + Cf) * (η / ((Cn + Cf) * Y + 1)) * Y := by
            simp only [hKdef]; ring
        _ ≤ _ := by linarith
    calc _ ≤ |calpha p * ∫ z, c04_aux_flat ((y - z) / y) *
            (iteratedDeriv (k + 1) h y - iteratedDeriv (k + 1) h z) / |y - z| ^ (1 + p)| +
          |calpha p * ∫ z, (1 - c04_aux_flat ((y - z) / y)) *
            (iteratedDeriv (k + 1) h y - iteratedDeriv (k + 1) h z) / |y - z| ^ (1 + p)| := by
          exact abs_add_le _ _
      _ ≤ Cn * K * y ^ (-2 * p - 1 - (k : ℝ)) + Cf * K * y ^ (-2 * p - 1 - (k : ℝ)) :=
          add_le_add b1 b2
      _ = (Cn + Cf) * K * y ^ (-2 * p - 1 - (k : ℝ)) := by ring
      _ ≤ _ := hfrac
  -- conversion to `⟨y⟩`
  have hfin : |iteratedDeriv j (residual_decomposition_E1 p R ε) y| ≤
      (16 * (Cn + Cf) * K₀ + 1) * ε * jb y ^ (-2 * p - 1 - j) := by
    refine (hcore j hj).trans ?_
    have hjr : (j : ℝ) ≤ 1 := by exact_mod_cast hj
    have hconv := c04_aux_rpow_le_jb y (2 * p + 1 + j) (by linarith) (by positivity) (by linarith)
    rw [show -(2 * p + 1 + (j : ℝ)) = -2 * p - 1 - j by ring] at hconv
    have hJ : 0 ≤ jb y ^ (-2 * p - 1 - (j : ℝ)) :=
      (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
    have hA : 0 ≤ (Cn + Cf) * (K₀ * ε) := by positivity
    calc (Cn + Cf) * (K₀ * ε) * y ^ (-2 * p - 1 - (j : ℝ)) ≤
        (Cn + Cf) * (K₀ * ε) * (16 * jb y ^ (-2 * p - 1 - (j : ℝ))) :=
          mul_le_mul_of_nonneg_left hconv hA
      _ = (16 * (Cn + Cf) * K₀) * ε * jb y ^ (-2 * p - 1 - (j : ℝ)) := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hJ
          apply mul_le_mul_of_nonneg_right _ hε0
          linarith
  refine ⟨hfin, fun γ hγ => hfin.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply rpow_le_rpow_of_exponent_le (c04_aux_one_le_jb y)
  have : 0 ≤ (j : ℝ) / p := by positivity
  linarith

/-! ### Control of `ℰ₂`, `ℰ₃`, `ℰ₄` -/

/-- Derivative of `g(x) = (1+x)^p - 1 - px`. -/
theorem c04_aux_taylor_g_hasDeriv (p x : ℝ) (hx : 0 < 1 + x) :
    HasDerivAt (c04_taylor_g p) (p * (1 + x) ^ (p - 1) - p) x := by
  have h1 : HasDerivAt (fun x : ℝ => (1 + x) ^ p) (1 * p * (1 + x) ^ (p - 1)) x :=
    ((hasDerivAt_id' x).const_add 1).rpow_const (Or.inl hx.ne')
  have := (h1.sub_const 1).sub ((hasDerivAt_id' x).const_mul p)
  convert this using 1
  · ext t; simp [c04_taylor_g]
  · ring

/-- `|g'(x)| ≤ 4|x|` and `|g(x)| ≤ 4x²` for `|x| ≤ 1/2`. -/
theorem c04_aux_taylor_g_bounds (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |p * (1 + x) ^ (p - 1) - p| ≤ 4 * |x| ∧ |c04_taylor_g p x| ≤ 4 * x ^ 2 := by
  have hderb : ∀ w : ℝ, |w| ≤ 1 / 2 → |p * (1 + w) ^ (p - 1) - p| ≤ 4 * |w| := by
    intro w hw
    have hs : Convex ℝ (Icc (-1/2 : ℝ) (1/2)) := convex_Icc _ _
    have hmem : ∀ v ∈ Icc (-1/2 : ℝ) (1/2), 0 < 1 + v := fun v hv => by linarith [hv.1]
    have hd : ∀ v ∈ Icc (-1/2 : ℝ) (1/2), HasDerivAt (fun v : ℝ => (1 + v) ^ (p - 1))
        (1 * (p - 1) * (1 + v) ^ (p - 1 - 1)) v := fun v hv =>
      ((hasDerivAt_id' v).const_add 1).rpow_const (Or.inl (hmem v hv).ne')
    have hb : ∀ v ∈ Icc (-1/2 : ℝ) (1/2), ‖deriv (fun v : ℝ => (1 + v) ^ (p - 1)) v‖ ≤ 4 := by
      intro v hv
      rw [(hd v hv).deriv, Real.norm_eq_abs, one_mul, abs_mul, abs_of_neg (by linarith : p - 1 < 0),
        abs_of_pos (rpow_pos_of_pos (hmem v hv) _)]
      have h1 : (1 + v) ^ (p - 1 - 1) ≤ (1 / 2) ^ (p - 1 - 1) :=
        rpow_le_rpow_of_nonpos (by norm_num) (by linarith [hv.1]) (by linarith)
      have h2 : (1 / 2 : ℝ) ^ (p - 1 - 1) ≤ (1 / 2) ^ (-2 : ℝ) :=
        rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      have h3 : (1 / 2 : ℝ) ^ (-2 : ℝ) = 4 := by
        rw [rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
      have h4 : 0 ≤ (1 + v) ^ (p - 1 - 1) := (rpow_pos_of_pos (hmem v hv) _).le
      nlinarith
    have hwI : w ∈ Icc (-1/2 : ℝ) (1/2) := by rw [abs_le] at hw; exact ⟨by linarith [hw.1], hw.2⟩
    have := hs.norm_image_sub_le_of_norm_deriv_le (fun v hv => (hd v hv).differentiableAt) hb
      (show (0:ℝ) ∈ Icc (-1/2 : ℝ) (1/2) by norm_num) hwI
    simp only [add_zero, Real.one_rpow, Real.norm_eq_abs, sub_zero] at this
    have hp' : p * (1 + w) ^ (p - 1) - p = p * ((1 + w) ^ (p - 1) - 1) := by ring
    rw [hp', abs_mul, abs_of_pos hp0]
    have : |(1 + w) ^ (p - 1) - 1| ≤ 4 * |w| := this
    nlinarith [abs_nonneg ((1 + w) ^ (p - 1) - 1)]
  refine ⟨hderb x hx, ?_⟩
  have hs : Convex ℝ (uIcc (0 : ℝ) x) := convex_uIcc _ _
  have hin : ∀ v ∈ uIcc (0 : ℝ) x, |v| ≤ |x| := by
    intro v hv
    rcases mem_uIcc.mp hv with h | h
    · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2
    · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]; linarith [h.1]
  have hd : ∀ v ∈ uIcc (0 : ℝ) x, HasDerivAt (c04_taylor_g p) (p * (1 + v) ^ (p - 1) - p) v :=
    fun v hv => c04_aux_taylor_g_hasDeriv p v (by
      have := (abs_le.mp ((hin v hv).trans hx)).1; linarith)
  have hb : ∀ v ∈ uIcc (0 : ℝ) x, ‖deriv (c04_taylor_g p) v‖ ≤ 4 * |x| := by
    intro v hv
    rw [(hd v hv).deriv, Real.norm_eq_abs]
    exact (hderb v ((hin v hv).trans hx)).trans (by linarith [hin v hv])
  have := hs.norm_image_sub_le_of_norm_deriv_le (fun v hv => (hd v hv).differentiableAt) hb
    left_mem_uIcc right_mem_uIcc
  have hg0 : c04_taylor_g p 0 = 0 := by simp [c04_taylor_g]
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
  calc |c04_taylor_g p x| ≤ 4 * |x| * |x| := this
    _ = 4 * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- `μ ∈ B̄` gives `‖μ‖ ≤ 2‖μ_*‖`. -/
theorem c04_aux_Bbar_norm (p δ : ℝ) (hδμ : δ ≤ ‖mu_star p‖ / 2) (μ : ℂ) (hμ : μ ∈ Bbar p δ) :
    ‖μ‖ ≤ 2 * ‖mu_star p‖ := by
  have := norm_le_of_mem_closedBall hμ
  have : 0 ≤ ‖mu_star p‖ := norm_nonneg _
  linarith

/-- The algebraic identities of lem:c04_lambda_taylor at a point where `λ = λ₀(1+λ̃)`, `1+λ̃>0`. -/
theorem c04_aux_lambda_ids (p ε : ℝ) (μ : ℂ) (y : ℝ) (hp0 : 0 < p) (hy : 0 < y)
    (hlam : fam_lambda p ε μ y = lambda0 p y * (1 + lambda_tilde p ε μ y))
    (hpos : 0 < 1 + lambda_tilde p ε μ y) :
    fam_lambda p ε μ y ^ p - y - p * lambda0 p y ^ (p - 1) * c_log p ε μ / y +
        c_eps p ε * y ^ (-p) = y * c04_taylor_g p (lambda_tilde p ε μ y) ∧
    fam_lambda p ε μ y ^ p - y + c_eps p ε * y ^ (-p) =
        p * c_log p ε μ * y ^ (-1 / p) + y * c04_taylor_g p (lambda_tilde p ε μ y) := by
  set L := lambda_tilde p ε μ y with hLdef
  have hl0 : lambda0 p y = y ^ (1 / p) := rfl
  have hpow : fam_lambda p ε μ y ^ p = y * (1 + L) ^ p := by
    rw [hlam, hl0, mul_rpow (rpow_nonneg hy.le _) hpos.le, ← rpow_mul hy.le,
      one_div_mul_cancel hp0.ne', rpow_one]
  have hl0p : p * lambda0 p y ^ (p - 1) * c_log p ε μ / y = p * c_log p ε μ * y ^ (-1 / p) := by
    rw [hl0, ← rpow_mul hy.le]
    have : 1 / p * (p - 1) = -1 / p + 1 := by field_simp; ring
    rw [this, rpow_add_one hy.ne']; field_simp
  have e1 : y * y ^ (-p - 1) = y ^ (-p) := by
    rw [show -p = (-p - 1) + 1 by ring, rpow_add_one hy.ne']; ring_nf
  have e2 : y * y ^ (-1 - 1 / p) = y ^ (-1 / p) := by
    rw [show -1 / p = (-1 - 1 / p) + 1 by ring, rpow_add_one hy.ne']; ring
  have hyL : y * L = -(c_eps p ε / p) * y ^ (-p) + c_log p ε μ * y ^ (-1 / p) := by
    simp only [hLdef, lambda_tilde]
    rw [← e1, ← e2]; ring
  have hexp : y * c04_taylor_g p L = y * (1 + L) ^ p - y - p * (y * L) := by
    unfold c04_taylor_g; ring
  constructor
  · rw [hpow, hl0p, hexp, hyL]; field_simp; ring
  · rw [hpow, hexp, hyL]; field_simp; ring

/-- Blueprint: lem:c04_lambda_taylor.  With `g(x) = (1+x)^p - 1 - px`, for `y ≥ R`:
`λ^p - y - pλ₀^{p-1}c_log/y + c_ε y^{-p} = y g(λ̃)`, `λ^p - y + c_ε y^{-p} = p c_log y^{-1/p} + y g(λ̃)`,
`|y g(λ̃)| ≤ Cε²y^{-2p-1}`, `|∂_y(y g(λ̃))| ≤ Cε²y^{-2p-2}`,
`|∂^k(λ^p - y + c_ε y^{-p})| ≤ Cεy^{-1/p-k}` (`k = 0,1`). -/
theorem c04_lambda_taylor (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        fam_lambda p ε μ y ^ p - y - p * lambda0 p y ^ (p - 1) * c_log p ε μ / y +
            c_eps p ε * y ^ (-p) = y * c04_taylor_g p (lambda_tilde p ε μ y) ∧
        fam_lambda p ε μ y ^ p - y + c_eps p ε * y ^ (-p) =
          p * c_log p ε μ * y ^ (-1 / p) + y * c04_taylor_g p (lambda_tilde p ε μ y)) ∧
      (∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        |y * c04_taylor_g p (lambda_tilde p ε μ y)| ≤ C * ε ^ 2 * y ^ (-2 * p - 1) ∧
        |deriv (fun t => t * c04_taylor_g p (lambda_tilde p ε μ t)) y| ≤
          C * ε ^ 2 * y ^ (-2 * p - 2) ∧
        ∀ k : ℕ, k ≤ 1 →
          |iteratedDeriv k (fun t => fam_lambda p ε μ t ^ p - t + c_eps p ε * t ^ (-p)) y| ≤
            C * ε * y ^ (-1 / p - k)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  obtain ⟨ε₀, hε₀, R₀, hR₀, hbasic, -, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  have hμs : 0 < ‖mu_star p‖ := by linarith
  obtain ⟨⟨Cc, hCc, hcs⟩, -, -, hcs4⟩ := c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)
  obtain ⟨C0, hC0, hl0⟩ := hcs4 0
  obtain ⟨C1, hC1, hl1⟩ := hcs4 1
  -- pointwise structure for `t > R/2`
  have pt : ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ t > R / 2,
      fam_lambda p ε μ t = lambda0 p t * (1 + lambda_tilde p ε μ t) ∧
        0 < 1 + lambda_tilde p ε μ t ∧ |lambda_tilde p ε μ t| ≤ 1 / 2 := by
    intro R hR ε hε μ hμ t ht
    obtain ⟨h1, h2, h3, -⟩ := hbasic R hR ε hε μ hμ t ht
    have ht0 : 0 < t := by linarith
    have hl : 0 < lambda0 p t := rpow_pos_of_pos ht0 _
    have hl' : lambda0 p t = t ^ (1 / p) := rfl
    rw [h1, ← hl'] at h2 h3
    have a1 : 1 / 2 ≤ 1 + lambda_tilde p ε μ t := by
      by_contra hc; push Not at hc; nlinarith
    have a2 : 1 + lambda_tilde p ε μ t ≤ 3 / 2 := by
      by_contra hc; push Not at hc; nlinarith
    exact ⟨h1, by linarith, by rw [abs_le]; constructor <;> linarith⟩
  refine ⟨ε₀, hε₀, R₀, hR₀, fun R hR ε hε μ hμ y hy => ?_, ?_⟩
  · have hy' : y > R / 2 := by linarith
    obtain ⟨h1, h2, -⟩ := pt R hR ε hε μ hμ y hy'
    exact c04_aux_lambda_ids p ε μ y hp0 (by linarith) h1 h2
  -- the bounds
  refine ⟨8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1, by positivity,
    fun R hR ε hε μ hμ y hy => ?_⟩
  have hR2 : 2 ≤ R := le_trans hR₀ hR
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hε₀.2⟩
  have hε0 := hε.1
  have hμK := c04_aux_Bbar_norm p δ hδμ μ hμ
  set L := lambda_tilde p ε μ with hLdef
  -- bounds on `λ̃`, `λ̃'` at any `t ≥ 1`
  have hLb : ∀ t ≥ (1 : ℝ), |L t| ≤ C0 * ε * t ^ (-p - 1) := fun t ht => by
    have := hl0 ε hε1 μ hμK t ht
    simpa using this
  have hLd : ∀ t > (0 : ℝ), DifferentiableAt ℝ L t := fun t ht => by
    simp only [hLdef]
    exact ((differentiableAt_id.rpow_const (Or.inl ht.ne')).const_mul _).add
      ((differentiableAt_id.rpow_const (Or.inl ht.ne')).const_mul _)
  have hL'b : |deriv L y| ≤ C1 * ε * y ^ (-p - 2) := by
    have := hl1 ε hε1 μ hμK y hy1
    rw [iteratedDeriv_one] at this
    convert this using 3; push_cast; ring
  obtain ⟨-, hpos, habs⟩ := pt R hR ε hε μ hμ y (by linarith)
  have hgb := c04_aux_taylor_g_bounds p hp0 hp1 (L y) habs
  -- `|λ̃|² ≤ C0² ε² y^{-2p-2}`
  have hsq : L y ^ 2 ≤ C0 ^ 2 * ε ^ 2 * y ^ (-2 * p - 2) := by
    have h := hLb y hy1
    have : L y ^ 2 ≤ (C0 * ε * y ^ (-p - 1)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    refine this.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, ← rpow_mul_natCast hy0.le]; congr 2; push_cast; ring
  have hpw1 : y * y ^ (-2 * p - 2) = y ^ (-2 * p - 1) := by
    rw [show -2 * p - 1 = (-2 * p - 2) + 1 by ring, rpow_add_one hy0.ne']; ring
  have hpw2 : y * y ^ (-p - 1) * y ^ (-p - 2) = y ^ (-2 * p - 2) := by
    rw [mul_assoc, ← rpow_add hy0, show -2 * p - 2 = (-p - 1 + (-p - 2)) + 1 by ring,
      rpow_add_one hy0.ne']; ring
  -- (i)
  have hb1 : |y * c04_taylor_g p (L y)| ≤ 4 * C0 ^ 2 * ε ^ 2 * y ^ (-2 * p - 1) := by
    rw [abs_mul, abs_of_pos hy0, ← hpw1]
    have := hgb.2
    have : |c04_taylor_g p (L y)| ≤ 4 * (C0 ^ 2 * ε ^ 2 * y ^ (-2 * p - 2)) := by linarith
    calc y * |c04_taylor_g p (L y)| ≤ y * (4 * (C0 ^ 2 * ε ^ 2 * y ^ (-2 * p - 2))) := by gcongr
      _ = _ := by ring
  -- (ii)
  have hgd := c04_aux_taylor_g_hasDeriv p (L y) hpos
  have hTd : HasDerivAt (fun t => t * c04_taylor_g p (L t))
      (1 * c04_taylor_g p (L y) + y * ((p * (1 + L y) ^ (p - 1) - p) * deriv L y)) y :=
    (hasDerivAt_id' y).mul (hgd.comp y (hLd y hy0).hasDerivAt)
  have hb2 : |deriv (fun t => t * c04_taylor_g p (L t)) y| ≤
      (4 * C0 ^ 2 + 4 * C0 * C1) * ε ^ 2 * y ^ (-2 * p - 2) := by
    rw [hTd.deriv, one_mul]
    have hA : |c04_taylor_g p (L y)| ≤ 4 * C0 ^ 2 * ε ^ 2 * y ^ (-2 * p - 2) := by
      linarith [hgb.2]
    have hB : |y * ((p * (1 + L y) ^ (p - 1) - p) * deriv L y)| ≤
        4 * C0 * C1 * ε ^ 2 * y ^ (-2 * p - 2) := by
      rw [abs_mul, abs_mul, abs_of_pos hy0, ← hpw2]
      have hq : |p * (1 + L y) ^ (p - 1) - p| ≤ 4 * (C0 * ε * y ^ (-p - 1)) :=
        hgb.1.trans (by linarith [hLb y hy1])
      have hn1 : 0 ≤ C0 * ε * y ^ (-p - 1) := by positivity
      calc y * (|p * (1 + L y) ^ (p - 1) - p| * |deriv L y|)
          ≤ y * ((4 * (C0 * ε * y ^ (-p - 1))) * (C1 * ε * y ^ (-p - 2))) := by
            gcongr
        _ = _ := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hA hB
      _ = _ := by ring
  have hεsq : ε ^ 2 ≤ ε := by nlinarith [hε1.2]
  have hCpos : 0 ≤ 4 * C0 ^ 2 + 4 * C0 * C1 := by positivity
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · refine hb1.trans ?_
    have : 0 ≤ y ^ (-2 * p - 1) := by positivity
    have h4 : 4 * C0 ^ 2 ≤ 8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1 := by
      have : 0 ≤ C0 * C1 := by positivity
      have := sq_nonneg C0; linarith
    calc 4 * C0 ^ 2 * ε ^ 2 * y ^ (-2 * p - 1) ≤
        (8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1) * ε ^ 2 * y ^ (-2 * p - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (sq_nonneg ε)) this
      _ = _ := by ring
  · refine hb2.trans ?_
    have : 0 ≤ y ^ (-2 * p - 2) := by positivity
    have h4 : 4 * C0 ^ 2 + 4 * C0 * C1 ≤ 8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1 := by
      have := sq_nonneg C0; linarith
    calc (4 * C0 ^ 2 + 4 * C0 * C1) * ε ^ 2 * y ^ (-2 * p - 2) ≤
        (8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1) * ε ^ 2 * y ^ (-2 * p - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (sq_nonneg ε)) this
      _ = _ := by ring
  · -- `λ^p - t + c_ε t^{-p} = p c_log t^{-1/p} + t g(λ̃)` near `y`
    have hev : (fun t => fam_lambda p ε μ t ^ p - t + c_eps p ε * t ^ (-p)) =ᶠ[𝓝 y]
        fun t => p * c_log p ε μ * t ^ (-1 / p) + t * c04_taylor_g p (L t) := by
      filter_upwards [Ioi_mem_nhds (show R / 2 < y by linarith)] with t ht
      obtain ⟨h1, h2, -⟩ := pt R hR ε hε μ hμ t ht
      exact (c04_aux_lambda_ids p ε μ t hp0 (by linarith [mem_Ioi.mp ht]) h1 h2).2
    have hcl := (hcs ε hε1 μ hμK).2.2.2.1
    have hexp1 : y ^ (-2 * p - 1) ≤ y ^ (-1 / p) := by
      apply rpow_le_rpow_of_exponent_le hy1
      have : 1 / p ≤ 2 * p + 1 := by rw [div_le_iff₀ hp0]; nlinarith
      have : -1 / p = -(1 / p) := by ring
      linarith
    have hexp2 : y ^ (-2 * p - 2) ≤ y ^ (-1 / p - 1) := by
      apply rpow_le_rpow_of_exponent_le hy1
      have : 1 / p ≤ 2 * p + 1 := by rw [div_le_iff₀ hp0]; nlinarith
      have : -1 / p = -(1 / p) := by ring
      linarith
    have hCtot : Cc + (4 * C0 ^ 2 + 4 * C0 * C1) ≤ 8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1 := by
      have := sq_nonneg C0; linarith
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · rw [iteratedDeriv_zero, hev.eq_of_nhds]
      simp only [Nat.cast_zero, sub_zero]
      have hq : |p * c_log p ε μ * y ^ (-1 / p)| ≤ Cc * ε * y ^ (-1 / p) := by
        rw [abs_mul, abs_mul, abs_of_pos hp0, abs_of_pos (rpow_pos_of_pos hy0 _)]
        have : p * |c_log p ε μ| ≤ Cc * ε :=
          (mul_le_mul_of_nonneg_right hp1.le (abs_nonneg _)).trans (by rw [one_mul]; exact hcl)
        exact mul_le_mul_of_nonneg_right this (rpow_pos_of_pos hy0 _).le
      have h2 : 4 * C0 ^ 2 * ε ^ 2 * y ^ (-2 * p - 1) ≤ 4 * C0 ^ 2 * ε * y ^ (-1 / p) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hεsq (by positivity)) hexp1 (by positivity)
          (by positivity)
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ Cc * ε * y ^ (-1 / p) + 4 * C0 ^ 2 * ε * y ^ (-1 / p) := add_le_add hq (hb1.trans h2)
        _ = (Cc + 4 * C0 ^ 2) * (ε * y ^ (-1 / p)) := by ring
        _ ≤ (8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1) * (ε * y ^ (-1 / p)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ C0 * C1 := by positivity
          linarith
        _ = _ := by ring
    · rw [iteratedDeriv_one, hev.deriv_eq]
      have hQ : HasDerivAt (fun t => p * c_log p ε μ * t ^ (-1 / p))
          (p * c_log p ε μ * ((-1 / p) * y ^ (-1 / p - 1))) y :=
        (hasDerivAt_rpow_const (Or.inl hy0.ne')).const_mul _
      have hTd' : DifferentiableAt ℝ (fun t => t * c04_taylor_g p (L t)) y :=
        hTd.differentiableAt
      rw [deriv_fun_add hQ.differentiableAt hTd', hQ.deriv]
      have hq : |p * c_log p ε μ * ((-1 / p) * y ^ (-1 / p - 1))| ≤ Cc * ε * y ^ (-1 / p - 1) := by
        have : p * c_log p ε μ * ((-1 / p) * y ^ (-1 / p - 1)) = -(c_log p ε μ * y ^ (-1 / p - 1)) := by
          field_simp
        rw [this, abs_neg, abs_mul, abs_of_pos (rpow_pos_of_pos hy0 _)]
        exact mul_le_mul_of_nonneg_right hcl (rpow_pos_of_pos hy0 _).le
      have h2 : (4 * C0 ^ 2 + 4 * C0 * C1) * ε ^ 2 * y ^ (-2 * p - 2) ≤
          (4 * C0 ^ 2 + 4 * C0 * C1) * ε * y ^ (-1 / p - 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hεsq hCpos) hexp2 (by positivity) (by positivity)
      simp only [Nat.cast_one]
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ Cc * ε * y ^ (-1 / p - 1) + (4 * C0 ^ 2 + 4 * C0 * C1) * ε * y ^ (-1 / p - 1) :=
          add_le_add hq (hb2.trans h2)
        _ = (Cc + (4 * C0 ^ 2 + 4 * C0 * C1)) * (ε * y ^ (-1 / p - 1)) := by ring
        _ ≤ (8 * C0 ^ 2 + 4 * C0 * C1 + 2 * Cc + 1) * (ε * y ^ (-1 / p - 1)) :=
          mul_le_mul_of_nonneg_right hCtot (by positivity)
        _ = _ := by ring

/-- `y^e ≤ 32 ⟨y⟩^e` for `y ≥ 1`, `-5 ≤ e ≤ 0`. -/
theorem c04_aux_rpow_le_jb32 (y e : ℝ) (hy : 1 ≤ y) (he : e ≤ 0) (he5 : -5 ≤ e) :
    y ^ e ≤ 32 * jb y ^ e := by
  have := c04_aux_rpow_le_jb' y (-e) hy (by linarith)
  rw [neg_neg] at this
  have h2 : (2 : ℝ) ^ (-e) ≤ 2 ^ (5 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (5 : ℝ) = 32 := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num
  have hJ : 0 ≤ jb y ^ e := (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
  calc y ^ e ≤ 2 ^ (-e) * jb y ^ e := this
    _ ≤ 32 * jb y ^ e := by rw [← h3]; exact mul_le_mul_of_nonneg_right h2 hJ

/-- Blueprint: prop:approx_E2.  `|∂^j ℰ₂(y)| ≤ C ε² ⟨y⟩^{-2p-1-β+j/p}` for `y ≥ 2R`, `j = 0,1`. -/
theorem approx_E2 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ 2 * R, ∀ j : ℕ, j ≤ 1 →
        |iteratedDeriv j (residual_decomposition_E2 p R ε μ) y| ≤
          C * ε ^ 2 * jb y ^ (-2 * p - 1 - beta p + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hid, Ct, hCt, hbt⟩ := c04_lambda_taylor p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hZb, -⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨CZ0, hCZ0, hZ0⟩ := hZb 0 1 one_pos
  obtain ⟨CZ1, hCZ1, hZ1⟩ := hZb 1 1 one_pos
  obtain ⟨ε₃, hε₃, R₃, hR₃, hbasic, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  have hβ : 0 < beta p := by unfold beta; positivity
  have hβ2 : beta p < 2 := by
    unfold beta; rw [div_lt_iff₀ (by positivity)]; linarith
  set B := 2 * Ct * (CZ0 + CZ1) with hBdef
  have hε₀ : min (min ε₁ ε₂) ε₃ ∈ Ioc (0 : ℝ) 1 := ⟨lt_min (lt_min hε₁.1 hε₂.1) hε₃.1,
      (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)⟩
  have hR₀ : max (max R₁ R₂) R₃ ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _))
  have hCpos : (0 : ℝ) < 32 * B + 1 := by
    have : 0 ≤ B := by rw [hBdef]; positivity
    linarith
  refine ⟨min (min ε₁ ε₂) ε₃, hε₀, max (max R₁ R₂) R₃, hR₀, 32 * B + 1, hCpos, ?_⟩
  intro R hR ε hε μ hμ y hy j hj
  have hRa : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hRb : R ≥ R₂ := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hRc : R ≥ R₃ := le_trans (le_max_right _ _) hR
  have hεa : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hεb : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hεc : ε ∈ Icc (0 : ℝ) ε₃ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hR2 : 2 ≤ R := le_trans hR₁ hRa
  have hR0 : 0 < R := by linarith
  have hyR : y ≥ R := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  set L := lambda_tilde p ε μ with hLdef
  set Tf : ℝ → ℝ := fun t => t * c04_taylor_g p (L t) with hTf
  set Z := fam_Z p R ε μ with hZdef
  obtain ⟨b1, b2, -⟩ := hbt R hRa ε hεa μ hμ y hyR
  obtain ⟨h1, h2, -, -⟩ := hbasic R hRc ε hεc μ hμ y (by linarith)
  obtain ⟨hlpos, hLpos⟩ := c04_aux_lam_pos p ε μ y hy0 h1 h2
  have hev : residual_decomposition_E2 p R ε μ =ᶠ[𝓝 y] fun t => 2 * Tf t * (Z t).re := by
    filter_upwards [Ioi_mem_nhds (show R < y by linarith)] with t ht
    unfold residual_decomposition_E2
    rw [(hid R hRa ε hεa μ hμ t (le_of_lt ht)).1]
  have hLd : DifferentiableAt ℝ L y := by
    simp only [hLdef]
    exact ((differentiableAt_id.rpow_const (Or.inl hy0.ne')).const_mul _).add
      ((differentiableAt_id.rpow_const (Or.inl hy0.ne')).const_mul _)
  have hTd : DifferentiableAt ℝ Tf y :=
    ((hasDerivAt_id' y).mul ((c04_aux_taylor_g_hasDeriv p (L y) hLpos).comp y
      hLd.hasDerivAt)).differentiableAt
  have hZd : DifferentiableAt ℝ Z y := c04_aux_famZ_diff p R ε μ hp0 hR0 hplus hμs y hy0 hlpos
  have hZre : HasDerivAt (fun t => (Z t).re) (deriv Z y).re y :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hZd.hasDerivAt
  have hz0 : ‖Z y‖ ≤ CZ0 * y ^ (-beta p) := by
    have := (hZ0 R hRb ε hεb μ hμ y hyR).1; simpa using this
  have hz1 : ‖deriv Z y‖ ≤ CZ1 * y ^ (-beta p + 1 / p) := by
    have := (hZ1 R hRb ε hεb μ hμ y hyR).1; simpa using this
  have hre0 := Complex.abs_re_le_norm (Z y)
  have hre1 := Complex.abs_re_le_norm (deriv Z y)
  have hε0 := hε.1
  have hE2 : ε ^ 2 * y ^ (-2 * p - 1) * y ^ (-beta p) = ε ^ 2 * y ^ (-2 * p - 1 - beta p) := by
    rw [mul_assoc, ← rpow_add hy0]; ring_nf
  -- the bound `B ε² y^{e_j}`
  have hmain : |iteratedDeriv j (residual_decomposition_E2 p R ε μ) y| ≤
      B * ε ^ 2 * y ^ (-2 * p - 1 - beta p + j / p) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · rw [iteratedDeriv_zero, hev.eq_of_nhds]
      simp only [Nat.cast_zero, zero_div, add_zero]
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |Tf y| * |(Z y).re| ≤ 2 * (Ct * ε ^ 2 * y ^ (-2 * p - 1)) * (CZ0 * y ^ (-beta p)) := by
            gcongr; exact hre0.trans hz0
        _ = 2 * Ct * CZ0 * (ε ^ 2 * y ^ (-2 * p - 1) * y ^ (-beta p)) := by ring
        _ = 2 * Ct * CZ0 * (ε ^ 2 * y ^ (-2 * p - 1 - beta p)) := by rw [hE2]
        _ ≤ B * ε ^ 2 * y ^ (-2 * p - 1 - beta p) := by
            have : 0 ≤ ε ^ 2 * y ^ (-2 * p - 1 - beta p) := by positivity
            rw [hBdef, show 2 * Ct * (CZ0 + CZ1) * ε ^ 2 * y ^ (-2 * p - 1 - beta p) =
              (2 * Ct * (CZ0 + CZ1)) * (ε ^ 2 * y ^ (-2 * p - 1 - beta p)) by ring]
            exact mul_le_mul_of_nonneg_right (by have := mul_pos hCt hCZ1; nlinarith) this
    · rw [iteratedDeriv_one, hev.deriv_eq]
      have hd : HasDerivAt (fun t => 2 * Tf t * (Z t).re)
          (2 * deriv Tf y * (Z y).re + 2 * Tf y * (deriv Z y).re) y :=
        (hTd.hasDerivAt.const_mul 2).mul hZre
      rw [hd.deriv]
      simp only [Nat.cast_one]
      have e1 : y ^ (-2 * p - 2) * y ^ (-beta p) ≤ y ^ (-2 * p - 1 - beta p + 1 / p) := by
        rw [← rpow_add hy0]
        apply rpow_le_rpow_of_exponent_le hy1
        have : 0 < 1 / p := by positivity
        linarith
      have e2 : y ^ (-2 * p - 1) * y ^ (-beta p + 1 / p) = y ^ (-2 * p - 1 - beta p + 1 / p) := by
        rw [← rpow_add hy0]; ring_nf
      have hY : 0 ≤ y ^ (-2 * p - 1 - beta p + 1 / p) := by positivity
      have hε2 : 0 ≤ ε ^ 2 := by positivity
      calc |2 * deriv Tf y * (Z y).re + 2 * Tf y * (deriv Z y).re|
          ≤ 2 * |deriv Tf y| * |(Z y).re| + 2 * |Tf y| * |(deriv Z y).re| := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
        _ ≤ 2 * (Ct * ε ^ 2 * y ^ (-2 * p - 2)) * (CZ0 * y ^ (-beta p)) +
            2 * (Ct * ε ^ 2 * y ^ (-2 * p - 1)) * (CZ1 * y ^ (-beta p + 1 / p)) := by
            gcongr
            · exact hre0.trans hz0
            · exact hre1.trans hz1
        _ = 2 * Ct * CZ0 * ε ^ 2 * (y ^ (-2 * p - 2) * y ^ (-beta p)) +
            2 * Ct * CZ1 * ε ^ 2 * (y ^ (-2 * p - 1) * y ^ (-beta p + 1 / p)) := by ring
        _ ≤ 2 * Ct * CZ0 * ε ^ 2 * y ^ (-2 * p - 1 - beta p + 1 / p) +
            2 * Ct * CZ1 * ε ^ 2 * y ^ (-2 * p - 1 - beta p + 1 / p) := by
            rw [e2]; gcongr
        _ = B * ε ^ 2 * y ^ (-2 * p - 1 - beta p + 1 / p) := by rw [hBdef]; ring
  refine hmain.trans ?_
  have hjr : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hconv := c04_aux_rpow_le_jb32 y (-2 * p - 1 - beta p + j / p) hy1
    (by
      have : (j : ℝ) / p ≤ 1 / p := by gcongr
      have : 1 / p ≤ 4 / 3 := by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
      linarith)
    (by have : 0 ≤ (j : ℝ) / p := by positivity
        linarith)
  have hJ : 0 ≤ jb y ^ (-2 * p - 1 - beta p + j / p) :=
    (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
  have hB : 0 ≤ B := by positivity
  calc B * ε ^ 2 * y ^ (-2 * p - 1 - beta p + j / p) ≤ B * ε ^ 2 * (32 * jb y ^ (-2 * p - 1 - beta p + j / p)) :=
        mul_le_mul_of_nonneg_left hconv (by positivity)
    _ = (32 * B) * ε ^ 2 * jb y ^ (-2 * p - 1 - beta p + j / p) := by ring
    _ ≤ (32 * B + 1) * ε ^ 2 * jb y ^ (-2 * p - 1 - beta p + j / p) := by
        apply mul_le_mul_of_nonneg_right _ hJ
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

/-- The algebraic identity of lem:c04_E3_cancellation at a point with `λ > 0`. -/
theorem c04_aux_E3_id (p R ε : ℝ) (μ : ℂ) (y : ℝ) (hp0 : 0 < p) (hy : 0 < y)
    (hlpos : 0 < fam_lambda p ε μ y) :
    residual_decomposition_E3 p R ε μ y =
      2 * n_eps p ε * ‖μ‖ ^ 2 * (‖astar p y‖ ^ 2 / fam_lambda p ε μ y - 1 / lambda0 p y) *
        (fam_Z p R ε μ y).re := by
  set L := fam_lambda p ε μ y with hL
  have hZn : ‖fam_Z p R ε μ y‖ ^ 2 = ‖μ‖ ^ 2 * ‖astar p y‖ ^ 2 * L ^ (-(p + 1)) := by
    unfold fam_Z
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, c04_aux_norm_exp_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hlpos _)]
    rw [mul_pow, mul_pow, ← rpow_mul_natCast hlpos.le]
    congr 2; push_cast; ring
  have hlp : L ^ p * L ^ (-(p + 1)) = 1 / L := by
    rw [← rpow_add hlpos, show p + -(p + 1) = -1 by ring, rpow_neg_one, one_div]
  have hl0 : lambda0 p y = y ^ (1 / p) := rfl
  have hl0p : p * lambda0 p y ^ (p - 1) * c_log p ε μ / y = -(n_eps p ε * ‖μ‖ ^ 2) * (1 / lambda0 p y) := by
    rw [hl0, ← rpow_mul hy.le]
    have e : 1 / p * (p - 1) = -(1 / p) + 1 := by field_simp; ring
    rw [e, rpow_add_one hy.ne', rpow_neg hy.le]
    unfold c_log
    field_simp
  unfold residual_decomposition_E3
  rw [hZn, hl0p]
  have e2 : n_eps p ε * L ^ p * (‖μ‖ ^ 2 * ‖astar p y‖ ^ 2 * L ^ (-(p + 1))) =
      n_eps p ε * ‖μ‖ ^ 2 * ‖astar p y‖ ^ 2 * (L ^ p * L ^ (-(p + 1))) := by ring
  rw [e2, hlp]; ring


/-- Derivative of `‖a‖²`. -/
theorem c04_aux_normsq_hasDeriv (a : ℝ → ℂ) (y : ℝ) (ha : DifferentiableAt ℝ a y) :
    HasDerivAt (fun t => ‖a t‖ ^ 2)
      (2 * ((a y).re * (deriv a y).re + (a y).im * (deriv a y).im)) y := by
  have h1 : HasDerivAt (fun t => (a t).re) (deriv a y).re y :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt y ha.hasDerivAt
  have h2 : HasDerivAt (fun t => (a t).im) (deriv a y).im y :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt y ha.hasDerivAt
  have e : (fun t => ‖a t‖ ^ 2) = fun t => (a t).re * (a t).re + (a t).im * (a t).im := by
    funext t; rw [Complex.sq_norm, Complex.normSq_apply]
  rw [e]
  convert (h1.mul h1).add (h2.mul h2) using 1; ring

/-- Pointwise bounds of lem:c04_E3_cancellation from the elementary inputs. -/
theorem c04_aux_E3_bound (p ε Ca Cl Cd : ℝ) (hp0 : 0 < p) (hε : 0 ≤ ε) (hCa : 0 ≤ Ca)
    (hCl : 0 ≤ Cl) (hCd : 0 ≤ Cd) (a : ℝ → ℂ) (L : ℝ → ℝ) (y : ℝ) (hy : 1 ≤ y)
    (had : DifferentiableAt ℝ a y) (hLd : DifferentiableAt ℝ L y)
    (hLlow : y ^ (1 / p) / 2 ≤ L y) (hLup : L y ≤ 3 / 2 * y ^ (1 / p))
    (ha2 : ‖a y‖ ≤ 2) (ha1 : ‖a y - 1‖ ≤ Ca * y ^ (-2 * beta p))
    (ha' : ‖deriv a y‖ ≤ Ca * y ^ (-2 * beta p - 1))
    (hL' : |deriv L y| ≤ Cl * y ^ (1 / p - 1))
    (hd0 : |L y - lambda0 p y| ≤ Cd * ε * y ^ (1 / p - p - 1))
    (hd1 : |deriv L y - deriv (lambda0 p) y| ≤ Cd * ε * y ^ (1 / p - p - 2)) :
    ∀ k : ℕ, k ≤ 1 → |iteratedDeriv k (fun t => ‖a t‖ ^ 2 / L t - 1 / lambda0 p t) y| ≤
      (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * y ^ (-1 / p - k) *
        (y ^ (-2 * beta p) + ε * y ^ (-p - 1)) := by
  have hy0 : 0 < y := by linarith
  set s := y ^ (1 / p) with hs
  set ys := y ^ (-1 / p) with hys
  set E1 := y ^ (-2 * beta p) with hE1
  set E2 := y ^ (-p - 1) with hE2
  have hspos : 0 < s := rpow_pos_of_pos hy0 _
  have hyspos : 0 < ys := rpow_pos_of_pos hy0 _
  have hE1p : 0 ≤ E1 := (rpow_pos_of_pos hy0 _).le
  have hE2p : 0 ≤ E2 := (rpow_pos_of_pos hy0 _).le
  have hyi : 0 < y⁻¹ := inv_pos.mpr hy0
  have hsys : s * ys = 1 := by
    rw [hs, hys, ← rpow_add hy0]; ring_nf; exact rpow_zero y
  have r1 : y ^ (1 / p - p - 1) = s * E2 := by rw [hs, hE2, ← rpow_add hy0]; ring_nf
  have r2 : y ^ (-2 * beta p - 1) = E1 * y⁻¹ := by
    rw [hE1, ← rpow_neg_one, ← rpow_add hy0]; ring_nf
  have r3 : y ^ (1 / p - 1) = s * y⁻¹ := by rw [hs, ← rpow_neg_one, ← rpow_add hy0]; ring_nf
  have r4 : y ^ (1 / p - p - 2) = s * E2 * y⁻¹ := by
    rw [hs, hE2, ← rpow_neg_one, ← rpow_add hy0, ← rpow_add hy0]; ring_nf
  have hL0 : lambda0 p y = s := rfl
  have hL0d : HasDerivAt (lambda0 p) (1 / p * (s * y⁻¹)) y := by
    rw [← r3]; exact hasDerivAt_rpow_const (Or.inl hy0.ne')
  have hLpos : 0 < L y := lt_of_lt_of_le (by positivity) hLlow
  have hiL : 1 / L y ≤ 2 * ys := by
    rw [div_le_iff₀ hLpos]
    have : 2 * ys * L y ≥ 2 * ys * (s / 2) := by gcongr
    nlinarith
  have hiLp : 0 ≤ 1 / L y := by positivity
  have hiL0 : 1 / lambda0 p y = ys := by
    rw [hL0]; field_simp; linarith [hsys]
  -- `|‖a‖² - 1| ≤ 3 Ca E1`
  have hA1 : |‖a y‖ ^ 2 - 1| ≤ 3 * Ca * E1 := by
    have h1 : |‖a y‖ - 1| ≤ ‖a y - 1‖ := by
      have := abs_norm_sub_norm_le (a y) 1; simpa using this
    have e : ‖a y‖ ^ 2 - 1 = (‖a y‖ - 1) * (‖a y‖ + 1) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖a y‖ + 1)]
    calc |‖a y‖ - 1| * (‖a y‖ + 1) ≤ (Ca * E1) * 3 :=
          mul_le_mul (h1.trans ha1) (by linarith) (by positivity) (by positivity)
      _ = 3 * Ca * E1 := by ring
  have hAd := c04_aux_normsq_hasDeriv a y had
  have hA' : |2 * ((a y).re * (deriv a y).re + (a y).im * (deriv a y).im)| ≤ 4 * Ca * E1 * y⁻¹ := by
    have e : (a y).re * (deriv a y).re + (a y).im * (deriv a y).im =
        ((starRingEnd ℂ) (a y) * deriv a y).re := by
      simp [Complex.mul_re]
    rw [e, abs_mul, abs_two]
    have h := Complex.abs_re_le_norm ((starRingEnd ℂ) (a y) * deriv a y)
    rw [norm_mul, Complex.norm_conj] at h
    have : ‖a y‖ * ‖deriv a y‖ ≤ 2 * (Ca * (E1 * y⁻¹)) :=
      mul_le_mul ha2 (by rw [← r2]; exact ha') (norm_nonneg _) (by norm_num)
    nlinarith
  have hCaCl := mul_nonneg hCa hCl
  have hCdp := div_nonneg hCd hp0.le
  have hεE2 : 0 ≤ ε * E2 := mul_nonneg hε hE2p
  have hX1 : 0 ≤ 12 * Ca * Cl := by positivity
  have hX2 : 0 ≤ 10 * Cd / p := by positivity
  have hfin : ∀ c1 c2 : ℝ, c1 ≤ (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) → c2 ≤ (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) →
      c1 * E1 + c2 * (ε * E2) ≤ (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * (E1 + ε * E2) := by
    intro c1 c2 h1 h2
    calc c1 * E1 + c2 * (ε * E2) ≤ (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * E1 + (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * (ε * E2) :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hE1p) (mul_le_mul_of_nonneg_right h2 hεE2)
      _ = (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * (E1 + ε * E2) := by ring
  intro k hk
  have hden : (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) ≥ 0 := by positivity
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
  · rw [iteratedDeriv_zero]
    simp only [Nat.cast_zero, sub_zero]
    have hLne : L y ≠ 0 := hLpos.ne'
    have hL0ne : lambda0 p y ≠ 0 := by rw [hL0]; exact hspos.ne'
    have e : ‖a y‖ ^ 2 / L y - 1 / lambda0 p y =
        (‖a y‖ ^ 2 - 1) * (1 / L y) + (lambda0 p y - L y) * (1 / L y) * (1 / lambda0 p y) := by
      field_simp; ring
    rw [e, hiL0]
    have hd0' : |lambda0 p y - L y| ≤ Cd * ε * (s * E2) := by rw [abs_sub_comm, ← r1]; exact hd0
    calc |(‖a y‖ ^ 2 - 1) * (1 / L y) + (lambda0 p y - L y) * (1 / L y) * ys|
        ≤ |‖a y‖ ^ 2 - 1| * (1 / L y) + |lambda0 p y - L y| * (1 / L y) * ys := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hiLp, abs_of_pos hyspos]
      _ ≤ (3 * Ca * E1) * (2 * ys) + (Cd * ε * (s * E2)) * (2 * ys) * ys := by gcongr
      _ = ys * (6 * Ca * E1 + 2 * Cd * ε * E2 * (s * ys)) := by ring
      _ = ys * (6 * Ca * E1 + 2 * Cd * ε * E2) := by rw [hsys, mul_one]
      _ ≤ ys * ((14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * (E1 + ε * E2)) := by
          apply mul_le_mul_of_nonneg_left _ hyspos.le
          have := hfin (6 * Ca) (2 * Cd) (by linarith) (by linarith)
          linarith
      _ = _ := by ring
  · rw [iteratedDeriv_one]
    have hL0ne : lambda0 p y ≠ 0 := by rw [hL0]; exact hspos.ne'
    have hfd : HasDerivAt (fun t => ‖a t‖ ^ 2 / L t - 1 / lambda0 p t)
        ((2 * ((a y).re * (deriv a y).re + (a y).im * (deriv a y).im) * L y -
            ‖a y‖ ^ 2 * deriv L y) / L y ^ 2 -
          (0 * lambda0 p y - 1 * (1 / p * (s * y⁻¹))) / lambda0 p y ^ 2) y :=
      (hAd.div hLd.hasDerivAt hLpos.ne').sub ((hasDerivAt_const y (1 : ℝ)).div hL0d hL0ne)
    rw [hfd.deriv]
    set A' := 2 * ((a y).re * (deriv a y).re + (a y).im * (deriv a y).im) with hA'def
    set L' := deriv L y
    have hL0'eq : deriv (lambda0 p) y = 1 / p * (s * y⁻¹) := hL0d.deriv
    rw [hL0'eq] at hd1
    set L0' := 1 / p * (s * y⁻¹) with hL0'def
    have e : (A' * L y - ‖a y‖ ^ 2 * L') / L y ^ 2 - (0 * lambda0 p y - 1 * L0') / lambda0 p y ^ 2 =
        A' * (1 / L y) - (‖a y‖ ^ 2 - 1) * L' * (1 / L y) ^ 2 - (L' - L0') * (1 / L y) ^ 2 +
          L0' * (L y - lambda0 p y) * (L y + lambda0 p y) * (1 / L y) ^ 2 * (1 / lambda0 p y) ^ 2 := by
      field_simp; ring
    rw [e, hiL0]
    have hL'b : |L'| ≤ Cl * (s * y⁻¹) := by rw [← r3]; exact hL'
    have hd1' : |L' - L0'| ≤ Cd * ε * (s * E2 * y⁻¹) := by rw [← r4]; exact hd1
    have hd0' : |L y - lambda0 p y| ≤ Cd * ε * (s * E2) := by rw [← r1]; exact hd0
    have hsum : |L y + lambda0 p y| ≤ 5 / 2 * s := by
      rw [abs_of_pos (by rw [hL0]; linarith), hL0]; linarith
    have hL0'p : 0 ≤ L0' := by positivity
    have hiL2 : (1 / L y) ^ 2 ≤ (2 * ys) ^ 2 := pow_le_pow_left₀ hiLp hiL 2
    have hiL2p : 0 ≤ (1 / L y) ^ 2 := by positivity
    calc |A' * (1 / L y) - (‖a y‖ ^ 2 - 1) * L' * (1 / L y) ^ 2 - (L' - L0') * (1 / L y) ^ 2 +
          L0' * (L y - lambda0 p y) * (L y + lambda0 p y) * (1 / L y) ^ 2 * ys ^ 2|
        ≤ |A'| * (1 / L y) + |‖a y‖ ^ 2 - 1| * |L'| * (1 / L y) ^ 2 + |L' - L0'| * (1 / L y) ^ 2 +
          L0' * |L y - lambda0 p y| * |L y + lambda0 p y| * (1 / L y) ^ 2 * ys ^ 2 := by
          have h1 := abs_add_le (A' * (1 / L y) - (‖a y‖ ^ 2 - 1) * L' * (1 / L y) ^ 2 -
            (L' - L0') * (1 / L y) ^ 2)
            (L0' * (L y - lambda0 p y) * (L y + lambda0 p y) * (1 / L y) ^ 2 * ys ^ 2)
          have h2 := abs_sub (A' * (1 / L y) - (‖a y‖ ^ 2 - 1) * L' * (1 / L y) ^ 2)
            ((L' - L0') * (1 / L y) ^ 2)
          have h3 := abs_sub (A' * (1 / L y)) ((‖a y‖ ^ 2 - 1) * L' * (1 / L y) ^ 2)
          simp only [abs_mul, abs_of_nonneg hiLp, abs_of_nonneg hiL2p, abs_of_nonneg hL0'p,
            abs_of_nonneg (sq_nonneg ys)] at h1 h2 h3 ⊢
          linarith
      _ ≤ (4 * Ca * E1 * y⁻¹) * (2 * ys) + (3 * Ca * E1) * (Cl * (s * y⁻¹)) * (2 * ys) ^ 2 +
          (Cd * ε * (s * E2 * y⁻¹)) * (2 * ys) ^ 2 +
          L0' * (Cd * ε * (s * E2)) * (5 / 2 * s) * (2 * ys) ^ 2 * ys ^ 2 := by
          gcongr
      _ = ys * y⁻¹ * ((8 * Ca + 12 * Ca * Cl * (s * ys)) * E1 +
          (4 * Cd * (s * ys) + 10 / p * Cd * (s * ys) ^ 3) * (ε * E2)) := by
          rw [hL0'def]; ring
      _ = ys * y⁻¹ * ((8 * Ca + 12 * Ca * Cl) * E1 + (4 * Cd + 10 * Cd / p) * (ε * E2)) := by
          rw [hsys]; ring
      _ ≤ ys * y⁻¹ * ((14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * (E1 + ε * E2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hfin _ _ (by linarith) (by rw [mul_div_assoc]; linarith)
      _ = (14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p) * y ^ (-1 / p - ((1 : ℕ) : ℝ)) *
            (E1 + ε * E2) := by
          rw [show -1 / p - ((1 : ℕ) : ℝ) = -1 / p + -1 by push_cast; ring, rpow_add hy0,
            rpow_neg_one]
          ring

/-- Blueprint: lem:c04_E3_cancellation.  For `y ≥ R`,
`ℰ₃ = 2n_ε|μ|²(|a_*|²/λ - 1/λ₀) Re Z` and
`|∂^k(|a_*|²/λ - 1/λ₀)| ≤ C y^{-1/p-k}(y^{-2β} + εy^{-p-1})` (`k = 0,1`). -/
theorem c04_E3_cancellation (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        residual_decomposition_E3 p R ε μ y =
          2 * n_eps p ε * ‖μ‖ ^ 2 * (‖astar p y‖ ^ 2 / fam_lambda p ε μ y - 1 / lambda0 p y) *
            (fam_Z p R ε μ y).re) ∧
      (∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R, ∀ k : ℕ, k ≤ 1 →
        |iteratedDeriv k (fun t => ‖astar p t‖ ^ 2 / fam_lambda p ε μ t - 1 / lambda0 p t) y| ≤
          C * y ^ (-1 / p - k) * (y ^ (-2 * beta p) + ε * y ^ (-p - 1))) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hbasic, hder, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨Cl, hCl, hLder⟩ := hder 1 1 one_pos
  obtain ⟨ε₂, hε₂, R₂, hR₂, hlpd⟩ := c04_lambda_psi_difference p hp hp1 δ hδ hδμ
  obtain ⟨Cd0, hCd0, hdd0⟩ := hlpd 0
  obtain ⟨Cd1, hCd1, hdd1⟩ := hlpd 1
  obtain ⟨y₀, hy₀, ha2, hamp⟩ := c04_seed_amplitude p hp hp1
  obtain ⟨Ca0, hCa0, ham0⟩ := hamp 0
  obtain ⟨Ca1, hCa1, ham1⟩ := hamp 1
  have hε₀ : min ε₁ ε₂ ∈ Ioc (0 : ℝ) 1 :=
    ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩
  have hR₀ : max (max R₁ R₂) y₀ ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _))
  have hpt : ∀ R ≥ max (max R₁ R₂) y₀, ∀ ε ∈ Icc (0 : ℝ) (min ε₁ ε₂), ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
      R ≥ R₁ ∧ R ≥ R₂ ∧ y ≥ y₀ ∧ ε ∈ Icc (0 : ℝ) ε₁ ∧ ε ∈ Icc (0 : ℝ) ε₂ ∧ 0 < y ∧ 1 ≤ y := by
    intro R hR ε hε μ hμ y hy
    have h1 : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
    refine ⟨h1, le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR,
      le_trans (le_trans (le_max_right _ _) hR) hy, ⟨hε.1, hε.2.trans (min_le_left _ _)⟩,
      ⟨hε.1, hε.2.trans (min_le_right _ _)⟩, by linarith, by linarith⟩
  set Ca := Ca0 + Ca1
  set Cd := Cd0 + Cd1
  refine ⟨min ε₁ ε₂, hε₀, max (max R₁ R₂) y₀, hR₀, fun R hR ε hε μ hμ y hy => ?_,
    14 * Ca + 12 * Ca * Cl + 6 * Cd + 10 * Cd / p, by positivity, ?_⟩
  · obtain ⟨hRa, -, -, hεa, -, hy0, -⟩ := hpt R hR ε hε μ hμ y hy
    obtain ⟨h1, h2, -, -⟩ := hbasic R hRa ε hεa μ hμ y (by linarith)
    exact c04_aux_E3_id p R ε μ y hp0 hy0 (c04_aux_lam_pos p ε μ y hy0 h1 h2).1
  intro R hR ε hε μ hμ y hy k hk
  obtain ⟨hRa, hRb, hyy, hεa, hεb, hy0, hy1⟩ := hpt R hR ε hε μ hμ y hy
  obtain ⟨h1, h2, h3, -⟩ := hbasic R hRa ε hεa μ hμ y (by linarith)
  have hYpos : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
  have hε0 := hε.1
  have hlam0d : DifferentiableAt ℝ (lambda0 p) y :=
    differentiableAt_id.rpow_const (Or.inl hy0.ne')
  have hLd := c04_aux_lambda_diff p ε μ y hy0
  refine c04_aux_E3_bound p ε Ca Cl Cd hp0 hε0 (by positivity) hCl.le (by positivity) (astar p)
    (fam_lambda p ε μ) y hy1 (c04_aux_astar_diff p hp0 hplus hμs y hy0) hLd h2 h3 (ha2 y hyy)
    ?_ ?_ ?_ ?_ ?_ k hk
  · have := (ham0 y hyy).1
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (hYpos _))
  · have := (ham1 y hyy).1
    rw [iteratedDeriv_one, deriv_sub_const] at this
    simp only [Nat.cast_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (hYpos _))
  · have := (hLder R hRa ε hεa μ hμ y (by linarith)).1
    rw [iteratedDeriv_one] at this
    simpa using this
  · have := (hdd0 R hRb ε hεb μ hμ y hy).1
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (hYpos _))
    exact mul_le_mul_of_nonneg_right (by linarith) hε0
  · have := (hdd1 R hRb ε hεb μ hμ y hy).1
    rw [iteratedDeriv_one, deriv_fun_sub hLd hlam0d] at this
    simp only [Nat.cast_one] at this
    refine (this.trans (le_of_eq ?_)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show Cd1 ≤ Cd by linarith) hε0) (hYpos _))
    congr 2; ring

/-- Blueprint: prop:approx_E3.
`|∂^j ℰ₃(y)| ≤ C ε² ⟨y⟩^{-p-3β+j/p} + C ε ⟨y⟩^{1-5β+j/p}` for `y ≥ 2R`, `j = 0,1`. -/
theorem approx_E3 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ 2 * R, ∀ j : ℕ, j ≤ 1 →
        |iteratedDeriv j (residual_decomposition_E3 p R ε μ) y| ≤
          C * ε ^ 2 * jb y ^ (-p - 3 * beta p + j / p) + C * ε * jb y ^ (1 - 5 * beta p + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, -, CE, hCE, hfb⟩ := c04_E3_cancellation p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hZb, -⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨CZ0, hCZ0, hZ0⟩ := hZb 0 1 one_pos
  obtain ⟨CZ1, hCZ1, hZ1⟩ := hZb 1 1 one_pos
  obtain ⟨ε₃, hε₃, R₃, hR₃, hbasic, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨Cc, hCc, hcs⟩ := (c04_constants_small p hp hp1 1 one_pos).1
  have hβ : 0 < beta p := by unfold beta; positivity
  have hβ76 : beta p < 7 / 6 := by
    unfold beta; rw [div_lt_iff₀ (by positivity)]; linarith
  have h2β : 2 * beta p = 1 + 1 / p := by unfold beta; field_simp
  have hm : -1 / p = -(1 / p) := by ring
  have h0p : (0 : ℝ) / p = 0 := zero_div p
  have hip : 1 / p < 4 / 3 := by rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith
  set M2 := (2 * ‖mu_star p‖) ^ 2 with hM2
  set B := 2 * Cc * M2 * CE * (CZ0 + CZ1) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hε₀ : min (min ε₁ ε₂) ε₃ ∈ Ioc (0 : ℝ) 1 := ⟨lt_min (lt_min hε₁.1 hε₂.1) hε₃.1,
      (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)⟩
  have hR₀ : max (max R₁ R₂) R₃ ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _))
  have hCpos : (0 : ℝ) < 64 * B + 1 := by linarith
  refine ⟨min (min ε₁ ε₂) ε₃, hε₀, max (max R₁ R₂) R₃, hR₀, 64 * B + 1, hCpos, ?_⟩
  intro R hR ε hε μ hμ y hy j hj
  have hRa : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hRb : R ≥ R₂ := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hRc : R ≥ R₃ := le_trans (le_max_right _ _) hR
  have hεa : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hεb : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hεc : ε ∈ Icc (0 : ℝ) ε₃ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans hε₁.2⟩
  have hε0 := hε.1
  have hR2 : 2 ≤ R := le_trans hR₁ hRa
  have hR0 : 0 < R := by linarith
  have hyR : y ≥ R := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  set Z := fam_Z p R ε μ with hZdef
  have hf0 : |(fun t => ‖astar p t‖ ^ 2 / fam_lambda p ε μ t - 1 / lambda0 p t) y| ≤
      CE * y ^ (-1 / p) * (y ^ (-2 * beta p) + ε * y ^ (-p - 1)) := by
    have := hfb R hRa ε hεa μ hμ y hyR 0 (by norm_num)
    rw [iteratedDeriv_zero] at this
    simpa only [Nat.cast_zero, sub_zero] using this
  have hf1 : |deriv (fun t => ‖astar p t‖ ^ 2 / fam_lambda p ε μ t - 1 / lambda0 p t) y| ≤
      CE * y ^ (-1 / p - 1) * (y ^ (-2 * beta p) + ε * y ^ (-p - 1)) := by
    have := hfb R hRa ε hεa μ hμ y hyR 1 le_rfl
    rw [iteratedDeriv_one] at this
    simpa only [Nat.cast_one] using this
  set f : ℝ → ℝ := fun t => ‖astar p t‖ ^ 2 / fam_lambda p ε μ t - 1 / lambda0 p t with hfdef
  set K := 2 * n_eps p ε * ‖μ‖ ^ 2 with hKdef
  obtain ⟨h1, h2, -, -⟩ := hbasic R hRc ε hεc μ hμ y (by linarith)
  obtain ⟨hlpos, -⟩ := c04_aux_lam_pos p ε μ y hy0 h1 h2
  have hev : residual_decomposition_E3 p R ε μ =ᶠ[𝓝 y] fun t => K * f t * (Z t).re := by
    filter_upwards [Ioi_mem_nhds (show R / 2 < y by linarith)] with t ht
    have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
    obtain ⟨g1, g2, -, -⟩ := hbasic R hRc ε hεc μ hμ t ht
    rw [c04_aux_E3_id p R ε μ t hp0 ht0 (c04_aux_lam_pos p ε μ t ht0 g1 g2).1]
  have had := c04_aux_astar_diff p hp0 hplus hμs y hy0
  have hfd : DifferentiableAt ℝ f y := by
    simp only [hfdef]
    exact ((c04_aux_normsq_hasDeriv (astar p) y had).differentiableAt.div
      (c04_aux_lambda_diff p ε μ y hy0) hlpos.ne').sub
      ((differentiableAt_const _).div (differentiableAt_id.rpow_const (Or.inl hy0.ne'))
        (rpow_pos_of_pos hy0 _).ne')
  have hZd : DifferentiableAt ℝ Z y := c04_aux_famZ_diff p R ε μ hp0 hR0 hplus hμs y hy0 hlpos
  have hZre : HasDerivAt (fun t => (Z t).re) (deriv Z y).re y :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hZd.hasDerivAt
  have hz0 : ‖Z y‖ ≤ CZ0 * y ^ (-beta p) := by
    have := (hZ0 R hRb ε hεb μ hμ y hyR).1; simpa using this
  have hz1 : ‖deriv Z y‖ ≤ CZ1 * y ^ (-beta p + 1 / p) := by
    have := (hZ1 R hRb ε hεb μ hμ y hyR).1; simpa using this
  have hK : |K| ≤ 2 * Cc * M2 * ε := by
    have hn := (hcs ε hε1 0 (by simp)).2.1
    have hμ2 : ‖μ‖ ^ 2 ≤ M2 := by
      rw [hM2]; exact pow_le_pow_left₀ (norm_nonneg _) (c04_aux_Bbar_norm p δ hδμ μ hμ) 2
    rw [hKdef, abs_mul, abs_mul, abs_two, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖μ‖ ^ 2)]
    calc 2 * |n_eps p ε| * ‖μ‖ ^ 2 ≤ 2 * (Cc * ε) * M2 := by gcongr
      _ = 2 * Cc * M2 * ε := by ring
  have hre0 := Complex.abs_re_le_norm (Z y)
  have hre1 := Complex.abs_re_le_norm (deriv Z y)
  -- exponent identities
  set e1 := 1 - 5 * beta p + (j : ℝ) / p with he1
  set e2 := -p - 3 * beta p + (j : ℝ) / p with he2
  have hjr : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hjp : 0 ≤ (j : ℝ) / p := by positivity
  have hjp1 : (j : ℝ) / p ≤ 1 / p := by gcongr
  have hM2nn : 0 ≤ M2 := by rw [hM2]; positivity
  have hX0 : 0 ≤ 2 * Cc * M2 * CE * CZ1 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hM2nn) hCE.le) hCZ1.le
  have hEpos : 0 ≤ ε * y ^ e1 + ε ^ 2 * y ^ e2 :=
    add_nonneg (mul_nonneg hε0 (rpow_nonneg hy0.le _)) (mul_nonneg (sq_nonneg ε) (rpow_nonneg hy0.le _))
  clear_value Z f K M2 B e1 e2
  have hmain : |iteratedDeriv j (residual_decomposition_E3 p R ε μ) y| ≤
      B * ε * y ^ e1 + B * ε ^ 2 * y ^ e2 := by
    have hYa : ∀ a b : ℝ, y ^ a * y ^ b = y ^ (a + b) := fun a b => (rpow_add hy0 a b).symm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · rw [iteratedDeriv_zero, hev.eq_of_nhds, abs_mul, abs_mul]
      have q1 : y ^ (-1 / p) * y ^ (-2 * beta p) * y ^ (-beta p) = y ^ e1 := by
        rw [hYa, hYa, he1]; congr 1; push_cast; linarith
      have q2 : y ^ (-1 / p) * y ^ (-p - 1) * y ^ (-beta p) = y ^ e2 := by
        rw [hYa, hYa, he2]; congr 1; push_cast; linarith
      calc |K| * |f y| * |(Z y).re| ≤ (2 * Cc * M2 * ε) *
            (CE * y ^ (-1 / p) * (y ^ (-2 * beta p) + ε * y ^ (-p - 1))) * (CZ0 * y ^ (-beta p)) := by
            gcongr; exact hre0.trans hz0
        _ = (2 * Cc * M2 * CE * CZ0) * (ε * (y ^ (-1 / p) * y ^ (-2 * beta p) * y ^ (-beta p)) +
            ε ^ 2 * (y ^ (-1 / p) * y ^ (-p - 1) * y ^ (-beta p))) := by ring
        _ = (2 * Cc * M2 * CE * CZ0) * (ε * y ^ e1 + ε ^ 2 * y ^ e2) := by rw [q1, q2]
        _ ≤ B * (ε * y ^ e1 + ε ^ 2 * y ^ e2) := by
            apply mul_le_mul_of_nonneg_right _ hEpos
            rw [hBdef]; linarith
        _ = _ := by ring
    · rw [iteratedDeriv_one, hev.deriv_eq]
      have hd : HasDerivAt (fun t => K * f t * (Z t).re)
          (K * deriv f y * (Z y).re + K * f y * (deriv Z y).re) y :=
        (hfd.hasDerivAt.const_mul K).mul hZre
      rw [hd.deriv]
      have q1 : y ^ (-1 / p - 1) * y ^ (-2 * beta p) * y ^ (-beta p) ≤ y ^ e1 := by
        rw [hYa, hYa, he1]; apply rpow_le_rpow_of_exponent_le hy1; push_cast; linarith
      have q2 : y ^ (-1 / p - 1) * y ^ (-p - 1) * y ^ (-beta p) ≤ y ^ e2 := by
        rw [hYa, hYa, he2]; apply rpow_le_rpow_of_exponent_le hy1; push_cast; linarith
      have q3 : y ^ (-1 / p) * y ^ (-2 * beta p) * y ^ (-beta p + 1 / p) = y ^ e1 := by
        rw [hYa, hYa, he1]; congr 1; push_cast; linarith
      have q4 : y ^ (-1 / p) * y ^ (-p - 1) * y ^ (-beta p + 1 / p) = y ^ e2 := by
        rw [hYa, hYa, he2]; congr 1; push_cast; linarith
      have hA : |K * deriv f y * (Z y).re| ≤ (2 * Cc * M2 * CE * CZ0) * (ε * y ^ e1 + ε ^ 2 * y ^ e2) := by
        rw [abs_mul, abs_mul]
        calc |K| * |deriv f y| * |(Z y).re| ≤ (2 * Cc * M2 * ε) *
              (CE * y ^ (-1 / p - 1) * (y ^ (-2 * beta p) + ε * y ^ (-p - 1))) * (CZ0 * y ^ (-beta p)) := by
              gcongr; exact hre0.trans hz0
          _ = (2 * Cc * M2 * CE * CZ0) * (ε * (y ^ (-1 / p - 1) * y ^ (-2 * beta p) * y ^ (-beta p)) +
              ε ^ 2 * (y ^ (-1 / p - 1) * y ^ (-p - 1) * y ^ (-beta p))) := by ring
          _ ≤ _ := by gcongr
      have hB' : |K * f y * (deriv Z y).re| ≤ (2 * Cc * M2 * CE * CZ1) * (ε * y ^ e1 + ε ^ 2 * y ^ e2) := by
        rw [abs_mul, abs_mul]
        calc |K| * |f y| * |(deriv Z y).re| ≤ (2 * Cc * M2 * ε) *
              (CE * y ^ (-1 / p) * (y ^ (-2 * beta p) + ε * y ^ (-p - 1))) * (CZ1 * y ^ (-beta p + 1 / p)) := by
              gcongr; exact hre1.trans hz1
          _ = (2 * Cc * M2 * CE * CZ1) * (ε * (y ^ (-1 / p) * y ^ (-2 * beta p) * y ^ (-beta p + 1 / p)) +
              ε ^ 2 * (y ^ (-1 / p) * y ^ (-p - 1) * y ^ (-beta p + 1 / p))) := by ring
          _ = _ := by rw [q3, q4]
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add hA hB'
        _ = B * ε * y ^ e1 + B * ε ^ 2 * y ^ e2 := by rw [hBdef]; ring
  have c1 := c04_aux_rpow_le_jb32 y e1 hy1 (by rw [he1]; linarith) (by rw [he1]; linarith)
  have c2 := c04_aux_rpow_le_jb32 y e2 hy1 (by rw [he2]; linarith) (by rw [he2]; linarith)
  refine hmain.trans ?_
  have hJ1 : 0 ≤ jb y ^ e1 := (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
  have hJ2 : 0 ≤ jb y ^ e2 := (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
  have hBε : 0 ≤ B * ε := mul_nonneg hB0 hε0
  have hBε2 : 0 ≤ B * ε ^ 2 := mul_nonneg hB0 (sq_nonneg ε)
  calc B * ε * y ^ e1 + B * ε ^ 2 * y ^ e2 ≤ B * ε * (32 * jb y ^ e1) + B * ε ^ 2 * (32 * jb y ^ e2) :=
        add_le_add (mul_le_mul_of_nonneg_left c1 hBε) (mul_le_mul_of_nonneg_left c2 hBε2)
    _ ≤ (64 * B + 1) * ε ^ 2 * jb y ^ e2 + (64 * B + 1) * ε * jb y ^ e1 := by
        have a1 : B * ε * (32 * jb y ^ e1) ≤ (64 * B + 1) * ε * jb y ^ e1 := by
          have : B * ε * (32 * jb y ^ e1) = (32 * B) * (ε * jb y ^ e1) := by ring
          rw [this, mul_assoc (64 * B + 1)]
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hε0 hJ1)
        have a2 : B * ε ^ 2 * (32 * jb y ^ e2) ≤ (64 * B + 1) * ε ^ 2 * jb y ^ e2 := by
          have : B * ε ^ 2 * (32 * jb y ^ e2) = (32 * B) * (ε ^ 2 * jb y ^ e2) := by ring
          rw [this, mul_assoc (64 * B + 1)]
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg ε) hJ2)
        linarith

/-- Real part of a differentiable complex function. -/
theorem c04_aux_re_hasDeriv (F : ℝ → ℂ) (y : ℝ) (hF : DifferentiableAt ℝ F y) :
    HasDerivAt (fun t => (F t).re) (deriv F y).re y :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hF.hasDerivAt

/-- Blueprint: prop:approx_E4.  `|∂^j ℰ₄(y)| ≤ C ε² ⟨y⟩^{1-5β+j/p}` for `y ≥ 2R`, `j = 0,1`. -/
theorem approx_E4 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ 2 * R, ∀ j : ℕ, j ≤ 1 →
        |iteratedDeriv j (residual_decomposition_E4 p R ε μ) y| ≤
          C * ε ^ 2 * jb y ^ (1 - 5 * beta p + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, -, Ct, hCt, hbt⟩ := c04_lambda_taylor p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hZb, -⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨CZ0, hCZ0, hZ0⟩ := hZb 0 1 one_pos
  obtain ⟨CZ1, hCZ1, hZ1⟩ := hZb 1 1 one_pos
  obtain ⟨ε₃, hε₃, R₃, hR₃, hbasic, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨Cc, hCc, hcs⟩ := (c04_constants_small p hp hp1 1 one_pos).1
  have hβ : 0 < beta p := by unfold beta; positivity
  have hβ76 : beta p < 7 / 6 := by
    unfold beta; rw [div_lt_iff₀ (by positivity)]; linarith
  have h2β : 2 * beta p = 1 + 1 / p := by unfold beta; field_simp
  set B := 2 * Cc * Ct * (CZ0 + CZ1) with hBdef
  have hε₀ : min (min ε₁ ε₂) ε₃ ∈ Ioc (0 : ℝ) 1 := ⟨lt_min (lt_min hε₁.1 hε₂.1) hε₃.1,
      (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)⟩
  have hR₀ : max (max R₁ R₂) R₃ ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _))
  have hCpos : (0 : ℝ) < 32 * B + 1 := by
    have : 0 ≤ B := by rw [hBdef]; positivity
    linarith
  refine ⟨min (min ε₁ ε₂) ε₃, hε₀, max (max R₁ R₂) R₃, hR₀, 32 * B + 1, hCpos, ?_⟩
  intro R hR ε hε μ hμ y hy j hj
  have hRa : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hRb : R ≥ R₂ := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hRc : R ≥ R₃ := le_trans (le_max_right _ _) hR
  have hεa : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hεb : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hεc : ε ∈ Icc (0 : ℝ) ε₃ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans hε₁.2⟩
  have hR2 : 2 ≤ R := le_trans hR₁ hRa
  have hR0 : 0 < R := by linarith
  have hyR : y ≥ R := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  set Z := fam_Z p R ε μ with hZdef
  set P : ℝ → ℝ := fun t => fam_lambda p ε μ t ^ p - t + c_eps p ε * t ^ (-p) with hPdef
  obtain ⟨h1, h2, -, -⟩ := hbasic R hRc ε hεc μ hμ y (by linarith)
  obtain ⟨hlpos, -⟩ := c04_aux_lam_pos p ε μ y hy0 h1 h2
  obtain ⟨-, -, hb3⟩ := hbt R hRa ε hεa μ hμ y hyR
  have hP0 : |P y| ≤ Ct * ε * y ^ (-1 / p) := by
    have := hb3 0 (by norm_num); simpa using this
  have hP1 : |deriv P y| ≤ Ct * ε * y ^ (-1 / p - 1) := by
    have := hb3 1 le_rfl; rw [iteratedDeriv_one] at this; simpa using this
  have hcc : |c_cubic p ε| ≤ Cc * ε := (hcs ε hε1 0 (by simp)).2.2.1
  have hPd : DifferentiableAt ℝ P y := by
    simp only [hPdef]
    apply DifferentiableAt.add
    · apply DifferentiableAt.sub
      · exact (c04_aux_lambda_diff p ε μ y hy0).rpow_const (Or.inl hlpos.ne')
      · exact differentiableAt_id
    · exact (differentiableAt_id.rpow_const (Or.inl hy0.ne')).const_mul _
  have hZd : DifferentiableAt ℝ Z y := c04_aux_famZ_diff p R ε μ hp0 hR0 hplus hμs y hy0 hlpos
  have hZ3d : DifferentiableAt ℝ (fun t => Z t ^ 3) y := hZd.pow 3
  have hW : HasDerivAt (fun t => (Z t ^ 3).re) (deriv (fun t => Z t ^ 3) y).re y :=
    c04_aux_re_hasDeriv (fun t => Z t ^ 3) y hZ3d
  have hz0 : ‖Z y ^ 3‖ ≤ CZ0 * y ^ (-3 * beta p) := by
    have := (hZ0 R hRb ε hεb μ hμ y hyR).2.1; simpa using this
  have hz1 : ‖deriv (fun t => Z t ^ 3) y‖ ≤ CZ1 * y ^ (-3 * beta p + 1 / p) := by
    have := (hZ1 R hRb ε hεb μ hμ y hyR).2.1; rw [iteratedDeriv_one] at this; simpa using this
  have hre0 := Complex.abs_re_le_norm (Z y ^ 3)
  have hre1 := Complex.abs_re_le_norm (deriv (fun t => Z t ^ 3) y)
  have hε0 := hε.1
  have hfun : residual_decomposition_E4 p R ε μ = fun t => 2 * c_cubic p ε * P t * (Z t ^ 3).re := by
    funext t; simp only [residual_decomposition_E4, hPdef, hZdef]
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  clear_value P Z B
  have hmain : |iteratedDeriv j (residual_decomposition_E4 p R ε μ) y| ≤
      B * ε ^ 2 * y ^ (1 - 5 * beta p + j / p) := by
    have hexp0 : y ^ (-1 / p) * y ^ (-3 * beta p) = y ^ (1 - 5 * beta p) := by
      rw [← rpow_add hy0]; congr 1
      have : -1 / p = -(1 / p) := by ring
      linarith
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · rw [iteratedDeriv_zero, hfun]
      simp only [Nat.cast_zero, zero_div, add_zero]
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      have hY : 0 ≤ y ^ (1 - 5 * beta p) := by positivity
      calc 2 * |c_cubic p ε| * |P y| * |(Z y ^ 3).re| ≤
          2 * (Cc * ε) * (Ct * ε * y ^ (-1 / p)) * (CZ0 * y ^ (-3 * beta p)) := by
            gcongr; exact hre0.trans hz0
        _ = (2 * Cc * Ct * CZ0) * (ε ^ 2 * (y ^ (-1 / p) * y ^ (-3 * beta p))) := by ring
        _ = (2 * Cc * Ct * CZ0) * (ε ^ 2 * y ^ (1 - 5 * beta p)) := by rw [hexp0]
        _ ≤ B * (ε ^ 2 * y ^ (1 - 5 * beta p)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hBdef]; have := mul_pos (mul_pos hCc hCt) hCZ1; nlinarith
        _ = _ := by ring
    · rw [iteratedDeriv_one, hfun]
      have hd : HasDerivAt (fun t => 2 * c_cubic p ε * P t * (Z t ^ 3).re)
          (2 * c_cubic p ε * deriv P y * (Z y ^ 3).re +
            2 * c_cubic p ε * P y * (deriv (fun t => Z t ^ 3) y).re) y :=
        (hPd.hasDerivAt.const_mul (2 * c_cubic p ε)).mul hW
      rw [hd.deriv]
      simp only [Nat.cast_one]
      have e1 : y ^ (-1 / p - 1) * y ^ (-3 * beta p) ≤ y ^ (1 - 5 * beta p + 1 / p) := by
        rw [← rpow_add hy0]
        apply rpow_le_rpow_of_exponent_le hy1
        have : 0 < 1 / p := by positivity
        have : -1 / p = -(1 / p) := by ring
        linarith
      have e2 : y ^ (-1 / p) * y ^ (-3 * beta p + 1 / p) = y ^ (1 - 5 * beta p + 1 / p) := by
        rw [← rpow_add hy0]; congr 1
        have : -1 / p = -(1 / p) := by ring
        linarith
      calc |2 * c_cubic p ε * deriv P y * (Z y ^ 3).re +
            2 * c_cubic p ε * P y * (deriv (fun t => Z t ^ 3) y).re|
          ≤ 2 * |c_cubic p ε| * |deriv P y| * |(Z y ^ 3).re| +
            2 * |c_cubic p ε| * |P y| * |(deriv (fun t => Z t ^ 3) y).re| := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
        _ ≤ 2 * (Cc * ε) * (Ct * ε * y ^ (-1 / p - 1)) * (CZ0 * y ^ (-3 * beta p)) +
            2 * (Cc * ε) * (Ct * ε * y ^ (-1 / p)) * (CZ1 * y ^ (-3 * beta p + 1 / p)) := by
            gcongr
            · exact hre0.trans hz0
            · exact hre1.trans hz1
        _ = (2 * Cc * Ct * CZ0) * ε ^ 2 * (y ^ (-1 / p - 1) * y ^ (-3 * beta p)) +
            (2 * Cc * Ct * CZ1) * ε ^ 2 * (y ^ (-1 / p) * y ^ (-3 * beta p + 1 / p)) := by ring
        _ ≤ (2 * Cc * Ct * CZ0) * ε ^ 2 * y ^ (1 - 5 * beta p + 1 / p) +
            (2 * Cc * Ct * CZ1) * ε ^ 2 * y ^ (1 - 5 * beta p + 1 / p) := by
            rw [e2]; gcongr
        _ = B * ε ^ 2 * y ^ (1 - 5 * beta p + 1 / p) := by rw [hBdef]; ring
  refine hmain.trans ?_
  have hjr : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hconv := c04_aux_rpow_le_jb32 y (1 - 5 * beta p + j / p) hy1
    (by
      have : (j : ℝ) / p ≤ 1 / p := by gcongr
      linarith)
    (by have : 0 ≤ (j : ℝ) / p := by positivity
        have : 1 / p < 4 / 3 := by rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith
        linarith)
  have hJ : 0 ≤ jb y ^ (1 - 5 * beta p + j / p) :=
    (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
  have hB : 0 ≤ B := hB0
  calc B * ε ^ 2 * y ^ (1 - 5 * beta p + j / p) ≤ B * ε ^ 2 * (32 * jb y ^ (1 - 5 * beta p + j / p)) :=
        mul_le_mul_of_nonneg_left hconv (mul_nonneg hB (sq_nonneg ε))
    _ = (32 * B) * ε ^ 2 * jb y ^ (1 - 5 * beta p + j / p) := by ring
    _ ≤ (32 * B + 1) * ε ^ 2 * jb y ^ (1 - 5 * beta p + j / p) := by
        apply mul_le_mul_of_nonneg_right _ hJ
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith


/-! ### Profile bounds: `f_osc`, regional forms, `approx_profile_bounds` -/

/-- Tail integrals: `F(y) = ∫_y^∞ G` has derivative `-G` on `(a,∞)` when `G` is continuous on
`(a,∞)` and integrable on `(b,∞)`. -/
theorem c04_aux_tail_hasDeriv (G : ℝ → ℂ) (a b : ℝ) (hG : ContinuousOn G (Ioi a))
    (hGi : IntegrableOn G (Ioi b)) (y : ℝ) (hy : a < y) :
    HasDerivAt (fun x => ∫ t in Ioi x, G t) (-G y) y := by
  have hII : ∀ x, a < x → IntervalIntegrable G volume x (max b x) := by
    intro x hx
    refine ContinuousOn.intervalIntegrable (hG.mono ?_)
    intro t ht
    rw [uIcc_of_le (le_max_right _ _)] at ht
    exact lt_of_lt_of_le hx ht.1
  have hrep : ∀ x, a < x → ∫ t in Ioi x, G t = (∫ t in Ioi (max b y), G t) - ∫ t in (max b y)..x, G t := by
    intro x hx
    have hB : IntegrableOn G (Ioi (max b y)) := hGi.mono_set (Ioi_subset_Ioi (le_max_left _ _))
    have hI : IntervalIntegrable G volume x (max b y) := by
      refine ContinuousOn.intervalIntegrable (hG.mono ?_)
      intro t ht
      rcases le_total x (max b y) with h | h
      · rw [uIcc_of_le h] at ht; exact lt_of_lt_of_le hx ht.1
      · rw [uIcc_of_ge h] at ht; exact lt_of_lt_of_le (lt_of_lt_of_le hy (le_max_right _ _)) ht.1
    rw [← intervalIntegral.integral_interval_add_Ioi' hI hB, intervalIntegral.integral_symm x]
    ring
  have hev : (fun x => ∫ t in Ioi x, G t) =ᶠ[𝓝 y]
      fun x => (∫ t in Ioi (max b y), G t) - ∫ t in (max b y)..x, G t := by
    filter_upwards [Ioi_mem_nhds hy] with x hx using hrep x hx
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hI2 : IntervalIntegrable G volume (max b y) y := by
    refine ContinuousOn.intervalIntegrable (hG.mono ?_)
    intro t ht
    rw [uIcc_of_ge (le_max_right _ _)] at ht; exact lt_of_lt_of_le hy ht.1
  have := intervalIntegral.integral_hasDerivAt_right hI2
    (hG.stronglyMeasurableAtFilter isOpen_Ioi y hy) (hG.continuousAt (Ioi_mem_nhds hy))
  simpa using this.const_sub (∫ t in Ioi (max b y), G t)

/-- Smoothness of tail integrals. -/
theorem c04_aux_tail_contDiffOn (G : ℝ → ℂ) (a b : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (Ioi a))
    (hGi : IntegrableOn G (Ioi b)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∫ t in Ioi x, G t) (Ioi a) := by
  have hd := c04_aux_tail_hasDeriv G a b hG.continuousOn hGi
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun y hy => (hd y hy).differentiableAt.differentiableWithinAt, ?_⟩
  exact hG.neg.congr (fun y hy => (hd y hy).deriv)

/-- Higher derivatives of tail integrals. -/
theorem c04_aux_tail_iteratedDeriv (G : ℝ → ℂ) (a b : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (Ioi a))
    (hGi : IntegrableOn G (Ioi b)) (k : ℕ) (y : ℝ) (hy : a < y) :
    iteratedDeriv (k + 1) (fun x => ∫ t in Ioi x, G t) y = -iteratedDeriv k G y := by
  have hd := c04_aux_tail_hasDeriv G a b hG.continuousOn hGi
  rw [iteratedDeriv_succ']
  have : deriv (fun x => ∫ t in Ioi x, G t) =ᶠ[𝓝 y] fun x => -G x := by
    filter_upwards [Ioi_mem_nhds hy] with x hx using (hd x hx).deriv
  rw [this.iteratedDeriv_eq]
  exact iteratedDeriv_neg (n := k) (f := G) (a := y)


/-- `y^e ≤ 2^{|e|} ⟨y⟩^e` for `y ≥ 1`. -/
theorem c04_aux_rpow_le_jb_gen (y e : ℝ) (hy : 1 ≤ y) : y ^ e ≤ 2 ^ |e| * jb y ^ e := by
  have hy0 : 0 < y := by linarith
  have hyj : y ≤ jb y := (le_abs_self y).trans (c04_aux_abs_le_jb y)
  rcases le_total 0 e with he | he
  · calc y ^ e ≤ jb y ^ e := rpow_le_rpow hy0.le hyj he
      _ ≤ 2 ^ |e| * jb y ^ e := le_mul_of_one_le_left (rpow_nonneg (by unfold jb; positivity) _) (one_le_rpow (by norm_num) (abs_nonneg _))
  · have := c04_aux_rpow_le_jb' y (-e) hy (by linarith)
    rw [neg_neg] at this
    rwa [abs_of_nonpos he]

/-- `Z_{ε,μ}` is smooth at `y > 0` with `λ(y) > 0`. -/
theorem c04_aux_famZ_contDiffAt (p R ε : ℝ) (μ : ℂ) (hR : 0 < R)
    (hplus : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p)) (hμs : mu_star p ≠ 0) (y : ℝ) (hy : 0 < y)
    (hlam : 0 < fam_lambda p ε μ y) : ContDiffAt ℝ (⊤ : ℕ∞) (fam_Z p R ε μ) y := by
  rw [contDiffAt_infty]
  intro j
  have haC : ContDiffAt ℝ j (astar p) y := c04_aux_astar_contDiffAt p hplus hμs j y hy
  have hlamC : ContDiffAt ℝ j (fam_lambda p ε μ) y :=
    (c04_aux_lambda_contDiffOn p ε μ j).contDiffAt (Ioi_mem_nhds hy)
  have hLC : ContDiffAt ℝ j (fun t => ((fam_lambda p ε μ t ^ (-(p + 1) / 2) : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y (hlamC.rpow_const_of_ne hlam.ne')
  have hPsiC : ContDiffAt ℝ j (fam_Psi p R ε μ) y :=
    (c04_aux_Psi_contDiffOn p R ε μ hR j).contDiffAt (Ioi_mem_nhds hy)
  have hEC : ContDiffAt ℝ j (fun t => Complex.exp (Complex.I * ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ))) y :=
    Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hPsiC.sub contDiffAt_const)))
  exact ((contDiffAt_const.mul haC).mul hLC).mul hEC

/-- The integrand of `f_osc`. -/
def c04_aux_Gosc (p R ε : ℝ) (μ : ℂ) (t : ℝ) : ℂ :=
  fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3 - μ / mu_star p * fam_Z0 p R t

/-- `f_osc = -2 χ_R Re ∫_y^∞ G` everywhere. -/
theorem c04_aux_fosc_eq (p R ε : ℝ) (μ : ℂ) (hR : 0 < R) :
    fam_osc p R ε μ = fun y => -2 * fam_chiR R y * (∫ t in Ioi y, c04_aux_Gosc p R ε μ t).re := by
  funext y
  unfold fam_osc c04_aux_Gosc
  split_ifs with h
  · rfl
  · rw [c04_aux_chiR_zero R y hR (not_lt.mp h)]; ring

/-- Standing analytic data on the family. -/
theorem c04_aux_std (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fam_Z p R ε μ) (Ioi (R / 2)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c04_aux_Gosc p R ε μ) (Ioi (R / 2)) ∧
      IntegrableOn (fam_Z p R ε μ) (Ioi R) ∧
      IntegrableOn (fun t => fam_Z p R ε μ t ^ 3) (Ioi R) ∧
      IntegrableOn (c04_aux_Gosc p R ε μ) (Ioi R) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fam_osc p R ε μ) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hbasic, -, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hZb, _, _, hZi⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨C3, hC3, hC3b⟩ := hZb 0 1 one_pos
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), ?_⟩
  -- smoothness of `Z` for admissible parameters
  have hZs : ∀ R ≥ max R₁ R₂, ∀ ε ∈ Icc (0 : ℝ) (min ε₁ ε₂), ∀ μ ∈ Bbar p δ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fam_Z p R ε μ) (Ioi (R / 2)) := by
    intro R hR ε hε μ hμ t ht
    have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
    have hR0 : 0 < R := by linarith
    have ht0 : 0 < t := lt_trans (by linarith) (mem_Ioi.mp ht)
    have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
    obtain ⟨g1, g2, -, -⟩ := hbasic R hR1 ε hε1 μ hμ t ht
    exact (c04_aux_famZ_contDiffAt p R ε μ hR0 hplus hμs t ht0
      (c04_aux_lam_pos p ε μ t ht0 g1 g2).1).contDiffWithinAt
  have hZint : ∀ R ≥ max R₁ R₂, ∀ ε ∈ Icc (0 : ℝ) (min ε₁ ε₂), ∀ μ ∈ Bbar p δ,
      IntegrableOn (fam_Z p R ε μ) (Ioi R) ∧ IntegrableOn (fun t => fam_Z p R ε μ t ^ 3) (Ioi R) := by
    intro R hR ε hε μ hμ
    have hR2 : R ≥ R₂ := le_trans (le_max_right _ _) hR
    have hR0 : 0 < R := by linarith [le_trans hR₁ (le_trans (le_max_left _ _) hR)]
    have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
    have hc : ContinuousOn (fam_Z p R ε μ) (Ioi R) :=
      (hZs R hR ε hε μ hμ).continuousOn.mono (Ioi_subset_Ioi (by linarith))
    obtain ⟨hn, -⟩ := hZi R hR2 ε hε2 μ hμ R le_rfl
    refine ⟨?_, ?_⟩
    · exact (integrable_norm_iff (hc.aestronglyMeasurable measurableSet_Ioi)).mp hn
    · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := -3 * beta p) (by linarith) hR0).const_mul C3)
        ((hc.pow 3).aestronglyMeasurable measurableSet_Ioi) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have := (hC3b R hR2 ε hε2 μ hμ t (le_of_lt ht)).2.1
      simpa using this
  intro R hR ε hε μ hμ
  have hR0 : 0 < R := by linarith [le_trans hR₁ (le_trans (le_max_left _ _) hR)]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (min ε₁ ε₂) := ⟨le_rfl, (lt_min hε₁.1 hε₂.1).le⟩
  have hμ0 : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  have hZ := hZs R hR ε hε μ hμ
  have hZ0 : ContDiffOn ℝ (⊤ : ℕ∞) (fam_Z0 p R) (Ioi (R / 2)) := hZs R hR 0 h0 _ hμ0
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (c04_aux_Gosc p R ε μ) (Ioi (R / 2)) := by
    unfold c04_aux_Gosc
    exact (hZ.add (contDiffOn_const.mul (hZ.pow 3))).sub (contDiffOn_const.mul hZ0)
  obtain ⟨i1, i3⟩ := hZint R hR ε hε μ hμ
  obtain ⟨i0, -⟩ := hZint R hR 0 h0 _ hμ0
  have hGi : IntegrableOn (c04_aux_Gosc p R ε μ) (Ioi R) := by
    unfold c04_aux_Gosc
    exact (i1.add (i3.const_mul _)).sub (i0.const_mul _)
  refine ⟨hZ, hG, i1, i3, hGi, ?_⟩
  rw [c04_aux_fosc_eq p R ε μ hR0, contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge (R / 2) y with hy | hy
  · have hF := (c04_aux_tail_contDiffOn _ (R / 2) R hG hGi).contDiffAt (Ioi_mem_nhds hy)
    exact (contDiffAt_const.mul (c04_aux_chiR_smooth R).contDiffAt).mul
      (Complex.reCLM.contDiff.contDiffAt.comp y hF)
  · have : (fun y => -2 * fam_chiR R y * (∫ t in Ioi y, c04_aux_Gosc p R ε μ t).re) =ᶠ[𝓝 y]
        fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show y < R by linarith)] with t ht
      rw [c04_aux_chiR_zero R t hR0 (le_of_lt ht)]; ring
    exact contDiffAt_const.congr_of_eventuallyEq this


/-- `|∂^m χ_R| ≤ B_m` for `R ≥ 1`. -/
theorem c04_aux_chiR_iter (m : ℕ) : ∃ B ≥ (0 : ℝ), ∀ R ≥ (1 : ℝ), ∀ y,
    |iteratedDeriv m (fam_chiR R) y| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := c04_aux_chiPlus_iter m
  refine ⟨B, hB0, fun R hR y => ?_⟩
  have hR0 : 0 < R := by linarith
  have : fam_chiR R = fun t => chiPlus (R⁻¹ * t) := by
    funext u; rw [fam_chiR, div_eq_inv_mul]
  rw [this, iteratedDeriv_comp_const_mul (c04_aux_chiPlus_smooth.of_le (by exact_mod_cast le_top)) R⁻¹,
    abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hR0)]
  calc R⁻¹ ^ m * |iteratedDeriv m chiPlus (R⁻¹ * y)| ≤ 1 * B :=
        mul_le_mul (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hR)) (hB _).1 (abs_nonneg _)
          zero_le_one
    _ = B := one_mul B

/-- Leibniz bound for `∂^j f_osc` on `(R,∞)` from bounds on `F = ∫_y^∞ G` and on `∂^i G`. -/
theorem c04_aux_fosc_iter_bound (p : ℝ) (hp0 : 0 < p) (j : ℕ) : ∃ K ≥ (0 : ℝ),
    ∀ R ≥ (2 : ℝ), ∀ ε : ℝ, ∀ μ : ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) (c04_aux_Gosc p R ε μ) (Ioi (R / 2)) →
      IntegrableOn (c04_aux_Gosc p R ε μ) (Ioi R) →
      ∀ A b : ℝ, 0 ≤ A → ∀ y > R,
        ‖∫ t in Ioi y, c04_aux_Gosc p R ε μ t‖ ≤ A * y ^ b →
        (∀ i < j, ‖iteratedDeriv i (c04_aux_Gosc p R ε μ) y‖ ≤ A * y ^ (b + (i + 1) / p)) →
        |iteratedDeriv j (fam_osc p R ε μ) y| ≤ K * A * y ^ (b + j / p) := by
  choose B hB0 hB using c04_aux_chiR_iter
  set Bs := ∑ i ∈ Finset.range (j + 1), B i with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg (fun i _ => hB0 i)
  refine ⟨2 * (2 ^ j * Bs), by positivity, ?_⟩
  intro R hR ε μ hG hGi A b hA y hy hF hGb
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  set G := c04_aux_Gosc p R ε μ with hGdef
  set F := fun x => ∫ t in Ioi x, G t with hFdef
  have hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (Ioi (R / 2)) := c04_aux_tail_contDiffOn G (R / 2) R hG hGi
  have hyR2 : R / 2 < y := by linarith
  have hFC : ContDiffAt ℝ (⊤ : ℕ∞) F y := hFs.contDiffAt (Ioi_mem_nhds hyR2)
  have hReC : ContDiffAt ℝ j (fun x => (F x).re) y :=
    (Complex.reCLM.contDiff.contDiffAt.comp y hFC).of_le (by exact_mod_cast le_top)
  have hχC : ContDiffAt ℝ j (fam_chiR R) y :=
    (c04_aux_chiR_smooth R).contDiffAt.of_le (by exact_mod_cast le_top)
  have heq : fam_osc p R ε μ = fun x => (-2 : ℝ) * ((fam_chiR R * fun x => (F x).re) x) := by
    rw [c04_aux_fosc_eq p R ε μ hR0]; funext x; simp only [Pi.mul_apply, hFdef, hGdef]; ring
  have hPC : ContDiffAt ℝ j (fam_chiR R * fun x => (F x).re) y := hχC.mul hReC
  rw [heq, iteratedDeriv_const_mul _ hPC, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
  have hL := c04_aux_leibniz (fam_chiR R) (fun x => (F x).re) y hy0 j hχC hReC Bs A 0 b (1 / p)
    (fun i hi => by
      rw [Real.norm_eq_abs]
      refine (hB i R (by linarith) y).trans ?_
      have h1 : B i ≤ Bs := Finset.single_le_sum (f := B) (fun i _ => hB0 i)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      have h2 : 1 ≤ y ^ ((0 : ℝ) + i * (1 / p)) := one_le_rpow hy1 (by positivity)
      nlinarith)
    (fun i hi => by
      rw [Real.norm_eq_abs]
      rcases i with _ | i
      · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, zero_mul, add_zero]
        exact (Complex.abs_re_le_norm _).trans hF
      · rw [c04_aux_iteratedDeriv_re F y (i + 1) (hFC.of_le (by exact_mod_cast le_top)),
          c04_aux_tail_iteratedDeriv G (R / 2) R hG hGi i y hyR2]
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_neg]
        refine (hGb i (by omega)).trans (le_of_eq ?_)
        congr 2; push_cast; ring)
  rw [Real.norm_eq_abs] at hL
  calc 2 * |iteratedDeriv j (fam_chiR R * fun x => (F x).re) y| ≤
        2 * (2 ^ j * (Bs * A) * y ^ (0 + b + j * (1 / p))) := by linarith
    _ = 2 * (2 ^ j * Bs) * A * y ^ (b + j / p) := by
        rw [show (0 : ℝ) + b + j * (1 / p) = b + j / p by ring]; ring


/-- `A = a_* λ^{-q}` is smooth on `(0,∞)` where `λ > 0`. -/
theorem c04_aux_Aq_contDiffAt (p ε : ℝ) (μ : ℂ) (q : ℝ)
    (hplus : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p)) (hμs : mu_star p ≠ 0) (y : ℝ) (hy : 0 < y)
    (hlam : 0 < fam_lambda p ε μ y) (n : ℕ) :
    ContDiffAt ℝ n (fun s => astar p s * ((fam_lambda p ε μ s ^ (-q) : ℝ) : ℂ)) y := by
  have haC : ContDiffAt ℝ n (astar p) y := c04_aux_astar_contDiffAt p hplus hμs n y hy
  have hlamC : ContDiffAt ℝ n (fam_lambda p ε μ) y :=
    (c04_aux_lambda_contDiffOn p ε μ n).contDiffAt (Ioi_mem_nhds hy)
  exact haC.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y (hlamC.rpow_const_of_ne hlam.ne'))

/-- The algebraic identity `Z = μ e^{-iπ/4} a_* λ^{-q₁} e^{iΨ} λ` (`q₁ = (p+3)/2`). -/
theorem c04_aux_Z_eq_A (p R ε : ℝ) (μ : ℂ) (t : ℝ) (hlam : 0 < fam_lambda p ε μ t) :
    fam_Z p R ε μ t = μ * Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) *
      (astar p t * ((fam_lambda p ε μ t ^ (-((p + 3) / 2)) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) * (fam_lambda p ε μ t : ℂ) := by
  have h1 : fam_lambda p ε μ t ^ (-((p + 3) / 2)) * fam_lambda p ε μ t =
      fam_lambda p ε μ t ^ (-(p + 1) / 2) := by
    rw [← rpow_add_one hlam.ne']; congr 1; ring
  have h2 : Complex.exp (Complex.I * ((fam_Psi p R ε μ t - π / 4 : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) * Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  unfold fam_Z
  rw [h2, ← h1, Complex.ofReal_mul]
  ring

/-- Integration-by-parts formula of lem:c04_Z_primitive. -/
theorem c04_aux_Zprim_formula (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        IntegrableOn (fam_Z p R ε μ) (Ioi y) ∧
        IntegrableOn (fun t => deriv (fun s => astar p s *
            ((fam_lambda p ε μ s ^ (-((p + 3) / 2)) : ℝ) : ℂ)) t *
          Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) (Ioi y) ∧
        ∫ t in Ioi y, fam_Z p R ε μ t =
          Complex.I * fam_Z p R ε μ y / (fam_lambda p ε μ y : ℂ) +
          Complex.I * μ * Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) *
            ∫ t in Ioi y, deriv (fun s => astar p s *
                ((fam_lambda p ε μ s ^ (-((p + 3) / 2)) : ℝ) : ℂ)) t *
              Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp (by linarith)
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hbasic, -, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hzb, -⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨ε₃, hε₃, R₃, hR₃, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  have hq1 : (0 : ℝ) < (p + 3) / 2 := by positivity
  obtain ⟨CA, hCA, hCAb⟩ := hzb 1 ((p + 3) / 2) hq1
  obtain ⟨Cz, hCz, hCzb⟩ := hzb 0 1 one_pos
  refine ⟨min (min ε₁ ε₂) ε₃, ⟨lt_min (lt_min hε₁.1 hε₂.1) hε₃.1,
    (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)⟩, max (max R₁ R₂) R₃,
    le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _)), fun R hR ε hε μ hμ y hy => ?_⟩
  have hR1 : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hR2 : R ≥ R₂ := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hR3 : R ≥ R₃ := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε3 : ε ∈ Icc (0 : ℝ) ε₃ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hy0 : 0 < y := by linarith
  have hlam : ∀ t > R / 2, 0 < fam_lambda p ε μ t := fun t ht => by
    obtain ⟨g1, g2, -, -⟩ := hbasic R hR1 ε hε1 μ hμ t ht
    exact (c04_aux_lam_pos p ε μ t (by linarith) g1 g2).1
  obtain ⟨-, -, i1, -, -, -⟩ := hstd R hR3 ε hε3 μ hμ
  have hZi : IntegrableOn (fam_Z p R ε μ) (Ioi y) := i1.mono_set (Ioi_subset_Ioi hy)
  set A : ℝ → ℂ := fun s => astar p s * ((fam_lambda p ε μ s ^ (-((p + 3) / 2)) : ℝ) : ℂ) with hA
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) with hE
  set K : ℂ := μ * Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) with hK
  have hAs : ContDiffOn ℝ 2 A (Ioi (R / 2)) := fun t ht =>
    (c04_aux_Aq_contDiffAt p ε μ _ hplus hμs t (by simp only [mem_Ioi] at ht; linarith)
      (hlam t ht) 2).contDiffWithinAt
  have hAd : ∀ t > R / 2, HasDerivAt A (deriv A t) t := fun t ht =>
    ((hAs.contDiffAt (Ioi_mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
  have hAc : ContinuousOn (deriv A) (Ioi (R / 2)) :=
    hAs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hEd : ∀ t > R / 2, HasDerivAt E (E t * (Complex.I * (fam_lambda p ε μ t : ℂ))) t := by
    intro t ht
    have h1 := ((c04_aux_Psi_hasDeriv p R ε μ hR0 t (by linarith)).ofReal_comp).const_mul Complex.I
    exact h1.cexp
  have hEc : ContinuousOn E (Ioi (R / 2)) := fun t ht => (hEd t ht).continuousAt.continuousWithinAt
  have hEn : ∀ t, ‖E t‖ = 1 := fun t => c04_aux_norm_exp_I _
  have hyR2 : y > R / 2 := by linarith
  -- integrability of `A' E`
  have hAb : ∀ t ≥ R, ‖deriv A t‖ ≤ CA * t ^ (-((p + 3) / 2) / p - 1) := by
    intro t ht
    have := (hCAb R hR2 ε hε2 μ hμ t ht).2.2.2
    rw [iteratedDeriv_one] at this
    simpa using this
  have hexp1 : -((p + 3) / 2) / p - 1 < -1 := by
    have : 0 < (p + 3) / 2 / p := by positivity
    rw [neg_div]; linarith
  have hAEi : IntegrableOn (fun t => deriv A t * E t) (Ioi y) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hexp1 hy0).const_mul CA)
      ((hAc.mul hEc).mono (Ioi_subset_Ioi hyR2.le) |>.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, hEn, mul_one]
    exact hAb t (le_trans hy (le_of_lt ht))
  refine ⟨hZi, hAEi, ?_⟩
  -- the primitive `f = K A E`
  have hZA : ∀ t > R / 2, fam_Z p R ε μ t = K * (A t * E t) * (fam_lambda p ε μ t : ℂ) := by
    intro t ht
    rw [c04_aux_Z_eq_A p R ε μ t (hlam t ht)]
  have hfd : ∀ x ∈ Ici y, HasDerivAt (fun t => K * (A t * E t))
      (K * (deriv A x * E x) + Complex.I * fam_Z p R ε μ x) x := by
    intro x hx
    have hx' : x > R / 2 := lt_of_lt_of_le hyR2 hx
    have h := ((hAd x hx').mul (hEd x hx')).const_mul K
    convert h using 1
    rw [hZA x hx']; ring
  have hfi : IntegrableOn (fun t => K * (deriv A t * E t) + Complex.I * fam_Z p R ε μ t) (Ioi y) :=
    (hAEi.const_mul K).add (hZi.const_mul Complex.I)
  have hft : Tendsto (fun t => K * (A t * E t)) atTop (𝓝 0) := by
    have hb : ∀ᶠ t in atTop, ‖K * (A t * E t)‖ ≤ Cz * t ^ (-(beta p + 1 / p)) := by
      filter_upwards [eventually_ge_atTop R] with t ht
      have hl := hlam t (by linarith)
      have hdiv : K * (A t * E t) = fam_Z p R ε μ t / (fam_lambda p ε μ t : ℂ) := by
        rw [hZA t (by linarith), mul_div_assoc, div_self (Complex.ofReal_ne_zero.mpr hl.ne'), mul_one]
      rw [hdiv]
      have := (hCzb R hR2 ε hε2 μ hμ t ht).2.2.1
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, zero_div, add_zero] at this
      rw [show -(beta p + 1 / p) = -beta p - 1 / p by ring]; exact this
    have h0 : Tendsto (fun t : ℝ => Cz * t ^ (-(beta p + 1 / p))) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := beta p + 1 / p) (by positivity)).const_mul Cz
      simpa using this
    exact squeeze_zero_norm' hb h0
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hfd hfi hft
  rw [integral_add (hAEi.const_mul K) (hZi.const_mul Complex.I), integral_const_mul,
    integral_const_mul] at hint
  have hfy : K * (A y * E y) = fam_Z p R ε μ y / (fam_lambda p ε μ y : ℂ) := by
    rw [hZA y hyR2, mul_div_assoc, div_self (Complex.ofReal_ne_zero.mpr (hlam y hyR2).ne'), mul_one]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [hK] at hint hfy
  linear_combination (-Complex.I) * hint + Complex.I * hfy + (∫ t in Ioi y, fam_Z p R ε μ t) * hI


/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_expI_diff (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have e : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [e, norm_mul, c04_aux_norm_exp_I, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at this

/-- `∫_y^∞ C t^{e} = C y^{e+1}/(-(e+1))` bound helper. -/
theorem c04_aux_tail_rpow (C e y : ℝ) (he : e < -1) (hy : 0 < y) :
    IntegrableOn (fun t => C * t ^ e) (Ioi y) ∧
    ∫ t in Ioi y, C * t ^ e = C / (-(e + 1)) * y ^ (e + 1) := by
  refine ⟨(integrableOn_Ioi_rpow_of_lt he hy).const_mul C, ?_⟩
  rw [integral_const_mul, integral_Ioi_rpow_of_lt he hy]
  have : e + 1 ≠ 0 := by linarith
  field_simp

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c04_Z_primitive.  For `y ≥ R`, with `q₁ = (p+3)/2`,
`∫_y^∞ Z = iZ(y)/λ(y) + iμe^{-iπ/4} ∫_y^∞ ∂_t(a_*λ^{-q₁}) e^{iΨ} dt` (absolutely convergent), and
the bounds (a), (b), (c). -/
theorem c04_Z_primitive (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        IntegrableOn (fam_Z p R ε μ) (Ioi y) ∧
        IntegrableOn (fun t => deriv (fun s => astar p s *
            ((fam_lambda p ε μ s ^ (-((p + 3) / 2)) : ℝ) : ℂ)) t *
          Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) (Ioi y) ∧
        ∫ t in Ioi y, fam_Z p R ε μ t =
          Complex.I * fam_Z p R ε μ y / (fam_lambda p ε μ y : ℂ) +
          Complex.I * μ * Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) *
            ∫ t in Ioi y, deriv (fun s => astar p s *
                ((fam_lambda p ε μ s ^ (-((p + 3) / 2)) : ℝ) : ℂ)) t *
              Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ))) ∧
      (∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        -- (a)
        ‖∫ t in Ioi y, fam_Z p R ε μ t‖ ≤ C * y ^ (-beta p - 1 / p) ∧
        -- (b)
        ‖∫ t in Ioi y, (fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t)‖ ≤
          C * ε * y ^ (-p - beta p) ∧
        -- (c)
        ‖(c_cubic p ε : ℂ) * ∫ t in Ioi y, fam_Z p R ε μ t ^ 3‖ ≤ C * ε * y ^ (1 - 3 * beta p) ∧
        y ^ (1 - 3 * beta p) ≤ min (y ^ (-p - beta p)) (y ^ (-beta p - 1 / p))) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs' : 0 < ‖mu_star p‖ := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp hμs'
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  have hq1p : (p + 3) / 2 / p = beta p + 1 / p := by unfold beta; field_simp; ring
  have hq1 : (0 : ℝ) < (p + 3) / 2 := by positivity
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hform⟩ := c04_aux_Zprim_formula p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hzb, -⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨ε₃, hε₃, R₃, hR₃, hzd⟩ := c04_Z_difference p hp hp1 δ hδ hδμ
  obtain ⟨ε₄, hε₄, R₄, hR₄, hlpd⟩ := c04_lambda_psi_difference p hp hp1 δ hδ hδμ
  obtain ⟨ε₅, hε₅, R₅, hR₅, hbasic, -, -, hb3⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₆, hε₆, R₆, hR₆, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  obtain ⟨⟨Cc, hCc, hcs⟩, -, -, -⟩ := c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)
  obtain ⟨CA, hCA, hCAb⟩ := hzb 1 ((p + 3) / 2) hq1
  obtain ⟨Cz, hCz, hCzb⟩ := hzb 0 1 one_pos
  obtain ⟨Cd, hCd, hCdb⟩ := hzd 0 ((p + 3) / 2) hq1
  obtain ⟨Cl, hCl, hClb⟩ := hlpd 0
  set ε₀ := min (min (min ε₁ ε₂) (min ε₃ ε₄)) (min ε₅ ε₆) with hε₀
  set R₀ := max (max (max R₁ R₂) (max R₃ R₄)) (max R₅ R₆) with hR₀
  have hε₀pos : 0 < ε₀ := lt_min (lt_min (lt_min hε₁.1 hε₂.1) (lt_min hε₃.1 hε₄.1)) (lt_min hε₅.1 hε₆.1)
  have hε₀1 : ε₀ ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2))
  have hR₀2 : R₀ ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hεs : ∀ ε ∈ Icc (0 : ℝ) ε₀, ε ∈ Icc (0 : ℝ) ε₁ ∧ ε ∈ Icc (0 : ℝ) ε₂ ∧ ε ∈ Icc (0 : ℝ) ε₃ ∧
      ε ∈ Icc (0 : ℝ) ε₄ ∧ ε ∈ Icc (0 : ℝ) ε₅ ∧ ε ∈ Icc (0 : ℝ) ε₆ := fun ε hε =>
    ⟨⟨hε.1, hε.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))⟩,
     ⟨hε.1, hε.2.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))⟩,
     ⟨hε.1, hε.2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩,
     ⟨hε.1, hε.2.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩,
     ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩,
     ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩⟩
  have hRs : ∀ R ≥ R₀, R ≥ R₁ ∧ R ≥ R₂ ∧ R ≥ R₃ ∧ R ≥ R₄ ∧ R ≥ R₅ ∧ R ≥ R₆ := fun R hR =>
    ⟨le_trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))) hR,
     le_trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))) hR,
     le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))) hR,
     le_trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))) hR,
     le_trans ((le_max_left _ _).trans (le_max_right _ _)) hR,
     le_trans ((le_max_right _ _).trans (le_max_right _ _)) hR⟩
  clear_value ε₀ R₀
  refine ⟨ε₀, ⟨hε₀pos, hε₀1⟩, R₀, hR₀2, fun R hR ε hε μ hμ y hy => ?_, ?_⟩
  · obtain ⟨hR1, -⟩ := hRs R hR
    exact hform R hR1 ε (hεs ε hε).1 μ hμ y hy
  have hβp : 0 < beta p + p := by linarith
  have h3β : 0 < 3 * beta p - 1 := by linarith
  have hqp : 0 < beta p + 1 / p := by positivity
  set Ca := Cz + 2 * ‖mu_star p‖ * (CA / (beta p + 1 / p)) with hCa
  set Cb := Cd + 2 * ‖mu_star p‖ * ((CA * Cl + Cd) / (beta p + p)) with hCb
  set Cc3 := Cc * (Cz / (3 * beta p - 1)) with hCc3
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hCc30 : 0 ≤ Cc3 := by rw [hCc3]; positivity
  refine ⟨Ca + Cb + Cc3 + 1, by positivity, fun R hR ε hε μ hμ y hy => ?_⟩
  obtain ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩ := hRs R hR
  obtain ⟨hε1, hε2, hε3, hε4, hε5, hε6⟩ := hεs ε hε
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hyR2 : y > R / 2 := by linarith
  have hYp : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hε₀1⟩
  have hμ0 : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  have h05 : (0 : ℝ) ∈ Icc (0 : ℝ) ε₅ := ⟨le_rfl, hε₅.1.le⟩
  have hμn : ‖μ‖ ≤ 2 * ‖mu_star p‖ := by
    have := norm_le_of_mem_closedBall hμ; linarith
  have hen : ‖Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ)))‖ = 1 := by
    rw [show -(Complex.I * ((π / 4 : ℝ) : ℂ)) = Complex.I * ((-(π / 4) : ℝ) : ℂ) by push_cast; ring]
    exact c04_aux_norm_exp_I _
  obtain ⟨-, -, hcc, -, -, -, -⟩ := hcs ε hεI μ hμn
  set A : ℝ → ℂ := fun s => astar p s * ((fam_lambda p ε μ s ^ (-((p + 3) / 2)) : ℝ) : ℂ) with hA
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * (fam_Psi p R ε μ t : ℂ)) with hE
  set A0 : ℝ → ℂ := fun s => astar p s * ((fam_lambda p 0 (mu_star p) s ^ (-((p + 3) / 2)) : ℝ) : ℂ)
    with hA0
  set E0 : ℝ → ℂ := fun t => Complex.exp (Complex.I * (fam_Psi p R 0 (mu_star p) t : ℂ)) with hE0
  obtain ⟨hZi, hJi, hF⟩ := hform R hR1 ε hε1 μ hμ y hy
  obtain ⟨hZ0i, hJ0i, hF0⟩ := hform R hR1 0 ⟨le_rfl, hε₁.1.le⟩ _ hμ0 y hy
  have hAb : ∀ t ≥ R, ‖deriv A t‖ ≤ CA * t ^ (-((p + 3) / 2) / p - 1) := by
    intro t ht
    have := (hCAb R hR2 ε hε2 μ hμ t ht).2.2.2
    rw [iteratedDeriv_one] at this
    simpa using this
  have hexp1 : -((p + 3) / 2) / p - 1 < -1 := by
    have : 0 < (p + 3) / 2 / p := by positivity
    rw [neg_div]; linarith
  have hJb : ‖∫ t in Ioi y, deriv A t * E t‖ ≤ CA / (beta p + 1 / p) * y ^ (-(beta p + 1 / p)) := by
    obtain ⟨hgi, hgv⟩ := c04_aux_tail_rpow CA _ y hexp1 hy0
    refine (norm_integral_le_of_norm_le hgi ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
    · rw [norm_mul, c04_aux_norm_exp_I, mul_one]; exact hAb t (le_trans hy (le_of_lt ht))
    · rw [hgv, neg_div, hq1p]; congr 2 <;> ring
  -- (a)
  have pa : ‖∫ t in Ioi y, fam_Z p R ε μ t‖ ≤ Ca * y ^ (-beta p - 1 / p) := by
    rw [hF]
    have h1 : ‖Complex.I * fam_Z p R ε μ y / (fam_lambda p ε μ y : ℂ)‖ ≤ Cz * y ^ (-beta p - 1 / p) := by
      rw [mul_div_assoc, norm_mul, Complex.norm_I, one_mul]
      have := (hCzb R hR2 ε hε2 μ hμ y hy).2.2.1
      simpa using this
    have h2 : ‖Complex.I * μ * Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) *
        ∫ t in Ioi y, deriv A t * E t‖ ≤ 2 * ‖mu_star p‖ * (CA / (beta p + 1 / p) * y ^ (-beta p - 1 / p)) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, hen, one_mul, mul_one]
      rw [show -beta p - 1 / p = -(beta p + 1 / p) by ring]
      exact mul_le_mul hμn hJb (norm_nonneg _) (by positivity)
    have := norm_add_le (Complex.I * fam_Z p R ε μ y / (fam_lambda p ε μ y : ℂ))
      (Complex.I * μ * Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) * ∫ t in Ioi y, deriv A t * E t)
    rw [hCa]; linarith
  -- (b)
  have pb : ‖∫ t in Ioi y, (fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t)‖ ≤
      Cb * ε * y ^ (-p - beta p) := by
    set q1 := (p + 3) / 2 with hq1def
    set e := Complex.exp (-(Complex.I * ((π / 4 : ℝ) : ℂ))) with he
    have hlamy : 0 < fam_lambda p ε μ y := by
      obtain ⟨g1, g2, -, -⟩ := hbasic R hR5 ε hε5 μ hμ y hyR2
      exact (c04_aux_lam_pos p ε μ y hy0 g1 g2).1
    have hlam0y : 0 < fam_lambda p 0 (mu_star p) y := by
      obtain ⟨g1, g2, -, -⟩ := hbasic R hR5 0 h05 _ hμ0 y hyR2
      exact (c04_aux_lam_pos p 0 _ y hy0 g1 g2).1
    obtain ⟨b31, b32, -, -⟩ := hb3 R hR5 _ hμ0 y hyR2
    -- boundary terms
    have hbd : fam_Z p R ε μ y / (fam_lambda p ε μ y : ℂ) - μ / mu_star p *
        (fam_Z p R 0 (mu_star p) y / (fam_lambda p 0 (mu_star p) y : ℂ)) =
        e * c04_Dq p R ε μ q1 y := by
      rw [c04_aux_Z_eq_A p R ε μ y hlamy, c04_aux_Z_eq_A p R 0 _ y hlam0y, b31, b32]
      have h1 : (fam_lambda p ε μ y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlamy.ne'
      have h2 : (lambda0 p y : ℂ) ≠ 0 := by rw [← b31]; exact Complex.ofReal_ne_zero.mpr hlam0y.ne'
      unfold c04_Dq
      field_simp
      ring
    have hDb : ‖c04_Dq p R ε μ q1 y‖ ≤ Cd * ε * y ^ (-p - beta p) := by
      have := (hCdb R hR3 ε hε3 μ hμ y hy).1
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, zero_div, add_zero] at this
      refine this.trans (le_of_eq ?_)
      rw [hq1p]; congr 1; ring
    -- the integrals
    have hJJ : ‖(∫ t in Ioi y, deriv A t * E t) - ∫ t in Ioi y, deriv A0 t * E0 t‖ ≤
        (CA * Cl + Cd) / (beta p + p) * ε * y ^ (-p - beta p) := by
      rw [← integral_sub hJi hJ0i]
      have hexp : -(beta p + p + 1) < -1 := by linarith
      obtain ⟨hgi, hgv⟩ := c04_aux_tail_rpow ((CA * Cl + Cd) * ε) _ y hexp hy0
      refine (norm_integral_le_of_norm_le hgi ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
      · have ht' : t ≥ R := le_trans hy (le_of_lt ht)
        have ht0 : 0 < t := by linarith
        have ht1 : 1 ≤ t := by linarith
        have htR2 : t > R / 2 := by linarith
        obtain ⟨c1, c2, -, -⟩ := hb3 R hR5 _ hμ0 t htR2
        have hE0 : E0 t = Complex.exp (Complex.I * (Psi0 p t : ℂ)) := by rw [hE0]; simp only [c2]
        have hEE : ‖E t - E0 t‖ ≤ Cl * ε * t ^ (1 / p - p) := by
          rw [hE0]
          refine (c04_aux_expI_diff _ _).trans ?_
          have := (hClb R hR4 ε hε4 μ hμ t ht').2
          simpa using this
        -- `A₀ = a_* λ₀^{-q₁}` near `t`
        have hA0ev : A0 =ᶠ[𝓝 t] fun s => astar p s * ((lambda0 p s ^ (-q1) : ℝ) : ℂ) := by
          filter_upwards [Ioi_mem_nhds htR2] with s hs
          rw [hA0]; simp only [(hb3 R hR5 _ hμ0 s hs).1]
        have hlt : 0 < fam_lambda p ε μ t := by
          obtain ⟨g1, g2, -, -⟩ := hbasic R hR5 ε hε5 μ hμ t htR2
          exact (c04_aux_lam_pos p ε μ t ht0 g1 g2).1
        have hl0t : 0 < fam_lambda p 0 (mu_star p) t := by
          obtain ⟨g1, g2, -, -⟩ := hbasic R hR5 0 h05 _ hμ0 t htR2
          exact (c04_aux_lam_pos p 0 _ t ht0 g1 g2).1
        have hAdiff : DifferentiableAt ℝ A t :=
          (c04_aux_Aq_contDiffAt p ε μ q1 hplus hμs t ht0 hlt 1).differentiableAt (by norm_num)
        have hA0diff : DifferentiableAt ℝ (fun s => astar p s * ((lambda0 p s ^ (-q1) : ℝ) : ℂ)) t :=
          ((c04_aux_Aq_contDiffAt p 0 _ q1 hplus hμs t ht0 hl0t 1).differentiableAt (by norm_num)).congr_of_eventuallyEq
            hA0ev.symm
        have hdd : deriv A t - deriv A0 t = deriv (fun s => astar p s * ((fam_lambda p ε μ s ^ (-q1) : ℝ) : ℂ) -
            astar p s * ((lambda0 p s ^ (-q1) : ℝ) : ℂ)) t := by
          rw [hA0ev.deriv_eq, deriv_fun_sub hAdiff hA0diff]
        have hdb : ‖deriv A t - deriv A0 t‖ ≤ Cd * ε * t ^ (-(beta p + p + 1)) := by
          rw [hdd]
          have := (hCdb R hR3 ε hε3 μ hμ t ht').2.1
          simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at this
          refine this.trans (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le ht1 ?_)
            (mul_nonneg hCd.le hε.1))
          rw [neg_div, hq1p]; have : 0 < 1 / p := by positivity
          linarith
        have hab := hAb t ht'
        have hsplit : deriv A t * E t - deriv A0 t * E0 t =
            deriv A t * (E t - E0 t) + (deriv A t - deriv A0 t) * E0 t := by ring
        rw [hsplit]
        have hn1 : ‖deriv A t * (E t - E0 t)‖ ≤ CA * Cl * ε * t ^ (-(beta p + p + 1)) := by
          rw [norm_mul]
          refine (mul_le_mul hab hEE (norm_nonneg _) (by positivity)).trans (le_of_eq ?_)
          rw [show CA * t ^ (-q1 / p - 1) * (Cl * ε * t ^ (1 / p - p)) =
            CA * Cl * ε * (t ^ (-q1 / p - 1) * t ^ (1 / p - p)) by ring, ← rpow_add ht0]
          congr 2
          rw [neg_div, hq1p]; ring
        have hn2 : ‖(deriv A t - deriv A0 t) * E0 t‖ ≤ Cd * ε * t ^ (-(beta p + p + 1)) := by
          rw [norm_mul, hE0, c04_aux_norm_exp_I, mul_one]; exact hdb
        refine (norm_add_le _ _).trans ?_
        have : (CA * Cl + Cd) * ε * t ^ (-(beta p + p + 1)) =
            CA * Cl * ε * t ^ (-(beta p + p + 1)) + Cd * ε * t ^ (-(beta p + p + 1)) := by ring
        linarith
      · rw [hgv]
        rw [show -(-(beta p + p + 1) + 1) = beta p + p by ring,
          show -(beta p + p + 1) + 1 = -p - beta p by ring]
        ring
    have hsplitI : ∫ t in Ioi y, (fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) =
        (∫ t in Ioi y, fam_Z p R ε μ t) - μ / mu_star p * ∫ t in Ioi y, fam_Z p R 0 (mu_star p) t := by
      unfold fam_Z0
      rw [integral_sub hZi (hZ0i.const_mul _), integral_const_mul]
    have hqμ : μ / mu_star p * mu_star p = μ := div_mul_cancel₀ μ hμs
    have key : ∫ t in Ioi y, (fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) =
        Complex.I * (e * c04_Dq p R ε μ q1 y) + Complex.I * μ * e *
          ((∫ t in Ioi y, deriv A t * E t) - ∫ t in Ioi y, deriv A0 t * E0 t) := by
      rw [hsplitI, hF, hF0, ← hbd]
      linear_combination (-(Complex.I * e * (∫ t in Ioi y, deriv A0 t * E0 t))) * hqμ
    rw [key]
    have n1 : ‖Complex.I * (e * c04_Dq p R ε μ q1 y)‖ ≤ Cd * ε * y ^ (-p - beta p) := by
      rw [norm_mul, norm_mul, Complex.norm_I, he, hen, one_mul, one_mul]; exact hDb
    have n2 : ‖Complex.I * μ * e * ((∫ t in Ioi y, deriv A t * E t) - ∫ t in Ioi y, deriv A0 t * E0 t)‖ ≤
        2 * ‖mu_star p‖ * ((CA * Cl + Cd) / (beta p + p) * ε * y ^ (-p - beta p)) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, he, hen, one_mul, mul_one]
      exact mul_le_mul hμn hJJ (norm_nonneg _) (by positivity)
    refine (norm_add_le _ _).trans ?_
    have : Cb * ε * y ^ (-p - beta p) = Cd * ε * y ^ (-p - beta p) +
        2 * ‖mu_star p‖ * ((CA * Cl + Cd) / (beta p + p) * ε * y ^ (-p - beta p)) := by
      rw [hCb]; ring
    linarith
  -- (c)
  have pc : ‖(c_cubic p ε : ℂ) * ∫ t in Ioi y, fam_Z p R ε μ t ^ 3‖ ≤ Cc3 * ε * y ^ (1 - 3 * beta p) := by
    obtain ⟨-, -, -, i3, -, -⟩ := hstd R hR6 ε hε6 μ hμ
    have hexp3 : -3 * beta p < -1 := by linarith
    obtain ⟨hgi, hgv⟩ := c04_aux_tail_rpow Cz _ y hexp3 hy0
    have hn : ‖∫ t in Ioi y, fam_Z p R ε μ t ^ 3‖ ≤ Cz / (3 * beta p - 1) * y ^ (1 - 3 * beta p) := by
      refine (norm_integral_le_of_norm_le hgi ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht => ?_))).trans (le_of_eq ?_)
      · have := (hCzb R hR2 ε hε2 μ hμ t (le_trans hy (le_of_lt ht))).2.1
        simpa using this
      · rw [hgv]; congr 2 <;> ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hCc3]
    have := mul_le_mul hcc hn (norm_nonneg _) (mul_nonneg hCc.le hε.1)
    linarith
  have hmin : y ^ (1 - 3 * beta p) ≤ min (y ^ (-p - beta p)) (y ^ (-beta p - 1 / p)) := by
    have hb : beta p = (p + 1) / (2 * p) := rfl
    refine le_min (rpow_le_rpow_of_exponent_le hy1 ?_) (le_of_eq (by congr 1; rw [hb]; field_simp; ring))
    have : 1 + p ≤ 2 * beta p := by
      rw [hb, show 2 * ((p + 1) / (2 * p)) = (p + 1) / p by field_simp]
      rw [le_div_iff₀ hp0]; nlinarith
    linarith
  have hε0 := hε.1
  refine ⟨pa.trans (mul_le_mul_of_nonneg_right (by linarith) (hYp _)),
    pb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε0) (hYp _)),
    pc.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε0) (hYp _)), hmin⟩

/-- Bounds for `F = ∫_y^∞ G` and `∂^j G` (`G` the integrand of `f_osc`), for `y ≥ R`. -/
theorem c04_aux_G_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ j : ℕ, ∃ C > (0 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
        ‖∫ t in Ioi y, c04_aux_Gosc p R ε μ t‖ ≤ C * ε * y ^ (-p - beta p) ∧
        ‖∫ t in Ioi y, c04_aux_Gosc p R ε μ t‖ ≤ C * y ^ (-beta p - 1 / p) ∧
        ‖iteratedDeriv j (c04_aux_Gosc p R ε μ) y‖ ≤ C * ε * y ^ (-p - beta p + (j + 1) / p) ∧
        ‖iteratedDeriv j (c04_aux_Gosc p R ε μ) y‖ ≤ C * y ^ (-beta p - 1 / p + (j + 1) / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs' : 0 < ‖mu_star p‖ := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp hμs'
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨ε₁, hε₁, R₁, hR₁, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hzd⟩ := c04_Z_difference p hp hp1 δ hδ hδμ
  obtain ⟨ε₃, hε₃, R₃, hR₃, -, Cp, hCp, hprim⟩ := c04_Z_primitive p hp hp1 δ hδ hδμ
  obtain ⟨ε₄, hε₄, R₄, hR₄, hzb, -⟩ := c04_Z_bounds p hp hp1 δ hδ hδμ
  obtain ⟨⟨Cc, hCc, hcs⟩, -, -, -⟩ := c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)
  have hε₀pos : 0 < min (min ε₁ ε₂) (min ε₃ ε₄) := lt_min (lt_min hε₁.1 hε₂.1) (lt_min hε₃.1 hε₄.1)
  have hε₀1 : min (min ε₁ ε₂) (min ε₃ ε₄) ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)
  have hR₀2 : max (max R₁ R₂) (max R₃ R₄) ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨_, ⟨hε₀pos, hε₀1⟩, _, hR₀2, fun j => ?_⟩
  obtain ⟨Cd, hCd, hCdb⟩ := hzd j 1 one_pos
  obtain ⟨Cb, hCb, hCbb⟩ := hzb j 1 one_pos
  refine ⟨4 * Cp + Cd + Cc * Cb + 3 * Cb + 1, by positivity, fun R hR ε hε μ hμ y hy => ?_⟩
  have hR1 : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hR2 : R ≥ R₂ := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hR3 : R ≥ R₃ := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hR
  have hR4 : R ≥ R₄ := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hR
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε3 : ε ∈ Icc (0 : ℝ) ε₃ := ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε4 : ε ∈ Icc (0 : ℝ) ε₄ := ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hε01 : ε ≤ 1 := hε.2.trans hε₀1
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε01⟩
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) ε₁ := ⟨le_rfl, hε₁.1.le⟩
  have h04 : (0 : ℝ) ∈ Icc (0 : ℝ) ε₄ := ⟨le_rfl, hε₄.1.le⟩
  have hμ0 : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  have hμn : ‖μ‖ ≤ 2 * ‖mu_star p‖ := by
    have := norm_le_of_mem_closedBall hμ; linarith
  have hμq : ‖μ / mu_star p‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ hμs']; linarith
  have hR0 : 0 < R := by linarith
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hYp : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
  obtain ⟨-, -, hcc, -, -, -, -⟩ := hcs ε hεI μ hμn
  have hcc' : ‖((c_cubic p ε : ℝ) : ℂ)‖ ≤ Cc * ε := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hcc
  obtain ⟨hZs, -, i1, i3, -, -⟩ := hstd R hR1 ε hε1 μ hμ
  obtain ⟨hZ0s, -, i0, -, -, -⟩ := hstd R hR1 0 h01 _ hμ0
  obtain ⟨pa, pb, pc, pmin⟩ := hprim R hR3 ε hε3 μ hμ y hy
  obtain ⟨pa0, -, -, -⟩ := hprim R hR3 0 ⟨le_rfl, hε₃.1.le⟩ _ hμ0 y hy
  have hmin1 : y ^ (1 - 3 * beta p) ≤ y ^ (-p - beta p) := pmin.trans (min_le_left _ _)
  have hmin2 : y ^ (1 - 3 * beta p) ≤ y ^ (-beta p - 1 / p) := pmin.trans (min_le_right _ _)
  -- integrability on `(y,∞)`
  have j1 : IntegrableOn (fam_Z p R ε μ) (Ioi y) := i1.mono_set (Ioi_subset_Ioi hy)
  have j3 : IntegrableOn (fun t => fam_Z p R ε μ t ^ 3) (Ioi y) := i3.mono_set (Ioi_subset_Ioi hy)
  have j0 : IntegrableOn (fam_Z0 p R) (Ioi y) := i0.mono_set (Ioi_subset_Ioi hy)
  have k1 : IntegrableOn (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) (Ioi y) :=
    j1.sub (j0.const_mul _)
  have k3 : IntegrableOn (fun t => (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3) (Ioi y) :=
    j3.const_mul _
  have k0 : IntegrableOn (fun t => μ / mu_star p * fam_Z0 p R t) (Ioi y) := j0.const_mul _
  have k13 : IntegrableOn (fun t => fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3) (Ioi y) :=
    j1.add k3
  have hF1 : ∫ t in Ioi y, c04_aux_Gosc p R ε μ t =
      (∫ t in Ioi y, (fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t)) +
        (c_cubic p ε : ℂ) * ∫ t in Ioi y, fam_Z p R ε μ t ^ 3 := by
    have e : c04_aux_Gosc p R ε μ = fun t => (fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) +
        (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3 := by
      funext t; unfold c04_aux_Gosc; ring
    rw [e, integral_add k1 k3, integral_const_mul]
  have hF2 : ∫ t in Ioi y, c04_aux_Gosc p R ε μ t =
      ((∫ t in Ioi y, fam_Z p R ε μ t) +
        (c_cubic p ε : ℂ) * (∫ t in Ioi y, fam_Z p R ε μ t ^ 3)) -
        μ / mu_star p * ∫ t in Ioi y, fam_Z0 p R t := by
    have e : c04_aux_Gosc p R ε μ = fun t => (fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3) -
        μ / mu_star p * fam_Z0 p R t := by
      funext t; unfold c04_aux_Gosc; ring
    rw [e, integral_sub k13 k0, integral_add j1 k3, integral_const_mul, integral_const_mul]
  -- derivatives of `G`
  have hyR2 : y ∈ Ioi (R / 2) := by simp only [mem_Ioi]; linarith
  have hZC : ContDiffAt ℝ j (fam_Z p R ε μ) y :=
    (hZs.contDiffAt (Ioi_mem_nhds hyR2)).of_le (by exact_mod_cast le_top)
  have hZ0C : ContDiffAt ℝ j (fam_Z0 p R) y :=
    (hZ0s.contDiffAt (Ioi_mem_nhds hyR2)).of_le (by exact_mod_cast le_top)
  have hZ3C : ContDiffAt ℝ j (fun t => fam_Z p R ε μ t ^ 3) y := hZC.pow 3
  have hG1 : iteratedDeriv j (c04_aux_Gosc p R ε μ) y =
      iteratedDeriv j (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) y +
        (c_cubic p ε : ℂ) * iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y := by
    have e : c04_aux_Gosc p R ε μ = fun t => (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) t +
        (fun t => (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3) t := by
      funext t; unfold c04_aux_Gosc; ring
    rw [e, iteratedDeriv_fun_add (hZC.sub (contDiffAt_const.mul hZ0C)) (contDiffAt_const.mul hZ3C),
      iteratedDeriv_const_mul _ hZ3C]
  have hG2 : iteratedDeriv j (c04_aux_Gosc p R ε μ) y =
      (iteratedDeriv j (fam_Z p R ε μ) y +
        (c_cubic p ε : ℂ) * iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y) -
        μ / mu_star p * iteratedDeriv j (fam_Z0 p R) y := by
    have e : c04_aux_Gosc p R ε μ = fun t => (fun t => fam_Z p R ε μ t + (c_cubic p ε : ℂ) *
        fam_Z p R ε μ t ^ 3) t - (fun t => μ / mu_star p * fam_Z0 p R t) t := by
      funext t; unfold c04_aux_Gosc; ring
    rw [e, iteratedDeriv_fun_sub (hZC.add (contDiffAt_const.mul hZ3C)) (contDiffAt_const.mul hZ0C),
      iteratedDeriv_fun_add hZC (contDiffAt_const.mul hZ3C), iteratedDeriv_const_mul _ hZ3C,
      iteratedDeriv_const_mul _ hZ0C]
  obtain ⟨-, -, hzd3⟩ := hCdb R hR2 ε hε2 μ hμ y hy
  obtain ⟨hzb1, hzb3, -, -⟩ := hCbb R hR4 ε hε4 μ hμ y hy
  obtain ⟨hzb0, -, -, -⟩ := hCbb R hR4 0 h04 _ hμ0 y hy
  have e1 : (1 / p - p - beta p + j / p) = -p - beta p + (j + 1) / p := by ring
  have e2 : (-beta p + j / p) = -beta p - 1 / p + (j + 1) / p := by ring
  rw [e1] at hzd3
  rw [e2] at hzb1 hzb0
  have hz3a : y ^ (-3 * beta p + j / p) ≤ y ^ (-p - beta p + (j + 1) / p) := by
    apply rpow_le_rpow_of_exponent_le hy1
    have : p ≤ 2 * beta p + 1 / p := by
      unfold beta; rw [show 2 * ((p + 1) / (2 * p)) + 1 / p = (p + 2) / p by field_simp; ring,
        le_div_iff₀ hp0]; nlinarith
    have : (j + 1) / p = j / p + 1 / p := by ring
    linarith
  have hz3b : y ^ (-3 * beta p + j / p) ≤ y ^ (-beta p - 1 / p + (j + 1) / p) := by
    rw [← e2]; apply rpow_le_rpow_of_exponent_le hy1; linarith
  have hCε : 0 ≤ Cc * ε := mul_nonneg hCc.le hε.1
  set K := 4 * Cp + Cd + Cc * Cb + 3 * Cb + 1 with hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF1]
    have n1 := norm_add_le (∫ t in Ioi y, (fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t))
      ((c_cubic p ε : ℂ) * ∫ t in Ioi y, fam_Z p R ε μ t ^ 3)
    have n2 := pc.trans (mul_le_mul_of_nonneg_left hmin1 (mul_nonneg hCp.le hε.1))
    have hk : 2 * Cp ≤ K := by rw [hK]; have := mul_pos hCc hCb; linarith
    have := mul_le_mul_of_nonneg_right hk (mul_nonneg hε.1 (hYp (-p - beta p)))
    linarith
  · rw [hF2]
    have n1 := norm_sub_le ((∫ t in Ioi y, fam_Z p R ε μ t) +
        (c_cubic p ε : ℂ) * (∫ t in Ioi y, fam_Z p R ε μ t ^ 3))
      (μ / mu_star p * ∫ t in Ioi y, fam_Z0 p R t)
    have n2 := norm_add_le (∫ t in Ioi y, fam_Z p R ε μ t)
      ((c_cubic p ε : ℂ) * (∫ t in Ioi y, fam_Z p R ε μ t ^ 3))
    have n3 : ‖μ / mu_star p * ∫ t in Ioi y, fam_Z0 p R t‖ ≤ 2 * (Cp * y ^ (-beta p - 1 / p)) := by
      rw [norm_mul]; exact mul_le_mul hμq pa0 (norm_nonneg _) (by norm_num)
    have n4 : ‖(c_cubic p ε : ℂ) * (∫ t in Ioi y, fam_Z p R ε μ t ^ 3)‖ ≤ Cp * y ^ (-beta p - 1 / p) := by
      refine pc.trans ?_
      calc Cp * ε * y ^ (1 - 3 * beta p) ≤ Cp * 1 * y ^ (-beta p - 1 / p) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hε01 hCp.le) hmin2 (hYp _) (by positivity)
        _ = _ := by ring
    have hk : 4 * Cp ≤ K := by rw [hK]; have := mul_pos hCc hCb; linarith
    have := mul_le_mul_of_nonneg_right hk (hYp (-beta p - 1 / p))
    linarith
  · rw [hG1]
    have n1 := norm_add_le (iteratedDeriv j (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) y)
      ((c_cubic p ε : ℂ) * iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y)
    have n2 : ‖(c_cubic p ε : ℂ) * iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y‖ ≤
        (Cc * ε) * (Cb * y ^ (-p - beta p + (j + 1) / p)) := by
      rw [norm_mul]
      exact mul_le_mul hcc' (hzb3.trans (mul_le_mul_of_nonneg_left hz3a hCb.le)) (norm_nonneg _) hCε
    have hk : Cd + Cc * Cb ≤ K := by rw [hK]; have := mul_pos hCc hCb; linarith
    have := mul_le_mul_of_nonneg_right hk (mul_nonneg hε.1 (hYp (-p - beta p + (j + 1) / p)))
    linarith
  · rw [hG2]
    have n1 := norm_sub_le (iteratedDeriv j (fam_Z p R ε μ) y +
        (c_cubic p ε : ℂ) * iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y)
      (μ / mu_star p * iteratedDeriv j (fam_Z0 p R) y)
    have n2 := norm_add_le (iteratedDeriv j (fam_Z p R ε μ) y)
      ((c_cubic p ε : ℂ) * iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y)
    have n3 : ‖(c_cubic p ε : ℂ) * iteratedDeriv j (fun t => fam_Z p R ε μ t ^ 3) y‖ ≤
        (Cc * 1) * (Cb * y ^ (-beta p - 1 / p + (j + 1) / p)) := by
      rw [norm_mul]
      exact mul_le_mul (hcc'.trans (mul_le_mul_of_nonneg_left hε01 hCc.le))
        (hzb3.trans (mul_le_mul_of_nonneg_left hz3b hCb.le)) (norm_nonneg _) (by positivity)
    have n4 : ‖μ / mu_star p * iteratedDeriv j (fam_Z0 p R) y‖ ≤
        2 * (Cb * y ^ (-beta p - 1 / p + (j + 1) / p)) := by
      rw [norm_mul]; exact mul_le_mul hμq hzb0 (norm_nonneg _) (by norm_num)
    have hk : 3 * Cb + Cc * Cb ≤ K := by rw [hK]; have := mul_pos hCc hCb; linarith
    have := mul_le_mul_of_nonneg_right hk (hYp (-beta p - 1 / p + (j + 1) / p))
    linarith


/-- A smooth function vanishing on `(-∞,a]` has all derivatives `0` at `a`. -/
theorem c04_aux_iter_zero_left (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ)
    (h0 : ∀ t ≤ a, f t = 0) (j : ℕ) (y : ℝ) (hy : y ≤ a) : iteratedDeriv j f y = 0 := by
  have hzero : ∀ s < a, iteratedDeriv j f s = 0 := by
    intro s hs
    have : f =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs] with u hu using h0 u (le_of_lt hu)
    rw [this.iteratedDeriv_eq, iteratedDeriv_const]; simp
  rcases lt_or_eq_of_le hy with h | h
  · exact hzero y h
  · have hcont : Continuous (iteratedDeriv j f) := hf.continuous_iteratedDeriv j (by exact_mod_cast le_top)
    have h1 := (hcont.continuousAt (x := y)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio y))
    have h2 : Tendsto (iteratedDeriv j f) (𝓝[<] y) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall
        (fun s hs => (hzero s (h ▸ hs)).symm))
    exact tendsto_nhds_unique h1 h2

/-- Blueprint: lem:approx_phase_differences.  For `y ≥ R`: the bounds (approx_phase_difference),
(approx_lambda_difference), (approx_Z_difference), the bound (approx_fosc_bounds) for `f_osc`, and
`‖f_osc‖_{L¹} ≤ C ε R^{1-p-β} ≤ C ε`. -/
theorem approx_phase_differences (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ j : ℕ, ∃ C > (0 : ℝ),
        ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
          |iteratedDeriv j (fun t => fam_Psi p R ε μ t - Psi0 p t) y| ≤
            C * ε * y ^ (1 / p - p - j) ∧
          |iteratedDeriv j (fun t => fam_lambda p ε μ t - lambda0 p t) y| ≤
            C * ε * y ^ (1 / p - p - 1 - j) ∧
          ‖iteratedDeriv j (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) y‖ ≤
            C * ε * y ^ (1 / p - p - beta p + j / p) ∧
          |iteratedDeriv j (fam_osc p R ε μ) y| ≤
            C * min (ε * jb y ^ (-p - beta p + j / p)) (jb y ^ (-beta p + ((j : ℝ) - 1) / p))) ∧
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≤ R, fam_osc p R ε μ y = 0) ∧
      (∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        Integrable (fam_osc p R ε μ) ∧
        ∫ y, |fam_osc p R ε μ y| ≤ C * ε * R ^ (1 - p - beta p) ∧
        C * ε * R ^ (1 - p - beta p) ≤ C * ε) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨ε₁, hε₁, R₁, hR₁, hlpd⟩ := c04_lambda_psi_difference p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hzd⟩ := c04_Z_difference p hp hp1 δ hδ hδμ
  obtain ⟨ε₃, hε₃, R₃, hR₃, hGb⟩ := c04_aux_G_bounds p hp hp1 δ hδ hδμ
  obtain ⟨ε₄, hε₄, R₄, hR₄, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  have hε₀pos : 0 < min (min ε₁ ε₂) (min ε₃ ε₄) := lt_min (lt_min hε₁.1 hε₂.1) (lt_min hε₃.1 hε₄.1)
  have hε₀1 : min (min ε₁ ε₂) (min ε₃ ε₄) ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)
  have hR₀2 : max (max R₁ R₂) (max R₃ R₄) ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _))
  have hRs : ∀ R ≥ max (max R₁ R₂) (max R₃ R₄), R ≥ R₁ ∧ R ≥ R₂ ∧ R ≥ R₃ ∧ R ≥ R₄ ∧ R ≥ 2 :=
    fun R hR => ⟨le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR,
      le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR,
      le_trans ((le_max_left _ _).trans (le_max_right _ _)) hR,
      le_trans ((le_max_right _ _).trans (le_max_right _ _)) hR,
      le_trans hR₀2 hR⟩
  have hεs : ∀ ε ∈ Icc (0 : ℝ) (min (min ε₁ ε₂) (min ε₃ ε₄)), ε ∈ Icc (0 : ℝ) ε₁ ∧ ε ∈ Icc (0 : ℝ) ε₂ ∧
      ε ∈ Icc (0 : ℝ) ε₃ ∧ ε ∈ Icc (0 : ℝ) ε₄ := fun ε hε =>
    ⟨⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩,
      ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩,
      ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩,
      ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩⟩
  choose Cg hCg0 hCg using hGb
  -- the two pointwise bounds for `∂^j f_osc`, `y > R`
  have hfosc : ∀ j : ℕ, ∃ K ≥ (0 : ℝ), ∀ R ≥ max (max R₁ R₂) (max R₃ R₄),
      ∀ ε ∈ Icc (0 : ℝ) (min (min ε₁ ε₂) (min ε₃ ε₄)), ∀ μ ∈ Bbar p δ, ∀ y > R,
        |iteratedDeriv j (fam_osc p R ε μ) y| ≤ K * ε * y ^ (-p - beta p + j / p) ∧
        |iteratedDeriv j (fam_osc p R ε μ) y| ≤ K * y ^ (-beta p - 1 / p + j / p) := by
    intro j
    obtain ⟨K, hK0, hK⟩ := c04_aux_fosc_iter_bound p hp0 j
    set S := ∑ i ∈ Finset.range (j + 1), Cg i with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hCg0 i).le)
    have hSi : ∀ i, i ≤ j → Cg i ≤ S := fun i hi =>
      Finset.single_le_sum (f := Cg) (fun i _ => (hCg0 i).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    refine ⟨K * S, by positivity, fun R hR ε hε μ hμ y hy => ?_⟩
    obtain ⟨hR1, hR2, hR3, hR4, hR2'⟩ := hRs R hR
    obtain ⟨hε1, hε2, hε3, hε4⟩ := hεs ε hε
    obtain ⟨-, hGs, -, -, hGi, -⟩ := hstd R hR4 ε hε4 μ hμ
    have hy0 : 0 < y := by linarith
    have hYp : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
    have hb := fun i => hCg i R hR3 ε hε3 μ hμ y (le_of_lt hy)
    constructor
    · have := hK R hR2' ε μ hGs hGi (S * ε) (-p - beta p) (mul_nonneg hS0 hε.1) y hy
        ((hb 0).1.trans (by
          have := mul_le_mul_of_nonneg_right (hSi 0 (Nat.zero_le _)) (mul_nonneg hε.1 (hYp (-p - beta p)))
          linarith))
        (fun i hi => (hb i).2.2.1.trans (by
          have := mul_le_mul_of_nonneg_right (hSi i hi.le)
            (mul_nonneg hε.1 (hYp (-p - beta p + (i + 1) / p)))
          linarith))
      refine this.trans (le_of_eq ?_); ring
    · have := hK R hR2' ε μ hGs hGi S (-beta p - 1 / p) hS0 y hy
        ((hb 0).2.1.trans (mul_le_mul_of_nonneg_right (hSi 0 (Nat.zero_le _)) (hYp _)))
        (fun i hi => (hb i).2.2.2.trans (mul_le_mul_of_nonneg_right (hSi i hi.le) (hYp _)))
      refine this.trans (le_of_eq ?_); ring
  have hzero : ∀ R ≥ max (max R₁ R₂) (max R₃ R₄), ∀ ε ∈ Icc (0 : ℝ) (min (min ε₁ ε₂) (min ε₃ ε₄)),
      ∀ μ ∈ Bbar p δ, ∀ y ≤ R, fam_osc p R ε μ y = 0 := by
    intro R hR ε hε μ hμ y hy
    unfold fam_osc; exact if_neg (not_lt.mpr hy)
  refine ⟨_, ⟨hε₀pos, hε₀1⟩, _, hR₀2, fun j => ?_, hzero, ?_⟩
  · obtain ⟨Cl, hCl, hClb⟩ := hlpd j
    obtain ⟨Cd, hCd, hCdb⟩ := hzd j 1 one_pos
    obtain ⟨K, hK0, hK⟩ := hfosc j
    set e1 : ℝ := -p - beta p + j / p with he1
    set e2 : ℝ := -beta p + ((j : ℝ) - 1) / p with he2
    set Cf := K * (2 ^ |e1| + 2 ^ |e2|) + 1 with hCf
    have hCf0 : 0 < Cf := by rw [hCf]; positivity
    refine ⟨Cl + Cd + Cf, by positivity, fun R hR ε hε μ hμ y hy => ?_⟩
    obtain ⟨hR1, hR2, hR3, hR4, hR2'⟩ := hRs R hR
    obtain ⟨hε1, hε2, hε3, hε4⟩ := hεs ε hε
    have hy0 : 0 < y := by linarith
    have hy1 : 1 ≤ y := by linarith
    have hYp : ∀ e : ℝ, 0 ≤ y ^ e := fun e => (rpow_pos_of_pos hy0 e).le
    have hjb0 : 0 < jb y := lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)
    have hJp : ∀ e : ℝ, 0 ≤ jb y ^ e := fun e => (rpow_pos_of_pos hjb0 e).le
    obtain ⟨hl1, hl2⟩ := hClb R hR1 ε hε1 μ hμ y hy
    obtain ⟨-, -, hd3⟩ := hCdb R hR2 ε hε2 μ hμ y hy
    have hεCl : Cl * ε ≤ (Cl + Cd + Cf) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.1
    have hεCd : Cd * ε ≤ (Cl + Cd + Cf) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.1
    refine ⟨hl2.trans (mul_le_mul_of_nonneg_right hεCl (hYp _)),
      hl1.trans (mul_le_mul_of_nonneg_right hεCl (hYp _)),
      hd3.trans (mul_le_mul_of_nonneg_right hεCd (hYp _)), ?_⟩
    have hosc : |iteratedDeriv j (fam_osc p R ε μ) y| ≤ Cf * min (ε * jb y ^ e1) (jb y ^ e2) := by
      rcases lt_or_eq_of_le hy with hy' | hy'
      · obtain ⟨b1, b2⟩ := hK R hR ε hε μ hμ y hy'
        have c1 := c04_aux_rpow_le_jb_gen y e1 hy1
        have c2 := c04_aux_rpow_le_jb_gen y e2 hy1
        have ee : -beta p - 1 / p + j / p = e2 := by rw [he2]; ring
        rw [ee] at b2
        rw [mul_min_of_nonneg _ _ hCf0.le]
        refine le_min ?_ ?_
        · refine b1.trans ?_
          have h2 : (0 : ℝ) ≤ 2 ^ |e2| := by positivity
          have := mul_le_mul_of_nonneg_left c1 (mul_nonneg hK0 hε.1)
          have h3 : K * ε * (2 ^ |e1| * jb y ^ e1) ≤ Cf * (ε * jb y ^ e1) := by
            rw [hCf]
            have := mul_nonneg (mul_nonneg hK0 h2) (mul_nonneg hε.1 (hJp e1))
            have := mul_nonneg hε.1 (hJp e1)
            nlinarith
          linarith
        · refine b2.trans ?_
          have h2 : (0 : ℝ) ≤ 2 ^ |e1| := by positivity
          have := mul_le_mul_of_nonneg_left c2 hK0
          have h3 : K * (2 ^ |e2| * jb y ^ e2) ≤ Cf * jb y ^ e2 := by
            rw [hCf]
            have := mul_nonneg (mul_nonneg hK0 h2) (hJp e2)
            have := hJp e2
            nlinarith
          linarith
      · obtain ⟨-, -, -, -, -, hfs⟩ := hstd R hR4 ε hε4 μ hμ
        rw [c04_aux_iter_zero_left _ hfs R (fun t ht => hzero R hR ε hε μ hμ t ht) j y hy'.symm.le,
          abs_zero]
        exact mul_nonneg hCf0.le (le_min (mul_nonneg hε.1 (hJp _)) (hJp _))
    refine hosc.trans (mul_le_mul_of_nonneg_right (by linarith) ?_)
    exact le_min (mul_nonneg hε.1 (hJp _)) (hJp _)
  · -- the `L¹` bound
    obtain ⟨K, hK0, hK⟩ := hfosc 0
    have hpb : 0 < p + beta p - 1 := by linarith
    refine ⟨K / (p + beta p - 1) + 1, by positivity, fun R hR ε hε μ hμ => ?_⟩
    obtain ⟨hR1, hR2, hR3, hR4, hR2'⟩ := hRs R hR
    obtain ⟨hε1, hε2, hε3, hε4⟩ := hεs ε hε
    have hR0 : 0 < R := by linarith
    obtain ⟨-, -, -, -, -, hfs⟩ := hstd R hR4 ε hε4 μ hμ
    set g : ℝ → ℝ := (Ioi R).indicator (fun y => K * ε * y ^ (-p - beta p)) with hg
    have hgi : Integrable g := by
      rw [hg, integrable_indicator_iff measurableSet_Ioi]
      exact (integrableOn_Ioi_rpow_of_lt (by linarith) hR0).const_mul _
    have hbd : ∀ y, |fam_osc p R ε μ y| ≤ g y := by
      intro y
      rcases le_or_gt y R with hy | hy
      · rw [hzero R hR ε hε μ hμ y hy, abs_zero, hg, indicator_of_notMem (by simpa using hy)]
      · rw [hg, indicator_of_mem (by exact hy)]
        have := (hK R hR ε hε μ hμ y hy).1
        simpa using this
    have hint : Integrable (fam_osc p R ε μ) :=
      Integrable.mono' hgi hfs.continuous.aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hbd y)
    have hgint : ∫ y, g y = K * ε * (R ^ (1 - p - beta p) / (p + beta p - 1)) := by
      rw [hg, integral_indicator measurableSet_Ioi, integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) hR0]
      congr 1
      rw [show -p - beta p + 1 = 1 - p - beta p by ring, neg_div, ← div_neg,
        show -(1 - p - beta p) = p + beta p - 1 by ring]
    have hRle : R ^ (1 - p - beta p) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hRp : 0 ≤ R ^ (1 - p - beta p) := (rpow_pos_of_pos hR0 _).le
    refine ⟨hint, ?_, ?_⟩
    · calc ∫ y, |fam_osc p R ε μ y| ≤ ∫ y, g y :=
            integral_mono hint.abs hgi hbd
        _ = K / (p + beta p - 1) * ε * R ^ (1 - p - beta p) := by rw [hgint]; ring
        _ ≤ (K / (p + beta p - 1) + 1) * ε * R ^ (1 - p - beta p) := by
            have := mul_nonneg hε.1 hRp
            nlinarith
    · have h := mul_nonneg (by positivity : (0 : ℝ) ≤ K / (p + beta p - 1) + 1) hε.1
      calc (K / (p + beta p - 1) + 1) * ε * R ^ (1 - p - beta p) ≤
          (K / (p + beta p - 1) + 1) * ε * 1 := mul_le_mul_of_nonneg_left hRle h
        _ = _ := by ring

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_chiR_one (R t : ℝ) (hR : 0 < R) (ht : 2 * R ≤ t) : fam_chiR R t = 1 := by
  unfold fam_chiR chiPlus
  apply Real.smoothTransition.one_of_one_le
  have : 2 ≤ t / R := by rw [le_div_iff₀ hR]; linarith
  linarith

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_deriv_chiR_top (R t : ℝ) (hR : 0 < R) (ht : 2 * R ≤ t) : deriv (fam_chiR R) t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  refine Eventually.of_forall fun s => ?_
  rw [c04_aux_chiR_one R t hR ht]
  exact Real.smoothTransition.le_one _

/-- Algebraic decomposition `f̄ = f_{0,low} + 2Re(μ/μ_* f_{0,+}) + f_slow + f_osc`. -/
theorem c04_aux_family_split (p R ε : ℝ) (μ : ℂ) (y : ℝ) :
    approximate_solution_family p R ε μ y = c04_linear_seed_low p y +
      2 * (μ / mu_star p * c04_linear_seed_plus p y).re + fam_slow p R ε y + fam_osc p R ε μ y := by
  unfold approximate_solution_family c04_linear_seed_mu c04_linear_seed_low c04_linear_seed_high
  rw [sub_mul, one_mul, Complex.sub_re]; ring

/-- Blueprint: lem:c04_family_regions.  Regional forms and smoothness of `f̄_{ε,μ}`. -/
theorem c04_family_regions (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀,
      (∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family p R ε μ) ∧
        approximate_solution_family p R ε μ ∈ c01_admissible_class ∧
        (∀ y ∈ Icc (-R) R, fam_slow p R ε y = 0) ∧
        (∀ y ≤ R, fam_osc p R ε μ y = 0) ∧
        -- (eqn:approx_family_positive)
        (∀ y ≥ 2 * R, approximate_solution_family p R ε μ y =
          c04_linear_seed_low p y + c_plus p ε * y ^ (-p) -
            2 * (∫ t in Ioi y, (fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3)).re) ∧
        -- (eqn:approx_family_negative)
        (∀ y ≤ -2 * R, approximate_solution_family p R ε μ y =
          c04_linear_seed p y + 2 * ((μ / mu_star p - 1) * c04_linear_seed_plus p y).re +
            c_minus p ε * |y| ^ (-p)) ∧
        (∀ y ≥ 2 * R, deriv (approximate_solution_family p R ε μ) y =
          deriv (c04_linear_seed_low p) y - p * c_plus p ε * y ^ (-p - 1) +
            2 * (fam_Z p R ε μ y + (c_cubic p ε : ℂ) * fam_Z p R ε μ y ^ 3).re)) ∧
      approximate_solution_family p R 0 (mu_star p) = c04_linear_seed p := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs' : 0 < ‖mu_star p‖ := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp hμs'
  obtain ⟨-, -, hplus, -, hplus0, -⟩ := c04_seed_decomposition p hp hp1
  have hf0s : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed p) := (c04_seed_decomposition p hp hp1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, hμseed⟩ := approx_linear_seed p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, -, -, -, hb3⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  obtain ⟨ε₃, hε₃, R₃, hR₃, hpd, -, -⟩ := approx_phase_differences p hp hp1 δ hδ hδμ
  obtain ⟨Cs, hCs, hslow⟩ := c04_aux_fslow_bound p hp hp1 1
  obtain ⟨Co, hCo, hosc1⟩ := hpd 1
  obtain ⟨-, ⟨-, -, -, -, -, hcp0, hcm0⟩, -, -⟩ :=
    c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)
  have hcc0 : c_cubic p 0 = 0 := by
    unfold c_cubic; rw [c04_aux_c2_lin p 0]; simp
  have hε₀pos : 0 < min (min ε₁ ε₂) ε₃ := lt_min (lt_min hε₁.1 hε₂.1) hε₃.1
  have hε₀1 : min (min ε₁ ε₂) ε₃ ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)
  have hR₀2 : max (max R₁ R₂) R₃ ≥ 2 := le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨_, ⟨hε₀pos, hε₀1⟩, _, hR₀2, fun R hR => ⟨fun ε hε μ hμ => ?_, ?_⟩⟩
  rotate_left
  · -- the case `ε = 0`, `μ = μ_*`
    have hR0 : 0 < R := by linarith [le_trans hR₀2 hR]
    funext y
    unfold approximate_solution_family c04_linear_seed_mu fam_slow fam_osc
    rw [hcp0, hcm0, hcc0, div_self hμs]
    simp only [sub_self, zero_mul, Complex.zero_re, mul_zero, add_zero, zero_add, Complex.ofReal_zero,
      one_mul]
    split_ifs
    · simp [fam_Z0]
    · simp
  have hR1 : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hR2 : R ≥ R₂ := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hR3 : R ≥ R₃ := le_trans (le_max_right _ _) hR
  have hR2' : (2 : ℝ) ≤ R := le_trans hR₀2 hR
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε3 : ε ∈ Icc (0 : ℝ) ε₃ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hε₀1⟩
  have hμ0 : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  obtain ⟨hZs, hGs, i1, i3, hGi, hfosc⟩ := hstd R hR2 ε hε2 μ hμ
  obtain ⟨hZ0s, -, i0, -, -, -⟩ := hstd R hR2 0 ⟨le_rfl, hε₂.1.le⟩ _ hμ0
  obtain ⟨hμs1, hμs2, -⟩ := hμseed μ
  have hslows : ContDiff ℝ (⊤ : ℕ∞) (fam_slow p R ε) := c04_aux_fam_slow_smooth p R ε hR0
  have hfam : approximate_solution_family p R ε μ =
      fun y => c04_linear_seed_mu p μ y + fam_slow p R ε y + fam_osc p R ε μ y := rfl
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family p R ε μ) := by
    rw [hfam]; exact (hμs1.add hslows).add hfosc
  have hd1 : ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → Differentiable ℝ f := fun f hf =>
    hf.differentiable (by simp)
  have hderiv : ∀ y, deriv (approximate_solution_family p R ε μ) y =
      deriv (c04_linear_seed_mu p μ) y + deriv (fam_slow p R ε) y + deriv (fam_osc p R ε μ) y := by
    intro y
    rw [hfam]
    exact ((((hd1 _ hμs1) y).hasDerivAt.add ((hd1 _ hslows) y).hasDerivAt).add
      ((hd1 _ hfosc) y).hasDerivAt).deriv
  have hzero_osc : ∀ y ≤ R, fam_osc p R ε μ y = 0 := by
    intro y hy; unfold fam_osc; exact if_neg (not_lt.mpr hy)
  -- the integral identity `f_{0,+}(y) = -∫_y^∞ Z₀`
  have hplus_int : ∀ y > R / 2, IntegrableOn (fam_Z0 p R) (Ioi y) →
      ∫ t in Ioi y, fam_Z0 p R t = -c04_linear_seed_plus p y := by
    intro y hy hint
    have hder : ∀ x ∈ Ioi y, HasDerivAt (c04_linear_seed_plus p) (fam_Z0 p R x) x := by
      intro x hx
      have hx' : x > R / 2 := lt_trans hy hx
      rw [(hb3 R hR1 μ hμ x hx').2.2.2]
      exact ((hplus.differentiable (by simp)) x).hasDerivAt
    have := integral_Ioi_of_hasDerivAt_of_tendsto
      ((hplus.differentiable (by simp)) y).continuousAt.continuousWithinAt hder hint
      (hplus0.mono_left (atTop_le_cocompact))
    rw [this]; ring
  refine ⟨hsm, ⟨hsm.of_le (by exact_mod_cast le_top), ?_, ?_⟩, ?_, hzero_osc, ?_, ?_, ?_⟩
  · -- bounded derivative
    obtain ⟨-, ⟨M, hM⟩, -⟩ := hμs2
    refine ⟨M + Cs + Co, fun y => ?_⟩
    rw [hderiv]
    have h2 : |deriv (fam_slow p R ε) y| ≤ Cs := by
      have := hslow R hR2' ε hεI y
      rw [iteratedDeriv_one] at this
      refine this.trans ?_
      have hj : jb y ^ (-p - ((1 : ℕ) : ℝ)) ≤ 1 :=
        rpow_le_one_of_one_le_of_nonpos (c04_aux_one_le_jb y) (by push_cast; linarith)
      have := mul_le_mul (mul_le_mul_of_nonneg_left hεI.2 hCs.le) hj
        (rpow_nonneg (by linarith [c04_aux_one_le_jb y]) _) (by positivity)
      linarith
    have h3 : |deriv (fam_osc p R ε μ) y| ≤ Co := by
      rcases le_or_gt R y with hy | hy
      · have := ((hosc1 R hR3 ε hε3 μ hμ y hy).2.2.2)
        rw [iteratedDeriv_one] at this
        refine this.trans ?_
        have hj : jb y ^ (-beta p + (((1 : ℕ) : ℝ) - 1) / p) ≤ 1 :=
          rpow_le_one_of_one_le_of_nonpos (c04_aux_one_le_jb y)
            (by
              push_cast; rw [sub_self, zero_div, add_zero]
              have : 0 < beta p := by unfold beta; positivity
              linarith)
        have hm := min_le_right (ε * jb y ^ (-p - beta p + ((1 : ℕ) : ℝ) / p))
          (jb y ^ (-beta p + (((1 : ℕ) : ℝ) - 1) / p))
        have := mul_le_mul_of_nonneg_left (hm.trans hj) hCo.le
        linarith
      · have : fam_osc p R ε μ =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds hy] with t ht using hzero_osc t (le_of_lt ht)
        rw [this.deriv_eq, deriv_const, abs_zero]; exact hCo.le
    have h1 := hM y
    calc _ ≤ |deriv (c04_linear_seed_mu p μ) y + deriv (fam_slow p R ε) y| +
          |deriv (fam_osc p R ε μ) y| := abs_add_le _ _
      _ ≤ |deriv (c04_linear_seed_mu p μ) y| + |deriv (fam_slow p R ε) y| +
          |deriv (fam_osc p R ε μ) y| := by gcongr; exact abs_add_le _ _
      _ ≤ M + Cs + Co := by linarith
  · -- locally Lipschitz derivative
    have : ContDiff ℝ 1 (deriv (approximate_solution_family p R ε μ)) :=
      (contDiff_infty_iff_deriv.mp hsm).2.of_le (by exact_mod_cast le_top)
    exact this.locallyLipschitz
  · -- `f_slow = 0` on `[-R,R]`
    intro y hy
    unfold fam_slow
    rw [c04_aux_chiR_zero R y hR0 hy.2, c04_aux_chiR_zero R (-y) hR0 (by linarith [hy.1])]
    ring
  · -- positive region
    intro y hy
    have hyR : y > R := by linarith
    have hyR2 : y > R / 2 := by linarith
    have j1 : IntegrableOn (fam_Z p R ε μ) (Ioi y) := i1.mono_set (Ioi_subset_Ioi hyR.le)
    have j3 : IntegrableOn (fun t => fam_Z p R ε μ t ^ 3) (Ioi y) := i3.mono_set (Ioi_subset_Ioi hyR.le)
    have j0 : IntegrableOn (fam_Z0 p R) (Ioi y) := i0.mono_set (Ioi_subset_Ioi hyR.le)
    have k13 : IntegrableOn (fun t => fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3) (Ioi y) :=
      j1.add (j3.const_mul _)
    have k0 : IntegrableOn (fun t => μ / mu_star p * fam_Z0 p R t) (Ioi y) := j0.const_mul _
    have hsplit : ∫ t in Ioi y, (fam_Z p R ε μ t + (c_cubic p ε : ℂ) * fam_Z p R ε μ t ^ 3 -
        μ / mu_star p * fam_Z0 p R t) = (∫ t in Ioi y, (fam_Z p R ε μ t + (c_cubic p ε : ℂ) *
          fam_Z p R ε μ t ^ 3)) - μ / mu_star p * ∫ t in Ioi y, fam_Z0 p R t := by
      rw [integral_sub k13 k0, integral_const_mul]
    rw [c04_aux_family_split]
    unfold fam_slow fam_osc
    rw [if_pos hyR, c04_aux_chiR_one R y hR0 hy, c04_aux_chiR_zero R (-y) hR0 (by linarith),
      hsplit, hplus_int y hyR2 j0, Complex.sub_re]
    simp only [mul_neg, Complex.neg_re]
    ring
  · -- negative region
    intro y hy
    have hyR : y ≤ R := by linarith
    unfold approximate_solution_family c04_linear_seed_mu fam_slow
    rw [hzero_osc y hyR, c04_aux_chiR_zero R y hR0 (by linarith),
      c04_aux_chiR_one R (-y) hR0 (by linarith)]
    ring
  · -- derivative in the positive region
    intro y hy
    have hyR : y > R := by linarith
    have hyR2 : y > R / 2 := by linarith
    have hy0 : 0 < y := by linarith
    rw [hderiv]
    -- `f_{0,μ}'`
    have hd0 : deriv (c04_linear_seed_mu p μ) y = deriv (c04_linear_seed_low p) y +
        2 * (μ / mu_star p * fam_Z0 p R y).re := by
      have hlow : c04_linear_seed_low p = fun t => c04_linear_seed p t -
          2 * (c04_linear_seed_plus p t).re := rfl
      have hmu : c04_linear_seed_mu p μ = fun t => c04_linear_seed p t +
          2 * ((μ / mu_star p - 1) * c04_linear_seed_plus p t).re := rfl
      have hpd := (hplus.differentiable (by simp)) y
      have hre1 := c04_aux_re_hasDeriv (c04_linear_seed_plus p) y hpd
      have hre2 := c04_aux_re_hasDeriv (fun t => (μ / mu_star p - 1) * c04_linear_seed_plus p t) y
        (hpd.const_mul _)
      have hf0d := ((hf0s.differentiable (by simp)) y).hasDerivAt
      have A : HasDerivAt (fun t => c04_linear_seed p t + 2 * ((μ / mu_star p - 1) *
          c04_linear_seed_plus p t).re) _ y := hf0d.add (hre2.const_mul 2)
      have B : HasDerivAt (fun t => c04_linear_seed p t - 2 * (c04_linear_seed_plus p t).re) _ y :=
        hf0d.sub (hre1.const_mul 2)
      rw [hlow, hmu, A.deriv, B.deriv,
        deriv_const_mul _ hpd, (hb3 R hR1 μ hμ y hyR2).2.2.2]
      rw [show (μ / mu_star p - 1) * deriv (c04_linear_seed_plus p) y =
        μ / mu_star p * deriv (c04_linear_seed_plus p) y - deriv (c04_linear_seed_plus p) y by ring,
        Complex.sub_re]
      ring
    -- `f_slow'`
    have hd1s : deriv (fam_slow p R ε) y = -p * c_plus p ε * y ^ (-p - 1) := by
      have e : fam_slow p R ε =ᶠ[𝓝 y] fun t => c_plus p ε * t ^ (-p) * fam_chiR R t := by
        filter_upwards [Ioi_mem_nhds (show (-R) < y by linarith)] with t ht
        unfold fam_slow
        rw [c04_aux_chiR_zero R (-t) hR0 (by linarith [mem_Ioi.mp ht])]; ring
      have hχ : HasDerivAt (fam_chiR R) 0 y := by
        have := ((c04_aux_chiR_smooth R).differentiable (by simp) y).hasDerivAt
        rwa [c04_aux_deriv_chiR_top R y hR0 hy] at this
      have hpow : HasDerivAt (fun t : ℝ => t ^ (-p)) (-p * y ^ (-p - 1)) y :=
        hasDerivAt_rpow_const (Or.inl hy0.ne')
      rw [e.deriv_eq]
      refine (((hpow.const_mul (c_plus p ε)).mul hχ).deriv).trans ?_
      rw [c04_aux_chiR_one R y hR0 hy]
      ring
    -- `f_osc'`
    have hd2 : deriv (fam_osc p R ε μ) y = 2 * (c04_aux_Gosc p R ε μ y).re := by
      rw [c04_aux_fosc_eq p R ε μ hR0]
      have hF := c04_aux_tail_hasDeriv _ (R / 2) R hGs.continuousOn hGi y hyR2
      have hre := c04_aux_re_hasDeriv (fun x => ∫ t in Ioi x, c04_aux_Gosc p R ε μ t) y
        hF.differentiableAt
      rw [hF.deriv] at hre
      have hχ : HasDerivAt (fam_chiR R) 0 y := by
        have := ((c04_aux_chiR_smooth R).differentiable (by simp) y).hasDerivAt
        rwa [c04_aux_deriv_chiR_top R y hR0 hy] at this
      refine (((hχ.const_mul (-2 : ℝ)).mul hre).deriv).trans ?_
      rw [c04_aux_chiR_one R y hR0 hy, Complex.neg_re]
      ring
    rw [hd0, hd1s, hd2]
    unfold c04_aux_Gosc
    rw [Complex.sub_re]
    ring


/-- Two-variable versions of `λ`, `Ψ` and `Z/μ` (with `s` in place of `c_log(μ)`). -/
def c04_aux_Lam (p ε : ℝ) (w : ℝ × ℝ) : ℝ :=
  w.2 ^ (1 / p) + c_power p ε * ((1 - p ^ 2) / p) * w.2 ^ (1 / p - p - 1) + w.1 / w.2

/-- Auxiliary lemma (chapter 04). -/
def c04_aux_Phs (p R ε : ℝ) (w : ℝ × ℝ) : ℝ :=
  Psi0 p w.2 + c_power p ε * (w.2 ^ (1 / p - p) - R ^ (1 / p - p)) + w.1 * Real.log (w.2 / R)

/-- Auxiliary lemma (chapter 04). -/
def c04_aux_W (p R ε : ℝ) (w : ℝ × ℝ) : ℂ :=
  astar p w.2 * ((c04_aux_Lam p ε w ^ (-(p + 1) / 2) : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((c04_aux_Phs p R ε w - π / 4 : ℝ) : ℂ))

/-- Auxiliary lemma (chapter 04). -/
def c04_aux_WU (p ε : ℝ) : Set (ℝ × ℝ) := {w | 0 < w.2 ∧ 0 < c04_aux_Lam p ε w}

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_Lam_contDiffAt (p ε : ℝ) (n : ℕ) (w : ℝ × ℝ) (hw : 0 < w.2) :
    ContDiffAt ℝ n (c04_aux_Lam p ε) w := by
  unfold c04_aux_Lam
  exact ((contDiffAt_snd.rpow_const_of_ne hw.ne').add (contDiffAt_const.mul
    (contDiffAt_snd.rpow_const_of_ne hw.ne'))).add (contDiffAt_fst.div contDiffAt_snd hw.ne')

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_WU_open (p ε : ℝ) : IsOpen (c04_aux_WU p ε) := by
  have hc : ContinuousOn (c04_aux_Lam p ε) {w : ℝ × ℝ | 0 < w.2} := fun w hw =>
    (c04_aux_Lam_contDiffAt p ε 0 w hw).continuousAt.continuousWithinAt
  have := hc.isOpen_inter_preimage (isOpen_lt continuous_const continuous_snd) (isOpen_Ioi (a := (0 : ℝ)))
  exact this

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_W_contDiffOn (p R ε : ℝ) (hR : 0 < R)
    (hplus : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus p)) (hμs : mu_star p ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c04_aux_W p R ε) (c04_aux_WU p ε) := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_infty]
  intro n
  obtain ⟨hw1, hw2⟩ := hw
  have ha : ContDiffAt ℝ n (fun w : ℝ × ℝ => astar p w.2) w :=
    (c04_aux_astar_contDiffAt p hplus hμs n w.2 hw1).comp w contDiffAt_snd
  have hL : ContDiffAt ℝ n (fun w => ((c04_aux_Lam p ε w ^ (-(p + 1) / 2) : ℝ) : ℂ)) w :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp w
      ((c04_aux_Lam_contDiffAt p ε n w hw1).rpow_const_of_ne hw2.ne')
  have hP : ContDiffAt ℝ n (c04_aux_Phs p R ε) w := by
    unfold c04_aux_Phs Psi0
    exact ((contDiffAt_const.mul (contDiffAt_snd.rpow_const_of_ne hw1.ne')).add
      (contDiffAt_const.mul ((contDiffAt_snd.rpow_const_of_ne hw1.ne').sub contDiffAt_const))).add
      (contDiffAt_fst.mul ((contDiffAt_snd.div_const R).log (div_pos hw1 hR).ne'))
  have hE : ContDiffAt ℝ n (fun w => Complex.exp (Complex.I * ((c04_aux_Phs p R ε w - π / 4 : ℝ) : ℂ))) w :=
    Complex.contDiff_exp.contDiffAt.comp w (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp w (hP.sub contDiffAt_const)))
  exact (ha.mul hL).mul hE


/-- Continuity of `iteratedDeriv` of a function smooth on an open set. -/
theorem c04_aux_iter_contOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (s : Set ℝ) (hs : IsOpen s) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (i : ℕ) :
    ContinuousOn (iteratedDeriv i f) s :=
  (hf.continuousOn_iteratedDerivWithin (m := i) (by exact_mod_cast le_top) hs.uniqueDiffOn).congr
    (fun x hx => (iteratedDerivWithin_of_isOpen hs hx).symm)

/-- Joint continuity of `(μ,y) ↦ ∂^i G_μ(y)` on `B̄ × (R/2,∞)`. -/
theorem c04_aux_Gder_cont (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ i : ℕ,
      ContinuousOn (fun z : ℂ × ℝ => iteratedDeriv i (c04_aux_Gosc p R ε z.1) z.2)
        (Bbar p δ ×ˢ Ioi (R / 2)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs' : 0 < ‖mu_star p‖ := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp hμs'
  obtain ⟨-, -, hplus, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hbasic, -, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  obtain ⟨-, -, hclc, -⟩ := c04_constants_small p hp hp1 (2 * ‖mu_star p‖) (by positivity)
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), fun R hR ε hε i => ?_⟩
  have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
  have hR2 : R ≥ R₂ := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hμ0 : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ.le
  obtain ⟨hZ0s, -, -, -, -, -⟩ := hstd R hR2 0 ⟨le_rfl, hε₂.1.le⟩ _ hμ0
  have hW := c04_aux_W_contDiffOn p R ε hR0 hplus hμs
  have hW3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => c04_aux_W p R ε w ^ 3) (c04_aux_WU p ε) := hW.pow 3
  have hU := c04_aux_WU_open p ε
  -- pointwise representation
  have hmem : ∀ μ ∈ Bbar p δ, ∀ τ > R / 2, (c_log p ε μ, τ) ∈ c04_aux_WU p ε := by
    intro μ hμ τ hτ
    obtain ⟨g1, g2, -, -⟩ := hbasic R hR1 ε hε1 μ hμ τ hτ
    have hτ0 : 0 < τ := by linarith
    exact ⟨hτ0, (c04_aux_lam_pos p ε μ τ hτ0 g1 g2).1⟩
  have hZW : ∀ μ ∈ Bbar p δ, ∀ τ > R / 2, fam_Z p R ε μ τ = μ * c04_aux_W p R ε (c_log p ε μ, τ) := by
    intro μ hμ τ hτ
    obtain ⟨-, -, -, g4⟩ := hbasic R hR1 ε hε1 μ hμ τ hτ
    unfold fam_Z c04_aux_W c04_aux_Phs
    rw [g4]
    simp only [fam_lambda, c04_aux_Lam]
    ring
  have hslice : ∀ (H : ℝ × ℝ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) H (c04_aux_WU p ε) →
      ∀ μ ∈ Bbar p δ, ∀ τ > R / 2, ContDiffAt ℝ i (fun t => H (c_log p ε μ, t)) τ := by
    intro H hH μ hμ τ hτ
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) H (c_log p ε μ, τ) := hH.contDiffAt (hU.mem_nhds (hmem μ hμ τ hτ))
    exact (h1.comp τ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by exact_mod_cast le_top)
  have hrep : ∀ z ∈ Bbar p δ ×ˢ Ioi (R / 2), iteratedDeriv i (c04_aux_Gosc p R ε z.1) z.2 =
      z.1 * iteratedDeriv i (fun t => c04_aux_W p R ε (c_log p ε z.1, t)) z.2 +
        (c_cubic p ε : ℂ) * (z.1 ^ 3 * iteratedDeriv i (fun t => c04_aux_W p R ε (c_log p ε z.1, t) ^ 3) z.2) -
        z.1 / mu_star p * iteratedDeriv i (fam_Z0 p R) z.2 := by
    rintro ⟨μ, y⟩ ⟨hμ, hy⟩
    simp only [mem_Ioi] at hy
    simp only
    have hev : c04_aux_Gosc p R ε μ =ᶠ[𝓝 y] fun t => (fun t => μ * c04_aux_W p R ε (c_log p ε μ, t)) t +
        (fun t => (c_cubic p ε : ℂ) * (μ ^ 3 * c04_aux_W p R ε (c_log p ε μ, t) ^ 3)) t -
        (fun t => μ / mu_star p * fam_Z0 p R t) t := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      unfold c04_aux_Gosc
      rw [hZW μ hμ t ht]; ring
    have c1 := hslice _ hW μ hμ y hy
    have c3 := hslice _ hW3 μ hμ y hy
    have c0 : ContDiffAt ℝ i (fam_Z0 p R) y :=
      (hZ0s.contDiffAt (Ioi_mem_nhds hy)).of_le (by exact_mod_cast le_top)
    rw [hev.iteratedDeriv_eq, iteratedDeriv_fun_sub ((contDiffAt_const.mul c1).add
      (contDiffAt_const.mul (contDiffAt_const.mul c3))) (contDiffAt_const.mul c0),
      iteratedDeriv_fun_add (contDiffAt_const.mul c1) (contDiffAt_const.mul (contDiffAt_const.mul c3)),
      iteratedDeriv_const_mul _ c1, iteratedDeriv_const_mul _ (contDiffAt_const.mul c3),
      iteratedDeriv_const_mul _ c3, iteratedDeriv_const_mul _ c0]
  refine ContinuousOn.congr ?_ hrep
  have hmaps : MapsTo (fun z : ℂ × ℝ => (c_log p ε z.1, z.2)) (Bbar p δ ×ˢ Ioi (R / 2)) (c04_aux_WU p ε) := by
    rintro ⟨μ, y⟩ ⟨hμ, hy⟩; exact hmem μ hμ y hy
  have hg : ContinuousOn (fun z : ℂ × ℝ => (c_log p ε z.1, z.2)) (Bbar p δ ×ˢ Ioi (R / 2)) :=
    ((hclc ε).comp continuous_fst |>.prodMk continuous_snd).continuousOn
  have h1 := (c04_aux_param_iter_cont hU hW i).comp hg hmaps
  have h3 := (c04_aux_param_iter_cont hU hW3 i).comp hg hmaps
  have h0 : ContinuousOn (fun z : ℂ × ℝ => iteratedDeriv i (fam_Z0 p R) z.2) (Bbar p δ ×ˢ Ioi (R / 2)) :=
    (c04_aux_iter_contOn _ _ isOpen_Ioi hZ0s i).comp continuous_snd.continuousOn
      (fun z hz => hz.2)
  exact ((continuous_fst.continuousOn.mul h1).add (continuousOn_const.mul
    ((continuous_fst.continuousOn.pow 3).mul h3))).sub
    ((continuous_fst.continuousOn.div_const _).mul h0)


/-- Joint continuity of `(μ,y) ↦ ∫_y^∞ G_μ` on `B̄ × (3R/4,∞)`. -/
theorem c04_aux_F_cont (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀,
      ContinuousOn (fun z : ℂ × ℝ => ∫ t in Ioi z.2, c04_aux_Gosc p R ε z.1 t)
        (Bbar p δ ×ˢ Ioi (3 * R / 4)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨ε₁, hε₁, R₁, hR₁, hGc⟩ := c04_aux_Gder_cont p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hGb⟩ := c04_aux_G_bounds p hp hp1 δ hδ hδμ
  obtain ⟨CG, hCG, hCGb⟩ := hGb 0
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), fun R hR ε hε => ?_⟩
  have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
  have hR2 : R ≥ R₂ := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  set a := 3 * R / 4 with ha
  have ha0 : 0 < a := by positivity
  have hG0 := hGc R hR1 ε hε1 0
  simp only [iteratedDeriv_zero] at hG0
  -- uniform bound on `[a,R]`
  have hKc : IsCompact (Bbar p δ ×ˢ Icc a R) := (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hG0.mono (prod_mono le_rfl (by
    intro t ht; simp only [mem_Ioi]; have := ht.1; linarith)))
  set K := |M| * R ^ beta p + CG with hK
  have hbound : ∀ μ ∈ Bbar p δ, ∀ t > a, ‖c04_aux_Gosc p R ε μ t‖ ≤ K * t ^ (-beta p) := by
    intro μ hμ t ht
    have ht0 : 0 < t := lt_trans ha0 ht
    have htp : 0 < t ^ (-beta p) := rpow_pos_of_pos ht0 _
    rcases le_or_gt t R with htR | htR
    · have h1 := hM (μ, t) ⟨hμ, ht.le, htR⟩
      simp only at h1
      have h2 : 1 ≤ R ^ beta p * t ^ (-beta p) := by
        rw [rpow_neg ht0.le, ← div_eq_mul_inv, le_div_iff₀ (rpow_pos_of_pos ht0 _), one_mul]
        exact rpow_le_rpow ht0.le htR (by linarith)
      have h3 : M ≤ |M| * (R ^ beta p * t ^ (-beta p)) := by
        have := le_abs_self M; have := abs_nonneg M; nlinarith
      have h4 : 0 ≤ CG * t ^ (-beta p) := by positivity
      rw [hK]; linarith
    · have := (hCGb R hR2 ε hε2 μ hμ t htR.le).2.2.2
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, zero_add] at this
      rw [show -beta p - 1 / p + 1 / p = -beta p by ring] at this
      have h4 : 0 ≤ |M| * R ^ beta p * t ^ (-beta p) := by positivity
      rw [hK]; linarith
  have hBint : Integrable (fun t => K * t ^ (-beta p)) (volume.restrict (Ioi a)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha0).const_mul K
  -- representation as an integral over the fixed set `(a,∞)`
  have hrepr : ∀ z ∈ Bbar p δ ×ˢ Ioi a, ∫ t in Ioi z.2, c04_aux_Gosc p R ε z.1 t =
      ∫ t in Ioi a, (Ioi z.2).indicator (c04_aux_Gosc p R ε z.1) t := by
    rintro ⟨μ, y⟩ ⟨-, hy⟩
    simp only [mem_Ioi] at hy
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hy.le]
  intro z0 hz0
  refine ContinuousWithinAt.congr ?_ (fun z hz => hrepr z hz) (hrepr z0 hz0)
  have hGcont : ∀ μ ∈ Bbar p δ, ContinuousOn (c04_aux_Gosc p R ε μ) (Ioi a) := by
    intro μ hμ t ht
    have hc : Continuous (fun s : ℝ => ((μ, s) : ℂ × ℝ)) := continuous_const.prodMk continuous_id
    have hmt : MapsTo (fun s : ℝ => ((μ, s) : ℂ × ℝ)) (Ioi a) (Bbar p δ ×ˢ Ioi (R / 2)) := by
      intro s hs; refine ⟨hμ, ?_⟩; simp only [mem_Ioi] at hs ⊢; linarith
    exact (hG0 (μ, t) (hmt ht)).comp hc.continuousWithinAt hmt
  apply continuousWithinAt_of_dominated (bound := fun t => K * t ^ (-beta p))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact ((hGcont z.1 hz.1).aestronglyMeasurable measurableSet_Ioi).indicator measurableSet_Ioi
  · filter_upwards [self_mem_nhdsWithin] with z hz
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    exact (norm_indicator_le_norm_self _ _).trans (hbound z.1 hz.1 t ht)
  · exact hBint
  · have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ z0.2 := by
      rw [ae_iff]; simp
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hne] with t ht1 ht2
    rcases lt_or_gt_of_ne ht2 with h | h
    · -- `t < y₀`: eventually `0`
      have hev : (fun z : ℂ × ℝ => (Ioi z.2).indicator (c04_aux_Gosc p R ε z.1) t) =ᶠ[𝓝[Bbar p δ ×ˢ Ioi a] z0]
          fun _ => 0 := by
        have : ∀ᶠ z in 𝓝 z0, t < z.2 := continuous_snd.continuousAt.eventually (Ioi_mem_nhds h)
        filter_upwards [nhdsWithin_le_nhds this] with z hz
        exact indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact hz.le) _
      exact continuousWithinAt_const.congr_of_eventuallyEq hev
        (indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact h.le) _)
    · have hev : (fun z : ℂ × ℝ => (Ioi z.2).indicator (c04_aux_Gosc p R ε z.1) t) =ᶠ[𝓝[Bbar p δ ×ˢ Ioi a] z0]
          fun z => c04_aux_Gosc p R ε z.1 t := by
        have : ∀ᶠ z in 𝓝 z0, z.2 < t := continuous_snd.continuousAt.eventually (Iio_mem_nhds h)
        filter_upwards [nhdsWithin_le_nhds this] with z hz
        exact indicator_of_mem (by exact hz) _
      have hc : ContinuousWithinAt (fun z : ℂ × ℝ => c04_aux_Gosc p R ε z.1 t) (Bbar p δ ×ˢ Ioi a) z0 := by
        have hc : Continuous (fun z : ℂ × ℝ => ((z.1, t) : ℂ × ℝ)) :=
          continuous_fst.prodMk continuous_const
        have hmt : MapsTo (fun z : ℂ × ℝ => ((z.1, t) : ℂ × ℝ)) (Bbar p δ ×ˢ Ioi a)
            (Bbar p δ ×ˢ Ioi (R / 2)) := by
          intro z hz; refine ⟨hz.1, ?_⟩; simp only [mem_Ioi] at ht1 ⊢; linarith
        exact ContinuousWithinAt.comp (f := fun z : ℂ × ℝ => ((z.1, t) : ℂ × ℝ)) (x := z0)
          (hG0 _ (hmt hz0)) hc.continuousWithinAt hmt
      exact hc.congr_of_eventuallyEq hev (indicator_of_mem (by exact h) _)


/-- Joint continuity of `(μ,y) ↦ ∂^k f_osc(y)` on `B̄ × ℝ`. -/
theorem c04_aux_fosc_cont (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ k : ℕ,
      ContinuousOn (fun z : ℂ × ℝ => iteratedDeriv k (fam_osc p R ε z.1) z.2) (Bbar p δ ×ˢ univ) := by
  intro δ hδ hδμ
  obtain ⟨ε₁, hε₁, R₁, hR₁, hGc⟩ := c04_aux_Gder_cont p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hFc⟩ := c04_aux_F_cont p hp hp1 δ hδ hδμ
  obtain ⟨ε₃, hε₃, R₃, hR₃, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  refine ⟨min (min ε₁ ε₂) ε₃, ⟨lt_min (lt_min hε₁.1 hε₂.1) hε₃.1,
    (min_le_left _ _).trans ((min_le_left _ _).trans hε₁.2)⟩, max (max R₁ R₂) R₃,
    le_trans hR₁ ((le_max_left _ _).trans (le_max_left _ _)), fun R hR ε hε k => ?_⟩
  have hR1 : R ≥ R₁ := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hR
  have hR2 : R ≥ R₂ := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hR
  have hR3 : R ≥ R₃ := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε3 : ε ∈ Icc (0 : ℝ) ε₃ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  set T := Bbar p δ ×ˢ Ioi (3 * R / 4) with hT
  -- derivatives of the tail integral
  have hH : ∀ m : ℕ, ContinuousOn (fun z : ℂ × ℝ =>
      iteratedDeriv m (fun x => ∫ t in Ioi x, c04_aux_Gosc p R ε z.1 t) z.2) T := by
    intro m
    rcases m with _ | m
    · simpa only [iteratedDeriv_zero] using hFc R hR2 ε hε2
    · refine ((hGc R hR1 ε hε1 m).neg.mono ?_).congr ?_
      · exact prod_mono le_rfl (Ioi_subset_Ioi (by linarith))
      · rintro ⟨μ, y⟩ ⟨hμ, hy⟩
        simp only [mem_Ioi] at hy
        obtain ⟨-, hGs, -, -, hGi, -⟩ := hstd R hR3 ε hε3 μ hμ
        exact c04_aux_tail_iteratedDeriv _ (R / 2) R hGs hGi m y (by linarith)
  -- Leibniz representation on `T`
  have hrep : ∀ z ∈ T, iteratedDeriv k (fam_osc p R ε z.1) z.2 =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * iteratedDeriv i (fun t => -2 * fam_chiR R t) z.2 *
        (iteratedDeriv (k - i) (fun x => ∫ t in Ioi x, c04_aux_Gosc p R ε z.1 t) z.2).re := by
    rintro ⟨μ, y⟩ ⟨hμ, hy⟩
    simp only [mem_Ioi] at hy
    simp only
    obtain ⟨-, hGs, -, -, hGi, -⟩ := hstd R hR3 ε hε3 μ hμ
    have hFs := c04_aux_tail_contDiffOn _ (R / 2) R hGs hGi
    have hFC : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ∫ t in Ioi x, c04_aux_Gosc p R ε μ t) y :=
      hFs.contDiffAt (Ioi_mem_nhds (by linarith))
    have heq : fam_osc p R ε μ = (fun t => -2 * fam_chiR R t) *
        (fun t => (∫ t' in Ioi t, c04_aux_Gosc p R ε μ t').re) := by
      rw [c04_aux_fosc_eq p R ε μ hR0]; rfl
    have hχ : ContDiffAt ℝ k (fun t => -2 * fam_chiR R t) y :=
      (contDiff_const.mul (c04_aux_chiR_smooth R)).contDiffAt.of_le (by exact_mod_cast le_top)
    have hre : ContDiffAt ℝ k (fun t => (∫ t' in Ioi t, c04_aux_Gosc p R ε μ t').re) y :=
      (Complex.reCLM.contDiff.contDiffAt.comp y hFC).of_le (by exact_mod_cast le_top)
    rw [heq, iteratedDeriv_mul hχ hre]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    obtain ⟨m, hm⟩ : ∃ m, m = k - i := ⟨_, rfl⟩
    rw [← hm, c04_aux_iteratedDeriv_re _ y m (hFC.of_le (by exact_mod_cast le_top))]
  have hsum : ContinuousOn (fun z : ℂ × ℝ => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      iteratedDeriv i (fun t => -2 * fam_chiR R t) z.2 *
        (iteratedDeriv (k - i) (fun x => ∫ t in Ioi x, c04_aux_Gosc p R ε z.1 t) z.2).re) T := by
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    have h1 : Continuous (fun z : ℂ × ℝ => iteratedDeriv i (fun t => -2 * fam_chiR R t) z.2) :=
      ((contDiff_const.mul (c04_aux_chiR_smooth R)).continuous_iteratedDeriv i
        (by exact_mod_cast le_top)).comp continuous_snd
    exact (continuousOn_const.mul h1.continuousOn).mul
      (Complex.continuous_re.comp_continuousOn (hH (k - i)))
  intro z0 hz0
  rcases lt_or_ge z0.2 R with h | h
  · have hev : (fun z : ℂ × ℝ => iteratedDeriv k (fam_osc p R ε z.1) z.2) =ᶠ[𝓝[Bbar p δ ×ˢ univ] z0]
        fun _ => 0 := by
      have : ∀ᶠ z in 𝓝 z0, z.2 < R := continuous_snd.continuousAt.eventually (Iio_mem_nhds h)
      filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with z hz hzS
      obtain ⟨-, -, -, -, -, hfs⟩ := hstd R hR3 ε hε3 z.1 hzS.1
      exact c04_aux_iter_zero_left _ hfs R (fun t ht => by
        unfold fam_osc; exact if_neg (not_lt.mpr ht)) k z.2 hz.le
    have h0 : iteratedDeriv k (fam_osc p R ε z0.1) z0.2 = 0 := by
      obtain ⟨-, -, -, -, -, hfs⟩ := hstd R hR3 ε hε3 z0.1 hz0.1
      exact c04_aux_iter_zero_left _ hfs R (fun t ht => by
        unfold fam_osc; exact if_neg (not_lt.mpr ht)) k z0.2 h.le
    exact continuousWithinAt_const.congr_of_eventuallyEq hev h0
  · have hz0T : z0 ∈ T := ⟨hz0.1, by simp only [mem_Ioi]; linarith⟩
    have hTmem : T ∈ 𝓝[Bbar p δ ×ˢ univ] z0 := by
      have : ∀ᶠ z in 𝓝 z0, 3 * R / 4 < z.2 :=
        continuous_snd.continuousAt.eventually (Ioi_mem_nhds (by linarith))
      filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with z hz hzS
      exact ⟨hzS.1, hz⟩
    exact ((hsum.congr hrep) z0 hz0T).mono_of_mem_nhdsWithin hTmem

/-- On `[-A,A]` (`A ≥ 1`): `1 ≤ (2A)^{|e|} ⟨y⟩^e`. -/
theorem c04_aux_jb_lower (y A e : ℝ) (hA : 1 ≤ A) (hy : |y| ≤ A) : 1 ≤ (2 * A) ^ |e| * jb y ^ e := by
  have hj1 : 1 ≤ jb y := c04_aux_one_le_jb y
  have hj2 : jb y ≤ 2 * A := by
    have : jb y ≤ 1 + |y| := by
      unfold jb
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [abs_nonneg y, sq_abs y]
    linarith
  have hj0 : 0 < jb y := by linarith
  rcases le_total 0 e with he | he
  · have h1 : 1 ≤ (2 * A) ^ |e| := one_le_rpow (by linarith) (abs_nonneg _)
    have h2 : 1 ≤ jb y ^ e := one_le_rpow hj1 he
    nlinarith
  · rw [abs_of_nonpos he]
    have h2 : (2 * A) ^ e ≤ jb y ^ e := rpow_le_rpow_of_nonpos hj0 hj2 he
    have h3 : (2 * A) ^ (-e) * (2 * A) ^ e = 1 := by
      rw [← rpow_add (by linarith)]; simp
    have h4 : 0 ≤ (2 * A) ^ (-e) := (rpow_pos_of_pos (by linarith) _).le
    nlinarith

/-- Tail bound plus continuity gives a global `⟨y⟩^e` bound on `[0,∞)`. -/
theorem c04_aux_jb_bound_pos {E : Type*} [NormedAddCommGroup E] (g : ℝ → E) (hg : Continuous g)
    (e K Y : ℝ) (hY : 1 ≤ Y) (h : ∀ y ≥ Y, ‖g y‖ ≤ K * y ^ e) :
    ∃ C > (0 : ℝ), ∀ y ≥ (0 : ℝ), ‖g y‖ ≤ C * jb y ^ e := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Y)).exists_bound_of_continuousOn
    hg.norm.continuousOn
  refine ⟨|M| * (2 * Y) ^ |e| + |K| * 2 ^ |e| + 1, by positivity, fun y hy => ?_⟩
  have hjp : 0 ≤ jb y ^ e := (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
  have hA : 0 ≤ |K| * 2 ^ |e| * jb y ^ e := by positivity
  rcases le_or_gt y Y with h1 | h1
  · have hb := hM y ⟨hy, h1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hb
    have hl := c04_aux_jb_lower y Y e hY (by rw [abs_of_nonneg hy]; exact h1)
    have : M ≤ |M| * ((2 * Y) ^ |e| * jb y ^ e) := by
      have := le_abs_self M
      have h0 : 0 ≤ |M| := abs_nonneg M
      nlinarith
    nlinarith
  · have hb := h y h1.le
    have hc := c04_aux_rpow_le_jb_gen y e (by linarith)
    have hy0 : 0 < y := by linarith
    have : K * y ^ e ≤ |K| * (2 ^ |e| * jb y ^ e) :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) (rpow_pos_of_pos hy0 _).le).trans
        (mul_le_mul_of_nonneg_left hc (abs_nonneg K))
    have h0 : 0 ≤ |M| * (2 * Y) ^ |e| * jb y ^ e := by positivity
    nlinarith

/-- Same on `(-∞,0]`. -/
theorem c04_aux_jb_bound_neg {E : Type*} [NormedAddCommGroup E] (g : ℝ → E) (hg : Continuous g)
    (e K Y : ℝ) (hY : 1 ≤ Y) (h : ∀ y ≤ -Y, ‖g y‖ ≤ K * |y| ^ e) :
    ∃ C > (0 : ℝ), ∀ y ≤ (0 : ℝ), ‖g y‖ ≤ C * jb y ^ e := by
  obtain ⟨C, hC, hb⟩ := c04_aux_jb_bound_pos (fun y => g (-y)) (hg.comp continuous_neg) e K Y hY
    (fun y hy => by
      have := h (-y) (by linarith)
      rwa [abs_neg, abs_of_nonneg (by linarith)] at this)
  refine ⟨C, hC, fun y hy => ?_⟩
  have := hb (-y) (by linarith)
  simp only [neg_neg] at this
  have hj : jb (-y) = jb y := by unfold jb; rw [neg_sq]
  rwa [hj] at this


/-- `f_{0,+}(y) = -∫_y^∞ Z₀` and the decay `|f_{0,+}(y)| ≤ K y^{-β-1/p}` for large `y`. -/
theorem c04_aux_f0plus_decay (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ K Y : ℝ, 1 ≤ Y ∧ ∀ y ≥ Y, ‖c04_linear_seed_plus p y‖ ≤ K * y ^ (-beta p - 1 / p) := by
  have hp0 : 0 < p := by linarith
  have hμs' : 0 < ‖mu_star p‖ := by
    rw [mu_star, norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    have : 0 < Real.sqrt (2 * π * p) := Real.sqrt_pos.mpr (by positivity)
    rw [abs_of_pos this]; positivity
  set δ := ‖mu_star p‖ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨-, -, hplus, -, hplus0, -⟩ := c04_seed_decomposition p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, -, -, -, hb3⟩ := c04_phase_basic p hp hp1 δ hδ0 le_rfl
  obtain ⟨ε₂, hε₂, R₂, hR₂, hstd⟩ := c04_aux_std p hp hp1 δ hδ0 le_rfl
  obtain ⟨ε₃, hε₃, R₃, hR₃, -, Cp, hCp, hprim⟩ := c04_Z_primitive p hp hp1 δ hδ0 le_rfl
  set R := max (max R₁ R₂) R₃ with hR
  have hR1 : R ≥ R₁ := (le_max_left _ _).trans (le_max_left _ _)
  have hR2 : R ≥ R₂ := (le_max_right _ _).trans (le_max_left _ _)
  have hR3 : R ≥ R₃ := le_max_right _ _
  have hμ0 : mu_star p ∈ Bbar p δ := Metric.mem_closedBall_self hδ0.le
  refine ⟨Cp, R, by linarith, fun y hy => ?_⟩
  obtain ⟨-, -, i0, -, -, -⟩ := hstd R hR2 0 ⟨le_rfl, hε₂.1.le⟩ _ hμ0
  have hint : IntegrableOn (fam_Z0 p R) (Ioi y) := i0.mono_set (Ioi_subset_Ioi hy)
  have hyR2 : y > R / 2 := by linarith
  have hder : ∀ x ∈ Ioi y, HasDerivAt (c04_linear_seed_plus p) (fam_Z0 p R x) x := by
    intro x hx
    have hx' : x > R / 2 := lt_trans hyR2 hx
    rw [(hb3 R hR1 _ hμ0 x hx').2.2.2]
    exact ((hplus.differentiable (by simp)) x).hasDerivAt
  have hid := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hplus.differentiable (by simp)) y).continuousAt.continuousWithinAt hder hint
    (hplus0.mono_left (atTop_le_cocompact))
  have ha := (hprim R hR3 0 ⟨le_rfl, hε₃.1.le⟩ _ hμ0 y hy).1
  have e : c04_linear_seed_plus p y = -∫ t in Ioi y, fam_Z p R 0 (mu_star p) t := by
    have : fam_Z p R 0 (mu_star p) = fam_Z0 p R := rfl
    rw [this, hid]; ring
  rw [e, norm_neg]; exact ha


/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_iter_add4 (A B C D : ℝ → ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (hD : ContDiff ℝ (⊤ : ℕ∞) D) (m : ℕ) (y : ℝ) :
    iteratedDeriv m (fun t => A t + B t + C t + D t) y =
      iteratedDeriv m A y + iteratedDeriv m B y + iteratedDeriv m C y + iteratedDeriv m D y := by
  have hA' := c04_aux_smooth_at hA m y
  have hB' := c04_aux_smooth_at hB m y
  have hC' := c04_aux_smooth_at hC m y
  have hD' := c04_aux_smooth_at hD m y
  rw [iteratedDeriv_fun_add ((hA'.add hB').add hC') hD', iteratedDeriv_fun_add (hA'.add hB') hC',
    iteratedDeriv_fun_add hA' hB']

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_iter_re_const (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c : ℂ) (m : ℕ) (y : ℝ) :
    iteratedDeriv m (fun t => 2 * (c * F t).re) y = 2 * (c * iteratedDeriv m F y).re := by
  have h1 : ContDiffAt ℝ m (fun t => c * F t) y := c04_aux_smooth_at (contDiff_const.mul hF) m y
  have h2 : ContDiffAt ℝ m (fun t => (c * F t).re) y :=
    c04_aux_smooth_at (Complex.reCLM.contDiff.comp (contDiff_const.mul hF)) m y
  rw [iteratedDeriv_const_mul _ h2, c04_aux_iteratedDeriv_re _ y m h1,
    iteratedDeriv_const_mul _ (c04_aux_smooth_at hF m y)]

/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_profile_bounds_main (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ j : ℕ, ∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        (∀ y ≥ (0 : ℝ), |approximate_solution_family p R ε μ y| ≤ C * jb y ^ (-p) ∧
          |iteratedDeriv (j + 1) (approximate_solution_family p R ε μ) y| ≤
            C * jb y ^ (-beta p + j / p)) ∧
        (∀ y ≤ (0 : ℝ),
          |iteratedDeriv j (fun t => approximate_solution_family p R ε μ t + t) y| ≤
            C * jb y ^ (-p - j))) ∧
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family p R ε μ)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hμs' : 0 < ‖mu_star p‖ := by linarith
  have hμs : mu_star p ≠ 0 := norm_pos_iff.mp hμs'
  have hβ1 : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  have hβp : beta p ≤ p + 1 := by
    unfold beta; rw [div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨-, -, hplus, -, -, -⟩ := c04_seed_decomposition p hp hp1
  have hf0s : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed p) :=
    (c04_seed_decomposition p hp hp1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hlows : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_low p) := by
    have : c04_linear_seed_low p = fun t => c04_linear_seed p t - 2 * (c04_linear_seed_plus p t).re := rfl
    rw [this]; exact hf0s.sub (contDiff_const.mul (Complex.reCLM.contDiff.comp hplus))
  obtain ⟨y₀, hy₀, -, hamp⟩ := c04_seed_amplitude p hp hp1
  obtain ⟨-, -, -, -, -, -, hμseed⟩ := approx_linear_seed p hp hp1
  obtain ⟨Kd, Yd, hYd, hdecay⟩ := c04_aux_f0plus_decay p hp hp1
  obtain ⟨ε₁, hε₁, R₁, hR₁, hfr⟩ := c04_family_regions p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hpd, hzero, -⟩ := approx_phase_differences p hp hp1 δ hδ hδμ
  have hε₀pos : 0 < min ε₁ ε₂ := lt_min hε₁.1 hε₂.1
  have hε₀1 : min ε₁ ε₂ ≤ 1 := (min_le_left _ _).trans hε₁.2
  have hR₀2 : max R₁ R₂ ≥ 2 := le_trans hR₁ (le_max_left _ _)
  have hsmooth : ∀ R ≥ max R₁ R₂, ∀ ε ∈ Icc (0 : ℝ) (min ε₁ ε₂), ∀ μ ∈ Bbar p δ,
      ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family p R ε μ) := fun R hR ε hε μ hμ =>
    ((hfr R (le_trans (le_max_left _ _) hR)).1 ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩ μ hμ).1
  refine ⟨_, ⟨hε₀pos, hε₀1⟩, _, hR₀2, fun j => ?_, hsmooth⟩
  -- the pieces
  have hW0 : ∀ m : ℕ, ∀ y > (0 : ℝ),
      iteratedDeriv m (fun t => c04_linear_seed_low p t - corner t) y = iteratedDeriv m (c04_linear_seed_low p) y := by
    intro m y hy
    have : (fun t => c04_linear_seed_low p t - corner t) =ᶠ[𝓝 y] c04_linear_seed_low p := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      simp only [corner, max_eq_right (show -t ≤ 0 by linarith [mem_Ioi.mp ht]), sub_zero]
    exact this.iteratedDeriv_eq m
  obtain ⟨Ct1, hCt1, ht1, -⟩ := c04_seed_tails p hp hp1 (j + 1)
  obtain ⟨Ct0, hCt0, ht0, -⟩ := c04_seed_tails p hp hp1 0
  obtain ⟨Ctj, hCtj, -, htj⟩ := c04_seed_tails p hp hp1 j
  obtain ⟨Ca, hCa, hCab⟩ := hamp j
  obtain ⟨Cn, hCn, hCnb⟩ := c04_f0plus_negative p hp hp1 j (p + j) (by positivity)
  obtain ⟨Cs0, hCs0, hs0⟩ := c04_aux_fslow_bound p hp hp1 0
  obtain ⟨Cs1, hCs1, hs1⟩ := c04_aux_fslow_bound p hp hp1 (j + 1)
  obtain ⟨Csj, hCsj, hsj⟩ := c04_aux_fslow_bound p hp hp1 j
  obtain ⟨Co0, hCo0, ho0⟩ := hpd 0
  obtain ⟨Co1, hCo1, ho1⟩ := hpd (j + 1)
  -- global bounds via the generic lemma
  obtain ⟨C1, hC1, hb1⟩ := c04_aux_jb_bound_pos (iteratedDeriv (j + 1) (c04_linear_seed_low p))
    (hlows.continuous_iteratedDeriv _ (by exact_mod_cast le_top)) (-p - ((j + 1 : ℕ) : ℝ)) Ct1 1 le_rfl
    (fun y hy => by
      have := ht1 y (by rw [abs_of_nonneg (by linarith)]; exact hy)
      rwa [hW0 _ y (by linarith), abs_of_nonneg (by linarith : (0 : ℝ) ≤ y)] at this)
  obtain ⟨C0, hC0, hb0⟩ := c04_aux_jb_bound_pos (c04_linear_seed_low p) hlows.continuous (-p) Ct0 1 le_rfl
    (fun y hy => by
      have := ht0 y (by rw [abs_of_nonneg (by linarith)]; exact hy)
      rw [hW0 0 y (by linarith), abs_of_nonneg (by linarith : (0 : ℝ) ≤ y)] at this
      simpa using this)
  obtain ⟨C2, hC2, hb2⟩ := c04_aux_jb_bound_pos (iteratedDeriv (j + 1) (c04_linear_seed_plus p))
    (hplus.continuous_iteratedDeriv _ (by exact_mod_cast le_top)) (-beta p + j / p) Ca y₀ (by linarith)
    (fun y hy => by rw [iteratedDeriv_succ']; exact ((hCab y hy).2.2))
  obtain ⟨C3, hC3, hb3⟩ := c04_aux_jb_bound_pos (c04_linear_seed_plus p) hplus.continuous (-p) |Kd| Yd hYd
    (fun y hy => by
      refine (hdecay y hy).trans ?_
      have hy1 : 1 ≤ y := le_trans hYd hy
      have : y ^ (-beta p - 1 / p) ≤ y ^ (-p) := by
        apply rpow_le_rpow_of_exponent_le hy1
        have : 0 < 1 / p := by positivity
        linarith
      exact mul_le_mul (le_abs_self Kd) this (rpow_pos_of_pos (by linarith) _).le (abs_nonneg _))
  obtain ⟨C4, hC4, hb4⟩ := c04_aux_jb_bound_neg (iteratedDeriv j (fun t => c04_linear_seed p t + t))
    ((hf0s.add contDiff_id).continuous_iteratedDeriv _ (by exact_mod_cast le_top)) (-p - j) Ctj 1 le_rfl
    (fun y hy => htj y hy)
  obtain ⟨C5, hC5, hb5⟩ := c04_aux_jb_bound_neg (iteratedDeriv j (c04_linear_seed_plus p))
    (hplus.continuous_iteratedDeriv _ (by exact_mod_cast le_top)) (-p - j) Cn 1 le_rfl
    (fun y hy => by
      have := hCnb y hy
      rwa [show -(p + (j : ℝ)) = -p - j by ring] at this)
  set S := C0 + C1 + C2 + C3 + C4 + C5 + Cs0 + Cs1 + Csj + Co0 + Co1 with hS
  refine ⟨8 * S + 1, by positivity, fun R hR ε hε μ hμ => ?_⟩
  have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
  have hR2 : R ≥ R₂ := le_trans (le_max_right _ _) hR
  have hR2' : (2 : ℝ) ≤ R := le_trans hR₀2 hR
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hε₀1⟩
  have hμn : ‖μ‖ ≤ 2 * ‖mu_star p‖ := by
    have := norm_le_of_mem_closedBall hμ; linarith
  have hq : ‖μ / mu_star p‖ ≤ 2 := by rw [norm_div, div_le_iff₀ hμs']; linarith
  have hq1 : ‖μ / mu_star p - 1‖ ≤ 3 := by
    have := norm_sub_le (μ / mu_star p) 1; rw [norm_one] at this; linarith
  obtain ⟨hfs, -, -, -, -, -, -⟩ := (hfr R hR1).1 ε hε1 μ hμ
  have hslows : ContDiff ℝ (⊤ : ℕ∞) (fam_slow p R ε) := c04_aux_fam_slow_smooth p R ε (by linarith)
  have hoscs : ContDiff ℝ (⊤ : ℕ∞) (fam_osc p R ε μ) := by
    have e : fam_osc p R ε μ = fun t => approximate_solution_family p R ε μ t -
        c04_linear_seed_mu p μ t - fam_slow p R ε t := by
      funext t; unfold approximate_solution_family; ring
    rw [e]; exact (hfs.sub (hμseed μ).1).sub hslows
  have hjp : ∀ (y e : ℝ), 0 ≤ jb y ^ e := fun y e =>
    (rpow_pos_of_pos (lt_of_lt_of_le one_pos (c04_aux_one_le_jb y)) _).le
  have hjmono : ∀ y (e1 e2 : ℝ), e1 ≤ e2 → jb y ^ e1 ≤ jb y ^ e2 := fun y e1 e2 h =>
    rpow_le_rpow_of_exponent_le (c04_aux_one_le_jb y) h
  have hosc_zero : ∀ m : ℕ, ∀ y ≤ R, iteratedDeriv m (fam_osc p R ε μ) y = 0 := fun m y hy =>
    c04_aux_iter_zero_left _ hoscs R (fun t ht => hzero R hR2 ε hε2 μ hμ t ht) m y hy
  have hsplitp : approximate_solution_family p R ε μ = fun t => c04_linear_seed_low p t +
      2 * (μ / mu_star p * c04_linear_seed_plus p t).re + fam_slow p R ε t + fam_osc p R ε μ t := by
    funext t; exact c04_aux_family_split p R ε μ t
  have hsplitn : (fun t => approximate_solution_family p R ε μ t + t) = fun t =>
      (c04_linear_seed p t + t) + 2 * ((μ / mu_star p - 1) * c04_linear_seed_plus p t).re +
        fam_slow p R ε t + fam_osc p R ε μ t := by
    funext t; unfold approximate_solution_family c04_linear_seed_mu; ring
  have hre2 : ∀ (c : ℂ) (F : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ (⊤ : ℕ∞) (fun t => 2 * (c * F t).re) := fun c F hF =>
    contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_const.mul hF))
  have hrebd : ∀ (c : ℂ) (w : ℂ) (K : ℝ), ‖c‖ ≤ K → |2 * (c * w).re| ≤ 2 * K * ‖w‖ := by
    intro c w K hK
    rw [abs_mul, abs_two]
    have h1 : ‖c * w‖ ≤ K * ‖w‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hK (norm_nonneg w)
    have := (Complex.abs_re_le_norm (c * w)).trans h1
    linarith
  have hSpos : 0 ≤ S := by rw [hS]; positivity
  refine ⟨fun y hy => ⟨?_, ?_⟩, fun y hy => ?_⟩
  · -- value, `y ≥ 0`
    have hval := congrFun hsplitp y
    rw [hval]
    have a1 := hb0 y hy
    have a2 := hrebd (μ / mu_star p) (c04_linear_seed_plus p y) 2 hq
    have a3 := hb3 y hy
    have a4 := hs0 R hR2' ε hεI y
    simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at a4
    have a4' : |fam_slow p R ε y| ≤ Cs0 * jb y ^ (-p) := by
      refine a4.trans ?_
      have := mul_le_mul_of_nonneg_right hεI.2 (mul_nonneg hCs0.le (hjp y (-p)))
      linarith
    have a5 : |fam_osc p R ε μ y| ≤ Co0 * jb y ^ (-p) := by
      rcases le_or_gt R y with hyR | hyR
      · have := (ho0 R hR2 ε hε2 μ hμ y hyR).2.2.2
        simp only [iteratedDeriv_zero, CharP.cast_eq_zero, zero_sub] at this
        refine this.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (hjmono y _ _ ?_)) hCo0.le)
        have : 0 < 1 / p := by positivity
        rw [neg_div]; linarith
      · rw [hzero R hR2 ε hε2 μ hμ y hyR.le, abs_zero]; exact mul_nonneg hCo0.le (hjp y _)
    rw [Real.norm_eq_abs] at a1
    have tri : |c04_linear_seed_low p y + 2 * (μ / mu_star p * c04_linear_seed_plus p y).re +
        fam_slow p R ε y + fam_osc p R ε μ y| ≤ |c04_linear_seed_low p y| +
        |2 * (μ / mu_star p * c04_linear_seed_plus p y).re| + |fam_slow p R ε y| +
        |fam_osc p R ε μ y| := by
      have := abs_add_le (c04_linear_seed_low p y + 2 * (μ / mu_star p * c04_linear_seed_plus p y).re +
        fam_slow p R ε y) (fam_osc p R ε μ y)
      have := abs_add_le (c04_linear_seed_low p y + 2 * (μ / mu_star p * c04_linear_seed_plus p y).re)
        (fam_slow p R ε y)
      have := abs_add_le (c04_linear_seed_low p y) (2 * (μ / mu_star p * c04_linear_seed_plus p y).re)
      linarith
    have hJ := hjp y (-p)
    have : C0 * jb y ^ (-p) + 2 * 2 * (C3 * jb y ^ (-p)) + Cs0 * jb y ^ (-p) + Co0 * jb y ^ (-p) ≤
        (8 * S + 1) * jb y ^ (-p) := by
      have h8 : C0 + 4 * C3 + Cs0 + Co0 ≤ 8 * S + 1 := by rw [hS]; linarith
      have := mul_le_mul_of_nonneg_right h8 hJ
      linarith
    linarith
  · -- derivative, `y ≥ 0`
    rw [hsplitp, c04_aux_iter_add4 _ _ _ _ hlows (hre2 _ _ hplus) hslows hoscs,
      c04_aux_iter_re_const _ hplus]
    set e := -beta p + j / p with he
    have a1 : |iteratedDeriv (j + 1) (c04_linear_seed_low p) y| ≤ C1 * jb y ^ e := by
      have := hb1 y hy
      rw [Real.norm_eq_abs] at this
      refine this.trans (mul_le_mul_of_nonneg_left (hjmono y _ _ ?_) hC1.le)
      have : (0 : ℝ) ≤ j / p := by positivity
      push_cast; linarith
    have a2 := hrebd (μ / mu_star p) (iteratedDeriv (j + 1) (c04_linear_seed_plus p) y) 2 hq
    have a3 := hb2 y hy
    have a4 := hs1 R hR2' ε hεI y
    have a4' : |iteratedDeriv (j + 1) (fam_slow p R ε) y| ≤ Cs1 * jb y ^ e := by
      refine a4.trans ?_
      have h1 : jb y ^ (-p - ((j + 1 : ℕ) : ℝ)) ≤ jb y ^ e := hjmono y _ _ (by
        have : (0 : ℝ) ≤ j / p := by positivity
        push_cast; linarith)
      have h2 := mul_le_mul hεI.2 h1 (hjp y _) zero_le_one
      have h3 := mul_le_mul_of_nonneg_left h2 hCs1.le
      linarith
    have a5 : |iteratedDeriv (j + 1) (fam_osc p R ε μ) y| ≤ Co1 * jb y ^ e := by
      rcases le_or_gt R y with hyR | hyR
      · have := (ho1 R hR2 ε hε2 μ hμ y hyR).2.2.2
        refine this.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (le_of_eq ?_)) hCo1.le)
        rw [he]; push_cast; ring_nf
      · rw [hosc_zero _ y hyR.le, abs_zero]; exact mul_nonneg hCo1.le (hjp y _)
    have tri := abs_add_le (iteratedDeriv (j + 1) (c04_linear_seed_low p) y +
        2 * (μ / mu_star p * iteratedDeriv (j + 1) (c04_linear_seed_plus p) y).re +
        iteratedDeriv (j + 1) (fam_slow p R ε) y) (iteratedDeriv (j + 1) (fam_osc p R ε μ) y)
    have tri2 := abs_add_le (iteratedDeriv (j + 1) (c04_linear_seed_low p) y +
        2 * (μ / mu_star p * iteratedDeriv (j + 1) (c04_linear_seed_plus p) y).re)
        (iteratedDeriv (j + 1) (fam_slow p R ε) y)
    have tri3 := abs_add_le (iteratedDeriv (j + 1) (c04_linear_seed_low p) y)
        (2 * (μ / mu_star p * iteratedDeriv (j + 1) (c04_linear_seed_plus p) y).re)
    have hJ := hjp y e
    have : C1 * jb y ^ e + 2 * 2 * (C2 * jb y ^ e) + Cs1 * jb y ^ e + Co1 * jb y ^ e ≤
        (8 * S + 1) * jb y ^ e := by
      have h8 : C1 + 4 * C2 + Cs1 + Co1 ≤ 8 * S + 1 := by rw [hS]; linarith
      have := mul_le_mul_of_nonneg_right h8 hJ
      linarith
    linarith
  · -- `y ≤ 0`
    have h4 := c04_aux_iter_add4 (fun t => c04_linear_seed p t + t)
      (fun t => 2 * ((μ / mu_star p - 1) * c04_linear_seed_plus p t).re) (fam_slow p R ε)
      (fam_osc p R ε μ) (hf0s.add contDiff_id) (hre2 _ _ hplus) hslows hoscs j y
    beta_reduce at h4
    rw [hsplitn, h4, c04_aux_iter_re_const _ hplus, hosc_zero j y (by linarith), add_zero]
    have a1 := hb4 y hy
    rw [Real.norm_eq_abs] at a1
    have a2 := hrebd (μ / mu_star p - 1) (iteratedDeriv j (c04_linear_seed_plus p) y) 3 hq1
    have a3 := hb5 y hy
    have a4 := hsj R hR2' ε hεI y
    have a4' : |iteratedDeriv j (fam_slow p R ε) y| ≤ Csj * jb y ^ (-p - j) := by
      refine a4.trans ?_
      have := mul_le_mul_of_nonneg_right hεI.2 (mul_nonneg hCsj.le (hjp y (-p - j)))
      linarith
    have tri2 := abs_add_le (iteratedDeriv j (fun t => c04_linear_seed p t + t) y +
        2 * ((μ / mu_star p - 1) * iteratedDeriv j (c04_linear_seed_plus p) y).re)
        (iteratedDeriv j (fam_slow p R ε) y)
    have tri3 := abs_add_le (iteratedDeriv j (fun t => c04_linear_seed p t + t) y)
        (2 * ((μ / mu_star p - 1) * iteratedDeriv j (c04_linear_seed_plus p) y).re)
    have hJ := hjp y (-p - j)
    have : C4 * jb y ^ (-p - j) + 2 * 3 * (C5 * jb y ^ (-p - j)) + Csj * jb y ^ (-p - j) ≤
        (8 * S + 1) * jb y ^ (-p - j) := by
      have h8 : C4 + 6 * C5 + Csj ≤ 8 * S + 1 := by rw [hS]; linarith
      have := mul_le_mul_of_nonneg_right h8 hJ
      linarith
    linarith


/-- Auxiliary lemma (chapter 04). -/
theorem c04_aux_family_cont (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀,
      ∀ (k : ℕ) (K : Set ℝ), IsCompact K → ∀ μ₀ ∈ Bbar p δ,
        TendstoUniformlyOn
          (fun (μ : ℂ) (y : ℝ) => iteratedDeriv k (approximate_solution_family p R ε μ) y)
          (iteratedDeriv k (approximate_solution_family p R ε μ₀)) (𝓝[Bbar p δ] μ₀) K := by
  intro δ hδ hδμ
  have hμs' : 0 < ‖mu_star p‖ := by linarith
  obtain ⟨-, -, hplus, -, -, -⟩ := c04_seed_decomposition p hp hp1
  have hf0s : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed p) :=
    (c04_seed_decomposition p hp hp1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ε₁, hε₁, R₁, hR₁, hfc⟩ := c04_aux_fosc_cont p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hstd⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), fun R hR ε hε k K hK μ₀ hμ₀ => ?_⟩
  have hR1 : R ≥ R₁ := le_trans (le_max_left _ _) hR
  have hR2 : R ≥ R₂ := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hslows : ContDiff ℝ (⊤ : ℕ∞) (fam_slow p R ε) := c04_aux_fam_slow_smooth p R ε hR0
  have hre2 : ∀ (c : ℂ), ContDiff ℝ (⊤ : ℕ∞) (fun t => 2 * (c * c04_linear_seed_plus p t).re) := fun c =>
    contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_const.mul hplus))
  -- joint continuity on `B̄ × ℝ`
  have hrep : ∀ z ∈ Bbar p δ ×ˢ (univ : Set ℝ),
      iteratedDeriv k (approximate_solution_family p R ε z.1) z.2 =
        iteratedDeriv k (c04_linear_seed p) z.2 +
        2 * ((z.1 / mu_star p - 1) * iteratedDeriv k (c04_linear_seed_plus p) z.2).re +
        iteratedDeriv k (fam_slow p R ε) z.2 + iteratedDeriv k (fam_osc p R ε z.1) z.2 := by
    rintro ⟨μ, y⟩ ⟨hμ, -⟩
    obtain ⟨-, -, -, -, -, hfs⟩ := hstd R hR2 ε hε2 μ hμ
    have e : approximate_solution_family p R ε μ = fun t => c04_linear_seed p t +
        2 * ((μ / mu_star p - 1) * c04_linear_seed_plus p t).re + fam_slow p R ε t + fam_osc p R ε μ t := by
      funext t; rfl
    simp only
    rw [e, c04_aux_iter_add4 _ _ _ _ hf0s (hre2 _) hslows hfs, c04_aux_iter_re_const _ hplus]
  have hcont : ContinuousOn (fun z : ℂ × ℝ => iteratedDeriv k (approximate_solution_family p R ε z.1) z.2)
      (Bbar p δ ×ˢ univ) := by
    refine ContinuousOn.congr ?_ hrep
    have c1 : Continuous (fun z : ℂ × ℝ => iteratedDeriv k (c04_linear_seed p) z.2) :=
      (hf0s.continuous_iteratedDeriv k (by exact_mod_cast le_top)).comp continuous_snd
    have c2 : Continuous (fun z : ℂ × ℝ => iteratedDeriv k (c04_linear_seed_plus p) z.2) :=
      (hplus.continuous_iteratedDeriv k (by exact_mod_cast le_top)).comp continuous_snd
    have c3 : Continuous (fun z : ℂ × ℝ => iteratedDeriv k (fam_slow p R ε) z.2) :=
      (hslows.continuous_iteratedDeriv k (by exact_mod_cast le_top)).comp continuous_snd
    have c2' : Continuous (fun z : ℂ × ℝ =>
        2 * ((z.1 / mu_star p - 1) * iteratedDeriv k (c04_linear_seed_plus p) z.2).re) :=
      continuous_const.mul (Complex.continuous_re.comp
        (((continuous_fst.div_const _).sub continuous_const).mul c2))
    exact ((c1.add c2').add c3).continuousOn.add (hfc R hR1 ε hε1 k)
  -- uniform convergence on the compact `K`
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hK.mem_uniformity_of_prod
    (f := fun (μ : ℂ) (y : ℝ) => iteratedDeriv k (approximate_solution_family p R ε μ) y)
    (hcont.mono (prod_mono le_rfl (subset_univ K))) hμ₀ (symmetrize_mem_uniformity hu)
  filter_upwards [hv] with μ hμ y hy
  exact SetRel.symmetrize_subset_inv (hvu μ hμ y hy)


/-- Blueprint: prop:approx_profile_bounds.  `|f̄| ≤ C₀⟨y⟩^{-p}`, `|∂^{j+1} f̄| ≤ C_j⟨y⟩^{-β+j/p}`
(`y ≥ 0`), `|∂^j(f̄ + y)| ≤ C_j⟨y⟩^{-p-j}` (`y ≤ 0`), uniformly in `ε, μ, R`; continuity of
`μ ↦ f̄_{ε,μ}` into `C^k(K)` for every compact `K`; `f̄` is smooth. -/
theorem approx_profile_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ j : ℕ, ∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        (∀ y ≥ (0 : ℝ), |approximate_solution_family p R ε μ y| ≤ C * jb y ^ (-p) ∧
          |iteratedDeriv (j + 1) (approximate_solution_family p R ε μ) y| ≤
            C * jb y ^ (-beta p + j / p)) ∧
        (∀ y ≤ (0 : ℝ),
          |iteratedDeriv j (fun t => approximate_solution_family p R ε μ t + t) y| ≤
            C * jb y ^ (-p - j))) ∧
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀,
        (∀ μ ∈ Bbar p δ, ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family p R ε μ)) ∧
        ∀ (k : ℕ) (K : Set ℝ), IsCompact K → ∀ μ₀ ∈ Bbar p δ,
          TendstoUniformlyOn
            (fun (μ : ℂ) (y : ℝ) => iteratedDeriv k (approximate_solution_family p R ε μ) y)
            (iteratedDeriv k (approximate_solution_family p R ε μ₀)) (𝓝[Bbar p δ] μ₀) K) := by
  intro δ hδ hδμ
  obtain ⟨ε₁, hε₁, R₁, hR₁, hb, hs⟩ := c04_aux_profile_bounds_main p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hc⟩ := c04_aux_family_cont p hp hp1 δ hδ hδμ
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), fun j => ?_, fun R hR ε hε => ⟨fun μ hμ => ?_, ?_⟩⟩
  · obtain ⟨C, hC, hCb⟩ := hb j
    exact ⟨C, hC, fun R hR ε hε μ hμ => hCb R (le_trans (le_max_left _ _) hR) ε
      ⟨hε.1, hε.2.trans (min_le_left _ _)⟩ μ hμ⟩
  · exact hs R (le_trans (le_max_left _ _) hR) ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩ μ hμ
  · exact hc R (le_trans (le_max_right _ _) hR) ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩


/-! ### Residual integrability and the residual identity -/

open scoped NNReal

theorem c04_aux_ri_A_mem (p ε u : ℝ) (hp0 : 0 < p) (hε : 0 ≤ ε) :
    0 < A_eps p ε u ∧ A_eps p ε u ≤ 1 := by
  unfold A_eps
  have h1 : 1 ≤ 1 + ε * u ^ 2 := by nlinarith [sq_nonneg u]
  exact ⟨rpow_pos_of_pos (by linarith) _, rpow_le_one_of_one_le_of_nonpos h1 (by linarith)⟩

theorem c04_aux_ri_A_hasDeriv (p ε u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (A_eps p ε) (2 * ε * u * (-(p + 1) / 2) * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1)) u := by
  have hb : 0 < 1 + ε * u ^ 2 := by nlinarith [sq_nonneg u]
  have h1 : HasDerivAt (fun u : ℝ => 1 + ε * u ^ 2) (2 * ε * u) u := by
    have := ((hasDerivAt_pow 2 u).const_mul ε).const_add 1
    convert this using 1; push_cast; ring
  exact h1.rpow_const (Or.inl hb.ne')

theorem c04_aux_ri_A_deriv_bound (p ε u : ℝ) (hp0 : 0 < p) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |deriv (A_eps p ε) u| ≤ p + 1 := by
  rw [(c04_aux_ri_A_hasDeriv p ε u hε0).deriv]
  have hb : 1 ≤ 1 + ε * u ^ 2 := by nlinarith [sq_nonneg u]
  have hb0 : 0 < 1 + ε * u ^ 2 := by linarith
  have hpow : (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) ≤ (1 + ε * u ^ 2) ^ (-1 : ℝ) :=
    rpow_le_rpow_of_exponent_le hb (by linarith)
  have hpos : 0 ≤ (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) := (rpow_pos_of_pos hb0 _).le
  rw [rpow_neg_one] at hpow
  have hεu : ε * |u| ≤ 1 + ε * u ^ 2 := by
    have : ε * |u| ≤ (ε + ε * u ^ 2) / 2 := by
      have h := sq_nonneg (|u| - 1)
      rw [sub_sq, sq_abs] at h
      nlinarith
    linarith
  rw [show 2 * ε * u * (-(p + 1) / 2) * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) =
    -((p + 1) * (ε * u) * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1)) by ring, abs_neg, abs_mul, abs_mul,
    abs_of_pos (by linarith : (0:ℝ) < p + 1), abs_of_nonneg hpos, abs_mul, abs_of_nonneg hε0]
  have : ε * |u| * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) ≤ 1 := by
    calc ε * |u| * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) ≤ (1 + ε * u ^ 2) * (1 + ε * u ^ 2)⁻¹ :=
          mul_le_mul hεu hpow hpos (by linarith)
      _ = 1 := mul_inv_cancel₀ hb0.ne'
  nlinarith

theorem c04_aux_ri_secant_bound (f : ℝ → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (y z : ℝ) :
    |c01_secant f y z| ≤ L := by
  unfold c01_secant
  split_ifs with h
  · exact (Real.norm_eq_abs _ ▸ norm_deriv_le_of_lipschitz hf)
  · have hyz : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr h)
    rw [abs_div, div_le_iff₀ hyz]
    have := hf.dist_le_mul y z
    simpa [Real.dist_eq] using this

theorem c04_aux_ri_secant_meas (f : ℝ → ℝ) (hf : Continuous f) (y : ℝ) :
    Measurable (fun z => c01_secant f y z) := by
  unfold c01_secant
  refine Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const ?_
  exact ((measurable_const.sub hf.measurable).div (measurable_const.sub measurable_id))

/-- Lipschitz constant from a derivative bound. -/
theorem c04_aux_ri_lip (f : ℝ → ℝ) (hf : Differentiable ℝ f) (M : ℝ) (hM : ∀ z, |deriv f z| ≤ M) :
    LipschitzWith (Real.toNNReal M) f := by
  refine lipschitzWith_of_nnnorm_deriv_le hf fun z => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal']
  exact (hM z).trans (le_max_left _ _)

/-- Kernel times a bounded measurable factor. -/
theorem c04_aux_ri_kernel_mul (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (M : ℝ) (hM : ∀ z, |g z| ≤ M) (y : ℝ) (B : ℝ → ℝ) (hB : Measurable B) (c : ℝ)
    (hBc : ∀ z, |B z| ≤ c) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1) * B z) :=
  (c04_aux_frac_int_C1 p hp hp1 g hg M hM y).mul_bdd hB.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hBc z)

/-- The cutoff `χ_Y`. -/
theorem c04_aux_ri_chiY_smooth (Y : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (res_chiY Y) := by
  unfold res_chiY chiAnnulus
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem c04_aux_ri_chiY_zero (Y z : ℝ) (hY : 0 < Y) (hz : z ≤ 3 / 10 * Y ∨ 7 / 2 * Y ≤ z) :
    res_chiY Y z = 0 := by
  unfold res_chiY chiAnnulus
  rcases hz with hz | hz
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 5)]
    have : z / Y ≤ 3 / 10 := by rw [div_le_iff₀ hY]; linarith
    linarith
  · rw [Real.smoothTransition.zero_of_nonpos (x := (7 / 2 - z / Y) / (1 / 2)), mul_zero]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 2)]
    have : 7 / 2 ≤ z / Y := by rw [le_div_iff₀ hY]; linarith
    linarith

/-- A `C¹` function with compact support has bounded derivative. -/
theorem c04_aux_ri_deriv_bdd (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ M, ∀ z, |deriv f z| ≤ M := by
  obtain ⟨M, hM⟩ := (hf.continuous_deriv le_rfl).bounded_above_of_compact_support hc.deriv
  exact ⟨M, fun z => (Real.norm_eq_abs _ ▸ hM z)⟩

/-- Blueprint: lem:c04_residual_integrability. Analytic input to the residual decomposition:
`f_slow` and `f_osc` are differentiable, the fractional derivative kernel of `f_{0,μ}` is
integrable, and all eight integral types in the nine residual pieces converge absolutely.
The thresholds are uniform in `R, ε, μ, Y, y`. -/
theorem c04_residual_integrability (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ Y ≥ 8 * R, ∀ y > R,
        Differentiable ℝ (fam_slow p R ε) ∧ Differentiable ℝ (fam_osc p R ε μ) ∧
        Integrable (fun z => (deriv (c04_linear_seed_mu p μ) y -
          deriv (c04_linear_seed_mu p μ) z) / |y - z| ^ (p + 1)) ∧
        -- Finiteness of every integral appearing in the nine residual pieces.
        (∀ g ∈ ({deriv (fam_slow p R ε), deriv (fam_osc p R ε μ)} : Set (ℝ → ℝ)),
          Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1))) ∧
        (∀ f ∈ ({approximate_solution_family p R ε μ,
            fun z => res_chiY Y z * approximate_solution_family p R ε μ z, corner} : Set (ℝ → ℝ)),
          Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
            (A_eps p ε (c01_secant f y z) - 1))) ∧
        (∀ v ∈ ({res_vY p R ε μ Y,
            fun z => res_chiY Y z * approximate_solution_family p R ε μ z} : Set (ℝ → ℝ)),
          Integrable (fun z => (deriv v y - deriv v z) / |y - z| ^ (p + 1) * c01_secant v y z ^ 2)) ∧
        IntegrableOn (fun z =>
          ((deriv (fun x => approximate_solution_family p R ε μ x - corner x) y -
              deriv (fun x => approximate_solution_family p R ε μ x - corner x) z) *
              (A_eps p ε (z / (y - z)) - 1) +
            deriv (A_eps p ε) (z / (y - z)) *
              c01_secant (fun x => approximate_solution_family p R ε μ x - corner x) y z) /
            (y - z) ^ (p + 1)) (Iio 0) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  obtain ⟨ε₁, hε₁, R₁, hR₁, hfam⟩ := c04_family_regions p hp hp1 δ hδ hδμ
  obtain ⟨Cs, hCs, hslowb⟩ := c04_aux_fslow_bound p hp hp1 1
  refine ⟨ε₁, hε₁, R₁, hR₁, ?_⟩
  intro R hR ε hε μ hμ Y hY y hy
  have hR2 : 2 ≤ R := le_trans hR₁ hR
  have hR0 : 0 < R := by linarith
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith
  have hε01 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans hε₁.2⟩
  obtain ⟨hFsm, hFadm, -, -, hpos, -, -⟩ := (hfam R hR).1 ε hε μ hμ
  obtain ⟨-, -, -, -, -, -, hmu⟩ := approx_linear_seed p hp hp1
  obtain ⟨hf0sm, hf0adm, -⟩ := hmu μ
  set F := approximate_solution_family p R ε μ with hF
  set f0 := c04_linear_seed_mu p μ with hf0
  have hSsm := c04_aux_fam_slow_smooth p R ε hR0
  have hoeq : fam_osc p R ε μ = fun z => F z - f0 z - fam_slow p R ε z := by
    funext z; simp only [hF, hf0, approximate_solution_family]; ring
  have hOsm : ContDiff ℝ (⊤ : ℕ∞) (fam_osc p R ε μ) := by rw [hoeq]; exact (hFsm.sub hf0sm).sub hSsm
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hC1d : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ 1 (deriv g) := fun g hg =>
    (contDiff_infty_iff_deriv.mp hg).2.of_le h1
  obtain ⟨MF, hMF⟩ := hFadm.2.1
  obtain ⟨M0, hM0⟩ := hf0adm.2.1
  have hSb : ∀ z, |deriv (fam_slow p R ε) z| ≤ Cs := by
    intro z
    have := hslowb R hR2 ε hε01 z
    rw [iteratedDeriv_one] at this
    refine this.trans ?_
    have hj : jb z ^ (-p - ((1 : ℕ) : ℝ)) ≤ 1 :=
      rpow_le_one_of_one_le_of_nonpos (c04_aux_one_le_jb z) (by push_cast; linarith)
    have : Cs * ε ≤ Cs := by nlinarith [hε01.2, hε01.1]
    calc Cs * ε * jb z ^ (-p - ((1 : ℕ) : ℝ)) ≤ Cs * ε * 1 :=
          mul_le_mul_of_nonneg_left hj (by nlinarith [hε01.1])
      _ ≤ Cs := by linarith
  have hOb : ∀ z, |deriv (fam_osc p R ε μ) z| ≤ MF + M0 + Cs := by
    intro z
    have e : deriv (fam_osc p R ε μ) z = deriv F z - deriv f0 z - deriv (fam_slow p R ε) z := by
      rw [hoeq]
      exact (((hFsm.differentiable (by simp) z).hasDerivAt.sub
        (hf0sm.differentiable (by simp) z).hasDerivAt).sub
        (hSsm.differentiable (by simp) z).hasDerivAt).deriv
    rw [e]
    have := hMF z; have := hM0 z; have := hSb z
    calc _ ≤ |deriv F z - deriv f0 z| + |deriv (fam_slow p R ε) z| := abs_sub _ _
      _ ≤ |deriv F z| + |deriv f0 z| + |deriv (fam_slow p R ε) z| := by
          linarith [abs_sub (deriv F z) (deriv f0 z)]
      _ ≤ _ := by linarith
  -- the localized family `χ_Y F`
  set G : ℝ → ℝ := fun z => res_chiY Y z * F z with hG
  have hGsm : ContDiff ℝ (⊤ : ℕ∞) G := (c04_aux_ri_chiY_smooth Y).mul hFsm
  have hGcs : HasCompactSupport G := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := 7 / 2 * Y)) ?_
    intro z hz
    by_contra h
    apply hz
    show res_chiY Y z * F z = 0
    rw [c04_aux_ri_chiY_zero Y z hY0 (by
      rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · left; nlinarith
      · right; linarith), zero_mul]
  obtain ⟨MG, hMG⟩ := c04_aux_ri_deriv_bdd G (hGsm.of_le h1) hGcs
  -- the front `v_Y = χ_Y (F - f_low - c₊ z^{-p})`
  set H : ℝ → ℝ := fun z => F z - c04_linear_seed_low p z - c_plus p ε * z ^ (-p) with hH
  have hveq : res_vY p R ε μ Y = fun z => res_chiY Y z * H z := by
    funext z
    unfold res_vY
    by_cases hc : res_chiY Y z = 0
    · split_ifs <;> simp [hc]
    · have hz : 3 / 10 * Y < z := by
        by_contra h
        exact hc (c04_aux_ri_chiY_zero Y z hY0 (Or.inl (not_lt.mp h)))
      have hz2 : z ≥ 2 * R := by linarith
      rw [if_pos (by linarith)]
      have := hpos z hz2
      simp only [hH]
      rw [this]; ring
  have hlowsm : ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_low p) :=
    (c04_seed_low_derivatives p hp hp1).1
  have hvsm : ContDiff ℝ (⊤ : ℕ∞) (res_vY p R ε μ Y) := by
    rw [hveq, contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x (3 / 10 * Y) with hx | hx
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hx] with t ht
      rw [c04_aux_ri_chiY_zero Y t hY0 (Or.inl (le_of_lt ht)), zero_mul]
    · have hx0 : 0 < x := by linarith
      exact (c04_aux_ri_chiY_smooth Y).contDiffAt.mul
        (((hFsm.contDiffAt).sub hlowsm.contDiffAt).sub
          (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hx0.ne')))
  have hvcs : HasCompactSupport (res_vY p R ε μ Y) := by
    rw [hveq]
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := 0) (b := 7 / 2 * Y)) ?_
    intro z hz
    by_contra h
    apply hz
    show res_chiY Y z * H z = 0
    rw [c04_aux_ri_chiY_zero Y z hY0 (by
      rw [mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · left; nlinarith
      · right; linarith), zero_mul]
  obtain ⟨Mv, hMv⟩ := c04_aux_ri_deriv_bdd _ (hvsm.of_le h1) hvcs
  -- measurability of the nonlinear factors
  have hAc := c04_aux_A_cont p ε hε.1
  have hAb : ∀ u, |A_eps p ε u - 1| ≤ 1 := fun u => by
    obtain ⟨h0, h1'⟩ := c04_aux_ri_A_mem p ε u hp0 hε.1
    rw [abs_le]; constructor <;> linarith
  refine ⟨hSsm.differentiable (by simp), hOsm.differentiable (by simp),
    c04_aux_frac_int_C1 p hp0 hp1 _ (hC1d f0 hf0sm) M0 hM0 y, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases hg with rfl | hg
    · exact c04_aux_frac_int_C1 p hp0 hp1 _ (hC1d _ hSsm) Cs hSb y
    · rw [mem_singleton_iff] at hg; subst hg
      exact c04_aux_frac_int_C1 p hp0 hp1 _ (hC1d _ hOsm) _ hOb y
  · intro f hf
    rcases hf with rfl | hf
    · exact c04_aux_ri_kernel_mul p hp0 hp1 _ (hC1d _ hFsm) MF hMF y _
        ((hAc.measurable.comp (c04_aux_ri_secant_meas _ hFsm.continuous y)).sub_const 1) 1
        (fun z => hAb _)
    rcases hf with rfl | hf
    · exact c04_aux_ri_kernel_mul p hp0 hp1 _ (hC1d _ hGsm) MG hMG y _
        ((hAc.measurable.comp (c04_aux_ri_secant_meas _ hGsm.continuous y)).sub_const 1) 1 (fun z => hAb _)
    · rw [mem_singleton_iff] at hf; subst hf
      exact (c04_QW p hp hp1 ε hε.1 y hy0).1
  · intro v hv
    have key : ∀ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v → ∀ M, (∀ z, |deriv v z| ≤ M) →
        Integrable (fun z => (deriv v y - deriv v z) / |y - z| ^ (p + 1) * c01_secant v y z ^ 2) := by
      intro v hv M hM
      have hlip := c04_aux_ri_lip v (hv.differentiable (by simp)) M hM
      exact c04_aux_ri_kernel_mul p hp0 hp1 _ (hC1d _ hv) M hM y _
        ((c04_aux_ri_secant_meas _ hv.continuous y).pow_const 2) ((Real.toNNReal M : ℝ) ^ 2)
        (fun z => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (c04_aux_ri_secant_bound v _ hlip y z) 2)
    rcases hv with rfl | hv
    · exact key _ hvsm Mv hMv
    · rw [mem_singleton_iff] at hv; subst hv
      exact key _ hGsm MG hMG
  · -- the kernel on the negative axis
    set h : ℝ → ℝ := fun x => F x - corner x with hh
    have hFlip := c04_aux_ri_lip F (hFsm.differentiable (by simp)) MF hMF
    have hWlip : LipschitzWith 1 corner := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      simp only [Real.dist_eq, NNReal.coe_one, one_mul, corner]
      exact (abs_max_sub_max_le_abs (-a) (-b) 0).trans (by rw [← abs_neg]; ring_nf; exact le_rfl)
    have hhlip : LipschitzWith (Real.toNNReal MF + 1) h := hFlip.sub hWlip
    set L : ℝ := ((Real.toNNReal MF + 1 : ℝ≥0) : ℝ) with hL
    have hL0 : 0 ≤ L := NNReal.coe_nonneg _
    have hdh : ∀ z, |deriv h z| ≤ L := fun z => Real.norm_eq_abs _ ▸ norm_deriv_le_of_lipschitz hhlip
    have hSh : ∀ z, |c01_secant h y z| ≤ L := c04_aux_ri_secant_bound h _ hhlip y
    have hhc : Continuous h := hFsm.continuous.sub (by unfold corner; fun_prop)
    have hq : Measurable (fun z : ℝ => z / (y - z)) := measurable_id.div (measurable_const.sub measurable_id)
    have hmeas : Measurable (fun z =>
        ((deriv h y - deriv h z) * (A_eps p ε (z / (y - z)) - 1) +
          deriv (A_eps p ε) (z / (y - z)) * c01_secant h y z) / (y - z) ^ (p + 1)) :=
      (((measurable_const.sub (measurable_deriv h)).mul ((hAc.measurable.comp hq).sub_const 1)).add
        (((measurable_deriv (A_eps p ε)).comp hq).mul (c04_aux_ri_secant_meas h hhc y))).div
        ((measurable_const.sub measurable_id).pow_const _)
    set C : ℝ := 2 * L + (p + 1) * L with hC
    have hmaj : IntegrableOn (fun z : ℝ => C * (y - z) ^ (-(p + 1))) (Iio 0) := by
      have h0 := (integrableOn_add_rpow_Ioi_of_lt (a := -(p + 1)) (m := y) (c := 0) (by linarith)
        (by linarith)).comp_neg_Iio (c := 0)
      have h0' : IntegrableOn (fun z : ℝ => (y - z) ^ (-(p + 1))) (Iio 0) :=
        h0.congr_fun (fun z _ => by simp only; ring_nf) measurableSet_Iio
      exact h0'.const_mul C
    refine hmaj.mono' hmeas.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Iio fun z hz => ?_)
    have hz0 : z < 0 := hz
    have hyz : 0 < y - z := by linarith
    have hpow : 0 < (y - z) ^ (p + 1) := rpow_pos_of_pos hyz _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_eq_mul_inv, ← rpow_neg hyz.le]
    refine mul_le_mul_of_nonneg_right ?_ (rpow_pos_of_pos hyz _).le
    have hA' := c04_aux_ri_A_deriv_bound p ε (z / (y - z)) hp0 hε.1 (hε.2.trans hε₁.2)
    calc |(deriv h y - deriv h z) * (A_eps p ε (z / (y - z)) - 1) +
          deriv (A_eps p ε) (z / (y - z)) * c01_secant h y z|
        ≤ |deriv h y - deriv h z| * |A_eps p ε (z / (y - z)) - 1| +
            |deriv (A_eps p ε) (z / (y - z))| * |c01_secant h y z| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (2 * L) * 1 + (p + 1) * L := by
          refine add_le_add (mul_le_mul ?_ (hAb _) (abs_nonneg _) (by linarith))
            (mul_le_mul hA' (hSh z) (abs_nonneg _) (by linarith))
          calc |deriv h y - deriv h z| ≤ |deriv h y| + |deriv h z| := abs_sub _ _
            _ ≤ 2 * L := by linarith [hdh y, hdh z]
      _ = C := by rw [hC]; ring

/-- Blueprint: lem:c04_residual_sum_algebra. The nine definitions cancel algebraically. -/
theorem c04_residual_sum_algebra (p R ε : ℝ) (μ : ℂ) (Y y : ℝ) :
    L0 p (fam_slow p R ε) y + L0 p (fam_osc p R ε μ) y +
      c01_Q_eps p ε (approximate_solution_family p R ε μ) y =
        residual_decomposition p R ε μ Y y := by
  simp only [residual_decomposition, residual_decomposition_E1, residual_decomposition_E2,
    residual_decomposition_E3, residual_decomposition_E4, residual_decomposition_E5,
    residual_decomposition_E6, residual_decomposition_E7, residual_decomposition_E8,
    residual_decomposition_E9, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Blueprint: lem:c04_residual_linear_identity. Linear reduction with explicit integrability. -/
theorem c04_residual_linear_identity (p R ε : ℝ) (μ : ℂ) (y : ℝ)
    (hseed : Differentiable ℝ (c04_linear_seed_mu p μ))
    (hslow : Differentiable ℝ (fam_slow p R ε))
    (hosc : Differentiable ℝ (fam_osc p R ε μ))
    (hseedI : Integrable (fun z =>
      (deriv (c04_linear_seed_mu p μ) y - deriv (c04_linear_seed_mu p μ) z) / |y - z| ^ (p + 1)))
    (hslowI : Integrable (fun z =>
      (deriv (fam_slow p R ε) y - deriv (fam_slow p R ε) z) / |y - z| ^ (p + 1)))
    (hoscI : Integrable (fun z =>
      (deriv (fam_osc p R ε μ) y - deriv (fam_osc p R ε μ) z) / |y - z| ^ (p + 1)))
    (hseedL : L0 p (c04_linear_seed_mu p μ) y = G_mu p μ y) :
    c01_quasilinear_residual p ε (approximate_solution_family p R ε μ) y - G_mu p μ y =
      L0 p (fam_slow p R ε) y + L0 p (fam_osc p R ε μ) y +
        c01_Q_eps p ε (approximate_solution_family p R ε μ) y := by
  have hderiv : deriv (approximate_solution_family p R ε μ) = fun x =>
      deriv (c04_linear_seed_mu p μ) x + deriv (fam_slow p R ε) x + deriv (fam_osc p R ε μ) x := by
    funext x
    exact (((hseed x).hasDerivAt.add (hslow x).hasDerivAt).add (hosc x).hasDerivAt).deriv
  have hfrac : fracDdy p (approximate_solution_family p R ε μ) y =
      fracDdy p (c04_linear_seed_mu p μ) y + fracDdy p (fam_slow p R ε) y +
        fracDdy p (fam_osc p R ε μ) y := by
    unfold fracDdy fracD
    rw [hderiv]
    have hsum : (fun z =>
        (deriv (c04_linear_seed_mu p μ) y + deriv (fam_slow p R ε) y + deriv (fam_osc p R ε μ) y -
          (deriv (c04_linear_seed_mu p μ) z + deriv (fam_slow p R ε) z + deriv (fam_osc p R ε μ) z)) /
            |y - z| ^ (p + 1)) = fun z =>
        ((deriv (c04_linear_seed_mu p μ) y - deriv (c04_linear_seed_mu p μ) z) / |y - z| ^ (p + 1) +
          (deriv (fam_slow p R ε) y - deriv (fam_slow p R ε) z) / |y - z| ^ (p + 1)) +
          (deriv (fam_osc p R ε μ) y - deriv (fam_osc p R ε μ) z) / |y - z| ^ (p + 1) := by
      funext z
      ring
    have hi := integral_add (hseedI.add hslowI) hoscI
    simp only [Pi.add_apply] at hi
    rw [hsum, hi, integral_add hseedI hslowI]
    ring
  unfold c01_quasilinear_residual L0
  rw [hfrac, hderiv, ← hseedL]
  unfold L0
  change _ + (c04_linear_seed_mu p μ y + fam_slow p R ε y + fam_osc p R ε μ y) - _ + _ - _ = _
  ring

/-- Blueprint: lem:c04_residual_identity.  For `Y ≥ 8R`, `y > R`, all terms of the residual
decomposition are finite (absolutely convergent integrals) and
`ℰ̃_ε(f) - G_μ = ℒ₀ f_slow + ℒ₀ f_osc + 𝒬_ε(f) = ℰ₁ + ⋯ + ℰ₉^Y`. -/
-- Encoding: "all terms are finite" is rendered as absolute convergence of the integrals
-- defining `|D|^p f_slow'`, `|D|^p f_osc'`, `𝒬_ε(f)`, `𝒬_ε(χ_Y f)`, `𝒬_ε(W)`, `𝒬_{ε,3}(v_Y)`,
-- `𝒬_{ε,3}(χ_Y f)` and `D𝒬_ε(W)[f - W]` at `y` (every Lean real is finite).
theorem c04_residual_identity (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ Y ≥ 8 * R, ∀ y > R,
        -- finiteness
        (∀ g ∈ ({deriv (fam_slow p R ε), deriv (fam_osc p R ε μ)} : Set (ℝ → ℝ)),
          Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1))) ∧
        (∀ f ∈ ({approximate_solution_family p R ε μ,
            fun z => res_chiY Y z * approximate_solution_family p R ε μ z, corner} : Set (ℝ → ℝ)),
          Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
            (A_eps p ε (c01_secant f y z) - 1))) ∧
        (∀ v ∈ ({res_vY p R ε μ Y,
            fun z => res_chiY Y z * approximate_solution_family p R ε μ z} : Set (ℝ → ℝ)),
          Integrable (fun z => (deriv v y - deriv v z) / |y - z| ^ (p + 1) * c01_secant v y z ^ 2)) ∧
        IntegrableOn (fun z =>
          ((deriv (fun x => approximate_solution_family p R ε μ x - corner x) y -
              deriv (fun x => approximate_solution_family p R ε μ x - corner x) z) *
              (A_eps p ε (z / (y - z)) - 1) +
            deriv (A_eps p ε) (z / (y - z)) *
              c01_secant (fun x => approximate_solution_family p R ε μ x - corner x) y z) /
            (y - z) ^ (p + 1)) (Iio 0) ∧
        -- the identity
        c01_quasilinear_residual p ε (approximate_solution_family p R ε μ) y - G_mu p μ y =
          L0 p (fam_slow p R ε) y + L0 p (fam_osc p R ε μ) y +
            c01_Q_eps p ε (approximate_solution_family p R ε μ) y ∧
        L0 p (fam_slow p R ε) y + L0 p (fam_osc p R ε μ) y +
            c01_Q_eps p ε (approximate_solution_family p R ε μ) y =
          residual_decomposition p R ε μ Y y := by
  intro δ hδ hδμ
  obtain ⟨ε₀, hε₀, R₀, hR₀, hconv⟩ := c04_residual_integrability p hp hp1 δ hδ hδμ
  obtain ⟨-, -, -, -, -, -, hseed⟩ := approx_linear_seed p hp hp1
  refine ⟨ε₀, hε₀, R₀, hR₀, fun R hR ε hε μ hμ Y hY y hy => ?_⟩
  obtain ⟨hslow, hosc, hseedI, hfracI, hQI, hcubI, hDQI⟩ := hconv R hR ε hε μ hμ Y hY y hy
  obtain ⟨hseedSmooth, -, hseedL⟩ := hseed μ
  refine ⟨hfracI, hQI, hcubI, hDQI, ?_, c04_residual_sum_algebra p R ε μ Y y⟩
  exact c04_residual_linear_identity p R ε μ y (hseedSmooth.differentiable (by simp)) hslow hosc
    hseedI (hfracI _ (by simp)) (hfracI _ (by simp)) (hseedL y)


end GSQG
