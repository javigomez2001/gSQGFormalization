import GSQG.SchauderEstimate.Kernels

/-!
# Beyond the paper (Schauder estimate cited in §4): dyadic increment sum, low-block bound,
uniform reconstruction (blueprint ch. 12). Helpers `c12i_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology FourierTransform

noncomputable section

namespace GSQG

theorem c12i_aux_geom_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K n : ℕ) :
    ∑ j ∈ Finset.range n, (if K ≤ j then q ^ j else 0) ≤ q ^ K / (1 - q) := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun j => K ≤ j) = Finset.Ico K n := by
    ext j; simp; omega
  rw [hf, Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 K)
  exact sum_le_hasSum _ (fun i _ => pow_nonneg hq0 i) (hasSum_geometric_of_lt_one hq0 hq1)

theorem c12i_aux_geom_head {r : ℝ} (hr : 1 < r) (K n : ℕ) :
    ∑ j ∈ Finset.range n, (if j < K then r ^ j else 0) ≤ r ^ K / (r - 1) := by
  rw [← Finset.sum_filter]
  have hsub : (Finset.range n).filter (fun j => j < K) ⊆ Finset.range K := by
    intro j; simp
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => pow_nonneg (by linarith) i)).trans ?_
  rw [geom_sum_eq hr.ne']
  have : 0 < r - 1 := by linarith
  gcongr
  linarith

theorem c12i_aux_rpow_pow (c : ℝ) (j : ℕ) : (2:ℝ) ^ (c * (j:ℝ)) = ((2:ℝ) ^ c) ^ j := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- Blueprint: lem:c12_dyadic_increment_sum.  For `0 < θ < 1`,
`∑_{j<n} min(2^{-θj}, d 2^{(1-θ)j}) ≤ C_θ d^θ` uniformly in `d ≥ 0` and `n`; and for `a > 0`,
`∑_{j≥0} 2^{-aj} = (1-2^{-a})⁻¹`. -/
theorem c12_dyadic_increment_sum :
    (∀ θ : ℝ, 0 < θ → θ < 1 → ∃ C : ℝ, 0 < C ∧ ∀ d : ℝ, 0 ≤ d → ∀ n : ℕ,
      ∑ j ∈ Finset.range n, min ((2 : ℝ) ^ (-θ * (j : ℝ))) (d * (2 : ℝ) ^ ((1 - θ) * (j : ℝ))) ≤
        C * d ^ θ) ∧
    (∀ a : ℝ, 0 < a → HasSum (fun j : ℕ => (2 : ℝ) ^ (-a * (j : ℝ))) (1 - (2 : ℝ) ^ (-a))⁻¹) := by
  refine ⟨fun θ hθ hθ1 => ?_, fun a ha => ?_⟩
  · set q : ℝ := (2:ℝ) ^ (-θ) with hq
    set r : ℝ := (2:ℝ) ^ (1 - θ) with hr
    have hq0 : 0 < q := by positivity
    have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
    have hr2 : r ≤ 2 := by
      calc r ≤ (2:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := by norm_num
    have hr1' : 0 < r - 1 := by linarith
    have hq1' : 0 < 1 - q := by linarith
    refine ⟨2 / (r - 1) + 1 / (1 - q), by positivity, fun d hd n => ?_⟩
    simp_rw [c12i_aux_rpow_pow]
    rw [← hq, ← hr]
    rcases hd.eq_or_lt with h0 | hd0
    · subst h0
      rw [Real.zero_rpow hθ.ne', mul_zero]
      refine Finset.sum_nonpos fun j _ => ?_
      simp only [zero_mul]
      exact min_le_right _ _
    rcases le_or_gt 1 d with hd1 | hd1
    · -- decreasing geometric series
      have h1 : 1 ≤ d ^ θ := Real.one_le_rpow hd1 hθ.le
      calc ∑ j ∈ Finset.range n, min (q ^ j) (d * r ^ j) ≤ ∑ j ∈ Finset.range n, q ^ j :=
            Finset.sum_le_sum fun j _ => min_le_left _ _
        _ ≤ (1 - q)⁻¹ := sum_le_hasSum _ (fun i _ => pow_nonneg hq0.le i)
            (hasSum_geometric_of_lt_one hq0.le hq1)
        _ = 1 / (1 - q) := by rw [one_div]
        _ ≤ 2 / (r - 1) + 1 / (1 - q) := le_add_of_nonneg_left (by positivity)
        _ ≤ (2 / (r - 1) + 1 / (1 - q)) * d ^ θ := le_mul_of_one_le_right (by positivity) h1
    · set J : ℕ := ⌊Real.logb 2 (1 / d)⌋₊ with hJ
      have hlog0 : 0 ≤ Real.logb 2 (1 / d) :=
        Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hd0]; linarith)
      have hJle : (2:ℝ) ^ (J:ℝ) ≤ 1 / d := by
        calc (2:ℝ) ^ (J:ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (1 / d)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hlog0)
          _ = 1 / d := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
      have hJlt : 1 / d < (2:ℝ) ^ ((J + 1 : ℕ) : ℝ) := by
        calc 1 / d = (2:ℝ) ^ (Real.logb 2 (1 / d)) :=
              (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
          _ < (2:ℝ) ^ ((J + 1 : ℕ) : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
              push_cast; exact Nat.lt_floor_add_one _
      set K := J + 1 with hK
      -- head: d r^K ≤ 2 d^θ
      have hhead : d * r ^ K ≤ 2 * d ^ θ := by
        have e : r ^ K = r * ((2:ℝ) ^ (J:ℝ)) ^ (1 - θ) := by
          rw [hK, pow_succ, mul_comm, hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num), mul_comm, mul_comm (J : ℝ), mul_comm]
        rw [e]
        have h2 : ((2:ℝ) ^ (J:ℝ)) ^ (1 - θ) ≤ (1 / d) ^ (1 - θ) :=
          Real.rpow_le_rpow (by positivity) hJle (by linarith)
        have h3 : d * (1 / d) ^ (1 - θ) = d ^ θ := by
          rw [one_div, Real.inv_rpow hd0.le, ← Real.rpow_neg hd0.le]
          conv_lhs => arg 1; rw [← Real.rpow_one d]
          rw [← Real.rpow_add hd0]; congr 1; ring
        calc d * (r * ((2:ℝ) ^ (J:ℝ)) ^ (1 - θ)) = r * (d * ((2:ℝ) ^ (J:ℝ)) ^ (1 - θ)) := by ring
          _ ≤ r * (d * (1 / d) ^ (1 - θ)) := by gcongr
          _ = r * d ^ θ := by rw [h3]
          _ ≤ 2 * d ^ θ := by gcongr
      have htail : q ^ K ≤ d ^ θ := by
        have e : q ^ K = ((2:ℝ) ^ ((K : ℕ) : ℝ)) ^ (-θ) := by
          rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num), mul_comm]
        rw [e]
        calc ((2:ℝ) ^ ((K : ℕ) : ℝ)) ^ (-θ) ≤ (1 / d) ^ (-θ) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hJlt.le (by linarith)
          _ = d ^ θ := by rw [one_div, Real.inv_rpow hd0.le, Real.rpow_neg hd0.le, inv_inv]
      have hterm : ∀ j : ℕ, min (q ^ j) (d * r ^ j) ≤
          d * (if j < K then r ^ j else 0) + (if K ≤ j then q ^ j else 0) := by
        intro j
        by_cases hj : j < K
        · simp [hj, show ¬ K ≤ j by omega]
        · simp [hj, show K ≤ j by omega]
      calc ∑ j ∈ Finset.range n, min (q ^ j) (d * r ^ j)
          ≤ ∑ j ∈ Finset.range n, (d * (if j < K then r ^ j else 0) + (if K ≤ j then q ^ j else 0)) :=
            Finset.sum_le_sum fun j _ => hterm j
        _ = d * ∑ j ∈ Finset.range n, (if j < K then r ^ j else 0) +
              ∑ j ∈ Finset.range n, (if K ≤ j then q ^ j else 0) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ d * (r ^ K / (r - 1)) + q ^ K / (1 - q) := by
            gcongr
            · exact c12i_aux_geom_head hr1 K n
            · exact c12i_aux_geom_tail hq0.le hq1 K n
        _ = (d * r ^ K) / (r - 1) + q ^ K / (1 - q) := by ring
        _ ≤ (2 * d ^ θ) / (r - 1) + d ^ θ / (1 - q) := by gcongr
        _ = (2 / (r - 1) + 1 / (1 - q)) * d ^ θ := by ring
  · simp_rw [c12i_aux_rpow_pow]
    exact hasSum_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

/-- `Re` commutes with iterated derivatives of a smooth complex-valued function. -/
theorem c12i_aux_iteratedDeriv_re {F : ℝ → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : ℕ) :
    iteratedDeriv m (fun x => (F x).re) = fun x => (iteratedDeriv m F x).re := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    have hd : DifferentiableAt ℝ (iteratedDeriv m F) x :=
      (hF.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)) x
    have := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt)
    exact this.deriv

theorem c12i_aux_iteratedDeriv_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv m f) := by
  rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv m hf

theorem c12i_aux_iteratedDeriv_hcs {f : ℝ → ℂ} (hcs : HasCompactSupport f) (m : ℕ) :
    HasCompactSupport (iteratedDeriv m f) := by
  rw [iteratedDeriv_eq_iterate]
  induction m with
  | zero => simpa using hcs
  | succ m ih => rw [Function.iterate_succ_apply']; exact ih.deriv

/-- For smooth compactly supported `f`: `f̂` is integrable and continuous, and `(f̂)^∨ = f`. -/
theorem c12i_aux_ft_inv {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    Integrable (fourierT f) ∧ Continuous (fourierT f) ∧ ∀ y, invFourierT (fourierT f) y = f y := by
  set g := hcs.toSchwartzMap hf
  have hg : (g : ℝ → ℂ) = f := funext (hcs.toSchwartzMap_toFun hf)
  obtain ⟨h1, h2⟩ := Lib.schwartz_fourier_inversion g
  rw [hg] at h1 h2
  refine ⟨h1, ?_, fun y => (h2 y)⟩
  have e : fourierT f = fun ξ => 𝓕 (⇑g) (ξ / (2 * π)) := by
    funext ξ; rw [hg]; exact Lib.integral_mul_exp_neg_I_eq_fourier _ ξ
  rw [e, ← SchwartzMap.fourier_coe]
  exact (𝓕 g).continuous.comp (continuous_id.div_const _)

theorem c12i_aux_ft_iter {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f)
    (m : ℕ) (ξ : ℝ) :
    fourierT (iteratedDeriv m f) ξ = (Complex.I * ξ) ^ m * fourierT f ξ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := c12i_aux_iteratedDeriv_smooth hf m
    have hc := c12i_aux_iteratedDeriv_hcs hcs m
    rw [iteratedDeriv_succ]
    have hd : Differentiable ℝ (iteratedDeriv m f) := hs.differentiable (by simp)
    have hcd : Continuous (deriv (iteratedDeriv m f)) := hs.continuous_deriv (by simp)
    have := Lib.integral_deriv_mul_exp_neg_I (hs.continuous.integrable_of_hasCompactSupport hc) hd
      (hcd.integrable_of_hasCompactSupport hc.deriv) ξ
    change (∫ x, _ * _) = _
    rw [this]
    change Complex.I * ξ * fourierT (iteratedDeriv m f) ξ = _
    rw [ih]; ring


theorem c12i_aux_rho_smooth : ContDiff ℝ (⊤ : ℕ∞) rho := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    have : ∀ᶠ ξ in 𝓝 (0 : ℝ), |ξ| < 1 := by
      have := (continuous_abs.tendsto (0 : ℝ)); rw [abs_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [this] with ξ hξ
    unfold rho
    exact Real.smoothTransition.one_of_one_le (by linarith)
  · unfold rho
    exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.sub (contDiffAt_abs hx))

theorem c12i_aux_rho_props : HasCompactSupport rho ∧ (∀ t : ℝ, |t| ≤ 1 → rho t = 1) ∧
    (∀ t : ℝ, 2 < |t| → rho t = 0) ∧ (∀ t, 0 ≤ rho t ∧ rho t ≤ 1) := by
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_, fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  · refine HasCompactSupport.intro (K := Icc (-2) 2) isCompact_Icc fun x hx => ?_
    unfold rho
    apply Real.smoothTransition.zero_of_nonpos
    have : 2 < |x| := by
      by_contra h; exact hx (abs_le.mp (not_lt.mp h))
    linarith
  · unfold rho; exact Real.smoothTransition.one_of_one_le (by linarith)
  · unfold rho; exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `ρ(·/2^n)` (as a complex function) is continuous with compact support. -/
theorem c12i_aux_rho_scaled (n : ℕ) :
    Continuous (fun ξ : ℝ => ((rho (ξ / (2 : ℝ) ^ n) : ℝ) : ℂ)) ∧
    HasCompactSupport (fun ξ : ℝ => ((rho (ξ / (2 : ℝ) ^ n) : ℝ) : ℂ)) := by
  obtain ⟨-, -, h0, -⟩ := c12i_aux_rho_props
  refine ⟨Complex.continuous_ofReal.comp
    (c12i_aux_rho_smooth.continuous.comp (continuous_id.div_const _)), ?_⟩
  refine HasCompactSupport.intro (K := Icc (-(2 * 2 ^ n)) (2 * 2 ^ n)) isCompact_Icc fun x hx => ?_
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have : 2 < |x / 2 ^ n| := by
    rw [abs_div, abs_of_pos h2n, lt_div_iff₀ h2n]
    by_contra h; exact hx (abs_le.mp (not_lt.mp h))
  simp [h0 _ this]

theorem c12i_aux_norm_exp (t : ℝ) : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem c12i_aux_integrable_mul_exp {a : ℝ → ℂ} (ha : Integrable a) (x : ℝ) :
    Integrable (fun ξ : ℝ => a ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) := by
  refine ha.norm.mono' (ha.aestronglyMeasurable.mul (by fun_prop : Continuous fun ξ : ℝ =>
    Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun ξ => ?_
  rw [norm_mul, mul_assoc, ← Complex.ofReal_mul, c12i_aux_norm_exp, mul_one]

theorem c12i_aux_invF_add {a b : ℝ → ℂ} (ha : Integrable a) (hb : Integrable b) (x : ℝ) :
    invFourierT (fun ξ => a ξ + b ξ) x = invFourierT a x + invFourierT b x := by
  unfold invFourierT
  rw [← mul_add, ← integral_add (c12i_aux_integrable_mul_exp ha x)
    (c12i_aux_integrable_mul_exp hb x)]
  congr 1; refine integral_congr_ae (Eventually.of_forall fun ξ => ?_); simp only; ring

theorem c12i_aux_invF_sub {a b : ℝ → ℂ} (ha : Integrable a) (hb : Integrable b) (x : ℝ) :
    invFourierT (fun ξ => a ξ - b ξ) x = invFourierT a x - invFourierT b x := by
  unfold invFourierT
  rw [← mul_sub, ← integral_sub (c12i_aux_integrable_mul_exp ha x)
    (c12i_aux_integrable_mul_exp hb x)]
  congr 1; refine integral_congr_ae (Eventually.of_forall fun ξ => ?_); simp only; ring

theorem c12i_aux_invF_norm_le (a : ℝ → ℂ) (x : ℝ) :
    ‖invFourierT a x‖ ≤ (2 * π)⁻¹ * ∫ ξ, ‖a ξ‖ := by
  unfold invFourierT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext ξ
  rw [norm_mul, mul_assoc, ← Complex.ofReal_mul, c12i_aux_norm_exp, mul_one]


/-- Fubini: `(b f̂)^∨ = b^∨ * f` for continuous compactly supported `b`, `f`. -/
theorem c12i_aux_invF_conv {b f : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : ℝ) :
    invFourierT (fun ξ => b ξ * fourierT f ξ) x = ∫ y, invFourierT b (x - y) * f y := by
  set F : ℝ → ℝ → ℂ := fun ξ y =>
    b ξ * f y * Complex.exp (Complex.I * ((x - y : ℝ) : ℂ) * (ξ : ℂ)) with hF
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF]; fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro (hbc.isCompact.prod hfc.isCompact) fun p hp => ?_
    simp only [Set.mem_prod, not_and_or] at hp
    simp only [hF, Function.uncurry]
    rcases hp with h | h
    · rw [image_eq_zero_of_notMem_tsupport h]; simp
    · rw [image_eq_zero_of_notMem_tsupport h]; simp
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hFc.integrable_of_hasCompactSupport hFs
  have e1 : invFourierT (fun ξ => b ξ * fourierT f ξ) x =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, ∫ y, F ξ y := by
    unfold invFourierT fourierT
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF]
    rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [show Complex.I * ((x - y : ℝ) : ℂ) * (ξ : ℂ) =
      -(Complex.I * (y : ℂ) * (ξ : ℂ)) + Complex.I * (x : ℂ) * (ξ : ℂ) by push_cast; ring,
      Complex.exp_add]
    ring
  rw [e1, integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hF]
  unfold invFourierT
  rw [mul_assoc, ← integral_mul_const]
  congr 2; funext ξ; ring

/-- The inverse transform of a smooth compactly supported function is integrable. -/
theorem c12i_aux_invF_integrable {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) : Integrable (invFourierT b) := by
  obtain ⟨A, hA, hAb⟩ := c03c_aux_smooth_decay hb hbc
  have hcont : Continuous (invFourierT b) := (c03c_aux_invF_smooth hb.continuous hbc).continuous
  refine (integrable_inv_one_add_sq.const_mul (2 * A)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hy2 : 0 < 1 + y ^ 2 := by positivity
  rcases le_or_gt 1 |y| with hy | hy
  · have hyp : 0 < |y| := by linarith
    refine ((hAb y).2 hy).trans ?_
    have h1 : |y| ^ (-(5:ℝ)) ≤ |y| ^ (-(2:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
    have h2 : |y| ^ (-(2:ℝ)) = (y ^ 2)⁻¹ := by
      rw [Real.rpow_neg hyp.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have h3 : (y ^ 2)⁻¹ ≤ 2 * (1 + y ^ 2)⁻¹ := by
      have : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) hy2]
      linarith
    calc A * |y| ^ (-(5:ℝ)) ≤ A * (2 * (1 + y ^ 2)⁻¹) := by
          gcongr; exact h1.trans (h2 ▸ h3)
      _ = 2 * A * (1 + y ^ 2)⁻¹ := by ring
  · refine (hAb y).1.trans ?_
    have : 1 ≤ 2 * (1 + y ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hy2]
      nlinarith [abs_nonneg y, sq_abs y]
    calc A = A * 1 := (mul_one A).symm
      _ ≤ A * (2 * (1 + y ^ 2)⁻¹) := by gcongr
      _ = 2 * A * (1 + y ^ 2)⁻¹ := by ring


theorem c12i_aux_ofReal_smooth {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (v y : ℂ)) := Complex.ofRealCLM.contDiff.comp hv

/-- Blueprint: lem:c12_low_block_bound.  For every `m` there is `C_m > 0` such that for every real
`v ∈ C_c^∞`, `S₀ v = χ^∨ * v` (with `χ^∨ = Re (ρ)^∨`) is smooth, every differentiated convolution
converges absolutely, and `‖∂^m S₀ v‖∞ ≤ C_m ‖v‖∞` (stated for every bound `M` of `|v|`). -/
theorem c12_low_block_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      ContDiff ℝ (⊤ : ℕ∞) (c12_low_block v) ∧
      (∀ x : ℝ,
        Integrable (fun y => iteratedDeriv m
          (fun z => (invFourierT (fun ξ => (rho ξ : ℂ)) z).re) (x - y) * v y) ∧
        iteratedDeriv m (c12_low_block v) x =
          ∫ y, iteratedDeriv m (fun z => (invFourierT (fun ξ => (rho ξ : ℂ)) z).re) (x - y) * v y) ∧
      ∀ M : ℝ, (∀ y, |v y| ≤ M) → ∀ x, |iteratedDeriv m (c12_low_block v) x| ≤ C * M := by
  set b : ℝ → ℂ := fun ξ => (Complex.I * ξ) ^ m * (rho ξ : ℂ) with hb
  obtain ⟨hρc, -, -, -⟩ := c12i_aux_rho_props
  have hρC : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (rho ξ : ℂ)) :=
    c12i_aux_ofReal_smooth c12i_aux_rho_smooth
  have hρcC : HasCompactSupport (fun ξ : ℝ => (rho ξ : ℂ)) := hρc.comp_left Complex.ofReal_zero
  have hbs : ContDiff ℝ (⊤ : ℕ∞) b := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (Complex.I * ξ) ^ m) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).pow m
    exact this.mul hρC
  have hbc : HasCompactSupport b := hρcC.mul_left
  set Km : ℝ → ℝ := fun z => (invFourierT b z).re with hKmdef
  have hbsm := c03c_aux_invF_smooth hbs.continuous hbc
  have hKm : Integrable Km := (c12i_aux_invF_integrable hbs hbc).re
  have hKmc : Continuous Km := Complex.continuous_re.comp hbsm.continuous
  have hk : iteratedDeriv m (fun z => (invFourierT (fun ξ => (rho ξ : ℂ)) z).re) = Km := by
    rw [c12i_aux_iteratedDeriv_re (c03c_aux_invF_smooth hρC.continuous hρcC) m,
      c03c_aux_invF_iter hρC.continuous hρcC m]
  refine ⟨(∫ z, |Km z|) + 1, by positivity, fun v hv hvc => ?_⟩
  set vc : ℝ → ℂ := fun y => (v y : ℂ) with hvcdef
  have hvcs : ContDiff ℝ (⊤ : ℕ∞) vc := c12i_aux_ofReal_smooth hv
  have hvcc : HasCompactSupport vc := hvc.comp_left Complex.ofReal_zero
  obtain ⟨-, hftc, -⟩ := c12i_aux_ft_inv hvcs hvcc
  set g : ℝ → ℂ := fun ξ => (rho ξ : ℂ) * fourierT vc ξ with hgdef
  have hgc : Continuous g := hρC.continuous.mul hftc
  have hgs : HasCompactSupport g := hρcC.mul_right
  have hS : c12_low_block v = fun x => (invFourierT g x).re := rfl
  have hSs := c03c_aux_invF_smooth hgc hgs
  have hintx : ∀ x, Integrable (fun y => Km (x - y) * v y) := fun x =>
    ((hKmc.comp (continuous_const.sub continuous_id)).mul hv.continuous).integrable_of_hasCompactSupport
      hvc.mul_left
  have hder : ∀ x, iteratedDeriv m (c12_low_block v) x = ∫ y, Km (x - y) * v y := by
    intro x
    rw [hS, c12i_aux_iteratedDeriv_re hSs m, c03c_aux_invF_iter hgc hgs m]
    have e : invFourierT (fun ξ => (Complex.I * ξ) ^ m * g ξ) x =
        invFourierT (fun ξ => b ξ * fourierT vc ξ) x := by
      congr 1; funext ξ; simp only [hgdef, hb]; ring
    have hic : Integrable (fun y => invFourierT b (x - y) * vc y) :=
      ((hbsm.continuous.comp (continuous_const.sub continuous_id)).mul
        hvcs.continuous).integrable_of_hasCompactSupport hvcc.mul_left
    show (invFourierT (fun ξ => (Complex.I * ξ) ^ m * g ξ) x).re = _
    rw [e, c12i_aux_invF_conv hbs.continuous hbc hvcs.continuous hvcc]
    have hre := integral_re hic
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    congr 1; funext y; simp [hvcdef, hKmdef]
  refine ⟨Complex.reCLM.contDiff.comp hSs, fun x => ⟨by rw [hk]; exact hintx x, by rw [hk, hder]⟩,
    fun M hM x => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [hder, ← Real.norm_eq_abs]
  calc ‖∫ y, Km (x - y) * v y‖ ≤ ∫ y, |Km (x - y)| * M :=
        norm_integral_le_of_norm_le ((hKm.comp_sub_left x).abs.mul_const M)
          (Eventually.of_forall fun y => by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _))
    _ = (∫ z, |Km z|) * M := by
        rw [integral_mul_const, integral_sub_left_eq_self (fun z => |Km z|)]
    _ ≤ ((∫ z, |Km z|) + 1) * M := by gcongr; linarith


/-- Blueprint: lem:c12_reconstruction_derivatives.  For real `v ∈ C_c^∞` and
`P_n v = S₀ v + ∑_{j<n} Δ_j v`, every `P_n v` is smooth and `∂^m P_n v → ∂^m v` uniformly on `ℝ`. -/
theorem c12_reconstruction_derivatives (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (m : ℕ) :
    (∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => c12_low_block v x + ∑ j ∈ Finset.range n, c12_block j v x)) ∧
    TendstoUniformly
      (fun (n : ℕ) (x : ℝ) => iteratedDeriv m
        (fun y => c12_low_block v y + ∑ j ∈ Finset.range n, c12_block j v y) x)
      (iteratedDeriv m v) atTop := by
  set vc : ℝ → ℂ := fun y => (v y : ℂ) with hvcdef
  have hvcs : ContDiff ℝ (⊤ : ℕ∞) vc := c12i_aux_ofReal_smooth hv
  have hvcc : HasCompactSupport vc := hvc.comp_left Complex.ofReal_zero
  obtain ⟨-, hftc, -⟩ := c12i_aux_ft_inv hvcs hvcc
  obtain ⟨-, hρ1, -, hρ01⟩ := c12i_aux_rho_props
  set g : ℕ → ℝ → ℂ := fun n ξ => ((rho (ξ / (2 : ℝ) ^ n) : ℝ) : ℂ) * fourierT vc ξ with hgdef
  have hgc : ∀ n, Continuous (g n) := fun n => (c12i_aux_rho_scaled n).1.mul hftc
  have hgs : ∀ n, HasCompactSupport (g n) := fun n => (c12i_aux_rho_scaled n).2.mul_right
  have hgi : ∀ n, Integrable (g n) := fun n => (hgc n).integrable_of_hasCompactSupport (hgs n)
  have hP : ∀ n, (fun x => c12_low_block v x + ∑ j ∈ Finset.range n, c12_block j v x) =
      fun x => (invFourierT (g n) x).re := by
    intro n; funext x
    induction n with
    | zero => simp [c12_low_block, hgdef, hvcdef]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      have key : (fun ξ : ℝ => (c12_annulus (ξ / (2 : ℝ) ^ n) : ℂ) * fourierT vc ξ) =
          fun ξ => g (n + 1) ξ - g n ξ := by
        funext ξ; simp only [hgdef, c12_annulus]; push_cast
        rw [pow_succ, ← div_div]; ring
      have hb : c12_block n v x = (invFourierT (fun ξ => g (n + 1) ξ - g n ξ) x).re := by
        rw [← key]; rfl
      rw [hb, c12i_aux_invF_sub (hgi (n + 1)) (hgi n), ← Complex.add_re]
      congr 1; ring
  have hPs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (invFourierT (g n)) := fun n =>
    c03c_aux_invF_smooth (hgc n) (hgs n)
  refine ⟨fun n => by rw [hP n]; exact Complex.reCLM.contDiff.comp (hPs n), ?_⟩
  have hPd : ∀ n x, iteratedDeriv m
      (fun y => c12_low_block v y + ∑ j ∈ Finset.range n, c12_block j v y) x =
      (invFourierT (fun ξ => (Complex.I * ξ) ^ m * g n ξ) x).re := by
    intro n x
    rw [hP n, c12i_aux_iteratedDeriv_re (hPs n) m, c03c_aux_invF_iter (hgc n) (hgs n) m]
  set H : ℝ → ℂ := fun ξ => (Complex.I * ξ) ^ m * fourierT vc ξ with hHdef
  obtain ⟨hHi, hHv⟩ : Integrable H ∧ ∀ x, iteratedDeriv m v x = (invFourierT H x).re := by
    obtain ⟨h1, -, h3⟩ := c12i_aux_ft_inv (c12i_aux_iteratedDeriv_smooth hvcs m)
      (c12i_aux_iteratedDeriv_hcs hvcc m)
    have e : fourierT (iteratedDeriv m vc) = H := funext (c12i_aux_ft_iter hvcs hvcc m)
    rw [e] at h1 h3
    refine ⟨h1, fun x => ?_⟩
    have ev : v = fun x => (vc x).re := by funext y; simp [hvcdef]
    rw [ev, c12i_aux_iteratedDeriv_re hvcs m]
    simp only
    rw [h3 x]
  have hgmi : ∀ n, Integrable (fun ξ => (Complex.I * ξ) ^ m * g n ξ) := fun n =>
    ((by fun_prop : Continuous fun ξ : ℝ => (Complex.I * ξ) ^ m).mul
      (hgc n)).integrable_of_hasCompactSupport (hgs n).mul_left
  have hdiff : ∀ n x, iteratedDeriv m
      (fun y => c12_low_block v y + ∑ j ∈ Finset.range n, c12_block j v y) x -
      iteratedDeriv m v x =
      (invFourierT (fun ξ => (((rho (ξ / (2 : ℝ) ^ n) : ℝ) : ℂ) - 1) * H ξ) x).re := by
    intro n x
    rw [hPd, hHv, ← Complex.sub_re, ← c12i_aux_invF_sub (hgmi n) hHi]
    congr 2; funext ξ; simp only [hgdef, hHdef]; ring
  set ε : ℕ → ℝ := fun n =>
    (2 * π)⁻¹ * ∫ ξ, ‖(((rho (ξ / (2 : ℝ) ^ n) : ℝ) : ℂ) - 1) * H ξ‖ with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ∫ ξ, ‖(((rho (ξ / (2 : ℝ) ^ n) : ℝ) : ℂ) - 1) * H ξ‖)
        atTop (𝓝 (∫ _ξ : ℝ, (0 : ℝ))) := by
      refine tendsto_integral_of_dominated_convergence (fun ξ => ‖H ξ‖)
        (fun n => (((c12i_aux_rho_scaled n).1.sub continuous_const).aestronglyMeasurable.mul
          hHi.aestronglyMeasurable).norm) hHi.norm (fun n => Eventually.of_forall fun ξ => ?_)
        (Eventually.of_forall fun ξ => ?_)
      · rw [norm_norm, norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_le]
        have := hρ01 (ξ / 2 ^ n)
        constructor <;> linarith
      · have hev : ∀ᶠ n : ℕ in atTop, |ξ| ≤ (2 : ℝ) ^ n :=
          (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop |ξ|
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        have h2n : (0 : ℝ) < 2 ^ n := by positivity
        have : rho (ξ / 2 ^ n) = 1 := hρ1 _ (by
          rw [abs_div, abs_of_pos h2n, div_le_one h2n]; exact hn)
        rw [this]; simp
    have := hlim.const_mul ((2 * π)⁻¹)
    simpa [hεdef] using this
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [hε.eventually (gt_mem_nhds hδ)] with n hn x
  rw [dist_comm, Real.dist_eq, hdiff]
  exact (Complex.abs_re_le_norm _).trans_lt ((c12i_aux_invF_norm_le _ x).trans_lt hn)

end GSQG
