import GSQG.Definitions
import GSQG.Sec3_FixedPoint.FixedPointArgument
import GSQG.Sec4_Analysis.Equation
import GSQG.AppendixAB.Statements
import GSQG.Sec1_Introduction.SelfSimilarReduction

/-!
# §§6.1–6.3: Linear inverse I (blueprint ch. 08) — conjugation, the free inverse `𝒯₀`, the functional `ℓ`,
and the low-frequency estimate

All nodes are proved.  Standing assumptions: `3/4 < p < 1` (def:parameters).

Conventions of this file.
* The constant `ε_c` of the chapter ("let `ε_c > 0` be such that `|c_ε| ≤ c₀` for `0 ≤ ε ≤ ε_c`")
  is not a definition; every statement about `0 ≤ ε ≤ ε_c` starts with `∃ εc > 0`, placed before
  the quantifier over `γ` (the blueprint's `ε_c` depends only on `p, χ₊, C₀`).  Results for the
  same `ε_c` are obtained by taking minima (all statements are monotone in `εc`).
* Likewise the constant `c₀` of lem:c08_phi_bounds is existentially quantified in each statement
  that uses it.
* `(∂_y + ∂_z) K(y,z)` is written `deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0`,
  `∂_y K(y,z)` is `deriv (fun y' => R_eps_kernel p ε y' z) y`.
* `ϑ` (a cutoff in lem:c08_R2_near/far) is universally quantified with its stated properties.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace GSQG

/-! ## Auxiliary lemmas (not blueprint nodes) -/

/-- `|c_α| ≤ 1/π` for `0 < p < 1` (log-convexity of `Γ` gives `Γ(1+p) ≤ 1`). -/
theorem c08_aux_calpha_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : |calpha p| ≤ 1 / π := by
  have hG1 : Real.Gamma (1 + p) ≤ 1 := by
    have h := (Real.convexOn_Gamma).2 (show (1:ℝ) ∈ Ioi 0 by norm_num) (show (2:ℝ) ∈ Ioi 0 by norm_num)
      (show 0 ≤ 1 - p by linarith) hp.le (by ring)
    simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
    convert h using 2 <;> ring
  have hG0 : 0 < Real.Gamma (1 + p) := Real.Gamma_pos_of_pos (by linarith)
  unfold calpha
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hG0]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  calc Real.Gamma (1 + p) * |Real.sin (π * p / 2)| ≤ 1 * 1 :=
        mul_le_mul hG1 (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- `∫₀¹ (1-t)^{p-1} dt = 1/p` (and integrability). -/
theorem c08_aux_int_one_sub_rpow (p : ℝ) (hp : 0 < p) :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (p - 1)) volume 0 1 ∧
    ∫ t in (0:ℝ)..1, (1 - t) ^ (p - 1) = 1 / p := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (p - 1)) volume (1 - 1) (1 - 0) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  refine ⟨?_, ?_⟩
  · have h2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (p - 1)) volume 1 0 := by
      simpa using hi.comp_sub_left 1
    exact h2.symm
  · rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (p - 1)) 1]
    rw [integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow hp.ne']

/-- Bound on `|A_ε(t) - 1|` for `0 ≤ ε`, `t ∈ [0,1]`. -/
theorem c08_aux_A_sub_one (p ε t : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (ht : t ∈ Icc (0:ℝ) 1) :
    |A_eps p ε t - 1| ≤ 1 ∧ |A_eps p ε t - 1| ≤ ε := by
  have hx : 0 ≤ ε * t ^ 2 := mul_nonneg hε (sq_nonneg _)
  have hx1 : ε * t ^ 2 ≤ ε := by
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith
  set s := (p + 1) / 2 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hA : A_eps p ε t = ((1 + ε * t ^ 2) ^ s)⁻¹ := by
    unfold A_eps
    rw [show -(p + 1) / 2 = -s by rw [hs]; ring, Real.rpow_neg (by linarith)]
  have hpos : 0 < (1 + ε * t ^ 2) ^ s := Real.rpow_pos_of_pos (by linarith) _
  have hge : 1 ≤ (1 + ε * t ^ 2) ^ s := Real.one_le_rpow (by linarith) hs0
  have hle : (1 + ε * t ^ 2) ^ s ≤ 1 + s * (ε * t ^ 2) :=
    rpow_one_add_le_one_add_mul_self (by linarith) hs0 hs1
  have hA1 : A_eps p ε t ≤ 1 := by rw [hA]; exact inv_le_one_of_one_le₀ hge
  have hA0 : 0 < A_eps p ε t := by rw [hA]; positivity
  rw [abs_of_nonpos (by linarith)]
  refine ⟨by linarith, ?_⟩
  -- 1 - 1/X ≤ X - 1 ≤ s ε t² ≤ ε
  have : 1 - A_eps p ε t ≤ (1 + ε * t ^ 2) ^ s - 1 := by
    rw [hA]
    have h1 : ((1 + ε * t ^ 2) ^ s)⁻¹ * (1 + ε * t ^ 2) ^ s = 1 := inv_mul_cancel₀ hpos.ne'
    nlinarith
  nlinarith

/-- `|c_ε| ≤ 1/2` and `|c_ε| ≤ ε` for `ε ≥ 0` (explicit form of lem:analysis_coefficient). -/
theorem c08_aux_c_eps_bound (p ε : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hε : 0 ≤ ε) :
    |c_eps p ε| ≤ 1 / 2 ∧ |c_eps p ε| ≤ ε := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hint, hval⟩ := c08_aux_int_one_sub_rpow p hp0
  have key : ∀ K : ℝ, (∀ t ∈ Icc (0:ℝ) 1, |A_eps p ε t - 1| ≤ K) →
      |c_eps p ε| ≤ (1 / π) * (K / p) := by
    intro K hK
    unfold c_eps
    rw [abs_mul]
    apply mul_le_mul (c08_aux_calpha_bound p hp0 hp1) _ (abs_nonneg _) (by positivity)
    have : |∫ t in (0:ℝ)..1, (A_eps p ε t - 1) * (1 - t) ^ (p - 1)| ≤
        ∫ t in (0:ℝ)..1, K * (1 - t) ^ (p - 1) := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · refine Filter.Eventually.of_forall (fun t ht => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (by linarith [ht.2]) _)]
        exact mul_le_mul_of_nonneg_right (hK t ⟨ht.1.le, ht.2⟩)
          (Real.rpow_nonneg (by linarith [ht.2]) _)
      · exact hint.const_mul K
    calc _ ≤ _ := this
      _ = K / p := by rw [intervalIntegral.integral_const_mul, hval]; ring
  have hpi : 3 < π := Real.pi_gt_three
  have hb : (1 / π) * (1 / p) ≤ 1 / 2 := by
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨?_, ?_⟩
  · exact (key 1 (fun t ht => (c08_aux_A_sub_one p ε t hp0 hp1 hε ht).1)).trans hb
  · refine (key ε (fun t ht => (c08_aux_A_sub_one p ε t hp0 hp1 hε ht).2)).trans ?_
    have : (1 / π) * (ε / p) = ε * ((1 / π) * (1 / p)) := by ring
    rw [this]; nlinarith

/-- `1 ≤ ⟨y⟩`. -/
theorem c08_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := by
  unfold jb
  calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])

/-- `0 < ⟨y⟩`. -/
theorem c08_aux_jb_pos (y : ℝ) : 0 < jb y := lt_of_lt_of_le one_pos (c08_aux_one_le_jb y)

/-- `⟨y⟩^{-a} = (1+‖y‖²)^{-a/2}`. -/
theorem c08_aux_jb_rpow_eq (y a : ℝ) : jb y ^ (-a) = (1 + ‖y‖ ^ 2) ^ (-a / 2) := by
  unfold jb
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.norm_eq_abs, sq_abs]
  ring_nf

/-- `⟨z⟩^{-b}` is integrable for `b > 1`. -/
theorem c08_aux_jb_rpow_integrable (b : ℝ) (hb : 1 < b) : Integrable (fun z : ℝ => jb z ^ (-b)) := by
  have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := b) (by simpa using hb)
  simpa [c08_aux_jb_rpow_eq] using this

/-- `|y| ≤ 2|u| → ⟨y⟩ ≤ 2⟨u⟩`. -/
theorem c08_aux_jb_le_two_mul {y u : ℝ} (h : |y| ≤ 2 * |u|) : jb y ≤ 2 * jb u := by
  unfold jb
  rw [show (2:ℝ) * Real.sqrt (1 + u ^ 2) = Real.sqrt (4 * (1 + u ^ 2)) by
    rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  have h1 : y ^ 2 ≤ (2 * |u|) ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have : (2 * |u|) ^ 2 = 4 * u ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  nlinarith

/-- `|y| ≤ 2|u| → ⟨u⟩^{-b} ≤ 2^b ⟨y⟩^{-b}` for `b ≥ 0`. -/
theorem c08_aux_jb_rpow_neg_le {y u b : ℝ} (hb : 0 ≤ b) (h : |y| ≤ 2 * |u|) :
    jb u ^ (-b) ≤ 2 ^ b * jb y ^ (-b) := by
  have h1 : jb y / 2 ≤ jb u := by linarith [c08_aux_jb_le_two_mul h]
  have h2 : jb u ^ (-b) ≤ (jb y / 2) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [c08_aux_jb_pos y]) h1 (by linarith)
  calc _ ≤ _ := h2
    _ = 2 ^ b * jb y ^ (-b) := by
      rw [Real.div_rpow (c08_aux_jb_pos y).le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp


/-- The project Fourier transform in terms of Mathlib's: `f̂(x) = 𝓕 f (x/2π)`. -/
theorem c08_aux_fourierT_eq (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    fourierT (⇑φ) x = 𝓕 (⇑φ) (x / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold fourierT
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [smul_eq_mul, mul_comm]
  have : (2 * π : ℝ) ≠ 0 := by positivity
  have e : -(Complex.I * (v : ℂ) * (x : ℂ)) = ((-2 * π * v * (x / (2 * π)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [e]

/-- `φ̂` is continuous for Schwartz `φ`. -/
theorem c08_aux_fourierT_continuous (φ : SchwartzMap ℝ ℂ) : Continuous (fourierT (⇑φ)) := by
  have : fourierT (⇑φ) = fun x => (𝓕 φ) (x / (2 * π)) := by
    ext x; rw [c08_aux_fourierT_eq, SchwartzMap.fourier_coe]
  rw [this]; fun_prop

/-- Injectivity of the distributional Fourier transform on continuous functions. -/
theorem c08_aux_distFourier_zero (u : ℝ → ℂ) (hu : Continuous u)
    (h : ∀ φ : SchwartzMap ℝ ℂ, ∫ x, u x * fourierT (⇑φ) x = 0) : u = 0 := by
  set v : ℝ → ℂ := fun w => u (2 * π * w) with hv
  have hvc : Continuous v := hu.comp (continuous_const.mul continuous_id)
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hS : ∀ g : SchwartzMap ℝ ℂ, ∫ w, v w * g w = 0 := by
    intro g
    have h1 := h (𝓕⁻ g : SchwartzMap ℝ ℂ)
    have h3 : ∀ x, fourierT (⇑(𝓕⁻ g : SchwartzMap ℝ ℂ)) x = g (x / (2 * π)) := by
      intro x
      rw [c08_aux_fourierT_eq, ← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq]
    simp_rw [h3] at h1
    have h4 := Measure.integral_comp_mul_left (fun x => u x * g (x / (2 * π))) (2 * π)
    simp only [h1, smul_zero] at h4
    rw [← h4]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hv]
    rw [mul_div_cancel_left₀ _ h2π]
  have hae : ∀ᵐ w ∂(volume : Measure ℝ), v w = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hvc.locallyIntegrable
    intro g hg hgs
    have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (g w : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hg
    have hgs' : HasCompactSupport (fun w => (g w : ℂ)) := hgs.comp_left Complex.ofReal_zero
    have : ∫ w, v w * (g w : ℂ) = 0 := hS (hgs'.toSchwartzMap hgc)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [Complex.real_smul, mul_comm]
  have hv0 : v = 0 := (hvc.ae_eq_iff_eq volume continuous_const).1 hae
  ext x
  have := congrFun hv0 (x / (2 * π))
  simp only [hv, Pi.zero_apply] at this ⊢
  rwa [mul_div_cancel₀ _ h2π] at this

/-- `⟨y⟩ ≤ 1 + |y|`. -/
theorem c08_aux_jb_le_one_add (y : ℝ) : jb y ≤ 1 + |y| := by
  unfold jb
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg y, sq_abs y]

/-- A continuous polynomially bounded function times the transform of a Schwartz function is
integrable. -/
theorem c08_aux_polyBounded_mul_fourierT_integrable (u : ℝ → ℂ) (hu : Continuous u)
    (hpb : IsPolyBounded u) (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x => u x * fourierT (⇑φ) x) := by
  obtain ⟨C, N, hC⟩ := hpb
  set ψ : SchwartzMap ℝ ℂ := 𝓕 φ
  set K : ℕ := ⌈N⌉₊
  obtain ⟨S, hS⟩ : ∃ S, ∀ w : ℝ, (1 + ‖w‖) ^ (K + 2) * ‖ψ w‖ ≤ S := by
    refine ⟨2 ^ (K + 2) * (Finset.Iic (K + 2, 0)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ, fun w => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K + 2, 0)) le_rfl le_rfl ψ w
    rwa [norm_iteratedFDeriv_zero] at this
  have h2π : (1:ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hdom : Integrable (fun x : ℝ => (|C| * (2 * π) ^ (K + 2) * S) * (1 + ‖x‖) ^ (-(2:ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)).const_mul _
  refine hdom.mono' ((hu.mul (c08_aux_fourierT_continuous φ)).aestronglyMeasurable) ?_
  refine Eventually.of_forall (fun x => ?_)
  have hx1 : (1:ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hx0 : (0:ℝ) < 1 + |x| := by linarith
  -- bound on u
  have hu1 : ‖u x‖ ≤ |C| * (1 + |x|) ^ K := by
    refine (hC x).trans ?_
    have h1 : jb x ^ N ≤ jb x ^ (K : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb x) (Nat.le_ceil N)
    rw [Real.rpow_natCast] at h1
    have h2 : jb x ^ K ≤ (1 + |x|) ^ K :=
      pow_le_pow_left₀ (c08_aux_jb_pos x).le (c08_aux_jb_le_one_add x) K
    have h3 : 0 ≤ jb x ^ N := Real.rpow_nonneg (c08_aux_jb_pos x).le _
    calc C * jb x ^ N ≤ |C| * jb x ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) h3
      _ ≤ |C| * (1 + |x|) ^ K := mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C)
  -- bound on the transform
  have hψ : ‖fourierT (⇑φ) x‖ * (1 + |x|) ^ (K + 2) ≤ (2 * π) ^ (K + 2) * S := by
    rw [c08_aux_fourierT_eq, ← SchwartzMap.fourier_coe]
    have := hS (x / (2 * π))
    have hle : 1 + |x| ≤ 2 * π * (1 + ‖x / (2 * π)‖) := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * π), mul_add,
        mul_div_cancel₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
      linarith
    calc ‖ψ (x / (2 * π))‖ * (1 + |x|) ^ (K + 2)
        ≤ ‖ψ (x / (2 * π))‖ * (2 * π * (1 + ‖x / (2 * π)‖)) ^ (K + 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0.le hle _) (norm_nonneg _)
      _ = (2 * π) ^ (K + 2) * ((1 + ‖x / (2 * π)‖) ^ (K + 2) * ‖ψ (x / (2 * π))‖) := by
          rw [mul_pow]; ring
      _ ≤ (2 * π) ^ (K + 2) * S := mul_le_mul_of_nonneg_left this (by positivity)
  rw [norm_mul, Real.norm_eq_abs x, Real.rpow_neg hx0.le, Real.rpow_two]
  have hpow : (1 + |x|) ^ (K + 2) = (1 + |x|) ^ K * (1 + |x|) ^ 2 := pow_add _ _ _
  rw [hpow] at hψ
  have hK0 : 0 < (1 + |x|) ^ K := pow_pos hx0 K
  have hsq0 : 0 < (1 + |x|) ^ 2 := pow_pos hx0 2
  rw [le_mul_inv_iff₀ hsq0]
  calc ‖u x‖ * ‖fourierT (⇑φ) x‖ * (1 + |x|) ^ 2
      ≤ |C| * (1 + |x|) ^ K * ‖fourierT (⇑φ) x‖ * (1 + |x|) ^ 2 := by
        gcongr
    _ = |C| * (‖fourierT (⇑φ) x‖ * ((1 + |x|) ^ K * (1 + |x|) ^ 2)) := by ring
    _ ≤ |C| * ((2 * π) ^ (K + 2) * S) := mul_le_mul_of_nonneg_left hψ (abs_nonneg C)
    _ = _ := by ring


/-- A continuous inequality holding a.e. on both half-lines holds everywhere. -/
theorem c08_aux_le_of_ae_halflines {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h1 : ∀ᵐ y ∂(volume.restrict (Ici (0:ℝ))), f y ≤ g y)
    (h2 : ∀ᵐ y ∂(volume.restrict (Iic (0:ℝ))), f y ≤ g y) : ∀ y, f y ≤ g y := by
  rw [ae_restrict_iff' measurableSet_Ici] at h1
  rw [ae_restrict_iff' measurableSet_Iic] at h2
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), f y ≤ g y := by
    filter_upwards [h1, h2] with y hy1 hy2
    rcases le_total 0 y with h | h
    · exact hy1 h
    · exact hy2 h
  have hopen : IsOpen {y | g y < f y} := isOpen_lt hg hf
  have hnull : volume {y | g y < f y} = 0 := by
    rw [ae_iff] at hae
    simpa [not_le] using hae
  have hempty := (hopen.measure_eq_zero_iff volume).1 hnull
  intro y
  by_contra hy
  have : y ∈ {y | g y < f y} := lt_of_not_ge hy
  rw [hempty] at this
  exact this

/-- From a finite essential supremum of `ofReal ∘ g` to an a.e. bound by its `toReal`. -/
theorem c08_aux_ae_le_essSup_toReal {μ : Measure ℝ} {g : ℝ → ℝ}
    (h : essSup (fun y => ENNReal.ofReal (g y)) μ < ⊤) :
    ∀ᵐ y ∂μ, g y ≤ (essSup (fun y => ENNReal.ofReal (g y)) μ).toReal := by
  filter_upwards [ENNReal.ae_le_essSup (fun y => ENNReal.ofReal (g y))] with y hy
  exact (ENNReal.ofReal_le_iff_le_toReal h.ne).1 hy

/-- `M ⟨y⟩^{-γ}` from `⟨y⟩^γ a ≤ M`. -/
theorem c08_aux_div_weight {a M γ y : ℝ} (h : jb y ^ γ * a ≤ M) : a ≤ M * jb y ^ (-γ) := by
  have hpos : 0 < jb y ^ γ := Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ
  rw [Real.rpow_neg (c08_aux_jb_pos y).le, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- Pointwise bound `|r y| ≤ ‖r‖_{X_γ} ⟨y⟩^{-γ}` for `r ∈ X_γ` (everywhere, by continuity). -/
theorem c08_aux_X_pointwise {p γ : ℝ} {r : ℝ → ℝ} (hr : r ∈ X_gamma p γ) (y : ℝ) :
    |r y| ≤ xNorm p γ r * jb y ^ (-γ) := by
  obtain ⟨⟨hC1, _⟩, hfin⟩ := hr
  unfold X_gamma_norm at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have hx : xNorm p γ r = _ := ENNReal.toReal_add h1.ne h2.ne
  have hcont : Continuous r := hC1.continuous
  have hw : Continuous (fun y => xNorm p γ r * jb y ^ (-γ)) := by
    apply continuous_const.mul
    exact (Real.continuous_sqrt.comp (by fun_prop)).rpow_const
      (fun y => Or.inl (c08_aux_jb_pos y).ne')
  refine c08_aux_le_of_ae_halflines (hcont.abs) hw ?_ ?_ y
  · filter_upwards [c08_aux_ae_le_essSup_toReal h1] with y hy
    apply c08_aux_div_weight
    rw [hx]
    have hw0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ).le
    have : jb y ^ γ * |r y| ≤ jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
        jb y ^ (-2 / p) * ‖deriv (deriv r) y‖) := by
      apply mul_le_mul_of_nonneg_left _ hw0
      rw [← Real.norm_eq_abs]
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-1 / p)
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-2 / p)
      have := norm_nonneg (deriv r y); have := norm_nonneg (deriv (deriv r) y)
      nlinarith
    linarith [ENNReal.toReal_nonneg (a := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ +
      jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0)))]
  · filter_upwards [c08_aux_ae_le_essSup_toReal h2] with y hy
    apply c08_aux_div_weight
    rw [hx]
    have hw0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ).le
    have : jb y ^ γ * |r y| ≤ jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
        jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖) := by
      apply mul_le_mul_of_nonneg_left _ hw0
      rw [← Real.norm_eq_abs]
      have := c08_aux_jb_pos y
      have := norm_nonneg (deriv r y); have := norm_nonneg (deriv (deriv r) y)
      have : 0 ≤ jb y ^ (2:ℕ) := by positivity
      nlinarith
    linarith [ENNReal.toReal_nonneg (a := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ +
      jb y ^ (-1 / p) * ‖deriv r y‖ + jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)))
      (volume.restrict (Ici 0)))]

/-- Elements of `X_γ` are continuous and polynomially bounded. -/
theorem c08_aux_X_polyBounded {p γ : ℝ} {r : ℝ → ℝ} (hr : r ∈ X_gamma p γ) :
    Continuous r ∧ IsPolyBounded r :=
  ⟨hr.1.1.continuous, ⟨xNorm p γ r, -γ, fun y => by
    rw [Real.norm_eq_abs]; exact c08_aux_X_pointwise hr y⟩⟩

/-- `Y_γ ⊆ Y_{γ'}` for `γ' ≤ γ`. -/
theorem c08_aux_Y_mono {p γ γ' : ℝ} (hγ : γ' ≤ γ) {G : ℝ → ℝ} (hG : G ∈ Y_gamma p γ) :
    G ∈ Y_gamma p γ' := by
  refine ⟨hG.1, lt_of_le_of_lt ?_ hG.2⟩
  unfold Y_gamma_norm
  have hw : ∀ y, jb y ^ γ' ≤ jb y ^ γ := fun y =>
    Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb y) hγ
  gcongr
  · refine essSup_mono_ae (Eventually.of_forall fun y => ?_)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right (hw y)
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-1 / p)
    positivity
  · refine essSup_mono_ae (Eventually.of_forall fun y => ?_)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right (hw y)
    have := c08_aux_jb_pos y
    positivity

/-- `‖(f+g)'(y)‖ ≤ ‖f'(y)‖ + ‖g'(y)‖` whenever `f` is differentiable at `y`. -/
theorem c08_aux_norm_deriv_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {y : ℝ} (hf : DifferentiableAt ℝ f y) :
    ‖deriv (f + g) y‖ ≤ ‖deriv f y‖ + ‖deriv g y‖ := by
  by_cases hg : DifferentiableAt ℝ g y
  · rw [deriv_add hf hg]; exact norm_add_le _ _
  · have : ¬ DifferentiableAt ℝ (f + g) y := by
      intro h
      apply hg
      have := h.sub hf
      simp only [add_sub_cancel_left] at this
      exact this
    rw [deriv_zero_of_not_differentiableAt this, norm_zero]
    positivity

/-- Triangle inequality for the `X_γ` norm when the first summand is `C²`
(so that `(r+s)'' ≤ r'' + s''` pointwise). -/
theorem c08_aux_X_norm_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p γ : ℝ) {r s : ℝ → E} (hr : ContDiff ℝ 2 r) (hs : ContDiff ℝ 1 s) :
    X_gamma_norm p γ (r + s) ≤ X_gamma_norm p γ r + X_gamma_norm p γ s := by
  have hd1 : deriv (r + s) = deriv r + deriv s := by
    ext y
    exact deriv_add (hr.differentiable (by norm_num) y) (hs.differentiable (by norm_num) y)
  have hdr : Differentiable ℝ (deriv r) := by
    have : ContDiff ℝ 1 (deriv r) := by
      have := hr.iterate_deriv' 1 1
      simpa using this
    exact this.differentiable (by norm_num)
  have hd2 : ∀ y, ‖deriv (deriv (r + s)) y‖ ≤ ‖deriv (deriv r) y‖ + ‖deriv (deriv s) y‖ := by
    intro y; rw [hd1]; exact c08_aux_norm_deriv_add_le (hdr y)
  have key : ∀ (w1 w2 : ℝ → ℝ), (∀ y, 0 ≤ w1 y) → (∀ y, 0 ≤ w2 y) → ∀ μ : Measure ℝ,
      essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖(r + s) y‖ + w1 y * ‖deriv (r + s) y‖ +
          w2 y * ‖deriv (deriv (r + s)) y‖))) μ ≤
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + w1 y * ‖deriv r y‖ +
          w2 y * ‖deriv (deriv r) y‖))) μ +
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖s y‖ + w1 y * ‖deriv s y‖ +
          w2 y * ‖deriv (deriv s) y‖))) μ := by
    intro w1 w2 hw1 hw2 μ
    refine le_trans (essSup_mono_ae (Eventually.of_forall fun y => ?_)) (ENNReal.essSup_add_le _ _)
    simp only [Pi.add_apply]
    rw [← ENNReal.ofReal_add (by have := c08_aux_jb_pos y; have := hw1 y; have := hw2 y; positivity)
      (by have := c08_aux_jb_pos y; have := hw1 y; have := hw2 y; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ).le
    have h1 : ‖r y + s y‖ ≤ ‖r y‖ + ‖s y‖ := norm_add_le _ _
    have h2 : ‖deriv (r + s) y‖ ≤ ‖deriv r y‖ + ‖deriv s y‖ := by
      rw [hd1]; exact norm_add_le _ _
    have h3 := hd2 y
    have := hw1 y; have := hw2 y
    nlinarith [mul_le_mul_of_nonneg_left h2 (hw1 y), mul_le_mul_of_nonneg_left h3 (hw2 y)]
  unfold X_gamma_norm
  have e1 := key (fun y => jb y ^ (-1 / p)) (fun y => jb y ^ (-2 / p))
    (fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le)
    (fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le) (volume.restrict (Ici 0))
  have e2 := key (fun y => jb y) (fun y => jb y ^ (2 : ℕ))
    (fun y => (c08_aux_jb_pos y).le) (fun y => by have := c08_aux_jb_pos y; positivity)
    (volume.restrict (Iic 0))
  calc _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- Uniqueness of the distributional inverse: if a continuous, polynomially bounded real `r` has
`r̂ = m` in `𝒮'`, then `distFourierInv m = r`. -/
theorem c08_aux_distFourierInv_eq {m : ℝ → ℂ} {r : ℝ → ℝ} (hr : Continuous r)
    (hpb : IsPolyBounded r) (hF : HasDistFourier (fun x => (r x : ℂ)) m) :
    distFourierInv m = r := by
  have hex : ∃ r : ℝ → ℝ, Continuous r ∧ IsPolyBounded r ∧ HasDistFourier (fun x => (r x : ℂ)) m :=
    ⟨r, hr, hpb, hF⟩
  unfold distFourierInv
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hc', hpb', hF'⟩ := Classical.choose_spec hex
  set r' := Classical.choose hex
  have hpbC : ∀ u : ℝ → ℝ, IsPolyBounded u → IsPolyBounded (fun x => (u x : ℂ)) := by
    rintro u ⟨C, N, hC⟩; exact ⟨C, N, fun x => by simpa using hC x⟩
  have hzero := c08_aux_distFourier_zero (fun x => (r' x : ℂ) - (r x : ℂ))
    ((Complex.continuous_ofReal.comp hc').sub (Complex.continuous_ofReal.comp hr)) (by
      intro φ
      have i1 : Integrable (fun x => ((r' x : ℝ) : ℂ) * fourierT (⇑φ) x) :=
        c08_aux_polyBounded_mul_fourierT_integrable _
          (Complex.continuous_ofReal.comp hc') (hpbC _ hpb') φ
      have i2 : Integrable (fun x => ((r x : ℝ) : ℂ) * fourierT (⇑φ) x) :=
        c08_aux_polyBounded_mul_fourierT_integrable _
          (Complex.continuous_ofReal.comp hr) (hpbC _ hpb) φ
      simp_rw [sub_mul]
      rw [integral_sub i1 i2, hF' φ, hF φ, sub_self])
  ext x
  have := congrFun hzero x
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact_mod_cast this

/-- Triangle inequality for the `Y_γ` norm when the first summand is differentiable everywhere. -/
theorem c08_aux_Y_norm_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p γ : ℝ) {f g : ℝ → E} (hf : Differentiable ℝ f) :
    Y_gamma_norm p γ (f + g) ≤ Y_gamma_norm p γ f + Y_gamma_norm p γ g := by
  have key : ∀ (w1 : ℝ → ℝ), (∀ y, 0 ≤ w1 y) → ∀ μ : Measure ℝ,
      essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖(f + g) y‖ + w1 y * ‖deriv (f + g) y‖))) μ ≤
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖f y‖ + w1 y * ‖deriv f y‖))) μ +
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖g y‖ + w1 y * ‖deriv g y‖))) μ := by
    intro w1 hw1 μ
    refine le_trans (essSup_mono_ae (Eventually.of_forall fun y => ?_)) (ENNReal.essSup_add_le _ _)
    simp only [Pi.add_apply]
    rw [← ENNReal.ofReal_add (by have := c08_aux_jb_pos y; have := hw1 y; positivity)
      (by have := c08_aux_jb_pos y; have := hw1 y; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ).le
    have h1 : ‖f y + g y‖ ≤ ‖f y‖ + ‖g y‖ := norm_add_le _ _
    have h2 : ‖deriv (f + g) y‖ ≤ ‖deriv f y‖ + ‖deriv g y‖ := c08_aux_norm_deriv_add_le (hf y)
    nlinarith [mul_le_mul_of_nonneg_left h2 (hw1 y)]
  unfold Y_gamma_norm
  have e1 := key (fun y => jb y ^ (-1 / p))
    (fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le) (volume.restrict (Ici 0))
  have e2 := key (fun y => jb y) (fun y => (c08_aux_jb_pos y).le) (volume.restrict (Iic 0))
  calc _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- `Y_γ` is closed under addition when the first summand is differentiable, with the triangle
inequality for `yNorm`. -/
theorem c08_aux_Y_add {p γ : ℝ} {f g : ℝ → ℝ} (hf : f ∈ Y_gamma p γ) (hg : g ∈ Y_gamma p γ)
    (hfd : Differentiable ℝ f) :
    f + g ∈ Y_gamma p γ ∧ yNorm p γ (f + g) ≤ yNorm p γ f + yNorm p γ g := by
  have hle := c08_aux_Y_norm_add_le p γ (g := g) hfd
  have hfin : Y_gamma_norm p γ f + Y_gamma_norm p γ g < ⊤ := ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩
  refine ⟨⟨hf.1.add hg.1, lt_of_le_of_lt hle hfin⟩, ?_⟩
  unfold yNorm
  rw [← ENNReal.toReal_add hf.2.ne hg.2.ne]
  exact ENNReal.toReal_mono hfin.ne hle

/-- A continuous function in `L^∞` is bounded everywhere. -/
theorem c08_aux_bounded_of_memLp_top {f : ℝ → ℝ} (hf : Continuous f) (hL : MemLp f ⊤ volume) :
    ∃ M : ℝ, ∀ y, |f y| ≤ M := by
  have hfin : eLpNormEssSup f volume < ⊤ :=
    lt_of_le_of_lt eLpNormEssSup_le_eLpNorm_top hL
  refine ⟨(eLpNormEssSup f volume).toReal, fun y => ?_⟩
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), |f y| ≤ (eLpNormEssSup f volume).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with y hy
    rw [← ofReal_norm, Real.norm_eq_abs] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 hy
  exact c08_aux_le_of_ae_halflines hf.abs continuous_const (ae_restrict_of_ae hae)
    (ae_restrict_of_ae hae) y

/-- Comparison of the `Y_γ` norm of `G` with the `X_γ` norm of `r` from a pointwise comparison of
the integrands on both half-lines. -/
theorem c08_aux_Y_le_of_X {p γ K : ℝ} (hK : 0 ≤ K) {G r : ℝ → ℝ}
    (h1 : ∀ y, 0 ≤ y → jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖) ≤
      K * (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
        jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)))
    (h2 : ∀ y, y ≤ 0 → jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖) ≤
      K * (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) :
    Y_gamma_norm p γ G ≤ ENNReal.ofReal K * X_gamma_norm p γ r := by
  unfold Y_gamma_norm X_gamma_norm
  rw [mul_add]
  gcongr
  · rw [← ENNReal.essSup_const_mul]
    refine essSup_mono_ae ((ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall
      fun y hy => ?_))
    simp only
    rw [← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (h1 y hy)
  · rw [← ENNReal.essSup_const_mul]
    refine essSup_mono_ae ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall
      fun y hy => ?_))
    simp only
    rw [← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (h2 y hy)

/-- Real-valued version of `c08_aux_Y_le_of_X`. -/
theorem c08_aux_yNorm_le_of_X {p γ K : ℝ} (hK : 0 ≤ K) {G r : ℝ → ℝ} (hr : r ∈ X_gamma p γ)
    (h1 : ∀ y, 0 ≤ y → jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖) ≤
      K * (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
        jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)))
    (h2 : ∀ y, y ≤ 0 → jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖) ≤
      K * (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) :
    Y_gamma_norm p γ G < ⊤ ∧ yNorm p γ G ≤ K * xNorm p γ r := by
  have h := c08_aux_Y_le_of_X hK h1 h2
  have hfin : ENNReal.ofReal K * X_gamma_norm p γ r < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hr.2
  refine ⟨lt_of_le_of_lt h hfin, ?_⟩
  unfold yNorm xNorm
  calc (Y_gamma_norm p γ G).toReal ≤ (ENNReal.ofReal K * X_gamma_norm p γ r).toReal :=
        ENNReal.toReal_mono hfin.ne h
    _ = K * (X_gamma_norm p γ r).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]

/-- The Fourier transform of an integrable function is continuous. -/
theorem c08_aux_fourierT_continuous_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fourierT f) := by
  unfold fourierT
  apply continuous_of_dominated (bound := fun x => ‖f x‖)
  · intro ξ
    exact hf.1.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · intro ξ
    refine Eventually.of_forall (fun x => ?_)
    rw [norm_mul]
    have : ‖Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, mul_one]
  · exact hf.norm
  · exact Eventually.of_forall (fun x => by fun_prop)

/-- Hermitian symmetry of the Fourier transform of a real function. -/
theorem c08_aux_fourierT_neg_real (G : ℝ → ℝ) (s : ℝ) :
    fourierT (fun x => (G x : ℂ)) (-s) = (starRingEnd ℂ) (fourierT (fun x => (G x : ℂ)) s) := by
  unfold fourierT
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (-(Complex.I * (x : ℂ) * (s : ℂ))) =
      -(Complex.I * (x : ℂ) * ((-s : ℝ) : ℂ)) := by
    simp [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [this]

/-- `Φ₀` is odd. -/
theorem c08_aux_Phi0_neg (p s : ℝ) : Phi0 p (-s) = -Phi0 p s := by
  unfold Phi0; rw [abs_neg]; ring

/-- `Φ₀` is continuous for `p ≥ 0`. -/
theorem c08_aux_Phi0_continuous (p : ℝ) (hp : 0 ≤ p) : Continuous (Phi0 p) := by
  unfold Phi0
  exact (continuous_id.mul (continuous_abs.rpow_const (fun _ => Or.inr hp))).div_const _

/-- `|t^q - 1| ≤ 7|t - 1|` for `t ∈ [0,2]`, `q ∈ [1,3]`. -/
theorem c08_aux_rpow_sub_one_le {t q : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) :
    |t ^ q - 1| ≤ 7 * |t - 1| := by
  rcases le_total 1 t with h | h
  · have hconv := (convexOn_rpow hq1).2 (show (1:ℝ) ∈ Ici 0 by simp) (show (2:ℝ) ∈ Ici 0 by simp)
      (show 0 ≤ 2 - t by linarith) (show 0 ≤ t - 1 by linarith) (by ring)
    simp only [smul_eq_mul, Real.one_rpow] at hconv
    have h2q : (2:ℝ) ^ q ≤ 8 := by
      calc (2:ℝ) ^ q ≤ 2 ^ (3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq3
        _ = 8 := by norm_num
    have hge : 1 ≤ t ^ q := Real.one_le_rpow h (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    rw [show (2 - t) * 1 + (t - 1) * 2 = t by ring] at hconv
    nlinarith
  · have hb := one_add_mul_self_le_rpow_one_add (show -1 ≤ t - 1 by linarith) hq1
    rw [show 1 + (t - 1) = t by ring] at hb
    have hle : t ^ q ≤ 1 := Real.rpow_le_one ht0 h (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    nlinarith

/-- For smooth `φ`: `(φ - id)' = φ' - 1` and `(φ - id)'' = φ''`. -/
theorem c08_aux_iteratedDeriv_sub_id {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    iteratedDeriv 1 (fun y => φ y - y) = (fun y => deriv φ y - 1) ∧
    iteratedDeriv 2 (fun y => φ y - y) = deriv (deriv φ) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have h1 : deriv (fun y => φ y - y) = fun y => deriv φ y - 1 := by
    ext y; rw [deriv_fun_sub (hd y) differentiableAt_fun_id, deriv_id'']
  refine ⟨by rw [iteratedDeriv_one, h1], ?_⟩
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, h1]
  ext y; rw [deriv_sub_const]

/-- `A ≤ 2B → B^{-b} ≤ 2^b A^{-b}` (`A > 0`, `b ≥ 0`). -/
theorem c08_aux_rpow_neg_le_of_le {A B b : ℝ} (hA : 0 < A) (hb : 0 ≤ b) (h : A ≤ 2 * B) :
    B ^ (-b) ≤ 2 ^ b * A ^ (-b) := by
  have h1 : A / 2 ≤ B := by linarith
  have h2 : B ^ (-b) ≤ (A / 2) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)
  calc _ ≤ _ := h2
    _ = 2 ^ b * A ^ (-b) := by
      rw [Real.div_rpow hA.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp

/-- The project Fourier transform of a real integrable function via `cos` and `sin`. -/
theorem c08_aux_fourierT_cos_sin {h : ℝ → ℝ} (hh : Integrable h) (ξ : ℝ) :
    fourierT (fun x => (h x : ℂ)) ξ =
      ((∫ x, h x * Real.cos (x * ξ) : ℝ) : ℂ) - Complex.I * ((∫ x, h x * Real.sin (x * ξ) : ℝ) : ℂ) := by
  have hc : Integrable (fun x => h x * Real.cos (x * ξ)) :=
    hh.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable (fun x => h x * Real.sin (x * ξ)) :=
    hh.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  unfold fourierT
  have hpt : ∀ x : ℝ, (h x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) =
      ((h x * Real.cos (x * ξ) : ℝ) : ℂ) - Complex.I * ((h x * Real.sin (x * ξ) : ℝ) : ℂ) := by
    intro x
    have e : -(Complex.I * (x : ℂ) * (ξ : ℂ)) = ((-(x * ξ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have k1 : ∫ x, ((h x * Real.cos (x * ξ) : ℝ) : ℂ) = ((∫ x, h x * Real.cos (x * ξ) : ℝ) : ℂ) :=
    integral_ofReal
  have k2 : ∫ x, ((h x * Real.sin (x * ξ) : ℝ) : ℂ) = ((∫ x, h x * Real.sin (x * ξ) : ℝ) : ℂ) :=
    integral_ofReal
  have k3 : ∫ x, Complex.I * ((h x * Real.sin (x * ξ) : ℝ) : ℂ) =
      Complex.I * ∫ x, ((h x * Real.sin (x * ξ) : ℝ) : ℂ) := integral_const_mul _ _
  have i1 : Integrable (fun x => ((h x * Real.cos (x * ξ) : ℝ) : ℂ)) := hc.ofReal
  have i2 : Integrable (fun x => Complex.I * ((h x * Real.sin (x * ξ) : ℝ) : ℂ)) :=
    hs.ofReal.const_mul _
  rw [integral_sub i1 i2, k3, k1, k2]

/-- Integration by parts on `[a,b]` for locally Lipschitz `f` against a `C¹` function `g`. -/
theorem c08_aux_ibp_interval {f g : ℝ → ℝ} (hf : LocallyLipschitz f) (hg : ContDiff ℝ 1 g)
    (a b : ℝ) :
    ∫ x in a..b, g x * deriv f x = g b * f b - g a * f a - ∫ x in a..b, deriv g x * f x := by
  have hfac : AbsolutelyContinuousOnInterval f a b := by
    obtain ⟨K, hK⟩ := (hf.locallyLipschitzOn (s := uIcc a b)).exists_lipschitzOnWith_of_compact
      isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval
  have hgac : AbsolutelyContinuousOnInterval g a b := hg.contDiffOn.absolutelyContinuousOnInterval
  exact AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hgac hfac

/-- Integration by parts on `ℝ`: `∫ g f' = -∫ g' f` for locally Lipschitz `f → 0` at infinity with
`f, f' ∈ L¹`, and `g` a bounded `C¹` function with bounded derivative. -/
theorem c08_aux_ibp_line {f g : ℝ → ℝ} (hf : LocallyLipschitz f) (hfi : Integrable f)
    (hdi : Integrable (deriv f)) (hlim : Tendsto f (cocompact ℝ) (nhds 0)) (hg : ContDiff ℝ 1 g)
    {B : ℝ} (hgB : ∀ x, |g x| ≤ B) (hg'B : ∀ x, |deriv g x| ≤ B) :
    ∫ x, g x * deriv f x = -∫ x, deriv g x * f x := by
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have i1 : Integrable (fun x => g x * deriv f x) :=
    hdi.bdd_mul hgc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hgB x)
  have i2 : Integrable (fun x => deriv g x * f x) :=
    hfi.bdd_mul hg'c.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hg'B x)
  have t1 := intervalIntegral_tendsto_integral i1 tendsto_neg_atTop_atBot tendsto_id
  have t2 := intervalIntegral_tendsto_integral i2 tendsto_neg_atTop_atBot tendsto_id
  have hbd : Tendsto (fun R : ℝ => g R * f R - g (-R) * f (-R)) atTop (nhds 0) := by
    have hfa : Tendsto f atTop (nhds 0) := hlim.mono_left atTop_le_cocompact
    have hfb : Tendsto (fun R : ℝ => f (-R)) atTop (nhds 0) :=
      (hlim.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot
    have hsq : ∀ (u : ℝ → ℝ), Tendsto u atTop (nhds 0) → ∀ v : ℝ → ℝ, (∀ R, |v R| ≤ B) →
        Tendsto (fun R => v R * u R) atTop (nhds 0) := by
      intro u hu v hv
      have hB : 0 ≤ B := le_trans (abs_nonneg _) (hv 0)
      apply squeeze_zero_norm (a := fun R => B * |u R|)
      · intro R; rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hv R) (abs_nonneg _)
      · have := (hu.abs).const_mul B
        simpa using this
    have := (hsq _ hfa g hgB).sub (hsq _ hfb (fun R => g (-R)) (fun R => hgB _))
    simpa using this
  have heq : ∀ R : ℝ, (∫ x in (-R)..id R, g x * deriv f x) =
      (g R * f R - g (-R) * f (-R)) - ∫ x in (-R)..id R, deriv g x * f x := by
    intro R; exact c08_aux_ibp_interval hf hg (-R) R
  have t3 : Tendsto (fun R : ℝ => ∫ x in (-R)..id R, g x * deriv f x) atTop
      (nhds (0 - ∫ x, deriv g x * f x)) := by
    simp_rw [heq]; exact hbd.sub t2
  rw [tendsto_nhds_unique t1 t3, zero_sub]

/-- `(f')^ = iξ f̂` for real locally Lipschitz `f` with `f, f' ∈ L¹` and `f → 0` at infinity. -/
theorem c08_aux_fourierT_deriv {f : ℝ → ℝ} (hf : LocallyLipschitz f) (hfi : Integrable f)
    (hdi : Integrable (deriv f)) (hlim : Tendsto f (cocompact ℝ) (nhds 0)) (ξ : ℝ) :
    fourierT (fun x => ((deriv f x : ℝ) : ℂ)) ξ = Complex.I * ξ * fourierT (fun x => (f x : ℂ)) ξ := by
  have hB : ∀ x : ℝ, |Real.cos (x * ξ)| ≤ 1 + |ξ| ∧ |Real.sin (x * ξ)| ≤ 1 + |ξ| ∧
      |ξ * Real.sin (x * ξ)| ≤ 1 + |ξ| ∧ |ξ * Real.cos (x * ξ)| ≤ 1 + |ξ| := by
    intro x
    have h1 := Real.abs_cos_le_one (x * ξ); have h2 := Real.abs_sin_le_one (x * ξ)
    have h0 := abs_nonneg ξ
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · rw [abs_mul]; nlinarith [abs_nonneg (Real.sin (x * ξ))]
    · rw [abs_mul]; nlinarith [abs_nonneg (Real.cos (x * ξ))]
  have hdc : deriv (fun x : ℝ => Real.cos (x * ξ)) = fun x => -(Real.sin (x * ξ) * ξ) := by
    ext x
    simp
  have hds : deriv (fun x : ℝ => Real.sin (x * ξ)) = fun x => Real.cos (x * ξ) * ξ := by
    ext x
    simp
  have ic := c08_aux_ibp_line hf hfi hdi hlim (g := fun x => Real.cos (x * ξ)) (by fun_prop)
    (fun x => (hB x).1) (fun x => by rw [hdc]; simp only [abs_neg]; rw [mul_comm]; exact (hB x).2.2.1)
  have is := c08_aux_ibp_line hf hfi hdi hlim (g := fun x => Real.sin (x * ξ)) (by fun_prop)
    (fun x => (hB x).2.1) (fun x => by rw [hds]; simp only; rw [mul_comm]; exact (hB x).2.2.2)
  rw [hdc] at ic; rw [hds] at is
  rw [c08_aux_fourierT_cos_sin hdi, c08_aux_fourierT_cos_sin hfi]
  simp_rw [mul_comm (deriv f _)]
  rw [ic, is]
  have e1 : ∫ x, -(Real.sin (x * ξ) * ξ) * f x = -(ξ * ∫ x, f x * Real.sin (x * ξ)) := by
    rw [← integral_const_mul, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have e2 : ∫ x, Real.cos (x * ξ) * ξ * f x = ξ * ∫ x, f x * Real.cos (x * ξ) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e1, e2]
  generalize (∫ x, f x * Real.sin (x * ξ)) = A
  generalize (∫ x, f x * Real.cos (x * ξ)) = B
  push_cast
  linear_combination ((ξ:ℂ) * A) * Complex.I_sq

/-- Combine a.e. statements on both half-lines into an a.e. statement on `ℝ`. -/
theorem c08_aux_ae_of_halflines {P : ℝ → Prop}
    (h1 : ∀ᵐ y ∂(volume.restrict (Ici (0:ℝ))), P y)
    (h2 : ∀ᵐ y ∂(volume.restrict (Iic (0:ℝ))), P y) : ∀ᵐ y ∂(volume : Measure ℝ), P y := by
  rw [ae_restrict_iff' measurableSet_Ici] at h1
  rw [ae_restrict_iff' measurableSet_Iic] at h2
  filter_upwards [h1, h2] with y hy1 hy2
  rcases le_total 0 y with h | h
  · exact hy1 h
  · exact hy2 h

/-- A.e. pointwise bounds for `G ∈ Y_γ`: `|G| ≤ ‖G‖⟨y⟩^{-γ}`, `|G'| ≤ ‖G‖⟨y⟩^{-γ+1/p}`. -/
theorem c08_aux_Y_ae_bound {p γ : ℝ} (hp : 0 < p) {G : ℝ → ℝ} (hG : G ∈ Y_gamma p γ) :
    ∀ᵐ y ∂(volume : Measure ℝ), |G y| ≤ yNorm p γ G * jb y ^ (-γ) ∧
      |deriv G y| ≤ yNorm p γ G * jb y ^ (-γ + 1 / p) := by
  have hfin := hG.2
  unfold Y_gamma_norm at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have hx : yNorm p γ G = _ := ENNReal.toReal_add h1.ne h2.ne
  set E1 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖)))
      (volume.restrict (Ici 0))
  set E2 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖)))
      (volume.restrict (Iic 0))
  have hN1 : E1.toReal ≤ yNorm p γ G := by rw [hx]; linarith [ENNReal.toReal_nonneg (a := E2)]
  have hN2 : E2.toReal ≤ yNorm p γ G := by rw [hx]; linarith [ENNReal.toReal_nonneg (a := E1)]
  apply c08_aux_ae_of_halflines
  · filter_upwards [c08_aux_ae_le_essSup_toReal h1] with y hy
    have hj := c08_aux_jb_pos y
    have hg := Real.rpow_pos_of_pos hj γ
    have hw := Real.rpow_pos_of_pos hj (-1 / p)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hy
    have a0 := abs_nonneg (G y); have a1 := abs_nonneg (deriv G y)
    constructor
    · apply c08_aux_div_weight
      nlinarith [mul_nonneg hg.le (mul_nonneg hw.le a1)]
    · have : jb y ^ (γ - 1 / p) * |deriv G y| ≤ yNorm p γ G := by
        rw [sub_eq_add_neg, Real.rpow_add hj, show -(1 / p) = -1 / p by ring]
        nlinarith [mul_nonneg hg.le a0]
      have := c08_aux_div_weight this
      rwa [show -(γ - 1 / p) = -γ + 1 / p by ring] at this
  · filter_upwards [c08_aux_ae_le_essSup_toReal h2] with y hy
    have hj := c08_aux_jb_pos y
    have hj1 := c08_aux_one_le_jb y
    have hg := Real.rpow_pos_of_pos hj γ
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hy
    have a0 := abs_nonneg (G y); have a1 := abs_nonneg (deriv G y)
    constructor
    · apply c08_aux_div_weight
      nlinarith [mul_nonneg hg.le (mul_nonneg hj.le a1)]
    · have h3 : jb y ^ (γ + 1) * |deriv G y| ≤ yNorm p γ G := by
        rw [Real.rpow_add hj, Real.rpow_one]
        nlinarith [mul_nonneg hg.le a0]
      have h4 := c08_aux_div_weight h3
      have hN0 : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
      have hp' : 0 < 1 / p := by positivity
      have h5 : jb y ^ (-(γ + 1)) ≤ jb y ^ (-γ + 1 / p) :=
        Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
      exact h4.trans (mul_le_mul_of_nonneg_left h5 hN0)

/-- A.e. pointwise bounds for `r ∈ X_γ`: `|r| ≤ ‖r‖⟨y⟩^{-γ}`, `|r'| ≤ ‖r‖⟨y⟩^{-γ+1/p}`. -/
theorem c08_aux_X_ae_bound {p γ : ℝ} (hp : 0 < p) {r : ℝ → ℝ} (hr : r ∈ X_gamma p γ) :
    ∀ᵐ y ∂(volume : Measure ℝ), |r y| ≤ xNorm p γ r * jb y ^ (-γ) ∧
      |deriv r y| ≤ xNorm p γ r * jb y ^ (-γ + 1 / p) := by
  have hfin := hr.2
  unfold X_gamma_norm at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have hx : xNorm p γ r = _ := ENNReal.toReal_add h1.ne h2.ne
  set E1 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv r) y‖))) (volume.restrict (Ici 0))
  set E2 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0))
  have hN1 : E1.toReal ≤ xNorm p γ r := by rw [hx]; linarith [ENNReal.toReal_nonneg (a := E2)]
  have hN2 : E2.toReal ≤ xNorm p γ r := by rw [hx]; linarith [ENNReal.toReal_nonneg (a := E1)]
  apply c08_aux_ae_of_halflines
  · filter_upwards [c08_aux_ae_le_essSup_toReal h1] with y hy
    have hj := c08_aux_jb_pos y
    have hg := Real.rpow_pos_of_pos hj γ
    have hw := Real.rpow_pos_of_pos hj (-1 / p)
    have hw2 := Real.rpow_pos_of_pos hj (-2 / p)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at hy
    have a0 := abs_nonneg (r y); have a1 := abs_nonneg (deriv r y)
    have a2 := abs_nonneg (deriv (deriv r) y)
    have t2 := mul_nonneg hg.le (mul_nonneg hw2.le a2)
    constructor
    · apply c08_aux_div_weight
      nlinarith [mul_nonneg hg.le (mul_nonneg hw.le a1)]
    · have : jb y ^ (γ - 1 / p) * |deriv r y| ≤ xNorm p γ r := by
        rw [sub_eq_add_neg, Real.rpow_add hj, show -(1 / p) = -1 / p by ring]
        nlinarith [mul_nonneg hg.le a0]
      have := c08_aux_div_weight this
      rwa [show -(γ - 1 / p) = -γ + 1 / p by ring] at this
  · filter_upwards [c08_aux_ae_le_essSup_toReal h2] with y hy
    have hj := c08_aux_jb_pos y
    have hj1 := c08_aux_one_le_jb y
    have hg := Real.rpow_pos_of_pos hj γ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at hy
    have a0 := abs_nonneg (r y); have a1 := abs_nonneg (deriv r y)
    have a2 := abs_nonneg (deriv (deriv r) y)
    have t2 : 0 ≤ jb y ^ γ * (jb y ^ (2 : ℕ) * |deriv (deriv r) y|) := by positivity
    constructor
    · apply c08_aux_div_weight
      nlinarith [mul_nonneg hg.le (mul_nonneg hj.le a1)]
    · have h3 : jb y ^ (γ + 1) * |deriv r y| ≤ xNorm p γ r := by
        rw [Real.rpow_add hj, Real.rpow_one]
        nlinarith [mul_nonneg hg.le a0]
      have h4 := c08_aux_div_weight h3
      have hN0 : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg
      have hp' : 0 < 1 / p := by positivity
      have h5 : jb y ^ (-(γ + 1)) ≤ jb y ^ (-γ + 1 / p) :=
        Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
      exact h4.trans (mul_le_mul_of_nonneg_left h5 hN0)

/-- `⟨y⟩^{-γ} → 0` at infinity for `γ > 0`. -/
theorem c08_aux_jb_rpow_tendsto {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun y => jb y ^ (-γ)) (cocompact ℝ) (nhds 0) := by
  have hj : Tendsto jb (cocompact ℝ) atTop := by
    refine tendsto_atTop_mono (fun y => ?_) tendsto_norm_cocompact_atTop
    rw [Real.norm_eq_abs]; unfold jb
    calc |y| = Real.sqrt (y ^ 2) := (Real.sqrt_sq_eq_abs y).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  exact (tendsto_rpow_neg_atTop hγ).comp hj

/-- A function bounded by `N ⟨y⟩^{-γ}` (`γ > 0`) tends to `0` at infinity. -/
theorem c08_aux_tendsto_of_bound {f : ℝ → ℝ} {N γ : ℝ} (hγ : 0 < γ)
    (h : ∀ y, |f y| ≤ N * jb y ^ (-γ)) : Tendsto f (cocompact ℝ) (nhds 0) := by
  have h2 : Tendsto (fun y => N * jb y ^ (-γ)) (cocompact ℝ) (nhds 0) := by
    simpa using (c08_aux_jb_rpow_tendsto hγ).const_mul N
  exact squeeze_zero_norm (fun y => by rw [Real.norm_eq_abs]; exact h y) h2

/-- Integrability, `L¹` bound and sup bound from a pointwise a.e. bound `N ⟨y⟩^{-a}`, `a > 1`. -/
theorem c08_aux_L1_Linf_of_bound {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) {N a : ℝ}
    (ha : 1 < a) (hN : 0 ≤ N) (h : ∀ᵐ y ∂(volume : Measure ℝ), |f y| ≤ N * jb y ^ (-a)) :
    Integrable f ∧ MemLp f ⊤ volume ∧
      (∫ x, |f x|) ≤ N * ∫ x, jb x ^ (-a) ∧ (eLpNorm f ⊤ volume).toReal ≤ N := by
  have hI := c08_aux_jb_rpow_integrable a ha
  have hb : ∀ᵐ y ∂(volume : Measure ℝ), ‖f y‖ ≤ N := by
    filter_upwards [h] with y hy
    rw [Real.norm_eq_abs]
    refine hy.trans ?_
    have : jb y ^ (-a) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by linarith)
    nlinarith
  have hint : Integrable f := (hI.const_mul N).mono' hf (by
    filter_upwards [h] with y hy; rwa [Real.norm_eq_abs])
  refine ⟨hint, memLp_top_of_bound hf N hb, ?_, ?_⟩
  · rw [← integral_const_mul]
    exact integral_mono_ae hint.abs (hI.const_mul N) h
  · rw [eLpNorm_exponent_top hf]
    exact ENNReal.toReal_le_of_le_ofReal hN (eLpNormEssSup_le_of_ae_bound hb)

/-- Essential suprema do not increase under composition with `ψ`, when `ψ` has a differentiable
left inverse `φ` (so `ψ`-preimages of null sets are null) and `ψ` maps `S` into `S`. -/
theorem c08_aux_essSup_comp_le {φ ψ : ℝ → ℝ} (hφ : Differentiable ℝ φ)
    (hinv : ∀ y, φ (ψ y) = y) {S : Set ℝ} (hSm : MeasurableSet S) (hS : ∀ y ∈ S, ψ y ∈ S)
    (g : ℝ → ℝ≥0∞) :
    essSup (fun y => g (ψ y)) (volume.restrict S) ≤ essSup g (volume.restrict S) := by
  set E := essSup g (volume.restrict S)
  have h1 : ∀ᵐ x ∂(volume.restrict S), g x ≤ E := ENNReal.ae_le_essSup g
  rw [ae_restrict_iff' hSm, ae_iff] at h1
  have hB : volume (φ '' {x | ¬(x ∈ S → g x ≤ E)}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ hφ.differentiableOn h1
  refine essSup_le_of_ae_le E ?_
  rw [EventuallyLE, ae_restrict_iff' hSm, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hB
  simp only [not_imp, Set.mem_ofPred_eq] at hy
  exact ⟨ψ y, by simp only [not_imp, Set.mem_ofPred_eq]; exact ⟨hS y hy.1, hy.2⟩, hinv y⟩

/-- Products of locally Lipschitz real functions are locally Lipschitz. -/
theorem c08_aux_locallyLipschitz_mul {f g : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g) : LocallyLipschitz (fun x => f x * g x) := by
  have hm : LocallyLipschitz (fun q : ℝ × ℝ => q.1 * q.2) :=
    (contDiff_mul (𝕜 := ℝ) (n := 1)).locallyLipschitz
  exact LocallyLipschitz.comp (f := fun q : ℝ × ℝ => q.1 * q.2) (g := fun x => (f x, g x))
    hm (hf.prodMk hg)

/-- `jb y ^ s ≤ 2^{|s|} jb x ^ s` when `⟨y⟩` and `⟨x⟩` are comparable within a factor `2`. -/
theorem c08_aux_jb_rpow_compare {x y : ℝ} (h1 : jb y ≤ 2 * jb x) (h2 : jb x ≤ 2 * jb y) (s : ℝ) :
    jb y ^ s ≤ 2 ^ |s| * jb x ^ s := by
  have hx := c08_aux_jb_pos x
  have hy := c08_aux_jb_pos y
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs, ← Real.mul_rpow (by norm_num) hx.le]
    exact Real.rpow_le_rpow hy.le h1 hs
  · rw [abs_of_nonpos hs]
    have := c08_aux_rpow_neg_le_of_le (A := jb x) (B := jb y) (b := -s) hx (by linarith) h2
    simpa using this

/-- The `X_γ` integrand on `y ≥ 0`. -/
def c08_aux_I1 (p γ : ℝ) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  jb y ^ γ * (‖u y‖ + jb y ^ (-1 / p) * ‖deriv u y‖ + jb y ^ (-2 / p) * ‖deriv (deriv u) y‖)

/-- The `X_γ` integrand on `y ≤ 0`. -/
def c08_aux_I2 (_p γ : ℝ) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  jb y ^ γ * (‖u y‖ + jb y * ‖deriv u y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv u) y‖)

/-- `X_γ` norm bound from pointwise comparisons of integrands through a map `ψ` with differentiable
left inverse, preserving both half-lines. -/
theorem c08_aux_X_norm_comp_le {p γ K : ℝ} (hK : 0 ≤ K) {φ ψ : ℝ → ℝ} (hφ : Differentiable ℝ φ)
    (hinv : ∀ y, φ (ψ y) = y) (hpos : ∀ y, 0 ≤ y → 0 ≤ ψ y) (hneg : ∀ y, y ≤ 0 → ψ y ≤ 0)
    {f r : ℝ → ℝ}
    (h1 : ∀ y, 0 ≤ y → c08_aux_I1 p γ f y ≤ K * c08_aux_I1 p γ r (ψ y))
    (h2 : ∀ y, y ≤ 0 → c08_aux_I2 p γ f y ≤ K * c08_aux_I2 p γ r (ψ y)) :
    X_gamma_norm p γ f ≤ ENNReal.ofReal K * X_gamma_norm p γ r := by
  unfold X_gamma_norm
  rw [mul_add]
  gcongr
  · calc _ ≤ essSup (fun y => ENNReal.ofReal K * ENNReal.ofReal (c08_aux_I1 p γ r (ψ y)))
          (volume.restrict (Ici 0)) := by
          refine essSup_mono_ae ((ae_restrict_iff' measurableSet_Ici).2
            (Eventually.of_forall fun y hy => ?_))
          simp only
          rw [← ENNReal.ofReal_mul hK]
          exact ENNReal.ofReal_le_ofReal (h1 y hy)
      _ = ENNReal.ofReal K * essSup (fun y => ENNReal.ofReal (c08_aux_I1 p γ r (ψ y)))
          (volume.restrict (Ici 0)) := ENNReal.essSup_const_mul
      _ ≤ _ := by
          gcongr
          exact c08_aux_essSup_comp_le hφ hinv measurableSet_Ici hpos
            (fun x => ENNReal.ofReal (c08_aux_I1 p γ r x))
  · calc _ ≤ essSup (fun y => ENNReal.ofReal K * ENNReal.ofReal (c08_aux_I2 p γ r (ψ y)))
          (volume.restrict (Iic 0)) := by
          refine essSup_mono_ae ((ae_restrict_iff' measurableSet_Iic).2
            (Eventually.of_forall fun y hy => ?_))
          simp only
          rw [← ENNReal.ofReal_mul hK]
          exact ENNReal.ofReal_le_ofReal (h2 y hy)
      _ = ENNReal.ofReal K * essSup (fun y => ENNReal.ofReal (c08_aux_I2 p γ r (ψ y)))
          (volume.restrict (Iic 0)) := ENNReal.essSup_const_mul
      _ ≤ _ := by
          gcongr
          exact c08_aux_essSup_comp_le hφ hinv measurableSet_Iic hneg
            (fun x => ENNReal.ofReal (c08_aux_I2 p γ r x))

/-- Composition `r ∘ ψ` with a `C²` diffeomorphism `ψ` which is the identity on `(-∞,1]`,
preserves `[0,∞)`, has `0 < ψ' ≤ 2`, `|ψ''| ≤ B` and `⟨ψ y⟩ ≈ ⟨y⟩`: it maps `X_γ` into itself. -/
theorem c08_aux_comp_X {p γ B : ℝ} (hp : 0 < p) (hB : 0 ≤ B) {φ ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hφ : Differentiable ℝ φ)
    (hinv : ∀ y, φ (ψ y) = y) (hinv2 : ∀ y, ψ (φ y) = y) (hid : ∀ y ≤ 1, ψ y = y)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ ψ y)
    (hd1 : ∀ y, 0 < deriv ψ y ∧ deriv ψ y ≤ 2) (hd2 : ∀ y, |deriv (deriv ψ) y| ≤ B)
    (hjb : ∀ y, jb y ≤ 2 * jb (ψ y) ∧ jb (ψ y) ≤ 2 * jb y)
    {r : ℝ → ℝ} (hr : r ∈ X_gamma p γ) :
    (fun y => r (ψ y)) ∈ X_gamma p γ ∧
      xNorm p γ (fun y => r (ψ y)) ≤ ((4 + B) * 2 ^ (|γ| + 2 / p)) * xNorm p γ r := by
  set f : ℝ → ℝ := fun y => r (ψ y) with hfdef
  set K := (4 + B) * 2 ^ (|γ| + 2 / p) with hKdef
  have hK1 : 1 ≤ K := by
    have : (1:ℝ) ≤ 2 ^ (|γ| + 2 / p) := Real.one_le_rpow (by norm_num) (by positivity)
    rw [hKdef]; nlinarith
  have hK0 : 0 ≤ K := by linarith
  have hrC : ContDiff ℝ 1 r := hr.1.1
  have hrd : Differentiable ℝ r := hrC.differentiable (by norm_num)
  obtain ⟨hψd, -, hψ'C⟩ := contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) ψ from hψ)
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ'C.differentiable (by norm_num)
  have hfcomp : f = r ∘ ψ := rfl
  have hf' : deriv f = fun y => deriv r (ψ y) * deriv ψ y := by
    ext y; rw [hfcomp, deriv_comp y (hrd _) (hψd y)]
  -- second derivative bound
  have hf'' : ∀ y, |deriv (deriv f) y| ≤
      |deriv (deriv r) (ψ y)| * deriv ψ y ^ 2 + |deriv r (ψ y)| * |deriv (deriv ψ) y| := by
    intro y
    rw [hf']
    by_cases hdr : DifferentiableAt ℝ (deriv r) (ψ y)
    · have hc : HasDerivAt (fun z => deriv r (ψ z)) (deriv (deriv r) (ψ y) * deriv ψ y) y :=
        hdr.hasDerivAt.comp y (hψd y).hasDerivAt
      have hm : HasDerivAt (fun z => deriv r (ψ z) * deriv ψ z)
          (deriv (deriv r) (ψ y) * deriv ψ y * deriv ψ y + deriv r (ψ y) * deriv (deriv ψ) y) y :=
        hc.mul (hψ'd y).hasDerivAt
      rw [hm.deriv]
      have hp1 := (hd1 y).1
      calc _ ≤ |deriv (deriv r) (ψ y) * deriv ψ y * deriv ψ y| +
            |deriv r (ψ y) * deriv (deriv ψ) y| := abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp1]; ring
    · have hnd : ¬ DifferentiableAt ℝ (fun z => deriv r (ψ z) * deriv ψ z) y := by
        intro h
        have h2 : DifferentiableAt ℝ (fun z => deriv r (ψ z) * deriv ψ z / deriv ψ z) y :=
          h.div (hψ'd y) (hd1 y).1.ne'
        have h3 : (fun z => deriv r (ψ z) * deriv ψ z / deriv ψ z) = fun z => deriv r (ψ z) := by
          ext z; rw [mul_div_assoc, div_self (hd1 z).1.ne', mul_one]
        rw [h3] at h2
        apply hdr
        have h4 : DifferentiableAt ℝ ((fun z => deriv r (ψ z)) ∘ φ) (ψ y) :=
          DifferentiableAt.comp (ψ y) (by rw [hinv y]; exact h2) (hφ _)
        have h5 : ((fun z => deriv r (ψ z)) ∘ φ) = deriv r := by
          ext z; simp [hinv2 z]
        rwa [h5] at h4
      rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
      positivity
  -- agreement on `(-∞, 1)`
  have hloc : ∀ y, y < 1 → f =ᶠ[nhds y] r := fun y hy =>
    Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => by
      simp only [hfdef]; rw [hid z (le_of_lt hz)])
  have hloc' : ∀ y, y < 1 → deriv f =ᶠ[nhds y] deriv r := fun y hy =>
    Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => (hloc z hz).deriv_eq)
  have hcmp : ∀ y : ℝ, ∀ s : ℝ, |s| ≤ |γ| + 2 / p →
      jb y ^ s ≤ 2 ^ (|γ| + 2 / p) * jb (ψ y) ^ s := by
    intro y s hs
    have h := c08_aux_jb_rpow_compare (hjb y).1 (hjb y).2 s
    have h2 : (2:ℝ) ^ |s| ≤ 2 ^ (|γ| + 2 / p) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
    have h3 := Real.rpow_pos_of_pos (c08_aux_jb_pos (ψ y)) s
    exact h.trans (mul_le_mul_of_nonneg_right h2 h3.le)
  have hp1 : 0 < 1 / p := by positivity
  have hfnorm := c08_aux_X_norm_comp_le (p := p) (γ := γ) hK0 hφ hinv hnn
    (fun y hy => by rw [hid y (by linarith)]; exact hy) (f := f) (r := r) ?_ ?_
  · have hfin : ENNReal.ofReal K * X_gamma_norm p γ r < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hr.2
    refine ⟨⟨⟨hrC.comp (hψ.of_le (by norm_num)), ?_⟩, lt_of_le_of_lt hfnorm hfin⟩, ?_⟩
    · rw [hf']
      exact c08_aux_locallyLipschitz_mul
        (LocallyLipschitz.comp (f := deriv r) (g := ψ) hr.1.2 ((hψ.of_le (by norm_num)).locallyLipschitz))
        hψ'C.locallyLipschitz
    · unfold xNorm
      calc (X_gamma_norm p γ f).toReal ≤ (ENNReal.ofReal K * X_gamma_norm p γ r).toReal :=
            ENNReal.toReal_mono hfin.ne hfnorm
        _ = K * (X_gamma_norm p γ r).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]
  · -- positive half-line
    intro y hy
    set x := ψ y
    set L := (2:ℝ) ^ (|γ| + 2 / p)
    have hL : 1 ≤ L := Real.one_le_rpow (by norm_num) (by positivity)
    have hjy := c08_aux_jb_pos y
    have hjx := c08_aux_jb_pos x
    have hjy1 := c08_aux_one_le_jb y
    have hp2 : 0 < 2 / p := by positivity
    have hp12 : 1 / p ≤ 2 / p := by rw [div_le_div_iff_of_pos_right hp]; norm_num
    -- weights
    have w0 : jb y ^ γ ≤ L * jb x ^ γ := hcmp y γ (by linarith [abs_nonneg γ])
    have w1 : jb y ^ γ * jb y ^ (-1 / p) ≤ L * (jb x ^ γ * jb x ^ (-1 / p)) := by
      rw [← Real.rpow_add hjy, ← Real.rpow_add hjx]
      apply hcmp
      have : |-1 / p| = 1 / p := by rw [abs_div, abs_neg, abs_one, abs_of_pos hp]
      calc |γ + -1 / p| ≤ |γ| + |-1 / p| := abs_add_le _ _
        _ ≤ _ := by rw [this]; linarith
    have w2 : jb y ^ γ * jb y ^ (-2 / p) ≤ L * (jb x ^ γ * jb x ^ (-2 / p)) := by
      rw [← Real.rpow_add hjy, ← Real.rpow_add hjx]
      apply hcmp
      have : |-2 / p| = 2 / p := by rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_pos hp]
      calc |γ + -2 / p| ≤ |γ| + |-2 / p| := abs_add_le _ _
        _ = _ := by rw [this]
    have w21 : jb y ^ (-2 / p) ≤ jb y ^ (-1 / p) :=
      Real.rpow_le_rpow_of_exponent_le hjy1 (by
        rw [div_le_div_iff_of_pos_right hp]; norm_num)
    have hg0 : 0 < jb y ^ γ := Real.rpow_pos_of_pos hjy γ
    have hw1p : 0 < jb y ^ (-1 / p) := Real.rpow_pos_of_pos hjy _
    have hw2p : 0 < jb y ^ (-2 / p) := Real.rpow_pos_of_pos hjy _
    -- derivative values
    have e1 : ‖deriv f y‖ ≤ 2 * ‖deriv r x‖ := by
      rw [hf', Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (hd1 y).1]
      nlinarith [abs_nonneg (deriv r x), (hd1 y).2]
    have e2 : ‖deriv (deriv f) y‖ ≤ 4 * ‖deriv (deriv r) x‖ + B * ‖deriv r x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      refine (hf'' y).trans ?_
      have hsq : deriv ψ y ^ 2 ≤ 4 := by nlinarith [(hd1 y).1, (hd1 y).2]
      have := abs_nonneg (deriv (deriv r) x)
      have := abs_nonneg (deriv r x)
      have := hd2 y
      have k1 : |deriv (deriv r) x| * deriv ψ y ^ 2 ≤ |deriv (deriv r) x| * 4 :=
        mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
      have k2 : |deriv r x| * |deriv (deriv ψ) y| ≤ |deriv r x| * B :=
        mul_le_mul_of_nonneg_left (hd2 y) (abs_nonneg _)
      linarith
    unfold c08_aux_I1
    set A0 := ‖r x‖; set A1 := ‖deriv r x‖; set A2 := ‖deriv (deriv r) x‖
    have a0 : 0 ≤ A0 := norm_nonneg _
    have a1 : 0 ≤ A1 := norm_nonneg _
    have a2 : 0 ≤ A2 := norm_nonneg _
    set Y0 := jb x ^ γ; set Y1 := jb x ^ γ * jb x ^ (-1 / p); set Y2 := jb x ^ γ * jb x ^ (-2 / p)
    have y1 : 0 ≤ Y1 := by positivity
    have y2 : 0 ≤ Y2 := by positivity
    have t0 : jb y ^ γ * ‖f y‖ ≤ L * (Y0 * A0) := by
      calc jb y ^ γ * ‖f y‖ ≤ (L * Y0) * A0 := mul_le_mul_of_nonneg_right w0 a0
        _ = _ := by ring
    have t1 : jb y ^ γ * (jb y ^ (-1 / p) * ‖deriv f y‖) ≤ 2 * L * (Y1 * A1) := by
      calc jb y ^ γ * (jb y ^ (-1 / p) * ‖deriv f y‖) =
            (jb y ^ γ * jb y ^ (-1 / p)) * ‖deriv f y‖ := by ring
        _ ≤ (L * Y1) * (2 * A1) := mul_le_mul w1 e1 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hB1 : jb y ^ γ * jb y ^ (-2 / p) ≤ L * Y1 :=
      (mul_le_mul_of_nonneg_left w21 hg0.le).trans w1
    have t2 : jb y ^ γ * (jb y ^ (-2 / p) * ‖deriv (deriv f) y‖) ≤
        4 * L * (Y2 * A2) + B * L * (Y1 * A1) := by
      calc jb y ^ γ * (jb y ^ (-2 / p) * ‖deriv (deriv f) y‖) =
            (jb y ^ γ * jb y ^ (-2 / p)) * ‖deriv (deriv f) y‖ := by ring
        _ ≤ (jb y ^ γ * jb y ^ (-2 / p)) * (4 * A2 + B * A1) :=
            mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = 4 * ((jb y ^ γ * jb y ^ (-2 / p)) * A2) + B * ((jb y ^ γ * jb y ^ (-2 / p)) * A1) := by
            ring
        _ ≤ 4 * ((L * Y2) * A2) + B * ((L * Y1) * A1) := by
            have k1 := mul_le_mul_of_nonneg_right w2 a2
            have k2 := mul_le_mul_of_nonneg_right hB1 a1
            have k3 := mul_le_mul_of_nonneg_left k2 hB
            linarith
        _ = _ := by ring
    have hLA : 0 ≤ L * (Y0 * A0) := by positivity
    have hLB : 0 ≤ L * (Y1 * A1) := by positivity
    have hLC : 0 ≤ L * (Y2 * A2) := by positivity
    calc jb y ^ γ * (‖f y‖ + jb y ^ (-1 / p) * ‖deriv f y‖ + jb y ^ (-2 / p) * ‖deriv (deriv f) y‖)
        = jb y ^ γ * ‖f y‖ + jb y ^ γ * (jb y ^ (-1 / p) * ‖deriv f y‖) +
          jb y ^ γ * (jb y ^ (-2 / p) * ‖deriv (deriv f) y‖) := by ring
      _ ≤ (4 + B) * L * (Y0 * A0 + Y1 * A1 + Y2 * A2) := by
          have := mul_le_mul_of_nonneg_left hLB hB
          nlinarith
      _ = _ := by simp only [hKdef, Y0, Y1, Y2]; ring
  · -- negative half-line
    intro y hy
    have hy1 : y < 1 := by linarith
    rw [hid y hy1.le]
    unfold c08_aux_I2
    rw [(hloc y hy1).eq_of_nhds, (hloc y hy1).deriv_eq, (hloc' y hy1).deriv_eq]
    have : 0 ≤ jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖) := by
      have := c08_aux_jb_pos y; have := Real.rpow_pos_of_pos this γ; positivity
    nlinarith

/-- The `Y_γ` integrand on `y ≥ 0`. -/
def c08_aux_J1 (p γ : ℝ) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  jb y ^ γ * (‖u y‖ + jb y ^ (-1 / p) * ‖deriv u y‖)

/-- The `Y_γ` integrand on `y ≤ 0`. -/
def c08_aux_J2 (γ : ℝ) (u : ℝ → ℝ) (y : ℝ) : ℝ :=
  jb y ^ γ * (‖u y‖ + jb y * ‖deriv u y‖)

/-- `Y_γ` analogue of `c08_aux_X_norm_comp_le`. -/
theorem c08_aux_Y_norm_comp_le {p γ K : ℝ} (hK : 0 ≤ K) {φ ψ : ℝ → ℝ} (hφ : Differentiable ℝ φ)
    (hinv : ∀ y, φ (ψ y) = y) (hpos : ∀ y, 0 ≤ y → 0 ≤ ψ y) (hneg : ∀ y, y ≤ 0 → ψ y ≤ 0)
    {f G : ℝ → ℝ}
    (h1 : ∀ y, 0 ≤ y → c08_aux_J1 p γ f y ≤ K * c08_aux_J1 p γ G (ψ y))
    (h2 : ∀ y, y ≤ 0 → c08_aux_J2 γ f y ≤ K * c08_aux_J2 γ G (ψ y)) :
    Y_gamma_norm p γ f ≤ ENNReal.ofReal K * Y_gamma_norm p γ G := by
  unfold Y_gamma_norm
  rw [mul_add]
  gcongr
  · calc _ ≤ essSup (fun y => ENNReal.ofReal K * ENNReal.ofReal (c08_aux_J1 p γ G (ψ y)))
          (volume.restrict (Ici 0)) := by
          refine essSup_mono_ae ((ae_restrict_iff' measurableSet_Ici).2
            (Eventually.of_forall fun y hy => ?_))
          simp only
          rw [← ENNReal.ofReal_mul hK]
          exact ENNReal.ofReal_le_ofReal (h1 y hy)
      _ = ENNReal.ofReal K * essSup (fun y => ENNReal.ofReal (c08_aux_J1 p γ G (ψ y)))
          (volume.restrict (Ici 0)) := ENNReal.essSup_const_mul
      _ ≤ _ := by
          gcongr
          exact c08_aux_essSup_comp_le hφ hinv measurableSet_Ici hpos
            (fun x => ENNReal.ofReal (c08_aux_J1 p γ G x))
  · calc _ ≤ essSup (fun y => ENNReal.ofReal K * ENNReal.ofReal (c08_aux_J2 γ G (ψ y)))
          (volume.restrict (Iic 0)) := by
          refine essSup_mono_ae ((ae_restrict_iff' measurableSet_Iic).2
            (Eventually.of_forall fun y hy => ?_))
          simp only
          rw [← ENNReal.ofReal_mul hK]
          exact ENNReal.ofReal_le_ofReal (h2 y hy)
      _ = ENNReal.ofReal K * essSup (fun y => ENNReal.ofReal (c08_aux_J2 γ G (ψ y)))
          (volume.restrict (Iic 0)) := ENNReal.essSup_const_mul
      _ ≤ _ := by
          gcongr
          exact c08_aux_essSup_comp_le hφ hinv measurableSet_Iic hneg
            (fun x => ENNReal.ofReal (c08_aux_J2 γ G x))

/-- Weighted composition `a · (G ∘ ψ)` maps `Y_γ` into itself (same hypotheses on `ψ` as
`c08_aux_comp_X`, `a` a bounded `C¹` positive weight with bounded derivative, `a = 1` on
`(-∞,1)`). -/
theorem c08_aux_comp_Y {p γ A : ℝ} (hp : 0 < p) (hA : 0 ≤ A) {φ ψ a : ℝ → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hφ : Differentiable ℝ φ)
    (hinv : ∀ y, φ (ψ y) = y) (hinv2 : ∀ y, ψ (φ y) = y) (hid : ∀ y ≤ 1, ψ y = y)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ ψ y) (hd1 : ∀ y, 0 < deriv ψ y ∧ deriv ψ y ≤ 2)
    (hjb : ∀ y, jb y ≤ 2 * jb (ψ y) ∧ jb (ψ y) ≤ 2 * jb y)
    (ha : ContDiff ℝ 1 a) (ha0 : ∀ y, 0 < a y) (ha1 : ∀ y, a y ≤ A) (ha' : ∀ y, |deriv a y| ≤ A)
    (haid : ∀ y < 1, a y = 1)
    {G : ℝ → ℝ} (hG : G ∈ Y_gamma p γ) :
    (fun y => a y * G (ψ y)) ∈ Y_gamma p γ ∧
      yNorm p γ (fun y => a y * G (ψ y)) ≤ ((2 * A + 1) * 2 ^ (|γ| + 1 / p)) * yNorm p γ G := by
  set f : ℝ → ℝ := fun y => a y * G (ψ y) with hfdef
  set K := (2 * A + 1) * 2 ^ (|γ| + 1 / p) with hKdef
  set L := (2:ℝ) ^ (|γ| + 1 / p) with hLdef
  have hL : 1 ≤ L := Real.one_le_rpow (by norm_num) (by positivity)
  have hK1 : 1 ≤ K := by rw [hKdef]; nlinarith
  have hK0 : 0 ≤ K := by linarith
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have had : Differentiable ℝ a := ha.differentiable (by norm_num)
  -- derivative bound
  have hf' : ∀ y, |deriv f y| ≤ |deriv a y| * |G (ψ y)| + a y * (|deriv G (ψ y)| * deriv ψ y) := by
    intro y
    by_cases hdG : DifferentiableAt ℝ G (ψ y)
    · have hc : HasDerivAt (fun z => G (ψ z)) (deriv G (ψ y) * deriv ψ y) y :=
        hdG.hasDerivAt.comp y (hψd y).hasDerivAt
      have hm : HasDerivAt f (deriv a y * G (ψ y) + a y * (deriv G (ψ y) * deriv ψ y)) y :=
        (had y).hasDerivAt.mul hc
      rw [hm.deriv]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (ha0 y), abs_of_pos (hd1 y).1]
    · have hnd : ¬ DifferentiableAt ℝ f y := by
        intro h
        have h2 : DifferentiableAt ℝ (fun z => f z / a z) y := h.div (had y) (ha0 y).ne'
        have h3 : (fun z => f z / a z) = fun z => G (ψ z) := by
          ext z; simp only [hfdef]; field_simp [(ha0 z).ne']
        rw [h3] at h2
        apply hdG
        have h4 : DifferentiableAt ℝ ((fun z => G (ψ z)) ∘ φ) (ψ y) :=
          DifferentiableAt.comp (ψ y) (by rw [hinv y]; exact h2) (hφ _)
        have h5 : ((fun z => G (ψ z)) ∘ φ) = G := by ext z; simp [hinv2 z]
        rwa [h5] at h4
      rw [deriv_zero_of_not_differentiableAt hnd, abs_zero]
      have := ha0 y; have := (hd1 y).1
      positivity
  have hloc : ∀ y, y < 1 → f =ᶠ[nhds y] G := fun y hy =>
    Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => by
      simp only [hfdef]; rw [hid z (le_of_lt hz), haid z hz, one_mul])
  have hcmp : ∀ y : ℝ, ∀ s : ℝ, |s| ≤ |γ| + 1 / p → jb y ^ s ≤ L * jb (ψ y) ^ s := by
    intro y s hs
    have h := c08_aux_jb_rpow_compare (hjb y).1 (hjb y).2 s
    have h2 : (2:ℝ) ^ |s| ≤ L := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs
    have h3 := Real.rpow_pos_of_pos (c08_aux_jb_pos (ψ y)) s
    exact h.trans (mul_le_mul_of_nonneg_right h2 h3.le)
  have hp1 : 0 < 1 / p := by positivity
  have hfnorm := c08_aux_Y_norm_comp_le (p := p) (γ := γ) hK0 hφ hinv hnn
    (fun y hy => by rw [hid y (by linarith)]; exact hy) (f := f) (G := G) ?_ ?_
  · have hfin : ENNReal.ofReal K * Y_gamma_norm p γ G < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG.2
    refine ⟨⟨?_, lt_of_le_of_lt hfnorm hfin⟩, ?_⟩
    · exact c08_aux_locallyLipschitz_mul ha.locallyLipschitz
        (LocallyLipschitz.comp (f := G) (g := ψ) hG.1 hψ.locallyLipschitz)
    · unfold yNorm
      calc (Y_gamma_norm p γ f).toReal ≤ (ENNReal.ofReal K * Y_gamma_norm p γ G).toReal :=
            ENNReal.toReal_mono hfin.ne hfnorm
        _ = K * (Y_gamma_norm p γ G).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]
  · intro y hy
    set x := ψ y
    have hjy := c08_aux_jb_pos y
    have hjx := c08_aux_jb_pos x
    have hjy1 := c08_aux_one_le_jb y
    have w0 : jb y ^ γ ≤ L * jb x ^ γ := hcmp y γ (by linarith [abs_nonneg γ])
    have w1 : jb y ^ γ * jb y ^ (-1 / p) ≤ L * (jb x ^ γ * jb x ^ (-1 / p)) := by
      rw [← Real.rpow_add hjy, ← Real.rpow_add hjx]
      apply hcmp
      have : |-1 / p| = 1 / p := by rw [abs_div, abs_neg, abs_one, abs_of_pos hp]
      calc |γ + -1 / p| ≤ |γ| + |-1 / p| := abs_add_le _ _
        _ = _ := by rw [this]
    have hw1 : jb y ^ (-1 / p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hjy1
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le)
    have hg0 : 0 < jb y ^ γ := Real.rpow_pos_of_pos hjy γ
    have hw1p : 0 < jb y ^ (-1 / p) := Real.rpow_pos_of_pos hjy _
    unfold c08_aux_J1
    set A0 := ‖G x‖; set A1 := ‖deriv G x‖
    have a0 : 0 ≤ A0 := norm_nonneg _
    have a1 : 0 ≤ A1 := norm_nonneg _
    set Y0 := jb x ^ γ; set Y1 := jb x ^ γ * jb x ^ (-1 / p)
    have y0 : 0 ≤ Y0 := (Real.rpow_pos_of_pos hjx _).le
    have y1 : 0 ≤ Y1 := by positivity
    have e0 : ‖f y‖ ≤ A * A0 := by
      simp only [hfdef]
      rw [norm_mul, Real.norm_eq_abs (a y), abs_of_pos (ha0 y)]
      exact mul_le_mul_of_nonneg_right (ha1 y) a0
    have e1 : ‖deriv f y‖ ≤ A * A0 + 2 * A * A1 := by
      rw [Real.norm_eq_abs]
      refine (hf' y).trans ?_
      have k1 : |deriv a y| * |G x| ≤ A * A0 := mul_le_mul (ha' y) le_rfl (abs_nonneg _) hA
      have k2 : |deriv G x| * deriv ψ y ≤ A1 * 2 :=
        mul_le_mul_of_nonneg_left (hd1 y).2 (abs_nonneg _)
      have k3 : a y * (|deriv G x| * deriv ψ y) ≤ A * (A1 * 2) :=
        mul_le_mul (ha1 y) k2 (by have := (hd1 y).1; positivity) hA
      linarith
    have t0 : jb y ^ γ * ‖f y‖ ≤ A * L * (Y0 * A0) := by
      calc jb y ^ γ * ‖f y‖ ≤ (L * Y0) * (A * A0) := mul_le_mul w0 e0 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have t1 : jb y ^ γ * (jb y ^ (-1 / p) * ‖deriv f y‖) ≤ A * L * (Y0 * A0) + 2 * A * L * (Y1 * A1) := by
      calc jb y ^ γ * (jb y ^ (-1 / p) * ‖deriv f y‖) ≤ jb y ^ γ * (jb y ^ (-1 / p) * (A * A0 + 2 * A * A1)) := by
            gcongr
        _ = (jb y ^ γ * jb y ^ (-1 / p)) * (A * A0) + (jb y ^ γ * jb y ^ (-1 / p)) * (2 * A * A1) := by ring
        _ ≤ (L * Y0) * (A * A0) + (L * Y1) * (2 * A * A1) := by
            have k1 : jb y ^ γ * jb y ^ (-1 / p) ≤ L * Y0 :=
              (mul_le_mul_of_nonneg_left hw1 hg0.le).trans (by rw [mul_one]; exact w0)
            have hAA : 0 ≤ A * A0 := by positivity
            have hAB : 0 ≤ 2 * A * A1 := by positivity
            exact add_le_add (mul_le_mul_of_nonneg_right k1 hAA) (mul_le_mul_of_nonneg_right w1 hAB)
        _ = _ := by ring
    have hLA : 0 ≤ L * (Y0 * A0) := by positivity
    have hLB : 0 ≤ L * (Y1 * A1) := by positivity
    calc jb y ^ γ * (‖f y‖ + jb y ^ (-1 / p) * ‖deriv f y‖)
        = jb y ^ γ * ‖f y‖ + jb y ^ γ * (jb y ^ (-1 / p) * ‖deriv f y‖) := by ring
      _ ≤ (2 * A + 1) * L * (Y0 * A0 + Y1 * A1) := by
          have := mul_le_mul_of_nonneg_left hLA hA
          have := mul_le_mul_of_nonneg_left hLB hA
          nlinarith
      _ = _ := by simp only [hKdef, Y0, Y1]; ring
  · intro y hy
    have hy1 : y < 1 := by linarith
    rw [hid y hy1.le]
    unfold c08_aux_J2
    rw [(hloc y hy1).eq_of_nhds, (hloc y hy1).deriv_eq]
    have : 0 ≤ jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖) := by
      have := c08_aux_jb_pos y; have := Real.rpow_pos_of_pos this γ; positivity
    nlinarith

/-- Properties of the weight `(ψ')^{p+1}` used by `𝒱_ε`, `𝒱_ε⁻¹`. -/
theorem c08_aux_weight {p B : ℝ} (hp : 0 < p) (hp1 : p < 1) (hB : 0 ≤ B) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hid : ∀ y ≤ 1, ψ y = y) (hd1 : ∀ y, 0 < deriv ψ y ∧ deriv ψ y ≤ 2)
    (hd2 : ∀ y, |deriv (deriv ψ) y| ≤ B) :
    ContDiff ℝ 1 (fun y => deriv ψ y ^ (p + 1)) ∧ (∀ y, 0 < deriv ψ y ^ (p + 1)) ∧
    (∀ y, deriv ψ y ^ (p + 1) ≤ 4 + 4 * B) ∧
    (∀ y, |deriv (fun y => deriv ψ y ^ (p + 1)) y| ≤ 4 + 4 * B) ∧
    (∀ y < 1, deriv ψ y ^ (p + 1) = 1) := by
  obtain ⟨-, -, hψ'C⟩ := contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) ψ from hψ)
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ'C.differentiable (by norm_num)
  refine ⟨hψ'C.rpow_const_of_ne (fun x => (hd1 x).1.ne'), fun y => Real.rpow_pos_of_pos (hd1 y).1 _,
    fun y => ?_, fun y => ?_, fun y hy => ?_⟩
  · calc deriv ψ y ^ (p + 1) ≤ 2 ^ (p + 1) := Real.rpow_le_rpow (hd1 y).1.le (hd1 y).2 (by linarith)
      _ ≤ 2 ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ 4 + 4 * B := by norm_num; linarith
  · have h := ((hψ'd y).hasDerivAt.rpow_const (p := p + 1) (Or.inl (hd1 y).1.ne'))
    rw [h.deriv, show p + 1 - 1 = p by ring]
    have hpow : deriv ψ y ^ p ≤ 2 := by
      calc deriv ψ y ^ p ≤ 2 ^ p := Real.rpow_le_rpow (hd1 y).1.le (hd1 y).2 hp.le
        _ ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
        _ = 2 := Real.rpow_one 2
    have hpos : 0 < deriv ψ y ^ p := Real.rpow_pos_of_pos (hd1 y).1 p
    rw [abs_mul, abs_mul, abs_of_pos hpos, abs_of_pos (by linarith : (0:ℝ) < p + 1)]
    have := hd2 y
    have h1 : |deriv (deriv ψ) y| * (p + 1) ≤ B * 2 :=
      mul_le_mul this (by linarith) (by linarith) hB
    have h2 : |deriv (deriv ψ) y| * (p + 1) * deriv ψ y ^ p ≤ B * 2 * 2 :=
      mul_le_mul h1 hpow hpos.le (by positivity)
    linarith
  · have hloc : ψ =ᶠ[nhds y] id :=
      Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => hid z (le_of_lt hz))
    rw [hloc.deriv_eq, deriv_id, Real.one_rpow]

/-- `⟨·⟩` is `1`-Lipschitz. -/
theorem c08_aux_jb_lip (a b : ℝ) : |jb a - jb b| ≤ |a - b| := by
  have ha := c08_aux_jb_pos a
  have hb := c08_aux_jb_pos b
  have hsa : jb a ^ 2 = 1 + a ^ 2 := by unfold jb; rw [Real.sq_sqrt (by positivity)]
  have hsb : jb b ^ 2 = 1 + b ^ 2 := by unfold jb; rw [Real.sq_sqrt (by positivity)]
  have habs : |a| ≤ jb a := by
    unfold jb; calc |a| = Real.sqrt (a ^ 2) := (Real.sqrt_sq_eq_abs a).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hbbs : |b| ≤ jb b := by
    unfold jb; calc |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have key : |jb a - jb b| * (jb a + jb b) = |a - b| * |a + b| := by
    rw [← abs_of_pos (by linarith : 0 < jb a + jb b), ← abs_mul, ← abs_mul]
    congr 1; nlinarith
  have hab : |a + b| ≤ jb a + jb b := (abs_add_le a b).trans (by linarith)
  have hpos : 0 < jb a + jb b := by linarith
  by_contra h
  push Not at h
  have := mul_lt_mul_of_pos_right h hpos
  nlinarith [abs_nonneg (a - b)]

/-- Mean value bound on a segment. -/
theorem c08_aux_mvt_bound {g : ℝ → ℝ} {x y K : ℝ}
    (hd : ∀ ξ ∈ uIcc x y, DifferentiableAt ℝ g ξ) (hb : ∀ ξ ∈ uIcc x y, |deriv g ξ| ≤ K) :
    |g x - g y| ≤ K * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) hd
    (fun ξ hξ => by rw [Real.norm_eq_abs]; exact hb ξ hξ) (convex_uIcc x y)
    (right_mem_uIcc) (left_mem_uIcc)
  simpa [Real.norm_eq_abs] using this

/-- Elements of `Y_γ`, `γ > 1`, are integrable, with `|G| ≤ ‖G‖⟨y⟩^{-γ}` everywhere. -/
theorem c08_aux_Y_integrable {p γ : ℝ} (hp : 0 < p) (hγ : 1 < γ) {G : ℝ → ℝ}
    (hG : G ∈ Y_gamma p γ) :
    Integrable G ∧ ∀ y, |G y| ≤ yNorm p γ G * jb y ^ (-γ) := by
  have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
  have hb := c08_aux_Y_ae_bound hp hG
  have hGc : Continuous G := hG.1.continuous
  have hpt : ∀ y, |G y| ≤ yNorm p γ G * jb y ^ (-γ) := by
    have hw : Continuous (fun y => yNorm p γ G * jb y ^ (-γ)) := by
      apply continuous_const.mul
      exact (Real.continuous_sqrt.comp (by fun_prop)).rpow_const
        (fun y => Or.inl (c08_aux_jb_pos y).ne')
    have hae : ∀ᵐ y ∂(volume : Measure ℝ), |G y| ≤ yNorm p γ G * jb y ^ (-γ) := by
      filter_upwards [hb] with y hy; exact hy.1
    exact c08_aux_le_of_ae_halflines hGc.abs hw (ae_restrict_of_ae hae) (ae_restrict_of_ae hae)
  exact ⟨(c08_aux_L1_Linf_of_bound hGc.aestronglyMeasurable hγ hN (Eventually.of_forall hpt)).1,
    hpt⟩

/-- Homogeneity of the phase: `Φ₀(tξ) = t^{p+1} Φ₀(ξ)` for `t ≥ 0`. -/
theorem c08_aux_Phi0_scale (p t ξ : ℝ) (hp : 0 < p) (ht : 0 ≤ t) :
    Phi0 p (t * ξ) = t ^ (p + 1) * Phi0 p ξ := by
  unfold Phi0
  rw [abs_mul, abs_of_nonneg ht, Real.mul_rpow ht (abs_nonneg _),
    Real.rpow_add_one' ht (by linarith)]
  ring

/-- `|Ĝ(ξ)| ≤ ‖G‖_{L¹}`. -/
theorem c08_aux_norm_fourierT_le (G : ℝ → ℝ) (ξ : ℝ) :
    ‖fourierT (fun x => (G x : ℂ)) ξ‖ ≤ ∫ x, |G x| := by
  unfold fourierT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : ‖Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [this, mul_one]

/-- `Φ₀'(ξ) = |ξ|^p` for `ξ ≠ 0`. -/
theorem c08_aux_Phi0_hasDerivAt (p ξ : ℝ) (hp : 0 < p) (hξ : ξ ≠ 0) :
    HasDerivAt (Phi0 p) (|ξ| ^ p) ξ := by
  have hp1 : p + 1 ≠ 0 := by linarith
  rcases lt_or_gt_of_ne hξ with h | h
  · have hloc : (fun x => -((-x) ^ (p + 1)) / (p + 1)) =ᶠ[nhds ξ] Phi0 p :=
      Filter.eventually_of_mem (Iio_mem_nhds h) (fun x hx => by
        have hx' : x < 0 := hx
        show -((-x) ^ (p + 1)) / (p + 1) = x * |x| ^ p / (p + 1)
        rw [abs_of_neg hx', Real.rpow_add_one' (by linarith) hp1]
        ring)
    have hd := ((hasDerivAt_neg ξ).rpow_const (p := p + 1) (Or.inl (by linarith))).neg.div_const
      (p + 1)
    refine (hd.congr_of_eventuallyEq hloc.symm).congr_deriv ?_
    rw [abs_of_neg h, show p + 1 - 1 = p by ring]; field_simp
  · have hloc : (fun x => x ^ (p + 1) / (p + 1)) =ᶠ[nhds ξ] Phi0 p :=
      Filter.eventually_of_mem (Ioi_mem_nhds h) (fun x hx => by
        have hx' : 0 < x := hx
        show x ^ (p + 1) / (p + 1) = x * |x| ^ p / (p + 1)
        rw [abs_of_pos hx', Real.rpow_add_one' hx'.le hp1]
        ring)
    have hd : HasDerivAt (fun x => x ^ (p + 1) / (p + 1)) ((p + 1) * ξ ^ (p + 1 - 1) / (p + 1)) ξ :=
      (Real.hasDerivAt_rpow_const (Or.inl h.ne')).div_const _
    refine (hd.congr_of_eventuallyEq hloc.symm).congr_deriv ?_
    rw [abs_of_pos h, show p + 1 - 1 = p by ring]; field_simp

/-- Rademacher on `ℝ`: a locally Lipschitz function is differentiable a.e. -/
theorem c08_aux_ae_differentiable {f : ℝ → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ f x := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIcc (-(n:ℝ)) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨K, hK⟩ := (hf.locallyLipschitzOn (s := uIcc (-(n:ℝ)) n)).exists_lipschitzOnWith_of_compact
      isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval.ae_differentiableAt
  rw [← ae_all_iff] at h
  filter_upwards [h] with x hx
  apply hx (Nat.ceil |x|)
  have h1 := Nat.le_ceil |x|
  rw [uIcc_of_le (by linarith [abs_nonneg x])]
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

/-- `Y_γ` is closed under subtraction, with the triangle inequality for the norm. -/
theorem c08_aux_Y_sub {p γ : ℝ} {G H : ℝ → ℝ} (hG : G ∈ Y_gamma p γ) (hH : H ∈ Y_gamma p γ) :
    G - H ∈ Y_gamma p γ ∧ Y_gamma_norm p γ (G - H) ≤ Y_gamma_norm p γ G + Y_gamma_norm p γ H := by
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), deriv (G - H) y = deriv G y - deriv H y := by
    filter_upwards [c08_aux_ae_differentiable hG.1, c08_aux_ae_differentiable hH.1] with y h1 h2
    exact deriv_sub h1 h2
  have key : ∀ (w : ℝ → ℝ), (∀ y, 0 ≤ w y) → ∀ S : Set ℝ,
      essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖(G - H) y‖ + w y * ‖deriv (G - H) y‖)))
          (volume.restrict S) ≤
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + w y * ‖deriv G y‖))) (volume.restrict S) +
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖H y‖ + w y * ‖deriv H y‖)))
          (volume.restrict S) := by
    intro w hw S
    refine le_trans (essSup_mono_ae ?_) (ENNReal.essSup_add_le _ _)
    filter_upwards [ae_restrict_of_ae hae] with y hy
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [← ENNReal.ofReal_add (by have := c08_aux_jb_pos y; have := hw y; positivity)
      (by have := c08_aux_jb_pos y; have := hw y; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ).le
    rw [hy]
    have h1 : ‖G y - H y‖ ≤ ‖G y‖ + ‖H y‖ := norm_sub_le _ _
    have h2 : ‖deriv G y - deriv H y‖ ≤ ‖deriv G y‖ + ‖deriv H y‖ := norm_sub_le _ _
    nlinarith [mul_le_mul_of_nonneg_left h2 (hw y)]
  have hle : Y_gamma_norm p γ (G - H) ≤ Y_gamma_norm p γ G + Y_gamma_norm p γ H := by
    unfold Y_gamma_norm
    have e1 := key (fun y => jb y ^ (-1 / p))
      (fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le) (Ici 0)
    have e2 := key (fun y => jb y) (fun y => (c08_aux_jb_pos y).le) (Iic 0)
    calc _ ≤ _ := add_le_add e1 e2
      _ = _ := by ring
  exact ⟨⟨hG.1.sub hH.1, lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨hG.2, hH.2⟩)⟩, hle⟩

/-- `‖-f‖_{Y_γ} = ‖f‖_{Y_γ}`. -/
theorem c08_aux_Y_norm_neg (p γ : ℝ) (f : ℝ → ℝ) : Y_gamma_norm p γ (-f) = Y_gamma_norm p γ f := by
  unfold Y_gamma_norm
  simp only [Pi.neg_apply, norm_neg, deriv.neg]

/-- Schwartz decay in the form `‖ψ x‖ (1 + |x|)^K ≤ S`. -/
theorem c08_aux_schwartz_decay (ψ : SchwartzMap ℝ ℂ) (K : ℕ) :
    ∃ S, ∀ x : ℝ, ‖ψ x‖ * (1 + |x|) ^ K ≤ S := by
  refine ⟨2 ^ K * (Finset.Iic (K, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) ψ, fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, 0)) le_rfl le_rfl ψ x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  linarith

/-- A continuous polynomially bounded function times a Schwartz function is integrable and tends
to `0` at infinity. -/
theorem c08_aux_polyBounded_mul_schwartz (u : ℝ → ℂ) (hu : Continuous u) (hpb : IsPolyBounded u)
    (ψ : SchwartzMap ℝ ℂ) :
    Integrable (fun x => u x * ψ x) ∧ Tendsto (fun x => u x * ψ x) (cocompact ℝ) (nhds 0) := by
  obtain ⟨C, N, hC⟩ := hpb
  set K : ℕ := ⌈N⌉₊
  obtain ⟨S, hS⟩ := c08_aux_schwartz_decay ψ (K + 2)
  have hbd : ∀ x : ℝ, ‖u x * ψ x‖ ≤ (|C| * S) * (1 + |x|) ^ (-(2:ℝ)) := by
    intro x
    have hx0 : (0:ℝ) < 1 + |x| := by linarith [abs_nonneg x]
    have hu1 : ‖u x‖ ≤ |C| * (1 + |x|) ^ K := by
      refine (hC x).trans ?_
      have h1 : jb x ^ N ≤ jb x ^ (K : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb x) (Nat.le_ceil N)
      rw [Real.rpow_natCast] at h1
      have h2 : jb x ^ K ≤ (1 + |x|) ^ K :=
        pow_le_pow_left₀ (c08_aux_jb_pos x).le (c08_aux_jb_le_one_add x) K
      have h3 : 0 ≤ jb x ^ N := Real.rpow_nonneg (c08_aux_jb_pos x).le _
      calc C * jb x ^ N ≤ |C| * jb x ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) h3
        _ ≤ |C| * (1 + |x|) ^ K := mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C)
    have hψ := hS x
    rw [pow_add] at hψ
    rw [norm_mul, Real.rpow_neg hx0.le, Real.rpow_two]
    have hK0 : 0 < (1 + |x|) ^ K := pow_pos hx0 K
    have hsq0 : 0 < (1 + |x|) ^ 2 := pow_pos hx0 2
    rw [le_mul_inv_iff₀ hsq0]
    calc ‖u x‖ * ‖ψ x‖ * (1 + |x|) ^ 2 ≤ |C| * (1 + |x|) ^ K * ‖ψ x‖ * (1 + |x|) ^ 2 := by gcongr
      _ = |C| * (‖ψ x‖ * ((1 + |x|) ^ K * (1 + |x|) ^ 2)) := by ring
      _ ≤ |C| * S := mul_le_mul_of_nonneg_left hψ (abs_nonneg C)
  have hdom : Integrable (fun x : ℝ => (|C| * S) * (1 + ‖x‖) ^ (-(2:ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)).const_mul _
  refine ⟨hdom.mono' (hu.mul ψ.continuous).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbd x), ?_⟩
  have ht : Tendsto (fun x : ℝ => (|C| * S) * (1 + |x|) ^ (-(2:ℝ))) (cocompact ℝ) (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 + |x|) (cocompact ℝ) atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_norm_cocompact_atTop (E := ℝ))
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 2)).comp h1).const_mul (|C| * S)
  exact squeeze_zero_norm hbd ht

/-- Parseval-type identity `∫ f φ̂ = ∫ f̂ φ` for `f ∈ L¹`, `φ` Schwartz. -/
theorem c08_aux_parseval {f : ℝ → ℂ} (hf : Integrable f) (φ : SchwartzMap ℝ ℂ) :
    ∫ x, f x * fourierT (⇑φ) x = ∫ ξ, fourierT f ξ * φ ξ := by
  set F : ℝ → ℝ → ℂ := fun x ξ => f x * (φ ξ * Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ))))
    with hF
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hp : Integrable (fun z : ℝ × ℝ => ‖f z.1‖ * ‖φ z.2‖) (volume.prod volume) :=
      hf.norm.mul_prod φ.integrable.norm
    refine hp.mono' ?_ (Eventually.of_forall fun z => ?_)
    · have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => f z.1) (volume.prod volume) :=
        hf.1.comp_fst
      have h2 : Continuous (fun z : ℝ × ℝ =>
          φ z.2 * Complex.exp (-(Complex.I * (z.2 : ℂ) * (z.1 : ℂ)))) := by
        have := φ.continuous; fun_prop
      exact h1.mul h2.aestronglyMeasurable
    · simp only [Function.uncurry, hF]
      rw [norm_mul, norm_mul]
      have : ‖Complex.exp (-(Complex.I * (z.2 : ℂ) * (z.1 : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, mul_one]
  have hswap := integral_integral_swap hFi
  have hL : ∫ x, f x * fourierT (⇑φ) x = ∫ x, ∫ ξ, F x ξ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF]; unfold fourierT
    rw [integral_const_mul]
  have hR : ∫ ξ, fourierT f ξ * φ ξ = ∫ ξ, ∫ x, F x ξ := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF]; unfold fourierT
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [show -(Complex.I * (x : ℂ) * (ξ : ℂ)) = -(Complex.I * (ξ : ℂ) * (x : ℂ)) by ring]
    ring
  rw [hL, hR, hswap]

/-- A continuous, polynomially bounded function orthogonal to all Schwartz functions vanishes. -/
theorem c08_aux_test_zero {v : ℝ → ℂ} (hv : Continuous v)
    (h : ∀ g : SchwartzMap ℝ ℂ, ∫ x, v x * g x = 0) : v = 0 := by
  have hae : ∀ᵐ w ∂(volume : Measure ℝ), v w = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hv.locallyIntegrable
    intro g hg hgs
    have hgc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (g w : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hg
    have hgs' : HasCompactSupport (fun w => (g w : ℂ)) := hgs.comp_left Complex.ofReal_zero
    have : ∫ w, v w * (g w : ℂ) = 0 := h (hgs'.toSchwartzMap hgc)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [Complex.real_smul, mul_comm]
  exact (hv.ae_eq_iff_eq volume continuous_const).1 hae

/-- A smooth compactly supported function with zero integral is the derivative of a smooth
compactly supported function. -/
theorem c08_aux_primitive {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψs : HasCompactSupport ψ) (h0 : ∫ x, ψ x = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ deriv φ = ψ := by
  obtain ⟨R, hR⟩ := hψs.isCompact.isBounded.subset_closedBall 0
  have hR0 : ∀ x, R < |x| → ψ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have := hR hm
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  set a := -(|R| + 1)
  have hψc : Continuous ψ := hψ.continuous
  set φ : ℝ → ℝ := fun x => ∫ t in a..x, ψ t with hφdef
  have hφd : ∀ x, HasDerivAt φ (ψ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hψc.intervalIntegrable _ _)
      (hψc.stronglyMeasurableAtFilter _ _) hψc.continuousAt
  have hderiv : deriv φ = ψ := funext fun x => (hφd x).deriv
  have hφC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun x => (hφd x).differentiableAt, by rw [hderiv]; exact hψ⟩
  refine ⟨φ, hφC, ?_, hderiv⟩
  apply HasCompactSupport.intro (isCompact_Icc (a := a) (b := |R| + 1))
  intro x hx
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · -- `x < a`: integrand vanishes on `[x, a]`
    simp only [hφdef]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun t ht => ?_)]
    · simp
    · rw [uIcc_of_ge hx.le] at ht
      apply hR0
      rw [abs_of_neg (by linarith [ht.2, abs_nonneg R])]
      linarith [ht.2, le_abs_self R]
  · simp only [hφdef]
    have hsupp : Function.support ψ ⊆ Ioc a (|R| + 1) := by
      intro t ht
      by_contra hn
      apply ht
      apply hR0
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hn
      rcases hn with h | h
      · rw [abs_of_neg (by linarith [abs_nonneg R])]; linarith [le_abs_self R, neg_abs_le R]
      · rw [abs_of_pos (by linarith [abs_nonneg R])]; linarith [le_abs_self R]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := |R| + 1)
      (hψc.intervalIntegrable _ _) (hψc.intervalIntegrable _ _),
      intervalIntegral.integral_eq_integral_of_support_subset hsupp, h0, zero_add]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun t ht => ?_)]
    · simp
    · rw [uIcc_of_le hx.le] at ht
      apply hR0
      rw [abs_of_pos (by linarith [ht.1, abs_nonneg R])]
      linarith [ht.1, le_abs_self R]

/-- du Bois-Reymond: a continuous function whose distributional derivative vanishes is constant. -/
theorem c08_aux_duBoisReymond {W : ℝ → ℂ} (hW : Continuous W)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∫ x, W x * ((deriv φ x : ℝ) : ℂ) = 0) : ∀ x, W x = W 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set ψ₀ := b.normed volume with hψ₀
  have hψ₀C : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀ := b.contDiff_normed
  have hψ₀s : HasCompactSupport ψ₀ := b.hasCompactSupport_normed
  have hψ₀i : ∫ x, ψ₀ x = 1 := b.integral_normed
  set c := ∫ x, W x * (ψ₀ x : ℂ)
  have hkey : ∀ g : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
      ∫ x, g x • (W x - c) = 0 := by
    intro g hg hgs
    set ψ := fun x => g x - (∫ y, g y) * ψ₀ x with hψdef
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgs
    have hψ₀int : Integrable ψ₀ := hψ₀C.continuous.integrable_of_hasCompactSupport hψ₀s
    have hψC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := hg.sub (contDiff_const.mul hψ₀C)
    have hψs : HasCompactSupport ψ := hgs.sub (hψ₀s.mul_left)
    have hψ0 : ∫ x, ψ x = 0 := by
      simp only [hψdef]
      rw [integral_sub hgi (hψ₀int.const_mul _), integral_const_mul, hψ₀i, mul_one, sub_self]
    obtain ⟨φ, hφC, hφs, hφd⟩ := c08_aux_primitive hψC hψs hψ0
    have h1 := h φ hφC hφs
    rw [hφd] at h1
    have hWc : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
        Integrable (fun x => W x * (f x : ℂ)) := fun f hf hfs =>
      (hW.mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
        (hfs.comp_left Complex.ofReal_zero).mul_left
    have i1 := hWc g hg.continuous hgs
    have i2 := (hWc ψ₀ hψ₀C.continuous hψ₀s).const_mul ((∫ y, g y : ℝ) : ℂ)
    have e1 : (fun x => W x * ((ψ x : ℝ) : ℂ)) =
        fun x => W x * (g x : ℂ) - ((∫ y, g y : ℝ) : ℂ) * (W x * (ψ₀ x : ℂ)) := by
      ext x; simp only [hψdef]; push_cast; ring
    rw [e1, integral_sub i1 i2, integral_const_mul] at h1
    have e2 : (fun x => g x • (W x - c)) = fun x => W x * (g x : ℂ) - c * (g x : ℂ) := by
      ext x; rw [Complex.real_smul]; ring
    have i3 : Integrable (fun x => c * ((g x : ℝ) : ℂ)) :=
      ((Complex.continuous_ofReal.comp hg.continuous).integrable_of_hasCompactSupport
        (hgs.comp_left Complex.ofReal_zero)).const_mul c
    have k : ∫ a, ((g a : ℝ) : ℂ) = ((∫ a, g a : ℝ) : ℂ) := integral_ofReal
    rw [e2, integral_sub i1 i3, integral_const_mul, k]
    rw [sub_eq_zero] at h1
    rw [h1]; ring
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), W x - c = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero (hW.sub continuous_const).locallyIntegrable hkey
  have hconst : (fun x => W x - c) = fun _ => 0 :=
    ((hW.sub continuous_const).ae_eq_iff_eq volume continuous_const).1 hae
  intro x
  have h1 := congrFun hconst x
  have h2 := congrFun hconst 0
  simp only [sub_eq_zero] at h1 h2
  rw [h1, h2]

/-! ## Integrability -/

/-- Blueprint: lem:c08_L1_embedding.  For `γ > 1 + 1/p`, elements of `X_γ`, `Y_γ` are in
`L¹ ∩ L^∞` together with their first derivative (bounded by the norm), `G → 0` at infinity and
`(G')^ = iξ Ĝ`, `(r')^ = iξ r̂`. -/
theorem c08_L1_embedding (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 + 1 / p < γ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ r ∈ X_gamma p γ,
        Integrable r ∧ Integrable (deriv r) ∧ MemLp r ⊤ ∧ MemLp (deriv r) ⊤ ∧
        (∫ x, |r x|) + (∫ x, |deriv r x|) + (eLpNorm r ⊤ volume).toReal +
            (eLpNorm (deriv r) ⊤ volume).toReal ≤ C * xNorm p γ r ∧
        ∀ ξ : ℝ, fourierT (fun x => ((deriv r x : ℝ) : ℂ)) ξ =
          Complex.I * ξ * fourierT (fun x => (r x : ℂ)) ξ) ∧
      (∀ G ∈ Y_gamma p γ,
        Integrable G ∧ Integrable (deriv G) ∧ MemLp G ⊤ ∧
        (∫ x, |G x|) + (∫ x, |deriv G x|) + (eLpNorm G ⊤ volume).toReal ≤ C * yNorm p γ G ∧
        Tendsto G (cocompact ℝ) (nhds 0) ∧
        ∀ ξ : ℝ, fourierT (fun x => ((deriv G x : ℝ) : ℂ)) ξ =
          Complex.I * ξ * fourierT (fun x => (G x : ℂ)) ξ) := by
  have hp0 : 0 < p := by linarith
  have hpi : 0 < 1 / p := by positivity
  have ha : 1 < γ - 1 / p := by linarith
  have hγ1 : 1 < γ := by linarith
  set I1 := ∫ x, jb x ^ (-γ)
  set I2 := ∫ x, jb x ^ (-(γ - 1 / p))
  have hI1 : 0 ≤ I1 := integral_nonneg (fun z => (Real.rpow_pos_of_pos (c08_aux_jb_pos z) _).le)
  have hI2 : 0 ≤ I2 := integral_nonneg (fun z => (Real.rpow_pos_of_pos (c08_aux_jb_pos z) _).le)
  have hexp : -γ + 1 / p = -(γ - 1 / p) := by ring
  refine ⟨I1 + I2 + 2, by positivity, ?_, ?_⟩
  · intro r hr
    have hN : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg
    have hb := c08_aux_X_ae_bound hp0 hr
    have hrc : Continuous r := hr.1.1.continuous
    have hr'c : Continuous (deriv r) := hr.1.1.continuous_deriv le_rfl
    obtain ⟨i1, m1, l1, s1⟩ := c08_aux_L1_Linf_of_bound hrc.aestronglyMeasurable hγ1 hN
      (by filter_upwards [hb] with y hy; exact hy.1)
    obtain ⟨i2, m2, l2, s2⟩ := c08_aux_L1_Linf_of_bound hr'c.aestronglyMeasurable ha hN
      (by filter_upwards [hb] with y hy; rw [← hexp]; exact hy.2)
    refine ⟨i1, i2, m1, m2, ?_, fun ξ => ?_⟩
    · nlinarith
    · exact c08_aux_fourierT_deriv hr.1.1.locallyLipschitz i1 i2
        (c08_aux_tendsto_of_bound (by linarith) (c08_aux_X_pointwise hr)) ξ
  · intro G hG
    have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    have hb := c08_aux_Y_ae_bound hp0 hG
    have hGc : Continuous G := hG.1.continuous
    have hpt : ∀ y, |G y| ≤ yNorm p γ G * jb y ^ (-γ) := by
      have hw : Continuous (fun y => yNorm p γ G * jb y ^ (-γ)) := by
        apply continuous_const.mul
        exact (Real.continuous_sqrt.comp (by fun_prop)).rpow_const
          (fun y => Or.inl (c08_aux_jb_pos y).ne')
      have hae : ∀ᵐ y ∂(volume : Measure ℝ), |G y| ≤ yNorm p γ G * jb y ^ (-γ) := by
        filter_upwards [hb] with y hy; exact hy.1
      exact c08_aux_le_of_ae_halflines hGc.abs hw (ae_restrict_of_ae hae) (ae_restrict_of_ae hae)
    obtain ⟨i1, m1, l1, s1⟩ := c08_aux_L1_Linf_of_bound hGc.aestronglyMeasurable hγ1 hN
      (Eventually.of_forall hpt)
    obtain ⟨i2, -, l2, -⟩ := c08_aux_L1_Linf_of_bound
      (measurable_deriv G).aestronglyMeasurable ha hN
      (by filter_upwards [hb] with y hy; rw [← hexp]; exact hy.2)
    have hlim := c08_aux_tendsto_of_bound (by linarith) hpt
    refine ⟨i1, i2, m1, ?_, hlim, fun ξ => c08_aux_fourierT_deriv hG.1 i1 i2 hlim ξ⟩
    nlinarith

/-! ## Symbol-type bounds (helpers for lem:c08_phi_integrand, lem:c08_phi_bounds) -/

/-- `x^a ≤ 2^{|a|}` for `x ∈ [1/2,2]`. -/
theorem c08_aux_rpow_le_two_abs {x a : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 2) : x ^ a ≤ 2 ^ |a| := by
  obtain ⟨hx1, hx2⟩ := hx
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]; exact Real.rpow_le_rpow (by linarith) hx2 ha
  · rw [abs_of_nonpos ha]
    calc x ^ a ≤ (1 / 2) ^ a := Real.rpow_le_rpow_of_nonpos (by norm_num) hx1 ha
      _ = 2 ^ (-a) := by
        rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]

/-- Uniform bounds for the derivatives of `x ↦ x^r` on `[1/2,2]`. -/
theorem c08_aux_iter_rpow_bound (r : ℝ) (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, i ≤ n →
    ∀ x ∈ Icc (1 / 2 : ℝ) 2, |iteratedDeriv i (fun x : ℝ => x ^ r) x| ≤ M := by
  refine ⟨∑ i ∈ Finset.range (n + 1), |(descPochhammer ℝ i).eval r| * 2 ^ (|r| + i),
    Finset.sum_nonneg (fun i _ => by positivity), fun i hi x hx => ?_⟩
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul]
  have hx0 : 0 < x := by linarith [hx.1]
  have h1 : |x ^ (r - i)| ≤ 2 ^ (|r| + i) := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    refine (c08_aux_rpow_le_two_abs hx).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have : (0:ℝ) ≤ i := by positivity
    calc |r - i| ≤ |r| + |(i:ℝ)| := abs_sub _ _
      _ = |r| + i := by rw [abs_of_nonneg this]
  calc _ ≤ |(descPochhammer ℝ i).eval r| * 2 ^ (|r| + i) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun i => |(descPochhammer ℝ i).eval r| * 2 ^ (|r| + (i:ℝ)))
        (fun i _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- Faà di Bruno bound (copy of the chapter-04 wrapper). -/
theorem c08_aux_fdb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) (f : ℝ → ℝ)
    (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) (n : ℕ) (hg : ContDiffOn ℝ n g t)
    (hf : ContDiffOn ℝ n f s) (hst : MapsTo f s t) (x : ℝ) (hx : x ∈ s) (C D : ℝ)
    (hC : ∀ i, i ≤ n → ‖iteratedDeriv i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i f x| ≤ D ^ i) :
    ‖iteratedDeriv n (g ∘ f) x‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_of_isOpen n hs hx]
  refine norm_iteratedFDerivWithin_comp_le hg hf le_rfl ht.uniqueDiffOn hs.uniqueDiffOn hst hx
    (fun i hi => ?_) (fun i hi1 hi => ?_)
  · rw [iteratedFDerivWithin_of_isOpen i ht (hst hx), norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC i hi
  · rw [iteratedFDerivWithin_of_isOpen i hs hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs]
    exact hD i hi1 hi

/-- Derivatives of `f^r` when `f ∈ [1/2,2]` and `|f^{(i)}(t)| ≤ Bδ t^{-a-i}` (`i ≥ 1`, `t ≥ 1`). -/
theorem c08_aux_comp_rpow_bound (r : ℝ) (n : ℕ) (hn : 1 ≤ n) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : ℝ → ℝ) (S : Set ℝ), IsOpen S → ContDiffOn ℝ n f S → MapsTo f S (Ioi 0) →
    ∀ t ∈ S, 1 ≤ t → f t ∈ Icc (1 / 2 : ℝ) 2 → ∀ (B δ a : ℝ), 1 ≤ B → 0 ≤ δ → δ ≤ 1 → 0 ≤ a →
    (∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i f t| ≤ B * δ * t ^ (-a - i)) →
    |iteratedDeriv n (fun x => f x ^ r) t| ≤ C * B ^ n * δ * t ^ (-a - n) := by
  obtain ⟨M, hM0, hM⟩ := c08_aux_iter_rpow_bound r n
  refine ⟨n.factorial * M, by positivity, fun f S hS hf hmap t htS ht1 hft B δ a hB hδ0 hδ1 ha hder => ?_⟩
  have ht0 : 0 < t := by linarith
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set D := B * δ ^ (1 / (n:ℝ)) * t ^ (-(1 + a / n)) with hD
  have hg : ContDiffOn ℝ n (fun x : ℝ => x ^ r) (Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)
  have key := c08_aux_fdb (fun x : ℝ => x ^ r) f S (Ioi 0) hS isOpen_Ioi n hg hf hmap t htS M D
    (fun i hi => by rw [Real.norm_eq_abs]; exact hM i hi _ hft) (fun i hi1 hi => ?_)
  · have hDn : D ^ n = B ^ n * δ * t ^ (-a - n) := by
      rw [hD, mul_pow, mul_pow, ← Real.rpow_natCast (δ ^ _), ← Real.rpow_mul hδ0,
        ← Real.rpow_natCast (t ^ _), ← Real.rpow_mul ht0.le]
      congr 2
      · rw [one_div_mul_cancel hnpos.ne', Real.rpow_one]
      · field_simp; ring
    rw [hDn] at key
    have : (fun x => f x ^ r) = (fun x : ℝ => x ^ r) ∘ f := rfl
    rw [this, ← Real.norm_eq_abs]
    calc _ ≤ _ := key
      _ = _ := by ring
  · have hi0 : (0:ℝ) < i := by exact_mod_cast (show 0 < i by omega)
    have hin : (i:ℝ) ≤ n := by exact_mod_cast hi
    refine (hder i hi1 hi).trans ?_
    rw [hD, mul_pow, mul_pow, ← Real.rpow_natCast (δ ^ _), ← Real.rpow_mul hδ0,
      ← Real.rpow_natCast (t ^ _), ← Real.rpow_mul ht0.le]
    have h1 : B ≤ B ^ i := le_self_pow₀ hB (by omega)
    have h2 : δ ≤ δ ^ (1 / (n:ℝ) * i) := by
      calc δ = δ ^ (1:ℝ) := (Real.rpow_one δ).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge' hδ0 hδ1 (by positivity)
            (by rw [div_mul_eq_mul_div, one_mul, div_le_one hnpos]; exact hin)
    have h3 : t ^ (-a - i) ≤ t ^ (-(1 + a / n) * i) := by
      apply Real.rpow_le_rpow_of_exponent_le ht1
      have : a * i / n ≤ a := by
        rw [mul_div_assoc]; exact mul_le_of_le_one_right ha ((div_le_one hnpos).2 hin)
      have e : -(1 + a / n) * i = -i - a * i / n := by ring
      rw [e]; linarith
    have hB0 : 0 ≤ B := by linarith
    gcongr


/-- Leibniz bound for power-type estimates at a point `y > 0`. -/
theorem c08_aux_leibniz (f g : ℝ → ℝ) (y : ℝ) (hy : 0 < y) (k : ℕ) (hf : ContDiffAt ℝ k f y)
    (hg : ContDiffAt ℝ k g y) (A B a b : ℝ)
    (hA : ∀ i, i ≤ k → |iteratedDeriv i f y| ≤ A * y ^ (a - i))
    (hB : ∀ i, i ≤ k → |iteratedDeriv i g y| ≤ B * y ^ (b - i)) :
    |iteratedDeriv k (fun x => f x * g x) y| ≤ 2 ^ k * (A * B) * y ^ (a + b - k) := by
  rw [show (fun x => f x * g x) = f * g from rfl, iteratedDeriv_mul hf hg]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(k.choose i : ℝ) * iteratedDeriv i f y * iteratedDeriv (k - i) g y| ≤
        (k.choose i : ℝ) * (A * B * y ^ (a + b - k)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : y ^ (a - i) * y ^ (b - ((k - i : ℕ) : ℝ)) = y ^ (a + b - k) := by
      rw [← rpow_add hy, Nat.cast_sub hik]; ring_nf
    have h2 := hA i hik
    have h3 := hB (k - i) (Nat.sub_le k i)
    have hA0 : 0 ≤ A * y ^ (a - i) := le_trans (abs_nonneg _) h2
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ k.choose i)]
    calc (k.choose i : ℝ) * |iteratedDeriv i f y| * |iteratedDeriv (k - i) g y|
        ≤ (k.choose i : ℝ) * (A * y ^ (a - i)) * (B * y ^ (b - ((k - i : ℕ) : ℝ))) := by gcongr
      _ = _ := by rw [← e]; ring
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), |(k.choose i : ℝ) * iteratedDeriv i f y * iteratedDeriv (k - i) g y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (A * B * y ^ (a + b - k)) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ k * (A * B) * y ^ (a + b - k) := by
        rw [← Finset.sum_mul]
        have := Nat.sum_range_choose k
        have h : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by exact_mod_cast this
        rw [h]; ring

/-- Uniformising constants over `i ≤ n`. -/
theorem c08_aux_uniform_const (P : ℕ → ℝ → Prop) (hmono : ∀ i K K', K ≤ K' → P i K → P i K')
    (h : ∀ i, ∃ K, 0 ≤ K ∧ P i K) (n : ℕ) : ∃ K, 0 ≤ K ∧ ∀ i, i ≤ n → P i K := by
  choose K hK0 hK using h
  refine ⟨∑ i ∈ Finset.range (n + 1), K i, Finset.sum_nonneg (fun i _ => hK0 i), fun i hi => ?_⟩
  exact hmono i _ _ (Finset.single_le_sum (fun j _ => hK0 j)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) (hK i)

/-- Leibniz bound, uniform version: bounds for all `i ≤ k` of the product. -/
theorem c08_aux_leibniz_all (f g : ℝ → ℝ) (y : ℝ) (hy : 0 < y) (k : ℕ) (hf : ContDiffAt ℝ k f y)
    (hg : ContDiffAt ℝ k g y) (A B a b : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ i, i ≤ k → |iteratedDeriv i f y| ≤ A * y ^ (a - i))
    (hB : ∀ i, i ≤ k → |iteratedDeriv i g y| ≤ B * y ^ (b - i)) :
    ∀ i, i ≤ k → |iteratedDeriv i (fun x => f x * g x) y| ≤ 2 ^ k * (A * B) * y ^ (a + b - i) := by
  intro i hi
  refine (c08_aux_leibniz f g y hy i (hf.of_le (by exact_mod_cast hi))
    (hg.of_le (by exact_mod_cast hi)) A B a b (fun j hj => hA j (hj.trans hi))
    (fun j hj => hB j (hj.trans hi))).trans ?_
  apply mul_le_mul_of_nonneg_right _ (rpow_pos_of_pos hy _).le
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA0 hB0)
  exact pow_le_pow_right₀ (by norm_num) hi

/-- Derivatives of `t ↦ t^b` at `t > 0`: `|∂^i t^b| ≤ P t^{b-i}`, uniformly in `i ≤ n`. -/
theorem c08_aux_iter_rpow_pow (b : ℝ) (n : ℕ) : ∃ P : ℝ, 0 ≤ P ∧ ∀ i, i ≤ n → ∀ t : ℝ, 0 < t →
    |iteratedDeriv i (fun t : ℝ => t ^ b) t| ≤ P * t ^ (b - i) := by
  refine ⟨∑ i ∈ Finset.range (n + 1), |(descPochhammer ℝ i).eval b|,
    Finset.sum_nonneg (fun i _ => abs_nonneg _), fun i hi t ht => ?_⟩
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos ht _).le
  exact Finset.single_le_sum (f := fun i => |(descPochhammer ℝ i).eval b|)
    (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- `χ₊` is smooth. -/
theorem c08_aux_chiPlus_contDiff : ContDiff ℝ (⊤ : ℕ∞) chiPlus := by
  unfold chiPlus
  exact Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

/-- `χ₊ = 0` on `(-∞,1]`, `χ₊ = 1` on `[2,∞)`, `0 ≤ χ₊ ≤ 1`. -/
theorem c08_aux_chiPlus_props :
    (∀ t : ℝ, t ≤ 1 → chiPlus t = 0) ∧ (∀ t : ℝ, 2 ≤ t → chiPlus t = 1) ∧
    (∀ t, 0 ≤ chiPlus t) ∧ (∀ t, chiPlus t ≤ 1) :=
  ⟨fun t ht => Real.smoothTransition.zero_of_nonpos (by linarith),
    fun t ht => Real.smoothTransition.one_of_one_le (by linarith),
    fun _ => Real.smoothTransition.nonneg _, fun _ => Real.smoothTransition.le_one _⟩

/-- `|χ₊^{(i)}(t)| ≤ A t^{-i}` for `t ≥ 1`, `i ≤ n`. -/
theorem c08_aux_chiPlus_iter_bound (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ i, i ≤ n → ∀ t : ℝ, 1 ≤ t →
    |iteratedDeriv i chiPlus t| ≤ A * t ^ ((0:ℝ) - i) := by
  obtain ⟨-, h2, h0, h1⟩ := c08_aux_chiPlus_props
  have hM : ∀ i : ℕ, ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc (1:ℝ) 2, |iteratedDeriv i chiPlus t| ≤ M := by
    intro i
    have hc : Continuous (iteratedDeriv i chiPlus) :=
      c08_aux_chiPlus_contDiff.continuous_iteratedDeriv i (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
      hc.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun t ht => (Real.norm_eq_abs _ ▸ hM t ht).trans
      (le_max_left _ _)⟩
  refine c08_aux_uniform_const (fun i A => ∀ t : ℝ, 1 ≤ t →
      |iteratedDeriv i chiPlus t| ≤ A * t ^ ((0:ℝ) - i)) ?_ ?_ n
  · intro i K K' hK h t ht
    exact (h t ht).trans (mul_le_mul_of_nonneg_right hK (Real.rpow_pos_of_pos (by linarith) _).le)
  · intro i
    obtain ⟨M, hM0, hM⟩ := hM i
    refine ⟨M * 2 ^ i + 1, by positivity, fun t ht => ?_⟩
    have ht0 : 0 < t := by linarith
    have hti : t ^ ((0:ℝ) - i) = (t ^ i)⁻¹ := by
      rw [zero_sub, Real.rpow_neg ht0.le, Real.rpow_natCast]
    rw [hti]
    rcases le_or_gt t 2 with h | h
    · have hb := hM t ⟨ht, h⟩
      have htp : t ^ i ≤ 2 ^ i := pow_le_pow_left₀ ht0.le h i
      have htp0 : 0 < t ^ i := pow_pos ht0 i
      rw [← div_eq_mul_inv, le_div_iff₀ htp0]
      nlinarith [mul_le_mul_of_nonneg_left htp hM0, abs_nonneg (iteratedDeriv i chiPlus t)]
    · rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one]
        rw [abs_of_nonneg (h0 t)]; linarith [h1 t]
      · have : chiPlus =ᶠ[nhds t] fun _ => (1:ℝ) :=
          Filter.eventually_of_mem (Ioi_mem_nhds h) (fun x hx => h2 x (le_of_lt hx))
        rw [this.iteratedDeriv_eq, iteratedDeriv_const]
        simp only [show i ≠ 0 by omega, ↓reduceIte, abs_zero]
        positivity


/-- `ϱ(t) = χ₊(t) t^{-1-p}` satisfies `0 ≤ ϱ ≤ 1` on `(0,∞)`. -/
theorem c08_aux_rho_range (p t : ℝ) (hp : 0 < p) (ht : 0 < t) :
    0 ≤ chiPlus t * t ^ (-1 - p) ∧ chiPlus t * t ^ (-1 - p) ≤ 1 ∧
    chiPlus t * t ^ (-1 - p) ≤ t ^ (-1 - p) := by
  obtain ⟨h0', -, h0, h1⟩ := c08_aux_chiPlus_props
  have hpos := Real.rpow_pos_of_pos ht (-1 - p)
  refine ⟨mul_nonneg (h0 t) hpos.le, ?_, mul_le_of_le_one_left hpos.le (h1 t)⟩
  rcases le_or_gt t 1 with h | h
  · rw [h0' t h, zero_mul]; norm_num
  · calc chiPlus t * t ^ (-1 - p) ≤ 1 * 1 :=
          mul_le_mul (h1 t) (Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)) hpos.le
            zero_le_one
      _ = 1 := by norm_num

/-- Derivative bounds for `ϱ(t) = χ₊(t) t^{-1-p}`. -/
theorem c08_aux_rho_iter_bound (p : ℝ) (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ i, i ≤ n → ∀ t : ℝ, 1 ≤ t →
    |iteratedDeriv i (fun t => chiPlus t * t ^ (-1 - p)) t| ≤ K * t ^ (-1 - p - i) := by
  obtain ⟨A, hA0, hA⟩ := c08_aux_chiPlus_iter_bound n
  obtain ⟨P, hP0, hP⟩ := c08_aux_iter_rpow_pow (-1 - p) n
  refine ⟨2 ^ n * (A * P), by positivity, fun i hi t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have := c08_aux_leibniz_all chiPlus (fun t : ℝ => t ^ (-1 - p)) t ht0 n
    (c08_aux_chiPlus_contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
    (contDiffAt_rpow_const (Or.inl ht0.ne')) A P 0 (-1 - p) hA0 hP0
    (fun j hj => hA j (hj.trans le_rfl) t ht) (fun j hj => hP j hj t ht0) i hi
  rw [zero_add] at this
  exact this

/-- `b_c(t) = c χ₊(t) t^{-p}` for all `t`. -/
theorem c08_aux_phi_b_eq (p c t : ℝ) : c08_phi_b p c t = c * chiPlus t * t ^ (-p) := by
  unfold c08_phi_b
  split_ifs with h
  · rfl
  · rw [c08_aux_chiPlus_props.1 t (not_lt.1 h)]; ring

/-- On `(0,∞)`: `(t - b_c(t))^{1/p} - t^{1/p} = t^{1/p}((1 - cϱ(t))^{1/p} - 1)`. -/
theorem c08_aux_g_eq (p c t : ℝ) (hp : 0 < p) (hc : |c| ≤ 1 / 2) (ht : 0 < t) :
    (t - c08_phi_b p c t) ^ (1 / p) - t ^ (1 / p) =
      t ^ (1 / p) * ((1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1) := by
  obtain ⟨hr0, hr1, -⟩ := c08_aux_rho_range p t hp ht
  have hf : 0 ≤ 1 - c * (chiPlus t * t ^ (-1 - p)) := by
    have : |c * (chiPlus t * t ^ (-1 - p))| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg hr0]; nlinarith [abs_nonneg c]
    linarith [(abs_le.1 this).2]
  have e : t - c08_phi_b p c t = t * (1 - c * (chiPlus t * t ^ (-1 - p))) := by
    rw [c08_aux_phi_b_eq]
    have : t * t ^ (-1 - p) = t ^ (-p) := by
      rw [← Real.rpow_one_add' ht.le (by linarith)]; ring_nf
    linear_combination (c * chiPlus t) * this
  rw [e, Real.mul_rpow ht.le hf]; ring


/-- `f_c = 1 - cϱ` is smooth on `(0,∞)` with values in `[1/2,3/2]`. -/
theorem c08_aux_fc_props (p c : ℝ) (hp : 0 < p) (hc : |c| ≤ 1 / 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun t => 1 - c * (chiPlus t * t ^ (-1 - p))) (Ioi 0) ∧
    ∀ t, 0 < t → 1 - c * (chiPlus t * t ^ (-1 - p)) ∈ Icc (1 / 2 : ℝ) 2 ∧
      |1 - c * (chiPlus t * t ^ (-1 - p)) - 1| ≤ |c| * t ^ (-1 - p) := by
  refine ⟨contDiffOn_const.sub (contDiffOn_const.mul (c08_aux_chiPlus_contDiff.contDiffOn.mul
    (contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)))), fun t ht => ?_⟩
  obtain ⟨hr0, hr1, hr2⟩ := c08_aux_rho_range p t hp ht
  have h1 : |c * (chiPlus t * t ^ (-1 - p))| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hr0]; nlinarith [abs_nonneg c]
  have h2 := abs_le.1 h1
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  rw [show 1 - c * (chiPlus t * t ^ (-1 - p)) - 1 = -(c * (chiPlus t * t ^ (-1 - p))) by ring,
    abs_neg, abs_mul, abs_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_left hr2 (abs_nonneg c)

/-- Derivative bounds for `(1 - cϱ)^{1/p} - 1`. -/
theorem c08_aux_fc_pow_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (i : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ t : ℝ, 1 ≤ t →
      |iteratedDeriv i (fun t => (1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1) t| ≤
        K * |c| * t ^ (-1 - p - i) := by
  have hp0 : 0 < p := by linarith
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    refine ⟨7, by norm_num, fun c hc t ht => ?_⟩
    obtain ⟨-, hf⟩ := c08_aux_fc_props p c hp0 hc
    obtain ⟨⟨hf1, hf2⟩, hf3⟩ := hf t (by linarith)
    simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero]
    have hq1 : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
    have hq3 : 1 / p ≤ 3 := by rw [div_le_iff₀ hp0]; linarith
    refine (c08_aux_rpow_sub_one_le (by linarith) hf2 hq1 hq3).trans ?_
    calc 7 * |1 - c * (chiPlus t * t ^ (-1 - p)) - 1| ≤ 7 * (|c| * t ^ (-1 - p)) := by gcongr
      _ = _ := by ring
  · obtain ⟨C, hC0, hC⟩ := c08_aux_comp_rpow_bound (1 / p) i hi
    obtain ⟨Kρ, hKρ0, hKρ⟩ := c08_aux_rho_iter_bound p i
    set B := max 1 Kρ
    refine ⟨C * B ^ i, by positivity, fun c hc t ht => ?_⟩
    obtain ⟨hfC, hf⟩ := c08_aux_fc_props p c hp0 hc
    have ht0 : 0 < t := by linarith
    have e : (fun t => (1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1) =
        fun t => (-1) + (1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) := by
      funext t; ring
    rw [e, iteratedDeriv_const_add hi]
    have key := hC (fun t => 1 - c * (chiPlus t * t ^ (-1 - p))) (Ioi 0) isOpen_Ioi
      (hfC.of_le (by exact_mod_cast le_top)) (fun x hx => by
        have := (hf x hx).1.1; simp only [mem_Ioi]; linarith) t ht0 ht (hf t ht0).1 B |c| (1 + p)
      (le_max_left _ _) (abs_nonneg c) (by linarith) (by linarith) ?_
    · calc _ ≤ _ := key
        _ = _ := by ring_nf
    · intro j hj1 hj
      have e2 : (fun t => 1 - c * (chiPlus t * t ^ (-1 - p))) =
          fun t => 1 - (fun t => c * (chiPlus t * t ^ (-1 - p))) t := rfl
      rw [e2, iteratedDeriv_const_sub (by omega), iteratedDeriv_neg, abs_neg,
        iteratedDeriv_const_mul_field, abs_mul]
      have := hKρ j hj t ht
      have hB : Kρ ≤ B := le_max_right _ _
      calc |c| * |iteratedDeriv j (fun t => chiPlus t * t ^ (-1 - p)) t|
          ≤ |c| * (B * t ^ (-1 - p - j)) := by
            gcongr
            exact this.trans (mul_le_mul_of_nonneg_right hB (Real.rpow_pos_of_pos ht0 _).le)
        _ = _ := by ring_nf

/-! ## The diffeomorphism `φ_c` -/

/-- Blueprint: lem:c08_phi_integrand.  `g_c(t) = (t - b_c(t))^{1/p} - t^{1/p}` is smooth on
`(1/2,∞)`, vanishes on `(1/2,1]` and `|g_c^{(j)}(t)| ≤ C_j |c| t^{1/p-p-1-j}` for `t ≥ 1`. -/
theorem c08_phi_integrand (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ c : ℝ, |c| ≤ 1 / 2 →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun t => (t - c08_phi_b p c t) ^ (1 / p) - t ^ (1 / p)) (Ioi (1 / 2)) ∧
      ∀ t ∈ Ioc (1 / 2 : ℝ) 1, (t - c08_phi_b p c t) ^ (1 / p) - t ^ (1 / p) = 0) ∧
    ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ t : ℝ, 1 ≤ t →
      |iteratedDeriv j (fun t => (t - c08_phi_b p c t) ^ (1 / p) - t ^ (1 / p)) t| ≤
        C * |c| * t ^ (1 / p - p - 1 - (j : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hfC : ∀ c : ℝ, |c| ≤ 1 / 2 → ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t => t ^ (1 / p) * ((1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1)) (Ioi 0) := by
    intro c hc
    obtain ⟨hfC, hf⟩ := c08_aux_fc_props p c hp0 hc
    exact (contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)).mul
      ((hfC.rpow_const_of_ne (fun x hx => by have := (hf x hx).1.1; linarith)).sub contDiffOn_const)
  refine ⟨fun c hc => ⟨?_, fun t ht => ?_⟩, fun j => ?_⟩
  · refine ((hfC c hc).mono (fun x hx => by
      simp only [mem_Ioi] at hx ⊢; linarith)).congr (fun t ht => ?_)
    exact c08_aux_g_eq p c t hp0 hc (by have : (1:ℝ)/2 < t := ht; linarith)
  · rw [c08_aux_phi_b_eq, c08_aux_chiPlus_props.1 t ht.2]; simp
  · obtain ⟨P, hP0, hP⟩ := c08_aux_iter_rpow_pow (1 / p) j
    obtain ⟨K, hK0, hK⟩ := c08_aux_uniform_const (fun i K => ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ t : ℝ,
      1 ≤ t → |iteratedDeriv i (fun t => (1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1) t| ≤
        K * |c| * t ^ (-1 - p - i)) (fun i K K' hK h c hc t ht => (h c hc t ht).trans (by
          have := Real.rpow_pos_of_pos (show (0:ℝ) < t by linarith) (-1 - p - i)
          gcongr)) (fun i => c08_aux_fc_pow_bound p hp hp1 i) j
    refine ⟨2 ^ j * (P * K) + 1, by positivity, fun c hc t ht => ?_⟩
    have ht0 : 0 < t := by linarith
    have heq : (fun t => (t - c08_phi_b p c t) ^ (1 / p) - t ^ (1 / p)) =ᶠ[nhds t]
        (fun t => t ^ (1 / p) * ((1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht0) (fun x hx => c08_aux_g_eq p c x hp0 hc hx)
    rw [heq.iteratedDeriv_eq]
    have hcd := ((hfC c hc).contDiffAt (Ioi_mem_nhds ht0))
    obtain ⟨hfC', hf⟩ := c08_aux_fc_props p c hp0 hc
    have h2 : ContDiffAt ℝ j (fun t => (1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1) t :=
      (((hfC'.rpow_const_of_ne (fun x hx => by have := (hf x hx).1.1; linarith)).sub
        contDiffOn_const).contDiffAt (Ioi_mem_nhds ht0)).of_le (by exact_mod_cast le_top)
    have := c08_aux_leibniz (fun t : ℝ => t ^ (1 / p))
      (fun t => (1 - c * (chiPlus t * t ^ (-1 - p))) ^ (1 / p) - 1) t ht0 j
      (contDiffAt_rpow_const (Or.inl ht0.ne')) h2 P (K * |c|) (1 / p) (-1 - p)
      (fun i hi => hP i hi t ht0) (fun i hi => hK i hi c hc t ht)
    calc _ ≤ _ := this
      _ = 2 ^ j * (P * K) * |c| * t ^ (1 / p - p - 1 - (j : ℝ)) := by ring_nf
      _ ≤ _ := by
        have := Real.rpow_pos_of_pos ht0 (1 / p - p - 1 - (j : ℝ))
        gcongr; linarith


/-- Blueprint: lem:c08_phi_diffeo.  For `|c| ≤ 1/2`, `φ_c` is a smooth increasing bijection of `ℝ`,
the identity on `(-∞,1]`, mapping `(1,∞)` onto itself, with smooth inverse `ψ_c` (identity on
`(-∞,1]`), and `φ_c φ_c'^p = y - b_c`. -/
theorem c08_phi_diffeo (p c : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hc : |c| ≤ 1 / 2) :
    ContDiff ℝ (⊤ : ℕ∞) (c08_phi p c) ∧
    (∀ y, 0 < deriv (c08_phi p c) y) ∧
    (∀ y ≤ 1, c08_phi p c y = y) ∧
    c08_phi p c '' Ioi 1 = Ioi 1 ∧
    Function.Bijective (c08_phi p c) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c08_phi_inv p c) ∧
    (∀ y ≤ 1, c08_phi_inv p c y = y) ∧
    ∀ y, c08_phi p c y * deriv (c08_phi p c) y ^ p = y - c08_phi_b p c y := by
  obtain ⟨hint1, -⟩ := c08_phi_integrand p hp hp1
  obtain ⟨hgC, hg0⟩ := hint1 c hc
  have hp0 : 0 < p := by linarith
  have hpi : 0 < 1 / p := by positivity
  set b := c08_phi_b p c with hbdef
  have hb_le : ∀ t, t ≤ 1 → b t = 0 := fun t ht => by
    simp only [hbdef, c08_phi_b, ite_eq_right_iff]
    intro h; exact absurd h (not_lt.2 ht)
  have hb_abs : ∀ t, |b t| ≤ 1 / 2 := by
    intro t
    simp only [hbdef, c08_phi_b]
    split_ifs with h
    · have hχ0 : 0 ≤ chiPlus t := Real.smoothTransition.nonneg _
      have hχ1 : chiPlus t ≤ 1 := Real.smoothTransition.le_one _
      have ht1 : t ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
      have ht0 : 0 < t ^ (-p) := Real.rpow_pos_of_pos (by linarith) _
      rw [abs_mul, abs_mul, abs_of_nonneg hχ0, abs_of_pos ht0]
      calc |c| * chiPlus t * t ^ (-p) ≤ (1 / 2) * 1 * 1 := by gcongr
        _ = 1 / 2 := by norm_num
    · simp
  have hpos_tb : ∀ t, 1 / 2 < t → 0 < t - b t := by
    intro t ht
    rcases le_or_gt t 1 with h | h
    · rw [hb_le t h]; linarith
    · have := abs_le.1 (hb_abs t); linarith
  set h : ℝ → ℝ := fun t => (t - b t) ^ (1 / p) with hhdef
  have hhpos : ∀ t, 1 / 2 < t → 0 < h t := fun t ht => Real.rpow_pos_of_pos (hpos_tb t ht) _
  have hhC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioi (1 / 2)) := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t ^ (1 / p)) (Ioi (1 / 2)) :=
      contDiffOn_id.rpow_const_of_ne (fun x hx => by
        have : (1:ℝ) / 2 < x := hx
        simp only [id]; linarith)
    refine (h1.add hgC).congr (fun t _ => ?_)
    simp only [hhdef]; ring
  have hhcont : ContinuousOn h (Ioi (1 / 2)) := hhC.continuousOn
  set F : ℝ → ℝ := fun y => 1 + (p + 1) / p * ∫ t in (1:ℝ)..y, h t with hFdef
  have hsub : ∀ y : ℝ, 1 / 2 < y → uIcc (1:ℝ) y ⊆ Ioi (1 / 2) := by
    intro y hy z hz
    rw [mem_Ioi]
    rcases le_total 1 y with h' | h'
    · rw [uIcc_of_le h'] at hz; linarith [hz.1]
    · rw [uIcc_of_ge h'] at hz; linarith [hz.1]
  have hFderiv : ∀ y, 1 / 2 < y → HasDerivAt F ((p + 1) / p * h y) y := by
    intro y hy
    have hI : HasDerivAt (fun u => ∫ t in (1:ℝ)..u, h t) (h y) y :=
      intervalIntegral.integral_hasDerivAt_right ((hhcont.mono (hsub y hy)).intervalIntegrable)
        (hhcont.stronglyMeasurableAtFilter isOpen_Ioi y hy)
        (hhcont.continuousAt (Ioi_mem_nhds hy))
    exact (hI.const_mul ((p + 1) / p)).const_add 1
  have hFC : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Ioi (1 / 2)) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hFderiv y hy).differentiableAt.differentiableWithinAt, ?_⟩
    refine (contDiffOn_const.mul hhC).congr (fun y hy => (hFderiv y hy).deriv)
  have hF_small : ∀ y, 1 / 2 < y → y ≤ 1 → F y = y ^ ((p + 1) / p) := by
    intro y hy hy1
    have hcongr : ∫ t in (1:ℝ)..y, h t = ∫ t in (1:ℝ)..y, t ^ (1 / p) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hy1] at ht
      simp only [hhdef]; rw [hb_le t ht.2, sub_zero]
    simp only [hFdef]
    rw [hcongr, integral_rpow (Or.inl (by linarith)), Real.one_rpow]
    have : 1 / p + 1 = (p + 1) / p := by field_simp; ring
    rw [this]
    field_simp
    ring
  have hF_ge : ∀ y, 1 ≤ y → 1 ≤ F y := by
    intro y hy
    have : 0 ≤ ∫ t in (1:ℝ)..y, h t :=
      intervalIntegral.integral_nonneg hy (fun t ht => (hhpos t (by linarith [ht.1])).le)
    simp only [hFdef]
    have : 0 ≤ (p + 1) / p := by positivity
    nlinarith
  have hFpos : ∀ y, 1 / 2 < y → 0 < F y := by
    intro y hy
    rcases le_or_gt y 1 with h' | h'
    · rw [hF_small y hy h']; exact Real.rpow_pos_of_pos (by linarith) _
    · linarith [hF_ge y h'.le]
  have hexp : (p + 1) / p * (p / (p + 1)) = 1 := by field_simp
  have hφeq : ∀ y, 1 / 2 < y → c08_phi p c y = F y ^ (p / (p + 1)) := by
    intro y hy
    rcases le_or_gt y 1 with h' | h'
    · rw [hF_small y hy h', ← Real.rpow_mul (by linarith), hexp, Real.rpow_one]
      simp [c08_phi, h']
    · simp only [c08_phi, hFdef, hhdef, hbdef, show ¬ (y ≤ 1) from not_le.2 h', ↓reduceIte]
  have hφid : ∀ y ≤ 1, c08_phi p c y = y := fun y hy => by simp [c08_phi, hy]
  -- smoothness
  have hφC_big : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c08_phi p c) (Ioi (1 / 2)) :=
    (hFC.rpow_const_of_ne (fun y hy => (hFpos y hy).ne')).congr hφeq
  have hφC : ContDiff ℝ (⊤ : ℕ∞) (c08_phi p c) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    rcases lt_or_ge y 1 with h' | h'
    · have : c08_phi p c =ᶠ[nhds y] id :=
        Filter.eventually_of_mem (Iio_mem_nhds h') (fun z hz => hφid z (le_of_lt hz))
      exact contDiffAt_id.congr_of_eventuallyEq this
    · exact hφC_big.contDiffAt (Ioi_mem_nhds (by linarith))
  -- derivative
  have hφderiv_big : ∀ y, 1 / 2 < y → HasDerivAt (c08_phi p c) (h y * F y ^ (-1 / (p + 1))) y := by
    intro y hy
    have h1 := (hFderiv y hy).rpow_const (p := p / (p + 1)) (Or.inl (hFpos y hy).ne')
    have h2 : (fun x => F x ^ (p / (p + 1))) =ᶠ[nhds y] c08_phi p c :=
      Filter.eventually_of_mem (Ioi_mem_nhds hy) (fun z hz => (hφeq z hz).symm)
    have h3 := h1.congr_of_eventuallyEq h2.symm
    convert h3 using 1
    have : p / (p + 1) - 1 = -1 / (p + 1) := by field_simp; ring
    rw [this]; field_simp
  have hφderiv_small : ∀ y, y < 1 → HasDerivAt (c08_phi p c) 1 y := by
    intro y hy
    have : c08_phi p c =ᶠ[nhds y] id :=
      Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => hφid z (le_of_lt hz))
    exact (hasDerivAt_id y).congr_of_eventuallyEq this
  have hφ'pos : ∀ y, 0 < deriv (c08_phi p c) y := by
    intro y
    rcases lt_or_ge y 1 with h' | h'
    · rw [(hφderiv_small y h').deriv]; norm_num
    · rw [(hφderiv_big y (by linarith)).deriv]
      exact mul_pos (hhpos y (by linarith)) (Real.rpow_pos_of_pos (hFpos y (by linarith)) _)
  -- the ODE
  have hode : ∀ y, c08_phi p c y * deriv (c08_phi p c) y ^ p = y - b y := by
    intro y
    rcases lt_or_ge y 1 with h' | h'
    · rw [(hφderiv_small y h').deriv, hφid y h'.le, hb_le y h'.le, Real.one_rpow]; ring
    · have hy : 1 / 2 < y := by linarith
      rw [(hφderiv_big y hy).deriv, hφeq y hy]
      have hF := hFpos y hy
      have hh := hhpos y hy
      rw [Real.mul_rpow hh.le (Real.rpow_pos_of_pos hF _).le, ← Real.rpow_mul hF.le]
      have e1 : h y ^ p = y - b y := by
        simp only [hhdef]; rw [← Real.rpow_mul (hpos_tb y hy).le, one_div_mul_cancel hp0.ne',
          Real.rpow_one]
      rw [e1, mul_comm (F y ^ (p / (p + 1))), mul_assoc, ← Real.rpow_add hF]
      have : -1 / (p + 1) * p + p / (p + 1) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero, mul_one]
  -- monotonicity, image, bijectivity
  have hmono : StrictMono (c08_phi p c) := strictMono_of_deriv_pos hφ'pos
  have hφcont : Continuous (c08_phi p c) := hφC.continuous
  have hφ1 : c08_phi p c 1 = 1 := hφid 1 le_rfl
  have hunb : ∀ M : ℝ, ∃ R, M < c08_phi p c R := by
    intro M
    -- `F y ≥ 1 + (p+1)/p (1/2)^{1/p} (y - 1)` for `y ≥ 1`
    set κ := (p + 1) / p * (1 / 2 : ℝ) ^ (1 / p) with hκ
    have hκpos : 0 < κ := by positivity
    have hFlin : ∀ y, 1 ≤ y → 1 + κ * (y - 1) ≤ F y := by
      intro y hy
      have hh2 : ∀ t ∈ Icc (1:ℝ) y, (1 / 2 : ℝ) ^ (1 / p) ≤ h t := by
        intro t ht
        apply Real.rpow_le_rpow (by norm_num) _ hpi.le
        have := abs_le.1 (hb_abs t); linarith [ht.1]
      have hint : (1 / 2 : ℝ) ^ (1 / p) * (y - 1) ≤ ∫ t in (1:ℝ)..y, h t := by
        have := intervalIntegral.integral_mono_on hy (intervalIntegrable_const (μ := volume))
          ((hhcont.mono (hsub y (by linarith))).intervalIntegrable) hh2
        simpa [mul_comm] using this
      simp only [hFdef, hκ]
      have : 0 ≤ (p + 1) / p := by positivity
      nlinarith
    -- choose `R` with `1 + κ (R - 1) ≥ (max M 1 + 1)^{(p+1)/p}`
    set T := (max M 1 + 1) ^ ((p + 1) / p)
    refine ⟨1 + T / κ, ?_⟩
    have hR : 1 ≤ 1 + T / κ := by have : 0 ≤ T := by positivity
                                  have : 0 ≤ T / κ := by positivity
                                  linarith
    have hFR : T ≤ F (1 + T / κ) := by
      have := hFlin _ hR
      have e : 1 + κ * (1 + T / κ - 1) = 1 + T := by field_simp; ring
      rw [e] at this; linarith
    rw [hφeq _ (by linarith)]
    have hT0 : 0 < max M 1 + 1 := by have := le_max_right M 1; linarith
    calc M < max M 1 + 1 := by have := le_max_left M 1; linarith
      _ = T ^ (p / (p + 1)) := by
          rw [← Real.rpow_mul hT0.le, hexp, Real.rpow_one]
      _ ≤ F (1 + T / κ) ^ (p / (p + 1)) :=
          Real.rpow_le_rpow (by positivity) hFR (by positivity)
  have hsurj : Function.Surjective (c08_phi p c) := by
    intro y
    rcases le_or_gt y 1 with h' | h'
    · exact ⟨y, hφid y h'⟩
    · obtain ⟨R, hR⟩ := hunb y
      have hR1 : 1 ≤ R := by
        by_contra hneg; push Not at hneg
        have := hmono hneg; rw [hφ1] at this; linarith
      obtain ⟨z, hz, hz'⟩ := intermediate_value_Icc hR1 hφcont.continuousOn
        ⟨by rw [hφ1]; exact h'.le, hR.le⟩
      exact ⟨z, hz'⟩
  have hbij : Function.Bijective (c08_phi p c) := ⟨hmono.injective, hsurj⟩
  have himg : c08_phi p c '' Ioi 1 = Ioi 1 := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩; have := hmono (show (1:ℝ) < z from hz); rw [hφ1] at this; exact this
    · intro hy
      obtain ⟨z, hz⟩ := hsurj y
      refine ⟨z, ?_, hz⟩
      by_contra hneg
      have : c08_phi p c z ≤ c08_phi p c 1 := hmono.monotone (not_lt.1 hneg)
      rw [hz, hφ1] at this; exact absurd hy (not_lt.2 this)
  -- the inverse
  set e := (hmono.orderIsoOfSurjective (c08_phi p c) hsurj).toHomeomorph with hedef
  have hecoe : (e : ℝ → ℝ) = c08_phi p c := rfl
  have hψeq : c08_phi_inv p c = e.symm := by
    ext y
    apply hmono.injective
    rw [show c08_phi_inv p c = Function.invFun (c08_phi p c) from rfl,
      Function.invFun_eq (hsurj y)]
    have := e.apply_symm_apply y
    rw [hecoe] at this; exact this.symm
  have hψC : ContDiff ℝ (⊤ : ℕ∞) (c08_phi_inv p c) := by
    rw [hψeq]
    exact e.contDiff_symm_deriv (f' := deriv (c08_phi p c)) (fun x => (hφ'pos x).ne')
      (fun x => (hφC.differentiable (by simp) x).hasDerivAt) hφC
  have hψid : ∀ y ≤ 1, c08_phi_inv p c y = y := by
    intro y hy
    have := Function.leftInverse_invFun hbij.1 y
    rw [hφid y hy] at this; exact this
  exact ⟨hφC, hφ'pos, hφid, himg, hbij, hψC, hψid, hode⟩

/-- Consequences of lem:c08_phi_diffeo: `ψ_c` is a two-sided inverse of `φ_c` and
`φ_c'(ψ_c y) ψ_c'(y) = 1 = ψ_c'(φ_c y) φ_c'(y)`. -/
theorem c08_aux_phi_inverse (p c : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hc : |c| ≤ 1 / 2) :
    (∀ y, c08_phi_inv p c (c08_phi p c y) = y) ∧ (∀ y, c08_phi p c (c08_phi_inv p c y) = y) ∧
    (∀ y, deriv (c08_phi p c) (c08_phi_inv p c y) * deriv (c08_phi_inv p c) y = 1) ∧
    (∀ y, deriv (c08_phi_inv p c) (c08_phi p c y) * deriv (c08_phi p c) y = 1) := by
  obtain ⟨hφ, -, -, -, hbij, hψ, -, -⟩ := c08_phi_diffeo p c hp hp1 hc
  have hl : Function.LeftInverse (c08_phi_inv p c) (c08_phi p c) :=
    Function.leftInverse_invFun hbij.1
  have hr : Function.RightInverse (c08_phi_inv p c) (c08_phi p c) :=
    Function.rightInverse_invFun hbij.2
  have hφd : Differentiable ℝ (c08_phi p c) := hφ.differentiable (by simp)
  have hψd : Differentiable ℝ (c08_phi_inv p c) := hψ.differentiable (by simp)
  refine ⟨hl, hr, fun y => ?_, fun y => ?_⟩
  · have h1 : c08_phi p c ∘ c08_phi_inv p c = id := funext hr
    have := deriv_comp y (hφd _) (hψd y)
    rw [h1, deriv_id] at this
    exact this.symm
  · have h1 : c08_phi_inv p c ∘ c08_phi p c = id := funext hl
    have := deriv_comp y (hψd _) (hφd y)
    rw [h1, deriv_id] at this
    exact this.symm

/-- The integrand `g_c(t) = (t - b_c(t))^{1/p} - t^{1/p}` of lem:c08_phi_integrand. -/
def c08_aux_g (p c t : ℝ) : ℝ := (t - c08_phi_b p c t) ^ (1 / p) - t ^ (1 / p)

/-- `I_c(y) = ∫₁^y g_c`. -/
def c08_aux_I (p c y : ℝ) : ℝ := ∫ t in (1:ℝ)..y, c08_aux_g p c t

/-- `E_c(y) = (p+1)/p · y^{-(p+1)/p} I_c(y)`. -/
def c08_aux_E (p c y : ℝ) : ℝ := (p + 1) / p * (y ^ (-(p + 1) / p) * c08_aux_I p c y)

/-- Properties of `I_c`. -/
theorem c08_aux_I_props (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ c : ℝ, |c| ≤ 1 / 2 →
      (∀ y, 1 / 2 < y → HasDerivAt (c08_aux_I p c) (c08_aux_g p c y) y) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c08_aux_I p c) (Ioi (1 / 2)) ∧
      (∀ y ∈ Ioc (1 / 2 : ℝ) 1, c08_aux_I p c y = 0)) ∧
    ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ y : ℝ, 1 ≤ y →
      |iteratedDeriv i (c08_aux_I p c) y| ≤ K * |c| * y ^ ((1 / p - p) - i) := by
  obtain ⟨h1, h2⟩ := c08_phi_integrand p hp hp1
  have hp0 : 0 < p := by linarith
  have hsub : ∀ y : ℝ, 1 / 2 < y → uIcc (1:ℝ) y ⊆ Ioi (1 / 2) := by
    intro y hy z hz
    rw [mem_Ioi]
    rcases le_total 1 y with h' | h'
    · rw [uIcc_of_le h'] at hz; linarith [hz.1]
    · rw [uIcc_of_ge h'] at hz; linarith [hz.1]
  have hder : ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ y, 1 / 2 < y →
      HasDerivAt (c08_aux_I p c) (c08_aux_g p c y) y := by
    intro c hc y hy
    have hcont : ContinuousOn (c08_aux_g p c) (Ioi (1 / 2)) := (h1 c hc).1.continuousOn
    exact intervalIntegral.integral_hasDerivAt_right ((hcont.mono (hsub y hy)).intervalIntegrable)
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi y hy) (hcont.continuousAt (Ioi_mem_nhds hy))
  have hI0 : ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ y ∈ Ioc (1 / 2 : ℝ) 1, c08_aux_I p c y = 0 := by
    intro c hc y hy
    unfold c08_aux_I
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun t ht => ?_)]
    · simp
    · rw [uIcc_of_ge hy.2] at ht
      exact (h1 c hc).2 t ⟨by linarith [hy.1, ht.1], ht.2⟩
  refine ⟨fun c hc => ⟨hder c hc, ?_, hI0 c hc⟩, fun i => ?_⟩
  · rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hder c hc y hy).differentiableAt.differentiableWithinAt, ?_⟩
    exact (h1 c hc).1.congr (fun y hy => (hder c hc y hy).deriv)
  · have hs : 0 < 1 / p - p := by
      have : 1 < 1 / p := by rw [lt_div_iff₀ hp0]; linarith
      linarith
    rcases i with _ | j
    · obtain ⟨C, hC0, hC⟩ := h2 0
      refine ⟨C / (1 / p - p), by positivity, fun c hc y hy => ?_⟩
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero]
      unfold c08_aux_I
      have hcont : ContinuousOn (fun t : ℝ => t ^ (1 / p - p - 1)) (Icc 1 y) :=
        fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt
      have hb : ∀ t ∈ Ioc (1:ℝ) y, ‖c08_aux_g p c t‖ ≤ C * |c| * t ^ (1 / p - p - 1) := by
        intro t ht
        have := hC c hc t (le_of_lt ht.1)
        simpa [c08_aux_g] using this
      have := intervalIntegral.norm_integral_le_of_norm_le hy (Eventually.of_forall hb)
        ((hcont.intervalIntegrable_of_Icc (μ := volume) hy).const_mul (C * |c|))
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        show 1 / p - p - 1 + 1 = 1 / p - p by ring, Real.one_rpow]
      have hy0 : 0 ≤ y ^ (1 / p - p) := Real.rpow_nonneg (by linarith) _
      have e : C * |c| * ((y ^ (1 / p - p) - 1) / (1 / p - p)) =
          C / (1 / p - p) * |c| * (y ^ (1 / p - p) - 1) := by ring
      rw [e]
      have : 0 ≤ C / (1 / p - p) * |c| := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) this
    · obtain ⟨C, hC0, hC⟩ := h2 j
      refine ⟨C, hC0.le, fun c hc y hy => ?_⟩
      rw [iteratedDeriv_succ']
      have : deriv (c08_aux_I p c) =ᶠ[nhds y] c08_aux_g p c :=
        Filter.eventually_of_mem (Ioi_mem_nhds (show (1:ℝ)/2 < y by linarith))
          (fun x hx => (hder c hc x hx).deriv)
      rw [this.iteratedDeriv_eq]
      have e : c08_aux_g p c = fun t => (t - c08_phi_b p c t) ^ (1 / p) - t ^ (1 / p) := rfl
      rw [e]; refine (hC c hc y hy).trans (le_of_eq ?_); congr 2; push_cast; ring


/-- Properties of `E_c`. -/
theorem c08_aux_E_props (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ c : ℝ, |c| ≤ 1 / 2 →
      ContDiffOn ℝ (⊤ : ℕ∞) (c08_aux_E p c) (Ioi (1 / 2)) ∧
      (∀ y ∈ Ioc (1 / 2 : ℝ) 1, c08_aux_E p c y = 0)) ∧
    ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ y : ℝ, 1 ≤ y →
      |iteratedDeriv i (c08_aux_E p c) y| ≤ K * |c| * y ^ (-1 - p - i) := by
  obtain ⟨hI1, hI2⟩ := c08_aux_I_props p hp hp1
  have hp0 : 0 < p := by linarith
  have hpow : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ (-(p + 1) / p)) (Ioi (1 / 2)) :=
    contDiffOn_id.rpow_const_of_ne (fun x hx => by
      have : (1:ℝ) / 2 < x := hx
      simp only [id]; linarith)
  refine ⟨fun c hc => ⟨?_, fun y hy => ?_⟩, fun i => ?_⟩
  · exact contDiffOn_const.mul (hpow.mul (hI1 c hc).2.1)
  · simp [c08_aux_E, (hI1 c hc).2.2 y hy]
  · obtain ⟨P, hP0, hP⟩ := c08_aux_iter_rpow_pow (-(p + 1) / p) i
    obtain ⟨K, hK0, hK⟩ := c08_aux_uniform_const (fun i K => ∀ c : ℝ, |c| ≤ 1 / 2 → ∀ y : ℝ,
      1 ≤ y → |iteratedDeriv i (c08_aux_I p c) y| ≤ K * |c| * y ^ ((1 / p - p) - i))
      (fun i K K' hK h c hc t ht => (h c hc t ht).trans (by
          have := Real.rpow_pos_of_pos (show (0:ℝ) < t by linarith) ((1 / p - p) - i)
          gcongr)) hI2 i
    refine ⟨(p + 1) / p * (2 ^ i * (P * K)), by positivity, fun c hc y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    have e : c08_aux_E p c =
        fun y => (p + 1) / p * ((fun y => y ^ (-(p + 1) / p) * c08_aux_I p c y) y) := rfl
    rw [e, iteratedDeriv_const_mul_field, abs_mul, abs_of_pos (by positivity : 0 < (p + 1) / p)]
    have hIc : ContDiffAt ℝ i (c08_aux_I p c) y :=
      ((hI1 c hc).2.1.contDiffAt (Ioi_mem_nhds (by linarith))).of_le (by exact_mod_cast le_top)
    have := c08_aux_leibniz (fun y : ℝ => y ^ (-(p + 1) / p)) (c08_aux_I p c) y hy0 i
      (contDiffAt_rpow_const (Or.inl hy0.ne')) hIc P (K * |c|) (-(p + 1) / p) (1 / p - p)
      (fun j hj => hP j hj y hy0) (fun j hj => hK j hj c hc y hy)
    have e2 : -(p + 1) / p + (1 / p - p) - i = -1 - p - i := by field_simp; ring
    rw [e2] at this
    calc (p + 1) / p * |iteratedDeriv i (fun y => y ^ (-(p + 1) / p) * c08_aux_I p c y) y|
        ≤ (p + 1) / p * (2 ^ i * (P * (K * |c|)) * y ^ (-1 - p - i)) := by gcongr
      _ = _ := by ring

/-- `|x^q - 1| ≤ |x - 1|` for `x ≥ 0`, `q ∈ [0,1]`. -/
theorem c08_aux_rpow_sub_one_le' {x q : ℝ} (hx : 0 ≤ x) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |x ^ q - 1| ≤ |x - 1| := by
  rcases le_total 1 x with h | h
  · have h1 : 1 ≤ x ^ q := Real.one_le_rpow h hq0
    have h2 : x ^ q ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h hq1
    rw [Real.rpow_one] at h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · have h1 : x ^ q ≤ 1 := Real.rpow_le_one hx h hq0
    have h2 : x ^ (1:ℝ) ≤ x ^ q := Real.rpow_le_rpow_of_exponent_ge' hx h hq0 hq1
    rw [Real.rpow_one] at h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- Smallness of `E_c` for small `|c|`. -/
theorem c08_aux_E_small (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c1 : ℝ, 0 < c1 ∧ c1 ≤ 1 / 2 ∧ ∀ c : ℝ, |c| ≤ c1 → ∀ y : ℝ, 1 / 2 < y →
      |c08_aux_E p c y| ≤ 1 / 2 := by
  obtain ⟨hE1, hE2⟩ := c08_aux_E_props p hp hp1
  obtain ⟨K, hK0, hK⟩ := hE2 0
  refine ⟨min (1 / 2) (1 / (2 * (K + 1))), by positivity, min_le_left _ _, fun c hc y hy => ?_⟩
  have hc2 : |c| ≤ 1 / 2 := hc.trans (min_le_left _ _)
  rcases le_or_gt y 1 with h | h
  · rw [(hE1 c hc2).2 y ⟨hy, h⟩]; norm_num
  · have := hK c hc2 y h.le
    simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at this
    have hpw : y ^ (-1 - p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
    have hpw0 : 0 ≤ y ^ (-1 - p) := (Real.rpow_pos_of_pos (by linarith) _).le
    have hc3 : |c| ≤ 1 / (2 * (K + 1)) := hc.trans (min_le_right _ _)
    have : K * |c| ≤ 1 / 2 := by
      calc K * |c| ≤ (K + 1) * (1 / (2 * (K + 1))) := by
            apply mul_le_mul (by linarith) hc3 (abs_nonneg _) (by linarith)
        _ = 1 / 2 := by field_simp
    have hK' := hK c hc2 y h.le
    simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at hK'
    calc |c08_aux_E p c y| ≤ K * |c| * y ^ (-1 - p) := hK'
      _ ≤ K * |c| * 1 := by gcongr
      _ ≤ 1 / 2 := by linarith


/-- `φ_c(y) = y (1 + E_c(y))^{p/(p+1)}` on `(1/2,∞)` (when `1 + E_c(y) ≥ 0`). -/
theorem c08_aux_phi_eq (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (c : ℝ) (hc : |c| ≤ 1 / 2)
    (y : ℝ) (hy : 1 / 2 < y) (hE : 0 ≤ 1 + c08_aux_E p c y) :
    c08_phi p c y = y * (1 + c08_aux_E p c y) ^ (p / (p + 1)) := by
  obtain ⟨hI1, -⟩ := c08_aux_I_props p hp hp1
  obtain ⟨hE1, -⟩ := c08_aux_E_props p hp hp1
  have hp0 : 0 < p := by linarith
  rcases le_or_gt y 1 with h | h
  · rw [(hE1 c hc).2 y ⟨hy, h⟩]; simp [c08_phi, h]
  · have hy0 : 0 < y := by linarith
    simp only [c08_phi, show ¬ (y ≤ 1) from not_le.2 h, ↓reduceIte]
    have hgc : ContinuousOn (c08_aux_g p c) (uIcc 1 y) := by
      refine ((c08_phi_integrand p hp hp1).1 c hc).1.continuousOn.mono ?_
      intro z hz; rw [uIcc_of_le h.le] at hz; simp only [mem_Ioi]; linarith [hz.1]
    have hsplit : ∫ t in (1:ℝ)..y, (t - c08_phi_b p c t) ^ (1 / p) =
        (∫ t in (1:ℝ)..y, t ^ (1 / p)) + c08_aux_I p c y := by
      unfold c08_aux_I
      rw [← intervalIntegral.integral_add (intervalIntegral.intervalIntegrable_rpow' (by
        have : 0 < 1 / p := by positivity
        linarith)) hgc.intervalIntegrable]
      apply intervalIntegral.integral_congr
      intro t _; simp only [c08_aux_g]; ring
    rw [hsplit, integral_rpow (Or.inl (by have : 0 < 1 / p := by positivity
                                          linarith)), Real.one_rpow]
    set a := (p + 1) / p with ha
    have ha' : 1 / p + 1 = a := by rw [ha]; field_simp; ring
    rw [ha']
    have hapos : 0 < a := by positivity
    have hya : 0 < y ^ a := Real.rpow_pos_of_pos hy0 a
    have hE' : c08_aux_E p c y = a * ((y ^ a)⁻¹ * c08_aux_I p c y) := by
      unfold c08_aux_E
      rw [← ha, show -(p + 1) / p = -a by rw [ha]; ring, Real.rpow_neg hy0.le]
    have hbr : 1 + a * ((y ^ a - 1) / a + c08_aux_I p c y) = y ^ a * (1 + c08_aux_E p c y) := by
      rw [hE']; field_simp; ring
    rw [hbr, Real.mul_rpow hya.le hE, ← Real.rpow_mul hy0.le]
    have : a * (p / (p + 1)) = 1 := by rw [ha]; field_simp
    rw [this, Real.rpow_one]

/-- All-order bounds for `φ_c - id` on `[1,∞)` for small `|c|`. -/
theorem c08_aux_phi_sub_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c1 : ℝ, 0 < c1 ∧ c1 ≤ 1 / 2 ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, |c| ≤ c1 → ∀ y : ℝ,
      1 ≤ y → |iteratedDeriv j (fun y => c08_phi p c y - y) y| ≤ C * |c| * y ^ (-p - j) := by
  obtain ⟨c1, hc1, hc1', hsmall⟩ := c08_aux_E_small p hp hp1
  obtain ⟨hE1, hE2⟩ := c08_aux_E_props p hp hp1
  have hp0 : 0 < p := by linarith
  set q := p / (p + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by linarith)]; linarith
  -- bounds for `H = (1+E)^q - 1`
  have hH : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ c1 → ∀ y : ℝ, 1 ≤ y →
      |iteratedDeriv i (fun y => (1 + c08_aux_E p c y) ^ q - 1) y| ≤
        K * |c| * y ^ (-1 - p - i) := by
    intro i
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      obtain ⟨K, hK0, hK⟩ := hE2 0
      refine ⟨K, hK0, fun c hc y hy => ?_⟩
      have h1 := hK c (hc.trans hc1') y hy
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at h1 ⊢
      have h2 := hsmall c hc y (by linarith)
      refine (c08_aux_rpow_sub_one_le' (by linarith [(abs_le.1 h2).1]) hq0 hq1).trans ?_
      simpa using h1
    · obtain ⟨C, hC0, hC⟩ := c08_aux_comp_rpow_bound q i hi
      obtain ⟨KE, hKE0, hKE⟩ := c08_aux_uniform_const (fun i K => ∀ c : ℝ, |c| ≤ 1 / 2 →
        ∀ y : ℝ, 1 ≤ y → |iteratedDeriv i (c08_aux_E p c) y| ≤ K * |c| * y ^ (-1 - p - i))
        (fun i K K' hK h c hc t ht => (h c hc t ht).trans (by
          have := Real.rpow_pos_of_pos (show (0:ℝ) < t by linarith) (-1 - p - i)
          gcongr)) hE2 i
      set B := max 1 KE
      refine ⟨C * B ^ i, by positivity, fun c hc y hy => ?_⟩
      have hc2 : |c| ≤ 1 / 2 := hc.trans hc1'
      have hy0 : 0 < y := by linarith
      have e : (fun y => (1 + c08_aux_E p c y) ^ q - 1) =
          fun y => (-1) + (1 + c08_aux_E p c y) ^ q := by funext y; ring
      rw [e, iteratedDeriv_const_add hi]
      have hf : ∀ x, 1 / 2 < x → 1 + c08_aux_E p c x ∈ Icc (1 / 2 : ℝ) 2 := by
        intro x hx
        have := abs_le.1 (hsmall c hc x hx)
        exact ⟨by linarith, by linarith⟩
      have key := hC (fun y => 1 + c08_aux_E p c y) (Ioi (1 / 2)) isOpen_Ioi
        ((contDiffOn_const.add (hE1 c hc2).1).of_le (by exact_mod_cast le_top))
        (fun x hx => by have := (hf x hx).1; simp only [mem_Ioi]; linarith) y
        (show (1:ℝ) / 2 < y by linarith) hy (hf y (by linarith)) B |c| (1 + p)
        (le_max_left _ _) (abs_nonneg c) (by linarith) (by linarith) ?_
      · calc _ ≤ _ := key
          _ = _ := by ring_nf
      · intro j hj1 hj
        rw [iteratedDeriv_const_add (by omega)]
        refine (hKE j hj c hc2 y hy).trans ?_
        have := Real.rpow_pos_of_pos hy0 (-1 - p - j)
        have hB : KE ≤ B := le_max_right _ _
        calc KE * |c| * y ^ (-1 - p - j) ≤ B * |c| * y ^ (-1 - p - j) := by gcongr
          _ = _ := by ring_nf
  refine ⟨c1, hc1, hc1', fun j => ?_⟩
  obtain ⟨P, hP0, hP⟩ := c08_aux_iter_rpow_pow 1 j
  obtain ⟨K, hK0, hK⟩ := c08_aux_uniform_const (fun i K => ∀ c : ℝ, |c| ≤ c1 → ∀ y : ℝ,
      1 ≤ y → |iteratedDeriv i (fun y => (1 + c08_aux_E p c y) ^ q - 1) y| ≤
        K * |c| * y ^ (-1 - p - i))
      (fun i K K' hK h c hc t ht => (h c hc t ht).trans (by
          have := Real.rpow_pos_of_pos (show (0:ℝ) < t by linarith) (-1 - p - i)
          gcongr)) hH j
  refine ⟨2 ^ j * (P * K) + 1, by positivity, fun c hc y hy => ?_⟩
  have hc2 : |c| ≤ 1 / 2 := hc.trans hc1'
  have hy0 : 0 < y := by linarith
  have heq : (fun y => c08_phi p c y - y) =ᶠ[nhds y]
      fun y => y ^ (1:ℝ) * ((1 + c08_aux_E p c y) ^ q - 1) :=
    Filter.eventually_of_mem (Ioi_mem_nhds (show (1:ℝ) / 2 < y by linarith)) (fun x hx => by
      have hx' : (1:ℝ) / 2 < x := hx
      show c08_phi p c x - x = x ^ (1:ℝ) * ((1 + c08_aux_E p c x) ^ q - 1)
      rw [c08_aux_phi_eq p hp hp1 c hc2 x hx' (by linarith [(abs_le.1 (hsmall c hc x hx')).1]),
        Real.rpow_one]; ring)
  rw [heq.iteratedDeriv_eq]
  have hHc : ContDiffAt ℝ j (fun y => (1 + c08_aux_E p c y) ^ q - 1) y := by
    have : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (1 + c08_aux_E p c y) ^ q - 1) (Ioi (1 / 2)) :=
      ((contDiffOn_const.add (hE1 c hc2).1).rpow_const_of_ne (fun x hx => by
        have := (abs_le.1 (hsmall c hc x hx)).1; linarith)).sub contDiffOn_const
    exact (this.contDiffAt (Ioi_mem_nhds (by linarith))).of_le (by exact_mod_cast le_top)
  have := c08_aux_leibniz (fun y : ℝ => y ^ (1:ℝ)) (fun y => (1 + c08_aux_E p c y) ^ q - 1)
    y hy0 j (contDiffAt_rpow_const (Or.inl hy0.ne')) hHc P (K * |c|) 1 (-1 - p)
    (fun i hi => hP i hi y hy0) (fun i hi => hK i hi c hc y hy)
  calc _ ≤ _ := this
    _ = 2 ^ j * (P * K) * |c| * y ^ (-p - (j:ℝ)) := by ring_nf
    _ ≤ _ := by
      have := Real.rpow_pos_of_pos hy0 (-p - (j:ℝ))
      gcongr; linarith


/-- All derivatives of `φ_c - id` vanish on `(-∞,1]`. -/
theorem c08_aux_phi_sub_vanish (p c : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hc : |c| ≤ 1 / 2)
    (j : ℕ) (y : ℝ) (hy : y ≤ 1) : iteratedDeriv j (fun y => c08_phi p c y - y) y = 0 := by
  obtain ⟨hφ, -, hφid, -⟩ := c08_phi_diffeo p c hp hp1 hc
  have hcont : Continuous (iteratedDeriv j (fun y => c08_phi p c y - y)) :=
    (hφ.sub contDiff_id).continuous_iteratedDeriv j (by exact_mod_cast le_top)
  have hsub : Iio (1:ℝ) ⊆ {x | iteratedDeriv j (fun y => c08_phi p c y - y) x = 0} := by
    intro x hx
    have : (fun y => c08_phi p c y - y) =ᶠ[nhds x] fun _ => (0:ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hx) (fun z hz => by
        simp only; rw [hφid z (le_of_lt hz)]; ring)
    simp only [mem_ofPred_eq]
    rw [this.iteratedDeriv_eq]; simp
  have hcl := (isClosed_eq hcont continuous_const).closure_subset_iff.2 hsub
  rw [closure_Iio] at hcl
  exact hcl hy

/-- All-order bounds for `φ_c - id` in terms of `⟨y⟩`. -/
theorem c08_aux_phi_sub_bound_jb (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c1 : ℝ, 0 < c1 ∧ c1 ≤ 1 / 2 ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, |c| ≤ c1 → ∀ y : ℝ,
      |iteratedDeriv j (fun y => c08_phi p c y - y) y| ≤ C * |c| * jb y ^ (-p - (j : ℝ)) := by
  obtain ⟨c1, hc1, hc1', hb⟩ := c08_aux_phi_sub_bound p hp hp1
  refine ⟨c1, hc1, hc1', fun j => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hb j
  refine ⟨C * 2 ^ (p + j), by positivity, fun c hc y => ?_⟩
  rcases le_or_gt y 1 with h | h
  · rw [c08_aux_phi_sub_vanish p c hp hp1 (hc.trans hc1') j y h, abs_zero]
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-p - (j : ℝ))
    positivity
  · refine (hCb c hc y h.le).trans ?_
    have hjb : jb y ≤ 2 * y := by
      have := c08_aux_jb_le_one_add y
      rw [abs_of_pos (by linarith)] at this; linarith
    have key := c08_aux_rpow_neg_le_of_le (c08_aux_jb_pos y)
      (show (0:ℝ) ≤ p + j by positivity) hjb
    rw [show -(p + (j:ℝ)) = -p - j by ring] at key
    calc C * |c| * y ^ (-p - (j:ℝ)) ≤ C * |c| * (2 ^ (p + j) * jb y ^ (-p - (j:ℝ))) := by
          gcongr
      _ = _ := by ring

/-- Blueprint: lem:c08_phi_bounds.  There is `c₀ ∈ (0,1/2]` such that for `|c| ≤ c₀`:
`|∂^j(φ_c(y) - y)| ≤ C_j |c| ⟨y⟩^{-p-j}`, `|φ_c' - 1| ≤ 1/2`, `|φ_c(y) - y| ≤ 1/2`,
`⟨y⟩/2 ≤ ⟨φ_c(y)⟩ ≤ 2⟨y⟩`, `|(φ_c')^{p+1} - 1| + ⟨y⟩|∂_y (φ_c')^{p+1}| ≤ C|c|⟨y⟩^{-p-1}`;
all these quantities vanish on `y ≤ 1`. -/
theorem c08_phi_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ 1 / 2 ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ,
        |iteratedDeriv j (fun y => c08_phi p c y - y) y| ≤ C * |c| * jb y ^ (-p - (j : ℝ))) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ,
        |deriv (c08_phi p c) y ^ (p + 1) - 1| +
            jb y * |deriv (fun y => deriv (c08_phi p c) y ^ (p + 1)) y| ≤
          C * |c| * jb y ^ (-p - 1)) ∧
      (∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ,
        |deriv (c08_phi p c) y - 1| ≤ 1 / 2 ∧ |c08_phi p c y - y| ≤ 1 / 2 ∧
        jb y / 2 ≤ jb (c08_phi p c y) ∧ jb (c08_phi p c y) ≤ 2 * jb y) ∧
      (∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ, y ≤ 1 →
        (∀ j : ℕ, iteratedDeriv j (fun y => c08_phi p c y - y) y = 0) ∧
        deriv (c08_phi p c) y ^ (p + 1) - 1 = 0 ∧
        deriv (fun y => deriv (c08_phi p c) y ^ (p + 1)) y = 0) := by
  obtain ⟨c1, hc1, hc1', hb⟩ := c08_aux_phi_sub_bound_jb p hp hp1
  obtain ⟨C0, hC0, hb0⟩ := hb 0
  obtain ⟨C1, hC1, hb1⟩ := hb 1
  obtain ⟨C2, hC2, hb2⟩ := hb 2
  have hp0 : 0 < p := by linarith
  set c0 := min c1 (min (1 / (2 * (C0 + 1))) (1 / (2 * (C1 + 1)))) with hc0def
  have hc0pos : 0 < c0 := by positivity
  have hc0c1 : c0 ≤ c1 := min_le_left _ _
  have hc0half : c0 ≤ 1 / 2 := hc0c1.trans hc1'
  -- basic facts for `|c| ≤ c0`
  have hjbneg : ∀ (y a : ℝ), 0 ≤ a → jb y ^ (-a) ≤ 1 := fun y a ha =>
    Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by linarith)
  have hsmallC : ∀ (C : ℝ), 0 < C → ∀ c : ℝ, |c| ≤ 1 / (2 * (C + 1)) → C * |c| ≤ 1 / 2 := by
    intro C hC c hc
    calc C * |c| ≤ (C + 1) * (1 / (2 * (C + 1))) :=
          mul_le_mul (by linarith) hc (abs_nonneg _) (by linarith)
      _ = 1 / 2 := by field_simp
  have hd1 : ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ,
      |deriv (c08_phi p c) y - 1| ≤ C1 * |c| * jb y ^ (-p - 1) := by
    intro c hc y
    have hc12 : |c| ≤ 1 / 2 := hc.trans hc0half
    obtain ⟨hφ, -⟩ := c08_phi_diffeo p c hp hp1 hc12
    have := hb1 c (hc.trans hc0c1) y
    rw [(c08_aux_iteratedDeriv_sub_id (hφ.of_le (by norm_cast))).1] at this
    simpa using this
  have hd2 : ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ,
      |deriv (deriv (c08_phi p c)) y| ≤ C2 * |c| * jb y ^ (-p - 2) := by
    intro c hc y
    have hc12 : |c| ≤ 1 / 2 := hc.trans hc0half
    obtain ⟨hφ, -⟩ := c08_phi_diffeo p c hp hp1 hc12
    have := hb2 c (hc.trans hc0c1) y
    rw [(c08_aux_iteratedDeriv_sub_id (hφ.of_le (by norm_cast))).2] at this
    simpa using this
  have hd0 : ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ, |c08_phi p c y - y| ≤ C0 * |c| * jb y ^ (-p) := by
    intro c hc y
    have := hb0 c (hc.trans hc0c1) y
    simpa using this
  have hhalf1 : ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ, |deriv (c08_phi p c) y - 1| ≤ 1 / 2 := by
    intro c hc y
    refine (hd1 c hc y).trans ?_
    have h1 := hjbneg y (p + 1) (by linarith)
    rw [show -(p + 1) = -p - 1 by ring] at h1
    have h2 := hsmallC C1 hC1 c (hc.trans ((min_le_right _ _).trans (min_le_right _ _)))
    calc C1 * |c| * jb y ^ (-p - 1) ≤ C1 * |c| * 1 := by gcongr
      _ ≤ 1 / 2 := by linarith
  have hhalf0 : ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ, |c08_phi p c y - y| ≤ 1 / 2 := by
    intro c hc y
    refine (hd0 c hc y).trans ?_
    have h1 := hjbneg y p hp0.le
    have h2 := hsmallC C0 hC0 c (hc.trans ((min_le_right _ _).trans (min_le_left _ _)))
    calc C0 * |c| * jb y ^ (-p) ≤ C0 * |c| * 1 := by gcongr
      _ ≤ 1 / 2 := by linarith
  -- derivative of `(φ')^{p+1}`
  have hder : ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ,
      deriv (fun y => deriv (c08_phi p c) y ^ (p + 1)) y =
        deriv (deriv (c08_phi p c)) y * (p + 1) * deriv (c08_phi p c) y ^ p := by
    intro c hc y
    have hc12 : |c| ≤ 1 / 2 := hc.trans hc0half
    obtain ⟨hφ, hφpos, -⟩ := c08_phi_diffeo p c hp hp1 hc12
    have hdd : Differentiable ℝ (deriv (c08_phi p c)) := by
      simpa using (hφ.iterate_deriv 1).differentiable (by simp)
    have := (hdd y).hasDerivAt.rpow_const (p := p + 1) (Or.inl (hφpos y).ne')
    rw [this.deriv, show p + 1 - 1 = p by ring]
  refine ⟨c0, hc0pos, hc0half, fun j => ?_, ⟨7 * C1 + 4 * C2 + 1, by positivity,
    fun c hc y => ?_⟩, fun c hc y => ⟨hhalf1 c hc y, hhalf0 c hc y, ?_, ?_⟩,
    fun c hc y hy => ⟨fun j => c08_aux_phi_sub_vanish p c hp hp1 (hc.trans hc0half) j y hy, ?_, ?_⟩⟩
  · obtain ⟨C, hC, hCb⟩ := hb j
    exact ⟨C, hC, fun c hc y => hCb c (hc.trans hc0c1) y⟩
  · have hda := abs_le.1 (hhalf1 c hc y)
    have e1 := c08_aux_rpow_sub_one_le (t := deriv (c08_phi p c) y) (q := p + 1) (by linarith)
      (by linarith) (by linarith) (by linarith)
    have hdp : deriv (c08_phi p c) y ^ p ≤ 2 := by
      calc deriv (c08_phi p c) y ^ p ≤ 2 ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
        _ ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
        _ = 2 := Real.rpow_one 2
    have hdp0 : 0 ≤ deriv (c08_phi p c) y ^ p := Real.rpow_nonneg (by linarith) _
    rw [hder c hc y]
    have hjb := c08_aux_jb_pos y
    have hjbe : jb y * jb y ^ (-p - 2) = jb y ^ (-p - 1) := by
      rw [← Real.rpow_one_add' hjb.le (by linarith)]; ring_nf
    have h2 : jb y * |deriv (deriv (c08_phi p c)) y * (p + 1) * deriv (c08_phi p c) y ^ p| ≤
        4 * C2 * |c| * jb y ^ (-p - 1) := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < p + 1), abs_of_nonneg hdp0]
      have := hd2 c hc y
      calc jb y * (|deriv (deriv (c08_phi p c)) y| * (p + 1) * deriv (c08_phi p c) y ^ p)
          ≤ jb y * (C2 * |c| * jb y ^ (-p - 2) * 2 * 2) := by gcongr; linarith
        _ = 4 * C2 * |c| * (jb y * jb y ^ (-p - 2)) := by ring
        _ = _ := by rw [hjbe]
    have h1 : |deriv (c08_phi p c) y ^ (p + 1) - 1| ≤ 7 * C1 * |c| * jb y ^ (-p - 1) := by
      refine e1.trans ?_
      have := hd1 c hc y
      calc 7 * |deriv (c08_phi p c) y - 1| ≤ 7 * (C1 * |c| * jb y ^ (-p - 1)) := by gcongr
        _ = _ := by ring
    have h3 : 0 ≤ |c| * jb y ^ (-p - 1) := by
      have := Real.rpow_pos_of_pos hjb (-p - 1); positivity
    nlinarith
  · have h := c08_aux_jb_lip (c08_phi p c y) y
    have := abs_le.1 (h.trans (hhalf0 c hc y))
    have := c08_aux_one_le_jb y
    linarith [this]
  · have h := c08_aux_jb_lip (c08_phi p c y) y
    have := abs_le.1 (h.trans (hhalf0 c hc y))
    have := c08_aux_one_le_jb y
    linarith
  · have h1 := c08_aux_phi_sub_vanish p c hp hp1 (hc.trans hc0half) 1 y hy
    obtain ⟨hφ, -⟩ := c08_phi_diffeo p c hp hp1 (hc.trans hc0half)
    rw [(c08_aux_iteratedDeriv_sub_id (hφ.of_le (by norm_cast))).1] at h1
    have : deriv (c08_phi p c) y = 1 := by simp only at h1; linarith
    rw [this, Real.one_rpow]; ring
  · have h1 := c08_aux_phi_sub_vanish p c hp hp1 (hc.trans hc0half) 2 y hy
    obtain ⟨hφ, -⟩ := c08_phi_diffeo p c hp hp1 (hc.trans hc0half)
    rw [(c08_aux_iteratedDeriv_sub_id (hφ.of_le (by norm_cast))).2] at h1
    rw [hder c hc y, h1]; ring


/-- Blueprint: lem:c08_psi_bounds.  Bounds for `ψ_c = φ_c⁻¹` for `|c| ≤ c₀`. -/
theorem c08_psi_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, |c| ≤ c0 →
      (∀ y ≤ 1, c08_phi_inv p c y = y) ∧
      c08_phi_inv p c '' Ioi 1 = Ioi 1 ∧
      ∀ y : ℝ,
        jb y / 2 ≤ jb (c08_phi_inv p c y) ∧ jb (c08_phi_inv p c y) ≤ 2 * jb y ∧
        deriv (c08_phi_inv p c) y = 1 / deriv (c08_phi p c) (c08_phi_inv p c y) ∧
        2 / 3 ≤ deriv (c08_phi_inv p c) y ∧ deriv (c08_phi_inv p c) y ≤ 2 ∧
        deriv (deriv (c08_phi_inv p c)) y =
          -(deriv (deriv (c08_phi p c)) (c08_phi_inv p c y)) /
            deriv (c08_phi p c) (c08_phi_inv p c y) ^ 3 ∧
        |c08_phi_inv p c y - y| ≤ C * |c| * jb y ^ (-p) ∧
        |deriv (c08_phi_inv p c) y - 1| ≤ C * |c| * jb y ^ (-p - 1) ∧
        |deriv (deriv (c08_phi_inv p c)) y| ≤ C * |c| * jb y ^ (-p - 2) ∧
        |deriv (c08_phi_inv p c) y ^ (p + 1) - 1| + |deriv (c08_phi_inv p c) y ^ (p + 2) - 1| ≤
          C * |c| * jb y ^ (-p - 1) := by
  obtain ⟨c0, hc0, hc0', hj, -, h3, -⟩ := c08_phi_bounds p hp hp1
  obtain ⟨C0, hC0, hb0⟩ := hj 0
  obtain ⟨C1, hC1, hb1⟩ := hj 1
  obtain ⟨C2, hC2, hb2⟩ := hj 2
  set K1 := 2 * C1 * 2 ^ (p + 1) with hK1
  have hK1p : 0 < K1 := by positivity
  refine ⟨c0, hc0, hc0', C0 * 2 ^ p + K1 + 8 * C2 * 2 ^ (p + 2) + 14 * K1, by positivity,
    fun c hc => ?_⟩
  have hc2 : |c| ≤ 1 / 2 := hc.trans hc0'
  obtain ⟨hφ, hpos, -, himg, -, hψ, hψid, -⟩ := c08_phi_diffeo p c hp hp1 hc2
  obtain ⟨hl, hr, hd1, -⟩ := c08_aux_phi_inverse p c hp hp1 hc2
  have hφ2 : ContDiff ℝ 2 (c08_phi p c) := hφ.of_le (by norm_cast)
  obtain ⟨hi1, hi2⟩ := c08_aux_iteratedDeriv_sub_id hφ2
  have hdφ : Differentiable ℝ (deriv (c08_phi p c)) :=
    ((contDiff_infty_iff_deriv.1 hφ).2).differentiable (by simp)
  have hψd : Differentiable ℝ (c08_phi_inv p c) := hψ.differentiable (by simp)
  have hψ'eq : deriv (c08_phi_inv p c) = fun z => (deriv (c08_phi p c) (c08_phi_inv p c z))⁻¹ := by
    ext z
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hd1 z)
  refine ⟨hψid, ?_, fun y => ?_⟩
  · calc c08_phi_inv p c '' Ioi 1 = c08_phi_inv p c '' (c08_phi p c '' Ioi 1) := by rw [himg]
      _ = Ioi 1 := by rw [Set.image_image]; simp [hl]
  set x := c08_phi_inv p c y with hxdef
  have hx : c08_phi p c x = y := hr y
  obtain ⟨hφ'1, -, hjb1, hjb2⟩ := h3 c hc x
  rw [hx] at hjb1 hjb2
  have hA := abs_le.1 hφ'1
  have hφ'lo : 1 / 2 ≤ deriv (c08_phi p c) x := by linarith
  have hφ'hi : deriv (c08_phi p c) x ≤ 3 / 2 := by linarith
  have hψ' : deriv (c08_phi_inv p c) y = 1 / deriv (c08_phi p c) x := by
    rw [hψ'eq, one_div]
  have hjy := c08_aux_jb_pos y
  have hjx := c08_aux_jb_pos x
  have hjxy : jb y ≤ 2 * jb x := hjb2
  have hcabs := abs_nonneg c
  -- weight transfer
  have hW : ∀ b : ℝ, 0 ≤ b → jb x ^ (-b) ≤ 2 ^ b * jb y ^ (-b) := fun b hb =>
    c08_aux_rpow_neg_le_of_le hjy hb hjxy
  have hφ1x : |deriv (c08_phi p c) x - 1| ≤ C1 * |c| * jb x ^ (-p - 1) := by
    have := hb1 c hc x
    rw [hi1] at this
    simpa using this
  have hφ2x : |deriv (deriv (c08_phi p c)) x| ≤ C2 * |c| * jb x ^ (-p - 2) := by
    have := hb2 c hc x
    rw [hi2] at this
    simpa using this
  have hφ0x : |c08_phi p c x - x| ≤ C0 * |c| * jb x ^ (-p) := by
    have := hb0 c hc x
    simpa [iteratedDeriv_zero] using this
  have hψ1 : |deriv (c08_phi_inv p c) y - 1| ≤ K1 * |c| * jb y ^ (-p - 1) := by
    rw [hψ']
    have e : 1 / deriv (c08_phi p c) x - 1 = (1 - deriv (c08_phi p c) x) / deriv (c08_phi p c) x := by
      field_simp
    rw [e, abs_div, abs_of_pos (show 0 < deriv (c08_phi p c) x by linarith), abs_sub_comm,
      div_le_iff₀ (by linarith)]
    have hw := hW (p + 1) (by linarith)
    rw [show -(p + 1) = -p - 1 by ring] at hw
    have hw0 : 0 ≤ jb y ^ (-p - 1) := (Real.rpow_pos_of_pos hjy _).le
    have hx0 : 0 ≤ jb x ^ (-p - 1) := (Real.rpow_pos_of_pos hjx _).le
    calc |deriv (c08_phi p c) x - 1| ≤ C1 * |c| * jb x ^ (-p - 1) := hφ1x
      _ ≤ C1 * |c| * (2 ^ (p + 1) * jb y ^ (-p - 1)) := by gcongr
      _ = K1 * |c| * jb y ^ (-p - 1) * (1 / 2) := by rw [hK1]; ring
      _ ≤ K1 * |c| * jb y ^ (-p - 1) * deriv (c08_phi p c) x := by gcongr
  have hCge : ∀ a : ℝ, 0 ≤ a → a ≤ C0 * 2 ^ p ∨ a ≤ K1 ∨ a ≤ 8 * C2 * 2 ^ (p + 2) ∨ a ≤ 14 * K1 →
      a ≤ C0 * 2 ^ p + K1 + 8 * C2 * 2 ^ (p + 2) + 14 * K1 := by
    intro a ha h
    have : 0 ≤ C0 * 2 ^ p := by positivity
    have : 0 ≤ 8 * C2 * 2 ^ (p + 2) := by positivity
    rcases h with h | h | h | h <;> linarith
  set C := C0 * 2 ^ p + K1 + 8 * C2 * 2 ^ (p + 2) + 14 * K1
  have hupg : ∀ (a e : ℝ), 0 ≤ a → a ≤ C → a * |c| * jb y ^ e ≤ C * |c| * jb y ^ e := by
    intro a e ha haC
    have := Real.rpow_pos_of_pos hjy e
    gcongr
  have hψ2 : deriv (deriv (c08_phi_inv p c)) y =
      -(deriv (deriv (c08_phi p c)) x) / deriv (c08_phi p c) x ^ 3 := by
    have hφ'' : HasDerivAt (deriv (c08_phi p c))
        (deriv (deriv (c08_phi p c)) (c08_phi_inv p c y)) (c08_phi_inv p c y) :=
      (hdφ _).hasDerivAt
    have hc' := hφ''.comp y (hψd y).hasDerivAt
    have hh := hc'.inv (hpos (c08_phi_inv p c y)).ne'
    have hfun : deriv (c08_phi_inv p c) = (deriv (c08_phi p c) ∘ c08_phi_inv p c)⁻¹ := by
      rw [hψ'eq]; rfl
    rw [hfun, hh.deriv]
    simp only [Function.comp_apply]
    rw [← hxdef, hψ']
    have := (hpos x).ne'
    field_simp
  refine ⟨by linarith, by linarith, hψ', ?_, ?_, hψ2, ?_, ?_, ?_, ?_⟩
  · rw [hψ', le_div_iff₀ (by linarith)]; linarith
  · rw [hψ', div_le_iff₀ (by linarith)]; linarith
  · rw [show x - y = -(c08_phi p c x - x) by rw [hx]; ring, abs_neg]
    calc |c08_phi p c x - x| ≤ C0 * |c| * jb x ^ (-p) := hφ0x
      _ ≤ C0 * |c| * (2 ^ p * jb y ^ (-p)) := by
          have := hW p (by linarith); gcongr
      _ = (C0 * 2 ^ p) * |c| * jb y ^ (-p) := by ring
      _ ≤ _ := hupg _ _ (by positivity) (hCge _ (by positivity) (Or.inl le_rfl))
  · exact hψ1.trans (hupg _ _ hK1p.le (hCge _ hK1p.le (Or.inr (Or.inl le_rfl))))
  · rw [hψ2, abs_div, abs_neg, abs_of_pos (pow_pos (hpos x) 3), div_le_iff₀ (pow_pos (hpos x) 3)]
    have h3pow : (1 / 8 : ℝ) ≤ deriv (c08_phi p c) x ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) hφ'lo 3
      norm_num at this ⊢; linarith
    have hw := hW (p + 2) (by linarith)
    rw [show -(p + 2) = -p - 2 by ring] at hw
    have h8 : (8 * C2 * 2 ^ (p + 2)) * |c| * jb y ^ (-p - 2) ≤ C * |c| * jb y ^ (-p - 2) :=
      hupg _ _ (by positivity) (hCge _ (by positivity) (Or.inr (Or.inr (Or.inl le_rfl))))
    have hmain : |deriv (deriv (c08_phi p c)) x| ≤ C2 * |c| * (2 ^ (p + 2) * jb y ^ (-p - 2)) :=
      hφ2x.trans (by gcongr)
    have hnn : 0 ≤ C * |c| * jb y ^ (-p - 2) := by
      have : 0 ≤ C := by positivity
      have := Real.rpow_pos_of_pos hjy (-p - 2)
      positivity
    have hm8 : 8 * |deriv (deriv (c08_phi p c)) x| ≤ (8 * C2 * 2 ^ (p + 2)) * |c| * jb y ^ (-p - 2) := by
      calc _ ≤ 8 * (C2 * |c| * (2 ^ (p + 2) * jb y ^ (-p - 2))) := by linarith
        _ = _ := by ring
    have hmul : C * |c| * jb y ^ (-p - 2) * (1 / 8) ≤
        C * |c| * jb y ^ (-p - 2) * deriv (c08_phi p c) x ^ 3 :=
      mul_le_mul_of_nonneg_left h3pow hnn
    linarith
  · have hψlo : 2 / 3 ≤ deriv (c08_phi_inv p c) y := by
      rw [hψ', le_div_iff₀ (by linarith)]; linarith
    have hψhi : deriv (c08_phi_inv p c) y ≤ 2 := by
      rw [hψ', div_le_iff₀ (by linarith)]; linarith
    have e1 := c08_aux_rpow_sub_one_le (q := p + 1) (by linarith) hψhi (by linarith) (by linarith)
    have e2 := c08_aux_rpow_sub_one_le (q := p + 2) (by linarith) hψhi (by linarith) (by linarith)
    have h14 : (14 * K1) * |c| * jb y ^ (-p - 1) ≤ C * |c| * jb y ^ (-p - 1) :=
      hupg _ _ (by positivity) (hCge _ (by positivity) (Or.inr (Or.inr (Or.inr le_rfl))))
    have h14' : 14 * |deriv (c08_phi_inv p c) y - 1| ≤ (14 * K1) * |c| * jb y ^ (-p - 1) := by
      have := mul_le_mul_of_nonneg_left hψ1 (by norm_num : (0:ℝ) ≤ 14)
      calc _ ≤ _ := this
        _ = _ := by ring
    linarith

/-- The data needed by `c08_aux_comp_X` for `ψ_ε` and for `φ_ε`, for `|c| ≤ c₀`. -/
theorem c08_aux_phi_psi_data (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ 1 / 2 ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ, |c| ≤ c0 →
      ContDiff ℝ 2 (c08_phi p c) ∧ ContDiff ℝ 2 (c08_phi_inv p c) ∧
      (∀ y, c08_phi_inv p c (c08_phi p c y) = y) ∧ (∀ y, c08_phi p c (c08_phi_inv p c y) = y) ∧
      (∀ y ≤ 1, c08_phi p c y = y) ∧ (∀ y ≤ 1, c08_phi_inv p c y = y) ∧
      (∀ y, 0 ≤ y → 0 ≤ c08_phi p c y) ∧ (∀ y, 0 ≤ y → 0 ≤ c08_phi_inv p c y) ∧
      (∀ y, 0 < deriv (c08_phi p c) y ∧ deriv (c08_phi p c) y ≤ 2) ∧
      (∀ y, 0 < deriv (c08_phi_inv p c) y ∧ deriv (c08_phi_inv p c) y ≤ 2) ∧
      (∀ y, |deriv (deriv (c08_phi p c)) y| ≤ B) ∧
      (∀ y, |deriv (deriv (c08_phi_inv p c)) y| ≤ B) ∧
      (∀ y, jb y ≤ 2 * jb (c08_phi p c y) ∧ jb (c08_phi p c y) ≤ 2 * jb y) ∧
      (∀ y, jb y ≤ 2 * jb (c08_phi_inv p c y) ∧ jb (c08_phi_inv p c y) ≤ 2 * jb y) := by
  obtain ⟨c1, hc1, hc1', hj, -, h3, -⟩ := c08_phi_bounds p hp hp1
  obtain ⟨C2, hC2, hb2⟩ := hj 2
  obtain ⟨c2, hc2, hc2', Cψ, hCψ, hψb⟩ := c08_psi_bounds p hp hp1
  refine ⟨min c1 c2, lt_min hc1 hc2, (min_le_left _ _).trans hc1', C2 + Cψ, by positivity,
    fun c hc => ?_⟩
  have hcc1 : |c| ≤ c1 := hc.trans (min_le_left _ _)
  have hcc2 : |c| ≤ c2 := hc.trans (min_le_right _ _)
  have hc12 : |c| ≤ 1 / 2 := hcc1.trans hc1'
  obtain ⟨hφ, hφpos, hφid, hφimg, -, hψ, hψid, -⟩ := c08_phi_diffeo p c hp hp1 hc12
  obtain ⟨hl, hr, -, -⟩ := c08_aux_phi_inverse p c hp hp1 hc12
  obtain ⟨-, hψimg, hψy⟩ := hψb c hcc2
  have hφ2 : ContDiff ℝ 2 (c08_phi p c) := hφ.of_le (by norm_cast)
  obtain ⟨-, hi2⟩ := c08_aux_iteratedDeriv_sub_id hφ2
  have hjbneg : ∀ y : ℝ, jb y ^ (-p - (2:ℕ)) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by push_cast; linarith)
  have hc0 : |c| ≤ 1 := by linarith
  refine ⟨hφ2, hψ.of_le (by norm_cast), hl, hr, hφid, hψid, ?_, ?_, fun y => ?_, fun y => ?_,
    fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · intro y hy
    rcases le_or_gt y 1 with h | h
    · rw [hφid y h]; exact hy
    · have : c08_phi p c y ∈ c08_phi p c '' Ioi 1 := ⟨y, h, rfl⟩
      rw [hφimg] at this; exact le_of_lt (lt_trans one_pos this)
  · intro y hy
    rcases le_or_gt y 1 with h | h
    · rw [hψid y h]; exact hy
    · have : c08_phi_inv p c y ∈ c08_phi_inv p c '' Ioi 1 := ⟨y, h, rfl⟩
      rw [hψimg] at this; exact le_of_lt (lt_trans one_pos this)
  · have := abs_le.1 (h3 c hcc1 y).1
    exact ⟨hφpos y, by linarith⟩
  · obtain ⟨-, -, -, h1, h2, -⟩ := hψy y
    exact ⟨by linarith, h2⟩
  · have := hb2 c hcc1 y
    rw [hi2] at this
    have h0 : 0 ≤ C2 * |c| := by positivity
    calc |deriv (deriv (c08_phi p c)) y| ≤ C2 * |c| * jb y ^ (-p - (2:ℕ)) := this
      _ ≤ C2 * 1 * 1 := by
          have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-p - (2:ℕ))
          gcongr; exact hjbneg y
      _ ≤ C2 + Cψ := by linarith
  · obtain ⟨-, -, -, -, -, -, -, -, h8, -⟩ := hψy y
    calc |deriv (deriv (c08_phi_inv p c)) y| ≤ Cψ * |c| * jb y ^ (-p - 2) := h8
      _ ≤ Cψ * 1 * 1 := by
          have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-p - 2)
          have h' : jb y ^ (-p - 2) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by linarith)
          gcongr
      _ ≤ C2 + Cψ := by linarith
  · obtain ⟨-, -, h1, h2⟩ := h3 c hcc1 y
    exact ⟨by linarith, h2⟩
  · obtain ⟨h1, h2, -⟩ := hψy y
    exact ⟨by linarith, h2⟩

/-! ## The conjugation identity -/

/-- Blueprint: lem:c08_conj_local.  For `r ∈ C¹`, `v = 𝒰_ε r`, `x = φ_ε(y)`:
`φ_ε'(y)^{p+1}(v(x) - x v'(x)) = r(y) - y r'(y) + b_ε(y) r'(y) + ℛ_{1,ε} r(y)`. -/
theorem c08_conj_local (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc → ∀ r : ℝ → ℝ, ContDiff ℝ 1 r → ∀ y : ℝ,
      deriv (phi_eps p ε) y ^ (p + 1) *
          (U_eps p ε r (phi_eps p ε y) -
            phi_eps p ε y * deriv (U_eps p ε r) (phi_eps p ε y)) =
        r y - y * deriv r y + b_eps p ε y * deriv r y + R_eps_one p ε r y := by
  refine ⟨1, one_pos, fun ε hε0 _ r hr y => ?_⟩
  have hc := (c08_aux_c_eps_bound p ε hp hp1 hε0).1
  obtain ⟨hl, -, -, hd2⟩ := c08_aux_phi_inverse p (c_eps p ε) hp hp1 hc
  obtain ⟨-, hφpos, -, -, -, hψ, -, hode⟩ := c08_phi_diffeo p (c_eps p ε) hp hp1 hc
  have hψd : Differentiable ℝ (c08_phi_inv p (c_eps p ε)) := hψ.differentiable (by simp)
  have hrd : Differentiable ℝ r := hr.differentiable (by norm_num)
  have hU1 : U_eps p ε r (phi_eps p ε y) = r y := by
    simp only [U_eps, phi_eps, psi_eps]; rw [hl y]
  have hU2 : deriv (U_eps p ε r) (phi_eps p ε y) =
      deriv r y * deriv (c08_phi_inv p (c_eps p ε)) (c08_phi p (c_eps p ε) y) := by
    have : U_eps p ε r = r ∘ c08_phi_inv p (c_eps p ε) := rfl
    rw [this, phi_eps, deriv_comp _ (hrd _) (hψd _), hl y]
  rw [hU1, hU2]
  have hode' := hode y
  have hd := hd2 y
  have hpow : deriv (phi_eps p ε) y ^ (p + 1) = deriv (phi_eps p ε) y ^ p * deriv (phi_eps p ε) y :=
    Real.rpow_add_one (hφpos y).ne' p
  unfold R_eps_one b_eps
  unfold phi_eps at hpow ⊢
  rw [hpow]
  set A := deriv (c08_phi p (c_eps p ε)) y
  set B := deriv (c08_phi_inv p (c_eps p ε)) (c08_phi p (c_eps p ε) y)
  have : c08_phi p (c_eps p ε) y * A ^ p = y - c08_phi_b p (c_eps p ε) y := hode'
  have hBA : B * A = 1 := hd
  linear_combination (-(deriv r y)) * this - (c08_phi p (c_eps p ε) y * A ^ p * deriv r y) * hBA

/-- Mean value form of the secant: `S_f(y,z) = f'(ξ)` with `ξ` between `y` and `z`. -/
theorem c08_aux_secant_mvt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {y z : ℝ} (h : y ≠ z) :
    ∃ ξ, |y - ξ| ≤ |y - z| ∧ c01_secant f y z = deriv f ξ := by
  unfold c01_secant
  simp only [h, ↓reduceIte]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · obtain ⟨ξ, hξ, e⟩ := exists_deriv_eq_slope f hlt hf.continuous.continuousOn
      (fun x _ => (hf x).differentiableWithinAt)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hξ.1]), abs_of_neg (by linarith)]; linarith [hξ.2]
    · rw [e]; field_simp; ring
  · obtain ⟨ξ, hξ, e⟩ := exists_deriv_eq_slope f hlt hf.continuous.continuousOn
      (fun x _ => (hf x).differentiableWithinAt)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hξ.2]), abs_of_pos (by linarith)]; linarith [hξ.1]
    · rw [e]

/-- `min(1,w) w^{-1-p} = min(w^{-p}, w^{-1-p})` for `w > 0`. -/
theorem c08_aux_min_rpow {w p : ℝ} (hw : 0 < w) :
    min 1 w * w ^ (-1 - p) = min (w ^ (-p)) (w ^ (-1 - p)) := by
  have e : w * w ^ (-1 - p) = w ^ (-p) := by
    rw [show w * w ^ (-1 - p) = w ^ (1:ℝ) * w ^ (-1 - p) by rw [Real.rpow_one],
      ← Real.rpow_add hw]; ring_nf
  have hpos := Real.rpow_pos_of_pos hw (-1 - p)
  rcases le_total 1 w with h | h
  · rw [min_eq_left h, one_mul]
    have : w ^ (-1 - p) ≤ w ^ (-p) := by rw [← e]; nlinarith
    rw [min_eq_right this]
  · rw [min_eq_right h, e]
    have : w ^ (-p) ≤ w ^ (-1 - p) := by rw [← e]; nlinarith
    rw [min_eq_left this]

/-- Third derivative of `φ - id`. -/
theorem c08_aux_iteratedDeriv_three_sub_id {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) :
    iteratedDeriv 3 (fun y => φ y - y) = deriv (deriv (deriv φ)) := by
  rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
    (c08_aux_iteratedDeriv_sub_id (hφ.of_le (by norm_num))).2]

/-- Bounds for `φ_c` used for the kernel `K_ε`: smoothness, `|φ' - 1| ≤ 1/4`,
`|φ''| ≤ C|c|⟨x⟩^{-p-2}`, `|φ'''| ≤ C|c|⟨x⟩^{-p-3}`. -/
theorem c08_aux_phi_kernel_data (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c1 : ℝ, 0 < c1 ∧ c1 ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, |c| ≤ c1 →
      ContDiff ℝ (⊤ : ℕ∞) (c08_phi p c) ∧ (∀ x ≤ 1, c08_phi p c x = x) ∧
      (∀ x, |deriv (c08_phi p c) x - 1| ≤ 1 / 4) ∧
      (∀ x, |deriv (deriv (c08_phi p c)) x| ≤ C * |c| * jb x ^ (-p - 2)) ∧
      (∀ x, |deriv (deriv (deriv (c08_phi p c))) x| ≤ C * |c| * jb x ^ (-p - 3)) := by
  obtain ⟨c0, hc0, hc0', hj, -, -, -⟩ := c08_phi_bounds p hp hp1
  obtain ⟨C1, hC1, h1⟩ := hj 1
  obtain ⟨C2, hC2, h2⟩ := hj 2
  obtain ⟨C3, hC3, h3⟩ := hj 3
  refine ⟨min c0 (1 / (4 * (C1 + 1))), by positivity, (min_le_left _ _).trans hc0', C2 + C3,
    by positivity, fun c hc => ?_⟩
  have hcc0 : |c| ≤ c0 := hc.trans (min_le_left _ _)
  have hc12 : |c| ≤ 1 / 2 := hcc0.trans hc0'
  obtain ⟨hφ, -, hφid, -⟩ := c08_phi_diffeo p c hp hp1 hc12
  have hφ3 : ContDiff ℝ 3 (c08_phi p c) := hφ.of_le (by norm_cast)
  refine ⟨hφ, hφid, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have := h1 c hcc0 x
    rw [(c08_aux_iteratedDeriv_sub_id (hφ.of_le (by norm_cast))).1] at this
    simp only at this
    refine this.trans ?_
    have hj1 : jb x ^ (-p - ((1:ℕ):ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb x) (by push_cast; linarith)
    have hc' : |c| ≤ 1 / (4 * (C1 + 1)) := hc.trans (min_le_right _ _)
    calc C1 * |c| * jb x ^ (-p - ((1:ℕ):ℝ)) ≤ C1 * |c| * 1 := by gcongr
      _ ≤ (C1 + 1) * (1 / (4 * (C1 + 1))) := by
          rw [mul_one]; exact mul_le_mul (by linarith) hc' (abs_nonneg _) (by linarith)
      _ = 1 / 4 := by field_simp
  · have := h2 c hcc0 x
    rw [(c08_aux_iteratedDeriv_sub_id (hφ.of_le (by norm_cast))).2] at this
    refine this.trans ?_
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos x) (-p - 2)
    push_cast
    gcongr; linarith
  · have := h3 c hcc0 x
    rw [c08_aux_iteratedDeriv_three_sub_id hφ3] at this
    refine this.trans ?_
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos x) (-p - 3)
    push_cast
    gcongr; linarith


/-- The diagonal derivative `(∂_y+∂_z)` of the kernel `c_α[1-(φ'(y)/S_φ)^{p+1}]/|y-z|^{1+p}`. -/
theorem c08_aux_kernel_hasDerivAt (p : ℝ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hpos : ∀ x, 0 < deriv φ x) {y z : ℝ} (h : y ≠ z) (hsec : 0 < c01_secant φ y z) :
    HasDerivAt (fun s => calpha p * (1 - (deriv φ (y + s) / c01_secant φ (y + s) (z + s)) ^ (p + 1)) /
        |y + s - (z + s)| ^ (1 + p))
      (-(calpha p) * (p + 1) * |y - z| ^ (-1 - p) *
        (deriv φ y / c01_secant φ y z) ^ (p + 1) *
        (deriv (deriv φ) y / deriv φ y - c01_secant (deriv φ) y z / c01_secant φ y z)) 0 := by
  have hyz : y - z ≠ 0 := sub_ne_zero.2 h
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv φ) := by
    have : ContDiff ℝ 1 (deriv φ) := hφ.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hsecs : ∀ s, c01_secant φ (y + s) (z + s) = (φ (y + s) - φ (z + s)) / (y - z) := by
    intro s
    unfold c01_secant
    simp only [show y + s ≠ z + s from fun e => h (by linarith), ↓reduceIte]
    congr 1; ring
  have hsec0 : c01_secant φ y z = (φ y - φ z) / (y - z) := by simpa using hsecs 0
  have hsec1 : c01_secant (deriv φ) y z = (deriv φ y - deriv φ z) / (y - z) := by
    unfold c01_secant; simp only [h, ↓reduceIte]
  have e : (fun s => calpha p * (1 - (deriv φ (y + s) / c01_secant φ (y + s) (z + s)) ^ (p + 1)) /
        |y + s - (z + s)| ^ (1 + p)) =
      fun s => calpha p * (1 - (deriv φ (y + s) / ((φ (y + s) - φ (z + s)) / (y - z))) ^ (p + 1)) /
        |y - z| ^ (1 + p) := by
    funext s; rw [hsecs s, show y + s - (z + s) = y - z by ring]
  rw [e]
  have hu : HasDerivAt (fun s => deriv φ (y + s)) (deriv (deriv φ) y) 0 := by
    have := (hd1 (y + 0)).hasDerivAt.comp_const_add y 0
    simpa using this
  have hv : HasDerivAt (fun s => (φ (y + s) - φ (z + s)) / (y - z))
      ((deriv φ y - deriv φ z) / (y - z)) 0 := by
    have h1 := (hd (y + 0)).hasDerivAt.comp_const_add y 0
    have h2 := (hd (z + 0)).hasDerivAt.comp_const_add z 0
    simp only [add_zero] at h1 h2
    exact (h1.sub h2).div_const _
  have hv0 : (φ (y + 0) - φ (z + 0)) / (y - z) ≠ 0 := by
    simp only [add_zero]; rw [← hsec0]; exact hsec.ne'
  have hq := hu.div hv hv0
  set q := deriv φ y / c01_secant φ y z with hqdef
  have hqpos : 0 < q := div_pos (hpos y) hsec
  have hq0 : ((fun s => deriv φ (y + s)) / fun s => (φ (y + s) - φ (z + s)) / (y - z)) 0 = q := by
    simp only [Pi.div_apply, add_zero]; rw [hqdef, hsec0]
  have hr := hq.rpow_const (p := p + 1) (Or.inl (by rw [hq0]; exact hqpos.ne'))
  have hfin := ((hr.const_sub 1).const_mul (calpha p)).div_const (|y - z| ^ (1 + p))
  convert hfin using 1
  rw [hq0]
  simp only [add_zero]
  rw [← hsec0, ← hsec1]
  have hw : 0 < |y - z| := abs_pos.2 hyz
  have hS := hsec.ne'
  have hu0 := (hpos y).ne'
  have hqp : q ^ (p + 1) = q ^ (p + 1 - 1) * q := by
    rw [show p + 1 - 1 = p by ring, Real.rpow_add_one hqpos.ne']
  rw [hqp, show -1 - p = -(1 + p) by ring, Real.rpow_neg hw.le, hqdef]
  have hwp : 0 < |y - z| ^ (1 + p) := Real.rpow_pos_of_pos hw _
  field_simp


/-- Elementary ratio bounds for `a, b ∈ [3/4, 5/4]`. -/
theorem c08_aux_ratio_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) {a b : ℝ}
    (ha : |a - 1| ≤ 1 / 4) (hb : |b - 1| ≤ 1 / 4) :
    |1 - (a / b) ^ (p + 1)| ≤ 10 * |a - b| ∧ 0 < (a / b) ^ (p + 1) ∧ (a / b) ^ (p + 1) ≤ 3 ∧
    ∀ u v : ℝ, |u / a - v / b| ≤ 2 * |u| * |a - b| + 3 * |u - v| := by
  have ha' := abs_le.1 ha; have hb' := abs_le.1 hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hq0 : 0 ≤ a / b := (div_pos ha0 hb0).le
  have hq2 : a / b ≤ 2 := by rw [div_le_iff₀ hb0]; linarith
  refine ⟨?_, Real.rpow_pos_of_pos (div_pos ha0 hb0) _, ?_, fun u v => ?_⟩
  · have h7 := c08_aux_rpow_sub_one_le hq0 hq2 (q := p + 1) (by linarith) (by linarith)
    rw [abs_sub_comm]
    refine h7.trans ?_
    rw [show a / b - 1 = (a - b) / b by field_simp, abs_div, abs_of_pos hb0]
    rw [mul_div_assoc', div_le_iff₀ hb0]
    nlinarith [abs_nonneg (a - b)]
  · have hq53 : a / b ≤ 5 / 3 := by rw [div_le_iff₀ hb0]; linarith
    calc (a / b) ^ (p + 1) ≤ (5 / 3) ^ (p + 1) := Real.rpow_le_rpow hq0 hq53 (by linarith)
      _ ≤ (5 / 3) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (5 / 3) ^ (2:ℕ) := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      _ ≤ 3 := by norm_num
  · have e : u / a - v / b = (u * (b - a) + a * (u - v)) / (a * b) := by field_simp; ring
    rw [e, abs_div, abs_of_pos (mul_pos ha0 hb0), div_le_iff₀ (mul_pos ha0 hb0)]
    have h1 : |u * (b - a) + a * (u - v)| ≤ |u| * |a - b| + a * |u - v| := by
      calc _ ≤ |u * (b - a)| + |a * (u - v)| := abs_add_le _ _
        _ = |u| * |a - b| + a * |u - v| := by
          rw [abs_mul, abs_mul, abs_of_pos ha0, abs_sub_comm b a]
    have hab : 9 / 16 ≤ a * b := by nlinarith
    have hx := mul_nonneg (abs_nonneg u) (abs_nonneg (a - b))
    have hy := abs_nonneg (u - v)
    nlinarith

/-- Core estimate for the kernel at a pair `y ≠ z`. -/
theorem c08_aux_kernel_core (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (h1 : ∀ x, |deriv φ x - 1| ≤ 1 / 4) {y z : ℝ} (h : y ≠ z) :
    ∃ ξ η : ℝ, |y - ξ| ≤ |y - z| ∧ |y - η| ≤ |y - z| ∧
      |calpha p * (1 - (deriv φ y / c01_secant φ y z) ^ (p + 1)) / |y - z| ^ (1 + p)| ≤
        4 * |deriv φ y - deriv φ ξ| * |y - z| ^ (-1 - p) ∧
      HasDerivAt (fun s => calpha p * (1 - (deriv φ (y + s) / c01_secant φ (y + s) (z + s)) ^ (p + 1)) /
        |y + s - (z + s)| ^ (1 + p))
        (-(calpha p) * (p + 1) * |y - z| ^ (-1 - p) *
          (deriv φ y / c01_secant φ y z) ^ (p + 1) *
          (deriv (deriv φ) y / deriv φ y - c01_secant (deriv φ) y z / c01_secant φ y z)) 0 ∧
      |-(calpha p) * (p + 1) * |y - z| ^ (-1 - p) *
          (deriv φ y / c01_secant φ y z) ^ (p + 1) *
          (deriv (deriv φ) y / deriv φ y - c01_secant (deriv φ) y z / c01_secant φ y z)| ≤
        2 * |y - z| ^ (-1 - p) * (2 * |deriv (deriv φ) y| * |deriv φ y - deriv φ ξ| +
          3 * |deriv (deriv φ) y - deriv (deriv φ) η|) := by
  have hp0 : 0 < p := by linarith
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv φ) := by
    have : ContDiff ℝ 1 (deriv φ) := hφ.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  obtain ⟨ξ, hξ, hsξ⟩ := c08_aux_secant_mvt hd h
  obtain ⟨η, hη, hsη⟩ := c08_aux_secant_mvt hd1 h
  have hpos : ∀ x, 0 < deriv φ x := fun x => by linarith [(abs_le.1 (h1 x)).1]
  have hsec : 0 < c01_secant φ y z := by rw [hsξ]; exact hpos ξ
  obtain ⟨r1, r2, r3, r4⟩ := c08_aux_ratio_bounds p hp0 hp1 (h1 y) (h1 ξ)
  have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 h)
  have hwp : 0 < |y - z| ^ (-1 - p) := Real.rpow_pos_of_pos hw _
  have hca := c08_aux_calpha_bound p hp0 hp1
  have hpi : 1 / π < 1 / 3 := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num)]; linarith [Real.pi_gt_three]
  refine ⟨ξ, η, hξ, hη, ?_, c08_aux_kernel_hasDerivAt p hφ hpos h hsec, ?_⟩
  · rw [hsξ, abs_div, abs_mul, show (1 + p) = -(-1 - p) by ring, Real.rpow_neg hw.le,
      abs_inv, abs_of_pos hwp, div_inv_eq_mul]
    have : |calpha p| * |1 - (deriv φ y / deriv φ ξ) ^ (p + 1)| ≤
        (1 / 3) * (10 * |deriv φ y - deriv φ ξ|) :=
      mul_le_mul (by linarith) r1 (abs_nonneg _) (by norm_num)
    have h' : |calpha p| * |1 - (deriv φ y / deriv φ ξ) ^ (p + 1)| ≤ 4 * |deriv φ y - deriv φ ξ| := by
      nlinarith [abs_nonneg (deriv φ y - deriv φ ξ)]
    exact mul_le_mul_of_nonneg_right h' hwp.le
  · rw [hsξ, hsη]
    have h4 := r4 (deriv (deriv φ) y) (deriv (deriv φ) η)
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : (0:ℝ) < p + 1),
      abs_of_pos hwp, abs_of_pos r2]
    have hA : |calpha p| * (p + 1) ≤ 2 / 3 := by nlinarith
    have hB : 0 ≤ 2 * |deriv (deriv φ) y| * |deriv φ y - deriv φ ξ| +
        3 * |deriv (deriv φ) y - deriv (deriv φ) η| := by positivity
    calc |calpha p| * (p + 1) * |y - z| ^ (-1 - p) * (deriv φ y / deriv φ ξ) ^ (p + 1) *
          |deriv (deriv φ) y / deriv φ y - deriv (deriv φ) η / deriv φ ξ|
        ≤ (2 / 3) * |y - z| ^ (-1 - p) * 3 *
          (2 * |deriv (deriv φ) y| * |deriv φ y - deriv φ ξ| +
            3 * |deriv (deriv φ) y - deriv (deriv φ) η|) := by gcongr
      _ = _ := by ring


/-- Weighted mean value bound: if `|g'| ≤ A⟨·⟩^{-b}` and `|y - ξ| ≤ ⟨y⟩/4`, then
`|g(y) - g(ξ)| ≤ 2^b A ⟨y⟩^{-b} |y - ξ|`. -/
theorem c08_aux_mvt_weighted {g : ℝ → ℝ} (hg : Differentiable ℝ g) {A b y ξ : ℝ} (hA : 0 ≤ A)
    (hb : 0 ≤ b) (hder : ∀ x, |deriv g x| ≤ A * jb x ^ (-b)) (hξ : |y - ξ| ≤ jb y / 4) :
    |g y - g ξ| ≤ 2 ^ b * A * jb y ^ (-b) * |y - ξ| := by
  apply c08_aux_mvt_bound (fun x _ => hg x)
  intro ζ hζ
  refine (hder ζ).trans ?_
  have h1 : |ζ - y| ≤ |ξ - y| := Set.abs_sub_left_of_mem_uIcc hζ
  have h2 : jb y ≤ 2 * jb ζ := by
    have := c08_aux_jb_lip y ζ
    rw [abs_sub_comm ξ y, abs_sub_comm ζ y] at h1
    have := abs_le.1 this
    linarith [c08_aux_one_le_jb y]
  have h3 := c08_aux_rpow_neg_le_of_le (c08_aux_jb_pos y) hb h2
  calc A * jb ζ ^ (-b) ≤ A * (2 ^ b * jb y ^ (-b)) := mul_le_mul_of_nonneg_left h3 hA
    _ = _ := by ring

/-- `∫_{|y-z| ≤ R} |y-z|^{-p} dz = 2R^{1-p}/(1-p)` (and integrability), `0 < p < 1`. -/
theorem c08_aux_ball_rpow {p : ℝ} (_hp : 0 < p) (hp1 : p < 1) (y : ℝ) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun z => |y - z| ^ (-p)) {z | |y - z| ≤ R} ∧
    ∫ z in {z | |y - z| ≤ R}, |y - z| ^ (-p) = 2 * R ^ (1 - p) / (1 - p) := by
  have hset : {z : ℝ | |y - z| ≤ R} = Icc (y - R) (y + R) := by
    ext z; simp only [mem_ofPred_eq, mem_Icc, abs_le]; constructor <;> intro h <;> constructor <;>
      linarith [h.1, h.2]
  have hr : -1 < -p := by linarith
  -- the half integrals
  have hpos : IntervalIntegrable (fun u : ℝ => |u| ^ (-p)) volume 0 R := by
    refine (intervalIntegral.intervalIntegrable_rpow' hr).congr (fun u hu => ?_)
    rw [uIoc_of_le hR.le] at hu
    show u ^ (-p) = |u| ^ (-p)
    rw [abs_of_pos hu.1]
  have hneg : IntervalIntegrable (fun u : ℝ => |u| ^ (-p)) volume (-R) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun u : ℝ => |u| ^ (-p)) (a := 0) (b := R)
      (by simp)).1 hpos
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  have hint0 : ∫ u in (0:ℝ)..R, |u| ^ (-p) = R ^ (1 - p) / (1 - p) := by
    rw [intervalIntegral.integral_congr (g := fun u : ℝ => u ^ (-p)) (fun u hu => by
      rw [uIcc_of_le hR.le] at hu; simp only; rw [abs_of_nonneg hu.1])]
    rw [integral_rpow (Or.inl hr), Real.zero_rpow (by linarith)]
    rw [show -p + 1 = 1 - p by ring]; ring
  have hint1 : ∫ u in (-R)..0, |u| ^ (-p) = R ^ (1 - p) / (1 - p) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun u : ℝ => |u| ^ (-p))
    simp only [abs_neg, neg_zero] at this
    rw [← this, hint0]
  have hfull : IntervalIntegrable (fun u : ℝ => |u| ^ (-p)) volume (-R) R := hneg.trans hpos
  have hfull' : IntervalIntegrable (fun z : ℝ => |y - z| ^ (-p)) volume (y - R) (y + R) := by
    have := hfull.comp_sub_left y (by simp)
    simp only [sub_neg_eq_add] at this
    exact this.symm
  rw [hset]
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 hfull', ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_left (fun u : ℝ => |u| ^ (-p)) y,
    show y - (y + R) = -R by ring, show y - (y - R) = R by ring,
    ← intervalIntegral.integral_add_adjacent_intervals hneg hpos, hint0, hint1]
  ring


/-- `∫_{x > b} |m - x|^{-1-p} dx = (b-m)^{-p}/p` for `m < b`, `p > 0`. -/
theorem c08_aux_halfline_Ioi {p : ℝ} (hp : 0 < p) {m b : ℝ} (hmb : m < b) :
    IntegrableOn (fun x => |m - x| ^ (-1 - p)) (Ioi b) ∧
    ∫ x in Ioi b, |m - x| ^ (-1 - p) = (b - m) ^ (-p) / p := by
  have hs : MeasurableSet (Ioi (b - m)) := measurableSet_Ioi
  have hd : ∀ u ∈ Ioi (b - m), HasDerivWithinAt (fun u => u + m) 1 (Ioi (b - m)) u :=
    fun u _ => ((hasDerivAt_id u).add_const m).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => u + m) (Ioi (b - m)) := fun u _ v _ h => by simpa using h
  have himg : (fun u : ℝ => u + m) '' Ioi (b - m) = Ioi b := by
    rw [image_add_const_Ioi]; congr 1; ring
  have hcongr : EqOn (fun u => |(1:ℝ)| • |m - (u + m)| ^ (-1 - p)) (fun u => u ^ (-1 - p))
      (Ioi (b - m)) := by
    intro u hu
    have hu0 : 0 < u := by simp only [mem_Ioi] at hu; linarith
    simp only [abs_one, one_smul, show m - (u + m) = -u by ring, abs_neg, abs_of_pos hu0]
  have hc : 0 < b - m := by linarith
  have hr : -1 - p < -1 := by linarith
  constructor
  · rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd hinj]
    exact (integrableOn_Ioi_rpow_of_lt hr hc).congr_fun hcongr.symm hs
  · rw [← himg, integral_image_eq_integral_abs_deriv_smul hs hd hinj, setIntegral_congr_fun hs hcongr,
      integral_Ioi_rpow_of_lt hr hc]
    rw [show -1 - p + 1 = -p by ring]
    field_simp

/-- `∫_{x < a} |m - x|^{-1-p} dx = (m-a)^{-p}/p` for `a < m`, `p > 0`. -/
theorem c08_aux_halfline_Iio {p : ℝ} (hp : 0 < p) {m a : ℝ} (ham : a < m) :
    IntegrableOn (fun x => |m - x| ^ (-1 - p)) (Iio a) ∧
    ∫ x in Iio a, |m - x| ^ (-1 - p) = (m - a) ^ (-p) / p := by
  have hs : MeasurableSet (Ioi (m - a)) := measurableSet_Ioi
  have hd : ∀ u ∈ Ioi (m - a), HasDerivWithinAt (fun u => m - u) (-1) (Ioi (m - a)) u :=
    fun u _ => ((hasDerivAt_id u).const_sub m).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => m - u) (Ioi (m - a)) := fun u _ v _ h => by simpa using h
  have himg : (fun u : ℝ => m - u) '' Ioi (m - a) = Iio a := by
    ext x; simp only [mem_image, mem_Ioi, mem_Iio]
    constructor
    · rintro ⟨u, hu, rfl⟩; linarith
    · intro hx; exact ⟨m - x, by linarith, by ring⟩
  have hcongr : EqOn (fun u => |(-1:ℝ)| • |m - (m - u)| ^ (-1 - p)) (fun u => u ^ (-1 - p))
      (Ioi (m - a)) := by
    intro u hu
    have hu0 : 0 < u := by simp only [mem_Ioi] at hu; linarith
    simp only [abs_neg, abs_one, one_smul, show m - (m - u) = u by ring, abs_of_pos hu0]
  have hc : 0 < m - a := by linarith
  have hr : -1 - p < -1 := by linarith
  constructor
  · rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd hinj]
    exact (integrableOn_Ioi_rpow_of_lt hr hc).congr_fun hcongr.symm hs
  · rw [← himg, integral_image_eq_integral_abs_deriv_smul hs hd hinj, setIntegral_congr_fun hs hcongr,
      integral_Ioi_rpow_of_lt hr hc]
    rw [show -1 - p + 1 = -p by ring]
    field_simp


/-- Truncated singular integral after the substitution `x = ψ(z)`:
`∫_{|y-z|>δ} ψ'(z)|ψ(y)-ψ(z)|^{-1-p} dz = [(ψ(y)-ψ(y-δ))^{-p} + (ψ(y+δ)-ψ(y))^{-p}]/p`. -/
theorem c08_aux_trunc {p : ℝ} (hp : 0 < p) {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ)
    (hpos : ∀ x, 0 < deriv ψ x) (hsurj : Function.Surjective ψ) (y : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun z => deriv ψ z * |ψ y - ψ z| ^ (-1 - p)) {z | δ < |y - z|} ∧
    ∫ z in {z | δ < |y - z|}, deriv ψ z * |ψ y - ψ z| ^ (-1 - p) =
      ((ψ y - ψ (y - δ)) ^ (-p) + (ψ (y + δ) - ψ y) ^ (-p)) / p := by
  have hmono : StrictMono ψ := strictMono_of_deriv_pos hpos
  set s := {z : ℝ | δ < |y - z|} with hsdef
  have hs_eq : s = Iio (y - δ) ∪ Ioi (y + δ) := by
    ext z; simp only [hsdef, mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; linarith
      · right; linarith
  have hs : MeasurableSet s := by rw [hs_eq]; exact measurableSet_Iio.union measurableSet_Ioi
  have hd : ∀ z ∈ s, HasDerivWithinAt ψ (deriv ψ z) s z :=
    fun z _ => (hψ z).hasDerivAt.hasDerivWithinAt
  have hinj : InjOn ψ s := hmono.injective.injOn
  set a := ψ (y - δ)
  set b := ψ (y + δ)
  have ha : a < ψ y := hmono (by linarith)
  have hb : ψ y < b := hmono (by linarith)
  have himg : ψ '' s = Iio a ∪ Ioi b := by
    rw [hs_eq, image_union]
    congr 1
    · ext x; simp only [mem_image, mem_Iio]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hmono hz
      · intro hx
        obtain ⟨z, rfl⟩ := hsurj x
        exact ⟨z, hmono.lt_iff_lt.1 hx, rfl⟩
    · ext x; simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hmono hz
      · intro hx
        obtain ⟨z, rfl⟩ := hsurj x
        exact ⟨z, hmono.lt_iff_lt.1 hx, rfl⟩
  have hcongr : EqOn (fun z => |deriv ψ z| • |ψ y - ψ z| ^ (-1 - p))
      (fun z => deriv ψ z * |ψ y - ψ z| ^ (-1 - p)) s := by
    intro z _; simp only [abs_of_pos (hpos z), smul_eq_mul]
  obtain ⟨i1, v1⟩ := c08_aux_halfline_Iio hp ha
  obtain ⟨i2, v2⟩ := c08_aux_halfline_Ioi hp hb
  have hdisj : Disjoint (Iio a) (Ioi b) := by
    rw [Set.disjoint_left]; intro x hx1 hx2
    simp only [mem_Iio] at hx1; simp only [mem_Ioi] at hx2; linarith
  constructor
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd hinj
      (fun x => |ψ y - x| ^ (-1 - p))).1 (by rw [himg]; exact i1.union i2)
    exact this.congr_fun hcongr hs
  · rw [← setIntegral_congr_fun hs hcongr, ← integral_image_eq_integral_abs_deriv_smul hs hd hinj (fun x => |ψ y - x| ^ (-1 - p)),
      himg, setIntegral_union hdisj measurableSet_Ioi i1 i2, v1, v2]
    ring


/-- `|u^p v - 1| ≤ (5/3)|u - 1| + |v - 1|` type bound for the cancellation lemma. -/
theorem c08_aux_cancel_E (p : ℝ) (hp : 0 < p) (hp1 : p < 1) {a b S : ℝ}
    (ha : |a - 1| ≤ 1 / 4) (hb : |b - 1| ≤ 1 / 4) (hS : |S - 1| ≤ 1 / 4) :
    |a ^ p * b / S ^ (1 + p) - 1| ≤ 3 * |a - S| + 2 * |b - S| := by
  have ha' := abs_le.1 ha; have hb' := abs_le.1 hb; have hS' := abs_le.1 hS
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hS0 : 0 < S := by linarith
  have e : a ^ p * b / S ^ (1 + p) = (a / S) ^ p * (b / S) := by
    rw [Real.div_rpow ha0.le hS0.le, Real.rpow_add hS0, Real.rpow_one]
    field_simp
  rw [e]
  have hu0 : 0 ≤ a / S := (div_pos ha0 hS0).le
  have h1 := c08_aux_rpow_sub_one_le' hu0 hp.le hp1.le
  have hv : b / S ≤ 5 / 3 := by rw [div_le_iff₀ hS0]; linarith
  have hv0 : 0 ≤ b / S := (div_pos hb0 hS0).le
  have hu1 : |a / S - 1| ≤ (4 / 3) * |a - S| := by
    rw [show a / S - 1 = (a - S) / S by field_simp, abs_div, abs_of_pos hS0, div_le_iff₀ hS0]
    nlinarith [abs_nonneg (a - S)]
  have hv1 : |b / S - 1| ≤ (4 / 3) * |b - S| := by
    rw [show b / S - 1 = (b - S) / S by field_simp, abs_div, abs_of_pos hS0, div_le_iff₀ hS0]
    nlinarith [abs_nonneg (b - S)]
  calc |(a / S) ^ p * (b / S) - 1| = |((a / S) ^ p - 1) * (b / S) + (b / S - 1)| := by ring_nf
    _ ≤ |(a / S) ^ p - 1| * (b / S) + |b / S - 1| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hv0]
    _ ≤ (4 / 3 * |a - S|) * (5 / 3) + 4 / 3 * |b - S| := by
        gcongr
        exact h1.trans hu1
    _ ≤ 3 * |a - S| + 2 * |b - S| := by nlinarith [abs_nonneg (a - S), abs_nonneg (b - S)]

/-- `min(1,w) w^{-1-p} ≤ 1_{w ≤ 1} w^{-p} + 4⟨u⟩^{-1-p}` where `w = |u|`. -/
theorem c08_aux_min_dominate {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {u : ℝ} (hu : 0 < |u|) :
    min 1 |u| * |u| ^ (-1 - p) ≤
      {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) u + 4 * jb u ^ (-1 - p) := by
  have hj := (Real.rpow_pos_of_pos (c08_aux_jb_pos u) (-1 - p)).le
  rcases le_total |u| 1 with h | h
  · rw [min_eq_right h, Set.indicator_of_mem (show u ∈ {v : ℝ | |v| ≤ 1} from h)]
    have : |u| * |u| ^ (-1 - p) = |u| ^ (-p) := by
      rw [show |u| * |u| ^ (-1 - p) = |u| ^ (1:ℝ) * |u| ^ (-1 - p) by rw [Real.rpow_one],
        ← Real.rpow_add hu]; ring_nf
    rw [this]; linarith
  · rw [min_eq_left h, one_mul]
    have hind : 0 ≤ {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) u :=
      Set.indicator_nonneg (fun v _ => Real.rpow_nonneg (abs_nonneg v) _) u
    have hjb : jb u ≤ 2 * |u| := by have := c08_aux_jb_le_one_add u; linarith
    have := c08_aux_rpow_neg_le_of_le (c08_aux_jb_pos u) (show (0:ℝ) ≤ 1 + p by linarith) hjb
    rw [show -(1 + p) = -1 - p by ring] at this
    have h2 : (2:ℝ) ^ (1 + p) ≤ 4 := by
      calc (2:ℝ) ^ (1 + p) ≤ 2 ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    nlinarith

/-- Blueprint: lem:c08_conj_cancellation.  For `|c| ≤ c₀`, `φ = φ_c`:
`z ↦ φ'(y)^p φ'(z)/|φ(y)-φ(z)|^{1+p} - 1/|y-z|^{1+p}` is integrable with integral `0`. -/
theorem c08_conj_cancellation (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c0 : ℝ, 0 < c0 ∧ c0 ≤ 1 / 2 ∧ ∀ c : ℝ, |c| ≤ c0 → ∀ y : ℝ,
      Integrable (fun z => deriv (c08_phi p c) y ^ p * deriv (c08_phi p c) z /
          |c08_phi p c y - c08_phi p c z| ^ (1 + p) - 1 / |y - z| ^ (1 + p)) ∧
      ∫ z, (deriv (c08_phi p c) y ^ p * deriv (c08_phi p c) z /
          |c08_phi p c y - c08_phi p c z| ^ (1 + p) - 1 / |y - z| ^ (1 + p)) = 0 := by
  obtain ⟨c1, hc1, hc1', C, hC, hdat⟩ := c08_aux_phi_kernel_data p hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨c1, hc1, hc1', fun c hc y => ?_⟩
  obtain ⟨hφ, -, h1, h2, -⟩ := hdat c hc
  obtain ⟨-, -, -, -, hbij, -⟩ := c08_phi_diffeo p c hp hp1 (hc.trans hc1')
  set φ := c08_phi p c with hφdef
  have hcle1 : |c| ≤ 1 := by linarith
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hd : Differentiable ℝ φ := hφ2.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv φ) := by
    have : ContDiff ℝ 1 (deriv φ) := hφ2.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hpos : ∀ x, 0 < deriv φ x := fun x => by linarith [(abs_le.1 (h1 x)).1]
  have h2b : ∀ x, |deriv (deriv φ) x| ≤ C := fun x => by
    refine (h2 x).trans ?_
    have h' : jb x ^ (-p - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb x) (by linarith)
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos x) (-p - 2)
    calc C * |c| * jb x ^ (-p - 2) ≤ C * 1 * 1 := by gcongr
      _ = C := by ring
  have hinc : ∀ u v : ℝ, |deriv φ u - deriv φ v| ≤ C * |u - v| := fun u v =>
    c08_aux_mvt_bound (fun x _ => hd1 x) (fun x _ => h2b x)
  have hinc2 : ∀ u v : ℝ, |deriv φ u - deriv φ v| ≤ 1 / 2 := fun u v => by
    have := abs_le.1 (h1 u); have := abs_le.1 (h1 v)
    rw [abs_le]; constructor <;> linarith
  set a := deriv φ y with ha
  have ha0 : 0 < a := hpos y
  set F : ℝ → ℝ := fun z => a ^ p * deriv φ z / |φ y - φ z| ^ (1 + p) - 1 / |y - z| ^ (1 + p)
    with hFdef
  set dom : ℝ → ℝ := fun z => 5 * (C + 1) * ({v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) (y - z) +
      4 * jb (y - z) ^ (-1 - p)) with hdom
  have hFbound : ∀ z, |F z| ≤ dom z := by
    intro z
    have hdom0 : 0 ≤ {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) (y - z) +
        4 * jb (y - z) ^ (-1 - p) := by
      have := Set.indicator_nonneg (s := {v : ℝ | |v| ≤ 1}) (f := fun v => |v| ^ (-p))
        (fun v _ => Real.rpow_nonneg (abs_nonneg v) _) (y - z)
      have := (Real.rpow_pos_of_pos (c08_aux_jb_pos (y - z)) (-1 - p)).le
      positivity
    by_cases hzy : z = y
    · subst hzy
      simp only [hFdef, hdom, sub_self, abs_zero, Real.zero_rpow (show (1:ℝ) + p ≠ 0 by linarith),
        div_zero]
      have := hdom0; simp only [sub_self] at this
      positivity
    have h : y ≠ z := Ne.symm hzy
    have hyz : y - z ≠ 0 := sub_ne_zero.2 h
    have hw : 0 < |y - z| := abs_pos.2 hyz
    obtain ⟨ξ, hξ, hsξ⟩ := c08_aux_secant_mvt hd h
    obtain ⟨ξ', hξ', hsξ'⟩ := c08_aux_secant_mvt hd (Ne.symm h)
    have hsym : c01_secant φ z y = c01_secant φ y z := by
      unfold c01_secant; simp only [h, Ne.symm h, ↓reduceIte]
      rw [← neg_sub (φ y), ← neg_sub y, neg_div_neg_eq]
    set S := deriv φ ξ with hS
    have hSdef : S = (φ y - φ z) / (y - z) := by
      rw [← hsξ]; unfold c01_secant; simp only [h, ↓reduceIte]
    have hS1 : |S - 1| ≤ 1 / 4 := h1 ξ
    have hS0 : 0 < S := by linarith [(abs_le.1 hS1).1]
    have e : φ y - φ z = S * (y - z) := by rw [hSdef]; field_simp
    have hdiff : |φ y - φ z| = S * |y - z| := by rw [e, abs_mul, abs_of_pos hS0]
    have hFz : F z = (a ^ p * deriv φ z / S ^ (1 + p) - 1) * |y - z| ^ (-1 - p) := by
      simp only [hFdef]
      rw [hdiff, Real.mul_rpow hS0.le hw.le, show -1 - p = -(1 + p) by ring,
        Real.rpow_neg hw.le]
      have := Real.rpow_pos_of_pos hS0 (1 + p)
      have := Real.rpow_pos_of_pos hw (1 + p)
      field_simp
    have hE := c08_aux_cancel_E p hp0 hp1 (h1 y) (h1 z) hS1
    have hA : |a - S| ≤ (C + 1) * min 1 |y - z| := by
      rcases le_total 1 |y - z| with hw1 | hw1
      · rw [min_eq_left hw1]; linarith [hinc2 y ξ]
      · rw [min_eq_right hw1]
        calc |a - deriv φ ξ| ≤ C * |y - ξ| := hinc y ξ
          _ ≤ C * |y - z| := by gcongr
          _ ≤ (C + 1) * |y - z| := by nlinarith
    have hB : |deriv φ z - S| ≤ (C + 1) * min 1 |y - z| := by
      rw [← hsξ, ← hsym, hsξ']
      have hzy' : |z - ξ'| ≤ |y - z| := by rw [abs_sub_comm y z]; exact hξ'
      rcases le_total 1 |y - z| with hw1 | hw1
      · rw [min_eq_left hw1]; linarith [hinc2 z ξ']
      · rw [min_eq_right hw1]
        calc |deriv φ z - deriv φ ξ'| ≤ C * |z - ξ'| := hinc z ξ'
          _ ≤ C * |y - z| := by gcongr
          _ ≤ (C + 1) * |y - z| := by nlinarith
    have hmin := c08_aux_min_dominate hp0 hp1 (u := y - z) hw
    have hwp := Real.rpow_pos_of_pos hw (-1 - p)
    rw [hFz, abs_mul, abs_of_pos hwp]
    have hm0 : 0 ≤ min 1 |y - z| := le_min zero_le_one hw.le
    calc |a ^ p * deriv φ z / S ^ (1 + p) - 1| * |y - z| ^ (-1 - p)
        ≤ (3 * ((C + 1) * min 1 |y - z|) + 2 * ((C + 1) * min 1 |y - z|)) * |y - z| ^ (-1 - p) := by
          gcongr
          exact hE.trans (by linarith)
      _ = 5 * (C + 1) * (min 1 |y - z| * |y - z| ^ (-1 - p)) := by ring
      _ ≤ dom z := by
          simp only [hdom]
          exact mul_le_mul_of_nonneg_left hmin (by positivity)
  -- integrability
  have hφc : Continuous φ := hd.continuous
  have hd1c : Continuous (deriv φ) := hd1.continuous
  have hFmeas : AEStronglyMeasurable F := by
    have : Measurable F := by
      simp only [hFdef]
      have m1 := hd1c.measurable
      have m2 := hφc.measurable
      fun_prop
    exact this.aestronglyMeasurable
  have hdomi : Integrable dom := by
    obtain ⟨hbi, -⟩ := c08_aux_ball_rpow hp0 hp1 0 one_pos
    have h1i : Integrable ({v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p))) := by
      have : IntegrableOn (fun v : ℝ => |v| ^ (-p)) {v : ℝ | |v| ≤ 1} := by
        simpa using hbi
      exact this.integrable_indicator (measurableSet_le (by fun_prop) measurable_const)
    have h2i := c08_aux_jb_rpow_integrable (1 + p) (by linarith)
    have h2i' : Integrable (fun z => jb (y - z) ^ (-1 - p)) := by
      have := h2i.comp_sub_left y
      simpa [show -(1 + p) = -1 - p by ring] using this
    exact ((h1i.comp_sub_left y).add (h2i'.const_mul 4)).const_mul _
  have hFi : Integrable F :=
    hdomi.mono' hFmeas (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hFbound z)
  refine ⟨hFi, ?_⟩
  -- truncations
  set s : ℕ → Set ℝ := fun n => {z | 1 / ((n:ℝ) + 1) < |y - z|} with hsdef
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt measurable_const (by fun_prop)
  have hmono : Monotone s := by
    intro n m hnm z hz
    simp only [hsdef, mem_ofPred_eq] at hz ⊢
    refine lt_of_le_of_lt ?_ hz
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hU : (⋃ n, s n) = {y}ᶜ := by
    ext z; simp only [hsdef, mem_iUnion, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨n, hn⟩ rfl; simp at hn; linarith [show (0:ℝ) < 1 / ((n:ℝ) + 1) by positivity]
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 (Ne.symm hz)))
      exact ⟨n, hn⟩
  have hlim := tendsto_setIntegral_of_monotone hsm hmono hFi.integrableOn
  rw [hU, restrict_compl_singleton] at hlim
  -- explicit values of the truncated integrals
  have hφsurj : Function.Surjective φ := hbij.2
  have hFe : F = fun z => a ^ p * (deriv φ z * |φ y - φ z| ^ (-1 - p)) -
      deriv (fun x : ℝ => x) z * |(fun x : ℝ => x) y - (fun x : ℝ => x) z| ^ (-1 - p) := by
    funext z
    simp only [hFdef, deriv_id'', one_mul]
    rw [show -1 - p = -(1 + p) by ring, Real.rpow_neg (abs_nonneg _), Real.rpow_neg (abs_nonneg _)]
    ring
  have hval : ∀ n : ℕ, |∫ z in s n, F z| ≤ (8 * C / (3 * p)) * (1 / ((n:ℝ) + 1)) ^ (1 - p) := by
    intro n
    set δ := 1 / ((n:ℝ) + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨i1, v1⟩ := c08_aux_trunc hp0 hd hpos hφsurj y hδ0
    obtain ⟨i2, v2⟩ := c08_aux_trunc hp0 (ψ := fun x : ℝ => x) differentiable_id
      (fun x => by simp) (fun x => ⟨x, rfl⟩) y hδ0
    simp only [hsdef]
    rw [hFe, integral_sub (i1.const_mul _) i2, integral_const_mul, v1, v2]
    simp only [show y - (y - δ) = δ by ring, show y + δ - y = δ by ring]
    -- secants on both sides
    obtain ⟨ξp, hξp, hsp⟩ := c08_aux_secant_mvt hd (show y ≠ y + δ by linarith)
    obtain ⟨ξm, hξm, hsm'⟩ := c08_aux_secant_mvt hd (show y ≠ y - δ by linarith)
    have hδne : δ ≠ 0 := hδ0.ne'
    have ep : φ (y + δ) - φ y = deriv φ ξp * δ := by
      rw [← hsp]; unfold c01_secant; simp only [show y ≠ y + δ by linarith, ↓reduceIte]
      rw [show y - (y + δ) = -δ by ring, div_neg, neg_mul, div_mul_cancel₀ _ hδne]; ring
    have em : φ y - φ (y - δ) = deriv φ ξm * δ := by
      rw [← hsm']; unfold c01_secant; simp only [show y ≠ y - δ by linarith, ↓reduceIte]
      rw [show y - (y - δ) = δ by ring, div_mul_cancel₀ _ hδne]
    rw [ep, em]
    have hpp := hpos ξp
    have hpm := hpos ξm
    rw [Real.mul_rpow hpp.le hδ0.le, Real.mul_rpow hpm.le hδ0.le]
    have key : ∀ S : ℝ, |S - 1| ≤ 1 / 4 → |a - S| ≤ C * δ →
        |a ^ p * S ^ (-p) - 1| ≤ (4 / 3) * (C * δ) := by
      intro S hS1 haS
      have hS0 : 0 < S := by linarith [(abs_le.1 hS1).1]
      have e : a ^ p * S ^ (-p) = (a / S) ^ p := by
        rw [Real.div_rpow ha0.le hS0.le, Real.rpow_neg hS0.le, div_eq_mul_inv]
      rw [e]
      refine (c08_aux_rpow_sub_one_le' (div_pos ha0 hS0).le hp0.le hp1.le).trans ?_
      rw [show a / S - 1 = (a - S) / S by field_simp, abs_div, abs_of_pos hS0, div_le_iff₀ hS0]
      nlinarith [abs_nonneg (a - S), (abs_le.1 hS1).1]
    have kp := key (deriv φ ξp) (h1 ξp) ((hinc y ξp).trans (by
      have : |y - ξp| ≤ δ := by rw [show |y - (y + δ)| = δ by
        rw [show y - (y + δ) = -δ by ring, abs_neg, abs_of_pos hδ0]] at hξp; exact hξp
      gcongr))
    have km := key (deriv φ ξm) (h1 ξm) ((hinc y ξm).trans (by
      have : |y - ξm| ≤ δ := by rw [show |y - (y - δ)| = δ by
        rw [show y - (y - δ) = δ by ring, abs_of_pos hδ0]] at hξm; exact hξm
      gcongr))
    have hδp : 0 < δ ^ (-p) := Real.rpow_pos_of_pos hδ0 _
    have eδ : δ ^ (-p) * δ = δ ^ (1 - p) := by
      rw [show (1:ℝ) - p = -p + 1 by ring, Real.rpow_add_one hδ0.ne']
    have hexpr : a ^ p * ((deriv φ ξm ^ (-p) * δ ^ (-p) + deriv φ ξp ^ (-p) * δ ^ (-p)) / p) -
        (δ ^ (-p) + δ ^ (-p)) / p =
        δ ^ (-p) / p * ((a ^ p * deriv φ ξm ^ (-p) - 1) + (a ^ p * deriv φ ξp ^ (-p) - 1)) := by
      field_simp; ring
    rw [hexpr, abs_mul, abs_of_pos (by positivity : 0 < δ ^ (-p) / p)]
    calc δ ^ (-p) / p * |(a ^ p * deriv φ ξm ^ (-p) - 1) + (a ^ p * deriv φ ξp ^ (-p) - 1)|
        ≤ δ ^ (-p) / p * ((4 / 3) * (C * δ) + (4 / 3) * (C * δ)) := by
          gcongr; exact (abs_add_le _ _).trans (add_le_add km kp)
      _ = (8 * C / (3 * p)) * (δ ^ (-p) * δ) := by field_simp; ring
      _ = _ := by rw [eδ]
  have hzero : Tendsto (fun n : ℕ => ∫ z in s n, F z) atTop (nhds 0) := by
    have ht : Tendsto (fun n : ℕ => (8 * C / (3 * p)) * (1 / ((n:ℝ) + 1)) ^ (1 - p)) atTop
        (nhds ((8 * C / (3 * p)) * 0 ^ (1 - p))) := by
      refine (tendsto_const_nhds.mul ?_)
      exact ((Real.continuousAt_rpow_const 0 (1 - p) (Or.inr (by linarith))).tendsto).comp
        tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.zero_rpow (by linarith), mul_zero] at ht
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hval n) ht
  exact tendsto_nhds_unique hlim hzero


/-- Blueprint: lem:c08_R2_kernel_near.  Kernel bounds in the near region `0 < |y-z| ≤ ⟨y⟩/4`,
and the global bound `|K| + |(∂_y+∂_z)K| ≤ C min(|y-z|^{-p}, |y-z|^{-1-p})`. -/
theorem c08_R2_kernel_near (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      (∀ y z : ℝ, 0 < |y - z| → |y - z| ≤ jb y / 4 →
        (max y z < 1 →
          R_eps_kernel p ε y z = 0 ∧
          deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 = 0) ∧
        (y ≤ 0 →
          R_eps_kernel p ε y z = 0 ∧
          deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 = 0) ∧
        |R_eps_kernel p ε y z| ≤ C * |c_eps p ε| * jb y ^ (-p - 2) * |y - z| ^ (-p) ∧
        HasDerivAt (fun s => R_eps_kernel p ε (y + s) (z + s))
          (-(calpha p) * (p + 1) * |y - z| ^ (-1 - p) *
            (deriv (phi_eps p ε) y / c01_secant (phi_eps p ε) y z) ^ (p + 1) *
            (deriv (deriv (phi_eps p ε)) y / deriv (phi_eps p ε) y -
              c01_secant (deriv (phi_eps p ε)) y z / c01_secant (phi_eps p ε) y z)) 0 ∧
        |deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0| ≤
          C * |c_eps p ε| * jb y ^ (-p - 3) * |y - z| ^ (-p)) ∧
      ∀ y z : ℝ, y ≠ z →
        |R_eps_kernel p ε y z| + |deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0| ≤
          C * min (|y - z| ^ (-p)) (|y - z| ^ (-1 - p)) := by
  obtain ⟨c1, hc1, hc1', C, hC, hdat⟩ := c08_aux_phi_kernel_data p hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨c1, hc1, 100 * (C + 1) ^ 2, by positivity, fun ε hε0 hε => ?_⟩
  have hcε := c08_aux_c_eps_bound p ε hp hp1 hε0
  have hc : |c_eps p ε| ≤ c1 := hcε.2.trans hε
  have hcle1 : |c_eps p ε| ≤ 1 := by linarith
  obtain ⟨hφ, hφid, h1, h2, h3⟩ := hdat (c_eps p ε) hc
  have hφe : phi_eps p ε = c08_phi p (c_eps p ε) := rfl
  rw [hφe]
  set c := c_eps p ε with hcdef
  set φ := c08_phi p c with hφdef
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hK : ∀ y z, R_eps_kernel p ε y z =
      calpha p * (1 - (deriv φ y / c01_secant φ y z) ^ (p + 1)) / |y - z| ^ (1 + p) :=
    fun y z => rfl
  have hKs : ∀ y z, (fun s => R_eps_kernel p ε (y + s) (z + s)) = fun s =>
      calpha p * (1 - (deriv φ (y + s) / c01_secant φ (y + s) (z + s)) ^ (p + 1)) /
        |y + s - (z + s)| ^ (1 + p) := fun y z => rfl
  have hd1 : Differentiable ℝ (deriv φ) := by
    have : ContDiff ℝ 1 (deriv φ) := hφ2.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv (deriv φ)) := by
    have : ContDiff ℝ 1 (deriv (deriv φ)) := (hφ.of_le (by norm_cast) : ContDiff ℝ 3 φ).iterate_deriv' 1 2
    simpa using this.differentiable (by norm_num)
  have hjbn : ∀ (x a : ℝ), 0 ≤ a → jb x ^ (-a) ≤ 1 := fun x a ha =>
    Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb x) (by linarith)
  have h2b : ∀ x, |deriv (deriv φ) x| ≤ C := fun x => by
    refine (h2 x).trans ?_
    have := hjbn x (p + 2) (by linarith)
    rw [show -(p + 2) = -p - 2 by ring] at this
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos x) (-p - 2)
    calc C * |c| * jb x ^ (-p - 2) ≤ C * 1 * 1 := by gcongr
      _ = C := by ring
  have h3b : ∀ x, |deriv (deriv (deriv φ)) x| ≤ C := fun x => by
    refine (h3 x).trans ?_
    have := hjbn x (p + 3) (by linarith)
    rw [show -(p + 3) = -p - 3 by ring] at this
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos x) (-p - 3)
    calc C * |c| * jb x ^ (-p - 3) ≤ C * 1 * 1 := by gcongr
      _ = C := by ring
  -- identity region
  have hd1id : ∀ x, x < 1 → deriv φ x = 1 := fun x hx => by
    have : φ =ᶠ[nhds x] id := Filter.eventually_of_mem (Iio_mem_nhds hx)
      (fun w hw => hφid w (le_of_lt hw))
    rw [this.deriv_eq, deriv_id]
  have hd2id : ∀ x, x < 1 → deriv (deriv φ) x = 0 := fun x hx => by
    have : deriv φ =ᶠ[nhds x] fun _ => 1 := Filter.eventually_of_mem (Iio_mem_nhds hx)
      (fun w hw => hd1id w hw)
    rw [this.deriv_eq, deriv_const]
  have hzero : ∀ y z, y ≠ z → max y z < 1 →
      R_eps_kernel p ε y z = 0 ∧ deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 = 0 := by
    intro y z h hm
    have hy1 : y < 1 := lt_of_le_of_lt (le_max_left _ _) hm
    have hz1 : z < 1 := lt_of_le_of_lt (le_max_right _ _) hm
    have hyz : y - z ≠ 0 := sub_ne_zero.2 h
    have hsec : c01_secant φ y z = 1 := by
      unfold c01_secant; simp only [h, ↓reduceIte]
      rw [hφid y hy1.le, hφid z hz1.le, div_self hyz]
    have hsec' : c01_secant (deriv φ) y z = 0 := by
      unfold c01_secant; simp only [h, ↓reduceIte]
      rw [hd1id y hy1, hd1id z hz1]; simp
    obtain ⟨_, _, -, -, -, hD, -⟩ := c08_aux_kernel_core p hp hp1 hφ2 h1 h
    refine ⟨?_, ?_⟩
    · rw [hK, hsec, hd1id y hy1]; simp
    · rw [hKs, hD.deriv, hsec, hsec', hd2id y hy1, hd1id y hy1]; simp
  refine ⟨fun y z hw hwy => ?_, fun y z h => ?_⟩
  · have h : y ≠ z := fun e => by rw [e, sub_self, abs_zero] at hw; exact lt_irrefl _ hw
    have hmax0 : y ≤ 0 → max y z < 1 := by
      intro hy0
      have hj := c08_aux_jb_le_one_add y
      rw [abs_of_nonpos hy0] at hj
      have : z ≤ y + |y - z| := by linarith [neg_abs_le (y - z)]
      apply max_lt (by linarith)
      linarith
    refine ⟨hzero y z h, fun hy0 => hzero y z h (hmax0 hy0), ?_⟩
    obtain ⟨ξ, η, hξ, hη, hKb, hD, hDb⟩ := c08_aux_kernel_core p hp hp1 hφ2 h1 h
    have hwp : 0 < |y - z| ^ (-1 - p) := Real.rpow_pos_of_pos hw _
    have hww : |y - z| * |y - z| ^ (-1 - p) = |y - z| ^ (-p) := by
      rw [show |y - z| * |y - z| ^ (-1 - p) = |y - z| ^ (1:ℝ) * |y - z| ^ (-1 - p) by
        rw [Real.rpow_one], ← Real.rpow_add hw]; ring_nf
    have hjy := c08_aux_jb_pos y
    -- weighted increments
    have hΔ1 : |deriv φ y - deriv φ ξ| ≤ 8 * C * |c| * jb y ^ (-p - 2) * |y - z| := by
      have hmv := c08_aux_mvt_weighted hd1 (A := C * |c|) (b := p + 2) (by positivity) (by linarith)
        (fun x => by rw [show -(p + 2) = -p - 2 by ring]; exact h2 x) (hξ.trans hwy)
      rw [show -(p + 2) = -p - 2 by ring] at hmv
      have h8 : (2:ℝ) ^ (p + 2) ≤ 8 := by
        calc (2:ℝ) ^ (p + 2) ≤ 2 ^ (3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 8 := by norm_num
      have := Real.rpow_pos_of_pos hjy (-p - 2)
      calc _ ≤ 2 ^ (p + 2) * (C * |c|) * jb y ^ (-p - 2) * |y - ξ| := hmv
        _ ≤ 8 * (C * |c|) * jb y ^ (-p - 2) * |y - z| := by gcongr
        _ = _ := by ring
    have hΔ2 : |deriv (deriv φ) y - deriv (deriv φ) η| ≤
        16 * C * |c| * jb y ^ (-p - 3) * |y - z| := by
      have hmv := c08_aux_mvt_weighted hd2 (A := C * |c|) (b := p + 3) (by positivity) (by linarith)
        (fun x => by rw [show -(p + 3) = -p - 3 by ring]; exact h3 x) (hη.trans hwy)
      rw [show -(p + 3) = -p - 3 by ring] at hmv
      have h16 : (2:ℝ) ^ (p + 3) ≤ 16 := by
        calc (2:ℝ) ^ (p + 3) ≤ 2 ^ (4:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 16 := by norm_num
      have := Real.rpow_pos_of_pos hjy (-p - 3)
      calc _ ≤ 2 ^ (p + 3) * (C * |c|) * jb y ^ (-p - 3) * |y - η| := hmv
        _ ≤ 16 * (C * |c|) * jb y ^ (-p - 3) * |y - z| := by gcongr
        _ = _ := by ring
    have hd2y : |deriv (deriv φ) y| ≤ C * jb y ^ (-1:ℝ) := by
      refine (h2 y).trans ?_
      have : jb y ^ (-p - 2) ≤ jb y ^ (-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb y) (by linarith)
      calc C * |c| * jb y ^ (-p - 2) ≤ C * 1 * jb y ^ (-1:ℝ) := by gcongr
        _ = _ := by ring
    have hjj : jb y ^ (-1:ℝ) * jb y ^ (-p - 2) = jb y ^ (-p - 3) := by
      rw [← Real.rpow_add hjy]; ring_nf
    have hCc : 0 ≤ C * |c| := by positivity
    refine ⟨?_, by rw [hKs]; exact hD, ?_⟩
    · rw [hK]
      refine hKb.trans ?_
      calc 4 * |deriv φ y - deriv φ ξ| * |y - z| ^ (-1 - p)
          ≤ 4 * (8 * C * |c| * jb y ^ (-p - 2) * |y - z|) * |y - z| ^ (-1 - p) := by gcongr
        _ = 32 * C * |c| * jb y ^ (-p - 2) * (|y - z| * |y - z| ^ (-1 - p)) := by ring
        _ ≤ 100 * (C + 1) ^ 2 * |c| * jb y ^ (-p - 2) * |y - z| ^ (-p) := by
          rw [hww]
          have := Real.rpow_pos_of_pos hjy (-p - 2)
          have := Real.rpow_pos_of_pos hw (-p)
          have h32 : 32 * C ≤ 100 * (C + 1) ^ 2 := by nlinarith
          gcongr
    · rw [hKs, hD.deriv]
      refine hDb.trans ?_
      have hjm := (Real.rpow_pos_of_pos hjy (-1:ℝ)).le
      calc 2 * |y - z| ^ (-1 - p) * (2 * |deriv (deriv φ) y| * |deriv φ y - deriv φ ξ| +
            3 * |deriv (deriv φ) y - deriv (deriv φ) η|)
          ≤ 2 * |y - z| ^ (-1 - p) * (2 * (C * jb y ^ (-1:ℝ)) *
              (8 * C * |c| * jb y ^ (-p - 2) * |y - z|) +
            3 * (16 * C * |c| * jb y ^ (-p - 3) * |y - z|)) := by gcongr
        _ = (32 * C ^ 2 * (jb y ^ (-1:ℝ) * jb y ^ (-p - 2)) + 96 * C * jb y ^ (-p - 3)) * |c| *
              (|y - z| * |y - z| ^ (-1 - p)) := by ring
        _ = (32 * C ^ 2 + 96 * C) * |c| * jb y ^ (-p - 3) * |y - z| ^ (-p) := by
          rw [hjj, hww]; ring
        _ ≤ 100 * (C + 1) ^ 2 * |c| * jb y ^ (-p - 3) * |y - z| ^ (-p) := by
          have := Real.rpow_pos_of_pos hjy (-p - 3)
          have := Real.rpow_pos_of_pos hw (-p)
          have h32 : 32 * C ^ 2 + 96 * C ≤ 100 * (C + 1) ^ 2 := by nlinarith
          gcongr
  · obtain ⟨ξ, η, hξ, hη, hKb, hD, hDb⟩ := c08_aux_kernel_core p hp hp1 hφ2 h1 h
    have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 h)
    have hwp : 0 < |y - z| ^ (-1 - p) := Real.rpow_pos_of_pos hw _
    set m := min 1 |y - z| with hm
    have hm0 : 0 ≤ m := le_min zero_le_one hw.le
    have hΔ1 : |deriv φ y - deriv φ ξ| ≤ (C + 1) * m := by
      have a1 : |deriv φ y - deriv φ ξ| ≤ C * |y - ξ| :=
        c08_aux_mvt_bound (fun x _ => hd1 x) (fun x _ => h2b x)
      have a2 : |deriv φ y - deriv φ ξ| ≤ 1 / 2 := by
        have := abs_le.1 (h1 y); have := abs_le.1 (h1 ξ)
        rw [abs_le]; constructor <;> linarith
      rcases le_total 1 |y - z| with hw1 | hw1
      · rw [hm, min_eq_left hw1]; linarith
      · rw [hm, min_eq_right hw1]
        calc _ ≤ C * |y - ξ| := a1
          _ ≤ C * |y - z| := by gcongr
          _ ≤ (C + 1) * |y - z| := by nlinarith
    have hΔ2 : |deriv (deriv φ) y - deriv (deriv φ) η| ≤ 2 * (C + 1) * m := by
      have a1 : |deriv (deriv φ) y - deriv (deriv φ) η| ≤ C * |y - η| :=
        c08_aux_mvt_bound (fun x _ => hd2 x) (fun x _ => h3b x)
      have a2 : |deriv (deriv φ) y - deriv (deriv φ) η| ≤ 2 * C := by
        calc _ ≤ |deriv (deriv φ) y| + |deriv (deriv φ) η| := abs_sub _ _
          _ ≤ C + C := add_le_add (h2b y) (h2b η)
          _ = 2 * C := by ring
      rcases le_total 1 |y - z| with hw1 | hw1
      · rw [hm, min_eq_left hw1]; linarith
      · rw [hm, min_eq_right hw1]
        calc _ ≤ C * |y - η| := a1
          _ ≤ C * |y - z| := by gcongr
          _ ≤ 2 * (C + 1) * |y - z| := by nlinarith
    rw [hK, hKs, hD.deriv, ← c08_aux_min_rpow hw]
    have e1 := hKb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hΔ1 (by norm_num : (0:ℝ) ≤ 4)) hwp.le)
    have e2 := hDb.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left (h2b y) (by norm_num)) hΔ1
        (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left hΔ2 (by norm_num : (0:ℝ) ≤ 3)))
      (by positivity : (0:ℝ) ≤ 2 * |y - z| ^ (-1 - p)))
    have : 4 * ((C + 1) * m) * |y - z| ^ (-1 - p) +
        2 * |y - z| ^ (-1 - p) * (2 * C * ((C + 1) * m) + 3 * (2 * (C + 1) * m)) ≤
        100 * (C + 1) ^ 2 * (m * |y - z| ^ (-1 - p)) := by
      have hmw : 0 ≤ m * |y - z| ^ (-1 - p) := mul_nonneg hm0 hwp.le
      have hk : (C + 1) * (4 * C + 16) ≤ 100 * (C + 1) ^ 2 := by nlinarith
      calc _ = (C + 1) * (4 * C + 16) * (m * |y - z| ^ (-1 - p)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hk hmw
    linarith


/-- `K_ε(y,y) = 0`. -/
theorem c08_aux_kernel_diag (p ε y : ℝ) (hp : 0 < p) : R_eps_kernel p ε y y = 0 := by
  unfold R_eps_kernel
  rw [sub_self, abs_zero, Real.zero_rpow (by linarith), div_zero]

/-- Dominating function `1_{|u| ≤ 1}|u|^{-p} + 4⟨u⟩^{-1-p}` (translated) is integrable. -/
theorem c08_aux_dom_integrable {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (y : ℝ) :
    Integrable (fun z => {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) (y - z) +
      4 * jb (y - z) ^ (-1 - p)) := by
  obtain ⟨hbi, -⟩ := c08_aux_ball_rpow hp hp1 0 one_pos
  have h1i : Integrable ({v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p))) := by
    have : IntegrableOn (fun v : ℝ => |v| ^ (-p)) {v : ℝ | |v| ≤ 1} := by
      simpa using hbi
    exact this.integrable_indicator (measurableSet_le (by fun_prop) measurable_const)
  have h2i := c08_aux_jb_rpow_integrable (1 + p) (by linarith)
  have h2i' : Integrable (fun z => jb (y - z) ^ (-1 - p)) := by
    have := h2i.comp_sub_left y
    simpa [show -(1 + p) = -1 - p by ring] using this
  exact (h1i.comp_sub_left y).add (h2i'.const_mul 4)

/-- `|D|^p`-integrand of a bounded locally Lipschitz function is integrable. -/
theorem c08_aux_frac_integrable {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {g : ℝ → ℝ}
    (hg : LocallyLipschitz g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (y : ℝ) :
    Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)) := by
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc (a := y - 1) (b := y + 1)) hg.locallyLipschitzOn
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hL0 : (0:ℝ) ≤ L := L.2
  have hgc : Continuous g := hg.continuous
  refine ((c08_aux_dom_integrable hp hp1 y).const_mul (L + 2 * M)).mono'
    ((measurable_const.sub hgc.measurable).div
      ((measurable_const.sub measurable_id).abs.pow_const _)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  have hdom0 : 0 ≤ {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) (y - z) +
      4 * jb (y - z) ^ (-1 - p) := by
    have := Set.indicator_nonneg (s := {v : ℝ | |v| ≤ 1}) (f := fun v => |v| ^ (-p))
      (fun v _ => Real.rpow_nonneg (abs_nonneg v) _) (y - z)
    have := (Real.rpow_pos_of_pos (c08_aux_jb_pos (y - z)) (-1 - p)).le
    positivity
  by_cases hzy : z = y
  · subst hzy; simp only [sub_self, zero_div, abs_zero]
    exact mul_nonneg (by linarith) (by simpa using hdom0)
  have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hzy))
  have hnum : |g y - g z| ≤ (L + 2 * M) * min 1 |y - z| := by
    rcases le_total |y - z| 1 with h | h
    · rw [min_eq_right h]
      have hy : y ∈ Icc (y - 1) (y + 1) := ⟨by linarith, by linarith⟩
      have hz : z ∈ Icc (y - 1) (y + 1) := by
        have := abs_le.1 h; exact ⟨by linarith, by linarith⟩
      have := hL.dist_le_mul y hy z hz
      rw [Real.dist_eq, Real.dist_eq] at this
      nlinarith
    · rw [min_eq_left h]
      calc |g y - g z| ≤ |g y| + |g z| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM y) (hM z)
        _ ≤ (L + 2 * M) * 1 := by linarith
  have hmin := c08_aux_min_dominate hp hp1 (u := y - z) hw
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hw _), show p + 1 = 1 + p by ring]
  have e : |y - z| ^ (-1 - p) = (|y - z| ^ (1 + p))⁻¹ := by
    rw [show -1 - p = -(1 + p) by ring, Real.rpow_neg hw.le]
  rw [div_eq_mul_inv, ← e]
  calc |g y - g z| * |y - z| ^ (-1 - p)
      ≤ (L + 2 * M) * min 1 |y - z| * |y - z| ^ (-1 - p) := by
        gcongr
    _ = (L + 2 * M) * (min 1 |y - z| * |y - z| ^ (-1 - p)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin (by linarith)


/-- Blueprint: lem:c08_conj_nonlocal.  For `r ∈ C¹` with `r'` bounded and locally Lipschitz,
`w = (𝒰_ε r)' = (r' ∘ ψ_ε) ψ_ε'` is bounded and locally Lipschitz and
`φ_ε'(y)^{p+1} (|D|^p w)(φ_ε(y)) = (|D|^p r')(y) + ℛ_{2,ε} r(y)` (absolutely convergent integrals). -/
theorem c08_conj_nonlocal (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc → ∀ r : ℝ → ℝ, ContDiff ℝ 1 r →
      (∃ M : ℝ, ∀ y, |deriv r y| ≤ M) → LocallyLipschitz (deriv r) →
      deriv (U_eps p ε r) = (fun x => deriv r (psi_eps p ε x) * deriv (psi_eps p ε) x) ∧
      (∃ M : ℝ, ∀ x, |deriv (U_eps p ε r) x| ≤ M) ∧
      LocallyLipschitz (deriv (U_eps p ε r)) ∧
      ∀ y : ℝ,
        Integrable (fun z => (deriv (U_eps p ε r) (phi_eps p ε y) - deriv (U_eps p ε r) z) /
          |phi_eps p ε y - z| ^ (p + 1)) ∧
        Integrable (fun z => (deriv r y - deriv r z) / |y - z| ^ (p + 1)) ∧
        Integrable (fun z => R_eps_kernel p ε y z * deriv r z) ∧
        deriv (phi_eps p ε) y ^ (p + 1) * fracD p (deriv (U_eps p ε r)) (phi_eps p ε y) =
          fracD p (deriv r) y + R_eps_two p ε r y := by
  obtain ⟨c0, hc0, hc0', hcanc⟩ := c08_conj_cancellation p hp hp1
  obtain ⟨ε1, hε1, Ck, hCk, hK⟩ := c08_R2_kernel_near p hp hp1
  obtain ⟨c2, hc2, hc2', B, hB, hdata⟩ := c08_aux_phi_psi_data p hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨min (min c0 ε1) c2, by positivity, fun ε hε0 hε r hr hrM hrL => ?_⟩
  have hcε := c08_aux_c_eps_bound p ε hp hp1 hε0
  have hcc0 : |c_eps p ε| ≤ c0 := hcε.2.trans (hε.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have e1 : ε ≤ ε1 := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcc2 : |c_eps p ε| ≤ c2 := hcε.2.trans (hε.trans (min_le_right _ _))
  obtain ⟨hφ2, hψ2, hl, hrr, -, -, -, -, hφd, hψd, -, -, -, -⟩ := hdata (c_eps p ε) hcc2
  obtain ⟨-, hKglob⟩ := hK ε hε0 e1
  have hφe : phi_eps p ε = c08_phi p (c_eps p ε) := rfl
  have hψe : psi_eps p ε = c08_phi_inv p (c_eps p ε) := rfl
  obtain ⟨M, hM⟩ := hrM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hrd : Differentiable ℝ r := hr.differentiable (by norm_num)
  set c := c_eps p ε with hcdef
  set φ := c08_phi p c with hφdef
  set ψ := c08_phi_inv p c with hψdef
  have hψdiff : Differentiable ℝ ψ := hψ2.differentiable (by norm_num)
  have hφdiff : Differentiable ℝ φ := hφ2.differentiable (by norm_num)
  have hinv := c08_aux_phi_inverse p c hp hp1 (hcc2.trans hc2')
  -- (A)
  have hA : deriv (U_eps p ε r) = fun x => deriv r (psi_eps p ε x) * deriv (psi_eps p ε) x := by
    funext x
    have : U_eps p ε r = r ∘ ψ := rfl
    rw [this, deriv_comp x (hrd _) (hψdiff x)]
    rfl
  set w := deriv (U_eps p ε r) with hwdef
  have hwφ : ∀ z, w (φ z) = deriv r z / deriv φ z := by
    intro z
    rw [hA]
    simp only [hψe]
    rw [show ψ (φ z) = z from hinv.1 z]
    have h1 := hinv.2.2.2 z
    have hpos := (hφd z).1
    field_simp
    rw [mul_assoc, show deriv ψ (φ z) * deriv φ z = 1 from h1, mul_one]
  -- (B)
  have hwM : ∀ x, |w x| ≤ M * 2 := by
    intro x
    rw [hA]; simp only [hψe]
    rw [abs_mul, abs_of_pos (hψd x).1]
    exact mul_le_mul (hM _) (hψd x).2 (hψd x).1.le hM0
  -- (C)
  have hwL : LocallyLipschitz w := by
    rw [hA]; simp only [hψe]
    apply c08_aux_locallyLipschitz_mul
    · exact hrL.comp (hψ2.of_le (by norm_num)).locallyLipschitz
    · exact (hψ2.iterate_deriv' 1 1).locallyLipschitz
  refine ⟨hA, ⟨M * 2, hwM⟩, hwL, fun y => ?_⟩
  -- (D)
  have hca : 0 < calpha p := by
    unfold calpha
    have h1 : 0 < Real.Gamma (1 + p) := Real.Gamma_pos_of_pos (by linarith)
    have h2 : 0 < Real.sin (π * p / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    positivity
  set a := deriv φ y with ha
  have ha0 : 0 < a := (hφd y).1
  have hBi := c08_aux_frac_integrable hp0 hp1 hrL hM y
  obtain ⟨hAi, hA0⟩ := hcanc c hcc0 y
  -- the kernel term
  have hφc : Continuous φ := hφdiff.continuous
  have hsecm : Measurable (fun z => c01_secant φ y z) := by
    unfold c01_secant
    exact Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const
      ((measurable_const.sub hφc.measurable).div (measurable_const.sub measurable_id))
  have hrc : Continuous (deriv r) := hr.continuous_deriv le_rfl
  have hKm : Measurable (fun z => R_eps_kernel p ε y z * deriv r z) := by
    unfold R_eps_kernel
    rw [hφe]
    exact ((measurable_const.mul (measurable_const.sub ((measurable_const.div hsecm).pow_const _))).div
      ((measurable_const.sub measurable_id).abs.pow_const _)).mul hrc.measurable
  have hKi : Integrable (fun z => R_eps_kernel p ε y z * deriv r z) := by
    refine ((c08_aux_dom_integrable hp0 hp1 y).const_mul (Ck * M)).mono' hKm.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hdom0 : 0 ≤ {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) (y - z) +
        4 * jb (y - z) ^ (-1 - p) := by
      have := Set.indicator_nonneg (s := {v : ℝ | |v| ≤ 1}) (f := fun v => |v| ^ (-p))
        (fun v _ => Real.rpow_nonneg (abs_nonneg v) _) (y - z)
      have := (Real.rpow_pos_of_pos (c08_aux_jb_pos (y - z)) (-1 - p)).le
      positivity
    by_cases hzy : z = y
    · subst hzy; rw [c08_aux_kernel_diag p ε z hp0, abs_zero, zero_mul]
      exact mul_nonneg (by positivity) (by simpa using hdom0)
    have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hzy))
    have hk := hKglob y z (Ne.symm hzy)
    rw [← c08_aux_min_rpow hw] at hk
    have hk' : |R_eps_kernel p ε y z| ≤ Ck * ({v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) (y - z) +
        4 * jb (y - z) ^ (-1 - p)) := by
      have := c08_aux_min_dominate hp0 hp1 (u := y - z) hw
      have h0 := abs_nonneg (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0)
      calc |R_eps_kernel p ε y z| ≤ Ck * (min 1 |y - z| * |y - z| ^ (-1 - p)) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left this hCk.le
    calc |R_eps_kernel p ε y z| * |deriv r z| ≤ (Ck * ({v : ℝ | |v| ≤ 1}.indicator
          (fun v => |v| ^ (-p)) (y - z) + 4 * jb (y - z) ^ (-1 - p))) * M :=
          mul_le_mul hk' (hM z) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  -- the change of variables
  have hsurj : Function.Surjective φ := Function.RightInverse.surjective hinv.2.1
  have hinj : Function.Injective φ := Function.LeftInverse.injective hinv.1
  have hd' : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt φ (deriv φ x) univ x :=
    fun x _ => (hφdiff x).hasDerivAt.hasDerivWithinAt
  set g : ℝ → ℝ := fun x => (w (φ y) - w x) / |φ y - x| ^ (p + 1) with hg
  have himg : φ '' univ = univ := image_univ_of_surjective hsurj
  -- pointwise identity
  set Af : ℝ → ℝ := fun z => deriv φ y ^ p * deriv φ z / |φ y - φ z| ^ (1 + p) - 1 / |y - z| ^ (1 + p)
    with hAf
  have hpt : ∀ z, calpha p * a ^ (p + 1) * (|deriv φ z| • g (φ z)) =
      calpha p * deriv r y * Af z + calpha p * ((deriv r y - deriv r z) / |y - z| ^ (p + 1)) +
        R_eps_kernel p ε y z * deriv r z := by
    intro z
    by_cases hzy : z = y
    · subst hzy
      simp only [hg, hAf, sub_self, abs_zero, smul_eq_mul, mul_zero,
        Real.zero_rpow (show p + 1 ≠ 0 by linarith), Real.zero_rpow (show 1 + p ≠ 0 by linarith),
        div_zero, add_zero]
      rw [c08_aux_kernel_diag p ε z hp0]; ring
    have h : y ≠ z := Ne.symm hzy
    have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 h)
    obtain ⟨ξ, -, hsξ⟩ := c08_aux_secant_mvt hφdiff h
    set S := c01_secant φ y z with hS
    have hS0 : 0 < S := by rw [hsξ]; exact (hφd ξ).1
    have hSdef : S = (φ y - φ z) / (y - z) := by
      show c01_secant φ y z = _; unfold c01_secant; simp only [h, ↓reduceIte]
    have e : φ y - φ z = S * (y - z) := by rw [hSdef]; field_simp [sub_ne_zero.2 h]
    have hdiff : |φ y - φ z| = S * |y - z| := by rw [e, abs_mul, abs_of_pos hS0]
    have hbz : 0 < deriv φ z := (hφd z).1
    have hK' : R_eps_kernel p ε y z = calpha p * (1 - (a / S) ^ (p + 1)) / |y - z| ^ (1 + p) := by
      rfl
    simp only [hg, hAf, smul_eq_mul]
    rw [hwφ, hwφ, hK', abs_of_pos hbz, hdiff, show (1:ℝ) + p = p + 1 by ring,
      Real.mul_rpow hS0.le hw.le, Real.div_rpow ha0.le hS0.le, Real.rpow_add_one ha0.ne']
    simp only [← ha]
    have h1 := Real.rpow_pos_of_pos hS0 (p + 1)
    have h2 := Real.rpow_pos_of_pos hw (p + 1)
    have h3 := Real.rpow_pos_of_pos ha0 p
    field_simp
    ring
  have hsum_i : Integrable (fun z => calpha p * deriv r y * Af z +
      calpha p * ((deriv r y - deriv r z) / |y - z| ^ (p + 1)) + R_eps_kernel p ε y z * deriv r z) :=
    ((hAi.const_mul _).add (hBi.const_mul _)).add hKi
  have hca2 : calpha p * a ^ (p + 1) ≠ 0 := (mul_pos hca (Real.rpow_pos_of_pos ha0 _)).ne'
  have hJ : Integrable (fun z => |deriv φ z| • g (φ z)) := by
    have := hsum_i.const_mul (calpha p * a ^ (p + 1))⁻¹
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [← hpt z]; field_simp
  have hgi : Integrable g := by
    have := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd'
      hinj.injOn g).2 hJ.integrableOn
    rw [himg] at this
    exact integrableOn_univ.1 this
  refine ⟨?_, hBi, hKi, ?_⟩
  · simpa [hg, hφe] using hgi
  · have hcv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd' hinj.injOn g
    rw [himg, Measure.restrict_univ] at hcv
    have hfr : fracD p w (φ y) = calpha p * ∫ x, g x := rfl
    rw [hφe, hfr, hcv]
    unfold fracD R_eps_two
    have e2 : a ^ (p + 1) * (calpha p * ∫ z, |deriv φ z| • g (φ z)) =
        ∫ z, calpha p * a ^ (p + 1) * (|deriv φ z| • g (φ z)) := by
      rw [integral_const_mul]; ring
    rw [show deriv (c08_phi p (c_eps p ε)) y = a from rfl, e2]
    simp_rw [hpt]
    have i1 : Integrable (fun z => calpha p * deriv r y * Af z) := hAi.const_mul _
    have i2 : Integrable (fun z => calpha p * ((deriv r y - deriv r z) / |y - z| ^ (p + 1))) :=
      hBi.const_mul _
    have i12 : Integrable (fun z => calpha p * deriv r y * Af z +
        calpha p * ((deriv r y - deriv r z) / |y - z| ^ (p + 1))) := i1.add i2
    rw [integral_add i12 hKi, integral_add i1 i2, integral_const_mul, integral_const_mul]
    have : ∫ z, Af z = 0 := hA0
    rw [this]; ring


/-! ## Boundedness of `𝒰_ε`, `𝒱_ε`, transport of `G_μ` -/

/-- Blueprint: lem:c08_U_bounded.  `𝒰_ε, 𝒰_ε⁻¹` map `X_γ` to itself with uniform bounds;
`𝒰_ε` restricts to a bijection of `X_γ`. -/
theorem c08_U_bounded (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      Set.BijOn (U_eps p ε) (X_gamma p γ) (X_gamma p γ) ∧
      ∀ r ∈ X_gamma p γ, U_eps p ε r ∈ X_gamma p γ ∧ U_eps_inv p ε r ∈ X_gamma p γ ∧
        xNorm p γ (U_eps p ε r) + xNorm p γ (U_eps_inv p ε r) ≤ C * xNorm p γ r := by
  obtain ⟨c0, hc0, hc0', B, hB, hdata⟩ := c08_aux_phi_psi_data p hp hp1
  refine ⟨c0, hc0, fun γ => ⟨2 * ((4 + B) * 2 ^ (|γ| + 2 / p)), by positivity,
    fun ε hε0 hε => ?_⟩⟩
  have hp0 : 0 < p := by linarith
  have hc : |c_eps p ε| ≤ c0 := (c08_aux_c_eps_bound p ε hp hp1 hε0).2.trans hε
  obtain ⟨hφ2, hψ2, hl, hrr, hφid, hψid, hφnn, hψnn, hφ1, hψ1, hφ'', hψ'', hφjb, hψjb⟩ :=
    hdata _ hc
  have hφd : Differentiable ℝ (c08_phi p (c_eps p ε)) := hφ2.differentiable (by norm_num)
  have hψd : Differentiable ℝ (c08_phi_inv p (c_eps p ε)) := hψ2.differentiable (by norm_num)
  have hU : ∀ r ∈ X_gamma p γ, U_eps p ε r ∈ X_gamma p γ ∧
      xNorm p γ (U_eps p ε r) ≤ ((4 + B) * 2 ^ (|γ| + 2 / p)) * xNorm p γ r := fun r hr =>
    c08_aux_comp_X hp0 hB hψ2 hφd hrr hl hψid hψnn hψ1 hψ'' hψjb hr
  have hUi : ∀ r ∈ X_gamma p γ, U_eps_inv p ε r ∈ X_gamma p γ ∧
      xNorm p γ (U_eps_inv p ε r) ≤ ((4 + B) * 2 ^ (|γ| + 2 / p)) * xNorm p γ r := fun r hr =>
    c08_aux_comp_X hp0 hB hφ2 hψd hl hrr hφid hφnn hφ1 hφ'' hφjb hr
  refine ⟨⟨fun r hr => (hU r hr).1, fun r1 _ r2 _ h => ?_, fun r hr => ⟨U_eps_inv p ε r,
    (hUi r hr).1, ?_⟩⟩, fun r hr => ⟨(hU r hr).1, (hUi r hr).1, ?_⟩⟩
  · ext x
    have := congrFun h (c08_phi p (c_eps p ε) x)
    simp only [U_eps, psi_eps] at this
    rwa [hl x] at this
  · ext y; simp only [U_eps, U_eps_inv, psi_eps, phi_eps]; rw [hrr y]
  · have := (hU r hr).2; have := (hUi r hr).2; linarith

/-- Blueprint: lem:c08_conjugation_identity.  For `γ > 1 + 1/p`, `r ∈ X_γ`: `𝒰_ε r ∈ X_γ` and
`𝒱_ε(ℒ₀(𝒰_ε r)) = ℒ₀ r + b_ε r' + ℛ_ε r = ℒ_ε r` pointwise. -/
theorem c08_conjugation_identity (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, 1 + 1 / p < γ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      ∀ r ∈ X_gamma p γ, U_eps p ε r ∈ X_gamma p γ ∧ ∀ y : ℝ,
        V_eps p ε (L0 p (U_eps p ε r)) y = L0 p r y + b_eps p ε y * deriv r y + R_eps p ε r y ∧
        V_eps p ε (L0 p (U_eps p ε r)) y = L_eps p ε r y := by
  obtain ⟨ε1, hε1, hU⟩ := c08_U_bounded p hp hp1
  obtain ⟨ε2, hε2, hloc⟩ := c08_conj_local p hp hp1
  obtain ⟨ε3, hε3, hnl⟩ := c08_conj_nonlocal p hp hp1
  refine ⟨min ε1 (min ε2 ε3), by positivity, fun γ hγ ε hε0 hε r hr => ?_⟩
  have e1 : ε ≤ ε1 := hε.trans (min_le_left _ _)
  have e2 : ε ≤ ε2 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : ε ≤ ε3 := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨CU, -, hU⟩ := hU γ
  have hUr := ((hU ε hε0 e1).2 r hr).1
  have hr1 : ContDiff ℝ 1 r := hr.1.1
  obtain ⟨CL, -, hL1, -⟩ := c08_L1_embedding p γ hp hp1 hγ
  obtain ⟨-, -, -, hdL, -⟩ := hL1 r hr
  obtain ⟨M, hM⟩ := c08_aux_bounded_of_memLp_top (hr1.continuous_deriv le_rfl) hdL
  have hfirst : ∀ y, V_eps p ε (L0 p (U_eps p ε r)) y =
      L0 p r y + b_eps p ε y * deriv r y + R_eps p ε r y := by
    intro y
    have h1 := hloc ε hε0 e2 r hr1 y
    have h2 := ((hnl ε hε0 e3 r hr1 ⟨M, hM⟩ hr.1.2).2.2.2 y).2.2.2
    simp only [V_eps, L0, fracDdy, R_eps]
    linear_combination h1 + h2
  exact ⟨hUr, fun y => ⟨hfirst y, hfirst y⟩⟩

/-- Blueprint: lem:c08_V_bounded.  `𝒱_ε, 𝒱_ε⁻¹` map `Y_γ` to itself with uniform bounds;
`𝒱_ε` restricts to a bijection of `Y_γ`. -/
theorem c08_V_bounded (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      Set.BijOn (V_eps p ε) (Y_gamma p γ) (Y_gamma p γ) ∧
      ∀ G ∈ Y_gamma p γ, V_eps p ε G ∈ Y_gamma p γ ∧ V_eps_inv p ε G ∈ Y_gamma p γ ∧
        yNorm p γ (V_eps p ε G) + yNorm p γ (V_eps_inv p ε G) ≤ C * yNorm p γ G := by
  obtain ⟨c0, hc0, hc0', B, hB, hdata⟩ := c08_aux_phi_psi_data p hp hp1
  refine ⟨c0, hc0, fun γ => ⟨2 * ((2 * (4 + 4 * B) + 1) * 2 ^ (|γ| + 1 / p)), by positivity,
    fun ε hε0 hε => ?_⟩⟩
  have hp0 : 0 < p := by linarith
  have hc : |c_eps p ε| ≤ c0 := (c08_aux_c_eps_bound p ε hp hp1 hε0).2.trans hε
  obtain ⟨hφ2, hψ2, hl, hrr, hφid, hψid, hφnn, hψnn, hφ1, hψ1, hφ'', hψ'', hφjb, hψjb⟩ :=
    hdata _ hc
  have hφd : Differentiable ℝ (c08_phi p (c_eps p ε)) := hφ2.differentiable (by norm_num)
  have hψd : Differentiable ℝ (c08_phi_inv p (c_eps p ε)) := hψ2.differentiable (by norm_num)
  obtain ⟨waC, wa0, wa1, wa', waid⟩ := c08_aux_weight hp0 hp1 hB hφ2 hφid hφ1 hφ''
  obtain ⟨wbC, wb0, wb1, wb', wbid⟩ := c08_aux_weight hp0 hp1 hB hψ2 hψid hψ1 hψ''
  have hA : (0:ℝ) ≤ 4 + 4 * B := by positivity
  have hV : ∀ G ∈ Y_gamma p γ, V_eps p ε G ∈ Y_gamma p γ ∧
      yNorm p γ (V_eps p ε G) ≤ ((2 * (4 + 4 * B) + 1) * 2 ^ (|γ| + 1 / p)) * yNorm p γ G :=
    fun G hG => c08_aux_comp_Y hp0 hA (hφ2.of_le (by norm_num)) hψd hl hrr hφid hφnn hφ1 hφjb
      waC wa0 wa1 wa' waid hG
  have hVi : ∀ G ∈ Y_gamma p γ, V_eps_inv p ε G ∈ Y_gamma p γ ∧
      yNorm p γ (V_eps_inv p ε G) ≤ ((2 * (4 + 4 * B) + 1) * 2 ^ (|γ| + 1 / p)) * yNorm p γ G :=
    fun G hG => c08_aux_comp_Y hp0 hA (hψ2.of_le (by norm_num)) hφd hrr hl hψid hψnn hψ1 hψjb
      wbC wb0 wb1 wb' wbid hG
  have hVVi : ∀ G, V_eps p ε (V_eps_inv p ε G) = G := by
    intro G; ext y
    obtain ⟨-, -, hd1, hd2⟩ := c08_aux_phi_inverse p (c_eps p ε) hp hp1
      (hc.trans hc0')
    simp only [V_eps, V_eps_inv, phi_eps, psi_eps]
    rw [hl y, ← mul_assoc, ← Real.mul_rpow (hφ1 y).1.le (hψ1 _).1.le,
      mul_comm (deriv (c08_phi p (c_eps p ε)) y), hd2 y, Real.one_rpow, one_mul]
  refine ⟨⟨fun G hG => (hV G hG).1, fun G1 _ G2 _ h => ?_, fun G hG => ⟨V_eps_inv p ε G,
    (hVi G hG).1, hVVi G⟩⟩, fun G hG => ⟨(hV G hG).1, (hVi G hG).1, ?_⟩⟩
  · have e1 : V_eps_inv p ε (V_eps p ε G1) = G1 := by
      ext y
      obtain ⟨-, -, hd1, hd2⟩ := c08_aux_phi_inverse p (c_eps p ε) hp hp1 (hc.trans hc0')
      simp only [V_eps, V_eps_inv, phi_eps, psi_eps]
      rw [hrr y, ← mul_assoc, ← Real.mul_rpow (hψ1 y).1.le (hφ1 _).1.le,
        mul_comm (deriv (c08_phi_inv p (c_eps p ε)) y), hd1 y, Real.one_rpow, one_mul]
    have e2 : V_eps_inv p ε (V_eps p ε G2) = G2 := by
      ext y
      obtain ⟨-, -, hd1, hd2⟩ := c08_aux_phi_inverse p (c_eps p ε) hp hp1 (hc.trans hc0')
      simp only [V_eps, V_eps_inv, phi_eps, psi_eps]
      rw [hrr y, ← mul_assoc, ← Real.mul_rpow (hψ1 y).1.le (hφ1 _).1.le,
        mul_comm (deriv (c08_phi_inv p (c_eps p ε)) y), hd1 y, Real.one_rpow, one_mul]
    rw [← e1, ← e2, h]
  · have := (hV G hG).2; have := (hVi G hG).2; linarith

/-- Blueprint: lem:c08_V_inverse_minus_identity.  For `G ∈ Y_γ ∩ C²((1,∞))` with
`M(G) = sup_{y>1} ⟨y⟩^γ(|G| + |G'| + |G''|) < ∞`: `‖(𝒱_ε⁻¹ - I)G‖_{Y_γ} ≤ C ε M(G)`. -/
theorem c08_V_inverse_minus_identity (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      ∀ G ∈ Y_gamma p γ, ContDiffOn ℝ 2 G (Ioi 1) →
        BddAbove ((fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1) →
        V_eps_inv p ε G - G ∈ Y_gamma p γ ∧
        yNorm p γ (V_eps_inv p ε G - G) ≤
          C * ε * sSup ((fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1) := by
  obtain ⟨c0, hc0, -, Cψ, hCψ, hψb⟩ := c08_psi_bounds p hp hp1
  obtain ⟨c1, hc1, hc1', B, hB, hdata⟩ := c08_aux_phi_psi_data p hp hp1
  refine ⟨min (min c0 c1) (1 / (2 * Cψ)), by positivity, fun γ =>
    ⟨16 * Cψ * 2 ^ |γ| + 1, by positivity, fun ε hε0 hε G hG hG2 hbdd => ?_⟩⟩
  have hp0 : 0 < p := by linarith
  have hεc0 : ε ≤ c0 := hε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεc1 : ε ≤ c1 := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεC : ε ≤ 1 / (2 * Cψ) := hε.trans (min_le_right _ _)
  have hcε := (c08_aux_c_eps_bound p ε hp hp1 hε0).2
  set c := c_eps p ε with hcdef
  obtain ⟨-, hψimg, hψy⟩ := hψb c (hcε.trans hεc0)
  obtain ⟨-, hψ2, -, -, -, hψid, -, -, -, hψ1, -, hψ'', -, -⟩ := hdata c (hcε.trans hεc1)
  set ψ := c08_phi_inv p c with hψdef
  have hψd : Differentiable ℝ ψ := hψ2.differentiable (by norm_num)
  obtain ⟨waC, wa0, -, -, waid⟩ := c08_aux_weight hp0 hp1 hB hψ2 hψid hψ1 hψ''
  set a : ℝ → ℝ := fun y => deriv ψ y ^ (p + 1) with hadef
  have had : Differentiable ℝ a := waC.differentiable (by norm_num)
  set S := (fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1
  set M := sSup S
  have hM : ∀ y, 1 < y → jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|) ≤ M :=
    fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
  have hM0 : 0 ≤ M := by
    refine le_trans ?_ (hM 2 (by norm_num))
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos 2) γ
    positivity
  have hMb : ∀ z, 1 < z → |G z| ≤ M * jb z ^ (-γ) ∧ |deriv G z| ≤ M * jb z ^ (-γ) ∧
      |deriv (deriv G) z| ≤ M * jb z ^ (-γ) := by
    intro z hz
    have h := hM z hz
    have hg := Real.rpow_pos_of_pos (c08_aux_jb_pos z) γ
    have a0 := abs_nonneg (G z); have a1 := abs_nonneg (deriv G z)
    have a2 := abs_nonneg (deriv (deriv G) z)
    refine ⟨c08_aux_div_weight ?_, c08_aux_div_weight ?_, c08_aux_div_weight ?_⟩ <;> nlinarith
  obtain ⟨hGd, -, hG'C⟩ := (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).1
    (show ContDiffOn ℝ (1 + 1) G (Ioi 1) from hG2)
  have hGda : ∀ z, 1 < z → DifferentiableAt ℝ G z := fun z hz =>
    (hGd z hz).differentiableAt (Ioi_mem_nhds hz)
  have hG'da : ∀ z, 1 < z → DifferentiableAt ℝ (deriv G) z := fun z hz =>
    ((hG'C.differentiableOn (by norm_num)) z hz).differentiableAt (Ioi_mem_nhds hz)
  set H := V_eps_inv p ε G - G with hHdef
  have hH : H = fun y => a y * G (ψ y) - G y := rfl
  set L : ℝ := 2 ^ |γ|
  set e : ℝ := Cψ * ε
  have he0 : 0 ≤ e := by positivity
  have he2 : e ≤ 1 / 2 := by
    have : Cψ * ε ≤ Cψ * (1 / (2 * Cψ)) := mul_le_mul_of_nonneg_left hεC hCψ.le
    calc e ≤ Cψ * (1 / (2 * Cψ)) := this
      _ = 1 / 2 := by field_simp
  have hce : ∀ q : ℝ, q ≤ 0 → Cψ * |c| * jb 0 ^ q ≤ e := fun _ _ => by simp [jb]; nlinarith
  -- bounds on `(1, ∞)`
  have key : ∀ y, 1 < y → |H y| ≤ 2 * e * (M * L * jb y ^ (-γ)) ∧
      |deriv H y| ≤ 6 * e * (M * L * jb y ^ (-γ)) := by
    intro y hy
    set x := ψ y with hxdef
    have hx1 : 1 < x := by
      have : x ∈ ψ '' Ioi 1 := ⟨y, hy, rfl⟩
      rw [hψimg] at this; exact this
    obtain ⟨hj1, hj2, -, hψlo, hψhi, -, hxy, -, hψ''b, hpow⟩ := hψy y
    have hjneg : ∀ q : ℝ, q ≤ 0 → Cψ * |c| * jb y ^ q ≤ e := by
      intro q hq
      have h1 : jb y ^ q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) hq
      have h2 : Cψ * |c| ≤ Cψ * ε := mul_le_mul_of_nonneg_left hcε hCψ.le
      have h3 : 0 ≤ Cψ * |c| := by positivity
      calc Cψ * |c| * jb y ^ q ≤ Cψ * |c| * 1 := mul_le_mul_of_nonneg_left h1 h3
        _ ≤ e := by rw [mul_one]; exact h2
    have hxy' : |x - y| ≤ e := hxy.trans (hjneg _ (by linarith))
    have hψ''e : |deriv (deriv ψ) y| ≤ e := hψ''b.trans (hjneg _ (by linarith))
    have hpowe := hpow.trans (hjneg _ (by linarith))
    have ha1 : |a y - 1| ≤ e := by
      have := abs_nonneg (deriv ψ y ^ (p + 2) - 1); simp only [hadef]; linarith
    have ha2 : |deriv ψ y ^ (p + 2) - 1| ≤ e := by
      have := abs_nonneg (deriv ψ y ^ (p + 1) - 1); linarith
    -- the segment between `x` and `y`
    have hseg : ∀ ξ ∈ uIcc x y, 1 < ξ ∧ jb ξ ^ (-γ) ≤ L * jb y ^ (-γ) := by
      intro ξ hξ
      have hξ1 : 1 < ξ := by
        rcases le_total x y with h | h
        · rw [uIcc_of_le h] at hξ; linarith [hξ.1]
        · rw [uIcc_of_ge h] at hξ; linarith [hξ.1]
      have hξy : |ξ - y| ≤ 1 / 2 := by
        have : |ξ - y| ≤ |x - y| := by
          rcases le_total x y with h | h
          · rw [uIcc_of_le h] at hξ
            rw [abs_of_nonpos (by linarith [hξ.2]), abs_of_nonpos (by linarith)]; linarith [hξ.1]
          · rw [uIcc_of_ge h] at hξ
            rw [abs_of_nonneg (by linarith [hξ.1]), abs_of_nonneg (by linarith)]; linarith [hξ.2]
        linarith
      have hl := c08_aux_jb_lip ξ y
      have hjξ := c08_aux_one_le_jb ξ
      have hjy := c08_aux_one_le_jb y
      have hlip := abs_le.1 (hl.trans hξy)
      refine ⟨hξ1, ?_⟩
      exact c08_aux_jb_rpow_compare (x := y) (y := ξ) (by linarith) (by linarith) (-γ) |>.trans
        (by rw [abs_neg])
    have hQ0 : 0 ≤ M * L * jb y ^ (-γ) := by
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-γ); positivity
    have hGx : |G x| ≤ M * L * jb y ^ (-γ) := by
      have h := (hMb x hx1).1
      have h2 := (hseg x left_mem_uIcc).2
      calc |G x| ≤ M * jb x ^ (-γ) := h
        _ ≤ M * (L * jb y ^ (-γ)) := mul_le_mul_of_nonneg_left h2 hM0
        _ = _ := by ring
    have hG'x : |deriv G x| ≤ M * L * jb y ^ (-γ) := by
      have h := (hMb x hx1).2.1
      have h2 := (hseg x left_mem_uIcc).2
      calc |deriv G x| ≤ M * jb x ^ (-γ) := h
        _ ≤ M * (L * jb y ^ (-γ)) := mul_le_mul_of_nonneg_left h2 hM0
        _ = _ := by ring
    have hmvt0 : |G x - G y| ≤ (M * L * jb y ^ (-γ)) * |x - y| :=
      c08_aux_mvt_bound (fun ξ hξ => hGda ξ (hseg ξ hξ).1) (fun ξ hξ => by
        have := (hMb ξ (hseg ξ hξ).1).2.1
        calc |deriv G ξ| ≤ M * jb ξ ^ (-γ) := this
          _ ≤ M * (L * jb y ^ (-γ)) := mul_le_mul_of_nonneg_left (hseg ξ hξ).2 hM0
          _ = _ := by ring)
    have hmvt1 : |deriv G x - deriv G y| ≤ (M * L * jb y ^ (-γ)) * |x - y| :=
      c08_aux_mvt_bound (fun ξ hξ => hG'da ξ (hseg ξ hξ).1) (fun ξ hξ => by
        have := (hMb ξ (hseg ξ hξ).1).2.2
        calc |deriv (deriv G) ξ| ≤ M * jb ξ ^ (-γ) := this
          _ ≤ M * (L * jb y ^ (-γ)) := mul_le_mul_of_nonneg_left (hseg ξ hξ).2 hM0
          _ = _ := by ring)
    set Q := M * L * jb y ^ (-γ)
    have hmvt0' : |G x - G y| ≤ Q * e := hmvt0.trans (mul_le_mul_of_nonneg_left hxy' hQ0)
    have hmvt1' : |deriv G x - deriv G y| ≤ Q * e := hmvt1.trans (mul_le_mul_of_nonneg_left hxy' hQ0)
    constructor
    · rw [hH]
      simp only
      have e1 : a y * G x - G y = (a y - 1) * G x + (G x - G y) := by ring
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have := mul_le_mul ha1 hGx (abs_nonneg _) he0
      linarith
    · -- derivative
      have hψ'pos : 0 < deriv ψ y := (hψ1 y).1
      have hψ'd : DifferentiableAt ℝ (deriv ψ) y := by
        obtain ⟨-, -, hC⟩ := contDiff_succ_iff_deriv.1 (show ContDiff ℝ (1 + 1) ψ from hψ2)
        exact (hC.differentiable (by norm_num)) y
      have hda : HasDerivAt a (deriv (deriv ψ) y * (p + 1) * deriv ψ y ^ (p + 1 - 1)) y :=
        hψ'd.hasDerivAt.rpow_const (Or.inl hψ'pos.ne')
      have hc1 : HasDerivAt (fun z => G (ψ z)) (deriv G x * deriv ψ y) y :=
        (hGda x hx1).hasDerivAt.comp y (hψd y).hasDerivAt
      have hHd : HasDerivAt H (deriv (deriv ψ) y * (p + 1) * deriv ψ y ^ (p + 1 - 1) * G x +
          a y * (deriv G x * deriv ψ y) - deriv G y) y := by
        rw [hH]; exact (hda.mul hc1).sub (hGda y hy).hasDerivAt
      rw [hHd.deriv]
      have hay : a y * deriv ψ y = deriv ψ y ^ (p + 2) := by
        simp only [hadef]; rw [show p + 2 = (p + 1) + 1 by ring, Real.rpow_add_one hψ'pos.ne' (p + 1)]
      have e1 : deriv (deriv ψ) y * (p + 1) * deriv ψ y ^ (p + 1 - 1) * G x +
          a y * (deriv G x * deriv ψ y) - deriv G y =
          (deriv (deriv ψ) y * (p + 1) * deriv ψ y ^ p) * G x +
          (deriv ψ y ^ (p + 2) - 1) * deriv G x + (deriv G x - deriv G y) := by
        rw [show p + 1 - 1 = p by ring, ← hay]; ring
      rw [e1]
      have hpp : deriv ψ y ^ p ≤ 2 := by
        calc deriv ψ y ^ p ≤ 2 ^ p := Real.rpow_le_rpow hψ'pos.le (hψ1 y).2 hp0.le
          _ ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
          _ = 2 := Real.rpow_one 2
      have hppos : 0 < deriv ψ y ^ p := Real.rpow_pos_of_pos hψ'pos p
      have ha' : |deriv (deriv ψ) y * (p + 1) * deriv ψ y ^ p| ≤ 4 * e := by
        rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < p + 1), abs_of_pos hppos]
        have k1 : |deriv (deriv ψ) y| * (p + 1) ≤ e * 2 :=
          mul_le_mul hψ''e (by linarith) (by linarith) he0
        have k2 := mul_le_mul k1 hpp hppos.le (by positivity)
        linarith
      have t1 := mul_le_mul ha' hGx (abs_nonneg _) (by positivity)
      have t2 := mul_le_mul ha2 hG'x (abs_nonneg _) he0
      calc _ ≤ |(deriv (deriv ψ) y * (p + 1) * deriv ψ y ^ p) * G x| +
            |(deriv ψ y ^ (p + 2) - 1) * deriv G x| + |deriv G x - deriv G y| := abs_add_three _ _ _
        _ ≤ 4 * e * Q + e * Q + Q * e := by
            rw [abs_mul (deriv (deriv ψ) y * (p + 1) * deriv ψ y ^ p) (G x),
              abs_mul (deriv ψ y ^ (p + 2) - 1) (deriv G x)]
            linarith
        _ = 6 * e * Q := by ring
  have hzero : ∀ y, y < 1 → H =ᶠ[nhds y] fun _ => 0 := fun y hy =>
    Filter.eventually_of_mem (Iio_mem_nhds hy) (fun z hz => by
      rw [hH]; simp only [hadef]
      rw [waid z hz, hψid z (le_of_lt hz), one_mul, sub_self])
  -- the norm bound
  have hjγ : ∀ y : ℝ, jb y ^ γ * jb y ^ (-γ) = 1 := fun y => by
    rw [← Real.rpow_add (c08_aux_jb_pos y), add_neg_cancel, Real.rpow_zero]
  have hK0 : 0 ≤ 8 * e * M * L := by positivity
  have hpt1 : ∀ y, 0 ≤ y → y ≠ 1 →
      jb y ^ γ * (‖H y‖ + jb y ^ (-1 / p) * ‖deriv H y‖) ≤ 8 * e * M * L := by
    intro y hy0 hy1
    rcases lt_or_gt_of_ne hy1 with h | h
    · rw [(hzero y h).eq_of_nhds, (hzero y h).deriv_eq]; simp; exact hK0
    · obtain ⟨k1, k2⟩ := key y h
      have hw : jb y ^ (-1 / p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
        (c08_aux_one_le_jb y) (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le)
      have hw0 : 0 ≤ jb y ^ (-1 / p) := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
      have hg := Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have k3 : jb y ^ (-1 / p) * |deriv H y| ≤ 6 * e * (M * L * jb y ^ (-γ)) :=
        (mul_le_of_le_one_left (abs_nonneg _) hw).trans k2
      calc jb y ^ γ * (|H y| + jb y ^ (-1 / p) * |deriv H y|)
          ≤ jb y ^ γ * (2 * e * (M * L * jb y ^ (-γ)) + 6 * e * (M * L * jb y ^ (-γ))) :=
            mul_le_mul_of_nonneg_left (add_le_add k1 k3) hg.le
        _ = 8 * e * M * L * (jb y ^ γ * jb y ^ (-γ)) := by ring
        _ = 8 * e * M * L := by rw [hjγ, mul_one]
  have hpt2 : ∀ y, y ≤ 0 → jb y ^ γ * (‖H y‖ + jb y * ‖deriv H y‖) ≤ 8 * e * M * L := by
    intro y hy
    have h : y < 1 := by linarith
    rw [(hzero y h).eq_of_nhds, (hzero y h).deriv_eq]; simp; exact hK0
  have hE1 : essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖H y‖ + jb y ^ (-1 / p) * ‖deriv H y‖)))
      (volume.restrict (Ici 0)) ≤ ENNReal.ofReal (8 * e * M * L) := by
    refine essSup_le_of_ae_le _ ?_
    have hne : ∀ᵐ y ∂(volume.restrict (Ici (0:ℝ))), y ≠ 1 := by
      apply ae_restrict_of_ae
      rw [ae_iff]; simp
    filter_upwards [hne, ae_restrict_mem measurableSet_Ici] with y hy1 hy0
    exact ENNReal.ofReal_le_ofReal (hpt1 y hy0 hy1)
  have hE2 : essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖H y‖ + jb y * ‖deriv H y‖)))
      (volume.restrict (Iic 0)) ≤ ENNReal.ofReal (8 * e * M * L) := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy0
    exact ENNReal.ofReal_le_ofReal (hpt2 y hy0)
  have hYle : Y_gamma_norm p γ H ≤ ENNReal.ofReal (16 * e * M * L) := by
    unfold Y_gamma_norm
    calc _ ≤ ENNReal.ofReal (8 * e * M * L) + ENNReal.ofReal (8 * e * M * L) := add_le_add hE1 hE2
      _ = ENNReal.ofReal (16 * e * M * L) := by
          rw [← ENNReal.ofReal_add hK0 hK0]; ring_nf
  have hLL : LocallyLipschitz H := by
    rw [hH]
    exact (c08_aux_locallyLipschitz_mul waC.locallyLipschitz
      (LocallyLipschitz.comp (f := G) (g := ψ) hG.1 (hψ2.of_le (by norm_num)).locallyLipschitz)).sub
      hG.1
  refine ⟨⟨hLL, lt_of_le_of_lt hYle ENNReal.ofReal_lt_top⟩, ?_⟩
  unfold yNorm
  have h1 : (Y_gamma_norm p γ H).toReal ≤ 16 * e * M * L :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hYle
  have hεM : 0 ≤ ε * M := mul_nonneg hε0 hM0
  calc (Y_gamma_norm p γ H).toReal ≤ 16 * e * M * L := h1
    _ = (16 * Cψ * L) * (ε * M) := by simp only [e]; ring
    _ ≤ (16 * Cψ * L + 1) * (ε * M) := by nlinarith
    _ = _ := by ring

/-- A real Schwartz function has `sup_{y>1} ⟨y⟩^γ(|S| + |S'| + |S''|) < ∞`. -/
theorem c08_aux_schwartz_M_bdd (S : SchwartzMap ℝ ℝ) (γ : ℝ) :
    BddAbove ((fun y => jb y ^ γ * (|S y| + |deriv S y| + |deriv (deriv S) y|)) '' Ioi 1) := by
  set K := ⌈|γ|⌉₊
  have hA : ∀ n : ℕ, ∃ A, ∀ y : ℝ, (1 + |y|) ^ K * |iteratedDeriv n S y| ≤ A := by
    intro n
    refine ⟨2 ^ K * (Finset.Iic (K, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S,
      fun y => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (K, n)) le_rfl le_rfl S y
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, Real.norm_eq_abs] at this
    exact this
  obtain ⟨A0, h0⟩ := hA 0
  obtain ⟨A1, h1⟩ := hA 1
  obtain ⟨A2, h2⟩ := hA 2
  refine ⟨A0 + A1 + A2, ?_⟩
  rintro _ ⟨y, -, rfl⟩
  have hjb : jb y ^ γ ≤ (1 + |y|) ^ K := by
    have h1 := c08_aux_one_le_jb y
    calc jb y ^ γ ≤ jb y ^ (K:ℝ) := Real.rpow_le_rpow_of_exponent_le h1
          ((le_abs_self γ).trans (Nat.le_ceil _))
      _ = jb y ^ K := Real.rpow_natCast _ _
      _ ≤ (1 + |y|) ^ K := pow_le_pow_left₀ (by linarith) (c08_aux_jb_le_one_add y) K
  have e1 : iteratedDeriv 1 S = deriv S := iteratedDeriv_one
  have e2 : iteratedDeriv 2 S = deriv (deriv S) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have g0 := h0 y; have g1 := h1 y; have g2 := h2 y
  rw [iteratedDeriv_zero] at g0
  rw [e1] at g1
  rw [e2] at g2
  simp only
  have hn : 0 ≤ |S y| + |deriv S y| + |deriv (deriv S) y| := by positivity
  calc jb y ^ γ * (|S y| + |deriv S y| + |deriv (deriv S) y|)
      ≤ (1 + |y|) ^ K * (|S y| + |deriv S y| + |deriv (deriv S) y|) :=
        mul_le_mul_of_nonneg_right hjb hn
    _ ≤ _ := by nlinarith

/-- Blueprint: lem:c08_V_inverse_G_mu.  `‖(𝒱_ε⁻¹ - I)G_μ‖_{Y_γ} ≤ C ε |1 - μ/μ_*|`; in particular
`≤ C ε δ/|μ_*|` on `B̄(μ_*,δ)`. -/
theorem c08_V_inverse_G_mu (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      (∀ μ : ℂ, V_eps_inv p ε (G_mu p μ) - G_mu p μ ∈ Y_gamma p γ ∧
        yNorm p γ (V_eps_inv p ε (G_mu p μ) - G_mu p μ) ≤ C * ε * ‖1 - μ / mu_star p‖) ∧
      ∀ δ : ℝ, 0 < δ → ∀ μ ∈ Bbar p δ,
        yNorm p γ (V_eps_inv p ε (G_mu p μ) - G_mu p μ) ≤ C * ε * δ / ‖mu_star p‖ := by
  obtain ⟨-, ⟨γ₁, γ₂, h1, h2, h3⟩, -⟩ := c02_parameter_range_nonempty p hp hp1
  let P : parameters := ⟨p, γ₁, γ₂, hp, hp1, h1, h2, h3⟩
  obtain ⟨-, -, ⟨Sp, hSp⟩, ⟨Sm, hSm⟩, hGY, -⟩ := c02_G_pm_properties P
  obtain ⟨hdec, -⟩ := c02_G_mu_decomposition P
  obtain ⟨εc, hεc, hV⟩ := c08_V_inverse_minus_identity p hp hp1
  refine ⟨εc, hεc, fun γ => ?_⟩
  obtain ⟨C, hC, hVγ⟩ := hV γ
  set Mf := fun G : ℝ → ℝ =>
    sSup ((fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1)
  have hMnn : ∀ S : SchwartzMap ℝ ℝ, 0 ≤ Mf S := by
    intro S
    obtain ⟨b, hb⟩ := c08_aux_schwartz_M_bdd S γ
    refine le_trans ?_ (le_csSup ⟨b, hb⟩ ⟨2, by norm_num, rfl⟩)
    have := Real.rpow_pos_of_pos (c08_aux_jb_pos 2) γ
    positivity
  set Mp := Mf (G_plus p)
  set Mm := Mf (G_minus p)
  have hMp : 0 ≤ Mp := by rw [show Mp = Mf Sp by rw [hSp]]; exact hMnn Sp
  have hMm : 0 ≤ Mm := by rw [show Mm = Mf Sm by rw [hSm]]; exact hMnn Sm
  refine ⟨2 * C * (Mp + Mm) + 1, by positivity, fun ε hε0 hε => ?_⟩
  have hsmooth : ∀ S : SchwartzMap ℝ ℝ, ContDiffOn ℝ 2 S (Ioi 1) := fun S =>
    (S.smooth 2).contDiffOn
  have hplus := hVγ ε hε0 hε (G_plus p) (hGY γ).1 (by rw [← hSp]; exact hsmooth Sp)
    (by rw [← hSp]; exact c08_aux_schwartz_M_bdd Sp γ)
  have hminus := hVγ ε hε0 hε (G_minus p) (hGY γ).2 (by rw [← hSm]; exact hsmooth Sm)
    (by rw [← hSm]; exact c08_aux_schwartz_M_bdd Sm γ)
  have main : ∀ μ : ℂ, V_eps_inv p ε (G_mu p μ) - G_mu p μ ∈ Y_gamma p γ ∧
      yNorm p γ (V_eps_inv p ε (G_mu p μ) - G_mu p μ) ≤
        (2 * C * (Mp + Mm) + 1) * ε * ‖1 - μ / mu_star p‖ := by
    intro μ
    set z := 1 - μ / mu_star p
    have e : V_eps_inv p ε (G_mu p μ) - G_mu p μ = fun x =>
        z.re * (V_eps_inv p ε (G_plus p) - G_plus p) x +
          z.im * (V_eps_inv p ε (G_minus p) - G_minus p) x := by
      rw [hdec μ]
      funext x
      simp only [V_eps_inv, Pi.sub_apply]
      ring
    obtain ⟨hm, hn⟩ := c02_aux_Y_lin P (γ := γ) z.re z.im hplus.1 hminus.1
    rw [e]
    refine ⟨hm, hn.trans ?_⟩
    have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hyp0 : 0 ≤ yNorm p γ (V_eps_inv p ε (G_plus p) - G_plus p) := ENNReal.toReal_nonneg
    have hym0 : 0 ≤ yNorm p γ (V_eps_inv p ε (G_minus p) - G_minus p) := ENNReal.toReal_nonneg
    have a1 : |z.re| * yNorm p γ (V_eps_inv p ε (G_plus p) - G_plus p) ≤ ‖z‖ * (C * ε * Mp) :=
      mul_le_mul hre hplus.2 hyp0 hz0
    have a2 : |z.im| * yNorm p γ (V_eps_inv p ε (G_minus p) - G_minus p) ≤ ‖z‖ * (C * ε * Mm) :=
      mul_le_mul him hminus.2 hym0 hz0
    have : 0 ≤ ‖z‖ * ε * (C * (Mp + Mm) + 1) := by positivity
    nlinarith
  refine ⟨main, fun δ hδ μ hμ => ?_⟩
  refine (main μ).2.trans ?_
  have hms : mu_star p ≠ 0 := by
    have := c02_aux_mu_star_ne P; exact this
  have hz : ‖1 - μ / mu_star p‖ ≤ δ / ‖mu_star p‖ := by
    have e : 1 - μ / mu_star p = (mu_star p - μ) / mu_star p := by field_simp
    rw [e, norm_div, div_le_div_iff_of_pos_right (norm_pos_iff.2 hms)]
    have : dist μ (mu_star p) ≤ δ := hμ
    rw [dist_eq_norm, ← norm_neg] at this
    simpa using this
  have : 0 ≤ (2 * C * (Mp + Mm) + 1) * ε := by positivity
  calc (2 * C * (Mp + Mm) + 1) * ε * ‖1 - μ / mu_star p‖
      ≤ (2 * C * (Mp + Mm) + 1) * ε * (δ / ‖mu_star p‖) := mul_le_mul_of_nonneg_left hz this
    _ = _ := by ring


/-! ## Bounds for the remainder -/

/-- Blueprint: lem:c08_R1_bound.  `‖ℛ_{1,ε} r‖_{Y_γ} ≤ C ε ‖r‖_{X_γ}`. -/
theorem c08_R1_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      ∀ r ∈ X_gamma p γ, R_eps_one p ε r ∈ Y_gamma p γ ∧
        yNorm p γ (R_eps_one p ε r) ≤ C * ε * xNorm p γ r := by
  obtain ⟨c0, hc0, hc0', -, ⟨Cb, hCb, hb⟩, -, -⟩ := c08_phi_bounds p hp hp1
  refine ⟨c0, hc0, fun γ => ⟨2 * Cb, by positivity, fun ε hε0 hε r hr => ?_⟩⟩
  have hcε := c08_aux_c_eps_bound p ε hp hp1 hε0
  have hc : |c_eps p ε| ≤ c0 := hcε.2.trans hε
  obtain ⟨hφ, hpos, -⟩ := c08_phi_diffeo p (c_eps p ε) hp hp1 hcε.1
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (c08_phi p (c_eps p ε))) :=
    (contDiff_infty_iff_deriv.1 hφ).2
  set a : ℝ → ℝ := fun y => deriv (phi_eps p ε) y ^ (p + 1) - 1 with ha
  have haC : ContDiff ℝ 1 a := by
    simp only [ha, phi_eps]
    exact ((hd.of_le (by norm_cast)).rpow_const_of_ne
      (fun x => (hpos x).ne')).sub contDiff_const
  have hrC : ContDiff ℝ 1 r := hr.1.1
  have hR : R_eps_one p ε r = fun y => a y * r y := rfl
  have hRC : ContDiff ℝ 1 (R_eps_one p ε r) := by rw [hR]; exact haC.mul hrC
  have hderiv : ∀ y, deriv (R_eps_one p ε r) y = deriv a y * r y + a y * deriv r y := by
    intro y; rw [hR]
    exact deriv_mul (haC.differentiable (by norm_num) y) (hrC.differentiable (by norm_num) y)
  have hda : ∀ y, deriv a y = deriv (fun y => deriv (c08_phi p (c_eps p ε)) y ^ (p + 1)) y := by
    intro y; simp only [ha, phi_eps]; exact deriv_sub_const _
  have hA : ∀ y, |a y| ≤ Cb * ε ∧ jb y * |deriv a y| ≤ Cb * ε := by
    intro y
    have h := hb _ hc y
    have hw : jb y ^ (-p - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by linarith)
    have hce : Cb * |c_eps p ε| * jb y ^ (-p - 1) ≤ Cb * ε := by
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-p - 1)
      calc Cb * |c_eps p ε| * jb y ^ (-p - 1) ≤ Cb * |c_eps p ε| * 1 := by gcongr
        _ ≤ Cb * ε := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hcε.2 hCb.le
    rw [hda]
    have h0 : 0 ≤ jb y * |deriv (fun y => deriv (c08_phi p (c_eps p ε)) y ^ (p + 1)) y| :=
      mul_nonneg (c08_aux_jb_pos y).le (abs_nonneg _)
    constructor
    · simp only [ha, phi_eps]; linarith [abs_nonneg (deriv (c08_phi p (c_eps p ε)) y ^ (p + 1) - 1)]
    · linarith [abs_nonneg (deriv (c08_phi p (c_eps p ε)) y ^ (p + 1) - 1)]
  have hK : 0 ≤ 2 * Cb * ε := by positivity
  refine (fun H => ?_) (c08_aux_yNorm_le_of_X (G := R_eps_one p ε r) hK hr ?_ ?_)
  · obtain ⟨hfin, hle⟩ := H
    exact ⟨⟨hRC.locallyLipschitz, hfin⟩, by rw [mul_assoc] at hle ⊢; linarith⟩
  · intro y hy
    obtain ⟨hA1, hA2⟩ := hA y
    have hj := c08_aux_one_le_jb y
    have hw0 : 0 ≤ jb y ^ (-1 / p) := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
    have hw1 : jb y ^ (-1 / p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hj (by
        have : 0 < p := by linarith
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le)
    have hw2 : 0 ≤ jb y ^ (-2 / p) := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
    have hg0 : 0 < jb y ^ γ := Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ
    have hda1 : |deriv a y| ≤ Cb * ε := by nlinarith [abs_nonneg (deriv a y)]
    rw [hderiv y]
    simp only [Real.norm_eq_abs, hR]
    rw [abs_mul]
    have e1 : |deriv a y * r y + a y * deriv r y| ≤ |deriv a y| * |r y| + |a y| * |deriv r y| := by
      rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    have hr0 := abs_nonneg (r y); have hr1 := abs_nonneg (deriv r y)
    have hr2 := abs_nonneg (deriv (deriv r) y)
    have hb1 : |a y| * |r y| + jb y ^ (-1 / p) * |deriv a y * r y + a y * deriv r y| ≤
        2 * Cb * ε * (|r y| + jb y ^ (-1 / p) * |deriv r y| + jb y ^ (-2 / p) * |deriv (deriv r) y|) := by
      have := mul_le_mul_of_nonneg_left e1 hw0
      have t1 : |a y| * |r y| ≤ Cb * ε * |r y| := mul_le_mul_of_nonneg_right hA1 hr0
      have t2 : jb y ^ (-1 / p) * (|deriv a y| * |r y|) ≤ Cb * ε * |r y| := by
        calc jb y ^ (-1 / p) * (|deriv a y| * |r y|) ≤ 1 * (Cb * ε * |r y|) :=
              mul_le_mul hw1 (mul_le_mul_of_nonneg_right hda1 hr0) (by positivity) zero_le_one
          _ = _ := one_mul _
      have t3 : jb y ^ (-1 / p) * (|a y| * |deriv r y|) ≤ Cb * ε * (jb y ^ (-1 / p) * |deriv r y|) := by
        nlinarith [mul_le_mul_of_nonneg_right hA1 hr1]
      have t4 : 0 ≤ Cb * ε * (jb y ^ (-2 / p) * |deriv (deriv r) y|) := by positivity
      have t5 : 0 ≤ Cb * ε * (jb y ^ (-1 / p) * |deriv r y|) := by positivity
      rw [mul_add] at this
      linarith
    calc jb y ^ γ * (|a y| * |r y| + jb y ^ (-1 / p) * |deriv a y * r y + a y * deriv r y|)
        ≤ jb y ^ γ * (2 * Cb * ε * (|r y| + jb y ^ (-1 / p) * |deriv r y| +
            jb y ^ (-2 / p) * |deriv (deriv r) y|)) := mul_le_mul_of_nonneg_left hb1 hg0.le
      _ = _ := by ring
  · intro y hy
    obtain ⟨hA1, hA2⟩ := hA y
    have hj := c08_aux_one_le_jb y
    have hg0 : 0 < jb y ^ γ := Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ
    rw [hderiv y]
    simp only [Real.norm_eq_abs, hR]
    rw [abs_mul]
    have e1 : |deriv a y * r y + a y * deriv r y| ≤ |deriv a y| * |r y| + |a y| * |deriv r y| := by
      rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    have hr0 := abs_nonneg (r y); have hr1 := abs_nonneg (deriv r y)
    have hr2 := abs_nonneg (deriv (deriv r) y)
    have hj2 : 0 ≤ jb y ^ (2 : ℕ) := by positivity
    have hb1 : |a y| * |r y| + jb y * |deriv a y * r y + a y * deriv r y| ≤
        2 * Cb * ε * (|r y| + jb y * |deriv r y| + jb y ^ (2 : ℕ) * |deriv (deriv r) y|) := by
      have := mul_le_mul_of_nonneg_left e1 (by linarith : (0:ℝ) ≤ jb y)
      have t1 : |a y| * |r y| ≤ Cb * ε * |r y| := mul_le_mul_of_nonneg_right hA1 hr0
      have t2 : jb y * (|deriv a y| * |r y|) ≤ Cb * ε * |r y| := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hA2 hr0
      have t3 : jb y * (|a y| * |deriv r y|) ≤ Cb * ε * (jb y * |deriv r y|) := by
        nlinarith [mul_le_mul_of_nonneg_right hA1 hr1]
      have t4 : 0 ≤ Cb * ε * (jb y ^ (2 : ℕ) * |deriv (deriv r) y|) := by positivity
      have t5 : 0 ≤ Cb * ε * (jb y * |deriv r y|) := by positivity
      rw [mul_add] at this
      linarith
    calc jb y ^ γ * (|a y| * |r y| + jb y * |deriv a y * r y + a y * deriv r y|)
        ≤ jb y ^ γ * (2 * Cb * ε * (|r y| + jb y * |deriv r y| +
            jb y ^ (2 : ℕ) * |deriv (deriv r) y|)) := mul_le_mul_of_nonneg_left hb1 hg0.le
      _ = _ := by ring

/-- Algebraic bound for the `y`-derivative of the kernel. -/
theorem c08_aux_kernel_y_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) {a b d2 t sg : ℝ}
    (ha : |a - 1| ≤ 1 / 4) (hb : |b - 1| ≤ 1 / 4) (ht : t ≠ 0) (hsg : |sg| ≤ 1) :
    |(calpha p * -((d2 * b - a * ((a - b) / t)) / b ^ 2 * (p + 1) * (a / b) ^ (p + 1 - 1)) *
        |t| ^ (1 + p) - calpha p * (1 - (a / b) ^ (p + 1)) * (sg * (1 + p) * |t| ^ (1 + p - 1))) /
        (|t| ^ (1 + p)) ^ 2| ≤ 4 * |d2| / |t| ^ (p + 1) + 12 * |a - b| / |t| ^ (p + 2) := by
  have hp0 : 0 < p := by linarith
  have ha' := abs_le.1 ha; have hb' := abs_le.1 hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨r1, -, -, -⟩ := c08_aux_ratio_bounds p hp0 hp1 ha hb
  set w := |t| with hwdef
  have hw : 0 < w := abs_pos.2 ht
  have hwp : 0 < w ^ p := Real.rpow_pos_of_pos hw p
  have e1 : w ^ (1 + p) = w * w ^ p := by rw [Real.rpow_add hw, Real.rpow_one]
  have e2 : w ^ (p + 1) = w * w ^ p := by rw [add_comm]; exact e1
  have e3 : w ^ (p + 2) = w ^ 2 * w ^ p := by
    rw [Real.rpow_add hw, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
  have e4 : w ^ (1 + p - 1) = w ^ p := by rw [show 1 + p - 1 = p by ring]
  have hca := c08_aux_calpha_bound p hp0 hp1
  have hpi : 1 / π < 1 / 3 := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num)]; linarith [Real.pi_gt_three]
  have hca3 : |calpha p| ≤ 1 / 3 := by linarith
  set q := a / b with hqdef
  have hqpos : 0 < q := div_pos ha0 hb0
  have hqp : q ^ (p + 1 - 1) ≤ 2 := by
    rw [show p + 1 - 1 = p by ring]
    have hq2 : q ≤ 2 := by rw [hqdef, div_le_iff₀ hb0]; linarith
    calc q ^ p ≤ 2 ^ p := Real.rpow_le_rpow hqpos.le hq2 hp0.le
      _ ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
      _ = 2 := Real.rpow_one 2
  have hqp0 : 0 ≤ q ^ (p + 1 - 1) := (Real.rpow_pos_of_pos hqpos _).le
  set Δ := |a - b| with hΔ
  set B2 := |d2| with hB2
  have hq' : |(d2 * b - a * ((a - b) / t)) / b ^ 2| ≤ 3 * (B2 + Δ / w) := by
    have hS2 : 9 / 16 ≤ b ^ 2 := by nlinarith
    rw [abs_div, abs_of_pos (by positivity : 0 < b ^ 2), div_le_iff₀ (by positivity)]
    have : |d2 * b - a * ((a - b) / t)| ≤ B2 * (5 / 4) + (5 / 4) * (Δ / w) := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_of_pos hb0]
        exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      · rw [abs_mul, abs_div, abs_of_pos ha0]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hB0 : 0 ≤ B2 + Δ / w := by positivity
    nlinarith
  set N' := calpha p * -((d2 * b - a * ((a - b) / t)) / b ^ 2 * (p + 1) * q ^ (p + 1 - 1)) with hN'
  set Nv := calpha p * (1 - q ^ (p + 1)) with hNv
  set D' := sg * (1 + p) * w ^ (1 + p - 1) with hD'
  have hN'b : |N'| ≤ 4 * (B2 + Δ / w) := by
    rw [hN', abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < p + 1),
      abs_of_nonneg hqp0]
    calc |calpha p| * (|(d2 * b - a * ((a - b) / t)) / b ^ 2| * (p + 1) * q ^ (p + 1 - 1))
        ≤ (1 / 3) * (3 * (B2 + Δ / w) * 2 * 2) := by
          gcongr
          · linarith
      _ = 4 * (B2 + Δ / w) := by ring
  have hNvb : |Nv| ≤ 4 * Δ := by
    rw [hNv, abs_mul]
    calc |calpha p| * |1 - q ^ (p + 1)| ≤ (1 / 3) * (10 * Δ) :=
          mul_le_mul hca3 r1 (abs_nonneg _) (by norm_num)
      _ ≤ 4 * Δ := by nlinarith [abs_nonneg (a - b)]
  have hD'b : |D'| ≤ 2 * w ^ p := by
    rw [hD', e4, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 + p), abs_of_pos hwp]
    calc |sg| * (1 + p) * w ^ p ≤ 1 * 2 * w ^ p := by gcongr; linarith
      _ = 2 * w ^ p := by ring
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  clear_value N' Nv D' q w Δ B2
  have hww : 0 < w * w ^ p := mul_pos hw hwp
  rw [e1, e2, e3]
  have hVe : (N' * (w * w ^ p) - Nv * D') / (w * w ^ p) ^ 2 =
      N' / (w * w ^ p) - Nv * D' / (w * w ^ p) ^ 2 := by
    rw [sub_div, pow_two, mul_div_mul_right _ _ hww.ne', ← pow_two]
  rw [hVe]
  calc |N' / (w * w ^ p) - Nv * D' / (w * w ^ p) ^ 2|
      ≤ |N'| / (w * w ^ p) + |Nv| * |D'| / (w * w ^ p) ^ 2 := by
        refine (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_div, abs_div, abs_of_pos hww, abs_of_pos (pow_pos hww 2), abs_mul]
    _ ≤ 4 * (B2 + Δ / w) / (w * w ^ p) + 4 * Δ * (2 * w ^ p) / (w * w ^ p) ^ 2 := by
        gcongr
    _ = 4 * B2 / (w * w ^ p) + 12 * Δ / (w ^ 2 * w ^ p) := by
        have hw0 := hw.ne'; have hp0' := hwp.ne'
        field_simp
        ring

/-- The `y`-derivative of the kernel `c_α[1-(φ'(y)/S_φ(y,z))^{p+1}]/|y-z|^{1+p}` for `y ≠ z`:
it exists and is bounded by `4|φ''(y)|/w^{p+1} + 12|φ'(y)-S|/w^{p+2}`, `w = |y-z|`. -/
theorem c08_aux_kernel_hasDerivAt_y (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (h1 : ∀ x, |deriv φ x - 1| ≤ 1 / 4) {y z : ℝ} (h : y ≠ z) :
    ∃ V : ℝ, HasDerivAt (fun y' => calpha p * (1 - (deriv φ y' / c01_secant φ y' z) ^ (p + 1)) /
        |y' - z| ^ (1 + p)) V y ∧
      |V| ≤ 4 * |deriv (deriv φ) y| / |y - z| ^ (p + 1) +
        12 * |deriv φ y - c01_secant φ y z| / |y - z| ^ (p + 2) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (deriv φ) := by
    have : ContDiff ℝ 1 (deriv φ) := hφ.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have hyz : y - z ≠ 0 := sub_ne_zero.2 h
  have hw : 0 < |y - z| := abs_pos.2 hyz
  have hS : c01_secant φ y z = (φ y - φ z) / (y - z) := by
    unfold c01_secant; simp only [h, ↓reduceIte]
  obtain ⟨ξ, -, hsξ⟩ := c08_aux_secant_mvt hd h
  have hS1 : |c01_secant φ y z - 1| ≤ 1 / 4 := by rw [hsξ]; exact h1 ξ
  have hS0 : 0 < c01_secant φ y z := by linarith [(abs_le.1 hS1).1]
  have hu0 : 0 < deriv φ y := by linarith [(abs_le.1 (h1 y)).1]
  have hSd : HasDerivAt (fun y' => (φ y' - φ z) / (y' - z))
      ((deriv φ y - c01_secant φ y z) / (y - z)) y := by
    have := ((hd y).hasDerivAt.sub_const (φ z)).div ((hasDerivAt_id y).sub_const z) hyz
    have e : (deriv φ y - c01_secant φ y z) / (y - z) =
        (deriv φ y * (id y - z) - (φ y - φ z) * 1) / (id y - z) ^ 2 := by
      rw [hS]; simp only [id]; field_simp
    rw [e]; exact this
  have hev : (fun y' => c01_secant φ y' z) =ᶠ[nhds y] fun y' => (φ y' - φ z) / (y' - z) := by
    filter_upwards [isOpen_ne.mem_nhds h] with y' hy'
    unfold c01_secant; simp only [show y' ≠ z from hy', ↓reduceIte]
  have hSd' : HasDerivAt (fun y' => c01_secant φ y' z)
      ((deriv φ y - c01_secant φ y z) / (y - z)) y := hSd.congr_of_eventuallyEq hev
  have hq := (hd1 y).hasDerivAt.div hSd' hS0.ne'
  have hqpos : 0 < deriv φ y / c01_secant φ y z := div_pos hu0 hS0
  have hr := hq.rpow_const (p := p + 1) (Or.inl hqpos.ne')
  have hN := (hr.const_sub 1).const_mul (calpha p)
  have hA : HasDerivAt (fun y' => |y' - z|) (SignType.sign (y - z) : ℝ) y := by
    refine ((hasDerivAt_abs hyz).comp y ((hasDerivAt_id y).sub_const z)).congr_deriv ?_
    simp
  have hD := hA.rpow_const (p := 1 + p) (Or.inl hw.ne')
  have hV := hN.div hD (Real.rpow_pos_of_pos hw _).ne'
  refine ⟨_, hV, ?_⟩
  have hsg : |(SignType.sign (y - z) : ℝ)| ≤ 1 := by
    rcases lt_trichotomy (y - z) 0 with hl | hl | hl
    · simp [sign_neg hl]
    · exact absurd hl hyz
    · simp [sign_pos hl]
  exact c08_aux_kernel_y_bound p hp hp1 (h1 y) hS1 hyz hsg


/-- Blueprint: lem:c08_R2_kernel_far.  Kernel bounds in the far region `|y-z| ≥ ⟨y⟩/8`. -/
theorem c08_R2_kernel_far (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      ∀ y z : ℝ, jb y / 8 ≤ |y - z| →
        |R_eps_kernel p ε y z| ≤
          C * |c_eps p ε| * (jb y ^ (-p - 1) / |y - z| ^ (p + 1) + jb z ^ (-p) / |y - z| ^ (p + 2)) ∧
        |deriv (fun y' => R_eps_kernel p ε y' z) y| ≤
          C * |c_eps p ε| * (jb y ^ (-p - 2) / |y - z| ^ (p + 1) + jb z ^ (-p) / |y - z| ^ (p + 3)) := by
  obtain ⟨c1, hc1, hc1', C, hC, hdat⟩ := c08_aux_phi_kernel_data p hp hp1
  obtain ⟨c0, hc0, hc0', hj, -⟩ := c08_phi_bounds p hp hp1
  obtain ⟨C0, hC0, h0⟩ := hj 0
  obtain ⟨C1, hC1, h1b⟩ := hj 1
  have hp0 : 0 < p := by linarith
  set A := C1 + 8 * C0 with hA
  have hA0 : 0 < A := by positivity
  refine ⟨min c1 c0, lt_min hc1 hc0, 4 * C + 96 * A + 12 * C0 + 4, by positivity,
    fun ε hε0 hε y z hyz => ?_⟩
  have hcε := c08_aux_c_eps_bound p ε hp hp1 hε0
  have hc : |c_eps p ε| ≤ c1 := hcε.2.trans (hε.trans (min_le_left _ _))
  have hc' : |c_eps p ε| ≤ c0 := hcε.2.trans (hε.trans (min_le_right _ _))
  obtain ⟨hφ, -, h1, h2, -⟩ := hdat (c_eps p ε) hc
  set c := c_eps p ε with hcdef
  set φ := c08_phi p c with hφdef
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hd : Differentiable ℝ φ := hφ2.differentiable (by norm_num)
  have hjy := c08_aux_jb_pos y
  have hjz := c08_aux_jb_pos z
  have hw : 0 < |y - z| := lt_of_lt_of_le (by positivity) hyz
  have h : y ≠ z := fun e => by rw [e, sub_self, abs_zero] at hw; exact lt_irrefl _ hw
  set w := |y - z| with hwdef
  have hw8 : ∀ X : ℝ, 0 ≤ X → X / w ≤ 8 * (X / jb y) := by
    intro X hX
    rw [div_le_iff₀ hw]
    have : X / jb y * jb y = X := by field_simp
    nlinarith [div_nonneg hX hjy.le]
  have hjb1 : jb y ^ (-p) / jb y = jb y ^ (-p - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hjy]; ring_nf
  have hjb2 : jb y ^ (-p - 1) / jb y = jb y ^ (-p - 2) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hjy]; ring_nf
  have ew2 : w ^ (p + 2) = w ^ (p + 1) * w := by
    rw [show p + 2 = (p + 1) + 1 by ring, Real.rpow_add_one hw.ne']
  have ew3 : w ^ (p + 3) = w ^ (p + 2) * w := by
    rw [show p + 3 = (p + 2) + 1 by ring, Real.rpow_add_one hw.ne']
  have hwp1 : 0 < w ^ (p + 1) := Real.rpow_pos_of_pos hw _
  have hwp2 : 0 < w ^ (p + 2) := Real.rpow_pos_of_pos hw _
  -- the increment `Δ = |φ'(y) - S|`
  have hS : c01_secant φ y z = (φ y - φ z) / (y - z) := by
    unfold c01_secant; simp only [h, ↓reduceIte]
  have hg0 : ∀ x, |φ x - x| ≤ C0 * |c| * jb x ^ (-p) := fun x => by
    have := h0 c hc' x; simpa using this
  have hg1 : |deriv φ y - 1| ≤ C1 * |c| * jb y ^ (-p - 1) := by
    have := h1b c hc' y
    rw [(c08_aux_iteratedDeriv_sub_id hφ2).1] at this
    simpa using this
  have hΔ : |deriv φ y - c01_secant φ y z| ≤ |c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w)) := by
    have e : deriv φ y - c01_secant φ y z =
        (deriv φ y - 1) - ((φ y - y) - (φ z - z)) / (y - z) := by
      rw [hS]; field_simp [sub_ne_zero.2 h]; ring
    rw [e]
    have hyz0 : y - z ≠ 0 := sub_ne_zero.2 h
    have t1 : |((φ y - y) - (φ z - z)) / (y - z)| ≤
        C0 * |c| * jb y ^ (-p) / w + C0 * |c| * jb z ^ (-p) / w := by
      rw [abs_div, ← hwdef, ← add_div]
      apply div_le_div_of_nonneg_right _ hw.le
      exact (abs_sub _ _).trans (add_le_add (hg0 y) (hg0 z))
    have t2 : C0 * |c| * jb y ^ (-p) / w ≤ 8 * C0 * |c| * jb y ^ (-p - 1) := by
      have := hw8 (C0 * |c| * jb y ^ (-p)) (by positivity)
      rw [show C0 * |c| * jb y ^ (-p) / jb y = C0 * |c| * (jb y ^ (-p) / jb y) by ring,
        hjb1] at this
      linarith
    calc |deriv φ y - 1 - ((φ y - y) - (φ z - z)) / (y - z)|
        ≤ |deriv φ y - 1| + |((φ y - y) - (φ z - z)) / (y - z)| := abs_sub _ _
      _ ≤ C1 * |c| * jb y ^ (-p - 1) + (8 * C0 * |c| * jb y ^ (-p - 1) +
            C0 * |c| * jb z ^ (-p) / w) := by linarith
      _ = _ := by rw [hA]; ring
  obtain ⟨ξ, -, hsξ⟩ := c08_aux_secant_mvt hd h
  have hS1 : |c01_secant φ y z - 1| ≤ 1 / 4 := by rw [hsξ]; exact h1 ξ
  obtain ⟨r1, -, -, -⟩ := c08_aux_ratio_bounds p hp0 hp1 (h1 y) hS1
  have hca := c08_aux_calpha_bound p hp0 hp1
  have hpi : 1 / π < 1 / 3 := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num)]; linarith [Real.pi_gt_three]
  have hca3 : |calpha p| ≤ 1 / 3 := by linarith
  have hc0 : 0 ≤ |c| := abs_nonneg _
  have hjz0 : 0 ≤ jb z ^ (-p) := (Real.rpow_pos_of_pos hjz _).le
  have hjy1 : 0 ≤ jb y ^ (-p - 1) := (Real.rpow_pos_of_pos hjy _).le
  have hjy2 : 0 ≤ jb y ^ (-p - 2) := (Real.rpow_pos_of_pos hjy _).le
  set Kc := 4 * C + 96 * A + 12 * C0 + 4 with hKc
  constructor
  · show |calpha p * (1 - (deriv φ y / c01_secant φ y z) ^ (p + 1)) / |y - z| ^ (1 + p)| ≤ _
    rw [← hwdef, abs_div, abs_of_pos (Real.rpow_pos_of_pos hw _), abs_mul, add_comm 1 p]
    have hk : |calpha p| * |1 - (deriv φ y / c01_secant φ y z) ^ (p + 1)| ≤
        4 * (|c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w))) := by
      calc _ ≤ (1 / 3) * (10 * |deriv φ y - c01_secant φ y z|) :=
            mul_le_mul hca3 r1 (abs_nonneg _) (by norm_num)
        _ ≤ (1 / 3) * (10 * (|c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w)))) := by gcongr
        _ ≤ _ := by
          have : 0 ≤ |c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w)) := by positivity
          linarith
    calc |calpha p| * |1 - (deriv φ y / c01_secant φ y z) ^ (p + 1)| / w ^ (p + 1)
        ≤ 4 * (|c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w))) / w ^ (p + 1) :=
          div_le_div_of_nonneg_right hk hwp1.le
      _ = |c| * (4 * A * (jb y ^ (-p - 1) / w ^ (p + 1)) + 4 * C0 * (jb z ^ (-p) / w ^ (p + 2))) := by
          rw [ew2]; field_simp
      _ ≤ |c| * (Kc * (jb y ^ (-p - 1) / w ^ (p + 1)) + Kc * (jb z ^ (-p) / w ^ (p + 2))) := by
          gcongr <;> linarith
      _ = Kc * |c| * (jb y ^ (-p - 1) / w ^ (p + 1) + jb z ^ (-p) / w ^ (p + 2)) := by ring
  · obtain ⟨V, hV, hVb⟩ := c08_aux_kernel_hasDerivAt_y p hp hp1 hφ2 h1 h
    have hfun : (fun y' => R_eps_kernel p ε y' z) = fun y' =>
        calpha p * (1 - (deriv φ y' / c01_secant φ y' z) ^ (p + 1)) / |y' - z| ^ (1 + p) := rfl
    rw [hfun, hV.deriv]
    refine hVb.trans ?_
    rw [← hwdef]
    have hd2 := h2 y
    have t1 : 4 * |deriv (deriv φ) y| / w ^ (p + 1) ≤ 4 * C * |c| * (jb y ^ (-p - 2) / w ^ (p + 1)) := by
      rw [mul_div_assoc', show 4 * C * |c| * jb y ^ (-p - 2) = 4 * (C * |c| * jb y ^ (-p - 2)) by ring]
      exact div_le_div_of_nonneg_right (by linarith) hwp1.le
    have t2 : 12 * |deriv φ y - c01_secant φ y z| / w ^ (p + 2) ≤
        12 * (|c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w))) / w ^ (p + 2) :=
      div_le_div_of_nonneg_right (by linarith) hwp2.le
    have t3 : jb y ^ (-p - 1) / w ^ (p + 2) ≤ 8 * (jb y ^ (-p - 2) / w ^ (p + 1)) := by
      have h8 := hw8 (jb y ^ (-p - 1)) hjy1
      rw [hjb2] at h8
      rw [ew2, show w ^ (p + 1) * w = w * w ^ (p + 1) by ring, ← div_div]
      calc jb y ^ (-p - 1) / w / w ^ (p + 1) ≤ 8 * jb y ^ (-p - 2) / w ^ (p + 1) :=
            div_le_div_of_nonneg_right h8 hwp1.le
        _ = _ := by ring
    have e3 : 12 * (|c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w))) / w ^ (p + 2) =
        |c| * (12 * A * (jb y ^ (-p - 1) / w ^ (p + 2)) + 12 * C0 * (jb z ^ (-p) / w ^ (p + 3))) := by
      rw [ew3]; field_simp
    have hq1 : 0 ≤ jb y ^ (-p - 2) / w ^ (p + 1) := by positivity
    have hq2 : 0 ≤ jb z ^ (-p) / w ^ (p + 3) := by positivity
    have hq3 : 0 ≤ jb y ^ (-p - 1) / w ^ (p + 2) := by positivity
    calc 4 * |deriv (deriv φ) y| / w ^ (p + 1) + 12 * |deriv φ y - c01_secant φ y z| / w ^ (p + 2)
        ≤ 4 * C * |c| * (jb y ^ (-p - 2) / w ^ (p + 1)) +
          12 * (|c| * (A * jb y ^ (-p - 1) + C0 * (jb z ^ (-p) / w))) / w ^ (p + 2) :=
          add_le_add t1 t2
      _ = 4 * C * |c| * (jb y ^ (-p - 2) / w ^ (p + 1)) +
          |c| * (12 * A * (jb y ^ (-p - 1) / w ^ (p + 2)) + 12 * C0 * (jb z ^ (-p) / w ^ (p + 3))) := by
          rw [e3]
      _ ≤ 4 * C * |c| * (jb y ^ (-p - 2) / w ^ (p + 1)) +
          |c| * (12 * A * (8 * (jb y ^ (-p - 2) / w ^ (p + 1))) +
            12 * C0 * (jb z ^ (-p) / w ^ (p + 3))) := by gcongr
      _ = |c| * ((4 * C + 96 * A) * (jb y ^ (-p - 2) / w ^ (p + 1)) +
            12 * C0 * (jb z ^ (-p) / w ^ (p + 3))) := by ring
      _ ≤ |c| * (Kc * (jb y ^ (-p - 2) / w ^ (p + 1)) + Kc * (jb z ^ (-p) / w ^ (p + 3))) := by
          gcongr <;> linarith
      _ = Kc * |c| * (jb y ^ (-p - 2) / w ^ (p + 1) + jb z ^ (-p) / w ^ (p + 3)) := by ring


theorem c08_aux_jb_sub_le (a b : ℝ) : jb (a - b) ≤ 2 * jb a * jb b := by
  unfold jb
  rw [show 2 * √(1 + a ^ 2) * √(1 + b ^ 2) = √(4 * ((1 + a ^ 2) * (1 + b ^ 2))) by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by positivity),
      show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; ring]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a + b), sq_nonneg (a * b)])

theorem c08_aux_ae_ne (y : ℝ) : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ y := by
  rw [ae_iff]; simp

theorem c08_aux_domS_integrable {p s : ℝ} (hp : 0 < p) (hp1 : p < 1) (hsp : s < p) :
    Integrable (fun u : ℝ => {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) u +
      4 * jb u ^ (-1 - p + s)) := by
  obtain ⟨hbi, -⟩ := c08_aux_ball_rpow hp hp1 0 one_pos
  have h1i : Integrable ({v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p))) := by
    have : IntegrableOn (fun v : ℝ => |v| ^ (-p)) {v : ℝ | |v| ≤ 1} := by simpa using hbi
    exact this.integrable_indicator (measurableSet_le (by fun_prop) measurable_const)
  have h2i := c08_aux_jb_rpow_integrable (1 + p - s) (by linarith)
  rw [show -(1 + p - s) = -1 - p + s by ring] at h2i
  exact h1i.add (h2i.const_mul 4)

theorem c08_aux_domS_le {p s : ℝ} (hp : 0 < p) (hp1 : p < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {u : ℝ} (hu : u ≠ 0) (y : ℝ) :
    min (|u| ^ (-p)) (|u| ^ (-1 - p)) * jb (y - u) ^ s ≤
      4 * jb y * ({v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) u + 4 * jb u ^ (-1 - p + s)) := by
  have hu' : 0 < |u| := abs_pos.2 hu
  have hm := c08_aux_min_dominate hp hp1 hu'
  rw [c08_aux_min_rpow hu'] at hm
  have hjy := c08_aux_one_le_jb y
  have hju := c08_aux_one_le_jb u
  have hw : jb (y - u) ^ s ≤ 2 * jb y * jb u ^ s := by
    calc jb (y - u) ^ s ≤ (2 * jb y * jb u) ^ s :=
          Real.rpow_le_rpow (c08_aux_jb_pos _).le (c08_aux_jb_sub_le y u) hs0
      _ = (2 * jb y) ^ s * jb u ^ s := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (2 * jb y) * jb u ^ s := by
          gcongr
          calc (2 * jb y) ^ s ≤ (2 * jb y) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hs1
            _ = 2 * jb y := Real.rpow_one _
  set I := {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) u with hIdef
  have hI0 : 0 ≤ I := Set.indicator_nonneg (fun v _ => Real.rpow_nonneg (abs_nonneg v) _) u
  have hIs : I * jb u ^ s ≤ 2 * I := by
    by_cases h : |u| ≤ 1
    · have : jb u ^ s ≤ 2 := by
        calc jb u ^ s ≤ jb u ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hju hs1
          _ ≤ 2 := by rw [Real.rpow_one]; linarith [c08_aux_jb_le_one_add u]
      nlinarith
    · have : I = 0 := by
        rw [hIdef]; exact Set.indicator_of_notMem (by simpa using h) _
      rw [this]; simp
  have hJ : jb u ^ (-1 - p) * jb u ^ s = jb u ^ (-1 - p + s) :=
    (Real.rpow_add (c08_aux_jb_pos u) _ _).symm
  have hm0 : 0 ≤ min (|u| ^ (-p)) (|u| ^ (-1 - p)) :=
    le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hjus : 0 ≤ jb u ^ s := (Real.rpow_pos_of_pos (c08_aux_jb_pos u) s).le
  have hJp := Real.rpow_pos_of_pos (c08_aux_jb_pos u) (-1 - p + s)
  calc min (|u| ^ (-p)) (|u| ^ (-1 - p)) * jb (y - u) ^ s
      ≤ min (|u| ^ (-p)) (|u| ^ (-1 - p)) * (2 * jb y * jb u ^ s) := by gcongr
    _ = 2 * jb y * (min (|u| ^ (-p)) (|u| ^ (-1 - p)) * jb u ^ s) := by ring
    _ ≤ 2 * jb y * ((I + 4 * jb u ^ (-1 - p)) * jb u ^ s) := by gcongr
    _ = 2 * jb y * (I * jb u ^ s + 4 * jb u ^ (-1 - p + s)) := by rw [← hJ]; ring
    _ ≤ 2 * jb y * (2 * I + 4 * jb u ^ (-1 - p + s)) := by gcongr
    _ ≤ 4 * jb y * (I + 4 * jb u ^ (-1 - p + s)) := by nlinarith

theorem c08_aux_secant_measurable {f : ℝ → ℝ} (hf : Continuous f) (y : ℝ) :
    Measurable (fun z => c01_secant f y z) := by
  unfold c01_secant
  exact Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const
    ((measurable_const.sub hf.measurable).div (measurable_const.sub measurable_id))

theorem c08_aux_kernel_md (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ c1 →
      ContDiff ℝ 2 (phi_eps p ε) ∧ (∀ x, |deriv (phi_eps p ε) x - 1| ≤ 1 / 4) ∧
      (∀ y, Measurable (fun z => R_eps_kernel p ε y z)) ∧
      (∀ y, AEStronglyMeasurable (fun z => deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0)
        volume) ∧
      (∀ y z, y ≠ z → HasDerivAt (fun s => R_eps_kernel p ε (y + s) (z + s))
          (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0) 0) := by
  obtain ⟨c1, hc1, -, C, -, hdat⟩ := c08_aux_phi_kernel_data p hp hp1
  refine ⟨c1, hc1, fun ε hε0 hε => ?_⟩
  have hc : |c_eps p ε| ≤ c1 := (c08_aux_c_eps_bound p ε hp hp1 hε0).2.trans hε
  obtain ⟨hφ, -, h1, -, -⟩ := hdat (c_eps p ε) hc
  have hφ2 : ContDiff ℝ 2 (phi_eps p ε) := hφ.of_le (by norm_cast)
  replace h1 : ∀ x, |deriv (phi_eps p ε) x - 1| ≤ 1 / 4 := h1
  set φ := phi_eps p ε with hφdef
  have hd : Differentiable ℝ φ := hφ2.differentiable (by norm_num)
  have hd1c : Continuous (deriv φ) := hφ2.continuous_deriv (by norm_num)
  have hpos : ∀ x, 0 < deriv φ x := fun x => by linarith [(abs_le.1 (h1 x)).1]
  have hsec : ∀ y z, y ≠ z → 0 < c01_secant φ y z := by
    intro y z h
    obtain ⟨ξ, -, e⟩ := c08_aux_secant_mvt hd h
    rw [e]; exact hpos ξ
  have hHD := fun y z (h : y ≠ z) => c08_aux_kernel_hasDerivAt p hφ2 hpos h (hsec y z h)
  refine ⟨hφ2, h1, fun y => ?_, fun y => ?_, fun y z h => ?_⟩
  · have hS := c08_aux_secant_measurable hd.continuous y
    unfold R_eps_kernel
    fun_prop
  · have hS := c08_aux_secant_measurable hd.continuous y
    have hS' := c08_aux_secant_measurable hd1c y
    have hm : Measurable (fun z => -(calpha p) * (p + 1) * |y - z| ^ (-1 - p) *
        (deriv φ y / c01_secant φ y z) ^ (p + 1) *
        (deriv (deriv φ) y / deriv φ y - c01_secant (deriv φ) y z / c01_secant φ y z)) := by
      fun_prop
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [c08_aux_ae_ne y] with z hz
    exact ((hHD y z (Ne.symm hz)).deriv).symm
  · exact (hHD y z h).differentiableAt.hasDerivAt

/-- A.e. bound for `r''`, `r ∈ X_γ`: `|r''| ≤ ‖r‖⟨y⟩^{-γ+2/p}`. -/
theorem c08_aux_X_ae_bound2 {p γ : ℝ} (hp : 0 < p) {r : ℝ → ℝ} (hr : r ∈ X_gamma p γ) :
    ∀ᵐ y ∂(volume : Measure ℝ), |deriv (deriv r) y| ≤ xNorm p γ r * jb y ^ (-γ + 2 / p) := by
  have hfin := hr.2
  unfold X_gamma_norm at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have hx : xNorm p γ r = _ := ENNReal.toReal_add h1.ne h2.ne
  set E1 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv r) y‖))) (volume.restrict (Ici 0))
  set E2 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0))
  have hN1 : E1.toReal ≤ xNorm p γ r := by rw [hx]; linarith [ENNReal.toReal_nonneg (a := E2)]
  have hN2 : E2.toReal ≤ xNorm p γ r := by rw [hx]; linarith [ENNReal.toReal_nonneg (a := E1)]
  have hN0 : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg
  apply c08_aux_ae_of_halflines
  · filter_upwards [c08_aux_ae_le_essSup_toReal h1] with y hy
    have hj := c08_aux_jb_pos y
    have hg := Real.rpow_pos_of_pos hj γ
    have hw := Real.rpow_pos_of_pos hj (-1 / p)
    have hw2 := Real.rpow_pos_of_pos hj (-2 / p)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at hy
    have a0 := abs_nonneg (r y); have a1 := abs_nonneg (deriv r y)
    have a2 := abs_nonneg (deriv (deriv r) y)
    have : jb y ^ (γ - 2 / p) * |deriv (deriv r) y| ≤ xNorm p γ r := by
      rw [sub_eq_add_neg, Real.rpow_add hj, show -(2 / p) = -2 / p by ring]
      nlinarith [mul_nonneg hg.le a0, mul_nonneg hg.le (mul_nonneg hw.le a1)]
    have := c08_aux_div_weight this
    rwa [show -(γ - 2 / p) = -γ + 2 / p by ring] at this
  · filter_upwards [c08_aux_ae_le_essSup_toReal h2] with y hy
    have hj := c08_aux_jb_pos y
    have hj1 := c08_aux_one_le_jb y
    have hg := Real.rpow_pos_of_pos hj γ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at hy
    have a0 := abs_nonneg (r y); have a1 := abs_nonneg (deriv r y)
    have a2 := abs_nonneg (deriv (deriv r) y)
    have h3 : jb y ^ (γ + 2) * |deriv (deriv r) y| ≤ xNorm p γ r := by
      rw [Real.rpow_add hj, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      nlinarith [mul_nonneg hg.le a0, mul_nonneg hg.le (mul_nonneg hj.le a1)]
    have h4 := c08_aux_div_weight h3
    have hp' : 0 < 2 / p := by positivity
    have h5 : jb y ^ (-(γ + 2)) ≤ jb y ^ (-γ + 2 / p) :=
      Real.rpow_le_rpow_of_exponent_le hj1 (by linarith)
    exact h4.trans (mul_le_mul_of_nonneg_left h5 hN0)


theorem c08_aux_lip_of_ae_deriv {f : ℝ → ℝ} (hf : LocallyLipschitz f) {a b K : ℝ}
    (h : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIcc a b → |deriv f t| ≤ K) :
    |f a - f b| ≤ K * |a - b| := by
  have e := c08_aux_ibp_interval hf (g := fun _ => (1:ℝ)) contDiff_const b a
  simp only [one_mul, deriv_const', zero_mul, intervalIntegral.integral_zero, sub_zero] at e
  rw [← e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := b) (b := a) (C := K)
    (f := deriv f) (by
      filter_upwards [h] with t ht htI
      exact ht (by rw [uIcc_comm]; exact uIoc_subset_uIcc htI))
  simpa using this

theorem c08_aux_tail {G : ℝ → ℝ} (hG : Integrable G) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, ∫ v, {v : ℝ | T < |v|}.indicator G v ≤ δ := by
  have hlim : Tendsto (fun T : ℝ => ∫ v, {v : ℝ | T < |v|}.indicator G v) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun T : ℝ => {v : ℝ | T < |v|}.indicator G) (f := fun _ => (0:ℝ))
      (fun v => ‖G v‖)
      (Eventually.of_forall fun T => hG.aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const continuous_abs.measurable))
      (Eventually.of_forall fun T => Eventually.of_forall fun v => norm_indicator_le_norm_self _ _)
      hG.norm
      (Eventually.of_forall fun v => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop |v|] with T hT
        exact (Set.indicator_of_notMem (by simp only [mem_ofPred_eq, not_lt]; exact hT) _).symm)
    simpa using this
  exact ((tendsto_order.1 hlim).2 δ hδ).exists.imp fun T hT => hT.le

/-- Differentiation under the integral for `y ↦ ∫ K(y,z) r'(z) dz` (abstract kernel version, used
for lem:c08_R2_derivative): `K(y,·)` measurable, `(∂_y+∂_z)K` exists off the diagonal, and
`|K| + |(∂_y+∂_z)K| ≤ C min(|y-z|^{-p},|y-z|^{-1-p})`; `r'` bounded and locally Lipschitz with
`|r''| ≤ N⟨z⟩^s` a.e.; `G` an integrable majorant of the weighted kernel bound. -/
theorem c08_aux_gen_hasDerivAt {p s C N : ℝ} {K : ℝ → ℝ → ℝ} {r G : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hN0 : 0 ≤ N)
    (hKm : ∀ y, Measurable (K y))
    (hHD : ∀ y z, y ≠ z → HasDerivAt (fun t => K (y + t) (z + t))
      (deriv (fun t => K (y + t) (z + t)) 0) 0)
    (hglob : ∀ y z, y ≠ z → |K y z| + |deriv (fun t => K (y + t) (z + t)) 0| ≤
      C * min (|y - z| ^ (-p)) (|y - z| ^ (-1 - p)))
    (hr'c : Continuous (deriv r)) (hr'L : LocallyLipschitz (deriv r))
    (hr'b : ∀ z, |deriv r z| ≤ N) (hr'' : ∀ᵐ z ∂(volume : Measure ℝ), |deriv (deriv r) z| ≤ N * jb z ^ s)
    (hGi : Integrable G) (hG0 : ∀ u, 0 ≤ G u)
    (hGle : ∀ u, u ≠ 0 → ∀ y, min (|u| ^ (-p)) (|u| ^ (-1 - p)) * jb (y - u) ^ s ≤ 4 * jb y * G u)
    (hKri : ∀ x, Integrable (fun z => K x z * deriv r z))
    (hHm : ∀ y, AEStronglyMeasurable (fun z => deriv (fun t => K (y + t) (z + t)) 0 * deriv r z +
        K y z * deriv (deriv r) z) volume)
    (x0 : ℝ) :
    HasDerivAt (fun y => ∫ z, K y z * deriv r z)
      (∫ z, (deriv (fun t => K (x0 + t) (z + t)) 0 * deriv r z + K x0 z * deriv (deriv r) z)) x0 := by
  have hC : 0 ≤ C := by
    have := hglob 1 0 one_ne_zero
    have h2 : 0 < min (|(1:ℝ) - 0| ^ (-p)) (|(1:ℝ) - 0| ^ (-1 - p)) := by simp
    by_contra hc
    replace hc := lt_of_not_ge hc
    have : C * min (|(1:ℝ) - 0| ^ (-p)) (|(1:ℝ) - 0| ^ (-1 - p)) < 0 := mul_neg_of_neg_of_pos hc h2
    linarith [abs_nonneg (K 1 0), abs_nonneg (deriv (fun t => K (1 + t) (0 + t)) 0)]
  have hdiffae := (volume.measurePreserving_sub_left x0).quasiMeasurePreserving.ae
    (c08_aux_ae_differentiable hr'L)
  -- the diagonal derivative of `x ↦ K(x, x-u)`
  have hkd : ∀ u, u ≠ 0 → ∀ ξ, HasDerivAt (fun x => K x (x - u))
      (deriv (fun t => K (ξ + t) (ξ - u + t)) 0) ξ := by
    intro u hu ξ
    have h0 := hHD ξ (ξ - u) (by intro h; apply hu; linarith)
    have h1 := (show HasDerivAt (fun t => K (ξ + t) (ξ - u + t))
      (deriv (fun t => K (ξ + t) (ξ - u + t)) 0) (ξ - ξ) by
        rw [sub_self]; exact h0).comp_sub_const ξ ξ
    convert h1 using 1
    funext x
    rw [show ξ + (x - ξ) = x by ring, show ξ - u + (x - ξ) = x - u by ring]
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume) (x₀ := x0)
    (F := fun x u => K x (x - u) * deriv r (x - u))
    (F' := fun u => deriv (fun t => K (x0 + t) (x0 - u + t)) 0 * deriv r (x0 - u) +
      K x0 (x0 - u) * deriv (deriv r) (x0 - u))
    (bound := fun u => 12 * C * N * jb x0 * G u)
    (Metric.ball_mem_nhds x0 one_pos)
    (Eventually.of_forall fun x =>
      (((hKm x).comp (measurable_const.sub measurable_id)).mul
        (hr'c.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    ((hKri x0).comp_sub_left x0)
    ((hHm x0).comp_measurePreserving (volume.measurePreserving_sub_left x0))
    ?_ (hGi.const_mul _) ?_
  · have e1 : (fun x => ∫ u, K x (x - u) * deriv r (x - u)) = fun y => ∫ z, K y z * deriv r z := by
      funext x
      exact integral_sub_left_eq_self (fun z => K x z * deriv r z) volume x
    have e2 := integral_sub_left_eq_self (fun z =>
      deriv (fun t => K (x0 + t) (z + t)) 0 * deriv r z + K x0 z * deriv (deriv r) z) volume x0
    rw [← e1, ← e2]
    exact key.2
  · -- Lipschitz bound
    filter_upwards [c08_aux_ae_ne 0] with u hu
    have hb0 : 0 ≤ 12 * C * N * jb x0 * G u := by
      have := c08_aux_jb_pos x0; have := hG0 u; positivity
    refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg hb0]
    rw [Metric.mem_ball, Real.dist_eq] at hx hx'
    have hm0 : 0 ≤ min (|u| ^ (-p)) (|u| ^ (-1 - p)) :=
      le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    set m := min (|u| ^ (-p)) (|u| ^ (-1 - p)) with hm
    have hkb : ∀ ξ, |K ξ (ξ - u)| + |deriv (fun t => K (ξ + t) (ξ - u + t)) 0| ≤ C * m := by
      intro ξ
      have := hglob ξ (ξ - u) (by intro h; apply hu; linarith)
      rwa [sub_sub_cancel] at this
    have hk : |K x (x - u) - K x' (x' - u)| ≤ C * m * |x - x'| := by
      refine c08_aux_mvt_bound (fun ξ _ => (hkd u hu ξ).differentiableAt) (fun ξ _ => ?_)
      rw [(hkd u hu ξ).deriv]
      linarith [hkb ξ, abs_nonneg (K ξ (ξ - u))]
    have hrl : |deriv r (x - u) - deriv r (x' - u)| ≤ (2 * N * jb (x0 - u) ^ s) * |x - x'| := by
      have := c08_aux_lip_of_ae_deriv hr'L (a := x - u) (b := x' - u)
        (K := 2 * N * jb (x0 - u) ^ s) (by
          filter_upwards [hr''] with t ht htI
          refine ht.trans ?_
          have hti : |t - (x0 - u)| ≤ 1 := by
            have ha1 := abs_lt.1 hx; have ha2 := abs_lt.1 hx'
            rcases le_total (x - u) (x' - u) with h | h
            · rw [uIcc_of_le h] at htI
              rw [abs_le]; constructor <;> linarith [htI.1, htI.2]
            · rw [uIcc_of_ge h] at htI
              rw [abs_le]; constructor <;> linarith [htI.1, htI.2]
          have hjt : jb t ≤ 2 * jb (x0 - u) := by
            have := abs_le.1 (c08_aux_jb_lip t (x0 - u))
            linarith [c08_aux_one_le_jb (x0 - u)]
          have hj0 := c08_aux_one_le_jb (x0 - u)
          calc N * jb t ^ s ≤ N * (2 * jb (x0 - u)) ^ s := by
                gcongr; exact (c08_aux_jb_pos t).le
            _ = N * (2 ^ s * jb (x0 - u) ^ s) := by rw [Real.mul_rpow (by norm_num) (by linarith)]
            _ ≤ N * (2 * jb (x0 - u) ^ s) := by
                gcongr
                calc (2:ℝ) ^ s ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
                  _ = 2 := Real.rpow_one 2
            _ = 2 * N * jb (x0 - u) ^ s := by ring)
      rwa [show x - u - (x' - u) = x - x' by ring] at this
    have hGu := hGle u hu x0
    have hjs := Real.one_le_rpow (c08_aux_one_le_jb (x0 - u)) hs0
    have hk' : |K x' (x' - u)| ≤ C * m := by
      linarith [hkb x', abs_nonneg (deriv (fun t => K (x' + t) (x' - u + t)) 0)]
    have hxx := abs_nonneg (x - x')
    calc |K x (x - u) * deriv r (x - u) - K x' (x' - u) * deriv r (x' - u)|
        = |(K x (x - u) - K x' (x' - u)) * deriv r (x - u) +
            K x' (x' - u) * (deriv r (x - u) - deriv r (x' - u))| := by ring_nf
      _ ≤ |K x (x - u) - K x' (x' - u)| * |deriv r (x - u)| +
            |K x' (x' - u)| * |deriv r (x - u) - deriv r (x' - u)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (C * m * |x - x'|) * N + (C * m) * ((2 * N * jb (x0 - u) ^ s) * |x - x'|) := by
          gcongr
          exact hr'b _
      _ = C * N * |x - x'| * (m * (1 + 2 * jb (x0 - u) ^ s)) := by ring
      _ ≤ C * N * |x - x'| * (m * (3 * jb (x0 - u) ^ s)) := by gcongr; linarith
      _ = 3 * C * N * |x - x'| * (m * jb (x0 - u) ^ s) := by ring
      _ ≤ 3 * C * N * |x - x'| * (4 * jb x0 * G u) := by gcongr
      _ = 12 * C * N * jb x0 * G u * |x - x'| := by ring
  · -- derivative for a.e. `u`
    filter_upwards [c08_aux_ae_ne 0, hdiffae] with u hu hdu
    exact (hkd u hu x0).mul (hdu.hasDerivAt.comp_sub_const x0 u)

/-- Abstract-kernel version of lem:c08_R2_derivative (all five conclusions). -/
theorem c08_aux_gen_R2 {p s C N : ℝ} {K : ℝ → ℝ → ℝ} {r G : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hN0 : 0 ≤ N)
    (hKm : ∀ y, Measurable (K y))
    (hDm : ∀ y, AEStronglyMeasurable (fun z => deriv (fun t => K (y + t) (z + t)) 0) volume)
    (hHD : ∀ y z, y ≠ z → HasDerivAt (fun t => K (y + t) (z + t))
      (deriv (fun t => K (y + t) (z + t)) 0) 0)
    (hglob : ∀ y z, y ≠ z → |K y z| + |deriv (fun t => K (y + t) (z + t)) 0| ≤
      C * min (|y - z| ^ (-p)) (|y - z| ^ (-1 - p)))
    (hr'c : Continuous (deriv r)) (hr'L : LocallyLipschitz (deriv r))
    (hr'b : ∀ z, |deriv r z| ≤ N) (hr'' : ∀ᵐ z ∂(volume : Measure ℝ), |deriv (deriv r) z| ≤ N * jb z ^ s)
    (hGi : Integrable G) (hG0 : ∀ u, 0 ≤ G u)
    (hGle : ∀ u, u ≠ 0 → ∀ y, min (|u| ^ (-p)) (|u| ^ (-1 - p)) * jb (y - u) ^ s ≤ 4 * jb y * G u) :
    LocallyLipschitz (fun y => ∫ z, K y z * deriv r z) ∧
    (∀ y, HasDerivAt (fun y => ∫ z, K y z * deriv r z)
      (∫ z, (deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z)) y) ∧
    (∀ y : ℝ, Integrable (fun z =>
      deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z)) ∧
    (∀ R : ℝ, ∃ B : ℝ, ∀ y ∈ Icc (-R) R,
      ∫ z, |deriv (fun t => K (y + t) (z + t)) 0 * deriv r z| + |K y z * deriv (deriv r) z| ≤ B) ∧
    (∀ R η : ℝ, 0 < η → ∃ M : ℝ, ∀ y ∈ Icc (-R) R,
      ∫ z in {z : ℝ | M < |z|}, |deriv (fun t => K (y + t) (z + t)) 0 * deriv r z| +
        |K y z * deriv (deriv r) z| ≤ η) := by
  have hC : 0 ≤ C := by
    have := hglob 1 0 one_ne_zero
    have h2 : 0 < min (|(1:ℝ) - 0| ^ (-p)) (|(1:ℝ) - 0| ^ (-1 - p)) := by simp
    by_contra hc
    replace hc := lt_of_not_ge hc
    have : C * min (|(1:ℝ) - 0| ^ (-p)) (|(1:ℝ) - 0| ^ (-1 - p)) < 0 := mul_neg_of_neg_of_pos hc h2
    linarith [abs_nonneg (K 1 0), abs_nonneg (deriv (fun t => K (1 + t) (0 + t)) 0)]
  have hr's : ∀ z, |deriv r z| ≤ N * jb z ^ s := fun z =>
    (hr'b z).trans (le_mul_of_one_le_right hN0 (Real.one_le_rpow (c08_aux_one_le_jb z) hs0))
  have hIG0 : 0 ≤ ∫ u, G u := integral_nonneg hG0
  have hHb : ∀ y, ∀ᵐ z ∂(volume : Measure ℝ),
      |deriv (fun t => K (y + t) (z + t)) 0 * deriv r z| + |K y z * deriv (deriv r) z| ≤
        4 * C * N * jb y * G (y - z) := by
    intro y
    filter_upwards [c08_aux_ae_ne y, hr''] with z hz hz''
    have hyz : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    have hw := hglob y z (Ne.symm hz)
    have hg := hGle (y - z) hyz y
    rw [sub_sub_cancel] at hg
    have hjs := (Real.rpow_pos_of_pos (c08_aux_jb_pos z) s).le
    have hm0 : 0 ≤ min (|y - z| ^ (-p)) (|y - z| ^ (-1 - p)) :=
      le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    rw [abs_mul, abs_mul]
    have hA := abs_nonneg (K y z)
    have hB := abs_nonneg (deriv (fun t => K (y + t) (z + t)) 0)
    calc |deriv (fun t => K (y + t) (z + t)) 0| * |deriv r z| + |K y z| * |deriv (deriv r) z|
        ≤ |deriv (fun t => K (y + t) (z + t)) 0| * (N * jb z ^ s) + |K y z| * (N * jb z ^ s) := by
          gcongr; exact hr's z
      _ = (|K y z| + |deriv (fun t => K (y + t) (z + t)) 0|) * (N * jb z ^ s) := by ring
      _ ≤ (C * min (|y - z| ^ (-p)) (|y - z| ^ (-1 - p))) * (N * jb z ^ s) := by gcongr
      _ = C * N * (min (|y - z| ^ (-p)) (|y - z| ^ (-1 - p)) * jb z ^ s) := by ring
      _ ≤ C * N * (4 * jb y * G (y - z)) := by gcongr
      _ = 4 * C * N * jb y * G (y - z) := by ring
  have hHm : ∀ y, AEStronglyMeasurable (fun z =>
      deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z) volume :=
    fun y => ((hDm y).mul hr'c.aestronglyMeasurable).add
      ((hKm y).aestronglyMeasurable.mul (measurable_deriv _).aestronglyMeasurable)
  have hGyi : ∀ y, Integrable (fun z => 4 * C * N * jb y * G (y - z)) := fun y =>
    (hGi.comp_sub_left y).const_mul _
  have hHi : ∀ y, Integrable (fun z =>
      deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z) := by
    intro y
    refine (hGyi y).mono' (hHm y) ?_
    filter_upwards [hHb y] with z hz
    exact (abs_add_le _ _).trans hz
  have hIGy : ∀ y, ∫ z, 4 * C * N * jb y * G (y - z) = 4 * C * N * jb y * ∫ u, G u := by
    intro y; rw [integral_const_mul, integral_sub_left_eq_self G volume y]
  have hHbound : ∀ y, |∫ z, (deriv (fun t => K (y + t) (z + t)) 0 * deriv r z +
      K y z * deriv (deriv r) z)| ≤ 4 * C * N * jb y * ∫ u, G u := by
    intro y
    rw [← hIGy y, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hGyi y) ?_
    filter_upwards [hHb y] with z hz
    exact (abs_add_le _ _).trans hz
  have hKri : ∀ x, Integrable (fun z => K x z * deriv r z) := by
    intro x
    refine (hGyi x).mono' ((hKm x).aestronglyMeasurable.mul hr'c.aestronglyMeasurable) ?_
    filter_upwards [c08_aux_ae_ne x] with z hz
    have hxz : x - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    have hw := hglob x z (Ne.symm hz)
    have hg := hGle (x - z) hxz x
    rw [sub_sub_cancel] at hg
    have hjs := Real.one_le_rpow (c08_aux_one_le_jb z) hs0
    have hm0 : 0 ≤ min (|x - z| ^ (-p)) (|x - z| ^ (-1 - p)) :=
      le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    rw [Real.norm_eq_abs, abs_mul]
    have hB := abs_nonneg (deriv (fun t => K (x + t) (z + t)) 0)
    have hmm : min (|x - z| ^ (-p)) (|x - z| ^ (-1 - p)) ≤
        min (|x - z| ^ (-p)) (|x - z| ^ (-1 - p)) * jb z ^ s := le_mul_of_one_le_right hm0 hjs
    calc |K x z| * |deriv r z|
        ≤ (C * min (|x - z| ^ (-p)) (|x - z| ^ (-1 - p))) * N := by
          gcongr
          · linarith
          · exact hr'b z
      _ ≤ C * N * (min (|x - z| ^ (-p)) (|x - z| ^ (-1 - p)) * jb z ^ s) := by
          have := mul_nonneg hC hN0
          nlinarith
      _ ≤ C * N * (4 * jb x * G (x - z)) := by gcongr
      _ = 4 * C * N * jb x * G (x - z) := by ring
  have hderiv := c08_aux_gen_hasDerivAt hs0 hs1 hN0 hKm hHD hglob hr'c hr'L hr'b hr'' hGi hG0 hGle
    hKri hHm
  refine ⟨fun x => ?_, hderiv, hHi, fun R => ?_, fun R η hη => ?_⟩
  · -- locally Lipschitz
    set B := 4 * C * N * (2 + |x|) * ∫ u, G u with hB
    have hB0 : 0 ≤ B := by have := abs_nonneg x; positivity
    refine ⟨Real.toNNReal B, Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
      LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hB0]
    refine c08_aux_mvt_bound (fun ξ _ => (hderiv ξ).differentiableAt) (fun ξ hξ => ?_)
    have hξ' : ξ ∈ Icc (x - 1) (x + 1) := uIcc_subset_Icc ha hb hξ
    rw [(hderiv ξ).deriv]
    refine (hHbound ξ).trans ?_
    have : jb ξ ≤ 2 + |x| := by
      have := c08_aux_jb_le_one_add ξ
      have : |ξ| ≤ 1 + |x| := by
        rw [abs_le]; constructor <;> linarith [hξ'.1, hξ'.2, le_abs_self x, neg_abs_le x]
      linarith
    rw [hB]
    gcongr
  · -- uniform bound
    refine ⟨4 * C * N * (1 + |R|) * ∫ u, G u, fun y hy => ?_⟩
    have hjy : jb y ≤ 1 + |R| := by
      have := c08_aux_jb_le_one_add y
      have : |y| ≤ |R| := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2, le_abs_self R, neg_abs_le R]
      linarith
    refine (integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity) (hGyi y)
      (hHb y)).trans ?_
    rw [hIGy y]
    gcongr
  · -- uniform tails
    set A := 4 * C * N * (1 + |R|) with hA
    have hA0 : 0 ≤ A := by positivity
    obtain ⟨T, hT⟩ := c08_aux_tail hGi (δ := η / (A + 1)) (by positivity)
    refine ⟨T + |R|, fun y hy => ?_⟩
    have hyR : |y| ≤ |R| := by
      rw [abs_le]; constructor <;> linarith [hy.1, hy.2, le_abs_self R, neg_abs_le R]
    have hjy : jb y ≤ 1 + |R| := by
      have := c08_aux_jb_le_one_add y
      linarith
    have hmeas : MeasurableSet {z : ℝ | T + |R| < |z|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have hmeasT : MeasurableSet {v : ℝ | T < |v|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    have step1 : ∫ z in {z : ℝ | T + |R| < |z|},
        |deriv (fun t => K (y + t) (z + t)) 0 * deriv r z| + |K y z * deriv (deriv r) z| ≤
        ∫ z in {z : ℝ | T + |R| < |z|}, A * G (y - z) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
        ((hGi.comp_sub_left y).const_mul A).integrableOn ?_
      filter_upwards [ae_restrict_of_ae (hHb y)] with z hz
      refine hz.trans ?_
      have := hG0 (y - z)
      rw [hA]
      have : 4 * C * N * jb y ≤ 4 * C * N * (1 + |R|) := by gcongr
      nlinarith
    have step2 : ∫ z in {z : ℝ | T + |R| < |z|}, A * G (y - z) ≤
        ∫ z, A * {v : ℝ | T < |v|}.indicator G (y - z) := by
      rw [← integral_indicator hmeas]
      refine integral_mono_of_nonneg ?_ (((hGi.indicator hmeasT).comp_sub_left y).const_mul A)
        (Eventually.of_forall fun z => ?_)
      · refine Eventually.of_forall fun z => ?_
        simp only [Pi.zero_apply]
        exact Set.indicator_nonneg (fun z _ => mul_nonneg hA0 (hG0 _)) z
      · by_cases hz : z ∈ {z : ℝ | T + |R| < |z|}
        · rw [Set.indicator_of_mem hz]
          have : y - z ∈ {v : ℝ | T < |v|} := by
            simp only [mem_ofPred_eq] at hz ⊢
            have := abs_sub_abs_le_abs_sub z y
            rw [abs_sub_comm z y] at this
            linarith
          show A * G (y - z) ≤ A * {v : ℝ | T < |v|}.indicator G (y - z)
          rw [Set.indicator_of_mem this]
        · rw [Set.indicator_of_notMem hz]
          exact mul_nonneg hA0 (Set.indicator_nonneg (fun v _ => hG0 v) _)
    have step3 : ∫ z, A * {v : ℝ | T < |v|}.indicator G (y - z) =
        A * ∫ v, {v : ℝ | T < |v|}.indicator G v := by
      rw [integral_const_mul, integral_sub_left_eq_self ({v : ℝ | T < |v|}.indicator G) volume y]
    refine step1.trans (step2.trans (le_of_eq_of_le step3 ?_))
    calc A * ∫ v, {v : ℝ | T < |v|}.indicator G v ≤ A * (η / (A + 1)) := by gcongr
      _ ≤ η := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith

/-- Blueprint: lem:c08_R2_derivative.  For admissible `γ`, `r ∈ X_γ`: `ℛ_{2,ε} r` is locally
Lipschitz and a.e. `∂_y ℛ_{2,ε} r = ∫ [(∂_y+∂_z)K r' + K r''] dz`, the integral absolutely
convergent locally uniformly in `y`.
Encoding: "absolutely convergent, locally uniformly in y" is formalised as: absolutely
integrable for every `y`, with `L¹`-norm bounded and tails `∫_{|z|>M}` uniformly small for `y` in
compact intervals. -/
theorem c08_R2_derivative (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, admissibleGamma p γ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
      ∀ r ∈ X_gamma p γ,
        LocallyLipschitz (R_eps_two p ε r) ∧
        (∀ᵐ y, deriv (R_eps_two p ε r) y =
          ∫ z, (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
            R_eps_kernel p ε y z * deriv (deriv r) z)) ∧
        (∀ y : ℝ, Integrable (fun z =>
          deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
            R_eps_kernel p ε y z * deriv (deriv r) z)) ∧
        (∀ R : ℝ, ∃ B : ℝ, ∀ y ∈ Icc (-R) R,
          ∫ z, |deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z| +
            |R_eps_kernel p ε y z * deriv (deriv r) z| ≤ B) ∧
        (∀ R η : ℝ, 0 < η → ∃ M : ℝ, ∀ y ∈ Icc (-R) R,
          ∫ z in {z : ℝ | M < |z|}, |deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z| +
            |R_eps_kernel p ε y z * deriv (deriv r) z| ≤ η) := by
  obtain ⟨ε1, hε1, C, hC, hKN⟩ := c08_R2_kernel_near p hp hp1
  obtain ⟨c1, hc1, hmd⟩ := c08_aux_kernel_md p hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨min ε1 c1, lt_min hε1 hc1, fun γ hγ ε hε0 hε r hr => ?_⟩
  obtain ⟨-, hglob⟩ := hKN ε hε0 (hε.trans (min_le_left _ _))
  obtain ⟨-, -, hKm, hDm, hHD⟩ := hmd ε hε0 (hε.trans (min_le_right _ _))
  set s := max 0 (2 / p - γ) with hsdef
  have hs0 : 0 ≤ s := le_max_left _ _
  have hγp : 2 / p - γ < p := by
    have hb : beta p = (p + 1) / (2 * p) := rfl
    have : 2 / p - (beta p + 1 / p) < p := by
      rw [hb, show 2 / p - ((p + 1) / (2 * p) + 1 / p) = (1 - p) / (2 * p) by field_simp; ring,
        div_lt_iff₀ (by positivity)]
      nlinarith
    linarith [hγ.1]
  have hsp : s < p := max_lt hp0 hγp
  have hs1 : s ≤ 1 := by linarith
  have hγ1 : 1 / p < γ := by
    have : 0 < beta p := by unfold beta; positivity
    linarith [hγ.1]
  have hN0 : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg
  have hr'c : Continuous (deriv r) := hr.1.1.continuous_deriv le_rfl
  have hr'b : ∀ z, |deriv r z| ≤ xNorm p γ r := by
    have hae : ∀ᵐ z ∂(volume : Measure ℝ), |deriv r z| ≤ xNorm p γ r := by
      filter_upwards [c08_aux_X_ae_bound hp0 hr] with z hz
      refine hz.2.trans ?_
      have : jb z ^ (-γ + 1 / p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb z) (by linarith)
      nlinarith
    exact c08_aux_le_of_ae_halflines hr'c.abs continuous_const (ae_restrict_of_ae hae)
      (ae_restrict_of_ae hae)
  have hr'' : ∀ᵐ z ∂(volume : Measure ℝ), |deriv (deriv r) z| ≤ xNorm p γ r * jb z ^ s := by
    filter_upwards [c08_aux_X_ae_bound2 hp0 hr] with z hz
    refine hz.trans (mul_le_mul_of_nonneg_left ?_ hN0)
    exact Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb z) (by
      rw [hsdef]; linarith [le_max_right 0 (2 / p - γ)])
  have hG0 : ∀ u, 0 ≤ {v : ℝ | |v| ≤ 1}.indicator (fun v => |v| ^ (-p)) u +
      4 * jb u ^ (-1 - p + s) := by
    intro u
    have := Set.indicator_nonneg (s := {v : ℝ | |v| ≤ 1}) (f := fun v => |v| ^ (-p))
      (fun v _ => Real.rpow_nonneg (abs_nonneg v) _) u
    have := (Real.rpow_pos_of_pos (c08_aux_jb_pos u) (-1 - p + s)).le
    positivity
  obtain ⟨hL, hD, hI, hB, hT⟩ := c08_aux_gen_R2 (K := R_eps_kernel p ε) hs0 hs1 hN0 hKm hDm hHD
    hglob hr'c hr.1.2 hr'b hr'' (c08_aux_domS_integrable hp0 hp1 hsp) hG0
    (fun u hu y => c08_aux_domS_le hp0 hp1 hs0 hs1 hu y)
  exact ⟨hL, Eventually.of_forall fun y => (hD y).deriv, hI, hB, hT⟩

/-- In the ball `|y - z| ≤ ⟨y⟩/4`: `⟨z⟩^s ≤ 2^{|s|}⟨y⟩^s`. -/
theorem c08_aux_ball_weight {y z : ℝ} (h : |y - z| ≤ jb y / 4) (s : ℝ) :
    jb z ^ s ≤ 2 ^ |s| * jb y ^ s := by
  have hl := abs_le.1 (c08_aux_jb_lip y z)
  have h1 := c08_aux_one_le_jb y
  exact c08_aux_jb_rpow_compare (by linarith) (by linarith) s

/-- Blueprint: lem:c08_R2_near.  Near contributions of `ℛ_{2,ε}` and of its derivative. -/
theorem c08_R2_near (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, admissibleGamma p γ →
      ∀ ϑ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ϑ → (∀ x, ϑ x ∈ Icc (0 : ℝ) 1) →
        (∀ x ∈ Icc (-1 / 8 : ℝ) (1 / 8), ϑ x = 1) → tsupport ϑ ⊆ Icc (-1 / 4 : ℝ) (1 / 4) →
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc → ∀ r ∈ X_gamma p γ,
        (∀ y : ℝ, |∫ z in {z : ℝ | |y - z| ≤ jb y / 4}, R_eps_kernel p ε y z * deriv r z| ≤
          C * |c_eps p ε| * xNorm p γ r * jb y ^ (-γ)) ∧
        (∀ᵐ y, |∫ z, ϑ ((y - z) / jb y) *
            (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
              R_eps_kernel p ε y z * deriv (deriv r) z)| ≤
          C * |c_eps p ε| * xNorm p γ r * jb y ^ (-γ + 1 / p)) ∧
        ∀ y : ℝ, y ≤ 0 →
          (∫ z in {z : ℝ | |y - z| ≤ jb y / 4}, R_eps_kernel p ε y z * deriv r z) = 0 ∧
          (∫ z, ϑ ((y - z) / jb y) *
            (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
              R_eps_kernel p ε y z * deriv (deriv r) z)) = 0 := by
  obtain ⟨ε1, hε1, Ck, hCk, hK⟩ := c08_R2_kernel_near p hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨ε1, hε1, fun γ hγ ϑ hϑC hϑr hϑ1 hϑs => ?_⟩
  have hγ1 : 1 + 1 / p < γ := by
    have : 1 ≤ beta p := by
      unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
    linarith [hγ.1]
  have hp2 : 1 / p ≤ 2 * p + 1 := by
    rw [div_le_iff₀ hp0]; nlinarith
  set s1 := -γ + 1 / p with hs1
  set s2 := -γ + 2 / p with hs2
  set M1 := (2:ℝ) ^ |s1|
  set M2 := (2:ℝ) ^ |s2|
  have hM1 : 0 < M1 := by positivity
  have hM2 : 0 < M2 := by positivity
  have h1p : 0 < 1 - p := by linarith
  refine ⟨Ck * (M1 + M2) * (2 / (1 - p)) + 1, by positivity, fun ε hε0 hε r hr => ?_⟩
  obtain ⟨hKn, -⟩ := hK ε hε0 hε
  set c := |c_eps p ε| with hc
  set X := xNorm p γ r with hX
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ c := abs_nonneg _
  have hr1 := c08_aux_X_ae_bound hp0 hr
  have hr2 := c08_aux_X_ae_bound2 hp0 hr
  have hdiagD : ∀ x, deriv (fun s => R_eps_kernel p ε (x + s) (x + s)) 0 = 0 := by
    intro x
    have : (fun s => R_eps_kernel p ε (x + s) (x + s)) = fun _ => 0 := by
      funext s; exact c08_aux_kernel_diag p ε (x + s) hp0
    rw [this, deriv_const]
  have hsupp : ∀ y z, ϑ ((y - z) / jb y) ≠ 0 → |y - z| ≤ jb y / 4 := by
    intro y z hz
    have := hϑs (subset_tsupport _ (Function.mem_support.2 hz))
    have h2 : |(y - z) / jb y| ≤ 1 / 4 := abs_le.2 ⟨by linarith [this.1], this.2⟩
    rw [abs_div, abs_of_pos (c08_aux_jb_pos y), div_le_iff₀ (c08_aux_jb_pos y)] at h2
    linarith
  have hϑ1' : ∀ x, |ϑ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hϑr x).1]; exact (hϑr x).2
  have hCC : Ck * (M1 + M2) * (2 / (1 - p)) ≤ Ck * (M1 + M2) * (2 / (1 - p)) + 1 := by linarith
  refine ⟨fun y => ?_, Eventually.of_forall (fun y => ?_), fun y hy0 => ⟨?_, ?_⟩⟩
  · -- value part
    have hjy := c08_aux_jb_pos y
    have hR : 0 < jb y / 4 := by positivity
    obtain ⟨hbi, hbv⟩ := c08_aux_ball_rpow hp0 hp1 y hR
    set G0 := Ck * c * jb y ^ (-p - 2) * (X * M1 * jb y ^ s1) with hG0
    have hmeas : MeasurableSet {z : ℝ | |y - z| ≤ jb y / 4} :=
      measurableSet_le (by fun_prop) measurable_const
    have hb : ∀ᵐ z ∂(volume.restrict {z : ℝ | |y - z| ≤ jb y / 4}),
        ‖R_eps_kernel p ε y z * deriv r z‖ ≤ G0 * |y - z| ^ (-p) := by
      filter_upwards [ae_restrict_of_ae hr1, ae_restrict_mem hmeas] with z hz hzB
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hzy : z = y
      · subst hzy; rw [c08_aux_kernel_diag p ε z hp0, abs_zero, zero_mul]
        have := Real.rpow_pos_of_pos hjy (-p - 2); positivity
      · have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hzy))
        obtain ⟨-, -, hKb, -, -⟩ := hKn y z hw hzB
        have hrz : |deriv r z| ≤ X * M1 * jb y ^ s1 := by
          refine hz.2.trans ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (c08_aux_ball_weight hzB s1) hX0
        have := Real.rpow_pos_of_pos hw (-p)
        calc |R_eps_kernel p ε y z| * |deriv r z|
            ≤ (Ck * c * jb y ^ (-p - 2) * |y - z| ^ (-p)) * (X * M1 * jb y ^ s1) :=
              mul_le_mul hKb hrz (abs_nonneg _) (by positivity)
          _ = G0 * |y - z| ^ (-p) := by rw [hG0]; ring
    have hint := norm_integral_le_of_norm_le (hbi.const_mul G0) hb
    rw [Real.norm_eq_abs, integral_const_mul, hbv] at hint
    refine hint.trans ?_
    -- exponent bookkeeping
    have h4 : (jb y / 4) ^ (1 - p) ≤ jb y ^ (1 - p) :=
      Real.rpow_le_rpow (by positivity) (by linarith) h1p.le
    have hexp : jb y ^ (-p - 2) * jb y ^ s1 * jb y ^ (1 - p) ≤ jb y ^ (-γ) := by
      rw [← Real.rpow_add hjy, ← Real.rpow_add hjy]
      exact Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb y) (by rw [hs1]; linarith)
    have hG00 : 0 ≤ Ck * c * X * M1 := by positivity
    calc G0 * (2 * (jb y / 4) ^ (1 - p) / (1 - p))
        = Ck * c * X * M1 * (2 / (1 - p)) * (jb y ^ (-p - 2) * jb y ^ s1 * (jb y / 4) ^ (1 - p)) := by
          rw [hG0]; ring
      _ ≤ Ck * c * X * M1 * (2 / (1 - p)) * (jb y ^ (-p - 2) * jb y ^ s1 * jb y ^ (1 - p)) := by
          have := Real.rpow_pos_of_pos hjy (-p - 2)
          have := Real.rpow_pos_of_pos hjy s1
          gcongr
      _ ≤ Ck * c * X * M1 * (2 / (1 - p)) * jb y ^ (-γ) := by gcongr
      _ ≤ (Ck * (M1 + M2) * (2 / (1 - p)) + 1) * c * X * jb y ^ (-γ) := by
          have := Real.rpow_pos_of_pos hjy (-γ)
          have hcx : 0 ≤ c * X * jb y ^ (-γ) := by positivity
          have : Ck * M1 * (2 / (1 - p)) ≤ Ck * (M1 + M2) * (2 / (1 - p)) + 1 := by
            have : Ck * M1 * (2 / (1 - p)) ≤ Ck * (M1 + M2) * (2 / (1 - p)) := by
              gcongr; linarith
            linarith
          nlinarith
  · -- derivative part
    have hjy := c08_aux_jb_pos y
    have hR : 0 < jb y / 4 := by positivity
    obtain ⟨hbi, hbv⟩ := c08_aux_ball_rpow hp0 hp1 y hR
    have hmeas : MeasurableSet {z : ℝ | |y - z| ≤ jb y / 4} :=
      measurableSet_le (by fun_prop) measurable_const
    set G0 := Ck * c * X * (M1 * jb y ^ (-p - 3) * jb y ^ s1 + M2 * jb y ^ (-p - 2) * jb y ^ s2)
      with hG0
    have hG0n : 0 ≤ G0 := by
      have := Real.rpow_pos_of_pos hjy (-p - 3); have := Real.rpow_pos_of_pos hjy s1
      have := Real.rpow_pos_of_pos hjy (-p - 2); have := Real.rpow_pos_of_pos hjy s2
      positivity
    have hb : ∀ᵐ z ∂(volume : Measure ℝ),
        ‖ϑ ((y - z) / jb y) * (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
          R_eps_kernel p ε y z * deriv (deriv r) z)‖ ≤
        {z : ℝ | |y - z| ≤ jb y / 4}.indicator (fun z => G0 * |y - z| ^ (-p)) z := by
      filter_upwards [hr1, hr2] with z hz hz2
      rw [Real.norm_eq_abs]
      by_cases hϑz : ϑ ((y - z) / jb y) = 0
      · rw [hϑz, zero_mul, abs_zero]
        exact Set.indicator_nonneg (fun z _ => by
          have := Real.rpow_nonneg (abs_nonneg (y - z)) (-p); positivity) z
      have hzB := hsupp y z hϑz
      rw [Set.indicator_of_mem (show z ∈ {z : ℝ | |y - z| ≤ jb y / 4} from hzB)]
      by_cases hzy : z = y
      · subst hzy
        rw [hdiagD z, c08_aux_kernel_diag p ε z hp0]; simp only [zero_mul, add_zero, mul_zero,
          abs_zero]
        have := Real.rpow_nonneg (abs_nonneg (z - z)) (-p); positivity
      have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hzy))
      obtain ⟨-, -, hKb, hD, hDb⟩ := hKn y z hw hzB
      have hrz : |deriv r z| ≤ X * M1 * jb y ^ s1 := by
        refine hz.2.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (c08_aux_ball_weight hzB s1) hX0
      have hrz2 : |deriv (deriv r) z| ≤ X * M2 * jb y ^ s2 := by
        refine hz2.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (c08_aux_ball_weight hzB s2) hX0
      have hwp := Real.rpow_pos_of_pos hw (-p)
      rw [abs_mul]
      calc |ϑ ((y - z) / jb y)| * |deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
            R_eps_kernel p ε y z * deriv (deriv r) z|
          ≤ 1 * (|deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0| * |deriv r z| +
              |R_eps_kernel p ε y z| * |deriv (deriv r) z|) := by
            gcongr
            · exact hϑ1' _
            · exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
        _ ≤ 1 * ((Ck * c * jb y ^ (-p - 3) * |y - z| ^ (-p)) * (X * M1 * jb y ^ s1) +
              (Ck * c * jb y ^ (-p - 2) * |y - z| ^ (-p)) * (X * M2 * jb y ^ s2)) := by
            gcongr
        _ = G0 * |y - z| ^ (-p) := by rw [hG0]; ring
    have hgi : Integrable ({z : ℝ | |y - z| ≤ jb y / 4}.indicator (fun z => G0 * |y - z| ^ (-p))) :=
      IntegrableOn.integrable_indicator (hbi.const_mul G0) hmeas
    have hint := norm_integral_le_of_norm_le hgi hb
    rw [Real.norm_eq_abs, integral_indicator hmeas, integral_const_mul, hbv] at hint
    refine hint.trans ?_
    have h4 : (jb y / 4) ^ (1 - p) ≤ jb y ^ (1 - p) :=
      Real.rpow_le_rpow (by positivity) (by linarith) h1p.le
    have hj1 := c08_aux_one_le_jb y
    have e1 : jb y ^ (-p - 3) * jb y ^ s1 * jb y ^ (1 - p) ≤ jb y ^ (-γ + 1 / p) := by
      rw [← Real.rpow_add hjy, ← Real.rpow_add hjy]
      exact Real.rpow_le_rpow_of_exponent_le hj1 (by rw [hs1]; linarith)
    have e2 : jb y ^ (-p - 2) * jb y ^ s2 * jb y ^ (1 - p) ≤ jb y ^ (-γ + 1 / p) := by
      rw [← Real.rpow_add hjy, ← Real.rpow_add hjy]
      have h2p : 2 / p = 2 * (1 / p) := by ring
      exact Real.rpow_le_rpow_of_exponent_le hj1 (by rw [hs2, h2p]; linarith)
    have hq := Real.rpow_pos_of_pos hjy (-γ + 1 / p)
    calc G0 * (2 * (jb y / 4) ^ (1 - p) / (1 - p))
        ≤ G0 * (2 * jb y ^ (1 - p) / (1 - p)) := by gcongr
      _ = Ck * c * X * (2 / (1 - p)) * (M1 * (jb y ^ (-p - 3) * jb y ^ s1 * jb y ^ (1 - p)) +
            M2 * (jb y ^ (-p - 2) * jb y ^ s2 * jb y ^ (1 - p))) := by rw [hG0]; ring
      _ ≤ Ck * c * X * (2 / (1 - p)) * (M1 * jb y ^ (-γ + 1 / p) + M2 * jb y ^ (-γ + 1 / p)) := by
          gcongr
      _ = Ck * (M1 + M2) * (2 / (1 - p)) * c * X * jb y ^ (-γ + 1 / p) := by ring
      _ ≤ _ := by
          have : 0 ≤ c * X * jb y ^ (-γ + 1 / p) := by positivity
          nlinarith
  · -- vanishing of the value part
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hzB
    by_cases hzy : z = y
    · subst hzy; rw [c08_aux_kernel_diag p ε z hp0, zero_mul]
    · have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hzy))
      obtain ⟨-, h0, -⟩ := hKn y z hw hzB
      rw [(h0 hy0).1, zero_mul]
  · -- vanishing of the derivative part
    refine integral_eq_zero_of_ae (Eventually.of_forall (fun z => ?_))
    simp only [Pi.zero_apply]
    by_cases hϑz : ϑ ((y - z) / jb y) = 0
    · rw [hϑz, zero_mul]
    have hzB := hsupp y z hϑz
    by_cases hzy : z = y
    · subst hzy; rw [hdiagD z, c08_aux_kernel_diag p ε z hp0]; ring
    · have hw : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hzy))
      obtain ⟨-, h0, -⟩ := hKn y z hw hzB
      rw [(h0 hy0).1, (h0 hy0).2]; ring


/-- Joint `C¹` regularity of `K_ε` off the diagonal. -/
theorem c08_aux_kernel_joint (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ c1 → ∀ y z : ℝ, y ≠ z →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => R_eps_kernel p ε q.1 q.2) (y, z) := by
  obtain ⟨c1, hc1, hmd⟩ := c08_aux_kernel_md p hp hp1
  refine ⟨c1, hc1, fun ε hε0 hε y z hyz => ?_⟩
  obtain ⟨hφ2, h1, -, -, -⟩ := hmd ε hε0 hε
  set φ := phi_eps p ε with hφdef
  have hd : Differentiable ℝ φ := hφ2.differentiable (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ2.of_le (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv φ) := hφ2.iterate_deriv' 1 1
  have hpos : ∀ x, 0 < deriv φ x := fun x => by linarith [(abs_le.1 (h1 x)).1]
  have hev : (fun q : ℝ × ℝ => R_eps_kernel p ε q.1 q.2) =ᶠ[𝓝 (y, z)]
      fun q => calpha p * (1 - (deriv φ q.1 / ((φ q.1 - φ q.2) / (q.1 - q.2))) ^ (p + 1)) /
        |q.1 - q.2| ^ (1 + p) := by
    have : IsOpen {q : ℝ × ℝ | q.1 ≠ q.2} := isOpen_ne_fun continuous_fst continuous_snd
    filter_upwards [this.mem_nhds hyz] with q hq
    unfold R_eps_kernel c01_secant
    simp only [hq, ↓reduceIte]
    rfl
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hw : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hS : (φ y - φ z) / (y - z) ≠ 0 := by
    obtain ⟨ξ, -, e⟩ := c08_aux_secant_mvt hd hyz
    unfold c01_secant at e; simp only [hyz, ↓reduceIte] at e
    rw [e]; exact (hpos ξ).ne'
  have hA : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => q.1 - q.2) (y, z) :=
    (contDiff_fst.sub contDiff_snd).contDiffAt
  have hN : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (φ q.1 - φ q.2) / (q.1 - q.2)) (y, z) :=
    ((hφ1.comp contDiff_fst).sub (hφ1.comp contDiff_snd)).contDiffAt.div hA hw
  have hQ : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => deriv φ q.1 / ((φ q.1 - φ q.2) / (q.1 - q.2))) (y, z) :=
    (hd1.comp contDiff_fst).contDiffAt.div hN hS
  have hQpos : deriv φ y / ((φ y - φ z) / (y - z)) ≠ 0 := div_ne_zero (hpos y).ne' hS
  have hR := hQ.rpow_const_of_ne (p := p + 1) hQpos
  have hAbs : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => |q.1 - q.2|) (y, z) :=
    ContDiffAt.comp (x := (y, z)) (g := fun x : ℝ => |x|) (f := fun q : ℝ × ℝ => q.1 - q.2)
      (contDiffAt_abs hw) hA
  have hD := hAbs.rpow_const_of_ne (p := 1 + p) (abs_ne_zero.2 hw)
  exact (contDiffAt_const.mul (contDiffAt_const.sub hR)).div hD
    (Real.rpow_pos_of_pos (abs_pos.2 hw) _).ne'

/-- Partial derivatives from joint differentiability: `(∂_y+∂_z)K = ∂_yK + ∂_zK`. -/
theorem c08_aux_joint_derivs {K : ℝ → ℝ → ℝ} {y z : ℝ}
    (h : DifferentiableAt ℝ (fun q : ℝ × ℝ => K q.1 q.2) (y, z)) :
    HasDerivAt (fun y' => K y' z) (deriv (fun y' => K y' z) y) y ∧
    HasDerivAt (fun z' => K y z') (deriv (fun z' => K y z') z) z ∧
    deriv (fun t => K (y + t) (z + t)) 0 =
      deriv (fun y' => K y' z) y + deriv (fun z' => K y z') z := by
  set L := fderiv ℝ (fun q : ℝ × ℝ => K q.1 q.2) (y, z)
  have hL := h.hasFDerivAt
  have h1 : HasDerivAt (fun y' => K y' z) (L (1, 0)) y :=
    hL.comp_hasDerivAt (f := fun y' : ℝ => (y', z)) y ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have h2 : HasDerivAt (fun z' => K y z') (L (0, 1)) z :=
    hL.comp_hasDerivAt (f := fun z' : ℝ => (y, z')) z ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  have hc : HasDerivAt (fun t : ℝ => (y + t, z + t)) ((1 : ℝ), (1 : ℝ)) 0 :=
    ((hasDerivAt_id (0:ℝ)).const_add y).prodMk ((hasDerivAt_id (0:ℝ)).const_add z)
  have hL0 : HasFDerivAt (fun q : ℝ × ℝ => K q.1 q.2) L (y + 0, z + 0) := by simpa using hL
  have h3 : HasDerivAt (fun t => K (y + t) (z + t)) (L (1, 1)) 0 :=
    hL0.comp_hasDerivAt (f := fun t : ℝ => (y + t, z + t)) 0 hc
  refine ⟨h1.differentiableAt.hasDerivAt, h2.differentiableAt.hasDerivAt, ?_⟩
  rw [h1.deriv, h2.deriv, h3.deriv, ← map_add]
  congr 1; simp

/-- `|y-z|^{-a} ≤ 8^a ⟨y⟩^{-a}` for `|y-z| ≥ ⟨y⟩/8`. -/
theorem c08_aux_far_weight_dist {y z a : ℝ} (ha : 0 ≤ a) (h : jb y / 8 ≤ |y - z|) :
    1 / |y - z| ^ a ≤ 8 ^ a * jb y ^ (-a) := by
  have hJ := c08_aux_jb_pos y
  have hw : 0 < jb y / 8 := by positivity
  have hJa := Real.rpow_pos_of_pos hJ a
  have h8a : (0:ℝ) < 8 ^ a := Real.rpow_pos_of_pos (by norm_num) a
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (hw.trans_le h) a)]
  calc (1:ℝ) = 8 ^ a * jb y ^ (-a) * (jb y / 8) ^ a := by
        rw [Real.div_rpow hJ.le (by norm_num), Real.rpow_neg hJ.le]; field_simp
    _ ≤ 8 ^ a * jb y ^ (-a) * |y - z| ^ a := by gcongr

/-- Far-region weights of lem:c08_R2_kernel_far, reduced to powers of `⟨y⟩`. -/
theorem c08_aux_far_weights {p y z : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h : jb y / 8 ≤ |y - z|) :
    jb y ^ (-p - 1) / |y - z| ^ (p + 1) + jb z ^ (-p) / |y - z| ^ (p + 2) ≤ 576 * jb y ^ (-p - 2) ∧
    jb y ^ (-p - 2) / |y - z| ^ (p + 1) + jb z ^ (-p) / |y - z| ^ (p + 3) ≤
      4160 * jb y ^ (-p - 3) := by
  have hJ := c08_aux_jb_pos y
  have hJ1 := c08_aux_one_le_jb y
  have hz1 : jb z ^ (-p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb z) (by linarith)
  have hz0 := (Real.rpow_pos_of_pos (c08_aux_jb_pos z) (-p)).le
  have w1 := c08_aux_far_weight_dist (a := p + 1) (by linarith) h
  have w2 := c08_aux_far_weight_dist (a := p + 2) (by linarith) h
  have w3 := c08_aux_far_weight_dist (a := p + 3) (by linarith) h
  have e8 : ∀ a b : ℝ, a ≤ b → (8:ℝ) ^ a ≤ 8 ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hab
  have k1 : (8:ℝ) ^ (p + 1) ≤ 64 := by
    have := e8 (p + 1) 2 (by linarith); norm_num at this; linarith
  have k2 : (8:ℝ) ^ (p + 2) ≤ 512 := by
    have := e8 (p + 2) 3 (by linarith); norm_num at this; linarith
  have k3 : (8:ℝ) ^ (p + 3) ≤ 4096 := by
    have := e8 (p + 3) 4 (by linarith); norm_num at this; linarith
  have j : ∀ a b : ℝ, a ≤ b → jb y ^ a ≤ jb y ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hJ1 hab
  have m : ∀ a b : ℝ, jb y ^ a * jb y ^ b = jb y ^ (a + b) := fun a b =>
    (Real.rpow_add hJ a b).symm
  have pa : ∀ a : ℝ, 0 ≤ jb y ^ a := fun a => (Real.rpow_pos_of_pos hJ a).le
  have q : ∀ a : ℝ, 0 ≤ (8:ℝ) ^ a := fun a => (Real.rpow_pos_of_pos (by norm_num) a).le
  have r1 : ∀ x : ℝ, 0 ≤ x → x / |y - z| ^ (p + 1) ≤ x * (8 ^ (p + 1) * jb y ^ (-(p + 1))) :=
    fun x hx => by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left w1 hx
  have r2 : ∀ x : ℝ, 0 ≤ x → x / |y - z| ^ (p + 2) ≤ x * (8 ^ (p + 2) * jb y ^ (-(p + 2))) :=
    fun x hx => by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left w2 hx
  have r3 : ∀ x : ℝ, 0 ≤ x → x / |y - z| ^ (p + 3) ≤ x * (8 ^ (p + 3) * jb y ^ (-(p + 3))) :=
    fun x hx => by rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left w3 hx
  constructor
  · have t1 := r1 _ (pa (-p - 1))
    have t2 := r2 _ hz0
    have u1 : jb y ^ (-p - 1) * (8 ^ (p + 1) * jb y ^ (-(p + 1))) ≤ 64 * jb y ^ (-p - 2) := by
      rw [show jb y ^ (-p - 1) * (8 ^ (p + 1) * jb y ^ (-(p + 1))) =
        8 ^ (p + 1) * (jb y ^ (-p - 1) * jb y ^ (-(p + 1))) by ring, m]
      exact mul_le_mul k1 (j _ _ (by linarith)) (pa _) (by norm_num)
    have u2 : jb z ^ (-p) * (8 ^ (p + 2) * jb y ^ (-(p + 2))) ≤ 512 * jb y ^ (-p - 2) := by
      rw [show -(p + 2) = -p - 2 by ring]
      have := pa (-p - 2)
      calc jb z ^ (-p) * (8 ^ (p + 2) * jb y ^ (-p - 2)) ≤ 1 * (512 * jb y ^ (-p - 2)) := by
            gcongr
        _ = _ := one_mul _
    linarith
  · have t1 := r1 _ (pa (-p - 2))
    have t2 := r3 _ hz0
    have u1 : jb y ^ (-p - 2) * (8 ^ (p + 1) * jb y ^ (-(p + 1))) ≤ 64 * jb y ^ (-p - 3) := by
      rw [show jb y ^ (-p - 2) * (8 ^ (p + 1) * jb y ^ (-(p + 1))) =
        8 ^ (p + 1) * (jb y ^ (-p - 2) * jb y ^ (-(p + 1))) by ring, m]
      exact mul_le_mul k1 (j _ _ (by linarith)) (pa _) (by norm_num)
    have u2 : jb z ^ (-p) * (8 ^ (p + 3) * jb y ^ (-(p + 3))) ≤ 4096 * jb y ^ (-p - 3) := by
      rw [show -(p + 3) = -p - 3 by ring]
      have := pa (-p - 3)
      calc jb z ^ (-p) * (8 ^ (p + 3) * jb y ^ (-p - 3)) ≤ 1 * (4096 * jb y ^ (-p - 3)) := by
            gcongr
        _ = _ := one_mul _
    linarith

/-- Abstract-kernel version of the integration by parts in lem:c08_R2_far (2), for fixed `y`. -/
theorem c08_aux_far_ibp {K : ℝ → ℝ → ℝ} {ϑ r : ℝ → ℝ} {y BK BD Mθ N δ : ℝ}
    (hKj : ∀ z, y ≠ z → ContDiffAt ℝ 1 (fun q : ℝ × ℝ => K q.1 q.2) (y, z))
    (hKm : Measurable (K y))
    (hϑ : ContDiff ℝ (⊤ : ℕ∞) ϑ) (hϑr : ∀ x, ϑ x ∈ Icc (0 : ℝ) 1)
    (hϑ1 : ∀ x ∈ Icc (-1 / 8 : ℝ) (1 / 8), ϑ x = 1) (hMθ : ∀ x, |deriv ϑ x| ≤ Mθ)
    (hr'c : Continuous (deriv r)) (hr'L : LocallyLipschitz (deriv r))
    (hr'i : Integrable (deriv r))
    (hδ : 0 < δ) (hr'd : ∀ z, |deriv r z| ≤ N * jb z ^ (-δ))
    (hI1 : Integrable (fun z => deriv (fun t => K (y + t) (z + t)) 0 * deriv r z +
      K y z * deriv (deriv r) z))
    (hfar : ∀ z, jb y / 8 ≤ |y - z| → |K y z| ≤ BK ∧ |deriv (fun y' => K y' z) y| ≤ BD) :
    (∫ z, (1 - ϑ ((y - z) / jb y)) *
        (deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z)) =
      (∫ z, (1 - ϑ ((y - z) / jb y)) * deriv (fun y' => K y' z) y * deriv r z) -
        1 / jb y * ∫ z, deriv ϑ ((y - z) / jb y) * K y z * deriv r z ∧
    |∫ z, (1 - ϑ ((y - z) / jb y)) *
        (deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z)| ≤
      (BD + Mθ * BK / jb y) * ∫ z, |deriv r z| := by
  set J := jb y with hJdef
  have hJ : 0 < J := c08_aux_jb_pos y
  have hJ8 : 0 < J / 8 := by positivity
  have hfy : J / 8 ≤ |y - (y + J)| := by
    rw [show y - (y + J) = -J by ring, abs_neg, abs_of_pos hJ]; linarith
  have hBK : 0 ≤ BK := (abs_nonneg _).trans (hfar _ hfy).1
  have hBD : 0 ≤ BD := (abs_nonneg _).trans (hfar _ hfy).2
  have hM : 0 ≤ Mθ := (abs_nonneg _).trans (hMθ 0)
  have hϑ1' : ContDiff ℝ 1 ϑ := hϑ.of_le (by exact_mod_cast le_top)
  have hϑd : Differentiable ℝ ϑ := hϑ1'.differentiable (by norm_num)
  have hϑ'c : Continuous (deriv ϑ) := hϑ1'.continuous_deriv le_rfl
  -- the cutoff `1 - ϑ((y-z)/J)`
  have harg : Continuous (fun z : ℝ => (y - z) / J) := (continuous_const.sub continuous_id).div_const _
  have hcutC : ContDiff ℝ 1 (fun z => 1 - ϑ ((y - z) / J)) :=
    contDiff_const.sub (hϑ1'.comp ((contDiff_const.sub contDiff_id).div_const _))
  have hcut01 : ∀ z, |1 - ϑ ((y - z) / J)| ≤ 1 := fun z => by
    have := hϑr ((y - z) / J); rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hnear : ∀ z, |y - z| ≤ J / 8 → 1 - ϑ ((y - z) / J) = 0 := by
    intro z hz
    rw [hϑ1 _ ⟨?_, ?_⟩, sub_self]
    · rw [le_div_iff₀ hJ]; linarith [(abs_le.1 hz).1]
    · rw [div_le_iff₀ hJ]; linarith [(abs_le.1 hz).2]
  have hnear' : ∀ z, |y - z| < J / 8 → deriv ϑ ((y - z) / J) = 0 := by
    intro z hz
    have hx : |(y - z) / J| < 1 / 8 := by
      rw [abs_div, abs_of_pos hJ, div_lt_iff₀ hJ]; linarith
    have hev : ϑ =ᶠ[𝓝 ((y - z) / J)] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhds (abs_lt.1 hx).1 (abs_lt.1 hx).2] with x hx'
      exact hϑ1 x ⟨by linarith [hx'.1], hx'.2.le⟩
    rw [hev.deriv_eq, deriv_const]
  have hcutfar : ∀ z, 1 - ϑ ((y - z) / J) ≠ 0 → J / 8 ≤ |y - z| := fun z hz => by
    by_contra h; exact hz (hnear z (lt_of_not_ge h).le)
  have hθfar : ∀ z, deriv ϑ ((y - z) / J) ≠ 0 → J / 8 ≤ |y - z| := fun z hz => by
    by_contra h; exact hz (hnear' z (lt_of_not_ge h))
  have hcutd : ∀ z, HasDerivAt (fun z => 1 - ϑ ((y - z) / J)) (deriv ϑ ((y - z) / J) / J) z := by
    intro z
    have h1 : HasDerivAt (fun z : ℝ => (y - z) / J) (-1 / J) z := by
      simpa using ((hasDerivAt_id z).const_sub y).div_const J
    have := ((hϑd ((y - z) / J)).hasDerivAt.comp z h1).const_sub 1
    exact this.congr_deriv (by ring)
  -- joint derivatives
  have hJD := fun z (h : y ≠ z) => c08_aux_joint_derivs ((hKj z h).differentiableAt (by norm_num))
  -- `f = (1-ϑ) K r'`
  set f : ℝ → ℝ := fun z => (1 - ϑ ((y - z) / J)) * K y z * deriv r z with hfdef
  have hfd : ∀ z, y ≠ z → DifferentiableAt ℝ (deriv r) z → HasDerivAt f
      (deriv ϑ ((y - z) / J) / J * K y z * deriv r z +
        (1 - ϑ ((y - z) / J)) * deriv (fun z' => K y z') z * deriv r z +
        (1 - ϑ ((y - z) / J)) * K y z * deriv (deriv r) z) z := by
    intro z h hd
    have := ((hcutd z).mul (hJD z h).2.1).mul hd.hasDerivAt
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply]; ring
  have hderf : ∀ᵐ z ∂(volume : Measure ℝ), deriv f z =
      deriv ϑ ((y - z) / J) / J * K y z * deriv r z +
        (1 - ϑ ((y - z) / J)) * deriv (fun z' => K y z') z * deriv r z +
        (1 - ϑ ((y - z) / J)) * K y z * deriv (deriv r) z := by
    filter_upwards [c08_aux_ae_ne y, c08_aux_ae_differentiable hr'L] with z hz hd
    exact (hfd z (Ne.symm hz) hd).deriv
  -- the three integrands
  have hI3 : Integrable (fun z => deriv ϑ ((y - z) / J) * K y z * deriv r z) := by
    refine (hr'i.abs.const_mul (Mθ * BK)).mono'
      (((hϑ'c.comp harg).measurable.mul hKm).mul hr'c.measurable).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases h0 : deriv ϑ ((y - z) / J) = 0
    · rw [h0, abs_zero, zero_mul, zero_mul]; positivity
    · have := (hfar z (hθfar z h0)).1
      have h1 := hMθ ((y - z) / J)
      have := abs_nonneg (deriv r z)
      calc |deriv ϑ ((y - z) / J)| * |K y z| * |deriv r z| ≤ Mθ * BK * |deriv r z| := by gcongr
        _ = _ := rfl
  have hI2b : ∀ z, |(1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z| ≤
      BD * |deriv r z| := by
    intro z
    rw [abs_mul, abs_mul]
    by_cases h0 : 1 - ϑ ((y - z) / J) = 0
    · rw [h0, abs_zero, zero_mul, zero_mul]; positivity
    · have := (hfar z (hcutfar z h0)).2
      have := hcut01 z
      have := abs_nonneg (deriv r z)
      calc |1 - ϑ ((y - z) / J)| * |deriv (fun y' => K y' z) y| * |deriv r z|
          ≤ 1 * BD * |deriv r z| := by gcongr
        _ = BD * |deriv r z| := by ring
  have hI1c : Integrable (fun z => (1 - ϑ ((y - z) / J)) *
      (deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z)) :=
    hI1.bdd_mul hcutC.continuous.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hcut01 z)
  have hEq : ∀ᵐ z ∂(volume : Measure ℝ), (1 - ϑ ((y - z) / J)) *
      (deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z) =
      (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z + deriv f z -
        1 / J * (deriv ϑ ((y - z) / J) * K y z * deriv r z) := by
    filter_upwards [hderf, c08_aux_ae_ne y] with z hz hzy
    rw [hz, (hJD z (Ne.symm hzy)).2.2]
    field_simp
    ring
  have hI2m : AEStronglyMeasurable (fun z =>
      (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z) volume := by
    refine ((hI1c.aestronglyMeasurable.sub (measurable_deriv f).aestronglyMeasurable).add
      (hI3.aestronglyMeasurable.const_mul (1 / J))).congr ?_
    filter_upwards [hEq] with z hz
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hz]; ring
  have hI2 : Integrable (fun z =>
      (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z) :=
    (hr'i.abs.const_mul BD).mono' hI2m (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hI2b z)
  have hdfi : Integrable (deriv f) := by
    refine ((hI1c.sub hI2).add (hI3.const_mul (1 / J))).congr ?_
    filter_upwards [hEq] with z hz
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hz]; ring
  -- `f` is locally Lipschitz, integrable and tends to `0`
  have hfb : ∀ z, |f z| ≤ BK * |deriv r z| := by
    intro z
    simp only [hfdef]
    rw [abs_mul, abs_mul]
    by_cases h0 : 1 - ϑ ((y - z) / J) = 0
    · rw [h0, abs_zero, zero_mul, zero_mul]; positivity
    · have := (hfar z (hcutfar z h0)).1
      have := hcut01 z
      have := abs_nonneg (deriv r z)
      calc |1 - ϑ ((y - z) / J)| * |K y z| * |deriv r z| ≤ 1 * BK * |deriv r z| := by gcongr
        _ = BK * |deriv r z| := by ring
  have hgC : ContDiff ℝ 1 (fun z => (1 - ϑ ((y - z) / J)) * K y z) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : |y - z| < J / 8
    · have hev : (fun z => (1 - ϑ ((y - z) / J)) * K y z) =ᶠ[𝓝 z] fun _ => 0 := by
        have hop : IsOpen {z' : ℝ | |y - z'| < J / 8} :=
          isOpen_lt (continuous_const.sub continuous_id).abs continuous_const
        filter_upwards [hop.mem_nhds hz] with z' hz'
        rw [hnear z' (le_of_lt hz'), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hyz : y ≠ z := by
        intro h; apply hz; rw [h, sub_self, abs_zero]; exact hJ8
      have hk : ContDiffAt ℝ 1 (fun z' => K y z') z :=
        ContDiffAt.comp (x := z) (g := fun q : ℝ × ℝ => K q.1 q.2) (f := fun z' : ℝ => (y, z'))
          (hKj z hyz) (contDiffAt_const.prodMk contDiffAt_id)
      exact hcutC.contDiffAt.mul hk
  have hfL : LocallyLipschitz f := c08_aux_locallyLipschitz_mul hgC.locallyLipschitz hr'L
  have hfi : Integrable f :=
    (hr'i.abs.const_mul BK).mono' hfL.continuous.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hfb z)
  have hlim : Tendsto f (cocompact ℝ) (𝓝 0) := by
    refine c08_aux_tendsto_of_bound (N := BK * N) hδ (fun z => (hfb z).trans ?_)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hr'd z) hBK
  have hibp := c08_aux_ibp_line hfL hfi hdfi hlim (g := fun _ => (1:ℝ)) contDiff_const (B := 1)
    (fun _ => by simp) (fun _ => by simp)
  simp only [one_mul, deriv_const', zero_mul, integral_zero, neg_zero] at hibp
  -- the identity
  have hid : (∫ z, (1 - ϑ ((y - z) / J)) *
      (deriv (fun t => K (y + t) (z + t)) 0 * deriv r z + K y z * deriv (deriv r) z)) =
      (∫ z, (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z) -
        1 / J * ∫ z, deriv ϑ ((y - z) / J) * K y z * deriv r z := by
    have hsum : Integrable (fun z => (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y *
        deriv r z + deriv f z) := hI2.add hdfi
    rw [integral_congr_ae hEq, integral_sub hsum (hI3.const_mul _),
      integral_add hI2 hdfi, hibp, integral_const_mul]
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  have b2 : |∫ z, (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z| ≤
      BD * ∫ z, |deriv r z| := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hr'i.abs.const_mul BD)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hI2b z)
  have b3 : |∫ z, deriv ϑ ((y - z) / J) * K y z * deriv r z| ≤ Mθ * BK * ∫ z, |deriv r z| := by
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hr'i.abs.const_mul _) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases h0 : deriv ϑ ((y - z) / J) = 0
    · rw [h0, abs_zero, zero_mul, zero_mul]; have := abs_nonneg (deriv r z); positivity
    · have := (hfar z (hθfar z h0)).1
      have h1 := hMθ ((y - z) / J)
      have := abs_nonneg (deriv r z)
      gcongr
  have hL0 : 0 ≤ ∫ z, |deriv r z| := integral_nonneg fun z => abs_nonneg _
  calc |(∫ z, (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z) -
        1 / J * ∫ z, deriv ϑ ((y - z) / J) * K y z * deriv r z|
      ≤ |∫ z, (1 - ϑ ((y - z) / J)) * deriv (fun y' => K y' z) y * deriv r z| +
        1 / J * |∫ z, deriv ϑ ((y - z) / J) * K y z * deriv r z| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / J)]
    _ ≤ BD * (∫ z, |deriv r z|) + 1 / J * (Mθ * BK * ∫ z, |deriv r z|) := by gcongr
    _ = (BD + Mθ * BK / J) * ∫ z, |deriv r z| := by field_simp

/-- Blueprint: lem:c08_R2_far.  Far contributions of `ℛ_{2,ε}` and the integration-by-parts identity
for the far part of its derivative. -/
theorem c08_R2_far (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, admissibleGamma p γ →
      ∀ ϑ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ϑ → (∀ x, ϑ x ∈ Icc (0 : ℝ) 1) →
        (∀ x ∈ Icc (-1 / 8 : ℝ) (1 / 8), ϑ x = 1) → tsupport ϑ ⊆ Icc (-1 / 4 : ℝ) (1 / 4) →
      ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc → ∀ r ∈ X_gamma p γ,
        (∀ y : ℝ, |∫ z in {z : ℝ | jb y / 4 < |y - z|}, R_eps_kernel p ε y z * deriv r z| ≤
          C * |c_eps p ε| * xNorm p γ r * jb y ^ (-p - 2)) ∧
        ∀ᵐ y,
          (∫ z, (1 - ϑ ((y - z) / jb y)) *
              (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
                R_eps_kernel p ε y z * deriv (deriv r) z)) =
            (∫ z, (1 - ϑ ((y - z) / jb y)) * deriv (fun y' => R_eps_kernel p ε y' z) y * deriv r z) -
              1 / jb y * ∫ z, deriv ϑ ((y - z) / jb y) * R_eps_kernel p ε y z * deriv r z ∧
          |∫ z, (1 - ϑ ((y - z) / jb y)) *
              (deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
                R_eps_kernel p ε y z * deriv (deriv r) z)| ≤
            C * |c_eps p ε| * xNorm p γ r * jb y ^ (-p - 3) := by
  obtain ⟨εD, hεD, hDer⟩ := c08_R2_derivative p hp hp1
  obtain ⟨εF, hεF, CF, hCF, hKF⟩ := c08_R2_kernel_far p hp hp1
  obtain ⟨c1, hc1, hmd⟩ := c08_aux_kernel_md p hp hp1
  obtain ⟨c2, hc2, hjoint⟩ := c08_aux_kernel_joint p hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨min (min εD εF) (min c1 c2), lt_min (lt_min hεD hεF) (lt_min hc1 hc2),
    fun γ hγ ϑ hϑ hϑr hϑ1 hϑs => ?_⟩
  have hγ1 : 1 + 1 / p < γ := by
    have : 1 ≤ beta p := by
      unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
    linarith [hγ.1]
  obtain ⟨CL, hCL, hL1, -⟩ := c08_L1_embedding p γ hp hp1 hγ1
  obtain ⟨Mθ, hMθ⟩ : ∃ M, ∀ x, |deriv ϑ x| ≤ M := by
    have hcs : HasCompactSupport ϑ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport ϑ) hϑs
    have hϑ1' : ContDiff ℝ 1 ϑ := hϑ.of_le (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := (hϑ1'.continuous_deriv le_rfl).bounded_above_of_compact_support hcs.deriv
    exact ⟨M, fun x => by rw [← Real.norm_eq_abs]; exact hM x⟩
  have hM0 : 0 ≤ Mθ := (abs_nonneg _).trans (hMθ 0)
  refine ⟨(4160 + 576 * (Mθ + 1)) * CF * CL, by positivity, fun ε hε0 hε r hr => ?_⟩
  have hεD' : ε ≤ εD := hε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεF' : ε ≤ εF := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hc1' : ε ≤ c1 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc2' : ε ≤ c2 := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨-, -, hKm, -, -⟩ := hmd ε hε0 hc1'
  obtain ⟨-, -, hI1, -, -⟩ := hDer γ hγ ε hε0 hεD' r hr
  set N := xNorm p γ r with hNdef
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set c := |c_eps p ε| with hcdef
  have hc0 : 0 ≤ c := abs_nonneg _
  obtain ⟨-, hr'i, -, -, hsum, -⟩ := hL1 r hr
  have hL1r : ∫ z, |deriv r z| ≤ CL * N := by
    have h1 : 0 ≤ ∫ x, |r x| := integral_nonneg fun x => abs_nonneg _
    have h2 : 0 ≤ (eLpNorm r ⊤ volume).toReal := ENNReal.toReal_nonneg
    have h3 : 0 ≤ (eLpNorm (deriv r) ⊤ volume).toReal := ENNReal.toReal_nonneg
    linarith
  have hL0 : 0 ≤ ∫ z, |deriv r z| := integral_nonneg fun z => abs_nonneg _
  have hr'c : Continuous (deriv r) := hr.1.1.continuous_deriv le_rfl
  have hr'd : ∀ z, |deriv r z| ≤ N * jb z ^ (-(γ - 1 / p)) := by
    have hjc : Continuous (fun z => N * jb z ^ (-(γ - 1 / p))) := by
      refine continuous_const.mul (Continuous.rpow_const ?_ fun z => Or.inl (c08_aux_jb_pos z).ne')
      unfold jb; fun_prop
    have hae : ∀ᵐ z ∂(volume : Measure ℝ), |deriv r z| ≤ N * jb z ^ (-(γ - 1 / p)) := by
      filter_upwards [c08_aux_X_ae_bound hp0 hr] with z hz
      rw [show -(γ - 1 / p) = -γ + 1 / p by ring]; exact hz.2
    exact c08_aux_le_of_ae_halflines hr'c.abs hjc (ae_restrict_of_ae hae) (ae_restrict_of_ae hae)
  have hfarK : ∀ y z, jb y / 8 ≤ |y - z| →
      |R_eps_kernel p ε y z| ≤ 576 * CF * c * jb y ^ (-p - 2) ∧
      |deriv (fun y' => R_eps_kernel p ε y' z) y| ≤ 4160 * CF * c * jb y ^ (-p - 3) := by
    intro y z h
    obtain ⟨k1, k2⟩ := hKF ε hε0 hεF' y z h
    obtain ⟨w1, w2⟩ := c08_aux_far_weights hp0 hp1 h
    have hCc : 0 ≤ CF * c := by positivity
    constructor
    · calc |R_eps_kernel p ε y z| ≤ CF * c * (jb y ^ (-p - 1) / |y - z| ^ (p + 1) +
            jb z ^ (-p) / |y - z| ^ (p + 2)) := k1
        _ ≤ CF * c * (576 * jb y ^ (-p - 2)) := mul_le_mul_of_nonneg_left w1 hCc
        _ = _ := by ring
    · calc |deriv (fun y' => R_eps_kernel p ε y' z) y| ≤ CF * c * (jb y ^ (-p - 2) /
            |y - z| ^ (p + 1) + jb z ^ (-p) / |y - z| ^ (p + 3)) := k2
        _ ≤ CF * c * (4160 * jb y ^ (-p - 3)) := mul_le_mul_of_nonneg_left w2 hCc
        _ = _ := by ring
  have hδ : 0 < γ - 1 / p := by
    have : 0 < 1 / p := by positivity
    linarith
  refine ⟨fun y => ?_, Eventually.of_forall fun y => ?_⟩
  · -- part (1)
    have hJ := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-p - 2)
    have hmeas : MeasurableSet {z : ℝ | jb y / 4 < |y - z|} :=
      measurableSet_lt measurable_const (measurable_const.sub measurable_id).abs
    have hb : ∀ᵐ z ∂(volume.restrict {z : ℝ | jb y / 4 < |y - z|}),
        ‖R_eps_kernel p ε y z * deriv r z‖ ≤ 576 * CF * c * jb y ^ (-p - 2) * |deriv r z| := by
      refine (ae_restrict_iff' hmeas).2 (Eventually.of_forall fun z hz => ?_)
      have hz' : jb y / 8 ≤ |y - z| := by
        have := (c08_aux_jb_pos y); simp only [mem_ofPred_eq] at hz; linarith
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hfarK y z hz').1 (abs_nonneg _)
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hr'i.abs.const_mul _).integrableOn hb).trans ?_
    rw [integral_const_mul]
    have hsub : ∫ z in {z : ℝ | jb y / 4 < |y - z|}, |deriv r z| ≤ ∫ z, |deriv r z| :=
      setIntegral_le_integral hr'i.abs (Eventually.of_forall fun z => abs_nonneg _)
    calc 576 * CF * c * jb y ^ (-p - 2) * ∫ z in {z : ℝ | jb y / 4 < |y - z|}, |deriv r z|
        ≤ 576 * CF * c * jb y ^ (-p - 2) * (CL * N) := by
          gcongr; exact hsub.trans hL1r
      _ = 576 * CF * CL * c * N * jb y ^ (-p - 2) := by ring
      _ ≤ (4160 + 576 * (Mθ + 1)) * CF * CL * c * N * jb y ^ (-p - 2) := by
          gcongr; nlinarith
  · -- part (2)
    obtain ⟨hid, hbd⟩ := c08_aux_far_ibp (K := R_eps_kernel p ε) (y := y)
      (BK := 576 * CF * c * jb y ^ (-p - 2)) (BD := 4160 * CF * c * jb y ^ (-p - 3))
      (fun z hz => hjoint ε hε0 hc2' y z hz) (hKm y) hϑ hϑr hϑ1 hMθ hr'c hr.1.2 hr'i hδ hr'd
      (hI1 y) (fun z hz => hfarK y z hz)
    refine ⟨hid, hbd.trans ?_⟩
    have hJ := c08_aux_jb_pos y
    have e : jb y ^ (-p - 2) / jb y = jb y ^ (-p - 3) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hJ]; ring_nf
    have hJ3 := Real.rpow_pos_of_pos hJ (-p - 3)
    calc (4160 * CF * c * jb y ^ (-p - 3) + Mθ * (576 * CF * c * jb y ^ (-p - 2)) / jb y) *
          ∫ z, |deriv r z|
        = (4160 + 576 * Mθ) * CF * c * jb y ^ (-p - 3) * ∫ z, |deriv r z| := by
          rw [mul_div_assoc, show 576 * CF * c * jb y ^ (-p - 2) / jb y =
            576 * CF * c * (jb y ^ (-p - 2) / jb y) by ring, e]; ring
      _ ≤ (4160 + 576 * Mθ) * CF * c * jb y ^ (-p - 3) * (CL * N) := by gcongr
      _ ≤ (4160 + 576 * (Mθ + 1)) * CF * CL * c * N * jb y ^ (-p - 3) := by
          have : 0 ≤ CF * CL * c * N * jb y ^ (-p - 3) := by positivity
          nlinarith

/-- `‖G‖_{Y_γ} ≤ 2η` from a.e. bounds on both half-lines. -/
theorem c08_aux_Y_norm_le_of_ae {p γ : ℝ} {G : ℝ → ℝ} {η : ℝ}
    (h0 : ∀ᵐ y, 0 ≤ y → jb y ^ γ * (|G y| + jb y ^ (-1 / p) * |deriv G y|) ≤ η)
    (h1 : ∀ᵐ y, y ≤ 0 → jb y ^ γ * (|G y| + jb y * |deriv G y|) ≤ η) :
    Y_gamma_norm p γ G ≤ ENNReal.ofReal η + ENNReal.ofReal η := by
  unfold Y_gamma_norm
  gcongr
  · refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_Ici] with y hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Real.norm_eq_abs]
    exact hy hy0
  · refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_Iic] with y hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Real.norm_eq_abs]
    exact hy hy0

/-- `ρ` is smooth. -/
theorem c08_aux_rho_contDiff : ContDiff ℝ (⊤ : ℕ∞) rho := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with h | h
  · subst h
    have : rho =ᶠ[nhds 0] fun _ => (1:ℝ) := by
      filter_upwards [Ioo_mem_nhds (show (-1:ℝ) < 0 by norm_num) (show (0:ℝ) < 1 by norm_num)]
        with y hy
      unfold rho
      exact Real.smoothTransition.one_of_one_le (by
        have : |y| < 1 := abs_lt.2 ⟨hy.1, hy.2⟩
        linarith)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · unfold rho
    exact Real.smoothTransition.contDiffAt.comp x (contDiffAt_const.sub (contDiffAt_abs h))

/-- A cutoff `ϑ` as in lem:c08_R2_near: `ϑ(x) = ρ(8x)`. -/
theorem c08_aux_theta_exists : ∃ ϑ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ϑ ∧ (∀ x, ϑ x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Icc (-1 / 8 : ℝ) (1 / 8), ϑ x = 1) ∧ tsupport ϑ ⊆ Icc (-1 / 4 : ℝ) (1 / 4) := by
  refine ⟨fun x => rho (8 * x), c08_aux_rho_contDiff.comp (contDiff_const.mul contDiff_id),
    fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun x hx => ?_, ?_⟩
  · simp only [rho]
    apply Real.smoothTransition.one_of_one_le
    have : |x| ≤ 1 / 8 := abs_le.2 ⟨by linarith [hx.1], hx.2⟩
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8)]; linarith
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    simp only [Function.mem_support, rho] at hx
    by_contra hneg
    apply hx
    apply Real.smoothTransition.zero_of_nonpos
    have : 1 / 4 < |x| := by
      rcases not_and_or.1 hneg with h | h
      · rw [abs_of_neg (by linarith [not_le.1 h])]; linarith [not_le.1 h]
      · rw [abs_of_pos (by linarith [not_le.1 h])]; linarith [not_le.1 h]
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8)]; linarith

/-- Blueprint: lem:c08_R2_bound.  `ℛ_{2,ε} : X_γ → Y_γ` with `‖ℛ_{2,ε} r‖_{Y_γ} ≤ C ε ‖r‖_{X_γ}`. -/
theorem c08_R2_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, admissibleGamma p γ → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc → ∀ r ∈ X_gamma p γ,
        R_eps_two p ε r ∈ Y_gamma p γ ∧ yNorm p γ (R_eps_two p ε r) ≤ C * ε * xNorm p γ r := by
  obtain ⟨ε1, hε1, hDer⟩ := c08_R2_derivative p hp hp1
  obtain ⟨ε2, hε2, hNear⟩ := c08_R2_near p hp hp1
  obtain ⟨ε3, hε3, hFar⟩ := c08_R2_far p hp hp1
  obtain ⟨ε4, hε4, hNL⟩ := c08_conj_nonlocal p hp hp1
  obtain ⟨ϑ, hϑC, hϑr, hϑ1, hϑs⟩ := c08_aux_theta_exists
  have hp0 : 0 < p := by linarith
  refine ⟨min (min ε1 ε2) (min ε3 ε4), by positivity, fun γ hγ => ?_⟩
  obtain ⟨Cn, hCn, hN⟩ := hNear γ hγ ϑ hϑC hϑr hϑ1 hϑs
  obtain ⟨Cf, hCf, hF⟩ := hFar γ hγ ϑ hϑC hϑr hϑ1 hϑs
  have hγ1 : 1 + 1 / p < γ := by
    have : 1 ≤ beta p := by
      unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
    linarith [hγ.1]
  have hγ2 : γ < p + 2 := by linarith [hγ.2]
  refine ⟨4 * (Cn + Cf) + 1, by positivity, fun ε hε0 hε r hr => ?_⟩
  have e1 : ε ≤ ε1 := hε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : ε ≤ ε2 := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : ε ≤ ε3 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e4 : ε ≤ ε4 := hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hLip, hDae, hDint, -, -⟩ := hDer γ hγ ε hε0 e1 r hr
  obtain ⟨hN1, hN2, hN3⟩ := hN ε hε0 e2 r hr
  obtain ⟨hF1, hF2⟩ := hF ε hε0 e3 r hr
  have hr1 : ContDiff ℝ 1 r := hr.1.1
  obtain ⟨CL, -, hL1, -⟩ := c08_L1_embedding p γ hp hp1 hγ1
  obtain ⟨-, -, -, hdL, -⟩ := hL1 r hr
  obtain ⟨M, hM⟩ := c08_aux_bounded_of_memLp_top (hr1.continuous_deriv le_rfl) hdL
  have hKint : ∀ y, Integrable (fun z => R_eps_kernel p ε y z * deriv r z) := fun y =>
    (((hNL ε hε0 e4 r hr1 ⟨M, hM⟩ hr.1.2).2.2.2) y).2.2.1
  set c := |c_eps p ε| with hcdef
  have hcε : c ≤ ε := (c08_aux_c_eps_bound p ε hp hp1 hε0).2
  set X := xNorm p γ r with hX
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hc0 : 0 ≤ c := abs_nonneg _
  -- value bound
  have hval : ∀ y, |R_eps_two p ε r y| ≤ (Cn + Cf) * c * X * jb y ^ (-γ) := by
    intro y
    have hS : MeasurableSet {z : ℝ | |y - z| ≤ jb y / 4} :=
      measurableSet_le (by fun_prop) measurable_const
    have hcompl : {z : ℝ | |y - z| ≤ jb y / 4}ᶜ = {z : ℝ | jb y / 4 < |y - z|} := by
      ext z; simp [not_le]
    have hsplit := integral_add_compl hS (hKint y)
    rw [hcompl] at hsplit
    unfold R_eps_two
    rw [← hsplit]
    have h1 := hN1 y
    have h2 := hF1 y
    have hjb : jb y ^ (-p - 2) ≤ jb y ^ (-γ) :=
      Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb y) (by linarith)
    have : Cf * c * X * jb y ^ (-p - 2) ≤ Cf * c * X * jb y ^ (-γ) := by gcongr
    calc _ ≤ |∫ z in {z : ℝ | |y - z| ≤ jb y / 4}, R_eps_kernel p ε y z * deriv r z| +
          |∫ z in {z : ℝ | jb y / 4 < |y - z|}, R_eps_kernel p ε y z * deriv r z| := abs_add_le _ _
      _ ≤ _ := by linarith
  -- derivative bounds
  have hϑm : Continuous (fun z : ℝ => ϑ z) := hϑC.continuous
  have hder : ∀ᵐ y, (0 ≤ y → |deriv (R_eps_two p ε r) y| ≤
        (Cn + Cf) * c * X * jb y ^ (-γ + 1 / p)) ∧
      (y ≤ 0 → |deriv (R_eps_two p ε r) y| ≤ Cf * c * X * jb y ^ (-γ - 1)) := by
    filter_upwards [hDae, hN2, hF2] with y hD hn hf
    obtain ⟨-, hf⟩ := hf
    set f := fun z => deriv (fun s => R_eps_kernel p ε (y + s) (z + s)) 0 * deriv r z +
      R_eps_kernel p ε y z * deriv (deriv r) z with hfdef
    have hfi : Integrable f := hDint y
    have hcont : Continuous (fun z : ℝ => ϑ ((y - z) / jb y)) :=
      hϑm.comp (by fun_prop)
    have hb1 : ∀ z, ‖ϑ ((y - z) / jb y)‖ ≤ 1 := fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hϑr _).1]; exact (hϑr _).2
    have hi1 : Integrable (fun z => ϑ ((y - z) / jb y) * f z) :=
      hfi.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall hb1)
    have hi2 : Integrable (fun z => (1 - ϑ ((y - z) / jb y)) * f z) :=
      hfi.bdd_mul (continuous_const.sub hcont).aestronglyMeasurable
        (Eventually.of_forall fun z => by
          have h := hϑr ((y - z) / jb y)
          rw [mem_Icc] at h
          show ‖1 - ϑ ((y - z) / jb y)‖ ≤ 1
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2])
    have hsum : deriv (R_eps_two p ε r) y =
        (∫ z, ϑ ((y - z) / jb y) * f z) + ∫ z, (1 - ϑ ((y - z) / jb y)) * f z := by
      rw [hD, ← integral_add hi1 hi2]
      congr 1; ext z; ring
    have hjb1 := c08_aux_one_le_jb y
    constructor
    · intro _
      rw [hsum]
      have hjb : jb y ^ (-p - 3) ≤ jb y ^ (-γ + 1 / p) :=
        Real.rpow_le_rpow_of_exponent_le hjb1 (by
          have : 0 < 1 / p := by positivity
          linarith)
      have : Cf * c * X * jb y ^ (-p - 3) ≤ Cf * c * X * jb y ^ (-γ + 1 / p) := by gcongr
      calc _ ≤ |∫ z, ϑ ((y - z) / jb y) * f z| + |∫ z, (1 - ϑ ((y - z) / jb y)) * f z| :=
            abs_add_le _ _
        _ ≤ _ := by linarith
    · intro hy
      rw [hsum, (hN3 y hy).2, zero_add]
      have hjb : jb y ^ (-p - 3) ≤ jb y ^ (-γ - 1) :=
        Real.rpow_le_rpow_of_exponent_le hjb1 (by linarith)
      have : Cf * c * X * jb y ^ (-p - 3) ≤ Cf * c * X * jb y ^ (-γ - 1) := by gcongr
      exact hf.trans this
  set η := 2 * (Cn + Cf) * c * X with hη
  have hjbγ : ∀ y, jb y ^ γ * jb y ^ (-γ) = 1 := fun y => by
    rw [← Real.rpow_add (c08_aux_jb_pos y)]; simp
  have hY := c08_aux_Y_norm_le_of_ae (p := p) (γ := γ) (G := R_eps_two p ε r) (η := η)
    (by
      filter_upwards [hder] with y hy hy0
      have hd := hy.1 hy0
      have hv := hval y
      have hj := c08_aux_jb_pos y
      have e : jb y ^ γ * (jb y ^ (-1 / p) * jb y ^ (-γ + 1 / p)) = 1 := by
        rw [← Real.rpow_add hj, ← Real.rpow_add hj]; ring_nf; simp
      have hg0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos hj _).le
      have hq0 : 0 ≤ jb y ^ (-1 / p) := (Real.rpow_pos_of_pos hj _).le
      calc jb y ^ γ * (|R_eps_two p ε r y| + jb y ^ (-1 / p) * |deriv (R_eps_two p ε r) y|)
          ≤ jb y ^ γ * ((Cn + Cf) * c * X * jb y ^ (-γ) +
              jb y ^ (-1 / p) * ((Cn + Cf) * c * X * jb y ^ (-γ + 1 / p))) := by gcongr
        _ = (Cn + Cf) * c * X * (jb y ^ γ * jb y ^ (-γ)) +
              (Cn + Cf) * c * X * (jb y ^ γ * (jb y ^ (-1 / p) * jb y ^ (-γ + 1 / p))) := by ring
        _ = η := by rw [hjbγ, e, hη]; ring)
    (by
      filter_upwards [hder] with y hy hy0
      have hd := hy.2 hy0
      have hv := hval y
      have hj := c08_aux_jb_pos y
      have e : jb y ^ γ * (jb y * jb y ^ (-γ - 1)) = 1 := by
        conv_lhs => rw [show jb y * jb y ^ (-γ - 1) = jb y ^ (1:ℝ) * jb y ^ (-γ - 1) by
          rw [Real.rpow_one]]
        rw [← Real.rpow_add hj, ← Real.rpow_add hj]; ring_nf; simp
      have hg0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos hj _).le
      calc jb y ^ γ * (|R_eps_two p ε r y| + jb y * |deriv (R_eps_two p ε r) y|)
          ≤ jb y ^ γ * ((Cn + Cf) * c * X * jb y ^ (-γ) +
              jb y * (Cf * c * X * jb y ^ (-γ - 1))) := by gcongr
        _ = (Cn + Cf) * c * X * (jb y ^ γ * jb y ^ (-γ)) +
              Cf * c * X * (jb y ^ γ * (jb y * jb y ^ (-γ - 1))) := by ring
        _ ≤ η := by
          rw [hjbγ, e, hη]
          have : 0 ≤ Cn * c * X := by positivity
          nlinarith)
  have hηfin : ENNReal.ofReal η + ENNReal.ofReal η < ⊤ := by simp
  refine ⟨⟨hLip, lt_of_le_of_lt hY hηfin⟩, ?_⟩
  have hη0 : 0 ≤ η := by positivity
  calc yNorm p γ (R_eps_two p ε r) ≤ (ENNReal.ofReal η + ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono hηfin.ne hY
    _ = 2 * η := by rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_ofReal hη0]; ring
    _ ≤ _ := by
      rw [hη]
      have h1 : 2 * (2 * (Cn + Cf) * c * X) ≤ 2 * (2 * (Cn + Cf) * ε * X) := by gcongr
      have : 0 ≤ ε * X := by positivity
      nlinarith


/-- `ℛ_{1,ε} r` is differentiable for differentiable `r` (when `|c_ε| ≤ 1/2`). -/
theorem c08_aux_R1_differentiable (p ε : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    {r : ℝ → ℝ} (hr : Differentiable ℝ r) : Differentiable ℝ (R_eps_one p ε r) := by
  obtain ⟨hφ, hpos, -⟩ := c08_phi_diffeo p (c_eps p ε) hp hp1 (c08_aux_c_eps_bound p ε hp hp1 hε).1
  have hd : Differentiable ℝ (deriv (c08_phi p (c_eps p ε))) :=
    ((contDiff_infty_iff_deriv.1 hφ).2).differentiable (by simp)
  intro y
  unfold R_eps_one phi_eps
  exact (((hd y).rpow_const (Or.inl (hpos y).ne')).sub_const 1).mul (hr y)

/-- `β + 1/p ≥ 1 + 1/p` for `p ≤ 1`, so admissible `γ` satisfy `γ > 1 + 1/p`. -/
theorem c08_aux_admissible_gt (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : admissibleGamma p γ) :
    1 + 1 / p < γ := by
  have : 1 ≤ beta p := by
    unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
  linarith [hγ.1]

/-- Blueprint: lem:linear_conjugation.  The conjugation of the linear operator, items (1)–(5),
for every admissible `γ` (`admissibleGamma p γ`) and `0 ≤ ε ≤ ε_c`:
(1) `𝒰_ε, 𝒱_ε` are `ℝ`-linear bijections of all functions `ℝ → ℝ` (inverses `𝒰_ε⁻¹, 𝒱_ε⁻¹`),
restricting to bijections of `X_γ`, resp. `Y_γ`, all four with norm `≤ C(γ)`;
(2) `‖ℛ_ε r‖_{Y_γ} ≤ C ε ‖r‖_{X_γ}`; (3) `𝒱_ε(ℒ₀(𝒰_ε r)) = ℒ_ε r` pointwise;
(4) `‖(𝒱_ε⁻¹ - I)G‖_{Y_γ} ≤ C ε sup_{y>1}⟨y⟩^γ(|G|+|G'|+|G''|)` for `G ∈ Y_γ ∩ C²((1,∞))`;
(5) `sup_{μ ∈ B̄(μ_*,δ)} ‖(𝒱_ε⁻¹ - I)G_μ‖_{Y_γ} ≤ C ε δ/|μ_*|`. -/
-- The range of `γ` is `admissibleGamma p γ` ("for every admissible γ"); item (2) relies on
-- lem:c08_R2_bound, which is stated for admissible `γ`.
theorem linear_conjugation (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, admissibleGamma p γ → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
        -- (1)
        ((∀ (a : ℝ) (u v : ℝ → ℝ), U_eps p ε (a • u + v) = a • U_eps p ε u + U_eps p ε v) ∧
          (∀ (a : ℝ) (u v : ℝ → ℝ), V_eps p ε (a • u + v) = a • V_eps p ε u + V_eps p ε v) ∧
          Function.LeftInverse (U_eps_inv p ε) (U_eps p ε) ∧
          Function.RightInverse (U_eps_inv p ε) (U_eps p ε) ∧
          Function.LeftInverse (V_eps_inv p ε) (V_eps p ε) ∧
          Function.RightInverse (V_eps_inv p ε) (V_eps p ε) ∧
          Set.BijOn (U_eps p ε) (X_gamma p γ) (X_gamma p γ) ∧
          Set.BijOn (V_eps p ε) (Y_gamma p γ) (Y_gamma p γ) ∧
          Set.MapsTo (U_eps_inv p ε) (X_gamma p γ) (X_gamma p γ) ∧
          Set.MapsTo (V_eps_inv p ε) (Y_gamma p γ) (Y_gamma p γ) ∧
          (∀ r ∈ X_gamma p γ, xNorm p γ (U_eps p ε r) ≤ C * xNorm p γ r ∧
            xNorm p γ (U_eps_inv p ε r) ≤ C * xNorm p γ r) ∧
          (∀ G ∈ Y_gamma p γ, yNorm p γ (V_eps p ε G) ≤ C * yNorm p γ G ∧
            yNorm p γ (V_eps_inv p ε G) ≤ C * yNorm p γ G)) ∧
        -- (2)
        (∀ r ∈ X_gamma p γ, R_eps p ε r ∈ Y_gamma p γ ∧
          yNorm p γ (R_eps p ε r) ≤ C * ε * xNorm p γ r) ∧
        -- (3)
        (∀ r ∈ X_gamma p γ, ∀ y : ℝ, V_eps p ε (L0 p (U_eps p ε r)) y = L_eps p ε r y) ∧
        -- (4)
        (∀ G ∈ Y_gamma p γ, ContDiffOn ℝ 2 G (Ioi 1) →
          BddAbove ((fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1) →
          V_eps_inv p ε G - G ∈ Y_gamma p γ ∧
          yNorm p γ (V_eps_inv p ε G - G) ≤ C * ε *
            sSup ((fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1)) ∧
        -- (5)
        (∀ δ : ℝ, 0 < δ → ∀ μ ∈ Bbar p δ,
          V_eps_inv p ε (G_mu p μ) - G_mu p μ ∈ Y_gamma p γ ∧
          yNorm p γ (V_eps_inv p ε (G_mu p μ) - G_mu p μ) ≤ C * ε * δ / ‖mu_star p‖) := by
  obtain ⟨ε1, hε1, hU⟩ := c08_U_bounded p hp hp1
  obtain ⟨ε2, hε2, hV⟩ := c08_V_bounded p hp hp1
  obtain ⟨ε3, hε3, hR1⟩ := c08_R1_bound p hp hp1
  obtain ⟨ε4, hε4, hR2⟩ := c08_R2_bound p hp hp1
  obtain ⟨ε5, hε5, hCI⟩ := c08_conjugation_identity p hp hp1
  obtain ⟨ε6, hε6, hVI⟩ := c08_V_inverse_minus_identity p hp hp1
  obtain ⟨ε7, hε7, hGmu⟩ := c08_V_inverse_G_mu p hp hp1
  refine ⟨min ε1 (min ε2 (min ε3 (min ε4 (min ε5 (min ε6 ε7))))), by positivity, ?_⟩
  intro γ hγ
  have hγ' := c08_aux_admissible_gt p γ hp hp1 hγ
  obtain ⟨CU, hCU, hU⟩ := hU γ
  obtain ⟨CV, hCV, hV⟩ := hV γ
  obtain ⟨C1, hC1, hR1⟩ := hR1 γ
  obtain ⟨C2, hC2, hR2⟩ := hR2 γ hγ
  obtain ⟨C6, hC6, hVI⟩ := hVI γ
  obtain ⟨C7, hC7, hGmu⟩ := hGmu γ
  refine ⟨CU + CV + C1 + C2 + C6 + C7, by positivity, ?_⟩
  intro ε hε0 hε
  have e1 : ε ≤ ε1 := hε.trans (min_le_left _ _)
  have e2 : ε ≤ ε2 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e3 : ε ≤ ε3 := hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e4 : ε ≤ ε4 := hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have e5 : ε ≤ ε5 := hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have e6 : ε ≤ ε6 := hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))))
  have e7 : ε ≤ ε7 := hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))))
  obtain ⟨hUbij, hUr⟩ := hU ε hε0 e1
  obtain ⟨hVbij, hVG⟩ := hV ε hε0 e2
  obtain ⟨hl, hr, hd1, hd2⟩ := c08_aux_phi_inverse p (c_eps p ε) hp hp1
    (c08_aux_c_eps_bound p ε hp hp1 hε0).1
  obtain ⟨-, hφpos, -⟩ := c08_phi_diffeo p (c_eps p ε) hp hp1 (c08_aux_c_eps_bound p ε hp hp1 hε0).1
  have hψpos : ∀ y, 0 < deriv (c08_phi_inv p (c_eps p ε)) y := by
    intro y
    have h := hd1 y
    have := hφpos (c08_phi_inv p (c_eps p ε) y)
    by_contra hneg
    have hneg := not_lt.1 hneg
    nlinarith
  have hCsum : CU ≤ CU + CV + C1 + C2 + C6 + C7 ∧ CV ≤ CU + CV + C1 + C2 + C6 + C7 ∧
      C1 + C2 ≤ CU + CV + C1 + C2 + C6 + C7 ∧ C6 ≤ CU + CV + C1 + C2 + C6 + C7 ∧
      C7 ≤ CU + CV + C1 + C2 + C6 + C7 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hUbij, hVbij, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a u v; ext y; simp [U_eps]
  · intro a u v; ext y; simp only [V_eps, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · intro u; ext y; simp only [U_eps_inv, U_eps]; exact congrArg u (hl y)
  · intro u; ext y; simp only [U_eps_inv, U_eps]; exact congrArg u (hr y)
  · intro u; ext y
    simp only [V_eps_inv, V_eps]
    have h1 : c08_phi p (c_eps p ε) (c08_phi_inv p (c_eps p ε) y) = y := hr y
    unfold phi_eps psi_eps
    rw [h1, ← mul_assoc, ← Real.mul_rpow (hψpos y).le (hφpos _).le, mul_comm (deriv _ y), hd1 y,
      Real.one_rpow, one_mul]
  · intro u; ext y
    simp only [V_eps_inv, V_eps]
    have h1 : c08_phi_inv p (c_eps p ε) (c08_phi p (c_eps p ε) y) = y := hl y
    unfold phi_eps psi_eps
    rw [h1, ← mul_assoc, ← Real.mul_rpow (hφpos y).le (hψpos _).le, mul_comm (deriv _ y), hd2 y,
      Real.one_rpow, one_mul]
  · intro r hr; exact (hUr r hr).2.1
  · intro G hG; exact (hVG G hG).2.1
  · intro r hr
    obtain ⟨-, -, hn⟩ := hUr r hr
    have h0 : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg
    have a0 : 0 ≤ xNorm p γ (U_eps p ε r) := ENNReal.toReal_nonneg
    have b0 : 0 ≤ xNorm p γ (U_eps_inv p ε r) := ENNReal.toReal_nonneg
    constructor <;> nlinarith [hCsum.1]
  · intro G hG
    obtain ⟨-, -, hn⟩ := hVG G hG
    have h0 : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    have a0 : 0 ≤ yNorm p γ (V_eps p ε G) := ENNReal.toReal_nonneg
    have b0 : 0 ≤ yNorm p γ (V_eps_inv p ε G) := ENNReal.toReal_nonneg
    constructor <;> nlinarith [hCsum.2.1]
  · intro r hr
    obtain ⟨h1m, h1n⟩ := hR1 ε hε0 e3 r hr
    obtain ⟨h2m, h2n⟩ := hR2 ε hε0 e4 r hr
    have hsum := c08_aux_Y_add h1m h2m (c08_aux_R1_differentiable p ε hp hp1 hε0
      (hr.1.1.differentiable (by norm_num)))
    have heq : R_eps p ε r = R_eps_one p ε r + R_eps_two p ε r := rfl
    rw [heq]
    refine ⟨hsum.1, hsum.2.trans ?_⟩
    have h0 : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg
    have := hCsum.2.2.1
    have : (C1 + C2) * ε * xNorm p γ r ≤ (CU + CV + C1 + C2 + C6 + C7) * ε * xNorm p γ r := by
      apply mul_le_mul_of_nonneg_right _ h0
      exact mul_le_mul_of_nonneg_right this hε0
    nlinarith
  · intro r hr y; exact ((hCI γ hγ' ε hε0 e5 r hr).2 y).2
  · intro G hG hC2' hbdd
    obtain ⟨hm, hn⟩ := hVI ε hε0 e6 G hG hC2' hbdd
    refine ⟨hm, hn.trans ?_⟩
    have hS : 0 ≤ sSup ((fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1) := by
      have hmem : (fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) 2 ∈
          (fun y => jb y ^ γ * (|G y| + |deriv G y| + |deriv (deriv G) y|)) '' Ioi 1 :=
        ⟨2, by norm_num, rfl⟩
      refine le_trans ?_ (le_csSup hbdd hmem)
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos 2) γ
      positivity
    have := hCsum.2.2.2.1
    apply mul_le_mul_of_nonneg_right _ hS
    exact mul_le_mul_of_nonneg_right this hε0
  · intro δ hδ μ hμ
    refine ⟨((hGmu ε hε0 e7).1 μ).1, ((hGmu ε hε0 e7).2 δ hδ μ hμ).trans ?_⟩
    have := hCsum.2.2.2.2
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hδ.le
    exact mul_le_mul_of_nonneg_right this hε0

/-- The shared `fourierT` versus Mathlib's `𝓕`: `f̂(x) = 𝓕 f (x/2π)`. -/
theorem c08_aux_fourierT_eq_fourier (f : ℝ → ℂ) (x : ℝ) : fourierT f x = 𝓕 f (x / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold fourierT
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/-- The shared `invFourierT` versus Mathlib's `𝓕⁻`: `m̌(x) = 𝓕⁻ (m(2π·)) x`. -/
theorem c08_aux_invFourierT_eq (m : ℝ → ℂ) (x : ℝ) :
    invFourierT m x = 𝓕⁻ (fun v => m (2 * π * v)) x := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  unfold invFourierT
  set g : ℝ → ℂ := fun ξ => m ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))
  have hsub := Measure.integral_comp_mul_left g (2 * π)
  rw [abs_inv, abs_of_pos h2π] at hsub
  have e : ∫ ξ, g ξ = ((2 * π : ℝ) : ℂ) * ∫ v, g (2 * π * v) := by
    rw [hsub, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ h2π.ne', Complex.ofReal_one, one_mul]
  show ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, g ξ = _
  rw [e, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast h2π.ne'), one_mul]
  congr 1; ext v
  simp only [g, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- Fourier inversion in the shared convention: if `m` is continuous and integrable and `m̌` is
integrable, then `(m̌)^ = m`. -/
theorem c08_aux_fourierT_invFourierT {m : ℝ → ℂ} (hm : Continuous m) (hmi : Integrable m)
    (hHi : Integrable (invFourierT m)) (ξ : ℝ) : fourierT (invFourierT m) ξ = m ξ := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set g : ℝ → ℂ := fun v => m (2 * π * v) with hg
  have hinv : invFourierT m = 𝓕⁻ g := funext fun x => c08_aux_invFourierT_eq m x
  have hgi : Integrable g := hmi.comp_mul_left' h2π.ne'
  have hFg : 𝓕 g = fun w => invFourierT m (-w) := by
    ext w; rw [hinv, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFgi : Integrable (𝓕 g) := by rw [hFg]; exact hHi.comp_neg
  rw [c08_aux_fourierT_eq_fourier, hinv,
    hgi.fourier_fourierInv_eq hFgi (hm.comp (continuous_const.mul continuous_id)).continuousAt]
  simp only [hg]
  congr 1; field_simp

/-- Rademacher on `ℝ` for complex-valued locally Lipschitz functions. -/
theorem c08_aux_ae_differentiable_C {f : ℝ → ℂ} (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ f x := by
  have hre : LocallyLipschitz (fun x => (f x).re) :=
    (Complex.reCLM.lipschitzWith.locallyLipschitz).comp hf
  have him : LocallyLipschitz (fun x => (f x).im) :=
    (Complex.imCLM.lipschitzWith.locallyLipschitz).comp hf
  filter_upwards [c08_aux_ae_differentiable hre, c08_aux_ae_differentiable him] with x h1 h2
  have e : f = fun x => (((f x).re : ℝ) : ℂ) + (((f x).im : ℝ) : ℂ) * Complex.I := by
    ext1 x; exact (Complex.re_add_im (f x)).symm
  rw [e]
  exact ((h1.hasDerivAt.ofReal_comp).add ((h2.hasDerivAt.ofReal_comp).mul_const _)).differentiableAt

/-- Triangle inequality `‖r - s‖_{X_γ} ≤ ‖r‖_{X_γ} + ‖s‖_{X_γ}` on `W^{2,∞}_loc(ℝ;ℂ)`. -/
theorem c08_aux_X_norm_sub_le (p γ : ℝ) {r s : ℝ → ℂ} (hr : W2inftyLoc r) (hs : W2inftyLoc s) :
    X_gamma_norm p γ (r - s) ≤ X_gamma_norm p γ r + X_gamma_norm p γ s := by
  have hd1 : deriv (r - s) = deriv r - deriv s := by
    ext y
    exact deriv_sub (hr.1.differentiable (by norm_num) y) (hs.1.differentiable (by norm_num) y)
  have hd2 : ∀ᵐ y ∂(volume : Measure ℝ),
      deriv (deriv (r - s)) y = deriv (deriv r) y - deriv (deriv s) y := by
    filter_upwards [c08_aux_ae_differentiable_C hr.2, c08_aux_ae_differentiable_C hs.2] with y h1 h2
    rw [hd1]; exact deriv_sub h1 h2
  have key : ∀ (w1 w2 : ℝ → ℝ) (μ : Measure ℝ), (∀ y, 0 ≤ w1 y) → (∀ y, 0 ≤ w2 y) →
      (∀ y, 0 ≤ jb y ^ γ) → μ ≪ volume →
      essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖(r - s) y‖ + w1 y * ‖deriv (r - s) y‖ +
        w2 y * ‖deriv (deriv (r - s)) y‖))) μ ≤
      essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + w1 y * ‖deriv r y‖ +
        w2 y * ‖deriv (deriv r) y‖))) μ +
      essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖s y‖ + w1 y * ‖deriv s y‖ +
        w2 y * ‖deriv (deriv s) y‖))) μ := by
    intro w1 w2 μ hw1 hw2 hg hμ
    refine le_trans (essSup_mono_ae ?_) (ENNReal.essSup_add_le _ _)
    filter_upwards [hμ.ae_le hd2] with y hy
    simp only [Pi.add_apply]
    rw [← ENNReal.ofReal_add (by have := hw1 y; have := hw2 y; have := hg y; positivity)
      (by have := hw1 y; have := hw2 y; have := hg y; positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hy, hd1, Pi.sub_apply, Pi.sub_apply, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (hg y)
    have a1 := norm_sub_le (r y) (s y)
    have a2 := norm_sub_le (deriv r y) (deriv s y)
    have a3 := norm_sub_le (deriv (deriv r) y) (deriv (deriv s) y)
    have := mul_le_mul_of_nonneg_left a2 (hw1 y)
    have := mul_le_mul_of_nonneg_left a3 (hw2 y)
    nlinarith
  have hg : ∀ y, 0 ≤ jb y ^ γ := fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
  unfold X_gamma_norm
  have k1 := key (fun y => jb y ^ (-1 / p)) (fun y => jb y ^ (-2 / p)) (volume.restrict (Ici 0))
    (fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le)
    (fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le) hg Measure.restrict_le_self.absolutelyContinuous
  have k2 := key (fun y => jb y) (fun y => jb y ^ (2 : ℕ)) (volume.restrict (Iic 0))
    (fun y => (c08_aux_jb_pos y).le) (fun y => by have := c08_aux_jb_pos y; positivity) hg
    Measure.restrict_le_self.absolutelyContinuous
  calc _ ≤ _ := add_le_add k1 k2
    _ = _ := add_add_add_comm _ _ _ _

/-- Continuous functions with finite `X_γ` norm satisfy the pointwise value bound. -/
theorem c08_aux_XC_pointwise {p γ : ℝ} {r : ℝ → ℂ} (hc : Continuous r)
    (hfin : X_gamma_norm p γ r < ⊤) (y : ℝ) : ‖r y‖ ≤ xNorm p γ r * jb y ^ (-γ) := by
  unfold X_gamma_norm at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have hx : xNorm p γ r = _ := ENNReal.toReal_add h1.ne h2.ne
  have hw : Continuous (fun y => xNorm p γ r * jb y ^ (-γ)) := by
    apply continuous_const.mul
    exact (Real.continuous_sqrt.comp (by fun_prop)).rpow_const
      (fun y => Or.inl (c08_aux_jb_pos y).ne')
  refine c08_aux_le_of_ae_halflines (f := fun y => ‖r y‖) hc.norm hw ?_ ?_ y
  · filter_upwards [c08_aux_ae_le_essSup_toReal h1] with y hy
    apply c08_aux_div_weight
    rw [hx]
    have hw0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ).le
    have : jb y ^ γ * ‖r y‖ ≤ jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
        jb y ^ (-2 / p) * ‖deriv (deriv r) y‖) := by
      apply mul_le_mul_of_nonneg_left _ hw0
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-1 / p)
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-2 / p)
      have := norm_nonneg (deriv r y); have := norm_nonneg (deriv (deriv r) y)
      nlinarith
    linarith [ENNReal.toReal_nonneg (a := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ +
      jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0)))]
  · filter_upwards [c08_aux_ae_le_essSup_toReal h2] with y hy
    apply c08_aux_div_weight
    rw [hx]
    have hw0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) γ).le
    have : jb y ^ γ * ‖r y‖ ≤ jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
        jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖) := by
      apply mul_le_mul_of_nonneg_left _ hw0
      have := c08_aux_jb_pos y
      have := norm_nonneg (deriv r y); have := norm_nonneg (deriv (deriv r) y)
      have : 0 ≤ jb y ^ (2:ℕ) := by positivity
      nlinarith
    linarith [ENNReal.toReal_nonneg (a := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ +
      jb y ^ (-1 / p) * ‖deriv r y‖ + jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)))
      (volume.restrict (Ici 0)))]

/-- `L¹` control by the `X_γ` norm (`γ > 1`), for continuous `r` with finite norm. -/
theorem c08_aux_XC_L1 {p γ : ℝ} (hγ : 1 < γ) {r : ℝ → ℂ} (hc : Continuous r)
    (hfin : X_gamma_norm p γ r < ⊤) :
    Integrable r ∧ ∫ y, ‖r y‖ ≤ xNorm p γ r * ∫ y, jb y ^ (-γ) := by
  have hI := c08_aux_jb_rpow_integrable γ hγ
  have hi : Integrable r := (hI.const_mul _).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun y => c08_aux_XC_pointwise hc hfin y)
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi.norm (hI.const_mul _) (fun y => c08_aux_XC_pointwise hc hfin y)

/-- `‖f̂(ξ)‖ ≤ ‖f‖_{L¹}`. -/
theorem c08_aux_norm_fourierT_le_C (f : ℝ → ℂ) (ξ : ℝ) : ‖fourierT f ξ‖ ≤ ∫ x, ‖f x‖ := by
  unfold fourierT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext x
  rw [norm_mul, Complex.norm_exp]; simp

/-- Fourier transform of a finite linear combination of integrable functions. -/
theorem c08_aux_fourierT_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ s, Integrable (F i)) (ξ : ℝ) :
    fourierT (fun y => ∑ i ∈ s, c i * F i y) ξ = ∑ i ∈ s, c i * fourierT (F i) ξ := by
  unfold fourierT
  have hi : ∀ i ∈ s, Integrable (fun x => c i * F i x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) :=
    fun i hi => Integrable.mul_bdd (c := 1) ((hF i hi).const_mul (c i))
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun x => le_of_eq (by rw [Complex.norm_exp]; simp))
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum s hi]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [mul_assoc]; rw [integral_const_mul]

/-- `f̂ - ĝ = (f - g)^` for integrable `f, g`. -/
theorem c08_aux_fourierT_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    fourierT f ξ - fourierT g ξ = fourierT (f - g) ξ := by
  unfold fourierT
  have hb : ∀ h : ℝ → ℂ, Integrable h →
      Integrable (fun x => h x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) := fun h hh =>
    Integrable.mul_bdd (c := 1) hh (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun x => le_of_eq (by rw [Complex.norm_exp]; simp))
  rw [← integral_sub (hb f hf) (hb g hg)]
  congr 1; ext x; simp only [Pi.sub_apply]; ring

/-- Fourier inversion in the shared convention: `(f̂)^∨ = f` for continuous integrable `f` with
integrable `f̂`. -/
theorem c08_aux_invFourierT_fourierT {f : ℝ → ℂ} (hc : Continuous f) (hf : Integrable f)
    (hF : Integrable (fourierT f)) (x : ℝ) : invFourierT (fourierT f) x = f x := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have e : (fun v => fourierT f (2 * π * v)) = 𝓕 f := by
    funext v
    rw [c08_aux_fourierT_eq_fourier, mul_div_cancel_left₀ v (by positivity : (2 * π : ℝ) ≠ 0)]
  have hFi : Integrable (𝓕 f) := by rw [← e]; exact hF.comp_mul_left' h2π.ne'
  rw [c08_aux_invFourierT_eq, e, hc.fourierInv_fourier_eq hf hFi]

/-- The inverse transform of a Hermitian function is real. -/
theorem c08_aux_invFourierT_im {h : ℝ → ℂ} (hh : ∀ ξ, h (-ξ) = (starRingEnd ℂ) (h ξ)) (y : ℝ) :
    (invFourierT h y).im = 0 := by
  apply Complex.conj_eq_iff_im.1
  unfold invFourierT
  rw [map_mul, ← integral_conj]
  have hc : ∀ ξ : ℝ, (starRingEnd ℂ) (h ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) =
      h (-ξ) * Complex.exp (Complex.I * (y : ℂ) * ((-ξ : ℝ) : ℂ)) := by
    intro ξ
    rw [map_mul, ← Complex.exp_conj, hh]
    congr 2
    simp [Complex.conj_ofReal]
  simp_rw [hc]
  rw [integral_neg_eq_self (fun ξ : ℝ => h ξ * Complex.exp (Complex.I * (y : ℂ) * ((ξ : ℝ) : ℂ)))]
  rw [map_inv₀, Complex.conj_ofReal]

/-- `deriv (↑f) = ↑(deriv f)` for real `f`. -/
theorem c08_aux_deriv_ofReal (f : ℝ → ℝ) :
    deriv (fun y => ((f y : ℝ) : ℂ)) = fun y => ((deriv f y : ℝ) : ℂ) := by
  funext y
  by_cases hd : DifferentiableAt ℝ f y
  · exact hd.hasDerivAt.ofReal_comp.deriv
  · have : ¬ DifferentiableAt ℝ (fun y => ((f y : ℝ) : ℂ)) y := fun h => hd (by
      have := (Complex.reCLM.differentiableAt.comp y h)
      simpa [Function.comp_def] using this)
    rw [deriv_zero_of_not_differentiableAt this, deriv_zero_of_not_differentiableAt hd]; simp

/-- `⟨·⟩` is monotone in `|·|`. -/
theorem c08_aux_jb_mono {a b : ℝ} (h : |a| ≤ |b|) : jb a ≤ jb b := by
  unfold jb
  apply Real.sqrt_le_sqrt
  have := sq_le_sq' (by linarith [abs_nonneg a, neg_abs_le a, le_abs_self a]) (h.trans' (le_abs_self a))
  nlinarith [sq_abs a, sq_abs b, mul_self_le_mul_self (abs_nonneg a) h]

/-- FTC for complex-valued locally Lipschitz functions on `ℝ`. -/
theorem c08_aux_ftc_C {w : ℝ → ℂ} (hw : LocallyLipschitz w) (a b : ℝ) :
    ∫ t in a..b, deriv w t = w b - w a := by
  set u : ℝ → ℝ := fun x => (w x).re
  set v : ℝ → ℝ := fun x => (w x).im
  have hu : LocallyLipschitz u := (Complex.reCLM.lipschitzWith.locallyLipschitz).comp hw
  have hv : LocallyLipschitz v := (Complex.imCLM.lipschitzWith.locallyLipschitz).comp hw
  have hac : ∀ f : ℝ → ℝ, LocallyLipschitz f → AbsolutelyContinuousOnInterval f a b := by
    intro f hf
    obtain ⟨K, hK⟩ := (hf.locallyLipschitzOn (s := uIcc a b)).exists_lipschitzOnWith_of_compact
      isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval
  have hae : ∀ᵐ x ∂(volume : Measure ℝ),
      deriv w x = ((deriv u x : ℝ) : ℂ) + Complex.I * ((deriv v x : ℝ) : ℂ) := by
    filter_upwards [c08_aux_ae_differentiable_C hw] with x hx
    have h1 := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv
    have h2 := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv
    have e1 : deriv u x = (deriv w x).re := h1
    have e2 : deriv v x = (deriv w x).im := h2
    rw [e1, e2]; apply Complex.ext <;> simp
  have iu := (hac u hu).intervalIntegrable_deriv
  have iv := (hac v hv).intervalIntegrable_deriv
  rw [intervalIntegral.integral_congr_ae (g := fun x => ((deriv u x : ℝ) : ℂ) +
    Complex.I * ((deriv v x : ℝ) : ℂ)) (by filter_upwards [hae] with x hx _; exact hx)]
  have iu' : IntervalIntegrable (fun x => ((deriv u x : ℝ) : ℂ)) volume a b :=
    ⟨iu.1.ofReal, iu.2.ofReal⟩
  have iv' : IntervalIntegrable (fun x => Complex.I * ((deriv v x : ℝ) : ℂ)) volume a b :=
    IntervalIntegrable.const_mul (⟨iv.1.ofReal, iv.2.ofReal⟩ :
      IntervalIntegrable (fun x => ((deriv v x : ℝ) : ℂ)) volume a b) _
  rw [intervalIntegral.integral_add iu' iv',
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, (hac u hu).integral_deriv_eq_sub,
    (hac v hv).integral_deriv_eq_sub]
  apply Complex.ext <;> simp [u, v]

/-- Lipschitz bound from an a.e. derivative bound on an interval. -/
theorem c08_aux_lip_C {w : ℝ → ℂ} (hw : LocallyLipschitz w) {a b K : ℝ} (hab : a ≤ b)
    (h : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc a b → ‖deriv w t‖ ≤ K) :
    ‖w b - w a‖ ≤ K * (b - a) := by
  rw [← c08_aux_ftc_C hw a b]
  have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b) (C := K)
    (f := deriv w) (by
      filter_upwards [h] with t ht htI
      rw [uIoc_of_le hab] at htI
      exact ht (Ioc_subset_Icc_self htI))
  rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this

theorem c08_aux_jb_add_two (x : ℝ) : jb (|x| + 2) ≤ 3 * jb x := by
  unfold jb
  rw [show (3:ℝ) = Real.sqrt 9 by rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have := sq_abs x
  nlinarith [abs_nonneg x]

theorem c08_aux_rpow_div (h p : ℝ) (hh : h ≠ 0) (hp : 0 < p) :
    |h| / |h| ^ (1 + p) = |h| ^ (-p) := by
  have ha : 0 < |h| := abs_pos.2 hh
  rw [Real.rpow_add ha, Real.rpow_one, Real.rpow_neg ha.le]
  field_simp

/-- Blueprint: lem:c08_frac_shift_majorant.  For locally Lipschitz `w : ℝ → ℂ` with `|w| ≤ M` and
`|w'| ≤ A⟨x⟩^N` a.e.: for `B ≥ 1`, `|x| ≤ B`, `h ≠ 0`,
`|w(x)-w(x-h)|/|h|^{1+p} ≤ A⟨B+1⟩^N|h|^{-p}𝟙_{0<|h|≤1} + 2M|h|^{-1-p}𝟙_{|h|>1}`, the majorant is
integrable in `h`, the integral defining `|D|^p w(x)` converges absolutely for every `x`,
`|D|^p w` is continuous and `||D|^p w(x)| ≤ C_{p,N}(A+M)⟨x⟩^N` with `C_{p,N}` independent of
`A, M, w, x`. -/
theorem c08_frac_shift_majorant (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A M : ℝ), 0 ≤ A → 0 ≤ M → ∀ w : ℝ → ℂ, LocallyLipschitz w →
      (∀ x, ‖w x‖ ≤ M) → (∀ᵐ x, ‖deriv w x‖ ≤ A * jb x ^ N) →
      (∀ B : ℝ, 1 ≤ B → ∀ x h : ℝ, |x| ≤ B → h ≠ 0 →
        ‖w x - w (x - h)‖ / |h| ^ (1 + p) ≤
          (if |h| ≤ 1 then A * jb (B + 1) ^ N * |h| ^ (-p) else 0) +
            (if 1 < |h| then 2 * M * |h| ^ (-1 - p) else 0)) ∧
      (∀ B : ℝ, Integrable (fun h : ℝ =>
          (if |h| ≤ 1 then A * jb (B + 1) ^ N * |h| ^ (-p) else 0) +
            (if 1 < |h| then 2 * M * |h| ^ (-1 - p) else 0))) ∧
      (∀ x : ℝ, Integrable (fun z : ℝ => (w x - w z) / ((|x - z| ^ (p + 1) : ℝ) : ℂ))) ∧
      Continuous (fracDC p w) ∧
      ∀ x : ℝ, ‖fracDC p w x‖ ≤ C * (A + M) * jb x ^ N := by
  have hp1' : 0 < 1 - p := by linarith
  refine ⟨|calpha p| * (2 * 3 ^ N / (1 - p) + 4 / p) + 1, by positivity,
    fun A M hA hM w hw hwM hw' => ?_⟩
  have hwc : Continuous w := hw.continuous
  set maj : ℝ → ℝ → ℝ := fun B h => (if |h| ≤ 1 then A * jb (B + 1) ^ N * |h| ^ (-p) else 0) +
    (if 1 < |h| then 2 * M * |h| ^ (-1 - p) else 0) with hmaj
  have hmaj_psi : ∀ B h, maj B h = c01_aux_psi p (A * jb (B + 1) ^ N) M |h| := by
    intro B h
    simp only [hmaj, c01_aux_psi]
    split_ifs with h1 h2 h2 <;> first | linarith | ring_nf
  have hmaj0 : ∀ B h, 0 ≤ maj B h := by
    intro B h
    simp only [hmaj]
    have : 0 ≤ A * jb (B + 1) ^ N := mul_nonneg hA (Real.rpow_nonneg (c08_aux_jb_pos _).le _)
    split_ifs <;> positivity
  have hmaj_int : ∀ B, Integrable (maj B) ∧
      ∫ h, maj B h = 2 * (A * jb (B + 1) ^ N / (1 - p) + 2 * M / p) := by
    intro B
    obtain ⟨hψi, hψ⟩ := c01_aux_psi_integral p (A * jb (B + 1) ^ N) M hp hp1
    have he : maj B = fun h => c01_aux_psi p (A * jb (B + 1) ^ N) M |h| := funext (hmaj_psi B)
    rw [he]
    exact ⟨c01_aux_integrable_comp_abs hψi, by rw [integral_comp_abs (f := c01_aux_psi p _ M), hψ]⟩
  -- the Lipschitz estimate
  have hlip : ∀ B : ℝ, 1 ≤ B → ∀ x h : ℝ, |x| ≤ B → |h| ≤ 1 →
      ‖w x - w (x - h)‖ ≤ A * jb (B + 1) ^ N * |h| := by
    intro B hB x h hx hh
    have hder : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc (min x (x - h)) (max x (x - h)) →
        ‖deriv w t‖ ≤ A * jb (B + 1) ^ N := by
      filter_upwards [hw'] with t ht htI
      refine ht.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (c08_aux_jb_pos t).le
        (c08_aux_jb_mono ?_) hN) hA)
      rw [abs_of_pos (by linarith : (0:ℝ) < B + 1), abs_le]
      have h1 := abs_le.1 hx; have h2 := abs_le.1 hh
      have l1 : -(B + 1) ≤ min x (x - h) := le_min (by linarith) (by linarith)
      have l2 : max x (x - h) ≤ B + 1 := max_le (by linarith) (by linarith)
      exact ⟨by linarith [htI.1], by linarith [htI.2]⟩
    rcases le_total 0 h with h0 | h0
    · have := c08_aux_lip_C hw (a := x - h) (b := x) (by linarith) (by
        filter_upwards [hder] with t ht htI
        exact ht (by rw [min_eq_right (by linarith), max_eq_left (by linarith)]; exact htI))
      rw [abs_of_nonneg h0]; simpa using this
    · have := c08_aux_lip_C hw (a := x) (b := x - h) (by linarith) (by
        filter_upwards [hder] with t ht htI
        exact ht (by rw [min_eq_left (by linarith), max_eq_right (by linarith)]; exact htI))
      rw [abs_of_nonpos h0, norm_sub_rev]; simpa using this
  have hbound : ∀ B : ℝ, 1 ≤ B → ∀ x h : ℝ, |x| ≤ B → h ≠ 0 →
      ‖w x - w (x - h)‖ / |h| ^ (1 + p) ≤ maj B h := by
    intro B hB x h hx hh
    have ha : 0 < |h| := abs_pos.2 hh
    have hpos : 0 < |h| ^ (1 + p) := Real.rpow_pos_of_pos ha _
    simp only [hmaj]
    by_cases h1 : |h| ≤ 1
    · rw [if_pos h1, if_neg (not_lt.2 h1), add_zero]
      calc ‖w x - w (x - h)‖ / |h| ^ (1 + p) ≤ A * jb (B + 1) ^ N * |h| / |h| ^ (1 + p) :=
            div_le_div_of_nonneg_right (hlip B hB x h hx h1) hpos.le
        _ = A * jb (B + 1) ^ N * |h| ^ (-p) := by
            rw [mul_div_assoc, c08_aux_rpow_div h p hh hp]
    · rw [if_neg h1, if_pos (not_le.1 h1), zero_add]
      have h2 : ‖w x - w (x - h)‖ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hwM x, hwM (x - h)])
      calc ‖w x - w (x - h)‖ / |h| ^ (1 + p) ≤ 2 * M / |h| ^ (1 + p) :=
            div_le_div_of_nonneg_right h2 hpos.le
        _ = 2 * M * |h| ^ (-1 - p) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg ha.le]; ring_nf
  -- integrand in the shifted variable
  set G : ℝ → ℝ → ℂ := fun x h => (w x - w (x - h)) / ((|h| ^ (p + 1) : ℝ) : ℂ) with hG
  have hGn : ∀ B : ℝ, 1 ≤ B → ∀ x h : ℝ, |x| ≤ B → ‖G x h‖ ≤ maj B h := by
    intro B hB x h hx
    rcases eq_or_ne h 0 with h0 | h0
    · simp [hG, h0, hmaj0]
    · simp only [hG, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _)]
      rw [add_comm p 1]; exact hbound B hB x h hx h0
  have hdenc : Continuous (fun h : ℝ => ((|h| ^ (p + 1) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_abs.rpow_const fun _ => Or.inr (by linarith))
  have hGm : ∀ x, AEStronglyMeasurable (G x) volume := fun x =>
    ((continuous_const.sub (hwc.comp (continuous_const.sub continuous_id))).measurable.div
      hdenc.measurable).aestronglyMeasurable
  have hshift : ∀ x, fracDC p w x = (calpha p : ℂ) * ∫ h, G x h := by
    intro x
    unfold fracDC
    congr 1
    rw [← integral_sub_left_eq_self (fun z => (w x - w z) / ((|x - z| ^ (p + 1) : ℝ) : ℂ)) volume x]
    congr 1; funext h; simp only [hG, sub_sub_cancel]
  have hBx : ∀ x : ℝ, 1 ≤ |x| + 1 ∧ |x| ≤ |x| + 1 := fun x => ⟨by linarith [abs_nonneg x], by linarith⟩
  have hGi : ∀ x, Integrable (G x) := fun x =>
    (hmaj_int (|x| + 1)).1.mono' (hGm x) (Eventually.of_forall fun h => hGn _ (hBx x).1 x h (hBx x).2)
  refine ⟨hbound, fun B => (hmaj_int B).1, fun x => ?_, ?_, fun x => ?_⟩
  · have := (hGi x).comp_sub_left x
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [hG, sub_sub_cancel]
  · have hcont : Continuous (fun x => ∫ h, G x h) := by
      rw [continuous_iff_continuousAt]
      intro x0
      set B := |x0| + 2
      have hB : 1 ≤ B := by linarith [abs_nonneg x0]
      refine continuousAt_of_dominated (bound := maj B) (Eventually.of_forall hGm) ?_
        (hmaj_int B).1 (Eventually.of_forall fun h => ?_)
      · filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
        refine Eventually.of_forall fun h => hGn B hB x h ?_
        have := Metric.mem_ball.1 hx
        rw [Real.dist_eq] at this
        have := abs_sub_abs_le_abs_sub x x0
        linarith
      · exact ((hwc.sub (hwc.comp (continuous_id.sub continuous_const))).div_const _).continuousAt
    have : fracDC p w = fun x => (calpha p : ℂ) * ∫ h, G x h := funext hshift
    rw [this]; exact continuous_const.mul hcont
  · rw [hshift, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    set B := |x| + 1
    have hB := hBx x
    have hint : ‖∫ h, G x h‖ ≤ ∫ h, maj B h :=
      norm_integral_le_of_norm_le (hmaj_int B).1 (Eventually.of_forall fun h => hGn B hB.1 x h hB.2)
    rw [(hmaj_int B).2] at hint
    have hj : jb (B + 1) ^ N ≤ 3 ^ N * jb x ^ N := by
      rw [← Real.mul_rpow (by norm_num) (c08_aux_jb_pos x).le]
      refine Real.rpow_le_rpow (c08_aux_jb_pos _).le ?_ hN
      have := c08_aux_jb_add_two x
      simp only [B]; rw [show |x| + 1 + 1 = |x| + 2 by ring]; exact this
    have hj1 : 1 ≤ jb x ^ N := Real.one_le_rpow (c08_aux_one_le_jb x) hN
    have hca := abs_nonneg (calpha p)
    calc |calpha p| * ‖∫ h, G x h‖
        ≤ |calpha p| * (2 * (A * jb (B + 1) ^ N / (1 - p) + 2 * M / p)) :=
          mul_le_mul_of_nonneg_left hint hca
      _ ≤ |calpha p| * (2 * (A * (3 ^ N * jb x ^ N) / (1 - p) + 2 * M * jb x ^ N / p)) := by
          have h2M : 2 * M / p ≤ 2 * M * jb x ^ N / p := by
            apply div_le_div_of_nonneg_right _ hp.le
            exact le_mul_of_one_le_right (by positivity) hj1
          have hA' : A * jb (B + 1) ^ N / (1 - p) ≤ A * (3 ^ N * jb x ^ N) / (1 - p) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj hA) hp1'.le
          gcongr
      _ = |calpha p| * (2 * 3 ^ N / (1 - p) * A + 4 / p * M) * jb x ^ N := by ring
      _ ≤ (|calpha p| * (2 * 3 ^ N / (1 - p) + 4 / p) + 1) * (A + M) * jb x ^ N := by
          apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one hj1)
          have h3 : 0 ≤ 2 * 3 ^ N / (1 - p) := by positivity
          have h4 : 0 ≤ 4 / p := by positivity
          nlinarith [mul_nonneg hca (mul_nonneg h3 hM), mul_nonneg hca (mul_nonneg h4 hA)]

/-- Integral of the radial majorant of lem:c08_frac_shift_majorant. -/
theorem c08_aux_maj_integral (p Λ M : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun h : ℝ => (if |h| ≤ 1 then Λ * |h| ^ (-p) else 0) +
        (if 1 < |h| then 2 * M * |h| ^ (-1 - p) else 0)) ∧
    ∫ h : ℝ, ((if |h| ≤ 1 then Λ * |h| ^ (-p) else 0) +
        (if 1 < |h| then 2 * M * |h| ^ (-1 - p) else 0)) = 2 * (Λ / (1 - p) + 2 * M / p) := by
  obtain ⟨hψi, hψ⟩ := c01_aux_psi_integral p Λ M hp hp1
  have he : (fun h : ℝ => (if |h| ≤ 1 then Λ * |h| ^ (-p) else 0) +
      (if 1 < |h| then 2 * M * |h| ^ (-1 - p) else 0)) = fun h => c01_aux_psi p Λ M |h| := by
    funext h
    simp only [c01_aux_psi]
    split_ifs with h1 h2 h2 <;> first | linarith | ring_nf
  rw [he]
  exact ⟨c01_aux_integrable_comp_abs hψi, by rw [integral_comp_abs (f := c01_aux_psi p Λ M), hψ]⟩

/-- `|D|^p w(x) = c_α ∫ (w(x) - w(x - h))/|h|^{1+p} dh`. -/
theorem c08_aux_fracDC_shift (p : ℝ) (w : ℝ → ℂ) (x : ℝ) :
    fracDC p w x = (calpha p : ℂ) * ∫ h, (w x - w (x - h)) / ((|h| ^ (p + 1) : ℝ) : ℂ) := by
  unfold fracDC
  congr 1
  rw [← integral_sub_left_eq_self (fun z => (w x - w z) / ((|x - z| ^ (p + 1) : ℝ) : ℂ)) volume x]
  congr 1; funext h; simp only [sub_sub_cancel]

/-- `|D|^p w(x) = c_α ∫ (w(x) - w(x + h))/|h|^{1+p} dh`. -/
theorem c08_aux_fracDC_shift' (p : ℝ) (w : ℝ → ℂ) (x : ℝ) :
    fracDC p w x = (calpha p : ℂ) * ∫ h, (w x - w (x + h)) / ((|h| ^ (p + 1) : ℝ) : ℂ) := by
  unfold fracDC
  congr 1
  rw [← integral_add_left_eq_self (fun z => (w x - w z) / ((|x - z| ^ (p + 1) : ℝ) : ℂ)) x]
  congr 1; funext h; simp only [sub_add_cancel_left, abs_neg]

/-- Blueprint: lem:c08_frac_pairing_fubini.  For `w ∈ L¹(ℝ;ℂ)` bounded, locally Lipschitz with
`|w'| ≤ A⟨x⟩^N` a.e., and `φ ∈ 𝒮(ℝ;ℂ)`: the absolute double integral
`∬ |w(x)-w(x-h)||φ(x)|/|h|^{1+p} dx dh` is finite, both pairings converge absolutely and
`∫ (|D|^p w) φ = ∫ w (|D|^p φ)` (no complex conjugation). -/
theorem c08_frac_pairing_fubini (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℂ)
    (hw : Integrable w) (hwb : ∃ M : ℝ, ∀ x, ‖w x‖ ≤ M) (hwl : LocallyLipschitz w)
    (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N) (hw' : ∀ᵐ x, ‖deriv w x‖ ≤ A * jb x ^ N)
    (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun q : ℝ × ℝ => ‖w q.1 - w (q.1 - q.2)‖ * ‖φ q.1‖ / |q.2| ^ (1 + p))
      (volume.prod volume) ∧
    Integrable (fun x => fracDC p w x * φ x) ∧
    Integrable (fun x => w x * fracDC p (⇑φ) x) ∧
    ∫ x, fracDC p w x * φ x = ∫ x, w x * fracDC p (⇑φ) x := by
  obtain ⟨M, hM⟩ := hwb
  have hM0 : 0 ≤ M := (norm_nonneg (w 0)).trans (hM 0)
  have hwc : Continuous w := hwl.continuous
  obtain ⟨C, hC, hmaj⟩ := c08_frac_shift_majorant p hp hp1 N hN
  obtain ⟨hbnd, -, -, hcont, hgrowth⟩ := hmaj A M hA hM0 w hwl hM hw'
  -- data for `φ`
  obtain ⟨Mφ, hMφ⟩ := c08_aux_schwartz_decay φ 0
  obtain ⟨Λφ, hΛφ⟩ := c08_aux_schwartz_decay (SchwartzMap.derivCLM ℝ ℂ φ) 0
  simp only [pow_zero, mul_one] at hMφ hΛφ
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hΛφ0 : 0 ≤ Λφ := (norm_nonneg _).trans (hΛφ 0)
  have hφc : Continuous (⇑φ) := φ.continuous
  have hφl : LocallyLipschitz (⇑φ) := (φ.smooth 1).locallyLipschitz
  have hφd : ∀ᵐ x ∂(volume : Measure ℝ), ‖deriv (⇑φ) x‖ ≤ Λφ * jb x ^ (0 : ℝ) :=
    Eventually.of_forall fun x => by
      rw [Real.rpow_zero, mul_one]
      have := hΛφ x; simpa [SchwartzMap.derivCLM_apply] using this
  obtain ⟨Cφ, -, hφmaj⟩ := c08_frac_shift_majorant p hp hp1 0 le_rfl
  obtain ⟨hφbnd, -, -, hφcont, hφgrowth⟩ := hφmaj Λφ Mφ hΛφ0 hMφ0 (⇑φ) hφl hMφ hφd
  have hφfb : ∀ x, ‖fracDC p (⇑φ) x‖ ≤ Cφ * (Λφ + Mφ) := fun x => by
    have := hφgrowth x; rwa [Real.rpow_zero, mul_one] at this
  -- (ii), (iii)
  have i2 : Integrable (fun x => fracDC p w x * φ x) :=
    (c08_aux_polyBounded_mul_schwartz (fracDC p w) hcont ⟨C * (A + M), N, hgrowth⟩ φ).1
  have i3 : Integrable (fun x => w x * fracDC p (⇑φ) x) :=
    Integrable.mul_bdd hw hφcont.aestronglyMeasurable (Eventually.of_forall hφfb)
  -- the majorants
  set maj : ℝ → ℝ → ℝ → ℝ := fun Λ M' h => (if |h| ≤ 1 then Λ * |h| ^ (-p) else 0) +
    (if 1 < |h| then 2 * M' * |h| ^ (-1 - p) else 0) with hmajdef
  have hmajI : ∀ Λ M', Integrable (maj Λ M') ∧ ∫ h, maj Λ M' h = 2 * (Λ / (1 - p) + 2 * M' / p) :=
    fun Λ M' => c08_aux_maj_integral p Λ M' hp hp1
  have hmaj0 : ∀ Λ M' h, 0 ≤ Λ → 0 ≤ M' → 0 ≤ maj Λ M' h := by
    intro Λ M' h h1 h2; simp only [hmajdef]; split_ifs <;> positivity
  set d : ℝ → ℂ := fun h => ((|h| ^ (p + 1) : ℝ) : ℂ) with hd
  have hdm : Measurable d := Complex.measurable_ofReal.comp
    ((continuous_abs.rpow_const fun _ => Or.inr (by linarith)).measurable)
  -- (i)
  set F : ℝ × ℝ → ℝ := fun q => ‖w q.1 - w (q.1 - q.2)‖ * ‖φ q.1‖ / |q.2| ^ (1 + p) with hF
  have hFm : Measurable F := by
    refine ((((hwc.measurable.comp measurable_fst).sub (hwc.measurable.comp
      (measurable_fst.sub measurable_snd))).norm).mul (hφc.measurable.comp measurable_fst).norm).div ?_
    exact ((continuous_abs.rpow_const fun _ => Or.inr (by linarith)).measurable).comp measurable_snd
  have hFx : ∀ x h, F (x, h) ≤ ‖φ x‖ * maj (A * jb (|x| + 1 + 1) ^ N) M h := by
    intro x h
    rcases eq_or_ne h 0 with h0 | h0
    · simp only [hF, h0, sub_zero, sub_self, norm_zero, zero_mul, zero_div]
      exact mul_nonneg (norm_nonneg _) (hmaj0 _ _ _ (mul_nonneg hA (Real.rpow_nonneg (c08_aux_jb_pos _).le _)) hM0)
    · have := hbnd (|x| + 1) (by linarith [abs_nonneg x]) x h (by linarith) h0
      simp only [hF]
      rw [mul_div_right_comm, mul_comm]
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have hF0 : ∀ x h, 0 ≤ F (x, h) := fun x h => by simp only [hF]; positivity
  set K := 2 * (A * 3 ^ N / (1 - p) + 2 * M / p)
  have hp1' : 0 < 1 - p := by linarith
  have hKint : ∀ x, ∫ h, maj (A * jb (|x| + 1 + 1) ^ N) M h ≤ K * jb x ^ N := by
    intro x
    rw [(hmajI (A * jb (|x| + 1 + 1) ^ N) M).2]
    have hj : jb (|x| + 1 + 1) ^ N ≤ 3 ^ N * jb x ^ N := by
      rw [← Real.mul_rpow (by norm_num) (c08_aux_jb_pos x).le]
      refine Real.rpow_le_rpow (c08_aux_jb_pos _).le ?_ hN
      rw [show |x| + 1 + 1 = |x| + 2 by ring]; exact c08_aux_jb_add_two x
    have hj1 : 1 ≤ jb x ^ N := Real.one_le_rpow (c08_aux_one_le_jb x) hN
    simp only [K]
    have a1 : A * jb (|x| + 1 + 1) ^ N / (1 - p) ≤ A * 3 ^ N / (1 - p) * jb x ^ N := by
      rw [div_mul_eq_mul_div, mul_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hj hA) hp1'.le
    have a2 : 2 * M / p ≤ 2 * M / p * jb x ^ N := le_mul_of_one_le_right (by positivity) hj1
    nlinarith
  have hK0 : 0 ≤ K := by
    simp only [K]
    have : 0 ≤ A * 3 ^ N / (1 - p) := div_nonneg (mul_nonneg hA (by positivity)) hp1'.le
    have : 0 ≤ 2 * M / p := div_nonneg (by positivity) hp.le
    linarith
  have hpbK : Integrable (fun x => K * jb x ^ N * ‖φ x‖) := by
    have hjc : Continuous (fun x => jb x ^ N) := (by unfold jb; fun_prop : Continuous jb).rpow_const
      fun x => Or.inl (c08_aux_jb_pos x).ne'
    have hu : Continuous (fun x => ((K * jb x ^ N : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul hjc)
    have hb : ∀ x, ‖((K * jb x ^ N : ℝ) : ℂ)‖ ≤ K * jb x ^ N := fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hK0 (Real.rpow_nonneg (c08_aux_jb_pos x).le _))]
    have := (c08_aux_polyBounded_mul_schwartz (fun x => ((K * jb x ^ N : ℝ) : ℂ)) hu
      ⟨K, N, hb⟩ φ).1.norm
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hK0 (Real.rpow_nonneg (c08_aux_jb_pos x).le _))]
  have i1 : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · refine (((hmajI (A * jb (|x| + 1 + 1) ^ N) M).1).const_mul ‖φ x‖).mono' (hFm.comp measurable_prodMk_left).aestronglyMeasurable
        (Eventually.of_forall fun h => ?_)
      exact (le_of_eq (Real.norm_of_nonneg (hF0 x h))).trans (hFx x h)
    · refine hpbK.mono' hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have hslice : Integrable (fun h => ‖φ x‖ * maj (A * jb (|x| + 1 + 1) ^ N) M h) :=
        ((hmajI (A * jb (|x| + 1 + 1) ^ N) M).1).const_mul _
      calc ∫ h, ‖F (x, h)‖ ≤ ∫ h, ‖φ x‖ * maj (A * jb (|x| + 1 + 1) ^ N) M h := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hslice
              (Eventually.of_forall fun h => ?_)
            exact (le_of_eq (Real.norm_of_nonneg (hF0 x h))).trans (hFx x h)
        _ = ‖φ x‖ * ∫ h, maj (A * jb (|x| + 1 + 1) ^ N) M h := integral_const_mul _ _
        _ ≤ ‖φ x‖ * (K * jb x ^ N) := mul_le_mul_of_nonneg_left (hKint x) (norm_nonneg _)
        _ = K * jb x ^ N * ‖φ x‖ := by ring
  refine ⟨i1, i2, i3, ?_⟩
  set G1 : ℝ → ℝ → ℂ := fun x h => (w x - w (x - h)) * φ x / d h with hG1
  set G2 : ℝ → ℝ → ℂ := fun x h => w x * (φ x - φ (x + h)) / d h with hG2
  have hdn : ∀ h, ‖d h‖ = |h| ^ (1 + p) := fun h => by
    simp only [hd]; rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg h) _), add_comm]
  have hG1m : Measurable (Function.uncurry G1) := by
    simp only [hG1, Function.uncurry_def]
    exact (((hwc.measurable.comp measurable_fst).sub (hwc.measurable.comp
      (measurable_fst.sub measurable_snd))).mul (hφc.measurable.comp measurable_fst)).div
      (hdm.comp measurable_snd)
  have hG2m : Measurable (Function.uncurry G2) := by
    simp only [hG2, Function.uncurry_def]
    exact ((hwc.measurable.comp measurable_fst).mul ((hφc.measurable.comp measurable_fst).sub
      (hφc.measurable.comp (measurable_fst.add measurable_snd)))).div (hdm.comp measurable_snd)
  have hG1i : Integrable (Function.uncurry G1) (volume.prod volume) := by
    refine i1.mono' hG1m.aestronglyMeasurable (Eventually.of_forall fun q => le_of_eq ?_)
    simp only [Function.uncurry_def, hG1, hF, norm_div, norm_mul, hdn]
  have hG2b : ∀ x h, ‖G2 x h‖ ≤ ‖w x‖ * maj Λφ Mφ h := by
    intro x h
    rcases eq_or_ne h 0 with h0 | h0
    · simp only [hG2, h0, add_zero, sub_self, mul_zero, zero_div, norm_zero]
      exact mul_nonneg (norm_nonneg _) (hmaj0 _ _ _ hΛφ0 hMφ0)
    · have := hφbnd (|x| + 1) (by linarith [abs_nonneg x]) x (-h) (by linarith)
        (neg_ne_zero.2 h0)
      simp only [abs_neg, sub_neg_eq_add, Real.rpow_zero, mul_one] at this
      simp only [hG2, norm_div, norm_mul, hdn]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have hG2i : Integrable (Function.uncurry G2) (volume.prod volume) :=
    (hw.norm.mul_prod (hmajI Λφ Mφ).1).mono' hG2m.aestronglyMeasurable
      (Eventually.of_forall fun q => hG2b q.1 q.2)
  have hφb : ∀ x, ‖φ x‖ ≤ Mφ := hMφ
  have slice : ∀ h, ∫ x, G1 x h = ∫ x, G2 x h := by
    intro h
    simp only [hG1, hG2]
    rw [integral_div, integral_div]
    congr 1
    have a1 : Integrable (fun x => w x * φ x) := Integrable.mul_bdd hw hφc.aestronglyMeasurable
      (Eventually.of_forall hφb)
    have a2 : Integrable (fun x => w (x - h) * φ x) :=
      Integrable.mul_bdd (hw.comp_sub_right h) hφc.aestronglyMeasurable (Eventually.of_forall hφb)
    have a3 : Integrable (fun x => w x * φ (x + h)) :=
      Integrable.mul_bdd hw (hφc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun x => hφb _)
    have e1 : (fun x => (w x - w (x - h)) * φ x) = fun x => w x * φ x - w (x - h) * φ x := by
      funext x; ring
    have e2 : (fun x => w x * (φ x - φ (x + h))) = fun x => w x * φ x - w x * φ (x + h) := by
      funext x; ring
    rw [e1, e2, integral_sub a1 a2, integral_sub a1 a3]
    congr 1
    have := integral_add_right_eq_self (μ := volume) (fun x => w (x - h) * φ x) h
    simp only [add_sub_cancel_right] at this
    exact this.symm
  calc ∫ x, fracDC p w x * φ x = ∫ x, (calpha p : ℂ) * ∫ h, G1 x h := by
        congr 1; funext x
        rw [c08_aux_fracDC_shift, mul_assoc, ← integral_mul_const]
        congr 1; congr 1; funext h; simp only [hG1, hd]; ring
    _ = (calpha p : ℂ) * ∫ x, ∫ h, G1 x h := integral_const_mul _ _
    _ = (calpha p : ℂ) * ∫ h, ∫ x, G1 x h := by rw [integral_integral_swap hG1i]
    _ = (calpha p : ℂ) * ∫ h, ∫ x, G2 x h := by
        congr 1; congr 1; funext h; exact slice h
    _ = (calpha p : ℂ) * ∫ x, ∫ h, G2 x h := by rw [integral_integral_swap hG2i]
    _ = ∫ x, w x * fracDC p (⇑φ) x := by
        rw [← integral_const_mul]
        congr 1; funext x
        rw [c08_aux_fracDC_shift', ← integral_const_mul, ← integral_const_mul,
          ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        simp only [hG2, hd]; ring

/-- `φ̂` (shared convention) as a Schwartz function. -/
theorem c08_aux_fourierT_schwartz (φ : SchwartzMap ℝ ℂ) :
    ∃ ψ : SchwartzMap ℝ ℂ, ∀ x, ψ x = fourierT (⇑φ) x := by
  have h2π : ((2 * π)⁻¹ : ℝ) ≠ 0 := by positivity
  set g : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ h2π)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ g (𝓕 φ), fun x => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.fourier_coe, c08_aux_fourierT_eq_fourier]
  congr 1

/-- Parseval-type Fubini identity for integrable functions. -/
theorem c08_aux_parseval_gen {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, f x * fourierT g x = ∫ ξ, fourierT f ξ * g ξ := by
  set e : ℝ → ℝ → ℂ := fun x ξ => Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) with he
  have hne : ∀ x ξ, ‖e x ξ‖ = 1 := fun x ξ => by
    rw [he]; dsimp only; rw [Complex.norm_exp]; simp
  have hF : Integrable (fun q : ℝ × ℝ => f q.1 * g q.2 * e q.1 q.2) (volume.prod volume) := by
    refine (hf.norm.mul_prod hg.norm).mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact ((hf.aestronglyMeasurable.comp_fst).mul hg.aestronglyMeasurable.comp_snd).mul
        (Continuous.aestronglyMeasurable (by rw [he]; fun_prop))
    · simp only [norm_mul, hne, mul_one]; rfl
  calc ∫ x, f x * fourierT g x = ∫ x, ∫ ξ, f x * g ξ * e x ξ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only; unfold fourierT; rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [he]
        rw [show Complex.I * (ξ : ℂ) * (x : ℂ) = Complex.I * (x : ℂ) * (ξ : ℂ) by ring]; ring
    _ = ∫ ξ, ∫ x, f x * g ξ * e x ξ := integral_integral_swap hF
    _ = ∫ ξ, fourierT f ξ * g ξ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only; unfold fourierT; rw [← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [he]; ring

/-- `|D|^p φ̂ = (|ξ|^p φ)^` for Schwartz `φ` (shared Fourier convention). -/
theorem c08_aux_fracDC_fourierT (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (φ : SchwartzMap ℝ ℂ)
    (x : ℝ) : fracDC p (fourierT (⇑φ)) x = fourierT (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * φ ξ) x := by
  obtain ⟨ψ, hψ⟩ := c08_aux_fourierT_schwartz φ
  have hΨ : fourierT (⇑φ) = ⇑ψ := funext fun x => (hψ x).symm
  set K : ℝ := π / (Real.Gamma (1 + p) * Real.sin (π * p / 2))
  have hK : 0 ≤ K := by
    have hsin : 0 < Real.sin (π * p / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    have := Real.Gamma_pos_of_pos (show 0 < 1 + p by linarith)
    positivity
  have hcK := c01_aux_calpha_mul p hp hp1
  set d : ℝ → ℂ := fun h => ((|h| ^ (p + 1) : ℝ) : ℂ) with hd
  set e : ℝ → ℂ := fun ξ => Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) with he
  have hne : ∀ ξ, ‖e ξ‖ = 1 := fun ξ => by rw [he]; dsimp only; rw [Complex.norm_exp]; simp
  -- integrability of the two shifted difference quotients
  obtain ⟨Mψ, hMψ⟩ := c08_aux_schwartz_decay ψ 0
  obtain ⟨Λψ, hΛψ⟩ := c08_aux_schwartz_decay (SchwartzMap.derivCLM ℝ ℂ ψ) 0
  simp only [pow_zero, mul_one] at hMψ hΛψ
  obtain ⟨Cψ, -, hψmaj⟩ := c08_frac_shift_majorant p hp hp1 0 le_rfl
  obtain ⟨-, -, hψint, -, -⟩ := hψmaj Λψ Mψ ((norm_nonneg _).trans (hΛψ 0))
    ((norm_nonneg _).trans (hMψ 0)) (⇑ψ) ((ψ.smooth 1).locallyLipschitz) hMψ
    (Eventually.of_forall fun y => by
      rw [Real.rpow_zero, mul_one]; simpa [SchwartzMap.derivCLM_apply] using hΛψ y)
  have i1 : Integrable (fun h => (ψ x - ψ (x - h)) / d h) := by
    have := (hψint x).comp_sub_left x
    refine this.congr (Eventually.of_forall fun h => ?_); simp only [hd, sub_sub_cancel]
  have i2 : Integrable (fun h => (ψ x - ψ (x + h)) / d h) := by
    have := (hψint x).comp_add_left x
    refine this.congr (Eventually.of_forall fun h => ?_)
    simp only [hd, sub_add_cancel_left, abs_neg]
  -- second differences on the Fourier side
  have hφi : Integrable (⇑φ) := φ.integrable
  have hsd : ∀ h : ℝ, 2 * ψ x - ψ (x - h) - ψ (x + h) =
      ∫ ξ, φ ξ * e ξ * ((2 * (1 - Real.cos (h * ξ)) : ℝ) : ℂ) := by
    intro h
    simp only [hψ]
    unfold fourierT
    have hb : ∀ c : ℝ, Integrable (fun ξ : ℝ => φ ξ * Complex.exp (-(Complex.I * (ξ : ℂ) * (c : ℂ)))) :=
      fun c => Integrable.mul_bdd (c := 1) hφi (Continuous.aestronglyMeasurable (by fun_prop))
        (Eventually.of_forall fun ξ => le_of_eq (by rw [Complex.norm_exp]; simp))
    have j1 : Integrable (fun ξ : ℝ => 2 * (φ ξ * Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ)))) -
        φ ξ * Complex.exp (-(Complex.I * (ξ : ℂ) * ((x - h : ℝ) : ℂ)))) :=
      ((hb x).const_mul 2).sub (hb (x - h))
    rw [← integral_const_mul, ← integral_sub ((hb x).const_mul 2) (hb (x - h)),
      ← integral_sub j1 (hb (x + h))]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [he]
    have e0 : Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ))) =
        Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) := by ring_nf
    have e1 : Complex.exp (-(Complex.I * (ξ : ℂ) * ((x - h : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) * Complex.exp (((h * ξ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : Complex.exp (-(Complex.I * (ξ : ℂ) * ((x + h : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) * Complex.exp (-((h * ξ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have hcos : Complex.exp (((h * ξ : ℝ) : ℂ) * Complex.I) + Complex.exp (-((h * ξ : ℝ) : ℂ) * Complex.I) =
        2 * ((Real.cos (h * ξ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos, Complex.cos]; ring
    rw [e0, e1, e2]
    push_cast at hcos ⊢
    linear_combination (-(φ ξ * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))))) * hcos
  -- the kernel
  set k : ℝ → ℝ → ℝ := fun h ξ => 2 * (1 - Real.cos (h * ξ)) * |h| ^ (-1 - p)
  have hk0 : ∀ h ξ, 0 ≤ k h ξ := fun h ξ => by
    simp only [k]; have := Real.cos_le_one (h * ξ)
    have := Real.rpow_nonneg (abs_nonneg h) (-1 - p); nlinarith
  have hlib := Lib.integral_one_sub_cos_mul_abs_rpow hp (by linarith)
  have hk_int : ∀ ξ, Integrable (fun h => k h ξ) ∧ ∫ h, k h ξ = 2 * |ξ| ^ p * K := by
    intro ξ
    obtain ⟨hi, hv⟩ := hlib ξ
    refine ⟨?_, ?_⟩
    · exact (hi.const_mul 2).congr (Eventually.of_forall fun h => by simp only [k]; ring)
    · simp only [k]; simp_rw [mul_assoc]; rw [integral_const_mul, hv]
  set F : ℝ → ℝ → ℂ := fun h ξ => φ ξ * e ξ * ((k h ξ : ℝ) : ℂ) with hF
  have hFm : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    simp only [hF, he, k, Function.uncurry_def]
    have := φ.continuous.measurable
    fun_prop
  have hpb : Integrable (fun ξ => ‖φ ξ‖ * (2 * |ξ| ^ p * K)) := by
    have hu : Continuous (fun ξ : ℝ => (((2 * K) * |ξ| ^ p : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul
        (continuous_abs.rpow_const fun _ => Or.inr hp.le))
    have := (c08_aux_polyBounded_mul_schwartz _ hu ⟨2 * K, p, fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg ξ)
        (by unfold jb; exact Real.abs_le_sqrt (by nlinarith [sq_abs ξ])) hp.le) (by positivity)⟩ φ).1.norm
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two, abs_of_nonneg hK,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) p)]; ring
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair, hF]
      exact (hk_int ξ).1.ofReal.const_mul _
    · refine hpb.congr (Eventually.of_forall fun ξ => ?_)
      simp only [Function.uncurry_apply_pair, hF, norm_mul, hne, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hk0 _ ξ)]
      rw [integral_const_mul, (hk_int ξ).2]
  have hsym : ∀ h, (2 * ψ x - ψ (x - h) - ψ (x + h)) / d h = ∫ ξ, F h ξ := by
    intro h
    have hr : (d h)⁻¹ = ((|h| ^ (-1 - p) : ℝ) : ℂ) := by
      rw [show -1 - p = -(p + 1) by ring, Real.rpow_neg (abs_nonneg h)]; simp [hd]
    rw [div_eq_mul_inv, hr, hsd, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF, k]; push_cast; ring
  have h2 : 2 * fracDC p (fourierT (⇑φ)) x = (calpha p : ℂ) * ∫ h, ∫ ξ, F h ξ := by
    rw [two_mul]
    nth_rewrite 1 [hΨ, c08_aux_fracDC_shift]
    rw [hΨ, c08_aux_fracDC_shift', ← mul_add, ← integral_add i1 i2]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only; rw [← hsym]; ring
  rw [integral_integral_swap hFi] at h2
  have h3 : ∫ ξ, ∫ h, F h ξ = ((2 * K : ℝ) : ℂ) * fourierT (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * φ ξ) x := by
    unfold fourierT
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF]
    rw [integral_const_mul, integral_complex_ofReal, (hk_int ξ).2]
    simp only [he]; push_cast; ring
  rw [h3] at h2
  have h1 : (calpha p : ℂ) * ((2 * K : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, show calpha p * (2 * K) = 2 * (calpha p * K) by ring, hcK]; simp
  linear_combination h2 / 2 + (fourierT (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * φ ξ) x / 2) * h1

/-- Blueprint: lem:c08_frac_test_transform.  For `w` as in lem:c08_frac_pairing_fubini and
`φ ∈ 𝒮(ℝ;ℂ)`: `∫ (|D|^p w) φ̂ = ∫ |ξ|^p ŵ(ξ) φ(ξ) dξ`, both integrals absolutely convergent;
i.e. `HasDistFourier (|D|^p w) (|ξ|^p ŵ)`. -/
theorem c08_frac_test_transform (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℂ)
    (hw : Integrable w) (hwb : ∃ M : ℝ, ∀ x, ‖w x‖ ≤ M) (hwl : LocallyLipschitz w)
    (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N) (hw' : ∀ᵐ x, ‖deriv w x‖ ≤ A * jb x ^ N) :
    (∀ φ : SchwartzMap ℝ ℂ,
      Integrable (fun x => fracDC p w x * fourierT (⇑φ) x) ∧
      Integrable (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ * φ ξ) ∧
      ∫ x, fracDC p w x * fourierT (⇑φ) x = ∫ ξ, ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ * φ ξ) ∧
    HasDistFourier (fracDC p w) (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ) := by
  have key : ∀ φ : SchwartzMap ℝ ℂ,
      Integrable (fun x => fracDC p w x * fourierT (⇑φ) x) ∧
      Integrable (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ * φ ξ) ∧
      ∫ x, fracDC p w x * fourierT (⇑φ) x = ∫ ξ, ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ * φ ξ := by
    intro φ
    obtain ⟨ψ, hψ⟩ := c08_aux_fourierT_schwartz φ
    have hΨ : fourierT (⇑φ) = ⇑ψ := funext fun x => (hψ x).symm
    obtain ⟨-, i2, -, heq⟩ := c08_frac_pairing_fubini p hp hp1 w hw hwb hwl A N hA hN hw' ψ
    have hg : Integrable (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * φ ξ) := by
      refine (c08_aux_polyBounded_mul_schwartz (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp (continuous_abs.rpow_const fun _ => Or.inr hp.le))
        ⟨1, p, fun ξ => ?_⟩ φ).1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) p),
        one_mul]
      exact Real.rpow_le_rpow (abs_nonneg ξ)
        (by unfold jb; exact Real.abs_le_sqrt (by nlinarith [sq_abs ξ])) hp.le
    have hFc : Continuous (fourierT w) := c08_aux_fourierT_continuous_of_integrable hw
    have hFb : ∀ ξ, ‖fourierT w ξ‖ ≤ ∫ x, ‖w x‖ := c08_aux_norm_fourierT_le_C w
    have hR : Integrable (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ * φ ξ) :=
      (Integrable.bdd_mul hg hFc.aestronglyMeasurable (Eventually.of_forall hFb)).congr
        (Eventually.of_forall fun ξ => by simp only; ring)
    refine ⟨by rw [hΨ]; exact i2, hR, ?_⟩
    rw [hΨ, heq, ← hΨ]
    simp_rw [c08_aux_fracDC_fourierT p hp hp1 φ]
    rw [c08_aux_parseval_gen hw hg]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only; ring
  exact ⟨key, fun φ => (key φ).2.2⟩

theorem c08_aux_fourierT_add_I {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    fourierT (fun x => f x + Complex.I * g x) ξ = fourierT f ξ + Complex.I * fourierT g ξ := by
  have := c08_aux_fourierT_sum (Finset.univ : Finset (Fin 2)) ![1, Complex.I] ![f, g]
    (fun i _ => by fin_cases i <;> simpa) ξ
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at this
  exact this

/-- Blueprint: lem:c08_fourier_deriv_L1.  For locally Lipschitz `u : ℝ → ℂ` with `u, u' ∈ L¹`
(`u' = deriv u`) and `u → 0` at `±∞`: `(u')^(ξ) = iξ û(ξ)` for every `ξ`, both Fourier integrals
absolutely convergent, `û` continuous and `|û(ξ)| ≤ ‖u‖_{L¹}`. -/
theorem c08_fourier_deriv_L1 (u : ℝ → ℂ) (hu : LocallyLipschitz u) (hui : Integrable u)
    (hdi : Integrable (deriv u)) (htop : Tendsto u atTop (nhds 0))
    (hbot : Tendsto u atBot (nhds 0)) :
    (∀ ξ : ℝ, Integrable (fun x : ℝ => u x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) ∧
      Integrable (fun x : ℝ => deriv u x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) ∧
      fourierT (deriv u) ξ = Complex.I * ξ * fourierT u ξ) ∧
    Continuous (fourierT u) ∧
    ∀ ξ : ℝ, ‖fourierT u ξ‖ ≤ ∫ x, ‖u x‖ := by
  have hexp : ∀ (ξ : ℝ) (h : ℝ → ℂ), Integrable h →
      Integrable (fun x : ℝ => h x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) :=
    fun ξ h hh => Integrable.mul_bdd (c := 1) hh (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun x => le_of_eq (by rw [Complex.norm_exp]; simp))
  refine ⟨fun ξ => ⟨hexp ξ u hui, hexp ξ _ hdi, ?_⟩,
    c08_aux_fourierT_continuous_of_integrable hui, c08_aux_norm_fourierT_le_C u⟩
  set a : ℝ → ℝ := fun x => (u x).re
  set b : ℝ → ℝ := fun x => (u x).im
  have ha : LocallyLipschitz a := (Complex.reCLM.lipschitzWith.locallyLipschitz).comp hu
  have hb : LocallyLipschitz b := (Complex.imCLM.lipschitzWith.locallyLipschitz).comp hu
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), deriv a x = (deriv u x).re ∧ deriv b x = (deriv u x).im := by
    filter_upwards [c08_aux_ae_differentiable_C hu] with x hx
    exact ⟨(Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv,
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt).deriv⟩
  have hai : Integrable (deriv a) :=
    (Complex.reCLM.integrable_comp hdi).congr
      (by filter_upwards [hae] with x hx; simp [hx.1])
  have hbi : Integrable (deriv b) :=
    (Complex.imCLM.integrable_comp hdi).congr
      (by filter_upwards [hae] with x hx; simp [hx.2])
  have hcc : ∀ f : ℝ → ℝ, Tendsto f atTop (nhds 0) → Tendsto f atBot (nhds 0) →
      Tendsto f (cocompact ℝ) (nhds 0) := fun f h1 h2 => by
    rw [cocompact_eq_atBot_atTop]; exact h2.sup h1
  have hla : Tendsto a (cocompact ℝ) (nhds 0) := hcc a
    (by have := (Complex.continuous_re.tendsto 0).comp htop; rwa [Complex.zero_re] at this)
    (by have := (Complex.continuous_re.tendsto 0).comp hbot; rwa [Complex.zero_re] at this)
  have hlb : Tendsto b (cocompact ℝ) (nhds 0) := hcc b
    (by have := (Complex.continuous_im.tendsto 0).comp htop; rwa [Complex.zero_im] at this)
    (by have := (Complex.continuous_im.tendsto 0).comp hbot; rwa [Complex.zero_im] at this)
  have hDa := c08_aux_fourierT_deriv ha (Complex.reCLM.integrable_comp hui) hai hla ξ
  have hDb := c08_aux_fourierT_deriv hb (Complex.imCLM.integrable_comp hui) hbi hlb ξ
  have hu_eq : u = fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ) := by
    funext x; simp only [a, b]; rw [mul_comm]; exact (Complex.re_add_im (u x)).symm
  have hdu : fourierT (deriv u) ξ =
      fourierT (fun x => ((deriv a x : ℝ) : ℂ) + Complex.I * ((deriv b x : ℝ) : ℂ)) ξ := by
    unfold fourierT
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx.1, hx.2]
    congr 1
    apply Complex.ext <;> simp
  have i1 : Integrable (fun x => ((deriv a x : ℝ) : ℂ)) := hai.ofReal
  have i2 : Integrable (fun x => ((deriv b x : ℝ) : ℂ)) := hbi.ofReal
  have i3 : Integrable (fun x => ((a x : ℝ) : ℂ)) := (Complex.reCLM.integrable_comp hui).ofReal
  have i4 : Integrable (fun x => ((b x : ℝ) : ℂ)) := (Complex.imCLM.integrable_comp hui).ofReal
  have e1 := c08_aux_fourierT_add_I i1 i2 ξ
  have e2 := c08_aux_fourierT_add_I i3 i4 ξ
  rw [hdu, e1, hDa, hDb]
  conv_rhs => rw [hu_eq]
  rw [e2]
  ring

/-- For Schwartz `φ`: `(φ')^(x) = i x φ̂(x)`. -/
theorem c08_aux_fourierT_schwartz_deriv (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    fourierT (deriv (⇑φ)) x = Complex.I * x * fourierT (⇑φ) x := by
  have hd : deriv (⇑φ) = ⇑(SchwartzMap.derivCLM ℝ ℂ φ) := by
    funext y; simp [SchwartzMap.derivCLM_apply]
  have hc : Tendsto (⇑φ) (cocompact ℝ) (nhds 0) := φ.tendsto_cocompact
  rw [cocompact_eq_atBot_atTop] at hc
  have h := (c08_fourier_deriv_L1 (⇑φ) ((φ.smooth 1).locallyLipschitz) φ.integrable
    (by rw [hd]; exact (SchwartzMap.derivCLM ℝ ℂ φ).integrable)
    (hc.mono_left le_sup_right) (hc.mono_left le_sup_left)).1 x
  exact h.2.2

/-- Blueprint: lem:c08_drift_test_transform.  For `u` as in lem:c08_fourier_deriv_L1 and
`φ ∈ 𝒮(ℝ;ℂ)`: `∫ -x u'(x) φ̂(x) dx = -∫ ξ û(ξ) φ'(ξ) dξ`, both integrals absolutely convergent
(the distributional transform of `-x u'` is `∂_ξ(ξ û)`). -/
theorem c08_drift_test_transform (u : ℝ → ℂ) (hu : LocallyLipschitz u) (hui : Integrable u)
    (hdi : Integrable (deriv u)) (htop : Tendsto u atTop (nhds 0))
    (hbot : Tendsto u atBot (nhds 0)) (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => -(x : ℂ) * deriv u x * fourierT (⇑φ) x) ∧
    Integrable (fun ξ : ℝ => (ξ : ℂ) * fourierT u ξ * deriv (⇑φ) ξ) ∧
    ∫ x : ℝ, -(x : ℂ) * deriv u x * fourierT (⇑φ) x =
      -∫ ξ : ℝ, (ξ : ℂ) * fourierT u ξ * deriv (⇑φ) ξ := by
  obtain ⟨hF, hFc, hFb⟩ := c08_fourier_deriv_L1 u hu hui hdi htop hbot
  set ψ : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ φ with hψ
  have hψe : ⇑ψ = deriv (⇑φ) := by funext y; simp [hψ, SchwartzMap.derivCLM_apply]
  -- `-x φ̂(x) = i (φ')^(x)`
  have hkey : ∀ x : ℝ, -(x : ℂ) * fourierT (⇑φ) x = Complex.I * fourierT (⇑ψ) x := by
    intro x
    rw [hψe, c08_aux_fourierT_schwartz_deriv]
    linear_combination (-((x : ℂ) * fourierT (⇑φ) x)) * Complex.I_sq
  have hψb : ∀ x, ‖fourierT (⇑ψ) x‖ ≤ ∫ y, ‖ψ y‖ := c08_aux_norm_fourierT_le_C _
  have hψc : Continuous (fourierT (⇑ψ)) := c08_aux_fourierT_continuous_of_integrable ψ.integrable
  have hL : (fun x : ℝ => -(x : ℂ) * deriv u x * fourierT (⇑φ) x) =
      fun x => Complex.I * (deriv u x * fourierT (⇑ψ) x) := by
    funext x
    rw [show -(x : ℂ) * deriv u x * fourierT (⇑φ) x = deriv u x * (-(x : ℂ) * fourierT (⇑φ) x) by
      ring, hkey]; ring
  have hLi : Integrable (fun x => deriv u x * fourierT (⇑ψ) x) :=
    Integrable.mul_bdd hdi hψc.aestronglyMeasurable (Eventually.of_forall hψb)
  -- right side integrability: `û` bounded, `ξ φ'(ξ)` integrable
  have hxφ : Integrable (fun ξ : ℝ => (ξ : ℂ) * deriv (⇑φ) ξ) := by
    have := (c08_aux_polyBounded_mul_schwartz (fun x : ℝ => (x : ℂ)) (by fun_prop)
      ⟨1, 1, fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_one, one_mul, jb]
        exact Real.abs_le_sqrt (by nlinarith)⟩ ψ).1
    rw [← hψe]; exact this
  have hRi : Integrable (fun ξ : ℝ => (ξ : ℂ) * fourierT u ξ * deriv (⇑φ) ξ) := by
    have := Integrable.bdd_mul hxφ hFc.aestronglyMeasurable (Eventually.of_forall hFb)
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only; ring
  refine ⟨hL ▸ hLi.const_mul Complex.I, hRi, ?_⟩
  rw [hL, integral_const_mul, c08_aux_parseval hdi ψ]
  have : ∀ ξ : ℝ, fourierT (deriv u) ξ * ψ ξ = Complex.I * ((ξ : ℂ) * fourierT u ξ * deriv (⇑φ) ξ) := by
    intro ξ; rw [(hF ξ).2.2, hψe]; ring
  simp_rw [this]
  rw [integral_const_mul, ← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-! ## The free operator on the Fourier side -/

/-- Blueprint: lem:c08_frac_kernel_fourier.  For `w ∈ L¹(ℝ;ℂ)` bounded, locally Lipschitz with
`|w'| ≤ A⟨x⟩^N` a.e.: `|D|^p w` is continuous, `≤ C⟨x⟩^N`, with distributional Fourier transform
`|ξ|^p ŵ(ξ)`. -/
theorem c08_frac_kernel_fourier (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (w : ℝ → ℂ)
    (hw : Integrable w) (hwb : ∃ M : ℝ, ∀ x, ‖w x‖ ≤ M) (hwl : LocallyLipschitz w)
    (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N) (hw' : ∀ᵐ x, ‖deriv w x‖ ≤ A * jb x ^ N) :
    Continuous (fracDC p w) ∧
    (∃ C : ℝ, ∀ x, ‖fracDC p w x‖ ≤ C * jb x ^ N) ∧
    HasDistFourier (fracDC p w) (fun ξ => ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ) := by
  obtain ⟨M, hM⟩ := hwb
  have hM0 : 0 ≤ M := (norm_nonneg (w 0)).trans (hM 0)
  obtain ⟨C, -, h⟩ := c08_frac_shift_majorant p (by linarith) hp1 N hN
  obtain ⟨-, -, -, hcont, hbd⟩ := h A M hA hM0 w hwl hM hw'
  exact ⟨hcont, ⟨C * (A + M), hbd⟩,
    (c08_frac_test_transform p (by linarith) hp1 w hw ⟨M, hM⟩ hwl A N hA hN hw').2⟩

/-- `|D|^p` of a real function, as the real part of the complex singular integral. -/
theorem c08_aux_fracD_ofReal (p : ℝ) (g : ℝ → ℝ) (y : ℝ) :
    ((fracD p g y : ℝ) : ℂ) = fracDC p (fun x => (g x : ℂ)) y := by
  unfold fracD fracDC
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  congr 1; funext z; push_cast; ring

theorem c08_aux_L0_polyBounded {p : ℝ} {r : ℝ → ℝ} {Cf Nn X Md : ℝ} (hNn : 0 ≤ Nn) (hX0 : 0 ≤ X)
    (hf : ∀ y, |fracD p (deriv r) y| ≤ Cf * jb y ^ Nn) (hrx : ∀ y, |r y| ≤ X)
    (hMd : ∀ y, |deriv r y| ≤ Md) : IsPolyBounded (L0 p r) := by
  refine ⟨|Cf| + X + |Md|, max Nn 1, fun y => ?_⟩
  have hj1 := c08_aux_one_le_jb y
  have e1 : jb y ^ Nn ≤ jb y ^ max Nn 1 := Real.rpow_le_rpow_of_exponent_le hj1 (le_max_left _ _)
  have e2 : jb y ≤ jb y ^ max Nn 1 := by
    conv_lhs => rw [← Real.rpow_one (jb y)]
    exact Real.rpow_le_rpow_of_exponent_le hj1 (le_max_right _ _)
  have e3 : 1 ≤ jb y ^ max Nn 1 := Real.one_le_rpow hj1 (le_trans zero_le_one (le_max_right _ _))
  have hy : |y| ≤ jb y := by unfold jb; exact Real.abs_le_sqrt (by nlinarith)
  have hJ0 : 0 ≤ jb y ^ Nn := Real.rpow_nonneg (c08_aux_jb_pos y).le _
  rw [Real.norm_eq_abs]
  unfold L0 fracDdy
  have a1 : |fracD p (deriv r) y| ≤ |Cf| * jb y ^ max Nn 1 :=
    (hf y).trans ((mul_le_mul_of_nonneg_right (le_abs_self Cf) hJ0).trans
      (mul_le_mul_of_nonneg_left e1 (abs_nonneg _)))
  have a2 : |r y| ≤ X * jb y ^ max Nn 1 := (hrx y).trans (le_mul_of_one_le_right hX0 e3)
  have a3 : |y| * |deriv r y| ≤ jb y ^ max Nn 1 * |Md| :=
    mul_le_mul (hy.trans e2) ((hMd y).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
  have t1 : |fracD p (deriv r) y + r y - y * deriv r y| ≤
      |fracD p (deriv r) y| + |r y| + |y| * |deriv r y| := by
    have h1 := norm_sub_le (fracD p (deriv r) y + r y) (y * deriv r y)
    have h2 := norm_add_le (fracD p (deriv r) y) (r y)
    simp only [Real.norm_eq_abs, abs_mul] at h1 h2
    linarith
  calc _ ≤ _ := t1
    _ ≤ |Cf| * jb y ^ max Nn 1 + X * jb y ^ max Nn 1 + jb y ^ max Nn 1 * |Md| := by linarith
    _ = (|Cf| + X + |Md|) * jb y ^ max Nn 1 := by ring

/-- Blueprint: lem:c08_L0_fourier.  For `γ > 1 + 1/p`, `r ∈ X_γ`: `r̂` is bounded and continuous,
`ℒ₀ r` is continuous and polynomially bounded, and in `𝒮'`
`(ℒ₀ r)^ = iξ|ξ|^p r̂ + r̂ + ∂_ξ(ξ r̂)` (tested against Schwartz functions). -/
theorem c08_L0_fourier (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 + 1 / p < γ)
    (r : ℝ → ℝ) (hr : r ∈ X_gamma p γ) :
    (∃ M : ℝ, ∀ ξ, ‖fourierT (fun x => (r x : ℂ)) ξ‖ ≤ M) ∧
    Continuous (fourierT (fun x => (r x : ℂ))) ∧
    Continuous (L0 p r) ∧ IsPolyBounded (L0 p r) ∧
    ∀ φ : SchwartzMap ℝ ℂ,
      ∫ x, (L0 p r x : ℂ) * fourierT (⇑φ) x =
        (∫ ξ, (Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * fourierT (fun x => (r x : ℂ)) ξ +
            fourierT (fun x => (r x : ℂ)) ξ) * φ ξ) -
          ∫ ξ : ℝ, (ξ : ℂ) * fourierT (fun x => (r x : ℂ)) ξ * deriv (⇑φ) ξ := by
  have hp0 : 0 < p := by linarith
  have h1p : 0 < 1 / p := by positivity
  obtain ⟨CL, -, hL1⟩ := c08_L1_embedding p γ hp hp1 hγ
  obtain ⟨hri, hdri, -, hdrinf, -, hFd⟩ := hL1.1 r hr
  set u : ℝ → ℂ := fun x => (r x : ℂ) with hu
  set w : ℝ → ℂ := fun x => ((deriv r x : ℝ) : ℂ) with hw
  have hdu : deriv u = w := c08_aux_deriv_ofReal r
  have hdw : deriv w = fun x => ((deriv (deriv r) x : ℝ) : ℂ) := c08_aux_deriv_ofReal (deriv r)
  have hrc : Continuous r := hr.1.1.continuous
  have hdrc : Continuous (deriv r) := hr.1.1.continuous_deriv le_rfl
  obtain ⟨Md, hMd⟩ := c08_aux_bounded_of_memLp_top hdrc hdrinf
  set X := xNorm p γ r
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hui : Integrable u := hri.ofReal
  have hwi : Integrable w := hdri.ofReal
  have hulip : LocallyLipschitz u :=
    (Complex.ofRealCLM.lipschitzWith.locallyLipschitz).comp (hr.1.1.locallyLipschitz)
  have hwlip : LocallyLipschitz w :=
    (Complex.ofRealCLM.lipschitzWith.locallyLipschitz).comp hr.1.2
  have hrb : ∀ y, |r y| ≤ X * jb y ^ (-γ) := c08_aux_X_pointwise hr
  have hγ0 : 0 < γ := by linarith
  have hlim := c08_aux_tendsto_of_bound hγ0 hrb
  rw [cocompact_eq_atBot_atTop] at hlim
  have hutop : Tendsto u atTop (nhds 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp (hlim.mono_left le_sup_right)
    rw [Complex.ofReal_zero] at this; exact this
  have hubot : Tendsto u atBot (nhds 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp (hlim.mono_left le_sup_left)
    rw [Complex.ofReal_zero] at this; exact this
  -- hypotheses for the fractional lemma, applied to `w`
  set Nn : ℝ := max 0 (-γ + 2 / p)
  have hw'b : ∀ᵐ x ∂(volume : Measure ℝ), ‖deriv w x‖ ≤ X * jb x ^ Nn := by
    filter_upwards [c08_aux_X_ae_bound2 hp0 hr] with x hx
    rw [hdw, Complex.norm_real, Real.norm_eq_abs]
    exact hx.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (c08_aux_one_le_jb x) (le_max_right _ _)) hX0)
  have hwb : ∃ M : ℝ, ∀ x, ‖w x‖ ≤ M := ⟨Md, fun x => by
    rw [hw]; dsimp only; rw [Complex.norm_real, Real.norm_eq_abs]; exact hMd x⟩
  obtain ⟨hfc, ⟨Cf, hCf⟩, hfF⟩ := c08_frac_kernel_fourier p hp hp1 w hwi hwb hwlip X Nn hX0
    (le_max_left _ _) hw'b
  have hfT := c08_frac_test_transform p hp0 hp1 w hwi hwb hwlip X Nn hX0 (le_max_left _ _) hw'b
  have hL0eq : ∀ y, (L0 p r y : ℂ) = fracDC p w y + u y + -(y : ℂ) * deriv u y := by
    intro y
    unfold L0 fracDdy
    rw [hdu]
    push_cast
    rw [c08_aux_fracD_ofReal]
    ring
  have hL0re : L0 p r = fun y => (fracDC p w y + u y + -(y : ℂ) * deriv u y).re := by
    funext y; rw [← hL0eq]; simp
  have hFb : ∀ ξ, ‖fourierT u ξ‖ ≤ ∫ x, ‖u x‖ := c08_aux_norm_fourierT_le_C u
  have hFc : Continuous (fourierT u) := c08_aux_fourierT_continuous_of_integrable hui
  refine ⟨⟨_, hFb⟩, hFc, ?_, ?_, fun φ => ?_⟩
  · rw [hL0re, hdu]
    exact Complex.continuous_re.comp ((hfc.add (Complex.continuous_ofReal.comp hrc)).add
      ((Complex.continuous_ofReal.comp continuous_id).neg.mul (Complex.continuous_ofReal.comp hdrc)))
  · refine c08_aux_L0_polyBounded (Cf := Cf) (Nn := Nn) (X := X) (Md := Md) (le_max_left _ _) hX0
      (fun y => ?_) (fun y => ?_) hMd
    · have hf := hCf y
      rw [← c08_aux_fracD_ofReal, Complex.norm_real, Real.norm_eq_abs] at hf
      exact hf
    · exact (hrb y).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by linarith)) hX0) (mul_one X))
  · obtain ⟨i1, i2, e1⟩ := hfT.1 φ
    obtain ⟨j1, j2, e2⟩ := c08_drift_test_transform u hulip hui (hdu ▸ hwi) hutop hubot φ
    have hφb : ∀ x, ‖fourierT (⇑φ) x‖ ≤ ∫ y, ‖φ y‖ := c08_aux_norm_fourierT_le_C _
    have k1 : Integrable (fun x => u x * fourierT (⇑φ) x) :=
      Integrable.mul_bdd hui (c08_aux_fourierT_continuous_of_integrable φ.integrable).aestronglyMeasurable
        (Eventually.of_forall hφb)
    have k2 : Integrable (fun ξ => fourierT u ξ * φ ξ) :=
      Integrable.bdd_mul φ.integrable hFc.aestronglyMeasurable (Eventually.of_forall hFb)
    have hwF : ∀ ξ, fourierT w ξ = Complex.I * ξ * fourierT u ξ := hFd
    calc ∫ x, (L0 p r x : ℂ) * fourierT (⇑φ) x
        = ∫ x, (fracDC p w x * fourierT (⇑φ) x + u x * fourierT (⇑φ) x +
            -(x : ℂ) * deriv u x * fourierT (⇑φ) x) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only; rw [hL0eq]; ring
      _ = (∫ x, fracDC p w x * fourierT (⇑φ) x) + (∫ x, u x * fourierT (⇑φ) x) +
            ∫ x : ℝ, -(x : ℂ) * deriv u x * fourierT (⇑φ) x := by
          have i12 : Integrable (fun x => fracDC p w x * fourierT (⇑φ) x + u x * fourierT (⇑φ) x) :=
            i1.add k1
          rw [integral_add i12 j1, integral_add i1 k1]
      _ = (∫ ξ, ((|ξ| ^ p : ℝ) : ℂ) * fourierT w ξ * φ ξ) + (∫ ξ, fourierT u ξ * φ ξ) -
            ∫ ξ : ℝ, (ξ : ℂ) * fourierT u ξ * deriv (⇑φ) ξ := by
          rw [e1, c08_aux_parseval hui φ, e2]; ring
      _ = _ := by
          rw [← integral_add i2 k2]
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
          simp only; rw [hwF]; ring

/-- Blueprint: lem:c08_free_ode.  Properties of the symbol `m_G` for `γ > 1`, `G ∈ Y_γ`:
(1) the second formula, continuity, `|m_G| ≤ ‖G‖_{L¹}/2`, `m_G(0) = Ĝ(0)/2`; (2) Hermitian;
(3) `C¹` off `0` with `ξ m_G' + (2 + iξ|ξ|^p) m_G = Ĝ`, i.e. `∂_ξ(ξ² e^{iΦ₀} m_G) = ξ e^{iΦ₀} Ĝ`;
(4) `ξ m_G` locally Lipschitz and `∂_ξ(ξ m_G) + m_G + iξ|ξ|^p m_G = Ĝ` a.e. and in `𝒟'`. -/
theorem c08_free_ode (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) :
    -- (1)
    ((∀ ξ : ℝ, ξ ≠ 0 → T_0_symbol p G ξ =
        Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) / (ξ : ℂ) ^ 2 *
          ∫ η in (0 : ℝ)..ξ, (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
            fourierT (fun x => (G x : ℂ)) η) ∧
      Continuous (T_0_symbol p G) ∧
      (∀ ξ : ℝ, ‖T_0_symbol p G ξ‖ ≤ (1 / 2) * ∫ x, |G x|) ∧
      T_0_symbol p G 0 = fourierT (fun x => (G x : ℂ)) 0 / 2) ∧
    -- (2)
    (∀ ξ : ℝ, T_0_symbol p G (-ξ) = (starRingEnd ℂ) (T_0_symbol p G ξ)) ∧
    -- (3)
    (ContDiffOn ℝ 1 (T_0_symbol p G) {0}ᶜ ∧
      ∀ ξ : ℝ, ξ ≠ 0 →
        (ξ : ℂ) * deriv (T_0_symbol p G) ξ +
            (2 + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ)) * T_0_symbol p G ξ =
          fourierT (fun x => (G x : ℂ)) ξ ∧
        HasDerivAt (fun η : ℝ => (η : ℂ) ^ 2 * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
            T_0_symbol p G η)
          ((ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ) ξ) ∧
    -- (4)
    (LocallyLipschitz (fun ξ : ℝ => (ξ : ℂ) * T_0_symbol p G ξ) ∧
      (∀ᵐ ξ, deriv (fun ξ : ℝ => (ξ : ℂ) * T_0_symbol p G ξ) ξ + T_0_symbol p G ξ +
          Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * T_0_symbol p G ξ =
        fourierT (fun x => (G x : ℂ)) ξ) ∧
      ∀ φ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        -(∫ ξ : ℝ, (ξ : ℂ) * T_0_symbol p G ξ * deriv φ ξ) +
            ∫ ξ, (T_0_symbol p G ξ + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * T_0_symbol p G ξ) * φ ξ =
          ∫ ξ, fourierT (fun x => (G x : ℂ)) ξ * φ ξ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hGi, -⟩ := c08_aux_Y_integrable hp0 hγ hG
  set Gh := fourierT (fun x => (G x : ℂ)) with hGh
  have hGhc : Continuous Gh := c08_aux_fourierT_continuous_of_integrable hGi.ofReal
  set A := ∫ x, |G x| with hAdef
  have hGhb : ∀ ξ, ‖Gh ξ‖ ≤ A := c08_aux_norm_fourierT_le G
  have hΦc := c08_aux_Phi0_continuous p hp0.le
  set m := T_0_symbol p G with hmdef
  set Fm : ℝ → ℝ → ℂ := fun ξ t => (t : ℂ) *
    Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) * Gh (t * ξ) with hFm
  have hm_eq : ∀ ξ, m ξ = ∫ t in (0:ℝ)..1, Fm ξ t := fun ξ => rfl
  have hrc : Continuous (fun t : ℝ => t ^ (p + 1)) := Real.continuous_rpow_const (by linarith)
  have hFmc : Continuous (Function.uncurry Fm) := by
    have h1 : Continuous (fun q : ℝ × ℝ => ((1 - q.2 ^ (p + 1)) * Phi0 p q.1 : ℝ)) :=
      ((continuous_const.sub (hrc.comp continuous_snd)).mul (hΦc.comp continuous_fst))
    have h2 : Continuous (fun q : ℝ × ℝ => Gh (q.2 * q.1)) :=
      hGhc.comp (continuous_snd.mul continuous_fst)
    have h3 : Continuous (fun q : ℝ × ℝ => ((q.2 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp continuous_snd
    have h4 : Continuous (fun q : ℝ × ℝ =>
        Complex.exp (-(Complex.I * (((1 - q.2 ^ (p + 1)) * Phi0 p q.1 : ℝ) : ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp h1)).neg)
    exact (h3.mul h4).mul h2
  have hmc : Continuous m := by
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hFmc 0 1
    exact this
  have hexp1 : ∀ x : ℝ, ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
    intro x; rw [Complex.norm_exp]; simp
  have hmb : ∀ ξ, ‖m ξ‖ ≤ (1 / 2) * A := by
    intro ξ
    have hle : ‖∫ t in (0:ℝ)..1, Fm ξ t‖ ≤ ∫ t in (0:ℝ)..1, t * A := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · refine Eventually.of_forall (fun t ht => ?_)
        simp only [hFm]
        rw [norm_mul, norm_mul, hexp1, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ht.1]
        exact mul_le_mul_of_nonneg_left (hGhb _) ht.1.le
      · exact (continuous_id.mul continuous_const).intervalIntegrable 0 1
    rw [hm_eq]
    refine hle.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const, integral_id]; ring_nf
  have hm0 : m 0 = Gh 0 / 2 := by
    rw [hm_eq]
    have : ∀ t : ℝ, Fm 0 t = (t : ℂ) * Gh 0 := by
      intro t; simp [hFm, Phi0]
    simp_rw [this]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_id]
    push_cast; ring_nf
  have hform : ∀ ξ : ℝ, ξ ≠ 0 → m ξ = Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) / (ξ : ℂ) ^ 2 *
      ∫ η in (0 : ℝ)..ξ, (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) * Gh η := by
    intro ξ hξ
    set f : ℝ → ℂ := fun η => (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) * Gh η with hf
    have hsub := intervalIntegral.integral_comp_mul_right (f := f) (a := 0) (b := 1) hξ
    rw [zero_mul, one_mul] at hsub
    have h1 : ∫ η in (0 : ℝ)..ξ, f η = ξ • ∫ t in (0 : ℝ)..1, f (t * ξ) := by
      rw [hsub, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    rw [h1, hm_eq, Complex.real_smul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    simp only [hFm, hf]
    rw [c08_aux_Phi0_scale p t ξ hp0 ht.1]
    have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hξ
    have hexp : Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) *
          Complex.exp (Complex.I * ((t ^ (p + 1) * Phi0 p ξ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring_nf
    rw [hexp]
    push_cast
    field_simp
  have hherm : ∀ ξ : ℝ, m (-ξ) = (starRingEnd ℂ) (m ξ) := by
    intro ξ
    have hpt : ∀ t : ℝ, Fm (-ξ) t = (starRingEnd ℂ) (Fm ξ t) := by
      intro t
      simp only [hFm]
      rw [show t * -ξ = -(t * ξ) by ring, hGh, c08_aux_fourierT_neg_real, ← hGh,
        c08_aux_Phi0_neg, map_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast; ring_nf
    rw [hm_eq, hm_eq]
    simp_rw [hpt]
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_conj]
  refine ⟨⟨hform, hmc, hmb, hm0⟩, hherm, ?_⟩
  -- the primitive
  set f : ℝ → ℂ := fun η => (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) * Gh η with hfdef
  have hfc : Continuous f := by
    simp only [hfdef]
    exact (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hΦc)))).mul hGhc
  set Iq : ℝ → ℂ := fun ξ => ∫ η in (0 : ℝ)..ξ, f η with hIqdef
  have hIq : ∀ ξ, HasDerivAt Iq (f ξ) ξ := fun ξ =>
    intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt
  set E : ℝ → ℂ := fun ξ => Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) with hEdef
  have hEe : ∀ ξ, E ξ * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) = 1 := by
    intro ξ; simp only [hEdef]; rw [← Complex.exp_add]; simp
  -- derivative of `m` off `0`
  have hmd : ∀ ξ : ℝ, ξ ≠ 0 → HasDerivAt m
      ((Gh ξ - (2 + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ)) * m ξ) / ξ) ξ := by
    intro ξ hξ
    have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hξ
    have hloc : (fun η => E η / (η : ℂ) ^ 2 * Iq η) =ᶠ[nhds ξ] m :=
      Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hξ) (fun η hη => (hform η hη).symm)
    have hΦ := (c08_aux_Phi0_hasDerivAt p ξ hp0 hξ).ofReal_comp
    have hE : HasDerivAt E (E ξ * (-(Complex.I * ((|ξ| ^ p : ℝ) : ℂ)))) ξ :=
      ((hΦ.const_mul Complex.I).neg).cexp
    have hq : HasDerivAt (fun η : ℝ => (η : ℂ) ^ 2) (2 * (ξ : ℂ)) ξ := by
      have := (hasDerivAt_pow 2 (ξ : ℂ)).comp_ofReal
      refine this.congr_deriv ?_
      ring_nf
    have hq0 : (ξ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hξc
    have hall := (hE.div hq hq0).mul (hIq ξ)
    refine (hall.congr_of_eventuallyEq hloc.symm).congr_deriv ?_
    have hmξ : m ξ = E ξ / (ξ : ℂ) ^ 2 * Iq ξ := hform ξ hξ
    rw [hmξ]
    have he := hEe ξ
    simp only [hfdef, Pi.div_apply]
    field_simp
    linear_combination ((ξ : ℂ) ^ 2 * Gh ξ) * he
  have hode : ∀ ξ : ℝ, ξ ≠ 0 → (ξ : ℂ) * deriv m ξ +
      (2 + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ)) * m ξ = Gh ξ := by
    intro ξ hξ
    rw [(hmd ξ hξ).deriv]
    have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hξ
    field_simp; ring_nf
  have habsc : Continuous (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr hp0.le))
  refine ⟨⟨?_, fun ξ hξ => ⟨hode ξ hξ, ?_⟩⟩, ?_⟩
  · -- `C¹` off `0`
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_compl_singleton]
    refine ⟨fun ξ hξ => (hmd ξ hξ).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
    rw [contDiffOn_zero]
    have hc : ContinuousOn (fun ξ : ℝ => (Gh ξ - (2 + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ)) * m ξ) / ξ)
        {0}ᶜ := by
      apply ContinuousOn.div (by fun_prop) (Complex.continuous_ofReal.continuousOn)
      intro ξ hξ; exact Complex.ofReal_ne_zero.2 hξ
    exact hc.congr (fun ξ hξ => (hmd ξ hξ).deriv)
  · -- the integrating factor
    have hξ' : ξ ≠ 0 := hξ
    have hloc : Iq =ᶠ[nhds ξ] fun η : ℝ => (η : ℂ) ^ 2 *
        Complex.exp (Complex.I * (Phi0 p η : ℂ)) * m η :=
      Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hξ') (fun η hη => by
        have hη' : η ≠ 0 := hη
        have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hη'
        show Iq η = (η : ℂ) ^ 2 * Complex.exp (Complex.I * (Phi0 p η : ℂ)) * m η
        rw [hform η hη']
        have he := hEe η
        simp only [hEdef] at he ⊢
        field_simp
        linear_combination (-(Iq η)) * he)
    exact (hIq ξ).congr_of_eventuallyEq hloc.symm
  · -- part (4)
    set D : ℝ → ℂ := fun ξ => Gh ξ - m ξ - Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ with hDdef
    have hDc : Continuous D := by simp only [hDdef]; fun_prop
    set P : ℝ → ℂ := fun ξ => (ξ : ℂ) * m ξ with hPdef
    have hPc : Continuous P := Complex.continuous_ofReal.mul hmc
    have hPd0 : ∀ ξ : ℝ, ξ ≠ 0 → HasDerivAt P (D ξ) ξ := by
      intro ξ hξ
      have h1 := ((hasDerivAt_id ξ).ofReal_comp).mul (hmd ξ hξ)
      refine h1.congr_deriv ?_
      have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hξ
      simp only [hDdef, id, Complex.ofReal_one]
      field_simp
      ring_nf
    have hPint : ∀ ξ : ℝ, P ξ = ∫ η in (0 : ℝ)..ξ, D η := by
      intro ξ
      have := integral_eq_of_hasDerivAt_off_countable P D (s := {0}) (Set.countable_singleton 0)
        hPc.continuousOn (fun x hx => hPd0 x hx.2) (hDc.intervalIntegrable 0 ξ)
      rw [this]; simp [hPdef]
    have hPd : ∀ ξ, HasDerivAt P (D ξ) ξ := by
      intro ξ
      have hfun : P = fun ξ => ∫ η in (0 : ℝ)..ξ, D η := funext hPint
      rw [hfun]
      exact intervalIntegral.integral_hasDerivAt_right (hDc.intervalIntegrable _ _)
        (hDc.stronglyMeasurableAtFilter _ _) hDc.continuousAt
    have hderivP : deriv P = D := funext fun ξ => (hPd ξ).deriv
    have hPC : ContDiff ℝ 1 P :=
      contDiff_one_iff_deriv.2 ⟨fun ξ => (hPd ξ).differentiableAt, by rw [hderivP]; exact hDc⟩
    refine ⟨hPC.locallyLipschitz, Eventually.of_forall fun ξ => ?_, ?_⟩
    · show deriv P ξ + m ξ + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ = Gh ξ
      rw [hderivP]; simp only [hDdef]; ring
    · intro φ hφ hφs
      have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
      have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
      have hs1 : HasCompactSupport (deriv φ) := hφs.deriv
      have i1 : Integrable (fun x => P x * deriv φ x) :=
        (hPc.mul hφ'c).integrable_of_hasCompactSupport hs1.mul_left
      have i2 : Integrable (fun x => D x * φ x) :=
        (hDc.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left
      have hPφ : HasCompactSupport (P * φ) := hφs.mul_left
      have hz : Tendsto (P * φ) (cocompact ℝ) (nhds 0) := hPφ.is_zero_at_infty
      have hibp := integral_mul_deriv_eq_deriv_mul (u := P) (v := φ) (u' := D) (v' := deriv φ)
        (fun x _ => hPd x) (fun x _ => (hφd x).hasDerivAt) i1 i2
        (hz.mono_left atBot_le_cocompact) (hz.mono_left atTop_le_cocompact)
      have i3 : Integrable (fun ξ => Gh ξ * φ ξ) :=
        (hGhc.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left
      have i4 : Integrable (fun ξ => (m ξ + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ) * φ ξ) :=
        ((by fun_prop : Continuous (fun ξ : ℝ => m ξ + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ)).mul
          hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left
      have hD : (fun x => D x * φ x) = fun x => Gh x * φ x -
          (m x + Complex.I * x * ((|x| ^ p : ℝ) : ℂ) * m x) * φ x := by
        ext x; simp only [hDdef]; ring
      rw [hD, integral_sub i3 i4] at hibp
      have : ∫ ξ : ℝ, (ξ : ℂ) * T_0_symbol p G ξ * deriv φ ξ = ∫ x, P x * deriv φ x := rfl
      rw [this, hibp]
      ring

/-- Blueprint: lem:c08_free_uniqueness.  If `γ > 1 + 1/p`, `r ∈ X_γ`, `G ∈ Y_γ`, `ℒ₀ r = G`, then
`r̂ = m_G`, i.e. `r = 𝒯₀ G` (and `𝒯₀ G` has distributional Fourier transform `m_G`).  In particular
`ℒ₀` is injective on `X_γ`. -/
theorem c08_free_uniqueness (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 + 1 / p < γ) :
    (∀ r ∈ X_gamma p γ, ∀ G ∈ Y_gamma p γ, (∀ y, L0 p r y = G y) →
      (∀ ξ : ℝ, fourierT (fun x => (r x : ℂ)) ξ = T_0_symbol p G ξ) ∧
      r = T_0 p G ∧ HasDistFourier (fun x => (T_0 p G x : ℂ)) (T_0_symbol p G)) ∧
    ∀ r ∈ X_gamma p γ, (∀ y, L0 p r y = 0) → r = 0 := by
  have hp0 : 0 < p := by linarith
  have hγ1 : 1 < γ := by have : 0 < 1 / p := by positivity
                         linarith
  have main : ∀ r ∈ X_gamma p γ, ∀ G ∈ Y_gamma p γ, (∀ y, L0 p r y = G y) →
      (∀ ξ : ℝ, fourierT (fun x => (r x : ℂ)) ξ = T_0_symbol p G ξ) ∧
      r = T_0 p G ∧ HasDistFourier (fun x => (T_0 p G x : ℂ)) (T_0_symbol p G) := by
    intro r hr G hG hL
    obtain ⟨⟨M, hM⟩, hRc, -, -, hL0F⟩ := c08_L0_fourier p γ hp hp1 hγ r hr
    obtain ⟨⟨-, hmc, hmb, -⟩, -, ⟨hmC1, hode⟩, -⟩ := c08_free_ode p γ hp hp1 hγ1 G hG
    obtain ⟨_, _, hL1r, hL1G⟩ := c08_L1_embedding p γ hp hp1 hγ
    obtain ⟨hri, -⟩ := hL1r r hr
    obtain ⟨hGi, -⟩ := hL1G G hG
    set m := T_0_symbol p G with hmdef
    set R := fourierT (fun x => (r x : ℂ)) with hRdef
    set Gh := fourierT (fun x => (G x : ℂ)) with hGh
    have hGhc : Continuous Gh := c08_aux_fourierT_continuous_of_integrable hGi.ofReal
    have habsc : Continuous (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr hp0.le))
    set E : ℝ → ℂ := fun ξ => Gh ξ - R ξ - Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * R ξ with hEdef
    have hEc : Continuous E := by simp only [hEdef]; fun_prop
    set Q : ℝ → ℂ := fun ξ => (ξ : ℂ) * R ξ with hQdef
    have hQc : Continuous Q := Complex.continuous_ofReal.mul hRc
    -- step 2: the distributional equation for compactly supported test functions
    have hdist : ∀ φ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        ∫ ξ, Q ξ * deriv φ ξ = -∫ ξ, E ξ * φ ξ := by
      intro φ hφ hφs
      set φS : SchwartzMap ℝ ℂ := hφs.toSchwartzMap hφ
      have h1 := hL0F φS
      have hLG : (fun x => ((L0 p r x : ℝ) : ℂ) * fourierT (⇑φS) x) =
          fun x => ((G x : ℝ) : ℂ) * fourierT (⇑φS) x := by
        ext x; rw [hL x]
      rw [hLG, c08_aux_parseval (f := fun x => (G x : ℂ)) hGi.ofReal φS] at h1
      have hcs : ∀ u : ℝ → ℂ, Continuous u → Integrable (fun ξ => u ξ * φ ξ) := fun u hu =>
        (hu.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left
      have i1 := hcs (fun ξ => Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * R ξ + R ξ) (by fun_prop)
      have i2 := hcs Gh hGhc
      have hEsplit : (fun ξ => E ξ * φ ξ) = fun ξ => Gh ξ * φ ξ -
          (Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * R ξ + R ξ) * φ ξ := by
        ext ξ; simp only [hEdef]; ring
      have h1' : ∫ ξ, Gh ξ * φ ξ = (∫ ξ, (Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * R ξ + R ξ) * φ ξ) -
          ∫ ξ : ℝ, (ξ : ℂ) * R ξ * deriv φ ξ := h1
      have hQ : ∫ ξ, Q ξ * deriv φ ξ = ∫ ξ : ℝ, (ξ : ℂ) * R ξ * deriv φ ξ := rfl
      rw [hQ, hEsplit, integral_sub i2 i1, h1']
      ring
    -- step 3: the primitive of `E`
    set Qt : ℝ → ℂ := fun ξ => ∫ η in (0 : ℝ)..ξ, E η with hQtdef
    have hQtd : ∀ ξ, HasDerivAt Qt (E ξ) ξ := fun ξ =>
      intervalIntegral.integral_hasDerivAt_right (hEc.intervalIntegrable _ _)
        (hEc.stronglyMeasurableAtFilter _ _) hEc.continuousAt
    have hQtc : Continuous Qt := continuous_iff_continuousAt.2 fun ξ => (hQtd ξ).continuousAt
    have hdist2 : ∀ φ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        ∫ ξ, Qt ξ * deriv φ ξ = -∫ ξ, E ξ * φ ξ := by
      intro φ hφ hφs
      have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
      have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
      have i1 : Integrable (fun x => Qt x * deriv φ x) :=
        (hQtc.mul hφ'c).integrable_of_hasCompactSupport hφs.deriv.mul_left
      have i2 : Integrable (fun x => E x * φ x) :=
        (hEc.mul hφ.continuous).integrable_of_hasCompactSupport hφs.mul_left
      have hz : Tendsto (Qt * φ) (cocompact ℝ) (nhds 0) :=
        (hφs.mul_left : HasCompactSupport (Qt * φ)).is_zero_at_infty
      have := integral_mul_deriv_eq_deriv_mul (u := Qt) (v := φ) (u' := E) (v' := deriv φ)
        (fun x _ => hQtd x) (fun x _ => (hφd x).hasDerivAt) i1 i2
        (hz.mono_left atBot_le_cocompact) (hz.mono_left atTop_le_cocompact)
      rw [this]; ring
    -- steps 4-5: `Q = Qt`
    set W : ℝ → ℂ := fun ξ => Q ξ - Qt ξ with hWdef
    have hWc : Continuous W := hQc.sub hQtc
    have hW0 : ∀ ξ, W ξ = W 0 := by
      apply c08_aux_duBoisReymond hWc
      intro φ hφ hφs
      set φc : ℝ → ℂ := fun x => (φ x : ℂ) with hφcdef
      have hφcC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φc := Complex.ofRealCLM.contDiff.comp hφ
      have hφcs : HasCompactSupport φc := hφs.comp_left Complex.ofReal_zero
      have hdφc : ∀ x, deriv φc x = ((deriv φ x : ℝ) : ℂ) := fun x =>
        ((hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
      have hφc'c : Continuous (deriv φc) := hφcC.continuous_deriv (by simp)
      have i1 : Integrable (fun x => Q x * deriv φc x) :=
        (hQc.mul hφc'c).integrable_of_hasCompactSupport hφcs.deriv.mul_left
      have i2 : Integrable (fun x => Qt x * deriv φc x) :=
        (hQtc.mul hφc'c).integrable_of_hasCompactSupport hφcs.deriv.mul_left
      have e : (fun x => W x * ((deriv φ x : ℝ) : ℂ)) = fun x => Q x * deriv φc x - Qt x * deriv φc x := by
        ext x; rw [hdφc]; simp only [hWdef]; ring
      rw [e, integral_sub i1 i2, hdist φc hφcC hφcs, hdist2 φc hφcC hφcs, sub_self]
    have hQQ : ∀ ξ, Q ξ = Qt ξ := by
      intro ξ
      have h := hW0 ξ
      have h0 : W 0 = 0 := by simp [hWdef, hQdef, hQtdef]
      rw [h0] at h
      simp only [hWdef, sub_eq_zero] at h
      exact h
    -- step 6: derivative of `R` off `0`
    have hRd : ∀ ξ : ℝ, ξ ≠ 0 → HasDerivAt R ((E ξ - R ξ) / ξ) ξ := by
      intro ξ hξ
      have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hξ
      have hloc : (fun η : ℝ => Qt η / (η : ℂ)) =ᶠ[nhds ξ] R :=
        Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hξ) (fun η hη => by
          have hη' : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hη
          show Qt η / (η : ℂ) = R η
          rw [← hQQ η]; simp only [hQdef]; field_simp)
      have h1 := (hQtd ξ).div ((hasDerivAt_id ξ).ofReal_comp) hξc
      refine (h1.congr_of_eventuallyEq hloc.symm).congr_deriv ?_
      rw [← hQQ ξ]; simp only [hQdef, id, Complex.ofReal_one]
      field_simp
    have hmd : ∀ ξ : ℝ, ξ ≠ 0 → HasDerivAt m
        ((Gh ξ - (2 + Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ)) * m ξ) / ξ) ξ := by
      intro ξ hξ
      have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hξ
      have h1 : HasDerivAt m (deriv m ξ) ξ :=
        ((hmC1.differentiableOn (by norm_num)) ξ hξ).differentiableAt
          (isOpen_compl_singleton.mem_nhds hξ) |>.hasDerivAt
      refine h1.congr_deriv ?_
      have := (hode ξ hξ).1
      field_simp
      linear_combination this
    -- step 7: `Z = ξ² e^{iΦ} (R - m)` is constant `0` on each half-line
    have hΦc := c08_aux_Phi0_continuous p hp0.le
    set Z : ℝ → ℂ := fun ξ => (ξ : ℂ) ^ 2 * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * (R ξ - m ξ)
      with hZdef
    have hZd : ∀ ξ : ℝ, ξ ≠ 0 → HasDerivAt Z 0 ξ := by
      intro ξ hξ
      have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hξ
      have hΦ := (c08_aux_Phi0_hasDerivAt p ξ hp0 hξ).ofReal_comp
      have he : HasDerivAt (fun η : ℝ => Complex.exp (Complex.I * (Phi0 p η : ℂ)))
          (Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * (Complex.I * ((|ξ| ^ p : ℝ) : ℂ))) ξ :=
        (hΦ.const_mul Complex.I).cexp
      have hq : HasDerivAt (fun η : ℝ => (η : ℂ) ^ 2) (2 * (ξ : ℂ)) ξ := by
        have := (hasDerivAt_pow 2 (ξ : ℂ)).comp_ofReal
        refine this.congr_deriv ?_
        ring
      have h := (hq.mul he).mul ((hRd ξ hξ).sub (hmd ξ hξ))
      refine h.congr_deriv ?_
      simp only [hEdef, Pi.mul_apply, Pi.sub_apply]
      field_simp
      ring
    set Kb : ℝ := M + (1 / 2) * ∫ x, |G x|
    have hZb : ∀ ξ : ℝ, ‖Z ξ‖ ≤ ξ ^ 2 * Kb := by
      intro ξ
      simp only [hZdef]
      rw [norm_mul, norm_mul]
      have e1 : ‖(ξ : ℂ) ^ 2‖ = ξ ^ 2 := by rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have e2 : ‖Complex.exp (Complex.I * (Phi0 p ξ : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
      rw [e1, e2, mul_one]
      have : ‖R ξ - m ξ‖ ≤ Kb := (norm_sub_le _ _).trans (add_le_add (hM ξ) (hmb ξ))
      exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
    have hZconst : ∀ ξ1 ξ2 : ℝ, (0 < ξ1 ∧ 0 < ξ2) ∨ (ξ1 < 0 ∧ ξ2 < 0) → Z ξ1 = Z ξ2 := by
      intro ξ1 ξ2 h
      have hseg : ∀ t ∈ uIcc ξ1 ξ2, t ≠ 0 := by
        intro t ht
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have : 0 < t := by
            rcases le_total ξ1 ξ2 with h' | h'
            · rw [uIcc_of_le h'] at ht; linarith [ht.1]
            · rw [uIcc_of_ge h'] at ht; linarith [ht.1]
          exact this.ne'
        · have : t < 0 := by
            rcases le_total ξ1 ξ2 with h' | h'
            · rw [uIcc_of_le h'] at ht; linarith [ht.2]
            · rw [uIcc_of_ge h'] at ht; linarith [ht.2]
          exact this.ne
      have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Z) (C := 0)
        (fun t ht => (hZd t (hseg t ht)).differentiableAt)
        (fun t ht => by rw [(hZd t (hseg t ht)).deriv, norm_zero]) (convex_uIcc ξ1 ξ2)
        left_mem_uIcc right_mem_uIcc
      rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
      exact this.symm
    have hZ0 : ∀ ξ : ℝ, ξ ≠ 0 → Z ξ = 0 := by
      intro ξ hξ
      rcases lt_or_gt_of_ne hξ with h | h
      · have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Iio 0), ‖Z ξ‖ ≤ ε ^ 2 * Kb := by
          filter_upwards [Ioo_mem_nhdsLT h, self_mem_nhdsWithin] with ε hε hε0
          rw [hZconst ξ ε (Or.inr ⟨h, hε0⟩)]; exact hZb ε
        have ht : Tendsto (fun ε : ℝ => ε ^ 2 * Kb) (nhdsWithin (0:ℝ) (Iio 0)) (nhds 0) := by
          have : Tendsto (fun ε : ℝ => ε ^ 2 * Kb) (nhds 0) (nhds (0 ^ 2 * Kb)) :=
            ((continuous_pow 2).mul continuous_const).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        exact norm_le_zero_iff.1 (ge_of_tendsto ht hev)
      · have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Ioi 0), ‖Z ξ‖ ≤ ε ^ 2 * Kb := by
          filter_upwards [Ioo_mem_nhdsGT h, self_mem_nhdsWithin] with ε hε hε0
          rw [hZconst ξ ε (Or.inl ⟨h, hε0⟩)]; exact hZb ε
        have ht : Tendsto (fun ε : ℝ => ε ^ 2 * Kb) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
          have : Tendsto (fun ε : ℝ => ε ^ 2 * Kb) (nhds 0) (nhds (0 ^ 2 * Kb)) :=
            ((continuous_pow 2).mul continuous_const).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        exact norm_le_zero_iff.1 (ge_of_tendsto ht hev)
    have hRm0 : ∀ ξ : ℝ, ξ ≠ 0 → R ξ = m ξ := by
      intro ξ hξ
      have h := hZ0 ξ hξ
      simp only [hZdef] at h
      have hξc : (ξ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hξ)
      have hexp : Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      rcases mul_eq_zero.1 h with h1 | h1
      · exact absurd h1 (mul_ne_zero hξc hexp)
      · exact sub_eq_zero.1 h1
    have hRm : ∀ ξ, R ξ = m ξ := by
      have hd : Dense ({0}ᶜ : Set ℝ) := dense_compl_singleton 0
      have := Continuous.ext_on hd hRc hmc (fun ξ hξ => hRm0 ξ hξ)
      exact fun ξ => congrFun this ξ
    -- step 8: conclusions
    have hRmf : R = m := funext hRm
    have hrF : HasDistFourier (fun x => (r x : ℂ)) m := by
      intro φ
      rw [c08_aux_parseval (f := fun x => (r x : ℂ)) hri.ofReal φ]
      rw [show fourierT (fun x => (r x : ℂ)) = m from hRmf]
    obtain ⟨hrcont, hrpb⟩ := c08_aux_X_polyBounded hr
    have hT : T_0 p G = r := c08_aux_distFourierInv_eq hrcont hrpb hrF
    exact ⟨hRm, hT.symm, by rw [hT]; exact hrF⟩
  refine ⟨main, fun r hr hL => ?_⟩
  have hes : ∀ S : Set ℝ, essSup (fun _ : ℝ => (0 : ℝ≥0∞)) (volume.restrict S) < ⊤ := fun S =>
    lt_of_le_of_lt (essSup_le_of_ae_le 0 (Eventually.of_forall fun _ => le_rfl)) ENNReal.zero_lt_top
  have hd0 : deriv (0 : ℝ → ℝ) = 0 := by ext x; simp
  have h0Y : (0 : ℝ → ℝ) ∈ Y_gamma p γ := by
    refine ⟨LocallyLipschitz.const 0, ?_⟩
    simp only [Y_gamma_norm, hd0, Pi.zero_apply, norm_zero, mul_zero, add_zero, ENNReal.ofReal_zero]
    exact ENNReal.add_lt_top.2 ⟨hes _, hes _⟩
  have h0X : (0 : ℝ → ℝ) ∈ X_gamma p γ := by
    refine ⟨⟨contDiff_const, by rw [hd0]; exact LocallyLipschitz.const 0⟩, ?_⟩
    simp only [X_gamma_norm, hd0, Pi.zero_apply, norm_zero, mul_zero, add_zero, ENNReal.ofReal_zero]
    exact ENNReal.add_lt_top.2 ⟨hes _, hes _⟩
  have hL00 : ∀ y, L0 p (0 : ℝ → ℝ) y = (0 : ℝ → ℝ) y := by
    intro y; simp [L0, fracDdy, fracD]
  have h1 := (main r hr 0 h0Y (fun y => by rw [hL y]; rfl)).2.1
  have h2 := (main 0 h0X 0 h0Y hL00).2.1
  rw [h1, ← h2]

/-- Blueprint: lem:c08_T0_right_inverse.  If `γ > 1 + 1/p`, `G ∈ Y_γ` and `r ∈ X_γ` has `r̂ = m_G`
(in `𝒮'`), then `ℒ₀ r = G` pointwise (no condition `ℓ(G) = 0`). -/
theorem c08_T0_right_inverse (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 + 1 / p < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (r : ℝ → ℝ) (hr : r ∈ X_gamma p γ)
    (hrG : HasDistFourier (fun x => (r x : ℂ)) (T_0_symbol p G)) :
    ∀ y, L0 p r y = G y := by
  have hp0 : 0 < p := by linarith
  have hγ1 : 1 < γ := by have : 0 < 1 / p := by positivity
                         linarith
  obtain ⟨⟨M, hM⟩, hrc, hL0c, hL0pb, hL0F⟩ := c08_L0_fourier p γ hp hp1 hγ r hr
  obtain ⟨⟨-, hmc, hmb, -⟩, -, ⟨hmC1, hode⟩, -⟩ := c08_free_ode p γ hp hp1 hγ1 G hG
  obtain ⟨_, _, hL1r, hL1G⟩ := c08_L1_embedding p γ hp hp1 hγ
  obtain ⟨hri, -⟩ := hL1r r hr
  obtain ⟨hGi, -⟩ := hL1G G hG
  set m := T_0_symbol p G with hmdef
  set Gh := fourierT (fun x => (G x : ℂ)) with hGh
  have hGhc : Continuous Gh := c08_aux_fourierT_continuous_of_integrable hGi.ofReal
  have hbdd : ∀ {u : ℝ → ℂ} {B : ℝ}, (∀ x, ‖u x‖ ≤ B) → IsPolyBounded u := fun {u B} h =>
    ⟨B, 0, fun x => by rw [Real.rpow_zero, mul_one]; exact h x⟩
  -- (a) `r̂ = m_G`
  have hrm : fourierT (fun x => (r x : ℂ)) = m := by
    have h0 := c08_aux_test_zero (v := fun ξ => fourierT (fun x => (r x : ℂ)) ξ - m ξ)
      (hrc.sub hmc) (by
        intro g
        have i1 := (c08_aux_polyBounded_mul_schwartz _ hrc (hbdd hM) g).1
        have i2 := (c08_aux_polyBounded_mul_schwartz _ hmc (hbdd hmb) g).1
        simp_rw [sub_mul]
        rw [integral_sub i1 i2, ← c08_aux_parseval (f := fun x => (r x : ℂ)) hri.ofReal g, hrG g,
          sub_self])
    ext ξ
    have := congrFun h0 ξ
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact this
  -- (b) `P = ξ m` is `C¹` with derivative `D`
  set D : ℝ → ℂ := fun ξ => Gh ξ - m ξ - Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ with hDdef
  have hDc : Continuous D := by
    have habsc : Continuous (fun ξ : ℝ => ((|ξ| ^ p : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr hp0.le))
    simp only [hDdef]; fun_prop
  set P : ℝ → ℂ := fun ξ => (ξ : ℂ) * m ξ with hPdef
  have hPc : Continuous P := Complex.continuous_ofReal.mul hmc
  have hPd0 : ∀ ξ : ℝ, ξ ≠ 0 → HasDerivAt P (D ξ) ξ := by
    intro ξ hξ
    have hmd : HasDerivAt m (deriv m ξ) ξ :=
      ((hmC1.differentiableOn (by norm_num)) ξ hξ).differentiableAt
        (isOpen_compl_singleton.mem_nhds hξ) |>.hasDerivAt
    have h1 := ((hasDerivAt_id ξ).ofReal_comp).mul hmd
    refine h1.congr_deriv ?_
    have := (hode ξ hξ).1
    simp only [hDdef, id, Complex.ofReal_one]
    linear_combination this
  have hPint : ∀ ξ : ℝ, P ξ = ∫ η in (0 : ℝ)..ξ, D η := by
    intro ξ
    have := integral_eq_of_hasDerivAt_off_countable P D (s := {0}) (Set.countable_singleton 0)
      hPc.continuousOn (fun x hx => hPd0 x hx.2) (hDc.intervalIntegrable 0 ξ)
    rw [this]; simp [hPdef]
  have hPd : ∀ ξ, HasDerivAt P (D ξ) ξ := by
    intro ξ
    have hfun : P = fun ξ => ∫ η in (0 : ℝ)..ξ, D η := funext hPint
    rw [hfun]
    exact intervalIntegral.integral_hasDerivAt_right (hDc.intervalIntegrable _ _)
      (hDc.stronglyMeasurableAtFilter _ _) hDc.continuousAt
  -- polynomial bounds
  set A := ∫ x, |G x|
  have hA0 : 0 ≤ A := integral_nonneg (fun x => abs_nonneg _)
  have hPpb : IsPolyBounded P := by
    refine ⟨A, 1, fun ξ => ?_⟩
    simp only [hPdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
    have h1 : |ξ| ≤ jb ξ := by
      unfold jb; calc |ξ| = Real.sqrt (ξ ^ 2) := (Real.sqrt_sq_eq_abs ξ).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    have h2 := hmb ξ
    nlinarith [abs_nonneg ξ, norm_nonneg (m ξ)]
  have hDpb : IsPolyBounded D := by
    refine ⟨3 * A, p + 1, fun ξ => ?_⟩
    have hj1 := c08_aux_one_le_jb ξ
    have hj : (1:ℝ) ≤ jb ξ ^ (p + 1) := Real.one_le_rpow hj1 (by linarith)
    have habs : |ξ| ^ (p + 1) ≤ jb ξ ^ (p + 1) := by
      apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith)
      unfold jb; calc |ξ| = Real.sqrt (ξ ^ 2) := (Real.sqrt_sq_eq_abs ξ).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
    have hGb := c08_aux_norm_fourierT_le G ξ
    have hmb' := hmb ξ
    simp only [hDdef]
    have e : ‖Complex.I * (ξ : ℂ) * ((|ξ| ^ p : ℝ) : ℂ) * m ξ‖ = |ξ| ^ (p + 1) * ‖m ξ‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        Real.rpow_add_one' (abs_nonneg _) (by linarith)]
      ring
    calc ‖Gh ξ - m ξ - Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ‖
        ≤ ‖Gh ξ‖ + ‖m ξ‖ + ‖Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr; exact norm_sub_le _ _
      _ ≤ A + (1 / 2) * A + jb ξ ^ (p + 1) * ((1 / 2) * A) := by
          rw [e]
          have := mul_le_mul habs hmb' (norm_nonneg _) (by positivity)
          linarith
      _ ≤ 3 * A * jb ξ ^ (p + 1) := by nlinarith
  -- (c) the Fourier-side identity for Schwartz `φ`
  have hid : ∀ φ : SchwartzMap ℝ ℂ,
      (∫ ξ, (Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ + m ξ) * φ ξ) -
        ∫ ξ : ℝ, (ξ : ℂ) * m ξ * deriv (⇑φ) ξ = ∫ ξ, Gh ξ * φ ξ := by
    intro φ
    set φ' : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℝ ℂ φ
    have hφ' : ∀ x, φ' x = deriv (⇑φ) x := fun x => SchwartzMap.derivCLM_apply (𝕜 := ℝ) φ x
    obtain ⟨i1, -⟩ := c08_aux_polyBounded_mul_schwartz P hPc hPpb φ'
    obtain ⟨i2, -⟩ := c08_aux_polyBounded_mul_schwartz D hDc hDpb φ
    obtain ⟨-, hz⟩ := c08_aux_polyBounded_mul_schwartz P hPc hPpb φ
    simp only [hφ'] at i1
    have hibp := integral_mul_deriv_eq_deriv_mul (u := P) (v := ⇑φ) (u' := D) (v' := deriv ⇑φ)
      (fun x _ => hPd x) (fun x _ => (φ.differentiableAt).hasDerivAt) i1 i2
      (hz.mono_left atBot_le_cocompact) (hz.mono_left atTop_le_cocompact)
    have i3 := (c08_aux_polyBounded_mul_schwartz Gh hGhc (hbdd (c08_aux_norm_fourierT_le G)) φ).1
    have hsplit : (fun ξ : ℝ => (Complex.I * ξ * ((|ξ| ^ p : ℝ) : ℂ) * m ξ + m ξ) * φ ξ) =
        fun ξ => Gh ξ * φ ξ - D ξ * φ ξ := by
      ext ξ; simp only [hDdef]; ring
    rw [hsplit, integral_sub i3 i2]
    have : ∫ ξ : ℝ, (ξ : ℂ) * m ξ * deriv (⇑φ) ξ = ∫ x, P x * deriv (⇑φ) x := rfl
    rw [this, hibp]
    ring
  -- (d) conclusion by injectivity of the distributional Fourier transform
  obtain ⟨-, hGpt⟩ := c08_aux_Y_integrable hp0 hγ1 hG
  have hGpb : IsPolyBounded (fun x => (G x : ℂ)) :=
    ⟨yNorm p γ G, -γ, fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hGpt x⟩
  have hGc : Continuous (fun x => (G x : ℂ)) := Complex.continuous_ofReal.comp hG.1.continuous
  have hzero := c08_aux_distFourier_zero (fun x => (L0 p r x : ℂ) - (G x : ℂ))
    ((Complex.continuous_ofReal.comp hL0c).sub hGc) (by
      intro φ
      have hL0pb' : IsPolyBounded (fun x => (L0 p r x : ℂ)) := by
        obtain ⟨C, N, hC⟩ := hL0pb
        exact ⟨C, N, fun x => by rw [Complex.norm_real]; exact hC x⟩
      have i1 : Integrable (fun x => ((L0 p r x : ℝ) : ℂ) * fourierT (⇑φ) x) :=
        c08_aux_polyBounded_mul_fourierT_integrable _ (Complex.continuous_ofReal.comp hL0c) hL0pb' φ
      have i2 : Integrable (fun x => ((G x : ℝ) : ℂ) * fourierT (⇑φ) x) :=
        c08_aux_polyBounded_mul_fourierT_integrable _ hGc hGpb φ
      simp_rw [sub_mul]
      rw [integral_sub i1 i2, hL0F φ, hrm, hid φ,
        c08_aux_parseval (f := fun x => (G x : ℂ)) hGi.ofReal φ, sub_self])
  intro y
  have := congrFun hzero y
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact_mod_cast this

/-! ## The functional `ℓ` -/

/-- Blueprint: lem:c08_ell_kernel (helper).  The truncated kernel
`K_R(y) = -i ∫₀^R e^{i(Φ₀(ξ) - yξ)} dξ`. -/
def c08_ell_kernel_KR (p R y : ℝ) : ℂ :=
  -Complex.I * ∫ ξ in (0 : ℝ)..R, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))

/-- Blueprint: lem:c08_ell_kernel (helper).  The kernel `K(y) = lim_{R→∞} K_R(y)`
(`limUnder`; existence is lem:c08_ell_kernel). -/
def c08_ell_kernel_K (p y : ℝ) : ℂ := limUnder atTop (fun R : ℝ => c08_ell_kernel_KR p R y)

/-- Blueprint: lem:c08_ell_kernel.  `K_R(y) → K(y)` and `sup_{R>0} |K_R(y)| ≤ C ϖ(y)` with
`ϖ(y) = ⟨y⟩^{-1}` (`y ≤ 0`), `ϖ(y) = ⟨y⟩^{(1-p)/(2p)}` (`y ≥ 0`). -/
theorem c08_ell_kernel (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ y : ℝ, Tendsto (fun R : ℝ => c08_ell_kernel_KR p R y) atTop (nhds (c08_ell_kernel_K p y))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ y R : ℝ, 0 < R →
      ‖c08_ell_kernel_KR p R y‖ ≤
        C * (if y ≤ 0 then jb y ^ (-1 : ℝ) else jb y ^ ((1 - p) / (2 * p))) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C, hC, hE⟩ := appendix_stationary p hp0 hp1
  let F : ℝ → ℝ → ℂ := fun y ξ => Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))
  let L : ℝ → ℂ := fun y => (∫ ξ in (0 : ℝ)..1, F y ξ) + c03_tailE p y 1
  let w : ℝ → ℝ := fun y => if y ≤ 0 then jb y ^ (-1 : ℝ) else jb y ^ ((1 - p) / (2 * p))
  have hFc : ∀ y, Continuous (F y) := fun y => c03_aux_tail_cont p y hp0
  have hL : ∀ y, Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, F y ξ) atTop (𝓝 (L y)) :=
    fun y => c03_aux_tail_shift p y hp0 ((hE y).1 1 one_pos)
  have hEb : ∀ y η, 0 < η → ‖c03_tailE p y η‖ ≤ C * w y := by
    intro y η hη
    by_cases hy : y ≤ 0
    · simpa [w, hy, Real.rpow_neg_one] using (hE y).2.1 hy η hη
    · simpa [w, hy] using (hE y).2.2 (le_of_lt (lt_of_not_ge hy)) η hη
  have hLb : ∀ y, ‖L y‖ ≤ C * w y := by
    intro y
    have hbase : Tendsto (fun η : ℝ => (∫ ξ in η..1, F y ξ) + c03_tailE p y 1)
        (𝓝[>] 0) (𝓝 (L y)) := by
      have hc := (intervalIntegral.continuous_primitive (μ := volume) (fun a b => (hFc y).intervalIntegrable a b) 1).neg.add_const
        (c03_tailE p y 1)
      have hh := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa only [Pi.neg_apply, ← intervalIntegral.integral_symm] using hh
    apply le_of_tendsto hbase.norm
    filter_upwards [self_mem_nhdsWithin] with η hη
    have heq := c03_aux_tailE_shift p y hp0 (η := η) (c := 1) hη one_pos
    simpa only [F, ← heq] using hEb y η hη
  constructor
  · intro y
    have ht := (hL y).const_mul (-Complex.I)
    have heq : c08_ell_kernel_K p y = -Complex.I * L y := ht.limUnder_eq
    rw [heq]
    exact ht
  · refine ⟨2 * C, by positivity, fun y R hR => ?_⟩
    have heq : L y = (∫ ξ in (0 : ℝ)..R, F y ξ) + c03_tailE p y R :=
      tendsto_nhds_unique (hL y) (c03_aux_tail_shift p y hp0 ((hE y).1 R hR))
    have hi : (∫ ξ in (0 : ℝ)..R, F y ξ) = L y - c03_tailE p y R := by rw [heq]; ring
    change ‖-Complex.I * (∫ ξ in (0 : ℝ)..R, F y ξ)‖ ≤ 2 * C * w y
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, hi]
    calc
      ‖L y - c03_tailE p y R‖ ≤ ‖L y‖ + ‖c03_tailE p y R‖ := norm_sub_le _ _
      _ ≤ C * w y + C * w y := add_le_add (hLb y) (hEb y R hR)
      _ = 2 * C * w y := by ring

/-- Blueprint: prop:linear_ell_continuity.  For `γ > β + 1/p` and `G ∈ Y_γ`, the limit defining
`ℓ(G)` exists, `ℓ(G) = ∫ G' K` (absolutely convergent), `|ℓ(G)| ≤ C‖G‖_{Y_γ}`; `ℓ` is `ℝ`-linear on
`Y_γ` and `Ỹ_γ` is closed (sequentially, for the `Y_γ`-norm). -/
theorem linear_ell_continuity (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : beta p + 1 / p < γ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ G ∈ Y_gamma p γ,
        Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
            (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ)
          atTop (nhds (ell p G)) ∧
        Integrable (fun y => ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y) ∧
        ell p G = ∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y ∧
        ‖ell p G‖ ≤ C * yNorm p γ G) ∧
      (∀ G ∈ Y_gamma p γ, ∀ H ∈ Y_gamma p γ, ∀ a : ℝ,
        ell p (a • G + H) = (a : ℂ) * ell p G + ell p H) ∧
      ∀ (Gn : ℕ → ℝ → ℝ) (G : ℝ → ℝ), (∀ n, Gn n ∈ Y_gamma_tilde p γ) → G ∈ Y_gamma p γ →
        Tendsto (fun n => yNorm p γ (Gn n - G)) atTop (nhds 0) → G ∈ Y_gamma_tilde p γ := by
  have hp0 : 0 < p := by linarith
  have hβ : 1 ≤ beta p := by unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
  have hγ' : 1 + 1 / p < γ := by linarith
  obtain ⟨hKlim, Ck, hCk, hKb⟩ := c08_ell_kernel p hp hp1
  obtain ⟨_, _, _, hL1G⟩ := c08_L1_embedding p γ hp hp1 hγ'
  set e := (1 - p) / (2 * p) with hedef
  have he0 : 0 ≤ e := by rw [hedef]; apply div_nonneg <;> linarith
  set a := γ - 1 / p - e with hadef
  have ha : 1 < a := by
    have : beta p + 1 / p = 1 + 1 / p + e := by
      rw [hedef]; unfold beta; field_simp; ring
    rw [hadef]; linarith
  set Ia := ∫ y, jb y ^ (-a)
  have hIa := c08_aux_jb_rpow_integrable a ha
  have hIa0 : 0 ≤ Ia := integral_nonneg (fun z => (Real.rpow_pos_of_pos (c08_aux_jb_pos z) _).le)
  -- kernel bounds
  have hϖ : ∀ y : ℝ, (if y ≤ 0 then jb y ^ (-1 : ℝ) else jb y ^ ((1 - p) / (2 * p))) ≤ jb y ^ e := by
    intro y
    split_ifs
    · exact (Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by norm_num)).trans
        (Real.one_le_rpow (c08_aux_one_le_jb y) he0)
    · exact le_rfl
  have hKRb : ∀ y R : ℝ, 0 < R → ‖c08_ell_kernel_KR p R y‖ ≤ Ck * jb y ^ e := fun y R hR =>
    (hKb y R hR).trans (mul_le_mul_of_nonneg_left (hϖ y) hCk.le)
  have hKbd : ∀ y, ‖c08_ell_kernel_K p y‖ ≤ Ck * jb y ^ e := by
    intro y
    refine le_of_tendsto ((hKlim y).norm) ?_
    filter_upwards [eventually_gt_atTop 0] with R hR using hKRb y R hR
  -- continuity of the truncated kernels
  have hKRc : ∀ R : ℝ, Continuous (fun y => c08_ell_kernel_KR p R y) := by
    intro R
    unfold c08_ell_kernel_KR
    have hΦc := c08_aux_Phi0_continuous p hp0.le
    apply continuous_const.mul
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    have : Continuous (fun q : ℝ × ℝ => ((Phi0 p q.2 - q.1 * q.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hΦc.comp continuous_snd).sub
        (continuous_fst.mul continuous_snd))
    exact Complex.continuous_exp.comp (continuous_const.mul this)
  have hKm : AEStronglyMeasurable (c08_ell_kernel_K p) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun R => (hKRc R).aestronglyMeasurable)
      (Eventually.of_forall hKlim)
  -- the core statement
  set seq : (ℝ → ℝ) → ℝ → ℂ := fun G R => ∫ ξ in (0 : ℝ)..R,
    (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ with hseq
  have core : ∀ G ∈ Y_gamma p γ,
      Tendsto (seq G) atTop (nhds (∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y)) ∧
      Integrable (fun y => ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y) ∧
      ‖∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y‖ ≤ Ck * Ia * yNorm p γ G := by
    intro G hG
    obtain ⟨hGi, hG'i, -, -, -, hFG⟩ := hL1G G hG
    have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    have hb := c08_aux_Y_ae_bound hp0 hG
    have hG'm : AEStronglyMeasurable (fun y => ((deriv G y : ℝ) : ℂ)) volume :=
      (Complex.measurable_ofReal.comp (measurable_deriv G)).aestronglyMeasurable
    -- pointwise bound
    have hbound : ∀ᵐ y ∂(volume : Measure ℝ), ∀ k : ℂ, ‖k‖ ≤ Ck * jb y ^ e →
        ‖((deriv G y : ℝ) : ℂ) * k‖ ≤ Ck * yNorm p γ G * jb y ^ (-a) := by
      filter_upwards [hb] with y hy k hk
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hy.2
      have hj := c08_aux_jb_pos y
      calc |deriv G y| * ‖k‖ ≤ (yNorm p γ G * jb y ^ (-γ + 1 / p)) * (Ck * jb y ^ e) :=
            mul_le_mul h1 hk (norm_nonneg _) (by positivity)
        _ = Ck * yNorm p γ G * (jb y ^ (-γ + 1 / p) * jb y ^ e) := by ring
        _ = Ck * yNorm p γ G * jb y ^ (-a) := by
            rw [← Real.rpow_add hj]; congr 2; rw [hadef]; ring
    have hdom : Integrable (fun y => Ck * yNorm p γ G * jb y ^ (-a)) := hIa.const_mul _
    have hint : Integrable (fun y => ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y) :=
      hdom.mono' (hG'm.mul hKm) (by
        filter_upwards [hbound] with y hy using hy _ (hKbd y))
    -- Fubini for `R > 0`
    have hfub : ∀ R : ℝ, 0 < R → seq G R = ∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_KR p R y := by
      intro R hR
      set F : ℝ → ℝ → ℂ := fun ξ y => -Complex.I * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
        (((deriv G y : ℝ) : ℂ) * Complex.exp (-(Complex.I * (y : ℂ) * (ξ : ℂ)))) with hF
      have hΦc := c08_aux_Phi0_continuous p hp0.le
      have hFint : Integrable (Function.uncurry F) ((volume.restrict (Ioc 0 R)).prod volume) := by
        have hprod : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * ‖deriv G z.2‖)
            ((volume.restrict (Ioc 0 R)).prod volume) :=
          (integrable_const (1 : ℝ)).mul_prod hG'i.norm
        refine hprod.mono' ?_ (Eventually.of_forall fun z => ?_)
        · have h1 : Continuous (fun z : ℝ × ℝ => -Complex.I *
              Complex.exp (Complex.I * (Phi0 p z.1 : ℂ))) := by
            fun_prop
          have h2 : Continuous (fun z : ℝ × ℝ => Complex.exp (-(Complex.I * (z.2 : ℂ) * (z.1 : ℂ)))) := by
            fun_prop
          have h3 : AEStronglyMeasurable (fun z : ℝ × ℝ => ((deriv G z.2 : ℝ) : ℂ))
              ((volume.restrict (Ioc 0 R)).prod volume) :=
            (Complex.measurable_ofReal.comp ((measurable_deriv G).comp measurable_snd)).aestronglyMeasurable
          have := h1.aestronglyMeasurable.mul (h3.mul h2.aestronglyMeasurable)
          exact this
        · simp only [Function.uncurry, hF, one_mul]
          rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
          have e1 : ‖Complex.exp (Complex.I * (Phi0 p z.1 : ℂ))‖ = 1 := by
            rw [Complex.norm_exp]; simp
          have e2 : ‖Complex.exp (-(Complex.I * (z.2 : ℂ) * (z.1 : ℂ)))‖ = 1 := by
            rw [Complex.norm_exp]; simp
          rw [e1, e2, Complex.norm_real]; simp
      have hswap := integral_integral_swap hFint
      -- left side
      have hL : seq G R = ∫ ξ in Ioc 0 R, ∫ y, F ξ y := by
        simp only [hseq]
        rw [intervalIntegral.integral_of_le hR.le]
        refine setIntegral_congr_fun measurableSet_Ioc (fun ξ _ => ?_)
        simp only [hF]
        rw [integral_const_mul]
        have h := hFG ξ
        unfold fourierT at h ⊢
        have hξ : (ξ : ℂ) * fourierT (fun x => (G x : ℂ)) ξ =
            -Complex.I * ∫ x, ((deriv G x : ℝ) : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) := by
          unfold fourierT; rw [h]; ring_nf; rw [Complex.I_sq]; ring
        calc (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) *
              ∫ x, (G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))
            = Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * ((ξ : ℂ) * fourierT (fun x => (G x : ℂ)) ξ) := by
              unfold fourierT; ring
          _ = _ := by rw [hξ]; ring
      -- right side
      have hR' : ∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_KR p R y = ∫ y, ∫ ξ in Ioc 0 R, F ξ y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [c08_ell_kernel_KR, hF]
        rw [intervalIntegral.integral_of_le hR.le, ← integral_const_mul, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioc (fun ξ _ => ?_)
        have : Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ)) =
            Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * Complex.exp (-(Complex.I * (y : ℂ) * (ξ : ℂ))) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [this]; ring
      rw [hL, hR', hswap]
    -- dominated convergence
    have hDCT : Tendsto (fun R : ℝ => ∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_KR p R y) atTop
        (nhds (∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun y => Ck * yNorm p γ G * jb y ^ (-a))
      · exact Eventually.of_forall fun R => hG'm.mul (hKRc R).aestronglyMeasurable
      · filter_upwards [eventually_gt_atTop 0] with R hR
        filter_upwards [hbound] with y hy using hy _ (hKRb y R hR)
      · exact hdom
      · exact Eventually.of_forall fun y => (hKlim y).const_mul _
    refine ⟨hDCT.congr' ?_, hint, ?_⟩
    · filter_upwards [eventually_gt_atTop 0] with R hR using (hfub R hR).symm
    · calc ‖∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y‖
          ≤ ∫ y, Ck * yNorm p γ G * jb y ^ (-a) := by
            apply norm_integral_le_of_norm_le hdom
            filter_upwards [hbound] with y hy using hy _ (hKbd y)
        _ = Ck * Ia * yNorm p γ G := by rw [integral_const_mul]; ring
  have hell : ∀ G ∈ Y_gamma p γ, ell p G = ∫ y, ((deriv G y : ℝ) : ℂ) * c08_ell_kernel_K p y :=
    fun G hG => (core G hG).1.limUnder_eq
  -- linearity of the sequences
  have hlin : ∀ G ∈ Y_gamma p γ, ∀ H ∈ Y_gamma p γ, ∀ c : ℝ,
      Tendsto (seq (c • G + H)) atTop (nhds ((c : ℂ) * ell p G + ell p H)) := by
    intro G hG H hH c
    obtain ⟨hGi, -⟩ := hL1G G hG
    obtain ⟨hHi, -⟩ := hL1G H hH
    have hft : ∀ ξ, fourierT (fun x => ((c • G + H) x : ℂ)) ξ =
        (c : ℂ) * fourierT (fun x => (G x : ℂ)) ξ + fourierT (fun x => (H x : ℂ)) ξ := by
      intro ξ
      unfold fourierT
      have hb : ∀ᵐ (x : ℝ) ∂volume, ‖Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))‖ ≤ 1 :=
        Eventually.of_forall fun x => by rw [Complex.norm_exp]; simp
      have hm : AEStronglyMeasurable (fun x : ℝ => Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))))
          volume := Continuous.aestronglyMeasurable (by fun_prop)
      have i1 : Integrable (fun x : ℝ => (c : ℂ) * ((G x : ℂ) *
          Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))))) :=
        (hGi.ofReal.mul_bdd hm hb).const_mul (c : ℂ)
      have i2 : Integrable (fun x : ℝ => (H x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) :=
        hHi.ofReal.mul_bdd hm hb
      beta_reduce
      rw [← integral_const_mul, ← integral_add i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
    have hGc := c08_aux_fourierT_continuous_of_integrable hGi.ofReal
    have hHc := c08_aux_fourierT_continuous_of_integrable hHi.ofReal
    have hΦc := c08_aux_Phi0_continuous p hp0.le
    have hc1 : Continuous (fun ξ : ℝ => (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ))) := by
      have := Complex.continuous_ofReal.comp hΦc; fun_prop
    have hseqeq : seq (c • G + H) = fun R => (c : ℂ) * seq G R + seq H R := by
      ext R
      simp only [hseq]
      simp_rw [hft]
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
      · refine intervalIntegral.integral_congr (fun ξ _ => ?_)
        ring
      · exact (continuous_const.mul (hc1.mul hGc)).intervalIntegrable _ _
      · exact (hc1.mul hHc).intervalIntegrable _ _
    rw [hseqeq]
    have h1 := (core G hG).1
    have h2 := (core H hH).1
    rw [← hell G hG] at h1
    rw [← hell H hH] at h2
    exact (h1.const_mul _).add h2
  have hlin' : ∀ G ∈ Y_gamma p γ, ∀ H ∈ Y_gamma p γ, ∀ c : ℝ,
      ell p (c • G + H) = (c : ℂ) * ell p G + ell p H := fun G hG H hH c =>
    (hlin G hG H hH c).limUnder_eq
  refine ⟨Ck * Ia + 1, by positivity, fun G hG => ⟨?_, (core G hG).2.1, hell G hG, ?_⟩, hlin', ?_⟩
  · rw [hell G hG]; exact (core G hG).1
  · rw [hell G hG]
    have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    have := (core G hG).2.2
    nlinarith
  · intro Gn G hGn hG hlim
    have hbd : ∀ n, ‖ell p G‖ ≤ (Ck * Ia + 1) * yNorm p γ (Gn n - G) := by
      intro n
      obtain ⟨hGnY, hGn0⟩ := hGn n
      obtain ⟨hsub, -⟩ := c08_aux_Y_sub hG hGnY
      have hsplit : G = (1 : ℝ) • (G - Gn n) + Gn n := by ext x; simp
      have h1 : ell p G = ell p (G - Gn n) := by
        conv_lhs => rw [hsplit]
        rw [hlin' _ hsub _ hGnY 1, hGn0]; simp
      have hneg : yNorm p γ (G - Gn n) = yNorm p γ (Gn n - G) := by
        unfold yNorm
        rw [show G - Gn n = -(Gn n - G) by ring, c08_aux_Y_norm_neg]
      rw [h1, hell _ hsub, ← hneg]
      have hN : 0 ≤ yNorm p γ (G - Gn n) := ENNReal.toReal_nonneg
      have := (core _ hsub).2.2
      nlinarith
    have hlim2 : Tendsto (fun n => (Ck * Ia + 1) * yNorm p γ (Gn n - G)) atTop (nhds 0) := by
      simpa using hlim.const_mul (Ck * Ia + 1)
    have hle : ‖ell p G‖ ≤ 0 := ge_of_tendsto hlim2 (Eventually.of_forall hbd)
    exact ⟨hG, norm_le_zero_iff.1 hle⟩

/-- Blueprint: lem:c08_T0_tail.  For `γ > β + 1/p`, `G ∈ Y_γ`, `ℓ(G) = 0`: the improper integrals
exist and `m_G(ξ) = -e^{-iΦ₀(ξ)} ξ^{-2} ∫_ξ^∞ η e^{iΦ₀} Ĝ` (`ξ > 0`),
`m_G(ξ) = e^{-iΦ₀(ξ)} ξ^{-2} ∫_{-∞}^ξ η e^{iΦ₀} Ĝ` (`ξ < 0`). -/
theorem c08_T0_tail (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : beta p + 1 / p < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (hℓ : ell p G = 0) :
    (∀ ξ : ℝ, 0 < ξ → ∃ I : ℂ,
      Tendsto (fun R : ℝ => ∫ η in ξ..R,
          (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) * fourierT (fun x => (G x : ℂ)) η)
        atTop (nhds I) ∧
      T_0_symbol p G ξ = -(Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) / (ξ : ℂ) ^ 2) * I) ∧
    ∀ ξ : ℝ, ξ < 0 → ∃ I : ℂ,
      Tendsto (fun R : ℝ => ∫ η in (-R)..ξ,
          (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) * fourierT (fun x => (G x : ℂ)) η)
        atTop (nhds I) ∧
      T_0_symbol p G ξ = Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) / (ξ : ℂ) ^ 2 * I := by
  have hγ' : 1 + 1 / p < γ := by
    have : 1 ≤ beta p := by
      unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
    linarith
  have hγ1 : 1 < γ := by
    have : 0 < 1 / p := by have : 0 < p := by linarith
                           positivity
    linarith
  obtain ⟨_, _, _, hL1G⟩ := c08_L1_embedding p γ hp hp1 hγ'
  have hGint : Integrable (fun x => (G x : ℂ)) := (hL1G G hG).1.ofReal
  have hGc := c08_aux_fourierT_continuous_of_integrable hGint
  set F : ℝ → ℂ := fun η => (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
    fourierT (fun x => (G x : ℂ)) η with hF
  have hFc : Continuous F := by
    have := c08_aux_Phi0_continuous p (by linarith)
    simp only [hF]; fun_prop
  have hFi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hFc.intervalIntegrable a b
  obtain ⟨_, _, hell, -, -⟩ := linear_ell_continuity p γ hp hp1 hγ
  have hlim : Tendsto (fun R : ℝ => ∫ η in (0 : ℝ)..R, F η) atTop (nhds 0) := by
    rw [← hℓ]; exact (hell G hG).1
  obtain ⟨⟨hform, -, -, -⟩, -⟩ := c08_free_ode p γ hp hp1 hγ1 G hG
  constructor
  · intro ξ hξ
    refine ⟨-(∫ η in (0 : ℝ)..ξ, F η), ?_, ?_⟩
    · have : (fun R : ℝ => ∫ η in ξ..R, F η) =
          fun R => (∫ η in (0 : ℝ)..R, F η) - ∫ η in (0 : ℝ)..ξ, F η := by
        ext R; rw [intervalIntegral.integral_interval_sub_left (hFi 0 R) (hFi 0 ξ)]
      rw [this, ← zero_sub]
      exact hlim.sub_const _
    · rw [hform ξ hξ.ne']; ring
  · intro ξ hξ
    refine ⟨∫ η in (0 : ℝ)..ξ, F η, ?_, hform ξ hξ.ne⟩
    have hneg : ∀ R : ℝ, 0 ≤ R → (∫ η in (-R)..0, F η) =
        -(starRingEnd ℂ) (∫ η in (0 : ℝ)..R, F η) := by
      intro R hR
      have h1 : (∫ η in (-R)..0, F η) = ∫ s in (0 : ℝ)..R, F (-s) := by
        rw [intervalIntegral.integral_comp_neg]; simp
      have h2 : ∀ s, F (-s) = -(starRingEnd ℂ) (F s) := by
        intro s
        simp only [hF]
        rw [c08_aux_Phi0_neg, c08_aux_fourierT_neg_real, map_mul, map_mul, ← Complex.exp_conj]
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast; ring_nf
      rw [h1, intervalIntegral.integral_of_le hR, intervalIntegral.integral_of_le hR]
      simp_rw [h2]
      rw [integral_neg, integral_conj]
    have hlim2 : Tendsto (fun R : ℝ => ∫ η in (-R)..0, F η) atTop (nhds 0) := by
      have h := ((Complex.continuous_conj.tendsto 0).comp hlim).neg
      simp only [map_zero, neg_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with R hR
      simp only [Function.comp]
      rw [hneg R hR]
    have : (fun R : ℝ => ∫ η in (-R)..ξ, F η) =
        fun R => (∫ η in (-R)..0, F η) + ∫ η in (0 : ℝ)..ξ, F η := by
      ext R; rw [intervalIntegral.integral_add_adjacent_intervals (hFi _ _) (hFi _ _)]
    rw [this]
    simpa using hlim2.add_const (∫ η in (0 : ℝ)..ξ, F η)

/-! ## Low-frequency estimate -/

/-- Blueprint: def:c08_Z_gamma.  The `Z_γ` norm (in `[0,∞]`):
`sup_y ⟨y⟩^γ|H(y)| + ess sup_{y ≤ -1} ⟨y⟩^γ(⟨y⟩|H'(y)| + ⟨y⟩²|H''(y)|)`. -/
def c08_Z_gamma_norm (γ : ℝ) (H : ℝ → ℂ) : ℝ≥0∞ :=
  (⨆ y : ℝ, ENNReal.ofReal (jb y ^ γ * ‖H y‖)) +
  essSup (fun y => ENNReal.ofReal (jb y ^ γ * (jb y * ‖deriv H y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv H) y‖))) (volume.restrict (Iic (-1)))

/-- Blueprint: def:c08_Z_gamma.  `Z_γ`: continuous `H : ℝ → ℂ` with
`H|_{(-∞,-1)} ∈ W^{2,∞}_loc((-∞,-1))` (`C¹` there with locally Lipschitz derivative) and
`‖H‖_{Z_γ} < ∞`. -/
def c08_Z_gamma (γ : ℝ) : Set (ℝ → ℂ) :=
  {H | Continuous H ∧ ContDiffOn ℝ 1 H (Iio (-1)) ∧ LocallyLipschitzOn (Iio (-1)) (deriv H) ∧
    c08_Z_gamma_norm γ H < ⊤}

/-- Blueprint: def:c08_low_operators.  The averaging operator
`𝒜_k G(y) = ∫₀¹ (1 - t^α)^k G(y/t) dt` (`α = p + 1`). -/
def c08_low_operators (p : ℝ) (k : ℕ) (G : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t ^ (p + 1)) ^ k * G (y / t)

/-- Blueprint: def:c08_low_operators.  The low-frequency multiplier `m_k(ξ) = χ(ξ) Φ₀(ξ)^k`
(`χ = GSQG.rho`). -/
def c08_low_operators_m (p : ℝ) (k : ℕ) (ξ : ℝ) : ℂ := ((rho ξ * Phi0 p ξ ^ k : ℝ) : ℂ)

/-- Blueprint: def:c08_low_operators.  The kernel `H_k = m_k^∨`,
`H_k(y) = (2π)⁻¹ ∫ m_k(ξ) e^{iyξ} dξ`. -/
def c08_low_operators_H (p : ℝ) (k : ℕ) : ℝ → ℂ := invFourierT (c08_low_operators_m p k)

/-- Blueprint: def:c08_low_operators.  `ℳ_k H = H_k * H` (convolution). -/
def c08_low_operators_M (p : ℝ) (k : ℕ) (H : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ z, c08_low_operators_H p k (y - z) * H z

theorem c08_aux_rho_props : (∀ ξ, 2 < |ξ| → rho ξ = 0) ∧ (∀ ξ ∈ Icc (-1:ℝ) 1, rho ξ = 1) ∧
    (∀ ξ, rho (-ξ) = rho ξ) ∧ (∀ ξ, 0 ≤ rho ξ ∧ rho ξ ≤ 1) := by
  refine ⟨fun ξ h => ?_, fun ξ h => ?_, fun ξ => by unfold rho; rw [abs_neg], fun ξ =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  · unfold rho; exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · unfold rho; apply Real.smoothTransition.one_of_one_le
    have : |ξ| ≤ 1 := abs_le.2 ⟨h.1, h.2⟩
    linarith

theorem c08_aux_m_eq (p : ℝ) (k : ℕ) : c03_symbol_mk p rho k = c08_low_operators_m p k := by
  ext ξ; unfold c03_symbol_mk c08_low_operators_m; push_cast; ring

theorem c08_aux_m_neg (p : ℝ) (k : ℕ) (ξ : ℝ) :
    c08_low_operators_m p k (-ξ) = (-1) ^ k * c08_low_operators_m p k ξ := by
  unfold c08_low_operators_m
  have h1 : rho (-ξ) = rho ξ := c08_aux_rho_props.2.2.1 ξ
  have h2 : Phi0 p (-ξ) = -Phi0 p ξ := c08_aux_Phi0_neg p ξ
  rw [h1, h2]; push_cast; rw [neg_pow]; ring

theorem c08_aux_H_conj (p : ℝ) (k : ℕ) (y : ℝ) :
    (starRingEnd ℂ) (c08_low_operators_H p k y) = (-1) ^ k * c08_low_operators_H p k y := by
  unfold c08_low_operators_H invFourierT
  rw [map_mul, ← integral_conj]
  have hc : ∀ ξ : ℝ, (starRingEnd ℂ) (c08_low_operators_m p k ξ *
      Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) =
      c08_low_operators_m p k ξ * Complex.exp (Complex.I * (y : ℂ) * ((-ξ : ℝ) : ℂ)) := by
    intro ξ
    rw [map_mul, ← Complex.exp_conj]
    unfold c08_low_operators_m
    rw [Complex.conj_ofReal]
    congr 2
    simp [Complex.conj_ofReal]
  simp_rw [hc]
  have := integral_neg_eq_self
    (fun ξ : ℝ => c08_low_operators_m p k (-ξ) * Complex.exp (Complex.I * (y : ℂ) * ((ξ : ℝ) : ℂ)))
    (volume : Measure ℝ)
  simp only [neg_neg] at this
  rw [this]
  simp_rw [c08_aux_m_neg, mul_assoc, integral_const_mul]
  rw [map_inv₀, Complex.conj_ofReal]; ring

/-- Blueprint: lem:c08_Hk_kernel.  `|∂^j H_k(y)| ≤ C₁ C₂^k ⟨y⟩^{-p-2-j}` (`j ≤ 2`), hence
`‖∂^j H_k‖_{L¹} ≤ C₁' C₂^k`; `H_k` is smooth, real for even `k`, imaginary for odd `k`,
`(-i)^k H_k` is real. -/
theorem c08_Hk_kernel (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C₁ C₂ C₁' : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₁' ∧
      (∀ (k j : ℕ), j ≤ 2 → ∀ y : ℝ,
        ‖iteratedDeriv j (c08_low_operators_H p k) y‖ ≤ C₁ * C₂ ^ k * jb y ^ (-p - 2 - (j : ℝ))) ∧
      (∀ (k j : ℕ), j ≤ 2 → Integrable (iteratedDeriv j (c08_low_operators_H p k)) ∧
        ∫ y, ‖iteratedDeriv j (c08_low_operators_H p k) y‖ ≤ C₁' * C₂ ^ k) ∧
      ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (c08_low_operators_H p k) ∧
        (Even k → ∀ y, (c08_low_operators_H p k y).im = 0) ∧
        (Odd k → ∀ y, (c08_low_operators_H p k y).re = 0) ∧
        ∀ y, ((-Complex.I) ^ k * c08_low_operators_H p k y).im = 0 := by
  obtain ⟨C, hC, hA⟩ := appendix_nonsmooth_fourier_inverse p (by linarith) hp1
  obtain ⟨hr0, hr1, -, -⟩ := c08_aux_rho_props
  obtain ⟨C₀, hC₀, hk⟩ := hA rho c08_aux_rho_contDiff hr0 hr1
  simp only [c08_aux_m_eq] at hk
  have hI := c08_aux_jb_rpow_integrable (p + 2) (by linarith)
  set I := ∫ y, jb y ^ (-(p + 2))
  have hI0 : 0 ≤ I := integral_nonneg fun y => (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
  have hbd : ∀ (k j : ℕ), j ≤ 2 → ∀ y : ℝ,
      ‖iteratedDeriv j (c08_low_operators_H p k) y‖ ≤ C₀ * C ^ k * jb y ^ (-p - 2 - (j : ℝ)) :=
    fun k j hj y => by exact_mod_cast (hk k).2 j hj y
  refine ⟨C₀, C, C₀ * (I + 1), hC₀, hC, by positivity, hbd, fun k j hj => ?_, fun k => ?_⟩
  · have hcont : Continuous (iteratedDeriv j (c08_low_operators_H p k)) :=
      (hk k).1.continuous_iteratedDeriv j (by exact_mod_cast le_top)
    have hle : ∀ y, ‖iteratedDeriv j (c08_low_operators_H p k) y‖ ≤ C₀ * C ^ k * jb y ^ (-(p + 2)) := by
      intro y
      refine (hbd k j hj y).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb y) (by
        have : (0:ℝ) ≤ j := Nat.cast_nonneg j
        linarith)
    have hint : Integrable (iteratedDeriv j (c08_low_operators_H p k)) :=
      (hI.const_mul (C₀ * C ^ k)).mono' hcont.aestronglyMeasurable (Eventually.of_forall hle)
    refine ⟨hint, ?_⟩
    calc ∫ y, ‖iteratedDeriv j (c08_low_operators_H p k) y‖
        ≤ ∫ y, C₀ * C ^ k * jb y ^ (-(p + 2)) :=
          integral_mono hint.norm (hI.const_mul _) hle
      _ = C₀ * C ^ k * I := integral_const_mul _ _
      _ ≤ C₀ * (I + 1) * C ^ k := by
          have : 0 ≤ C₀ * C ^ k := by positivity
          nlinarith
  · have hconj := c08_aux_H_conj p k
    refine ⟨(hk k).1, fun he y => ?_, fun ho y => ?_, fun y => ?_⟩
    · have h := hconj y
      rw [he.neg_one_pow, one_mul] at h
      exact Complex.conj_eq_iff_im.1 h
    · have h := hconj y
      rw [ho.neg_one_pow] at h
      have := congrArg Complex.re h
      simp at this
      linarith
    · apply Complex.conj_eq_iff_im.1
      rw [map_mul, hconj y, map_pow, map_neg, Complex.conj_I, neg_neg, ← mul_assoc, ← mul_pow]
      congr 2; ring

/-- Blueprint: lem:c08_convolution_weight.  For `a ≥ b > 1`:
`∫ ⟨y-z⟩^{-a} ⟨z⟩^{-b} dz ≤ C_{a,b} ⟨y⟩^{-b}`. -/
theorem c08_convolution_weight (a b : ℝ) (hb : 1 < b) (hab : b ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      Integrable (fun z => jb (y - z) ^ (-a) * jb z ^ (-b)) ∧
      ∫ z, jb (y - z) ^ (-a) * jb z ^ (-b) ≤ C * jb y ^ (-b) := by
  have hIa := c08_aux_jb_rpow_integrable a (by linarith)
  have hIb := c08_aux_jb_rpow_integrable b hb
  set Ia := ∫ z, jb z ^ (-a)
  set Ib := ∫ z, jb z ^ (-b)
  have hIa0 : 0 ≤ Ia := integral_nonneg (fun z => (Real.rpow_pos_of_pos (c08_aux_jb_pos z) _).le)
  have hIb0 : 0 ≤ Ib := integral_nonneg (fun z => (Real.rpow_pos_of_pos (c08_aux_jb_pos z) _).le)
  refine ⟨2 ^ b * (Ia + Ib) + 1, by positivity, fun y => ?_⟩
  have hpt : ∀ z, jb (y - z) ^ (-a) * jb z ^ (-b) ≤
      2 ^ b * jb y ^ (-b) * (jb (y - z) ^ (-a) + jb z ^ (-b)) := by
    intro z
    have hA0 : 0 ≤ jb (y - z) ^ (-a) := (Real.rpow_pos_of_pos (c08_aux_jb_pos _) _).le
    have hB0 : 0 ≤ jb z ^ (-b) := (Real.rpow_pos_of_pos (c08_aux_jb_pos _) _).le
    have hA1 : jb (y - z) ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb _) (by linarith)
    have hB1 : jb z ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb _) (by linarith)
    have hC0 : 0 ≤ 2 ^ b * jb y ^ (-b) := by
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-b); positivity
    rcases le_total (|y|) (2 * |z|) with h | h
    · have := c08_aux_jb_rpow_neg_le (b := b) (by linarith) h
      calc jb (y - z) ^ (-a) * jb z ^ (-b) ≤ jb (y - z) ^ (-a) * (2 ^ b * jb y ^ (-b)) :=
            mul_le_mul_of_nonneg_left this hA0
        _ ≤ _ := by nlinarith
    · have h' : |y| ≤ 2 * |y - z| := by
        have := abs_sub_abs_le_abs_sub y z
        linarith
      have h1 := c08_aux_jb_rpow_neg_le (u := y - z) (b := b) (by linarith) h'
      have h2 : jb (y - z) ^ (-a) ≤ jb (y - z) ^ (-b) :=
        Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb _) (by linarith)
      calc jb (y - z) ^ (-a) * jb z ^ (-b) ≤ (2 ^ b * jb y ^ (-b)) * jb z ^ (-b) :=
            mul_le_mul_of_nonneg_right (h2.trans h1) hB0
        _ ≤ _ := by nlinarith
  have hIa' : Integrable (fun z => jb (y - z) ^ (-a)) := hIa.comp_sub_left y
  have hsum : Integrable (fun z => 2 ^ b * jb y ^ (-b) * (jb (y - z) ^ (-a) + jb z ^ (-b))) :=
    (hIa'.add hIb).const_mul _
  have hint : Integrable (fun z => jb (y - z) ^ (-a) * jb z ^ (-b)) := by
    refine hsum.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (hIa'.aestronglyMeasurable.mul hIb.aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (c08_aux_jb_pos _) _).le
        (Real.rpow_pos_of_pos (c08_aux_jb_pos _) _).le)]
      exact hpt z
  refine ⟨hint, ?_⟩
  calc ∫ z, jb (y - z) ^ (-a) * jb z ^ (-b)
      ≤ ∫ z, 2 ^ b * jb y ^ (-b) * (jb (y - z) ^ (-a) + jb z ^ (-b)) := integral_mono hint hsum hpt
    _ = 2 ^ b * jb y ^ (-b) * (Ia + Ib) := by
      rw [integral_const_mul, integral_add hIa' hIb, integral_sub_left_eq_self (fun z => jb z ^ (-a))]
    _ ≤ (2 ^ b * (Ia + Ib) + 1) * jb y ^ (-b) := by
      have := Real.rpow_pos_of_pos (c08_aux_jb_pos y) (-b); nlinarith

/-- Blueprint: lem:c08_average_fourier.  For `G ∈ Y_γ` (`γ > 1`) and `k ≥ 0`: `𝒜_k G ∈ L¹` with
`‖𝒜_k G‖_{L¹} ≤ ½‖G‖_{L¹}`, the double integral `∫₀¹∫ (1-t^α)^k G(y/t) dy dt` converges absolutely,
and `(𝒜_k G)^(ξ) = ∫₀¹ t(1-t^{p+1})^k Ĝ(tξ) dt` for every `ξ`. -/
theorem c08_average_fourier (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (k : ℕ) :
    Integrable G ∧
    Integrable (Function.uncurry fun (t y : ℝ) => (1 - t ^ (p + 1)) ^ k * G (y / t))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) ∧
    Integrable (c08_low_operators p k G) ∧
    ∫ y, ‖c08_low_operators p k G y‖ ≤ 1 / 2 * ∫ y, ‖G y‖ ∧
    ∀ ξ : ℝ, fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ =
      ∫ t in (0 : ℝ)..1, (t : ℂ) * (((1 - t ^ (p + 1)) ^ k : ℝ) : ℂ) *
        fourierT (fun x => (G x : ℂ)) (t * ξ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hGi, -⟩ := c08_aux_Y_integrable hp0 hγ hG
  have hGc : Continuous G := hG.1.continuous
  set μ := volume.restrict (Ioc (0 : ℝ) 1)
  set w : ℝ → ℝ := fun t => (1 - t ^ (p + 1)) ^ k with hw
  set F : ℝ × ℝ → ℝ := Function.uncurry fun (t y : ℝ) => w t * G (y / t) with hF
  have hw01 : ∀ t ∈ Ioc (0:ℝ) 1, 0 ≤ w t ∧ w t ≤ 1 := by
    intro t ht
    have h1 : t ^ (p + 1) ≤ 1 := Real.rpow_le_one ht.1.le ht.2 (by linarith)
    have h0 : 0 ≤ t ^ (p + 1) := Real.rpow_nonneg ht.1.le _
    exact ⟨pow_nonneg (by linarith) k, pow_le_one₀ (by linarith) (by linarith)⟩
  have hwc : Continuous w := by
    simp only [hw]
    exact (continuous_const.sub (continuous_id.rpow_const fun _ => Or.inr (by linarith))).pow k
  have hFm : Measurable F := by
    have : Measurable (fun q : ℝ × ℝ => q.2 / q.1) := measurable_snd.div measurable_fst
    exact (hwc.measurable.comp measurable_fst).mul (hGc.measurable.comp this)
  have hsec : ∀ t ∈ Ioc (0:ℝ) 1, Integrable (fun y => F (t, y)) ∧
      ∫ y, ‖F (t, y)‖ = w t * t * ∫ y, ‖G y‖ := by
    intro t ht
    refine ⟨(hGi.comp_div ht.1.ne').const_mul (w t), ?_⟩
    simp only [hF, Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs (w t),
      abs_of_nonneg (hw01 t ht).1]
    rw [integral_const_mul, Measure.integral_comp_div (fun y => ‖G y‖) t, smul_eq_mul,
      abs_of_pos ht.1]; ring
  have hFi : Integrable F (μ.prod volume) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => (hsec t ht).1), ?_⟩
    have hb : ∀ᵐ t ∂μ, ‖∫ y, ‖F (t, y)‖‖ ≤ ∫ y, ‖G y‖ := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      have h0 := (hw01 t ht).1; have h1 := ht.1.le
      have h2 := integral_nonneg (μ := volume) (fun y => norm_nonneg (G y))
      rw [(hsec t ht).2, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hw1 := (hw01 t ht).2
      have h1 : w t * t ≤ 1 := by nlinarith [ht.2, ht.1]
      nlinarith
    have : IsFiniteMeasure μ := by
      simp only [μ]; exact isFiniteMeasure_restrict.2 (by simp)
    exact Integrable.mono' (integrable_const (∫ y, ‖G y‖))
      (hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) hb
  have hA : ∀ y, c08_low_operators p k G y = ∫ t, F (t, y) ∂μ := by
    intro y
    simp only [c08_low_operators, hF, hw, Function.uncurry_apply_pair, μ]
    rw [intervalIntegral.integral_of_le zero_le_one]
  have hAeq : c08_low_operators p k G = fun y => ∫ t, F (t, y) ∂μ := funext hA
  have hAi : Integrable (c08_low_operators p k G) := by
    rw [hAeq]; exact hFi.integral_prod_right
  have hFn : Integrable (fun q => ‖F q‖) (μ.prod volume) := hFi.norm
  refine ⟨hGi, hFi, hAi, ?_, fun ξ => ?_⟩
  · calc ∫ y, ‖c08_low_operators p k G y‖ ≤ ∫ y, ∫ t, ‖F (t, y)‖ ∂μ := by
          refine integral_mono hAi.norm hFn.integral_prod_right (fun y => ?_)
          rw [hA y]; exact norm_integral_le_integral_norm _
      _ = ∫ t, ∫ y, ‖F (t, y)‖ ∂volume ∂μ := (integral_integral_swap hFn).symm
      _ = ∫ t, w t * t * ∫ y, ‖G y‖ ∂volume ∂μ :=
          setIntegral_congr_fun measurableSet_Ioc (fun t ht => (hsec t ht).2)
      _ ≤ ∫ t, t * ∫ y, ‖G y‖ ∂volume ∂μ := by
          have hI0 := integral_nonneg (μ := volume) (fun y => norm_nonneg (G y))
          refine integral_mono_ae ?_ ?_ ((ae_restrict_iff' measurableSet_Ioc).2
            (Eventually.of_forall fun t ht => ?_))
          · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
          · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
          · have := hw01 t ht
            have h := mul_le_mul_of_nonneg_right this.2 ht.1.le
            nlinarith
      _ = 1 / 2 * ∫ y, ‖G y‖ := by
          rw [integral_mul_const, ← intervalIntegral.integral_of_le zero_le_one, integral_id]
          ring
  · set e : ℝ → ℂ := fun y => Complex.exp (-(Complex.I * (y : ℂ) * (ξ : ℂ))) with he
    have hec : Continuous e := by rw [he]; fun_prop
    have hne : ∀ y, ‖e y‖ = 1 := fun y => by
      rw [he]; dsimp only; rw [Complex.norm_exp]; simp
    have hFc : Integrable (fun q : ℝ × ℝ => ((F q : ℝ) : ℂ) * e q.2) (μ.prod volume) :=
      Integrable.mul_bdd hFi.ofReal (hec.comp continuous_snd).aestronglyMeasurable
        (Eventually.of_forall fun q => (hne q.2).le)
    have hinner : ∀ t ∈ Ioc (0:ℝ) 1, ∫ y, ((F (t, y) : ℝ) : ℂ) * e y =
        (t : ℂ) * ((w t : ℝ) : ℂ) * fourierT (fun x => (G x : ℂ)) (t * ξ) := by
      intro t ht
      have ht0 : t ≠ 0 := ht.1.ne'
      set g : ℝ → ℂ := fun u => (G u : ℂ) * Complex.exp (-(Complex.I * ((t * u : ℝ) : ℂ) * (ξ : ℂ)))
      have h1 : (fun y => ((F (t, y) : ℝ) : ℂ) * e y) = fun y => ((w t : ℝ) : ℂ) * g (y / t) := by
        ext y
        simp only [hF, Function.uncurry_apply_pair, he, g]
        rw [mul_div_cancel₀ y ht0]; push_cast; ring
      rw [h1, integral_const_mul, Measure.integral_comp_div g t, abs_of_pos ht.1, Complex.real_smul]
      unfold fourierT
      have h2 : (fun u => g u) = fun u => (G u : ℂ) * Complex.exp (-(Complex.I * (u : ℂ) * ((t * ξ : ℝ) : ℂ))) := by
        ext u; simp only [g]; push_cast; ring_nf
      rw [h2]; ring
    calc fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ
        = ∫ y, ∫ t, ((F (t, y) : ℝ) : ℂ) * e y ∂μ := by
          unfold fourierT
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only
          rw [hA y, integral_mul_const]
          exact congrArg (· * e y) integral_complex_ofReal.symm
      _ = ∫ t, ∫ y, ((F (t, y) : ℝ) : ℂ) * e y ∂volume ∂μ :=
          (integral_integral_swap (f := fun t y => ((F (t, y) : ℝ) : ℂ) * e y) hFc).symm
      _ = ∫ t, (t : ℂ) * ((w t : ℝ) : ℂ) * fourierT (fun x => (G x : ℂ)) (t * ξ) ∂μ :=
          setIntegral_congr_fun measurableSet_Ioc hinner
      _ = _ := by
          rw [intervalIntegral.integral_of_le zero_le_one]




theorem c08_aux_m_continuous (p : ℝ) (hp : 0 < p) (k : ℕ) : Continuous (c08_low_operators_m p k) := by
  unfold c08_low_operators_m
  exact Complex.continuous_ofReal.comp (c08_aux_rho_contDiff.continuous.mul
    ((c08_aux_Phi0_continuous p hp.le).pow k))

theorem c08_aux_m_integrable (p : ℝ) (hp : 0 < p) (k : ℕ) : Integrable (c08_low_operators_m p k) := by
  apply (c08_aux_m_continuous p hp k).integrable_of_hasCompactSupport
  rw [HasCompactSupport]
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (-2:ℝ)) (b := 2)) (isClosed_tsupport _)
  apply closure_minimal _ isClosed_Icc
  intro ξ hξ
  by_contra h
  apply hξ
  have : 2 < |ξ| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  unfold c08_low_operators_m
  rw [c08_aux_rho_props.1 ξ this]; simp

/-- Blueprint: lem:c08_convolution_fourier.  `H_k ∈ L¹(ℝ;ℂ)`, `Ĥ_k = m_k` pointwise, and for
`H ∈ L¹(ℝ;ℂ)` the convolution `ℳ_k H(y)` converges absolutely for every `y`, `ℳ_k H ∈ L¹` with
`‖ℳ_k H‖_{L¹} ≤ ‖H_k‖_{L¹}‖H‖_{L¹}`, and `(ℳ_k H)^ = m_k Ĥ` pointwise. -/
theorem c08_convolution_fourier (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (k : ℕ) :
    Integrable (c08_low_operators_H p k) ∧
    (∀ ξ : ℝ, fourierT (c08_low_operators_H p k) ξ = c08_low_operators_m p k ξ) ∧
    ∀ H : ℝ → ℂ, Integrable H →
      (∀ y : ℝ, Integrable (fun z => c08_low_operators_H p k (y - z) * H z)) ∧
      Integrable (c08_low_operators_M p k H) ∧
      ∫ y, ‖c08_low_operators_M p k H y‖ ≤
        (∫ y, ‖c08_low_operators_H p k y‖) * ∫ y, ‖H y‖ ∧
      ∀ ξ : ℝ, fourierT (c08_low_operators_M p k H) ξ =
        c08_low_operators_m p k ξ * fourierT H ξ := by
  obtain ⟨C₁, C₂, C₁', hC₁, hC₂, -, hbd, hL1, hsm⟩ := c08_Hk_kernel p hp hp1
  set Hk := c08_low_operators_H p k with hHk
  have hHki : Integrable Hk := by simpa using (hL1 k 0 (by norm_num)).1
  have hHkc : Continuous Hk := (hsm k).1.continuous
  have hHkb : ∀ y, ‖Hk y‖ ≤ C₁ * C₂ ^ k := by
    intro y
    have := hbd k 0 (by norm_num) y
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at this
    have h1 : jb y ^ (-p - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y) (by linarith)
    have h2 : 0 ≤ C₁ * C₂ ^ k := by positivity
    calc ‖Hk y‖ ≤ C₁ * C₂ ^ k * jb y ^ (-p - 2) := this
      _ ≤ C₁ * C₂ ^ k * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = C₁ * C₂ ^ k := mul_one _
  have hF : ∀ ξ, fourierT Hk ξ = c08_low_operators_m p k ξ :=
    c08_aux_fourierT_invFourierT (c08_aux_m_continuous p (by linarith) k)
      (c08_aux_m_integrable p (by linarith) k) hHki
  refine ⟨hHki, hF, fun H hH => ?_⟩
  have hprod : Integrable (fun q : ℝ × ℝ => Hk (q.1 - q.2) * H q.2) (volume.prod volume) := by
    have := hH.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hHki (μ := volume)
    refine this.congr (Eventually.of_forall fun q => ?_)
    simp [mul_comm]
  have hsec : ∀ y : ℝ, Integrable (fun z => Hk (y - z) * H z) := by
    intro y
    exact hH.bdd_mul (hHkc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => hHkb (y - z))
  have hMi : Integrable (c08_low_operators_M p k H) := hprod.integral_prod_left
  refine ⟨hsec, hMi, ?_, fun ξ => ?_⟩
  · have hnorm : Integrable (fun q : ℝ × ℝ => ‖Hk (q.1 - q.2) * H q.2‖) (volume.prod volume) :=
      hprod.norm
    calc ∫ y, ‖c08_low_operators_M p k H y‖
        ≤ ∫ y, ∫ z, ‖Hk (y - z) * H z‖ := by
          refine integral_mono hMi.norm hnorm.integral_prod_left (fun y => ?_)
          exact norm_integral_le_integral_norm _
      _ = ∫ z, ∫ y, ‖Hk (y - z) * H z‖ := integral_integral_swap hnorm
      _ = ∫ z, (∫ y, ‖Hk y‖) * ‖H z‖ := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [norm_mul]
          rw [integral_mul_const, integral_sub_right_eq_self (fun y => ‖Hk y‖)]
      _ = (∫ y, ‖Hk y‖) * ∫ y, ‖H y‖ := integral_const_mul _ _
  · set e : ℝ → ℂ := fun y => Complex.exp (-(Complex.I * (y : ℂ) * (ξ : ℂ))) with he
    have hec : Continuous e := by rw [he]; fun_prop
    have hne : ∀ y, ‖e y‖ = 1 := fun y => by
      rw [he]; dsimp only; rw [Complex.norm_exp]; simp
    have hprod2 : Integrable (fun q : ℝ × ℝ => Hk (q.1 - q.2) * H q.2 * e q.1) (volume.prod volume) :=
      Integrable.mul_bdd hprod (hec.comp continuous_fst).aestronglyMeasurable
        (Eventually.of_forall fun q => (hne q.1).le)
    have esplit : ∀ y z : ℝ, e y = e (y - z) * e z := by
      intro y z; rw [he]; dsimp only; rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc fourierT (c08_low_operators_M p k H) ξ
        = ∫ y, ∫ z, Hk (y - z) * H z * e y := by
          unfold fourierT
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [c08_low_operators_M, ← hHk]
          rw [← integral_mul_const]
      _ = ∫ z, ∫ y, Hk (y - z) * H z * e y := integral_integral_swap hprod2
      _ = ∫ z, (H z * e z) * ∫ y, Hk y * e y := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only
          rw [← integral_const_mul]
          rw [← integral_sub_right_eq_self (fun y => H z * e z * (Hk y * e y)) z]
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only
          rw [esplit y z]; ring
      _ = c08_low_operators_m p k ξ * fourierT H ξ := by
          rw [integral_mul_const, ← hF ξ, mul_comm]
          rfl

/-- Exponential series remainder: `|e^z - Σ_{k<n} z^k/k!| ≤ Σ_{k≥n} M^k/k!` for `|z| ≤ M`. -/
theorem c08_aux_exp_remainder (z : ℂ) (M : ℝ) (hz : ‖z‖ ≤ M) (n : ℕ) :
    ‖Complex.exp z - ∑ k ∈ Finset.range n, z ^ k / (k.factorial : ℂ)‖ ≤
      ∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ) := by
  have hs := NormedSpace.expSeries_div_hasSum_exp z
  rw [← Complex.exp_eq_exp_ℂ] at hs
  have e := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at e
  rw [← e, add_sub_cancel_left]
  have hM0 : 0 ≤ M := (norm_nonneg z).trans hz
  have hsn : Summable (fun k : ℕ => ‖z‖ ^ (k + n) / ((k + n).factorial : ℝ)) :=
    (summable_nat_add_iff n).2 (Real.summable_pow_div_factorial ‖z‖)
  have hsM : Summable (fun k : ℕ => M ^ (k + n) / ((k + n).factorial : ℝ)) :=
    (summable_nat_add_iff n).2 (Real.summable_pow_div_factorial M)
  have hnorm : ∀ k : ℕ, ‖z ^ (k + n) / ((k + n).factorial : ℂ)‖ = ‖z‖ ^ (k + n) / ((k + n).factorial : ℝ) := by
    intro k; rw [norm_div, norm_pow]; norm_cast
  refine (norm_tsum_le_tsum_norm (by simpa [hnorm] using hsn)).trans ?_
  simp_rw [hnorm]
  refine Summable.tsum_le_tsum (fun k => ?_) hsn hsM
  gcongr

/-- Blueprint: lem:c08_low_fourier_series.  With `M_p = 2^{p+1}/(p+1)`,
`Q_n = Σ_{k<n} (-i)^k/k! m_k (𝒜_k G)^` and `e_n = Σ_{k≥n} M_p^k/k!`: the scalar series converges,
`e_n → 0`, and `|χ m_G(ξ) - Q_n(ξ)| ≤ ½‖G‖_{L¹} e_n` for all `n, ξ`; hence `Q_n → χ m_G`
uniformly on `ℝ` (no upper restriction on `γ`). -/
theorem c08_low_fourier_series (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) :
    Summable (fun k : ℕ => (2 ^ (p + 1) / (p + 1)) ^ k / (k.factorial : ℝ)) ∧
    Tendsto (fun n : ℕ => ∑' k : ℕ, (2 ^ (p + 1) / (p + 1)) ^ (k + n) / ((k + n).factorial : ℝ))
      atTop (nhds 0) ∧
    (∀ (n : ℕ) (ξ : ℝ),
      ‖(rho ξ : ℂ) * T_0_symbol p G ξ -
          ∑ k ∈ Finset.range n, (-Complex.I) ^ k / (k.factorial : ℂ) * c08_low_operators_m p k ξ *
            fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ‖ ≤
        1 / 2 * (∫ y, ‖G y‖) *
          ∑' k : ℕ, (2 ^ (p + 1) / (p + 1)) ^ (k + n) / ((k + n).factorial : ℝ)) ∧
    TendstoUniformly
      (fun (N : ℕ) (ξ : ℝ) => ∑ k ∈ Finset.range N,
        (-Complex.I) ^ k / (k.factorial : ℂ) * c08_low_operators_m p k ξ *
          fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ)
      (fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ) atTop := by
  have hp0 : 0 < p := by linarith
  set M : ℝ := 2 ^ (p + 1) / (p + 1) with hM
  have hM0 : 0 ≤ M := by positivity
  have he0 : ∀ n : ℕ, 0 ≤ ∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ) :=
    fun n => tsum_nonneg fun k => by positivity
  have hsum := Real.summable_pow_div_factorial M
  have hlim : Tendsto (fun n : ℕ => ∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ)) atTop (nhds 0) :=
    _root_.tendsto_sum_nat_add (fun k => M ^ k / (k.factorial : ℝ))
  obtain ⟨hGi, -⟩ := c08_aux_Y_integrable hp0 hγ hG
  set L := ∫ y, ‖G y‖ with hL
  have hL0 : 0 ≤ L := integral_nonneg fun y => norm_nonneg _
  set Gh : ℝ → ℂ := fourierT (fun x => (G x : ℂ)) with hGh
  have hGhc : Continuous Gh := c08_aux_fourierT_continuous_of_integrable hGi.ofReal
  have hGhb : ∀ s, ‖Gh s‖ ≤ L := fun s => by
    have := c08_aux_norm_fourierT_le G s
    simpa [hL, Real.norm_eq_abs] using this
  have hmain : ∀ (n : ℕ) (ξ : ℝ),
      ‖(rho ξ : ℂ) * T_0_symbol p G ξ -
          ∑ k ∈ Finset.range n, (-Complex.I) ^ k / (k.factorial : ℂ) * c08_low_operators_m p k ξ *
            fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ‖ ≤ 1 / 2 * L * (∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ)) := by
    intro n ξ
    set a : ℝ → ℝ := fun t => (1 - t ^ (p + 1)) * Phi0 p ξ with ha
    have hpow : Continuous (fun t : ℝ => t ^ (p + 1)) :=
      continuous_id.rpow_const fun _ => Or.inr (by linarith)
    have hac : Continuous a := by
      simp only [ha]; exact (continuous_const.sub hpow).mul continuous_const
    have hGt : Continuous (fun t : ℝ => Gh (t * ξ)) := hGhc.comp (continuous_id.mul continuous_const)
    set f0 : ℝ → ℂ := fun t => (t : ℂ) * Complex.exp (-(Complex.I * ((a t : ℝ) : ℂ))) * Gh (t * ξ)
    set f : ℕ → ℝ → ℂ := fun k t => (t : ℂ) * (((1 - t ^ (p + 1)) ^ k : ℝ) : ℂ) * Gh (t * ξ)
    have hf0c : Continuous f0 := by
      simp only [f0]
      exact (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp hac)).neg))).mul hGt
    have hfc : ∀ k, Continuous (f k) := fun k => by
      simp only [f]
      exact (Complex.continuous_ofReal.mul (Complex.continuous_ofReal.comp
        ((continuous_const.sub hpow).pow k))).mul hGt
    have hT : T_0_symbol p G ξ = ∫ t in (0:ℝ)..1, f0 t := by
      simp only [T_0_symbol, f0, ha, hGh]
    have hAk : ∀ k, fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ = ∫ t in (0:ℝ)..1, f k t :=
      fun k => (c08_average_fourier p γ hp hp1 hγ G hG k).2.2.2.2 ξ
    simp_rw [hAk]
    set c : ℕ → ℂ := fun k => (-Complex.I) ^ k / (k.factorial : ℂ) * c08_low_operators_m p k ξ
    have e1 : ∑ k ∈ Finset.range n, c k * ∫ t in (0:ℝ)..1, f k t =
        ∫ t in (0:ℝ)..1, ∑ k ∈ Finset.range n, c k * f k t := by
      have hi : ∀ k ∈ Finset.range n, IntervalIntegrable (fun t => c k * f k t) volume 0 1 :=
        fun k _ => (continuous_const.mul (hfc k)).intervalIntegrable 0 1
      rw [intervalIntegral.integral_finsetSum hi]
      exact Finset.sum_congr rfl fun k _ => (intervalIntegral.integral_const_mul _ _).symm
    have i1 : IntervalIntegrable (fun t => (rho ξ : ℂ) * f0 t) volume 0 1 :=
      (continuous_const.mul hf0c).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun t => ∑ k ∈ Finset.range n, c k * f k t) volume 0 1 :=
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hfc k)).intervalIntegrable 0 1
    rw [e1, hT, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub i1 i2]
    have hpt : ∀ t ∈ Set.uIcc (0:ℝ) 1, ‖(rho ξ : ℂ) * f0 t - ∑ k ∈ Finset.range n, c k * f k t‖ ≤
        t * L * (∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ)) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hid : (rho ξ : ℂ) * f0 t - ∑ k ∈ Finset.range n, c k * f k t =
          (rho ξ : ℂ) * (t : ℂ) * Gh (t * ξ) * (Complex.exp (-(Complex.I * ((a t : ℝ) : ℂ))) -
            ∑ k ∈ Finset.range n, (-(Complex.I * ((a t : ℝ) : ℂ))) ^ k / (k.factorial : ℂ)) := by
        rw [mul_sub, Finset.mul_sum]
        congr 1
        · simp only [f0]; ring
        · refine Finset.sum_congr rfl fun k _ => ?_
          simp only [c, f, c08_low_operators_m, ha]
          push_cast
          rw [← neg_mul, mul_pow, mul_pow]
          ring
      rw [hid, norm_mul, norm_mul, norm_mul]
      have hr : ‖(rho ξ : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (c08_aux_rho_props.2.2.2 ξ).1]
        exact (c08_aux_rho_props.2.2.2 ξ).2
      have htn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      rcases eq_or_ne (rho ξ) 0 with h0 | h0
      · rw [h0]; simp only [Complex.ofReal_zero, norm_zero, zero_mul]
        exact mul_nonneg (mul_nonneg ht.1 hL0) (he0 n)
      · have hξ : |ξ| ≤ 2 := by
          by_contra hc; exact h0 (c08_aux_rho_props.1 ξ (lt_of_not_ge hc))
        have hz : ‖-(Complex.I * ((a t : ℝ) : ℂ))‖ ≤ M := by
          rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          simp only [ha]
          have h1 : t ^ (p + 1) ≤ 1 := Real.rpow_le_one ht.1 ht.2 (by linarith)
          have h2 : 0 ≤ t ^ (p + 1) := Real.rpow_nonneg ht.1 _
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t ^ (p + 1))]
          have hP : |Phi0 p ξ| ≤ M := by
            unfold Phi0
            rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg ξ) p),
              abs_of_pos (by linarith : (0:ℝ) < p + 1), hM]
            apply div_le_div_of_nonneg_right _ (by linarith)
            rw [← Real.rpow_one_add' (abs_nonneg ξ) (by linarith)]
            rw [add_comm]
            exact Real.rpow_le_rpow (abs_nonneg ξ) hξ (by linarith)
          calc (1 - t ^ (p + 1)) * |Phi0 p ξ| ≤ 1 * M := by
                apply mul_le_mul (by linarith) hP (abs_nonneg _) zero_le_one
            _ = M := one_mul M
        have hR := c08_aux_exp_remainder _ M hz n
        rw [htn]
        calc ‖(rho ξ : ℂ)‖ * t * ‖Gh (t * ξ)‖ * ‖Complex.exp (-(Complex.I * ((a t : ℝ) : ℂ))) -
              ∑ k ∈ Finset.range n, (-(Complex.I * ((a t : ℝ) : ℂ))) ^ k / (k.factorial : ℂ)‖
            ≤ 1 * t * L * (∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ)) := by
              have hE := he0 n
              have hRn := norm_nonneg (Complex.exp (-(Complex.I * ((a t : ℝ) : ℂ))) -
                ∑ k ∈ Finset.range n, (-(Complex.I * ((a t : ℝ) : ℂ))) ^ k / (k.factorial : ℂ))
              have A : ‖(rho ξ : ℂ)‖ * t ≤ 1 * t := mul_le_mul_of_nonneg_right hr ht.1
              have B : ‖(rho ξ : ℂ)‖ * t * ‖Gh (t * ξ)‖ ≤ 1 * t * L :=
                mul_le_mul A (hGhb _) (norm_nonneg _) (by linarith [ht.1])
              exact mul_le_mul B hR hRn (by nlinarith [ht.1])
          _ = t * L * (∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ)) := by ring
    calc ‖∫ t in (0:ℝ)..1, ((rho ξ : ℂ) * f0 t - ∑ k ∈ Finset.range n, c k * f k t)‖
        ≤ ∫ t in (0:ℝ)..1, t * L * (∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ)) :=
          intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (Eventually.of_forall fun t ht => hpt t (Set.Ioc_subset_Icc_self ht |> fun h => by
              rw [Set.uIcc_of_le zero_le_one]; exact h))
            (Continuous.intervalIntegrable (by fun_prop) 0 1)
      _ = 1 / 2 * L * (∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ)) := by
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, integral_id]
          ring
  refine ⟨hsum, hlim, hmain, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h2 : Tendsto (fun n => 1 / 2 * L * (∑' k : ℕ, M ^ (k + n) / ((k + n).factorial : ℝ))) atTop (nhds 0) := by
    simpa using hlim.const_mul (1 / 2 * L)
  filter_upwards [(h2.eventually (gt_mem_nhds hε))] with n hn ξ
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hmain n ξ) hn










/-- Blueprint: lem:c08_low_series_identification.  If the partial sums
`S_n = Σ_{k<n} (-i)^k ℳ_k 𝒜_k G / k!` and `S` lie in `X_γ^ℂ` and `‖S_n - S‖_{X_γ^ℂ} → 0`, then
`Ŝ = χ m_G` pointwise and `S(y) = 𝒯_l G(y)` for every `y` (a conditional statement). -/
theorem c08_low_series_identification (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (S : ℝ → ℂ) (hS : S ∈ X_gammaC p γ)
    (hSn : ∀ N : ℕ, (fun y => ∑ k ∈ Finset.range N, (-Complex.I) ^ k / (k.factorial : ℂ) *
        c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) ∈ X_gammaC p γ)
    (hlim : Tendsto (fun N : ℕ => xNorm p γ ((fun y => ∑ k ∈ Finset.range N,
        (-Complex.I) ^ k / (k.factorial : ℂ) *
          c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) - S))
      atTop (nhds 0)) :
    (∀ ξ : ℝ, fourierT S ξ = (rho ξ : ℂ) * T_0_symbol p G ξ) ∧
    ∀ y : ℝ, (T_low p G y : ℂ) = S y := by
  have hp0 : 0 < p := by linarith
  set Sn : ℕ → ℝ → ℂ := fun N y => ∑ k ∈ Finset.range N, (-Complex.I) ^ k / (k.factorial : ℂ) *
    c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y with hSndef
  set m : ℝ → ℂ := fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ with hm
  have hSc : Continuous S := hS.1.1.continuous
  obtain ⟨hSi, -⟩ := c08_aux_XC_L1 hγ hSc hS.2
  set I0 := ∫ y, jb y ^ (-γ)
  -- transforms of the partial sums
  have hFk : ∀ k, Integrable (c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ))) :=
    fun k => ((c08_convolution_fourier p hp hp1 k).2.2 _
      (c08_average_fourier p γ hp hp1 hγ G hG k).2.2.1.ofReal).2.1
  have hFSn : ∀ N ξ, fourierT (Sn N) ξ = ∑ k ∈ Finset.range N,
      (-Complex.I) ^ k / (k.factorial : ℂ) * c08_low_operators_m p k ξ *
        fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ := by
    intro N ξ
    rw [hSndef, c08_aux_fourierT_sum _ _ _ (fun k _ => hFk k) ξ]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := ((c08_convolution_fourier p hp hp1 k).2.2 (fun x => (c08_low_operators p k G x : ℂ))
      (c08_average_fourier p γ hp hp1 hγ G hG k).2.2.1.ofReal).2.2.2 ξ
    rw [this, mul_assoc]
  have hSni : ∀ N, Integrable (Sn N) := by
    intro N
    simp only [hSndef]
    exact integrable_finsetSum _ fun k _ => (hFk k).const_mul _
  have hUnif := (c08_low_fourier_series p γ hp hp1 hγ G hG).2.2.2
  have hF : ∀ ξ, fourierT S ξ = m ξ := by
    intro ξ
    have t1 : Tendsto (fun N => fourierT (Sn N) ξ) atTop (nhds (m ξ)) := by
      simp_rw [hFSn]; exact hUnif.tendsto_at ξ
    have t2 : Tendsto (fun N => fourierT (Sn N) ξ) atTop (nhds (fourierT S ξ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by
        simpa using hlim.mul_const I0)
      have hfin : X_gamma_norm p γ (Sn N - S) < ⊤ :=
        lt_of_le_of_lt (c08_aux_X_norm_sub_le p γ (hSn N).1 hS.1)
          (ENNReal.add_lt_top.2 ⟨(hSn N).2, hS.2⟩)
      have hc : Continuous (Sn N - S) := (hSn N).1.1.continuous.sub hSc
      rw [c08_aux_fourierT_sub (hSni N) hSi]
      exact (c08_aux_norm_fourierT_le_C _ ξ).trans (c08_aux_XC_L1 hγ hc hfin).2
    exact tendsto_nhds_unique t2 t1
  refine ⟨hF, fun y => ?_⟩
  obtain ⟨⟨-, hmc, hmb, -⟩, hherm, -⟩ := c08_free_ode p γ hp hp1 hγ G hG
  have hρi : Integrable (fun ξ => (rho ξ : ℂ)) := by
    have := c08_aux_m_integrable p hp0 0
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp [c08_low_operators_m]
  have hmi : Integrable m := Integrable.mul_bdd hρi hmc.aestronglyMeasurable
    (Eventually.of_forall fun ξ => hmb ξ)
  have hFS : fourierT S = m := funext hF
  have hinv : invFourierT m y = S y := by
    rw [← hFS]; exact c08_aux_invFourierT_fourierT hSc hSi (hFS ▸ hmi) y
  have hHerm : ∀ ξ, m (-ξ) = (starRingEnd ℂ) (m ξ) := by
    intro ξ
    simp only [hm, map_mul, Complex.conj_ofReal, hherm ξ, c08_aux_rho_props.2.2.1 ξ]
  have him := c08_aux_invFourierT_im hHerm y
  unfold T_low
  rw [← hinv]
  exact Complex.ext (by simp only [Complex.ofReal_re]; rfl) (by simp [him])

/-- Blueprint: lem:c08_low_series.  Fourier transforms of `𝒜_k G` and `ℳ_k H`, the uniformly
convergent series `χ m_G = Σ (-i)^k/k! m_k (𝒜_k G)^`, and `𝒯_l G = Σ (-i)^k/k! ℳ_k 𝒜_k G` whenever
the latter series converges in `X_γ^ℂ`. -/
theorem c08_low_series (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) :
    (∀ (k : ℕ) (ξ : ℝ), fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ =
      ∫ t in (0 : ℝ)..1, (t : ℂ) * (((1 - t ^ (p + 1)) ^ k : ℝ) : ℂ) *
        fourierT (fun x => (G x : ℂ)) (t * ξ)) ∧
    (∀ (k : ℕ) (H : ℝ → ℂ), Integrable H → ∀ ξ : ℝ,
      fourierT (c08_low_operators_M p k H) ξ = c08_low_operators_m p k ξ * fourierT H ξ) ∧
    TendstoUniformly
      (fun (N : ℕ) (ξ : ℝ) => ∑ k ∈ Finset.range N,
        (-Complex.I) ^ k / (k.factorial : ℂ) * c08_low_operators_m p k ξ *
          fourierT (fun y => (c08_low_operators p k G y : ℂ)) ξ)
      (fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ) atTop ∧
    ∀ S : ℝ → ℂ, S ∈ X_gammaC p γ →
      (∀ N : ℕ, (fun y => ∑ k ∈ Finset.range N, (-Complex.I) ^ k / (k.factorial : ℂ) *
          c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) ∈ X_gammaC p γ) →
      Tendsto (fun N : ℕ => xNorm p γ ((fun y => ∑ k ∈ Finset.range N,
          (-Complex.I) ^ k / (k.factorial : ℂ) *
            c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) - S))
        atTop (nhds 0) →
      ∀ y : ℝ, (T_low p G y : ℂ) = S y := by
  refine ⟨fun k ξ => (c08_average_fourier p γ hp hp1 hγ G hG k).2.2.2.2 ξ,
    fun k H hH ξ => ((c08_convolution_fourier p hp hp1 k).2.2 H hH).2.2.2 ξ,
    (c08_low_fourier_series p γ hp hp1 hγ G hG).2.2.2,
    fun S hS hSn hlim => (c08_low_series_identification p γ hp hp1 hγ G hG S hS hSn hlim).2⟩

/-- A.e. bound for `G'` on `(-∞,0]` for `G ∈ Y_γ`: `|G'| ≤ ‖G‖⟨y⟩^{-γ-1}`. -/
theorem c08_aux_Y_ae_neg {p γ : ℝ} {G : ℝ → ℝ} (hG : G ∈ Y_gamma p γ) :
    ∀ᵐ y ∂(volume : Measure ℝ), y ≤ 0 → |deriv G y| ≤ yNorm p γ G * jb y ^ (-γ - 1) := by
  have hfin := hG.2
  unfold Y_gamma_norm at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have hx : yNorm p γ G = _ := ENNReal.toReal_add h1.ne h2.ne
  set E1 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖)))
      (volume.restrict (Ici 0))
  set E2 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖)))
      (volume.restrict (Iic 0))
  have hN2 : E2.toReal ≤ yNorm p γ G := by rw [hx]; linarith [ENNReal.toReal_nonneg (a := E1)]
  have := c08_aux_ae_le_essSup_toReal h2
  rw [ae_restrict_iff' measurableSet_Iic] at this
  filter_upwards [this] with y hy hy0
  have hy := hy hy0
  have hj := c08_aux_jb_pos y
  have hg := Real.rpow_pos_of_pos hj γ
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hy
  have a0 := abs_nonneg (G y); have a1 := abs_nonneg (deriv G y)
  have h3 : jb y ^ (γ + 1) * |deriv G y| ≤ yNorm p γ G := by
    rw [Real.rpow_add hj, Real.rpow_one]
    nlinarith [mul_nonneg hg.le a0]
  have h4 := c08_aux_div_weight h3
  rwa [show -(γ + 1) = -γ - 1 by ring] at h4

/-- An a.e. bound by a continuous function on `(-∞,0)` for the derivative of a locally Lipschitz
function holds everywhere on `(-∞,0)`. -/
theorem c08_aux_deriv_bound_everywhere {G w : ℝ → ℝ} (hG : LocallyLipschitz G)
    (hw : ContinuousOn w (Iio 0)) (hw0 : ∀ x, x < 0 → 0 ≤ w x)
    (h : ∀ᵐ x ∂(volume : Measure ℝ), x < 0 → |deriv G x| ≤ w x) :
    ∀ x, x < 0 → |deriv G x| ≤ w x := by
  intro x hx
  by_cases hd : DifferentiableAt ℝ G x
  swap
  · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]; exact hw0 x hx
  refine le_of_forall_pos_lt_add (fun η hη => ?_)
  have hwc : ContinuousAt w x := hw.continuousAt (Iio_mem_nhds hx)
  obtain ⟨δ, hδ, hδw⟩ := Metric.continuousAt_iff.1 hwc (η / 2) (by linarith)
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt).mono_left
    (nhdsWithin_mono x (show Ioi x ⊆ {x}ᶜ from fun s (hs : x < s) => ne_of_gt hs))
  have hev : ∀ᶠ s in nhdsWithin x (Ioi x), |slope G x s| ≤ w x + η / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show x < x + min (δ / 2) (-x / 2) by
      have : 0 < min (δ / 2) (-x / 2) := lt_min (by linarith) (by linarith)
      linarith)] with s hs
    have hs1 : s - x ≤ δ / 2 := by linarith [hs.2, min_le_left (δ / 2) (-x / 2)]
    have hs2 : s < 0 := by linarith [hs.2, min_le_right (δ / 2) (-x / 2)]
    have hxs : x ≤ s := hs.1.le
    have hftc := c02_aux_ftc hG x s
    have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc x s → ‖deriv G t‖ ≤ w x + η / 2 := by
      filter_upwards [h] with t ht htI
      have htneg : t < 0 := lt_of_le_of_lt htI.2 hs2
      refine (Real.norm_eq_abs _ ▸ ht htneg).trans ?_
      have : dist t x < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [htI.1])]; linarith [htI.2]
      have := hδw this
      rw [Real.dist_eq] at this
      linarith [(abs_lt.1 this).2]
    have hint := intervalIntegral.norm_integral_le_of_norm_le hxs hb
      (intervalIntegrable_const (μ := volume) (c := w x + η / 2))
    rw [hftc.1, intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs] at hint
    rw [slope_def_field, abs_div, abs_of_pos (sub_pos.2 hs.1), div_le_iff₀ (sub_pos.2 hs.1)]
    linarith
  have hlim := le_of_tendsto hslope.abs hev
  linarith

theorem c08_aux_diff_of_comp_div {G : ℝ → ℝ} {t s : ℝ} (ht : t ≠ 0)
    (h : DifferentiableAt ℝ (fun s => G (s / t)) s) : DifferentiableAt ℝ G (s / t) := by
  have h' : DifferentiableAt ℝ (fun s => G (s / t)) ((s / t) * t) := by
    rwa [div_mul_cancel₀ s ht]
  have hm : DifferentiableAt ℝ (fun v : ℝ => v * t) (s / t) := differentiableAt_id.mul_const t
  have := h'.comp (s / t) hm
  convert this using 1
  funext v; simp [Function.comp_def, mul_div_cancel_right₀ v ht]

theorem c08_aux_diff_of_comp_inv {G : ℝ → ℝ} {y t : ℝ} (hy : y ≠ 0) (ht : t ≠ 0)
    (h : DifferentiableAt ℝ (fun t => G (y / t)) t) : DifferentiableAt ℝ G (y / t) := by
  have h' : DifferentiableAt ℝ (fun t => G (y / t)) (y / (y / t)) := by
    rwa [div_div_cancel₀ hy]
  have hm : DifferentiableAt ℝ (fun v : ℝ => y / v) (y / t) :=
    (differentiableAt_const y).div differentiableAt_id (div_ne_zero hy ht)
  have := h'.comp (y / t) hm
  convert this using 1
  funext v
  by_cases hv : v = 0
  · simp [hv]
  · simp [Function.comp_def, div_div_cancel₀ hy]

/-- A.e. chain rule: for `t > 0`, `d/ds G(s/t) = t⁻¹ G'(s/t)` for a.e. `s`. -/
theorem c08_aux_ae_chain_div {G : ℝ → ℝ} (hG : LocallyLipschitz G) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ s ∂(volume : Measure ℝ), HasDerivAt (fun s => G (s / t)) (t⁻¹ * deriv G (s / t)) s := by
  have hg : LocallyLipschitz (fun s => G (s / t)) :=
    hG.comp ((contDiff_id.div_const (𝕜 := ℝ) t).locallyLipschitz)
  filter_upwards [c08_aux_ae_differentiable hg] with s hs
  have hGd := c08_aux_diff_of_comp_div ht.ne' hs
  have := hGd.hasDerivAt.comp s ((hasDerivAt_id s).div_const t)
  convert this using 1
  · rfl
  · rw [one_div, mul_comm]

/-- FTC along `s ↦ G(s/t)`. -/
theorem c08_aux_ftc_div {G : ℝ → ℝ} (hG : LocallyLipschitz G) {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    G (b / t) - G (a / t) = ∫ s in a..b, t⁻¹ * deriv G (s / t) := by
  have hg : LocallyLipschitz (fun s => G (s / t)) :=
    hG.comp ((contDiff_id.div_const (𝕜 := ℝ) t).locallyLipschitz)
  obtain ⟨K, hK⟩ := (hg.locallyLipschitzOn (s := uIcc a b)).exists_lipschitzOnWith_of_compact
    isCompact_uIcc
  have hac := hK.absolutelyContinuousOnInterval
  rw [← hac.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [c08_aux_ae_chain_div hG ht] with s hs _
  exact hs.deriv

/-- Pointwise bound `|t⁻¹ G'(s/t)| ≤ N |b|^{-γ-1}` for `s ≤ b < 0`, `t ∈ (0,1]`. -/
theorem c08_aux_Dbound {G : ℝ → ℝ} {N γ : ℝ} (hN : 0 ≤ N) (hγ : 0 ≤ γ)
    (hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1)) {s b t : ℝ} (hb : b < 0) (hs : s ≤ b)
    (ht : t ∈ Ioc (0:ℝ) 1) : |t⁻¹ * deriv G (s / t)| ≤ N * |b| ^ (-γ - 1) := by
  have ht0 := ht.1
  have hst : s / t < 0 := div_neg_of_neg_of_pos (by linarith) ht0
  have h1 := hG' (s / t) hst
  have hb0 : 0 < |b| := abs_pos.2 hb.ne
  have habs : |b| / t ≤ jb (s / t) := by
    have : |b| ≤ |s| := by rw [abs_of_neg hb, abs_of_neg (by linarith)]; linarith
    calc |b| / t ≤ |s| / t := div_le_div_of_nonneg_right this ht0.le
      _ = |s / t| := by rw [abs_div, abs_of_pos ht0]
      _ ≤ jb (s / t) := by unfold jb; exact Real.abs_le_sqrt (by nlinarith [sq_abs (s / t)])
  have h2 : jb (s / t) ^ (-γ - 1) ≤ (|b| / t) ^ (-γ - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) habs (by linarith)
  have h3 : (|b| / t) ^ (-γ - 1) = t ^ (γ + 1) * |b| ^ (-γ - 1) := by
    rw [Real.div_rpow hb0.le ht0.le, show -γ - 1 = -(γ + 1) by ring, Real.rpow_neg ht0.le]
    field_simp
  have h4 : t⁻¹ * t ^ (γ + 1) ≤ 1 := by
    rw [Real.rpow_add ht0, Real.rpow_one, show t⁻¹ * (t ^ γ * t) = t ^ γ * (t⁻¹ * t) by ring,
      inv_mul_cancel₀ ht0.ne', mul_one]
    exact Real.rpow_le_one ht0.le ht.2 hγ
  rw [abs_mul, abs_inv, abs_of_pos ht0]
  have hb1 : 0 ≤ |b| ^ (-γ - 1) := (Real.rpow_pos_of_pos hb0 _).le
  calc t⁻¹ * |deriv G (s / t)| ≤ t⁻¹ * (N * (t ^ (γ + 1) * |b| ^ (-γ - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ht0.le)
        rw [← h3]; exact h1.trans (mul_le_mul_of_nonneg_left h2 hN)
    _ = N * |b| ^ (-γ - 1) * (t⁻¹ * t ^ (γ + 1)) := by ring
    _ ≤ N * |b| ^ (-γ - 1) * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = N * |b| ^ (-γ - 1) := mul_one _

/-- Integral representation `A_ω(y₁) - A_ω(y₀) = ∫_{y₀}^{y₁} D_ω` on the negative half-line. -/
theorem c08_aux_Aw_repr {G : ℝ → ℝ} {N γ : ℝ} (hN : 0 ≤ N) (hγ : 0 ≤ γ)
    (hGl : LocallyLipschitz G) (hGb : ∀ x, |G x| ≤ N)
    (hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1)) {ω : ℝ → ℝ} (hω : Continuous ω)
    {y0 y1 : ℝ} (h01 : y0 ≤ y1) (h1 : y1 < 0) :
    (∫ t in Ioc (0:ℝ) 1, ω t * G (y1 / t)) - (∫ t in Ioc (0:ℝ) 1, ω t * G (y0 / t)) =
      ∫ s in y0..y1, ∫ t in Ioc (0:ℝ) 1, ω t * (t⁻¹ * deriv G (s / t)) := by
  obtain ⟨Ω, hΩ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hω.continuousOn
  have hΩ0 : 0 ≤ Ω := (norm_nonneg _).trans (hΩ 0 ⟨le_rfl, zero_le_one⟩)
  have hGc : Continuous G := hGl.continuous
  have hAi : ∀ y, IntegrableOn (fun t => ω t * G (y / t)) (Ioc (0:ℝ) 1) := by
    intro y
    refine Measure.integrableOn_of_bounded (M := Ω * N) (by simp) ?_ ?_
    · exact (hω.measurable.mul (hGc.measurable.comp (measurable_const.div measurable_id))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      rw [norm_mul, Real.norm_eq_abs (G _)]
      exact mul_le_mul (hΩ t (Ioc_subset_Icc_self ht)) (hGb _) (abs_nonneg _) hΩ0
  set F : ℝ × ℝ → ℝ := fun q => ω q.1 * (q.1⁻¹ * deriv G (q.2 / q.1)) with hF
  have hFm : Measurable F := (hω.measurable.comp measurable_fst).mul
    ((measurable_fst.inv).mul ((measurable_deriv G).comp (measurable_snd.div measurable_fst)))
  have hFi : Integrable F ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc y0 y1))) := by
    rw [Measure.prod_restrict]
    refine Measure.integrableOn_of_bounded (M := Ω * (N * |y1| ^ (-γ - 1))) ?_ hFm.aestronglyMeasurable ?_
    · rw [Measure.prod_prod]; simp
    · refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2
        (Eventually.of_forall fun q hq => ?_)
      simp only [hF, norm_mul]
      exact mul_le_mul (hΩ q.1 (Ioc_subset_Icc_self hq.1))
        (by rw [← norm_mul, Real.norm_eq_abs]; exact c08_aux_Dbound hN hγ hG' h1 hq.2.2 hq.1)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hΩ0
  rw [← integral_sub (hAi y1) (hAi y0), intervalIntegral.integral_of_le h01]
  calc ∫ t in Ioc (0:ℝ) 1, (ω t * G (y1 / t) - ω t * G (y0 / t))
      = ∫ t in Ioc (0:ℝ) 1, ∫ s in Ioc y0 y1, F (t, s) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        simp only [hF]
        rw [← mul_sub, c08_aux_ftc_div hGl ht.1 y0 y1, intervalIntegral.integral_of_le h01,
          ← integral_const_mul]
    _ = ∫ s in Ioc y0 y1, ∫ t in Ioc (0:ℝ) 1, F (t, s) := integral_integral_swap hFi
    _ = _ := rfl

/-- `t ↦ y / max t ε` is Lipschitz (`ε > 0`). -/
theorem c08_aux_lip_inv_clamp (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    LocallyLipschitz (fun t : ℝ => y / max t ε) := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨|y| / ε ^ 2, by positivity⟩) fun a b => ?_).locallyLipschitz
  have ha : ε ≤ max a ε := le_max_right _ _
  have hb : ε ≤ max b ε := le_max_right _ _
  have ha0 : 0 < max a ε := lt_of_lt_of_le hε ha
  have hb0 : 0 < max b ε := lt_of_lt_of_le hε hb
  simp only [Real.dist_eq]
  rw [div_sub_div _ _ ha0.ne' hb0.ne', abs_div, abs_mul, abs_of_pos ha0, abs_of_pos hb0]
  show _ ≤ (|y| / ε ^ 2) * |a - b|
  have hm : |max b ε - max a ε| ≤ |a - b| := by
    rw [abs_sub_comm]; exact abs_max_sub_max_le_abs a b ε
  have hden : ε ^ 2 ≤ max a ε * max b ε := by nlinarith
  rw [show y * max b ε - max a ε * y = y * (max b ε - max a ε) by ring, abs_mul]
  rw [div_le_iff₀ (mul_pos ha0 hb0)]
  calc |y| * |max b ε - max a ε| ≤ |y| * |a - b| := mul_le_mul_of_nonneg_left hm (abs_nonneg y)
    _ = |y| / ε ^ 2 * |a - b| * ε ^ 2 := by field_simp
    _ ≤ |y| / ε ^ 2 * |a - b| * (max a ε * max b ε) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- For `y ≠ 0`, `G` is differentiable at `y/t` for a.e. `t > 0`. -/
theorem c08_aux_ae_diff_inv {G : ℝ → ℝ} (hGl : LocallyLipschitz G) {y : ℝ} (hy : y ≠ 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), 0 < t → DifferentiableAt ℝ G (y / t) := by
  have hn : ∀ n : ℕ, ∀ᵐ t ∂(volume : Measure ℝ), 1 / ((n : ℝ) + 1) < t →
      DifferentiableAt ℝ G (y / t) := by
    intro n
    set ε : ℝ := 1 / ((n : ℝ) + 1)
    have hε : 0 < ε := by positivity
    have hg := hGl.comp (c08_aux_lip_inv_clamp y hε)
    filter_upwards [c08_aux_ae_differentiable hg] with t ht htε
    have heq : (fun t => G (y / max t ε)) =ᶠ[𝓝 t] fun t => G (y / t) := by
      filter_upwards [Ioi_mem_nhds htε] with s hs
      have hs' : ε < s := hs
      show G (y / max s ε) = G (y / s)
      rw [max_eq_left hs'.le]
    exact c08_aux_diff_of_comp_inv hy (ne_of_gt (lt_trans hε htε))
      ((heq.differentiableAt_iff).1 ht)
  rw [← ae_all_iff] at hn
  filter_upwards [hn] with t ht ht0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht0
  exact ht n hn

/-- Integration by parts in `t`: `y D_ω(y) = A_{ω+tω'}(y) - ω(1) G(y)` for `y < 0`. -/
theorem c08_aux_Aw_ibp {G : ℝ → ℝ} {N γ : ℝ} (hN : 0 ≤ N) (hγ : 0 ≤ γ)
    (hGl : LocallyLipschitz G) (hGb : ∀ x, |G x| ≤ N)
    (hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1)) {ω ω' : ℝ → ℝ} (hω : Continuous ω)
    (hω' : Continuous ω') (hd : ∀ t, HasDerivAt ω (ω' t) t) {y : ℝ} (hy : y < 0) :
    y * (∫ t in Ioc (0:ℝ) 1, ω t * (t⁻¹ * deriv G (y / t))) =
      (∫ t in Ioc (0:ℝ) 1, (ω t + t * ω' t) * G (y / t)) - ω 1 * G y := by
  obtain ⟨Ω, hΩ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hω.continuousOn
  obtain ⟨Ω', hΩ'⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hω'.continuousOn
  have hΩ0 : 0 ≤ Ω := (norm_nonneg _).trans (hΩ 0 ⟨le_rfl, zero_le_one⟩)
  have hΩ0' : 0 ≤ Ω' := (norm_nonneg _).trans (hΩ' 0 ⟨le_rfl, zero_le_one⟩)
  have hGc : Continuous G := hGl.continuous
  set P : ℝ → ℝ := fun t => (ω t + t * ω' t) * G (y / t) with hP
  set Q : ℝ → ℝ := fun t => ω t * (t⁻¹ * deriv G (y / t)) with hQ
  set BP := (Ω + Ω') * N
  set BQ := Ω * (N * |y| ^ (-γ - 1))
  have hPb : ∀ t ∈ Ioc (0:ℝ) 1, ‖P t‖ ≤ BP := by
    intro t ht
    simp only [hP, norm_mul, Real.norm_eq_abs]
    have h1 : |ω t + t * ω' t| ≤ Ω + Ω' := by
      have a := hΩ t (Ioc_subset_Icc_self ht); have b := hΩ' t (Ioc_subset_Icc_self ht)
      rw [Real.norm_eq_abs] at a b
      calc |ω t + t * ω' t| ≤ |ω t| + |t| * |ω' t| := (abs_add_le _ _).trans (by rw [abs_mul])
        _ ≤ Ω + 1 * Ω' := by
          gcongr; rw [abs_of_pos ht.1]; exact ht.2
        _ = Ω + Ω' := by ring
    exact mul_le_mul h1 (hGb _) (abs_nonneg _) (by positivity)
  have hQb : ∀ t ∈ Ioc (0:ℝ) 1, ‖Q t‖ ≤ BQ := by
    intro t ht
    simp only [hQ, norm_mul]
    exact mul_le_mul (hΩ t (Ioc_subset_Icc_self ht))
      (by rw [← norm_mul, Real.norm_eq_abs]; exact c08_aux_Dbound hN hγ hG' hy le_rfl ht)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hΩ0
  have hPm : Measurable P := ((hω.measurable.add (measurable_id.mul hω'.measurable)).mul
    (hGc.measurable.comp (measurable_const.div measurable_id)))
  have hQm : Measurable Q := hω.measurable.mul (measurable_id.inv.mul
    ((measurable_deriv G).comp (measurable_const.div measurable_id)))
  have hPi : ∀ a b, 0 ≤ a → b ≤ 1 → IntegrableOn P (Ioc a b) := fun a b ha hb =>
    Measure.integrableOn_of_bounded (M := BP) (by simp) hPm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht =>
        hPb t ⟨lt_of_le_of_lt ha ht.1, ht.2.trans hb⟩))
  have hQi : ∀ a b, 0 ≤ a → b ≤ 1 → IntegrableOn Q (Ioc a b) := fun a b ha hb =>
    Measure.integrableOn_of_bounded (M := BQ) (by simp) hQm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht =>
        hQb t ⟨lt_of_le_of_lt ha ht.1, ht.2.trans hb⟩))
  -- pointwise derivative of `h(t) = t ω(t) G(y/t)`
  have hderiv : ∀ t, 0 < t → DifferentiableAt ℝ G (y / t) →
      HasDerivAt (fun t => t * ω t * G (y / t)) (P t - y * Q t) t := by
    intro t ht hGd
    have h1 : HasDerivAt (fun t => y / t) (y * -(t ^ 2)⁻¹) t := by
      have := (hasDerivAt_inv ht.ne').const_mul y
      simpa [div_eq_mul_inv] using this
    have h2 := hGd.hasDerivAt.comp t h1
    have h3 := ((hasDerivAt_id t).mul (hd t)).mul h2
    have hf : (fun t => t * ω t * G (y / t)) = id * ω * G ∘ HDiv.hDiv y := rfl
    rw [hf]
    convert h3 using 1
    show (ω t + t * ω' t) * G (y / t) - y * (ω t * (t⁻¹ * deriv G (y / t))) = _
    simp only [id, Function.comp_def, Pi.mul_apply]
    field_simp
    ring
  have hae := c08_aux_ae_diff_inv hGl hy.ne
  -- FTC on `[ε, 1]`
  have hω1 : ContDiff ℝ 1 ω := contDiff_one_iff_deriv.2 ⟨fun t => (hd t).differentiableAt,
    by rw [show deriv ω = ω' from funext fun t => (hd t).deriv]; exact hω'⟩
  have key : ∀ ε, 0 < ε → ε < 1 →
      ω 1 * G y - ε * ω ε * G (y / ε) = (∫ t in Ioc ε 1, P t) - y * ∫ t in Ioc ε 1, Q t := by
    intro ε hε0 hε1
    set hε : ℝ → ℝ := fun t => t * ω t * G (y / max t ε)
    have hl : LocallyLipschitz hε := c08_aux_locallyLipschitz_mul
      (c08_aux_locallyLipschitz_mul LocallyLipschitz.id hω1.locallyLipschitz)
      (hGl.comp (c08_aux_lip_inv_clamp y hε0))
    obtain ⟨K, hK⟩ := (hl.locallyLipschitzOn (s := uIcc ε 1)).exists_lipschitzOnWith_of_compact
      isCompact_uIcc
    have hftc := hK.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    have e1 : hε 1 = ω 1 * G y := by simp only [hε, max_eq_left hε1.le, one_mul, div_one]
    have e2 : hε ε = ε * ω ε * G (y / ε) := by simp only [hε, max_self]
    rw [e1, e2] at hftc
    rw [← hftc, intervalIntegral.integral_of_le hε1.le, ← integral_const_mul, ← integral_sub
      (hPi ε 1 hε0.le le_rfl) ((hQi ε 1 hε0.le le_rfl).const_mul y)]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have h1null : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := compl_mem_ae_iff.2 (measure_singleton 1)
    filter_upwards [hae, h1null] with t ht ht1 htI
    have htpos : 0 < t := lt_trans hε0 htI.1
    have heq : hε =ᶠ[𝓝 t] fun t => t * ω t * G (y / t) := by
      filter_upwards [Ioi_mem_nhds htI.1] with s hs
      have hs' : ε < s := hs
      simp only [hε, max_eq_left hs'.le]
    rw [heq.deriv_eq, (hderiv t htpos (ht htpos)).deriv]
  -- let `ε → 0`
  set E := (∫ t in Ioc (0:ℝ) 1, P t) - ω 1 * G y - y * ∫ t in Ioc (0:ℝ) 1, Q t
  have hsplit : ∀ (f : ℝ → ℝ), (∀ a b, 0 ≤ a → b ≤ 1 → IntegrableOn f (Ioc a b)) → ∀ ε, 0 < ε → ε < 1 →
      ∫ t in Ioc (0:ℝ) 1, f t = (∫ t in Ioc (0:ℝ) ε, f t) + ∫ t in Ioc ε 1, f t := by
    intro f hf ε hε0 hε1
    rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hf 0 ε le_rfl hε1.le) (hf ε 1 hε0.le le_rfl), Ioc_union_Ioc_eq_Ioc hε0.le hε1.le]
  have hsmall : ∀ (f : ℝ → ℝ) (B : ℝ), (∀ t ∈ Ioc (0:ℝ) 1, ‖f t‖ ≤ B) → ∀ ε, 0 < ε → ε < 1 →
      ‖∫ t in Ioc (0:ℝ) ε, f t‖ ≤ B * ε := by
    intro f B hB ε hε0 hε1
    have := norm_setIntegral_le_of_norm_le_const (s := Ioc (0:ℝ) ε) (C := B) (measure_Ioc_lt_top (μ := (volume : Measure ℝ)))
      (fun t ht => hB t ⟨ht.1, ht.2.trans hε1.le⟩)
    simpa [Real.volume_Ioc, ENNReal.toReal_ofReal hε0.le, max_eq_left hε0.le] using this
  have hbound : ∀ ε, 0 < ε → ε < 1 → |E| ≤ ε * (BP + |y| * BQ + Ω * N) := by
    intro ε hε0 hε1
    have hk := key ε hε0 hε1
    have hE : E = (∫ t in Ioc (0:ℝ) ε, P t) - y * (∫ t in Ioc (0:ℝ) ε, Q t) - ε * ω ε * G (y / ε) := by
      simp only [E]
      rw [hsplit P hPi ε hε0 hε1, hsplit Q hQi ε hε0 hε1]
      linear_combination (-1 : ℝ) * hk
    rw [hE]
    have a1 := hsmall P BP hPb ε hε0 hε1
    have a2 := hsmall Q BQ hQb ε hε0 hε1
    rw [Real.norm_eq_abs] at a1 a2
    have a3 : |ε * ω ε * G (y / ε)| ≤ ε * (Ω * N) := by
      rw [abs_mul, abs_mul, abs_of_pos hε0, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hε0.le
      exact mul_le_mul (by simpa using hΩ ε ⟨hε0.le, hε1.le⟩) (hGb _) (abs_nonneg _) hΩ0
    have a4 : |y * ∫ t in Ioc (0:ℝ) ε, Q t| ≤ |y| * (BQ * ε) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left a2 (abs_nonneg y)
    calc |(∫ t in Ioc (0:ℝ) ε, P t) - y * (∫ t in Ioc (0:ℝ) ε, Q t) - ε * ω ε * G (y / ε)|
        ≤ |∫ t in Ioc (0:ℝ) ε, P t| + |y * ∫ t in Ioc (0:ℝ) ε, Q t| + |ε * ω ε * G (y / ε)| := by
          have t1 := norm_sub_le ((∫ t in Ioc (0:ℝ) ε, P t) - y * (∫ t in Ioc (0:ℝ) ε, Q t))
            (ε * ω ε * G (y / ε))
          have t2 := norm_sub_le (∫ t in Ioc (0:ℝ) ε, P t) (y * (∫ t in Ioc (0:ℝ) ε, Q t))
          simp only [Real.norm_eq_abs] at t1 t2
          linarith
      _ ≤ BP * ε + |y| * (BQ * ε) + ε * (Ω * N) := by linarith
      _ = ε * (BP + |y| * BQ + Ω * N) := by ring
  have hE0 : E = 0 := by
    by_contra hne
    have hpos : 0 < |E| := abs_pos.2 hne
    set C := BP + |y| * BQ + Ω * N + 1
    have hC : 0 < C := by
      have : 0 ≤ BP := by positivity
      have : 0 ≤ BQ := by have := Real.rpow_nonneg (abs_nonneg y) (-γ - 1); positivity
      positivity
    set ε := min (1 / 2) (|E| / (2 * C))
    have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have h1 := hbound ε hε0 hε1
    have h2 : ε * (BP + |y| * BQ + Ω * N) ≤ ε * C := mul_le_mul_of_nonneg_left (by simp [C]) hε0.le
    have h3 : ε * C ≤ |E| / 2 := by
      calc ε * C ≤ |E| / (2 * C) * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
        _ = |E| / 2 := by field_simp
    linarith
  linear_combination (-1 : ℝ) * hE0

theorem c08_aux_Aw_cont {G : ℝ → ℝ} {N : ℝ} (hGc : Continuous G) (hGb : ∀ x, |G x| ≤ N)
    {ω : ℝ → ℝ} (hω : Continuous ω) :
    Continuous (fun y => ∫ t in Ioc (0:ℝ) 1, ω t * G (y / t)) := by
  obtain ⟨Ω, hΩ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hω.continuousOn
  have hΩ0 : 0 ≤ Ω := (norm_nonneg _).trans (hΩ 0 ⟨le_rfl, zero_le_one⟩)
  refine continuous_of_dominated (bound := fun _ => Ω * N) (fun y =>
    (hω.measurable.mul (hGc.measurable.comp (measurable_const.div measurable_id))).aestronglyMeasurable)
    (fun y => (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_))
    (Measure.integrableOn_of_bounded (M := Ω * N)
      (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := 0) (b := 1)).ne
      aestronglyMeasurable_const (Eventually.of_forall fun _ => le_of_eq (by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hΩ0 ((abs_nonneg _).trans (hGb 0)))])))
    (Eventually.of_forall fun t => ?_)
  · rw [norm_mul, Real.norm_eq_abs (G _)]
    exact mul_le_mul (hΩ t (Ioc_subset_Icc_self ht)) (hGb _) (abs_nonneg _) hΩ0
  · exact continuous_const.mul (hGc.comp (continuous_id.div_const t))

theorem c08_aux_Dw_bound {G : ℝ → ℝ} {N γ : ℝ} (hN : 0 ≤ N) (hγ : 0 ≤ γ)
    (hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1)) {ω : ℝ → ℝ} {Ω : ℝ} (hΩ0 : 0 ≤ Ω)
    (hΩ : ∀ t ∈ Icc (0:ℝ) 1, ‖ω t‖ ≤ Ω) {s b : ℝ} (hb : b < 0) (hs : s ≤ b) :
    |∫ t in Ioc (0:ℝ) 1, ω t * (t⁻¹ * deriv G (s / t))| ≤ Ω * (N * |b| ^ (-γ - 1)) := by
  rw [← Real.norm_eq_abs]
  have := norm_setIntegral_le_of_norm_le_const (s := Ioc (0:ℝ) 1) (C := Ω * (N * |b| ^ (-γ - 1)))
    (f := fun t => ω t * (t⁻¹ * deriv G (s / t))) (measure_Ioc_lt_top (μ := (volume : Measure ℝ)))
    (fun t ht => by
      rw [norm_mul]
      exact mul_le_mul (hΩ t (Ioc_subset_Icc_self ht))
        (by rw [Real.norm_eq_abs]; exact c08_aux_Dbound hN hγ hG' hb hs ht) (norm_nonneg _) hΩ0)
  simpa [Real.volume_Ioc] using this

/-- Two-sided version of the representation. -/
theorem c08_aux_Aw_repr' {G : ℝ → ℝ} {N γ : ℝ} (hN : 0 ≤ N) (hγ : 0 ≤ γ)
    (hGl : LocallyLipschitz G) (hGb : ∀ x, |G x| ≤ N)
    (hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1)) {ω : ℝ → ℝ} (hω : Continuous ω)
    {y0 y1 : ℝ} (h0 : y0 < 0) (h1 : y1 < 0) :
    (∫ t in Ioc (0:ℝ) 1, ω t * G (y1 / t)) = (∫ t in Ioc (0:ℝ) 1, ω t * G (y0 / t)) +
      ∫ s in y0..y1, ∫ t in Ioc (0:ℝ) 1, ω t * (t⁻¹ * deriv G (s / t)) := by
  rcases le_total y0 y1 with h | h
  · rw [← c08_aux_Aw_repr hN hγ hGl hGb hG' hω h h1]; ring
  · rw [intervalIntegral.integral_symm, ← c08_aux_Aw_repr hN hγ hGl hGb hG' hω h h0]; ring

/-- Blueprint: lem:c08_Ak_formulas.  On `(-∞,0)`, `𝒜_k G ∈ C¹` with
`(𝒜_k G)'(y) = ∫₀¹ (1-t^α)^k t⁻¹ G'(y/t) dt`, `(𝒜_k G)'` locally Lipschitz, and a.e. on `y < 0`:
`(𝒜_k G)'' = -G'(y)/y` (`k = 0`), `-(αk/y) ∫₀¹ t^{α-1}(1-t^α)^{k-1} G'(y/t) dt` (`k ≥ 1`). -/
theorem c08_Ak_formulas (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (k : ℕ) :
    ContDiffOn ℝ 1 (c08_low_operators p k G) (Iio 0) ∧
    (∀ y : ℝ, y < 0 → deriv (c08_low_operators p k G) y =
      ∫ t in (0 : ℝ)..1, (1 - t ^ (p + 1)) ^ k * t⁻¹ * deriv G (y / t)) ∧
    LocallyLipschitzOn (Iio 0) (deriv (c08_low_operators p k G)) ∧
    ∀ᵐ y, y < 0 → deriv (deriv (c08_low_operators p k G)) y =
      if k = 0 then -(deriv G y) / y
      else -((p + 1) * k / y) *
        ∫ t in (0 : ℝ)..1, t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) * deriv G (y / t) := by
  have hp0 : 0 < p := by linarith
  have hγ0 : 0 ≤ γ := by linarith
  set N := yNorm p γ G
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  obtain ⟨-, hGpt⟩ := c08_aux_Y_integrable hp0 hγ hG
  have hGl : LocallyLipschitz G := hG.1
  have hGc : Continuous G := hGl.continuous
  have hGb : ∀ x, |G x| ≤ N := fun x => (hGpt x).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb x) (by linarith)) hN) (mul_one N))
  have hjbc : Continuous jb := by unfold jb; fun_prop
  have hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1) := by
    refine c08_aux_deriv_bound_everywhere hG.1 ?_ (fun x _ => ?_) ?_
    · exact (continuous_const.mul (hjbc.rpow_const (fun x => Or.inl (c08_aux_jb_pos x).ne'))).continuousOn
    · have := Real.rpow_pos_of_pos (c08_aux_jb_pos x) (-γ - 1); positivity
    · filter_upwards [c08_aux_Y_ae_neg hG] with x hx hx0 using hx hx0.le
  -- the weight and its derivative
  set ω : ℝ → ℝ := fun t => (1 - t ^ (p + 1)) ^ k with hωdef
  set ω' : ℝ → ℝ := fun t => -(k : ℝ) * ((p + 1) * t ^ (p + 1 - 1)) * (1 - t ^ (p + 1)) ^ (k - 1)
    with hω'def
  have hpow : Continuous (fun t : ℝ => t ^ (p + 1)) :=
    continuous_id.rpow_const fun _ => Or.inr (by linarith)
  have hpow' : Continuous (fun t : ℝ => t ^ (p + 1 - 1)) :=
    continuous_id.rpow_const fun _ => Or.inr (by linarith)
  have hω : Continuous ω := (continuous_const.sub hpow).pow k
  have hω' : Continuous ω' :=
    (continuous_const.mul (continuous_const.mul hpow')).mul ((continuous_const.sub hpow).pow _)
  have hd : ∀ t, HasDerivAt ω (ω' t) t := by
    intro t
    have h1 := ((Real.hasDerivAt_rpow_const (x := t) (p := p + 1) (Or.inr (by linarith))).const_sub 1).pow k
    convert h1 using 1
    simp only [hω'def]; ring
  set ωt : ℝ → ℝ := fun t => ω t + t * ω' t with hωt
  have hωtc : Continuous ωt := hω.add (continuous_id.mul hω')
  set c := ω 1 with hc
  -- the three integrals
  set A := c08_low_operators p k G with hAdef
  set D : ℝ → ℝ := fun y => ∫ t in Ioc (0:ℝ) 1, ω t * (t⁻¹ * deriv G (y / t)) with hD
  set At : ℝ → ℝ := fun y => ∫ t in Ioc (0:ℝ) 1, ωt t * G (y / t) with hAt
  set Dt : ℝ → ℝ := fun y => ∫ t in Ioc (0:ℝ) 1, ωt t * (t⁻¹ * deriv G (y / t)) with hDt
  have hA : ∀ y, A y = ∫ t in Ioc (0:ℝ) 1, ω t * G (y / t) := fun y => by
    simp only [hAdef, c08_low_operators, hωdef]; rw [intervalIntegral.integral_of_le zero_le_one]
  have hibp : ∀ y, y < 0 → D y = (At y - c * G y) / y := by
    intro y hy
    have := c08_aux_Aw_ibp hN hγ0 hGl hGb hG' hω hω' hd hy
    rw [eq_div_iff hy.ne, mul_comm]; exact this
  have hAtc : Continuous At := c08_aux_Aw_cont hGc hGb hωtc
  have hDc : ContinuousOn D (Iio 0) := by
    refine ContinuousOn.congr ?_ (fun y hy => hibp y hy)
    exact ((hAtc.sub (continuous_const.mul hGc)).continuousOn).div continuousOn_id
      (fun y hy => (ne_of_lt hy))
  have hrepr : ∀ y0 y1, y0 < 0 → y1 < 0 → A y1 = A y0 + ∫ s in y0..y1, D s := by
    intro y0 y1 h0 h1
    rw [hA, hA]; exact c08_aux_Aw_repr' hN hγ0 hGl hGb hG' hω h0 h1
  have hderA : ∀ y, y < 0 → HasDerivAt A (D y) y := by
    intro y hy
    have hy0 : y - 1 < 0 := by linarith
    have hsub : uIcc (y - 1) y ⊆ Iio 0 := by
      rw [uIcc_of_le (by linarith)]; intro u hu; exact lt_of_le_of_lt hu.2 hy
    have hint : IntervalIntegrable D volume (y - 1) y := (hDc.mono hsub).intervalIntegrable
    have hF := (intervalIntegral.integral_hasDerivAt_right hint
      (hDc.stronglyMeasurableAtFilter isOpen_Iio y hy)
      (hDc.continuousAt (isOpen_Iio.mem_nhds hy))).const_add (A (y - 1))
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hy] with u hu
    exact hrepr (y - 1) u hy0 hu
  have hdA : ∀ y, y < 0 → deriv A y = D y := fun y hy => (hderA y hy).deriv
  obtain ⟨Ωt, hΩt⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hωtc.continuousOn
  have hΩt0 : 0 ≤ Ωt := (norm_nonneg _).trans (hΩt 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨?_, fun y hy => ?_, ?_, ?_⟩
  · -- C¹ on the negative half-line
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Iio]
    refine ⟨fun y hy => (hderA y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact contDiffOn_zero.2 (hDc.congr fun y hy => hdA y hy)
  · rw [hdA y hy, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [hωdef]; ring
  · -- local Lipschitz bound for `A' = (A_t - c G)/y`
    intro x hx
    have hx0 : x < 0 := hx
    set δ := |x| / 2
    have hδ : 0 < δ := by have := abs_pos.2 hx0.ne; positivity
    set I := Icc (x - δ) (x + δ)
    have hI : ∀ y ∈ I, y ≤ x / 2 := by
      intro y hy; have := hy.2; simp only [δ, abs_of_neg hx0] at this; linarith
    have hIneg : ∀ y ∈ I, y < 0 := fun y hy => lt_of_le_of_lt (hI y hy) (by linarith)
    have hIabs : ∀ y ∈ I, |x| / 2 ≤ |y| := by
      intro y hy; have := hI y hy
      rw [abs_of_neg hx0, abs_of_neg (hIneg y hy)]; linarith
    obtain ⟨KG, hKG⟩ := (hGl.locallyLipschitzOn (s := I)).exists_lipschitzOnWith_of_compact
      isCompact_Icc
    set BD := Ωt * (N * |x / 2| ^ (-γ - 1))
    have hBD0 : 0 ≤ BD := by have := Real.rpow_nonneg (abs_nonneg (x / 2)) (-γ - 1); positivity
    have hAtLip : ∀ y1 ∈ I, ∀ y2 ∈ I, |At y1 - At y2| ≤ BD * |y1 - y2| := by
      intro y1 h1 y2 h2
      have hr := c08_aux_Aw_repr' hN hγ0 hGl hGb hG' hωtc (hIneg y2 h2) (hIneg y1 h1)
      have : At y1 - At y2 = ∫ s in y2..y1, Dt s := by simp only [hAt, hDt]; rw [hr]; ring
      rw [this, ← Real.norm_eq_abs]
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
      have hsI : s ∈ I := Set.uIcc_subset_Icc h2 h1 (uIoc_subset_uIcc hs)
      rw [Real.norm_eq_abs]
      exact c08_aux_Dw_bound hN hγ0 hG' hΩt0 hΩt (by linarith) (hI s hsI)
    have hAtb : ∀ y, |At y| ≤ Ωt * N := by
      intro y
      rw [← Real.norm_eq_abs]
      have := norm_setIntegral_le_of_norm_le_const (s := Ioc (0:ℝ) 1) (C := Ωt * N)
        (f := fun t => ωt t * G (y / t)) (measure_Ioc_lt_top (μ := (volume : Measure ℝ)))
        (fun t ht => by
          rw [norm_mul, Real.norm_eq_abs (G _)]
          exact mul_le_mul (hΩt t (Ioc_subset_Icc_self ht)) (hGb _) (abs_nonneg _) hΩt0)
      simpa [Real.volume_Ioc] using this
    set M1 := Ωt * N + |c| * N
    set L1 := BD + |c| * KG
    have hxa : 0 < |x| := abs_pos.2 hx0.ne
    set K := 2 / |x| * L1 + M1 * (4 / x ^ 2)
    have hK0 : 0 ≤ K := by
      have : (0:ℝ) ≤ KG := KG.2
      positivity
    refine ⟨K.toNNReal, I, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)),
      LipschitzOnWith.of_dist_le_mul fun y1 h1 y2 h2 => ?_⟩
    rw [Real.coe_toNNReal _ hK0, Real.dist_eq, Real.dist_eq, hdA y1 (hIneg y1 h1),
      hdA y2 (hIneg y2 h2), hibp y1 (hIneg y1 h1), hibp y2 (hIneg y2 h2)]
    set f1 := At y1 - c * G y1
    set f2 := At y2 - c * G y2
    have hf12 : |f1 - f2| ≤ L1 * |y1 - y2| := by
      have hG12 : |G y1 - G y2| ≤ KG * |y1 - y2| := by
        have := hKG.dist_le_mul y1 h1 y2 h2; simpa [Real.dist_eq] using this
      calc |f1 - f2| = |(At y1 - At y2) - c * (G y1 - G y2)| := by simp only [f1, f2]; ring_nf
        _ ≤ |At y1 - At y2| + |c| * |G y1 - G y2| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ BD * |y1 - y2| + |c| * (KG * |y1 - y2|) := by
            gcongr; exact hAtLip y1 h1 y2 h2
        _ = L1 * |y1 - y2| := by simp only [L1]; ring
    have hf2 : |f2| ≤ M1 := by
      calc |f2| ≤ |At y2| + |c| * |G y2| := by simp only [f2]; rw [← abs_mul]; exact abs_sub _ _
        _ ≤ Ωt * N + |c| * N := by gcongr; exacts [hAtb y2, hGb y2]
    have hy1 := hIabs y1 h1; have hy2 := hIabs y2 h2
    have hy1n := hIneg y1 h1; have hy2n := hIneg y2 h2
    have ha1 : 0 < |y1| := abs_pos.2 hy1n.ne
    have ha2 : 0 < |y2| := abs_pos.2 hy2n.ne
    have hy1ne : y1 ≠ 0 := hy1n.ne
    have hy2ne : y2 ≠ 0 := hy2n.ne
    have e : f1 / y1 - f2 / y2 = (f1 - f2) / y1 + f2 * (y2 - y1) / (y1 * y2) := by
      field_simp; ring
    rw [e]
    have i1 : |(f1 - f2) / y1| ≤ 2 / |x| * (L1 * |y1 - y2|) := by
      rw [abs_div, div_eq_mul_inv, mul_comm]
      apply mul_le_mul _ hf12 (abs_nonneg _) (by positivity)
      rw [inv_le_comm₀ ha1 (by positivity)]; field_simp; linarith
    have i2 : |f2 * (y2 - y1) / (y1 * y2)| ≤ M1 * (4 / x ^ 2) * |y1 - y2| := by
      rw [abs_div, abs_mul, abs_mul, abs_sub_comm y2 y1]
      have hden : x ^ 2 / 4 ≤ |y1| * |y2| := by
        have : x ^ 2 = |x| * |x| := by rw [abs_mul_abs_self, sq]
        rw [this]; nlinarith
      have hpos : 0 < |y1| * |y2| := mul_pos ha1 ha2
      rw [div_le_iff₀ hpos]
      have hM1 : 0 ≤ M1 := (abs_nonneg _).trans hf2
      calc |f2| * |y1 - y2| ≤ M1 * |y1 - y2| := mul_le_mul_of_nonneg_right hf2 (abs_nonneg _)
        _ = M1 * (4 / x ^ 2) * |y1 - y2| * (x ^ 2 / 4) := by
            have : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0.ne
            have hx1 : x ≠ 0 := hx0.ne
            field_simp
        _ ≤ M1 * (4 / x ^ 2) * |y1 - y2| * (|y1| * |y2|) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    calc |(f1 - f2) / y1 + f2 * (y2 - y1) / (y1 * y2)|
        ≤ |(f1 - f2) / y1| + |f2 * (y2 - y1) / (y1 * y2)| := abs_add_le _ _
      _ ≤ 2 / |x| * (L1 * |y1 - y2|) + M1 * (4 / x ^ 2) * |y1 - y2| := add_le_add i1 i2
      _ = K * |y1 - y2| := by simp only [K]; ring
  · -- a.e. second derivative
    set Ft : ℝ × ℝ → ℝ := fun q => ωt q.1 * (q.1⁻¹ * deriv G (q.2 / q.1)) with hFt
    have hFtm : Measurable Ft := (hωtc.measurable.comp measurable_fst).mul
      ((measurable_fst.inv).mul ((measurable_deriv G).comp (measurable_snd.div measurable_fst)))
    have hDtm : StronglyMeasurable Dt :=
      hFtm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0:ℝ) 1))
    have hLebn : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Ioo (-((n:ℝ) + 1)) (-(1 / ((n:ℝ) + 1))) →
        HasDerivAt At (Dt y) y := by
      intro n
      set a : ℝ := -((n:ℝ) + 1)
      set b : ℝ := -(1 / ((n:ℝ) + 1))
      have hb : b < 0 := by
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        simp only [b]; linarith
      have hab : a ≤ b := by
        simp only [a, b]
        have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
        linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hint : IntervalIntegrable Dt volume a b := by
        refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 ?_
        refine Measure.integrableOn_of_bounded (M := Ωt * (N * |b| ^ (-γ - 1)))
          measure_Ioc_lt_top.ne hDtm.aestronglyMeasurable
          ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_))
        rw [Real.norm_eq_abs]
        exact c08_aux_Dw_bound hN hγ0 hG' hΩt0 hΩt hb hs.2
      filter_upwards [hint.ae_hasDerivAt_integral] with y hy hyI
      have hyU : y ∈ uIcc a b := by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self hyI
      have haU : a ∈ uIcc a b := left_mem_uIcc
      have h := (hy hyU a haU).const_add (At a)
      refine h.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hyI.1 hyI.2] with u hu
      have hu0 : u < 0 := lt_trans hu.2 hb
      have ha0 : a < 0 := lt_of_le_of_lt hab hb
      simp only [hAt, hDt]
      exact c08_aux_Aw_repr' hN hγ0 hGl hGb hG' hωtc ha0 hu0
    have hLeb : ∀ᵐ y ∂(volume : Measure ℝ), y < 0 → HasDerivAt At (Dt y) y := by
      rw [← ae_all_iff] at hLebn
      filter_upwards [hLebn] with y hy hy0
      obtain ⟨n, hn⟩ := exists_nat_gt (max (-y) (1 / (-y)))
      apply hy n
      constructor
      · have := (le_max_left _ _).trans_lt hn; linarith
      · have h1 : 1 / (-y) < (n:ℝ) + 1 := by have := (le_max_right _ _).trans_lt hn; linarith
        have hy' : 0 < -y := by linarith
        have : 1 / ((n:ℝ) + 1) < -y := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hy'] at h1; linarith
        linarith
    filter_upwards [hLeb, c08_aux_ae_differentiable hGl] with y hyL hyG hy
    have hDev : deriv A =ᶠ[𝓝 y] fun u => (At u - c * G u) / u := by
      filter_upwards [isOpen_Iio.mem_nhds hy] with u hu
      rw [hdA u hu, hibp u hu]
    have hder2 : HasDerivAt (fun u => (At u - c * G u) / u)
        (((Dt y - c * deriv G y) * y - (At y - c * G y) * 1) / y ^ 2) y :=
      ((hyL hy).sub (hyG.hasDerivAt.const_mul c)).div (hasDerivAt_id y) hy.ne
    rw [hDev.deriv_eq, hder2.deriv]
    -- `D_t - D = ∫ ω' G'(y/t)`
    have hbd : ∀ (w : ℝ → ℝ), Continuous w →
        IntegrableOn (fun t => w t * (t⁻¹ * deriv G (y / t))) (Ioc (0:ℝ) 1) := by
      intro w hw
      obtain ⟨W, hW⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
        hw.continuousOn
      have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 ⟨le_rfl, zero_le_one⟩)
      refine Measure.integrableOn_of_bounded (M := W * (N * |y| ^ (-γ - 1)))
        measure_Ioc_lt_top.ne ?_ ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun t ht => ?_))
      · exact (hw.measurable.mul (measurable_id.inv.mul ((measurable_deriv G).comp
          (measurable_const.div measurable_id)))).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_mul (hW t (Ioc_subset_Icc_self ht))
          (by rw [Real.norm_eq_abs]; exact c08_aux_Dbound hN hγ0 hG' hy le_rfl ht)
          (norm_nonneg _) hW0
    have hdiff : Dt y - D y = ∫ t in Ioc (0:ℝ) 1, ω' t * deriv G (y / t) := by
      simp only [hDt, hD]
      rw [← integral_sub (hbd ωt hωtc) (hbd ω hω)]
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      have ht0 : t ≠ 0 := ht.1.ne'
      simp only [hωt]; field_simp; ring
    have hDy := hibp y hy
    have key : ((Dt y - c * deriv G y) * y - (At y - c * G y) * 1) / y ^ 2 =
        ((∫ t in Ioc (0:ℝ) 1, ω' t * deriv G (y / t)) - c * deriv G y) / y := by
      rw [← hdiff]
      have hyne : y ≠ 0 := hy.ne
      rw [hDy]; field_simp; ring
    rw [key]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hω'0 : ∀ t, ω' t = 0 := fun t => by simp [hω'def]
      have hc1 : c = 1 := by simp [hc, hωdef]
      simp only [hω'0, zero_mul, integral_zero, hc1, one_mul, if_true]
      ring
    · have hk0 : k ≠ 0 := hk.ne'
      have hc0 : c = 0 := by
        simp only [hc, hωdef, Real.one_rpow, sub_self]; exact zero_pow hk0
      simp only [hk0, if_false, hc0, zero_mul, sub_zero]
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
      have : ∫ t in Ioc (0:ℝ) 1, ω' t * deriv G (y / t) =
          ∫ t in Ioc (0:ℝ) 1, -((p + 1) * k) * (t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) *
            deriv G (y / t)) :=
        setIntegral_congr_fun measurableSet_Ioc (fun t _ => by simp only [hω'def]; ring)
      rw [this, integral_const_mul, integral_const_mul]
      field_simp




/-- For `t ∈ (0,1]`: `|y| ≤ |y/t|`. -/
theorem c08_aux_abs_le_div {y t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) : |y| ≤ |y / t| := by
  rw [abs_div, abs_of_pos ht.1, le_div_iff₀ ht.1]
  exact mul_le_of_le_one_right (abs_nonneg y) ht.2

/-- `0 ≤ (1 - t^α)^k ≤ 1` for `t ∈ [0,1]`. -/
theorem c08_aux_one_sub_pow_bound (p t : ℝ) (k : ℕ) (hp : 0 < p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (1 - t ^ (p + 1)) ^ k ∧ (1 - t ^ (p + 1)) ^ k ≤ 1 := by
  have h1 : t ^ (p + 1) ≤ 1 := Real.rpow_le_one ht0 ht1 (by linarith)
  have h0 : 0 ≤ t ^ (p + 1) := Real.rpow_nonneg ht0 _
  exact ⟨pow_nonneg (by linarith) k, pow_le_one₀ (by linarith) (by linarith)⟩

/-- `∫₀¹ t^{α-1}(1-t^α)^{k-1} dt = 1/(αk)` for `k ≥ 1`. -/
theorem c08_aux_beta_integral (p : ℝ) (hp : 0 < p) (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in (0:ℝ)..1, t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) = 1 / ((p + 1) * k) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hderiv : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => -(1 - t ^ (p + 1)) ^ k / ((p + 1) * k))
      (t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1)) t := by
    intro t _
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := p + 1) (Or.inr (by linarith))
    have h2 := ((h1.const_sub 1).pow k).neg.div_const ((p + 1) * k)
    convert h2 using 1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have hcont : Continuous (fun t : ℝ => t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1)) :=
    (Real.continuous_rpow_const (by linarith)).mul
      ((continuous_const.sub (Real.continuous_rpow_const (by linarith))).pow _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [Real.one_rpow, sub_self, Real.zero_rpow (show p + 1 ≠ 0 by linarith)]
  rw [zero_pow (by omega)]
  field_simp
  ring

/-- Value bound for `𝒜_k G`. -/
theorem c08_aux_Ak_value (p γ N : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ) (k : ℕ) (G : ℝ → ℝ)
    (hG : ∀ x, |G x| ≤ N * jb x ^ (-γ)) (y : ℝ) :
    |c08_low_operators p k G y| ≤ N * jb y ^ (-γ) := by
  have hN : 0 ≤ N := by
    have := (abs_nonneg _).trans (hG 0)
    have h1 := Real.rpow_pos_of_pos (c08_aux_jb_pos 0) (-γ)
    exact nonneg_of_mul_nonneg_left this h1
  unfold c08_low_operators
  have := intervalIntegral.norm_integral_le_of_norm_le (zero_le_one' ℝ)
    (f := fun t => (1 - t ^ (p + 1)) ^ k * G (y / t)) (g := fun _ => N * jb y ^ (-γ))
    (Eventually.of_forall fun t ht => ?_) (intervalIntegrable_const (μ := volume))
  · simpa using this
  · obtain ⟨b0, b1⟩ := c08_aux_one_sub_pow_bound p t k hp ht.1.le ht.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg b0]
    have hj : jb y ^ (-γ) ≥ jb (y / t) ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos (c08_aux_jb_pos y) (c08_aux_jb_mono (c08_aux_abs_le_div ht))
        (by linarith)
    calc (1 - t ^ (p + 1)) ^ k * |G (y / t)| ≤ 1 * (N * jb y ^ (-γ)) :=
          mul_le_mul b1 ((hG _).trans (mul_le_mul_of_nonneg_left hj hN)) (abs_nonneg _)
            zero_le_one
      _ = _ := one_mul _

/-- First-derivative bound for `𝒜_k G` on `y ≤ -1`. -/
theorem c08_aux_Ak_deriv (p γ N : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ) (hN : 0 ≤ N) (k : ℕ) (G : ℝ → ℝ)
    (hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1)) (y : ℝ) (hy : y ≤ -1) :
    |∫ t in (0 : ℝ)..1, (1 - t ^ (p + 1)) ^ k * t⁻¹ * deriv G (y / t)| ≤
      N * jb y ^ (-γ) / |y| := by
  have hy0 : 0 < |y| := by rw [abs_of_neg (by linarith)]; linarith
  have := intervalIntegral.norm_integral_le_of_norm_le (zero_le_one' ℝ)
    (f := fun t => (1 - t ^ (p + 1)) ^ k * t⁻¹ * deriv G (y / t))
    (g := fun _ => N * jb y ^ (-γ) / |y|) (Eventually.of_forall fun t ht => ?_)
    (intervalIntegrable_const (μ := volume))
  · simpa using this
  · obtain ⟨b0, b1⟩ := c08_aux_one_sub_pow_bound p t k hp ht.1.le ht.2
    have ht0 := ht.1
    have hyt : y / t < 0 := div_neg_of_neg_of_pos (by linarith) ht0
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg b0, abs_of_pos (inv_pos.2 ht0)]
    have hjt := c08_aux_jb_pos (y / t)
    -- `⟨y/t⟩^{-γ-1} ≤ ⟨y⟩^{-γ} · t/|y|`
    have hA : jb (y / t) ^ (-γ) ≤ jb y ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos (c08_aux_jb_pos y) (c08_aux_jb_mono (c08_aux_abs_le_div ht))
        (by linarith)
    have hB : jb (y / t) ^ (-1:ℝ) ≤ t / |y| := by
      rw [Real.rpow_neg_one]
      have : |y| / t ≤ jb (y / t) := by
        have h1 : |y / t| ≤ jb (y / t) := by
          unfold jb; rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
        rwa [abs_div, abs_of_pos ht0] at h1
      rw [inv_le_comm₀ hjt (div_pos ht0 hy0), inv_div]; exact this
    have hsplit : jb (y / t) ^ (-γ - 1) = jb (y / t) ^ (-γ) * jb (y / t) ^ (-1:ℝ) := by
      rw [← Real.rpow_add hjt]; ring_nf
    have hG1 := hG' _ hyt
    rw [hsplit] at hG1
    have hjγ0 : 0 ≤ jb y ^ (-γ) := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
    calc (1 - t ^ (p + 1)) ^ k * t⁻¹ * |deriv G (y / t)|
        ≤ 1 * t⁻¹ * (N * (jb y ^ (-γ) * (t / |y|))) := by
          gcongr
          refine hG1.trans (mul_le_mul_of_nonneg_left ?_ hN)
          exact mul_le_mul hA hB (Real.rpow_pos_of_pos hjt _).le hjγ0
      _ = N * jb y ^ (-γ) / |y| := by field_simp

/-- Second-derivative integral bound for `𝒜_k G`, `k ≥ 1`, on `y ≤ -1`. -/
theorem c08_aux_Ak_deriv2 (p γ N : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ) (hN : 0 ≤ N) (k : ℕ) (hk : 1 ≤ k)
    (G : ℝ → ℝ) (hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1)) (y : ℝ) (hy : y ≤ -1) :
    |∫ t in (0 : ℝ)..1, t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) * deriv G (y / t)| ≤
      N * jb y ^ (-γ - 1) * (1 / ((p + 1) * k)) := by
  have hcont : Continuous (fun t : ℝ => t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1)) :=
    (Real.continuous_rpow_const (by linarith)).mul
      ((continuous_const.sub (Real.continuous_rpow_const (by linarith))).pow _)
  have := intervalIntegral.norm_integral_le_of_norm_le (zero_le_one' ℝ)
    (f := fun t => t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) * deriv G (y / t))
    (g := fun t => N * jb y ^ (-γ - 1) * (t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1)))
    (Eventually.of_forall fun t ht => ?_) ((hcont.intervalIntegrable (μ := volume) 0 1).const_mul _)
  · rw [intervalIntegral.integral_const_mul, c08_aux_beta_integral p hp k hk] at this
    simpa using this
  · obtain ⟨b0, b1⟩ := c08_aux_one_sub_pow_bound p t (k - 1) hp ht.1.le ht.2
    have ht0 := ht.1
    have hyt : y / t < 0 := div_neg_of_neg_of_pos (by linarith) ht0
    have hw0 : 0 ≤ t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) b0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
    have hA : jb (y / t) ^ (-γ - 1) ≤ jb y ^ (-γ - 1) :=
      Real.rpow_le_rpow_of_nonpos (c08_aux_jb_pos y) (c08_aux_jb_mono (c08_aux_abs_le_div ht))
        (by linarith)
    calc t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) * |deriv G (y / t)|
        ≤ t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) * (N * jb y ^ (-γ - 1)) :=
          mul_le_mul_of_nonneg_left ((hG' _ hyt).trans (mul_le_mul_of_nonneg_left hA hN)) hw0
      _ = _ := by ring


/-- Blueprint: lem:c08_Ak_bound.  For `γ > 1`: `‖𝒜_k G‖_{Z_γ} ≤ C ‖G‖_{Y_γ}` uniformly in `k`. -/
theorem c08_Ak_bound (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), ∀ G ∈ Y_gamma p γ,
      (fun y => (c08_low_operators p k G y : ℂ)) ∈ c08_Z_gamma γ ∧
      (c08_Z_gamma_norm γ (fun y => (c08_low_operators p k G y : ℂ))).toReal ≤ C * yNorm p γ G := by
  have hp0 : 0 < p := by linarith
  refine ⟨5, by norm_num, fun k G hG => ?_⟩
  set N := yNorm p γ G with hNdef
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  obtain ⟨-, hGpt⟩ := c08_aux_Y_integrable hp0 hγ hG
  have hGc : Continuous G := hG.1.continuous
  have hjbc : Continuous jb := by unfold jb; fun_prop
  have hG' : ∀ x, x < 0 → |deriv G x| ≤ N * jb x ^ (-γ - 1) := by
    refine c08_aux_deriv_bound_everywhere hG.1 ?_ (fun x _ => ?_) ?_
    · exact (continuous_const.mul (hjbc.rpow_const (fun x => Or.inl (c08_aux_jb_pos x).ne'))).continuousOn
    · have := Real.rpow_pos_of_pos (c08_aux_jb_pos x) (-γ - 1); positivity
    · filter_upwards [c08_aux_Y_ae_neg hG] with x hx hx0 using hx hx0.le
  obtain ⟨hC1, hD1, hLip, hD2⟩ := c08_Ak_formulas p γ hp hp1 hγ G hG k
  set A := c08_low_operators p k G with hAdef
  have hV : ∀ y, |A y| ≤ N * jb y ^ (-γ) := c08_aux_Ak_value p γ N hp0 (by linarith) k G hGpt
  have hyabs : ∀ y : ℝ, y ≤ -1 → jb y ≤ 2 * |y| := fun y hy => by
    have := c08_aux_jb_le_one_add y
    have : 1 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hA1 : ∀ y : ℝ, y ≤ -1 → jb y * |deriv A y| ≤ 2 * N * jb y ^ (-γ) := by
    intro y hy
    rw [hD1 y (by linarith)]
    have h := c08_aux_Ak_deriv p γ N hp0 (by linarith) hN k G hG' y hy
    have hy0 : 0 < |y| := by rw [abs_of_neg (by linarith)]; linarith
    have hj := c08_aux_jb_pos y
    have hw : 0 ≤ N * jb y ^ (-γ) := by have := Real.rpow_pos_of_pos hj (-γ); positivity
    calc jb y * |∫ t in (0:ℝ)..1, (1 - t ^ (p + 1)) ^ k * t⁻¹ * deriv G (y / t)|
        ≤ jb y * (N * jb y ^ (-γ) / |y|) := mul_le_mul_of_nonneg_left h hj.le
      _ = (jb y / |y|) * (N * jb y ^ (-γ)) := by ring
      _ ≤ 2 * (N * jb y ^ (-γ)) := by
          apply mul_le_mul_of_nonneg_right _ hw
          rw [div_le_iff₀ hy0]; exact hyabs y hy
      _ = _ := by ring
  have hA2 : ∀ᵐ y ∂(volume : Measure ℝ), y ≤ -1 →
      jb y ^ (2 : ℕ) * |deriv (deriv A) y| ≤ 2 * N * jb y ^ (-γ) := by
    filter_upwards [hD2] with y hy hy1
    have hy0 : 0 < |y| := by rw [abs_of_neg (by linarith)]; linarith
    have hj := c08_aux_jb_pos y
    have hjγ : jb y ^ (2 : ℕ) * jb y ^ (-γ - 1) = jb y * jb y ^ (-γ) := by
      rw [show -γ - 1 = -γ + (-1) by ring, Real.rpow_add hj, Real.rpow_neg_one]
      field_simp
    have hw : 0 ≤ N * jb y ^ (-γ) := by have := Real.rpow_pos_of_pos hj (-γ); positivity
    have key : jb y ^ (2 : ℕ) * |deriv (deriv A) y| ≤ jb y ^ (2 : ℕ) * (N * jb y ^ (-γ - 1) / |y|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hy (by linarith)]
      split_ifs with hk
      · rw [neg_div, abs_neg, abs_div]
        exact div_le_div_of_nonneg_right (hG' y (by linarith)) hy0.le
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
        have h := c08_aux_Ak_deriv2 p γ N hp0 (by linarith) hN k hk1 G hG' y hy1
        have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
        rw [abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < (p + 1) * k)]
        calc (p + 1) * k / |y| * |∫ t in (0:ℝ)..1, t ^ (p + 1 - 1) * (1 - t ^ (p + 1)) ^ (k - 1) *
              deriv G (y / t)| ≤ (p + 1) * k / |y| * (N * jb y ^ (-γ - 1) * (1 / ((p + 1) * k))) :=
              mul_le_mul_of_nonneg_left h (by positivity)
          _ = _ := by field_simp
    calc _ ≤ _ := key
      _ = (jb y / |y|) * (N * (jb y ^ (2 : ℕ) * jb y ^ (-γ - 1)) / jb y) := by
          field_simp
      _ = (jb y / |y|) * (N * jb y ^ (-γ)) := by rw [hjγ]; field_simp
      _ ≤ 2 * (N * jb y ^ (-γ)) := by
          apply mul_le_mul_of_nonneg_right _ hw
          rw [div_le_iff₀ hy0]; exact hyabs y hy1
      _ = _ := by ring
  -- continuity of `A`
  have hAc : Continuous A := by
    have hb : ∀ y : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
        ‖(1 - t ^ (p + 1)) ^ k * G (y / t)‖ ≤ N := by
      intro y
      refine Eventually.of_forall (fun t ht => ?_)
      rw [uIoc_of_le zero_le_one] at ht
      obtain ⟨b0, b1⟩ := c08_aux_one_sub_pow_bound p t k hp0 ht.1.le ht.2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg b0]
      have h1 : jb (y / t) ^ (-γ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb _) (by linarith)
      calc (1 - t ^ (p + 1)) ^ k * |G (y / t)| ≤ 1 * (N * 1) :=
            mul_le_mul b1 ((hGpt _).trans (mul_le_mul_of_nonneg_left h1 hN)) (abs_nonneg _)
              zero_le_one
        _ = N := by ring
    refine intervalIntegral.continuous_of_dominated_interval (bound := fun _ => N)
      (fun y => ?_) hb intervalIntegrable_const (Eventually.of_forall fun t ht => ?_)
    · exact (((continuous_const.sub (Real.continuous_rpow_const (by linarith))).pow k).measurable.mul
        (hGc.measurable.comp (measurable_const.div measurable_id))).aestronglyMeasurable
    · rw [uIoc_of_le zero_le_one] at ht
      exact continuous_const.mul (hGc.comp (continuous_id.div_const t))
  have hderH : deriv (fun y => ((A y : ℝ) : ℂ)) = fun y => ((deriv A y : ℝ) : ℂ) :=
    c08_aux_deriv_ofReal A
  have hderH2 : deriv (deriv (fun y => ((A y : ℝ) : ℂ))) = fun y => ((deriv (deriv A) y : ℝ) : ℂ) := by
    rw [hderH]; exact c08_aux_deriv_ofReal (deriv A)
  -- the norm
  have hnorm : c08_Z_gamma_norm γ (fun y => ((A y : ℝ) : ℂ)) ≤
      ENNReal.ofReal N + ENNReal.ofReal (4 * N) := by
    unfold c08_Z_gamma_norm
    gcongr
    · refine iSup_le (fun y => ENNReal.ofReal_le_ofReal ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hj := c08_aux_jb_pos y
      have := mul_le_mul_of_nonneg_left (hV y) (Real.rpow_pos_of_pos hj γ).le
      calc jb y ^ γ * |A y| ≤ jb y ^ γ * (N * jb y ^ (-γ)) := this
        _ = N * (jb y ^ γ * jb y ^ (-γ)) := by ring
        _ = N := by rw [← Real.rpow_add hj]; simp
    · refine essSup_le_of_ae_le _ ?_
      have hA2' := ae_restrict_of_ae (μ := volume) (s := Iic (-1)) hA2
      filter_upwards [hA2', ae_restrict_mem measurableSet_Iic] with y hy hy1
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hderH2, hderH]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have hj := c08_aux_jb_pos y
      have h1 := hA1 y hy1
      have h2 := hy hy1
      have hg := (Real.rpow_pos_of_pos hj γ).le
      calc jb y ^ γ * (jb y * |deriv A y| + jb y ^ (2 : ℕ) * |deriv (deriv A) y|)
          ≤ jb y ^ γ * (2 * N * jb y ^ (-γ) + 2 * N * jb y ^ (-γ)) := by gcongr
        _ = 4 * N * (jb y ^ γ * jb y ^ (-γ)) := by ring
        _ = 4 * N := by rw [← Real.rpow_add hj]; simp
  have hfin : ENNReal.ofReal N + ENNReal.ofReal (4 * N) < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  refine ⟨⟨Complex.continuous_ofReal.comp hAc, ?_, ?_, lt_of_le_of_lt hnorm hfin⟩, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hC1.mono (Iio_subset_Iio (by norm_num : (-1:ℝ) ≤ 0))))
  · rw [hderH]
    intro x hx
    have hx0 : x < 0 := lt_trans (show x < -1 from hx) (by norm_num)
    obtain ⟨K, t, ht, hL⟩ := hLip (show x ∈ Iio (0:ℝ) from hx0)
    refine ⟨K, t ∩ Iio 0, ?_, ?_⟩
    · have h1 : t ∈ nhdsWithin x (Iio (-1)) := nhdsWithin_mono x (Iio_subset_Iio (by norm_num : (-1:ℝ) ≤ 0)) ht
      exact Filter.inter_mem h1 (nhdsWithin_le_nhds (Iio_mem_nhds hx0))
    · have := (Complex.isometry_ofReal.lipschitzWith.comp_lipschitzOnWith hL).mono
        (inter_subset_left : t ∩ Iio 0 ⊆ t)
      simpa [Function.comp_def] using this
  · calc (c08_Z_gamma_norm γ (fun y => ((A y : ℝ) : ℂ))).toReal
        ≤ (ENNReal.ofReal N + ENNReal.ofReal (4 * N)).toReal := ENNReal.toReal_mono hfin.ne hnorm
      _ = N + 4 * N := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hN,
            ENNReal.toReal_ofReal (by positivity)]
      _ = 5 * N := by ring


/-- Pointwise value bound for `H ∈ Z_γ`. -/
theorem c08_aux_Z_pointwise {γ : ℝ} {H : ℝ → ℂ} (hH : H ∈ c08_Z_gamma γ) (y : ℝ) :
    ‖H y‖ ≤ (c08_Z_gamma_norm γ H).toReal * jb y ^ (-γ) := by
  apply c08_aux_div_weight
  have h1 : ENNReal.ofReal (jb y ^ γ * ‖H y‖) ≤ c08_Z_gamma_norm γ H := by
    unfold c08_Z_gamma_norm
    exact (le_iSup (fun y => ENNReal.ofReal (jb y ^ γ * ‖H y‖)) y).trans le_self_add
  exact (ENNReal.ofReal_le_iff_le_toReal hH.2.2.2.ne).1 h1

/-- `H ∈ Z_γ` (`γ > 1`) is integrable with `‖H‖_{L¹} ≤ (∫⟨z⟩^{-γ}) ‖H‖_{Z_γ}`. -/
theorem c08_aux_Z_integrable {γ : ℝ} (hγ : 1 < γ) {H : ℝ → ℂ} (hH : H ∈ c08_Z_gamma γ) :
    Integrable H ∧ ∫ z, ‖H z‖ ≤ (c08_Z_gamma_norm γ H).toReal * ∫ z, jb z ^ (-γ) := by
  have hI := c08_aux_jb_rpow_integrable γ hγ
  have hi : Integrable H := (hI.const_mul _).mono' hH.1.aestronglyMeasurable
    (Eventually.of_forall fun z => c08_aux_Z_pointwise hH z)
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi.norm (hI.const_mul _) (fun z => c08_aux_Z_pointwise hH z)

/-- Differentiation under a convolution with a bounded `C¹` kernel. -/
theorem c08_aux_conv_hasDerivAt {K K' H : ℝ → ℂ} {B : ℝ} (hK : Continuous K)
    (hK' : Continuous K') (hK'b : ∀ x, ‖K' x‖ ≤ B) (hd : ∀ x, HasDerivAt K (K' x) x)
    (hKb : ∃ B0, ∀ x, ‖K x‖ ≤ B0) (hH : Integrable H) (y : ℝ) :
    HasDerivAt (fun y => ∫ z, K (y - z) * H z) (∫ z, K' (y - z) * H z) y := by
  obtain ⟨B0, hB0⟩ := hKb
  have hmeas : ∀ y : ℝ, AEStronglyMeasurable (fun z => K (y - z) * H z) volume := fun y =>
    (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hH.aestronglyMeasurable
  have hint : Integrable (fun z => K (y - z) * H z) :=
    hH.bdd_mul (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => hB0 (y - z))
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := y)
    (F := fun y z => K (y - z) * H z) (F' := fun y z => K' (y - z) * H z)
    (bound := fun z => B * ‖H z‖) (s := univ) Filter.univ_mem (Eventually.of_forall hmeas) hint
    ((hK'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hH.aestronglyMeasurable)
    (Eventually.of_forall fun z x _ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hK'b _) (norm_nonneg _))
    (hH.norm.const_mul B)
    (Eventually.of_forall fun z x _ => by
      have h1 : HasDerivAt (fun x => K (x - z)) (K' (x - z)) x := by
        have := (hd (x - z)).comp_sub_const x z
        simpa using this
      exact h1.mul_const (H z))
  exact this.2

/-- Continuity of a convolution with a bounded continuous kernel. -/
theorem c08_aux_conv_continuous {K H : ℝ → ℂ} {B : ℝ} (hK : Continuous K)
    (hKb : ∀ x, ‖K x‖ ≤ B) (hH : Integrable H) :
    Continuous (fun y => ∫ z, K (y - z) * H z) := by
  refine continuous_of_dominated (bound := fun z => B * ‖H z‖) (fun y =>
    (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hH.aestronglyMeasurable)
    (fun y => Eventually.of_forall fun z => ?_) (hH.norm.const_mul B)
    (Eventually.of_forall fun z => ?_)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hKb _) (norm_nonneg _)
  · exact (hK.comp (continuous_id.sub continuous_const)).mul continuous_const

theorem c08_aux_Hk_basic (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ k : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (c08_low_operators_H p k) ∧
      (∀ j : ℕ, j ≤ 2 → Continuous (iteratedDeriv j (c08_low_operators_H p k))) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ y, ‖iteratedDeriv j (c08_low_operators_H p k) y‖ ≤
        C₁ * C₂ ^ k * jb y ^ (-p - 2 - (j : ℝ))) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ y, ‖iteratedDeriv j (c08_low_operators_H p k) y‖ ≤ C₁ * C₂ ^ k) ∧
      (∀ j : ℕ, ∀ x, HasDerivAt (iteratedDeriv j (c08_low_operators_H p k))
        (iteratedDeriv (j + 1) (c08_low_operators_H p k) x) x) := by
  obtain ⟨C₁, C₂, C₁', hC₁, hC₂, -, hbd, -, hsm⟩ := c08_Hk_kernel p hp hp1
  refine ⟨C₁, C₂, hC₁, hC₂, fun k => ⟨(hsm k).1, fun j _ =>
    (hsm k).1.continuous_iteratedDeriv j (by exact_mod_cast le_top), hbd k, fun j hj y => ?_,
    fun j x => ?_⟩⟩
  · refine (hbd k j hj y).trans ?_
    have h1 : jb y ^ (-p - 2 - (j : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c08_aux_one_le_jb y)
        (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    have h2 : 0 ≤ C₁ * C₂ ^ k := by positivity
    calc C₁ * C₂ ^ k * jb y ^ (-p - 2 - (j : ℝ)) ≤ C₁ * C₂ ^ k * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = C₁ * C₂ ^ k := mul_one _
  · rw [iteratedDeriv_succ]
    have hd : Differentiable ℝ (iteratedDeriv j (c08_low_operators_H p k)) :=
      (hsm k).1.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)
    exact (hd x).hasDerivAt

/-- Blueprint: lem:c08_Mk_differentiation.  For `H ∈ Z_γ` (`γ > 1`): `ℳ_k H ∈ C²(ℝ;ℂ)` and
`∂^j ℳ_k H(y) = ∫ H_k^{(j)}(y-z) H(z) dz` (`j ≤ 2`, every `y`), each integral absolutely
convergent; and `‖H‖_{L¹} ≤ C_γ ‖H‖_{Z_γ}` with `C_γ` independent of `H`. -/
theorem c08_Mk_differentiation (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), ∀ H ∈ c08_Z_gamma γ,
      ContDiff ℝ 2 (c08_low_operators_M p k H) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
        Integrable (fun z => iteratedDeriv j (c08_low_operators_H p k) (y - z) * H z) ∧
        iteratedDeriv j (c08_low_operators_M p k H) y =
          ∫ z, iteratedDeriv j (c08_low_operators_H p k) (y - z) * H z) ∧
      Integrable H ∧
      ∫ z, ‖H z‖ ≤ C * (c08_Z_gamma_norm γ H).toReal := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hK⟩ := c08_aux_Hk_basic p hp hp1
  have hI := c08_aux_jb_rpow_integrable γ hγ
  have hI0 : 0 ≤ ∫ z, jb z ^ (-γ) :=
    integral_nonneg fun z => (Real.rpow_pos_of_pos (c08_aux_jb_pos z) _).le
  refine ⟨(∫ z, jb z ^ (-γ)) + 1, by positivity, fun k H hH => ?_⟩
  obtain ⟨-, hcont, -, hb, hder⟩ := hK k
  obtain ⟨hHi, hHL1⟩ := c08_aux_Z_integrable hγ hH
  set D : ℕ → ℝ → ℂ := fun j => iteratedDeriv j (c08_low_operators_H p k) with hD
  set F : ℕ → ℝ → ℂ := fun j y => ∫ z, D j (y - z) * H z with hF
  have hF0 : c08_low_operators_M p k H = F 0 := by
    ext y; simp [hF, hD, c08_low_operators_M]
  have hFd : ∀ j, j ≤ 1 → ∀ y, HasDerivAt (F j) (F (j + 1) y) y := by
    intro j hj y
    exact c08_aux_conv_hasDerivAt (hcont j (by omega)) (hcont (j + 1) (by omega))
      (hb (j + 1) (by omega)) (hder j) ⟨_, hb j (by omega)⟩ hHi y
  have hdF0 : deriv (F 0) = F 1 := funext fun y => (hFd 0 (by norm_num) y).deriv
  have hdF1 : deriv (F 1) = F 2 := funext fun y => (hFd 1 le_rfl y).deriv
  have hF2c : Continuous (F 2) := c08_aux_conv_continuous (hcont 2 le_rfl) (hb 2 le_rfl) hHi
  have hdiff0 : Differentiable ℝ (F 0) := fun y => (hFd 0 (by norm_num) y).differentiableAt
  have hdiff1 : Differentiable ℝ (F 1) := fun y => (hFd 1 le_rfl y).differentiableAt
  have hit : ∀ j, j ≤ 2 → iteratedDeriv j (F 0) = F j := by
    intro j hj
    interval_cases j
    · simp
    · rw [iteratedDeriv_one, hdF0]
    · rw [iteratedDeriv_succ, iteratedDeriv_one, hdF0, hdF1]
  refine ⟨?_, fun j hj y => ⟨?_, ?_⟩, hHi, ?_⟩
  · rw [hF0]
    have h1 : ContDiff ℝ 1 (F 1) := contDiff_one_iff_deriv.2 ⟨hdiff1, by rw [hdF1]; exact hF2c⟩
    exact (contDiff_succ_iff_deriv (n := 1)).2 ⟨hdiff0, by simp, by rw [hdF0]; exact h1⟩
  · exact hHi.bdd_mul ((hcont j hj).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => hb j hj (y - z))
  · rw [hF0, hit j hj]
  · calc ∫ z, ‖H z‖ ≤ (c08_Z_gamma_norm γ H).toReal * ∫ z, jb z ^ (-γ) := hHL1
      _ ≤ ((∫ z, jb z ^ (-γ)) + 1) * (c08_Z_gamma_norm γ H).toReal := by
          have := ENNReal.toReal_nonneg (a := c08_Z_gamma_norm γ H); nlinarith

/-- Blueprint: lem:c08_Mk_global_decay.  For `1 < γ < p + 2`: `|∂^j ℳ_k H(y)| ≤ C Q^k ‖H‖_{Z_γ} ⟨y⟩^{-γ}`
for all `k`, `H ∈ Z_γ`, `j ≤ 2`, `y ∈ ℝ`. -/
theorem c08_Mk_global_decay (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (hγ' : γ < p + 2) :
    ∃ C Q : ℝ, 0 < C ∧ 0 < Q ∧ ∀ (k : ℕ), ∀ H ∈ c08_Z_gamma γ, ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
      ‖iteratedDeriv j (c08_low_operators_M p k H) y‖ ≤
        C * Q ^ k * (c08_Z_gamma_norm γ H).toReal * jb y ^ (-γ) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hK⟩ := c08_aux_Hk_basic p hp hp1
  obtain ⟨_, _, hMd⟩ := c08_Mk_differentiation p γ hp hp1 hγ
  have hw : ∀ j : ℕ, ∃ Cw : ℝ, 0 < Cw ∧ ∀ y : ℝ,
      Integrable (fun z => jb (y - z) ^ (-(p + 2 + j)) * jb z ^ (-γ)) ∧
      ∫ z, jb (y - z) ^ (-(p + 2 + j)) * jb z ^ (-γ) ≤ Cw * jb y ^ (-γ) := fun j =>
    c08_convolution_weight (p + 2 + j) γ hγ (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  choose Cw hCw hCwb using hw
  refine ⟨C₁ * (Cw 0 + Cw 1 + Cw 2), C₂, by
    have := hCw 0; have := hCw 1; have := hCw 2; positivity, hC₂, fun k H hH j hj y => ?_⟩
  obtain ⟨-, -, hb, -, -⟩ := hK k
  obtain ⟨-, hrep, -, -⟩ := hMd k H hH
  obtain ⟨hint, heq⟩ := hrep j hj y
  set Z := (c08_Z_gamma_norm γ H).toReal
  have hZ : 0 ≤ Z := ENNReal.toReal_nonneg
  have hcj : Cw j ≤ Cw 0 + Cw 1 + Cw 2 := by
    have := hCw 0; have := hCw 1; have := hCw 2
    interval_cases j <;> linarith
  obtain ⟨hwi, hwb⟩ := hCwb j y
  rw [heq]
  calc ‖∫ z, iteratedDeriv j (c08_low_operators_H p k) (y - z) * H z‖
      ≤ ∫ z, ‖iteratedDeriv j (c08_low_operators_H p k) (y - z) * H z‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, (C₁ * C₂ ^ k * Z) * (jb (y - z) ^ (-(p + 2 + j)) * jb z ^ (-γ)) := by
        refine integral_mono hint.norm (hwi.const_mul _) (fun z => ?_)
        rw [norm_mul]
        have h1 := hb j hj (y - z)
        have h2 := c08_aux_Z_pointwise hH z
        have e : -p - 2 - (j : ℝ) = -(p + 2 + j) := by ring
        rw [e] at h1
        calc ‖iteratedDeriv j (c08_low_operators_H p k) (y - z)‖ * ‖H z‖
            ≤ (C₁ * C₂ ^ k * jb (y - z) ^ (-(p + 2 + j))) * (Z * jb z ^ (-γ)) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by
                have := Real.rpow_pos_of_pos (c08_aux_jb_pos (y - z)) (-(p + 2 + j)); positivity)
          _ = _ := by ring
    _ = (C₁ * C₂ ^ k * Z) * ∫ z, jb (y - z) ^ (-(p + 2 + j)) * jb z ^ (-γ) := integral_const_mul _ _
    _ ≤ (C₁ * C₂ ^ k * Z) * (Cw j * jb y ^ (-γ)) := mul_le_mul_of_nonneg_left hwb (by positivity)
    _ ≤ (C₁ * C₂ ^ k * Z) * ((Cw 0 + Cw 1 + Cw 2) * jb y ^ (-γ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hcj (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
    _ = _ := by ring

/-- An a.e. inequality between functions continuous on an open set holds everywhere there. -/
theorem c08_aux_le_on_open {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hg : ContinuousOn g U) (h : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ U → f x ≤ g x) :
    ∀ x ∈ U, f x ≤ g x := by
  intro x hx
  by_contra hlt
  push Not at hlt
  set S := U ∩ (fun t => f t - g t) ⁻¹' Ioi 0
  have hSo : IsOpen S := (hf.sub hg).isOpen_inter_preimage hU isOpen_Ioi
  have hxS : x ∈ S := ⟨hx, by simp only [mem_preimage, mem_Ioi]; linarith⟩
  have hpos : 0 < volume S := hSo.measure_pos volume ⟨x, hxS⟩
  have hnull : volume S = 0 := by
    rw [ae_iff] at h
    refine measure_mono_null (fun t ht => ?_) h
    simp only [mem_setOf, not_imp, not_le]
    exact ⟨ht.1, by have := ht.2; simp only [mem_preimage, mem_Ioi] at this; linarith⟩
  exact absurd hnull hpos.ne'

/-- Negative-axis derivative bounds for `H ∈ Z_γ`. -/
theorem c08_aux_Z_neg_bounds {γ : ℝ} {H : ℝ → ℂ} (hH : H ∈ c08_Z_gamma γ) :
    (∀ z, z < -1 → ‖deriv H z‖ ≤ (c08_Z_gamma_norm γ H).toReal * jb z ^ (-γ - 1)) ∧
    (∀ᵐ z ∂(volume : Measure ℝ), z < -1 →
      ‖deriv (deriv H) z‖ ≤ (c08_Z_gamma_norm γ H).toReal * jb z ^ (-γ - 2)) := by
  have hfin := hH.2.2.2
  have hE : essSup (fun y => ENNReal.ofReal (jb y ^ γ * (jb y * ‖deriv H y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv H) y‖))) (volume.restrict (Iic (-1))) ≤
      c08_Z_gamma_norm γ H := by
    unfold c08_Z_gamma_norm; exact le_add_self
  have h2 := lt_of_le_of_lt hE hfin
  set Z := (c08_Z_gamma_norm γ H).toReal with hZdef
  have hZ := ENNReal.toReal_mono hfin.ne hE
  have hae := (ae_restrict_iff' measurableSet_Iic).1 (c08_aux_ae_le_essSup_toReal h2)
  have hpt : ∀ᵐ z ∂(volume : Measure ℝ), z ≤ -1 →
      ‖deriv H z‖ ≤ Z * jb z ^ (-γ - 1) ∧ ‖deriv (deriv H) z‖ ≤ Z * jb z ^ (-γ - 2) := by
    filter_upwards [hae] with z hz hz1
    have hz := (hz hz1).trans hZ
    have hj := c08_aux_jb_pos z
    have hg0 : 0 ≤ jb z ^ γ := (Real.rpow_pos_of_pos hj γ).le
    have n1 := norm_nonneg (deriv H z); have n2 := norm_nonneg (deriv (deriv H) z)
    have hj2 : 0 ≤ jb z ^ (2 : ℕ) := by positivity
    constructor
    · rw [show -γ - 1 = -(γ + 1) by ring]
      refine c08_aux_div_weight (γ := γ + 1) ?_
      rw [Real.rpow_add hj, Real.rpow_one]
      calc jb z ^ γ * jb z * ‖deriv H z‖ = jb z ^ γ * (jb z * ‖deriv H z‖) := by ring
        _ ≤ jb z ^ γ * (jb z * ‖deriv H z‖ + jb z ^ (2 : ℕ) * ‖deriv (deriv H) z‖) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hj2 n2)) hg0
        _ ≤ Z := hz
    · rw [show -γ - 2 = -(γ + 2) by ring]
      refine c08_aux_div_weight (γ := γ + 2) ?_
      rw [Real.rpow_add hj,
        show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      calc jb z ^ γ * jb z ^ (2 : ℕ) * ‖deriv (deriv H) z‖ =
            jb z ^ γ * (jb z ^ (2 : ℕ) * ‖deriv (deriv H) z‖) := by ring
        _ ≤ jb z ^ γ * (jb z * ‖deriv H z‖ + jb z ^ (2 : ℕ) * ‖deriv (deriv H) z‖) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hj.le n1)) hg0
        _ ≤ Z := hz
  refine ⟨?_, by filter_upwards [hpt] with z hz hz1 using (hz hz1.le).2⟩
  have hjc : Continuous jb := by unfold jb; fun_prop
  have hc1 : ContinuousOn (deriv H) (Iio (-1)) :=
    hH.2.1.continuousOn_deriv_of_isOpen isOpen_Iio le_rfl
  exact c08_aux_le_on_open isOpen_Iio hc1.norm
    (continuous_const.mul (hjc.rpow_const fun z => Or.inl (c08_aux_jb_pos z).ne')).continuousOn
    (by filter_upwards [hpt] with z hz hz1 using (hz (le_of_lt hz1)).1)

/-- Mean value inequality on `uIcc a b`. -/
theorem c08_aux_mvt {f f' : ℝ → ℂ} {a b C : ℝ} (hd : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ uIcc a b, ‖f' x‖ ≤ C) : ‖f b - f a‖ ≤ C * |b - a| := by
  rcases le_total a b with hab | hab
  · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (C := C)
      (fun x hx => (hd x (by rw [uIcc_of_le hab]; exact hx)).hasDerivWithinAt)
      (fun x hx => hb x (by rw [uIcc_of_le hab]; exact Ico_subset_Icc_self hx)) b
      (right_mem_Icc.2 hab)
    rwa [abs_of_nonneg (sub_nonneg.2 hab)]
  · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (C := C)
      (fun x hx => (hd x (by rw [uIcc_of_ge hab]; exact hx)).hasDerivWithinAt)
      (fun x hx => hb x (by rw [uIcc_of_ge hab]; exact Ico_subset_Icc_self hx)) a
      (right_mem_Icc.2 hab)
    rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]; exact this

/-- First- and second-order Taylor bounds for `H ∈ Z_γ` on a window inside `(-∞,-1)`. -/
theorem c08_aux_Z_taylor {γ : ℝ} {H : ℝ → ℂ} (hH : H ∈ c08_Z_gamma γ) {y L K1 K2 : ℝ}
    (hL : 0 < L) (hreg : y + L < -1)
    (hK1 : ∀ z ∈ Icc (y - L) (y + L), ‖deriv H z‖ ≤ K1)
    (hK2 : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Icc (y - L) (y + L) → ‖deriv (deriv H) z‖ ≤ K2)
    (hK2pos : 0 ≤ K2) :
    ∀ u, |u| ≤ L → ‖H (y - u) - H y‖ ≤ K1 * |u| ∧
      ‖H (y - u) - H y + u * deriv H y‖ ≤ K2 * u ^ 2 := by
  set a := y - L; set b := y + L
  have hR : Icc a b ⊆ Iio (-1) := fun z hz => lt_of_le_of_lt hz.2 hreg
  have hdiff : ∀ z ∈ Icc a b, HasDerivAt H (deriv H z) z := fun z hz =>
    ((hH.2.1.differentiableOn one_ne_zero).differentiableAt (isOpen_Iio.mem_nhds (hR hz))).hasDerivAt
  -- Lipschitz bound for `H'` on the window via a clamped extension
  obtain ⟨K, hK⟩ := (hH.2.2.1.mono hR).exists_lipschitzOnWith_of_compact isCompact_Icc
  set c : ℝ → ℝ := fun t => max a (min t b)
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hc : LipschitzWith 1 c := (LipschitzWith.id.min_const b).const_max a
  have hcm : ∀ t, c t ∈ Icc a b := fun t => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  set g : ℝ → ℂ := fun t => deriv H (c t)
  have hgL : LocallyLipschitz g := by
    have : LipschitzOnWith (K * 1) g univ :=
      hK.comp hc.lipschitzOnWith (fun t _ => hcm t)
    exact (lipschitzOnWith_univ.1 this).locallyLipschitz
  have hgeq : ∀ t ∈ Icc a b, g t = deriv H t := fun t ht => by
    simp only [g, c, min_eq_left ht.2, max_eq_right ht.1]
  have hgd : ∀ t ∈ Ioo a b, deriv g t = deriv (deriv H) t := by
    intro t ht
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hgeq s (Ioo_subset_Icc_self hs)
  have hlip2 : ∀ s1 ∈ Icc a b, ∀ s2 ∈ Icc a b, ‖deriv H s2 - deriv H s1‖ ≤ K2 * |s2 - s1| := by
    have key : ∀ s1 ∈ Icc a b, ∀ s2 ∈ Icc a b, s1 ≤ s2 →
        ‖deriv H s2 - deriv H s1‖ ≤ K2 * |s2 - s1| := by
      intro s1 h1 s2 h2 h12
      have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a ∧ t ≠ b := by
        filter_upwards [compl_mem_ae_iff.2 (measure_singleton a),
          compl_mem_ae_iff.2 (measure_singleton b)] with t ha hb
        exact ⟨ha, hb⟩
      have := c08_aux_lip_C hgL h12 (K := K2) (by
        filter_upwards [hK2, hnull] with t ht hne htI
        have htI' : t ∈ Ioo a b := ⟨lt_of_le_of_ne (h1.1.trans htI.1) (Ne.symm hne.1),
          lt_of_le_of_ne (htI.2.trans h2.2) hne.2⟩
        rw [hgd t htI']
        exact ht (Ioo_subset_Icc_self htI'))
      rw [hgeq s2 h2, hgeq s1 h1] at this
      rwa [abs_of_nonneg (sub_nonneg.2 h12)]
    intro s1 h1 s2 h2
    rcases le_total s1 s2 with h | h
    · exact key s1 h1 s2 h2 h
    · rw [norm_sub_rev, abs_sub_comm]; exact key s2 h2 s1 h1 h
  intro u hu
  have hsu : ∀ s ∈ uIcc 0 u, |s| ≤ |u| := by
    intro s hs
    rcases le_total 0 u with h0 | h0
    · rw [uIcc_of_le h0] at hs; rw [abs_of_nonneg hs.1, abs_of_nonneg h0]; exact hs.2
    · rw [uIcc_of_ge h0] at hs; rw [abs_of_nonpos hs.2, abs_of_nonpos h0]; linarith [hs.1]
  have hmem : ∀ s ∈ uIcc 0 u, y - s ∈ Icc a b := by
    intro s hs
    have := abs_le.1 ((hsu s hs).trans hu)
    simp only [a, b]; constructor <;> linarith
  have hHd : ∀ s ∈ uIcc 0 u, HasDerivAt (fun s => H (y - s)) (-deriv H (y - s)) s := by
    intro s hs
    exact (hdiff (y - s) (hmem s hs)).comp_const_sub y s
  constructor
  · have := c08_aux_mvt (f := fun s => H (y - s)) (a := 0) (b := u) (C := K1) hHd
      (fun s hs => by rw [norm_neg]; exact hK1 _ (hmem s hs))
    simpa using this
  · have hy : y ∈ Icc a b := by simpa using hmem 0 (left_mem_uIcc)
    have := c08_aux_mvt (f := fun s => H (y - s) + s * deriv H y)
      (f' := fun s => -deriv H (y - s) + deriv H y) (a := 0) (b := u) (C := K2 * |u|)
      (fun s hs => (hHd s hs).add (by simpa using (hasDerivAt_id s).ofReal_comp.mul_const (deriv H y)))
      (fun s hs => by
        rw [neg_add_eq_sub]
        refine (hlip2 _ (hmem s hs) _ hy).trans ?_
        apply mul_le_mul_of_nonneg_left _ hK2pos
        rw [sub_sub_cancel]; exact hsu s hs)
    simp only [Complex.ofReal_zero, zero_mul, add_zero, sub_zero] at this
    rw [show H (y - u) - H y + u * deriv H y = H (y - u) + u * deriv H y - H y by ring,
      show K2 * u ^ 2 = K2 * |u| * |u| by rw [mul_assoc, abs_mul_abs_self, sq]]
    exact this


/-- Far-region weight: `|u| ≥ ⟨y⟩/8` gives `⟨u⟩^{-s} ≤ 8^s ⟨y⟩^{-s}`. -/
theorem c08_aux_far_weight {u y s : ℝ} (hs : 0 ≤ s) (hu : jb y / 8 < |u|) :
    jb u ^ (-s) ≤ 8 ^ s * jb y ^ (-s) := by
  have hj := c08_aux_jb_pos y
  have h1 : jb y / 8 ≤ jb u := hu.le.trans (by
    unfold jb; exact Real.abs_le_sqrt (by nlinarith [sq_abs u]))
  have hpos : 0 < jb y / 8 := by positivity
  calc jb u ^ (-s) ≤ (jb y / 8) ^ (-s) := Real.rpow_le_rpow_of_nonpos hpos h1 (by linarith)
    _ = 8 ^ s * jb y ^ (-s) := by
      rw [Real.div_rpow hj.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8)]
      field_simp

/-- `‖∫_s f‖ ≤ ∫_s g` from a pointwise bound on `s`. -/
theorem c08_aux_setint_le {f : ℝ → ℂ} {g : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hg : IntegrableOn g s) (h : ∀ u ∈ s, ‖f u‖ ≤ g u) : ‖∫ u in s, f u‖ ≤ ∫ u in s, g u :=
  norm_integral_le_of_norm_le hg ((ae_restrict_iff' hs).2 (Eventually.of_forall h))

/-- The core near/far estimate behind lem:c08_Mk_negative_gain (first and second derivatives). -/
theorem c08_aux_neg_gain_core {p γ : ℝ} (hp : 0 < p) (hγp : γ < p + 2) (hγ : 0 ≤ γ)
    {D0 D1 D2 H : ℝ → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hD0 : Continuous D0) (hD1 : Continuous D1) (hD2 : Continuous D2)
    (hb0 : ∀ u, ‖D0 u‖ ≤ c * jb u ^ (-p - 2)) (hb1 : ∀ u, ‖D1 u‖ ≤ c * jb u ^ (-p - 3))
    (hb2 : ∀ u, ‖D2 u‖ ≤ c * jb u ^ (-p - 4))
    (hd0 : ∀ u, HasDerivAt D0 (D1 u) u) (hd1 : ∀ u, HasDerivAt D1 (D2 u) u)
    (hH : Integrable H) (hHc : Continuous H) {y K0 K1 K1' K2 : ℝ}
    (hK0 : ‖H y‖ ≤ K0) (hK1' : ‖deriv H y‖ ≤ K1')
    (hT : ∀ u, |u| ≤ jb y / 8 → ‖H (y - u) - H y‖ ≤ K1 * |u| ∧
      ‖H (y - u) - H y + u * deriv H y‖ ≤ K2 * u ^ 2) (hK1p : 0 ≤ K1) (hK2p : 0 ≤ K2) :
    ‖∫ u, D1 u * H (y - u)‖ ≤ c * (8 ^ (γ + 1) * jb y ^ (-γ - 1) * (∫ z, ‖H z‖) +
        K1 * (∫ u, jb u ^ (-p - 2)) + K0 * (8 * jb y ^ (-1 : ℝ)) * (∫ u, jb u ^ (-p - 2))) ∧
    ‖∫ u, D2 u * H (y - u)‖ ≤ c * (8 ^ (γ + 2) * jb y ^ (-γ - 2) * (∫ z, ‖H z‖) +
        K2 * (∫ u, jb u ^ (-p - 2)) + K0 * (64 * jb y ^ (-2 : ℝ)) * (∫ u, jb u ^ (-p - 2)) +
        K1' * (8 * jb y ^ (-1 : ℝ)) * (∫ u, jb u ^ (-p - 2))) := by
  set L := jb y / 8
  set S : Set ℝ := {u | |u| ≤ L} with hSdef
  have hS : MeasurableSet S := measurableSet_le continuous_abs.measurable measurable_const
  have hSc : ∀ u ∈ Sᶜ, L < |u| := fun u hu => not_le.1 hu
  have hjy := c08_aux_jb_pos y
  have hI := c08_aux_jb_rpow_integrable (p + 2) (by linarith)
  have hI' : Integrable (fun u => jb u ^ (-p - 2)) := by
    simpa [show -(p + 2) = -p - 2 by ring] using hI
  set I := ∫ u, jb u ^ (-p - 2)
  have hI0 : 0 ≤ I := integral_nonneg fun u => (Real.rpow_pos_of_pos (c08_aux_jb_pos u) _).le
  have hw0 : ∀ u, 0 ≤ jb u ^ (-p - 2) := fun u => (Real.rpow_pos_of_pos (c08_aux_jb_pos u) _).le
  -- weight algebra
  have wsplit : ∀ (u : ℝ) (k : ℝ), jb u ^ (-p - 2 - k) = jb u ^ (-k) * jb u ^ (-p - 2) := by
    intro u k; rw [← Real.rpow_add (c08_aux_jb_pos u)]; ring_nf
  have wabs : ∀ (u : ℝ) (k : ℝ), 0 ≤ k → |u| ^ k * jb u ^ (-k) ≤ 1 := by
    intro u k hk
    have hju := c08_aux_jb_pos u
    have : |u| ≤ jb u := by unfold jb; exact Real.abs_le_sqrt (by nlinarith [sq_abs u])
    calc |u| ^ k * jb u ^ (-k) ≤ jb u ^ k * jb u ^ (-k) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg u) this hk)
            (Real.rpow_pos_of_pos hju _).le
      _ = 1 := by rw [← Real.rpow_add hju]; simp
  have wfar : ∀ u ∈ Sᶜ, ∀ k : ℝ, 0 ≤ k → jb u ^ (-k) ≤ 8 ^ k * jb y ^ (-k) :=
    fun u hu k hk => c08_aux_far_weight hk (hSc u hu)
  have wle : ∀ (u a b : ℝ), a ≤ b → jb u ^ a ≤ jb u ^ b := fun u a b h =>
    Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb u) h
  -- integrability
  have hbdd : ∀ (D : ℝ → ℂ) (k : ℝ), 0 ≤ k → (∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2 - k)) →
      ∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2) := by
    intro D k hk h u
    exact (h u).trans (mul_le_mul_of_nonneg_left (wle u _ _ (by linarith)) hc)
  have hb1' : ∀ u, ‖D1 u‖ ≤ c * jb u ^ (-p - 2 - 1) := fun u => by
    rw [show -p - 2 - 1 = -p - 3 by ring]; exact hb1 u
  have hb2' : ∀ u, ‖D2 u‖ ≤ c * jb u ^ (-p - 2 - 2) := fun u => by
    rw [show -p - 2 - 2 = -p - 4 by ring]; exact hb2 u
  have iD : ∀ D : ℝ → ℂ, Continuous D → (∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2)) → Integrable D :=
    fun D hD h => (hI'.const_mul c).mono' hD.aestronglyMeasurable (Eventually.of_forall h)
  have iD0 := iD D0 hD0 hb0
  have iD1 := iD D1 hD1 (hbdd D1 1 zero_le_one hb1')
  have iD2 := iD D2 hD2 (hbdd D2 2 zero_le_two hb2')
  have huD : ∀ (D : ℝ → ℂ) (k : ℝ), 1 ≤ k → Continuous D → (∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2 - k)) →
      ∀ u : ℝ, ‖(u : ℂ) * D u‖ ≤ c * jb u ^ (-p - 2) := by
    intro D k hk hDc h u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := wabs u 1 zero_le_one
    rw [Real.rpow_one] at this
    calc |u| * ‖D u‖ ≤ |u| * (c * (jb u ^ (-1 : ℝ) * jb u ^ (-p - 2))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg u)
          refine (h u).trans (mul_le_mul_of_nonneg_left ?_ hc)
          rw [← wsplit]; exact wle u _ _ (by linarith)
      _ = c * (|u| * jb u ^ (-1 : ℝ)) * jb u ^ (-p - 2) := by ring
      _ ≤ c * 1 * jb u ^ (-p - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) (hw0 u)
      _ = c * jb u ^ (-p - 2) := by ring
  have iuD1 : Integrable (fun u : ℝ => (u : ℂ) * D1 u) :=
    iD _ (Complex.continuous_ofReal.mul hD1) (huD D1 1 le_rfl hD1 hb1')
  have iuD2 : Integrable (fun u : ℝ => (u : ℂ) * D2 u) :=
    iD _ (Complex.continuous_ofReal.mul hD2) (huD D2 2 one_le_two hD2 hb2')
  have z1 : ∫ u, D1 u = 0 := integral_eq_zero_of_hasDerivAt_of_integrable hd0 iD1 iD0
  have z2 : ∫ u, D2 u = 0 := integral_eq_zero_of_hasDerivAt_of_integrable hd1 iD2 iD1
  have z3 : ∫ u : ℝ, (u : ℂ) * D2 u = 0 := by
    refine integral_eq_zero_of_hasDerivAt_of_integrable (f := fun u : ℝ => (u : ℂ) * D1 u - D0 u)
      (fun u => ?_) iuD2 (iuD1.sub iD0)
    have := ((hasDerivAt_id u).ofReal_comp.mul (hd1 u)).sub (hd0 u)
    simp only [id, Complex.ofReal_one, one_mul] at this
    convert this using 1; ring
  have hHs : Integrable (fun u => H (y - u)) := hH.comp_sub_left y
  have hHn : ∫ u, ‖H (y - u)‖ = ∫ z, ‖H z‖ := integral_sub_left_eq_self (fun z => ‖H z‖) volume y
  have iDH : ∀ D : ℝ → ℂ, Continuous D → (∀ u, ‖D u‖ ≤ c) → Integrable (fun u => D u * H (y - u)) :=
    fun D hD h => hHs.bdd_mul hD.aestronglyMeasurable (Eventually.of_forall h)
  have hle1 : ∀ (D : ℝ → ℂ) (k : ℝ), 0 ≤ k → (∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2 - k)) →
      ∀ u, ‖D u‖ ≤ c := fun D k hk h u =>
    (h u).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos
      (c08_aux_one_le_jb u) (by linarith)) hc) (mul_one c))
  -- generic far bound
  have far : ∀ (D : ℝ → ℂ) (k : ℝ), 0 ≤ k → Continuous D → (∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2 - k)) →
      γ + k ≤ p + 2 + k →
      ‖∫ u in Sᶜ, D u * H (y - u)‖ ≤ c * (8 ^ (γ + k) * jb y ^ (-γ - k) * ∫ z, ‖H z‖) := by
    intro D k hk hDc h _
    have hgi : Integrable (fun u => c * (8 ^ (γ + k) * jb y ^ (-γ - k)) * ‖H (y - u)‖) :=
      hHs.norm.const_mul _
    refine (c08_aux_setint_le hS.compl hgi.integrableOn (fun u hu => ?_)).trans ?_
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      refine (h u).trans (mul_le_mul_of_nonneg_left ?_ hc)
      have := wfar u hu (γ + k) (by linarith)
      rw [show -γ - k = -(γ + k) by ring]
      exact (wle u _ _ (by linarith)).trans this
    · rw [integral_const_mul]
      have : ∫ u in Sᶜ, ‖H (y - u)‖ ≤ ∫ z, ‖H z‖ := by
        rw [← hHn]; exact setIntegral_le_integral hHs.norm (Eventually.of_forall fun _ => norm_nonneg _)
      have h8 : 0 ≤ c * (8 ^ (γ + k) * jb y ^ (-γ - k)) := by
        have := Real.rpow_pos_of_pos hjy (-γ - k); positivity
      calc c * (8 ^ (γ + k) * jb y ^ (-γ - k)) * ∫ u in Sᶜ, ‖H (y - u)‖
          ≤ c * (8 ^ (γ + k) * jb y ^ (-γ - k)) * ∫ z, ‖H z‖ := mul_le_mul_of_nonneg_left this h8
        _ = _ := by ring
  -- generic tail bound for `∫_{Sᶜ} |u|^m D`
  have tail : ∀ (D : ℝ → ℂ) (k : ℝ), 0 ≤ k → (∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2 - k)) →
      ∀ u ∈ Sᶜ, ‖D u‖ ≤ c * (8 ^ k * jb y ^ (-k)) * jb u ^ (-p - 2) := by
    intro D k hk h u hu
    calc ‖D u‖ ≤ c * jb u ^ (-p - 2 - k) := h u
      _ = c * (jb u ^ (-k) * jb u ^ (-p - 2)) := by rw [wsplit]
      _ ≤ c * (8 ^ k * jb y ^ (-k) * jb u ^ (-p - 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (wfar u hu k hk) (hw0 u)) hc
      _ = _ := by ring
  have hK0p : 0 ≤ K0 := (norm_nonneg _).trans hK0
  have hK1'p : 0 ≤ K1' := (norm_nonneg _).trans hK1'
  have hcompl : ∀ (f : ℝ → ℂ), Integrable f → ∫ u, f u = 0 → ∫ u in S, f u = -∫ u in Sᶜ, f u :=
    fun f hf hz => by have h := integral_add_compl hS hf; rw [hz] at h; linear_combination h
  have hSle : ∀ g : ℝ → ℝ, Integrable g → (∀ u, 0 ≤ g u) → ∫ u in S, g u ≤ ∫ u, g u :=
    fun g hg h0 => setIntegral_le_integral hg (Eventually.of_forall h0)
  have hScle : ∀ g : ℝ → ℝ, Integrable g → (∀ u, 0 ≤ g u) → ∫ u in Sᶜ, g u ≤ ∫ u, g u :=
    fun g hg h0 => setIntegral_le_integral hg (Eventually.of_forall h0)
  -- tail integrals of the kernels
  have tailInt : ∀ (D : ℝ → ℂ) (k : ℝ), 0 ≤ k → (∀ u, ‖D u‖ ≤ c * jb u ^ (-p - 2 - k)) →
      ‖∫ u in Sᶜ, D u‖ ≤ c * (8 ^ k * jb y ^ (-k)) * I := by
    intro D k hk h
    refine (c08_aux_setint_le hS.compl (hI'.const_mul _).integrableOn (tail D k hk h)).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hScle _ hI' hw0) (by
      have := Real.rpow_pos_of_pos hjy (-k); positivity)
  have hb1u : ∀ u : ℝ, ‖(u : ℂ) * D2 u‖ ≤ c * jb u ^ (-p - 2 - 1) := by
    intro u
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := wabs u 1 zero_le_one
    rw [Real.rpow_one] at this
    calc |u| * ‖D2 u‖ ≤ |u| * (c * (jb u ^ (-1 : ℝ) * jb u ^ (-p - 2 - 1))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg u)
          refine (hb2' u).trans (le_of_eq ?_)
          rw [← Real.rpow_add (c08_aux_jb_pos u)]; ring_nf
      _ = c * (|u| * jb u ^ (-1 : ℝ)) * jb u ^ (-p - 2 - 1) := by ring
      _ ≤ c * 1 * jb u ^ (-p - 2 - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc)
            (Real.rpow_pos_of_pos (c08_aux_jb_pos u) _).le
      _ = c * jb u ^ (-p - 2 - 1) := by ring
  constructor
  · -- first derivative
    have iH1 := iDH D1 hD1 (hle1 D1 1 zero_le_one hb1')
    have iA : Integrable (fun u => D1 u * (H (y - u) - H y)) := by
      have := iH1.sub (iD1.mul_const (H y))
      refine this.congr (Eventually.of_forall fun u => ?_); simp only [Pi.sub_apply]; ring
    have dec : ∫ u, D1 u * H (y - u) = (∫ u in S, D1 u * (H (y - u) - H y)) -
        H y * (∫ u in Sᶜ, D1 u) + ∫ u in Sᶜ, D1 u * H (y - u) := by
      have e1 : ∫ u in S, D1 u * H (y - u) = (∫ u in S, D1 u * (H (y - u) - H y)) +
          H y * ∫ u in S, D1 u := by
        rw [← integral_const_mul, ← integral_add iA.integrableOn (iD1.const_mul _).integrableOn]
        congr 1; funext u; ring
      rw [← integral_add_compl hS iH1, e1, hcompl D1 iD1 z1]; ring
    rw [dec]
    have A1 : ‖∫ u in S, D1 u * (H (y - u) - H y)‖ ≤ c * K1 * I := by
      refine (c08_aux_setint_le hS ((hI'.const_mul (c * K1)).integrableOn) (fun u hu => ?_)).trans ?_
      · rw [norm_mul]
        have h1 := (hT u hu).1
        have h2 := hb1' u
        have hw := wabs u 1 zero_le_one
        rw [Real.rpow_one] at hw
        calc ‖D1 u‖ * ‖H (y - u) - H y‖ ≤ (c * jb u ^ (-p - 2 - 1)) * (K1 * |u|) :=
              mul_le_mul h2 h1 (norm_nonneg _) (mul_nonneg hc (Real.rpow_pos_of_pos (c08_aux_jb_pos u) _).le)
          _ = c * K1 * (|u| * jb u ^ (-1 : ℝ)) * jb u ^ (-p - 2) := by rw [wsplit]; ring
          _ ≤ c * K1 * 1 * jb u ^ (-p - 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (mul_nonneg hc hK1p)) (hw0 u)
          _ = c * K1 * jb u ^ (-p - 2) := by ring
      · rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hSle _ hI' hw0) (mul_nonneg hc hK1p)
    have A2 : ‖H y * ∫ u in Sᶜ, D1 u‖ ≤ K0 * (c * (8 ^ (1:ℝ) * jb y ^ (-1 : ℝ)) * I) := by
      rw [norm_mul]
      exact mul_le_mul hK0 (tailInt D1 1 zero_le_one hb1') (norm_nonneg _) hK0p
    have A3 := far D1 1 zero_le_one hD1 hb1' (by linarith)
    rw [Real.rpow_one] at A2
    have t1 := norm_add_le ((∫ u in S, D1 u * (H (y - u) - H y)) - H y * (∫ u in Sᶜ, D1 u))
      (∫ u in Sᶜ, D1 u * H (y - u))
    have t2 := norm_sub_le (∫ u in S, D1 u * (H (y - u) - H y)) (H y * (∫ u in Sᶜ, D1 u))
    have : c * K1 * I + K0 * (c * (8 * jb y ^ (-1 : ℝ)) * I) +
        c * (8 ^ (γ + 1) * jb y ^ (-γ - 1) * ∫ z, ‖H z‖) =
        c * (8 ^ (γ + 1) * jb y ^ (-γ - 1) * (∫ z, ‖H z‖) +
        K1 * I + K0 * (8 * jb y ^ (-1 : ℝ)) * I) := by ring
    linarith
  · -- second derivative
    have iH2 := iDH D2 hD2 (hle1 D2 2 zero_le_two hb2')
    set Tf : ℝ → ℂ := fun u => H (y - u) - H y + u * deriv H y with hTf
    have iB : Integrable (fun u => D2 u * Tf u) := by
      have := (iH2.sub (iD2.mul_const (H y))).add (iuD2.mul_const (deriv H y))
      refine this.congr (Eventually.of_forall fun u => ?_); simp only [Pi.sub_apply, Pi.add_apply, hTf]; ring
    have dec : ∫ u, D2 u * H (y - u) = (∫ u in S, D2 u * Tf u) - H y * (∫ u in Sᶜ, D2 u) +
        deriv H y * (∫ u in Sᶜ, (u : ℂ) * D2 u) + ∫ u in Sᶜ, D2 u * H (y - u) := by
      have e1 : ∫ u in S, D2 u * H (y - u) = (∫ u in S, D2 u * Tf u) +
          H y * (∫ u in S, D2 u) - deriv H y * ∫ u in S, (u : ℂ) * D2 u := by
        have j1 : IntegrableOn (fun u => D2 u * Tf u + H y * D2 u) S :=
          (iB.add (iD2.const_mul (H y))).integrableOn
        have j2 : IntegrableOn (fun u : ℝ => deriv H y * ((u : ℂ) * D2 u)) S :=
          (iuD2.const_mul _).integrableOn
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add iB.integrableOn (iD2.const_mul _).integrableOn, ← integral_sub j1 j2]
        congr 1; funext u; simp only [hTf]; ring
      rw [← integral_add_compl hS iH2, e1, hcompl D2 iD2 z2, hcompl _ iuD2 z3]; ring
    rw [dec]
    have B1 : ‖∫ u in S, D2 u * Tf u‖ ≤ c * K2 * I := by
      refine (c08_aux_setint_le hS ((hI'.const_mul (c * K2)).integrableOn) (fun u hu => ?_)).trans ?_
      · rw [norm_mul]
        have h1 := (hT u hu).2
        have h2 := hb2' u
        have hw := wabs u 2 zero_le_two
        have hu2 : |u| ^ (2 : ℝ) = u ^ 2 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs]
        rw [hu2] at hw
        calc ‖D2 u‖ * ‖Tf u‖ ≤ (c * jb u ^ (-p - 2 - 2)) * (K2 * u ^ 2) :=
              mul_le_mul h2 h1 (norm_nonneg _) (mul_nonneg hc (Real.rpow_pos_of_pos (c08_aux_jb_pos u) _).le)
          _ = c * K2 * (u ^ 2 * jb u ^ (-2 : ℝ)) * jb u ^ (-p - 2) := by rw [wsplit]; ring
          _ ≤ c * K2 * 1 * jb u ^ (-p - 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (mul_nonneg hc hK2p)) (hw0 u)
          _ = c * K2 * jb u ^ (-p - 2) := by ring
      · rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hSle _ hI' hw0) (mul_nonneg hc hK2p)
    have B2 : ‖H y * ∫ u in Sᶜ, D2 u‖ ≤ K0 * (c * (8 ^ (2:ℝ) * jb y ^ (-2 : ℝ)) * I) := by
      rw [norm_mul]
      exact mul_le_mul hK0 (tailInt D2 2 zero_le_two hb2') (norm_nonneg _) hK0p
    have B3 : ‖deriv H y * ∫ u in Sᶜ, (u : ℂ) * D2 u‖ ≤ K1' * (c * (8 ^ (1:ℝ) * jb y ^ (-1 : ℝ)) * I) := by
      rw [norm_mul]
      exact mul_le_mul hK1' (tailInt _ 1 zero_le_one hb1u) (norm_nonneg _) hK1'p
    have B4 := far D2 2 zero_le_two hD2 hb2' (by linarith)
    rw [show (8:ℝ) ^ (2:ℝ) = 64 by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num]
      at B2
    rw [Real.rpow_one] at B3
    have t1 := norm_add_le ((∫ u in S, D2 u * Tf u) - H y * (∫ u in Sᶜ, D2 u) +
        deriv H y * (∫ u in Sᶜ, (u : ℂ) * D2 u)) (∫ u in Sᶜ, D2 u * H (y - u))
    have t2 := norm_add_le ((∫ u in S, D2 u * Tf u) - H y * (∫ u in Sᶜ, D2 u))
        (deriv H y * (∫ u in Sᶜ, (u : ℂ) * D2 u))
    have t3 := norm_sub_le (∫ u in S, D2 u * Tf u) (H y * (∫ u in Sᶜ, D2 u))
    have : c * K2 * I + K0 * (c * (64 * jb y ^ (-2 : ℝ)) * I) +
        K1' * (c * (8 * jb y ^ (-1 : ℝ)) * I) +
        c * (8 ^ (γ + 2) * jb y ^ (-γ - 2) * ∫ z, ‖H z‖) =
        c * (8 ^ (γ + 2) * jb y ^ (-γ - 2) * (∫ z, ‖H z‖) + K2 * I +
          K0 * (64 * jb y ^ (-2 : ℝ)) * I + K1' * (8 * jb y ^ (-1 : ℝ)) * I) := by ring
    linarith

/-- Blueprint: lem:c08_Mk_negative_gain.  For `1 < γ < p + 2`, `j ∈ {1,2}` and `y ≤ -2`:
`|∂^j ℳ_k H(y)| ≤ C Q^k ‖H‖_{Z_γ} ⟨y⟩^{-γ-j}`. -/
theorem c08_Mk_negative_gain (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (hγ' : γ < p + 2) :
    ∃ C Q : ℝ, 0 < C ∧ 0 < Q ∧ ∀ (k : ℕ), ∀ H ∈ c08_Z_gamma γ, ∀ j : ℕ, 1 ≤ j → j ≤ 2 →
      ∀ y : ℝ, y ≤ -2 →
        ‖iteratedDeriv j (c08_low_operators_M p k H) y‖ ≤
          C * Q ^ k * (c08_Z_gamma_norm γ H).toReal * jb y ^ (-γ - (j : ℝ)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Cd, hCd, hMd⟩ := c08_Mk_differentiation p γ hp hp1 hγ
  obtain ⟨C₁, C₂, hC₁, hC₂, hK⟩ := c08_aux_Hk_basic p hp hp1
  set I := ∫ u, jb u ^ (-p - 2)
  have hI0 : 0 ≤ I := integral_nonneg fun u => (Real.rpow_pos_of_pos (c08_aux_jb_pos u) _).le
  refine ⟨C₁ * (8 ^ (γ + 2) * Cd + 2 ^ (γ + 2) * I + 72 * I + 1), C₂, by positivity, hC₂,
    fun k H hH j hj1 hj2 y hy => ?_⟩
  obtain ⟨hsm, hcont, hbd, -, hder⟩ := hK k
  obtain ⟨-, hrep, hHi, hHL1⟩ := hMd k H hH
  set Z := (c08_Z_gamma_norm γ H).toReal
  have hZ0 : 0 ≤ Z := ENNReal.toReal_nonneg
  set c := C₁ * C₂ ^ k
  have hc : 0 ≤ c := by positivity
  set Dk : ℕ → ℝ → ℂ := fun j => iteratedDeriv j (c08_low_operators_H p k)
  have hbj : ∀ j : ℕ, j ≤ 2 → ∀ u, ‖Dk j u‖ ≤ c * jb u ^ (-p - 2 - (j : ℝ)) := hbd
  have hb0 : ∀ u, ‖Dk 0 u‖ ≤ c * jb u ^ (-p - 2) := fun u => by simpa using hbj 0 (by norm_num) u
  have hb1 : ∀ u, ‖Dk 1 u‖ ≤ c * jb u ^ (-p - 3) := fun u => by
    have := hbj 1 (by norm_num) u; rw [show -p - 2 - ((1:ℕ):ℝ) = -p - 3 by push_cast; ring] at this
    exact this
  have hb2 : ∀ u, ‖Dk 2 u‖ ≤ c * jb u ^ (-p - 4) := fun u => by
    have := hbj 2 le_rfl u; rw [show -p - 2 - ((2:ℕ):ℝ) = -p - 4 by push_cast; ring] at this
    exact this
  have hjy := c08_aux_jb_pos y
  set L := jb y / 8
  have hL : 0 < L := by positivity
  have hjyle : jb y ≤ 1 - y := by
    have := c08_aux_jb_le_one_add y; rw [abs_of_neg (by linarith)] at this; linarith
  have hreg : y + L < -1 := by simp only [L]; linarith
  have hwin : ∀ z ∈ Icc (y - L) (y + L), jb y ≤ 2 * jb z := by
    intro z hz
    have h1 : -z ≥ -y - L := by linarith [hz.2]
    have hzabs : |y| ≤ 2 * |z| := by
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith [hz.2])]
      simp only [L] at h1; linarith
    exact c08_aux_jb_le_two_mul hzabs
  obtain ⟨hH1, hH2⟩ := c08_aux_Z_neg_bounds hH
  have hK1 : ∀ z ∈ Icc (y - L) (y + L), ‖deriv H z‖ ≤ Z * 2 ^ (γ + 1) * jb y ^ (-(γ + 1)) := by
    intro z hz
    refine (hH1 z (by linarith [hz.2])).trans ?_
    rw [show -γ - 1 = -(γ + 1) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left (c08_aux_rpow_neg_le_of_le hjy (by linarith) (hwin z hz)) hZ0
  have hK2 : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Icc (y - L) (y + L) →
      ‖deriv (deriv H) z‖ ≤ Z * 2 ^ (γ + 2) * jb y ^ (-(γ + 2)) := by
    filter_upwards [hH2] with z hz hzI
    refine (hz (by linarith [hzI.2])).trans ?_
    rw [show -γ - 2 = -(γ + 2) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left (c08_aux_rpow_neg_le_of_le hjy (by linarith) (hwin z hzI)) hZ0
  have hT := c08_aux_Z_taylor hH hL hreg hK1 hK2 (by positivity)
  have hK0 : ‖H y‖ ≤ Z * jb y ^ (-γ) := c08_aux_Z_pointwise hH y
  have hK1' : ‖deriv H y‖ ≤ Z * jb y ^ (-γ - 1) := hH1 y (by linarith)
  have core := c08_aux_neg_gain_core hp0 hγ' (by linarith) hc (hcont 0 (by norm_num))
    (hcont 1 (by norm_num)) (hcont 2 le_rfl) hb0 hb1 hb2 (hder 0) (hder 1) hHi hH.1 hK0 hK1' hT
    (by positivity) (by positivity)
  have hshift : ∀ j, iteratedDeriv j (c08_low_operators_M p k H) y =
      ∫ z, Dk j (y - z) * H z → iteratedDeriv j (c08_low_operators_M p k H) y =
      ∫ u, Dk j u * H (y - u) := by
    intro j h
    rw [h, ← integral_sub_left_eq_self (fun z => Dk j (y - z) * H z) volume y]
    congr 1; funext u; simp only [sub_sub_cancel]
  have hHL1' : ∫ z, ‖H z‖ ≤ Cd * Z := hHL1
  have hHn0 : 0 ≤ ∫ z, ‖H z‖ := integral_nonneg fun _ => norm_nonneg _
  have e1 : jb y ^ (-γ) * jb y ^ (-1 : ℝ) = jb y ^ (-γ - 1) := by
    rw [← Real.rpow_add hjy]; ring_nf
  have e2 : jb y ^ (-γ) * jb y ^ (-2 : ℝ) = jb y ^ (-γ - 2) := by
    rw [← Real.rpow_add hjy]; ring_nf
  have e3 : jb y ^ (-γ - 1) * jb y ^ (-1 : ℝ) = jb y ^ (-γ - 2) := by
    rw [← Real.rpow_add hjy]; ring_nf
  have p8 : (8:ℝ) ^ (γ + 1) ≤ 8 ^ (γ + 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have p2 : (2:ℝ) ^ (γ + 1) ≤ 2 ^ (γ + 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have p8' : (0:ℝ) ≤ 8 ^ (γ + 1) := by positivity
  have p2' : (0:ℝ) ≤ 2 ^ (γ + 1) := by positivity
  interval_cases j
  · rw [hshift 1 (hrep 1 (by norm_num) y).2]
    refine core.1.trans ?_
    set J := jb y ^ (-γ - 1)
    have hJ : 0 ≤ J := (Real.rpow_pos_of_pos hjy _).le
    rw [show -(γ + 1) = -γ - 1 by ring, show -γ - ((1:ℕ):ℝ) = -γ - 1 by push_cast; ring]
    have hA : Z * jb y ^ (-γ) * (8 * jb y ^ (-1 : ℝ)) = 8 * Z * J := by
      rw [show Z * jb y ^ (-γ) * (8 * jb y ^ (-1 : ℝ)) = 8 * Z * (jb y ^ (-γ) * jb y ^ (-1 : ℝ)) by ring, e1]
    rw [hA]
    have h1 : 8 ^ (γ + 1) * J * (∫ z, ‖H z‖) ≤ 8 ^ (γ + 2) * J * (Cd * Z) :=
      mul_le_mul (mul_le_mul_of_nonneg_right p8 hJ) hHL1' hHn0 (by positivity)
    have h2 : Z * 2 ^ (γ + 1) * J * I ≤ Z * 2 ^ (γ + 2) * J * I := by gcongr
    have h3 : 0 ≤ Z * J * I := by positivity
    have h4 : 0 ≤ Z * J := by positivity
    calc c * (8 ^ (γ + 1) * J * (∫ z, ‖H z‖) + Z * 2 ^ (γ + 1) * J * I + 8 * Z * J * I)
        ≤ c * (8 ^ (γ + 2) * J * (Cd * Z) + Z * 2 ^ (γ + 2) * J * I + 8 * Z * J * I) := by gcongr
      _ ≤ c * (Z * J * (8 ^ (γ + 2) * Cd + 2 ^ (γ + 2) * I + 72 * I + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          nlinarith
      _ = C₁ * (8 ^ (γ + 2) * Cd + 2 ^ (γ + 2) * I + 72 * I + 1) * C₂ ^ k * Z * J := by
          simp only [c]; ring
  · rw [hshift 2 (hrep 2 le_rfl y).2]
    refine core.2.trans ?_
    set J := jb y ^ (-γ - 2)
    have hJ : 0 ≤ J := (Real.rpow_pos_of_pos hjy _).le
    rw [show -(γ + 2) = -γ - 2 by ring, show -γ - ((2:ℕ):ℝ) = -γ - 2 by push_cast; ring]
    have hA : Z * jb y ^ (-γ) * (64 * jb y ^ (-2 : ℝ)) = 64 * Z * J := by
      rw [show Z * jb y ^ (-γ) * (64 * jb y ^ (-2 : ℝ)) = 64 * Z * (jb y ^ (-γ) * jb y ^ (-2 : ℝ)) by
        ring, e2]
    have hB : Z * jb y ^ (-γ - 1) * (8 * jb y ^ (-1 : ℝ)) = 8 * Z * J := by
      rw [show Z * jb y ^ (-γ - 1) * (8 * jb y ^ (-1 : ℝ)) = 8 * Z * (jb y ^ (-γ - 1) * jb y ^ (-1 : ℝ)) by
        ring, e3]
    rw [hA, hB]
    have h1 : 8 ^ (γ + 2) * J * (∫ z, ‖H z‖) ≤ 8 ^ (γ + 2) * J * (Cd * Z) :=
      mul_le_mul_of_nonneg_left hHL1' (by positivity)
    have h3 : 0 ≤ Z * J * I := by positivity
    have h4 : 0 ≤ Z * J := by positivity
    calc c * (8 ^ (γ + 2) * J * (∫ z, ‖H z‖) + Z * 2 ^ (γ + 2) * J * I + 64 * Z * J * I +
          8 * Z * J * I)
        ≤ c * (8 ^ (γ + 2) * J * (Cd * Z) + Z * 2 ^ (γ + 2) * J * I + 64 * Z * J * I +
          8 * Z * J * I) := by gcongr
      _ ≤ c * (Z * J * (8 ^ (γ + 2) * Cd + 2 ^ (γ + 2) * I + 72 * I + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          nlinarith
      _ = C₁ * (8 ^ (γ + 2) * Cd + 2 ^ (γ + 2) * I + 72 * I + 1) * C₂ ^ k * Z * J := by
          simp only [c]; ring

/-- `X_γ` norm (any normed target) from pointwise weighted bounds on both half-lines. -/
theorem c08_aux_X_norm_le_of_forall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p γ K : ℝ} {r : ℝ → E}
    (h1 : ∀ y, 0 ≤ y → jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv r) y‖) ≤ K)
    (h2 : ∀ y, y ≤ 0 → jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖) ≤ K) :
    X_gamma_norm p γ r ≤ ENNReal.ofReal K + ENNReal.ofReal K := by
  unfold X_gamma_norm
  refine add_le_add (essSup_le_of_ae_le _ ?_) (essSup_le_of_ae_le _ ?_)
  · exact (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun y hy =>
      ENNReal.ofReal_le_ofReal (h1 y hy))
  · exact (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun y hy =>
      ENNReal.ofReal_le_ofReal (h2 y hy))

/-- Blueprint: lem:c08_Mk_bound.  For `1 < γ < p + 2`: `ℳ_k H ∈ C²` and
`‖ℳ_k H‖_{X_γ^ℂ} ≤ C C₂^k ‖H‖_{Z_γ}`.
Encoding: `C₂` is the constant of lem:c08_Hk_kernel; here it is
existentially quantified (only the geometric growth in `k` matters). -/
theorem c08_Mk_bound (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ) (hγ' : γ < p + 2) :
    ∃ C C₂ : ℝ, 0 < C ∧ 0 < C₂ ∧ ∀ (k : ℕ), ∀ H ∈ c08_Z_gamma γ,
      ContDiff ℝ 2 (c08_low_operators_M p k H) ∧
      c08_low_operators_M p k H ∈ X_gammaC p γ ∧
      xNorm p γ (c08_low_operators_M p k H) ≤ C * C₂ ^ k * (c08_Z_gamma_norm γ H).toReal := by
  have hp0 : 0 < p := by linarith
  obtain ⟨_, _, hMd⟩ := c08_Mk_differentiation p γ hp hp1 hγ
  obtain ⟨C, Q, hC, hQ, hG⟩ := c08_Mk_global_decay p γ hp hp1 hγ hγ'
  obtain ⟨C', Q', hC', hQ', hN⟩ := c08_Mk_negative_gain p γ hp hp1 hγ hγ'
  set Qm := max Q Q'
  refine ⟨26 * (C + C'), Qm, by positivity, lt_max_of_lt_left hQ, fun k H hH => ?_⟩
  obtain ⟨hC2, -, -, -⟩ := hMd k H hH
  set M := c08_low_operators_M p k H
  set Z := (c08_Z_gamma_norm γ H).toReal
  have hZ : 0 ≤ Z := ENNReal.toReal_nonneg
  have hQk : Q ^ k ≤ Qm ^ k := pow_le_pow_left₀ hQ.le (le_max_left _ _) k
  have hQk' : Q' ^ k ≤ Qm ^ k := pow_le_pow_left₀ hQ'.le (le_max_right _ _) k
  set K := 13 * (C + C') * Qm ^ k * Z
  have hd1 : ∀ y, deriv M y = iteratedDeriv 1 M y := fun y => by rw [iteratedDeriv_one]
  have hd2 : ∀ y, deriv (deriv M) y = iteratedDeriv 2 M y := fun y => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hG' : ∀ j : ℕ, j ≤ 2 → ∀ y, jb y ^ γ * ‖iteratedDeriv j M y‖ ≤ C * Qm ^ k * Z := by
    intro j hj y
    have h := hG k H hH j hj y
    have hj0 := c08_aux_jb_pos y
    have e : jb y ^ γ * jb y ^ (-γ) = 1 := by
      rw [← Real.rpow_add hj0]; simp
    calc jb y ^ γ * ‖iteratedDeriv j M y‖ ≤ jb y ^ γ * (C * Q ^ k * Z * jb y ^ (-γ)) :=
          mul_le_mul_of_nonneg_left h (Real.rpow_pos_of_pos hj0 _).le
      _ = C * Q ^ k * Z := by rw [show jb y ^ γ * (C * Q ^ k * Z * jb y ^ (-γ)) =
            C * Q ^ k * Z * (jb y ^ γ * jb y ^ (-γ)) by ring, e, mul_one]
      _ ≤ C * Qm ^ k * Z := by gcongr
  have hN' : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ y, y ≤ -2 →
      jb y ^ γ * (jb y ^ j * ‖iteratedDeriv j M y‖) ≤ C' * Qm ^ k * Z := by
    intro j hj1 hj2 y hy
    have h := hN k H hH j hj1 hj2 y hy
    have hj0 := c08_aux_jb_pos y
    have e : jb y ^ γ * (jb y ^ j * jb y ^ (-γ - (j : ℝ))) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hj0, ← Real.rpow_add hj0]; ring_nf; simp
    calc jb y ^ γ * (jb y ^ j * ‖iteratedDeriv j M y‖)
        ≤ jb y ^ γ * (jb y ^ j * (C' * Q' ^ k * Z * jb y ^ (-γ - (j : ℝ)))) := by
          gcongr
      _ = C' * Q' ^ k * Z * (jb y ^ γ * (jb y ^ j * jb y ^ (-γ - (j : ℝ)))) := by ring
      _ = C' * Q' ^ k * Z := by rw [e, mul_one]
      _ ≤ C' * Qm ^ k * Z := by gcongr
  have hCQ : 0 ≤ C * Qm ^ k * Z := by positivity
  have hCQ' : 0 ≤ C' * Qm ^ k * Z := by positivity
  have hb1 : ∀ y, 0 ≤ y → jb y ^ γ * (‖M y‖ + jb y ^ (-1 / p) * ‖deriv M y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv M) y‖) ≤ K := by
    intro y _
    have hj1 := c08_aux_one_le_jb y
    have w1 : jb y ^ (-1 / p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hj1
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le)
    have w2 : jb y ^ (-2 / p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hj1
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp0.le)
    have a0 := hG' 0 (by norm_num) y; have a1 := hG' 1 (by norm_num) y
    have a2 := hG' 2 (by norm_num) y
    simp only [iteratedDeriv_zero] at a0
    rw [hd1, hd2]
    have g0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
    have n1 := norm_nonneg (iteratedDeriv 1 M y); have n2 := norm_nonneg (iteratedDeriv 2 M y)
    have e1 : jb y ^ γ * (jb y ^ (-1 / p) * ‖iteratedDeriv 1 M y‖) ≤ jb y ^ γ * ‖iteratedDeriv 1 M y‖ := by
      apply mul_le_mul_of_nonneg_left _ g0; nlinarith
    have e2 : jb y ^ γ * (jb y ^ (-2 / p) * ‖iteratedDeriv 2 M y‖) ≤ jb y ^ γ * ‖iteratedDeriv 2 M y‖ := by
      apply mul_le_mul_of_nonneg_left _ g0; nlinarith
    have : K = 13 * (C * Qm ^ k * Z) + 13 * (C' * Qm ^ k * Z) := by simp only [K]; ring
    rw [this, mul_add, mul_add]
    linarith
  have hb2 : ∀ y, y ≤ 0 → jb y ^ γ * (‖M y‖ + jb y * ‖deriv M y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv M) y‖) ≤ K := by
    intro y hy
    have a0 := hG' 0 (by norm_num) y; have a1 := hG' 1 (by norm_num) y
    have a2 := hG' 2 (by norm_num) y
    simp only [iteratedDeriv_zero] at a0
    rw [hd1, hd2]
    have g0 : 0 ≤ jb y ^ γ := (Real.rpow_pos_of_pos (c08_aux_jb_pos y) _).le
    have hKe : K = 13 * (C * Qm ^ k * Z) + 13 * (C' * Qm ^ k * Z) := by simp only [K]; ring
    rcases le_or_gt y (-2) with hy2 | hy2
    · have b1 := hN' 1 le_rfl (by norm_num) y hy2
      have b2 := hN' 2 (by norm_num) le_rfl y hy2
      simp only [pow_one] at b1
      rw [hKe, mul_add, mul_add]
      linarith
    · have hjb : jb y ≤ 3 := by
        unfold jb
        rw [Real.sqrt_le_left (by norm_num)]
        nlinarith
      have hj0 := c08_aux_jb_pos y
      have n1 := norm_nonneg (iteratedDeriv 1 M y); have n2 := norm_nonneg (iteratedDeriv 2 M y)
      have e1 : jb y ^ γ * (jb y * ‖iteratedDeriv 1 M y‖) ≤ 3 * (jb y ^ γ * ‖iteratedDeriv 1 M y‖) := by
        have : jb y * ‖iteratedDeriv 1 M y‖ ≤ 3 * ‖iteratedDeriv 1 M y‖ :=
          mul_le_mul_of_nonneg_right hjb n1
        nlinarith
      have e2 : jb y ^ γ * (jb y ^ (2 : ℕ) * ‖iteratedDeriv 2 M y‖) ≤
          9 * (jb y ^ γ * ‖iteratedDeriv 2 M y‖) := by
        have h9 : jb y ^ (2 : ℕ) ≤ 9 := by nlinarith
        have : jb y ^ (2 : ℕ) * ‖iteratedDeriv 2 M y‖ ≤ 9 * ‖iteratedDeriv 2 M y‖ :=
          mul_le_mul_of_nonneg_right h9 n2
        nlinarith
      rw [hKe, mul_add, mul_add]
      nlinarith
  have hX := c08_aux_X_norm_le_of_forall (p := p) hb1 hb2
  have hfin : X_gamma_norm p γ M < ⊤ :=
    lt_of_le_of_lt hX (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  refine ⟨hC2, ⟨⟨hC2.of_le (by norm_num), ?_⟩, hfin⟩, ?_⟩
  · have h1 : ContDiff ℝ 1 (deriv M) := (show ContDiff ℝ (1 + 1) M from hC2).deriv'
    exact h1.locallyLipschitz
  · have hK0 : 0 ≤ K := by positivity
    unfold xNorm
    calc (X_gamma_norm p γ M).toReal ≤ (ENNReal.ofReal K + ENNReal.ofReal K).toReal :=
          ENNReal.toReal_mono (by finiteness) hX
      _ = 2 * K := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hK0]; ring
      _ = 26 * (C + C') * Qm ^ k * Z := by simp only [K]; ring

/-- The pointwise integrand of the `X_γ` norm (positive branch for `x ≥ 0`). -/
def c08_aux_W (p γ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  if 0 ≤ x then jb x ^ γ * (‖f x‖ + jb x ^ (-1 / p) * ‖deriv f x‖ +
      jb x ^ (-2 / p) * ‖deriv (deriv f) x‖)
  else jb x ^ γ * (‖f x‖ + jb x * ‖deriv f x‖ + jb x ^ (2 : ℕ) * ‖deriv (deriv f) x‖)

theorem c08_aux_W_le_xNorm {p γ : ℝ} {f : ℝ → ℂ} (hfin : X_gamma_norm p γ f < ⊤) :
    ∀ᵐ x ∂(volume : Measure ℝ), c08_aux_W p γ f x ≤ xNorm p γ f := by
  unfold X_gamma_norm at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_lt_top.1 hfin
  have hx : xNorm p γ f = _ := ENNReal.toReal_add h1.ne h2.ne
  have a1 := (ae_restrict_iff' measurableSet_Ici).1 (c08_aux_ae_le_essSup_toReal h1)
  have a2 := (ae_restrict_iff' measurableSet_Iic).1 (c08_aux_ae_le_essSup_toReal h2)
  filter_upwards [a1, a2] with x hx1 hx2
  rw [hx]
  unfold c08_aux_W
  split_ifs with h
  · have := hx1 h; linarith [ENNReal.toReal_nonneg (a := essSup (fun y => ENNReal.ofReal (jb y ^ γ *
      (‖f y‖ + jb y * ‖deriv f y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv f) y‖))) (volume.restrict (Iic 0)))]
  · have := hx2 (le_of_lt (not_le.1 h)); linarith [ENNReal.toReal_nonneg (a := essSup (fun y =>
      ENNReal.ofReal (jb y ^ γ * (‖f y‖ + jb y ^ (-1 / p) * ‖deriv f y‖ +
        jb y ^ (-2 / p) * ‖deriv (deriv f) y‖))) (volume.restrict (Ici 0)))]

theorem c08_aux_X_norm_le_of_W {p γ K : ℝ} {f : ℝ → ℂ}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), c08_aux_W p γ f x ≤ K) :
    X_gamma_norm p γ f ≤ ENNReal.ofReal K + ENNReal.ofReal K := by
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  unfold X_gamma_norm
  refine add_le_add (essSup_le_of_ae_le _ ?_) (essSup_le_of_ae_le _ ?_)
  · refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [h] with x hx hx0
    apply ENNReal.ofReal_le_ofReal
    unfold c08_aux_W at hx; simp only [show (0:ℝ) ≤ x from hx0, ite_true] at hx; exact hx
  · refine (ae_restrict_iff' measurableSet_Iic).2 ?_
    filter_upwards [h, h0] with x hx hne hx0
    apply ENNReal.ofReal_le_ofReal
    unfold c08_aux_W at hx
    simp only [show ¬ (0:ℝ) ≤ x from fun h' => hne (le_antisymm (show x ≤ 0 from hx0) h'), ite_false] at hx; exact hx

theorem c08_aux_W_lower {p γ : ℝ} (hp : 0 < p) (hγ : 0 ≤ γ) (f : ℝ → ℂ) (x : ℝ) :
    jb x ^ (-2 / p) * (‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖) ≤ c08_aux_W p γ f x := by
  have hj1 := c08_aux_one_le_jb x
  have hj0 := c08_aux_jb_pos x
  have g1 : 1 ≤ jb x ^ γ := Real.one_le_rpow hj1 hγ
  have w2 : jb x ^ (-2 / p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hj1
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le)
  have w20 : 0 ≤ jb x ^ (-2 / p) := (Real.rpow_pos_of_pos hj0 _).le
  have n0 := norm_nonneg (f x); have n1 := norm_nonneg (deriv f x)
  have n2 := norm_nonneg (deriv (deriv f) x)
  unfold c08_aux_W
  split_ifs with h
  · have w12 : jb x ^ (-2 / p) ≤ jb x ^ (-1 / p) := Real.rpow_le_rpow_of_exponent_le hj1
      (div_le_div_of_nonneg_right (by norm_num) hp.le)
    have : jb x ^ (-2 / p) * (‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖) ≤
        ‖f x‖ + jb x ^ (-1 / p) * ‖deriv f x‖ + jb x ^ (-2 / p) * ‖deriv (deriv f) x‖ := by
      nlinarith
    have hA : 0 ≤ ‖f x‖ + jb x ^ (-1 / p) * ‖deriv f x‖ + jb x ^ (-2 / p) * ‖deriv (deriv f) x‖ := by
      have := (Real.rpow_pos_of_pos hj0 (-1 / p)).le; positivity
    nlinarith
  · have hsq : 1 ≤ jb x ^ (2 : ℕ) := one_le_pow₀ hj1
    have : jb x ^ (-2 / p) * (‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖) ≤
        ‖f x‖ + jb x * ‖deriv f x‖ + jb x ^ (2 : ℕ) * ‖deriv (deriv f) x‖ := by
      nlinarith
    have hA : 0 ≤ ‖f x‖ + jb x * ‖deriv f x‖ + jb x ^ (2 : ℕ) * ‖deriv (deriv f) x‖ := by positivity
    nlinarith

/-- From an a.e. `W`-bound to everywhere pointwise bounds for a `C²` function. -/
theorem c08_aux_W_pointwise {p γ K : ℝ} (hp : 0 < p) (hγ : 0 ≤ γ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (h : ∀ᵐ x ∂(volume : Measure ℝ), c08_aux_W p γ f x ≤ K) (x : ℝ) :
    ‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖ ≤ K * jb x ^ (2 / p) := by
  have hc0 : Continuous f := hf.continuous
  have hc1 : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hc2 : Continuous (deriv (deriv f)) :=
    ((show ContDiff ℝ (1 + 1) f from hf).deriv').continuous_deriv le_rfl
  have hjc : Continuous jb := by unfold jb; fun_prop
  have hg : Continuous (fun x => K * jb x ^ (2 / p)) :=
    continuous_const.mul (hjc.rpow_const fun x => Or.inl (c08_aux_jb_pos x).ne')
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖ ≤ K * jb x ^ (2 / p) := by
    filter_upwards [h] with x hx
    have hl := (c08_aux_W_lower hp hγ f x).trans hx
    have hj0 := c08_aux_jb_pos x
    have e : jb x ^ (2 / p) * jb x ^ (-2 / p) = 1 := by
      rw [← Real.rpow_add hj0]; ring_nf; simp
    have hp2 : 0 < jb x ^ (2 / p) := Real.rpow_pos_of_pos hj0 _
    calc ‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖
        = jb x ^ (2 / p) * (jb x ^ (-2 / p) * (‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖)) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ jb x ^ (2 / p) * K := mul_le_mul_of_nonneg_left hl hp2.le
      _ = K * jb x ^ (2 / p) := mul_comm _ _
  exact c08_aux_le_of_ae_halflines (f := fun x => ‖f x‖ + ‖deriv f x‖ + ‖deriv (deriv f) x‖)
    ((hc0.norm.add hc1.norm).add hc2.norm) hg (ae_restrict_of_ae hae) (ae_restrict_of_ae hae) x

theorem c08_aux_W_const_mul (p γ : ℝ) (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    c08_aux_W p γ (fun y => c * f y) x = ‖c‖ * c08_aux_W p γ f x := by
  have d1 : deriv (fun y => c * f y) = fun y => c * deriv f y := deriv_const_mul_field' c
  have d2 : deriv (fun y => c * deriv f y) = fun y => c * deriv (deriv f) y :=
    deriv_const_mul_field' c
  unfold c08_aux_W
  rw [d1, d2]
  simp only [norm_mul]
  split_ifs <;> ring

theorem c08_aux_W_neg (p γ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    c08_aux_W p γ (-f) x = c08_aux_W p γ f x := by
  have d1 : deriv (-f) = -deriv f := by
    funext y; show deriv (fun y => -f y) y = -deriv f y; exact deriv.neg
  have d2 : deriv (-deriv f) = -deriv (deriv f) := by
    funext y; show deriv (fun y => -deriv f y) y = -deriv (deriv f) y; exact deriv.neg
  unfold c08_aux_W
  rw [d1, d2]
  simp only [Pi.neg_apply, norm_neg]

/-- A series of `C²` functions with summable `X_γ`-type bounds: the sum is `C²`, differentiated
termwise, and obeys the summed `W`-bound a.e. -/
theorem c08_aux_series_X {p γ : ℝ} (hp : 0 < p) (hγ : 0 ≤ γ) (T : ℕ → ℝ → ℂ)
    (hT : ∀ k, ContDiff ℝ 2 (T k)) (b : ℕ → ℝ) (hb : Summable b)
    (hW : ∀ k, ∀ᵐ x ∂(volume : Measure ℝ), c08_aux_W p γ (T k) x ≤ b k) :
    ContDiff ℝ 2 (fun y => ∑' k, T k y) ∧
    (∀ y, deriv (fun y => ∑' k, T k y) y = ∑' k, deriv (T k) y) ∧
    (∀ y, deriv (deriv (fun y => ∑' k, T k y)) y = ∑' k, deriv (deriv (T k)) y) ∧
    ∀ᵐ x ∂(volume : Measure ℝ), c08_aux_W p γ (fun y => ∑' k, T k y) x ≤ ∑' k, b k := by
  have hpt : ∀ k x, ‖T k x‖ + ‖deriv (T k) x‖ + ‖deriv (deriv (T k)) x‖ ≤ b k * jb x ^ (2 / p) :=
    fun k x => c08_aux_W_pointwise hp hγ (hT k) (hW k) x
  have hb0 : ∀ k, 0 ≤ b k := by
    intro k
    have h := hpt k 0
    have : jb 0 ^ (2 / p) = 1 := by simp [jb]
    rw [this, mul_one] at h
    linarith [norm_nonneg (T k 0), norm_nonneg (deriv (T k) 0), norm_nonneg (deriv (deriv (T k)) 0)]
  have b0 : ∀ k x, ‖T k x‖ ≤ b k * jb x ^ (2 / p) := fun k x => by
    have := hpt k x; linarith [norm_nonneg (deriv (T k) x), norm_nonneg (deriv (deriv (T k)) x)]
  have b1 : ∀ k x, ‖deriv (T k) x‖ ≤ b k * jb x ^ (2 / p) := fun k x => by
    have := hpt k x; linarith [norm_nonneg (T k x), norm_nonneg (deriv (deriv (T k)) x)]
  have b2 : ∀ k x, ‖deriv (deriv (T k)) x‖ ≤ b k * jb x ^ (2 / p) := fun k x => by
    have := hpt k x; linarith [norm_nonneg (deriv (T k) x), norm_nonneg (T k x)]
  -- local uniform bounds on balls
  have hloc : ∀ (R : ℝ) (x : ℝ), x ∈ Metric.ball (0:ℝ) R → jb x ^ (2 / p) ≤ jb R ^ (2 / p) := by
    intro R x hx
    have : |x| ≤ R := by
      have := Metric.mem_ball.1 hx; rw [dist_zero_right, Real.norm_eq_abs] at this; linarith
    exact Real.rpow_le_rpow (c08_aux_jb_pos x).le (c08_aux_jb_mono (this.trans (le_abs_self R))) (by positivity)
  have hd0 : ∀ k, Differentiable ℝ (T k) := fun k => (hT k).differentiable (by norm_num)
  have hd1 : ∀ k, Differentiable ℝ (deriv (T k)) := fun k =>
    ((show ContDiff ℝ (1 + 1) (T k) from hT k).deriv').differentiable one_ne_zero
  have hc2 : ∀ k, Continuous (deriv (deriv (T k))) := fun k =>
    ((show ContDiff ℝ (1 + 1) (T k) from hT k).deriv').continuous_deriv le_rfl
  have hsum : ∀ (g : ℕ → ℝ → ℂ), (∀ k x, ‖g k x‖ ≤ b k * jb x ^ (2 / p)) → ∀ x,
      Summable (fun k => g k x) := fun g hg x =>
    Summable.of_norm_bounded (hb.mul_right _) (fun k => hg k x)
  have hder : ∀ (g : ℕ → ℝ → ℂ), (∀ k, Differentiable ℝ (g k)) →
      (∀ k x, ‖g k x‖ ≤ b k * jb x ^ (2 / p)) → (∀ k x, ‖deriv (g k) x‖ ≤ b k * jb x ^ (2 / p)) →
      ∀ y, HasDerivAt (fun z => ∑' k, g k z) (∑' k, deriv (g k) y) y := by
    intro g hgd hg0 hg1 y
    set R := |y| + 1
    exact hasDerivAt_tsum_of_isPreconnected (u := fun k => b k * jb R ^ (2 / p))
      (hb.mul_right _) Metric.isOpen_ball (convex_ball (0:ℝ) R).isPreconnected
      (fun k z _ => (hgd k z).hasDerivAt)
      (fun k z hz => (hg1 k z).trans (mul_le_mul_of_nonneg_left (hloc R z hz) (hb0 k)))
      (show y ∈ Metric.ball (0:ℝ) R by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith)
      (hsum g hg0 y)
      (show y ∈ Metric.ball (0:ℝ) R by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith)
  have D1 := hder T hd0 b0 b1
  have D2 := hder (fun k => deriv (T k)) hd1 b1 b2
  have e1 : deriv (fun y => ∑' k, T k y) = fun y => ∑' k, deriv (T k) y :=
    funext fun y => (D1 y).deriv
  have e2 : deriv (fun y => ∑' k, deriv (T k) y) = fun y => ∑' k, deriv (deriv (T k)) y :=
    funext fun y => (D2 y).deriv
  have hcont2 : Continuous (fun y => ∑' k, deriv (deriv (T k)) y) := by
    rw [continuous_iff_continuousAt]
    intro y
    set R := |y| + 1
    have hon := continuousOn_tsum (s := Metric.ball (0:ℝ) R) (u := fun k => b k * jb R ^ (2 / p))
      (fun k => (hc2 k).continuousOn) (hb.mul_right _)
      (fun k z hz => (b2 k z).trans (mul_le_mul_of_nonneg_left (hloc R z hz) (hb0 k)))
    exact hon.continuousAt (Metric.isOpen_ball.mem_nhds (by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith))
  refine ⟨?_, fun y => by rw [e1], fun y => by rw [e1, e2], ?_⟩
  · have h1 : ContDiff ℝ 1 (fun y => ∑' k, deriv (T k) y) :=
      contDiff_one_iff_deriv.2 ⟨fun y => (D2 y).differentiableAt, by rw [e2]; exact hcont2⟩
    exact (contDiff_succ_iff_deriv (n := 1)).2 ⟨fun y => (D1 y).differentiableAt, by simp,
      by rw [e1]; exact h1⟩
  · rw [← ae_all_iff] at hW
    filter_upwards [hW] with x hx
    have hsn : ∀ (g : ℕ → ℝ → ℂ), (∀ k x, ‖g k x‖ ≤ b k * jb x ^ (2 / p)) →
        Summable (fun k => ‖g k x‖) := fun g hg =>
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hg k x) (hb.mul_right _)
    have n0 : ‖∑' k, T k x‖ ≤ ∑' k, ‖T k x‖ := norm_tsum_le_tsum_norm (hsn T b0)
    have n1 : ‖∑' k, deriv (T k) x‖ ≤ ∑' k, ‖deriv (T k) x‖ :=
      norm_tsum_le_tsum_norm (hsn _ b1)
    have n2 : ‖∑' k, deriv (deriv (T k)) x‖ ≤ ∑' k, ‖deriv (deriv (T k)) x‖ :=
      norm_tsum_le_tsum_norm (hsn _ b2)
    have hWs : Summable (fun k => c08_aux_W p γ (T k) x) := by
      refine Summable.of_nonneg_of_le (fun k => ?_) hx hb
      exact (mul_nonneg (Real.rpow_pos_of_pos (c08_aux_jb_pos x) _).le (by positivity)).trans
        (c08_aux_W_lower hp hγ (T k) x)
    have key : c08_aux_W p γ (fun y => ∑' k, T k y) x ≤ ∑' k, c08_aux_W p γ (T k) x := by
      unfold c08_aux_W
      rw [e1, e2]
      have hg : 0 ≤ jb x ^ γ := (Real.rpow_pos_of_pos (c08_aux_jb_pos x) _).le
      have tri : ∀ w1 w2 : ℝ, 0 ≤ w1 → 0 ≤ w2 →
          jb x ^ γ * (‖∑' k, T k x‖ + w1 * ‖∑' k, deriv (T k) x‖ +
            w2 * ‖∑' k, deriv (deriv (T k)) x‖) ≤
          ∑' k, jb x ^ γ * (‖T k x‖ + w1 * ‖deriv (T k) x‖ + w2 * ‖deriv (deriv (T k)) x‖) := by
        intro w1 w2 hw1 hw2
        rw [tsum_mul_left, Summable.tsum_add ((hsn T b0).add ((hsn _ b1).mul_left _)) ((hsn _ b2).mul_left _),
          Summable.tsum_add (hsn T b0) ((hsn _ b1).mul_left _), tsum_mul_left, tsum_mul_left]
        apply mul_le_mul_of_nonneg_left _ hg
        have := mul_le_mul_of_nonneg_left n1 hw1
        have := mul_le_mul_of_nonneg_left n2 hw2
        linarith
      split_ifs with h
      · exact tri _ _ (Real.rpow_pos_of_pos (c08_aux_jb_pos x) _).le
          (Real.rpow_pos_of_pos (c08_aux_jb_pos x) _).le
      · exact tri _ _ (c08_aux_jb_pos x).le (by have := c08_aux_jb_pos x; positivity)
    exact key.trans (Summable.tsum_le_tsum hx hWs hb)


/-- The inverse transform of a continuous function supported in `[-2,2]` is `C^∞`. -/
theorem c08_aux_invFourierT_smooth {m : ℝ → ℂ} (hm : Continuous m)
    (hsupp : ∀ ξ, 2 < |ξ| → m ξ = 0) : ContDiff ℝ (⊤ : ℕ∞) (invFourierT m) := by
  set g : ℝ → ℂ := fun v => m (2 * π * v) with hg
  have he : invFourierT m = fun x => 𝓕 g (-x) := by
    funext x; rw [c08_aux_invFourierT_eq, Real.fourierInv_eq_fourier_neg]
  have hgc : Continuous g := hm.comp (continuous_const.mul continuous_id)
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro (K := Icc (-1) 1) isCompact_Icc (fun v hv => ?_)
    apply hsupp
    have h1 : 1 < |v| := by
      by_contra h; push Not at h; exact hv (abs_le.1 h)
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    have := Real.pi_gt_three
    nlinarith
  have hF : ContDiff ℝ (⊤ : ℕ∞) (𝓕 g) := by
    apply Real.contDiff_fourier
    intro n _
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_norm.pow n).mul hgc.norm
    · exact hgs.norm.mul_left
  rw [he]
  exact hF.comp contDiff_neg

/-- Blueprint: prop:linear_low_frequency.  For `1 < γ < p + 2` and `G ∈ Y_γ`, `𝒯_l G` is a real
`C^∞` function in `X_γ` with `‖𝒯_l G‖_{X_γ} ≤ C_l ‖G‖_{Y_γ}` (no condition `ℓ(G) = 0`).  We also
record `(𝒯_l G)^ = χ m_G` in `𝒮'` (its defining property in def:c08_frequency_split; `GSQG/Definitions`
realises `𝒯_l G` as the real part of `(χ m_G)^∨`). -/
theorem linear_low_frequency (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (hγ' : γ < p + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ G ∈ Y_gamma p γ,
      ContDiff ℝ (⊤ : ℕ∞) (T_low p G) ∧ T_low p G ∈ X_gamma p γ ∧
      xNorm p γ (T_low p G) ≤ C * yNorm p γ G ∧
      HasDistFourier (fun y => (T_low p G y : ℂ)) (fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ) := by
  have hp0 : 0 < p := by linarith
  have hγ0 : 0 ≤ γ := by linarith
  obtain ⟨CA, hCA, hAk⟩ := c08_Ak_bound p γ hp hp1 hγ
  obtain ⟨CM, C2, hCM, hC2, hMk⟩ := c08_Mk_bound p γ hp hp1 hγ hγ'
  set E := ∑' k : ℕ, C2 ^ k / (k.factorial : ℝ) with hE
  have hEs := Real.summable_pow_div_factorial C2
  have hE0 : 0 ≤ E := tsum_nonneg fun k => by positivity
  refine ⟨2 * (CM * CA) * E + 1, by positivity, fun G hG => ?_⟩
  set N := yNorm p γ G with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  set H : ℕ → ℝ → ℂ := fun k y => (c08_low_operators p k G y : ℂ) with hHdef
  set T : ℕ → ℝ → ℂ := fun k y => (-Complex.I) ^ k / (k.factorial : ℂ) *
    c08_low_operators_M p k (H k) y with hTdef
  set b : ℕ → ℝ := fun k => (CM * CA * N) * (C2 ^ k / (k.factorial : ℝ)) with hbdef
  have hb : Summable b := hEs.mul_left _
  have hb0 : ∀ k, 0 ≤ b k := fun k => by simp only [hbdef]; positivity
  have hT2 : ∀ k, ContDiff ℝ 2 (T k) := fun k =>
    contDiff_const.mul ((hMk k (H k) (hAk k G hG).1).1)
  have hck : ∀ k : ℕ, ‖(-Complex.I) ^ k / (k.factorial : ℂ)‖ = 1 / (k.factorial : ℝ) := by
    intro k; rw [norm_div, norm_pow, norm_neg, Complex.norm_I, one_pow]; norm_cast
  have hW : ∀ k, ∀ᵐ x ∂(volume : Measure ℝ), c08_aux_W p γ (T k) x ≤ b k := by
    intro k
    obtain ⟨-, hMX, hMb⟩ := hMk k (H k) (hAk k G hG).1
    have hZ := (hAk k G hG).2
    filter_upwards [c08_aux_W_le_xNorm hMX.2] with x hx
    simp only [hTdef]
    rw [c08_aux_W_const_mul, hck]
    have hZ0 : 0 ≤ (c08_Z_gamma_norm γ (H k)).toReal := ENNReal.toReal_nonneg
    have h1 : xNorm p γ (c08_low_operators_M p k (H k)) ≤ CM * C2 ^ k * (CA * N) :=
      hMb.trans (mul_le_mul_of_nonneg_left hZ (by positivity))
    have hf : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    calc 1 / (k.factorial : ℝ) * c08_aux_W p γ (c08_low_operators_M p k (H k)) x
        ≤ 1 / (k.factorial : ℝ) * (CM * C2 ^ k * (CA * N)) :=
          mul_le_mul_of_nonneg_left (hx.trans h1) (by positivity)
      _ = b k := by simp only [hbdef]; ring
  obtain ⟨hS2, -, -, hSW⟩ := c08_aux_series_X hp0 hγ0 T hT2 b hb hW
  set S : ℝ → ℂ := fun y => ∑' k, T k y with hSdef
  have hSfin : X_gamma_norm p γ S < ⊤ :=
    lt_of_le_of_lt (c08_aux_X_norm_le_of_W hSW)
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  have hW2 : ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f → W2inftyLoc f := fun {f} hf =>
    ⟨hf.of_le (by norm_num), ((show ContDiff ℝ (1 + 1) f from hf).deriv').locallyLipschitz⟩
  have hSX : S ∈ X_gammaC p γ := ⟨hW2 hS2, hSfin⟩
  -- partial sums
  have hSn : ∀ n : ℕ, (fun y => ∑ k ∈ Finset.range n, (-Complex.I) ^ k / (k.factorial : ℂ) *
      c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) ∈ X_gammaC p γ := by
    intro n
    set T' : ℕ → ℝ → ℂ := fun k y => (if k < n then (1:ℂ) else 0) * T k y with hT'
    have hT'2 : ∀ k, ContDiff ℝ 2 (T' k) := fun k => contDiff_const.mul (hT2 k)
    have hW' : ∀ k, ∀ᵐ x ∂(volume : Measure ℝ), c08_aux_W p γ (T' k) x ≤ b k := by
      intro k
      filter_upwards [hW k] with x hx
      simp only [hT']
      rw [c08_aux_W_const_mul]
      have hW0 : 0 ≤ c08_aux_W p γ (T k) x :=
        (mul_nonneg (Real.rpow_pos_of_pos (c08_aux_jb_pos x) _).le (by positivity)).trans
          (c08_aux_W_lower hp0 hγ0 (T k) x)
      split_ifs <;> simp <;> linarith [hb0 k]
    obtain ⟨h2, -, -, hW'' ⟩ := c08_aux_series_X hp0 hγ0 T' hT'2 b hb hW'
    have heq : (fun y => ∑' k, T' k y) = (fun y => ∑ k ∈ Finset.range n, (-Complex.I) ^ k /
        (k.factorial : ℂ) * c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) := by
      funext y
      rw [tsum_eq_sum (s := Finset.range n)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [hT', hTdef, hHdef, if_pos (Finset.mem_range.1 hk), one_mul]
      · intro k hk
        simp only [hT', if_neg (fun h => hk (Finset.mem_range.2 h)), zero_mul]
    rw [← heq]
    exact ⟨hW2 h2, lt_of_le_of_lt (c08_aux_X_norm_le_of_W hW'')
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)⟩
  -- tails
  have hlim : Tendsto (fun n : ℕ => xNorm p γ ((fun y => ∑ k ∈ Finset.range n,
      (-Complex.I) ^ k / (k.factorial : ℂ) *
        c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) - S))
      atTop (nhds 0) := by
    have htail : Tendsto (fun n : ℕ => 2 * ∑' k, b (k + n)) atTop (nhds 0) := by
      simpa using (_root_.tendsto_sum_nat_add b).const_mul 2
    refine squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => ?_) htail
    obtain ⟨-, -, -, hWR⟩ := c08_aux_series_X hp0 hγ0 (fun k => T (k + n)) (fun k => hT2 _)
      (fun k => b (k + n)) ((summable_nat_add_iff n).2 hb) (fun k => hW (k + n))
    have heq : ((fun y => ∑ k ∈ Finset.range n, (-Complex.I) ^ k / (k.factorial : ℂ) *
        c08_low_operators_M p k (fun x => (c08_low_operators p k G x : ℂ)) y) - S) =
        -(fun y => ∑' k, T (k + n) y) := by
      funext y
      have hsy : Summable (fun k => T k y) := by
        have := c08_aux_W_pointwise hp0 hγ0 (hT2 0) (hW 0) y
        refine Summable.of_norm_bounded (hb.mul_right (jb y ^ (2 / p))) (fun k => ?_)
        have := c08_aux_W_pointwise hp0 hγ0 (hT2 k) (hW k) y
        linarith [norm_nonneg (deriv (T k) y), norm_nonneg (deriv (deriv (T k)) y)]
      have := hsy.sum_add_tsum_nat_add n
      simp only [Pi.sub_apply, Pi.neg_apply, hSdef]
      rw [← this]
      simp only [hTdef, hHdef]
      ring
    rw [heq]
    have hb2 : 0 ≤ ∑' k, b (k + n) := tsum_nonneg fun k => hb0 _
    have hX := c08_aux_X_norm_le_of_W (p := p) (γ := γ) (f := -(fun y => ∑' k, T (k + n) y))
      (by filter_upwards [hWR] with x hx; rw [c08_aux_W_neg]; exact hx)
    unfold xNorm
    calc (X_gamma_norm p γ (-(fun y => ∑' k, T (k + n) y))).toReal
        ≤ (ENNReal.ofReal (∑' k, b (k + n)) + ENNReal.ofReal (∑' k, b (k + n))).toReal :=
          ENNReal.toReal_mono (by finiteness) hX
      _ = 2 * ∑' k, b (k + n) := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hb2]; ring
  obtain ⟨hFS, hTS⟩ := c08_low_series_identification p γ hp hp1 hγ G hG S hSX hSn hlim
  have hTSf : (fun y => (T_low p G y : ℂ)) = S := funext hTS
  -- regularity of T_low
  obtain ⟨⟨-, hmc, -, -⟩, -⟩ := c08_free_ode p γ hp hp1 hγ G hG
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (T_low p G) := by
    have h := c08_aux_invFourierT_smooth (m := fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ)
      ((Complex.continuous_ofReal.comp c08_aux_rho_contDiff.continuous).mul hmc)
      (fun ξ hξ => by simp [c08_aux_rho_props.1 ξ hξ])
    exact Complex.reCLM.contDiff.comp h
  have hT2' : ContDiff ℝ 2 (T_low p G) := hsmooth.of_le (by norm_cast)
  have hXeq : X_gamma_norm p γ (T_low p G) = X_gamma_norm p γ S := by
    rw [← hTSf]
    unfold X_gamma_norm
    have d1 := c08_aux_deriv_ofReal (T_low p G)
    have d2 := c08_aux_deriv_ofReal (deriv (T_low p G))
    rw [d1, d2]
    simp only [Complex.norm_real]
  have hSb : xNorm p γ S ≤ 2 * ∑' k, b k := by
    have hX := c08_aux_X_norm_le_of_W hSW
    have hb2 : 0 ≤ ∑' k, b k := tsum_nonneg hb0
    unfold xNorm
    calc (X_gamma_norm p γ S).toReal
        ≤ (ENNReal.ofReal (∑' k, b k) + ENNReal.ofReal (∑' k, b k)).toReal :=
          ENNReal.toReal_mono (by finiteness) hX
      _ = 2 * ∑' k, b k := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hb2]; ring
  have hbsum : ∑' k, b k = CM * CA * N * E := by simp only [hbdef]; rw [tsum_mul_left]
  refine ⟨hsmooth, ⟨⟨hT2'.of_le (by norm_num),
    ((show ContDiff ℝ (1 + 1) (T_low p G) from hT2').deriv').locallyLipschitz⟩, hXeq ▸ hSfin⟩, ?_, ?_⟩
  · unfold xNorm; rw [hXeq]
    calc (X_gamma_norm p γ S).toReal ≤ 2 * ∑' k, b k := hSb
      _ = 2 * (CM * CA) * E * N := by rw [hbsum]; ring
      _ ≤ (2 * (CM * CA) * E + 1) * N := by nlinarith
  · intro ψ
    have hSi := (c08_aux_XC_L1 hγ hS2.continuous hSfin).1
    rw [hTSf, c08_aux_parseval hSi ψ]
    simp_rw [hFS]

/-- Blueprint: lem:c08_frequency_split_sum.  `𝒯₀ G = 𝒯_l G + 𝒯_h G` (in `𝒮'`, hence pointwise for
functions), and if both parts lie in `X_γ` then so does `𝒯₀ G`, with
`‖𝒯₀ G‖_{X_γ} ≤ ‖𝒯_l G‖_{X_γ} + ‖𝒯_h G‖_{X_γ}`. -/
theorem c08_frequency_split_sum (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ)
    (hl : T_low p G ∈ X_gamma p γ) (hh : T_high p G ∈ X_gamma p γ)
    (hhF : HasDistFourier (fun x => (T_high p G x : ℂ))
      (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ)) :
    T_0 p G = T_low p G + T_high p G ∧
    HasDistFourier (fun x => (T_0 p G x : ℂ)) (T_0_symbol p G) ∧
    T_0 p G ∈ X_gamma p γ ∧
    xNorm p γ (T_0 p G) ≤ xNorm p γ (T_low p G) + xNorm p γ (T_high p G) := by
  obtain ⟨_, _, hlow⟩ := linear_low_frequency p (min γ (p + 1)) hp hp1
    (lt_min hγ (by linarith)) (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  obtain ⟨hTsmooth, -, -, hlF⟩ := hlow G (c08_aux_Y_mono (min_le_left _ _) hG)
  obtain ⟨⟨-, hmcont, hmbd, -⟩, -⟩ := c08_free_ode p γ hp hp1 hγ G hG
  set m := T_0_symbol p G
  set S : ℝ → ℝ := T_low p G + T_high p G with hSdef
  obtain ⟨hlc, Cl, Nl, hlpb⟩ := c08_aux_X_polyBounded hl
  obtain ⟨hhc, Ch, Nh, hhpb⟩ := c08_aux_X_polyBounded hh
  have hSc : Continuous S := hlc.add hhc
  have hSpb : IsPolyBounded S := by
    refine ⟨|Cl| + |Ch|, max Nl Nh, fun x => ?_⟩
    have h1 : jb x ^ Nl ≤ jb x ^ max Nl Nh :=
      Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb x) (le_max_left _ _)
    have h2 : jb x ^ Nh ≤ jb x ^ max Nl Nh :=
      Real.rpow_le_rpow_of_exponent_le (c08_aux_one_le_jb x) (le_max_right _ _)
    have h0l : 0 ≤ jb x ^ Nl := Real.rpow_nonneg (c08_aux_jb_pos x).le _
    have h0h : 0 ≤ jb x ^ Nh := Real.rpow_nonneg (c08_aux_jb_pos x).le _
    have a1 := hlpb x; have a2 := hhpb x
    simp only [hSdef, Pi.add_apply]
    calc ‖T_low p G x + T_high p G x‖ ≤ ‖T_low p G x‖ + ‖T_high p G x‖ := norm_add_le _ _
      _ ≤ Cl * jb x ^ Nl + Ch * jb x ^ Nh := add_le_add a1 a2
      _ ≤ |Cl| * jb x ^ max Nl Nh + |Ch| * jb x ^ max Nl Nh := by
        exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self Cl) h0l).trans
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)))
          ((mul_le_mul_of_nonneg_right (le_abs_self Ch) h0h).trans
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
      _ = _ := by ring
  have hpbC : ∀ u : ℝ → ℝ, IsPolyBounded u → IsPolyBounded (fun x => (u x : ℂ)) := by
    rintro u ⟨C, N, hC⟩; exact ⟨C, N, fun x => by simpa using hC x⟩
  have hSF : HasDistFourier (fun x => (S x : ℂ)) m := by
    intro φ
    have i1 : Integrable (fun x => ((T_low p G x : ℝ) : ℂ) * fourierT (⇑φ) x) :=
      c08_aux_polyBounded_mul_fourierT_integrable _
        (Complex.continuous_ofReal.comp hlc) (hpbC _ ⟨Cl, Nl, hlpb⟩) φ
    have i2 : Integrable (fun x => ((T_high p G x : ℝ) : ℂ) * fourierT (⇑φ) x) :=
      c08_aux_polyBounded_mul_fourierT_integrable _
        (Complex.continuous_ofReal.comp hhc) (hpbC _ ⟨Ch, Nh, hhpb⟩) φ
    have hρc : Continuous (fun ξ : ℝ => (rho ξ : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.smoothTransition.continuous.comp (by fun_prop))
    have hρ1 : ∀ ξ, ‖(rho ξ : ℂ)‖ ≤ 1 := fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold rho
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hρ1' : ∀ ξ, ‖(((1 - rho ξ : ℝ)) : ℂ)‖ ≤ 1 := fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := Real.smoothTransition.nonneg (2 - |ξ|)
      have := Real.smoothTransition.le_one (2 - |ξ|)
      unfold rho; rw [abs_le]; constructor <;> linarith
    have hm1 : Integrable (fun ξ => m ξ * φ ξ) :=
      (SchwartzMap.integrable φ).bdd_mul hmcont.aestronglyMeasurable
        (Eventually.of_forall hmbd)
    have j1 : Integrable (fun ξ => (rho ξ : ℂ) * m ξ * φ ξ) := by
      simp_rw [mul_assoc]
      exact hm1.bdd_mul hρc.aestronglyMeasurable (Eventually.of_forall hρ1)
    have j2 : Integrable (fun ξ => (((1 - rho ξ : ℝ)) : ℂ) * m ξ * φ ξ) := by
      simp_rw [mul_assoc]
      exact hm1.bdd_mul (Complex.continuous_ofReal.comp (continuous_const.sub
        (Real.smoothTransition.continuous.comp (by fun_prop)))).aestronglyMeasurable
        (Eventually.of_forall hρ1')
    have e1 : (fun x => ((S x : ℝ) : ℂ) * fourierT (⇑φ) x) = fun x =>
        ((T_low p G x : ℝ) : ℂ) * fourierT (⇑φ) x + ((T_high p G x : ℝ) : ℂ) * fourierT (⇑φ) x := by
      ext x; simp only [hSdef, Pi.add_apply]; push_cast; ring
    rw [e1, integral_add i1 i2, hlF φ, hhF φ, ← integral_add j1 j2]
    exact integral_congr_ae (Eventually.of_forall fun ξ => by simp only; push_cast; ring)
  have hT0 : T_0 p G = S := c08_aux_distFourierInv_eq hSc hSpb hSF
  have hl2 : ContDiff ℝ 2 (T_low p G) := hTsmooth.of_le (by norm_cast)
  have hnorm := c08_aux_X_norm_add_le p γ hl2 hh.1.1
  have hfin : X_gamma_norm p γ (T_low p G) + X_gamma_norm p γ (T_high p G) < ⊤ :=
    ENNReal.add_lt_top.2 ⟨hl.2, hh.2⟩
  have hderiv : deriv S = deriv (T_low p G) + deriv (T_high p G) := by
    ext y
    exact deriv_add (hl.1.1.differentiable (by norm_num) y) (hh.1.1.differentiable (by norm_num) y)
  refine ⟨hT0, hT0 ▸ hSF, ?_, ?_⟩
  · rw [hT0]
    refine ⟨⟨hl.1.1.add hh.1.1, ?_⟩, lt_of_le_of_lt hnorm hfin⟩
    rw [hderiv]; exact hl.1.2.add hh.1.2
  · rw [hT0]
    unfold xNorm
    rw [← ENNReal.toReal_add hl.2.ne hh.2.ne]
    exact ENNReal.toReal_mono hfin.ne hnorm

end GSQG
