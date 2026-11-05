import GSQG.SchauderEstimate.Setup

/-!
# Beyond the paper (Schauder estimate cited in §4): dyadic telescoping, annular kernels, moments
and scaling (blueprint ch. 12). Helpers `c12k_aux_*`.
-/

open MeasureTheory Set Filter Real FourierTransform
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-- Blueprint: lem:c12_dyadic_telescope.  `χ(ξ) + Σ_{j<n} φ(2^{-j}ξ) = χ(2^{-n}ξ)`; the right side is
bounded by one in absolute value, tends to one, and is eventually equal to one. -/
theorem c12_dyadic_telescope :
    (∀ (n : ℕ) (ξ : ℝ),
      rho ξ + ∑ j ∈ Finset.range n, c12_annulus (ξ / (2 : ℝ) ^ j) = rho (ξ / (2 : ℝ) ^ n)) ∧
    (∀ (n : ℕ) (ξ : ℝ), |rho (ξ / (2 : ℝ) ^ n)| ≤ 1) ∧
    (∀ ξ : ℝ, Tendsto (fun n : ℕ => rho (ξ / (2 : ℝ) ^ n)) atTop (𝓝 1)) ∧
    (∀ ξ : ℝ, ∀ᶠ n : ℕ in atTop, rho (ξ / (2 : ℝ) ^ n) = 1) := by
  have hev : ∀ ξ : ℝ, ∀ᶠ n : ℕ in atTop, rho (ξ / (2 : ℝ) ^ n) = 1 := by
    intro ξ
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt |ξ| (by norm_num : (1 : ℝ) < 2)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply c12k_aux_rho_one
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n), div_le_one (by positivity)]
    exact hN.le.trans (pow_le_pow_right₀ (by norm_num) hn)
  refine ⟨fun n ξ => ?_, fun n ξ => ?_, fun ξ => ?_, hev⟩
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      unfold c12_annulus
      rw [div_div, ← pow_succ]
      ring
  · unfold rho
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · exact tendsto_const_nhds.congr' (by filter_upwards [hev ξ] with n hn using hn.symm)

/-! ### Generic Schwartz kernels of smooth compactly supported symbols -/

/-- The rescaled symbol `ξ ↦ G(2πξ)`. -/
theorem c12k_aux_scaled_symbol {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hcs : HasCompactSupport G) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ => G (2 * π * w)) ∧
    HasCompactSupport (fun w : ℝ => G (2 * π * w)) := by
  refine ⟨hG.comp (contDiff_const.mul contDiff_id), ?_⟩
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have := hcs.comp_homeomorph (Homeomorph.mulLeft₀ (2 * π) h2π)
  exact this

/-- Schwartz inverse transform of a smooth compactly supported symbol, in the project convention. -/
theorem c12k_aux_schwartz {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hcs : HasCompactSupport G) :
    ∃ K : SchwartzMap ℝ ℂ, (∀ x, K x = invFourierT G x) ∧
      (∀ w, 𝓕 (⇑K) w = G (2 * π * w)) ∧ (∀ ξ, fourierT (fun x => K x) ξ = G ξ) := by
  obtain ⟨hHs, hHc⟩ := c12k_aux_scaled_symbol hG hcs
  set Hs : SchwartzMap ℝ ℂ := hHc.toSchwartzMap hHs
  have hH : ∀ w, Hs w = G (2 * π * w) := fun w => hHc.toSchwartzMap_toFun hHs w
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  set K : SchwartzMap ℝ ℂ := 𝓕⁻ Hs with hKdef
  have hF : ∀ w, 𝓕 (⇑K) w = G (2 * π * w) := by
    intro w
    rw [← SchwartzMap.fourier_coe, hKdef, fourier_fourierInv_eq, hH]
  refine ⟨K, fun x => ?_, hF, fun ξ => ?_⟩
  · rw [hKdef, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    unfold invFourierT
    have := Measure.integral_comp_mul_left
      (fun ξ : ℝ => G ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) (2 * π)
    rw [abs_inv, abs_of_pos (by positivity), Complex.real_smul, Complex.ofReal_inv] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, RCLike.inner_apply, hH]
    rw [mul_comm]
    congr 2
    push_cast
    simp
    ring
  · show (∫ x, K x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) = G ξ
    rw [Lib.integral_mul_exp_neg_I_eq_fourier, hF]
    congr 1; field_simp

/-- Even real symbols have real inverse transforms. -/
theorem c12k_aux_invF_real {g : ℝ → ℝ} (hev : ∀ ξ, g (-ξ) = g ξ) (x : ℝ) :
    invFourierT (fun ξ => (g ξ : ℂ)) x = ((invFourierT (fun ξ => (g ξ : ℂ)) x).re : ℂ) := by
  symm
  rw [← Complex.conj_eq_iff_re]
  unfold invFourierT
  rw [map_mul, ← integral_conj, map_inv₀, Complex.conj_ofReal]
  congr 1
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  rw [hev]
  push_cast
  ring_nf

/-- Iterated derivatives commute with the real part. -/
theorem c12k_aux_iteratedDeriv_re {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) :
    iteratedDeriv m (fun x => (f x).re) = fun x => (iteratedDeriv m f x).re := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    have hd : DifferentiableAt ℝ (iteratedDeriv m f) x :=
      (hf.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
    have := (Complex.reCLM.hasFDerivAt (x := iteratedDeriv m f x)).comp_hasDerivAt x hd.hasDerivAt
    exact this.deriv

/-- `|z|^a ≤ 1 + |z|^⌈a⌉₊`. -/
theorem c12k_aux_rpow_le (a : ℝ) (ha : 0 ≤ a) (z : ℝ) : |z| ^ a ≤ 1 + |z| ^ (⌈a⌉₊) := by
  rcases le_or_gt (|z|) 1 with h | h
  · have := Real.rpow_le_one (abs_nonneg z) h ha
    have : 0 ≤ |z| ^ (⌈a⌉₊) := by positivity
    linarith
  · have : |z| ^ a ≤ |z| ^ ((⌈a⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h.le (Nat.le_ceil a)
    rw [Real.rpow_natCast] at this
    linarith

/-- Weighted integrability of the real part of a Schwartz function. -/
theorem c12k_aux_weighted_re (K : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun z => |z| ^ a * |(K z).re|) := by
  refine (K.integrable.norm.add (K.integrable_pow_mul volume ⌈a⌉₊)).mono' ?_ ?_
  · exact ((continuous_abs.rpow_const (fun _ => Or.inr ha)).mul
      (Complex.continuous_re.comp K.continuous).abs).aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply, Real.norm_eq_abs]
    have h1 := c12k_aux_rpow_le a ha z
    have h2 : |(K z).re| ≤ ‖K z‖ := Complex.abs_re_le_norm _
    calc |z| ^ a * |(K z).re| ≤ (1 + |z| ^ (⌈a⌉₊)) * ‖K z‖ :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ‖K z‖ + |z| ^ (⌈a⌉₊) * ‖K z‖ := by ring

/-- Polynomial-weight integrability of a Schwartz function. -/
theorem c12k_aux_pow_mul_int (K : SchwartzMap ℝ ℂ) (r : ℕ) :
    Integrable (fun z : ℝ => (z : ℂ) ^ r * K z) := by
  refine (K.integrable_pow_mul volume r).mono' (by fun_prop) ?_
  refine Eventually.of_forall fun z => ?_
  rw [norm_mul, norm_pow, Complex.norm_real]

/-- Moments of a Schwartz function whose Fourier transform vanishes near zero. -/
theorem c12k_aux_moment_zero (K : SchwartzMap ℝ ℂ) (hK : 𝓕 (⇑K) =ᶠ[𝓝 0] fun _ => 0) (r : ℕ) :
    ∫ z : ℝ, (z : ℂ) ^ r * K z = 0 := by
  have hint : ∀ n : ℕ, ((n : ℕ∞) ≤ (r : ℕ∞)) →
      Integrable (fun x : ℝ => x ^ n • K x) volume := by
    intro n _
    refine (K.integrable_pow_mul volume n).mono' (by fun_prop) ?_
    refine Eventually.of_forall fun z => ?_
    rw [norm_smul, norm_pow, Real.norm_eq_abs]
  have h := Real.iteratedDeriv_fourier (f := ⇑K) (N := (r : ℕ∞)) (n := r) hint le_rfl
  have h0 := congrFun h 0
  rw [hK.iteratedDeriv_eq] at h0
  simp only [iteratedDeriv_const, Real.fourier_real_eq_integral_exp_smul, mul_zero,
    Complex.ofReal_zero] at h0
  simp only [ite_self, zero_mul, Complex.exp_zero, smul_eq_mul, one_mul] at h0
  have he : ∀ v : ℝ, (-2 * (π : ℂ) * Complex.I * v) ^ r * K v =
      (-2 * (π : ℂ) * Complex.I) ^ r * ((v : ℂ) ^ r * K v) := fun v => by ring
  simp_rw [he] at h0
  rw [integral_const_mul] at h0
  have hc : ((-2 : ℂ) * π * Complex.I) ^ r ≠ 0 := by
    apply pow_ne_zero
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  rcases mul_eq_zero.mp h0.symm with h | h
  · exact absurd h hc
  · exact h

/-- The kernel package for a smooth compactly supported even real symbol `g`. -/
theorem c12k_aux_real_kernel {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcs : HasCompactSupport g)
    (hev : ∀ ξ, g (-ξ) = g ξ) :
    (∃ K : SchwartzMap ℝ ℂ, (∀ x, K x = invFourierT (fun ξ => (g ξ : ℂ)) x) ∧
      (∀ ξ, fourierT (fun x => K x) ξ = (g ξ : ℂ))) ∧
    (∀ x, invFourierT (fun ξ => (g ξ : ℂ)) x = ((invFourierT (fun ξ => (g ξ : ℂ)) x).re : ℂ)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (invFourierT (fun ξ => (g ξ : ℂ)) x).re) ∧
    (∀ m : ℕ, ∃ K : SchwartzMap ℝ ℂ,
      (∀ x, iteratedDeriv m (fun x => (invFourierT (fun ξ => (g ξ : ℂ)) x).re) x = (K x).re) ∧
      ∀ w, 𝓕 (⇑K) w = (Complex.I * ((2 * π * w : ℝ) : ℂ)) ^ m * (g (2 * π * w) : ℂ)) ∧
    (∀ m : ℕ, Integrable (iteratedDeriv m (fun x => (invFourierT (fun ξ => (g ξ : ℂ)) x).re))) ∧
    (∀ (m : ℕ) (a : ℝ), 0 ≤ a → Integrable (fun z => |z| ^ a *
      |iteratedDeriv m (fun x => (invFourierT (fun ξ => (g ξ : ℂ)) x).re) z|)) := by
  set G : ℝ → ℂ := fun ξ => (g ξ : ℂ) with hGdef
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport G := hcs.comp_left Complex.ofReal_zero
  obtain ⟨K0, hK0, -, hK0f⟩ := c12k_aux_schwartz hGs hGc
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (invFourierT G) := by
    have : invFourierT G = ⇑K0 := funext fun x => (hK0 x).symm
    rw [this]; exact K0.smooth ⊤
  have hder : ∀ m : ℕ, ∃ K : SchwartzMap ℝ ℂ,
      (∀ x, iteratedDeriv m (fun x => (invFourierT G x).re) x = (K x).re) ∧
      ∀ w, 𝓕 (⇑K) w = (Complex.I * ((2 * π * w : ℝ) : ℂ)) ^ m * (g (2 * π * w) : ℂ) := by
    intro m
    have hGms : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (Complex.I * ξ) ^ m * G ξ) :=
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).pow m).mul hGs
    have hGmc : HasCompactSupport (fun ξ : ℝ => (Complex.I * ξ) ^ m * G ξ) := hGc.mul_left
    obtain ⟨Km, hKm, hKmF, -⟩ := c12k_aux_schwartz hGms hGmc
    refine ⟨Km, fun x => ?_, fun w => ?_⟩
    · rw [c12k_aux_iteratedDeriv_re hsm m,
        c03c_aux_invF_iter hGs.continuous hGc m, hKm x]
    · rw [hKmF w]
  refine ⟨⟨K0, hK0, hK0f⟩, c12k_aux_invF_real hev, Complex.reCLM.contDiff.comp hsm, hder,
    fun m => ?_, fun m a ha => ?_⟩
  · obtain ⟨K, hK, -⟩ := hder m
    have : iteratedDeriv m (fun x => (invFourierT G x).re) = fun x => (K x).re := funext hK
    rw [this]
    exact K.integrable.re
  · obtain ⟨K, hK, -⟩ := hder m
    have : iteratedDeriv m (fun x => (invFourierT G x).re) = fun x => (K x).re := funext hK
    rw [this]
    exact c12k_aux_weighted_re K a ha

/-- `q_p` package from `c12_cutoffs`. -/
theorem c12k_aux_q_props (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c12_inverse_symbol p) ∧ HasCompactSupport (c12_inverse_symbol p) ∧
    (∀ ξ, c12_inverse_symbol p (-ξ) = c12_inverse_symbol p ξ) ∧
    (fun w : ℝ => c12_inverse_symbol p (2 * π * w)) =ᶠ[𝓝 0] fun _ => 0 := by
  obtain ⟨hs, hev, hz, -, hc, -⟩ := c12_cutoffs.2.2.2 p hp hp1
  refine ⟨hs, hc, hev, ?_⟩
  have ht : Tendsto (fun w : ℝ => 2 * π * w) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun w : ℝ => 2 * π * w) (𝓝 0) (𝓝 (2 * π * 0)) :=
      ((continuous_const (y := 2 * π)).mul continuous_id).tendsto (0 : ℝ)
    rwa [mul_zero] at h
  filter_upwards [ht.eventually c12k_aux_near_zero] with w hw
  exact hz _ (Or.inl hw.le)

/-- Blueprint: lem:c12_kernel_schwartz.  For `0 < p < 1` the inverse transforms of `q_p` and `χ` are
real Schwartz functions whose (project-convention) Fourier transforms are `q_p` and `χ`; the real
kernels `K_p = Re q_p^∨` and `Re χ^∨` are smooth, and all their derivatives are integrable against
`|z|^a`, `a ≥ 0`. -/
theorem c12_kernel_schwartz (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∃ Kq : SchwartzMap ℝ ℂ,
      (∀ x, Kq x = invFourierT (fun ξ => (c12_inverse_symbol p ξ : ℂ)) x) ∧
      (∀ x, invFourierT (fun ξ => (c12_inverse_symbol p ξ : ℂ)) x = (c12_kernel p x : ℂ)) ∧
      (∀ ξ, fourierT (fun x => Kq x) ξ = (c12_inverse_symbol p ξ : ℂ))) ∧
    (∃ Kχ : SchwartzMap ℝ ℂ,
      (∀ x, Kχ x = invFourierT (fun ξ => (rho ξ : ℂ)) x) ∧
      (∀ x, invFourierT (fun ξ => (rho ξ : ℂ)) x =
        ((invFourierT (fun ξ => (rho ξ : ℂ)) x).re : ℂ)) ∧
      (∀ ξ, fourierT (fun x => Kχ x) ξ = (rho ξ : ℂ))) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c12_kernel p) ∧
    (∀ m : ℕ, Integrable (iteratedDeriv m (c12_kernel p))) ∧
    (∀ (m : ℕ) (a : ℝ), 0 ≤ a →
      Integrable (fun z => |z| ^ a * |iteratedDeriv m (c12_kernel p) z|)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (invFourierT (fun ξ => (rho ξ : ℂ)) x).re) ∧
    (∀ m : ℕ, Integrable (iteratedDeriv m (fun x => (invFourierT (fun ξ => (rho ξ : ℂ)) x).re))) ∧
    (∀ (m : ℕ) (a : ℝ), 0 ≤ a → Integrable (fun z => |z| ^ a *
      |iteratedDeriv m (fun x => (invFourierT (fun ξ => (rho ξ : ℂ)) x).re) z|)) := by
  obtain ⟨hs, hc, hev, -⟩ := c12k_aux_q_props p hp hp1
  obtain ⟨hKq, hrq, hsq, -, hiq, hwq⟩ := c12k_aux_real_kernel hs hc hev
  obtain ⟨hrs, hre, -, -, -, -, hrc⟩ := c12_cutoffs.2.1
  obtain ⟨hKr, hrr, hsr, -, hir, hwr⟩ := c12k_aux_real_kernel hrs hrc hre
  obtain ⟨Kq, h1, h2⟩ := hKq
  obtain ⟨Kr, h3, h4⟩ := hKr
  exact ⟨⟨Kq, h1, hrq, h2⟩, ⟨Kr, h3, hrr, h4⟩, hsq, hiq, hwq, hsr, hir, hwr⟩

/-- Blueprint: lem:c12_kernel_moments.  For `0 < p < 1` and `r, m ∈ ℕ`, `z^r K_p^{(m)}(z)` is
integrable with zero integral. -/
theorem c12_kernel_moments (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (r m : ℕ) :
    Integrable (fun z => z ^ r * iteratedDeriv m (c12_kernel p) z) ∧
    ∫ z, z ^ r * iteratedDeriv m (c12_kernel p) z = 0 := by
  obtain ⟨hs, hc, hev, hz⟩ := c12k_aux_q_props p hp hp1
  obtain ⟨-, -, -, hder, -, -⟩ := c12k_aux_real_kernel hs hc hev
  obtain ⟨K, hK, hKF⟩ := hder m
  have hD : iteratedDeriv m (c12_kernel p) = fun x => (K x).re := funext hK
  have hF : 𝓕 (⇑K) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hz] with w hw
    rw [hKF w, hw]; simp
  have he : (fun z : ℝ => z ^ r * iteratedDeriv m (c12_kernel p) z) =
      fun z : ℝ => RCLike.re ((z : ℂ) ^ r * K z) := by
    funext z; rw [hD]; simp [← Complex.ofReal_pow]
  rw [he]
  refine ⟨(c12k_aux_pow_mul_int K r).re, ?_⟩
  rw [integral_re (c12k_aux_pow_mul_int K r), c12k_aux_moment_zero K hF r]
  simp

/-! ### Scaling helpers -/

theorem c12k_aux_two_pow (j : ℕ) : (2 : ℝ) ^ j = (2 : ℝ) ^ (j : ℝ) := (Real.rpow_natCast 2 j).symm

theorem c12k_aux_deriv_formula (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j m : ℕ) (x : ℝ) :
    iteratedDeriv m (c12_scaled_kernel p j) x =
      (2 : ℝ) ^ (((m : ℝ) + 1 - p) * (j : ℝ)) * iteratedDeriv m (c12_kernel p) ((2 : ℝ) ^ j * x) := by
  obtain ⟨-, -, hsm, -⟩ := c12_kernel_schwartz p hp hp1
  have h1 : c12_scaled_kernel p j = fun x =>
      (2 : ℝ) ^ ((1 - p) * (j : ℝ)) * (fun y => c12_kernel p ((2 : ℝ) ^ j * y)) x := rfl
  rw [h1, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul (hsm.of_le (by simp))]
  rw [← mul_assoc]
  congr 1
  rw [c12k_aux_two_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1; ring

theorem c12k_aux_scale_const (p : ℝ) (j : ℕ) :
    ((2 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ ((1 - p) * (j : ℝ)) = ((2 : ℝ) ^ j) ^ (-p) := by
  rw [c12k_aux_two_pow, ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_mul (by norm_num)]
  congr 1; ring

theorem c12k_aux_fourier_scaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j : ℕ) (ξ : ℝ) :
    fourierT (fun x => (c12_scaled_kernel p j x : ℂ)) ξ =
      ((if ξ = 0 then 0 else c12_annulus (ξ / (2 : ℝ) ^ j) * |ξ| ^ (-p) : ℝ) : ℂ) := by
  obtain ⟨⟨Kq, h1, hrq, h2⟩, -⟩ := c12_kernel_schwartz p hp hp1
  have hF : ∀ η, fourierT (fun x => (c12_kernel p x : ℂ)) η = (c12_inverse_symbol p η : ℂ) := by
    intro η
    rw [← h2 η]
    congr 1; funext x; rw [h1, hrq]
  set c : ℝ := (2 : ℝ) ^ j with hc
  have hc0 : 0 < c := by positivity
  set s : ℝ := (2 : ℝ) ^ ((1 - p) * (j : ℝ)) with hs
  set g : ℝ → ℂ := fun u => (s : ℂ) * ((c12_kernel p u : ℂ) *
    Complex.exp (-(Complex.I * (u : ℂ) * ((ξ / c : ℝ) : ℂ)))) with hg
  have hint : fourierT (fun x => (c12_scaled_kernel p j x : ℂ)) ξ = ∫ x, g (c * x) := by
    unfold fourierT
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hg, c12_scaled_kernel]
    push_cast
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    field_simp
    rw [mul_comm x c]
  rw [hint, Measure.integral_comp_mul_left, hg, integral_const_mul]
  have hF' := hF (ξ / c)
  unfold fourierT at hF'
  rw [hF', abs_inv, abs_of_pos hc0, Complex.real_smul]
  have key : c⁻¹ * s * c12_inverse_symbol p (ξ / c) =
      (if ξ = 0 then 0 else c12_annulus (ξ / c) * |ξ| ^ (-p)) := by
    unfold c12_inverse_symbol
    by_cases hξ : ξ = 0
    · simp [hξ]
    · have hξc : ξ / c ≠ 0 := div_ne_zero hξ hc0.ne'
      simp only [hξc, hξ, ↓reduceIte]
      rw [abs_div, abs_of_pos hc0,
        Real.div_rpow (abs_nonneg _) hc0.le, hc, hs, c12k_aux_scale_const]
      have : ((2 : ℝ) ^ j) ^ (-p) ≠ 0 := by positivity
      field_simp
  rw [← key]
  push_cast
  ring

theorem c12k_aux_weight_const (p a : ℝ) (j m : ℕ) :
    (2 : ℝ) ^ (((m : ℝ) + 1 - p) * (j : ℝ)) * (((2 : ℝ) ^ j) ^ a)⁻¹ * ((2 : ℝ) ^ j)⁻¹ =
      (2 : ℝ) ^ (((m : ℝ) - p - a) * (j : ℝ)) := by
  rw [c12k_aux_two_pow, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num),
    ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1; ring

theorem c12k_aux_weighted_scaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun z => |z| ^ a * |iteratedDeriv m (c12_scaled_kernel p j) z|) ∧
      ∫ z, |z| ^ a * |iteratedDeriv m (c12_scaled_kernel p j) z| =
        (2 : ℝ) ^ (((m : ℝ) - p - a) * (j : ℝ)) *
          ∫ z, |z| ^ a * |iteratedDeriv m (c12_kernel p) z| := by
  obtain ⟨-, -, -, -, hw, -⟩ := c12_kernel_schwartz p hp hp1
  set c : ℝ := (2 : ℝ) ^ j with hc
  have hc0 : 0 < c := by positivity
  set T : ℝ := (2 : ℝ) ^ (((m : ℝ) + 1 - p) * (j : ℝ)) with hT
  have hT0 : 0 < T := by positivity
  set w : ℝ → ℝ := fun u => |u| ^ a * |iteratedDeriv m (c12_kernel p) u| with hwdef
  have hpt : (fun z => |z| ^ a * |iteratedDeriv m (c12_scaled_kernel p j) z|) =
      fun z => (T * (c ^ a)⁻¹) * w (c * z) := by
    funext z
    rw [c12k_aux_deriv_formula p hp hp1 j m z, hwdef]
    simp only
    rw [abs_mul (T), abs_of_pos hT0, abs_mul c, abs_of_pos hc0,
      Real.mul_rpow hc0.le (abs_nonneg z)]
    have : c ^ a ≠ 0 := by positivity
    field_simp
    rw [mul_comm z c]
  rw [hpt]
  refine ⟨((hw m a ha).comp_mul_left' hc0.ne').const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left, abs_inv, abs_of_pos hc0, smul_eq_mul,
    ← mul_assoc, hT, hc, c12k_aux_weight_const]

theorem c12k_aux_moment_scaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j r m : ℕ) :
    Integrable (fun z => z ^ r * iteratedDeriv m (c12_scaled_kernel p j) z) ∧
      ∫ z, z ^ r * iteratedDeriv m (c12_scaled_kernel p j) z = 0 := by
  obtain ⟨hi, h0⟩ := c12_kernel_moments p hp hp1 r m
  set c : ℝ := (2 : ℝ) ^ j with hc
  have hc0 : 0 < c := by positivity
  set T : ℝ := (2 : ℝ) ^ (((m : ℝ) + 1 - p) * (j : ℝ)) with hT
  have hpt : (fun z => z ^ r * iteratedDeriv m (c12_scaled_kernel p j) z) =
      fun z => (T * (c ^ r)⁻¹) * ((c * z) ^ r * iteratedDeriv m (c12_kernel p) (c * z)) := by
    funext z
    rw [c12k_aux_deriv_formula p hp hp1 j m z, mul_pow]
    have : c ^ r ≠ 0 := by positivity
    field_simp
    rw [mul_comm z c]
  rw [hpt]
  refine ⟨(hi.comp_mul_left' hc0.ne').const_mul _, ?_⟩
  rw [integral_const_mul,
    Measure.integral_comp_mul_left (fun u => u ^ r * iteratedDeriv m (c12_kernel p) u), h0]
  simp

/-- Blueprint: lem:c12_kernel_scaling.  Exact dyadic scaling of `K_{p,j}`: derivative formula,
Fourier transform `φ(2^{-j}ξ)|ξ|^{-p}` (zero at `ξ = 0`), weighted integrals and vanishing moments. -/
theorem c12_kernel_scaling (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (c12_scaled_kernel p j) ∧
    (∀ (m : ℕ) (x : ℝ), iteratedDeriv m (c12_scaled_kernel p j) x =
      (2 : ℝ) ^ (((m : ℝ) + 1 - p) * (j : ℝ)) * iteratedDeriv m (c12_kernel p) ((2 : ℝ) ^ j * x)) ∧
    (∀ ξ : ℝ, fourierT (fun x => (c12_scaled_kernel p j x : ℂ)) ξ =
      ((if ξ = 0 then 0 else c12_annulus (ξ / (2 : ℝ) ^ j) * |ξ| ^ (-p) : ℝ) : ℂ)) ∧
    (∀ (m : ℕ) (a : ℝ), 0 ≤ a →
      Integrable (fun z => |z| ^ a * |iteratedDeriv m (c12_scaled_kernel p j) z|) ∧
      ∫ z, |z| ^ a * |iteratedDeriv m (c12_scaled_kernel p j) z| =
        (2 : ℝ) ^ (((m : ℝ) - p - a) * (j : ℝ)) *
          ∫ z, |z| ^ a * |iteratedDeriv m (c12_kernel p) z|) ∧
    (∀ (r m : ℕ), Integrable (fun z => z ^ r * iteratedDeriv m (c12_scaled_kernel p j) z) ∧
      ∫ z, z ^ r * iteratedDeriv m (c12_scaled_kernel p j) z = 0) := by
  obtain ⟨-, -, hsm, -⟩ := c12_kernel_schwartz p hp hp1
  refine ⟨contDiff_const.mul (hsm.comp (contDiff_const.mul contDiff_id)),
    c12k_aux_deriv_formula p hp hp1 j, c12k_aux_fourier_scaled p hp hp1 j,
    c12k_aux_weighted_scaled p hp hp1 j, fun r m => c12k_aux_moment_scaled p hp hp1 j r m⟩

end GSQG
