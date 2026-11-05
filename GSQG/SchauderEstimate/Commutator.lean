import GSQG.SchauderEstimate.HolderTransport

/-!
# Beyond the paper (Schauder estimate cited in §4): local finiteness of `|D|^p w`, the cutoff
commutator and the localized right-hand side (blueprint ch. 12). Helpers `c12m_aux_*`.

Notation: `χ = rho`, `η = c12_eta`, `c_p = calpha p` (the constant of `fracD`),
`N_a(u) = c03_holder_normR a univ u`, `N_a(u; I) = c03_holder_normR a I u`.
The far kernel `κ_p(z) = (1 - χ(z)) |z|^{-1-p}` is written out explicitly.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

theorem c12m_aux_rho_nonneg (z : ℝ) : 0 ≤ rho z := Real.smoothTransition.nonneg _
theorem c12m_aux_rho_le_one (z : ℝ) : rho z ≤ 1 := Real.smoothTransition.le_one _
theorem c12m_aux_rho_zero {z : ℝ} (hz : 2 ≤ |z|) : rho z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem c12m_aux_rho_one {z : ℝ} (hz : |z| ≤ 1) : rho z = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem c12m_aux_rho_cont : Continuous rho :=
  Real.smoothTransition.continuous.comp (continuous_const.sub continuous_abs)

/-- Local bound for a continuous function on a compact interval. -/
theorem c12m_aux_bound {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    ∃ M, ∀ y ∈ Icc a b, |f y| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨M, fun y hy => by simpa [Real.norm_eq_abs] using hM y hy⟩

/-- The near majorant is integrable. -/
theorem c12m_aux_near_majorant_int (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Integrable ((Icc (-2 : ℝ) 2).indicator (fun z => |z| ^ (-p))) := by
  refine (c03_aux_psi_integrable p 1 2 hp hp1).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((continuous_abs.measurable.pow_const _).indicator measurableSet_Icc).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    by_cases hz : z ∈ Icc (-2 : ℝ) 2
    · rw [indicator_of_mem hz, abs_of_nonneg (by positivity)]
      unfold c03_aux_psi
      split_ifs with h1
      · linarith
      · rw [not_le] at h1
        have hz2 : |z| ≤ 2 := abs_le.2 hz
        have hzp : 0 < |z| := by linarith
        have : |z| ^ (-p) = |z| * |z| ^ (-(p + 1)) := by
          rw [show -p = 1 + (-(p+1)) by ring, Real.rpow_add hzp, Real.rpow_one]
        rw [this]
        exact mul_le_mul_of_nonneg_right hz2 (by positivity)
    · rw [indicator_of_notMem hz, abs_zero]
      exact c03_aux_psi_nonneg p (by norm_num) (by norm_num) z

/-- Pointwise near bound. -/
theorem c12m_aux_near_bound (p : ℝ) (hp : 0 < p) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (a b M : ℝ) (hM : ∀ y ∈ Icc (a - 2) (b + 2), |deriv f y| ≤ M) (x : ℝ) (hx : x ∈ Icc a b)
    (z : ℝ) :
    |rho z * (f x - f (x - z)) / |z| ^ (1 + p)| ≤
      M * (Icc (-2 : ℝ) 2).indicator (fun z => |z| ^ (-p)) z := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  by_cases hz : z ∈ Icc (-2 : ℝ) 2
  · rw [indicator_of_mem hz]
    rcases eq_or_ne z 0 with rfl | hz0
    · simp [Real.zero_rpow (by linarith : (1 + p) ≠ 0)]
      exact mul_nonneg hM0 (by positivity)
    have hzp : 0 < |z| := abs_pos.2 hz0
    have hmv : ‖f x - f (x - z)‖ ≤ M * ‖x - (x - z)‖ := by
      refine (convex_Icc (a - 2) (b + 2)).norm_image_sub_le_of_norm_deriv_le
        (fun y _ => hf.differentiableAt) (fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy)
        ⟨by linarith [hx.1, hz.2], by linarith [hx.2, hz.1]⟩
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simp only [Real.norm_eq_abs, sub_sub_cancel] at hmv
    rw [abs_div, abs_mul, abs_of_nonneg (c12m_aux_rho_nonneg z),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      div_le_iff₀ (Real.rpow_pos_of_pos hzp _)]
    have h1 : |z| ^ (-p) * |z| ^ (1 + p) = |z| := by
      rw [← Real.rpow_add hzp]; simp
    calc rho z * |f x - f (x - z)| ≤ 1 * (M * |z|) :=
          mul_le_mul (c12m_aux_rho_le_one z) hmv (abs_nonneg _) (by norm_num)
      _ = M * (|z| ^ (-p) * |z| ^ (1 + p)) := by rw [h1]; ring
      _ = M * |z| ^ (-p) * |z| ^ (1 + p) := by ring
  · rw [indicator_of_notMem hz, mul_zero]
    have h2 : 2 ≤ |z| := by
      by_contra h; rw [not_le] at h; exact hz (abs_le.1 h.le)
    rw [c12m_aux_rho_zero h2]; simp

/-- Blueprint: lem:c12_frac_near_smooth.  The near part
`U(x) = c_p ∫ χ(z) (w(x) - w(x-z)) |z|^{-1-p} dz` of `|D|^p w` is smooth for every smooth `w`
(no global bounds); its `m`-th derivative is the same absolutely convergent integral with `w^{(m)}`,
and on `[a,b]` all differentiated integrands are dominated by `M 1_{[-2,2]}(z) |z|^{-p}`, where `M`
is any bound of `w^{(m+1)}` on `[a-2,b+2]`. -/
theorem c12_frac_near_smooth (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => calpha p * ∫ z, rho z * (w x - w (x - z)) / |z| ^ (1 + p)) ∧
    (∀ (m : ℕ) (x : ℝ),
      Integrable (fun z => rho z * (iteratedDeriv m w x - iteratedDeriv m w (x - z)) /
        |z| ^ (1 + p)) ∧
      iteratedDeriv m (fun x => calpha p * ∫ z, rho z * (w x - w (x - z)) / |z| ^ (1 + p)) x =
        calpha p * ∫ z, rho z * (iteratedDeriv m w x - iteratedDeriv m w (x - z)) /
          |z| ^ (1 + p)) ∧
    Integrable ((Icc (-2 : ℝ) 2).indicator (fun z => |z| ^ (-p))) ∧
    (∀ (m : ℕ) (a b M : ℝ), (∀ y ∈ Icc (a - 2) (b + 2), |iteratedDeriv (m + 1) w y| ≤ M) →
      ∀ x ∈ Icc a b, ∀ z : ℝ,
        |rho z * (iteratedDeriv m w x - iteratedDeriv m w (x - z)) / |z| ^ (1 + p)| ≤
          M * (Icc (-2 : ℝ) 2).indicator (fun z => |z| ^ (-p)) z) := by
  set I : ℝ → ℝ := (Icc (-2 : ℝ) 2).indicator (fun z => |z| ^ (-p)) with hI
  have hIint : Integrable I := c12m_aux_near_majorant_int p hp hp1
  set W : ℕ → ℝ → ℝ := fun m => iteratedDeriv m w with hW
  have hWc : ∀ m, Continuous (W m) := fun m =>
    hw.continuous_iteratedDeriv m (by exact_mod_cast le_top)
  have hWd : ∀ m, Differentiable ℝ (W m) := fun m =>
    hw.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)
  have hWderiv : ∀ m, deriv (W m) = W (m + 1) := fun m => by
    simp only [W, iteratedDeriv_succ]
  set N : ℕ → ℝ → ℝ → ℝ := fun m x z => rho z * (W m x - W m (x - z)) / |z| ^ (1 + p) with hN
  have hbound : ∀ (m : ℕ) (a b M : ℝ), (∀ y ∈ Icc (a - 2) (b + 2), |W (m + 1) y| ≤ M) →
      ∀ x ∈ Icc a b, ∀ z : ℝ, |N m x z| ≤ M * I z := by
    intro m a b M hM x hx z
    exact c12m_aux_near_bound p hp (hWd m) a b M (fun y hy => by rw [hWderiv]; exact hM y hy) x hx z
  have hmeas : ∀ m x, AEStronglyMeasurable (N m x) volume := fun m x =>
    (((c12m_aux_rho_cont.measurable).mul (measurable_const.sub
      ((hWc m).measurable.comp (measurable_const.sub measurable_id)))).div
      (continuous_abs.measurable.pow_const _)).aestronglyMeasurable
  have hint : ∀ m x, Integrable (N m x) := by
    intro m x
    obtain ⟨M, hM⟩ := c12m_aux_bound (hWc (m + 1)) (x - 2) (x + 2)
    exact (hIint.const_mul M).mono' (hmeas m x) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hbound m x x M hM x ⟨le_rfl, le_rfl⟩ z)
  set H : ℕ → ℝ → ℝ := fun m x => calpha p * ∫ z, N m x z with hH
  have hderiv : ∀ m x₀, HasDerivAt (H m) (H (m + 1) x₀) x₀ := by
    intro m x₀
    obtain ⟨M, hM⟩ := c12m_aux_bound (hWc (m + 2)) (x₀ - 1 - 2) (x₀ + 1 + 2)
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun x z => N m x z) (F' := fun x z => N (m + 1) x z)
      (bound := fun z => M * I z) (x₀ := x₀) (s := Metric.ball x₀ 1)
      (Metric.ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x => hmeas m x) (hint m x₀) (hmeas (m + 1) x₀)
      (Eventually.of_forall fun z x hx => by
        rw [Real.norm_eq_abs]
        have hx' : x ∈ Icc (x₀ - 1) (x₀ + 1) := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
          exact ⟨by linarith, by linarith⟩
        exact hbound (m + 1) (x₀ - 1) (x₀ + 1) M hM x hx' z)
      (hIint.const_mul M)
      (Eventually.of_forall fun z x _ => by
        have h1 : HasDerivAt (W m) (W (m + 1) x) x := by
          rw [← hWderiv]; exact (hWd m x).hasDerivAt
        have h2 : HasDerivAt (fun x => W m (x - z)) (W (m + 1) (x - z)) x := by
          have := (hWd m (x - z)).hasDerivAt
          rw [hWderiv] at this
          simpa using this.comp_sub_const x z
        have h3 := ((h1.sub h2).const_mul (rho z)).div_const (|z| ^ (1 + p))
        simpa [N] using h3)
    exact key.2.const_mul (calpha p)
  have hiter : ∀ m x, iteratedDeriv m (H 0) x = H m x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [iteratedDeriv_succ, funext ih, (hderiv m x).deriv]
  have hH0 : (fun x => calpha p * ∫ z, rho z * (w x - w (x - z)) / |z| ^ (1 + p)) = H 0 := by
    funext x; simp [H, N, W]
  rw [hH0]
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun m x => ⟨hint m x, hiter m x⟩,
    hIint, fun m a b M hM x hx z => hbound m a b M hM x hx z⟩
  rw [funext (hiter m)]
  exact fun x => (hderiv m x).differentiableAt


theorem c12m_aux_rho_smooth : ContDiff ℝ (⊤ : ℕ∞) rho := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    have : ∀ᶠ ξ in 𝓝 (0 : ℝ), |ξ| < 1 := by
      have := (continuous_abs.tendsto (0 : ℝ)); rw [abs_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [this] with ξ hξ
    exact c12m_aux_rho_one hξ.le
  · unfold rho
    exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.sub (contDiffAt_abs hx))

/-- Shifted Peetre bound. -/
theorem c12m_aux_shift {r : ℝ} (hr : 0 ≤ r) {x x₀ R : ℝ} (hx : |x - x₀| ≤ R) (z : ℝ) :
    (1 + |x - z|) ^ (-r) ≤ (1 + R) ^ r * (1 + |z - x₀|) ^ (-r) := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hx
  have hp := c03_aux_peetre (x - x₀) (z - x₀)
  rw [show x - x₀ - (z - x₀) = x - z by ring] at hp
  have h1 : (1 + |z - x₀|) / (1 + R) ≤ 1 + |x - z| := by
    rw [div_le_iff₀ (by positivity)]
    calc 1 + |z - x₀| ≤ (1 + |x - x₀|) * (1 + |x - z|) := hp
      _ ≤ (1 + R) * (1 + |x - z|) := by gcongr
      _ = _ := by ring
  calc (1 + |x - z|) ^ (-r) ≤ ((1 + |z - x₀|) / (1 + R)) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    _ = (1 + R) ^ r * (1 + |z - x₀|) ^ (-r) := by
        rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + R),
          div_eq_mul_inv, inv_inv]; ring

theorem c12m_aux_shift_int {r : ℝ} (hr : 1 < r) (x₀ : ℝ) :
    Integrable (fun z : ℝ => (1 + |z - x₀|) ^ (-r)) := by
  have hint0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-r)) volume :=
    integrable_one_add_norm (by simp; linarith)
  simpa [Real.norm_eq_abs] using hint0.comp_sub_right x₀

/-- Smoothness of `x ↦ ∫ κ(x - z) G(z) dz` for bounded measurable `G` and a smooth kernel with
integrable derivative decay; derivatives fall on the kernel. -/
theorem c12m_aux_conv_smooth {κ : ℝ → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {r : ℝ} (hr : 1 < r)
    (D : ℕ → ℝ) (hD0 : ∀ j, 0 ≤ D j) (hD : ∀ j t, |iteratedDeriv j κ t| ≤ D j * (1 + |t|) ^ (-r))
    {G : ℝ → ℝ} (hG : Measurable G) {M : ℝ} (hM : ∀ z, |G z| ≤ M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z, κ (x - z) * G z) ∧
    (∀ j x, Integrable (fun z => iteratedDeriv j κ (x - z) * G z) ∧
      iteratedDeriv j (fun x => ∫ z, κ (x - z) * G z) x =
        ∫ z, iteratedDeriv j κ (x - z) * G z) ∧
    (∀ j x₀ R x, |x - x₀| ≤ R → ∀ z, |iteratedDeriv j κ (x - z) * G z| ≤
        M * D j * ((1 + R) ^ r * (1 + |z - x₀|) ^ (-r))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hcj : ∀ j, Continuous (iteratedDeriv j κ) := fun j =>
    hκ.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  have hunif : ∀ j x₀ R x, |x - x₀| ≤ R → ∀ z, |iteratedDeriv j κ (x - z) * G z| ≤
      M * D j * ((1 + R) ^ r * (1 + |z - x₀|) ^ (-r)) := by
    intro j x₀ R x hx z
    rw [abs_mul]
    calc |iteratedDeriv j κ (x - z)| * |G z| ≤ (D j * (1 + |x - z|) ^ (-r)) * M :=
          mul_le_mul (hD j _) (hM z) (abs_nonneg _) (mul_nonneg (hD0 j) (by positivity))
      _ ≤ (D j * ((1 + R) ^ r * (1 + |z - x₀|) ^ (-r))) * M := by
          have := c12m_aux_shift (r := r) (by linarith) hx z
          have := hD0 j
          gcongr
      _ = _ := by ring
  have hmeas : ∀ j x, AEStronglyMeasurable (fun z => iteratedDeriv j κ (x - z) * G z) volume :=
    fun j x => (((hcj j).measurable.comp (measurable_const.sub measurable_id)).mul hG).aestronglyMeasurable
  have hint : ∀ j x, Integrable (fun z => iteratedDeriv j κ (x - z) * G z) := fun j x =>
    (((c12m_aux_shift_int hr x).const_mul ((1 + 0) ^ r)).const_mul (M * D j)).mono' (hmeas j x)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hunif j x 0 x (by simp) z)
  set F : ℕ → ℝ → ℝ := fun j x => ∫ z, iteratedDeriv j κ (x - z) * G z with hF
  have hderiv : ∀ j x₀, HasDerivAt (F j) (F (j + 1) x₀) x₀ := by
    intro j x₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun x z => iteratedDeriv j κ (x - z) * G z)
      (F' := fun x z => iteratedDeriv (j + 1) κ (x - z) * G z)
      (bound := fun z => M * D (j + 1) * ((1 + 1) ^ r * (1 + |z - x₀|) ^ (-r)))
      (x₀ := x₀) (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x => hmeas j x) (hint j x₀) (hmeas (j + 1) x₀)
      (Eventually.of_forall fun z x hx => by
        rw [Real.norm_eq_abs]
        rw [Metric.mem_ball, Real.dist_eq] at hx
        exact hunif (j + 1) x₀ 1 x hx.le z)
      (((c12m_aux_shift_int hr x₀).const_mul _).const_mul _)
      (Eventually.of_forall fun z x _ => by
        have h1 : HasDerivAt (iteratedDeriv j κ) (iteratedDeriv (j + 1) κ (x - z)) (x - z) := by
          have := ((hκ.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _))
            (x - z)).hasDerivAt
          rwa [← iteratedDeriv_succ] at this
        exact (h1.comp_sub_const x z).mul_const (G z))
    exact key.2
  have hiter : ∀ j x, iteratedDeriv j (F 0) x = F j x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [iteratedDeriv_succ, funext ih, (hderiv j x).deriv]
  have hF0 : (fun x => ∫ z, κ (x - z) * G z) = F 0 := by
    funext x; simp [F]
  rw [hF0]
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_,
    fun j x => ⟨hint j x, hiter j x⟩, hunif⟩
  rw [funext (hiter m)]
  exact fun x => (hderiv m x).differentiableAt

/-- Blueprint: lem:c12_frac_far_smooth.  The far kernel `κ_p(z) = (1 - χ(z)) |z|^{-1-p}` is smooth
with integrable derivatives; for smooth bounded `w` the far part
`c_p ∫ (1-χ(z)) (w(x) - w(x-z)) |z|^{-1-p} dz = c_p (w(x) ∫ κ_p - ∫ κ_p(x-z) w(z) dz)` converges
absolutely and is smooth, the convolution being differentiated through the kernel, with integrable
majorants uniform for `x` in compact intervals. -/
theorem c12_frac_far_smooth (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwb : ∃ M, ∀ x, |w x| ≤ M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => (1 - rho z) / |z| ^ (1 + p)) ∧
    (∀ m : ℕ, Integrable (iteratedDeriv m (fun z : ℝ => (1 - rho z) / |z| ^ (1 + p)))) ∧
    (∀ x : ℝ, Integrable (fun z => (1 - rho z) * (w x - w (x - z)) / |z| ^ (1 + p)) ∧
      calpha p * ∫ z, (1 - rho z) * (w x - w (x - z)) / |z| ^ (1 + p) =
        calpha p * (w x * (∫ z, (1 - rho z) / |z| ^ (1 + p)) -
          ∫ z, (1 - rho (x - z)) / |x - z| ^ (1 + p) * w z)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x => calpha p * (w x * (∫ z, (1 - rho z) / |z| ^ (1 + p)) -
          ∫ z, (1 - rho (x - z)) / |x - z| ^ (1 + p) * w z)) ∧
    (∀ (m : ℕ) (x : ℝ),
      Integrable (fun z => iteratedDeriv m (fun t : ℝ => (1 - rho t) / |t| ^ (1 + p)) (x - z) *
        w z) ∧
      iteratedDeriv m (fun x => ∫ z, (1 - rho (x - z)) / |x - z| ^ (1 + p) * w z) x =
        ∫ z, iteratedDeriv m (fun t : ℝ => (1 - rho t) / |t| ^ (1 + p)) (x - z) * w z) ∧
    (∀ (m : ℕ) (a b : ℝ), ∃ g : ℝ → ℝ, Integrable g ∧ ∀ x ∈ Icc a b, ∀ z : ℝ,
      |iteratedDeriv m (fun t : ℝ => (1 - rho t) / |t| ^ (1 + p)) (x - z) * w z| ≤ g z) := by
  obtain ⟨M, hM⟩ := hwb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set κ : ℝ → ℝ := fun z : ℝ => (1 - rho z) / |z| ^ (1 + p) with hκdef
  have hκeq : κ = c03_aux_faromega p rho := by
    funext t; simp only [κ, c03_aux_faromega, add_comm (1 : ℝ) p]
  have hrho1 : ∀ t ∈ Icc (-1 : ℝ) 1, rho t = 1 := fun t ht => c12m_aux_rho_one (abs_le.2 ht)
  have hrho2 : ∀ t, 2 < |t| → rho t = 0 := fun t ht => c12m_aux_rho_zero ht.le
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ := by
    rw [hκeq]; exact c03_aux_faromega_smooth p c12m_aux_rho_smooth hrho1
  have hdec : ∀ j, ∃ C, 0 ≤ C ∧ ∀ t, |iteratedDeriv j κ t| ≤ C * (1 + |t|) ^ (-(p + 1)) := by
    intro j
    obtain ⟨C, hC0, hC⟩ := c03_aux_faromega_decay p hp c12m_aux_rho_smooth hrho1 hrho2 j
    exact ⟨C, hC0, fun t => by rw [hκeq, ← Real.norm_eq_abs]; exact hC t⟩
  choose D hD0 hD using hdec
  have hr : 1 < p + 1 := by linarith
  have hcj : ∀ j, Continuous (iteratedDeriv j κ) := fun j =>
    hκs.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  have hκint : ∀ j, Integrable (iteratedDeriv j κ) := fun j =>
    ((c12m_aux_shift_int hr 0).const_mul (D j)).mono' (hcj j).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, sub_zero]; exact hD j t)
  have hκint0 : Integrable κ := by simpa using hκint 0
  obtain ⟨hCs, hCd, hCu⟩ := c12m_aux_conv_smooth hκs hr D hD0 hD hw.continuous.measurable hM
  refine ⟨hκs, hκint, fun x => ?_, ?_, hCd, fun m a b => ?_⟩
  · have hfun : (fun z => (1 - rho z) * (w x - w (x - z)) / |z| ^ (1 + p)) =
        fun z => w x * κ z - κ z * w (x - z) := by
      funext z; simp only [κ]; ring
    have hi2 : Integrable (fun z => κ z * w (x - z)) := by
      have := (hCd 0 x).1
      have h2 := this.comp_sub_left x
      simpa [sub_sub_cancel] using h2
    have hi1 : Integrable (fun z => w x * κ z) := hκint0.const_mul _
    rw [hfun]
    refine ⟨hi1.sub hi2, ?_⟩
    rw [integral_sub hi1 hi2, integral_const_mul]
    congr 2
    have := integral_sub_left_eq_self (fun z => κ (x - z) * w z) (μ := volume) x
    simp only [sub_sub_cancel] at this
    exact this
  · exact contDiff_const.mul ((hw.mul contDiff_const).sub hCs)
  · refine ⟨fun z => M * D m * ((1 + |b - a|) ^ (p + 1) * (1 + |z - a|) ^ (-(p + 1))),
      ((c12m_aux_shift_int hr a).const_mul _).const_mul _, fun x hx z => ?_⟩
    exact hCu m a |b - a| x (by rw [abs_of_nonneg (by linarith [hx.1])]; exact
      (sub_le_sub_right hx.2 a).trans (le_abs_self _)) z


/-- The split `|D|^p w = near + far`, with absolute convergence. -/
theorem c12m_aux_frac_split (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwb : ∃ M, ∀ x, |w x| ≤ M) (y : ℝ) :
    Integrable (fun z => (w y - w z) / |y - z| ^ (p + 1)) ∧
    fracD p w y = calpha p * (∫ z, rho z * (w y - w (y - z)) / |z| ^ (1 + p)) +
      calpha p * (w y * (∫ z, (1 - rho z) / |z| ^ (1 + p)) -
          ∫ z, (1 - rho (y - z)) / |y - z| ^ (1 + p) * w z) := by
  have hN := ((c12_frac_near_smooth p hp hp1 w hw).2.1 0 y).1
  simp only [iteratedDeriv_zero] at hN
  obtain ⟨hFi, hFe⟩ := (c12_frac_far_smooth p hp hp1 w hw hwb).2.2.1 y
  set g : ℝ → ℝ := fun z => (w y - w (y - z)) / |z| ^ (p + 1) with hg
  have hgs : g = fun z => rho z * (w y - w (y - z)) / |z| ^ (1 + p) +
      (1 - rho z) * (w y - w (y - z)) / |z| ^ (1 + p) := by
    funext z; simp only [g, add_comm p 1]; ring
  have hgi : Integrable g := by rw [hgs]; exact hN.add hFi
  have hfg : (fun z => (w y - w z) / |y - z| ^ (p + 1)) = fun z => g (y - z) := by
    funext z; simp [g]
  refine ⟨by rw [hfg]; exact hgi.comp_sub_left y, ?_⟩
  unfold fracD
  rw [hfg, integral_sub_left_eq_self g (μ := volume) y, hgs, integral_add hN hFi, mul_add, hFe]

/-- Blueprint: lem:c12_frac_local_finite.  For smooth bounded `w` the singular integral of
`|D|^p w(y)` converges absolutely at every `y`, `|D|^p w` is smooth, and hence
`|D|^p w ∈ C^a([-1,1])` for every noninteger `a > 0` (qualitative; no bound is claimed). -/
theorem c12_frac_local_finite (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwb : ∃ M, ∀ x, |w x| ≤ M) :
    (∀ y : ℝ, Integrable (fun z => (w y - w z) / |y - z| ^ (p + 1))) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fracD p w) ∧
    ∀ a : ℝ, 0 < a → (∀ n : ℕ, a ≠ n) → fracD p w ∈ c03_holder a (Icc (-1) 1) := by
  have hsplit := c12m_aux_frac_split p hp hp1 w hw hwb
  have heq : fracD p w = fun y => calpha p * (∫ z, rho z * (w y - w (y - z)) / |z| ^ (1 + p)) +
      calpha p * (w y * (∫ z, (1 - rho z) / |z| ^ (1 + p)) -
          ∫ z, (1 - rho (y - z)) / |y - z| ^ (1 + p) * w z) := funext fun y => (hsplit y).2
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fracD p w) := by
    rw [heq]
    exact (c12_frac_near_smooth p hp hp1 w hw).1.add
      (c12_frac_far_smooth p hp hp1 w hw hwb).2.2.2.1
  exact ⟨fun y => (hsplit y).1, hcd, fun a _ _ =>
    c03_aux_holder_smooth a (fracD p w) (hcd.of_le (by exact_mod_cast le_top)) (-1) 1⟩


theorem c12m_aux_eta_smooth : ContDiff ℝ (⊤ : ℕ∞) c12_eta := by
  unfold c12_eta
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem c12m_aux_eta_nonneg (x : ℝ) : 0 ≤ c12_eta x := Real.smoothTransition.nonneg _
theorem c12m_aux_eta_le_one (x : ℝ) : c12_eta x ≤ 1 := Real.smoothTransition.le_one _

theorem c12m_aux_eta_zero {x : ℝ} (hx : 7 / 8 ≤ |x|) : c12_eta x = 0 := by
  unfold c12_eta
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h : (7 / 8 : ℝ) ^ 2 ≤ x ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hx 2; rwa [sq_abs] at this
  rw [div_nonpos_iff]; right; constructor <;> nlinarith

theorem c12m_aux_eta_cs : HasCompactSupport c12_eta :=
  HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
    refine c12m_aux_eta_zero ?_
    have : 1 < |x| := by
      by_contra h; rw [not_lt] at h; exact hx (abs_le.1 h)
    linarith

theorem c12m_aux_eta_lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |c12_eta x - c12_eta y| ≤ L * |x - y| := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport c12m_aux_eta_cs
    c12m_aux_eta_smooth (by simp)
  exact ⟨C, C.2, fun x y => by
    have := hC.dist_le_mul x y; rwa [Real.dist_eq, Real.dist_eq] at this⟩

theorem c12m_aux_eta_diff_le (x y : ℝ) : |c12_eta x - c12_eta y| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [c12m_aux_eta_nonneg x, c12m_aux_eta_nonneg y,
    c12m_aux_eta_le_one x, c12m_aux_eta_le_one y]

/-- The `z = 0` convention is automatic for quotients by `|z|^{1+p}`. -/
theorem c12m_aux_ite_div (p : ℝ) (hp : 0 < p) (A : ℝ) (z : ℝ) :
    (if z = 0 then 0 else A / |z| ^ (1 + p)) = A / |z| ^ (1 + p) := by
  split_ifs with h
  · subst h; simp [Real.zero_rpow (by linarith : (1 + p) ≠ 0)]
  · rfl

/-- Change of variables `z ↦ x - z` in the singular integrand. -/
theorem c12m_aux_frac_sub (p : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    (fun z => (u x - u z) / |x - z| ^ (p + 1)) =
      fun z => (fun t => (u x - u (x - t)) / |t| ^ (1 + p)) (x - z) := by
  funext z; simp [add_comm p 1]

/-- The commutator integrand is integrable. -/
theorem c12m_aux_comm_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) {w : ℝ → ℝ}
    (hwc : Continuous w) {M : ℝ} (hM : ∀ x, |w x| ≤ M) (x : ℝ) :
    Integrable (fun z => (c12_eta x - c12_eta (x - z)) * w (x - z) / |z| ^ (1 + p)) := by
  obtain ⟨L, hL0, hL⟩ := c12m_aux_eta_lip
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hec : Continuous c12_eta := c12m_aux_eta_smooth.continuous
  refine (c03_aux_psi_integrable p (L * M) M hp hp1).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (((measurable_const.sub (hec.measurable.comp (measurable_const.sub measurable_id))).mul
      (hwc.measurable.comp (measurable_const.sub measurable_id))).div
      (continuous_abs.measurable.pow_const _)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), add_comm 1 p]
    refine c03_aux_psi_bound p hp (by positivity) hM0 z _ (fun _ => ?_) ?_
    · rw [abs_mul]
      calc |c12_eta x - c12_eta (x - z)| * |w (x - z)| ≤ (L * |z|) * M := by
            refine mul_le_mul ?_ (hM _) (abs_nonneg _) (by positivity)
            have := hL x (x - z); rwa [sub_sub_cancel] at this
        _ = L * M * |z| := by ring
    · rw [abs_mul]
      calc |c12_eta x - c12_eta (x - z)| * |w (x - z)| ≤ 1 * M :=
            mul_le_mul (c12m_aux_eta_diff_le _ _) (hM _) (abs_nonneg _) (by norm_num)
        _ = M := one_mul M

/-- Blueprint: lem:c12_commutator_identity.  For smooth bounded `w`, the integrals of
`|D|^p(η w)`, `|D|^p w` and `C_{η,p} w` converge absolutely and
`|D|^p(η w) = η |D|^p w + C_{η,p} w` at every point. -/
theorem c12_commutator_identity (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwb : ∃ M, ∀ x, |w x| ≤ M) (x : ℝ) :
    Integrable (fun z => (c12_eta x * w x - c12_eta z * w z) / |x - z| ^ (p + 1)) ∧
    Integrable (fun z => (w x - w z) / |x - z| ^ (p + 1)) ∧
    Integrable (fun z => if z = 0 then 0 else
      (c12_eta x - c12_eta (x - z)) * w (x - z) / |z| ^ (1 + p)) ∧
    fracD p (fun y => c12_eta y * w y) x = c12_eta x * fracD p w x + c12_commutator p w x := by
  obtain ⟨M, hM⟩ := hwb
  have hW := (c12_frac_local_finite p hp hp1 w hw ⟨M, hM⟩).1 x
  have hC := c12m_aux_comm_integrable p hp hp1 hw.continuous hM x
  have hite : (fun z => if z = 0 then 0 else
      (c12_eta x - c12_eta (x - z)) * w (x - z) / |z| ^ (1 + p)) =
      fun z => (c12_eta x - c12_eta (x - z)) * w (x - z) / |z| ^ (1 + p) :=
    funext fun z => c12m_aux_ite_div p hp _ z
  -- shifted forms
  set Gw : ℝ → ℝ := fun t => (w x - w (x - t)) / |t| ^ (1 + p) with hGw
  have hGwi : Integrable Gw := by
    have := hW.comp_sub_left x
    simpa [Gw, sub_sub_cancel, add_comm p 1] using this
  have hsplit : (fun t => (c12_eta x * w x - c12_eta (x - t) * w (x - t)) / |t| ^ (1 + p)) =
      fun t => c12_eta x * Gw t + (c12_eta x - c12_eta (x - t)) * w (x - t) / |t| ^ (1 + p) := by
    funext t; simp only [Gw]; ring
  have hGi : Integrable (fun t => (c12_eta x * w x - c12_eta (x - t) * w (x - t)) /
      |t| ^ (1 + p)) := by
    rw [hsplit]; exact (hGwi.const_mul _).add hC
  have e1 : ∫ z, (c12_eta x * w x - c12_eta z * w z) / |x - z| ^ (p + 1) =
      ∫ t, (c12_eta x * w x - c12_eta (x - t) * w (x - t)) / |t| ^ (1 + p) := by
    rw [← integral_sub_left_eq_self (fun t => (c12_eta x * w x - c12_eta (x - t) * w (x - t)) /
      |t| ^ (1 + p)) (μ := volume) x]
    congr 1; funext z; simp [add_comm p 1]
  have e2 : ∫ z, (w x - w z) / |x - z| ^ (p + 1) = ∫ t, Gw t := by
    rw [← integral_sub_left_eq_self Gw (μ := volume) x]
    congr 1; funext z; simp [Gw, add_comm p 1]
  refine ⟨?_, hW, by rw [hite]; exact hC, ?_⟩
  · have := hGi.comp_sub_left x
    simpa [sub_sub_cancel, add_comm p 1] using this
  · unfold fracD c12_commutator
    rw [e1, e2, hite, hsplit, integral_add (hGwi.const_mul _) hC, integral_const_mul]
    ring



theorem c12m_aux_param_iter {G : ℝ → ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => G q.1 q.2))
    (r : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => iteratedDeriv r (fun x => G x q.2) q.1) := by
  induction r with
  | zero => simpa using hG
  | succ r ih =>
    simp only [iteratedDeriv_succ]
    have hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry
        (fun (q : ℝ × ℝ) (x : ℝ) => iteratedDeriv r (fun x' => G x' q.2) x)) := by
      have : Function.uncurry (fun (q : ℝ × ℝ) (x : ℝ) => iteratedDeriv r (fun x' => G x' q.2) x) =
          (fun q : ℝ × ℝ => iteratedDeriv r (fun x => G x q.2) q.1) ∘
            (fun u : (ℝ × ℝ) × ℝ => (u.2, u.1.2)) := by
        funext u; rfl
      rw [this]; exact ih.comp (by fun_prop)
    exact hf.fderiv_apply (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (g := fun q : ℝ × ℝ => q.1)
      (k := fun _ => (1 : ℝ)) contDiff_fst contDiff_const (by simp)

theorem c12m_aux_normR_const_mul_univ {s : ℝ} (c : ℝ) {f : ℝ → ℝ} (hf : f ∈ c03_holder s univ) :
    (fun x => c * f x) ∈ c03_holder s univ ∧
      c03_holder_normR s univ (fun x => c * f x) ≤ |c| * c03_holder_normR s univ f := by
  set k := ⌊s⌋₊
  set I : Set ℝ := univ
  have heq : ∀ i x, iteratedDerivWithin i (fun x => c * f x) I x =
      c * iteratedDerivWithin i f I x := fun i x => by
    simp only [I, iteratedDerivWithin_univ]; exact iteratedDeriv_const_mul_field c f
  have hHf := c03_aux_semi_holder hf
  have hB : HolderOnWith (Real.toNNReal |c| * (c03_aux_semi s I f).toNNReal)
      (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ (fun x => c * f x) I) I := by
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [heq, heq, Real.dist_eq, ← mul_sub, abs_mul, ← Real.dist_eq]
    push_cast [Real.coe_toNNReal _ (abs_nonneg c)]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hHf.dist_le hx hy) (abs_nonneg c)
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I _ (contDiffOn_const.mul hf.1)
    (fun i => |c| * (c03_aux_supD i I f).toReal) (fun _ _ => by positivity)
    (fun i hi x hx => by
      rw [heq, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact c03_aux_le_supD hf hi hx)
        (abs_nonneg c)) _ hB
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hf, mul_add, Finset.mul_sum]
  push_cast [ENNReal.coe_toNNReal_eq_toReal, Real.coe_toNNReal _ (abs_nonneg c)]
  ring


/-- The scalar majorant `min(|z|,1) |z|^{-1-p}` is integrable. -/
theorem c12m_aux_min_int (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun z : ℝ => min |z| 1 / |z| ^ (1 + p)) := by
  refine (c03_aux_psi_integrable p 1 1 hp hp1).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (((continuous_abs : Continuous (fun z : ℝ => |z|)).min continuous_const).measurable.div
      (continuous_abs.measurable.pow_const _)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      add_comm 1 p]
    refine c03_aux_psi_bound p hp zero_le_one zero_le_one z _ (fun _ => ?_) ?_
    · rw [abs_of_nonneg (le_min (abs_nonneg _) zero_le_one), one_mul]; exact min_le_left _ _
    · rw [abs_of_nonneg (le_min (abs_nonneg _) zero_le_one)]; exact min_le_right _ _

/-- Blueprint: lem:c12_commutator_norm.  `N_a(C_{η,p} w) ≤ C_{p,a} N_a(w)` for smooth
`w ∈ C^a(ℝ)`. -/
theorem c12_commutator_norm (p a : ℝ) (hp : 0 < p) (hp1 : p < 1) (ha : 0 < a)
    (haN : ∀ n : ℕ, a ≠ n) :
    ∃ C, 0 < C ∧ ∀ w : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) w → w ∈ c03_holder a univ →
      c12_commutator p w ∈ c03_holder a univ ∧
      c03_holder_normR a univ (c12_commutator p w) ≤ C * c03_holder_normR a univ w := by
  obtain ⟨Cd, hCd, hdiff⟩ := c12_cutoff_difference a ha haN
  obtain ⟨Cp, hCp, hprod⟩ := c12_holder_product a ha haN
  set J := ∫ z : ℝ, min |z| 1 / |z| ^ (1 + p) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun z => by positivity
  refine ⟨((⌊a⌋₊ : ℝ) + 2) * (|calpha p| * Cp * Cd * J) + 1, by positivity, fun w hw hwa => ?_⟩
  set Nw := c03_holder_normR a univ w with hNw
  have hNw0 : 0 ≤ Nw := c03_aux_normR_nonneg a univ w
  set F : ℝ → ℝ → ℝ := fun x z => calpha p / |z| ^ (1 + p) *
    ((c12_eta x - c12_eta (x - z)) * w (x - z)) with hF
  set B : ℝ → ℝ := fun z => |calpha p| * Cp * Cd * Nw * (min |z| 1 / |z| ^ (1 + p)) with hB
  have hB0 : ∀ z, 0 ≤ B z := fun z => by simp only [B]; positivity
  have hBi : Integrable B := (c12m_aux_min_int p hp hp1).const_mul _
  have hsec : ∀ z, (fun x => F x z) ∈ c03_holder a univ ∧
      c03_holder_normR a univ (fun x => F x z) ≤ B z := by
    intro z
    obtain ⟨hd, hdn⟩ := hdiff z
    obtain ⟨ht, htn, -⟩ := c12_holder_translation a ha haN z w hwa
    obtain ⟨hm, hmn⟩ := hprod _ _ hd ht
    obtain ⟨hc, hcn⟩ := c12m_aux_normR_const_mul_univ (calpha p / |z| ^ (1 + p)) hm
    refine ⟨hc, hcn.trans ?_⟩
    have hd0 := c03_aux_normR_nonneg a univ (fun x => c12_eta x - c12_eta (x - z))
    rw [htn] at hmn
    have habs : |calpha p / |z| ^ (1 + p)| = |calpha p| / |z| ^ (1 + p) := by
      rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rw [habs]
    calc |calpha p| / |z| ^ (1 + p) * c03_holder_normR a univ
          (fun x => (c12_eta x - c12_eta (x - z)) * w (x - z))
        ≤ |calpha p| / |z| ^ (1 + p) * (Cp * (Cd * min |z| 1) * Nw) := by
          gcongr
          exact hmn.trans (by gcongr)
      _ = B z := by simp only [B]; ring
  have hmeas : ∀ r ≤ ⌊a⌋₊,
      Measurable (fun q : ℝ × ℝ => iteratedDeriv r (fun x => F x q.2) q.1) := by
    intro r _
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ =>
        (c12_eta q.1 - c12_eta (q.1 - q.2)) * w (q.1 - q.2)) :=
      (c12m_aux_eta_smooth.comp contDiff_fst |>.sub
        (c12m_aux_eta_smooth.comp (contDiff_fst.sub contDiff_snd))).mul
        (hw.comp (contDiff_fst.sub contDiff_snd))
    have hit := c12m_aux_param_iter (G := fun x z => (c12_eta x - c12_eta (x - z)) * w (x - z))
      hG r
    have heq : (fun q : ℝ × ℝ => iteratedDeriv r (fun x => F x q.2) q.1) =
        fun q => calpha p / |q.2| ^ (1 + p) *
          iteratedDeriv r (fun x => (c12_eta x - c12_eta (x - q.2)) * w (x - q.2)) q.1 := by
      funext q; simp only [F]; exact iteratedDeriv_const_mul_field _ _
    rw [heq]
    have h0 : Measurable (fun z : ℝ => calpha p / |z| ^ (1 + p)) :=
      Measurable.div (f := fun _ : ℝ => calpha p) (g := fun z : ℝ => |z| ^ (1 + p))
        measurable_const (continuous_abs.measurable.pow_const _)
    have h1 : Measurable (fun q : ℝ × ℝ => calpha p / |q.2| ^ (1 + p)) :=
      h0.comp measurable_snd
    exact h1.mul hit.continuous.measurable
  obtain ⟨-, hU, hUn, -⟩ := c12_holder_integral a ha haN F B hB0 hBi (fun z => (hsec z).1)
    (fun z => (hsec z).2) hmeas
  have hcomm : c12_commutator p w = fun x => ∫ z, F x z := by
    funext x
    unfold c12_commutator
    rw [← integral_const_mul]
    congr 1; funext z
    rw [c12m_aux_ite_div p hp]
    simp only [F]; ring
  have hIB : ∫ z, B z = |calpha p| * Cp * Cd * J * Nw := by
    simp only [B, J]; rw [integral_const_mul]; ring
  rw [hcomm]
  refine ⟨hU, hUn.trans ?_⟩
  rw [hIB]
  nlinarith

/-- Triangle inequality for the global `C^s(ℝ)` norm. -/
theorem c12m_aux_normR_add_le_univ {s : ℝ} {f g : ℝ → ℝ}
    (hf : f ∈ c03_holder s univ) (hg : g ∈ c03_holder s univ) :
    (fun x => f x + g x) ∈ c03_holder s univ ∧
      c03_holder_normR s univ (fun x => f x + g x) ≤
        c03_holder_normR s univ f + c03_holder_normR s univ g := by
  set k := ⌊s⌋₊
  set I : Set ℝ := univ
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_univ
  have heq : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i (fun x => f x + g x) I x =
      iteratedDerivWithin i f I x + iteratedDerivWithin i g I x := fun i hi x hx =>
    iteratedDerivWithin_add hx hU ((hf.1.of_le (by exact_mod_cast hi)) x hx)
      ((hg.1.of_le (by exact_mod_cast hi)) x hx)
  have hHf := c03_aux_semi_holder hf
  have hHg := c03_aux_semi_holder hg
  have hB : HolderOnWith ((c03_aux_semi s I f).toNNReal + (c03_aux_semi s I g).toNNReal)
      (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ (fun x => f x + g x) I) I := by
    intro x hx y hy
    rw [heq k le_rfl x hx, heq k le_rfl y hy]
    refine (edist_add_add_le _ _ _ _).trans ?_
    rw [ENNReal.coe_add, add_mul]
    exact add_le_add (hHf x hx y hy) (hHg x hx y hy)
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I _ (hf.1.add hg.1)
    (fun i => (c03_aux_supD i I f).toReal + (c03_aux_supD i I g).toReal)
    (fun _ _ => by positivity)
    (fun i hi x hx => by
      rw [heq i hi x hx]
      exact (norm_add_le _ _).trans (add_le_add (c03_aux_le_supD hf hi hx)
        (c03_aux_le_supD hg hi hx))) _ hB
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hf, c03_aux_normR_eq hg, Finset.sum_add_distrib]
  push_cast [ENNReal.coe_toNNReal_eq_toReal]
  ring

/-- Blueprint: lem:c12_localized_rhs.  For smooth `w ∈ C^β(ℝ)`, `v = η w` is smooth with compact
support, `h = |D|^p v ∈ C^β(ℝ)` with `N_β(h) ≤ C (N_β(w) + N_β(|D|^p w; [-1,1]))`, and
`‖v‖_∞ ≤ N_β(w)`. -/
theorem c12_localized_rhs (p β : ℝ) (hp : 0 < p) (hp1 : p < 1) (hβ : 0 < β)
    (hβN : ∀ n : ℕ, β ≠ n) :
    ∃ C, 0 < C ∧ ∀ w : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) w → w ∈ c03_holder β univ →
      ContDiff ℝ (⊤ : ℕ∞) (fun x => c12_eta x * w x) ∧
      HasCompactSupport (fun x => c12_eta x * w x) ∧
      fracD p (fun x => c12_eta x * w x) ∈ c03_holder β univ ∧
      c03_holder_normR β univ (fracD p (fun x => c12_eta x * w x)) ≤
        C * (c03_holder_normR β univ w + c03_holder_normR β (Icc (-1) 1) (fracD p w)) ∧
      ∀ x, |c12_eta x * w x| ≤ c03_holder_normR β univ w := by
  obtain ⟨C1, hC1, hext⟩ := c12_cutoff_extension β hβ hβN
  obtain ⟨C2, hC2, hcomm⟩ := c12_commutator_norm p β hp hp1 hβ hβN
  refine ⟨C1 + C2, by positivity, fun w hw hwβ => ?_⟩
  have hwb : ∀ x, |w x| ≤ c03_holder_normR β univ w := fun x => by
    have := c03_aux_le_normR hwβ (Nat.zero_le _) (mem_univ x)
    rwa [iteratedDerivWithin_zero, Real.norm_eq_abs] at this
  have hloc := (c12_frac_local_finite p hp hp1 w hw ⟨_, hwb⟩).2.2 β hβ hβN
  obtain ⟨hE, hEn⟩ := hext (fracD p w) hloc
  obtain ⟨hCm, hCn⟩ := hcomm w hw hwβ
  have hid : fracD p (fun x => c12_eta x * w x) =
      fun x => c12_eta x * fracD p w x + c12_commutator p w x :=
    funext fun x => (c12_commutator_identity p hp hp1 w hw ⟨_, hwb⟩ x).2.2.2
  obtain ⟨hS, hSn⟩ := c12m_aux_normR_add_le_univ hE hCm
  have hn1 := c03_aux_normR_nonneg β univ w
  have hn2 := c03_aux_normR_nonneg β (Icc (-1 : ℝ) 1) (fracD p w)
  refine ⟨c12m_aux_eta_smooth.mul hw, c12m_aux_eta_cs.mul_right, by rw [hid]; exact hS, ?_,
    fun x => ?_⟩
  · rw [hid]
    calc _ ≤ _ := hSn
      _ ≤ C1 * c03_holder_normR β (Icc (-1) 1) (fracD p w) + C2 * c03_holder_normR β univ w :=
          add_le_add hEn hCn
      _ ≤ (C1 + C2) * (c03_holder_normR β univ w + c03_holder_normR β (Icc (-1) 1) (fracD p w)) := by
          nlinarith
  · rw [abs_mul, abs_of_nonneg (c12m_aux_eta_nonneg x)]
    calc c12_eta x * |w x| ≤ 1 * |w x| :=
          mul_le_mul_of_nonneg_right (c12m_aux_eta_le_one x) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hwb x

end GSQG
