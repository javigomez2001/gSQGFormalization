import GSQG.SchauderEstimate.Setup

/-!
# Beyond the paper (Schauder estimate cited in §4): global Hölder transport — translation,
products, parameter integration, cutoff difference and extension (blueprint ch. 12).
Helpers `c12h_aux_*`.

Notation: `N_a(u) = c03_holder_normR a univ u` (global norm; within-`univ` derivatives are the
ordinary derivatives) and `N_a(u; I) = c03_holder_normR a I u`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

section Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Global criterion: bounds on the ordinary derivatives and a Hölder bound on the top one. -/
theorem c12h_aux_global_of_bounds (a : ℝ) (g : ℝ → E) (hg : ContDiff ℝ ⌊a⌋₊ g)
    (A : ℕ → ℝ) (hA0 : ∀ i ≤ ⌊a⌋₊, 0 ≤ A i)
    (hA : ∀ i ≤ ⌊a⌋₊, ∀ x, ‖iteratedDeriv i g x‖ ≤ A i) (B : ℝ≥0)
    (hB : ∀ x y, dist (iteratedDeriv ⌊a⌋₊ g x) (iteratedDeriv ⌊a⌋₊ g y) ≤
      B * dist x y ^ ((Real.toNNReal (a - ⌊a⌋₊) : ℝ≥0) : ℝ)) :
    g ∈ c03_holder a univ ∧
      c03_holder_normR a univ g ≤ ∑ i ∈ Finset.range (⌊a⌋₊ + 1), A i + B := by
  refine c03_aux_normR_le a univ g hg.contDiffOn A hA0 (fun i hi x _ => ?_) B ?_
  · rw [iteratedDerivWithin_univ]; exact hA i hi x
  · rw [iteratedDerivWithin_univ]
    exact c03_aux_holderOnWith_of_dist fun x _ y _ => hB x y

theorem c12h_aux_contDiff {a : ℝ} {u : ℝ → E} (hu : u ∈ c03_holder a univ) :
    ContDiff ℝ ⌊a⌋₊ u := contDiffOn_univ.1 hu.1

theorem c12h_aux_le_normR {a : ℝ} {u : ℝ → E} (hu : u ∈ c03_holder a univ) {i : ℕ}
    (hi : i ≤ ⌊a⌋₊) (x : ℝ) : ‖iteratedDeriv i u x‖ ≤ c03_holder_normR a univ u := by
  have := c03_aux_le_normR hu hi (mem_univ x)
  rwa [iteratedDerivWithin_univ] at this

theorem c12h_aux_supD_le {a : ℝ} {u : ℝ → E} (hu : u ∈ c03_holder a univ) {i : ℕ}
    (hi : i ≤ ⌊a⌋₊) (x : ℝ) : ‖iteratedDeriv i u x‖ ≤ (c03_aux_supD i univ u).toReal := by
  have := c03_aux_le_supD hu hi (mem_univ x)
  rwa [iteratedDerivWithin_univ] at this

theorem c12h_aux_semi {a : ℝ} {u : ℝ → E} (hu : u ∈ c03_holder a univ) (x y : ℝ) :
    dist (iteratedDeriv ⌊a⌋₊ u x) (iteratedDeriv ⌊a⌋₊ u y) ≤
      (c03_aux_semi a univ u).toNNReal * dist x y ^ ((Real.toNNReal (a - ⌊a⌋₊) : ℝ≥0) : ℝ) := by
  have := (c03_aux_semi_holder hu).dist_le (mem_univ x) (mem_univ y)
  rwa [iteratedDerivWithin_univ] at this

theorem c12h_aux_normR_eq {a : ℝ} {u : ℝ → E} (hu : u ∈ c03_holder a univ) :
    c03_holder_normR a univ u = ∑ i ∈ Finset.range (⌊a⌋₊ + 1), (c03_aux_supD i univ u).toReal +
      ((c03_aux_semi a univ u).toNNReal : ℝ) := by
  rw [c03_aux_normR_eq hu, ENNReal.coe_toNNReal_eq_toReal]

theorem c12h_aux_translate_le {a : ℝ} (t : ℝ) {u : ℝ → E} (hu : u ∈ c03_holder a univ) :
    (fun x => u (x - t)) ∈ c03_holder a univ ∧
      c03_holder_normR a univ (fun x => u (x - t)) ≤ c03_holder_normR a univ u := by
  have hc := c12h_aux_contDiff hu
  have hd : ∀ i x, iteratedDeriv i (fun x => u (x - t)) x = iteratedDeriv i u (x - t) :=
    fun i x => by rw [iteratedDeriv_comp_sub_const]
  obtain ⟨hm, hle⟩ := c12h_aux_global_of_bounds a (fun x => u (x - t))
    (hc.comp (contDiff_id.sub contDiff_const))
    (fun i => (c03_aux_supD i univ u).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i hi x => by rw [hd]; exact c12h_aux_supD_le hu hi _)
    (c03_aux_semi a univ u).toNNReal
    (fun x y => by
      rw [hd, hd]
      have := c12h_aux_semi hu (x - t) (y - t)
      rwa [dist_sub_right] at this)
  exact ⟨hm, hle.trans (c12h_aux_normR_eq hu).ge⟩

theorem c12h_aux_restrict {a : ℝ} {u : ℝ → E} (hu : u ∈ c03_holder a univ) {b c : ℝ}
    (hbc : b < c) :
    u ∈ c03_holder a (Icc b c) ∧ c03_holder_normR a (Icc b c) u ≤ c03_holder_normR a univ u := by
  have hc := c12h_aux_contDiff hu
  have hU : UniqueDiffOn ℝ (Icc b c) := uniqueDiffOn_Icc hbc
  have heq : ∀ i ≤ ⌊a⌋₊, ∀ x ∈ Icc b c,
      iteratedDerivWithin i u (Icc b c) x = iteratedDeriv i u x := fun i hi x hx =>
    iteratedDerivWithin_eq_iteratedDeriv hU ((hc.of_le (by exact_mod_cast hi)).contDiffAt) hx
  obtain ⟨hm, hle⟩ := c03_aux_normR_le a (Icc b c) u hc.contDiffOn
    (fun i => (c03_aux_supD i univ u).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i hi x hx => by rw [heq i hi x hx]; exact c12h_aux_supD_le hu hi x)
    (c03_aux_semi a univ u).toNNReal
    (c03_aux_holderOnWith_of_dist fun x hx y hy => by
      rw [heq _ le_rfl x hx, heq _ le_rfl y hy]; exact c12h_aux_semi hu x y)
  exact ⟨hm, hle.trans (c12h_aux_normR_eq hu).ge⟩

end Aux

/-- Exhaustion of the line by the intervals `[-R,R]`, `R ≥ 1`. -/
theorem c12h_aux_global_of_intervals {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (g : ℝ → E) (hg : ContDiff ℝ ⌊a⌋₊ g) (M : ℝ) (hM : 0 ≤ M)
    (hI : ∀ R : ℝ, 1 ≤ R → g ∈ c03_holder a (Icc (-R) R) ∧ c03_holder_normR a (Icc (-R) R) g ≤ M) :
    g ∈ c03_holder a univ ∧ c03_holder_normR a univ g ≤ ((⌊a⌋₊ : ℝ) + 2) * M := by
  have heq : ∀ R : ℝ, 1 ≤ R → ∀ i ≤ ⌊a⌋₊, ∀ x ∈ Icc (-R) R,
      iteratedDerivWithin i g (Icc (-R) R) x = iteratedDeriv i g x := fun R hR i hi x hx =>
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
      ((hg.of_le (by exact_mod_cast hi)).contDiffAt) hx
  obtain ⟨hm, hle⟩ := c12h_aux_global_of_bounds a g hg (fun _ => M) (fun _ _ => hM)
    (fun i hi x => by
      have hR : (1 : ℝ) ≤ |x| + 1 := by linarith [abs_nonneg x]
      have hx : x ∈ Icc (-(|x| + 1)) (|x| + 1) :=
        ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      rw [← heq _ hR i hi x hx]
      exact (c03_aux_le_normR (hI _ hR).1 hi hx).trans (hI _ hR).2)
    M.toNNReal
    (fun x y => by
      set R := |x| + |y| + 1
      have hR : (1 : ℝ) ≤ R := by linarith [abs_nonneg x, abs_nonneg y]
      have hx : x ∈ Icc (-R) R := ⟨by linarith [neg_abs_le x, abs_nonneg y],
        by linarith [le_abs_self x, abs_nonneg y]⟩
      have hy : y ∈ Icc (-R) R := ⟨by linarith [neg_abs_le y, abs_nonneg x],
        by linarith [le_abs_self y, abs_nonneg x]⟩
      rw [← heq _ hR _ le_rfl x hx, ← heq _ hR _ le_rfl y hy]
      refine ((c03_aux_semi_holder (hI R hR).1).dist_le hx hy).trans
        (mul_le_mul_of_nonneg_right ?_ (by positivity))
      rw [ENNReal.coe_toNNReal_eq_toReal, Real.coe_toNNReal _ hM]
      exact (c03_aux_semi_le_normR (hI R hR).1).trans (hI R hR).2)
  refine ⟨hm, hle.trans (le_of_eq ?_)⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.coe_toNNReal _ hM]
  push_cast; ring

/-- Real functions on an interval, viewed as complex functions. -/
theorem c12h_aux_ofReal {s b c : ℝ} (hbc : b < c) {g : ℝ → ℝ} (hg : g ∈ c03_holder s (Icc b c)) :
    (fun x => (g x : ℂ)) ∈ c03_holder s (Icc b c) ∧
      c03_holder_normR s (Icc b c) (fun x => (g x : ℂ)) ≤ c03_holder_normR s (Icc b c) g ∧
      c03_holder_supNorm (Icc b c) (fun x => (g x : ℂ)) ≤ c03_holder_supNorm (Icc b c) g :=
  c03_aux_holder_clm_norm hbc Complex.ofRealCLM Complex.ofRealCLM_norm.le hg

theorem c12h_aux_re {s b c : ℝ} (hbc : b < c) {G : ℝ → ℂ} (hG : G ∈ c03_holder s (Icc b c)) :
    (fun x => (G x).re) ∈ c03_holder s (Icc b c) ∧
      c03_holder_normR s (Icc b c) (fun x => (G x).re) ≤ c03_holder_normR s (Icc b c) G :=
  let h := c03_aux_holder_clm_norm hbc Complex.reCLM Complex.reCLM_norm.le hG
  ⟨h.1, h.2.1⟩

/-- Interval product bound for real functions (from the complex `c03_holder_product_tame`). -/
theorem c12h_aux_product_Icc (a : ℝ) (ha : 0 < a) (haN : ∀ n : ℕ, a ≠ n) :
    ∃ C, 0 < C ∧ ∀ b c : ℝ, 1 ≤ c - b → ∀ u v : ℝ → ℝ,
      u ∈ c03_holder a (Icc b c) → v ∈ c03_holder a (Icc b c) →
      (fun x => u x * v x) ∈ c03_holder a (Icc b c) ∧
      c03_holder_normR a (Icc b c) (fun x => u x * v x) ≤
        C * (c03_holder_supNorm (Icc b c) u * c03_holder_normR a (Icc b c) v +
          c03_holder_supNorm (Icc b c) v * c03_holder_normR a (Icc b c) u) := by
  obtain ⟨C, hC, hP⟩ := c03_holder_product_tame a ha haN
  refine ⟨C, hC, fun b c hbc u v hu hv => ?_⟩
  have hbc' : b < c := by linarith
  obtain ⟨hU, hUn, hUs⟩ := c12h_aux_ofReal hbc' hu
  obtain ⟨hV, hVn, hVs⟩ := c12h_aux_ofReal hbc' hv
  obtain ⟨hUV, hUVn⟩ := hP b c hbc _ _ hU hV
  obtain ⟨hre, hren⟩ := c12h_aux_re hbc' hUV
  have hfun : (fun x => (((fun x => (u x : ℂ)) * (fun x => (v x : ℂ))) x).re) =
      fun x => u x * v x := by
    funext x; simp
  rw [hfun] at hre hren
  refine ⟨hre, hren.trans (hUVn.trans (mul_le_mul_of_nonneg_left ?_ hC.le))⟩
  have h0 := c03_aux_supNorm_nonneg (Icc b c) (fun x => (u x : ℂ))
  have h1 := c03_aux_supNorm_nonneg (Icc b c) (fun x => (v x : ℂ))
  have h2 := c03_aux_normR_nonneg a (Icc b c) (fun x => (u x : ℂ))
  have h3 := c03_aux_normR_nonneg a (Icc b c) (fun x => (v x : ℂ))
  have h4 := c03_aux_supNorm_nonneg (Icc b c) u
  have h5 := c03_aux_supNorm_nonneg (Icc b c) v
  gcongr


/-- Blueprint: lem:c12_holder_translation.  Global translation invariance and restriction to a
nondegenerate compact interval. -/
theorem c12_holder_translation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (_ha : 0 < a) (_haN : ∀ n : ℕ, a ≠ n) (t : ℝ) (u : ℝ → E)
    (hu : u ∈ c03_holder a univ) :
    (fun x => u (x - t)) ∈ c03_holder a univ ∧
      c03_holder_normR a univ (fun x => u (x - t)) = c03_holder_normR a univ u ∧
      ∀ b c : ℝ, b < c →
        u ∈ c03_holder a (Icc b c) ∧ c03_holder_normR a (Icc b c) u ≤ c03_holder_normR a univ u := by
  obtain ⟨hm, hle⟩ := c12h_aux_translate_le t hu
  obtain ⟨-, hle'⟩ := c12h_aux_translate_le (-t) hm
  have hback : (fun x => (fun x => u (x - t)) (x - -t)) = u := by
    funext x; simp
  rw [hback] at hle'
  exact ⟨hm, le_antisymm hle hle', fun b c hbc => c12h_aux_restrict hu hbc⟩

/-- Blueprint: lem:c12_holder_product.  Global product bound. -/
theorem c12_holder_product (a : ℝ) (ha : 0 < a) (haN : ∀ n : ℕ, a ≠ n) :
    ∃ C, 0 < C ∧ ∀ u v : ℝ → ℝ, u ∈ c03_holder a univ → v ∈ c03_holder a univ →
      (fun x => u x * v x) ∈ c03_holder a univ ∧
      c03_holder_normR a univ (fun x => u x * v x) ≤
        C * c03_holder_normR a univ u * c03_holder_normR a univ v := by
  obtain ⟨C, hC, hP⟩ := c12h_aux_product_Icc a ha haN
  refine ⟨((⌊a⌋₊ : ℝ) + 2) * (2 * C), by positivity, fun u v hu hv => ?_⟩
  have hNu := c03_aux_normR_nonneg a univ u
  have hNv := c03_aux_normR_nonneg a univ v
  obtain ⟨hm, hle⟩ := c12h_aux_global_of_intervals a (fun x => u x * v x)
    ((c12h_aux_contDiff hu).mul (c12h_aux_contDiff hv))
    (2 * C * c03_holder_normR a univ u * c03_holder_normR a univ v) (by positivity)
    (fun R hR => by
      have hRR : 1 ≤ R - -R := by linarith
      have hR' : -R < R := by linarith
      obtain ⟨hu1, hu2⟩ := c12h_aux_restrict hu hR'
      obtain ⟨hv1, hv2⟩ := c12h_aux_restrict hv hR'
      obtain ⟨hm, hle⟩ := hP (-R) R hRR u v hu1 hv1
      refine ⟨hm, hle.trans ?_⟩
      have hsu := (c03_aux_supNorm_le_normR hu1).trans hu2
      have hsv := (c03_aux_supNorm_le_normR hv1).trans hv2
      have h0 := c03_aux_supNorm_nonneg (Icc (-R) R) u
      have h1 := c03_aux_supNorm_nonneg (Icc (-R) R) v
      have h2 := c03_aux_normR_nonneg a (Icc (-R) R) u
      have h3 := c03_aux_normR_nonneg a (Icc (-R) R) v
      calc C * (c03_holder_supNorm (Icc (-R) R) u * c03_holder_normR a (Icc (-R) R) v +
            c03_holder_supNorm (Icc (-R) R) v * c03_holder_normR a (Icc (-R) R) u)
          ≤ C * (c03_holder_normR a univ u * c03_holder_normR a univ v +
            c03_holder_normR a univ v * c03_holder_normR a univ u) := by gcongr
        _ = _ := by ring)
  exact ⟨hm, hle.trans (le_of_eq (by ring))⟩

/-- Blueprint: lem:c12_holder_integral.  Parameter integration with an integrable majorant of
the global Hölder norms of the sections; derivatives commute with the integral. -/
theorem c12_holder_integral (a : ℝ) (_ha : 0 < a) (_haN : ∀ n : ℕ, a ≠ n)
    (F : ℝ → ℝ → ℝ) (B : ℝ → ℝ) (hB0 : ∀ t, 0 ≤ B t) (hBi : Integrable B)
    (hF : ∀ t, (fun x => F x t) ∈ c03_holder a univ)
    (hFB : ∀ t, c03_holder_normR a univ (fun x => F x t) ≤ B t)
    (hmeas : ∀ r ≤ ⌊a⌋₊,
      Measurable (fun q : ℝ × ℝ => iteratedDeriv r (fun x => F x q.2) q.1)) :
    (∀ x, Integrable (fun t => F x t)) ∧
      (fun x => ∫ t, F x t) ∈ c03_holder a univ ∧
      c03_holder_normR a univ (fun x => ∫ t, F x t) ≤ ((⌊a⌋₊ : ℝ) + 2) * ∫ t, B t ∧
      ∀ r ≤ ⌊a⌋₊, ∀ x, Integrable (fun t => iteratedDeriv r (fun y => F y t) x) ∧
        iteratedDeriv r (fun y => ∫ t, F y t) x = ∫ t, iteratedDeriv r (fun y => F y t) x := by
  set k := ⌊a⌋₊ with hk
  set D : ℕ → ℝ → ℝ → ℝ := fun r x t => iteratedDeriv r (fun y => F y t) x with hD
  have hcd : ∀ t, ContDiff ℝ k (fun x => F x t) := fun t => c12h_aux_contDiff (hF t)
  have hbd : ∀ r ≤ k, ∀ x t, ‖D r x t‖ ≤ B t := fun r hr x t =>
    (c12h_aux_le_normR (hF t) hr x).trans (hFB t)
  have hsm : ∀ r ≤ k, ∀ x, AEStronglyMeasurable (fun t => D r x t) volume := fun r hr x =>
    ((hmeas r hr).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hint : ∀ r ≤ k, ∀ x, Integrable (fun t => D r x t) := fun r hr x =>
    hBi.mono' (hsm r hr x) (ae_of_all _ fun t => hbd r hr x t)
  have hD0 : ∀ x t, D 0 x t = F x t := fun x t => by simp [hD]
  -- derivative of the parameter integral
  have hderiv : ∀ r, r + 1 ≤ k → ∀ x₀,
      HasDerivAt (fun x => ∫ t, D r x t) (∫ t, D (r + 1) x₀ t) x₀ := by
    intro r hr x₀
    have hr' : r ≤ k := by omega
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := B) (F' := fun x t => D (r + 1) x t)
      univ_mem (Eventually.of_forall fun x => hsm r hr' x) (hint r hr' x₀) (hsm (r + 1) hr x₀)
      (ae_of_all _ fun t x _ => hbd (r + 1) hr x t) hBi
      (ae_of_all _ fun t x _ => ?_)).2
    have hdif := (hcd t).differentiable_iteratedDeriv r (by exact_mod_cast (show r < k by omega))
    have := (hdif x).hasDerivAt
    simp only [hD]
    rwa [iteratedDeriv_succ]
  have hid : ∀ r ≤ k, ∀ x, iteratedDeriv r (fun y => ∫ t, F y t) x = ∫ t, D r x t := by
    intro r
    induction r with
    | zero => intro _ x; simp [hD]
    | succ r ih =>
      intro hr x
      have hfun : iteratedDeriv r (fun y => ∫ t, F y t) = fun x => ∫ t, D r x t :=
        funext (ih (by omega))
      rw [iteratedDeriv_succ, hfun]
      exact (hderiv r hr x).deriv
  have hcont : ∀ r ≤ k, Continuous (fun x => ∫ t, D r x t) := fun r hr =>
    continuous_of_dominated (fun x => hsm r hr x) (fun x => ae_of_all _ fun t => hbd r hr x t) hBi
      (ae_of_all _ fun t => (hcd t).continuous_iteratedDeriv r (by exact_mod_cast hr))
  have hUcd : ContDiff ℝ k (fun x => ∫ t, F x t) := by
    rw [show ((k : ℕ) : WithTop ℕ∞) = ((k : ℕ∞) : WithTop ℕ∞) from rfl, contDiff_iff_iteratedDeriv]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m ≤ k := by exact_mod_cast hm
      rw [funext (hid m hm')]; exact hcont m hm'
    · have hm' : m + 1 ≤ k := by
        have : m < k := by exact_mod_cast hm
        omega
      rw [funext (hid m (by omega))]
      exact fun x => (hderiv m hm' x).differentiableAt
  have hIB : 0 ≤ ∫ t, B t := integral_nonneg hB0
  obtain ⟨hmem, hle⟩ := c12h_aux_global_of_bounds a (fun x => ∫ t, F x t) hUcd
    (fun _ => ∫ t, B t) (fun _ _ => hIB)
    (fun i hi x => by
      rw [hid i hi x]
      exact norm_integral_le_of_norm_le hBi (ae_of_all _ fun t => hbd i hi x t))
    (∫ t, B t).toNNReal
    (fun x y => by
      rw [hid k le_rfl x, hid k le_rfl y, dist_eq_norm, ← integral_sub (hint k le_rfl x)
        (hint k le_rfl y), Real.coe_toNNReal _ hIB, ← integral_mul_const]
      refine norm_integral_le_of_norm_le (hBi.mul_const _) (ae_of_all _ fun t => ?_)
      rw [← dist_eq_norm]
      refine (c12h_aux_semi (hF t) x y).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      rw [ENNReal.coe_toNNReal_eq_toReal]
      exact (c03_aux_semi_le_normR (hF t)).trans (hFB t))
  refine ⟨fun x => by simpa [hD0] using hint 0 (Nat.zero_le _) x, hmem, ?_, fun r hr x =>
    ⟨hint r hr x, hid r hr x⟩⟩
  refine hle.trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.coe_toNNReal _ hIB]
  push_cast; ring

/-- Derivatives of a smooth compactly supported function are bounded. -/
theorem c12h_aux_deriv_bdd {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f)
    (i : ℕ) : ∃ M, 0 ≤ M ∧ ∀ x, ‖iteratedDeriv i f x‖ ≤ M := by
  have hcs : HasCompactSupport (iteratedDeriv i f) := by
    induction i with
    | zero => simpa using hs
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  obtain ⟨M, hM⟩ := (hf.continuous_iteratedDeriv i (by exact_mod_cast le_top)).bounded_above_of_compact_support hcs
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

/-- Mean value bound on the line. -/
theorem c12h_aux_mvt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C : ℝ} (hC : ∀ x, ‖deriv f x‖ ≤ C)
    (x y : ℝ) : ‖f x - f y‖ ≤ C * |x - y| := by
  have := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hf x) (fun x _ => hC x)
    (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- Global criterion from uniform bounds on the derivatives of order `≤ ⌊a⌋ + 1`. -/
theorem c12h_aux_global_of_derivs (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ (⌊a⌋₊ + 1) g) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ i ≤ ⌊a⌋₊ + 1, ∀ x, ‖iteratedDeriv i g x‖ ≤ A) :
    g ∈ c03_holder a univ ∧ c03_holder_normR a univ g ≤ ((⌊a⌋₊ : ℝ) + 3) * A := by
  set k := ⌊a⌋₊
  set θ : ℝ := ((Real.toNNReal (a - k) : ℝ≥0) : ℝ)
  have hθ0 : 0 ≤ θ := NNReal.coe_nonneg _
  have hθ1 : θ ≤ 1 := by exact_mod_cast c03_aux_theta_le a
  have hdiff : Differentiable ℝ (iteratedDeriv k g) :=
    hg.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
  have hlip : ∀ x y, ‖iteratedDeriv k g x - iteratedDeriv k g y‖ ≤ A * |x - y| :=
    c12h_aux_mvt hdiff (fun x => by rw [← iteratedDeriv_succ]; exact hA (k + 1) le_rfl x)
  obtain ⟨hm, hle⟩ := c12h_aux_global_of_bounds a g (hg.of_le (by exact_mod_cast Nat.le_succ k))
    (fun _ => A) (fun _ _ => hA0) (fun i hi x => hA i (by omega) x) (2 * A).toNNReal
    (fun x y => by
      rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, Real.dist_eq]
      rcases le_or_gt |x - y| 1 with hd | hd
      · refine (hlip x y).trans ?_
        have : |x - y| ≤ |x - y| ^ θ := by
          simpa using Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (x - y)) hd hθ0 hθ1
        nlinarith [Real.rpow_nonneg (abs_nonneg (x - y)) θ]
      · have h1 : 1 ≤ |x - y| ^ θ := Real.one_le_rpow hd.le hθ0
        have h2 : ‖iteratedDeriv k g x - iteratedDeriv k g y‖ ≤ 2 * A :=
          (norm_sub_le _ _).trans (by linarith [hA k (by omega) x, hA k (by omega) y])
        nlinarith)
  refine ⟨hm, hle.trans (le_of_eq ?_)⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.coe_toNNReal _ (by positivity)]
  push_cast; ring

/-- Blueprint: lem:c12_cutoff_difference.  `N_a(η - τ_z η) ≤ C_a min(|z|, 1)`. -/
theorem c12_cutoff_difference (a : ℝ) (_ha : 0 < a) (_haN : ∀ n : ℕ, a ≠ n) :
    ∃ C, 0 < C ∧ ∀ z : ℝ,
      (fun x => c12_eta x - c12_eta (x - z)) ∈ c03_holder a univ ∧
      c03_holder_normR a univ (fun x => c12_eta x - c12_eta (x - z)) ≤ C * min |z| 1 := by
  set k := ⌊a⌋₊
  obtain ⟨hsm, -, -, -, -, -, hcs⟩ := c12_cutoffs.1
  choose M hM0 hM using c12h_aux_deriv_bdd hsm hcs
  set S := ∑ i ∈ Finset.range (k + 3), M i
  have hS : ∀ i ≤ k + 2, M i ≤ S := fun i hi =>
    Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_range.2 (by omega))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hM0 j
  refine ⟨((k : ℝ) + 3) * (2 * S) + 1, by positivity, fun z => ?_⟩
  have hsmz : ContDiff ℝ (⊤ : ℕ∞) (fun x => c12_eta (x - z)) :=
    hsm.comp (contDiff_id.sub contDiff_const)
  have hd : ∀ i x, iteratedDeriv i (fun x => c12_eta x - c12_eta (x - z)) x =
      iteratedDeriv i c12_eta x - iteratedDeriv i c12_eta (x - z) := fun i x => by
    rw [iteratedDeriv_fun_sub (hsm.of_le (by exact_mod_cast le_top)).contDiffAt
      (hsmz.of_le (by exact_mod_cast le_top)).contDiffAt, iteratedDeriv_comp_sub_const]
  have hmin0 : 0 ≤ min |z| 1 := le_min (abs_nonneg z) zero_le_one
  obtain ⟨hm, hle⟩ := c12h_aux_global_of_derivs a (g := fun x => c12_eta x - c12_eta (x - z))
    ((hsm.sub hsmz).of_le (by exact_mod_cast le_top)) (A := 2 * S * min |z| 1) (by positivity)
    (fun i hi x => by
      rw [hd]
      have hdiff : Differentiable ℝ (iteratedDeriv i c12_eta) :=
        hsm.differentiable_iteratedDeriv i (by exact_mod_cast WithTop.coe_lt_top _)
      have h1 : ‖iteratedDeriv i c12_eta x - iteratedDeriv i c12_eta (x - z)‖ ≤ S * |z| := by
        have hi1 : i + 1 ≤ k + 2 := by omega
        have := c12h_aux_mvt hdiff (C := S)
          (fun y => by rw [← iteratedDeriv_succ]; exact (hM _ y).trans (hS _ hi1)) x (x - z)
        simpa using this
      have hi2 : i ≤ k + 2 := by omega
      have e1 := (hM i x).trans (hS i hi2)
      have e2 := (hM i (x - z)).trans (hS i hi2)
      have h2 : ‖iteratedDeriv i c12_eta x - iteratedDeriv i c12_eta (x - z)‖ ≤ 2 * S :=
        (norm_sub_le _ _).trans (by linarith)
      rcases le_or_gt |z| 1 with hz | hz
      · rw [min_eq_left hz]; nlinarith [abs_nonneg z]
      · rw [min_eq_right hz.le]; linarith)
  refine ⟨hm, hle.trans ?_⟩
  nlinarith

/-- Blueprint: lem:c12_cutoff_extension.  For `h ∈ C^a([-1,1])`, `η h` (which vanishes outside
`[-7/8,7/8]`, so it is the zero extension of `η h|_{[-1,1]}` and does not depend on the values of
`h` outside `[-1,1]`) is in `C^a(ℝ)` with `N_a(η h) ≤ C_a N_a(h; [-1,1])`. -/
-- Encoding: the zero extension is written as the global product `η h`; these agree since
-- `η = 0` outside `[-7/8,7/8]`, and the bound only involves `N_a(h; [-1,1])`.
theorem c12_cutoff_extension (a : ℝ) (ha : 0 < a) (haN : ∀ n : ℕ, a ≠ n) :
    ∃ C, 0 < C ∧ ∀ h : ℝ → ℝ, h ∈ c03_holder a (Icc (-1) 1) →
      (fun x => c12_eta x * h x) ∈ c03_holder a univ ∧
      c03_holder_normR a univ (fun x => c12_eta x * h x) ≤
        C * c03_holder_normR a (Icc (-1) 1) h := by
  set k := ⌊a⌋₊
  set I : Set ℝ := Icc (-1) 1
  obtain ⟨hsm, -, -, -, heta0, -, -⟩ := c12_cutoffs.1
  obtain ⟨C₁, hC₁, hP⟩ := c12h_aux_product_Icc a ha haN
  have hηI : c12_eta ∈ c03_holder a I :=
    c03_aux_holder_smooth a c12_eta (hsm.of_le (by exact_mod_cast le_top)) (-1) 1
  set Nη := c03_holder_normR a I c12_eta
  have hNη : 0 ≤ Nη := c03_aux_normR_nonneg _ _ _
  refine ⟨((k : ℝ) + 9) * (2 * C₁ * Nη) + 1, by positivity, fun h hh => ?_⟩
  set g : ℝ → ℝ := fun x => c12_eta x * h x
  set Nh := c03_holder_normR a I h
  have hNh : 0 ≤ Nh := c03_aux_normR_nonneg _ _ _
  -- the interval estimate
  obtain ⟨hgI, hgIn⟩ := hP (-1) 1 (by norm_num) c12_eta h hηI hh
  set NI := c03_holder_normR a I g
  have hNI0 : 0 ≤ NI := c03_aux_normR_nonneg _ _ _
  have hNI : NI ≤ 2 * C₁ * Nη * Nh := by
    refine hgIn.trans ?_
    have h1 := c03_aux_supNorm_le_normR hηI
    have h2 := c03_aux_supNorm_le_normR hh
    have h3 := c03_aux_supNorm_nonneg I c12_eta
    have h4 := c03_aux_supNorm_nonneg I h
    calc C₁ * (c03_holder_supNorm I c12_eta * Nh + c03_holder_supNorm I h * Nη)
        ≤ C₁ * (Nη * Nh + Nh * Nη) := by gcongr
      _ = _ := by ring
  -- vanishing near the complement of `[-7/8, 7/8]`
  have hzero : ∀ x : ℝ, 7 / 8 < |x| → g =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    have hopen : IsOpen {y : ℝ | 7 / 8 < |y|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp [g, heta0 y hy.le]
  have hIn : ∀ x : ℝ, |x| < 1 → I ∈ 𝓝 x := fun x hx =>
    Icc_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x])
  have hcd : ContDiff ℝ k g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge |x| 1 with hx | hx
    · exact ((hsm.of_le (by exact_mod_cast le_top)).contDiffAt).mul (hh.1.contDiffAt (hIn x hx))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x (by linarith))
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by norm_num)
  have heq : ∀ i ≤ k, ∀ x ∈ I, iteratedDeriv i g x = iteratedDerivWithin i g I x :=
    fun i hi x hx => (iteratedDerivWithin_eq_iteratedDeriv hU
      ((hcd.of_le (by exact_mod_cast hi)).contDiffAt) hx).symm
  have hout : ∀ i, ∀ x : ℝ, 7 / 8 < |x| → iteratedDeriv i g x = 0 := fun i x hx => by
    rw [(hzero x hx).iteratedDeriv_eq]; simp
  have hbd : ∀ i ≤ k, ∀ x, ‖iteratedDeriv i g x‖ ≤ NI := by
    intro i hi x
    by_cases hx : x ∈ I
    · rw [heq i hi x hx]; exact c03_aux_le_normR hgI hi hx
    · have : 1 < |x| := by
        by_contra hc; rw [not_lt] at hc; exact hx (abs_le.mp hc)
      rw [hout i x (by linarith)]; simpa using hNI0
  set θ : ℝ := ((Real.toNNReal (a - k) : ℝ≥0) : ℝ)
  have hθ0 : 0 ≤ θ := NNReal.coe_nonneg _
  have hθ1 : θ ≤ 1 := by exact_mod_cast c03_aux_theta_le a
  have hsemi : ∀ x ∈ I, ∀ y ∈ I, dist (iteratedDeriv k g x) (iteratedDeriv k g y) ≤
      NI * dist x y ^ θ := by
    intro x hx y hy
    rw [heq k le_rfl x hx, heq k le_rfl y hy]
    refine ((c03_aux_semi_holder hgI).dist_le hx hy).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    rw [ENNReal.coe_toNNReal_eq_toReal]; exact c03_aux_semi_le_normR hgI
  have hcross : ∀ x y, y ∉ I → dist (iteratedDeriv k g x) (iteratedDeriv k g y) ≤
      8 * NI * dist x y ^ θ := by
    intro x y hy
    have hy1 : 1 < |y| := by
      by_contra hc; rw [not_lt] at hc; exact hy (abs_le.mp hc)
    rw [hout k y (by linarith), dist_zero_right]
    rcases lt_or_ge (7 / 8 : ℝ) |x| with hx | hx
    · rw [hout k x hx, norm_zero]; positivity
    · have hxI : x ∈ I := abs_le.mp (by linarith)
      have hd : (1 / 8 : ℝ) ≤ dist x y := by
        rw [Real.dist_eq]
        have := abs_sub_abs_le_abs_sub y x
        rw [abs_sub_comm] at this; linarith
      have h1 : (1 / 8 : ℝ) ≤ (1 / 8 : ℝ) ^ θ := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' (by norm_num : (0:ℝ) ≤ 1 / 8)
          (by norm_num) hθ0 hθ1
      have h2 : (1 / 8 : ℝ) ^ θ ≤ dist x y ^ θ := Real.rpow_le_rpow (by norm_num) hd hθ0
      have h3 := hbd k le_rfl x
      nlinarith
  obtain ⟨hm, hle⟩ := c12h_aux_global_of_bounds a g hcd (fun _ => NI) (fun _ _ => hNI0) hbd
    (8 * NI).toNNReal
    (fun x y => by
      rw [Real.coe_toNNReal _ (by positivity)]
      by_cases hx : x ∈ I
      · by_cases hy : y ∈ I
        · refine (hsemi x hx y hy).trans ?_
          nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) θ]
        · exact hcross x y hy
      · rw [dist_comm, dist_comm x y]; exact hcross y x hx)
  refine ⟨hm, hle.trans ?_⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.coe_toNNReal _ (by positivity)]
  push_cast
  have : ((k : ℝ) + 1) * NI + 8 * NI = ((k : ℝ) + 9) * NI := by ring
  rw [this]
  calc ((k : ℝ) + 9) * NI ≤ ((k : ℝ) + 9) * (2 * C₁ * Nη * Nh) := by gcongr
    _ ≤ (((k : ℝ) + 9) * (2 * C₁ * Nη) + 1) * Nh := by nlinarith

end GSQG
