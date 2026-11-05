import GSQG.PatchEquation.Equivalence
import GSQG.PatchEquation.FourierNormalization
import GSQG.Sec3_FixedPoint.MainTheorem
import GSQG.Sec1_Introduction.GeometricFrontEquation

/-!
# Beyond the paper (2D patch derivation): admissibility of the self-similar family, time normalization,
Theorem 1.1 for canonical 2D patches (blueprint ch. 13)

Helpers are named `c13p_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### lem:c13_main_graph_admissible -/

/-- Profile bounds of thm:main give the global slope bound `|f'| ≤ C + 1`. -/
theorem c13p_aux_profile_slope (p C : ℝ) (hp : 0 < p) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : c01_profile_bounds_hold p C f) (y : ℝ) : |deriv f y| ≤ C + 1 := by
  have hC : 0 ≤ C := by
    have h := hb.2.1 0 le_rfl
    have : jb 0 ^ (-p) = 1 := by simp [jb]
    rw [this, mul_one] at h
    exact (abs_nonneg _).trans h
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  rcases le_total y 0 with hy | hy
  · have h := hb.1 y hy 1 (by norm_num)
    have hd : deriv (fun y' => f y' + y') y = deriv f y + 1 := by
      exact ((hfd y).hasDerivAt.add (hasDerivAt_id' y)).deriv.trans (by simp)
    rw [iteratedDeriv_one, hd] at h
    have hj : jb y ^ (-p - ((1 : ℕ) : ℝ)) ≤ 1 := by
      have := c01_aux_jb_rpow_neg_le_one y (p + 1) (by linarith)
      convert this using 2; push_cast; ring
    have h2 : |deriv f y + 1| ≤ C := h.trans (mul_le_of_le_one_right hC hj)
    calc |deriv f y| = |(deriv f y + 1) - 1| := by ring_nf
      _ ≤ |deriv f y + 1| + |(1:ℝ)| := abs_sub _ _
      _ ≤ C + 1 := by rw [abs_one]; linarith
  · have h := hb.2.2 y hy 0 (by norm_num)
    rw [zero_add, iteratedDeriv_one] at h
    have hβ : 0 ≤ beta p := by unfold beta; positivity
    have hj : jb y ^ (-beta p + ((0 : ℕ) : ℝ) / p) ≤ 1 := by
      simpa using c01_aux_jb_rpow_neg_le_one y (beta p) hβ
    linarith [mul_le_of_le_one_right hC hj]

/-- Blueprint: lem:c13_main_graph_admissible.  For every profile with the profile bounds of
thm:main (constant `C`), the graph `F = F_{ε,T}` is jointly smooth on `ℝ × (-∞,T)` with the
uniform slope bound `|F_x| ≤ √ε (C+1)`; no curvature bound is used. -/
theorem c13_main_graph_admissible (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (C ε T : ℝ)
    (hε : 0 < ε) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : c01_profile_bounds_hold p C f) :
    c13_graph_class (Iio T) (self_similar_ansatz p ε T f) ∧
    ∀ x t : ℝ, t < T →
      |deriv (fun x => self_similar_ansatz p ε T f x t) x| ≤ Real.sqrt ε * (C + 1) := by
  have hp0 : 0 < p := by linarith
  have hf1 : ContDiff ℝ 1 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hA := c01_ansatz_time_derivative p hp0 hp1 ε T hε f hf1
  have hslope : ∀ x t : ℝ, t < T →
      |deriv (fun x => self_similar_ansatz p ε T f x t) x| ≤ Real.sqrt ε * (C + 1) := by
    intro x t ht
    rw [(hA.2.1 x t ht).1, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (c13p_aux_profile_slope p C hp0 f hf1 hb _)
      (Real.sqrt_nonneg _)
  refine ⟨⟨isOpen_Iio, ⟨T - 1, by simp⟩, ?_, fun J₀ hJ _ => ⟨Real.sqrt ε * (C + 1), ?_,
    fun x t ht => hslope x t (hJ ht)⟩⟩, hslope⟩
  · exact contDiffOn_infty.mpr fun k =>
      (hA.2.2 k (hf.of_le (WithTop.coe_le_coe.mpr le_top))).1
  · exact (abs_nonneg _).trans (hslope 0 (T - 1) (by linarith))

/-! ### lem:c13_time_normalization -/

/-- Positivity of `c_front`, `c_std` and `κ` for `1 < α < 2`. -/
theorem c13p_aux_time_ratio_pos (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) :
    0 < calpha (α - 1) ∧ 0 < c13_standard_coefficient α ∧ 0 < c13_time_ratio α := by
  have h1 : 0 < calpha (α - 1) := by
    unfold calpha
    have hg : 0 < Real.Gamma (1 + (α - 1)) := Real.Gamma_pos_of_pos (by linarith)
    have hs : 0 < Real.sin (π * (α - 1) / 2) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := Real.pi_pos; have : 0 < α - 1 := by linarith
        positivity
      · have := Real.pi_pos; nlinarith
    have := Real.pi_pos
    positivity
  have h2 : 0 < c13_standard_coefficient α := by
    unfold c13_standard_coefficient c13_riesz_factor
    have hg1 : 0 < Real.Gamma (1 - α / 2) := Real.Gamma_pos_of_pos (by linarith)
    have hg2 : 0 < Real.Gamma (α / 2) := Real.Gamma_pos_of_pos (by linarith)
    have := Real.pi_pos
    have : 0 < (2 : ℝ) ^ (2 - α) := by positivity
    positivity
  exact ⟨h1, h2, div_pos h1 h2⟩

theorem c13p_aux_pt_norm (x u s v : ℝ) :
    ‖c13_pt x u - c13_pt s v‖ = Real.sqrt ((x - s) ^ 2 + (u - v) ^ 2) := by
  simp [c13_pt, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem c13p_aux_kernel_eq (α a x u s v : ℝ) :
    a * ‖c13_pt x u - c13_pt s v‖ ^ (-α) =
      a / ((x - s) ^ 2 + (u - v) ^ 2) ^ (α / 2) := by
  rw [c13p_aux_pt_norm, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
    show 1 / 2 * -α = -(α / 2) by ring, Real.rpow_neg (by positivity)]
  exact (div_eq_mul_inv _ _).symm



/-- Blueprint: lem:c13_time_normalization.  With `p = α - 1` and `κ = κ_α > 0`, if an admissible
`F` solves the existing normalized front equation on `I`, then `G(x,t) = F(x,t/κ)` is admissible
on `{t | t/κ ∈ I}` and solves the coefficient-`c_std` graph equation `G_t = W_{α,c_std}[G]` (with
absolutely convergent integral); `I = (-∞,T/κ)` becomes `(-∞,T)`; and the self-similar ansatz at
normalized time has physical scale `L_std(t) = (α(T-t)/κ)^{1/α}`. -/
theorem c13_time_normalization (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) :
    0 < c13_time_ratio α ∧
    (∀ (I : Set ℝ) (F : ℝ → ℝ → ℝ), c13_graph_class I F → gsqg_front_equation (α - 1) I F →
      c13_graph_class {t | t / c13_time_ratio α ∈ I} (fun x t => F x (t / c13_time_ratio α)) ∧
      ∀ t ∈ {t | t / c13_time_ratio α ∈ I}, ∀ x : ℝ,
        Integrable (fun s : ℝ =>
          (deriv (fun x => F x (t / c13_time_ratio α)) x -
              deriv (fun x => F x (t / c13_time_ratio α)) s) *
            ‖c13_pt x (F x (t / c13_time_ratio α)) - c13_pt s (F s (t / c13_time_ratio α))‖ ^
              (-α)) ∧
        deriv (fun s => F x (s / c13_time_ratio α)) t =
          c13_normal_speed α (c13_standard_coefficient α)
            (fun x t => F x (t / c13_time_ratio α)) x t) ∧
    (∀ T : ℝ, {t | t / c13_time_ratio α ∈ Iio (T / c13_time_ratio α)} = Iio T) ∧
    (∀ (ε T : ℝ) (f : ℝ → ℝ) (x t : ℝ),
      self_similar_ansatz (α - 1) ε (T / c13_time_ratio α) f x (t / c13_time_ratio α) =
        Real.sqrt ε * (α * (T - t) / c13_time_ratio α) ^ (1 / α) *
          f (x / (α * (T - t) / c13_time_ratio α) ^ (1 / α))) := by
  obtain ⟨hcf, hcs, hκ⟩ := c13p_aux_time_ratio_pos α hα1 hα2
  set κ := c13_time_ratio α with hκdef
  refine ⟨hκ, fun I F hF hfront => ?_, fun T => ?_, fun ε T f x t => ?_⟩
  · obtain ⟨hIo, ⟨t₀, ht₀⟩, hsm, hsl⟩ := hF
    have hcont : Continuous (fun t : ℝ => t / κ) := continuous_id.div_const κ
    refine ⟨⟨hIo.preimage hcont, ⟨t₀ * κ, by
        show t₀ * κ / κ ∈ I; rwa [mul_div_cancel_right₀ _ hκ.ne']⟩, ?_, ?_⟩, ?_⟩
    · have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.1, q.2 / κ)) :=
        contDiff_fst.prodMk (contDiff_snd.div_const κ)
      exact hsm.comp hmap.contDiffOn (fun q hq => ⟨mem_univ _, hq.2⟩)
    · intro J₀ hJ hc
      obtain ⟨M, hM, hMb⟩ := hsl ((fun t => t / κ) '' J₀)
        (by rintro _ ⟨t, ht, rfl⟩; exact hJ ht) (hc.image hcont)
      exact ⟨M, hM, fun x t ht => hMb x (t / κ) ⟨t, ht, rfl⟩⟩
    · intro t ht x
      obtain ⟨hint, heq⟩ := c01_front_equation_paper (α - 1) (by linarith) (by linarith) I F
        hfront (t / κ) ht x
      have hpα : (α - 1 + 1) / 2 = α / 2 := by ring
      rw [hpα] at hint heq
      have hfun : (fun s : ℝ => (deriv (fun x => F x (t / κ)) x - deriv (fun x => F x (t / κ)) s) *
            ‖c13_pt x (F x (t / κ)) - c13_pt s (F s (t / κ))‖ ^ (-α)) =
          fun z => (deriv (fun y => F y (t / κ)) x - deriv (fun y => F y (t / κ)) z) /
            ((x - z) ^ 2 + (F x (t / κ) - F z (t / κ)) ^ 2) ^ (α / 2) :=
        funext fun s => c13p_aux_kernel_eq α _ _ _ _ _
      refine ⟨hfun ▸ hint, ?_⟩
      -- time derivative by the chain rule
      have hIo' : IsOpen ((univ : Set ℝ) ×ˢ I) := isOpen_univ.prod hIo
      have hat : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2) (x, t / κ) :=
        (hfront.1.contDiffAt (hIo'.mem_nhds ⟨mem_univ _, ht⟩))
      have hdx : DifferentiableAt ℝ (fun s => F x s) (t / κ) := by
        have h1 := hat.differentiableAt one_ne_zero
        have h2 : DifferentiableAt ℝ (fun s : ℝ => ((x, s) : ℝ × ℝ)) (t / κ) :=
          (differentiableAt_const _).prodMk differentiableAt_id
        exact h1.comp (t / κ) h2
      have hd : HasDerivAt (fun s => F x (s / κ)) (deriv (fun s => F x s) (t / κ) * (1 / κ)) t := by
        have h3 : HasDerivAt (fun s : ℝ => s / κ) (1 / κ) t := by
          simpa using (hasDerivAt_id t).div_const κ
        exact HasDerivAt.comp (h₂ := fun s => F x s) t hdx.hasDerivAt h3
      rw [hd.deriv, heq]
      show _ = c13_standard_coefficient α * ∫ s : ℝ,
        (deriv (fun x => F x (t / κ)) x - deriv (fun x => F x (t / κ)) s) *
            ‖c13_pt x (F x (t / κ)) - c13_pt s (F s (t / κ))‖ ^ (-α)
      rw [hfun]
      have hcs' : c13_standard_coefficient α = calpha (α - 1) / κ := by
        rw [hκdef]; unfold c13_time_ratio; field_simp
      rw [hcs']; ring
  · ext t; simp only [mem_ofPred_eq, mem_Iio]
    exact div_lt_div_iff_of_pos_right hκ
  · unfold self_similar_ansatz self_similar_ansatz_L
    rw [show α - 1 + 1 = α by ring, show α * (T / κ - t / κ) = α * (T - t) / κ by ring]

/-! ### thm:c13_patch_main -/

/-! Helpers: local `L¹` convergence of subgraph indicators, and the initial trace at `t = 0`. -/

theorem c13p_aux_indicator_diff_le (S S' : Set c13_E) (X : c13_E) :
    |S.indicator (1 : c13_E → ℝ) X - S'.indicator (1 : c13_E → ℝ) X| ≤ 1 := by
  by_cases h1 : X ∈ S <;> by_cases h2 : X ∈ S' <;> simp [h1, h2]

theorem c13p_aux_L1loc (G : ℝ → ℝ → ℝ) (h : ℝ → ℝ) (hh : Continuous h) (T : ℝ)
    (hG : ∀ t, t < T → Continuous (fun x => G x t)) (η : ℝ → ℝ)
    (hη : Tendsto η (𝓝[<] T) (𝓝 0)) (hb : ∀ t, t < T → ∀ x, |G x t - h x| ≤ η t)
    (K : Set c13_E) (hK : IsCompact K) :
    (∀ t : ℝ, t < T → IntegrableOn (fun X : c13_E => |(c13_patch G t).indicator 1 X -
        {X : c13_E | X 1 < h (X 0)}.indicator (1 : c13_E → ℝ) X|) K) ∧
    Tendsto (fun t => ∫ X in K, |(c13_patch G t).indicator 1 X -
        {X : c13_E | X 1 < h (X 0)}.indicator (1 : c13_E → ℝ) X|) (𝓝[<] T) (𝓝 0) := by
  have hc0 : Continuous (fun X : c13_E => X 0) := by fun_prop
  have hc1 : Continuous (fun X : c13_E => X 1) := by fun_prop
  have hS : MeasurableSet {X : c13_E | X 1 < h (X 0)} :=
    (isOpen_lt hc1 (hh.comp hc0)).measurableSet
  have hSt : ∀ t, t < T → MeasurableSet (c13_patch G t) := fun t ht =>
    (isOpen_lt hc1 ((hG t ht).comp hc0)).measurableSet
  have hmeas : ∀ t, t < T → ∀ μ : Measure c13_E, AEStronglyMeasurable (fun X : c13_E =>
      |(c13_patch G t).indicator 1 X - {X : c13_E | X 1 < h (X 0)}.indicator (1 : c13_E → ℝ) X|)
      μ := fun t ht _ =>
    (continuous_abs.measurable.comp ((measurable_const.indicator (hSt t ht)).sub
      (measurable_const.indicator hS))).aestronglyMeasurable
  have hKf : volume K ≠ ⊤ := hK.measure_lt_top.ne
  refine ⟨fun t ht => Measure.integrableOn_of_bounded (M := 1) hKf (hmeas t ht _)
    (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_abs]; exact c13p_aux_indicator_diff_le _ _ X), ?_⟩
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K)
    (l := 𝓝[<] T) (fun _ => (1 : ℝ)) (f := fun _ => (0 : ℝ))
    (F := fun t X => |(c13_patch G t).indicator 1 X -
        {X : c13_E | X 1 < h (X 0)}.indicator (1 : c13_E → ℝ) X|)
    (eventually_nhdsWithin_of_forall fun t ht => hmeas t ht _)
    (Eventually.of_forall fun t => Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_abs]; exact c13p_aux_indicator_diff_le _ _ X)
    (by
      have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hKf
      exact integrable_const _) ?_
  · simpa using hlim
  · have hnull := c13g_aux_graph_null h hh
    have hae : ∀ᵐ X : c13_E ∂volume, X ∉ {X : c13_E | X 1 = h (X 0)} :=
      measure_eq_zero_iff_ae_notMem.mp hnull
    refine ae_restrict_of_ae (hae.mono fun X hX => ?_)
    have hd : 0 < |X 1 - h (X 0)| := abs_pos.mpr (sub_ne_zero.mpr hX)
    apply tendsto_const_nhds.congr'
    filter_upwards [hη.eventually (gt_mem_nhds hd), self_mem_nhdsWithin] with t h1 ht
    have hb' := hb t ht (X 0)
    have hiff : X ∈ c13_patch G t ↔ X ∈ {X : c13_E | X 1 < h (X 0)} := by
      simp only [c13_patch, mem_ofPred_eq]
      have key := lt_abs.mp h1
      rw [abs_le] at hb'
      constructor <;> intro hlt <;> rcases key with k | k <;> linarith
    by_cases hm : X ∈ c13_patch G t
    · have := hiff.mp hm; simp [indicator_of_mem hm, indicator_of_mem this]
    · have : X ∉ {X : c13_E | X 1 < h (X 0)} := fun h' => hm (hiff.mpr h')
      simp [indicator_of_notMem hm, indicator_of_notMem this]

/-- A spacetime test of `E × (-∞,T)` vanishes for all times beyond some `t₂ < T`. -/
theorem c13p_aux_test_time_bound (T : ℝ) (ζ : c13_E × ℝ → ℝ) (hζ : c13_scalar_test (Iio T) ζ) :
    ∃ t₂ : ℝ, t₂ < T ∧ ∀ X t, t₂ < t → ζ (X, t) = 0 := by
  obtain ⟨-, hcs, hsub⟩ := hζ
  have hK : IsCompact (Prod.snd '' tsupport ζ) := hcs.image continuous_snd
  rcases (Prod.snd '' tsupport ζ).eq_empty_or_nonempty with he | hne
  · refine ⟨T - 1, by linarith, fun X t _ => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
    have : t ∈ Prod.snd '' tsupport ζ := ⟨(X, t), hm, rfl⟩
    rw [he] at this; exact this
  · obtain ⟨m, hm, hmax⟩ := hK.exists_isGreatest hne
    obtain ⟨q, hq, rfl⟩ := hm
    refine ⟨q.2, (hsub hq).2, fun X t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
    have := hmax ⟨(X, t), hm, rfl⟩
    exact absurd this (not_le.mpr ht)

/-- The transport integrand vanishes at times where the test vanishes identically nearby. -/
theorem c13p_aux_integrand_zero (θ : c13_E → ℝ → ℝ) (u : c13_E → ℝ → c13_E)
    (ζ : c13_E × ℝ → ℝ) (t₂ : ℝ) (h0 : ∀ X t, t₂ < t → ζ (X, t) = 0) (p : c13_E × ℝ)
    (hp : t₂ < p.2) :
    θ p.1 p.2 * (deriv (fun s => ζ (p.1, s)) p.2 +
      fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2)) = 0 := by
  have h1 : deriv (fun s => ζ (p.1, s)) p.2 = 0 := by
    have : (fun s => ζ (p.1, s)) =ᶠ[𝓝 p.2] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hp] with s hs using h0 _ _ hs
    rw [this.deriv_eq]; simp
  have h2 : (fun Y => ζ (Y, p.2)) = fun _ => (0 : ℝ) := funext fun Y => h0 _ _ hp
  rw [h1, h2]; simp

/-- Initial trace at `t = 0` for a weak patch solution on `E × (-∞,T)`, `T > 0`, from
lem:c13_patch_time_trace, for every spacetime test of `E × (-∞,T)`. -/
theorem c13p_aux_initial_trace {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c) {T : ℝ}
    (hT : 0 < T) {F : ℝ → ℝ → ℝ} (hF : c13_graph_class (Iio T) F)
    (hw : c13_weak_patch_system α c (Iio T) (fun X t => (c13_patch F t).indicator 1 X)
      (c13_graph_velocity α c F))
    (ζ : c13_E × ℝ → ℝ) (hζ : c13_scalar_test (Iio T) ζ) :
    IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1
          (c13_graph_velocity α c F p.1 p.2))) (univ ×ˢ Ico 0 T) ∧
    (∫ p in univ ×ˢ Ico 0 T, (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1
          (c13_graph_velocity α c F p.1 p.2))) +
      (∫ X, (c13_patch F 0).indicator 1 X * ζ (X, 0)) = 0 := by
  obtain ⟨t₂, ht₂, h0⟩ := c13p_aux_test_time_bound T ζ hζ
  set t₃ := max t₂ 0 with ht₃
  have ht₃T : t₃ < T := max_lt ht₂ hT
  set t₁ := (t₃ + T) / 2 with ht₁
  have h01 : 0 < t₁ := by have := le_max_right t₂ 0; rw [ht₁]; linarith
  have h1T : t₁ < T := by rw [ht₁]; linarith
  have h31 : t₃ < t₁ := by rw [ht₁]; linarith
  have hsub : Icc 0 t₁ ⊆ Iio T := fun t ht => lt_of_le_of_lt ht.2 h1T
  have hKc : IsCompact (Prod.fst '' tsupport ζ) := hζ.2.1.image continuous_fst
  obtain ⟨hint, hid⟩ := (c13_patch_time_trace hα1 hα2 hc hF).2.2.1 hw 0 t₁ h01 hsub ζ univ
    isOpen_univ (subset_univ _) hζ.1.contDiffOn (Prod.fst '' tsupport ζ) hKc
    (fun t _ X hX => image_eq_zero_of_notMem_tsupport fun hm => hX ⟨(X, t), hm, rfl⟩)
    ⟨(t₁ - t₃) / 2, by linarith, fun t ht X => h0 X t (by
      have := le_max_left t₂ 0; have := ht.1; linarith)⟩
  have hss : univ ×ˢ Icc 0 t₁ ⊆ (univ : Set c13_E) ×ˢ Ico 0 T :=
    prod_mono le_rfl fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 h1T⟩
  have hmeas : MeasurableSet ((univ : Set c13_E) ×ˢ Ico (0 : ℝ) T) :=
    MeasurableSet.univ.prod measurableSet_Ico
  have hdiff : ∀ p ∈ (univ : Set c13_E) ×ˢ Ico (0 : ℝ) T \ univ ×ˢ Icc 0 t₁,
      (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1
          (c13_graph_velocity α c F p.1 p.2)) = 0 := by
    intro p hp
    refine c13p_aux_integrand_zero (fun X t => (c13_patch F t).indicator 1 X)
      (c13_graph_velocity α c F) ζ t₂ h0 p ?_
    have h1 : p.2 ∈ Ico (0 : ℝ) T := hp.1.2
    have h2 : p.2 ∉ Icc 0 t₁ := fun h => hp.2 ⟨mem_univ _, h⟩
    have : t₁ < p.2 := by
      by_contra hle; push Not at hle; exact h2 ⟨h1.1, hle⟩
    have := le_max_left t₂ 0; linarith
  refine ⟨hint.of_forall_sdiff_eq_zero hmeas hdiff, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hss hdiff]
  exact hid

-- Encoding: the canonical normalization `u = -∇^⊥(-Δ)^{-1+α/2}θ` is recorded as
-- `c_std A_α = 1` together with the Fourier symbol `-i (Jξ)_j |ξ|^{α-2}` of the coefficient-`c_std`
-- cancellation operator on Schwartz functions; the weak system itself is def:c13_weak_patch_system
-- with `c = c_std` and density jump one (`θ = 1_{Ω_t}`). `G` is introduced by an equation
-- hypothesis. The initial trace at `t = 0` is the weak formulation on `E × [0,T)` with initial
-- term `∫ θ(X,0) ζ(X,0)` for every spacetime test of `E × (-∞,T)` (not required to vanish at `0`).
-- The `L^∞` corner bound is pointwise in `x`, and the curvature supremum is taken in `ℝ≥0∞`,
-- as in `GSQG.main`.
/-- Blueprint: thm:c13_patch_main.  Canonical two-dimensional gSQG patches forming a corner. -/
theorem c13_patch_main (α : ℝ) (hα1 : 7 / 4 < α) (hα2 : α < 2) :
    c13_standard_coefficient α * c13_riesz_factor α = 1 ∧
    (∀ (φ : SchwartzMap c13_E ℝ) (ξ : c13_E) (j : Fin 2),
      ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) *
          (((∫ z : c13_E, (φ (X - z) - φ X) •
              c13_velocity_kernel α (c13_standard_coefficient α) z) j : ℝ) : ℂ) =
        (-Complex.I * ((c13_rotation ξ j * ‖ξ‖ ^ (α - 2) : ℝ) : ℂ)) *
          ∫ X : c13_E, Complex.exp (-Complex.I * (inner ℝ X ξ : ℝ)) * (φ X : ℂ)) ∧
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ c01_profile_bounds_hold (α - 1) C f ∧
          ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 0 < T → ∀ G : ℝ → ℝ → ℝ,
            G = (fun x t => Real.sqrt ε * (α * (T - t) / c13_time_ratio α) ^ (1 / α) *
              f (x / (α * (T - t) / c13_time_ratio α) ^ (1 / α))) →
            -- smooth admissible interface before `T`
            c13_graph_class (Iio T) G ∧
            -- weak solution of the canonical patch system on `E × (-∞,T)`
            c13_weak_patch_system α (c13_standard_coefficient α) (Iio T)
              (fun X t => (c13_patch G t).indicator 1 X)
              (c13_graph_velocity α (c13_standard_coefficient α) G) ∧
            -- initial trace at `t = 0`
            (∀ ζ : c13_E × ℝ → ℝ, c13_scalar_test (Iio T) ζ →
              IntegrableOn (fun p : c13_E × ℝ => (c13_patch G p.2).indicator 1 p.1 *
                  (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1
                    (c13_graph_velocity α (c13_standard_coefficient α) G p.1 p.2)))
                (univ ×ˢ Ico 0 T) ∧
              (∫ p in univ ×ˢ Ico 0 T, (c13_patch G p.2).indicator 1 p.1 *
                  (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1
                    (c13_graph_velocity α (c13_standard_coefficient α) G p.1 p.2))) +
                (∫ X, (c13_patch G 0).indicator 1 X * ζ (X, 0)) = 0) ∧
            -- corner convergence of the interface
            (∀ t : ℝ, t < T → ∀ x : ℝ,
              |G x t - Real.sqrt ε * corner x| ≤ C * Real.sqrt ε * (T - t) ^ (1 / α)) ∧
            -- curvature blow-up, with `b` independent of `T` and `δ`
            (∀ δ : ℝ, 0 < δ → ∃ tδ : ℝ, tδ < T ∧ ∀ t : ℝ, tδ < t → t < T →
              ENNReal.ofReal (b * (T - t) ^ (-1 / α)) ≤
                ⨆ x ∈ Ioo (-δ) δ, ENNReal.ofReal |iteratedDeriv 2 (fun x' => G x' t) x|) ∧
            -- local `L¹` convergence to the corner patch
            (∀ K : Set c13_E, IsCompact K →
              (∀ t : ℝ, t < T → IntegrableOn (fun X : c13_E => |(c13_patch G t).indicator 1 X -
                {X : c13_E | X 1 < Real.sqrt ε * corner (X 0)}.indicator (1 : c13_E → ℝ) X|) K) ∧
              Tendsto (fun t => ∫ X in K, |(c13_patch G t).indicator 1 X -
                {X : c13_E | X 1 < Real.sqrt ε * corner (X 0)}.indicator (1 : c13_E → ℝ) X|)
                (𝓝[<] T) (𝓝 0)) := by
  have hα1' : 1 < α := by linarith
  obtain ⟨hcf, hcs, hκ⟩ := c13p_aux_time_ratio_pos α hα1' hα2
  have hA : 0 < c13_riesz_factor α := by
    unfold c13_riesz_factor
    have hg1 : 0 < Real.Gamma (1 - α / 2) := Real.Gamma_pos_of_pos (by linarith)
    have hg2 : 0 < Real.Gamma (α / 2) := Real.Gamma_pos_of_pos (by linarith)
    have := Real.pi_pos
    have : 0 < (2 : ℝ) ^ (2 - α) := by positivity
    positivity
  have hone : c13_standard_coefficient α * c13_riesz_factor α = 1 := by
    unfold c13_standard_coefficient; exact inv_mul_cancel₀ hA.ne'
  refine ⟨hone, fun φ ξ j => ?_, ?_⟩
  · have := (c13_fourier_identification hα1' hα2 (c := c13_standard_coefficient α) φ).2.2.2.1 ξ j
    rw [this, hone, one_mul]
  set κ := c13_time_ratio α with hκdef
  obtain ⟨ε₀, hε₀, C, hC, hmain⟩ := main (α - 1) (by linarith) (by linarith)
  have hαe : α - 1 + 1 = α := by ring
  set C' := C * max 1 (κ ^ (1 / α))⁻¹ with hC'
  have hCC' : C ≤ C' := le_mul_of_one_le_right hC.le (le_max_left _ _)
  have hC'0 : 0 < C' := lt_of_lt_of_le hC hCC'
  refine ⟨ε₀, hε₀, C', hC'0, fun ε hε hεε => ?_⟩
  obtain ⟨f, hf, b1, b2, b3, h2, h3, c, hc, h4⟩ := hmain ε hε hεε
  have hjb : ∀ y a : ℝ, 0 ≤ jb y ^ a := fun y a => Real.rpow_nonneg (Real.sqrt_nonneg _) a
  have hb : c01_profile_bounds_hold (α - 1) C f := ⟨b1, b2, b3⟩
  have hb' : c01_profile_bounds_hold (α - 1) C' f :=
    ⟨fun y hy j hj => (b1 y hy j hj).trans (mul_le_mul_of_nonneg_right hCC' (hjb _ _)),
     fun y hy => (b2 y hy).trans (mul_le_mul_of_nonneg_right hCC' (hjb _ _)),
     fun y hy j hj => (b3 y hy j hj).trans (mul_le_mul_of_nonneg_right hCC' (hjb _ _))⟩
  have hκa : 0 < κ ^ (1 / α) := Real.rpow_pos_of_pos hκ _
  refine ⟨f, hf, hb', c * κ ^ (1 / α), mul_pos hc hκa, fun T hT G hG => ?_⟩
  have hT' : 0 < T / κ := div_pos hT hκ
  obtain ⟨-, hnorm, hIio, hans⟩ := c13_time_normalization α hα1' hα2
  set F := self_similar_ansatz (α - 1) ε (T / κ) f with hFdef
  have hGF : G = fun x t => F x (t / κ) := by
    rw [hG]; funext x t; rw [hFdef, hans]
  have hadm := (c13_main_graph_admissible (α - 1) (by linarith) (by linarith) C ε (T / κ) hε f
    hf hb).1
  have hfront := (h2 (T / κ) hT').1
  obtain ⟨hGc, heq⟩ := hnorm (Iio (T / κ)) F hadm hfront
  rw [hIio] at hGc heq
  rw [hGF]
  -- corner bound in canonical time
  have hcorner : ∀ t : ℝ, t < T → ∀ x : ℝ,
      |F x (t / κ) - Real.sqrt ε * corner x| ≤ C' * Real.sqrt ε * (T - t) ^ (1 / α) := by
    intro t ht x
    have h := h3 (T / κ) hT' (t / κ) (div_lt_div_of_pos_right ht hκ) x
    rw [hαe, show T / κ - t / κ = (T - t) / κ by ring,
      Real.div_rpow (by linarith) hκ.le] at h
    have hTt : 0 ≤ (T - t) ^ (1 / α) := Real.rpow_nonneg (by linarith) _
    have hsε : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
    have : C * Real.sqrt ε * ((T - t) ^ (1 / α) / κ ^ (1 / α)) ≤
        C * Real.sqrt ε * (T - t) ^ (1 / α) * max 1 (κ ^ (1 / α))⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    refine h.trans (this.trans (le_of_eq ?_))
    rw [hC']; ring
  have hw : c13_weak_patch_system α (c13_standard_coefficient α) (Iio T)
      (fun X t => (c13_patch (fun x t => F x (t / κ)) t).indicator 1 X)
      (c13_graph_velocity α (c13_standard_coefficient α) (fun x t => F x (t / κ))) := by
    refine (c13_patch_front_equivalence hα1' hα2 hcs hGc).2.1.mpr fun x t ht => ?_
    rw [(heq t ht x).2]
    unfold c13_normal_speed
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun s => c13p_aux_kernel_eq α _ _ _ _ _)
  refine ⟨hGc, hw, fun ζ hζ => c13p_aux_initial_trace hα1' hα2 hcs hT hGc hw ζ hζ, hcorner,
    fun δ hδ => ?_, fun K hK => ?_⟩
  · obtain ⟨tδ, htδ, hbl⟩ := h4 (T / κ) hT' δ hδ
    refine ⟨tδ * κ, by rwa [← lt_div_iff₀ hκ], fun t h1 h2' => ?_⟩
    have hs1 : tδ < t / κ := by rwa [lt_div_iff₀ hκ]
    have hs2 : t / κ < T / κ := div_lt_div_of_pos_right h2' hκ
    have h := hbl (t / κ) hs1 hs2
    have hrw : c * (T / κ - t / κ) ^ (-1 / (α - 1 + 1)) =
        c * κ ^ (1 / α) * (T - t) ^ (-1 / α) := by
      rw [hαe, show T / κ - t / κ = (T - t) / κ by ring, Real.div_rpow (by linarith) hκ.le,
        show -1 / α = -(1 / α) by ring, Real.rpow_neg hκ.le]
      field_simp
    rw [hrw] at h
    exact h
  · have hcont : Continuous (fun x : ℝ => Real.sqrt ε * corner x) := by
      unfold corner; fun_prop
    have hη : Tendsto (fun t => C' * Real.sqrt ε * (T - t) ^ (1 / α)) (𝓝[<] T) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => (T - t) ^ (1 / α)) :=
        (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by positivity))
      have := (hc.tendsto T).const_mul (C' * Real.sqrt ε)
      rw [sub_self, Real.zero_rpow (by positivity), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact c13p_aux_L1loc (fun x t => F x (t / κ)) _ hcont T
      (fun t ht => ((hfront.2.1 (t / κ) (div_lt_div_of_pos_right ht hκ)).continuous))
      _ hη hcorner K hK

end GSQG
