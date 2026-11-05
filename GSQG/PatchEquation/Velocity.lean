import GSQG.PatchEquation.GraphFlux
import GSQG.PatchEquation.CancellationOperator

/-!
# Beyond the paper (2D patch derivation): velocity bound, local integrability, divergence-free (blueprint ch. 13)

Helpers are named `c13v_aux_*`.

Notation in the statements: `γ_t(s) = c13_pt s (F s t)`, `τ_t(s) = c13_pt 1 (F_x(s,t))`, with
`F_x(s,t) = deriv (fun x => F x t) s`; the graph at time `t` is `{X | X 1 = F (X 0) t}`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### Pure helpers -/

lemma c13v_aux_norm_sub_sq (X : c13_E) (s y : ℝ) :
    ‖X - c13_pt s y‖ ^ 2 = (X 0 - s) ^ 2 + (X 1 - y) ^ 2 := by
  simp [c13_pt, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

lemma c13v_aux_norm_tau (a : ℝ) : ‖c13_pt 1 a‖ ≤ 1 + |a| := by
  have h : ‖c13_pt 1 a‖ ^ 2 = 1 + a ^ 2 := by
    simp [c13_pt, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  nlinarith [sq_abs a, abs_nonneg a, norm_nonneg (c13_pt 1 a)]

lemma c13v_aux_pt_continuous : Continuous (fun p : ℝ × ℝ => c13_pt p.1 p.2) := by
  unfold c13_pt; fun_prop

lemma c13v_aux_dist {f : ℝ → ℝ} {M : ℝ} (hf : Differentiable ℝ f) (hM : ∀ x, |deriv f x| ≤ M)
    (x y s : ℝ) :
    (s - x) ^ 2 + (y - f x) ^ 2 ≤ 2 * (1 + M ^ 2) * ((s - x) ^ 2 + (y - f s) ^ 2) := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun z _ => hf z)
    (fun z _ => hM z) convex_univ (mem_univ x) (mem_univ s)
  simp only [Real.norm_eq_abs] at h
  have h2 : (f s - f x) ^ 2 ≤ M ^ 2 * (s - x) ^ 2 := by
    calc (f s - f x) ^ 2 = |f s - f x| ^ 2 := (sq_abs _).symm
      _ ≤ (M * |s - x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = M ^ 2 * (s - x) ^ 2 := by rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg (y - f s - (f s - f x)), sq_nonneg (s - x), sq_nonneg M,
    sq_nonneg (y - f s)]

lemma c13v_aux_kernel1d {α : ℝ} (hα : 1 < α) (x d : ℝ) (hd : d ≠ 0) :
    Integrable (fun s : ℝ => ((s - x) ^ 2 + d ^ 2) ^ (-α / 2)) ∧
    ∫ s : ℝ, ((s - x) ^ 2 + d ^ 2) ^ (-α / 2) =
      (∫ u : ℝ, (1 + u ^ 2) ^ (-α / 2)) * |d| ^ (1 - α) := by
  have had : 0 < |d| := abs_pos.mpr hd
  have hg : Integrable (fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-α / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hα)
  simp only [Real.norm_eq_abs, sq_abs] at hg
  have hpt : ∀ s : ℝ, ((s - x) ^ 2 + d ^ 2) ^ (-α / 2) =
      |d| ^ (-α) * (1 + ((s - x) / |d|) ^ 2) ^ (-α / 2) := by
    intro s
    have h1 : (s - x) ^ 2 + d ^ 2 = |d| ^ 2 * (1 + ((s - x) / |d|) ^ 2) := by
      field_simp; rw [sq_abs]; ring
    rw [h1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul had.le]
    congr 2; push_cast; ring
  simp_rw [hpt]
  refine ⟨((hg.comp_div had.ne').comp_sub_right x).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub_right_eq_self (fun s => (1 + (s / |d|) ^ 2) ^ (-α / 2)) x,
    Measure.integral_comp_div (fun s => (1 + s ^ 2) ^ (-α / 2)), abs_of_pos had, smul_eq_mul,
    sub_eq_add_neg, Real.rpow_add had, Real.rpow_one]
  ring

/-- Blueprint: lem:c13_velocity_bound.  For a fixed-time slope bound `|F_x| ≤ M`, the contour
integral defining `U(X,t)` converges absolutely at every off-graph point, and
`|U((x,y),t)| ≤ C |y - F(x,t)|^{1-α}` with `C = C_{α,c,M}` independent of `F`, `t`, `X`.
The scalar majorant `∫ |τ_t(s)| |X - γ_t(s)|^{-α} ds` obeys the same bound. -/
theorem c13_velocity_bound {α : ℝ} (hα1 : 1 < α) (c M : ℝ) (hM : 0 ≤ M) :
    ∃ C, 0 < C ∧ ∀ (F : ℝ → ℝ → ℝ) (t : ℝ),
      Differentiable ℝ (fun x => F x t) →
      (∀ x, |deriv (fun x => F x t) x| ≤ M) →
      ∀ X : c13_E, X 1 ≠ F (X 0) t →
        Integrable (fun s : ℝ => (‖X - c13_pt s (F s t)‖ ^ (-α)) •
            c13_pt 1 (deriv (fun x => F x t) s)) ∧
        (∫ s : ℝ, ‖c13_pt 1 (deriv (fun x => F x t) s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α))
          ≤ C * |X 1 - F (X 0) t| ^ (1 - α) ∧
        ‖c13_graph_velocity α c F X t‖ ≤ C * |X 1 - F (X 0) t| ^ (1 - α) := by
  set K0 := ∫ u : ℝ, (1 + u ^ 2) ^ (-α / 2) with hK0
  have hK0n : 0 ≤ K0 := integral_nonneg fun u => by positivity
  set L := (1 + M) * (2 * (1 + M ^ 2)) ^ (α / 2) with hL
  have hLn : 0 ≤ L := by positivity
  refine ⟨(|c| + 1) * (L * K0) + 1, by positivity, ?_⟩
  intro F t hFd hFM X hX
  set f := fun x => F x t with hf
  set δ := X 1 - F (X 0) t with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hX
  obtain ⟨hgi, hgint⟩ := c13v_aux_kernel1d hα1 (X 0) δ hδ0
  have hpow : 0 ≤ |δ| ^ (1 - α) := by positivity
  -- pointwise majorant
  have hmaj : ∀ s : ℝ, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α) ≤
      L * ((s - X 0) ^ 2 + δ ^ 2) ^ (-α / 2) := by
    intro s
    have hA : 0 < (s - X 0) ^ 2 + δ ^ 2 := by positivity
    have hd := c13v_aux_dist hFd hFM (X 0) (X 1) s
    have hN := c13v_aux_norm_sub_sq X s (F s t)
    have hB : 0 < 2 * (1 + M ^ 2) := by positivity
    have hlow : ((s - X 0) ^ 2 + δ ^ 2) / (2 * (1 + M ^ 2)) ≤ ‖X - c13_pt s (F s t)‖ ^ 2 := by
      rw [div_le_iff₀ hB, hN]; simp only [hf] at hd; nlinarith [hd]
    have h1 : ‖X - c13_pt s (F s t)‖ ^ (-α) = (‖X - c13_pt s (F s t)‖ ^ 2) ^ (-α / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; ring
    have h2 : ‖X - c13_pt s (F s t)‖ ^ (-α) ≤
        ((s - X 0) ^ 2 + δ ^ 2) ^ (-α / 2) * (2 * (1 + M ^ 2)) ^ (α / 2) := by
      rw [h1]
      refine (Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)).trans_eq ?_
      have e : (2 * (1 + M ^ 2)) ^ (-α / 2) = ((2 * (1 + M ^ 2)) ^ (α / 2))⁻¹ := by
        rw [neg_div, Real.rpow_neg hB.le]
      rw [Real.div_rpow hA.le hB.le, e, div_inv_eq_mul]
    have h3 : ‖c13_pt 1 (deriv f s)‖ ≤ 1 + M :=
      (c13v_aux_norm_tau _).trans (by linarith [hFM s])
    calc _ ≤ (1 + M) * (((s - X 0) ^ 2 + δ ^ 2) ^ (-α / 2) * (2 * (1 + M ^ 2)) ^ (α / 2)) :=
          mul_le_mul h3 h2 (by positivity) (by positivity)
      _ = _ := by rw [hL]; ring
  have hmeas : AEStronglyMeasurable (fun s : ℝ => (‖X - c13_pt s (F s t)‖ ^ (-α)) •
      c13_pt 1 (deriv f s)) volume := by
    have hc : Continuous (fun s => F s t) := hFd.continuous
    have e1 : Measurable (fun s : ℝ => ‖X - c13_pt s (F s t)‖ ^ (-α)) := by
      have : Continuous (fun s : ℝ => ‖X - c13_pt s (F s t)‖) :=
        (continuous_const.sub (c13v_aux_pt_continuous.comp
          (continuous_id.prodMk hc))).norm
      exact this.measurable.pow_const _
    have e2 : Measurable (fun s : ℝ => c13_pt 1 (deriv f s)) :=
      c13v_aux_pt_continuous.measurable.comp (measurable_const.prodMk (measurable_deriv f))
    exact (e1.smul e2).aestronglyMeasurable
  have hnorm : ∀ s : ℝ, ‖(‖X - c13_pt s (F s t)‖ ^ (-α)) • c13_pt 1 (deriv f s)‖ =
      ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α) := by
    intro s
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
  have hint : Integrable (fun s : ℝ => (‖X - c13_pt s (F s t)‖ ^ (-α)) •
      c13_pt 1 (deriv f s)) :=
    Integrable.mono' (hgi.const_mul L) hmeas (ae_of_all _ fun s => (hnorm s).trans_le (hmaj s))
  have hbd : (∫ s : ℝ, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α)) ≤
      L * K0 * |δ| ^ (1 - α) := by
    calc _ ≤ ∫ s : ℝ, L * ((s - X 0) ^ 2 + δ ^ 2) ^ (-α / 2) :=
          integral_mono_of_nonneg (ae_of_all _ fun s => by positivity) (hgi.const_mul L)
            (ae_of_all _ hmaj)
      _ = _ := by rw [integral_const_mul, hgint]; ring
  have hCbd : L * K0 * |δ| ^ (1 - α) ≤ ((|c| + 1) * (L * K0) + 1) * |δ| ^ (1 - α) := by
    have : L * K0 ≤ (|c| + 1) * (L * K0) + 1 := by nlinarith [abs_nonneg c, mul_nonneg hLn hK0n]
    exact mul_le_mul_of_nonneg_right this hpow
  refine ⟨hint, hbd.trans hCbd, ?_⟩
  have hU : c13_graph_velocity α c F X t = (-c) • ∫ s : ℝ, (‖X - c13_pt s (F s t)‖ ^ (-α)) •
      c13_pt 1 (deriv f s) := by
    simp only [c13_graph_velocity, hX, ↓reduceIte, hf]
  rw [hU, norm_smul, Real.norm_eq_abs, abs_neg]
  have h1 : ‖∫ s : ℝ, (‖X - c13_pt s (F s t)‖ ^ (-α)) • c13_pt 1 (deriv f s)‖ ≤
      L * K0 * |δ| ^ (1 - α) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simp_rw [hnorm]; exact hbd
  calc |c| * _ ≤ |c| * (L * K0 * |δ| ^ (1 - α)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    _ ≤ _ := by nlinarith [abs_nonneg c, mul_nonneg (mul_nonneg hLn hK0n) hpow]


/-! ### Helpers for local integrability -/

lemma c13v_aux_abs_rpow_ball {p : ℝ} (hp : -1 < p) :
    ∫⁻ u in Metric.ball (0 : ℝ) 1, ENNReal.ofReal (|u| ^ p) < ⊤ := by
  have h : IntegrableOn (fun u : ℝ => |u| ^ p) (Metric.ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := -p) (by simp)
      (by simp; linarith) (ae_of_all _ fun u => ?_) ?_
    · simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) p)]
    · exact (continuous_abs.measurable.pow_const p).aestronglyMeasurable
  have := h.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun u => Real.rpow_nonneg (abs_nonneg u) p)]
    at this
  exact this

lemma c13v_aux_vertical_le {p : ℝ} (hp0 : p ≤ 0) (R : ℝ) (b : ℝ) :
    ∫⁻ y in Icc (-R) R, ENNReal.ofReal (|y - b| ^ p) ≤
      (∫⁻ u in Metric.ball (0 : ℝ) 1, ENNReal.ofReal (|u| ^ p)) + ENNReal.ofReal (2 * R) := by
  have hpt : ∀ y : ℝ, ENNReal.ofReal (|y - b| ^ p) ≤
      (Metric.ball (0 : ℝ) 1).indicator (fun u => ENNReal.ofReal (|u| ^ p)) (y - b) + 1 := by
    intro y
    by_cases h : y - b ∈ Metric.ball (0 : ℝ) 1
    · rw [indicator_of_mem h]; exact le_self_add
    · rw [indicator_of_notMem h, zero_add, ENNReal.ofReal_le_one]
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt] at h
      exact Real.rpow_le_one_of_one_le_of_nonpos h hp0
  calc _ ≤ ∫⁻ y in Icc (-R) R,
        ((Metric.ball (0 : ℝ) 1).indicator (fun u => ENNReal.ofReal (|u| ^ p)) (y - b) + 1) :=
        lintegral_mono hpt
    _ = (∫⁻ y in Icc (-R) R,
          (Metric.ball (0 : ℝ) 1).indicator (fun u => ENNReal.ofReal (|u| ^ p)) (y - b)) +
          volume (Icc (-R) R) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, one_mul]
    _ ≤ (∫⁻ y, (Metric.ball (0 : ℝ) 1).indicator (fun u => ENNReal.ofReal (|u| ^ p)) (y - b)) +
          volume (Icc (-R) R) := add_le_add_left (setLIntegral_le_lintegral _ _) _
    _ = _ := by
        rw [lintegral_sub_right_eq_self (fun u => (Metric.ball (0 : ℝ) 1).indicator
          (fun u => ENNReal.ofReal (|u| ^ p)) u) b,
          lintegral_indicator measurableSet_ball, Real.volume_Icc]
        congr 2; ring

/-- Uniform vertical estimate: `∫_{closedBall 0 R} |y - b(x)|^p dX` is bounded independently
of `b`, for `-1 < p ≤ 0`. -/
lemma c13v_aux_box {p : ℝ} (hp : -1 < p) (hp0 : p ≤ 0) (R : ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ b : ℝ → ℝ,
      ∫⁻ X in Metric.closedBall (0 : c13_E) R, ENNReal.ofReal (|X 1 - b (X 0)| ^ p) ≤ C := by
  refine ⟨((∫⁻ u in Metric.ball (0 : ℝ) 1, ENNReal.ofReal (|u| ^ p)) + ENNReal.ofReal (2 * R)) *
    ENNReal.ofReal (2 * R), ENNReal.mul_lt_top (ENNReal.add_lt_top.2
      ⟨c13v_aux_abs_rpow_ball hp, ENNReal.ofReal_lt_top⟩) ENNReal.ofReal_lt_top, fun b => ?_⟩
  set T : Set c13_E := {X | X 0 ∈ Icc (-R) R ∧ X 1 ∈ Icc (-R) R}
  have hsub : Metric.closedBall (0 : c13_E) R ⊆ T := by
    intro X hX
    rw [Metric.mem_closedBall, dist_zero_right] at hX
    have h2 := c13g_aux_norm_sq X
    have hR : 0 ≤ R := (norm_nonneg X).trans hX
    have hX2 : ‖X‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hX 2
    refine ⟨abs_le.1 ?_, abs_le.1 ?_⟩ <;>
      refine abs_le_of_sq_le_sq' ?_ hR |> fun h => abs_le.2 h <;> nlinarith [sq_nonneg (X 0), sq_nonneg (X 1)]
  have hpre : c13g_aux_equiv ⁻¹' T = Icc (-R) R ×ˢ Icc (-R) R := by
    ext q; simp only [T, mem_preimage, mem_ofPred_eq, c13g_aux_equiv_apply, c13g_aux_pt_zero,
      c13g_aux_pt_one, mem_prod]
  calc _ ≤ ∫⁻ X in T, ENNReal.ofReal (|X 1 - b (X 0)| ^ p) := lintegral_mono_set hsub
    _ = ∫⁻ q in c13g_aux_equiv ⁻¹' T,
          ENNReal.ofReal (|c13g_aux_equiv q 1 - b (c13g_aux_equiv q 0)| ^ p) :=
        (c13g_aux_mp.setLIntegral_comp_preimage_emb c13g_aux_equiv.measurableEmbedding _ T).symm
    _ = ∫⁻ q in Icc (-R) R ×ˢ Icc (-R) R, ENNReal.ofReal (|q.2 - b q.1| ^ p) := by
        rw [hpre]; simp only [c13g_aux_equiv_apply, c13g_aux_pt_zero, c13g_aux_pt_one]
    _ ≤ ∫⁻ x in Icc (-R) R, ∫⁻ y in Icc (-R) R, ENNReal.ofReal (|y - b x| ^ p) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]; exact lintegral_prod_le _
    _ ≤ ∫⁻ x in Icc (-R) R, ((∫⁻ u in Metric.ball (0 : ℝ) 1, ENNReal.ofReal (|u| ^ p)) +
          ENNReal.ofReal (2 * R)) := lintegral_mono fun x => c13v_aux_vertical_le hp0 R (b x)
    _ = _ := by rw [setLIntegral_const, Real.volume_Icc]; congr 2; ring

lemma c13v_aux_partial {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {s t : ℝ}
    (ht : t ∈ I) :
    HasDerivAt (fun x => F x t) (fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) (s, t) (1, 0)) s := by
  have hO : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hF.1
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => F q.1 q.2) (s, t) :=
    (hF.2.2.1.contDiffAt (hO.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt (by simp)
  have := hd.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  simp only [Function.comp_def, id] at this
  exact this

lemma c13v_aux_deriv_continuousOn {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    ContinuousOn (fun q : ℝ × ℝ => deriv (fun x => F x q.2) q.1) (univ ×ˢ I) := by
  have hO : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hF.1
  refine ((hF.2.2.1.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply
    (continuousOn_const (c := ((1 : ℝ), (0 : ℝ))))).congr fun q hq => ?_
  exact (c13v_aux_partial hF hq.2).deriv

lemma c13v_aux_measurable (α c : ℝ) {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    ∃ U' : c13_E × ℝ → c13_E, Measurable U' ∧
      ∀ p : c13_E × ℝ, p.2 ∈ I → U' p = c13_graph_velocity α c F p.1 p.2 := by
  classical
  let O : Set ((c13_E × ℝ) × ℝ) := {q | q.1.2 ∈ I}
  have hOo : IsOpen O := hF.1.preimage (continuous_snd.comp continuous_fst)
  let h : (c13_E × ℝ) × ℝ → c13_E × ℝ := fun q =>
    (q.1.1 - c13_pt q.2 (F q.2 q.1.2), deriv (fun x => F x q.1.2) q.2)
  have hmap : MapsTo (fun q : (c13_E × ℝ) × ℝ => (q.2, q.1.2)) O (univ ×ˢ I) :=
    fun q hq => ⟨mem_univ _, hq⟩
  have hc2 : Continuous (fun q : (c13_E × ℝ) × ℝ => (q.2, q.1.2)) :=
    continuous_snd.prodMk (continuous_snd.comp continuous_fst)
  have hcont : ContinuousOn h O := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine (continuous_fst.fst).continuousOn.sub ?_
      have h1 := hF.2.2.1.continuousOn.comp hc2.continuousOn hmap
      simp only [Function.comp_def] at h1
      have h2 := c13v_aux_pt_continuous.comp_continuousOn (continuousOn_snd.prodMk h1)
      simp only [Function.comp_def] at h2
      exact h2
    · have h1 := (c13v_aux_deriv_continuousOn hF).comp hc2.continuousOn hmap
      simp only [Function.comp_def] at h1
      exact h1
  let g : c13_E × ℝ → c13_E := fun v => ‖v.1‖ ^ (-α) • c13_pt 1 v.2
  have hg : Measurable g := ((continuous_fst.norm).measurable.pow_const _).smul
    (c13v_aux_pt_continuous.measurable.comp (measurable_const.prodMk measurable_snd))
  let f' := fun q => g (O.piecewise h (fun _ => 0) q)
  have hf' : Measurable f' :=
    hg.comp (hcont.measurable_piecewise continuousOn_const hOo.measurableSet)
  let S : Set (c13_E × ℝ) := {p | p.2 ∈ I}
  let k := S.piecewise (fun p : c13_E × ℝ => p.1 1 - F (p.1 0) p.2) (fun _ => 1)
  have hkc : ContinuousOn (fun p : c13_E × ℝ => p.1 1 - F (p.1 0) p.2) S :=
    (by fun_prop : Continuous fun p : c13_E × ℝ => p.1 1).continuousOn.sub
      (c13g_aux_continuousOn hF)
  have hk : Measurable k := hkc.measurable_piecewise continuousOn_const
    (hF.1.preimage continuous_snd).measurableSet
  have hint : Measurable (fun p : c13_E × ℝ => ∫ s, f' (p, s)) :=
    hf'.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨fun p => if k p = 0 then 0 else (-c) • ∫ s, f' (p, s), ?_, ?_⟩
  · refine Measurable.ite (hk (measurableSet_singleton 0)) measurable_const ?_
    exact hint.const_smul (-c)
  · intro p hp
    have hkp : k p = p.1 1 - F (p.1 0) p.2 := piecewise_eq_of_mem _ _ _ hp
    have hf'p : ∀ s, f' (p, s) = ‖p.1 - c13_pt s (F s p.2)‖ ^ (-α) •
        c13_pt 1 (deriv (fun x => F x p.2) s) := fun s => by
      simp only [f', g, piecewise_eq_of_mem _ _ _ (show (p, s) ∈ O from hp), h]
    simp only [c13_graph_velocity, hkp, sub_eq_zero, hf'p]

/-- Blueprint: lem:c13_velocity_local_integrable.  For an admissible graph, `U` is jointly
(a.e.-strongly) measurable and locally integrable on `E × I`, integrable on every `Q × J₀` with
`Q` compact and `J₀ ⊆ I` compact; and for every compactly supported bounded measurable spatial
test `Φ` the joint contour-test integrand `|τ_t(s)| |X - γ_t(s)|^{-α} |Φ(X)|` is integrable in
`(s, X)`, with a bound uniform in `t ∈ J₀` for tests supported in a fixed compact `K` with
`sup |Φ| ≤ B`.  (Tonelli/a.e. majorants; no nonintegrable Bochner integral is used.) -/
theorem c13_velocity_local_integrable {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (c : ℝ)
    (I : Set ℝ) (F : ℝ → ℝ → ℝ) (hF : c13_graph_class I F) :
    AEStronglyMeasurable (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2)
      ((volume : Measure (c13_E × ℝ)).restrict (univ ×ˢ I)) ∧
    LocallyIntegrableOn (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2) (univ ×ˢ I) ∧
    (∀ Q : Set c13_E, IsCompact Q → ∀ J₀ ⊆ I, IsCompact J₀ →
      IntegrableOn (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2) (Q ×ˢ J₀)) ∧
    (∀ J₀ ⊆ I, IsCompact J₀ → ∀ K : Set c13_E, IsCompact K →
      ∃ C, 0 ≤ C ∧ ∀ t ∈ J₀, ∀ Φ : c13_E → ℝ, AEStronglyMeasurable Φ volume →
        (∀ X, X ∉ K → Φ X = 0) → ∀ B : ℝ, (∀ X, |Φ X| ≤ B) →
        Integrable (fun q : ℝ × c13_E => ‖c13_pt 1 (deriv (fun x => F x t) q.1)‖ *
            ‖q.2 - c13_pt q.1 (F q.1 t)‖ ^ (-α) * |Φ q.2|) ∧
        (∫ q : ℝ × c13_E, ‖c13_pt 1 (deriv (fun x => F x t) q.1)‖ *
            ‖q.2 - c13_pt q.1 (F q.1 t)‖ ^ (-α) * |Φ q.2|) ≤ C * B) := by
  have hp1 : -1 < 1 - α := by linarith
  have hp0 : 1 - α ≤ 0 := by linarith
  have hdiff : ∀ t ∈ I, Differentiable ℝ (fun x => F x t) := fun t ht =>
    (c13g_aux_slice_contDiff hF ht).differentiable (by simp)
  -- (A) measurability
  have hA : AEStronglyMeasurable (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2)
      ((volume : Measure (c13_E × ℝ)).restrict (univ ×ˢ I)) := by
    obtain ⟨U', hU'm, hU'⟩ := c13v_aux_measurable α c hF
    refine hU'm.aestronglyMeasurable.congr ?_
    exact (ae_restrict_iff' ((isOpen_univ.prod hF.1).measurableSet)).2
      (ae_of_all _ fun p hp => hU' p hp.2)
  -- pointwise bound on a compact time interval
  have hptJ : ∀ J₀ ⊆ I, IsCompact J₀ → ∃ Cb, 0 < Cb ∧ ∀ t ∈ J₀, ∀ X : c13_E,
      ‖c13_graph_velocity α c F X t‖ ≤ Cb * |X 1 - F (X 0) t| ^ (1 - α) := by
    intro J₀ hJ hJc
    obtain ⟨M, hM0, hMb⟩ := hF.2.2.2 J₀ hJ hJc
    obtain ⟨Cb, hCb, hbd⟩ := c13_velocity_bound hα1 c M hM0
    refine ⟨Cb, hCb, fun t ht X => ?_⟩
    by_cases hX : X 1 = F (X 0) t
    · simp only [c13_graph_velocity, hX, ↓reduceIte, norm_zero]; positivity
    · exact (hbd F t (hdiff t (hJ ht)) (fun x => hMb x t ht) X hX).2.2
  -- (C) compact integrability
  have hC : ∀ Q : Set c13_E, IsCompact Q → ∀ J₀ ⊆ I, IsCompact J₀ →
      IntegrableOn (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2) (Q ×ˢ J₀) := by
    intro Q hQ J₀ hJ hJc
    obtain ⟨Cb, hCb, hpt⟩ := hptJ J₀ hJ hJc
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall 0
    obtain ⟨Cx, hCx, hbox⟩ := c13v_aux_box hp1 hp0 R
    refine ⟨hA.mono_measure (Measure.restrict_mono (prod_mono (subset_univ _) hJ) le_rfl), ?_⟩
    rw [HasFiniteIntegral, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← lintegral_prod_swap]
    refine lt_of_le_of_lt (lintegral_prod_le _) ?_
    have hin : ∀ t ∈ J₀, ∫⁻ X in Q, ‖c13_graph_velocity α c F X t‖ₑ ≤
        ENNReal.ofReal Cb * Cx := by
      intro t ht
      calc _ ≤ ∫⁻ X in Metric.closedBall (0 : c13_E) R, ‖c13_graph_velocity α c F X t‖ₑ :=
            lintegral_mono_set hR
        _ ≤ ∫⁻ X in Metric.closedBall (0 : c13_E) R,
              ENNReal.ofReal Cb * ENNReal.ofReal (|X 1 - F (X 0) t| ^ (1 - α)) := by
            refine lintegral_mono fun X => ?_
            rw [← ofReal_norm, ← ENNReal.ofReal_mul hCb.le]
            exact ENNReal.ofReal_le_ofReal (hpt t ht X)
        _ = ENNReal.ofReal Cb * ∫⁻ X in Metric.closedBall (0 : c13_E) R,
              ENNReal.ofReal (|X 1 - F (X 0) t| ^ (1 - α)) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ _ := by gcongr; exact hbox (fun x => F x t)
    calc _ ≤ ∫⁻ t in J₀, ENNReal.ofReal Cb * Cx :=
          setLIntegral_mono' hJc.isClosed.measurableSet hin
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCx)
            hJc.measure_lt_top
  refine ⟨hA, ?_, hC, ?_⟩
  · refine (locallyIntegrableOn_iff (isOpen_univ.prod hF.1).isLocallyClosed).2
      fun k hk hkc => ?_
    refine (hC _ (hkc.image continuous_fst) _ ?_ (hkc.image continuous_snd)).mono_set
      fun q hq => ⟨mem_image_of_mem _ hq, mem_image_of_mem _ hq⟩
    rintro _ ⟨q, hq, rfl⟩; exact (hk hq).2
  -- (D) joint contour-test integrability
  intro J₀ hJ hJc K hK
  obtain ⟨M, hM0, hMb⟩ := hF.2.2.2 J₀ hJ hJc
  obtain ⟨Cb, hCb, hbd⟩ := c13_velocity_bound hα1 0 M hM0
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨Cx, hCx, hbox⟩ := c13v_aux_box hp1 hp0 R
  refine ⟨Cb * Cx.toReal, by positivity, fun t ht Φ hΦ hΦK B hB => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hFd := hdiff t (hJ ht)
  have hFc : Continuous (fun x => F x t) := hFd.continuous
  set m : ℝ × c13_E → ℝ := fun q => ‖c13_pt 1 (deriv (fun x => F x t) q.1)‖ *
      ‖q.2 - c13_pt q.1 (F q.1 t)‖ ^ (-α) * |Φ q.2| with hm
  have hm0 : ∀ q, 0 ≤ m q := fun q => by positivity
  have hmeas : AEStronglyMeasurable m (volume.prod volume) := by
    have e1 : Measurable (fun q : ℝ × c13_E => ‖c13_pt 1 (deriv (fun x => F x t) q.1)‖ *
        ‖q.2 - c13_pt q.1 (F q.1 t)‖ ^ (-α)) := by
      have h1 : Measurable (fun q : ℝ × c13_E => ‖c13_pt 1 (deriv (fun x => F x t) q.1)‖) :=
        (c13v_aux_pt_continuous.measurable.comp
          (measurable_const.prodMk ((measurable_deriv _).comp measurable_fst))).norm
      have : Continuous (fun q : ℝ × c13_E => ‖q.2 - c13_pt q.1 (F q.1 t)‖) :=
        (continuous_snd.sub (c13v_aux_pt_continuous.comp
          (continuous_fst.prodMk (hFc.comp continuous_fst)))).norm
      have h2 : Measurable (fun q : ℝ × c13_E => ‖q.2 - c13_pt q.1 (F q.1 t)‖ ^ (-α)) :=
        this.measurable.pow_const _
      exact h1.mul h2
    have e2 : AEStronglyMeasurable (fun q : ℝ × c13_E => |Φ q.2|) (volume.prod volume) :=
      (hΦ.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).norm
    exact e1.aestronglyMeasurable.mul e2
  have hnull : ∀ᵐ X : c13_E, X ∉ {X : c13_E | X 1 = F (X 0) t} :=
    (measure_eq_zero_iff_ae_notMem).1 (c13g_aux_graph_null (fun x => F x t) hFc)
  have hinner : ∀ᵐ X : c13_E, ∫⁻ s, ENNReal.ofReal (m (s, X)) ≤
      (Metric.closedBall (0 : c13_E) R).indicator (fun X => ENNReal.ofReal B *
        (ENNReal.ofReal Cb * ENNReal.ofReal (|X 1 - F (X 0) t| ^ (1 - α)))) X := by
    filter_upwards [hnull] with X hX
    have hX' : X 1 ≠ F (X 0) t := hX
    by_cases hXK : X ∈ K
    · obtain ⟨hi, hmaj, -⟩ := hbd F t hFd (fun x => hMb x t ht) X hX'
      have hmi : Integrable (fun s : ℝ => ‖c13_pt 1 (deriv (fun x => F x t) s)‖ *
          ‖X - c13_pt s (F s t)‖ ^ (-α)) := by
        refine hi.norm.congr (ae_of_all _ fun s => ?_)
        simp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
      rw [indicator_of_mem (hR hXK)]
      calc ∫⁻ s, ENNReal.ofReal (m (s, X)) = (∫⁻ s, ENNReal.ofReal
            (‖c13_pt 1 (deriv (fun x => F x t) s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α))) *
            ENNReal.ofReal |Φ X| := by
            rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun s => ?_
            simp only [hm]; rw [ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (∫ s, ‖c13_pt 1 (deriv (fun x => F x t) s)‖ *
              ‖X - c13_pt s (F s t)‖ ^ (-α)) * ENNReal.ofReal |Φ X| := by
            rw [ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ fun s => by positivity)]
        _ ≤ ENNReal.ofReal (Cb * |X 1 - F (X 0) t| ^ (1 - α)) * ENNReal.ofReal B := by
            gcongr
            · exact hB X
        _ = _ := by rw [ENNReal.ofReal_mul hCb.le]; ring
    · have h0 : ∀ s, m (s, X) = 0 := fun s => by simp [hm, hΦK X hXK]
      simp only [h0, ENNReal.ofReal_zero, lintegral_const, zero_mul]
      exact bot_le
  have hlin : ∫⁻ q, ENNReal.ofReal (m q) ∂(volume.prod volume) ≤
      ENNReal.ofReal (Cb * Cx.toReal * B) := by
    rw [← lintegral_prod_swap]
    refine (lintegral_prod_le _).trans ?_
    refine (lintegral_mono_ae hinner).trans ?_
    rw [lintegral_indicator measurableSet_closedBall, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc _ ≤ ENNReal.ofReal B * (ENNReal.ofReal Cb * Cx) := by
          gcongr; exact hbox (fun x => F x t)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCb.le,
            ENNReal.ofReal_toReal hCx.ne]; ring
  have hint : Integrable m (volume.prod volume) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hm0)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · rw [← Measure.volume_eq_prod] at hint; exact hint
  · have := integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hm0) hmeas
    rw [Measure.volume_eq_prod, this]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin


/-! ### Helpers for spatial smoothness and divergence -/

/-- The contour kernel `|X - γ_t(s)|^{-α} τ_t(s)` (helper). -/
def c13v_aux_K (α : ℝ) (F : ℝ → ℝ → ℝ) (X : c13_E) (t s : ℝ) : c13_E :=
  ‖X - c13_pt s (F s t)‖ ^ (-α) • c13_pt 1 (deriv (fun x => F x t) s)

/-- Its spatial derivative `v ↦ -α |w|^{-α-2} ⟪w, v⟫ τ`, `w = X - γ_t(s)` (helper). -/
def c13v_aux_DK (α : ℝ) (F : ℝ → ℝ → ℝ) (X : c13_E) (t s : ℝ) : c13_E →L[ℝ] c13_E :=
  (-α * ‖X - c13_pt s (F s t)‖ ^ (-α - 2)) •
    (innerSL ℝ (X - c13_pt s (F s t))).smulRight (c13_pt 1 (deriv (fun x => F x t) s))

lemma c13v_aux_U_eq (α c : ℝ) (F : ℝ → ℝ → ℝ) {X : c13_E} {t : ℝ} (hX : X 1 ≠ F (X 0) t) :
    c13_graph_velocity α c F X t = (-c) • ∫ s, c13v_aux_K α F X t s := by
  simp only [c13_graph_velocity, hX, ↓reduceIte, c13v_aux_K]

lemma c13v_aux_ne_of_off {F : ℝ → ℝ → ℝ} {X : c13_E} {t : ℝ} (hX : X 1 ≠ F (X 0) t) (s : ℝ) :
    X - c13_pt s (F s t) ≠ 0 := by
  intro h
  have h1 : X = c13_pt s (F s t) := sub_eq_zero.mp h
  apply hX; rw [h1]; simp

lemma c13v_aux_hasFDerivAt_K (α : ℝ) (F : ℝ → ℝ → ℝ) {X : c13_E} {t s : ℝ}
    (hw : X - c13_pt s (F s t) ≠ 0) :
    HasFDerivAt (fun Y => c13v_aux_K α F Y t s) (c13v_aux_DK α F X t s) X := by
  set γ := c13_pt s (F s t)
  set τ := c13_pt 1 (deriv (fun x => F x t) s)
  have hn : ‖X - γ‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hn2 : ‖X - γ‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have h1 : HasFDerivAt (fun Y : c13_E => ‖Y - γ‖ ^ 2)
      (2 • (innerSL ℝ (X - γ)).comp (ContinuousLinearMap.id ℝ c13_E)) X :=
    ((hasFDerivAt_id X).sub_const γ).norm_sq
  have h2 := (h1.rpow_const (p := -α / 2) (Or.inl hn2)).smul_const τ
  have heq : (fun Y : c13_E => (‖Y - γ‖ ^ 2) ^ (-α / 2) • τ) = fun Y => c13v_aux_K α F Y t s := by
    funext Y
    simp only [c13v_aux_K, γ, τ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 2; push_cast; ring
  rw [heq] at h2
  convert h2 using 1
  ext v i
  simp only [c13v_aux_DK, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    γ, τ]
  have e : (‖X - γ‖ ^ 2) ^ (-α / 2 - 1) = ‖X - γ‖ ^ (-α - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; push_cast; ring
  rw [e]
  simp only [PiLp.smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

lemma c13v_aux_norm_DK (α : ℝ) (hα : 0 ≤ α) (F : ℝ → ℝ → ℝ) {X : c13_E} {t s : ℝ}
    (hw : X - c13_pt s (F s t) ≠ 0) :
    ‖c13v_aux_DK α F X t s‖ ≤
      α * ‖c13_pt 1 (deriv (fun x => F x t) s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-(α + 1)) := by
  have hn : ‖X - c13_pt s (F s t)‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [c13v_aux_DK, norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm,
    Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hα,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have e : ‖X - c13_pt s (F s t)‖ ^ (-(α + 1)) =
      ‖X - c13_pt s (F s t)‖ ^ (-α - 2) * ‖X - c13_pt s (F s t)‖ := by
    rw [← Real.rpow_add_one hn]; congr 1; ring
  rw [e]; apply le_of_eq; ring

lemma c13v_aux_dom {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ}
    (hM : ∀ x, |deriv f x| ≤ M) (X : c13_E) (s x₀ d₀ : ℝ) (hd₀ : 0 < d₀) (hd₁ : d₀ ≤ 1)
    (hX0 : |X 0 - x₀| ≤ 1) (hδ : d₀ ≤ |X 1 - f (X 0)|) :
    ‖X - c13_pt s (f s)‖ ^ (-r) ≤
      (2 * (1 + M ^ 2)) ^ (r / 2) * (d₀ ^ 2 / 3) ^ (-r / 2) * (1 + (s - x₀) ^ 2) ^ (-r / 2) := by
  have hB : 0 < 2 * (1 + M ^ 2) := by positivity
  set δ := X 1 - f (X 0)
  have hd := c13v_aux_dist hf hM (X 0) (X 1) s
  have hN := c13v_aux_norm_sub_sq X s (f s)
  have hδ2 : d₀ ^ 2 ≤ δ ^ 2 := by
    have := pow_le_pow_left₀ hd₀.le hδ 2; rwa [sq_abs] at this
  have hx2 : (s - x₀) ^ 2 ≤ 2 * (s - X 0) ^ 2 + 2 := by
    have : |X 0 - x₀| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (X 0 - x₀)]
    rw [sq_abs] at this; nlinarith [sq_nonneg (s - X 0 - (X 0 - x₀))]
  set A₀ := d₀ ^ 2 / 3 * (1 + (s - x₀) ^ 2)
  have hA₀ : 0 < A₀ := by positivity
  have hA : A₀ ≤ (s - X 0) ^ 2 + δ ^ 2 := by
    have h3 : d₀ ^ 2 * (1 + (s - x₀) ^ 2) ≤ 3 * ((s - X 0) ^ 2 + δ ^ 2) := by
      nlinarith [sq_nonneg (s - X 0), sq_nonneg d₀, mul_le_mul_of_nonneg_left hx2 (sq_nonneg d₀),
        pow_le_one₀ hd₀.le hd₁ (n := 2)]
    simp only [A₀]; linarith
  have hlow : A₀ / (2 * (1 + M ^ 2)) ≤ ‖X - c13_pt s (f s)‖ ^ 2 := by
    rw [div_le_iff₀ hB, hN]; nlinarith [hd, hA]
  have h1 : ‖X - c13_pt s (f s)‖ ^ (-r) = (‖X - c13_pt s (f s)‖ ^ 2) ^ (-r / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; congr 1; push_cast; ring
  rw [h1]
  refine (Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)).trans_eq ?_
  have e : (2 * (1 + M ^ 2)) ^ (-r / 2) = ((2 * (1 + M ^ 2)) ^ (r / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg hB.le]
  rw [Real.div_rpow hA₀.le hB.le, e, div_inv_eq_mul, Real.mul_rpow (by positivity) (by positivity)]
  ring

lemma c13v_aux_contL : Continuous (fun q : c13_E × ℝ =>
    (innerSL ℝ q.1).smulRight (c13_pt 1 q.2)) := by
  have h1 : Continuous (fun q : c13_E × ℝ => innerSL ℝ q.1) :=
    (innerSL ℝ (E := c13_E)).continuous.comp continuous_fst
  have h2 : Continuous (fun q : c13_E × ℝ => c13_pt 1 q.2) :=
    c13v_aux_pt_continuous.comp (continuous_const.prodMk continuous_snd)
  exact (ContinuousLinearMap.smulRightL ℝ c13_E c13_E).continuous₂.comp (h1.prodMk h2)

lemma c13v_aux_meas_K (α : ℝ) (F : ℝ → ℝ → ℝ) (X : c13_E) (t : ℝ)
    (hc : Continuous (fun s => F s t)) :
    AEStronglyMeasurable (fun s => c13v_aux_K α F X t s) volume := by
  have e1 : Measurable (fun s : ℝ => ‖X - c13_pt s (F s t)‖ ^ (-α)) := by
    have : Continuous (fun s : ℝ => ‖X - c13_pt s (F s t)‖) :=
      (continuous_const.sub (c13v_aux_pt_continuous.comp (continuous_id.prodMk hc))).norm
    exact this.measurable.pow_const _
  have e2 : Measurable (fun s : ℝ => c13_pt 1 (deriv (fun x => F x t) s)) :=
    c13v_aux_pt_continuous.measurable.comp (measurable_const.prodMk (measurable_deriv _))
  exact (e1.smul e2).aestronglyMeasurable

lemma c13v_aux_meas_DK (α : ℝ) (F : ℝ → ℝ → ℝ) (X : c13_E) (t : ℝ)
    (hc : Continuous (fun s => F s t)) :
    AEStronglyMeasurable (fun s => c13v_aux_DK α F X t s) volume := by
  have hw : Continuous (fun s : ℝ => X - c13_pt s (F s t)) :=
    continuous_const.sub (c13v_aux_pt_continuous.comp (continuous_id.prodMk hc))
  have e0 : Measurable (fun s : ℝ => ‖X - c13_pt s (F s t)‖ ^ (-α - 2)) :=
    hw.norm.measurable.pow_const _
  have e1 : Measurable (fun s : ℝ => -α * ‖X - c13_pt s (F s t)‖ ^ (-α - 2)) :=
    measurable_const.mul e0
  have e2 : Measurable (fun s : ℝ => (innerSL ℝ (X - c13_pt s (F s t))).smulRight
      (c13_pt 1 (deriv (fun x => F x t) s))) := by
    have h3 : Measurable (fun s : ℝ => (X - c13_pt s (F s t), deriv (fun x => F x t) s)) :=
      hw.measurable.prodMk (measurable_deriv (fun x => F x t))
    have h4 := c13v_aux_contL.measurable.comp h3
    exact h4
  unfold c13v_aux_DK
  exact (e1.smul e2).aestronglyMeasurable

lemma c13v_aux_local {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {p₀ : c13_E × ℝ}
    (hp₀ : p₀.2 ∈ I) (hoff : p₀.1 1 ≠ F (p₀.1 0) p₀.2) :
    ∃ M d₀ : ℝ, 0 ≤ M ∧ 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ᶠ p in 𝓝 p₀, p.2 ∈ I ∧
      (∀ x, |deriv (fun x => F x p.2) x| ≤ M) ∧ |p.1 0 - p₀.1 0| ≤ 1 ∧
      d₀ ≤ |p.1 1 - F (p.1 0) p.2| := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hF.1 p₀.2 hp₀
  have hJ : Metric.closedBall p₀.2 (ε / 2) ⊆ I :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨M, hM0, hMb⟩ := hF.2.2.2 _ hJ (isCompact_closedBall _ _)
  set δ₀ := p₀.1 1 - F (p₀.1 0) p₀.2
  have hδ₀ : 0 < |δ₀| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  refine ⟨M, min (|δ₀| / 2) 1, hM0, by positivity, min_le_right _ _, ?_⟩
  have hkc : ContinuousOn (fun p : c13_E × ℝ => p.1 1 - F (p.1 0) p.2) {p | p.2 ∈ I} :=
    (by fun_prop : Continuous fun p : c13_E × ℝ => p.1 1).continuousOn.sub
      (c13g_aux_continuousOn hF)
  have hkca : ContinuousAt (fun p : c13_E × ℝ => |p.1 1 - F (p.1 0) p.2|) p₀ :=
    continuous_abs.continuousAt.comp
      (hkc.continuousAt ((hF.1.preimage continuous_snd).mem_nhds hp₀))
  have e1 : ∀ᶠ p : c13_E × ℝ in 𝓝 p₀, min (|δ₀| / 2) 1 < |p.1 1 - F (p.1 0) p.2| :=
    hkca.eventually (lt_mem_nhds (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
  have e2 : ∀ᶠ p : c13_E × ℝ in 𝓝 p₀, p.2 ∈ Metric.ball p₀.2 (ε / 2) :=
    continuous_snd.continuousAt.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have e3 : ∀ᶠ p : c13_E × ℝ in 𝓝 p₀, p.1 0 ∈ Metric.ball (p₀.1 0) 1 :=
    (by fun_prop : Continuous fun p : c13_E × ℝ => p.1 0).continuousAt.eventually
      (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [e1, e2, e3] with p h1 h2 h3
  have h2' : p.2 ∈ Metric.closedBall p₀.2 (ε / 2) := Metric.ball_subset_closedBall h2
  refine ⟨hJ h2', fun x => hMb x p.2 h2', ?_, h1.le⟩
  rw [Metric.mem_ball, Real.dist_eq] at h3; exact h3.le

lemma c13v_aux_cont_K (α : ℝ) {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F)
    {X₀ : c13_E} {t₀ s : ℝ} (ht₀ : t₀ ∈ I) (hw : X₀ - c13_pt s (F s t₀) ≠ 0) :
    ContinuousAt (fun p : c13_E × ℝ => c13v_aux_K α F p.1 p.2 s) (X₀, t₀) ∧
    ContinuousAt (fun p : c13_E × ℝ => c13v_aux_DK α F p.1 p.2 s) (X₀, t₀) := by
  have hO : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hF.1
  have hmem : (s, t₀) ∈ univ ×ˢ I := ⟨mem_univ _, ht₀⟩
  have hc2 : ContinuousAt (fun p : c13_E × ℝ => (s, p.2)) (X₀, t₀) :=
    (continuous_const.prodMk continuous_snd).continuousAt
  have hγ : ContinuousAt (fun p : c13_E × ℝ => F s p.2) (X₀, t₀) := by
    have := ContinuousAt.comp (x := (X₀, t₀)) (g := fun q : ℝ × ℝ => F q.1 q.2)
      (hF.2.2.1.continuousOn.continuousAt (hO.mem_nhds hmem)) hc2
    exact this
  have hd : ContinuousAt (fun p : c13_E × ℝ => deriv (fun x => F x p.2) s) (X₀, t₀) := by
    have := ContinuousAt.comp (x := (X₀, t₀)) (g := fun q : ℝ × ℝ => deriv (fun x => F x q.2) q.1)
      ((c13v_aux_deriv_continuousOn hF).continuousAt (hO.mem_nhds hmem)) hc2
    exact this
  have hwc : ContinuousAt (fun p : c13_E × ℝ => p.1 - c13_pt s (F s p.2)) (X₀, t₀) := by
    have h := c13v_aux_pt_continuous.continuousAt.comp (x := (X₀, t₀))
      (g := fun q : ℝ × ℝ => c13_pt q.1 q.2) ((continuousAt_const : ContinuousAt (fun _ : c13_E × ℝ => s) (X₀, t₀)).prodMk hγ)
    exact continuousAt_fst.sub h
  have hτ : ContinuousAt (fun p : c13_E × ℝ => c13_pt 1 (deriv (fun x => F x p.2) s)) (X₀, t₀) := by
    have h := c13v_aux_pt_continuous.continuousAt.comp (x := (X₀, t₀))
      (g := fun q : ℝ × ℝ => c13_pt q.1 q.2) ((continuousAt_const : ContinuousAt (fun _ : c13_E × ℝ => (1 : ℝ)) (X₀, t₀)).prodMk hd)
    exact h
  have hn : ‖X₀ - c13_pt s (F s t₀)‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  constructor
  · exact (hwc.norm.rpow_const (Or.inl hn)).smul hτ
  · have hL := c13v_aux_contL.continuousAt.comp (x := (X₀, t₀))
      (g := fun q : c13_E × ℝ => (innerSL ℝ q.1).smulRight (c13_pt 1 q.2))
      (hwc.prodMk hd)
    exact (continuousAt_const.mul (hwc.norm.rpow_const (Or.inl hn))).smul hL

lemma c13v_aux_off_of_le {F : ℝ → ℝ → ℝ} {p : c13_E × ℝ} {d₀ : ℝ} (hd : 0 < d₀)
    (h : d₀ ≤ |p.1 1 - F (p.1 0) p.2|) : p.1 1 ≠ F (p.1 0) p.2 := by
  intro h'; rw [h', sub_self, abs_zero] at h; linarith

lemma c13v_aux_integrable_bracket {r : ℝ} (hr : 1 < r) (x₀ : ℝ) :
    Integrable (fun s : ℝ => (1 + (s - x₀) ^ 2) ^ (-r / 2)) := by
  have hg : Integrable (fun u : ℝ => ((1 : ℝ) + ‖u‖ ^ 2) ^ (-r / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hr)
  simp only [Real.norm_eq_abs, sq_abs] at hg
  exact hg.comp_sub_right x₀

lemma c13v_aux_hasFDerivAt_int {α : ℝ} (hα1 : 1 < α) {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hF : c13_graph_class I F) {X₀ : c13_E} {t : ℝ} (ht : t ∈ I) (hoff : X₀ 1 ≠ F (X₀ 0) t) :
    Integrable (fun s => c13v_aux_DK α F X₀ t s) ∧
    HasFDerivAt (fun X => ∫ s, c13v_aux_K α F X t s) (∫ s, c13v_aux_DK α F X₀ t s) X₀ := by
  obtain ⟨M, d₀, hM0, hd0, hd1, hev⟩ := c13v_aux_local hF (p₀ := (X₀, t)) ht hoff
  have hevX : ∀ᶠ X : c13_E in 𝓝 X₀, t ∈ I ∧
      (∀ x, |deriv (fun x => F x t) x| ≤ M) ∧ |X 0 - X₀ 0| ≤ 1 ∧
      d₀ ≤ |X 1 - F (X 0) t| :=
    ((continuous_id.prodMk continuous_const).tendsto X₀).eventually hev
  have hFd : Differentiable ℝ (fun x => F x t) :=
    (c13g_aux_slice_contDiff hF ht).differentiable (by simp)
  have hFM : ∀ x, |deriv (fun x => F x t) x| ≤ M := (hevX.self_of_nhds).2.1
  set G : ℝ → ℝ := fun s => α * (1 + M) * ((2 * (1 + M ^ 2)) ^ ((α + 1) / 2) *
    (d₀ ^ 2 / 3) ^ (-(α + 1) / 2) * (1 + (s - X₀ 0) ^ 2) ^ (-(α + 1) / 2)) with hG
  have hGi : Integrable G :=
    ((c13v_aux_integrable_bracket (r := α + 1) (by linarith) (X₀ 0)).const_mul _).const_mul _
  have hbound : ∀ s, ∀ X ∈ {X : c13_E | t ∈ I ∧
      (∀ x, |deriv (fun x => F x t) x| ≤ M) ∧ |X 0 - X₀ 0| ≤ 1 ∧
      d₀ ≤ |X 1 - F (X 0) t|}, ‖c13v_aux_DK α F X t s‖ ≤ G s := by
    intro s X hX
    obtain ⟨-, -, hX0, hδ⟩ := hX
    have hw := c13v_aux_ne_of_off (c13v_aux_off_of_le (p := (X, t)) hd0 hδ) s
    refine (c13v_aux_norm_DK α (by linarith) F hw).trans ?_
    have h1 := c13v_aux_dom (r := α + 1) (by linarith) hFd hFM X s (X₀ 0) d₀ hd0 hd1 hX0 hδ
    have h2 : ‖c13_pt 1 (deriv (fun x => F x t) s)‖ ≤ 1 + M :=
      (c13v_aux_norm_tau _).trans (by linarith [hFM s])
    simp only [hG]
    rw [mul_assoc, mul_assoc α]
    gcongr
  obtain ⟨Cb, -, hbd⟩ := c13_velocity_bound hα1 0 M hM0
  have hKi : Integrable (fun s => c13v_aux_K α F X₀ t s) := (hbd F t hFd hFM X₀ hoff).1
  have hcont : Continuous (fun s => F s t) := hFd.continuous
  have hDKi : Integrable (fun s => c13v_aux_DK α F X₀ t s) :=
    Integrable.mono' hGi (c13v_aux_meas_DK α F X₀ t hcont)
      (ae_of_all _ fun s => hbound s X₀ hevX.self_of_nhds)
  refine ⟨hDKi, ?_⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := G) (x₀ := X₀)
    (F := fun X s => c13v_aux_K α F X t s) (F' := fun X s => c13v_aux_DK α F X t s) hevX
    (Eventually.of_forall fun X => c13v_aux_meas_K α F X t hcont) hKi
    (c13v_aux_meas_DK α F X₀ t hcont) (ae_of_all _ fun s X hX => hbound s X hX) hGi
    (ae_of_all _ fun s X hX => ?_)
  obtain ⟨-, -, -, hδ⟩ := hX
  exact c13v_aux_hasFDerivAt_K α F (c13v_aux_ne_of_off (c13v_aux_off_of_le (p := (X, t)) hd0 hδ) s)

lemma c13v_aux_cont_int {α : ℝ} (hα1 : 1 < α) {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hF : c13_graph_class I F) {X₀ : c13_E} {t₀ : ℝ} (ht : t₀ ∈ I)
    (hoff : X₀ 1 ≠ F (X₀ 0) t₀) :
    ContinuousAt (fun p : c13_E × ℝ => ∫ s, c13v_aux_K α F p.1 p.2 s) (X₀, t₀) ∧
    ContinuousAt (fun p : c13_E × ℝ => ∫ s, c13v_aux_DK α F p.1 p.2 s) (X₀, t₀) := by
  obtain ⟨M, d₀, hM0, hd0, hd1, hev⟩ := c13v_aux_local hF (p₀ := (X₀, t₀)) ht hoff
  have hmeasK : ∀ᶠ p : c13_E × ℝ in 𝓝 (X₀, t₀),
      AEStronglyMeasurable (fun s => c13v_aux_K α F p.1 p.2 s) volume := by
    filter_upwards [hev] with p hp
    exact c13v_aux_meas_K α F p.1 p.2
      ((c13g_aux_slice_contDiff hF hp.1).differentiable (by simp)).continuous
  have hmeasDK : ∀ᶠ p : c13_E × ℝ in 𝓝 (X₀, t₀),
      AEStronglyMeasurable (fun s => c13v_aux_DK α F p.1 p.2 s) volume := by
    filter_upwards [hev] with p hp
    exact c13v_aux_meas_DK α F p.1 p.2
      ((c13g_aux_slice_contDiff hF hp.1).differentiable (by simp)).continuous
  have hw₀ : ∀ s, X₀ - c13_pt s (F s t₀) ≠ 0 := c13v_aux_ne_of_off hoff
  constructor
  · refine continuousAt_of_dominated (bound := fun s => (1 + M) * ((2 * (1 + M ^ 2)) ^ (α / 2) *
      (d₀ ^ 2 / 3) ^ (-α / 2) * (1 + (s - X₀ 0) ^ 2) ^ (-α / 2))) hmeasK ?_
      (((c13v_aux_integrable_bracket hα1 (X₀ 0)).const_mul _).const_mul _)
      (ae_of_all _ fun s => (c13v_aux_cont_K α hF ht (hw₀ s)).1)
    filter_upwards [hev] with p hp
    refine ae_of_all _ fun s => ?_
    obtain ⟨hpI, hpM, hp0, hδ⟩ := hp
    have hFd : Differentiable ℝ (fun x => F x p.2) :=
      (c13g_aux_slice_contDiff hF hpI).differentiable (by simp)
    have h1 := c13v_aux_dom (r := α) (by linarith) hFd hpM p.1 s (X₀ 0) d₀ hd0 hd1 hp0 hδ
    have h2 : ‖c13_pt 1 (deriv (fun x => F x p.2) s)‖ ≤ 1 + M :=
      (c13v_aux_norm_tau _).trans (by linarith [hpM s])
    rw [c13v_aux_K, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    gcongr
  · refine continuousAt_of_dominated (bound := fun s => α * (1 + M) *
      ((2 * (1 + M ^ 2)) ^ ((α + 1) / 2) * (d₀ ^ 2 / 3) ^ (-(α + 1) / 2) *
        (1 + (s - X₀ 0) ^ 2) ^ (-(α + 1) / 2))) hmeasDK ?_
      (((c13v_aux_integrable_bracket (r := α + 1) (by linarith) (X₀ 0)).const_mul _).const_mul _)
      (ae_of_all _ fun s => (c13v_aux_cont_K α hF ht (hw₀ s)).2)
    filter_upwards [hev] with p hp
    refine ae_of_all _ fun s => ?_
    obtain ⟨hpI, hpM, hp0, hδ⟩ := hp
    have hFd : Differentiable ℝ (fun x => F x p.2) :=
      (c13g_aux_slice_contDiff hF hpI).differentiable (by simp)
    have hw := c13v_aux_ne_of_off (c13v_aux_off_of_le hd0 hδ) s
    refine (c13v_aux_norm_DK α (by linarith) F hw).trans ?_
    have h1 := c13v_aux_dom (r := α + 1) (by linarith) hFd hpM p.1 s (X₀ 0) d₀ hd0 hd1 hp0 hδ
    have h2 : ‖c13_pt 1 (deriv (fun x => F x p.2) s)‖ ≤ 1 + M :=
      (c13v_aux_norm_tau _).trans (by linarith [hpM s])
    rw [mul_assoc, mul_assoc α]
    gcongr

/-- The divergence integrand is minus an exact `s`-derivative whose primitive
`|X - γ(s)|^{-α}` vanishes at `s → ±∞`. -/
lemma c13v_aux_div_scalar {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (X : c13_E) (hX : X 1 ≠ f (X 0))
    (hint : Integrable (fun s => -α * ‖X - c13_pt s (f s)‖ ^ (-α - 2) *
      ((X 0 - s) + (X 1 - f s) * deriv f s))) :
    ∫ s, -α * ‖X - c13_pt s (f s)‖ ^ (-α - 2) * ((X 0 - s) + (X 1 - f s) * deriv f s) = 0 := by
  set g : ℝ → ℝ := fun s => ‖X - c13_pt s (f s)‖ ^ (-α) with hg
  set g' : ℝ → ℝ := fun s => α * ‖X - c13_pt s (f s)‖ ^ (-α - 2) *
      ((X 0 - s) + (X 1 - f s) * deriv f s) with hg'
  have hw : ∀ s, X - c13_pt s (f s) ≠ 0 := fun s => c13v_aux_ne_of_off (F := fun x _ => f x)
    (t := 0) hX s
  have hderiv : ∀ s, HasDerivAt g (g' s) s := by
    intro s
    have hq : HasDerivAt (fun s => (X 0 - s) ^ 2 + (X 1 - f s) ^ 2)
        (2 * (X 0 - s) * (-1) + 2 * (X 1 - f s) * (-deriv f s)) s := by
      have h1 := ((hasDerivAt_id s).const_sub (X 0)).pow 2
      have h2 := ((hf s).hasDerivAt.const_sub (X 1)).pow 2
      convert h1.add h2 using 1
      · funext u; simp only [Pi.add_apply, Pi.pow_apply, id]
      · simp only [id]; ring
    have hq0 : (X 0 - s) ^ 2 + (X 1 - f s) ^ 2 ≠ 0 := by
      rw [← c13v_aux_norm_sub_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hw s))
    have h3 := hq.rpow_const (p := -α / 2) (Or.inl hq0)
    have heq : (fun s => ((X 0 - s) ^ 2 + (X 1 - f s) ^ 2) ^ (-α / 2)) = g := by
      funext u
      simp only [hg]
      rw [← c13v_aux_norm_sub_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1; push_cast; ring
    rw [heq] at h3
    convert h3 using 1
    simp only [hg']
    rw [← c13v_aux_norm_sub_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have : ((2 : ℕ) : ℝ) * (-α / 2 - 1) = -α - 2 := by push_cast; ring
    rw [this]; ring
  have hg'i : Integrable g' := by
    have := hint.neg
    refine this.congr (ae_of_all _ fun s => ?_)
    simp only [hg', Pi.neg_apply]; ring
  have hle : ∀ s, s ≠ X 0 → g s ≤ |s - X 0| ^ (-α) := by
    intro s hs
    have hpos : 0 < |s - X 0| := abs_pos.mpr (sub_ne_zero.mpr hs)
    have hle : |s - X 0| ≤ ‖X - c13_pt s (f s)‖ := by
      have h := c13v_aux_norm_sub_sq X s (f s)
      have : (s - X 0) ^ 2 ≤ ‖X - c13_pt s (f s)‖ ^ 2 := by
        rw [h]; nlinarith [sq_nonneg (X 1 - f s), sq_nonneg (s - X 0)]
      have := sq_le_sq.mp this
      rwa [abs_norm] at this
    exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  have hg0 : ∀ s, 0 ≤ g s := fun s => by positivity
  have hlim0 : ∀ l : Filter ℝ, Tendsto (fun s => |s - X 0|) l atTop → (∀ᶠ s in l, s ≠ X 0) →
      Tendsto g l (𝓝 0) := by
    intro l hl hne
    have h0 : Tendsto (fun s => |s - X 0| ^ (-α)) l (𝓝 0) := (tendsto_rpow_neg_atTop hα).comp hl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall hg0) ?_
    filter_upwards [hne] with s hs using hle s hs
  have htop : Tendsto g atTop (𝓝 0) := hlim0 atTop
    (tendsto_abs_atTop_atTop.comp (tendsto_atTop_add_const_right _ (-X 0) tendsto_id |>.congr
      fun s => by simp [sub_eq_add_neg]))
    ((eventually_gt_atTop (X 0)).mono fun s hs => hs.ne')
  have hbot : Tendsto g atBot (𝓝 0) := hlim0 atBot
    (tendsto_abs_atBot_atTop.comp (tendsto_atBot_add_const_right _ (-X 0) tendsto_id |>.congr
      fun s => by simp [sub_eq_add_neg]))
    ((eventually_lt_atBot (X 0)).mono fun s hs => hs.ne)
  have hI := integral_of_hasDerivAt_of_tendsto hderiv hg'i hbot htop
  have : (fun s => -α * ‖X - c13_pt s (f s)‖ ^ (-α - 2) *
      ((X 0 - s) + (X 1 - f s) * deriv f s)) = fun s => -g' s := by
    funext s; simp only [hg']; ring
  rw [this, integral_neg, hI]; simp

/-- Blueprint: lem:c13_velocity_divergence.  For each `t ∈ I`, `U(·,t)` is `C¹` on the open
off-graph set and divergence-free there; `U` and its spatial derivative `D_X U` are jointly
continuous in `(X, t)` off the spacetime graph (over `t ∈ I`).  No time differentiability of `U`
is claimed. -/
theorem c13_velocity_divergence {α : ℝ} (hα1 : 1 < α) (c : ℝ)
    (I : Set ℝ) (F : ℝ → ℝ → ℝ) (hF : c13_graph_class I F) :
    (∀ t ∈ I, ContDiffOn ℝ 1 (fun X => c13_graph_velocity α c F X t) {X | X 1 ≠ F (X 0) t}) ∧
    (∀ t ∈ I, ∀ X : c13_E, X 1 ≠ F (X 0) t →
      fderiv ℝ (fun Y => c13_graph_velocity α c F Y t) X (EuclideanSpace.single 0 1) 0 +
        fderiv ℝ (fun Y => c13_graph_velocity α c F Y t) X (EuclideanSpace.single 1 1) 1 = 0) ∧
    ContinuousOn (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2)
      {p | p.2 ∈ I ∧ p.1 1 ≠ F (p.1 0) p.2} ∧
    ContinuousOn (fun p : c13_E × ℝ => fderiv ℝ (fun Y => c13_graph_velocity α c F Y p.2) p.1)
      {p | p.2 ∈ I ∧ p.1 1 ≠ F (p.1 0) p.2} := by
  have hopen : ∀ t ∈ I, IsOpen {Y : c13_E | Y 1 ≠ F (Y 0) t} := fun t ht =>
    isOpen_ne_fun (by fun_prop)
      ((c13g_aux_slice_contDiff hF ht).continuous.comp (by fun_prop))
  have hfd : ∀ t ∈ I, ∀ X : c13_E, X 1 ≠ F (X 0) t →
      HasFDerivAt (fun Y => c13_graph_velocity α c F Y t)
        ((-c) • ∫ s, c13v_aux_DK α F X t s) X := by
    intro t ht X hX
    have h := ((c13v_aux_hasFDerivAt_int hα1 hF ht hX).2).const_smul (-c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [(hopen t ht).mem_nhds hX] with Y hY
    exact c13v_aux_U_eq α c F hY
  have hfderiv : ∀ t ∈ I, ∀ X : c13_E, X 1 ≠ F (X 0) t →
      fderiv ℝ (fun Y => c13_graph_velocity α c F Y t) X =
        (-c) • ∫ s, c13v_aux_DK α F X t s := fun t ht X hX => (hfd t ht X hX).fderiv
  have hcontD : ∀ p : c13_E × ℝ, p.2 ∈ I → p.1 1 ≠ F (p.1 0) p.2 →
      ContinuousAt (fun p : c13_E × ℝ =>
        fderiv ℝ (fun Y => c13_graph_velocity α c F Y p.2) p.1) p := by
    rintro ⟨X₀, t₀⟩ ht hoff
    obtain ⟨M, d₀, -, hd0, -, hev⟩ := c13v_aux_local hF (p₀ := (X₀, t₀)) ht hoff
    have h := ((c13v_aux_cont_int hα1 hF ht hoff).2).const_smul (-c)
    refine h.congr ?_
    filter_upwards [hev] with p hp
    exact (hfderiv p.2 hp.1 p.1 (c13v_aux_off_of_le hd0 hp.2.2.2)).symm
  have hcontU : ∀ p : c13_E × ℝ, p.2 ∈ I → p.1 1 ≠ F (p.1 0) p.2 →
      ContinuousAt (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2) p := by
    rintro ⟨X₀, t₀⟩ ht hoff
    obtain ⟨M, d₀, -, hd0, -, hev⟩ := c13v_aux_local hF (p₀ := (X₀, t₀)) ht hoff
    have h := ((c13v_aux_cont_int hα1 hF ht hoff).1).const_smul (-c)
    refine h.congr ?_
    filter_upwards [hev] with p hp
    exact (c13v_aux_U_eq α c F (c13v_aux_off_of_le hd0 hp.2.2.2)).symm
  refine ⟨?_, ?_, fun p hp => (hcontU p hp.1 hp.2).continuousWithinAt,
    fun p hp => (hcontD p hp.1 hp.2).continuousWithinAt⟩
  · intro t ht
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderiv_of_isOpen (hopen t ht)]
    refine ⟨fun X hX => (hfd t ht X hX).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    intro X hX
    have h := (hcontD (X, t) ht hX).comp (x := X)
      (g := fun p : c13_E × ℝ => fderiv ℝ (fun Y => c13_graph_velocity α c F Y p.2) p.1)
      (continuous_id.prodMk continuous_const).continuousAt
    exact h.continuousWithinAt
  · intro t ht X hX
    have hFd : Differentiable ℝ (fun x => F x t) :=
      (c13g_aux_slice_contDiff hF ht).differentiable (by simp)
    rw [hfderiv t ht X hX]
    have : CompleteSpace (c13_E →L[ℝ] c13_E) := FiniteDimensional.complete ℝ _
    obtain ⟨hDKi, -⟩ := c13v_aux_hasFDerivAt_int hα1 hF ht hX
    set L0 : (c13_E →L[ℝ] c13_E) →L[ℝ] ℝ := (EuclideanSpace.proj (0 : Fin 2)).comp
      (ContinuousLinearMap.apply ℝ c13_E (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) with hL0
    set L1 : (c13_E →L[ℝ] c13_E) →L[ℝ] ℝ := (EuclideanSpace.proj (1 : Fin 2)).comp
      (ContinuousLinearMap.apply ℝ c13_E (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) with hL1
    have e0 : ((-c) • ∫ s, c13v_aux_DK α F X t s) (EuclideanSpace.single 0 1) 0 =
        -c * L0 (∫ s, c13v_aux_DK α F X t s) := by simp [hL0]
    have e1 : ((-c) • ∫ s, c13v_aux_DK α F X t s) (EuclideanSpace.single 1 1) 1 =
        -c * L1 (∫ s, c13v_aux_DK α F X t s) := by simp [hL1]
    rw [e0, e1, ← L0.integral_comp_comm hDKi, ← L1.integral_comp_comm hDKi, ← mul_add,
      ← integral_add (L0.integrable_comp hDKi) (L1.integrable_comp hDKi)]
    have hpt : ∀ s, L0 (c13v_aux_DK α F X t s) + L1 (c13v_aux_DK α F X t s) =
        -α * ‖X - c13_pt s (F s t)‖ ^ (-α - 2) *
          ((X 0 - s) + (X 1 - F s t) * deriv (fun x => F x t) s) := by
      intro s
      simp [hL0, hL1, c13v_aux_DK, EuclideanSpace.inner_single_right]
      ring
    have hint : Integrable (fun s => -α * ‖X - c13_pt s (F s t)‖ ^ (-α - 2) *
          ((X 0 - s) + (X 1 - F s t) * deriv (fun x => F x t) s)) :=
      ((L0.integrable_comp hDKi).add (L1.integrable_comp hDKi)).congr (ae_of_all _ hpt)
    have hz := c13v_aux_div_scalar (by linarith) hFd X hX hint
    simp_rw [hpt]
    rw [hz, mul_zero]


end GSQG
