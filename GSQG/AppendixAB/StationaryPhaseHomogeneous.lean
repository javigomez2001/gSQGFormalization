import GSQG.AppendixAB.StationaryPhaseCompact

/-!
# Appendix B: stationary phase, far part and homogeneous-phase assembly (toolbox for Lemma B.3; blueprint ch. 03)

Blueprint sublemmas (with their blueprint Lean names) and proofs of the nodes `c03_sp_far`
and `appendix_homogeneous_stationary_phase` under the prefix `c03f_` (same statements as the public ones in
`AppendixAB/Statements.lean`). Helpers: `c03f_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### Statements -/

theorem c03f_aux_phase_deriv (p y : ℝ) (hp : 0 < p) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun ξ => Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)))
      (Complex.I * ((y - ξ ^ p : ℝ) : ℂ) * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) ξ := by
  have hp1' : p + 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (c03_sp_phi p y) (y - ξ ^ p) ξ := by
    unfold c03_sp_phi
    have := ((hasDerivAt_id ξ).const_mul y).sub
      ((Real.hasDerivAt_rpow_const (p := p + 1) (Or.inl hξ.ne')).div_const (p + 1))
    refine this.congr_deriv ?_
    rw [add_sub_cancel_right]; field_simp
  have := (h1.ofReal_comp.const_mul Complex.I).cexp
  convert this using 1; ring


section farIBP
variable (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1)
    (a : ℝ → ℂ) (ha : a ∈ c03_sp_symbol m) (y : ℝ) (hy : 0 < y)

include hp hp1 hχ hχs hχ1 hχ01 ha hy

/-- Differentiability of `ξ ↦ a_l(y,ξ)` on `(0,∞)`. -/
theorem c03f_aux_farAmp_diff (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    DifferentiableAt ℝ (fun ξ => c03c_farAmp p χ a l y ξ) ξ := by
  have hs := ((c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).1 a ha l).1
  have h1 := (hs.contDiffAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds
    (show (y, ξ) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) from ⟨hy, hξ⟩))).differentiableAt (by simp)
  exact h1.comp ξ ((hasDerivAt_const ξ y).prodMk (hasDerivAt_id ξ)).differentiableAt

/-- The quotient `u_l = a_l/(i φ')` is differentiable on `(0,∞)` with derivative `a_{l+1}`. -/
theorem c03f_aux_u_hasDerivAt (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun ξ => c03c_farAmp p χ a l y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ)))
      (c03c_farAmp p χ a (l + 1) y ξ) ξ := by
  have hvan := ((c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).1 a ha l).2
  have hd : DifferentiableAt ℝ
      (fun ξ => c03c_farAmp p χ a l y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))) ξ := by
    by_cases h : y - ξ ^ p = 0
    · have hl : lambda0 p y = ξ := by
        unfold lambda0
        rw [show y = ξ ^ p by linarith, one_div, Real.rpow_rpow_inv hξ.le hp.ne']
      have hL : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
      have hev : (fun ξ => c03c_farAmp p χ a l y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))) =ᶠ[𝓝 ξ]
          fun _ => 0 := by
        filter_upwards [Ioo_mem_nhds (show 3 * lambda0 p y / 4 < ξ by linarith)
          (show ξ < 3 * lambda0 p y / 2 by linarith)] with z hz
        rw [hvan y z hy (by linarith [hz.1]) (Or.inr ⟨hz.1.le, hz.2.le⟩), zero_div]
      exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hev
    · have hden : HasDerivAt (fun ξ : ℝ => Complex.I * ((y - ξ ^ p : ℝ) : ℂ))
          (Complex.I * ((0 - p * ξ ^ (p - 1) : ℝ) : ℂ)) ξ :=
        (((hasDerivAt_const ξ y).sub (Real.hasDerivAt_rpow_const (Or.inl hξ.ne'))).ofReal_comp).const_mul
          Complex.I
      refine (c03f_aux_farAmp_diff p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy l hξ).div
        hden.differentiableAt ?_
      exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 h)
  exact hd.hasDerivAt

/-- `u_l (e^{iφ})' = a_l e^{iφ}` on `(0,∞)`. -/
theorem c03f_aux_u_mul (l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    c03c_farAmp p χ a l y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ)) *
        (Complex.I * ((y - ξ ^ p : ℝ) : ℂ) * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) =
      c03c_farAmp p χ a l y ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)) := by
  have hvan := ((c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).1 a ha l).2
  by_cases h : y - ξ ^ p = 0
  · have hl : lambda0 p y = ξ := by
      unfold lambda0
      rw [show y = ξ ^ p by linarith, one_div, Real.rpow_rpow_inv hξ.le hp.ne']
    rw [hvan y ξ hy hξ (Or.inr ⟨by linarith, by linarith⟩)]; simp
  · have : Complex.I * ((y - ξ ^ p : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 h)
    rw [mul_comm (Complex.I * ((y - ξ ^ p : ℝ) : ℂ)), ← mul_assoc, mul_right_comm,
      div_mul_cancel₀ _ this]

/-- One integration by parts on `[1,R]`. -/
theorem c03f_aux_ibp_step (l : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (∫ ξ in (1 : ℝ)..R, c03c_farAmp p χ a l y ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) =
      c03c_farAmp p χ a l y R * Complex.exp (Complex.I * (c03_sp_phi p y R : ℂ)) /
          (Complex.I * ((y - R ^ p : ℝ) : ℂ)) -
        ∫ ξ in (1 : ℝ)..R, c03c_farAmp p χ a (l + 1) y ξ *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)) := by
  have hvan := ((c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).1 a ha l).2
  have hpos : ∀ x ∈ uIcc (1 : ℝ) R, 0 < x := fun x hx => by
    rw [uIcc_of_le hR] at hx; linarith [hx.1]
  have hu := fun x (hx : 0 < x) => c03f_aux_u_hasDerivAt p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy l hx
  have hv := fun x (hx : 0 < x) => c03f_aux_phase_deriv p y hp (ξ := x) hx
  have hmm : min (1 : ℝ) R = 1 := min_eq_left hR
  have hMM : max (1 : ℝ) R = R := max_eq_right hR
  have hcu : ContinuousOn (fun ξ => c03c_farAmp p χ a l y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ)))
      (uIcc 1 R) := fun x hx => (hu x (hpos x hx)).continuousAt.continuousWithinAt
  have hcv : ContinuousOn (fun ξ => Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) (uIcc 1 R) :=
    fun x hx => (hv x (hpos x hx)).continuousAt.continuousWithinAt
  have hca : ContinuousOn (fun ξ => c03c_farAmp p χ a (l + 1) y ξ) (uIcc 1 R) := fun x hx =>
    (c03f_aux_farAmp_diff p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy (l + 1)
      (hpos x hx)).continuousAt.continuousWithinAt
  have hcv' : ContinuousOn (fun ξ => Complex.I * ((y - ξ ^ p : ℝ) : ℂ) *
      Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) (uIcc 1 R) := by
    refine (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.sub (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (hpos x hx).ne'))))).mul hcv
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcu hcv
    (fun x hx => hu x (by rw [hmm] at hx; linarith [hx.1]))
    (fun x hx => hv x (by rw [hmm] at hx; linarith [hx.1]))
    hca.intervalIntegrable hcv'.intervalIntegrable
  have h1 : c03c_farAmp p χ a l y 1 = 0 := hvan y 1 hy one_pos (Or.inl le_rfl)
  rw [h1, zero_div, zero_mul, sub_zero] at ibp
  have hint : (∫ ξ in (1 : ℝ)..R, c03c_farAmp p χ a l y ξ *
      Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) = ∫ ξ in (1 : ℝ)..R,
      c03c_farAmp p χ a l y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ)) *
        (Complex.I * ((y - ξ ^ p : ℝ) : ℂ) * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) :=
    intervalIntegral.integral_congr fun x hx =>
      (c03f_aux_u_mul p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy l (hpos x hx)).symm
  rw [hint, ibp]
  ring

/-- Iterated integration by parts. -/
theorem c03f_aux_ibp_iter (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (∫ ξ in (1 : ℝ)..R, c03c_farAmp p χ a 0 y ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) =
      (∑ l ∈ Finset.range n, (-1 : ℂ) ^ l * (c03c_farAmp p χ a l y R *
        Complex.exp (Complex.I * (c03_sp_phi p y R : ℂ)) / (Complex.I * ((y - R ^ p : ℝ) : ℂ)))) +
        (-1 : ℂ) ^ n * ∫ ξ in (1 : ℝ)..R, c03c_farAmp p χ a n y ξ *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, c03f_aux_ibp_step p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy n hR, Finset.sum_range_succ,
      pow_succ]
    ring

/-- Pointwise bound `|a_l(y,ξ)| ≤ D ξ^{m-l} (y+ξ^p)^{-l}` for `ξ ≥ 1`. -/
theorem c03f_aux_farAmp_bound (l : ℕ) : ∃ D, 0 < D ∧ ∀ ξ : ℝ, 1 ≤ ξ →
    ‖c03c_farAmp p χ a l y ξ‖ ≤ D * ξ ^ (m - l) * (y + ξ ^ p) ^ (-(l : ℝ)) := by
  choose Ck hCk using ha.2.2
  obtain ⟨D, hD, hb⟩ := (c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).2 l 0 0 Ck
  refine ⟨D, hD, fun ξ hξ => ?_⟩
  have := hb a ha (fun i _ ξ hξ => hCk i ξ hξ) y ξ hy hξ
  simpa using this

end farIBP

theorem c03f_aux_norm_expI (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

/-- Blueprint: lem:c03_sp_far_limit_identity.  For `m < p`, `y > 0`, `n ≥ 1`: `a_n(y,·)` is
integrable on `[1,∞)`, `lim_R ∫₁^R g_y e^{iφ_y} = (-1)^n ∫₁^∞ a_n e^{iφ_y}`, the boundary terms
`a_l(y,R) e^{iφ_y(R)}/(i(y-R^p))` (`l < n`) tend to `0`, and `a_l(y,1) = 0`. -/
theorem c03_sp_far_limit_identity (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (hm : m < p) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1)
    (a : ℝ → ℂ) (ha : a ∈ c03_sp_symbol m) (y : ℝ) (hy : 0 < y) (n : ℕ) (hn : 1 ≤ n) :
    IntegrableOn (fun ξ => c03c_farAmp p χ a n y ξ) (Ioi 1) ∧
    Tendsto (fun R : ℝ => ∫ ξ in (1 : ℝ)..R,
        c03c_farAmp p χ a 0 y ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) atTop
      (𝓝 ((-1 : ℂ) ^ n * ∫ ξ in Ioi (1 : ℝ),
        c03c_farAmp p χ a n y ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)))) ∧
    (∀ l < n, Tendsto (fun R : ℝ => c03c_farAmp p χ a l y R *
        Complex.exp (Complex.I * (c03_sp_phi p y R : ℂ)) / (Complex.I * ((y - R ^ p : ℝ) : ℂ)))
      atTop (𝓝 0)) ∧
    ∀ l : ℕ, c03c_farAmp p χ a l y 1 = 0 := by
  have hvan := fun l => ((c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).1 a ha l).2
  have hcont : ∀ l, ContinuousOn (fun ξ => c03c_farAmp p χ a l y ξ) (Ioi 1) := fun l x hx =>
    (c03f_aux_farAmp_diff p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy l
      (lt_trans zero_lt_one (show (1 : ℝ) < x from hx))).continuousAt.continuousWithinAt
  -- integrability for every `l ≥ 1`
  have hint : ∀ l, 1 ≤ l → IntegrableOn (fun ξ => c03c_farAmp p χ a l y ξ) (Ioi 1) := by
    intro l hl
    obtain ⟨D, hD, hb⟩ := c03f_aux_farAmp_bound p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy l
    have hexp : m - l - p * l < -1 := by
      have : (1 : ℝ) ≤ l := by exact_mod_cast hl
      nlinarith
    have hmaj : IntegrableOn (fun ξ : ℝ => D * ξ ^ (m - l - p * l)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt hexp one_pos).const_mul D
    refine hmaj.mono' ((hcont l).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun ξ hξ => ?_
    have hξ1 : (1 : ℝ) ≤ ξ := le_of_lt hξ
    have hξ0 : 0 < ξ := by linarith
    have hξp : 0 < ξ ^ p := Real.rpow_pos_of_pos hξ0 _
    refine (hb ξ hξ1).trans ?_
    have h1 : (y + ξ ^ p) ^ (-(l : ℝ)) ≤ (ξ ^ p) ^ (-(l : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hξp (by linarith) (by simp)
    rw [← Real.rpow_mul hξ0.le] at h1
    calc D * ξ ^ (m - l) * (y + ξ ^ p) ^ (-(l : ℝ)) ≤ D * ξ ^ (m - l) * ξ ^ (p * -(l : ℝ)) := by
          gcongr
      _ = D * ξ ^ (m - l - p * l) := by
          rw [mul_assoc, ← Real.rpow_add hξ0]; ring_nf
  -- boundary terms
  obtain ⟨c, hc, hcb⟩ := (c03_sp_far_phase_bounds p hp hp1).1
  have hbdry : ∀ l : ℕ, Tendsto (fun R : ℝ => c03c_farAmp p χ a l y R *
      Complex.exp (Complex.I * (c03_sp_phi p y R : ℂ)) / (Complex.I * ((y - R ^ p : ℝ) : ℂ)))
      atTop (𝓝 0) := by
    intro l
    obtain ⟨D, hD, hb⟩ := c03f_aux_farAmp_bound p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy l
    set e : ℝ := p - m + l * (1 + p) with he
    have he0 : 0 < e := by
      have : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      rw [he]; nlinarith
    have hlim : Tendsto (fun R : ℝ => D / c * R ^ (-e)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop he0).const_mul (D / c)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (max 1 (3 * lambda0 p y / 2))] with R hR
    have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
    have hR0 : 0 < R := by linarith
    have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR0 _
    have hph := hcb y R hy hR0 (Or.inr (le_trans (le_max_right _ _) hR))
    have hyR : 0 < |y - R ^ p| := lt_of_lt_of_le (by positivity) hph
    rw [norm_div, norm_mul, c03f_aux_norm_expI, mul_one, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hyR]
    have h1 : (y + R ^ p) ^ (-(l : ℝ)) ≤ (R ^ p) ^ (-(l : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hRp (by linarith) (by simp)
    rw [← Real.rpow_mul hR0.le] at h1
    have h2 : R ^ (-e) * R ^ p = R ^ (m - l) * R ^ (p * -(l : ℝ)) := by
      rw [← Real.rpow_add hR0, ← Real.rpow_add hR0, he]; ring_nf
    calc ‖c03c_farAmp p χ a l y R‖ ≤ D * R ^ (m - l) * (y + R ^ p) ^ (-(l : ℝ)) := hb R hR1
      _ ≤ D * R ^ (m - l) * R ^ (p * -(l : ℝ)) := by gcongr
      _ = D / c * R ^ (-e) * (c * R ^ p) := by
          rw [show D / c * R ^ (-e) * (c * R ^ p) = D * (R ^ (-e) * R ^ p) by field_simp, h2]; ring
      _ ≤ D / c * R ^ (-e) * |y - R ^ p| := by
          gcongr; exact le_trans (by nlinarith) hph
  refine ⟨hint n hn, ?_, fun l _ => hbdry l, fun l => hvan l y 1 hy one_pos (Or.inl le_rfl)⟩
  -- the limit
  have hintn : IntegrableOn (fun ξ => c03c_farAmp p χ a n y ξ *
      Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) (Ioi 1) := by
    refine (hint n hn).norm.mono' ?_ ((ae_restrict_mem measurableSet_Ioi).mono fun ξ _ => ?_)
    · refine ((hcont n).mul ?_).aestronglyMeasurable measurableSet_Ioi
      exact fun x hx => (c03f_aux_phase_deriv p y hp (ξ := x)
        (lt_trans zero_lt_one (show (1 : ℝ) < x from hx))).continuousAt.continuousWithinAt
    · rw [norm_mul, c03f_aux_norm_expI, mul_one]
  have hT := (tendsto_finsetSum (Finset.range n) fun l _ => (hbdry l).const_mul ((-1 : ℂ) ^ l)).add
    ((intervalIntegral_tendsto_integral_Ioi 1 hintn tendsto_id).const_mul ((-1 : ℂ) ^ n))
  simp only [mul_zero, Finset.sum_const_zero, zero_add] at hT
  refine hT.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with R hR
  exact (c03f_aux_ibp_iter p m hp hp1 χ hχ hχs hχ1 hχ01 a ha y hy n hR).symm

/-- `∂_y^k e^{iφ_y(ξ)} = (iξ)^k e^{iφ_y(ξ)}`. -/
theorem c03f_aux_iter_phase_y (p ξ : ℝ) (k : ℕ) :
    iteratedDeriv k (fun y => Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) =
      fun y => (Complex.I * ξ) ^ k * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)) := by
  set g : ℝ → ℂ := fun y => Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)) with hg
  have hgd : ∀ y, HasDerivAt g (Complex.I * ξ * g y) y := by
    intro y
    have h1 : HasDerivAt (fun y => c03_sp_phi p y ξ) ξ y := by
      unfold c03_sp_phi
      simpa using ((hasDerivAt_id y).mul_const ξ).sub_const (ξ ^ (p + 1) / (p + 1))
    have := (h1.ofReal_comp.const_mul Complex.I).cexp
    convert this using 1; simp only [hg]; ring
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ((c03_sp_phi p y ξ : ℝ) : ℂ)) := by
      unfold c03_sp_phi
      exact Complex.ofRealCLM.contDiff.comp ((contDiff_id.mul contDiff_const).sub contDiff_const)
    exact (contDiff_const.mul this).cexp
  induction k with
  | zero => simp [hg]
  | succ k ih =>
    rw [iteratedDeriv_succ', show deriv g = fun y => Complex.I * ξ * g y from
      funext fun y => (hgd y).deriv]
    funext y
    rw [iteratedDeriv_const_mul _ ((hgc.of_le (by exact_mod_cast le_top)).contDiffAt), ih]
    ring

/-- Leibniz bound in `y` for `a_n(y,ξ) e^{iφ_y(ξ)}`. -/
theorem c03f_aux_dom_leibniz (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1)
    (a : ℝ → ℂ) (ha : a ∈ c03_sp_symbol m) (n j : ℕ) {y ξ : ℝ} (hy : 0 < y) (hξ : 1 ≤ ξ) :
    ‖iteratedDeriv j (fun y' => c03c_farAmp p χ a n y' ξ *
        Complex.exp (Complex.I * (c03_sp_phi p y' ξ : ℂ))) y‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedDeriv i (fun y' => c03c_farAmp p χ a n y' ξ) y‖ * ξ ^ (j - i) := by
  have hξ0 : 0 < ξ := by linarith
  have hs := ((c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).1 a ha n).1
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => c03c_farAmp p χ a n y' ξ) (Ioi 0) :=
    hs.comp (f := fun y' : ℝ => (y', ξ)) (contDiffOn_id.prodMk contDiffOn_const)
      (fun y' hy' => ⟨hy', hξ0⟩)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)))
      (Ioi 0) := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ((c03_sp_phi p y ξ : ℝ) : ℂ)) := by
      unfold c03_sp_phi
      exact Complex.ofRealCLM.contDiff.comp ((contDiff_id.mul contDiff_const).sub contDiff_const)
    exact (contDiff_const.mul this).cexp.contDiffOn
  refine (c03s_aux_leibniz hA hE hy j).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [c03f_aux_iter_phase_y, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ0, c03f_aux_norm_expI, mul_one]

/-- Blueprint: lem:c03_sp_far_domination.  For `y, ξ ≥ 1`:
`|∂_y^j(a_n e^{iφ_y})| ≤ C ξ^{m-n+j}(y+ξ^p)^{-n} ≤ C y^{-n/2} ξ^{m-n+j-pn/2}`, with
`C = C(p,m,n,j,χ_sp,C_0,…,C_{n+j+2})`; on a compact `[y₁,y₂] ⊂ (0,∞)` the same derivatives are
bounded by `C_J ξ^{m-(p+1)n+j}` (`ξ ≥ 1`). Constants are independent of any truncation radius. -/
theorem c03_sp_far_domination (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) :
    (∀ n j : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ i ≤ n + j + 2, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) →
      ∀ y ξ : ℝ, 1 ≤ y → 1 ≤ ξ →
        ‖iteratedDeriv j (fun y' => c03c_farAmp p χ a n y' ξ *
            Complex.exp (Complex.I * (c03_sp_phi p y' ξ : ℂ))) y‖ ≤
          C * ξ ^ (m - n + j) * (y + ξ ^ p) ^ (-(n : ℝ)) ∧
        C * ξ ^ (m - n + j) * (y + ξ ^ p) ^ (-(n : ℝ)) ≤
          C * y ^ (-(n : ℝ) / 2) * ξ ^ (m - n + j - p * n / 2)) ∧
    ∀ n j : ℕ, ∀ Ck : ℕ → ℝ, ∀ y₁ y₂ : ℝ, 0 < y₁ → ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ i ≤ n + j + 2, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) →
      ∀ y ∈ Icc y₁ y₂, ∀ ξ : ℝ, 1 ≤ ξ →
        ‖iteratedDeriv j (fun y' => c03c_farAmp p χ a n y' ξ *
            Complex.exp (Complex.I * (c03_sp_phi p y' ξ : ℂ))) y‖ ≤
          C * ξ ^ (m - (p + 1) * n + j) := by
  have hSI := (c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).2
  constructor
  · intro n j Ck
    choose Dd hDd hb using fun i => hSI n 0 i Ck
    set S : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Dd i with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hDd i).le
    refine ⟨S + 1, by positivity, fun a ha hCk y ξ hy hξ => ⟨?_, ?_⟩⟩
    · have hy0 : 0 < y := by linarith
      have hξ0 : 0 < ξ := by linarith
      have hW : 0 ≤ ξ ^ (m - n) * (y + ξ ^ p) ^ (-(n : ℝ)) := by positivity
      refine (c03f_aux_dom_leibniz p m hp hp1 χ hχ hχs hχ1 hχ01 a ha n j hy0 hξ).trans ?_
      calc _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            (Dd i * (ξ ^ (m - n) * (y + ξ ^ p) ^ (-(n : ℝ)))) * ξ ^ j := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            have h1 := hb i a ha (fun i' hi'' ξ' hξ' => hCk i' (by omega) ξ' hξ') y ξ hy0 hξ
            simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1
            have hyi : y ^ (-(i : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by simp)
            have h2 : ‖iteratedDeriv i (fun y' => c03c_farAmp p χ a n y' ξ) y‖ ≤
                Dd i * (ξ ^ (m - n) * (y + ξ ^ p) ^ (-(n : ℝ))) := by
              refine h1.trans ?_
              rw [mul_assoc, mul_assoc]
              refine mul_le_mul_of_nonneg_left ?_ (hDd i).le
              calc ξ ^ (m - n) * ((y + ξ ^ p) ^ (-(n : ℝ)) * y ^ (-(i : ℝ)))
                  ≤ ξ ^ (m - n) * ((y + ξ ^ p) ^ (-(n : ℝ)) * 1) := by gcongr
                _ = _ := by ring
            have h3 : ξ ^ (j - i) ≤ ξ ^ j := pow_le_pow_right₀ hξ (Nat.sub_le j i)
            exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h3 (by positivity)
              (mul_nonneg (by positivity) (mul_nonneg (hDd i).le hW))
        _ = S * (ξ ^ (m - n) * ξ ^ j) * (y + ξ ^ p) ^ (-(n : ℝ)) := by
            rw [hS]; simp only [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ (S + 1) * ξ ^ (m - n + j) * (y + ξ ^ p) ^ (-(n : ℝ)) := by
            rw [show ξ ^ (m - n) * ξ ^ j = ξ ^ (m - n + j) by
              rw [Real.rpow_add hξ0, Real.rpow_natCast]]
            gcongr; linarith
    · have hy0 : 0 < y := by linarith
      have hξ0 : 0 < ξ := by linarith
      set u : ℝ := y ^ (1 / 2 : ℝ)
      set v : ℝ := ξ ^ (p / 2)
      have hu : 0 < u := Real.rpow_pos_of_pos hy0 _
      have hv : 0 < v := Real.rpow_pos_of_pos hξ0 _
      have hu2 : u ^ 2 = y := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
      have hv2 : v ^ 2 = ξ ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]; congr 1; push_cast; ring
      have huv : u * v ≤ y + ξ ^ p := by nlinarith [sq_nonneg (u - v)]
      have h1 : (y + ξ ^ p) ^ (-(n : ℝ)) ≤ (u * v) ^ (-(n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) huv (by simp)
      have h2 : (u * v) ^ (-(n : ℝ)) * ξ ^ (m - n + j) =
          y ^ (-(n : ℝ) / 2) * ξ ^ (m - n + j - p * n / 2) := by
        have hx1 : (u * v) ^ (-(n : ℝ)) = y ^ (-(n : ℝ) / 2) * ξ ^ (-(p * n) / 2) := by
          rw [Real.mul_rpow hu.le hv.le, ← Real.rpow_mul hy0.le, ← Real.rpow_mul hξ0.le]
          congr 2 <;> ring
        have hx2 : ξ ^ (-(p * n) / 2) * ξ ^ (m - n + j) = ξ ^ (m - n + j - p * n / 2) := by
          rw [← Real.rpow_add hξ0]; congr 1; ring
        rw [hx1, mul_assoc, hx2]
      calc (S + 1) * ξ ^ (m - n + j) * (y + ξ ^ p) ^ (-(n : ℝ))
          ≤ (S + 1) * ξ ^ (m - n + j) * (u * v) ^ (-(n : ℝ)) := by gcongr
        _ = (S + 1) * ((u * v) ^ (-(n : ℝ)) * ξ ^ (m - n + j)) := by ring
        _ = _ := by rw [h2]; ring
  · intro n j Ck y₁ y₂ hy₁
    choose Dd hDd hb using fun i => hSI n 0 i Ck
    set S : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Dd i * y₁ ^ (-(i : ℝ))) with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
      (mul_nonneg (hDd i).le (by positivity))
    refine ⟨S + 1, by positivity, fun a ha hCk y hyI ξ hξ => ?_⟩
    have hy0 : 0 < y := lt_of_lt_of_le hy₁ hyI.1
    have hξ0 : 0 < ξ := by linarith
    have hξp : 0 < ξ ^ p := Real.rpow_pos_of_pos hξ0 _
    refine (c03f_aux_dom_leibniz p m hp hp1 χ hχ hχs hχ1 hχ01 a ha n j hy0 hξ).trans ?_
    have hW : 0 ≤ ξ ^ (m - n) * ξ ^ (p * -(n : ℝ)) := by positivity
    calc _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (Dd i * y₁ ^ (-(i : ℝ)) * (ξ ^ (m - n) * ξ ^ (p * -(n : ℝ)))) * ξ ^ j := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have h1 := hb i a ha (fun i' hi'' ξ' hξ' => hCk i' (by omega) ξ' hξ') y ξ hy0 hξ
          simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1
          have hyi : y ^ (-(i : ℝ)) ≤ y₁ ^ (-(i : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hy₁ hyI.1 (by simp)
          have hpn : (y + ξ ^ p) ^ (-(n : ℝ)) ≤ ξ ^ (p * -(n : ℝ)) := by
            rw [Real.rpow_mul hξ0.le]
            exact Real.rpow_le_rpow_of_nonpos hξp (by linarith) (by simp)
          have h2 : ‖iteratedDeriv i (fun y' => c03c_farAmp p χ a n y' ξ) y‖ ≤
              Dd i * y₁ ^ (-(i : ℝ)) * (ξ ^ (m - n) * ξ ^ (p * -(n : ℝ))) := by
            refine h1.trans ?_
            have : 0 ≤ ξ ^ (m - n) := by positivity
            calc Dd i * ξ ^ (m - n) * (y + ξ ^ p) ^ (-(n : ℝ)) * y ^ (-(i : ℝ))
                ≤ Dd i * ξ ^ (m - n) * ξ ^ (p * -(n : ℝ)) * y₁ ^ (-(i : ℝ)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hpn (mul_nonneg (hDd i).le this)) hyi
                    (by positivity) (mul_nonneg (mul_nonneg (hDd i).le this) (by positivity))
              _ = _ := by ring
          have h3 : ξ ^ (j - i) ≤ ξ ^ j := pow_le_pow_right₀ hξ (Nat.sub_le j i)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h3 (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (hDd i).le (by positivity)) hW))
      _ = S * (ξ ^ (m - n) * ξ ^ (p * -(n : ℝ)) * ξ ^ j) := by
          rw [hS, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (S + 1) * ξ ^ (m - (p + 1) * n + j) := by
          rw [show ξ ^ (m - n) * ξ ^ (p * -(n : ℝ)) * ξ ^ j = ξ ^ (m - (p + 1) * n + j) by
            rw [← Real.rpow_natCast, ← Real.rpow_add hξ0, ← Real.rpow_add hξ0]; congr 1; ring]
          gcongr; linarith

/-- `y`-derivatives of a jointly smooth function are jointly smooth. -/
theorem c03f_aux_iter_joint {F : ℝ → ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) (Ioi 0 ×ˢ Ioi 1)) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => iteratedDeriv j (fun y => F y q.2) q.1)
      (Ioi 0 ×ˢ Ioi 1) := by
  induction j with
  | zero => exact hF.congr fun q _ => by simp [Function.uncurry]
  | succ j ih =>
    rw [contDiffOn_infty]
    intro n
    have h1 : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
        (Function.uncurry fun (y ξ : ℝ) => iteratedDeriv j (fun y => F y ξ) y) (Ioi 0 ×ˢ Ioi 1) :=
      ih.of_le (by exact_mod_cast le_top)
    have h2 := (h1.fderiv_left isOpen_Ioi)
    have h3 : ContDiffOn ℝ n (fun x : ℝ × ℝ =>
        (fderiv ℝ (fun y => iteratedDeriv j (fun y => F y x.2) y) x.1) 1) (Ioi 0 ×ˢ Ioi 1) :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).contDiff.comp_contDiffOn h2)
    refine h3.congr fun q _ => ?_
    simp only [iteratedDeriv_succ, fderiv_apply_one_eq_deriv]

/-- Proposed blueprint node (supports `lem:c03_sp_far`): differentiation of a parametric integral
over `(1,∞)` to a finite order `N`, under joint smoothness and locally uniform integrable majorants
of the `y`-derivatives up to order `N`. -/
theorem c03f_aux_param_integral (F : ℝ → ℝ → ℂ) (N : ℕ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) (Ioi 0 ×ˢ Ioi 1))
    (hdom : ∀ j ≤ N, ∀ y₁ y₂ : ℝ, 0 < y₁ → ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 1) ∧
      ∀ y ∈ Icc y₁ y₂, ∀ ξ ∈ Ioi (1 : ℝ), ‖iteratedDeriv j (fun y => F y ξ) y‖ ≤ g ξ) :
    ContDiffOn ℝ N (fun y => ∫ ξ in Ioi (1 : ℝ), F y ξ) (Ioi 0) ∧
    ∀ j ≤ N, ∀ y : ℝ, 0 < y → iteratedDeriv j (fun y => ∫ ξ in Ioi (1 : ℝ), F y ξ) y =
      ∫ ξ in Ioi (1 : ℝ), iteratedDeriv j (fun y => F y ξ) y := by
  set G : ℕ → ℝ → ℝ → ℂ := fun j y ξ => iteratedDeriv j (fun y => F y ξ) y with hG
  have hGs := c03f_aux_iter_joint hF
  -- continuity in `ξ`, differentiability in `y`
  have hcξ : ∀ j y, 0 < y → ContinuousOn (fun ξ => G j y ξ) (Ioi 1) := fun j y hy =>
    (hGs j).continuousOn.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
      (fun ξ hξ => (⟨hy, hξ⟩ : (y, ξ) ∈ Ioi (0 : ℝ) ×ˢ Ioi (1 : ℝ)))
  have hdy : ∀ j y ξ, 0 < y → 1 < ξ → HasDerivAt (fun y => G j y ξ) (G (j + 1) y ξ) y := by
    intro j y ξ hy hξ
    have h1 := ((hGs j).contDiffAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds
      (show (y, ξ) ∈ Ioi (0 : ℝ) ×ˢ Ioi (1 : ℝ) from ⟨hy, hξ⟩))).differentiableAt (by simp)
    have h2 := (h1.comp y ((hasDerivAt_id y).prodMk (hasDerivAt_const y ξ)).differentiableAt).hasDerivAt
    simp only [hG, iteratedDeriv_succ]
    exact h2
  have hmeas : ∀ j y, 0 < y → AEStronglyMeasurable (fun ξ => G j y ξ) (volume.restrict (Ioi 1)) :=
    fun j y hy => (hcξ j y hy).aestronglyMeasurable measurableSet_Ioi
  -- derivative of `I_j`
  have hder : ∀ j < N, ∀ y, 0 < y → HasDerivAt (fun y => ∫ ξ in Ioi (1 : ℝ), G j y ξ)
      (∫ ξ in Ioi (1 : ℝ), G (j + 1) y ξ) y := by
    intro j hj y hy
    obtain ⟨g, hg, hgb⟩ := hdom (j + 1) hj (y / 2) (2 * y) (by linarith)
    obtain ⟨g0, hg0, hg0b⟩ := hdom j hj.le (y / 2) (2 * y) (by linarith)
    have hs : Ioo (y / 2) (2 * y) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 1))
      (F := fun y ξ => G j y ξ) (F' := fun y ξ => G (j + 1) y ξ) (bound := g) hs
      ?_ ?_ (hmeas (j + 1) y hy) ?_ hg ?_).2
    · filter_upwards [Ioi_mem_nhds hy] with z hz using hmeas j z hz
    · refine hg0.mono' (hmeas j y hy) ((ae_restrict_mem measurableSet_Ioi).mono fun ξ hξ => ?_)
      exact hg0b y ⟨by linarith, by linarith⟩ ξ hξ
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun ξ hξ z hz => ?_
      exact hgb z ⟨hz.1.le, hz.2.le⟩ ξ hξ
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun ξ hξ z hz => ?_
      exact hdy j z ξ (by linarith [hz.1]) hξ
  -- the derivative formula
  have hform : ∀ j ≤ N, ∀ y, 0 < y → iteratedDeriv j (fun y => ∫ ξ in Ioi (1 : ℝ), F y ξ) y =
      ∫ ξ in Ioi (1 : ℝ), G j y ξ := by
    intro j
    induction j with
    | zero => intro _ y _; simp [hG]
    | succ j ih =>
      intro hj y hy
      have hev : iteratedDeriv j (fun y => ∫ ξ in Ioi (1 : ℝ), F y ξ) =ᶠ[𝓝 y]
          fun y => ∫ ξ in Ioi (1 : ℝ), G j y ξ := by
        filter_upwards [Ioi_mem_nhds hy] with z hz using ih (by omega) z hz
      rw [iteratedDeriv_succ, hev.deriv_eq, (hder j (by omega) y hy).deriv]
  refine ⟨?_, hform⟩
  -- smoothness
  have hcont : ∀ j ≤ N, ContinuousOn (fun y => ∫ ξ in Ioi (1 : ℝ), G j y ξ) (Ioi 0) := by
    intro j hj y hy
    have hy0 : (0 : ℝ) < y := hy
    obtain ⟨g, hg, hgb⟩ := hdom j hj (y / 2) (2 * y) (by linarith)
    refine (continuousAt_of_dominated (bound := g) ?_ ?_ hg ?_).continuousWithinAt
    · filter_upwards [Ioi_mem_nhds hy0] with z hz using hmeas j z hz
    · filter_upwards [Ioo_mem_nhds (show y / 2 < y by linarith) (show y < 2 * y by linarith)]
        with z hz
      exact (ae_restrict_mem measurableSet_Ioi).mono fun ξ hξ => hgb z ⟨hz.1.le, hz.2.le⟩ ξ hξ
    · exact (ae_restrict_mem measurableSet_Ioi).mono fun ξ hξ =>
        (hdy j y ξ hy0 hξ).continuousAt
  have key : ContDiffOn ℝ ((N : ℕ∞) : WithTop ℕ∞) (fun y => ∫ ξ in Ioi (1 : ℝ), F y ξ) (Ioi 0) := by
    refine (contDiffOn_iff_continuousOn_differentiableOn_deriv isOpen_Ioi.uniqueDiffOn).2
      ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hj' : j ≤ N := by exact_mod_cast hj
      exact (hcont j hj').congr fun y hy => by
        rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hy, hform j hj' y hy]
    · have hj' : j < N := by exact_mod_cast hj
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      have hd := (hder j hj' y hy0).differentiableAt
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [Ioi_mem_nhds hy0] with z hz
      rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hz, hform j hj'.le z hz]
  exact key

/-- Blueprint: lem:c03_sp_far (prefixed copy of `GSQG.c03_sp_far`). -/
theorem c03f_c03_sp_far (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (hm : m < p) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) :
    (∀ a ∈ c03_sp_symbol m,
      (∀ y, 0 < y → Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
        a ξ * ((1 - χ (ξ / lambda0 p y) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) atTop (𝓝 (c03_sp_Ifar p χ a y))) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_Ifar p χ a) (Ioi 0)) ∧
    ∀ j : ℕ, ∀ M : ℝ, 0 ≤ M → ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ k ≤ k₀, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ y, 1 ≤ y → ‖iteratedDeriv j (c03_sp_Ifar p χ a) y‖ ≤ C * y ^ (-M) := by
  set F : (ℝ → ℂ) → ℕ → ℝ → ℝ → ℂ := fun a n y ξ => c03c_farAmp p χ a n y ξ *
    Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)) with hFdef
  have FD := c03_sp_far_domination p m hp hp1 χ hχ hχs hχ1 hχ01
  -- joint smoothness
  have hFs : ∀ a ∈ c03_sp_symbol m, ∀ n,
      ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (F a n)) (Ioi 0 ×ˢ Ioi 1) := by
    intro a ha n
    have h1 := ((c03_sp_far_symbol_iteration p m hp hp1 χ hχ hχs hχ1 hχ01).1 a ha n).1
    have hsub : Ioi (0 : ℝ) ×ˢ Ioi (1 : ℝ) ⊆ Ioi 0 ×ˢ Ioi 0 :=
      prod_mono subset_rfl (fun x (hx : x ∈ Ioi (1 : ℝ)) => show x ∈ Ioi (0 : ℝ) from lt_trans zero_lt_one (show (1 : ℝ) < x from hx))
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c03_sp_phi p q.1 q.2) (Ioi 0 ×ˢ Ioi 1) := by
      unfold c03_sp_phi
      exact (contDiffOn_fst.mul contDiffOn_snd).sub ((contDiffOn_snd.rpow_const_of_ne
        (fun x (hx : x ∈ Ioi (0 : ℝ) ×ˢ Ioi (1 : ℝ)) =>
          (ne_of_gt (lt_trans zero_lt_one (show (1 : ℝ) < x.2 from hx.2))))).div_const _)
    have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ =>
        Complex.exp (Complex.I * ((c03_sp_phi p q.1 q.2 : ℝ) : ℂ))) (Ioi 0 ×ˢ Ioi 1) :=
      (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn h2)).cexp
    refine ((h1.mono hsub).mul h3).congr fun q _ => ?_
    simp [hFdef, Function.uncurry]
  -- representation
  have hrep : ∀ a ∈ c03_sp_symbol m, ∀ y, 0 < y → ∀ n, 1 ≤ n →
      Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, a ξ * ((1 - χ (ξ / lambda0 p y) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) atTop
        (𝓝 ((-1 : ℂ) ^ n * ∫ ξ in Ioi (1 : ℝ), F a n y ξ)) := by
    intro a ha y hy n hn
    have FL := (c03_sp_far_limit_identity p m hp hp1 hm χ hχ hχs hχ1 hχ01 a ha y hy n hn).2.1
    refine FL.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with R hR
    rw [intervalIntegral.integral_of_le hR,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ R by linarith)]
    have hsub : Ioc (1 : ℝ) R ⊆ Ioc 0 R := fun x hx => ⟨by linarith [hx.1], hx.2⟩
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) measurableSet_Ioc hsub
      (fun ξ hξ => ?_)).symm.trans ?_
    · have h1 : ξ ≤ 1 := by
        by_contra h; exact hξ.2 ⟨lt_of_not_ge h, hξ.1.2⟩
      show a ξ * _ * _ = 0
      rw [ha.2.1 ξ ⟨hξ.1.1, h1⟩]; simp
    · rfl
  have hIfar : ∀ a ∈ c03_sp_symbol m, ∀ y, 0 < y → ∀ n, 1 ≤ n →
      c03_sp_Ifar p χ a y = (-1 : ℂ) ^ n * ∫ ξ in Ioi (1 : ℝ), F a n y ξ :=
    fun a ha y hy n hn => (hrep a ha y hy n hn).limUnder_eq
  -- integrable majorants on compacts
  have hdomK : ∀ a ∈ c03_sp_symbol m, ∀ n k : ℕ, m - (p + 1) * n + k < -1 →
      ∀ j ≤ k, ∀ y₁ y₂ : ℝ, 0 < y₁ → ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 1) ∧
        ∀ y ∈ Icc y₁ y₂, ∀ ξ ∈ Ioi (1 : ℝ), ‖iteratedDeriv j (fun y => F a n y ξ) y‖ ≤ g ξ := by
    intro a ha n k hk j hj y₁ y₂ hy₁
    choose Ck hCk using ha.2.2
    obtain ⟨C, hC, hb⟩ := FD.2 n j Ck y₁ y₂ hy₁
    refine ⟨fun ξ => C * ξ ^ (m - (p + 1) * n + k),
      (integrableOn_Ioi_rpow_of_lt hk one_pos).const_mul C, fun y hyI ξ hξ => ?_⟩
    have hξ1 : (1 : ℝ) ≤ ξ := le_of_lt hξ
    refine (hb a ha (fun i _ ξ hξ => hCk i ξ hξ) y hyI ξ hξ1).trans ?_
    show C * _ ≤ C * _
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast hj
    gcongr
  refine ⟨fun a ha => ⟨fun y hy => ?_, ?_⟩, ?_⟩
  · rw [hIfar a ha y hy 1 le_rfl]; exact hrep a ha y hy 1 le_rfl
  · rw [contDiffOn_infty]
    intro k
    set n : ℕ := ⌈(|m| + k + 1) / (p + 1)⌉₊ + 1 with hn
    have hn1 : 1 ≤ n := by omega
    have hnk : m - (p + 1) * n + k < -1 := by
      have h1 : (|m| + k + 1) / (p + 1) ≤ ⌈(|m| + k + 1) / (p + 1)⌉₊ := Nat.le_ceil _
      have h2 : (n : ℝ) = ⌈(|m| + k + 1) / (p + 1)⌉₊ + 1 := by rw [hn]; push_cast; ring
      have h3 : |m| + k + 1 ≤ (p + 1) * ⌈(|m| + k + 1) / (p + 1)⌉₊ := by
        rw [div_le_iff₀ (by linarith)] at h1; linarith
      rw [h2]; nlinarith [le_abs_self m]
    have haux := c03f_aux_param_integral (F a n) k (hFs a ha n)
      (fun j hj y₁ y₂ hy₁ => hdomK a ha n k hnk j hj y₁ y₂ hy₁)
    exact (contDiffOn_const.mul haux.1).congr fun y hy => hIfar a ha y hy n hn1
  · intro j M hM
    set n : ℕ := ⌈2 * M + |m| + j + 2⌉₊ + 1 with hn
    have hnr : (n : ℝ) ≥ 2 * M + |m| + j + 2 + 1 := by
      have := Nat.le_ceil (2 * M + |m| + j + 2)
      rw [hn]; push_cast; linarith
    have hn1 : 1 ≤ n := by omega
    have he : m - n + j - p * n / 2 < -1 := by
      have : 0 ≤ p * n / 2 := by positivity
      linarith [le_abs_self m]
    have hnk : m - (p + 1) * n + j < -1 := by
      have : 0 ≤ p * n := by positivity
      nlinarith [le_abs_self m]
    refine ⟨n + j + 2, fun Ck => ?_⟩
    obtain ⟨C, hC, hb⟩ := FD.1 n j Ck
    set e : ℝ := m - n + j - p * n / 2 with hedef
    set Ie : ℝ := ∫ ξ in Ioi (1 : ℝ), ξ ^ e with hIe
    have hIe0 : 0 ≤ Ie := setIntegral_nonneg measurableSet_Ioi fun ξ hξ =>
      Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hξ)) _
    refine ⟨C * Ie + 1, by positivity, fun a ha hCk y hy => ?_⟩
    have hy0 : 0 < y := by linarith
    have haux := c03f_aux_param_integral (F a n) j (hFs a ha n)
      (fun j' hj' y₁ y₂ hy₁ => hdomK a ha n j hnk j' hj' y₁ y₂ hy₁)
    have hev : c03_sp_Ifar p χ a =ᶠ[𝓝 y] fun y => (-1 : ℂ) ^ n * ∫ ξ in Ioi (1 : ℝ), F a n y ξ := by
      filter_upwards [Ioi_mem_nhds hy0] with z hz using hIfar a ha z hz n hn1
    have hcd : ContDiffAt ℝ j (fun y => ∫ ξ in Ioi (1 : ℝ), F a n y ξ) y :=
      haux.1.contDiffAt (Ioi_mem_nhds hy0)
    rw [(hev.iteratedDeriv j).eq_of_nhds, iteratedDeriv_const_mul _ hcd, haux.2 j le_rfl y hy0,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hint : Integrable (fun ξ => C * y ^ (-(n : ℝ) / 2) * ξ ^ e) (volume.restrict (Ioi 1)) :=
      (integrableOn_Ioi_rpow_of_lt he one_pos).const_mul _
    refine (norm_integral_le_of_norm_le hint ?_).trans ?_
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun ξ hξ => ?_
      have h := hb a ha (fun i hi ξ hξ => hCk i (by omega) ξ hξ) y ξ hy (le_of_lt hξ)
      exact h.1.trans h.2
    · rw [integral_const_mul]
      have hyM : y ^ (-(n : ℝ) / 2) ≤ y ^ (-M) :=
        Real.rpow_le_rpow_of_exponent_le hy (by
          have := abs_nonneg m; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
      calc C * y ^ (-(n : ℝ) / 2) * Ie ≤ C * y ^ (-M) * Ie := by gcongr
        _ ≤ (C * Ie + 1) * y ^ (-M) := by
          have : 0 ≤ y ^ (-M) := by positivity
          nlinarith

/-! ### Helpers for the homogeneous-phase assembly -/

/-- A fixed cutoff `χ_sp`. -/
theorem c03f_aux_cutoff : ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ tsupport χ ⊆ Ioo (1 / 2) 2 ∧
    (∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) ∧ ∀ s, 0 ≤ χ s ∧ χ s ≤ 1 := by
  let f : ContDiffBump (9 / 8 : ℝ) := ⟨3 / 8, 1 / 2, by norm_num, by norm_num⟩
  refine ⟨f, f.contDiff, ?_, fun s hs => f.one_of_mem_closedBall ?_, fun s => ⟨f.nonneg, f.le_one⟩⟩
  · rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    change -(1/2 : ℝ) ≤ x - 9/8 ∧ x - 9/8 ≤ 1/2 at hx
    constructor <;> linarith [hx.1, hx.2]
  · rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -(3/8 : ℝ) ≤ s - 9/8 ∧ s - 9/8 ≤ 3/8
    constructor <;> linarith [hs.1, hs.2]

/-- A symbol, extended by zero to `(-∞,0]`, is continuous. -/
theorem c03f_aux_sym_cont {m : ℝ} {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) :
    Continuous ((Ioi (0 : ℝ)).indicator a) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · have h1 : ContinuousAt a x :=
      (ha.1.continuousOn).continuousAt (Ioi_mem_nhds hx)
    refine h1.congr ?_
    filter_upwards [Ioi_mem_nhds hx] with z hz
    rw [indicator_of_mem hz]
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [Iio_mem_nhds (show x < 1 by linarith)] with z hz
    by_cases hz0 : 0 < z
    · rw [indicator_of_mem hz0, ha.2.1 z ⟨hz0, (mem_Iio.1 hz).le⟩]
    · rw [indicator_of_notMem hz0]

/-- Interval integrability of a symbol against a continuous function on `[0,R]`. -/
theorem c03f_aux_sym_ii {m : ℝ} {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) {h : ℝ → ℂ}
    (hh : Continuous h) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun ξ => a ξ * h ξ) volume 0 R := by
  have hc : Continuous (fun ξ => (Ioi (0 : ℝ)).indicator a ξ * h ξ) :=
    (c03f_aux_sym_cont ha).mul hh
  refine (hc.intervalIntegrable 0 R).congr ?_
  rw [uIoc_of_le hR]
  intro ξ hξ
  simp only [indicator_of_mem (show ξ ∈ Ioi (0 : ℝ) from hξ.1)]

/-- Derivatives of `y ↦ c y^r` (`y > 0`). -/
theorem c03f_aux_iter_rpow (c r : ℝ) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (fun y : ℝ => c * y ^ r) y =
      c * ((descPochhammer ℝ k).eval r * y ^ (r - k)) := by
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_rpow_const]

/-- `t ↦ e^{-i(t-π/4)}` has `k`-th derivative `(-i)^k e^{-i(t-π/4)}`. -/
theorem c03f_aux_iter_expI (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => Complex.exp (-(Complex.I * ((t - π / 4 : ℝ) : ℂ)))) =
      fun t => (-Complex.I) ^ k * Complex.exp (-(Complex.I * ((t - π / 4 : ℝ) : ℂ))) := by
  set g : ℝ → ℂ := fun t => Complex.exp (-(Complex.I * ((t - π / 4 : ℝ) : ℂ))) with hg
  have hgd : ∀ t, HasDerivAt g (-Complex.I * g t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(Complex.I * ((t - π / 4 : ℝ) : ℂ))) (-Complex.I) t := by
      have := (((hasDerivAt_id t).sub_const (π / 4)).ofReal_comp.const_mul Complex.I).neg
      convert this using 1
      · funext y; simp
      · simp
    have := h1.cexp
    simpa [hg, mul_comm] using this
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ((t - π / 4 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)
    rw [hg]; fun_prop
  induction k with
  | zero => simp [hg]
  | succ k ih =>
    rw [iteratedDeriv_succ', show deriv g = fun t => -Complex.I * g t from
      funext fun t => (hgd t).deriv]
    funext t
    rw [iteratedDeriv_const_mul _ ((hgc.of_le (by exact_mod_cast le_top)).contDiffAt), ih]
    ring

theorem c03f_aux_Pinv (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ y, 0 < y → c03_sp_P p y ≠ 0) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (c03_sp_P p y)⁻¹) (Ioi 0) ∧
    ∀ n : ℕ, ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y →
      ‖iteratedDeriv n (fun y => (c03_sp_P p y)⁻¹) y‖ ≤ C * y ^ ((n : ℝ) / p) := by
  set e : ℝ := (p - 1) / (2 * p) with he
  set K : ℝ := Real.sqrt (p / (2 * π)) with hK
  set f1 : ℝ → ℂ := fun y => ((y ^ e : ℝ) : ℂ) with hf1
  set g : ℝ → ℂ := fun t => Complex.exp (-(Complex.I * ((t - π / 4 : ℝ) : ℂ))) with hg
  set f2 : ℝ → ℂ := fun y => g (Psi0 p y) with hf2
  have hPsi : Psi0 p = fun y => p / (p + 1) * y ^ (1 + 1 / p) := rfl
  have hsq : ∀ y, 0 < y → 0 < Real.sqrt (2 * π / (p * lambda0 p y ^ (p - 1))) := by
    intro y hy
    apply Real.sqrt_pos.2
    have : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
    positivity
  have hP0 : ∀ y, 0 < y → c03_sp_P p y ≠ 0 := by
    intro y hy
    unfold c03_sp_P
    exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.2 (hsq y hy).ne')
  have hform : ∀ y, 0 < y → (c03_sp_P p y)⁻¹ = (K : ℂ) * (f1 y * f2 y) := by
    intro y hy
    have hl : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
    have hs : (Real.sqrt (2 * π / (p * lambda0 p y ^ (p - 1))))⁻¹ = K * y ^ e := by
      rw [← Real.sqrt_inv, inv_div, hK, he, mul_div_right_comm,
        Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (lambda0 p y ^ (p - 1)),
        ← Real.rpow_mul hl.le, lambda0, ← Real.rpow_mul hy.le]
      congr 2; field_simp
    unfold c03_sp_P
    rw [mul_inv, ← Complex.exp_neg, ← Complex.ofReal_inv, hs]
    simp only [hf1, hf2, hg, Complex.ofReal_mul]
    ring
  have hgc : ContDiff ℝ (⊤ : ℕ∞) g := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ((t - π / 4 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)
    rw [hg]; fun_prop
  have hrp : ∀ r : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ r) (Ioi 0) := fun r =>
    contDiffOn_id.rpow_const_of_ne (fun x hx => (ne_of_gt hx))
  have hf1s : ContDiffOn ℝ (⊤ : ℕ∞) f1 (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hrp e)
  have hPsis : ContDiffOn ℝ (⊤ : ℕ∞) (Psi0 p) (Ioi 0) := by
    rw [hPsi]; exact contDiffOn_const.mul (hrp _)
  have hf2s : ContDiffOn ℝ (⊤ : ℕ∞) f2 (Ioi 0) := hgc.comp_contDiffOn hPsis
  have hprod : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => (K : ℂ) * (f1 y * f2 y)) (Ioi 0) :=
    contDiffOn_const.mul (hf1s.mul hf2s)
  refine ⟨hP0, hprod.congr (fun y hy => hform y hy), fun n => ?_⟩
  -- bounds for `f1`
  have b1 : ∀ i : ℕ, ∀ y, 1 ≤ y → ‖iteratedDeriv i f1 y‖ ≤ |(descPochhammer ℝ i).eval e| := by
    intro i y hy
    have hy0 : 0 < y := by linarith
    have hca : ContDiffAt ℝ i (fun y : ℝ => y ^ e) y :=
      ((hrp e).contDiffAt (Ioi_mem_nhds hy0)).of_le (by exact_mod_cast le_top)
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      show f1 = Complex.ofRealLI ∘ (fun y : ℝ => y ^ e) from rfl,
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left hca le_rfl,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_rpow_const,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
    have he0 : e < 0 := by rw [he]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    have : y ^ (e - i) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith)
    calc _ ≤ |(descPochhammer ℝ i).eval e| * 1 := by gcongr
      _ = _ := mul_one _
  -- bounds for `f2`
  set A : ℝ := 1 + ∑ i ∈ Finset.range (n + 1), |p / (p + 1) * (descPochhammer ℝ i).eval (1 + 1 / p)|
    with hA
  have hA1 : 1 ≤ A := by
    rw [hA]; linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (n + 1)) =>
      abs_nonneg (p / (p + 1) * (descPochhammer ℝ i).eval (1 + 1 / p)))]
  have b2 : ∀ k ≤ n, ∀ y, 1 ≤ y → ‖iteratedDeriv k f2 y‖ ≤ k.factorial * (A ^ k * y ^ ((k : ℝ) / p)) := by
    intro k hk y hy
    have hy0 : 0 < y := by linarith
    have hyD : 1 ≤ A * y ^ (1 / p) := by
      have : 1 ≤ y ^ (1 / p) := Real.one_le_rpow hy (by positivity)
      nlinarith
    have key := norm_iteratedFDerivWithin_comp_le (g := g) (f := Psi0 p) (n := k) (s := Ioi 0)
      (t := univ) (x := y) (N := (⊤ : ℕ∞)) hgc.contDiffOn hPsis (by exact_mod_cast le_top)
      uniqueDiffOn_univ isOpen_Ioi.uniqueDiffOn (mapsTo_univ _ _) hy0 (C := 1)
      (D := A * y ^ (1 / p)) ?_ ?_
    · rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_of_isOpen isOpen_Ioi hy0] at key
      refine (key.trans_eq ?_)
      rw [mul_one, mul_pow, ← Real.rpow_natCast (y ^ (1 / p)), ← Real.rpow_mul hy0.le]
      congr 3; ring
    · intro i hi
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, hg,
        c03f_aux_iter_expI]
      simp [Complex.norm_exp]
    · intro i hi1 hik
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_of_isOpen isOpen_Ioi hy0, hPsi, c03f_aux_iter_rpow,
        ← mul_assoc, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hy0 _)]
      have h1 : y ^ (1 + 1 / p - i) ≤ y ^ (1 / p) := by
        apply Real.rpow_le_rpow_of_exponent_le hy
        have : (1 : ℝ) ≤ i := by exact_mod_cast hi1
        linarith
      have h2 : |p / (p + 1) * (descPochhammer ℝ i).eval (1 + 1 / p)| ≤ A := by
        rw [hA]
        have := Finset.single_le_sum (f := fun i => |p / (p + 1) * (descPochhammer ℝ i).eval
          (1 + 1 / p)|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans hik hk)))
        linarith
      calc _ ≤ A * y ^ (1 / p) := by
            apply mul_le_mul h2 h1 (by positivity) (by linarith)
        _ ≤ (A * y ^ (1 / p)) ^ i := le_self_pow₀ hyD (by omega)
  refine ⟨K * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |(descPochhammer ℝ i).eval e| *
      ((n - i).factorial * A ^ (n - i)), by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hev : (fun y => (c03_sp_P p y)⁻¹) =ᶠ[𝓝 y] (fun y => (K : ℂ) * (f1 y * f2 y)) := by
    filter_upwards [Ioi_mem_nhds hy0] with z hz using hform z hz
  have hca : ContDiffAt ℝ n (fun y => f1 y * f2 y) y :=
    ((hf1s.mul hf2s).contDiffAt (Ioi_mem_nhds hy0)).of_le (by exact_mod_cast le_top)
  rw [(hev.iteratedDeriv n).eq_of_nhds, iteratedDeriv_const_mul _ hca, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  refine (c03s_aux_leibniz hf1s hf2s hy0 n).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 := b1 i y hy
  have h2 := b2 (n - i) (Nat.sub_le n i) y hy
  have h3 : y ^ (((n - i : ℕ) : ℝ) / p) ≤ y ^ ((n : ℝ) / p) := by
    apply Real.rpow_le_rpow_of_exponent_le hy
    apply div_le_div_of_nonneg_right _ hp.le; exact_mod_cast Nat.sub_le n i
  calc (n.choose i : ℝ) * ‖iteratedDeriv i f1 y‖ * ‖iteratedDeriv (n - i) f2 y‖
      ≤ (n.choose i : ℝ) * |(descPochhammer ℝ i).eval e| *
          ((n - i).factorial * (A ^ (n - i) * y ^ (((n - i : ℕ) : ℝ) / p))) := by gcongr
    _ ≤ (n.choose i : ℝ) * |(descPochhammer ℝ i).eval e| *
          ((n - i).factorial * (A ^ (n - i) * y ^ ((n : ℝ) / p))) := by gcongr
    _ = _ := by ring


/-- Blueprint: lem:appendix_homogeneous_stationary_phase (prefixed copy of
`GSQG.appendix_homogeneous_stationary_phase`). -/
theorem c03f_appendix_homogeneous_stationary_phase (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (hm : m < p) :
    (∀ a ∈ c03_sp_symbol m,
      (∀ y, 0 < y → Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
        a ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) atTop (𝓝 (c03_hsp_I p a y))) ∧
      (∀ y, 0 < y → c03_hsp_I p a y = c03_sp_P p y * (a (lambda0 p y) + c03_hsp_r p a y)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c03_hsp_r p a) (Ioi 0)) ∧
    ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ k ≤ k₀, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ y, 1 ≤ y → ‖iteratedDeriv j (c03_hsp_r p a) y‖ ≤
        C * lambda0 p y ^ (m - (p + 1)) * y ^ (-(j : ℝ)) := by
  obtain ⟨χ, hχ, hχs, hχ1, hχ01⟩ := c03f_aux_cutoff
  have far := c03f_c03_sp_far p m hp hp1 hm χ hχ hχs hχ1 hχ01
  have near := c03s_c03_sp_near p m hp hp1 χ hχ hχs hχ1 hχ01
  obtain ⟨hP0, hPs, hPb⟩ := c03f_aux_Pinv p hp hp1
  have hlam : ∀ y, 0 < y → 0 < lambda0 p y := fun y hy => Real.rpow_pos_of_pos hy _
  -- decomposition of the truncated integrals
  have hdec : ∀ a ∈ c03_sp_symbol m, ∀ y, 0 < y → Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
      a ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) atTop
      (𝓝 (c03_sp_Inear p χ a y + c03_sp_Ifar p χ a y)) := by
    intro a ha y hy
    have hF := ((far.1 a ha).1 y hy).const_add (c03_sp_Inear p χ a y)
    refine hF.congr' ?_
    filter_upwards [eventually_ge_atTop (2 * lambda0 p y), eventually_ge_atTop 0] with R hR hR0
    have hc1 : Continuous (fun ξ : ℝ => (χ (ξ / lambda0 p y) : ℂ) *
        Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) := by
      unfold c03_sp_phi
      have := hχ.continuous
      fun_prop
    have hc2 : Continuous (fun ξ : ℝ => ((1 - χ (ξ / lambda0 p y) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) := by
      unfold c03_sp_phi
      have := hχ.continuous
      fun_prop
    have i1 := c03f_aux_sym_ii ha hc1 hR0
    have i2 := c03f_aux_sym_ii ha hc2 hR0
    have hsplit : (∫ ξ in (0 : ℝ)..R, a ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) =
        (∫ ξ in (0 : ℝ)..R, a ξ * ((χ (ξ / lambda0 p y) : ℂ) *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)))) +
        ∫ ξ in (0 : ℝ)..R, a ξ * (((1 - χ (ξ / lambda0 p y) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) := by
      rw [← intervalIntegral.integral_add i1 i2]
      congr 1; funext ξ; push_cast; ring
    rw [hsplit]
    congr 1
    · unfold c03_sp_Inear
      rw [intervalIntegral.integral_of_le hR0]
      have hz : ∀ ξ ∈ Ioi (0 : ℝ) \ Ioc 0 R, a ξ * (χ (ξ / lambda0 p y) : ℂ) *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)) = 0 := by
        intro ξ hξ
        have hξR : R < ξ := by
          by_contra h; exact hξ.2 ⟨hξ.1, not_lt.1 h⟩
        have : χ (ξ / lambda0 p y) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hm'
          have h2 := (hχs hm').2
          rw [div_lt_iff₀ (hlam y hy)] at h2
          linarith
        simp [this]
      have hsub : Ioc (0:ℝ) R ⊆ Ioi 0 := fun x hx => hx.1
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) measurableSet_Ioi
        hsub hz]
      congr 1; funext ξ; ring
    · congr 1; funext ξ; ring
  have hI : ∀ a ∈ c03_sp_symbol m, ∀ y, 0 < y →
      c03_hsp_I p a y = c03_sp_Inear p χ a y + c03_sp_Ifar p χ a y :=
    fun a ha y hy => (hdec a ha y hy).limUnder_eq
  set nearT : (ℝ → ℂ) → ℝ → ℂ := fun a y => ((lambda0 p y ^ m : ℝ) : ℂ) *
    c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s) with hnearT
  have hr : ∀ a ∈ c03_sp_symbol m, ∀ y, 0 < y →
      c03_hsp_r p a y = nearT a y + c03_sp_Ifar p χ a y * (c03_sp_P p y)⁻¹ := by
    intro a ha y hy
    unfold c03_hsp_r
    have := near.2.1 a ha y hy
    simp only [hnearT, ← this]
    rw [hI a ha y hy, add_div, div_eq_mul_inv (c03_sp_Ifar p χ a y)]
    ring
  have hrs : ∀ a ∈ c03_sp_symbol m, ContDiffOn ℝ (⊤ : ℕ∞) (c03_hsp_r p a) (Ioi 0) := fun a ha =>
    ((near.2.2.1 a ha).add ((far.1 a ha).2.mul hPs)).congr (fun y hy => hr a ha y hy)
  refine ⟨fun a ha => ⟨fun y hy => (hI a ha y hy) ▸ hdec a ha y hy, fun y hy => ?_, hrs a ha⟩, ?_⟩
  · unfold c03_hsp_r
    rw [add_sub_cancel, mul_div_cancel₀ _ (hP0 y hy)]
  · intro j
    choose K hK using fun (i : ℕ) (M : ℝ) (hM : 0 ≤ M) => far.2 i M hM
    set N : ℝ := (j : ℝ) / p with hN
    set T : ℝ := (m - (p + 1)) / p - j with hT
    set M : ℝ := max 0 (N - T) with hMdef
    have hM0 : 0 ≤ M := le_max_left _ _
    refine ⟨max (j + 4) ((Finset.range (j + 1)).sup fun i => K i M hM0), fun Ck => ?_⟩
    obtain ⟨Cn, hCn, hnb⟩ := near.2.2.2 j Ck
    choose Cf hCf hfb using fun i => hK i M hM0 Ck
    choose CP hCP hPbd using hPb
    refine ⟨Cn + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cf i * CP (j - i),
      add_pos_of_pos_of_nonneg hCn (Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (by positivity) (hCf i).le) (hCP _)), ?_⟩
    intro a ha hCk y hy
    have hy0 : 0 < y := by linarith
    have hev : c03_hsp_r p a =ᶠ[𝓝 y]
        (fun y => nearT a y + c03_sp_Ifar p χ a y * (c03_sp_P p y)⁻¹) := by
      filter_upwards [Ioi_mem_nhds hy0] with z hz using hr a ha z hz
    have hcd1 : ContDiffAt ℝ j (nearT a) y :=
      ((near.2.2.1 a ha).contDiffAt (Ioi_mem_nhds hy0)).of_le (by exact_mod_cast le_top)
    have hcd2 : ContDiffAt ℝ j (fun y => c03_sp_Ifar p χ a y * (c03_sp_P p y)⁻¹) y :=
      ((((far.1 a ha).2.mul hPs)).contDiffAt (Ioi_mem_nhds hy0)).of_le (by exact_mod_cast le_top)
    rw [(hev.iteratedDeriv j).eq_of_nhds, iteratedDeriv_fun_add hcd1 hcd2]
    have hTeq : lambda0 p y ^ (m - (p + 1)) * y ^ (-(j : ℝ)) = y ^ T := by
      unfold lambda0
      rw [← Real.rpow_mul hy0.le, ← Real.rpow_add hy0, hT]
      congr 1; ring
    have b1 : ‖iteratedDeriv j (nearT a) y‖ ≤ Cn * (lambda0 p y ^ (m - (p + 1)) * y ^ (-(j : ℝ))) := by
      have := hnb a ha (fun k hk ξ hξ => hCk k (le_trans hk (le_max_left _ _)) ξ hξ) y hy
      rw [show m - p - 1 = m - (p + 1) by ring] at this
      simpa [hnearT, mul_assoc] using this
    have b2 : ‖iteratedDeriv j (fun y => c03_sp_Ifar p χ a y * (c03_sp_P p y)⁻¹) y‖ ≤
        (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Cf i * CP (j - i)) * y ^ T := by
      refine (c03s_aux_leibniz (far.1 a ha).2 hPs hy0 j).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 := hfb i a ha (fun k hk ξ hξ => hCk k (le_trans hk (le_trans
        (Finset.le_sup (f := fun i => K i M hM0) hi) (le_max_right _ _))) ξ hξ) y hy
      have h2 := hPbd (j - i) y hy
      have hexp : y ^ (-M) * y ^ (((j - i : ℕ) : ℝ) / p) ≤ y ^ T := by
        rw [← Real.rpow_add hy0]
        apply Real.rpow_le_rpow_of_exponent_le hy
        have : ((j - i : ℕ) : ℝ) / p ≤ N := by
          rw [hN]; apply div_le_div_of_nonneg_right _ hp.le; exact_mod_cast Nat.sub_le j i
        have : N - T ≤ M := le_max_right _ _
        linarith
      calc (j.choose i : ℝ) * ‖iteratedDeriv i (c03_sp_Ifar p χ a) y‖ *
            ‖iteratedDeriv (j - i) (fun y => (c03_sp_P p y)⁻¹) y‖
          ≤ (j.choose i : ℝ) * (Cf i * y ^ (-M)) * (CP (j - i) * y ^ (((j - i : ℕ) : ℝ) / p)) := by
            have : 0 ≤ Cf i * y ^ (-M) := mul_nonneg (hCf i).le (by positivity)
            gcongr
        _ = (j.choose i : ℝ) * Cf i * CP (j - i) * (y ^ (-M) * y ^ (((j - i : ℕ) : ℝ) / p)) := by
            ring
        _ ≤ (j.choose i : ℝ) * Cf i * CP (j - i) * y ^ T := by
            gcongr
            exact mul_nonneg (mul_nonneg (by positivity) (hCf i).le) (hCP _)
    rw [hTeq] at b1
    rw [mul_assoc, hTeq]
    calc _ ≤ ‖iteratedDeriv j (nearT a) y‖ +
          ‖iteratedDeriv j (fun y => c03_sp_Ifar p χ a y * (c03_sp_P p y)⁻¹) y‖ := norm_add_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add b1 b2


end GSQG
