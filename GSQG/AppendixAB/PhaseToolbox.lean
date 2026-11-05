import GSQG.Definitions

/-!
# Appendices A–B: stationary phase, oscillatory multipliers, Fourier lemmas (toolbox)

Proofs of the stationary-phase / oscillatory-multiplier / Fourier lemmas of blueprint chapter 03,
stated here with the prefix `c03sp_` (theorem `c03sp_X` has exactly the statement of the public
`GSQG.X`).  The chapter-03 definitions these statements need (`c03_Ck_norm`, `c03_sp_*`,
`c03_hsp_*`, `c03_mult_*`, …) live in this file; `AppendixAB/Statements.lean` proves each public
`X` by `c03sp_X`.  Helpers are named `c03sp_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- Blueprint: def:c03_holder (integer-order part).  `∑_{i ≤ k} sup_I |g^{(i)}|` (in `[0,∞]`),
with the derivatives taken within `I` (`iteratedDerivWithin`). For `I = univ` this is the global
`C^k(ℝ)` norm. -/
def c03_Ck_norm (k : ℕ) (I : Set ℝ) (g : ℝ → E) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (k + 1), ⨆ x ∈ I, ‖iteratedDerivWithin i g I x‖ₑ

/-- Blueprint: def:c03_holder.  Real-valued `C^k(I)` norm. -/
def c03_Ck_normR (k : ℕ) (I : Set ℝ) (g : ℝ → E) : ℝ := (c03_Ck_norm k I g).toReal

/-- Blueprint: lem:c03_frac_kernel_formula.  `c_p = (∫ (1-cos z)/|z|^{1+p} dz)⁻¹`. -/
def c03_cp (p : ℝ) : ℝ := (∫ z, (1 - Real.cos z) / |z| ^ (1 + p))⁻¹

-- Encoding: `GSQG/Definitions` defines `|D|^p` (`fracD`) by the singular integral with the constant
-- `c_α = calpha p`; the identity `c_p = c_α` (last-but-one conjunct) makes explicit that this
-- agrees with the Fourier multiplier `|ξ|^p` ("as in def:frac_multiplier").

/-- Blueprint: lem:c03_nonsmooth_symbol_bounds.  `a_{k,j}(ξ) = (iξ)^j χ(ξ) Φ₀(ξ)^k`. -/
def c03_symbol_akj (p : ℝ) (χ : ℝ → ℝ) (k j : ℕ) (ξ : ℝ) : ℂ :=
  (Complex.I * ξ) ^ j * (χ ξ : ℂ) * ((Phi0 p ξ : ℝ) : ℂ) ^ k



/-- Blueprint: prop:appendix_nonsmooth_fourier_inverse.  `m_k = χ Φ₀^k`. -/
def c03_symbol_mk (p : ℝ) (χ : ℝ → ℝ) (k : ℕ) (ξ : ℝ) : ℂ := (χ ξ : ℂ) * ((Phi0 p ξ : ℝ) : ℂ) ^ k


/-- Blueprint: lem:c03_morse_h (notation of the subsection).  `h(s) = s - s^{p+1}/(p+1)`. -/
def c03_h (p s : ℝ) : ℝ := s - s ^ (p + 1) / (p + 1)

/-- Blueprint: lem:c03_sp_compact (notation of the subsection).
`ρ(μ;c) = e^{iπ/4} (pμ/2π)^{1/2} e^{-iμh(1)} ∫₀^∞ c(s) e^{iμh(s)} ds - c(1)`. -/
def c03_sp_rho (p μ : ℝ) (c : ℝ → ℂ) : ℂ :=
  Complex.exp (Complex.I * (π / 4 : ℝ)) * (Real.sqrt (p * μ / (2 * π)) : ℂ) *
      Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))) *
      (∫ s in Ioi (0 : ℝ), c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) - c 1

/-! ### Helpers for `c03_fresnel_expansion` (van der Corput copied from `AppendixAB/Statements.lean`) -/

/-- Differentiation of `w ↦ ∫₀¹ t^k G(tw) dt`. -/
theorem c03sp_aux_param_deriv {G G' : ℝ → ℂ} (hG : ∀ x, HasDerivAt G (G' x) x)
    (hG'c : Continuous G') {B : ℝ} (hB : ∀ x, ‖G' x‖ ≤ B) (k : ℕ) (w : ℝ) :
    HasDerivAt (fun w => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * G (t * w))
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ (k + 1) * G' (t * w)) w := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (x₀ := w) (s := univ) (bound := fun _ => B)
    (F := fun x t => (t : ℂ) ^ k * G (t * x))
    (F' := fun x t => (t : ℂ) ^ (k + 1) * G' (t * x)) Filter.univ_mem
    (Eventually.of_forall fun x => (by
      exact ((Complex.continuous_ofReal.pow k).mul
        (hGc.comp (continuous_id.mul continuous_const))).aestronglyMeasurable))
    ((Continuous.intervalIntegrable (by
      exact (Complex.continuous_ofReal.pow k).mul
        (hGc.comp (continuous_id.mul continuous_const))) _ _))
    (((Complex.continuous_ofReal.pow (k + 1)).mul
        (hG'c.comp (continuous_id.mul continuous_const))).aestronglyMeasurable)
    (Eventually.of_forall fun t ht x _ => by
      rw [uIoc_of_le zero_le_one] at ht
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t ^ (k + 1) * ‖G' (t * x)‖ ≤ 1 * B := by
            apply mul_le_mul (pow_le_one₀ ht.1.le ht.2) (hB _) (norm_nonneg _) zero_le_one
        _ = B := one_mul B)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ x _ => by
      have := ((hG (t * x)).scomp x ((hasDerivAt_id' x).const_mul t)).const_mul ((t : ℂ) ^ k)
      convert this using 1
      · rfl
      · rw [Complex.real_smul]; push_cast; ring
      )
  exact h.2

/-- `f(w) = w ∫₀¹ f'(tw) dt` when `f(0) = 0`. -/
theorem c03sp_aux_div_formula {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf'c : Continuous f') (hf0 : f 0 = 0) (w : ℝ) :
    f w = (w : ℂ) * ∫ t in (0 : ℝ)..1, f' (t * w) := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw; simp [hf0]
  have h1 : ∫ x in (0 : ℝ)..w, f' x = f w - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x)
      (hf'c.intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_comp_mul_right (a := 0) (b := 1) f' hw
  simp only [zero_mul, one_mul] at h2
  rw [hf0, sub_zero] at h1
  rw [h2, h1, Complex.real_smul]
  have : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast; field_simp

/-- The Gaussian `g(w) = e^{-w²/2}` (complex-valued). -/
def c03sp_aux_g0 (w : ℝ) : ℂ := Complex.exp (-((w : ℂ) ^ 2) / 2)

theorem c03sp_aux_g0_norm (w : ℝ) : ‖c03sp_aux_g0 w‖ = Real.exp (-(w ^ 2) / 2) := by
  unfold c03sp_aux_g0
  rw [Complex.norm_exp]; congr 1; norm_cast

theorem c03sp_aux_g0_hasDerivAt {P : ℝ → ℂ} {p' : ℂ} {w : ℝ} (hP : HasDerivAt P p' w) :
    HasDerivAt (fun w => P w * c03sp_aux_g0 w)
      ((p' - (w : ℂ) * P w) * c03sp_aux_g0 w) w := by
  have h1 : HasDerivAt (fun w : ℝ => -((w : ℂ) ^ 2) / 2) (-(w : ℂ)) w := by
    have := ((hasDerivAt_id' w).ofReal_comp.pow 2).neg.div_const 2
    convert this using 1; push_cast; ring
  have := hP.mul h1.cexp
  convert this using 1
  · rfl
  · unfold c03sp_aux_g0; ring

/-- `|w|^j e^{-w²/2} ≤ 8` for `j ≤ 3`. -/
theorem c03sp_aux_poly_gauss (w : ℝ) {j : ℕ} (hj : j ≤ 3) :
    |w| ^ j * Real.exp (-(w ^ 2) / 2) ≤ 8 := by
  have hx : 0 ≤ w ^ 2 / 2 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have he : Real.exp (-(w ^ 2) / 2) = (Real.exp (w ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [he, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have hw2 : |w| ^ 2 = w ^ 2 := sq_abs w
  have ha : 0 ≤ |w| := abs_nonneg w
  have key : |w| ^ j ≤ 1 + |w| ^ 4 := by
    rcases le_total |w| 1 with h | h
    · have : |w| ^ j ≤ 1 := pow_le_one₀ ha h
      linarith [pow_nonneg ha 4]
    · have : |w| ^ j ≤ |w| ^ 4 := pow_le_pow_right₀ h (by omega)
      linarith
  have h4 : |w| ^ 4 = (w ^ 2) ^ 2 := by rw [← hw2]; ring
  nlinarith [sq_nonneg (w ^ 2)]

/-! ### Van der Corput -/

/-- The derivative of a function monotone on `[c,d]` is nonnegative at interior points. -/
theorem c03sp_v_aux_deriv_nonneg_of_monotoneOn {c d x : ℝ} {g : ℝ → ℝ} {g' : ℝ}
    (hg : MonotoneOn g (Icc c d)) (hx : x ∈ Ioo c d) (hd : HasDerivAt g g' x) : 0 ≤ g' := by
  have h1 : Tendsto (slope g x) (𝓝[>] x) (𝓝 g') :=
    hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
  have h2 : ∀ᶠ y in 𝓝[>] x, 0 ≤ slope g x y := by
    filter_upwards [Ioo_mem_nhdsGT hx.2] with y hy
    rw [slope_def_field]
    apply div_nonneg _ (by linarith [hy.1])
    exact sub_nonneg.2 (hg ⟨hx.1.le, hx.2.le⟩ ⟨by linarith [hx.1, hy.1], hy.2.le⟩ hy.1.le)
  exact ge_of_tendsto h1 h2

/-- `|y| + |x| + |x-y| ≤ 2 max(|x|,|y|)` when `x, y` have the same sign. -/
theorem c03sp_v_aux_abs_arith (x y : ℝ) (h : 0 ≤ x * y) :
    |y| + |x| + |x - y| ≤ 2 * max |x| |y| := by
  have hm : |x| * |y| = x * y := by rw [← abs_mul, abs_of_nonneg h]
  have key : |x - y| = |(|x| - |y|)| := by
    rw [← sq_eq_sq₀ (abs_nonneg _) (abs_nonneg _), sq_abs, sq_abs]
    nlinarith [sq_abs x, sq_abs y]
  rw [key]
  rcases le_total |x| |y| with hxy | hxy
  · rw [abs_of_nonpos (a := |x| - |y|) (by linarith), max_eq_right hxy]; linarith
  · rw [abs_of_nonneg (a := |x| - |y|) (by linarith), max_eq_left hxy]; linarith

/-- Van der Corput, first derivative test, in terms of an explicit derivative `g = Φ'` with
derivative `g'` on the open interval (the core estimate behind `c03sp_v_vdc_first`). -/
theorem c03sp_v_aux_vdc1 {c d lam : ℝ} (hcd : c < d) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Icc c d)) (hgc : ContinuousOn g (Icc c d))
    (hg'c : ContinuousOn g' (Icc c d))
    (hΦd : ∀ x ∈ Ioo c d, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioo c d, HasDerivAt g (g' x) x)
    (hmono : MonotoneOn g (Icc c d) ∨ AntitoneOn g (Icc c d))
    (hlow : ∀ x ∈ Icc c d, lam ≤ |g x|) :
    ‖∫ x in c..d, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 2 * max (|g c|⁻¹) (|g d|⁻¹) := by
  have hne : ∀ x ∈ Icc c d, g x ≠ 0 := fun x hx h => by
    have := hlow x hx; rw [h, abs_zero] at this; linarith
  have huIcc : uIcc c d = Icc c d := uIcc_of_le hcd.le
  have hmin : min c d = c := min_eq_left hcd.le
  have hmax : max c d = d := max_eq_right hcd.le
  set u : ℝ → ℂ := fun x => -Complex.I * (((g x)⁻¹ : ℝ) : ℂ) with hu
  set v : ℝ → ℂ := fun x => Complex.exp (Complex.I * (Φ x : ℂ)) with hv
  set u' : ℝ → ℂ := fun x => -Complex.I * ((-(g' x) / g x ^ 2 : ℝ) : ℂ) with hu'
  set v' : ℝ → ℂ := fun x => Complex.exp (Complex.I * (Φ x : ℂ)) * (Complex.I * (g x : ℂ))
    with hv'
  have hgc' : ContinuousOn (fun x => (g x)⁻¹) (Icc c d) := hgc.inv₀ hne
  have huc : ContinuousOn u (Icc c d) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hgc')
  have hvc : ContinuousOn v (Icc c d) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦc))
  have hu'c : ContinuousOn u' (Icc c d) := by
    refine continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_)
    exact hg'c.neg.div (hgc.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
  have hv'c : ContinuousOn v' (Icc c d) :=
    hvc.mul (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hgc))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := c) (b := d)
    (u := u) (v := v) (u' := u') (v' := v') (by rwa [huIcc]) (by rwa [huIcc])
    (fun x hx => by
      rw [hmin, hmax] at hx
      have := ((hgd x hx).inv (hne x (Ioo_subset_Icc_self hx))).ofReal_comp.const_mul (-Complex.I)
      simpa [hu, hu'] using this)
    (fun x hx => by
      rw [hmin, hmax] at hx
      have := (((hΦd x hx).ofReal_comp).const_mul Complex.I).cexp
      simpa [hv, hv'] using this)
    (hu'c.intervalIntegrable_of_Icc hcd.le) (hv'c.intervalIntegrable_of_Icc hcd.le)
  have hlhs : ∫ x in c..d, u x * v' x = ∫ x in c..d, Complex.exp (Complex.I * (Φ x : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [huIcc] at hx
    have h1 : (g x : ℂ) ≠ 0 := by exact_mod_cast hne x hx
    simp only [hu, hv']
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
  rw [← hlhs, hibp]
  set k : ℝ → ℝ := fun x => g' x / g x ^ 2 with hk
  have hkc : ContinuousOn k (Icc c d) :=
    hg'c.div (hgc.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
  have hnorm_u'v : ∀ x ∈ Icc c d, ‖u' x * v x‖ = |k x| := by
    intro x hx
    simp only [hu', hv, hk, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_comm Complex.I, norm_neg,
      Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, mul_one, neg_div]
  have hint_le : ‖∫ x in c..d, u' x * v x‖ ≤ ∫ x in c..d, |k x| := by
    refine (intervalIntegral.norm_integral_le_integral_norm hcd.le).trans (le_of_eq ?_)
    apply intervalIntegral.integral_congr
    intro x hx; rw [huIcc] at hx; exact hnorm_u'v x hx
  have hftc : ∫ x in c..d, -k x = (g d)⁻¹ - (g c)⁻¹ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd.le hgc'
    · intro x hx
      have := (hgd x hx).inv (hne x (Ioo_subset_Icc_self hx))
      convert this using 1
      simp [hk, neg_div]
    · exact (hkc.neg).intervalIntegrable_of_Icc hcd.le
  have hsign : ∫ x in c..d, |k x| ≤ |(g c)⁻¹ - (g d)⁻¹| := by
    have hIoo : ∀ (f : ℝ → ℝ), ∫ x in c..d, f x = ∫ x in Ioo c d, f x := fun f => by
      rw [intervalIntegral.integral_of_le hcd.le, integral_Ioc_eq_integral_Ioo]
    rcases hmono with hm | hm
    · have hk0 : ∀ x ∈ Ioo c d, 0 ≤ k x := fun x hx =>
        div_nonneg (c03sp_v_aux_deriv_nonneg_of_monotoneOn hm hx (hgd x hx)) (sq_nonneg _)
      have : ∫ x in c..d, |k x| = ∫ x in c..d, -(-k x) := by
        rw [hIoo, hIoo]
        refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
        simp [abs_of_nonneg (hk0 x hx)]
      rw [this, intervalIntegral.integral_neg, hftc]
      rw [neg_sub]; exact le_abs_self _
    · have hk0 : ∀ x ∈ Ioo c d, k x ≤ 0 := fun x hx => by
        have := c03sp_v_aux_deriv_nonneg_of_monotoneOn (g := fun x => -g x) hm.neg hx (hgd x hx).neg
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
      have : ∫ x in c..d, |k x| = ∫ x in c..d, -k x := by
        rw [hIoo, hIoo]
        refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
        simp [abs_of_nonpos (hk0 x hx)]
      rw [this, hftc, abs_sub_comm]; exact le_abs_self _
  have hend : ∀ x ∈ Icc c d, ‖u x * v x‖ = |(g x)⁻¹| := by
    intro x hx
    simp only [hu, hv, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul]
    rw [Complex.norm_exp]; simp
  have hsame : 0 ≤ (g c)⁻¹ * (g d)⁻¹ := by
    rw [← mul_inv]
    apply inv_nonneg.2
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn g (uIcc c d) := by rwa [huIcc]
    have h0 : (0 : ℝ) ∈ uIcc (g c) (g d) := by
      rcases lt_or_gt_of_ne (hne c ⟨le_rfl, hcd.le⟩) with h | h
      · have : 0 < g d := by nlinarith
        exact ⟨min_le_of_left_le h.le, le_max_of_le_right this.le⟩
      · have : g d < 0 := by nlinarith
        exact ⟨min_le_of_right_le this.le, le_max_of_le_left h.le⟩
    obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hcont h0
    rw [huIcc] at hx
    exact hne x hx hx0
  calc ‖u d * v d - u c * v c - ∫ x in c..d, u' x * v x‖
      ≤ ‖u d * v d‖ + ‖u c * v c‖ + ‖∫ x in c..d, u' x * v x‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ |(g d)⁻¹| + |(g c)⁻¹| + |(g c)⁻¹ - (g d)⁻¹| := by
        rw [hend d ⟨hcd.le, le_rfl⟩, hend c ⟨le_rfl, hcd.le⟩]
        gcongr
        exact hint_le.trans hsign
    _ ≤ 2 * max (|g c|⁻¹) (|g d|⁻¹) := by
        rw [← abs_inv, ← abs_inv]
        exact c03sp_v_aux_abs_arith _ _ hsame

/-- `2 max(|x|⁻¹,|y|⁻¹) ≤ 2/λ` when `|x|,|y| ≥ λ`. -/
theorem c03sp_v_aux_max_inv_le {lam x y : ℝ} (hlam : 0 < lam) (hx : lam ≤ |x|) (hy : lam ≤ |y|) :
    2 * max (|x|⁻¹) (|y|⁻¹) ≤ 2 / lam := by
  rw [div_eq_mul_inv]
  gcongr
  exact max_le (inv_anti₀ hlam hx) (inv_anti₀ hlam hy)

/-- First derivative test on `[c,d]`, `c ≤ d`, in the form `≤ 2/λ`. -/
theorem c03sp_v_aux_vdc1' {c d lam : ℝ} (hcd : c ≤ d) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Icc c d)) (hgc : ContinuousOn g (Icc c d))
    (hg'c : ContinuousOn g' (Icc c d))
    (hΦd : ∀ x ∈ Ioo c d, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioo c d, HasDerivAt g (g' x) x)
    (hmono : MonotoneOn g (Icc c d) ∨ AntitoneOn g (Icc c d))
    (hlow : ∀ x ∈ Icc c d, lam ≤ |g x|) :
    ‖∫ x in c..d, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 2 / lam := by
  rcases hcd.lt_or_eq with hcd | rfl
  · exact (c03sp_v_aux_vdc1 hcd hlam hΦc hgc hg'c hΦd hgd hmono hlow).trans
      (c03sp_v_aux_max_inv_le hlam (hlow c ⟨le_rfl, hcd.le⟩) (hlow d ⟨hcd.le, le_rfl⟩))
  · simp; positivity

/-- Regularity data of a `C²` function on a set. -/
theorem c03sp_v_aux_C2_setup {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ s) :
    ContinuousOn Φ s ∧ ContinuousOn (derivWithin Φ s) s ∧
    ContinuousOn (derivWithin (derivWithin Φ s) s) s ∧
    ∀ x, s ∈ 𝓝 x → HasDerivAt Φ (derivWithin Φ s x) x ∧
      HasDerivAt (derivWithin Φ s) (derivWithin (derivWithin Φ s) s x) x := by
  have h1 : ContDiffOn ℝ 1 (derivWithin Φ s) s := hΦ.derivWithin hs (by norm_num)
  refine ⟨hΦ.continuousOn, h1.continuousOn, h1.continuousOn_derivWithin hs le_rfl, fun x hx => ?_⟩
  have hd0 : DifferentiableAt ℝ Φ x :=
    ((hΦ.differentiableOn (by norm_num)) x (mem_of_mem_nhds hx)).differentiableAt hx
  have hd1 : DifferentiableAt ℝ (derivWithin Φ s) x :=
    ((h1.differentiableOn one_ne_zero) x (mem_of_mem_nhds hx)).differentiableAt hx
  refine ⟨?_, ?_⟩
  · rw [derivWithin_of_mem_nhds hx]; exact hd0.hasDerivAt
  · rw [derivWithin_of_mem_nhds hx]; exact hd1.hasDerivAt

/-- Splitting point of a continuous function at level `t`. -/
theorem c03sp_v_aux_split {a b t : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hgc : ContinuousOn g (Icc a b)) :
    ∃ c ∈ Icc a b, (a < c → g c ≤ t) ∧ (c < b → t ≤ g c) := by
  by_cases h1 : t ≤ g a
  · exact ⟨a, ⟨le_rfl, hab⟩, fun h => absurd h (lt_irrefl a), fun _ => h1⟩
  by_cases h2 : g b ≤ t
  · exact ⟨b, ⟨hab, le_rfl⟩, fun _ => h2, fun h => absurd h (lt_irrefl b)⟩
  push Not at h1 h2
  obtain ⟨c, hc, hct⟩ := intermediate_value_Icc hab hgc ⟨h1.le, h2.le⟩
  exact ⟨c, hc, fun _ => hct.le, fun _ => hct.ge⟩

/-- Second derivative test, increasing case. -/
theorem c03sp_v_aux_vdc2_inc {a b lam : ℝ} (hab : a < b) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hg'c : ContinuousOn g' (Icc a b))
    (hΦd : ∀ x ∈ Ioo a b, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hlow : ∀ x ∈ Icc a b, lam ≤ g' x) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 6 * lam ^ (-(1 / 2 : ℝ)) := by
  set s := Real.sqrt lam with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hlam
  have hss : s * s = lam := Real.mul_self_sqrt hlam.le
  have hrpow : lam ^ (-(1 / 2 : ℝ)) = 1 / s := by
    rw [Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hrpow]
  -- growth of g
  have hgrow : MonotoneOn (fun x => g x - x * lam) (Icc a b) := by
    have hd : ∀ x ∈ Ioo a b, HasDerivAt (fun x => g x - x * lam) (g' x - lam) x :=
      fun x hx => (hgd x hx).sub (hasDerivAt_mul_const lam)
    apply monotoneOn_of_deriv_nonneg (f := fun x => g x - x * lam) (convex_Icc a b)
      (hgc.sub (continuousOn_id.mul continuousOn_const))
    · rw [interior_Icc]; intro x hx
      exact (hd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro x hx
      rw [(hd x hx).deriv]
      have := hlow x (Ioo_subset_Icc_self hx); linarith
  have hgmono : MonotoneOn g (Icc a b) := by
    intro x hx y hy hxy
    have := hgrow hx hy hxy
    simp only at this
    nlinarith
  obtain ⟨c₁, hc₁, hc₁a, hc₁b⟩ := c03sp_v_aux_split (t := -s) hab.le hgc
  obtain ⟨c₂, hc₂, hc₂a, hc₂b⟩ := c03sp_v_aux_split (t := s) hc₁.2 (hgc.mono (Icc_subset_Icc hc₁.1 le_rfl))
  have hsub1 : Icc a c₁ ⊆ Icc a b := Icc_subset_Icc le_rfl hc₁.2
  have hsub2 : Icc c₁ c₂ ⊆ Icc a b := Icc_subset_Icc hc₁.1 hc₂.2
  have hsub3 : Icc c₂ b ⊆ Icc a b := Icc_subset_Icc (hc₁.1.trans hc₂.1) le_rfl
  have hcont : ContinuousOn (fun x => Complex.exp (Complex.I * (Φ x : ℂ))) (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦc))
  have hii : ∀ c d, Icc c d ⊆ Icc a b → c ≤ d →
      IntervalIntegrable (fun x => Complex.exp (Complex.I * (Φ x : ℂ))) volume c d :=
    fun c d h hcd => (hcont.mono h).intervalIntegrable_of_Icc hcd
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii a c₁ hsub1 hc₁.1)
    (hii c₁ b (Icc_subset_Icc hc₁.1 le_rfl) hc₁.2),
    ← intervalIntegral.integral_add_adjacent_intervals (hii c₁ c₂ hsub2 hc₂.1)
    (hii c₂ b hsub3 hc₂.2)]
  -- piece 1
  have hp1 : ‖∫ x in a..c₁, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 2 / s := by
    rcases hc₁.1.lt_or_eq with h | h
    · apply c03sp_v_aux_vdc1' hc₁.1 hs0 (hΦc.mono hsub1) (hgc.mono hsub1) (hg'c.mono hsub1)
        (fun x hx => hΦd x (Ioo_subset_Ioo le_rfl hc₁.2 hx))
        (fun x hx => hgd x (Ioo_subset_Ioo le_rfl hc₁.2 hx)) (Or.inl (hgmono.mono hsub1))
      intro x hx
      have := hgmono (hsub1 hx) (hsub1 ⟨hc₁.1, le_rfl⟩) hx.2
      have := hc₁a h
      rw [abs_of_neg (by linarith)]; linarith
    · rw [← h]; simp; positivity
  have hp3 : ‖∫ x in c₂..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 2 / s := by
    rcases hc₂.2.lt_or_eq with h | h
    · apply c03sp_v_aux_vdc1' hc₂.2 hs0 (hΦc.mono hsub3) (hgc.mono hsub3) (hg'c.mono hsub3)
        (fun x hx => hΦd x (Ioo_subset_Ioo (hc₁.1.trans hc₂.1) le_rfl hx))
        (fun x hx => hgd x (Ioo_subset_Ioo (hc₁.1.trans hc₂.1) le_rfl hx))
        (Or.inl (hgmono.mono hsub3))
      intro x hx
      have := hgmono (hsub3 ⟨le_rfl, hc₂.2⟩) (hsub3 hx) hx.1
      have := hc₂b h
      rw [abs_of_pos (by linarith)]; linarith
    · rw [h]; simp; positivity
  have hp2 : ‖∫ x in c₁..c₂, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 2 / s := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (fun x _ => ?_)).trans ?_
    · rw [Complex.norm_exp]; simp
    · rw [one_mul, abs_of_nonneg (sub_nonneg.2 hc₂.1)]
      rcases hc₂.1.lt_or_eq with h | h
      · have h1 := hc₁b (lt_of_lt_of_le h hc₂.2)
        have h2 := hc₂a h
        have h3 := hgrow (hsub2 ⟨le_rfl, hc₂.1⟩) (hsub2 ⟨hc₂.1, le_rfl⟩) hc₂.1
        simp only at h3
        rw [le_div_iff₀ hs0]
        nlinarith
      · rw [h, sub_self]; positivity
  calc _ ≤ ‖∫ x in a..c₁, Complex.exp (Complex.I * (Φ x : ℂ))‖ +
        (‖∫ x in c₁..c₂, Complex.exp (Complex.I * (Φ x : ℂ))‖ +
          ‖∫ x in c₂..b, Complex.exp (Complex.I * (Φ x : ℂ))‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 2 / s + (2 / s + 2 / s) := by gcongr
    _ = 6 * (1 / s) := by ring

/-- A continuous nonvanishing function on `[a,b]` has constant sign. -/
theorem c03sp_v_aux_sign {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hne : ∀ x ∈ Icc a b, f x ≠ 0) :
    (∀ x ∈ Icc a b, 0 < f x) ∨ (∀ x ∈ Icc a b, f x < 0) := by
  by_cases hab : a ≤ b
  swap
  · left; intro x hx; exact absurd (hx.1.trans hx.2) hab
  have key : ∀ x ∈ Icc a b, 0 < f a * f x := by
    intro x hx
    by_contra h
    push Not at h
    have hsub : uIcc a x ⊆ Icc a b := by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2
    have h0 : (0 : ℝ) ∈ uIcc (f a) (f x) := by
      rcases lt_or_gt_of_ne (hne a ⟨le_rfl, hab⟩) with h1 | h1
      · have : 0 ≤ f x := by nlinarith
        exact ⟨min_le_of_left_le h1.le, le_max_of_le_right this⟩
      · have : f x ≤ 0 := by nlinarith
        exact ⟨min_le_of_right_le this, le_max_of_le_left h1.le⟩
    obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc (hf.mono hsub) h0
    exact hne y (hsub hy) hy0
  rcases lt_or_gt_of_ne (hne a ⟨le_rfl, hab⟩) with h1 | h1
  · right; intro x hx; have := key x hx; nlinarith
  · left; intro x hx; have := key x hx; nlinarith

/-- `‖∫ e^{-iΦ}‖ = ‖∫ e^{iΦ}‖`. -/
theorem c03sp_v_aux_norm_integral_exp_neg (a b : ℝ) (Φ : ℝ → ℝ) :
    ‖∫ x in a..b, Complex.exp (Complex.I * ((-Φ x : ℝ) : ℂ))‖ =
      ‖∫ x in a..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ := by
  have h : ∀ x, Complex.exp (Complex.I * ((-Φ x : ℝ) : ℂ)) =
      (starRingEnd ℂ) (Complex.exp (Complex.I * (Φ x : ℂ))) := by
    intro x; rw [← Complex.exp_conj]; simp
  simp_rw [h]
  rw [intervalIntegral, intervalIntegral, integral_conj, integral_conj, ← map_sub,
    Complex.norm_conj]

/-- IBP against a primitive of `e` based at `c ∈ [a,b]`. -/
theorem c03sp_v_aux_amp_ibp {a b c : ℝ} (hab : a < b) (hc : c ∈ Icc a b) {e ψ : ℝ → ℂ}
    (he : ContinuousOn e (Icc a b)) (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) :
    ∫ x in a..b, ψ x * e x = ψ b * (∫ t in c..b, e t) - ψ a * (∫ t in c..a, e t) -
      ∫ x in a..b, derivWithin ψ (Icc a b) x * (∫ t in c..x, e t) := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hmin : min a b = a := min_eq_left hab.le
  have hmax : max a b = b := max_eq_right hab.le
  have hint : IntervalIntegrable e volume a b := he.intervalIntegrable_of_Icc hab.le
  have hcu : c ∈ uIcc a b := by rw [huIcc]; exact hc
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
  · rw [huIcc]; exact hψ.continuousOn
  · exact intervalIntegral.continuousOn_primitive_interval' hint hcu
  · intro x hx
    rw [hmin, hmax] at hx
    have hd := ((hψ.differentiableOn one_ne_zero) x (Ioo_subset_Icc_self hx)).differentiableAt
      (Icc_mem_nhds hx.1 hx.2)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
    exact hd.hasDerivAt
  · intro x hx
    rw [hmin, hmax] at hx
    have hsub : uIcc c x ⊆ Icc a b := uIcc_subset_Icc hc (Ioo_subset_Icc_self hx)
    apply intervalIntegral.integral_hasDerivAt_right ((he.mono hsub).intervalIntegrable)
    · exact (he.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
    · exact (he.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hx)
  · exact (hψ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl).intervalIntegrable_of_Icc
      hab.le
  · exact hint

/-- Amplitude bound from uniform bounds on primitives. -/
theorem c03sp_v_aux_amp {a b K : ℝ} (hab : a < b) {e ψ : ℝ → ℂ}
    (he : ContinuousOn e (Icc a b)) (hψ : ContDiffOn ℝ 1 ψ (Icc a b))
    (hK : ∀ x ∈ Icc a b, ‖∫ t in a..x, e t‖ ≤ K ∧ ‖∫ t in x..b, e t‖ ≤ K) :
    ‖∫ x in a..b, ψ x * e x‖ ≤ K * (‖ψ b‖ + ∫ x in a..b, ‖derivWithin ψ (Icc a b) x‖) ∧
    ‖∫ x in a..b, ψ x * e x‖ ≤ K * (‖ψ a‖ + ∫ x in a..b, ‖derivWithin ψ (Icc a b) x‖) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK a ⟨le_rfl, hab.le⟩).1
  have hψ'c : ContinuousOn (derivWithin ψ (Icc a b)) (Icc a b) :=
    hψ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  have hrest : ∀ c ∈ Icc a b, (∀ x ∈ Icc a b, ‖∫ t in c..x, e t‖ ≤ K) →
      ‖∫ x in a..b, derivWithin ψ (Icc a b) x * (∫ t in c..x, e t)‖ ≤
        K * ∫ x in a..b, ‖derivWithin ψ (Icc a b) x‖ := by
    intro c hc hcK
    refine (intervalIntegral.norm_integral_le_integral_norm hab.le).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le
    · refine ContinuousOn.intervalIntegrable_of_Icc hab.le ?_
      refine (hψ'c.mul ?_).norm
      have := intervalIntegral.continuousOn_primitive_interval'
        (he.intervalIntegrable_of_Icc (μ := volume) hab.le) (by rw [uIcc_of_le hab.le]; exact hc)
      rwa [uIcc_of_le hab.le] at this
    · exact (hψ'c.norm.intervalIntegrable_of_Icc (μ := volume) hab.le).const_mul K
    · intro x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hcK x hx) (norm_nonneg _)
  constructor
  · rw [c03sp_v_aux_amp_ibp hab ⟨le_rfl, hab.le⟩ he hψ, intervalIntegral.integral_same, mul_zero,
      sub_zero]
    refine (norm_sub_le _ _).trans ?_
    rw [mul_add, norm_mul]
    refine add_le_add ?_ ?_
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hK b ⟨hab.le, le_rfl⟩).1 (norm_nonneg _)
    · exact hrest a ⟨le_rfl, hab.le⟩ (fun x hx => (hK x hx).1)
  · rw [c03sp_v_aux_amp_ibp hab ⟨hab.le, le_rfl⟩ he hψ, intervalIntegral.integral_same, mul_zero,
      zero_sub]
    refine (norm_sub_le _ _).trans ?_
    rw [mul_add, norm_neg, norm_mul]
    refine add_le_add ?_ ?_
    · rw [mul_comm, intervalIntegral.integral_symm, norm_neg]
      exact mul_le_mul_of_nonneg_right (hK a ⟨le_rfl, hab.le⟩).2 (norm_nonneg _)
    · refine hrest b ⟨hab.le, le_rfl⟩ (fun x hx => ?_)
      rw [intervalIntegral.integral_symm, norm_neg]; exact (hK x hx).2

/-- Van der Corput, second derivative test, in terms of explicit derivatives. -/
theorem c03sp_v_aux_vdc2 {a b lam : ℝ} (hab : a < b) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hg'c : ContinuousOn g' (Icc a b))
    (hΦd : ∀ x ∈ Ioo a b, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hlow : ∀ x ∈ Icc a b, lam ≤ |g' x|) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 6 * lam ^ (-(1 / 2 : ℝ)) := by
  rcases c03sp_v_aux_sign hg'c (fun x hx h => by
      have := hlow x hx; rw [h, abs_zero] at this; linarith) with hpos | hneg
  · exact c03sp_v_aux_vdc2_inc hab hlam hΦc hgc hg'c hΦd hgd (fun x hx => by
      have := hlow x hx; rwa [abs_of_pos (hpos x hx)] at this)
  · rw [← c03sp_v_aux_norm_integral_exp_neg]
    exact c03sp_v_aux_vdc2_inc (Φ := fun x => -Φ x) (g := fun x => -g x) (g' := fun x => -g' x)
      hab hlam hΦc.neg hgc.neg hg'c.neg (fun x hx => (hΦd x hx).neg) (fun x hx => (hgd x hx).neg)
      (fun x hx => by have := hlow x hx; rwa [abs_of_neg (hneg x hx)] at this)

/-- Second derivative test on `[c,d]` with `c ≤ d`. -/
theorem c03sp_v_aux_vdc2' {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hg'c : ContinuousOn g' (Icc a b))
    (hΦd : ∀ x ∈ Ioo a b, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hlow : ∀ x ∈ Icc a b, lam ≤ |g' x|) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 6 * lam ^ (-(1 / 2 : ℝ)) := by
  rcases hab.lt_or_eq with hab | rfl
  · exact c03sp_v_aux_vdc2 hab hlam hΦc hgc hg'c hΦd hgd hlow
  · simp; positivity

/-- Amplitude bounds (three forms) from a uniform bound `K` on all subinterval integrals. -/
theorem c03sp_v_aux_amp_all {a b K : ℝ} (hab : a < b) {e ψ : ℝ → ℂ}
    (he : ContinuousOn e (Icc a b)) (hψ : ContDiffOn ℝ 1 ψ (Icc a b))
    (hK : ∀ c d, a ≤ c → c ≤ d → d ≤ b → ‖∫ t in c..d, e t‖ ≤ K) :
    ‖∫ x in a..b, ψ x * e x‖ ≤ K * (‖ψ b‖ + ∫ x in a..b, ‖derivWithin ψ (Icc a b) x‖) ∧
    ‖∫ x in a..b, ψ x * e x‖ ≤ K * (‖ψ a‖ + ∫ x in a..b, ‖derivWithin ψ (Icc a b) x‖) ∧
    ∀ B : ℝ, (∀ ξ ∈ Icc a b, ‖ψ ξ‖ ≤ B) →
      ‖∫ x in a..b, ψ x * e x‖ ≤ K * (B + ∫ x in a..b, ‖derivWithin ψ (Icc a b) x‖) := by
  have hK0 : 0 ≤ K := by
    have := hK a a le_rfl le_rfl hab.le; simpa using this
  obtain ⟨h1, h2⟩ := c03sp_v_aux_amp hab he hψ (fun x hx =>
    ⟨hK a x le_rfl hx.1 hx.2, hK x b hx.1 hx.2 le_rfl⟩)
  refine ⟨h1, h2, fun B hB => h1.trans ?_⟩
  gcongr
  exact hB b ⟨hab.le, le_rfl⟩

/-- `C²` data of `Φ` on `[a,b]` in the form used by the van der Corput helpers. -/
theorem c03sp_v_aux_C2_Icc {a b : ℝ} (hab : a < b) {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ (Icc a b)) :
    ContinuousOn Φ (Icc a b) ∧ ContinuousOn (derivWithin Φ (Icc a b)) (Icc a b) ∧
    ContinuousOn (derivWithin (derivWithin Φ (Icc a b)) (Icc a b)) (Icc a b) ∧
    (∀ x ∈ Ioo a b, HasDerivAt Φ (derivWithin Φ (Icc a b) x) x) ∧
    (∀ x ∈ Ioo a b, HasDerivAt (derivWithin Φ (Icc a b))
      (derivWithin (derivWithin Φ (Icc a b)) (Icc a b) x) x) := by
  obtain ⟨h1, h2, h3, h4⟩ := c03sp_v_aux_C2_setup (uniqueDiffOn_Icc hab) hΦ
  exact ⟨h1, h2, h3, fun x hx => (h4 x (Icc_mem_nhds hx.1 hx.2)).1,
    fun x hx => (h4 x (Icc_mem_nhds hx.1 hx.2)).2⟩

/-- `iteratedDerivWithin 2 = derivWithin ∘ derivWithin`. -/
theorem c03sp_v_aux_iteratedDerivWithin_two (Φ : ℝ → ℝ) (s : Set ℝ) :
    iteratedDerivWithin 2 Φ s = derivWithin (derivWithin Φ s) s := by
  rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]

-- Not in Mathlib; proved in this file.
/-- Blueprint: lem:c03sp_v_vdc_first.  Van der Corput, first derivative test on `[a,b]`:
`|∫_a^b e^{iΦ}| ≤ 2 max(|Φ'(a)|⁻¹, |Φ'(b)|⁻¹) ≤ 2/λ` when `Φ'` is monotone and `|Φ'| ≥ λ`. -/
theorem c03sp_v_vdc_first (a b lam : ℝ) (hab : a < b) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Icc a b))
    (hmono : MonotoneOn (derivWithin Φ (Icc a b)) (Icc a b) ∨
      AntitoneOn (derivWithin Φ (Icc a b)) (Icc a b))
    (hlow : ∀ ξ ∈ Icc a b, lam ≤ |derivWithin Φ (Icc a b) ξ|) :
    ‖∫ ξ in a..b, Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
      2 * max (|derivWithin Φ (Icc a b) a|⁻¹) (|derivWithin Φ (Icc a b) b|⁻¹) ∧
    2 * max (|derivWithin Φ (Icc a b) a|⁻¹) (|derivWithin Φ (Icc a b) b|⁻¹) ≤ 2 / lam := by
  obtain ⟨hΦc, hgc, hg'c, hΦd, hgd⟩ := c03sp_v_aux_C2_Icc hab hΦ
  exact ⟨c03sp_v_aux_vdc1 hab hlam hΦc hgc hg'c hΦd hgd hmono hlow,
    c03sp_v_aux_max_inv_le hlam (hlow a ⟨le_rfl, hab.le⟩) (hlow b ⟨hab.le, le_rfl⟩)⟩

-- Not in Mathlib; proved in this file.
/-- Blueprint: lem:c03sp_v_vdc_second.  Van der Corput, second derivative test:
`|Φ''| ≥ λ` on `[a,b]` implies `|∫_a^b e^{iΦ}| ≤ 6 λ^{-1/2}`. -/
theorem c03sp_v_vdc_second (a b lam : ℝ) (hab : a < b) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Icc a b))
    (hlow : ∀ ξ ∈ Icc a b, lam ≤ |iteratedDerivWithin 2 Φ (Icc a b) ξ|) :
    ‖∫ ξ in a..b, Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤ 6 * lam ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨hΦc, hgc, hg'c, hΦd, hgd⟩ := c03sp_v_aux_C2_Icc hab hΦ
  rw [c03sp_v_aux_iteratedDerivWithin_two] at hlow
  exact c03sp_v_aux_vdc2 hab hlam hΦc hgc hg'c hΦd hgd hlow

-- Not in Mathlib; proved in this file.
/-- Blueprint: lem:c03sp_v_vdc_interval_amplitude.  Van der Corput with a `C¹` amplitude on `[a,b]`
(`k = 1`: constant `2`, `λ⁻¹`; `k = 2`: constant `6`, `λ^{-1/2}`), with `|ψ(b)|`, `|ψ(a)|` or a
sup bound `B` for `ψ`, plus `∫_a^b |ψ'|`. -/
theorem c03sp_v_vdc_interval_amplitude (a b lam : ℝ) (hab : a < b) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Icc a b)) (ψ : ℝ → ℂ) (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) :
    (((MonotoneOn (derivWithin Φ (Icc a b)) (Icc a b) ∨
        AntitoneOn (derivWithin Φ (Icc a b)) (Icc a b)) ∧
        ∀ ξ ∈ Icc a b, lam ≤ |derivWithin Φ (Icc a b) ξ|) →
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          2 * lam⁻¹ * (‖ψ b‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          2 * lam⁻¹ * (‖ψ a‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ∀ B : ℝ, (∀ ξ ∈ Icc a b, ‖ψ ξ‖ ≤ B) →
        ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          2 * lam⁻¹ * (B + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖)) ∧
    ((∀ ξ ∈ Icc a b, lam ≤ |iteratedDerivWithin 2 Φ (Icc a b) ξ|) →
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          6 * lam ^ (-(1 / 2 : ℝ)) * (‖ψ b‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          6 * lam ^ (-(1 / 2 : ℝ)) * (‖ψ a‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ∀ B : ℝ, (∀ ξ ∈ Icc a b, ‖ψ ξ‖ ≤ B) →
        ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          6 * lam ^ (-(1 / 2 : ℝ)) * (B + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖)) := by
  obtain ⟨hΦc, hgc, hg'c, hΦd, hgd⟩ := c03sp_v_aux_C2_Icc hab hΦ
  have he : ContinuousOn (fun x => Complex.exp (Complex.I * (Φ x : ℂ))) (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦc))
  refine ⟨fun ⟨hmono, hlow⟩ => ?_, fun hlow => ?_⟩
  · rw [← div_eq_mul_inv]
    refine c03sp_v_aux_amp_all hab he hψ (fun c d hc hcd hd => ?_)
    have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hc hd
    have hsub' : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hc hd
    exact c03sp_v_aux_vdc1' hcd hlam (hΦc.mono hsub) (hgc.mono hsub) (hg'c.mono hsub)
      (fun x hx => hΦd x (hsub' hx)) (fun x hx => hgd x (hsub' hx))
      (hmono.elim (fun h => Or.inl (h.mono hsub)) (fun h => Or.inr (h.mono hsub)))
      (fun x hx => hlow x (hsub hx))
  · rw [c03sp_v_aux_iteratedDerivWithin_two] at hlow
    refine c03sp_v_aux_amp_all hab he hψ (fun c d hc hcd hd => ?_)
    have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hc hd
    have hsub' : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hc hd
    exact c03sp_v_aux_vdc2' hcd hlam (hΦc.mono hsub) (hgc.mono hsub) (hg'c.mono hsub)
      (fun x hx => hΦd x (hsub' hx)) (fun x hx => hgd x (hsub' hx))
      (fun x hx => hlow x (hsub hx))

/-- The constant `∫ e^{-w²/2}(|w|+3) dw`. -/
def c03sp_aux_K3 : ℝ := ∫ w : ℝ, Real.exp (-(w ^ 2) / 2) * (|w| + 3)

theorem c03sp_aux_K3_int : Integrable (fun w : ℝ => Real.exp (-(w ^ 2) / 2) * (|w| + 3)) := by
  have h1 := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := 1) (by norm_num)
  have h0 := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  have h1' : Integrable (fun x : ℝ => |x| * Real.exp (-(1 / 2) * x ^ 2)) := by
    have h1n := h1.norm
    refine h1n.congr (Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_one, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (h1'.add (h0.const_mul 3)).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]; ring_nf

theorem c03sp_aux_K3_nonneg : 0 ≤ c03sp_aux_K3 :=
  integral_nonneg fun w => mul_nonneg (Real.exp_pos _).le (by positivity)

/-- Core of the Fresnel expansion: for `f ∈ C³` with `f(0) = 0` and `f = c g` outside `[-L,L]`,
`|∫ f e^{-iνw²/2}| ≤ 6 ν^{-3/2} (B + 2LB + 2B K₃)`. -/
theorem c03sp_aux_fresnel_core {ν L B : ℝ} (hν : 0 < ν) (hL : 1 ≤ L) (c : ℂ) (hc : ‖c‖ ≤ B)
    {f f1 f2 f3 : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f1 x) x) (hf1 : ∀ x, HasDerivAt f1 (f2 x) x)
    (hf2 : ∀ x, HasDerivAt f2 (f3 x) x) (hf3c : Continuous f3)
    (hb1 : ∀ x, ‖f1 x‖ ≤ B) (hb2 : ∀ x, ‖f2 x‖ ≤ B) (hb3 : ∀ x, ‖f3 x‖ ≤ B) (hf0 : f 0 = 0)
    (hout : ∀ x, L < |x| → f x = c * c03sp_aux_g0 x) :
    Integrable (fun w : ℝ => f w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))) ∧
    ‖∫ w : ℝ, f w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))‖ ≤
      6 * ν ^ (-(3 / 2 : ℝ)) * (B + 2 * L * B + 2 * B * c03sp_aux_K3) := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) hc
  have hf1c : Continuous f1 := continuous_iff_continuousAt.2 fun x => (hf1 x).continuousAt
  have hf2c : Continuous f2 := continuous_iff_continuousAt.2 fun x => (hf2 x).continuousAt
  set d : ℝ → ℂ := fun w => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 0 * f1 (t * w) with hd
  set d1 : ℝ → ℂ := fun w => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (0 + 1) * f2 (t * w) with hd1
  set d2 : ℝ → ℂ := fun w => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (1 + 1) * f3 (t * w) with hd2
  have hdd : ∀ w, HasDerivAt d (d1 w) w := fun w =>
    c03sp_aux_param_deriv hf1 hf2c hb2 0 w
  have hdd1 : ∀ w, HasDerivAt d1 (d2 w) w := fun w =>
    c03sp_aux_param_deriv hf2 hf3c hb3 1 w
  have hfd : ∀ w, f w = (w : ℂ) * d w := by
    intro w; rw [c03sp_aux_div_formula hf hf1c hf0 w]; simp [hd]
  have hbint : ∀ (k : ℕ) (G : ℝ → ℂ), (∀ x, ‖G x‖ ≤ B) → ∀ w,
      ‖∫ t in (0 : ℝ)..1, (t : ℂ) ^ k * G (t * w)‖ ≤ B := by
    intro k G hG w
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := B)
      (f := fun t => (t : ℂ) ^ k * G (t * w)) (fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
        calc t ^ k * ‖G (t * w)‖ ≤ 1 * B :=
              mul_le_mul (pow_le_one₀ ht.1.le ht.2) (hG _) (norm_nonneg _) zero_le_one
          _ = B := one_mul B)
    simpa using this
  have hdb : ∀ w, ‖d w‖ ≤ B := hbint 0 f1 hb1
  have hd1b : ∀ w, ‖d1 w‖ ≤ B := hbint 1 f2 hb2
  have hd2b : ∀ w, ‖d2 w‖ ≤ B := hbint 2 f3 hb3
  have hd2c : Continuous d2 := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (Complex.continuous_ofReal.comp continuous_snd).pow _ |>.mul
      (hf3c.comp (continuous_snd.mul continuous_fst))
  -- outside `[-L,L]`
  set g0 := c03sp_aux_g0 with hg0
  have hU : IsOpen {x : ℝ | L < |x|} := isOpen_lt continuous_const continuous_abs
  have hne : ∀ x : ℝ, L < |x| → (x : ℂ) ≠ 0 := fun x hx h => by
    have : x = 0 := by exact_mod_cast h
    rw [this, abs_zero] at hx; linarith
  set P0 : ℝ → ℂ := fun x => c * (x : ℂ)⁻¹ with hP0
  set P1 : ℝ → ℂ := fun x => -c * ((x : ℂ) ^ 2)⁻¹ - c with hP1
  have hP0d : ∀ w : ℝ, (w : ℂ) ≠ 0 → HasDerivAt P0 (-c * ((w : ℂ) ^ 2)⁻¹) w := by
    intro w hw
    have h := ((hasDerivAt_id' (w : ℂ)).inv hw).const_mul c
    have := h.comp_ofReal
    convert this using 1; field_simp
  have hP1d : ∀ w : ℝ, (w : ℂ) ≠ 0 → HasDerivAt P1 (2 * c * ((w : ℂ) ^ 3)⁻¹) w := by
    intro w hw
    have h := ((((hasDerivAt_id' (w : ℂ)).pow 2).inv (pow_ne_zero 2 hw)).const_mul (-c)).sub_const c
    have := h.comp_ofReal
    convert this using 1
    simp only [Pi.pow_apply]; field_simp; ring
  have hdout : ∀ x : ℝ, L < |x| → d x = P0 x * g0 x := by
    intro x hx
    have h1 := hfd x; rw [hout x hx] at h1
    simp only [hP0]
    have hx0 := hne x hx
    calc d x = (x : ℂ)⁻¹ * ((x : ℂ) * d x) := by field_simp
      _ = c * (x : ℂ)⁻¹ * g0 x := by rw [← h1]; ring
  have hd1out : ∀ w : ℝ, L < |w| → d1 w = P1 w * g0 w := by
    intro w hw
    have hev : d =ᶠ[𝓝 w] fun x => P0 x * g0 x := by
      filter_upwards [hU.mem_nhds hw] with x hx using hdout x hx
    have h' := (hdd w).congr_of_eventuallyEq hev.symm
    rw [h'.unique (c03sp_aux_g0_hasDerivAt (hP0d w (hne w hw)))]
    simp only [hP1, hP0]; congr 1; field_simp [hne w hw]
  have hd2out : ∀ w : ℝ, L < |w| →
      d2 w = (2 * c * ((w : ℂ) ^ 3)⁻¹ - w * P1 w) * g0 w := by
    intro w hw
    have hev : d1 =ᶠ[𝓝 w] fun x => P1 x * g0 x := by
      filter_upwards [hU.mem_nhds hw] with x hx using hd1out x hx
    have h' := (hdd1 w).congr_of_eventuallyEq hev.symm
    exact h'.unique (c03sp_aux_g0_hasDerivAt (hP1d w (hne w hw)))
  -- norms outside
  have hinv : ∀ w : ℝ, L < |w| → ‖((w : ℂ))⁻¹‖ ≤ 1 := by
    intro w hw
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hP0n : ∀ w : ℝ, L < |w| → ‖P0 w‖ ≤ B := by
    intro w hw; simp only [hP0, norm_mul]
    calc ‖c‖ * ‖((w : ℂ))⁻¹‖ ≤ B * 1 := mul_le_mul hc (hinv w hw) (norm_nonneg _) hB
      _ = B := mul_one B
  have hP1n : ∀ w : ℝ, L < |w| → ‖P1 w‖ ≤ 2 * B := by
    intro w hw; simp only [hP1]
    have h2 : ‖((w : ℂ) ^ 2)⁻¹‖ ≤ 1 := by
      rw [← inv_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hinv w hw)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_neg]
    nlinarith [norm_nonneg ((w : ℂ) ^ 2)⁻¹, norm_nonneg c]
  have hexp_nn : ∀ w : ℝ, 0 ≤ Real.exp (-(w ^ 2) / 2) * (|w| + 3) := fun w =>
    mul_nonneg (Real.exp_pos _).le (by positivity)
  have hd1on : ∀ w : ℝ, L < |w| → ‖d1 w‖ ≤ 2 * B * (Real.exp (-(w ^ 2) / 2) * (|w| + 3)) := by
    intro w hw
    rw [hd1out w hw, norm_mul, hg0, c03sp_aux_g0_norm]
    have := hP1n w hw
    have he := (Real.exp_pos (-(w ^ 2) / 2)).le
    calc ‖P1 w‖ * Real.exp (-(w ^ 2) / 2) ≤ 2 * B * Real.exp (-(w ^ 2) / 2) :=
          mul_le_mul_of_nonneg_right this he
      _ ≤ _ := by
          have h3 : Real.exp (-(w ^ 2) / 2) ≤ Real.exp (-(w ^ 2) / 2) * (|w| + 3) := by
            nlinarith [abs_nonneg w]
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hd2on : ∀ w : ℝ, L < |w| → ‖d2 w‖ ≤ 2 * B * (Real.exp (-(w ^ 2) / 2) * (|w| + 3)) := by
    intro w hw
    rw [hd2out w hw, norm_mul, hg0, c03sp_aux_g0_norm]
    have h3 : ‖((w : ℂ) ^ 3)⁻¹‖ ≤ 1 := by
      rw [← inv_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hinv w hw)
    have hA : ‖2 * c * ((w : ℂ) ^ 3)⁻¹ - w * P1 w‖ ≤ 2 * B + |w| * (2 * B) := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_mul, Complex.norm_two]
        nlinarith [norm_nonneg ((w : ℂ) ^ 3)⁻¹, norm_nonneg c]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hP1n w hw) (abs_nonneg w)
    have he := (Real.exp_pos (-(w ^ 2) / 2)).le
    calc ‖2 * c * ((w : ℂ) ^ 3)⁻¹ - w * P1 w‖ * Real.exp (-(w ^ 2) / 2)
        ≤ (2 * B + |w| * (2 * B)) * Real.exp (-(w ^ 2) / 2) := mul_le_mul_of_nonneg_right hA he
      _ ≤ _ := by nlinarith [abs_nonneg w]
  -- the majorant
  set m : ℝ → ℝ := fun w => (Icc (-L) L).indicator (fun _ => B) w +
    2 * B * (Real.exp (-(w ^ 2) / 2) * (|w| + 3)) with hm
  have hm_int : Integrable m := by
    refine Integrable.add ?_ (c03sp_aux_K3_int.const_mul _)
    exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have hm_val : ∫ w, m w = 2 * L * B + 2 * B * c03sp_aux_K3 := by
    rw [hm, integral_add ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc)
      (c03sp_aux_K3_int.const_mul _), integral_indicator_const _ measurableSet_Icc,
      integral_const_mul, c03sp_aux_K3, Real.volume_real_Icc_of_le (by linarith)]
    simp only [smul_eq_mul]; ring
  have hmb : ∀ w, ∀ z : ℂ, (‖z‖ ≤ B) → (L < |w| → ‖z‖ ≤ 2 * B * (Real.exp (-(w ^ 2) / 2) * (|w| + 3)))
      → ‖z‖ ≤ m w := by
    intro w z h1 h2
    by_cases hw : L < |w|
    · have : 0 ≤ (Icc (-L) L).indicator (fun _ => B) w :=
        Set.indicator_nonneg (fun _ _ => hB) w
      simp only [hm]; linarith [h2 hw]
    · have hmem : w ∈ Icc (-L) L := abs_le.1 (not_lt.1 hw)
      simp only [hm, Set.indicator_of_mem hmem]
      have := hexp_nn w
      nlinarith
  have hd1m : ∀ w, ‖d1 w‖ ≤ m w := fun w => hmb w _ (hd1b w) (hd1on w)
  have hd2m : ∀ w, ‖d2 w‖ ≤ m w := fun w => hmb w _ (hd2b w) (hd2on w)
  -- the chirp
  set E : ℝ → ℂ := fun w => Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2)) with hE
  have hEn : ∀ w, ‖E w‖ = 1 := by
    intro w; simp only [hE]
    rw [show -(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2) = ((-(ν * w ^ 2 / 2) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hEc : Continuous E := by simp only [hE]; fun_prop
  have hEd : ∀ w : ℝ, HasDerivAt E (E w * (-(Complex.I * ν * w))) w := by
    intro w
    have h : HasDerivAt (fun x : ℝ => -(Complex.I * (ν : ℂ) * (x : ℂ) ^ 2 / 2))
        (-(Complex.I * ν * w)) w := by
      have := (((hasDerivAt_id' w).ofReal_comp.pow 2).const_mul (Complex.I * (ν : ℂ))).div_const 2
      convert this.neg using 1; push_cast; ring
    exact h.cexp
  have hd1c : Continuous d1 := continuous_iff_continuousAt.2 fun x => (hdd1 x).continuousAt
  have hdc : Continuous d := continuous_iff_continuousAt.2 fun x => (hdd x).continuousAt
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hd1E : Integrable (fun w => d1 w * E w) := by
    refine Integrable.mono' hm_int (hd1c.mul hEc).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul, hEn, mul_one]; exact hd1m w
  have hfE : Integrable (fun w => f w * E w) := by
    refine Integrable.mono' (hm_int.const_mul L) (hfc.mul hEc).aestronglyMeasurable
      (Eventually.of_forall fun w => ?_)
    rw [norm_mul, hEn, mul_one]
    by_cases hw : L < |w|
    · rw [hout w hw, norm_mul, hg0, c03sp_aux_g0_norm]
      have := hmb w (c * c03sp_aux_g0 w) (by
          rw [norm_mul, c03sp_aux_g0_norm]
          calc ‖c‖ * Real.exp (-(w ^ 2) / 2) ≤ B * 1 :=
                mul_le_mul hc (by rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg w])
                  (Real.exp_pos _).le hB
            _ = B := mul_one B) (fun _ => by
          rw [norm_mul, c03sp_aux_g0_norm]
          have he := (Real.exp_pos (-(w ^ 2) / 2)).le
          calc ‖c‖ * Real.exp (-(w ^ 2) / 2) ≤ B * Real.exp (-(w ^ 2) / 2) :=
                mul_le_mul_of_nonneg_right hc he
            _ ≤ _ := by
                have h3 : Real.exp (-(w ^ 2) / 2) ≤ 2 * (Real.exp (-(w ^ 2) / 2) * (|w| + 3)) := by
                  nlinarith [abs_nonneg w]
                have := mul_le_mul_of_nonneg_left h3 hB
                linarith)
      rw [norm_mul, c03sp_aux_g0_norm] at this
      have hm0 : 0 ≤ m w := le_trans (by positivity) this
      nlinarith
    · rw [hfd w, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hmb w (d w) (hdb w) (fun h => absurd h hw)
      exact mul_le_mul (not_lt.1 hw) this (norm_nonneg _) (by linarith)
  -- integration by parts on the line
  set v : ℝ → ℂ := fun w => Complex.I / ν * E w with hv
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hvd : ∀ w : ℝ, HasDerivAt v ((w : ℂ) * E w) w := by
    intro w
    have := (hEd w).const_mul (Complex.I / ν)
    convert this using 1
    field_simp; ring_nf; rw [Complex.I_sq]; ring
  have hvn : ∀ w, ‖v w‖ = ν⁻¹ := by
    intro w; simp only [hv, norm_mul, norm_div, Complex.norm_I, hEn, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hν]; ring
  have hdv_bound : ∀ w, L < |w| → ‖d w * v w‖ ≤ B * ν⁻¹ * Real.exp (-(w ^ 2) / 2) := by
    intro w hw
    rw [norm_mul, hvn, hdout w hw, norm_mul, hg0, c03sp_aux_g0_norm]
    have := hP0n w hw
    have he := (Real.exp_pos (-(w ^ 2) / 2)).le
    have hνi : 0 ≤ ν⁻¹ := by positivity
    calc ‖P0 w‖ * Real.exp (-(w ^ 2) / 2) * ν⁻¹ ≤ B * Real.exp (-(w ^ 2) / 2) * ν⁻¹ := by gcongr
      _ = _ := by ring
  have hexp_top : Tendsto (fun w : ℝ => Real.exp (-(w ^ 2) / 2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have : Tendsto (fun w : ℝ => w ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
    exact (tendsto_neg_atTop_atBot.comp this).atBot_div_const two_pos
  have hexp_bot : Tendsto (fun w : ℝ => Real.exp (-(w ^ 2) / 2)) atBot (𝓝 0) := by
    have := hexp_top.comp tendsto_neg_atBot_atTop
    refine this.congr (fun w => ?_); simp
  have hlim : ∀ l : Filter ℝ, Tendsto (fun w : ℝ => Real.exp (-(w ^ 2) / 2)) l (𝓝 0) →
      (∀ᶠ w in l, L < |w|) → Tendsto (d * v) l (𝓝 0) := by
    intro l hl hev
    have h0 : Tendsto (fun w => B * ν⁻¹ * Real.exp (-(w ^ 2) / 2)) l (𝓝 0) := by
      simpa using hl.const_mul (B * ν⁻¹)
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hev] with w hw using hdv_bound w hw
  have htop : ∀ᶠ w : ℝ in atTop, L < |w| := by
    filter_upwards [eventually_gt_atTop L] with w hw
    exact lt_of_lt_of_le hw (le_abs_self w)
  have hbot : ∀ᶠ w : ℝ in atBot, L < |w| := by
    filter_upwards [eventually_lt_atBot (-L)] with w hw
    exact lt_of_lt_of_le (by linarith) (neg_le_abs w)
  have hibp := integral_mul_deriv_eq_deriv_mul (u := d) (v := v) (u' := d1)
    (v' := fun w => (w : ℂ) * E w) (a' := 0) (b' := 0)
    (fun x _ => hdd x) (fun x _ => hvd x)
    (by
      refine hfE.congr (Eventually.of_forall fun w => ?_)
      simp only [Pi.mul_apply]; rw [hfd w]; ring)
    (by
      refine (hd1E.const_mul (Complex.I / ν)).congr (Eventually.of_forall fun w => ?_)
      simp only [Pi.mul_apply, hv]; ring)
    (hlim atBot hexp_bot hbot) (hlim atTop hexp_top htop)
  have hfEeq : ∫ w, f w * E w = -(Complex.I / ν) * ∫ w, d1 w * E w := by
    have e1 : ∫ w, f w * E w = ∫ w, d w * ((w : ℂ) * E w) := by
      congr 1; funext w; rw [hfd w]; ring
    rw [e1, hibp, ← integral_const_mul]
    simp only [hv, sub_self, zero_sub, ← integral_neg]
    congr 1; funext w; ring
  -- van der Corput on `[-R,R]`
  set Φ : ℝ → ℝ := fun x => -(ν * x ^ 2 / 2) with hΦ
  have hΦC : ContDiff ℝ 2 Φ := by simp only [hΦ]; fun_prop
  have hΦd : ∀ x, HasDerivAt Φ (-(ν * x)) x := by
    intro x
    have := (((hasDerivAt_id' x).pow 2).const_mul ν).div_const 2
    convert this.neg using 1; push_cast; ring
  have hΦ1 : deriv Φ = fun x => -(ν * x) := funext fun x => (hΦd x).deriv
  have hΦ2 : deriv (deriv Φ) = fun _ => -ν := by
    rw [hΦ1]; funext x
    have : HasDerivAt (fun x : ℝ => -(ν * x)) (-(ν * 1)) x := ((hasDerivAt_id' x).const_mul ν).neg
    rw [this.deriv]; ring
  have hd1C : ContDiff ℝ 1 d1 := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hdd1 x).differentiableAt, ?_⟩
    rw [show deriv d1 = d2 from funext fun x => (hdd1 x).deriv]; exact hd2c
  have hint_m : ∀ R : ℝ, 0 < R → ∫ ξ in (-R)..R, ‖d2 ξ‖ ≤ 2 * L * B + 2 * B * c03sp_aux_K3 := by
    intro R hR
    rw [← hm_val]
    calc ∫ ξ in (-R)..R, ‖d2 ξ‖ ≤ ∫ ξ in (-R)..R, m ξ := by
          apply intervalIntegral.integral_mono_on (by linarith)
            (hd2c.norm.intervalIntegrable _ _) (hm_int.intervalIntegrable)
          intro ξ _; exact hd2m ξ
      _ ≤ ∫ ξ, m ξ := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          apply setIntegral_le_integral hm_int
          exact Eventually.of_forall fun ξ => le_trans (norm_nonneg _) (hd2m ξ)
  have hvdcR : ∀ R : ℝ, 0 < R → ‖∫ ξ in (-R)..R, d1 ξ * E ξ‖ ≤
      6 * ν ^ (-(1 / 2 : ℝ)) * (B + (2 * L * B + 2 * B * c03sp_aux_K3)) := by
    intro R hR
    have hab : -R < R := by linarith
    have hv := ((c03sp_v_vdc_interval_amplitude (-R) R ν hab hν Φ hΦC.contDiffOn d1
      hd1C.contDiffOn).2 (fun ξ hξ => by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
          (hΦC.contDiffAt) hξ, iteratedDeriv_succ, iteratedDeriv_one, hΦ2]
        simp [abs_of_pos hν])).2.2 B (fun ξ _ => hd1b ξ)
    have hEq : ∫ ξ in (-R)..R, d1 ξ * Complex.exp (Complex.I * (Φ ξ : ℂ)) =
        ∫ ξ in (-R)..R, d1 ξ * E ξ := by
      apply intervalIntegral.integral_congr; intro ξ _
      simp only [hΦ, hE]; congr 2; push_cast; ring
    have hD : ∫ ξ in (-R)..R, ‖derivWithin d1 (Icc (-R) R) ξ‖ = ∫ ξ in (-R)..R, ‖d2 ξ‖ := by
      apply intervalIntegral.integral_congr; intro ξ hξ
      rw [uIcc_of_le hab.le] at hξ
      simp only
      rw [(hdd1 ξ).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab ξ hξ)]
    rw [hEq, hD] at hv
    refine hv.trans ?_
    gcongr
    exact hint_m R hR
  have hlimR := intervalIntegral_tendsto_integral hd1E tendsto_neg_atTop_atBot tendsto_id
  have hd1Eb : ‖∫ w, d1 w * E w‖ ≤
      6 * ν ^ (-(1 / 2 : ℝ)) * (B + (2 * L * B + 2 * B * c03sp_aux_K3)) := by
    refine le_of_tendsto hlimR.norm ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact hvdcR R hR
  refine ⟨hfE, ?_⟩
  change ‖∫ w, f w * E w‖ ≤ _
  rw [hfEeq, norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hν]
  have h32 : ν ^ (-(3 / 2 : ℝ)) = 1 / ν * ν ^ (-(1 / 2 : ℝ)) := by
    rw [show -(3 / 2 : ℝ) = -1 + -(1 / 2) by norm_num, Real.rpow_add hν, Real.rpow_neg_one]
    ring
  rw [h32]
  calc 1 / ν * ‖∫ w, d1 w * E w‖ ≤ 1 / ν *
        (6 * ν ^ (-(1 / 2 : ℝ)) * (B + (2 * L * B + 2 * B * c03sp_aux_K3))) := by
        gcongr
    _ = _ := by ring

/-- `‖e^{(i)}(x)‖ ≤ ‖e‖_{C^k}` for compactly supported `e ∈ C^k`, `i ≤ k`. -/
theorem c03sp_aux_Ck_le {e : ℝ → ℂ} {k : ℕ} (he : ContDiff ℝ k e) (hs : HasCompactSupport e)
    {i : ℕ} (hi : i ≤ k) (x : ℝ) : ‖iteratedDeriv i e x‖ ≤ c03_Ck_normR k univ e := by
  have hcs : ∀ j : ℕ, HasCompactSupport (iteratedDeriv j e) := by
    intro j; rw [iteratedDeriv_eq_iterate]
    induction j with
    | zero => simpa using hs
    | succ n ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  have hb : ∀ j ∈ Finset.range (k + 1), (⨆ y ∈ univ, ‖iteratedDerivWithin j e univ y‖ₑ) ≠ ⊤ := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    obtain ⟨C, hC⟩ := (he.continuous_iteratedDeriv j (by exact_mod_cast hjk)).bounded_above_of_compact_support
      (hcs j)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup₂_le fun y _ => ?_)
    rw [iteratedDerivWithin_univ, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC y)
  unfold c03_Ck_normR c03_Ck_norm
  have hS := ENNReal.sum_ne_top.2 hb
  have h1 : ‖iteratedDeriv i e x‖ₑ ≤
      ∑ j ∈ Finset.range (k + 1), ⨆ y ∈ univ, ‖iteratedDerivWithin j e univ y‖ₑ := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ y ∈ univ,
      ‖iteratedDerivWithin j e univ y‖ₑ) (fun _ _ => zero_le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
    refine le_iSup₂_of_le x (mem_univ x) ?_
    rw [iteratedDerivWithin_univ]
  have := ENNReal.toReal_mono hS h1
  rwa [toReal_enorm] at this

theorem c03sp_aux_fresnel_value {ν : ℝ} (hν : 0 < ν) :
    ((π : ℂ) / ((0 + Complex.I * ν) / 2)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 * π / ν) : ℂ) * Complex.exp (-(Complex.I * (π / 4 : ℝ))) := by
  set r : ℝ := 2 * π / ν with hr
  have hrp : 0 < r := by positivity
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have h1 : (π : ℂ) / ((0 + Complex.I * ν) / 2) = (r : ℂ) * (-Complex.I) := by
    rw [hr]; push_cast; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [h1, Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hrp.ne')
    (neg_ne_zero.2 Complex.I_ne_zero)), Complex.log_ofReal_mul hrp
    (neg_ne_zero.2 Complex.I_ne_zero), Complex.log_neg_I]
  have h2 : ((Real.log r : ℂ) + -(π / 2) * Complex.I) * (1 / 2) =
      ((Real.log r / 2 : ℝ) : ℂ) + (-(Complex.I * (π / 4 : ℝ))) := by push_cast; ring
  rw [h2, Complex.exp_add, ← Complex.ofReal_exp]
  congr 2
  rw [← Real.log_sqrt hrp.le, Real.exp_log (Real.sqrt_pos.2 hrp)]

/-- `|(π/b)^{1/2} - (2π/ν)^{1/2}e^{-iπ/4}| ≤ 2ν^{-3/2}` for `b = (1+iν)/2`. -/
theorem c03sp_aux_fresnel_gauss {ν : ℝ} (hν : 0 < ν) :
    ‖((π : ℂ) / ((1 + Complex.I * ν) / 2)) ^ (1 / 2 : ℂ) -
      (Real.sqrt (2 * π / ν) : ℂ) * Complex.exp (-(Complex.I * (π / 4 : ℝ)))‖ ≤
      2 * ν ^ (-(3 / 2 : ℝ)) := by
  rw [← c03sp_aux_fresnel_value hν]
  have hz0 : ∀ s : ℝ, ((s : ℂ) + Complex.I * ν) ≠ 0 := by
    intro s h; have := congrArg Complex.im h; simp at this; linarith
  have hnorm : ∀ s : ℝ, ν ≤ ‖(s : ℂ) + Complex.I * ν‖ := by
    intro s
    have : |((s : ℂ) + Complex.I * ν).im| ≤ ‖(s : ℂ) + Complex.I * ν‖ := Complex.abs_im_le_norm _
    simpa [abs_of_pos hν] using this
  set u : ℂ → ℂ := fun z => 2 * π / (z + Complex.I * ν) with hu
  have hend : ∀ s : ℝ, (π : ℂ) / (((s : ℂ) + Complex.I * ν) / 2) = u s := by
    intro s; simp only [hu]; field_simp [hz0 s]
  have e1 := hend 1
  have e0 := hend 0
  push_cast at e1 e0
  rw [e1, e0]
  have hslit : ∀ s : ℝ, u s ∈ Complex.slitPlane := by
    intro s
    apply Or.inr
    simp only [hu]
    rw [Complex.div_im]
    simp
    constructor <;> [positivity; exact (hz0 s)]
  have hun : ∀ s : ℝ, u s ≠ 0 := by
    intro s; simp only [hu]
    exact div_ne_zero (by norm_num [Real.pi_ne_zero]) (hz0 s)
  set u' : ℂ → ℂ := fun z => (0 * (z + Complex.I * ν) - 2 * π * 1) / (z + Complex.I * ν) ^ 2
  have hud : ∀ s : ℝ, HasDerivAt u (u' s) (s : ℂ) := by
    intro s
    exact (hasDerivAt_const (s : ℂ) (2 * (π : ℂ))).div
      ((hasDerivAt_id' (s : ℂ)).add_const (Complex.I * ν)) (hz0 s)
  have hgd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => u s ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * u s ^ ((1 / 2 : ℂ) - 1) * u' s) s := fun s =>
    ((hud s).cpow_const (hslit s)).comp_ofReal
  have hbd : ∀ s : ℝ, ‖(1 / 2 : ℂ) * u s ^ ((1 / 2 : ℂ) - 1) * u' s‖ ≤ 2 * ν ^ (-(3 / 2 : ℝ)) := by
    intro s
    set R := ‖(s : ℂ) + Complex.I * ν‖ with hR
    have hRν : ν ≤ R := hnorm s
    have hRp : 0 < R := lt_of_lt_of_le hν hRν
    have hnu : ‖u s‖ = 2 * π / R := by
      simp only [hu, norm_div, hR]; simp [abs_of_pos Real.pi_pos]
    have hnu' : ‖u' s‖ = 2 * π / R ^ 2 := by
      simp only [u', norm_div, norm_pow, hR]; simp [abs_of_pos Real.pi_pos]
    have hcp : ‖u s ^ ((1 / 2 : ℂ) - 1)‖ = (2 * π / R) ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.norm_cpow_of_ne_zero (hun s), hnu]; norm_num
    rw [norm_mul, norm_mul, hcp, hnu']
    have hsq : ∀ x : ℝ, 0 ≤ x → x ^ (1 / 2 : ℝ) = Real.sqrt x := fun x _ =>
      (Real.sqrt_eq_rpow x).symm
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hRp
    have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
    have hs2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
    have hA : (2 * π / R) ^ (-(1 / 2 : ℝ)) = Real.sqrt R / Real.sqrt (2 * π) := by
      rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) hRp.le,
        hsq _ (by positivity), hsq _ hRp.le, inv_div]
    have hB : ν ^ (-(3 / 2 : ℝ)) = (ν * Real.sqrt ν)⁻¹ := by
      rw [Real.rpow_neg hν.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hν,
        Real.rpow_one, hsq ν hν.le]
    have hC : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hA, hB, hC]
    have hkey : π ≤ 2 * Real.sqrt (2 * π) := by
      have h1 : Real.sqrt (2 * π) * Real.sqrt (2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
      nlinarith [Real.pi_pos, Real.pi_lt_four]
    have hmono : ν * Real.sqrt ν ≤ R * Real.sqrt R :=
      mul_le_mul hRν (Real.sqrt_le_sqrt hRν) hsν.le hRp.le
    have hRR : R ^ 2 = R * Real.sqrt R * Real.sqrt R := by
      rw [mul_assoc, Real.mul_self_sqrt hRp.le]; ring
    rw [hRR]
    rw [show 1 / 2 * (Real.sqrt R / Real.sqrt (2 * π)) * (2 * π / (R * Real.sqrt R * Real.sqrt R)) =
      π / Real.sqrt (2 * π) * (R * Real.sqrt R)⁻¹ by field_simp]
    apply mul_le_mul _ (inv_anti₀ (by positivity) hmono) (by positivity) (by norm_num)
    rw [div_le_iff₀ hs2]; linarith
  have := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
    (f := fun s : ℝ => u s ^ (1 / 2 : ℂ)) (fun s _ => (hgd s).hasDerivWithinAt)
    (fun s _ => hbd s) 1 ⟨zero_le_one, le_rfl⟩
  simp only [Complex.ofReal_one, Complex.ofReal_zero, sub_zero, mul_one] at this
  exact this


/-- Blueprint: lem:c03_fresnel_expansion.  For `e ∈ C³` supported in `[-L,L]`:
`|∫ e(w) e^{-iνw²/2} dw - (2π/ν)^{1/2} e^{-iπ/4} e(0)| ≤ C L ν^{-3/2} ‖e‖_{C³(ℝ)}`. -/
theorem c03sp_c03_fresnel_expansion :
    ∃ C, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ L : ℝ, 1 ≤ L → ∀ e : ℝ → ℂ, ContDiff ℝ 3 e →
      (∀ w, L < |w| → e w = 0) →
      ‖(∫ w : ℝ, e w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))) -
          (Real.sqrt (2 * π / ν) : ℂ) * Complex.exp (-(Complex.I * (π / 4 : ℝ))) * e 0‖ ≤
        C * L * ν ^ (-(3 / 2 : ℝ)) * c03_Ck_normR 3 univ e := by
  have hK := c03sp_aux_K3_nonneg
  refine ⟨600 + 396 * c03sp_aux_K3, by positivity, ?_⟩
  intro ν hν L hL e he hsupp
  set N := c03_Ck_normR 3 univ e with hNdef
  have hs : HasCompactSupport e := HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L))
    (fun x hx => hsupp x (by
      by_contra h; exact hx (abs_le.1 (not_lt.1 h))))
  have hN : ∀ i ≤ 3, ∀ x, ‖iteratedDeriv i e x‖ ≤ N := fun i hi x =>
    c03sp_aux_Ck_le he hs hi x
  have he3 : ContDiff ℝ (2 + 1) e := he
  obtain ⟨hdiff0, -, he1C⟩ := contDiff_succ_iff_deriv.1 he3
  have he1C' : ContDiff ℝ (1 + 1) (deriv e) := he1C
  obtain ⟨hdiff1, -, he2C⟩ := contDiff_succ_iff_deriv.1 he1C'
  have he2C' : ContDiff ℝ (0 + 1) (deriv (deriv e)) := he2C
  obtain ⟨hdiff2, -, he3C⟩ := contDiff_succ_iff_deriv.1 he2C'
  have hN0 : ∀ x, ‖e x‖ ≤ N := fun x => by simpa using hN 0 (by norm_num) x
  have hN1 : ∀ x, ‖deriv e x‖ ≤ N := fun x => by simpa using hN 1 (by norm_num) x
  have hN2 : ∀ x, ‖deriv (deriv e) x‖ ≤ N := fun x => by
    have := hN 2 (by norm_num) x
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  have hN3 : ∀ x, ‖deriv (deriv (deriv e)) x‖ ≤ N := fun x => by
    have := hN 3 (by norm_num) x
    rwa [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at this
  have hNnn : 0 ≤ N := le_trans (norm_nonneg _) (hN0 0)
  -- the Gaussian and its derivatives
  set g0 := c03sp_aux_g0 with hg0
  set G1 : ℝ → ℂ := fun w => -(w : ℂ) * g0 w
  set G2 : ℝ → ℂ := fun w => ((w : ℂ) ^ 2 - 1) * g0 w
  set G3 : ℝ → ℂ := fun w => (3 * (w : ℂ) - (w : ℂ) ^ 3) * g0 w
  have hid : ∀ w : ℝ, HasDerivAt (fun x : ℝ => (x : ℂ)) 1 w := fun w =>
    (hasDerivAt_id' w).ofReal_comp
  have hG0 : ∀ w, HasDerivAt g0 (G1 w) w := by
    intro w
    have := c03sp_aux_g0_hasDerivAt (P := fun _ => (1 : ℂ)) (hasDerivAt_const w (1 : ℂ))
    convert this using 1
    · funext x; simp [hg0]
    · simp only [G1]; ring
  have hG1 : ∀ w, HasDerivAt G1 (G2 w) w := by
    intro w
    have := c03sp_aux_g0_hasDerivAt (P := fun x : ℝ => -(x : ℂ)) (hid w).neg
    convert this using 1; simp only [G2]; ring
  have hG2 : ∀ w, HasDerivAt G2 (G3 w) w := by
    intro w
    have := c03sp_aux_g0_hasDerivAt (P := fun x : ℝ => (x : ℂ) ^ 2 - 1)
      (((hid w).pow 2).sub_const 1)
    convert this using 1; simp only [G3]; push_cast; ring
  have hgn : ∀ w, ‖g0 w‖ = Real.exp (-(w ^ 2) / 2) := c03sp_aux_g0_norm
  have hP1 := fun w => c03sp_aux_poly_gauss w (j := 1) (by norm_num)
  have hP2 := fun w => c03sp_aux_poly_gauss w (j := 2) (by norm_num)
  have hP3 := fun w => c03sp_aux_poly_gauss w (j := 3) (by norm_num)
  have hP0 := fun w => c03sp_aux_poly_gauss w (j := 0) (by norm_num)
  have hG1b : ∀ w, ‖G1 w‖ ≤ 32 := by
    intro w; simp only [G1, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, hgn]
    have := hP1 w; simp only [pow_one] at this; linarith
  have hG2b : ∀ w, ‖G2 w‖ ≤ 32 := by
    intro w; simp only [G2, norm_mul, hgn]
    have h : ‖(w : ℂ) ^ 2 - 1‖ ≤ |w| ^ 2 + 1 := by
      refine (norm_sub_le _ _).trans ?_
      simp [Complex.norm_real]
    have := hP2 w; have := hP0 w; simp only [pow_zero, one_mul] at this
    have he := (Real.exp_pos (-(w ^ 2) / 2)).le
    nlinarith
  have hG3b : ∀ w, ‖G3 w‖ ≤ 32 := by
    intro w; simp only [G3, norm_mul, hgn]
    have h : ‖3 * (w : ℂ) - (w : ℂ) ^ 3‖ ≤ 3 * |w| + |w| ^ 3 := by
      refine (norm_sub_le _ _).trans ?_
      simp [Complex.norm_real]
    have := hP1 w; have := hP3 w; simp only [pow_one] at *
    have he := (Real.exp_pos (-(w ^ 2) / 2)).le
    nlinarith
  -- `f = e - e(0) g`
  set c : ℂ := e 0
  set f : ℝ → ℂ := fun w => e w - c * g0 w with hf
  have hf0 : f 0 = 0 := by simp [hf, hg0, c03sp_aux_g0, c]
  have hcore := c03sp_aux_fresnel_core (B := 33 * N) hν hL (-c) (by
      rw [norm_neg]; linarith [hN0 0])
    (f := f) (f1 := fun w => deriv e w - c * G1 w) (f2 := fun w => deriv (deriv e) w - c * G2 w)
    (f3 := fun w => deriv (deriv (deriv e)) w - c * G3 w)
    (fun x => (hdiff0 x).hasDerivAt.sub ((hG0 x).const_mul c))
    (fun x => (hdiff1 x).hasDerivAt.sub ((hG1 x).const_mul c))
    (fun x => (hdiff2 x).hasDerivAt.sub ((hG2 x).const_mul c))
    (he3C.continuous.sub (continuous_const.mul (by
      simp only [hg0, c03sp_aux_g0]; fun_prop)))
    (fun x => by
      refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      nlinarith [hN1 x, hG1b x, hN0 0, norm_nonneg c, norm_nonneg (G1 x)])
    (fun x => by
      refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      nlinarith [hN2 x, hG2b x, hN0 0, norm_nonneg c, norm_nonneg (G2 x)])
    (fun x => by
      refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
      nlinarith [hN3 x, hG3b x, hN0 0, norm_nonneg c, norm_nonneg (G3 x)])
    hf0 (fun x hx => by simp only [hf, hsupp x hx]; ring)
  obtain ⟨hfE, hfb⟩ := hcore
  -- the Gaussian part
  set b : ℂ := (1 + Complex.I * ν) / 2
  have hb : 0 < b.re := by simp [b]
  have hgE : ∀ w : ℝ, g0 w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2)) =
      Complex.exp (-b * (w : ℂ) ^ 2) := by
    intro w; simp only [hg0, c03sp_aux_g0, b]; rw [← Complex.exp_add]; congr 1; ring
  have hgint : Integrable (fun w : ℝ => g0 w *
      Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))) := by
    simp_rw [hgE]; exact integrable_cexp_neg_mul_sq hb
  have hgval : ∫ w : ℝ, g0 w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2)) =
      ((π : ℂ) / ((1 + Complex.I * ν) / 2)) ^ (1 / 2 : ℂ) := by
    simp_rw [hgE]; exact integral_gaussian_complex hb
  have hsplit : ∫ w : ℝ, e w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2)) =
      c * (∫ w : ℝ, g0 w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))) +
        ∫ w : ℝ, f w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2)) := by
    rw [← integral_const_mul, ← integral_add (hgint.const_mul c) hfE]
    congr 1; funext w; simp only [hf]; ring
  rw [hsplit, hgval]
  have hgauss := c03sp_aux_fresnel_gauss hν
  set S : ℂ := (Real.sqrt (2 * π / ν) : ℂ) * Complex.exp (-(Complex.I * (π / 4 : ℝ)))
  set G : ℂ := ((π : ℂ) / ((1 + Complex.I * ν) / 2)) ^ (1 / 2 : ℂ)
  set If := ∫ w : ℝ, f w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))
  have hX : 0 ≤ ν ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have h1 : ‖c * G + If - S * e 0‖ ≤ N * (2 * ν ^ (-(3 / 2 : ℝ))) + ‖If‖ := by
    rw [show c * G + If - S * e 0 = c * (G - S) + If by simp only [c]; ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    gcongr
    exact hN0 0
  refine h1.trans ?_
  set X := ν ^ (-(3 / 2 : ℝ))
  have hNX : 0 ≤ N * X := mul_nonneg hNnn hX
  have hKX : 0 ≤ c03sp_aux_K3 * (N * X) := mul_nonneg hK hNX
  calc N * (2 * X) + ‖If‖ ≤ N * (2 * X) + 6 * X * (33 * N + 2 * L * (33 * N) +
        2 * (33 * N) * c03sp_aux_K3) := by linarith
    _ = 200 * (N * X) + 396 * L * (N * X) + 396 * (c03sp_aux_K3 * (N * X)) := by ring
    _ ≤ (600 + 396 * c03sp_aux_K3) * L * X * N := by
        have h2 : 200 * (N * X) ≤ 200 * L * (N * X) := by nlinarith
        have h3 : 396 * (c03sp_aux_K3 * (N * X)) ≤ 396 * L * (c03sp_aux_K3 * (N * X)) := by
          nlinarith
        nlinarith


/-- Blueprint: lem:c03_sp_euler.  `q(s) = (h(s) - h(1))/h'(s)` (`h'(s) = 1 - s^p`), `q(1) = 0`. -/
def c03_sp_q (p s : ℝ) : ℝ := if s = 1 then 0 else (c03_h p s - c03_h p 1) / (1 - s ^ p)

/-- Blueprint: lem:c03_sp_euler.  `Tc = ½c - (cq)'`. -/
def c03_sp_T (p : ℝ) (c : ℝ → ℂ) (s : ℝ) : ℂ :=
  c s / 2 - deriv (fun s => c s * (c03_sp_q p s : ℂ)) s


/-- Blueprint: lem:c03_sp_near.  Amplitudes: `a ∈ C^∞(0,∞)`, `a = 0` on `(0,1]`,
`|a^{(k)}(ξ)| ≤ C_k ξ^{m-k}` for `ξ ≥ 1`. -/
def c03_sp_symbol (m : ℝ) : Set (ℝ → ℂ) :=
  {a | ContDiffOn ℝ (⊤ : ℕ∞) a (Ioi 0) ∧ (∀ ξ ∈ Ioc (0 : ℝ) 1, a ξ = 0) ∧
    ∀ k : ℕ, ∃ C, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ C * ξ ^ (m - k)}

/-- Blueprint: lem:c03_sp_near.  The phase `φ_y(ξ) = yξ - ξ^{p+1}/(p+1)`. -/
def c03_sp_phi (p y ξ : ℝ) : ℝ := y * ξ - ξ ^ (p + 1) / (p + 1)

/-- Blueprint: lem:c03_sp_near.  `μ(y) = y^{1+1/p} = λ₀^{p+1}`. -/
def c03_sp_mu (p y : ℝ) : ℝ := y ^ (1 + 1 / p)

/-- Blueprint: lem:c03_sp_near.  `P(y) = e^{i(Ψ₀(y) - π/4)} (2π/(p λ₀^{p-1}))^{1/2}`. -/
def c03_sp_P (p y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ)) *
    (Real.sqrt (2 * π / (p * lambda0 p y ^ (p - 1))) : ℂ)

/-- Blueprint: lem:c03_sp_near.  `b_y(s) = λ₀^{-m} a(λ₀ s)`. -/
def c03_sp_b (p m : ℝ) (a : ℝ → ℂ) (y s : ℝ) : ℂ :=
  ((lambda0 p y ^ (-m) : ℝ) : ℂ) * a (lambda0 p y * s)

/-- Blueprint: lem:c03_sp_near.  `I_near(y) = ∫₀^∞ a(ξ) χ_sp(ξ/λ₀) e^{iφ_y(ξ)} dξ`. -/
def c03_sp_Inear (p : ℝ) (χ : ℝ → ℝ) (a : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ ξ in Ioi (0 : ℝ), a ξ * (χ (ξ / lambda0 p y) : ℂ) *
    Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))

/-- Blueprint: lem:c03_sp_far.  `I_far(y) = ∫₀^∞ a(ξ)(1-χ_sp(ξ/λ₀)) e^{iφ_y(ξ)} dξ` (improper). -/
def c03_sp_Ifar (p : ℝ) (χ : ℝ → ℝ) (a : ℝ → ℂ) (y : ℝ) : ℂ :=
  limUnder atTop (fun R : ℝ => ∫ ξ in (0 : ℝ)..R, a ξ * ((1 - χ (ξ / lambda0 p y) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)))



/-- Blueprint: lem:appendix_homogeneous_stationary_phase.
`I(y) = ∫₀^∞ a(ξ) e^{i(yξ - ξ^{p+1}/(p+1))} dξ` (improper). -/
def c03_hsp_I (p : ℝ) (a : ℝ → ℂ) (y : ℝ) : ℂ :=
  limUnder atTop (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
    a ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ)))

/-- Blueprint: lem:appendix_homogeneous_stationary_phase.  The remainder `r`, defined by
`I(y) = P(y)[a(λ₀(y)) + r(y)]`. -/
def c03_hsp_r (p : ℝ) (a : ℝ → ℂ) (y : ℝ) : ℂ := c03_hsp_I p a y / c03_sp_P p y - a (lambda0 p y)


/-! ### Helpers for `appendix_triangle` -/

/-- Mean value theorem on an open interval, in the form `f x - f y = f' z (x - y)` with `z`
between `x` and `y`. -/
theorem c03sp_aux_mvt {α β : ℝ} {f f' : ℝ → ℝ} (hf : ∀ z ∈ Ioo α β, HasDerivAt f (f' z) z)
    {x y : ℝ} (hx : x ∈ Ioo α β) (hy : y ∈ Ioo α β) :
    ∃ z ∈ Ioo α β, |z - y| ≤ |x - y| ∧ f x - f y = f' z * (x - y) := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hc : ContinuousOn f (Icc x y) := fun t ht =>
      (hf t ⟨by linarith [hx.1, ht.1], by linarith [hy.2, ht.2]⟩).continuousAt.continuousWithinAt
    obtain ⟨z, hz, hz'⟩ := exists_hasDerivAt_eq_slope f f' hxy hc
      (fun t ht => hf t ⟨by linarith [hx.1, ht.1], by linarith [hy.2, ht.2]⟩)
    refine ⟨z, ⟨by linarith [hx.1, hz.1], by linarith [hy.2, hz.2]⟩, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hz.2]), abs_of_neg (by linarith)]; linarith [hz.1]
    · rw [hz']; field_simp; ring
  · subst hxy; exact ⟨x, hx, by simp, by simp⟩
  · have hc : ContinuousOn f (Icc y x) := fun t ht =>
      (hf t ⟨by linarith [hy.1, ht.1], by linarith [hx.2, ht.2]⟩).continuousAt.continuousWithinAt
    obtain ⟨z, hz, hz'⟩ := exists_hasDerivAt_eq_slope f f' hxy hc
      (fun t ht => hf t ⟨by linarith [hy.1, ht.1], by linarith [hx.2, ht.2]⟩)
    refine ⟨z, ⟨by linarith [hy.1, hz.1], by linarith [hx.2, hz.2]⟩, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hz.1]), abs_of_pos (by linarith)]; linarith [hz.2]
    · rw [hz']; field_simp

/-- `∫_c^d (t-x₀)^{-2} dt = (c-x₀)⁻¹ - (d-x₀)⁻¹` when `x₀ ∉ [c,d]`. -/
theorem c03sp_aux_integral_inv_sq {c d x₀ : ℝ} (hcd : c ≤ d) (h : x₀ < c ∨ d < x₀) :
    ∫ t in c..d, ((t - x₀) ^ 2)⁻¹ = (c - x₀)⁻¹ - (d - x₀)⁻¹ := by
  have hne : ∀ t ∈ uIcc c d, t - x₀ ≠ 0 := by
    intro t ht; rw [uIcc_of_le hcd] at ht
    rcases h with h | h
    · linarith [ht.1]
    · linarith [ht.2]
  have hd : ∀ t ∈ uIcc c d, HasDerivAt (fun t => -(t - x₀)⁻¹) (((t - x₀) ^ 2)⁻¹) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t - x₀) 1 t := (hasDerivAt_id' t).sub_const x₀
    have := (h1.inv (hne t ht)).neg
    convert this using 1
    rw [neg_div, neg_neg, one_div]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · have hc : ContinuousOn (fun t : ℝ => (t - x₀) ^ 2) (uIcc c d) :=
      ((continuous_id.sub continuous_const).pow 2).continuousOn
    exact (hc.inv₀ (fun t ht => pow_ne_zero 2 (hne t ht))).intervalIntegrable

/-- `‖∫_c^d e^{iωu}/u du‖ ≤ 3/(|ω| c)` for `0 < c ≤ d`, `ω ≠ 0`. -/
theorem c03sp_aux_osc_inv {c d ω : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hω : ω ≠ 0) :
    ‖∫ u in c..d, Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) / (u : ℂ)‖ ≤ 3 / (|ω| * c) := by
  have hpos : ∀ u ∈ uIcc c d, 0 < u := fun u hu => by
    rw [uIcc_of_le hcd] at hu; linarith [hu.1]
  set v : ℝ → ℂ := fun u => Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) / (Complex.I * ω)
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have hIω : (Complex.I * ω) ≠ 0 := mul_ne_zero Complex.I_ne_zero hω'
  have hv : ∀ u ∈ uIcc c d, HasDerivAt v (Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ))) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => Complex.I * ((ω * u : ℝ) : ℂ)) (Complex.I * ω) u := by
      have := ((hasDerivAt_id u).const_mul ω).ofReal_comp.const_mul Complex.I
      simpa using this
    have := (h1.cexp).div_const (Complex.I * ω)
    convert this using 1; field_simp
  have hu : ∀ u ∈ uIcc c d, HasDerivAt (fun u : ℝ => ((u : ℂ))⁻¹) (-((u : ℂ) ^ 2)⁻¹) u := by
    intro u hu'
    have h0 : (u : ℂ) ≠ 0 := by exact_mod_cast (hpos u hu').ne'
    have := (Complex.ofRealCLM.hasDerivAt (x := u)).inv h0
    convert this using 1
    · funext x; simp
    · simp [neg_div, one_div]
  have hcont1 : ContinuousOn (fun u : ℝ => -((u : ℂ) ^ 2)⁻¹) (uIcc c d) := by
    have hc : ContinuousOn (fun u : ℝ => (u : ℂ) ^ 2) (uIcc c d) :=
      (Complex.continuous_ofReal.pow 2).continuousOn
    exact (hc.inv₀ (fun u hu' => pow_ne_zero 2 (by exact_mod_cast (hpos u hu').ne'))).neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hcont1.intervalIntegrable
    ((Continuous.cexp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable _ _)
  have heq : (∫ u in c..d, Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) / (u : ℂ)) =
      ∫ u in c..d, ((u : ℂ))⁻¹ * Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr; intro u _; simp only; rw [div_eq_inv_mul]
  rw [heq, hibp]
  have hvn : ∀ u : ℝ, ‖v u‖ = |ω|⁻¹ := by
    intro u; simp only [v, norm_div, norm_mul, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, one_mul]
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]; simp
  have hωp : 0 < |ω| := abs_pos.2 hω
  have hb1 : ‖((d : ℂ))⁻¹ * v d‖ ≤ 1 / (|ω| * c) := by
    rw [norm_mul, hvn, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [one_div, mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hc hcd) (by positivity)
  have hb2 : ‖((c : ℂ))⁻¹ * v c‖ = 1 / (|ω| * c) := by
    rw [norm_mul, hvn, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    field_simp
  have hb3 : ‖∫ u in c..d, -((u : ℂ) ^ 2)⁻¹ * v u‖ ≤ 1 / (|ω| * c) := by
    have h1 : ‖∫ u in c..d, -((u : ℂ) ^ 2)⁻¹ * v u‖ ≤ ∫ u in c..d, |ω|⁻¹ * ((u - 0) ^ 2)⁻¹ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hcd
      · refine Eventually.of_forall fun u hu' => ?_
        rw [norm_mul, hvn, norm_neg, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          sq_abs, sub_zero, mul_comm]
      · have hc : ContinuousOn (fun u : ℝ => (u - 0) ^ 2) (uIcc c d) :=
          ((continuous_id.sub continuous_const).pow 2).continuousOn
        exact (continuousOn_const.mul (hc.inv₀ (fun u hu' =>
          pow_ne_zero 2 (by linarith [hpos u hu'])))).intervalIntegrable
    rw [intervalIntegral.integral_const_mul, c03sp_aux_integral_inv_sq hcd (Or.inl (by simpa using hc))] at h1
    refine h1.trans ?_
    rw [sub_zero, sub_zero]
    have : (c)⁻¹ - d⁻¹ ≤ c⁻¹ := by linarith [inv_pos.2 (lt_of_lt_of_le hc hcd)]
    calc |ω|⁻¹ * (c⁻¹ - d⁻¹) ≤ |ω|⁻¹ * c⁻¹ := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / (|ω| * c) := by field_simp
  calc _ ≤ ‖((d : ℂ))⁻¹ * v d‖ + ‖((c : ℂ))⁻¹ * v c‖ + ‖∫ u in c..d, -((u : ℂ) ^ 2)⁻¹ * v u‖ :=
        norm_sub_le_of_le (norm_sub_le _ _) le_rfl
    _ ≤ 3 / (|ω| * c) := by rw [hb2]; linarith [hb1, hb3, show 3 / (|ω| * c) = 3 * (1 / (|ω| * c)) by ring]

/-- The integrand `(e^{iωu} - e^{-iωu})/u` used in the sine-integral bound. -/
def c03sp_aux_sinc (ω u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) / (u : ℂ) -
    Complex.exp (Complex.I * ((-ω * u : ℝ) : ℂ)) / (u : ℂ)

theorem c03sp_aux_sinc_cont (ω : ℝ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    IntervalIntegrable (c03sp_aux_sinc ω) volume c d := by
  apply ContinuousOn.intervalIntegrable
  have hne : ∀ u ∈ uIcc c d, (u : ℂ) ≠ 0 := fun u hu => by
    rw [uIcc_of_le hcd] at hu; exact_mod_cast (show u ≠ 0 by linarith [hu.1])
  unfold c03sp_aux_sinc
  apply ContinuousOn.sub
  · exact ((Continuous.cexp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)))).continuousOn).div
      Complex.continuous_ofReal.continuousOn hne
  · exact ((Continuous.cexp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)))).continuousOn).div
      Complex.continuous_ofReal.continuousOn hne

theorem c03sp_aux_sinc_small {ω u : ℝ} (hu : 0 < u) : ‖c03sp_aux_sinc ω u‖ ≤ 2 * |ω| := by
  unfold c03sp_aux_sinc
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, div_le_iff₀ hu]
  have h1 := norm_exp_I_mul_ofReal_sub_one_le (x := ω * u)
  have h2 := norm_exp_I_mul_ofReal_sub_one_le (x := -ω * u)
  have : Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) - Complex.exp (Complex.I * ((-ω * u : ℝ) : ℂ))
      = (Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) - 1) -
        (Complex.exp (Complex.I * ((-ω * u : ℝ) : ℂ)) - 1) := by ring
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  have : |ω * u| = |ω| * u := by rw [abs_mul, abs_of_pos hu]
  have h3 : |-ω * u| = |ω| * u := by rw [abs_mul, abs_neg, abs_of_pos hu]
  rw [Real.norm_eq_abs] at h1; rw [Real.norm_eq_abs] at h2
  linarith

/-- `‖∫_c^d (e^{iωu} - e^{-iωu})/u du‖ ≤ 6/(|ω| c)` for `0 < c ≤ d`, `ω ≠ 0`. -/
theorem c03sp_aux_sinc_large {c d ω : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hω : ω ≠ 0) :
    ‖∫ u in c..d, c03sp_aux_sinc ω u‖ ≤ 6 / (|ω| * c) := by
  have hne : ∀ u ∈ uIcc c d, (u : ℂ) ≠ 0 := fun u hu => by
    rw [uIcc_of_le hcd] at hu; exact_mod_cast (show u ≠ 0 by linarith [hu.1])
  have hi : ∀ w : ℝ, IntervalIntegrable
      (fun u : ℝ => Complex.exp (Complex.I * ((w * u : ℝ) : ℂ)) / (u : ℂ)) volume c d := fun w =>
    (((Continuous.cexp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)))).continuousOn).div
      Complex.continuous_ofReal.continuousOn hne).intervalIntegrable
  unfold c03sp_aux_sinc
  rw [intervalIntegral.integral_sub (hi ω) (hi (-ω))]
  refine (norm_sub_le _ _).trans ?_
  have h1 := c03sp_aux_osc_inv hc hcd hω
  have h2 := c03sp_aux_osc_inv hc hcd (neg_ne_zero.2 hω)
  rw [abs_neg] at h2
  have : 6 / (|ω| * c) = 3 / (|ω| * c) + 3 / (|ω| * c) := by ring
  linarith

/-- The sine integral is bounded: `‖∫_δ^L (e^{iωu} - e^{-iωu})/u du‖ ≤ 10`. -/
theorem c03sp_aux_sinc_bound (ω : ℝ) {δ L : ℝ} (hδ : 0 < δ) (hδL : δ ≤ L) :
    ‖∫ u in δ..L, c03sp_aux_sinc ω u‖ ≤ 10 := by
  rcases eq_or_ne ω 0 with h0 | hω
  · subst h0; simp [c03sp_aux_sinc]
  have hωp : 0 < |ω| := abs_pos.2 hω
  set r := |ω|⁻¹ with hr
  have hrp : 0 < r := inv_pos.2 hωp
  have hsmall : ∀ c d, δ ≤ c → c ≤ d → d ≤ r → ‖∫ u in c..d, c03sp_aux_sinc ω u‖ ≤ 2 := by
    intro c d hc hcd hdr
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := d)
      (C := 2 * |ω|) (f := c03sp_aux_sinc ω) (fun u hu => by
        rw [uIoc_of_le hcd] at hu; exact c03sp_aux_sinc_small (by linarith [hu.1]))
    refine this.trans ?_
    rw [abs_of_nonneg (show (0:ℝ) ≤ d - c by linarith)]
    have : |ω| * (d - c) ≤ |ω| * r := mul_le_mul_of_nonneg_left (by linarith) hωp.le
    rw [hr, mul_inv_cancel₀ hωp.ne'] at this
    linarith
  have hlarge : ∀ c d, r ≤ c → c ≤ d → ‖∫ u in c..d, c03sp_aux_sinc ω u‖ ≤ 6 := by
    intro c d hc hcd
    refine (c03sp_aux_sinc_large (by linarith) hcd hω).trans ?_
    rw [div_le_iff₀ (mul_pos hωp (by linarith))]
    have : |ω| * r ≤ |ω| * c := mul_le_mul_of_nonneg_left hc hωp.le
    rw [hr, mul_inv_cancel₀ hωp.ne'] at this
    linarith
  rcases le_total L r with hLr | hrL
  · linarith [hsmall δ L le_rfl hδL hLr]
  rcases le_total r δ with hrδ | hδr
  · linarith [hlarge δ L hrδ hδL]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := r)
    (c03sp_aux_sinc_cont ω hδ hδr) (c03sp_aux_sinc_cont ω (by linarith) hrL)]
  refine (norm_add_le _ _).trans ?_
  linarith [hsmall δ r le_rfl hδr le_rfl, hlarge r L le_rfl hrL]

/-- A function with `tsupport ⊆ (α,β)` vanishes on `(-∞,α+η) ∪ (β-η,∞)` for some `η > 0`. -/
theorem c03sp_aux_supp_margin {α β : ℝ} {a : ℝ → ℂ} (h : tsupport a ⊆ Ioo α β) :
    ∃ η > 0, ∀ t, (t < α + η ∨ β - η < t) → a t = 0 := by
  have hK : IsCompact (tsupport a) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport a)
      (Bornology.IsBounded.subset (Metric.isBounded_Ioo α β) h)
  obtain ⟨η, hη, hsub⟩ := hK.exists_thickening_subset_open isOpen_Ioo h
  refine ⟨η, hη, fun t ht => ?_⟩
  by_contra hne
  have htK : t ∈ tsupport a := subset_tsupport a hne
  have htI := h htK
  rcases ht with ht | ht
  · have : α ∈ Metric.thickening η (tsupport a) :=
      Metric.mem_thickening_iff.2 ⟨t, htK, by rw [Real.dist_eq, abs_of_neg (by linarith [htI.1])]; linarith⟩
    exact lt_irrefl _ (hsub this).1
  · have : β ∈ Metric.thickening η (tsupport a) :=
      Metric.mem_thickening_iff.2 ⟨t, htK, by rw [Real.dist_eq, abs_of_pos (by linarith [htI.2])]; linarith⟩
    exact lt_irrefl _ (hsub this).2

/-- The tail integral `E(t) = ∫_t^∞ e^{iΨ}` has derivative `-e^{iΨ(t)}`. -/
theorem c03sp_aux_tail_deriv {α β : ℝ} {Ψ : ℝ → ℝ} {E : ℝ → ℂ} (hΨ : ContinuousOn Ψ (Ici α))
    (hE : ∀ t ∈ Ioo α β, Tendsto (fun R : ℝ => ∫ s in t..R, Complex.exp (Complex.I * (Ψ s : ℂ)))
      atTop (𝓝 (E t))) :
    ∀ t ∈ Ioo α β, HasDerivAt E (-Complex.exp (Complex.I * (Ψ t : ℂ))) t := by
  set f : ℝ → ℂ := fun s => Complex.exp (Complex.I * (Ψ s : ℂ))
  have hfc : ContinuousOn f (Ici α) :=
    (continuous_const.mul Complex.continuous_ofReal).cexp.comp_continuousOn hΨ |>.congr
      (fun s _ => rfl)
  have hii : ∀ u v, α ≤ u → α ≤ v → IntervalIntegrable f volume u v := fun u v hu hv =>
    (hfc.mono (by
      intro x hx; rw [mem_uIcc] at hx; simp only [mem_Ici]
      rcases hx with hx | hx <;> linarith [hx.1])).intervalIntegrable
  intro t ht
  have key : ∀ s ∈ Ioo α β, E s = E t - ∫ x in t..s, f x := by
    intro s hs
    have h1 : Tendsto (fun R : ℝ => (∫ x in s..t, f x) + ∫ x in t..R, f x) atTop
        (𝓝 ((∫ x in s..t, f x) + E t)) := (hE t ht).const_add _
    have h2 : (fun R : ℝ => ∫ x in s..R, f x) =ᶠ[atTop]
        (fun R : ℝ => (∫ x in s..t, f x) + ∫ x in t..R, f x) := by
      filter_upwards [eventually_ge_atTop α] with R hR
      rw [intervalIntegral.integral_add_adjacent_intervals (hii s t hs.1.le ht.1.le)
        (hii t R ht.1.le hR)]
    have := tendsto_nhds_unique (hE s hs) (h1.congr' h2.symm)
    rw [this, intervalIntegral.integral_symm]; ring
  have hEq : (fun s => E t - ∫ x in t..s, f x) =ᶠ[𝓝 t] E := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using (key s hs).symm
  have hd : HasDerivAt (fun s => ∫ x in t..s, f x) (f t) t := by
    apply intervalIntegral.integral_hasDerivAt_right (hii t t ht.1.le ht.1.le)
    · exact hfc.mono Ioi_subset_Ici_self |>.stronglyMeasurableAtFilter isOpen_Ioi t ht.1
    · exact hfc.continuousAt (Ici_mem_nhds ht.1)
  exact (hd.const_sub (E t)).congr_of_eventuallyEq hEq.symm

/-- Integration by parts for `∫ a e^{iΦ} E` with `e^{iΦ} = (iΦ')⁻¹ ∂ e^{iΦ}` and `E' = -e^{iΨ}`. -/
theorem c03sp_aux_tri_ibp {c d : ℝ} (hcd : c ≤ d) {a a1 E : ℝ → ℂ} {Φ g g2 Ψ : ℝ → ℝ}
    (ha : ∀ t ∈ Icc c d, HasDerivAt a (a1 t) t) (hΦ : ∀ t ∈ Icc c d, HasDerivAt Φ (g t) t)
    (hg : ∀ t ∈ Icc c d, HasDerivAt g (g2 t) t)
    (hE : ∀ t ∈ Icc c d, HasDerivAt E (-Complex.exp (Complex.I * (Ψ t : ℂ))) t)
    (hg0 : ∀ t ∈ Icc c d, g t ≠ 0) (ha1c : ContinuousOn a1 (Icc c d))
    (hg2c : ContinuousOn g2 (Icc c d)) (hΨc : ContinuousOn Ψ (Icc c d)) :
    ∫ t in c..d, a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t =
      a d / (Complex.I * g d) * E d * Complex.exp (Complex.I * (Φ d : ℂ)) -
        a c / (Complex.I * g c) * E c * Complex.exp (Complex.I * (Φ c : ℂ)) -
        ∫ t in c..d, ((a1 t * g t - a t * g2 t) / (Complex.I * (g t : ℂ) ^ 2) * E t -
          a t / (Complex.I * g t) * Complex.exp (Complex.I * (Ψ t : ℂ))) *
            Complex.exp (Complex.I * (Φ t : ℂ)) := by
  have hu : ∀ t ∈ uIcc c d, HasDerivAt (fun t => a t / (Complex.I * g t) * E t)
      ((a1 t * g t - a t * g2 t) / (Complex.I * (g t : ℂ) ^ 2) * E t +
        a t / (Complex.I * g t) * (-Complex.exp (Complex.I * (Ψ t : ℂ)))) t := by
    intro t ht; rw [uIcc_of_le hcd] at ht
    have hgt : (Complex.I * (g t : ℂ)) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hg0 t ht)
    have h1 : HasDerivAt (fun t => Complex.I * (g t : ℂ)) (Complex.I * (g2 t : ℂ)) t :=
      (hg t ht).ofReal_comp.const_mul _
    have := ((ha t ht).div h1 hgt).mul (hE t ht)
    convert this using 2
    have : (g t : ℂ) ≠ 0 := by exact_mod_cast hg0 t ht
    field_simp
  have hv : ∀ t ∈ uIcc c d, HasDerivAt (fun t => Complex.exp (Complex.I * (Φ t : ℂ)))
      (Complex.exp (Complex.I * (Φ t : ℂ)) * (Complex.I * g t)) t := by
    intro t ht; rw [uIcc_of_le hcd] at ht
    exact ((hΦ t ht).ofReal_comp.const_mul Complex.I).cexp
  have hcont : ∀ {F : ℝ → ℂ} {F' : ℝ → ℂ}, (∀ t ∈ Icc c d, HasDerivAt F (F' t) t) →
      ContinuousOn F (Icc c d) := fun h t ht => (h t ht).continuousAt.continuousWithinAt
  have hcontR : ∀ {F : ℝ → ℝ} {F' : ℝ → ℝ}, (∀ t ∈ Icc c d, HasDerivAt F (F' t) t) →
      ContinuousOn F (Icc c d) := fun h t ht => (h t ht).continuousAt.continuousWithinAt
  have hgc := hcontR hg
  have hΦc := hcontR hΦ
  have hac := hcont ha
  have hEc := hcont hE
  have hgC : ContinuousOn (fun t => (g t : ℂ)) (Icc c d) :=
    Complex.continuous_ofReal.comp_continuousOn hgc
  have hg2C : ContinuousOn (fun t => (g2 t : ℂ)) (Icc c d) :=
    Complex.continuous_ofReal.comp_continuousOn hg2c
  have hexpΦ : ContinuousOn (fun t => Complex.exp (Complex.I * (Φ t : ℂ))) (Icc c d) :=
    ((continuous_const.mul Complex.continuous_ofReal).cexp).comp_continuousOn hΦc
  have hexpΨ : ContinuousOn (fun t => Complex.exp (Complex.I * (Ψ t : ℂ))) (Icc c d) :=
    ((continuous_const.mul Complex.continuous_ofReal).cexp).comp_continuousOn hΨc
  have hIg : ∀ t ∈ Icc c d, Complex.I * (g t : ℂ) ≠ 0 := fun t ht =>
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hg0 t ht)
  have hIg2 : ∀ t ∈ Icc c d, Complex.I * (g t : ℂ) ^ 2 ≠ 0 := fun t ht =>
    mul_ne_zero Complex.I_ne_zero (pow_ne_zero 2 (by exact_mod_cast hg0 t ht))
  have hQc : ContinuousOn (fun t => a t / (Complex.I * g t)) (Icc c d) :=
    hac.div (continuousOn_const.mul hgC) hIg
  have hQ'c : ContinuousOn (fun t => (a1 t * g t - a t * g2 t) / (Complex.I * (g t : ℂ) ^ 2))
      (Icc c d) :=
    ((ha1c.mul hgC).sub (hac.mul hg2C)).div (continuousOn_const.mul (hgC.pow 2)) hIg2
  have i1 : IntervalIntegrable (fun t => (a1 t * g t - a t * g2 t) / (Complex.I * (g t : ℂ) ^ 2) * E t +
        a t / (Complex.I * g t) * (-Complex.exp (Complex.I * (Ψ t : ℂ)))) volume c d := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hcd]
    exact ((hQ'c.mul hEc).add (hQc.mul hexpΨ.neg))
  have i2 : IntervalIntegrable (fun t => Complex.exp (Complex.I * (Φ t : ℂ)) * (Complex.I * g t))
      volume c d := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hcd]
    exact (hexpΦ.mul (continuousOn_const.mul hgC))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv i1 i2
  have e1 : ∫ t in c..d, a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t =
      ∫ t in c..d, a t / (Complex.I * g t) * E t *
        (Complex.exp (Complex.I * (Φ t : ℂ)) * (Complex.I * g t)) := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [uIcc_of_le hcd] at ht
    simp only
    have : (g t : ℂ) ≠ 0 := by exact_mod_cast hg0 t ht
    field_simp
  rw [e1, hibp]
  refine congrArg (fun z => _ - z) (intervalIntegral.integral_congr fun t _ => ?_)
  simp only [mul_neg, ← sub_eq_add_neg]

/-- Pointwise bound for `(a/(iΦ'))'` in the proof of `appendix_triangle`. -/
theorem c03sp_aux_tri_alg1 {a1 a : ℂ} {G G2 u κ A c₁ c₂ c₄ : ℝ} (hu : 0 < u) (hκ : 0 < κ)
    (hc₁ : 0 < c₁) (hG : c₁ * κ * u ≤ |G|) (ha1 : ‖a1‖ ≤ c₄ * A / u) (ha : ‖a‖ ≤ c₄ * A)
    (hG2 : |G2| ≤ c₂ * κ) :
    ‖(a1 * G - a * G2) / (Complex.I * (G : ℂ) ^ 2)‖ ≤
      (c₄ / c₁ + c₄ * c₂ / c₁ ^ 2) * A / κ * (u ^ 2)⁻¹ := by
  have hGp : 0 < |G| := lt_of_lt_of_le (by positivity) hG
  have hA : 0 ≤ c₄ * A := le_trans (norm_nonneg _) ha
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hN : ‖a1 * G - a * G2‖ ≤ ‖a1‖ * |G| + ‖a‖ * |G2| := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  have e : (‖a1‖ * |G| + ‖a‖ * |G2|) / |G| ^ 2 = ‖a1‖ / |G| + ‖a‖ * |G2| / |G| ^ 2 := by
    field_simp
  calc _ ≤ (‖a1‖ * |G| + ‖a‖ * |G2|) / |G| ^ 2 := by gcongr
    _ = ‖a1‖ / |G| + ‖a‖ * |G2| / |G| ^ 2 := e
    _ ≤ (c₄ * A / u) / (c₁ * κ * u) + (c₄ * A) * (c₂ * κ) / (c₁ * κ * u) ^ 2 := by
        have h1 : 0 ≤ c₄ * A / u := le_trans (norm_nonneg _) ha1
        have h2 : 0 ≤ c₂ * κ := le_trans (abs_nonneg _) hG2
        gcongr
    _ = _ := by field_simp

/-- Pointwise bound for `a/(iΦ') - h(0)/(i t)` in the proof of `appendix_triangle`. -/
theorem c03sp_aux_tri_alg2 {a_t a0 : ℂ} {gt g20 u L κ A c₁ c₂ c₃ c₄ : ℝ} (hu : u ≠ 0)
    (hκ : 0 < κ) (hL : 0 < L) (hc₁ : 0 < c₁) (hgt : c₁ * κ * |u| ≤ |gt|)
    (hg20 : c₁ * κ ≤ |g20|) (hg20' : |g20| ≤ c₂ * κ) (ha0 : ‖a0‖ ≤ c₄ * A)
    (hdiff : ‖a_t - a0‖ ≤ c₄ * A / L * |u|) (htay : |gt - g20 * u| ≤ c₃ * κ / L * u ^ 2) :
    ‖a_t / (Complex.I * gt) - a0 / g20 / (Complex.I * u)‖ ≤
      c₄ * (c₂ + c₃) / c₁ ^ 2 * A / (κ * L) := by
  have hup : 0 < |u| := abs_pos.2 hu
  have hgtp : 0 < |gt| := lt_of_lt_of_le (by positivity) hgt
  have hg20p : 0 < |g20| := lt_of_lt_of_le (by positivity) hg20
  have hgt0 : (gt : ℂ) ≠ 0 := by exact_mod_cast abs_pos.1 hgtp
  have hg200 : (g20 : ℂ) ≠ 0 := by exact_mod_cast abs_pos.1 hg20p
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have hA : 0 ≤ c₄ * A := le_trans (norm_nonneg _) ha0
  have key : a_t / (Complex.I * gt) - a0 / g20 / (Complex.I * u) =
      ((a_t - a0) * g20 * u - a0 * ((gt - g20 * u : ℝ) : ℂ)) / (Complex.I * gt * g20 * u) := by
    push_cast; field_simp; ring
  rw [key, norm_div]
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hN : ‖(a_t - a0) * g20 * u - a0 * ((gt - g20 * u : ℝ) : ℂ)‖ ≤
      c₄ * A / L * |u| * (c₂ * κ) * |u| + c₄ * A * (c₃ * κ / L * u ^ 2) := by
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
  calc _ ≤ (c₄ * A / L * |u| * (c₂ * κ) * |u| + c₄ * A * (c₃ * κ / L * u ^ 2)) /
        (c₁ * κ * |u| * (c₁ * κ) * |u|) := by
        apply div_le_div₀ (le_trans (norm_nonneg _) hN) hN (by positivity)
        gcongr
    _ = _ := by
        rw [← sq_abs u]; field_simp

/-- The model term `h₀ e^{i(ωt+ω₀)}/(i(t-x₀))` of the proof of `appendix_triangle`. -/
def c03sp_aux_triH (x₀ ω ω₀ : ℝ) (h0 : ℂ) (t : ℝ) : ℂ :=
  h0 / (Complex.I * ((t - x₀ : ℝ) : ℂ)) * Complex.exp (Complex.I * ((ω * t + ω₀ : ℝ) : ℂ))

theorem c03sp_aux_triH_cont (x₀ ω ω₀ : ℝ) (h0 : ℂ) {t : ℝ} (ht : t ≠ x₀) :
    ContinuousAt (c03sp_aux_triH x₀ ω ω₀ h0) t := by
  have hc1 : Continuous (fun t : ℝ => Complex.I * ((t - x₀ : ℝ) : ℂ)) := by fun_prop
  have hc2 : Continuous (fun t : ℝ => Complex.exp (Complex.I * ((ω * t + ω₀ : ℝ) : ℂ))) := by
    fun_prop
  have hne : Complex.I * ((t - x₀ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast sub_ne_zero.2 ht)
  exact (continuousAt_const.div hc1.continuousAt hne).mul hc2.continuousAt

theorem c03sp_aux_triH_ii (x₀ ω ω₀ : ℝ) (h0 : ℂ) {c d : ℝ} (hcd : c ≤ d)
    (h : x₀ < c ∨ d < x₀) : IntervalIntegrable (c03sp_aux_triH x₀ ω ω₀ h0) volume c d := by
  apply ContinuousOn.intervalIntegrable
  intro t ht; rw [uIcc_of_le hcd] at ht
  apply (c03sp_aux_triH_cont x₀ ω ω₀ h0 _).continuousWithinAt
  rcases h with h | h
  · exact ne_of_gt (by linarith [ht.1])
  · exact ne_of_lt (by linarith [ht.2])

theorem c03sp_aux_tri_Hsum (x₀ ω ω₀ : ℝ) (h0 : ℂ) {δ L : ℝ} (hδ : 0 < δ) (hδL : δ ≤ L) :
    (∫ t in (x₀ + δ)..(x₀ + L), c03sp_aux_triH x₀ ω ω₀ h0 t) +
      ∫ t in (x₀ - L)..(x₀ - δ), c03sp_aux_triH x₀ ω ω₀ h0 t =
    h0 / Complex.I * Complex.exp (Complex.I * ((ω * x₀ + ω₀ : ℝ) : ℂ)) *
      ∫ u in δ..L, c03sp_aux_sinc ω u := by
  have e1 : (∫ t in (x₀ + δ)..(x₀ + L), (c03sp_aux_triH x₀ ω ω₀ h0) t) = ∫ u in δ..L, (c03sp_aux_triH x₀ ω ω₀ h0) (u + x₀) := by
    rw [intervalIntegral.integral_comp_add_right (c03sp_aux_triH x₀ ω ω₀ h0) x₀, add_comm δ, add_comm L]
  have e2 : (∫ t in (x₀ - L)..(x₀ - δ), (c03sp_aux_triH x₀ ω ω₀ h0) t) = ∫ u in δ..L, (c03sp_aux_triH x₀ ω ω₀ h0) (-u + x₀) := by
    rw [intervalIntegral.integral_comp_neg (fun u => (c03sp_aux_triH x₀ ω ω₀ h0) (u + x₀)),
      intervalIntegral.integral_comp_add_right (c03sp_aux_triH x₀ ω ω₀ h0) x₀]
    congr 1 <;> ring
  have i1 : IntervalIntegrable (fun u => (c03sp_aux_triH x₀ ω ω₀ h0) (u + x₀)) volume δ L := by
    apply ContinuousOn.intervalIntegrable
    intro u hu; rw [uIcc_of_le hδL] at hu
    apply ContinuousAt.continuousWithinAt
    exact (c03sp_aux_triH_cont x₀ ω ω₀ h0 (t := u + x₀) (by linarith [hu.1])).comp
      (f := fun u : ℝ => u + x₀) (x := u) (continuousAt_id.add continuousAt_const)
  have i2 : IntervalIntegrable (fun u => (c03sp_aux_triH x₀ ω ω₀ h0) (-u + x₀)) volume δ L := by
    apply ContinuousOn.intervalIntegrable
    intro u hu; rw [uIcc_of_le hδL] at hu
    apply ContinuousAt.continuousWithinAt
    exact (c03sp_aux_triH_cont x₀ ω ω₀ h0 (t := -u + x₀) (by linarith [hu.1])).comp
      (f := fun u : ℝ => -u + x₀) (x := u) (continuousAt_id.neg.add continuousAt_const)
  rw [e1, e2, ← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu; rw [uIcc_of_le hδL] at hu
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by linarith [hu.1])
  simp only [c03sp_aux_triH, c03sp_aux_sinc]
  have ex1 : Complex.exp (Complex.I * ((ω * (u + x₀) + ω₀ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((ω * u : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((ω * x₀ + ω₀ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have ex2 : Complex.exp (Complex.I * ((ω * (-u + x₀) + ω₀ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((-ω * u : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((ω * x₀ + ω₀ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [ex1, ex2]
  have s1 : ((u + x₀ - x₀ : ℝ) : ℂ) = u := by push_cast; ring
  have s2 : ((-u + x₀ - x₀ : ℝ) : ℂ) = -u := by push_cast; ring
  rw [s1, s2]
  field_simp
  ring

/-- Triangle inequality for eight terms. -/
theorem c03sp_aux_norm8 (z1 z2 z3 z4 z5 z6 z7 z8 : ℂ) :
    ‖z1 + z2 - z3 - z4 - z5 + z6 + z7 + z8‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖ + ‖z7‖ + ‖z8‖ := by
  have a1 := norm_add_le (z1 + z2 - z3 - z4 - z5 + z6 + z7) z8
  have a2 := norm_add_le (z1 + z2 - z3 - z4 - z5 + z6) z7
  have a3 := norm_add_le (z1 + z2 - z3 - z4 - z5) z6
  have a4 := norm_sub_le (z1 + z2 - z3 - z4) z5
  have a5 := norm_sub_le (z1 + z2 - z3) z4
  have a6 := norm_sub_le (z1 + z2) z3
  have a7 := norm_add_le z1 z2
  linarith

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:appendix_triangle.  `|∫_I a e^{iΦ} E| ≤ C A (M κ^{-1/2} + κ⁻¹)` with
`C = C(c₁,…,c₄)`, where `E(t) = ∫_t^∞ e^{iΨ}` (improper) and `Φ + Ψ` is affine on `I`. -/
theorem c03sp_appendix_triangle (c₁ c₂ c₃ c₄ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hc₄ : 0 < c₄) :
    ∃ C, 0 < C ∧ ∀ x₀ L κ A M ω ω₀ : ℝ, 0 < L → 0 < κ → 0 ≤ A → 0 ≤ M →
      ∀ (Φ Ψ : ℝ → ℝ) (a E : ℝ → ℂ),
      ContDiffOn ℝ 3 Φ (Icc (x₀ - L) (x₀ + L)) →
      derivWithin Φ (Icc (x₀ - L) (x₀ + L)) x₀ = 0 →
      (∀ t ∈ Ioo (x₀ - L) (x₀ + L),
        c₁ * κ ≤ |iteratedDerivWithin 2 Φ (Icc (x₀ - L) (x₀ + L)) t| ∧
        |iteratedDerivWithin 2 Φ (Icc (x₀ - L) (x₀ + L)) t| ≤ c₂ * κ ∧
        |iteratedDerivWithin 3 Φ (Icc (x₀ - L) (x₀ + L)) t| ≤ c₃ * κ / L) →
      ContDiff ℝ 2 a → tsupport a ⊆ Ioo (x₀ - L) (x₀ + L) →
      (∀ j ≤ 2, ∀ t ∈ Ioo (x₀ - L) (x₀ + L),
        ‖iteratedDeriv j a t‖ ≤ c₄ * A * L ^ (-(j : ℝ))) →
      ContinuousOn Ψ (Ici (x₀ - L)) →
      (∀ t ∈ Ioo (x₀ - L) (x₀ + L),
        Tendsto (fun R : ℝ => ∫ s in t..R, Complex.exp (Complex.I * (Ψ s : ℂ))) atTop
          (𝓝 (E t)) ∧ ‖E t‖ ≤ M) →
      (∀ t ∈ Ioo (x₀ - L) (x₀ + L), Φ t + Ψ t = ω * t + ω₀) →
      ‖∫ t in Ioo (x₀ - L) (x₀ + L), a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t‖ ≤
        C * A * (M * κ ^ (-(1 / 2 : ℝ)) + κ⁻¹) := by
  set K₁ : ℝ := c₄ / c₁ + c₄ * c₂ / c₁ ^ 2 with hK₁
  set K₂ : ℝ := c₄ * (c₂ + c₃) / c₁ ^ 2 + c₄ / c₁ with hK₂
  have hK₁p : 0 < K₁ := by positivity
  have hK₂p : 0 < K₂ := by positivity
  have hc41 : 0 < c₄ / c₁ := by positivity
  refine ⟨2 * c₄ + 2 * (c₄ / c₁) + 2 * K₁ + 2 * K₂ + 10 * (c₄ / c₁), by positivity, ?_⟩
  intro x₀ L κ A M ω ω₀ hL hκ hA hM Φ Ψ a E hΦ hΦ0 hΦb ha has hab hΨ hE hlin
  set C : ℝ := 2 * c₄ + 2 * (c₄ / c₁) + 2 * K₁ + 2 * K₂ + 10 * (c₄ / c₁) with hC
  have hαβ : x₀ - L < x₀ + L := by linarith
  set I := Ioo (x₀ - L) (x₀ + L) with hI
  have hIo : IsOpen I := isOpen_Ioo
  have hIc : Convex ℝ I := convex_Ioo _ _
  have hx₀I : x₀ ∈ I := ⟨by linarith, by linarith⟩
  have hΦo : ContDiffOn ℝ 3 Φ I := hΦ.mono Ioo_subset_Icc_self
  have hgo : ContDiffOn ℝ 2 (deriv Φ) I := hΦo.deriv_of_isOpen hIo (by norm_num)
  have hg2o : ContDiffOn ℝ 1 (deriv (deriv Φ)) I := hgo.deriv_of_isOpen hIo (by norm_num)
  have dΦ : ∀ t ∈ I, HasDerivAt Φ (deriv Φ t) t := fun t ht =>
    (((hΦo.differentiableOn (by norm_num)) t ht).differentiableAt (hIo.mem_nhds ht)).hasDerivAt
  have dg : ∀ t ∈ I, HasDerivAt (deriv Φ) (deriv (deriv Φ) t) t := fun t ht =>
    (((hgo.differentiableOn (by norm_num)) t ht).differentiableAt (hIo.mem_nhds ht)).hasDerivAt
  have dg2 : ∀ t ∈ I, HasDerivAt (deriv (deriv Φ)) (deriv (deriv (deriv Φ)) t) t := fun t ht =>
    (((hg2o.differentiableOn (by norm_num)) t ht).differentiableAt (hIo.mem_nhds ht)).hasDerivAt
  have hit : ∀ t ∈ I, ∀ k : ℕ, k ≤ 3 →
      iteratedDerivWithin k Φ (Icc (x₀ - L) (x₀ + L)) t = iteratedDeriv k Φ t := by
    intro t ht k hk
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hαβ)
      ((hΦ.contDiffAt (Icc_mem_nhds ht.1 ht.2)).of_le (by exact_mod_cast hk))
      (Ioo_subset_Icc_self ht)
  have hi2 : iteratedDeriv 2 Φ = deriv (deriv Φ) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hi3 : iteratedDeriv 3 Φ = deriv (deriv (deriv Φ)) := by
    rw [iteratedDeriv_succ, hi2]
  have hb : ∀ t ∈ I, c₁ * κ ≤ |deriv (deriv Φ) t| ∧ |deriv (deriv Φ) t| ≤ c₂ * κ ∧
      |deriv (deriv (deriv Φ)) t| ≤ c₃ * κ / L := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hΦb t ht
    rw [hit t ht 2 (by norm_num), hi2] at h1 h2
    rw [hit t ht 3 (by norm_num), hi3] at h3
    exact ⟨h1, h2, h3⟩
  have hg0 : deriv Φ x₀ = 0 := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx₀I.1 hx₀I.2)]; exact hΦ0
  have hda : ∀ t, HasDerivAt a (deriv a t) t := fun t =>
    ((ha.differentiable (by norm_num)) t).hasDerivAt
  have hda1 : Continuous (deriv a) := ha.continuous_deriv (by norm_num)
  have ha0 : ∀ t ∈ I, ‖a t‖ ≤ c₄ * A := by
    intro t ht; have := hab 0 (by norm_num) t ht; simpa using this
  have ha1 : ∀ t ∈ I, ‖deriv a t‖ ≤ c₄ * A / L := by
    intro t ht; have := hab 1 (by norm_num) t ht
    simpa [iteratedDeriv_one, Real.rpow_neg_one, div_eq_mul_inv] using this
  have hzero : ∀ t, t ∉ I → a t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun h => ht (has h))
  have hA0 : 0 ≤ c₄ * A := le_trans (norm_nonneg _) (ha0 x₀ hx₀I)
  have hEd := c03sp_aux_tail_deriv hΨ (fun t ht => (hE t ht).1)
  have hEM : ∀ t ∈ I, ‖E t‖ ≤ M := fun t ht => (hE t ht).2
  have hglow : ∀ t ∈ I, c₁ * κ * |t - x₀| ≤ |deriv Φ t| := by
    intro t ht
    obtain ⟨z, hz, -, hzeq⟩ := c03sp_aux_mvt dg ht hx₀I
    rw [hg0, sub_zero] at hzeq
    rw [hzeq, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb z hz).1 (abs_nonneg _)
  have htay : ∀ t ∈ I, |deriv Φ t - deriv (deriv Φ) x₀ * (t - x₀)| ≤
      c₃ * κ / L * (t - x₀) ^ 2 := by
    intro t ht
    have hk : ∀ s ∈ I, HasDerivAt (fun s => deriv Φ s - deriv (deriv Φ) x₀ * (s - x₀))
        (deriv (deriv Φ) s - deriv (deriv Φ) x₀) s := by
      intro s hs
      have := (dg s hs).sub (((hasDerivAt_id' s).sub_const x₀).const_mul (deriv (deriv Φ) x₀))
      convert this using 1; simp
    obtain ⟨z, hz, hzt, hzeq⟩ := c03sp_aux_mvt hk ht hx₀I
    simp only [hg0, sub_self, mul_zero, sub_zero] at hzeq
    obtain ⟨w, hw, -, hweq⟩ := c03sp_aux_mvt dg2 hz hx₀I
    rw [hzeq, hweq, abs_mul, abs_mul]
    have h3 := (hb w hw).2.2
    have hc3 : 0 ≤ c₃ * κ / L := by positivity
    calc |deriv (deriv (deriv Φ)) w| * |z - x₀| * |t - x₀|
        ≤ c₃ * κ / L * |t - x₀| * |t - x₀| := by gcongr
      _ = c₃ * κ / L * (t - x₀) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  have hadiff : ∀ t ∈ I, ‖a t - a x₀‖ ≤ c₄ * A / L * |t - x₀| := by
    intro t ht
    have := hIc.norm_image_sub_le_of_norm_deriv_le (fun s _ => (hda s).differentiableAt)
      ha1 hx₀I ht
    simpa [Real.norm_eq_abs] using this
  have hn1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  set δ : ℝ := κ ^ (-(1 / 2 : ℝ)) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hκ _
  have hδδ : δ * δ = κ⁻¹ := by
    rw [hδdef, ← Real.rpow_add hκ]; norm_num; exact Real.rpow_neg_one κ
  have hκδ : (κ * δ)⁻¹ = δ := by
    have h1 : κ * (δ * δ) = 1 := by rw [hδδ, mul_inv_cancel₀ hκ.ne']
    exact inv_eq_of_mul_eq_one_right (by rw [mul_assoc]; exact h1)
  set X : ℝ := A * M * δ with hX
  set Y : ℝ := A * κ⁻¹ with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hgoal : C * A * (M * δ + κ⁻¹) = C * X + C * Y := by rw [hX, hY]; ring
  rw [hgoal]
  have hFb : ∀ t, ‖a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t‖ ≤ c₄ * A * M := by
    intro t; by_cases ht : t ∈ I
    · rw [norm_mul, norm_mul, hn1, mul_one]
      exact mul_le_mul (ha0 t ht) (hEM t ht) (norm_nonneg _) hA0
    · rw [hzero t ht]; simp only [zero_mul, norm_zero]; exact mul_nonneg hA0 hM
  have hconv : ∫ t in I, a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t =
      ∫ t in (x₀ - L)..(x₀ + L), a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t := by
    rw [intervalIntegral.integral_of_le hαβ.le, integral_Ioc_eq_integral_Ioo]
  rw [hconv]
  by_cases hLδ : L ≤ δ
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀ - L) (b := x₀ + L)
      (fun t _ => hFb t)
    rw [abs_of_pos (by linarith)] at this
    have h1 : c₄ * A * M * (x₀ + L - (x₀ - L)) ≤ 2 * c₄ * X := by
      rw [hX]
      have : x₀ + L - (x₀ - L) ≤ 2 * δ := by linarith
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hA0 hM)
      linarith
    have h2 : 2 * c₄ * X ≤ C * X := mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hX0
    have h3 : 0 ≤ C * Y := mul_nonneg (by positivity) hY0
    linarith
  rw [not_le] at hLδ
  obtain ⟨η, hη, hη0⟩ := c03sp_aux_supp_margin has
  set η' : ℝ := min η ((L - δ) / 2) with hη'def
  have hη' : 0 < η' := lt_min hη (by linarith)
  have hη'1 : η' ≤ η := min_le_left _ _
  have hη'2 : η' ≤ (L - δ) / 2 := min_le_right _ _
  set bm : ℝ := x₀ - L + η' / 2 with hbm
  set bp : ℝ := x₀ + L - η' / 2 with hbp
  have hz' : ∀ t, (t ≤ bm ∨ bp ≤ t) → a t = 0 := fun t ht => hη0 t (by
    rcases ht with h | h
    · left; linarith
    · right; linarith)
  -- continuity of the integrand
  set F : ℝ → ℂ := fun t => a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t with hFdef
  have hexpc : ∀ t ∈ I, ContinuousAt (fun s => Complex.exp (Complex.I * (Φ s : ℂ))) t :=
    fun t ht => ((continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (dΦ t ht).continuousAt)).cexp)
  have hFc : Continuous F := by
    rw [continuous_iff_continuousAt]; intro t
    by_cases ht : t ∈ I
    · exact ((hda t).continuousAt.mul (hexpc t ht)).mul (hEd t ht).continuousAt
    · have hev : F =ᶠ[𝓝 t] fun _ => 0 := by
        rcases not_and_or.1 ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < x₀ - L + η by linarith [not_lt.1 h])] with s hs
          simp [hFdef, hη0 s (Or.inl hs)]
        · filter_upwards [Ioi_mem_nhds (show x₀ + L - η < t by linarith [not_lt.1 h])] with s hs
          simp [hFdef, hη0 s (Or.inr hs)]
      exact continuousAt_const.congr hev.symm
  have hii : ∀ u v, IntervalIntegrable F volume u v := fun u v => hFc.intervalIntegrable u v
  have hsplit : ∫ t in (x₀ - L)..(x₀ + L), F t = (∫ t in (x₀ - L)..bm, F t) +
      (∫ t in bm..(x₀ - δ), F t) + (∫ t in (x₀ - δ)..(x₀ + δ), F t) +
      (∫ t in (x₀ + δ)..bp, F t) + ∫ t in bp..(x₀ + L), F t := by
    simp only [intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)]
  have h0L : ∫ t in (x₀ - L)..bm, F t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
    · simp
    intro t ht; rw [uIcc_of_le (by linarith)] at ht
    simp [hFdef, hz' t (Or.inl ht.2)]
  have h0R : ∫ t in bp..(x₀ + L), F t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
    · simp
    intro t ht; rw [uIcc_of_le (by linarith)] at ht
    simp [hFdef, hz' t (Or.inr ht.1)]
  have hmid : ‖∫ t in (x₀ - δ)..(x₀ + δ), F t‖ ≤ 2 * c₄ * X := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀ - δ) (b := x₀ + δ)
      (fun t _ => hFb t)
    rw [abs_of_pos (by linarith)] at this
    refine this.trans (le_of_eq ?_); rw [hX]; ring
  -- the amplitude `Q = a/(iΦ')` and its derivative
  set Q : ℝ → ℂ := fun t => a t / (Complex.I * ((deriv Φ t : ℝ) : ℂ)) with hQdef
  set Q' : ℝ → ℂ := fun t => (deriv a t * deriv Φ t - a t * deriv (deriv Φ) t) /
    (Complex.I * ((deriv Φ t : ℝ) : ℂ) ^ 2) with hQ'def
  set eΦ : ℝ → ℂ := fun t => Complex.exp (Complex.I * (Φ t : ℂ)) with heΦ
  set eΨ : ℝ → ℂ := fun t => Complex.exp (Complex.I * (Ψ t : ℂ)) with heΨ
  have hgnz : ∀ t ∈ I, t ≠ x₀ → deriv Φ t ≠ 0 := by
    intro t ht htx h
    have := hglow t ht; rw [h, abs_zero] at this
    have : 0 < c₁ * κ * |t - x₀| := by
      have := abs_pos.2 (sub_ne_zero.2 htx); positivity
    linarith
  have hΨat : ∀ t ∈ I, ContinuousAt Ψ t := fun t ht => hΨ.continuousAt (Ici_mem_nhds ht.1)
  have hgC : ∀ t ∈ I, ContinuousAt (fun s => ((deriv Φ s : ℝ) : ℂ)) t := fun t ht =>
    Complex.continuous_ofReal.continuousAt.comp (dg t ht).continuousAt
  have hg2C : ∀ t ∈ I, ContinuousAt (fun s => ((deriv (deriv Φ) s : ℝ) : ℂ)) t := fun t ht =>
    Complex.continuous_ofReal.continuousAt.comp (dg2 t ht).continuousAt
  have hcQ : ∀ t ∈ I, t ≠ x₀ → ContinuousAt Q t := fun t ht htx =>
    (hda t).continuousAt.div (continuousAt_const.mul (hgC t ht))
      (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hgnz t ht htx))
  have hcQ' : ∀ t ∈ I, t ≠ x₀ → ContinuousAt Q' t := fun t ht htx =>
    ((hda1.continuousAt.mul (hgC t ht)).sub ((hda t).continuousAt.mul (hg2C t ht))).div
      (continuousAt_const.mul ((hgC t ht).pow 2))
      (mul_ne_zero Complex.I_ne_zero (pow_ne_zero 2 (by exact_mod_cast hgnz t ht htx)))
  have hceΨ : ∀ t ∈ I, ContinuousAt eΨ t := fun t ht =>
    (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp (hΨat t ht))).cexp
  -- integration by parts on a side interval
  have ibp : ∀ c d, c ≤ d → Icc c d ⊆ I → (∀ t ∈ Icc c d, t ≠ x₀) →
      ∫ t in c..d, F t = Q d * E d * eΦ d - Q c * E c * eΦ c -
        (∫ t in c..d, Q' t * E t * eΦ t) + ∫ t in c..d, Q t * eΨ t * eΦ t := by
    intro c d hcd hsub hne
    have h := c03sp_aux_tri_ibp hcd (a := a) (a1 := deriv a) (E := E) (Φ := Φ) (g := deriv Φ)
      (g2 := deriv (deriv Φ)) (Ψ := Ψ) (fun t _ => hda t) (fun t ht => dΦ t (hsub ht))
      (fun t ht => dg t (hsub ht)) (fun t ht => hEd t (hsub ht))
      (fun t ht => hgnz t (hsub ht) (hne t ht)) hda1.continuousOn
      (fun t ht => (dg2 t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hΨat t (hsub ht)).continuousWithinAt)
    have i1 : IntervalIntegrable (fun t => Q' t * E t * eΦ t) volume c d := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hcd]
      intro t ht
      exact (((hcQ' t (hsub ht) (hne t ht)).mul (hEd t (hsub ht)).continuousAt).mul
        (hexpc t (hsub ht))).continuousWithinAt
    have i2 : IntervalIntegrable (fun t => Q t * eΨ t * eΦ t) volume c d := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hcd]
      intro t ht
      exact (((hcQ t (hsub ht) (hne t ht)).mul (hceΨ t (hsub ht))).mul
        (hexpc t (hsub ht))).continuousWithinAt
    have h2 : ∫ t in c..d, ((deriv a t * deriv Φ t - a t * deriv (deriv Φ) t) /
        (Complex.I * ((deriv Φ t : ℝ) : ℂ) ^ 2) * E t - a t / (Complex.I * deriv Φ t) *
          Complex.exp (Complex.I * (Ψ t : ℂ))) * Complex.exp (Complex.I * (Φ t : ℂ)) =
        (∫ t in c..d, Q' t * E t * eΦ t) - ∫ t in c..d, Q t * eΨ t * eΦ t := by
      rw [← intervalIntegral.integral_sub i1 i2]
      apply intervalIntegral.integral_congr; intro t _; simp only [hQdef, hQ'def, heΦ, heΨ]; ring
    rw [hFdef]; simp only at h ⊢; rw [h, h2]; ring
  -- boundary terms
  have hbd : ∀ t ∈ I, δ ≤ |t - x₀| → ‖Q t * E t * eΦ t‖ ≤ c₄ / c₁ * X := by
    intro t ht hδt
    have hgp : c₁ * κ * δ ≤ |deriv Φ t| :=
      le_trans (mul_le_mul_of_nonneg_left hδt (by positivity)) (hglow t ht)
    have hpos : 0 < c₁ * κ * δ := by positivity
    simp only [hQdef, heΦ]
    rw [norm_mul, norm_mul, hn1, mul_one, norm_div, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    calc ‖a t‖ / |deriv Φ t| * ‖E t‖ ≤ c₄ * A / (c₁ * κ * δ) * M := by
          apply mul_le_mul (div_le_div₀ hA0 (ha0 t ht) hpos hgp) (hEM t ht) (norm_nonneg _)
            (by positivity)
      _ = c₄ / c₁ * A * M * (κ * δ)⁻¹ := by field_simp
      _ = c₄ / c₁ * X := by rw [hκδ, hX]; ring
  -- the integral of `Q' E e^{iΦ}`
  have hJ : ∀ c d, c ≤ d → Icc c d ⊆ I → (∀ t ∈ Icc c d, δ ≤ |t - x₀|) →
      (x₀ < c ∨ d < x₀) → ‖∫ t in c..d, Q' t * E t * eΦ t‖ ≤ K₁ * X := by
    intro c d hcd hsub hδt hside
    have hne : ∀ t ∈ Icc c d, t - x₀ ≠ 0 := fun t ht h => by
      have := hδt t ht; rw [h, abs_zero] at this; linarith
    have hbound : ∀ t ∈ Icc c d, ‖Q' t * E t * eΦ t‖ ≤ K₁ * A * M / κ * ((t - x₀) ^ 2)⁻¹ := by
      intro t ht
      have hu : 0 < |t - x₀| := abs_pos.2 (hne t ht)
      have htL : |t - x₀| < L := by
        have := hsub ht; rw [abs_lt]; constructor <;> linarith [this.1, this.2]
      have h1 := c03sp_aux_tri_alg1 (a1 := deriv a t) (a := a t) (G := deriv Φ t)
        (G2 := deriv (deriv Φ) t) (c₂ := c₂) hu hκ hc₁ (hglow t (hsub ht))
        ((ha1 t (hsub ht)).trans (div_le_div_of_nonneg_left hA0 hu htL.le))
        (ha0 t (hsub ht)) (hb t (hsub ht)).2.1
      simp only [hQ'def, heΦ]
      rw [norm_mul, norm_mul, hn1, mul_one, ← hK₁, sq_abs] at *
      calc _ ≤ K₁ * A / κ * ((t - x₀) ^ 2)⁻¹ * M :=
            mul_le_mul h1 (hEM t (hsub ht)) (norm_nonneg _) (by
              have : 0 ≤ ((t - x₀) ^ 2)⁻¹ := by positivity
              positivity)
        _ = K₁ * A * M / κ * ((t - x₀) ^ 2)⁻¹ := by ring
    have hint : IntervalIntegrable (fun t => K₁ * A * M / κ * ((t - x₀) ^ 2)⁻¹) volume c d := by
      apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hcd]
      exact continuousOn_const.mul (((continuous_id.sub continuous_const).pow 2).continuousOn.inv₀
        (fun t ht => pow_ne_zero 2 (hne t ht)))
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hcd
      (Eventually.of_forall fun t ht => hbound t (Ioc_subset_Icc_self ht)) hint
    rw [intervalIntegral.integral_const_mul, c03sp_aux_integral_inv_sq hcd hside] at h1
    refine h1.trans ?_
    have hdiff : (c - x₀)⁻¹ - (d - x₀)⁻¹ ≤ δ⁻¹ := by
      rcases hside with h | h
      · have h1 := hδt c ⟨le_rfl, hcd⟩
        rw [abs_of_pos (by linarith)] at h1
        have : (c - x₀)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ h1
        have : 0 < (d - x₀)⁻¹ := inv_pos.2 (by linarith)
        linarith
      · have h1 := hδt d ⟨hcd, le_rfl⟩
        rw [abs_of_neg (by linarith)] at h1
        have : (x₀ - d)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (by linarith)
        have : (c - x₀)⁻¹ < 0 := inv_lt_zero.2 (by linarith)
        have : (d - x₀)⁻¹ = -(x₀ - d)⁻¹ := by rw [← inv_neg, neg_sub]
        linarith
    have hK : 0 ≤ K₁ * A * M / κ := by positivity
    calc K₁ * A * M / κ * ((c - x₀)⁻¹ - (d - x₀)⁻¹) ≤ K₁ * A * M / κ * δ⁻¹ :=
          mul_le_mul_of_nonneg_left hdiff hK
      _ = K₁ * X := by
          rw [hX, ← hκδ]; field_simp
          rw [show A * M * κ * δ ^ 2 = A * M * (κ * (δ * δ)) by ring, hδδ,
            mul_inv_cancel₀ hκ.ne', mul_one]
  have hη2 : η' / 2 < L - δ := by linarith
  have hbm1 : x₀ - L < bm := by rw [hbm]; linarith
  have hbm2 : bm < x₀ - δ := by rw [hbm]; linarith
  have hbp1 : x₀ + δ < bp := by rw [hbp]; linarith
  have hbp2 : bp < x₀ + L := by rw [hbp]; linarith
  have hδx : x₀ - δ < x₀ := by linarith
  have hδx' : x₀ < x₀ + δ := by linarith
  have hRsub : Icc (x₀ + δ) bp ⊆ I := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hLsub : Icc bm (x₀ - δ) ⊆ I := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hR := ibp (x₀ + δ) bp (by linarith) hRsub (fun t ht h => by linarith [ht.1])
  have hL' := ibp bm (x₀ - δ) (by linarith) hLsub (fun t ht h => by linarith [ht.2])
  have hQbp : Q bp = 0 := by simp [hQdef, hz' bp (Or.inr le_rfl)]
  have hQbm : Q bm = 0 := by simp [hQdef, hz' bm (Or.inl le_rfl)]
  rw [hQbp, zero_mul, zero_mul, zero_sub] at hR
  rw [hQbm, zero_mul, zero_mul, sub_zero] at hL'
  have hJR := hJ (x₀ + δ) bp (by linarith) hRsub
    (fun t ht => by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]) (Or.inl (by linarith))
  have hJL := hJ bm (x₀ - δ) (by linarith) hLsub
    (fun t ht => by rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]) (Or.inr (by linarith))
  have hbR := hbd (x₀ + δ) (hRsub ⟨le_rfl, by linarith⟩) (by rw [add_sub_cancel_left, abs_of_pos hδ])
  have hbL := hbd (x₀ - δ) (hLsub ⟨by linarith, le_rfl⟩)
    (by rw [show x₀ - δ - x₀ = -δ by ring, abs_neg, abs_of_pos hδ])
  -- the phase `Φ + Ψ` is affine
  set G : ℝ → ℂ := fun t => Q t * Complex.exp (Complex.I * ((ω * t + ω₀ : ℝ) : ℂ)) with hGdef
  have hGeq : ∀ t ∈ I, Q t * eΨ t * eΦ t = G t := by
    intro t ht
    simp only [hGdef, heΨ, heΦ]
    rw [mul_assoc, ← Complex.exp_add, ← mul_add]
    have hc : ((Ψ t : ℂ) + Φ t) = ((ω * t + ω₀ : ℝ) : ℂ) := by
      rw [← hlin t ht]; push_cast; ring
    rw [hc]
  have hGc : ∀ t, t ≠ x₀ → ContinuousAt G t := by
    intro t htx
    by_cases ht : t ∈ I
    · exact (hcQ t ht htx).mul (Continuous.cexp (continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_const.mul continuous_id).add
          continuous_const)))).continuousAt
    · have hev : G =ᶠ[𝓝 t] fun _ => 0 := by
        rcases not_and_or.1 ht with h | h
        · filter_upwards [Iio_mem_nhds (show t < x₀ - L + η by linarith [not_lt.1 h])] with s hs
          simp [hGdef, hQdef, hη0 s (Or.inl hs)]
        · filter_upwards [Ioi_mem_nhds (show x₀ + L - η < t by linarith [not_lt.1 h])] with s hs
          simp [hGdef, hQdef, hη0 s (Or.inr hs)]
      exact continuousAt_const.congr hev.symm
  have hGi : ∀ u v, u ≤ v → (x₀ < u ∨ v < x₀) → IntervalIntegrable G volume u v := by
    intro u v huv hs
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le huv]
    intro t ht; apply (hGc t _).continuousWithinAt
    rcases hs with h | h
    · exact ne_of_gt (by linarith [ht.1])
    · exact ne_of_lt (by linarith [ht.2])
  have hTR : ∫ t in (x₀ + δ)..bp, Q t * eΨ t * eΦ t = ∫ t in (x₀ + δ)..(x₀ + L), G t := by
    rw [intervalIntegral.integral_congr (g := G) (fun t ht => hGeq t (hRsub (by
      rwa [uIcc_of_le (by linarith)] at ht)))]
    have h0 : ∫ t in bp..(x₀ + L), G t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
      · simp
      intro t ht; rw [uIcc_of_le (by linarith)] at ht
      simp [hGdef, hQdef, hz' t (Or.inr ht.1)]
    have := intervalIntegral.integral_add_adjacent_intervals (a := x₀ + δ) (b := bp) (c := x₀ + L)
      (hGi _ _ hbp1.le (Or.inl hδx')) (hGi _ _ hbp2.le (Or.inl (hδx'.trans hbp1)))
    rw [h0, add_zero] at this
    exact this
  have hTL : ∫ t in bm..(x₀ - δ), Q t * eΨ t * eΦ t = ∫ t in (x₀ - L)..(x₀ - δ), G t := by
    rw [intervalIntegral.integral_congr (g := G) (fun t ht => hGeq t (hLsub (by
      rwa [uIcc_of_le (by linarith)] at ht)))]
    have h0 : ∫ t in (x₀ - L)..bm, G t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_]
      · simp
      intro t ht; rw [uIcc_of_le (by linarith)] at ht
      simp [hGdef, hQdef, hz' t (Or.inl ht.2)]
    have := intervalIntegral.integral_add_adjacent_intervals (a := x₀ - L) (b := bm) (c := x₀ - δ)
      (hGi _ _ hbm1.le (Or.inr (hbm2.trans hδx))) (hGi _ _ hbm2.le (Or.inr hδx))
    rw [h0, zero_add] at this
    exact this
  -- the model term
  set h0 : ℂ := a x₀ / ((deriv (deriv Φ) x₀ : ℝ) : ℂ) with hh0
  set H := c03sp_aux_triH x₀ ω ω₀ h0 with hHdef
  have hg20 := hb x₀ hx₀I
  have hh0n : ‖h0‖ ≤ c₄ / c₁ * Y := by
    rw [hh0, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < c₁ * κ := by positivity
    calc ‖a x₀‖ / |deriv (deriv Φ) x₀| ≤ c₄ * A / (c₁ * κ) :=
          div_le_div₀ hA0 (ha0 x₀ hx₀I) hpos hg20.1
      _ = c₄ / c₁ * Y := by rw [hY]; field_simp
  have hDb : ∀ t, t ≠ x₀ → |t - x₀| ≤ L → ‖G t - H t‖ ≤ K₂ * Y / L := by
    intro t htx htL
    have e : G t - H t = (Q t - h0 / (Complex.I * ((t - x₀ : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ((ω * t + ω₀ : ℝ) : ℂ)) := by
      simp only [hGdef, hHdef, c03sp_aux_triH]; ring
    rw [e, norm_mul, hn1, mul_one]
    by_cases ht : t ∈ I
    · have h2 := c03sp_aux_tri_alg2 (a_t := a t) (a0 := a x₀) (gt := deriv Φ t)
        (g20 := deriv (deriv Φ) x₀) (u := t - x₀) (sub_ne_zero.2 htx) hκ hL hc₁ (hglow t ht)
        hg20.1 hg20.2.1 (ha0 x₀ hx₀I) (hadiff t ht) (htay t ht)
      simp only [hQdef, hh0]
      refine h2.trans ?_
      rw [hY, hK₂]
      have : c₄ * (c₂ + c₃) / c₁ ^ 2 * A / (κ * L) ≤
          (c₄ * (c₂ + c₃) / c₁ ^ 2 + c₄ / c₁) * A / (κ * L) := by
        gcongr; linarith
      refine this.trans (le_of_eq ?_); field_simp
    · have hat : a t = 0 := hzero t ht
      have htL' : |t - x₀| = L := by
        apply le_antisymm htL
        by_contra hlt; push Not at hlt
        exact ht ⟨by linarith [neg_abs_le (t - x₀)], by linarith [le_abs_self (t - x₀)]⟩
      simp only [hQdef, hat, zero_div, zero_sub, norm_neg, norm_div, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, htL']
      calc ‖h0‖ / L ≤ c₄ / c₁ * Y / L := by gcongr
        _ ≤ K₂ * Y / L := by
          gcongr; rw [hK₂]; have : 0 ≤ c₄ * (c₂ + c₃) / c₁ ^ 2 := by positivity
          linarith
  have hHi : ∀ u v, u ≤ v → (x₀ < u ∨ v < x₀) → IntervalIntegrable H volume u v :=
    fun u v huv hs => c03sp_aux_triH_ii x₀ ω ω₀ h0 huv hs
  have hDR : ‖∫ t in (x₀ + δ)..(x₀ + L), (G t - H t)‖ ≤ K₂ * Y := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀ + δ) (b := x₀ + L)
      (C := K₂ * Y / L) (f := fun t => G t - H t) (fun t ht => by
        rw [uIoc_of_le (by linarith)] at ht
        exact hDb t (by linarith [ht.1]) (by
          rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.2]))
    refine this.trans ?_
    rw [abs_of_pos (by linarith)]
    calc K₂ * Y / L * (x₀ + L - (x₀ + δ)) ≤ K₂ * Y / L * L := by
          gcongr; linarith
      _ = K₂ * Y := by field_simp
  have hDL : ‖∫ t in (x₀ - L)..(x₀ - δ), (G t - H t)‖ ≤ K₂ * Y := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀ - L) (b := x₀ - δ)
      (C := K₂ * Y / L) (f := fun t => G t - H t) (fun t ht => by
        rw [uIoc_of_le (by linarith)] at ht
        exact hDb t (by linarith [ht.2]) (by
          rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.1]))
    refine this.trans ?_
    rw [abs_of_pos (by linarith)]
    calc K₂ * Y / L * (x₀ - δ - (x₀ - L)) ≤ K₂ * Y / L * L := by
          gcongr; linarith
      _ = K₂ * Y := by field_simp
  have hHs := c03sp_aux_tri_Hsum x₀ ω ω₀ h0 hδ hLδ.le
  have hHsb : ‖h0 / Complex.I * Complex.exp (Complex.I * ((ω * x₀ + ω₀ : ℝ) : ℂ)) *
      ∫ u in δ..L, c03sp_aux_sinc ω u‖ ≤ 10 * (c₄ / c₁) * Y := by
    rw [norm_mul, norm_mul, hn1, mul_one, norm_div, Complex.norm_I, div_one]
    have := c03sp_aux_sinc_bound ω hδ hLδ.le
    calc ‖h0‖ * ‖∫ u in δ..L, c03sp_aux_sinc ω u‖ ≤ (c₄ / c₁ * Y) * 10 :=
          mul_le_mul hh0n this (norm_nonneg _) (by positivity)
      _ = 10 * (c₄ / c₁) * Y := by ring
  have hsubR : ∫ t in (x₀ + δ)..(x₀ + L), G t =
      (∫ t in (x₀ + δ)..(x₀ + L), (G t - H t)) + ∫ t in (x₀ + δ)..(x₀ + L), H t := by
    rw [intervalIntegral.integral_sub (hGi _ _ (by linarith) (Or.inl (by linarith)))
      (hHi _ _ (by linarith) (Or.inl (by linarith)))]; ring
  have hsubL : ∫ t in (x₀ - L)..(x₀ - δ), G t =
      (∫ t in (x₀ - L)..(x₀ - δ), (G t - H t)) + ∫ t in (x₀ - L)..(x₀ - δ), H t := by
    rw [intervalIntegral.integral_sub (hGi _ _ (by linarith) (Or.inr (by linarith)))
      (hHi _ _ (by linarith) (Or.inr (by linarith)))]; ring
  have htotal : ∫ t in (x₀ - L)..(x₀ + L), F t =
      (∫ t in (x₀ - δ)..(x₀ + δ), F t) + Q (x₀ - δ) * E (x₀ - δ) * eΦ (x₀ - δ) -
        (∫ t in bm..(x₀ - δ), Q' t * E t * eΦ t) -
        Q (x₀ + δ) * E (x₀ + δ) * eΦ (x₀ + δ) - (∫ t in (x₀ + δ)..bp, Q' t * E t * eΦ t) +
        (∫ t in (x₀ - L)..(x₀ - δ), (G t - H t)) + (∫ t in (x₀ + δ)..(x₀ + L), (G t - H t)) +
        h0 / Complex.I * Complex.exp (Complex.I * ((ω * x₀ + ω₀ : ℝ) : ℂ)) *
          ∫ u in δ..L, c03sp_aux_sinc ω u := by
    rw [hsplit, h0L, h0R, hR, hL', hTR, hTL, hsubR, hsubL, ← hHs]; ring
  rw [htotal]
  have hfin := c03sp_aux_norm8 (∫ t in (x₀ - δ)..(x₀ + δ), F t)
    (Q (x₀ - δ) * E (x₀ - δ) * eΦ (x₀ - δ)) (∫ t in bm..(x₀ - δ), Q' t * E t * eΦ t)
    (Q (x₀ + δ) * E (x₀ + δ) * eΦ (x₀ + δ)) (∫ t in (x₀ + δ)..bp, Q' t * E t * eΦ t)
    (∫ t in (x₀ - L)..(x₀ - δ), (G t - H t)) (∫ t in (x₀ + δ)..(x₀ + L), (G t - H t))
    (h0 / Complex.I * Complex.exp (Complex.I * ((ω * x₀ + ω₀ : ℝ) : ℂ)) *
      ∫ u in δ..L, c03sp_aux_sinc ω u)
  have hCX : (2 * c₄ + 2 * (c₄ / c₁) + 2 * K₁) * X ≤ C * X :=
    mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hX0
  have hCY : (2 * K₂ + 10 * (c₄ / c₁)) * Y ≤ C * Y :=
    mul_le_mul_of_nonneg_right (by rw [hC]; linarith) hY0
  have hlin2 : (2 * c₄ + 2 * (c₄ / c₁) + 2 * K₁) * X + (2 * K₂ + 10 * (c₄ / c₁)) * Y =
      2 * c₄ * X + c₄ / c₁ * X + K₁ * X + c₄ / c₁ * X + K₁ * X + K₂ * Y + K₂ * Y +
        10 * (c₄ / c₁) * Y := by ring
  linarith [hmid, hbL, hJL, hbR, hJR, hDL, hDR, hHsb]



/-- Blueprint: def:c03_multiplier_phase.  `Θ_y(z) = Ψ(y+z) - Ψ(y) - λ(y) z`, `λ = Ψ'`. -/
def c03_mult_Theta (Ψ : ℝ → ℝ) (y z : ℝ) : ℝ := Ψ (y + z) - Ψ y - deriv Ψ y * z

/-- Blueprint: def:c03_multiplier_phase.  `F_y(z) = a(y+z) e^{iΘ_y(z)}` for `y+z ∈ (Y/4,4Y)`,
`0` otherwise. -/
def c03_mult_F (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (y z : ℝ) : ℂ :=
  if y + z ∈ Ioo (Y / 4) (4 * Y) then
    a (y + z) * Complex.exp (Complex.I * (c03_mult_Theta Ψ y z : ℂ)) else 0

/-- Blueprint: def:c03_multiplier_remainder (eqn:appendix_oscillatory_multiplier_coefficients).
`B_k(y) = (-i)^k/k! · m^{(k)}(λ(y)) · ∂_z^k F_y(0)`, `m(ξ) = ξ^p`. -/
def c03_mult_B (p Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (k : ℕ) (y : ℝ) : ℂ :=
  (-Complex.I) ^ k / (Nat.factorial k : ℂ) *
    ((iteratedDeriv k (fun ξ : ℝ => ξ ^ p) (deriv Ψ y) : ℝ) : ℂ) *
    iteratedDeriv k (c03_mult_F Y a Ψ y) 0

/-- Blueprint: def:c03_multiplier_remainder (eqn:appendix_oscillatory_multiplier_expansion).
`ℛ_{mult,N}(y) = e^{-iΨ(y)} |D|^p(a e^{iΨ})(y) - ∑_{k=0}^{2N-2} B_k(y)` (`|D|^p = fracDC`). -/
def c03_mult_R (p Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (N : ℕ) (y : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (Ψ y : ℂ))) *
      fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y -
    ∑ k ∈ Finset.range (2 * N - 1), c03_mult_B p Y a Ψ k y

/-- Blueprint: def:c03_multiplier_remainder.  Taylor remainder
`R_{2N-1}(z) = F_y(z) - ∑_{k=0}^{2N-2} F_y^{(k)}(0) z^k / k!`. -/
def c03_mult_taylorR (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (N : ℕ) (y z : ℝ) : ℂ :=
  c03_mult_F Y a Ψ y z - ∑ k ∈ Finset.range (2 * N - 1),
    iteratedDeriv k (c03_mult_F Y a Ψ y) 0 / (Nat.factorial k : ℂ) * (z : ℂ) ^ k

/-- Blueprint: def:c03_multiplier_remainder.  The index set of the Taylor remainder formula:
`(r, q)` with `q : Fin (2N-1) → ℕ` (`q i` = `q_{i+1}`) and `r + ∑_j j q_j = 2N-1`. -/
def c03_mult_index (N : ℕ) : Finset (ℕ × (Fin (2 * N - 1) → ℕ)) :=
  ((Finset.range (2 * N)) ×ˢ Fintype.piFinset (fun _ : Fin (2 * N - 1) => Finset.range (2 * N))).filter
    (fun rq => rq.1 + ∑ i, (i.val + 1) * rq.2 i = 2 * N - 1)

/-- Blueprint: def:c03_multiplier_remainder.  `i^{∑ q_j} / (r! ∏_j q_j! (j!)^{q_j})`. -/
def c03_mult_coeff {n : ℕ} (r : ℕ) (q : Fin n → ℕ) : ℂ :=
  Complex.I ^ (∑ i, q i) /
    ((Nat.factorial r : ℂ) * ∏ i, (Nat.factorial (q i) : ℂ) * (Nat.factorial (i.val + 1) : ℂ) ^ q i)

/-- Blueprint: def:c03_multiplier_summands.  The amplitude
`b_t(z) = z^{2N-1} a^{(r)}(y+tz) ∏_j (Θ_y^{(j)}(tz))^{q_j}` (`0` if `y+tz ∉ (Y/4,4Y)`). -/
def c03_mult_bt (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (N r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (y t z : ℝ) : ℂ :=
  if y + t * z ∈ Ioo (Y / 4) (4 * Y) then
    (z : ℂ) ^ (2 * N - 1) * iteratedDeriv r a (y + t * z) *
      ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) (t * z) : ℝ) : ℂ) ^ q i
  else 0

/-- Blueprint: def:c03_multiplier_summands.  The phase `φ_t(z) = λ(y) z + Θ_y(tz)`. -/
def c03_mult_phit (Ψ : ℝ → ℝ) (y t z : ℝ) : ℝ := deriv Ψ y * z + c03_mult_Theta Ψ y (t * z)

/-- Blueprint: def:c03_multiplier_summands.  The summand integral
`I_η(y,t) = ∫ e^{iφ_t(z) - ηz²} b_t(z) |z|^{-1-p} dz`. -/
def c03_mult_I (p Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (N r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (η y t : ℝ) : ℂ :=
  ∫ z : ℝ, Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
    c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)

/-- Blueprint: def:c03_multiplier_summands.  `q₁` (the multiplicity of `Θ'`). -/
def c03_mult_q1 {n : ℕ} (q : Fin n → ℕ) : ℕ := ∑ i, if i.val = 0 then q i else 0

/-- Blueprint: def:c03_multiplier_summands.  `ℓ = ∑_{j ≥ 2} q_j`. -/
def c03_mult_ell {n : ℕ} (q : Fin n → ℕ) : ℕ := ∑ i, if 1 ≤ i.val then q i else 0

/-- Blueprint: def:c03_multiplier_summands.  The size `B = A Λ^{q₁+ℓ} Y^{-2N+1+ℓ} t^{q₁}`. -/
def c03_mult_size (N : ℕ) {n : ℕ} (q : Fin n → ℕ) (Y Λ A t : ℝ) : ℝ :=
  A * Λ ^ (c03_mult_q1 q + c03_mult_ell q) *
    Y ^ (-(2 * N : ℝ) + 1 + c03_mult_ell q) * t ^ c03_mult_q1 q

/-- Blueprint: def:c03_multiplier_phase (hypotheses).  `a ∈ C_c^∞((Y/4,4Y);ℂ)`,
`Ψ ∈ C^∞((Y/4,4Y);ℝ)`, and on `(Y/4,4Y)`: `c₀⁻¹Λ ≤ λ ≤ c₀Λ`, `|∂^kλ| ≤ C_k Λ Y^{-k}`,
`|∂^k a| ≤ C_k A Y^{-k}` for `k ≤ k₀`. -/
def c03_mult_hyp (Y Λ A c₀ : ℝ) (Ck : ℕ → ℝ) (k₀ : ℕ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) a ∧ tsupport a ⊆ Ioo (Y / 4) (4 * Y) ∧
  ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)) ∧
  ∀ y ∈ Ioo (Y / 4) (4 * Y), c₀⁻¹ * Λ ≤ deriv Ψ y ∧ deriv Ψ y ≤ c₀ * Λ ∧
    ∀ k ≤ k₀, |iteratedDeriv k (deriv Ψ) y| ≤ Ck k * Λ * Y ^ (-(k : ℝ)) ∧
      ‖iteratedDeriv k a y‖ ≤ Ck k * A * Y ^ (-(k : ℝ))




/-- Blueprint: def:c03_multiplier_remainder
(eqn:appendix_oscillatory_multiplier_two_term_expansion).
`ℛ̃_{mult,2} = ℛ_{mult,2} - p(p-1)/2 · λ^{p-2} a''`. -/
def c03_mult_R2tilde (p Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (y : ℝ) : ℂ :=
  c03_mult_R p Y a Ψ 2 y - ((p * (p - 1) / 2 * deriv Ψ y ^ (p - 2) : ℝ) : ℂ) * deriv (deriv a) y


end GSQG
