import GSQG.AppendixAB.SymbolCalculus

/-!
# Appendix B: stationary phase, compact/Euler/near part (toolbox; blueprint ch. 03)

Blueprint sublemmas (with their blueprint Lean names) and proofs of the nodes
`c03_sp_compact`, `c03_sp_euler`, `c03_sp_near` under the prefix `c03s_` (same statements as the public ones in
`AppendixAB/Statements.lean`). Helpers: `c03s_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### Data -/

/-- Morse coordinate of `lem:c03_morse_h`,
`w(s) = (s-1) ((2/p) ∫₀¹ (1-t) p (1+t(s-1))^{p-1} dt)^{1/2}`.
Same body as `GSQG.c03_morse_w` (in `AppendixAB/Statements.lean`, which this module does not
import). -/
def c03s_aux_morse_w (p s : ℝ) : ℝ :=
  (s - 1) * Real.sqrt (2 / p * ∫ t in (0 : ℝ)..1, (1 - t) * p * (1 + t * (s - 1)) ^ (p - 1))

/-- The inverse Morse coordinate `s(v)` (inverse of `w` on `(0,∞)`). -/
def c03s_aux_morse_s (p : ℝ) : ℝ → ℝ := Function.invFunOn (c03s_aux_morse_w p) (Ioi 0)

/-- Blueprint: lem:c03_sp_morse_amplitude.  The transported amplitude
`e(v) = c(s(v)) s'(v)` on `J = (w(1/2), w(2))`, extended by zero. -/
def c03s_aux_morse_e (p : ℝ) (c : ℝ → ℂ) (v : ℝ) : ℂ :=
  if v ∈ Ioo (c03s_aux_morse_w p (1 / 2)) (c03s_aux_morse_w p 2) then
    c (c03s_aux_morse_s p v) * ((deriv (c03s_aux_morse_s p) v : ℝ) : ℂ)
  else 0

/-- The Euler operator `𝔈 b = p⁻¹(-m b + s b')` of `lem:c03_sp_scaled_symbol`. -/
def c03s_aux_frakE (p m : ℝ) (b : ℝ → ℂ) (s : ℝ) : ℂ :=
  (1 / p : ℂ) * (-(m : ℂ) * b s + (s : ℂ) * deriv b s)

/-- The Euler operator `E = y ∂_y` acting on functions of `y`. -/
def c03s_aux_E (F : ℝ → ℂ) (y : ℝ) : ℂ := (y : ℂ) * deriv F y

/-! ### Helpers for `c03_euler_to_deriv` -/

theorem c03s_aux_E_contDiffOn {F : ℝ → ℂ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_E F) (Ioi 0) := by
  unfold c03s_aux_E
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (deriv F) (Ioi 0) :=
    hF.deriv_of_isOpen isOpen_Ioi (by exact_mod_cast le_rfl)
  exact (Complex.ofRealCLM.contDiff.contDiffOn).mul h1

theorem c03s_aux_E_iter_contDiffOn {F : ℝ → ℂ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Ioi 0)) (l : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_E^[l] F) (Ioi 0) := by
  induction l with
  | zero => simpa using hF
  | succ l ih => rw [Function.iterate_succ_apply']; exact c03s_aux_E_contDiffOn ih

theorem c03s_aux_hasDerivAt_iteratedDeriv {F : ℝ → ℂ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Ioi 0))
    (j : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j + 1) F y) y := by
  have hd : DifferentiableOn ℝ (iteratedDerivWithin j F (Ioi 0)) (Ioi 0) :=
    hF.differentiableOn_iteratedDerivWithin (by exact_mod_cast WithTop.coe_lt_top _)
      isOpen_Ioi.uniqueDiffOn
  have hev : iteratedDerivWithin j F (Ioi 0) =ᶠ[𝓝 y] iteratedDeriv j F := by
    filter_upwards [Ioi_mem_nhds hy] with z hz using iteratedDerivWithin_of_isOpen isOpen_Ioi hz
  have h1 := ((hd y hy).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt.congr_of_eventuallyEq hev.symm
  rw [iteratedDeriv_succ]
  rwa [hev.deriv_eq] at h1

theorem c03s_aux_coeff_succ (j l : ℕ) :
    (((descPochhammer ℤ (j + 1)).coeff (l + 1) : ℤ) : ℂ) =
      (((descPochhammer ℤ j).coeff l : ℤ) : ℂ) - (j : ℂ) * (((descPochhammer ℤ j).coeff (l + 1) : ℤ) : ℂ) := by
  rw [descPochhammer_succ_right, show ((j : Polynomial ℤ)) = Polynomial.C (j : ℤ) by simp,
    Polynomial.coeff_mul_X_sub_C]
  push_cast; ring

theorem c03s_aux_coeff_zero (j : ℕ) :
    (((descPochhammer ℤ (j + 1)).coeff 0 : ℤ) : ℂ) =
      -((j : ℂ) * (((descPochhammer ℤ j).coeff 0 : ℤ) : ℂ)) := by
  rw [descPochhammer_succ_right, show ((j : Polynomial ℤ)) = Polynomial.C (j : ℤ) by simp,
    mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C]
  push_cast; ring

theorem c03s_aux_coeff_top (j : ℕ) : (descPochhammer ℤ j).coeff (j + 1) = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [descPochhammer_natDegree]; omega)

/-! ### Helpers for `c03_sp_near` -/

/-- Leibniz bound for iterated derivatives at a point of `(0,∞)`. -/
theorem c03s_aux_leibniz {f g : ℝ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0)) {y : ℝ} (hy : 0 < y) (n : ℕ) :
    ‖iteratedDeriv n (fun y => f y * g y) y‖ ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedDeriv i f y‖ * ‖iteratedDeriv (n - i) g y‖ := by
  have hs : UniqueDiffOn ℝ (Ioi (0 : ℝ)) := isOpen_Ioi.uniqueDiffOn
  have e : ∀ (F : ℝ → ℂ) k, ‖iteratedDeriv k F y‖ = ‖iteratedFDerivWithin ℝ k F (Ioi 0) y‖ := by
    intro F k
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_of_isOpen isOpen_Ioi hy]
  simp_rw [e]
  exact norm_iteratedFDerivWithin_mul_le hf hg hs hy (by exact_mod_cast le_top)

/-- `y ↦ (y^r : ℂ)` is smooth on `(0,∞)` with `|∂^i y^r| = |(r)_i| y^{r-i}`. -/
theorem c03s_aux_ofReal_rpow (r : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => ((y ^ r : ℝ) : ℂ)) (Ioi 0) ∧
    ∀ i : ℕ, ∀ y : ℝ, 0 < y → ‖iteratedDeriv i (fun y : ℝ => ((y ^ r : ℝ) : ℂ)) y‖ =
      |(descPochhammer ℝ i).eval r| * y ^ (r - i) := by
  have hrp : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ r) (Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (fun x hx => (ne_of_gt hx))
  refine ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn hrp, fun i y hy => ?_⟩
  have hca : ContDiffAt ℝ i (fun y : ℝ => y ^ r) y :=
    (hrp.contDiffAt (Ioi_mem_nhds hy)).of_le (by exact_mod_cast le_top)
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    show (fun y : ℝ => ((y ^ r : ℝ) : ℂ)) = Complex.ofRealLI ∘ (fun y : ℝ => y ^ r) from rfl,
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left hca le_rfl,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_rpow_const,
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]

/-! ### Statements -/




theorem c03s_aux_base {s t : ℝ} (hs : 0 < s) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + t * (s - 1) := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]; linarith
  · nlinarith [ht.1]

/-- Smoothness of `s ↦ ∫₀¹ G(1 + t(s-1)) dt` for `G` smooth on `(0,∞)`. -/
theorem c03s_aux_param_smooth {G : ℝ → ℝ} (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => ∫ t in (0 : ℝ)..1, G (1 + t * (s - 1))) (Ioi 0) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  apply ContDiffOn.parametric_integral (μ := volume) isOpen_Ioi isCompact_Icc
    Ioc_subset_Icc_self ?_ (by simp)
  have hl : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => 1 + x.2 * (x.1 - 1)) (Ioi 0 ×ˢ Icc 0 1) :=
    (contDiff_const.add (contDiff_snd.mul (contDiff_fst.sub contDiff_const))).contDiffOn
  exact hG.comp hl (fun x hx => c03s_aux_base hx.1 hx.2)

/-- `(∫₀¹ G'(1+t(s-1)) dt) (s-1) = G(s) - G(1)`. -/
theorem c03s_aux_param_ftc {G G' : ℝ → ℝ} (hG : ∀ x, 0 < x → HasDerivAt G (G' x) x)
    (hG' : ContinuousOn G' (Ioi 0)) {s : ℝ} (hs : 0 < s) :
    (∫ t in (0 : ℝ)..1, G' (1 + t * (s - 1))) * (s - 1) = G s - G 1 := by
  have hx : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < 1 + t * (s - 1) := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht; exact c03s_aux_base hs ht
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => G (1 + t * (s - 1)))
      (G' (1 + t * (s - 1)) * (s - 1)) t := by
    intro t ht
    have hl : HasDerivAt (fun t : ℝ => 1 + t * (s - 1)) (1 * (s - 1)) t :=
      ((hasDerivAt_id t).mul_const (s - 1)).const_add 1
    rw [one_mul] at hl
    exact (hG _ (hx t ht)).comp t hl
  have hc : ContinuousOn (fun t => G' (1 + t * (s - 1)) * (s - 1)) (uIcc 0 1) :=
    (hG'.comp (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      (fun t ht => hx t ht)).mul continuousOn_const
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [intervalIntegral.integral_mul_const] at this
  rw [this]; simp

/-- Blueprint: lem:c03_sp_q_extension.  With `N(s) = ∫₀¹ h'(1+t(s-1)) dt`,
`D(s) = ∫₀¹ h''(1+t(s-1)) dt` (`h'(x) = 1 - x^p`, `h''(x) = -p x^{p-1}`): `N, D ∈ C^∞(0,∞)`,
`D < 0`, `q = N/D` (which equals `(h(s)-h(1))/h'(s)` for `s ≠ 1`), `q(1) = 0`, `q'(1) = ½`, and
every derivative of `q` is bounded on `[½,2]`. -/
theorem c03_sp_q_extension (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => ∫ t in (0 : ℝ)..1, (1 - (1 + t * (s - 1)) ^ p)) (Ioi 0) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => ∫ t in (0 : ℝ)..1, -(p * (1 + t * (s - 1)) ^ (p - 1)))
      (Ioi 0) ∧
    (∀ s, 0 < s → (∫ t in (0 : ℝ)..1, -(p * (1 + t * (s - 1)) ^ (p - 1))) < 0) ∧
    (∀ s, 0 < s → c03_sp_q p s = (∫ t in (0 : ℝ)..1, (1 - (1 + t * (s - 1)) ^ p)) /
      ∫ t in (0 : ℝ)..1, -(p * (1 + t * (s - 1)) ^ (p - 1))) ∧
    (∀ s, 0 < s → s ≠ 1 → c03_sp_q p s = (c03_h p s - c03_h p 1) / (1 - s ^ p)) ∧
    c03_sp_q p 1 = 0 ∧ deriv (c03_sp_q p) 1 = 1 / 2 ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_q p) (Ioi 0) ∧
    ∀ k : ℕ, ∃ C, ∀ s ∈ Icc (1 / 2 : ℝ) 2, |iteratedDeriv k (c03_sp_q p) s| ≤ C := by
  set N : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..1, (1 - (1 + t * (s - 1)) ^ p) with hN
  set Dn : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..1, -(p * (1 + t * (s - 1)) ^ (p - 1)) with hD
  have hrp : ∀ r : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ r) (Ioi 0) := fun r =>
    contDiffOn_id.rpow_const_of_ne (fun x hx => (ne_of_gt hx))
  have hNs : ContDiffOn ℝ (⊤ : ℕ∞) N (Ioi 0) :=
    c03s_aux_param_smooth (G := fun x => 1 - x ^ p) (contDiffOn_const.sub (hrp p))
  have hDs : ContDiffOn ℝ (⊤ : ℕ∞) Dn (Ioi 0) :=
    c03s_aux_param_smooth (G := fun x => -(p * x ^ (p - 1))) (contDiffOn_const.mul (hrp _)).neg
  have hDneg : ∀ s, 0 < s → Dn s < 0 := by
    intro s hs
    have hc : ContinuousOn (fun t => p * (1 + t * (s - 1)) ^ (p - 1)) (Icc 0 1) :=
      continuousOn_const.mul (ContinuousOn.rpow_const (by fun_prop)
        (fun t ht => Or.inl (c03s_aux_base hs ht).ne'))
    have := intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc.intervalIntegrable_of_Icc zero_le_one) (fun t ht =>
        mul_pos hp (Real.rpow_pos_of_pos (c03s_aux_base hs (Ioo_subset_Icc_self ht)) _)) zero_lt_one
    simp only [hD, intervalIntegral.integral_neg]
    linarith
  -- derivative of `h` and of `h'`
  have hhd : ∀ x, 0 < x → HasDerivAt (c03_h p) (1 - x ^ p) x := by
    intro x hx
    have hr := Real.hasDerivAt_rpow_const (p := p + 1) (Or.inl hx.ne')
    have h := (hasDerivAt_id x).sub (hr.div_const (p + 1))
    have hp1' : p + 1 ≠ 0 := by linarith
    unfold c03_h
    exact h.congr_deriv (by rw [add_sub_cancel_right]; field_simp)
  have hh'd : ∀ x, 0 < x → HasDerivAt (fun x : ℝ => 1 - x ^ p) (-(p * x ^ (p - 1))) x := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).const_sub 1
  have hNid : ∀ s, 0 < s → N s * (s - 1) = c03_h p s - c03_h p 1 :=
    fun s hs => c03s_aux_param_ftc hhd (continuousOn_const.sub (hrp p).continuousOn) hs
  have hDid : ∀ s, 0 < s → Dn s * (s - 1) = 1 - s ^ p := by
    intro s hs
    have := c03s_aux_param_ftc hh'd ((continuousOn_const.mul (hrp (p - 1)).continuousOn).neg) hs
    rw [this]; simp
  have hqND : ∀ s, 0 < s → c03_sp_q p s = N s / Dn s := by
    intro s hs
    unfold c03_sp_q
    split_ifs with h1
    · subst h1; simp [hN]
    · have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
      rw [← hNid s hs, ← hDid s hs, mul_div_mul_right _ _ hs1]
  have hqs : ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_q p) (Ioi 0) :=
    (hNs.div hDs fun s hs => (hDneg s hs).ne).congr fun s hs => hqND s hs
  -- `N'(1) = -p/2` via the second derivative of `N(s)(s-1)`
  have hdiff : ∀ {f : ℝ → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0) → ∀ x, 0 < x →
      HasDerivAt f (deriv f x) x := fun hf x hx =>
    ((hf.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hN's : ContDiffOn ℝ (⊤ : ℕ∞) (deriv N) (Ioi 0) :=
    hNs.deriv_of_isOpen isOpen_Ioi (by exact_mod_cast le_rfl)
  have hfirst : ∀ s, 0 < s → deriv N s * (s - 1) + N s = 1 - s ^ p := by
    intro s hs
    have h1 : HasDerivAt (fun s => N s * (s - 1)) (deriv N s * (s - 1) + N s * 1) s :=
      (hdiff hNs s hs).mul ((hasDerivAt_id s).sub_const 1)
    have h2 : HasDerivAt (fun s => N s * (s - 1)) (1 - s ^ p) s := by
      refine ((hhd s hs).sub_const (c03_h p 1)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hs] with z hz using hNid z hz
    rw [← h1.unique h2]; ring
  have hN1 : deriv N 1 = -(p / 2) := by
    have h1 : HasDerivAt (fun s => deriv N s * (s - 1) + N s)
        (deriv (deriv N) 1 * (1 - 1) + deriv N 1 * 1 + deriv N 1) 1 :=
      ((hdiff hN's 1 one_pos).mul ((hasDerivAt_id (1 : ℝ)).sub_const 1)).add (hdiff hNs 1 one_pos)
    have h2 : HasDerivAt (fun s => deriv N s * (s - 1) + N s) (-(p * (1 : ℝ) ^ (p - 1))) 1 := by
      refine (hh'd 1 one_pos).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds one_pos] with z hz using hfirst z hz
    have := h1.unique h2
    simp at this; linarith
  have hN1v : N 1 = 0 := by simp [hN]
  have hD1v : Dn 1 = -p := by simp [hD]
  have hq1 : deriv (c03_sp_q p) 1 = 1 / 2 := by
    have h1 : HasDerivAt (fun s => N s / Dn s)
        ((deriv N 1 * Dn 1 - N 1 * deriv Dn 1) / Dn 1 ^ 2) 1 :=
      (hdiff hNs 1 one_pos).div (hdiff hDs 1 one_pos) (hDneg 1 one_pos).ne
    have h2 := h1.congr_of_eventuallyEq (show c03_sp_q p =ᶠ[𝓝 1] fun s => N s / Dn s by
      filter_upwards [Ioi_mem_nhds one_pos] with z hz using hqND z hz)
    rw [h2.deriv, hN1, hN1v, hD1v]
    field_simp; ring
  refine ⟨hNs, hDs, hDneg, hqND, fun s hs h1 => ?_, by simp [c03_sp_q], hq1, hqs, fun k => ?_⟩
  · unfold c03_sp_q; simp [h1]
  · have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by
      simp only [mem_Ioi]; linarith [hx.1]
    have hcont : ContinuousOn (iteratedDerivWithin k (c03_sp_q p) (Ioi 0)) (Ioi 0) :=
      hqs.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) isOpen_Ioi.uniqueDiffOn
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.mono hsub)
    refine ⟨C, fun s hs => ?_⟩
    have := hC s hs
    rwa [iteratedDerivWithin_of_isOpen isOpen_Ioi (hsub hs), Real.norm_eq_abs] at this

/-- Upper bound for the `C^k` norm from pointwise derivative bounds. -/
theorem c03s_aux_Ck_norm_le {g : ℝ → ℂ} {k : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i ≤ k, ∀ x, ‖iteratedDeriv i g x‖ ≤ B) : c03_Ck_normR k univ g ≤ (k + 1) * B := by
  unfold c03_Ck_normR c03_Ck_norm
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  calc ∑ i ∈ Finset.range (k + 1), ⨆ x ∈ univ, ‖iteratedDerivWithin i g univ x‖ₑ
      ≤ ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal B := by
        refine Finset.sum_le_sum fun i hi => iSup₂_le fun x _ => ?_
        rw [iteratedDerivWithin_univ, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hB i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) x)
    _ = ENNReal.ofReal ((k + 1) * B) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB0)]
        simp

theorem c03s_aux_Ck_nonneg (k : ℕ) (g : ℝ → ℂ) : 0 ≤ c03_Ck_normR k univ g := ENNReal.toReal_nonneg

/-- A function locally vanishing off `tsupport c`. -/
theorem c03s_aux_iter_zero_off {f : ℝ → ℂ} {S : Set ℝ} (hS : IsClosed S) (hf : ∀ s ∉ S, f s = 0)
    (i : ℕ) {s : ℝ} (hs : s ∉ S) : iteratedDeriv i f s = 0 := by
  have hev : f =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [hS.isOpen_compl.mem_nhds hs] with z hz using hf z hz
  rw [(hev.iteratedDeriv i).eq_of_nhds]; simp

/-- Blueprint: lem:c03_sp_T_bounds.  For `c ∈ C_c^∞((½,2))`: `Tc ∈ C_c^∞((½,2))`, `Tc(1) = 0`, and
`‖Tc‖_{C^k} ≤ C_k ‖c‖_{C^{k+1}}` with `C_k = C_k(p)`. -/
theorem c03_sp_T_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      ContDiff ℝ (⊤ : ℕ∞) (c03_sp_T p c) ∧ tsupport (c03_sp_T p c) ⊆ Ioo (1 / 2) 2 ∧
      c03_sp_T p c 1 = 0) ∧
    ∀ k : ℕ, ∃ C, 0 < C ∧ ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      c03_Ck_normR k univ (c03_sp_T p c) ≤ C * c03_Ck_normR (k + 1) univ c := by
  obtain ⟨-, -, -, -, -, hq1v, hq1d, hqs, hqb⟩ := c03_sp_q_extension p hp hp1
  set qc : ℝ → ℂ := fun s => ((c03_sp_q p s : ℝ) : ℂ) with hqc
  have hqcs : ContDiffOn ℝ (⊤ : ℕ∞) qc (Ioi 0) := Complex.ofRealCLM.contDiff.comp_contDiffOn hqs
  have hsub : Ioo (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by simp only [mem_Ioi]; linarith [hx.1]
  -- smoothness of `cq`
  have hcq : ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      ContDiff ℝ (⊤ : ℕ∞) (fun s => c s * qc s) := by
    intro c hc hcs
    rw [contDiff_iff_contDiffAt]
    intro s
    by_cases hs : s ∈ tsupport c
    · exact hc.contDiffAt.mul (hqcs.contDiffAt (Ioi_mem_nhds (hsub (hcs hs))))
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport c).isOpen_compl.mem_nhds hs] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hoff : ∀ c : ℝ → ℂ, ∀ s ∉ tsupport c, c03_sp_T p c s = 0 := by
    intro c s hs
    unfold c03_sp_T
    have h1 : (fun s => c s * qc s) =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport c).isOpen_compl.mem_nhds hs] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    have := h1.deriv_eq
    simp only [hqc] at this
    rw [this, image_eq_zero_of_notMem_tsupport hs]; simp
  have hTs : ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      ContDiff ℝ (⊤ : ℕ∞) (c03_sp_T p c) := by
    intro c hc hcs
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun s => c s * qc s)) := by
      simpa using (hcq c hc hcs).iterate_deriv 1
    exact (hc.div_const 2).sub h1
  have hTsupp : ∀ c : ℝ → ℂ, tsupport (c03_sp_T p c) ⊆ tsupport c := fun c =>
    closure_minimal (fun s hs => by
      by_contra h; exact hs (hoff c s h)) (isClosed_tsupport c)
  refine ⟨fun c hc hcs => ⟨hTs c hc hcs, (hTsupp c).trans hcs, ?_⟩, fun k => ?_⟩
  · -- `Tc(1) = 0`
    have hqd : HasDerivAt (c03_sp_q p) (1 / 2) 1 := by
      have := ((hqs.contDiffAt (Ioi_mem_nhds one_pos)).differentiableAt (by simp)).hasDerivAt
      rwa [hq1d] at this
    have hqcd : HasDerivAt qc ((1 / 2 : ℝ) : ℂ) 1 := hqd.ofReal_comp
    have hcd : HasDerivAt c (deriv c 1) 1 := (hc.differentiable (by simp) 1).hasDerivAt
    have := hcd.mul hqcd
    unfold c03_sp_T
    change c 1 / 2 - deriv (c * qc) 1 = 0
    rw [this.deriv]
    simp [hqc, hq1v]; ring
  · -- the norm bound
    choose Q hQ using hqb
    have hQc : ∀ i : ℕ, ∀ s ∈ Ioo (1 / 2 : ℝ) 2, ‖iteratedDeriv i qc s‖ ≤ |Q i| := by
      intro i s hs
      have hca : ContDiffAt ℝ i (c03_sp_q p) s :=
        (hqs.contDiffAt (Ioi_mem_nhds (hsub hs))).of_le (by exact_mod_cast le_top)
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        show qc = Complex.ofRealLI ∘ (c03_sp_q p) from rfl,
        Complex.ofRealLI.norm_iteratedFDeriv_comp_left hca le_rfl,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact (hQ i s (Ioo_subset_Icc_self hs)).trans (le_abs_self _)
    set S : ℝ := ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (i + 2),
      ((i + 1).choose j : ℝ) * |Q (i + 1 - j)| with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
    refine ⟨(k + 1) * (1 / 2 + S) + 1, by positivity, fun c hc hcs => ?_⟩
    set P := c03_Ck_normR (k + 1) univ c
    have hP0 : 0 ≤ P := c03s_aux_Ck_nonneg _ _
    have hcomp : HasCompactSupport c :=
      HasCompactSupport.intro' (K := tsupport c) (isCompact_Icc.of_isClosed_subset
        (isClosed_tsupport c) (hcs.trans Ioo_subset_Icc_self)) (isClosed_tsupport c)
        (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    have hcP : ∀ j ≤ k + 1, ∀ x, ‖iteratedDeriv j c x‖ ≤ P := fun j hj x =>
      c03sp_aux_Ck_le (hc.of_le (by exact_mod_cast le_top)) hcomp hj x
    have hbound : ∀ i ≤ k, ∀ x, ‖iteratedDeriv i (c03_sp_T p c) x‖ ≤ P * (1 / 2 + S) := by
      intro i hi x
      by_cases hx : x ∈ tsupport c
      · have hx0 : 0 < x := hsub (hcs hx)
        have hc' : ContDiffAt ℝ i (fun s => c s / 2) x :=
          (hc.div_const 2).contDiffAt.of_le (by exact_mod_cast le_top)
        have hd' : ContDiffAt ℝ i (deriv (fun s => c s * qc s)) x := by
          have : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun s => c s * qc s)) := by
            simpa using (hcq c hc hcs).iterate_deriv 1
          exact this.contDiffAt.of_le (by exact_mod_cast le_top)
        have e1 : iteratedDeriv i (c03_sp_T p c) x =
            iteratedDeriv i (fun s => c s / 2) x - iteratedDeriv (i + 1) (fun s => c s * qc s) x := by
          change iteratedDeriv i ((fun s => c s / 2) - deriv (fun s => c s * qc s)) x = _
          rw [iteratedDeriv_sub hc' hd', iteratedDeriv_succ']
        have e2 : iteratedDeriv i (fun s => c s / 2) x = (1 / 2 : ℂ) * iteratedDeriv i c x := by
          rw [show (fun s => c s / 2) = fun s => (1 / 2 : ℂ) * c s by funext s; ring,
            iteratedDeriv_const_mul _ (hc.contDiffAt.of_le (by exact_mod_cast le_top))]
        rw [e1, e2]
        have hL := c03s_aux_leibniz (hc.contDiffOn) hqcs hx0 (i + 1)
        have h1 : ‖(1 / 2 : ℂ) * iteratedDeriv i c x‖ ≤ P * (1 / 2) := by
          rw [norm_mul]; norm_num
          linarith [hcP i (by omega) x]
        have h2 : ‖iteratedDeriv (i + 1) (fun s => c s * qc s) x‖ ≤ P * S := by
          refine hL.trans ?_
          have hsi : ∑ j ∈ Finset.range (i + 2), ((i + 1).choose j : ℝ) * |Q (i + 1 - j)| ≤ S :=
            Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (i + 2),
              ((i + 1).choose j : ℝ) * |Q (i + 1 - j)|)
              (fun i _ => Finset.sum_nonneg fun j _ => by positivity)
              (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
          calc _ ≤ ∑ j ∈ Finset.range (i + 1 + 1), ((i + 1).choose j : ℝ) * P * |Q (i + 1 - j)| := by
                refine Finset.sum_le_sum fun j hj => ?_
                have hj' : j ≤ i + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
                gcongr
                · exact hcP j (by omega) x
                · exact hQc _ x (hcs hx)
            _ = P * ∑ j ∈ Finset.range (i + 2), ((i + 1).choose j : ℝ) * |Q (i + 1 - j)| := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
            _ ≤ P * S := mul_le_mul_of_nonneg_left hsi hP0
        calc _ ≤ ‖(1 / 2 : ℂ) * iteratedDeriv i c x‖ + ‖iteratedDeriv (i + 1) (fun s => c s * qc s) x‖ :=
              norm_sub_le _ _
          _ ≤ P * (1 / 2) + P * S := add_le_add h1 h2
          _ = _ := by ring
      · rw [c03s_aux_iter_zero_off (isClosed_tsupport c) (hoff c) i hx, norm_zero]
        positivity
    calc c03_Ck_normR k univ (c03_sp_T p c) ≤ (k + 1) * (P * (1 / 2 + S)) :=
          c03s_aux_Ck_norm_le (by positivity) hbound
      _ ≤ ((k + 1) * (1 / 2 + S) + 1) * P := by nlinarith

/-- An integral over `(0,∞)` of a function vanishing off `(1/2,2)` is an integral over `[1/2,2]`. -/
theorem c03s_aux_Ioi_Icc {f : ℝ → ℂ} (hf : ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → f s = 0) :
    ∫ s in Ioi (0 : ℝ), f s = ∫ s in Icc (1 / 2 : ℝ) 2, f s := by
  have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by simp only [mem_Ioi]; linarith [hx.1]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    (fun s hs => hf s (fun h => hs.2 (Ioo_subset_Icc_self h)))

theorem c03s_aux_hasDerivAt_expI (φ : ℝ) (μ : ℝ) :
    HasDerivAt (fun μ : ℝ => Complex.exp (Complex.I * ((μ * φ : ℝ) : ℂ)))
      (Complex.I * φ * Complex.exp (Complex.I * ((μ * φ : ℝ) : ℂ))) μ := by
  have h1 : HasDerivAt (fun μ : ℝ => Complex.I * ((μ * φ : ℝ) : ℂ)) (Complex.I * ((1 * φ : ℝ) : ℂ)) μ :=
    (((hasDerivAt_id μ).mul_const φ).ofReal_comp).const_mul Complex.I
  convert h1.cexp using 1
  push_cast; ring

/-- Differentiation in `μ` under a compact integral. -/
theorem c03s_aux_mu_deriv {g : ℝ → ℂ} {φ : ℝ → ℝ} (hg : ContinuousOn g (Icc (1 / 2 : ℝ) 2))
    (hφ : ContinuousOn φ (Icc (1 / 2 : ℝ) 2)) (μ₀ : ℝ) :
    HasDerivAt (fun μ : ℝ => ∫ s in Icc (1 / 2 : ℝ) 2, g s * Complex.exp (Complex.I * ((μ * φ s : ℝ) : ℂ)))
      (∫ s in Icc (1 / 2 : ℝ) 2, Complex.I * φ s * g s *
        Complex.exp (Complex.I * ((μ₀ * φ s : ℝ) : ℂ))) μ₀ := by
  set K := Icc (1 / 2 : ℝ) 2
  have hφc : ContinuousOn (fun s => ((φ s : ℝ) : ℂ)) K := Complex.continuous_ofReal.comp_continuousOn hφ
  have hE : ∀ μ : ℝ, ContinuousOn (fun s => Complex.exp (Complex.I * ((μ * φ s : ℝ) : ℂ))) K := by
    intro μ
    exact Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hφ)))
  have hFc : ∀ μ : ℝ, ContinuousOn (fun s => g s * Complex.exp (Complex.I * ((μ * φ s : ℝ) : ℂ))) K :=
    fun μ => hg.mul (hE μ)
  have hF'c : ∀ μ : ℝ, ContinuousOn (fun s => Complex.I * φ s * g s *
      Complex.exp (Complex.I * ((μ * φ s : ℝ) : ℂ))) K :=
    fun μ => ((continuousOn_const.mul hφc).mul hg).mul (hE μ)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun s => Complex.I * (φ s : ℂ) * g s) ((continuousOn_const.mul hφc).mul hg)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict K) (x₀ := μ₀)
    (F := fun μ s => g s * Complex.exp (Complex.I * ((μ * φ s : ℝ) : ℂ)))
    (F' := fun μ s => Complex.I * φ s * g s * Complex.exp (Complex.I * ((μ * φ s : ℝ) : ℂ)))
    (bound := fun _ => M) Filter.univ_mem
    (Eventually.of_forall fun μ => (hFc μ).aestronglyMeasurable measurableSet_Icc)
    ((hFc μ₀).integrableOn_compact isCompact_Icc)
    ((hF'c μ₀).aestronglyMeasurable measurableSet_Icc)
    (ae_restrict_of_forall_mem measurableSet_Icc fun s hs μ _ => by
      rw [norm_mul, show Complex.I * ((μ * φ s : ℝ) : ℂ) = ((μ * φ s : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hM s hs)
    (integrable_const M)
    (ae_restrict_of_forall_mem measurableSet_Icc fun s hs μ _ => by
      have := (c03s_aux_hasDerivAt_expI (φ s) μ).const_mul (g s)
      convert this using 1; ring)
  exact this.2

theorem c03s_aux_h_smooth (p : ℝ) (_hp : 0 < p) : ContDiffOn ℝ (⊤ : ℕ∞) (c03_h p) (Ioi 0) := by
  unfold c03_h
  exact contDiffOn_id.sub ((contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)).div_const _)

theorem c03s_aux_K_sub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by
  simp only [mem_Ioi]; linarith [hx.1]

/-- Part 1 of `c03_sp_J_parameter`. -/
theorem c03s_aux_J_single (p : ℝ) (hp : 0 < p) (c : ℝ → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcs : tsupport c ⊆ Ioo (1 / 2) 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
        c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) ∧
    (∀ j : ℕ, ∀ μ : ℝ, iteratedDeriv j (fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
        c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) μ =
      ∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ j * c s *
        Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) ∧
    ∀ j : ℕ, ∀ μ : ℝ, HasDerivAt (fun μ : ℝ => ∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ j *
        c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)))
      (∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ (j + 1) * c s *
        Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) μ := by
  have hc0 : ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → c s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport (fun h => hs (hcs h))
  have hhc : ContinuousOn (c03_h p) (Icc (1 / 2 : ℝ) 2) :=
    (c03s_aux_h_smooth p hp).continuousOn.mono c03s_aux_K_sub
  have hJ : ∀ j : ℕ, ∀ μ : ℝ, HasDerivAt (fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
      (Complex.I * (c03_h p s : ℂ)) ^ j * c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)))
      (∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ (j + 1) * c s *
        Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) μ := by
    intro j μ
    have hz : ∀ (k : ℕ) (μ : ℝ) (s : ℝ), s ∉ Ioo (1 / 2 : ℝ) 2 → (Complex.I * (c03_h p s : ℂ)) ^ k *
        c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)) = 0 := by
      intro k μ s hs; rw [hc0 s hs]; ring
    have hfun : (fun μ : ℝ => ∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ j * c s *
        Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) = fun μ : ℝ =>
        ∫ s in Icc (1 / 2 : ℝ) 2, ((Complex.I * (c03_h p s : ℂ)) ^ j * c s) *
          Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)) := by
      funext μ; exact c03s_aux_Ioi_Icc (hz j μ)
    rw [hfun, c03s_aux_Ioi_Icc (hz (j + 1) μ)]
    have hg : ContinuousOn (fun s => (Complex.I * (c03_h p s : ℂ)) ^ j * c s) (Icc (1 / 2 : ℝ) 2) :=
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hhc)).pow j).mul
        hc.continuous.continuousOn
    convert c03s_aux_mu_deriv hg hhc μ using 2
    funext s; ring
  have hit : ∀ j : ℕ, iteratedDeriv j (fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
      c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) = fun μ =>
      ∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ j * c s *
        Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)) := by
    intro j
    induction j with
    | zero => funext μ; simp
    | succ j ih => rw [iteratedDeriv_succ, ih]; funext μ; exact (hJ j μ).deriv
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun j μ => by rw [hit j], hJ⟩
  rw [hit m]; exact fun μ => (hJ m μ).differentiableAt

/-- `(y,μ) ↦ ∫₀^∞ c(y,s) e^{iμh(s)} ds` is smooth for a smooth family vanishing off `(1/2,2)`. -/
theorem c03s_aux_J_joint (p : ℝ) (hp : 0 < p) {V : Set ℝ} {c : ℝ → ℝ → ℂ} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry c) (V ×ˢ univ))
    (hc0 : ∀ y ∈ V, ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → c y s = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => ∫ s in Ioi (0 : ℝ),
      c x.1 s * Complex.exp (Complex.I * ((x.2 * c03_h p s : ℝ) : ℂ))) (V ×ˢ univ) := by
  have hhs := c03s_aux_h_smooth p hp
  have hEs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : (ℝ × ℝ) × ℝ =>
      Complex.exp (Complex.I * ((z.1.2 * c03_h p z.2 : ℝ) : ℂ))) ((V ×ˢ univ) ×ˢ Icc (1 / 2 : ℝ) 2) := by
    have : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : (ℝ × ℝ) × ℝ => z.1.2 * c03_h p z.2)
        ((V ×ˢ univ) ×ˢ Icc (1 / 2 : ℝ) 2) :=
      contDiffOn_fst.snd.mul (hhs.comp contDiffOn_snd (fun z hz => c03s_aux_K_sub hz.2))
    exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn this))).cexp
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : (ℝ × ℝ) × ℝ => Function.uncurry c (z.1.1, z.2))
      ((V ×ˢ univ) ×ˢ Icc (1 / 2 : ℝ) 2) :=
    hcd.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd) (fun z hz => ⟨hz.1.1, trivial⟩)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry fun (x : ℝ × ℝ) (s : ℝ) =>
      c x.1 s * Complex.exp (Complex.I * ((x.2 * c03_h p s : ℝ) : ℂ)))
      ((V ×ˢ univ) ×ˢ Icc (1 / 2 : ℝ) 2) := h1.mul hEs
  have := hF.parametric_integral (μ := volume) (hV.prod isOpen_univ) isCompact_Icc subset_rfl
    (by simp)
  refine this.congr fun x hx => c03s_aux_Ioi_Icc (fun s hs => ?_)
  rw [hc0 x.1 hx.1 s hs, zero_mul]

/-- Differentiation in the family parameter. -/
theorem c03s_aux_J_y (p : ℝ) (hp : 0 < p) {V : Set ℝ} {c : ℝ → ℝ → ℂ} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry c) (V ×ˢ univ))
    (hc0 : ∀ y ∈ V, ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → c y s = 0) {y : ℝ} (hy : y ∈ V) (μ : ℝ) :
    HasDerivAt (fun y' => ∫ s in Ioi (0 : ℝ),
          c y' s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)))
        (∫ s in Ioi (0 : ℝ), deriv (fun y' => c y' s) y *
          Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) y := by
  set E : ℝ → ℂ := fun s => Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)) with hE
  have hhs := c03s_aux_h_smooth p hp
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry fun (y : ℝ) (s : ℝ) => c y s * E s)
      (V ×ˢ Icc (1 / 2 : ℝ) 2) := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry c) (V ×ˢ Icc (1 / 2 : ℝ) 2) :=
      hcd.mono (prod_mono subset_rfl (subset_univ _))
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => E z.2) (V ×ˢ Icc (1 / 2 : ℝ) 2) := by
      have : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => μ * c03_h p z.2) (V ×ˢ Icc (1 / 2 : ℝ) 2) :=
        contDiffOn_const.mul (hhs.comp contDiffOn_snd (fun z hz => c03s_aux_K_sub hz.2))
      exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn this))).cexp
    exact h1.mul h2
  have hf1 : ContDiffOn ℝ 1 (Function.uncurry fun (y : ℝ) (s : ℝ) => c y s * E s)
      (V ×ˢ Icc (1 / 2 : ℝ) 2) := hf.of_le (by exact_mod_cast le_top)
  have hfd := hasFDerivAt_integral_of_contDiffOn (μ := volume) (hV.mem_nhds hy) isCompact_Icc
    (by simp) subset_rfl hf1
  have hcont : ContinuousOn (fun s => fderiv ℝ (fun y' => c y' s * E s) y) (Icc (1 / 2 : ℝ) 2) := by
    have h0 : ContDiffOn ℝ (0 + 1 : WithTop ℕ∞) (Function.uncurry fun (y : ℝ) (s : ℝ) => c y s * E s)
      (V ×ˢ Icc (1 / 2 : ℝ) 2) := by rw [zero_add]; exact hf1
    have h3 : ContinuousOn (fun x : ℝ × ℝ => fderiv ℝ (fun y' => c y' x.2 * E x.2) x.1)
        (V ×ˢ Icc (1 / 2 : ℝ) 2) := (h0.fderiv_left hV).continuousOn
    exact h3.comp (f := fun s : ℝ => (y, s)) (Continuous.prodMk continuous_const continuous_id).continuousOn
      (fun s hs => (⟨hy, hs⟩ : (y, s) ∈ V ×ˢ Icc (1 / 2 : ℝ) 2))
  have hint := hcont.integrableOn_compact (μ := volume) isCompact_Icc
  have hd := hfd.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hint] at hd
  have hcy : ∀ s, DifferentiableAt ℝ (fun y' => c y' s) y := by
    intro s
    have := (hcd.contDiffAt ((hV.prod isOpen_univ).mem_nhds
      (show (y, s) ∈ V ×ˢ (univ : Set ℝ) from ⟨hy, trivial⟩))).differentiableAt (by simp)
    exact this.comp y ((hasDerivAt_id y).prodMk (hasDerivAt_const y s)).differentiableAt
  have heq1 : ∀ s, fderiv ℝ (fun y' => c y' s * E s) y 1 = deriv (fun y' => c y' s) y * E s := by
    intro s
    rw [fderiv_apply_one_eq_deriv, deriv_mul_const (hcy s)]
  simp_rw [heq1] at hd
  have hev : (fun y' => ∫ s in Ioi (0 : ℝ), c y' s * E s) =ᶠ[𝓝 y]
      fun y' => ∫ s in Icc (1 / 2 : ℝ) 2, c y' s * E s := by
    filter_upwards [hV.mem_nhds hy] with z hz using
      c03s_aux_Ioi_Icc (fun s hs => by rw [hc0 z hz s hs, zero_mul])
  have hz' : ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → deriv (fun y' => c y' s) y * E s = 0 := by
    intro s hs
    have : (fun y' => c y' s) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hy] with z hz using hc0 z hz s hs
    rw [this.deriv_eq]; simp
  rw [c03s_aux_Ioi_Icc hz']
  exact hd.congr_of_eventuallyEq hev

/-- Blueprint: lem:c03_sp_J_parameter.  `J(μ;c) = ∫₀^∞ c(s) e^{iμh(s)} ds` is smooth in `μ ∈ ℝ` with
`∂_μ^j J = ∫ (ih)^j c e^{iμh}`; for a smooth family `c(y,·)` with locally uniform compact support in
`(½,2)` (`y ∈ V` open), `(y,μ) ↦ J(μ;c(y,·))` is smooth on `V × ℝ`, `∂_y` passes under the integral,
and `(y,μ) ↦ ρ(μ;c(y,·))` is smooth on `V × (0,∞)` with partial derivatives
`∂_y ρ = ρ(μ;∂_y c)` and `∂_μ ρ`. -/
theorem c03_sp_J_parameter (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      ContDiff ℝ (⊤ : ℕ∞) (fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
        c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) ∧
      ∀ j : ℕ, ∀ μ : ℝ, iteratedDeriv j (fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
          c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) μ =
        ∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ j * c s *
          Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) ∧
    ∀ (V : Set ℝ) (c : ℝ → ℝ → ℂ), IsOpen V →
      ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry c) (V ×ˢ univ) →
      (∀ y₀ ∈ V, ∃ ε, 0 < ε ∧ ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo (1 / 2) 2 ∧
        ∀ y ∈ V, |y - y₀| < ε → ∀ s ∉ K, c y s = 0) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => ∫ s in Ioi (0 : ℝ),
        c x.1 s * Complex.exp (Complex.I * ((x.2 * c03_h p s : ℝ) : ℂ))) (V ×ˢ univ) ∧
      (∀ y ∈ V, ∀ μ : ℝ, HasDerivAt (fun y' => ∫ s in Ioi (0 : ℝ),
          c y' s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)))
        (∫ s in Ioi (0 : ℝ), deriv (fun y' => c y' s) y *
          Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) y) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => c03_sp_rho p x.2 (c x.1)) (V ×ˢ Ioi 0) ∧
      ∀ y ∈ V, ∀ μ : ℝ, 0 < μ →
        HasFDerivAt (fun x : ℝ × ℝ => c03_sp_rho p x.2 (c x.1))
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
              (c03_sp_rho p μ (fun s => deriv (fun y' => c y' s) y)) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
              (deriv (fun μ' => c03_sp_rho p μ' (c y)) μ)) (y, μ) := by
  refine ⟨fun c hc hcs => ⟨(c03s_aux_J_single p hp c hc hcs).1, (c03s_aux_J_single p hp c hc hcs).2.1⟩,
    fun V c hV hcd hsupp => ?_⟩
  have hc0 : ∀ y ∈ V, ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → c y s = 0 := by
    intro y hy s hs
    obtain ⟨ε, hε, K', -, hK', hz⟩ := hsupp y hy
    exact hz y hy (by simpa using hε) s (fun h => hs (hK' h))
  set E : ℝ → ℝ → ℂ := fun μ s => Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)) with hE
  have hJs := c03s_aux_J_joint p hp hV hcd hc0
  have hJy := fun y (hy : y ∈ V) μ => c03s_aux_J_y p hp hV hcd hc0 hy μ
  -- (3) smoothness of `ρ`
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun μ : ℝ => Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (Real.sqrt (p * μ / (2 * π)) : ℂ) * Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))))
      (Ioi 0) := by
    have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun μ : ℝ => Real.sqrt (p * μ / (2 * π))) (Ioi 0) :=
      ((contDiffOn_const.mul contDiffOn_id).div_const _).sqrt (fun μ hμ => by
        have h : (0 : ℝ) < μ := hμ
        exact (div_pos (mul_pos hp h) (by positivity)).ne')
    have he : ContDiff ℝ (⊤ : ℕ∞) (fun μ : ℝ => Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)))) :=
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const))).neg).cexp
    exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hs)).mul he.contDiffOn
  have hc1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => c x.1 1) (V ×ˢ Ioi 0) :=
    hcd.comp (f := fun x : ℝ × ℝ => (x.1, (1 : ℝ))) (contDiffOn_fst.prodMk contDiffOn_const)
      (fun z hz => ⟨hz.1, trivial⟩)
  have hrho : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => c03_sp_rho p x.2 (c x.1)) (V ×ˢ Ioi 0) := by
    have h1 := (hA.comp contDiffOn_snd (fun z (hz : z ∈ V ×ˢ Ioi (0 : ℝ)) => hz.2)).mul
      (hJs.mono (prod_mono subset_rfl (subset_univ _)))
    exact (h1.sub hc1).congr fun x hx => by simp [c03_sp_rho]
  refine ⟨hJs, hJy, hrho, fun y hy μ hμ => ?_⟩
  -- (4) the total derivative
  have hopen : IsOpen (V ×ˢ Ioi (0 : ℝ)) := hV.prod isOpen_Ioi
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => c03_sp_rho p x.2 (c x.1)) (y, μ) :=
    (hrho.contDiffAt (hopen.mem_nhds (show (y, μ) ∈ V ×ˢ Ioi (0 : ℝ) from ⟨hy, hμ⟩))).differentiableAt (by simp)
  have hF := hdiff.hasFDerivAt
  set L := fderiv ℝ (fun x : ℝ × ℝ => c03_sp_rho p x.2 (c x.1)) (y, μ)
  -- partial derivative in `y`
  have hpy : HasDerivAt (fun y' => c03_sp_rho p μ (c y')) (L (1, 0)) y := by
    exact hF.comp_hasDerivAt y ((hasDerivAt_id y).prodMk (hasDerivAt_const y μ))
  have hpy' : HasDerivAt (fun y' => c03_sp_rho p μ (c y'))
      (c03_sp_rho p μ (fun s => deriv (fun y' => c y' s) y)) y := by
    have hc1y : HasDerivAt (fun y' => c y' 1) (deriv (fun y' => c y' 1) y) y := by
      have := (hcd.contDiffAt ((hV.prod isOpen_univ).mem_nhds
        (show (y, (1 : ℝ)) ∈ V ×ˢ (univ : Set ℝ) from ⟨hy, trivial⟩))).differentiableAt (by simp)
      exact (this.comp y ((hasDerivAt_id y).prodMk (hasDerivAt_const y (1 : ℝ))).differentiableAt).hasDerivAt
    have := ((hJy y hy μ).const_mul (Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (Real.sqrt (p * μ / (2 * π)) : ℂ) * Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))))).sub
      hc1y
    exact this
  have hpm : HasDerivAt (fun μ' => c03_sp_rho p μ' (c y)) (L (0, 1)) μ := by
    exact hF.comp_hasDerivAt μ ((hasDerivAt_const μ y).prodMk (hasDerivAt_id μ))
  have key : L = (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
        (c03_sp_rho p μ (fun s => deriv (fun y' => c y' s) y)) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (deriv (fun μ' => c03_sp_rho p μ' (c y)) μ) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    calc L v = L (v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ))) := by rw [← hv]
      _ = v.1 • L (1, 0) + v.2 • L (0, 1) := by rw [map_add, map_smul, map_smul]
      _ = _ := by
        rw [← hpy'.unique hpy, ← hpm.deriv]
        simp
  rw [← key]; exact hF

theorem c03s_aux_Ioi_interval {f : ℝ → ℂ} (hf : ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → f s = 0) :
    ∫ s in Ioi (0 : ℝ), f s = ∫ s in (1 / 4 : ℝ)..3, f s := by
  rw [c03s_aux_Ioi_Icc hf, intervalIntegral.integral_of_le (by norm_num)]
  have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioc (1 / 4) 3 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub
    (fun s hs => hf s (fun h => hs.2 (Ioo_subset_Icc_self h)))).symm

theorem c03s_aux_h_deriv (p : ℝ) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (c03_h p) (1 - x ^ p) x := by
  have hr := Real.hasDerivAt_rpow_const (p := p + 1) (Or.inl hx.ne')
  have h := (hasDerivAt_id x).sub (hr.div_const (p + 1))
  have hp1' : p + 1 ≠ 0 := by linarith
  unfold c03_h
  exact h.congr_deriv (by rw [add_sub_cancel_right]; field_simp)

/-- Blueprint: lem:c03_sp_euler_identity.  `μ ∂_μ ρ(μ;c) = ρ(μ;Tc)` for `c ∈ C_c^∞((½,2))`. -/
theorem c03_sp_euler_identity (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c : ℝ → ℂ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : tsupport c ⊆ Ioo (1 / 2) 2) (μ : ℝ) (hμ : 0 < μ) :
    (μ : ℂ) * deriv (fun μ => c03_sp_rho p μ c) μ = c03_sp_rho p μ (c03_sp_T p c) := by
  obtain ⟨-, -, -, -, hqf, hq1v, -, hqs, -⟩ := c03_sp_q_extension p hp hp1
  obtain ⟨hTs, hTsupp, hT1⟩ := (c03_sp_T_bounds p hp hp1).1 c hc hcs
  have hc0 : ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → c s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport (fun h => hs (hcs h))
  have hT0 : ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → c03_sp_T p c s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport (fun h => hs (hTsupp h))
  set qc : ℝ → ℂ := fun s => ((c03_sp_q p s : ℝ) : ℂ) with hqc
  set u : ℝ → ℂ := fun s => c s * qc s with hu
  have hus : ContDiff ℝ (⊤ : ℕ∞) u := by
    rw [contDiff_iff_contDiffAt]
    intro s
    by_cases hs : s ∈ tsupport c
    · have h0 : 0 < s := by linarith [(hcs hs).1]
      exact hc.contDiffAt.mul ((Complex.ofRealCLM.contDiff.comp_contDiffOn hqs).contDiffAt
        (Ioi_mem_nhds h0))
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport c).isOpen_compl.mem_nhds hs] with z hz
      simp [hu, image_eq_zero_of_notMem_tsupport hz]
  have hu0 : ∀ s, s ∉ Ioo (1 / 2 : ℝ) 2 → deriv u s = 0 := by
    intro s hs
    have : c03_sp_T p c s = c s / 2 - deriv u s := rfl
    rw [hT0 s hs, hc0 s hs] at this
    linear_combination this
  set e : ℝ → ℂ := fun s => Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)) with he
  -- the `μ`-derivative of `J`
  have hJ : HasDerivAt (fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
      c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)))
      (∫ s in Ioi (0 : ℝ), Complex.I * (c03_h p s : ℂ) * c s * e s) μ := by
    have := (c03s_aux_J_single p hp c hc hcs).2.2 0 μ
    have e1 : (fun μ : ℝ => ∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ 0 * c s *
        Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) = fun μ : ℝ => ∫ s in Ioi (0 : ℝ),
        c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)) := by
      funext μ; congr 1; funext s; rw [pow_zero, one_mul]
    have e2 : (∫ s in Ioi (0 : ℝ), (Complex.I * (c03_h p s : ℂ)) ^ (0 + 1) * c s *
        Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) =
        ∫ s in Ioi (0 : ℝ), Complex.I * (c03_h p s : ℂ) * c s * e s := by
      congr 1; funext s; rw [zero_add, pow_one]
    rwa [e1, e2] at this
  -- the normalizing factor
  have hX0 : 0 < p * μ / (2 * π) := by positivity
  set A : ℝ → ℂ := fun μ => Complex.exp (Complex.I * (π / 4 : ℝ)) *
    (Real.sqrt (p * μ / (2 * π)) : ℂ) * Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))) with hA
  have hsq : HasDerivAt (fun μ : ℝ => Real.sqrt (p * μ / (2 * π)))
      (p / (2 * π) / (2 * Real.sqrt (p * μ / (2 * π)))) μ := by
    have h1 : HasDerivAt (fun μ : ℝ => p * μ / (2 * π)) (p / (2 * π)) μ := by
      simpa using ((hasDerivAt_id μ).const_mul p).div_const (2 * π)
    exact h1.sqrt hX0.ne'
  have hE1 : HasDerivAt (fun μ : ℝ => Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))))
      (-(Complex.I * c03_h p 1) * Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)))) μ := by
    have h1 : HasDerivAt (fun μ : ℝ => -(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)))
        (-(Complex.I * ((1 * c03_h p 1 : ℝ) : ℂ))) μ :=
      ((((hasDerivAt_id μ).mul_const (c03_h p 1)).ofReal_comp).const_mul Complex.I).neg
    convert h1.cexp using 1; push_cast; ring
  set E1 : ℂ := Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))) with hE1def
  set dS : ℂ := (((p / (2 * π) / (2 * Real.sqrt (p * μ / (2 * π)))) : ℝ) : ℂ) with hdS
  have hAd : HasDerivAt A (Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (dS * E1 + (Real.sqrt (p * μ / (2 * π)) : ℂ) * (-(Complex.I * c03_h p 1) * E1))) μ := by
    have := ((hsq.ofReal_comp.mul hE1).const_mul (Complex.exp (Complex.I * (π / 4 : ℝ))))
    convert this using 1
    funext μ; simp only [hA, Pi.mul_apply, mul_assoc]
  have hrho := (hAd.mul hJ).sub_const (c 1)
  rw [show deriv (fun μ => c03_sp_rho p μ c) μ = _ from hrho.deriv]
  -- continuity on `[1/4,3]`
  have hpos : ∀ s ∈ uIcc (1 / 4 : ℝ) 3, 0 < s := fun s hs => by
    rw [uIcc_of_le (by norm_num)] at hs; linarith [hs.1]
  have hhc : ContinuousOn (fun s => ((c03_h p s : ℝ) : ℂ)) (uIcc (1 / 4 : ℝ) 3) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((c03s_aux_h_smooth p hp).continuousOn.mono (fun s hs => hpos s hs))
  have hec : ContinuousOn e (uIcc (1 / 4 : ℝ) 3) := by
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    have : ContinuousOn (fun s => ((μ : ℂ) * ((c03_h p s : ℝ) : ℂ))) (uIcc (1 / 4 : ℝ) 3) :=
      continuousOn_const.mul hhc
    refine this.congr fun s _ => ?_
    push_cast; ring
  have hcc : ContinuousOn c (uIcc (1 / 4 : ℝ) 3) := hc.continuous.continuousOn
  have hduc : ContinuousOn (deriv u) (uIcc (1 / 4 : ℝ) 3) :=
    (hus.continuous_deriv (by exact_mod_cast le_top)).continuousOn
  -- conversions to interval integrals
  have cJc : (∫ s in Ioi (0 : ℝ), c s * e s) = ∫ s in (1 / 4 : ℝ)..3, c s * e s :=
    c03s_aux_Ioi_interval (fun s hs => by simp [hc0 s hs])
  have cJh : (∫ s in Ioi (0 : ℝ), Complex.I * (c03_h p s : ℂ) * c s * e s) =
      ∫ s in (1 / 4 : ℝ)..3, Complex.I * (c03_h p s : ℂ) * c s * e s :=
    c03s_aux_Ioi_interval (fun s hs => by simp [hc0 s hs])
  have cJT : (∫ s in Ioi (0 : ℝ), c03_sp_T p c s * e s) =
      ∫ s in (1 / 4 : ℝ)..3, (c s / 2 * e s - deriv u s * e s) := by
    rw [c03s_aux_Ioi_interval (fun s hs => by simp [hT0 s hs])]
    congr 1; funext s; simp only [c03_sp_T]; ring
  have iI1 : IntervalIntegrable (fun s => c s * e s) volume (1 / 4 : ℝ) 3 :=
    (hcc.mul hec).intervalIntegrable
  have iI2 : IntervalIntegrable (fun s => deriv u s * e s) volume (1 / 4 : ℝ) 3 :=
    (hduc.mul hec).intervalIntegrable
  have iI3 : IntervalIntegrable (fun s => Complex.I * (c03_h p s : ℂ) * c s * e s) volume
      (1 / 4 : ℝ) 3 := (((continuousOn_const.mul hhc).mul hcc).mul hec).intervalIntegrable
  -- F1
  have F1 : (∫ s in (1 / 4 : ℝ)..3, (c s / 2 * e s - deriv u s * e s)) =
      (∫ s in (1 / 4 : ℝ)..3, c s * e s) / 2 - ∫ s in (1 / 4 : ℝ)..3, deriv u s * e s := by
    rw [intervalIntegral.integral_sub (by simpa [div_mul_eq_mul_div] using iI1.div_const 2) iI2]
    congr 1
    rw [← intervalIntegral.integral_div]; congr 1; funext s; ring
  -- F2: integration by parts
  have hvd : ∀ s ∈ Ioo (min (1 / 4 : ℝ) 3) (max (1 / 4 : ℝ) 3), HasDerivAt e
      (Complex.I * μ * ((1 - s ^ p : ℝ) : ℂ) * e s) s := by
    intro s hs
    have hs0 : 0 < s := by
      have : min (1 / 4 : ℝ) 3 = 1 / 4 := by norm_num
      rw [this] at hs; linarith [hs.1]
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * ((μ * c03_h p s : ℝ) : ℂ))
        (Complex.I * ((μ * (1 - s ^ p) : ℝ) : ℂ)) s :=
      (((c03s_aux_h_deriv p hp hs0).const_mul μ).ofReal_comp).const_mul Complex.I
    convert h1.cexp using 1; simp only [he]; push_cast; ring
  have hud : ∀ s ∈ Ioo (min (1 / 4 : ℝ) 3) (max (1 / 4 : ℝ) 3), HasDerivAt u (deriv u s) s :=
    fun s _ => (hus.differentiable (by simp) s).hasDerivAt
  have hv'c : ContinuousOn (fun s => Complex.I * μ * ((1 - s ^ p : ℝ) : ℂ) * e s)
      (uIcc (1 / 4 : ℝ) 3) := by
    refine (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_)).mul hec
    exact continuousOn_const.sub (ContinuousOn.rpow_const continuousOn_id
      (fun s hs => Or.inl (hpos s hs).ne'))
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hus.continuous.continuousOn hec hud hvd hduc.intervalIntegrable hv'c.intervalIntegrable
  have hu3 : u 3 = 0 := by
    show c 3 * qc 3 = 0; rw [hc0 3 (fun h => by linarith [h.2]), zero_mul]
  have hu4 : u (1 / 4) = 0 := by
    show c (1 / 4) * qc (1 / 4) = 0; rw [hc0 (1 / 4) (fun h => by linarith [h.1]), zero_mul]
  rw [hu3, hu4, zero_mul, zero_mul, sub_zero, zero_sub] at ibp
  have hqh : ∀ s, 0 < s → ((c03_sp_q p s : ℝ) : ℂ) * ((1 - s ^ p : ℝ) : ℂ) =
      ((c03_h p s : ℝ) : ℂ) - ((c03_h p 1 : ℝ) : ℂ) := by
    intro s hs
    rcases eq_or_ne s 1 with h | h
    · subst h; simp [hq1v]
    · have hne : 1 - s ^ p ≠ 0 := by
        intro h0
        have : s ^ p = 1 := by linarith
        rcases lt_or_gt_of_ne h with h' | h'
        · linarith [Real.rpow_lt_one hs.le h' hp]
        · linarith [Real.one_lt_rpow h' hp]
      rw [hqf s hs h, ← Complex.ofReal_mul, div_mul_cancel₀ _ hne]; push_cast; ring
  have hL : (∫ s in (1 / 4 : ℝ)..3, u s * (Complex.I * μ * ((1 - s ^ p : ℝ) : ℂ) * e s)) =
      μ * (∫ s in (1 / 4 : ℝ)..3, Complex.I * (c03_h p s : ℂ) * c s * e s) -
        Complex.I * μ * (c03_h p 1 : ℂ) * ∫ s in (1 / 4 : ℝ)..3, c s * e s := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (iI3.const_mul _) (iI1.const_mul _)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have := hqh s (hpos s hs)
    simp only [hu, hqc]
    linear_combination (Complex.I * μ * c s * e s) * this
  rw [hL] at ibp
  -- F3: the normalizing factor
  have hsX : Real.sqrt (p * μ / (2 * π)) ^ 2 = p * μ / (2 * π) := Real.sq_sqrt hX0.le
  have hsX0 : Real.sqrt (p * μ / (2 * π)) ≠ 0 := (Real.sqrt_pos.2 hX0).ne'
  have F3 : (μ : ℂ) * dS = (Real.sqrt (p * μ / (2 * π)) : ℂ) / 2 := by
    have h1 : μ * (p / (2 * π) / (2 * Real.sqrt (p * μ / (2 * π)))) =
        Real.sqrt (p * μ / (2 * π)) ^ 2 / (2 * Real.sqrt (p * μ / (2 * π))) := by
      rw [hsX]; ring
    have h2 : Real.sqrt (p * μ / (2 * π)) ^ 2 / (2 * Real.sqrt (p * μ / (2 * π))) =
        Real.sqrt (p * μ / (2 * π)) / 2 := by
      field_simp
    rw [hdS, ← Complex.ofReal_mul, h1, h2]; push_cast; ring
  -- assemble
  have hT1' : c03_sp_T p c 1 = 0 := hT1
  have cJc' : (∫ s in Ioi (0 : ℝ), c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) =
      ∫ s in (1 / 4 : ℝ)..3, c s * e s := cJc
  show _ = A μ * (∫ s in Ioi (0 : ℝ), c03_sp_T p c s * e s) - c03_sp_T p c 1
  rw [hT1', cJT, F1, cJc', cJh]
  simp only [hA]
  linear_combination (Complex.exp (Complex.I * (π / 4 : ℝ)) * E1 *
      ∫ s in (1 / 4 : ℝ)..3, c s * e s) * F3 +
    (Complex.exp (Complex.I * (π / 4 : ℝ)) * (Real.sqrt (p * μ / (2 * π)) : ℂ) * E1) * ibp

/-- `μ ↦ ρ(μ;c)` is smooth on `(0,∞)`. -/
theorem c03s_aux_rho_smooth (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c : ℝ → ℂ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : tsupport c ⊆ Ioo (1 / 2) 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun μ => c03_sp_rho p μ c) (Ioi 0) := by
  have hJ := ((c03_sp_J_parameter p hp hp1).1 c hc hcs).1
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun μ : ℝ => Real.sqrt (p * μ / (2 * π))) (Ioi 0) :=
    ((contDiffOn_const.mul contDiffOn_id).div_const _).sqrt (fun μ hμ => by
      have h : (0 : ℝ) < μ := hμ
      exact (div_pos (mul_pos hp h) (by positivity)).ne')
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun μ : ℝ => Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)))) :=
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const))).neg).cexp
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun μ : ℝ => Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (Real.sqrt (p * μ / (2 * π)) : ℂ) * Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))))
      (Ioi 0) :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hs)).mul he.contDiffOn
  exact ((hA.mul hJ.contDiffOn).sub contDiffOn_const)

/-- Blueprint: lem:c03_sp_euler (prefixed copy of `GSQG.c03_sp_euler`). -/
theorem c03s_c03_sp_euler (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_q p) (Ioi 0) ∧ deriv (c03_sp_q p) 1 = 1 / 2 ∧
    (∀ k : ℕ, ∃ C, 0 < C ∧ ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      c03_Ck_normR k univ (c03_sp_T p c) ≤ C * c03_Ck_normR (k + 1) univ c) ∧
    ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      tsupport (c03_sp_T p c) ⊆ Ioo (1 / 2) 2 ∧ c03_sp_T p c 1 = 0 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun μ => c03_sp_rho p μ c) (Ioi 0) ∧
      ∀ μ : ℝ, 0 < μ → (μ : ℂ) * deriv (fun μ => c03_sp_rho p μ c) μ = c03_sp_rho p μ (c03_sp_T p c) := by
  obtain ⟨-, -, -, -, -, -, hq1d, hqs, -⟩ := c03_sp_q_extension p hp hp1
  have hT := c03_sp_T_bounds p hp hp1
  exact ⟨hqs, hq1d, hT.2, fun c hc hcs => ⟨(hT.1 c hc hcs).2.1, (hT.1 c hc hcs).2.2,
    c03s_aux_rho_smooth p hp hp1 c hc hcs, fun μ hμ => c03_sp_euler_identity p hp hp1 c hc hcs μ hμ⟩⟩

theorem c03s_aux_hasDerivAt_of_cdo {f : ℝ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0)) {x : ℝ}
    (hx : 0 < x) : HasDerivAt f (deriv f x) x :=
  ((hf.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)).hasDerivAt

theorem c03s_aux_contDiffAt_of_cdo {f : ℝ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0)) {x : ℝ}
    (hx : 0 < x) (n : ℕ) : ContDiffAt ℝ n f x :=
  (hf.contDiffAt (Ioi_mem_nhds hx)).of_le (by exact_mod_cast le_top)

/-- Chain rule for a dilation, all orders, on `(0,∞)`. -/
theorem c03s_aux_iter_dil {a : ℝ → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ioi 0)) {L : ℝ} (hL : 0 < L)
    (k : ℕ) : ∀ s, 0 < s → iteratedDeriv k (fun s => a (L * s)) s =
      (L : ℂ) ^ k * iteratedDeriv k a (L * s) := by
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    have hLs : 0 < L * s := mul_pos hL hs
    have hev : iteratedDeriv k (fun s => a (L * s)) =ᶠ[𝓝 s]
        fun s => (L : ℂ) ^ k * iteratedDeriv k a (L * s) := by
      filter_upwards [Ioi_mem_nhds hs] with z hz using ih z hz
    have hl : HasDerivAt (fun s : ℝ => L * s) L s := by
      simpa using (hasDerivAt_id s).const_mul L
    have hd := ((c03s_aux_hasDerivAt_iteratedDeriv ha k hLs).scomp s hl).const_mul ((L : ℂ) ^ k)
    rw [iteratedDeriv_succ, hev.deriv_eq]
    refine hd.deriv.trans ?_
    rw [Complex.real_smul]; ring

/-- `x ∂_x` commutes with derivatives: `∂^k(x a') = x a^{(k+1)} + k a^{(k)}` on `(0,∞)`. -/
theorem c03s_aux_iter_xderiv {a : ℝ → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ioi 0)) (k : ℕ) :
    ∀ x : ℝ, 0 < x → iteratedDeriv k (fun x : ℝ => (x : ℂ) * deriv a x) x =
      (x : ℂ) * iteratedDeriv (k + 1) a x + (k : ℂ) * iteratedDeriv k a x := by
  induction k with
  | zero => intro x _; simp [iteratedDeriv_one]
  | succ k ih =>
    intro x hx
    have hev : iteratedDeriv k (fun x : ℝ => (x : ℂ) * deriv a x) =ᶠ[𝓝 x]
        fun x => (x : ℂ) * iteratedDeriv (k + 1) a x + (k : ℂ) * iteratedDeriv k a x := by
      filter_upwards [Ioi_mem_nhds hx] with z hz using ih z hz
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have hd := (h1.mul (c03s_aux_hasDerivAt_iteratedDeriv ha (k + 1) hx)).add
      ((c03s_aux_hasDerivAt_iteratedDeriv ha k hx).const_mul (k : ℂ))
    rw [iteratedDeriv_succ, hev.deriv_eq]
    refine hd.deriv.trans ?_
    push_cast; ring

/-- A function vanishing on `(0,1]` and smooth on `(0,∞)` has all derivatives zero on `(0,1]`. -/
theorem c03s_aux_iter_zero {a : ℝ → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ioi 0))
    (h0 : ∀ ξ ∈ Ioc (0 : ℝ) 1, a ξ = 0) (k : ℕ) : ∀ ξ ∈ Ioc (0 : ℝ) 1, iteratedDeriv k a ξ = 0 := by
  have hopen : ∀ ξ ∈ Ioo (0 : ℝ) 1, iteratedDeriv k a ξ = 0 := by
    intro ξ hξ
    have hev : a =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with z hz using h0 z ⟨hz.1, hz.2.le⟩
    rw [(hev.iteratedDeriv k).eq_of_nhds]; simp
  intro ξ hξ
  rcases eq_or_lt_of_le hξ.2 with h | h
  · subst h
    have hc : ContinuousAt (iteratedDeriv k a) 1 :=
      (c03s_aux_hasDerivAt_iteratedDeriv ha k one_pos).continuousAt
    have hlim : Tendsto (iteratedDeriv k a) (𝓝[<] 1) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with z hz
      exact (hopen z ⟨by linarith [hz.1], hz.2⟩).symm
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  · exact hopen ξ ⟨hξ.1, h⟩

/-- Smoothness of `𝔈a` and the formula for its derivatives. -/
theorem c03s_aux_frakE_formula (p m : ℝ) {a : ℝ → ℂ} (has : ContDiffOn ℝ (⊤ : ℕ∞) a (Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_frakE p m a) (Ioi 0) ∧
    ∀ i : ℕ, ∀ x, 0 < x → iteratedDeriv i (c03s_aux_frakE p m a) x =
      (1 / p : ℂ) * (-(m : ℂ) * iteratedDeriv i a x + ((x : ℂ) * iteratedDeriv (i + 1) a x +
        (i : ℂ) * iteratedDeriv i a x)) := by
  have hda : ContDiffOn ℝ (⊤ : ℕ∞) (deriv a) (Ioi 0) :=
    has.deriv_of_isOpen isOpen_Ioi (by exact_mod_cast le_rfl)
  have hxs : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.contDiffOn
  refine ⟨?_, fun i x hx => ?_⟩
  · unfold c03s_aux_frakE
    exact contDiffOn_const.mul ((contDiffOn_const.mul has).add (hxs.mul hda))
  · have c1 := c03s_aux_contDiffAt_of_cdo has hx i
    have c2 := c03s_aux_contDiffAt_of_cdo (hxs.mul hda) hx i
    have c1' : ContDiffAt ℝ i (fun x => -(m : ℂ) * a x) x := contDiffAt_const.mul c1
    have c3 : ContDiffAt ℝ i (fun x : ℝ => -(m : ℂ) * a x + (x : ℂ) * deriv a x) x := c1'.add c2
    unfold c03s_aux_frakE
    rw [iteratedDeriv_const_mul _ c3, iteratedDeriv_fun_add c1' c2,
      iteratedDeriv_const_mul _ c1, c03s_aux_iter_xderiv has i x hx]

/-- Symbol bounds for `𝔈a` from those of `a`. -/
theorem c03s_aux_frakE_bound (p m : ℝ) (hp : 0 < p) {a : ℝ → ℂ}
    (has : ContDiffOn ℝ (⊤ : ℕ∞) a (Ioi 0)) (n : ℕ) (A : ℕ → ℝ)
    (hA : ∀ i ≤ n + 1, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ A i * ξ ^ (m - i)) :
    ∀ i ≤ n, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i (c03s_aux_frakE p m a) ξ‖ ≤
      (1 / p) * ((|m| + i) * A i + A (i + 1)) * ξ ^ (m - i) := by
  intro i hi ξ hξ
  have hξ0 : 0 < ξ := by linarith
  rw [(c03s_aux_frakE_formula p m has).2 i ξ hξ0]
  have h1 := hA i (by omega) ξ hξ
  have h2 := hA (i + 1) (by omega) ξ hξ
  have hpow : ξ * ξ ^ (m - ((i + 1 : ℕ) : ℝ)) = ξ ^ (m - i) := by
    rw [Real.rpow_sub hξ0, Real.rpow_sub hξ0, Real.rpow_natCast, Real.rpow_natCast]
    field_simp; ring
  have hp' : (0 : ℝ) < 1 / p := by positivity
  rw [norm_mul, show ‖(1 / p : ℂ)‖ = 1 / p by
    rw [show (1 / p : ℂ) = ((1 / p : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp'], mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hp'.le
  calc ‖-(m : ℂ) * iteratedDeriv i a ξ + ((ξ : ℂ) * iteratedDeriv (i + 1) a ξ +
        (i : ℂ) * iteratedDeriv i a ξ)‖
      ≤ |m| * ‖iteratedDeriv i a ξ‖ + (ξ * ‖iteratedDeriv (i + 1) a ξ‖ +
        i * ‖iteratedDeriv i a ξ‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ((norm_add_le _ _).trans ?_))
        · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ0,
            Complex.norm_natCast]
    _ ≤ |m| * (A i * ξ ^ (m - i)) + (ξ * (A (i + 1) * ξ ^ (m - ((i + 1 : ℕ) : ℝ))) +
        i * (A i * ξ ^ (m - i))) := by gcongr
    _ = ((|m| + i) * A i + A (i + 1)) * ξ ^ (m - i) := by
        rw [show ξ * (A (i + 1) * ξ ^ (m - ((i + 1 : ℕ) : ℝ))) =
          A (i + 1) * (ξ * ξ ^ (m - ((i + 1 : ℕ) : ℝ))) by ring, hpow]; ring

/-- `𝔈` preserves the symbol class. -/
theorem c03s_aux_frakE_symbol (p m : ℝ) (hp : 0 < p) {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) :
    c03s_aux_frakE p m a ∈ c03_sp_symbol m := by
  obtain ⟨has, ha0, hab⟩ := ha
  have hz := c03s_aux_iter_zero has ha0
  refine ⟨(c03s_aux_frakE_formula p m has).1, fun ξ hξ => ?_, fun k => ?_⟩
  · have h1 := hz 0 ξ hξ
    have h2 := hz 1 ξ hξ
    simp only [iteratedDeriv_zero, iteratedDeriv_one] at h1 h2
    simp [c03s_aux_frakE, h1, h2]
  · choose C hC using hab
    refine ⟨(1 / p) * ((|m| + k) * |C k| + |C (k + 1)|), fun ξ hξ => ?_⟩
    refine c03s_aux_frakE_bound p m hp has k (fun i => |C i|) (fun i _ ξ hξ => ?_) k le_rfl ξ hξ
    exact (hC i ξ hξ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))

/-- Derivatives of the rescaled amplitude `b_y[c](s) = λ₀^{-m} c(λ₀ s)`. -/
theorem c03s_aux_b_iter (p m : ℝ) {c : ℝ → ℂ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0)) {y : ℝ}
    (hy : 0 < y) (k : ℕ) : ∀ s, 0 < s → iteratedDeriv k (c03_sp_b p m c y) s =
      ((lambda0 p y ^ ((k : ℝ) - m) : ℝ) : ℂ) * iteratedDeriv k c (lambda0 p y * s) := by
  intro s hs
  set L := lambda0 p y with hLdef
  have hL : 0 < L := Real.rpow_pos_of_pos hy _
  have hcs : ContDiffOn ℝ (⊤ : ℕ∞) (fun s => c (L * s)) (Ioi 0) :=
    hc.comp (contDiffOn_const.mul contDiffOn_id) (fun x hx => mul_pos hL hx)
  have : c03_sp_b p m c y = fun s => ((L ^ (-m) : ℝ) : ℂ) * c (L * s) := rfl
  rw [this, iteratedDeriv_const_mul _ (c03s_aux_contDiffAt_of_cdo hcs hs k),
    c03s_aux_iter_dil hc hL k s hs, ← mul_assoc]
  congr 1
  rw [show (L : ℂ) ^ k = ((L ^ (k : ℝ) : ℝ) : ℂ) by rw [Real.rpow_natCast]; push_cast; rfl,
    ← Complex.ofReal_mul, ← Real.rpow_add hL]
  congr 2; ring

/-- Symbol bound for the rescaled amplitude. -/
theorem c03s_aux_b_bound (p m : ℝ) {c : ℝ → ℂ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0))
    (hc0 : ∀ ξ ∈ Ioc (0 : ℝ) 1, c ξ = 0) (k : ℕ) (A : ℝ)
    (hA : ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k c ξ‖ ≤ A * ξ ^ (m - k)) {y s : ℝ} (hy : 0 < y)
    (hs : 0 < s) : ‖iteratedDeriv k (c03_sp_b p m c y) s‖ ≤ A * s ^ (m - k) := by
  have hA0 : 0 ≤ A := by have := hA 1 le_rfl; simp at this; linarith [norm_nonneg (iteratedDeriv k c 1)]
  set L := lambda0 p y with hLdef
  have hL : 0 < L := Real.rpow_pos_of_pos hy _
  rw [c03s_aux_b_iter p m hc hy k s hs, ← hLdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL _)]
  rcases le_or_gt 1 (L * s) with h | h
  · calc L ^ ((k : ℝ) - m) * ‖iteratedDeriv k c (L * s)‖
        ≤ L ^ ((k : ℝ) - m) * (A * (L * s) ^ (m - k)) := by gcongr; exact hA _ h
      _ = A * (L ^ ((k : ℝ) - m) * L ^ (m - k)) * s ^ (m - k) := by
          rw [Real.mul_rpow hL.le hs.le]; ring
      _ = A * s ^ (m - k) := by
          rw [← Real.rpow_add hL, show (k : ℝ) - m + (m - k) = 0 by ring, Real.rpow_zero, mul_one]
  · rw [c03s_aux_iter_zero hc hc0 k (L * s) ⟨mul_pos hL hs, h.le⟩, norm_zero, mul_zero]
    positivity

/-- `𝔈` only sees the germ. -/
theorem c03s_aux_frakE_congr (p m : ℝ) {g g' : ℝ → ℂ} {s : ℝ} (h : g =ᶠ[𝓝 s] g') :
    c03s_aux_frakE p m g s = c03s_aux_frakE p m g' s := by
  unfold c03s_aux_frakE; rw [h.eq_of_nhds, h.deriv_eq]

/-- `𝔈` commutes with the rescaling. -/
theorem c03s_aux_frakE_b (p m : ℝ) {c : ℝ → ℂ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0)) {y s : ℝ}
    (hy : 0 < y) (hs : 0 < s) :
    c03s_aux_frakE p m (c03_sp_b p m c y) s = c03_sp_b p m (c03s_aux_frakE p m c) y s := by
  have h1 := c03s_aux_b_iter p m hc hy 1 s hs
  rw [iteratedDeriv_one] at h1
  set L := lambda0 p y with hLdef
  have hL : 0 < L := Real.rpow_pos_of_pos hy _
  have hLe : L ^ ((1 : ℕ) - m : ℝ) = L ^ (-m) * L := by
    rw [show ((1 : ℕ) : ℝ) - m = -m + 1 by push_cast; ring, Real.rpow_add hL, Real.rpow_one]
  unfold c03s_aux_frakE
  rw [h1, hLe]
  simp only [c03_sp_b, ← hLdef, iteratedDeriv_one]
  push_cast; ring

/-- Iterates of `𝔈` on rescaled amplitudes. -/
theorem c03s_aux_frakE_iter_b (p m : ℝ) (hp : 0 < p) {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m)
    (j : ℕ) : (c03s_aux_frakE p m)^[j] a ∈ c03_sp_symbol m ∧
      ∀ y s : ℝ, 0 < y → 0 < s → ((c03s_aux_frakE p m)^[j] (c03_sp_b p m a y)) s =
        c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y s := by
  induction j with
  | zero => exact ⟨ha, fun _ _ _ _ => rfl⟩
  | succ j ih =>
    refine ⟨?_, fun y s hy hs => ?_⟩
    · rw [Function.iterate_succ_apply']; exact c03s_aux_frakE_symbol p m hp ih.1
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hev : (c03s_aux_frakE p m)^[j] (c03_sp_b p m a y) =ᶠ[𝓝 s]
          c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y := by
        filter_upwards [Ioi_mem_nhds hs] with z hz using ih.2 y z hy hz
      rw [c03s_aux_frakE_congr p m hev, c03s_aux_frakE_b p m ih.1.1 hy hs]

/-- Recursive constants for `𝔈^j`. -/
def c03s_aux_Aj (p m : ℝ) (Ck : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun i => |Ck i|
  | j + 1 => fun i => (1 / p) * ((|m| + i) * c03s_aux_Aj p m Ck j i + c03s_aux_Aj p m Ck j (i + 1))

theorem c03s_aux_frakE_iter_bound (p m : ℝ) (hp : 0 < p) (Ck : ℕ → ℝ) {a : ℝ → ℂ}
    (ha : a ∈ c03_sp_symbol m) (j : ℕ) : ∀ n : ℕ,
    (∀ i ≤ n + j, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) →
    ∀ i ≤ n, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i ((c03s_aux_frakE p m)^[j] a) ξ‖ ≤
      c03s_aux_Aj p m Ck j i * ξ ^ (m - i) := by
  induction j with
  | zero =>
    intro n hn i hi ξ hξ
    exact (hn i (by omega) ξ hξ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  | succ j ih =>
    intro n hn i hi ξ hξ
    rw [Function.iterate_succ_apply']
    exact c03s_aux_frakE_bound p m hp (c03s_aux_frakE_iter_b p m hp ha j).1.1 n
      (c03s_aux_Aj p m Ck j) (fun i' hi' ξ' hξ' => ih (n + 1) (fun i'' hi'' => hn i'' (by omega))
        i' hi' ξ' hξ') i hi ξ hξ

/-- Blueprint: lem:c03_sp_scaled_symbol.  For `a` in the symbol class with constants `C_k`:
`(y,s) ↦ b_y(s)` is smooth on `(0,∞)²`, `∂_s^k b_y(s) = λ₀^{k-m} a^{(k)}(λ₀ s)`,
`|∂_s^k b_y(s)| ≤ C_k s^{m-k}`, `y ∂_y b_y = 𝔈 b_y`; moreover `𝔈^j b_y` is the rescaling of the
symbol `𝔈^j a`, and `sup_{[½,2]} |∂_s^k 𝔈^j b_y| ≤ D(p,m,j,k,C_0,…,C_{j+k})` uniformly in `y > 0`. -/
theorem c03_sp_scaled_symbol (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ a ∈ c03_sp_symbol m,
      ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry (c03_sp_b p m a)) (Ioi 0 ×ˢ Ioi 0) ∧
      (∀ k : ℕ, ∀ y s : ℝ, 0 < y → 0 < s → iteratedDeriv k (c03_sp_b p m a y) s =
        ((lambda0 p y ^ ((k : ℝ) - m) : ℝ) : ℂ) * iteratedDeriv k a (lambda0 p y * s)) ∧
      (∀ y s : ℝ, 0 < y → 0 < s → (y : ℂ) * deriv (fun y' => c03_sp_b p m a y' s) y =
        c03s_aux_frakE p m (c03_sp_b p m a y) s) ∧
      (∀ j : ℕ, (c03s_aux_frakE p m)^[j] a ∈ c03_sp_symbol m ∧
        ∀ y s : ℝ, 0 < y → 0 < s →
          ((c03s_aux_frakE p m)^[j] (c03_sp_b p m a y)) s =
            c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y s)) ∧
    (∀ Ck : ℕ → ℝ, ∀ a ∈ c03_sp_symbol m,
      (∀ k : ℕ, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ k : ℕ, ∀ y s : ℝ, 0 < y → 0 < s →
        ‖iteratedDeriv k (c03_sp_b p m a y) s‖ ≤ Ck k * s ^ (m - k)) ∧
    ∀ j k : ℕ, ∀ Ck : ℕ → ℝ, ∃ D, ∀ a ∈ c03_sp_symbol m,
      (∀ i ≤ j + k, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) →
      ∀ y, 0 < y → ∀ s ∈ Icc (1 / 2 : ℝ) 2,
        ‖iteratedDeriv k ((c03s_aux_frakE p m)^[j] (c03_sp_b p m a y)) s‖ ≤ D := by
  refine ⟨fun a ha => ⟨?_, fun k y s hy hs => c03s_aux_b_iter p m ha.1 hy k s hs, ?_,
    c03s_aux_frakE_iter_b p m hp ha⟩, fun Ck a ha hCk k y s hy hs =>
      c03s_aux_b_bound p m ha.1 ha.2.1 k (Ck k) (hCk k) hy hs, ?_⟩
  · -- joint smoothness
    have hl : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => x.1 ^ (1 / p)) (Ioi 0 ×ˢ Ioi 0) :=
      contDiffOn_fst.rpow_const_of_ne (fun x hx => (ne_of_gt hx.1))
    have hlpos : ∀ x ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), 0 < x.1 ^ (1 / p) := fun x hx =>
      Real.rpow_pos_of_pos hx.1 _
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => (x.1 ^ (1 / p)) ^ (-m)) (Ioi 0 ×ˢ Ioi 0) :=
      hl.rpow_const_of_ne (fun x hx => (hlpos x hx).ne')
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => a (x.1 ^ (1 / p) * x.2)) (Ioi 0 ×ˢ Ioi 0) :=
      ha.1.comp (hl.mul contDiffOn_snd) (fun x hx => mul_pos (hlpos x hx) hx.2)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).mul h2
  · -- Euler identity in `y`
    intro y s hy hs
    have hL : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
    have hdl : HasDerivAt (lambda0 p) (1 / p * y ^ (1 / p - 1)) y := by
      unfold lambda0; exact Real.hasDerivAt_rpow_const (Or.inl hy.ne')
    have hdl2 : HasDerivAt (fun y => lambda0 p y ^ (-m))
        (-m * lambda0 p y ^ (-m - 1) * (1 / p * y ^ (1 / p - 1))) y := by
      have := (Real.hasDerivAt_rpow_const (p := -m) (Or.inl hL.ne')).comp y hdl
      exact this.congr_deriv (by ring)
    have hda : HasDerivAt a (deriv a (lambda0 p y * s)) (lambda0 p y * s) :=
      c03s_aux_hasDerivAt_of_cdo ha.1 (mul_pos hL hs)
    have hd3 : HasDerivAt (fun y => a (lambda0 p y * s))
        (deriv a (lambda0 p y * s) * ((1 / p * y ^ (1 / p - 1)) * s : ℝ)) y := by
      have h := hda.scomp y (hdl.mul_const s)
      exact h.congr_deriv (by rw [Complex.real_smul]; ring)
    have hd := (hdl2.ofReal_comp).mul hd3
    have heq : (fun y' => c03_sp_b p m a y' s) = fun y' => ((lambda0 p y' ^ (-m) : ℝ) : ℂ) *
        a (lambda0 p y' * s) := rfl
    rw [heq, show deriv (fun y' => ((lambda0 p y' ^ (-m) : ℝ) : ℂ) * a (lambda0 p y' * s)) y = _
      from hd.deriv]
    have h1 := c03s_aux_b_iter p m ha.1 hy 1 s hs
    rw [iteratedDeriv_one] at h1
    unfold c03s_aux_frakE
    rw [h1, iteratedDeriv_one]
    -- algebra with real powers
    have hyy : y * y ^ (1 / p - 1) = lambda0 p y := by
      unfold lambda0
      rw [Real.rpow_sub_one hy.ne', mul_div_assoc', mul_div_cancel_left₀ _ hy.ne']
    have e1 : y * (lambda0 p y ^ (-m - 1) * y ^ (1 / p - 1)) = lambda0 p y ^ (-m) := by
      rw [show y * (lambda0 p y ^ (-m - 1) * y ^ (1 / p - 1)) =
        lambda0 p y ^ (-m - 1) * (y * y ^ (1 / p - 1)) by ring, hyy,
        Real.rpow_sub_one hL.ne', div_mul_cancel₀ _ hL.ne']
    have e2 : y * (lambda0 p y ^ (-m) * y ^ (1 / p - 1)) = lambda0 p y ^ ((1 : ℕ) - m : ℝ) := by
      rw [show ((1 : ℕ) : ℝ) - m = -m + 1 by push_cast; ring, Real.rpow_add hL, Real.rpow_one,
        ← hyy]
      ring
    have e1' : (y : ℂ) * ((lambda0 p y ^ (-m - 1) : ℝ) : ℂ) * ((y ^ (1 / p - 1) : ℝ) : ℂ) =
        ((lambda0 p y ^ (-m) : ℝ) : ℂ) := by rw [← e1]; push_cast; ring
    have e2' : (y : ℂ) * ((lambda0 p y ^ (-m) : ℝ) : ℂ) * ((y ^ (1 / p - 1) : ℝ) : ℂ) =
        ((lambda0 p y ^ ((1 : ℕ) - m : ℝ) : ℝ) : ℂ) := by rw [← e2]; push_cast; ring
    simp only [c03_sp_b]
    push_cast
    push_cast at e1' e2'
    linear_combination (-(m : ℂ) / p * a (lambda0 p y * s)) * e1' +
      ((s : ℂ) / p * deriv a (lambda0 p y * s)) * e2'
  · -- uniform bounds on `[1/2,2]`
    intro j k Ck
    refine ⟨c03s_aux_Aj p m Ck j k * (2 ^ (m - k) + (1 / 2) ^ (m - k)), fun a ha hCk y hy s hs => ?_⟩
    have hs0 : 0 < s := by linarith [hs.1]
    have hev : (c03s_aux_frakE p m)^[j] (c03_sp_b p m a y) =ᶠ[𝓝 s]
        c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y := by
      filter_upwards [Ioi_mem_nhds hs0] with z hz using (c03s_aux_frakE_iter_b p m hp ha j).2 y z hy hz
    have hsym := (c03s_aux_frakE_iter_b p m hp ha j).1
    rw [(hev.iteratedDeriv k).eq_of_nhds]
    have hb := c03s_aux_b_bound p m hsym.1 hsym.2.1 k _ (fun ξ hξ =>
      c03s_aux_frakE_iter_bound p m hp Ck ha j k (fun i hi ξ hξ => hCk i (by omega) ξ hξ)
        k le_rfl ξ hξ) hy hs0
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · rcases le_or_gt 0 (m - k) with h | h
      · have : s ^ (m - k) ≤ 2 ^ (m - k) := Real.rpow_le_rpow hs0.le hs.2 h
        have : 0 ≤ (1 / 2 : ℝ) ^ (m - k) := by positivity
        linarith
      · have : s ^ (m - k) ≤ (1 / 2) ^ (m - k) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hs.1 h.le
        have : 0 ≤ (2 : ℝ) ^ (m - k) := by positivity
        linarith
    · have := c03s_aux_frakE_iter_bound p m hp Ck ha j k (fun i hi ξ hξ => hCk i (by omega) ξ hξ)
        k le_rfl 1 le_rfl
      simp at this; linarith [norm_nonneg (iteratedDeriv k ((c03s_aux_frakE p m)^[j] a) 1)]

/-- Joint smoothness of the localized rescaled amplitude `(y,s) ↦ χ(s) b_y(s)`. -/
theorem c03s_aux_cfam_smooth (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2) {a : ℝ → ℂ}
    (ha : a ∈ c03_sp_symbol m) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry fun y s => (χ s : ℂ) * c03_sp_b p m a y s)
      (Ioi 0 ×ˢ univ) := by
  have hb := ((c03_sp_scaled_symbol p m hp hp1).1 a ha).1
  intro x hx
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hs : x.2 ∈ tsupport χ
  · have hs0 : 0 < x.2 := by linarith [(hχs hs).1]
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => ((χ z.2 : ℝ) : ℂ)) x :=
      (Complex.ofRealCLM.contDiff.comp (hχ.comp contDiff_snd)).contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (c03_sp_b p m a)) x :=
      hb.contDiffAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds ⟨hx.1, hs0⟩)
    exact h1.mul h2
  · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    have : {z : ℝ × ℝ | z.2 ∈ (tsupport χ)ᶜ} ∈ 𝓝 x :=
      continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport χ).isOpen_compl.mem_nhds hs)
    filter_upwards [this] with z hz
    simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]


/-- The rescaling identity `I_near/P - a(λ₀) = λ₀^m ρ(μ;c_y)`. -/
theorem c03s_aux_near_identity (p m : ℝ) (hp : 0 < p) (χ : ℝ → ℝ)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (a : ℝ → ℂ) (y : ℝ) (hy : 0 < y) :
    c03_sp_Inear p χ a y / c03_sp_P p y - a (lambda0 p y) =
      ((lambda0 p y ^ m : ℝ) : ℂ) *
        c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s) := by
  set L := lambda0 p y with hLdef
  have hL : 0 < L := Real.rpow_pos_of_pos hy _
  have hLp : L ^ p = y := by
    rw [hLdef, lambda0, ← Real.rpow_mul hy.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have hmu : c03_sp_mu p y = L ^ (p + 1) := by
    rw [hLdef, lambda0, ← Real.rpow_mul hy.le, c03_sp_mu]; congr 1; field_simp
  have hLp1 : L ^ (p + 1) = y * L := by rw [Real.rpow_add_one hL.ne', hLp]
  have hP0 : c03_sp_P p y ≠ 0 := by
    unfold c03_sp_P
    refine mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 ?_).ne')
    have : 0 < L ^ (p - 1) := Real.rpow_pos_of_pos hL _
    positivity
  set Jc : ℂ := ∫ s in Ioi (0 : ℝ), (χ s : ℂ) * c03_sp_b p m a y s *
    Complex.exp (Complex.I * ((c03_sp_mu p y * c03_h p s : ℝ) : ℂ)) with hJc
  have hLL : ((L ^ m : ℝ) : ℂ) * ((L ^ (-m) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hL, add_neg_cancel, Real.rpow_zero,
      Complex.ofReal_one]
  have hInear : c03_sp_Inear p χ a y = (L : ℂ) * ((L ^ m : ℝ) : ℂ) * Jc := by
    unfold c03_sp_Inear
    have hcv := integral_comp_mul_left_Ioi (fun ξ => a ξ * (χ (ξ / L) : ℂ) *
      Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) 0 hL
    rw [mul_zero] at hcv
    have h2 : (∫ ξ in Ioi (0 : ℝ), a ξ * (χ (ξ / L) : ℂ) *
        Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) = (L : ℂ) * ∫ x in Ioi (0 : ℝ),
        a (L * x) * (χ (L * x / L) : ℂ) * Complex.exp (Complex.I * (c03_sp_phi p y (L * x) : ℂ)) := by
      rw [hcv, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hL.ne',
        Complex.ofReal_one, one_mul]
    rw [h2, mul_assoc]
    refine congrArg (fun z => (L : ℂ) * z) ?_
    rw [hJc, ← integral_const_mul]
    refine setIntegral_congr_fun (μ := volume) (measurableSet_Ioi (a := (0 : ℝ))) (fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs
    have e1 : L * s / L = s := by field_simp
    have e2 : c03_sp_phi p y (L * s) = c03_sp_mu p y * c03_h p s := by
      unfold c03_sp_phi c03_h
      rw [hmu, Real.mul_rpow hL.le hs0.le, hLp1]
      ring
    have e3 : a (L * s) = ((L ^ m : ℝ) : ℂ) * c03_sp_b p m a y s := by
      simp only [c03_sp_b, ← hLdef]
      rw [← mul_assoc, hLL, one_mul]
    simp only [e1, e2, e3]
    ring
  have hPK : c03_sp_P p y * (Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (Real.sqrt (p * c03_sp_mu p y / (2 * π)) : ℂ) *
      Complex.exp (-(Complex.I * ((c03_sp_mu p y * c03_h p 1 : ℝ) : ℂ)))) = L := by
    unfold c03_sp_P
    have hPsi : Psi0 p y = c03_sp_mu p y * c03_h p 1 := by
      unfold Psi0 c03_sp_mu c03_h; rw [Real.one_rpow]; field_simp; ring
    have hexp : Complex.exp (Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (π / 4 : ℝ)) *
        Complex.exp (-(Complex.I * ((c03_sp_mu p y * c03_h p 1 : ℝ) : ℂ))) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add, hPsi]
      convert Complex.exp_zero using 2
      push_cast; ring
    have hsq : Real.sqrt (2 * π / (p * L ^ (p - 1))) * Real.sqrt (p * c03_sp_mu p y / (2 * π)) = L := by
      have hLm : 0 < L ^ (p - 1) := Real.rpow_pos_of_pos hL _
      rw [← Real.sqrt_mul (by positivity)]
      have : 2 * π / (p * L ^ (p - 1)) * (p * c03_sp_mu p y / (2 * π)) = L ^ 2 := by
        rw [hmu, show p + 1 = (p - 1) + 2 by ring, Real.rpow_add hL, Real.rpow_two]
        field_simp
      rw [this, Real.sqrt_sq hL.le]
    rw [hLdef] at hsq ⊢
    calc _ = (Complex.exp (Complex.I * ((Psi0 p y - π / 4 : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (π / 4 : ℝ)) *
          Complex.exp (-(Complex.I * ((c03_sp_mu p y * c03_h p 1 : ℝ) : ℂ)))) *
        ((Real.sqrt (2 * π / (p * lambda0 p y ^ (p - 1))) *
          Real.sqrt (p * c03_sp_mu p y / (2 * π)) : ℝ) : ℂ) := by push_cast; ring
      _ = _ := by rw [hexp, hsq, one_mul]
  have hc1 : (fun s => (χ s : ℂ) * c03_sp_b p m a y s) 1 = ((L ^ (-m) : ℝ) : ℂ) * a L := by
    simp only [c03_sp_b, ← hLdef, mul_one]
    rw [hχ1 1 ⟨by norm_num, by norm_num⟩]; simp
  unfold c03_sp_rho
  rw [hc1, hInear]
  rw [div_sub' hP0, div_eq_iff hP0]
  have hJc' : (∫ s in Ioi (0 : ℝ), (χ s : ℂ) * c03_sp_b p m a y s *
      Complex.exp (Complex.I * ((c03_sp_mu p y * c03_h p s : ℝ) : ℂ))) = Jc := rfl
  rw [hJc']
  linear_combination (-(((L ^ m : ℝ) : ℂ)) * Jc) * hPK + (a L * c03_sp_P p y) * hLL

/-- Blueprint: lem:c03_sp_near_rescaling.  `c_y = χ_sp b_y ∈ C_c^∞((½,2))`, `I_near(y)` converges
absolutely, `P(y) ≠ 0`, `I_near/P - a(λ₀) = λ₀^m ρ(μ;c_y)`, and both sides are smooth in `y > 0`. -/
theorem c03_sp_near_rescaling (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1)
    (a : ℝ → ℂ) (ha : a ∈ c03_sp_symbol m) :
    (∀ y, 0 < y →
      ContDiff ℝ (⊤ : ℕ∞) (fun s => (χ s : ℂ) * c03_sp_b p m a y s) ∧
      tsupport (fun s => (χ s : ℂ) * c03_sp_b p m a y s) ⊆ Ioo (1 / 2) 2 ∧
      IntegrableOn (fun ξ => a ξ * (χ (ξ / lambda0 p y) : ℂ) *
        Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) (Ioi 0) ∧
      c03_sp_P p y ≠ 0 ∧
      c03_sp_Inear p χ a y / c03_sp_P p y - a (lambda0 p y) =
        ((lambda0 p y ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => c03_sp_Inear p χ a y / c03_sp_P p y - a (lambda0 p y))
      (Ioi 0) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((lambda0 p y ^ m : ℝ) : ℂ) *
      c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) (Ioi 0) := by
  have hcf := c03s_aux_cfam_smooth p m hp hp1 hχ hχs ha
  have hχK : IsCompact (tsupport χ) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ)
    (hχs.trans Ioo_subset_Icc_self)
  have hcy : ∀ y, 0 < y → ContDiff ℝ (⊤ : ℕ∞) (fun s => (χ s : ℂ) * c03_sp_b p m a y s) := by
    intro y hy
    have := hcf.comp (f := fun s : ℝ => (y, s))
      ((contDiff_const.prodMk contDiff_id).contDiffOn (s := univ))
      (fun s _ => (⟨hy, trivial⟩ : (y, s) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)))
    exact contDiffOn_univ.1 this
  have hcsupp : ∀ y, tsupport (fun s => (χ s : ℂ) * c03_sp_b p m a y s) ⊆ tsupport χ := fun y =>
    closure_minimal (fun s hs => subset_tsupport _ (fun h => hs (by simp [h])))
      (isClosed_tsupport χ)
  -- the RHS is smooth
  have hJ := (c03_sp_J_parameter p hp hp1).2 (Ioi 0) (fun y s => (χ s : ℂ) * c03_sp_b p m a y s)
    isOpen_Ioi hcf (fun y₀ _ => ⟨1, one_pos, tsupport χ, hχK, hχs, fun y _ _ s hs => by
      simp [image_eq_zero_of_notMem_tsupport hs]⟩)
  have hmu : ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_mu p) (Ioi 0) := by
    unfold c03_sp_mu; exact contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)
  have hlm : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => lambda0 p y ^ m) (Ioi 0) := by
    unfold lambda0
    exact (contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt hx)).rpow_const_of_ne
      (fun x hx => (Real.rpow_pos_of_pos hx _).ne')
  have hR : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((lambda0 p y ^ m : ℝ) : ℂ) *
      c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) (Ioi 0) := by
    have h1 := hJ.2.2.1.comp (f := fun y => (y, c03_sp_mu p y)) (contDiffOn_id.prodMk hmu)
      (fun y hy => ⟨hy, Real.rpow_pos_of_pos hy _⟩)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn hlm).mul h1
  -- pointwise statements
  have hpt : ∀ y, 0 < y →
      ContDiff ℝ (⊤ : ℕ∞) (fun s => (χ s : ℂ) * c03_sp_b p m a y s) ∧
      tsupport (fun s => (χ s : ℂ) * c03_sp_b p m a y s) ⊆ Ioo (1 / 2) 2 ∧
      IntegrableOn (fun ξ => a ξ * (χ (ξ / lambda0 p y) : ℂ) *
        Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) (Ioi 0) ∧
      c03_sp_P p y ≠ 0 ∧
      c03_sp_Inear p χ a y / c03_sp_P p y - a (lambda0 p y) =
        ((lambda0 p y ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s) := by
    intro y hy
    set L := lambda0 p y with hLdef
    have hL : 0 < L := Real.rpow_pos_of_pos hy _
    have hχ0 : ∀ t, t ∉ Ioo (1 / 2 : ℝ) 2 → χ t = 0 := fun t ht =>
      image_eq_zero_of_notMem_tsupport (fun h => ht (hχs h))
    have hLp : L ^ p = y := by
      rw [hLdef, lambda0, ← Real.rpow_mul hy.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
    have hmu : c03_sp_mu p y = L ^ (p + 1) := by
      rw [hLdef, lambda0, ← Real.rpow_mul hy.le, c03_sp_mu]; congr 1; field_simp
    have hLp1 : L ^ (p + 1) = y * L := by rw [Real.rpow_add_one hL.ne', hLp]
    have hP0 : c03_sp_P p y ≠ 0 := by
      unfold c03_sp_P
      refine mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 ?_).ne')
      have : 0 < L ^ (p - 1) := Real.rpow_pos_of_pos hL _
      positivity
    refine ⟨hcy y hy, (hcsupp y).trans hχs, ?_, hP0, ?_⟩
    · -- integrability
      have hsub : Icc (L / 2) (2 * L) ⊆ Ioi 0 := fun x hx => by
        simp only [mem_Ioi]; linarith [hx.1]
      have hcont : ContinuousOn (fun ξ => a ξ * (χ (ξ / L) : ℂ) *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) (Icc (L / 2) (2 * L)) := by
        refine ((ha.1.continuousOn.mono hsub).mul ?_).mul ?_
        · exact (Complex.continuous_ofReal.comp (hχ.continuous.comp
            (continuous_id.div_const L))).continuousOn
        · refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
            (Complex.continuous_ofReal.comp_continuousOn ?_))
          unfold c03_sp_phi
          exact (continuousOn_const.mul continuousOn_id).sub
            ((ContinuousOn.rpow_const continuousOn_id
              (fun x hx => Or.inl (ne_of_gt (hsub hx)))).div_const _)
      refine (hcont.integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun ξ hξ => ?_)
      have : χ (ξ / L) = 0 := by
        apply hχ0
        intro h
        apply hξ.2
        constructor
        · have := h.1; rw [lt_div_iff₀ hL] at this; linarith
        · have := h.2; rw [div_lt_iff₀ hL] at this; linarith
      simp [this]
    · exact c03s_aux_near_identity p m hp χ hχ1 a y hy
  exact ⟨hpt, hR.congr fun y hy => (hpt y hy).2.2.2.2, hR⟩

/-! ### Morse coordinate, compact stationary phase -/


/-- The integral `I(s) = ∫₀¹ (1-t) p (1+t(s-1))^{p-1} dt` of the Morse coordinate. -/
def c03s_aux_morseI (p s : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (1 - t) * p * (1 + t * (s - 1)) ^ (p - 1)

/-- `I` is smooth and positive on `(0,∞)`, and `I(1) = p/2`. -/
theorem c03s_aux_morseI_props (p : ℝ) (hp : 0 < p) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_morseI p) (Ioi 0) ∧ (∀ s, 0 < s → 0 < c03s_aux_morseI p s) ∧
    c03s_aux_morseI p 1 = p / 2 := by
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · unfold c03s_aux_morseI
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    apply ContDiffOn.parametric_integral (μ := volume) isOpen_Ioi isCompact_Icc
      Ioc_subset_Icc_self ?_ (by simp)
    have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => (1 + x.2 * (x.1 - 1)) ^ (p - 1))
        (Ioi 0 ×ˢ Icc 0 1) :=
      ContDiffOn.rpow_const_of_ne (by fun_prop) (fun x hx => (c03s_aux_base hx.1 hx.2).ne')
    exact ((contDiffOn_const.sub contDiffOn_snd).mul contDiffOn_const).mul hb
  · unfold c03s_aux_morseI
    have hc : ContinuousOn (fun t => (1 - t) * p * (1 + t * (s - 1)) ^ (p - 1)) (Icc 0 1) :=
      ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).mul
        (ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (c03s_aux_base hs ht).ne'))
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc.intervalIntegrable_of_Icc zero_le_one) _ zero_lt_one
    intro t ht
    have := c03s_aux_base hs (Ioo_subset_Icc_self ht)
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have h2 : 0 < (1 + t * (s - 1)) ^ (p - 1) := Real.rpow_pos_of_pos this _
    positivity
  · unfold c03s_aux_morseI
    simp only [sub_self, mul_zero, add_zero, Real.one_rpow, mul_one]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, integral_id]
    simp; ring

/-- `h(s) - h(1) = -(s-1)² I(s)` for `s > 0` (Taylor with integral remainder). -/
theorem c03s_aux_morse_taylor (p : ℝ) (hp : 0 < p) {s : ℝ} (hs : 0 < s) :
    c03_h p s - c03_h p 1 = -(s - 1) ^ 2 * c03s_aux_morseI p s := by
  have hx : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < 1 + t * (s - 1) := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht; exact c03s_aux_base hs ht
  -- `G(t) = (1-t)(s-1)(1 - x^p) + h(x)`, `x = 1 + t(s-1)`
  have hG : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t => (1 - t) * (s - 1) * (1 - (1 + t * (s - 1)) ^ p) + c03_h p (1 + t * (s - 1)))
      (-((s - 1) ^ 2 * ((1 - t) * p * (1 + t * (s - 1)) ^ (p - 1)))) t := by
    intro t ht
    have hxt := hx t ht
    have hlin : HasDerivAt (fun t => 1 + t * (s - 1)) (s - 1) t := by
      simpa using ((hasDerivAt_id t).mul_const (s - 1)).const_add 1
    have hpow := hlin.rpow_const (p := p) (Or.inl hxt.ne')
    have hpow1 := hlin.rpow_const (p := p + 1) (Or.inl hxt.ne')
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) * (s - 1)) (-(s - 1)) t := by
      simpa using ((hasDerivAt_id t).const_sub 1).mul_const (s - 1)
    have hh : HasDerivAt (fun t => c03_h p (1 + t * (s - 1)))
        ((s - 1) - (s - 1) * (p + 1) * (1 + t * (s - 1)) ^ (p + 1 - 1) / (p + 1)) t := by
      unfold c03_h
      exact hlin.sub (hpow1.div_const (p + 1))
    have := (h1.mul (hpow.const_sub 1)).add hh
    refine this.congr_deriv ?_
    rw [add_sub_cancel_right]
    have e : (1 + t * (s - 1)) ^ p = (1 + t * (s - 1)) ^ (p - 1) * (1 + t * (s - 1)) := by
      rw [← Real.rpow_add_one hxt.ne', sub_add_cancel]
    rw [e]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => -((s - 1) ^ 2 * ((1 - t) * p * (1 + t * (s - 1)) ^ (p - 1))))
      (uIcc 0 1) :=
    (continuousOn_const.mul (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).mul
      (ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (hx t ht).ne')))).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hftc
  simp only [sub_self, zero_mul, add_zero, Real.one_rpow, mul_zero, one_mul, sub_zero,
    zero_add] at hftc
  rw [show 1 + (s - 1) = s by ring] at hftc
  unfold c03s_aux_morseI
  linarith

/-- Blueprint: lem:c03_morse_h.  `w ∈ C^∞(0,∞)`, `h(s) - h(1) = -(p/2) w(s)²`, `w(1) = 0`,
`w'(1) = 1`, `w' > 0`; `w` is a diffeomorphism of `[½,2]` onto `[w(½),w(2)]` whose inverse has
bounded `C^k` norms. -/
theorem c03s_aux_morse_h (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_morse_w p) (Ioi 0) ∧
    (∀ s, 0 < s → c03_h p s - c03_h p 1 = -(p / 2) * c03s_aux_morse_w p s ^ 2) ∧
    c03s_aux_morse_w p 1 = 0 ∧ deriv (c03s_aux_morse_w p) 1 = 1 ∧
    (∀ s, 0 < s → 0 < deriv (c03s_aux_morse_w p) s) ∧
    StrictMonoOn (c03s_aux_morse_w p) (Ioi 0) ∧
    (∀ s, 0 < s → c03s_aux_morse_s p (c03s_aux_morse_w p s) = s) ∧
    ∀ v ∈ Icc (c03s_aux_morse_w p (1 / 2)) (c03s_aux_morse_w p 2),
      c03s_aux_morse_s p v ∈ Icc (1 / 2 : ℝ) 2 ∧ c03s_aux_morse_w p (c03s_aux_morse_s p v) = v ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (c03s_aux_morse_s p) v ∧
      deriv (c03s_aux_morse_s p) v * deriv (c03s_aux_morse_w p) (c03s_aux_morse_s p v) = 1 := by
  obtain ⟨hIs, hIpos, hI1⟩ := c03s_aux_morseI_props p hp
  set w := c03s_aux_morse_w p with hwdef
  set q : ℝ → ℝ := fun s => Real.sqrt (2 / p * c03s_aux_morseI p s) with hqdef
  have hw_eq : w = fun s => (s - 1) * q s := rfl
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi 0) :=
    (contDiffOn_const.mul hIs).sqrt (fun s hs => (mul_pos (by positivity) (hIpos s hs)).ne')
  have hqpos : ∀ s, 0 < s → 0 < q s := fun s hs =>
    Real.sqrt_pos.2 (mul_pos (by positivity) (hIpos s hs))
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) w (Ioi 0) := by
    rw [hw_eq]; exact (contDiffOn_id.sub contDiffOn_const).mul hq
  have hsq : ∀ s, 0 < s → c03_h p s - c03_h p 1 = -(p / 2) * w s ^ 2 := by
    intro s hs
    rw [c03s_aux_morse_taylor p hp hs, hw_eq]
    simp only [hqdef]
    rw [mul_pow, Real.sq_sqrt (mul_pos (by positivity) (hIpos s hs)).le]
    field_simp
  have hw1 : w 1 = 0 := by simp [hw_eq]
  have hdiff : ∀ s, 0 < s → HasDerivAt w (deriv w s) s := fun s hs =>
    ((hw.contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hq1 : q 1 = 1 := by
    simp only [hqdef, hI1]
    rw [show 2 / p * (p / 2) = 1 by field_simp, Real.sqrt_one]
  have hd1 : deriv w 1 = 1 := by
    have hqd : HasDerivAt q (deriv q 1) 1 :=
      ((hq.contDiffAt (Ioi_mem_nhds one_pos)).differentiableAt (by simp)).hasDerivAt
    have := ((hasDerivAt_id (1 : ℝ)).sub_const 1).mul hqd
    rw [hw_eq]
    exact this.deriv.trans (by simp [hq1])
  have hdpos : ∀ s, 0 < s → 0 < deriv w s := by
    intro s hs
    have h1 : HasDerivAt (fun s => w s ^ 2) (2 * w s * deriv w s) s := by
      have := (hdiff s hs).fun_pow 2
      exact this.congr_deriv (by push_cast; ring)
    have h2 : HasDerivAt (fun s => -(2 / p) * (c03_h p s - c03_h p 1))
        (-(2 / p) * (1 - s ^ p)) s := by
      unfold c03_h
      have hr := (Real.hasDerivAt_rpow_const (p := p + 1) (Or.inl hs.ne'))
      have := (((hasDerivAt_id s).sub (hr.div_const (p + 1))).sub_const
        (1 - 1 ^ (p + 1) / (p + 1))).const_mul (-(2 / p))
      refine this.congr_deriv ?_
      rw [add_sub_cancel_right]; field_simp
    have heq : (fun s => w s ^ 2) =ᶠ[𝓝 s] (fun s => -(2 / p) * (c03_h p s - c03_h p 1)) := by
      filter_upwards [Ioi_mem_nhds hs] with x hx
      rw [hsq x hx]; field_simp
    have key := h1.unique (h2.congr_of_eventuallyEq heq)
    rcases lt_trichotomy s 1 with hlt | rfl | hgt
    · have hwneg : w s < 0 := by
        rw [hw_eq]; exact mul_neg_of_neg_of_pos (by linarith) (hqpos s hs)
      have hsp : s ^ p < 1 := Real.rpow_lt_one hs.le hlt hp
      have hR : -(2 / p) * (1 - s ^ p) < 0 := by
        have : 0 < 2 / p := by positivity
        nlinarith
      by_contra hc; push Not at hc
      nlinarith
    · rw [hd1]; exact one_pos
    · have hwpos : 0 < w s := by
        rw [hw_eq]; exact mul_pos (by linarith) (hqpos s hs)
      have hsp : 1 < s ^ p := Real.one_lt_rpow hgt hp
      have hR : 0 < -(2 / p) * (1 - s ^ p) := by
        have : 0 < 2 / p := by positivity
        nlinarith
      by_contra hc; push Not at hc
      nlinarith
  have hmono : StrictMonoOn w (Ioi 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioi 0) hw.continuousOn (by rw [interior_Ioi]; exact hdpos)
  have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by
    simp only [mem_Ioi]; linarith [hx.1]
  have hmonoI : StrictMonoOn w (Icc (1 / 2) 2) := hmono.mono hsub
  have himg : w '' Icc (1 / 2) 2 = Icc (w (1 / 2)) (w 2) := by
    ext x; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hmonoI.monotoneOn ⟨le_rfl, by norm_num⟩ hs hs.1,
        hmonoI.monotoneOn hs ⟨by norm_num, le_rfl⟩ hs.2⟩
    · intro hx
      exact intermediate_value_Icc (by norm_num) (hw.continuousOn.mono hsub) hx
  -- the inverse
  set g := c03s_aux_morse_s p with hgdef
  have hinj : InjOn w (Ioi 0) := hmono.injOn
  have hg_left : ∀ s ∈ Ioi (0 : ℝ), g (w s) = s := fun s hs => hinj.leftInvOn_invFunOn hs
  have hJ : ∀ x ∈ Icc (w (1 / 2)) (w 2), ∃ a ∈ Icc (1 / 2 : ℝ) 2, w a = x := by
    rw [← himg]; intro x hx; exact hx
  have hgcd : ∀ x ∈ Icc (w (1 / 2)) (w 2), ContDiffAt ℝ (⊤ : ℕ∞) g x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hJ x hx
    have ha0 : 0 < a := hsub ha
    have hca : ContDiffAt ℝ (⊤ : ℕ∞) w a := hw.contDiffAt (Ioi_mem_nhds ha0)
    have hf' := (hdiff a ha0).hasFDerivAt_equiv (hdpos a ha0).ne'
    have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hL := hca.to_localInverse hf' hn
    have hS := hca.hasStrictFDerivAt hf' hn
    refine hL.congr_of_eventuallyEq ?_
    have hLa : hca.localInverse hf' hn (w a) = a := hca.localInverse_apply_image hf' hn
    have hev1 : ∀ᶠ y in 𝓝 (w a), hca.localInverse hf' hn y ∈ Ioi 0 :=
      hL.continuousAt.preimage_mem_nhds (by rw [hLa]; exact Ioi_mem_nhds ha0)
    filter_upwards [hev1, hS.eventually_right_inverse] with y hy1 hy2
    have hy : ∃ b ∈ Ioi (0 : ℝ), w b = y := ⟨_, hy1, hy2⟩
    exact hinj (Function.invFunOn_mem hy) hy1 ((Function.invFunOn_eq hy).trans hy2.symm)
  refine ⟨hw, hsq, hw1, hd1, hdpos, hmono, fun s hs => hg_left s hs, fun v hv => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hJ v hv
  have ha0 : 0 < a := hsub ha
  have hga : g (w a) = a := hg_left a ha0
  refine ⟨by rw [hga]; exact ha, by rw [hga], hgcd _ hv, ?_⟩
  have hfg : ∀ᶠ y in 𝓝 (w a), w (g y) = y := by
    have h1 : w (a / 2) < w a := hmono (show a / 2 ∈ Ioi (0 : ℝ) from half_pos ha0) ha0 (half_lt_self ha0)
    have h2 : w a < w (a + 1) := hmono ha0 (show a + 1 ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith) (lt_add_one a)
    filter_upwards [Ioo_mem_nhds h1 h2] with y hy
    have hsub2 : Icc (a / 2) (a + 1) ⊆ Ioi 0 := fun x hx => by
      simp only [mem_Ioi]; linarith [hx.1]
    obtain ⟨b, hb, hby⟩ := intermediate_value_Ioo (show a / 2 ≤ a + 1 by linarith)
      (hw.continuousOn.mono hsub2) hy
    exact Function.invFunOn_eq ⟨b, hsub2 (Ioo_subset_Icc_self hb), hby⟩
  have hgd := HasDerivAt.of_local_left_inverse (hgcd _ hv).continuousAt
    (by rw [hga]; exact hdiff a ha0) (hdpos a ha0).ne' hfg
  rw [hgd.deriv, hga, inv_mul_cancel₀ (hdpos a ha0).ne']

/-- Leibniz bound on an open set. -/
theorem c03s_aux_leibnizU {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℂ} (hf : ContDiffOn ℝ 3 f U)
    (hg : ContDiffOn ℝ 3 g U) {y : ℝ} (hy : y ∈ U) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedDeriv n (fun y => f y * g y) y‖ ≤ ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedDeriv i f y‖ * ‖iteratedDeriv (n - i) g y‖ := by
  have e : ∀ (F : ℝ → ℂ) k, ‖iteratedDeriv k F y‖ = ‖iteratedFDerivWithin ℝ k F U y‖ := by
    intro F k
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin, iteratedDerivWithin_of_isOpen hU hy]
  simp_rw [e]
  exact norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hy (by exact_mod_cast hn)

/-- Blueprint: lem:c03_sp_morse_amplitude.  `e = (c ∘ s) s'` (extended by zero) is `C³`, supported
in `[-L,L]`, `e(0) = c(1)` and `‖e‖_{C³} ≤ C ‖c‖_{C³}` with `L, C` depending only on `p`. -/
theorem c03_sp_morse_amplitude (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ L, 1 ≤ L ∧ ∃ C, 0 < C ∧ ∀ c : ℝ → ℂ, ContDiff ℝ 3 c → tsupport c ⊆ Ioo (1 / 2) 2 →
      ContDiff ℝ 3 (c03s_aux_morse_e p c) ∧ HasCompactSupport (c03s_aux_morse_e p c) ∧
      (∀ v, L < |v| → c03s_aux_morse_e p c v = 0) ∧ c03s_aux_morse_e p c 0 = c 1 ∧
      c03_Ck_normR 3 univ (c03s_aux_morse_e p c) ≤ C * c03_Ck_normR 3 univ c := by
  obtain ⟨hw, -, hw1, hd1, -, hmono, hsw, hsv⟩ := c03s_aux_morse_h p hp hp1
  set w := c03s_aux_morse_w p with hwdef
  set s := c03s_aux_morse_s p with hsdef
  set W1 := w (1 / 2) with hW1def
  set W2 := w 2 with hW2def
  have hW1 : W1 < 0 := by
    rw [hW1def, ← hw1]
    exact hmono (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (by norm_num)
  have hW2 : 0 < W2 := by
    rw [hW2def, ← hw1]
    exact hmono (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num)
  have hW12 : W1 < W2 := by linarith
  have hsC : ∀ v ∈ Icc W1 W2, ContDiffAt ℝ (⊤ : ℕ∞) s v := fun v hv => (hsv v hv).2.2.1
  have hsJ : ContDiffOn ℝ (⊤ : ℕ∞) s (Ioo W1 W2) := fun v hv =>
    (hsC v (Ioo_subset_Icc_self hv)).contDiffWithinAt
  have h3top : (3 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    show ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.2 le_top
  have hdsJ : ContDiffOn ℝ (⊤ : ℕ∞) (deriv s) (Ioo W1 W2) :=
    hsJ.deriv_of_isOpen isOpen_Ioo (by exact_mod_cast le_rfl)
  -- derivative bounds for the inverse coordinate
  have hsb : ∀ l : ℕ, ∃ B, ∀ v ∈ Icc W1 W2, |iteratedDeriv l s v| ≤ B := by
    intro l
    have hcI : ContDiffOn ℝ (⊤ : ℕ∞) s (Icc W1 W2) := fun v hv => (hsC v hv).contDiffWithinAt
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hcI.continuousOn_iteratedDerivWithin (m := l) (by exact_mod_cast le_top)
        (uniqueDiffOn_Icc hW12))
    refine ⟨B, fun v hv => ?_⟩
    have := hB v hv
    rwa [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hW12)
      ((hsC v hv).of_le (by exact_mod_cast le_top)) hv, Real.norm_eq_abs] at this
  choose B hB using hsb
  set Ds : ℝ := 1 + |B 0| + |B 1| + |B 2| + |B 3| + |B 4| with hDs
  have hDs1 : 1 ≤ Ds := by
    rw [hDs]; linarith [abs_nonneg (B 0), abs_nonneg (B 1), abs_nonneg (B 2), abs_nonneg (B 3),
      abs_nonneg (B 4)]
  have hBD : ∀ l ≤ 4, ∀ v ∈ Icc W1 W2, |iteratedDeriv l s v| ≤ Ds := by
    intro l hl v hv
    refine (hB l v hv).trans ((le_abs_self _).trans ?_)
    have h0 := abs_nonneg (B 0); have h1 := abs_nonneg (B 1); have h2 := abs_nonneg (B 2)
    have h3 := abs_nonneg (B 3); have h4 := abs_nonneg (B 4)
    interval_cases l <;> (rw [hDs]; linarith)
  set L : ℝ := max 1 (max |W1| |W2|) with hL
  refine ⟨L, le_max_left _ _, 192 * Ds ^ 4, by positivity, fun c hc hcs => ?_⟩
  set e := c03s_aux_morse_e p c with hedef
  have hK : IsCompact (tsupport c) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport c)
    (hcs.trans Ioo_subset_Icc_self)
  have hcomp : HasCompactSupport c := hK
  have hKpos : tsupport c ⊆ Ioi 0 := fun x hx => by
    simp only [mem_Ioi]; linarith [(hcs hx).1]
  set S := w '' tsupport c with hSdef
  have hS : IsCompact S := hK.image_of_continuousOn (hw.continuousOn.mono hKpos)
  have hSJ : S ⊆ Ioo W1 W2 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hcs hx
    exact ⟨hmono (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) (hKpos hx) hx'.1,
      hmono (hKpos hx) (show (2 : ℝ) ∈ Ioi 0 by norm_num) hx'.2⟩
  have he0 : ∀ v ∉ S, e v = 0 := by
    intro v hv
    simp only [hedef, c03s_aux_morse_e]
    split_ifs with hvJ
    · have : s v ∉ tsupport c := by
        intro h
        apply hv
        exact ⟨s v, h, (hsv v (Ioo_subset_Icc_self hvJ)).2.1⟩
      rw [image_eq_zero_of_notMem_tsupport this, zero_mul]
    · rfl
  set f0 : ℝ → ℂ := fun v => c (s v) * ((deriv s v : ℝ) : ℂ) with hf0
  have hloc : ∀ v ∈ Ioo W1 W2, e =ᶠ[𝓝 v] f0 := by
    intro v hv
    filter_upwards [isOpen_Ioo.mem_nhds hv] with z hz
    simp only [hedef, c03s_aux_morse_e, hf0]
    rw [if_pos hz]
  have hcs3 : ContDiffOn ℝ 3 (fun v => c (s v)) (Ioo W1 W2) :=
    hc.comp_contDiffOn (hsJ.of_le h3top)
  have hds3 : ContDiffOn ℝ 3 (fun v => ((deriv s v : ℝ) : ℂ)) (Ioo W1 W2) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hdsJ.of_le h3top)
  have hf03 : ContDiffOn ℝ 3 f0 (Ioo W1 W2) := hcs3.mul hds3
  have heC : ContDiff ℝ 3 e := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ Ioo W1 W2
    · exact (hf03.contDiffAt (isOpen_Ioo.mem_nhds hv)).congr_of_eventuallyEq (hloc v hv)
    · have hvS : v ∉ S := fun h => hv (hSJ h)
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hvS] with z hz using he0 z hz
  refine ⟨heC, HasCompactSupport.intro hS he0, fun v hv => ?_, ?_, ?_⟩
  · simp only [hedef, c03s_aux_morse_e]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have : |v| ≤ L := by
      rw [abs_le]; constructor
      · have : |W1| ≤ L := le_trans (le_max_left _ _) (le_max_right _ _)
        rw [abs_of_neg hW1] at this; linarith
      · have : |W2| ≤ L := le_trans (le_max_right _ _) (le_max_right _ _)
        rw [abs_of_pos hW2] at this; linarith
    linarith
  · have h0 : (0 : ℝ) ∈ Ioo W1 W2 := ⟨hW1, hW2⟩
    have hs0 : s 0 = 1 := by
      have := hsw 1 one_pos
      rwa [show w 1 = 0 from hw1] at this
    have hds0 : deriv s 0 = 1 := by
      have := (hsv 0 (Ioo_subset_Icc_self h0)).2.2.2
      rwa [hs0, hd1, mul_one] at this
    simp only [hedef, c03s_aux_morse_e]
    rw [if_pos h0, show c03s_aux_morse_s p 0 = 1 from hs0,
      show deriv (c03s_aux_morse_s p) 0 = 1 from hds0]; simp
  · -- the norm bound
    set Ncc := c03_Ck_normR 3 univ c with hNcc
    have hN0 : 0 ≤ Ncc := c03s_aux_Ck_nonneg _ _
    have hcl : ∀ l ≤ 3, ∀ x, ‖iteratedDeriv l c x‖ ≤ Ncc := fun l hl x =>
      c03sp_aux_Ck_le hc hcomp hl x
    have hbound : ∀ k ≤ 3, ∀ v, ‖iteratedDeriv k e v‖ ≤ 48 * Ds ^ 4 * Ncc := by
      intro k hk v
      by_cases hvS : v ∈ S
      · have hvJ := hSJ hvS
        have hvI := Ioo_subset_Icc_self hvJ
        rw [((hloc v hvJ).iteratedDeriv k).eq_of_nhds]
        refine (c03s_aux_leibnizU isOpen_Ioo hcs3 hds3 hvJ hk).trans ?_
        -- Faà di Bruno for `c ∘ s`
        have hFdB : ∀ i ≤ k, ‖iteratedDeriv i (fun v => c (s v)) v‖ ≤ 6 * Ncc * Ds ^ 3 := by
          intro i hi
          have key := norm_iteratedFDerivWithin_comp_le (g := c) (f := s) (n := i)
            (s := Ioo W1 W2) (t := univ) (x := v) (N := 3) hc.contDiffOn
            (hsJ.of_le h3top) (by exact_mod_cast (hi.trans hk))
            uniqueDiffOn_univ isOpen_Ioo.uniqueDiffOn (mapsTo_univ _ _) hvJ (C := Ncc) (D := Ds)
            (fun l hl => by
              rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
              exact hcl l (by omega) _)
            (fun l hl1 hl2 => by
              rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
                iteratedDerivWithin_of_isOpen isOpen_Ioo hvJ, Real.norm_eq_abs]
              exact (hBD l (by omega) v hvI).trans (le_self_pow₀ hDs1 (by omega)))
          rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
            iteratedDerivWithin_of_isOpen isOpen_Ioo hvJ] at key
          refine key.trans ?_
          have hf : (i.factorial : ℝ) ≤ 6 := by
            have : i.factorial ≤ Nat.factorial 3 := Nat.factorial_le (by omega)
            exact_mod_cast this.trans (by decide)
          have hp3 : Ds ^ i ≤ Ds ^ 3 := pow_le_pow_right₀ hDs1 (by omega)
          have hfin : (i.factorial : ℝ) * Ncc * Ds ^ i ≤ 6 * Ncc * Ds ^ 3 := by gcongr
          exact hfin
        have hdsb : ∀ i ≤ k, ‖iteratedDeriv (k - i) (fun v => ((deriv s v : ℝ) : ℂ)) v‖ ≤ Ds := by
          intro i hi
          have hle : (((k - i : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
            WithTop.coe_le_coe.2 le_top
          have hca : ContDiffAt ℝ (k - i) (deriv s) v :=
            (hdsJ.contDiffAt (isOpen_Ioo.mem_nhds hvJ)).of_le hle
          rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
            show (fun v => ((deriv s v : ℝ) : ℂ)) = Complex.ofRealLI ∘ (deriv s) from rfl,
            Complex.ofRealLI.norm_iteratedFDeriv_comp_left hca le_rfl,
            norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedDeriv_succ', Real.norm_eq_abs]
          exact hBD _ (by omega) v hvI
        have hstep1 : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ‖iteratedDeriv i (fun v => c (s v)) v‖ *
            ‖iteratedDeriv (k - i) (fun v => ((deriv s v : ℝ) : ℂ)) v‖ ≤
            ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (6 * Ncc * Ds ^ 3) * Ds := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have h1 := hFdB i hi'
          have h2 := hdsb i hi'
          have h3 : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
          have h4 : 0 ≤ ‖iteratedDeriv i (fun v => c (s v)) v‖ := norm_nonneg _
          have h5 : 0 ≤ ‖iteratedDeriv (k - i) (fun v => ((deriv s v : ℝ) : ℂ)) v‖ := norm_nonneg _
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 h5
            (mul_nonneg h3 (h4.trans h1))
        have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
          exact_mod_cast Nat.sum_range_choose k
        have hstep2 : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (6 * Ncc * Ds ^ 3) * Ds =
            (2 : ℝ) ^ k * (6 * Ncc * Ds ^ 4) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]; ring
        have h2k : (2 : ℝ) ^ k ≤ 8 := le_trans (pow_le_pow_right₀ (by norm_num) hk) (by norm_num)
        have h6 : 0 ≤ 6 * Ncc * Ds ^ 4 := by positivity
        refine hstep1.trans (hstep2.le.trans ?_)
        exact le_trans (mul_le_mul_of_nonneg_right h2k h6) (le_of_eq (by ring))
      · rw [c03s_aux_iter_zero_off hS.isClosed he0 k hvS, norm_zero]
        positivity
    calc c03_Ck_normR 3 univ e ≤ (3 + 1) * (48 * Ds ^ 4 * Ncc) :=
          c03s_aux_Ck_norm_le (by positivity) hbound
      _ = 192 * Ds ^ 4 * Ncc := by ring

/-- Blueprint: lem:c03_sp_morse_integral.  `∫₀^∞ c(s) e^{iμh(s)} ds = e^{iμh(1)} ∫ e(v) e^{-ipμv²/2} dv`,
both integrands absolutely integrable. -/
theorem c03_sp_morse_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c : ℝ → ℂ) (hc : ContDiff ℝ 3 c)
    (hcs : tsupport c ⊆ Ioo (1 / 2) 2) (μ : ℝ) (hμ : 0 < μ) :
    IntegrableOn (fun s => c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) (Ioi 0) ∧
    Integrable (fun v : ℝ => c03s_aux_morse_e p c v *
      Complex.exp (-(Complex.I * ((p * μ : ℝ) : ℂ) * (v : ℂ) ^ 2 / 2))) ∧
    (∫ s in Ioi (0 : ℝ), c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)) *
        ∫ v : ℝ, c03s_aux_morse_e p c v *
          Complex.exp (-(Complex.I * ((p * μ : ℝ) : ℂ) * (v : ℂ) ^ 2 / 2)) := by
  obtain ⟨hw, hsq, hw1, hd1, hdpos, hmono, hsw, hsv⟩ := c03s_aux_morse_h p hp hp1
  obtain ⟨L, hL, CM, hCM, hMA⟩ := c03_sp_morse_amplitude p hp hp1
  obtain ⟨heC, hecs, -, -, -⟩ := hMA c hc hcs
  set w := c03s_aux_morse_w p with hwdef
  set s := c03s_aux_morse_s p with hsdef
  have hc0 : ∀ x, x ∉ Ioo (1 / 2 : ℝ) 2 → c x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hcs h))
  have hsubI : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by simp only [mem_Ioi]; linarith [hx.1]
  have hhc : ContinuousOn (c03_h p) (Icc (1 / 2 : ℝ) 2) :=
    (c03s_aux_h_smooth p hp).continuousOn.mono hsubI
  set G : ℝ → ℂ := fun v => Complex.exp (-(Complex.I * ((p * μ : ℝ) : ℂ) * (v : ℂ) ^ 2 / 2)) with hG
  have hGc : Continuous G := by
    rw [hG]; exact Complex.continuous_exp.comp (by fun_prop)
  set e := c03s_aux_morse_e p c with hedef
  have heG : Continuous (fun v => e v * G v) := heC.continuous.mul hGc
  -- integrability
  have hint1 : IntegrableOn (fun s => c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)))
      (Ioi 0) := by
    have hcont : ContinuousOn (fun s => c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ)))
        (Icc (1 / 2 : ℝ) 2) :=
      hc.continuous.continuousOn.mul (Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
          (continuousOn_const.mul hhc))))
    refine (hcont.integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => ?_)
    rw [hc0 x (fun h => hx.2 (Ioo_subset_Icc_self h)), zero_mul]
  have hint2 : Integrable (fun v => e v * G v) := heG.integrable_of_hasCompactSupport hecs.mul_right
  refine ⟨hint1, hint2, ?_⟩
  -- W-interval
  set W1 := w (1 / 2) with hW1def
  set W2 := w 2 with hW2def
  have hW12 : W1 < W2 := hmono (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num)
  have he_off : ∀ v, v ∉ Ioo W1 W2 → e v = 0 := by
    intro v hv; simp only [hedef, c03s_aux_morse_e]; rw [if_neg hv]
  have hR : (∫ v, e v * G v) = ∫ v in W1..W2, e v * G v := by
    rw [intervalIntegral.integral_of_le hW12.le]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [he_off v (fun h => hv (Ioo_subset_Ioc_self h)), zero_mul]
  have hL : (∫ x in Ioi (0 : ℝ), c x * Complex.exp (Complex.I * ((μ * c03_h p x : ℝ) : ℂ))) =
      ∫ x in (1 / 2 : ℝ)..2, c x * Complex.exp (Complex.I * ((μ * c03_h p x : ℝ) : ℂ)) := by
    rw [c03s_aux_Ioi_Icc (fun x hx => by rw [hc0 x hx, zero_mul]), integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num)]
  -- change of variables
  have hwd : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, HasDerivAt w (deriv w x) x := fun x hx => by
    rw [uIcc_of_le (by norm_num)] at hx
    exact ((hw.contDiffAt (Ioi_mem_nhds (hsubI hx))).differentiableAt (by simp)).hasDerivAt
  have hwdc : ContinuousOn (deriv w) (uIcc (1 / 2 : ℝ) 2) := by
    rw [uIcc_of_le (by norm_num)]
    exact (hw.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsubI
  have hcov := intervalIntegral.integral_deriv_smul_comp hwd hwdc heG
  rw [hR, hL, ← hcov, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (by norm_num)] at hx
  have hx0 : 0 < x := hsubI hx
  simp only [Function.comp_apply, Complex.real_smul]
  by_cases hxo : x ∈ Ioo (1 / 2 : ℝ) 2
  · have hwx : w x ∈ Ioo W1 W2 :=
      ⟨hmono (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) hx0 hxo.1,
        hmono hx0 (show (2 : ℝ) ∈ Ioi 0 by norm_num) hxo.2⟩
    have hsx : s (w x) = x := hsw x hx0
    have hds := (hsv (w x) (Ioo_subset_Icc_self hwx)).2.2.2
    rw [hsx] at hds
    have hex : e (w x) = c x * ((deriv s (w x) : ℝ) : ℂ) := by
      simp only [hedef, c03s_aux_morse_e]; rw [if_pos hwx]
      exact congrArg (fun z => c z * ((deriv s (w x) : ℝ) : ℂ)) hsx
    rw [hex]
    have hr : (μ * c03_h p x : ℝ) - μ * c03_h p 1 = -(p * μ) * w x ^ 2 / 2 := by
      rw [← mul_sub, hsq x hx0]; ring
    have hrC : ((μ * c03_h p x : ℝ) : ℂ) - ((μ * c03_h p 1 : ℝ) : ℂ) =
        -((p * μ : ℝ) : ℂ) * ((w x : ℝ) : ℂ) ^ 2 / 2 := by
      rw [← Complex.ofReal_sub, hr]; push_cast; ring
    have hexp : -(Complex.I * ((p * μ : ℝ) : ℂ) * ((w x : ℝ) : ℂ) ^ 2 / 2) =
        Complex.I * ((μ * c03_h p x : ℝ) : ℂ) + -(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)) := by
      linear_combination (-Complex.I) * hrC
    have hG' : G (w x) = Complex.exp (Complex.I * ((μ * c03_h p x : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))) := by
      show Complex.exp (-(Complex.I * ((p * μ : ℝ) : ℂ) * ((w x : ℝ) : ℂ) ^ 2 / 2)) = _
      rw [hexp, Complex.exp_add]
    rw [hG']
    have hds' : ((deriv w x : ℝ) : ℂ) * ((deriv s (w x) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_comm, hds, Complex.ofReal_one]
    have hE : Complex.exp (Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    linear_combination (-(c x * Complex.exp (Complex.I * ((μ * c03_h p x : ℝ) : ℂ)))) * hE -
      (Complex.exp (Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)) * c x *
        Complex.exp (Complex.I * ((μ * c03_h p x : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)))) * hds'
  · rw [hc0 x hxo, zero_mul]
    have hwx : w x ∉ Ioo W1 W2 := by
      rintro ⟨h1, h2⟩
      apply hxo
      constructor
      · by_contra h; push Not at h
        exact absurd h1 (not_lt.2 (hmono.monotoneOn hx0 (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) h))
      · by_contra h; push Not at h
        exact absurd h2 (not_lt.2 (hmono.monotoneOn (show (2 : ℝ) ∈ Ioi 0 by norm_num) hx0 h))
    rw [he_off _ hwx]; ring

/-- Blueprint: lem:c03_sp_compact (prefixed copy of `GSQG.c03_sp_compact`). -/
theorem c03s_c03_sp_compact (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ μ : ℝ, 0 < μ → ∀ c : ℝ → ℂ, ContDiff ℝ 3 c → tsupport c ⊆ Ioo (1 / 2) 2 →
      ‖c03_sp_rho p μ c‖ ≤ C * μ⁻¹ * c03_Ck_normR 3 univ c := by
  obtain ⟨L, hL, CM, hCM, hMA⟩ := c03_sp_morse_amplitude p hp hp1
  obtain ⟨CF, hCF, hF⟩ := c03sp_c03_fresnel_expansion
  refine ⟨CF * L * CM / (Real.sqrt (2 * π) * p), by positivity, fun μ hμ c hc hcs => ?_⟩
  obtain ⟨heC, -, heL, he0, hnorm⟩ := hMA c hc hcs
  obtain ⟨-, -, hJ⟩ := c03_sp_morse_integral p hp hp1 c hc hcs μ hμ
  set ν : ℝ := p * μ with hν
  have hν0 : 0 < ν := by positivity
  have hFr := hF ν hν0 L hL (c03s_aux_morse_e p c) heC heL
  set Ie := ∫ w : ℝ, c03s_aux_morse_e p c w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))
    with hIe
  have hJ' : (∫ s in Ioi (0 : ℝ), c s * Complex.exp (Complex.I * ((μ * c03_h p s : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)) * Ie := hJ
  have hS : Real.sqrt (p * μ / (2 * π)) * Real.sqrt (2 * π / ν) = 1 := by
    rw [← Real.sqrt_mul (by positivity), hν, show p * μ / (2 * π) * (2 * π / (p * μ)) = 1 by
      field_simp, Real.sqrt_one]
  have hrho : c03_sp_rho p μ c = Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (Real.sqrt (p * μ / (2 * π)) : ℂ) * (Ie - (Real.sqrt (2 * π / ν) : ℂ) *
        Complex.exp (-(Complex.I * (π / 4 : ℝ))) * c03s_aux_morse_e p c 0) := by
    unfold c03_sp_rho
    rw [hJ', he0]
    have hE1 : Complex.exp (-(Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ((μ * c03_h p 1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hE2 : Complex.exp (Complex.I * (π / 4 : ℝ)) * Complex.exp (-(Complex.I * (π / 4 : ℝ))) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hS' : (Real.sqrt (p * μ / (2 * π)) : ℂ) * (Real.sqrt (2 * π / ν) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hS, Complex.ofReal_one]
    linear_combination (Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (Real.sqrt (p * μ / (2 * π)) : ℂ) * Ie) * hE1 +
      (c 1 * (Real.sqrt (p * μ / (2 * π)) : ℂ) * (Real.sqrt (2 * π / ν) : ℂ)) * hE2 + c 1 * hS'
  have hK : ‖Complex.exp (Complex.I * (π / 4 : ℝ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hSν : Real.sqrt (p * μ / (2 * π)) * ν ^ (-(3 / 2 : ℝ)) = (Real.sqrt (2 * π))⁻¹ * ν⁻¹ := by
    rw [show p * μ / (2 * π) = ν / (2 * π) by rw [hν], Real.sqrt_div' _ (by positivity),
      Real.sqrt_eq_rpow ν, div_eq_mul_inv, mul_comm (ν ^ (1 / 2 : ℝ)), mul_assoc,
      ← Real.rpow_add hν0, show (1 / 2 : ℝ) + -(3 / 2) = -1 by norm_num, Real.rpow_neg_one]
  have hN := hnorm
  set Nc := c03_Ck_normR 3 univ c
  have hNe0 : 0 ≤ c03_Ck_normR 3 univ (c03s_aux_morse_e p c) := ENNReal.toReal_nonneg
  rw [hrho, norm_mul, norm_mul, hK, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hS0 : 0 ≤ Real.sqrt (p * μ / (2 * π)) := Real.sqrt_nonneg _
  calc Real.sqrt (p * μ / (2 * π)) * ‖Ie - (Real.sqrt (2 * π / ν) : ℂ) *
        Complex.exp (-(Complex.I * (π / 4 : ℝ))) * c03s_aux_morse_e p c 0‖
      ≤ Real.sqrt (p * μ / (2 * π)) *
        (CF * L * ν ^ (-(3 / 2 : ℝ)) * c03_Ck_normR 3 univ (c03s_aux_morse_e p c)) :=
        mul_le_mul_of_nonneg_left hFr hS0
    _ ≤ Real.sqrt (p * μ / (2 * π)) * (CF * L * ν ^ (-(3 / 2 : ℝ)) * (CM * Nc)) := by
        gcongr
    _ = CF * L * CM * (Real.sqrt (p * μ / (2 * π)) * ν ^ (-(3 / 2 : ℝ))) * Nc := by ring
    _ = CF * L * CM / (Real.sqrt (2 * π) * p) * μ⁻¹ * Nc := by
        rw [hSν, hν]; field_simp

/-- Partial derivatives as directional derivatives. -/
theorem c03s_aux_partial_y {f : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun y => f (y, x.2)) (fderiv ℝ f x (1, 0)) x.1 := by
  have h := hf.hasFDerivAt.comp_hasDerivAt x.1 ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  exact h

theorem c03s_aux_partial_m {f : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun μ => f (x.1, μ)) (fderiv ℝ f x (0, 1)) x.2 := by
  have h := hf.hasFDerivAt.comp_hasDerivAt x.2 ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))
  exact h

/-- Directional derivatives of smooth functions are smooth. -/
theorem c03s_aux_dir_smooth {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ × ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (v : ℝ × ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z v) U := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by exact_mod_cast le_rfl)
  exact ((ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp_contDiffOn h1)

/-- Symmetry of mixed partial derivatives. -/
theorem c03s_aux_mixed {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ × ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {x : ℝ × ℝ} (hx : x ∈ U) :
    fderiv ℝ (fun z => fderiv ℝ f z (0, 1)) x (1, 0) =
      fderiv ℝ (fun z => fderiv ℝ f z (1, 0)) x (0, 1) := by
  have hfx : ContDiffAt ℝ (⊤ : ℕ∞) f x := hf.contDiffAt (hU.mem_nhds hx)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ f) x :=
      hfx.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_rfl)
    exact this.differentiableAt (by simp)
  have hsymm := hfx.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [fderiv_clm_apply h2 (differentiableAt_const _), fderiv_clm_apply h2 (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm (1, 0) (0, 1)

/-- `ρ` is linear in the amplitude. -/
theorem c03s_aux_rho_smul (p μ : ℝ) (k : ℂ) (d : ℝ → ℂ) :
    c03_sp_rho p μ (fun s => k * d s) = k * c03_sp_rho p μ d := by
  unfold c03_sp_rho
  simp_rw [mul_assoc k, integral_const_mul]
  ring

/-- The Pascal-type reindexing used in the Euler recurrence. -/
theorem c03s_aux_pascal (X : ℕ → ℕ → ℂ) (r : ℂ) (l : ℕ) :
    ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * r ^ i * (X i (l - i + 1) + r * X (i + 1) (l - i)) =
      ∑ i ∈ Finset.range (l + 2), ((l + 1).choose i : ℂ) * r ^ i * X i (l + 1 - i) := by
  have h1 : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * r ^ i * X i (l - i + 1) =
      ∑ i ∈ Finset.range (l + 1), (l.choose (i + 1) : ℂ) * r ^ (i + 1) * X (i + 1) (l - i) +
        X 0 (l + 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
      Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < l := Finset.mem_range.1 hi
    congr 2; omega
  rw [Finset.sum_range_succ' _ (l + 1)]
  simp only [Nat.choose_succ_succ, Nat.cast_add, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    one_mul, Nat.sub_zero, add_mul, Finset.sum_add_distrib]
  simp only [Nat.add_sub_add_right, Nat.succ_eq_add_one]
  simp only [mul_add, Finset.sum_add_distrib, h1]
  rw [show ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * r ^ i * (r * X (i + 1) (l - i)) =
    ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * r ^ (i + 1) * X (i + 1) (l - i) from
    Finset.sum_congr rfl fun i _ => by ring]
  ring

section recurrence
variable (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1)

/-- `Ψ_k(a')(y,μ) = ρ(μ; T^k(χ b_y[a']))`. -/
def c03s_aux_Psi (k : ℕ) (a : ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  c03_sp_rho p x.2 ((c03_sp_T p)^[k] (fun s => (χ s : ℂ) * c03_sp_b p m a x.1 s))

include hp hp1 hχ hχs hχ1 hχ01

/-- The amplitudes `T^k(χ b_y)` are smooth with support in `(1/2,2)`. -/
theorem c03s_aux_Tk_amp {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) {y : ℝ} (hy : 0 < y) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((c03_sp_T p)^[k] (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) ∧
    tsupport ((c03_sp_T p)^[k] (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) ⊆ Ioo (1 / 2) 2 := by
  have h0 := (c03_sp_near_rescaling p m hp hp1 χ hχ hχs hχ1 hχ01 a ha).1 y hy
  induction k with
  | zero => exact ⟨h0.1, h0.2.1⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, -⟩ := (c03_sp_T_bounds p hp hp1).1 _ ih.1 ih.2
    exact ⟨h1, h2⟩

/-- Joint smoothness of `Ψ_0`. -/
theorem c03s_aux_Psi0_smooth {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_Psi p m χ 0 a) (Ioi 0 ×ˢ Ioi 0) := by
  have hcf := c03s_aux_cfam_smooth p m hp hp1 hχ hχs ha
  have hχK : IsCompact (tsupport χ) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ)
    (hχs.trans Ioo_subset_Icc_self)
  have hJ := (c03_sp_J_parameter p hp hp1).2 (Ioi 0) (fun y s => (χ s : ℂ) * c03_sp_b p m a y s)
    isOpen_Ioi hcf (fun y₀ _ => ⟨1, one_pos, tsupport χ, hχK, hχs, fun y _ _ s hs => by
      simp [image_eq_zero_of_notMem_tsupport hs]⟩)
  exact hJ.2.2.1

/-- The `μ`-step: `Ψ_{k+1} = μ ∂_μ Ψ_k`. -/
theorem c03s_aux_Psi_mu {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) (k : ℕ) {x : ℝ × ℝ}
    (hx : x ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) (hd : DifferentiableAt ℝ (c03s_aux_Psi p m χ k a) x) :
    c03s_aux_Psi p m χ (k + 1) a x = (x.2 : ℂ) * fderiv ℝ (c03s_aux_Psi p m χ k a) x (0, 1) := by
  obtain ⟨hc, hcs⟩ := c03s_aux_Tk_amp p m hp hp1 χ hχ hχs hχ1 hχ01 ha (y := x.1) hx.1 k
  have hE := c03_sp_euler_identity p hp hp1 _ hc hcs x.2 hx.2
  have hpm := c03s_aux_partial_m hd
  unfold c03s_aux_Psi
  rw [Function.iterate_succ_apply', ← hE]
  congr 1
  exact hpm.deriv

/-- Joint smoothness of all `Ψ_k`. -/
theorem c03s_aux_Psi_smooth {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_Psi p m χ k a) (Ioi 0 ×ˢ Ioi 0) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  induction k with
  | zero => exact c03s_aux_Psi0_smooth p m hp hp1 χ hχ hχs hχ1 hχ01 ha
  | succ k ih =>
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × ℝ => (z.2 : ℂ) *
        fderiv ℝ (c03s_aux_Psi p m χ k a) z (0, 1)) (Ioi 0 ×ˢ Ioi 0) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_snd).mul
        (c03s_aux_dir_smooth hU ih (0, 1))
    refine h1.congr fun z hz => ?_
    exact c03s_aux_Psi_mu p m hp hp1 χ hχ hχs hχ1 hχ01 ha k hz
      ((ih.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

/-- The `y`-step: `y ∂_y Ψ_k(a) = Ψ_k(𝔈a)`. -/
theorem c03s_aux_Psi_y (k : ℕ) : ∀ {a : ℝ → ℂ}, a ∈ c03_sp_symbol m → ∀ {x : ℝ × ℝ},
    x ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) →
    (x.1 : ℂ) * fderiv ℝ (c03s_aux_Psi p m χ k a) x (1, 0) =
      c03s_aux_Psi p m χ k (c03s_aux_frakE p m a) x := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  induction k with
  | zero =>
    intro a ha x hx
    have hcf := c03s_aux_cfam_smooth p m hp hp1 hχ hχs ha
    have hχK : IsCompact (tsupport χ) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ)
      (hχs.trans Ioo_subset_Icc_self)
    have hJ := (c03_sp_J_parameter p hp hp1).2 (Ioi 0) (fun y s => (χ s : ℂ) * c03_sp_b p m a y s)
      isOpen_Ioi hcf (fun y₀ _ => ⟨1, one_pos, tsupport χ, hχK, hχs, fun y _ _ s hs => by
        simp [image_eq_zero_of_notMem_tsupport hs]⟩)
    have hF := (hJ.2.2.2 x.1 hx.1 x.2 hx.2)
    have hfd : fderiv ℝ (c03s_aux_Psi p m χ 0 a) x = _ := hF.fderiv
    rw [hfd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', one_smul, zero_smul, add_zero]
    rw [← c03s_aux_rho_smul]
    unfold c03s_aux_Psi
    simp only [Function.iterate_zero, id]
    congr 1
    funext s
    have hss := c03_sp_scaled_symbol p m hp hp1
    by_cases hs : 0 < s
    · have hbd : DifferentiableAt ℝ (fun y' => c03_sp_b p m a y' s) x.1 := by
        have := ((hss.1 a ha).1.contDiffAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds
          (show (x.1, s) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) from ⟨hx.1, hs⟩))).differentiableAt (by simp)
        exact this.comp x.1 ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 s)).differentiableAt
      rw [deriv_const_mul _ hbd]
      have h3 := (hss.1 a ha).2.2.1 x.1 s hx.1 hs
      have h4 := ((hss.1 a ha).2.2.2 1).2 x.1 s hx.1 hs
      simp only [Function.iterate_one] at h4
      rw [← h4, ← h3]; ring
    · have hχ0 : χ s = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hs (by linarith [(hχs h).1]))
      simp [hχ0]
  | succ k ih =>
    intro a ha x hx
    have hs := c03s_aux_Psi_smooth p m hp hp1 χ hχ hχs hχ1 hχ01 ha
    have hsE := c03s_aux_Psi_smooth p m hp hp1 χ hχ hχs hχ1 hχ01
      (c03s_aux_frakE_symbol p m hp ha)
    have hdiff : ∀ (k' : ℕ) (b : ℝ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) (c03s_aux_Psi p m χ k' b)
        (Ioi 0 ×ˢ Ioi 0) → ∀ z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        DifferentiableAt ℝ (c03s_aux_Psi p m χ k' b) z := fun k' b h z hz =>
      (h.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    set H : ℝ × ℝ → ℂ := fun z => fderiv ℝ (c03s_aux_Psi p m χ k a) z (0, 1) with hH
    set H' : ℝ × ℝ → ℂ := fun z => fderiv ℝ (c03s_aux_Psi p m χ k a) z (1, 0) with hH'
    have hHs : ContDiffOn ℝ (⊤ : ℕ∞) H (Ioi 0 ×ˢ Ioi 0) := c03s_aux_dir_smooth hU (hs k) (0, 1)
    have hH's : ContDiffOn ℝ (⊤ : ℕ∞) H' (Ioi 0 ×ˢ Ioi 0) := c03s_aux_dir_smooth hU (hs k) (1, 0)
    have hHd : DifferentiableAt ℝ H x := (hHs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hH'd : DifferentiableAt ℝ H' x :=
      (hH's.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    -- `Ψ_{k+1} = μ H` near `x`
    have hev : c03s_aux_Psi p m χ (k + 1) a =ᶠ[𝓝 x] fun z => (z.2 : ℂ) * H z := by
      filter_upwards [hU.mem_nhds hx] with z hz using
        c03s_aux_Psi_mu p m hp hp1 χ hχ hχs hχ1 hχ01 ha k hz (hdiff k a (hs k) z hz)
    have hGd : DifferentiableAt ℝ (fun z : ℝ × ℝ => (z.2 : ℂ) * H z) x :=
      ((Complex.ofRealCLM.differentiable.comp differentiable_snd) x).mul hHd
    have h1 : fderiv ℝ (c03s_aux_Psi p m χ (k + 1) a) x (1, 0) = (x.2 : ℂ) * fderiv ℝ H x (1, 0) := by
      rw [hev.fderiv_eq]
      have hA := c03s_aux_partial_y hGd
      have hB : HasDerivAt (fun y => ((y, x.2) : ℝ × ℝ).2 * H (y, x.2))
          ((x.2 : ℂ) * fderiv ℝ H x (1, 0)) x.1 := (c03s_aux_partial_y hHd).const_mul (x.2 : ℂ)
      exact hA.unique hB
    -- mixed partials
    have hmix : fderiv ℝ H x (1, 0) = fderiv ℝ H' x (0, 1) :=
      c03s_aux_mixed hU (hs k) hx
    -- `H' = Ψ_k(𝔈a)/y` near `x`
    have hev' : (fun μ => H' (x.1, μ)) =ᶠ[𝓝 x.2]
        fun μ => c03s_aux_Psi p m χ k (c03s_aux_frakE p m a) (x.1, μ) / (x.1 : ℂ) := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < x.2 from hx.2)] with μ hμ
      have := ih ha (x := (x.1, μ)) ⟨hx.1, hμ⟩
      rw [← this]
      have hx1' : (x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hx.1)
      simp only [hH']
      field_simp
    have h2 : fderiv ℝ H' x (0, 1) =
        fderiv ℝ (c03s_aux_Psi p m χ k (c03s_aux_frakE p m a)) x (0, 1) / (x.1 : ℂ) := by
      have hA := c03s_aux_partial_m hH'd
      have hB := ((c03s_aux_partial_m (hdiff k _ (hsE k) x hx)).div_const (x.1 : ℂ))
      exact hA.unique (hB.congr_of_eventuallyEq hev')
    have hx1 : (x.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hx.1)
    rw [h1, hmix, h2, c03s_aux_Psi_mu p m hp hp1 χ hχ hχs hχ1 hχ01
      (c03s_aux_frakE_symbol p m hp ha) k hx (hdiff k _ (hsE k) x hx)]
    field_simp

/-- Euler derivative of `y ↦ Ψ_i(a)(y, μ(y))`. -/
theorem c03s_aux_Phi_E {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) (i : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => c03s_aux_Psi p m χ i a (y, c03_sp_mu p y))
      (fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (1, 0) +
        ((1 + 1 / p) * y ^ (1 / p) : ℝ) *
          fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (0, 1)) y ∧
    (y : ℂ) * deriv (fun y => c03s_aux_Psi p m χ i a (y, c03_sp_mu p y)) y =
      c03s_aux_Psi p m χ i (c03s_aux_frakE p m a) (y, c03_sp_mu p y) +
        ((1 + 1 / p : ℝ) : ℂ) * c03s_aux_Psi p m χ (i + 1) a (y, c03_sp_mu p y) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hmu0 : 0 < c03_sp_mu p y := Real.rpow_pos_of_pos hy _
  have hx : (y, c03_sp_mu p y) ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := ⟨hy, hmu0⟩
  have hs := c03s_aux_Psi_smooth p m hp hp1 χ hχ hχs hχ1 hχ01 ha i
  have hd : DifferentiableAt ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) :=
    (hs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hmud : HasDerivAt (c03_sp_mu p) ((1 + 1 / p) * y ^ (1 / p)) y := by
    unfold c03_sp_mu
    have := Real.hasDerivAt_rpow_const (p := 1 + 1 / p) (Or.inl hy.ne')
    convert this using 2; ring
  have hc := hd.hasFDerivAt.comp_hasDerivAt y ((hasDerivAt_id y).prodMk hmud)
  have hlin : fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (1, (1 + 1 / p) * y ^ (1 / p)) =
      fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (1, 0) +
        ((1 + 1 / p) * y ^ (1 / p) : ℝ) *
          fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (0, 1) := by
    rw [show ((1 : ℝ), (1 + 1 / p) * y ^ (1 / p)) =
      ((1 : ℝ), (0 : ℝ)) + ((1 + 1 / p) * y ^ (1 / p)) • ((0 : ℝ), (1 : ℝ)) by
        ext <;> simp, map_add, map_smul, Complex.real_smul]
  have hD : HasDerivAt (fun y => c03s_aux_Psi p m χ i a (y, c03_sp_mu p y))
      (fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (1, 0) +
        ((1 + 1 / p) * y ^ (1 / p) : ℝ) *
          fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (0, 1)) y := by
    rw [← hlin]; exact hc
  refine ⟨hD, ?_⟩
  rw [hD.deriv, mul_add]
  have hy1 := c03s_aux_Psi_y p m hp hp1 χ hχ hχs hχ1 hχ01 i ha hx
  have hm1 := c03s_aux_Psi_mu p m hp hp1 χ hχ hχs hχ1 hχ01 ha i hx hd
  simp only at hy1 hm1
  rw [hy1, hm1]
  have hyy : y * ((1 + 1 / p) * y ^ (1 / p)) = (1 + 1 / p) * c03_sp_mu p y := by
    unfold c03_sp_mu
    rw [Real.rpow_add hy, Real.rpow_one]; ring
  have hyyC : (y : ℂ) * (((1 + 1 / p) * y ^ (1 / p) : ℝ) : ℂ) =
      ((1 + 1 / p : ℝ) : ℂ) * (c03_sp_mu p y : ℂ) := by
    rw [← Complex.ofReal_mul, hyy]; push_cast; ring
  linear_combination (fderiv ℝ (c03s_aux_Psi p m χ i a) (y, c03_sp_mu p y) (0, 1)) * hyyC

/-- The Euler recurrence in `Ψ` form. -/
theorem c03s_aux_rec_Psi {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) (l : ℕ) : ∀ y, 0 < y →
    (c03s_aux_E^[l] (fun y => c03s_aux_Psi p m χ 0 a (y, c03_sp_mu p y))) y =
      ∑ i ∈ Finset.range (l + 1), ((l.choose i : ℕ) : ℂ) * ((1 + 1 / p : ℝ) : ℂ) ^ i *
        c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i] a) (y, c03_sp_mu p y) := by
  have hsym : ∀ j, (c03s_aux_frakE p m)^[j] a ∈ c03_sp_symbol m := fun j =>
    (c03s_aux_frakE_iter_b p m hp ha j).1
  induction l with
  | zero => intro y _; simp
  | succ l ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    have hev : (c03s_aux_E^[l] (fun y => c03s_aux_Psi p m χ 0 a (y, c03_sp_mu p y))) =ᶠ[𝓝 y]
        fun y => ∑ i ∈ Finset.range (l + 1), ((l.choose i : ℕ) : ℂ) * ((1 + 1 / p : ℝ) : ℂ) ^ i *
          c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i] a) (y, c03_sp_mu p y) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz using ih z hz
    have hsum : HasDerivAt (fun y => ∑ i ∈ Finset.range (l + 1), ((l.choose i : ℕ) : ℂ) *
          ((1 + 1 / p : ℝ) : ℂ) ^ i *
          c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i] a) (y, c03_sp_mu p y))
        (∑ i ∈ Finset.range (l + 1), ((l.choose i : ℕ) : ℂ) * ((1 + 1 / p : ℝ) : ℂ) ^ i *
          deriv (fun y => c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i] a)
            (y, c03_sp_mu p y)) y) y :=
      HasDerivAt.fun_sum fun i _ =>
        ((c03s_aux_Phi_E p m hp hp1 χ hχ hχs hχ1 hχ01 (hsym (l - i)) i hy).1.const_mul _).congr_deriv
          (by rw [(c03s_aux_Phi_E p m hp hp1 χ hχ hχs hχ1 hχ01 (hsym (l - i)) i hy).1.deriv])
    change (y : ℂ) * deriv (c03s_aux_E^[l]
      (fun y => c03s_aux_Psi p m χ 0 a (y, c03_sp_mu p y))) y = _
    rw [hev.deriv_eq, hsum.deriv, Finset.mul_sum]
    have hterm : ∀ i ∈ Finset.range (l + 1), (y : ℂ) * (((l.choose i : ℕ) : ℂ) *
        ((1 + 1 / p : ℝ) : ℂ) ^ i * deriv (fun y => c03s_aux_Psi p m χ i
          ((c03s_aux_frakE p m)^[l - i] a) (y, c03_sp_mu p y)) y) =
        ((l.choose i : ℕ) : ℂ) * ((1 + 1 / p : ℝ) : ℂ) ^ i *
          (c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i + 1] a) (y, c03_sp_mu p y) +
            ((1 + 1 / p : ℝ) : ℂ) * c03s_aux_Psi p m χ (i + 1)
              ((c03s_aux_frakE p m)^[l - i] a) (y, c03_sp_mu p y)) := by
      intro i _
      rw [Function.iterate_succ_apply', ← (c03s_aux_Phi_E p m hp hp1 χ hχ hχs hχ1 hχ01
        (hsym (l - i)) i hy).2]
      ring
    rw [Finset.sum_congr rfl hterm]
    exact c03s_aux_pascal (fun i j => c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[j] a)
      (y, c03_sp_mu p y)) _ l

/-- Uniform `C^N` bounds for the localized rescaled amplitudes `χ b_y[𝔈^j a]`. -/
theorem c03s_aux_amp_norm (j N : ℕ) (Ck : ℕ → ℝ) : ∃ B, 0 ≤ B ∧ ∀ a ∈ c03_sp_symbol m,
    (∀ i ≤ j + N, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) → ∀ y, 0 < y →
    c03_Ck_normR N univ (fun s => (χ s : ℂ) * c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y s) ≤ B := by
  have hss := (c03_sp_scaled_symbol p m hp hp1).2.2
  choose D hD using fun k => hss j k Ck
  have hχC : ContDiff ℝ (⊤ : ℕ∞) (fun s => ((χ s : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hχK : IsCompact (tsupport χ) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ)
    (hχs.trans Ioo_subset_Icc_self)
  have hχcs : HasCompactSupport (fun s => ((χ s : ℝ) : ℂ)) :=
    HasCompactSupport.intro hχK (fun s hs => by simp [image_eq_zero_of_notMem_tsupport hs])
  have hX : ∀ r : ℕ, ∃ X, ∀ s, ‖iteratedDeriv r (fun s => ((χ s : ℝ) : ℂ)) s‖ ≤ X := by
    intro r
    have hcs : HasCompactSupport (iteratedDeriv r (fun s => ((χ s : ℝ) : ℂ))) := by
      rw [iteratedDeriv_eq_iterate]
      clear hD
      induction r with
      | zero => simpa using hχcs
      | succ n ih => rw [Function.iterate_succ_apply']; exact ih.deriv
    exact (hχC.continuous_iteratedDeriv r (by exact_mod_cast le_top)).bounded_above_of_compact_support hcs
  choose X hX using hX
  set Xs : ℝ := ∑ r ∈ Finset.range (N + 1), |X r| with hXs
  set Dsum : ℝ := ∑ k ∈ Finset.range (N + 1), |D k| with hDsum
  have hXs0 : 0 ≤ Xs := Finset.sum_nonneg fun r _ => abs_nonneg _
  have hDs0 : 0 ≤ Dsum := Finset.sum_nonneg fun r _ => abs_nonneg _
  have hXr : ∀ r ≤ N, ∀ s, ‖iteratedDeriv r (fun s => ((χ s : ℝ) : ℂ)) s‖ ≤ Xs := fun r hr s =>
    (hX r s).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun r => |X r|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hr))))
  refine ⟨(N + 1) * (2 ^ N * (Xs * Dsum)), by positivity, fun a ha hCk y hy => ?_⟩
  have hsym := (c03s_aux_frakE_iter_b p m hp ha j)
  refine c03s_aux_Ck_norm_le (by positivity) fun n hn s => ?_
  by_cases hs : s ∈ tsupport χ
  · have hs0 : 0 < s := by linarith [(hχs hs).1]
    have hsI : s ∈ Icc (1 / 2 : ℝ) 2 := Ioo_subset_Icc_self (hχs hs)
    have hbs : ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y) (Ioi 0) :=
      ((c03_sp_scaled_symbol p m hp hp1).1 _ hsym.1).1.comp (f := fun s => (y, s))
        (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => ⟨hy, hs⟩)
    refine (c03s_aux_leibniz hχC.contDiffOn hbs hs0 n).trans ?_
    calc ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) *
          ‖iteratedDeriv r (fun s => ((χ s : ℝ) : ℂ)) s‖ *
          ‖iteratedDeriv (n - r) (c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y) s‖
        ≤ ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * Xs * Dsum := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
          have hev : (c03s_aux_frakE p m)^[j] (c03_sp_b p m a y) =ᶠ[𝓝 s]
              c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y := by
            filter_upwards [Ioi_mem_nhds hs0] with z hz using hsym.2 y z hy hz
          have h1 : ‖iteratedDeriv (n - r) (c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y) s‖ ≤
              Dsum := by
            rw [← (hev.iteratedDeriv (n - r)).eq_of_nhds]
            refine (hD (n - r) a ha (fun i hi ξ hξ => hCk i (by omega) ξ hξ) y hy s hsI).trans ?_
            exact (le_abs_self _).trans (Finset.single_le_sum (f := fun k => |D k|)
              (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega)))
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hXr r (by omega) s) (by positivity)) h1
            (norm_nonneg _) (mul_nonneg (by positivity) hXs0)
      _ = 2 ^ n * (Xs * Dsum) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have : ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]; ring
      _ ≤ 2 ^ N * (Xs * Dsum) := by
          gcongr
          · norm_num
  · rw [c03s_aux_iter_zero_off (isClosed_tsupport χ) (fun s hs => by
      simp [image_eq_zero_of_notMem_tsupport hs]) n hs, norm_zero]
    positivity

end recurrence

/-- Iterated `T` norm bound. -/
theorem c03s_aux_Titer_norm (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (CT : ℕ → ℝ) (hCT : ∀ k, 0 < CT k)
    (hT : ∀ k, ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      c03_Ck_normR k univ (c03_sp_T p c) ≤ CT k * c03_Ck_normR (k + 1) univ c) (i : ℕ) :
    ∀ k : ℕ, ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      c03_Ck_normR k univ ((c03_sp_T p)^[i] c) ≤
        (∏ t ∈ Finset.range i, CT (k + t)) * c03_Ck_normR (k + i) univ c := by
  induction i with
  | zero => intro k c _ _; simp
  | succ i ih =>
    intro k c hc hcs
    obtain ⟨h1, h2, -⟩ := (c03_sp_T_bounds p hp hp1).1 c hc hcs
    rw [Function.iterate_succ_apply]
    refine (ih k _ h1 h2).trans ?_
    have hP : 0 ≤ ∏ t ∈ Finset.range i, CT (k + t) :=
      Finset.prod_nonneg fun t _ => (hCT _).le
    calc (∏ t ∈ Finset.range i, CT (k + t)) * c03_Ck_normR (k + i) univ (c03_sp_T p c)
        ≤ (∏ t ∈ Finset.range i, CT (k + t)) * (CT (k + i) * c03_Ck_normR (k + i + 1) univ c) :=
          mul_le_mul_of_nonneg_left (hT _ c hc hcs) hP
      _ = _ := by rw [Finset.prod_range_succ, ← add_assoc]; ring

/-- Blueprint: lem:c03_sp_near_euler_recurrence.  With `F(y) = ρ(μ(y); χ_sp b_y)` and `E = y∂_y`:
`E^l F = ∑_{i ≤ l} C(l,i) (1+1/p)^i ρ(μ; T^i(χ_sp 𝔈^{l-i} b_y))`, and
`|E^l F(y)| ≤ C_l μ(y)⁻¹` for all `y > 0`, `C_l = C_l(p,m,χ_sp,C_0,…,C_{l+4})`. -/
theorem c03_sp_near_euler_recurrence (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) :
    (∀ a ∈ c03_sp_symbol m, ∀ l : ℕ, ∀ y, 0 < y →
      (c03s_aux_E^[l] (fun y' => c03_sp_rho p (c03_sp_mu p y')
          (fun s => (χ s : ℂ) * c03_sp_b p m a y' s))) y =
        ∑ i ∈ Finset.range (l + 1), ((l.choose i : ℕ) : ℂ) * ((1 + 1 / p : ℝ) : ℂ) ^ i *
          c03_sp_rho p (c03_sp_mu p y) ((c03_sp_T p)^[i]
            (fun s => (χ s : ℂ) * ((c03s_aux_frakE p m)^[l - i] (c03_sp_b p m a y)) s))) ∧
    ∀ l : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ k ≤ l + 4, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ y, 0 < y →
        ‖(c03s_aux_E^[l] (fun y' => c03_sp_rho p (c03_sp_mu p y')
          (fun s => (χ s : ℂ) * c03_sp_b p m a y' s))) y‖ ≤ C * (c03_sp_mu p y)⁻¹ := by
  -- the amplitudes agree with the rescalings of `𝔈^j a`
  have hamp : ∀ a ∈ c03_sp_symbol m, ∀ j y, 0 < y →
      (fun s => (χ s : ℂ) * ((c03s_aux_frakE p m)^[j] (c03_sp_b p m a y)) s) =
        fun s => (χ s : ℂ) * c03_sp_b p m ((c03s_aux_frakE p m)^[j] a) y s := by
    intro a ha j y hy
    funext s
    by_cases hs : 0 < s
    · rw [(c03s_aux_frakE_iter_b p m hp ha j).2 y s hy hs]
    · have : χ s = 0 := image_eq_zero_of_notMem_tsupport (fun h => hs (by linarith [(hχs h).1]))
      simp [this]
  have hid : ∀ a ∈ c03_sp_symbol m, ∀ l : ℕ, ∀ y, 0 < y →
      (c03s_aux_E^[l] (fun y' => c03_sp_rho p (c03_sp_mu p y')
          (fun s => (χ s : ℂ) * c03_sp_b p m a y' s))) y =
        ∑ i ∈ Finset.range (l + 1), ((l.choose i : ℕ) : ℂ) * ((1 + 1 / p : ℝ) : ℂ) ^ i *
          c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i] a) (y, c03_sp_mu p y) := fun a ha l y hy =>
    c03s_aux_rec_Psi p m hp hp1 χ hχ hχs hχ1 hχ01 ha l y hy
  refine ⟨fun a ha l y hy => ?_, fun l Ck => ?_⟩
  · rw [hid a ha l y hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hamp a ha (l - i) y hy]
    rfl
  -- the bound
  obtain ⟨Cc, hCc, hcomp⟩ := c03s_c03_sp_compact p hp hp1
  choose CT hCT hT using (c03_sp_T_bounds p hp hp1).2
  choose B hB0 hB using fun i : ℕ => c03s_aux_amp_norm p m hp hp1 χ hχ hχs hχ1 hχ01 (l - i) (3 + i) Ck
  set r : ℝ := 1 + 1 / p with hr
  have hr0 : 0 < r := by positivity
  set K : ℝ := ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * r ^ i *
    (Cc * ((∏ t ∈ Finset.range i, CT (3 + t)) * B i)) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
    (mul_nonneg hCc.le (mul_nonneg (Finset.prod_nonneg fun t _ => (hCT _).le) (hB0 i)))
  refine ⟨K + 1, by positivity, fun a ha hCk y hy => ?_⟩
  have hmu0 : 0 < c03_sp_mu p y := Real.rpow_pos_of_pos hy _
  rw [hid a ha l y hy]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (l + 1), ‖((l.choose i : ℕ) : ℂ) * ((1 + 1 / p : ℝ) : ℂ) ^ i *
      c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i] a) (y, c03_sp_mu p y)‖ ≤
      (l.choose i : ℝ) * r ^ i * (Cc * ((∏ t ∈ Finset.range i, CT (3 + t)) * B i)) *
        (c03_sp_mu p y)⁻¹ := by
    intro i hi
    have hi' : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hsym := (c03s_aux_frakE_iter_b p m hp ha (l - i)).1
    obtain ⟨hc, hcs⟩ := c03s_aux_Tk_amp p m hp hp1 χ hχ hχs hχ1 hχ01 hsym hy i
    obtain ⟨hc0, hcs0⟩ := c03s_aux_Tk_amp p m hp hp1 χ hχ hχs hχ1 hχ01 hsym hy 0
    simp only [Function.iterate_zero, id] at hc0 hcs0
    have h3top : (3 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      show ((3 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2 le_top
    have h1 := hcomp (c03_sp_mu p y) hmu0 _ (hc.of_le h3top) hcs
    have h2 := c03s_aux_Titer_norm p hp hp1 CT hCT hT i 3 _ hc0 hcs0
    have h3 := hB i a ha (fun i' hi'' ξ hξ => hCk i' (by omega) ξ hξ) y hy
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
    have hP : 0 ≤ ∏ t ∈ Finset.range i, CT (3 + t) := Finset.prod_nonneg fun t _ => (hCT _).le
    have hmuinv : 0 ≤ (c03_sp_mu p y)⁻¹ := by positivity
    calc (l.choose i : ℝ) * r ^ i * ‖c03s_aux_Psi p m χ i ((c03s_aux_frakE p m)^[l - i] a)
          (y, c03_sp_mu p y)‖
        ≤ (l.choose i : ℝ) * r ^ i * (Cc * (c03_sp_mu p y)⁻¹ *
            ((∏ t ∈ Finset.range i, CT (3 + t)) * B i)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
          refine mul_le_mul_of_nonneg_left (h2.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 hP
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have : 0 ≤ (c03_sp_mu p y)⁻¹ := by positivity
  nlinarith

/-- Blueprint: lem:c03_euler_to_deriv.  With `∏_{r<j}(X - r) = ∑_l a_{j,l} X^l`
(`descPochhammer`): `y^j F^{(j)}(y) = ∑_l a_{j,l} E^l F(y)` for `y > 0`; hence bounds
`|E^l F| ≤ B_l y^σ` (`y ≥ 1`, `l ≤ j`) give `|F^{(j)}(y)| ≤ (∑_l |a_{j,l}| B_l) y^{σ-j}`. -/
theorem c03_euler_to_deriv (F : ℝ → ℂ) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Ioi 0)) (j : ℕ) :
    (∀ y : ℝ, 0 < y → (y : ℂ) ^ j * iteratedDeriv j F y =
      ∑ l ∈ Finset.range (j + 1), (((descPochhammer ℤ j).coeff l : ℤ) : ℂ) * (c03s_aux_E^[l] F) y) ∧
    ∀ (σ : ℝ) (B : ℕ → ℝ), (∀ l ≤ j, 0 ≤ B l) →
      (∀ l ≤ j, ∀ y, 1 ≤ y → ‖(c03s_aux_E^[l] F) y‖ ≤ B l * y ^ σ) →
      ∀ y, 1 ≤ y → ‖iteratedDeriv j F y‖ ≤
        (∑ l ∈ Finset.range (j + 1), |(((descPochhammer ℤ j).coeff l : ℤ) : ℝ)| * B l) *
          y ^ (σ - j) := by
  have hid : ∀ j : ℕ, ∀ y : ℝ, 0 < y → (y : ℂ) ^ j * iteratedDeriv j F y =
      ∑ l ∈ Finset.range (j + 1), (((descPochhammer ℤ j).coeff l : ℤ) : ℂ) * (c03s_aux_E^[l] F) y := by
    intro j
    induction j with
    | zero => intro y hy; simp
    | succ j ih =>
      intro y hy
      set c : ℕ → ℕ → ℂ := fun j l => (((descPochhammer ℤ j).coeff l : ℤ) : ℂ) with hc
      set G : ℝ → ℂ := fun y => ∑ l ∈ Finset.range (j + 1), c j l * (c03s_aux_E^[l] F) y with hG
      have hdl : ∀ l, HasDerivAt (c03s_aux_E^[l] F) (deriv (c03s_aux_E^[l] F) y) y := fun l =>
        (((c03s_aux_E_iter_contDiffOn hF l).contDiffAt (Ioi_mem_nhds hy)).differentiableAt
          (by simp)).hasDerivAt
      have hGd : HasDerivAt G (∑ l ∈ Finset.range (j + 1), c j l * deriv (c03s_aux_E^[l] F) y) y :=
        HasDerivAt.fun_sum fun l _ => (hdl l).const_mul _
      have hH : HasDerivAt (fun y : ℝ => (y : ℂ) ^ j * iteratedDeriv j F y)
          ((j : ℂ) * (y : ℂ) ^ (j - 1) * iteratedDeriv j F y +
            (y : ℂ) ^ j * iteratedDeriv (j + 1) F y) y := by
        have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ j) ((j : ℂ) * (y : ℂ) ^ (j - 1)) y := by
          have := ((hasDerivAt_id y).ofReal_comp).pow j
          convert this using 1
          · funext z; simp
          · simp
        exact h1.mul (c03s_aux_hasDerivAt_iteratedDeriv hF j hy)
      have hev : (fun y : ℝ => (y : ℂ) ^ j * iteratedDeriv j F y) =ᶠ[𝓝 y] G := by
        filter_upwards [Ioi_mem_nhds hy] with z hz using ih z hz
      have huniq := (hH.congr_of_eventuallyEq hev.symm).unique hGd
      -- expand the new sum
      rw [Finset.sum_range_succ']
      simp only [Function.iterate_succ_apply', c03s_aux_E]
      have e1 : ∀ l ∈ Finset.range (j + 1), c (j + 1) (l + 1) * ((y : ℂ) *
          deriv (c03s_aux_E^[l] F) y) = c j l * ((y : ℂ) * deriv (c03s_aux_E^[l] F) y) -
          (j : ℂ) * (c j (l + 1) * ((y : ℂ) * deriv (c03s_aux_E^[l] F) y)) := by
        intro l _; rw [hc]; simp only; rw [c03s_aux_coeff_succ]; ring
      rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hc0 := c03s_aux_coeff_zero j
      have hsum : ∑ l ∈ Finset.range (j + 1), c j (l + 1) * ((y : ℂ) *
          deriv (c03s_aux_E^[l] F) y) + c j 0 * (c03s_aux_E^[0] F) y = G y := by
        have htop : c j (j + 1) = 0 := by rw [hc]; simp [c03s_aux_coeff_top]
        have : G y = ∑ l ∈ Finset.range (j + 2), c j l * (c03s_aux_E^[l] F) y := by
          rw [Finset.sum_range_succ _ (j + 1), htop, zero_mul, add_zero]
        rw [this]
        conv_rhs => rw [Finset.sum_range_succ']
        simp only [Function.iterate_succ_apply', c03s_aux_E]
      have hS1 : ∑ l ∈ Finset.range (j + 1), c j l * ((y : ℂ) * deriv (c03s_aux_E^[l] F) y) =
          (y : ℂ) * ∑ l ∈ Finset.range (j + 1), c j l * deriv (c03s_aux_E^[l] F) y := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => by ring
      have hpow : (y : ℂ) * ((j : ℂ) * (y : ℂ) ^ (j - 1)) = (j : ℂ) * (y : ℂ) ^ j := by
        rcases j with _ | j
        · simp
        · simp [pow_succ]; ring
      rw [hc0]
      have ihy := ih y hy
      linear_combination (-1 : ℂ) * hS1 + (j : ℂ) * hsum + (y : ℂ) * huniq - (j : ℂ) * ihy -
        iteratedDeriv j F y * hpow
  refine ⟨hid j, fun σ B hB hbd y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have h1 : ‖(y : ℂ) ^ j * iteratedDeriv j F y‖ ≤
      (∑ l ∈ Finset.range (j + 1), |(((descPochhammer ℤ j).coeff l : ℤ) : ℝ)| * B l) * y ^ σ := by
    rw [hid j y hy0, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    have hl' : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    rw [norm_mul, Complex.norm_intCast, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd l hl' y hy) (abs_nonneg _)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0] at h1
  have hyj : 0 < y ^ j := pow_pos hy0 j
  rw [Real.rpow_sub hy0, Real.rpow_natCast, mul_div_assoc', le_div_iff₀ hyj, mul_comm]
  exact h1

/-- Blueprint: lem:c03_sp_near (prefixed copy of `GSQG.c03_sp_near`). -/
-- Includes the smoothness conjunct for `λ₀^m ρ(μ;c_y)`, as in `GSQG.c03_sp_near`.
theorem c03s_c03_sp_near (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) :
    (∀ Ck : ℕ → ℝ, ∀ a ∈ c03_sp_symbol m,
      (∀ k : ℕ, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) → ∀ y, 0 < y →
      (∀ k : ℕ, ∀ s, 0 < s → ‖iteratedDeriv k (c03_sp_b p m a y) s‖ ≤ Ck k * s ^ (m - k)) ∧
      (∀ s, 0 < s → (y : ℂ) * deriv (fun y' => c03_sp_b p m a y' s) y =
        (1 / p : ℂ) * (-(m : ℂ) * c03_sp_b p m a y s + (s : ℂ) * deriv (c03_sp_b p m a y) s))) ∧
    (∀ a ∈ c03_sp_symbol m, ∀ y, 0 < y →
      c03_sp_Inear p χ a y / c03_sp_P p y - a (lambda0 p y) =
        ((lambda0 p y ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) ∧
    (∀ a ∈ c03_sp_symbol m, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((lambda0 p y ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) (Ioi 0)) ∧
    ∀ j : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ k ≤ j + 4, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ y, 1 ≤ y → ‖iteratedDeriv j (fun y' => ((lambda0 p y' ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y') (fun s => (χ s : ℂ) * c03_sp_b p m a y' s)) y‖ ≤
        C * lambda0 p y ^ (m - p - 1) * y ^ (-(j : ℝ)) := by
  have hss := c03_sp_scaled_symbol p m hp hp1
  have hres := c03_sp_near_rescaling p m hp hp1 χ hχ hχs hχ1 hχ01
  have hrec := c03_sp_near_euler_recurrence p m hp hp1 χ hχ hχs hχ1 hχ01
  -- `F(y) = ρ(μ(y); χ b_y)` and `Λ(y) = y^{m/p}`
  set F : (ℝ → ℂ) → ℝ → ℂ := fun a y => c03_sp_rho p (c03_sp_mu p y)
    (fun s => (χ s : ℂ) * c03_sp_b p m a y s) with hFdef
  have hlam : ∀ y : ℝ, 0 < y → lambda0 p y ^ m = y ^ (m / p) := by
    intro y hy; unfold lambda0; rw [← Real.rpow_mul hy.le]; ring_nf
  have hFs : ∀ a ∈ c03_sp_symbol m, ContDiffOn ℝ (⊤ : ℕ∞) (F a) (Ioi 0) := by
    intro a ha
    have h1 := (c03s_aux_ofReal_rpow (-(m / p))).1.mul (hres a ha).2.2
    refine h1.congr fun y hy => ?_
    have hy : (0 : ℝ) < y := hy
    simp only [hFdef]
    rw [← mul_assoc, hlam y hy, ← Complex.ofReal_mul, ← Real.rpow_add hy]
    simp
  refine ⟨fun Ck a ha hCk y hy => ⟨fun k s hs => (hss.2.1 Ck a ha hCk k y s hy hs),
      fun s hs => by rw [(hss.1 a ha).2.2.1 y s hy hs]; rfl⟩,
    fun a ha y hy => ((hres a ha).1 y hy).2.2.2.2, fun a ha => (hres a ha).2.2, ?_⟩
  intro j Ck
  choose CR hCR hRb using fun l => hrec.2 l Ck
  set σ : ℝ := -(1 + 1 / p) with hσ
  set Bk : ℕ → ℝ := fun k => ∑ l ∈ Finset.range (k + 1),
    |(((descPochhammer ℤ k).coeff l : ℤ) : ℝ)| * CR l with hBk
  have hBk0 : ∀ k, 0 ≤ Bk k := fun k => Finset.sum_nonneg fun l _ =>
    mul_nonneg (abs_nonneg _) (hCR l).le
  refine ⟨1 + ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      |(descPochhammer ℝ i).eval (m / p)| * Bk (j - i),
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (hBk0 _)), ?_⟩
  intro a ha hCk y hy
  have hy0 : 0 < y := by linarith
  -- derivative bounds for `F`
  have hFb : ∀ k ≤ j, ‖iteratedDeriv k (F a) y‖ ≤ Bk k * y ^ (σ - k) := by
    intro k hk
    refine (c03_euler_to_deriv (F a) (hFs a ha) k).2 σ CR (fun l _ => (hCR l).le) ?_ y hy
    intro l hl z hz
    have hz0 : 0 < z := by linarith
    have := hRb l a ha (fun k' hk' ξ hξ => hCk k' (by omega) ξ hξ) z hz0
    refine this.trans_eq ?_
    unfold c03_sp_mu
    rw [hσ, Real.rpow_neg hz0.le]
  have hev : (fun y' => ((lambda0 p y' ^ m : ℝ) : ℂ) * F a y') =ᶠ[𝓝 y]
      (fun y' => ((y' ^ (m / p) : ℝ) : ℂ) * F a y') := by
    filter_upwards [Ioi_mem_nhds hy0] with z hz using by rw [hlam z hz]
  change ‖iteratedDeriv j (fun y' => ((lambda0 p y' ^ m : ℝ) : ℂ) * F a y') y‖ ≤ _
  rw [(hev.iteratedDeriv j).eq_of_nhds]
  have hT : lambda0 p y ^ (m - p - 1) * y ^ (-(j : ℝ)) = y ^ (m / p + σ - j) := by
    unfold lambda0
    rw [← Real.rpow_mul hy0.le, ← Real.rpow_add hy0, hσ]
    congr 1; field_simp; ring
  rw [mul_assoc, hT]
  refine (c03s_aux_leibniz (c03s_aux_ofReal_rpow (m / p)).1 (hFs a ha) hy0 j).trans ?_
  have hpos : 0 ≤ y ^ (m / p + σ - j) := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hpos)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [(c03s_aux_ofReal_rpow (m / p)).2 i y hy0]
  have h2 := hFb (j - i) (Nat.sub_le j i)
  calc (j.choose i : ℝ) * (|(descPochhammer ℝ i).eval (m / p)| * y ^ (m / p - i)) *
        ‖iteratedDeriv (j - i) (F a) y‖
      ≤ (j.choose i : ℝ) * (|(descPochhammer ℝ i).eval (m / p)| * y ^ (m / p - i)) *
        (Bk (j - i) * y ^ (σ - ((j - i : ℕ) : ℝ))) := by gcongr
    _ = (j.choose i : ℝ) * |(descPochhammer ℝ i).eval (m / p)| * Bk (j - i) *
        (y ^ (m / p - i) * y ^ (σ - ((j - i : ℕ) : ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hy0, Nat.cast_sub hi']
      congr 2; ring

end GSQG
