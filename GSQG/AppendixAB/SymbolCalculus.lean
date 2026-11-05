import GSQG.AppendixAB.PhaseToolbox
import GSQG.Auxiliary.SpecialIntegrals

/-!
# Appendices A–B: shared symbol calculus, iterated integration by parts, fractional Fourier

Blueprint sublemmas of `03_analysis_appendix.tex` (with their blueprint Lean names), plus proofs of
the nodes `c03_frac_kernel_formula`, `c03_nonsmooth_symbol_bounds`,
`c03_power_singularity_decay`, `appendix_nonsmooth_fourier_inverse` and `c03_ibp_homogeneous` under
the prefix `c03c_` (`c03c_X` has exactly the statement of the public `GSQG.X` in `AppendixAB/Statements.lean` or
`Sec4_Analysis/Equation.lean`, which prove `X` by `c03c_X`). Helpers: `c03c_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section


namespace GSQG




/-! ## Data definitions used in the statements below -/

open Classical in
/-- Blueprint: lem:c03_ibp_compact_iteration.  The integration-by-parts operator
`L_φ a = (a/(iφ'))'` on `U`, and `0` outside `U`. -/
def c03c_ibpL (U : Set ℝ) (φ : ℝ → ℝ) (a : ℝ → ℂ) : ℝ → ℂ := fun x =>
  if x ∈ U then deriv (fun t => a t / (Complex.I * ((deriv φ t : ℝ) : ℂ))) x else 0

/-- Blueprint: lem:c03_homogeneous_cutoff_symbol.
`g_{η,Λ}(z) = (1 - χ₁(Λz)) e^{-ηz²} b(z) |z|^{-1-p}` (the value at `z = 0` is `0`). -/
def c03c_homg (p : ℝ) (χ₁ : ℝ → ℝ) (Λ η : ℝ) (b : ℝ → ℂ) (z : ℝ) : ℂ :=
  (((1 - χ₁ (Λ * z)) * Real.exp (-(η * z ^ 2)) : ℝ) : ℂ) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ)

/-- Blueprint: lem:c03_exp_jet_recursion.  `E₀ = 1`, `E_{n+1} = E_n' + iΘ'E_n`. -/
def c03c_expJet (Θ : ℝ → ℝ) : ℕ → ℝ → ℂ
  | 0 => fun _ => 1
  | n + 1 => fun x => deriv (c03c_expJet Θ n) x + Complex.I * ((deriv Θ x : ℝ) : ℂ) * c03c_expJet Θ n x

/-- Blueprint: lem:c03_sp_far_symbol_iteration.  `a₀(y,ξ) = a(ξ)(1 - χ_sp(ξ/λ₀(y)))`,
`a_{n+1}(y,ξ) = ∂_ξ (a_n(y,ξ)/(i(y - ξ^p)))` (Lean's `x/0 = 0` gives the value zero at the
critical point, where the numerator vanishes on a neighbourhood). -/
def c03c_farAmp (p : ℝ) (χ : ℝ → ℝ) (a : ℝ → ℂ) : ℕ → ℝ → ℝ → ℂ
  | 0 => fun y ξ => a ξ * ((1 - χ (ξ / lambda0 p y) : ℝ) : ℂ)
  | n + 1 => fun y ξ => deriv (fun ξ' => c03c_farAmp p χ a n y ξ' /
      (Complex.I * ((y - ξ' ^ p : ℝ) : ℂ))) ξ

/-! ## Shared finite-order symbol and integration-by-parts interfaces -/

/-- The recurrence `D₀ = 1`, `D_j = 1 + ∑_{l=1}^j binom(j,l) A_l D_{j-l}`. -/
def c03c_aux_recD (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => 1 + ∑ i ∈ Finset.range (k + 1),
      ((k + 1).choose (i + 1) : ℝ) * A (i + 1) * c03c_aux_recD A (k - i)
decreasing_by omega

theorem c03c_aux_recD_ge_one (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (j : ℕ) : 1 ≤ c03c_aux_recD A j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => simp [c03c_aux_recD]
    | succ k =>
      rw [c03c_aux_recD]
      have : 0 ≤ ∑ i ∈ Finset.range (k + 1),
          ((k + 1).choose (i + 1) : ℝ) * A (i + 1) * c03c_aux_recD A (k - i) := by
        refine Finset.sum_nonneg fun i hi => ?_
        have := ih (k - i) (by omega)
        have := hA (i + 1)
        positivity
      linarith

/-- Blueprint: lem:c03_reciprocal_symbol.  If `|v| ≥ λ` and `|v^{(j)}| ≤ A_j λ w^{-j}` on an open
`U` (`1 ≤ j ≤ n`), then `1/v ∈ C^n(U)` and `|(1/v)^{(j)}| ≤ D_j λ⁻¹ w^{-j}` (`0 ≤ j ≤ n`), with
`D_j` depending only on `A` (`D` is chosen before `n`, `U`, `v`, `λ`, `w`; no regularity of `w`). -/
-- Encoding: `D_j = D_j(A_1,…,A_j)` is encoded as `D` chosen after the whole
-- sequence `A` but before `n`; the proof's recurrence `D_j = 1 + ∑ binom(j,l) A_l D_{j-l}` only
-- uses `A_1,…,A_j`.
theorem c03_reciprocal_symbol (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 < D j) ∧
      ∀ (n : ℕ) (U : Set ℝ) (v : ℝ → ℂ) (lam : ℝ) (w : ℝ → ℝ),
        IsOpen U → ContDiffOn ℝ n v U → 0 < lam → (∀ x ∈ U, 0 < w x) →
        (∀ x ∈ U, lam ≤ ‖v x‖) →
        (∀ x ∈ U, ∀ j, 1 ≤ j → j ≤ n → ‖iteratedDeriv j v x‖ ≤ A j * lam / w x ^ j) →
        ContDiffOn ℝ n (fun x => (v x)⁻¹) U ∧
        ∀ x ∈ U, ∀ j ≤ n, ‖iteratedDeriv j (fun x => (v x)⁻¹) x‖ ≤ D j * lam⁻¹ / w x ^ j := by
  refine ⟨c03c_aux_recD A, fun j => lt_of_lt_of_le one_pos (c03c_aux_recD_ge_one A hA j), ?_⟩
  intro n U v lam w hU hv hlam hw hvl hvd
  have hv0 : ∀ x ∈ U, v x ≠ 0 := fun x hx h => by
    have := hvl x hx; rw [h, norm_zero] at this; linarith
  have hu : ContDiffOn ℝ n (fun x => (v x)⁻¹) U := hv.inv hv0
  refine ⟨hu, ?_⟩
  intro x hx
  set u : ℝ → ℂ := fun x => (v x)⁻¹ with hudef
  have hvx : ContDiffAt ℝ n v x := hv.contDiffAt (hU.mem_nhds hx)
  have hux : ContDiffAt ℝ n u x := hu.contDiffAt (hU.mem_nhds hx)
  have hwx := hw x hx
  have hvlx := hvl x hx
  -- the Leibniz identity
  have hprod : ∀ j, 1 ≤ j → j ≤ n → ∑ i ∈ Finset.range (j + 1),
      (j.choose i : ℂ) * iteratedDeriv i v x * iteratedDeriv (j - i) u x = 0 := by
    intro j hj hjn
    have hcj : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hjn
    rw [← iteratedDeriv_mul (hvx.of_le hcj) (hux.of_le hcj)]
    have hev : (v * u) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      simp [hudef, mul_inv_cancel₀ (hv0 y hy)]
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  intro j hjn
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero =>
      simp only [iteratedDeriv_zero, pow_zero, div_one]
      rw [c03c_aux_recD, one_mul, norm_inv]
      exact inv_anti₀ hlam hvlx
    | succ k =>
      have hid := hprod (k + 1) (by omega) hjn
      rw [Finset.sum_range_succ'] at hid
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
        Nat.sub_zero] at hid
      -- v x * u^{(k+1)} = - ∑ ...
      have hkey : v x * iteratedDeriv (k + 1) u x = -∑ i ∈ Finset.range (k + 1),
          ((k + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) v x *
            iteratedDeriv (k + 1 - (i + 1)) u x := by
        linear_combination hid
      have hsum : ‖∑ i ∈ Finset.range (k + 1),
          ((k + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) v x *
            iteratedDeriv (k + 1 - (i + 1)) u x‖ ≤
          ∑ i ∈ Finset.range (k + 1), ((k + 1).choose (i + 1) : ℝ) * A (i + 1) *
            c03c_aux_recD A (k - i) / w x ^ (k + 1) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [Finset.mem_range] at hi
        have h1 := hvd x hx (i + 1) (by omega) (by omega)
        have h2 := ih (k - i) (by omega) (by omega)
        have hki : k + 1 - (i + 1) = k - i := by omega
        rw [hki]
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        have hA' := hA (i + 1)
        have hD := c03c_aux_recD_ge_one A hA (k - i)
        calc ((k + 1).choose (i + 1) : ℝ) * ‖iteratedDeriv (i + 1) v x‖ *
              ‖iteratedDeriv (k - i) u x‖
            ≤ ((k + 1).choose (i + 1) : ℝ) * (A (i + 1) * lam / w x ^ (i + 1)) *
              (c03c_aux_recD A (k - i) * lam⁻¹ / w x ^ (k - i)) := by gcongr
          _ = ((k + 1).choose (i + 1) : ℝ) * A (i + 1) * c03c_aux_recD A (k - i) /
              w x ^ (k + 1) := by
            have : w x ^ (k + 1) = w x ^ (i + 1) * w x ^ (k - i) := by
              rw [← pow_add]; congr 1; omega
            rw [this]; field_simp
      have hvpos : 0 < ‖v x‖ := lt_of_lt_of_le hlam hvlx
      have hnorm : ‖iteratedDeriv (k + 1) u x‖ = ‖v x‖⁻¹ * ‖v x * iteratedDeriv (k + 1) u x‖ := by
        rw [norm_mul, ← mul_assoc, inv_mul_cancel₀ hvpos.ne', one_mul]
      rw [hnorm, hkey, norm_neg]
      calc ‖v x‖⁻¹ * ‖∑ i ∈ Finset.range (k + 1),
          ((k + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) v x *
            iteratedDeriv (k + 1 - (i + 1)) u x‖
          ≤ lam⁻¹ * (∑ i ∈ Finset.range (k + 1), ((k + 1).choose (i + 1) : ℝ) * A (i + 1) *
            c03c_aux_recD A (k - i) / w x ^ (k + 1)) := by
            gcongr
        _ ≤ c03c_aux_recD A (k + 1) * lam⁻¹ / w x ^ (k + 1) := by
            rw [c03c_aux_recD, ← Finset.sum_div]
            have hw' : 0 < w x ^ (k + 1) := pow_pos hwx _
            rw [mul_div_assoc', div_le_div_iff_of_pos_right hw', mul_comm]
            gcongr
            linarith

theorem c03c_aux_cont_mul_exp {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ} (hf : Continuous f)
    (hfU : tsupport f ⊆ U) {φ : ℝ → ℝ} (hφ : ContinuousOn φ U) :
    Continuous (fun x => f x * Complex.exp (Complex.I * (φ x : ℂ))) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · have h1 : ContinuousAt φ x := hφ.continuousAt (hU.mem_nhds hx)
    have h2 : ContinuousAt (fun x => Complex.exp (Complex.I * (φ x : ℂ))) x :=
      Complex.continuous_exp.continuousAt.comp
        ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp h1)))
    exact hf.continuousAt.mul h2
  · have hx' : x ∉ tsupport f := fun h => hx (hfU h)
    refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
    simp [hy]

theorem c03c_aux_integrable_mul_exp {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) {φ : ℝ → ℝ} (hφ : ContinuousOn φ U) :
    Integrable (fun x => f x * Complex.exp (Complex.I * (φ x : ℂ))) :=
  (c03c_aux_cont_mul_exp hU hf hfU hφ).integrable_of_hasCompactSupport hfc.mul_right

theorem c03c_aux_q_contDiff (k : ℕ) {U : Set ℝ} (hU : IsOpen U) {a : ℝ → ℂ}
    (ha : ContDiff ℝ (k + 1 : ℕ) a) (haU : tsupport a ⊆ U) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ (k + 2 : ℕ) φ U) (hφ' : ∀ x ∈ U, deriv φ x ≠ 0) :
    ContDiff ℝ (k + 1 : ℕ) (fun t => a t / (Complex.I * ((deriv φ t : ℝ) : ℂ))) := by
  have hd : ContDiffOn ℝ (k + 1 : ℕ) (deriv φ) U :=
    hφ.deriv_of_isOpen hU (by push_cast; exact le_of_eq (by ring))
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport a
  · have hxU := haU hx
    have h1 : ContDiffAt ℝ (k + 1 : ℕ) (fun t => Complex.I * ((deriv φ t : ℝ) : ℂ)) x :=
      contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (hd.contDiffAt (hU.mem_nhds hxU)))
    simp_rw [div_eq_mul_inv]
    have hne : Complex.I * ((deriv φ x : ℝ) : ℂ) ≠ 0 := by simp [hφ' x hxU]
    exact ha.contDiffAt.mul (h1.inv hne)
  · refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

theorem c03c_aux_ibpL_eq {U : Set ℝ} {a : ℝ → ℂ} (haU : tsupport a ⊆ U) (φ : ℝ → ℝ) :
    c03c_ibpL U φ a = deriv (fun t => a t / (Complex.I * ((deriv φ t : ℝ) : ℂ))) := by
  funext x
  unfold c03c_ibpL
  split_ifs with hx
  · rfl
  · have hx' : x ∉ tsupport a := fun h => hx (haU h)
    symm
    apply deriv_of_notMem_tsupport
    intro h
    apply hx'
    refine closure_mono ?_ h
    intro t ht
    simp only [Function.mem_support] at ht ⊢
    intro h0; apply ht; simp [h0]

theorem c03c_aux_tsupport_q {a : ℝ → ℂ} (φ : ℝ → ℝ) :
    tsupport (fun t => a t / (Complex.I * ((deriv φ t : ℝ) : ℂ))) ⊆ tsupport a := by
  refine closure_mono ?_
  intro t ht
  simp only [Function.mem_support] at ht ⊢
  intro h0; apply ht; simp [h0]

/-- One integration by parts. -/
theorem c03c_aux_ibp_step (k : ℕ) {U : Set ℝ} (hU : IsOpen U) {a : ℝ → ℂ}
    (ha : ContDiff ℝ (k + 1 : ℕ) a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ (k + 2 : ℕ) φ U) (hφ' : ∀ x ∈ U, deriv φ x ≠ 0) :
    ContDiff ℝ k (c03c_ibpL U φ a) ∧ tsupport (c03c_ibpL U φ a) ⊆ tsupport a ∧
    (∫ x, a x * Complex.exp (Complex.I * (φ x : ℂ))) =
      -∫ x, c03c_ibpL U φ a x * Complex.exp (Complex.I * (φ x : ℂ)) := by
  set q : ℝ → ℂ := fun t => a t / (Complex.I * ((deriv φ t : ℝ) : ℂ)) with hq
  have hqc : ContDiff ℝ (k + 1 : ℕ) q := c03c_aux_q_contDiff k hU ha haU hφ hφ'
  have hL : c03c_ibpL U φ a = deriv q := c03c_aux_ibpL_eq haU φ
  have hqs : tsupport q ⊆ tsupport a := c03c_aux_tsupport_q φ
  have hLs : tsupport (c03c_ibpL U φ a) ⊆ tsupport a := hL ▸ (tsupport_deriv_subset.trans hqs)
  have hLc : ContDiff ℝ k (c03c_ibpL U φ a) := by
    rw [hL]
    have := hqc
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl] at this
    exact (contDiff_succ_iff_deriv.mp this).2.2
  refine ⟨hLc, hLs, ?_⟩
  have hφc : ContinuousOn φ U := hφ.continuousOn
  set E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (φ x : ℂ)) with hE
  have hk1 : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_add_left 1 k
  have hqd : Differentiable ℝ q := hqc.differentiable (by simp)
  have hqcs : HasCompactSupport q := IsCompact.of_isClosed_subset hac (isClosed_tsupport _) hqs
  have hφd : DifferentiableOn ℝ φ U := hφ.differentiableOn (by simp)
  have hder : ∀ x, HasDerivAt (fun x => q x * E x) (deriv q x * E x + a x * E x) x := by
    intro x
    by_cases hx : x ∈ U
    · have hq' : HasDerivAt q (deriv q x) x := (hqd x).hasDerivAt
      have hφx : HasDerivAt φ (deriv φ x) x :=
        ((hφd x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
      have hE' : HasDerivAt E (E x * (Complex.I * ((deriv φ x : ℝ) : ℂ))) x := by
        have := ((hφx.ofReal_comp).const_mul Complex.I).cexp
        simpa [hE, mul_comm] using this
      convert hq'.mul hE' using 1
      have hne : Complex.I * ((deriv φ x : ℝ) : ℂ) ≠ 0 := by simp [hφ' x hx]
      have hd0 : ((deriv φ x : ℝ) : ℂ) ≠ 0 := by simp [hφ' x hx]
      simp only [hq]
      field_simp
    · have hx' : x ∉ tsupport a := fun h => hx (haU h)
      have hxq : x ∉ tsupport q := fun h => hx' (hqs h)
      have hxg : x ∉ tsupport (fun x => q x * E x) := fun h => hxq (tsupport_mul_subset_left h)
      have h0 := HasDerivAt.of_notMem_tsupport hxg
      rw [deriv_of_notMem_tsupport hxq, image_eq_zero_of_notMem_tsupport hx']
      simpa using h0
  have hi1 : Integrable (fun x => deriv q x * E x) :=
    c03c_aux_integrable_mul_exp hU (hL ▸ hLc.continuous) hqcs.deriv
      (tsupport_deriv_subset.trans (hqs.trans haU)) hφc
  have hi2 : Integrable (fun x => a x * E x) :=
    c03c_aux_integrable_mul_exp hU ha.continuous hac haU hφc
  have hi3 : Integrable (fun x => q x * E x) :=
    c03c_aux_integrable_mul_exp hU hqc.continuous hqcs (hqs.trans haU) hφc
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hder (hi1.add hi2) hi3
  rw [integral_add hi1 hi2] at h0
  rw [hL]
  linear_combination h0

theorem c03c_aux_ibpL_congr (U : Set ℝ) (hU : IsOpen U) (φ φ₂ : ℝ → ℝ) (h : EqOn φ φ₂ U) :
    c03c_ibpL U φ₂ = c03c_ibpL U φ := by
  funext b x
  unfold c03c_ibpL
  split_ifs with hx
  · apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hx] with y hy
    have : deriv φ₂ y = deriv φ y := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hU.mem_nhds hy] with z hz using (h hz).symm
    rw [this]
  · rfl

/-- Blueprint: lem:c03_ibp_compact_iteration.  For `φ ∈ C^{n+1}(U)` with `φ' ≠ 0` and
`a ∈ C_c^n(U)` (extended by zero), `L_φ^j a` (`j ≤ n`) is continuous, compactly supported in
`supp a`, of class `C^{n-j}(ℝ)`; the integrals converge absolutely and
`∫ a e^{iφ} = (-1)^n ∫ L_φ^n a e^{iφ}`; the iterates do not depend on `φ` outside `U`. -/
theorem c03_ibp_compact_iteration (U : Set ℝ) (hU : IsOpen U) (n : ℕ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (n + 1 : ℕ) φ U) (hφ' : ∀ x ∈ U, deriv φ x ≠ 0) (a : ℝ → ℂ)
    (ha : ContDiff ℝ n a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) :
    (∀ j ≤ n, Continuous ((c03c_ibpL U φ)^[j] a) ∧ HasCompactSupport ((c03c_ibpL U φ)^[j] a) ∧
      tsupport ((c03c_ibpL U φ)^[j] a) ⊆ tsupport a ∧
      ContDiff ℝ (n - j : ℕ) ((c03c_ibpL U φ)^[j] a)) ∧
    (∀ j ≤ n, Integrable (fun x => (c03c_ibpL U φ)^[j] a x * Complex.exp (Complex.I * (φ x : ℂ)))) ∧
    (∫ x, a x * Complex.exp (Complex.I * (φ x : ℂ))) =
      (-1 : ℂ) ^ n * ∫ x, (c03c_ibpL U φ)^[n] a x * Complex.exp (Complex.I * (φ x : ℂ)) ∧
    ∀ φ₂ : ℝ → ℝ, EqOn φ φ₂ U → ∀ j ≤ n, (c03c_ibpL U φ₂)^[j] a = (c03c_ibpL U φ)^[j] a := by
  have main : ∀ j ≤ n, ContDiff ℝ (n - j : ℕ) ((c03c_ibpL U φ)^[j] a) ∧
      tsupport ((c03c_ibpL U φ)^[j] a) ⊆ tsupport a ∧
      (∫ x, a x * Complex.exp (Complex.I * (φ x : ℂ))) =
        (-1 : ℂ) ^ j * ∫ x, (c03c_ibpL U φ)^[j] a x * Complex.exp (Complex.I * (φ x : ℂ)) := by
    intro j
    induction j with
    | zero => intro _; simpa using ha
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hk : n - j = (n - (j + 1)) + 1 := by omega
      rw [hk] at h1
      have hφk : ContDiffOn ℝ ((n - (j + 1)) + 2 : ℕ) φ U :=
        hφ.of_le (by exact_mod_cast (by omega : n - (j + 1) + 2 ≤ n + 1))
      obtain ⟨s1, s2, s3⟩ := c03c_aux_ibp_step (n - (j + 1)) hU h1
        (IsCompact.of_isClosed_subset hac (isClosed_tsupport _) h2) (h2.trans haU) hφk hφ'
      rw [Function.iterate_succ_apply']
      refine ⟨s1, s2.trans h2, ?_⟩
      rw [h3, s3, pow_succ]; ring
  refine ⟨fun j hj => ?_, fun j hj => ?_, by simpa using (main n le_rfl).2.2, ?_⟩
  · obtain ⟨h1, h2, _⟩ := main j hj
    exact ⟨h1.continuous, IsCompact.of_isClosed_subset hac (isClosed_tsupport _) h2, h2, h1⟩
  · obtain ⟨h1, h2, _⟩ := main j hj
    exact c03c_aux_integrable_mul_exp hU h1.continuous
      (IsCompact.of_isClosed_subset hac (isClosed_tsupport _) h2) (h2.trans haU) hφ.continuousOn
  · intro φ₂ h j _
    rw [c03c_aux_ibpL_congr U hU φ φ₂ h]

theorem c03c_aux_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- `∂^k ↑f = ↑(∂^k f)`. -/
theorem c03c_aux_iteratedDeriv_ofReal (f : ℝ → ℝ) (y : ℝ) (k : ℕ) (hf : ContDiffAt ℝ k f y) :
    iteratedDeriv k (fun t => ((f t : ℝ) : ℂ)) y = ((iteratedDeriv k f y : ℝ) : ℂ) := by
  have : (fun t => ((f t : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    Complex.ofRealCLM.iteratedFDeriv_comp_left hf le_rfl]
  simp

theorem c03c_aux_ibpL_smooth {U : Set ℝ} (hU : IsOpen U) {a : ℝ → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) (hφ' : ∀ x ∈ U, deriv φ x ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (c03c_ibpL U φ a) ∧ HasCompactSupport (c03c_ibpL U φ a) ∧
      tsupport (c03c_ibpL U φ a) ⊆ tsupport a := by
  have hs := c03c_aux_ibp_step 0 hU (ha.of_le (c03c_aux_le_top _)) hac haU
    (hφ.of_le (c03c_aux_le_top _)) hφ'
  refine ⟨?_, IsCompact.of_isClosed_subset hac (isClosed_tsupport _) hs.2.1, hs.2.1⟩
  rw [contDiff_infty]
  intro k
  exact (c03c_aux_ibp_step k hU (ha.of_le (c03c_aux_le_top _)) hac haU
    (hφ.of_le (c03c_aux_le_top _)) hφ').1

/-- One step of the symbol bound: `(L a)^{(ℓ)} = ∑ binom(ℓ+1,l) a^{(l)} (1/(iφ'))^{(ℓ+1-l)}`. -/
theorem c03c_aux_ibp_symbol_step {U : Set ℝ} (hU : IsOpen U) {a : ℝ → ℂ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (haU : tsupport a ⊆ U)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) (hφ' : ∀ x ∈ U, deriv φ x ≠ 0)
    (σ B Λ : ℝ) (A Q : ℕ → ℝ) (hB : 0 ≤ B) (hΛ : 0 < Λ) (hA : ∀ l, 0 ≤ A l) (hQ : ∀ l, 0 ≤ Q l)
    (ℓ : ℕ) (z : ℝ) (hz : z ∈ U) (hz0 : z ≠ 0)
    (hab : ∀ l ≤ ℓ + 1, ‖iteratedDeriv l a z‖ ≤ A l * B * |z| ^ (σ - l))
    (hqb : ∀ l ≤ ℓ + 1,
      |iteratedDeriv l (fun z => 1 / deriv φ z) z| ≤ Q l * Λ⁻¹ * |z| ^ (-(l : ℝ))) :
    ‖iteratedDeriv ℓ (c03c_ibpL U φ a) z‖ ≤
      (∑ l ∈ Finset.range (ℓ + 2), ((ℓ + 1).choose l : ℝ) * A l * Q (ℓ + 1 - l)) *
        (B * Λ⁻¹) * |z| ^ (σ - 1 - ℓ) := by
  set r : ℝ → ℂ := fun t => -Complex.I * (((1 / deriv φ t : ℝ)) : ℂ) with hr
  have hq : (fun t => a t / (Complex.I * ((deriv φ t : ℝ) : ℂ))) = fun t => a t * r t := by
    funext t
    simp only [hr]
    by_cases h : deriv φ t = 0
    · simp [h]
    · have : ((deriv φ t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
      field_simp
      rw [Complex.ofReal_div, Complex.ofReal_one]
      field_simp
      rw [Complex.I_sq]; ring
  have hL : c03c_ibpL U φ a = deriv (fun t => a t * r t) := by
    rw [c03c_aux_ibpL_eq haU φ, hq]
  have hdφ : ContDiffOn ℝ (⊤ : ℕ∞) (deriv φ) U :=
    ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp hφ).2
  have h2z : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => 1 / deriv φ t) z := by
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (deriv φ) z := hdφ.contDiffAt (hU.mem_nhds hz)
    simp_rw [one_div]; exact h1.inv (hφ' z hz)
  have hrz : ContDiffAt ℝ (⊤ : ℕ∞) r z := by
    have h2 := h2z
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp z h2)
  rw [hL, ← iteratedDeriv_succ', iteratedDeriv_fun_mul (ha.contDiffAt.of_le
    (c03c_aux_le_top _)) (hrz.of_le (c03c_aux_le_top _))]
  have hrd : ∀ m, iteratedDeriv m r z =
      -Complex.I * ((iteratedDeriv m (fun t => 1 / deriv φ t) z : ℝ) : ℂ) := by
    intro m
    rw [hr, iteratedDeriv_const_mul_field]
    congr 1
    exact c03c_aux_iteratedDeriv_ofReal _ _ _ (h2z.of_le (c03c_aux_le_top _))
  have hzpos : 0 < |z| := abs_pos.mpr hz0
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
  rw [Finset.mem_range] at hl
  rw [hrd, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast]
  have h1 := hab l (by omega)
  have h2 := hqb (ℓ + 1 - l) (by omega)
  have hpow : |z| ^ (σ - l) * |z| ^ (-((ℓ + 1 - l : ℕ) : ℝ)) = |z| ^ (σ - 1 - ℓ) := by
    rw [← Real.rpow_add hzpos]
    congr 1
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  calc ((ℓ + 1).choose l : ℝ) * ‖iteratedDeriv l a z‖ *
        |iteratedDeriv (ℓ + 1 - l) (fun t => 1 / deriv φ t) z|
      ≤ ((ℓ + 1).choose l : ℝ) * (A l * B * |z| ^ (σ - l)) *
        (Q (ℓ + 1 - l) * Λ⁻¹ * |z| ^ (-((ℓ + 1 - l : ℕ) : ℝ))) := by
        have := hA l
        gcongr
    _ = ((ℓ + 1).choose l : ℝ) * A l * Q (ℓ + 1 - l) * (B * Λ⁻¹) *
        (|z| ^ (σ - l) * |z| ^ (-((ℓ + 1 - l : ℕ) : ℝ))) := by ring
    _ = _ := by rw [hpow]

/-- Blueprint: lem:c03_ibp_symbol_iteration.  If `|a^{(ℓ)}| ≤ A_ℓ B |z|^{σ-ℓ}` and
`|(1/φ')^{(ℓ)}| ≤ Q_ℓ Λ⁻¹ |z|^{-ℓ}` on `U ⊆ ℝ∖0` for `ℓ ≤ n+j+1`, then
`|(L_φ^n a)^{(j)}| ≤ C B Λ^{-n} |z|^{σ-n-j}` on `U`, `C = C(n,j,σ,A,Q)`. -/
theorem c03_ibp_symbol_iteration (n j : ℕ) (σ : ℝ) (A Q : ℕ → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hQ : ∀ l, 0 ≤ Q l) :
    ∃ C, 0 < C ∧ ∀ (U : Set ℝ) (a : ℝ → ℂ) (φ : ℝ → ℝ) (B Λ : ℝ),
      IsOpen U → U ⊆ {0}ᶜ → ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U →
      ContDiffOn ℝ (⊤ : ℕ∞) φ U → 0 ≤ B → 0 < Λ → (∀ z ∈ U, deriv φ z ≠ 0) →
      (∀ z ∈ U, ∀ l ≤ n + j + 1, ‖iteratedDeriv l a z‖ ≤ A l * B * |z| ^ (σ - l)) →
      (∀ z ∈ U, ∀ l ≤ n + j + 1,
        |iteratedDeriv l (fun z => 1 / deriv φ z) z| ≤ Q l * Λ⁻¹ * |z| ^ (-(l : ℝ))) →
      ∀ z ∈ U, ‖iteratedDeriv j ((c03c_ibpL U φ)^[n] a) z‖ ≤
        C * B * (Λ ^ n)⁻¹ * |z| ^ (σ - n - j) := by
  induction n generalizing j σ A Q with
  | zero =>
    refine ⟨A j + 1, by linarith [hA j], ?_⟩
    intro U a φ B Λ _ _ _ _ _ _ hB _ _ hab _ z hz
    have := hab z hz j (by omega)
    simp only [Function.iterate_zero, id_eq, pow_zero, inv_one, mul_one, CharP.cast_eq_zero,
      sub_zero]
    calc ‖iteratedDeriv j a z‖ ≤ A j * B * |z| ^ (σ - j) := this
      _ ≤ (A j + 1) * B * |z| ^ (σ - j) := by gcongr; linarith
  | succ n ih =>
    set A' : ℕ → ℝ := fun ℓ =>
      ∑ l ∈ Finset.range (ℓ + 2), ((ℓ + 1).choose l : ℝ) * A l * Q (ℓ + 1 - l) with hA'
    have hA'0 : ∀ ℓ, 0 ≤ A' ℓ := fun ℓ => Finset.sum_nonneg fun l _ => by
      have := hA l; have := hQ (ℓ + 1 - l); positivity
    obtain ⟨C, hC, hCb⟩ := ih j (σ - 1) A' Q hA'0 hQ
    refine ⟨C, hC, ?_⟩
    intro U a φ B Λ hU hU0 ha hac haU hφ hB hΛ hφ' hab hqb z hz
    obtain ⟨hs1, hs2, hs3⟩ := c03c_aux_ibpL_smooth hU ha hac haU hφ hφ'
    have key := hCb U (c03c_ibpL U φ a) φ (B * Λ⁻¹) Λ hU hU0 hs1 hs2 (hs3.trans haU) hφ
      (by positivity) hΛ hφ'
      (fun z hz ℓ hℓ => by
        have := c03c_aux_ibp_symbol_step hU ha haU hφ hφ' σ B Λ A Q hB hΛ hA hQ ℓ z hz
          (fun h => hU0 hz h)
          (fun l hl => hab z hz l (by omega)) (fun l hl => hqb z hz l (by omega))
        simpa [hA', mul_assoc] using this)
      (fun z hz l hl => hqb z hz l (by omega)) z hz
    rw [Function.iterate_succ_apply]
    calc ‖iteratedDeriv j ((c03c_ibpL U φ)^[n] (c03c_ibpL U φ a)) z‖
        ≤ C * (B * Λ⁻¹) * (Λ ^ n)⁻¹ * |z| ^ (σ - 1 - n - j) := key
      _ = C * B * (Λ ^ (n + 1))⁻¹ * |z| ^ (σ - ((n + 1 : ℕ) : ℝ) - j) := by
        push_cast
        rw [pow_succ, mul_inv]
        ring_nf

/-- Blueprint: lem:c03_supported_phase_product.  For `a ∈ C_c^∞(U)` (extended by zero) and
`φ ∈ C^∞(U)` (arbitrary outside `U`), `a e^{iφ} ∈ C_c^∞(ℝ)` with support in `supp a`; its
derivatives are given on `U` by the Leibniz formula, vanish near every point outside `supp a`, and
are integrable. -/
theorem c03_supported_phase_product (U : Set ℝ) (hU : IsOpen U) (a : ℝ → ℂ) (φ : ℝ → ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hac : HasCompactSupport a) (haU : tsupport a ⊆ U)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => a x * Complex.exp (Complex.I * (φ x : ℂ))) ∧
    HasCompactSupport (fun x => a x * Complex.exp (Complex.I * (φ x : ℂ))) ∧
    tsupport (fun x => a x * Complex.exp (Complex.I * (φ x : ℂ))) ⊆ tsupport a ∧
    (∀ k : ℕ, ∀ x ∈ U, iteratedDeriv k (fun x => a x * Complex.exp (Complex.I * (φ x : ℂ))) x =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℂ) * iteratedDeriv i a x *
        iteratedDeriv (k - i) (fun x => Complex.exp (Complex.I * (φ x : ℂ))) x) ∧
    (∀ k : ℕ, ∀ x ∉ tsupport a, ∀ᶠ t in 𝓝 x,
      iteratedDeriv k (fun x => a x * Complex.exp (Complex.I * (φ x : ℂ))) t = 0) ∧
    ∀ k : ℕ, Integrable (iteratedDeriv k (fun x => a x * Complex.exp (Complex.I * (φ x : ℂ)))) := by
  set e : ℝ → ℂ := fun x => Complex.exp (Complex.I * (φ x : ℂ)) with he
  have heU : ∀ x ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) e x := by
    intro x hx
    have hφx : ContDiffAt ℝ (⊤ : ℕ∞) φ x := hφ.contDiffAt (hU.mem_nhds hx)
    have : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ((φ x : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hφx
    exact (contDiffAt_const.mul this).cexp
  have hzero : ∀ x ∉ tsupport a, (fun x => a x * e x) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    intro x hx
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => a x * e x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport a
    · exact ha.contDiffAt.mul (heU x (haU hx))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx)
  have hcs : HasCompactSupport (fun x => a x * e x) := hac.mul_right
  refine ⟨hsm, hcs, tsupport_mul_subset_left, ?_, ?_, ?_⟩
  · intro k x hx
    have := iteratedDeriv_fun_mul (n := k) (ha.contDiffAt.of_le (by exact_mod_cast le_top))
      ((heU x hx).of_le (by exact_mod_cast le_top))
    simpa using this
  · intro k x hx
    have h1 := (hzero x hx).iteratedDeriv k
    filter_upwards [h1] with t ht
    rw [ht, iteratedDeriv_const]; split_ifs <;> rfl
  · intro k
    refine (hsm.continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport ?_
    rw [HasCompactSupport] at hcs ⊢
    refine hcs.of_isClosed_subset (isClosed_tsupport _) ?_
    intro t ht
    by_contra hcon
    have := (notMem_tsupport_iff_eventuallyEq.mp hcon).iteratedDeriv k
    have h2 : iteratedDeriv k (fun x => a x * e x) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [this] with s hs
      rw [hs, show (0 : ℝ → ℂ) = fun _ => (0 : ℂ) from rfl, iteratedDeriv_const]; split_ifs <;> rfl
    exact (notMem_tsupport_iff_eventuallyEq.mpr h2) ht

/-! ## Homogeneous-kernel integration by parts -/

/-- `|y|^n e^{-y²/2} ≤ 1 + 2^n n!`. -/
theorem c03c_aux_pow_gauss_le (n : ℕ) (y : ℝ) :
    |y| ^ n * Real.exp (-(y ^ 2 / 2)) ≤ 1 + 2 ^ n * (n.factorial : ℝ) := by
  have he : 0 < Real.exp (y ^ 2 / 2) := Real.exp_pos _
  have h1 : (y ^ 2 / 2) ^ n / (n.factorial : ℝ) ≤ Real.exp (y ^ 2 / 2) :=
    Real.pow_div_factorial_le_exp (x := y ^ 2 / 2) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h2 : |y| ^ n ≤ 1 + |y| ^ (2 * n) := by
    rcases le_or_gt |y| 1 with h | h
    · have : |y| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg y) h
      have : 0 ≤ |y| ^ (2 * n) := by positivity
      linarith
    · have : |y| ^ n ≤ |y| ^ (2 * n) := pow_le_pow_right₀ h.le (by omega)
      linarith
  have h3 : |y| ^ (2 * n) = 2 ^ n * (y ^ 2 / 2) ^ n := by
    rw [pow_mul, sq_abs, div_pow, mul_div_cancel₀]; positivity
  have h4 : |y| ^ (2 * n) ≤ 2 ^ n * (n.factorial : ℝ) * Real.exp (y ^ 2 / 2) := by
    rw [h3, div_le_iff₀ hf] at *
    nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n]
  have h5 : Real.exp (-(y ^ 2 / 2)) * Real.exp (y ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h6 : Real.exp (-(y ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
  have h7 : 0 ≤ Real.exp (-(y ^ 2 / 2)) := (Real.exp_pos _).le
  calc |y| ^ n * Real.exp (-(y ^ 2 / 2)) ≤ (1 + 2 ^ n * (n.factorial : ℝ) * Real.exp (y ^ 2 / 2)) *
        Real.exp (-(y ^ 2 / 2)) := by gcongr; linarith
    _ = Real.exp (-(y ^ 2 / 2)) + 2 ^ n * (n.factorial : ℝ) * (Real.exp (-(y ^ 2 / 2)) *
        Real.exp (y ^ 2 / 2)) := by ring
    _ ≤ 1 + 2 ^ n * (n.factorial : ℝ) := by rw [h5]; linarith

/-- `|y|^j |∂^j e^{-y²/2}| ≤ M_j`. -/
theorem c03c_aux_gauss_deriv_bound (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ y : ℝ, |y| ^ j * |iteratedDeriv j (fun y => Real.exp (-(y ^ 2 / 2))) y| ≤ M := by
  set P := Polynomial.hermite j
  set N := P.natDegree
  refine ⟨1 + ∑ i ∈ Finset.range (N + 1), |(P.coeff i : ℝ)| * (1 + 2 ^ (i + j) * ((i + j).factorial : ℝ)),
    ?_, fun y => ?_⟩
  · have : 0 ≤ ∑ i ∈ Finset.range (N + 1), |(P.coeff i : ℝ)| * (1 + 2 ^ (i + j) * ((i + j).factorial : ℝ)) :=
      Finset.sum_nonneg fun i _ => by positivity
    linarith
  rw [iteratedDeriv_eq_iterate, Polynomial.deriv_gaussian_eq_hermite_mul_gaussian,
    Polynomial.aeval_eq_sum_range]
  have hE : 0 ≤ Real.exp (-(y ^ 2 / 2)) := (Real.exp_pos _).le
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hE]
  have : |y| ^ j * (|∑ i ∈ Finset.range (N + 1), P.coeff i • y ^ i| * Real.exp (-(y ^ 2 / 2))) ≤
      ∑ i ∈ Finset.range (N + 1), |(P.coeff i : ℝ)| * (1 + 2 ^ (i + j) * ((i + j).factorial : ℝ)) := by
    rw [show ∀ a b c : ℝ, a * (b * c) = b * (a * c) from fun a b c => by ring]
    calc |∑ i ∈ Finset.range (N + 1), P.coeff i • y ^ i| * (|y| ^ j * Real.exp (-(y ^ 2 / 2)))
        ≤ (∑ i ∈ Finset.range (N + 1), |(P.coeff i : ℝ)| * |y| ^ i) *
          (|y| ^ j * Real.exp (-(y ^ 2 / 2))) := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [zsmul_eq_mul, abs_mul, abs_pow]
      _ = ∑ i ∈ Finset.range (N + 1), |(P.coeff i : ℝ)| *
          (|y| ^ (i + j) * Real.exp (-(y ^ 2 / 2))) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
          gcongr; exact c03c_aux_pow_gauss_le (i + j) y
  linarith

/-- Uniform Gaussian derivative bounds `|∂^j e^{-ηz²}| ≤ M_j |z|^{-j}` (`η ≥ 0`, `z ≠ 0`). -/
theorem c03c_aux_gauss_eta_bound (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ η : ℝ, 0 ≤ η → ∀ z : ℝ, z ≠ 0 →
      |iteratedDeriv j (fun z : ℝ => Real.exp (-(η * z ^ 2))) z| ≤ M * |z| ^ (-(j : ℝ)) := by
  obtain ⟨M, hM, hMb⟩ := c03c_aux_gauss_deriv_bound j
  refine ⟨M, hM, fun η hη z hz => ?_⟩
  set c := Real.sqrt (2 * η)
  have hfun : (fun z : ℝ => Real.exp (-(η * z ^ 2))) =
      fun z => (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (c * z) := by
    funext z
    simp only [c]
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    ring_nf
  have hG : ContDiff ℝ j (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) := by fun_prop
  rw [hfun, iteratedDeriv_comp_const_mul hG c]
  have hzpos : 0 < |z| ^ j := pow_pos (abs_pos.mpr hz) j
  rw [Real.rpow_neg (abs_nonneg z), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hzpos,
    abs_mul, abs_pow]
  have := hMb (c * z)
  rw [abs_mul, mul_pow] at this
  linarith [this]


/-- Leibniz bound for symbols at a point `z ≠ 0`. -/
theorem c03c_aux_symbol_mul {f g : ℝ → ℂ} {z : ℝ} (hz : z ≠ 0) (n : ℕ)
    (hf : ContDiffAt ℝ n f z) (hg : ContDiffAt ℝ n g z) (F G : ℕ → ℝ) (α β : ℝ)
    (hfb : ∀ i ≤ n, ‖iteratedDeriv i f z‖ ≤ F i * |z| ^ (α - i))
    (hgb : ∀ i ≤ n, ‖iteratedDeriv i g z‖ ≤ G i * |z| ^ (β - i)) :
    ∀ j ≤ n, ‖iteratedDeriv j (fun x => f x * g x) z‖ ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * F i * G (j - i)) * |z| ^ (α + β - j) := by
  intro j hj
  have hzpos : 0 < |z| := abs_pos.mpr hz
  have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  rw [iteratedDeriv_fun_mul (hf.of_le hjn) (hg.of_le hjn), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have h1 := hfb i (by omega)
  have h2 := hgb (j - i) (by omega)
  have hpow : |z| ^ (α - i) * |z| ^ (β - ((j - i : ℕ) : ℝ)) = |z| ^ (α + β - j) := by
    rw [← Real.rpow_add hzpos]; congr 1; rw [Nat.cast_sub (by omega)]; ring
  calc (j.choose i : ℝ) * ‖iteratedDeriv i f z‖ * ‖iteratedDeriv (j - i) g z‖
      ≤ (j.choose i : ℝ) * (F i * |z| ^ (α - i)) * (G (j - i) * |z| ^ (β - ((j - i : ℕ) : ℝ))) := by
        have : 0 ≤ F i * |z| ^ (α - i) := (norm_nonneg _).trans h1
        gcongr
    _ = (j.choose i : ℝ) * F i * G (j - i) * (|z| ^ (α - i) * |z| ^ (β - ((j - i : ℕ) : ℝ))) := by
        ring
    _ = _ := by rw [hpow]

/-- Derivatives of `|x|^s` away from `0`. -/
theorem c03c_aux_abs_rpow_deriv (s : ℝ) {z : ℝ} (hz : z ≠ 0) (j : ℕ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => |x| ^ s) z ∧
    |iteratedDeriv j (fun x : ℝ => |x| ^ s) z| ≤
      |(descPochhammer ℝ j).eval s| * |z| ^ (s - j) := by
  have hzpos : 0 < |z| := abs_pos.mpr hz
  refine ⟨(Real.contDiffAt_rpow_const_of_ne hzpos.ne').comp z (contDiffAt_abs hz), ?_⟩
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hev : (fun x : ℝ => |x| ^ s) =ᶠ[𝓝 z] fun x => (fun y : ℝ => y ^ s) (-x) := by
      filter_upwards [Iio_mem_nhds hneg] with x hx
      rw [abs_of_neg hx]
    have hn := iteratedDeriv_comp_neg j (fun y : ℝ => y ^ s) z
    rw [hev.iteratedDeriv_eq, hn, iteratedDeriv_eq_iterate,
      Real.iter_deriv_rpow_const, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_mul, abs_of_neg hneg, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  · have hev : (fun x : ℝ => |x| ^ s) =ᶠ[𝓝 z] fun y : ℝ => y ^ s := by
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      rw [abs_of_pos hx]
    rw [hev.iteratedDeriv_eq, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul,
      abs_of_pos hpos, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]

/-- Iterated derivatives of a smooth compactly supported function are bounded. -/
theorem c03c_aux_iteratedDeriv_bdd {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcs : HasCompactSupport χ) (i : ℕ) : ∃ M, 0 ≤ M ∧ ∀ x, |iteratedDeriv i χ x| ≤ M := by
  have hc : HasCompactSupport (iteratedDeriv i χ) := by
    rw [iteratedDeriv_eq_iterate]
    induction i with
    | zero => simpa using hcs
    | succ i ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  obtain ⟨C, hC⟩ := (hχ.continuous_iteratedDeriv i (by exact_mod_cast le_top)).bounded_above_of_compact_support hc
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Derivative bounds for `1 - χ₁(Λz)`, uniformly in `Λ > 0`. -/
theorem c03c_aux_cutoff_deriv (χ₁ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ₁)
    (hχ01 : ∀ z, 0 ≤ χ₁ z ∧ χ₁ z ≤ 1)
    (hχ1 : ∀ z ∈ Icc (-1 : ℝ) 1, χ₁ z = 1) (hχs : ∀ z, 2 < |z| → χ₁ z = 0) (i : ℕ) :
    ∃ M, 0 < M ∧ ∀ Λ : ℝ, 0 < Λ → ∀ z : ℝ, z ≠ 0 →
      |iteratedDeriv i (fun z => 1 - χ₁ (Λ * z)) z| ≤ M * |z| ^ (-(i : ℝ)) := by
  have hcs : HasCompactSupport χ₁ := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-2) 2) isCompact_Icc ?_
    intro x hx
    by_contra h
    apply hx
    apply hχs
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨Mχ, hMχ0, hMχ⟩ := c03c_aux_iteratedDeriv_bdd hχ hcs i
  refine ⟨1 + 2 ^ i * Mχ, by positivity, fun Λ hΛ z hz => ?_⟩
  have hzpos : 0 < |z| := abs_pos.mpr hz
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, neg_zero, Real.rpow_zero, mul_one,
      pow_zero, one_mul]
    have := hχ01 (Λ * z)
    rw [abs_le]; constructor <;> linarith
  · rw [iteratedDeriv_const_sub hi, iteratedDeriv_neg, abs_neg,
      iteratedDeriv_comp_const_mul (hχ.of_le (by exact_mod_cast le_top)), abs_mul, abs_pow,
      abs_of_pos hΛ]
    have hloc : ∀ w, |w| < 1 ∨ 2 < |w| → iteratedDeriv i χ₁ w = 0 := by
      intro w hw
      rcases hw with hw | hw
      · have hev : χ₁ =ᶠ[𝓝 w] fun _ => 1 := by
          have : Ioo (-1 : ℝ) 1 ∈ 𝓝 w := Ioo_mem_nhds (by linarith [neg_abs_le w])
            (by linarith [le_abs_self w])
          filter_upwards [this] with x hx using hχ1 x ⟨hx.1.le, hx.2.le⟩
        rw [hev.iteratedDeriv_eq, iteratedDeriv_const]; simp [hi.ne']
      · have hev : χ₁ =ᶠ[𝓝 w] fun _ => 0 := by
          have : {x : ℝ | 2 < |x|} ∈ 𝓝 w :=
            (isOpen_lt continuous_const continuous_abs).mem_nhds hw
          filter_upwards [this] with x hx using hχs x hx
        rw [hev.iteratedDeriv_eq, iteratedDeriv_const]; simp [hi.ne']
    have hrhs : 0 ≤ (1 + 2 ^ i * Mχ) * |z| ^ (-(i : ℝ)) := by positivity
    by_cases hw : |Λ * z| < 1 ∨ 2 < |Λ * z|
    · rw [hloc _ hw, abs_zero, mul_zero]; exact hrhs
    · push Not at hw
      have hΛz : Λ ≤ 2 / |z| := by
        rw [le_div_iff₀ hzpos]; rw [abs_mul, abs_of_pos hΛ] at hw; linarith [hw.2]
      have hΛi : Λ ^ i ≤ 2 ^ i * |z| ^ (-(i : ℝ)) := by
        rw [Real.rpow_neg hzpos.le, Real.rpow_natCast, ← div_eq_mul_inv, ← div_pow]
        exact pow_le_pow_left₀ hΛ.le hΛz i
      calc Λ ^ i * |iteratedDeriv i χ₁ (Λ * z)| ≤ (2 ^ i * |z| ^ (-(i : ℝ))) * Mχ := by
            gcongr; exact hMχ _
        _ ≤ (1 + 2 ^ i * Mχ) * |z| ^ (-(i : ℝ)) := by
            have : 0 ≤ |z| ^ (-(i : ℝ)) := by positivity
            nlinarith

/-- Blueprint: lem:c03_homogeneous_cutoff_symbol.  Uniform Gaussian derivative bounds
`|∂^j e^{-ηz²}| ≤ D_j |z|^{-j}` (`η ≥ 0`), and: if `|b^{(j)}| ≤ C_j B |z|^{K-j}` (`j ≤ n`) then
`g_{η,Λ}` is smooth on `ℝ`, vanishes on `|z| ≤ 1/Λ`, and `|g^{(j)}| ≤ D B |z|^{K-1-p-j}`,
`D = D(p,K,n,χ₁,C_0,…,C_n)`. -/
theorem c03_homogeneous_cutoff_symbol (p K : ℝ) (hp : 0 < p) (hp1 : p < 1) (hK : p < K) (n : ℕ)
    (χ₁ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ₁) (hχ01 : ∀ z, 0 ≤ χ₁ z ∧ χ₁ z ≤ 1)
    (hχ1 : ∀ z ∈ Icc (-1 : ℝ) 1, χ₁ z = 1) (hχs : ∀ z, 2 < |z| → χ₁ z = 0) :
    (∃ D : ℕ → ℝ, ∀ j ≤ n, 0 < D j ∧ ∀ η : ℝ, 0 ≤ η → ∀ z : ℝ, z ≠ 0 →
      |iteratedDeriv j (fun z : ℝ => Real.exp (-(η * z ^ 2))) z| ≤ D j * |z| ^ (-(j : ℝ))) ∧
    ∀ Cs : ℕ → ℝ, ∃ D, 0 < D ∧ ∀ (B Λ η : ℝ) (b : ℝ → ℂ), 0 ≤ B → 0 < Λ → 0 ≤ η →
      ContDiff ℝ (⊤ : ℕ∞) b →
      (∀ j ≤ n, ∀ z : ℝ, z ≠ 0 → ‖iteratedDeriv j b z‖ ≤ Cs j * B * |z| ^ (K - j)) →
      ContDiff ℝ (⊤ : ℕ∞) (c03c_homg p χ₁ Λ η b) ∧
      (∀ z : ℝ, |z| ≤ 1 / Λ → c03c_homg p χ₁ Λ η b z = 0) ∧
      ∀ j ≤ n, ∀ z : ℝ, z ≠ 0 →
        ‖iteratedDeriv j (c03c_homg p χ₁ Λ η b) z‖ ≤ D * B * |z| ^ (K - 1 - p - j) := by
  choose Dg hDg hDgb using c03c_aux_gauss_eta_bound
  refine ⟨⟨Dg, fun j _ => ⟨hDg j, hDgb j⟩⟩, ?_⟩
  intro Cs
  choose Mc hMc hMcb using c03c_aux_cutoff_deriv χ₁ hχ hχ01 hχ1 hχs
  set Pk : ℕ → ℝ := fun i => |(descPochhammer ℝ i).eval (-(1 + p))| with hPk
  set P1 : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * Mc l * Dg (i - l)
    with hP1
  set P2 : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * P1 l * Pk (i - l)
    with hP2
  set T : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * P2 l * Cs (i - l)
    with hT
  refine ⟨1 + ∑ i ∈ Finset.range (n + 1), |T i|,
    by have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (n + 1)) => abs_nonneg (T i)); linarith,
    ?_⟩
  intro B Λ η b hB hΛ hη hb hbd
  set fc : ℝ → ℂ := fun z => ((1 - χ₁ (Λ * z) : ℝ) : ℂ) with hfc
  set fe : ℝ → ℂ := fun z => ((Real.exp (-(η * z ^ 2)) : ℝ) : ℂ) with hfe
  set fk : ℝ → ℂ := fun z => ((|z| ^ (-(1 + p)) : ℝ) : ℂ) with hfk
  have hg : c03c_homg p χ₁ Λ η b = fun z => (fun z => (fun z => fc z * fe z) z * fk z) z * b z := by
    funext z
    simp only [c03c_homg, hfc, hfe, hfk]
    rw [Real.rpow_neg (abs_nonneg z), Complex.ofReal_inv, Complex.ofReal_mul]
    ring
  have hcχ : ContDiff ℝ (⊤ : ℕ∞) (fun z => 1 - χ₁ (Λ * z)) :=
    contDiff_const.sub (hχ.comp (contDiff_const.mul contDiff_id))
  have hce : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => Real.exp (-(η * z ^ 2))) := by fun_prop
  have hfcs : ContDiff ℝ (⊤ : ℕ∞) fc := Complex.ofRealCLM.contDiff.comp hcχ
  have hfes : ContDiff ℝ (⊤ : ℕ∞) fe := Complex.ofRealCLM.contDiff.comp hce
  have hfkz : ∀ z : ℝ, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) fk z := fun z hz =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (c03c_aux_abs_rpow_deriv (-(1 + p)) hz 0).1
  have hzero : ∀ z : ℝ, |z| ≤ 1 / Λ → c03c_homg p χ₁ Λ η b z = 0 := by
    intro z hz
    have h1 : χ₁ (Λ * z) = 1 := by
      apply hχ1
      rw [mem_Icc, ← abs_le, abs_mul, abs_of_pos hΛ]
      rw [le_div_iff₀ hΛ] at hz; linarith
    simp [c03c_homg, h1]
  refine ⟨?_, hzero, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : |z| < 1 / Λ
    · refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : ℂ)) ?_
      have : {x : ℝ | |x| < 1 / Λ} ∈ 𝓝 z := (isOpen_lt continuous_abs continuous_const).mem_nhds hz
      filter_upwards [this] with x hx using hzero x hx.le
    · have hz0 : z ≠ 0 := by
        intro h; apply hz; rw [h, abs_zero]; positivity
      rw [hg]
      exact ((hfcs.contDiffAt.mul hfes.contDiffAt).mul (hfkz z hz0)).mul hb.contDiffAt
  · intro j hj z hz
    have hzpos : 0 < |z| := abs_pos.mpr hz
    have hle : ∀ i : ℕ, ((i : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun i => by
      exact_mod_cast le_top
    have bc : ∀ i ≤ n, ‖iteratedDeriv i fc z‖ ≤ Mc i * |z| ^ ((0 : ℝ) - i) := by
      intro i _
      rw [hfc, c03c_aux_iteratedDeriv_ofReal _ _ _ (hcχ.contDiffAt.of_le (hle i)), Complex.norm_real,
        Real.norm_eq_abs, zero_sub]
      exact hMcb i Λ hΛ z hz
    have be : ∀ i ≤ n, ‖iteratedDeriv i fe z‖ ≤ Dg i * |z| ^ ((0 : ℝ) - i) := by
      intro i _
      rw [hfe, c03c_aux_iteratedDeriv_ofReal _ _ _ (hce.contDiffAt.of_le (hle i)), Complex.norm_real,
        Real.norm_eq_abs, zero_sub]
      exact hDgb i η hη z hz
    have bk : ∀ i ≤ n, ‖iteratedDeriv i fk z‖ ≤ Pk i * |z| ^ (-(1 + p) - i) := by
      intro i _
      rw [hfk, c03c_aux_iteratedDeriv_ofReal _ _ _
        ((c03c_aux_abs_rpow_deriv (-(1 + p)) hz 0).1.of_le (hle i)), Complex.norm_real,
        Real.norm_eq_abs]
      exact (c03c_aux_abs_rpow_deriv (-(1 + p)) hz i).2
    have bb : ∀ i ≤ n, ‖iteratedDeriv i b z‖ ≤ (Cs i * B) * |z| ^ (K - i) := fun i hi =>
      hbd i hi z hz
    have b1 := c03c_aux_symbol_mul hz n (hfcs.contDiffAt.of_le (hle n))
      (hfes.contDiffAt.of_le (hle n)) Mc Dg 0 0 bc be
    have b2 := c03c_aux_symbol_mul hz n
      ((hfcs.contDiffAt.mul hfes.contDiffAt).of_le (hle n))
      ((hfkz z hz).of_le (hle n)) P1 Pk (0 + 0) (-(1 + p)) b1 bk
    have b3 := c03c_aux_symbol_mul hz n
      (((hfcs.contDiffAt.mul hfes.contDiffAt).mul (hfkz z hz)).of_le (hle n))
      (hb.contDiffAt.of_le (hle n)) P2 (fun i => Cs i * B) (0 + 0 + -(1 + p)) K b2 bb j hj
    rw [hg]
    have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * P2 i * (Cs (j - i) * B)) =
        T j * B := by
      rw [hT, Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum] at b3
    have hexp : (0 + 0 + -(1 + p) + K - j : ℝ) = K - 1 - p - j := by ring
    rw [hexp] at b3
    refine b3.trans ?_
    have hTj : T j ≤ 1 + ∑ i ∈ Finset.range (n + 1), |T i| := by
      have : |T j| ≤ ∑ i ∈ Finset.range (n + 1), |T i| :=
        Finset.single_le_sum (f := fun i => |T i|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
      linarith [le_abs_self (T j)]
    have : 0 ≤ |z| ^ (K - 1 - p - j) := by positivity
    gcongr

theorem c03c_aux_abs_rpow_ii {s R : ℝ} (hs : -1 < s) (hR : 0 ≤ R) :
    IntervalIntegrable (fun z : ℝ => |z| ^ s) volume (-R) R ∧
    ∫ z in (-R)..R, |z| ^ s = 2 * (R ^ (s + 1) / (s + 1)) := by
  have h0 : IntervalIntegrable (fun z : ℝ => z ^ s) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' hs
  have heq : EqOn (fun z : ℝ => |z| ^ s) (fun z : ℝ => z ^ s) (uIcc 0 R) := by
    intro z hz
    rw [uIcc_of_le hR] at hz
    simp [abs_of_nonneg hz.1]
  have h1 : IntervalIntegrable (fun z : ℝ => |z| ^ s) volume 0 R :=
    (intervalIntegrable_congr (fun z hz => heq (uIoc_subset_uIcc hz))).mpr h0
  have h2 : IntervalIntegrable (fun z : ℝ => |z| ^ s) volume (-R) 0 := by
    have := (IntervalIntegrable.iff_comp_neg (f := fun z : ℝ => |z| ^ s) (a := 0) (b := R)
      (by simp)).mp h1
    simpa [abs_neg] using this.symm
  have hI1 : ∫ z in (0:ℝ)..R, |z| ^ s = R ^ (s + 1) / (s + 1) := by
    rw [intervalIntegral.integral_congr heq, integral_rpow (Or.inl hs),
      Real.zero_rpow (by linarith), sub_zero]
  have hI2 : ∫ z in (-R)..0, |z| ^ s = R ^ (s + 1) / (s + 1) := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun z : ℝ => |z| ^ s)
    simp only [abs_neg, neg_zero] at this
    rw [← this, hI1]
  refine ⟨h2.trans h1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h2 h1, hI1, hI2]
  ring


theorem c03c_aux_abs_rpow_ind {s R : ℝ} (hs : -1 < s) (hR : 0 ≤ R) :
    Integrable (Set.indicator (Icc (-R) R) (fun z : ℝ => |z| ^ s)) ∧
    ∫ z, Set.indicator (Icc (-R) R) (fun z : ℝ => |z| ^ s) z = 2 * (R ^ (s + 1) / (s + 1)) := by
  obtain ⟨hii, hI⟩ := c03c_aux_abs_rpow_ii hs hR
  have hle : -R ≤ R := by linarith
  have hon : IntegrableOn (fun z : ℝ => |z| ^ s) (Icc (-R) R) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hii
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mpr hon, ?_⟩
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, hI]

/-- Blueprint: lem:c03_homogeneous_near.  Absolute bound for the near-diagonal piece:
`|∫ χ₁(Λz) e^{iφ-ηz²} b |z|^{-1-p}| ≤ 2C₀B/(K-p) (2/Λ)^{K-p}`, the integrand being integrable. -/
theorem c03_homogeneous_near (p K B C₀ Λ η : ℝ) (hp : 0 < p) (hp1 : p < 1) (hK : p < K)
    (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hΛ : 0 < Λ) (hη : 0 ≤ η) (b : ℝ → ℂ)
    (hb : AEStronglyMeasurable b) (hbd : ∀ z : ℝ, z ≠ 0 → ‖b z‖ ≤ C₀ * B * |z| ^ K)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (χ₁ : ℝ → ℝ) (hχm : Measurable χ₁)
    (hχ01 : ∀ z, 0 ≤ χ₁ z ∧ χ₁ z ≤ 1) (hχs : ∀ z, 2 < |z| → χ₁ z = 0) :
    Integrable (fun z : ℝ => (χ₁ (Λ * z) : ℂ) * (Complex.exp (Complex.I * (φ z : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ))) ∧
    ‖∫ z : ℝ, (χ₁ (Λ * z) : ℂ) * (Complex.exp (Complex.I * (φ z : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ))‖ ≤
      2 * C₀ * B / (K - p) * (2 / Λ) ^ (K - p) := by
  set R := 2 / Λ with hRdef
  have hR : 0 ≤ R := by positivity
  have hs : -1 < K - 1 - p := by linarith
  obtain ⟨hgi, hgI⟩ := c03c_aux_abs_rpow_ind hs hR
  have hm1 : Measurable (fun z : ℝ => (χ₁ (Λ * z) : ℂ)) :=
    Complex.measurable_ofReal.comp (hχm.comp (measurable_const_mul Λ))
  have hm2 : Measurable (fun z : ℝ => Complex.exp (Complex.I * (φ z : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))) := by
    have : Measurable (fun z : ℝ => Complex.exp (Complex.I * (φ z : ℂ))) :=
      Complex.measurable_exp.comp ((measurable_const_mul _).comp (Complex.measurable_ofReal.comp hφ))
    exact this.mul (by fun_prop)
  have hm3 : Measurable (fun z : ℝ => ((|z| ^ (1 + p) : ℝ) : ℂ)) := by fun_prop
  have hmeas := hm1.aestronglyMeasurable.mul
    ((hm2.aestronglyMeasurable.mul hb).div₀ hm3.aestronglyMeasurable)
  set F := fun z : ℝ => (χ₁ (Λ * z) : ℂ) * (Complex.exp (Complex.I * (φ z : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ)) with hF
  have hbound : ∀ᵐ z ∂volume, ‖F z‖ ≤
      (C₀ * B) * Set.indicator (Icc (-R) R) (fun z : ℝ => |z| ^ (K - 1 - p)) z := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
    have hzpos : 0 < |z| := abs_pos.mpr hz
    by_cases hzR : z ∈ Icc (-R) R
    · rw [Set.indicator_of_mem hzR]
      simp only [hF, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |χ₁ (Λ * z)| ≤ 1 := by
        rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
      have h2 : ‖Complex.exp (Complex.I * (φ z : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      have h3 : ‖Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        simp only [Complex.neg_re, Complex.ofReal_re]
        exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
      have h4 : |(|z| ^ (1 + p))| = |z| ^ (1 + p) := abs_of_nonneg (by positivity)
      rw [h2, h4]
      have hpow : |z| ^ K / |z| ^ (1 + p) = |z| ^ (K - 1 - p) := by
        rw [← Real.rpow_sub hzpos]; ring_nf
      have hb' := hbd z hz
      have hden : 0 < |z| ^ (1 + p) := by positivity
      calc |χ₁ (Λ * z)| * (1 * ‖Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ * ‖b z‖ / |z| ^ (1 + p))
          ≤ 1 * (1 * 1 * (C₀ * B * |z| ^ K) / |z| ^ (1 + p)) := by
            gcongr
        _ = C₀ * B * |z| ^ (K - 1 - p) := by rw [← hpow]; ring
    · rw [Set.indicator_of_notMem hzR, mul_zero]
      have : 2 < |Λ * z| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hzR
        rw [abs_mul, abs_of_pos hΛ]
        rcases hzR with h | h
        · have : 2 / Λ < -z := by linarith
          rw [div_lt_iff₀ hΛ] at this
          rw [abs_of_neg (by nlinarith)]; linarith
        · rw [div_lt_iff₀ hΛ] at h
          rw [abs_of_pos (by nlinarith)]; linarith
      simp [hF, hχs _ this]
  have hmeas' : AEStronglyMeasurable F := by rw [hF]; exact hmeas
  clear_value F
  have hFi : Integrable F := Integrable.mono' (hgi.const_mul (C₀ * B)) hmeas' hbound
  refine ⟨hFi, ?_⟩
  calc ‖∫ z, F z‖ ≤ ∫ z, (C₀ * B) * Set.indicator (Icc (-R) R) (fun z : ℝ => |z| ^ (K - 1 - p)) z :=
        norm_integral_le_of_norm_le (hgi.const_mul (C₀ * B)) hbound
    _ = 2 * C₀ * B / (K - p) * (2 / Λ) ^ (K - p) := by
        rw [integral_const_mul, hgI]
        have : K - 1 - p + 1 = K - p := by ring
        rw [this]; ring

theorem c03c_aux_integrable_comp_abs {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : IntegrableOn f (Ioi 0)) : Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) := by
    refine hf.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  have := int_Iic.union hf'
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- `∫_{|z| ≥ R} |z|^s dz = 2 R^{s+1}/(-(s+1))` for `s < -1`, `R > 0`. -/
theorem c03c_aux_abs_rpow_tail {s R : ℝ} (hs : s < -1) (hR : 0 < R) :
    Integrable (Set.indicator {z : ℝ | R ≤ |z|} (fun z : ℝ => |z| ^ s)) ∧
    ∫ z, Set.indicator {z : ℝ | R ≤ |z|} (fun z : ℝ => |z| ^ s) z = 2 * (R ^ (s + 1) / (-(s + 1))) := by
  set f : ℝ → ℝ := Set.indicator (Ici R) (fun t => t ^ s) with hf
  have hfa : (fun z => f |z|) = Set.indicator {z : ℝ | R ≤ |z|} (fun z : ℝ => |z| ^ s) := by
    funext z
    simp only [hf, Set.indicator, mem_Ici, mem_ofPred_eq]
  have hon : IntegrableOn f (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => t ^ s) (Ioi R) := integrableOn_Ioi_rpow_of_lt hs hR
    have h2 : IntegrableOn (fun t : ℝ => t ^ s) (Ici R) := (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
    have h3 : Integrable f := (integrable_indicator_iff measurableSet_Ici).mpr h2
    exact h3.integrableOn
  refine ⟨hfa ▸ c03c_aux_integrable_comp_abs hon, ?_⟩
  rw [← hfa, integral_comp_abs]
  have : ∫ x in Ioi (0 : ℝ), f x = ∫ x in Ioi R, x ^ s := by
    rw [hf, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (Ici_subset_Ioi.mpr hR), integral_Ici_eq_integral_Ioi]
  rw [this, integral_Ioi_rpow_of_lt hs hR, div_neg]
  ring


theorem c03c_aux_far_arith {C B Λ K p : ℝ} {L : ℕ} (hΛ : 0 < Λ) :
    C * B * (Λ ^ L)⁻¹ * (2 * ((1 / Λ) ^ (K - 1 - p - L + 1) / (-(K - 1 - p - L + 1)))) =
      2 * C * B * Λ ^ (p - K) / (L + p - K) := by
  have hx : K - 1 - p - (L : ℝ) + 1 = K - p - L := by ring
  have h1 : (1 / Λ) ^ (K - p - L) = Λ ^ (-(K - p - L)) := by
    rw [one_div, Real.inv_rpow hΛ.le, Real.rpow_neg hΛ.le]
  have h2 : (Λ ^ L)⁻¹ = Λ ^ (-(L : ℝ)) := by
    rw [Real.rpow_neg hΛ.le, Real.rpow_natCast]
  have hΛpow : Λ ^ (-(L : ℝ)) * Λ ^ (-(K - p - L)) = Λ ^ (p - K) := by
    rw [← Real.rpow_add hΛ]; ring_nf
  have hden : -(K - p - (L : ℝ)) = L + p - K := by ring
  rw [hx, h1, h2, ← hΛpow]
  generalize Λ ^ (-(L : ℝ)) = u
  generalize Λ ^ (-(K - p - L)) = v
  rw [hden]
  ring

/-- Blueprint: lem:c03_homogeneous_far.  For `g = g_{η,Λ}` and an integer `L > K - p`:
`∫ e^{iφ} g = (-1)^L ∫ e^{iφ} L_φ^L g`, `|L_φ^L g(z)| ≤ C B Λ^{-L} |z|^{K-1-p-L} 1_{|z| ≥ 1/Λ}`,
all integrals absolutely convergent, and the modulus is `≤ 2CBΛ^{p-K}/(L+p-K)`;
`C = C(p,K,L,c₀,χ₁,C_0,…,C_{L+1})`. -/
theorem c03_homogeneous_far (p K c₀ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hK : p < K) (hc₀ : 0 < c₀)
    (L : ℕ) (hL : K - p < L)
    (χ₁ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ₁) (hχ01 : ∀ z, 0 ≤ χ₁ z ∧ χ₁ z ≤ 1)
    (hχ1 : ∀ z ∈ Icc (-1 : ℝ) 1, χ₁ z = 1) (hχs : ∀ z, 2 < |z| → χ₁ z = 0) :
    ∀ Cs : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ (B Λ η : ℝ) (U : Set ℝ) (b : ℝ → ℂ) (φ : ℝ → ℝ),
      0 ≤ B → 0 < Λ → 0 ≤ η → IsOpen U → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b →
      tsupport b ⊆ U → ContDiffOn ℝ (⊤ : ℕ∞) φ U →
      (∀ z ∈ U, z ≠ 0 → ∀ j ≤ L + 1, ‖iteratedDeriv j b z‖ ≤ Cs j * B * |z| ^ (K - j)) →
      (∀ z ∈ U, z ≠ 0 → ∀ j ≤ L + 1,
        |iteratedDeriv j (fun z => 1 / deriv φ z) z| ≤ Cs j * Λ⁻¹ * |z| ^ (-(j : ℝ))) →
      (∀ z ∈ U, c₀⁻¹ * Λ ≤ |deriv φ z| ∧ |deriv φ z| ≤ c₀ * Λ) →
      Integrable (fun z => Complex.exp (Complex.I * (φ z : ℂ)) * c03c_homg p χ₁ Λ η b z) ∧
      Integrable (fun z => Complex.exp (Complex.I * (φ z : ℂ)) *
        (c03c_ibpL U φ)^[L] (c03c_homg p χ₁ Λ η b) z) ∧
      (∫ z, Complex.exp (Complex.I * (φ z : ℂ)) * c03c_homg p χ₁ Λ η b z) =
        (-1 : ℂ) ^ L * ∫ z, Complex.exp (Complex.I * (φ z : ℂ)) *
          (c03c_ibpL U φ)^[L] (c03c_homg p χ₁ Λ η b) z ∧
      (∀ z, ‖(c03c_ibpL U φ)^[L] (c03c_homg p χ₁ Λ η b) z‖ ≤
        Set.indicator {z : ℝ | 1 / Λ ≤ |z|}
          (fun z => C * B * (Λ ^ L)⁻¹ * |z| ^ (K - 1 - p - L)) z) ∧
      ‖∫ z, Complex.exp (Complex.I * (φ z : ℂ)) * c03c_homg p χ₁ Λ η b z‖ ≤
        2 * C * B * Λ ^ (p - K) / (L + p - K) := by
  intro Cs
  obtain ⟨D, hD, hDb⟩ := (c03_homogeneous_cutoff_symbol p K hp hp1 hK (L + 1) χ₁ hχ hχ01 hχ1
    hχs).2 (fun j => |Cs j|)
  obtain ⟨C, hC, hCb⟩ := c03_ibp_symbol_iteration L 0 (K - 1 - p) (fun _ => D)
    (fun l => |Cs l|) (fun _ => hD.le) (fun l => abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro B Λ η U b φ hB hΛ hη hU hb hbc hbU hφ hbd hqd hφd
  have hφ' : ∀ z ∈ U, deriv φ z ≠ 0 := by
    intro z hz h
    have := (hφd z hz).1
    rw [h, abs_zero] at this
    have : 0 < c₀⁻¹ * Λ := by positivity
    linarith
  -- bounds on b everywhere
  have hbd' : ∀ j ≤ L + 1, ∀ z : ℝ, z ≠ 0 → ‖iteratedDeriv j b z‖ ≤ |Cs j| * B * |z| ^ (K - j) := by
    intro j hj z hz
    by_cases hzU : z ∈ U
    · refine (hbd z hzU hz j hj).trans ?_
      have : 0 ≤ |z| ^ (K - j) := by positivity
      gcongr; exact le_abs_self _
    · have hz' : z ∉ tsupport b := fun h => hzU (hbU h)
      have hev := (notMem_tsupport_iff_eventuallyEq.mp hz').iteratedDeriv_eq j
      rw [hev, show (0 : ℝ → ℂ) = fun _ => (0 : ℂ) from rfl, iteratedDeriv_const]
      have : 0 ≤ |Cs j| * B * |z| ^ (K - j) := by positivity
      split_ifs <;> simpa using this
  obtain ⟨hgs, hg0, hgb⟩ := hDb B Λ η b hB hΛ hη hb hbd'
  set g := c03c_homg p χ₁ Λ η b with hgdef
  have hsupp_b : tsupport g ⊆ tsupport b := by
    refine closure_mono ?_
    intro t ht
    simp only [Function.mem_support] at ht ⊢
    intro h0; apply ht; simp [hgdef, c03c_homg, h0]
  have hsupp_L : tsupport g ⊆ {z : ℝ | 1 / Λ ≤ |z|} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_abs)
    intro t ht
    simp only [Function.mem_support] at ht
    by_contra h
    simp only [mem_ofPred_eq, not_le] at h
    exact ht (hg0 t h.le)
  have hgc : HasCompactSupport g := IsCompact.of_isClosed_subset hbc (isClosed_tsupport _) hsupp_b
  set U' := U ∩ {0}ᶜ with hU'
  have hU'o : IsOpen U' := hU.inter isOpen_compl_singleton
  have hgU' : tsupport g ⊆ U' := by
    intro z hz
    refine ⟨hbU (hsupp_b hz), ?_⟩
    have := hsupp_L hz
    simp only [mem_ofPred_eq] at this
    intro h; simp only [mem_singleton_iff] at h
    rw [h, abs_zero] at this
    have : 0 < 1 / Λ := by positivity
    linarith
  have hφU' : ContDiffOn ℝ (⊤ : ℕ∞) φ U' := hφ.mono inter_subset_left
  -- iterates agree for U and U'
  have hiter : ∀ j, (c03c_ibpL U φ)^[j] g = (c03c_ibpL U' φ)^[j] g ∧
      ContDiff ℝ (⊤ : ℕ∞) ((c03c_ibpL U' φ)^[j] g) ∧
      HasCompactSupport ((c03c_ibpL U' φ)^[j] g) ∧ tsupport ((c03c_ibpL U' φ)^[j] g) ⊆ tsupport g := by
    intro j
    induction j with
    | zero => exact ⟨rfl, hgs, hgc, subset_rfl⟩
    | succ j ih =>
      obtain ⟨e, s1, s2, s3⟩ := ih
      obtain ⟨t1, t2, t3⟩ := c03c_aux_ibpL_smooth hU'o s1 s2 (s3.trans hgU') hφU'
        (fun z hz => hφ' z hz.1)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', e]
      refine ⟨?_, t1, t2, t3.trans s3⟩
      rw [c03c_aux_ibpL_eq (s3.trans (hgU'.trans inter_subset_left)) φ,
        c03c_aux_ibpL_eq (s3.trans hgU') φ]
  obtain ⟨hI1, hI2, hI3, -⟩ := c03_ibp_compact_iteration U hU L φ
    (hφ.of_le (by exact_mod_cast le_top)) hφ' g (hgs.of_le (by exact_mod_cast le_top)) hgc
    (hsupp_b.trans hbU)
  have hcomm : ∀ f : ℝ → ℂ, (fun z => Complex.exp (Complex.I * (φ z : ℂ)) * f z) =
      fun z => f z * Complex.exp (Complex.I * (φ z : ℂ)) := fun f => by funext z; ring
  have hInt0 := hI2 0 (Nat.zero_le _)
  have hIntL := hI2 L le_rfl
  simp only [Function.iterate_zero, id_eq] at hInt0
  -- pointwise bound
  have hpt : ∀ z, ‖(c03c_ibpL U φ)^[L] g z‖ ≤ Set.indicator {z : ℝ | 1 / Λ ≤ |z|}
      (fun z => C * B * (Λ ^ L)⁻¹ * |z| ^ (K - 1 - p - L)) z := by
    intro z
    obtain ⟨e, s1, s2, s3⟩ := hiter L
    rw [e]
    by_cases hz : z ∈ tsupport g
    · have hzL := hsupp_L hz
      rw [Set.indicator_of_mem hzL]
      have hzU' := hgU' hz
      have := hCb U' g φ B Λ hU'o inter_subset_right hgs hgc hgU' hφU' hB hΛ
        (fun z hz => hφ' z hz.1)
        (fun z hz l hl => by
          have := hgb l (by omega) z hz.2
          simpa using this)
        (fun z hz l hl => (hqd z hz.1 hz.2 l (by omega)).trans (by
          have : 0 ≤ Λ⁻¹ * |z| ^ (-(l : ℝ)) := by positivity
          rw [mul_assoc, mul_assoc]; gcongr; exact le_abs_self _)) z hzU'
      simpa using this
    · have hz' : z ∉ tsupport ((c03c_ibpL U' φ)^[L] g) := fun h => hz (s3 h)
      rw [image_eq_zero_of_notMem_tsupport hz', norm_zero]
      by_cases hzL : z ∈ {z : ℝ | 1 / Λ ≤ |z|}
      · rw [Set.indicator_of_mem hzL]; positivity
      · rw [Set.indicator_of_notMem hzL]
  have hs : K - 1 - p - L < -1 := by linarith
  obtain ⟨htI, htV⟩ := c03c_aux_abs_rpow_tail hs (by positivity : (0 : ℝ) < 1 / Λ)
  have hident : (∫ z, Complex.exp (Complex.I * (φ z : ℂ)) * g z) =
      (-1 : ℂ) ^ L * ∫ z, Complex.exp (Complex.I * (φ z : ℂ)) * (c03c_ibpL U φ)^[L] g z := by
    rw [hcomm, hcomm]; exact hI3
  refine ⟨hcomm g ▸ hInt0, hcomm _ ▸ hIntL, hident, hpt, ?_⟩
  rw [hident, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hmaj : ∀ z, ‖Complex.exp (Complex.I * (φ z : ℂ)) * (c03c_ibpL U φ)^[L] g z‖ ≤
      (C * B * (Λ ^ L)⁻¹) * Set.indicator {z : ℝ | 1 / Λ ≤ |z|} (fun z : ℝ => |z| ^ (K - 1 - p - L)) z := by
    intro z
    have h1 : ‖Complex.exp (Complex.I * (φ z : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [norm_mul, h1, one_mul]
    refine (hpt z).trans (le_of_eq ?_)
    by_cases hz : z ∈ {z : ℝ | 1 / Λ ≤ |z|}
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  have hfin := norm_integral_le_of_norm_le (htI.const_mul (C * B * (Λ ^ L)⁻¹))
    (Eventually.of_forall hmaj)
  rw [integral_const_mul, htV] at hfin
  refine hfin.trans (le_of_eq ?_)
  exact c03c_aux_far_arith hΛ

/-! ## Far-region phase bounds for the homogeneous stationary phase -/

/-- Coefficients of `∂_ξ^k (y - ξ^p)⁻¹ = ∑_i a_{k,i} ξ^{pi-k} (y-ξ^p)^{-(i+1)}`. -/
def c03c_aux_farA (p : ℝ) : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 1 else 0
  | k + 1, i => c03c_aux_farA p k i * (p * i - k) +
      (if i = 0 then 0 else c03c_aux_farA p k (i - 1) * i * p)

theorem c03c_aux_farA_zero (p : ℝ) : ∀ k i, k < i → c03c_aux_farA p k i = 0 := by
  intro k
  induction k with
  | zero => intro i hi; simp [c03c_aux_farA, show i ≠ 0 by omega]
  | succ k ih =>
    intro i hi
    simp only [c03c_aux_farA, ih i (by omega), zero_mul, zero_add, show i ≠ 0 by omega, ite_false,
      ih (i - 1) (by omega)]

/-- The term `ξ^{r} (y - ξ^p)^m` and its `ξ`-derivative. -/
theorem c03c_aux_term_deriv (p y r : ℝ) (m : ℤ) {ξ : ℝ} (hξ : 0 < ξ) (hw : y - ξ ^ p ≠ 0) :
    HasDerivAt (fun x : ℝ => x ^ r * (y - x ^ p) ^ m)
      (r * ξ ^ (r - 1) * (y - ξ ^ p) ^ m +
        ξ ^ r * ((m : ℝ) * (y - ξ ^ p) ^ (m - 1) * (-(p * ξ ^ (p - 1))))) ξ := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ r) (r * ξ ^ (r - 1)) ξ :=
    Real.hasDerivAt_rpow_const (Or.inl hξ.ne')
  have h2 : HasDerivAt (fun x : ℝ => y - x ^ p) (-(p * ξ ^ (p - 1))) ξ :=
    (Real.hasDerivAt_rpow_const (Or.inl hξ.ne')).const_sub y
  have h3 : HasDerivAt (fun x : ℝ => (y - x ^ p) ^ m)
      ((m : ℝ) * (y - ξ ^ p) ^ (m - 1) * (-(p * ξ ^ (p - 1)))) ξ := by
    have h4 : HasDerivAt (fun x : ℝ => x ^ m) ((m : ℝ) * (y - ξ ^ p) ^ (m - 1)) (y - ξ ^ p) :=
      hasDerivAt_zpow m (y - ξ ^ p) (Or.inl hw)
    exact h4.comp ξ h2
  exact h1.mul h3

/-- Explicit `ξ`-derivatives of `(y - ξ^p)⁻¹` on `{ξ > 0, ξ^p ≠ y}`. -/
theorem c03c_aux_xi_derivs (p y : ℝ) (k : ℕ) : ∀ ξ : ℝ, 0 < ξ → y - ξ ^ p ≠ 0 →
    iteratedDeriv k (fun ξ' : ℝ => 1 / (y - ξ' ^ p)) ξ =
      ∑ i ∈ Finset.range (k + 1), c03c_aux_farA p k i * ξ ^ (p * i - k) *
        (y - ξ ^ p) ^ (-((i : ℤ) + 1)) := by
  induction k with
  | zero =>
    intro ξ _ _
    simp [c03c_aux_farA]
  | succ k ih =>
    intro ξ hξ hw
    have hnb : ∀ᶠ x in 𝓝 ξ, 0 < x ∧ y - x ^ p ≠ 0 :=
      (eventually_gt_nhds hξ).and
        ((continuousAt_const.sub (Real.continuousAt_rpow_const ξ p (Or.inl hξ.ne'))).eventually_ne hw)
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun ξ' : ℝ => 1 / (y - ξ' ^ p)) =ᶠ[𝓝 ξ] fun x =>
        ∑ i ∈ Finset.range (k + 1), c03c_aux_farA p k i * (x ^ (p * i - k) *
          (y - x ^ p) ^ (-((i : ℤ) + 1))) := by
      filter_upwards [hnb] with x hx
      rw [ih x hx.1 hx.2]; simp only [mul_assoc]
    rw [hev.deriv_eq]
    have hd := HasDerivAt.fun_sum (u := Finset.range (k + 1)) (fun i _ =>
      (c03c_aux_term_deriv p y (p * i - k) (-((i : ℤ) + 1)) hξ hw).const_mul (c03c_aux_farA p k i))
    rw [hd.deriv]
    set w := y - ξ ^ p with hwdef
    have hterm : ∀ i : ℕ, c03c_aux_farA p k i * ((p * i - k) * ξ ^ (p * i - k - 1) *
        w ^ (-((i : ℤ) + 1)) + ξ ^ (p * i - k) * (((-((i : ℤ) + 1) : ℤ) : ℝ) *
          w ^ (-((i : ℤ) + 1) - 1) * (-(p * ξ ^ (p - 1))))) =
        c03c_aux_farA p k i * (p * i - k) * ξ ^ (p * i - ((k + 1 : ℕ) : ℝ)) * w ^ (-((i : ℤ) + 1)) +
        c03c_aux_farA p k i * (((i + 1 : ℕ) : ℝ) * p) * ξ ^ (p * ((i + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) *
          w ^ (-(((i + 1 : ℕ) : ℤ) + 1)) := by
      intro i
      have e1 : p * i - k - 1 = p * i - ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      have e2 : ξ ^ (p * i - k) * ξ ^ (p - 1) = ξ ^ (p * ((i + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add hξ]; push_cast; ring_nf
      have e3 : (-((i : ℤ) + 1) - 1) = -(((i + 1 : ℕ) : ℤ) + 1) := by push_cast; ring
      rw [e1, e3, ← e2]
      push_cast
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    have hR : ∀ x : ℕ, c03c_aux_farA p (k + 1) x * ξ ^ (p * x - ((k + 1 : ℕ) : ℝ)) *
        w ^ (-((x : ℤ) + 1)) =
        c03c_aux_farA p k x * (p * x - k) * ξ ^ (p * x - ((k + 1 : ℕ) : ℝ)) * w ^ (-((x : ℤ) + 1)) +
        (if x = 0 then 0 else c03c_aux_farA p k (x - 1) * x * p) *
          ξ ^ (p * x - ((k + 1 : ℕ) : ℝ)) * w ^ (-((x : ℤ) + 1)) := by
      intro x; simp only [c03c_aux_farA]; ring
    have hA : ∑ x ∈ Finset.range (k + 1 + 1), c03c_aux_farA p k x * (p * x - k) *
        ξ ^ (p * x - ((k + 1 : ℕ) : ℝ)) * w ^ (-((x : ℤ) + 1)) =
        ∑ x ∈ Finset.range (k + 1), c03c_aux_farA p k x * (p * x - k) *
        ξ ^ (p * x - ((k + 1 : ℕ) : ℝ)) * w ^ (-((x : ℤ) + 1)) := by
      rw [Finset.sum_range_succ, c03c_aux_farA_zero p k (k + 1) (by omega)]; simp
    have hB : ∑ x ∈ Finset.range (k + 1 + 1),
        (if x = 0 then 0 else c03c_aux_farA p k (x - 1) * x * p) *
          ξ ^ (p * x - ((k + 1 : ℕ) : ℝ)) * w ^ (-((x : ℤ) + 1)) =
        ∑ x ∈ Finset.range (k + 1), c03c_aux_farA p k x * (((x + 1 : ℕ) : ℝ) * p) *
          ξ ^ (p * ((x + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) * w ^ (-(((x + 1 : ℕ) : ℤ) + 1)) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, ite_true, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast; ring
    rw [Finset.sum_congr rfl (fun x _ => hR x), Finset.sum_add_distrib, hA, hB]


/-- Explicit mixed derivatives `∂_y^j ∂_ξ^k (y - ξ^p)⁻¹`. -/
theorem c03c_aux_mixed_derivs (p ξ : ℝ) (hξ : 0 < ξ) (k j : ℕ) : ∀ y : ℝ, y - ξ ^ p ≠ 0 →
    iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' : ℝ => 1 / (y' - ξ' ^ p)) ξ) y =
      ∑ i ∈ Finset.range (k + 1), c03c_aux_farA p k i * ξ ^ (p * i - k) *
        (∏ l ∈ Finset.range j, (((-((i : ℤ) + 1) : ℤ) : ℝ) - l)) *
        (y - ξ ^ p) ^ (-((i : ℤ) + 1) - j) := by
  induction j with
  | zero =>
    intro y hy
    simp only [iteratedDeriv_zero, Finset.prod_range_zero, mul_one, CharP.cast_eq_zero, sub_zero]
    exact c03c_aux_xi_derivs p y k ξ hξ hy
  | succ j ih =>
    intro y hy
    rw [iteratedDeriv_succ]
    have hnb : ∀ᶠ x in 𝓝 y, x - ξ ^ p ≠ 0 :=
      (continuous_id.sub continuous_const).continuousAt.eventually_ne hy
    have hev : iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' : ℝ => 1 / (y' - ξ' ^ p)) ξ)
        =ᶠ[𝓝 y] fun x => ∑ i ∈ Finset.range (k + 1), (c03c_aux_farA p k i * ξ ^ (p * i - k) *
          (∏ l ∈ Finset.range j, (((-((i : ℤ) + 1) : ℤ) : ℝ) - l))) *
          (x - ξ ^ p) ^ (-((i : ℤ) + 1) - j) := by
      filter_upwards [hnb] with x hx using ih x hx
    rw [hev.deriv_eq]
    have ht : ∀ i : ℕ, ∀ C : ℝ, HasDerivAt (fun x : ℝ => C * (x - ξ ^ p) ^ (-((i : ℤ) + 1) - j))
        (C * (((-((i : ℤ) + 1) - j : ℤ) : ℝ) * (y - ξ ^ p) ^ (-((i : ℤ) + 1) - j - 1))) y := by
      intro i C
      have h4 : HasDerivAt (fun x : ℝ => x ^ (-((i : ℤ) + 1) - j))
          (((-((i : ℤ) + 1) - j : ℤ) : ℝ) * (y - ξ ^ p) ^ (-((i : ℤ) + 1) - j - 1)) (y - ξ ^ p) :=
        hasDerivAt_zpow _ _ (Or.inl hy)
      have h5 := h4.comp y ((hasDerivAt_id y).sub_const (ξ ^ p))
      simpa using h5.const_mul C
    have hd := HasDerivAt.fun_sum (u := Finset.range (k + 1)) (fun i _ =>
      ht i (c03c_aux_farA p k i * ξ ^ (p * i - k) *
          (∏ l ∈ Finset.range j, (((-((i : ℤ) + 1) : ℤ) : ℝ) - l))))
    rw [hd.deriv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_range_succ]
    have : (-((i : ℤ) + 1) - j - 1) = (-((i : ℤ) + 1) - ((j + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [this]
    push_cast
    ring


/-- Lower bound `|y - ξ^p| ≥ (1-r^p)/2 (y+ξ^p)` away from `λ₀(y)`. -/
theorem c03c_aux_far_lower {p r : ℝ} (hp : 0 < p) (hr0 : 0 < r) (hr1 : r < 1) {y ξ : ℝ}
    (hy : 0 < y) (hξ : 0 < ξ) (h : ξ ≤ r * lambda0 p y ∨ lambda0 p y / r ≤ ξ) :
    (1 - r ^ p) / 2 * (y + ξ ^ p) ≤ |y - ξ ^ p| := by
  have hl : lambda0 p y ^ p = y := by
    rw [lambda0, ← Real.rpow_mul hy.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  have hl0 : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
  have hrp : r ^ p < 1 := Real.rpow_lt_one hr0.le hr1 hp
  have hrp0 : 0 < r ^ p := Real.rpow_pos_of_pos hr0 _
  have hξp : 0 < ξ ^ p := Real.rpow_pos_of_pos hξ _
  rcases h with h | h
  · have : ξ ^ p ≤ r ^ p * y := by
      rw [← hl, ← Real.mul_rpow hr0.le hl0.le]
      exact Real.rpow_le_rpow hξ.le h hp.le
    have h1 : ξ ^ p ≤ y := by nlinarith
    rw [abs_of_pos (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hrp.le)]
  · have : y ≤ r ^ p * ξ ^ p := by
      have h2 : lambda0 p y ≤ r * ξ := by rwa [div_le_iff₀ hr0, mul_comm] at h
      rw [← hl, ← Real.mul_rpow hr0.le hξ.le]
      exact Real.rpow_le_rpow hl0.le h2 hp.le
    have h1 : y ≤ ξ ^ p := by nlinarith
    rw [abs_of_neg (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hrp.le)]

theorem c03c_aux_far_deriv_bound (p : ℝ) (hp : 0 < p) (c : ℝ) (hc : 0 < c) (k j : ℕ) :
    ∃ C, 0 < C ∧ ∀ y ξ : ℝ, 0 < y → 0 < ξ → c * (y + ξ ^ p) ≤ |y - ξ ^ p| →
      |iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' => 1 / (y' - ξ' ^ p)) ξ) y| ≤
        C * ξ ^ (-(k : ℝ)) * (y + ξ ^ p) ^ (-1 - (j : ℝ)) := by
  set K : ℕ → ℝ := fun i => |c03c_aux_farA p k i| *
    |∏ l ∈ Finset.range j, (((-((i : ℤ) + 1) : ℤ) : ℝ) - l)| * (c ^ (i + 1 + j))⁻¹ with hK
  refine ⟨1 + ∑ i ∈ Finset.range (k + 1), K i, by
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), K i := Finset.sum_nonneg fun i _ => by positivity
    linarith, ?_⟩
  intro y ξ hy hξ hlow
  have hξp : 0 < ξ ^ p := Real.rpow_pos_of_pos hξ _
  set s := y + ξ ^ p with hs
  have hspos : 0 < s := by positivity
  have hw : y - ξ ^ p ≠ 0 := by
    intro h; rw [h, abs_zero] at hlow; nlinarith
  rw [c03c_aux_mixed_derivs p ξ hξ k j y hw]
  have hwabs : c * s ≤ |y - ξ ^ p| := hlow
  have hterm : ∀ i ∈ Finset.range (k + 1), |c03c_aux_farA p k i * ξ ^ (p * i - k) *
      (∏ l ∈ Finset.range j, (((-((i : ℤ) + 1) : ℤ) : ℝ) - l)) *
      (y - ξ ^ p) ^ (-((i : ℤ) + 1) - j)| ≤ K i * (ξ ^ (-(k : ℝ)) * s ^ (-1 - (j : ℝ))) := by
    intro i _
    have e1 : ξ ^ (p * i - k) = (ξ ^ p) ^ i * ξ ^ (-(k : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hξ, ← Real.rpow_natCast (ξ ^ p) i, ← Real.rpow_mul hξ.le]
    have e2 : (y - ξ ^ p) ^ (-((i : ℤ) + 1) - j) = ((y - ξ ^ p) ^ (i + 1 + j))⁻¹ := by
      rw [show (-((i : ℤ) + 1) - j) = -((i + 1 + j : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    have e3 : s ^ (-1 - (j : ℝ)) = s ^ i * (s ^ (i + 1 + j))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hspos.le, ← Real.rpow_add hspos]
      congr 1; push_cast; ring
    rw [e1, e2, e3, abs_mul, abs_mul, abs_mul, abs_mul, abs_inv, abs_pow, abs_pow,
      abs_of_pos hξp, abs_of_pos (Real.rpow_pos_of_pos hξ _)]
    have hpi : (ξ ^ p) ^ i ≤ s ^ i := pow_le_pow_left₀ hξp.le (by linarith) i
    have hwi : (c * s) ^ (i + 1 + j) ≤ |y - ξ ^ p| ^ (i + 1 + j) :=
      pow_le_pow_left₀ (by positivity) hwabs _
    have hinv : (|y - ξ ^ p| ^ (i + 1 + j))⁻¹ ≤ (c ^ (i + 1 + j))⁻¹ * (s ^ (i + 1 + j))⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      exact inv_anti₀ (by positivity) hwi
    simp only [hK]
    calc |c03c_aux_farA p k i| * ((ξ ^ p) ^ i * ξ ^ (-(k : ℝ))) *
          |∏ l ∈ Finset.range j, (((-((i : ℤ) + 1) : ℤ) : ℝ) - l)| * (|y - ξ ^ p| ^ (i + 1 + j))⁻¹
        ≤ |c03c_aux_farA p k i| * (s ^ i * ξ ^ (-(k : ℝ))) *
          |∏ l ∈ Finset.range j, (((-((i : ℤ) + 1) : ℤ) : ℝ) - l)| *
          ((c ^ (i + 1 + j))⁻¹ * (s ^ (i + 1 + j))⁻¹) := by gcongr
      _ = _ := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul]
  have : 0 ≤ ξ ^ (-(k : ℝ)) * s ^ (-1 - (j : ℝ)) := by positivity
  rw [mul_assoc]
  gcongr
  linarith

/-- Blueprint: lem:c03_sp_far_phase_bounds.  Away from `ξ = λ₀(y)`: `|y - ξ^p| ≥ c(y + ξ^p)` and
`|∂_y^j ∂_ξ^k (y - ξ^p)⁻¹| ≤ C_{k,j} ξ^{-k} (y + ξ^p)^{-1-j}`, on `ξ ≤ 3λ₀/4 ∨ ξ ≥ 3λ₀/2` and
(enlarged constants) on `ξ < 7λ₀/8 ∨ ξ > 5λ₀/4`. -/
theorem c03_sp_far_phase_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∃ c, 0 < c ∧ ∀ y ξ : ℝ, 0 < y → 0 < ξ →
      (ξ ≤ 3 * lambda0 p y / 4 ∨ 3 * lambda0 p y / 2 ≤ ξ) → c * (y + ξ ^ p) ≤ |y - ξ ^ p|) ∧
    (∀ k j : ℕ, ∃ C, 0 < C ∧ ∀ y ξ : ℝ, 0 < y → 0 < ξ →
      (ξ ≤ 3 * lambda0 p y / 4 ∨ 3 * lambda0 p y / 2 ≤ ξ) →
      |iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' => 1 / (y' - ξ' ^ p)) ξ) y| ≤
        C * ξ ^ (-(k : ℝ)) * (y + ξ ^ p) ^ (-1 - (j : ℝ))) ∧
    (∃ c, 0 < c ∧ ∀ y ξ : ℝ, 0 < y → 0 < ξ →
      (ξ < 7 * lambda0 p y / 8 ∨ 5 * lambda0 p y / 4 < ξ) → c * (y + ξ ^ p) ≤ |y - ξ ^ p|) ∧
    ∀ k j : ℕ, ∃ C, 0 < C ∧ ∀ y ξ : ℝ, 0 < y → 0 < ξ →
      (ξ < 7 * lambda0 p y / 8 ∨ 5 * lambda0 p y / 4 < ξ) →
      |iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' => 1 / (y' - ξ' ^ p)) ξ) y| ≤
        C * ξ ^ (-(k : ℝ)) * (y + ξ ^ p) ^ (-1 - (j : ℝ)) := by
  set c := (1 - (7 / 8 : ℝ) ^ p) / 2 with hcdef
  have hc : 0 < c := by
    have : (7 / 8 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
    rw [hcdef]; linarith
  have hwide : ∀ y ξ : ℝ, 0 < y → 0 < ξ →
      (ξ < 7 * lambda0 p y / 8 ∨ 5 * lambda0 p y / 4 < ξ) → c * (y + ξ ^ p) ≤ |y - ξ ^ p| := by
    intro y ξ hy hξ h
    have hl0 : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
    refine c03c_aux_far_lower hp (by norm_num) (by norm_num) hy hξ ?_
    rcases h with h | h
    · left; linarith
    · right; rw [div_le_iff₀ (by norm_num)]; linarith
  have hnarrow : ∀ y ξ : ℝ, 0 < y → 0 < ξ →
      (ξ ≤ 3 * lambda0 p y / 4 ∨ 3 * lambda0 p y / 2 ≤ ξ) →
      (ξ < 7 * lambda0 p y / 8 ∨ 5 * lambda0 p y / 4 < ξ) := by
    intro y ξ hy hξ h
    have hl0 : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
    rcases h with h | h
    · left; linarith
    · right; linarith
  refine ⟨⟨c, hc, fun y ξ hy hξ h => hwide y ξ hy hξ (hnarrow y ξ hy hξ h)⟩, ?_,
    ⟨c, hc, hwide⟩, ?_⟩
  · intro k j
    obtain ⟨C, hC, hCb⟩ := c03c_aux_far_deriv_bound p hp c hc k j
    exact ⟨C, hC, fun y ξ hy hξ h => hCb y ξ hy hξ (hwide y ξ hy hξ (hnarrow y ξ hy hξ h))⟩
  · intro k j
    obtain ⟨C, hC, hCb⟩ := c03c_aux_far_deriv_bound p hp c hc k j
    exact ⟨C, hC, fun y ξ hy hξ h => hCb y ξ hy hξ (hwide y ξ hy hξ h)⟩

/-! ### Two-variable partial-derivative calculus on `(y, ξ)` -/

/-- `∂_ξ F`. -/
def c03c_aux_Dx (F : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := fun y ξ => deriv (F y) ξ

/-- `∂_y F`. -/
def c03c_aux_Dy (F : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ := fun y ξ => deriv (fun y' => F y' ξ) y

theorem c03c_aux_iterDx (F : ℝ → ℝ → ℂ) (k : ℕ) (y : ℝ) :
    iteratedDeriv k (F y) = (c03c_aux_Dx^[k] F) y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']; rfl

theorem c03c_aux_iterDy (G : ℝ → ℝ → ℂ) (j : ℕ) (ξ : ℝ) :
    iteratedDeriv j (fun y' => G y' ξ) = fun y => (c03c_aux_Dy^[j] G) y ξ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']; rfl

/-- The statement's mixed derivative is `D_y^j D_ξ^k F`. -/
theorem c03c_aux_mixed_eq (F : ℝ → ℝ → ℂ) (j k : ℕ) (y ξ : ℝ) :
    iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' => F y' ξ') ξ) y =
      (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] F)) y ξ := by
  have : (fun y' => iteratedDeriv k (fun ξ' => F y' ξ') ξ) = fun y' => (c03c_aux_Dx^[k] F) y' ξ := by
    funext y'; exact congrFun (c03c_aux_iterDx F k y') ξ
  rw [this, c03c_aux_iterDy]

/-- Smoothness on an open set of `ℝ × ℝ`. -/
def c03c_aux_Sm (F : ℝ → ℝ → ℂ) (V : Set (ℝ × ℝ)) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) V

theorem c03c_aux_Sm_hasDerivAt_x {F : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) {y ξ : ℝ} (h : (y, ξ) ∈ V) :
    HasDerivAt (F y) (fderiv ℝ (Function.uncurry F) (y, ξ) (0, 1)) ξ := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (y, ξ)) (y, ξ) :=
    ((hF.contDiffAt (hV.mem_nhds h)).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasDerivAt (fun ξ' : ℝ => ((y, ξ') : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) ξ :=
    (hasDerivAt_const ξ y).prodMk (hasDerivAt_id ξ)
  exact h1.comp_hasDerivAt ξ h2

theorem c03c_aux_Sm_hasDerivAt_y {F : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) {y ξ : ℝ} (h : (y, ξ) ∈ V) :
    HasDerivAt (fun y' => F y' ξ) (fderiv ℝ (Function.uncurry F) (y, ξ) (1, 0)) y := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (y, ξ)) (y, ξ) :=
    ((hF.contDiffAt (hV.mem_nhds h)).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasDerivAt (fun y' : ℝ => ((y', ξ) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) y :=
    (hasDerivAt_id y).prodMk (hasDerivAt_const y ξ)
  exact h1.comp_hasDerivAt y h2

theorem c03c_aux_Sm_Dx {F : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) : c03c_aux_Sm (c03c_aux_Dx F) V := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry F)) V :=
    hF.fderiv_of_isOpen hV (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ (Function.uncurry F) q ((0, 1) : ℝ × ℝ)) V :=
    hd.clm_apply contDiffOn_const
  refine h2.congr fun q hq => ?_
  obtain ⟨y, ξ⟩ := q
  exact (c03c_aux_Sm_hasDerivAt_x hV hF hq).deriv

theorem c03c_aux_Sm_Dy {F : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) : c03c_aux_Sm (c03c_aux_Dy F) V := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Function.uncurry F)) V :=
    hF.fderiv_of_isOpen hV (by simp)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ (Function.uncurry F) q ((1, 0) : ℝ × ℝ)) V :=
    hd.clm_apply contDiffOn_const
  refine h2.congr fun q hq => ?_
  obtain ⟨y, ξ⟩ := q
  exact (c03c_aux_Sm_hasDerivAt_y hV hF hq).deriv

theorem c03c_aux_Sm_iter {F : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) (j k : ℕ) : c03c_aux_Sm (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] F)) V := by
  have hx : ∀ k, c03c_aux_Sm (c03c_aux_Dx^[k] F) V := by
    intro k; induction k with
    | zero => exact hF
    | succ k ih => rw [Function.iterate_succ_apply']; exact c03c_aux_Sm_Dx hV ih
  induction j with
  | zero => exact hx k
  | succ j ih => rw [Function.iterate_succ_apply']; exact c03c_aux_Sm_Dy hV ih

theorem c03c_aux_Sm_contDiffAt_x {F : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) {y ξ : ℝ} (h : (y, ξ) ∈ V) : ContDiffAt ℝ (⊤ : ℕ∞) (F y) ξ := by
  have h1 := hF.contDiffAt (hV.mem_nhds h)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun ξ' : ℝ => ((y, ξ') : ℝ × ℝ)) ξ :=
    contDiffAt_const.prodMk contDiffAt_id
  exact h1.comp ξ h2

theorem c03c_aux_Sm_contDiffAt_y {F : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) {y ξ : ℝ} (h : (y, ξ) ∈ V) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' => F y' ξ) y := by
  have h1 := hF.contDiffAt (hV.mem_nhds h)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : ℝ => ((y', ξ) : ℝ × ℝ)) y :=
    contDiffAt_id.prodMk contDiffAt_const
  exact h1.comp y h2


theorem c03c_aux_nhds_x {V : Set (ℝ × ℝ)} (hV : IsOpen V) {y ξ : ℝ} (h : (y, ξ) ∈ V) :
    ∀ᶠ ξ' in 𝓝 ξ, ((y, ξ') : ℝ × ℝ) ∈ V :=
  (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds h)

theorem c03c_aux_nhds_y {V : Set (ℝ × ℝ)} (hV : IsOpen V) {y ξ : ℝ} (h : (y, ξ) ∈ V) :
    ∀ᶠ y' in 𝓝 y, ((y', ξ) : ℝ × ℝ) ∈ V :=
  (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV.mem_nhds h)

theorem c03c_aux_eqOn_iter {F G : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hFG : ∀ q ∈ V, F q.1 q.2 = G q.1 q.2) (j k : ℕ) :
    ∀ q ∈ V, (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] F)) q.1 q.2 =
      (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] G)) q.1 q.2 := by
  have hx : ∀ k, ∀ q ∈ V, (c03c_aux_Dx^[k] F) q.1 q.2 = (c03c_aux_Dx^[k] G) q.1 q.2 := by
    intro k; induction k with
    | zero => exact hFG
    | succ k ih =>
      rintro ⟨y, ξ⟩ hq
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show deriv _ ξ = deriv _ ξ
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [c03c_aux_nhds_x hV hq] with ξ' hξ' using ih _ hξ'
  induction j with
  | zero => exact hx k
  | succ j ih =>
    rintro ⟨y, ξ⟩ hq
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show deriv _ y = deriv _ y
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [c03c_aux_nhds_y hV hq] with y' hy' using ih _ hy'

/-- Two-variable Leibniz formula. -/
theorem c03c_aux_leibniz2 {F G : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) (hG : c03c_aux_Sm G V) (j k : ℕ) {y ξ : ℝ} (h : (y, ξ) ∈ V) :
    (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] (fun y ξ => F y ξ * G y ξ))) y ξ =
      ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
        ((j.choose a : ℂ) * (k.choose b : ℂ)) *
          ((c03c_aux_Dy^[a] (c03c_aux_Dx^[b] F)) y ξ *
            (c03c_aux_Dy^[j - a] (c03c_aux_Dx^[k - b] G)) y ξ) := by
  -- Leibniz in ξ on V
  have hx : ∀ q ∈ V, (c03c_aux_Dx^[k] (fun y ξ => F y ξ * G y ξ)) q.1 q.2 =
      (fun y ξ => ∑ b ∈ Finset.range (k + 1), (k.choose b : ℂ) *
        ((c03c_aux_Dx^[b] F) y ξ * (c03c_aux_Dx^[k - b] G) y ξ)) q.1 q.2 := by
    rintro ⟨y', ξ'⟩ hq
    simp only
    rw [← c03c_aux_iterDx, iteratedDeriv_fun_mul
      ((c03c_aux_Sm_contDiffAt_x hV hF hq).of_le (c03c_aux_le_top k))
      ((c03c_aux_Sm_contDiffAt_x hV hG hq).of_le (c03c_aux_le_top k))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [c03c_aux_iterDx, c03c_aux_iterDx]; ring
  have h1 := c03c_aux_eqOn_iter (F := c03c_aux_Dx^[k] (fun y ξ => F y ξ * G y ξ))
    (G := fun y ξ => ∑ b ∈ Finset.range (k + 1), (k.choose b : ℂ) *
        ((c03c_aux_Dx^[b] F) y ξ * (c03c_aux_Dx^[k - b] G) y ξ)) hV hx j 0 (y, ξ) h
  simp only [Function.iterate_zero, id_eq] at h1
  have h2 := congrFun (c03c_aux_iterDy (fun y ξ => ∑ b ∈ Finset.range (k + 1), (k.choose b : ℂ) *
        ((c03c_aux_Dx^[b] F) y ξ * (c03c_aux_Dx^[k - b] G) y ξ)) j ξ) y
  rw [h1, ← h2]
  have hsm : ∀ b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y' => (c03c_aux_Dx^[b] F) y' ξ) y := fun b =>
    c03c_aux_Sm_contDiffAt_y hV (c03c_aux_Sm_iter hV hF 0 b) h
  have hsmG : ∀ b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y' => (c03c_aux_Dx^[b] G) y' ξ) y := fun b =>
    c03c_aux_Sm_contDiffAt_y hV (c03c_aux_Sm_iter hV hG 0 b) h
  rw [iteratedDeriv_fun_sum (fun b _ => (contDiffAt_const.mul ((hsm b).mul (hsmG (k - b)))).of_le
    (c03c_aux_le_top j))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul ((hsm b).of_le (c03c_aux_le_top j))
    ((hsmG (k - b)).of_le (c03c_aux_le_top j)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [congrFun (c03c_aux_iterDy (c03c_aux_Dx^[b] F) a ξ) y,
    congrFun (c03c_aux_iterDy (c03c_aux_Dx^[k - b] G) (j - a) ξ) y]
  ring


/-- Symbol class: `|D_y^j D_ξ^k F| ≤ K_{jk} ξ^{μ-k} (y+ξ^p)^ν y^{-j}` (`y > 0`, `ξ ≥ 1`,
`j + k ≤ N`). -/
def c03c_aux_Sym (p : ℝ) (F : ℝ → ℝ → ℂ) (μ ν : ℝ) (K : ℕ → ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ j k : ℕ, j + k ≤ N → ∀ y ξ : ℝ, 0 < y → 1 ≤ ξ →
    ‖(c03c_aux_Dy^[j] (c03c_aux_Dx^[k] F)) y ξ‖ ≤
      K j k * ξ ^ (μ - k) * (y + ξ ^ p) ^ ν * y ^ (-(j : ℝ))

/-- The region `y > 0, ξ > 0`. -/
def c03c_aux_W : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

theorem c03c_aux_W_open : IsOpen c03c_aux_W := isOpen_Ioi.prod isOpen_Ioi

theorem c03c_aux_Sym_mul {p : ℝ} (hp : 0 < p) {F G : ℝ → ℝ → ℂ} (hF : c03c_aux_Sm F c03c_aux_W)
    (hG : c03c_aux_Sm G c03c_aux_W) {μ1 ν1 μ2 ν2 : ℝ} {K1 K2 : ℕ → ℕ → ℝ} {N : ℕ}
    (h1 : c03c_aux_Sym p F μ1 ν1 K1 N) (h2 : c03c_aux_Sym p G μ2 ν2 K2 N) :
    c03c_aux_Sym p (fun y ξ => F y ξ * G y ξ) (μ1 + μ2) (ν1 + ν2)
      (fun j k => ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
        (j.choose a : ℝ) * (k.choose b : ℝ) * (K1 a b * K2 (j - a) (k - b))) N := by
  intro j k hjk y ξ hy hξ
  have hξ0 : 0 < ξ := by linarith
  have hW : (y, ξ) ∈ c03c_aux_W := ⟨hy, hξ0⟩
  rw [c03c_aux_leibniz2 c03c_aux_W_open hF hG j k hW]
  have hs : 0 < y + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; linarith
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  rw [Finset.mem_range] at ha hb
  have b1 := h1 a b (by omega) y ξ hy hξ
  have b2 := h2 (j - a) (k - b) (by omega) y ξ hy hξ
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have e1 : ξ ^ (μ1 - b) * ξ ^ (μ2 - ((k - b : ℕ) : ℝ)) = ξ ^ (μ1 + μ2 - k) := by
    rw [← Real.rpow_add hξ0]; congr 1; rw [Nat.cast_sub (by omega)]; ring
  have e2 : (y + ξ ^ p) ^ ν1 * (y + ξ ^ p) ^ ν2 = (y + ξ ^ p) ^ (ν1 + ν2) := by
    rw [← Real.rpow_add hs]
  have e3 : y ^ (-(a : ℝ)) * y ^ (-((j - a : ℕ) : ℝ)) = y ^ (-(j : ℝ)) := by
    rw [← Real.rpow_add hy]; congr 1; rw [Nat.cast_sub (by omega)]; ring
  have n1 : 0 ≤ K1 a b * ξ ^ (μ1 - b) * (y + ξ ^ p) ^ ν1 * y ^ (-(a : ℝ)) :=
    (norm_nonneg _).trans b1
  calc (j.choose a : ℝ) * (k.choose b : ℝ) *
        (‖(c03c_aux_Dy^[a] (c03c_aux_Dx^[b] F)) y ξ‖ *
          ‖(c03c_aux_Dy^[j - a] (c03c_aux_Dx^[k - b] G)) y ξ‖)
      ≤ (j.choose a : ℝ) * (k.choose b : ℝ) *
        ((K1 a b * ξ ^ (μ1 - b) * (y + ξ ^ p) ^ ν1 * y ^ (-(a : ℝ))) *
          (K2 (j - a) (k - b) * ξ ^ (μ2 - ((k - b : ℕ) : ℝ)) * (y + ξ ^ p) ^ ν2 *
            y ^ (-((j - a : ℕ) : ℝ)))) := by gcongr
    _ = (j.choose a : ℝ) * (k.choose b : ℝ) * (K1 a b * K2 (j - a) (k - b)) *
        (ξ ^ (μ1 - b) * ξ ^ (μ2 - ((k - b : ℕ) : ℝ))) *
        ((y + ξ ^ p) ^ ν1 * (y + ξ ^ p) ^ ν2) * (y ^ (-(a : ℝ)) * y ^ (-((j - a : ℕ) : ℝ))) := by
        ring
    _ = _ := by rw [e1, e2, e3]

theorem c03c_aux_Sym_Dx {p : ℝ} {F : ℝ → ℝ → ℂ} {μ ν : ℝ} {K : ℕ → ℕ → ℝ} {N : ℕ}
    (h : c03c_aux_Sym p F μ ν K (N + 1)) :
    c03c_aux_Sym p (c03c_aux_Dx F) (μ - 1) ν (fun j k => K j (k + 1)) N := by
  intro j k hjk y ξ hy hξ
  have := h j (k + 1) (by omega) y ξ hy hξ
  rw [← Function.iterate_succ_apply c03c_aux_Dx k F]
  refine this.trans (le_of_eq ?_)
  congr 3; push_cast; ring

theorem c03c_aux_Sym_congr {p : ℝ} {F G : ℝ → ℝ → ℂ} {μ ν : ℝ} {K : ℕ → ℕ → ℝ} {N : ℕ}
    (hFG : ∀ q ∈ c03c_aux_W, F q.1 q.2 = G q.1 q.2) (h : c03c_aux_Sym p F μ ν K N) :
    c03c_aux_Sym p G μ ν K N := by
  intro j k hjk y ξ hy hξ
  rw [← c03c_aux_eqOn_iter c03c_aux_W_open hFG j k (y, ξ) ⟨hy, by simp; linarith⟩]
  exact h j k hjk y ξ hy hξ


/-! ### Cutoffs `g(ξ y^{-1/p})` -/

/-- `H_0 = G`, `H_{j+1}(r) = (-k/p - j) H_j(r) - (1/p) r H_j'(r)`. -/
def c03c_aux_Hseq (p : ℝ) (k : ℕ) (G : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => G
  | j + 1 => fun r => (-(k : ℝ) / p - j) * c03c_aux_Hseq p k G j r -
      (1 / p) * r * deriv (c03c_aux_Hseq p k G j) r

theorem c03c_aux_Hseq_smooth (p : ℝ) (k : ℕ) {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (c03c_aux_Hseq p k G j) := by
  induction j with
  | zero => exact hG
  | succ j ih =>
    have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv (c03c_aux_Hseq p k G j)) :=
      (contDiff_infty_iff_deriv.mp ih).2
    show ContDiff ℝ (⊤ : ℕ∞) (fun r => (-(k : ℝ) / p - j) * c03c_aux_Hseq p k G j r -
      (1 / p) * r * deriv (c03c_aux_Hseq p k G j) r)
    exact (contDiff_const.mul ih).sub ((contDiff_const.mul contDiff_id).mul hd)

theorem c03c_aux_Hseq_vanish (p : ℝ) (k : ℕ) {G : ℝ → ℝ} {O : Set ℝ} (hO : IsOpen O)
    (hG : ∀ r ∈ O, G r = 0) (j : ℕ) : ∀ r ∈ O, c03c_aux_Hseq p k G j r = 0 := by
  induction j with
  | zero => exact hG
  | succ j ih =>
    intro r hr
    have hd : deriv (c03c_aux_Hseq p k G j) r = 0 := by
      have : c03c_aux_Hseq p k G j =ᶠ[𝓝 r] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hr] with x hx using ih x hx
      rw [this.deriv_eq]; simp
    show (-(k : ℝ) / p - j) * c03c_aux_Hseq p k G j r -
      (1 / p) * r * deriv (c03c_aux_Hseq p k G j) r = 0
    rw [ih r hr, hd]; ring

/-- For `k = 0`, `H_1` only involves `G'`. -/
theorem c03c_aux_Hseq_vanish0 (p : ℝ) {G : ℝ → ℝ} {O : Set ℝ} (hO : IsOpen O)
    (hG : ∀ r ∈ O, deriv G r = 0) (j : ℕ) (hj : 1 ≤ j) :
    ∀ r ∈ O, c03c_aux_Hseq p 0 G j r = 0 := by
  induction j with
  | zero => omega
  | succ j ih =>
    intro r hr
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · show (-((0 : ℕ) : ℝ) / p - ((0 : ℕ) : ℝ)) * G r - (1 / p) * r * deriv G r = 0
      rw [hG r hr]; simp
    · have ih' := ih hj'
      have hd : deriv (c03c_aux_Hseq p 0 G j) r = 0 := by
        have : c03c_aux_Hseq p 0 G j =ᶠ[𝓝 r] fun _ => 0 := by
          filter_upwards [hO.mem_nhds hr] with x hx using ih' x hx
        rw [this.deriv_eq]; simp
      show (-((0 : ℕ) : ℝ) / p - j) * c03c_aux_Hseq p 0 G j r -
        (1 / p) * r * deriv (c03c_aux_Hseq p 0 G j) r = 0
      rw [ih' r hr, hd]; ring

/-- One `y`-derivative of `y^e h(ξ y^{-1/p})`. -/
theorem c03c_aux_cut_hasDerivAt (p : ℝ) (hp : 0 < p) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (e ξ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => y ^ e * h (ξ * y ^ (-1 / p)))
      (y ^ (e - 1) * (e * h (ξ * y ^ (-1 / p)) -
        (1 / p) * (ξ * y ^ (-1 / p)) * deriv h (ξ * y ^ (-1 / p)))) y := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ e) (e * y ^ (e - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have h2 : HasDerivAt (fun y : ℝ => ξ * y ^ (-1 / p)) (ξ * ((-1 / p) * y ^ (-1 / p - 1))) y :=
    (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul ξ
  have h3 : HasDerivAt (fun y : ℝ => h (ξ * y ^ (-1 / p)))
      (deriv h (ξ * y ^ (-1 / p)) * (ξ * ((-1 / p) * y ^ (-1 / p - 1)))) y :=
    ((hh.differentiable (by simp)) _).hasDerivAt.comp y h2
  convert h1.mul h3 using 1
  have e1 : y ^ e * y ^ (-1 / p - 1) = y ^ (e - 1) * y ^ (-1 / p) := by
    rw [← Real.rpow_add hy, ← Real.rpow_add hy]; ring_nf
  have : y ^ e * (deriv h (ξ * y ^ (-1 / p)) * (ξ * (-1 / p * y ^ (-1 / p - 1)))) =
      -(1 / p) * ξ * deriv h (ξ * y ^ (-1 / p)) * (y ^ e * y ^ (-1 / p - 1)) := by ring
  rw [this, e1]; ring


/-- The cutoff `Γ_g(y, ξ) = g(ξ y^{-1/p})`. -/
def c03c_aux_Gam (p : ℝ) (g : ℝ → ℝ) : ℝ → ℝ → ℂ := fun y ξ => ((g (ξ * y ^ (-1 / p)) : ℝ) : ℂ)

theorem c03c_aux_Gam_Dx (p : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k : ℕ) (y ξ : ℝ) :
    (c03c_aux_Dx^[k] (c03c_aux_Gam p g)) y ξ =
      (((y ^ (-1 / p)) ^ k * iteratedDeriv k g (ξ * y ^ (-1 / p)) : ℝ) : ℂ) := by
  rw [← c03c_aux_iterDx]
  have h1 : c03c_aux_Gam p g y = fun ξ => ((((fun x => g (y ^ (-1 / p) * x)) ξ) : ℝ) : ℂ) := by
    funext ξ; simp [c03c_aux_Gam, mul_comm]
  have hcd : ContDiffAt ℝ k (fun x => g (y ^ (-1 / p) * x)) ξ :=
    (hg.comp (contDiff_const.mul contDiff_id)).contDiffAt.of_le (c03c_aux_le_top k)
  rw [h1, c03c_aux_iteratedDeriv_ofReal (fun x => g (y ^ (-1 / p) * x)) ξ k hcd,
    iteratedDeriv_comp_const_mul (hg.of_le (c03c_aux_le_top k)), mul_comm ξ]

theorem c03c_aux_Gam_mixed (p : ℝ) (hp : 0 < p) {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k : ℕ)
    (j : ℕ) : ∀ y ξ : ℝ, 0 < y → (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] (c03c_aux_Gam p g))) y ξ =
      ((y ^ (-(k : ℝ) / p - j) *
        c03c_aux_Hseq p k (iteratedDeriv k g) j (ξ * y ^ (-1 / p)) : ℝ) : ℂ) := by
  have hgk : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k g) := by
    have := hg.iterate_deriv k; rwa [← iteratedDeriv_eq_iterate] at this
  induction j with
  | zero =>
    intro y ξ hy
    simp only [Function.iterate_zero, id_eq]
    rw [c03c_aux_Gam_Dx p hg k y ξ]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; congr 1; push_cast; ring
  | succ j ih =>
    intro y ξ hy
    rw [Function.iterate_succ_apply']
    show deriv (fun y' => (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] (c03c_aux_Gam p g))) y' ξ) y = _
    have hev : (fun y' => (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] (c03c_aux_Gam p g))) y' ξ) =ᶠ[𝓝 y]
        fun y' => ((y' ^ (-(k : ℝ) / p - j) *
          c03c_aux_Hseq p k (iteratedDeriv k g) j (ξ * y' ^ (-1 / p)) : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hy] with y' hy' using ih y' ξ hy'
    rw [hev.deriv_eq]
    set H := c03c_aux_Hseq p k (iteratedDeriv k g) j with hH
    set e : ℝ := -(k : ℝ) / p - j with he
    have hd : HasDerivAt (fun y' : ℝ => ((y' ^ e * H (ξ * y' ^ (-1 / p)) : ℝ) : ℂ))
        (((y ^ (e - 1) * (e * H (ξ * y ^ (-1 / p)) -
          (1 / p) * (ξ * y ^ (-1 / p)) * deriv H (ξ * y ^ (-1 / p))) : ℝ) : ℂ)) y :=
      (c03c_aux_cut_hasDerivAt p hp (c03c_aux_Hseq_smooth p k hgk j) e ξ hy).ofReal_comp
    rw [hd.deriv]
    have hee : e - 1 = -(k : ℝ) / p - ((j + 1 : ℕ) : ℝ) := by rw [he]; push_cast; ring
    rw [hee]
    rfl


theorem c03c_aux_Gam_Sym (p : ℝ) (hp : 0 < p) {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg1 : ∀ r, |g r| ≤ 1) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hg' : ∀ r, (r < α ∨ β < r) → deriv g r = 0) :
    ∃ K : ℕ → ℕ → ℝ, (∀ j k, 0 ≤ K j k) ∧ ∀ N, c03c_aux_Sym p (c03c_aux_Gam p g) 0 0 K N := by
  set O : Set ℝ := {r | r < α ∨ β < r} with hO
  have hOo : IsOpen O := (isOpen_lt continuous_id continuous_const).union
    (isOpen_lt continuous_const continuous_id)
  have hgk : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k g) := fun k => by
    have := hg.iterate_deriv k; rwa [← iteratedDeriv_eq_iterate] at this
  have hvk : ∀ k, 1 ≤ k → ∀ r ∈ O, iteratedDeriv k g r = 0 := by
    intro k hk r hr
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [iteratedDeriv_succ']
    have : deriv g =ᶠ[𝓝 r] fun _ => 0 := by
      filter_upwards [hOo.mem_nhds hr] with x hx using hg' x hx
    rw [this.iteratedDeriv_eq, iteratedDeriv_const]; simp
  have hbd : ∀ k j : ℕ, ∃ M, 0 ≤ M ∧ ∀ r ∈ Icc α β,
      |c03c_aux_Hseq p k (iteratedDeriv k g) j r| ≤ M := by
    intro k j
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (c03c_aux_Hseq_smooth p k (hgk k) j).continuous.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun r hr => (hM r hr).trans (le_max_left _ _)⟩
  choose M hM0 hM using hbd
  refine ⟨fun j k => if j = 0 ∧ k = 0 then 1 else β ^ k * M k j, fun j k => by
    simp only
    split_ifs
    · norm_num
    · exact mul_nonneg (pow_nonneg (by linarith) _) (hM0 k j), fun N => ?_⟩
  intro j k _ y ξ hy hξ
  simp only
  have hξ0 : 0 < ξ := by linarith
  rw [c03c_aux_Gam_mixed p hp hg k j y ξ hy, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_zero, mul_one, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hy _)]
  set r := ξ * y ^ (-1 / p) with hr
  have hs0 : 0 < y ^ (-1 / p) := Real.rpow_pos_of_pos hy _
  have hy1 : y ^ (-(k : ℝ) / p - j) = (y ^ (-1 / p)) ^ k * y ^ (-(j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_add hy]; congr 1; ring
  have hRHS : 0 ≤ ξ ^ ((0 : ℝ) - k) * y ^ (-(j : ℝ)) := by positivity
  by_cases h00 : j = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h00
    simp only [and_self, ite_true, CharP.cast_eq_zero, neg_zero, zero_div, sub_zero,
      Real.rpow_zero, one_mul, mul_one]
    exact hg1 _
  · rw [ite_cond_eq_false _ _ (eq_false h00)]
    by_cases hrO : r ∈ O
    · have : c03c_aux_Hseq p k (iteratedDeriv k g) j r = 0 := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          have hj : 1 ≤ j := by
            rcases Nat.eq_zero_or_pos j with hj | hj
            · exact absurd ⟨hj, rfl⟩ h00
            · exact hj
          exact c03c_aux_Hseq_vanish0 p hOo (fun r hr => hg' r hr) j hj r hrO
        · exact c03c_aux_Hseq_vanish p k hOo (hvk k hk) j r hrO
      rw [this, abs_zero, mul_zero]
      have := hM0 k j
      have := pow_nonneg (by linarith : (0 : ℝ) ≤ β) k
      positivity
    · have hrI : r ∈ Icc α β := by
        simp only [hO, mem_setOf_eq, not_or, not_lt] at hrO
        exact ⟨hrO.1, hrO.2⟩
      have hsk : (y ^ (-1 / p)) ^ k ≤ β ^ k * ξ ^ ((0 : ℝ) - k) := by
        have : y ^ (-1 / p) ≤ β / ξ := by
          rw [le_div_iff₀ hξ0, mul_comm]; exact hrI.2
        calc (y ^ (-1 / p)) ^ k ≤ (β / ξ) ^ k := pow_le_pow_left₀ hs0.le this k
          _ = β ^ k * ξ ^ ((0 : ℝ) - k) := by
            rw [div_pow, zero_sub, Real.rpow_neg hξ0.le, Real.rpow_natCast, div_eq_mul_inv]
      rw [hy1]
      have hH := hM k j r hrI
      calc (y ^ (-1 / p)) ^ k * y ^ (-(j : ℝ)) * |c03c_aux_Hseq p k (iteratedDeriv k g) j r|
          ≤ (β ^ k * ξ ^ ((0 : ℝ) - k)) * y ^ (-(j : ℝ)) * M k j := by
            have : 0 ≤ β ^ k * ξ ^ ((0 : ℝ) - k) * y ^ (-(j : ℝ)) := by
              have := pow_nonneg (by linarith : (0 : ℝ) ≤ β) k
              positivity
            gcongr
        _ = β ^ k * M k j * ξ ^ ((0 : ℝ) - k) * y ^ (-(j : ℝ)) := by ring


theorem c03c_aux_ofReal_mixed {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry f) V) (j k : ℕ) {y ξ : ℝ} (h : (y, ξ) ∈ V) :
    (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] (fun y ξ => ((f y ξ : ℝ) : ℂ)))) y ξ =
      ((iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' => f y' ξ') ξ) y : ℝ) : ℂ) := by
  set Fc : ℝ → ℝ → ℂ := fun y ξ => ((f y ξ : ℝ) : ℂ) with hFc
  have hsm : c03c_aux_Sm Fc V := Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hfx : ∀ q ∈ V, ContDiffAt ℝ (⊤ : ℕ∞) (f q.1) q.2 := by
    rintro ⟨y', ξ'⟩ hq
    exact (hf.contDiffAt (hV.mem_nhds hq)).comp ξ' (contDiffAt_const.prodMk contDiffAt_id)
  have step1 : ∀ q ∈ V, (c03c_aux_Dx^[k] Fc) q.1 q.2 =
      (fun y ξ => ((iteratedDeriv k (f y) ξ : ℝ) : ℂ)) q.1 q.2 := by
    rintro ⟨y', ξ'⟩ hq
    simp only
    rw [← c03c_aux_iterDx]
    exact c03c_aux_iteratedDeriv_ofReal (f y') ξ' k ((hfx _ hq).of_le (c03c_aux_le_top k))
  have h2 := c03c_aux_eqOn_iter (F := c03c_aux_Dx^[k] Fc)
    (G := fun y ξ => ((iteratedDeriv k (f y) ξ : ℝ) : ℂ)) hV step1 j 0 (y, ξ) h
  simp only [Function.iterate_zero, id_eq] at h2
  rw [h2]
  have h3 := congrFun (c03c_aux_iterDy (fun y ξ => ((iteratedDeriv k (f y) ξ : ℝ) : ℂ)) j ξ) y
  rw [← h3]
  -- smoothness of the partial derivative in y
  have hg : ContDiffAt ℝ j (fun y' => iteratedDeriv k (fun ξ' => f y' ξ') ξ) y := by
    have hc := c03c_aux_Sm_contDiffAt_y hV (c03c_aux_Sm_iter hV hsm 0 k) h
    have hre := (Complex.reCLM.contDiff.contDiffAt (x := (c03c_aux_Dx^[k] Fc) y ξ)).comp y hc
    refine (hre.of_le (c03c_aux_le_top j)).congr_of_eventuallyEq ?_
    filter_upwards [c03c_aux_nhds_y hV h] with y' hy'
    have := step1 (y', ξ) hy'
    simp only at this
    simp only [Function.comp_apply, Function.iterate_zero, id_eq, this, Complex.reCLM_apply,
      Complex.ofReal_re]
  exact c03c_aux_iteratedDeriv_ofReal _ y j hg

theorem c03c_aux_iter_const_mul (c : ℂ) (F : ℝ → ℝ → ℂ) (j k : ℕ) (y ξ : ℝ) :
    (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] (fun y ξ => c * F y ξ))) y ξ =
      c * (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] F)) y ξ := by
  have hx : ∀ k, c03c_aux_Dx^[k] (fun y ξ => c * F y ξ) = fun y ξ => c * (c03c_aux_Dx^[k] F) y ξ := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext y ξ; exact deriv_const_mul_field (v := (c03c_aux_Dx^[k] F) y) c
  have hy : ∀ j (G : ℝ → ℝ → ℂ), c03c_aux_Dy^[j] (fun y ξ => c * G y ξ) =
      fun y ξ => c * (c03c_aux_Dy^[j] G) y ξ := by
    intro j G; induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext y ξ
      exact deriv_const_mul_field (v := fun y' => (c03c_aux_Dy^[j] G) y' ξ) c
  rw [hx, hy]


/-- Pointwise Leibniz bound on an open set `V`. -/
theorem c03c_aux_mul_bound_at {p : ℝ} {F G : ℝ → ℝ → ℂ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : c03c_aux_Sm F V) (hG : c03c_aux_Sm G V) {y ξ : ℝ} (hq : (y, ξ) ∈ V) (hy : 0 < y)
    (hξ0 : 0 < ξ) {μ1 ν1 μ2 ν2 : ℝ} {K1 K2 : ℕ → ℕ → ℝ} (j k : ℕ)
    (h1 : ∀ a ≤ j, ∀ b ≤ k, ‖(c03c_aux_Dy^[a] (c03c_aux_Dx^[b] F)) y ξ‖ ≤
      K1 a b * ξ ^ (μ1 - b) * (y + ξ ^ p) ^ ν1 * y ^ (-(a : ℝ)))
    (h2 : ∀ a ≤ j, ∀ b ≤ k, ‖(c03c_aux_Dy^[a] (c03c_aux_Dx^[b] G)) y ξ‖ ≤
      K2 a b * ξ ^ (μ2 - b) * (y + ξ ^ p) ^ ν2 * y ^ (-(a : ℝ))) :
    ‖(c03c_aux_Dy^[j] (c03c_aux_Dx^[k] (fun y ξ => F y ξ * G y ξ))) y ξ‖ ≤
      (∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
        (j.choose a : ℝ) * (k.choose b : ℝ) * (K1 a b * K2 (j - a) (k - b))) *
        ξ ^ (μ1 + μ2 - k) * (y + ξ ^ p) ^ (ν1 + ν2) * y ^ (-(j : ℝ)) := by
  rw [c03c_aux_leibniz2 hV hF hG j k hq]
  have hs : 0 < y + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; linarith
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  rw [Finset.mem_range] at ha hb
  have b1 := h1 a (by omega) b (by omega)
  have b2 := h2 (j - a) (by omega) (k - b) (by omega)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have e1 : ξ ^ (μ1 - b) * ξ ^ (μ2 - ((k - b : ℕ) : ℝ)) = ξ ^ (μ1 + μ2 - k) := by
    rw [← Real.rpow_add hξ0]; congr 1; rw [Nat.cast_sub (by omega)]; ring
  have e2 : (y + ξ ^ p) ^ ν1 * (y + ξ ^ p) ^ ν2 = (y + ξ ^ p) ^ (ν1 + ν2) := by
    rw [← Real.rpow_add hs]
  have e3 : y ^ (-(a : ℝ)) * y ^ (-((j - a : ℕ) : ℝ)) = y ^ (-(j : ℝ)) := by
    rw [← Real.rpow_add hy]; congr 1; rw [Nat.cast_sub (by omega)]; ring
  have n1 : 0 ≤ K1 a b * ξ ^ (μ1 - b) * (y + ξ ^ p) ^ ν1 * y ^ (-(a : ℝ)) :=
    (norm_nonneg _).trans b1
  calc (j.choose a : ℝ) * (k.choose b : ℝ) *
        (‖(c03c_aux_Dy^[a] (c03c_aux_Dx^[b] F)) y ξ‖ *
          ‖(c03c_aux_Dy^[j - a] (c03c_aux_Dx^[k - b] G)) y ξ‖)
      ≤ (j.choose a : ℝ) * (k.choose b : ℝ) *
        ((K1 a b * ξ ^ (μ1 - b) * (y + ξ ^ p) ^ ν1 * y ^ (-(a : ℝ))) *
          (K2 (j - a) (k - b) * ξ ^ (μ2 - ((k - b : ℕ) : ℝ)) * (y + ξ ^ p) ^ ν2 *
            y ^ (-((j - a : ℕ) : ℝ)))) := by gcongr
    _ = (j.choose a : ℝ) * (k.choose b : ℝ) * (K1 a b * K2 (j - a) (k - b)) *
        (ξ ^ (μ1 - b) * ξ ^ (μ2 - ((k - b : ℕ) : ℝ))) *
        ((y + ξ ^ p) ^ ν1 * (y + ξ ^ p) ^ ν2) * (y ^ (-(a : ℝ)) * y ^ (-((j - a : ℕ) : ℝ))) := by
        ring
    _ = _ := by rw [e1, e2, e3]

theorem c03c_aux_iter_zero_of_local {F : ℝ → ℝ → ℂ} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hz : ∀ q ∈ O, F q.1 q.2 = 0) (j k : ℕ) {y ξ : ℝ} (h : (y, ξ) ∈ O) :
    (c03c_aux_Dy^[j] (c03c_aux_Dx^[k] F)) y ξ = 0 := by
  have := c03c_aux_eqOn_iter (G := fun _ _ => (0 : ℂ)) hO hz j k (y, ξ) h
  rw [this]
  have hx : ∀ k, c03c_aux_Dx^[k] (fun _ _ => (0 : ℂ)) = fun _ _ => 0 := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih]; funext y ξ; simp [c03c_aux_Dx]
  have hy : ∀ j, c03c_aux_Dy^[j] (fun _ _ => (0 : ℂ)) = fun _ _ => 0 := by
    intro j; induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; funext y ξ; simp [c03c_aux_Dy]
  rw [hx, hy]


/-! ### The far reciprocal `R̃ = (1 - θ(ξ/λ₀)) / (i(y - ξ^p))` -/

/-- A bump `θ = 1` on `[0.8, 1.3]`, `θ = 0` outside `(0.76, 1.45)`. -/
def c03c_aux_theta (r : ℝ) : ℝ :=
  Real.smoothTransition ((r - 0.76) / 0.04) * Real.smoothTransition ((1.45 - r) / 0.15)

theorem c03c_aux_theta_smooth : ContDiff ℝ (⊤ : ℕ∞) c03c_aux_theta := by
  unfold c03c_aux_theta
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

theorem c03c_aux_theta_one {r : ℝ} (h1 : 0.8 ≤ r) (h2 : r ≤ 1.3) : c03c_aux_theta r = 1 := by
  unfold c03c_aux_theta
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith),
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith), mul_one]

theorem c03c_aux_theta_zero {r : ℝ} (h : r ≤ 0.76 ∨ 1.45 ≤ r) : c03c_aux_theta r = 0 := by
  unfold c03c_aux_theta
  rcases h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith),
      zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (x := (1.45 - r) / 0.15)
      (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith), mul_zero]

theorem c03c_aux_theta_bounds (r : ℝ) : 0 ≤ c03c_aux_theta r ∧ c03c_aux_theta r ≤ 1 := by
  unfold c03c_aux_theta
  have a1 := Real.smoothTransition.nonneg ((r - 0.76) / 0.04)
  have a2 := Real.smoothTransition.le_one ((r - 0.76) / 0.04)
  have b1 := Real.smoothTransition.nonneg ((1.45 - r) / 0.15)
  have b2 := Real.smoothTransition.le_one ((1.45 - r) / 0.15)
  exact ⟨mul_nonneg a1 b1, by nlinarith⟩

theorem c03c_aux_one_sub_theta_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (fun r => 1 - c03c_aux_theta r) :=
  contDiff_const.sub c03c_aux_theta_smooth

/-- `-i / (y - ξ^p)`. -/
def c03c_aux_R0 (p : ℝ) : ℝ → ℝ → ℂ := fun y ξ => -Complex.I * (((1 / (y - ξ ^ p)) : ℝ) : ℂ)

/-- `R̃ = (1 - θ(ξ y^{-1/p})) · (-i)/(y - ξ^p)`. -/
def c03c_aux_Rt (p : ℝ) : ℝ → ℝ → ℂ := fun y ξ =>
  c03c_aux_Gam p (fun r => 1 - c03c_aux_theta r) y ξ * c03c_aux_R0 p y ξ


theorem c03c_aux_r_eq (p : ℝ) {y : ℝ} (hy : 0 < y) (ξ : ℝ) : ξ * y ^ (-1 / p) = ξ / lambda0 p y := by
  rw [lambda0, div_eq_mul_inv ξ, ← Real.rpow_neg hy.le]; congr 2; ring

theorem c03c_aux_r_one (p : ℝ) (hp : 0 < p) {y ξ : ℝ} (hy : 0 < y) (hξ : 0 < ξ)
    (h : y - ξ ^ p = 0) : ξ * y ^ (-1 / p) = 1 := by
  have hy' : y = ξ ^ p := by linarith
  rw [hy', ← Real.rpow_mul hξ.le, show p * (-1 / p) = -1 by field_simp, Real.rpow_neg_one,
    mul_inv_cancel₀ hξ.ne']

theorem c03c_aux_rmap_cont (p : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => q.2 * q.1 ^ (-1 / p)) c03c_aux_W := by
  intro q hq
  apply ContinuousAt.continuousWithinAt
  exact continuous_snd.continuousAt.mul
    (continuous_fst.continuousAt.rpow_const (Or.inl (ne_of_gt hq.1)))

theorem c03c_aux_Gam_Sm (p : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    c03c_aux_Sm (c03c_aux_Gam p g) c03c_aux_W := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.2 * q.1 ^ (-1 / p)) q :=
    contDiffAt_snd.mul ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt hq.1)).comp q contDiffAt_fst)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp q (hg.contDiffAt.comp q h1)

/-- The set where `R₀` is smooth. -/
def c03c_aux_V1 (p : ℝ) : Set (ℝ × ℝ) := {q | q ∈ c03c_aux_W ∧ q.1 - q.2 ^ p ≠ 0}

theorem c03c_aux_V1_open (p : ℝ) : IsOpen (c03c_aux_V1 p) := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => q.1 - q.2 ^ p) c03c_aux_W := by
    intro q hq
    exact (continuous_fst.continuousAt.sub (continuous_snd.continuousAt.rpow_const
      (Or.inl (ne_of_gt hq.2)))).continuousWithinAt
  have := hc.isOpen_inter_preimage c03c_aux_W_open (isOpen_compl_singleton (x := (0 : ℝ)))
  convert this using 1
  ext q; simp [c03c_aux_V1]

theorem c03c_aux_f_smooth (p : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry fun y ξ : ℝ => 1 / (y - ξ ^ p)) (c03c_aux_V1 p) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1 - q.2 ^ p) q :=
    contDiffAt_fst.sub ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt hq.1.2)).comp q contDiffAt_snd)
  have := (contDiffAt_const (c := (1 : ℝ))).div h1 hq.2
  exact this

theorem c03c_aux_R0_Sm (p : ℝ) : c03c_aux_Sm (c03c_aux_R0 p) (c03c_aux_V1 p) := by
  have := Complex.ofRealCLM.contDiff.comp_contDiffOn (c03c_aux_f_smooth p)
  exact contDiffOn_const.mul this


/-- The set where `θ(ξ y^{-1/p}) = 1` locally. -/
def c03c_aux_O (p : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∈ c03c_aux_W ∧ 0.8 < q.2 * q.1 ^ (-1 / p) ∧ q.2 * q.1 ^ (-1 / p) < 1.3}

theorem c03c_aux_O_open (p : ℝ) : IsOpen (c03c_aux_O p) := by
  have := (c03c_aux_rmap_cont p).isOpen_inter_preimage c03c_aux_W_open
    (isOpen_Ioo (a := (0.8 : ℝ)) (b := 1.3))
  convert this using 1
  ext q; simp [c03c_aux_O]; tauto

theorem c03c_aux_Rt_zero (p : ℝ) : ∀ q ∈ c03c_aux_O p, c03c_aux_Rt p q.1 q.2 = 0 := by
  rintro ⟨y, ξ⟩ ⟨_, h1, h2⟩
  simp only [c03c_aux_Rt, c03c_aux_Gam]
  rw [c03c_aux_theta_one h1.le h2.le]; simp

theorem c03c_aux_notO_V1 (p : ℝ) (hp : 0 < p) {y ξ : ℝ} (hy : 0 < y) (hξ : 0 < ξ)
    (h : (y, ξ) ∉ c03c_aux_O p) : (y, ξ) ∈ c03c_aux_V1 p := by
  refine ⟨⟨hy, hξ⟩, fun h0 => h ⟨⟨hy, hξ⟩, ?_⟩⟩
  have := c03c_aux_r_one p hp hy hξ h0
  simp only at this ⊢
  rw [this]; norm_num

theorem c03c_aux_Rt_Sm (p : ℝ) (hp : 0 < p) : c03c_aux_Sm (c03c_aux_Rt p) c03c_aux_W := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hO : q ∈ c03c_aux_O p
  · refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [(c03c_aux_O_open p).mem_nhds hO] with q' hq'
    exact c03c_aux_Rt_zero p q' hq'
  · obtain ⟨y, ξ⟩ := q
    have hV := c03c_aux_notO_V1 p hp hq.1 hq.2 hO
    have h1 := ((c03c_aux_Gam_Sm p c03c_aux_one_sub_theta_smooth).mono
      (fun q (hq : q ∈ c03c_aux_V1 p) => hq.1)).mul (c03c_aux_R0_Sm p)
    exact h1.contDiffAt ((c03c_aux_V1_open p).mem_nhds hV)

theorem c03c_aux_Rt_Sym (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ K : ℕ → ℕ → ℝ, (∀ j k, 0 ≤ K j k) ∧ ∀ N, c03c_aux_Sym p (c03c_aux_Rt p) 0 (-1) K N := by
  have hg' : ∀ r, (r < 0.76 ∨ 1.45 < r) → deriv (fun r => 1 - c03c_aux_theta r) r = 0 := by
    intro r hr
    have : (fun r => 1 - c03c_aux_theta r) =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
      rcases hr with hr | hr
      · filter_upwards [Iio_mem_nhds hr] with x hx
        rw [c03c_aux_theta_zero (Or.inl (le_of_lt hx))]; ring
      · filter_upwards [Ioi_mem_nhds hr] with x hx
        rw [c03c_aux_theta_zero (Or.inr (le_of_lt hx))]; ring
    rw [this.deriv_eq]; simp
  obtain ⟨KG, hKG0, hKG⟩ := c03c_aux_Gam_Sym p hp (g := fun r => 1 - c03c_aux_theta r)
    c03c_aux_one_sub_theta_smooth
    (fun r => by have := c03c_aux_theta_bounds r; rw [abs_le]; constructor <;> linarith)
    (by norm_num : (0 : ℝ) < 0.76) (by norm_num) hg'
  obtain ⟨-, -, -, hwide⟩ := c03_sp_far_phase_bounds p hp hp1
  choose CR hCR hCRb using hwide
  refine ⟨fun j k => ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
    (j.choose a : ℝ) * (k.choose b : ℝ) * (KG a b * CR (k - b) (j - a)), fun j k =>
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
        have := hKG0 a b; have := hCR (k - b) (j - a); positivity, fun N => ?_⟩
  intro j k hjk y ξ hy hξ
  have hξ0 : 0 < ξ := by linarith
  have hRHS : 0 ≤ ξ ^ ((0 : ℝ) - k) * (y + ξ ^ p) ^ (-1 : ℝ) * y ^ (-(j : ℝ)) := by
    have : 0 < y + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; linarith
    positivity
  by_cases hO : (y, ξ) ∈ c03c_aux_O p
  · rw [c03c_aux_iter_zero_of_local (c03c_aux_O_open p) (c03c_aux_Rt_zero p) j k hO, norm_zero]
    have : 0 ≤ ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
        (j.choose a : ℝ) * (k.choose b : ℝ) * (KG a b * CR (k - b) (j - a)) :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
        have := hKG0 a b; have := hCR (k - b) (j - a); positivity
    have := mul_nonneg this hRHS
    simpa [mul_assoc] using this
  · have hV := c03c_aux_notO_V1 p hp hy hξ0 hO
    -- the wide condition
    have hwc : ξ < 7 * lambda0 p y / 8 ∨ 5 * lambda0 p y / 4 < ξ := by
      have hl : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
      have hr := c03c_aux_r_eq p hy ξ
      simp only [c03c_aux_O, mem_ofPred_eq, not_and, not_lt] at hO
      have hO' := hO ⟨hy, hξ0⟩
      rw [hr] at hO'
      by_cases h8 : ξ / lambda0 p y ≤ 0.8
      · left; rw [div_le_iff₀ hl] at h8; linarith
      · right
        have := hO' (not_le.mp h8)
        rw [le_div_iff₀ hl] at this; linarith
    have hm := c03c_aux_mul_bound_at (p := p) (c03c_aux_V1_open p)
      ((c03c_aux_Gam_Sm p c03c_aux_one_sub_theta_smooth).mono
        (fun q (hq : q ∈ c03c_aux_V1 p) => hq.1))
      (c03c_aux_R0_Sm p) hV hy hξ0 (μ1 := 0) (ν1 := 0) (μ2 := 0) (ν2 := -1)
      (K1 := KG) (K2 := fun a b => CR b a) j k
      (fun a ha b hb => hKG (j + k) a b (by omega) y ξ hy hξ)
      (fun a ha b hb => by
        show ‖(c03c_aux_Dy^[a] (c03c_aux_Dx^[b]
          (fun y ξ => -Complex.I * (((1 / (y - ξ ^ p)) : ℝ) : ℂ)))) y ξ‖ ≤ _
        rw [c03c_aux_iter_const_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
          c03c_aux_ofReal_mixed (c03c_aux_V1_open p) (c03c_aux_f_smooth p) a b hV,
          Complex.norm_real, Real.norm_eq_abs]
        have := hCRb b a y ξ hy hξ0 hwc
        refine this.trans ?_
        have hs : 0 < y + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; linarith
        have e1 : (y + ξ ^ p) ^ (-1 - (a : ℝ)) = (y + ξ ^ p) ^ (-1 : ℝ) * (y + ξ ^ p) ^ (-(a : ℝ)) := by
          rw [← Real.rpow_add hs]; ring_nf
        have e2 : (y + ξ ^ p) ^ (-(a : ℝ)) ≤ y ^ (-(a : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hy (by have := Real.rpow_pos_of_pos hξ0 p; linarith)
            (by simp)
        rw [e1, zero_sub]
        have := hCR b a
        have : 0 ≤ ξ ^ (-(b : ℝ)) * (y + ξ ^ p) ^ (-1 : ℝ) := by positivity
        calc CR b a * ξ ^ (-(b : ℝ)) * ((y + ξ ^ p) ^ (-1 : ℝ) * (y + ξ ^ p) ^ (-(a : ℝ)))
            = (CR b a * ξ ^ (-(b : ℝ)) * (y + ξ ^ p) ^ (-1 : ℝ)) * (y + ξ ^ p) ^ (-(a : ℝ)) := by
              ring
          _ ≤ (CR b a * ξ ^ (-(b : ℝ)) * (y + ξ ^ p) ^ (-1 : ℝ)) * y ^ (-(a : ℝ)) := by
              gcongr
          _ = _ := by ring)
    refine hm.trans (le_of_eq ?_)
    simp only [add_zero, zero_add]


/-! ### The far amplitudes -/

theorem c03c_aux_deriv_zero_side {f : ℝ → ℂ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (h : (∃ ε > 0, ∀ t ∈ Icc x (x + ε), f t = 0) ∨ (∃ ε > 0, ∀ t ∈ Icc (x - ε) x, f t = 0)) :
    deriv f x = 0 := by
  rcases h with ⟨ε, hε, hz⟩ | ⟨ε, hε, hz⟩
  · have hu : UniqueDiffWithinAt ℝ (Icc x (x + ε)) x :=
      uniqueDiffOn_Icc (by linarith) x ⟨le_rfl, by linarith⟩
    have h1 := hf.hasDerivAt.hasDerivWithinAt (s := Icc x (x + ε))
    have h2 : HasDerivWithinAt f 0 (Icc x (x + ε)) x :=
      (hasDerivWithinAt_const x _ (0 : ℂ)).congr (fun t ht => hz t ht) (hz x ⟨le_rfl, by linarith⟩)
    exact hu.eq_deriv _ h1 h2
  · have hu : UniqueDiffWithinAt ℝ (Icc (x - ε) x) x :=
      uniqueDiffOn_Icc (by linarith) x ⟨by linarith, le_rfl⟩
    have h1 := hf.hasDerivAt.hasDerivWithinAt (s := Icc (x - ε) x)
    have h2 : HasDerivWithinAt f 0 (Icc (x - ε) x) x :=
      (hasDerivWithinAt_const x _ (0 : ℂ)).congr (fun t ht => hz t ht) (hz x ⟨by linarith, le_rfl⟩)
    exact hu.eq_deriv _ h1 h2

theorem c03c_aux_A_Sm {a : ℝ → ℂ} {m : ℝ} (ha : a ∈ c03_sp_symbol m) :
    c03c_aux_Sm (fun _ ξ => a ξ) c03c_aux_W := by
  have : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => a q.2) c03c_aux_W :=
    ha.1.comp contDiffOn_snd (fun q hq => hq.2)
  exact this

theorem c03c_aux_A_Sym {a : ℝ → ℂ} {m p : ℝ} (Ck : ℕ → ℝ) (N : ℕ)
    (hb : ∀ i ≤ N, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) :
    c03c_aux_Sym p (fun _ ξ => a ξ) m 0 (fun j k => if j = 0 then Ck k else 0) N := by
  have hx : ∀ k, c03c_aux_Dx^[k] (fun _ ξ => a ξ) = fun _ ξ => iteratedDeriv k a ξ := by
    intro k; funext y ξ; rw [← c03c_aux_iterDx]
  have hy : ∀ j, 1 ≤ j → ∀ (G : ℝ → ℂ), c03c_aux_Dy^[j] (fun _ ξ => G ξ) = fun _ _ => 0 := by
    intro j hj G
    induction j with
    | zero => omega
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      rcases Nat.eq_zero_or_pos j with rfl | hj'
      · funext y ξ; simp [c03c_aux_Dy]
      · rw [ih hj']; funext y ξ; simp [c03c_aux_Dy]
  intro j k hjk y ξ hy0 hξ
  rw [hx]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Function.iterate_zero, id_eq, if_true, Real.rpow_zero, mul_one,
      CharP.cast_eq_zero, neg_zero]
    exact hb k (by omega) ξ hξ
  · rw [hy j hj (iteratedDeriv k a)]
    simp [Nat.pos_iff_ne_zero.mp hj]


theorem c03c_aux_farAmp0_eq (p : ℝ) (χ : ℝ → ℝ) (a : ℝ → ℂ) :
    ∀ q ∈ c03c_aux_W, c03c_farAmp p χ a 0 q.1 q.2 =
      (fun y ξ => a ξ * c03c_aux_Gam p (fun r => 1 - χ r) y ξ) q.1 q.2 := by
  rintro ⟨y, ξ⟩ hq
  simp only [c03c_farAmp, c03c_aux_Gam]
  rw [c03c_aux_r_eq p hq.1 ξ]

theorem c03c_aux_farAmp_succ_eq (p : ℝ) (hp : 0 < p) (χ : ℝ → ℝ) (a : ℝ → ℂ) (n : ℕ)
    (hvan : ∀ y ξ : ℝ, 0 < y → 0 < ξ → 3 * lambda0 p y / 4 ≤ ξ → ξ ≤ 3 * lambda0 p y / 2 →
      c03c_farAmp p χ a n y ξ = 0) :
    ∀ q ∈ c03c_aux_W, c03c_farAmp p χ a (n + 1) q.1 q.2 =
      c03c_aux_Dx (fun y ξ => c03c_farAmp p χ a n y ξ * c03c_aux_Rt p y ξ) q.1 q.2 := by
  rintro ⟨y, ξ⟩ ⟨hy, hξ⟩
  have hy : 0 < y := hy
  have hξ : 0 < ξ := hξ
  show deriv (fun ξ' => c03c_farAmp p χ a n y ξ' / (Complex.I * ((y - ξ' ^ p : ℝ) : ℂ))) ξ =
    deriv (fun ξ' => c03c_farAmp p χ a n y ξ' * c03c_aux_Rt p y ξ') ξ
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hξ] with ξ' hξ'
  have hξ'0 : 0 < ξ' := hξ'
  by_cases h0 : c03c_farAmp p χ a n y ξ' = 0
  · rw [h0]; simp
  · have hl : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
    have hout : ξ' < 3 * lambda0 p y / 4 ∨ 3 * lambda0 p y / 2 < ξ' := by
      by_contra hc
      push Not at hc
      exact h0 (hvan y ξ' hy hξ'0 hc.1 hc.2)
    have hθ : c03c_aux_theta (ξ' * y ^ (-1 / p)) = 0 := by
      apply c03c_aux_theta_zero
      rw [c03c_aux_r_eq p hy ξ']
      rcases hout with h | h
      · left; rw [div_le_iff₀ hl]; linarith
      · right; rw [le_div_iff₀ hl]; linarith
    simp only [c03c_aux_Rt, c03c_aux_Gam, c03c_aux_R0, hθ, sub_zero, Complex.ofReal_one, one_mul]
    by_cases hw : y - ξ' ^ p = 0
    · simp [hw]
    · have hw' : ((y - ξ' ^ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
      push_cast
      field_simp
      rw [Complex.I_sq]; ring


theorem c03c_aux_farAmp_SV (p m : ℝ) (hp : 0 < p) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1)
    {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) : ∀ n : ℕ,
    c03c_aux_Sm (c03c_farAmp p χ a n) c03c_aux_W ∧
      ∀ y ξ : ℝ, 0 < y → 0 < ξ →
        (ξ ≤ 1 ∨ (3 * lambda0 p y / 4 ≤ ξ ∧ ξ ≤ 3 * lambda0 p y / 2)) →
        c03c_farAmp p χ a n y ξ = 0 := by
  have hPsi : c03c_aux_Sm (c03c_aux_Gam p (fun r => 1 - χ r)) c03c_aux_W :=
    c03c_aux_Gam_Sm p (contDiff_const.sub hχ)
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · have h := (c03c_aux_A_Sm ha).mul hPsi
      refine h.congr fun q hq => ?_
      exact c03c_aux_farAmp0_eq p χ a q hq
    · intro y ξ hy hξ h
      simp only [c03c_farAmp]
      rcases h with h | ⟨h1, h2⟩
      · rw [ha.2.1 ξ ⟨hξ, h⟩, zero_mul]
      · have hl : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
        rw [hχ1 (ξ / lambda0 p y) ⟨by rw [le_div_iff₀ hl]; linarith,
          by rw [div_le_iff₀ hl]; linarith⟩]
        simp
  | succ n ih =>
    obtain ⟨hsm, hvan⟩ := ih
    have heq := c03c_aux_farAmp_succ_eq p hp χ a n
      (fun y ξ hy hξ h1 h2 => hvan y ξ hy hξ (Or.inr ⟨h1, h2⟩))
    have hprod : c03c_aux_Sm (fun y ξ => c03c_farAmp p χ a n y ξ * c03c_aux_Rt p y ξ)
        c03c_aux_W := hsm.mul (c03c_aux_Rt_Sm p hp)
    refine ⟨?_, ?_⟩
    · exact (c03c_aux_Sm_Dx c03c_aux_W_open hprod).congr fun q hq => heq q hq
    · intro y ξ hy hξ h
      rw [heq (y, ξ) ⟨hy, hξ⟩]
      show deriv (fun ξ' => c03c_farAmp p χ a n y ξ' * c03c_aux_Rt p y ξ') ξ = 0
      have hd : DifferentiableAt ℝ (fun ξ' => c03c_farAmp p χ a n y ξ' * c03c_aux_Rt p y ξ') ξ :=
        (c03c_aux_Sm_hasDerivAt_x c03c_aux_W_open hprod (y := y) (ξ := ξ) ⟨hy, hξ⟩).differentiableAt
      apply c03c_aux_deriv_zero_side hd
      have hl : 0 < lambda0 p y := Real.rpow_pos_of_pos hy _
      rcases h with h | ⟨h1, h2⟩
      · right
        refine ⟨ξ / 2, by linarith, fun t ht => ?_⟩
        have : c03c_farAmp p χ a n y t = 0 :=
          hvan y t hy (by linarith [ht.1]) (Or.inl (by linarith [ht.2]))
        simp [this]
      · rcases lt_or_eq_of_le h2 with h2 | h2
        · left
          refine ⟨3 * lambda0 p y / 2 - ξ, by linarith, fun t ht => ?_⟩
          have : c03c_farAmp p χ a n y t = 0 :=
            hvan y t hy (by linarith [ht.1]) (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          simp [this]
        · right
          refine ⟨3 * lambda0 p y / 4, by linarith, fun t ht => ?_⟩
          have : c03c_farAmp p χ a n y t = 0 :=
            hvan y t hy (by linarith [ht.1]) (Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          simp [this]


/-- Leibniz constant combination. -/
def c03c_aux_Kprod (K1 K2 : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun j k =>
  ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (k + 1),
    (j.choose a : ℝ) * (k.choose b : ℝ) * (K1 a b * K2 (j - a) (k - b))

/-- Constants for the far amplitudes. -/
def c03c_aux_Kseq (K0 KR : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => K0
  | n + 1 => fun j k => c03c_aux_Kprod (c03c_aux_Kseq K0 KR n) KR j (k + 1)

theorem c03c_aux_Sym_eq {p : ℝ} {F : ℝ → ℝ → ℂ} {μ ν μ' ν' : ℝ} {K : ℕ → ℕ → ℝ} {N : ℕ}
    (h : c03c_aux_Sym p F μ ν K N) (hμ : μ = μ') (hν : ν = ν') : c03c_aux_Sym p F μ' ν' K N := by
  subst hμ hν; exact h

theorem c03c_aux_farAmp_Bnd (p m : ℝ) (hp : 0 < p) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1)
    {a : ℝ → ℂ} (ha : a ∈ c03_sp_symbol m) (Ck : ℕ → ℝ) (KP KR : ℕ → ℕ → ℝ)
    (hKP : ∀ N, c03c_aux_Sym p (c03c_aux_Gam p (fun r => 1 - χ r)) 0 0 KP N)
    (hKR : ∀ N, c03c_aux_Sym p (c03c_aux_Rt p) 0 (-1) KR N) (n : ℕ) : ∀ N : ℕ,
    (∀ i ≤ N + n, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) →
    c03c_aux_Sym p (c03c_farAmp p χ a n) (m - n) (-(n : ℝ))
      (c03c_aux_Kseq (c03c_aux_Kprod (fun j k => if j = 0 then Ck k else 0) KP) KR n) N := by
  have hSV := c03c_aux_farAmp_SV p m hp χ hχ hχ1 ha
  have hPsi : c03c_aux_Sm (c03c_aux_Gam p (fun r => 1 - χ r)) c03c_aux_W :=
    c03c_aux_Gam_Sm p (contDiff_const.sub hχ)
  induction n with
  | zero =>
    intro N hb
    have h := c03c_aux_Sym_mul hp (c03c_aux_A_Sm ha) hPsi
      (c03c_aux_A_Sym (p := p) Ck N (fun i hi => hb i (by omega))) (hKP N)
    have h2 := c03c_aux_Sym_congr (fun q hq => (c03c_aux_farAmp0_eq p χ a q hq).symm) h
    exact c03c_aux_Sym_eq h2 (by simp) (by simp)
  | succ n ih =>
    intro N hb
    have h1 := ih (N + 1) (fun i hi => hb i (by omega))
    have h2 := c03c_aux_Sym_mul hp (hSV n).1 (c03c_aux_Rt_Sm p hp) h1 (hKR (N + 1))
    have h3 := c03c_aux_Sym_Dx h2
    have heq := c03c_aux_farAmp_succ_eq p hp χ a n
      (fun y ξ hy hξ h1 h2 => (hSV n).2 y ξ hy hξ (Or.inr ⟨h1, h2⟩))
    have h4 := c03c_aux_Sym_congr (fun q hq => (heq q hq).symm) h3
    exact c03c_aux_Sym_eq h4 (by push_cast; ring) (by push_cast; ring)

/-- Blueprint: lem:c03_sp_far_symbol_iteration.  The far-region IBP amplitudes `a_n(y,ξ)` are
smooth on `y, ξ > 0`, vanish for `ξ ≤ 1` and for `3λ₀/4 ≤ ξ ≤ 3λ₀/2`, and
`|∂_y^j ∂_ξ^k a_n| ≤ D ξ^{m-n-k} (y+ξ^p)^{-n} y^{-j}` (`y > 0`, `ξ ≥ 1`),
`D = D(p,m,n,k,j,χ_sp,C_0,…,C_{n+k+j+2})`. -/
theorem c03_sp_far_symbol_iteration (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) :
    (∀ a ∈ c03_sp_symbol m, ∀ n : ℕ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c03c_farAmp p χ a n q.1 q.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ∀ y ξ : ℝ, 0 < y → 0 < ξ →
        (ξ ≤ 1 ∨ (3 * lambda0 p y / 4 ≤ ξ ∧ ξ ≤ 3 * lambda0 p y / 2)) →
        c03c_farAmp p χ a n y ξ = 0) ∧
    ∀ n k j : ℕ, ∀ Ck : ℕ → ℝ, ∃ D, 0 < D ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ i ≤ n + k + j + 2, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv i a ξ‖ ≤ Ck i * ξ ^ (m - i)) →
      ∀ y ξ : ℝ, 0 < y → 1 ≤ ξ →
        ‖iteratedDeriv j (fun y' => iteratedDeriv k (fun ξ' => c03c_farAmp p χ a n y' ξ') ξ) y‖ ≤
          D * ξ ^ (m - n - k) * (y + ξ ^ p) ^ (-(n : ℝ)) * y ^ (-(j : ℝ)) := by
  refine ⟨fun a ha n => c03c_aux_farAmp_SV p m hp χ hχ hχ1 ha n, ?_⟩
  -- constants of the cutoff and of the reciprocal
  have hg' : ∀ r, (r < 1 / 2 ∨ 2 < r) → deriv (fun r => 1 - χ r) r = 0 := by
    intro r hr
    have hnot : r ∉ tsupport χ := fun h => by
      have := hχs h; rcases hr with hr | hr
      · linarith [this.1]
      · linarith [this.2]
    have : (fun r => 1 - χ r) =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with x hx
      simp [hx]
    rw [this.deriv_eq]; simp
  obtain ⟨KP, -, hKP⟩ := c03c_aux_Gam_Sym p hp (g := fun r => 1 - χ r) (contDiff_const.sub hχ)
    (fun r => by have := hχ01 r; rw [abs_le]; constructor <;> linarith)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hg'
  obtain ⟨KR, -, hKR⟩ := c03c_aux_Rt_Sym p hp hp1
  intro n k j Ck
  set K := c03c_aux_Kseq (c03c_aux_Kprod (fun j k => if j = 0 then Ck k else 0) KP) KR n j k
  refine ⟨|K| + 1, by positivity, fun a ha hb y ξ hy hξ => ?_⟩
  have hS := c03c_aux_farAmp_Bnd p m hp χ hχ hχ1 ha Ck KP KR hKP hKR n (j + k)
    (fun i hi => hb i (by omega))
  rw [c03c_aux_mixed_eq]
  refine (hS j k le_rfl y ξ hy hξ).trans ?_
  have hξ0 : 0 < ξ := by linarith
  have hs : 0 < y + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; linarith
  have hX : 0 ≤ ξ ^ (m - n - k) * (y + ξ ^ p) ^ (-(n : ℝ)) * y ^ (-(j : ℝ)) := by positivity
  have hK : K ≤ |K| + 1 := by linarith [le_abs_self K]
  calc K * ξ ^ (m - n - k) * (y + ξ ^ p) ^ (-(n : ℝ)) * y ^ (-(j : ℝ))
      = K * (ξ ^ (m - n - k) * (y + ξ ^ p) ^ (-(n : ℝ)) * y ^ (-(j : ℝ))) := by ring
    _ ≤ (|K| + 1) * (ξ ^ (m - n - k) * (y + ξ ^ p) ^ (-(n : ℝ)) * y ^ (-(j : ℝ))) :=
        mul_le_mul_of_nonneg_right hK hX
    _ = _ := by ring

/-! ## Exponential jets -/

/-- Blueprint: lem:c03_exp_jet_recursion.  `E_n` is smooth on `U`, `∂^n e^{iΘ} = e^{iΘ} E_n` on
`U`, `E₁ = iΘ'`, `E₂ = iΘ'' - (Θ')²`. -/
theorem c03_exp_jet_recursion (U : Set ℝ) (hU : IsOpen U) (Θ : ℝ → ℝ)
    (hΘ : ContDiffOn ℝ (⊤ : ℕ∞) Θ U) :
    (∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (c03c_expJet Θ n) U ∧
      ∀ x ∈ U, iteratedDeriv n (fun x => Complex.exp (Complex.I * (Θ x : ℂ))) x =
        Complex.exp (Complex.I * (Θ x : ℂ)) * c03c_expJet Θ n x) ∧
    (∀ x ∈ U, c03c_expJet Θ 1 x = Complex.I * ((deriv Θ x : ℝ) : ℂ)) ∧
    ∀ x ∈ U, c03c_expJet Θ 2 x = Complex.I * ((iteratedDeriv 2 Θ x : ℝ) : ℂ) - ((deriv Θ x : ℝ) : ℂ) ^ 2 := by
  have hΘ' := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hΘ
  have hdΘ : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ((deriv Θ x : ℝ) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hΘ'.2
  set e : ℝ → ℂ := fun x => Complex.exp (Complex.I * (Θ x : ℂ)) with he
  have hede : ∀ x ∈ U, HasDerivAt e (e x * (Complex.I * ((deriv Θ x : ℝ) : ℂ))) x := by
    intro x hx
    have hd : HasDerivAt Θ (deriv Θ x) x :=
      ((hΘ'.1 x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
    have := ((hd.ofReal_comp).const_mul Complex.I).cexp
    simpa [he, mul_comm] using this
  have main : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (c03c_expJet Θ n) U ∧
      ∀ x ∈ U, iteratedDeriv n e x = e x * c03c_expJet Θ n x := by
    intro n
    induction n with
    | zero =>
      refine ⟨contDiffOn_const, fun x _ => ?_⟩
      simp [c03c_expJet]
    | succ n ih =>
      obtain ⟨hc, hid⟩ := ih
      have hc' := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp hc
      refine ⟨?_, fun x hx => ?_⟩
      · show ContDiffOn ℝ (⊤ : ℕ∞) (fun x => deriv (c03c_expJet Θ n) x +
          Complex.I * ((deriv Θ x : ℝ) : ℂ) * c03c_expJet Θ n x) U
        exact hc'.2.add ((contDiffOn_const.mul hdΘ).mul hc)
      · rw [iteratedDeriv_succ]
        have hev : iteratedDeriv n e =ᶠ[𝓝 x] fun y => e y * c03c_expJet Θ n y := by
          filter_upwards [hU.mem_nhds hx] with y hy using hid y hy
        rw [hev.deriv_eq]
        have hE : HasDerivAt (c03c_expJet Θ n) (deriv (c03c_expJet Θ n) x) x :=
          ((hc'.1 x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
        have hm : deriv (fun y => e y * c03c_expJet Θ n y) x = _ := ((hede x hx).mul hE).deriv
        rw [hm]
        simp only [c03c_expJet]
        ring
  refine ⟨main, fun x hx => ?_, fun x hx => ?_⟩
  · simp [c03c_expJet]
  · have h1 : c03c_expJet Θ 1 = fun x => Complex.I * ((deriv Θ x : ℝ) : ℂ) := by
      funext y; simp [c03c_expJet]
    show deriv (c03c_expJet Θ 1) x + Complex.I * ((deriv Θ x : ℝ) : ℂ) * c03c_expJet Θ 1 x = _
    rw [h1]
    have hd2 : HasDerivAt (deriv Θ) (deriv (deriv Θ) x) x :=
      (((contDiffOn_infty_iff_deriv_of_isOpen hU).mp hΘ'.2).1 x hx
        |>.differentiableAt (hU.mem_nhds hx)).hasDerivAt
    have hm := ((hd2.ofReal_comp).const_mul Complex.I).deriv
    rw [hm, iteratedDeriv_succ, iteratedDeriv_one]
    linear_combination (((deriv Θ x : ℝ) : ℂ) ^ 2) * Complex.I_mul_I

/-! ### Combinatorics of exponential jets -/

/-- Weight `∑ (i+1) q_i`. -/
def c03c_aux_wt {N : ℕ} (q : Fin N → ℕ) : ℕ := ∑ i, (i.val + 1) * q i

/-- Index set `{q : q_i ≤ N, wt q = n}`. -/
def c03c_aux_S (N n : ℕ) : Finset (Fin N → ℕ) :=
  (Fintype.piFinset fun _ : Fin N => Finset.range (N + 1)).filter (fun q => c03c_aux_wt q = n)

/-- `∏ q_i! ((i+1)!)^{q_i}`. -/
def c03c_aux_D {N : ℕ} (q : Fin N → ℕ) : ℕ := ∏ i, (q i).factorial * (i.val + 1).factorial ^ q i

/-- `i^{|q|}/D(q)`. -/
def c03c_aux_coef {N : ℕ} (q : Fin N → ℕ) : ℂ := Complex.I ^ (∑ i, q i) / (c03c_aux_D q : ℂ)

/-- `∏ v_i^{q_i}`. -/
def c03c_aux_mon {N : ℕ} (v : Fin N → ℂ) (q : Fin N → ℕ) : ℂ := ∏ i, v i ^ q i

theorem c03c_aux_upd_prod {N : ℕ} {M : Type*} [CommMonoid M] (F : Fin N → ℕ → M) (q : Fin N → ℕ)
    (j : Fin N) (b : ℕ) :
    (∏ i, F i (Function.update q j b i)) * F j (q j) = (∏ i, F i (q i)) * F j b := by
  rw [Fintype.prod_eq_mul_prod_compl j (fun i => F i (Function.update q j b i)),
    Fintype.prod_eq_mul_prod_compl j (fun i => F i (q i))]
  simp only [Function.update_self]
  have : ∏ i ∈ {j}ᶜ, F i (Function.update q j b i) = ∏ i ∈ {j}ᶜ, F i (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Finset.mem_compl, Finset.mem_singleton] at hi
      rw [Function.update_of_ne hi]
  rw [this]; ac_rfl

theorem c03c_aux_upd_sum {N : ℕ} (F : Fin N → ℕ → ℕ) (q : Fin N → ℕ) (j : Fin N) (b : ℕ) :
    (∑ i, F i (Function.update q j b i)) + F j (q j) = (∑ i, F i (q i)) + F j b := by
  rw [Fintype.sum_eq_add_sum_compl j (fun i => F i (Function.update q j b i)),
    Fintype.sum_eq_add_sum_compl j (fun i => F i (q i))]
  simp only [Function.update_self]
  have : ∑ i ∈ {j}ᶜ, F i (Function.update q j b i) = ∑ i ∈ {j}ᶜ, F i (q i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_compl, Finset.mem_singleton] at hi
      rw [Function.update_of_ne hi]
  rw [this]; ring

theorem c03c_aux_mem_S {N n : ℕ} (hn : n ≤ N) (q : Fin N → ℕ) :
    q ∈ c03c_aux_S N n ↔ c03c_aux_wt q = n := by
  simp only [c03c_aux_S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have : (i.val + 1) * q i ≤ n := by
      rw [← h, c03c_aux_wt]
      exact Finset.single_le_sum (f := fun i => (i.val + 1) * q i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    nlinarith


theorem c03c_aux_mon_update {N : ℕ} (v : Fin N → ℂ) (q : Fin N → ℕ) (j : Fin N) (b : ℕ) :
    c03c_aux_mon v (Function.update q j b) = v j ^ b * ∏ i ∈ {j}ᶜ, v i ^ q i := by
  rw [c03c_aux_mon, Fintype.prod_eq_mul_prod_compl j, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_compl, Finset.mem_singleton] at hi
  rw [Function.update_of_ne hi]

theorem c03c_aux_mon_eq {N : ℕ} (v : Fin N → ℂ) (q : Fin N → ℕ) (j : Fin N) :
    c03c_aux_mon v q = v j ^ q j * ∏ i ∈ {j}ᶜ, v i ^ q i := by
  rw [c03c_aux_mon, Fintype.prod_eq_mul_prod_compl j]

theorem c03c_aux_wt_update {N : ℕ} (q : Fin N → ℕ) (j : Fin N) (b : ℕ) :
    c03c_aux_wt (Function.update q j b) + (j.val + 1) * q j = c03c_aux_wt q + (j.val + 1) * b :=
  c03c_aux_upd_sum (fun i x => (i.val + 1) * x) q j b

theorem c03c_aux_card_update {N : ℕ} (q : Fin N → ℕ) (j : Fin N) (b : ℕ) :
    (∑ i, Function.update q j b i) + q j = (∑ i, q i) + b :=
  c03c_aux_upd_sum (fun _ x => x) q j b

theorem c03c_aux_D_update {N : ℕ} (q : Fin N → ℕ) (j : Fin N) (b : ℕ) :
    c03c_aux_D (Function.update q j b) * ((q j).factorial * (j.val + 1).factorial ^ q j) =
      c03c_aux_D q * (b.factorial * (j.val + 1).factorial ^ b) :=
  c03c_aux_upd_prod (fun i x => x.factorial * (i.val + 1).factorial ^ x) q j b

theorem c03c_aux_D_pos {N : ℕ} (q : Fin N → ℕ) : 0 < c03c_aux_D q :=
  Finset.prod_pos fun i _ => Nat.mul_pos (Nat.factorial_pos _) (pow_pos (Nat.factorial_pos _) _)

/-- Multiplication by `iΘ'`: the shift `q ↦ q + e₀`. -/
theorem c03c_aux_jet_A (M n : ℕ) (hn : n + 1 ≤ M + 1) (v : Fin (M + 1) → ℂ) :
    ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * Complex.I *
        c03c_aux_mon v (Function.update q 0 (q 0 + 1)) =
      ∑ q ∈ c03c_aux_S (M + 1) (n + 1), (q 0 : ℂ) * c03c_aux_coef q * c03c_aux_mon v q := by
  set inc : (Fin (M + 1) → ℕ) → (Fin (M + 1) → ℕ) := fun q => Function.update q 0 (q 0 + 1)
    with hinc
  have hwt : ∀ q, c03c_aux_wt (inc q) = c03c_aux_wt q + 1 := by
    intro q; have := c03c_aux_wt_update q 0 (q 0 + 1); simp at this; simp only [hinc]; omega
  have hinj : Set.InjOn inc (c03c_aux_S (M + 1) n) := by
    intro q _ q' _ h
    have h0 : q 0 = q' 0 := by
      have := congrFun h 0; simp [hinc] at this; exact this
    funext i
    by_cases hi : i = 0
    · rw [hi, h0]
    · have := congrFun h i; simp [hinc, Function.update_of_ne hi] at this; exact this
  have hsub : (c03c_aux_S (M + 1) n).image inc ⊆ c03c_aux_S (M + 1) (n + 1) := by
    intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    rw [c03c_aux_mem_S (by omega)] at hq ⊢
    rw [hwt, hq]
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hinc, Function.update_self]
    have hcard := c03c_aux_card_update q 0 (q 0 + 1)
    have hD := c03c_aux_D_update q 0 (q 0 + 1)
    simp only [Fin.val_zero, zero_add, Nat.factorial_one, one_pow, mul_one] at hD
    rw [Nat.factorial_succ] at hD
    have hDq := c03c_aux_D_pos q
    have hDq' := c03c_aux_D_pos (Function.update q 0 (q 0 + 1))
    have hf := Nat.factorial_pos (q 0)
    have hD' : c03c_aux_D (Function.update q 0 (q 0 + 1)) = c03c_aux_D q * (q 0 + 1) := by
      have : c03c_aux_D (Function.update q 0 (q 0 + 1)) * (q 0).factorial =
          c03c_aux_D q * (q 0 + 1) * (q 0).factorial := by rw [hD]; ring
      exact Nat.eq_of_mul_eq_mul_right hf this
    have hcard' : ∑ i, Function.update q 0 (q 0 + 1) i = (∑ i, q i) + 1 := by omega
    simp only [c03c_aux_coef, hcard', hD']
    push_cast
    have : (c03c_aux_D q : ℂ) ≠ 0 := by exact_mod_cast hDq.ne'
    field_simp
    ring
  · intro q' hq' hnot
    by_cases h0 : q' 0 = 0
    · simp [h0]
    · exfalso; apply hnot
      refine Finset.mem_image.mpr ⟨Function.update q' 0 (q' 0 - 1), ?_, ?_⟩
      · rw [c03c_aux_mem_S (by omega)] at hq' ⊢
        have := c03c_aux_wt_update q' 0 (q' 0 - 1)
        simp at this; omega
      · simp only [hinc, Function.update_self]
        funext i
        by_cases hi : i = 0
        · rw [hi, Function.update_self]; omega
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]


/-- The shift `q ↦ q - e_a + e_s` (`a = j`, `s = j+1`). -/
def c03c_aux_tau {M : ℕ} (j : Fin M) (q : Fin (M + 1) → ℕ) : Fin (M + 1) → ℕ :=
  Function.update (Function.update q j.castSucc (q j.castSucc - 1)) j.succ (q j.succ + 1)

theorem c03c_aux_tau_apply_a {M : ℕ} (j : Fin M) (q : Fin (M + 1) → ℕ) :
    c03c_aux_tau j q j.castSucc = q j.castSucc - 1 := by
  rw [c03c_aux_tau, Function.update_of_ne (Fin.castSucc_lt_succ).ne, Function.update_self]

theorem c03c_aux_tau_apply_s {M : ℕ} (j : Fin M) (q : Fin (M + 1) → ℕ) :
    c03c_aux_tau j q j.succ = q j.succ + 1 := by
  rw [c03c_aux_tau, Function.update_self]

theorem c03c_aux_tau_apply_ne {M : ℕ} (j : Fin M) (q : Fin (M + 1) → ℕ) (i : Fin (M + 1))
    (ha : i ≠ j.castSucc) (hs : i ≠ j.succ) : c03c_aux_tau j q i = q i := by
  rw [c03c_aux_tau, Function.update_of_ne hs, Function.update_of_ne ha]

theorem c03c_aux_wt_tau {M : ℕ} (j : Fin M) (q : Fin (M + 1) → ℕ) (h : 1 ≤ q j.castSucc) :
    c03c_aux_wt (c03c_aux_tau j q) = c03c_aux_wt q + 1 := by
  have h1 := c03c_aux_wt_update q j.castSucc (q j.castSucc - 1)
  have h2 := c03c_aux_wt_update (Function.update q j.castSucc (q j.castSucc - 1)) j.succ
    (q j.succ + 1)
  rw [Function.update_of_ne (Fin.castSucc_lt_succ).ne'] at h2
  simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
  rw [c03c_aux_tau]
  have e : (j.val + 1) * (q j.castSucc - 1) + (j.val + 1) = (j.val + 1) * q j.castSucc := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel h]
  nlinarith

theorem c03c_aux_card_tau {M : ℕ} (j : Fin M) (q : Fin (M + 1) → ℕ) (h : 1 ≤ q j.castSucc) :
    ∑ i, c03c_aux_tau j q i = ∑ i, q i := by
  have h1 := c03c_aux_card_update q j.castSucc (q j.castSucc - 1)
  have h2 := c03c_aux_card_update (Function.update q j.castSucc (q j.castSucc - 1)) j.succ
    (q j.succ + 1)
  rw [Function.update_of_ne (Fin.castSucc_lt_succ).ne'] at h2
  rw [c03c_aux_tau]
  omega

theorem c03c_aux_coef_tau {M : ℕ} (j : Fin M) (q : Fin (M + 1) → ℕ) (h : 1 ≤ q j.castSucc) :
    c03c_aux_coef q * (q j.castSucc : ℂ) =
      ((j.val : ℂ) + 2) * ((q j.succ : ℂ) + 1) * c03c_aux_coef (c03c_aux_tau j q) := by
  set a := j.castSucc
  set s := j.succ
  obtain ⟨m, hm⟩ : ∃ m, q a = m + 1 := ⟨q a - 1, by omega⟩
  set u1 := Function.update q a m with hu1
  have h1 := c03c_aux_D_update q a m
  have h2 := c03c_aux_D_update u1 s (q s + 1)
  have hu1s : u1 s = q s := Function.update_of_ne (Fin.castSucc_lt_succ).ne' _ _
  rw [hu1s] at h2
  have hta : c03c_aux_tau j q = Function.update u1 s (q s + 1) := by
    rw [c03c_aux_tau, hu1]; congr 2; change q a - 1 = m; omega
  have ha : (a : ℕ) = j.val := Fin.val_castSucc j
  have hs : (s : ℕ) = j.val + 1 := Fin.val_succ j
  rw [ha, hm, Nat.factorial_succ m, pow_succ] at h1
  rw [hs, Nat.factorial_succ (q s), pow_succ, Nat.factorial_succ (j.val + 1)] at h2
  have g1 : c03c_aux_D u1 * ((m + 1) * (j.val + 1).factorial) = c03c_aux_D q := by
    have hp : 0 < m.factorial * (j.val + 1).factorial ^ m :=
      Nat.mul_pos (Nat.factorial_pos _) (pow_pos (Nat.factorial_pos _) _)
    apply Nat.eq_of_mul_eq_mul_right hp
    calc c03c_aux_D u1 * ((m + 1) * (j.val + 1).factorial) * (m.factorial * (j.val + 1).factorial ^ m)
        = c03c_aux_D u1 * ((m + 1) * m.factorial * ((j.val + 1).factorial ^ m *
          (j.val + 1).factorial)) := by ring
      _ = _ := h1
  have g2 : c03c_aux_D (Function.update u1 s (q s + 1)) =
      c03c_aux_D u1 * ((q s + 1) * ((j.val + 1 + 1) * (j.val + 1).factorial)) := by
    have hp : 0 < (q s).factorial * ((j.val + 1 + 1) * (j.val + 1).factorial) ^ q s :=
      Nat.mul_pos (Nat.factorial_pos _) (pow_pos (Nat.mul_pos (Nat.succ_pos _)
        (Nat.factorial_pos _)) _)
    apply Nat.eq_of_mul_eq_mul_right hp
    rw [h2]; ring
  have hc := c03c_aux_card_tau j q h
  rw [c03c_aux_coef, c03c_aux_coef, hc, hta, g2, ← g1, hm]
  have hD1 := c03c_aux_D_pos u1
  have hD1c : (c03c_aux_D u1 : ℂ) ≠ 0 := by exact_mod_cast hD1.ne'
  have hfc : ((j.val + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast
  have : (j.val : ℂ) + 1 + 1 ≠ 0 := by norm_cast
  have : (m : ℂ) + 1 ≠ 0 := by norm_cast
  have : (q s : ℂ) + 1 ≠ 0 := by norm_cast
  field_simp
  ring


/-- Differentiation of a factor: the shift `q ↦ τ_j q`. -/
theorem c03c_aux_jet_B (M n : ℕ) (hn : n + 1 ≤ M + 1) (v : Fin (M + 1) → ℂ) (j : Fin M) :
    ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * (q j.castSucc : ℂ) *
        c03c_aux_mon v (c03c_aux_tau j q) =
      ∑ q ∈ c03c_aux_S (M + 1) (n + 1),
        ((j.val : ℂ) + 2) * (q j.succ : ℂ) * c03c_aux_coef q * c03c_aux_mon v q := by
  have has : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ).ne
  -- restrict the left sum
  set T := (c03c_aux_S (M + 1) n).filter (fun q => 1 ≤ q j.castSucc) with hT
  have hL : ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * (q j.castSucc : ℂ) *
      c03c_aux_mon v (c03c_aux_tau j q) =
      ∑ q ∈ T, c03c_aux_coef q * (q j.castSucc : ℂ) * c03c_aux_mon v (c03c_aux_tau j q) := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs with h
    · rfl
    · have : q j.castSucc = 0 := by omega
      simp [this]
  rw [hL]
  have hinj : Set.InjOn (c03c_aux_tau j) T := by
    intro q hq q' hq' h
    simp only [hT, Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
    funext i
    by_cases hia : i = j.castSucc
    · have := congrFun h j.castSucc
      rw [c03c_aux_tau_apply_a, c03c_aux_tau_apply_a] at this
      rw [hia]; omega
    · by_cases his : i = j.succ
      · have := congrFun h j.succ
        rw [c03c_aux_tau_apply_s, c03c_aux_tau_apply_s] at this
        rw [his]; omega
      · have := congrFun h i
        rwa [c03c_aux_tau_apply_ne j q i hia his, c03c_aux_tau_apply_ne j q' i hia his] at this
  have hsub : T.image (c03c_aux_tau j) ⊆ c03c_aux_S (M + 1) (n + 1) := by
    intro q' hq'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    simp only [hT, Finset.mem_filter] at hq
    rw [c03c_aux_mem_S (by omega)] at hq ⊢
    rw [c03c_aux_wt_tau j q hq.2, hq.1]
  rw [← Finset.sum_subset hsub ?_, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun q hq => ?_
    simp only [hT, Finset.mem_filter] at hq
    rw [c03c_aux_tau_apply_s, c03c_aux_coef_tau j q hq.2]
    push_cast; ring
  · intro q' hq' hnot
    by_cases h0 : q' j.succ = 0
    · simp [h0]
    · exfalso; apply hnot
      set q := Function.update (Function.update q' j.succ (q' j.succ - 1)) j.castSucc (q' j.castSucc + 1) with hq
      have hqa : q j.castSucc = q' j.castSucc + 1 := by rw [hq, Function.update_self]
      have hqs : q j.succ = q' j.succ - 1 := by
        rw [hq, Function.update_of_ne has.symm, Function.update_self]
      refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
      · simp only [hT, Finset.mem_filter]
        refine ⟨?_, by omega⟩
        rw [c03c_aux_mem_S (by omega)] at hq' ⊢
        have e1 := c03c_aux_wt_update q' j.succ (q' j.succ - 1)
        have e2 := c03c_aux_wt_update (Function.update q' j.succ (q' j.succ - 1)) j.castSucc (q' j.castSucc + 1)
        rw [Function.update_of_ne has] at e2
        simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
        have e : (j.val + 1 + 1) * (q' j.succ - 1) + (j.val + 1 + 1) = (j.val + 1 + 1) * q' j.succ := by
          rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
        rw [← hq] at e2
        nlinarith
      · funext i
        by_cases hia : i = j.castSucc
        · rw [hia, c03c_aux_tau_apply_a, hqa]; omega
        · by_cases his : i = j.succ
          · rw [his, c03c_aux_tau_apply_s, hqs]; omega
          · rw [c03c_aux_tau_apply_ne j q i hia his, hq, Function.update_of_ne hia,
              Function.update_of_ne his]


/-- `∏_{k ≠ a} v_k^{q_k} · (q_a v_a^{q_a-1} v_s) = q_a · mon(τ_j q)`. -/
theorem c03c_aux_mon_tau {M : ℕ} (v : Fin (M + 1) → ℂ) (j : Fin M) (q : Fin (M + 1) → ℕ) :
    (∏ k ∈ Finset.univ.erase j.castSucc, v k ^ q k) *
        ((q j.castSucc : ℂ) * v j.castSucc ^ (q j.castSucc - 1) * v j.succ) =
      (q j.castSucc : ℂ) * c03c_aux_mon v (c03c_aux_tau j q) := by
  have has : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ).ne
  have hs : j.succ ∈ Finset.univ.erase j.castSucc := Finset.mem_erase.mpr ⟨has.symm, Finset.mem_univ _⟩
  rw [c03c_aux_mon, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j.castSucc),
    ← Finset.mul_prod_erase _ (fun k => v k ^ c03c_aux_tau j q k) hs,
    ← Finset.mul_prod_erase _ (fun k => v k ^ q k) hs,
    c03c_aux_tau_apply_a, c03c_aux_tau_apply_s]
  have hrest : ∏ k ∈ (Finset.univ.erase j.castSucc).erase j.succ, v k ^ c03c_aux_tau j q k =
      ∏ k ∈ (Finset.univ.erase j.castSucc).erase j.succ, v k ^ q k := by
    refine Finset.prod_congr rfl fun k hk => ?_
    simp only [Finset.mem_erase] at hk
    rw [c03c_aux_tau_apply_ne j q k hk.2.1 hk.1]
  rw [hrest]
  ring


/-- The jet values `v_i(x) = Θ^{(i+1)}(x)`. -/
def c03c_aux_jv {N : ℕ} (Θ : ℝ → ℝ) (x : ℝ) : Fin N → ℂ :=
  fun i => ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ)

theorem c03c_aux_iter_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {Θ : ℝ → ℝ}
    (hΘ : ContDiffOn ℝ (⊤ : ℕ∞) Θ U) (k : ℕ) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun y => ((iteratedDeriv k Θ y : ℝ) : ℂ)) ((iteratedDeriv (k + 1) Θ x : ℝ) : ℂ) x := by
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin k Θ U) U :=
    hΘ.differentiableOn_iteratedDerivWithin (by exact_mod_cast WithTop.coe_lt_top _)
      hU.uniqueDiffOn
  have heq : iteratedDerivWithin k Θ U =ᶠ[𝓝 x] iteratedDeriv k Θ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact iteratedDerivWithin_of_isOpen hU hy
  have h2 : DifferentiableAt ℝ (iteratedDeriv k Θ) x :=
    ((h1 x hx).differentiableAt (hU.mem_nhds hx)).congr_of_eventuallyEq heq.symm
  rw [iteratedDeriv_succ]
  exact h2.hasDerivAt.ofReal_comp

/-- Derivative of a jet monomial. -/
theorem c03c_aux_mon_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {Θ : ℝ → ℝ}
    (hΘ : ContDiffOn ℝ (⊤ : ℕ∞) Θ U) {M : ℕ} (q : Fin (M + 1) → ℕ) (hlast : q (Fin.last M) = 0)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun y => c03c_aux_mon (c03c_aux_jv Θ y) q)
      (∑ j : Fin M, (q j.castSucc : ℂ) * c03c_aux_mon (c03c_aux_jv Θ x) (c03c_aux_tau j q)) x := by
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin (M + 1))),
      HasDerivAt (fun y => (c03c_aux_jv Θ y i) ^ q i)
        ((q i : ℂ) * (c03c_aux_jv Θ x i) ^ (q i - 1) *
          ((iteratedDeriv (i.val + 1 + 1) Θ x : ℝ) : ℂ)) x := by
    intro i _
    have h := (c03c_aux_iter_hasDerivAt hU hΘ (i.val + 1) hx).fun_pow (q i)
    simp only [c03c_aux_jv]
    convert h using 1
  have := HasDerivAt.fun_finsetProd hf
  refine (this.congr_deriv ?_)
  rw [Fin.sum_univ_castSucc]
  simp only [hlast, Nat.cast_zero, zero_mul, mul_zero, add_zero, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← c03c_aux_mon_tau]
  congr 2


theorem c03c_aux_S_zero (N : ℕ) : c03c_aux_S N 0 = {fun _ => 0} := by
  ext q
  rw [c03c_aux_mem_S (Nat.zero_le _), Finset.mem_singleton, c03c_aux_wt]
  constructor
  · intro h
    funext i
    have := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
    simpa using this
  · rintro rfl; simp

theorem c03c_aux_wt_succ_split {M : ℕ} (q : Fin (M + 1) → ℕ) :
    c03c_aux_wt q = q 0 + ∑ j : Fin M, (j.val + 2) * q j.succ := by
  rw [c03c_aux_wt, Fin.sum_univ_succ]
  simp only [Fin.val_zero, zero_add, one_mul, Fin.val_succ]

theorem c03c_aux_last_zero {M n : ℕ} (hn : n ≤ M) (q : Fin (M + 1) → ℕ)
    (hq : c03c_aux_wt q = n) : q (Fin.last M) = 0 := by
  have : (M + 1) * q (Fin.last M) ≤ n := by
    rw [← hq, c03c_aux_wt]
    have := Finset.single_le_sum (f := fun i : Fin (M + 1) => (i.val + 1) * q i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.last M))
    simpa using this
  by_contra h
  have : M + 1 ≤ (M + 1) * q (Fin.last M) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h)
  omega

theorem c03c_aux_jet_step_alg (M n : ℕ) (hn : n + 1 ≤ M + 1) (v : Fin (M + 1) → ℂ) :
    (n.factorial : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q *
        ∑ j : Fin M, (q j.castSucc : ℂ) * c03c_aux_mon v (c03c_aux_tau j q) +
      Complex.I * v 0 * ((n.factorial : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) n,
        c03c_aux_coef q * c03c_aux_mon v q) =
      ((n + 1).factorial : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) (n + 1),
        c03c_aux_coef q * c03c_aux_mon v q := by
  have hinc : ∀ q : Fin (M + 1) → ℕ, v 0 * c03c_aux_mon v q =
      c03c_aux_mon v (Function.update q 0 (q 0 + 1)) := by
    intro q
    rw [c03c_aux_mon_update, c03c_aux_mon_eq _ q 0, pow_succ]; ring
  have P1 : ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q *
        ∑ j : Fin M, (q j.castSucc : ℂ) * c03c_aux_mon v (c03c_aux_tau j q) =
      ∑ j : Fin M, ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * (q j.castSucc : ℂ) *
        c03c_aux_mon v (c03c_aux_tau j q) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  have P2 : Complex.I * v 0 * ∑ q ∈ c03c_aux_S (M + 1) n,
        c03c_aux_coef q * c03c_aux_mon v q =
      ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * Complex.I *
        c03c_aux_mon v (Function.update q 0 (q 0 + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← hinc q]; ring
  have P3 : ∑ j : Fin M, ∑ q ∈ c03c_aux_S (M + 1) (n + 1),
        ((j.val : ℂ) + 2) * (q j.succ : ℂ) * c03c_aux_coef q * c03c_aux_mon v q +
      ∑ q ∈ c03c_aux_S (M + 1) (n + 1), (q 0 : ℂ) * c03c_aux_coef q * c03c_aux_mon v q =
      ((n + 1 : ℕ) : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) (n + 1), c03c_aux_coef q * c03c_aux_mon v q := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hw := (c03c_aux_mem_S hn q).mp hq
    rw [c03c_aux_wt_succ_split] at hw
    have hwc : ((n + 1 : ℕ) : ℂ) = (q 0 : ℂ) + ∑ j : Fin M, ((j.val : ℂ) + 2) * (q j.succ : ℂ) := by
      rw [← hw]; push_cast; ring
    rw [hwc, add_mul, Finset.sum_mul, add_comm]
    congr 1 <;> first | exact Finset.sum_congr rfl fun j _ => by ring | ring
  calc (n.factorial : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q *
        ∑ j : Fin M, (q j.castSucc : ℂ) * c03c_aux_mon v (c03c_aux_tau j q) +
      Complex.I * v 0 * ((n.factorial : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) n,
        c03c_aux_coef q * c03c_aux_mon v q)
      = (n.factorial : ℂ) * (∑ j : Fin M, ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q *
          (q j.castSucc : ℂ) * c03c_aux_mon v (c03c_aux_tau j q) +
        ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * Complex.I *
          c03c_aux_mon v (Function.update q 0 (q 0 + 1))) := by
        rw [P1, ← P2]; ring
    _ = (n.factorial : ℂ) * (∑ j : Fin M, ∑ q ∈ c03c_aux_S (M + 1) (n + 1),
        ((j.val : ℂ) + 2) * (q j.succ : ℂ) * c03c_aux_coef q * c03c_aux_mon v q +
        ∑ q ∈ c03c_aux_S (M + 1) (n + 1), (q 0 : ℂ) * c03c_aux_coef q * c03c_aux_mon v q) := by
        rw [c03c_aux_jet_A M n hn v, Finset.sum_congr rfl fun j _ => c03c_aux_jet_B M n hn v j]
    _ = ((n + 1).factorial : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) (n + 1),
        c03c_aux_coef q * c03c_aux_mon v q := by
        rw [P3, Nat.factorial_succ]; push_cast; ring


theorem c03c_aux_jet_formula {U : Set ℝ} (hU : IsOpen U) {Θ : ℝ → ℝ}
    (hΘ : ContDiffOn ℝ (⊤ : ℕ∞) Θ U) (M : ℕ) :
    ∀ n ≤ M + 1, ∀ x ∈ U, c03c_expJet Θ n x = (n.factorial : ℂ) *
      ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * c03c_aux_mon (c03c_aux_jv Θ x) q := by
  intro n
  induction n with
  | zero =>
    intro _ x _
    rw [c03c_aux_S_zero, Finset.sum_singleton]
    simp [c03c_expJet, c03c_aux_coef, c03c_aux_mon, c03c_aux_D]
  | succ n ih =>
    intro hn x hx
    have hev : c03c_expJet Θ n =ᶠ[𝓝 x] fun y => (n.factorial : ℂ) *
        ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * c03c_aux_mon (c03c_aux_jv Θ y) q := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih (by omega) y hy
    have hd : HasDerivAt (fun y => (n.factorial : ℂ) *
        ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q * c03c_aux_mon (c03c_aux_jv Θ y) q)
        ((n.factorial : ℂ) * ∑ q ∈ c03c_aux_S (M + 1) n, c03c_aux_coef q *
          ∑ j : Fin M, (q j.castSucc : ℂ) * c03c_aux_mon (c03c_aux_jv Θ x) (c03c_aux_tau j q)) x := by
      refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun q hq => ?_)
      have hq' := (c03c_aux_mem_S (by omega) q).mp hq
      exact (c03c_aux_mon_hasDerivAt hU hΘ q (c03c_aux_last_zero (by omega) q hq') hx).const_mul _
    have hE : c03c_expJet Θ (n + 1) x = deriv (c03c_expJet Θ n) x +
        Complex.I * ((deriv Θ x : ℝ) : ℂ) * c03c_expJet Θ n x := rfl
    rw [hE, hev.deriv_eq, hd.deriv, ih (by omega) x hx]
    have hv0 : ((deriv Θ x : ℝ) : ℂ) = c03c_aux_jv (N := M + 1) Θ x 0 := by
      simp [c03c_aux_jv, iteratedDeriv_one]
    rw [hv0]
    exact c03c_aux_jet_step_alg M n hn _

/-- Blueprint: lem:c03_exp_jet_coefficients.  For `n ≥ 1`, on `U`,
`E_n = n! ∑_{q : ∑ j q_j = n} i^{∑ q_j} / ∏ (q_j! (j!)^{q_j}) ∏ (Θ^{(j)})^{q_j}`
(`q i` is the multiplicity of `Θ^{(i+1)}`; each `q_j ≤ n`). -/
theorem c03_exp_jet_coefficients (U : Set ℝ) (hU : IsOpen U) (Θ : ℝ → ℝ)
    (hΘ : ContDiffOn ℝ (⊤ : ℕ∞) Θ U) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x ∈ U, c03c_expJet Θ n x = (n.factorial : ℂ) *
      ∑ q ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).filter
          (fun q => ∑ i, (i.val + 1) * q i = n),
        Complex.I ^ (∑ i, q i) / ((∏ i, (q i).factorial * (i.val + 1).factorial ^ q i : ℕ) : ℂ) *
          ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ q i := by
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 1 := ⟨n - 1, by omega⟩
  intro x hx
  exact c03c_aux_jet_formula hU hΘ M (M + 1) le_rfl x hx

/-! ## Proof of `c03_power_singularity_decay` -/

/-- One integration by parts against `e^{iyξ}` on an interval. -/
theorem c03c_aux_ibp_exp_interval {u u' : ℝ → ℂ} {c d y : ℝ} (hy : y ≠ 0)
    (hu : ∀ x ∈ uIcc c d, HasDerivAt u (u' x) x) (hu' : IntervalIntegrable u' volume c d) :
    ∫ x in c..d, u x * Complex.exp (Complex.I * y * x) =
      u d * (Complex.exp (Complex.I * y * d) / (Complex.I * y)) -
        u c * (Complex.exp (Complex.I * y * c) / (Complex.I * y)) -
        (Complex.I * y)⁻¹ * ∫ x in c..d, u' x * Complex.exp (Complex.I * y * x) := by
  have hIy : Complex.I * (y : ℂ) ≠ 0 := by simp [hy]
  have hv : ∀ x ∈ uIcc c d, HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * y * x) / (Complex.I * y))
      (Complex.exp (Complex.I * y * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => Complex.I * y * (x : ℂ)) (Complex.I * y) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (Complex.I * (y : ℂ))
    have := (h1.cexp).div_const (Complex.I * y)
    convert this using 1
    rw [mul_div_assoc, div_self hIy, mul_one]
  have hcont : Continuous (fun x : ℝ => Complex.exp (Complex.I * y * x)) := by fun_prop
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' (hcont.intervalIntegrable _ _)]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  show u' x * (Complex.exp (Complex.I * y * x) / (Complex.I * y)) =
    (Complex.I * y)⁻¹ * (u' x * Complex.exp (Complex.I * y * x))
  rw [div_eq_mul_inv]; ring


theorem c03c_aux_norm_exp_div {y x : ℝ} (hy : y ≠ 0) :
    ‖Complex.exp (Complex.I * y * x) / (Complex.I * y)‖ = |y|⁻¹ := by
  rw [norm_div, show Complex.I * (y : ℂ) * (x : ℂ) = ((y * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, one_div]

/-- Far region `[1/|y|, 2]`: two integrations by parts. -/
theorem c03c_aux_far_right {p M y : ℝ} (hp : 0 < p) (hp1 : p < 1) (hM : 0 ≤ M) (hy : 1 ≤ |y|)
    {b b1 b2 : ℝ → ℂ} (hd1 : ∀ x, 0 < x → HasDerivAt b (b1 x) x)
    (hd2 : ∀ x, 0 < x → HasDerivAt b1 (b2 x) x) (hb2c : ContinuousOn b2 (Ioi 0))
    (hb2 : b 2 = 0) (hb12 : b1 2 = 0)
    (B0 : ∀ x, 0 < x → x ≤ 2 → ‖b x‖ ≤ M * x ^ p)
    (B1 : ∀ x, 0 < x → x ≤ 2 → ‖b1 x‖ ≤ M * x ^ (p - 1))
    (B2 : ∀ x, 0 < x → x ≤ 2 → ‖b2 x‖ ≤ M * x ^ (p - 2)) :
    ‖∫ x in (1 / |y|)..2, b x * Complex.exp (Complex.I * y * x)‖ ≤
      (2 + 1 / (1 - p)) * M * |y| ^ (-1 - p) := by
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; linarith
  have hyp : 0 < |y| := abs_pos.mpr hy0
  set δ := 1 / |y| with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hyp]; exact hy
  have hsub : uIcc δ 2 ⊆ Ioi 0 := by
    rw [uIcc_of_le (by linarith)]; intro x hx; exact lt_of_lt_of_le hδ0 hx.1
  have hb1c : ContinuousOn b1 (uIcc δ 2) := fun x hx => (hd2 x (hsub hx)).continuousAt.continuousWithinAt
  have hb2c' : ContinuousOn b2 (uIcc δ 2) := hb2c.mono hsub
  have e1 := c03c_aux_ibp_exp_interval hy0 (fun x hx => hd1 x (hsub hx)) hb1c.intervalIntegrable
  have e2 := c03c_aux_ibp_exp_interval hy0 (fun x hx => hd2 x (hsub hx)) hb2c'.intervalIntegrable
  rw [e1, e2, hb2, hb12]; simp only [zero_mul, zero_sub]
  have hI2 : ‖∫ x in δ..2, b2 x * Complex.exp (Complex.I * y * x)‖ ≤ M * δ ^ (p - 1) / (1 - p) := by
    have hle : ∀ x ∈ Ioc δ 2, ‖b2 x * Complex.exp (Complex.I * y * x)‖ ≤ M * x ^ (p - 2) := by
      intro x hx
      have h1 : ‖Complex.exp (Complex.I * y * x)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [norm_mul, h1, mul_one]
      exact B2 x (lt_of_lt_of_le hδ0 hx.1.le) hx.2
    refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun x hx => hle x hx) ?_).trans ?_
    · exact (ContinuousOn.intervalIntegrable (fun x hx => ((continuousAt_const.mul
        ((continuousAt_id.rpow_const (Or.inl (hsub hx).ne'))))).continuousWithinAt))
    · rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1]⟩)]
      have h2 : (2 : ℝ) ^ (p - 2 + 1) ≥ 0 := by positivity
      have h3 : p - 2 + 1 = p - 1 := by ring
      rw [h3]
      have : (2 ^ (p - 1) - δ ^ (p - 1)) / (p - 1) = (δ ^ (p - 1) - 2 ^ (p - 1)) / (1 - p) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]; ring
      rw [this, mul_div_assoc]
      have : (0 : ℝ) ≤ 2 ^ (p - 1) := by positivity
      gcongr
      linarith
  have hb0 := B0 δ hδ0 (by linarith)
  have hb1 := B1 δ hδ0 (by linarith)
  have hnI : ‖(Complex.I * (y : ℂ))⁻¹‖ = |y|⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hE := c03c_aux_norm_exp_div (x := δ) hy0
  calc ‖-(b δ * (Complex.exp (Complex.I * y * δ) / (Complex.I * y))) - (Complex.I * y)⁻¹ *
        (-(b1 δ * (Complex.exp (Complex.I * y * δ) / (Complex.I * y))) -
          (Complex.I * y)⁻¹ * ∫ x in δ..2, b2 x * Complex.exp (Complex.I * y * x))‖
      ≤ ‖b δ‖ * |y|⁻¹ + |y|⁻¹ * (‖b1 δ‖ * |y|⁻¹ + |y|⁻¹ * (M * δ ^ (p - 1) / (1 - p))) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, hE, norm_mul, hnI]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, hE, norm_mul, hnI]
        gcongr
    _ ≤ M * δ ^ p * δ + δ * (M * δ ^ (p - 1) * δ + δ * (M * δ ^ (p - 1) / (1 - p))) := by
        rw [show |y|⁻¹ = δ by rw [hδ, one_div]]
        gcongr
    _ = (2 + 1 / (1 - p)) * M * (δ ^ p * δ) := by
        rw [Real.rpow_sub_one hδ0.ne']
        have h1p : (1 - p) ≠ 0 := by linarith
        field_simp
        ring
    _ = (2 + 1 / (1 - p)) * M * |y| ^ (-1 - p) := by
        rw [← Real.rpow_add_one hδ0.ne', hδ, one_div |y|, Real.inv_rpow hyp.le, ← Real.rpow_neg hyp.le]
        congr 2; ring


theorem c03c_aux_iterC_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ} {N : ℕ}
    (hf : ContDiffOn ℝ N f U) {m : ℕ} (hm : m < N) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
  have h1 : DifferentiableOn ℝ (iteratedDerivWithin m f U) U :=
    hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hm) hU.uniqueDiffOn
  have heq : iteratedDerivWithin m f U =ᶠ[𝓝 x] iteratedDeriv m f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact iteratedDerivWithin_of_isOpen hU hy
  have h2 : DifferentiableAt ℝ (iteratedDeriv m f) x :=
    ((h1 x hx).differentiableAt (hU.mem_nhds hx)).congr_of_eventuallyEq heq.symm
  rw [iteratedDeriv_succ]
  exact h2.hasDerivAt

theorem c03c_aux_iterC_continuousOn {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ} {N : ℕ}
    (hf : ContDiffOn ℝ N f U) : ContinuousOn (iteratedDeriv N f) U := by
  have h1 : ContinuousOn (iteratedDerivWithin N f U) U :=
    hf.continuousOn_iteratedDerivWithin le_rfl hU.uniqueDiffOn
  exact h1.congr fun y hy => (iteratedDerivWithin_of_isOpen hU hy).symm

/-- Core decay estimate for `b = a^{(n-1)}`. -/
theorem c03c_aux_decay_core {p M y : ℝ} (hp : 0 < p) (hp1 : p < 1) (hM : 0 ≤ M) (hy : 1 ≤ |y|)
    {b b1 b2 : ℝ → ℂ} (hbc : Continuous b) (hbs : ∀ x, 2 < |x| → b x = 0)
    (hd1 : ∀ x, x ≠ 0 → HasDerivAt b (b1 x) x)
    (hd2 : ∀ x, x ≠ 0 → HasDerivAt b1 (b2 x) x) (hb2c : ContinuousOn b2 {0}ᶜ)
    (B0 : ∀ x, 0 < |x| → |x| ≤ 2 → ‖b x‖ ≤ M * |x| ^ p)
    (B1 : ∀ x, 0 < |x| → |x| ≤ 2 → ‖b1 x‖ ≤ M * |x| ^ (p - 1))
    (B2 : ∀ x, 0 < |x| → |x| ≤ 2 → ‖b2 x‖ ≤ M * |x| ^ (p - 2)) :
    ‖∫ x, b x * Complex.exp (Complex.I * y * x)‖ ≤
      (2 * (2 + 1 / (1 - p)) + 2) * M * |y| ^ (-1 - p) := by
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; linarith
  have hyp : 0 < |y| := abs_pos.mpr hy0
  set δ := 1 / |y| with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hyp]; exact hy
  -- b and b1 vanish beyond 2
  have hzero_out : ∀ x, 2 < |x| → b =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    have : {z : ℝ | 2 < |z|} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_abs).mem_nhds hx
    filter_upwards [this] with z hz
    exact hbs z hz
  have hb1_out : ∀ x, 2 < |x| → b1 x = 0 := by
    intro x hx
    have hx0 : x ≠ 0 := by intro h; rw [h, abs_zero] at hx; linarith
    have h1 := hd1 x hx0
    have h2 : HasDerivAt b 0 x := (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq (hzero_out x hx)
    exact h1.unique h2
  have hlim : ∀ (f : ℝ → ℂ) (s : ℝ), ContinuousAt f s → (∀ x, 2 < |x| → f x = 0) → |s| = 2 →
      f s = 0 := by
    intro f s hf hz hs
    have h1 : Tendsto f (𝓝[{x | 2 < |x|}] s) (𝓝 (f s)) := hf.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto f (𝓝[{x | 2 < |x|}] s) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hz x hx).symm)
    have : (𝓝[{x | 2 < |x|}] s).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot]
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 2) |>.mp hs with h | h
      · rw [h]
        have : Ioi (2 : ℝ) ⊆ {x | 2 < |x|} := fun x hx => by
          simp only [mem_ofPred_eq]; rw [abs_of_pos (by linarith [mem_Ioi.mp hx])]; exact hx
        exact closure_mono this (by rw [closure_Ioi]; simp)
      · rw [h]
        have : Iio (-2 : ℝ) ⊆ {x | 2 < |x|} := fun x hx => by
          simp only [mem_ofPred_eq]; rw [abs_of_neg (by linarith [mem_Iio.mp hx])]; linarith [mem_Iio.mp hx]
        exact closure_mono this (by rw [closure_Iio]; simp)
    exact tendsto_nhds_unique h1 h2
  have hb2 : b 2 = 0 := hlim b 2 hbc.continuousAt hbs (by norm_num)
  have hbm2 : b (-2) = 0 := hlim b (-2) hbc.continuousAt hbs (by norm_num)
  have hb12 : b1 2 = 0 := hlim b1 2 (hd2 2 (by norm_num)).continuousAt hb1_out (by norm_num)
  have hb1m2 : b1 (-2) = 0 := hlim b1 (-2) (hd2 (-2) (by norm_num)).continuousAt hb1_out (by norm_num)
  set F : ℝ → ℂ := fun x => b x * Complex.exp (Complex.I * y * x) with hF
  have hFc : Continuous F := hbc.mul (by fun_prop)
  have hFint : ∀ c d : ℝ, IntervalIntegrable F volume c d := fun c d => hFc.intervalIntegrable c d
  -- reduce to [-2, 2]
  have hfull : ∫ x, F x = ∫ x in (-2 : ℝ)..2, F x := by
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have : 2 < |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [hF, hbs x this]
  rw [hfull, ← intervalIntegral.integral_add_adjacent_intervals (hFint (-2) (-δ)) (hFint (-δ) 2),
    ← intervalIntegral.integral_add_adjacent_intervals (hFint (-δ) δ) (hFint δ 2)]
  -- right piece
  have hR := c03c_aux_far_right hp hp1 hM hy (b := b) (b1 := b1) (b2 := b2)
    (fun x hx => hd1 x hx.ne') (fun x hx => hd2 x hx.ne')
    (hb2c.mono fun x hx => (mem_Ioi.mp hx).ne') hb2 hb12
    (fun x hx h2 => by have := B0 x (by rwa [abs_of_pos hx]) (by rwa [abs_of_pos hx]); rwa [abs_of_pos hx] at this)
    (fun x hx h2 => by have := B1 x (by rwa [abs_of_pos hx]) (by rwa [abs_of_pos hx]); rwa [abs_of_pos hx] at this)
    (fun x hx h2 => by have := B2 x (by rwa [abs_of_pos hx]) (by rwa [abs_of_pos hx]); rwa [abs_of_pos hx] at this)
  -- left piece
  have hyn : 1 ≤ |-y| := by rwa [abs_neg]
  have hL := c03c_aux_far_right hp hp1 hM hyn (b := fun x => b (-x)) (b1 := fun x => -b1 (-x))
    (b2 := fun x => b2 (-x))
    (fun x hx => by
      have hx' : -x ≠ 0 := by linarith
      have := HasDerivAt.scomp x (hd1 (-x) hx') (hasDerivAt_neg x)
      exact this.congr_deriv (by simp))
    (fun x hx => by
      have hx' : -x ≠ 0 := by linarith
      have := (HasDerivAt.scomp x (hd2 (-x) hx') (hasDerivAt_neg x)).neg
      exact this.congr_deriv (by simp))
    (by
      refine hb2c.comp continuous_neg.continuousOn ?_
      intro x hx; simp only [mem_compl_iff, mem_singleton_iff, neg_eq_zero]; exact (mem_Ioi.mp hx).ne')
    (by simpa using hbm2) (by simp [hb1m2])
    (fun x hx h2 => by
      have := B0 (-x) (by rw [abs_neg, abs_of_pos hx]; exact hx) (by rw [abs_neg, abs_of_pos hx]; exact h2)
      rwa [abs_neg, abs_of_pos hx] at this)
    (fun x hx h2 => by
      have := B1 (-x) (by rw [abs_neg, abs_of_pos hx]; exact hx) (by rw [abs_neg, abs_of_pos hx]; exact h2)
      rw [abs_neg, abs_of_pos hx] at this; simpa using this)
    (fun x hx h2 => by
      have := B2 (-x) (by rw [abs_neg, abs_of_pos hx]; exact hx) (by rw [abs_neg, abs_of_pos hx]; exact h2)
      rwa [abs_neg, abs_of_pos hx] at this)
  rw [abs_neg] at hL
  have hLeq : ∫ x in (-2 : ℝ)..(-δ), F x =
      ∫ x in (1 / |y|)..2, b (-x) * Complex.exp (Complex.I * ((-y : ℝ) : ℂ) * x) := by
    rw [← hδ]
    have := intervalIntegral.integral_comp_neg (a := δ) (b := 2) F
    rw [← this]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hF]; push_cast; ring_nf
  -- middle piece
  have hmid : ‖∫ x in (-δ)..δ, F x‖ ≤ 2 * M * |y| ^ (-1 - p) := by
    obtain ⟨hii, hI⟩ := c03c_aux_abs_rpow_ii (s := p) (R := δ) (by linarith) hδ0.le
    have hb : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioc (-δ) δ → ‖F x‖ ≤ M * |x| ^ p := by
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx0 hx
      have h1 : ‖Complex.exp (Complex.I * y * x)‖ = 1 := by rw [Complex.norm_exp]; simp
      simp only [hF, norm_mul, h1, mul_one]
      exact B0 x (abs_pos.mpr hx0) (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
    refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) hb (hii.const_mul M)).trans ?_
    rw [intervalIntegral.integral_const_mul, hI]
    have hδp : δ ^ (p + 1) = |y| ^ (-1 - p) := by
      rw [hδ, one_div, Real.inv_rpow hyp.le, ← Real.rpow_neg hyp.le]; congr 1; ring
    rw [hδp]
    have : 0 ≤ |y| ^ (-1 - p) := by positivity
    have h1p : 1 ≤ p + 1 := by linarith
    calc M * (2 * (|y| ^ (-1 - p) / (p + 1))) = 2 * M * |y| ^ (-1 - p) / (p + 1) := by ring
      _ ≤ 2 * M * |y| ^ (-1 - p) := div_le_self (by positivity) h1p
  calc ‖(∫ x in (-2 : ℝ)..(-δ), F x) + ((∫ x in (-δ)..δ, F x) + ∫ x in δ..2, F x)‖
      ≤ ‖∫ x in (-2 : ℝ)..(-δ), F x‖ + (‖∫ x in (-δ)..δ, F x‖ + ‖∫ x in δ..2, F x‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (2 + 1 / (1 - p)) * M * |y| ^ (-1 - p) + (2 * M * |y| ^ (-1 - p) +
          (2 + 1 / (1 - p)) * M * |y| ^ (-1 - p)) := by
        gcongr
        rw [hLeq]; exact hL
    _ = _ := by ring


/-- `m` integrations by parts against `e^{iyx}`. -/
theorem c03c_aux_fourier_ibp {f : ℝ → ℂ} (m : ℕ) (hf : ContDiff ℝ m f) (hcs : HasCompactSupport f)
    {y : ℝ} (hy : y ≠ 0) :
    ∫ x, f x * Complex.exp (Complex.I * y * x) =
      (-1 : ℂ) ^ m * ∫ x, iteratedDeriv m f x / (Complex.I * y) ^ m *
        Complex.exp (Complex.I * y * x) := by
  have hφ : ContDiffOn ℝ (m + 1 : ℕ) (fun x : ℝ => y * x) univ :=
    (contDiff_const.mul contDiff_id).contDiffOn
  have hd : ∀ t : ℝ, deriv (fun x : ℝ => y * x) t = y := fun t => by simp
  obtain ⟨-, -, hI, -⟩ := c03_ibp_compact_iteration univ isOpen_univ m (fun x => y * x) hφ
    (fun t _ => by rw [hd]; exact hy) f hf hcs (subset_univ _)
  have hL : ∀ k : ℕ, (c03c_ibpL univ (fun x => y * x))^[k] f =
      fun x => iteratedDeriv k f x / (Complex.I * y) ^ k := by
    intro k
    induction k with
    | zero => funext x; simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x
      simp only [c03c_ibpL, mem_univ, if_true, hd]
      rw [deriv_div_const, deriv_div_const, iteratedDeriv_succ, pow_succ, div_div]
  have he : ∀ x : ℝ, Complex.exp (Complex.I * (((fun x : ℝ => y * x) x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * y * x) := fun x => by push_cast; ring_nf
  simp only [he, hL] at hI
  exact hI

/-- Blueprint: lem:c03_power_singularity_decay.  If `supp a ⊆ [-2,2]`, `a ∈ C^{n-1}`,
`a ∈ C^{n+1}(ℝ∖0)`, `∂^l a(0) = 0` (`l ≤ n-1`) and `|∂^l a(ξ)| ≤ M|ξ|^{n-1+p-l}`, then
`|ǎ(y)| ≤ C M |y|^{-n-p}` for `|y| ≥ 1` and `|ǎ| ≤ C M`, with `C = C(n,p)`. -/
theorem c03c_c03_power_singularity_decay (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C, 0 < C ∧ ∀ M : ℝ, 0 ≤ M → ∀ a : ℝ → ℂ, (∀ ξ, 2 < |ξ| → a ξ = 0) →
      ContDiff ℝ (n - 1 : ℕ) a → ContDiffOn ℝ (n + 1 : ℕ) a {0}ᶜ →
      (∀ l < n, iteratedDeriv l a 0 = 0) →
      (∀ ξ, 0 < |ξ| → |ξ| ≤ 2 → ∀ l ≤ n + 1,
        ‖iteratedDeriv l a ξ‖ ≤ M * |ξ| ^ ((n : ℝ) - 1 + p - l)) →
      (∀ y, 1 ≤ |y| → ‖invFourierT a y‖ ≤ C * M * |y| ^ (-(n : ℝ) - p)) ∧
      ∀ y, ‖invFourierT a y‖ ≤ C * M := by
  set K : ℝ := 2 * (2 + 1 / (1 - p)) + 2 with hK
  have hK0 : 0 < K := by
    have : 0 < 1 / (1 - p) := by apply div_pos one_pos; linarith
    rw [hK]; linarith
  have hs : -1 < (n : ℝ) - 1 + p := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨hindI, hindV⟩ := c03c_aux_abs_rpow_ind hs (by norm_num : (0 : ℝ) ≤ 2)
  set S0 : ℝ := 2 * ((2 : ℝ) ^ ((n : ℝ) - 1 + p + 1) / ((n : ℝ) - 1 + p + 1)) with hS0
  have hS00 : 0 ≤ S0 := by
    have : 0 < (n : ℝ) - 1 + p + 1 := by linarith
    rw [hS0]; positivity
  have h2π : (0 : ℝ) < 2 * π := by positivity
  refine ⟨(2 * π)⁻¹ * (K + S0), by positivity, ?_⟩
  intro M hM a hsupp hc1 hc2 _hvan hbd
  have hac : Continuous a := hc1.continuous
  have hcs : HasCompactSupport a := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-2) 2) isCompact_Icc ?_
    intro x hx
    by_contra h
    apply hx
    apply hsupp
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hinv : ∀ y : ℝ, invFourierT a y = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ, a ξ * Complex.exp (Complex.I * y * ξ) := fun y => rfl
  have hnorm2π : ‖((2 * π : ℝ) : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2π]
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; linarith
    have hyp : 0 < |y| := abs_pos.mpr hy0
    rw [hinv, c03c_aux_fourier_ibp (n - 1) hc1 hcs hy0]
    have hopen : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
    have hn1 : n - 1 + 1 = n := by omega
    have hcore := c03c_aux_decay_core (y := y) hp hp1 hM hy
      (b := iteratedDeriv (n - 1) a) (b1 := iteratedDeriv n a) (b2 := iteratedDeriv (n + 1) a)
      (hc1.continuous_iteratedDeriv (n - 1) le_rfl)
      (fun x hx => by
        have : {z : ℝ | 2 < |z|} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_abs).mem_nhds hx
        have hev : a =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
          filter_upwards [this] with z hz using hsupp z hz
        rw [hev.iteratedDeriv_eq, iteratedDeriv_const]; simp)
      (fun x hx => by
        have := c03c_aux_iterC_hasDerivAt hopen hc2 (m := n - 1) (by omega) hx
        rwa [hn1] at this)
      (fun x hx => c03c_aux_iterC_hasDerivAt hopen hc2 (m := n) (by omega) hx)
      (c03c_aux_iterC_continuousOn hopen hc2)
      (fun x h0 h2 => by
        have := hbd x h0 h2 (n - 1) (by omega)
        rwa [show (n : ℝ) - 1 + p - ((n - 1 : ℕ) : ℝ) = p by
          rw [Nat.cast_sub hn]; push_cast; ring] at this)
      (fun x h0 h2 => by
        have := hbd x h0 h2 n (by omega)
        rwa [show (n : ℝ) - 1 + p - (n : ℝ) = p - 1 by ring] at this)
      (fun x h0 h2 => by
        have := hbd x h0 h2 (n + 1) le_rfl
        rwa [show (n : ℝ) - 1 + p - ((n + 1 : ℕ) : ℝ) = p - 2 by push_cast; ring] at this)
    have hIy : (Complex.I * (y : ℂ)) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by simp [hy0])
    have hrw : ∫ x, iteratedDeriv (n - 1) a x / (Complex.I * y) ^ (n - 1) *
        Complex.exp (Complex.I * y * x) =
        (∫ x, iteratedDeriv (n - 1) a x * Complex.exp (Complex.I * y * x)) /
          (Complex.I * y) ^ (n - 1) := by
      rw [← integral_div]; congr 1; funext x; ring
    rw [hrw, norm_mul, hnorm2π, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hpow : |y| ^ (-1 - p) / |y| ^ (n - 1) = |y| ^ (-(n : ℝ) - p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hyp, Nat.cast_sub hn]; congr 1; push_cast; ring
    calc (2 * π)⁻¹ * (‖∫ x, iteratedDeriv (n - 1) a x * Complex.exp (Complex.I * y * x)‖ /
          |y| ^ (n - 1))
        ≤ (2 * π)⁻¹ * (K * M * |y| ^ (-1 - p) / |y| ^ (n - 1)) := by
          gcongr
      _ = (2 * π)⁻¹ * K * M * |y| ^ (-(n : ℝ) - p) := by rw [← hpow]; ring
      _ ≤ (2 * π)⁻¹ * (K + S0) * M * |y| ^ (-(n : ℝ) - p) := by
          gcongr; linarith
  · rw [hinv, norm_mul, hnorm2π]
    have hb : ∀ᵐ ξ ∂(volume : Measure ℝ), ‖a ξ * Complex.exp (Complex.I * y * ξ)‖ ≤
        M * Set.indicator (Icc (-2) 2) (fun z : ℝ => |z| ^ ((n : ℝ) - 1 + p)) ξ := by
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with ξ hξ
      have h1 : ‖Complex.exp (Complex.I * y * ξ)‖ = 1 := by rw [Complex.norm_exp]; simp
      rw [norm_mul, h1, mul_one]
      by_cases hm : ξ ∈ Icc (-2 : ℝ) 2
      · rw [Set.indicator_of_mem hm]
        have := hbd ξ (abs_pos.mpr hξ) (abs_le.mpr hm) 0 (Nat.zero_le _)
        simpa using this
      · rw [Set.indicator_of_notMem hm, mul_zero, hsupp ξ (by
          rw [mem_Icc, not_and_or, not_le, not_le] at hm
          rcases hm with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith), norm_zero]
    have := norm_integral_le_of_norm_le (hindI.const_mul M) hb
    rw [integral_const_mul, hindV] at this
    calc (2 * π)⁻¹ * ‖∫ ξ, a ξ * Complex.exp (Complex.I * y * ξ)‖ ≤ (2 * π)⁻¹ * (M * S0) := by
          gcongr
      _ ≤ (2 * π)⁻¹ * (K + S0) * M := by
          have : 0 ≤ K * M := by positivity
          nlinarith [inv_pos.mpr h2π]

/-! ## Proof of `c03_nonsmooth_symbol_bounds` -/

/-- Piecewise power `cp ξ^e` (`ξ>0`), `cm (-ξ)^e` (`ξ<0`), `0` at `0`. -/
def c03c_aux_pw (cp cm : ℂ) (e : ℝ) (ξ : ℝ) : ℂ :=
  if 0 < ξ then cp * ((ξ ^ e : ℝ) : ℂ) else if ξ < 0 then cm * (((-ξ) ^ e : ℝ) : ℂ) else 0

theorem c03c_aux_pw_bound (cp cm : ℂ) (e : ℝ) (ξ : ℝ) :
    ‖c03c_aux_pw cp cm e ξ‖ ≤ (‖cp‖ + ‖cm‖) * |ξ| ^ e := by
  unfold c03c_aux_pw
  split_ifs with h1 h2
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h1.le _),
      abs_of_pos h1]
    have : 0 ≤ ‖cm‖ * ξ ^ e := by positivity
    nlinarith [norm_nonneg cp, Real.rpow_nonneg h1.le e]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_neg h2]
    have : 0 ≤ ‖cp‖ * (-ξ) ^ e := by have := Real.rpow_nonneg (show (0:ℝ) ≤ -ξ by linarith) e; positivity
    nlinarith [norm_nonneg cm]
  · simp only [norm_zero]; positivity

theorem c03c_aux_pw_local_pos (cp cm : ℂ) (e : ℝ) {ξ : ℝ} (h : 0 < ξ) :
    c03c_aux_pw cp cm e =ᶠ[𝓝 ξ] fun x => cp * ((x ^ e : ℝ) : ℂ) := by
  filter_upwards [Ioi_mem_nhds h] with x hx
  simp [c03c_aux_pw, mem_Ioi.mp hx]

theorem c03c_aux_pw_local_neg (cp cm : ℂ) (e : ℝ) {ξ : ℝ} (h : ξ < 0) :
    c03c_aux_pw cp cm e =ᶠ[𝓝 ξ] fun x => cm * (((-x) ^ e : ℝ) : ℂ) := by
  filter_upwards [Iio_mem_nhds h] with x hx
  have hx' : x < 0 := hx
  simp [c03c_aux_pw, hx', not_lt.mpr hx'.le]

theorem c03c_aux_pw_hasDerivAt (cp cm : ℂ) {e : ℝ} (he : 1 < e) (ξ : ℝ) :
    HasDerivAt (c03c_aux_pw cp cm e) (c03c_aux_pw (cp * e) (-(cm * e)) (e - 1) ξ) ξ := by
  rcases lt_trichotomy ξ 0 with h | h | h
  · have h1 : HasDerivAt (fun x : ℝ => (-x) ^ e) ((-1) * e * (-ξ) ^ (e - 1)) ξ :=
      (hasDerivAt_neg ξ).rpow_const (Or.inl (by linarith))
    have h2 := (h1.ofReal_comp).const_mul cm
    refine (h2.congr_of_eventuallyEq (c03c_aux_pw_local_neg cp cm e h)).congr_deriv ?_
    simp [c03c_aux_pw, h, not_lt.mpr h.le]
    ring
  · subst h
    rw [hasDerivAt_iff_tendsto_slope]
    have hval : c03c_aux_pw (cp * e) (-(cm * e)) (e - 1) 0 = 0 := by simp [c03c_aux_pw]
    rw [hval]
    have hz : c03c_aux_pw cp cm e 0 = 0 := by simp [c03c_aux_pw]
    refine squeeze_zero_norm' (a := fun x => (‖cp‖ + ‖cm‖) * |x| ^ (e - 1)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [slope_def_module, hz, sub_zero, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs]
      have hx0 : 0 < |x| := abs_pos.mpr hx
      rw [inv_mul_le_iff₀ hx0]
      refine (c03c_aux_pw_bound cp cm e x).trans (le_of_eq ?_)
      have : |x| ^ e = |x| * |x| ^ (e - 1) := by
        rw [← Real.rpow_one_add' hx0.le (by linarith)]; ring_nf
      rw [this]; ring
    · have : Tendsto (fun x : ℝ => (‖cp‖ + ‖cm‖) * |x| ^ (e - 1)) (𝓝 0) (𝓝 0) := by
        have hc : ContinuousAt (fun x : ℝ => (‖cp‖ + ‖cm‖) * |x| ^ (e - 1)) 0 :=
          continuousAt_const.mul ((continuous_abs.continuousAt).rpow_const (Or.inr (by linarith)))
        simpa [Real.zero_rpow (show e - 1 ≠ 0 by linarith)] using hc.tendsto
      exact this.mono_left nhdsWithin_le_nhds
  · have h1 : HasDerivAt (fun x : ℝ => x ^ e) (e * ξ ^ (e - 1)) ξ :=
      Real.hasDerivAt_rpow_const (Or.inl h.ne')
    have h2 := (h1.ofReal_comp).const_mul cp
    refine (h2.congr_of_eventuallyEq (c03c_aux_pw_local_pos cp cm e h)).congr_deriv ?_
    simp [c03c_aux_pw, h]
    ring


theorem c03c_aux_pw_continuous (cp cm : ℂ) {e : ℝ} (he : 0 < e) : Continuous (c03c_aux_pw cp cm e) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  rcases lt_trichotomy ξ 0 with h | h | h
  · refine ContinuousAt.congr ?_ (c03c_aux_pw_local_neg cp cm e h).symm
    exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      ((continuous_neg.continuousAt).rpow_const (Or.inl (by linarith))))
  · subst h
    have hz : c03c_aux_pw cp cm e 0 = 0 := by simp [c03c_aux_pw]
    rw [ContinuousAt, hz]
    refine squeeze_zero_norm (fun x => c03c_aux_pw_bound cp cm e x) ?_
    have hc : ContinuousAt (fun x : ℝ => (‖cp‖ + ‖cm‖) * |x| ^ e) 0 :=
      continuousAt_const.mul ((continuous_abs.continuousAt).rpow_const (Or.inr he.le))
    simpa [Real.zero_rpow he.ne'] using hc.tendsto
  · refine ContinuousAt.congr ?_ (c03c_aux_pw_local_pos cp cm e h).symm
    exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      ((continuous_id.continuousAt).rpow_const (Or.inl h.ne')))

theorem c03c_aux_pw_deriv (cp cm : ℂ) {e : ℝ} (he : 1 < e) :
    deriv (c03c_aux_pw cp cm e) = c03c_aux_pw (cp * e) (-(cm * e)) (e - 1) := by
  funext ξ; exact (c03c_aux_pw_hasDerivAt cp cm he ξ).deriv

theorem c03c_aux_pw_contDiff (n : ℕ) : ∀ (cp cm : ℂ) (e : ℝ), (n : ℝ) < e →
    ContDiff ℝ n (c03c_aux_pw cp cm e) := by
  induction n with
  | zero =>
    intro cp cm e he
    rw [Nat.cast_zero, contDiff_zero]
    exact c03c_aux_pw_continuous cp cm (by simpa using he)
  | succ n ih =>
    intro cp cm e he
    have he1 : 1 < e := by push_cast at he; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun ξ => (c03c_aux_pw_hasDerivAt cp cm he1 ξ).differentiableAt, by simp, ?_⟩
    rw [c03c_aux_pw_deriv cp cm he1]
    exact ih _ _ _ (by push_cast at he; linarith)

theorem c03c_aux_pw_iteratedDeriv (l : ℕ) : ∀ (cp cm : ℂ) (e : ℝ), (l : ℝ) < e →
    ∃ c d : ℂ, iteratedDeriv l (c03c_aux_pw cp cm e) = c03c_aux_pw c d (e - l) := by
  induction l with
  | zero => intro cp cm e _; exact ⟨cp, cm, by simp⟩
  | succ l ih =>
    intro cp cm e he
    have he1 : 1 < e := by push_cast at he; linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
    rw [iteratedDeriv_succ', c03c_aux_pw_deriv cp cm he1]
    obtain ⟨c, d, h⟩ := ih (cp * e) (-(cm * e)) (e - 1) (by push_cast at he; linarith)
    exact ⟨c, d, by rw [h]; congr 1; push_cast; ring⟩

theorem c03c_aux_pw_iteratedDeriv_zero (l : ℕ) (cp cm : ℂ) (e : ℝ) (he : (l : ℝ) < e) :
    iteratedDeriv l (c03c_aux_pw cp cm e) 0 = 0 := by
  obtain ⟨c, d, h⟩ := c03c_aux_pw_iteratedDeriv l cp cm e he
  rw [h]; simp [c03c_aux_pw]

theorem c03c_aux_pw_deriv_bound (cp cm : ℂ) (e : ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) (l : ℕ) :
    ‖iteratedDeriv l (c03c_aux_pw cp cm e) ξ‖ ≤
      (‖cp‖ + ‖cm‖) * |(descPochhammer ℝ l).eval e| * |ξ| ^ (e - l) := by
  rcases lt_or_gt_of_ne hξ with h | h
  · rw [(c03c_aux_pw_local_neg cp cm e h).iteratedDeriv_eq, iteratedDeriv_const_mul_field]
    have hc : ContDiffAt ℝ l (fun x : ℝ => (-x) ^ e) ξ :=
      (Real.contDiffAt_rpow_const_of_ne (by linarith : -ξ ≠ 0)).comp ξ contDiff_neg.contDiffAt
    rw [c03c_aux_iteratedDeriv_ofReal (fun x : ℝ => (-x) ^ e) ξ l hc]
    have hn := iteratedDeriv_comp_neg l (fun y : ℝ => y ^ e) ξ
    rw [hn, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_neg h, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have : 0 ≤ |(descPochhammer ℝ l).eval e| * (-ξ) ^ (e - l) := by
      have := Real.rpow_nonneg (show (0:ℝ) ≤ -ξ by linarith) (e - l); positivity
    nlinarith [norm_nonneg cp]
  · rw [(c03c_aux_pw_local_pos cp cm e h).iteratedDeriv_eq, iteratedDeriv_const_mul_field]
    have hc : ContDiffAt ℝ l (fun x : ℝ => x ^ e) ξ := Real.contDiffAt_rpow_const_of_ne h.ne'
    rw [c03c_aux_iteratedDeriv_ofReal (fun x : ℝ => x ^ e) ξ l hc, iteratedDeriv_eq_iterate,
      Real.iter_deriv_rpow_const, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos h, abs_of_nonneg (Real.rpow_nonneg h.le _)]
    have : 0 ≤ |(descPochhammer ℝ l).eval e| * ξ ^ (e - l) := by
      have := Real.rpow_nonneg h.le (e - l); positivity
    nlinarith [norm_nonneg cm]


theorem c03c_aux_descPoch_le {e : ℝ} (he : 0 ≤ e) (l : ℕ) :
    |(descPochhammer ℝ l).eval e| ≤ (e + l) ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [descPochhammer_succ_eval, abs_mul, pow_succ]
    have h1 : (e + l) ^ l ≤ (e + (l + 1 : ℕ)) ^ l := by
      apply pow_le_pow_left₀ (by positivity); push_cast; linarith
    have h2 : |e - l| ≤ e + (l + 1 : ℕ) := by
      rw [abs_le]; push_cast; constructor <;> linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
    calc |(descPochhammer ℝ l).eval e| * |e - l| ≤ (e + l) ^ l * (e + (l + 1 : ℕ)) := by
          gcongr
      _ ≤ (e + (l + 1 : ℕ)) ^ l * (e + (l + 1 : ℕ)) := by gcongr

/-- `ξ^j Φ₀(ξ)^k = sgn^{j+k} |ξ|^{j+(p+1)k}/(p+1)^k`. -/
theorem c03c_aux_phi0_pow (p : ℝ) (hp : 0 < p) (j k : ℕ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ξ ^ j * Phi0 p ξ ^ k =
      (if 0 < ξ then 1 else (-1) ^ (j + k)) * |ξ| ^ ((j : ℝ) + (p + 1) * k) / (p + 1) ^ k := by
  have hξa : 0 < |ξ| := abs_pos.mpr hξ
  have hsplit : |ξ| ^ ((j : ℝ) + (p + 1) * k) = |ξ| ^ j * (|ξ| * |ξ| ^ p) ^ k := by
    rw [Real.rpow_add hξa, Real.rpow_natCast, ← Real.rpow_one_add' hξa.le (by linarith),
      ← Real.rpow_natCast (|ξ| ^ (1 + p)) k, ← Real.rpow_mul hξa.le]
    congr 2; ring
  rw [hsplit, Phi0]
  split_ifs with h
  · rw [abs_of_pos h]; ring
  · have hneg : ξ < 0 := lt_of_le_of_ne (not_lt.mp h) hξ
    obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ ξ = -s := ⟨-ξ, by linarith, by ring⟩
    rw [abs_neg, abs_of_pos hs, show -s * s ^ p = -(s * s ^ p) by ring, neg_div, neg_pow s,
      neg_pow (s * s ^ p / (p + 1)), div_pow, pow_add]
    ring


/-- The non-smooth factor `h(ξ) = (iξ)^j Φ₀(ξ)^k` as a piecewise power. -/
theorem c03c_aux_akj_eq (p : ℝ) (hp : 0 < p) (χ : ℝ → ℝ) (k j : ℕ) (hk : 1 ≤ k) :
    c03_symbol_akj p χ k j = fun ξ => (χ ξ : ℂ) *
      c03c_aux_pw (Complex.I ^ j / ((p + 1 : ℝ) : ℂ) ^ k)
        (Complex.I ^ j * (-1) ^ (j + k) / ((p + 1 : ℝ) : ℂ) ^ k) ((j : ℝ) + (p + 1) * k) ξ := by
  funext ξ
  rw [c03_symbol_akj]
  by_cases hξ : ξ = 0
  · subst hξ
    have : Phi0 p 0 = 0 := by simp [Phi0]
    simp [this, c03c_aux_pw, zero_pow (by omega : k ≠ 0)]
  · have hr := c03c_aux_phi0_pow p hp j k hξ
    have hpk : ((p + 1 : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by linarith : p + 1 ≠ 0))
    have key : (Complex.I * ξ) ^ j * ((Phi0 p ξ : ℝ) : ℂ) ^ k =
        Complex.I ^ j * (((ξ ^ j * Phi0 p ξ ^ k : ℝ)) : ℂ) := by push_cast; ring
    rcases lt_or_gt_of_ne hξ with h | h
    · rw [if_neg (not_lt.mpr h.le)] at hr
      have hne : ¬ (0 < ξ) := not_lt.mpr h.le
      simp only [c03c_aux_pw, hne, h, if_false, if_true]
      rw [mul_comm ((Complex.I * ξ) ^ j), mul_assoc, key, hr, abs_of_neg h]
      push_cast; field_simp
    · rw [if_pos h] at hr
      simp only [c03c_aux_pw, h, if_true]
      rw [mul_comm ((Complex.I * ξ) ^ j), mul_assoc, key, hr, abs_of_pos h]
      push_cast; field_simp

/-- Blueprint: lem:c03_nonsmooth_symbol_bounds.  Regularity, support, vanishing at `0` and the
bounds `|∂^l a_{k,j}(ξ)| ≤ C₁ C^k |ξ|^{p+1+j-l}` (`C = C(p)`, `C₁ = C₁(p,χ)`). -/
theorem c03c_c03_nonsmooth_symbol_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → (∀ ξ, 2 < |ξ| → χ ξ = 0) →
      (∀ ξ ∈ Icc (-1) 1, χ ξ = 1) → ∃ C₁, 0 < C₁ ∧ ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j ≤ 2 →
      ContDiff ℝ (j + 1 : ℕ) (c03_symbol_akj p χ k j) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c03_symbol_akj p χ k j) {0}ᶜ ∧
      (∀ ξ, 2 < |ξ| → c03_symbol_akj p χ k j ξ = 0) ∧
      (∀ l ≤ j + 1, iteratedDeriv l (c03_symbol_akj p χ k j) 0 = 0) ∧
      ∀ ξ, 0 < |ξ| → |ξ| ≤ 2 → ∀ l ≤ j + 3,
        ‖iteratedDeriv l (c03_symbol_akj p χ k j) ξ‖ ≤ C₁ * C ^ k * |ξ| ^ (p + 1 + j - l) := by
  refine ⟨128, by norm_num, ?_⟩
  intro χ hχ hχs hχ1
  have hcs : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-2) 2) isCompact_Icc ?_
    intro x hx
    by_contra h
    apply hx
    apply hχs
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  choose Mi hMi0 hMi using fun i => c03c_aux_iteratedDeriv_bdd hχ hcs i
  set Mχ := ∑ i ∈ Finset.range 6, Mi i with hMχ
  have hMχ0 : 0 ≤ Mχ := Finset.sum_nonneg fun i _ => hMi0 i
  have hMle : ∀ i ≤ 5, Mi i ≤ Mχ := fun i hi =>
    Finset.single_le_sum (f := Mi) (fun i _ => hMi0 i) (Finset.mem_range.mpr (by omega))
  refine ⟨2 * 3 ^ 5 * 7 ^ 5 * (Mχ + 1), by positivity, ?_⟩
  intro k hk j hj
  set e : ℝ := (j : ℝ) + (p + 1) * k with he
  set cp : ℂ := Complex.I ^ j / ((p + 1 : ℝ) : ℂ) ^ k
  set cm : ℂ := Complex.I ^ j * (-1) ^ (j + k) / ((p + 1 : ℝ) : ℂ) ^ k
  have hkey := c03c_aux_akj_eq p hp χ k j hk
  have hek : (j : ℝ) + 1 + p ≤ e := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [he]; nlinarith
  have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => (χ ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hhc : ContDiff ℝ (j + 1 : ℕ) (c03c_aux_pw cp cm e) :=
    c03c_aux_pw_contDiff (j + 1) cp cm e (by push_cast; linarith)
  have hloc : ∀ ξ : ℝ, ξ ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (c03c_aux_pw cp cm e) ξ := by
    intro ξ hξ
    rcases lt_or_gt_of_ne hξ with h | h
    · refine ContDiffAt.congr_of_eventuallyEq ?_ (c03c_aux_pw_local_neg cp cm e h)
      exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
        ((Real.contDiffAt_rpow_const_of_ne (by linarith : -ξ ≠ 0)).comp ξ contDiff_neg.contDiffAt))
    · refine ContDiffAt.congr_of_eventuallyEq ?_ (c03c_aux_pw_local_pos cp cm e h)
      exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
        (Real.contDiffAt_rpow_const_of_ne h.ne'))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hkey]; exact (hχc.of_le (c03c_aux_le_top _)).mul hhc
  · intro ξ hξ
    rw [hkey]
    exact ((hχc.contDiffAt).mul (hloc ξ hξ)).contDiffWithinAt
  · intro ξ hξ; simp [c03_symbol_akj, hχs ξ hξ]
  · intro l hl
    rw [hkey, iteratedDeriv_fun_mul (hχc.contDiffAt.of_le (c03c_aux_le_top l))
      (hhc.contDiffAt.of_le (by exact_mod_cast (by omega : l ≤ j + 1)))]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [c03c_aux_pw_iteratedDeriv_zero (l - i) cp cm e (by
      have : ((l - i : ℕ) : ℝ) ≤ j + 1 := by exact_mod_cast (by omega : l - i ≤ j + 1)
      linarith), mul_zero]
  · intro ξ hξ0 hξ2 l hl
    have hξ : ξ ≠ 0 := abs_pos.mp hξ0
    have hcpn : ‖cp‖ ≤ 1 := by
      simp only [cp, norm_div, norm_pow, Complex.norm_I, one_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < p + 1)]
      exact div_le_one_of_le₀ (one_le_pow₀ (by linarith)) (by positivity)
    have hcmn : ‖cm‖ ≤ 1 := by
      simp only [cm, norm_div, norm_mul, norm_pow, Complex.norm_I, one_pow, norm_neg, norm_one,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < p + 1)]
      exact div_le_one_of_le₀ (one_le_pow₀ (by linarith)) (by positivity)
    -- bound on χ
    have bχ : ∀ i ≤ j + 3, ‖iteratedDeriv i (fun ξ => (χ ξ : ℂ)) ξ‖ ≤
        (Mχ * 2 ^ i) * |ξ| ^ ((0 : ℝ) - i) := by
      intro i hi
      rw [c03c_aux_iteratedDeriv_ofReal _ _ _ (hχ.contDiffAt.of_le (c03c_aux_le_top i)),
        Complex.norm_real, Real.norm_eq_abs, zero_sub]
      have h1 : 1 ≤ 2 ^ i * |ξ| ^ (-(i : ℝ)) := by
        rw [Real.rpow_neg hξ0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
          one_mul]
        exact pow_le_pow_left₀ hξ0.le hξ2 i
      calc |iteratedDeriv i χ ξ| ≤ Mχ := (hMi i ξ).trans (hMle i (by omega))
        _ ≤ Mχ * (2 ^ i * |ξ| ^ (-(i : ℝ))) := le_mul_of_one_le_right hMχ0 h1
        _ = _ := by ring
    -- bound on h
    set G : ℝ := 2 * 7 ^ 5 * 128 ^ k with hG
    have bh : ∀ i ≤ j + 3, ‖iteratedDeriv i (c03c_aux_pw cp cm e) ξ‖ ≤
        G * |ξ| ^ ((p + 1 + j : ℝ) - i) := by
      intro i hi
      refine (c03c_aux_pw_deriv_bound cp cm e hξ i).trans ?_
      have he0 : 0 ≤ e := by linarith
      have hd : |(descPochhammer ℝ i).eval e| ≤ 7 ^ 5 * 32 ^ k := by
        refine (c03c_aux_descPoch_le he0 i).trans ?_
        have hk1 : (e + 5) ≤ 7 * 2 ^ k := by
          have h2k : (1 : ℝ) + k ≤ 2 ^ k := by
            have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) k
            norm_num at this; linarith
          have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
          rw [he]; nlinarith
        calc (e + i) ^ i ≤ (e + 5) ^ i := by
              gcongr; exact_mod_cast (by omega : i ≤ 5)
          _ ≤ (e + 5) ^ 5 := pow_le_pow_right₀ (by linarith) (by omega)
          _ ≤ (7 * 2 ^ k) ^ 5 := by gcongr
          _ = 7 ^ 5 * 32 ^ k := by rw [mul_pow, ← pow_mul, mul_comm k 5, pow_mul]; norm_num
      have hsplit : |ξ| ^ (e - i) = |ξ| ^ ((p + 1 + j : ℝ) - i) * |ξ| ^ ((p + 1) * ((k : ℝ) - 1)) := by
        rw [← Real.rpow_add hξ0]; congr 1; rw [he]; ring
      have hpow : |ξ| ^ ((p + 1) * ((k : ℝ) - 1)) ≤ 4 ^ k := by
        have hk1 : (0 : ℝ) ≤ (p + 1) * ((k : ℝ) - 1) := by
          have : (1 : ℝ) ≤ k := by exact_mod_cast hk
          nlinarith
        calc |ξ| ^ ((p + 1) * ((k : ℝ) - 1)) ≤ 2 ^ ((p + 1) * ((k : ℝ) - 1)) :=
              Real.rpow_le_rpow hξ0.le hξ2 hk1
          _ ≤ 2 ^ ((2 : ℝ) * k) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
          _ = 4 ^ k := by
              rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]; norm_num
      rw [hsplit]
      have hA : ‖cp‖ + ‖cm‖ ≤ 2 := by linarith
      have hB : 0 ≤ |ξ| ^ ((p + 1 + j : ℝ) - i) := by positivity
      calc (‖cp‖ + ‖cm‖) * |(descPochhammer ℝ i).eval e| *
            (|ξ| ^ ((p + 1 + j : ℝ) - i) * |ξ| ^ ((p + 1) * ((k : ℝ) - 1)))
          ≤ 2 * (7 ^ 5 * 32 ^ k) * (|ξ| ^ ((p + 1 + j : ℝ) - i) * 4 ^ k) := by
            gcongr
        _ = G * |ξ| ^ ((p + 1 + j : ℝ) - i) := by
            rw [hG, show (128 : ℝ) ^ k = 32 ^ k * 4 ^ k by rw [← mul_pow]; norm_num]; ring
    have hm := c03c_aux_symbol_mul hξ (j + 3) (hχc.contDiffAt.of_le (c03c_aux_le_top _))
      ((hloc ξ hξ).of_le (c03c_aux_le_top _)) (fun i => Mχ * 2 ^ i) (fun _ => G) 0
      (p + 1 + j) bχ bh l hl
    rw [hkey]
    refine hm.trans ?_
    have hsum : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (Mχ * 2 ^ i) * G =
        Mχ * G * 3 ^ l := by
      have := (add_pow (2 : ℝ) 1 l)
      rw [show (2 : ℝ) + 1 = 3 by norm_num] at this
      rw [this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by simp; ring
    rw [hsum, show (0 : ℝ) + (p + 1 + j) - l = p + 1 + j - l by ring]
    have h3 : (3 : ℝ) ^ l ≤ 3 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpos : 0 ≤ |ξ| ^ (p + 1 + j - l) := by positivity
    rw [hG]
    have : Mχ * (2 * 7 ^ 5 * 128 ^ k) * 3 ^ l ≤ 2 * 3 ^ 5 * 7 ^ 5 * (Mχ + 1) * 128 ^ k := by
      calc Mχ * (2 * 7 ^ 5 * 128 ^ k) * 3 ^ l = 2 * 7 ^ 5 * (Mχ * 128 ^ k * 3 ^ l) := by ring
        _ ≤ 2 * 7 ^ 5 * ((Mχ + 1) * 128 ^ k * 3 ^ 5) := by gcongr; linarith
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right this hpos

/-! ## Proof of `appendix_nonsmooth_fourier_inverse` -/

/-- `∂_y ǧ = ((iξ) g)^∨` for continuous compactly supported `g`. -/
theorem c03c_aux_invF_hasDerivAt {g : ℝ → ℂ} (hg : Continuous g) (hcs : HasCompactSupport g) (y : ℝ) :
    HasDerivAt (invFourierT g) (invFourierT (fun ξ => Complex.I * ξ * g ξ) y) y := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  have hbound_int : Integrable (fun ξ : ℝ => |ξ| * ‖g ξ‖) :=
    ((continuous_abs.mul hg.norm).integrable_of_hasCompactSupport
      (hcs.norm.mul_left))
  have hF : ∀ x : ℝ, AEStronglyMeasurable (fun ξ : ℝ => g ξ * Complex.exp (Complex.I * x * ξ)) :=
    fun x => (hg.mul (by fun_prop)).aestronglyMeasurable
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hcs
  have hF0 : Integrable (fun ξ : ℝ => g ξ * Complex.exp (Complex.I * y * ξ)) :=
    hgi.norm.mono' (hF y) (Eventually.of_forall fun ξ => by
      rw [norm_mul, Complex.norm_exp]; simp)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := y) (s := univ)
    (F := fun (x : ℝ) (ξ : ℝ) => g ξ * Complex.exp (Complex.I * (x : ℂ) * ξ))
    (F' := fun (x : ℝ) (ξ : ℝ) => g ξ * (Complex.I * ξ * Complex.exp (Complex.I * (x : ℂ) * ξ)))
    (bound := fun ξ => |ξ| * ‖g ξ‖) univ_mem (Eventually.of_forall hF) hF0
    ((hg.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun ξ x _ => by
      have h1 : ‖Complex.exp (Complex.I * (x : ℂ) * ξ)‖ = 1 := by rw [Complex.norm_exp]; simp
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, h1, mul_one, mul_comm])
    hbound_int
    (Eventually.of_forall fun ξ x _ => by
      have h1 : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ) * ξ) (Complex.I * ξ) x := by
        simpa using (((hasDerivAt_id x).ofReal_comp).const_mul Complex.I).mul_const (ξ : ℂ)
      have := (h1.cexp).const_mul (g ξ)
      convert this using 1; ring)
  have h2 := key.2.const_mul (((2 * π : ℝ) : ℂ)⁻¹)
  have e1 : invFourierT g = fun x : ℝ => ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ, g ξ * Complex.exp (Complex.I * (x : ℂ) * ξ) := rfl
  have e2 : invFourierT (fun ξ => Complex.I * ξ * g ξ) y = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, g ξ * (Complex.I * ξ * Complex.exp (Complex.I * (y : ℂ) * ξ)) := by
    show ((2 * π : ℝ) : ℂ)⁻¹ * _ = _
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only; ring
  rw [e1, e2]
  exact h2


theorem c03c_aux_invF_iter {g : ℝ → ℂ} (hg : Continuous g) (hcs : HasCompactSupport g) (j : ℕ) :
    iteratedDeriv j (invFourierT g) = invFourierT (fun ξ => (Complex.I * ξ) ^ j * g ξ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    have hgj : Continuous (fun ξ : ℝ => (Complex.I * ξ) ^ j * g ξ) := by fun_prop
    have hcj : HasCompactSupport (fun ξ : ℝ => (Complex.I * ξ) ^ j * g ξ) := hcs.mul_left
    funext y
    rw [(c03c_aux_invF_hasDerivAt hgj hcj y).deriv]
    congr 1
    funext ξ; ring

theorem c03c_aux_invF_smooth {g : ℝ → ℂ} (hg : Continuous g) (hcs : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ℕ∞) (invFourierT g) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [c03c_aux_invF_iter hg hcs m]
  have hgj : Continuous (fun ξ : ℝ => (Complex.I * ξ) ^ m * g ξ) := by fun_prop
  exact fun y => (c03c_aux_invF_hasDerivAt hgj hcs.mul_left y).differentiableAt


theorem c03c_aux_jb_combine {s A B y : ℝ} (hs0 : 0 ≤ s) (hs5 : s ≤ 5) (hB : 0 ≤ B)
    (h1 : 1 ≤ |y| → A ≤ B * |y| ^ (-s)) (h2 : A ≤ B) : A ≤ 32 * B * jb y ^ (-s) := by
  have hjb : 0 < jb y := Real.sqrt_pos.mpr (by positivity)
  have h32 : (2 : ℝ) ^ s ≤ 32 := by
    calc (2 : ℝ) ^ s ≤ 2 ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs5
      _ = 32 := by norm_num
  rw [Real.rpow_neg hjb.le]
  by_cases hy : 1 ≤ |y|
  · have hyp : 0 < |y| := by linarith
    have hj : jb y ≤ 2 * |y| := by
      rw [jb, Real.sqrt_le_left (by positivity)]
      nlinarith [sq_abs y]
    have hjs : jb y ^ s ≤ 2 ^ s * |y| ^ s := by
      rw [← Real.mul_rpow (by norm_num) hyp.le]
      exact Real.rpow_le_rpow hjb.le hj hs0
    refine (h1 hy).trans ?_
    rw [Real.rpow_neg hyp.le]
    have hys : 0 < |y| ^ s := Real.rpow_pos_of_pos hyp s
    have hjs0 : 0 < jb y ^ s := Real.rpow_pos_of_pos hjb s
    rw [show 32 * B * (jb y ^ s)⁻¹ = B * (32 * (jb y ^ s)⁻¹) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hys hjs0, one_mul]
    nlinarith
  · push Not at hy
    have hj : jb y ≤ 2 := by
      rw [jb, Real.sqrt_le_left (by norm_num)]
      nlinarith [sq_abs y, abs_nonneg y]
    have hjs : jb y ^ s ≤ 32 := (Real.rpow_le_rpow hjb.le hj hs0).trans h32
    have hjs0 : 0 < jb y ^ s := Real.rpow_pos_of_pos hjb s
    refine h2.trans ?_
    rw [show 32 * B * (jb y ^ s)⁻¹ = B * (32 * (jb y ^ s)⁻¹) by ring]
    refine le_mul_of_one_le_right hB ?_
    rw [← div_eq_mul_inv, le_div_iff₀ hjs0, one_mul]
    exact hjs


theorem c03c_aux_smooth_decay {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hcs : HasCompactSupport b) :
    ∃ A, 0 ≤ A ∧ ∀ y : ℝ, ‖invFourierT b y‖ ≤ A ∧
      (1 ≤ |y| → ‖invFourierT b y‖ ≤ A * |y| ^ (-(5 : ℝ))) := by
  have hb5 : Continuous (iteratedDeriv 5 b) := hb.continuous_iteratedDeriv 5 (c03c_aux_le_top 5)
  have hcs5 : HasCompactSupport (iteratedDeriv 5 b) := by
    rw [iteratedDeriv_eq_iterate]
    have : ∀ m, HasCompactSupport (deriv^[m] b) := by
      intro m; induction m with
      | zero => simpa using hcs
      | succ m ih => rw [Function.iterate_succ_apply']; exact ih.deriv
    exact this 5
  have hbi : Integrable b := hb.continuous.integrable_of_hasCompactSupport hcs
  have hb5i : Integrable (iteratedDeriv 5 b) := hb5.integrable_of_hasCompactSupport hcs5
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hnorm2π : ‖((2 * π : ℝ) : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2π]
  have i1 : 0 ≤ ∫ x, ‖b x‖ := integral_nonneg (fun x => norm_nonneg (b x))
  have i2 : 0 ≤ ∫ x, ‖iteratedDeriv 5 b x‖ := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨(2 * π)⁻¹ * ((∫ x, ‖b x‖) + ∫ x, ‖iteratedDeriv 5 b x‖),
    mul_nonneg (inv_nonneg.mpr h2π.le) (add_nonneg i1 i2), fun y => ⟨?_, fun hy => ?_⟩⟩
  · have hI : invFourierT b y = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, b ξ * Complex.exp (Complex.I * y * ξ) := rfl
    rw [hI, norm_mul, hnorm2π]
    have h1 : ‖∫ ξ, b ξ * Complex.exp (Complex.I * y * ξ)‖ ≤ ∫ ξ, ‖b ξ‖ :=
      norm_integral_le_of_norm_le hbi.norm (Eventually.of_forall fun ξ => by
        rw [norm_mul, Complex.norm_exp]; simp)
    gcongr
    linarith
  · have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; linarith
    have hyp : 0 < |y| := abs_pos.mpr hy0
    have hI : invFourierT b y = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, b ξ * Complex.exp (Complex.I * y * ξ) := rfl
    rw [hI, c03c_aux_fourier_ibp 5 (hb.of_le (c03c_aux_le_top 5)) hcs hy0, norm_mul, hnorm2π,
      norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h1 : ‖∫ x, iteratedDeriv 5 b x / (Complex.I * y) ^ 5 * Complex.exp (Complex.I * y * x)‖ ≤
        (∫ x, ‖iteratedDeriv 5 b x‖) * |y| ^ (-(5 : ℝ)) := by
      rw [← integral_mul_const]
      refine norm_integral_le_of_norm_le (hb5i.norm.mul_const _) (Eventually.of_forall fun x => ?_)
      have he : ‖Complex.exp (Complex.I * y * x)‖ = 1 := by rw [Complex.norm_exp]; simp
      rw [norm_mul, he, mul_one, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, Real.rpow_neg hyp.le,
        show (|y| : ℝ) ^ (5 : ℝ) = |y| ^ (5 : ℕ) by norm_cast, div_eq_mul_inv]
    have hp5 : 0 ≤ |y| ^ (-(5 : ℝ)) := by positivity
    calc (2 * π)⁻¹ * ‖∫ x, iteratedDeriv 5 b x / (Complex.I * y) ^ 5 * Complex.exp (Complex.I * y * x)‖
        ≤ (2 * π)⁻¹ * ((∫ x, ‖iteratedDeriv 5 b x‖) * |y| ^ (-(5 : ℝ))) := by gcongr
      _ ≤ (2 * π)⁻¹ * ((∫ x, ‖b x‖) + ∫ x, ‖iteratedDeriv 5 b x‖) * |y| ^ (-(5 : ℝ)) := by
        rw [mul_assoc]; gcongr; linarith

/-- Blueprint: prop:appendix_nonsmooth_fourier_inverse.  `m̌_k ∈ C^∞` and
`|∂^j m̌_k(y)| ≤ C₀ C^k ⟨y⟩^{-p-2-j}` for `j ≤ 2`, `k ≥ 0` (`C = C(p)`, `C₀ = C₀(p,χ)`). -/
theorem c03c_appendix_nonsmooth_fourier_inverse (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → (∀ ξ, 2 < |ξ| → χ ξ = 0) →
      (∀ ξ ∈ Icc (-1) 1, χ ξ = 1) → ∃ C₀, 0 < C₀ ∧ ∀ k : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (invFourierT (c03_symbol_mk p χ k)) ∧
      ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
        ‖iteratedDeriv j (invFourierT (c03_symbol_mk p χ k)) y‖ ≤
          C₀ * C ^ k * jb y ^ (-p - 2 - j) := by
  obtain ⟨C, hC, hNS⟩ := c03c_c03_nonsmooth_symbol_bounds p hp hp1
  choose Cps hCps hPS using fun n : ℕ => c03c_c03_power_singularity_decay p hp hp1 (n + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro χ hχ hχs hχ1
  obtain ⟨C₁, hC₁, hb⟩ := hNS χ hχ hχs hχ1
  have hcs : HasCompactSupport χ := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-2) 2) isCompact_Icc ?_
    intro x hx
    by_contra h
    apply hx
    apply hχs
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hχc : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => (χ ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hχcs : HasCompactSupport (fun ξ => (χ ξ : ℂ)) := by
    simpa [Function.comp_def] using hcs.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  choose A hA0 hA using fun j : ℕ => c03c_aux_smooth_decay
    (b := fun ξ : ℝ => (Complex.I * ξ) ^ j * (χ ξ : ℂ))
    (((contDiff_const.mul Complex.ofRealCLM.contDiff).pow j).mul hχc) hχcs.mul_left
  set Cp : ℝ := Cps 1 + Cps 2 + Cps 3 with hCp
  have hCp0 : 0 < Cp := by have := hCps 1; have := hCps 2; have := hCps 3; positivity
  set C₀ : ℝ := 32 * (A 0 + A 1 + A 2 + Cp * C₁) + 1 with hC₀
  have hA012 : ∀ j ≤ 2, A j ≤ A 0 + A 1 + A 2 := by
    intro j hj
    have := hA0 0; have := hA0 1; have := hA0 2
    interval_cases j <;> linarith
  have hCpj : ∀ j ≤ 2, Cps (j + 1) ≤ Cp := by
    intro j hj
    have := hCps 1; have := hCps 2; have := hCps 3
    interval_cases j <;> simp only [hCp] <;> linarith
  refine ⟨C₀, by have := hA0 0; have := hA0 1; have := hA0 2; positivity, fun k => ?_⟩
  -- continuity and support of m_k
  have hphi : Continuous (fun ξ : ℝ => ((Phi0 p ξ : ℝ) : ℂ)) := by
    unfold Phi0
    have : Continuous (fun ξ : ℝ => |ξ| ^ p) := continuous_abs.rpow_const (fun _ => Or.inr hp.le)
    fun_prop
  have hmc : Continuous (c03_symbol_mk p χ k) := by
    unfold c03_symbol_mk
    exact (Complex.continuous_ofReal.comp hχ.continuous).mul (hphi.pow k)
  have hmcs : HasCompactSupport (c03_symbol_mk p χ k) := by
    unfold c03_symbol_mk; exact hχcs.mul_right
  refine ⟨c03c_aux_invF_smooth hmc hmcs, fun j hj y => ?_⟩
  rw [c03c_aux_invF_iter hmc hmcs j]
  have hs0 : 0 ≤ p + 2 + j := by positivity
  have hs5 : p + 2 + j ≤ 5 := by
    have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    linarith
  rw [show -p - 2 - (j : ℝ) = -(p + 2 + j) by ring]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- k = 0
    have heq : (fun ξ : ℝ => (Complex.I * ξ) ^ j * c03_symbol_mk p χ 0 ξ) =
        fun ξ : ℝ => (Complex.I * ξ) ^ j * (χ ξ : ℂ) := by
      funext ξ; simp [c03_symbol_mk]
    rw [heq, pow_zero, mul_one]
    have hfin := c03c_aux_jb_combine (y := y) hs0 hs5 (hA0 j) (fun hy => by
      refine ((hA j y).2 hy).trans ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy (by linarith)) (hA0 j))
      (hA j y).1
    refine hfin.trans ?_
    have : 0 ≤ jb y ^ (-(p + 2 + j)) := by
      have : 0 < jb y := Real.sqrt_pos.mpr (by positivity)
      positivity
    have h1 := hA012 j hj
    have : 32 * A j ≤ C₀ := by rw [hC₀]; have := hC₁; have : 0 ≤ Cp * C₁ := by positivity
                               linarith
    gcongr
  · -- k ≥ 1
    obtain ⟨hcd, hcon, hsupp, hvan, hbnd⟩ := hb k hk j hj
    have heq : (fun ξ : ℝ => (Complex.I * ξ) ^ j * c03_symbol_mk p χ k ξ) =
        c03_symbol_akj p χ k j := by
      funext ξ; simp only [c03_symbol_mk, c03_symbol_akj]; ring
    rw [heq]
    have hM : 0 ≤ C₁ * C ^ k := by positivity
    have hn : (j + 1 + 1 - 1 : ℕ) = j + 1 := by omega
    obtain ⟨hfar, hall⟩ := hPS (j + 1) (C₁ * C ^ k) hM (c03_symbol_akj p χ k j) hsupp
      (by rw [hn]; exact hcd) (hcon.of_le (c03c_aux_le_top _))
      (fun l hl => hvan l (by omega))
      (fun ξ h0 h2 l hl => by
        have := hbnd ξ h0 h2 l (by omega)
        refine this.trans (le_of_eq ?_)
        congr 2; push_cast; ring)
    have hfin := c03c_aux_jb_combine (y := y) (B := Cps (j + 1) * (C₁ * C ^ k)) hs0 hs5
      (by have := hCps (j + 1); positivity)
      (fun hy => by
        have := hfar y hy
        rwa [show (-( ((j + 1 + 1 : ℕ) : ℝ)) - p) = -(p + 2 + j) by push_cast; ring] at this)
      (hall y)
    refine hfin.trans ?_
    have hjb : 0 ≤ jb y ^ (-(p + 2 + j)) := by
      have : 0 < jb y := Real.sqrt_pos.mpr (by positivity)
      positivity
    have h1 := hCpj j hj
    have hCk : 0 ≤ C ^ k := by positivity
    have : 32 * (Cps (j + 1) * C₁) ≤ C₀ := by
      rw [hC₀]
      have : Cps (j + 1) * C₁ ≤ Cp * C₁ := mul_le_mul_of_nonneg_right h1 hC₁.le
      have := hA0 0; have := hA0 1; have := hA0 2
      linarith
    calc 32 * (Cps (j + 1) * (C₁ * C ^ k)) * jb y ^ (-(p + 2 + j))
        = (32 * (Cps (j + 1) * C₁)) * C ^ k * jb y ^ (-(p + 2 + j)) := by ring
      _ ≤ C₀ * C ^ k * jb y ^ (-(p + 2 + j)) := by gcongr

/-! ## Proof of `c03_frac_kernel_formula` -/

theorem c03c_aux_calpha_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < calpha p := by
  have hsin : 0 < Real.sin (π * p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have := Real.Gamma_pos_of_pos (show 0 < 1 + p by linarith)
  unfold calpha; positivity

/-- `∫ (1 - cos(λz))/|z|^{1+p} = |λ|^p / c_α`. -/
theorem c03c_aux_cos_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (lam : ℝ) :
    Integrable (fun z : ℝ => (1 - Real.cos (lam * z)) / |z| ^ (1 + p)) ∧
    ∫ z : ℝ, (1 - Real.cos (lam * z)) / |z| ^ (1 + p) = |lam| ^ p / calpha p := by
  obtain ⟨hI, hV⟩ := Lib.integral_one_sub_cos_mul_abs_rpow hp (by linarith) lam
  have he : (fun z : ℝ => (1 - Real.cos (lam * z)) / |z| ^ (1 + p)) =
      fun h => (1 - Real.cos (h * lam)) * |h| ^ (-1 - p) := by
    funext z
    rw [mul_comm lam z, show (-1 - p) = -(1 + p) by ring, Real.rpow_neg (abs_nonneg z),
      div_eq_mul_inv]
  rw [he]
  refine ⟨hI, ?_⟩
  rw [hV, calpha]
  have hsin : 0 < Real.sin (π * p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have := Real.Gamma_pos_of_pos (show 0 < 1 + p by linarith)
  field_simp

theorem c03c_aux_cp_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : c03_cp p = calpha p := by
  have := (c03c_aux_cos_kernel hp hp1 1).2
  simp only [one_mul, abs_one, Real.one_rpow] at this
  rw [c03_cp, this, one_div, inv_inv]

/-- An integrable majorant `B|z|^{-p} 1_{|z|≤1} + A|z|^{-1-p} 1_{|z|≥1}`. -/
theorem c03c_aux_min_majorant {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (A B : ℝ) :
    Integrable (fun z : ℝ => B * Set.indicator (Icc (-1) 1) (fun z : ℝ => |z| ^ (-p)) z +
      A * Set.indicator {z : ℝ | 1 ≤ |z|} (fun z : ℝ => |z| ^ (-1 - p)) z) := by
  have h1 := (c03c_aux_abs_rpow_ind (s := -p) (R := 1) (by linarith) zero_le_one).1
  have h2 := (c03c_aux_abs_rpow_tail (s := -1 - p) (R := 1) (by linarith) one_pos).1
  exact (h1.const_mul B).add (h2.const_mul A)

theorem c03c_aux_min_bound {p : ℝ} (hp : 0 < p) {A B z v : ℝ} (hz : z ≠ 0) (hA : v ≤ A)
    (hB : v ≤ B * |z|) (hv : 0 ≤ v) :
    v / |z| ^ (1 + p) ≤ B * Set.indicator (Icc (-1) 1) (fun z : ℝ => |z| ^ (-p)) z +
      A * Set.indicator {z : ℝ | 1 ≤ |z|} (fun z : ℝ => |z| ^ (-1 - p)) z := by
  have hzpos : 0 < |z| := abs_pos.mpr hz
  have hden : 0 < |z| ^ (1 + p) := by positivity
  have hBn : 0 ≤ B * |z| := hv.trans hB
  have hAn : 0 ≤ A := hv.trans hA
  have hB0 : 0 ≤ B := by
    by_contra h; push Not at h; nlinarith
  by_cases h1 : |z| ≤ 1
  · have hm : z ∈ Icc (-1 : ℝ) 1 := abs_le.mp h1
    rw [Set.indicator_of_mem hm]
    have : v / |z| ^ (1 + p) ≤ B * |z| ^ (-p) := by
      rw [div_le_iff₀ hden]
      calc v ≤ B * |z| := hB
        _ = B * |z| ^ (-p) * |z| ^ (1 + p) := by
          rw [mul_assoc, ← Real.rpow_add hzpos]; norm_num
    have : 0 ≤ A * Set.indicator {z : ℝ | 1 ≤ |z|} (fun z : ℝ => |z| ^ (-1 - p)) z := by
      apply mul_nonneg hAn; apply Set.indicator_nonneg; intro _ _; positivity
    linarith
  · push Not at h1
    have hm : z ∈ {z : ℝ | 1 ≤ |z|} := h1.le
    rw [Set.indicator_of_mem hm]
    have : v / |z| ^ (1 + p) ≤ A * |z| ^ (-1 - p) := by
      rw [div_le_iff₀ hden]
      calc v ≤ A := hA
        _ = A * |z| ^ (-1 - p) * |z| ^ (1 + p) := by
          rw [mul_assoc, ← Real.rpow_add hzpos]; norm_num
    have : 0 ≤ B * Set.indicator (Icc (-1) 1) (fun z : ℝ => |z| ^ (-p)) z := by
      apply mul_nonneg hB0; apply Set.indicator_nonneg; intro _ _; positivity
    linarith


theorem c03c_aux_sin_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (lam : ℝ) :
    Integrable (fun z : ℝ => Real.sin (lam * z) / |z| ^ (1 + p)) ∧
    ∫ z : ℝ, Real.sin (lam * z) / |z| ^ (1 + p) = 0 := by
  have hmaj := c03c_aux_min_majorant hp hp1 1 |lam|
  have hint : Integrable (fun z : ℝ => Real.sin (lam * z) / |z| ^ (1 + p)) := by
    have hm : Measurable (fun z : ℝ => Real.sin (lam * z) / |z| ^ (1 + p)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).measurable.div
        (by fun_prop)
    refine hmaj.mono' hm.aestronglyMeasurable ?_
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < |z| ^ (1 + p))]
    exact c03c_aux_min_bound hp hz (Real.abs_sin_le_one _)
      ((Real.abs_sin_le_abs).trans (by rw [abs_mul])) (abs_nonneg _)
  refine ⟨hint, ?_⟩
  have h := integral_neg_eq_self (fun z : ℝ => Real.sin (lam * z) / |z| ^ (1 + p)) volume
  simp only [mul_neg, Real.sin_neg, abs_neg, neg_div, integral_neg] at h
  linarith

theorem c03c_aux_exp_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (lam : ℝ) :
    Integrable (fun z : ℝ =>
        (1 - Complex.exp (Complex.I * lam * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
      (c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) /
        ((|z| ^ (1 + p) : ℝ) : ℂ) = ((|lam| ^ p : ℝ) : ℂ) := by
  obtain ⟨hc, hcV⟩ := c03c_aux_cos_kernel hp hp1 lam
  obtain ⟨hs, hsV⟩ := c03c_aux_sin_kernel hp hp1 lam
  have he : (fun z : ℝ => (1 - Complex.exp (Complex.I * lam * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
      fun z => (((1 - Real.cos (lam * z)) / |z| ^ (1 + p) : ℝ) : ℂ) -
        Complex.I * ((Real.sin (lam * z) / |z| ^ (1 + p) : ℝ) : ℂ) := by
    funext z
    have : Complex.I * lam * z = ((lam * z : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I]
    push_cast
    ring
  rw [he]
  have hci : Integrable (fun z : ℝ => (((1 - Real.cos (lam * z)) / |z| ^ (1 + p) : ℝ) : ℂ)) :=
    hc.ofReal
  have hsi : Integrable (fun z : ℝ => Complex.I * ((Real.sin (lam * z) / |z| ^ (1 + p) : ℝ) : ℂ)) :=
    hs.ofReal.const_mul _
  refine ⟨hci.sub hsi, ?_⟩
  rw [integral_sub hci hsi, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, hcV, hsV,
    c03c_aux_cp_eq hp hp1]
  have := c03c_aux_calpha_pos hp hp1
  have hne : ((calpha p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  push_cast
  field_simp
  simp

theorem c03c_aux_fracD_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (hgb : ∃ M, ∀ x, |g x| ≤ M) (hgd : ∃ M, ∀ x, |deriv g x| ≤ M) (y : ℝ) :
    Integrable (fun z => (g y - g (y + z)) / |z| ^ (1 + p)) ∧
      fracD p g y = c03_cp p * ∫ z, (g y - g (y + z)) / |z| ^ (1 + p) := by
  obtain ⟨M, hM⟩ := hgb
  obtain ⟨M', hM'⟩ := hgd
  have hmaj := c03c_aux_min_majorant hp hp1 (2 * M) M'
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hint : Integrable (fun z => (g y - g (y + z)) / |z| ^ (1 + p)) := by
    refine hmaj.mono' ?_ ?_
    · have : Continuous g := hg.continuous
      exact ((continuous_const.sub (this.comp (continuous_const.add continuous_id))).measurable.div
        (by fun_prop : Measurable fun z : ℝ => |z| ^ (1 + p))).aestronglyMeasurable
    · filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < |z| ^ (1 + p))]
      refine c03c_aux_min_bound hp hz ?_ ?_ (abs_nonneg _)
      · have := hM y; have := hM (y + z)
        rw [abs_le] at *; constructor <;> linarith
      · have := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := univ) (x := y + z) (y := y)
          (C := M') (fun x _ => hdiff x) (fun x _ => hM' x) convex_univ trivial trivial
        simpa [Real.norm_eq_abs] using this
  refine ⟨hint, ?_⟩
  rw [fracD, c03c_aux_cp_eq hp hp1]
  congr 1
  rw [← integral_add_left_eq_self y (μ := volume)
    (f := fun z => (g y - g z) / |y - z| ^ (p + 1))]
  congr 1
  funext z
  rw [show y - (y + z) = -z by ring, abs_neg, add_comm p 1]


/-- `∫ |1 - e^{iξz}|/|z|^{1+p} dz ≤ |ξ| I₁ + 2 I₂`. -/
theorem c03c_aux_exp_kernel_norm {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (ξ : ℝ) :
    ∫ z : ℝ, ‖(1 - Complex.exp (Complex.I * ξ * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ ≤
      |ξ| * (∫ z : ℝ, Set.indicator (Icc (-1) 1) (fun z : ℝ => |z| ^ (-p)) z) +
        2 * (∫ z : ℝ, Set.indicator {z : ℝ | 1 ≤ |z|} (fun z : ℝ => |z| ^ (-1 - p)) z) := by
  have hmaj := c03c_aux_min_majorant hp hp1 2 |ξ|
  have hb : ∀ᵐ (z : ℝ) ∂(volume : Measure ℝ),
      ‖(1 - Complex.exp (Complex.I * ξ * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ ≤
      |ξ| * Set.indicator (Icc (-1) 1) (fun z : ℝ => |z| ^ (-p)) z +
        2 * Set.indicator {z : ℝ | 1 ≤ |z|} (fun z : ℝ => |z| ^ (-1 - p)) z := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < |z| ^ (1 + p))]
    have he : Complex.I * ξ * z = Complex.I * ((ξ * z : ℝ) : ℂ) := by push_cast; ring
    refine c03c_aux_min_bound hp hz ?_ ?_ (norm_nonneg _)
    · refine (norm_sub_le _ _).trans ?_
      rw [he, norm_one, Complex.norm_exp_I_mul_ofReal]; norm_num
    · rw [he, norm_sub_rev]
      refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
      rw [Real.norm_eq_abs, abs_mul]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hmaj hb).trans
    (le_of_eq ?_)
  rw [integral_add, integral_const_mul, integral_const_mul]
  · exact ((c03c_aux_abs_rpow_ind (s := -p) (R := 1) (by linarith) zero_le_one).1.const_mul _)
  · exact ((c03c_aux_abs_rpow_tail (s := -1 - p) (R := 1) (by linarith) one_pos).1.const_mul _)

/-- Fubini integrability for the Fourier side of the kernel formula. -/
theorem c03c_aux_fubini_int {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {G : ℝ → ℂ} (y : ℝ)
    (hGc : Continuous G) (hGi : Integrable G) (hGξ : Integrable (fun ξ : ℝ => |ξ| * ‖G ξ‖)) :
    Integrable (Function.uncurry fun ξ z : ℝ => G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
      ((1 - Complex.exp (Complex.I * ξ * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ))) (volume.prod volume) := by
  have hFm : AEStronglyMeasurable (Function.uncurry fun ξ z : ℝ => G ξ *
      Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
      ((1 - Complex.exp (Complex.I * ξ * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ))) (volume.prod volume) := by
    have h1 : Continuous (fun q : ℝ × ℝ => G q.1 * Complex.exp (Complex.I * (y : ℂ) * (q.1 : ℂ)) *
        (1 - Complex.exp (Complex.I * q.1 * q.2))) := by fun_prop
    have h2 : Measurable (fun q : ℝ × ℝ => ((|q.2| ^ (1 + p) : ℝ) : ℂ)) := by fun_prop
    refine (h1.measurable.div h2).aestronglyMeasurable.congr (Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, Pi.div_apply]; ring
  rw [integrable_prod_iff hFm]
  refine ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
  · show Integrable (fun z : ℝ => G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
      ((1 - Complex.exp (Complex.I * ξ * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ))) volume
    exact (c03c_aux_exp_kernel hp hp1 ξ).1.const_mul (G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))
  · set I1 := ∫ z : ℝ, Set.indicator (Icc (-1) 1) (fun z : ℝ => |z| ^ (-p)) z
    set I2 := ∫ z : ℝ, Set.indicator {z : ℝ | 1 ≤ |z|} (fun z : ℝ => |z| ^ (-1 - p)) z
    have hbd : Integrable (fun ξ : ℝ => ‖G ξ‖ * (|ξ| * I1 + 2 * I2)) := by
      have := (hGξ.mul_const I1).add (hGi.norm.mul_const (2 * I2))
      refine this.congr (Eventually.of_forall fun ξ => ?_); simp only [Pi.add_apply]; ring
    refine hbd.mono' hFm.norm.integral_prod_right' (Eventually.of_forall fun ξ => ?_)
    simp only [Function.uncurry, norm_mul]
    have h1 : ‖Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [h1, mul_one, integral_const_mul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (c03c_aux_exp_kernel_norm hp hp1 ξ) (norm_nonneg _)


open scoped FourierTransform in
theorem c03c_aux_schwartz_kernel {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (g : SchwartzMap ℝ ℂ) (y : ℝ) :
    fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (⇑g) y =
      (c03_cp p : ℂ) * ∫ z : ℝ, (g y - g (y + z)) / ((|z| ^ (1 + p) : ℝ) : ℂ) := by
  obtain ⟨hGi, hinv⟩ := Lib.schwartz_fourier_inversion g
  set G : ℝ → ℂ := fun ξ => ∫ x, g x * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) with hG
  have hGf : G = fun ξ => 𝓕 (⇑g) (ξ / (2 * π)) := by
    funext ξ; exact Lib.integral_mul_exp_neg_I_eq_fourier _ ξ
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  have hGc : Continuous G := by
    rw [hGf, ← SchwartzMap.fourier_coe]
    exact (𝓕 g).continuous.comp (continuous_id.div_const _)
  have hGξ : Integrable (fun ξ : ℝ => |ξ| * ‖G ξ‖) := by
    have h1 := ((𝓕 g).integrable_pow_mul volume 1).comp_div h2π
    have h2 := h1.const_mul (2 * π)
    refine h2.congr (Eventually.of_forall fun ξ => ?_)
    simp only [hGf, ← SchwartzMap.fourier_coe, pow_one, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    field_simp
  have hunim : ∀ t : ℝ, Integrable (fun ξ : ℝ => G ξ * Complex.exp (Complex.I * (t : ℂ) * (ξ : ℂ))) := by
    intro t
    refine hGi.norm.mono' (by fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Complex.norm_exp]; simp
  have hFi := c03c_aux_fubini_int hp hp1 y hGc hGi hGξ
  have hcp : (c03_cp p : ℂ) ≠ 0 := by
    rw [c03c_aux_cp_eq hp hp1]; exact_mod_cast (c03c_aux_calpha_pos hp hp1).ne'
  have hgy : ∀ z : ℝ, (g y - g (y + z)) / ((|z| ^ (1 + p) : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ ξ, G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
        ((1 - Complex.exp (Complex.I * ξ * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
    intro z
    rw [← hinv y, ← hinv (y + z), ← mul_sub, ← integral_sub (hunim y) (hunim (y + z)),
      mul_div_assoc, ← integral_div]
    congr 1; refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hG]
    rw [show Complex.I * ((y + z : ℝ) : ℂ) * (ξ : ℂ) = Complex.I * (y : ℂ) * (ξ : ℂ) +
      Complex.I * ξ * z by push_cast; ring, Complex.exp_add]
    ring
  have hinner : ∀ ξ : ℝ, ∫ z : ℝ, G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
      ((1 - Complex.exp (Complex.I * ξ * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
      G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) * (((|ξ| ^ p : ℝ) : ℂ) / (c03_cp p : ℂ)) := by
    intro ξ
    rw [integral_const_mul, ← (c03c_aux_exp_kernel hp hp1 ξ).2]
    field_simp
  simp_rw [hgy]
  rw [integral_const_mul, ← integral_integral_swap hFi]
  simp_rw [hinner]
  rw [fourierMultiplier, invFourierT]
  have : ∀ ξ : ℝ, G ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
      (((|ξ| ^ p : ℝ) : ℂ) / (c03_cp p : ℂ)) = (c03_cp p : ℂ)⁻¹ *
      (((|ξ| ^ p : ℝ) : ℂ) * fourierT (⇑g) ξ * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) := by
    intro ξ
    have hfg : fourierT (⇑g) ξ = G ξ := rfl
    rw [hfg, div_eq_mul_inv]
    ring
  simp_rw [this]
  rw [integral_const_mul]
  field_simp

/-- Blueprint: lem:c03_frac_kernel_formula.  `c_p ∫ (1-e^{iλz})/|z|^{1+p} dz = |λ|^p`, and
`|D|^p g(y) = c_p ∫ (g(y)-g(y+z))/|z|^{1+p} dz` for Schwartz `g` (Fourier side) and for bounded
`C¹` functions with bounded derivative (the shared `fracD`). -/
theorem c03c_c03_frac_kernel_formula (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun z : ℝ => (1 - Real.cos z) / |z| ^ (1 + p)) ∧ 0 < c03_cp p ∧
    (∀ lam : ℝ, Integrable (fun z : ℝ =>
        (1 - Complex.exp (Complex.I * lam * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
      (c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) /
        ((|z| ^ (1 + p) : ℝ) : ℂ) = ((|lam| ^ p : ℝ) : ℂ)) ∧
    (∀ g : SchwartzMap ℝ ℂ, ∀ y : ℝ,
      fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (⇑g) y =
        (c03_cp p : ℂ) * ∫ z : ℝ, (g y - g (y + z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    c03_cp p = calpha p ∧
    (∀ g : ℝ → ℝ, ContDiff ℝ 1 g → (∃ M, ∀ x, |g x| ≤ M) → (∃ M, ∀ x, |deriv g x| ≤ M) →
      ∀ y, Integrable (fun z => (g y - g (y + z)) / |z| ^ (1 + p)) ∧
        fracD p g y = c03_cp p * ∫ z, (g y - g (y + z)) / |z| ^ (1 + p)) := by
  refine ⟨?_, ?_, fun lam => c03c_aux_exp_kernel hp hp1 lam,
    fun g y => c03c_aux_schwartz_kernel hp hp1 g y, c03c_aux_cp_eq hp hp1,
    fun g hg hgb hgd y => c03c_aux_fracD_kernel hp hp1 g hg hgb hgd y⟩
  · simpa using (c03c_aux_cos_kernel hp hp1 1).1
  · rw [c03c_aux_cp_eq hp hp1]; exact c03c_aux_calpha_pos hp hp1

/-! ## Assembly of `c03_ibp_homogeneous` -/

/-- A concrete cutoff `χ₁(z) = smoothTransition(2 - |z|)`. -/
theorem c03c_aux_cutoff_exists : ∃ χ₁ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ₁ ∧
    (∀ z, 0 ≤ χ₁ z ∧ χ₁ z ≤ 1) ∧ (∀ z ∈ Icc (-1 : ℝ) 1, χ₁ z = 1) ∧
    (∀ z, 2 < |z| → χ₁ z = 0) := by
  refine ⟨fun z => Real.smoothTransition (2 - |z|), ?_, fun z =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · refine contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (1 : ℝ)) ?_
      have : Ioo (-1 : ℝ) 1 ∈ 𝓝 z := Ioo_mem_nhds (by rw [hz]; norm_num) (by rw [hz]; norm_num)
      filter_upwards [this] with x hx
      apply Real.smoothTransition.one_of_one_le
      have : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
      linarith
    · exact Real.smoothTransition.contDiffAt.comp z (contDiffAt_const.sub (contDiffAt_abs hz))
  · intro z hz
    apply Real.smoothTransition.one_of_one_le
    have : |z| ≤ 1 := abs_le.mpr hz
    linarith
  · intro z hz
    exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Blueprint: lem:c03_ibp_homogeneous.  Integration by parts against `|z|^{-1-p}`:
`|∫ e^{iφ} e^{-ηz²} b |z|^{-1-p} dz| ≤ C B Λ^{p-K}` for `η ≥ 0`, continuous in `η ≥ 0`;
`C` depends on `p, K, c₀` and finitely many `C_s`. -/
theorem c03c_c03_ibp_homogeneous (p K c₀ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hK : p < K)
    (hc₀ : 0 < c₀) :
    ∃ s₀ : ℕ, ∀ Cs : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ (Λ B : ℝ) (U : Set ℝ) (b : ℝ → ℂ) (φ : ℝ → ℝ),
      0 < Λ → 0 ≤ B → IsOpen U → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b →
      tsupport b ⊆ U → ContDiffOn ℝ (⊤ : ℕ∞) φ U →
      (∀ z ∈ U, z ≠ 0 → ∀ s ≤ s₀, ‖iteratedDeriv s b z‖ ≤ Cs s * B * |z| ^ (K - s)) →
      (∀ z ∈ U, c₀⁻¹ * Λ ≤ |deriv φ z| ∧ |deriv φ z| ≤ c₀ * Λ) →
      (∀ z ∈ U, z ≠ 0 → ∀ s ≤ s₀,
        |iteratedDeriv s (fun z => 1 / deriv φ z) z| ≤ Cs s * Λ⁻¹ * |z| ^ (-(s : ℝ))) →
      (∀ η : ℝ, 0 ≤ η → ‖∫ z : ℝ, Complex.exp (Complex.I * (φ z : ℂ)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ ≤
        C * B * Λ ^ (p - K)) ∧
      ContinuousOn (fun η : ℝ => ∫ z : ℝ, Complex.exp (Complex.I * (φ z : ℂ)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ)) (Ici 0) := by
  obtain ⟨χ₁, hχ, hχ01, hχ1, hχs⟩ := c03c_aux_cutoff_exists
  set L : ℕ := ⌊K - p⌋₊ + 1 with hLdef
  have hL : K - p < L := by
    rw [hLdef]; push_cast; exact Nat.lt_floor_add_one _
  refine ⟨L + 1, fun Cs => ?_⟩
  obtain ⟨Cf, hCf, hCfb⟩ := c03_homogeneous_far p K c₀ hp hp1 hK hc₀ L hL χ₁ hχ hχ01 hχ1 hχs Cs
  have hLpK : 0 < (L : ℝ) + p - K := by linarith
  set Cn : ℝ := 2 * |Cs 0| / (K - p) * 2 ^ (K - p) with hCn
  have hCn0 : 0 ≤ Cn := by
    have : 0 < K - p := by linarith
    positivity
  refine ⟨Cn + 2 * Cf / (L + p - K) + 1, by positivity, ?_⟩
  intro Λ B U b φ hΛ hB hU hb hbc hbU hφ hbd hφd hqd
  have hφc : ContinuousOn φ U := hφ.continuousOn
  set be : ℝ → ℂ := fun z => b z * Complex.exp (Complex.I * (φ z : ℂ)) with hbe
  have hbec : Continuous be := c03c_aux_cont_mul_exp hU hb.continuous hbU hφc
  -- global pointwise bound on b
  have hb0 : ∀ z : ℝ, z ≠ 0 → ‖b z‖ ≤ |Cs 0| * B * |z| ^ K := by
    intro z hz
    by_cases hzU : z ∈ U
    · have := hbd z hzU hz 0 (Nat.zero_le _)
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at this
      refine this.trans ?_
      have : 0 ≤ |z| ^ K := by positivity
      gcongr; exact le_abs_self _
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hzU (hbU h)), norm_zero]; positivity
  have hbe0 : ∀ z : ℝ, z ≠ 0 → ‖be z‖ ≤ |Cs 0| * B * |z| ^ K := by
    intro z hz
    have h1 : ‖Complex.exp (Complex.I * (φ z : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [hbe, norm_mul, h1, mul_one]; exact hb0 z hz
  set F : ℝ → ℝ → ℂ := fun η z => Complex.exp (Complex.I * (φ z : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ) with hF
  have hsplit : ∀ η z, F η z = (χ₁ (Λ * z) : ℂ) * (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * be z / ((|z| ^ (1 + p) : ℝ) : ℂ)) +
      Complex.exp (Complex.I * (φ z : ℂ)) * c03c_homg p χ₁ Λ η b z := by
    intro η z
    simp only [hF, hbe, c03c_homg, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp,
      Complex.ofReal_neg]
    ring
  have hbound : ∀ η, 0 ≤ η → Integrable (F η) ∧ ‖∫ z, F η z‖ ≤
      (Cn + 2 * Cf / (L + p - K) + 1) * B * Λ ^ (p - K) := by
    intro η hη
    obtain ⟨hni, hnb⟩ := c03_homogeneous_near p K B |Cs 0| Λ η hp hp1 hK hB (abs_nonneg _) hΛ hη
      be hbec.aestronglyMeasurable hbe0 (fun _ => 0) measurable_const χ₁ hχ.continuous.measurable
      hχ01 hχs
    obtain ⟨hfi, -, -, -, hfb⟩ := hCfb B Λ η U b φ hB hΛ hη hU hb hbc hbU hφ
      (fun z hz hz0 j hj => hbd z hz hz0 j hj) (fun z hz hz0 j hj => hqd z hz hz0 j hj) hφd
    have hFe : F η = fun z => (χ₁ (Λ * z) : ℂ) * (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * be z / ((|z| ^ (1 + p) : ℝ) : ℂ)) +
      Complex.exp (Complex.I * (φ z : ℂ)) * c03c_homg p χ₁ Λ η b z := funext (hsplit η)
    refine ⟨hFe ▸ hni.add hfi, ?_⟩
    rw [hFe, integral_add hni hfi]
    refine (norm_add_le _ _).trans ?_
    have hnear : 2 * |Cs 0| * B / (K - p) * (2 / Λ) ^ (K - p) = Cn * B * Λ ^ (p - K) := by
      rw [hCn, Real.div_rpow (by norm_num) hΛ.le, show p - K = -(K - p) by ring,
        Real.rpow_neg hΛ.le]
      generalize Λ ^ (K - p) = u
      generalize (2 : ℝ) ^ (K - p) = v
      ring
    have hfar : 2 * Cf * B * Λ ^ (p - K) / (L + p - K) = 2 * Cf / (L + p - K) * B * Λ ^ (p - K) := by
      ring
    have hpos : 0 ≤ B * Λ ^ (p - K) := by positivity
    rw [hnear] at hnb; rw [hfar] at hfb
    nlinarith
  refine ⟨fun η hη => (hbound η hη).2, ?_⟩
  -- continuity in η
  obtain ⟨R, hR⟩ := hbc.isBounded.subset_closedBall 0
  set R' := max R 0
  have hs : -1 < K - 1 - p := by linarith
  obtain ⟨hgi, -⟩ := c03c_aux_abs_rpow_ind hs (le_max_right R 0)
  refine continuousOn_of_dominated (bound := fun z => (|Cs 0| * B) *
      Set.indicator (Icc (-R') R') (fun z : ℝ => |z| ^ (K - 1 - p)) z) ?_ ?_
    (hgi.const_mul _) ?_
  · intro η hη; exact (hbound η hη).1.aestronglyMeasurable
  · intro η hη
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz
    by_cases hzs : z ∈ tsupport b
    · have hzR : z ∈ Icc (-R') R' := by
        have := hR hzs
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
        exact abs_le.mp (this.trans (le_max_left _ _))
      rw [Set.indicator_of_mem hzR]
      have hzpos : 0 < |z| := abs_pos.mpr hz
      have h1 : ‖Complex.exp (Complex.I * (φ z : ℂ))‖ = 1 := by rw [Complex.norm_exp]; simp
      have h3 : ‖Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        simp only [Complex.neg_re, Complex.ofReal_re]
        exact Real.exp_le_one_iff.mpr (by have := (mem_Ici.mp hη); nlinarith [sq_nonneg z])
      simp only [hF, norm_div, norm_mul, h1, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _)]
      have hpow : |z| ^ K / |z| ^ (1 + p) = |z| ^ (K - 1 - p) := by
        rw [← Real.rpow_sub hzpos]; ring_nf
      calc ‖Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ * ‖b z‖ / |z| ^ (1 + p)
          ≤ 1 * (|Cs 0| * B * |z| ^ K) / |z| ^ (1 + p) := by
            gcongr; exact hb0 z hz
        _ = |Cs 0| * B * |z| ^ (K - 1 - p) := by rw [← hpow]; ring
    · rw [image_eq_zero_of_notMem_tsupport hzs] at *
      simp only [hF, mul_zero, zero_div, norm_zero]
      by_cases hzR : z ∈ Icc (-R') R'
      · rw [Set.indicator_of_mem hzR]; positivity
      · rw [Set.indicator_of_notMem hzR, mul_zero]
  · refine Eventually.of_forall fun z => ?_
    apply Continuous.continuousOn
    show Continuous (fun η : ℝ => Complex.exp (Complex.I * (φ z : ℂ)) *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ))
    fun_prop


end GSQG
