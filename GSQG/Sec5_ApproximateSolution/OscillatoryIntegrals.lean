import GSQG.Definitions
import GSQG.Auxiliary.SpecialIntegrals
import GSQG.AppendixAB.SymbolCalculus

/-!
# §5.1: oscillatory integrals (blueprint ch. 04; blueprint notation `Osc[a]`)

Used by `FamilyAndE1toE4.lean` (which imports this file): `c04_eiphase`, `c04_IsTruncation` and the node
`lem:c04_osc_integral` (`c04_osc_integral_properties`, statement unchanged). Also holds the new
oscillatory-foundation sublemmas of `04_approx_family.tex` under their exact blueprint Lean names.
Helpers: `c04o_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology ComplexConjugate

noncomputable section

namespace GSQG

/-- Chapter 04 (local).  The oscillatory factor `e^{i(yξ - Φ₀(ξ))}`. -/
def c04_eiphase (p y ξ : ℝ) : ℂ := Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ))

/-- Chapter 04 (local, def:c04_osc_integral).  `ρ' ∈ C_c^∞(ℝ;[0,1])`, `ρ' = 1` on `[-1,1]`,
`supp ρ' ⊆ [-2,2]` (an admissible truncation, used to state independence of `ρ`). -/
def c04_IsTruncation (ρ' : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ρ' ∧ (∀ x, ρ' x ∈ Icc (0 : ℝ) 1) ∧ (∀ x ∈ Icc (-1 : ℝ) 1, ρ' x = 1) ∧
    tsupport ρ' ⊆ Icc (-2) 2

/-! ### Auxiliary data: the integration-by-parts operator, its constants, tail cutoffs -/

/-- Chapter 04 (local, lem:c04_osc_ibp_step).  The integration-by-parts operator
`T_q b = -∂_ξ(b q / i)` on `(L,∞)`, extended by `0` to `(-∞,L]`. -/
def c04o_aux_ibpOp (L : ℝ) (q : ℝ → ℝ) (b : ℝ → ℂ) : ℝ → ℂ :=
  fun ξ => if L < ξ then -deriv (fun x => b x * (q x : ℂ) / Complex.I) ξ else 0

/-- Chapter 04 (local, lem:c04_osc_ibp_iteration).  The recurrence coefficients
`E_{0,k} = B_k`, `E_{n+1,k} = ∑_{r=0}^{k+1} binom(k+1,r) E_{n,r} D_{k+1-r}`. -/
def c04o_aux_E (B D : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => B k
  | n + 1, k => ∑ r ∈ Finset.range (k + 2), ((k + 1).choose r : ℝ) * c04o_aux_E B D n r * D (k + 1 - r)

/-- Chapter 04 (local, lem:c04_osc_cutoff_symbols).  A tail cutoff at scale `L`:
`θ ∈ C_c^∞(ℝ;[0,1])`, `θ = 1` on `[0,L]`, `θ = 0` on `[2L,∞)`. -/
def c04o_aux_IsTailCutoff (L : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧ (∀ x, θ x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Icc (0 : ℝ) L, θ x = 1) ∧ ∀ x, 2 * L ≤ x → θ x = 0

/-! ### Pure helpers for the integration-by-parts operator -/

theorem c04o_aux_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- `∂^k ↑f = ↑(∂^k f)`. -/
theorem c04o_aux_iteratedDeriv_ofReal (f : ℝ → ℝ) (y : ℝ) (k : ℕ) (hf : ContDiffAt ℝ k f y) :
    iteratedDeriv k (fun t => ((f t : ℝ) : ℂ)) y = ((iteratedDeriv k f y : ℝ) : ℂ) := by
  have : (fun t => ((f t : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    Complex.ofRealCLM.iteratedFDeriv_comp_left hf le_rfl]
  simp

/-- Flatness: a smooth function vanishing on `(-∞,L)` has all derivatives zero on `(-∞,L]`. -/
theorem c04o_aux_flat {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {L : ℝ}
    (h0 : ∀ ξ < L, f ξ = 0) (k : ℕ) : ∀ ξ ≤ L, iteratedDeriv k f ξ = 0 := by
  have hz : ∀ ξ < L, iteratedDeriv k f ξ = 0 := by
    intro ξ hξ
    have : f =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hξ] with x hx using h0 x hx
    rw [this.iteratedDeriv_eq]; simp
  have hcl : IsClosed {x | iteratedDeriv k f x = 0} :=
    isClosed_eq (hf.continuous_iteratedDeriv k (by exact_mod_cast le_top)) continuous_const
  have : Iic L ⊆ {x | iteratedDeriv k f x = 0} := by
    rw [← closure_Iio]
    exact hcl.closure_subset_iff.2 hz
  exact fun ξ hξ => this hξ

/-- The product `b q` is smooth when `b` vanishes on `(-∞,L]` and `q` is smooth on `(L/2,∞)`,
and `T_q b = i ∂(bq)` globally. -/
theorem c04o_aux_ibpOp_eq (L : ℝ) (hL : 0 < L) (q : ℝ → ℝ) (b : ℝ → ℂ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbL : ∀ ξ ≤ L, b ξ = 0)
    (hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => b x * (q x : ℂ)) ∧
    c04o_aux_ibpOp L q b = fun ξ => Complex.I * deriv (fun x => b x * (q x : ℂ)) ξ := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x * (q x : ℂ)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x L with hx | hx
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [hbL y (le_of_lt hy)]
    · exact hb.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (hq.contDiffAt (Ioi_mem_nhds (by linarith))))
  refine ⟨hg, funext fun ξ => ?_⟩
  unfold c04o_aux_ibpOp
  split_ifs with h
  · rw [deriv_div_const, div_eq_mul_inv, Complex.inv_I]; ring
  · have := c04o_aux_flat hg (L := L) (fun x hx => by simp [hbL x hx.le]) 1 ξ (not_lt.1 h)
    rw [iteratedDeriv_one] at this
    rw [this, mul_zero]

/-- Power-tail integrability: a continuous `f` with `‖f ξ‖ ≤ c ξ^d` on `(L,∞)`, `d < -1`. -/
theorem c04o_aux_powtail_Ioi {f : ℝ → ℂ} (hf : Continuous f) {L c d : ℝ} (hL : 0 < L)
    (hd : d < -1) (hb : ∀ ξ, L ≤ ξ → ‖f ξ‖ ≤ c * ξ ^ d) :
    IntegrableOn f (Ioi L) ∧ ∫ ξ in Ioi L, ‖f ξ‖ ≤ c * (L ^ (d + 1) / (-d - 1)) := by
  have hg : IntegrableOn (fun ξ : ℝ => c * ξ ^ d) (Ioi L) :=
    (integrableOn_Ioi_rpow_of_lt hd hL).const_mul c
  have hI : IntegrableOn f (Ioi L) := by
    refine Integrable.mono' hg hf.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ξ hξ => hb ξ (le_of_lt hξ))
  refine ⟨hI, ?_⟩
  calc ∫ ξ in Ioi L, ‖f ξ‖ ≤ ∫ ξ in Ioi L, c * ξ ^ d :=
        setIntegral_mono_on hI.norm hg measurableSet_Ioi fun ξ hξ => hb ξ (le_of_lt hξ)
    _ = c * (L ^ (d + 1) / (-d - 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt hd hL]
        have : d + 1 ≠ 0 := by linarith
        have : -d - 1 ≠ 0 := by linarith
        congr 1
        field_simp
        ring

/-- Power-tail integrability on `(0,∞)` for a continuous function vanishing on `(-∞,L]`. -/
theorem c04o_aux_powtail {f : ℝ → ℂ} (hf : Continuous f) {L c d : ℝ} (hL : 0 < L)
    (hd : d < -1) (h0 : ∀ ξ ≤ L, f ξ = 0) (hb : ∀ ξ, L ≤ ξ → ‖f ξ‖ ≤ c * ξ ^ d) :
    IntegrableOn f (Ioi 0) ∧ ∫ ξ in Ioi (0 : ℝ), ‖f ξ‖ ≤ c * (L ^ (d + 1) / (-d - 1)) := by
  obtain ⟨hI, hB⟩ := c04o_aux_powtail_Ioi hf hL hd hb
  refine ⟨((hf.integrableOn_Icc (a := 0) (b := L)).mono_set Ioc_subset_Icc_self |>.union hI).mono_set
    (fun x hx => ?_), ?_⟩
  · rcases le_or_gt x L with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi hL.le) (fun x hx => by
        simp only [Set.mem_sdiff, mem_Ioi, not_lt] at hx
        simp [h0 x hx.2])] at hB
    exact hB

/-- A function continuous on `[L,R] ⊆ (0,∞)` and vanishing on the rest of `(0,∞)`. -/
theorem c04o_aux_Icc_supported {f : ℝ → ℂ} {L R : ℝ} (hL : 0 < L) (hLR : L ≤ R)
    (hf : ContinuousOn f (Icc L R)) (h0 : ∀ ξ, 0 < ξ → ξ ∉ Icc L R → f ξ = 0) :
    IntegrableOn f (Ioi 0) ∧ ∫ ξ in Ioi (0 : ℝ), f ξ = ∫ ξ in L..R, f ξ := by
  have hI : IntegrableOn f (Icc L R) := hf.integrableOn_Icc
  have hsub : Icc L R ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hL hx.1
  refine ⟨hI.of_forall_sdiff_eq_zero measurableSet_Ioi fun x hx => h0 x hx.1 hx.2, ?_⟩
  rw [intervalIntegral.integral_of_le hLR, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      fun x hx => h0 x hx.1 hx.2]

/-- Constants for derivatives of a reciprocal: `D_0 = 1`,
`D_l = ∑_{r=1}^{l} binom(l,r) G_r D_{l-r}`. -/
def c04o_aux_recD (G : ℕ → ℝ) (l : ℕ) : ℝ :=
  if h : l = 0 then 1 else
    ∑ i : Fin l, ((l.choose (i + 1) : ℕ) : ℝ) * G (i + 1) * c04o_aux_recD G (l - (i + 1))
termination_by l
decreasing_by omega

theorem c04o_aux_recD_nonneg (G : ℕ → ℝ) (hG : ∀ r, 0 ≤ G r) (l : ℕ) : 0 ≤ c04o_aux_recD G l := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rw [c04o_aux_recD]
    split_ifs with h
    · norm_num
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hG _))
        (ih _ (by omega))

/-- Pointwise derivative bounds for a reciprocal `1/g` from bounds `|g^{(r)}| ≤ G_r W ξ^{-r}`
(`1 ≤ r ≤ l`) and `|g| ≥ W`. -/
theorem c04o_aux_recip_bound (G : ℕ → ℝ) (hG : ∀ r, 0 ≤ G r) (g : ℝ → ℝ) (ξ W : ℝ)
    (hξ : 0 < ξ) (hW : 0 < W) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g ξ) (hgW : W ≤ |g ξ|) (l : ℕ)
    (hgr : ∀ r, 1 ≤ r → r ≤ l → |iteratedDeriv r g ξ| ≤ G r * W * ξ ^ (-(r : ℝ))) :
    |iteratedDeriv l (fun x => (g x)⁻¹) ξ| ≤ c04o_aux_recD G l * W⁻¹ * ξ ^ (-(l : ℝ)) := by
  have hne : g ξ ≠ 0 := fun h => by rw [h, abs_zero] at hgW; linarith
  have hgpos : 0 < |g ξ| := abs_pos.2 hne
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (g x)⁻¹) ξ := hg.inv hne
  have hev : (fun x => g x * (g x)⁻¹) =ᶠ[𝓝 ξ] fun _ => (1 : ℝ) := by
    filter_upwards [hg.continuousAt.eventually_ne hne] with x hx using mul_inv_cancel₀ hx
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst h0
      rw [c04o_aux_recD, dif_pos rfl]
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, rpow_zero, mul_one, one_mul]
      rw [abs_inv]
      exact inv_anti₀ hW hgW
    · have hL := iteratedDeriv_fun_mul (n := l) (x := ξ) (hg.of_le (c04o_aux_le_top l))
        (hq.of_le (c04o_aux_le_top l))
      rw [hev.iteratedDeriv_eq, iteratedDeriv_const, if_neg hpos.ne', Finset.sum_range_succ'] at hL
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
        Nat.sub_zero] at hL
      have hid : iteratedDeriv l (fun x => (g x)⁻¹) ξ = -(g ξ)⁻¹ * ∑ i ∈ Finset.range l,
          (l.choose (i + 1) : ℝ) * iteratedDeriv (i + 1) g ξ *
            iteratedDeriv (l - (i + 1)) (fun x => (g x)⁻¹) ξ := by
        have hgX := add_eq_zero_iff_eq_neg'.1 hL.symm
        calc iteratedDeriv l (fun x => (g x)⁻¹) ξ
            = (g ξ)⁻¹ * (g ξ * iteratedDeriv l (fun x => (g x)⁻¹) ξ) := by
              rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
          _ = _ := by rw [hgX]; ring
      rw [hid, abs_mul, abs_neg, abs_inv, c04o_aux_recD, dif_neg hpos.ne',
        Fin.sum_univ_eq_sum_range (fun i => ((l.choose (i + 1) : ℕ) : ℝ) * G (i + 1) *
          c04o_aux_recD G (l - (i + 1))) l, Finset.sum_mul, Finset.sum_mul]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i + 1 ≤ l := Finset.mem_range.1 hi
      have h1 := hgr (i + 1) (by omega) hi'
      have h2 := ih (l - (i + 1)) (by omega) (fun r hr1 hr2 => hgr r hr1 (by omega))
      have hD := c04o_aux_recD_nonneg G hG (l - (i + 1))
      rw [abs_mul, abs_mul, Nat.abs_cast]
      have hpow : ξ ^ (-(l : ℝ)) = ξ ^ (-((i + 1 : ℕ) : ℝ)) * ξ ^ (-((l - (i + 1) : ℕ) : ℝ)) := by
        rw [← rpow_add hξ]; congr 1; push_cast [hi']; ring
      rw [hpow]
      have hc : (0 : ℝ) ≤ (l.choose (i + 1) : ℝ) := by positivity
      calc |g ξ|⁻¹ * ((l.choose (i + 1) : ℝ) * |iteratedDeriv (i + 1) g ξ| *
              |iteratedDeriv (l - (i + 1)) (fun x => (g x)⁻¹) ξ|)
          ≤ W⁻¹ * ((l.choose (i + 1) : ℝ) * (G (i + 1) * W * ξ ^ (-((i + 1 : ℕ) : ℝ))) *
              (c04o_aux_recD G (l - (i + 1)) * W⁻¹ * ξ ^ (-((l - (i + 1) : ℕ) : ℝ)))) := by
            gcongr
            exact mul_nonneg hc (mul_nonneg (mul_nonneg (hG _) hW.le) (by positivity))
        _ = ((l.choose (i + 1) : ℕ) : ℝ) * G (i + 1) * c04o_aux_recD G (l - (i + 1)) * W⁻¹ *
              (ξ ^ (-((i + 1 : ℕ) : ℝ)) * ξ ^ (-((l - (i + 1) : ℕ) : ℝ))) := by
            field_simp

/-- Derivatives of `y - x^p` at `ξ > 0`. -/
theorem c04o_aux_iteratedDeriv_sub_rpow (p y ξ : ℝ) (hξ : 0 < ξ) (r : ℕ) (hr : 1 ≤ r) :
    |iteratedDeriv r (fun x : ℝ => y - x ^ p) ξ| =
      |(descPochhammer ℝ r).eval p| * ξ ^ (p - r) := by
  rw [iteratedDeriv_const_sub (by omega), iteratedDeriv_neg, abs_neg, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, abs_mul, abs_of_pos (rpow_pos_of_pos hξ _)]

/-- `∂_ξ(yξ - Φ₀(ξ)) = y - ξ^p` for `ξ > 0`. -/
theorem c04o_aux_deriv_phase (p y ξ : ℝ) (hp : 0 < p) (hξ : 0 < ξ) :
    HasDerivAt (fun x : ℝ => y * x - Phi0 p x) (y - ξ ^ p) ξ := by
  have hev : (fun x : ℝ => y * x - Phi0 p x) =ᶠ[𝓝 ξ] fun x => y * x - x ^ (p + 1) / (p + 1) := by
    filter_upwards [Ioi_mem_nhds hξ] with x hx
    have hx' : (0 : ℝ) < x := hx
    unfold Phi0
    rw [abs_of_pos hx', rpow_add hx', rpow_one, mul_comm (x ^ p) x]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 := (hasDerivAt_id ξ).const_mul y
  have h2 := (Real.hasDerivAt_rpow_const (p := p + 1) (Or.inl hξ.ne')).div_const (p + 1)
  have h3 : HasDerivAt (fun x : ℝ => y * x - x ^ (p + 1) / (p + 1))
      (y * 1 - (p + 1) * ξ ^ (p + 1 - 1) / (p + 1)) ξ := h1.sub h2
  convert h3 using 1
  have : p + 1 ≠ 0 := by linarith
  rw [add_sub_cancel_right]
  field_simp

/-- Leibniz bound for symbol-type estimates at one point. -/
theorem c04o_aux_symb_mul (f a : ℝ → ℂ) (ξ : ℝ) (hξ : 0 < ξ) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f ξ)
    (ha : ContDiffAt ℝ (⊤ : ℕ∞) a ξ) (m₁ m₂ : ℝ) (F A : ℕ → ℝ) (l : ℕ)
    (hF : ∀ i ≤ l, ‖iteratedDeriv i f ξ‖ ≤ F i * ξ ^ (m₁ - i))
    (hA : ∀ i ≤ l, ‖iteratedDeriv i a ξ‖ ≤ A i * ξ ^ (m₂ - i)) :
    ‖iteratedDeriv l (fun x => f x * a x) ξ‖ ≤
      (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * F i * A (l - i)) * ξ ^ (m₁ + m₂ - l) := by
  rw [iteratedDeriv_fun_mul (hf.of_le (c04o_aux_le_top l)) (ha.of_le (c04o_aux_le_top l)),
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hpow : ξ ^ (m₁ + m₂ - l) = ξ ^ (m₁ - i) * ξ ^ (m₂ - ((l - i : ℕ) : ℝ)) := by
    rw [← rpow_add hξ]; congr 1; push_cast [hi']; ring
  rw [hpow]
  have h1 := hF i hi'
  have h2 := hA (l - i) (Nat.sub_le _ _)
  have hc : (0 : ℝ) ≤ (l.choose i : ℝ) := by positivity
  calc (l.choose i : ℝ) * ‖iteratedDeriv i f ξ‖ * ‖iteratedDeriv (l - i) a ξ‖
      ≤ (l.choose i : ℝ) * (F i * ξ ^ (m₁ - i)) * (A (l - i) * ξ ^ (m₂ - ((l - i : ℕ) : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
          (mul_nonneg hc ((norm_nonneg _).trans h1))
    _ = _ := by ring

/-- Derivatives of a compactly supported smooth real function are bounded. -/
theorem c04o_aux_bdd_iter (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (i : ℕ) : ∃ R ≥ (0 : ℝ), ∀ x, |iteratedDeriv i f x| ≤ R := by
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv i (c04o_aux_le_top i)).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact (hC x hx).trans (le_max_left _ _)
  · have : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [this.iteratedDeriv_eq]
    simp

/-- A truncation has compact support. -/
theorem c04o_aux_trunc_compact {ρ' : ℝ → ℝ} (hρ : c04_IsTruncation ρ') : HasCompactSupport ρ' :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hρ.2.2.2

/-- Zero derivatives outside the topological support. -/
theorem c04o_aux_iter_notMem {f : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport f) (i : ℕ) :
    iteratedDeriv i f x = 0 := by
  have : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [this.iteratedDeriv_eq]
  simp

/-- Order-zero symbol bounds of the rescaled truncation `ρ(·/M)`, uniform in `M > 0`. -/
theorem c04o_aux_trunc_symb {ρ' : ℝ → ℝ} (hρ : c04_IsTruncation ρ') (i : ℕ) :
    ∃ R ≥ (0 : ℝ), ∀ M : ℝ, 0 < M → ∀ ξ : ℝ, 0 < ξ →
      ‖iteratedDeriv i (fun x => ((ρ' (x / M) : ℝ) : ℂ)) ξ‖ ≤ R * ξ ^ (0 - (i : ℝ)) := by
  obtain ⟨R, hR0, hR⟩ := c04o_aux_bdd_iter ρ' hρ.1 (c04o_aux_trunc_compact hρ) i
  refine ⟨R * 2 ^ i, by positivity, fun M hM ξ hξ => ?_⟩
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x => ρ' (M⁻¹ * x)) := hρ.1.comp (contDiff_const.mul contDiff_id)
  have heq : (fun x => ρ' (x / M)) = fun x => ρ' (M⁻¹ * x) := by
    funext x; rw [div_eq_inv_mul]
  rw [c04o_aux_iteratedDeriv_ofReal _ _ _ (by rw [heq]; exact hsm.contDiffAt.of_le (c04o_aux_le_top i)),
    Complex.norm_real, Real.norm_eq_abs, heq, iteratedDeriv_comp_const_mul (hρ.1.of_le (c04o_aux_le_top i)) M⁻¹]
  simp only
  rw [abs_mul, abs_pow, abs_inv, abs_of_pos hM]
  by_cases hx : M⁻¹ * ξ ∈ tsupport ρ'
  · have h2 : M⁻¹ * ξ ≤ 2 := (hρ.2.2.2 hx).2
    have hMi : M⁻¹ ≤ 2 * ξ⁻¹ := by
      rw [inv_mul_le_iff₀ hM] at h2
      calc M⁻¹ = (M * 2)⁻¹ * 2 := by field_simp
        _ ≤ ξ⁻¹ * 2 := by gcongr
        _ = 2 * ξ⁻¹ := by ring
    have hpow : ξ ^ (0 - (i : ℝ)) = (ξ⁻¹) ^ i := by
      rw [zero_sub, rpow_neg hξ.le, rpow_natCast, inv_pow]
    rw [hpow]
    calc M⁻¹ ^ i * |iteratedDeriv i ρ' (M⁻¹ * ξ)| ≤ (2 * ξ⁻¹) ^ i * R :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hMi i) (hR _) (abs_nonneg _) (by positivity)
      _ = R * 2 ^ i * ξ⁻¹ ^ i := by rw [mul_pow]; ring
  · rw [c04o_aux_iter_notMem hx, abs_zero, mul_zero]
    positivity

/-- Derivatives of `(iξ)^j`. -/
theorem c04o_aux_monomial_symb (j i : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ‖iteratedDeriv i (fun x : ℝ => (Complex.I * (x : ℂ)) ^ j) ξ‖ ≤
      (j.descFactorial i : ℝ) * ξ ^ ((j : ℝ) - i) := by
  have heq : (fun x : ℝ => (Complex.I * (x : ℂ)) ^ j) =
      fun x : ℝ => Complex.I ^ j * (((x ^ j : ℝ)) : ℂ) := by
    funext x; push_cast; ring
  rw [heq, iteratedDeriv_const_mul_field, c04o_aux_iteratedDeriv_ofReal (fun x : ℝ => x ^ j) _ _
    ((contDiff_id.pow j).contDiffAt.of_le (c04o_aux_le_top i)), iteratedDeriv_pow, norm_mul,
    norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt i j with h | h
  · rw [abs_of_nonneg (by positivity), ← rpow_natCast, Nat.cast_sub h]
  · rw [(Nat.descFactorial_eq_zero_iff_lt).2 h]
    simp only [Nat.cast_zero, zero_mul, abs_zero]
    exact le_refl _

/-- Order-zero symbol bounds of `1 - θ` for a tail cutoff. -/
theorem c04o_aux_tail_symb {L : ℝ} (hL : 1 ≤ L) {θ : ℝ → ℝ} (hθ : c04o_aux_IsTailCutoff L θ)
    (i : ℕ) : ∃ H ≥ (0 : ℝ), ∀ ξ : ℝ, 1 ≤ ξ →
      ‖iteratedDeriv i (fun x => ((1 - θ x : ℝ) : ℂ)) ξ‖ ≤ H * ξ ^ (0 - (i : ℝ)) := by
  obtain ⟨hθs, hθc, hθ01, hθ1, hθ0⟩ := hθ
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => 1 - θ x) := contDiff_const.sub hθs
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    refine ⟨1, zero_le_one, fun ξ hξ => ?_⟩
    simp only [iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs, Nat.cast_zero, sub_zero,
      rpow_zero, mul_one]
    have := hθ01 ξ
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · obtain ⟨T, hT0, hT⟩ := c04o_aux_bdd_iter θ hθs hθc i
    refine ⟨T * (2 * L) ^ i, by positivity, fun ξ hξ => ?_⟩
    have hξ0 : 0 < ξ := by linarith
    rw [c04o_aux_iteratedDeriv_ofReal _ _ _ (hcd.contDiffAt.of_le (c04o_aux_le_top i)),
      Complex.norm_real, Real.norm_eq_abs, iteratedDeriv_const_sub hpos, iteratedDeriv_neg,
      abs_neg]
    have hpow : ξ ^ (0 - (i : ℝ)) = (ξ⁻¹) ^ i := by
      rw [zero_sub, rpow_neg hξ0.le, rpow_natCast, inv_pow]
    rw [hpow]
    rcases le_or_gt ξ (2 * L) with h | h
    · have h1 : 1 ≤ (2 * L) ^ i * ξ⁻¹ ^ i := by
        rw [← mul_pow]
        exact one_le_pow₀ (by rw [← div_eq_mul_inv, one_le_div hξ0]; exact h)
      calc |iteratedDeriv i θ ξ| ≤ T := hT ξ
        _ ≤ T * ((2 * L) ^ i * ξ⁻¹ ^ i) := le_mul_of_one_le_right hT0 h1
        _ = T * (2 * L) ^ i * ξ⁻¹ ^ i := by ring
    · have : θ =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds h] with x hx using hθ0 x (le_of_lt hx)
      rw [this.iteratedDeriv_eq]
      simp only [iteratedDeriv_const, if_neg hpos.ne', abs_zero]
      positivity

/-- Multiplying symbol bounds of `a` by an order-`m₁` symbol `f`, with a positive constant. -/
theorem c04o_aux_symb_mul' (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m₁ m : ℝ) (F C : ℕ → ℝ)
    (l : ℕ) (hF : ∀ i ≤ l, ∀ ξ : ℝ, 1 ≤ ξ → ‖iteratedDeriv i f ξ‖ ≤ F i * ξ ^ (m₁ - i)) :
    ∃ K > (0 : ℝ), ∀ a : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) a →
      (∀ l' ≤ l, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l' a ξ‖ ≤ C l' * ξ ^ (m - l')) →
      ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l (fun x => f x * a x) ξ‖ ≤ K * ξ ^ (m₁ + m - l) := by
  refine ⟨1 + |∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * F i * C (l - i)|, by positivity,
    fun a ha haC ξ hξ => ?_⟩
  have hξ0 : 0 < ξ := by linarith
  refine (c04o_aux_symb_mul f a ξ hξ0 hf.contDiffAt ha.contDiffAt m₁ m F C l
    (fun i hi => hF i hi ξ hξ) (fun i hi => haC i hi ξ hξ)).trans ?_
  have := rpow_pos_of_pos hξ0 (m₁ + m - l)
  gcongr
  linarith [le_abs_self (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * F i * C (l - i))]

theorem c04o_aux_trunc_contDiff {ρ' : ℝ → ℝ} (hρ : c04_IsTruncation ρ') (M : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ((ρ' (x / M) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hρ.1.comp (contDiff_id.div_const M))

theorem c04o_aux_tail_contDiff {L : ℝ} {θ : ℝ → ℝ} (hθ : c04o_aux_IsTailCutoff L θ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ((1 - θ x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hθ.1)

theorem c04o_aux_trunc_zero {ρ' : ℝ → ℝ} (hρ : c04_IsTruncation ρ') {M : ℝ} (hM : 0 < M) (x : ℝ)
    (hx : x ∉ Icc (-(2 * M)) (2 * M)) : ρ' (x / M) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have h2 := hρ.2.2.2 h
  apply hx
  constructor
  · have := h2.1; rw [le_div_iff₀ hM] at this; linarith
  · have := h2.2; rw [div_le_iff₀ hM] at this; linarith

theorem c04o_aux_trunc_one {ρ' : ℝ → ℝ} (hρ : c04_IsTruncation ρ') {M : ℝ} (hM : 0 < M) :
    EqOn (fun x => ((ρ' (x / M) : ℝ) : ℂ)) (fun _ => 1) (Ioo (-M) M) := by
  intro x hx
  simp only
  rw [hρ.2.2.1 (x / M) ⟨by rw [le_div_iff₀ hM]; linarith [hx.1], by
    rw [div_le_iff₀ hM]; linarith [hx.2]⟩]
  simp

/-! ### Cutoff symbols, phase reciprocal and one integration-by-parts step -/

/-- Blueprint: lem:c04_osc_cutoff_symbols.  Symbol bounds for `(iξ)^j a`, for the truncations
`a_M = ρ(·/M) a`, and for the tail pieces `b_M = ρ(·/M)(1-θ)a`, `b_∞ = (1-θ)a`, with constants
depending only on the listed data (in particular never on `M` or on `a` beyond its constants `C_l`).
Each bound of order `l` only assumes the symbol bounds of `a` up to order `l`. -/
theorem c04_osc_cutoff_symbols (m : ℝ) (C : ℕ → ℝ) :
    -- multiplication by `(iξ)^j`: uniform constants
    (∀ j l : ℕ, ∃ K > (0 : ℝ), ∀ a : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) a → (∀ ξ ≤ 1, a ξ = 0) →
      (∀ l' ≤ l, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l' a ξ‖ ≤ C l' * ξ ^ (m - l')) →
      ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l (fun x : ℝ => (Complex.I * (x : ℂ)) ^ j * a x) ξ‖ ≤
        K * ξ ^ (m + j - l)) ∧
    (∀ a ∈ c04_osc_symbol m, ∀ j : ℕ,
      (fun x : ℝ => (Complex.I * (x : ℂ)) ^ j * a x) ∈ c04_osc_symbol (m + j)) ∧
    -- truncation `a_M = ρ(·/M) a`
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ l : ℕ, ∃ B > (0 : ℝ), ∀ a : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) a → (∀ ξ ≤ 1, a ξ = 0) →
      (∀ l' ≤ l, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l' a ξ‖ ≤ C l' * ξ ^ (m - l')) →
      ∀ M : ℝ, 1 ≤ M → ∀ ξ, 1 ≤ ξ →
        ‖iteratedDeriv l (fun x => (ρ' (x / M) : ℂ) * a x) ξ‖ ≤ B * ξ ^ (m - l)) ∧
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ a : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) a →
      (∀ ξ ≤ 1, a ξ = 0) → ∀ M : ℝ, 1 ≤ M →
      ContDiff ℝ (⊤ : ℕ∞) (fun x => (ρ' (x / M) : ℂ) * a x) ∧
      HasCompactSupport (fun x => (ρ' (x / M) : ℂ) * a x) ∧
      (∀ ξ ≤ 1, (ρ' (ξ / M) : ℂ) * a ξ = 0) ∧
      ∀ l : ℕ, ∀ ξ, 0 < ξ → ξ < M →
        iteratedDeriv l (fun x => (ρ' (x / M) : ℂ) * a x) ξ = iteratedDeriv l a ξ) ∧
    -- tail pieces `b_M = ρ(·/M)(1-θ)a`, `b_∞ = (1-θ)a`
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ L : ℝ, 1 ≤ L → ∀ θ : ℝ → ℝ,
      c04o_aux_IsTailCutoff L θ → ∀ l : ℕ, ∃ B > (0 : ℝ), ∀ a : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) a → (∀ ξ ≤ 1, a ξ = 0) →
      (∀ l' ≤ l, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l' a ξ‖ ≤ C l' * ξ ^ (m - l')) →
      (∀ M : ℝ, 1 ≤ M → ∀ ξ, 1 ≤ ξ →
        ‖iteratedDeriv l (fun x => (ρ' (x / M) : ℂ) * ((1 - θ x : ℝ) : ℂ) * a x) ξ‖ ≤
          B * ξ ^ (m - l)) ∧
      ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l (fun x => ((1 - θ x : ℝ) : ℂ) * a x) ξ‖ ≤ B * ξ ^ (m - l)) ∧
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ L : ℝ, 1 ≤ L → ∀ θ : ℝ → ℝ,
      c04o_aux_IsTailCutoff L θ → ∀ a : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) a → (∀ ξ ≤ 1, a ξ = 0) →
      ContDiff ℝ (⊤ : ℕ∞) (fun x => ((1 - θ x : ℝ) : ℂ) * a x) ∧
      (∀ ξ ≤ L, ((1 - θ ξ : ℝ) : ℂ) * a ξ = 0) ∧
      ∀ M : ℝ, 1 ≤ M →
        ContDiff ℝ (⊤ : ℕ∞) (fun x => (ρ' (x / M) : ℂ) * ((1 - θ x : ℝ) : ℂ) * a x) ∧
        HasCompactSupport (fun x => (ρ' (x / M) : ℂ) * ((1 - θ x : ℝ) : ℂ) * a x) ∧
        (∀ ξ ≤ L, (ρ' (ξ / M) : ℂ) * ((1 - θ ξ : ℝ) : ℂ) * a ξ = 0) ∧
        ∀ l : ℕ, ∀ ξ, 0 < ξ → ξ < M →
          iteratedDeriv l (fun x => (ρ' (x / M) : ℂ) * ((1 - θ x : ℝ) : ℂ) * a x) ξ =
            iteratedDeriv l (fun x => ((1 - θ x : ℝ) : ℂ) * a x) ξ) := by
  -- part (iξ)^j, for arbitrary constants
  have hmono : ∀ (C' : ℕ → ℝ) (j l : ℕ), ∃ K > (0 : ℝ), ∀ a : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) a →
      (∀ ξ ≤ 1, a ξ = 0) →
      (∀ l' ≤ l, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l' a ξ‖ ≤ C' l' * ξ ^ (m - l')) →
      ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l (fun x : ℝ => (Complex.I * (x : ℂ)) ^ j * a x) ξ‖ ≤
        K * ξ ^ (m + j - l) := by
    intro C' j l
    obtain ⟨K, hK, hKa⟩ := c04o_aux_symb_mul' (fun x : ℝ => (Complex.I * (x : ℂ)) ^ j)
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).pow j) j m
      (fun i => (j.descFactorial i : ℝ)) C' l
      (fun i _ ξ hξ => c04o_aux_monomial_symb j i ξ (by linarith))
    refine ⟨K, hK, fun a ha _ haC ξ hξ => ?_⟩
    have := hKa a ha haC ξ hξ
    rwa [show (j : ℝ) + m - l = m + j - l by ring] at this
  -- truncation, for arbitrary constants
  have htr : ∀ (C' : ℕ → ℝ) (ρ' : ℝ → ℝ), c04_IsTruncation ρ' → ∀ l : ℕ, ∃ B > (0 : ℝ),
      ∀ a : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) a →
      (∀ l' ≤ l, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l' a ξ‖ ≤ C' l' * ξ ^ (m - l')) →
      ∀ M : ℝ, 1 ≤ M → ∀ ξ, 1 ≤ ξ →
        ‖iteratedDeriv l (fun x => (ρ' (x / M) : ℂ) * a x) ξ‖ ≤ B * ξ ^ (m - l) := by
    intro C' ρ' hρ l
    choose R hR0 hR using c04o_aux_trunc_symb hρ
    have hK := fun M => c04o_aux_symb_mul' (fun x => ((ρ' (x / M) : ℝ) : ℂ))
      (c04o_aux_trunc_contDiff hρ M) 0 m R C' l
    -- uniform constant: the one from `symb_mul'` does not depend on `M`
    refine ⟨1 + |∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * R i * C' (l - i)|, by positivity,
      fun a ha haC M hM ξ hξ => ?_⟩
    have hξ0 : 0 < ξ := by linarith
    refine (c04o_aux_symb_mul _ a ξ hξ0 (c04o_aux_trunc_contDiff hρ M).contDiffAt ha.contDiffAt
      0 m R C' l (fun i _ => hR i M (by linarith) ξ hξ0) (fun i hi => haC i hi ξ hξ)).trans ?_
    rw [zero_add]
    have := rpow_pos_of_pos hξ0 (m - l)
    gcongr
    linarith [le_abs_self (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * R i * C' (l - i))]
  -- tail pieces
  have htail : ∀ (C' : ℕ → ℝ) (ρ' : ℝ → ℝ), c04_IsTruncation ρ' → ∀ L : ℝ, 1 ≤ L →
      ∀ θ : ℝ → ℝ, c04o_aux_IsTailCutoff L θ → ∀ l : ℕ, ∃ B > (0 : ℝ), ∀ a : ℝ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) a → (∀ ξ ≤ 1, a ξ = 0) →
      (∀ l' ≤ l, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l' a ξ‖ ≤ C' l' * ξ ^ (m - l')) →
      (∀ M : ℝ, 1 ≤ M → ∀ ξ, 1 ≤ ξ →
        ‖iteratedDeriv l (fun x => (ρ' (x / M) : ℂ) * ((1 - θ x : ℝ) : ℂ) * a x) ξ‖ ≤
          B * ξ ^ (m - l)) ∧
      ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l (fun x => ((1 - θ x : ℝ) : ℂ) * a x) ξ‖ ≤
        B * ξ ^ (m - l) := by
    intro C' ρ' hρ L hL θ hθ l
    choose R hR0 hR using c04o_aux_trunc_symb hρ
    choose H hH0 hH using c04o_aux_tail_symb hL hθ
    set E : ℕ → ℝ := fun i => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * R k * H (i - k)
    have hE : ∀ M : ℝ, 1 ≤ M → ∀ i : ℕ, ∀ ξ : ℝ, 1 ≤ ξ →
        ‖iteratedDeriv i (fun x => ((ρ' (x / M) : ℝ) : ℂ) * ((1 - θ x : ℝ) : ℂ)) ξ‖ ≤
          E i * ξ ^ ((0 + 0 : ℝ) - i) := fun M hM i ξ hξ =>
      c04o_aux_symb_mul _ _ ξ (by linarith) (c04o_aux_trunc_contDiff hρ M).contDiffAt
        (c04o_aux_tail_contDiff hθ).contDiffAt 0 0 R H i
        (fun k _ => hR k M (by linarith) ξ (by linarith)) (fun k _ => hH k ξ hξ)
    set S1 := ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * E i * C' (l - i)
    set S2 := ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * H i * C' (l - i)
    refine ⟨1 + |S1| + |S2|, by positivity, fun a ha _ haC => ⟨fun M hM ξ hξ => ?_, fun ξ hξ => ?_⟩⟩
    · have hξ0 : 0 < ξ := by linarith
      refine (c04o_aux_symb_mul (fun x => ((ρ' (x / M) : ℝ) : ℂ) * ((1 - θ x : ℝ) : ℂ)) a ξ hξ0
        ((c04o_aux_trunc_contDiff hρ M).mul (c04o_aux_tail_contDiff hθ)).contDiffAt
        ha.contDiffAt (0 + 0) m E C' l (fun i _ => hE M hM i ξ hξ)
        (fun i hi => haC i hi ξ hξ)).trans ?_
      rw [show (0 + 0 : ℝ) + m - l = m - l by ring]
      have := rpow_pos_of_pos hξ0 (m - l)
      gcongr
      linarith [le_abs_self S1, abs_nonneg S2]
    · have hξ0 : 0 < ξ := by linarith
      refine (c04o_aux_symb_mul _ a ξ hξ0 (c04o_aux_tail_contDiff hθ).contDiffAt
        ha.contDiffAt 0 m H C' l (fun i _ => hH i ξ hξ) (fun i hi => haC i hi ξ hξ)).trans ?_
      rw [zero_add]
      have := rpow_pos_of_pos hξ0 (m - l)
      gcongr
      linarith [le_abs_self S2, abs_nonneg S1]
  refine ⟨hmono C, ?_, fun ρ' hρ l => ?_, ?_, fun ρ' hρ L hL θ hθ l => ?_, ?_⟩
  · intro a ha j
    choose Ca hCa using ha.2.2
    refine ⟨((contDiff_const.mul Complex.ofRealCLM.contDiff).pow j).mul ha.1,
      fun ξ hξ => by simp [ha.2.1 ξ hξ], fun l => ?_⟩
    obtain ⟨K, _, hK⟩ := hmono Ca j l
    exact ⟨K, hK a ha.1 ha.2.1 (fun l' _ ξ hξ => hCa l' ξ hξ)⟩
  · obtain ⟨B, hB, hBa⟩ := htr C ρ' hρ l
    exact ⟨B, hB, fun a ha _ haC => hBa a ha haC⟩
  · intro ρ' hρ a ha ha1 M hM
    have hM0 : 0 < M := by linarith
    refine ⟨(c04o_aux_trunc_contDiff hρ M).mul ha, ?_, fun ξ hξ => by simp [ha1 ξ hξ],
      fun l ξ hξ hξM => ?_⟩
    · refine HasCompactSupport.intro (K := Icc (-(2 * M)) (2 * M)) isCompact_Icc fun x hx => ?_
      simp [c04o_aux_trunc_zero hρ hM0 x hx]
    · refine Set.EqOn.iteratedDeriv_of_isOpen (s := Ioo (-M) M) (fun x hx => ?_) isOpen_Ioo l
        (show ξ ∈ Ioo (-M) M from ⟨by linarith, hξM⟩)
      have := c04o_aux_trunc_one hρ hM0 hx
      simp only at this
      simp only [this, one_mul]
  · obtain ⟨B, hB, hBa⟩ := htail C ρ' hρ L hL θ hθ l
    exact ⟨B, hB, hBa⟩
  · intro ρ' hρ L hL θ hθ a ha ha1
    have hvan : ∀ ξ ≤ L, ((1 - θ ξ : ℝ) : ℂ) * a ξ = 0 := by
      intro ξ hξ
      rcases le_or_gt ξ 1 with h | h
      · simp [ha1 ξ h]
      · rw [hθ.2.2.2.1 ξ ⟨by linarith, hξ⟩]; simp
    refine ⟨(c04o_aux_tail_contDiff hθ).mul ha, hvan, fun M hM => ?_⟩
    have hM0 : 0 < M := by linarith
    refine ⟨((c04o_aux_trunc_contDiff hρ M).mul (c04o_aux_tail_contDiff hθ)).mul ha, ?_,
      fun ξ hξ => by rw [mul_assoc, hvan ξ hξ, mul_zero], fun l ξ hξ hξM => ?_⟩
    · refine HasCompactSupport.intro (K := Icc (-(2 * M)) (2 * M)) isCompact_Icc fun x hx => ?_
      simp [c04o_aux_trunc_zero hρ hM0 x hx]
    · refine Set.EqOn.iteratedDeriv_of_isOpen (s := Ioo (-M) M) (fun x hx => ?_) isOpen_Ioo l
        (show ξ ∈ Ioo (-M) M from ⟨by linarith, hξM⟩)
      have := c04o_aux_trunc_one hρ hM0 hx
      simp only at this
      simp only [this, one_mul]

/-- Blueprint: lem:c04_osc_phase_reciprocal.  With `φ_y(ξ) = yξ - Φ₀(ξ)` and
`q_y = (y - ξ^p)⁻¹`: nonstationarity and reciprocal derivative bounds, (i) for `|y| ≤ Y`,
`ξ ≥ (2Y)^{1/p} + 2`, (ii) for `y ≤ -1`, `ξ ≥ 1`.  Smoothness is asserted at every point of the
regions (`ContDiffAt`). -/
theorem c04_osc_phase_reciprocal (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ l : ℕ, ∃ D > (0 : ℝ),
      (∀ Y : ℝ, 1 ≤ Y → ∀ y : ℝ, |y| ≤ Y → ∀ ξ : ℝ, (2 * Y) ^ (1 / p) + 2 ≤ ξ →
        ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (y - x ^ p)⁻¹) ξ ∧
        (1 / 2) * ξ ^ p ≤ |deriv (fun x : ℝ => y * x - Phi0 p x) ξ| ∧
        |iteratedDeriv l (fun x : ℝ => (y - x ^ p)⁻¹) ξ| ≤ D * ξ ^ (-p - l)) ∧
      (∀ y : ℝ, y ≤ -1 → ∀ ξ : ℝ, 1 ≤ ξ →
        ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (y - x ^ p)⁻¹) ξ ∧
        |deriv (fun x : ℝ => y * x - Phi0 p x) ξ| = |y| + ξ ^ p ∧
        |iteratedDeriv l (fun x : ℝ => (y - x ^ p)⁻¹) ξ| ≤ D * (|y| + ξ ^ p)⁻¹ * ξ ^ (-(l : ℝ)) ∧
        D * (|y| + ξ ^ p)⁻¹ * ξ ^ (-(l : ℝ)) ≤ D * |y|⁻¹ * ξ ^ (-(l : ℝ))) := by
  intro l
  set P : ℕ → ℝ := fun r => |(descPochhammer ℝ r).eval p| with hPdef
  set G : ℕ → ℝ := fun r => 2 * P r with hGdef
  have hG : ∀ r, 0 ≤ G r := fun r => by positivity
  set D0 := c04o_aux_recD G l with hD0def
  have hD0 : 0 ≤ D0 := c04o_aux_recD_nonneg G hG l
  -- generic facts at a point `ξ > 0`
  have hcd : ∀ y ξ : ℝ, 0 < ξ → y - ξ ^ p ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (y - x ^ p)⁻¹) ξ := fun y ξ hξ hne =>
    (contDiffAt_const.sub (Real.contDiffAt_rpow_const_of_ne hξ.ne')).inv hne
  have hgd : ∀ y ξ : ℝ, 0 < ξ → ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => y - x ^ p) ξ :=
    fun y ξ hξ => contDiffAt_const.sub (Real.contDiffAt_rpow_const_of_ne hξ.ne')
  have hdr : ∀ y ξ W : ℝ, 0 < ξ → 0 < W → ξ ^ p ≤ 2 * W → ∀ r, 1 ≤ r →
      |iteratedDeriv r (fun x : ℝ => y - x ^ p) ξ| ≤ G r * W * ξ ^ (-(r : ℝ)) := by
    intro y ξ W hξ hW hpW r hr
    rw [c04o_aux_iteratedDeriv_sub_rpow p y ξ hξ r hr, sub_eq_add_neg, rpow_add hξ]
    have h1 : 0 ≤ P r := abs_nonneg _
    have h2 : 0 < ξ ^ (-(r : ℝ)) := rpow_pos_of_pos hξ _
    simp only [hGdef]
    nlinarith [mul_le_mul_of_nonneg_left hpW (mul_nonneg h1 h2.le)]
  refine ⟨2 * D0 + 1, by positivity, ?_, ?_⟩
  · intro Y hY y hy ξ hξ
    have hξ0 : 0 < ξ := by
      have : 0 ≤ (2 * Y) ^ (1 / p) := rpow_nonneg (by linarith) _
      linarith
    have hξp : 2 * Y ≤ ξ ^ p := by
      have h1 : (2 * Y) ^ (1 / p) ≤ ξ := by linarith
      calc 2 * Y = ((2 * Y) ^ (1 / p)) ^ p := by
              rw [one_div, Real.rpow_inv_rpow (by linarith) hp.ne']
        _ ≤ ξ ^ p := rpow_le_rpow (rpow_nonneg (by linarith) _) h1 hp.le
    have hyab := abs_le.1 hy
    have hW : 0 < ξ ^ p / 2 := by positivity
    have hgW : ξ ^ p / 2 ≤ |y - ξ ^ p| := by
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    have hne : y - ξ ^ p ≠ 0 := fun h => by rw [h, abs_zero] at hgW; linarith
    refine ⟨hcd y ξ hξ0 hne, ?_, ?_⟩
    · rw [(c04o_aux_deriv_phase p y ξ hp hξ0).deriv]
      linarith
    · have := c04o_aux_recip_bound G hG (fun x => y - x ^ p) ξ (ξ ^ p / 2) hξ0 hW
        (hgd y ξ hξ0) hgW l (fun r hr _ => hdr y ξ _ hξ0 hW (by linarith) r hr)
      refine this.trans ?_
      have hpl : ξ ^ (-p - l) = (ξ ^ p)⁻¹ * ξ ^ (-(l : ℝ)) := by
        rw [sub_eq_add_neg, rpow_add hξ0, rpow_neg hξ0.le]
      rw [hpl, inv_div]
      have h3 : 0 < ξ ^ (-(l : ℝ)) := rpow_pos_of_pos hξ0 _
      have h4 : 0 < (ξ ^ p)⁻¹ := inv_pos.2 (rpow_pos_of_pos hξ0 _)
      have : 2 / ξ ^ p = 2 * (ξ ^ p)⁻¹ := by rw [div_eq_mul_inv]
      rw [this]
      nlinarith [mul_pos h3 h4]
  · intro y hy ξ hξ
    have hξ0 : 0 < ξ := by linarith
    have hpos : 0 < ξ ^ p := rpow_pos_of_pos hξ0 _
    have hya : |y| = -y := abs_of_neg (by linarith)
    have hW : 0 < |y| + ξ ^ p := by positivity
    have hgW : |y - ξ ^ p| = |y| + ξ ^ p := by
      rw [abs_of_neg (by linarith), hya]; ring
    have hne : y - ξ ^ p ≠ 0 := by intro h; rw [h, abs_zero] at hgW; linarith
    refine ⟨hcd y ξ hξ0 hne, ?_, ?_, ?_⟩
    · rw [(c04o_aux_deriv_phase p y ξ hp hξ0).deriv, hgW]
    · have := c04o_aux_recip_bound G hG (fun x => y - x ^ p) ξ (|y| + ξ ^ p) hξ0 hW
        (hgd y ξ hξ0) hgW.ge l (fun r hr _ => hdr y ξ _ hξ0 hW (by
          have := abs_nonneg y; linarith) r hr)
      refine this.trans ?_
      gcongr
      linarith
    · have hy0 : 0 < |y| := by rw [hya]; linarith
      gcongr
      linarith

/-- Blueprint: lem:c04_osc_ibp_step.  One integration-by-parts step `T_q b = -∂(bq/i)` (zero
extended below `L`): smoothness, flatness, support, Leibniz formula and the one-step bound. -/
theorem c04_osc_ibp_step (L m σ A H : ℝ) (hL : 1 ≤ L) (hA : 0 < A) (hH : 0 < H)
    (b : ℝ → ℂ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbL : ∀ ξ ≤ L, b ξ = 0)
    (q : ℝ → ℝ) (hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (c04o_aux_ibpOp L q b) ∧
    (∀ k : ℕ, ∀ ξ ≤ L, iteratedDeriv k (c04o_aux_ibpOp L q b) ξ = 0) ∧
    tsupport (c04o_aux_ibpOp L q b) ⊆ tsupport b ∧
    (∀ k : ℕ, ∀ ξ, L ≤ ξ → iteratedDeriv k (c04o_aux_ibpOp L q b) ξ =
      Complex.I * ∑ r ∈ Finset.range (k + 2), ((k + 1).choose r : ℂ) *
        iteratedDeriv r b ξ * ((iteratedDeriv (k + 1 - r) q ξ : ℝ) : ℂ)) ∧
    (∀ (k : ℕ) (B D : ℕ → ℝ), (∀ r, 0 ≤ B r) → (∀ r, 0 ≤ D r) →
      (∀ r ≤ k + 1, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r b ξ‖ ≤ B r * A * ξ ^ (m - r)) →
      (∀ r ≤ k + 1, ∀ ξ, L ≤ ξ → |iteratedDeriv r q ξ| ≤ D r * H * ξ ^ (-σ - r)) →
      ∀ ξ, L ≤ ξ → ‖iteratedDeriv k (c04o_aux_ibpOp L q b) ξ‖ ≤
        (∑ r ∈ Finset.range (k + 2), ((k + 1).choose r : ℝ) * B r * D (k + 1 - r)) *
          A * H * ξ ^ (m - 1 - σ - k)) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hg, hT⟩ := c04o_aux_ibpOp_eq L hL0 q b hb hbL hq
  set g := fun x => b x * (q x : ℂ) with hgdef
  have hdg : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := (contDiff_infty_iff_deriv.1 hg).2
  have hTs : ContDiff ℝ (⊤ : ℕ∞) (c04o_aux_ibpOp L q b) := by
    rw [hT]; exact contDiff_const.mul hdg
  have hDer : ∀ k : ℕ, ∀ ξ, iteratedDeriv k (c04o_aux_ibpOp L q b) ξ =
      Complex.I * iteratedDeriv (k + 1) g ξ := by
    intro k ξ
    rw [hT, iteratedDeriv_const_mul_field, iteratedDeriv_succ']
  have hForm : ∀ k : ℕ, ∀ ξ, L ≤ ξ → iteratedDeriv k (c04o_aux_ibpOp L q b) ξ =
      Complex.I * ∑ r ∈ Finset.range (k + 2), ((k + 1).choose r : ℂ) *
        iteratedDeriv r b ξ * ((iteratedDeriv (k + 1 - r) q ξ : ℝ) : ℂ) := by
    intro k ξ hξ
    have hqξ : ContDiffAt ℝ (⊤ : ℕ∞) q ξ := hq.contDiffAt (Ioi_mem_nhds (by linarith))
    have hqc : ContDiffAt ℝ (k + 1 : ℕ) (fun x => ((q x : ℝ) : ℂ)) ξ :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ hqξ).of_le (by exact_mod_cast le_top)
    rw [hDer, hgdef, iteratedDeriv_fun_mul (hb.contDiffAt.of_le (by exact_mod_cast le_top)) hqc]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [c04o_aux_iteratedDeriv_ofReal _ _ _ (hqξ.of_le (c04o_aux_le_top _))]
  refine ⟨hTs, fun k => c04o_aux_flat hTs (fun ξ hξ => by
      unfold c04o_aux_ibpOp; split_ifs with h
      · linarith
      · rfl) k, ?_, hForm, ?_⟩
  · rw [hT]
    refine (tsupport_mul_subset_right).trans (tsupport_deriv_subset.trans ?_)
    exact tsupport_mul_subset_left
  · intro k B D hB0 hD0 hBb hDq ξ hξ
    have hξ0 : 0 < ξ := by linarith
    rw [hForm k ξ hξ, norm_mul, Complex.norm_I, one_mul, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    have hr' : r ≤ k + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
    have hpow : ξ ^ (m - 1 - σ - k) = ξ ^ (m - r) * ξ ^ (-σ - ((k + 1 - r : ℕ) : ℝ)) := by
      rw [← rpow_add hξ0]; congr 1; push_cast [hr']; ring
    rw [hpow]
    have h1 := hBb r hr' ξ hξ
    have h2 := hDq (k + 1 - r) (Nat.sub_le _ _) ξ hξ
    have hc : (0 : ℝ) ≤ ((k + 1).choose r : ℝ) := by positivity
    calc ((k + 1).choose r : ℝ) * ‖iteratedDeriv r b ξ‖ * |iteratedDeriv (k + 1 - r) q ξ|
        ≤ ((k + 1).choose r : ℝ) * (B r * A * ξ ^ (m - r)) *
          (D (k + 1 - r) * H * ξ ^ (-σ - ((k + 1 - r : ℕ) : ℝ))) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (abs_nonneg _)
            (mul_nonneg hc ((norm_nonneg _).trans h1))
      _ = _ := by ring

/-- One step of the integration-by-parts identity for a compactly supported amplitude. -/
theorem c04o_aux_ibp_identity_step (L R : ℝ) (hL : 1 ≤ L) (hLR : L < R) (c : ℝ → ℂ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcL : ∀ ξ ≤ L, c ξ = 0) (hcR : ∀ ξ, R ≤ ξ → ξ ∉ tsupport c)
    (q : ℝ → ℝ) (hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2)))
    (φ : ℝ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ioi 0)) (hqφ : ∀ ξ, L < ξ → q ξ * deriv φ ξ = 1) :
    IntegrableOn (fun ξ => c ξ * Complex.exp (Complex.I * (φ ξ : ℂ))) (Ioi 0) ∧
    IntegrableOn (fun ξ => c04o_aux_ibpOp L q c ξ * Complex.exp (Complex.I * (φ ξ : ℂ))) (Ioi 0) ∧
    ∫ ξ in Ioi (0 : ℝ), c ξ * Complex.exp (Complex.I * (φ ξ : ℂ)) =
      ∫ ξ in Ioi (0 : ℝ), c04o_aux_ibpOp L q c ξ * Complex.exp (Complex.I * (φ ξ : ℂ)) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hg, hT⟩ := c04o_aux_ibpOp_eq L hL0 q c hc hcL hq
  have hs := c04_osc_ibp_step L 0 0 1 1 hL one_pos one_pos c hc hcL q hq
  set E : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * (φ ξ : ℂ)) with hEdef
  have hsub : Icc L R ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hL0 hx.1
  have hEc : ContinuousOn E (Icc L R) :=
    (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (hφ.continuousOn.mono hsub))))
  have hTR : ∀ ξ, R ≤ ξ → c04o_aux_ibpOp L q c ξ = 0 := fun ξ hξ =>
    image_eq_zero_of_notMem_tsupport (fun h => hcR ξ hξ (hs.2.2.1 h))
  have hcR' : ∀ ξ, R ≤ ξ → c ξ = 0 := fun ξ hξ => image_eq_zero_of_notMem_tsupport (hcR ξ hξ)
  have hTL : ∀ ξ ≤ L, c04o_aux_ibpOp L q c ξ = 0 := fun ξ hξ => by
    simpa using hs.2.1 0 ξ hξ
  have hout : ∀ (u : ℝ → ℂ), (∀ ξ ≤ L, u ξ = 0) → (∀ ξ, R ≤ ξ → u ξ = 0) →
      ∀ ξ, 0 < ξ → ξ ∉ Icc L R → u ξ * E ξ = 0 := by
    intro u h1 h2 ξ _ hξ
    simp only [mem_Icc, not_and_or, not_le] at hξ
    rcases hξ with h | h
    · rw [h1 ξ h.le, zero_mul]
    · rw [h2 ξ h.le, zero_mul]
  obtain ⟨hI1, hE1⟩ := c04o_aux_Icc_supported (f := fun ξ => c ξ * E ξ) hL0 hLR.le (hc.continuous.continuousOn.mul hEc)
    (hout c hcL hcR')
  obtain ⟨hI2, hE2⟩ := c04o_aux_Icc_supported (f := fun ξ => c04o_aux_ibpOp L q c ξ * E ξ) hL0 hLR.le (hs.1.continuous.continuousOn.mul hEc)
    (hout _ hTL hTR)
  refine ⟨hI1, hI2, ?_⟩
  have hii1 : IntervalIntegrable (fun ξ => c ξ * E ξ) volume L R :=
    (hc.continuous.continuousOn.mul hEc).intervalIntegrable_of_Icc hLR.le
  have hii2 : IntervalIntegrable (fun ξ => c04o_aux_ibpOp L q c ξ * E ξ) volume L R :=
    (hs.1.continuous.continuousOn.mul hEc).intervalIntegrable_of_Icc hLR.le
  rw [hE1, hE2, ← sub_eq_zero, ← intervalIntegral.integral_sub hii1 hii2]
  set g := fun x => c x * (q x : ℂ) with hgdef
  set F : ℝ → ℂ := fun ξ => -Complex.I * g ξ * E ξ with hFdef
  have hFd : ∀ x ∈ Ioo L R, HasDerivAt F (c x * E x - c04o_aux_ibpOp L q c x * E x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hL0 hx.1
    have hφd : HasDerivAt φ (deriv φ x) x :=
      ((hφ.contDiffAt (Ioi_mem_nhds hx0)).differentiableAt (by simp)).hasDerivAt
    have hEd : HasDerivAt E (E x * (Complex.I * ((deriv φ x : ℝ) : ℂ))) x := by
      have := (hφd.ofReal_comp.const_mul Complex.I).cexp
      simpa [hEdef] using this
    have hgd : HasDerivAt g (deriv g x) x :=
      (hg.differentiable (by simp) x).hasDerivAt
    have := (hgd.const_mul (-Complex.I)).mul hEd
    convert this using 1
    rw [hT]
    have h1 : ((q x : ℝ) : ℂ) * ((deriv φ x : ℝ) : ℂ) = 1 := by exact_mod_cast hqφ x hx.1
    simp only [hgdef]
    linear_combination (c x * E x * ((q x : ℝ) : ℂ) * ((deriv φ x : ℝ) : ℂ)) * Complex.I_sq -
      (c x * E x) * h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hLR.le ?_ hFd
    (((hc.continuous.continuousOn.mul hEc).sub (hs.1.continuous.continuousOn.mul hEc)).intervalIntegrable_of_Icc hLR.le)]
  · simp [hFdef, hgdef, hcR' R le_rfl, hcL L le_rfl]
  · exact ((continuousOn_const.mul hg.continuous.continuousOn).mul hEc)

/-! ### Iterated integration by parts -/

/-- Blueprint: lem:c04_osc_ibp_iteration.  Iterates `T_q^N b`: smoothness, flatness, support,
bounds `E_{N,k} A H^N ξ^{m-N(1+σ)-k}` with the recurrence coefficients `c04o_aux_E`, finite
dependence of `E_{N,k}`, and the `L¹` bound when `m - N(1+σ) < -1`.
The bound of order `(N,k)` only assumes the derivative bounds of `b`, `q` up to
order `N + k`. -/
theorem c04_osc_ibp_iteration (L m σ A H : ℝ) (hL : 1 ≤ L) (hA : 0 < A) (hH : 0 < H)
    (b : ℝ → ℂ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbL : ∀ ξ ≤ L, b ξ = 0)
    (q : ℝ → ℝ) (hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2)))
    (B D : ℕ → ℝ) (hB0 : ∀ r, 0 ≤ B r) (hD0 : ∀ r, 0 ≤ D r) :
    (∀ N k : ℕ, 0 ≤ c04o_aux_E B D N k) ∧
    (∀ (N k : ℕ) (B' D' : ℕ → ℝ), (∀ r ≤ N + k, B' r = B r) → (∀ r ≤ N + k, D' r = D r) →
      c04o_aux_E B' D' N k = c04o_aux_E B D N k) ∧
    (∀ N : ℕ, ContDiff ℝ (⊤ : ℕ∞) ((c04o_aux_ibpOp L q)^[N] b) ∧
      (∀ ξ ≤ L, ((c04o_aux_ibpOp L q)^[N] b) ξ = 0) ∧
      tsupport ((c04o_aux_ibpOp L q)^[N] b) ⊆ tsupport b) ∧
    (∀ N k : ℕ,
      (∀ r ≤ N + k, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r b ξ‖ ≤ B r * A * ξ ^ (m - r)) →
      (∀ r ≤ N + k, ∀ ξ, L ≤ ξ → |iteratedDeriv r q ξ| ≤ D r * H * ξ ^ (-σ - r)) →
      ∀ ξ, L ≤ ξ → ‖iteratedDeriv k ((c04o_aux_ibpOp L q)^[N] b) ξ‖ ≤
        c04o_aux_E B D N k * A * H ^ N * ξ ^ (m - N * (1 + σ) - k)) ∧
    (∀ N : ℕ, m - N * (1 + σ) < -1 →
      (∀ r ≤ N, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r b ξ‖ ≤ B r * A * ξ ^ (m - r)) →
      (∀ r ≤ N, ∀ ξ, L ≤ ξ → |iteratedDeriv r q ξ| ≤ D r * H * ξ ^ (-σ - r)) →
      IntegrableOn ((c04o_aux_ibpOp L q)^[N] b) (Ioi 0) ∧
      ∫ ξ in Ioi (0 : ℝ), ‖((c04o_aux_ibpOp L q)^[N] b) ξ‖ ≤
        c04o_aux_E B D N 0 * A * H ^ N *
          (L ^ (m - N * (1 + σ) + 1) / (-(m - N * (1 + σ)) - 1))) := by
  set T := c04o_aux_ibpOp L q with hTdef
  have hE0 : ∀ N k : ℕ, 0 ≤ c04o_aux_E B D N k := by
    intro N
    induction N with
    | zero => intro k; exact hB0 k
    | succ n ih =>
      intro k
      exact Finset.sum_nonneg fun r _ => mul_nonneg (mul_nonneg (by positivity) (ih r)) (hD0 _)
  have hEdep : ∀ (N k : ℕ) (B' D' : ℕ → ℝ), (∀ r ≤ N + k, B' r = B r) →
      (∀ r ≤ N + k, D' r = D r) → c04o_aux_E B' D' N k = c04o_aux_E B D N k := by
    intro N
    induction N with
    | zero => intro k B' D' hB' _; exact hB' k (by omega)
    | succ n ih =>
      intro k B' D' hB' hD'
      simp only [c04o_aux_E]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' : r ≤ k + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
      rw [ih r B' D' (fun i hi => hB' i (by omega)) (fun i hi => hD' i (by omega)),
        hD' (k + 1 - r) (by omega)]
  have hReg : ∀ N : ℕ, ContDiff ℝ (⊤ : ℕ∞) (T^[N] b) ∧ (∀ ξ ≤ L, (T^[N] b) ξ = 0) ∧
      tsupport (T^[N] b) ⊆ tsupport b := by
    intro N
    induction N with
    | zero => exact ⟨hb, hbL, subset_rfl⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hs := c04_osc_ibp_step L m σ A H hL hA hH (T^[n] b) h1 h2 q hq
      rw [Function.iterate_succ_apply']
      refine ⟨hs.1, fun ξ hξ => ?_, hs.2.2.1.trans h3⟩
      have := hs.2.1 0 ξ hξ
      simpa using this
  have hBd : ∀ N k : ℕ,
      (∀ r ≤ N + k, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r b ξ‖ ≤ B r * A * ξ ^ (m - r)) →
      (∀ r ≤ N + k, ∀ ξ, L ≤ ξ → |iteratedDeriv r q ξ| ≤ D r * H * ξ ^ (-σ - r)) →
      ∀ ξ, L ≤ ξ → ‖iteratedDeriv k (T^[N] b) ξ‖ ≤
        c04o_aux_E B D N k * A * H ^ N * ξ ^ (m - N * (1 + σ) - k) := by
    intro N
    induction N with
    | zero =>
      intro k hb' _ ξ hξ
      simpa [c04o_aux_E] using hb' k (by omega) ξ hξ
    | succ n ih =>
      intro k hb' hq' ξ hξ
      obtain ⟨h1, h2, _⟩ := hReg n
      have hs := c04_osc_ibp_step L (m - n * (1 + σ)) σ (A * H ^ n) H hL (by positivity) hH
        (T^[n] b) h1 h2 q hq
      have := hs.2.2.2.2 k (c04o_aux_E B D n) D (hE0 n) hD0
        (fun r hr ξ hξ => by
          have := ih r (fun i hi => hb' i (by omega)) (fun i hi => hq' i (by omega)) ξ hξ
          rw [show m - n * (1 + σ) - r = m - (n : ℝ) * (1 + σ) - (r : ℝ) from rfl]
          linarith)
        (fun r hr ξ hξ => hq' r (by omega) ξ hξ) ξ hξ
      rw [Function.iterate_succ_apply']
      refine this.trans (le_of_eq ?_)
      simp only [c04o_aux_E]
      rw [pow_succ]
      push_cast
      ring_nf
  refine ⟨hE0, hEdep, hReg, hBd, ?_⟩
  intro N hd hb' hq' 
  have hL0 : 0 < L := by linarith
  have := c04o_aux_powtail (hReg N).1.continuous hL0 hd (hReg N).2.1
    (c := c04o_aux_E B D N 0 * A * H ^ N) (fun ξ hξ => by
      have := hBd N 0 (fun r hr => hb' r (by omega)) (fun r hr => hq' r (by omega)) ξ hξ
      simpa using this)
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  ring_nf

/-! ### Transfer of symbol bounds -/

/-- Blueprint: lem:c04_osc_ibp_transfer.  Repeated integration by parts with quantified symbol
loss.  The constant `C_{N,k}` is chosen before `L, A, H, b, q` (it depends only on
`N, k, m, σ, B, D`).  The bound of order `(N,k)` only assumes derivative bounds up
to order `N + k`. -/
theorem c04_osc_ibp_transfer (m σ : ℝ) (B D : ℕ → ℝ) (hB0 : ∀ r, 0 ≤ B r) (hD0 : ∀ r, 0 ≤ D r) :
    (∀ N k : ℕ, ∃ C > (0 : ℝ), ∀ L A H : ℝ, 1 ≤ L → 0 < A → 0 < H →
      ∀ b : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) b → (∀ ξ ≤ L, b ξ = 0) →
      ∀ q : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2)) →
      (∀ r ≤ N + k, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r b ξ‖ ≤ B r * A * ξ ^ (m - r)) →
      (∀ r ≤ N + k, ∀ ξ, L ≤ ξ → |iteratedDeriv r q ξ| ≤ D r * H * ξ ^ (-σ - r)) →
      ContDiff ℝ (⊤ : ℕ∞) ((c04o_aux_ibpOp L q)^[N] b) ∧
      (∀ ξ ≤ L, ((c04o_aux_ibpOp L q)^[N] b) ξ = 0) ∧
      ∀ ξ, L ≤ ξ → ‖iteratedDeriv k ((c04o_aux_ibpOp L q)^[N] b) ξ‖ ≤
        C * A * H ^ N * ξ ^ (m - N * (1 + σ) - k)) ∧
    (∀ N : ℕ, m - N * (1 + σ) < -1 → ∀ L A H : ℝ, 1 ≤ L → 0 < A → 0 < H →
      ∀ b : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) b → (∀ ξ ≤ L, b ξ = 0) →
      ∀ q : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2)) →
      (∀ r ≤ N, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r b ξ‖ ≤ B r * A * ξ ^ (m - r)) →
      (∀ r ≤ N, ∀ ξ, L ≤ ξ → |iteratedDeriv r q ξ| ≤ D r * H * ξ ^ (-σ - r)) →
      IntegrableOn ((c04o_aux_ibpOp L q)^[N] b) (Ioi 0)) ∧
    (∀ L : ℝ, 1 ≤ L → ∀ b : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) b → (∀ ξ ≤ L, b ξ = 0) →
      HasCompactSupport b →
      ∀ q : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2)) →
      ∀ φ : ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) φ (Ioi 0) → (∀ ξ, L < ξ → q ξ * deriv φ ξ = 1) →
      ∀ N : ℕ,
        IntegrableOn (fun ξ => b ξ * Complex.exp (Complex.I * (φ ξ : ℂ))) (Ioi 0) ∧
        IntegrableOn (fun ξ => ((c04o_aux_ibpOp L q)^[N] b) ξ *
          Complex.exp (Complex.I * (φ ξ : ℂ))) (Ioi 0) ∧
        ∫ ξ in Ioi (0 : ℝ), b ξ * Complex.exp (Complex.I * (φ ξ : ℂ)) =
          ∫ ξ in Ioi (0 : ℝ), ((c04o_aux_ibpOp L q)^[N] b) ξ *
            Complex.exp (Complex.I * (φ ξ : ℂ))) := by
  refine ⟨fun N k => ⟨1 + c04o_aux_E B D N k, ?_, fun L A H hL hA hH b hb hbL q hq hBb hDq => ?_⟩,
    fun N hd L A H hL hA hH b hb hbL q hq hBb hDq => ?_, ?_⟩
  · have := (c04_osc_ibp_iteration 1 m σ 1 1 le_rfl one_pos one_pos 0 contDiff_const
      (fun _ _ => rfl) 0 contDiffOn_const B D hB0 hD0).1 N k
    linarith
  · have hit := c04_osc_ibp_iteration L m σ A H hL hA hH b hb hbL q hq B D hB0 hD0
    refine ⟨(hit.2.2.1 N).1, (hit.2.2.1 N).2.1, fun ξ hξ => ?_⟩
    refine (hit.2.2.2.1 N k hBb hDq ξ hξ).trans ?_
    have hξ0 : 0 < ξ := by linarith
    gcongr
    linarith
  · exact ((c04_osc_ibp_iteration L m σ A H hL hA hH b hb hbL q hq B D hB0 hD0).2.2.2.2 N hd
      hBb hDq).1
  · intro L hL b hb hbL hbc q hq φ hφ hqφ
    obtain ⟨R0, hR0⟩ := hbc.isCompact.bddAbove
    set R := max (R0 + 1) (L + 1) with hRdef
    have hLR : L < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hreg := (c04_osc_ibp_iteration L 0 0 1 1 hL one_pos one_pos b hb hbL q hq
      (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl)).2.2.1
    have hRt : ∀ N : ℕ, ∀ ξ, R ≤ ξ → ξ ∉ tsupport ((c04o_aux_ibpOp L q)^[N] b) := by
      intro N ξ hξ h
      have := hR0 ((hreg N).2.2 h)
      have : R0 + 1 ≤ ξ := le_trans (le_max_left _ _) hξ
      linarith
    intro N
    induction N with
    | zero =>
      have := c04o_aux_ibp_identity_step L R hL hLR b hb hbL (hRt 0) q hq φ hφ hqφ
      exact ⟨this.1, this.1, rfl⟩
    | succ n ih =>
      have := c04o_aux_ibp_identity_step L R hL hLR _ (hreg n).1 (hreg n).2.1 (hRt n) q hq φ hφ hqφ
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1, this.2.1, ih.2.2.trans this.2.2⟩

/-! ### Helpers for the limit and parameter-derivative statements -/

/-- The fixed truncation `ρ = GSQG.rho` is admissible. -/
theorem c04o_aux_rho_trunc : c04_IsTruncation rho := by
  refine ⟨?_, fun t => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun t ht => ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      have : ∀ᶠ ξ in 𝓝 (0 : ℝ), |ξ| < 1 := by
        have := (continuous_abs.tendsto (0 : ℝ)); rw [abs_zero] at this
        exact this.eventually (gt_mem_nhds one_pos)
      filter_upwards [this] with ξ hξ
      unfold rho
      exact Real.smoothTransition.one_of_one_le (by linarith)
    · unfold rho
      exact Real.smoothTransition.contDiff.contDiffAt.comp x
        (contDiffAt_const.sub (contDiffAt_abs hx))
  · unfold rho; exact Real.smoothTransition.one_of_one_le (by linarith [abs_le.2 ⟨ht.1, ht.2⟩])
  · refine closure_minimal (fun x hx => ?_) isClosed_Icc
    by_contra h
    apply hx
    unfold rho
    apply Real.smoothTransition.zero_of_nonpos
    have : 2 < |x| := by
      by_contra h'; exact h (abs_le.mp (not_lt.mp h'))
    linarith

theorem c04o_aux_Phi0_cont (p : ℝ) (hp : 0 < p) : Continuous (fun x => Phi0 p x) := by
  unfold Phi0
  exact (continuous_id.mul (continuous_abs.rpow_const fun _ => Or.inr hp.le)).div_const _

theorem c04o_aux_eiphase_cont (p y : ℝ) (hp : 0 < p) : Continuous (fun ξ => c04_eiphase p y ξ) := by
  unfold c04_eiphase
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    ((continuous_const.mul continuous_id).sub (c04o_aux_Phi0_cont p hp))))

theorem c04o_aux_eiphase_norm (p y ξ : ℝ) : ‖c04_eiphase p y ξ‖ = 1 := by
  unfold c04_eiphase
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _

theorem c04o_aux_Phi0_smooth (p : ℝ) (hp : 0 < p) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => Phi0 p x) (Ioi 0) := by
  have : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ (p + 1) / (p + 1)) (Ioi 0) := fun x hx =>
    ((Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)).div_const _).contDiffWithinAt
  refine this.congr fun x hx => ?_
  have hx' : (0 : ℝ) < x := hx
  unfold Phi0
  rw [abs_of_pos hx', rpow_add hx', rpow_one, mul_comm (x ^ p) x]

/-- Locality of `T_q`. -/
theorem c04o_aux_ibpOp_local (L : ℝ) (q : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U) {c₁ c₂ : ℝ → ℂ}
    (h : EqOn c₁ c₂ U) (N : ℕ) : EqOn ((c04o_aux_ibpOp L q)^[N] c₁) ((c04o_aux_ibpOp L q)^[N] c₂) U := by
  induction N with
  | zero => exact h
  | succ n ih =>
    intro ξ hξ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    generalize (c04o_aux_ibpOp L q)^[n] c₁ = g₁ at ih ⊢
    generalize (c04o_aux_ibpOp L q)^[n] c₂ = g₂ at ih ⊢
    unfold c04o_aux_ibpOp
    split_ifs with hL
    · congr 1
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hU.mem_nhds hξ] with x hx
      rw [ih hx]
    · rfl

theorem c04o_aux_q_smooth (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Y : ℝ) (hY : 1 ≤ Y) (y : ℝ)
    (hy : |y| ≤ Y) (L : ℝ) (hL : (2 * Y) ^ (1 / p) + 2 ≤ L) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => (y - x ^ p)⁻¹) (Ioi (L / 2)) := by
  intro ξ hξ
  have hξ' : L / 2 < ξ := hξ
  set x0 := (2 * Y) ^ (1 / p) with hx0
  have hx00 : 0 ≤ x0 := rpow_nonneg (by linarith) _
  have hx0p : x0 ^ p = 2 * Y := by rw [hx0, one_div, Real.rpow_inv_rpow (by linarith) hp.ne']
  have h1 : x0 / 2 < ξ := by linarith
  have h2 : (x0 / 2) ^ p < ξ ^ p := rpow_lt_rpow (by positivity) h1 hp
  have h3 : (2 : ℝ) ^ p ≤ 2 := by
    calc (2 : ℝ) ^ p ≤ 2 ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
      _ = 2 := rpow_one 2
  have h4 : Y ≤ (x0 / 2) ^ p := by
    rw [div_rpow hx00 (by norm_num), hx0p, le_div_iff₀ (by positivity)]
    nlinarith
  have hne : y - ξ ^ p ≠ 0 := by
    have := (abs_le.1 hy).2
    intro h; linarith
  have hξ0 : 0 < ξ := lt_of_le_of_lt (by positivity) h1
  exact ((contDiffAt_const.sub (Real.contDiffAt_rpow_const_of_ne hξ0.ne')).inv hne).contDiffWithinAt

/-- `ρ(·/L)` is a tail cutoff. -/
theorem c04o_aux_rho_tail (L : ℝ) (hL : 0 < L) : c04o_aux_IsTailCutoff L (fun x => rho (x / L)) := by
  have hr := c04o_aux_rho_trunc
  refine ⟨hr.1.comp (contDiff_id.div_const L), ?_, fun x => hr.2.1 _, fun x hx => hr.2.2.1 _ ?_,
    fun x hx => ?_⟩
  · refine HasCompactSupport.intro (K := Icc (-(2 * L)) (2 * L)) isCompact_Icc fun x hx => ?_
    exact c04o_aux_trunc_zero hr hL x hx
  · constructor
    · have : 0 ≤ x / L := div_nonneg hx.1 hL.le
      linarith
    · rw [div_le_iff₀ hL]; linarith [hx.2]
  · simp only
    unfold rho
    apply Real.smoothTransition.zero_of_nonpos
    have : 2 ≤ x / L := by rw [le_div_iff₀ hL]; linarith
    rw [abs_of_pos (by linarith)]; linarith

/-- Compactly supported continuous amplitudes give integrable oscillatory integrands. -/
theorem c04o_aux_cpt_int (p y : ℝ) (hp : 0 < p) {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    IntegrableOn (fun ξ => f ξ * c04_eiphase p y ξ) (Ioi 0) :=
  ((hf.mul (c04o_aux_eiphase_cont p y hp)).integrable_of_hasCompactSupport
    (hc.mul_right)).integrableOn

/-- The core estimate behind `lem:c04_osc_cutoff_limit`. -/
theorem c04o_aux_core (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℝ) (a : ℝ → ℂ)
    (ha : a ∈ c04_osc_symbol m) (Y : ℝ) (hY : 1 ≤ Y) (L : ℝ) (hL : (2 * Y) ^ (1 / p) + 2 ≤ L)
    (θ : ℝ → ℝ) (hθ : c04o_aux_IsTailCutoff L θ) (N : ℕ) (hN : m - N * (1 + p) < -1)
    (ρ' : ℝ → ℝ) (hρ : c04_IsTruncation ρ') :
    ∃ C > (0 : ℝ), ∀ y : ℝ, |y| ≤ Y →
      IntegrableOn (fun ξ => (θ ξ : ℂ) * a ξ * c04_eiphase p y ξ) (Ioi 0) ∧
      IntegrableOn (fun ξ => ((c04o_aux_ibpOp L (fun x => (y - x ^ p)⁻¹))^[N]
          (fun x => ((1 - θ x : ℝ) : ℂ) * a x)) ξ * c04_eiphase p y ξ) (Ioi 0) ∧
      ∀ M : ℝ, 2 * L ≤ M →
        ‖(∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ) -
          ((∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * c04_eiphase p y ξ) +
            ∫ ξ in Ioi (0 : ℝ), ((c04o_aux_ibpOp L (fun x => (y - x ^ p)⁻¹))^[N]
              (fun x => ((1 - θ x : ℝ) : ℂ) * a x)) ξ * c04_eiphase p y ξ)‖ ≤
          C * M ^ (m - N * (1 + p) + 1) := by
  have hx0 : 0 ≤ (2 * Y) ^ (1 / p) := rpow_nonneg (by linarith) _
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  choose Ca hCa using ha.2.2
  have hsym := c04_osc_cutoff_symbols m Ca
  choose Bf hBpos hBf using fun l => hsym.2.2.2.2.1 ρ' hρ L hL1 θ hθ l
  obtain ⟨hbs, hbv, hbM⟩ := hsym.2.2.2.2.2 ρ' hρ L hL1 θ hθ a ha.1 ha.2.1
  choose Df hDpos hDf using c04_osc_phase_reciprocal p hp hp1
  obtain ⟨Ct, hCt, hCtf⟩ := (c04_osc_ibp_transfer m p Bf Df (fun r => (hBpos r).le)
    (fun r => (hDpos r).le)).1 N 0
  have hId := (c04_osc_ibp_transfer m p Bf Df (fun r => (hBpos r).le)
    (fun r => (hDpos r).le)).2.2
  set d := m - N * (1 + p) with hd
  have hd1 : 0 < -d - 1 := by linarith
  refine ⟨2 * Ct / (-d - 1), by positivity, fun y hy => ?_⟩
  set q : ℝ → ℝ := fun x => (y - x ^ p)⁻¹ with hqdef
  have hq := c04o_aux_q_smooth p hp hp1 Y hY y hy L hL
  set T := c04o_aux_ibpOp L q with hTdef
  set binf : ℝ → ℂ := fun x => ((1 - θ x : ℝ) : ℂ) * a x with hbinf
  set e : ℝ → ℂ := fun ξ => c04_eiphase p y ξ with hedef
  have hec : Continuous e := c04o_aux_eiphase_cont p y hp
  have hen : ∀ ξ, ‖e ξ‖ = 1 := fun ξ => c04o_aux_eiphase_norm p y ξ
  have hqb : ∀ r ≤ N + 0, ∀ ξ, L ≤ ξ → |iteratedDeriv r q ξ| ≤ Df r * 1 * ξ ^ (-p - r) :=
    fun r _ ξ hξ => by
      rw [mul_one]; exact ((hDf r).1 Y hY y hy ξ (by linarith)).2.2
  have hbib : ∀ r ≤ N + 0, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r binf ξ‖ ≤ Bf r * 1 * ξ ^ (m - r) :=
    fun r _ ξ hξ => by
      rw [mul_one]
      exact ((hBf r) a ha.1 ha.2.1 (fun l' _ ξ hξ => hCa l' ξ hξ)).2 ξ (by linarith)
  obtain ⟨hTis, hTiv, hTib⟩ := hCtf L 1 1 hL1 one_pos one_pos binf hbs hbv q hq hbib hqb
  have hTib' : ∀ ξ, L ≤ ξ → ‖(T^[N] binf) ξ‖ ≤ Ct * ξ ^ d := fun ξ hξ => by
    simpa using hTib ξ hξ
  have hTie : ∀ ξ, L ≤ ξ → ‖(T^[N] binf) ξ * e ξ‖ ≤ Ct * ξ ^ d := fun ξ hξ => by
    rw [norm_mul, hen, mul_one]; exact hTib' ξ hξ
  have hIinf := (c04o_aux_powtail (hTis.continuous.mul hec) hL0 (by linarith)
    (fun ξ hξ => by simp [hTiv ξ hξ]) hTie).1
  have hθc : HasCompactSupport (fun ξ => (θ ξ : ℂ)) := hθ.2.1.comp_left Complex.ofReal_zero
  have hθa : Continuous (fun ξ => (θ ξ : ℂ) * a ξ) :=
    (Complex.continuous_ofReal.comp hθ.1.continuous).mul ha.1.continuous
  have hIθ : IntegrableOn (fun ξ => (θ ξ : ℂ) * a ξ * e ξ) (Ioi 0) :=
    c04o_aux_cpt_int p y hp hθa hθc.mul_right
  refine ⟨hIθ, hIinf, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  obtain ⟨hbMs, hbMc, hbMv, hbMd⟩ := hbM M hM1
  set bM : ℝ → ℂ := fun x => (ρ' (x / M) : ℂ) * ((1 - θ x : ℝ) : ℂ) * a x with hbMdef
  have hbMb : ∀ r ≤ N + 0, ∀ ξ, L ≤ ξ → ‖iteratedDeriv r bM ξ‖ ≤ Bf r * 1 * ξ ^ (m - r) :=
    fun r _ ξ hξ => by
      rw [mul_one]
      exact ((hBf r) a ha.1 ha.2.1 (fun l' _ ξ hξ => hCa l' ξ hξ)).1 M hM1 ξ (by linarith)
  obtain ⟨hTMs, hTMv, hTMb⟩ := hCtf L 1 1 hL1 one_pos one_pos bM hbMs hbMv q hq hbMb hqb
  have hTMb' : ∀ ξ, L ≤ ξ → ‖(T^[N] bM) ξ‖ ≤ Ct * ξ ^ d := fun ξ hξ => by
    simpa using hTMb ξ hξ
  -- the phase
  set φ : ℝ → ℝ := fun x => y * x - Phi0 p x with hφdef
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ioi 0) :=
    (contDiffOn_const.mul contDiffOn_id).sub (c04o_aux_Phi0_smooth p hp)
  have hqφ : ∀ ξ, L < ξ → q ξ * deriv φ ξ = 1 := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith
    have hder := (c04o_aux_deriv_phase p y ξ hp hξ0).deriv
    have hlow := ((hDf 0).1 Y hY y hy ξ (by linarith)).2.1
    rw [hder] at hlow ⊢
    have : y - ξ ^ p ≠ 0 := by
      intro h; rw [h, abs_zero] at hlow; linarith [rpow_pos_of_pos hξ0 p]
    exact inv_mul_cancel₀ this
  obtain ⟨hIbM, hITM, hEq⟩ := hId L hL1 bM hbMs hbMv hbMc q hq φ hφ hqφ N
  -- splitting the cutoff integral
  have hsplit : ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ =
      (∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * e ξ) +
        ∫ ξ in Ioi (0 : ℝ), bM ξ * Complex.exp (Complex.I * (φ ξ : ℂ)) := by
    rw [← integral_add hIθ hIbM]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
    have hξ0 : (0 : ℝ) < ξ := hξ
    simp only [hbMdef, hedef, hφdef, c04_eiphase]
    rcases le_or_gt ξ (2 * L) with h | h
    · have : ρ' (ξ / M) = 1 := hρ.2.2.1 _ ⟨by
          have : 0 ≤ ξ / M := div_nonneg hξ0.le hM0.le
          linarith, by rw [div_le_iff₀ hM0]; linarith⟩
      rw [this]; push_cast; ring
    · rw [hθ.2.2.2.2 ξ h.le]; push_cast; ring
  -- locality and the error
  have hloc := c04o_aux_ibpOp_local L q isOpen_Ioo (U := Ioo (-M) M) (c₁ := bM) (c₂ := binf)
    (fun x hx => by
      have := c04o_aux_trunc_one hρ hM0 hx
      simp only at this
      simp only [hbMdef, hbinf, this, one_mul]) N
  set g : ℝ → ℂ := fun ξ => (T^[N] bM) ξ - (T^[N] binf) ξ with hgdef
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := hTMs.sub hTis
  have hg0 : ∀ ξ ≤ M, g ξ = 0 := by
    have := c04o_aux_flat hgs (L := M) (fun ξ hξ => by
      rcases le_or_gt ξ L with h | h
      · show (T^[N] bM) ξ - (T^[N] binf) ξ = 0
        rw [hTMv ξ h, hTiv ξ h, sub_self]
      · simp only [hgdef]; rw [hloc ⟨by linarith, hξ⟩, sub_self]) 0
    simpa using this
  have hgb : ∀ ξ, M ≤ ξ → ‖g ξ * e ξ‖ ≤ (2 * Ct) * ξ ^ d := by
    intro ξ hξ
    rw [norm_mul, hen, mul_one]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hTMb' ξ (by linarith)
    have h2 := hTib' ξ (by linarith)
    linarith
  obtain ⟨hIg, hIgb⟩ := c04o_aux_powtail (hgs.continuous.mul hec) hM0 (by linarith)
    (fun ξ hξ => by simp [hg0 ξ hξ]) hgb
  have hdiff : (∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ) -
      ((∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * c04_eiphase p y ξ) +
        ∫ ξ in Ioi (0 : ℝ), (T^[N] binf) ξ * c04_eiphase p y ξ) =
      ∫ ξ in Ioi (0 : ℝ), g ξ * e ξ := by
    rw [hsplit, hEq]
    have : ∫ ξ in Ioi (0 : ℝ), g ξ * e ξ = (∫ ξ in Ioi (0 : ℝ), (T^[N] bM) ξ * e ξ) -
        ∫ ξ in Ioi (0 : ℝ), (T^[N] binf) ξ * e ξ := by
      have hITM' : IntegrableOn (fun ξ => (T^[N] bM) ξ * e ξ) (Ioi 0) := hITM
      have hIinf' : IntegrableOn (fun ξ => (T^[N] binf) ξ * e ξ) (Ioi 0) := hIinf
      rw [← integral_sub hITM' hIinf']
      congr 1; funext ξ; simp only [hgdef]; ring
    rw [this]
    simp only [hedef, hφdef, c04_eiphase]
    ring
  rw [hdiff]
  refine (norm_integral_le_integral_norm _).trans (hIgb.trans (le_of_eq ?_))
  rw [show d + 1 = m - N * (1 + p) + 1 by rw [hd]]
  field_simp

theorem c04o_aux_tendsto_pow (e : ℝ) (he : e < 0) : Tendsto (fun M : ℝ => M ^ e) atTop (𝓝 0) := by
  have := tendsto_rpow_neg_atTop (y := -e) (by linarith)
  simpa using this

/-- Eventual bound `C M^e` (`e < 0`) on a set gives uniform convergence there. -/
theorem c04o_aux_unif_of_bound {F : ℝ → ℝ → ℂ} {f : ℝ → ℂ} {S : Set ℝ} {C e M0 : ℝ}
    (he : e < 0) (hb : ∀ M, M0 ≤ M → ∀ y ∈ S, ‖F M y - f y‖ ≤ C * M ^ e) :
    TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun M : ℝ => C * M ^ e) atTop (𝓝 0) := by
    simpa using (c04o_aux_tendsto_pow e he).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_ge_atTop M0] with M hM hM0 y hy
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt (hb M hM0 y hy) hM

theorem c04o_aux_trunc_cpt {ρ' : ℝ → ℝ} (hρ : c04_IsTruncation ρ') {M : ℝ} (hM : 0 < M)
    (a : ℝ → ℂ) : HasCompactSupport (fun ξ => (ρ' (ξ / M) : ℂ) * a ξ) := by
  refine HasCompactSupport.intro (K := Icc (-(2 * M)) (2 * M)) isCompact_Icc fun x hx => ?_
  simp [c04o_aux_trunc_zero hρ hM x hx]

/-- Continuity in `y` of an oscillatory integral with continuous compactly supported amplitude. -/
theorem c04o_aux_param_cont (p : ℝ) (hp : 0 < p) {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    Continuous (fun y => ∫ ξ in Ioi (0 : ℝ), f ξ * c04_eiphase p y ξ) := by
  refine continuous_of_dominated (bound := fun ξ => ‖f ξ‖) (fun y => ?_) (fun y => ?_) ?_ ?_
  · exact ((hf.mul (c04o_aux_eiphase_cont p y hp)).aestronglyMeasurable)
  · exact Eventually.of_forall fun ξ => by rw [norm_mul, c04o_aux_eiphase_norm, mul_one]
  · exact (hf.norm.integrable_of_hasCompactSupport hc.norm).integrableOn
  · refine Eventually.of_forall fun ξ => continuous_const.mul ?_
    unfold c04_eiphase
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_id.mul continuous_const).sub continuous_const)))

/-- Choice of the auxiliary data for a given `Y ≥ 1`. -/
theorem c04o_aux_data (p : ℝ) (hp : 0 < p) (m : ℝ) (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ L : ℝ, (2 * Y) ^ (1 / p) + 2 ≤ L ∧ c04o_aux_IsTailCutoff L (fun x => rho (x / L)) ∧
      ∃ N : ℕ, m - N * (1 + p) < -1 := by
  have hL0 : 0 < (2 * Y) ^ (1 / p) + 2 := by
    have := rpow_nonneg (show (0 : ℝ) ≤ 2 * Y by linarith) (1 / p); linarith
  refine ⟨_, le_rfl, c04o_aux_rho_tail _ hL0, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ((m + 1) / (1 + p))
  refine ⟨N, ?_⟩
  rw [div_lt_iff₀ (by linarith)] at hN
  linarith

/-! ### The cutoff limit -/

/-- Blueprint: lem:c04_osc_cutoff_limit.  The cutoff integrals converge absolutely, converge
locally uniformly to the continuous function `Osc[a]` for every admissible truncation, and for
`|y| ≤ Y` one has the integrated-by-parts representation and the quantitative error bound. -/
theorem c04_osc_cutoff_limit (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℝ) (a : ℝ → ℂ)
    (ha : a ∈ c04_osc_symbol m) :
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ M : ℝ, 0 < M → ∀ y : ℝ,
      IntegrableOn (fun ξ => (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ) (Ioi 0)) ∧
    Continuous (c04_osc_integral p a) ∧
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' →
      TendstoLocallyUniformly
        (fun (M : ℝ) (y : ℝ) => ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
        (c04_osc_integral p a) atTop) ∧
    (∀ Y : ℝ, 1 ≤ Y → ∀ L : ℝ, (2 * Y) ^ (1 / p) + 2 ≤ L → ∀ θ : ℝ → ℝ,
      c04o_aux_IsTailCutoff L θ → ∀ N : ℕ, m - N * (1 + p) < -1 →
      (∀ y : ℝ, |y| ≤ Y →
        IntegrableOn (fun ξ => (θ ξ : ℂ) * a ξ * c04_eiphase p y ξ) (Ioi 0) ∧
        IntegrableOn (fun ξ => ((c04o_aux_ibpOp L (fun x => (y - x ^ p)⁻¹))^[N]
          (fun x => ((1 - θ x : ℝ) : ℂ) * a x)) ξ * c04_eiphase p y ξ) (Ioi 0) ∧
        c04_osc_integral p a y =
          (∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * c04_eiphase p y ξ) +
          ∫ ξ in Ioi (0 : ℝ), ((c04o_aux_ibpOp L (fun x => (y - x ^ p)⁻¹))^[N]
            (fun x => ((1 - θ x : ℝ) : ℂ) * a x)) ξ * c04_eiphase p y ξ) ∧
      ∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∃ C > (0 : ℝ), ∀ M : ℝ, 2 * L ≤ M → ∀ y : ℝ, |y| ≤ Y →
        ‖(∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ) -
          c04_osc_integral p a y‖ ≤ C * M ^ (m - N * (1 + p) + 1)) := by
  -- representation of `Osc[a]` on `|y| ≤ Y`
  have hOsc : ∀ Y : ℝ, 1 ≤ Y → ∀ L : ℝ, (2 * Y) ^ (1 / p) + 2 ≤ L → ∀ θ : ℝ → ℝ,
      c04o_aux_IsTailCutoff L θ → ∀ N : ℕ, m - N * (1 + p) < -1 → ∀ y : ℝ, |y| ≤ Y →
      c04_osc_integral p a y =
          (∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * c04_eiphase p y ξ) +
          ∫ ξ in Ioi (0 : ℝ), ((c04o_aux_ibpOp L (fun x => (y - x ^ p)⁻¹))^[N]
            (fun x => ((1 - θ x : ℝ) : ℂ) * a x)) ξ * c04_eiphase p y ξ := by
    intro Y hY L hL θ hθ N hN y hy
    obtain ⟨C, _, hC⟩ := c04o_aux_core p hp hp1 m a ha Y hY L hL θ hθ N hN rho c04o_aux_rho_trunc
    have hu := c04o_aux_unif_of_bound (S := {y}) (M0 := 2 * L) (C := C) (e := m - N * (1 + p) + 1)
      (F := fun (M : ℝ) (y : ℝ) => ∫ ξ in Ioi (0 : ℝ), (rho (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
      (f := fun y => (∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * c04_eiphase p y ξ) +
          ∫ ξ in Ioi (0 : ℝ), ((c04o_aux_ibpOp L (fun x => (y - x ^ p)⁻¹))^[N]
            (fun x => ((1 - θ x : ℝ) : ℂ) * a x)) ξ * c04_eiphase p y ξ)
      (by linarith) (fun M hM y' hy' => by
        rw [mem_singleton_iff] at hy'; subst hy'; exact (hC y' hy).2.2 M hM)
    exact (hu.tendsto_at (mem_singleton y)).limUnder_eq
  have hbd : ∀ Y : ℝ, 1 ≤ Y → ∀ L : ℝ, (2 * Y) ^ (1 / p) + 2 ≤ L → ∀ θ : ℝ → ℝ,
      c04o_aux_IsTailCutoff L θ → ∀ N : ℕ, m - N * (1 + p) < -1 →
      ∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∃ C > (0 : ℝ), ∀ M : ℝ, 2 * L ≤ M → ∀ y : ℝ, |y| ≤ Y →
        ‖(∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ) -
          c04_osc_integral p a y‖ ≤ C * M ^ (m - N * (1 + p) + 1) := by
    intro Y hY L hL θ hθ N hN ρ' hρ
    obtain ⟨C, hC0, hC⟩ := c04o_aux_core p hp hp1 m a ha Y hY L hL θ hθ N hN ρ' hρ
    refine ⟨C, hC0, fun M hM y hy => ?_⟩
    rw [hOsc Y hY L hL θ hθ N hN y hy]
    exact (hC y hy).2.2 M hM
  have hloc : ∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' →
      TendstoLocallyUniformly
        (fun (M : ℝ) (y : ℝ) => ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
        (c04_osc_integral p a) atTop := by
    intro ρ' hρ
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    set Y := |x| + 1 with hYdef
    have hY : 1 ≤ Y := by have := abs_nonneg x; linarith
    obtain ⟨L, hL, hθ, N, hN⟩ := c04o_aux_data p hp m Y hY
    obtain ⟨C, _, hC⟩ := hbd Y hY L hL _ hθ N hN ρ' hρ
    have hu := c04o_aux_unif_of_bound (S := Icc (-Y) Y) (M0 := 2 * L) (C := C) (e := m - N * (1 + p) + 1)
      (F := fun (M : ℝ) (y : ℝ) => ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
      (f := c04_osc_integral p a) (by linarith) (fun M hM y hy => hC M hM y (abs_le.2 hy))
    rw [Metric.tendstoUniformlyOn_iff] at hu
    refine ⟨Icc (-Y) Y, Icc_mem_nhds (by linarith [neg_abs_le x, hYdef]) (by linarith [le_abs_self x, hYdef]),
      hu ε hε⟩
  refine ⟨fun ρ' hρ M hM y => c04o_aux_cpt_int p y hp
      ((Complex.continuous_ofReal.comp (hρ.1.continuous.comp (continuous_id.div_const M))).mul
        ha.1.continuous) (c04o_aux_trunc_cpt hρ hM a), ?_, hloc,
    fun Y hY L hL θ hθ N hN => ⟨fun y hy => ?_, hbd Y hY L hL θ hθ N hN⟩⟩
  · refine (hloc rho c04o_aux_rho_trunc).continuous ?_
    refine (eventually_gt_atTop (0 : ℝ)).frequently.mono fun M hM => ?_
    exact c04o_aux_param_cont p hp
      ((Complex.continuous_ofReal.comp (c04o_aux_rho_trunc.1.continuous.comp
        (continuous_id.div_const M))).mul ha.1.continuous) (c04o_aux_trunc_cpt c04o_aux_rho_trunc hM a)
  · obtain ⟨C, _, hC⟩ := c04o_aux_core p hp hp1 m a ha Y hY L hL θ hθ N hN rho c04o_aux_rho_trunc
    exact ⟨(hC y hy).1, (hC y hy).2.1, hOsc Y hY L hL θ hθ N hN y hy⟩

/-! ### Ordinary integrals, parameter derivatives and the negative tail -/

/-- One integration by parts on `[L,M]` with boundary term (no compact support). -/
theorem c04o_aux_ibp_boundary (L M : ℝ) (hL : 1 ≤ L) (hLM : L < M) (c : ℝ → ℂ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcL : ∀ ξ ≤ L, c ξ = 0)
    (q : ℝ → ℝ) (hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (L / 2)))
    (φ : ℝ → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ioi 0)) (hqφ : ∀ ξ, L < ξ → q ξ * deriv φ ξ = 1) :
    ∫ ξ in L..M, (c ξ * Complex.exp (Complex.I * (φ ξ : ℂ)) -
        c04o_aux_ibpOp L q c ξ * Complex.exp (Complex.I * (φ ξ : ℂ))) =
      -Complex.I * (c M * (q M : ℂ)) * Complex.exp (Complex.I * (φ M : ℂ)) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hg, hT⟩ := c04o_aux_ibpOp_eq L hL0 q c hc hcL hq
  have hs := c04_osc_ibp_step L 0 0 1 1 hL one_pos one_pos c hc hcL q hq
  set E : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * (φ ξ : ℂ)) with hEdef
  have hsub : Icc L M ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hL0 hx.1
  have hEc : ContinuousOn E (Icc L M) :=
    (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (hφ.continuousOn.mono hsub))))
  set g := fun x => c x * (q x : ℂ) with hgdef
  set F : ℝ → ℂ := fun ξ => -Complex.I * g ξ * E ξ with hFdef
  have hFd : ∀ x ∈ Ioo L M, HasDerivAt F (c x * E x - c04o_aux_ibpOp L q c x * E x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hL0 hx.1
    have hφd : HasDerivAt φ (deriv φ x) x :=
      ((hφ.contDiffAt (Ioi_mem_nhds hx0)).differentiableAt (by simp)).hasDerivAt
    have hEd : HasDerivAt E (E x * (Complex.I * ((deriv φ x : ℝ) : ℂ))) x := by
      have := (hφd.ofReal_comp.const_mul Complex.I).cexp
      simpa [hEdef] using this
    have hgd : HasDerivAt g (deriv g x) x :=
      (hg.differentiable (by simp) x).hasDerivAt
    have := (hgd.const_mul (-Complex.I)).mul hEd
    convert this using 1
    rw [hT]
    have h1 : ((q x : ℝ) : ℂ) * ((deriv φ x : ℝ) : ℂ) = 1 := by exact_mod_cast hqφ x hx.1
    simp only [hgdef]
    linear_combination (c x * E x * ((q x : ℝ) : ℂ) * ((deriv φ x : ℝ) : ℂ)) * Complex.I_sq -
      (c x * E x) * h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hLM.le
    ((continuousOn_const.mul hg.continuous.continuousOn).mul hEc) hFd
    (((hc.continuous.continuousOn.mul hEc).sub
      (hs.1.continuous.continuousOn.mul hEc)).intervalIntegrable_of_Icc hLM.le)]
  simp [hFdef, hgdef, hcL L le_rfl]
  left; rfl

/-- Blueprint: lem:c04_osc_ordinary_integrals.  Agreement of `Osc[a]` with the Lebesgue integral
(if `a ∈ L¹(0,∞)`) and with the improper Riemann integral (if `m < p`). -/
theorem c04_osc_ordinary_integrals (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℝ) (a : ℝ → ℂ)
    (ha : a ∈ c04_osc_symbol m) :
    (IntegrableOn a (Ioi 0) → ∀ y : ℝ,
      IntegrableOn (fun ξ => a ξ * c04_eiphase p y ξ) (Ioi 0) ∧
      c04_osc_integral p a y = ∫ ξ in Ioi (0 : ℝ), a ξ * c04_eiphase p y ξ) ∧
    (m < p → ∀ y : ℝ,
      Tendsto (fun M : ℝ => ∫ ξ in (0 : ℝ)..M, a ξ * c04_eiphase p y ξ)
        atTop (𝓝 (c04_osc_integral p a y))) := by
  constructor
  · intro hint y
    have hec := c04o_aux_eiphase_cont p y hp
    have hae : IntegrableOn (fun ξ => a ξ * c04_eiphase p y ξ) (Ioi 0) :=
      Integrable.mono' hint.norm (ha.1.continuous.mul hec).aestronglyMeasurable
        (ae_of_all _ fun ξ => by rw [norm_mul, c04o_aux_eiphase_norm, mul_one])
    refine ⟨hae, ?_⟩
    have ht : Tendsto (fun M : ℝ => ∫ ξ in Ioi (0 : ℝ), (rho (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
        atTop (𝓝 (∫ ξ in Ioi (0 : ℝ), a ξ * c04_eiphase p y ξ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖a ξ‖)
        (Eventually.of_forall fun M => ?_) (Eventually.of_forall fun M => ae_of_all _ fun ξ => ?_)
        hint.norm (ae_of_all _ fun ξ => ?_)
      · exact (((Complex.continuous_ofReal.comp (c04o_aux_rho_trunc.1.continuous.comp
          (continuous_id.div_const M))).mul ha.1.continuous).mul hec).aestronglyMeasurable
      · rw [norm_mul, c04o_aux_eiphase_norm, mul_one, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
        have h := c04o_aux_rho_trunc.2.1 (ξ / M)
        rw [abs_of_nonneg h.1]
        exact mul_le_of_le_one_left (norm_nonneg _) h.2
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (|ξ| + 1)] with M hM
        have hM0 : 0 < M := by linarith [abs_nonneg ξ]
        have : rho (ξ / M) = 1 := c04o_aux_rho_trunc.2.2.1 _ (by
          rw [mem_Icc, le_div_iff₀ hM0, div_le_iff₀ hM0]
          constructor <;> linarith [neg_abs_le ξ, le_abs_self ξ])
        simp [this]
    unfold c04_osc_integral
    exact ht.limUnder_eq
  · intro hmp y
    set Y := |y| + 1 with hYdef
    have hY : 1 ≤ Y := by have := abs_nonneg y; linarith
    have hy : |y| ≤ Y := by linarith
    obtain ⟨L, hL, hθ, -⟩ := c04o_aux_data p hp m Y hY
    set θ : ℝ → ℝ := fun x => rho (x / L) with hθdef
    have hx0 : 0 ≤ (2 * Y) ^ (1 / p) := rpow_nonneg (by linarith) _
    have hL1 : 1 ≤ L := by linarith
    have hL0 : 0 < L := by linarith
    have hN1 : m - ((1 : ℕ) : ℝ) * (1 + p) < -1 := by push_cast; linarith
    obtain ⟨hIθ, hIT, hrep⟩ := ((c04_osc_cutoff_limit p hp hp1 m a ha).2.2.2 Y hY L hL θ hθ 1 hN1).1 y hy
    rw [Function.iterate_one] at hIT hrep
    set q : ℝ → ℝ := fun x => (y - x ^ p)⁻¹ with hqdef
    set binf : ℝ → ℂ := fun x => ((1 - θ x : ℝ) : ℂ) * a x with hbinf
    set e : ℝ → ℂ := fun ξ => c04_eiphase p y ξ with hedef
    have hec : Continuous e := c04o_aux_eiphase_cont p y hp
    choose Ca hCa using ha.2.2
    have hsym := c04_osc_cutoff_symbols m Ca
    obtain ⟨hbs, hbv, -⟩ := hsym.2.2.2.2.2 rho c04o_aux_rho_trunc L hL1 θ hθ a ha.1 ha.2.1
    obtain ⟨B, -, hB⟩ := hsym.2.2.2.2.1 rho c04o_aux_rho_trunc L hL1 θ hθ 0
    have hB0 := (hB a ha.1 ha.2.1 (fun l' _ ξ hξ => hCa l' ξ hξ)).2
    obtain ⟨D, -, hD, -⟩ := c04_osc_phase_reciprocal p hp hp1 0
    have hq := c04o_aux_q_smooth p hp hp1 Y hY y hy L hL
    have hTs := (c04_osc_ibp_step L 0 0 1 1 hL1 one_pos one_pos binf hbs hbv q hq).1
    have hTv : ∀ ξ ≤ L, c04o_aux_ibpOp L q binf ξ = 0 := fun ξ hξ => by
      simpa using (c04_osc_ibp_step L 0 0 1 1 hL1 one_pos one_pos binf hbs hbv q hq).2.1 0 ξ hξ
    set φ : ℝ → ℝ := fun x => y * x - Phi0 p x with hφdef
    have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ioi 0) :=
      (contDiffOn_const.mul contDiffOn_id).sub (c04o_aux_Phi0_smooth p hp)
    have hqφ : ∀ ξ, L < ξ → q ξ * deriv φ ξ = 1 := by
      intro ξ hξ
      have hξ0 : 0 < ξ := by linarith
      have hder := (c04o_aux_deriv_phase p y ξ hp hξ0).deriv
      have hlow := (hD Y hY y hy ξ (by linarith)).2.1
      rw [hder] at hlow ⊢
      have : y - ξ ^ p ≠ 0 := by
        intro h; rw [h, abs_zero] at hlow; linarith [rpow_pos_of_pos hξ0 p]
      exact inv_mul_cancel₀ this
    -- the eventual identity
    have hθa : Continuous (fun ξ => (θ ξ : ℂ) * a ξ * e ξ) :=
      ((Complex.continuous_ofReal.comp hθ.1.continuous).mul ha.1.continuous).mul hec
    have hbe : Continuous (fun ξ => binf ξ * e ξ) := hbs.continuous.mul hec
    have hTe : Continuous (fun ξ => c04o_aux_ibpOp L q binf ξ * e ξ) := hTs.continuous.mul hec
    have hzero : ∀ (u : ℝ → ℂ), Continuous u → (∀ ξ ≤ L, u ξ = 0) → ∀ M, L ≤ M →
        ∫ ξ in (0 : ℝ)..M, u ξ * e ξ = ∫ ξ in L..M, u ξ * e ξ := by
      intro u hu hu0 M hM
      have hii : ∀ a b : ℝ, IntervalIntegrable (fun ξ => u ξ * e ξ) volume a b :=
        fun _ _ => (hu.mul hec).intervalIntegrable _ _
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := L) (hii 0 L) (hii L M)]
      have : ∫ ξ in (0 : ℝ)..L, u ξ * e ξ = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun ξ hξ => by
          rw [uIcc_of_le hL0.le] at hξ; simp [hu0 ξ hξ.2])]
        simp
      rw [this, zero_add]
    have heq : ∀ᶠ M in atTop, (∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * e ξ) +
        (∫ ξ in (0 : ℝ)..M, c04o_aux_ibpOp L q binf ξ * e ξ) +
        -Complex.I * (binf M * (q M : ℂ)) * e M = ∫ ξ in (0 : ℝ)..M, a ξ * c04_eiphase p y ξ := by
      filter_upwards [eventually_ge_atTop (2 * L)] with M hM
      have hM0 : 0 < M := by linarith
      have h1 : ∫ ξ in (0 : ℝ)..M, a ξ * c04_eiphase p y ξ =
          (∫ ξ in (0 : ℝ)..M, (θ ξ : ℂ) * a ξ * e ξ) + ∫ ξ in (0 : ℝ)..M, binf ξ * e ξ := by
        rw [← intervalIntegral.integral_add (hθa.intervalIntegrable _ _) (hbe.intervalIntegrable _ _)]
        refine intervalIntegral.integral_congr fun ξ _ => ?_
        simp only [hbinf, hedef]; push_cast; ring
      have h2 : ∫ ξ in (0 : ℝ)..M, (θ ξ : ℂ) * a ξ * e ξ =
          ∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * e ξ := by
        rw [intervalIntegral.integral_of_le hM0.le,
          setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
            (fun x hx => ?_)]
        simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hx
        have : θ x = 0 := hθ.2.2.2.2 x (by linarith [hx.2 hx.1])
        simp [this]
      have hbd0 := c04o_aux_ibp_boundary L M hL1 (by linarith) binf hbs hbv q hq φ hφ hqφ
      have hbd : ∫ ξ in L..M, (binf ξ * e ξ - c04o_aux_ibpOp L q binf ξ * e ξ) =
          -Complex.I * (binf M * (q M : ℂ)) * e M := hbd0
      have hi1 : IntervalIntegrable (fun ξ => binf ξ * e ξ) volume L M := hbe.intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun ξ => c04o_aux_ibpOp L q binf ξ * e ξ) volume L M :=
        hTe.intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hi1 hi2] at hbd
      rw [h1, h2, hzero binf hbs.continuous (fun ξ hξ => hbv ξ hξ) M (by linarith),
        hzero _ hTs.continuous hTv M (by linarith)]
      rw [← hbd]; ring
    have hlim1 : Tendsto (fun M : ℝ => ∫ ξ in (0 : ℝ)..M, c04o_aux_ibpOp L q binf ξ * e ξ) atTop
        (𝓝 (∫ ξ in Ioi (0 : ℝ), c04o_aux_ibpOp L q binf ξ * e ξ)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hIT tendsto_id
    have hlim2 : Tendsto (fun M : ℝ => -Complex.I * (binf M * (q M : ℂ)) * e M) atTop (𝓝 0) := by
      have hpow : Tendsto (fun M : ℝ => B * D * M ^ (m - p)) atTop (𝓝 0) := by
        simpa using (c04o_aux_tendsto_pow (m - p) (by linarith)).const_mul (B * D)
      refine squeeze_zero_norm' ?_ hpow
      filter_upwards [eventually_ge_atTop L] with M hM
      have hM0 : 0 < M := by linarith
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, hedef,
        c04o_aux_eiphase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hB0 M (by linarith)
      have h2 := (hD Y hY y hy M (by linarith)).2.2
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1 h2
      rw [sub_eq_add_neg, rpow_add hM0]
      calc ‖binf M‖ * |q M| ≤ (B * M ^ m) * (D * M ^ (-p)) :=
            mul_le_mul h1 h2 (abs_nonneg _) ((norm_nonneg _).trans h1)
        _ = B * D * (M ^ m * M ^ (-p)) := by ring
    have hlim := (tendsto_const_nhds (x := ∫ ξ in Ioi (0 : ℝ), (θ ξ : ℂ) * a ξ * e ξ)).add
      hlim1 |>.add hlim2
    rw [add_zero] at hlim
    rw [hrep]
    exact hlim.congr' heq

/-- Differentiation under the integral for a continuous compactly supported amplitude. -/
theorem c04o_aux_param_hasDeriv (p : ℝ) (hp : 0 < p) {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (y : ℝ) :
    HasDerivAt (fun y => ∫ ξ in Ioi (0 : ℝ), f ξ * c04_eiphase p y ξ)
      (∫ ξ in Ioi (0 : ℝ), (Complex.I * (ξ : ℂ) * f ξ) * c04_eiphase p y ξ) y := by
  have hg : Continuous (fun ξ : ℝ => Complex.I * (ξ : ℂ) * f ξ) :=
    (continuous_const.mul Complex.continuous_ofReal).mul hf
  have hgc : HasCompactSupport (fun ξ : ℝ => Complex.I * (ξ : ℂ) * f ξ) := hc.mul_left
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (s := univ) (bound := fun ξ : ℝ => ‖Complex.I * (ξ : ℂ) * f ξ‖)
    (F := fun (y : ℝ) (ξ : ℝ) => f ξ * c04_eiphase p y ξ)
    (F' := fun (y : ℝ) (ξ : ℝ) => (Complex.I * (ξ : ℂ) * f ξ) * c04_eiphase p y ξ) univ_mem
    (Eventually.of_forall fun y' => (hf.mul (c04o_aux_eiphase_cont p y' hp)).aestronglyMeasurable)
    (c04o_aux_cpt_int p y hp hf hc)
    ((hg.mul (c04o_aux_eiphase_cont p y hp)).aestronglyMeasurable)
    (Eventually.of_forall fun ξ y' _ => by rw [norm_mul, c04o_aux_eiphase_norm, mul_one])
    ((hg.norm.integrable_of_hasCompactSupport hgc.norm).integrableOn)
    (Eventually.of_forall fun ξ y' _ => ?_)).2
  have h1 : HasDerivAt (fun y : ℝ => ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) (ξ : ℂ) y' := by
    have := (((hasDerivAt_id y').mul_const ξ).sub_const (Phi0 p ξ)).ofReal_comp
    simpa using this
  have h2 := ((h1.const_mul Complex.I).cexp).const_mul (f ξ)
  unfold c04_eiphase
  convert h2 using 1
  ring

/-- Iterated parameter derivatives of a compactly supported oscillatory integral. -/
theorem c04o_aux_param_iter (p : ℝ) (hp : 0 < p) (j : ℕ) :
    ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
      iteratedDeriv j (fun y => ∫ ξ in Ioi (0 : ℝ), f ξ * c04_eiphase p y ξ) =
        fun y => ∫ ξ in Ioi (0 : ℝ), ((Complex.I * (ξ : ℂ)) ^ j * f ξ) * c04_eiphase p y ξ := by
  induction j with
  | zero => intro f _ _; simp
  | succ n ih =>
    intro f hf hc
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y => ∫ ξ in Ioi (0 : ℝ), f ξ * c04_eiphase p y ξ) =
        fun y => ∫ ξ in Ioi (0 : ℝ), (Complex.I * (ξ : ℂ) * f ξ) * c04_eiphase p y ξ :=
      funext fun y => (c04o_aux_param_hasDeriv p hp hf hc y).deriv
    rw [hd, ih (fun ξ : ℝ => Complex.I * (ξ : ℂ) * f ξ)
      ((continuous_const.mul Complex.continuous_ofReal).mul hf) hc.mul_left]
    funext y
    congr 1; funext ξ; ring

theorem c04o_aux_param_smooth (p : ℝ) (hp : 0 < p) {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ∫ ξ in Ioi (0 : ℝ), f ξ * c04_eiphase p y ξ) := by
  refine contDiff_of_differentiable_iteratedDeriv fun j _ => ?_
  rw [c04o_aux_param_iter p hp j f hf hc]
  have hg : Continuous (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j * f ξ) :=
    ((continuous_const.mul Complex.continuous_ofReal).pow j).mul hf
  exact fun y => (c04o_aux_param_hasDeriv p hp hg hc.mul_left y).differentiableAt

theorem c04o_aux_symb_I (m : ℝ) (a : ℝ → ℂ) (ha : a ∈ c04_osc_symbol m) :
    (fun ξ : ℝ => Complex.I * (ξ : ℂ) * a ξ) ∈ c04_osc_symbol (m + 1) := by
  have := (c04_osc_cutoff_symbols m (fun _ => 0)).2.1 a ha 1
  simp only [pow_one, Nat.cast_one] at this
  exact this

/-- `∂_y Osc[a] = Osc[iξa]`. -/
theorem c04o_aux_osc_hasDeriv (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℝ) (a : ℝ → ℂ)
    (ha : a ∈ c04_osc_symbol m) (y : ℝ) :
    HasDerivAt (c04_osc_integral p a)
      (c04_osc_integral p (fun ξ : ℝ => Complex.I * (ξ : ℂ) * a ξ) y) y := by
  have ha1 := c04o_aux_symb_I m a ha
  have hCL := c04_osc_cutoff_limit p hp hp1 m a ha
  have hCL1 := c04_osc_cutoff_limit p hp hp1 (m + 1) _ ha1
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (s := univ) isOpen_univ
    ((hCL1.2.2.1 rho c04o_aux_rho_trunc).tendstoLocallyUniformlyOn) ?_ ?_ (mem_univ y)
    (f := fun (M : ℝ) (y : ℝ) => ∫ ξ in Ioi (0 : ℝ), (rho (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM x _
    have hfc : Continuous (fun ξ => (rho (ξ / M) : ℂ) * a ξ) :=
      (Complex.continuous_ofReal.comp (c04o_aux_rho_trunc.1.continuous.comp
        (continuous_id.div_const M))).mul ha.1.continuous
    have := c04o_aux_param_hasDeriv p hp hfc (c04o_aux_trunc_cpt c04o_aux_rho_trunc hM a) x
    convert this using 1
    congr 1; funext ξ; ring
  · intro x _
    exact ((hCL.2.2.1 rho c04o_aux_rho_trunc).tendstoLocallyUniformlyOn (s := univ)).tendsto_at
      (mem_univ x)

theorem c04o_aux_osc_iter (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j : ℕ) :
    ∀ (m : ℝ) (a : ℝ → ℂ), a ∈ c04_osc_symbol m →
      iteratedDeriv j (c04_osc_integral p a) =
        c04_osc_integral p (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j * a ξ) := by
  induction j with
  | zero => intro m a _; simp
  | succ n ih =>
    intro m a ha
    rw [iteratedDeriv_succ']
    have hd : deriv (c04_osc_integral p a) =
        c04_osc_integral p (fun ξ : ℝ => Complex.I * (ξ : ℂ) * a ξ) :=
      funext fun y => (c04o_aux_osc_hasDeriv p hp hp1 m a ha y).deriv
    rw [hd, ih (m + 1) _ (c04o_aux_symb_I m a ha)]
    congr 1; funext ξ; ring

/-- Blueprint: lem:c04_osc_parameter_derivatives.  The cutoff integrals are smooth in `y` with
`∂_y^j F_M^ρ(a) = F_M^ρ((iξ)^j a)`; `Osc[a]` is smooth with `∂_y^j Osc[a] = Osc[(iξ)^j a]`;
in particular `iξa ∈ S^{m+1}_+` and `∂_y Osc[a] = Osc[iξa]`. -/
theorem c04_osc_parameter_derivatives (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℝ) (a : ℝ → ℂ)
    (ha : a ∈ c04_osc_symbol m) :
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ M : ℝ, 0 < M → ∀ j : ℕ, ∀ y : ℝ,
      IntegrableOn (fun ξ => (ρ' (ξ / M) : ℂ) * ((Complex.I * (ξ : ℂ)) ^ j * a ξ) *
        c04_eiphase p y ξ) (Ioi 0)) ∧
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ M : ℝ, 0 < M →
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y => ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ) ∧
      ∀ j : ℕ, ∀ y : ℝ,
        iteratedDeriv j
          (fun y => ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ) y =
        ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * ((Complex.I * (ξ : ℂ)) ^ j * a ξ) *
          c04_eiphase p y ξ) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c04_osc_integral p a) ∧
    (∀ j : ℕ, ∀ y : ℝ, iteratedDeriv j (c04_osc_integral p a) y =
      c04_osc_integral p (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j * a ξ) y) ∧
    (fun ξ : ℝ => Complex.I * (ξ : ℂ) * a ξ) ∈ c04_osc_symbol (m + 1) ∧
    (∀ y : ℝ, deriv (c04_osc_integral p a) y =
      c04_osc_integral p (fun ξ : ℝ => Complex.I * (ξ : ℂ) * a ξ) y) := by
  have hfc : ∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ M : ℝ, ∀ b : ℝ → ℂ, Continuous b →
      Continuous (fun ξ => (ρ' (ξ / M) : ℂ) * b ξ) := fun ρ' hρ M b hb =>
    (Complex.continuous_ofReal.comp (hρ.1.continuous.comp (continuous_id.div_const M))).mul hb
  have hIj : ∀ j : ℕ, Continuous (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j * a ξ) := fun j =>
    ((continuous_const.mul Complex.continuous_ofReal).pow j).mul ha.1.continuous
  refine ⟨fun ρ' hρ M hM j y => c04o_aux_cpt_int p y hp (hfc ρ' hρ M _ (hIj j))
      (c04o_aux_trunc_cpt hρ hM _), fun ρ' hρ M hM => ⟨c04o_aux_param_smooth p hp
      (hfc ρ' hρ M a ha.1.continuous) (c04o_aux_trunc_cpt hρ hM a), fun j y => ?_⟩, ?_,
    fun j y => by rw [c04o_aux_osc_iter p hp hp1 j m a ha], c04o_aux_symb_I m a ha,
    fun y => (c04o_aux_osc_hasDeriv p hp hp1 m a ha y).deriv⟩
  · have h := congrFun (c04o_aux_param_iter p hp j (fun ξ => (ρ' (ξ / M) : ℂ) * a ξ)
      (hfc ρ' hρ M a ha.1.continuous) (c04o_aux_trunc_cpt hρ hM a)) y
    refine h.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    ring
  · refine contDiff_of_differentiable_iteratedDeriv fun j _ => ?_
    rw [c04o_aux_osc_iter p hp hp1 j m a ha]
    have hmem := (c04_osc_cutoff_symbols m (fun _ => 0)).2.1 a ha j
    exact fun y => (c04o_aux_osc_hasDeriv p hp hp1 _ _ hmem y).differentiableAt

/-- Blueprint: lem:c04_osc_negative_tail.  Rapid decay on `y ≤ -1`, uniformly in the cutoff
parameter `M ≥ 1`, for any integer `K ≥ N` with `K > m + 1`; the constant depends only on
`p, m, N, ρ, K` and the symbol constants `C_0, …, C_K` of `a`. -/
theorem c04_osc_negative_tail (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℝ) (N : ℝ) (hN : 0 ≤ N)
    (Cs : ℕ → ℝ) (K : ℕ) (hKN : N ≤ K) (hKm : m + 1 < K) :
    ∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∃ C > (0 : ℝ), ∀ a ∈ c04_osc_symbol m,
      (∀ l ≤ K, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv l a ξ‖ ≤ Cs l * ξ ^ (m - l)) →
      (∀ M : ℝ, 1 ≤ M → ∀ y : ℝ, y ≤ -1 →
        ‖∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ‖ ≤ C * |y| ^ (-N)) ∧
      ∀ y : ℝ, y ≤ -1 → ‖c04_osc_integral p a y‖ ≤ C * |y| ^ (-N) := by
  intro ρ' hρ
  have hsym := c04_osc_cutoff_symbols m Cs
  choose Bf hBpos hBf using hsym.2.2.1 ρ' hρ
  choose Df hDpos hDf using c04_osc_phase_reciprocal p hp hp1
  have htr := c04_osc_ibp_transfer m 0 Bf Df (fun r => (hBpos r).le) (fun r => (hDpos r).le)
  obtain ⟨Ct, hCt, hCtf⟩ := htr.1 K 0
  set d := m - K * (1 + 0) with hd
  have hd1 : 0 < -d - 1 := by rw [hd]; linarith
  refine ⟨Ct / (-d - 1), by positivity, fun a ha haK => ?_⟩
  have hF : ∀ M : ℝ, 1 ≤ M → ∀ y : ℝ, y ≤ -1 →
      ‖∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ‖ ≤ Ct / (-d - 1) * |y| ^ (-N) := by
    intro M hM y hy
    have hM0 : 0 < M := by linarith
    have hya : |y| = -y := abs_of_neg (by linarith)
    have hy1 : 1 ≤ |y| := by rw [hya]; linarith
    have hH : 0 < |y|⁻¹ := by positivity
    obtain ⟨hbs, hbc, hbv, _⟩ := hsym.2.2.2.1 ρ' hρ a ha.1 ha.2.1 M hM
    set b : ℝ → ℂ := fun x => (ρ' (x / M) : ℂ) * a x with hbdef
    set q : ℝ → ℝ := fun x => (y - x ^ p)⁻¹ with hqdef
    have hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi (1 / 2)) := by
      intro ξ hξ
      have hξ0 : (0 : ℝ) < ξ := by have : (1 : ℝ) / 2 < ξ := hξ; linarith
      have hne : y - ξ ^ p ≠ 0 := by have := rpow_pos_of_pos hξ0 p; intro h; linarith
      exact ((contDiffAt_const.sub (Real.contDiffAt_rpow_const_of_ne hξ0.ne')).inv hne).contDiffWithinAt
    have hbb : ∀ r ≤ K + 0, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv r b ξ‖ ≤ Bf r * 1 * ξ ^ (m - r) :=
      fun r hr ξ hξ => by
        rw [mul_one]
        exact hBf r a ha.1 ha.2.1 (fun l' hl' ξ hξ => haK l' (by omega) ξ hξ) M hM ξ hξ
    have hqb : ∀ r ≤ K + 0, ∀ ξ, 1 ≤ ξ → |iteratedDeriv r q ξ| ≤ Df r * |y|⁻¹ * ξ ^ (-(0 : ℝ) - (r : ℝ)) :=
      fun r _ ξ hξ => by
        have h := (hDf r).2 y hy ξ hξ
        rw [neg_zero, zero_sub]
        exact h.2.2.1.trans h.2.2.2
    obtain ⟨hTs, hTv, hTb⟩ := hCtf 1 1 |y|⁻¹ le_rfl one_pos hH b hbs (fun ξ hξ => hbv ξ hξ) q
      (by simpa using hq) hbb hqb
    set φ : ℝ → ℝ := fun x => y * x - Phi0 p x with hφdef
    have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ioi 0) :=
      (contDiffOn_const.mul contDiffOn_id).sub (c04o_aux_Phi0_smooth p hp)
    have hqφ : ∀ ξ, 1 < ξ → q ξ * deriv φ ξ = 1 := by
      intro ξ hξ
      have hξ0 : 0 < ξ := by linarith
      rw [(c04o_aux_deriv_phase p y ξ hp hξ0).deriv]
      have : y - ξ ^ p ≠ 0 := by have := rpow_pos_of_pos hξ0 p; intro h; linarith
      exact inv_mul_cancel₀ this
    obtain ⟨_, _, hEq⟩ := htr.2.2 1 le_rfl b hbs (fun ξ hξ => hbv ξ hξ) hbc q
      (by simpa using hq) φ hφ hqφ K
    have hEq' : ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ =
        ∫ ξ in Ioi (0 : ℝ), ((c04o_aux_ibpOp 1 q)^[K] b) ξ * c04_eiphase p y ξ := hEq
    rw [hEq']
    have hbound : ∀ ξ, 1 ≤ ξ → ‖((c04o_aux_ibpOp 1 q)^[K] b) ξ * c04_eiphase p y ξ‖ ≤
        (Ct * |y|⁻¹ ^ K) * ξ ^ d := by
      intro ξ hξ
      rw [norm_mul, c04o_aux_eiphase_norm, mul_one]
      have := hTb ξ hξ
      have h2 : ξ ^ (m - (K : ℝ) * (1 + 0) - ((0 : ℕ) : ℝ)) = ξ ^ d := by
        rw [hd, Nat.cast_zero, sub_zero]
      rw [iteratedDeriv_zero, h2, mul_one] at this
      exact this
    obtain ⟨_, hI⟩ := c04o_aux_powtail ((hTs.continuous).mul (c04o_aux_eiphase_cont p y hp))
      one_pos (by linarith) (fun ξ hξ => by simp [hTv ξ hξ]) hbound
    refine (norm_integral_le_integral_norm _).trans (hI.trans ?_)
    rw [one_rpow, inv_pow, ← rpow_natCast, ← rpow_neg (by linarith)]
    have hpow : |y| ^ (-(K : ℝ)) ≤ |y| ^ (-N) :=
      rpow_le_rpow_of_exponent_le hy1 (by linarith)
    calc Ct * |y| ^ (-(K : ℝ)) * (1 / (-d - 1)) = Ct / (-d - 1) * |y| ^ (-(K : ℝ)) := by ring
      _ ≤ Ct / (-d - 1) * |y| ^ (-N) := by gcongr
  refine ⟨hF, fun y hy => ?_⟩
  have ht := ((c04_osc_cutoff_limit p hp hp1 m a ha).2.2.1 ρ' hρ).tendstoLocallyUniformlyOn
    (s := univ) |>.tendsto_at (mem_univ y)
  refine le_of_tendsto ht.norm ?_
  filter_upwards [eventually_ge_atTop 1] with M hM using hF M hM y hy

/-! ### The assembly -/

/-- Blueprint: lem:c04_osc_integral.  Properties of `Osc[a]` for `a ∈ S^m_+`: (1) the limit exists
locally uniformly, is independent of `ρ`, equals the Lebesgue integral if `a ∈ L¹` and the
improper Riemann integral if `m < p`; (2) `Osc[a] ∈ C^∞`, `∂_y Osc[a] = Osc[iξa]`; (3) rapid decay
on `y ≤ -1`.  (Lean name differs from the definition `c04_osc_integral`.) -/
theorem c04_osc_integral_properties (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (m : ℝ) (a : ℝ → ℂ)
    (ha : a ∈ c04_osc_symbol m) :
    -- (1)
    TendstoLocallyUniformly
      (fun (M : ℝ) (y : ℝ) => ∫ ξ in Ioi (0 : ℝ), (rho (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
      (c04_osc_integral p a) atTop ∧
    (∀ ρ' : ℝ → ℝ, c04_IsTruncation ρ' → ∀ y,
      Tendsto (fun M : ℝ => ∫ ξ in Ioi (0 : ℝ), (ρ' (ξ / M) : ℂ) * a ξ * c04_eiphase p y ξ)
        atTop (𝓝 (c04_osc_integral p a y))) ∧
    (IntegrableOn a (Ioi 0) → ∀ y,
      c04_osc_integral p a y = ∫ ξ in Ioi (0 : ℝ), a ξ * c04_eiphase p y ξ) ∧
    (m < p → ∀ y,
      Tendsto (fun M : ℝ => ∫ ξ in (0 : ℝ)..M, a ξ * c04_eiphase p y ξ)
        atTop (𝓝 (c04_osc_integral p a y))) ∧
    -- (2)
    (fun ξ : ℝ => Complex.I * (ξ : ℂ) * a ξ) ∈ c04_osc_symbol (m + 1) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c04_osc_integral p a) ∧
    (∀ y, deriv (c04_osc_integral p a) y =
      c04_osc_integral p (fun ξ : ℝ => Complex.I * (ξ : ℂ) * a ξ) y) ∧
    -- (3)
    (∀ N : ℝ, 0 ≤ N → ∃ C > (0 : ℝ), ∀ y ≤ (-1 : ℝ), ‖c04_osc_integral p a y‖ ≤ C * |y| ^ (-N)) := by
  have hp0 : 0 < p := by linarith
  have hCL := c04_osc_cutoff_limit p hp0 hp1 m a ha
  have hOI := c04_osc_ordinary_integrals p hp0 hp1 m a ha
  have hPD := c04_osc_parameter_derivatives p hp0 hp1 m a ha
  refine ⟨hCL.2.2.1 rho c04o_aux_rho_trunc, fun ρ' hρ' y => ((hCL.2.2.1 ρ' hρ').tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ y),
    fun hint y => (hOI.1 hint y).2, hOI.2, hPD.2.2.2.2.1, hPD.2.2.1, hPD.2.2.2.2.2, ?_⟩
  intro N hN
  choose Cs hCs using ha.2.2
  obtain ⟨K, hK⟩ := exists_nat_gt (max N (m + 1))
  obtain ⟨C, hC, hCa⟩ := c04_osc_negative_tail p hp0 hp1 m N hN Cs K
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hK))
    (lt_of_le_of_lt (le_max_right _ _) hK) rho c04o_aux_rho_trunc
  exact ⟨C, hC, (hCa a ha (fun l _ ξ hξ => hCs l ξ hξ)).2⟩

end GSQG
