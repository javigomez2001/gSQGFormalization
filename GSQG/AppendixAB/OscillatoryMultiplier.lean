import GSQG.AppendixAB.StationaryPhaseHomogeneous
import GSQG.Auxiliary.SpecialIntegrals

/-!
# Appendix B: oscillatory multiplier expansion (toolbox for Lemma B.5; blueprint ch. 03)

Blueprint sublemmas (with their blueprint Lean names) and proofs of the nodes
`c03_frac_moments`, `c03_mult_expansion`, `c03_mult_summand`, `c03_mult_difference`,
`appendix_oscillatory_multiplier` under the prefix `c03m_` (same statements as the public ones in `AppendixAB/Statements.lean`).
Helpers: `c03m_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ## Pure helpers -/

lemma c03m_aux_Icc_sub_Ioo {Y y : ℝ} (hY : 1 ≤ Y) (hy : y ∈ Icc Y (2 * Y)) :
    y ∈ Ioo (Y / 2) (3 * Y) :=
  ⟨by linarith [hy.1], by linarith [hy.2]⟩

lemma c03m_aux_hyp_mono {Y Λ A c₀ : ℝ} {Ck : ℕ → ℝ} {k₁ k₂ : ℕ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ}
    (hk : k₁ ≤ k₂) (h : c03_mult_hyp Y Λ A c₀ Ck k₂ a Ψ) : c03_mult_hyp Y Λ A c₀ Ck k₁ a Ψ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, fun y hy => ⟨(h4 y hy).1, (h4 y hy).2.1,
    fun k hk' => (h4 y hy).2.2 k (hk'.trans hk)⟩⟩

lemma c03m_aux_ell_le (N r : ℕ) (hN : 1 ≤ N) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) : c03_mult_ell q + 1 ≤ N := by
  unfold c03_mult_ell
  have h2 : 2 * (∑ i : Fin (2 * N - 1), if 1 ≤ i.val then q i else 0) ≤
      ∑ i : Fin (2 * N - 1), (i.val + 1) * q i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · exact Nat.mul_le_mul_right _ (by omega)
    · simp
  omega

lemma c03m_aux_size_bound (N r : ℕ) (hN : 1 ≤ N) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) {p Y Λ A t : ℝ} (j : ℝ) (hY : 1 ≤ Y)
    (hΛ : 1 ≤ Λ) (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    c03_mult_size N q Y Λ A t * Y ^ (-j) * Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) ≤
      A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
  have hell := c03m_aux_ell_le N r hN q hrq
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  unfold c03_mult_size
  set q1 := c03_mult_q1 q
  set ℓ := c03_mult_ell q
  have ht : t ^ q1 ≤ 1 := pow_le_one₀ ht0 ht1
  have hcast : ((2 * N - 1 + q1 : ℕ) : ℝ) = 2 * (N : ℝ) - 1 + q1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast]
  have hΛe : Λ ^ (q1 + ℓ) * Λ ^ (p - (2 * (N : ℝ) - 1 + q1)) = Λ ^ (p + ℓ + 1 - 2 * N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hΛ0]; push_cast; ring_nf
  have hYe : Y ^ (-(2 * N : ℝ) + 1 + ℓ) * Y ^ (-j) = Y ^ (ℓ + 1 - 2 * N - j) := by
    rw [← Real.rpow_add hY0]; ring_nf
  have hℓ : (ℓ : ℝ) + 1 ≤ N := by exact_mod_cast hell
  have h1 : Λ ^ (p + ℓ + 1 - 2 * N) ≤ Λ ^ (p - N) :=
    Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
  have h2 : Y ^ ((ℓ : ℝ) + 1 - 2 * N - j) ≤ Y ^ (-((N : ℝ) + j)) :=
    Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  calc A * Λ ^ (q1 + ℓ) * Y ^ (-(2 * N : ℝ) + 1 + ℓ) * t ^ q1 * Y ^ (-j) *
        Λ ^ (p - (2 * (N : ℝ) - 1 + q1))
      = A * t ^ q1 * (Λ ^ (q1 + ℓ) * Λ ^ (p - (2 * (N : ℝ) - 1 + q1))) *
          (Y ^ (-(2 * N : ℝ) + 1 + ℓ) * Y ^ (-j)) := by ring
    _ = A * t ^ q1 * Λ ^ (p + ℓ + 1 - 2 * N) * Y ^ ((ℓ : ℝ) + 1 - 2 * N - j) := by
          rw [hΛe, hYe]
    _ ≤ A * 1 * Λ ^ (p - N) * Y ^ (-((N : ℝ) + j)) := by
          gcongr
    _ = A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by ring


lemma c03m_aux_size_nonneg (N : ℕ) {n : ℕ} (q : Fin n → ℕ) {Y Λ A t : ℝ} (hY : 0 < Y)
    (hΛ : 0 ≤ Λ) (hA : 0 ≤ A) (ht0 : 0 ≤ t) : 0 ≤ c03_mult_size N q Y Λ A t := by
  unfold c03_mult_size
  have := Real.rpow_nonneg hY.le (-(2 * N : ℝ) + 1 + c03_mult_ell q)
  positivity

lemma c03m_aux_size_bound2 (N r : ℕ) (hN : 1 ≤ N) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) {p Y Λ A t : ℝ} (j : ℝ) (hY : 1 ≤ Y)
    (hΛ : 1 ≤ Λ) (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    c03_mult_size N q Y Λ A t * Y ^ (-j - 1) *
        Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) ≤
      A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have h := c03m_aux_size_bound N r hN q hrq (p := p) (Λ := Λ) (A := A) (t := t) (j + 1) hY hΛ hA
    ht0 ht1
  have hS := c03m_aux_size_nonneg N q (Λ := Λ) (A := A) (t := t) hY0 hΛ0.le hA ht0
  have e1 : Y ^ (-j - 1) = Y ^ (-(j + 1)) := by ring_nf
  have e2 : Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) =
      Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) * Λ ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hΛ0]; ring_nf
  have hΛ1 : Λ ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΛ (by norm_num)
  have hΛ1' : 0 ≤ Λ ^ (-1 : ℝ) := Real.rpow_nonneg hΛ0.le _
  have hY1 : Y ^ (-((N : ℝ) + (j + 1))) ≤ Y ^ (-((N : ℝ) + j)) :=
    Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  rw [e1, e2]
  have hP : 0 ≤ c03_mult_size N q Y Λ A t * Y ^ (-(j + 1)) *
      Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) := by
    have := Real.rpow_nonneg hY0.le (-(j + 1))
    have := Real.rpow_nonneg hΛ0.le (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ))
    positivity
  calc c03_mult_size N q Y Λ A t * Y ^ (-(j + 1)) *
        (Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) * Λ ^ (-1 : ℝ))
      = (c03_mult_size N q Y Λ A t * Y ^ (-(j + 1)) *
        Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ))) * Λ ^ (-1 : ℝ) := by ring
    _ ≤ (c03_mult_size N q Y Λ A t * Y ^ (-(j + 1)) *
        Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hΛ1 hP
    _ ≤ A * Y ^ (-((N : ℝ) + (j + 1))) * Λ ^ (p - N) := by rw [mul_one]; exact h
    _ ≤ A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
          have := Real.rpow_nonneg hΛ0.le (p - N)
          gcongr


lemma c03m_aux_R_identity (p Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (N : ℕ) (y : ℝ) :
    fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y =
      Complex.exp (Complex.I * (Ψ y : ℂ)) *
        ((∑ k ∈ Finset.range (2 * N - 1), c03_mult_B p Y a Ψ k y) + c03_mult_R p Y a Ψ N y) := by
  unfold c03_mult_R
  rw [add_sub_cancel, ← mul_assoc, ← Complex.exp_add]
  simp

lemma c03m_aux_norm_deriv_sub {f g : ℝ → ℂ} {y : ℝ} (hg : DifferentiableAt ℝ g y) :
    ‖deriv (fun x => f x - g x) y‖ ≤ ‖deriv f y‖ + ‖deriv g y‖ := by
  by_cases hf : DifferentiableAt ℝ f y
  · rw [show (fun x => f x - g x) = f - g from rfl, deriv_sub hf hg]; exact norm_sub_le _ _
  · have : ¬ DifferentiableAt ℝ (fun x => f x - g x) y := by
      intro h
      apply hf
      have := h.add hg
      convert this using 1
      funext x; simp
    rw [deriv_zero_of_not_differentiableAt this, norm_zero]; positivity

lemma c03m_aux_lam_pos {Y Λ A c₀ : ℝ} {Ck : ℕ → ℝ} {k₀ : ℕ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ}
    (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ) (h : c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ) :
    ∀ x ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ x := by
  intro x hx
  have := (h.2.2.2 x hx).1
  have : 0 < c₀⁻¹ * Λ := by positivity
  linarith

lemma c03m_aux_g_diff (p Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (hlam : ∀ x ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ x) (y : ℝ) (hy : y ∈ Ioo (Y / 4) (4 * Y)) :
    DifferentiableAt ℝ (fun y' => ((p * (p - 1) / 2 * deriv Ψ y' ^ (p - 2) : ℝ) : ℂ) *
      deriv (deriv a) y') y := by
  have hU : IsOpen (Ioo (Y / 4) (4 * Y)) := isOpen_Ioo
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) (Ioo (Y / 4) (4 * Y)) :=
    hΨ.deriv_of_isOpen hU (by simp)
  have hdy : DifferentiableAt ℝ (deriv Ψ) y :=
    (hd.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  have h1 : DifferentiableAt ℝ (fun y' => p * (p - 1) / 2 * deriv Ψ y' ^ (p - 2)) y :=
    (hdy.rpow_const (Or.inl (hlam y hy).ne')).const_mul _
  have h2 : DifferentiableAt ℝ (deriv (deriv a)) y := by
    have : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv a)) := (ha.iterate_deriv 2)
    exact this.differentiable (by simp) y
  exact (Complex.ofRealCLM.differentiableAt.comp y h1).mul h2


lemma c03m_aux_param_sum_bound {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℝ → ℂ)
    (K : ι → ℝ) (M cp : ℝ) (n m : ℕ)
    (h : ∀ i ∈ s, ∀ t ∈ Ioc (0 : ℝ) 1, ‖g i t‖ ≤ K i * M) :
    ‖-(cp : ℂ) * (n : ℂ) * ∑ i ∈ s, c i * ∫ t in (0 : ℝ)..1, (((1 - t) ^ m : ℝ) : ℂ) * g i t‖ ≤
      (|cp| * n * ∑ i ∈ s, ‖c i‖ * K i) * M := by
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
    mul_assoc, Finset.mul_sum, Finset.sum_mul]
  have hcn : 0 ≤ |cp| * (n : ℝ) := by positivity
  rw [← mul_assoc]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hcn).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul, mul_assoc _ (‖c i‖ * K i), mul_assoc (‖c i‖)]
  apply mul_le_mul_of_nonneg_left _ hcn
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := K i * M)
    (f := fun t => (((1 - t) ^ m : ℝ) : ℂ) * g i t) (fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h0 : 0 ≤ 1 - t := by linarith [ht.2]
      have h1 : |(1 - t) ^ m| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg h0 m)]; exact pow_le_one₀ h0 (by linarith [ht.1])
      calc |(1 - t) ^ m| * ‖g i t‖ ≤ 1 * ‖g i t‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ K i * M := by rw [one_mul]; exact h i hi t ht)
  simpa using this

lemma c03m_aux_finite_order {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∃ k, P i k) : ∃ K, ∀ i ∈ s, ∃ k ≤ K, P i k := by
  classical
  choose! f hf using h
  exact ⟨s.sup f, fun i hi => ⟨f i, Finset.le_sup hi, hf i hi⟩⟩


lemma c03m_aux_m_deriv (p x : ℝ) (k : ℕ) :
    iteratedDeriv k (fun ξ : ℝ => ξ ^ p) x = (descPochhammer ℝ k).eval p * x ^ (p - k) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

/-- Locally near `z = 0`, `F_y` is the unrestricted product. -/
lemma c03m_aux_F_eventuallyEq (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (y z : ℝ)
    (hz : y + z ∈ Ioo (Y / 4) (4 * Y)) :
    c03_mult_F Y a Ψ y =ᶠ[𝓝 z]
      fun z' => a (y + z') * Complex.exp (Complex.I * (c03_mult_Theta Ψ y z' : ℂ)) := by
  have : ∀ᶠ z' in 𝓝 z, y + z' ∈ Ioo (Y / 4) (4 * Y) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hz)
  filter_upwards [this] with z' hz'
  simp [c03_mult_F, hz']

lemma c03m_aux_F_jets (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (y : ℝ)
    (hy : y ∈ Ioo (Y / 4) (4 * Y)) :
    iteratedDeriv 0 (c03_mult_F Y a Ψ y) 0 = a y ∧
    iteratedDeriv 1 (c03_mult_F Y a Ψ y) 0 = deriv a y ∧
    iteratedDeriv 2 (c03_mult_F Y a Ψ y) 0 =
      deriv (deriv a) y + Complex.I * ((deriv (deriv Ψ) y : ℝ) : ℂ) * a y := by
  set U := Ioo (Y / 4) (4 * Y)
  have hU : IsOpen U := isOpen_Ioo
  have hdΨ : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) U := hΨ.deriv_of_isOpen hU (by simp)
  have hΨd : ∀ x ∈ U, HasDerivAt Ψ (deriv Ψ x) x := fun x hx =>
    ((hΨ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hld : ∀ x ∈ U, HasDerivAt (deriv Ψ) (deriv (deriv Ψ) x) x := fun x hx =>
    ((hdΨ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have had : ∀ x, HasDerivAt a (deriv a x) x := fun x =>
    (ha.differentiable (by simp) x).hasDerivAt
  have hadd : ∀ x, HasDerivAt (deriv a) (deriv (deriv a) x) x := fun x =>
    ((ha.iterate_deriv 1).differentiable (by simp) x).hasDerivAt
  set V := {z : ℝ | y + z ∈ U}
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have h0V : (0 : ℝ) ∈ V := by simpa [V] using hy
  -- the phase and its derivatives
  set θ1 : ℝ → ℝ := fun z => deriv Ψ (y + z) - deriv Ψ y
  set E : ℝ → ℂ := fun z => Complex.exp (Complex.I * (c03_mult_Theta Ψ y z : ℂ))
  have hΘ : ∀ z ∈ V, HasDerivAt (c03_mult_Theta Ψ y) (θ1 z) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => Ψ (y + z)) (deriv Ψ (y + z)) z :=
      HasDerivAt.comp_const_add y z (hΨd (y + z) hz)
    have := (h1.sub_const (Ψ y)).sub ((hasDerivAt_id z).const_mul (deriv Ψ y))
    convert this using 1
    · funext w; simp [c03_mult_Theta]
    · simp [θ1]
  have hθ1 : ∀ z ∈ V, HasDerivAt θ1 (deriv (deriv Ψ) (y + z)) z := by
    intro z hz
    exact (HasDerivAt.comp_const_add y z (hld (y + z) hz)).sub_const (deriv Ψ y)
  have hE : ∀ z ∈ V, HasDerivAt E (E z * (Complex.I * (θ1 z : ℂ))) z := by
    intro z hz
    have h := ((hΘ z hz).ofReal_comp).const_mul Complex.I
    have := h.cexp
    simpa [E, mul_comm, mul_left_comm, mul_assoc] using this
  set G : ℝ → ℂ := fun z => a (y + z) * E z
  set G1 : ℝ → ℂ := fun z => deriv a (y + z) * E z + a (y + z) * (E z * (Complex.I * (θ1 z : ℂ)))
  have hG : ∀ z ∈ V, HasDerivAt G (G1 z) z := by
    intro z hz
    have ha' : HasDerivAt (fun z => a (y + z)) (deriv a (y + z)) z :=
      HasDerivAt.comp_const_add y z (had (y + z))
    exact ha'.mul (hE z hz)
  have hFG : ∀ z ∈ V, c03_mult_F Y a Ψ y =ᶠ[𝓝 z] G := fun z hz =>
    c03m_aux_F_eventuallyEq Y a Ψ y z hz
  have hdF : deriv (c03_mult_F Y a Ψ y) =ᶠ[𝓝 0] G1 := by
    filter_upwards [hV.mem_nhds h0V] with z hz
    rw [(hFG z hz).deriv_eq]; exact (hG z hz).deriv
  have hE0 : E 0 = 1 := by simp [E, c03_mult_Theta]
  have hθ0 : θ1 0 = 0 := by simp [θ1]
  refine ⟨?_, ?_, ?_⟩
  · have hy' : Y / 4 < y ∧ y < 4 * Y := hy
    simp [iteratedDeriv_zero, c03_mult_F, hy', c03_mult_Theta]
  · rw [iteratedDeriv_one, hdF.eq_of_nhds]; simp [G1, hE0, hθ0]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hdF.deriv_eq]
    have hadd' : HasDerivAt (fun z => deriv a (y + z)) (deriv (deriv a) (y + 0)) 0 :=
      HasDerivAt.comp_const_add y 0 (hadd (y + 0))
    have ha' : HasDerivAt (fun z => a (y + z)) (deriv a (y + 0)) 0 :=
      HasDerivAt.comp_const_add y 0 (had (y + 0))
    have hθc : HasDerivAt (fun z => ((θ1 z : ℝ) : ℂ)) ((deriv (deriv Ψ) (y + 0) : ℝ) : ℂ) 0 :=
      (hθ1 0 h0V).ofReal_comp
    have hd := (hadd'.mul (hE 0 h0V)).add (ha'.mul ((hE 0 h0V).mul (hθc.const_mul Complex.I)))
    have hG1 : G1 = fun z => deriv a (y + z) * E z + a (y + z) * (E z * (Complex.I * (θ1 z : ℂ))) :=
      rfl
    have hd' : HasDerivAt
        (fun z => deriv a (y + z) * E z + a (y + z) * (E z * (Complex.I * (θ1 z : ℂ)))) _ 0 := hd
    rw [hG1, hd'.deriv]
    simp only [hE0, hθ0, add_zero]
    push_cast
    ring_nf
    simp [hθ0]


lemma c03m_aux_two_term_B (p : ℝ) : (∀ (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 0 < Y → ContDiff ℝ (⊤ : ℕ∞) a →
      tsupport a ⊆ Ioo (Y / 4) (4 * Y) → ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)) →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ x) → ∀ y ∈ Icc Y (2 * Y),
        c03_mult_B p Y a Ψ 0 y = ((deriv Ψ y ^ p : ℝ) : ℂ) * a y ∧
        c03_mult_B p Y a Ψ 1 y = -Complex.I * ((p * deriv Ψ y ^ (p - 1) : ℝ) : ℂ) * deriv a y ∧
        c03_mult_B p Y a Ψ 2 y = -((p * (p - 1) / 2 * deriv Ψ y ^ (p - 2) : ℝ) : ℂ) *
          (deriv (deriv a) y + Complex.I * ((deriv (deriv Ψ) y : ℝ) : ℂ) * a y)) := by
  intro Y a Ψ hY ha _ hΨ _ y hy
  have hyU : y ∈ Ioo (Y / 4) (4 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨j0, j1, j2⟩ := c03m_aux_F_jets Y a Ψ ha hΨ y hyU
  refine ⟨?_, ?_, ?_⟩ <;> unfold c03_mult_B
  · rw [j0, c03m_aux_m_deriv]; simp
  · rw [j1, c03m_aux_m_deriv]; simp
  · rw [j2, c03m_aux_m_deriv]
    simp [descPochhammer_succ_right]
    push_cast
    ring_nf


lemma c03m_aux_two_term_bound (p : ℝ) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ j : ℕ, j ≤ 1 → ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck 4 a Ψ → ∀ y ∈ Icc Y (2 * Y),
        ‖iteratedDeriv j (fun y' => ((p * (p - 1) / 2 * deriv Ψ y' ^ (p - 2) : ℝ) : ℂ) *
            deriv (deriv a) y') y‖ ≤ C * A * Y ^ (-(2 : ℝ) - j) * Λ ^ (p - 2) := by
  intro j hj Ck
  set c := p * (p - 1) / 2
  set K2 := (c₀⁻¹) ^ (p - 2)
  set K3 := (c₀⁻¹) ^ (p - 3)
  have hK2 : 0 < K2 := Real.rpow_pos_of_pos (by positivity) _
  have hK3 : 0 < K3 := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨|c| * K2 * |Ck 2| + |c| * |p - 2| * K3 * |Ck 1| * |Ck 2| + |c| * K2 * |Ck 3| + 1,
    by positivity, ?_⟩
  intro Y Λ A a Ψ hY hΛ hA hyp y hy
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hyU : y ∈ Ioo (Y / 4) (4 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨ha, -, hΨ, hb⟩ := hyp
  obtain ⟨hl1, -, hk⟩ := hb y hyU
  obtain ⟨l, hl_def⟩ : ∃ l, deriv Ψ y = l := ⟨_, rfl⟩
  rw [hl_def] at hl1
  have hL : 0 < c₀⁻¹ * Λ := by positivity
  have hl : 0 < l := lt_of_lt_of_le hL hl1
  have hpow : ∀ q : ℝ, q ≤ 0 → l ^ q ≤ (c₀⁻¹) ^ q * Λ ^ q := fun q hq => by
    rw [← Real.mul_rpow (by positivity) hΛ0.le]
    exact Real.rpow_le_rpow_of_nonpos hL hl1 hq
  have ha2 : ‖deriv (deriv a) y‖ ≤ Ck 2 * A * Y ^ (-(2 : ℝ)) := by
    have := (hk 2 (by norm_num)).2
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this
  have ha3 : ‖deriv (deriv (deriv a)) y‖ ≤ Ck 3 * A * Y ^ (-(3 : ℝ)) := by
    have := (hk 3 (by norm_num)).2
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this
  have hl' : |deriv (deriv Ψ) y| ≤ Ck 1 * Λ * Y ^ (-(1 : ℝ)) := by
    have := (hk 1 (by norm_num)).1
    simpa [iteratedDeriv_one] using this
  have hY2 : 0 < Y ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hY0 _
  have hY1 : 0 < Y ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hY0 _
  have hY3 : Y ^ (-(3 : ℝ)) = Y ^ (-(1 : ℝ)) * Y ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hY0]; norm_num
  have hΛ2 : 0 < Λ ^ (p - 2) := Real.rpow_pos_of_pos hΛ0 _
  have hΛ3 : Λ ^ (p - 3) * Λ = Λ ^ (p - 2) := by
    rw [← Real.rpow_add_one hΛ0.ne']; ring_nf
  have hlp2 : l ^ (p - 2) ≤ K2 * Λ ^ (p - 2) := hpow _ (by linarith)
  have hlp3 : l ^ (p - 3) ≤ K3 * Λ ^ (p - 3) := hpow _ (by linarith)
  have hl2 : 0 ≤ l ^ (p - 2) := Real.rpow_nonneg hl.le _
  have hl3 : 0 ≤ l ^ (p - 3) := Real.rpow_nonneg hl.le _
  have hA2 : ‖deriv (deriv a) y‖ ≤ |Ck 2| * A * Y ^ (-(2 : ℝ)) :=
    ha2.trans (by gcongr; exact le_abs_self _)
  have hA3 : ‖deriv (deriv (deriv a)) y‖ ≤ |Ck 3| * A * (Y ^ (-(1 : ℝ)) * Y ^ (-(2 : ℝ))) :=
    hY3 ▸ ha3.trans (by gcongr; exact le_abs_self _)
  have hL1 : |deriv (deriv Ψ) y| ≤ |Ck 1| * Λ * Y ^ (-(1 : ℝ)) :=
    hl'.trans (by gcongr; exact le_abs_self _)
  interval_cases j
  · simp only [iteratedDeriv_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hl2]
    simp only [CharP.cast_eq_zero, sub_zero]
    rw [hl_def, abs_of_nonneg hl2]
    calc |c| * l ^ (p - 2) * ‖deriv (deriv a) y‖
        ≤ |c| * (K2 * Λ ^ (p - 2)) * (|Ck 2| * A * Y ^ (-(2 : ℝ))) := by gcongr
      _ = (|c| * K2 * |Ck 2|) * A * Y ^ (-(2 : ℝ)) * Λ ^ (p - 2) := by ring
      _ ≤ _ := by
        have hX : 0 ≤ A * Y ^ (-(2 : ℝ)) * Λ ^ (p - 2) := by positivity
        have : 0 ≤ |c| * |p - 2| * K3 * |Ck 1| * |Ck 2| + |c| * K2 * |Ck 3| := by positivity
        have e : ∀ X : ℝ, X * A * Y ^ (-(2 : ℝ)) * Λ ^ (p - 2) = X * (A * Y ^ (-(2 : ℝ)) * Λ ^ (p - 2)) :=
          fun X => by ring
        rw [e, e]
        exact mul_le_mul_of_nonneg_right (by linarith) hX
  · simp only [iteratedDeriv_one]
    have hd1 : HasDerivAt (deriv Ψ) (deriv (deriv Ψ) y) y := by
      have hU : IsOpen (Ioo (Y / 4) (4 * Y)) := isOpen_Ioo
      have hdΨ : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) (Ioo (Y / 4) (4 * Y)) :=
        hΨ.deriv_of_isOpen hU (by simp)
      exact ((hdΨ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hyU)).hasDerivAt
    have hr := ((hd1.rpow_const (p := p - 2) (Or.inl (hl_def ▸ hl.ne'))).const_mul c).ofReal_comp
    have ha'' : HasDerivAt (deriv (deriv a)) (deriv (deriv (deriv a)) y) y :=
      ((ha.iterate_deriv 2).differentiable (by simp) y).hasDerivAt
    have hd := hr.mul ha''
    have hd' : HasDerivAt (fun y' => ((c * deriv Ψ y' ^ (p - 2) : ℝ) : ℂ) * deriv (deriv a) y')
        _ y := hd
    rw [hd'.deriv]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hl2]
    have e : p - 2 - 1 = p - 3 := by ring
    rw [e, hl_def, abs_of_nonneg hl3, abs_of_nonneg hl2]
    simp only [Nat.cast_one]
    have hpos : 0 ≤ A * Y ^ (-(2 : ℝ) - 1) * Λ ^ (p - 2) := by positivity
    have hY21 : Y ^ (-(2 : ℝ) - 1) = Y ^ (-(1 : ℝ)) * Y ^ (-(2 : ℝ)) := by
      rw [← hY3]; norm_num
    calc |c| * (|deriv (deriv Ψ) y| * |p - 2| * l ^ (p - 3)) * ‖deriv (deriv a) y‖ +
          |c| * l ^ (p - 2) * ‖deriv (deriv (deriv a)) y‖
        ≤ |c| * ((|Ck 1| * Λ * Y ^ (-(1 : ℝ))) * |p - 2| * (K3 * Λ ^ (p - 3))) *
            (|Ck 2| * A * Y ^ (-(2 : ℝ))) +
          |c| * (K2 * Λ ^ (p - 2)) * (|Ck 3| * A * (Y ^ (-(1 : ℝ)) * Y ^ (-(2 : ℝ)))) := by
          gcongr
      _ = (|c| * |p - 2| * K3 * |Ck 1| * |Ck 2|) * A * (Y ^ (-(1 : ℝ)) * Y ^ (-(2 : ℝ))) *
            (Λ ^ (p - 3) * Λ) +
          (|c| * K2 * |Ck 3|) * A * (Y ^ (-(1 : ℝ)) * Y ^ (-(2 : ℝ))) * Λ ^ (p - 2) := by ring
      _ ≤ _ := by
        rw [hΛ3, ← hY21]
        have : 0 ≤ |c| * K2 * |Ck 2| := by positivity
        have e : ∀ X : ℝ, X * A * Y ^ (-(2 : ℝ) - 1) * Λ ^ (p - 2) =
            X * (A * Y ^ (-(2 : ℝ) - 1) * Λ ^ (p - 2)) := fun X => by ring
        rw [e, e, e, ← add_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) hpos


/-- The majorant `min(x^{-p}, x^{-1-p})` of the singular kernel is integrable on `(0,∞)`. -/
lemma c03m_aux_majorant_integrableOn {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (fun x : ℝ => if x ≤ 1 then x ^ (-p) else x ^ (-1 - p)) (Ioi 0) := by
  have h1 : IntegrableOn (fun x : ℝ => if x ≤ 1 then x ^ (-p) else x ^ (-1 - p)) (Ioc 0 1) := by
    have : IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -p) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp [hx.2]
  have h2 : IntegrableOn (fun x : ℝ => if x ≤ 1 then x ^ (-p) else x ^ (-1 - p)) (Ioi 1) := by
    have : IntegrableOn (fun x : ℝ => x ^ (-1 - p)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [not_le.2 (show (1 : ℝ) < x from hx)]
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

/-- A continuous function vanishing linearly at `0` and bounded is integrable against
`|z|^{-1-p}`. -/
lemma c03m_aux_kernel_integrable {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {h : ℝ → ℂ}
    (hh : AEStronglyMeasurable h) {K : ℝ} (h1 : ∀ z, ‖h z‖ ≤ K * |z|) (h2 : ∀ z, ‖h z‖ ≤ K) :
    Integrable (fun z => h z / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
  have hm := GSQG.Lib.integrable_comp_abs_of_integrableOn_Ioi (c03m_aux_majorant_integrableOn hp hp1)
  refine (hm.const_mul K).mono' ?_ (Eventually.of_forall fun z => ?_)
  · have hc : Continuous (fun z : ℝ => ((|z| ^ (1 + p) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr (by linarith)))
    exact (hh.aemeasurable.div hc.measurable.aemeasurable).aestronglyMeasurable
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases eq_or_ne z 0 with rfl | hz
    · simp
      have := h2 0
      have : 0 ≤ K := (norm_nonneg _).trans this
      rw [Real.zero_rpow (by linarith), div_zero]
      positivity
    have hz' : 0 < |z| := abs_pos.mpr hz
    have hpos : 0 < |z| ^ (1 + p) := Real.rpow_pos_of_pos hz' _
    rw [div_le_iff₀ hpos]
    split_ifs with hle
    · calc ‖h z‖ ≤ K * |z| := h1 z
        _ = K * |z| ^ (-p) * |z| ^ (1 + p) := by
          rw [mul_assoc, ← Real.rpow_add hz']; simp
    · calc ‖h z‖ ≤ K := h2 z
        _ = K * |z| ^ (-1 - p) * |z| ^ (1 + p) := by
          rw [mul_assoc, ← Real.rpow_add hz']; simp


/-- Bounds for a `C¹` compactly supported function: `‖G(x+w) - G x‖ ≤ M|w|` and
`‖G(x+w) - G x‖ ≤ M`. -/
lemma c03m_aux_lip_bound {G : ℝ → ℂ} (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G) :
    ∃ M, 0 ≤ M ∧ ∀ x w : ℝ, ‖G (x + w) - G x‖ ≤ M * |w| ∧ ‖G (x + w) - G x‖ ≤ M := by
  obtain ⟨L, hL⟩ := hG.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  obtain ⟨B, hB⟩ := hG.continuous.bounded_above_of_compact_support hc
  refine ⟨L + 2 * max B 0, by positivity, fun x w => ⟨?_, ?_⟩⟩
  · have := hL.dist_le_mul (x + w) x
    rw [dist_eq_norm, Real.dist_eq] at this
    simp only [add_sub_cancel_left] at this
    calc _ ≤ (L : ℝ) * |w| := this
      _ ≤ _ := by gcongr; have := le_max_right B 0; linarith
  · calc ‖G (x + w) - G x‖ ≤ ‖G (x + w)‖ + ‖G x‖ := norm_sub_le _ _
      _ ≤ max B 0 + max B 0 := add_le_add ((hB _).trans (le_max_left _ _))
          ((hB _).trans (le_max_left _ _))
      _ ≤ _ := by have : (0 : ℝ) ≤ L := L.2; linarith

lemma c03m_aux_tsupport_compact {Y : ℝ} {a : ℝ → ℂ} (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) :
    IsCompact (tsupport a) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport a) (has.trans Ioo_subset_Icc_self)

lemma c03m_aux_zero_near {Y : ℝ} {a : ℝ → ℂ} (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) {x : ℝ}
    (hx : x ∉ Ioo (Y / 4) (4 * Y)) : a =ᶠ[𝓝 x] 0 :=
  notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (has h))

/-- `a e^{iΨ}` (localized by `tsupport a`) is smooth, with compact support. -/
lemma c03m_aux_prod_smooth {Y : ℝ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) ∧
    HasCompactSupport (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) := by
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ Ioo (Y / 4) (4 * Y)
    · have hΨx : ContDiffAt ℝ (⊤ : ℕ∞) Ψ x := hΨ.contDiffAt (isOpen_Ioo.mem_nhds hx)
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => ((Ψ x : ℝ) : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x hΨx
      exact ha.contDiffAt.mul (Complex.contDiff_exp.contDiffAt.comp x
        (contDiffAt_const.mul h1))
    · have h0 := c03m_aux_zero_near has hx
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [h0] with x' hx'
      simp [hx']
  · exact HasCompactSupport.mul_right (f := a) (c03m_aux_tsupport_compact has)

/--  is smooth with compact support (for any ). -/
lemma c03m_aux_F_smooth {Y : ℝ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (y : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (c03_mult_F Y a Ψ y) ∧ HasCompactSupport (c03_mult_F Y a Ψ y) := by
  refine ⟨contDiff_iff_contDiffAt.2 fun z => ?_, ?_⟩
  · by_cases hz : y + z ∈ Ioo (Y / 4) (4 * Y)
    · refine ContDiffAt.congr_of_eventuallyEq ?_ (c03m_aux_F_eventuallyEq Y a Ψ y z hz)
      have hsh : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' : ℝ => y + z') z :=
        contDiffAt_const.add contDiffAt_id
      have hΨx : ContDiffAt ℝ (⊤ : ℕ∞) Ψ (y + z) := hΨ.contDiffAt (isOpen_Ioo.mem_nhds hz)
      have hΘ : ContDiffAt ℝ (⊤ : ℕ∞) (c03_mult_Theta Ψ y) z := by
        unfold c03_mult_Theta
        exact ((hΨx.comp z hsh).sub contDiffAt_const).sub (contDiffAt_const.mul contDiffAt_id)
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' => ((c03_mult_Theta Ψ y z' : ℝ) : ℂ)) z :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp z hΘ
      exact (ha.contDiffAt.comp z hsh).mul (Complex.contDiff_exp.contDiffAt.comp z
        (contDiffAt_const.mul h1))
    · have h0 := c03m_aux_zero_near has hz
      have h0' : ∀ᶠ z' in 𝓝 z, a (y + z') = 0 :=
        ((continuous_const.add continuous_id).tendsto z).eventually h0
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [h0'] with z' hz'
      simp [c03_mult_F, hz']
  · refine HasCompactSupport.intro ((c03m_aux_tsupport_compact has).image
      (continuous_id.sub continuous_const : Continuous fun x : ℝ => x - y)) (fun z hz => ?_)
    have : y + z ∉ tsupport a := fun h => hz ⟨y + z, h, by simp⟩
    simp [c03_mult_F, image_eq_zero_of_notMem_tsupport this]

lemma c03m_aux_norm_exp_I (l z : ℝ) : ‖Complex.exp (Complex.I * (l : ℂ) * (z : ℂ))‖ = 1 := by
  rw [show Complex.I * (l : ℂ) * (z : ℂ) = ((l * z : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The pointwise identity `e^{-iΨ(y)} a(y+w) e^{iΨ(y+w)} = e^{iλ(y)w} F_y(w)`. -/
lemma c03m_aux_F_shift {Y : ℝ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y))
    (y w : ℝ) :
    Complex.exp (-(Complex.I * (Ψ y : ℂ))) * (a (y + w) * Complex.exp (Complex.I * (Ψ (y + w) : ℂ))) =
      Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * w) * c03_mult_F Y a Ψ y w := by
  by_cases hw : y + w ∈ Ioo (Y / 4) (4 * Y)
  · simp only [c03_mult_F, hw, ite_true]
    have : Complex.exp (-(Complex.I * (Ψ y : ℂ))) * Complex.exp (Complex.I * (Ψ (y + w) : ℂ)) =
        Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * w) *
          Complex.exp (Complex.I * (c03_mult_Theta Ψ y w : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [c03_mult_Theta]; push_cast; ring
    linear_combination a (y + w) * this
  · have h0 : a (y + w) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hw (has h))
    simp [c03_mult_F, hw, h0]


lemma c03m_aux_gauss_norm (η z : ℝ) : ‖Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ = Real.exp (-(η * z ^ 2)) := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]

lemma c03m_aux_gauss_le (η z : ℝ) (hη : 0 ≤ η) : ‖Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ ≤ 1 := by
  rw [c03m_aux_gauss_norm, Real.exp_le_one_iff]; nlinarith [sq_nonneg z]

/-- Regularized moment integrands are integrable. -/
lemma c03m_aux_moment_integrable {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (l η : ℝ) (hη : 0 < η)
    (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun z : ℝ => Complex.exp (Complex.I * (l : ℂ) * z) * (z : ℂ) ^ m *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
  have hs : -1 < (m : ℝ) - 1 - p := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hmaj := GSQG.Lib.integrable_comp_abs_of_integrableOn_Ioi
    (integrableOn_rpow_mul_exp_neg_mul_sq hη hs)
  refine hmaj.mono' ?_ (Eventually.of_forall fun z => ?_)
  · have hc : Continuous (fun z : ℝ => ((|z| ^ (1 + p) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr (by linarith)))
    have hn : Continuous (fun z : ℝ => Complex.exp (Complex.I * (l : ℂ) * z) * (z : ℂ) ^ m *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))) := by fun_prop
    exact (hn.aemeasurable.div hc.measurable.aemeasurable).aestronglyMeasurable
  · rw [norm_div, norm_mul, norm_mul, c03m_aux_norm_exp_I, c03m_aux_gauss_norm, one_mul,
      norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |z| ^ (1 + p)), sq_abs]
    rcases eq_or_ne z 0 with rfl | hz
    · rw [abs_zero, Real.zero_rpow (by linarith), div_zero]
      positivity
    have hz' : 0 < |z| := abs_pos.mpr hz
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hz' _), mul_right_comm, ← Real.rpow_add hz',
      ← Real.rpow_natCast]
    ring_nf; rfl


/-- `y`-partial derivative of a function on `ℝ × ℝ`. -/
lemma c03m_aux_partial_hasDerivAt {H : ℝ × ℝ → ℂ} {y z : ℝ}
    (h : DifferentiableAt ℝ H (y, z)) :
    HasDerivAt (fun y' => H (y', z)) (fderiv ℝ H (y, z) ((1 : ℝ), (0 : ℝ))) y := by
  have h1 : HasDerivAt (fun y' : ℝ => (y', z)) ((1 : ℝ), (0 : ℝ)) y :=
    (hasDerivAt_id y).prodMk (hasDerivAt_const y z)
  exact h.hasFDerivAt.comp_hasDerivAt y h1

/-- Hypotheses of the parametric-integral lemma are stable under `∂_y`. -/
lemma c03m_aux_partial_hyp {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ)) (hsupp : ∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ H q ((1 : ℝ), (0 : ℝ))) (V ×ˢ univ) ∧
    ∀ y ∈ V, ∀ z ∉ K, fderiv ℝ H (y, z) ((1 : ℝ), (0 : ℝ)) = 0 := by
  have hS : IsOpen (V ×ˢ (univ : Set ℝ)) := hV.prod isOpen_univ
  refine ⟨?_, fun y hy z hz => ?_⟩
  · have := hH.fderiv_of_isOpen hS (m := (⊤ : ℕ∞)) (by exact_mod_cast le_rfl)
    exact (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ), (0 : ℝ))).contDiff.comp_contDiffOn this
  · have hd : DifferentiableAt ℝ H (y, z) :=
      (hH.differentiableOn (by simp)).differentiableAt (hS.mem_nhds ⟨hy, trivial⟩)
    have h1 := c03m_aux_partial_hasDerivAt hd
    have h0 : HasDerivAt (fun y' => H (y', z)) 0 y := by
      refine (hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hV.mem_nhds hy] with y' hy'
      exact hsupp y' hy' z hz
    exact h1.unique h0

lemma c03m_aux_param_hasDerivAt {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} (hK : IsCompact K)
    {w : ℝ → ℂ} (hwm : AEStronglyMeasurable w) (hw : IntegrableOn w K) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ)) (hsupp : ∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0)
    (y₀ : ℝ) (hy₀ : y₀ ∈ V) :
    HasDerivAt (fun y => ∫ z, w z * H (y, z))
      (∫ z, w z * fderiv ℝ H (y₀, z) ((1 : ℝ), (0 : ℝ))) y₀ := by
  have hS : IsOpen (V ×ˢ (univ : Set ℝ)) := hV.prod isOpen_univ
  obtain ⟨hD, hDs⟩ := c03m_aux_partial_hyp hV hH hsupp
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV y₀ hy₀
  have hcb : Metric.closedBall y₀ (ε / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεV
  have hcpt : IsCompact (Metric.closedBall y₀ (ε / 2) ×ˢ K) :=
    (isCompact_closedBall _ _).prod hK
  have hsub : Metric.closedBall y₀ (ε / 2) ×ˢ K ⊆ V ×ˢ univ :=
    prod_mono hcb (subset_univ _)
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (hD.continuousOn.mono hsub)
  have hcont : ∀ y ∈ V, Continuous fun z => H (y, z) := fun y hy =>
    hH.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hy, trivial⟩)
  have hcontD : ∀ y ∈ V, Continuous fun z => fderiv ℝ H (y, z) ((1 : ℝ), (0 : ℝ)) :=
    fun y hy => hD.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hy, trivial⟩)
  have hball : Metric.ball y₀ (ε / 2) ∈ 𝓝 y₀ := Metric.ball_mem_nhds _ (by linarith)
  have hbV : Metric.ball y₀ (ε / 2) ⊆ V := Metric.ball_subset_closedBall.trans hcb
  have hint0 : Integrable (fun z => w z * H (y₀, z)) := by
    refine (hw.mul_continuousOn (hcont y₀ hy₀).continuousOn hK).integrable_of_forall_notMem_eq_zero
      (fun z hz => ?_)
    simp [hsupp y₀ hy₀ z hz]
  have hK' : MeasurableSet K := hK.measurableSet
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun y z => w z * fderiv ℝ H (y, z) ((1 : ℝ), (0 : ℝ)))
    (bound := K.indicator fun z => ‖w z‖ * M) hball ?_ hint0 ?_ ?_ ?_ ?_).2
  · filter_upwards [hV.mem_nhds hy₀] with y hy
    exact hwm.mul (hcont y hy).aestronglyMeasurable
  · exact hwm.mul (hcontD y₀ hy₀).aestronglyMeasurable
  · refine Eventually.of_forall fun z y hy => ?_
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_left (hM (y, z) ⟨Metric.ball_subset_closedBall hy, hz⟩)
        (norm_nonneg _)
    · rw [indicator_of_notMem hz, hDs y (hbV hy) z hz]; simp
  · exact (IntegrableOn.integrable_indicator (Integrable.mul_const hw.norm M) hK')
  · refine Eventually.of_forall fun z y hy => ?_
    have hd : DifferentiableAt ℝ H (y, z) :=
      (hH.differentiableOn (by simp)).differentiableAt (hS.mem_nhds ⟨hbV hy, trivial⟩)
    exact (c03m_aux_partial_hasDerivAt hd).const_mul (w z)

/-- Smoothness of a weighted parametric integral with jointly smooth, uniformly compactly
supported integrand. -/
lemma c03m_aux_param_contDiffOn {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} (hK : IsCompact K)
    {w : ℝ → ℂ} (hwm : AEStronglyMeasurable w) (hw : IntegrableOn w K) :
    ∀ n : ℕ, ∀ H : ℝ × ℝ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ) →
      (∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0) →
      ContDiffOn ℝ n (fun y => ∫ z, w z * H (y, z)) V := by
  intro n
  induction n with
  | zero =>
    intro H hH hsupp
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun y hy => (c03m_aux_param_hasDerivAt hV hK hwm hw hH hsupp y hy).continuousAt
      |>.continuousWithinAt
  | succ n ih =>
    intro H hH hsupp
    obtain ⟨hD, hDs⟩ := c03m_aux_partial_hyp hV hH hsupp
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hV]
    refine ⟨fun y hy => (c03m_aux_param_hasDerivAt hV hK hwm hw hH hsupp y hy).differentiableAt
      |>.differentiableWithinAt, by simp, ?_⟩
    refine (ih _ hD hDs).congr fun y hy => ?_
    exact (c03m_aux_param_hasDerivAt hV hK hwm hw hH hsupp y hy).deriv

lemma c03m_aux_param_smooth {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} (hK : IsCompact K)
    {w : ℝ → ℂ} (hwm : AEStronglyMeasurable w) (hw : IntegrableOn w K) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ)) (hsupp : ∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ∫ z, w z * H (y, z)) V :=
  contDiffOn_infty.2 fun n => c03m_aux_param_contDiffOn hV hK hwm hw n H hH hsupp


lemma c03m_aux_tsupport_iteratedDeriv (f : ℝ → ℂ) (k : ℕ) :
    tsupport (iteratedDeriv k f) ⊆ tsupport f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset (𝕜 := ℝ)).trans ih

lemma c03m_aux_iteratedDeriv_contDiffOn {U : Set ℝ} (hU : IsOpen U) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U) (k : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k Ψ) U := by
  induction k with
  | zero => simpa using hΨ
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 ih).2

/-- A localized product `[ℓ ∈ U] A(ℓ) B` is smooth when `A` is supported inside `U`. -/
lemma c03m_aux_localized_smooth {U : Set ℝ} [DecidablePred (· ∈ U)] (hU : IsOpen U) {A : ℝ → ℂ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : tsupport A ⊆ U) {ℓ : ℝ × ℝ → ℝ}
    (hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ) {S : Set (ℝ × ℝ)} (hS : IsOpen S) {B : ℝ × ℝ → ℂ}
    (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (S ∩ ℓ ⁻¹' U)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => if ℓ q ∈ U then A (ℓ q) * B q else 0) S := by
  intro q hq
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hqU : ℓ q ∈ U
  · have hO : S ∩ ℓ ⁻¹' U ∈ 𝓝 q :=
      (hS.inter (hU.preimage hℓ.continuous)).mem_nhds ⟨hq, hqU⟩
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => A (ℓ q) * B q) q :=
      (hA.contDiffAt.comp q hℓ.contDiffAt).mul (hB.contDiffAt hO)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hO] with q' hq'
    have : ℓ q' ∈ U := hq'.2
    simp only [this, ↓reduceIte]
  · have h0 : A =ᶠ[𝓝 (ℓ q)] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 (fun h => hqU (hAs h))
    have h0' : ∀ᶠ q' in 𝓝 q, A (ℓ q') = 0 := (hℓ.continuous.tendsto q).eventually h0
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [h0'] with q' hq'
    simp [hq']

/-- Derivatives of `Θ_y`: for `k ≥ 1` and `y, y + w` in the phase interval,
`Θ_y^{(k)}(w) = Ψ^{(k)}(y+w) - [k = 1] Ψ'(y)`. -/
lemma c03m_aux_Theta_iteratedDeriv {U : Set ℝ} (hU : IsOpen U) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U) (y w : ℝ) (hw : y + w ∈ U) (k : ℕ) (hk : 1 ≤ k) :
    iteratedDeriv k (c03_mult_Theta Ψ y) w =
      iteratedDeriv k Ψ (y + w) - if k = 1 then deriv Ψ y else 0 := by
  have hΨw : ContDiffAt ℝ k Ψ (y + w) :=
    (hΨ.contDiffAt (hU.mem_nhds hw)).of_le (by exact_mod_cast le_top)
  have h1 : ContDiffAt ℝ k (fun w => Ψ (y + w)) w :=
    hΨw.comp w (contDiffAt_const.add contDiffAt_id)
  have hfun : c03_mult_Theta Ψ y = fun w => (Ψ (y + w) - Ψ y) - deriv Ψ y * w := by
    funext w; simp [c03_mult_Theta]
  have hl : ContDiffAt ℝ k (fun w : ℝ => deriv Ψ y * w) w := contDiffAt_const.mul contDiffAt_id
  have hc' : ContDiffAt ℝ k (fun _ : ℝ => Ψ y) w := contDiffAt_const
  rw [hfun, iteratedDeriv_fun_sub (h1.sub hc') hl, iteratedDeriv_fun_sub h1 hc']
  rw [iteratedDeriv_comp_const_add]
  have hc : iteratedDeriv k (fun _ : ℝ => Ψ y) w = 0 := by
    rw [iteratedDeriv_const]; simp; omega
  rw [hc, sub_zero]
  congr 1
  rcases Nat.lt_or_ge 1 k with h | h
  · simp only [show ¬ k = 1 by omega, ↓reduceIte]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    simp
  · obtain rfl : k = 1 := by omega
    simp


/-- The phase-derivative product appearing in `b_t`, written with derivatives of `Ψ`. -/
def c03m_aux_Pi (Ψ : ℝ → ℝ) {n : ℕ} (q : Fin n → ℕ) (y x : ℝ) : ℂ :=
  ∏ i, ((iteratedDeriv (i.val + 1) Ψ x - if i.val = 0 then deriv Ψ y else 0 : ℝ) : ℂ) ^ q i

lemma c03m_aux_bt_eq {Y : ℝ} (a : ℝ → ℂ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (N r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (y t z : ℝ) :
    c03_mult_bt Y a Ψ N r q y t z = (z : ℂ) ^ (2 * N - 1) *
      (if y + t * z ∈ Ioo (Y / 4) (4 * Y) then
        iteratedDeriv r a (y + t * z) * c03m_aux_Pi Ψ q y (y + t * z) else 0) := by
  unfold c03_mult_bt
  split_ifs with h
  · rw [mul_assoc]
    congr 2
    unfold c03m_aux_Pi
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [c03m_aux_Theta_iteratedDeriv isOpen_Ioo hΨ y (t * z) h (i.val + 1) (by omega)]
    simp
  · simp

lemma c03m_aux_Pi_smooth {Y : ℝ} {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) {n : ℕ} (q : Fin n → ℕ) (t : ℝ)
    {V : Set ℝ} (hV : V ⊆ Ioo (Y / 4) (4 * Y)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03m_aux_Pi Ψ q w.1 (w.1 + t * w.2))
      ((V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) := by
  have hU : IsOpen (Ioo (Y / 4) (4 * Y)) := isOpen_Ioo
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => w.1 + t * w.2) := by fun_prop
  unfold c03m_aux_Pi
  refine contDiffOn_prod fun i _ => ?_
  refine ContDiffOn.pow ?_ _
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
  refine ContDiffOn.sub ?_ ?_
  · exact (c03m_aux_iteratedDeriv_contDiffOn hU hΨ (i.val + 1)).comp hℓ.contDiffOn
      (fun w hw => hw.2)
  · split_ifs
    · have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) (Ioo (Y / 4) (4 * Y)) :=
        ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hΨ).2
      exact hd.comp contDiff_fst.contDiffOn (fun w hw => hV hw.1.1)
    · exact contDiffOn_const

lemma c03m_aux_phit_smooth {Y : ℝ} {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (t : ℝ)
    {V : Set ℝ} (hV : V ⊆ Ioo (Y / 4) (4 * Y)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_phit Ψ w.1 t w.2)
      ((V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) := by
  have hU : IsOpen (Ioo (Y / 4) (4 * Y)) := isOpen_Ioo
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => w.1 + t * w.2) := by fun_prop
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) (Ioo (Y / 4) (4 * Y)) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hΨ).2
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => deriv Ψ w.1)
      ((V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) :=
    hd.comp contDiff_fst.contDiffOn (fun w hw => hV hw.1.1)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => Ψ (w.1 + t * w.2))
      ((V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) :=
    hΨ.comp hℓ.contDiffOn (fun w hw => hw.2)
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => Ψ w.1)
      ((V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) :=
    hΨ.comp contDiff_fst.contDiffOn (fun w hw => hV hw.1.1)
  unfold c03_mult_phit c03_mult_Theta
  exact (h1.mul contDiff_snd.contDiffOn).add ((h2.sub h3).sub (h1.mul (contDiffOn_const.mul
    contDiff_snd.contDiffOn)))


lemma c03m_aux_weight_meas (p : ℝ) (hp : 0 < p) (n : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => (z : ℂ) ^ n / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
  have hc : Continuous (fun z : ℝ => ((|z| ^ (1 + p) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_abs.rpow_const (fun _ => Or.inr (by linarith)))
  have hn : Continuous (fun z : ℝ => (z : ℂ) ^ n) := by fun_prop
  exact (hn.aemeasurable.div hc.measurable.aemeasurable).aestronglyMeasurable

lemma c03m_aux_weight_integrableOn {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 1 ≤ n)
    (R : ℝ) : IntegrableOn (fun z : ℝ => (z : ℂ) ^ n / ((|z| ^ (1 + p) : ℝ) : ℂ)) (Icc (-R) R) := by
  have hm := (GSQG.Lib.integrable_comp_abs_of_integrableOn_Ioi
    (c03m_aux_majorant_integrableOn hp hp1)).const_mul (max 1 (|R| ^ n))
  refine (hm.integrableOn).mono' (c03m_aux_weight_meas p hp n).restrict
    (ae_restrict_of_forall_mem measurableSet_Icc fun z hz => ?_)
  have hzR : |z| ≤ |R| := by
    rw [abs_le] at *; constructor <;> cases' abs_cases R with h h <;> linarith [hz.1, hz.2]
  rw [norm_div, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |z| ^ (1 + p))]
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [abs_zero, Real.zero_rpow (by linarith), div_zero]
    have : 0 ≤ (if |(0 : ℝ)| ≤ 1 then |(0 : ℝ)| ^ (-p) else |(0 : ℝ)| ^ (-1 - p)) := by
      split_ifs <;> positivity
    have : (0 : ℝ) ≤ max 1 (|R| ^ n) := le_max_of_le_left zero_le_one
    positivity
  have hz' : 0 < |z| := abs_pos.mpr hz0
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hz' _)]
  split_ifs with hle
  · have h1 : |z| ^ n ≤ |z| := by
      calc |z| ^ n ≤ |z| ^ 1 := pow_le_pow_of_le_one (abs_nonneg _) hle hn
        _ = |z| := pow_one _
    have e : |z| ^ (-p) * |z| ^ (1 + p) = |z| := by rw [← Real.rpow_add hz']; simp
    calc |z| ^ n ≤ |z| := h1
      _ = 1 * (|z| ^ (-p) * |z| ^ (1 + p)) := by rw [e, one_mul]
      _ ≤ max 1 (|R| ^ n) * (|z| ^ (-p) * |z| ^ (1 + p)) := by
          gcongr; exact le_max_left _ _
      _ = _ := by ring
  · have e : |z| ^ (-1 - p) * |z| ^ (1 + p) = 1 := by rw [← Real.rpow_add hz']; simp
    calc |z| ^ n ≤ |R| ^ n := pow_le_pow_left₀ (abs_nonneg _) hzR n
      _ ≤ max 1 (|R| ^ n) := le_max_right _ _
      _ = max 1 (|R| ^ n) * (|z| ^ (-1 - p) * |z| ^ (1 + p)) := by rw [e, mul_one]
      _ = _ := by ring

/-- `w · G` is integrable when `G` is continuous and vanishes off a compact `K` on which `w`
is integrable. -/
lemma c03m_aux_wG_integrable {K : Set ℝ} (hK : IsCompact K) {w G : ℝ → ℂ}
    (hw : IntegrableOn w K) (hG : Continuous G) (hGK : ∀ z ∉ K, G z = 0) :
    Integrable (fun z => w z * G z) :=
  (hw.mul_continuousOn hG.continuousOn hK).integrable_of_forall_notMem_eq_zero
    (fun z hz => by simp [hGK z hz])

/-- `e^{iu} - e^{iv} = i(u-v) ∫₀¹ e^{i((1-σ)v+σu)} dσ`. -/
lemma c03m_aux_exp_interp (u v : ℝ) :
    Complex.exp (Complex.I * (u : ℂ)) - Complex.exp (Complex.I * (v : ℂ)) =
      Complex.I * ((u - v : ℝ) : ℂ) *
        ∫ σ in (0 : ℝ)..1, Complex.exp (Complex.I * (((1 - σ) * v + σ * u : ℝ) : ℂ)) := by
  rw [← intervalIntegral.integral_const_mul]
  have hd : ∀ σ ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun σ : ℝ => Complex.exp (Complex.I * (((1 - σ) * v + σ * u : ℝ) : ℂ)))
      (Complex.I * ((u - v : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((1 - σ) * v + σ * u : ℝ) : ℂ))) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => (1 - σ) * v + σ * u) (u - v) σ := by
      have := ((hasDerivAt_id σ).const_sub 1).mul_const v |>.add ((hasDerivAt_id σ).mul_const u)
      convert this using 1
      · funext x; simp only [Pi.add_apply, id]
      · ring
    have := ((h1.ofReal_comp).const_mul Complex.I).cexp
    convert this using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
  · refine (Continuous.intervalIntegrable (by fun_prop) _ _)


/-- Iterated `y`-partial derivatives of a function on `ℝ × ℝ`. -/
def c03m_aux_partialN (H : ℝ × ℝ → ℂ) : ℕ → ℝ × ℝ → ℂ
  | 0 => H
  | k + 1 => fun q => fderiv ℝ (c03m_aux_partialN H k) q ((1 : ℝ), (0 : ℝ))

lemma c03m_aux_partialN_hyp {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ)) (hsupp : ∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0) :
    ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (c03m_aux_partialN H k) (V ×ˢ univ) ∧
      ∀ y ∈ V, ∀ z ∉ K, c03m_aux_partialN H k (y, z) = 0 := by
  intro k
  induction k with
  | zero => exact ⟨hH, hsupp⟩
  | succ k ih => exact c03m_aux_partial_hyp hV ih.1 ih.2

lemma c03m_aux_partialN_eq {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ)) (hsupp : ∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0) :
    ∀ k, ∀ y ∈ V, ∀ z, iteratedDeriv k (fun y' => H (y', z)) y = c03m_aux_partialN H k (y, z) := by
  have hS : IsOpen (V ×ˢ (univ : Set ℝ)) := hV.prod isOpen_univ
  intro k
  induction k with
  | zero => intro y _ z; simp [c03m_aux_partialN]
  | succ k ih =>
    intro y hy z
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun y' => H (y', z)) =ᶠ[𝓝 y]
        fun y' => c03m_aux_partialN H k (y', z) := by
      filter_upwards [hV.mem_nhds hy] with y' hy' using ih y' hy' z
    rw [hev.deriv_eq]
    have hd : DifferentiableAt ℝ (c03m_aux_partialN H k) (y, z) :=
      (((c03m_aux_partialN_hyp hV hH hsupp k).1).differentiableOn (by simp)).differentiableAt
        (hS.mem_nhds ⟨hy, trivial⟩)
    exact (c03m_aux_partial_hasDerivAt hd).deriv

lemma c03m_aux_param_iteratedDeriv {V : Set ℝ} (hV : IsOpen V) {K : Set ℝ} (hK : IsCompact K)
    {w : ℝ → ℂ} (hwm : AEStronglyMeasurable w) (hw : IntegrableOn w K) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ)) (hsupp : ∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0) :
    ∀ k, ∀ y ∈ V, iteratedDeriv k (fun y => ∫ z, w z * H (y, z)) y =
      ∫ z, w z * c03m_aux_partialN H k (y, z) := by
  intro k
  induction k with
  | zero => intro y _; simp [c03m_aux_partialN]
  | succ k ih =>
    intro y hy
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun y => ∫ z, w z * H (y, z)) =ᶠ[𝓝 y]
        fun y => ∫ z, w z * c03m_aux_partialN H k (y, z) := by
      filter_upwards [hV.mem_nhds hy] with y' hy' using ih y' hy'
    rw [hev.deriv_eq]
    obtain ⟨h1, h2⟩ := c03m_aux_partialN_hyp hV hH hsupp k
    exact (c03m_aux_param_hasDerivAt hV hK hwm hw h1 h2 y hy).deriv

/-- Representation of the summand integrand as `w(z) H(y,z)` with `H` jointly smooth on
`(Y/2,3Y) × ℝ` and uniformly compactly supported in `z`. -/
lemma c03m_aux_I_repr {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (N r : ℕ) (hN : 1 ≤ N)
    (q : Fin (2 * N - 1) → ℕ) {Y : ℝ} (hY : 0 < Y) {a : ℝ → ℂ} {Ψ : ℝ → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y))
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (η t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ∃ H : ℝ × ℝ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Ioo (Y / 2) (3 * Y) ×ˢ univ) ∧
      (∀ y ∈ Ioo (Y / 2) (3 * Y), ∀ z ∉ Icc (-(8 * Y / t)) (8 * Y / t), H (y, z) = 0) ∧
      ∀ y z, Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) =
        ((z : ℂ) ^ (2 * N - 1) / ((|z| ^ (1 + p) : ℝ) : ℂ)) * H (y, z) := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hV : IsOpen V := isOpen_Ioo
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have ht0 : 0 < t := ht.1
  set K := Icc (-(8 * Y / t)) (8 * Y / t) with hK_def
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 + t * w.2 with hℓ_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ := by fun_prop
  set S := V ×ˢ (univ : Set ℝ) with hS_def
  have hS : IsOpen S := hV.prod isOpen_univ
  have hout : ∀ y ∈ V, ∀ z ∉ K, y + t * z ∉ U := by
    intro y hy z hz hU'
    simp only [hK_def, mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · have : t * z < -(8 * Y) := by
        have := (lt_div_iff₀ ht0).1 (show z < -(8 * Y) / t by rw [neg_div]; exact hz)
        linarith
      linarith [hU'.1, hy.2]
    · have : 8 * Y < t * z := by
        have := (div_lt_iff₀ ht0).1 hz
        linarith
      linarith [hU'.2, hy.1]
  set A := iteratedDeriv r a
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    rw [show A = deriv^[r] a from iteratedDeriv_eq_iterate]; exact ha.iterate_deriv r
  have hAs : tsupport A ⊆ U := (c03m_aux_tsupport_iteratedDeriv a r).trans has
  set P : ℝ × ℝ → ℂ := fun w => c03m_aux_Pi Ψ q w.1 (w.1 + t * w.2)
  have hP := c03m_aux_Pi_smooth hΨ q t hVU
  have hφ := c03m_aux_phit_smooth hΨ t hVU
  have hE : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => Complex.exp (Complex.I *
      (c03_mult_phit Ψ w.1 t w.2 : ℂ) - ((η * w.2 ^ 2 : ℝ) : ℂ))) (S ∩ ℓ ⁻¹' U) := by
    refine Complex.contDiff_exp.comp_contDiffOn ?_
    refine (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)).sub ?_
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_const.mul (contDiff_snd.contDiffOn.pow 2))
  refine ⟨fun w => if ℓ w ∈ U then A (ℓ w) * (P w * Complex.exp (Complex.I *
      (c03_mult_phit Ψ w.1 t w.2 : ℂ) - ((η * w.2 ^ 2 : ℝ) : ℂ))) else 0,
    c03m_aux_localized_smooth hU hA hAs hℓ hS (hP.mul hE), fun y hy z hz => ?_, fun y z => ?_⟩
  · simp [ℓ, hout y hy z hz]
  · rw [c03m_aux_bt_eq a hΨ N r q y t z]
    simp only [ℓ, P, A]
    split_ifs <;> ring

/-- Smoothness of `y ↦ I_η(y,t)` on `(Y/2,3Y)` and differentiation under the integral sign. -/
lemma c03m_aux_I_smooth_formula (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (N : ℕ) (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) (Y : ℝ) (hY : 0 < Y) (a : ℝ → ℂ) (Ψ : ℝ → ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y))
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (η : ℝ) :
        ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => c03_mult_I p Y a Ψ N r q η y' t)
          (Ioo (Y / 2) (3 * Y)) ∧
        (∀ i : ℕ, ∀ y ∈ Ioo (Y / 2) (3 * Y),
          Integrable (fun z : ℝ => iteratedDeriv i (fun y' =>
            Complex.exp (Complex.I * (c03_mult_phit Ψ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
              c03_mult_bt Y a Ψ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y) ∧
          iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y =
            ∫ z : ℝ, iteratedDeriv i (fun y' =>
              Complex.exp (Complex.I * (c03_mult_phit Ψ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
                c03_mult_bt Y a Ψ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y) := by
  obtain ⟨H, hH, hs, heq⟩ := c03m_aux_I_repr hp hp1 N r hN q hY ha has hΨ η t ht
  have hV : IsOpen (Ioo (Y / 2) (3 * Y)) := isOpen_Ioo
  have hK : IsCompact (Icc (-(8 * Y / t)) (8 * Y / t)) := isCompact_Icc
  have hwK := c03m_aux_weight_integrableOn hp hp1 (2 * N - 1) (by omega) (8 * Y / t)
  have hwm := c03m_aux_weight_meas p hp (2 * N - 1)
  have hI : (fun y' => c03_mult_I p Y a Ψ N r q η y' t) =
      fun y' => ∫ z : ℝ, ((z : ℂ) ^ (2 * N - 1) / ((|z| ^ (1 + p) : ℝ) : ℂ)) * H (y', z) := by
    funext y'; unfold c03_mult_I; simp_rw [heq]
  have hpt : ∀ i, ∀ y ∈ Ioo (Y / 2) (3 * Y), ∀ z, iteratedDeriv i (fun y' =>
      Complex.exp (Complex.I * (c03_mult_phit Ψ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y =
      ((z : ℂ) ^ (2 * N - 1) / ((|z| ^ (1 + p) : ℝ) : ℂ)) * c03m_aux_partialN H i (y, z) := by
    intro i y hy z
    simp_rw [heq]
    rw [iteratedDeriv_const_mul_field, c03m_aux_partialN_eq hV hH hs i y hy z]
  refine ⟨?_, fun i y hy => ⟨?_, ?_⟩⟩
  · rw [hI]; exact c03m_aux_param_smooth hV hK hwm hwK hH hs
  · obtain ⟨h1, h2⟩ := c03m_aux_partialN_hyp hV hH hs i
    have hc : Continuous fun z => c03m_aux_partialN H i (y, z) :=
      h1.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => ⟨hy, trivial⟩)
    exact (c03m_aux_wG_integrable hK hwK hc (h2 y hy)).congr
      (Eventually.of_forall fun z => (hpt i y hy z).symm)
  · rw [hI, c03m_aux_param_iteratedDeriv hV hK hwm hwK hH hs i y hy]
    congr 1; funext z; exact (hpt i y hy z).symm


/-! ### Two-variable mixed-derivative API -/

/-- Iterated directional derivatives of a function on `ℝ × ℝ`. -/
def c03m_aux_pd (v : ℝ × ℝ) (H : ℝ × ℝ → ℂ) : ℕ → ℝ × ℝ → ℂ
  | 0 => H
  | k + 1 => fun q => fderiv ℝ (c03m_aux_pd v H k) q v

/-- The mixed derivative `∂_y^a ∂_z^b F` at `(y,z)`, as it appears in the statements. -/
def c03m_aux_M (F : ℝ × ℝ → ℂ) (a b : ℕ) (y z : ℝ) : ℂ :=
  iteratedDeriv a (fun y' => iteratedDeriv b (fun z' => F (y', z')) z) y

lemma c03m_aux_pd_smooth {W : Set (ℝ × ℝ)} (hW : IsOpen W) (v : ℝ × ℝ) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (c03m_aux_pd v H k) W := by
  intro k
  induction k with
  | zero => exact hH
  | succ k ih =>
    have := ih.fderiv_of_isOpen hW (m := (⊤ : ℕ∞)) (by exact_mod_cast le_rfl)
    exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp_contDiffOn this

/-- `z`-derivatives of a jointly smooth function are the directional iterates in direction
`(0,1)`. -/
lemma c03m_aux_pdz_eq {W : Set (ℝ × ℝ)} (hW : IsOpen W) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) :
    ∀ k, ∀ q ∈ W, iteratedDeriv k (fun z' => H (q.1, z')) q.2 =
      c03m_aux_pd ((0 : ℝ), (1 : ℝ)) H k q := by
  intro k
  induction k with
  | zero => intro q _; simp [c03m_aux_pd]
  | succ k ih =>
    intro q hq
    rw [iteratedDeriv_succ]
    have hc : Continuous fun z' : ℝ => ((q.1, z') : ℝ × ℝ) := continuous_const.prodMk continuous_id
    have hW' : ∀ᶠ z' in 𝓝 q.2, ((q.1, z') : ℝ × ℝ) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hq)
    have hev : iteratedDeriv k (fun z' => H (q.1, z')) =ᶠ[𝓝 q.2]
        fun z' => c03m_aux_pd ((0 : ℝ), (1 : ℝ)) H k (q.1, z') := by
      filter_upwards [hW'] with z' hz' using ih _ hz'
    rw [hev.deriv_eq]
    have hd : DifferentiableAt ℝ (c03m_aux_pd ((0 : ℝ), (1 : ℝ)) H k) q :=
      ((c03m_aux_pd_smooth hW _ hH k).differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)
    have h1 : HasDerivAt (fun z' : ℝ => ((q.1, z') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    have := hd.hasFDerivAt.comp_hasDerivAt q.2 (by simpa using h1)
    exact this.deriv

lemma c03m_aux_pdy_eq {W : Set (ℝ × ℝ)} (hW : IsOpen W) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) :
    ∀ k, ∀ q ∈ W, iteratedDeriv k (fun y' => H (y', q.2)) q.1 =
      c03m_aux_pd ((1 : ℝ), (0 : ℝ)) H k q := by
  intro k
  induction k with
  | zero => intro q _; simp [c03m_aux_pd]
  | succ k ih =>
    intro q hq
    rw [iteratedDeriv_succ]
    have hc : Continuous fun y' : ℝ => ((y', q.2) : ℝ × ℝ) := continuous_id.prodMk continuous_const
    have hW' : ∀ᶠ y' in 𝓝 q.1, ((y', q.2) : ℝ × ℝ) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hq)
    have hev : iteratedDeriv k (fun y' => H (y', q.2)) =ᶠ[𝓝 q.1]
        fun y' => c03m_aux_pd ((1 : ℝ), (0 : ℝ)) H k (y', q.2) := by
      filter_upwards [hW'] with y' hy' using ih _ hy'
    rw [hev.deriv_eq]
    have hd : DifferentiableAt ℝ (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) H k) q :=
      ((c03m_aux_pd_smooth hW _ hH k).differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)
    have h1 : HasDerivAt (fun y' : ℝ => ((y', q.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q.1 :=
      (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
    have := hd.hasFDerivAt.comp_hasDerivAt q.1 (by simpa using h1)
    exact this.deriv

/-- Mixed derivatives as iterated directional derivatives. -/
lemma c03m_aux_M_eq {W : Set (ℝ × ℝ)} (hW : IsOpen W) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) (a b : ℕ) {y z : ℝ} (hq : (y, z) ∈ W) :
    c03m_aux_M H a b y z = c03m_aux_pd ((1 : ℝ), (0 : ℝ))
      (c03m_aux_pd ((0 : ℝ), (1 : ℝ)) H b) a (y, z) := by
  unfold c03m_aux_M
  have hc : Continuous fun y' : ℝ => ((y', z) : ℝ × ℝ) := continuous_id.prodMk continuous_const
  have hW' : ∀ᶠ y' in 𝓝 y, ((y', z) : ℝ × ℝ) ∈ W :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hq)
  have hev : (fun y' => iteratedDeriv b (fun z' => H (y', z')) z) =ᶠ[𝓝 y]
      fun y' => c03m_aux_pd ((0 : ℝ), (1 : ℝ)) H b (y', z) := by
    filter_upwards [hW'] with y' hy' using c03m_aux_pdz_eq hW hH b (y', z) hy'
  rw [hev.iteratedDeriv_eq]
  exact c03m_aux_pdy_eq hW (c03m_aux_pd_smooth hW _ hH b) a (y, z) hq

/-- Mixed derivatives only depend on the germ at `(y,z)`. -/
lemma c03m_aux_M_congr {F G : ℝ × ℝ → ℂ} {y z : ℝ} (h : F =ᶠ[𝓝 (y, z)] G) (a b : ℕ) :
    c03m_aux_M F a b y z = c03m_aux_M G a b y z := by
  rw [nhds_prod_eq] at h
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.1 h
  unfold c03m_aux_M
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hu] with y' hy'
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hv] with z' hz'
  exact huv ⟨hy', hz'⟩

/-- Two-variable Leibniz rule for mixed derivatives. -/
lemma c03m_aux_M_mul {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) (j s : ℕ) {y z : ℝ}
    (hq : (y, z) ∈ W) :
    c03m_aux_M (fun w => F w * G w) j s y z =
      ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
        (j.choose a : ℂ) * (s.choose b : ℂ) * (c03m_aux_M F a b y z *
          c03m_aux_M G (j - a) (s - b) y z) := by
  have hFG : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => F w * G w) W := hF.mul hG
  rw [c03m_aux_M_eq hW hFG j s hq]
  have hc : Continuous fun y' : ℝ => ((y', z) : ℝ × ℝ) := continuous_id.prodMk continuous_const
  have hW' : ∀ᶠ y' in 𝓝 y, ((y', z) : ℝ × ℝ) ∈ W :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hq)
  set PF := fun b => c03m_aux_pd ((0 : ℝ), (1 : ℝ)) F b
  set PG := fun b => c03m_aux_pd ((0 : ℝ), (1 : ℝ)) G b
  have hPF : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (PF b) W := c03m_aux_pd_smooth hW _ hF
  have hPG : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (PG b) W := c03m_aux_pd_smooth hW _ hG
  -- inner Leibniz in `z`
  have hin : ∀ q ∈ W, c03m_aux_pd ((0 : ℝ), (1 : ℝ)) (fun w => F w * G w) s q =
      ∑ b ∈ Finset.range (s + 1), (s.choose b : ℂ) * (PF b q * PG (s - b) q) := by
    intro q hqW
    rw [← c03m_aux_pdz_eq hW hFG s q hqW]
    have hcz : Continuous fun z' : ℝ => ((q.1, z') : ℝ × ℝ) :=
      continuous_const.prodMk continuous_id
    have hWz : ((q.1, q.2) : ℝ × ℝ) ∈ W := hqW
    have hFz : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' => F (q.1, z')) q.2 :=
      (hF.contDiffAt (hW.mem_nhds hWz)).comp q.2 (contDiff_const.prodMk contDiff_id).contDiffAt
    have hGz : ContDiffAt ℝ (⊤ : ℕ∞) (fun z' => G (q.1, z')) q.2 :=
      (hG.contDiffAt (hW.mem_nhds hWz)).comp q.2 (contDiff_const.prodMk contDiff_id).contDiffAt
    rw [iteratedDeriv_fun_mul (hFz.of_le (by exact_mod_cast le_top))
      (hGz.of_le (by exact_mod_cast le_top))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [c03m_aux_pdz_eq hW hF b q hqW, c03m_aux_pdz_eq hW hG (s - b) q hqW]
    simp only [PF, PG]; push_cast; ring
  -- outer Leibniz in `y`
  rw [← c03m_aux_pdy_eq hW (c03m_aux_pd_smooth hW _ hFG s) j (y, z) hq]
  have hev : (fun y' => c03m_aux_pd ((0 : ℝ), (1 : ℝ)) (fun w => F w * G w) s (y', z)) =ᶠ[𝓝 y]
      fun y' => ∑ b ∈ Finset.range (s + 1), (s.choose b : ℂ) * (PF b (y', z) * PG (s - b) (y', z)) := by
    filter_upwards [hW'] with y' hy' using hin _ hy'
  rw [hev.iteratedDeriv_eq]
  have hyc : ∀ (P : ℝ × ℝ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) P W →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' => P (y', z)) y := fun P hP =>
    (hP.contDiffAt (hW.mem_nhds hq)).comp y (contDiff_id.prodMk contDiff_const).contDiffAt
  rw [iteratedDeriv_fun_sum (fun b _ => ((contDiffAt_const.mul ((hyc _ (hPF b)).mul
    (hyc _ (hPG (s - b))))).of_le (by exact_mod_cast le_top)))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul
    ((hyc _ (hPF b)).of_le (by exact_mod_cast le_top))
    ((hyc _ (hPG (s - b))).of_le (by exact_mod_cast le_top)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have e1 : iteratedDeriv a (fun y' => PF b (y', z)) y = c03m_aux_M F a b y z := by
    rw [c03m_aux_M_eq hW hF a b hq, ← c03m_aux_pdy_eq hW (hPF b) a (y, z) hq]
  have e2 : iteratedDeriv (j - a) (fun y' => PG (s - b) (y', z)) y =
      c03m_aux_M G (j - a) (s - b) y z := by
    rw [c03m_aux_M_eq hW hG (j - a) (s - b) hq, ← c03m_aux_pdy_eq hW (hPG (s - b)) (j - a) (y, z) hq]
  rw [e1, e2]; ring


lemma c03m_aux_pd_congr {W : Set (ℝ × ℝ)} (hW : IsOpen W) (v : ℝ × ℝ) {H₁ H₂ : ℝ × ℝ → ℂ}
    (h : ∀ w ∈ W, H₁ w = H₂ w) : ∀ k, ∀ w ∈ W, c03m_aux_pd v H₁ k w = c03m_aux_pd v H₂ k w := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro w hw
    have hev : c03m_aux_pd v H₁ k =ᶠ[𝓝 w] c03m_aux_pd v H₂ k := by
      filter_upwards [hW.mem_nhds hw] with w' hw' using ih w' hw'
    simp only [c03m_aux_pd]
    rw [hev.fderiv_eq]

lemma c03m_aux_iteratedDeriv_contDiffOnC {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (k : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 ih).2

/-- A Fréchet derivative applied to a vector is a one-variable derivative. -/
lemma c03m_aux_fderiv_dir {H : ℝ × ℝ → ℂ} {w : ℝ × ℝ} (hd : DifferentiableAt ℝ H w)
    (v : ℝ × ℝ) : fderiv ℝ H w v = deriv (fun s : ℝ => H (w + s • v)) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => w + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd.hasFDerivAt h1 (by simp)
  exact this.deriv.symm

/-- Directional derivatives of `f(w₁ + t w₂)`. -/
lemma c03m_aux_pd_comp {U' : Set ℝ} (hU' : IsOpen U') {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U') (t : ℝ) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hWU : ∀ w ∈ W, w.1 + t * w.2 ∈ U') (v : ℝ × ℝ) :
    ∀ k, ∀ w ∈ W, c03m_aux_pd v (fun w => f (w.1 + t * w.2)) k w =
      ((v.1 + t * v.2 : ℝ) : ℂ) ^ k * iteratedDeriv k f (w.1 + t * w.2) := by
  intro k
  induction k with
  | zero => intro w _; simp [c03m_aux_pd]
  | succ k ih =>
    intro w hw
    have hev : c03m_aux_pd v (fun w => f (w.1 + t * w.2)) k =ᶠ[𝓝 w]
        fun w => ((v.1 + t * v.2 : ℝ) : ℂ) ^ k * iteratedDeriv k f (w.1 + t * w.2) := by
      filter_upwards [hW.mem_nhds hw] with w' hw' using ih w' hw'
    simp only [c03m_aux_pd]
    rw [hev.fderiv_eq]
    have hdk : DifferentiableAt ℝ (iteratedDeriv k f) (w.1 + t * w.2) :=
      ((c03m_aux_iteratedDeriv_contDiffOnC hU' hf k).differentiableOn (by simp)).differentiableAt
        (hU'.mem_nhds (hWU w hw))
    have hF : DifferentiableAt ℝ
        (fun w : ℝ × ℝ => ((v.1 + t * v.2 : ℝ) : ℂ) ^ k * iteratedDeriv k f (w.1 + t * w.2)) w := by
      have hl : DifferentiableAt ℝ (fun w : ℝ × ℝ => w.1 + t * w.2) w := by fun_prop
      exact (differentiableAt_const _).mul (DifferentiableAt.comp (g := iteratedDeriv k f) w hdk hl)
    rw [c03m_aux_fderiv_dir hF]
    have h1 : HasDerivAt (fun s : ℝ => (w + s • v).1 + t * (w + s • v).2) (v.1 + t * v.2) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const v.1).add
        (((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_mul t)
      convert this.const_add (w.1 + t * w.2) using 1
      · funext s; simp; ring
      · simp
    have hfk : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f (w.1 + t * w.2))
        (w.1 + t * w.2) := by
      rw [iteratedDeriv_succ]; exact hdk.hasDerivAt
    have hy0 : w.1 + t * w.2 = (w + (0 : ℝ) • v).1 + t * (w + (0 : ℝ) • v).2 := by simp
    have := (HasDerivAt.scomp_of_eq (0 : ℝ) hfk h1 hy0).const_mul
      (((v.1 + t * v.2 : ℝ) : ℂ) ^ k)
    rw [show (fun s : ℝ => ((v.1 + t * v.2 : ℝ) : ℂ) ^ k * iteratedDeriv k f ((w + s • v).1 +
        t * (w + s • v).2)) = fun y => ((v.1 + t * v.2 : ℝ) : ℂ) ^ k *
        (iteratedDeriv k f ∘ fun s => (w + s • v).1 + t * (w + s • v).2) y from rfl, this.deriv]
    simp only [Complex.real_smul]
    push_cast; ring

/-- Mixed derivatives of `f(y + t z)`. -/
lemma c03m_aux_M_comp {U' : Set ℝ} (hU' : IsOpen U') {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U') (t : ℝ) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hWU : ∀ w ∈ W, w.1 + t * w.2 ∈ U') (a b : ℕ) {y z : ℝ} (hq : (y, z) ∈ W) :
    c03m_aux_M (fun w => f (w.1 + t * w.2)) a b y z =
      (t : ℂ) ^ b * iteratedDeriv (a + b) f (y + t * z) := by
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => f (w.1 + t * w.2)) W :=
    hf.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ × ℝ => w.1 + t * w.2).contDiffOn
      (fun w hw => hWU w hw)
  rw [c03m_aux_M_eq hW hF a b hq]
  set g : ℝ → ℂ := fun x => (t : ℂ) ^ b * iteratedDeriv b f x
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g U' :=
    contDiffOn_const.mul (c03m_aux_iteratedDeriv_contDiffOnC hU' hf b)
  have h1 : ∀ w ∈ W, c03m_aux_pd ((0 : ℝ), (1 : ℝ)) (fun w => f (w.1 + t * w.2)) b w =
      g (w.1 + t * w.2) := by
    intro w hw
    rw [c03m_aux_pd_comp hU' hf t hW hWU _ b w hw]; simp [g]
  rw [c03m_aux_pd_congr hW _ h1 a (y, z) hq,
    c03m_aux_pd_comp hU' hg t hW hWU _ a (y, z) hq]
  simp only [g, iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply]
  simp

/-- Mixed derivatives of a function of `y` alone. -/
lemma c03m_aux_M_fst (g : ℝ → ℂ) (a b : ℕ) (y z : ℝ) :
    c03m_aux_M (fun w => g w.1) a b y z = if b = 0 then iteratedDeriv a g y else 0 := by
  unfold c03m_aux_M
  split_ifs with hb
  · subst hb; simp
  · have : (fun y' => iteratedDeriv b (fun _ : ℝ => g y') z) = fun _ => 0 := by
      funext y'; rw [iteratedDeriv_const]; simp [hb]
    simp only [this]
    rw [iteratedDeriv_const]; split_ifs <;> rfl

/-! ### Pointwise symbol bounds -/

/-- `SB F y z J S c M α β`: `‖∂_y^a ∂_z^b F(y,z)‖ ≤ c M α^a β^b` for `a ≤ J`, `b ≤ S`. -/
def c03m_aux_SB (F : ℝ × ℝ → ℂ) (y z : ℝ) (J S : ℕ) (c M α β : ℝ) : Prop :=
  ∀ a ≤ J, ∀ b ≤ S, ‖c03m_aux_M F a b y z‖ ≤ c * M * α ^ a * β ^ b

lemma c03m_aux_SB_mul {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) {y z : ℝ}
    (hq : (y, z) ∈ W) {J S : ℕ} {c₁ c₂ M₁ M₂ α β : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h₁ : c03m_aux_SB F y z J S c₁ M₁ α β) (h₂ : c03m_aux_SB G y z J S c₂ M₂ α β) :
    c03m_aux_SB (fun w => F w * G w) y z J S (2 ^ (J + S) * c₁ * c₂) (M₁ * M₂) α β := by
  intro j hj s hs
  rw [c03m_aux_M_mul hW hF hG j s hq]
  have hX : 0 ≤ c₁ * c₂ * (M₁ * M₂) * α ^ j * β ^ s := by positivity
  calc _ ≤ ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
        ((j.choose a : ℝ) * (s.choose b : ℝ)) * (c₁ * c₂ * (M₁ * M₂) * α ^ j * β ^ s) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
        have ha' : a ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
        have hb' : b ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
        have e1 := h₁ a (ha'.trans hj) b (hb'.trans hs)
        have e2 := h₂ (j - a) ((Nat.sub_le _ _).trans hj) (s - b) ((Nat.sub_le _ _).trans hs)
        have hpa : α ^ a * α ^ (j - a) = α ^ j := by rw [← pow_add, Nat.add_sub_cancel' ha']
        have hpb : β ^ b * β ^ (s - b) = β ^ s := by rw [← pow_add, Nat.add_sub_cancel' hb']
        calc (j.choose a : ℝ) * (s.choose b : ℝ) * (‖c03m_aux_M F a b y z‖ *
              ‖c03m_aux_M G (j - a) (s - b) y z‖)
            ≤ (j.choose a : ℝ) * (s.choose b : ℝ) * ((c₁ * M₁ * α ^ a * β ^ b) *
              (c₂ * M₂ * α ^ (j - a) * β ^ (s - b))) := by
              gcongr
          _ = _ := by rw [← hpa, ← hpb]; ring
    _ = (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)) * (∑ b ∈ Finset.range (s + 1),
          (s.choose b : ℝ)) * (c₁ * c₂ * (M₁ * M₂) * α ^ j * β ^ s) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
    _ = 2 ^ j * 2 ^ s * (c₁ * c₂ * (M₁ * M₂) * α ^ j * β ^ s) := by
        rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.sum_range_choose, Nat.sum_range_choose]; push_cast; ring
    _ ≤ 2 ^ (J + S) * (c₁ * c₂ * (M₁ * M₂) * α ^ j * β ^ s) := by
        gcongr
        rw [pow_add]; gcongr <;> norm_num
    _ = _ := by ring

lemma c03m_aux_SB_mono {F : ℝ × ℝ → ℂ} {y z : ℝ} {J S : ℕ} {c c' M α β : ℝ}
    (h : c03m_aux_SB F y z J S c M α β) (hcc : c ≤ c') (hM : 0 ≤ M) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    c03m_aux_SB F y z J S c' M α β := fun a ha b hb =>
  (h a ha b hb).trans (by gcongr)

/-- Finite products. -/
lemma c03m_aux_SB_prod {ι : Type*} (s : Finset ι) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    {F : ι → ℝ × ℝ → ℂ} (hF : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F i) W) {y z : ℝ}
    (hq : (y, z) ∈ W) {J S : ℕ} {c M : ι → ℝ} {α β : ℝ} (hc : ∀ i ∈ s, 0 ≤ c i)
    (hM : ∀ i ∈ s, 0 ≤ M i) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : ∀ i ∈ s, c03m_aux_SB (F i) y z J S (c i) (M i) α β) :
    c03m_aux_SB (fun w => ∏ i ∈ s, F i w) y z J S (2 ^ ((J + S) * s.card) * ∏ i ∈ s, c i)
      (∏ i ∈ s, M i) α β := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro a ha b hb
    simp only [Finset.prod_empty, Finset.card_empty, mul_zero, pow_zero, one_mul]
    have h1 := c03m_aux_M_fst (fun _ => (1 : ℂ)) a b y z
    rw [h1]
    split_ifs with hb0
    · rw [iteratedDeriv_const]
      split_ifs with ha0
      · subst ha0; subst hb0; simp
      · simp; positivity
    · simp; positivity
  | insert i s hi ih =>
    have hF' : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F i) W := fun j hj => hF j (by simp [hj])
    have ih' := ih hF' (fun j hj => hc j (by simp [hj])) (fun j hj => hM j (by simp [hj]))
      (fun j hj => h j (by simp [hj]))
    have hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ∏ j ∈ s, F j w) W :=
      contDiffOn_prod fun j hj => hF' j hj
    have hci := hc i (by simp)
    have hcs : 0 ≤ 2 ^ ((J + S) * s.card) * ∏ j ∈ s, c j :=
      mul_nonneg (by positivity) (Finset.prod_nonneg fun j hj => hc j (by simp [hj]))
    have hMs : 0 ≤ ∏ j ∈ s, M j := Finset.prod_nonneg fun j hj => hM j (by simp [hj])
    have := c03m_aux_SB_mul hW (hF i (by simp)) hP hq hci hcs (hM i (by simp)) hMs hα hβ
      (h i (by simp)) ih'
    intro a ha b hb
    have e := this a ha b hb
    simp only [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    convert e using 2
    rw [mul_add, pow_add]; ring


lemma c03m_aux_M_snd (g : ℝ → ℂ) (a b : ℕ) (y z : ℝ) :
    c03m_aux_M (fun w => g w.2) a b y z = if a = 0 then iteratedDeriv b g z else 0 := by
  unfold c03m_aux_M
  split_ifs with ha
  · subst ha; simp
  · show iteratedDeriv a (fun _ : ℝ => iteratedDeriv b g z) y = 0
    rw [iteratedDeriv_const]; simp [ha]

lemma c03m_aux_SB_z (y z : ℝ) (hz : z ≠ 0) (J S : ℕ) {α : ℝ} (hα : 0 ≤ α) :
    c03m_aux_SB (fun w => ((w.2 : ℝ) : ℂ)) y z J S 1 |z| α |z|⁻¹ := by
  intro a _ b _
  have hz' : 0 < |z| := abs_pos.2 hz
  rw [c03m_aux_M_snd (fun x : ℝ => (x : ℂ)) a b y z]
  split_ifs with ha
  · subst ha
    rcases b with _ | _ | b
    · simp
    · have : iteratedDeriv (0 + 1) (fun x : ℝ => (x : ℂ)) z = 1 := by
        rw [zero_add, iteratedDeriv_one]; exact (hasDerivAt_id z).ofReal_comp.deriv
      rw [this]; simp [hz'.ne']
    · have hd : ∀ x, deriv (fun x : ℝ => (x : ℂ)) x = 1 := fun x =>
        (hasDerivAt_id x).ofReal_comp.deriv
      rw [iteratedDeriv_succ', iteratedDeriv_succ', show deriv (fun x : ℝ => (x : ℂ)) =
        fun _ => 1 from funext hd, deriv_const']
      rw [iteratedDeriv_const]; simp; positivity
  · simp; positivity

lemma c03m_aux_M_sub {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) (a b : ℕ) {y z : ℝ}
    (hq : (y, z) ∈ W) :
    c03m_aux_M (fun w => F w - G w) a b y z = c03m_aux_M F a b y z - c03m_aux_M G a b y z := by
  have hFG : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => F w - G w) W := hF.sub hG
  rw [c03m_aux_M_eq hW hFG a b hq, c03m_aux_M_eq hW hF a b hq, c03m_aux_M_eq hW hG a b hq]
  have h1 : ∀ k, ∀ w ∈ W, c03m_aux_pd ((0 : ℝ), (1 : ℝ)) (fun w => F w - G w) k w =
      c03m_aux_pd ((0 : ℝ), (1 : ℝ)) F k w - c03m_aux_pd ((0 : ℝ), (1 : ℝ)) G k w := by
    intro k
    induction k with
    | zero => intro w _; rfl
    | succ k ih =>
      intro w hw
      have hev : c03m_aux_pd ((0 : ℝ), (1 : ℝ)) (fun w => F w - G w) k =ᶠ[𝓝 w]
          fun w => c03m_aux_pd ((0 : ℝ), (1 : ℝ)) F k w - c03m_aux_pd ((0 : ℝ), (1 : ℝ)) G k w := by
        filter_upwards [hW.mem_nhds hw] with w' hw' using ih w' hw'
      simp only [c03m_aux_pd]
      rw [hev.fderiv_eq, fderiv_fun_sub
        (((c03m_aux_pd_smooth hW _ hF k).differentiableOn (by simp)).differentiableAt (hW.mem_nhds hw))
        (((c03m_aux_pd_smooth hW _ hG k).differentiableOn (by simp)).differentiableAt (hW.mem_nhds hw))]
      rfl
  have h2 : ∀ (P Q : ℝ × ℝ → ℂ), ContDiffOn ℝ (⊤ : ℕ∞) P W → ContDiffOn ℝ (⊤ : ℕ∞) Q W →
      ∀ k, ∀ w ∈ W, c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (fun w => P w - Q w) k w =
      c03m_aux_pd ((1 : ℝ), (0 : ℝ)) P k w - c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Q k w := by
    intro P Q hP hQ k
    induction k with
    | zero => intro w _; rfl
    | succ k ih =>
      intro w hw
      have hev : c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (fun w => P w - Q w) k =ᶠ[𝓝 w]
          fun w => c03m_aux_pd ((1 : ℝ), (0 : ℝ)) P k w - c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Q k w := by
        filter_upwards [hW.mem_nhds hw] with w' hw' using ih w' hw'
      simp only [c03m_aux_pd]
      rw [hev.fderiv_eq, fderiv_fun_sub
        (((c03m_aux_pd_smooth hW _ hP k).differentiableOn (by simp)).differentiableAt (hW.mem_nhds hw))
        (((c03m_aux_pd_smooth hW _ hQ k).differentiableOn (by simp)).differentiableAt (hW.mem_nhds hw))]
      rfl
  rw [c03m_aux_pd_congr hW _ (h1 b) a (y, z) hq]
  exact h2 _ _ (c03m_aux_pd_smooth hW _ hF b) (c03m_aux_pd_smooth hW _ hG b) a (y, z) hq

/-- Symbol bound for `f(y + t z)` from derivative bounds of `f` at `y + t z`. -/
lemma c03m_aux_SB_comp {U' : Set ℝ} (hU' : IsOpen U') {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U') {t Y : ℝ} (ht : 0 ≤ t) (hY : 0 < Y) {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hWU : ∀ w ∈ W, w.1 + t * w.2 ∈ U') {y z : ℝ} (hq : (y, z) ∈ W)
    (hz : z ≠ 0) (htz : t * |z| ≤ 4 * Y) (J S : ℕ) {K Mf : ℝ} (hK : 0 ≤ K) (hMf : 0 ≤ Mf)
    (hbd : ∀ k ≤ J + S, ‖iteratedDeriv k f (y + t * z)‖ ≤ K * Mf * Y⁻¹ ^ k) :
    c03m_aux_SB (fun w => f (w.1 + t * w.2)) y z J S (4 ^ S * K) Mf Y⁻¹ |z|⁻¹ := by
  intro a ha b hb
  rw [c03m_aux_M_comp hU' hf t hW hWU a b hq, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ht]
  have hz' : 0 < |z| := abs_pos.2 hz
  have h1 := hbd (a + b) (by omega)
  have htY : t * Y⁻¹ ≤ 4 * |z|⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ hY]
    calc t = t * |z| * |z|⁻¹ := by field_simp
      _ ≤ 4 * Y * |z|⁻¹ := by gcongr
      _ = _ := by ring
  have h4 : (t * Y⁻¹) ^ b ≤ 4 ^ S * |z|⁻¹ ^ b := by
    calc (t * Y⁻¹) ^ b ≤ (4 * |z|⁻¹) ^ b := pow_le_pow_left₀ (by positivity) htY b
      _ = 4 ^ b * |z|⁻¹ ^ b := mul_pow _ _ _
      _ ≤ 4 ^ S * |z|⁻¹ ^ b := by gcongr; norm_num
  calc t ^ b * ‖iteratedDeriv (a + b) f (y + t * z)‖ ≤ t ^ b * (K * Mf * Y⁻¹ ^ (a + b)) := by
        gcongr
    _ = K * Mf * Y⁻¹ ^ a * (t * Y⁻¹) ^ b := by rw [mul_pow, pow_add]; ring
    _ ≤ K * Mf * Y⁻¹ ^ a * (4 ^ S * |z|⁻¹ ^ b) := by gcongr
    _ = _ := by ring


lemma c03m_aux_iteratedDeriv_ofReal (f : ℝ → ℝ) (y : ℝ) (k : ℕ) (hf : ContDiffAt ℝ k f y) :
    iteratedDeriv k (fun t => ((f t : ℝ) : ℂ)) y = ((iteratedDeriv k f y : ℝ) : ℂ) := by
  have : (fun t => ((f t : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [this, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    Complex.ofRealCLM.iteratedFDeriv_comp_left hf le_rfl]
  simp

lemma c03m_aux_iter_shift (Ψ : ℝ → ℝ) (k i : ℕ) :
    iteratedDeriv k (iteratedDeriv i (deriv Ψ)) = iteratedDeriv (k + i) (deriv Ψ) := by
  simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]

/-- The product of the factor sizes is `B |z|^K`. -/
lemma c03m_aux_size_eq (N r : ℕ) (hN : 1 ≤ N) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) {Y Λ A t z : ℝ} (hY : 0 < Y) :
    |z| ^ (2 * N - 1) * (A * Y⁻¹ ^ r * ∏ i, (if i.val = 0 then Λ * Y⁻¹ * (t * |z|)
        else Λ * Y⁻¹ ^ i.val) ^ q i) =
      c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q) := by
  have hYne : Y ≠ 0 := hY.ne'
  have hfac : ∀ i : Fin (2 * N - 1), (if i.val = 0 then Λ * Y⁻¹ * (t * |z|)
      else Λ * Y⁻¹ ^ i.val) ^ q i = Λ ^ q i * Y⁻¹ ^ ((i.val + 1) * q i) *
        (t * |z|) ^ (if i.val = 0 then q i else 0) * Y ^ (if 1 ≤ i.val then q i else 0) := by
    intro i
    split_ifs with h0 h1 h1
    · omega
    · simp [h0, mul_pow]
    · have : Y⁻¹ ^ ((i.val + 1) * q i) * Y ^ q i = Y⁻¹ ^ (i.val * q i) := by
        rw [add_mul, one_mul, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hYne, one_pow,
          mul_one]
      rw [mul_pow, ← pow_mul, pow_zero, mul_one, mul_assoc (Λ ^ q i), this, mul_comm i.val]
    · omega
  simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ i : Fin (2 * N - 1), q i = c03_mult_q1 q + c03_mult_ell q := by
    unfold c03_mult_q1 c03_mult_ell
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  have hsY : ∑ i : Fin (2 * N - 1), (i.val + 1) * q i = 2 * N - 1 - r := by omega
  have hell := c03m_aux_ell_le N r hN q hrq
  rw [hsum, hsY]
  unfold c03_mult_size
  change _ = A * Λ ^ (c03_mult_q1 q + c03_mult_ell q) * Y ^ (-(2 * N : ℝ) + 1 + c03_mult_ell q) *
    t ^ c03_mult_q1 q * |z| ^ (2 * N - 1 + c03_mult_q1 q)
  have hYr : Y ^ (-(2 * N : ℝ) + 1 + c03_mult_ell q) = Y⁻¹ ^ (2 * N - 1) * Y ^ c03_mult_ell q := by
    rw [show (-(2 * N : ℝ) + 1 + c03_mult_ell q) = -((2 * N - 1 : ℕ) : ℝ) + (c03_mult_ell q : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_add hY, Real.rpow_neg hY.le,
      Real.rpow_natCast, Real.rpow_natCast, inv_pow]
  rw [hYr]
  have h1 : Y⁻¹ ^ (2 * N - 1) = Y⁻¹ ^ r * Y⁻¹ ^ (2 * N - 1 - r) := by
    rw [← pow_add]; congr 1; omega
  have h2 : (∑ i : Fin (2 * N - 1), (if i.val = 0 then q i else 0)) = c03_mult_q1 q := rfl
  have h3 : (∑ i : Fin (2 * N - 1), (if 1 ≤ i.val then q i else 0)) = c03_mult_ell q := rfl
  rw [h2, h3, h1, mul_pow, pow_add]
  ring


/-! ## Amplitude and phase symbols, kernel identity, interpolation integral -/

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c03_mult_amplitude_symbol.  For a fixed Taylor index `(r,q)`, the amplitude
`b_t` is smooth, compactly supported in `{z : y + t z ∈ (Y/4,4Y)}`, jointly smooth in `(y,z)`, and
`|∂_y^j ∂_z^s b_t(z)| ≤ C B Y^{-j} |z|^{K-s}` (`K = 2N-1+q₁`, `z ≠ 0`), uniformly in
`Y, Λ, A, y, t`, under `𝖧` through order `2N+j+s+2`.
Encoding: stated directly on the neighbourhood `Y/2 < y < 3Y` (the blueprint's
"enlarged constants" extension), which contains `[Y,2Y]`. -/
theorem c03_mult_amplitude_symbol (c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ) (hN : 1 ≤ N) (r : ℕ)
    (q : Fin (2 * N - 1) → ℕ) (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    ∀ j s : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + s + 2) a Ψ → ∀ t ∈ Ioc (0 : ℝ) 1,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_bt Y a Ψ N r q w.1 t w.2)
        (Ioo (Y / 2) (3 * Y) ×ˢ univ) ∧
      ∀ y ∈ Ioo (Y / 2) (3 * Y),
        ContDiff ℝ (⊤ : ℕ∞) (c03_mult_bt Y a Ψ N r q y t) ∧
        HasCompactSupport (c03_mult_bt Y a Ψ N r q y t) ∧
        tsupport (c03_mult_bt Y a Ψ N r q y t) ⊆ {z | y + t * z ∈ Ioo (Y / 4) (4 * Y)} ∧
        ∀ z : ℝ, z ≠ 0 →
          ‖iteratedDeriv j (fun y' => iteratedDeriv s (c03_mult_bt Y a Ψ N r q y' t) z) y‖ ≤
            C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) := by
  intro j s Ck
  set CS : ℝ := ∑ k ∈ Finset.range (2 * N + j + s + 3), |Ck k| + 1 with hCS
  have hCS1 : 1 ≤ CS := by
    have : 0 ≤ ∑ k ∈ Finset.range (2 * N + j + s + 3), |Ck k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hCk : ∀ k < 2 * N + j + s + 3, Ck k ≤ CS := by
    intro k hk
    have := Finset.single_le_sum (f := fun k => |Ck k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hk)
    linarith [le_abs_self (Ck k)]
  set cs : ℝ := 4 ^ s * CS with hcs
  have hcs1 : 1 ≤ cs := by
    have : (1 : ℝ) ≤ 4 ^ s := one_le_pow₀ (by norm_num)
    nlinarith
  set JS := j + s
  -- the product constant
  set Cq : ℝ := 2 ^ (JS * (2 * N - 1)) * ∏ i : Fin (2 * N - 1), (2 ^ (JS * q i) * cs ^ q i)
  set Ctot : ℝ := 2 ^ JS * (2 ^ (JS * (2 * N - 1)) * cs ^ (2 * N - 1)) * (2 ^ JS * cs * Cq)
  have hCq : 0 ≤ Cq := mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => by positivity)
  refine ⟨Ctot + 1, by positivity, ?_⟩
  intro Y Λ A a Ψ hY hΛ hA hyp t ht
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨ha, has, hΨ, hb⟩ := hyp
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hV : IsOpen V := isOpen_Ioo
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have ht0 : 0 < t := ht.1
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 + t * w.2 with hℓ_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ := by fun_prop
  set A' := iteratedDeriv r a
  have hA' : ContDiff ℝ (⊤ : ℕ∞) A' := by
    rw [show A' = deriv^[r] a from iteratedDeriv_eq_iterate]; exact ha.iterate_deriv r
  have hA's : tsupport A' ⊆ U := (c03m_aux_tsupport_iteratedDeriv a r).trans has
  set P : ℝ × ℝ → ℂ := fun w => c03m_aux_Pi Ψ q w.1 (w.1 + t * w.2)
  have hP := c03m_aux_Pi_smooth hΨ q t hVU
  set Hl : ℝ × ℝ → ℂ := fun w => if ℓ w ∈ U then A' (ℓ w) * P w else 0
  have hHl : ContDiffOn ℝ (⊤ : ℕ∞) Hl (V ×ˢ univ) :=
    c03m_aux_localized_smooth hU hA' hA's hℓ (hV.prod isOpen_univ) hP
  have hbteq : ∀ y z, c03_mult_bt Y a Ψ N r q y t z = ((z : ℂ) ^ (2 * N - 1)) * Hl (y, z) := by
    intro y z; rw [c03m_aux_bt_eq a hΨ N r q y t z]
  have hjoint : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_bt Y a Ψ N r q w.1 t w.2)
      (V ×ˢ univ) := by
    simp_rw [hbteq]
    exact (Complex.ofRealCLM.contDiff.comp contDiff_snd).pow _ |>.contDiffOn.mul hHl
  refine ⟨hjoint, fun y hy => ⟨?_, ?_, ?_, fun z hz => ?_⟩⟩
  · have := hjoint.comp (s := (univ : Set ℝ)) (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun z _ => (⟨hy, trivial⟩ : ((y, z) : ℝ × ℝ) ∈ V ×ˢ univ))
    exact contDiffOn_univ.1 this
  · -- compact support
    refine HasCompactSupport.intro ((c03m_aux_tsupport_compact has).image
      (by fun_prop : Continuous fun x : ℝ => (x - y) / t)) fun z hz => ?_
    have hz' : y + t * z ∉ tsupport A' := fun h => hz ⟨y + t * z, (c03m_aux_tsupport_iteratedDeriv a r) h,
      by field_simp; ring⟩
    rw [hbteq]; simp [Hl, ℓ, image_eq_zero_of_notMem_tsupport hz']
  · refine (closure_minimal (fun z hz => ?_) ((isClosed_tsupport A').preimage
      (by fun_prop : Continuous fun z : ℝ => y + t * z))).trans (fun z hz => hA's hz)
    by_contra hc
    apply hz
    rw [hbteq]; simp [Hl, ℓ, image_eq_zero_of_notMem_tsupport hc]
  -- the symbol bound
  have hz' : 0 < |z| := abs_pos.2 hz
  have hX0 : 0 ≤ c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
      |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) :=
    mul_nonneg (mul_nonneg (c03m_aux_size_nonneg N q hY0 hΛ0.le hA.le ht0.le)
      (Real.rpow_nonneg hY0.le _)) (Real.rpow_nonneg hz'.le _)
  change ‖c03m_aux_M (fun w => c03_mult_bt Y a Ψ N r q w.1 t w.2) j s y z‖ ≤ _
  by_cases hin : y + t * z ∈ U
  swap
  · -- the amplitude vanishes near `(y,z)`
    have h0 : A' =ᶠ[𝓝 (y + t * z)] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hin (hA's h))
    have h0' : ∀ᶠ w in 𝓝 ((y, z) : ℝ × ℝ), A' (ℓ w) = 0 := (hℓ.continuous.tendsto (y, z)).eventually h0
    have hev : (fun w : ℝ × ℝ => c03_mult_bt Y a Ψ N r q w.1 t w.2) =ᶠ[𝓝 (y, z)] fun _ => 0 := by
      filter_upwards [h0'] with w hw
      rw [hbteq]; simp [Hl, hw]
    have hpos : 0 ≤ (Ctot + 1) * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
        |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) := by
      have := mul_nonneg (show (0 : ℝ) ≤ Ctot + 1 by positivity) hX0
      simpa only [mul_assoc] using this
    have hM0 : c03m_aux_M (fun _ => (0 : ℂ)) j s y z = 0 := by
      simp [c03m_aux_M, iteratedDeriv_const]
    rw [c03m_aux_M_congr hev, hM0, norm_zero]; exact hpos
  -- inside the phase domain
  set W : Set (ℝ × ℝ) := (V ×ˢ univ) ∩ ℓ ⁻¹' U
  have hW : IsOpen W := (hV.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
  have hq : ((y, z) : ℝ × ℝ) ∈ W := ⟨⟨hy, trivial⟩, hin⟩
  have hWU : ∀ w ∈ W, w.1 + t * w.2 ∈ U := fun w hw => hw.2
  have htz : t * |z| ≤ 4 * Y := by
    have h1 : |t * z| ≤ 4 * Y := by
      rw [abs_le]; constructor <;> linarith [hin.1, hin.2, hy.1, hy.2]
    rwa [abs_mul, abs_of_pos ht0] at h1
  -- factors
  set Φ : Fin (2 * N - 1) → ℝ × ℝ → ℂ := fun i w =>
    ((iteratedDeriv (i.val + 1) Ψ (w.1 + t * w.2) - if i.val = 0 then deriv Ψ w.1 else 0 : ℝ) : ℂ)
  set G : ℝ × ℝ → ℂ := fun w => (∏ _k ∈ Finset.range (2 * N - 1), ((w.2 : ℝ) : ℂ)) *
    (A' (ℓ w) * ∏ i, ∏ _m ∈ Finset.range (q i), Φ i w)
  have hGeq : ∀ w ∈ W, c03_mult_bt Y a Ψ N r q w.1 t w.2 = G w := by
    intro w hw
    rw [hbteq]
    have h2 : ℓ w ∈ U := hw.2
    simp only [Hl, G, h2, ↓reduceIte, Finset.prod_const, Finset.card_range]
    simp only [P, c03m_aux_Pi, Φ, ℓ]
  have hev : (fun w : ℝ × ℝ => c03_mult_bt Y a Ψ N r q w.1 t w.2) =ᶠ[𝓝 (y, z)] G := by
    filter_upwards [hW.mem_nhds hq] with w hw using hGeq w hw
  rw [c03m_aux_M_congr hev]
  -- smoothness of the factors on `W`
  have hdΨ : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) U := ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hΨ).2
  have hΦs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) W := by
    intro i
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn (ContDiffOn.sub ?_ ?_)
    · exact (c03m_aux_iteratedDeriv_contDiffOn hU hΨ (i.val + 1)).comp hℓ.contDiffOn
        (fun w hw => hw.2)
    · split_ifs
      · exact hdΨ.comp contDiff_fst.contDiffOn (fun w hw => hVU hw.1.1)
      · exact contDiffOn_const
  have hzs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ)) W :=
    (Complex.ofRealCLM.contDiff.comp contDiff_snd).contDiffOn
  have hAs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => A' (ℓ w)) W := (hA'.comp hℓ).contDiffOn
  -- factor bounds
  have hYi : 0 ≤ Y⁻¹ := by positivity
  have hzi : 0 ≤ |z|⁻¹ := by positivity
  have hrp : ∀ k : ℕ, Y ^ (-(k : ℝ)) = Y⁻¹ ^ k := fun k => by
    rw [Real.rpow_neg hY0.le, Real.rpow_natCast, inv_pow]
  have hbz : c03m_aux_SB (fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ)) y z j s cs |z| Y⁻¹ |z|⁻¹ :=
    c03m_aux_SB_mono (c03m_aux_SB_z y z hz j s hYi) hcs1 hz'.le hYi hzi
  have hbA : c03m_aux_SB (fun w => A' (ℓ w)) y z j s cs (A * Y⁻¹ ^ r) Y⁻¹ |z|⁻¹ := by
    refine c03m_aux_SB_comp isOpen_univ hA'.contDiffOn ht0.le hY0 hW (fun _ _ => trivial) hq hz htz
      j s (by linarith) (by positivity) fun k hk => ?_
    have e : iteratedDeriv k A' (y + t * z) = iteratedDeriv (r + k) a (y + t * z) := by
      simp only [A', iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, add_comm k r]
    rw [e]
    have h1 := ((hb (y + t * z) hin).2.2 (r + k) (by omega)).2
    rw [hrp, pow_add] at h1
    calc _ ≤ Ck (r + k) * A * (Y⁻¹ ^ r * Y⁻¹ ^ k) := h1
      _ ≤ CS * A * (Y⁻¹ ^ r * Y⁻¹ ^ k) := by gcongr; exact hCk _ (by omega)
      _ = _ := by ring
  have hdΨk : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k (deriv Ψ)) U := fun k =>
    c03m_aux_iteratedDeriv_contDiffOn hU hdΨ k
  -- bounds for `λ^{(k)}` on the phase interval
  have hlam : ∀ k ≤ 2 * N + j + s + 2, ∀ x ∈ U,
      |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k := by
    intro k hk x hx
    have h1 := ((hb x hx).2.2 k hk).1
    rw [hrp] at h1
    exact h1.trans (by gcongr; exact hCk k (by omega))
  -- `f = λ^{(i)}` composed with `ℓ`
  have hcompl : ∀ i ≤ 2 * N - 1, c03m_aux_SB (fun w => (((iteratedDeriv i (deriv Ψ)) (ℓ w) : ℝ) : ℂ))
      y z j s cs (Λ * Y⁻¹ ^ i) Y⁻¹ |z|⁻¹ := by
    intro i hi
    have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ((iteratedDeriv i (deriv Ψ) x : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hdΨk i)
    refine c03m_aux_SB_comp hU hf ht0.le hY0 hW hWU hq hz htz j s (by linarith) (by positivity)
      fun k hk => ?_
    rw [c03m_aux_iteratedDeriv_ofReal _ _ _ (((hdΨk i).contDiffAt (hU.mem_nhds hin)).of_le
      (by exact_mod_cast le_top)), Complex.norm_real, Real.norm_eq_abs, c03m_aux_iter_shift]
    calc _ ≤ CS * Λ * Y⁻¹ ^ (k + i) := hlam (k + i) (by omega) _ hin
      _ = _ := by rw [pow_add]; ring
  have hΦb : ∀ i : Fin (2 * N - 1), c03m_aux_SB (Φ i) y z j s cs
      (if i.val = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i.val) Y⁻¹ |z|⁻¹ := by
    intro i
    by_cases hi0 : i.val = 0
    · rw [if_pos hi0]
      have hΦ0 : Φ i = fun w => (((iteratedDeriv 0 (deriv Ψ)) (ℓ w) : ℝ) : ℂ) -
          (((iteratedDeriv 0 (deriv Ψ)) w.1 : ℝ) : ℂ) := by
        funext w; simp [Φ, hi0, ℓ, iteratedDeriv_one]
      rw [hΦ0]
      intro a ha b hb'
      have hF2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => (((iteratedDeriv 0 (deriv Ψ)) w.1 : ℝ) : ℂ)) W :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn ((hdΨk 0).comp contDiff_fst.contDiffOn
          (fun w hw => hVU hw.1.1))
      have hF1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => (((iteratedDeriv 0 (deriv Ψ)) (ℓ w) : ℝ) : ℂ)) W :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn ((hdΨk 0).comp hℓ.contDiffOn (fun w hw => hw.2))
      rw [c03m_aux_M_sub hW hF1 hF2 a b hq]
      have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ((iteratedDeriv 0 (deriv Ψ) x : ℝ) : ℂ)) U :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn (hdΨk 0)
      rw [show (fun w : ℝ × ℝ => (((iteratedDeriv 0 (deriv Ψ)) (ℓ w) : ℝ) : ℂ)) =
          fun w => (fun x => ((iteratedDeriv 0 (deriv Ψ) x : ℝ) : ℂ)) (w.1 + t * w.2) from rfl,
        c03m_aux_M_comp hU hf t hW hWU a b hq,
        c03m_aux_M_fst (fun x => ((iteratedDeriv 0 (deriv Ψ) x : ℝ) : ℂ)) a b y z]
      rw [c03m_aux_iteratedDeriv_ofReal _ _ _ (((hdΨk 0).contDiffAt (hU.mem_nhds hin)).of_le
        (by exact_mod_cast le_top)), c03m_aux_iter_shift, add_zero]
      have htY : t * Y⁻¹ = (Y⁻¹ * (t * |z|)) * |z|⁻¹ := by field_simp
      have htY4 : t * Y⁻¹ ≤ 4 * |z|⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ hY0]
        calc t = t * |z| * |z|⁻¹ := by field_simp
          _ ≤ 4 * Y * |z|⁻¹ := by gcongr
          _ = _ := by ring
      split_ifs with hb0
      · -- `b = 0`: mean value theorem
        subst hb0
        rw [c03m_aux_iteratedDeriv_ofReal _ _ _ (((hdΨk 0).contDiffAt (hU.mem_nhds (hVU hy))).of_le
          (by exact_mod_cast le_top)), c03m_aux_iter_shift, add_zero, pow_zero, one_mul,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, pow_zero, mul_one]
        have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := iteratedDeriv a (deriv Ψ))
          (C := CS * Λ * Y⁻¹ ^ (a + 1)) (s := U)
          (fun x hx => ((hdΨk a).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
          (fun x hx => by
            rw [← iteratedDeriv_succ, Real.norm_eq_abs]
            exact hlam (a + 1) (by omega) x hx) (convex_Ioo _ _) (hVU hy) hin
        rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left, abs_mul, abs_of_pos ht0] at hmvt
        calc _ ≤ CS * Λ * Y⁻¹ ^ (a + 1) * (t * |z|) := hmvt
          _ ≤ cs * Λ * Y⁻¹ ^ (a + 1) * (t * |z|) := by
              gcongr; rw [hcs]; nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := s)]
          _ = _ := by rw [pow_add]; ring
      · -- `b ≥ 1`
        rw [sub_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
          Complex.norm_real, Real.norm_eq_abs]
        have h1 := hlam (a + b) (by omega) _ hin
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        have h4 : (t * Y⁻¹) ^ b' ≤ 4 ^ s * |z|⁻¹ ^ b' := by
          calc (t * Y⁻¹) ^ b' ≤ (4 * |z|⁻¹) ^ b' := pow_le_pow_left₀ (by positivity) htY4 b'
            _ = 4 ^ b' * |z|⁻¹ ^ b' := mul_pow _ _ _
            _ ≤ 4 ^ s * |z|⁻¹ ^ b' := by gcongr; norm_num; omega
        calc t ^ (b' + 1) * |iteratedDeriv (a + (b' + 1)) (deriv Ψ) (y + t * z)|
            ≤ t ^ (b' + 1) * (CS * Λ * Y⁻¹ ^ (a + (b' + 1))) := by gcongr
          _ = CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) * (t * Y⁻¹) ^ b' := by ring
          _ = CS * Λ * Y⁻¹ ^ a * ((Y⁻¹ * (t * |z|)) * |z|⁻¹) * (t * Y⁻¹) ^ b' := by rw [← htY]
          _ ≤ CS * Λ * Y⁻¹ ^ a * ((Y⁻¹ * (t * |z|)) * |z|⁻¹) * (4 ^ s * |z|⁻¹ ^ b') := by gcongr
          _ = _ := by rw [hcs]; ring
    · rw [if_neg hi0]
      have hΦi : Φ i = fun w => (((iteratedDeriv (i.val) (deriv Ψ)) (ℓ w) : ℝ) : ℂ) := by
        funext w; simp only [Φ, hi0, ↓reduceIte, sub_zero, ℓ]
        rw [iteratedDeriv_succ']
      rw [hΦi]; exact hcompl i.val (by omega)
  -- assemble
  have hMi : ∀ i : Fin (2 * N - 1), 0 ≤ (if i.val = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i.val) := by
    intro i; split_ifs <;> positivity
  have hZ := c03m_aux_SB_prod (Finset.range (2 * N - 1)) hW (F := fun _ w => ((w.2 : ℝ) : ℂ))
    (fun _ _ => hzs) hq (c := fun _ => cs) (M := fun _ => |z|) (fun _ _ => by positivity)
    (fun _ _ => hz'.le) hYi hzi (fun _ _ => hbz)
  have hPow : ∀ i : Fin (2 * N - 1), c03m_aux_SB (fun w => ∏ _m ∈ Finset.range (q i), Φ i w) y z j s
      (2 ^ ((j + s) * q i) * cs ^ q i)
      ((if i.val = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i.val) ^ q i) Y⁻¹ |z|⁻¹ := by
    intro i
    have := c03m_aux_SB_prod (Finset.range (q i)) hW (F := fun _ => Φ i) (fun _ _ => hΦs i) hq
      (c := fun _ => cs) (M := fun _ => (if i.val = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i.val))
      (fun _ _ => by positivity) (fun _ _ => hMi i) hYi hzi (fun _ _ => hΦb i)
    simpa [Finset.prod_const, Finset.card_range] using this
  have hPi := c03m_aux_SB_prod Finset.univ hW (F := fun i w => ∏ _m ∈ Finset.range (q i), Φ i w)
    (fun i _ => contDiffOn_prod fun _ _ => hΦs i) hq (fun i _ => by positivity)
    (fun i _ => pow_nonneg (hMi i) _) hYi hzi (fun i _ => hPow i)
  have hAPi := c03m_aux_SB_mul hW hAs (contDiffOn_prod fun i _ => contDiffOn_prod fun _ _ => hΦs i)
    hq (by positivity) (by positivity)
    (by positivity) (Finset.prod_nonneg fun i _ => pow_nonneg (hMi i) _) hYi hzi hbA hPi
  have hG := c03m_aux_SB_mul hW (contDiffOn_prod fun _ _ => hzs)
    (hAs.mul (contDiffOn_prod fun i _ => contDiffOn_prod fun _ _ => hΦs i)) hq
    (by simpa using (show (0 : ℝ) ≤ 2 ^ ((j + s) * (2 * N - 1)) * cs ^ (2 * N - 1) by positivity))
    (by positivity) (by simp) (by positivity) hYi hzi hZ hAPi
  have hb' := hG j le_rfl s le_rfl
  have hb2 : ‖c03m_aux_M G j s y z‖ ≤ (2 ^ (j + s) * (2 ^ ((j + s) * (2 * N - 1)) * cs ^ (2 * N - 1)) *
      (2 ^ (j + s) * cs * (2 ^ ((j + s) * (2 * N - 1)) *
        ∏ i : Fin (2 * N - 1), (2 ^ ((j + s) * q i) * cs ^ q i)))) *
      (|z| ^ (2 * N - 1) * (A * Y⁻¹ ^ r * ∏ i : Fin (2 * N - 1),
        (if i.val = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i.val) ^ q i)) * Y⁻¹ ^ j *
      |z|⁻¹ ^ s := by
    simpa only [G, Finset.prod_const, Finset.card_range, Finset.card_univ, Fintype.card_fin]
      using hb'
  rw [c03m_aux_size_eq N r hN q hrq hY0] at hb2
  refine hb2.trans ?_
  rw [hrp, Real.rpow_sub hz', Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
  have hsz := c03m_aux_size_nonneg N q hY0 hΛ0.le hA.le ht0.le
  have hC : 2 ^ (j + s) * (2 ^ ((j + s) * (2 * N - 1)) * cs ^ (2 * N - 1)) *
      (2 ^ (j + s) * cs * (2 ^ ((j + s) * (2 * N - 1)) *
        ∏ i : Fin (2 * N - 1), (2 ^ ((j + s) * q i) * cs ^ q i))) ≤ Ctot + 1 := by
    simp only [Ctot, Cq, JS]; linarith
  have hX : 0 ≤ c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q) * Y⁻¹ ^ j *
      |z|⁻¹ ^ s := by positivity
  calc _ = (2 ^ (j + s) * (2 ^ ((j + s) * (2 * N - 1)) * cs ^ (2 * N - 1)) *
      (2 ^ (j + s) * cs * (2 ^ ((j + s) * (2 * N - 1)) *
        ∏ i : Fin (2 * N - 1), (2 ^ ((j + s) * q i) * cs ^ q i)))) *
      (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q) * Y⁻¹ ^ j * |z|⁻¹ ^ s) := by
        ring
    _ ≤ (Ctot + 1) * (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q) * Y⁻¹ ^ j *
      |z|⁻¹ ^ s) := mul_le_mul_of_nonneg_right hC hX
    _ = _ := by ring


/-! ### Phase-symbol helpers -/

lemma c03m_aux_deriv_ofReal (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun t => ((f t : ℝ) : ℂ)) x = ((deriv f x : ℝ) : ℂ) := by
  by_cases hf : DifferentiableAt ℝ f x
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have h : ¬ DifferentiableAt ℝ (fun t => ((f t : ℝ) : ℂ)) x := by
      intro h
      apply hf
      have := (Complex.reCLM.differentiableAt (x := ((f x : ℝ) : ℂ))).comp x h
      simpa [Function.comp_def] using this
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt hf]
    simp

lemma c03m_aux_iteratedDeriv_ofReal' (f : ℝ → ℝ) (k : ℕ) :
    iteratedDeriv k (fun t => ((f t : ℝ) : ℂ)) = fun x => ((iteratedDeriv k f x : ℝ) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x; exact c03m_aux_deriv_ofReal _ x

/-- Real-to-complex transfer for mixed derivatives. -/
lemma c03m_aux_M_ofReal (F : ℝ × ℝ → ℝ) (a b : ℕ) (y z : ℝ) :
    c03m_aux_M (fun w => ((F w : ℝ) : ℂ)) a b y z =
      ((iteratedDeriv a (fun y' => iteratedDeriv b (fun z' => F (y', z')) z) y : ℝ) : ℂ) := by
  unfold c03m_aux_M
  have h1 : (fun y' => iteratedDeriv b (fun z' => ((F (y', z') : ℝ) : ℂ)) z) =
      fun y' => ((iteratedDeriv b (fun z' => F (y', z')) z : ℝ) : ℂ) := by
    funext y'
    rw [c03m_aux_iteratedDeriv_ofReal' (fun z' => F (y', z'))]
  rw [h1, c03m_aux_iteratedDeriv_ofReal']

lemma c03m_aux_M_const_mul (c : ℂ) (F : ℝ × ℝ → ℂ) (a b : ℕ) (y z : ℝ) :
    c03m_aux_M (fun w => c * F w) a b y z = c * c03m_aux_M F a b y z := by
  unfold c03m_aux_M
  simp only [iteratedDeriv_const_mul_field]

lemma c03m_aux_M_add {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) (a b : ℕ) {y z : ℝ}
    (hq : (y, z) ∈ W) :
    c03m_aux_M (fun w => F w + G w) a b y z = c03m_aux_M F a b y z + c03m_aux_M G a b y z := by
  have h : (fun w => F w + G w) = fun w => F w - (-1 : ℂ) * G w := by funext w; ring
  rw [h, c03m_aux_M_sub hW hF (contDiffOn_const.mul hG) a b hq, c03m_aux_M_const_mul]
  ring

lemma c03m_aux_M_zero (F : ℝ × ℝ → ℂ) (y z : ℝ) : c03m_aux_M F 0 0 y z = F (y, z) := by
  simp [c03m_aux_M]

/-- Two-variable reciprocal symbol bound. -/
lemma c03m_aux_SB_inv {W : Set (ℝ × ℝ)} (hW : IsOpen W) {G : ℝ × ℝ → ℂ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) (hG0 : ∀ w ∈ W, G w ≠ 0) {y z : ℝ} (hq : (y, z) ∈ W)
    {J S : ℕ} {c M m α β : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (hm : 0 < m) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hGm : m ≤ ‖G (y, z)‖) (h : c03m_aux_SB G y z J S c M α β) :
    c03m_aux_SB (fun w => (G w)⁻¹) y z J S ((2 ^ (J + S) * c * M * m⁻¹ + 1) ^ (J + S)) m⁻¹
      α β := by
  set K := 2 ^ (J + S) * c * M * m⁻¹ + 1 with hK
  have hK0 : 0 ≤ 2 ^ (J + S) * c * M * m⁻¹ := by positivity
  have hK1 : 1 ≤ K := by linarith
  have hGi : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => (G w)⁻¹) W := hG.inv hG0
  have hzero : ∀ j s, j + s ≠ 0 → c03m_aux_M (fun w => G w * (G w)⁻¹) j s y z = 0 := by
    intro j s hjs
    have hev : (fun w => G w * (G w)⁻¹) =ᶠ[𝓝 (y, z)] fun w => ((fun _ : ℝ => (1 : ℂ)) w.1) := by
      filter_upwards [hW.mem_nhds hq] with w hw
      simp [mul_inv_cancel₀ (hG0 w hw)]
    have h1 := c03m_aux_M_fst (fun _ : ℝ => (1 : ℂ)) j s y z
    rw [c03m_aux_M_congr hev, h1]
    split_ifs with hs
    · rw [iteratedDeriv_const]
      split_ifs with hj
      · omega
      · rfl
    · rfl
  have key : ∀ n, ∀ j s, j + s = n → j ≤ J → s ≤ S →
      ‖c03m_aux_M (fun w => (G w)⁻¹) j s y z‖ ≤ m⁻¹ * K ^ (j + s) * α ^ j * β ^ s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro j s hn hj hs
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · obtain rfl : j = 0 := by omega
      obtain rfl : s = 0 := by omega
      rw [c03m_aux_M_zero, norm_inv]
      simpa using inv_anti₀ hm hGm
    · have hL := c03m_aux_M_mul hW hG hGi j s hq
      rw [hzero j s (by omega)] at hL
      set T : ℕ → ℕ → ℂ := fun a b => (j.choose a : ℂ) * (s.choose b : ℂ) *
        (c03m_aux_M G a b y z * c03m_aux_M (fun w => (G w)⁻¹) (j - a) (s - b) y z) with hT
      have hsplit : ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1), T a b =
          (∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
            (if a = 0 ∧ b = 0 then T a b else 0)) +
          ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
            (if a = 0 ∧ b = 0 then 0 else T a b) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      have h00 : ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
          (if a = 0 ∧ b = 0 then T a b else 0) = T 0 0 := by
        rw [Finset.sum_eq_single 0]
        · rw [Finset.sum_eq_single 0]
          · simp
          · intro b _ hb; simp [hb]
          · intro h; simp at h
        · intro a _ ha
          refine Finset.sum_eq_zero fun b _ => ?_
          simp [ha]
        · intro h; simp at h
      have hT00 : T 0 0 = G (y, z) * c03m_aux_M (fun w => (G w)⁻¹) j s y z := by
        simp [hT, c03m_aux_M_zero]
      set X : ℝ := c * M * m⁻¹ * K ^ (n - 1) * α ^ j * β ^ s with hX
      have hX0 : 0 ≤ X := by positivity
      have hterm : ∀ a ∈ Finset.range (j + 1), ∀ b ∈ Finset.range (s + 1),
          ‖(if a = 0 ∧ b = 0 then 0 else T a b)‖ ≤ ((j.choose a : ℝ) * (s.choose b : ℝ)) * X := by
        intro a ha b hb
        have ha' : a ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
        have hb' : b ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
        split_ifs with hab
        · rw [norm_zero]; positivity
        · have hab' : 1 ≤ a + b := by
            by_contra hc'; exact hab ⟨by omega, by omega⟩
          have e1 := h a (ha'.trans hj) b (hb'.trans hs)
          have e2 := ih ((j - a) + (s - b)) (by omega) (j - a) (s - b) rfl
            ((Nat.sub_le _ _).trans hj) ((Nat.sub_le _ _).trans hs)
          have hKp : K ^ ((j - a) + (s - b)) ≤ K ^ (n - 1) :=
            pow_le_pow_right₀ hK1 (by omega)
          have hpa : α ^ a * α ^ (j - a) = α ^ j := by rw [← pow_add, Nat.add_sub_cancel' ha']
          have hpb : β ^ b * β ^ (s - b) = β ^ s := by rw [← pow_add, Nat.add_sub_cancel' hb']
          rw [hT]
          simp only
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
          calc (j.choose a : ℝ) * (s.choose b : ℝ) * (‖c03m_aux_M G a b y z‖ *
                ‖c03m_aux_M (fun w => (G w)⁻¹) (j - a) (s - b) y z‖)
              ≤ (j.choose a : ℝ) * (s.choose b : ℝ) * ((c * M * α ^ a * β ^ b) *
                (m⁻¹ * K ^ ((j - a) + (s - b)) * α ^ (j - a) * β ^ (s - b))) := by gcongr
            _ ≤ (j.choose a : ℝ) * (s.choose b : ℝ) * ((c * M * α ^ a * β ^ b) *
                (m⁻¹ * K ^ (n - 1) * α ^ (j - a) * β ^ (s - b))) := by gcongr
            _ = _ := by rw [hX, ← hpa, ← hpb]; ring
      have hsum : ‖∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
          (if a = 0 ∧ b = 0 then 0 else T a b)‖ ≤ 2 ^ (J + S) * X := by
        calc _ ≤ ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
              ((j.choose a : ℝ) * (s.choose b : ℝ)) * X := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
              exact hterm a ha b hb
          _ = (∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)) *
              (∑ b ∈ Finset.range (s + 1), (s.choose b : ℝ)) * X := by
              rw [Finset.sum_mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_mul]
          _ = 2 ^ j * 2 ^ s * X := by
              rw [← Nat.cast_sum, ← Nat.cast_sum, Nat.sum_range_choose, Nat.sum_range_choose]
              push_cast; ring
          _ ≤ 2 ^ (J + S) * X := by
              gcongr
              rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hid : G (y, z) * c03m_aux_M (fun w => (G w)⁻¹) j s y z =
          -∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
            (if a = 0 ∧ b = 0 then 0 else T a b) := by
        rw [← hT00, ← h00]
        have := hL.symm
        rw [show (∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1),
          (j.choose a : ℂ) * (s.choose b : ℂ) * (c03m_aux_M G a b y z *
            c03m_aux_M (fun w => (G w)⁻¹) (j - a) (s - b) y z)) =
            ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (s + 1), T a b from rfl,
          hsplit] at this
        linear_combination this
      have hnorm : m * ‖c03m_aux_M (fun w => (G w)⁻¹) j s y z‖ ≤ 2 ^ (J + S) * X := by
        calc m * ‖c03m_aux_M (fun w => (G w)⁻¹) j s y z‖
            ≤ ‖G (y, z)‖ * ‖c03m_aux_M (fun w => (G w)⁻¹) j s y z‖ := by gcongr
          _ = _ := by rw [← norm_mul, hid, norm_neg]
          _ ≤ _ := hsum
      have hKn : K ^ n = K * K ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hn]
      rw [← le_div_iff₀' hm] at hnorm
      refine hnorm.trans ?_
      rw [div_eq_inv_mul, hKn, hX]
      have h2 : 2 ^ (J + S) * c * M * m⁻¹ ≤ K := by linarith
      calc m⁻¹ * (2 ^ (J + S) * (c * M * m⁻¹ * K ^ (n - 1) * α ^ j * β ^ s))
          = m⁻¹ * (2 ^ (J + S) * c * M * m⁻¹) * K ^ (n - 1) * α ^ j * β ^ s := by ring
        _ ≤ m⁻¹ * K * K ^ (n - 1) * α ^ j * β ^ s := by gcongr
        _ = _ := by ring
  intro a ha b hb
  refine (key (a + b) a b rfl ha hb).trans ?_
  have : K ^ (a + b) ≤ K ^ (J + S) := pow_le_pow_right₀ hK1 (by omega)
  calc m⁻¹ * K ^ (a + b) * α ^ a * β ^ b ≤ m⁻¹ * K ^ (J + S) * α ^ a * β ^ b := by gcongr
    _ = _ := by ring

lemma c03m_aux_phit_hasDerivAt {U : Set ℝ} (hU : IsOpen U) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ U) (y t z : ℝ) (hz : y + t * z ∈ U) :
    HasDerivAt (c03_mult_phit Ψ y t) ((1 - t) * deriv Ψ y + t * deriv Ψ (y + t * z)) z := by
  have hd : DifferentiableAt ℝ Ψ (y + t * z) :=
    (hΨ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  have h1 : HasDerivAt (fun z => y + t * z) t z := by
    simpa using ((hasDerivAt_id z).const_mul t).const_add y
  have h2 : HasDerivAt (fun z => Ψ (y + t * z)) (deriv Ψ (y + t * z) * t) z :=
    hd.hasDerivAt.comp z h1
  have h3 := ((hasDerivAt_id z).const_mul (deriv Ψ y)).add
    ((h2.sub_const (Ψ y)).sub (((hasDerivAt_id z).const_mul t).const_mul (deriv Ψ y)))
  convert h3 using 1
  · funext z'; simp only [c03_mult_phit, c03_mult_Theta, Pi.add_apply, Pi.sub_apply, id]
  · simp; ring

lemma c03m_aux_convex_bounds {lo hi u v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : lo ≤ u ∧ u ≤ hi)
    (hv : lo ≤ v ∧ v ≤ hi) : lo ≤ (1 - t) * u + t * v ∧ (1 - t) * u + t * v ≤ hi := by
  constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2]

/-- `|t z| < 4Y` when `y ∈ (Y/2,3Y)` and `y + tz ∈ (Y/4,4Y)`. -/
lemma c03m_aux_tz_le {Y y t z : ℝ} (ht : 0 < t) (hy : y ∈ Ioo (Y / 2) (3 * Y))
    (hyz : y + t * z ∈ Ioo (Y / 4) (4 * Y)) : t * |z| ≤ 4 * Y := by
  have hY : 0 < Y := by have := hy.1; have := hy.2; linarith
  have e : t * |z| = |t * z| := by rw [abs_mul, abs_of_pos ht]
  rw [e, abs_le]; constructor <;> nlinarith [hy.1, hy.2, hyz.1, hyz.2]

/-- Mixed-derivative bounds for `(1-t) λ(y) + t λ(y+tz)`. -/
lemma c03m_aux_lamt_M {Y Λ CS : ℝ} (hY : 0 < Y) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) {K : ℕ}
    (hbd : ∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ K, |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k)
    (hCS : 0 ≤ CS) (hΛ : 0 ≤ Λ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {y z : ℝ}
    (hy : y ∈ Ioo (Y / 4) (4 * Y)) (hyz : y + t * z ∈ Ioo (Y / 4) (4 * Y)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((1 - t : ℝ) : ℂ) * ((deriv Ψ w.1 : ℝ) : ℂ) +
        ((t : ℝ) : ℂ) * ((deriv Ψ (w.1 + t * w.2) : ℝ) : ℂ))
      ((Ioo (Y / 4) (4 * Y) ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) ∧
    ∀ a b, a + b ≤ K →
      ‖c03m_aux_M (fun w : ℝ × ℝ => ((1 - t : ℝ) : ℂ) * ((deriv Ψ w.1 : ℝ) : ℂ) +
        ((t : ℝ) : ℂ) * ((deriv Ψ (w.1 + t * w.2) : ℝ) : ℂ)) a b y z‖ ≤
        CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set W := (U ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U with hW_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => w.1 + t * w.2) := by fun_prop
  have hW : IsOpen W := (hU.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
  have hq : (y, z) ∈ W := ⟨⟨hy, trivial⟩, hyz⟩
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) U :=
    ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hΨ).2
  set f : ℝ → ℂ := fun x => ((deriv Ψ x : ℝ) : ℂ) with hf_def
  have hfU : ContDiffOn ℝ (⊤ : ℕ∞) f U := Complex.ofRealCLM.contDiff.comp_contDiffOn hd
  have hF1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => f w.1) W :=
    hfU.comp contDiff_fst.contDiffOn (fun w hw => hw.1.1)
  have hF2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => f (w.1 + t * w.2)) W :=
    hfU.comp hℓ.contDiffOn (fun w hw => hw.2)
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((1 - t : ℝ) : ℂ) * f w.1 +
      ((t : ℝ) : ℂ) * f (w.1 + t * w.2)) W :=
    (contDiffOn_const.mul hF1).add (contDiffOn_const.mul hF2)
  refine ⟨hsm, ?_⟩
  intro a b hab
  have e := c03m_aux_M_add hW ((contDiffOn_const (c := ((1 - t : ℝ) : ℂ))).mul hF1)
    ((contDiffOn_const (c := ((t : ℝ) : ℂ))).mul hF2) a b hq
  simp only [hf_def] at e
  rw [e, c03m_aux_M_const_mul, c03m_aux_M_const_mul]
  have e1 := c03m_aux_M_fst f a b y z
  have e2 := c03m_aux_M_comp hU hfU t hW (fun w hw => hw.2) a b hq
  simp only [hf_def] at e1 e2
  rw [e1, e2]
  have hit : ∀ k x, iteratedDeriv k f x = ((iteratedDeriv k (deriv Ψ) x : ℝ) : ℂ) := by
    intro k x; rw [hf_def, c03m_aux_iteratedDeriv_ofReal']
  have hX : 0 ≤ CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b := by positivity
  have hb1 : ‖(if b = 0 then iteratedDeriv a (fun x => ((deriv Ψ x : ℝ) : ℂ)) y else 0)‖ ≤
      CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b := by
    split_ifs with hb
    · subst hb
      have := hit a y
      simp only [hf_def] at this
      rw [this, Complex.norm_real, Real.norm_eq_abs, pow_zero, mul_one]
      exact hbd y hy a (by omega)
    · rw [norm_zero]; exact hX
  have hb2 : ‖((t : ℝ) : ℂ) ^ b * iteratedDeriv (a + b) (fun x => ((deriv Ψ x : ℝ) : ℂ))
      (y + t * z)‖ ≤ CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b := by
    have := hit (a + b) (y + t * z)
    simp only [hf_def] at this
    rw [this, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t ^ b * |iteratedDeriv (a + b) (deriv Ψ) (y + t * z)| ≤
        t ^ b * (CS * Λ * Y⁻¹ ^ (a + b)) := by gcongr; exact hbd _ hyz _ hab
      _ = _ := by rw [pow_add, mul_pow]; ring
  calc _ ≤ ‖((1 - t : ℝ) : ℂ) * (if b = 0 then iteratedDeriv a
        (fun x => ((deriv Ψ x : ℝ) : ℂ)) y else 0)‖ + ‖((t : ℝ) : ℂ) * (((t : ℝ) : ℂ) ^ b *
        iteratedDeriv (a + b) (fun x => ((deriv Ψ x : ℝ) : ℂ)) (y + t * z))‖ := norm_add_le _ _
    _ ≤ (1 - t) * (CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b) + t * (CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b) := by
        rw [norm_mul, norm_mul (((t : ℝ) : ℂ)), Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg ht0]
        gcongr
    _ = _ := by ring

/-- Mixed-derivative bounds for the phase `φ_t(y,z)` (`z ≠ 0`). -/
lemma c03m_aux_phit_M {Y Λ CS : ℝ} (hY : 0 < Y) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) {j s : ℕ}
    (hbd : ∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ j + s,
      |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k)
    (hCS : 0 ≤ CS) (hΛ : 0 ≤ Λ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {y z : ℝ}
    (hy : y ∈ Ioo (Y / 2) (3 * Y)) (hyz : y + t * z ∈ Ioo (Y / 4) (4 * Y)) (hz : z ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((c03_mult_phit Ψ w.1 t w.2 : ℝ) : ℂ))
      ((Ioo (Y / 4) (4 * Y) ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) ∧
    ‖c03m_aux_M (fun w : ℝ × ℝ => ((c03_mult_phit Ψ w.1 t w.2 : ℝ) : ℂ)) j s y z‖ ≤
      (2 ^ (j + s) * CS + 4 ^ s * CS) * Λ * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ s) := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  have hyU : y ∈ U := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  set W := (U ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U with hW_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => w.1 + t * w.2) := by fun_prop
  have hW : IsOpen W := (hU.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
  have hq : (y, z) ∈ W := ⟨⟨hyU, trivial⟩, hyz⟩
  have hz' : 0 < |z| := abs_pos.2 hz
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) U :=
    ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hΨ).2
  set f : ℝ → ℂ := fun x => ((deriv Ψ x : ℝ) : ℂ) with hf_def
  set g : ℝ → ℂ := fun x => ((Ψ x : ℝ) : ℂ) with hg_def
  have hfU : ContDiffOn ℝ (⊤ : ℕ∞) f U := Complex.ofRealCLM.contDiff.comp_contDiffOn hd
  have hgU : ContDiffOn ℝ (⊤ : ℕ∞) g U := Complex.ofRealCLM.contDiff.comp_contDiffOn hΨ
  have hF1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => f w.1) W :=
    hfU.comp contDiff_fst.contDiffOn (fun w hw => hw.1.1)
  have hF2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ)) W :=
    (Complex.ofRealCLM.contDiff.comp contDiff_snd).contDiffOn
  have hF3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => g (w.1 + t * w.2)) W :=
    hgU.comp hℓ.contDiffOn (fun w hw => hw.2)
  have hF4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => g w.1) W :=
    hgU.comp contDiff_fst.contDiffOn (fun w hw => hw.1.1)
  have hP : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => f w.1 * ((w.2 : ℝ) : ℂ)) W := hF1.mul hF2
  have hA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × ℝ => ((1 - t : ℝ) : ℂ) * (f w.1 * ((w.2 : ℝ) : ℂ))) W :=
    contDiffOn_const.mul hP
  have hB : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => g (w.1 + t * w.2) - g w.1) W := hF3.sub hF4
  have hfun : (fun w : ℝ × ℝ => ((c03_mult_phit Ψ w.1 t w.2 : ℝ) : ℂ)) =
      fun w => ((1 - t : ℝ) : ℂ) * (f w.1 * ((w.2 : ℝ) : ℂ)) + (g (w.1 + t * w.2) - g w.1) := by
    funext w; simp only [hf_def, hg_def, c03_mult_phit, c03_mult_Theta]; push_cast; ring
  rw [hfun]
  refine ⟨hA.add hB, ?_⟩
  rw [c03m_aux_M_add hW hA hB j s hq, c03m_aux_M_const_mul, c03m_aux_M_sub hW hF3 hF4 j s hq,
    c03m_aux_M_comp hU hgU t hW (fun w hw => hw.2) j s hq]
  have e4 := c03m_aux_M_fst g j s y z
  rw [e4]
  -- the product term
  have hSB1 : c03m_aux_SB (fun w : ℝ × ℝ => f w.1) y z j s CS Λ Y⁻¹ |z|⁻¹ := by
    intro a ha b hb
    have e := c03m_aux_M_fst f a b y z
    rw [e]
    split_ifs with hb0
    · subst hb0
      rw [hf_def, c03m_aux_iteratedDeriv_ofReal', Complex.norm_real, Real.norm_eq_abs, pow_zero,
        mul_one]
      exact hbd y hyU a (by omega)
    · rw [norm_zero]; positivity
  have hSB2 := c03m_aux_SB_z y z hz j s (α := Y⁻¹) (by positivity)
  have hSB := c03m_aux_SB_mul hW hF1 hF2 hq hCS zero_le_one hΛ (abs_nonneg z) (by positivity)
    (by positivity) hSB1 hSB2
  have hT1 := hSB j le_rfl s le_rfl
  have hit : ∀ k x, iteratedDeriv k g x = ((iteratedDeriv k Ψ x : ℝ) : ℂ) := by
    intro k x; rw [hg_def, c03m_aux_iteratedDeriv_ofReal']
  have htz := c03m_aux_tz_le ht0 hy hyz
  -- the difference term
  have hT2 : ‖((t : ℝ) : ℂ) ^ s * iteratedDeriv (j + s) g (y + t * z) -
      (if s = 0 then iteratedDeriv j g y else 0)‖ ≤ 4 ^ s * CS * Λ * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ s) := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      simp only [pow_zero, one_mul, add_zero, ↓reduceIte, mul_one]
      rw [hit, hit, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hdiff : ∀ x ∈ U, DifferentiableAt ℝ (iteratedDeriv j Ψ) x := fun x hx =>
        ((c03m_aux_iteratedDeriv_contDiffOn hU hΨ j).differentiableOn (by simp)).differentiableAt
          (hU.mem_nhds hx)
      have hder : ∀ x ∈ U, ‖deriv (iteratedDeriv j Ψ) x‖ ≤ CS * Λ * Y⁻¹ ^ j := by
        intro x hx
        rw [← iteratedDeriv_succ, iteratedDeriv_succ', Real.norm_eq_abs]
        exact hbd x hx j (by omega)
      have := (convex_Ioo (Y / 4) (4 * Y)).norm_image_sub_le_of_norm_deriv_le hdiff hder hyU hyz
      rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left, abs_mul, abs_of_pos ht0] at this
      refine this.trans ?_
      have h1 : t * |z| ≤ |z| := by nlinarith
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    · simp only [(show s ≠ 0 by omega), ↓reduceIte, sub_zero]
      rw [hit, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos ht0]
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      have e : iteratedDeriv (j + (s' + 1)) Ψ = iteratedDeriv (j + s') (deriv Ψ) := by
        rw [show j + (s' + 1) = (j + s') + 1 by omega, iteratedDeriv_succ']
      rw [e]
      have hb := hbd _ hyz (j + s') (by omega)
      have htY : t * Y⁻¹ ≤ 4 * |z|⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ hY]
        calc t = t * |z| * |z|⁻¹ := by field_simp
          _ ≤ 4 * Y * |z|⁻¹ := by gcongr
          _ = _ := by ring
      have hzz : |z| * |z|⁻¹ = 1 := mul_inv_cancel₀ hz'.ne'
      calc t ^ (s' + 1) * |iteratedDeriv (j + s') (deriv Ψ) (y + t * z)|
          ≤ t ^ (s' + 1) * (CS * Λ * Y⁻¹ ^ (j + s')) := by gcongr
        _ = t * (CS * Λ * Y⁻¹ ^ j) * (t * Y⁻¹) ^ s' := by rw [mul_pow, pow_add]; ring
        _ ≤ 1 * (CS * Λ * Y⁻¹ ^ j) * (4 * |z|⁻¹) ^ s' := by gcongr
        _ = 4 ^ s' * (CS * Λ * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ (s' + 1))) := by
            have hzs : |z| * |z|⁻¹ ^ (s' + 1) = |z|⁻¹ ^ s' := by
              rw [pow_succ, mul_comm (|z|⁻¹ ^ s') _, ← mul_assoc, hzz, one_mul]
            rw [hzs, mul_pow]; ring
        _ ≤ 4 ^ (s' + 1) * (CS * Λ * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ (s' + 1))) := by
            have h4 : (4 : ℝ) ^ s' ≤ 4 ^ (s' + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
            have : 0 ≤ CS * Λ * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ (s' + 1)) := by positivity
            exact mul_le_mul_of_nonneg_right h4 this
        _ = _ := by ring
  have h1t : ‖((1 - t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  calc _ ≤ ‖((1 - t : ℝ) : ℂ) * c03m_aux_M (fun w : ℝ × ℝ => f w.1 * ((w.2 : ℝ) : ℂ)) j s y z‖ +
        ‖((t : ℝ) : ℂ) ^ s * iteratedDeriv (j + s) g (y + t * z) -
          (if s = 0 then iteratedDeriv j g y else 0)‖ := norm_add_le _ _
    _ ≤ 1 * (2 ^ (j + s) * CS * 1 * (Λ * |z|) * Y⁻¹ ^ j * |z|⁻¹ ^ s) +
        4 ^ s * CS * Λ * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ s) := by
        rw [norm_mul]; gcongr
    _ = _ := by ring

/-- Blueprint: lem:c03_mult_phase_symbol.  For the convex interpolation
`Φ = (1-σ) φ_{0,t} + σ φ_{1,t}` of the phases of two data (the single-phase case is
`Ψ₀ = Ψ₁`): `∂_z φ_{ν,t}(z) = (1-t)λ_ν(y) + tλ_ν(y+tz)`, `c₀⁻¹Λ ≤ ∂_zΦ ≤ c₀Λ`,
`|∂_y^j ∂_z^s (1/∂_zΦ)| ≤ C Λ⁻¹ Y^{-j} (t/Y)^s`, and for `j ≥ 1`, `z ≠ 0`,
`|∂_y^j ∂_z^s Φ| ≤ C Λ Y^{-j} |z|^{1-s}`; on `y + tz ∈ (Y/4,4Y)`, under the phase bounds of `𝖧`
through order `j+s+2`.
Encoding: stated directly on the neighbourhood `Y/2 < y < 3Y` (contains `[Y,2Y]`);
the convex-combination clause of the blueprint is built in through `σ`. -/
theorem c03_mult_phase_symbol (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ j s : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ : ℝ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ →
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ₀ (Ioo (Y / 4) (4 * Y)) →
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ₁ (Ioo (Y / 4) (4 * Y)) →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), c₀⁻¹ * Λ ≤ deriv Ψ₀ x ∧ deriv Ψ₀ x ≤ c₀ * Λ ∧
        ∀ k ≤ j + s + 2, |iteratedDeriv k (deriv Ψ₀) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ))) →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), c₀⁻¹ * Λ ≤ deriv Ψ₁ x ∧ deriv Ψ₁ x ≤ c₀ * Λ ∧
        ∀ k ≤ j + s + 2, |iteratedDeriv k (deriv Ψ₁) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ))) →
      ∀ σ ∈ Icc (0 : ℝ) 1, ∀ y ∈ Ioo (Y / 2) (3 * Y), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ z : ℝ,
      y + t * z ∈ Ioo (Y / 4) (4 * Y) →
        deriv (c03_mult_phit Ψ₀ y t) z = (1 - t) * deriv Ψ₀ y + t * deriv Ψ₀ (y + t * z) ∧
        deriv (c03_mult_phit Ψ₁ y t) z = (1 - t) * deriv Ψ₁ y + t * deriv Ψ₁ (y + t * z) ∧
        deriv (fun z' => (1 - σ) * c03_mult_phit Ψ₀ y t z' + σ * c03_mult_phit Ψ₁ y t z') z =
          (1 - σ) * deriv (c03_mult_phit Ψ₀ y t) z + σ * deriv (c03_mult_phit Ψ₁ y t) z ∧
        c₀⁻¹ * Λ ≤
          deriv (fun z' => (1 - σ) * c03_mult_phit Ψ₀ y t z' + σ * c03_mult_phit Ψ₁ y t z') z ∧
        deriv (fun z' => (1 - σ) * c03_mult_phit Ψ₀ y t z' + σ * c03_mult_phit Ψ₁ y t z') z ≤
          c₀ * Λ ∧
        |iteratedDeriv j (fun y' => iteratedDeriv s (fun z' => 1 / deriv (fun z'' =>
            (1 - σ) * c03_mult_phit Ψ₀ y' t z'' + σ * c03_mult_phit Ψ₁ y' t z'') z') z) y| ≤
          C * Λ⁻¹ * Y ^ (-(j : ℝ)) * (t / Y) ^ s ∧
        (1 ≤ j → z ≠ 0 →
          |iteratedDeriv j (fun y' => iteratedDeriv s (fun z' =>
              (1 - σ) * c03_mult_phit Ψ₀ y' t z' + σ * c03_mult_phit Ψ₁ y' t z') z) y| ≤
            C * Λ * Y ^ (-(j : ℝ)) * |z| ^ (1 - (s : ℝ))) := by
  intro j s Ck
  set CS : ℝ := ∑ k ∈ Finset.range (j + s + 3), |Ck k| + 1 with hCS
  have hCS1 : 1 ≤ CS := by
    have : 0 ≤ ∑ k ∈ Finset.range (j + s + 3), |Ck k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hCk : ∀ k < j + s + 3, Ck k ≤ CS := by
    intro k hk
    have := Finset.single_le_sum (f := fun k => |Ck k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hk)
    linarith [le_abs_self (Ck k)]
  set Kc : ℝ := 2 ^ (j + s) * CS * c₀ + 1 with hKc
  refine ⟨c₀ * Kc ^ (j + s) + (2 ^ (j + s) * CS + 4 ^ s * CS), by positivity, ?_⟩
  intro Y Λ Ψ₀ Ψ₁ hY hΛ hΨ₀ hΨ₁ h₀ h₁ σ hσ y hy t ht z hyz
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  have hyU : y ∈ U := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hb : ∀ Ψ : ℝ → ℝ, (∀ x ∈ U, c₀⁻¹ * Λ ≤ deriv Ψ x ∧ deriv Ψ x ≤ c₀ * Λ ∧
      ∀ k ≤ j + s + 2, |iteratedDeriv k (deriv Ψ) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ))) →
      ∀ x ∈ U, ∀ k ≤ j + s, |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k := by
    intro Ψ h x hx k hk
    have := (h x hx).2.2 k (by omega)
    rw [Real.rpow_neg hY0.le, Real.rpow_natCast] at this
    refine this.trans ?_
    rw [inv_pow]
    gcongr
    exact hCk k (by omega)
  have hb₀ := hb Ψ₀ h₀
  have hb₁ := hb Ψ₁ h₁
  -- derivative formulas
  have hD₀ := c03m_aux_phit_hasDerivAt hU hΨ₀ y t z hyz
  have hD₁ := c03m_aux_phit_hasDerivAt hU hΨ₁ y t z hyz
  have hDΦ := (hD₀.const_mul (1 - σ)).add (hD₁.const_mul σ)
  have hl₀ := c03m_aux_convex_bounds ht0.le ht1 ⟨(h₀ y hyU).1, (h₀ y hyU).2.1⟩
    ⟨(h₀ _ hyz).1, (h₀ _ hyz).2.1⟩
  have hl₁ := c03m_aux_convex_bounds ht0.le ht1 ⟨(h₁ y hyU).1, (h₁ y hyU).2.1⟩
    ⟨(h₁ _ hyz).1, (h₁ _ hyz).2.1⟩
  have hlΦ := c03m_aux_convex_bounds hσ.1 hσ.2 hl₀ hl₁
  have hDΦd : deriv (fun z' => (1 - σ) * c03_mult_phit Ψ₀ y t z' + σ * c03_mult_phit Ψ₁ y t z') z =
      (1 - σ) * ((1 - t) * deriv Ψ₀ y + t * deriv Ψ₀ (y + t * z)) +
        σ * ((1 - t) * deriv Ψ₁ y + t * deriv Ψ₁ (y + t * z)) := hDΦ.deriv
  refine ⟨hD₀.deriv, hD₁.deriv, by rw [hDΦd, hD₀.deriv, hD₁.deriv], by rw [hDΦd]; exact hlΦ.1,
    by rw [hDΦd]; exact hlΦ.2, ?_, ?_⟩
  · -- the reciprocal
    set W := (U ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U with hW_def
    have hℓ : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => w.1 + t * w.2) := by fun_prop
    have hW : IsOpen W := (hU.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
    have hq : (y, z) ∈ W := ⟨⟨hyU, trivial⟩, hyz⟩
    obtain ⟨hL₀s, hL₀⟩ := c03m_aux_lamt_M hY0 hΨ₀ hb₀ (by linarith) hΛ0.le ht0.le ht1 hyU hyz
    obtain ⟨hL₁s, hL₁⟩ := c03m_aux_lamt_M hY0 hΨ₁ hb₁ (by linarith) hΛ0.le ht0.le ht1 hyU hyz
    set L₀ : ℝ × ℝ → ℂ := fun w : ℝ × ℝ => ((1 - t : ℝ) : ℂ) * ((deriv Ψ₀ w.1 : ℝ) : ℂ) +
        ((t : ℝ) : ℂ) * ((deriv Ψ₀ (w.1 + t * w.2) : ℝ) : ℂ) with hL₀_def
    set L₁ : ℝ × ℝ → ℂ := fun w : ℝ × ℝ => ((1 - t : ℝ) : ℂ) * ((deriv Ψ₁ w.1 : ℝ) : ℂ) +
        ((t : ℝ) : ℂ) * ((deriv Ψ₁ (w.1 + t * w.2) : ℝ) : ℂ) with hL₁_def
    set g : ℝ × ℝ → ℝ := fun w => (1 - σ) * ((1 - t) * deriv Ψ₀ w.1 + t * deriv Ψ₀ (w.1 + t * w.2)) +
        σ * ((1 - t) * deriv Ψ₁ w.1 + t * deriv Ψ₁ (w.1 + t * w.2)) with hg_def
    set G : ℝ × ℝ → ℂ := fun w => ((1 - σ : ℝ) : ℂ) * L₀ w + ((σ : ℝ) : ℂ) * L₁ w with hG_def
    have hGg : ∀ w, G w = ((g w : ℝ) : ℂ) := by
      intro w; simp only [hG_def, hL₀_def, hL₁_def, hg_def]; push_cast; ring
    have hA₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ((1 - σ : ℝ) : ℂ) * L₀ w) W :=
      contDiffOn_const.mul hL₀s
    have hA₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ((σ : ℝ) : ℂ) * L₁ w) W :=
      contDiffOn_const.mul hL₁s
    have hGs : ContDiffOn ℝ (⊤ : ℕ∞) G W := hA₀.add hA₁
    have hgpos : ∀ w ∈ W, c₀⁻¹ * Λ ≤ g w := by
      intro w hw
      have e₀ := c03m_aux_convex_bounds ht0.le ht1 ⟨(h₀ _ hw.1.1).1, (h₀ _ hw.1.1).2.1⟩
        ⟨(h₀ _ hw.2).1, (h₀ _ hw.2).2.1⟩
      have e₁ := c03m_aux_convex_bounds ht0.le ht1 ⟨(h₁ _ hw.1.1).1, (h₁ _ hw.1.1).2.1⟩
        ⟨(h₁ _ hw.2).1, (h₁ _ hw.2).2.1⟩
      exact (c03m_aux_convex_bounds hσ.1 hσ.2 e₀ e₁).1
    have hm : 0 < c₀⁻¹ * Λ := by positivity
    have hG0 : ∀ w ∈ W, G w ≠ 0 := by
      intro w hw
      rw [hGg]
      exact_mod_cast (hm.trans_le (hgpos w hw)).ne'
    have hGm : c₀⁻¹ * Λ ≤ ‖G (y, z)‖ := by
      rw [hGg, Complex.norm_real, Real.norm_eq_abs]
      exact (hgpos _ hq).trans (le_abs_self _)
    have hSB : c03m_aux_SB G y z j s CS Λ Y⁻¹ (t * Y⁻¹) := by
      intro a ha b hb'
      rw [c03m_aux_M_add hW hA₀ hA₁ a b hq, c03m_aux_M_const_mul, c03m_aux_M_const_mul]
      have e₀ := hL₀ a b (by omega)
      have e₁ := hL₁ a b (by omega)
      calc _ ≤ ‖((1 - σ : ℝ) : ℂ) * c03m_aux_M L₀ a b y z‖ +
            ‖((σ : ℝ) : ℂ) * c03m_aux_M L₁ a b y z‖ := norm_add_le _ _
        _ ≤ (1 - σ) * (CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b) +
            σ * (CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) ^ b) := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg (by linarith [hσ.2]), abs_of_nonneg hσ.1]
            gcongr
            · linarith [hσ.2]
            · exact hσ.1
        _ = _ := by ring
    have hInv := c03m_aux_SB_inv hW hGs hG0 hq (by linarith) hΛ0.le hm (by positivity)
      (by positivity) hGm hSB j le_rfl s le_rfl
    have hev : (fun w : ℝ × ℝ => ((1 / deriv (fun z'' => (1 - σ) * c03_mult_phit Ψ₀ w.1 t z'' +
        σ * c03_mult_phit Ψ₁ w.1 t z'') w.2 : ℝ) : ℂ)) =ᶠ[𝓝 (y, z)] fun w => (G w)⁻¹ := by
      filter_upwards [hW.mem_nhds hq] with w hw
      have d₀ := c03m_aux_phit_hasDerivAt hU hΨ₀ w.1 t w.2 hw.2
      have d₁ := c03m_aux_phit_hasDerivAt hU hΨ₁ w.1 t w.2 hw.2
      have dd : deriv (fun z'' => (1 - σ) * c03_mult_phit Ψ₀ w.1 t z'' +
          σ * c03_mult_phit Ψ₁ w.1 t z'') w.2 =
          (1 - σ) * ((1 - t) * deriv Ψ₀ w.1 + t * deriv Ψ₀ (w.1 + t * w.2)) +
            σ * ((1 - t) * deriv Ψ₁ w.1 + t * deriv Ψ₁ (w.1 + t * w.2)) :=
        ((d₀.const_mul (1 - σ)).add (d₁.const_mul σ)).deriv
      rw [dd, hGg]
      simp only [hg_def]
      push_cast
      ring
    have eF := c03m_aux_M_ofReal (fun w : ℝ × ℝ => 1 / deriv (fun z'' => (1 - σ) *
      c03_mult_phit Ψ₀ w.1 t z'' + σ * c03_mult_phit Ψ₁ w.1 t z'') w.2) j s y z
    calc _ = ‖c03m_aux_M (fun w : ℝ × ℝ => ((1 / deriv (fun z'' => (1 - σ) *
          c03_mult_phit Ψ₀ w.1 t z'' + σ * c03_mult_phit Ψ₁ w.1 t z'') w.2 : ℝ) : ℂ)) j s y z‖ := by
          rw [eF, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖c03m_aux_M (fun w => (G w)⁻¹) j s y z‖ := by rw [c03m_aux_M_congr hev]
      _ ≤ (2 ^ (j + s) * CS * Λ * (c₀⁻¹ * Λ)⁻¹ + 1) ^ (j + s) * (c₀⁻¹ * Λ)⁻¹ * Y⁻¹ ^ j *
          (t * Y⁻¹) ^ s := hInv
      _ = (c₀ * Kc ^ (j + s)) * Λ⁻¹ * Y ^ (-(j : ℝ)) * (t / Y) ^ s := by
          have e1 : 2 ^ (j + s) * CS * Λ * (c₀⁻¹ * Λ)⁻¹ + 1 = Kc := by
            rw [hKc]; field_simp
          rw [e1, Real.rpow_neg hY0.le, Real.rpow_natCast, inv_pow, div_eq_mul_inv, mul_inv,
            inv_inv]
          ring
      _ ≤ _ := by
          gcongr
          linarith [show 0 ≤ 2 ^ (j + s) * CS + 4 ^ s * CS by positivity]
  · -- the phase
    intro hj hz
    have hz' : 0 < |z| := abs_pos.2 hz
    obtain ⟨hP₀s, hP₀⟩ := c03m_aux_phit_M hY0 hΨ₀ hb₀ (by linarith) hΛ0.le ht0 ht1 hy hyz hz
    obtain ⟨hP₁s, hP₁⟩ := c03m_aux_phit_M hY0 hΨ₁ hb₁ (by linarith) hΛ0.le ht0 ht1 hy hyz hz
    set W := (U ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U with hW_def
    have hℓ : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => w.1 + t * w.2) := by fun_prop
    have hW : IsOpen W := (hU.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
    have hq : (y, z) ∈ W := ⟨⟨hyU, trivial⟩, hyz⟩
    have hA₀ := (contDiffOn_const (c := ((1 - σ : ℝ) : ℂ))).mul hP₀s
    have hA₁ := (contDiffOn_const (c := ((σ : ℝ) : ℂ))).mul hP₁s
    have eF := c03m_aux_M_ofReal (fun w : ℝ × ℝ => (1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 +
      σ * c03_mult_phit Ψ₁ w.1 t w.2) j s y z
    have hfun : (fun w : ℝ × ℝ => (((1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 +
        σ * c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ)) = fun w =>
        ((1 - σ : ℝ) : ℂ) * ((c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ) +
          ((σ : ℝ) : ℂ) * ((c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ) := by
      funext w; push_cast; ring
    set B := (2 ^ (j + s) * CS + 4 ^ s * CS) * Λ * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ s) with hB
    calc _ = ‖c03m_aux_M (fun w : ℝ × ℝ => (((1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 +
          σ * c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ)) j s y z‖ := by
          rw [eF, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (1 - σ) * B + σ * B := by
          rw [hfun, c03m_aux_M_add hW hA₀ hA₁ j s hq, c03m_aux_M_const_mul,
            c03m_aux_M_const_mul]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (by linarith [hσ.2]), abs_of_nonneg hσ.1]
          gcongr
          · linarith [hσ.2]
          · exact hσ.1
      _ = (2 ^ (j + s) * CS + 4 ^ s * CS) * Λ * Y ^ (-(j : ℝ)) * |z| ^ (1 - (s : ℝ)) := by
          rw [Real.rpow_neg hY0.le, Real.rpow_natCast, Real.rpow_sub hz', Real.rpow_one,
            Real.rpow_natCast, hB, inv_pow, inv_pow]
          ring
      _ ≤ _ := by
          have hC : 2 ^ (j + s) * CS + 4 ^ s * CS ≤
              c₀ * Kc ^ (j + s) + (2 ^ (j + s) * CS + 4 ^ s * CS) := by
            linarith [show 0 ≤ c₀ * Kc ^ (j + s) by positivity]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC hΛ0.le) (by positivity)) (by positivity)

/-- Blueprint: lem:c03_mult_kernel_identity.  For `y` in the phase interval (in particular
`y ∈ [Y,2Y]`), `F_y ∈ C_c^∞`, `F_y(0) = a(y)`, the defining kernel integral of
`|D|^p(ae^{iΨ})(y)` and the localized kernel integral converge absolutely, and
`e^{-iΨ(y)}|D|^p(ae^{iΨ})(y) - λ(y)^p a(y) = -c_p ∫ e^{iλ(y)z}(F_y(z)-a(y))|z|^{-1-p} dz`.
Encoding: stated for `Y/2 < y < 3Y` (contains `[Y,2Y]`), as needed for `y`-derivatives
downstream. -/
theorem c03_mult_kernel_identity (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Y : ℝ) (hY : 1 ≤ Y)
    (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (hlam : ∀ y ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ y) (y : ℝ) (hy : y ∈ Ioo (Y / 2) (3 * Y)) :
    ContDiff ℝ (⊤ : ℕ∞) (c03_mult_F Y a Ψ y) ∧ HasCompactSupport (c03_mult_F Y a Ψ y) ∧
    c03_mult_F Y a Ψ y 0 = a y ∧
    Integrable (fun z : ℝ => ((fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y -
        (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) ∧
    Integrable (fun z : ℝ => Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
      (c03_mult_F Y a Ψ y z - a y) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    Complex.exp (-(Complex.I * (Ψ y : ℂ))) *
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y -
        ((deriv Ψ y ^ p : ℝ) : ℂ) * a y =
      -(c03_cp p : ℂ) * ∫ z : ℝ, Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
        (c03_mult_F Y a Ψ y z - a y) / ((|z| ^ (1 + p) : ℝ) : ℂ) := by
  have hyU : y ∈ Ioo (Y / 4) (4 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨hFs, hFc⟩ := c03m_aux_F_smooth ha has hΨ y
  set g : ℝ → ℂ := fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ)) with hg_def
  obtain ⟨hgs, hgc⟩ := c03m_aux_prod_smooth ha has hΨ
  have hF0 : c03_mult_F Y a Ψ y 0 = a y := by
    have h : Y / 4 < y ∧ y < 4 * Y := hyU
    simp [c03_mult_F, h, c03_mult_Theta]
  set l := deriv Ψ y with hl_def
  have hl : 0 < l := hlam y hyU
  -- the localized integrand
  obtain ⟨MF, hMF0, hMF⟩ := c03m_aux_lip_bound (hFs.of_le (by exact_mod_cast le_top)) hFc
  have hI2 : Integrable (fun z : ℝ => Complex.exp (Complex.I * (l : ℂ) * z) *
      (c03_mult_F Y a Ψ y z - a y) / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
    refine c03m_aux_kernel_integrable hp hp1 (K := MF) ?_ (fun z => ?_) (fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ => Complex.exp (Complex.I * (l : ℂ) * z)).mul
        (hFs.continuous.sub continuous_const) |>.aestronglyMeasurable
    · rw [norm_mul, c03m_aux_norm_exp_I, one_mul, ← hF0]
      simpa using (hMF 0 z).1
    · rw [norm_mul, c03m_aux_norm_exp_I, one_mul, ← hF0]
      simpa using (hMF 0 z).2
  -- the defining kernel integrand
  obtain ⟨Mg, hMg0, hMg⟩ := c03m_aux_lip_bound (hgs.of_le (by exact_mod_cast le_top)) hgc
  have hk : Integrable (fun w : ℝ => (g y - g (y + w)) / ((|w| ^ (1 + p) : ℝ) : ℂ)) := by
    refine c03m_aux_kernel_integrable hp hp1 (K := Mg) ?_ (fun w => ?_) (fun w => ?_)
    · exact (continuous_const.sub (hgs.continuous.comp (continuous_const.add continuous_id)))
        |>.aestronglyMeasurable
    · rw [norm_sub_rev]; exact (hMg y w).1
    · rw [norm_sub_rev]; exact (hMg y w).2
  have hI1 : Integrable (fun z : ℝ => (g y - g z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ)) := by
    have := hk.comp_sub_right y
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [add_sub_cancel, abs_sub_comm z y, add_comm p 1]
  refine ⟨hFs, hFc, hF0, hI1, hI2, ?_⟩
  -- the identity
  obtain ⟨-, -, hker, -, hcp, -⟩ := c03c_c03_frac_kernel_formula p hp hp1
  obtain ⟨hint1, hval1⟩ := hker l
  have hshift : ∫ z : ℝ, (g y - g z) / ((|y - z| ^ (p + 1) : ℝ) : ℂ) =
      ∫ w : ℝ, (g y - g (y + w)) / ((|w| ^ (1 + p) : ℝ) : ℂ) := by
    rw [← integral_add_left_eq_self _ y]
    congr 1; funext w
    simp only [sub_add_cancel_left, abs_neg, add_comm p 1]
  have hpt : ∀ w : ℝ, Complex.exp (-(Complex.I * (Ψ y : ℂ))) *
      ((g y - g (y + w)) / ((|w| ^ (1 + p) : ℝ) : ℂ)) =
      a y * ((1 - Complex.exp (Complex.I * (l : ℂ) * w)) / ((|w| ^ (1 + p) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (l : ℂ) * w) * (c03_mult_F Y a Ψ y w - a y) /
        ((|w| ^ (1 + p) : ℝ) : ℂ) := by
    intro w
    have h1 := c03m_aux_F_shift (Ψ := Ψ) has y w
    have h2 : Complex.exp (-(Complex.I * (Ψ y : ℂ))) * g y = a y := by
      simp only [hg_def]
      rw [mul_left_comm, ← Complex.exp_add]; simp
    simp only [hg_def] at h2 ⊢
    rw [mul_div_assoc', mul_sub, h2, h1]
    ring
  unfold fracDC
  rw [hshift, ← mul_assoc, mul_comm (Complex.exp _), mul_assoc, ← integral_const_mul]
  simp only [hpt]
  rw [integral_sub (hint1.const_mul _) hI2, integral_const_mul, ← hcp]
  rw [show ((l ^ p : ℝ) : ℂ) = ((|l| ^ p : ℝ) : ℂ) by rw [abs_of_pos hl], ← hval1]
  ring


/-! ### Symbol bounds for differences -/

lemma c03m_aux_SB_add {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) {y z : ℝ}
    (hq : (y, z) ∈ W) {J S : ℕ} {c₁ c₂ M α β : ℝ}
    (h₁ : c03m_aux_SB F y z J S c₁ M α β) (h₂ : c03m_aux_SB G y z J S c₂ M α β) :
    c03m_aux_SB (fun w => F w + G w) y z J S (c₁ + c₂) M α β := by
  intro a ha b hb
  rw [c03m_aux_M_add hW hF hG a b hq]
  calc _ ≤ ‖c03m_aux_M F a b y z‖ + ‖c03m_aux_M G a b y z‖ := norm_add_le _ _
    _ ≤ c₁ * M * α ^ a * β ^ b + c₂ * M * α ^ a * β ^ b := add_le_add (h₁ a ha b hb) (h₂ a ha b hb)
    _ = _ := by ring

lemma c03m_aux_SB_congr {F G : ℝ × ℝ → ℂ} {y z : ℝ} (h : F =ᶠ[𝓝 (y, z)] G) {J S : ℕ}
    {c M α β : ℝ} (hG : c03m_aux_SB G y z J S c M α β) : c03m_aux_SB F y z J S c M α β := by
  intro a ha b hb
  rw [c03m_aux_M_congr h]
  exact hG a ha b hb

lemma c03m_aux_SB_monoM {F : ℝ × ℝ → ℂ} {y z : ℝ} {J S : ℕ} {c M M' α β : ℝ}
    (h : c03m_aux_SB F y z J S c M α β) (hMM : M ≤ M') (hc : 0 ≤ c) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    c03m_aux_SB F y z J S c M' α β := fun a ha b hb =>
  (h a ha b hb).trans (by gcongr)

lemma c03m_aux_M_zero_fun (a b : ℕ) (y z : ℝ) : c03m_aux_M (fun _ => (0 : ℂ)) a b y z = 0 := by
  simp [c03m_aux_M, iteratedDeriv_const]

/-- Telescoping: symbol bound for a difference of finite products. -/
lemma c03m_aux_SB_prod_diff {ι : Type*} [DecidableEq ι] (s : Finset ι) {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) {F₁ F₀ : ι → ℝ × ℝ → ℂ} (hF₁ : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F₁ i) W)
    (hF₀ : ∀ i ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F₀ i) W) {y z : ℝ} (hq : (y, z) ∈ W) {J S : ℕ}
    {c δ α β : ℝ} {M : ι → ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hM : ∀ i ∈ s, 0 ≤ M i) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (h₁ : ∀ i ∈ s, c03m_aux_SB (F₁ i) y z J S c (M i) α β)
    (h₀ : ∀ i ∈ s, c03m_aux_SB (F₀ i) y z J S c (M i) α β)
    (hd : ∀ i ∈ s, c03m_aux_SB (fun w => F₁ i w - F₀ i w) y z J S c (δ * M i) α β) :
    c03m_aux_SB (fun w => ∏ i ∈ s, F₁ i w - ∏ i ∈ s, F₀ i w) y z J S
      (s.card * (2 ^ (J + S) * (c + 1)) ^ s.card) (δ * ∏ i ∈ s, M i) α β := by
  set Q : ℝ := 2 ^ (J + S) * (c + 1) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hcQ : 2 ^ (J + S) * c ≤ Q := by rw [hQ]; gcongr; linarith
  induction s using Finset.induction_on with
  | empty =>
    intro a ha b hb
    have : (fun w : ℝ × ℝ => ∏ i ∈ (∅ : Finset ι), F₁ i w - ∏ i ∈ (∅ : Finset ι), F₀ i w) =
        fun _ => (0 : ℂ) := by funext w; simp
    rw [this, c03m_aux_M_zero_fun, norm_zero]
    simp
  | insert i s hi ih =>
    have hF₁' : ∀ k ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F₁ k) W := fun k hk => hF₁ k (by simp [hk])
    have hF₀' : ∀ k ∈ s, ContDiffOn ℝ (⊤ : ℕ∞) (F₀ k) W := fun k hk => hF₀ k (by simp [hk])
    have hM' : ∀ k ∈ s, 0 ≤ M k := fun k hk => hM k (by simp [hk])
    have ih' := ih hF₁' hF₀' hM' (fun k hk => h₁ k (by simp [hk])) (fun k hk => h₀ k (by simp [hk]))
      (fun k hk => hd k (by simp [hk]))
    have hMs : 0 ≤ ∏ k ∈ s, M k := Finset.prod_nonneg hM'
    have hMi := hM i (by simp)
    have hP₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ∏ k ∈ s, F₁ k w) W := contDiffOn_prod hF₁'
    have hP₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ∏ k ∈ s, F₀ k w) W := contDiffOn_prod hF₀'
    have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ∏ k ∈ s, F₁ k w - ∏ k ∈ s, F₀ k w) W := hP₁.sub hP₀
    have hE : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => F₁ i w - F₀ i w) W :=
      (hF₁ i (by simp)).sub (hF₀ i (by simp))
    -- the two terms
    have hT1 := c03m_aux_SB_mul hW (hF₁ i (by simp)) hD hq hc (by positivity) hMi
      (by positivity) hα hβ (h₁ i (by simp)) ih'
    have hP0b := c03m_aux_SB_prod s hW hF₀' hq (c := fun _ => c) (fun _ _ => hc) hM' hα hβ
      (fun k hk => h₀ k (by simp [hk]))
    have hT2 := c03m_aux_SB_mul hW hE hP₀ hq hc (by positivity) (by positivity) hMs hα hβ
      (hd i (by simp)) hP0b
    have e1 : M i * (δ * ∏ k ∈ s, M k) = δ * ∏ k ∈ insert i s, M k := by
      rw [Finset.prod_insert hi]; ring
    have e2 : δ * M i * ∏ k ∈ s, M k = δ * ∏ k ∈ insert i s, M k := by
      rw [Finset.prod_insert hi]; ring
    rw [e1] at hT1
    rw [e2] at hT2
    have hsum := c03m_aux_SB_add hW ((hF₁ i (by simp)).mul hD) (hE.mul hP₀) hq hT1 hT2
    have hfun : (fun w => ∏ k ∈ insert i s, F₁ k w - ∏ k ∈ insert i s, F₀ k w) =
        fun w => F₁ i w * (∏ k ∈ s, F₁ k w - ∏ k ∈ s, F₀ k w) +
          (F₁ i w - F₀ i w) * ∏ k ∈ s, F₀ k w := by
      funext w; rw [Finset.prod_insert hi, Finset.prod_insert hi]; ring
    rw [hfun]
    refine c03m_aux_SB_mono hsum ?_ (mul_nonneg hδ (Finset.prod_nonneg hM)) hα hβ
    rw [Finset.card_insert_of_notMem hi, Finset.prod_const, Finset.card_eq_sum_ones s]
    rw [← Finset.card_eq_sum_ones]
    have hcn : (2 : ℝ) ^ ((J + S) * s.card) * c ^ s.card ≤ Q ^ s.card := by
      rw [pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcQ _
    have hQn : 0 ≤ Q ^ s.card := by positivity
    calc 2 ^ (J + S) * c * (s.card * Q ^ s.card) +
          2 ^ (J + S) * c * (2 ^ ((J + S) * s.card) * c ^ s.card)
        ≤ Q * (s.card * Q ^ s.card) + Q * Q ^ s.card := by gcongr
      _ = ((s.card + 1 : ℕ) : ℝ) * Q ^ (s.card + 1) := by push_cast; ring

/-- Symbol bound for one phase factor `Θ_y^{(i+1)}(tz) = Ψ^{(i+1)}(y+tz) - [i=0]λ(y)`. -/
lemma c03m_aux_Phi_SB {Y Λ CS t : ℝ} (hY0 : 0 < Y) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) {j s i : ℕ}
    (hlam : ∀ k ≤ i + j + s + 1, ∀ x ∈ Ioo (Y / 4) (4 * Y),
      |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k)
    (hCS : 0 ≤ CS) (hΛ : 0 ≤ Λ) (ht0 : 0 < t) {W : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hW1 : ∀ w ∈ W, w.1 ∈ Ioo (Y / 4) (4 * Y)) (hW2 : ∀ w ∈ W, w.1 + t * w.2 ∈ Ioo (Y / 4) (4 * Y))
    {y z : ℝ} (hq : (y, z) ∈ W) (hz : z ≠ 0) (htz : t * |z| ≤ 4 * Y) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ =>
      ((iteratedDeriv (i + 1) Ψ (w.1 + t * w.2) - if i = 0 then deriv Ψ w.1 else 0 : ℝ) : ℂ)) W ∧
    c03m_aux_SB (fun w : ℝ × ℝ =>
      ((iteratedDeriv (i + 1) Ψ (w.1 + t * w.2) - if i = 0 then deriv Ψ w.1 else 0 : ℝ) : ℂ))
      y z j s (4 ^ s * CS) (if i = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i) Y⁻¹ |z|⁻¹ := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 + t * w.2 with hℓ_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ := by fun_prop
  have hin : y + t * z ∈ U := hW2 _ hq
  have hyU : y ∈ U := hW1 _ hq
  have hz' : 0 < |z| := abs_pos.2 hz
  set cs : ℝ := 4 ^ s * CS with hcs
  have hdΨ : ContDiffOn ℝ (⊤ : ℕ∞) (deriv Ψ) U := ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hΨ).2
  have hdΨk : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k (deriv Ψ)) U := fun k =>
    c03m_aux_iteratedDeriv_contDiffOn hU hdΨ k
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ =>
      ((iteratedDeriv (i + 1) Ψ (w.1 + t * w.2) - if i = 0 then deriv Ψ w.1 else 0 : ℝ) : ℂ)) W := by
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn (ContDiffOn.sub ?_ ?_)
    · exact (c03m_aux_iteratedDeriv_contDiffOn hU hΨ (i + 1)).comp hℓ.contDiffOn
        (fun w hw => hW2 w hw)
    · split_ifs
      · exact hdΨ.comp contDiff_fst.contDiffOn (fun w hw => hW1 w hw)
      · exact contDiffOn_const
  refine ⟨hsm, ?_⟩
  have hYi : 0 ≤ Y⁻¹ := by positivity
  have hcompl : ∀ i' ≤ i, c03m_aux_SB (fun w => (((iteratedDeriv i' (deriv Ψ)) (ℓ w) : ℝ) : ℂ))
      y z j s cs (Λ * Y⁻¹ ^ i') Y⁻¹ |z|⁻¹ := by
    intro i' hi'
    have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ((iteratedDeriv i' (deriv Ψ) x : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hdΨk i')
    refine c03m_aux_SB_comp hU hf ht0.le hY0 hW hW2 hq hz htz j s hCS (by positivity)
      fun k hk => ?_
    rw [c03m_aux_iteratedDeriv_ofReal _ _ _ (((hdΨk i').contDiffAt (hU.mem_nhds hin)).of_le
      (by exact_mod_cast le_top)), Complex.norm_real, Real.norm_eq_abs, c03m_aux_iter_shift]
    calc _ ≤ CS * Λ * Y⁻¹ ^ (k + i') := hlam (k + i') (by omega) _ hin
      _ = _ := by rw [pow_add]; ring
  by_cases hi0 : i = 0
  · subst hi0
    simp only [↓reduceIte]
    have hΦ0 : (fun w : ℝ × ℝ => ((iteratedDeriv (0 + 1) Ψ (w.1 + t * w.2) -
        deriv Ψ w.1 : ℝ) : ℂ)) = fun w => (((iteratedDeriv 0 (deriv Ψ)) (ℓ w) : ℝ) : ℂ) -
        (((iteratedDeriv 0 (deriv Ψ)) w.1 : ℝ) : ℂ) := by
      funext w; simp [ℓ, iteratedDeriv_one]
    rw [hΦ0]
    intro a ha b hb'
    have hF2 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun w : ℝ × ℝ => (((iteratedDeriv 0 (deriv Ψ)) w.1 : ℝ) : ℂ)) W :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((hdΨk 0).comp contDiff_fst.contDiffOn
        (fun w hw => hW1 w hw))
    have hF1 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun w : ℝ × ℝ => (((iteratedDeriv 0 (deriv Ψ)) (ℓ w) : ℝ) : ℂ)) W :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((hdΨk 0).comp hℓ.contDiffOn
        (fun w hw => hW2 w hw))
    rw [c03m_aux_M_sub hW hF1 hF2 a b hq]
    have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ((iteratedDeriv 0 (deriv Ψ) x : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hdΨk 0)
    rw [show (fun w : ℝ × ℝ => (((iteratedDeriv 0 (deriv Ψ)) (ℓ w) : ℝ) : ℂ)) =
        fun w => (fun x => ((iteratedDeriv 0 (deriv Ψ) x : ℝ) : ℂ)) (w.1 + t * w.2) from rfl,
      c03m_aux_M_comp hU hf t hW hW2 a b hq,
      c03m_aux_M_fst (fun x => ((iteratedDeriv 0 (deriv Ψ) x : ℝ) : ℂ)) a b y z]
    rw [c03m_aux_iteratedDeriv_ofReal _ _ _ (((hdΨk 0).contDiffAt (hU.mem_nhds hin)).of_le
      (by exact_mod_cast le_top)), c03m_aux_iter_shift, add_zero]
    have htY : t * Y⁻¹ = (Y⁻¹ * (t * |z|)) * |z|⁻¹ := by field_simp
    have htY4 : t * Y⁻¹ ≤ 4 * |z|⁻¹ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hY0]
      calc t = t * |z| * |z|⁻¹ := by field_simp
        _ ≤ 4 * Y * |z|⁻¹ := by gcongr
        _ = _ := by ring
    split_ifs with hb0
    · -- `b = 0`: mean value theorem
      subst hb0
      rw [c03m_aux_iteratedDeriv_ofReal _ _ _ (((hdΨk 0).contDiffAt (hU.mem_nhds hyU)).of_le
        (by exact_mod_cast le_top)), c03m_aux_iter_shift, add_zero, pow_zero, one_mul,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, pow_zero, mul_one]
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := iteratedDeriv a (deriv Ψ))
        (C := CS * Λ * Y⁻¹ ^ (a + 1)) (s := U)
        (fun x hx => ((hdΨk a).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
        (fun x hx => by
          rw [← iteratedDeriv_succ, Real.norm_eq_abs]
          exact hlam (a + 1) (by omega) x hx) (convex_Ioo _ _) hyU hin
      rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left, abs_mul, abs_of_pos ht0] at hmvt
      calc _ ≤ CS * Λ * Y⁻¹ ^ (a + 1) * (t * |z|) := hmvt
        _ ≤ cs * Λ * Y⁻¹ ^ (a + 1) * (t * |z|) := by
            gcongr; rw [hcs]; nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := s)]
        _ = _ := by rw [pow_add]; ring
    · -- `b ≥ 1`
      rw [sub_zero, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
        Complex.norm_real, Real.norm_eq_abs]
      have h1 := hlam (a + b) (by omega) _ hin
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have h4 : (t * Y⁻¹) ^ b' ≤ 4 ^ s * |z|⁻¹ ^ b' := by
        calc (t * Y⁻¹) ^ b' ≤ (4 * |z|⁻¹) ^ b' := pow_le_pow_left₀ (by positivity) htY4 b'
          _ = 4 ^ b' * |z|⁻¹ ^ b' := mul_pow _ _ _
          _ ≤ 4 ^ s * |z|⁻¹ ^ b' := by gcongr; norm_num; omega
      calc t ^ (b' + 1) * |iteratedDeriv (a + (b' + 1)) (deriv Ψ) (y + t * z)|
          ≤ t ^ (b' + 1) * (CS * Λ * Y⁻¹ ^ (a + (b' + 1))) := by gcongr
        _ = CS * Λ * Y⁻¹ ^ a * (t * Y⁻¹) * (t * Y⁻¹) ^ b' := by ring
        _ = CS * Λ * Y⁻¹ ^ a * ((Y⁻¹ * (t * |z|)) * |z|⁻¹) * (t * Y⁻¹) ^ b' := by rw [← htY]
        _ ≤ CS * Λ * Y⁻¹ ^ a * ((Y⁻¹ * (t * |z|)) * |z|⁻¹) * (4 ^ s * |z|⁻¹ ^ b') := by gcongr
        _ = _ := by rw [hcs]; ring
  · rw [if_neg hi0]
    have hΦi : (fun w : ℝ × ℝ => ((iteratedDeriv (i + 1) Ψ (w.1 + t * w.2) -
        if i = 0 then deriv Ψ w.1 else 0 : ℝ) : ℂ)) =
        fun w => (((iteratedDeriv i (deriv Ψ)) (ℓ w) : ℝ) : ℂ) := by
      funext w; simp only [hi0, ↓reduceIte, sub_zero, ℓ]
      rw [iteratedDeriv_succ']
    rw [hΦi]; exact hcompl i le_rfl

/-- Blueprint: lem:c03_mult_difference_symbols.  For two data with `δ`-close derivatives
(`δ ≥ 0`), `|∂_y^j ∂_z^s(b_{1,t} - b_{0,t})| ≤ C δ B Y^{-j} |z|^{K-s}` (`z ≠ 0`) and, where
`y + tz ∈ (Y/4,4Y)`, `|∂_y^j ∂_z^s(φ_{1,t} - φ_{0,t})| ≤ C δ Y^{-j-1} |z|^{1-s}`; symbol and
difference hypotheses through order `2N+j+s+3`. -/
theorem c03_mult_difference_symbols (c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ) (hN : 1 ≤ N) (r : ℕ)
    (q : Fin (2 * N - 1) → ℕ) (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    ∀ j s : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ →
      c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + s + 3) a₀ Ψ₀ →
      c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + s + 3) a₁ Ψ₁ →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ 2 * N + j + s + 3,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
      ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ z : ℝ, z ≠ 0 →
        ‖iteratedDeriv j (fun y' => iteratedDeriv s (fun z' =>
            c03_mult_bt Y a₁ Ψ₁ N r q y' t z' - c03_mult_bt Y a₀ Ψ₀ N r q y' t z') z) y‖ ≤
          C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) ∧
        (y + t * z ∈ Ioo (Y / 4) (4 * Y) →
        |iteratedDeriv j (fun y' => iteratedDeriv s (fun z' =>
            c03_mult_phit Ψ₁ y' t z' - c03_mult_phit Ψ₀ y' t z') z) y| ≤
          C * δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ))) := by
  intro j s Ck
  set CS : ℝ := ∑ k ∈ Finset.range (2 * N + j + s + 4), |Ck k| + 1 with hCS
  have hCS1 : 1 ≤ CS := by
    have : 0 ≤ ∑ k ∈ Finset.range (2 * N + j + s + 4), |Ck k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hCk : ∀ k < 2 * N + j + s + 4, Ck k ≤ CS := by
    intro k hk
    have := Finset.single_le_sum (f := fun k => |Ck k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hk)
    linarith [le_abs_self (Ck k)]
  set cs : ℝ := 4 ^ s * CS with hcs
  have hcs1 : 1 ≤ cs := by
    have : (1 : ℝ) ≤ 4 ^ s := one_le_pow₀ (by norm_num)
    nlinarith
  set T : Finset (Σ _ : Fin (2 * N - 1), ℕ) := Finset.univ.sigma (fun i => Finset.range (q i))
    with hT
  set nT := T.card
  set Q : ℝ := 2 ^ (j + s) * (cs + 1) with hQ
  set CZ : ℝ := 2 ^ ((j + s) * (2 * N - 1)) * cs ^ (2 * N - 1) with hCZ
  set PT : ℝ := 2 ^ ((j + s) * nT) * cs ^ nT with hPT
  set DT : ℝ := nT * Q ^ nT with hDT
  set Cb : ℝ := 2 ^ (j + s) * CZ * (2 ^ (j + s) * cs * DT + 2 ^ (j + s) * cs * PT) with hCb
  set Cφ : ℝ := 2 ^ (j + s) * CS + 4 ^ s * CS with hCφ
  have hCb0 : 0 ≤ Cb := by positivity
  have hCφ0 : 0 ≤ Cφ := by positivity
  refine ⟨Cb + Cφ + 1, by positivity, ?_⟩
  intro Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ hyp₀ hyp₁ hdiff y hy t ht z hz
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hz' : 0 < |z| := abs_pos.2 hz
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hV : IsOpen V := isOpen_Ioo
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyV : y ∈ V := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hyU : y ∈ U := hVU hyV
  obtain ⟨ha₀, has₀, hΨ₀, hb₀⟩ := hyp₀
  obtain ⟨ha₁, has₁, hΨ₁, hb₁⟩ := hyp₁
  have hYi : 0 ≤ Y⁻¹ := by positivity
  have hzi : 0 ≤ |z|⁻¹ := by positivity
  have hrp : ∀ k : ℕ, Y ^ (-(k : ℝ)) = Y⁻¹ ^ k := fun k => by
    rw [Real.rpow_neg hY0.le, Real.rpow_natCast, inv_pow]
  have hY1 : Y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hY
  -- the phase difference `D = Ψ₁ - Ψ₀`
  set D : ℝ → ℝ := fun x => Ψ₁ x - Ψ₀ x with hD_def
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) D U := hΨ₁.sub hΨ₀
  have hlamD : ∀ k ≤ 2 * N + j + s + 2, ∀ x ∈ U,
      |iteratedDeriv k (deriv D) x| ≤ CS * (δ * Y⁻¹) * Y⁻¹ ^ k := by
    intro k hk x hx
    rw [← iteratedDeriv_succ']
    have h1 := (hdiff x hx (k + 1) (by omega)).2
    rw [hrp] at h1
    refine h1.trans ?_
    rw [pow_succ]
    have hc := hCk (k + 1) (by omega)
    have h0 : 0 ≤ δ * (Y⁻¹ ^ k * Y⁻¹) := mul_nonneg hδ (mul_nonneg (pow_nonneg hYi _) hYi)
    calc Ck (k + 1) * δ * (Y⁻¹ ^ k * Y⁻¹) = Ck (k + 1) * (δ * (Y⁻¹ ^ k * Y⁻¹)) := by ring
      _ ≤ CS * (δ * (Y⁻¹ ^ k * Y⁻¹)) := mul_le_mul_of_nonneg_right hc h0
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  swap
  · -- the phase difference
    intro hyz
    obtain ⟨-, hP⟩ := c03m_aux_phit_M hY0 hD (j := j) (s := s) (fun x hx k hk => hlamD k (by omega) x hx)
      (by linarith) (by positivity) ht0 ht1 hyV hyz hz
    have eF := c03m_aux_M_ofReal (fun w : ℝ × ℝ => c03_mult_phit Ψ₁ w.1 t w.2 -
      c03_mult_phit Ψ₀ w.1 t w.2) j s y z
    have hev : (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₁ w.1 t w.2 - c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ))
        =ᶠ[𝓝 (y, z)] fun w => ((c03_mult_phit D w.1 t w.2 : ℝ) : ℂ) := by
      have hO : ∀ᶠ w : ℝ × ℝ in 𝓝 (y, z), w.1 ∈ U :=
        continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
      filter_upwards [hO] with w hw
      have h1 : DifferentiableAt ℝ Ψ₁ w.1 :=
        (hΨ₁.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hw)
      have h0 : DifferentiableAt ℝ Ψ₀ w.1 :=
        (hΨ₀.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hw)
      have hdD : deriv D w.1 = deriv Ψ₁ w.1 - deriv Ψ₀ w.1 := deriv_sub h1 h0
      simp only [c03_mult_phit, c03_mult_Theta, hdD]
      simp only [hD_def]
      push_cast; ring
    calc _ = ‖c03m_aux_M (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₁ w.1 t w.2 -
          c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ)) j s y z‖ := by
          rw [eF, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖c03m_aux_M (fun w : ℝ × ℝ => ((c03_mult_phit D w.1 t w.2 : ℝ) : ℂ)) j s y z‖ := by
          rw [c03m_aux_M_congr hev]
      _ ≤ Cφ * (δ * Y⁻¹) * Y⁻¹ ^ j * (|z| * |z|⁻¹ ^ s) := hP
      _ = Cφ * δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ)) := by
          rw [Real.rpow_sub hY0, Real.rpow_neg hY0.le, Real.rpow_natCast, Real.rpow_one,
            Real.rpow_sub hz', Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv, div_eq_mul_inv,
            inv_pow, inv_pow]
          ring
      _ ≤ _ := by
          have hC : Cφ ≤ Cb + Cφ + 1 := by linarith
          have : 0 ≤ δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ)) := by positivity
          calc Cφ * δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ)) =
              Cφ * (δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ))) := by ring
            _ ≤ (Cb + Cφ + 1) * (δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ))) :=
              mul_le_mul_of_nonneg_right hC this
            _ = _ := by ring
  -- the amplitude difference
  have hcs0 : 0 ≤ cs := by linarith
  have hδY : δ * Y⁻¹ ≤ δ * Λ := mul_le_mul_of_nonneg_left (hY1.trans hΛ) hδ
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 + t * w.2 with hℓ_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ := by fun_prop
  have hAd : ∀ a : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) a → ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv r a) := by
    intro a ha
    rw [iteratedDeriv_eq_iterate]; exact ha.iterate_deriv r
  have hA₀s : tsupport (iteratedDeriv r a₀) ⊆ U := (c03m_aux_tsupport_iteratedDeriv a₀ r).trans has₀
  have hA₁s : tsupport (iteratedDeriv r a₁) ⊆ U := (c03m_aux_tsupport_iteratedDeriv a₁ r).trans has₁
  change ‖c03m_aux_M (fun w => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 -
    c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) j s y z‖ ≤ _
  have hsz := c03m_aux_size_nonneg N q hY0 hΛ0.le hA.le ht0.le
  have hX0 : 0 ≤ δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
      |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) := by positivity
  by_cases hin : y + t * z ∈ U
  swap
  · have h0₀ : iteratedDeriv r a₀ =ᶠ[𝓝 (y + t * z)] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 (fun h => hin (hA₀s h))
    have h0₁ : iteratedDeriv r a₁ =ᶠ[𝓝 (y + t * z)] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 (fun h => hin (hA₁s h))
    have h0₀' : ∀ᶠ w in 𝓝 ((y, z) : ℝ × ℝ), iteratedDeriv r a₀ (ℓ w) = 0 :=
      (hℓ.continuous.tendsto (y, z)).eventually h0₀
    have h0₁' : ∀ᶠ w in 𝓝 ((y, z) : ℝ × ℝ), iteratedDeriv r a₁ (ℓ w) = 0 :=
      (hℓ.continuous.tendsto (y, z)).eventually h0₁
    have hev : (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 -
        c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) =ᶠ[𝓝 (y, z)] fun _ => 0 := by
      filter_upwards [h0₀', h0₁'] with w hw₀ hw₁
      rw [c03m_aux_bt_eq a₁ hΨ₁ N r q, c03m_aux_bt_eq a₀ hΨ₀ N r q]
      simp only [ℓ] at hw₀ hw₁
      simp only [hw₀, hw₁, zero_mul, mul_zero, ite_self, sub_self]
    rw [c03m_aux_M_congr hev, c03m_aux_M_zero_fun, norm_zero]
    have : 0 ≤ Cb + Cφ + 1 := by linarith
    calc (0 : ℝ) ≤ (Cb + Cφ + 1) * (δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
          |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s)) := mul_nonneg this hX0
      _ = _ := by ring
  -- inside the phase domain
  set W : Set (ℝ × ℝ) := (V ×ˢ univ) ∩ ℓ ⁻¹' U with hW_def
  have hW : IsOpen W := (hV.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
  have hq : ((y, z) : ℝ × ℝ) ∈ W := ⟨⟨hyV, trivial⟩, hin⟩
  have hW1 : ∀ w ∈ W, w.1 ∈ U := fun w hw => hVU hw.1.1
  have hW2 : ∀ w ∈ W, w.1 + t * w.2 ∈ U := fun w hw => hw.2
  have htz : t * |z| ≤ 4 * Y := c03m_aux_tz_le ht0 hyV hin
  set Φ : (ℝ → ℝ) → Fin (2 * N - 1) → ℝ × ℝ → ℂ := fun Ψ i w =>
    ((iteratedDeriv (i.val + 1) Ψ (w.1 + t * w.2) - if i.val = 0 then deriv Ψ w.1 else 0 : ℝ) : ℂ)
    with hΦ_def
  set Mf : Fin (2 * N - 1) → ℝ := fun i =>
    if i.val = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i.val with hMf
  have hMf0 : ∀ i, 0 ≤ Mf i := by
    intro i; simp only [hMf]; split_ifs
    · exact mul_nonneg (mul_nonneg hΛ0.le hYi) (mul_nonneg ht0.le hz'.le)
    · exact mul_nonneg hΛ0.le (pow_nonneg hYi _)
  set Z : ℝ × ℝ → ℂ := fun w => ∏ _k ∈ Finset.range (2 * N - 1), ((w.2 : ℝ) : ℂ) with hZ_def
  have hGeq : ∀ (a : ℝ → ℂ) (Ψ : ℝ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Ψ U → ∀ w ∈ W,
      c03_mult_bt Y a Ψ N r q w.1 t w.2 =
        Z w * (iteratedDeriv r a (ℓ w) * ∏ p ∈ T, Φ Ψ p.1 w) := by
    intro a Ψ hΨ w hw
    rw [c03m_aux_bt_eq a hΨ N r q, if_pos (hW2 w hw)]
    simp only [hZ_def, hT, Finset.prod_sigma, Finset.prod_const, Finset.card_range, c03m_aux_Pi,
      hΦ_def, ℓ]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    have e := Finset.prod_const (s := Finset.range (q i))
      (((iteratedDeriv (i.val + 1) Ψ (w.1 + t * w.2) - if i.val = 0 then deriv Ψ w.1 else 0 : ℝ) : ℂ))
    rw [Finset.card_range] at e
    exact e.symm
  have hev : (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 -
      c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) =ᶠ[𝓝 (y, z)] fun w => Z w *
        (iteratedDeriv r a₁ (ℓ w) * (∏ p ∈ T, Φ Ψ₁ p.1 w - ∏ p ∈ T, Φ Ψ₀ p.1 w) +
          (iteratedDeriv r a₁ (ℓ w) - iteratedDeriv r a₀ (ℓ w)) * ∏ p ∈ T, Φ Ψ₀ p.1 w) := by
    filter_upwards [hW.mem_nhds hq] with w hw
    rw [hGeq a₁ Ψ₁ hΨ₁ w hw, hGeq a₀ Ψ₀ hΨ₀ w hw]; ring
  -- coefficient bounds
  have hlam : ∀ (Ψ : ℝ → ℝ) (a : ℝ → ℂ), (∀ y ∈ U, c₀⁻¹ * Λ ≤ deriv Ψ y ∧ deriv Ψ y ≤ c₀ * Λ ∧
      ∀ k ≤ 2 * N + j + s + 3, |iteratedDeriv k (deriv Ψ) y| ≤ Ck k * Λ * Y ^ (-(k : ℝ)) ∧
        ‖iteratedDeriv k a y‖ ≤ Ck k * A * Y ^ (-(k : ℝ))) →
      (∀ k ≤ 2 * N + j + s + 2, ∀ x ∈ U, |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k) ∧
      (∀ k ≤ 2 * N + j + s + 3, ∀ x ∈ U, ‖iteratedDeriv k a x‖ ≤ CS * A * Y⁻¹ ^ k) := by
    intro Ψ a hb
    constructor
    · intro k hk x hx
      have h1 := ((hb x hx).2.2 k (by omega)).1
      rw [hrp] at h1
      exact h1.trans (by gcongr; exact hCk k (by omega))
    · intro k hk x hx
      have h1 := ((hb x hx).2.2 k hk).2
      rw [hrp] at h1
      exact h1.trans (by gcongr; exact hCk k (by omega))
  obtain ⟨hl₀, hα₀⟩ := hlam Ψ₀ a₀ hb₀
  obtain ⟨hl₁, hα₁⟩ := hlam Ψ₁ a₁ hb₁
  have hαD : ∀ k ≤ 2 * N + j + s + 3, ∀ x ∈ U,
      ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ CS * (δ * A) * Y⁻¹ ^ k := by
    intro k hk x hx
    have h1 := (hdiff x hx k hk).1
    rw [hrp] at h1
    refine h1.trans ?_
    have hc := hCk k (by omega)
    have h0 : 0 ≤ δ * A * Y⁻¹ ^ k := mul_nonneg (mul_nonneg hδ hA.le) (pow_nonneg hYi _)
    calc Ck k * δ * A * Y⁻¹ ^ k = Ck k * (δ * A * Y⁻¹ ^ k) := by ring
      _ ≤ CS * (δ * A * Y⁻¹ ^ k) := mul_le_mul_of_nonneg_right hc h0
      _ = _ := by ring
  -- phase factors
  have hCSn : 0 ≤ CS := by linarith
  have hΦSB : ∀ (Ψ : ℝ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Ψ U → ∀ Λ' : ℝ, 0 ≤ Λ' →
      (∀ k ≤ 2 * N + j + s + 2, ∀ x ∈ U, |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ' * Y⁻¹ ^ k) →
      ∀ i : Fin (2 * N - 1), ContDiffOn ℝ (⊤ : ℕ∞) (Φ Ψ i) W ∧
        c03m_aux_SB (Φ Ψ i) y z j s cs
          (if i.val = 0 then Λ' * Y⁻¹ * (t * |z|) else Λ' * Y⁻¹ ^ i.val) Y⁻¹ |z|⁻¹ := by
    intro Ψ hΨ Λ' hΛ' hl i
    have hi := i.isLt
    exact c03m_aux_Phi_SB hY0 hΨ (i := i.val) (fun k hk x hx => hl k (by omega) x hx)
      hCSn hΛ' ht0 hW hW1 hW2 hq hz htz
  have hsubD : ∀ k, ∀ x ∈ U, iteratedDeriv k D x = iteratedDeriv k Ψ₁ x - iteratedDeriv k Ψ₀ x := by
    intro k x hx
    exact iteratedDeriv_fun_sub ((hΨ₁.contDiffAt (hU.mem_nhds hx)).of_le
      (by exact_mod_cast le_top)) ((hΨ₀.contDiffAt (hU.mem_nhds hx)).of_le
      (by exact_mod_cast le_top))
  have hΦD : ∀ i, (fun w => Φ Ψ₁ i w - Φ Ψ₀ i w) =ᶠ[𝓝 (y, z)] Φ D i := by
    intro i
    filter_upwards [hW.mem_nhds hq] with w hw
    have hd : deriv D w.1 = deriv Ψ₁ w.1 - deriv Ψ₀ w.1 := by
      have := hsubD 1 w.1 (hW1 w hw); simpa [iteratedDeriv_one] using this
    simp only [hΦ_def, hsubD (i.val + 1) _ (hW2 w hw), hd]
    split_ifs <;> push_cast <;> ring
  have hF₁ : ∀ p ∈ T, ContDiffOn ℝ (⊤ : ℕ∞) (Φ Ψ₁ p.1) W := fun p _ =>
    (hΦSB Ψ₁ hΨ₁ Λ hΛ0.le hl₁ p.1).1
  have hF₀ : ∀ p ∈ T, ContDiffOn ℝ (⊤ : ℕ∞) (Φ Ψ₀ p.1) W := fun p _ =>
    (hΦSB Ψ₀ hΨ₀ Λ hΛ0.le hl₀ p.1).1
  have h₁ : ∀ p ∈ T, c03m_aux_SB (Φ Ψ₁ p.1) y z j s cs (Mf p.1) Y⁻¹ |z|⁻¹ := fun p _ =>
    (hΦSB Ψ₁ hΨ₁ Λ hΛ0.le hl₁ p.1).2
  have h₀ : ∀ p ∈ T, c03m_aux_SB (Φ Ψ₀ p.1) y z j s cs (Mf p.1) Y⁻¹ |z|⁻¹ := fun p _ =>
    (hΦSB Ψ₀ hΨ₀ Λ hΛ0.le hl₀ p.1).2
  have hd : ∀ p ∈ T, c03m_aux_SB (fun w => Φ Ψ₁ p.1 w - Φ Ψ₀ p.1 w) y z j s cs (δ * Mf p.1)
      Y⁻¹ |z|⁻¹ := by
    intro p _
    refine c03m_aux_SB_congr (hΦD p.1) ?_
    have h := (hΦSB D hD (δ * Y⁻¹) (mul_nonneg hδ hYi) hlamD p.1).2
    refine c03m_aux_SB_monoM h ?_ hcs0 hYi hzi
    simp only [hMf]
    split_ifs
    · have h2 : 0 ≤ Y⁻¹ * (t * |z|) := mul_nonneg hYi (mul_nonneg ht0.le hz'.le)
      calc δ * Y⁻¹ * Y⁻¹ * (t * |z|) = (δ * Y⁻¹) * (Y⁻¹ * (t * |z|)) := by ring
        _ ≤ (δ * Λ) * (Y⁻¹ * (t * |z|)) := mul_le_mul_of_nonneg_right hδY h2
        _ = _ := by ring
    · have h2 : 0 ≤ Y⁻¹ ^ p.1.val := pow_nonneg hYi _
      calc δ * Y⁻¹ * Y⁻¹ ^ p.1.val = (δ * Y⁻¹) * Y⁻¹ ^ p.1.val := by ring
        _ ≤ (δ * Λ) * Y⁻¹ ^ p.1.val := mul_le_mul_of_nonneg_right hδY h2
        _ = _ := by ring
  have hPd := c03m_aux_SB_prod_diff T hW hF₁ hF₀ hq hcs0 hδ (fun p _ => hMf0 p.1) hYi hzi h₁ h₀ hd
  have hP0 := c03m_aux_SB_prod T hW hF₀ hq (c := fun _ => cs) (fun _ _ => hcs0)
    (fun p _ => hMf0 p.1) hYi hzi h₀
  rw [Finset.prod_const] at hP0
  have hP₁s : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ∏ p ∈ T, Φ Ψ₁ p.1 w) W := contDiffOn_prod hF₁
  have hP₀s : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ∏ p ∈ T, Φ Ψ₀ p.1 w) W := contDiffOn_prod hF₀
  have hMT : 0 ≤ ∏ p ∈ T, Mf p.1 := Finset.prod_nonneg fun p _ => hMf0 p.1
  -- amplitude factors
  have hbA : ∀ (f : ℝ → ℂ) (A' : ℝ), ContDiff ℝ (⊤ : ℕ∞) f → 0 ≤ A' →
      (∀ k ≤ 2 * N + j + s + 3, ∀ x ∈ U, ‖iteratedDeriv k f x‖ ≤ CS * A' * Y⁻¹ ^ k) →
      c03m_aux_SB (fun w => iteratedDeriv r f (ℓ w)) y z j s cs (A' * Y⁻¹ ^ r) Y⁻¹ |z|⁻¹ := by
    intro f A' hf hA' hab
    refine c03m_aux_SB_comp isOpen_univ (hAd f hf).contDiffOn ht0.le hY0 hW (fun _ _ => trivial)
      hq hz htz j s hCSn (mul_nonneg hA' (pow_nonneg hYi _)) fun k hk => ?_
    have e : iteratedDeriv k (iteratedDeriv r f) (y + t * z) =
        iteratedDeriv (r + k) f (y + t * z) := by
      simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply, add_comm k r]
    rw [e]
    have hr : r ≤ 2 * N - 1 := by omega
    have h1 := hab (r + k) (by omega) _ hin
    rw [pow_add] at h1
    calc _ ≤ CS * A' * (Y⁻¹ ^ r * Y⁻¹ ^ k) := h1
      _ = _ := by ring
  have hbA₁ := hbA a₁ A ha₁ hA.le hα₁
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fun x => a₁ x - a₀ x) := ha₁.sub ha₀
  have hbAD' := hbA (fun x => a₁ x - a₀ x) (δ * A) hdA (mul_nonneg hδ hA.le) hαD
  have hevA : (fun w : ℝ × ℝ => iteratedDeriv r a₁ (ℓ w) - iteratedDeriv r a₀ (ℓ w)) =ᶠ[𝓝 (y, z)]
      fun w => iteratedDeriv r (fun x => a₁ x - a₀ x) (ℓ w) := by
    refine Filter.Eventually.of_forall fun w => ?_
    exact (iteratedDeriv_fun_sub (ha₁.contDiffAt.of_le (by exact_mod_cast le_top))
      (ha₀.contDiffAt.of_le (by exact_mod_cast le_top))).symm
  have hbAD := c03m_aux_SB_congr hevA hbAD'
  have hA₁c : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => iteratedDeriv r a₁ (ℓ w)) W :=
    ((hAd a₁ ha₁).comp hℓ).contDiffOn
  have hA₀c : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => iteratedDeriv r a₀ (ℓ w)) W :=
    ((hAd a₀ ha₀).comp hℓ).contDiffOn
  -- the two terms
  have hQ0 : 0 ≤ 2 ^ (j + s) * (cs + 1) := mul_nonneg (pow_nonneg zero_le_two _) (by linarith [hcs0])
  have hDT0 : 0 ≤ (T.card : ℝ) * (2 ^ (j + s) * (cs + 1)) ^ T.card :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hQ0 _)
  have hPT0 : 0 ≤ (2 : ℝ) ^ ((j + s) * T.card) * cs ^ T.card :=
    mul_nonneg (pow_nonneg zero_le_two _) (pow_nonneg hcs0 _)
  have hAY : 0 ≤ A * Y⁻¹ ^ r := mul_nonneg hA.le (pow_nonneg hYi _)
  have hδAY : 0 ≤ δ * A * Y⁻¹ ^ r := mul_nonneg (mul_nonneg hδ hA.le) (pow_nonneg hYi _)
  have hδM : 0 ≤ δ * ∏ p ∈ T, Mf p.1 := mul_nonneg hδ hMT
  have hT1 := c03m_aux_SB_mul hW hA₁c (hP₁s.sub hP₀s) hq hcs0 hDT0 hAY hδM hYi hzi hbA₁ hPd
  have hT2 := c03m_aux_SB_mul hW (hA₁c.sub hA₀c) hP₀s hq hcs0 hPT0 hδAY hMT hYi hzi hbAD hP0
  have e1 : A * Y⁻¹ ^ r * (δ * ∏ p ∈ T, Mf p.1) = δ * (A * Y⁻¹ ^ r * ∏ p ∈ T, Mf p.1) := by ring
  have e2 : δ * A * Y⁻¹ ^ r * ∏ p ∈ T, Mf p.1 = δ * (A * Y⁻¹ ^ r * ∏ p ∈ T, Mf p.1) := by ring
  rw [e1] at hT1
  rw [e2] at hT2
  have hX := c03m_aux_SB_add hW (hA₁c.mul (hP₁s.sub hP₀s)) ((hA₁c.sub hA₀c).mul hP₀s) hq hT1 hT2
  -- the `z^{2N-1}` factor
  have hzs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ)) W :=
    (Complex.ofRealCLM.contDiff.comp contDiff_snd).contDiffOn
  have hbz : c03m_aux_SB (fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ)) y z j s cs |z| Y⁻¹ |z|⁻¹ :=
    c03m_aux_SB_mono (c03m_aux_SB_z y z hz j s hYi) hcs1 hz'.le hYi hzi
  have hZ0 := c03m_aux_SB_prod (Finset.range (2 * N - 1)) hW (F := fun _ w => ((w.2 : ℝ) : ℂ))
    (fun _ _ => hzs) hq (c := fun _ => cs) (M := fun _ => |z|) (fun _ _ => hcs0)
    (fun _ _ => hz'.le) hYi hzi (fun _ _ => hbz)
  have hZ : c03m_aux_SB Z y z j s (2 ^ ((j + s) * (2 * N - 1)) * cs ^ (2 * N - 1))
      (|z| ^ (2 * N - 1)) Y⁻¹ |z|⁻¹ := by
    intro a ha b hb
    have h := hZ0 a ha b hb
    rw [Finset.prod_const, Finset.prod_const, Finset.card_range] at h
    exact h
  have hG := c03m_aux_SB_mul hW (contDiffOn_prod fun _ _ => hzs)
    ((hA₁c.mul (hP₁s.sub hP₀s)).add ((hA₁c.sub hA₀c).mul hP₀s)) hq
    (mul_nonneg (pow_nonneg zero_le_two _) (pow_nonneg hcs0 _))
    (add_nonneg (mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) hcs0) hDT0)
      (mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) hcs0) hPT0))
    (pow_nonneg hz'.le _) (mul_nonneg hδ (mul_nonneg hAY hMT)) hYi hzi hZ hX
  have hb' := (c03m_aux_SB_congr hev hG) j le_rfl s le_rfl
  have hprodT : ∏ p ∈ T, Mf p.1 = ∏ i : Fin (2 * N - 1),
      (if i.val = 0 then Λ * Y⁻¹ * (t * |z|) else Λ * Y⁻¹ ^ i.val) ^ q i := by
    rw [hT, Finset.prod_sigma]
    simp only [Finset.prod_const, Finset.card_range, hMf]
  rw [hprodT] at hb'
  have hsize := c03m_aux_size_eq N r hN q hrq (Λ := Λ) (A := A) (t := t) (z := z) hY0
  have hb2 : ‖c03m_aux_M (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 -
      c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) j s y z‖ ≤
      Cb * δ * (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) * Y⁻¹ ^ j *
        |z|⁻¹ ^ s := by
    rw [← hsize]
    refine hb'.trans (le_of_eq ?_)
    simp only [hCb]
    ring
  refine hb2.trans ?_
  rw [hrp, Real.rpow_sub hz', Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
  have hC : Cb ≤ Cb + Cφ + 1 := by linarith
  have hY' : 0 ≤ δ * (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) * Y⁻¹ ^ j *
      |z|⁻¹ ^ s :=
    mul_nonneg (mul_nonneg (mul_nonneg hδ (mul_nonneg hsz (pow_nonneg hz'.le _)))
      (pow_nonneg hYi _)) (pow_nonneg hzi _)
  calc Cb * δ * (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) * Y⁻¹ ^ j *
        |z|⁻¹ ^ s = Cb * (δ * (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) *
        Y⁻¹ ^ j * |z|⁻¹ ^ s) := by ring
    _ ≤ (Cb + Cφ + 1) * (δ * (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) *
        Y⁻¹ ^ j * |z|⁻¹ ^ s) := mul_le_mul_of_nonneg_right hC hY'
    _ = _ := by ring

/-- Blueprint: lem:c03_mult_interpolation_integral.  For `0 < Y`, smooth compactly supported
amplitudes, smooth phases on `(Y/4,4Y)`, `Y/2 < y < 3Y`, `0 < t ≤ 1`, `η ≥ 0`: all integrals
(including the `(σ,z)` double integral) converge absolutely, the interpolation identity holds,
and both right-hand terms are smooth in `y ∈ (Y/2,3Y)` (so the identity may be differentiated
in `y` any number of times).
Encoding: the identity is stated on the open neighbourhood `(Y/2,3Y)` of `[Y,2Y]`; the
differentiability clause is expressed as smoothness of both sides there. -/
theorem c03_mult_interpolation_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (N : ℕ) (hN : 1 ≤ N)
    (r : ℕ) (q : Fin (2 * N - 1) → ℕ) (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1)
    (Y : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ) (hY : 0 < Y)
    (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) (has₀ : tsupport a₀ ⊆ Ioo (Y / 4) (4 * Y))
    (ha₁ : ContDiff ℝ (⊤ : ℕ∞) a₁) (has₁ : tsupport a₁ ⊆ Ioo (Y / 4) (4 * Y))
    (hΨ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ₀ (Ioo (Y / 4) (4 * Y)))
    (hΨ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ₁ (Ioo (Y / 4) (4 * Y)))
    (η t : ℝ) (hη : 0 ≤ η) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∀ y ∈ Ioo (Y / 2) (3 * Y),
      Integrable (fun z : ℝ => Complex.exp (Complex.I * (c03_mult_phit Ψ₀ y t z : ℂ) -
          ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
      Integrable (fun z : ℝ => Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) -
          ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a₁ Ψ₁ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
      Integrable (fun z : ℝ => Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) -
          ((η * z ^ 2 : ℝ) : ℂ)) *
          (c03_mult_bt Y a₁ Ψ₁ N r q y t z - c03_mult_bt Y a₀ Ψ₀ N r q y t z) /
            ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
      Integrable (Function.uncurry fun (σ z : ℝ) =>
          Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y t z +
              σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
            ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
            c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ))
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) ∧
      c03_mult_I p Y a₁ Ψ₁ N r q η y t - c03_mult_I p Y a₀ Ψ₀ N r q η y t =
        (∫ z : ℝ, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
          (c03_mult_bt Y a₁ Ψ₁ N r q y t z - c03_mult_bt Y a₀ Ψ₀ N r q y t z) /
            ((|z| ^ (1 + p) : ℝ) : ℂ)) +
        Complex.I * ∫ σ in (0 : ℝ)..1, ∫ z : ℝ,
          Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y t z +
              σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
            ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
            c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ =>
      ∫ z : ℝ, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
          (c03_mult_bt Y a₁ Ψ₁ N r q y t z - c03_mult_bt Y a₀ Ψ₀ N r q y t z) /
            ((|z| ^ (1 + p) : ℝ) : ℂ)) (Ioo (Y / 2) (3 * Y)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ =>
      ∫ σ in (0 : ℝ)..1, ∫ z : ℝ,
          Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y t z +
              σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
            ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
            c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) (Ioo (Y / 2) (3 * Y)) := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hV : IsOpen V := isOpen_Ioo
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have ht0 : 0 < t := ht.1
  have hn : 1 ≤ 2 * N - 1 := by omega
  set wt : ℝ → ℂ := fun z => (z : ℂ) ^ (2 * N - 1) / ((|z| ^ (1 + p) : ℝ) : ℂ) with hwt
  set K := Icc (-(8 * Y / t)) (8 * Y / t) with hK_def
  have hK : IsCompact K := isCompact_Icc
  have hwK : IntegrableOn wt K := c03m_aux_weight_integrableOn hp hp1 (2 * N - 1) hn _
  have hwm : AEStronglyMeasurable wt := c03m_aux_weight_meas p hp (2 * N - 1)
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 + t * w.2 with hℓ_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ := by fun_prop
  set S := V ×ˢ (univ : Set ℝ) with hS_def
  have hS : IsOpen S := hV.prod isOpen_univ
  have hout : ∀ y ∈ V, ∀ z ∉ K, y + t * z ∉ U := by
    intro y hy z hz hU'
    simp only [hK_def, mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · have : t * z < -(8 * Y) := by
        have := (lt_div_iff₀ ht0).1 (show z < -(8 * Y) / t by rw [neg_div]; exact hz)
        linarith
      linarith [hU'.1, hy.2]
    · have : 8 * Y < t * z := by
        have := (div_lt_iff₀ ht0).1 hz
        linarith
      linarith [hU'.2, hy.1]
  -- the localized amplitudes
  set A₀ := iteratedDeriv r a₀
  set A₁ := iteratedDeriv r a₁
  have hA₀ : ContDiff ℝ (⊤ : ℕ∞) A₀ := by
    rw [show A₀ = deriv^[r] a₀ from iteratedDeriv_eq_iterate]; exact ha₀.iterate_deriv r
  have hA₁ : ContDiff ℝ (⊤ : ℕ∞) A₁ := by
    rw [show A₁ = deriv^[r] a₁ from iteratedDeriv_eq_iterate]; exact ha₁.iterate_deriv r
  have hA₀s : tsupport A₀ ⊆ U := (c03m_aux_tsupport_iteratedDeriv a₀ r).trans has₀
  have hA₁s : tsupport A₁ ⊆ U := (c03m_aux_tsupport_iteratedDeriv a₁ r).trans has₁
  set P₀ : ℝ × ℝ → ℂ := fun w => c03m_aux_Pi Ψ₀ q w.1 (w.1 + t * w.2)
  set P₁ : ℝ × ℝ → ℂ := fun w => c03m_aux_Pi Ψ₁ q w.1 (w.1 + t * w.2)
  have hP₀ := c03m_aux_Pi_smooth hΨ₀ q t hVU
  have hP₁ := c03m_aux_Pi_smooth hΨ₁ q t hVU
  set φ₀ : ℝ × ℝ → ℝ := fun w => c03_mult_phit Ψ₀ w.1 t w.2
  set φ₁ : ℝ × ℝ → ℝ := fun w => c03_mult_phit Ψ₁ w.1 t w.2
  have hφ₀ := c03m_aux_phit_smooth hΨ₀ t hVU
  have hφ₁ := c03m_aux_phit_smooth hΨ₁ t hVU
  set E₀ : ℝ × ℝ → ℂ := fun w =>
    Complex.exp (Complex.I * (φ₀ w : ℂ) - ((η * w.2 ^ 2 : ℝ) : ℂ))
  set E₁ : ℝ × ℝ → ℂ := fun w =>
    Complex.exp (Complex.I * (φ₁ w : ℂ) - ((η * w.2 ^ 2 : ℝ) : ℂ))
  have hE : ∀ φ : ℝ × ℝ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) φ (S ∩ ℓ ⁻¹' U) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w => Complex.exp (Complex.I * (φ w : ℂ) -
        ((η * w.2 ^ 2 : ℝ) : ℂ))) (S ∩ ℓ ⁻¹' U) := by
    intro φ hφ
    refine Complex.contDiff_exp.comp_contDiffOn ?_
    refine (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)).sub ?_
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_const.mul (contDiff_snd.contDiffOn.pow 2))
  have hE₀ := hE φ₀ hφ₀
  have hE₁ := hE φ₁ hφ₁
  set H₀ : ℝ × ℝ → ℂ := fun w => if ℓ w ∈ U then A₀ (ℓ w) * (P₀ w * E₀ w) else 0
  set H₁ : ℝ × ℝ → ℂ := fun w => if ℓ w ∈ U then A₁ (ℓ w) * (P₁ w * E₁ w) else 0
  set H₁₀ : ℝ × ℝ → ℂ := fun w => if ℓ w ∈ U then A₀ (ℓ w) * (P₀ w * E₁ w) else 0
  have hH₀ : ContDiffOn ℝ (⊤ : ℕ∞) H₀ S :=
    c03m_aux_localized_smooth hU hA₀ hA₀s hℓ hS (hP₀.mul hE₀)
  have hH₁ : ContDiffOn ℝ (⊤ : ℕ∞) H₁ S :=
    c03m_aux_localized_smooth hU hA₁ hA₁s hℓ hS (hP₁.mul hE₁)
  have hH₁₀ : ContDiffOn ℝ (⊤ : ℕ∞) H₁₀ S :=
    c03m_aux_localized_smooth hU hA₀ hA₀s hℓ hS (hP₀.mul hE₁)
  have hsuppH : ∀ (A B : ℝ → ℂ) (Pw : ℝ × ℝ → ℂ), ∀ y ∈ V, ∀ z ∉ K,
      (if ℓ (y, z) ∈ U then A (ℓ (y, z)) * Pw (y, z) else 0) = 0 := by
    intro A B Pw y hy z hz
    simp [ℓ, hout y hy z hz]
  have hcontz : ∀ H : ℝ × ℝ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H S → ∀ y ∈ V,
      Continuous fun z => H (y, z) := fun H hH y hy =>
    hH.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hy, trivial⟩)
  -- integrand identities
  have heq : ∀ (a : ℝ → ℂ) (Ψ : ℝ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Ψ U → ∀ (φ : ℝ → ℝ) (y z : ℝ),
      Complex.exp (Complex.I * (φ z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) =
      wt z * (if ℓ (y, z) ∈ U then iteratedDeriv r a (ℓ (y, z)) *
        (c03m_aux_Pi Ψ q y (y + t * z) *
          Complex.exp (Complex.I * (φ z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ))) else 0) := by
    intro a Ψ hΨ φ y z
    rw [c03m_aux_bt_eq a hΨ N r q y t z]
    simp only [ℓ, wt]
    split_ifs <;> ring
  have heq₀ : ∀ y z, Complex.exp (Complex.I * (c03_mult_phit Ψ₀ y t z : ℂ) -
      ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) =
      wt z * H₀ (y, z) := fun y z => heq a₀ Ψ₀ hΨ₀ (fun z => c03_mult_phit Ψ₀ y t z) y z
  have heq₁ : ∀ y z, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) -
      ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a₁ Ψ₁ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) =
      wt z * H₁ (y, z) := fun y z => heq a₁ Ψ₁ hΨ₁ (fun z => c03_mult_phit Ψ₁ y t z) y z
  have heq₁₀ : ∀ y z, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) -
      ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) =
      wt z * H₁₀ (y, z) := fun y z => heq a₀ Ψ₀ hΨ₀ (fun z => c03_mult_phit Ψ₁ y t z) y z
  have heqT : ∀ y z, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) -
      ((η * z ^ 2 : ℝ) : ℂ)) *
      (c03_mult_bt Y a₁ Ψ₁ N r q y t z - c03_mult_bt Y a₀ Ψ₀ N r q y t z) /
        ((|z| ^ (1 + p) : ℝ) : ℂ) = wt z * (H₁ (y, z) - H₁₀ (y, z)) := by
    intro y z
    rw [mul_sub, sub_div, heq₁ y z, heq₁₀ y z]; ring
  have hint : ∀ H : ℝ × ℝ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H S → (∀ y ∈ V, ∀ z ∉ K, H (y, z) = 0) →
      ∀ y ∈ V, Integrable (fun z => wt z * H (y, z)) := fun H hH hs y hy =>
    c03m_aux_wG_integrable hK hwK (hcontz H hH y hy) (hs y hy)
  have hs₀ : ∀ y ∈ V, ∀ z ∉ K, H₀ (y, z) = 0 := fun y hy z hz => by simp [H₀, ℓ, hout y hy z hz]
  have hs₁ : ∀ y ∈ V, ∀ z ∉ K, H₁ (y, z) = 0 := fun y hy z hz => by simp [H₁, ℓ, hout y hy z hz]
  have hs₁₀ : ∀ y ∈ V, ∀ z ∉ K, H₁₀ (y, z) = 0 := fun y hy z hz => by
    simp [H₁₀, ℓ, hout y hy z hz]
  have hsT : ∀ y ∈ V, ∀ z ∉ K, (H₁ (y, z) - H₁₀ (y, z)) = 0 := fun y hy z hz => by
    rw [hs₁ y hy z hz, hs₁₀ y hy z hz, sub_zero]
  have hI₀ : ∀ y, c03_mult_I p Y a₀ Ψ₀ N r q η y t = ∫ z, wt z * H₀ (y, z) := fun y => by
    unfold c03_mult_I; simp_rw [heq₀]
  have hI₁ : ∀ y, c03_mult_I p Y a₁ Ψ₁ N r q η y t = ∫ z, wt z * H₁ (y, z) := fun y => by
    unfold c03_mult_I; simp_rw [heq₁]
  have hnormE : ∀ x c : ℝ, 0 ≤ c → ‖Complex.exp (Complex.I * (x : ℂ) - ((c : ℝ) : ℂ))‖ ≤ 1 := by
    intro x c hc
    rw [Complex.norm_exp]
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
    rw [Real.exp_le_one_iff]; linarith
  -- the double integrand
  set J : ℝ → ℝ × ℝ → ℂ := fun y w => if y + t * w.2 ∈ U then A₀ (y + t * w.2) *
    (P₀ (y, w.2) * (Complex.exp (Complex.I * (((1 - w.1) * φ₀ (y, w.2) + w.1 * φ₁ (y, w.2) : ℝ) : ℂ) -
      ((η * w.2 ^ 2 : ℝ) : ℂ)) * ((φ₁ (y, w.2) - φ₀ (y, w.2) : ℝ) : ℂ))) else 0 with hJ
  set G₀ : ℝ × ℝ → ℂ := fun w => if ℓ w ∈ U then A₀ (ℓ w) * (P₀ w * ((φ₁ w - φ₀ w : ℝ) : ℂ))
    else 0
  have hG₀ : ContDiffOn ℝ (⊤ : ℕ∞) G₀ S :=
    c03m_aux_localized_smooth hU hA₀ hA₀s hℓ hS
      (hP₀.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (hφ₁.sub hφ₀)))
  have hsG : ∀ y ∈ V, ∀ z ∉ K, G₀ (y, z) = 0 := fun y hy z hz => by simp [G₀, ℓ, hout y hy z hz]
  have hJcont : ∀ y ∈ V, Continuous (J y) := by
    intro y hy
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((y, w.2) : ℝ × ℝ)) :=
      contDiff_const.prodMk contDiff_snd
    have hmaps : MapsTo (fun w : ℝ × ℝ => ((y, w.2) : ℝ × ℝ))
        (univ ∩ (fun w : ℝ × ℝ => y + t * w.2) ⁻¹' U) (S ∩ ℓ ⁻¹' U) :=
      fun w hw => ⟨⟨hy, trivial⟩, hw.2⟩
    have hP' := hP₀.comp hm.contDiffOn hmaps
    have hφ₀' := hφ₀.comp hm.contDiffOn hmaps
    have hφ₁' := hφ₁.comp hm.contDiffOn hmaps
    have hB : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => P₀ (y, w.2) *
        (Complex.exp (Complex.I * (((1 - w.1) * φ₀ (y, w.2) + w.1 * φ₁ (y, w.2) : ℝ) : ℂ) -
          ((η * w.2 ^ 2 : ℝ) : ℂ)) * ((φ₁ (y, w.2) - φ₀ (y, w.2) : ℝ) : ℂ)))
        (univ ∩ (fun w : ℝ × ℝ => y + t * w.2) ⁻¹' U) := by
      refine hP'.mul (ContDiffOn.mul ?_ ?_)
      · refine Complex.contDiff_exp.comp_contDiffOn ((contDiffOn_const.mul
          (Complex.ofRealCLM.contDiff.comp_contDiffOn ?_)).sub ?_)
        · exact ((contDiffOn_const.sub contDiff_fst.contDiffOn).mul hφ₀').add
            (contDiff_fst.contDiffOn.mul hφ₁')
        · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
            (contDiffOn_const.mul (contDiff_snd.contDiffOn.pow 2))
      · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hφ₁'.sub hφ₀')
    have := c03m_aux_localized_smooth hU hA₀ hA₀s (ℓ := fun w : ℝ × ℝ => y + t * w.2)
      (by fun_prop) isOpen_univ hB
    exact (contDiffOn_univ.1 this).continuous
  have hJle : ∀ y z σ, ‖J y (σ, z)‖ ≤ ‖G₀ (y, z)‖ := by
    intro y z σ
    simp only [hJ, G₀, ℓ]
    split_ifs
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
      have := hnormE ((1 - σ) * φ₀ (y, z) + σ * φ₁ (y, z)) (η * z ^ 2) (by positivity)
      have h1 := norm_nonneg (A₀ (y + t * z))
      have h2 := norm_nonneg (P₀ (y, z))
      have h3 := norm_nonneg (((φ₁ (y, z) - φ₀ (y, z) : ℝ) : ℂ))
      calc _ = ‖A₀ (y + t * z)‖ * (‖P₀ (y, z)‖ * (‖Complex.exp (Complex.I *
              (((1 - σ) * φ₀ (y, z) + σ * φ₁ (y, z) : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ))‖ *
              ‖((φ₁ (y, z) - φ₀ (y, z) : ℝ) : ℂ)‖)) := rfl
        _ ≤ ‖A₀ (y + t * z)‖ * (‖P₀ (y, z)‖ * (1 * ‖((φ₁ (y, z) - φ₀ (y, z) : ℝ) : ℂ)‖)) := by
            gcongr
        _ = _ := by ring
    · simp
  have heqD : ∀ y σ z, Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y t z +
        σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
      ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
      c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) = wt z * J y (σ, z) := by
    intro y σ z
    rw [c03m_aux_bt_eq a₀ hΨ₀ N r q y t z]
    simp only [hJ, wt, P₀, φ₀, φ₁]
    split_ifs <;> ring
  have hprod : ∀ y ∈ V, Integrable (Function.uncurry fun (σ z : ℝ) => wt z * J y (σ, z))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    intro y hy
    have hg := (hint G₀ hG₀ hsG y hy).norm
    have hmaj := (integrable_const (1 : ℝ) (μ := volume.restrict (Ioc (0 : ℝ) 1))).mul_prod hg
    refine hmaj.mono' ?_ (Eventually.of_forall fun w => ?_)
    · exact hwm.comp_snd.mul (hJcont y hy).aestronglyMeasurable
    · simp only [Function.uncurry, one_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hJle y w.2 w.1) (norm_nonneg _)
  -- the identity
  have hident : ∀ y ∈ V, c03_mult_I p Y a₁ Ψ₁ N r q η y t - c03_mult_I p Y a₀ Ψ₀ N r q η y t =
      (∫ z : ℝ, wt z * (H₁ (y, z) - H₁₀ (y, z))) +
        Complex.I * ∫ σ in (0 : ℝ)..1, ∫ z : ℝ, wt z * J y (σ, z) := by
    intro y hy
    have hi₀ := hint H₀ hH₀ hs₀ y hy
    have hi₁ := hint H₁ hH₁ hs₁ y hy
    have hiT := hint (fun w => H₁ w - H₁₀ w) (hH₁.sub hH₁₀) hsT y hy
    have hpt : ∀ z, wt z * H₁ (y, z) - wt z * H₀ (y, z) = wt z * (H₁ (y, z) - H₁₀ (y, z)) +
        Complex.I * ∫ σ in (0 : ℝ)..1, wt z * J y (σ, z) := by
      intro z
      rw [← heq₁ y z, ← heq₀ y z, ← heqT y z]
      simp_rw [← heqD y]
      set c : ℂ := ((η * z ^ 2 : ℝ) : ℂ)
      have hc : ∀ x : ℂ, Complex.exp (Complex.I * x - c) = Complex.exp (Complex.I * x) /
          Complex.exp c := fun x => Complex.exp_sub _ _
      simp_rw [hc]
      have hσ : (∫ σ in (0 : ℝ)..1, Complex.exp (Complex.I *
            (((1 - σ) * c03_mult_phit Ψ₀ y t z + σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ)) /
            Complex.exp c * ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
            c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
          (∫ σ in (0 : ℝ)..1, Complex.exp (Complex.I *
            (((1 - σ) * c03_mult_phit Ψ₀ y t z + σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ))) *
            (((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
              c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) / Complex.exp c) := by
        rw [← intervalIntegral.integral_mul_const]
        congr 1; funext σ; ring
      rw [hσ]
      have hi := c03m_aux_exp_interp (c03_mult_phit Ψ₁ y t z) (c03_mult_phit Ψ₀ y t z)
      linear_combination (c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) /
        Complex.exp c) * hi
    have hInner : Integrable (fun z => ∫ σ in (0 : ℝ)..1, wt z * J y (σ, z)) := by
      simp_rw [intervalIntegral.integral_of_le zero_le_one]
      exact (hprod y hy).integral_prod_right
    calc c03_mult_I p Y a₁ Ψ₁ N r q η y t - c03_mult_I p Y a₀ Ψ₀ N r q η y t
        = (∫ z, wt z * H₁ (y, z)) - ∫ z, wt z * H₀ (y, z) := by rw [hI₁, hI₀]
      _ = ∫ z, (wt z * H₁ (y, z) - wt z * H₀ (y, z)) := (integral_sub hi₁ hi₀).symm
      _ = ∫ z, (wt z * (H₁ (y, z) - H₁₀ (y, z)) +
            Complex.I * ∫ σ in (0 : ℝ)..1, wt z * J y (σ, z)) := by
          congr 1; funext z; exact hpt z
      _ = (∫ z, wt z * (H₁ (y, z) - H₁₀ (y, z))) +
            ∫ z, Complex.I * ∫ σ in (0 : ℝ)..1, wt z * J y (σ, z) :=
          integral_add hiT (hInner.const_mul _)
      _ = _ := by
          rw [integral_const_mul]
          congr 2
          simp_rw [intervalIntegral.integral_of_le zero_le_one]
          exact (integral_integral_swap (f := fun σ z => wt z * J y (σ, z)) (hprod y hy)).symm
  have hsmI₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => c03_mult_I p Y a₀ Ψ₀ N r q η y t) V := by
    simp_rw [hI₀]; exact c03m_aux_param_smooth hV hK hwm hwK hH₀ hs₀
  have hsmI₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => c03_mult_I p Y a₁ Ψ₁ N r q η y t) V := by
    simp_rw [hI₁]; exact c03m_aux_param_smooth hV hK hwm hwK hH₁ hs₁
  have hsmT : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ∫ z : ℝ, wt z * (H₁ (y, z) - H₁₀ (y, z))) V :=
    c03m_aux_param_smooth hV hK hwm hwK (H := fun w => H₁ w - H₁₀ w) (hH₁.sub hH₁₀) hsT
  have hTform : ∀ y, (∫ z : ℝ, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) -
      ((η * z ^ 2 : ℝ) : ℂ)) *
      (c03_mult_bt Y a₁ Ψ₁ N r q y t z - c03_mult_bt Y a₀ Ψ₀ N r q y t z) /
        ((|z| ^ (1 + p) : ℝ) : ℂ)) = ∫ z : ℝ, wt z * (H₁ (y, z) - H₁₀ (y, z)) := fun y => by
    congr 1; funext z; exact heqT y z
  have hDform : ∀ y, (∫ σ in (0 : ℝ)..1, ∫ z : ℝ,
      Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y t z +
          σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
        c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
      ∫ σ in (0 : ℝ)..1, ∫ z : ℝ, wt z * J y (σ, z) := fun y => by
    congr 1; funext σ; congr 1; funext z; exact heqD y σ z
  refine ⟨fun y hy => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (hint H₀ hH₀ hs₀ y hy).congr (Eventually.of_forall fun z => (heq₀ y z).symm)
  · exact (hint H₁ hH₁ hs₁ y hy).congr (Eventually.of_forall fun z => (heq₁ y z).symm)
  · exact (hint (fun w => H₁ w - H₁₀ w) (hH₁.sub hH₁₀) hsT y hy).congr
      (Eventually.of_forall fun z => (heqT y z).symm)
  · exact (hprod y hy).congr (Eventually.of_forall fun w => (heqD y w.1 w.2).symm)
  · rw [hident y hy, hTform, hDform]
  · simp_rw [hTform]; exact hsmT
  · simp_rw [hDform]
    refine (((hsmI₁.sub hsmI₀).sub hsmT).const_smul (-Complex.I)).congr fun y hy => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hident y hy]
    ring_nf
    rw [Complex.I_sq]; ring

/-- Blueprint: lem:c03_mult_two_term_coefficients.  `B₀ = λ^p a`, `B₁ = -ipλ^{p-1}a'`,
`B₂ = -p(p-1)/2 · λ^{p-2}(a'' + iλ'a)`, and for `j = 0,1`,
`|∂_y^j(p(p-1)/2 · λ^{p-2} a'')| ≤ C A Y^{-2-j} Λ^{p-2}` under `𝖧` through order `4`. -/
theorem c03_mult_two_term_coefficients (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ)
    (hc₀ : 0 < c₀) :
    (∀ (Y : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 0 < Y → ContDiff ℝ (⊤ : ℕ∞) a →
      tsupport a ⊆ Ioo (Y / 4) (4 * Y) → ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)) →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ x) → ∀ y ∈ Icc Y (2 * Y),
        c03_mult_B p Y a Ψ 0 y = ((deriv Ψ y ^ p : ℝ) : ℂ) * a y ∧
        c03_mult_B p Y a Ψ 1 y = -Complex.I * ((p * deriv Ψ y ^ (p - 1) : ℝ) : ℂ) * deriv a y ∧
        c03_mult_B p Y a Ψ 2 y = -((p * (p - 1) / 2 * deriv Ψ y ^ (p - 2) : ℝ) : ℂ) *
          (deriv (deriv a) y + Complex.I * ((deriv (deriv Ψ) y : ℝ) : ℂ) * a y)) ∧
    ∀ j : ℕ, j ≤ 1 → ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck 4 a Ψ → ∀ y ∈ Icc Y (2 * Y),
        ‖iteratedDeriv j (fun y' => ((p * (p - 1) / 2 * deriv Ψ y' ^ (p - 2) : ℝ) : ℂ) *
            deriv (deriv a) y') y‖ ≤ C * A * Y ^ (-(2 : ℝ) - j) * Λ ^ (p - 2) := by
  exact ⟨c03m_aux_two_term_B p, c03m_aux_two_term_bound p hp1 c₀ hc₀⟩

/-! ### Regularised fractional moments -/

lemma c03m_aux_fm_cut_bound (χ₁ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ₁)
    (hχ01 : ∀ z, 0 ≤ χ₁ z ∧ χ₁ z ≤ 1)
    (hχ1 : ∀ z ∈ Icc (-1 : ℝ) 1, χ₁ z = 1) (hχs : ∀ z, 2 < |z| → χ₁ z = 0) (i : ℕ) :
    ∃ M, 0 < M ∧ ∀ Λ : ℝ, 0 < Λ → ∀ z : ℝ, z ≠ 0 →
      ‖iteratedDeriv i (fun z => ((χ₁ (Λ * z) : ℝ) : ℂ)) z‖ ≤ M * |z| ^ (0 - (i : ℝ)) := by
  obtain ⟨M, hM, hb⟩ := c03c_aux_cutoff_deriv χ₁ hχ hχ01 hχ1 hχs i
  refine ⟨M + 1, by positivity, fun Λ hΛ z hz => ?_⟩
  rw [c03m_aux_iteratedDeriv_ofReal', Complex.norm_real, Real.norm_eq_abs, zero_sub]
  have h0 : 0 ≤ |z| ^ (-(i:ℝ)) := by positivity
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, neg_zero, Real.rpow_zero, mul_one]
    have := hχ01 (Λ * z); rw [abs_of_nonneg this.1]; linarith
  · have := hb Λ hΛ z hz
    rw [iteratedDeriv_const_sub hi, iteratedDeriv_neg, abs_neg] at this
    nlinarith

lemma c03m_aux_fm_pow_bound (m i : ℕ) (z : ℝ) :
    ‖iteratedDeriv i (fun z : ℝ => ((z ^ m : ℝ) : ℂ)) z‖ ≤
      (m.descFactorial i : ℝ) * |z| ^ ((m : ℝ) - i) := by
  rw [c03m_aux_iteratedDeriv_ofReal', Complex.norm_real, Real.norm_eq_abs]
  rw [iteratedDeriv_pow, abs_mul, abs_pow, Nat.abs_cast]
  rcases le_or_gt i m with him | him
  · rw [← Real.rpow_natCast, Nat.cast_sub him]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 him]; simp

lemma c03m_aux_fm_cut_supp (χ₁ : ℝ → ℝ) (hχs : ∀ z, 2 < |z| → χ₁ z = 0) {Λ : ℝ} (hΛ : 0 < Λ) :
    HasCompactSupport (fun z => ((χ₁ (Λ * z) : ℝ) : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-(2 / Λ)) (2 / Λ))
    isCompact_Icc ?_
  intro x hx
  by_contra h
  apply hx
  have : 2 < |Λ * x| := by
    rw [abs_mul, abs_of_pos hΛ, ← div_lt_iff₀' hΛ]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [abs_of_neg (by linarith [show 0 < 2 / Λ by positivity])]; linarith
    · rw [abs_of_pos (by linarith [show 0 < 2 / Λ by positivity])]; linarith
  simp [hχs _ this]

lemma c03m_aux_fm_trunc (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hm : 1 ≤ m)
    (χ₁ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ₁) (hχ01 : ∀ z, 0 ≤ χ₁ z ∧ χ₁ z ≤ 1)
    (hχ1 : ∀ z ∈ Icc (-1 : ℝ) 1, χ₁ z = 1) (hχs : ∀ z, 2 < |z| → χ₁ z = 0) :
    ∃ C, 0 < C ∧ ∀ Λ : ℝ, 0 < Λ → ∀ η : ℝ, 0 ≤ η → ∀ l : ℝ, 0 < l →
      ‖∫ z : ℝ, Complex.exp (Complex.I * ((l * z : ℝ) : ℂ)) * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) *
        (((z ^ m : ℝ) : ℂ) * ((χ₁ (Λ * z) : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ ≤
        C * l ^ (p - m) := by
  have hK : p < (m : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨s₀, hs₀⟩ := c03c_c03_ibp_homogeneous p m 1 hp hp1 hK one_pos
  choose M hM hMb using c03m_aux_fm_cut_bound χ₁ hχ hχ01 hχ1 hχs
  set T : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * (m.descFactorial i : ℝ) * M (j - i) with hT
  obtain ⟨C, hC, hCb⟩ := hs₀ (fun s => 1 + |T s|)
  refine ⟨C, hC, fun Λ hΛ η hη l hl => ?_⟩
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((χ₁ (Λ * z) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_const.mul contDiff_id))
  have hpd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ => ((z ^ m : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.pow m)
  have hderiv : ∀ z, deriv (fun z : ℝ => l * z) z = l := fun z => by
    simp
  have hb : ∀ z ∈ (univ : Set ℝ), z ≠ 0 → ∀ s ≤ s₀,
      ‖iteratedDeriv s (fun z => ((z ^ m : ℝ) : ℂ) * ((χ₁ (Λ * z) : ℝ) : ℂ)) z‖ ≤
        (1 + |T s|) * 1 * |z| ^ ((m : ℝ) - s) := by
    intro z _ hz s _
    have := c03c_aux_symbol_mul hz s (hpd.contDiffAt.of_le (by exact_mod_cast le_top)) (hcd.contDiffAt.of_le (by exact_mod_cast le_top)) (fun i => (m.descFactorial i : ℝ))
      M m 0 (fun i _ => c03m_aux_fm_pow_bound m i z) (fun i _ => hMb i Λ hΛ z hz) s le_rfl
    rw [add_zero] at this
    refine this.trans ?_
    rw [mul_one]
    gcongr
    exact (le_abs_self _).trans (by linarith)
  have hph : ∀ z ∈ (univ : Set ℝ), (1 : ℝ)⁻¹ * l ≤ |deriv (fun z : ℝ => l * z) z| ∧
      |deriv (fun z : ℝ => l * z) z| ≤ 1 * l := by
    intro z _
    rw [hderiv, abs_of_pos hl]; simp
  have hrec : ∀ z ∈ (univ : Set ℝ), z ≠ 0 → ∀ s ≤ s₀,
      |iteratedDeriv s (fun z => 1 / deriv (fun z : ℝ => l * z) z) z| ≤
        (1 + |T s|) * l⁻¹ * |z| ^ (-(s : ℝ)) := by
    intro z _ _ s _
    simp only [hderiv]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [abs_of_pos hl]
      have : 0 ≤ |T 0| * l⁻¹ := by positivity
      nlinarith
    · simp only [iteratedDeriv_const, hs.ne', ite_false, abs_zero]; positivity
  have h1 := (hCb l 1 univ (fun z => ((z ^ m : ℝ) : ℂ) * ((χ₁ (Λ * z) : ℝ) : ℂ))
    (fun z => l * z) hl zero_le_one isOpen_univ (hpd.mul hcd)
    ((c03m_aux_fm_cut_supp χ₁ hχs hΛ).mul_left) (subset_univ _)
    (contDiff_const.mul contDiff_id).contDiffOn hb hph hrec).1 η hη
  simpa using h1

/-- Integrands of the regularised moments: `1 - e^{ilz}` for `m = 0`, `-e^{ilz} z^m` for `m ≥ 1`. -/
def c03m_aux_fmP (m : ℕ) (l z : ℝ) : ℂ :=
  if m = 0 then 1 - Complex.exp (Complex.I * l * z) else -(Complex.exp (Complex.I * l * z) * (z : ℂ) ^ m)

/-- Regularised moments `Q_m(η,l) = c_p ∫ P_m(l,z) e^{-ηz²} |z|^{-1-p} dz`. -/
def c03m_aux_fmQ (p : ℝ) (m : ℕ) (η l : ℝ) : ℂ :=
  (c03_cp p : ℂ) * ∫ z : ℝ, c03m_aux_fmP m l z * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) /
    ((|z| ^ (1 + p) : ℝ) : ℂ)

lemma c03m_aux_fmQ_pos (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (η l : ℝ) :
    c03m_aux_fmQ p m η l = -(c03_cp p : ℂ) * ∫ z : ℝ, Complex.exp (Complex.I * l * z) *
      (z : ℂ) ^ m * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) := by
  have hm0 : m ≠ 0 := by omega
  simp only [c03m_aux_fmQ, c03m_aux_fmP, hm0, ite_false]
  rw [neg_mul, ← mul_neg, ← integral_neg]
  congr 2; funext z; ring

/-- Uniform bound on the regularised moments of order `m ≥ 1` for `l ≥ a > 0`. -/
lemma c03m_aux_fm_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (hm : 1 ≤ m) (a : ℝ)
    (ha : 0 < a) : ∃ C, ∀ η : ℝ, 0 < η → ∀ l : ℝ, a ≤ l → ‖c03m_aux_fmQ p m η l‖ ≤ C := by
  obtain ⟨χ₁, hχ, hχ01, hχ1, hχs⟩ := c03c_aux_cutoff_exists
  obtain ⟨C₁, hC₁, hb⟩ := c03m_aux_fm_trunc p hp hp1 m hm χ₁ hχ hχ01 hχ1 hχs
  refine ⟨c03_cp p * (C₁ * a ^ (p - m)), fun η hη l hl => ?_⟩
  have hl : 0 < l := ha.trans_le hl
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, f = fun z : ℝ => Complex.exp (Complex.I * l * z) * (z : ℂ) ^ m *
    Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hfi : Integrable f := hf ▸ c03m_aux_moment_integrable hp hp1 l η hη m hm
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → ℂ, F = fun (n : ℕ) (z : ℝ) => Complex.exp (Complex.I * ((l * z : ℝ) : ℂ)) *
    Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * (((z ^ m : ℝ) : ℂ) * ((χ₁ ((1 / (n + 1 : ℝ)) * z) : ℝ) : ℂ)) /
      ((|z| ^ (1 + p) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hFf : ∀ n z, F n z = f z * ((χ₁ ((1 / (n + 1 : ℝ)) * z) : ℝ) : ℂ) := by
    intro n z; rw [hF, hf]; push_cast; ring_nf
  have hlim : Tendsto (fun n => ∫ z, F n z) atTop (𝓝 (∫ z, f z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖f z‖) (fun n => ?_) hfi.norm
      (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · have hc : Continuous (fun z => ((χ₁ ((1 / (n + 1 : ℝ)) * z) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (hχ.continuous.comp (continuous_const.mul continuous_id))
      rw [show F n = _ from funext (hFf n)]
      exact hfi.aestronglyMeasurable.mul hc.aestronglyMeasurable
    · rw [hFf, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hχ01 ((1 / (n + 1 : ℝ)) * z)
      rw [abs_of_nonneg this.1]
      exact mul_le_of_le_one_right (norm_nonneg _) this.2
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge |z|
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [hFf]
      have hn' : |z| ≤ (n + 1 : ℝ) := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have : (1 / (n + 1 : ℝ)) * z ∈ Icc (-1 : ℝ) 1 := by
        have hpos : (0 : ℝ) < n + 1 := by positivity
        rw [mem_Icc, ← abs_le, abs_mul, abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ hpos,
          mul_one]
        exact hn'
      rw [hχ1 _ this]; simp
  have hbd : ‖∫ z, f z‖ ≤ C₁ * l ^ (p - m) := by
    refine le_of_tendsto' (hlim.norm) (fun n => ?_)
    rw [hF]
    exact hb _ (by positivity) η hη.le l hl
  have hQ : c03m_aux_fmQ p m η l = -(c03_cp p : ℂ) * ∫ z, f z := by
    rw [hf]; exact c03m_aux_fmQ_pos p m hm η l
  have hcp : 0 < c03_cp p := (c03c_c03_frac_kernel_formula p hp hp1).2.1
  rw [hQ, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcp]
  refine mul_le_mul_of_nonneg_left (hbd.trans ?_) hcp.le
  refine mul_le_mul_of_nonneg_left ?_ hC₁.le
  have : p - (m : ℝ) ≤ 0 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  exact Real.rpow_le_rpow_of_nonpos ha (by assumption) this



/-- Second-order Taylor bound from a derivative bound. -/
lemma c03m_aux_taylor2 {G G' G'' : ℝ → ℂ} {l h C : ℝ} (hh : 0 ≤ h)
    (hd1 : ∀ μ ∈ Icc l (l + h), HasDerivAt G (G' μ) μ)
    (hd2 : ∀ μ ∈ Icc l (l + h), HasDerivAt G' (G'' μ) μ)
    (hb : ∀ μ ∈ Icc l (l + h), ‖G'' μ‖ ≤ C) :
    ‖G (l + h) - G l - (h : ℂ) * G' l‖ ≤ C * h * h := by
  have h1 : ∀ x ∈ Icc l (l + h), ‖G' x - G' l‖ ≤ C * (x - l) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun x hx => (hd2 x hx).hasDerivWithinAt)
      (fun x hx => hb x (Ico_subset_Icc_self hx))
  have h2 := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun μ => G μ - (μ : ℂ) * G' l)
    (f' := fun μ => G' μ - G' l) (C := C * h) (a := l) (b := l + h)
    (fun x hx => by
      have := (hd1 x hx).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (G' l))
      simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] at this
      exact this.hasDerivWithinAt)
    (fun x hx => (h1 x (Ico_subset_Icc_self hx)).trans (by
      have hC : 0 ≤ C := (norm_nonneg _).trans (hb l ⟨le_rfl, by linarith⟩)
      exact mul_le_mul_of_nonneg_left (by linarith [hx.2]) hC)) (l + h) ⟨by linarith, le_rfl⟩
  convert h2 using 2
  · push_cast; ring
  · ring

/-- Convergence of derivatives from convergence of functions and uniform second-derivative
bounds. -/
lemma c03m_aux_deriv_limit {G G' G'' : ℝ → ℝ → ℂ} {g : ℝ → ℂ} {g' : ℂ} {l δ₀ C : ℝ}
    {L : Filter ℝ} (hδ₀ : 0 < δ₀)
    (hG : ∀ μ ∈ Ioo (l - δ₀) (l + δ₀), Tendsto (fun η => G η μ) L (𝓝 (g μ)))
    (hg : HasDerivAt g g' l)
    (hd : ∀ᶠ η in L, ∀ μ ∈ Ioo (l - δ₀) (l + δ₀), HasDerivAt (G η) (G' η μ) μ ∧
      HasDerivAt (G' η) (G'' η μ) μ ∧ ‖G'' η μ‖ ≤ C) :
    Tendsto (fun η => G' η l) L (𝓝 g') := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hlo := (hasDerivAt_iff_isLittleO.1 hg).def (show 0 < ε / 4 by positivity)
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.1 hlo
  set h : ℝ := min (min (ρ / 2) (δ₀ / 2)) (ε / (4 * (C' + 1))) with hhdef
  have hh : 0 < h := by positivity
  have hhρ : h < ρ := by
    have := min_le_left (min (ρ / 2) (δ₀ / 2)) (ε / (4 * (C' + 1)))
    have := min_le_left (ρ / 2) (δ₀ / 2); linarith
  have hhδ : h < δ₀ := by
    have := min_le_left (min (ρ / 2) (δ₀ / 2)) (ε / (4 * (C' + 1)))
    have := min_le_right (ρ / 2) (δ₀ / 2); linarith
  have hhε : C' * h ≤ ε / 4 := by
    have := min_le_right (min (ρ / 2) (δ₀ / 2)) (ε / (4 * (C' + 1)))
    calc C' * h ≤ (C' + 1) * (ε / (4 * (C' + 1))) := by gcongr; linarith
      _ = ε / 4 := by field_simp
  have hgh : ‖g (l + h) - g l - h • g'‖ ≤ ε / 4 * h := by
    have := hρb (y := l + h) (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hh]; exact hhρ)
    rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos hh] at this
    exact this
  have hm1 : l + h ∈ Ioo (l - δ₀) (l + δ₀) := ⟨by linarith, by linarith⟩
  have hm0 : l ∈ Ioo (l - δ₀) (l + δ₀) := ⟨by linarith, by linarith⟩
  have e1 := (Metric.tendsto_nhds.1 (hG _ hm1)) (ε * h / 8) (by positivity)
  have e0 := (Metric.tendsto_nhds.1 (hG _ hm0)) (ε * h / 8) (by positivity)
  filter_upwards [hd, e1, e0] with η hη h1 h0
  have hsub : Icc l (l + h) ⊆ Ioo (l - δ₀) (l + δ₀) := fun x hx => ⟨by linarith [hx.1], by
    linarith [hx.2]⟩
  have hT := c03m_aux_taylor2 (G := G η) (G' := G' η) (G'' := G'' η) (C := C') hh.le
    (fun μ hμ => (hη μ (hsub hμ)).1) (fun μ hμ => (hη μ (hsub hμ)).2.1)
    (fun μ hμ => (hη μ (hsub hμ)).2.2.trans (le_max_left _ _))
  rw [dist_eq_norm] at h1 h0 ⊢
  have key : (h : ℂ) * (G' η l - g') = -(G η (l + h) - G η l - (h : ℂ) * G' η l) +
      (G η (l + h) - g (l + h)) - (G η l - g l) + (g (l + h) - g l - h • g') := by
    rw [Complex.real_smul]; ring
  have hn : h * ‖G' η l - g'‖ ≤ C' * h * h + ε * h / 8 + ε * h / 8 + ε / 4 * h := by
    have := congrArg norm key
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] at this
    rw [this]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ?_ hgh
    refine (norm_sub_le _ _).trans (add_le_add ?_ h0.le)
    refine (norm_add_le _ _).trans (add_le_add ?_ h1.le)
    rw [norm_neg]; exact hT
  have : ‖G' η l - g'‖ ≤ C' * h + ε / 2 := by
    have : h * ‖G' η l - g'‖ ≤ h * (C' * h + ε / 2) := by nlinarith
    exact le_of_mul_le_mul_left this hh
  linarith



lemma c03m_aux_fmP_hasDerivAt (m : ℕ) (l z : ℝ) :
    HasDerivAt (fun x => c03m_aux_fmP m x z) (Complex.I * c03m_aux_fmP (m + 1) l z) l := by
  have he : HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * x * z))
      (Complex.exp (Complex.I * l * z) * (Complex.I * 1 * z)) l :=
    (((hasDerivAt_id l).ofReal_comp.const_mul Complex.I).mul_const (z : ℂ)).cexp
  simp only [c03m_aux_fmP, Nat.add_one_ne_zero, ite_false]
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [ite_true]
    convert he.const_sub 1 using 1; ring
  · simp only [hm, ite_false]
    convert (he.mul_const ((z : ℂ) ^ m)).neg using 1; ring

lemma c03m_aux_fmP_norm (m : ℕ) (l z : ℝ) :
    ‖c03m_aux_fmP (m + 1) l z‖ = |z| ^ (m + 1) := by
  simp only [c03m_aux_fmP, Nat.add_one_ne_zero, ite_false, norm_neg, norm_mul,
    c03m_aux_norm_exp_I, one_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

lemma c03m_aux_one_sub_exp_le (l z : ℝ) : ‖1 - Complex.exp (Complex.I * l * z)‖ ≤ |l| * |z| := by
  rw [norm_sub_rev, show Complex.I * (l : ℂ) * (z : ℂ) = Complex.I * ((l * z : ℝ) : ℂ) by push_cast; ring]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]

lemma c03m_aux_fm_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (η l : ℝ) (hη : 0 < η) :
    Integrable (fun z : ℝ => c03m_aux_fmP m l z * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) /
      ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [c03m_aux_fmP, ite_true]
    have hK : 0 ≤ max |l| 2 := by positivity
    refine c03m_aux_kernel_integrable hp hp1 (K := max |l| 2) ?_ (fun z => ?_) (fun z => ?_)
    · exact (by fun_prop : Continuous fun z : ℝ => (1 - Complex.exp (Complex.I * l * z)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))).aestronglyMeasurable
    · rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) (c03m_aux_gauss_le η z hη.le)).trans ?_
      exact (c03m_aux_one_sub_exp_le l z).trans (by gcongr; exact le_max_left _ _)
    · rw [norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) (c03m_aux_gauss_le η z hη.le)).trans ?_
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, c03m_aux_norm_exp_I]
      linarith [le_max_right |l| 2]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have := (c03m_aux_moment_integrable hp hp1 l η hη (k + 1) (by omega)).neg
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [c03m_aux_fmP, Nat.add_one_ne_zero, ite_false, Pi.neg_apply]
    ring


lemma c03m_aux_fmQ_hasDerivAt (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (m : ℕ) (η : ℝ) (hη : 0 < η)
    (l : ℝ) : HasDerivAt (c03m_aux_fmQ p m η) (Complex.I * c03m_aux_fmQ p (m + 1) η l) l := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := l) (s := univ)
    (F := fun x z => c03m_aux_fmP m x z * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) /
      ((|z| ^ (1 + p) : ℝ) : ℂ))
    (F' := fun x z => Complex.I * (c03m_aux_fmP (m + 1) x z * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) /
      ((|z| ^ (1 + p) : ℝ) : ℂ)))
    (bound := fun z => ‖Complex.I * (c03m_aux_fmP (m + 1) 0 z *
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ))‖)
    univ_mem (Eventually.of_forall fun x =>
      (c03m_aux_fm_integrable p hp hp1 m η x hη).aestronglyMeasurable)
    (c03m_aux_fm_integrable p hp hp1 m η l hη)
    ((c03m_aux_fm_integrable p hp hp1 (m + 1) η l hη).const_mul Complex.I).aestronglyMeasurable
    (ae_of_all _ fun z x _ => le_of_eq (by
      simp only [norm_mul, norm_div, c03m_aux_fmP_norm]))
    ((c03m_aux_fm_integrable p hp hp1 (m + 1) η 0 hη).const_mul Complex.I).norm
    (ae_of_all _ fun z x _ => by
      convert ((c03m_aux_fmP_hasDerivAt m x z).mul_const
        (Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)))).div_const (((|z| ^ (1 + p) : ℝ) : ℂ)) using 1
      ring)
  have := key.2.const_mul (c03_cp p : ℂ)
  unfold c03m_aux_fmQ
  convert this using 1
  rw [integral_const_mul]; ring

/-- `k = 0`: the Gaussian-regularised integrals converge to the absolutely convergent one. -/
lemma c03m_aux_fm_base (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (l : ℝ) :
    Tendsto (fun η => c03m_aux_fmQ p 0 η l) (𝓝[>] 0)
      (𝓝 ((c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * l * z)) /
          ((|z| ^ (1 + p) : ℝ) : ℂ))) := by
  simp only [c03m_aux_fmQ, c03m_aux_fmP, ite_true]
  refine Tendsto.const_mul _ ?_
  have hint := ((c03c_c03_frac_kernel_formula p hp hp1).2.2.1 l).1
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖(1 - Complex.exp (Complex.I * l * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖) ?_ ?_ hint.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with η hη
    simpa [c03m_aux_fmP] using (c03m_aux_fm_integrable p hp hp1 0 η l hη).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
    refine Eventually.of_forall fun z => ?_
    rw [norm_div, norm_div, norm_mul]
    gcongr
    exact mul_le_of_le_one_right (norm_nonneg _) (c03m_aux_gauss_le η z hη.le)
  · refine Eventually.of_forall fun z => ?_
    have hc : Continuous (fun η : ℝ => (1 - Complex.exp (Complex.I * l * z)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this

/-- The limits `(-i)^m m^{(m)}(l)` written explicitly, `m(ξ) = ξ^p`. -/
lemma c03m_aux_fm_iter (p : ℝ) (m : ℕ) (l : ℝ) :
    iteratedDeriv m (fun ξ : ℝ => ξ ^ p) l = (descPochhammer ℝ m).eval p * l ^ (p - m) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

lemma c03m_aux_fm_target_deriv (p : ℝ) (m : ℕ) (l : ℝ) (hl : 0 < l) :
    HasDerivAt (fun μ : ℝ => (-Complex.I) ^ m * (((descPochhammer ℝ m).eval p * μ ^ (p - m) : ℝ) : ℂ))
      (Complex.I * ((-Complex.I) ^ (m + 1) *
        (((descPochhammer ℝ (m + 1)).eval p * l ^ (p - (m + 1 : ℕ)) : ℝ) : ℂ))) l := by
  have h1 := ((Real.hasDerivAt_rpow_const (x := l) (p := p - m) (Or.inl hl.ne')).const_mul
    ((descPochhammer ℝ m).eval p)).ofReal_comp.const_mul ((-Complex.I) ^ m)
  convert h1 using 1
  rw [descPochhammer_succ_eval, pow_succ]
  have e : p - ((m + 1 : ℕ) : ℝ) = p - m - 1 := by push_cast; ring
  rw [e]
  push_cast
  ring_nf
  rw [Complex.I_sq]; ring

/-- Pointwise limits of the regularised moments. -/
lemma c03m_aux_fm_limit (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ m : ℕ, ∀ l : ℝ, 0 < l → Tendsto (fun η => c03m_aux_fmQ p m η l) (𝓝[>] 0)
      (𝓝 ((-Complex.I) ^ m * (((descPochhammer ℝ m).eval p * l ^ (p - m) : ℝ) : ℂ))) := by
  intro m
  induction m with
  | zero =>
    intro l hl
    have h := c03m_aux_fm_base p hp hp1 l
    rw [((c03c_c03_frac_kernel_formula p hp hp1).2.2.1 l).2, abs_of_pos hl] at h
    simpa using h
  | succ m ih =>
    intro l hl
    obtain ⟨C, hC⟩ := c03m_aux_fm_bound p hp hp1 (m + 2) (by omega) (l / 2) (by positivity)
    have hlim := c03m_aux_deriv_limit (G := fun η => c03m_aux_fmQ p m η)
      (G' := fun η μ => Complex.I * c03m_aux_fmQ p (m + 1) η μ)
      (G'' := fun η μ => Complex.I * (Complex.I * c03m_aux_fmQ p (m + 2) η μ))
      (C := C) (L := 𝓝[>] (0 : ℝ)) (δ₀ := l / 2) (by positivity)
      (fun μ hμ => ih μ (by linarith [hμ.1])) (c03m_aux_fm_target_deriv p m l hl) (by
        filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
        intro μ hμ
        refine ⟨c03m_aux_fmQ_hasDerivAt p hp hp1 m η hη μ,
          (c03m_aux_fmQ_hasDerivAt p hp hp1 (m + 1) η hη μ).const_mul Complex.I, ?_⟩
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
        exact hC η hη μ (by linarith [hμ.1]))
    have := hlim.const_mul (-Complex.I)
    simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul] at this
    exact this

/-- Scaling `z = w/l`: `Q_m(η,l) = l^{p-m} Q_m(η/l², 1)`. -/
lemma c03m_aux_fm_scale (p : ℝ) (m : ℕ) (hm : 1 ≤ m) (η l : ℝ) (hl : 0 < l) :
    c03m_aux_fmQ p m η l = ((l ^ (p - m) : ℝ) : ℂ) * c03m_aux_fmQ p m (η / l ^ 2) 1 := by
  have hm0 : m ≠ 0 := by omega
  set h : ℝ → ℂ := fun w => c03m_aux_fmP m 1 w * Complex.exp (-((η / l ^ 2 * w ^ 2 : ℝ) : ℂ)) /
    ((|w| ^ (1 + p) : ℝ) : ℂ) with hh
  have hpt : ∀ z : ℝ, c03m_aux_fmP m l z * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) /
      ((|z| ^ (1 + p) : ℝ) : ℂ) = ((l ^ (1 + p - m) : ℝ) : ℂ) * h (l * z) := by
    intro z
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have e1 : |l * z| ^ (1 + p) = l ^ (1 + p) * |z| ^ (1 + p) := by
      rw [abs_mul, abs_of_pos hl, Real.mul_rpow hl.le (abs_nonneg z)]
    have e2 : η / l ^ 2 * (l * z) ^ 2 = η * z ^ 2 := by field_simp
    have e3 : (l ^ (1 + p - m) : ℝ) * l ^ m = l ^ (1 + p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hl]; ring_nf
    have e4 : (l ^ (1 + p) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hl _).ne'
    simp only [hh, c03m_aux_fmP, hm0, ite_false, e1, e2]
    push_cast
    have e3' : ((l ^ (1 + p - m) : ℝ) : ℂ) * (l : ℂ) ^ m = ((l ^ (1 + p) : ℝ) : ℂ) := by
      exact_mod_cast e3
    have e4' : ((l ^ (1 + p) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast e4
    have e6 : ((l ^ (1 + p - m) : ℝ) : ℂ) * (l : ℂ) ^ m * (((l ^ (1 + p) : ℝ) : ℂ))⁻¹ = 1 := by
      rw [e3', mul_inv_cancel₀ e4']
    rw [mul_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_one, ← mul_assoc Complex.I]
    linear_combination ((Complex.exp (Complex.I * l * z)) * (z : ℂ) ^ m *
      Complex.exp (-((η : ℂ) * (z : ℂ) ^ 2)) * (((|z| ^ (1 + p) : ℝ) : ℂ))⁻¹) * e6
  unfold c03m_aux_fmQ
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    Measure.integral_comp_mul_left (fun w => h w) l]
  rw [abs_of_pos (inv_pos.2 hl), Complex.real_smul]
  have e5 : (l ^ (1 + p - m) : ℝ) * l⁻¹ = l ^ (p - m) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hl]; ring_nf
  have e5' : ((l ^ (1 + p - m) : ℝ) : ℂ) * ((l⁻¹ : ℝ) : ℂ) = ((l ^ (p - m) : ℝ) : ℂ) := by
    exact_mod_cast e5
  rw [← e5']
  simp only [hh]
  ring

/-- Blueprint: lem:c03_frac_moments.  For `k ≥ 1`, `-c_p ∫^osc e^{iλz} z^k |z|^{-1-p} dz =
(-i)^k m^{(k)}(λ)` (`m(ξ) = ξ^p`), the Gaussian-regularised integrals converging locally uniformly
in `λ ∈ (0,∞)`; and `c_p ∫^osc (1-e^{iλz})|z|^{-1-p} = c_p ∫ (1-e^{iλz})|z|^{-1-p} = λ^p`. -/
theorem c03m_c03_frac_moments (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ lam₁ lam₂ : ℝ, 0 < lam₁ →
      TendstoUniformlyOn
        (fun (η lam : ℝ) => -(c03_cp p : ℂ) * ∫ z : ℝ, Complex.exp (Complex.I * lam * z) *
          (z : ℂ) ^ k * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ))
        (fun lam => (-Complex.I) ^ k * ((iteratedDeriv k (fun ξ : ℝ => ξ ^ p) lam : ℝ) : ℂ))
        (𝓝[>] 0) (Icc lam₁ lam₂)) ∧
    ∀ lam : ℝ, 0 < lam →
      Tendsto (fun η : ℝ => (c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 ((c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) /
          ((|z| ^ (1 + p) : ℝ) : ℂ))) ∧
      (c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) /
          ((|z| ^ (1 + p) : ℝ) : ℂ) = ((lam ^ p : ℝ) : ℂ) := by
  refine ⟨fun k hk lam₁ lam₂ hlam₁ => ?_, fun lam hlam => ⟨?_, ?_⟩⟩
  · have hF : (fun (η lam : ℝ) => -(c03_cp p : ℂ) * ∫ z : ℝ, Complex.exp (Complex.I * lam * z) *
          (z : ℂ) ^ k * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
        fun η lam => c03m_aux_fmQ p k η lam := by
      funext η lam; exact (c03m_aux_fmQ_pos p k hk η lam).symm
    set T : ℂ := (-Complex.I) ^ k * (((descPochhammer ℝ k).eval p * (1 : ℝ) ^ (p - k) : ℝ) : ℂ)
      with hT
    have hG : (fun lam => (-Complex.I) ^ k * ((iteratedDeriv k (fun ξ : ℝ => ξ ^ p) lam : ℝ) : ℂ))
        = fun lam => ((lam ^ (p - k) : ℝ) : ℂ) * T := by
      funext lam
      rw [c03m_aux_fm_iter, hT, Real.one_rpow, mul_one]; push_cast; ring
    rw [hF, hG, Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set M := lam₁ ^ (p - k) with hMdef
    have hM : 0 < M := Real.rpow_pos_of_pos hlam₁ _
    have hlim := c03m_aux_fm_limit p hp hp1 k 1 one_pos
    obtain ⟨δ, hδ, hδb⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim (ε / M) (by positivity)
    filter_upwards [Ioo_mem_nhdsGT (mul_pos hδ (pow_pos hlam₁ 2))] with η hη
    intro lam hlam
    have hl : 0 < lam := hlam₁.trans_le hlam.1
    rw [c03m_aux_fm_scale p k hk η lam hl, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hl _)]
    have hx : η / lam ^ 2 ∈ Ioi (0 : ℝ) := div_pos hη.1 (pow_pos hl 2)
    have hd : dist (η / lam ^ 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx]
      rw [div_lt_iff₀ (pow_pos hl 2)]
      calc η < δ * lam₁ ^ 2 := hη.2
        _ ≤ δ * lam ^ 2 := by gcongr; exact hlam.1
    have h2 := hδb hx hd
    rw [dist_eq_norm, norm_sub_rev] at h2
    have hle : lam ^ (p - k) ≤ M := by
      have : p - (k : ℝ) ≤ 0 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      exact Real.rpow_le_rpow_of_nonpos hlam₁ hlam.1 this
    calc lam ^ (p - k) * ‖T - c03m_aux_fmQ p k (η / lam ^ 2) 1‖
        ≤ M * ‖T - c03m_aux_fmQ p k (η / lam ^ 2) 1‖ := by gcongr
      _ < M * (ε / M) := by
        gcongr
      _ = ε := by field_simp
  · simpa [c03m_aux_fmQ, c03m_aux_fmP] using c03m_aux_fm_base p hp hp1 lam
  · rw [((c03c_c03_frac_kernel_formula p hp hp1).2.2.1 lam).2, abs_of_pos hlam]

/-! ## Taylor formula and its regularised limit -/


/-! ### Reindexing the exponential jet -/

/-- A `Fin n`-indexed family as a function on `ℕ` (zero outside). -/
def c03m_aux_toNat {n : ℕ} (q : Fin n → ℕ) (k : ℕ) : ℕ := if h : k < n then q ⟨k, h⟩ else 0

lemma c03m_aux_toNat_apply {n : ℕ} (q : Fin n → ℕ) (i : Fin n) : c03m_aux_toNat q i.val = q i := by
  simp [c03m_aux_toNat, i.isLt]

lemma c03m_aux_prod_toNat {M : Type*} [CommMonoid M] {n : ℕ} (q : Fin n → ℕ) (g : ℕ → ℕ → M) :
    ∏ i : Fin n, g i.val (q i) = ∏ k ∈ Finset.range n, g k (c03m_aux_toNat q k) := by
  rw [← Fin.prod_univ_eq_prod_range (fun k => g k (c03m_aux_toNat q k))]
  simp only [c03m_aux_toNat_apply]

/-- Extension by zero from `Fin m` to `Fin n`. -/
def c03m_aux_ext {m : ℕ} (n : ℕ) (q : Fin m → ℕ) : Fin n → ℕ := fun i => c03m_aux_toNat q i.val

lemma c03m_aux_toNat_ext {m n : ℕ} (hmn : m ≤ n) (q : Fin m → ℕ) :
    c03m_aux_toNat (c03m_aux_ext n q) = c03m_aux_toNat q := by
  funext k
  simp only [c03m_aux_toNat, c03m_aux_ext]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Products of factors with `g k 0 = 1` only see the support. -/
lemma c03m_aux_prod_range_extend {M : Type*} [CommMonoid M] {m n : ℕ} (hmn : m ≤ n)
    (Q : ℕ → ℕ) (hQ : ∀ k, m ≤ k → Q k = 0) (g : ℕ → ℕ → M) (hg : ∀ k, g k 0 = 1) :
    ∏ k ∈ Finset.range n, g k (Q k) = ∏ k ∈ Finset.range m, g k (Q k) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [Finset.prod_range_add]
  have : ∏ x ∈ Finset.range d, g (m + x) (Q (m + x)) = 1 :=
    Finset.prod_eq_one fun x _ => by rw [hQ (m + x) (by omega), hg]
  rw [this, mul_one]

lemma c03m_aux_sum_range_extend {m n : ℕ} (hmn : m ≤ n) (Q : ℕ → ℕ) (hQ : ∀ k, m ≤ k → Q k = 0) :
    ∑ k ∈ Finset.range n, (k + 1) * Q k = ∑ k ∈ Finset.range m, (k + 1) * Q k := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [Finset.sum_range_add]
  have : ∑ x ∈ Finset.range d, (m + x + 1) * Q (m + x) = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [hQ (m + x) (by omega), mul_zero]
  rw [this, add_zero]

lemma c03m_aux_sum_toNat {n : ℕ} (q : Fin n → ℕ) :
    ∑ i : Fin n, (i.val + 1) * q i = ∑ k ∈ Finset.range n, (k + 1) * c03m_aux_toNat q k := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (k + 1) * c03m_aux_toNat q k)]
  simp only [c03m_aux_toNat_apply]

/-- If `∑ (i+1) q_i = m` then `q_k = 0` for `k ≥ m`, and `q_k ≤ m`. -/
lemma c03m_aux_toNat_bound {n m : ℕ} (q : Fin n → ℕ) (hq : ∑ i : Fin n, (i.val + 1) * q i = m) :
    ∀ k, (k + 1) * c03m_aux_toNat q k ≤ m := by
  intro k
  by_cases hk : k < n
  · rw [← hq]
    have := Finset.single_le_sum (f := fun i : Fin n => (i.val + 1) * q i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨k, hk⟩ : Fin n))
    simpa [c03m_aux_toNat, hk] using this
  · simp [c03m_aux_toNat, hk]

lemma c03m_aux_toNat_zero {n m : ℕ} (q : Fin n → ℕ) (hq : ∑ i : Fin n, (i.val + 1) * q i = m) :
    ∀ k, m ≤ k → c03m_aux_toNat q k = 0 := by
  intro k hk
  have := c03m_aux_toNat_bound q hq k
  by_contra h
  have : (k + 1) * 1 ≤ (k + 1) * c03m_aux_toNat q k := Nat.mul_le_mul_left _ (by omega)
  omega

/-- Reindexing sums over partitions from `Fin m` to `Fin n` (`m ≤ n < B`). -/
lemma c03m_aux_reindex {M : Type*} [AddCommMonoid M] {m n B : ℕ} (hmn : m ≤ n) (hB : n < B)
    (G : (ℕ → ℕ) → M) :
    ∑ q ∈ (Fintype.piFinset fun _ : Fin m => Finset.range (m + 1)).filter
        (fun q => ∑ i, (i.val + 1) * q i = m), G (c03m_aux_toNat q) =
      ∑ q ∈ (Fintype.piFinset fun _ : Fin n => Finset.range B).filter
        (fun q => ∑ i, (i.val + 1) * q i = m), G (c03m_aux_toNat q) := by
  refine Finset.sum_nbij' (c03m_aux_ext n) (fun q i => c03m_aux_toNat q i.val) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hq ⊢
    have hsum := hq.2
    refine ⟨fun i => ?_, ?_⟩
    · have := c03m_aux_toNat_bound q hsum i.val
      simp only [c03m_aux_ext]
      nlinarith
    · rw [c03m_aux_sum_toNat, c03m_aux_toNat_ext hmn,
        c03m_aux_sum_range_extend hmn _ (c03m_aux_toNat_zero q hsum), ← c03m_aux_sum_toNat, hsum]
  · intro q hq
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hq ⊢
    have hsum := hq.2
    have hz := c03m_aux_toNat_zero q hsum
    refine ⟨fun i => ?_, ?_⟩
    · have := c03m_aux_toNat_bound q hsum i.val
      nlinarith
    · have e : c03m_aux_toNat (fun i : Fin m => c03m_aux_toNat q i.val) = c03m_aux_toNat q := by
        funext k
        by_cases hk : k < m
        · have hkn : k < n := lt_of_lt_of_le hk hmn
          simp [c03m_aux_toNat, hk, hkn]
        · rw [hz k (by omega)]; simp [c03m_aux_toNat, hk]
      rw [c03m_aux_sum_toNat, e, ← c03m_aux_sum_range_extend hmn _ hz, ← c03m_aux_sum_toNat, hsum]
  · intro q _
    funext i
    have h1 : i.val < n := lt_of_lt_of_le i.isLt hmn
    simp [c03m_aux_ext, c03m_aux_toNat, h1, i.isLt]
  · intro q hq
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hq
    have hz := c03m_aux_toNat_zero q hq.2
    funext i
    by_cases hi : i.val < m
    · simp [c03m_aux_ext, c03m_aux_toNat, hi, i.isLt]
    · have := hz i.val (by omega)
      simp only [c03m_aux_toNat, i.isLt, ↓reduceDIte] at this
      simp [c03m_aux_ext, c03m_aux_toNat, hi, this]
  · intro q _
    rw [c03m_aux_toNat_ext hmn]

/-- A function on `ℝ` that is smooth on an open set `O` and vanishes near every point outside
`O` is smooth. -/
lemma c03m_aux_smooth_of_local {O : Set ℝ} (hO : IsOpen O) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f O) (h0 : ∀ x ∉ O, f =ᶠ[𝓝 x] fun _ => 0) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ O
  · exact hf.contDiffAt (hO.mem_nhds hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (h0 x hx)

/-- Leibniz expansion of the jets of `F_y` on the phase interval. -/
lemma c03m_aux_F_jet {Y : ℝ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (y x : ℝ)
    (hx : y + x ∈ Ioo (Y / 4) (4 * Y)) (m : ℕ) :
    iteratedDeriv m (c03_mult_F Y a Ψ y) x = ∑ r ∈ Finset.range (m + 1), (m.choose r : ℂ) *
      iteratedDeriv r a (y + x) * (Complex.exp (Complex.I * (c03_mult_Theta Ψ y x : ℂ)) *
        c03c_expJet (c03_mult_Theta Ψ y) (m - r) x) := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  set Uy : Set ℝ := {w | y + w ∈ U} with hUy
  have hUyo : IsOpen Uy := isOpen_Ioo.preimage (by fun_prop)
  have hΘ : ContDiffOn ℝ (⊤ : ℕ∞) (c03_mult_Theta Ψ y) Uy := by
    have e : c03_mult_Theta Ψ y = fun w => Ψ (y + w) - Ψ y - deriv Ψ y * w := by
      funext w; simp [c03_mult_Theta]
    rw [e]
    exact ((hΨ.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ => y + w).contDiffOn
      (fun w hw => hw)).sub contDiffOn_const).sub (contDiffOn_const.mul contDiffOn_id)
  obtain ⟨hJ, -, -⟩ := c03_exp_jet_recursion Uy hUyo _ hΘ
  have hev : c03_mult_F Y a Ψ y =ᶠ[𝓝 x] (fun w => a (y + w)) *
      fun w => Complex.exp (Complex.I * (c03_mult_Theta Ψ y w : ℂ)) := by
    filter_upwards [hUyo.mem_nhds hx] with w hw
    simp only [c03_mult_F, Pi.mul_apply]
    exact if_pos hw
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w => Complex.exp (Complex.I * (c03_mult_Theta Ψ y w : ℂ))) Uy :=
    Complex.contDiff_exp.comp_contDiffOn
      (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hΘ))
  have h1 : ContDiffAt ℝ m (fun w => a (y + w)) x :=
    ((ha.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ => y + w)).contDiffAt).of_le
      (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ m (fun w => Complex.exp (Complex.I * (c03_mult_Theta Ψ y w : ℂ))) x :=
    (hE.contDiffAt (hUyo.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  rw [hev.iteratedDeriv_eq, iteratedDeriv_mul h1 h2]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [iteratedDeriv_comp_const_add, (hJ (m - r)).2 x hx]

/-- The jet of `F_y` of order `2N-1` in terms of the Taylor index set. -/
lemma c03m_aux_F_jet_index {Y : ℝ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (N : ℕ) (hN : 1 ≤ N) (y x : ℝ)
    (hx : y + x ∈ Ioo (Y / 4) (4 * Y)) :
    iteratedDeriv (2 * N - 1) (c03_mult_F Y a Ψ y) x = ((2 * N - 1).factorial : ℂ) *
      ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
        (iteratedDeriv rq.1 a (y + x) * Complex.exp (Complex.I * (c03_mult_Theta Ψ y x : ℂ)) *
          ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) x : ℝ) : ℂ) ^ rq.2 i) := by
  set n := 2 * N - 1 with hn
  have hn2 : 2 * N = n + 1 := by omega
  set Θ := c03_mult_Theta Ψ y with hΘ_def
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  set Uy : Set ℝ := {w | y + w ∈ U} with hUy
  have hUyo : IsOpen Uy := isOpen_Ioo.preimage (by fun_prop)
  have hΘs : ContDiffOn ℝ (⊤ : ℕ∞) Θ Uy := by
    have e : Θ = fun w => Ψ (y + w) - Ψ y - deriv Ψ y * w := by
      funext w; simp [hΘ_def, c03_mult_Theta]
    rw [e]
    exact ((hΨ.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ => y + w).contDiffOn
      (fun w hw => hw)).sub contDiffOn_const).sub (contDiffOn_const.mul contDiffOn_id)
  set g : ℕ → ℕ → ℂ := fun k j => Complex.I ^ j / ((j.factorial : ℂ) * ((k + 1).factorial : ℂ) ^ j) *
    ((iteratedDeriv (k + 1) Θ x : ℝ) : ℂ) ^ j with hg
  have hg0 : ∀ k, g k 0 = 1 := fun k => by simp [hg]
  set P : (ℕ → ℕ) → ℂ := fun Q => ∏ k ∈ Finset.range n, g k (Q k) with hP
  set T : ℕ → Finset (Fin n → ℕ) := fun m =>
    (Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).filter
      (fun q => ∑ i, (i.val + 1) * q i = m) with hT
  -- (a) the coefficient form
  have hcoef : ∀ (r : ℕ) (q : Fin n → ℕ), c03_mult_coeff r q *
      ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ q i =
        ((r.factorial : ℂ))⁻¹ * P (c03m_aux_toNat q) := by
    intro r q
    simp only [hP]
    rw [← c03m_aux_prod_toNat q g]
    simp only [c03_mult_coeff, hg]
    rw [← Finset.prod_pow_eq_pow_sum, mul_comm ((r.factorial : ℂ)), div_mul_eq_div_div,
      div_eq_mul_inv _ ((r.factorial : ℂ)), ← Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  -- (b) the jet coefficients in the `Fin n` indexing
  have hjet : ∀ m ≤ n, c03c_expJet Θ m x = (m.factorial : ℂ) * ∑ q ∈ T m, P (c03m_aux_toNat q) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      have hT0 : T 0 = {fun _ => 0} := by
        ext q
        simp only [hT, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
          Finset.mem_singleton]
        constructor
        · rintro ⟨-, hq⟩
          funext i
          have := Finset.sum_eq_zero_iff.1 hq i (Finset.mem_univ _)
          simpa using this
        · rintro rfl
          simp
      rw [hT0, Finset.sum_singleton]
      have hP0 : P (c03m_aux_toNat (fun _ : Fin n => 0)) = 1 := by
        simp only [hP]
        exact Finset.prod_eq_one fun k _ => by simp [c03m_aux_toNat, hg0]
      simp [hP0, c03c_expJet]
    · have hc := c03_exp_jet_coefficients Uy hUyo Θ hΘs m hpos x hx
      rw [hc]
      congr 1
      rw [← c03m_aux_reindex (G := P) hm (show n < n + 1 by omega)]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [hP]
      rw [c03m_aux_prod_range_extend (show m ≤ n from hm) _ (fun k hk => by
        simp [c03m_aux_toNat, show ¬ k < m by omega]) g hg0, ← c03m_aux_prod_toNat q g]
      simp only [hg]
      rw [← Finset.prod_pow_eq_pow_sum, Nat.cast_prod, ← Finset.prod_div_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      push_cast
      ring
  -- (c) the Leibniz expansion
  rw [c03m_aux_F_jet ha hΨ y x hx n]
  -- (d) rewrite the right side
  have hRHS : ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
      (iteratedDeriv rq.1 a (y + x) * Complex.exp (Complex.I * (Θ x : ℂ)) *
        ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ rq.2 i) =
      ∑ r ∈ Finset.range (n + 1), ∑ q ∈ T (n - r), ((r.factorial : ℂ))⁻¹ *
        (iteratedDeriv r a (y + x) * Complex.exp (Complex.I * (Θ x : ℂ))) *
          P (c03m_aux_toNat q) := by
    simp only [c03_mult_index, Finset.sum_filter]
    rw [Finset.sum_product, hn2]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    simp only [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hiff : (r + ∑ i, (i.val + 1) * q i = n + 1 - 1) ↔ (∑ i, (i.val + 1) * q i = n - r) := by
      constructor <;> intro h <;> omega
    split_ifs with h1 h2 h2
    · have := hcoef r q
      calc c03_mult_coeff r q * (iteratedDeriv r a (y + x) * Complex.exp (Complex.I * (Θ x : ℂ)) *
            ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ q i)
          = (c03_mult_coeff r q * ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ q i) *
            (iteratedDeriv r a (y + x) * Complex.exp (Complex.I * (Θ x : ℂ))) := by ring
        _ = _ := by erw [this]; ring
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  rw [hRHS, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  rw [hjet (n - r) (Nat.sub_le _ _)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hch : (n.choose r : ℂ) * ((n - r).factorial : ℂ) = (n.factorial : ℂ) * ((r.factorial : ℂ))⁻¹ := by
    have h1 : n.choose r * (n - r).factorial * r.factorial = n.factorial := by
      rw [mul_right_comm]; exact Nat.choose_mul_factorial_mul_factorial hr'
    have hr0 : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
    rw [eq_mul_inv_iff_mul_eq₀ hr0]
    exact_mod_cast h1
  calc (n.choose r : ℂ) * iteratedDeriv r a (y + x) * (Complex.exp (Complex.I * (Θ x : ℂ)) *
        (((n - r).factorial : ℂ) * P (c03m_aux_toNat q)))
      = ((n.choose r : ℂ) * ((n - r).factorial : ℂ)) * (iteratedDeriv r a (y + x) *
          Complex.exp (Complex.I * (Θ x : ℂ))) * P (c03m_aux_toNat q) := by ring
    _ = _ := by rw [hch]; ring

/-- Blueprint: lem:c03_mult_taylor_formula.  Integral Taylor remainder with explicit amplitude and
phase factors: with `n = 2N-1`, `R_n(z) = n ∑_{(r,q)} d_{r,q} ∫₀¹ (1-t)^{n-1} e^{iΘ_y(tz)} b_t(z) dt`,
each `t`-integral converging absolutely.
Encoding: stated for `Y/2 < y < 3Y` (contains `[Y,2Y]`). -/
theorem c03_mult_taylor_formula (Y : ℝ) (hY : 1 ≤ Y) (a : ℝ → ℂ) (Ψ : ℝ → ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y))
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (hlam : ∀ y ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ y) (N : ℕ) (hN : 1 ≤ N)
    (y : ℝ) (hy : y ∈ Ioo (Y / 2) (3 * Y)) (z : ℝ) :
    (∀ rq ∈ c03_mult_index N, IntervalIntegrable (fun t : ℝ =>
        (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (c03_mult_Theta Ψ y (t * z) : ℂ)) *
          c03_mult_bt Y a Ψ N rq.1 rq.2 y t z) volume 0 1) ∧
    c03_mult_taylorR Y a Ψ N y z =
      ((2 * N - 1 : ℕ) : ℂ) * ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
        ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (c03_mult_Theta Ψ y (t * z) : ℂ)) *
          c03_mult_bt Y a Ψ N rq.1 rq.2 y t z := by
  set n := 2 * N - 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 * N - 2 = n - 1 := by omega
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  set Uy : Set ℝ := {w | y + w ∈ U} with hUy
  have hUyo : IsOpen Uy := isOpen_Ioo.preimage (by fun_prop)
  set Θ := c03_mult_Theta Ψ y with hΘ_def
  have hΘs : ContDiffOn ℝ (⊤ : ℕ∞) Θ Uy := by
    have e : Θ = fun w => Ψ (y + w) - Ψ y - deriv Ψ y * w := by
      funext w; simp [hΘ_def, c03_mult_Theta]
    rw [e]
    exact ((hΨ.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ => y + w).contDiffOn
      (fun w hw => hw)).sub contDiffOn_const).sub (contDiffOn_const.mul contDiffOn_id)
  obtain ⟨hFs, -⟩ := c03m_aux_F_smooth ha has hΨ y
  set F := c03_mult_F Y a Ψ y with hF_def
  -- the localized summands
  set h : ℕ × (Fin n → ℕ) → ℝ → ℂ := fun rq x => if y + x ∈ U then
    iteratedDeriv rq.1 a (y + x) * Complex.exp (Complex.I * (Θ x : ℂ)) *
      ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ rq.2 i else 0 with hh
  have hzero : ∀ (f : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ U → ∀ x, y + x ∉ U →
      ∀ᶠ x' in 𝓝 x, f (y + x') = 0 := by
    intro f hf hfs x hx
    have h0 : f =ᶠ[𝓝 (y + x)] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hfs h))
    exact ((continuous_const.add continuous_id).tendsto x).eventually h0
  have hhc : ∀ rq : ℕ × (Fin n → ℕ), Continuous (h rq) := by
    intro rq
    have hA : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv rq.1 a) := by
      rw [iteratedDeriv_eq_iterate]; exact ha.iterate_deriv _
    have hAs : tsupport (iteratedDeriv rq.1 a) ⊆ U :=
      (c03m_aux_tsupport_iteratedDeriv a rq.1).trans has
    refine (c03m_aux_smooth_of_local hUyo ?_ ?_).continuous
    · have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iteratedDeriv rq.1 a (y + x) *
          Complex.exp (Complex.I * (Θ x : ℂ)) *
            ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ rq.2 i) Uy := by
        refine ((hA.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ => y + w)).contDiffOn.mul
          (Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul
            (Complex.ofRealCLM.contDiff.comp_contDiffOn hΘs)))).mul ?_
        exact contDiffOn_prod fun i _ => (Complex.ofRealCLM.contDiff.comp_contDiffOn
          (c03m_aux_iteratedDeriv_contDiffOn hUyo hΘs (i.val + 1))).pow _
      exact h1.congr fun x hx => by simp only [hh]; exact if_pos hx
    · intro x hx
      filter_upwards [hzero _ hA hAs x hx] with x' hx'
      simp only [hh]
      split_ifs
      · rw [hx']; ring
      · rfl
  -- the jet at every point
  have hjet : ∀ x, iteratedDeriv n F x = (n.factorial : ℂ) *
      ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 * h rq x := by
    intro x
    by_cases hx : y + x ∈ U
    · rw [hF_def, c03m_aux_F_jet_index ha hΨ N hN y x hx]
      congr 1
      refine Finset.sum_congr rfl fun rq _ => ?_
      simp only [hh]
      rw [if_pos hx]
    · have hev : F =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hzero a ha has x hx] with x' hx'
        simp only [hF_def, c03_mult_F]
        split_ifs
        · rw [hx', zero_mul]
        · rfl
      rw [hev.iteratedDeriv_eq]
      have : ∀ rq : ℕ × (Fin n → ℕ), h rq x = 0 := fun rq => by simp only [hh]; exact if_neg hx
      simp [this, iteratedDeriv_const]
  -- the integrand
  have hint : ∀ rq : ℕ × (Fin n → ℕ), ∀ t : ℝ, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (Θ (t * z) : ℂ)) * c03_mult_bt Y a Ψ N rq.1 rq.2 y t z =
      (((1 - t) ^ (n - 1) : ℝ) : ℂ) * ((z : ℂ) ^ n * h rq (t * z)) := by
    intro rq t
    rw [hn2]
    simp only [c03_mult_bt, hh, hΘ_def]
    split_ifs <;> ring
  have hii : ∀ rq : ℕ × (Fin n → ℕ), IntervalIntegrable (fun t : ℝ =>
      (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (Θ (t * z) : ℂ)) *
        c03_mult_bt Y a Ψ N rq.1 rq.2 y t z) volume 0 1 := by
    intro rq
    simp_rw [hint rq]
    exact (((Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).pow _))).mul
      (continuous_const.mul ((hhc rq).comp (continuous_id.mul continuous_const)))).intervalIntegrable
      _ _
  refine ⟨fun rq _ => hii rq, ?_⟩
  -- the case `z = 0`
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : ∀ rq : ℕ × (Fin n → ℕ), ∀ t : ℝ, c03_mult_bt Y a Ψ N rq.1 rq.2 y t 0 = 0 := by
      intro rq t
      simp only [c03_mult_bt]
      split_ifs
      · rw [Complex.ofReal_zero, zero_pow (by omega)]; ring
      · rfl
    simp only [h0, mul_zero, intervalIntegral.integral_zero]
    simp only [c03_mult_taylorR]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; simp [zero_pow hk]
    · intro h; simp at h; omega
  -- Taylor's formula with integral remainder
  have hT := taylor_integral_remainder (f := F) (x₀ := 0) (x := z) (n := n - 1)
    (hFs.contDiffOn.of_le (WithTop.coe_le_coe.2 le_top))
  have hU2 : UniqueDiffOn ℝ (uIcc 0 z) := uniqueDiffOn_uIcc hz.symm
  have hwd : ∀ k, ∀ s ∈ uIcc 0 z, iteratedDerivWithin k F (uIcc 0 z) s = iteratedDeriv k F s :=
    fun k s hs => iteratedDerivWithin_eq_iteratedDeriv hU2
      (hFs.contDiffAt.of_le (by exact_mod_cast le_top)) hs
  rw [taylor_within_apply, show n - 1 + 1 = n by omega] at hT
  have hR : c03_mult_taylorR Y a Ψ N y z = ∫ s in (0 : ℝ)..z,
      (((z - s) ^ (n - 1) / ((n - 1).factorial : ℝ) : ℝ) : ℂ) * iteratedDeriv n F s := by
    have e1 : c03_mult_taylorR Y a Ψ N y z = F z - ∑ k ∈ Finset.range n,
        (((k.factorial : ℝ)⁻¹ * (z - 0) ^ k : ℝ) : ℂ) * iteratedDerivWithin k F (uIcc 0 z) 0 := by
      simp only [c03_mult_taylorR, hF_def]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hwd k 0 left_mem_uIcc]
      push_cast; ring
    rw [e1]
    simp only [← Complex.real_smul] at hT ⊢
    rw [hT]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [hwd n s hs]
  rw [hR]
  -- change of variables `s = t z`
  have hcv := intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := 1)
    (fun s => (((z - s) ^ (n - 1) / ((n - 1).factorial : ℝ) : ℝ) : ℂ) * iteratedDeriv n F s) hz
  simp only [zero_mul, one_mul] at hcv
  rw [show (∫ s in (0 : ℝ)..z, (((z - s) ^ (n - 1) / ((n - 1).factorial : ℝ) : ℝ) : ℂ) *
      iteratedDeriv n F s) = z • ∫ t in (0 : ℝ)..1, (((z - t * z) ^ (n - 1) /
        ((n - 1).factorial : ℝ) : ℝ) : ℂ) * iteratedDeriv n F (t * z) by
    rw [hcv, smul_smul, mul_inv_cancel₀ hz, one_smul]]
  simp_rw [hjet]
  have hii' : ∀ rq ∈ c03_mult_index N, IntervalIntegrable (fun t : ℝ =>
      (((1 - t) ^ (n - 1) : ℝ) : ℂ) * ((z : ℂ) ^ n * h rq (t * z))) volume 0 1 := by
    intro rq _
    exact (((Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).pow _))).mul
      (continuous_const.mul ((hhc rq).comp (continuous_id.mul continuous_const)))).intervalIntegrable
      _ _
  have hzc : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  have hrw : ∀ t : ℝ, (((z - t * z) ^ (n - 1) / ((n - 1).factorial : ℝ) : ℝ) : ℂ) *
      ((n.factorial : ℂ) * ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 * h rq (t * z)) =
      (z : ℂ)⁻¹ * ((n : ℂ) * ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
        ((((1 - t) ^ (n - 1) : ℝ) : ℂ) * ((z : ℂ) ^ n * h rq (t * z)))) := by
    intro t
    have hf : (n.factorial : ℂ) = n * ((n - 1).factorial : ℂ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
    have hf0 : ((n - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hzn : (z : ℂ) ^ n = (z : ℂ) ^ (n - 1) * z := by
      rw [← pow_succ, show n - 1 + 1 = n by omega]
    rw [hf, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun rq _ => ?_
    push_cast
    rw [show (z : ℂ) - t * z = (1 - t) * z by ring, mul_pow, hzn]
    field_simp
  simp_rw [hrw, hint]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun rq hrq => (hii' rq hrq).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hzc, one_mul]

/-- Blueprint: lem:c03_mult_taylor_regularized_limit.  For `η > 0` the regularized integrand
`e^{iλz - ηz²} R_{2N-1}(z) |z|^{-1-p}` is integrable, and
`lim_{η↓0} -c_p ∫ e^{iλz-ηz²} R_{2N-1}(z) |z|^{-1-p} dz = ℛ_{mult,N}(y)`.
Encoding: stated for `Y/2 < y < 3Y` (contains `[Y,2Y]`). -/
theorem c03_mult_taylor_regularized_limit (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Y : ℝ)
    (hY : 1 ≤ Y) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (hlam : ∀ y ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ y) (N : ℕ) (hN : 1 ≤ N)
    (y : ℝ) (hy : y ∈ Ioo (Y / 2) (3 * Y)) :
    (∀ η : ℝ, 0 < η → Integrable (fun z : ℝ =>
      Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) * c03_mult_taylorR Y a Ψ N y z *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ))) ∧
    Tendsto (fun η : ℝ => -(c03_cp p : ℂ) * ∫ z : ℝ,
        Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) * c03_mult_taylorR Y a Ψ N y z *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (c03_mult_R p Y a Ψ N y)) := by
  have hyU : y ∈ Ioo (Y / 4) (4 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨-, -, hF0, -, hbase, hid⟩ :=
    c03_mult_kernel_identity p hp hp1 Y hY a Ψ ha has hΨ hlam y hy
  set l := deriv Ψ y with hl_def
  have hl : 0 < l := hlam y hyU
  set F := c03_mult_F Y a Ψ y
  set c : ℕ → ℂ := fun k => iteratedDeriv k F 0 / (Nat.factorial k : ℂ)
  set e : ℝ → ℂ := fun z => Complex.exp (Complex.I * (l : ℂ) * z)
  set G : ℝ → ℝ → ℂ := fun η z => Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))
  set D : ℝ → ℂ := fun z => ((|z| ^ (1 + p) : ℝ) : ℂ)
  set base : ℝ → ℂ := fun z => e z * (F z - a y) / D z
  set mom : ℕ → ℝ → ℝ → ℂ := fun k η z => e z * (z : ℂ) ^ k * G η z / D z
  have hR : ∀ z, c03_mult_taylorR Y a Ψ N y z =
      (F z - a y) - ∑ k ∈ Finset.range (2 * N - 2), c (k + 1) * (z : ℂ) ^ (k + 1) := by
    intro z
    unfold c03_mult_taylorR
    rw [show 2 * N - 1 = (2 * N - 2) + 1 by omega, Finset.sum_range_succ']
    simp only [c, F, iteratedDeriv_zero, hF0, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_zero, mul_one]
    ring
  have hint : ∀ η z, e z * c03_mult_taylorR Y a Ψ N y z * G η z / D z =
      base z * G η z - ∑ k ∈ Finset.range (2 * N - 2), c (k + 1) * mom (k + 1) η z := by
    intro η z
    rw [hR z, mul_sub, sub_mul, sub_div, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    congr 1
    · simp only [base]; ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mom]; ring
  have hGc : ∀ η, Continuous (G η) := fun η => by fun_prop
  have hbaseG : ∀ η, 0 ≤ η → Integrable (fun z => base z * G η z) := fun η hη =>
    hbase.mul_bdd (hGc η).aestronglyMeasurable (Eventually.of_forall fun z => c03m_aux_gauss_le η z hη)
  have hmom : ∀ η, 0 < η → ∀ k ∈ Finset.range (2 * N - 2),
      Integrable (fun z => c (k + 1) * mom (k + 1) η z) := fun η hη k _ =>
    (c03m_aux_moment_integrable hp hp1 l η hη (k + 1) (by omega)).const_mul _
  have hsplit : ∀ η, 0 < η → ∫ z, e z * c03_mult_taylorR Y a Ψ N y z * G η z / D z =
      (∫ z, base z * G η z) - ∑ k ∈ Finset.range (2 * N - 2), c (k + 1) * ∫ z, mom (k + 1) η z := by
    intro η hη
    simp_rw [hint]
    rw [integral_sub (hbaseG η hη.le) (integrable_finsetSum _ (hmom η hη)),
      integral_finsetSum _ (hmom η hη)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    exact integral_const_mul _ _
  refine ⟨fun η hη => ?_, ?_⟩
  · have : (fun z => e z * c03_mult_taylorR Y a Ψ N y z * G η z / D z) =
        fun z => base z * G η z - ∑ k ∈ Finset.range (2 * N - 2), c (k + 1) * mom (k + 1) η z :=
      funext (hint η)
    rw [this]
    exact (hbaseG η hη.le).sub (integrable_finsetSum _ (hmom η hη))
  -- limits
  have hlim1 : Tendsto (fun η => ∫ z, base z * G η z) (𝓝[>] 0) (𝓝 (∫ z, base z)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖base z‖) ?_ ?_ hbase.norm ?_
    · exact Eventually.of_forall fun η => (hbase.aestronglyMeasurable.mul (hGc η).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with η hη
      refine Eventually.of_forall fun z => ?_
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (c03m_aux_gauss_le η z (le_of_lt hη))
    · refine Eventually.of_forall fun z => ?_
      have : Tendsto (fun η : ℝ => G η z) (𝓝[>] 0) (𝓝 (G 0 z)) :=
        ((by fun_prop : Continuous fun η : ℝ => G η z).tendsto 0).mono_left nhdsWithin_le_nhds
      simpa [G] using this.const_mul (base z)
  have hmomlim : ∀ k : ℕ, Tendsto (fun η => -(c03_cp p : ℂ) * ∫ z, mom (k + 1) η z) (𝓝[>] 0)
      (𝓝 ((-Complex.I) ^ (k + 1) * ((iteratedDeriv (k + 1) (fun ξ : ℝ => ξ ^ p) l : ℝ) : ℂ))) := by
    intro k
    have hu := (c03m_c03_frac_moments p hp hp1).1 (k + 1) (by omega) l l hl
    exact hu.tendsto_at ⟨le_rfl, le_rfl⟩
  have hfinal := ((hlim1.const_mul (-(c03_cp p : ℂ))).sub
    (tendsto_finsetSum (Finset.range (2 * N - 2)) fun k _ => (hmomlim k).const_mul (c (k + 1))))
  have hev : (fun η : ℝ => -(c03_cp p : ℂ) * ∫ z : ℝ,
        Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) * c03_mult_taylorR Y a Ψ N y z *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      fun η => -(c03_cp p : ℂ) * (∫ z, base z * G η z) -
        ∑ k ∈ Finset.range (2 * N - 2), c (k + 1) * (-(c03_cp p : ℂ) * ∫ z, mom (k + 1) η z) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have := hsplit η hη
    simp only [e, G, D] at this
    rw [this, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  refine Tendsto.congr' hev.symm (hfinal.trans_eq ?_) |>.mono_left le_rfl
  -- identify the limit
  have hbase_eq : -(c03_cp p : ℂ) * ∫ z, base z = Complex.exp (-(Complex.I * (Ψ y : ℂ))) *
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y -
        ((l ^ p : ℝ) : ℂ) * a y := by
    rw [hid]
  rw [hbase_eq]
  unfold c03_mult_R c03_mult_B
  rw [show 2 * N - 1 = (2 * N - 2) + 1 by omega, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, iteratedDeriv_zero]
  have hF0' : c03_mult_F Y a Ψ y 0 = a y := hF0
  rw [hF0', ← hl_def]
  congr 1
  have hs : ∑ k ∈ Finset.range (2 * N - 2),
      c (k + 1) * ((-Complex.I) ^ (k + 1) * ((iteratedDeriv (k + 1) (fun ξ : ℝ => ξ ^ p) l : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (2 * N - 2), (-Complex.I) ^ (k + 1) / ((k + 1).factorial : ℂ) *
        ((iteratedDeriv (k + 1) (fun ξ : ℝ => ξ ^ p) l : ℝ) : ℂ) *
        iteratedDeriv (k + 1) (c03_mult_F Y a Ψ y) 0 :=
    Finset.sum_congr rfl fun k _ => by simp only [c, F]; ring
  rw [hs]; ring


/-! ### Commuting `y`- and `z`-derivatives; the differentiated-amplitude recursion -/

lemma c03m_aux_pd_add (v : ℝ × ℝ) (G : ℝ × ℝ → ℂ) (m : ℕ) :
    ∀ n, c03m_aux_pd v (c03m_aux_pd v G m) n = c03m_aux_pd v G (m + n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext q
    simp only [c03m_aux_pd, ih]
    rfl

/-- Symmetry of second directional derivatives. -/
lemma c03m_aux_pd_symm2 {W : Set (ℝ × ℝ)} (hW : IsOpen W) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) (u v : ℝ × ℝ) {q : ℝ × ℝ} (hq : q ∈ W) :
    c03m_aux_pd v (c03m_aux_pd u H 1) 1 q = c03m_aux_pd u (c03m_aux_pd v H 1) 1 q := by
  have hfx : ContDiffAt ℝ (⊤ : ℕ∞) H q := hH.contDiffAt (hW.mem_nhds hq)
  have h2 : DifferentiableAt ℝ (fderiv ℝ H) q := by
    have : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ H) q :=
      hfx.fderiv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_rfl)
    exact this.differentiableAt (by simp)
  have hsymm := hfx.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  show fderiv ℝ (fun z => fderiv ℝ H z u) q v = fderiv ℝ (fun z => fderiv ℝ H z v) q u
  rw [fderiv_clm_apply h2 (differentiableAt_const _), fderiv_clm_apply h2 (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hsymm v u

/-- One `u`-derivative commutes with `b` `v`-derivatives. -/
lemma c03m_aux_pd_comm {W : Set (ℝ × ℝ)} (hW : IsOpen W) {H : ℝ × ℝ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) (u v : ℝ × ℝ) :
    ∀ b, ∀ q ∈ W, c03m_aux_pd v (c03m_aux_pd u H 1) b q = c03m_aux_pd u (c03m_aux_pd v H b) 1 q := by
  intro b
  induction b with
  | zero => intro q _; rfl
  | succ b ih =>
    intro q hq
    have e1 : c03m_aux_pd v (c03m_aux_pd u H 1) (b + 1) =
        c03m_aux_pd v (c03m_aux_pd v (c03m_aux_pd u H 1) b) 1 := rfl
    rw [e1, c03m_aux_pd_congr hW v ih 1 q hq,
      c03m_aux_pd_symm2 hW (c03m_aux_pd_smooth hW v hH b) u v hq]
    rfl

/-- `∂_z^b ∂_y` and `∂_y ∂_z^b` agree: mixed derivatives of `∂_y F`. -/
lemma c03m_aux_M_dy {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (a b : ℕ) {y z : ℝ} (hq : (y, z) ∈ W) :
    c03m_aux_M (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) F 1) a b y z = c03m_aux_M F (a + 1) b y z := by
  have hF1 := c03m_aux_pd_smooth hW ((1 : ℝ), (0 : ℝ)) hF 1
  rw [c03m_aux_M_eq hW hF1 a b hq, c03m_aux_M_eq hW hF (a + 1) b hq,
    c03m_aux_pd_congr hW _ (c03m_aux_pd_comm hW hF _ _ b) a (y, z) hq, c03m_aux_pd_add,
    add_comm 1 a]

lemma c03m_aux_SB_dy {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) {y z : ℝ} (hq : (y, z) ∈ W) {J S : ℕ} {c M α β : ℝ}
    (h : c03m_aux_SB F y z (J + 1) S c M α β) :
    c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) F 1) y z J S c (M * α) α β := by
  intro a ha b hb
  rw [c03m_aux_M_dy hW hF a b hq]
  refine (h (a + 1) (by omega) b hb).trans (le_of_eq ?_)
  ring

lemma c03m_aux_SB_const_mul {F : ℝ × ℝ → ℂ} {y z : ℝ} {J S : ℕ} {c M α β : ℝ} (k : ℂ)
    (hk : ‖k‖ ≤ 1) (hX : ∀ a ≤ J, ∀ b ≤ S, 0 ≤ c * M * α ^ a * β ^ b)
    (h : c03m_aux_SB F y z J S c M α β) : c03m_aux_SB (fun w => k * F w) y z J S c M α β := by
  intro a ha b hb
  rw [c03m_aux_M_const_mul, norm_mul]
  calc ‖k‖ * ‖c03m_aux_M F a b y z‖ ≤ 1 * (c * M * α ^ a * β ^ b) :=
        mul_le_mul hk (h a ha b hb) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma c03m_aux_SB_monoJ {F : ℝ × ℝ → ℂ} {y z : ℝ} {J J' S : ℕ} {c M α β : ℝ}
    (h : c03m_aux_SB F y z J S c M α β) (hJ : J' ≤ J) : c03m_aux_SB F y z J' S c M α β :=
  fun a ha b hb => h a (ha.trans hJ) b hb

/-- The differentiated amplitudes: `E₀,₀ = H`, `E_{j+1,l} = ∂_y E_{j,l} + i (∂_yΦ) E_{j,l-1}`. -/
def c03m_aux_E (Φ H : ℝ × ℝ → ℂ) : ℕ → ℕ → ℝ × ℝ → ℂ
  | 0, l => if l = 0 then H else fun _ => 0
  | j + 1, l => fun w => c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (c03m_aux_E Φ H j l) 1 w +
      (if l = 0 then 0 else Complex.I * c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1 w *
        c03m_aux_E Φ H j (l - 1) w)

lemma c03m_aux_E_smooth {W : Set (ℝ × ℝ)} (hW : IsOpen W) {Φ H : ℝ × ℝ → ℂ}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ W) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) :
    ∀ j l, ContDiffOn ℝ (⊤ : ℕ∞) (c03m_aux_E Φ H j l) W := by
  intro j
  induction j with
  | zero =>
    intro l
    simp only [c03m_aux_E]
    split_ifs
    · exact hH
    · exact contDiffOn_const
  | succ j ih =>
    intro l
    simp only [c03m_aux_E]
    refine (c03m_aux_pd_smooth hW _ (ih l) 1).add ?_
    split_ifs
    · exact contDiffOn_const
    · exact (contDiffOn_const.mul (c03m_aux_pd_smooth hW _ hΦ 1)).mul (ih (l - 1))

lemma c03m_aux_pd_zero (v : ℝ × ℝ) : ∀ k, c03m_aux_pd v (fun _ => (0 : ℂ)) k = fun _ => 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext q
    simp only [c03m_aux_pd, ih]
    simp

lemma c03m_aux_E_zero (Φ H : ℝ × ℝ → ℂ) : ∀ j l, j < l → c03m_aux_E Φ H j l = fun _ => 0 := by
  intro j
  induction j with
  | zero =>
    intro l hl
    simp only [c03m_aux_E, show l ≠ 0 by omega, ↓reduceIte]
  | succ j ih =>
    intro l hl
    funext w
    simp only [c03m_aux_E, ih l (by omega), c03m_aux_pd_zero, show l ≠ 0 by omega, ↓reduceIte,
      ih (l - 1) (by omega)]
    simp

/-- `∂_y^j (e^{iΦ} H) = e^{iΦ} ∑_{l ≤ j} E_{j,l}` on `W`. -/
lemma c03m_aux_E_identity {W : Set (ℝ × ℝ)} (hW : IsOpen W) {Φ H : ℝ × ℝ → ℂ}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ W) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) :
    ∀ j, ∀ q ∈ W, iteratedDeriv j (fun y' => Complex.exp (Complex.I * Φ (y', q.2)) * H (y', q.2))
      q.1 = Complex.exp (Complex.I * Φ q) * ∑ l ∈ Finset.range (j + 1), c03m_aux_E Φ H j l q := by
  have hE := c03m_aux_E_smooth hW hΦ hH
  intro j
  induction j with
  | zero => intro q _; simp [c03m_aux_E]
  | succ j ih =>
    intro q hq
    rw [iteratedDeriv_succ]
    have hc : Continuous fun y' : ℝ => ((y', q.2) : ℝ × ℝ) := continuous_id.prodMk continuous_const
    have hW' : ∀ᶠ y' in 𝓝 q.1, ((y', q.2) : ℝ × ℝ) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hq)
    have hev : iteratedDeriv j (fun y' => Complex.exp (Complex.I * Φ (y', q.2)) * H (y', q.2)) =ᶠ[𝓝 q.1]
        fun y' => Complex.exp (Complex.I * Φ (y', q.2)) *
          ∑ l ∈ Finset.range (j + 1), c03m_aux_E Φ H j l (y', q.2) := by
      filter_upwards [hW'] with y' hy' using ih _ hy'
    rw [hev.deriv_eq]
    -- derivatives along `y`
    have hdy : ∀ G : ℝ × ℝ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) G W →
        HasDerivAt (fun y' => G (y', q.2)) (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) G 1 q) q.1 := by
      intro G hG
      have hd : DifferentiableAt ℝ (fun y' => G (y', q.2)) q.1 := by
        have h1 : DifferentiableAt ℝ G q :=
          (hG.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hq)
        exact h1.comp q.1 (differentiableAt_id.prodMk (differentiableAt_const _))
      have := c03m_aux_pdy_eq hW hG 1 q hq
      rw [iteratedDeriv_one] at this
      rw [← this]
      exact hd.hasDerivAt
    have hΦd := hdy Φ hΦ
    have hexp : HasDerivAt (fun y' => Complex.exp (Complex.I * Φ (y', q.2)))
        (Complex.exp (Complex.I * Φ q) * (Complex.I * c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1 q)) q.1 :=
      (hΦd.const_mul Complex.I).cexp
    have hsum : HasDerivAt (fun y' => ∑ l ∈ Finset.range (j + 1), c03m_aux_E Φ H j l (y', q.2))
        (∑ l ∈ Finset.range (j + 1), c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (c03m_aux_E Φ H j l) 1 q) q.1 :=
      HasDerivAt.fun_sum fun l _ => hdy _ (hE j l)
    have hd2 : HasDerivAt (fun y' => Complex.exp (Complex.I * Φ (y', q.2)) *
        ∑ l ∈ Finset.range (j + 1), c03m_aux_E Φ H j l (y', q.2)) _ q.1 := hexp.mul hsum
    rw [hd2.deriv]
    -- algebra
    have hz1 : c03m_aux_E Φ H j (j + 1) = fun _ => 0 := c03m_aux_E_zero Φ H j (j + 1) (by omega)
    have hR : ∑ l ∈ Finset.range (j + 1 + 1), c03m_aux_E Φ H (j + 1) l q =
        ∑ l ∈ Finset.range (j + 1), c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (c03m_aux_E Φ H j l) 1 q +
          Complex.I * c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1 q *
            ∑ l ∈ Finset.range (j + 1), c03m_aux_E Φ H j l q := by
      simp only [c03m_aux_E]
      rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun l => c03m_aux_pd _ _ 1 q), hz1,
        c03m_aux_pd_zero, add_zero, Finset.mul_sum]
      congr 1
      rw [Finset.sum_range_succ']
      simp
    rw [hR]
    ring

/-- Symbol bounds for the differentiated amplitudes `E_{j,l}`. -/
lemma c03m_aux_E_SB {W : Set (ℝ × ℝ)} (hW : IsOpen W) {Φ H : ℝ × ℝ → ℂ}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ W) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H W) {y z : ℝ}
    (hq : (y, z) ∈ W) {J S : ℕ} {cH cΦ BH L α β : ℝ} (hcH : 0 ≤ cH) (hcΦ : 0 ≤ cΦ)
    (hBH : 0 ≤ BH) (hL : 0 ≤ L) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hHb : c03m_aux_SB H y z J S cH BH α β)
    (hΦb : c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1) y z J S cΦ (L * α) α β) :
    ∀ j ≤ J, ∀ l, c03m_aux_SB (c03m_aux_E Φ H j l) y z (J - j) S
      ((1 + 2 ^ (J + S) * cΦ) ^ j * cH) (BH * L ^ l * α ^ j) α β := by
  have hE := c03m_aux_E_smooth hW hΦ hH
  have hK1 : 1 ≤ 1 + 2 ^ (J + S) * cΦ := by
    have : 0 ≤ 2 ^ (J + S) * cΦ := by positivity
    linarith
  intro j
  induction j with
  | zero =>
    intro _ l
    simp only [c03m_aux_E, pow_zero, one_mul, mul_one, Nat.sub_zero]
    split_ifs with hl
    · subst hl; simpa using hHb
    · intro a _ b _
      rw [c03m_aux_M_zero_fun, norm_zero]; positivity
  | succ j ih =>
    intro hj l
    have ih' := ih (by omega)
    have hDj : 0 ≤ (1 + 2 ^ (J + S) * cΦ) ^ j * cH := by positivity
    have hJ : J - j = (J - (j + 1)) + 1 := by omega
    have h1 : c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (c03m_aux_E Φ H j l) 1) y z (J - (j + 1)) S
        ((1 + 2 ^ (J + S) * cΦ) ^ j * cH) (BH * L ^ l * α ^ (j + 1)) α β := by
      have := c03m_aux_SB_dy hW (hE j l) hq (J := J - (j + 1)) (hJ ▸ ih' l)
      rw [show BH * L ^ l * α ^ j * α = BH * L ^ l * α ^ (j + 1) by ring] at this
      exact this
    have hD1 : (1 + 2 ^ (J + S) * cΦ) ^ j * cH ≤ (1 + 2 ^ (J + S) * cΦ) ^ (j + 1) * cH := by
      rw [pow_succ]; nlinarith
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      have e : c03m_aux_E Φ H (j + 1) 0 = c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (c03m_aux_E Φ H j 0) 1 := by
        funext w; simp [c03m_aux_E]
      rw [e]
      exact c03m_aux_SB_mono h1 hD1 (by positivity) hα hβ
    · have e : c03m_aux_E Φ H (j + 1) l = fun w =>
          c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (c03m_aux_E Φ H j l) 1 w +
            (Complex.I * c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1 w) * c03m_aux_E Φ H j (l - 1) w := by
        funext w; simp only [c03m_aux_E, show l ≠ 0 by omega, ↓reduceIte]
      rw [e]
      have hΦs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => Complex.I * c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1 w) W :=
        contDiffOn_const.mul (c03m_aux_pd_smooth hW _ hΦ 1)
      have hΦb' : c03m_aux_SB (fun w => Complex.I * c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1 w) y z
          (J - (j + 1)) S cΦ (L * α) α β :=
        c03m_aux_SB_const_mul Complex.I (by simp) (fun a _ b _ => by positivity)
          (c03m_aux_SB_monoJ hΦb (by omega))
      have hEl := c03m_aux_SB_monoJ (ih' (l - 1)) (show J - (j + 1) ≤ J - j by omega)
      have h2 := c03m_aux_SB_mul hW hΦs (hE j (l - 1)) hq hcΦ hDj (by positivity) (by positivity)
        hα hβ hΦb' hEl
      rw [show L * α * (BH * L ^ (l - 1) * α ^ j) = BH * L ^ l * α ^ (j + 1) by
        obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring] at h2
      have h3 := c03m_aux_SB_add hW (c03m_aux_pd_smooth hW _ (hE j l) 1) (hΦs.mul (hE j (l - 1))) hq
        h1 h2
      refine c03m_aux_SB_mono h3 ?_ (by positivity) hα hβ
      have : 2 ^ (J - (j + 1) + S) * cΦ * ((1 + 2 ^ (J + S) * cΦ) ^ j * cH) ≤
          2 ^ (J + S) * cΦ * ((1 + 2 ^ (J + S) * cΦ) ^ j * cH) := by
        gcongr
        · norm_num
        · omega
      rw [pow_succ]
      nlinarith

/-! ## Parameter integration by parts and difference bounds -/


lemma c03m_aux_E_vanish {O : Set (ℝ × ℝ)} (hO : IsOpen O) (Φ : ℝ × ℝ → ℂ) {H : ℝ × ℝ → ℂ}
    (hH0 : ∀ w ∈ O, H w = 0) : ∀ j l, ∀ w ∈ O, c03m_aux_E Φ H j l w = 0 := by
  intro j
  induction j with
  | zero =>
    intro l w hw
    simp only [c03m_aux_E]
    split_ifs
    · exact hH0 w hw
    · rfl
  | succ j ih =>
    intro l w hw
    have hev : c03m_aux_E Φ H j l =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [hO.mem_nhds hw] with w' hw' using ih l w' hw'
    simp only [c03m_aux_E, c03m_aux_pd, hev.fderiv_eq]
    split_ifs
    · simp
    · simp [ih (l - 1) w hw]



set_option maxHeartbeats 800000 in
/-- PROPOSED blueprint node (supports lem:c03_mult_parameter_ibp): the pure estimate
`|∂_y^j I_η(y,t)| ≤ C B Y^{-j} Λ^{p-K}` on `Y/2 < y < 3Y`, `0 < t ≤ 1`, `η ≥ 0`, under `𝖧`
through a finite order `k₀(p,N,j)`; proof: differentiated-amplitude recursion
`b_{j+1,l} = ∂_y b_{j,l} + i(∂_yφ_t) b_{j,l-1}` with `c03_mult_amplitude_symbol`,
`c03_mult_phase_symbol` and homogeneous IBP (`c03_ibp_homogeneous`). -/
theorem c03_mult_parameter_ibp_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (N : ℕ) (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ η : ℝ, 0 ≤ η →
        ∀ y ∈ Ioo (Y / 2) (3 * Y),
          ‖iteratedDeriv j (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y‖ ≤
            C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) := by
  intro j
  set K₀ : ℕ := 2 * N - 1 + c03_mult_q1 q with hK₀
  have hKl : ∀ l : ℕ, p < ((K₀ + l : ℕ) : ℝ) := by
    intro l
    have : (1 : ℝ) ≤ ((K₀ + l : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ K₀ + l by omega)
    linarith
  have hibp := fun l : ℕ => c03c_c03_ibp_homogeneous p ((K₀ + l : ℕ) : ℝ) c₀ hp hp1 (hKl l) hc₀
  choose s0 hs0 using hibp
  set S : ℕ := ∑ l ∈ Finset.range (j + 1), s0 l with hS
  have hsS : ∀ l ≤ j, s0 l ≤ S := fun l hl =>
    Finset.single_le_sum (f := s0) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  refine ⟨2 * N + j + S + 4, fun Ck => ?_⟩
  have hamp := fun a' b' : ℕ => c03_mult_amplitude_symbol c₀ hc₀ N hN r q hrq a' b' Ck
  choose Camp hCamp0 hampb using hamp
  set cH : ℝ := ∑ a' ∈ Finset.range (j + 1), ∑ b' ∈ Finset.range (S + 1), Camp a' b' with hcH_def
  have hcH : ∀ a' ≤ j, ∀ b' ≤ S, Camp a' b' ≤ cH := by
    intro a' ha b' hb
    calc Camp a' b' ≤ ∑ b'' ∈ Finset.range (S + 1), Camp a' b'' :=
          Finset.single_le_sum (f := fun b'' => Camp a' b'') (fun i _ => (hCamp0 a' i).le)
            (Finset.mem_range.2 (by omega))
      _ ≤ cH := Finset.single_le_sum (f := fun a'' => ∑ b'' ∈ Finset.range (S + 1), Camp a'' b'')
            (fun i _ => Finset.sum_nonneg fun k _ => (hCamp0 i k).le) (Finset.mem_range.2 (by omega))
  have hcH0 : 0 ≤ cH := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => (hCamp0 i k).le
  have hrec := fun s : ℕ => c03_mult_phase_symbol c₀ hc₀ 0 s Ck
  choose Crec hCrec0 hrecb using hrec
  set CS : ℝ := ∑ k ∈ Finset.range (2 * N + j + S + 5), |Ck k| + 1 with hCS
  have hCS1 : 1 ≤ CS := by
    have : 0 ≤ ∑ k ∈ Finset.range (2 * N + j + S + 5), |Ck k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hCk : ∀ k < 2 * N + j + S + 5, Ck k ≤ CS := by
    intro k hk
    have := Finset.single_le_sum (f := fun k => |Ck k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hk)
    linarith [le_abs_self (Ck k)]
  set cΦ : ℝ := 2 ^ (j + S + 1) * CS + 4 ^ S * CS with hcΦ
  have hcΦ0 : 0 ≤ cΦ := by positivity
  set D : ℝ := (1 + 2 ^ (j + S) * cΦ) ^ j * cH with hD
  have hD0 : 0 ≤ D := by positivity
  set Cs : ℕ → ℝ := fun s => D + 4 ^ s * Crec s with hCs
  have hCl := fun l => hs0 l Cs
  choose Cl hCl0 hClb using hCl
  refine ⟨∑ l ∈ Finset.range (j + 1), Cl l + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun l _ => (hCl0 l).le) one_pos, ?_⟩
  intro Y Λ A a Ψ hY hΛ hA hyp t ht η hη y hy
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  obtain ⟨ha, has, hΨ, hb⟩ := id hyp
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyU : y ∈ U := hVU hy
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 + t * w.2 with hℓ_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ := by fun_prop
  set W : Set (ℝ × ℝ) := (V ×ˢ univ) ∩ ℓ ⁻¹' U with hW_def
  have hW : IsOpen W := (isOpen_Ioo.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
  set Φ : ℝ × ℝ → ℂ := fun w => ((c03_mult_phit Ψ w.1 t w.2 : ℝ) : ℂ) with hΦ_def
  set H : ℝ × ℝ → ℂ := fun w => c03_mult_bt Y a Ψ N r q w.1 t w.2 with hH_def
  have hΦs : ContDiffOn ℝ (⊤ : ℕ∞) Φ W :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (c03m_aux_phit_smooth hΨ t hVU)
  have hHs : ContDiffOn ℝ (⊤ : ℕ∞) H W :=
    ((hampb 0 0 Y Λ A a Ψ hY hΛ hA (c03m_aux_hyp_mono (by omega) hyp) t ht).1).mono
      inter_subset_left
  set A' := iteratedDeriv r a with hA'_def
  have hA's : tsupport A' ⊆ U := (c03m_aux_tsupport_iteratedDeriv a r).trans has
  -- `H` vanishes where `y + tz ∉ supp A'`
  have hHA : ∀ y' z', A' (y' + t * z') = 0 → H (y', z') = 0 := by
    intro y' z' h
    simp only [hH_def]
    rw [c03m_aux_bt_eq a hΨ N r q]
    simp only [hA'_def] at h
    simp [h]
  set O : Set (ℝ × ℝ) := W ∩ ℓ ⁻¹' (tsupport A')ᶜ with hO_def
  have hO : IsOpen O := hW.inter ((isClosed_tsupport A').isOpen_compl.preimage hℓ.continuous)
  have hH0 : ∀ w ∈ O, H w = 0 := fun w hw =>
    hHA w.1 w.2 (image_eq_zero_of_notMem_tsupport hw.2)
  have hEv := c03m_aux_E_vanish hO Φ hH0
  have hEs := c03m_aux_E_smooth hW hΦs hHs
  -- the localized amplitudes `β_l`
  set Uz : Set ℝ := {z | y + t * z ∈ U} with hUz
  have hUzo : IsOpen Uz := hU.preimage (by fun_prop)
  have hyzW : ∀ z ∈ Uz, (y, z) ∈ W := fun z hz => ⟨⟨hy, trivial⟩, hz⟩
  set β : ℕ → ℝ → ℂ := fun l z => if y + t * z ∈ U then c03m_aux_E Φ H j l (y, z) else 0
    with hβ
  have hβ_eq : ∀ l, ∀ z ∈ Uz, β l =ᶠ[𝓝 z] fun z' => c03m_aux_E Φ H j l (y, z') := by
    intro l z hz
    filter_upwards [hUzo.mem_nhds hz] with z' hz'
    simp only [hβ]
    exact if_pos hz'
  have hβ0 : ∀ l, ∀ z, y + t * z ∉ tsupport A' → β l =ᶠ[𝓝 z] fun _ => 0 := by
    intro l z hz
    have hopen : IsOpen {z' : ℝ | y + t * z' ∉ tsupport A'} :=
      (isClosed_tsupport A').isOpen_compl.preimage (by fun_prop)
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    simp only [hβ]
    split_ifs with h
    · exact hEv j l (y, z') ⟨hyzW z' h, hz'⟩
    · rfl
  have hEyz : ∀ l, ContDiffOn ℝ (⊤ : ℕ∞) (fun z' => c03m_aux_E Φ H j l (y, z')) Uz :=
    fun l => (hEs j l).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun z hz => hyzW z hz)
  have hβs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (β l) := by
    intro l
    refine c03m_aux_smooth_of_local hUzo ?_ ?_
    · exact (hEyz l).congr (fun z hz => by simp only [hβ]; exact if_pos hz)
    · intro z hz; exact hβ0 l z (fun h => hz (hA's h))
  have hβsupp : ∀ l, tsupport (β l) ⊆ {z | y + t * z ∈ tsupport A'} := by
    intro l
    refine closure_minimal (fun z hz => ?_) ((isClosed_tsupport A').preimage (by fun_prop))
    by_contra hc
    exact hz ((hβ0 l z hc).self_of_nhds)
  have htsU : ∀ l, tsupport (β l) ⊆ Uz := fun l => (hβsupp l).trans (fun z hz => hA's hz)
  have hA'c : IsCompact (tsupport A') :=
    (c03m_aux_tsupport_compact has).of_isClosed_subset (isClosed_tsupport _)
      (c03m_aux_tsupport_iteratedDeriv a r)
  have hβc : ∀ l, HasCompactSupport (β l) := by
    intro l
    refine HasCompactSupport.intro (hA'c.image (by fun_prop : Continuous fun x : ℝ => (x - y) / t))
      fun z hz => ?_
    have hz' : y + t * z ∉ tsupport A' := fun h => hz ⟨y + t * z, h, by field_simp; ring⟩
    exact (hβ0 l z hz').self_of_nhds
  have hYi : 0 ≤ Y⁻¹ := by positivity
  have hrp : ∀ k : ℕ, Y ^ (-(k : ℝ)) = Y⁻¹ ^ k := fun k => by
    rw [Real.rpow_neg hY0.le, Real.rpow_natCast, inv_pow]
  set B0 : ℝ := c03_mult_size N q Y Λ A t with hB0
  have hB00 : 0 ≤ B0 := c03m_aux_size_nonneg N q hY0 hΛ0.le hA.le ht0.le
  -- symbol bounds of the amplitude and the phase at `(y,z)`
  have hSBz : ∀ z ∈ Uz, z ≠ 0 → ∀ l, c03m_aux_SB (c03m_aux_E Φ H j l) y z 0 S D
      (B0 * |z| ^ K₀ * (Λ * |z|) ^ l * Y⁻¹ ^ j) Y⁻¹ |z|⁻¹ := by
    intro z hz hz0 l
    have hz' : 0 < |z| := abs_pos.2 hz0
    have hzi : 0 ≤ |z|⁻¹ := by positivity
    have hHb : c03m_aux_SB H y z j S cH (B0 * |z| ^ K₀) Y⁻¹ |z|⁻¹ := by
      intro a' ha' b' hb'
      have h1 := ((hampb a' b' Y Λ A a Ψ hY hΛ hA (c03m_aux_hyp_mono (by omega) hyp) t ht).2 y
        hy).2.2.2 z hz0
      have e : c03m_aux_M H a' b' y z = iteratedDeriv a' (fun y' =>
          iteratedDeriv b' (c03_mult_bt Y a Ψ N r q y' t) z) y := rfl
      rw [e]
      refine h1.trans ?_
      rw [hrp, Real.rpow_sub hz', Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
      have hc := hcH a' ha' b' hb'
      have : 0 ≤ B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b') := by positivity
      calc Camp a' b' * B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')
          = Camp a' b' * (B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')) := by ring
        _ ≤ cH * (B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')) := mul_le_mul_of_nonneg_right hc this
        _ = _ := by ring
    have hΦb : c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) Φ 1) y z j S cΦ (Λ * |z| * Y⁻¹)
        Y⁻¹ |z|⁻¹ := by
      intro a' ha' b' hb'
      rw [c03m_aux_M_dy hW hΦs a' b' (hyzW z hz)]
      have hbd : ∀ x ∈ U, ∀ k ≤ (a' + 1) + b',
          |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k := by
        intro x hx k hk
        have h1 := ((hb x hx).2.2 k (by omega)).1
        rw [hrp] at h1
        exact h1.trans (by gcongr; exact hCk k (by omega))
      obtain ⟨-, h2⟩ := c03m_aux_phit_M hY0 hΨ (j := a' + 1) (s := b') hbd (by linarith)
        hΛ0.le ht0 ht1 hy hz hz0
      refine h2.trans ?_
      have e1 : (2 : ℝ) ^ (a' + 1 + b') ≤ 2 ^ (j + S + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have e2 : (4 : ℝ) ^ b' ≤ 4 ^ S := pow_le_pow_right₀ (by norm_num) hb'
      have hC : 2 ^ (a' + 1 + b') * CS + 4 ^ b' * CS ≤ cΦ := by
        rw [hcΦ]; gcongr
      have : 0 ≤ Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b') := by positivity
      calc (2 ^ (a' + 1 + b') * CS + 4 ^ b' * CS) * Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')
          = (2 ^ (a' + 1 + b') * CS + 4 ^ b' * CS) * (Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')) := by
            ring
        _ ≤ cΦ * (Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')) := mul_le_mul_of_nonneg_right hC this
        _ = _ := by ring
    have := c03m_aux_E_SB hW hΦs hHs (hyzW z hz) hcH0 hcΦ0 (by positivity) (by positivity) hYi hzi
      hHb hΦb j le_rfl l
    rwa [Nat.sub_self] at this
  -- the `z`-derivative bounds of `β_l`
  have hβd : ∀ l, ∀ z ∈ Uz, z ≠ 0 → ∀ s ≤ S, ‖iteratedDeriv s (β l) z‖ ≤
      D * (B0 * Λ ^ l * Y⁻¹ ^ j) * |z| ^ (((K₀ + l : ℕ) : ℝ) - s) := by
    intro l z hz hz0 s hs
    have hz' : 0 < |z| := abs_pos.2 hz0
    rw [(hβ_eq l z hz).iteratedDeriv_eq]
    have h1 := hSBz z hz hz0 l 0 le_rfl s hs
    have e : c03m_aux_M (c03m_aux_E Φ H j l) 0 s y z =
        iteratedDeriv s (fun z' => c03m_aux_E Φ H j l (y, z')) z := by
      simp [c03m_aux_M]
    rw [e] at h1
    refine h1.trans (le_of_eq ?_)
    rw [Real.rpow_sub hz', Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow,
      mul_pow, pow_add]
    ring
  -- the phase on `Uz`
  have hφs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => c03_mult_phit Ψ y t z) Uz := by
    have e : (fun z => c03_mult_phit Ψ y t z) =
        fun z => deriv Ψ y * z + (Ψ (y + t * z) - Ψ y - deriv Ψ y * (t * z)) := rfl
    rw [e]
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Ψ (y + t * z)) Uz :=
      hΨ.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun z : ℝ => y + t * z).contDiffOn
        (fun z hz => hz)
    exact (contDiffOn_const.mul contDiffOn_id).add ((h1.sub contDiffOn_const).sub
      (contDiffOn_const.mul (contDiffOn_const.mul contDiffOn_id)))
  have hφd : ∀ z ∈ Uz, c₀⁻¹ * Λ ≤ |deriv (fun z => c03_mult_phit Ψ y t z) z| ∧
      |deriv (fun z => c03_mult_phit Ψ y t z) z| ≤ c₀ * Λ := by
    intro z hz
    have hd := (c03m_aux_phit_hasDerivAt hU hΨ y t z hz).deriv
    have hc := c03m_aux_convex_bounds ht0.le ht1 ⟨(hb y hyU).1, (hb y hyU).2.1⟩
      ⟨(hb _ hz).1, (hb _ hz).2.1⟩
    have hpos : 0 < c₀⁻¹ * Λ := by positivity
    rw [hd, abs_of_pos (hpos.trans_le hc.1)]
    exact hc
  have hrecz : ∀ z ∈ Uz, z ≠ 0 → ∀ s ≤ S,
      |iteratedDeriv s (fun z => 1 / deriv (fun z => c03_mult_phit Ψ y t z) z) z| ≤ Cs s * Λ⁻¹ * |z| ^ (-(s : ℝ)) := by
    intro z hz hz0 s hs
    have hz' : 0 < |z| := abs_pos.2 hz0
    have hΨb : ∀ x ∈ U, c₀⁻¹ * Λ ≤ deriv Ψ x ∧ deriv Ψ x ≤ c₀ * Λ ∧
        ∀ k ≤ 0 + s + 2, |iteratedDeriv k (deriv Ψ) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ)) :=
      fun x hx => ⟨(hb x hx).1, (hb x hx).2.1, fun k hk => ((hb x hx).2.2 k (by omega)).1⟩
    have h1 := (hrecb s Y Λ Ψ Ψ hY hΛ hΨ hΨ hΨb hΨb 0 ⟨le_rfl, zero_le_one⟩ y hy t ht z
      hz).2.2.2.2.2.1
    simp only [sub_zero, one_mul, zero_mul, add_zero, iteratedDeriv_zero, Nat.cast_zero, neg_zero,
      Real.rpow_zero, mul_one] at h1
    refine h1.trans ?_
    have htz := c03m_aux_tz_le ht0 hy hz
    have htY : t / Y ≤ 4 * |z|⁻¹ := by
      rw [div_le_iff₀ hY0]
      calc t = t * |z| * |z|⁻¹ := by field_simp
        _ ≤ 4 * Y * |z|⁻¹ := by gcongr
        _ = _ := by ring
    have h4 : (t / Y) ^ s ≤ 4 ^ s * |z| ^ (-(s : ℝ)) := by
      rw [Real.rpow_neg hz'.le, Real.rpow_natCast, ← inv_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) htY s
    have hC : Crec s ≤ Cs s / 4 ^ s := by
      rw [hCs, le_div_iff₀ (by positivity)]; nlinarith [hD0, hCrec0 s]
    calc Crec s * Λ⁻¹ * (t / Y) ^ s ≤ Crec s * Λ⁻¹ * (4 ^ s * |z| ^ (-(s : ℝ))) := by
          have := (hCrec0 s).le; gcongr
      _ ≤ Cs s / 4 ^ s * Λ⁻¹ * (4 ^ s * |z| ^ (-(s : ℝ))) := by gcongr
      _ = _ := by field_simp
  -- `β_l` vanishes at the origin
  have h0Uz : (0 : ℝ) ∈ Uz := by
    show y + t * 0 ∈ U
    simpa using hyU
  have hβ00 : ∀ l ≤ j, β l 0 = 0 := by
    intro l hl
    have he : (0 : ℝ) < ((K₀ + l : ℕ) : ℝ) - ((0 : ℕ) : ℝ) := by
      have := hKl l; push_cast at this ⊢; linarith
    have h1 : Tendsto (fun z => ‖β l z‖) (𝓝[≠] 0) (𝓝 ‖β l 0‖) :=
      ((hβs l).continuous.norm.tendsto 0).mono_left nhdsWithin_le_nhds
    have hc : Continuous (fun z : ℝ =>
        D * (B0 * Λ ^ l * Y⁻¹ ^ j) * |z| ^ (((K₀ + l : ℕ) : ℝ) - ((0 : ℕ) : ℝ))) :=
      continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr he.le))
    have h2 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    rw [abs_zero, Real.zero_rpow he.ne', mul_zero] at h2
    have h3 : ∀ᶠ z in 𝓝[≠] (0 : ℝ), ‖β l z‖ ≤
        D * (B0 * Λ ^ l * Y⁻¹ ^ j) * |z| ^ (((K₀ + l : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hUzo.mem_nhds h0Uz)]
        with z hz0 hz
      have := hβd l z hz hz0 0 (Nat.zero_le _)
      rwa [iteratedDeriv_zero] at this
    exact norm_le_zero_iff.1 (le_of_tendsto_of_tendsto h1 h2 h3)
  -- integrability of the pieces
  have hintl : ∀ l ≤ j, Integrable (fun z : ℝ =>
      Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * β l z / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
    intro l hl
    obtain ⟨M, hM0, hM⟩ := c03m_aux_lip_bound ((hβs l).of_le (by exact_mod_cast le_top)) (hβc l)
    have hcont : Continuous (fun z => β l z * Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ))) :=
      c03c_aux_cont_mul_exp hUzo (hβs l).continuous (htsU l) hφs.continuousOn
    have hcont2 : Continuous (fun z : ℝ => β l z *
        Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))) := hcont.mul (by fun_prop)
    have hnb : ∀ z, ‖β l z * Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ ≤ ‖β l z‖ := by
      intro z
      rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (c03m_aux_gauss_le η z hη)
    have hk := c03m_aux_kernel_integrable hp hp1 hcont2.aestronglyMeasurable (K := M)
      (fun z => (hnb z).trans (by
        have := (hM 0 z).1
        rwa [zero_add, hβ00 l hl, sub_zero] at this))
      (fun z => (hnb z).trans (by
        have := (hM 0 z).2
        rwa [zero_add, hβ00 l hl, sub_zero] at this))
    refine hk.congr (Eventually.of_forall fun z => ?_)
    simp only
    ring
  -- the integrand
  have hint : ∀ z : ℝ, iteratedDeriv j (fun y' =>
      Complex.exp (Complex.I * (c03_mult_phit Ψ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y =
      ∑ l ∈ Finset.range (j + 1), Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * β l z / ((|z| ^ (1 + p) : ℝ) : ℂ) := by
    intro z
    have hfun : (fun y' => Complex.exp (Complex.I * (c03_mult_phit Ψ y' t z : ℂ) -
        ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a Ψ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
        fun y' => (Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) *
          (Complex.exp (Complex.I * Φ (y', z)) * H (y', z)) := by
      funext y'
      simp only [hΦ_def, hH_def]
      rw [sub_eq_add_neg, Complex.exp_add]; ring
    rw [hfun, iteratedDeriv_const_mul_field]
    by_cases hz : y + t * z ∈ U
    · have h1 := c03m_aux_E_identity hW hΦs hHs j (y, z) (hyzW z hz)
      dsimp only at h1
      rw [h1, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hβz : β l z = c03m_aux_E Φ H j l (y, z) := by simp only [hβ]; exact if_pos hz
      rw [hβz]
      simp only [hΦ_def]
      ring
    · have hz' : y + t * z ∉ tsupport A' := fun h => hz (hA's h)
      have hopen : IsOpen {y' : ℝ | y' + t * z ∉ tsupport A'} :=
        (isClosed_tsupport A').isOpen_compl.preimage (by fun_prop)
      have hev : (fun y' => Complex.exp (Complex.I * Φ (y', z)) * H (y', z)) =ᶠ[𝓝 y]
          fun _ => 0 := by
        filter_upwards [hopen.mem_nhds hz'] with y' hy'
        rw [hHA y' z (image_eq_zero_of_notMem_tsupport hy'), mul_zero]
      rw [hev.iteratedDeriv_eq]
      have hβz : ∀ l, β l z = 0 := fun l => by simp only [hβ]; exact if_neg hz
      simp [hβz, iteratedDeriv_const]
  have hform := (c03m_aux_I_smooth_formula p hp hp1 c₀ hc₀ N hN r q hrq Y hY0 a Ψ ha has hΨ t ht
    η).2 j y hy
  rw [hform.2, integral_congr_ae (Filter.Eventually.of_forall hint),
    integral_finsetSum _ (fun l hl => hintl l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)))]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ l ∈ Finset.range (j + 1), ‖∫ z : ℝ,
      Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * β l z / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ ≤
      Cl l * (B0 * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hB : 0 ≤ B0 * Λ ^ l * Y⁻¹ ^ j := by positivity
    obtain ⟨hbd, -⟩ := hClb l Λ (B0 * Λ ^ l * Y⁻¹ ^ j) Uz (β l) (fun z => c03_mult_phit Ψ y t z)
      hΛ0 hB hUzo (hβs l) (hβc l) (htsU l) hφs
      (fun z hz hz0 s hs => (hβd l z hz hz0 s (hs.trans (hsS l hl'))).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by rw [hCs]; have := (hCrec0 s).le; simp only; nlinarith [pow_pos (show (0:ℝ) < 4 by norm_num) s])
          hB) (Real.rpow_nonneg (abs_nonneg _) _)))
      hφd (fun z hz hz0 s hs => hrecz z hz hz0 s (hs.trans (hsS l hl')))
    refine (hbd η hη).trans (le_of_eq ?_)
    rw [Nat.cast_add, show p - ((K₀ : ℝ) + (l : ℝ)) = (p - K₀) - l by ring,
      Real.rpow_sub hΛ0, Real.rpow_natCast]
    field_simp
  have hS0 : 0 ≤ B0 * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ)) := by positivity
  calc _ ≤ ∑ l ∈ Finset.range (j + 1), Cl l * (B0 * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (∑ l ∈ Finset.range (j + 1), Cl l) * (B0 * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ l ∈ Finset.range (j + 1), Cl l + 1) * (B0 * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hS0
    _ = _ := by rw [hrp]; ring

/-- Blueprint: lem:c03_mult_parameter_ibp.  For each `j` there is a finite order `k₀ = k₀(p,N,j)`
such that under `𝖧` through order `k₀`: for each `η ≥ 0`, `0 < t ≤ 1`, `y ↦ I_η(y,t)` is smooth
on `(Y/2,3Y)`, its derivatives are the integrals of the (absolutely integrable) `y`-derivatives of
the integrand, and `|∂_y^j I_η(y,t)| ≤ C B Y^{-j} Λ^{p-K} ≤ C A Y^{-N-j} Λ^{p-N}`.
Encoding: the bound is stated on the neighbourhood `Y/2 < y < 3Y` of `[Y,2Y]` (blueprint:
"extend to `Y/2<y<3Y` with enlarged constants" for the symbol lemmas), as needed to differentiate
under the `t`-integral in `c03_mult_remainder_parameter_integral`. -/
theorem c03_mult_parameter_ibp (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (N : ℕ) (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ η : ℝ, 0 ≤ η →
        ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => c03_mult_I p Y a Ψ N r q η y' t)
          (Ioo (Y / 2) (3 * Y)) ∧
        (∀ i : ℕ, ∀ y ∈ Ioo (Y / 2) (3 * Y),
          Integrable (fun z : ℝ => iteratedDeriv i (fun y' =>
            Complex.exp (Complex.I * (c03_mult_phit Ψ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
              c03_mult_bt Y a Ψ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y) ∧
          iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y =
            ∫ z : ℝ, iteratedDeriv i (fun y' =>
              Complex.exp (Complex.I * (c03_mult_phit Ψ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
                c03_mult_bt Y a Ψ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y) ∧
        ∀ y ∈ Ioo (Y / 2) (3 * Y),
          ‖iteratedDeriv j (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y‖ ≤
            C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) ∧
          C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) ≤
            C * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
  intro j
  obtain ⟨k₀, hk⟩ := c03_mult_parameter_ibp_bound p hp hp1 c₀ hc₀ N hN r q hrq j
  refine ⟨k₀, fun Ck => ?_⟩
  obtain ⟨C, hC, hb⟩ := hk Ck
  refine ⟨C, hC, fun Y Λ A a Ψ hY hΛ hA hyp t ht η hη => ?_⟩
  obtain ⟨hsm, hform⟩ := c03m_aux_I_smooth_formula p hp hp1 c₀ hc₀ N hN r q hrq Y
    (by linarith) a Ψ hyp.1 hyp.2.1 hyp.2.2.1 t ht η
  refine ⟨hsm, hform, fun y hy => ⟨hb Y Λ A a Ψ hY hΛ hA hyp t ht η hη y hy, ?_⟩⟩
  have := c03m_aux_size_bound N r hN q hrq (p := p) (Λ := Λ) (A := A) (t := t) (j : ℝ) hY hΛ
    hA.le ht.1.le ht.2
  have e1 : C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
      Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) = C * (c03_mult_size N q Y Λ A t *
        Y ^ (-(j : ℝ)) * Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ))) := by ring
  have e2 : C * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) =
      C * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left this hC.le

/-! ### Difference of two summand integrals -/

lemma c03m_aux_SB_smul {F : ℝ × ℝ → ℂ} {y z : ℝ} {J S : ℕ} {c M α β : ℝ} (k : ℂ)
    (h : c03m_aux_SB F y z J S c M α β) :
    c03m_aux_SB (fun w => k * F w) y z J S (‖k‖ * c) M α β := by
  intro a ha b hb
  rw [c03m_aux_M_const_mul, norm_mul]
  calc ‖k‖ * ‖c03m_aux_M F a b y z‖ ≤ ‖k‖ * (c * M * α ^ a * β ^ b) :=
        mul_le_mul_of_nonneg_left (h a ha b hb) (norm_nonneg _)
    _ = _ := by ring

/-- Pointwise domination, vanishing and continuity of `z ↦ ∂_y^j(e^{iΦ}H)(y,z)`. -/
lemma c03m_aux_core_dom {Y t y : ℝ} (hY : 0 < Y) (hy : y ∈ Ioo (Y / 2) (3 * Y))
    {T : Set ℝ} (hTc : IsCompact T) (hTU : T ⊆ Ioo (Y / 4) (4 * Y))
    {Φr : ℝ × ℝ → ℝ} {H : ℝ × ℝ → ℂ}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ((Φr w : ℝ) : ℂ))
      ((Ioo (Y / 2) (3 * Y) ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)))
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H
      ((Ioo (Y / 2) (3 * Y) ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)))
    (hHT : ∀ y' z', y' + t * z' ∉ T → H (y', z') = 0)
    {j S K₀ : ℕ} {cH cΦ BH Λ : ℝ} (hcH : 0 ≤ cH) (hcΦ : 0 ≤ cΦ) (hBH : 0 ≤ BH) (hΛ : 0 ≤ Λ)
    (hSBH : ∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → z ≠ 0 →
      c03m_aux_SB H y z j S cH (BH * |z| ^ K₀) Y⁻¹ |z|⁻¹)
    (hSBΦ : ∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → z ≠ 0 →
      c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (fun w => ((Φr w : ℝ) : ℂ)) 1) y z j S cΦ
        (Λ * |z| * Y⁻¹) Y⁻¹ |z|⁻¹) :
    (∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → z ≠ 0 →
      ‖iteratedDeriv j (fun y' => Complex.exp (Complex.I * ((Φr (y', z) : ℝ) : ℂ)) * H (y', z)) y‖ ≤
        (1 + 2 ^ (j + S) * cΦ) ^ j * cH * (BH * Y⁻¹ ^ j) *
          ∑ l ∈ Finset.range (j + 1), |z| ^ K₀ * (Λ * |z|) ^ l) ∧
    (∀ z, y + t * z ∉ T →
      iteratedDeriv j (fun y' => Complex.exp (Complex.I * ((Φr (y', z) : ℝ) : ℂ)) * H (y', z)) y = 0) ∧
    Continuous (fun z =>
      iteratedDeriv j (fun y' => Complex.exp (Complex.I * ((Φr (y', z) : ℝ) : ℂ)) * H (y', z)) y) := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  set W : Set (ℝ × ℝ) := (V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U with hW_def
  have hW : IsOpen W := (isOpen_Ioo.prod isOpen_univ).inter (isOpen_Ioo.preimage (by fun_prop))
  set Φ : ℝ × ℝ → ℂ := fun w => ((Φr w : ℝ) : ℂ) with hΦ_def
  have hyzW : ∀ z, y + t * z ∈ U → (y, z) ∈ W := fun z hz => ⟨⟨hy, trivial⟩, hz⟩
  have hid := c03m_aux_E_identity hW hΦ hH j
  have hEs := c03m_aux_E_smooth hW hΦ hH
  refine ⟨fun z hz hz0 => ?_, fun z hz => ?_, ?_⟩
  · have h1 := hid (y, z) (hyzW z hz)
    simp only at h1
    rw [h1, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    have hz' : 0 < |z| := abs_pos.2 hz0
    have h2 := c03m_aux_E_SB hW hΦ hH (hyzW z hz) (L := Λ * |z|) hcH hcΦ (by positivity)
      (by positivity) (by positivity) (by positivity) (hSBH z hz hz0) (hSBΦ z hz hz0)
      j le_rfl l 0 (Nat.zero_le _) 0 (Nat.zero_le _)
    have e : c03m_aux_M (c03m_aux_E Φ H j l) 0 0 y z = c03m_aux_E Φ H j l (y, z) := by
      simp [c03m_aux_M]
    rw [e] at h2
    refine h2.trans (le_of_eq ?_)
    simp only [pow_zero, mul_one, mul_pow]
    ring
  · have hopen : IsOpen {y' : ℝ | y' + t * z ∉ T} :=
      hTc.isClosed.isOpen_compl.preimage (by fun_prop)
    have hev : (fun y' => Complex.exp (Complex.I * ((Φr (y', z) : ℝ) : ℂ)) * H (y', z)) =ᶠ[𝓝 y]
        fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hz] with y' hy'
      rw [hHT y' z hy', mul_zero]
    rw [hev.iteratedDeriv_eq]
    simp
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : y + t * z ∈ U
    · have hUz : IsOpen {z' : ℝ | y + t * z' ∈ U} := isOpen_Ioo.preimage (by fun_prop)
      have hc : ContinuousOn (fun z' => Complex.exp (Complex.I * Φ (y, z')) *
          ∑ l ∈ Finset.range (j + 1), c03m_aux_E Φ H j l (y, z')) {z' : ℝ | y + t * z' ∈ U} := by
        have hm : ContinuousOn (fun z' : ℝ => ((y, z') : ℝ × ℝ)) {z' : ℝ | y + t * z' ∈ U} :=
          (continuous_const.prodMk continuous_id).continuousOn
        refine ((Complex.continuous_exp.comp_continuousOn
          (continuousOn_const.mul (hΦ.continuousOn.comp hm fun z' hz' => hyzW z' hz')))).mul ?_
        exact continuousOn_finsetSum _ fun l _ =>
          (hEs j l).continuousOn.comp hm fun z' hz' => hyzW z' hz'
      refine ((hc.continuousAt (hUz.mem_nhds hz)).congr ?_)
      filter_upwards [hUz.mem_nhds hz] with z' hz'
      exact (hid (y, z') (hyzW z' hz')).symm
    · have hzT : y + t * z ∉ T := fun h => hz (hTU h)
      have hopen : IsOpen {z' : ℝ | y + t * z' ∉ T} :=
        hTc.isClosed.isOpen_compl.preimage (by fun_prop)
      refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
      filter_upwards [hopen.mem_nhds hzT] with z' hz'
      have hopen' : IsOpen {y' : ℝ | y' + t * z' ∉ T} :=
        hTc.isClosed.isOpen_compl.preimage (by fun_prop)
      have hev : (fun y' => Complex.exp (Complex.I * ((Φr (y', z') : ℝ) : ℂ)) * H (y', z')) =ᶠ[𝓝 y]
          fun _ => 0 := by
        filter_upwards [hopen'.mem_nhds hz'] with y' hy'
        rw [hHT y' z' hy', mul_zero]
      rw [hev.iteratedDeriv_eq]
      simp

/-- Integrability against the regularised kernel of a continuous function with compact
support vanishing to first order at `0`. -/
lemma c03m_aux_dom_integrable {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f : ℝ → ℂ} (hf : Continuous f)
    {R C0 Λ : ℝ} {K₀ j : ℕ} (hK₀ : 1 ≤ K₀) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hΛ : 0 ≤ Λ)
    (hsupp : ∀ z, R < |z| → f z = 0)
    (hb : ∀ z, z ≠ 0 → |z| ≤ R → ‖f z‖ ≤ C0 * ∑ l ∈ Finset.range (j + 1), |z| ^ K₀ * (Λ * |z|) ^ l)
    (η : ℝ) (hη : 0 ≤ η) :
    Integrable (fun z : ℝ => Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) * f z) := by
  set M : ℝ := C0 * ∑ l ∈ Finset.range (j + 1), R ^ (K₀ - 1) * (Λ * R) ^ l with hM
  have hM0 : 0 ≤ M := by positivity
  have hlin : ∀ z, z ≠ 0 → ‖f z‖ ≤ M * |z| := by
    intro z hz
    by_cases hzR : |z| ≤ R
    · refine (hb z hz hzR).trans ?_
      rw [hM, mul_assoc, Finset.sum_mul]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hC0
      have e : |z| ^ K₀ = |z| ^ (K₀ - 1) * |z| := by
        rw [← pow_succ]; congr 1; omega
      rw [e]
      have h1 : |z| ^ (K₀ - 1) ≤ R ^ (K₀ - 1) := pow_le_pow_left₀ (abs_nonneg _) hzR _
      have h2 : (Λ * |z|) ^ l ≤ (Λ * R) ^ l := pow_le_pow_left₀ (by positivity) (by gcongr) _
      calc |z| ^ (K₀ - 1) * |z| * (Λ * |z|) ^ l = (|z| ^ (K₀ - 1) * (Λ * |z|) ^ l) * |z| := by ring
        _ ≤ (R ^ (K₀ - 1) * (Λ * R) ^ l) * |z| := by gcongr
    · rw [hsupp z (not_le.1 hzR), norm_zero]; positivity
  have hf0 : f 0 = 0 := by
    have h1 : Tendsto (fun z => ‖f z‖) (𝓝[≠] 0) (𝓝 ‖f 0‖) :=
      (hf.norm.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun z : ℝ => M * |z|) (𝓝[≠] 0) (𝓝 0) := by
      have hc : Continuous (fun z : ℝ => M * |z|) := continuous_const.mul continuous_abs
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using this
    have h3 : ∀ᶠ z in 𝓝[≠] (0 : ℝ), ‖f z‖ ≤ M * |z| := by
      filter_upwards [self_mem_nhdsWithin] with z hz using hlin z hz
    exact norm_le_zero_iff.1 (le_of_tendsto_of_tendsto h1 h2 h3)
  have hK : 0 ≤ M * (1 + R) := by positivity
  have hk := c03m_aux_kernel_integrable hp hp1
    (h := fun z => Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * f z) (K := M * (1 + R))
    ((by fun_prop : Continuous fun z : ℝ => Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))).mul hf).aestronglyMeasurable
    (fun z => ?_) (fun z => ?_)
  · refine hk.congr (Eventually.of_forall fun z => ?_)
    simp only; ring
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (c03m_aux_gauss_le η z hη)).trans ?_
    rcases eq_or_ne z 0 with rfl | hz
    · rw [hf0, norm_zero]; positivity
    · refine (hlin z hz).trans ?_
      have : M ≤ M * (1 + R) := by nlinarith
      gcongr
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (c03m_aux_gauss_le η z hη)).trans ?_
    rcases eq_or_ne z 0 with rfl | hz
    · rw [hf0, norm_zero]; positivity
    · by_cases hzR : |z| ≤ R
      · refine (hlin z hz).trans ?_
        nlinarith
      · rw [hsupp z (not_le.1 hzR), norm_zero]; positivity


/-- Symbol bounds of a linear combination. -/
lemma c03m_aux_SB_lin {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) {y z : ℝ}
    (hq : (y, z) ∈ W) {J S : ℕ} {c M α β : ℝ} (a b : ℂ)
    (h₁ : c03m_aux_SB F y z J S c M α β) (h₂ : c03m_aux_SB G y z J S c M α β) :
    c03m_aux_SB (fun w => a * F w + b * G w) y z J S ((‖a‖ + ‖b‖) * c) M α β := by
  have := c03m_aux_SB_add hW (contDiffOn_const.mul hF) (contDiffOn_const.mul hG) hq
    (c03m_aux_SB_smul a h₁) (c03m_aux_SB_smul b h₂)
  rw [add_mul]; exact this

/-- `∂_v` of a linear combination. -/
lemma c03m_aux_pd_lin {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) (v : ℝ × ℝ) (a b : ℂ)
    {w : ℝ × ℝ} (hw : w ∈ W) :
    c03m_aux_pd v (fun w => a * F w + b * G w) 1 w =
      a * c03m_aux_pd v F 1 w + b * c03m_aux_pd v G 1 w := by
  have hFd : DifferentiableAt ℝ F w := (hF.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hw)
  have hGd : DifferentiableAt ℝ G w := (hG.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hw)
  simp only [c03m_aux_pd]
  rw [fderiv_fun_add (hFd.const_mul a) (hGd.const_mul b), fderiv_const_mul hFd,
    fderiv_const_mul hGd]
  simp

/-- Symbol bounds of `∂_y` of a linear combination. -/
lemma c03m_aux_SB_pd_lin {W : Set (ℝ × ℝ)} (hW : IsOpen W) {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F W) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W) {y z : ℝ}
    (hq : (y, z) ∈ W) {J S : ℕ} {c M α β : ℝ} (a b : ℂ)
    (h₁ : c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) F 1) y z J S c M α β)
    (h₂ : c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) G 1) y z J S c M α β) :
    c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (fun w => a * F w + b * G w) 1) y z J S
      ((‖a‖ + ‖b‖) * c) M α β := by
  have hF1 := c03m_aux_pd_smooth hW ((1 : ℝ), (0 : ℝ)) hF 1
  have hG1 := c03m_aux_pd_smooth hW ((1 : ℝ), (0 : ℝ)) hG 1
  refine c03m_aux_SB_congr ?_ (c03m_aux_SB_lin hW hF1 hG1 hq a b h₁ h₂)
  filter_upwards [hW.mem_nhds hq] with w hw
  exact c03m_aux_pd_lin hW hF hG _ a b hw

lemma c03m_aux_SB_monoS {F : ℝ × ℝ → ℂ} {y z : ℝ} {J S S' : ℕ} {c M α β : ℝ}
    (h : c03m_aux_SB F y z J S c M α β) (hS : S' ≤ S) : c03m_aux_SB F y z J S' c M α β :=
  fun a ha b hb => h a ha b (hb.trans hS)

lemma c03m_aux_poly_lin {R Λ z : ℝ} {K₀ j : ℕ} (hK₀ : 1 ≤ K₀) (hΛ : 0 ≤ Λ) (hzR : |z| ≤ R) :
    ∑ l ∈ Finset.range (j + 1), |z| ^ K₀ * (Λ * |z|) ^ l ≤
      (∑ l ∈ Finset.range (j + 1), R ^ (K₀ - 1) * (Λ * R) ^ l) * |z| := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  have e : |z| ^ K₀ = |z| ^ (K₀ - 1) * |z| := by
    rw [← pow_succ]; congr 1; omega
  rw [e]
  have h1 : |z| ^ (K₀ - 1) ≤ R ^ (K₀ - 1) := pow_le_pow_left₀ (abs_nonneg _) hzR _
  have h2 : (Λ * |z|) ^ l ≤ (Λ * R) ^ l := pow_le_pow_left₀ (by positivity) (by gcongr) _
  calc |z| ^ (K₀ - 1) * |z| * (Λ * |z|) ^ l = (|z| ^ (K₀ - 1) * (Λ * |z|) ^ l) * |z| := by ring
    _ ≤ (R ^ (K₀ - 1) * (Λ * R) ^ l) * |z| := by
      have hR : 0 ≤ R := (abs_nonneg z).trans hzR
      exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (pow_nonneg (mul_nonneg hΛ
        (abs_nonneg _)) _) (pow_nonneg hR _)) (abs_nonneg _)


set_option maxHeartbeats 800000 in
/-- Generic homogeneous-IBP bound for `∫ e^{-ηz²}|z|^{-1-p} ∂_y^j(e^{iΦ}H)(y,z) dz` from symbol
bounds of `H` (order `K₀`, size `BH`) and of `∂_yΦ`, and the phase bounds of `Φ(y,·)`
(extracted from `c03_mult_parameter_ibp_bound`). -/
lemma c03m_aux_core_ibp (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀) (K₀ : ℕ)
    (hK₀ : 1 ≤ K₀) (j : ℕ) :
    ∃ S : ℕ, ∀ (cH cΦ : ℝ) (Cr : ℕ → ℝ), 0 ≤ cH → 0 ≤ cΦ → (∀ s, 0 ≤ Cr s) → ∃ C, 0 < C ∧
      ∀ (Y Λ BH t η y : ℝ) (T : Set ℝ) (Φr : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ),
      0 < Y → 0 < Λ → 0 ≤ BH → 0 < t → 0 ≤ η → y ∈ Ioo (Y / 2) (3 * Y) → IsCompact T →
      T ⊆ Ioo (Y / 4) (4 * Y) →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w => ((Φr w : ℝ) : ℂ))
        ((Ioo (Y / 2) (3 * Y) ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) →
      ContDiffOn ℝ (⊤ : ℕ∞) H
        ((Ioo (Y / 2) (3 * Y) ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' Ioo (Y / 4) (4 * Y)) →
      (∀ y' z', y' + t * z' ∉ T → H (y', z') = 0) →
      (∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → c₀⁻¹ * Λ ≤ |deriv (fun z => Φr (y, z)) z| ∧
        |deriv (fun z => Φr (y, z)) z| ≤ c₀ * Λ) →
      (∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → z ≠ 0 → ∀ s ≤ S,
        |iteratedDeriv s (fun z => 1 / deriv (fun z => Φr (y, z)) z) z| ≤
          Cr s * Λ⁻¹ * |z| ^ (-(s : ℝ))) →
      (∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → z ≠ 0 →
        c03m_aux_SB H y z j S cH (BH * |z| ^ K₀) Y⁻¹ |z|⁻¹) →
      (∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → z ≠ 0 →
        c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (fun w => ((Φr w : ℝ) : ℂ)) 1) y z j S cΦ
          (Λ * |z| * Y⁻¹) Y⁻¹ |z|⁻¹) →
      ‖∫ z : ℝ, Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) *
          iteratedDeriv j (fun y' => Complex.exp (Complex.I * ((Φr (y', z) : ℝ) : ℂ)) * H (y', z)) y‖ ≤
        C * BH * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ)) := by
  have hKl : ∀ l : ℕ, p < ((K₀ + l : ℕ) : ℝ) := by
    intro l
    have : (1 : ℝ) ≤ ((K₀ + l : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ K₀ + l by omega)
    linarith
  have hibp := fun l : ℕ => c03c_c03_ibp_homogeneous p ((K₀ + l : ℕ) : ℝ) c₀ hp hp1 (hKl l) hc₀
  choose s0 hs0 using hibp
  set S : ℕ := ∑ l ∈ Finset.range (j + 1), s0 l with hS
  have hsS : ∀ l ≤ j, s0 l ≤ S := fun l hl =>
    Finset.single_le_sum (f := s0) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  refine ⟨S, fun cH cΦ Cr hcH0 hcΦ0 hCr => ?_⟩
  set D : ℝ := (1 + 2 ^ (j + S) * cΦ) ^ j * cH with hD
  have hD0 : 0 ≤ D := by positivity
  set Cs : ℕ → ℝ := fun s => D + Cr s with hCs
  have hCl := fun l => hs0 l Cs
  choose Cl hCl0 hClb using hCl
  refine ⟨∑ l ∈ Finset.range (j + 1), Cl l + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun l _ => (hCl0 l).le) one_pos, ?_⟩
  intro Y Λ BH t η y T Φr H hY0 hΛ0 hB00 ht0 hη hy hTc hTU hΦs hHs hHT hφd hrecz hSBH hSBΦ
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  have hU : IsOpen U := isOpen_Ioo
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyU : y ∈ U := hVU hy
  set ℓ : ℝ × ℝ → ℝ := fun w => w.1 + t * w.2 with hℓ_def
  have hℓ : ContDiff ℝ (⊤ : ℕ∞) ℓ := by fun_prop
  set W : Set (ℝ × ℝ) := (V ×ˢ univ) ∩ ℓ ⁻¹' U with hW_def
  have hW : IsOpen W := (isOpen_Ioo.prod isOpen_univ).inter (hU.preimage hℓ.continuous)
  set Φ : ℝ × ℝ → ℂ := fun w => ((Φr w : ℝ) : ℂ) with hΦ_def
  set O : Set (ℝ × ℝ) := W ∩ ℓ ⁻¹' Tᶜ with hO_def
  have hO : IsOpen O := hW.inter (hTc.isClosed.isOpen_compl.preimage hℓ.continuous)
  have hH0 : ∀ w ∈ O, H w = 0 := fun w hw => hHT w.1 w.2 hw.2
  have hEv := c03m_aux_E_vanish hO Φ hH0
  have hEs := c03m_aux_E_smooth hW hΦs hHs
  set Uz : Set ℝ := {z | y + t * z ∈ U} with hUz
  have hUzo : IsOpen Uz := hU.preimage (by fun_prop)
  have hyzW : ∀ z ∈ Uz, (y, z) ∈ W := fun z hz => ⟨⟨hy, trivial⟩, hz⟩
  set β : ℕ → ℝ → ℂ := fun l z => if y + t * z ∈ U then c03m_aux_E Φ H j l (y, z) else 0
    with hβ
  have hβ_eq : ∀ l, ∀ z ∈ Uz, β l =ᶠ[𝓝 z] fun z' => c03m_aux_E Φ H j l (y, z') := by
    intro l z hz
    filter_upwards [hUzo.mem_nhds hz] with z' hz'
    simp only [hβ]
    exact if_pos hz'
  have hβ0 : ∀ l, ∀ z, y + t * z ∉ T → β l =ᶠ[𝓝 z] fun _ => 0 := by
    intro l z hz
    have hopen : IsOpen {z' : ℝ | y + t * z' ∉ T} :=
      hTc.isClosed.isOpen_compl.preimage (by fun_prop)
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    simp only [hβ]
    split_ifs with h
    · exact hEv j l (y, z') ⟨hyzW z' h, hz'⟩
    · rfl
  have hEyz : ∀ l, ContDiffOn ℝ (⊤ : ℕ∞) (fun z' => c03m_aux_E Φ H j l (y, z')) Uz :=
    fun l => (hEs j l).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun z hz => hyzW z hz)
  have hβs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (β l) := by
    intro l
    refine c03m_aux_smooth_of_local hUzo ?_ ?_
    · exact (hEyz l).congr (fun z hz => by simp only [hβ]; exact if_pos hz)
    · intro z hz; exact hβ0 l z (fun h => hz (hTU h))
  have hβsupp : ∀ l, tsupport (β l) ⊆ {z | y + t * z ∈ T} := by
    intro l
    refine closure_minimal (fun z hz => ?_) (hTc.isClosed.preimage (by fun_prop))
    by_contra hc
    exact hz ((hβ0 l z hc).self_of_nhds)
  have htsU : ∀ l, tsupport (β l) ⊆ Uz := fun l => (hβsupp l).trans (fun z hz => hTU hz)
  have hβc : ∀ l, HasCompactSupport (β l) := by
    intro l
    refine HasCompactSupport.intro (hTc.image (by fun_prop : Continuous fun x : ℝ => (x - y) / t))
      fun z hz => ?_
    have hz' : y + t * z ∉ T := fun h => hz ⟨y + t * z, h, by field_simp; ring⟩
    exact (hβ0 l z hz').self_of_nhds
  have hYi : 0 ≤ Y⁻¹ := by positivity
  have hSBz : ∀ z ∈ Uz, z ≠ 0 → ∀ l, c03m_aux_SB (c03m_aux_E Φ H j l) y z 0 S D
      (BH * |z| ^ K₀ * (Λ * |z|) ^ l * Y⁻¹ ^ j) Y⁻¹ |z|⁻¹ := by
    intro z hz hz0 l
    have hz' : 0 < |z| := abs_pos.2 hz0
    have := c03m_aux_E_SB hW hΦs hHs (hyzW z hz) (L := Λ * |z|) hcH0 hcΦ0 (by positivity)
      (by positivity) hYi (by positivity) (hSBH z hz hz0) (hSBΦ z hz hz0) j le_rfl l
    rwa [Nat.sub_self] at this
  have hβd : ∀ l, ∀ z ∈ Uz, z ≠ 0 → ∀ s ≤ S, ‖iteratedDeriv s (β l) z‖ ≤
      D * (BH * Λ ^ l * Y⁻¹ ^ j) * |z| ^ (((K₀ + l : ℕ) : ℝ) - s) := by
    intro l z hz hz0 s hs
    have hz' : 0 < |z| := abs_pos.2 hz0
    rw [(hβ_eq l z hz).iteratedDeriv_eq]
    have h1 := hSBz z hz hz0 l 0 le_rfl s hs
    have e : c03m_aux_M (c03m_aux_E Φ H j l) 0 s y z =
        iteratedDeriv s (fun z' => c03m_aux_E Φ H j l (y, z')) z := by
      simp [c03m_aux_M]
    rw [e] at h1
    refine h1.trans (le_of_eq ?_)
    rw [Real.rpow_sub hz', Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow,
      mul_pow, pow_add]
    ring
  -- the phase on `Uz`
  have hφs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Φr (y, z)) Uz := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ((Φr (y, z) : ℝ) : ℂ)) Uz :=
      hΦs.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun z hz => hyzW z hz)
    have := Complex.reCLM.contDiff.comp_contDiffOn h1
    simpa [Function.comp_def] using this
  have h0Uz : (0 : ℝ) ∈ Uz := by
    show y + t * 0 ∈ U
    simpa using hyU
  have hβ00 : ∀ l ≤ j, β l 0 = 0 := by
    intro l hl
    have he : (0 : ℝ) < ((K₀ + l : ℕ) : ℝ) - ((0 : ℕ) : ℝ) := by
      have := hKl l; push_cast at this ⊢; linarith
    have h1 : Tendsto (fun z => ‖β l z‖) (𝓝[≠] 0) (𝓝 ‖β l 0‖) :=
      ((hβs l).continuous.norm.tendsto 0).mono_left nhdsWithin_le_nhds
    have hc : Continuous (fun z : ℝ =>
        D * (BH * Λ ^ l * Y⁻¹ ^ j) * |z| ^ (((K₀ + l : ℕ) : ℝ) - ((0 : ℕ) : ℝ))) :=
      continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr he.le))
    have h2 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    rw [abs_zero, Real.zero_rpow he.ne', mul_zero] at h2
    have h3 : ∀ᶠ z in 𝓝[≠] (0 : ℝ), ‖β l z‖ ≤
        D * (BH * Λ ^ l * Y⁻¹ ^ j) * |z| ^ (((K₀ + l : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hUzo.mem_nhds h0Uz)]
        with z hz0 hz
      have := hβd l z hz hz0 0 (Nat.zero_le _)
      rwa [iteratedDeriv_zero] at this
    exact norm_le_zero_iff.1 (le_of_tendsto_of_tendsto h1 h2 h3)
  have hintl : ∀ l ≤ j, Integrable (fun z : ℝ =>
      Complex.exp (Complex.I * (Φr (y, z) : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * β l z / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
    intro l hl
    obtain ⟨M, hM0, hM⟩ := c03m_aux_lip_bound ((hβs l).of_le (by exact_mod_cast le_top)) (hβc l)
    have hcont : Continuous (fun z => β l z * Complex.exp (Complex.I * (Φr (y, z) : ℂ))) :=
      c03c_aux_cont_mul_exp hUzo (hβs l).continuous (htsU l) hφs.continuousOn
    have hcont2 : Continuous (fun z : ℝ => β l z *
        Complex.exp (Complex.I * (Φr (y, z) : ℂ)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))) := hcont.mul (by fun_prop)
    have hnb : ∀ z, ‖β l z * Complex.exp (Complex.I * (Φr (y, z) : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ))‖ ≤ ‖β l z‖ := by
      intro z
      rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (c03m_aux_gauss_le η z hη)
    have hk := c03m_aux_kernel_integrable hp hp1 hcont2.aestronglyMeasurable (K := M)
      (fun z => (hnb z).trans (by
        have := (hM 0 z).1
        rwa [zero_add, hβ00 l hl, sub_zero] at this))
      (fun z => (hnb z).trans (by
        have := (hM 0 z).2
        rwa [zero_add, hβ00 l hl, sub_zero] at this))
    refine hk.congr (Eventually.of_forall fun z => ?_)
    simp only
    ring
  have hint : ∀ z : ℝ, Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) *
      iteratedDeriv j (fun y' => Complex.exp (Complex.I * ((Φr (y', z) : ℝ) : ℂ)) * H (y', z)) y =
      ∑ l ∈ Finset.range (j + 1), Complex.exp (Complex.I * (Φr (y, z) : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * β l z / ((|z| ^ (1 + p) : ℝ) : ℂ) := by
    intro z
    by_cases hz : y + t * z ∈ U
    · have h1 := c03m_aux_E_identity hW hΦs hHs j (y, z) (hyzW z hz)
      dsimp only at h1
      rw [h1, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hβz : β l z = c03m_aux_E Φ H j l (y, z) := by simp only [hβ]; exact if_pos hz
      rw [hβz]
      simp only [hΦ_def]
      ring
    · have hz' : y + t * z ∉ T := fun h => hz (hTU h)
      have hopen : IsOpen {y' : ℝ | y' + t * z ∉ T} :=
        hTc.isClosed.isOpen_compl.preimage (by fun_prop)
      have hev : (fun y' => Complex.exp (Complex.I * ((Φr (y', z) : ℝ) : ℂ)) * H (y', z)) =ᶠ[𝓝 y]
          fun _ => 0 := by
        filter_upwards [hopen.mem_nhds hz'] with y' hy'
        rw [hHT y' z hy', mul_zero]
      rw [hev.iteratedDeriv_eq]
      have hβz : ∀ l, β l z = 0 := fun l => by simp only [hβ]; exact if_neg hz
      simp [hβz, iteratedDeriv_const]
  rw [integral_congr_ae (Filter.Eventually.of_forall hint),
    integral_finsetSum _ (fun l hl => hintl l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)))]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ l ∈ Finset.range (j + 1), ‖∫ z : ℝ,
      Complex.exp (Complex.I * (Φr (y, z) : ℂ)) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * β l z / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ ≤
      Cl l * (BH * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) := by
    intro l hl
    have hl' : l ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have hB : 0 ≤ BH * Λ ^ l * Y⁻¹ ^ j := by positivity
    obtain ⟨hbd, -⟩ := hClb l Λ (BH * Λ ^ l * Y⁻¹ ^ j) Uz (β l) (fun z => Φr (y, z))
      hΛ0 hB hUzo (hβs l) (hβc l) (htsU l) hφs
      (fun z hz hz0 s hs => (hβd l z hz hz0 s (hs.trans (hsS l hl'))).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by rw [hCs]; have := hCr s; simp only; linarith)
          hB) (Real.rpow_nonneg (abs_nonneg _) _)))
      (fun z hz => hφd z hz)
      (fun z hz hz0 s hs => (hrecz z hz hz0 s (hs.trans (hsS l hl'))).trans (by
        have h0 : 0 ≤ Λ⁻¹ * |z| ^ (-(s : ℝ)) := by positivity
        have : Cr s ≤ Cs s := by rw [hCs]; simp only; linarith
        nlinarith))
    refine (hbd η hη).trans (le_of_eq ?_)
    rw [Nat.cast_add, show p - ((K₀ : ℝ) + (l : ℝ)) = (p - K₀) - l by ring,
      Real.rpow_sub hΛ0, Real.rpow_natCast]
    field_simp
  have hS0 : 0 ≤ BH * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ)) := by positivity
  calc _ ≤ ∑ l ∈ Finset.range (j + 1), Cl l * (BH * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (∑ l ∈ Finset.range (j + 1), Cl l) * (BH * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) := by
        rw [Finset.sum_mul]
    _ ≤ (∑ l ∈ Finset.range (j + 1), Cl l + 1) * (BH * Y⁻¹ ^ j * Λ ^ (p - (K₀ : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) hS0
    _ = _ := by ring


lemma c03m_aux_sigma_deriv {O : Set ℝ} (hO : IsOpen O) {y : ℝ} (hy : y ∈ O) {f₀ f₁ : ℝ → ℝ}
    {h₀ h₁ : ℝ → ℂ} (hf₀ : ContDiffOn ℝ (⊤ : ℕ∞) f₀ O) (hf₁ : ContDiffOn ℝ (⊤ : ℕ∞) f₁ O)
    (hh₀ : ContDiffOn ℝ (⊤ : ℕ∞) h₀ O) (hh₁ : ContDiffOn ℝ (⊤ : ℕ∞) h₁ O) (j : ℕ) (σ : ℝ) :
    HasDerivAt (fun σ' : ℝ => iteratedDeriv j (fun y' =>
        Complex.exp (Complex.I * (((1 - σ') * f₀ y' + σ' * f₁ y' : ℝ) : ℂ)) *
          (((1 - σ' : ℝ) : ℂ) * h₀ y' + (σ' : ℂ) * h₁ y')) y)
      (iteratedDeriv j (fun y' =>
        Complex.exp (Complex.I * (((1 - σ) * f₀ y' + σ * f₁ y' : ℝ) : ℂ)) *
          ((h₁ y' - h₀ y') + Complex.I * ((f₁ y' - f₀ y' : ℝ) : ℂ) *
            (((1 - σ : ℝ) : ℂ) * h₀ y' + (σ : ℂ) * h₁ y'))) y) σ := by
  set W : Set (ℝ × ℝ) := O ×ˢ univ with hW_def
  have hW : IsOpen W := hO.prod isOpen_univ
  have hfst : ∀ {g : ℝ → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) g O →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((g w.1 : ℝ) : ℂ)) W := fun hg =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hg.comp contDiff_fst.contDiffOn
      (fun w hw => hw.1))
  have hfstC : ∀ {g : ℝ → ℂ}, ContDiffOn ℝ (⊤ : ℕ∞) g O →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => g w.1) W := fun hg =>
    hg.comp contDiff_fst.contDiffOn (fun w hw => hw.1)
  have hsnd : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((w.2 : ℝ) : ℂ)) W :=
    (Complex.ofRealCLM.contDiff.comp contDiff_snd).contDiffOn
  set G : ℝ × ℝ → ℂ := fun w => Complex.exp (Complex.I * (((1 - w.2) * f₀ w.1 + w.2 * f₁ w.1 : ℝ) : ℂ)) *
    (((1 - w.2 : ℝ) : ℂ) * h₀ w.1 + (w.2 : ℂ) * h₁ w.1) with hG_def
  set G' : ℝ × ℝ → ℂ := fun w => Complex.exp (Complex.I * (((1 - w.2) * f₀ w.1 + w.2 * f₁ w.1 : ℝ) : ℂ)) *
    ((h₁ w.1 - h₀ w.1) + Complex.I * ((f₁ w.1 - f₀ w.1 : ℝ) : ℂ) *
      (((1 - w.2 : ℝ) : ℂ) * h₀ w.1 + (w.2 : ℂ) * h₁ w.1)) with hG'_def
  have hphase : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ =>
      (((1 - w.2) * f₀ w.1 + w.2 * f₁ w.1 : ℝ) : ℂ)) W := by
    have : (fun w : ℝ × ℝ => (((1 - w.2) * f₀ w.1 + w.2 * f₁ w.1 : ℝ) : ℂ)) =
        fun w => (1 - ((w.2 : ℝ) : ℂ)) * ((f₀ w.1 : ℝ) : ℂ) + ((w.2 : ℝ) : ℂ) * ((f₁ w.1 : ℝ) : ℂ) := by
      funext w; push_cast; ring
    rw [this]
    exact ((contDiffOn_const.sub hsnd).mul (hfst hf₀)).add (hsnd.mul (hfst hf₁))
  have hamp : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ =>
      (((1 - w.2 : ℝ) : ℂ) * h₀ w.1 + (w.2 : ℂ) * h₁ w.1)) W := by
    have : (fun w : ℝ × ℝ => (((1 - w.2 : ℝ) : ℂ) * h₀ w.1 + (w.2 : ℂ) * h₁ w.1)) =
        fun w => (1 - ((w.2 : ℝ) : ℂ)) * h₀ w.1 + ((w.2 : ℝ) : ℂ) * h₁ w.1 := by
      funext w; push_cast; ring
    rw [this]
    exact ((contDiffOn_const.sub hsnd).mul (hfstC hh₀)).add (hsnd.mul (hfstC hh₁))
  have hGs : ContDiffOn ℝ (⊤ : ℕ∞) G W :=
    (Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hphase)).mul hamp
  have hG's : ContDiffOn ℝ (⊤ : ℕ∞) G' W :=
    (Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hphase)).mul
      (((hfstC hh₁).sub (hfstC hh₀)).add ((contDiffOn_const.mul (hfst (hf₁.sub hf₀))).mul hamp))
  -- `∂_σ G = G'`
  have hA : ∀ w ∈ W, c03m_aux_pd ((0 : ℝ), (1 : ℝ)) G 1 w = G' w := by
    intro w hw
    rw [← c03m_aux_pdz_eq hW hGs 1 w hw, iteratedDeriv_one]
    have h1 : HasDerivAt (fun s : ℝ => (((1 - s) * f₀ w.1 + s * f₁ w.1 : ℝ) : ℂ))
        (((f₁ w.1 - f₀ w.1 : ℝ) : ℂ)) w.2 := by
      have hr : HasDerivAt (fun s : ℝ => (1 - s) * f₀ w.1 + s * f₁ w.1)
          ((-1) * f₀ w.1 + 1 * f₁ w.1) w.2 :=
        (((hasDerivAt_id' w.2).const_sub 1).mul_const (f₀ w.1)).fun_add
          ((hasDerivAt_id' w.2).mul_const (f₁ w.1))
      exact hr.ofReal_comp.congr_deriv (by push_cast; ring)
    have h2 : HasDerivAt (fun s : ℝ => (((1 - s : ℝ) : ℂ) * h₀ w.1 + (s : ℂ) * h₁ w.1))
        (h₁ w.1 - h₀ w.1) w.2 := by
      have hr : HasDerivAt (fun s : ℝ => (((1 - s : ℝ) : ℂ)))  (((-1 : ℝ) : ℂ)) w.2 :=
        ((hasDerivAt_id' w.2).const_sub 1).ofReal_comp
      have hr2 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) (((1 : ℝ) : ℂ)) w.2 :=
        (hasDerivAt_id' w.2).ofReal_comp
      exact ((hr.mul_const (h₀ w.1)).fun_add (hr2.mul_const (h₁ w.1))).congr_deriv
        (by push_cast; ring)
    have h3 : HasDerivAt (fun z' => G (w.1, z')) _ w.2 := ((h1.const_mul Complex.I).cexp).fun_mul h2
    rw [h3.deriv]
    simp only [hG'_def]
    ring
  have hB := c03m_aux_pd_comm hW hGs ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) j (y, σ) ⟨hy, trivial⟩
  rw [c03m_aux_pd_congr hW _ hA j (y, σ) ⟨hy, trivial⟩,
    ← c03m_aux_pdy_eq hW hG's j (y, σ) ⟨hy, trivial⟩] at hB
  have hfun : (fun σ' : ℝ => iteratedDeriv j (fun y' =>
        Complex.exp (Complex.I * (((1 - σ') * f₀ y' + σ' * f₁ y' : ℝ) : ℂ)) *
          (((1 - σ' : ℝ) : ℂ) * h₀ y' + (σ' : ℂ) * h₁ y')) y) =
      fun σ' => c03m_aux_pd ((1 : ℝ), (0 : ℝ)) G j (y, σ') := by
    funext σ'
    exact c03m_aux_pdy_eq hW hGs j (y, σ') ⟨hy, trivial⟩
  rw [hfun]
  have hd : DifferentiableAt ℝ (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) G j) (y, σ) :=
    ((c03m_aux_pd_smooth hW _ hGs j).differentiableOn (by simp)).differentiableAt
      (hW.mem_nhds ⟨hy, trivial⟩)
  have hd' : DifferentiableAt ℝ (fun σ' => c03m_aux_pd ((1 : ℝ), (0 : ℝ)) G j (y, σ')) σ :=
    hd.comp σ ((differentiableAt_const _).prodMk differentiableAt_id)
  convert hd'.hasDerivAt using 1
  rw [← iteratedDeriv_one, c03m_aux_pdz_eq hW (c03m_aux_pd_smooth hW _ hGs j) 1 (y, σ)
    ⟨hy, trivial⟩]
  exact hB

lemma c03m_aux_bt_vanish {Y : ℝ} (a : ℝ → ℂ) {Ψ : ℝ → ℝ}
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y))) (N r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    {y t z : ℝ} (h : y + t * z ∉ tsupport (iteratedDeriv r a)) :
    c03_mult_bt Y a Ψ N r q y t z = 0 := by
  rw [c03m_aux_bt_eq a hΨ N r q, image_eq_zero_of_notMem_tsupport h]
  simp

/-- The `σ`-derivative of the interpolated differentiated integrand at a fixed `z`. -/
lemma c03m_aux_diff_sigma {Y t y z : ℝ} (hY : 0 < Y) (hy : y ∈ Ioo (Y / 2) (3 * Y)) {a₀ a₁ : ℝ → ℂ}
    {Ψ₀ Ψ₁ : ℝ → ℝ} (has₀ : tsupport a₀ ⊆ Ioo (Y / 4) (4 * Y))
    (has₁ : tsupport a₁ ⊆ Ioo (Y / 4) (4 * Y))
    (hΨ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ₀ (Ioo (Y / 4) (4 * Y)))
    (hΨ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ₁ (Ioo (Y / 4) (4 * Y))) (N r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hH₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2)
      (Ioo (Y / 2) (3 * Y) ×ˢ univ))
    (hH₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2)
      (Ioo (Y / 2) (3 * Y) ×ˢ univ)) (j : ℕ) (σ : ℝ) :
    HasDerivAt (fun σ' : ℝ => iteratedDeriv j (fun y' =>
        Complex.exp (Complex.I * (((1 - σ') * c03_mult_phit Ψ₀ y' t z +
          σ' * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
          (((1 - σ' : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
            (σ' : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z)) y)
      (iteratedDeriv j (fun y' =>
        Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y' t z +
          σ * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
          (c03_mult_bt Y a₁ Ψ₁ N r q y' t z - c03_mult_bt Y a₀ Ψ₀ N r q y' t z)) y +
       iteratedDeriv j (fun y' =>
        Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y' t z +
          σ * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
          (Complex.I * ((c03_mult_phit Ψ₁ y' t z - c03_mult_phit Ψ₀ y' t z : ℝ) : ℂ) *
            (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
              (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z))) y) σ := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  by_cases hz : y + t * z ∈ U
  · set O : Set ℝ := V ∩ (fun y' => y' + t * z) ⁻¹' U with hO_def
    have hO : IsOpen O := isOpen_Ioo.inter (isOpen_Ioo.preimage (by fun_prop))
    have hyO : y ∈ O := ⟨hy, hz⟩
    have hmap : ∀ y' ∈ O, ((y', z) : ℝ × ℝ) ∈ (V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U :=
      fun y' hy' => ⟨⟨hy'.1, trivial⟩, hy'.2⟩
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y' : ℝ => ((y', z) : ℝ × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    have hf : ∀ {Ψ : ℝ → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) Ψ U →
        ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => c03_mult_phit Ψ y' t z) O := by
      intro Ψ hΨ
      have h := ContDiffOn.comp (c03m_aux_phit_smooth hΨ t hVU) hm.contDiffOn hmap
      exact h
    have hh : ∀ {H : ℝ × ℝ → ℂ}, ContDiffOn ℝ (⊤ : ℕ∞) H (V ×ˢ univ) →
        ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => H (y', z)) O := by
      intro H hH
      have hmap' : MapsTo (fun y' : ℝ => ((y', z) : ℝ × ℝ)) O (V ×ˢ univ) :=
        fun y' hy' => ⟨hy'.1, trivial⟩
      have h := ContDiffOn.comp hH hm.contDiffOn hmap'
      exact h
    have h1 := c03m_aux_sigma_deriv hO hyO (hf hΨ₀) (hf hΨ₁) (hh hH₀) (hh hH₁) j σ
    convert h1 using 1
    have hc : ∀ {g : ℝ → ℂ}, ContDiffOn ℝ (⊤ : ℕ∞) g O → ContDiffAt ℝ j g y := fun hg =>
      (hg.contDiffAt (hO.mem_nhds hyO)).of_le (by exact_mod_cast le_top)
    have hE : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => Complex.exp (Complex.I *
        (((1 - σ) * c03_mult_phit Ψ₀ y' t z + σ * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ))) O :=
      Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul
        (Complex.ofRealCLM.contDiff.comp_contDiffOn
          ((contDiffOn_const.mul (hf hΨ₀)).add (contDiffOn_const.mul (hf hΨ₁)))))
    have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' =>
        ((c03_mult_phit Ψ₁ y' t z - c03_mult_phit Ψ₀ y' t z : ℝ) : ℂ)) O :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((hf hΨ₁).sub (hf hΨ₀))
    have hHs : ContDiffOn ℝ (⊤ : ℕ∞) (fun y' => (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
        (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z)) O :=
      (contDiffOn_const.mul (hh hH₀)).add (contDiffOn_const.mul (hh hH₁))
    rw [← iteratedDeriv_fun_add (hc (hE.mul ((hh hH₁).sub (hh hH₀))))
      (hc (hE.mul ((contDiffOn_const.mul hD).mul hHs)))]
    congr 1
    funext y'
    ring
  · have hT₀ : y + t * z ∉ tsupport (iteratedDeriv r a₀) := fun h =>
      hz (((c03m_aux_tsupport_iteratedDeriv a₀ r).trans has₀) h)
    have hT₁ : y + t * z ∉ tsupport (iteratedDeriv r a₁) := fun h =>
      hz (((c03m_aux_tsupport_iteratedDeriv a₁ r).trans has₁) h)
    have hopen : IsOpen {y' : ℝ | y' + t * z ∉ tsupport (iteratedDeriv r a₀) ∧
        y' + t * z ∉ tsupport (iteratedDeriv r a₁)} :=
      ((isClosed_tsupport _).isOpen_compl.preimage (by fun_prop)).inter
        ((isClosed_tsupport _).isOpen_compl.preimage (by fun_prop))
    have hv0 : ∀ G : ℝ → ℂ, (∀ y', y' + t * z ∉ tsupport (iteratedDeriv r a₀) →
        y' + t * z ∉ tsupport (iteratedDeriv r a₁) → G y' = 0) → iteratedDeriv j G y = 0 := by
      intro G hG
      have hev : G =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds ⟨hT₀, hT₁⟩] with y' hy' using hG y' hy'.1 hy'.2
      rw [hev.iteratedDeriv_eq]; simp
    have hb : ∀ y', y' + t * z ∉ tsupport (iteratedDeriv r a₀) →
        y' + t * z ∉ tsupport (iteratedDeriv r a₁) →
        c03_mult_bt Y a₀ Ψ₀ N r q y' t z = 0 ∧ c03_mult_bt Y a₁ Ψ₁ N r q y' t z = 0 :=
      fun y' h0 h1 => ⟨c03m_aux_bt_vanish a₀ hΨ₀ N r q h0, c03m_aux_bt_vanish a₁ hΨ₁ N r q h1⟩
    have e : (fun σ' : ℝ => iteratedDeriv j (fun y' =>
        Complex.exp (Complex.I * (((1 - σ') * c03_mult_phit Ψ₀ y' t z +
          σ' * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
          (((1 - σ' : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
            (σ' : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z)) y) = fun _ => 0 := by
      funext σ'
      exact hv0 _ fun y' h0 h1 => by rw [(hb y' h0 h1).1, (hb y' h0 h1).2]; ring
    rw [e, hv0 _ (fun y' h0 h1 => by rw [(hb y' h0 h1).1, (hb y' h0 h1).2]; ring),
      hv0 _ (fun y' h0 h1 => by rw [(hb y' h0 h1).1, (hb y' h0 h1).2]; ring), add_zero]
    exact hasDerivAt_const _ _


set_option maxHeartbeats 800000 in
/-- Symbol bounds at `(y,z)` of the two amplitudes, of their difference, of the phase
difference and of `∂_y` of the two phases, as used for the difference estimate. -/
lemma c03m_aux_diff_SBs (c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ) (hN : 1 ≤ N) (r : ℕ)
    (q : Fin (2 * N - 1) → ℕ) (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) (j S : ℕ)
    (Ck : ℕ → ℝ) :
    ∃ cH cD cΦ : ℝ, 0 ≤ cH ∧ 0 ≤ cD ∧ 0 ≤ cΦ ∧
      ∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ →
      c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + S + 4) a₀ Ψ₀ →
      c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + S + 4) a₁ Ψ₁ →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ 2 * N + j + S + 4,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
      ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ z : ℝ, y + t * z ∈ Ioo (Y / 4) (4 * Y) →
        z ≠ 0 →
        c03m_aux_SB (fun w : ℝ × ℝ => c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) y z j S cH
          (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) Y⁻¹ |z|⁻¹ ∧
        c03m_aux_SB (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2) y z j S cH
          (c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) Y⁻¹ |z|⁻¹ ∧
        c03m_aux_SB (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 -
            c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) y z j S cD
          (δ * c03_mult_size N q Y Λ A t * |z| ^ (2 * N - 1 + c03_mult_q1 q)) Y⁻¹ |z|⁻¹ ∧
        c03m_aux_SB (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₁ w.1 t w.2 -
            c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ)) y z j S cD (δ * Y⁻¹ * |z|) Y⁻¹ |z|⁻¹ ∧
        c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ))
            (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ)) 1) y z j S cΦ
          (Λ * |z| * Y⁻¹) Y⁻¹ |z|⁻¹ ∧
        c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ))
            (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ)) 1) y z j S cΦ
          (Λ * |z| * Y⁻¹) Y⁻¹ |z|⁻¹ := by
  set K₀ : ℕ := 2 * N - 1 + c03_mult_q1 q with hK₀
  have hamp := fun a' b' : ℕ => c03_mult_amplitude_symbol c₀ hc₀ N hN r q hrq a' b' Ck
  choose Camp hCamp0 hampb using hamp
  have hdif := fun a' b' : ℕ => c03_mult_difference_symbols c₀ hc₀ N hN r q hrq a' b' Ck
  choose Cdif hCdif0 hdifb using hdif
  set cH : ℝ := ∑ a' ∈ Finset.range (j + 1), ∑ b' ∈ Finset.range (S + 1), Camp a' b' with hcH_def
  set cD : ℝ := ∑ a' ∈ Finset.range (j + 1), ∑ b' ∈ Finset.range (S + 1), Cdif a' b' with hcD_def
  have hsum : ∀ (F : ℕ → ℕ → ℝ), (∀ a b, 0 < F a b) → ∀ a' ≤ j, ∀ b' ≤ S,
      F a' b' ≤ ∑ a ∈ Finset.range (j + 1), ∑ b ∈ Finset.range (S + 1), F a b := by
    intro F hF a' ha b' hb
    calc F a' b' ≤ ∑ b'' ∈ Finset.range (S + 1), F a' b'' :=
          Finset.single_le_sum (f := fun b'' => F a' b'') (fun i _ => (hF a' i).le)
            (Finset.mem_range.2 (by omega))
      _ ≤ _ := Finset.single_le_sum (f := fun a'' => ∑ b'' ∈ Finset.range (S + 1), F a'' b'')
            (fun i _ => Finset.sum_nonneg fun k _ => (hF i k).le) (Finset.mem_range.2 (by omega))
  have hcH0 : 0 ≤ cH := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => (hCamp0 i k).le
  have hcD0 : 0 ≤ cD := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => (hCdif0 i k).le
  set CS : ℝ := ∑ k ∈ Finset.range (2 * N + j + S + 5), |Ck k| + 1 with hCS
  have hCS1 : 1 ≤ CS := by
    have : 0 ≤ ∑ k ∈ Finset.range (2 * N + j + S + 5), |Ck k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hCk : ∀ k < 2 * N + j + S + 5, Ck k ≤ CS := by
    intro k hk
    have := Finset.single_le_sum (f := fun k => |Ck k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hk)
    linarith [le_abs_self (Ck k)]
  set cΦ : ℝ := 2 ^ (j + S + 1) * CS + 4 ^ S * CS with hcΦ
  have hcΦ0 : 0 ≤ cΦ := by positivity
  refine ⟨cH, cD, cΦ, hcH0, hcD0, hcΦ0, ?_⟩
  intro Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ hyp₀ hyp₁ hdiff y hyI t ht z hz hz0
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hy : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
  have hz' : 0 < |z| := abs_pos.2 hz0
  have hzi : 0 ≤ |z|⁻¹ := by positivity
  have hYi : 0 ≤ Y⁻¹ := by positivity
  have hrp : ∀ k : ℕ, Y ^ (-(k : ℝ)) = Y⁻¹ ^ k := fun k => by
    rw [Real.rpow_neg hY0.le, Real.rpow_natCast, inv_pow]
  set B0 : ℝ := c03_mult_size N q Y Λ A t with hB0
  have hB00 : 0 ≤ B0 := c03m_aux_size_nonneg N q hY0 hΛ0.le hA.le ht0.le
  have hHb : ∀ (a : ℝ → ℂ) (Ψ : ℝ → ℝ), c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + S + 4) a Ψ →
      c03m_aux_SB (fun w : ℝ × ℝ => c03_mult_bt Y a Ψ N r q w.1 t w.2) y z j S cH
        (B0 * |z| ^ K₀) Y⁻¹ |z|⁻¹ := by
    intro a Ψ hyp a' ha' b' hb'
    have h1 := ((hampb a' b' Y Λ A a Ψ hY hΛ hA (c03m_aux_hyp_mono (by omega) hyp) t ht).2 y
      hy).2.2.2 z hz0
    have e : c03m_aux_M (fun w : ℝ × ℝ => c03_mult_bt Y a Ψ N r q w.1 t w.2) a' b' y z =
        iteratedDeriv a' (fun y' => iteratedDeriv b' (c03_mult_bt Y a Ψ N r q y' t) z) y := rfl
    rw [e]
    refine h1.trans ?_
    rw [hrp, Real.rpow_sub hz', Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
    have hc := hsum Camp hCamp0 a' ha' b' hb'
    have : 0 ≤ B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b') := by positivity
    calc Camp a' b' * B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')
        = Camp a' b' * (B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')) := by ring
      _ ≤ cH * (B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')) := mul_le_mul_of_nonneg_right hc this
      _ = _ := by ring
  have hΦb : ∀ Ψ : ℝ → ℝ, c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + S + 4) a₀ Ψ ∨
      c03_mult_hyp Y Λ A c₀ Ck (2 * N + j + S + 4) a₁ Ψ →
      c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ))
        (fun w : ℝ × ℝ => ((c03_mult_phit Ψ w.1 t w.2 : ℝ) : ℂ)) 1) y z j S cΦ
        (Λ * |z| * Y⁻¹) Y⁻¹ |z|⁻¹ := by
    intro Ψ hyp
    have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)) := by
      rcases hyp with h | h
      · exact h.2.2.1
      · exact h.2.2.1
    have hb : ∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ 2 * N + j + S + 4,
        |iteratedDeriv k (deriv Ψ) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ)) := by
      intro x hx k hk
      rcases hyp with h | h
      · exact ((h.2.2.2 x hx).2.2 k hk).1
      · exact ((h.2.2.2 x hx).2.2 k hk).1
    set U := Ioo (Y / 4) (4 * Y)
    set V := Ioo (Y / 2) (3 * Y)
    have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    set W : Set (ℝ × ℝ) := (V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U with hW_def
    have hW : IsOpen W := (isOpen_Ioo.prod isOpen_univ).inter (isOpen_Ioo.preimage (by fun_prop))
    have hΦs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((c03_mult_phit Ψ w.1 t w.2 : ℝ) : ℂ)) W :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (c03m_aux_phit_smooth hΨ t hVU)
    intro a' ha' b' hb'
    rw [c03m_aux_M_dy hW hΦs a' b' ⟨⟨hy, trivial⟩, hz⟩]
    have hbd : ∀ x ∈ U, ∀ k ≤ (a' + 1) + b',
        |iteratedDeriv k (deriv Ψ) x| ≤ CS * Λ * Y⁻¹ ^ k := by
      intro x hx k hk
      have h1 := hb x hx k (by omega)
      rw [hrp] at h1
      exact h1.trans (by gcongr; exact hCk k (by omega))
    obtain ⟨-, h2⟩ := c03m_aux_phit_M hY0 hΨ (j := a' + 1) (s := b') hbd (by linarith)
      hΛ0.le ht0 ht1 hy hz hz0
    refine h2.trans ?_
    have e1 : (2 : ℝ) ^ (a' + 1 + b') ≤ 2 ^ (j + S + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e2 : (4 : ℝ) ^ b' ≤ 4 ^ S := pow_le_pow_right₀ (by norm_num) hb'
    have hC : 2 ^ (a' + 1 + b') * CS + 4 ^ b' * CS ≤ cΦ := by
      rw [hcΦ]; gcongr
    have : 0 ≤ Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b') := by positivity
    calc (2 ^ (a' + 1 + b') * CS + 4 ^ b' * CS) * Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')
        = (2 ^ (a' + 1 + b') * CS + 4 ^ b' * CS) * (Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')) := by
          ring
      _ ≤ cΦ * (Λ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')) := mul_le_mul_of_nonneg_right hC this
      _ = _ := by ring
  refine ⟨hHb a₀ Ψ₀ hyp₀, hHb a₁ Ψ₁ hyp₁, ?_, ?_, hΦb Ψ₀ (Or.inl hyp₀), hΦb Ψ₁ (Or.inr hyp₁)⟩
  · intro a' ha' b' hb'
    have h1 := (hdifb a' b' Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ (c03m_aux_hyp_mono (by omega) hyp₀)
      (c03m_aux_hyp_mono (by omega) hyp₁) (fun x hx k hk => hdiff x hx k (by omega)) y hyI t ht
      z hz0).1
    have e : c03m_aux_M (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 -
        c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) a' b' y z =
        iteratedDeriv a' (fun y' => iteratedDeriv b' (fun z' =>
          c03_mult_bt Y a₁ Ψ₁ N r q y' t z' - c03_mult_bt Y a₀ Ψ₀ N r q y' t z') z) y := rfl
    rw [e]
    refine h1.trans ?_
    rw [hrp, Real.rpow_sub hz', Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
    have hc := hsum Cdif hCdif0 a' ha' b' hb'
    have : 0 ≤ δ * B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b') := by positivity
    calc Cdif a' b' * δ * B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')
        = Cdif a' b' * (δ * B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')) := by ring
      _ ≤ cD * (δ * B0 * Y⁻¹ ^ a' * (|z| ^ K₀ * |z|⁻¹ ^ b')) := mul_le_mul_of_nonneg_right hc this
      _ = _ := by ring
  · intro a' ha' b' hb'
    have h1 := (hdifb a' b' Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ (c03m_aux_hyp_mono (by omega) hyp₀)
      (c03m_aux_hyp_mono (by omega) hyp₁) (fun x hx k hk => hdiff x hx k (by omega)) y hyI t ht
      z hz0).2 hz
    rw [c03m_aux_M_ofReal (fun w : ℝ × ℝ => c03_mult_phit Ψ₁ w.1 t w.2 - c03_mult_phit Ψ₀ w.1 t w.2),
      Complex.norm_real, Real.norm_eq_abs]
    refine h1.trans ?_
    rw [show -(a' : ℝ) - 1 = -((a' + 1 : ℕ) : ℝ) by push_cast; ring, hrp,
      Real.rpow_sub hz', Real.rpow_one, Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
    have hc := hsum Cdif hCdif0 a' ha' b' hb'
    have : 0 ≤ δ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b') := by positivity
    calc Cdif a' b' * δ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')
        = Cdif a' b' * (δ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')) := by ring
      _ ≤ cD * (δ * Y⁻¹ ^ (a' + 1) * (|z| * |z|⁻¹ ^ b')) := mul_le_mul_of_nonneg_right hc this
      _ = _ := by ring


/-- Integrability and bounded support from the conclusions of `c03m_aux_core_dom`. -/
lemma c03m_aux_dom_int2 {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {Y t y : ℝ} (hY : 0 < Y) (ht : 0 < t)
    (hy : y ∈ Ioo (Y / 2) (3 * Y)) {T : Set ℝ} (hTU : T ⊆ Ioo (Y / 4) (4 * Y)) {f : ℝ → ℂ}
    {C0 Λ : ℝ} {K₀ j : ℕ} (hK₀ : 1 ≤ K₀) (hC0 : 0 ≤ C0) (hΛ : 0 ≤ Λ)
    (h1 : ∀ z, y + t * z ∈ Ioo (Y / 4) (4 * Y) → z ≠ 0 →
      ‖f z‖ ≤ C0 * ∑ l ∈ Finset.range (j + 1), |z| ^ K₀ * (Λ * |z|) ^ l)
    (h2 : ∀ z, y + t * z ∉ T → f z = 0) (h3 : Continuous f) :
    (∀ z, 4 * Y / t < |z| → f z = 0) ∧
    (∀ z, z ≠ 0 → |z| ≤ 4 * Y / t →
      ‖f z‖ ≤ C0 * ∑ l ∈ Finset.range (j + 1), |z| ^ K₀ * (Λ * |z|) ^ l) ∧
    ∀ η : ℝ, 0 ≤ η → Integrable (fun z : ℝ =>
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) * f z) := by
  have hout : ∀ z, 4 * Y / t < |z| → f z = 0 := by
    intro z hz
    refine h2 z fun hT => ?_
    have := c03m_aux_tz_le ht hy (hTU hT)
    rw [div_lt_iff₀ ht] at hz
    linarith
  have hb : ∀ z, z ≠ 0 → |z| ≤ 4 * Y / t →
      ‖f z‖ ≤ C0 * ∑ l ∈ Finset.range (j + 1), |z| ^ K₀ * (Λ * |z|) ^ l := by
    intro z hz0 _
    by_cases hz : y + t * z ∈ Ioo (Y / 4) (4 * Y)
    · exact h1 z hz hz0
    · rw [h2 z (fun h => hz (hTU h)), norm_zero]; positivity
  exact ⟨hout, hb, fun η hη => c03m_aux_dom_integrable hp hp1 h3 hK₀ (by positivity) hC0 hΛ
    hout hb η hη⟩

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c03_mult_difference_integral_bound.  For every `j` there is a finite `k₀` such
that, for two data with `δ`-close derivatives (`δ ≥ 0`),
`|∂_y^j(I_{1,η} - I_{0,η})| ≤ CδBY^{-j}Λ^{p-K} + CδBY^{-j-1}Λ^{p-K-1} ≤ 2CδAY^{-N-j}Λ^{p-N}`. -/
theorem c03_mult_difference_integral_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ)
    (hc₀ : 0 < c₀) (N : ℕ) (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a₀ Ψ₀ → c03_mult_hyp Y Λ A c₀ Ck k₀ a₁ Ψ₁ →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ k₀,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
      ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ η : ℝ, 0 ≤ η →
        ‖iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N r q η y' t -
            c03_mult_I p Y a₀ Ψ₀ N r q η y' t) y‖ ≤
          C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
            C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) ∧
        C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
            C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) ≤
          2 * C * δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
  intro j
  set K : ℕ := 2 * N - 1 + c03_mult_q1 q with hK
  have hK1 : 1 ≤ K := by omega
  obtain ⟨S₁, hS₁⟩ := c03m_aux_core_ibp p hp hp1 c₀ hc₀ K hK1 j
  obtain ⟨S₂, hS₂⟩ := c03m_aux_core_ibp p hp hp1 c₀ hc₀ (K + 1) (by omega) j
  set S : ℕ := S₁ + S₂ with hS
  refine ⟨2 * N + j + S + 4, fun Ck => ?_⟩
  obtain ⟨cH, cD, cΦ, hcH, hcD, hcΦ, hSB⟩ := c03m_aux_diff_SBs c₀ hc₀ N hN r q hrq j S Ck
  have hrec := fun s : ℕ => c03_mult_phase_symbol c₀ hc₀ 0 s Ck
  choose Crec hCrec0 hrecb using hrec
  set Cr : ℕ → ℝ := fun s => 4 ^ s * Crec s with hCr_def
  have hCr : ∀ s, 0 ≤ Cr s := fun s => by
    have := (hCrec0 s).le; simp only [hCr_def]; positivity
  obtain ⟨C₁, hC₁, hb₁⟩ := hS₁ cD (3 * cΦ) Cr hcD (by positivity) hCr
  obtain ⟨C₂, hC₂, hb₂⟩ := hS₂ (2 ^ (j + S) * cD * (3 * cH)) (3 * cΦ) Cr (by positivity)
    (by positivity) hCr
  obtain ⟨Ca00, -, hamp00⟩ := c03_mult_amplitude_symbol c₀ hc₀ N hN r q hrq 0 0 Ck
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ hyp₀ hyp₁ hdiff y hyI t ht η hη
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hy : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
  set B0 : ℝ := c03_mult_size N q Y Λ A t with hB0
  have hB00 : 0 ≤ B0 := c03m_aux_size_nonneg N q hY0 hΛ0.le hA.le ht0.le
  obtain ⟨ha₀, has₀, hΨ₀, hΨb₀⟩ := id hyp₀
  obtain ⟨ha₁, has₁, hΨ₁, hΨb₁⟩ := id hyp₁
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hVU : V ⊆ U := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set W : Set (ℝ × ℝ) := (V ×ˢ univ) ∩ (fun w : ℝ × ℝ => w.1 + t * w.2) ⁻¹' U with hW_def
  have hW : IsOpen W := (isOpen_Ioo.prod isOpen_univ).inter (isOpen_Ioo.preimage (by fun_prop))
  have hyzW : ∀ z, y + t * z ∈ U → (y, z) ∈ W := fun z hz => ⟨⟨hy, trivial⟩, hz⟩
  have hH₀V := (hamp00 Y Λ A a₀ Ψ₀ hY hΛ hA (c03m_aux_hyp_mono (by omega) hyp₀) t ht).1
  have hH₁V := (hamp00 Y Λ A a₁ Ψ₁ hY hΛ hA (c03m_aux_hyp_mono (by omega) hyp₁) t ht).1
  have hH₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) W :=
    hH₀V.mono inter_subset_left
  have hH₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2) W :=
    hH₁V.mono inter_subset_left
  have hφ₀ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_phit Ψ₀ w.1 t w.2) W :=
    c03m_aux_phit_smooth hΨ₀ t hVU
  have hφ₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_phit Ψ₁ w.1 t w.2) W :=
    c03m_aux_phit_smooth hΨ₁ t hVU
  have hφ₀c : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ)) W :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hφ₀
  have hφ₁c : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ)) W :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hφ₁
  have hΦσ : ∀ σ : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => (((1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 +
      σ * c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ)) W := fun σ =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_const.mul hφ₀).add
      (contDiffOn_const.mul hφ₁))
  have hHσ : ∀ σ : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((1 - σ : ℝ) : ℂ) *
      c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2 + (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2) W :=
    fun σ => (contDiffOn_const.mul hH₀).add (contDiffOn_const.mul hH₁)
  have hG1s : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 -
      c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2) W := hH₁.sub hH₀
  have hDs : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => ((c03_mult_phit Ψ₁ w.1 t w.2 -
      c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ)) W :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hφ₁.sub hφ₀)
  have hG2s : ∀ σ : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℝ × ℝ => Complex.I *
      ((c03_mult_phit Ψ₁ w.1 t w.2 - c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ) *
      (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2 +
        (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2)) W := fun σ =>
    (contDiffOn_const.mul hDs).mul (hHσ σ)
  -- supports
  set T : Set ℝ := tsupport (iteratedDeriv r a₀) ∪ tsupport (iteratedDeriv r a₁) with hT_def
  have hTc : IsCompact T :=
    ((c03m_aux_tsupport_compact has₀).of_isClosed_subset (isClosed_tsupport _)
      (c03m_aux_tsupport_iteratedDeriv a₀ r)).union
    ((c03m_aux_tsupport_compact has₁).of_isClosed_subset (isClosed_tsupport _)
      (c03m_aux_tsupport_iteratedDeriv a₁ r))
  have hTU : T ⊆ U := union_subset ((c03m_aux_tsupport_iteratedDeriv a₀ r).trans has₀)
    ((c03m_aux_tsupport_iteratedDeriv a₁ r).trans has₁)
  have hv : ∀ y' z', y' + t * z' ∉ T → c03_mult_bt Y a₀ Ψ₀ N r q y' t z' = 0 ∧
      c03_mult_bt Y a₁ Ψ₁ N r q y' t z' = 0 := fun y' z' h =>
    ⟨c03m_aux_bt_vanish a₀ hΨ₀ N r q (fun h' => h (Or.inl h')),
      c03m_aux_bt_vanish a₁ hΨ₁ N r q (fun h' => h (Or.inr h'))⟩
  -- symbol bounds
  have hSBz := fun z (hz : y + t * z ∈ U) (hz0 : z ≠ 0) =>
    hSB Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ hyp₀ hyp₁ hdiff y hyI t ht z hz hz0
  have hcoef : ∀ σ ∈ Icc (-1 : ℝ) 2, ‖((1 - σ : ℝ) : ℂ)‖ + ‖((σ : ℝ) : ℂ)‖ ≤ 3 := by
    intro σ hσ
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := hσ
    rcases abs_cases (1 - σ) with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rcases abs_cases σ with ⟨e2, -⟩ | ⟨e2, -⟩ <;>
      rw [e1, e2] <;> linarith
  have hSBHσ : ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ z, y + t * z ∈ U → z ≠ 0 →
      c03m_aux_SB (fun w : ℝ × ℝ => ((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2 +
        (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2) y z j S (3 * cH) (B0 * |z| ^ K)
        Y⁻¹ |z|⁻¹ := fun σ hσ z hz hz0 =>
    c03m_aux_SB_mono (c03m_aux_SB_lin hW hH₀ hH₁ (hyzW z hz) _ _ (hSBz z hz hz0).1
      (hSBz z hz hz0).2.1) (mul_le_mul_of_nonneg_right (hcoef σ hσ) hcH) (by positivity)
      (by positivity) (by positivity)
  have hSBΦσ : ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ z, y + t * z ∈ U → z ≠ 0 →
      c03m_aux_SB (c03m_aux_pd ((1 : ℝ), (0 : ℝ)) (fun w : ℝ × ℝ => (((1 - σ) *
        c03_mult_phit Ψ₀ w.1 t w.2 + σ * c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ)) 1) y z j S
        (3 * cΦ) (Λ * |z| * Y⁻¹) Y⁻¹ |z|⁻¹ := by
    intro σ hσ z hz hz0
    have e : (fun w : ℝ × ℝ => (((1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 +
        σ * c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ)) = fun w => ((1 - σ : ℝ) : ℂ) *
        ((c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ) + ((σ : ℝ) : ℂ) *
        ((c03_mult_phit Ψ₁ w.1 t w.2 : ℝ) : ℂ) := by
      funext w; push_cast; ring
    rw [e]
    exact c03m_aux_SB_mono (c03m_aux_SB_pd_lin hW hφ₀c hφ₁c (hyzW z hz) _ _
      (hSBz z hz hz0).2.2.2.2.1 (hSBz z hz hz0).2.2.2.2.2)
      (mul_le_mul_of_nonneg_right (hcoef σ hσ) hcΦ) (by positivity) (by positivity)
      (by positivity)
  have hSBG2 : ∀ σ ∈ Icc (-1 : ℝ) 2, ∀ z, y + t * z ∈ U → z ≠ 0 →
      c03m_aux_SB (fun w : ℝ × ℝ => Complex.I *
        ((c03_mult_phit Ψ₁ w.1 t w.2 - c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ) *
        (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2 +
          (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2)) y z j S
        (2 ^ (j + S) * cD * (3 * cH)) (δ * B0 * Y⁻¹ * |z| ^ (K + 1)) Y⁻¹ |z|⁻¹ := by
    intro σ hσ z hz hz0
    have h1 := c03m_aux_SB_const_mul Complex.I (by simp) (fun a _ b _ => by positivity)
      (hSBz z hz hz0).2.2.2.1
    have h2 := c03m_aux_SB_mul hW (contDiffOn_const.mul hDs) (hHσ σ) (hyzW z hz) hcD
      (by positivity : (0 : ℝ) ≤ 3 * cH) (by positivity) (by positivity) (by positivity)
      (by positivity) h1 (hSBHσ σ hσ z hz hz0)
    refine c03m_aux_SB_monoM h2 (le_of_eq ?_) (by positivity) (by positivity) (by positivity)
    ring
  -- phase bounds of the interpolated phases
  have hΨb₀' : ∀ s ≤ S, ∀ x ∈ U, c₀⁻¹ * Λ ≤ deriv Ψ₀ x ∧ deriv Ψ₀ x ≤ c₀ * Λ ∧
      ∀ k ≤ 0 + s + 2, |iteratedDeriv k (deriv Ψ₀) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ)) :=
    fun s hs x hx => ⟨(hΨb₀ x hx).1, (hΨb₀ x hx).2.1, fun k hk =>
      ((hΨb₀ x hx).2.2 k (by omega)).1⟩
  have hΨb₁' : ∀ s ≤ S, ∀ x ∈ U, c₀⁻¹ * Λ ≤ deriv Ψ₁ x ∧ deriv Ψ₁ x ≤ c₀ * Λ ∧
      ∀ k ≤ 0 + s + 2, |iteratedDeriv k (deriv Ψ₁) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ)) :=
    fun s hs x hx => ⟨(hΨb₁ x hx).1, (hΨb₁ x hx).2.1, fun k hk =>
      ((hΨb₁ x hx).2.2 k (by omega)).1⟩
  have hφd : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z, y + t * z ∈ U →
      c₀⁻¹ * Λ ≤ |deriv (fun z => (1 - σ) * c03_mult_phit Ψ₀ y t z +
        σ * c03_mult_phit Ψ₁ y t z) z| ∧
      |deriv (fun z => (1 - σ) * c03_mult_phit Ψ₀ y t z + σ * c03_mult_phit Ψ₁ y t z) z| ≤
        c₀ * Λ := by
    intro σ hσ z hz
    have h := hrecb 0 Y Λ Ψ₀ Ψ₁ hY hΛ hΨ₀ hΨ₁ (hΨb₀' 0 (Nat.zero_le _))
      (hΨb₁' 0 (Nat.zero_le _)) σ hσ y hy t ht z hz
    have hpos : 0 < c₀⁻¹ * Λ := by positivity
    rw [abs_of_pos (hpos.trans_le h.2.2.2.1)]
    exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩
  have hrecz : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z, y + t * z ∈ U → z ≠ 0 → ∀ s ≤ S,
      |iteratedDeriv s (fun z => 1 / deriv (fun z => (1 - σ) * c03_mult_phit Ψ₀ y t z +
        σ * c03_mult_phit Ψ₁ y t z) z) z| ≤ Cr s * Λ⁻¹ * |z| ^ (-(s : ℝ)) := by
    intro σ hσ z hz hz0 s hs
    have hz' : 0 < |z| := abs_pos.2 hz0
    have h1 := (hrecb s Y Λ Ψ₀ Ψ₁ hY hΛ hΨ₀ hΨ₁ (hΨb₀' s hs) (hΨb₁' s hs) σ hσ y hy t ht z
      hz).2.2.2.2.2.1
    simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h1
    refine h1.trans ?_
    have htz := c03m_aux_tz_le ht0 hy hz
    have htY : t / Y ≤ 4 * |z|⁻¹ := by
      rw [div_le_iff₀ hY0]
      calc t = t * |z| * |z|⁻¹ := by field_simp
        _ ≤ 4 * Y * |z|⁻¹ := by gcongr
        _ = _ := by ring
    have h4 : (t / Y) ^ s ≤ 4 ^ s * |z| ^ (-(s : ℝ)) := by
      rw [Real.rpow_neg hz'.le, Real.rpow_natCast, ← inv_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) htY s
    calc Crec s * Λ⁻¹ * (t / Y) ^ s ≤ Crec s * Λ⁻¹ * (4 ^ s * |z| ^ (-(s : ℝ))) := by
          have := (hCrec0 s).le; gcongr
      _ = _ := by simp only [hCr_def]; ring
  -- vanishing outside `T`
  have hHσT : ∀ σ : ℝ, ∀ y' z', y' + t * z' ∉ T → ((1 - σ : ℝ) : ℂ) *
      c03_mult_bt Y a₀ Ψ₀ N r q y' t z' + (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z' = 0 :=
    fun σ y' z' h => by rw [(hv y' z' h).1, (hv y' z' h).2]; ring
  have hG1T : ∀ y' z', y' + t * z' ∉ T → c03_mult_bt Y a₁ Ψ₁ N r q y' t z' -
      c03_mult_bt Y a₀ Ψ₀ N r q y' t z' = 0 :=
    fun y' z' h => by rw [(hv y' z' h).1, (hv y' z' h).2]; ring
  have hG2T : ∀ σ : ℝ, ∀ y' z', y' + t * z' ∉ T → Complex.I *
      ((c03_mult_phit Ψ₁ y' t z' - c03_mult_phit Ψ₀ y' t z' : ℝ) : ℂ) *
      (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z' +
        (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z') = 0 :=
    fun σ y' z' h => by rw [(hv y' z' h).1, (hv y' z' h).2]; ring
  -- pointwise domination
  have hdomF := fun σ (hσ : σ ∈ Icc (-1 : ℝ) 2) => c03m_aux_core_dom hY0 hy hTc hTU
    (Φr := fun w : ℝ × ℝ => (1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 + σ * c03_mult_phit Ψ₁ w.1 t w.2)
    (hΦσ σ) (hHσ σ) (hHσT σ) (j := j) (S := S) (K₀ := K) (by positivity : (0 : ℝ) ≤ 3 * cH)
    (by positivity : (0 : ℝ) ≤ 3 * cΦ) hB00 hΛ0.le (hSBHσ σ hσ) (hSBΦσ σ hσ)
  have hdom1 := fun σ (hσ : σ ∈ Icc (-1 : ℝ) 2) => c03m_aux_core_dom hY0 hy hTc hTU
    (Φr := fun w : ℝ × ℝ => (1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 + σ * c03_mult_phit Ψ₁ w.1 t w.2)
    (hΦσ σ) hG1s hG1T (j := j) (S := S) (K₀ := K) hcD
    (by positivity : (0 : ℝ) ≤ 3 * cΦ) (by positivity : (0 : ℝ) ≤ δ * B0) hΛ0.le
    (fun z hz hz0 => (hSBz z hz hz0).2.2.1) (hSBΦσ σ hσ)
  have hdom2 := fun σ (hσ : σ ∈ Icc (-1 : ℝ) 2) => c03m_aux_core_dom hY0 hy hTc hTU
    (Φr := fun w : ℝ × ℝ => (1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 + σ * c03_mult_phit Ψ₁ w.1 t w.2)
    (hΦσ σ) (hG2s σ) (hG2T σ) (j := j) (S := S) (K₀ := K + 1)
    (by positivity : (0 : ℝ) ≤ 2 ^ (j + S) * cD * (3 * cH))
    (by positivity : (0 : ℝ) ≤ 3 * cΦ) (by positivity : (0 : ℝ) ≤ δ * B0 * Y⁻¹) hΛ0.le
    (hSBG2 σ hσ) (hSBΦσ σ hσ)
  set R : ℝ := 4 * Y / t with hR_def
  have hR0 : 0 ≤ R := by positivity
  have hiF := fun σ (hσ : σ ∈ Icc (-1 : ℝ) 2) => c03m_aux_dom_int2 hp hp1 hY0 ht0 hy hTU hK1
    (by positivity) hΛ0.le (hdomF σ hσ).1 (hdomF σ hσ).2.1 (hdomF σ hσ).2.2
  have hi1 := fun σ (hσ : σ ∈ Icc (-1 : ℝ) 2) => c03m_aux_dom_int2 hp hp1 hY0 ht0 hy hTU hK1
    (by positivity) hΛ0.le (hdom1 σ hσ).1 (hdom1 σ hσ).2.1 (hdom1 σ hσ).2.2
  have hi2 := fun σ (hσ : σ ∈ Icc (-1 : ℝ) 2) => c03m_aux_dom_int2 hp hp1 hY0 ht0 hy hTU
    (by omega : 1 ≤ K + 1) (by positivity) hΛ0.le (hdom2 σ hσ).1 (hdom2 σ hσ).2.1 (hdom2 σ hσ).2.2
  -- names for the integrands
  obtain ⟨wz, hwz⟩ : ∃ wz : ℝ → ℂ, ∀ z, wz z =
      Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ Gf : ℝ → ℝ → ℂ, ∀ σ z, Gf σ z = iteratedDeriv j (fun y' =>
      Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y' t z +
        σ * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
        (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
          (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z)) y := ⟨_, fun _ _ => rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ → ℝ → ℂ, ∀ σ z, G1 σ z = iteratedDeriv j (fun y' =>
      Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y' t z +
        σ * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
        (c03_mult_bt Y a₁ Ψ₁ N r q y' t z - c03_mult_bt Y a₀ Ψ₀ N r q y' t z)) y :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2 : ℝ → ℝ → ℂ, ∀ σ z, G2 σ z = iteratedDeriv j (fun y' =>
      Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y' t z +
        σ * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
        (Complex.I * ((c03_mult_phit Ψ₁ y' t z - c03_mult_phit Ψ₀ y' t z : ℝ) : ℂ) *
          (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
            (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z))) y := ⟨_, fun _ _ => rfl⟩
  have hFi : ∀ σ ∈ Icc (-1 : ℝ) 2, Integrable (fun z => wz z * Gf σ z) := fun σ hσ => by
    simp only [hwz, hGf]; exact (hiF σ hσ).2.2 η hη
  have hF1i : ∀ σ ∈ Icc (-1 : ℝ) 2, Integrable (fun z => wz z * G1 σ z) := fun σ hσ => by
    simp only [hwz, hG1]; exact (hi1 σ hσ).2.2 η hη
  have hF2i : ∀ σ ∈ Icc (-1 : ℝ) 2, Integrable (fun z => wz z * G2 σ z) := fun σ hσ => by
    simp only [hwz, hG2]; exact (hi2 σ hσ).2.2 η hη
  have hwz0 : wz 0 = 0 := by rw [hwz]; simp [Real.zero_rpow (by linarith : (1 + p) ≠ 0)]
  have hwzn : ∀ z, ‖wz z‖ ≤ ‖((z : ℂ) ^ 0) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ := by
    intro z
    rw [hwz, norm_div, norm_div, pow_zero, norm_one]
    gcongr
    exact c03m_aux_gauss_le η z hη
  -- differentiation in `σ`
  set C1d : ℝ := (1 + 2 ^ (j + S) * (3 * cΦ)) ^ j * cD * (δ * B0 * Y⁻¹ ^ j) with hC1d
  set C2d : ℝ := (1 + 2 ^ (j + S) * (3 * cΦ)) ^ j * (2 ^ (j + S) * cD * (3 * cH)) *
    (δ * B0 * Y⁻¹ * Y⁻¹ ^ j) with hC2d
  set Mb : ℝ := C1d * ∑ l ∈ Finset.range (j + 1), R ^ (K - 1) * (Λ * R) ^ l +
    C2d * ∑ l ∈ Finset.range (j + 1), R ^ (K + 1 - 1) * (Λ * R) ^ l with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have hderiv : ∀ σ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun σ' => ∫ z, wz z * Gf σ' z)
      (∫ z, wz z * (G1 σ z + G2 σ z)) σ := by
    intro σ hσ
    have hs : Ioo (σ - 1) (σ + 1) ∈ 𝓝 σ := Ioo_mem_nhds (by linarith) (by linarith)
    have hsI : ∀ σ' ∈ Ioo (σ - 1) (σ + 1), σ' ∈ Icc (-1 : ℝ) 2 := fun σ' h =>
      ⟨by linarith [h.1, hσ.1], by linarith [h.2, hσ.2]⟩
    have hσI : σ ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun σ' z => wz z * Gf σ' z) (F' := fun σ' z => wz z * (G1 σ' z + G2 σ' z))
      (bound := (Icc (-R) R).indicator fun z => Mb * ‖((z : ℂ) ^ 1) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖)
      hs ?_ (hFi σ hσI) ?_ ?_ ?_ ?_).2
    · filter_upwards [hs] with σ' hσ'
      exact (hFi σ' (hsI σ' hσ')).aestronglyMeasurable
    · exact (((hF1i σ hσI).add (hF2i σ hσI)).congr (Eventually.of_forall fun z => by
        simp only [Pi.add_apply]; ring)).aestronglyMeasurable
    · refine Eventually.of_forall fun z σ' hσ' => ?_
      have hσ'I := hsI σ' hσ'
      by_cases hzR : z ∈ Icc (-R) R
      · rw [indicator_of_mem hzR]
        rcases eq_or_ne z 0 with rfl | hz0
        · simp [hwz0]
        have hzR' : |z| ≤ R := abs_le.2 hzR
        have e1 : ‖G1 σ' z‖ ≤ C1d * ∑ l ∈ Finset.range (j + 1), |z| ^ K * (Λ * |z|) ^ l := by
          rw [hG1]; exact (hi1 σ' hσ'I).2.1 z hz0 hzR'
        have e2 : ‖G2 σ' z‖ ≤ C2d * ∑ l ∈ Finset.range (j + 1), |z| ^ (K + 1) * (Λ * |z|) ^ l := by
          rw [hG2]; exact (hi2 σ' hσ'I).2.1 z hz0 hzR'
        have p1 := c03m_aux_poly_lin (j := j) hK1 hΛ0.le hzR'
        have p2 := c03m_aux_poly_lin (j := j) (by omega : 1 ≤ K + 1) hΛ0.le hzR'
        have hG : ‖G1 σ' z + G2 σ' z‖ ≤ Mb * |z| := by
          refine (norm_add_le _ _).trans ?_
          have hC1 : 0 ≤ C1d := by positivity
          have hC2 : 0 ≤ C2d := by positivity
          calc ‖G1 σ' z‖ + ‖G2 σ' z‖ ≤
              C1d * ((∑ l ∈ Finset.range (j + 1), R ^ (K - 1) * (Λ * R) ^ l) * |z|) +
              C2d * ((∑ l ∈ Finset.range (j + 1), R ^ (K + 1 - 1) * (Λ * R) ^ l) * |z|) :=
                add_le_add (e1.trans (mul_le_mul_of_nonneg_left p1 hC1))
                  (e2.trans (mul_le_mul_of_nonneg_left p2 hC2))
            _ = Mb * |z| := by rw [hMb]; ring
        rw [norm_mul]
        calc ‖wz z‖ * ‖G1 σ' z + G2 σ' z‖ ≤ ‖((z : ℂ) ^ 0) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ *
            (Mb * |z|) := mul_le_mul (hwzn z) hG (norm_nonneg _) (norm_nonneg _)
          _ = Mb * ‖((z : ℂ) ^ 1) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ := by
            simp only [norm_div, pow_zero, pow_one, norm_one, Complex.norm_real, Real.norm_eq_abs]; ring
      · rw [indicator_of_notMem hzR]
        have hzR' : R < |z| := by
          by_contra h; exact hzR (abs_le.1 (not_lt.1 h))
        have e1 : G1 σ' z = 0 := by rw [hG1]; exact (hi1 σ' hσ'I).1 z hzR'
        have e2 : G2 σ' z = 0 := by rw [hG2]; exact (hi2 σ' hσ'I).1 z hzR'
        simp [e1, e2]
    · have hI : IntegrableOn (fun z : ℝ => Mb * ‖((z : ℂ) ^ 1) / ((|z| ^ (1 + p) : ℝ) : ℂ)‖)
          (Icc (-R) R) := ((c03m_aux_weight_integrableOn hp hp1 1 le_rfl R).norm.const_mul Mb :)
      exact hI.integrable_indicator measurableSet_Icc
    · refine Eventually.of_forall fun z σ' _ => ?_
      have h := (c03m_aux_diff_sigma hY0 hy has₀ has₁ hΨ₀ hΨ₁ N r q hH₀V hH₁V j σ' (z := z)).const_mul
        (wz z)
      have e : (fun σ'' => Gf σ'' z) = fun σ'' => iteratedDeriv j (fun y' =>
          Complex.exp (Complex.I * (((1 - σ'') * c03_mult_phit Ψ₀ y' t z +
            σ'' * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
            (((1 - σ'' : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
              (σ'' : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z)) y := funext fun σ'' => hGf σ'' z
      show HasDerivAt (fun σ'' => wz z * Gf σ'' z) (wz z * (G1 σ' z + G2 σ' z)) σ'
      simp only [hGf, hG1, hG2]
      exact h
  -- the uniform bound on the `σ`-derivative
  have hbound : ∀ σ ∈ Icc (0 : ℝ) 1, ‖∫ z, wz z * (G1 σ z + G2 σ z)‖ ≤
      C₁ * (δ * B0) * Y⁻¹ ^ j * Λ ^ (p - (K : ℝ)) +
        C₂ * (δ * B0 * Y⁻¹) * Y⁻¹ ^ j * Λ ^ (p - ((K + 1 : ℕ) : ℝ)) := by
    intro σ hσ
    have hσI : σ ∈ Icc (-1 : ℝ) 2 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have e : (fun z => wz z * (G1 σ z + G2 σ z)) =
        fun z => wz z * G1 σ z + wz z * G2 σ z := funext fun z => by ring
    rw [e, integral_add (hF1i σ hσI) (hF2i σ hσI)]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have h := hb₁ Y Λ (δ * B0) t η y T
        (fun w : ℝ × ℝ => (1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 + σ * c03_mult_phit Ψ₁ w.1 t w.2)
        (fun w : ℝ × ℝ => c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2 - c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2)
        hY0 hΛ0 (by positivity) ht0 hη hy hTc hTU (hΦσ σ) hG1s hG1T (hφd σ hσ)
        (fun z hz hz0 s hs => hrecz σ hσ z hz hz0 s (by omega))
        (fun z hz hz0 => c03m_aux_SB_monoS (hSBz z hz hz0).2.2.1 (by omega))
        (fun z hz hz0 => c03m_aux_SB_monoS (hSBΦσ σ hσI z hz hz0) (by omega))
      simp only [hwz, hG1]
      exact h
    · have h := hb₂ Y Λ (δ * B0 * Y⁻¹) t η y T
        (fun w : ℝ × ℝ => (1 - σ) * c03_mult_phit Ψ₀ w.1 t w.2 + σ * c03_mult_phit Ψ₁ w.1 t w.2)
        (fun w : ℝ × ℝ => Complex.I *
          ((c03_mult_phit Ψ₁ w.1 t w.2 - c03_mult_phit Ψ₀ w.1 t w.2 : ℝ) : ℂ) *
          (((1 - σ : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q w.1 t w.2 +
            (σ : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q w.1 t w.2))
        hY0 hΛ0 (by positivity) ht0 hη hy hTc hTU (hΦσ σ) (hG2s σ) (hG2T σ) (hφd σ hσ)
        (fun z hz hz0 s hs => hrecz σ hσ z hz hz0 s (by omega))
        (fun z hz hz0 => c03m_aux_SB_monoS (hSBG2 σ hσI z hz hz0) (by omega))
        (fun z hz hz0 => c03m_aux_SB_monoS (hSBΦσ σ hσI z hz hz0) (by omega))
      simp only [hwz, hG2]
      exact h
  -- endpoints: the two summand integrals
  obtain ⟨hs₀, hf₀⟩ := c03m_aux_I_smooth_formula p hp hp1 c₀ hc₀ N hN r q hrq Y hY0 a₀ Ψ₀ ha₀ has₀
    hΨ₀ t ht η
  obtain ⟨hs₁, hf₁⟩ := c03m_aux_I_smooth_formula p hp hp1 c₀ hc₀ N hN r q hrq Y hY0 a₁ Ψ₁ ha₁ has₁
    hΨ₁ t ht η
  have hA0 : ∀ z, iteratedDeriv j (fun y' =>
      Complex.exp (Complex.I * (c03_mult_phit Ψ₀ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a₀ Ψ₀ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y = wz z * Gf 0 z := by
    intro z
    have e : (fun y' => Complex.exp (Complex.I * (c03_mult_phit Ψ₀ y' t z : ℂ) -
        ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
        fun y' => wz z * (Complex.exp (Complex.I * (((1 - 0) * c03_mult_phit Ψ₀ y' t z +
          0 * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
          (((1 - 0 : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
            ((0 : ℝ) : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z)) := by
      funext y'
      rw [hwz]
      simp only [sub_zero, one_mul, zero_mul, add_zero, Complex.ofReal_zero, Complex.ofReal_one]
      rw [sub_eq_add_neg, Complex.exp_add]; ring
    rw [e, iteratedDeriv_const_mul_field, hGf]
  have hA1 : ∀ z, iteratedDeriv j (fun y' =>
      Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y' t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a₁ Ψ₁ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) y = wz z * Gf 1 z := by
    intro z
    have e : (fun y' => Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y' t z : ℂ) -
        ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
        fun y' => wz z * (Complex.exp (Complex.I * (((1 - 1) * c03_mult_phit Ψ₀ y' t z +
          1 * c03_mult_phit Ψ₁ y' t z : ℝ) : ℂ)) *
          (((1 - 1 : ℝ) : ℂ) * c03_mult_bt Y a₀ Ψ₀ N r q y' t z +
            ((1 : ℝ) : ℂ) * c03_mult_bt Y a₁ Ψ₁ N r q y' t z)) := by
      funext y'
      rw [hwz]
      simp only [sub_self, one_mul, zero_mul, zero_add, Complex.ofReal_zero, Complex.ofReal_one]
      rw [sub_eq_add_neg, Complex.exp_add]; ring
    rw [e, iteratedDeriv_const_mul_field, hGf]
  have hc₀' : ContDiffAt ℝ j (fun y' => c03_mult_I p Y a₀ Ψ₀ N r q η y' t) y :=
    (hs₀.contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (by exact_mod_cast le_top)
  have hc₁' : ContDiffAt ℝ j (fun y' => c03_mult_I p Y a₁ Ψ₁ N r q η y' t) y :=
    (hs₁.contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (by exact_mod_cast le_top)
  have hid : iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N r q η y' t -
      c03_mult_I p Y a₀ Ψ₀ N r q η y' t) y =
      (∫ z, wz z * Gf 1 z) - ∫ z, wz z * Gf 0 z := by
    rw [iteratedDeriv_fun_sub hc₁' hc₀', (hf₁ j y hy).2, (hf₀ j y hy).2]
    simp only [hA0, hA1]
  -- mean value inequality in `σ`
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun σ => ∫ z, wz z * Gf σ z) (f' := fun σ => ∫ z, wz z * (G1 σ z + G2 σ z))
    (C := C₁ * (δ * B0) * Y⁻¹ ^ j * Λ ^ (p - (K : ℝ)) +
        C₂ * (δ * B0 * Y⁻¹) * Y⁻¹ ^ j * Λ ^ (p - ((K + 1 : ℕ) : ℝ))) (a := 0) (b := 1)
    (fun x hx => (hderiv x hx).hasDerivWithinAt) (fun x hx => hbound x (Ico_subset_Icc_self hx))
    1 ⟨zero_le_one, le_rfl⟩
  simp only [sub_zero, mul_one] at hmvt
  have hrp : ∀ k : ℕ, Y ^ (-(k : ℝ)) = Y⁻¹ ^ k := fun k => by
    rw [Real.rpow_neg hY0.le, Real.rpow_natCast, inv_pow]
  have hY1 : Y ^ (-(j : ℝ) - 1) = Y⁻¹ * Y⁻¹ ^ j := by
    rw [Real.rpow_sub hY0, hrp, Real.rpow_one, div_eq_mul_inv]; ring
  have hL1 : Λ ^ (p - ((K + 1 : ℕ) : ℝ)) = Λ ^ (p - (K : ℝ) - 1) := by
    congr 1; push_cast; ring
  set X : ℝ := max C₁ C₂ with hX
  have hX1 : C₁ ≤ X := le_max_left _ _
  have hX2 : C₂ ≤ X := le_max_right _ _
  have hP1 : 0 ≤ δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ)) := by positivity
  have hP2 : 0 ≤ δ * B0 * Y ^ (-(j : ℝ) - 1) * Λ ^ (p - (K : ℝ) - 1) := by positivity
  refine ⟨?_, ?_⟩
  · rw [hid]
    refine hmvt.trans ?_
    rw [hL1]
    calc C₁ * (δ * B0) * Y⁻¹ ^ j * Λ ^ (p - (K : ℝ)) +
          C₂ * (δ * B0 * Y⁻¹) * Y⁻¹ ^ j * Λ ^ (p - (K : ℝ) - 1)
        = C₁ * (δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ))) +
          C₂ * (δ * B0 * Y ^ (-(j : ℝ) - 1) * Λ ^ (p - (K : ℝ) - 1)) := by
          rw [hrp, hY1]; ring
      _ ≤ X * (δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ))) +
          X * (δ * B0 * Y ^ (-(j : ℝ) - 1) * Λ ^ (p - (K : ℝ) - 1)) :=
          add_le_add (mul_le_mul_of_nonneg_right hX1 hP1) (mul_le_mul_of_nonneg_right hX2 hP2)
      _ = _ := by ring
  · have hsz := c03m_aux_size_bound N r hN q hrq (p := p) (Λ := Λ) (A := A) (t := t) (j : ℝ) hY hΛ
      hA.le ht0.le ht1
    have hYle : Y ^ (-(j : ℝ) - 1) ≤ Y ^ (-(j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hY (by linarith)
    have hLle : Λ ^ (p - (K : ℝ) - 1) ≤ Λ ^ (p - (K : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
    have hX0 : 0 ≤ X := hC₁.le.trans hX1
    have h2 : δ * B0 * Y ^ (-(j : ℝ) - 1) * Λ ^ (p - (K : ℝ) - 1) ≤
        δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ)) := by
      have : 0 ≤ δ * B0 := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hYle this) hLle (by positivity) (by positivity)
    have h3 : δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ)) ≤
        δ * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by
      have := mul_le_mul_of_nonneg_left hsz hδ
      calc δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ)) =
          δ * (B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ))) := by ring
        _ ≤ _ := this
    calc X * δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ)) +
          X * δ * B0 * Y ^ (-(j : ℝ) - 1) * Λ ^ (p - (K : ℝ) - 1)
        = X * (δ * B0 * Y ^ (-(j : ℝ)) * Λ ^ (p - (K : ℝ))) +
          X * (δ * B0 * Y ^ (-(j : ℝ) - 1) * Λ ^ (p - (K : ℝ) - 1)) := by ring
      _ ≤ X * (δ * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N))) +
          X * (δ * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N))) :=
          add_le_add (mul_le_mul_of_nonneg_left h3 hX0)
            (mul_le_mul_of_nonneg_left (h2.trans h3) hX0)
      _ = _ := by ring

/-! ### The `t`-parameter integral -/

/-- The localized `t`-independent profile `h(x) = [y+x ∈ U] a^{(r)}(y+x) e^{iΘ_y(x)} ∏ Θ_y^{(i+1)}(x)^{q_i}`
is continuous. -/
lemma c03m_aux_h_cont {Y : ℝ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (y : ℝ) (r : ℕ) {n : ℕ} (q : Fin n → ℕ) :
    Continuous (fun x => if y + x ∈ Ioo (Y / 4) (4 * Y) then
      iteratedDeriv r a (y + x) * Complex.exp (Complex.I * (c03_mult_Theta Ψ y x : ℂ)) *
        ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) x : ℝ) : ℂ) ^ q i else 0) := by
  set U := Ioo (Y / 4) (4 * Y) with hU_def
  set Uy : Set ℝ := {w | y + w ∈ U} with hUy
  have hUyo : IsOpen Uy := isOpen_Ioo.preimage (by fun_prop)
  set Θ := c03_mult_Theta Ψ y with hΘ_def
  have hΘs : ContDiffOn ℝ (⊤ : ℕ∞) Θ Uy := by
    have e : Θ = fun w => Ψ (y + w) - Ψ y - deriv Ψ y * w := by
      funext w; simp [hΘ_def, c03_mult_Theta]
    rw [e]
    exact ((hΨ.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ => y + w).contDiffOn
      (fun w hw => hw)).sub contDiffOn_const).sub (contDiffOn_const.mul contDiffOn_id)
  have hA : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv r a) := by
    rw [iteratedDeriv_eq_iterate]; exact ha.iterate_deriv _
  have hAs : tsupport (iteratedDeriv r a) ⊆ U := (c03m_aux_tsupport_iteratedDeriv a r).trans has
  refine (c03m_aux_smooth_of_local hUyo ?_ ?_).continuous
  · have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iteratedDeriv r a (y + x) *
        Complex.exp (Complex.I * (Θ x : ℂ)) *
          ∏ i, ((iteratedDeriv (i.val + 1) Θ x : ℝ) : ℂ) ^ q i) Uy := by
      refine ((hA.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun w : ℝ => y + w)).contDiffOn.mul
        (Complex.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul
          (Complex.ofRealCLM.contDiff.comp_contDiffOn hΘs)))).mul ?_
      exact contDiffOn_prod fun i _ => (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (c03m_aux_iteratedDeriv_contDiffOn hUyo hΘs (i.val + 1))).pow _
    exact h1.congr fun x hx => if_pos hx
  · intro x hx
    have h0 : iteratedDeriv r a =ᶠ[𝓝 (y + x)] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hAs h))
    have h0' : ∀ᶠ x' in 𝓝 x, iteratedDeriv r a (y + x') = 0 :=
      ((continuous_const.add continuous_id).tendsto x).eventually h0
    filter_upwards [h0'] with x' hx'
    split_ifs
    · rw [hx']; simp
    · rfl

/-- Measurability in `t` of `∂_y^i I_η(y,t)`. -/
lemma c03m_aux_I_meas (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (N : ℕ) (hN : 1 ≤ N) (r : ℕ)
    (q : Fin (2 * N - 1) → ℕ) (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) {Y : ℝ}
    (hY : 0 < Y) {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (η : ℝ) : ∀ i, ∀ y ∈ Ioo (Y / 2) (3 * Y), AEStronglyMeasurable
      (fun t => iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  intro i
  induction i with
  | zero =>
    intro y _
    simp only [iteratedDeriv_zero]
    refine StronglyMeasurable.aestronglyMeasurable ?_
    unfold c03_mult_I
    refine StronglyMeasurable.integral_prod_right (f := fun t z =>
      Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) ?_
    have hh := c03m_aux_h_cont ha has hΨ y r q
    set h := fun x => if y + x ∈ Ioo (Y / 4) (4 * Y) then
      iteratedDeriv r a (y + x) * Complex.exp (Complex.I * (c03_mult_Theta Ψ y x : ℂ)) *
        ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) x : ℝ) : ℂ) ^ q i else 0 with hh_def
    have hfun : Function.uncurry (fun t z =>
        Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
          c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) =
        fun w : ℝ × ℝ => (Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * w.2 -
          ((η * w.2 ^ 2 : ℝ) : ℂ)) * ((w.2 : ℂ) ^ (2 * N - 1) * h (w.1 * w.2))) /
            ((|w.2| ^ (1 + p) : ℝ) : ℂ) := by
      funext w
      simp only [Function.uncurry, c03_mult_bt, c03_mult_phit, hh_def]
      split_ifs with h1
      · push_cast
        simp only [mul_add, sub_eq_add_neg, Complex.exp_add]
        ring
      · simp
    rw [hfun]
    refine (Continuous.stronglyMeasurable ?_).div ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).mul
        ((by fun_prop : Continuous fun w : ℝ × ℝ => (w.2 : ℂ) ^ (2 * N - 1)).mul
          (hh.comp (by fun_prop)))
    · exact (Complex.continuous_ofReal.comp ((continuous_abs.comp continuous_snd).rpow_const
        (fun _ => Or.inr (by linarith)))).stronglyMeasurable
  | succ i ih =>
    intro y hy
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) δ, y + s ∈ Ioo (Y / 2) (3 * Y) := by
      refine ⟨(3 * Y - y) / 2, by linarith [hy.2], fun s hs => ⟨by linarith [hy.1, hs.1],
        by linarith [hs.2, hy.2]⟩⟩
    set u : ℕ → ℝ := fun k => δ / (k + 1) with hu
    have hu0 : ∀ k, 0 < u k := fun k => by positivity
    have huδ : ∀ k, u k ≤ δ := fun k => by
      rw [hu]; exact div_le_self hδ0.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hut : Tendsto u atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
      simpa [hu, div_eq_mul_inv] using this
    have hlim : ∀ t ∈ Ioc (0 : ℝ) 1, Tendsto (fun k => (u k)⁻¹ •
        (iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N r q η y'' t) (y + u k) -
          iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N r q η y'' t) y)) atTop
        (𝓝 (iteratedDeriv (i + 1) (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y)) := by
      intro t ht
      have hsm := (c03m_aux_I_smooth_formula p hp hp1 1 one_pos N hN r q hrq Y hY a Ψ ha has hΨ t
        ht η).1
      have hdiff : DifferentiableAt ℝ
          (iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N r q η y'' t)) y :=
        ((c03m_aux_iteratedDeriv_contDiffOnC isOpen_Ioo hsm i).differentiableOn
          (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hy)
      have hd := hdiff.hasDerivAt
      have e : deriv (iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N r q η y'' t)) y =
          iteratedDeriv (i + 1) (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y := by
        rw [iteratedDeriv_succ]
      rw [e] at hd
      have hu' : Tendsto u atTop (𝓝[≠] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨hut, Eventually.of_forall fun k => (hu0 k).ne'⟩
      exact hd.tendsto_slope_zero.comp hu'
    have hmeas : ∀ k, AEStronglyMeasurable ((u k)⁻¹ •
        ((fun t => iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N r q η y'' t) (y + u k)) -
          fun t => iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N r q η y'' t) y))
        (volume.restrict (Ioc (0 : ℝ) 1)) := fun k =>
      ((ih _ (hδ _ ⟨(hu0 k).le, huδ k⟩)).sub (ih y hy)).const_smul _
    refine aestronglyMeasurable_of_tendsto_ae atTop hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall hlim

/-- The summand integrand in the factorized form `e^{iλz-ηz²} z^n h(tz) / |z|^{1+p}`. -/
lemma c03m_aux_I_integrand_eq {Y : ℝ} (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (p : ℝ) (N r : ℕ)
    (q : Fin (2 * N - 1) → ℕ) (η y t z : ℝ) :
    Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ) =
      Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z - ((η * z ^ 2 : ℝ) : ℂ)) *
        ((z : ℂ) ^ (2 * N - 1) * (if y + t * z ∈ Ioo (Y / 4) (4 * Y) then
          iteratedDeriv r a (y + t * z) * Complex.exp (Complex.I * (c03_mult_Theta Ψ y (t * z) : ℂ)) *
            ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) (t * z) : ℝ) : ℂ) ^ q i
          else 0)) / ((|z| ^ (1 + p) : ℝ) : ℂ) := by
  simp only [c03_mult_bt, c03_mult_phit]
  split_ifs with h1
  · push_cast
    simp only [mul_add, sub_eq_add_neg, Complex.exp_add]
    ring
  · simp

/-- Uniform boundedness of the localized profile. -/
lemma c03m_aux_h_bdd {Y : ℝ} {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (y : ℝ) (r : ℕ) {n : ℕ} (q : Fin n → ℕ) : ∃ C, ∀ x, ‖(if y + x ∈ Ioo (Y / 4) (4 * Y) then
      iteratedDeriv r a (y + x) * Complex.exp (Complex.I * (c03_mult_Theta Ψ y x : ℂ)) *
        ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) x : ℝ) : ℂ) ^ q i else 0)‖ ≤ C := by
  have hc := c03m_aux_h_cont ha has hΨ y r q
  refine hc.bounded_above_of_compact_support ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := Y / 4 - y) (b := 4 * Y - y)) fun x hx => ?_
  have : y + x ∉ Ioo (Y / 4) (4 * Y) := fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩
  simp only [this, ↓reduceIte]

set_option maxHeartbeats 800000 in
/-- Fubini for the regularized remainder: for `η > 0`,
`∫ e^{iλz} R_n(z) e^{-ηz²}|z|^{-1-p} = n ∑ d_{r,q} ∫₀¹ (1-t)^{n-1} I_η(y,t) dt`. -/
lemma c03m_aux_R_fubini (p : ℝ) (hp : 0 < p) (hp1 : p < 1) {Y : ℝ} (hY : 1 ≤ Y) {a : ℝ → ℂ}
    {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y))
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (hlam : ∀ y ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ y) (N : ℕ) (hN : 1 ≤ N) (y : ℝ)
    (hy : y ∈ Ioo (Y / 2) (3 * Y)) (η : ℝ) (hη : 0 < η) :
    ∫ z : ℝ, Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) * c03_mult_taylorR Y a Ψ N y z *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ) =
      ((2 * N - 1 : ℕ) : ℂ) * ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
        ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          c03_mult_I p Y a Ψ N rq.1 rq.2 η y t := by
  set G : ℕ × (Fin (2 * N - 1) → ℕ) → ℝ → ℝ → ℂ := fun rq t z =>
    (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N rq.1 rq.2 y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) with hG
  -- product integrability
  have hGint : ∀ rq : ℕ × (Fin (2 * N - 1) → ℕ), Integrable (Function.uncurry (G rq))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
    intro rq
    obtain ⟨Mh, hMh⟩ := c03m_aux_h_bdd ha has hΨ y rq.1 rq.2
    have hmom := c03m_aux_moment_integrable hp hp1 0 η hη (2 * N - 1) (by omega)
    have hb : Integrable (fun w : ℝ × ℝ => (1 : ℝ) * (Mh * ‖Complex.exp (Complex.I * ((0 : ℝ) : ℂ) *
        w.2) * (w.2 : ℂ) ^ (2 * N - 1) * Complex.exp (-((η * w.2 ^ 2 : ℝ) : ℂ)) /
          ((|w.2| ^ (1 + p) : ℝ) : ℂ)‖)) ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) (hmom.norm.const_mul Mh)
    refine hb.mono' ?_ ?_
    · have hfun : Function.uncurry (G rq) = fun w : ℝ × ℝ =>
          (((1 - w.1) ^ (2 * N - 2) : ℝ) : ℂ) *
            (Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * w.2 - ((η * w.2 ^ 2 : ℝ) : ℂ)) *
              ((w.2 : ℂ) ^ (2 * N - 1) * (if y + w.1 * w.2 ∈ Ioo (Y / 4) (4 * Y) then
                iteratedDeriv rq.1 a (y + w.1 * w.2) *
                  Complex.exp (Complex.I * (c03_mult_Theta Ψ y (w.1 * w.2) : ℂ)) *
                  ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) (w.1 * w.2) : ℝ) : ℂ) ^
                    rq.2 i else 0)) / ((|w.2| ^ (1 + p) : ℝ) : ℂ)) := by
        funext w
        simp only [Function.uncurry, hG]
        rw [c03m_aux_I_integrand_eq]
      rw [hfun]
      have hh := c03m_aux_h_cont ha has hΨ y rq.1 rq.2
      refine StronglyMeasurable.aestronglyMeasurable ?_
      refine (Continuous.stronglyMeasurable ?_).mul ((Continuous.stronglyMeasurable ?_).div ?_)
      · fun_prop
      · exact (Complex.continuous_exp.comp (by fun_prop)).mul
          ((by fun_prop : Continuous fun w : ℝ × ℝ => (w.2 : ℂ) ^ (2 * N - 1)).mul
            (hh.comp (by fun_prop)))
      · exact (Complex.continuous_ofReal.comp ((continuous_abs.comp continuous_snd).rpow_const
          (fun _ => Or.inr (by linarith)))).stronglyMeasurable
    · have hmem : ∀ᵐ w : ℝ × ℝ ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure ℝ)),
          w.1 ∈ Ioc (0 : ℝ) 1 :=
        (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc (0 : ℝ) 1))
          (ν := (volume : Measure ℝ))).ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hmem] with w hw
      simp only [Function.uncurry, hG]
      rw [c03m_aux_I_integrand_eq, one_mul]
      have h1t : ‖(((1 - w.1) ^ (2 * N - 2) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [hw.2])]
        exact pow_le_one₀ (by linarith [hw.2]) (by linarith [hw.1])
      have hE1 : ‖Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * w.2 - ((η * w.2 ^ 2 : ℝ) : ℂ))‖ =
          ‖Complex.exp (-((η * w.2 ^ 2 : ℝ) : ℂ))‖ := by
        rw [Complex.norm_exp, Complex.norm_exp]; congr 1; simp
      have hE0 : ‖Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * w.2)‖ = 1 := by simp
      rw [norm_mul, norm_div, norm_mul, norm_mul, hE1, norm_div, norm_mul, norm_mul, hE0]
      have hH := hMh (w.1 * w.2)
      have hT0 : 0 ≤ ‖(((1 - w.1) ^ (2 * N - 2) : ℝ) : ℂ)‖ := norm_nonneg _
      calc ‖(((1 - w.1) ^ (2 * N - 2) : ℝ) : ℂ)‖ * (‖Complex.exp (-((η * w.2 ^ 2 : ℝ) : ℂ))‖ *
            (‖(w.2 : ℂ) ^ (2 * N - 1)‖ * ‖(if y + w.1 * w.2 ∈ Ioo (Y / 4) (4 * Y) then
              iteratedDeriv rq.1 a (y + w.1 * w.2) *
                Complex.exp (Complex.I * (c03_mult_Theta Ψ y (w.1 * w.2) : ℂ)) *
                ∏ i, ((iteratedDeriv (i.val + 1) (c03_mult_Theta Ψ y) (w.1 * w.2) : ℝ) : ℂ) ^
                  rq.2 i else 0)‖) / ‖(((|w.2| ^ (1 + p) : ℝ) : ℂ))‖)
          ≤ 1 * (‖Complex.exp (-((η * w.2 ^ 2 : ℝ) : ℂ))‖ * (‖(w.2 : ℂ) ^ (2 * N - 1)‖ * Mh) /
              ‖(((|w.2| ^ (1 + p) : ℝ) : ℂ))‖) := by gcongr
        _ = _ := by ring
  -- pointwise rewriting of the left integrand
  have hpt : ∀ z : ℝ, Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
      c03_mult_taylorR Y a Ψ N y z * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) /
        ((|z| ^ (1 + p) : ℝ) : ℂ) = ∑ rq ∈ c03_mult_index N,
          ((2 * N - 1 : ℕ) : ℂ) * c03_mult_coeff rq.1 rq.2 * ∫ t in Ioc (0 : ℝ) 1, G rq t z := by
    intro z
    rw [(c03_mult_taylor_formula Y hY a Ψ ha has hΨ hlam N hN y hy z).2, Finset.mul_sum,
      Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun rq _ => ?_
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have e : ∀ t : ℝ, G rq t z = (Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
        Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) *
        ((((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (c03_mult_Theta Ψ y (t * z) : ℂ)) *
            c03_mult_bt Y a Ψ N rq.1 rq.2 y t z) := by
      intro t
      simp only [hG, c03_mult_phit]
      push_cast
      simp only [mul_add, sub_eq_add_neg, Complex.exp_add]
      ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun rq _ => by
    exact ((hGint rq).integral_prod_right).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun rq _ => ?_
  rw [← integral_integral_swap (hGint rq), intervalIntegral.integral_of_le zero_le_one]
  have e2 : ∀ t : ℝ, ∫ z : ℝ, G rq t z = (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
      c03_mult_I p Y a Ψ N rq.1 rq.2 η y t := by
    intro t
    simp only [hG, c03_mult_I]
    rw [integral_const_mul]
  simp_rw [e2]
  ring


lemma c03m_aux_bdd_ii {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) 1)))
    {M : ℝ} (hM : ∀ t ∈ Ioc (0 : ℝ) 1, ‖f t‖ ≤ M) : IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine (integrableOn_const (C := M) (by simp)).mono' hf ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall hM

/-- `I_η(y,t) → I_0(y,t)` as `η ↓ 0`. -/
lemma c03m_aux_I_tendsto (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (N : ℕ) (hN : 1 ≤ N) (r : ℕ)
    (q : Fin (2 * N - 1) → ℕ) (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) {Y : ℝ}
    (hY : 0 < Y) {a : ℝ → ℂ} {Ψ : ℝ → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (y : ℝ) (hy : y ∈ Ioo (Y / 2) (3 * Y)) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun η => c03_mult_I p Y a Ψ N r q η y t) (𝓝[>] 0)
      (𝓝 (c03_mult_I p Y a Ψ N r q 0 y t)) := by
  have hint : ∀ η : ℝ, Integrable (fun z : ℝ =>
      Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
        c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) := fun η => by
    have := ((c03m_aux_I_smooth_formula p hp hp1 1 one_pos N hN r q hrq Y hY a Ψ ha has hΨ t ht
      η).2 0 y hy).1
    simpa only [iteratedDeriv_zero] using this
  unfold c03_mult_I
  refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖Complex.exp (Complex.I *
      (c03_mult_phit Ψ y t z : ℂ) - ((0 * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a Ψ N r q y t z /
        ((|z| ^ (1 + p) : ℝ) : ℂ)‖) (Eventually.of_forall fun η => (hint η).aestronglyMeasurable)
    ?_ (hint 0).norm (Eventually.of_forall fun z => ?_)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    refine Eventually.of_forall fun z => ?_
    rw [norm_div, norm_mul, norm_div, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have hη' : 0 < η := hη
    have hre : (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)).re ≤
        (Complex.I * (c03_mult_phit Ψ y t z : ℂ) - ((0 * z ^ 2 : ℝ) : ℂ)).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, zero_sub, mul_zero, sub_zero]
      nlinarith [sq_nonneg z]
    gcongr ?_ * _ / _
    exact Real.exp_le_exp.2 hre
  · have hc : Continuous (fun η : ℝ => Complex.exp (Complex.I * (c03_mult_phit Ψ y t z : ℂ) -
        ((η * z ^ 2 : ℝ) : ℂ)) * c03_mult_bt Y a Ψ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) := by
      fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c03_mult_remainder_parameter_integral.  For each `j` there is `k₀ = k₀(p,N,j)`
such that under `𝖧` through order `k₀`, with `n = 2N-1`:
`ℛ_{mult,N}(y) = -c_p n ∑_{(r,q)} d_{r,q} ∫₀¹ (1-t)^{n-1} I₀(y,t) dt` (absolutely convergent
`t`-integrals), `ℛ_{mult,N}` is `C^j` on `(Y/2,3Y)`, and its derivatives of order `≤ j` are the
same finite sums with `∂_y^i I₀` under the `t`-integral.
Encoding: the representation is stated on `(Y/2,3Y)` (contains `[Y,2Y]`), where the
derivatives are taken. The all-orders smoothness remark follows by applying this for every `j`. -/
theorem c03_mult_remainder_parameter_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ)
    (hc₀ : 0 < c₀) (N : ℕ) (hN : 1 ≤ N) :
    ∀ j : ℕ, ∃ k₀ : ℕ, ∀ (Ck : ℕ → ℝ) (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ),
      1 ≤ Y → 1 ≤ Λ → 0 < A → c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ →
      (∀ y ∈ Ioo (Y / 2) (3 * Y), ∀ i ≤ j, ∀ rq ∈ c03_mult_index N,
        IntervalIntegrable (fun t : ℝ => (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y' t) y) volume 0 1) ∧
      ContDiffOn ℝ j (c03_mult_R p Y a Ψ N) (Ioo (Y / 2) (3 * Y)) ∧
      ∀ i ≤ j, ∀ y ∈ Ioo (Y / 2) (3 * Y),
        iteratedDeriv i (c03_mult_R p Y a Ψ N) y =
          -(c03_cp p : ℂ) * ((2 * N - 1 : ℕ) : ℂ) *
            ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
              ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
                iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y' t) y := by
  intro j
  have hmemrq : ∀ rq ∈ c03_mult_index N, rq.1 + ∑ i, (i.val + 1) * rq.2 i = 2 * N - 1 :=
    fun rq h => (Finset.mem_filter.1 h).2
  have hP : ∀ rq ∈ c03_mult_index N, ∀ i : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ η : ℝ, 0 ≤ η →
        ∀ y ∈ Ioo (Y / 2) (3 * Y),
          ‖iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 η y' t) y‖ ≤
            C * c03_mult_size N rq.2 Y Λ A t * Y ^ (-(i : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 rq.2 : ℕ) : ℝ)) := fun rq h i =>
    c03_mult_parameter_ibp_bound p hp hp1 c₀ hc₀ N hN rq.1 rq.2 (hmemrq rq h) i
  choose! k0 hk0 using hP
  set K0 : ℕ := ∑ rq ∈ c03_mult_index N, ∑ i ∈ Finset.range (j + 2), k0 rq i with hK0
  have hkK : ∀ rq ∈ c03_mult_index N, ∀ i ≤ j + 1, k0 rq i ≤ K0 := by
    intro rq hrq i hi
    calc k0 rq i ≤ ∑ i' ∈ Finset.range (j + 2), k0 rq i' :=
          Finset.single_le_sum (f := fun i' => k0 rq i') (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.2 (by omega))
      _ ≤ K0 := Finset.single_le_sum (f := fun rq' => ∑ i' ∈ Finset.range (j + 2), k0 rq' i')
            (fun _ _ => Nat.zero_le _) hrq
  refine ⟨K0, fun Ck Y Λ A a Ψ hY hΛ hA hyp => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨ha, has, hΨ, -⟩ := id hyp
  have hlam := c03m_aux_lam_pos hc₀ hΛ hyp
  set V := Ioo (Y / 2) (3 * Y) with hV_def
  have hV : IsOpen V := isOpen_Ioo
  -- uniform bounds
  have hM : ∀ rq ∈ c03_mult_index N, ∀ i ≤ j + 1, ∃ M, ∀ y ∈ V, ∀ t ∈ Ioc (0 : ℝ) 1,
      ∀ η : ℝ, 0 ≤ η →
        ‖iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 η y' t) y‖ ≤ M := by
    intro rq hrq i hi
    obtain ⟨C, hC, hb⟩ := hk0 rq hrq i Ck
    refine ⟨C * (A * Λ ^ (c03_mult_q1 rq.2 + c03_mult_ell rq.2) *
      Y ^ (-(2 * N : ℝ) + 1 + c03_mult_ell rq.2)) * Y ^ (-(i : ℝ)) *
        Λ ^ (p - ((2 * N - 1 + c03_mult_q1 rq.2 : ℕ) : ℝ)), fun y hy t ht η hη => ?_⟩
    refine (hb Y Λ A a Ψ hY hΛ hA (c03m_aux_hyp_mono (hkK rq hrq i hi) hyp) t ht η hη y hy).trans ?_
    have hs : c03_mult_size N rq.2 Y Λ A t ≤ A * Λ ^ (c03_mult_q1 rq.2 + c03_mult_ell rq.2) *
        Y ^ (-(2 * N : ℝ) + 1 + c03_mult_ell rq.2) := by
      unfold c03_mult_size
      have h1 : t ^ c03_mult_q1 rq.2 ≤ 1 := pow_le_one₀ ht.1.le ht.2
      have h2 : 0 ≤ A * Λ ^ (c03_mult_q1 rq.2 + c03_mult_ell rq.2) *
          Y ^ (-(2 * N : ℝ) + 1 + c03_mult_ell rq.2) := by positivity
      nlinarith
    have : 0 ≤ Y ^ (-(i : ℝ)) * Λ ^ (p - ((2 * N - 1 + c03_mult_q1 rq.2 : ℕ) : ℝ)) := by
      positivity
    calc C * c03_mult_size N rq.2 Y Λ A t * Y ^ (-(i : ℝ)) *
          Λ ^ (p - ((2 * N - 1 + c03_mult_q1 rq.2 : ℕ) : ℝ))
        = C * c03_mult_size N rq.2 Y Λ A t * (Y ^ (-(i : ℝ)) *
          Λ ^ (p - ((2 * N - 1 + c03_mult_q1 rq.2 : ℕ) : ℝ))) := by ring
      _ ≤ C * (A * Λ ^ (c03_mult_q1 rq.2 + c03_mult_ell rq.2) *
          Y ^ (-(2 * N : ℝ) + 1 + c03_mult_ell rq.2)) * (Y ^ (-(i : ℝ)) *
          Λ ^ (p - ((2 * N - 1 + c03_mult_q1 rq.2 : ℕ) : ℝ))) := by gcongr
      _ = _ := by ring
  choose! M hMb using hM
  -- the `t`-integrands
  have hw : ∀ t ∈ Ioc (0 : ℝ) 1, ‖(((1 - t) ^ (2 * N - 2) : ℝ) : ℂ)‖ ≤ 1 := by
    intro t ht
    rw [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [ht.2])]
    exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
  have hwc : Continuous (fun t : ℝ => (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ)) := by fun_prop
  have hmeas : ∀ rq ∈ c03_mult_index N, ∀ i, ∀ y ∈ V, ∀ η : ℝ, AEStronglyMeasurable
      (fun t => (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
        iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 η y' t) y)
      (volume.restrict (Ioc (0 : ℝ) 1)) := fun rq hrq i y hy η =>
    hwc.aestronglyMeasurable.mul (c03m_aux_I_meas p hp hp1 N hN rq.1 rq.2 (hmemrq rq hrq) hY0 ha
      has hΨ η i y hy)
  have hbdw : ∀ rq ∈ c03_mult_index N, ∀ i ≤ j + 1, ∀ y ∈ V, ∀ η : ℝ, 0 ≤ η →
      ∀ t ∈ Ioc (0 : ℝ) 1, ‖(((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
        iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 η y' t) y‖ ≤ M rq i := by
    intro rq hrq i hi y hy η hη t ht
    rw [norm_mul]
    have := hMb rq hrq i hi y hy t ht η hη
    calc _ ≤ 1 * M rq i := mul_le_mul (hw t ht) this (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hii : ∀ rq ∈ c03_mult_index N, ∀ i ≤ j + 1, ∀ y ∈ V, IntervalIntegrable (fun t : ℝ =>
      (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
        iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y' t) y) volume 0 1 :=
    fun rq hrq i hi y hy => c03m_aux_bdd_ii (hmeas rq hrq i y hy 0)
      (hbdw rq hrq i hi y hy 0 le_rfl)
  -- the formula functions
  set Φ : ℕ → ℝ → ℂ := fun i y => -(c03_cp p : ℂ) * ((2 * N - 1 : ℕ) : ℂ) *
    ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
      ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
        iteratedDeriv i (fun y' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y' t) y with hΦ
  -- derivatives of the formula functions
  have hderiv : ∀ i ≤ j, ∀ y ∈ V, HasDerivAt (Φ i) (Φ (i + 1) y) y := by
    intro i hi y hy
    have hrq : ∀ rq ∈ c03_mult_index N, HasDerivAt (fun y' => ∫ t in (0 : ℝ)..1,
        (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y'' t) y')
        (∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          iteratedDeriv (i + 1) (fun y'' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y'' t) y) y := by
      intro rq hrq
      refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
        (a := 0) (b := 1)
        (F := fun y' t => (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y'' t) y')
        (F' := fun y' t => (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
          iteratedDeriv (i + 1) (fun y'' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y'' t) y')
        (bound := fun _ => M rq (i + 1)) (hV.mem_nhds hy) ?_ (hii rq hrq i (by omega) y hy) ?_ ?_
        intervalIntegrable_const ?_).2
      · filter_upwards [hV.mem_nhds hy] with y' hy'
        rw [Set.uIoc_of_le zero_le_one]
        exact hmeas rq hrq i y' hy' 0
      · rw [Set.uIoc_of_le zero_le_one]
        exact hmeas rq hrq (i + 1) y hy 0
      · refine Eventually.of_forall fun t ht y' hy' => ?_
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact hbdw rq hrq (i + 1) (by omega) y' hy' 0 le_rfl t ht
      · refine Eventually.of_forall fun t ht y' hy' => ?_
        rw [Set.uIoc_of_le zero_le_one] at ht
        have hsm := (c03m_aux_I_smooth_formula p hp hp1 1 one_pos N hN rq.1 rq.2 (hmemrq rq hrq) Y
          hY0 a Ψ ha has hΨ t ht 0).1
        have hd : DifferentiableAt ℝ
            (iteratedDeriv i (fun y'' => c03_mult_I p Y a Ψ N rq.1 rq.2 0 y'' t)) y' :=
          ((c03m_aux_iteratedDeriv_contDiffOnC hV hsm i).differentiableOn (by simp)).differentiableAt
            (hV.mem_nhds hy')
        have := hd.hasDerivAt.const_mul ((((1 - t) ^ (2 * N - 2) : ℝ) : ℂ))
        rwa [← iteratedDeriv_succ] at this
    have hsum := HasDerivAt.fun_sum (u := c03_mult_index N) (fun rq hrq' => (hrq rq hrq').const_mul
      (c03_mult_coeff rq.1 rq.2))
    exact hsum.const_mul _
  -- the base representation
  have hbase : ∀ y ∈ V, c03_mult_R p Y a Ψ N y = Φ 0 y := by
    intro y hy
    obtain ⟨-, hlim⟩ := c03_mult_taylor_regularized_limit p hp hp1 Y hY a Ψ ha has hΨ hlam N hN y hy
    have hlim2 : Tendsto (fun η : ℝ => -(c03_cp p : ℂ) * (((2 * N - 1 : ℕ) : ℂ) *
        ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
          ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
            c03_mult_I p Y a Ψ N rq.1 rq.2 η y t)) (𝓝[>] 0) (𝓝 (Φ 0 y)) := by
      have e : Φ 0 y = -(c03_cp p : ℂ) * (((2 * N - 1 : ℕ) : ℂ) *
          ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
            ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
              c03_mult_I p Y a Ψ N rq.1 rq.2 0 y t) := by
        simp only [hΦ, iteratedDeriv_zero]; ring
      rw [e]
      refine ((tendsto_finsetSum _ fun rq hrq => ?_).const_mul _).const_mul _
      refine Tendsto.const_mul _ ?_
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => M rq 0) ?_ ?_ intervalIntegrable_const ?_
      · refine Eventually.of_forall fun η => ?_
        rw [Set.uIoc_of_le zero_le_one]
        simpa only [iteratedDeriv_zero] using hmeas rq hrq 0 y hy η
      · filter_upwards [self_mem_nhdsWithin] with η hη
        refine Eventually.of_forall fun t ht => ?_
        rw [Set.uIoc_of_le zero_le_one] at ht
        simpa only [iteratedDeriv_zero] using hbdw rq hrq 0 (by omega) y hy η (le_of_lt hη) t ht
      · refine Eventually.of_forall fun t ht => ?_
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact (c03m_aux_I_tendsto p hp hp1 N hN rq.1 rq.2 (hmemrq rq hrq) hY0 ha has hΨ y hy t
          ht).const_mul _
    have heq : (fun η : ℝ => -(c03_cp p : ℂ) * ∫ z : ℝ,
        Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) * c03_mult_taylorR Y a Ψ N y z *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
        fun η => -(c03_cp p : ℂ) * (((2 * N - 1 : ℕ) : ℂ) *
          ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
            ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
              c03_mult_I p Y a Ψ N rq.1 rq.2 η y t) := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [c03m_aux_R_fubini p hp hp1 hY ha has hΨ hlam N hN y hy η hη]
    exact tendsto_nhds_unique hlim (hlim2.congr' heq.symm)
  -- iterated derivatives
  have hiter : ∀ i ≤ j + 1, ∀ y ∈ V, iteratedDeriv i (c03_mult_R p Y a Ψ N) y = Φ i y := by
    intro i
    induction i with
    | zero => intro _ y hy; rw [iteratedDeriv_zero]; exact hbase y hy
    | succ i ih =>
      intro hi y hy
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv i (c03_mult_R p Y a Ψ N) =ᶠ[𝓝 y] Φ i := by
        filter_upwards [hV.mem_nhds hy] with y' hy' using ih (by omega) y' hy'
      rw [hev.deriv_eq]
      exact (hderiv i (by omega) y hy).deriv
  refine ⟨fun y hy i hi rq hrq => hii rq hrq i (by omega) y hy, ?_, fun i hi y hy => ?_⟩
  · refine contDiffOn_of_differentiableOn_deriv fun m hm => ?_
    have hm' : m ≤ j := by exact_mod_cast hm
    intro y hy
    have h1 : DifferentiableAt ℝ (Φ m) y := (hderiv m hm' y hy).differentiableAt
    have h2 : iteratedDerivWithin m (c03_mult_R p Y a Ψ N) V =ᶠ[𝓝 y] Φ m := by
      filter_upwards [hV.mem_nhds hy] with y' hy'
      rw [iteratedDerivWithin_of_isOpen hV hy', hiter m (by omega) y' hy']
    exact (h1.congr_of_eventuallyEq h2).differentiableWithinAt
  · rw [hiter i (by omega) y hy]

/-! ## The remainder to all orders -/

/-- Blueprint: lem:c03_mult_remainder_all_orders.  For every `j` there is `k₀ = k₀(p,N,j)` such
that for all finite symbol constants there is `C > 0` with
`|∂_y^j ℛ_{mult,N}(y)| ≤ C A Y^{-N-j} Λ^{p-N}` on `[Y,2Y]`, and for two data with `δ`-close
derivatives (`δ ≥ 0`), `|∂_y^j(ℛ_{mult,N,1} - ℛ_{mult,N,0})| ≤ C min(1,δ) A Y^{-N-j} Λ^{p-N}`. -/
theorem c03_mult_remainder_all_orders (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ)
    (hc₀ : 0 < c₀) (N : ℕ) (hN : 1 ≤ N) :
    ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      (∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
        c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y),
          ‖iteratedDeriv j (c03_mult_R p Y a Ψ N) y‖ ≤
            C * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) ∧
      (∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ →
        c03_mult_hyp Y Λ A c₀ Ck k₀ a₀ Ψ₀ → c03_mult_hyp Y Λ A c₀ Ck k₀ a₁ Ψ₁ →
        (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ k₀,
          ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
          |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
        ∀ y ∈ Icc Y (2 * Y),
          ‖iteratedDeriv j (fun y' => c03_mult_R p Y a₁ Ψ₁ N y' - c03_mult_R p Y a₀ Ψ₀ N y') y‖ ≤
            C * min 1 δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by
  intro j
  classical
  set s := c03_mult_index N
  have hrqs : ∀ rq ∈ s, rq.1 + ∑ i, (i.val + 1) * rq.2 i = 2 * N - 1 :=
    fun rq h => (Finset.mem_filter.1 h).2
  obtain ⟨kR, hR⟩ := c03_mult_remainder_parameter_integral p hp hp1 c₀ hc₀ N hN j
  obtain ⟨KI, hKI⟩ := c03m_aux_finite_order s _ (fun rq h =>
    c03_mult_parameter_ibp p hp hp1 c₀ hc₀ N hN rq.1 rq.2 (hrqs rq h) j)
  obtain ⟨KD, hKD⟩ := c03m_aux_finite_order s _ (fun rq h =>
    c03_mult_difference_integral_bound p hp hp1 c₀ hc₀ N hN rq.1 rq.2 (hrqs rq h) j)
  choose! kI hkIle hkI using hKI
  choose! kD hkDle hkD using hKD
  refine ⟨max kR (max KI KD), fun Ck => ?_⟩
  choose! CI hCI hI using fun rq (h : rq ∈ s) => hkI rq h Ck
  choose! CD hCD hD using fun rq (h : rq ∈ s) => hkD rq h Ck
  have hW : 0 ≤ |c03_cp p| * ((2 * N - 1 : ℕ) : ℝ) *
      ∑ rq ∈ s, ‖c03_mult_coeff rq.1 rq.2‖ * (2 * CI rq + 2 * CD rq) := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro rq h
    have := hCI rq h; have := hCD rq h
    positivity
  refine ⟨|c03_cp p| * ((2 * N - 1 : ℕ) : ℝ) *
      ∑ rq ∈ s, ‖c03_mult_coeff rq.1 rq.2‖ * (2 * CI rq + 2 * CD rq) + 1, by positivity, ?_, ?_⟩
  · intro Y Λ A a Ψ hY hΛ hA hyp y hy
    have hY0 : 0 < Y := by linarith
    have hΛ0 : 0 < Λ := by linarith
    have hy' := c03m_aux_Icc_sub_Ioo hY hy
    have hM : 0 ≤ A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
      have := Real.rpow_nonneg hY0.le (-((N : ℝ) + j))
      have := Real.rpow_nonneg hΛ0.le (p - N)
      positivity
    obtain ⟨-, -, hrep⟩ := hR Ck Y Λ A a Ψ hY hΛ hA
      (c03m_aux_hyp_mono (le_max_left _ _) hyp)
    rw [hrep j le_rfl y hy']
    refine (c03m_aux_param_sum_bound s _ _ (fun rq => 2 * CI rq + 2 * CD rq)
      (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) _ _ _ (fun rq h t ht => ?_)).trans ?_
    · have hk : kI rq ≤ max kR (max KI KD) :=
        (hkIle rq h).trans ((le_max_left _ _).trans (le_max_right _ _))
      have hb := (hI rq h Y Λ A a Ψ hY hΛ hA (c03m_aux_hyp_mono hk hyp) t ht 0 le_rfl).2.2 y hy'
      have := hCI rq h; have := hCD rq h
      calc _ ≤ _ := hb.1.trans hb.2
        _ ≤ (2 * CI rq + 2 * CD rq) * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by
          have e : CI rq * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) =
              CI rq * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (by linarith) hM
    · nlinarith
  · intro Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ hyp₀ hyp₁ hdiff y hy
    have hY0 : 0 < Y := by linarith
    have hΛ0 : 0 < Λ := by linarith
    have hy' := c03m_aux_Icc_sub_Ioo hY hy
    set M := A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)
    have hM : 0 ≤ M := by
      have := Real.rpow_nonneg hY0.le (-((N : ℝ) + j))
      have := Real.rpow_nonneg hΛ0.le (p - N)
      positivity
    obtain ⟨hii₀, hcd₀, hrep₀⟩ := hR Ck Y Λ A a₀ Ψ₀ hY hΛ hA
      (c03m_aux_hyp_mono (le_max_left _ _) hyp₀)
    obtain ⟨hii₁, hcd₁, hrep₁⟩ := hR Ck Y Λ A a₁ Ψ₁ hY hΛ hA
      (c03m_aux_hyp_mono (le_max_left _ _) hyp₁)
    have hnhds : Ioo (Y / 2) (3 * Y) ∈ 𝓝 y := isOpen_Ioo.mem_nhds hy'
    rw [iteratedDeriv_fun_sub ((hcd₁.contDiffAt hnhds)) ((hcd₀.contDiffAt hnhds)),
      hrep₁ j le_rfl y hy', hrep₀ j le_rfl y hy', ← mul_sub, ← Finset.sum_sub_distrib]
    have hsum : ∀ rq ∈ s,
        c03_mult_coeff rq.1 rq.2 * (∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
            iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N rq.1 rq.2 0 y' t) y) -
          c03_mult_coeff rq.1 rq.2 * (∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
            iteratedDeriv j (fun y' => c03_mult_I p Y a₀ Ψ₀ N rq.1 rq.2 0 y' t) y) =
        c03_mult_coeff rq.1 rq.2 * ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
            (iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N rq.1 rq.2 0 y' t) y -
              iteratedDeriv j (fun y' => c03_mult_I p Y a₀ Ψ₀ N rq.1 rq.2 0 y' t) y) := by
      intro rq h
      rw [← mul_sub, ← intervalIntegral.integral_sub (hii₁ y hy' j le_rfl rq h)
        (hii₀ y hy' j le_rfl rq h)]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simp only
      ring
    rw [Finset.sum_congr rfl hsum]
    refine (c03m_aux_param_sum_bound s _ _ (fun rq => 2 * CI rq + 2 * CD rq) (min 1 δ * M) _ _ _
      (fun rq h t ht => ?_)).trans ?_
    · have hkI' : kI rq ≤ max kR (max KI KD) :=
        (hkIle rq h).trans ((le_max_left _ _).trans (le_max_right _ _))
      have hkD' : kD rq ≤ max kR (max KI KD) :=
        (hkDle rq h).trans ((le_max_right _ _).trans (le_max_right _ _))
      obtain ⟨hs₁, -, hb₁⟩ := hI rq h Y Λ A a₁ Ψ₁ hY hΛ hA (c03m_aux_hyp_mono hkI' hyp₁) t ht 0
        le_rfl
      obtain ⟨hs₀, -, hb₀⟩ := hI rq h Y Λ A a₀ Ψ₀ hY hΛ hA (c03m_aux_hyp_mono hkI' hyp₀) t ht 0
        le_rfl
      have hCI0 := hCI rq h; have hCD0 := hCD rq h
      by_cases hδ1 : δ ≤ 1
      · have hd := (hD rq h Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ (c03m_aux_hyp_mono hkD' hyp₀)
          (c03m_aux_hyp_mono hkD' hyp₁)
          (fun x hx k hk => hdiff x hx k (hk.trans hkD')) y hy t ht 0 le_rfl)
        have e : iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N rq.1 rq.2 0 y' t) y -
            iteratedDeriv j (fun y' => c03_mult_I p Y a₀ Ψ₀ N rq.1 rq.2 0 y' t) y =
            iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N rq.1 rq.2 0 y' t -
              c03_mult_I p Y a₀ Ψ₀ N rq.1 rq.2 0 y' t) y := by
          rw [iteratedDeriv_fun_sub ((hs₁.contDiffAt hnhds).of_le (by exact_mod_cast le_top))
            ((hs₀.contDiffAt hnhds).of_le (by exact_mod_cast le_top))]
        rw [e, min_eq_right hδ1]
        refine hd.1.trans (hd.2.trans ?_)
        have : 0 ≤ δ * M := mul_nonneg hδ hM
        calc 2 * CD rq * δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) = (2 * CD rq) * (δ * M) := by
              simp only [M]; ring
          _ ≤ (2 * CI rq + 2 * CD rq) * (δ * M) := by nlinarith
      · rw [min_eq_left (by linarith)]
        have b1 := (hb₁ y hy').1.trans (hb₁ y hy').2
        have b0 := (hb₀ y hy').1.trans (hb₀ y hy').2
        refine (norm_sub_le _ _).trans ?_
        have : 0 ≤ CI rq * M := mul_nonneg hCI0.le hM
        have hM' : 0 ≤ CD rq * M := mul_nonneg hCD0.le hM
        calc _ ≤ CI rq * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) +
              CI rq * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := add_le_add b1 b0
          _ = 2 * (CI rq * M) := by simp only [M]; ring
          _ ≤ (2 * CI rq + 2 * CD rq) * (1 * M) := by nlinarith
    · have : 0 ≤ min 1 δ * M := mul_nonneg (le_min zero_le_one hδ) hM
      calc _ = (|c03_cp p| * ((2 * N - 1 : ℕ) : ℝ) *
            ∑ rq ∈ s, ‖c03_mult_coeff rq.1 rq.2‖ * (2 * CI rq + 2 * CD rq)) * (min 1 δ * M) := rfl
        _ ≤ (|c03_cp p| * ((2 * N - 1 : ℕ) : ℝ) *
            ∑ rq ∈ s, ‖c03_mult_coeff rq.1 rq.2‖ * (2 * CI rq + 2 * CD rq) + 1) *
              (min 1 δ * M) := by nlinarith
        _ = _ := by simp only [M]; ring

/-! ## Chapter-3 nodes (prefixed `c03m_`, same statements as in `AppendixAB/Statements.lean`) -/


/-- Blueprint: lem:c03_mult_expansion.  Kernel representation of
`e^{-iΨ}|D|^p(ae^{iΨ}) - λ^p a`, the oscillatory-integral representation of `ℛ_{mult,N}` and
the Taylor remainder formula (eqn:appendix_oscillatory_multiplier_taylor_remainder). -/
theorem c03m_c03_mult_expansion (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Y Λ : ℝ) (hY : 1 ≤ Y)
    (hΛ : 1 ≤ Λ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (hlam : ∀ y ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ y) (y : ℝ) (hy : y ∈ Icc Y (2 * Y)) :
    ContDiff ℝ (⊤ : ℕ∞) (c03_mult_F Y a Ψ y) ∧ HasCompactSupport (c03_mult_F Y a Ψ y) ∧
    Integrable (fun z : ℝ => Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
      (c03_mult_F Y a Ψ y z - a y) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    Complex.exp (-(Complex.I * (Ψ y : ℂ))) *
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y -
        ((deriv Ψ y ^ p : ℝ) : ℂ) * a y =
      -(c03_cp p : ℂ) * ∫ z : ℝ, Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
        (c03_mult_F Y a Ψ y z - a y) / ((|z| ^ (1 + p) : ℝ) : ℂ) ∧
    ∀ N : ℕ, 1 ≤ N →
      Tendsto (fun η : ℝ => -(c03_cp p : ℂ) * ∫ z : ℝ,
          Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) * c03_mult_taylorR Y a Ψ N y z *
            Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (c03_mult_R p Y a Ψ N y)) ∧
      ∀ z : ℝ, c03_mult_taylorR Y a Ψ N y z =
        ((2 * N - 1 : ℕ) : ℂ) * ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
          ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (c03_mult_Theta Ψ y (t * z) : ℂ)) *
            c03_mult_bt Y a Ψ N rq.1 rq.2 y t z := by
  have hy' : y ∈ Ioo (Y / 2) (3 * Y) := c03m_aux_Icc_sub_Ioo hY hy
  obtain ⟨h1, h2, -, -, h5, h6⟩ :=
    c03_mult_kernel_identity p hp hp1 Y hY a Ψ ha has hΨ hlam y hy'
  refine ⟨h1, h2, h5, h6, fun N hN => ⟨?_, fun z => ?_⟩⟩
  · exact (c03_mult_taylor_regularized_limit p hp hp1 Y hY a Ψ ha has hΨ hlam N hN y hy').2
  · exact (c03_mult_taylor_formula Y hY a Ψ ha has hΨ hlam N hN y hy' z).2

/-- Blueprint: lem:c03_mult_summand.  Symbol bounds for `b_t`, the phase bounds for `φ_t`, and
the bound `|∂_y^j I_η(y,t)| ≤ C B Y^{-j} Λ^{p-K} ≤ C A Y^{-N-j} Λ^{p-N}` (`K = 2N-1+q₁`),
uniformly in `t ∈ (0,1]`, `y ∈ [Y,2Y]`, `η ≥ 0`; constants depend on `p, N, s, j, c₀` and finitely
many `C_k`. -/
theorem c03m_c03_mult_summand (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ)
    (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    (∀ s : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∀ z : ℝ, z ≠ 0 → ‖iteratedDeriv s (c03_mult_bt Y a Ψ N r q y t) z‖ ≤
        C * c03_mult_size N q Y Λ A t * |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s)) ∧
      (∀ z : ℝ, y + t * z ∈ Ioo (Y / 4) (4 * Y) →
        deriv (c03_mult_phit Ψ y t) z = (1 - t) * deriv Ψ y + t * deriv Ψ (y + t * z) ∧
        c₀⁻¹ * Λ ≤ deriv (c03_mult_phit Ψ y t) z ∧ deriv (c03_mult_phit Ψ y t) z ≤ c₀ * Λ ∧
        |iteratedDeriv s (fun z => 1 / deriv (c03_mult_phit Ψ y t) z) z| ≤
          C * Λ⁻¹ * (t / Y) ^ s ∧
        (z ≠ 0 → |iteratedDeriv s (fun z => 1 / deriv (c03_mult_phit Ψ y t) z) z| ≤
          C * Λ⁻¹ * |z| ^ (-(s : ℝ))))) ∧
    (∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1,
      ∀ η : ℝ, 0 ≤ η →
        ‖iteratedDeriv j (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y‖ ≤
          C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) ∧
        C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) ≤
          C * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by
  refine ⟨fun s => ⟨2 * N + s + 2, fun Ck => ?_⟩, fun j => ?_⟩
  · obtain ⟨Ca, hCa, hA⟩ := c03_mult_amplitude_symbol c₀ hc₀ N hN r q hrq 0 s Ck
    obtain ⟨Cp, hCp, hP⟩ := c03_mult_phase_symbol c₀ hc₀ 0 s Ck
    have h3 : (1 : ℝ) ≤ 3 ^ s := one_le_pow₀ (by norm_num)
    refine ⟨(Ca + Cp) * 3 ^ s, by positivity, ?_⟩
    intro Y Λ A a Ψ hY hΛ hA0 hyp y hy t ht
    have hY0 : 0 < Y := by linarith
    have hΛ0 : 0 < Λ := by linarith
    have hy' := c03m_aux_Icc_sub_Ioo hY hy
    have hyp' : c03_mult_hyp Y Λ A c₀ Ck (2 * N + 0 + s + 2) a Ψ := by simpa using hyp
    obtain ⟨-, -, hΨs, hb⟩ := hyp
    have hph : ∀ x ∈ Ioo (Y / 4) (4 * Y), c₀⁻¹ * Λ ≤ deriv Ψ x ∧ deriv Ψ x ≤ c₀ * Λ ∧
        ∀ k ≤ 0 + s + 2, |iteratedDeriv k (deriv Ψ) x| ≤ Ck k * Λ * Y ^ (-(k : ℝ)) :=
      fun x hx => ⟨(hb x hx).1, (hb x hx).2.1, fun k hk => ((hb x hx).2.2 k (by omega)).1⟩
    have hS : 0 ≤ c03_mult_size N q Y Λ A t :=
      c03m_aux_size_nonneg N q hY0 hΛ0.le hA0.le ht.1.le
    have hCle : Ca ≤ (Ca + Cp) * 3 ^ s := by nlinarith
    have hCle' : Cp ≤ (Ca + Cp) * 3 ^ s := by nlinarith
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have h := ((hA Y Λ A a Ψ hY hΛ hA0 hyp' t ht).2 y hy').2.2.2 z hz
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, neg_zero, Real.rpow_zero,
        mul_one] at h
      refine h.trans ?_
      have : 0 ≤ |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) :=
        Real.rpow_nonneg (abs_nonneg _) _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hS) this
    · obtain ⟨e0, -, -, l1, l2, rc, -⟩ := hP Y Λ Ψ Ψ hY hΛ hΨs hΨs hph hph 0
        ⟨le_rfl, zero_le_one⟩ y hy' t ht z hz
      have hfun : ∀ y' : ℝ, (fun z' => (1 - (0 : ℝ)) * c03_mult_phit Ψ y' t z' +
          0 * c03_mult_phit Ψ y' t z') = c03_mult_phit Ψ y' t := by
        intro y'; funext z'; ring
      simp only [hfun, iteratedDeriv_zero, CharP.cast_eq_zero, neg_zero, Real.rpow_zero,
        mul_one] at l1 l2 rc
      have hL : 0 ≤ Λ⁻¹ := by positivity
      have htY : 0 ≤ (t / Y) ^ s := by have := ht.1; positivity
      refine ⟨e0, l1, l2, rc.trans ?_, fun hz0 => rc.trans ?_⟩
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle' hL) htY
      -- `t / Y ≤ 3 / |z|` on the phase domain
      have htz : t * |z| ≤ 3 * Y := by
        have h1 : |t * z| ≤ 3 * Y := by
          rw [abs_le]; constructor <;> nlinarith [hz.1, hz.2, hy.1, hy.2]
        rwa [abs_mul, abs_of_pos ht.1] at h1
      have hz0' : 0 < |z| := abs_pos.mpr hz0
      have hq : t / Y ≤ 3 * |z|⁻¹ := by
        rw [div_le_iff₀ hY0]
        calc t = t * |z| * |z|⁻¹ := by field_simp
          _ ≤ 3 * Y * |z|⁻¹ := by gcongr
          _ = 3 * |z|⁻¹ * Y := by ring
      have hpow : (t / Y) ^ s ≤ 3 ^ s * |z| ^ (-(s : ℝ)) := by
        rw [Real.rpow_neg hz0'.le, Real.rpow_natCast, ← inv_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by have := ht.1; positivity) hq s
      have hzs : 0 ≤ |z| ^ (-(s : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
      calc Cp * Λ⁻¹ * (t / Y) ^ s
          ≤ Cp * Λ⁻¹ * (3 ^ s * |z| ^ (-(s : ℝ))) := by gcongr
        _ = (Cp * 3 ^ s) * Λ⁻¹ * |z| ^ (-(s : ℝ)) := by ring
        _ ≤ ((Ca + Cp) * 3 ^ s) * Λ⁻¹ * |z| ^ (-(s : ℝ)) := by
            gcongr; linarith
  · obtain ⟨k₀, hk⟩ := c03_mult_parameter_ibp p hp hp1 c₀ hc₀ N hN r q hrq j
    refine ⟨k₀, fun Ck => ?_⟩
    obtain ⟨C, hC, h⟩ := hk Ck
    exact ⟨C, hC, fun Y Λ A a Ψ hY hΛ hA hyp y hy t ht η hη =>
      (h Y Λ A a Ψ hY hΛ hA hyp t ht η hη).2.2 y (c03m_aux_Icc_sub_Ioo hY hy)⟩

/-- Blueprint: lem:c03_mult_difference.  For two data `(a_ν, Ψ_ν)` with `δ`-close derivatives:
difference bounds for the amplitudes and phases, the interpolation identity
(eqn:appendix_oscillatory_multiplier_difference_integrals) and
`|∂_y^j(I₁ - I₀)| ≤ C δ B Y^{-j} Λ^{p-K} + C δ B Y^{-j-1} Λ^{p-K-1} ≤ 2 C δ A Y^{-N-j} Λ^{p-N}`. -/
-- The interpolation identity is stated for smooth, compactly supported data and `y, t` in the
-- stated domain; the phase-difference bounds are stated where `y + t z` lies in the phase domain;
-- the final sum carries the constant `2 C`.
theorem c03m_c03_mult_difference (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ)
    (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    -- the interpolation identity
    (∀ (Y : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ) (η y t : ℝ), 0 < Y →
      ContDiff ℝ (⊤ : ℕ∞) a₀ → tsupport a₀ ⊆ Ioo (Y / 4) (4 * Y) →
      ContDiff ℝ (⊤ : ℕ∞) a₁ → tsupport a₁ ⊆ Ioo (Y / 4) (4 * Y) →
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ₀ (Ioo (Y / 4) (4 * Y)) →
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ₁ (Ioo (Y / 4) (4 * Y)) →
      y ∈ Icc Y (2 * Y) → t ∈ Ioc (0 : ℝ) 1 → 0 < η →
      c03_mult_I p Y a₁ Ψ₁ N r q η y t - c03_mult_I p Y a₀ Ψ₀ N r q η y t =
        (∫ z : ℝ, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
          (c03_mult_bt Y a₁ Ψ₁ N r q y t z - c03_mult_bt Y a₀ Ψ₀ N r q y t z) /
            ((|z| ^ (1 + p) : ℝ) : ℂ)) +
        Complex.I * ∫ σ in (0 : ℝ)..1, ∫ z : ℝ,
          Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y t z +
              σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
            ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
            c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    -- the bounds
    ∀ j s : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ → δ ≤ 1 →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a₀ Ψ₀ → c03_mult_hyp Y Λ A c₀ Ck k₀ a₁ Ψ₁ →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ k₀,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
      ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∀ z : ℝ, z ≠ 0 →
        ‖iteratedDeriv j (fun y' => iteratedDeriv s (fun z' =>
            c03_mult_bt Y a₁ Ψ₁ N r q y' t z' - c03_mult_bt Y a₀ Ψ₀ N r q y' t z') z) y‖ ≤
          C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) ∧
        (y + t * z ∈ Ioo (Y / 4) (4 * Y) →
        |iteratedDeriv j (fun y' => iteratedDeriv s (fun z' =>
            c03_mult_phit Ψ₁ y' t z' - c03_mult_phit Ψ₀ y' t z') z) y| ≤
          C * δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ)))) ∧
      ∀ η : ℝ, 0 ≤ η →
        ‖iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N r q η y' t -
            c03_mult_I p Y a₀ Ψ₀ N r q η y' t) y‖ ≤
          C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
            C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) ∧
        C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
            C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) ≤
          2 * C * δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
  refine ⟨fun Y a₀ a₁ Ψ₀ Ψ₁ η y t hY ha₀ has₀ ha₁ has₁ hΨ₀ hΨ₁ hy ht hη => ?_, fun j s => ?_⟩
  · have hy' : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact ((c03_mult_interpolation_integral p hp hp1 N hN r q hrq Y a₀ a₁ Ψ₀ Ψ₁ hY ha₀ has₀
      ha₁ has₁ hΨ₀ hΨ₁ η t hη.le ht).1 y hy').2.2.2.2
  · obtain ⟨k₁, hk₁⟩ := c03_mult_difference_integral_bound p hp hp1 c₀ hc₀ N hN r q hrq j
    refine ⟨max (2 * N + j + s + 3) k₁, fun Ck => ?_⟩
    obtain ⟨Cs, hCs, hS⟩ := c03_mult_difference_symbols c₀ hc₀ N hN r q hrq j s Ck
    obtain ⟨Cb, hCb, hB⟩ := hk₁ Ck
    refine ⟨Cs + Cb, by positivity, ?_⟩
    intro Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ hδ1 hyp₀ hyp₁ hdiff y hy t ht
    have hY0 : 0 < Y := by linarith
    have hΛ0 : 0 < Λ := by linarith
    have hsz : 0 ≤ c03_mult_size N q Y Λ A t :=
      c03m_aux_size_nonneg N q hY0 hΛ0.le hA.le ht.1.le
    have hd1 : ∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ 2 * N + j + s + 3,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ)) :=
      fun x hx k hk => hdiff x hx k (hk.trans (le_max_left _ _))
    have hd2 : ∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ k₁,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ)) :=
      fun x hx k hk => hdiff x hx k (hk.trans (le_max_right _ _))
    have hS' := hS Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ
      (c03m_aux_hyp_mono (le_max_left _ _) hyp₀) (c03m_aux_hyp_mono (le_max_left _ _) hyp₁)
      hd1 y hy t ht
    have hB' := hB Y Λ A δ a₀ a₁ Ψ₀ Ψ₁ hY hΛ hA hδ
      (c03m_aux_hyp_mono (le_max_right _ _) hyp₀) (c03m_aux_hyp_mono (le_max_right _ _) hyp₁)
      hd2 y hy t ht
    refine ⟨fun z hz => ⟨(hS' z hz).1.trans ?_, fun hz' => ((hS' z hz).2 hz').trans ?_⟩,
      fun η hη => ⟨((hB' η hη).1).trans ?_, ?_⟩⟩
    · have : 0 ≤ δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
          |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) := by
        have := Real.rpow_nonneg hY0.le (-(j : ℝ))
        have := Real.rpow_nonneg (abs_nonneg z) (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s)
        positivity
      nlinarith
    · have : 0 ≤ δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ)) := by
        have := Real.rpow_nonneg hY0.le (-(j : ℝ) - 1)
        have := Real.rpow_nonneg (abs_nonneg z) (1 - (s : ℝ))
        positivity
      nlinarith
    · set X1 := c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
          Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ))
      set X2 := c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
          Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1)
      have h1 : 0 ≤ X1 := by
        have := Real.rpow_nonneg hY0.le (-(j : ℝ))
        have := Real.rpow_nonneg hΛ0.le (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ))
        positivity
      have h2 : 0 ≤ X2 := by
        have := Real.rpow_nonneg hY0.le (-(j : ℝ) - 1)
        have := Real.rpow_nonneg hΛ0.le (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1)
        positivity
      have e : ∀ C' : ℝ, C' * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
          C' * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) = C' * δ * (X1 + X2) := by
        intro C'; simp only [X1, X2]; ring
      rw [e, e]
      have : 0 ≤ δ * (X1 + X2) := by positivity
      nlinarith
    · have b1 := c03m_aux_size_bound N r hN q hrq (p := p) (Λ := Λ) (A := A) (t := t) (j : ℝ)
        hY hΛ hA.le ht.1.le ht.2
      have b2 := c03m_aux_size_bound2 N r hN q hrq (p := p) (Λ := Λ) (A := A) (t := t) (j : ℝ)
        hY hΛ hA.le ht.1.le ht.2
      have hC : 0 ≤ (Cs + Cb) * δ := by positivity
      have := add_le_add (mul_le_mul_of_nonneg_left b1 hC) (mul_le_mul_of_nonneg_left b2 hC)
      calc (Cs + Cb) * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
          (Cs + Cb) * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1)
          = (Cs + Cb) * δ * (c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ))) +
          (Cs + Cb) * δ * (c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1)) := by ring
        _ ≤ (Cs + Cb) * δ * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) +
            (Cs + Cb) * δ * (A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := this
        _ = 2 * (Cs + Cb) * δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by ring

/-- Blueprint: lem:appendix_oscillatory_multiplier.  Oscillatory multiplier expansion
`|D|^p(ae^{iΨ}) = e^{iΨ}[∑_{k=0}^{2N-2} B_k + ℛ_{mult,N}]` with
`|∂_y^j ℛ_{mult,N}| ≤ C A Y^{-N-j} Λ^{p-N}` (`j = 0,1`), the two-term form, and the difference
estimate `|∂_y^j(ℛ_{mult,N,1} - ℛ_{mult,N,0})| ≤ C min(1,δ) A Y^{-N-j} Λ^{p-N}` (all `j`);
`C = C(p, N, j, c₀, (C_k)_{k ≤ k₀(N,j)})`. -/
theorem c03m_appendix_oscillatory_multiplier (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ)
    (hc₀ : 0 < c₀) :
    -- the expansion (eqn:appendix_oscillatory_multiplier_expansion) and the remainder bound
    (∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, j ≤ 1 → ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y),
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y =
          Complex.exp (Complex.I * (Ψ y : ℂ)) *
            ((∑ k ∈ Finset.range (2 * N - 1), c03_mult_B p Y a Ψ k y) + c03_mult_R p Y a Ψ N y) ∧
        ‖iteratedDeriv j (c03_mult_R p Y a Ψ N) y‖ ≤
          C * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) ∧
    -- the two-term expansion
    (∀ j : ℕ, j ≤ 1 → ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y),
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y =
          Complex.exp (Complex.I * (Ψ y : ℂ)) *
            (((deriv Ψ y ^ p : ℝ) : ℂ) * a y -
              Complex.I * ((p * deriv Ψ y ^ (p - 1) : ℝ) : ℂ) * deriv a y -
              Complex.I * ((p * (p - 1) / 2 * deriv Ψ y ^ (p - 2) * deriv (deriv Ψ) y : ℝ) : ℂ) *
                a y +
              c03_mult_R2tilde p Y a Ψ y) ∧
        ‖iteratedDeriv j (c03_mult_R2tilde p Y a Ψ) y‖ ≤
          C * A * Y ^ (-(2 : ℝ) - j) * Λ ^ (p - 2)) ∧
    -- the difference estimate
    (∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a₀ Ψ₀ → c03_mult_hyp Y Λ A c₀ Ck k₀ a₁ Ψ₁ →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ k₀,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
      ∀ y ∈ Icc Y (2 * Y),
        ‖iteratedDeriv j (fun y' => c03_mult_R p Y a₁ Ψ₁ N y' - c03_mult_R p Y a₀ Ψ₀ N y') y‖ ≤
          C * min 1 δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by
  refine ⟨fun N hN j _ => ?_, fun j hj => ?_, fun N hN j => ?_⟩
  · obtain ⟨k₀, hk⟩ := c03_mult_remainder_all_orders p hp hp1 c₀ hc₀ N hN j
    refine ⟨k₀, fun Ck => ?_⟩
    obtain ⟨C, hC, h1, -⟩ := hk Ck
    exact ⟨C, hC, fun Y Λ A a Ψ hY hΛ hA hyp y hy =>
      ⟨c03m_aux_R_identity p Y a Ψ N y, h1 Y Λ A a Ψ hY hΛ hA hyp y hy⟩⟩
  · obtain ⟨k₀, hk⟩ := c03_mult_remainder_all_orders p hp hp1 c₀ hc₀ 2 (by norm_num) j
    refine ⟨max k₀ 4, fun Ck => ?_⟩
    obtain ⟨C₁, hC₁, h1, -⟩ := hk Ck
    obtain ⟨hB, hT⟩ := c03_mult_two_term_coefficients p hp hp1 c₀ hc₀
    obtain ⟨C₂, hC₂, h2⟩ := hT j hj Ck
    refine ⟨C₁ + C₂, by positivity, fun Y Λ A a Ψ hY hΛ hA hyp y hy => ⟨?_, ?_⟩⟩
    · have hY0 : 0 < Y := by linarith
      obtain ⟨e0, e1, e2⟩ := hB Y a Ψ hY0 hyp.1 hyp.2.1 hyp.2.2.1
        (c03m_aux_lam_pos hc₀ hΛ hyp) y hy
      rw [c03m_aux_R_identity p Y a Ψ 2 y]
      congr 1
      have hs : ∑ k ∈ Finset.range (2 * 2 - 1), c03_mult_B p Y a Ψ k y =
          c03_mult_B p Y a Ψ 0 y + c03_mult_B p Y a Ψ 1 y + c03_mult_B p Y a Ψ 2 y := by
        simp [Finset.sum_range_succ]
      rw [hs, e0, e1, e2]
      unfold c03_mult_R2tilde
      push_cast
      ring
    · have hY0 : 0 < Y := by linarith
      have hy' : y ∈ Ioo (Y / 4) (4 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have b1 := h1 Y Λ A a Ψ hY hΛ hA (c03m_aux_hyp_mono (le_max_left _ _) hyp) y hy
      have b2 := h2 Y Λ A a Ψ hY hΛ hA (c03m_aux_hyp_mono (le_max_right _ _) hyp) y hy
      have hE : (-(((2 : ℕ) : ℝ) + j)) = -(2 : ℝ) - j := by push_cast; ring
      rw [hE] at b1
      push_cast at b1
      have hpos : 0 ≤ A * Y ^ (-(2 : ℝ) - j) * Λ ^ (p - 2) := by
        have := Real.rpow_nonneg hY0.le (-(2 : ℝ) - j)
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ Λ by linarith) (p - 2)
        positivity
      have key : ‖iteratedDeriv j (c03_mult_R2tilde p Y a Ψ) y‖ ≤
          ‖iteratedDeriv j (c03_mult_R p Y a Ψ 2) y‖ +
          ‖iteratedDeriv j (fun y' => ((p * (p - 1) / 2 * deriv Ψ y' ^ (p - 2) : ℝ) : ℂ) *
            deriv (deriv a) y') y‖ := by
        interval_cases j
        · simp only [iteratedDeriv_zero]; unfold c03_mult_R2tilde; exact norm_sub_le _ _
        · simp only [iteratedDeriv_one]
          exact c03m_aux_norm_deriv_sub (c03m_aux_g_diff p Y a Ψ hyp.1 hyp.2.2.1
            (c03m_aux_lam_pos hc₀ hΛ hyp) y hy')
      refine key.trans ?_
      have := add_le_add b1 b2
      nlinarith
  · obtain ⟨k₀, hk⟩ := c03_mult_remainder_all_orders p hp hp1 c₀ hc₀ N hN j
    refine ⟨k₀, fun Ck => ?_⟩
    obtain ⟨C, hC, -, h2⟩ := hk Ck
    exact ⟨C, hC, h2⟩

end GSQG
