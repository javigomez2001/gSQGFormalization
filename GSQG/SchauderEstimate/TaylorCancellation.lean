import GSQG.SchauderEstimate.Kernels

/-!
# Beyond the paper (Schauder estimate cited in §4): Hölder Taylor remainder and the block
derivative bound (blueprint ch. 12). Helpers `c12t_aux_*`.

Convolution convention: `(K * h)(x) = ∫ z, K z * h (x - z)`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

theorem c12t_aux_iDW_Icc_eq {f : ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ k f) {a b : ℝ} (hab : a < b)
    {i : ℕ} (hi : i ≤ k) {t : ℝ} (ht : t ∈ Icc a b) :
    iteratedDerivWithin i f (Icc a b) t = iteratedDeriv i f t :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
    ((hf.of_le (by exact_mod_cast hi)).contDiffAt) ht

/-- Blueprint: lem:c12_holder_taylor.  For noninteger `β = k + θ > 0` (`k = ⌊β⌋`) there is `C_β`
with `|h(x-z) - ∑_{r ≤ k} h^{(r)}(x)(-z)^r/r!| ≤ C_β ‖h‖_{C^β(ℝ)} |z|^β` for all `h ∈ C^β(ℝ)` and
all `x z`. -/
theorem c12_holder_taylor (β : ℝ) (hβ : 0 < β) (hβN : ∀ n : ℕ, β ≠ n) :
    ∃ C, 0 < C ∧ ∀ h : ℝ → ℝ, h ∈ c03_holder β univ → ∀ x z : ℝ,
      |h (x - z) - ∑ r ∈ Finset.range (⌊β⌋₊ + 1),
          iteratedDeriv r h x * (-z) ^ r / (Nat.factorial r : ℝ)| ≤
        C * c03_holder_normR β univ h * |z| ^ β := by
  refine ⟨1, one_pos, fun h hh x z => ?_⟩
  set k := ⌊β⌋₊ with hkdef
  have hcd : ContDiff ℝ k h := contDiffOn_univ.1 hh.1
  have hS := c03_aux_semi_holder hh
  rw [iteratedDerivWithin_univ] at hS
  change HolderOnWith _ (Real.toNNReal (β - k)) (iteratedDeriv k h) univ at hS
  have hSle := c03_aux_semi_le_normR hh
  set S := (c03_aux_semi β univ h).toNNReal with hSdef
  have hSR : (S : ℝ) = (c03_aux_semi β univ h).toReal := rfl
  have hθ : ((Real.toNNReal (β - k) : ℝ≥0) : ℝ) = β - k :=
    Real.coe_toNNReal _ (by have := Nat.floor_le hβ.le; linarith)
  suffices H : |h (x - z) - ∑ r ∈ Finset.range (k + 1),
          iteratedDeriv r h x * (-z) ^ r / (Nat.factorial r : ℝ)| ≤ S * |z| ^ β by
    refine H.trans ?_
    rw [one_mul, hSR]
    gcongr
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk] at hS hθ ⊢
    have := hS.dist_le (mem_univ (x - z)) (mem_univ x)
    simp only [iteratedDeriv_zero, Real.dist_eq, sub_sub_cancel_left, abs_neg] at this
    rw [hθ, Nat.cast_zero, sub_zero] at this
    simpa using this
  · set a := x - |z| - 1
    set b := x + |z| + 1
    have hab : a < b := by simp only [a, b]; linarith [abs_nonneg z]
    have hx : x ∈ Icc a b := ⟨by simp only [a]; linarith [abs_nonneg z], by simp only [b]; linarith [abs_nonneg z]⟩
    have hy : x - z ∈ Icc a b := ⟨by simp only [a]; linarith [le_abs_self z], by simp only [b]; linarith [neg_abs_le z]⟩
    have hS' : HolderOnWith S (Real.toNNReal (β - k)) (iteratedDerivWithin k h (Icc a b)) (Icc a b) := by
      intro s hs t ht
      rw [c12t_aux_iDW_Icc_eq hcd hab le_rfl hs, c12t_aux_iDW_Icc_eq hcd hab le_rfl ht]
      exact hS s (mem_univ s) t (mem_univ t)
    have hT := c03_aux_taylor_holder k hk (Real.toNNReal (β - k)) a b hab h hcd.contDiffOn S hS' x (x - z) hx hy
    rw [hθ] at hT
    have hsum : ∑ i ∈ Finset.range (k + 1),
        ((Nat.factorial i : ℝ)⁻¹ * (x - z - x) ^ i) • iteratedDerivWithin i h (Icc a b) x =
        ∑ r ∈ Finset.range (k + 1), iteratedDeriv r h x * (-z) ^ r / (Nat.factorial r : ℝ) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [c12t_aux_iDW_Icc_eq hcd hab (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hx, smul_eq_mul]
      ring
    rw [hsum, Real.norm_eq_abs] at hT
    simpa [show (k : ℝ) + (β - k) = β by ring, abs_neg] using hT

/-- `(K * h)(x) = ∫ K(x-y) h(y) dy`. -/
theorem c12t_aux_conv_swap (K h : ℝ → ℝ) (x : ℝ) :
    ∫ z, K z * h (x - z) = ∫ y, K (x - y) * h y := by
  rw [← integral_sub_left_eq_self (fun y => K (x - y) * h y) volume x]
  simp only [sub_sub_cancel]

/-- `K * h` is continuous for integrable `K` and bounded continuous `h`. -/
theorem c12t_aux_conv_continuous {K h : ℝ → ℝ} (hKi : Integrable K) (hc : Continuous h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) : Continuous (fun x => ∫ z, K z * h (x - z)) := by
  refine continuous_of_dominated (bound := fun z => |K z| * M) (fun x => ?_) (fun x => ?_)
    (hKi.abs.mul_const M) (Eventually.of_forall fun z => ?_)
  · exact hKi.aestronglyMeasurable.mul (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  · exact continuous_const.mul (hc.comp (continuous_id.sub continuous_const))

theorem c12t_aux_conv_integrable {K h : ℝ → ℝ} (hKi : Integrable K) (hc : Continuous h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x : ℝ) : Integrable (fun z => K z * h (x - z)) :=
  hKi.mul_bdd (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM _)

/-- Differentiation of `K * h` through the kernel. -/
theorem c12t_aux_conv_hasDerivAt {K h : ℝ → ℝ} (hK : ContDiff ℝ 1 K) (hKi : Integrable K)
    (hK'i : Integrable (deriv K)) (hc : Continuous h) {M : ℝ} (hM : ∀ y, |h y| ≤ M) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ z, K z * h (x - z)) (∫ z, deriv K z * h (x₀ - z)) x₀ := by
  set G : ℝ → ℝ := fun t => ∫ z, deriv K z * h (t - z)
  have hGc : Continuous G := c12t_aux_conv_continuous hK'i hc hM
  have hKd : ∀ t, HasDerivAt K (deriv K t) t := fun t =>
    (hK.differentiable one_ne_zero t).hasDerivAt
  have hK'c : Continuous (deriv K) := hK.continuous_deriv le_rfl
  have hmeas : ∀ x : ℝ, AEStronglyMeasurable (fun y => K (x - y)) volume := fun x =>
    (hK.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : ∀ x, Integrable (fun y => K (x - y) * h y) := fun x =>
    (hKi.comp_sub_left x).mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM _)
  have key : ∀ x, (∫ z, K z * h (x - z)) = (∫ z, K z * h (x₀ - z)) + ∫ t in x₀..x, G t := by
    intro x
    rw [c12t_aux_conv_swap, c12t_aux_conv_swap, ← sub_eq_iff_eq_add', ← integral_sub (hint x) (hint x₀)]
    have hFTC : ∀ y, K (x - y) - K (x₀ - y) = ∫ t in x₀..x, deriv K (t - y) := by
      intro y
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => K (t - y))]
      · intro t _
        exact (hKd (t - y)).comp_sub_const t y
      · exact (hK'c.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
    simp_rw [← sub_mul, hFTC, ← intervalIntegral.integral_mul_const]
    have hGswap : ∀ t, G t = ∫ y, deriv K (t - y) * h y := fun t => c12t_aux_conv_swap _ _ t
    simp_rw [hGswap]
    symm
    apply intervalIntegral_integral_swap
    -- integrability on the product
    have hjm : AEStronglyMeasurable (Function.uncurry fun t y => deriv K (t - y) * h y)
        ((volume.restrict (uIoc x₀ x)).prod volume) :=
      ((hK'c.comp (continuous_fst.sub continuous_snd)).mul (hc.comp continuous_snd)).aestronglyMeasurable
    rw [integrable_prod_iff hjm]
    refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · exact (hK'i.comp_sub_left t).mul_bdd hc.aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM _)
    · refine Integrable.mono' (g := fun _ => M * ∫ z, |deriv K z|) ?_ hjm.norm.integral_prod_right' ?_
      · have : IsFiniteMeasure (volume.restrict (uIoc x₀ x)) := ⟨by rw [Measure.restrict_apply_univ, uIoc]; exact measure_Ioc_lt_top⟩
        exact integrable_const _
      · refine Eventually.of_forall fun t => ?_
        simp only [Function.uncurry_apply_pair, norm_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (integral_nonneg fun _ => by positivity)]
        calc ∫ y, |deriv K (t - y)| * |h y| ≤ ∫ y, M * |deriv K (t - y)| := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
                ((hK'i.comp_sub_left t).abs.const_mul M) (Eventually.of_forall fun y => ?_)
              simp only; rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)
          _ = M * ∫ z, |deriv K z| := by
              rw [integral_const_mul, integral_sub_left_eq_self (fun z => |deriv K z|) volume t]
  have hfun : (fun x => ∫ z, K z * h (x - z)) = fun x => (∫ z, K z * h (x₀ - z)) + ∫ t in x₀..x, G t :=
    funext key
  rw [hfun]
  exact ((hGc.integral_hasStrictDerivAt x₀ x₀).hasDerivAt.const_add _)

theorem c12t_aux_conv_iteratedDeriv {K h : ℝ → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hKi : ∀ n, Integrable (iteratedDeriv n K)) (hc : Continuous h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (n : ℕ) :
    iteratedDeriv n (fun x => ∫ z, K z * h (x - z)) =
      fun x => ∫ z, iteratedDeriv n K z * h (x - z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hKn : ContDiff ℝ 1 (iteratedDeriv n K) := by
      rw [iteratedDeriv_eq_iterate]
      exact (ContDiff.iterate_deriv n (hK.of_le (by simp))).of_le (by simp)
    have hd := c12t_aux_conv_hasDerivAt hKn (hKi n)
      (by rw [← iteratedDeriv_succ]; exact hKi (n + 1)) hc hM x
    rw [hd.deriv, ← iteratedDeriv_succ]

theorem c12t_aux_conv_contDiff {K h : ℝ → ℝ} (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hKi : ∀ n, Integrable (iteratedDeriv n K)) (hc : Continuous h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z, K z * h (x - z)) := by
  refine contDiff_of_differentiable_iteratedDeriv fun n _ => ?_
  rw [c12t_aux_conv_iteratedDeriv hK hKi hc hM n]
  intro x
  have hKn : ContDiff ℝ 1 (iteratedDeriv n K) := by
    rw [iteratedDeriv_eq_iterate]
    exact (ContDiff.iterate_deriv n (hK.of_le (by simp))).of_le (by simp)
  exact (c12t_aux_conv_hasDerivAt hKn (hKi n)
    (by rw [← iteratedDeriv_succ]; exact hKi (n + 1)) hc hM x).differentiableAt

/-- Blueprint: lem:c12_block_derivative_bound.  For `0 < p < 1`, noninteger `β > 0` and `m ∈ ℕ`
there is `C_{p,β,m}` such that for every `h ∈ C^β(ℝ)` and `j ∈ ℕ`: `K_{p,j} * h` is smooth, its
`m`-th derivative is the absolutely convergent convolution `K_{p,j}^{(m)} * h`, and
`‖∂^m (K_{p,j} * h)‖_∞ ≤ C 2^{(m-β-p)j} ‖h‖_{C^β(ℝ)}`. -/
theorem c12_block_derivative_bound (p β : ℝ) (hp : 0 < p) (hp1 : p < 1) (hβ : 0 < β)
    (hβN : ∀ n : ℕ, β ≠ n) (m : ℕ) :
    ∃ C, 0 < C ∧ ∀ h : ℝ → ℝ, h ∈ c03_holder β univ → ∀ j : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z, c12_scaled_kernel p j z * h (x - z)) ∧
      (∀ x, Integrable (fun z => iteratedDeriv m (c12_scaled_kernel p j) z * h (x - z))) ∧
      (∀ x, iteratedDeriv m (fun x => ∫ z, c12_scaled_kernel p j z * h (x - z)) x =
        ∫ z, iteratedDeriv m (c12_scaled_kernel p j) z * h (x - z)) ∧
      ∀ x, |iteratedDeriv m (fun x => ∫ z, c12_scaled_kernel p j z * h (x - z)) x| ≤
        C * (2 : ℝ) ^ (((m : ℝ) - β - p) * (j : ℝ)) * c03_holder_normR β univ h := by
  obtain ⟨Ct, hCt0, hCt⟩ := c12_holder_taylor β hβ hβN
  set I := ∫ z, |z| ^ β * |iteratedDeriv m (c12_kernel p) z|
  have hI0 : 0 ≤ I := integral_nonneg fun _ => by positivity
  refine ⟨Ct * (I + 1), by positivity, fun h hh j => ?_⟩
  obtain ⟨hKs, -, -, hW, hMom⟩ := c12_kernel_scaling p hp hp1 j
  set Kj := c12_scaled_kernel p j
  have hKi : ∀ n, Integrable (iteratedDeriv n Kj) := by
    intro n
    have h0 := (hW n 0 le_rfl).1
    simp only [Real.rpow_zero, one_mul] at h0
    exact (integrable_norm_iff
      (hKs.continuous_iteratedDeriv n (by exact_mod_cast le_top)).aestronglyMeasurable).1 h0
  set N := c03_holder_normR β univ h
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hM : ∀ y, |h y| ≤ N := by
    intro y
    have := c03_aux_le_normR hh (i := 0) (Nat.zero_le _) (mem_univ y)
    simpa using this
  have hc : Continuous h := continuousOn_univ.1 hh.1.continuousOn
  have hD := c12t_aux_conv_iteratedDeriv hKs hKi hc hM m
  refine ⟨c12t_aux_conv_contDiff hKs hKi hc hM, fun x => c12t_aux_conv_integrable (hKi m) hc hM x,
    fun x => by rw [hD], fun x => ?_⟩
  rw [hD]
  set Km := iteratedDeriv m Kj
  set P : ℝ → ℝ := fun z => ∑ r ∈ Finset.range (⌊β⌋₊ + 1),
    iteratedDeriv r h x * (-z) ^ r / (Nat.factorial r : ℝ)
  have hPe : ∀ z, Km z * P z = ∑ r ∈ Finset.range (⌊β⌋₊ + 1),
      (iteratedDeriv r h x * (-1) ^ r / (Nat.factorial r : ℝ)) * (z ^ r * Km z) := by
    intro z
    simp only [P, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [neg_pow z r]
    ring
  have hPi : Integrable (fun z => Km z * P z) := by
    simp_rw [hPe]
    exact integrable_finsetSum _ fun r _ => (hMom r m).1.const_mul _
  have hP0 : ∫ z, Km z * P z = 0 := by
    simp_rw [hPe]
    rw [integral_finsetSum _ fun r _ => (hMom r m).1.const_mul _]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [integral_const_mul, (hMom r m).2, mul_zero]
  have hhi := c12t_aux_conv_integrable (hKi m) hc hM x
  have hsplit : ∫ z, Km z * h (x - z) = ∫ z, Km z * (h (x - z) - P z) := by
    simp_rw [mul_sub]
    rw [integral_sub hhi hPi, hP0, sub_zero]
  show |∫ z, Km z * h (x - z)| ≤ _
  rw [hsplit]
  have hb : ∀ z, ‖Km z * (h (x - z) - P z)‖ ≤ Ct * N * (|z| ^ β * |Km z|) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul]
    calc |Km z| * |h (x - z) - P z| ≤ |Km z| * (Ct * N * |z| ^ β) :=
          mul_le_mul_of_nonneg_left (hCt h hh x z) (abs_nonneg _)
      _ = _ := by ring
  have hle := norm_integral_le_of_norm_le ((hW m β hβ.le).1.const_mul (Ct * N))
    (Eventually.of_forall hb)
  rw [Real.norm_eq_abs, integral_const_mul, (hW m β hβ.le).2] at hle
  refine hle.trans ?_
  rw [show (m : ℝ) - p - β = m - β - p by ring]
  have h2 : 0 ≤ (2 : ℝ) ^ (((m : ℝ) - β - p) * (j : ℝ)) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hCt0.le hN0) h2]

end GSQG
