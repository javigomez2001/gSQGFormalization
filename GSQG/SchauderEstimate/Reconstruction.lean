import GSQG.SchauderEstimate.FourierFactorization
import GSQG.SchauderEstimate.TaylorCancellation
import GSQG.SchauderEstimate.DyadicIncrements

/-!
# Beyond the paper (Schauder estimate cited in §4): the compact-input Schauder estimate
(blueprint ch. 12). Helpers `c12r_aux_*`.

Blueprint `12_schauder.tex`, lem:c12_compact_schauder. The abstract dyadic assembly
`c12r_aux_assembly` (fully proved) reconstructs the global `C^s` norm from a low block and dyadic
blocks with derivative bounds through order `⌊s⌋ + 1`; the top order is used only for increments
(mean value bound on each block), never summed as a series.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-- `θ := s - ⌊s⌋` lies in `(0,1)` for noninteger `s > 0`. -/
theorem c12r_aux_theta (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) :
    0 < s - ⌊s⌋₊ ∧ s - ⌊s⌋₊ < 1 := by
  refine ⟨?_, by linarith [Nat.lt_floor_add_one s]⟩
  have h1 : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs.le
  have h2 : (⌊s⌋₊ : ℝ) ≠ s := fun h => hsN _ h.symm
  exact sub_pos.2 (lt_of_le_of_ne h1 h2)

/-- `∑_{j<n} 2^{-θ j} ≤ (1 - 2^{-θ})⁻¹`. -/
theorem c12r_aux_geom (θ : ℝ) (hθ : 0 < θ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (2 : ℝ) ^ (-θ * j) ≤ (1 - (2 : ℝ) ^ (-θ))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-θ) := by positivity
  have hr1 : (2 : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have heq : ∀ j : ℕ, (2 : ℝ) ^ (-θ * j) = ((2 : ℝ) ^ (-θ)) ^ j := fun j => by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  simp_rw [heq]
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1
  rw [Finset.range_eq_Ico]; refine this.trans (le_of_eq ?_); rw [pow_zero, one_div]

/-- Mean value bound for an increment of `iteratedDeriv k f`. -/
theorem c12r_aux_mvt (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (M : ℝ)
    (hM : ∀ x, |iteratedDeriv (k + 1) f x| ≤ M) (x y : ℝ) :
    |iteratedDeriv k f x - iteratedDeriv k f y| ≤ M * |x - y| := by
  have hd : Differentiable ℝ (iteratedDeriv k f) :=
    hf.differentiable_iteratedDeriv k (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top k))
  have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := iteratedDeriv k f) (C := M) (fun z _ => hd z)
    (fun z _ => by rw [Real.norm_eq_abs, ← iteratedDeriv_succ]; exact hM z) (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- `2^{(m-s)j} ≤ 2^{-θ j}` for `m ≤ ⌊s⌋`. -/
theorem c12r_aux_pow_le (s : ℝ) (m j : ℕ) (hm : m ≤ ⌊s⌋₊) :
    (2 : ℝ) ^ (((m : ℝ) - s) * j) ≤ (2 : ℝ) ^ (-(s - ⌊s⌋₊) * j) := by
  have : (m : ℝ) ≤ ⌊s⌋₊ := by exact_mod_cast hm
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg j))

/-- `min(2a, b d) ≤ (2a + b) d^θ` for `a,b ≥ 0`, `d ≥ 0`, `0 < θ ≤ 1`. -/
theorem c12r_aux_min_le (a b d θ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) : min (2 * a) (b * d) ≤ (2 * a + b) * d ^ θ := by
  rcases le_total d 1 with h | h
  · have h1 : d ≤ d ^ θ := Real.self_le_rpow_of_le_one hd h hθ1
    have h2 : 0 ≤ d ^ θ := Real.rpow_nonneg hd θ
    calc min (2 * a) (b * d) ≤ b * d := min_le_right _ _
      _ ≤ b * d ^ θ := mul_le_mul_of_nonneg_left h1 hb
      _ ≤ (2 * a + b) * d ^ θ := by nlinarith
  · have h1 : 1 ≤ d ^ θ := Real.one_le_rpow h hθ.le
    calc min (2 * a) (b * d) ≤ 2 * a := min_le_left _ _
      _ ≤ 2 * a * d ^ θ := by nlinarith
      _ ≤ (2 * a + b) * d ^ θ := by nlinarith

/-- Abstract dyadic assembly of the global `C^s` norm from a low block `L` and blocks `B j`. -/
theorem c12r_aux_assembly (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) (A : ℕ → ℝ)
    (hA : ∀ m, 0 ≤ A m) (Cθ : ℝ) (hCθ : 0 ≤ Cθ)
    (hinc : ∀ d : ℝ, 0 ≤ d → ∀ n : ℕ, ∑ j ∈ Finset.range n,
        min ((2 : ℝ) ^ (-(s - ⌊s⌋₊) * j)) (d * (2 : ℝ) ^ ((1 - (s - ⌊s⌋₊)) * j)) ≤
          Cθ * d ^ (s - ⌊s⌋₊)) :
    ∃ C, 0 < C ∧ ∀ (v L : ℝ → ℝ) (B : ℕ → ℝ → ℝ) (N H : ℝ), 0 ≤ N → 0 ≤ H →
      ContDiff ℝ (⊤ : ℕ∞) v → ContDiff ℝ (⊤ : ℕ∞) L → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (B j)) →
      (∀ m ≤ ⌊s⌋₊ + 1, ∀ x, |iteratedDeriv m L x| ≤ A m * N) →
      (∀ m ≤ ⌊s⌋₊ + 1, ∀ (j : ℕ) x,
        |iteratedDeriv m (B j) x| ≤ A m * (2 : ℝ) ^ (((m : ℝ) - s) * j) * H) →
      (∀ m ≤ ⌊s⌋₊, ∀ x, Tendsto (fun n => iteratedDeriv m L x +
        ∑ j ∈ Finset.range n, iteratedDeriv m (B j) x) atTop (𝓝 (iteratedDeriv m v x))) →
      v ∈ c03_holder s univ ∧ c03_holder_normR s univ v ≤ C * (N + H) := by
  set k := ⌊s⌋₊ with hk
  set θ := s - (k : ℝ) with hθdef
  obtain ⟨hθ0, hθ1⟩ := c12r_aux_theta s hs hsN
  set G := (1 - (2 : ℝ) ^ (-θ))⁻¹ with hG
  have hG0 : 0 ≤ G := by
    have : (2 : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact inv_nonneg.2 (by linarith)
  set M := (2 * A k + A (k + 1)) * (1 + Cθ) with hMdef
  refine ⟨∑ i ∈ Finset.range (k + 1), A i * (1 + G) + M + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ i ∈ Finset.range (k + 1), A i * (1 + G) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (by linarith)
    have : 0 ≤ M := mul_nonneg (by linarith [hA k, hA (k + 1)]) (by linarith)
    linarith
  intro v L B N H hN hH hv hL hB hLb hBb hconv
  -- sup bounds
  have hsup : ∀ m ≤ k, ∀ x, |iteratedDeriv m v x| ≤ A m * N + A m * H * G := by
    intro m hm x
    refine le_of_tendsto' ((continuous_abs.tendsto _).comp (hconv m hm x)) fun n => ?_
    simp only [Function.comp]
    calc |iteratedDeriv m L x + ∑ j ∈ Finset.range n, iteratedDeriv m (B j) x|
        ≤ |iteratedDeriv m L x| + ∑ j ∈ Finset.range n, |iteratedDeriv m (B j) x| :=
          (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ A m * N + ∑ j ∈ Finset.range n, A m * H * (2 : ℝ) ^ (-θ * j) := by
          refine add_le_add (hLb m (by omega) x) (Finset.sum_le_sum fun j _ => ?_)
          refine (hBb m (by omega) j x).trans ?_
          have := c12r_aux_pow_le s m j hm
          have h2 := mul_le_mul_of_nonneg_left this (hA m)
          nlinarith [mul_le_mul_of_nonneg_right h2 hH]
      _ ≤ A m * N + A m * H * G := by
          rw [← Finset.mul_sum]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (c12r_aux_geom θ hθ0 n)
            (mul_nonneg (hA m) hH))
  -- Hölder bound of the k-th derivative
  have hhol : ∀ x y, |iteratedDeriv k v x - iteratedDeriv k v y| ≤ M * (N + H) * |x - y| ^ θ := by
    intro x y
    set d := |x - y|
    have hd : 0 ≤ d := abs_nonneg _
    have hdθ : 0 ≤ d ^ θ := Real.rpow_nonneg hd θ
    have hlim := ((hconv k le_rfl x).sub (hconv k le_rfl y))
    refine le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) fun n => ?_
    simp only [Function.comp]
    have hLinc : |iteratedDeriv k L x - iteratedDeriv k L y| ≤ (2 * A k + A (k + 1)) * N * d ^ θ := by
      have h1 : |iteratedDeriv k L x - iteratedDeriv k L y| ≤ 2 * (A k * N) :=
        (abs_sub _ _).trans (by linarith [hLb k (by omega) x, hLb k (by omega) y])
      have h2 : |iteratedDeriv k L x - iteratedDeriv k L y| ≤ (A (k + 1) * N) * d :=
        c12r_aux_mvt L hL k _ (hLb (k + 1) le_rfl) x y
      have := c12r_aux_min_le (A k * N) (A (k + 1) * N) d θ (mul_nonneg (hA k) hN)
        (mul_nonneg (hA (k + 1)) hN) hd hθ0 hθ1.le
      calc _ ≤ min (2 * (A k * N)) (A (k + 1) * N * d) := le_min h1 h2
        _ ≤ _ := this
        _ = _ := by ring
    have hBinc : ∀ j : ℕ, |iteratedDeriv k (B j) x - iteratedDeriv k (B j) y| ≤
        (2 * A k + A (k + 1)) * H *
          min ((2 : ℝ) ^ (-θ * j)) (d * (2 : ℝ) ^ ((1 - θ) * j)) := by
      intro j
      have e1 : (2 : ℝ) ^ (((k : ℝ) - s) * j) = (2 : ℝ) ^ (-θ * j) := by
        congr 1; rw [hθdef]; ring
      have e2 : (2 : ℝ) ^ ((((k + 1 : ℕ) : ℝ) - s) * j) = (2 : ℝ) ^ ((1 - θ) * j) := by
        congr 1; rw [hθdef]; push_cast; ring
      have hb1 := hBb k (by omega) j x
      have hb2 := hBb k (by omega) j y
      rw [e1] at hb1 hb2
      have h1 : |iteratedDeriv k (B j) x - iteratedDeriv k (B j) y| ≤
          2 * (A k * H) * (2 : ℝ) ^ (-θ * j) :=
        (abs_sub _ _).trans (by linarith)
      have h2 : |iteratedDeriv k (B j) x - iteratedDeriv k (B j) y| ≤
          A (k + 1) * H * (d * (2 : ℝ) ^ ((1 - θ) * j)) := by
        have := c12r_aux_mvt (B j) (hB j) k (A (k + 1) * (2 : ℝ) ^ ((1 - θ) * j) * H)
          (fun z => by have := hBb (k + 1) le_rfl j z; rwa [e2] at this) x y
        calc _ ≤ _ := this
          _ = _ := by ring
      have hP : 0 ≤ (2 : ℝ) ^ (-θ * j) := by positivity
      have hQ : 0 ≤ d * (2 : ℝ) ^ ((1 - θ) * j) := mul_nonneg hd (by positivity)
      have hAk := hA k; have hAk1 := hA (k + 1)
      rcases le_total ((2 : ℝ) ^ (-θ * j)) (d * (2 : ℝ) ^ ((1 - θ) * j)) with hc | hc
      · rw [min_eq_left hc]
        have : 0 ≤ A (k + 1) * H * (2 : ℝ) ^ (-θ * j) := by positivity
        nlinarith
      · rw [min_eq_right hc]
        have : 0 ≤ 2 * A k * H * (d * (2 : ℝ) ^ ((1 - θ) * j)) := by positivity
        nlinarith
    have hsum := hinc d hd n
    calc |(iteratedDeriv k L x + ∑ j ∈ Finset.range n, iteratedDeriv k (B j) x) -
          (iteratedDeriv k L y + ∑ j ∈ Finset.range n, iteratedDeriv k (B j) y)|
        = |(iteratedDeriv k L x - iteratedDeriv k L y) +
            ∑ j ∈ Finset.range n, (iteratedDeriv k (B j) x - iteratedDeriv k (B j) y)| := by
          rw [Finset.sum_sub_distrib]; ring_nf
      _ ≤ |iteratedDeriv k L x - iteratedDeriv k L y| +
            ∑ j ∈ Finset.range n, |iteratedDeriv k (B j) x - iteratedDeriv k (B j) y| :=
          (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ (2 * A k + A (k + 1)) * N * d ^ θ + (2 * A k + A (k + 1)) * H *
            ∑ j ∈ Finset.range n, min ((2 : ℝ) ^ (-θ * j)) (d * (2 : ℝ) ^ ((1 - θ) * j)) := by
          rw [Finset.mul_sum]; exact add_le_add hLinc (Finset.sum_le_sum fun j _ => hBinc j)
      _ ≤ (2 * A k + A (k + 1)) * N * d ^ θ + (2 * A k + A (k + 1)) * H * (Cθ * d ^ θ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (by linarith [hA k, hA (k + 1)]) hH))
      _ ≤ M * (N + H) * d ^ θ := by
          have hK : 0 ≤ 2 * A k + A (k + 1) := by linarith [hA k, hA (k + 1)]
          have : 0 ≤ (2 * A k + A (k + 1)) * N * Cθ * d ^ θ := by positivity
          have : 0 ≤ (2 * A k + A (k + 1)) * H * d ^ θ := by positivity
          rw [hMdef]; nlinarith
  -- assemble the norm
  have hcd : ContDiffOn ℝ k v univ := (hv.of_le (by exact_mod_cast le_top)).contDiffOn
  have hMN : 0 ≤ M * (N + H) :=
    mul_nonneg (mul_nonneg (by linarith [hA k, hA (k + 1)]) (by linarith)) (by linarith)
  have hHol : HolderOnWith (M * (N + H)).toNNReal (Real.toNNReal (s - k))
      (iteratedDerivWithin k v univ) univ := by
    refine c03_aux_holderOnWith_of_dist fun x _ y _ => ?_
    rw [iteratedDerivWithin_univ, Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hMN,
      Real.coe_toNNReal _ hθ0.le]
    exact hhol x y
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s univ v hcd (fun i => A i * N + A i * H * G)
    (fun i _ => by have := hA i; positivity)
    (fun i hi x _ => by rw [iteratedDerivWithin_univ, Real.norm_eq_abs]; exact hsup i hi x)
    _ hHol
  refine ⟨hmem, hle.trans ?_⟩
  rw [Real.coe_toNNReal _ hMN, ← hk, add_mul, add_mul, Finset.sum_mul, one_mul]
  have : ∀ i ∈ Finset.range (k + 1), A i * N + A i * H * G ≤ A i * (1 + G) * (N + H) := by
    intro i _
    have := hA i
    have : 0 ≤ A i * N * G := by positivity
    have : 0 ≤ A i * H := by positivity
    nlinarith
  have := Finset.sum_le_sum this
  have : 0 ≤ N + H := by linarith
  linarith


/-- The fixed cutoff `η` equals one on `[-1/2, 1/2]` (directly from its formula). -/
theorem c12r_aux_eta_one (x : ℝ) (hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2)) : c12_eta x = 1 := by
  unfold c12_eta
  apply Real.smoothTransition.one_of_one_le
  have : x ^ 2 ≤ 1 / 4 := by nlinarith [hx.1, hx.2]
  rw [le_div_iff₀ (by norm_num)]; nlinarith

/-- Blueprint: lem:c12_compact_schauder.  For `0 < p < 1`, noninteger `β > 0` with `β + p`
noninteger, there is `C_{p,β} > 0` such that every real `v ∈ C_c^∞(ℝ)` with
`h = |D|^p v ∈ C^β(ℝ)` lies in `C^{β+p}(ℝ)` and `N_{β+p}(v) ≤ C (‖v‖_∞ + N_β(h))`
(stated for every bound `M` of `|v|`). -/
theorem c12_compact_schauder (p β : ℝ) (hp : 0 < p) (hp1 : p < 1) (hβ : 0 < β)
    (hβN : ∀ n : ℕ, β ≠ n) (hβpN : ∀ n : ℕ, β + p ≠ n) :
    ∃ C, 0 < C ∧ ∀ v : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      fracD p v ∈ c03_holder β univ →
      v ∈ c03_holder (β + p) univ ∧
      ∀ M : ℝ, (∀ x, |v x| ≤ M) →
        c03_holder_normR (β + p) univ v ≤ C * (M + c03_holder_normR β univ (fracD p v)) := by
  have hs : 0 < β + p := by linarith
  obtain ⟨hθ0, hθ1⟩ := c12r_aux_theta (β + p) hs hβpN
  obtain ⟨Cθ, hCθ0, hinc⟩ := c12_dyadic_increment_sum.1 _ hθ0 hθ1
  choose Cb hCb0 hCb using fun m => c12_block_derivative_bound p β hp hp1 hβ hβN m
  choose Cl hCl0 hCl using c12_low_block_bound
  obtain ⟨C, hC0, hC⟩ := c12r_aux_assembly (β + p) hs hβpN (fun m => max (Cb m) (Cl m))
    (fun m => le_max_of_le_left (hCb0 m).le) Cθ hCθ0.le hinc
  refine ⟨C, hC0, fun v hv hvc hh => ?_⟩
  set h := fracD p v with hhdef
  have hH : 0 ≤ c03_holder_normR β univ h := c03_aux_normR_nonneg _ _ _
  have hBeq : ∀ j, c12_block j v = fun x => ∫ z, c12_scaled_kernel p j z * h (x - z) :=
    fun j => funext fun x => (c12_block_factorization hp hp1 hv hvc j x).2.2
  have hLsm : ContDiff ℝ (⊤ : ℕ∞) (c12_low_block v) := (hCl 0 v hv hvc).1
  have hBsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c12_block j v) := fun j => by
    rw [hBeq]; exact (hCb 0 h hh j).1
  have key : ∀ M : ℝ, (∀ x, |v x| ≤ M) → v ∈ c03_holder (β + p) univ ∧
      c03_holder_normR (β + p) univ v ≤ C * (M + c03_holder_normR β univ h) := by
    intro M hM
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    refine hC v (c12_low_block v) (fun j => c12_block j v) M _ hM0 hH hv hLsm hBsm
      (fun m _ x => ((hCl m v hv hvc).2.2 M hM x).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hM0))
      (fun m _ j x => ?_) (fun m _ x => ?_)
    · rw [hBeq]
      refine ((hCb m h hh j).2.2.2 x).trans ?_
      rw [sub_sub]
      · have : 0 ≤ (2 : ℝ) ^ (((m : ℝ) - (β + p)) * (j : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) this) hH
    · have ht := (c12_reconstruction_derivatives v hv hvc m).2.tendsto_at x
      refine ht.congr fun n => ?_
      have hca : ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → ContDiffAt ℝ m f x := fun f hf =>
        (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      rw [iteratedDeriv_fun_add (hca _ hLsm)
        (ContDiffAt.sum fun j _ => hca _ (hBsm j)), iteratedDeriv_fun_sum fun j _ => hca _ (hBsm j)]
  obtain ⟨M0, hM0⟩ := hv.continuous.bounded_above_of_compact_support hvc
  exact ⟨(key M0 fun x => by simpa [Real.norm_eq_abs] using hM0 x).1, fun M hM => (key M hM).2⟩

end GSQG
