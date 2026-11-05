import GSQG.Definitions
import GSQG.Sec5_ApproximateSolution.FamilyAndE1toE4

/-!
# §§5.9–5.12: control of `ℰ₆, ℰ₇, ℰ₈, ℰ₉` (blueprint ch. 06)

Statements and proofs of blueprint chapter `06_E6_E9.tex` (fully proved; no `sorry`).

Standing assumptions of the chapter.  The fixed parameters are `P : parameters` (`3/4 < p < 1`).
`ε₀ ∈ (0,1]` and `δ ∈ (0, |μ_*|/2]` are the constants of def:approximate_solution_family,
and `R ≥ R₀` is the cutoff scale of the family.  An *admissible constant* depends only on
`p, ε₀, δ, R` and the fixed cutoffs, so it is quantified as `∃ C` after `R` and before
`ε ∈ [0,ε₀]`, `μ ∈ B̄(μ_*,δ)`, `Y`, `y`.

Encoding of `R₀`: one `R₀ ≥ 1` is fixed, "so large that the estimates of
lem:approx_linear_seed, lem:approx_phase_differences, prop:approx_profile_bounds hold".
Each statement about the family here says `∃ R₀ ≥ 1, ∀ R ≥ R₀, ...` (so `R₀` may a priori
differ between statements; the final `R₀` is the maximum of the finitely many ones).

Smallness of `ε₀`: `δ ∈ (0, |μ_*|/2]` is arbitrary, and `ε₀ ∈ (0,1]` is small: the chapter 04
results used here (prop:approx_profile_bounds, lem:c04_family_regions, lem:c04_Z_bounds,
lem:c04_Z_primitive) hold for small `ε₀ ∈ (0,1]`, so every family statement of this chapter
carries the hypothesis `hε₀s : ε₀ ≤ c06_eps0_star P δ`, where `c06_eps0_star P δ` is the minimum
of those four thresholds (each chosen with `Classical.choose`). It is positive for
`0 < δ ≤ |μ_*|/2` (`c07_aux_eps0_pos`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ## Elementary helpers (not blueprint nodes) -/

/-- Helper: `⟨y⟩ ≥ 1`. -/
theorem c06_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := by
  unfold jb
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + y ^ 2 by nlinarith [sq_nonneg y])
  simpa using this

/-- Helper: `⟨y⟩ > 0`. -/
theorem c06_aux_jb_pos (y : ℝ) : 0 < jb y := lt_of_lt_of_le one_pos (c06_aux_one_le_jb y)

/-- Helper: `2β = 1 + 1/p`. -/
theorem c06_aux_two_beta (p : ℝ) (hp : 0 < p) : 2 * beta p = 1 + 1 / p := by
  unfold beta; field_simp

/-- Helper: for `1 ≤ Y ≤ y ≤ 2Y` and `b ≥ 0`, `Y^{-b} ≤ 3^b ⟨y⟩^{-b}`. -/
theorem c06_aux_Y_le_jb (b Y y : ℝ) (hb : 0 ≤ b) (hY : 1 ≤ Y) (hy1 : Y ≤ y) (hy2 : y ≤ 2 * Y) :
    Y ^ (-b) ≤ (3 : ℝ) ^ b * jb y ^ (-b) := by
  have hY0 : 0 < Y := by linarith
  have hjb : jb y ≤ 3 * Y := by
    unfold jb
    rw [show 3 * Y = Real.sqrt ((3 * Y) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h1 : (3 * Y) ^ (-b) ≤ jb y ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (c06_aux_jb_pos y) hjb (by linarith)
  rw [Real.mul_rpow (by norm_num) hY0.le] at h1
  have h3 : (3 : ℝ) ^ b * (3 : ℝ) ^ (-b) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  calc Y ^ (-b) = (3 : ℝ) ^ b * ((3 : ℝ) ^ (-b) * Y ^ (-b)) := by
        rw [← mul_assoc, h3, one_mul]
    _ ≤ (3 : ℝ) ^ b * jb y ^ (-b) := by
        gcongr

/-- Helper: conversion `K ε Y^{-b} ≤ 3^B K ε ⟨y⟩^{-b}` for `0 ≤ b ≤ B`, `1 ≤ Y ≤ y ≤ 2Y`. -/
theorem c06_aux_conv (K ε b B Y y X : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hb : 0 ≤ b) (hbB : b ≤ B)
    (hY : 1 ≤ Y) (hy1 : Y ≤ y) (hy2 : y ≤ 2 * Y) (hX : X ≤ K * ε * Y ^ (-b)) :
    X ≤ (3 : ℝ) ^ B * K * ε * jb y ^ (-b) := by
  have hc := c06_aux_Y_le_jb b Y y hb hY hy1 hy2
  have h3 : (3 : ℝ) ^ b ≤ (3 : ℝ) ^ B := Real.rpow_le_rpow_of_exponent_le (by norm_num) hbB
  have hj0 := Real.rpow_nonneg (c06_aux_jb_pos y).le (-b)
  have hKε : 0 ≤ K * ε := mul_nonneg hK hε
  calc X ≤ K * ε * Y ^ (-b) := hX
    _ ≤ K * ε * ((3 : ℝ) ^ b * jb y ^ (-b)) := by gcongr
    _ ≤ K * ε * ((3 : ℝ) ^ B * jb y ^ (-b)) := by gcongr
    _ = (3 : ℝ) ^ B * K * ε * jb y ^ (-b) := by ring

/-- Helper: mean value inequality `|w a - w b| ≤ M |a - b|` from `|w'| ≤ M`. -/
theorem c06_aux_lip (w : ℝ → ℝ) (hw : Differentiable ℝ w) (M : ℝ) (hM : ∀ x, |deriv w x| ≤ M)
    (a b : ℝ) : |w a - w b| ≤ M * |a - b| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := w) (x := b) (y := a)
    (fun x _ => hw x) (fun x _ => by simpa [Real.norm_eq_abs] using hM x) convex_univ
    (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using this

/-- Helper: secant bound on the segment, `|S_w(y,z)| ≤ sup_{[y,z]} |w'|`. -/
theorem c06_aux_secant_le_seg (w : ℝ → ℝ) (hw : Differentiable ℝ w) (y z : ℝ) (hyz : y ≠ z)
    (M : ℝ) (hM : ∀ x ∈ uIcc y z, |deriv w x| ≤ M) : |c01_secant w y z| ≤ M := by
  unfold c01_secant
  simp only [hyz, ite_false]
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := uIcc y z) (f := w) (x := z) (y := y)
    (fun x _ => hw x) (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx) (convex_uIcc y z)
    right_mem_uIcc left_mem_uIcc
  simp only [Real.norm_eq_abs] at this
  have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr hyz)
  rw [abs_div, div_le_iff₀ hpos]
  exact this

/-- Helper: global secant bound `|S_w(y,z)| ≤ M` from `|w'| ≤ M`. -/
theorem c06_aux_secant_le (w : ℝ → ℝ) (hw : Differentiable ℝ w) (M : ℝ)
    (hM : ∀ x, |deriv w x| ≤ M) (y z : ℝ) : |c01_secant w y z| ≤ M := by
  by_cases hyz : y = z
  · unfold c01_secant; simp only [hyz, ite_true]; exact hM z
  · exact c06_aux_secant_le_seg w hw y z hyz M (fun x _ => hM x)

/-- Helper: `(C Y^a)^{1-p} (C Y^b)^p = C Y^{a(1-p)+bp}`. -/
theorem c06_aux_interp (C Y a b p : ℝ) (hC : 0 < C) (hY : 0 < Y) :
    (C * Y ^ a) ^ (1 - p) * (C * Y ^ b) ^ p = C * Y ^ (a * (1 - p) + b * p) := by
  rw [Real.mul_rpow hC.le (Real.rpow_nonneg hY.le _), Real.mul_rpow hC.le (Real.rpow_nonneg hY.le _),
    ← Real.rpow_mul hY.le, ← Real.rpow_mul hY.le, Real.rpow_add hY]
  have : C ^ (1 - p) * C ^ p = C := by
    rw [← Real.rpow_add hC]; simp
  calc C ^ (1 - p) * Y ^ (a * (1 - p)) * (C ^ p * Y ^ (b * p))
      = (C ^ (1 - p) * C ^ p) * (Y ^ (a * (1 - p)) * Y ^ (b * p)) := by ring
    _ = _ := by rw [this]

/-! ## Standing conventions and elementary tools -/

/-- Helper (Bernoulli-type bound): `0 ≤ 1 - (1+σ)^{-b} ≤ bσ` for `b > 0`, `σ ≥ 0`. -/
theorem c06_aux_bern (b σ : ℝ) (hb : 0 < b) (hσ : 0 ≤ σ) :
    0 ≤ 1 - (1 + σ) ^ (-b) ∧ 1 - (1 + σ) ^ (-b) ≤ b * σ := by
  constructor
  · have := Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1 : ℝ) ≤ 1 + σ)
      (by linarith : -b ≤ 0)
    linarith
  · have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => (1 + x) ^ (-b))
        (1 * (-b) * (1 + x) ^ (-b - 1)) x := fun x hx =>
      ((hasDerivAt_id x).const_add 1).rpow_const (Or.inl (by simp at hx ⊢; linarith))
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Ici (0 : ℝ))
      (f := fun x => (1 + x) ^ (-b)) (x := 0) (y := σ) (C := b)
      (fun x hx => (hd x hx).differentiableAt)
      (fun x hx => by
        rw [(hd x hx).deriv, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (by simp at hx; linarith) _)]
        simp only [abs_one, one_mul, abs_neg, abs_of_pos hb]
        have : (1 + x) ^ (-b - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by simp at hx; linarith) (by linarith)
        nlinarith)
      (convex_Ici 0) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hσ)
    simp only [add_zero, Real.one_rpow, Real.norm_eq_abs, sub_zero, abs_of_nonneg hσ] at this
    rw [abs_le] at this
    linarith [this.1]

/-- Helper (second-order bound): `|(1+σ)^{-a} - 1 + aσ| ≤ a(a+1)σ²` for `a > 0`, `σ ≥ 0`. -/
theorem c06_aux_taylor2 (a σ : ℝ) (ha : 0 < a) (hσ : 0 ≤ σ) :
    |(1 + σ) ^ (-a) - 1 + a * σ| ≤ a * (a + 1) * σ ^ 2 := by
  have hd : ∀ x ∈ Icc (0 : ℝ) σ, HasDerivAt (fun x => (1 + x) ^ (-a) - 1 + a * x)
      (1 * (-a) * (1 + x) ^ (-a - 1) + a * 1) x := fun x hx =>
    ((((hasDerivAt_id x).const_add 1).rpow_const (Or.inl (by simp only [id]; linarith [hx.1]))).sub_const 1).add
      ((hasDerivAt_id x).const_mul a)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc (0 : ℝ) σ)
    (f := fun x => (1 + x) ^ (-a) - 1 + a * x) (x := 0) (y := σ) (C := a * (a + 1) * σ)
    (fun x hx => (hd x hx).differentiableAt)
    (fun x hx => by
      rw [(hd x hx).deriv, Real.norm_eq_abs]
      have hb := c06_aux_bern (a + 1) x (by linarith) hx.1
      rw [show -a - 1 = -(a + 1) by ring]
      have e : 1 * -a * (1 + x) ^ (-(a + 1)) + a * 1 = a * (1 - (1 + x) ^ (-(a + 1))) := by ring
      rw [e, abs_mul, abs_of_pos ha, abs_of_nonneg hb.1]
      have : (a + 1) * x ≤ (a + 1) * σ := by nlinarith [hx.2]
      nlinarith)
    (convex_Icc 0 σ) ⟨le_rfl, hσ⟩ ⟨hσ, le_rfl⟩
  simp only [add_zero, Real.one_rpow, Real.norm_eq_abs, sub_zero, mul_zero, sub_self,
    abs_of_nonneg hσ] at this
  calc _ ≤ a * (a + 1) * σ * σ := this
    _ = a * (a + 1) * σ ^ 2 := by ring

/-- Helper: derivative of `u ↦ (1+εu²)^s`. -/
theorem c06_aux_hq (ε s u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (fun u => (1 + ε * u ^ 2) ^ s) (2 * ε * u * s * (1 + ε * u ^ 2) ^ (s - 1)) u := by
  have hq : HasDerivAt (fun u => 1 + ε * u ^ 2) (2 * ε * u) u :=
    (((hasDerivAt_pow 2 u).const_mul ε).const_add 1).congr_deriv (by simp; ring)
  exact (hq.rpow_const (Or.inl (by nlinarith [mul_nonneg hε (sq_nonneg u)]))).congr_deriv
    (by ring)

/-- Helper: first derivative of `(1+εu²)^{-a}`. -/
theorem c06_aux_hd0 (a ε u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (fun u => (1 + ε * u ^ 2) ^ (-a))
      (-2 * a * ε * u * (1 + ε * u ^ 2) ^ (-a - 1)) u :=
  (c06_aux_hq ε (-a) u hε).congr_deriv (by ring)

/-- Helper: second derivative of `(1+εu²)^{-a}`. -/
theorem c06_aux_hd1 (a ε u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (fun u => -2 * a * ε * u * (1 + ε * u ^ 2) ^ (-a - 1))
      (-2 * a * ε * (1 + ε * u ^ 2) ^ (-a - 1) +
        4 * a * (a + 1) * ε ^ 2 * u ^ 2 * (1 + ε * u ^ 2) ^ (-a - 2)) u := by
  have := ((hasDerivAt_id u).const_mul (-2 * a * ε)).mul (c06_aux_hq ε (-a - 1) u hε)
  refine this.congr_deriv ?_
  rw [show -a - 1 - 1 = -a - 2 by ring]; simp only [id]; ring

/-- Helper: third derivative of `(1+εu²)^{-a}`. -/
theorem c06_aux_hd2 (a ε u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (fun u => -2 * a * ε * (1 + ε * u ^ 2) ^ (-a - 1) +
        4 * a * (a + 1) * ε ^ 2 * u ^ 2 * (1 + ε * u ^ 2) ^ (-a - 2))
      (12 * a * (a + 1) * ε ^ 2 * u * (1 + ε * u ^ 2) ^ (-a - 2) -
        8 * a * (a + 1) * (a + 2) * ε ^ 3 * u ^ 3 * (1 + ε * u ^ 2) ^ (-a - 3)) u := by
  have h1 := (c06_aux_hq ε (-a - 1) u hε).const_mul (-2 * a * ε)
  have h2 := ((hasDerivAt_pow 2 u).const_mul (4 * a * (a + 1) * ε ^ 2)).mul
    (c06_aux_hq ε (-a - 2) u hε)
  refine (h1.add h2).congr_deriv ?_
  rw [show -a - 1 - 1 = -a - 2 by ring, show -a - 2 - 1 = -a - 3 by ring]; simp; ring

/-- Helper: `|A''| + |A'''| ≤ (2a + 4a(a+1) + 12a(a+1) + 8a(a+1)(a+2)) ε`. -/
theorem c06_aux_d23_bound (a ε u : ℝ) (ha : 0 < a) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |-2 * a * ε * (1 + ε * u ^ 2) ^ (-a - 1) +
        4 * a * (a + 1) * ε ^ 2 * u ^ 2 * (1 + ε * u ^ 2) ^ (-a - 2)| +
      |12 * a * (a + 1) * ε ^ 2 * u * (1 + ε * u ^ 2) ^ (-a - 2) -
        8 * a * (a + 1) * (a + 2) * ε ^ 3 * u ^ 3 * (1 + ε * u ^ 2) ^ (-a - 3)| ≤
      (2 * a + 4 * a * (a + 1) + 12 * a * (a + 1) + 8 * a * (a + 1) * (a + 2)) * ε := by
  set q := 1 + ε * u ^ 2 with hq
  have hq1 : 1 ≤ q := by nlinarith [mul_nonneg hε (sq_nonneg u)]
  have hq0 : 0 < q := by linarith
  have f1 : q ^ (-a - 2) = q ^ (-a - 1) / q := by
    rw [show -a - 2 = (-a - 1) - 1 by ring, Real.rpow_sub_one hq0.ne']
  have f2 : q ^ (-a - 3) = q ^ (-a - 1) / q / q := by
    rw [show -a - 3 = (-a - 1) - 1 - 1 by ring, Real.rpow_sub_one hq0.ne',
      Real.rpow_sub_one hq0.ne']
  have hQ0 : 0 < q ^ (-a - 1) := Real.rpow_pos_of_pos hq0 _
  have hQ1 : q ^ (-a - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  have hY0 : 0 ≤ ε * u ^ 2 / q := by positivity
  have hY1 : ε * u ^ 2 / q ≤ 1 := by rw [div_le_one hq0]; linarith
  have hX : |ε * u / q| ≤ 1 := by
    rw [abs_div, abs_of_pos hq0, div_le_one hq0, abs_mul, abs_of_nonneg hε]
    have h2 : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1)]
    nlinarith [mul_nonneg hε (sq_nonneg u), abs_nonneg u]
  rw [f1, f2]
  set Q := q ^ (-a - 1)
  set Yv := ε * u ^ 2 / q with hYv
  have e2 : -2 * a * ε * Q + 4 * a * (a + 1) * ε ^ 2 * u ^ 2 * (Q / q) =
      -(2 * ε * a * Q) + 4 * ε * a * (a + 1) * Yv * Q := by
    rw [hYv]; field_simp
  have e3 : 12 * a * (a + 1) * ε ^ 2 * u * (Q / q) -
      8 * a * (a + 1) * (a + 2) * ε ^ 3 * u ^ 3 * (Q / q / q) =
      (ε * u / q) * (12 * ε * a * (a + 1) * Q - 8 * ε * a * (a + 1) * (a + 2) * Yv * Q) := by
    rw [hYv]; field_simp
  rw [e2, e3]
  have hYQ : Yv * Q ≤ 1 := by nlinarith
  have t1 : 0 ≤ 2 * ε * a * Q := by positivity
  have t2 : 0 ≤ 4 * ε * a * (a + 1) * Yv * Q := by positivity
  have t3 : 0 ≤ 12 * ε * a * (a + 1) * Q := by positivity
  have t4 : 0 ≤ 8 * ε * a * (a + 1) * (a + 2) * Yv * Q := by positivity
  have u1 : 2 * ε * a * Q ≤ 2 * ε * a := by
    have := mul_le_mul_of_nonneg_left hQ1 (by positivity : (0 : ℝ) ≤ 2 * ε * a); linarith
  have u2 : 4 * ε * a * (a + 1) * Yv * Q ≤ 4 * ε * a * (a + 1) := by
    have := mul_le_mul_of_nonneg_left hYQ (by positivity : (0 : ℝ) ≤ 4 * ε * a * (a + 1))
    linarith
  have u3 : 12 * ε * a * (a + 1) * Q ≤ 12 * ε * a * (a + 1) := by
    have := mul_le_mul_of_nonneg_left hQ1 (by positivity : (0 : ℝ) ≤ 12 * ε * a * (a + 1))
    linarith
  have u4 : 8 * ε * a * (a + 1) * (a + 2) * Yv * Q ≤ 8 * ε * a * (a + 1) * (a + 2) := by
    have := mul_le_mul_of_nonneg_left hYQ (by positivity : (0 : ℝ) ≤ 8 * ε * a * (a + 1) * (a + 2))
    linarith
  have b2 : |-(2 * ε * a * Q) + 4 * ε * a * (a + 1) * Yv * Q| ≤
      2 * ε * a + 4 * ε * a * (a + 1) := by
    rw [abs_le]; constructor <;> linarith
  have hin : |12 * ε * a * (a + 1) * Q - 8 * ε * a * (a + 1) * (a + 2) * Yv * Q| ≤
      12 * ε * a * (a + 1) + 8 * ε * a * (a + 1) * (a + 2) := by
    rw [abs_le]; constructor <;> linarith
  have b3 : |(ε * u / q) * (12 * ε * a * (a + 1) * Q -
      8 * ε * a * (a + 1) * (a + 2) * Yv * Q)| ≤
      12 * ε * a * (a + 1) + 8 * ε * a * (a + 1) * (a + 2) := by
    rw [abs_mul]
    calc _ ≤ 1 * (12 * ε * a * (a + 1) + 8 * ε * a * (a + 1) * (a + 2)) :=
          mul_le_mul hX hin (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  linarith

/-- Blueprint: lem:c06_A_eps_bounds (auxiliary definition).  The quintic remainder
`Ã_ε(u) = c_α [A_ε(u) - 1 + (α/2) ε u²]`. -/
def c06_A_eps_bounds_quintic (p ε u : ℝ) : ℝ :=
  calpha p * (A_eps p ε u - 1 + (p + 1) / 2 * ε * u ^ 2)

/-- Blueprint: lem:c06_A_eps_bounds.  Bounds for `A_ε` and its quintic remainder, uniform in
`ε ∈ [0,1]`, with a constant `C_A` depending only on `p`. -/
theorem c06_A_eps_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ ε ∈ Icc (0 : ℝ) 1,
      ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε) ∧
      (∀ u : ℝ,
        (0 ≤ 1 - A_eps p ε u ∧ 1 - A_eps p ε u ≤ (p + 1) / 2 * ε * u ^ 2) ∧
        |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| ∧
        |iteratedDeriv 2 (A_eps p ε) u| + |iteratedDeriv 3 (A_eps p ε) u| ≤ C_A * ε ∧
        |c06_A_eps_bounds_quintic p ε u| ≤ C_A * ε ^ 2 * u ^ 4 ∧
        |deriv (c06_A_eps_bounds_quintic p ε) u| ≤ C_A * ε ^ 2 * |u| ^ 3) ∧
      A_eps p ε 0 = 1 ∧ deriv (A_eps p ε) 0 = 0 := by
  set a : ℝ := (p + 1) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set K : ℝ := 2 * a + 4 * a * (a + 1) + 12 * a * (a + 1) + 8 * a * (a + 1) * (a + 2) +
    2 * a * (a + 1) * |calpha p| + 1 with hK
  have hK0 : 0 < K := by positivity
  have hS0 : 0 ≤ 2 * a + 4 * a * (a + 1) + 12 * a * (a + 1) + 8 * a * (a + 1) * (a + 2) := by
    positivity
  have hC0 : 0 ≤ 2 * a * (a + 1) * |calpha p| := by positivity
  have hKc3 : 2 * a + 4 * a * (a + 1) + 12 * a * (a + 1) + 8 * a * (a + 1) * (a + 2) ≤ K := by
    rw [hK]; linarith
  have hKc2 : 2 * a * (a + 1) * |calpha p| ≤ K := by rw [hK]; linarith
  have hKc1 : |calpha p| * a * (a + 1) ≤ K := by
    have : 0 ≤ |calpha p| * a * (a + 1) := by positivity
    linarith
  refine ⟨K, hK0, fun ε hε => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε
  have hAf : A_eps p ε = fun u => (1 + ε * u ^ 2) ^ (-a) := by
    funext u; simp only [A_eps]; rw [ha, neg_div]
  have D1 : deriv (A_eps p ε) = fun u => -2 * a * ε * u * (1 + ε * u ^ 2) ^ (-a - 1) := by
    funext u; rw [hAf]; exact (c06_aux_hd0 a ε u hε0).deriv
  have D2 : deriv (deriv (A_eps p ε)) = fun u => -2 * a * ε * (1 + ε * u ^ 2) ^ (-a - 1) +
      4 * a * (a + 1) * ε ^ 2 * u ^ 2 * (1 + ε * u ^ 2) ^ (-a - 2) := by
    funext u; rw [D1]; exact (c06_aux_hd1 a ε u hε0).deriv
  have D3 : deriv (deriv (deriv (A_eps p ε))) = fun u =>
      12 * a * (a + 1) * ε ^ 2 * u * (1 + ε * u ^ 2) ^ (-a - 2) -
        8 * a * (a + 1) * (a + 2) * ε ^ 3 * u ^ 3 * (1 + ε * u ^ 2) ^ (-a - 3) := by
    funext u; rw [D2]; exact (c06_aux_hd2 a ε u hε0).deriv
  have hq0 : ∀ u, 0 < 1 + ε * u ^ 2 := fun u => by nlinarith [mul_nonneg hε0 (sq_nonneg u)]
  have hAc : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε) := by
    rw [hAf]
    exact (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).rpow_const_of_ne
      (fun u => (hq0 u).ne')
  refine ⟨hAc, fun u => ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- (1)
    have hb := c06_aux_bern a (ε * u ^ 2) ha0 (by positivity)
    rw [congrFun hAf u, show (p + 1) / 2 * ε * u ^ 2 = a * (ε * u ^ 2) by rw [ha]; ring]
    exact hb
  · -- (2)
    rw [D1]
    have hQ0 : 0 < (1 + ε * u ^ 2) ^ (-a - 1) := Real.rpow_pos_of_pos (hq0 u) _
    have hQ1 : (1 + ε * u ^ 2) ^ (-a - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [mul_nonneg hε0 (sq_nonneg u)])
        (by linarith)
    have e : -2 * a * ε * u * (1 + ε * u ^ 2) ^ (-a - 1) =
        -(2 * a * ε * (1 + ε * u ^ 2) ^ (-a - 1) * u) := by ring
    simp only
    rw [e, abs_neg, abs_mul, abs_of_nonneg (by positivity)]
    have h2 : (p + 1) * ε * |u| = 2 * a * ε * |u| := by rw [ha]; ring
    rw [h2]
    have : 0 ≤ 2 * a * ε * |u| := by positivity
    nlinarith
  · -- (3)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [D3, D2]
    exact le_trans (c06_aux_d23_bound a ε u ha0 hε0 hε1) (mul_le_mul_of_nonneg_right hKc3 hε0)
  · -- (4a)
    unfold c06_A_eps_bounds_quintic
    have ht := c06_aux_taylor2 a (ε * u ^ 2) ha0 (by positivity)
    rw [congrFun hAf u, show (p + 1) / 2 * ε * u ^ 2 = a * (ε * u ^ 2) by rw [ha]; ring, abs_mul]
    calc |calpha p| * |(1 + ε * u ^ 2) ^ (-a) - 1 + a * (ε * u ^ 2)|
        ≤ |calpha p| * (a * (a + 1) * (ε * u ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      _ = (|calpha p| * a * (a + 1)) * (ε ^ 2 * u ^ 4) := by ring
      _ ≤ K * (ε ^ 2 * u ^ 4) := mul_le_mul_of_nonneg_right hKc1 (by positivity)
      _ = K * ε ^ 2 * u ^ 4 := by ring
  · -- (4b)
    have hA : HasDerivAt (A_eps p ε) (-2 * a * ε * u * (1 + ε * u ^ 2) ^ (-a - 1)) u := by
      rw [hAf]; exact c06_aux_hd0 a ε u hε0
    have hd : HasDerivAt (c06_A_eps_bounds_quintic p ε)
        (calpha p * (2 * a * ε * u) * (1 - (1 + ε * u ^ 2) ^ (-(a + 1)))) u := by
      have := (((hA.sub_const 1).add ((hasDerivAt_pow 2 u).const_mul (a * ε))).const_mul
        (calpha p))
      refine this.congr_deriv ?_
      rw [show -(a + 1) = -a - 1 by ring]; simp; ring
    rw [hd.deriv]
    have hb := c06_aux_bern (a + 1) (ε * u ^ 2) (by linarith) (by positivity)
    have hu : |2 * a * ε * u| = 2 * a * ε * |u| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a * ε)]
    rw [abs_mul, abs_mul, abs_of_nonneg hb.1, hu]
    have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    calc |calpha p| * (2 * a * ε * |u|) * (1 - (1 + ε * u ^ 2) ^ (-(a + 1)))
        ≤ |calpha p| * (2 * a * ε * |u|) * ((a + 1) * (ε * u ^ 2)) :=
          mul_le_mul_of_nonneg_left hb.2 (by positivity)
      _ = (2 * a * (a + 1) * |calpha p|) * (ε ^ 2 * |u| ^ 3) := by rw [hu2]; ring
      _ ≤ K * (ε ^ 2 * |u| ^ 3) := mul_le_mul_of_nonneg_right hKc2 (by positivity)
      _ = K * ε ^ 2 * |u| ^ 3 := by ring
  · simp [A_eps]
  · rw [D1]; simp

/-- Blueprint: lem:c06_secant_calculus.  Secant calculus for `S_w(y,z) = c01_secant w y z`. -/
theorem c06_secant_calculus (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hw' : ∃ M, ∀ x, |deriv w x| ≤ M) :
    -- (1) bound by the sup of `|w'|` on the segment between `y` and `z`
    (∀ y z : ℝ, y ≠ z → ∀ M : ℝ, (∀ x ∈ uIcc y z, |deriv w x| ≤ M) → |c01_secant w y z| ≤ M) ∧
    -- (2) the map `y ↦ S_w(y,y-s)` for `w ∈ C²` with bounded `w''`
    (ContDiff ℝ 2 w → ∀ M₂ : ℝ, (∀ x, |deriv (deriv w) x| ≤ M₂) → ∀ s : ℝ,
      ContDiff ℝ 1 (fun y => c01_secant w y (y - s)) ∧
      ∀ y : ℝ, deriv (fun y' => c01_secant w y' (y' - s)) y = c01_secant (deriv w) y (y - s) ∧
        |c01_secant (deriv w) y (y - s)| ≤ M₂) ∧
    -- (3) derivative in `y` for fixed `z`, `y ≠ z`
    (∀ y z : ℝ, y ≠ z →
      HasDerivAt (fun y' => c01_secant w y' z) ((deriv w y - c01_secant w y z) / (y - z)) y) ∧
    -- (4) linearity
    (∀ w₁ w₂ : ℝ → ℝ, ContDiff ℝ 1 w₁ → ContDiff ℝ 1 w₂ → ∀ (c y z : ℝ),
      c01_secant (fun x => w₁ x + w₂ x) y z = c01_secant w₁ y z + c01_secant w₂ y z ∧
      c01_secant (fun x => c * w₁ x) y z = c * c01_secant w₁ y z) := by
  have dw : Differentiable ℝ w := hw.differentiable (by norm_num)
  refine ⟨fun y z hyz M hM => c06_aux_secant_le_seg w dw y z hyz M hM, ?_, ?_, ?_⟩
  · intro hw2 M₂ hM₂ s
    have hd : ContDiff ℝ 1 (deriv w) := (contDiff_succ_iff_deriv.mp hw2).2.2
    have dd : Differentiable ℝ (deriv w) := hd.differentiable (by norm_num)
    have hw1 : ContDiff ℝ 1 w := hw
    by_cases hs : s = 0
    · subst hs
      have e : (fun y => c01_secant w y (y - 0)) = deriv w := by
        funext y; simp [c01_secant]
      have e' : (fun y => c01_secant (deriv w) y (y - 0)) = deriv (deriv w) := by
        funext y; simp [c01_secant]
      refine ⟨by rw [e]; exact hd, fun y => ⟨?_, ?_⟩⟩
      · rw [e]; simp [c01_secant]
      · exact c06_aux_secant_le _ dd _ hM₂ _ _
    · have e : (fun y => c01_secant w y (y - s)) = fun y => (w y - w (y - s)) / s := by
        funext y
        have : y ≠ y - s := by intro h; apply hs; linarith
        simp [c01_secant, this]
      refine ⟨?_, fun y => ⟨?_, c06_aux_secant_le _ dd _ hM₂ _ _⟩⟩
      · rw [e]
        exact (hw1.sub (hw1.comp (contDiff_id.sub contDiff_const))).div_const s
      · rw [e]
        have : y ≠ y - s := by intro h; apply hs; linarith
        have hda : HasDerivAt (fun y => (w y - w (y - s)) / s)
            ((deriv w y - deriv w (y - s) * 1) / s) y := by
          apply HasDerivAt.div_const
          apply (dw y).hasDerivAt.sub
          exact (dw (y - s)).hasDerivAt.comp y ((hasDerivAt_id y).sub_const s)
        rw [hda.deriv]
        simp [c01_secant, this]
  · intro y z hyz
    have hev : (fun y' => c01_secant w y' z) =ᶠ[nhds y] fun y' => (w y' - w z) / (y' - z) := by
      filter_upwards [isOpen_ne.mem_nhds hyz] with y' hy'
      simp [c01_secant, hy']
    have hsub : y - z ≠ 0 := sub_ne_zero.mpr hyz
    have hd : HasDerivAt (fun y' => (w y' - w z) / (y' - z))
        (((deriv w y) * (y - z) - (w y - w z) * 1) / (y - z) ^ 2) y := by
      exact ((dw y).hasDerivAt.sub_const (w z)).div ((hasDerivAt_id y).sub_const z) hsub
    apply hd.congr_of_eventuallyEq hev |>.congr_deriv
    simp only [c01_secant, hyz, ite_false]
    field_simp
  · intro w₁ w₂ h₁ h₂ c y z
    have d₁ : Differentiable ℝ w₁ := h₁.differentiable (by norm_num)
    have d₂ : Differentiable ℝ w₂ := h₂.differentiable (by norm_num)
    by_cases hyz : y = z
    · simp only [c01_secant, hyz, ite_true]
      exact ⟨((d₁ z).hasDerivAt.add (d₂ z).hasDerivAt).deriv,
        ((d₁ z).hasDerivAt.const_mul c).deriv⟩
    · simp only [c01_secant, hyz, ite_false]
      constructor <;> ring

/-- Helper: `y ↦ S_w(y,y-s)` has derivative `S_{w'}(y,y-s)` (from lem:c06_secant_calculus). -/
theorem c06_aux_sec_hasDeriv (w : ℝ → ℝ) (hw2 : ContDiff ℝ 2 w) (M₁ M₂ : ℝ)
    (h1 : ∀ x, |deriv w x| ≤ M₁) (h2 : ∀ x, |deriv (deriv w) x| ≤ M₂) (y s : ℝ) :
    HasDerivAt (fun y' => c01_secant w y' (y' - s)) (c01_secant (deriv w) y (y - s)) y := by
  obtain ⟨-, H2, -, -⟩ := c06_secant_calculus w (hw2.of_le (by norm_num)) ⟨M₁, h1⟩
  obtain ⟨hc, hd⟩ := H2 hw2 M₂ h2 s
  have := (hc.differentiable (by norm_num) y).hasDerivAt
  rwa [(hd y).1] at this

/-- Helper: `Y^a Y^b ≤ Y^c` for `Y ≥ 1`, `a + b ≤ c`. -/
theorem c06_aux_mono2 (Y a b c : ℝ) (hY : 1 ≤ Y) (h : a + b ≤ c) : Y ^ a * Y ^ b ≤ Y ^ c := by
  rw [← Real.rpow_add (by linarith)]; exact Real.rpow_le_rpow_of_exponent_le hY h

/-- Helper: `Y^a Y^b Y^c ≤ Y^d` for `Y ≥ 1`, `a + b + c ≤ d`. -/
theorem c06_aux_mono3 (Y a b c d : ℝ) (hY : 1 ≤ Y) (h : a + b + c ≤ d) :
    Y ^ a * Y ^ b * Y ^ c ≤ Y ^ d := by
  rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hY h

/-- Helper: an even function `x ↦ φ |x|` is integrable when `φ` is integrable on `(0,∞)`. -/
theorem c06_aux_integrable_comp_abs (φ : ℝ → ℝ) (h : IntegrableOn φ (Ioi 0)) :
    Integrable (fun x => φ |x|) := by
  have hf : IntegrableOn (fun x => φ |x|) (Ioi 0) :=
    h.congr_fun (fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ φ |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
  have := int_Iic.union hf
  rw [Iic_union_Ioi, integrableOn_univ] at this
  exact this

/-- Helper: the dominating profile `φ(t) = B t^{-p}` (`t ≤ r`), `2A t^{-1-p}` (`t > r`) is
integrable on `(0,∞)` with integral `B r^{1-p}/(1-p) + 2A r^{-p}/p`. -/
theorem c06_aux_profile_int (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (A B r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun t => if t ≤ r then B * t ^ (-p) else 2 * A * t ^ (-1 - p)) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), (if t ≤ r then B * t ^ (-p) else 2 * A * t ^ (-1 - p)) =
      B * r ^ (1 - p) / (1 - p) + 2 * A * r ^ (-p) / p := by
  set φ := fun t : ℝ => if t ≤ r then B * t ^ (-p) else 2 * A * t ^ (-1 - p) with hφ
  have i1 : IntegrableOn (fun t : ℝ => B * t ^ (-p)) (Ioc 0 r) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) (r := -p) (by linarith)).const_mul B
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp this
  have i2 : IntegrableOn (fun t : ℝ => 2 * A * t ^ (-1 - p)) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hr).const_mul _
  have e1 : EqOn (fun t : ℝ => B * t ^ (-p)) φ (Ioc 0 r) := fun t ht => by
    simp only [hφ, ht.2, ↓reduceIte]
  have e2 : EqOn (fun t : ℝ => 2 * A * t ^ (-1 - p)) φ (Ioi r) := fun t ht => by
    simp only [hφ, not_le.mpr (mem_Ioi.mp ht), ↓reduceIte]
  have j1 := i1.congr_fun e1 measurableSet_Ioc
  have j2 := i2.congr_fun e2 measurableSet_Ioi
  have hU : Ioc 0 r ∪ Ioi r = Ioi 0 := Ioc_union_Ioi_eq_Ioi hr.le
  refine ⟨hU ▸ j1.union j2, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi j1 j2,
    ← setIntegral_congr_fun measurableSet_Ioc e1, ← setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_const_mul, ← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by linarith)), integral_Ioi_rpow_of_lt (by linarith) hr,
    Real.zero_rpow (by linarith)]
  have h1 : -p + 1 = 1 - p := by ring
  have h2 : -1 - p + 1 = -p := by ring
  rw [h1, h2]
  field_simp
  ring

/-- Helper: pointwise domination of the difference quotient by the profile of
`c06_aux_profile_int` (with `r = 2A/B`). -/
theorem c06_aux_diff_le_profile (p : ℝ) (hp : 0 < p) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (w : ℝ → ℝ) (hwA : ∀ x, |w x| ≤ A) (hwB : ∀ a b, |w a - w b| ≤ B * |a - b|) (y s : ℝ) :
    |w y - w (y - s)| / |s| ^ (1 + p) ≤
      (if |s| ≤ 2 * A / B then B * |s| ^ (-p) else 2 * A * |s| ^ (-1 - p)) := by
  by_cases hs : s = 0
  · subst hs
    simp only [sub_zero, sub_self, abs_zero, zero_div]
    split_ifs <;> positivity
  have hsp : 0 < |s| := abs_pos.mpr hs
  have hsq : 0 < |s| ^ (1 + p) := Real.rpow_pos_of_pos hsp _
  split_ifs with hle
  · have h1 : |w y - w (y - s)| ≤ B * |s| := by
      have := hwB y (y - s); rwa [show y - (y - s) = s by ring] at this
    calc |w y - w (y - s)| / |s| ^ (1 + p) ≤ B * |s| / |s| ^ (1 + p) :=
          div_le_div_of_nonneg_right h1 hsq.le
      _ = B * |s| ^ (-p) := by
          rw [Real.rpow_add hsp, Real.rpow_one, Real.rpow_neg hsp.le]
          field_simp
  · have h1 : |w y - w (y - s)| ≤ 2 * A := by
      have := abs_sub (w y) (w (y - s))
      linarith [hwA y, hwA (y - s)]
    calc |w y - w (y - s)| / |s| ^ (1 + p) ≤ 2 * A / |s| ^ (1 + p) :=
          div_le_div_of_nonneg_right h1 hsq.le
      _ = 2 * A * |s| ^ (-1 - p) := by
          rw [show -1 - p = -(1 + p) by ring, Real.rpow_neg hsp.le]
          field_simp

/-- Blueprint: lem:c06_difference_integral.  For `|w| ≤ A` and `w` `B`-Lipschitz,
`∫ |w(y)-w(y-s)|/|s|^{1+p} ds ≤ C_p A^{1-p} B^p` with `C_p = 2^{2-p}(1/(1-p) + 1/p)`. -/
theorem c06_difference_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (A B : ℝ) (hA : 0 < A)
    (hB : 0 < B) (w : ℝ → ℝ) (hwA : ∀ x, |w x| ≤ A) (hwB : ∀ a b, |w a - w b| ≤ B * |a - b|)
    (y : ℝ) :
    Integrable (fun s : ℝ => |w y - w (y - s)| / |s| ^ (1 + p)) ∧
    ∫ s, |w y - w (y - s)| / |s| ^ (1 + p) ≤
      (2 : ℝ) ^ (2 - p) * (1 / (1 - p) + 1 / p) * A ^ (1 - p) * B ^ p := by
  set r := 2 * A / B with hr
  have hr0 : 0 < r := by positivity
  set φ := fun t : ℝ => if t ≤ r then B * t ^ (-p) else 2 * A * t ^ (-1 - p) with hφ
  obtain ⟨hφi, hφv⟩ := c06_aux_profile_int p hp hp1 A B r hr0
  have hGi := c06_aux_integrable_comp_abs φ hφi
  have hcont : Continuous w := by
    have : LipschitzWith ⟨B, hB.le⟩ w := LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, Real.dist_eq]; exact hwB a b
    exact this.continuous
  have hmeas : AEStronglyMeasurable (fun s : ℝ => |w y - w (y - s)| / |s| ^ (1 + p)) := by
    refine Measurable.aestronglyMeasurable ?_
    exact (continuous_const.sub (hcont.comp (continuous_const.sub continuous_id))).abs.measurable.div
      (continuous_abs.measurable.pow_const _)
  have bound : ∀ s : ℝ, |w y - w (y - s)| / |s| ^ (1 + p) ≤ φ |s| := by
    intro s
    by_cases hs : s = 0
    · subst hs
      simp only [sub_zero, sub_self, abs_zero, zero_div, hφ]
      split_ifs <;> positivity
    have hsp : 0 < |s| := abs_pos.mpr hs
    have hsq : 0 < |s| ^ (1 + p) := Real.rpow_pos_of_pos hsp _
    simp only [hφ]
    split_ifs with hle
    · have h1 : |w y - w (y - s)| ≤ B * |s| := by
        have := hwB y (y - s); rwa [show y - (y - s) = s by ring] at this
      calc |w y - w (y - s)| / |s| ^ (1 + p) ≤ B * |s| / |s| ^ (1 + p) :=
            div_le_div_of_nonneg_right h1 hsq.le
        _ = B * |s| ^ (-p) := by
            rw [Real.rpow_add hsp, Real.rpow_one, Real.rpow_neg hsp.le]
            field_simp
    · have h1 : |w y - w (y - s)| ≤ 2 * A := by
        have := abs_sub (w y) (w (y - s))
        linarith [hwA y, hwA (y - s)]
      calc |w y - w (y - s)| / |s| ^ (1 + p) ≤ 2 * A / |s| ^ (1 + p) :=
            div_le_div_of_nonneg_right h1 hsq.le
        _ = 2 * A * |s| ^ (-1 - p) := by
            rw [show -1 - p = -(1 + p) by ring, Real.rpow_neg hsp.le]
            field_simp
  have hint : Integrable (fun s : ℝ => |w y - w (y - s)| / |s| ^ (1 + p)) :=
    hGi.mono' hmeas (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact bound s)
  refine ⟨hint, ?_⟩
  calc ∫ s, |w y - w (y - s)| / |s| ^ (1 + p) ≤ ∫ s, φ |s| := integral_mono hint hGi bound
    _ = 2 * (B * r ^ (1 - p) / (1 - p) + 2 * A * r ^ (-p) / p) := by
        rw [integral_comp_abs, hφv]
    _ = _ := by
        have h2A : 0 < 2 * A := by positivity
        set a := (2 * A) ^ (1 - p) * B ^ p with ha
        have k1 : B * r ^ (1 - p) = a := by
          rw [hr, Real.div_rpow h2A.le hB.le, ha]
          have : B ^ p = B ^ (1 : ℝ) / B ^ (1 - p) := by
            rw [← Real.rpow_sub hB]; congr 1; ring
          rw [this, Real.rpow_one]
          have : 0 < B ^ (1 - p) := Real.rpow_pos_of_pos hB _
          field_simp
        have k2 : 2 * A * r ^ (-p) = a := by
          rw [hr, Real.div_rpow h2A.le hB.le, ha]
          have : (2 * A) ^ (1 - p) = (2 * A) ^ (1 : ℝ) * (2 * A) ^ (-p) := by
            rw [← Real.rpow_add h2A]; congr 1
          rw [this, Real.rpow_one, Real.rpow_neg hB.le]
          have : 0 < B ^ p := Real.rpow_pos_of_pos hB _
          field_simp
        have k3 : a = (2 : ℝ) ^ (1 - p) * A ^ (1 - p) * B ^ p := by
          rw [ha, Real.mul_rpow (by norm_num) hA.le]
        have k4 : (2 : ℝ) ^ (2 - p) = 2 * (2 : ℝ) ^ (1 - p) := by
          rw [show (2 : ℝ) - p = 1 + (1 - p) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
        rw [k1, k2, k3, k4]
        ring

/-- Helper: pointwise bound `|a/|s|^q · Φ| ≤ M |a|/|s|^q` when `|Φ| ≤ M`. -/
theorem c06_aux_pt (a s q Φ M : ℝ) (hΦ : |Φ| ≤ M) : |a / |s| ^ q * Φ| ≤ M * (|a| / |s| ^ q) := by
  rw [abs_mul, abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg s) q), mul_comm]
  exact mul_le_mul_of_nonneg_right hΦ (by positivity)

/-- Helper: an integral dominated by `M |w(y)-w(y-s)|/|s|^{1+p}` is bounded through
lem:c06_difference_integral. -/
theorem c06_aux_frac_int_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (A B : ℝ) (hA : 0 < A)
    (hB : 0 < B) (w : ℝ → ℝ) (hwA : ∀ x, |w x| ≤ A) (hwB : ∀ a b, |w a - w b| ≤ B * |a - b|)
    (y M : ℝ) (hM : 0 ≤ M) (F : ℝ → ℝ)
    (hF : ∀ s, |F s| ≤ M * (|w y - w (y - s)| / |s| ^ (1 + p))) :
    |∫ s, F s| ≤ M * ((2 : ℝ) ^ (2 - p) * (1 / (1 - p) + 1 / p) * A ^ (1 - p) * B ^ p) := by
  obtain ⟨hi, hle⟩ := c06_difference_integral p hp hp1 A B hA hB w hwA hwB y
  calc |∫ s, F s| = ‖∫ s, F s‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ s, M * (|w y - w (y - s)| / |s| ^ (1 + p)) :=
        norm_integral_le_of_norm_le (hi.const_mul M)
          (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hF s)
    _ = M * ∫ s, |w y - w (y - s)| / |s| ^ (1 + p) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hle hM

/-- Helper: `0 < A_ε(u) ≤ 1` for `ε ≥ 0`. -/
theorem c06_aux_A_mem (p ε u : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) :
    0 < A_eps p ε u ∧ A_eps p ε u ≤ 1 := by
  unfold A_eps
  have h1 : 1 ≤ 1 + ε * u ^ 2 := by nlinarith [sq_nonneg u]
  exact ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)⟩

/-- Helper: `|A_ε(u) - 1| ≤ 1` for `ε ≥ 0`. -/
theorem c06_aux_A_sub_one (p ε u : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) : |A_eps p ε u - 1| ≤ 1 := by
  obtain ⟨h0, h1⟩ := c06_aux_A_mem p ε u hp hε
  rw [abs_le]; constructor <;> linarith

/-- Helper: the `s`-form and `z`-form of fractional integrands (`z = y - s`). -/
theorem c06_aux_change_var (y : ℝ) (G : ℝ → ℝ) :
    (Integrable G → Integrable (fun z => G (y - z))) ∧ ∫ z, G (y - z) = ∫ s, G s :=
  ⟨fun h => h.comp_sub_left y, integral_sub_left_eq_self (μ := volume) G y⟩

/-- Helper: integrability of `(w'(y)-w'(y-s))/|s|^{1+p} · Ψ(s)` for bounded measurable `Ψ`, when
`w'` and `w''` are bounded. -/
theorem c06_aux_frac_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ 2 w) (B₁ B₂ : ℝ) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (h1 : ∀ x, |deriv w x| ≤ B₁) (h2 : ∀ x, |deriv (deriv w) x| ≤ B₂) (y : ℝ)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (M : ℝ) (hM : ∀ s, |Ψ s| ≤ M) :
    Integrable (fun s => (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * Ψ s) := by
  have hd : ContDiff ℝ 1 (deriv w) := (contDiff_succ_iff_deriv.mp hw).2.2
  have dd : Differentiable ℝ (deriv w) := hd.differentiable (by norm_num)
  obtain ⟨DI, -⟩ := c06_difference_integral p hp hp1 B₁ B₂ hB₁ hB₂ (deriv w) h1
    (c06_aux_lip _ dd _ h2) y
  refine (DI.const_mul M).mono' ?_ (ae_of_all _ fun s => by
    rw [Real.norm_eq_abs]; exact c06_aux_pt _ _ _ _ _ (hM s))
  exact (((measurable_const.sub (dd.continuous.measurable.comp
    (measurable_const.sub measurable_id))).div
    (continuous_abs.measurable.pow_const _)).mul hΨ).aestronglyMeasurable

/-- Blueprint: lem:c06_translated_derivative.  Differentiation of
`I(y) = ∫ (w'(y)-w'(y-s))/|s|^{1+p} Φ(y,s) ds` under the integral sign, with bounds. -/
theorem c06_translated_derivative (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ 3 w) (B₁ B₂ B₃ : ℝ) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB₃ : 0 < B₃)
    (hw1 : ∀ x, |deriv w x| ≤ B₁) (hw2 : ∀ x, |deriv (deriv w) x| ≤ B₂)
    (hw3 : ∀ x, |deriv (deriv (deriv w)) x| ≤ B₃)
    (Φ : ℝ → ℝ → ℝ) (hΦm : Measurable (fun q : ℝ × ℝ => Φ q.1 q.2))
    (hΦd : ∀ s, Differentiable ℝ (fun y => Φ y s))
    (hΦdm : Measurable (fun q : ℝ × ℝ => deriv (fun y => Φ y q.2) q.1))
    (M₀ M₁ : ℝ) (hM₀ : ∀ y s, |Φ y s| ≤ M₀) (hM₁ : ∀ y s, |deriv (fun y' => Φ y' s) y| ≤ M₁) :
    let I : ℝ → ℝ := fun y => ∫ s, (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * Φ y s
    let I' : ℝ → ℝ := fun y => ∫ s, ((deriv (deriv w) y - deriv (deriv w) (y - s)) * Φ y s +
        (deriv w y - deriv w (y - s)) * deriv (fun y' => Φ y' s) y) / |s| ^ (1 + p)
    let Cp : ℝ := (2 : ℝ) ^ (2 - p) * (1 / (1 - p) + 1 / p)
    ∀ y : ℝ,
      Integrable (fun s : ℝ => (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * Φ y s) ∧
      HasDerivAt I (I' y) y ∧
      |I y| ≤ Cp * M₀ * B₁ ^ (1 - p) * B₂ ^ p ∧
      |I' y| ≤ Cp * (M₀ * B₂ ^ (1 - p) * B₃ ^ p + M₁ * B₁ ^ (1 - p) * B₂ ^ p) := by
  intro I I' Cp y
  have hw2' : ContDiff ℝ 2 (deriv w) := (contDiff_succ_iff_deriv.mp hw).2.2
  have hw1' : ContDiff ℝ 1 (deriv (deriv w)) := (contDiff_succ_iff_deriv.mp hw2').2.2
  have dw1 : Differentiable ℝ (deriv w) := hw2'.differentiable (by norm_num)
  have dw2 : Differentiable ℝ (deriv (deriv w)) := hw1'.differentiable (by norm_num)
  have lip1 := c06_aux_lip (deriv w) dw1 B₂ hw2
  have lip2 := c06_aux_lip (deriv (deriv w)) dw2 B₃ hw3
  have hM₀0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀ 0 0)
  have hM₁0 : 0 ≤ M₁ := le_trans (abs_nonneg _) (hM₁ 0 0)
  have hpd := fun y s => (hΦd s y).hasDerivAt
  -- dominating functions
  set φ₁ := fun t : ℝ => if t ≤ 2 * B₁ / B₂ then B₂ * t ^ (-p) else 2 * B₁ * t ^ (-1 - p)
    with hφ₁
  set φ₂ := fun t : ℝ => if t ≤ 2 * B₂ / B₃ then B₃ * t ^ (-p) else 2 * B₂ * t ^ (-1 - p)
    with hφ₂
  have G₁ := c06_aux_integrable_comp_abs φ₁ (c06_aux_profile_int p hp hp1 B₁ B₂ _ (by positivity)).1
  have G₂ := c06_aux_integrable_comp_abs φ₂ (c06_aux_profile_int p hp hp1 B₂ B₃ _ (by positivity)).1
  have P₁ := fun x s => c06_aux_diff_le_profile p hp B₁ B₂ hB₁ hB₂ (deriv w) hw1 lip1 x s
  have P₂ := fun x s => c06_aux_diff_le_profile p hp B₂ B₃ hB₂ hB₃ (deriv (deriv w)) hw2 lip2 x s
  -- measurability
  have mΦ : ∀ x, Measurable (fun s => Φ x s) := fun x =>
    hΦm.comp (measurable_const.prodMk measurable_id)
  have mΦ' : ∀ x, Measurable (fun s => deriv (fun y' => Φ y' s) x) := fun x =>
    hΦdm.comp (measurable_const.prodMk measurable_id)
  have mden : Measurable (fun s : ℝ => |s| ^ (1 + p)) := continuous_abs.measurable.pow_const _
  have mF : ∀ x, AEStronglyMeasurable
      (fun s => (deriv w x - deriv w (x - s)) / |s| ^ (1 + p) * Φ x s) := fun x =>
    (((measurable_const.sub (dw1.continuous.measurable.comp (measurable_const.sub measurable_id))).div
      mden).mul (mΦ x)).aestronglyMeasurable
  have mF' : AEStronglyMeasurable (fun s => ((deriv (deriv w) y - deriv (deriv w) (y - s)) * Φ y s +
      (deriv w y - deriv w (y - s)) * deriv (fun y' => Φ y' s) y) / |s| ^ (1 + p)) :=
    ((((measurable_const.sub (dw2.continuous.measurable.comp
      (measurable_const.sub measurable_id))).mul (mΦ y)).add
      ((measurable_const.sub (dw1.continuous.measurable.comp
      (measurable_const.sub measurable_id))).mul (mΦ' y))).div mden).aestronglyMeasurable
  -- pointwise bounds
  have bF : ∀ x s, |(deriv w x - deriv w (x - s)) / |s| ^ (1 + p) * Φ x s| ≤
      M₀ * (|deriv w x - deriv w (x - s)| / |s| ^ (1 + p)) := fun x s =>
    c06_aux_pt _ _ _ _ _ (hM₀ x s)
  have bF' : ∀ x s, |((deriv (deriv w) x - deriv (deriv w) (x - s)) * Φ x s +
      (deriv w x - deriv w (x - s)) * deriv (fun y' => Φ y' s) x) / |s| ^ (1 + p)| ≤
      M₀ * (|deriv (deriv w) x - deriv (deriv w) (x - s)| / |s| ^ (1 + p)) +
      M₁ * (|deriv w x - deriv w (x - s)| / |s| ^ (1 + p)) := by
    intro x s
    rw [add_div]
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [mul_div_right_comm]; exact c06_aux_pt _ _ _ _ _ (hM₀ x s)
    · rw [mul_div_right_comm]; exact c06_aux_pt _ _ _ _ _ (hM₁ x s)
  obtain ⟨DI1, DB1⟩ := c06_difference_integral p hp hp1 B₁ B₂ hB₁ hB₂ (deriv w) hw1 lip1 y
  obtain ⟨DI2, DB2⟩ := c06_difference_integral p hp hp1 B₂ B₃ hB₂ hB₃ (deriv (deriv w)) hw2 lip2 y
  have hintF : Integrable (fun s : ℝ => (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * Φ y s) :=
    (DI1.const_mul M₀).mono' (mF y) (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]; exact bF y s)
  -- differentiation under the integral sign
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x s => (deriv w x - deriv w (x - s)) / |s| ^ (1 + p) * Φ x s)
    (F' := fun x s => ((deriv (deriv w) x - deriv (deriv w) (x - s)) * Φ x s +
      (deriv w x - deriv w (x - s)) * deriv (fun y' => Φ y' s) x) / |s| ^ (1 + p))
    (x₀ := y) (bound := fun s => M₀ * φ₂ |s| + M₁ * φ₁ |s|) (s := univ) univ_mem
    (Eventually.of_forall mF) hintF mF'
    (ae_of_all _ fun s x _ => by
      rw [Real.norm_eq_abs]
      refine le_trans (bF' x s) (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (P₂ x s) hM₀0
      · exact mul_le_mul_of_nonneg_left (P₁ x s) hM₁0)
    ((G₂.const_mul M₀).add (G₁.const_mul M₁))
    (ae_of_all _ fun s x _ => by
      have h1 : HasDerivAt (fun x => deriv w x - deriv w (x - s))
          (deriv (deriv w) x - deriv (deriv w) (x - s)) x :=
        (dw1 x).hasDerivAt.sub (HasDerivAt.comp_sub_const x s (dw1 (x - s)).hasDerivAt)
      have h2 := (h1.div_const (|s| ^ (1 + p))).mul (hpd x s)
      refine h2.congr_deriv ?_
      ring)
  refine ⟨hintF, hder.2, ?_, ?_⟩
  · have := c06_aux_frac_int_le p hp hp1 B₁ B₂ hB₁ hB₂ (deriv w) hw1 lip1 y M₀ hM₀0 _ (bF y)
    exact le_trans this (le_of_eq (by simp only [Cp]; ring))
  · calc |I' y| = ‖I' y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ s, (M₀ * (|deriv (deriv w) y - deriv (deriv w) (y - s)| / |s| ^ (1 + p)) +
            M₁ * (|deriv w y - deriv w (y - s)| / |s| ^ (1 + p))) :=
          norm_integral_le_of_norm_le ((DI2.const_mul M₀).add (DI1.const_mul M₁))
            (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact bF' y s)
      _ = M₀ * (∫ s, |deriv (deriv w) y - deriv (deriv w) (y - s)| / |s| ^ (1 + p)) +
            M₁ * (∫ s, |deriv w y - deriv w (y - s)| / |s| ^ (1 + p)) := by
          rw [integral_add (DI2.const_mul M₀) (DI1.const_mul M₁), integral_const_mul,
            integral_const_mul]
      _ ≤ M₀ * (Cp * B₂ ^ (1 - p) * B₃ ^ p) + M₁ * (Cp * B₁ ^ (1 - p) * B₂ ^ p) :=
          add_le_add (mul_le_mul_of_nonneg_left DB2 hM₀0) (mul_le_mul_of_nonneg_left DB1 hM₁0)
      _ = _ := by ring

/-- Helper: lem:c06_translated_derivative in the form used below (the `y`-derivative of `Φ`
given explicitly as `Φ'`). -/
theorem c06_aux_TD (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ 3 w) (B₁ B₂ B₃ : ℝ) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB₃ : 0 < B₃)
    (hw1 : ∀ x, |deriv w x| ≤ B₁) (hw2 : ∀ x, |deriv (deriv w) x| ≤ B₂)
    (hw3 : ∀ x, |deriv (deriv (deriv w)) x| ≤ B₃)
    (Φ Φ' : ℝ → ℝ → ℝ) (hΦm : Measurable (fun q : ℝ × ℝ => Φ q.1 q.2))
    (hΦ'm : Measurable (fun q : ℝ × ℝ => Φ' q.1 q.2))
    (hΦd : ∀ y s, HasDerivAt (fun y' => Φ y' s) (Φ' y s) y)
    (M₀ M₁ : ℝ) (hM₀ : ∀ y s, |Φ y s| ≤ M₀) (hM₁ : ∀ y s, |Φ' y s| ≤ M₁) (y : ℝ) :
    HasDerivAt (fun y => ∫ s, (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * Φ y s)
      (∫ s, ((deriv (deriv w) y - deriv (deriv w) (y - s)) * Φ y s +
        (deriv w y - deriv w (y - s)) * Φ' y s) / |s| ^ (1 + p)) y ∧
    |∫ s, ((deriv (deriv w) y - deriv (deriv w) (y - s)) * Φ y s +
        (deriv w y - deriv w (y - s)) * Φ' y s) / |s| ^ (1 + p)| ≤
      (2 : ℝ) ^ (2 - p) * (1 / (1 - p) + 1 / p) *
        (M₀ * B₂ ^ (1 - p) * B₃ ^ p + M₁ * B₁ ^ (1 - p) * B₂ ^ p) := by
  have hderiv : ∀ y s, deriv (fun y' => Φ y' s) y = Φ' y s := fun y s => (hΦd y s).deriv
  have hm' : Measurable (fun q : ℝ × ℝ => deriv (fun y => Φ y q.2) q.1) := by
    have : (fun q : ℝ × ℝ => deriv (fun y => Φ y q.2) q.1) = fun q => Φ' q.1 q.2 := by
      funext q; exact hderiv q.1 q.2
    rw [this]; exact hΦ'm
  have H := c06_translated_derivative p hp hp1 w hw B₁ B₂ B₃ hB₁ hB₂ hB₃ hw1 hw2 hw3 Φ hΦm
    (fun s y => (hΦd y s).differentiableAt) hm' M₀ M₁ hM₀
    (fun y s => by rw [hderiv]; exact hM₁ y s) y
  simp only [hderiv] at H
  exact ⟨H.2.1, H.2.2.2⟩

/-- Helper: joint measurability of `(y,s) ↦ S_w(y,y-s)` for continuous `w`. -/
theorem c06_aux_secant_meas (w : ℝ → ℝ) (hw : Continuous w) :
    Measurable (fun q : ℝ × ℝ => c01_secant w q.1 (q.1 - q.2)) := by
  unfold c01_secant
  refine Measurable.ite ?_ ((measurable_deriv w).comp measurable_fst) ?_
  · exact measurableSet_eq_fun measurable_fst (measurable_fst.sub measurable_snd)
  · exact ((hw.measurable.comp measurable_fst).sub
      (hw.measurable.comp (measurable_fst.sub measurable_snd))).div
      (measurable_fst.sub (measurable_fst.sub measurable_snd))

/-- Helper: the reflection `z ↦ y - z` maps `(-∞,0)` onto `(y,∞)`. -/
theorem c06_aux_shift (y : ℝ) (g : ℝ → ℝ) :
    (IntegrableOn g (Ioi y) → IntegrableOn (fun z => g (y - z)) (Iio 0)) ∧
    ∫ z in Iio (0 : ℝ), g (y - z) = ∫ t in Ioi y, g t := by
  have hmp : MeasurePreserving (fun z : ℝ => y - z) volume volume := Measure.measurePreserving_sub_left volume y
  have hme : MeasurableEmbedding (fun z : ℝ => y - z) := (Homeomorph.subLeft y).measurableEmbedding
  have hpre : (fun z : ℝ => y - z) ⁻¹' Ioi y = Iio 0 := by ext z; simp
  refine ⟨fun h => ?_, ?_⟩
  · have := (hmp.integrableOn_comp_preimage hme (f := g) (s := Ioi y)).mpr h
    rwa [hpre] at this
  · have := hmp.setIntegral_preimage_emb hme g (Ioi y)
    rwa [hpre] at this

/-- Helper: the reflection `z ↦ y - z` on a general set. -/
theorem c06_aux_shift_set (y : ℝ) (g : ℝ → ℝ) (s : Set ℝ) :
    (IntegrableOn g s → IntegrableOn (fun z => g (y - z)) ((fun z => y - z) ⁻¹' s)) ∧
    ∫ z in (fun z => y - z) ⁻¹' s, g (y - z) = ∫ t in s, g t := by
  have hmp : MeasurePreserving (fun z : ℝ => y - z) volume volume := Measure.measurePreserving_sub_left volume y
  have hme : MeasurableEmbedding (fun z : ℝ => y - z) := (Homeomorph.subLeft y).measurableEmbedding
  exact ⟨fun h => (hmp.integrableOn_comp_preimage hme (f := g) (s := s)).mpr h,
    hmp.setIntegral_preimage_emb hme g s⟩

/-- Helper: lem:c06_tail_integrals (1). -/
theorem c06_aux_tail1 (a y : ℝ) (ha : 1 < a) (hy : 0 < y) :
      IntegrableOn (fun z => (y - z) ^ (-a)) (Iio 0) ∧
      ∫ z in Iio (0 : ℝ), (y - z) ^ (-a) = y ^ (1 - a) / (a - 1) := by
  obtain ⟨h1, h2⟩ := c06_aux_shift y (fun t => t ^ (-a))
  refine ⟨h1 (integrableOn_Ioi_rpow_of_lt (by linarith) hy), ?_⟩
  rw [h2, integral_Ioi_rpow_of_lt (by linarith) hy]
  rw [show -a + 1 = 1 - a by ring, show (1 - a) = -(a - 1) by ring, neg_div, div_neg, neg_neg]

/-- Helper: lem:c06_tail_integrals (2). -/
theorem c06_aux_tail2 (a r y : ℝ) (ha : 1 < a) (hr : 0 < r) :
      IntegrableOn (fun z => |y - z| ^ (-a)) {z | r ≤ |y - z|} ∧
      ∫ z in {z | r ≤ |y - z|}, |y - z| ^ (-a) = 2 * r ^ (1 - a) / (a - 1) := by
  have hpre : {z | r ≤ |y - z|} = (fun z => y - z) ⁻¹' {t | r ≤ |t|} := rfl
  obtain ⟨h1, h2⟩ := c06_aux_shift_set y (fun t => |t| ^ (-a)) {t | r ≤ |t|}
  set h : ℝ → ℝ := fun s => if r ≤ s then s ^ (-a) else 0 with hh
  have hind : ∀ t, {t : ℝ | r ≤ |t|}.indicator (fun t => |t| ^ (-a)) t = h |t| := by
    intro t; simp only [indicator, mem_ofPred_eq, hh]
  have hms : MeasurableSet {t : ℝ | r ≤ |t|} := measurableSet_le measurable_const measurable_abs
  have hIci : IntegrableOn (fun s : ℝ => s ^ (-a)) (Ici r) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_Ioi_rpow_of_lt (by linarith) hr)
  have hhi : IntegrableOn h (Ioi 0) := by
    have : IntegrableOn ((Ici r).indicator (fun s : ℝ => s ^ (-a))) (Ioi 0) :=
      (hIci.integrable_indicator measurableSet_Ici).integrableOn
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [indicator, mem_Ici, hh]
  have hint : Integrable (fun t => h |t|) := c06_aux_integrable_comp_abs h hhi
  have hon : IntegrableOn (fun t => |t| ^ (-a)) {t | r ≤ |t|} := by
    rw [← integrable_indicator_iff hms]
    exact hint.congr (ae_of_all _ fun t => (hind t).symm)
  refine ⟨hpre ▸ h1 hon, ?_⟩
  rw [hpre, h2, ← integral_indicator hms]
  simp_rw [hind]
  rw [integral_comp_abs]
  have : ∫ s in Ioi (0 : ℝ), h s = ∫ s in Ici r, s ^ (-a) := by
    rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Ioi]
    congr 1; funext s
    simp only [indicator, mem_Ici, mem_Ioi, hh]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; linarith)
  rw [this, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hr]
  rw [show -a + 1 = 1 - a by ring]
  have : a - 1 ≠ 0 := by linarith
  have : 1 - a ≠ 0 := by linarith
  field_simp
  ring

/-- Helper: integral of the two-piece profile `B t^{-q}` (`t ≤ r`), `C t^e` (`t > r`). -/
theorem c06_aux_split_int (q e B C r : ℝ) (hq : q < 1) (he : e < -1) (hr : 0 < r) :
    IntegrableOn (fun t => if t ≤ r then B * t ^ (-q) else C * t ^ e) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), (if t ≤ r then B * t ^ (-q) else C * t ^ e) =
      B * r ^ (1 - q) / (1 - q) + C * (-r ^ (e + 1) / (e + 1)) := by
  set φ := fun t : ℝ => if t ≤ r then B * t ^ (-q) else C * t ^ e with hφ
  have i1 : IntegrableOn (fun t : ℝ => B * t ^ (-q)) (Ioc 0 r) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r) (r := -q)
      (by linarith)).const_mul B
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp this
  have i2 : IntegrableOn (fun t : ℝ => C * t ^ e) (Ioi r) :=
    (integrableOn_Ioi_rpow_of_lt he hr).const_mul _
  have e1 : EqOn (fun t : ℝ => B * t ^ (-q)) φ (Ioc 0 r) := fun t ht => by
    simp only [hφ, ht.2, ↓reduceIte]
  have e2 : EqOn (fun t : ℝ => C * t ^ e) φ (Ioi r) := fun t ht => by
    simp only [hφ, not_le.mpr (mem_Ioi.mp ht), ↓reduceIte]
  have j1 := i1.congr_fun e1 measurableSet_Ioc
  have j2 := i2.congr_fun e2 measurableSet_Ioi
  have hU : Ioc 0 r ∪ Ioi r = Ioi 0 := Ioc_union_Ioi_eq_Ioi hr.le
  refine ⟨hU ▸ j1.union j2, ?_⟩
  rw [← hU, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi j1 j2,
    ← setIntegral_congr_fun measurableSet_Ioc e1, ← setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_const_mul, ← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by linarith)), integral_Ioi_rpow_of_lt he hr,
    Real.zero_rpow (by linarith)]
  rw [show -q + 1 = 1 - q by ring]
  ring

/-- Helper: `⟨z⟩ ≥ |z|`. -/
theorem c06_aux_abs_le_jb (z : ℝ) : |z| ≤ jb z := by
  unfold jb
  rw [show |z| = Real.sqrt (z ^ 2) by rw [Real.sqrt_sq_eq_abs]]
  exact Real.sqrt_le_sqrt (by linarith)

/-- Helper: lem:c06_tail_integrals (3). -/
theorem c06_aux_tail3 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (a y : ℝ) (ha : 0 < a) (hy : 0 < y) :
      IntegrableOn (fun z => jb z ^ (-1 - p) * (y - z) ^ (-a)) (Iio 0) ∧
      ∫ z in Iio (0 : ℝ), jb z ^ (-1 - p) * (y - z) ^ (-a) ≤ (1 + 1 / p) * y ^ (-a) := by
  set ψ := fun t : ℝ => if t ≤ 1 then 1 * t ^ (-0 : ℝ) else 1 * t ^ (-1 - p) with hψ
  obtain ⟨hψi, hψv⟩ := c06_aux_split_int 0 (-1 - p) 1 1 1 (by norm_num) (by linarith) one_pos
  obtain ⟨s1, s2⟩ := c06_aux_shift 0 ψ
  have hψi' := s1 hψi
  have hjb : Continuous jb := by unfold jb; fun_prop
  have hmeas : AEStronglyMeasurable (fun z => jb z ^ (-1 - p) * (y - z) ^ (-a))
      (volume.restrict (Iio 0)) :=
    ((hjb.measurable.pow_const _).mul ((measurable_const.sub measurable_id).pow_const _)
      ).aestronglyMeasurable
  have hya : 0 < y ^ (-a) := Real.rpow_pos_of_pos hy _
  have bound : ∀ z ∈ Iio (0 : ℝ), jb z ^ (-1 - p) * (y - z) ^ (-a) ≤ y ^ (-a) * ψ (0 - z) := by
    intro z hz
    have hz0 : z < 0 := hz
    have h1 : (y - z) ^ (-a) ≤ y ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hy (by linarith) (by linarith)
    have h2 : jb z ^ (-1 - p) ≤ ψ (0 - z) := by
      simp only [hψ, zero_sub, one_mul]
      split_ifs with hle
      · rw [neg_zero, Real.rpow_zero]
        exact Real.rpow_le_one_of_one_le_of_nonpos (c06_aux_one_le_jb z) (by linarith)
      · have : -z ≤ jb z := by have := c06_aux_abs_le_jb z; rwa [abs_of_neg hz0] at this
        exact Real.rpow_le_rpow_of_nonpos (by linarith) this (by linarith)
    have h3 : 0 ≤ jb z ^ (-1 - p) := Real.rpow_nonneg (c06_aux_jb_pos z).le _
    have h4 : 0 ≤ (y - z) ^ (-a) := Real.rpow_nonneg (by linarith) _
    calc jb z ^ (-1 - p) * (y - z) ^ (-a) ≤ ψ (0 - z) * y ^ (-a) := mul_le_mul h2 h1 h4 (by linarith)
      _ = _ := mul_comm _ _
  have hint : IntegrableOn (fun z => jb z ^ (-1 - p) * (y - z) ^ (-a)) (Iio 0) := by
    refine Integrable.mono' (hψi'.const_mul (y ^ (-a))) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (c06_aux_jb_pos z).le _)
      (Real.rpow_nonneg (by linarith [show z < 0 from hz]) _))]
    exact bound z hz
  refine ⟨hint, ?_⟩
  calc ∫ z in Iio (0 : ℝ), jb z ^ (-1 - p) * (y - z) ^ (-a)
      ≤ ∫ z in Iio (0 : ℝ), y ^ (-a) * ψ (0 - z) :=
        setIntegral_mono_on hint (hψi'.const_mul _) measurableSet_Iio bound
    _ = y ^ (-a) * (1 + 1 / p) := by
        rw [integral_const_mul, s2, hψv]
        have : (-1 - p + 1) = -p := by ring
        rw [this]
        simp only [Real.one_rpow, sub_zero, div_one, one_mul, neg_div_neg_eq]
    _ = _ := mul_comm _ _

/-- Helper: lem:c06_tail_integrals (4). -/
theorem c06_aux_tail4 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (a y : ℝ) (ha : 1 - p < a) (hy : 0 < y) :
      IntegrableOn (fun t => jb t ^ (-p) * (y + t) ^ (-a)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), jb t ^ (-p) * (y + t) ^ (-a) ≤
        (1 / (1 - p) + 1 / (a + p - 1)) * y ^ (1 - p - a) := by
  have ha0 : 0 < a := by linarith
  set χ := fun t : ℝ => if t ≤ y then y ^ (-a) * t ^ (-p) else 1 * t ^ (-p - a) with hχ
  obtain ⟨hχi, hχv⟩ := c06_aux_split_int p (-p - a) (y ^ (-a)) 1 y hp1 (by linarith) hy
  have hjb : Continuous jb := by unfold jb; fun_prop
  have hmeas : AEStronglyMeasurable (fun t => jb t ^ (-p) * (y + t) ^ (-a))
      (volume.restrict (Ioi 0)) :=
    ((hjb.measurable.pow_const _).mul ((measurable_const.add measurable_id).pow_const _)
      ).aestronglyMeasurable
  have bound : ∀ t ∈ Ioi (0 : ℝ), jb t ^ (-p) * (y + t) ^ (-a) ≤ χ t := by
    intro t ht
    have ht0 : 0 < t := ht
    have hj : jb t ^ (-p) ≤ t ^ (-p) := by
      have : t ≤ jb t := by have := c06_aux_abs_le_jb t; rwa [abs_of_pos ht0] at this
      exact Real.rpow_le_rpow_of_nonpos ht0 this (by linarith)
    have h3 : 0 ≤ jb t ^ (-p) := Real.rpow_nonneg (c06_aux_jb_pos t).le _
    have h4 : 0 ≤ (y + t) ^ (-a) := Real.rpow_nonneg (by linarith) _
    simp only [hχ]
    split_ifs with hle
    · have h1 : (y + t) ^ (-a) ≤ y ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hy (by linarith) (by linarith)
      calc jb t ^ (-p) * (y + t) ^ (-a) ≤ t ^ (-p) * y ^ (-a) :=
            mul_le_mul hj h1 h4 (Real.rpow_nonneg ht0.le _)
        _ = _ := mul_comm _ _
    · have h1 : (y + t) ^ (-a) ≤ t ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith)
      calc jb t ^ (-p) * (y + t) ^ (-a) ≤ t ^ (-p) * t ^ (-a) :=
            mul_le_mul hj h1 h4 (Real.rpow_nonneg ht0.le _)
        _ = 1 * t ^ (-p - a) := by rw [one_mul, ← Real.rpow_add ht0]; ring_nf
  have hint : IntegrableOn (fun t => jb t ^ (-p) * (y + t) ^ (-a)) (Ioi 0) := by
    refine Integrable.mono' hχi hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (c06_aux_jb_pos t).le _)
      (Real.rpow_nonneg (by linarith [show 0 < t from ht]) _))]
    exact bound t ht
  refine ⟨hint, ?_⟩
  calc ∫ t in Ioi (0 : ℝ), jb t ^ (-p) * (y + t) ^ (-a) ≤ ∫ t in Ioi (0 : ℝ), χ t :=
        setIntegral_mono_on hint hχi measurableSet_Ioi bound
    _ = _ := by
        rw [hχv]
        have e1 : y ^ (-a) * y ^ (1 - p) = y ^ (1 - p - a) := by
          rw [← Real.rpow_add hy]; ring_nf
        have e2 : -p - a + 1 = 1 - p - a := by ring
        rw [e2]
        have : a + p - 1 ≠ 0 := by linarith
        have : 1 - p ≠ 0 := by linarith
        have : -p - a + 1 ≠ 0 := by linarith
        have : 1 - p - a ≠ 0 := by linarith
        rw [show y ^ (-a) * y ^ (1 - p) / (1 - p) = y ^ (1 - p - a) / (1 - p) by rw [e1]]
        field_simp
        ring

/-- Blueprint: lem:c06_tail_integrals.  Elementary tail integrals. -/
theorem c06_tail_integrals (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    -- (1)
    (∀ a y : ℝ, 1 < a → 0 < y →
      IntegrableOn (fun z => (y - z) ^ (-a)) (Iio 0) ∧
      ∫ z in Iio (0 : ℝ), (y - z) ^ (-a) = y ^ (1 - a) / (a - 1)) ∧
    -- (2)
    (∀ a r y : ℝ, 1 < a → 0 < r →
      IntegrableOn (fun z => |y - z| ^ (-a)) {z | r ≤ |y - z|} ∧
      ∫ z in {z | r ≤ |y - z|}, |y - z| ^ (-a) = 2 * r ^ (1 - a) / (a - 1)) ∧
    -- (3)
    (∀ a y : ℝ, 0 < a → 0 < y →
      IntegrableOn (fun z => jb z ^ (-1 - p) * (y - z) ^ (-a)) (Iio 0) ∧
      ∫ z in Iio (0 : ℝ), jb z ^ (-1 - p) * (y - z) ^ (-a) ≤ (1 + 1 / p) * y ^ (-a)) ∧
    -- (4)
    (∀ a y : ℝ, 1 - p < a → 0 < y →
      IntegrableOn (fun t => jb t ^ (-p) * (y + t) ^ (-a)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), jb t ^ (-p) * (y + t) ^ (-a) ≤
        (1 / (1 - p) + 1 / (a + p - 1)) * y ^ (1 - p - a)) := by
  exact ⟨fun a y ha hy => c06_aux_tail1 a y ha hy, fun a r y ha hr => c06_aux_tail2 a r y ha hr,
    fun a y ha hy => c06_aux_tail3 p hp hp1 a y ha hy,
    fun a y ha hy => c06_aux_tail4 p hp hp1 a y ha hy⟩

/-- Helper: the smallness threshold `ε₀*(δ)` for `ε`
coming from blueprint chapter 04 (`FamilyAndE1toE4`): the minimum of the `ε₀`'s provided (for the given `δ`) by
prop:approx_profile_bounds, lem:c04_family_regions, lem:c04_Z_bounds and lem:c04_Z_primitive
(`1` if `δ` is out of range, never used).  The chapter's family statements assume
`ε₀ ≤ c06_eps0_star P δ`. -/
def c06_eps0_star (P : parameters) (δ : ℝ) : ℝ :=
  if h : 0 < δ ∧ δ ≤ ‖mu_star P.p‖ / 2 then
    min (Classical.choose (approx_profile_bounds P.p P.hp_lo P.hp_hi δ h.1 h.2))
      (min (Classical.choose (c04_family_regions P.p P.hp_lo P.hp_hi δ h.1 h.2))
        (min (Classical.choose (c04_Z_bounds P.p P.hp_lo P.hp_hi δ h.1 h.2))
          (Classical.choose (c04_Z_primitive P.p P.hp_lo P.hp_hi δ h.1 h.2))))
  else 1

/-- Helper: `ε ∈ [0, ε₀*(δ)]` implies `ε ∈ [0, ε₀]` for each of the four chapter 04 thresholds. -/
theorem c06_aux_eps0_star_le (P : parameters) (δ : ℝ) (hδ : 0 < δ)
    (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) (c06_eps0_star P δ)) :
    ε ∈ Icc (0 : ℝ) (Classical.choose (approx_profile_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ)) ∧
    ε ∈ Icc (0 : ℝ) (Classical.choose (c04_family_regions P.p P.hp_lo P.hp_hi δ hδ hδμ)) ∧
    ε ∈ Icc (0 : ℝ) (Classical.choose (c04_Z_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ)) ∧
    ε ∈ Icc (0 : ℝ) (Classical.choose (c04_Z_primitive P.p P.hp_lo P.hp_hi δ hδ hδμ)) := by
  have h : 0 < δ ∧ δ ≤ ‖mu_star P.p‖ / 2 := ⟨hδ, hδμ⟩
  have e : c06_eps0_star P δ =
      min (Classical.choose (approx_profile_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ))
      (min (Classical.choose (c04_family_regions P.p P.hp_lo P.hp_hi δ hδ hδμ))
        (min (Classical.choose (c04_Z_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ))
          (Classical.choose (c04_Z_primitive P.p P.hp_lo P.hp_hi δ hδ hδμ)))) := by
    simp [c06_eps0_star, hδ, hδμ]
  obtain ⟨h0, h1⟩ := hε
  rw [e] at h1
  refine ⟨⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩, ⟨h0, ?_⟩⟩
  · exact le_trans h1 (min_le_left _ _)
  · exact le_trans h1 (le_trans (min_le_right _ _) (min_le_left _ _))
  · exact le_trans h1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  · exact le_trans h1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))

/-- Helper: the profile bounds of prop:approx_profile_bounds for `ε ≤ ε₀*(δ)`. -/
theorem c06_aux_eps0_star_spec (P : parameters) (δ : ℝ) (hδ : 0 < δ)
    (hδμ : δ ≤ ‖mu_star P.p‖ / 2) :
    ∃ R₀ ≥ (2 : ℝ),
      (∀ j : ℕ, ∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) (c06_eps0_star P δ), ∀ μ ∈ Bbar P.p δ,
        (∀ y ≥ (0 : ℝ), |approximate_solution_family P.p R ε μ y| ≤ C * jb y ^ (-P.p) ∧
          |iteratedDeriv (j + 1) (approximate_solution_family P.p R ε μ) y| ≤
            C * jb y ^ (-beta P.p + j / P.p)) ∧
        (∀ y ≤ (0 : ℝ),
          |iteratedDeriv j (fun t => approximate_solution_family P.p R ε μ t + t) y| ≤
            C * jb y ^ (-P.p - j))) ∧
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) (c06_eps0_star P δ),
        (∀ μ ∈ Bbar P.p δ, ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family P.p R ε μ))) := by
  obtain ⟨-, R₀, hR₀, hA, hB⟩ :=
    Classical.choose_spec (approx_profile_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ)
  refine ⟨R₀, hR₀, fun j => ?_, fun R hR ε hε => (hB R hR ε (c06_aux_eps0_star_le P δ hδ hδμ ε hε).1).1⟩
  obtain ⟨C, hC, H⟩ := hA j
  exact ⟨C, hC, fun R hR ε hε => H R hR ε (c06_aux_eps0_star_le P δ hδ hδμ ε hε).1⟩

/-- Helper: lem:c04_family_regions for `ε ≤ ε₀*(δ)`. -/
theorem c06_aux_eps0_regions (P : parameters) (δ : ℝ) (hδ : 0 < δ)
    (hδμ : δ ≤ ‖mu_star P.p‖ / 2) :
    ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) (c06_eps0_star P δ), ∀ μ ∈ Bbar P.p δ,
        (∀ y ≥ 2 * R, approximate_solution_family P.p R ε μ y =
          c04_linear_seed_low P.p y + c_plus P.p ε * y ^ (-P.p) -
            2 * (∫ t in Ioi y, (fam_Z P.p R ε μ t + (c_cubic P.p ε : ℂ) * fam_Z P.p R ε μ t ^ 3)).re) ∧
        (∀ y ≥ 2 * R, deriv (approximate_solution_family P.p R ε μ) y =
          deriv (c04_linear_seed_low P.p) y - P.p * c_plus P.p ε * y ^ (-P.p - 1) +
            2 * (fam_Z P.p R ε μ y + (c_cubic P.p ε : ℂ) * fam_Z P.p R ε μ y ^ 3).re) := by
  obtain ⟨-, R₀, hR₀, H⟩ :=
    Classical.choose_spec (c04_family_regions P.p P.hp_lo P.hp_hi δ hδ hδμ)
  refine ⟨R₀, hR₀, fun R hR ε hε μ hμ => ?_⟩
  obtain ⟨-, -, -, -, h1, -, h2⟩ := (H R hR).1 ε (c06_aux_eps0_star_le P δ hδ hδμ ε hε).2.1 μ hμ
  exact ⟨h1, h2⟩

/-- Helper: integrability of `Z` (lem:c04_Z_primitive) and the bound `|Z| ≤ C y^{-β}`
(lem:c04_Z_bounds) for `ε ≤ ε₀*(δ)`. -/
theorem c06_aux_eps0_Z (P : parameters) (δ : ℝ) (hδ : 0 < δ)
    (hδμ : δ ≤ ‖mu_star P.p‖ / 2) :
    ∃ R₀ ≥ (2 : ℝ), ∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) (c06_eps0_star P δ),
      ∀ μ ∈ Bbar P.p δ, ∀ y ≥ R,
        IntegrableOn (fam_Z P.p R ε μ) (Ioi y) ∧ ‖fam_Z P.p R ε μ y‖ ≤ C * y ^ (-beta P.p) := by
  obtain ⟨-, R₁, hR₁, H1, -⟩ :=
    Classical.choose_spec (c04_Z_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ)
  obtain ⟨-, R₂, hR₂, H2, -⟩ :=
    Classical.choose_spec (c04_Z_primitive P.p P.hp_lo P.hp_hi δ hδ hδμ)
  obtain ⟨C, hC, H1'⟩ := H1 0 1 one_pos
  refine ⟨max R₁ R₂, le_trans hR₁ (le_max_left _ _), C, hC, fun R hR ε hε μ hμ y hy => ?_⟩
  have hε' := c06_aux_eps0_star_le P δ hδ hδμ ε hε
  refine ⟨(H2 R (le_trans (le_max_right _ _) hR) ε hε'.2.2.2 μ hμ y hy).1, ?_⟩
  have := (H1' R (le_trans (le_max_left _ _) hR) ε hε'.2.2.1 μ hμ y hy).1
  simpa using this

/-- Helper: for `z ≥ 1` and `e ≤ 3`, `⟨z⟩^e ≤ 8 z^e`. -/
theorem c06_aux_jb_rpow_le (z e : ℝ) (hz : 1 ≤ z) (he : e ≤ 3) : jb z ^ e ≤ 8 * z ^ e := by
  have hz0 : 0 < z := by linarith
  have hzj : z ≤ jb z := le_trans (le_abs_self z) (c06_aux_abs_le_jb z)
  have hj2 : jb z ≤ 2 * z := by
    unfold jb
    rw [show 2 * z = Real.sqrt ((2 * z) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hze := Real.rpow_pos_of_pos hz0 e
  rcases le_total e 0 with h | h
  · have := Real.rpow_le_rpow_of_nonpos hz0 hzj h
    linarith
  · calc jb z ^ e ≤ (2 * z) ^ e := Real.rpow_le_rpow (c06_aux_jb_pos z).le hj2 h
      _ = 2 ^ e * z ^ e := Real.mul_rpow (by norm_num) hz0.le
      _ ≤ 2 ^ (3 : ℝ) * z ^ e := by
          gcongr
          · norm_num
      _ = 8 * z ^ e := by norm_num

/-- Helper: `⟨z⟩^{-b} ≤ 1` for `b ≥ 0`. -/
theorem c06_aux_jb_rpow_neg_le_one (z b : ℝ) (hb : 0 ≤ b) : jb z ^ (-b) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (c06_aux_one_le_jb z) (by linarith)

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_profile_consequences.  Uniform consequences of the profile bounds for
`f = f̄_{ε,μ}`. -/
theorem c06_profile_consequences (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let f := approximate_solution_family P.p R ε μ
        ContDiff ℝ (⊤ : ℕ∞) f ∧
        -- (1)
        (∀ z : ℝ, |deriv f z| ≤ C₀ ∧ |f z - corner z| ≤ C₀ * jb z ^ (-P.p)) ∧
        -- (2)
        (∀ z : ℝ, 0 ≤ z → |f z| ≤ C₀ * jb z ^ (-P.p) ∧ |deriv f z| ≤ C₀ * jb z ^ (-beta P.p)) ∧
        (∀ z : ℝ, z ≤ 0 → |deriv f z + 1| ≤ C₀ * jb z ^ (-P.p - 1)) ∧
        -- (3)
        (∀ z : ℝ, 1 ≤ z → |f z| ≤ C₀ * z ^ (-P.p) ∧
          ∀ k : ℕ, k ≤ 2 → |iteratedDeriv (k + 1) f z| ≤ C₀ * z ^ (-beta P.p + k / P.p)) := by
  obtain ⟨R₀, hR₀, HB, HS⟩ := c06_aux_eps0_star_spec P δ hδ hδμ
  obtain ⟨C0, hC0, H0⟩ := HB 0
  obtain ⟨C1, hC1, H1⟩ := HB 1
  obtain ⟨C2, hC2, H2⟩ := HB 2
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hb1 : 1 ≤ beta P.p := by
    unfold beta; rw [le_div_iff₀ (by linarith)]; linarith [P.hp_hi]
  have hpinv : 1 / P.p < 4 / 3 := by
    rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith [P.hp_lo]
  refine ⟨R₀, by linarith, fun R hR => ⟨8 * (C0 + C1 + C2) + 1, by linarith, ?_⟩⟩
  intro ε hε μ hμ
  have hε' : ε ∈ Icc (0 : ℝ) (c06_eps0_star P δ) := ⟨hε.1, le_trans hε.2 hε₀s⟩
  set f := approximate_solution_family P.p R ε μ with hf
  have hsm : ContDiff ℝ (⊤ : ℕ∞) f := HS R hR ε hε' μ hμ
  have hdf : Differentiable ℝ f := hsm.differentiable (by simp)
  obtain ⟨H0p, H0n⟩ := H0 R hR ε hε' μ hμ
  obtain ⟨H1p, H1n⟩ := H1 R hR ε hε' μ hμ
  obtain ⟨H2p, -⟩ := H2 R hR ε hε' μ hμ
  have hD1 : ∀ z, iteratedDeriv 1 (fun t => f t + t) z = deriv f z + 1 := fun z => by
    rw [iteratedDeriv_one]
    exact ((hdf z).hasDerivAt.add (hasDerivAt_id z)).deriv
  -- basic bounds
  have bpos_f : ∀ z, 0 ≤ z → |f z| ≤ C0 * jb z ^ (-P.p) := fun z hz => (H0p z hz).1
  have bpos_d : ∀ z, 0 ≤ z → |deriv f z| ≤ C0 * jb z ^ (-beta P.p) := fun z hz => by
    have := (H0p z hz).2
    simpa [iteratedDeriv_one] using this
  have bneg_f : ∀ z, z ≤ 0 → |f z + z| ≤ C0 * jb z ^ (-P.p) := fun z hz => by
    have := H0n z hz
    simpa using this
  have bneg_d : ∀ z, z ≤ 0 → |deriv f z + 1| ≤ C1 * jb z ^ (-P.p - 1) := fun z hz => by
    have := H1n z hz
    rw [hD1] at this
    simpa using this
  have hCs : 0 ≤ C0 + C1 + C2 := by linarith
  refine ⟨hsm, fun z => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩, fun z hz => ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rcases le_total 0 z with hz | hz
    · have := bpos_d z hz
      have := c06_aux_jb_rpow_neg_le_one z (beta P.p) (by linarith)
      nlinarith
    · have h1 := bneg_d z hz
      have h2 := c06_aux_jb_rpow_neg_le_one z (P.p + 1) (by linarith)
      rw [show -P.p - 1 = -(P.p + 1) by ring] at h1
      have h3 : |deriv f z| ≤ |deriv f z + 1| + 1 := by
        have := abs_sub (deriv f z + 1) 1
        simp at this; linarith
      nlinarith
  · have hj := Real.rpow_nonneg (c06_aux_jb_pos z).le (-P.p)
    rcases le_total 0 z with hz | hz
    · have hc : corner z = 0 := by simp [corner]; linarith
      rw [hc, sub_zero]
      have := bpos_f z hz
      nlinarith
    · have hc : corner z = -z := by simp [corner]; linarith
      rw [hc, sub_neg_eq_add]
      have := bneg_f z hz
      nlinarith
  · have hj := Real.rpow_nonneg (c06_aux_jb_pos z).le (-P.p)
    have := bpos_f z hz; nlinarith
  · have hj := Real.rpow_nonneg (c06_aux_jb_pos z).le (-beta P.p)
    have := bpos_d z hz; nlinarith
  · have hj := Real.rpow_nonneg (c06_aux_jb_pos z).le (-P.p - 1)
    have := bneg_d z hz; nlinarith
  · have h1 := bpos_f z (by linarith)
    have h2 := c06_aux_jb_rpow_le z (-P.p) hz (by linarith)
    have hz0 := Real.rpow_nonneg (show (0 : ℝ) ≤ z by linarith) (-P.p)
    nlinarith
  · intro k hk
    have hexp : -beta P.p + (k : ℝ) / P.p ≤ 3 := by
      have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
      have : (k : ℝ) / P.p ≤ 2 * (1 / P.p) := by
        rw [div_le_iff₀ hp0]; field_simp; linarith
      linarith
    have h2 := c06_aux_jb_rpow_le z (-beta P.p + k / P.p) hz hexp
    have hz0 := Real.rpow_nonneg (show (0 : ℝ) ≤ z by linarith) (-beta P.p + k / P.p)
    have hbd : |iteratedDeriv (k + 1) f z| ≤ (C0 + C1 + C2) * jb z ^ (-beta P.p + k / P.p) := by
      have hj := Real.rpow_nonneg (c06_aux_jb_pos z).le (-beta P.p + k / P.p)
      interval_cases k
      · have := (H0p z (by linarith)).2; push_cast at this ⊢; nlinarith
      · have := (H1p z (by linarith)).2; push_cast at this ⊢; nlinarith
      · have := (H2p z (by linarith)).2; push_cast at this ⊢; nlinarith
    nlinarith

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_positive_representation.  Representation of `f` on the positive side,
with `P(y) = -2 Re ∫_y^∞ (Z + c_cubic Z³) dt`. -/
theorem c06_positive_representation (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let f := approximate_solution_family P.p R ε μ
        let Zc : ℝ → ℂ := fun t =>
          fam_Z P.p R ε μ t + (c_cubic P.p ε : ℂ) * fam_Z P.p R ε μ t ^ 3
        let Ptail : ℝ → ℝ := fun y => -2 * (∫ t in Ioi y, Zc t).re
        let g : ℝ → ℝ := fun y => c04_linear_seed_low P.p y + c_plus P.p ε * y ^ (-P.p)
        -- absolute convergence of `P`
        (∀ y : ℝ, R ≤ y → IntegrableOn Zc (Ioi y)) ∧
        -- (1)
        |c_eps P.p ε| + |c_plus P.p ε| ≤ C₁ * ε ∧
        -- (2)
        (∀ y : ℝ, 2 * R ≤ y →
          f y = c04_linear_seed_low P.p y + c_plus P.p ε * y ^ (-P.p) + Ptail y ∧
          deriv f y - 2 * (Zc y).re =
            deriv (c04_linear_seed_low P.p) y - P.p * c_plus P.p ε * y ^ (-P.p - 1)) ∧
        -- (3)
        (∀ y : ℝ, 2 * R ≤ y → ∀ k : ℕ, k ≤ 3 →
          |iteratedDeriv k g y| ≤ C₁ * y ^ (-P.p - k)) ∧
        -- (4)
        (∀ y : ℝ, 2 * R ≤ y → ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (fun y' => deriv f y' - 2 * (Zc y').re) y| ≤
            C₁ * y ^ (-P.p - 1 - j)) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 : P.p < 1 := P.hp_hi
  obtain ⟨Rg, hRg, HG⟩ := c06_aux_eps0_regions P δ hδ hδμ
  obtain ⟨RZ, hRZ, CZ, hCZ, HZ⟩ := c06_aux_eps0_Z P δ hδ hδμ
  obtain ⟨-, -, -, -, -, -, hlow, -⟩ := c04_seed_decomposition P.p P.hp_lo P.hp_hi
  obtain ⟨-, -, -, -, -, ⟨y₀, -, HL⟩, -⟩ := approx_linear_seed P.p P.hp_lo P.hp_hi
  obtain ⟨Cc, hCc, Hc⟩ := c04_aux_c_eps_bound P.p hp0 hp1.le
  choose CL hCL HLb using HL
  set SL : ℝ := ∑ k ∈ Finset.range 4, CL k with hSL
  set M : ℝ := ∑ k ∈ Finset.range 4, |(descPochhammer ℝ k).eval (-P.p)| with hM
  have hCLle : ∀ k, k ≤ 3 → CL k ≤ SL := fun k hk =>
    Finset.single_le_sum (f := CL) (fun i _ => (hCL i).le) (Finset.mem_range.mpr (by omega))
  have hMle : ∀ k, k ≤ 3 → |(descPochhammer ℝ k).eval (-P.p)| ≤ M := fun k hk =>
    Finset.single_le_sum (f := fun k => |(descPochhammer ℝ k).eval (-P.p)|)
      (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
  have hSL0 : 0 ≤ SL := Finset.sum_nonneg (fun i _ => (hCL i).le)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨max Rg RZ, le_trans (by norm_num) (le_trans hRg (le_max_left _ _)), fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (by norm_num) (le_trans hRg (le_trans (le_max_left _ _) hR))
  refine ⟨2 * Cc + SL + Cc * M + 1, by positivity, fun ε hε μ hμ => ?_⟩
  intro f Zc Ptail g
  have hε' : ε ∈ Icc (0 : ℝ) (c06_eps0_star P δ) := ⟨hε.1, le_trans hε.2 hε₀s⟩
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hG1, hG2⟩ := HG R (le_trans (le_max_left _ _) hR) ε hε' μ hμ
  have hRZ' : RZ ≤ R := le_trans (le_max_right _ _) hR
  -- `|c₊| ≤ |c_ε| ≤ Cc ε`
  have hce := Hc ε hε0
  have hcp : |c_plus P.p ε| ≤ |c_eps P.p ε| := by
    unfold c_plus
    rw [abs_div, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < P.p + 1)]
    exact div_le_self (abs_nonneg _) (by linarith)
  have hcp1 : |c_plus P.p ε| ≤ Cc := by
    have : Cc * ε ≤ Cc := by nlinarith
    linarith
  -- (3), proved first
  have hg3 : ∀ y : ℝ, 2 * R ≤ y → ∀ k : ℕ, k ≤ 3 →
      |iteratedDeriv k g y| ≤ (2 * Cc + SL + Cc * M + 1) * y ^ (-P.p - k) := by
    intro y hy k hk
    have hy0 : 0 < y := by linarith
    have hA : ContDiffAt ℝ k (c04_linear_seed_low P.p) y :=
      hlow.contDiffAt.of_le (by exact_mod_cast le_top)
    have hB : ContDiffAt ℝ k (fun t : ℝ => t ^ (-P.p)) y := contDiffAt_rpow_const_of_ne hy0.ne'
    have e1 : iteratedDeriv k g y = iteratedDeriv k (c04_linear_seed_low P.p) y +
        c_plus P.p ε * ((descPochhammer ℝ k).eval (-P.p) * y ^ (-P.p - k)) := by
      show iteratedDeriv k (fun t => c04_linear_seed_low P.p t + c_plus P.p ε * t ^ (-P.p)) y = _
      have e3 : iteratedDeriv k (fun t : ℝ => t ^ (-P.p)) y =
          (descPochhammer ℝ k).eval (-P.p) * y ^ (-P.p - k) := by
        rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const]
      rw [iteratedDeriv_fun_add hA (contDiffAt_const.mul hB), iteratedDeriv_const_mul _ hB, e3]
    have e2 : iteratedDeriv k (c04_linear_seed_low P.p) y =
        iteratedDeriv k (fun t => c04_linear_seed_low P.p t - corner t) y := by
      apply Filter.EventuallyEq.iteratedDeriv_eq
      filter_upwards [Ioi_mem_nhds hy0] with t ht
      have : corner t = 0 := by simp [corner]; exact le_of_lt ht
      rw [this, sub_zero]
    have hb1 := HLb k
    have hb := hb1.2.1 y (by rw [abs_of_pos hy0]; linarith)
    rw [abs_of_pos hy0] at hb
    rw [e1, e2]
    have hyk := Real.rpow_nonneg hy0.le (-P.p - k)
    have t2 : |c_plus P.p ε * ((descPochhammer ℝ k).eval (-P.p) * y ^ (-P.p - k))| ≤
        Cc * M * y ^ (-P.p - k) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hyk]
      have := hMle k hk
      calc |c_plus P.p ε| * (|(descPochhammer ℝ k).eval (-P.p)| * y ^ (-P.p - k))
          ≤ Cc * (M * y ^ (-P.p - k)) := by gcongr
        _ = Cc * M * y ^ (-P.p - k) := by ring
    have t1 : |iteratedDeriv k (fun t => c04_linear_seed_low P.p t - corner t) y| ≤
        SL * y ^ (-P.p - k) := le_trans hb (mul_le_mul_of_nonneg_right (hCLle k hk) hyk)
    have := abs_add_le (iteratedDeriv k (fun t => c04_linear_seed_low P.p t - corner t) y)
      (c_plus P.p ε * ((descPochhammer ℝ k).eval (-P.p) * y ^ (-P.p - k)))
    have : 0 ≤ (2 * Cc + 1) * y ^ (-P.p - k) := by positivity
    nlinarith
  -- `deriv g = f_low' - p c₊ y^{-p-1}` on `(0,∞)`
  have hgd : ∀ y, 0 < y → deriv g y = deriv (c04_linear_seed_low P.p) y -
      P.p * c_plus P.p ε * y ^ (-P.p - 1) := fun y hy => by
    have h1 := (hlow.differentiable (by simp) y).hasDerivAt
    have h2 := (Real.hasDerivAt_rpow_const (p := -P.p) (Or.inl hy.ne')).const_mul (c_plus P.p ε)
    have h3 : HasDerivAt g (deriv (c04_linear_seed_low P.p) y +
        c_plus P.p ε * (-P.p * y ^ (-P.p - 1))) y := h1.add h2
    rw [h3.deriv]; ring
  have hF : ∀ y, 2 * R ≤ y → deriv f y - 2 * (Zc y).re = deriv g y := fun y hy => by
    rw [hgd y (by linarith), hG2 y hy]; ring
  refine ⟨fun y hy => ?_, ?_, fun y hy => ⟨?_, ?_⟩, hg3, fun y hy j hj => ?_⟩
  · -- integrability of `Z + c Z³`
    obtain ⟨hZi, -⟩ := HZ R hRZ' ε hε' μ hμ y hy
    have hbd : ∀ t ∈ Ioi y, ‖fam_Z P.p R ε μ t‖ ≤ CZ := fun t ht => by
      have ht' : y < t := ht
      have h := (HZ R hRZ' ε hε' μ hμ t (by linarith)).2
      have : t ^ (-beta P.p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by unfold beta; have := hp0; rw [neg_nonpos]; positivity)
      nlinarith
    have h3 : IntegrableOn (fun t => fam_Z P.p R ε μ t ^ 3) (Ioi y) := by
      refine Integrable.mono' (hZi.norm.const_mul (CZ ^ 2)) (hZi.aestronglyMeasurable.pow 3) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
      rw [norm_pow]
      have h1 := hbd t ht
      have h0 := norm_nonneg (fam_Z P.p R ε μ t)
      have : ‖fam_Z P.p R ε μ t‖ ^ 2 ≤ CZ ^ 2 := pow_le_pow_left₀ h0 h1 2
      calc ‖fam_Z P.p R ε μ t‖ ^ 3 = ‖fam_Z P.p R ε μ t‖ ^ 2 * ‖fam_Z P.p R ε μ t‖ := by ring
        _ ≤ CZ ^ 2 * ‖fam_Z P.p R ε μ t‖ := mul_le_mul_of_nonneg_right this h0
    exact hZi.add (h3.const_mul _)
  · have : |c_eps P.p ε| + |c_plus P.p ε| ≤ 2 * Cc * ε := by linarith
    have : 0 ≤ (SL + Cc * M + 1) * ε := by positivity
    nlinarith
  · show approximate_solution_family P.p R ε μ y = c04_linear_seed_low P.p y +
      c_plus P.p ε * y ^ (-P.p) +
      -2 * (∫ t in Ioi y, (fam_Z P.p R ε μ t + (c_cubic P.p ε : ℂ) * fam_Z P.p R ε μ t ^ 3)).re
    rw [hG1 y hy]; ring
  · rw [hG2 y hy]; ring
  · -- (4)
    have hy0 : 0 < y := by linarith
    interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      rw [hF y hy]
      have := hg3 y hy 1 (by norm_num)
      simpa [iteratedDeriv_one] using this
    · simp only [iteratedDeriv_one, Nat.cast_one]
      set F : ℝ → ℝ := fun y' => deriv f y' - 2 * (Zc y').re with hFdef
      have hb := hg3 y hy 2 (by norm_num)
      simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hb
      rw [show (-P.p - ((2 : ℕ) : ℝ)) = -P.p - 1 - 1 by push_cast; ring] at hb
      by_cases hd : DifferentiableAt ℝ F y
      · have hgs : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0) :=
          hlow.contDiffOn.add (contDiffOn_const.mul (contDiffOn_id.rpow_const_of_ne
            (fun x hx => (ne_of_gt (show (0 : ℝ) < x from hx)))))
        have hdgs : ContDiffOn ℝ 1 (deriv g) (Ioi 0) :=
          hgs.deriv_of_isOpen isOpen_Ioi (WithTop.coe_le_coe.mpr le_top)
        have hdg : DifferentiableAt ℝ (deriv g) y :=
          (hdgs.contDiffAt (Ioi_mem_nhds hy0)).differentiableAt (by norm_num)
        have h1 : HasDerivWithinAt F (deriv F y) (Ici y) y := hd.hasDerivAt.hasDerivWithinAt
        have h2 : HasDerivWithinAt F (deriv (deriv g) y) (Ici y) y :=
          hdg.hasDerivAt.hasDerivWithinAt.congr (fun x hx => hF x (le_trans hy hx)) (hF y hy)
        rw [(uniqueDiffWithinAt_Ici y).eq_deriv _ h1 h2]
        exact hb
      · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
        positivity

/-! ## Control of `ℰ₆` -/

/-- Blueprint: def:c06_wedge_kernel.  `K_ε(y,t) = (A_ε(-t/(y+t)) - 1)/(y+t)^{1+p}`
(used for `y > 0`, `t ≥ 0`). -/
def c06_wedge_kernel (p ε y t : ℝ) : ℝ :=
  (A_eps p ε (-t / (y + t)) - 1) / (y + t) ^ (1 + p)

/-- Helper: `y`-derivative of `G(-t/(y+t)) (y+t)^e`. -/
theorem c06_aux_Ly (G G' : ℝ → ℝ) (e t y : ℝ)
    (hG : HasDerivAt G (G' (-t / (y + t))) (-t / (y + t))) (hs : 0 < y + t) :
    HasDerivAt (fun y' => G (-t / (y' + t)) * (y' + t) ^ e)
      ((-(-t / (y + t)) * G' (-t / (y + t)) + e * G (-t / (y + t))) * (y + t) ^ (e - 1)) y := by
  have hu : HasDerivAt (fun y' => -t / (y' + t)) ((0 * (y + t) - -t * 1) / (y + t) ^ 2) y :=
    (hasDerivAt_const y (-t)).div ((hasDerivAt_id y).add_const t) hs.ne'
  have hr : HasDerivAt (fun y' => (y' + t) ^ e) (1 * e * (y + t) ^ (e - 1)) y :=
    ((hasDerivAt_id y).add_const t).rpow_const (Or.inl hs.ne')
  refine ((hG.comp y hu).mul hr).congr_deriv ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_sub_one hs.ne']
  field_simp
  ring

/-- Helper: `t`-derivative of `G(-t/(y+t)) (y+t)^e`. -/
theorem c06_aux_Lt (G G' : ℝ → ℝ) (e t y : ℝ)
    (hG : HasDerivAt G (G' (-t / (y + t))) (-t / (y + t))) (hs : 0 < y + t) :
    HasDerivAt (fun t' => G (-t' / (y + t')) * (y + t') ^ e)
      ((-(y / (y + t)) * G' (-t / (y + t)) + e * G (-t / (y + t))) * (y + t) ^ (e - 1)) t := by
  have hu : HasDerivAt (fun t' => -t' / (y + t')) ((-1 * (y + t) - -t * 1) / (y + t) ^ 2) t :=
    ((hasDerivAt_id t).neg).div ((hasDerivAt_id t).const_add y) hs.ne'
  have hr : HasDerivAt (fun t' => (y + t') ^ e) (1 * e * (y + t) ^ (e - 1)) t :=
    ((hasDerivAt_id t).const_add y).rpow_const (Or.inl hs.ne')
  refine ((hG.comp t hu).mul hr).congr_deriv ?_
  simp only [Function.comp_apply]
  rw [Real.rpow_sub_one hs.ne']
  field_simp
  ring

/-- Blueprint: lem:c06_wedge_kernel_bounds.  Smoothness, bounds and the identity
`∂_y K - ∂_t K = A_ε'(-t/(y+t))/(y+t)^{p+2}`. -/
theorem c06_wedge_kernel_bounds (P : parameters) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ ε ∈ Icc (0 : ℝ) 1,
      -- (1)
      (∀ y : ℝ, 0 < y → c06_wedge_kernel P.p ε y 0 = 0) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c06_wedge_kernel P.p ε q.1 q.2) (Ioi 0 ×ˢ Ici 0) ∧
      ∀ y t : ℝ, 0 < y → 0 ≤ t →
        -- (2)
        (∀ k : ℕ, k ≤ 2 →
          |iteratedDeriv k (fun y' => c06_wedge_kernel P.p ε y' t) y| ≤
            C_K * ε * (y + t) ^ (-1 - P.p - k)) ∧
        -- (3)
        deriv (fun y' => c06_wedge_kernel P.p ε y' t) y -
            deriv (fun t' => c06_wedge_kernel P.p ε y t') t =
          deriv (A_eps P.p ε) (-t / (y + t)) / (y + t) ^ (P.p + 2) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  obtain ⟨CA, hCA, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  set α : ℝ := P.p + 1 with hα
  have hα0 : 0 < α := by linarith
  set C₁ : ℝ := α + (1 + P.p) * α / 2 with hC₁
  set C₂ : ℝ := (2 + P.p) * α + CA + (2 + P.p) * C₁ with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₂ + C₁ + α / 2 + 1, by positivity, fun ε hε => ?_⟩
  have hε0 : 0 ≤ ε := hε.1
  obtain ⟨hAc, hAb, hA0, -⟩ := HA ε hε
  set a := A_eps P.p ε with ha
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have da : Differentiable ℝ a := hAc.differentiable (by simp)
  have dda : Differentiable ℝ (deriv a) := by
    simpa using hAc.differentiable_iteratedDeriv 1 htop1
  set e : ℝ := -(1 + P.p) with he
  set F : ℝ → ℝ := fun u => -u * deriv a u + e * (a u - 1) with hF
  set F' : ℝ → ℝ := fun u => -(1 * deriv a u + u * deriv (deriv a) u) + e * deriv a u with hF'
  have hFd : ∀ u, HasDerivAt F (F' u) u := fun u =>
    ((((hasDerivAt_id u).neg).mul (dda u).hasDerivAt).add
      (((da u).hasDerivAt.sub_const 1).const_mul e)).congr_deriv (by simp [hF']; ring)
  -- pointwise bounds for `|u| ≤ 1`
  have bA : ∀ u, |u| ≤ 1 → |a u - 1| ≤ α / 2 * ε := fun u hu => by
    obtain ⟨⟨h0, h1⟩, -⟩ := hAb u
    have : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
    rw [abs_sub_comm, abs_of_nonneg h0]
    calc 1 - a u ≤ (P.p + 1) / 2 * ε * u ^ 2 := h1
      _ ≤ (P.p + 1) / 2 * ε * 1 := by gcongr
      _ = α / 2 * ε := by rw [hα]; ring
  have bA1 : ∀ u, |u| ≤ 1 → |deriv a u| ≤ α * ε := fun u hu => by
    obtain ⟨-, h, -⟩ := hAb u
    calc |deriv a u| ≤ (P.p + 1) * ε * |u| := h
      _ ≤ (P.p + 1) * ε * 1 := by gcongr
      _ = α * ε := by rw [hα]; ring
  have bA2 : ∀ u, |deriv (deriv a) u| ≤ CA * ε := fun u => by
    obtain ⟨-, -, h, -⟩ := hAb u
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
    linarith [abs_nonneg (deriv (deriv (deriv a)) u)]
  have bF : ∀ u, |u| ≤ 1 → |F u| ≤ C₁ * ε := fun u hu => by
    simp only [hF]
    have h1 := bA u hu
    have h2 := bA1 u hu
    have h3 : |-u * deriv a u| ≤ α * ε := by
      rw [abs_mul, abs_neg]
      calc |u| * |deriv a u| ≤ 1 * (α * ε) := mul_le_mul hu h2 (abs_nonneg _) zero_le_one
        _ = α * ε := one_mul _
    have h4 : |e * (a u - 1)| ≤ (1 + P.p) * (α / 2 * ε) := by
      rw [abs_mul, he, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 1 + P.p)]
      exact mul_le_mul_of_nonneg_left h1 (by linarith)
    calc _ ≤ |-u * deriv a u| + |e * (a u - 1)| := abs_add_le _ _
      _ ≤ α * ε + (1 + P.p) * (α / 2 * ε) := add_le_add h3 h4
      _ = C₁ * ε := by rw [hC₁]; ring
  have bF' : ∀ u, |u| ≤ 1 → |F' u| ≤ ((2 + P.p) * α + CA) * ε := fun u hu => by
    simp only [hF']
    have h2 := bA1 u hu
    have h5 := bA2 u
    have h3 : |u * deriv (deriv a) u| ≤ CA * ε := by
      rw [abs_mul]
      calc |u| * |deriv (deriv a) u| ≤ 1 * (CA * ε) := mul_le_mul hu h5 (abs_nonneg _) zero_le_one
        _ = CA * ε := one_mul _
    have h4 : |e * deriv a u| ≤ (1 + P.p) * (α * ε) := by
      rw [abs_mul, he, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 1 + P.p)]
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have h6 := abs_add_le (-(1 * deriv a u + u * deriv (deriv a) u)) (e * deriv a u)
    have h7 := abs_add_le (1 * deriv a u) (u * deriv (deriv a) u)
    rw [abs_neg] at h6
    rw [one_mul] at h7 ⊢
    have : ((2 + P.p) * α + CA) * ε = α * ε + CA * ε + (1 + P.p) * (α * ε) := by rw [hα]; ring
    rw [this]
    rw [one_mul] at h6
    linarith
  have hGd : ∀ u, HasDerivAt (fun u => a u - 1) (deriv a u) u := fun u =>
    (da u).hasDerivAt.sub_const 1
  refine ⟨fun y hy => ?_, ?_, fun y t hy ht => ⟨?_, ?_⟩⟩
  · -- (1) `K(y,0) = 0`
    simp only [c06_wedge_kernel, neg_zero, zero_div, add_zero]
    rw [show A_eps P.p ε 0 = 1 from hA0]; simp
  · -- smoothness
    have hden : ∀ q ∈ (Ioi (0 : ℝ) ×ˢ Ici (0 : ℝ)), q.1 + q.2 ≠ 0 := fun q hq => by
      have h1 : 0 < q.1 := hq.1
      have h2 : 0 ≤ q.2 := hq.2
      linarith
    have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => -q.2 / (q.1 + q.2)) (Ioi 0 ×ˢ Ici 0) :=
      (contDiffOn_snd.neg).div (contDiffOn_fst.add contDiffOn_snd) hden
    have hn : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => a (-q.2 / (q.1 + q.2)) - 1)
        (Ioi 0 ×ˢ Ici 0) := (hAc.comp_contDiffOn hu).sub contDiffOn_const
    have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.1 + q.2) ^ (1 + P.p))
        (Ioi 0 ×ˢ Ici 0) := (contDiffOn_fst.add contDiffOn_snd).rpow_const_of_ne hden
    exact hn.div hd (fun q hq => (Real.rpow_pos_of_pos (by
      have h1 : 0 < q.1 := hq.1
      have h2 : 0 ≤ q.2 := hq.2
      linarith) _).ne')
  · -- (2) bounds
    have hs : 0 < y + t := by linarith
    set u := -t / (y + t) with hu
    have hu1 : |u| ≤ 1 := by
      rw [hu, abs_div, abs_neg, abs_of_nonneg ht, abs_of_pos hs, div_le_one hs]; linarith
    set k : ℝ → ℝ := fun y' => c06_wedge_kernel P.p ε y' t with hk
    set k₀ : ℝ → ℝ := fun y' => (a (-t / (y' + t)) - 1) * (y' + t) ^ e with hk₀
    set k₁ : ℝ → ℝ := fun y' => F (-t / (y' + t)) * (y' + t) ^ (e - 1) with hk₁
    have hopen : IsOpen (Ioi (-t)) := isOpen_Ioi
    have hkk₀ : ∀ y' ∈ Ioi (-t), k y' = k₀ y' := fun y' hy' => by
      have : 0 < y' + t := by have : -t < y' := hy'; linarith
      simp only [hk, hk₀, c06_wedge_kernel, he]
      rw [Real.rpow_neg this.le, div_eq_mul_inv]
    have hD0 : ∀ y' ∈ Ioi (-t), HasDerivAt k (k₁ y') y' := fun y' hy' => by
      have hs' : 0 < y' + t := by have : -t < y' := hy'; linarith
      have := c06_aux_Ly (fun u => a u - 1) (deriv a) e t y' (hGd _) hs'
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hy'] with z hz using hkk₀ z hz
    have hD1 : HasDerivAt k₁ ((-u * F' u + (e - 1) * F u) * (y + t) ^ (e - 1 - 1)) y :=
      c06_aux_Ly F F' (e - 1) t y (hFd _) hs
    have hdk : deriv k =ᶠ[nhds y] k₁ := by
      filter_upwards [hopen.mem_nhds (show y ∈ Ioi (-t) by simp; linarith)] with z hz
      exact (hD0 z hz).deriv
    have hy' : y ∈ Ioi (-t) := by simp; linarith
    intro j hj
    interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      rw [hkk₀ y hy']
      simp only [hk₀, abs_mul]
      rw [abs_of_pos (Real.rpow_pos_of_pos hs _), show (-1 - P.p : ℝ) = e by rw [he]; ring]
      have := bA u hu1
      have hsp := Real.rpow_pos_of_pos hs e
      calc |a u - 1| * (y + t) ^ e ≤ (α / 2 * ε) * (y + t) ^ e :=
            mul_le_mul_of_nonneg_right this hsp.le
        _ ≤ (C₂ + C₁ + α / 2 + 1) * ε * (y + t) ^ e := by
            have : 0 ≤ (C₂ + C₁ + 1) * ε * (y + t) ^ e := by positivity
            nlinarith
    · simp only [iteratedDeriv_one, Nat.cast_one]
      rw [(hD0 y hy').deriv]
      simp only [hk₁, abs_mul]
      rw [abs_of_pos (Real.rpow_pos_of_pos hs _), show (-1 - P.p - 1 : ℝ) = e - 1 by rw [he]; ring]
      have := bF u hu1
      have hsp := Real.rpow_pos_of_pos hs (e - 1)
      calc |F u| * (y + t) ^ (e - 1) ≤ (C₁ * ε) * (y + t) ^ (e - 1) :=
            mul_le_mul_of_nonneg_right this hsp.le
        _ ≤ (C₂ + C₁ + α / 2 + 1) * ε * (y + t) ^ (e - 1) := by
            have : 0 ≤ (C₂ + α / 2 + 1) * ε * (y + t) ^ (e - 1) := by positivity
            nlinarith
    · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
      rw [hdk.deriv_eq, hD1.deriv, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _),
        show (-1 - P.p - ((2 : ℕ) : ℝ) : ℝ) = e - 1 - 1 by rw [he]; push_cast; ring]
      have h1 := bF u hu1
      have h2 := bF' u hu1
      have hsp := Real.rpow_pos_of_pos hs (e - 1 - 1)
      have hb : |-u * F' u + (e - 1) * F u| ≤ C₂ * ε := by
        have h3 : |-u * F' u| ≤ ((2 + P.p) * α + CA) * ε := by
          rw [abs_mul, abs_neg]
          calc |u| * |F' u| ≤ 1 * (((2 + P.p) * α + CA) * ε) :=
                mul_le_mul hu1 h2 (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        have h4 : |(e - 1) * F u| ≤ (2 + P.p) * (C₁ * ε) := by
          rw [abs_mul, show e - 1 = -(2 + P.p) by rw [he]; ring, abs_neg,
            abs_of_pos (by linarith : (0 : ℝ) < 2 + P.p)]
          exact mul_le_mul_of_nonneg_left h1 (by linarith)
        have := abs_add_le (-u * F' u) ((e - 1) * F u)
        have e2 : C₂ * ε = ((2 + P.p) * α + CA) * ε + (2 + P.p) * (C₁ * ε) := by rw [hC₂]; ring
        linarith
      calc |-u * F' u + (e - 1) * F u| * (y + t) ^ (e - 1 - 1)
          ≤ (C₂ * ε) * (y + t) ^ (e - 1 - 1) := mul_le_mul_of_nonneg_right hb hsp.le
        _ ≤ (C₂ + C₁ + α / 2 + 1) * ε * (y + t) ^ (e - 1 - 1) := by
            have : 0 ≤ (C₁ + α / 2 + 1) * ε * (y + t) ^ (e - 1 - 1) := by positivity
            nlinarith
  · -- (3) the identity
    have hs : 0 < y + t := by linarith
    have hy' : y ∈ Ioi (-t) := by simp; linarith
    have hopen : IsOpen (Ioi (-t)) := isOpen_Ioi
    have hdy : HasDerivAt (fun y' => c06_wedge_kernel P.p ε y' t)
        (F (-t / (y + t)) * (y + t) ^ (e - 1)) y := by
      refine (c06_aux_Ly (fun u => a u - 1) (deriv a) e t y (hGd _) hs).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hy'] with z hz
      have : 0 < z + t := by have : -t < z := hz; linarith
      simp only [c06_wedge_kernel, he]
      rw [Real.rpow_neg this.le, div_eq_mul_inv]
    have hopen2 : IsOpen (Ioi (-y)) := isOpen_Ioi
    have ht' : t ∈ Ioi (-y) := by simp; linarith
    have hdt : HasDerivAt (fun t' => c06_wedge_kernel P.p ε y t')
        ((-(y / (y + t)) * deriv a (-t / (y + t)) + e * (a (-t / (y + t)) - 1)) *
          (y + t) ^ (e - 1)) t := by
      refine (c06_aux_Lt (fun u => a u - 1) (deriv a) e t y (hGd _) hs).congr_of_eventuallyEq ?_
      filter_upwards [hopen2.mem_nhds ht'] with z hz
      have : 0 < y + z := by have : -y < z := hz; linarith
      simp only [c06_wedge_kernel, he]
      rw [Real.rpow_neg this.le, div_eq_mul_inv]
    rw [hdy.deriv, hdt.deriv]
    simp only [hF]
    have : e - 1 = -(P.p + 2) := by rw [he]; ring
    rw [this, Real.rpow_neg hs.le]
    have : (y + t) ^ (P.p + 2) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
    field_simp
    ring

/-- Helper: lem:c06_wedge_kernel_mass by the substitution `t = yσ/(1-σ)`. -/
theorem c06_aux_wmass (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε : ℝ) (hε : 0 ≤ ε) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun t => (A_eps p ε (-t / (y + t)) - 1) / (y + t) ^ (1 + p)) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), (A_eps p ε (-t / (y + t)) - 1) / (y + t) ^ (1 + p) =
      y ^ (-p) * ∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * (1 - t) ^ (p - 1) := by
  set s : Set ℝ := Ioo 0 1 with hs
  set g : ℝ → ℝ := fun σ => y * σ / (1 - σ) with hg
  set g' : ℝ → ℝ := fun σ => y / (1 - σ) ^ 2 with hg'
  have hder : ∀ σ ∈ s, HasDerivWithinAt g (g' σ) s σ := by
    intro σ hσ
    have h1 : (1 - σ) ≠ 0 := by linarith [hσ.2]
    have := ((hasDerivAt_id σ).const_mul y).div ((hasDerivAt_id σ).const_sub 1) h1
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [id, hg']; field_simp; ring
  have hinj : InjOn g s := by
    intro a ha b hb hab
    simp only [hg] at hab
    have h1 : (1 - a) ≠ 0 := by linarith [ha.2]
    have h2 : (1 - b) ≠ 0 := by linarith [hb.2]
    field_simp at hab
    nlinarith [hy]
  have himg : g '' s = Ioi 0 := by
    ext t; constructor
    · rintro ⟨σ, hσ, rfl⟩
      simp only [hg, mem_Ioi]
      exact div_pos (mul_pos hy hσ.1) (by linarith [hσ.2])
    · intro ht
      have ht0 : 0 < t := ht
      refine ⟨t / (y + t), ⟨div_pos ht0 (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩, ?_⟩
      simp only [hg]
      have : y + t ≠ 0 := by linarith
      have : y ≠ 0 := hy.ne'
      rw [show 1 - t / (y + t) = y / (y + t) by field_simp; ring]
      field_simp
  set K := fun t : ℝ => (A_eps p ε (-t / (y + t)) - 1) / (y + t) ^ (1 + p) with hK
  set h : ℝ → ℝ := fun σ => y ^ (-p) * ((A_eps p ε σ - 1) * (1 - σ) ^ (p - 1)) with hh
  have hpt : ∀ σ ∈ s, |g' σ| • K (g σ) = h σ := by
    intro σ hσ
    have h1 : 0 < 1 - σ := by linarith [hσ.2]
    simp only [hg', hK, hg, hh, smul_eq_mul]
    have e1 : -(y * σ / (1 - σ)) / (y + y * σ / (1 - σ)) = -σ := by
      field_simp; ring
    have e2 : y + y * σ / (1 - σ) = y / (1 - σ) := by field_simp; ring
    have eA : A_eps p ε (-σ) = A_eps p ε σ := by simp [A_eps]
    rw [e1, e2, eA, abs_of_pos (by positivity), Real.div_rpow hy.le h1.le]
    have r1 : y ^ (1 + p) = y * y ^ p := by rw [Real.rpow_add hy, Real.rpow_one]
    have r2 : (1 - σ) ^ (1 + p) = (1 - σ) ^ 2 * (1 - σ) ^ (p - 1) := by
      rw [show (1 + p) = (2 : ℝ) + (p - 1) by ring, Real.rpow_add h1, Real.rpow_two]
    have r3 : y ^ (-p) = (y ^ p)⁻¹ := Real.rpow_neg hy.le p
    rw [r1, r2, r3]
    have : 0 < y ^ p := Real.rpow_pos_of_pos hy p
    have : 0 < (1 - σ) ^ (p - 1) := Real.rpow_pos_of_pos h1 _
    field_simp
  -- integrability of `h` on `(0,1)`
  have hint_h : IntegrableOn h s := by
    have hb : IntervalIntegrable (fun σ : ℝ => (1 - σ) ^ (p - 1)) volume 0 1 := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := p - 1)
        (by linarith)).comp_sub_left 1
      simpa using this.symm
    have hb' : IntegrableOn (fun σ : ℝ => (1 - σ) ^ (p - 1)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hb
    have hb'' : IntegrableOn (fun σ : ℝ => (1 - σ) ^ (p - 1)) s := hb'.mono_set Ioo_subset_Ioc_self
    have hAc : Continuous (A_eps p ε) := by
      unfold A_eps
      exact (continuous_const.add (continuous_const.mul (continuous_pow 2))).rpow_const
        (fun u => Or.inl (by
          show (1 : ℝ) + ε * u ^ 2 ≠ 0
          exact ne_of_gt (by nlinarith [mul_nonneg hε (sq_nonneg u)])))
    have : IntegrableOn (fun σ => (A_eps p ε σ - 1) * (1 - σ) ^ (p - 1)) s := by
      refine Integrable.mono' hb'' ?_ ?_
      · exact ((hAc.measurable.sub measurable_const).mul
          ((measurable_const.sub measurable_id).pow_const _)).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun σ hσ => ?_)
        have h1 : 0 < 1 - σ := by linarith [hσ.2]
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos h1 _)]
        have := c06_aux_A_sub_one p ε σ hp hε
        have := Real.rpow_pos_of_pos h1 (p - 1)
        nlinarith
    exact this.const_mul _
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hder hinj K
  have hval := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj K
  rw [himg] at hiff hval
  have hcongr : ∫ σ in s, |g' σ| • K (g σ) = ∫ σ in s, h σ :=
    setIntegral_congr_fun measurableSet_Ioo hpt
  refine ⟨hiff.mpr (hint_h.congr_fun (fun σ hσ => (hpt σ hσ).symm) measurableSet_Ioo), ?_⟩
  rw [hval, hcongr, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]

/-- Helper: continuity of `(y,t) ↦ Φ(-t/(y+t)) (y+t)^c` in each variable separately. -/
theorem c06_aux_cont_wedge (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (c : ℝ) :
    (∀ t, ContinuousOn (fun y => Φ (-t / (y + t)) * (y + t) ^ c) (Ioi (-t))) ∧
    (∀ y, ContinuousOn (fun t => Φ (-t / (y + t)) * (y + t) ^ c) (Ioi (-y))) := by
  constructor
  · intro t
    have hne : ∀ y ∈ Ioi (-t), y + t ≠ 0 := fun y hy => by
      have : -t < y := hy; exact ne_of_gt (by linarith)
    have h1 : ContinuousOn (fun y : ℝ => y + t) (Ioi (-t)) := by fun_prop
    exact (hΦ.comp_continuousOn (continuousOn_const.div h1 hne)).mul
      (h1.rpow_const (fun y hy => Or.inl (hne y hy)))
  · intro y
    have hne : ∀ t ∈ Ioi (-y), y + t ≠ 0 := fun t ht => by
      have : -y < t := ht; exact ne_of_gt (by linarith)
    have h1 : ContinuousOn (fun t : ℝ => y + t) (Ioi (-y)) := by fun_prop
    exact (hΦ.comp_continuousOn ((continuousOn_id.neg).div h1 hne)).mul
      (h1.rpow_const (fun t ht => Or.inl (hne t ht)))

/-- Helper: explicit `y`-derivatives `K₁ = ∂_y K_ε`, `K₂ = ∂_y K₁` of the wedge kernel (for
`y + t > 0`), with the continuity properties needed to differentiate under the integral. -/
theorem c06_aux_Kder (P : parameters) (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) :
    ∃ K1 K2 : ℝ → ℝ → ℝ,
      (∀ y t, 0 < y + t → HasDerivAt (fun y' => c06_wedge_kernel P.p ε y' t) (K1 y t) y) ∧
      (∀ y t, 0 < y + t → HasDerivAt (fun y' => K1 y' t) (K2 y t) y) ∧
      (∀ t, ContinuousOn (fun y => K2 y t) (Ioi (-t))) ∧
      (∀ y, ContinuousOn (fun t => K1 y t) (Ioi (-y))) ∧
      (∀ y, ContinuousOn (fun t => K2 y t) (Ioi (-y))) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 P.hp_hi
  obtain ⟨hAc, -, -, -⟩ := HA ε hε
  set a := A_eps P.p ε with ha
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have da : Differentiable ℝ a := hAc.differentiable (by simp)
  have dda : Differentiable ℝ (deriv a) := by
    simpa using hAc.differentiable_iteratedDeriv 1 htop1
  have ca : Continuous a := hAc.continuous
  have cda : Continuous (deriv a) := dda.continuous
  have cdda : Continuous (deriv (deriv a)) := by
    have := hAc.differentiable_iteratedDeriv 2 (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
    simpa [iteratedDeriv_succ] using this.continuous
  set e : ℝ := -(1 + P.p) with he
  set F : ℝ → ℝ := fun u => -u * deriv a u + e * (a u - 1) with hF
  set F' : ℝ → ℝ := fun u => -(1 * deriv a u + u * deriv (deriv a) u) + e * deriv a u with hF'
  have hFd : ∀ u, HasDerivAt F (F' u) u := fun u =>
    ((((hasDerivAt_id u).neg).mul (dda u).hasDerivAt).add
      (((da u).hasDerivAt.sub_const 1).const_mul e)).congr_deriv (by simp [hF']; ring)
  have cF : Continuous F := by simp only [hF]; fun_prop
  have cF' : Continuous F' := by simp only [hF']; fun_prop
  set G2 : ℝ → ℝ := fun u => -u * F' u + (e - 1) * F u with hG2
  have cG2 : Continuous G2 := by simp only [hG2]; fun_prop
  refine ⟨fun y t => F (-t / (y + t)) * (y + t) ^ (e - 1),
    fun y t => G2 (-t / (y + t)) * (y + t) ^ (e - 1 - 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro y t hs
    have hGd : ∀ u, HasDerivAt (fun u => a u - 1) (deriv a u) u := fun u =>
      (da u).hasDerivAt.sub_const 1
    refine (c06_aux_Ly (fun u => a u - 1) (deriv a) e t y (hGd _) hs).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds (show y ∈ Ioi (-t) by simp; linarith)] with z hz
    have : 0 < z + t := by have : -t < z := hz; linarith
    simp only [c06_wedge_kernel, he]
    rw [Real.rpow_neg this.le, div_eq_mul_inv]
  · intro y t hs
    exact c06_aux_Ly F F' (e - 1) t y (hFd _) hs
  · intro t; exact (c06_aux_cont_wedge G2 cG2 (e - 1 - 1)).1 t
  · intro y; exact (c06_aux_cont_wedge F cF (e - 1)).2 y
  · intro y; exact (c06_aux_cont_wedge G2 cG2 (e - 1 - 1)).2 y

/-- Helper: integrability and size of `∫₀^∞ Φ` when `|Φ(t)| ≤ K ⟨t⟩^{-p} (y+t)^{-a}`. -/
theorem c06_aux_int_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Φ : ℝ → ℝ) (Kc a y : ℝ)
    (ha : 1 - p < a) (hy : 0 < y) (hKc : 0 ≤ Kc)
    (hmeas : AEStronglyMeasurable Φ (volume.restrict (Ioi 0)))
    (hb : ∀ t, 0 < t → |Φ t| ≤ Kc * (jb t ^ (-p) * (y + t) ^ (-a))) :
    IntegrableOn Φ (Ioi 0) ∧
      |∫ t in Ioi (0 : ℝ), Φ t| ≤ Kc * ((1 / (1 - p) + 1 / (a + p - 1)) * y ^ (1 - p - a)) := by
  obtain ⟨hi, hv⟩ := c06_aux_tail4 p hp hp1 a y ha hy
  have hg : IntegrableOn (fun t => Kc * (jb t ^ (-p) * (y + t) ^ (-a))) (Ioi 0) := hi.const_mul Kc
  have hae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ‖Φ t‖ ≤ Kc * (jb t ^ (-p) * (y + t) ^ (-a)) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => by
      rw [Real.norm_eq_abs]; exact hb t ht)
  refine ⟨Integrable.mono' hg hmeas hae, ?_⟩
  have := norm_integral_le_of_norm_le hg hae
  rw [Real.norm_eq_abs, integral_const_mul] at this
  exact le_trans this (mul_le_mul_of_nonneg_left hv hKc)

/-- Blueprint: lem:c06_wedge_kernel_mass.  `c_α ∫₀^∞ K_ε(y,t) dt = c_ε y^{-p}`. -/
theorem c06_wedge_kernel_mass (P : parameters) (ε : ℝ) (hε : 0 ≤ ε) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun t => c06_wedge_kernel P.p ε y t) (Ioi 0) ∧
    calpha P.p * ∫ t in Ioi (0 : ℝ), c06_wedge_kernel P.p ε y t = c_eps P.p ε * y ^ (-P.p) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨hi, hv⟩ := c06_aux_wmass P.p hp0 P.hp_hi ε hε y hy
  refine ⟨hi, ?_⟩
  show calpha P.p * ∫ t in Ioi (0 : ℝ), (A_eps P.p ε (-t / (y + t)) - 1) / (y + t) ^ (1 + P.p) = _
  rw [hv, c_eps]
  ring

/-! ### Helpers for lem:c06_wedge_first_variation -/

/-- Helper: reflection `t ↦ -t` maps `(0,∞)` onto `(-∞,0)`. -/
theorem c06_aux_wfv_neg (g : ℝ → ℝ) :
    (IntegrableOn g (Iio 0) → IntegrableOn (fun t => g (-t)) (Ioi 0)) ∧
    ∫ t in Ioi (0 : ℝ), g (-t) = ∫ z in Iio (0 : ℝ), g z := by
  have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume := Measure.measurePreserving_neg volume
  have hme : MeasurableEmbedding (Neg.neg : ℝ → ℝ) := (Homeomorph.neg ℝ).measurableEmbedding
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Iio 0 = Ioi 0 := by ext z; simp
  refine ⟨fun h => ?_, ?_⟩
  · have := (hmp.integrableOn_comp_preimage hme (f := g) (s := Iio 0)).mpr h
    rwa [hpre] at this
  · rw [integral_comp_neg_Ioi, neg_zero, integral_Iic_eq_integral_Iio]

/-- Helper: `t ↦ (c+t)^{-a}` is integrable on `(0,∞)` for `a > 1`, `c > 0`. -/
theorem c06_aux_wfv_tail (a c : ℝ) (ha : 1 < a) (hc : 0 < c) :
    IntegrableOn (fun t => (c + t) ^ (-a)) (Ioi 0) := by
  have := (c06_aux_wfv_neg (fun z => (c - z) ^ (-a))).1 (c06_aux_tail1 a c ha hc).1
  simpa [sub_neg_eq_add] using this

/-- Helper: a function with `|f s| ≤ C |s|^3` has derivative `0` at `0`. -/
theorem c06_aux_wfv_cubic (f : ℝ → ℝ) (C : ℝ) (hf : ∀ s, |f s| ≤ C * |s| ^ 3) :
    HasDerivAt f 0 0 := by
  have h0 : f 0 = 0 := by
    have := hf 0; simpa using this
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, h0, sub_zero, smul_zero]
  have hO : f =O[𝓝 0] fun s : ℝ => s ^ 3 :=
    Asymptotics.IsBigO.of_bound C (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]; exact hf s)
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

/-- Helper: `|h'(y) - h'(z)| / |y-z|^{1+p}` is integrable when `h` is Lipschitz and `C²` near `y`. -/
theorem c06_aux_wfv_Phi (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (h : ℝ → ℝ) (L : ℝ≥0)
    (hL : LipschitzWith L h) (hC2 : ContDiffOn ℝ 2 h (Ioi 0)) (y : ℝ) (hy : 0 < y) :
    Integrable (fun z => |deriv h y - deriv h z| / |y - z| ^ (p + 1)) := by
  have hdh : ∀ x, |deriv h x| ≤ L := fun x => by
    have := norm_deriv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) hL
    rwa [Real.norm_eq_abs] at this
  have hC1 : ContDiffOn ℝ 1 (deriv h) (Ioi 0) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioi).mp
      (by rw [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]; exact hC2)).2.2
  set r : ℝ := y / 2 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨K2, hK2⟩ := (hC1.mono (show Icc (y / 2) (3 * y / 2) ⊆ Ioi 0 from fun x hx => by
    simp only [mem_Icc, mem_Ioi] at hx ⊢; linarith [hx.1])).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  set kK : ℝ := (K2 : ℝ) with hkK
  set lL : ℝ := (L : ℝ) with hlL
  set Ψ : ℝ → ℝ := fun u => if |u| ≤ r then kK * |u| ^ (-p) else (2 * lL) * |u| ^ (-(p + 1))
    with hΨ
  have hΨm : Measurable Ψ := by
    refine Measurable.ite (measurableSet_le measurable_id.abs measurable_const) ?_ ?_
    · exact measurable_const.mul ((measurable_id.abs).pow_const (-p))
    · exact measurable_const.mul ((measurable_id.abs).pow_const (-(p + 1)))
  have hΨ0 : ∀ u, 0 ≤ Ψ u := fun u => by
    simp only [hΨ]; split_ifs <;> positivity
  have hΨeven : ∀ u, Ψ (-u) = Ψ u := fun u => by simp [hΨ, abs_neg]
  have hIoi : IntegrableOn Ψ (Ioi 0) := by
    have := (c06_aux_split_int p (-(p + 1)) kK (2 * lL) r hp1 (by linarith) hr0).1
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have : |t| = t := abs_of_pos ht
    simp only [hΨ, this]
  have hIio : IntegrableOn Ψ (Iio 0) := by
    have hmp : MeasurePreserving (Neg.neg : ℝ → ℝ) volume volume :=
      Measure.measurePreserving_neg volume
    have hme : MeasurableEmbedding (Neg.neg : ℝ → ℝ) := (Homeomorph.neg ℝ).measurableEmbedding
    have h1 := (hmp.integrableOn_comp_preimage hme (f := Ψ) (s := Ioi 0)).mpr hIoi
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Ioi 0 = Iio 0 := by ext z; simp
    rw [hpre] at h1
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Iio
    exact hΨeven t
  have hΨi : Integrable Ψ := by
    rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ))]
    exact hIio.union ((integrableOn_Ici_iff_integrableOn_Ioi (f := Ψ)).mpr hIoi)
  have hΨs : Integrable (fun z => Ψ (y - z)) := hΨi.comp_sub_left y
  refine hΨs.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (((measurable_const.sub (measurable_deriv h)).abs).div
      ((measurable_const.sub measurable_id).abs.pow_const _)).aestronglyMeasurable
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hyz : y = z
  · subst hyz; simp only [sub_self, abs_zero, zero_div]; exact hΨ0 _
  have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr hyz)
  have hsplit : |y - z| ^ (p + 1) = |y - z| ^ p * |y - z| := Real.rpow_add_one hpos.ne' p
  simp only [hΨ]
  split_ifs with hle
  · have hz : z ∈ Icc (y / 2) (3 * y / 2) := by
      rw [abs_le] at hle; constructor <;> linarith [hle.1, hle.2]
    have hy' : y ∈ Icc (y / 2) (3 * y / 2) := by constructor <;> linarith
    have hlip := hK2.dist_le_mul y hy' z hz
    rw [Real.dist_eq, Real.dist_eq] at hlip
    rw [div_le_iff₀ (by positivity), hsplit, Real.rpow_neg hpos.le]
    calc |deriv h y - deriv h z| ≤ K2 * |y - z| := hlip
      _ = kK * (|y - z| ^ p)⁻¹ * (|y - z| ^ p * |y - z|) := by
          rw [hkK]; field_simp
  · rw [div_le_iff₀ (by positivity), Real.rpow_neg hpos.le, mul_assoc,
      inv_mul_cancel₀ (by positivity), mul_one]
    have := abs_sub (deriv h y) (deriv h z)
    linarith [hdh y, hdh z]

/-- Helper: integration by parts on `(0,∞)` for a `C¹` kernel vanishing at `0` and at `∞` against a
bounded Lipschitz function (whose derivative exists only a.e.). -/
theorem c06_aux_wfv_ibp (k g : ℝ → ℝ) (hk : ContDiffOn ℝ 1 k (Ici 0)) (hk0 : k 0 = 0)
    (hkT : Tendsto k atTop (𝓝 0)) (Lg : ℝ≥0) (hg : LipschitzWith Lg g) (Mg : ℝ)
    (hgb : ∀ t, |g t| ≤ Mg)
    (h1 : IntegrableOn (fun t => k t * deriv g t) (Ioi 0))
    (h2 : IntegrableOn (fun t => deriv k t * g t) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), deriv k t * g t = -∫ t in Ioi (0 : ℝ), k t * deriv g t := by
  have hI : ∀ T : ℝ, 0 ≤ T → ∫ x in (0 : ℝ)..T, k x * deriv g x =
      k T * g T - k 0 * g 0 - ∫ x in (0 : ℝ)..T, deriv k x * g x := by
    intro T hT
    have hsub : uIcc 0 T ⊆ Ici (0 : ℝ) := by
      rw [uIcc_of_le hT]; exact Icc_subset_Ici_self
    exact AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
      ((hk.mono hsub).absolutelyContinuousOnInterval)
      (hg.lipschitzOnWith.absolutelyContinuousOnInterval)
  have l1 := intervalIntegral_tendsto_integral_Ioi 0 h1 tendsto_id
  have l2 := intervalIntegral_tendsto_integral_Ioi 0 h2 tendsto_id
  have l3 : Tendsto (fun T => k T * g T) atTop (𝓝 0) := by
    have hM : Tendsto (fun T => |k T| * Mg) atTop (𝓝 0) := by
      simpa using (hkT.abs).mul_const Mg
    refine squeeze_zero_norm (fun T => ?_) hM
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb T) (abs_nonneg _)
  have l4 : Tendsto (fun T => k T * g T - k 0 * g 0 - ∫ x in (0 : ℝ)..T, deriv k x * g x) atTop
      (𝓝 (0 - k 0 * g 0 - ∫ t in Ioi (0 : ℝ), deriv k t * g t)) :=
    (l3.sub_const _).sub l2
  rw [hk0, zero_mul, sub_zero, zero_sub] at l4
  have := tendsto_nhds_unique l1 (l4.congr' (by
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [id, hI T hT, hk0, zero_mul, sub_zero]))
  linarith

/-- Helper: integrability on `(0,∞)` from a bound `c (y+t)^{-a}`, `a > 1`. -/
theorem c06_aux_wfv_intb (F : ℝ → ℝ) (c a y : ℝ) (ha : 1 < a) (hy : 0 < y)
    (hF : AEStronglyMeasurable F (volume.restrict (Ioi 0)))
    (hb : ∀ t, 0 < t → |F t| ≤ c * (y + t) ^ (-a)) : IntegrableOn F (Ioi 0) :=
  Integrable.mono' ((c06_aux_wfv_tail a y ha hy).const_mul c) hF
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => by
      rw [Real.norm_eq_abs]; exact hb t ht))

/-- Helper for lem:c06_wedge_first_variation: the `t`-side identities (F1), (F2) and the
derivative of `y ↦ ∫₀^∞ K_ε(y,t)(h(y)-h(-t)) dt`. -/
theorem c06_aux_wfv_t (P : parameters) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h : ℝ → ℝ) (M : ℝ)
    (hM : ∀ x, |h x| ≤ M) (L : ℝ≥0) (hL : LipschitzWith L h) (hC2 : ContDiffOn ℝ 2 h (Ioi 0))
    (y : ℝ) (hy : 0 < y) :
    res_DQW P.p ε h y =
        calpha P.p * (∫ t in Ioi (0 : ℝ), c06_wedge_kernel P.p ε y t * (deriv h y - deriv h (-t))) +
        calpha P.p * (∫ t in Ioi (0 : ℝ),
          deriv (A_eps P.p ε) (-t / (y + t)) / (y + t) ^ (P.p + 2) * (h y - h (-t))) ∧
    res_DQW P.p ε h y =
        calpha P.p * ∫ t in Ioi (0 : ℝ), (c06_wedge_kernel P.p ε y t * deriv h y +
          deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (h y - h (-t))) ∧
    HasDerivAt (fun y' => ∫ t in Ioi (0 : ℝ), c06_wedge_kernel P.p ε y' t * (h y' - h (-t)))
      (∫ t in Ioi (0 : ℝ), (c06_wedge_kernel P.p ε y t * deriv h y +
          deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (h y - h (-t)))) y := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε, hε1⟩
  obtain ⟨CK, hCK, HK⟩ := c06_wedge_kernel_bounds P
  obtain ⟨hK0, hKs, HKb⟩ := HK ε hεI
  obtain ⟨K1, K2, hK1, -, -, cK1t, -⟩ := c06_aux_Kder P ε hεI
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  obtain ⟨hAc, hAb, -, -⟩ := HA ε hεI
  clear HK HA
  set K : ℝ → ℝ → ℝ := fun y t => c06_wedge_kernel P.p ε y t with hKdef
  have hdh : ∀ x, |deriv h x| ≤ L := fun x => by
    have := norm_deriv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) hL
    rwa [Real.norm_eq_abs] at this
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hhc : Continuous h := hL.continuous
  have hdm : Measurable (deriv h) := measurable_deriv h
  have hAcont : Continuous (A_eps P.p ε) := hAc.continuous
  have hdAcont : Continuous (deriv (A_eps P.p ε)) := hAc.continuous_deriv (by simp)
  have hdiffh : ∀ x, 0 < x → DifferentiableAt ℝ h x := fun x hx =>
    (hC2.differentiableOn (by norm_num) x hx).differentiableAt (Ioi_mem_nhds hx)
  have hKm : ∀ y, Measurable (fun t => K y t) := fun y => by
    simp only [hKdef, c06_wedge_kernel]
    exact ((hAcont.measurable.comp (measurable_neg.div (measurable_const.add measurable_id))).sub
      measurable_const).div ((measurable_const.add measurable_id).pow_const _)
  have bK : ∀ y t, 0 < y → 0 ≤ t → |K y t| ≤ CK * ε * (y + t) ^ (-(1 + P.p)) := by
    intro y t hy ht
    have := (HKb y t hy ht).1 0 (by norm_num)
    rw [iteratedDeriv_zero] at this
    rw [show (-(1 + P.p) : ℝ) = -1 - P.p - ((0 : ℕ) : ℝ) by push_cast; ring]; exact this
  have hdK : ∀ y t, 0 < y + t → deriv (fun y' => c06_wedge_kernel P.p ε y' t) y = K1 y t :=
    fun y t h => (hK1 y t h).deriv
  have bK1 : ∀ y t, 0 < y → 0 ≤ t → |K1 y t| ≤ CK * ε * (y + t) ^ (-(2 + P.p)) := by
    intro y t hy ht
    have := (HKb y t hy ht).1 1 (by norm_num)
    rw [iteratedDeriv_one, hdK y t (by linarith)] at this
    rw [show (-(2 + P.p) : ℝ) = -1 - P.p - ((1 : ℕ) : ℝ) by push_cast; ring]; exact this
  have hKe : 0 ≤ CK * ε := by positivity
  -- the function `g(t) = h(y) - h(-t)`
  set g : ℝ → ℝ := fun t => h y - h (-t) with hg
  have hgc : Continuous g := continuous_const.sub (hhc.comp continuous_neg)
  have hgm : Measurable g := hgc.measurable
  have hgb : ∀ t, |g t| ≤ 2 * M := fun t => by
    have := abs_sub (h y) (h (-t)); linarith [hM y, hM (-t)]
  have hgL : LipschitzWith L g := LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, Real.dist_eq]
    have := hL.dist_le_mul (-b) (-a)
    rw [Real.dist_eq, Real.dist_eq] at this
    calc |g a - g b| = |h (-b) - h (-a)| := by simp only [hg]; ring_nf
      _ ≤ L * |-b - -a| := this
      _ = L * |a - b| := by rw [show -b - -a = -(b - a) by ring, abs_neg, abs_sub_comm]
  have hdg : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), deriv g t = deriv h (-t) := by
    have h1 : ∀ᵐ x, DifferentiableAt ℝ h x := hL.ae_differentiableAt
    have h2 : ∀ᵐ t, DifferentiableAt ℝ h (-t) :=
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae h1
    refine ae_restrict_of_ae ?_
    filter_upwards [h2] with t ht
    have := (ht.hasDerivAt.comp t (hasDerivAt_neg t)).const_sub (h y)
    show deriv (fun x => h y - (h ∘ Neg.neg) x) t = _
    rw [this.deriv]; ring
  -- integrability of the pieces
  have iT1 : IntegrableOn (fun t => K y t * (deriv h y - deriv h (-t))) (Ioi 0) := by
    refine c06_aux_wfv_intb _ (CK * ε * (2 * L)) (1 + P.p) y (by linarith) hy
      (((hKm y).mul (measurable_const.sub (hdm.comp measurable_neg))).aestronglyMeasurable)
      (fun t ht => ?_)
    rw [abs_mul]
    have h2 : |deriv h y - deriv h (-t)| ≤ 2 * L := by
      have := abs_sub (deriv h y) (deriv h (-t)); linarith [hdh y, hdh (-t)]
    calc |K y t| * |deriv h y - deriv h (-t)| ≤ (CK * ε * (y + t) ^ (-(1 + P.p))) * (2 * L) :=
          mul_le_mul (bK y t hy ht.le) h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have iT2 : IntegrableOn (fun t => deriv (A_eps P.p ε) (-t / (y + t)) / (y + t) ^ (P.p + 2) *
      (h y - h (-t))) (Ioi 0) := by
    refine c06_aux_wfv_intb _ ((P.p + 1) * (2 * M)) (P.p + 2) y (by linarith) hy
      ((((hdAcont.measurable.comp (measurable_neg.div (measurable_const.add measurable_id))).div
        ((measurable_const.add measurable_id).pow_const _)).mul hgm).aestronglyMeasurable)
      (fun t ht => ?_)
    have hyt : 0 < y + t := by linarith [ht]
    have hu : |-t / (y + t)| ≤ 1 := by
      rw [abs_div, abs_neg, abs_of_pos ht, abs_of_pos hyt, div_le_one hyt]; linarith
    have hA' : |deriv (A_eps P.p ε) (-t / (y + t))| ≤ P.p + 1 := by
      have := (hAb (-t / (y + t))).2.1
      calc _ ≤ (P.p + 1) * ε * |-t / (y + t)| := this
        _ ≤ (P.p + 1) * 1 * 1 := by gcongr
        _ = _ := by ring
    rw [abs_mul, abs_div, abs_of_pos (Real.rpow_pos_of_pos hyt _), div_eq_mul_inv,
      ← Real.rpow_neg hyt.le]
    calc |deriv (A_eps P.p ε) (-t / (y + t))| * (y + t) ^ (-(P.p + 2)) * |h y - h (-t)|
        ≤ (P.p + 1) * (y + t) ^ (-(P.p + 2)) * (2 * M) := by
          gcongr
          · exact hgb t
      _ = _ := by ring
  have iKc : IntegrableOn (fun t => K y t * deriv h y) (Ioi 0) :=
    (c06_wedge_kernel_mass P ε hε y hy).1.mul_const _
  have iKn : IntegrableOn (fun t => K y t * deriv h (-t)) (Ioi 0) := by
    have := iKc.sub iT1
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; ring
  have iK1 : IntegrableOn (fun t => deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * g t)
      (Ioi 0) := by
    refine c06_aux_wfv_intb _ (CK * ε * (2 * M)) (2 + P.p) y (by linarith) hy
      ((((cK1t y).mono (show Ioi (0 : ℝ) ⊆ Ioi (-y) from fun t ht => by
        simp only [mem_Ioi] at ht ⊢; linarith)).mul hgc.continuousOn).aestronglyMeasurable
        measurableSet_Ioi |>.congr ?_) (fun t ht => ?_)
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => by
        simp only [mem_Ioi] at ht; simp only [Pi.mul_apply]; rw [hdK y t (by linarith)])
    · rw [hdK y t (by linarith [ht]), abs_mul]
      calc |K1 y t| * |g t| ≤ (CK * ε * (y + t) ^ (-(2 + P.p))) * (2 * M) :=
            mul_le_mul (bK1 y t hy ht.le) (hgb t) (abs_nonneg _) (by positivity)
        _ = _ := by ring
  -- (F1)
  have hF1 : res_DQW P.p ε h y =
      calpha P.p * (∫ t in Ioi (0 : ℝ), K y t * (deriv h y - deriv h (-t))) +
      calpha P.p * (∫ t in Ioi (0 : ℝ),
        deriv (A_eps P.p ε) (-t / (y + t)) / (y + t) ^ (P.p + 2) * (h y - h (-t))) := by
    unfold res_DQW
    rw [← (c06_aux_wfv_neg _).2, ← mul_add, ← integral_add iT1 iT2]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    have hyt : 0 < y + t := by linarith
    have hne : y ≠ -t := by intro h'; linarith
    simp only [c01_secant, if_neg hne, sub_neg_eq_add, hKdef, c06_wedge_kernel]
    have e2 : (y + t) ^ (P.p + 2) = (y + t) ^ (P.p + 1) * (y + t) := by
      rw [show P.p + 2 = (P.p + 1) + 1 by ring, Real.rpow_add_one hyt.ne']
    have e1 : (y + t) ^ (1 + P.p) = (y + t) ^ (P.p + 1) := by rw [add_comm 1 P.p]
    rw [e2, e1]
    have : 0 < (y + t) ^ (P.p + 1) := Real.rpow_pos_of_pos hyt _
    field_simp
  -- (F2): the identity `∂_y K - ∂_t K = A'/(y+t)^{p+2}` and integration by parts in `t`
  have hid : ∀ t, 0 < t → deriv (A_eps P.p ε) (-t / (y + t)) / (y + t) ^ (P.p + 2) * (h y - h (-t)) =
      deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * g t -
        deriv (fun t' => c06_wedge_kernel P.p ε y t') t * g t := fun t ht => by
    rw [← (HKb y t hy ht.le).2]; simp only [hg]; ring
  have iKt : IntegrableOn (fun t => deriv (fun t' => c06_wedge_kernel P.p ε y t') t * g t)
      (Ioi 0) := by
    refine (iK1.sub iT2).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; rw [hid t ht]; ring
  have iKdg : IntegrableOn (fun t => K y t * deriv g t) (Ioi 0) := by
    refine iKn.congr ?_
    filter_upwards [hdg] with t ht
    rw [ht]
  have hkC : ContDiffOn ℝ 1 (fun t => c06_wedge_kernel P.p ε y t) (Ici 0) := by
    have hin : ContDiffOn ℝ 1 (fun t : ℝ => ((y, t) : ℝ × ℝ)) (Ici 0) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h1 := (hKs.of_le (show ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)).comp hin (fun t ht => ⟨hy, ht⟩)
    exact h1
  have hkT : Tendsto (fun t => c06_wedge_kernel P.p ε y t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => (y + T) ^ (-(1 + P.p))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp (tendsto_atTop_add_const_left _ y tendsto_id)
    have h2 := h1.const_mul (CK * ε)
    rw [mul_zero] at h2
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [Real.norm_eq_abs]; exact bK y T hy hT
  have hibp := c06_aux_wfv_ibp (fun t => c06_wedge_kernel P.p ε y t) g hkC (hK0 y hy) hkT L hgL
    (2 * M) hgb iKdg iKt
  have hdgI : ∫ t in Ioi (0 : ℝ), K y t * deriv g t = ∫ t in Ioi (0 : ℝ), K y t * deriv h (-t) :=
    integral_congr_ae (by filter_upwards [hdg] with t ht; rw [ht])
  have hF2 : res_DQW P.p ε h y =
      calpha P.p * ∫ t in Ioi (0 : ℝ), (c06_wedge_kernel P.p ε y t * deriv h y +
        deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (h y - h (-t))) := by
    rw [hF1, integral_add iKc iK1]
    have e1 : ∫ t in Ioi (0 : ℝ), K y t * (deriv h y - deriv h (-t)) =
        (∫ t in Ioi (0 : ℝ), K y t * deriv h y) - ∫ t in Ioi (0 : ℝ), K y t * deriv h (-t) := by
      rw [← integral_sub iKc iKn]; congr 1; funext t; ring
    have e2 : ∫ t in Ioi (0 : ℝ), deriv (A_eps P.p ε) (-t / (y + t)) / (y + t) ^ (P.p + 2) *
        (h y - h (-t)) = (∫ t in Ioi (0 : ℝ), deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * g t) -
          ∫ t in Ioi (0 : ℝ), deriv (fun t' => c06_wedge_kernel P.p ε y t') t * g t := by
      rw [← integral_sub iK1 iKt]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => hid t ht)
    rw [e1, e2, hibp, hdgI]
    simp only [hKdef, hg]
    ring
  refine ⟨hF1, hF2, ?_⟩
  -- differentiation under the integral sign
  have hball : ∀ x ∈ Metric.ball y (y / 2), y / 2 ≤ x := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx; linarith
  have hy2 : 0 < y / 2 := by linarith
  have hFm : ∀ x, AEStronglyMeasurable (fun t => K x t * (h x - h (-t))) (volume.restrict (Ioi 0)) :=
    fun x => ((hKm x).mul (measurable_const.sub (hhc.measurable.comp measurable_neg))).aestronglyMeasurable
  have hFi : Integrable (fun t => K y t * (h y - h (-t))) (volume.restrict (Ioi 0)) := by
    refine c06_aux_wfv_intb _ (CK * ε * (2 * M)) (1 + P.p) y (by linarith) hy (hFm y)
      (fun t ht => ?_)
    rw [abs_mul]
    calc |K y t| * |h y - h (-t)| ≤ (CK * ε * (y + t) ^ (-(1 + P.p))) * (2 * M) :=
          mul_le_mul (bK y t hy ht.le) (hgb t) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hF'm : AEStronglyMeasurable (fun t => K1 y t * (h y - h (-t)) + K y t * deriv h y)
      (volume.restrict (Ioi 0)) := by
    refine AEStronglyMeasurable.add ?_ (((hKm y).mul_const _).aestronglyMeasurable)
    exact (((cK1t y).mono (show Ioi (0 : ℝ) ⊆ Ioi (-y) from fun t ht => by
        simp only [mem_Ioi] at ht ⊢; linarith)).mul hgc.continuousOn).aestronglyMeasurable
        measurableSet_Ioi
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x t => K x t * (h x - h (-t)))
    (F' := fun x t => K1 x t * (h x - h (-t)) + K x t * deriv h x) (x₀ := y)
    (bound := fun t => CK * ε * (2 * M) * (y / 2 + t) ^ (-(2 + P.p)) +
      CK * ε * L * (y / 2 + t) ^ (-(1 + P.p)))
    (s := Metric.ball y (y / 2)) (Metric.ball_mem_nhds _ hy2)
    (Eventually.of_forall hFm) hFi hF'm
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht x hx => by
      have ht0 : 0 < t := ht
      have hx2 := hball x hx
      have hx0 : 0 < x := by linarith
      rw [Real.norm_eq_abs]
      have m1 : (x + t) ^ (-(2 + P.p)) ≤ (y / 2 + t) ^ (-(2 + P.p)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      have m2 : (x + t) ^ (-(1 + P.p)) ≤ (y / 2 + t) ^ (-(1 + P.p)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      have hgx : |h x - h (-t)| ≤ 2 * M := by
        have := abs_sub (h x) (h (-t)); linarith [hM x, hM (-t)]
      calc |K1 x t * (h x - h (-t)) + K x t * deriv h x|
          ≤ |K1 x t| * |h x - h (-t)| + |K x t| * |deriv h x| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ (CK * ε * (y / 2 + t) ^ (-(2 + P.p))) * (2 * M) +
            (CK * ε * (y / 2 + t) ^ (-(1 + P.p))) * L := by
            gcongr
            · exact (bK1 x t hx0 ht0.le).trans (mul_le_mul_of_nonneg_left m1 hKe)
            · exact (bK x t hx0 ht0.le).trans (mul_le_mul_of_nonneg_left m2 hKe)
            · exact hdh x
        _ = _ := by ring))
    (((c06_aux_wfv_tail (2 + P.p) (y / 2) (by linarith) hy2).const_mul _).add
      ((c06_aux_wfv_tail (1 + P.p) (y / 2) (by linarith) hy2).const_mul _))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht x hx => by
      have ht0 : 0 < t := ht
      have hx0 : 0 < x := by linarith [hball x hx]
      exact (hK1 x t (by linarith)).mul ((hdiffh x hx0).hasDerivAt.sub_const (h (-t)))))
  refine H.2.congr_deriv ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := ht
  simp only [hKdef]
  rw [hdK y t (by linarith)]
  ring
/-- Helper: `W(z) + s h(z)` has derivative `-1 + s h'(z)` at `z < 0` and `s h'(z)` at `z > 0`
when `h` is differentiable at `z`. -/
theorem c06_aux_wfv_corner_deriv (h : ℝ → ℝ) (s z : ℝ) (hd : DifferentiableAt ℝ h z) :
    (z < 0 → deriv (fun x => corner x + s * h x) z = -1 + s * deriv h z) ∧
    (0 < z → deriv (fun x => corner x + s * h x) z = s * deriv h z) := by
  constructor
  · intro hz
    have hc : HasDerivAt corner (-1) z := by
      refine (hasDerivAt_neg z).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hz] with x hx
      simp only [corner]; exact max_eq_left (by linarith [mem_Iio.mp hx])
    exact (HasDerivAt.add (f := corner) (g := fun x => s * h x) hc
      (hd.hasDerivAt.const_mul s)).deriv
  · intro hz
    have hc : HasDerivAt corner 0 z := by
      refine (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hz] with x hx
      simp only [corner]; exact max_eq_right (by linarith [mem_Ioi.mp hx])
    have e := (HasDerivAt.add (f := corner) (g := fun x => s * h x) hc
      (hd.hasDerivAt.const_mul s)).deriv
    rw [zero_add] at e; exact e


/-- Helper for lem:c06_wedge_first_variation: the Gateaux derivative of `s ↦ 𝒬_ε(W+sh)(y)`. -/
theorem c06_aux_wfv_gateaux (P : parameters) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h : ℝ → ℝ)
    (M : ℝ) (hM : ∀ x, |h x| ≤ M) (L : ℝ≥0) (hL : LipschitzWith L h)
    (hC2 : ContDiffOn ℝ 2 h (Ioi 0)) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℝ => c01_Q_eps P.p ε (fun z => corner z + s * h z) y)
      (res_DQW P.p ε h y) 0 := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε, hε1⟩
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  obtain ⟨hAc, hAb, -, -⟩ := HA ε hεI
  clear HA
  set a := A_eps P.p ε with ha
  set da := deriv (A_eps P.p ε) with hda
  have hda' : ∀ u, HasDerivAt a (da u) u := fun u =>
    ((hAc.differentiable (by simp)) u).hasDerivAt
  have hac : Continuous a := hAc.continuous
  have hdac : Continuous da := hAc.continuous_deriv (by simp)
  have hdh : ∀ x, |deriv h x| ≤ L := fun x => by
    have := norm_deriv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) hL
    rwa [Real.norm_eq_abs] at this
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hhc : Continuous h := hL.continuous
  have hdm : Measurable (deriv h) := measurable_deriv h
  have hdiffy : DifferentiableAt ℝ h y :=
    (hC2.differentiableOn (by norm_num) y hy).differentiableAt (Ioi_mem_nhds hy)
  have hD : ∀ᵐ x, DifferentiableAt ℝ h x := hL.ae_differentiableAt
  set dh := deriv h with hdhdef
  set S : ℝ → ℝ := fun z => (h y - h z) / (y - z) with hS
  have hSb : ∀ z, |S z| ≤ L := fun z => by
    by_cases hz : y = z
    · simp [hS, hz]
    have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr hz)
    simp only [hS, abs_div]
    rw [div_le_iff₀ hpos]
    have := hL.dist_le_mul y z
    rwa [Real.dist_eq, Real.dist_eq] at this
  have hSm : Measurable S := (measurable_const.sub hhc.measurable).div
    (measurable_const.sub measurable_id)
  set GN : ℝ → ℝ → ℝ := fun s z => (1 + s * (dh y - dh z)) / (y - z) ^ (P.p + 1) *
    (a (z / (y - z) + s * S z) - 1) with hGN
  set GP : ℝ → ℝ → ℝ := fun s z => (s * dh y - s * dh z) / |y - z| ^ (P.p + 1) *
    (a (s * S z) - 1) with hGP
  set F : ℝ → ℝ → ℝ := fun s z => (deriv (fun x => corner x + s * h x) y -
    deriv (fun x => corner x + s * h x) z) / |y - z| ^ (P.p + 1) *
    (a (c01_secant (fun x => corner x + s * h x) y z) - 1) with hF
  have hcy : corner y = 0 := by simp only [corner]; exact max_eq_right (by linarith)
  have hdy : ∀ s, deriv (fun x => corner x + s * h x) y = s * dh y := fun s =>
    (c06_aux_wfv_corner_deriv h s y hdiffy).2 hy
  have eqN : ∀ s z, z < 0 → DifferentiableAt ℝ h z → F s z = GN s z := by
    intro s z hz hdz
    have hyz : 0 < y - z := by linarith
    have hne : y ≠ z := by intro e; linarith
    have hcz : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
    simp only [hF, hGN, hdy s, (c06_aux_wfv_corner_deriv h s z hdz).1 hz, c01_secant, if_neg hne,
      hcy, hcz, abs_of_pos hyz]
    congr 2
    · ring
    · simp only [hS]; field_simp; ring
  have eqP : ∀ s z, 0 < z → z ≠ y → DifferentiableAt ℝ h z → F s z = GP s z := by
    intro s z hz hzy hdz
    have hne : y ≠ z := fun e => hzy e.symm
    have hcz : corner z = 0 := by simp only [corner]; exact max_eq_right (by linarith)
    have hyz : y - z ≠ 0 := sub_ne_zero.mpr hne
    simp only [hF, hGP, hdy s, (c06_aux_wfv_corner_deriv h s z hdz).2 hz, c01_secant, if_neg hne,
      hcy, hcz]
    congr 2
    simp only [hS]; field_simp; ring
  -- integrability
  have hdhb2 : ∀ z, |dh y - dh z| ≤ 2 * L := fun z => by
    have := abs_sub (dh y) (dh z); linarith [hdh y, hdh z]
  have hGNm : ∀ s, Measurable (GN s) := fun s => by
    simp only [hGN]
    exact ((measurable_const.add (measurable_const.mul (measurable_const.sub hdm))).div
      ((measurable_const.sub measurable_id).pow_const _)).mul
      ((hac.measurable.comp ((measurable_id.div (measurable_const.sub measurable_id)).add
        (measurable_const.mul hSm))).sub measurable_const)
  have iGN : ∀ s, IntegrableOn (GN s) (Iio 0) := fun s => by
    refine Integrable.mono' (((c06_aux_tail1 (P.p + 1) y (by linarith) hy).1).const_mul
      (1 + |s| * (2 * L))) (hGNm s).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
    have hz0 : z < 0 := hz
    have hyz : 0 < y - z := by linarith
    rw [Real.norm_eq_abs]
    simp only [hGN]
    rw [abs_mul, abs_div, abs_of_pos (Real.rpow_pos_of_pos hyz _), div_eq_mul_inv,
      ← Real.rpow_neg hyz.le]
    have h1 : |1 + s * (dh y - dh z)| ≤ 1 + |s| * (2 * L) := by
      calc _ ≤ |(1 : ℝ)| + |s * (dh y - dh z)| := abs_add_le _ _
        _ ≤ _ := by rw [abs_one, abs_mul]; gcongr; exact hdhb2 z
    have h2 := c06_aux_A_sub_one P.p ε (z / (y - z) + s * S z) hp0 hε
    calc |1 + s * (dh y - dh z)| * (y - z) ^ (-(P.p + 1)) * |a (z / (y - z) + s * S z) - 1|
        ≤ (1 + |s| * (2 * L)) * (y - z) ^ (-(P.p + 1)) * 1 := by gcongr
      _ = _ := by ring
  set Φ : ℝ → ℝ := fun z => |dh y - dh z| / |y - z| ^ (P.p + 1) with hΦ
  have iΦ : Integrable Φ := c06_aux_wfv_Phi P.p hp0 hp1 h L hL hC2 y hy
  set C3 : ℝ := (P.p + 1) / 2 * (L : ℝ) ^ 2 with hC3
  have hC30 : 0 ≤ C3 := by positivity
  have bGP : ∀ s z, |GP s z| ≤ C3 * |s| ^ 3 * Φ z := fun s z => by
    have hA := (hAb (s * S z)).1
    have hu : (s * S z) ^ 2 ≤ s ^ 2 * (L : ℝ) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by
        have := hSb z
        calc S z ^ 2 = |S z| ^ 2 := (sq_abs _).symm
          _ ≤ (L : ℝ) ^ 2 := by gcongr) (sq_nonneg s)
    have hAa : |a (s * S z) - 1| ≤ (P.p + 1) / 2 * (s ^ 2 * (L : ℝ) ^ 2) := by
      rw [abs_sub_comm, abs_of_nonneg hA.1]
      calc _ ≤ (P.p + 1) / 2 * ε * (s * S z) ^ 2 := hA.2
        _ ≤ (P.p + 1) / 2 * 1 * (s ^ 2 * (L : ℝ) ^ 2) := by gcongr
        _ = _ := by ring
    have hΦ0 : 0 ≤ Φ z := by simp only [hΦ]; positivity
    have e : GP s z = s * Φ z * (a (s * S z) - 1) * (if 0 ≤ dh y - dh z then 1 else -1) := by
      simp only [hGP, hΦ]
      split_ifs with hs
      · rw [abs_of_nonneg hs]; ring
      · rw [abs_of_neg (not_le.mp hs)]; ring
    rw [e, abs_mul, abs_mul, abs_mul, abs_of_nonneg hΦ0]
    have hsg : |(if 0 ≤ dh y - dh z then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
    rw [hsg, mul_one]
    calc |s| * Φ z * |a (s * S z) - 1| ≤ |s| * Φ z * ((P.p + 1) / 2 * (s ^ 2 * (L : ℝ) ^ 2)) := by
          gcongr
      _ = C3 * |s| ^ 3 * Φ z := by
          rw [hC3, show s ^ 2 = |s| ^ 2 from (sq_abs s).symm]; ring
  have hGPm : ∀ s, Measurable (GP s) := fun s => by
    simp only [hGP]
    exact (((measurable_const.sub (measurable_const.mul hdm))).div
      ((measurable_const.sub measurable_id).abs.pow_const _)).mul
      ((hac.measurable.comp (measurable_const.mul hSm)).sub measurable_const)
  have iGP : ∀ s, IntegrableOn (GP s) (Ioi 0) := fun s =>
    Integrable.mono' ((iΦ.const_mul (C3 * |s| ^ 3)).integrableOn) (hGPm s).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact bGP s z)
  -- `𝒬_ε(W+sh)(y) = c_α (N(s) + P(s))`
  have aeN : ∀ s, F s =ᵐ[volume.restrict (Iio 0)] GN s := fun s => by
    filter_upwards [ae_restrict_mem measurableSet_Iio, ae_restrict_of_ae hD] with z hz hdz
    exact eqN s z hz hdz
  have aeP : ∀ s, F s =ᵐ[volume.restrict (Ioi 0)] GP s := fun s => by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hD,
      ae_restrict_of_ae (Measure.ae_ne volume y)] with z hz hdz hzy
    exact eqP s z hz hzy hdz
  have hQ : ∀ s, c01_Q_eps P.p ε (fun z => corner z + s * h z) y =
      calpha P.p * ((∫ z in Iio (0 : ℝ), GN s z) + ∫ z in Ioi (0 : ℝ), GP s z) := by
    intro s
    have i1 : IntegrableOn (F s) (Iio 0) := (iGN s).congr_fun_ae (aeN s).symm
    have i2 : IntegrableOn (F s) (Ici 0) :=
      (integrableOn_Ici_iff_integrableOn_Ioi (f := F s)).mpr ((iGP s).congr_fun_ae (aeP s).symm)
    have hsplit : ∫ z, F s z = (∫ z in Iio (0 : ℝ), F s z) + ∫ z in Ici (0 : ℝ), F s z := by
      rw [← setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
        simp only [mem_Iio, mem_Ici] at hx hx'; linarith) measurableSet_Ici i1 i2,
        Iio_union_Ici, setIntegral_univ]
    have e1 : c01_Q_eps P.p ε (fun z => corner z + s * h z) y = calpha P.p * ∫ z, F s z := rfl
    rw [e1, hsplit, integral_Ici_eq_integral_Ioi, integral_congr_ae (aeN s),
      integral_congr_ae (aeP s)]
  -- the `(0,∞)` part is `O(|s|³)`
  have hPd : HasDerivAt (fun s => ∫ z in Ioi (0 : ℝ), GP s z) 0 0 := by
    refine c06_aux_wfv_cubic _ (C3 * ∫ z, Φ z) (fun s => ?_)
    have := norm_integral_le_of_norm_le ((iΦ.const_mul (C3 * |s| ^ 3)).integrableOn
      (s := Ioi (0 : ℝ))) (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact bGP s z)
    rw [Real.norm_eq_abs, integral_const_mul] at this
    have hle : ∫ z in Ioi (0 : ℝ), Φ z ≤ ∫ z, Φ z :=
      setIntegral_le_integral iΦ (ae_of_all _ fun z => by simp only [hΦ]; positivity)
    calc _ ≤ C3 * |s| ^ 3 * ∫ z in Ioi (0 : ℝ), Φ z := this
      _ ≤ C3 * |s| ^ 3 * ∫ z, Φ z := by gcongr
      _ = _ := by ring
  -- the `(-∞,0)` part: differentiation under the integral sign
  set GN' : ℝ → ℝ → ℝ := fun s z => (dh y - dh z) / (y - z) ^ (P.p + 1) *
      (a (z / (y - z) + s * S z) - 1) +
    (1 + s * (dh y - dh z)) / (y - z) ^ (P.p + 1) * (da (z / (y - z) + s * S z) * S z) with hGN'
  set B : ℝ := 2 * L + (1 + 2 * L) * ((P.p + 1) * (1 + L)) * L with hB
  have hB0 : 0 ≤ B := by positivity
  have hGN'm : Measurable (GN' 0) := by
    simp only [hGN']
    exact ((((measurable_const.sub hdm)).div
      ((measurable_const.sub measurable_id).pow_const _)).mul
      ((hac.measurable.comp ((measurable_id.div (measurable_const.sub measurable_id)).add
        (measurable_const.mul hSm))).sub measurable_const)).add
      (((measurable_const.add (measurable_const.mul (measurable_const.sub hdm))).div
      ((measurable_const.sub measurable_id).pow_const _)).mul
      ((hdac.measurable.comp ((measurable_id.div (measurable_const.sub measurable_id)).add
        (measurable_const.mul hSm))).mul hSm))
  have HN := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Iio 0))
    (F := GN) (F' := GN') (x₀ := 0) (bound := fun z => B * (y - z) ^ (-(P.p + 1)))
    (s := Metric.ball 0 1) (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun s => (hGNm s).aestronglyMeasurable) (iGN 0)
    hGN'm.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz s hs => by
      have hz0 : z < 0 := hz
      have hyz : 0 < y - z := by linarith
      have hs1 : |s| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      rw [Real.norm_eq_abs]
      simp only [hGN']
      have hu : |z / (y - z) + s * S z| ≤ 1 + L := by
        calc _ ≤ |z / (y - z)| + |s * S z| := abs_add_le _ _
          _ ≤ 1 + 1 * L := by
            gcongr
            · rw [abs_div, abs_of_pos hyz, div_le_one hyz, abs_of_neg hz0]; linarith
            · rw [abs_mul]; exact mul_le_mul hs1.le (hSb z) (abs_nonneg _) zero_le_one
          _ = _ := by ring
      have hda1 : |da (z / (y - z) + s * S z)| ≤ (P.p + 1) * (1 + L) := by
        calc _ ≤ (P.p + 1) * ε * |z / (y - z) + s * S z| := (hAb _).2.1
          _ ≤ (P.p + 1) * 1 * (1 + L) := by gcongr
          _ = _ := by ring
      have h1s : |1 + s * (dh y - dh z)| ≤ 1 + 2 * L := by
        calc _ ≤ |(1 : ℝ)| + |s * (dh y - dh z)| := abs_add_le _ _
          _ ≤ 1 + 1 * (2 * L) := by
            rw [abs_one, abs_mul]; gcongr
            · exact hdhb2 z
          _ = _ := by ring
      have hk : (y - z) ^ (P.p + 1) > 0 := Real.rpow_pos_of_pos hyz _
      rw [show (dh y - dh z) / (y - z) ^ (P.p + 1) = (dh y - dh z) * (y - z) ^ (-(P.p + 1)) by
          rw [Real.rpow_neg hyz.le, div_eq_mul_inv],
        show (1 + s * (dh y - dh z)) / (y - z) ^ (P.p + 1) =
          (1 + s * (dh y - dh z)) * (y - z) ^ (-(P.p + 1)) by
          rw [Real.rpow_neg hyz.le, div_eq_mul_inv]]
      have hA1 := c06_aux_A_sub_one P.p ε (z / (y - z) + s * S z) hp0 hε
      have hpos : 0 < (y - z) ^ (-(P.p + 1)) := Real.rpow_pos_of_pos hyz _
      calc _ ≤ |(dh y - dh z) * (y - z) ^ (-(P.p + 1)) * (a (z / (y - z) + s * S z) - 1)| +
            |(1 + s * (dh y - dh z)) * (y - z) ^ (-(P.p + 1)) *
              (da (z / (y - z) + s * S z) * S z)| := abs_add_le _ _
        _ = |dh y - dh z| * (y - z) ^ (-(P.p + 1)) * |a (z / (y - z) + s * S z) - 1| +
            |1 + s * (dh y - dh z)| * (y - z) ^ (-(P.p + 1)) *
              (|da (z / (y - z) + s * S z)| * |S z|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hpos]
        _ ≤ (2 * L) * (y - z) ^ (-(P.p + 1)) * 1 +
            (1 + 2 * L) * (y - z) ^ (-(P.p + 1)) * (((P.p + 1) * (1 + L)) * L) := by
            gcongr
            · exact hdhb2 z
            · exact hSb z
        _ = _ := by simp only [hB]; ring))
    ((c06_aux_tail1 (P.p + 1) y (by linarith) hy).1.const_mul B)
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz s _ => by
      simp only [hGN, hGN']
      have h1 : HasDerivAt (fun s => (1 + s * (dh y - dh z)) / (y - z) ^ (P.p + 1))
          ((dh y - dh z) / (y - z) ^ (P.p + 1)) s := by
        have := (((hasDerivAt_id s).mul_const (dh y - dh z)).const_add 1).div_const
          ((y - z) ^ (P.p + 1))
        simpa using this
      have h2 : HasDerivAt (fun s => a (z / (y - z) + s * S z) - 1)
          (da (z / (y - z) + s * S z) * S z) s := by
        have hin : HasDerivAt (fun s => z / (y - z) + s * S z) (S z) s := by
          simpa using ((hasDerivAt_id s).mul_const (S z)).const_add (z / (y - z))
        have hc := HasDerivAt.comp (h₂ := a) (h := fun s => z / (y - z) + s * S z) s
          (hda' (z / (y - z) + s * S z)) hin
        exact hc.sub_const 1
      exact h1.mul h2))
  have hval : res_DQW P.p ε h y = calpha P.p * ∫ z in Iio (0 : ℝ), GN' 0 z := by
    unfold res_DQW
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio (fun z hz => ?_)
    have hz0 : z < 0 := hz
    have hne : y ≠ z := by intro e; linarith
    simp only [hGN', c01_secant, if_neg hne, hS, zero_mul, add_zero, one_mul, zero_add]
    ring
  rw [hval]
  have := ((HN.2.add hPd).const_mul (calpha P.p))
  rw [add_zero] at this
  exact this.congr_of_eventuallyEq (Eventually.of_forall fun s => hQ s)

/-- Blueprint: lem:c06_wedge_first_variation.  `D𝒬_ε(W)[h](y)` (`res_DQW`) is the Gateaux
derivative of `s ↦ 𝒬_ε(W+sh)(y)` at `s = 0`, and has the forms (F1), (F2). -/
-- In (F1) the two integrals are parenthesized separately, so that (F1) is the sum of two
-- integrals, as in the first-variation formula of the paper.
theorem c06_wedge_first_variation (P : parameters) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h : ℝ → ℝ) (hbdd : ∃ M, ∀ x, |h x| ≤ M) (hLip : ∃ L, LipschitzWith L h)
    (hC2 : ContDiffOn ℝ 2 h (Ioi 0)) :
    (∀ y : ℝ, 0 < y →
      -- Gateaux derivative (the `z`-form is the definition of `res_DQW`)
      HasDerivAt (fun s : ℝ => c01_Q_eps P.p ε (fun z => corner z + s * h z) y)
        (res_DQW P.p ε h y) 0 ∧
      -- (F1)
      res_DQW P.p ε h y =
        calpha P.p * (∫ t in Ioi (0 : ℝ), c06_wedge_kernel P.p ε y t * (deriv h y - deriv h (-t))) +
        calpha P.p * (∫ t in Ioi (0 : ℝ),
          deriv (A_eps P.p ε) (-t / (y + t)) / (y + t) ^ (P.p + 2) * (h y - h (-t))) ∧
      -- (F2)
      res_DQW P.p ε h y =
        calpha P.p * ∫ t in Ioi (0 : ℝ), (c06_wedge_kernel P.p ε y t * deriv h y +
          deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (h y - h (-t))) ∧
      res_DQW P.p ε h y =
        calpha P.p * deriv (fun y' => ∫ t in Ioi (0 : ℝ),
          c06_wedge_kernel P.p ε y' t * (h y' - h (-t))) y) ∧
    DifferentiableOn ℝ (fun y' => ∫ t in Ioi (0 : ℝ),
      c06_wedge_kernel P.p ε y' t * (h y' - h (-t))) (Ioi 0) := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨L, hL⟩ := hLip
  refine ⟨fun y hy => ?_, fun y hy =>
    (c06_aux_wfv_t P ε hε hε1 h M hM L hL hC2 y hy).2.2.differentiableAt.differentiableWithinAt⟩
  obtain ⟨hF1, hF2, hd⟩ := c06_aux_wfv_t P ε hε hε1 h M hM L hL hC2 y hy
  exact ⟨c06_aux_wfv_gateaux P ε hε hε1 h M hM L hL hC2 y hy, hF1, hF2, by rw [hF2, hd.deriv]⟩

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E6_exact_decomposition.  Exact decomposition of `ℰ₆` for `y ≥ 2R`. -/
theorem c06_E6_exact_decomposition (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y : ℝ, 2 * R ≤ y →
        let f := approximate_solution_family P.p R ε μ
        IntegrableOn (fun t => deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (f (-t) - t))
          (Ioi 0) ∧
        residual_decomposition_E6 P.p R ε μ y =
          c_eps P.p ε * y ^ (-P.p) *
              (deriv (c04_linear_seed_low P.p) y - P.p * c_plus P.p ε * y ^ (-P.p - 1)) -
            P.p * c_eps P.p ε * y ^ (-P.p - 1) * f y -
            calpha P.p * ∫ t in Ioi (0 : ℝ),
              deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (f (-t) - t) := by
  obtain ⟨R₃, hR₃, HP⟩ := c06_positive_representation P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₄, hR₄, HC⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CK, hCK, HK⟩ := c06_wedge_kernel_bounds P
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 : P.p < 1 := P.hp_hi
  refine ⟨max R₃ R₄, le_trans hR₃ (le_max_left _ _), fun R hR ε hε μ hμ y hy => ?_⟩
  obtain ⟨C₁, -, HP'⟩ := HP R (le_trans (le_max_left _ _) hR)
  obtain ⟨C₀, hC₀, HC'⟩ := HC R (le_trans (le_max_right _ _) hR)
  have hR1 : 1 ≤ R := le_trans hR₃ (le_trans (le_max_left _ _) hR)
  have hy0 : 0 < y := by linarith
  intro f
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, le_trans hε.2 hε₀1⟩
  obtain ⟨hfs, hc1, -, -, -⟩ := HC' ε hε μ hμ
  obtain ⟨-, -, hrep, -, -⟩ := HP' ε hε μ hμ
  obtain ⟨-, -, HKb⟩ := HK ε hε1
  obtain ⟨K1, K2, hK1, hK2, -, cK1t, -⟩ := c06_aux_Kder P ε hε1
  clear HC HK HC' HP HP'
  have hdf : Differentiable ℝ f := hfs.differentiable (by simp)
  set w : ℝ → ℝ := fun t => f (-t) - t with hw
  have cw : Continuous w := (hfs.continuous.comp continuous_neg).sub continuous_id
  have bw : ∀ t, 0 ≤ t → |w t| ≤ C₀ * jb t ^ (-P.p) := fun t ht => by
    have h := (hc1 (-t)).2
    have hc : corner (-t) = t := by simp only [corner, neg_neg]; exact max_eq_left ht
    have hj : jb (-t) = jb t := by simp [jb]
    rw [hc, hj] at h; exact h
  have hdK : ∀ y t, 0 < y + t → deriv (fun y' => c06_wedge_kernel P.p ε y' t) y = K1 y t :=
    fun y t h => (hK1 y t h).deriv
  have bK0 : ∀ y t, 0 < y → 0 ≤ t → |c06_wedge_kernel P.p ε y t| ≤ CK * ε * (y + t) ^ (-(1 + P.p)) := by
    intro y t hy ht
    have := (HKb y t hy ht).1 0 (by norm_num)
    rw [iteratedDeriv_zero] at this
    rw [show (-(1 + P.p) : ℝ) = -1 - P.p - ((0 : ℕ) : ℝ) by push_cast; ring]; exact this
  have bK1 : ∀ y t, 0 < y → 0 ≤ t → |K1 y t| ≤ CK * ε * (y + t) ^ (-(2 + P.p)) := by
    intro y t hy ht
    have := (HKb y t hy ht).1 1 (by norm_num)
    rw [iteratedDeriv_one, hdK y t (by linarith)] at this
    rw [show (-(2 + P.p) : ℝ) = -1 - P.p - ((1 : ℕ) : ℝ) by push_cast; ring]; exact this
  have hKc : 0 ≤ CK * ε * C₀ := by positivity
  have mA : Measurable (A_eps P.p ε) := (c04_aux_A_cont P.p ε hε0).measurable
  have mK : ∀ y, Measurable (fun t => c06_wedge_kernel P.p ε y t) := fun y => by
    unfold c06_wedge_kernel; fun_prop
  have meas0 : ∀ y, AEStronglyMeasurable (fun t => c06_wedge_kernel P.p ε y t * w t)
      (volume.restrict (Ioi 0)) := fun y =>
    ((mK y).mul cw.measurable).aestronglyMeasurable
  have meas1 : ∀ y, 0 < y → AEStronglyMeasurable (fun t => K1 y t * w t) (volume.restrict (Ioi 0)) :=
    fun y hy => (((cK1t y).mono (show Ioi (0 : ℝ) ⊆ Ioi (-y) from fun t ht => by
        simp only [mem_Ioi] at ht ⊢; linarith)).mul
      cw.continuousOn).aestronglyMeasurable measurableSet_Ioi
  have dom0 : ∀ y y₁, 0 < y₁ → y₁ ≤ y → ∀ t, 0 < t →
      |c06_wedge_kernel P.p ε y t * w t| ≤ CK * ε * C₀ * (jb t ^ (-P.p) * (y₁ + t) ^ (-(1 + P.p))) := by
    intro y y₁ hy₁ hyy t ht
    rw [abs_mul]
    have h1 := bK0 y t (by linarith) ht.le
    have h2 := bw t ht.le
    have hm : (y + t) ^ (-(1 + P.p)) ≤ (y₁ + t) ^ (-(1 + P.p)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    calc _ ≤ (CK * ε * (y₁ + t) ^ (-(1 + P.p))) * (C₀ * jb t ^ (-P.p)) :=
          mul_le_mul (le_trans h1 (by gcongr)) h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have dom1 : ∀ y y₁, 0 < y₁ → y₁ ≤ y → ∀ t, 0 < t →
      |K1 y t * w t| ≤ CK * ε * C₀ * (jb t ^ (-P.p) * (y₁ + t) ^ (-(2 + P.p))) := by
    intro y y₁ hy₁ hyy t ht
    rw [abs_mul]
    have h1 := bK1 y t (by linarith) ht.le
    have h2 := bw t ht.le
    have hm : (y + t) ^ (-(2 + P.p)) ≤ (y₁ + t) ^ (-(2 + P.p)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    calc _ ≤ (CK * ε * (y₁ + t) ^ (-(2 + P.p))) * (C₀ * jb t ^ (-P.p)) :=
          mul_le_mul (le_trans h1 (by gcongr)) h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hint1 : IntegrableOn (fun t => K1 y t * w t) (Ioi 0) :=
    (c06_aux_int_bound P.p hp0 hp1 _ _ (2 + P.p) y (by linarith) hy0 hKc (meas1 y hy0)
      (dom1 y y hy0 le_rfl)).1
  have hcongr : ∫ t in Ioi (0 : ℝ), deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (f (-t) - t) =
      ∫ t in Ioi (0 : ℝ), K1 y t * w t := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have : 0 < t := ht
    simp only [hw]
    rw [hdK y t (by linarith)]
  refine ⟨hint1.congr_fun (fun t ht => by
    have : 0 < t := ht; simp only [hw]; rw [hdK y t (by linarith)]) measurableSet_Ioi, ?_⟩
  -- the first variation, in divergence form
  set h : ℝ → ℝ := fun z => f z - corner z with hh
  have hbdd : ∃ M, ∀ x, |h x| ≤ M := ⟨C₀, fun x => by
    have := (hc1 x).2
    have := Real.rpow_le_one_of_one_le_of_nonpos (c06_aux_one_le_jb x) (by linarith : -P.p ≤ 0)
    nlinarith⟩
  have hLip : ∃ L, LipschitzWith L h := by
    refine ⟨Real.toNNReal (C₀ + 1), LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    rw [Real.coe_toNNReal _ (by linarith), Real.dist_eq, Real.dist_eq]
    have h1 := c06_aux_lip f hdf C₀ (fun x => (hc1 x).1) a b
    have h2 : |corner a - corner b| ≤ |a - b| := by
      have := abs_max_sub_max_le_abs (-a) (-b) 0
      simp only [corner]
      calc _ ≤ |-a - -b| := this
        _ = |a - b| := by rw [show -a - -b = -(a - b) by ring, abs_neg]
    have : h a - h b = (f a - f b) - (corner a - corner b) := by simp only [hh]; ring
    rw [this]
    have := abs_sub (f a - f b) (corner a - corner b)
    have : 0 ≤ |a - b| := abs_nonneg _
    nlinarith
  have hC2 : ContDiffOn ℝ 2 h (Ioi 0) :=
    (show ContDiff ℝ 2 f by simpa using contDiff_infty.mp hfs 2).contDiffOn.congr (fun x hx => by
      have : (0 : ℝ) < x := hx
      simp only [hh, corner]; rw [max_eq_right (by linarith), sub_zero])
  obtain ⟨hFV, hGd⟩ := c06_wedge_first_variation P ε hε0 hε1.2 h hbdd hLip hC2
  obtain ⟨-, -, -, hF2⟩ := hFV y hy0
  set G : ℝ → ℝ := fun y' => ∫ t in Ioi (0 : ℝ), c06_wedge_kernel P.p ε y' t * (h y' - h (-t))
    with hG
  set J0 : ℝ → ℝ := fun y' => ∫ t in Ioi (0 : ℝ), c06_wedge_kernel P.p ε y' t * w t with hJ0
  -- `c_α G = c_ε y^{-p} f - c_α J₀` on `(0,∞)`
  have hGeq : ∀ y', 0 < y' → calpha P.p * G y' =
      c_eps P.p ε * y' ^ (-P.p) * f y' - calpha P.p * J0 y' := by
    intro y' hy'
    obtain ⟨hKi, hmass⟩ := c06_wedge_kernel_mass P ε hε0 y' hy'
    have hKw : IntegrableOn (fun t => c06_wedge_kernel P.p ε y' t * w t) (Ioi 0) :=
      (c06_aux_int_bound P.p hp0 hp1 _ _ (1 + P.p) y' (by linarith) hy' hKc (meas0 y')
        (dom0 y' y' hy' le_rfl)).1
    have e1 : G y' = ∫ t in Ioi (0 : ℝ), (f y' * c06_wedge_kernel P.p ε y' t -
        c06_wedge_kernel P.p ε y' t * w t) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have : (0 : ℝ) < t := ht
      have c1 : corner y' = 0 := by simp only [corner]; exact max_eq_right (by linarith)
      have c2 : corner (-t) = t := by simp only [corner, neg_neg]; exact max_eq_left this.le
      simp only [hh, hw, c1, c2]; ring
    rw [e1, integral_sub (hKi.const_mul _) hKw, integral_const_mul, mul_sub, ← hmass]
    simp only [hJ0]; ring
  -- derivative of `J₀`
  have hJd : HasDerivAt J0 (∫ t in Ioi (0 : ℝ), K1 y t * w t) y := by
    have hball : ∀ x ∈ Metric.ball y (y / 2), y / 2 ≤ x := fun x hx => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx; linarith
    have hint0 : Integrable (fun t => c06_wedge_kernel P.p ε y t * w t) (volume.restrict (Ioi 0)) :=
      (c06_aux_int_bound P.p hp0 hp1 _ _ (1 + P.p) y (by linarith) hy0 hKc (meas0 y)
        (dom0 y y hy0 le_rfl)).1
    have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := fun y' t => c06_wedge_kernel P.p ε y' t * w t) (F' := fun y' t => K1 y' t * w t)
      (x₀ := y)
      (bound := fun t => CK * ε * C₀ * (jb t ^ (-P.p) * (y / 2 + t) ^ (-(2 + P.p))))
      (s := Metric.ball y (y / 2)) (Metric.ball_mem_nhds _ (by linarith))
      (Eventually.of_forall meas0) hint0 (meas1 y hy0)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht x hx => by
        rw [Real.norm_eq_abs]
        exact dom1 x (y / 2) (by linarith) (hball x hx) t ht))
      ((c06_aux_tail4 P.p hp0 hp1 (2 + P.p) (y / 2) (by linarith) (by linarith)).1.const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht x hx =>
        (hK1 x t (by have := hball x hx; have : (0 : ℝ) < t := ht; linarith)).mul_const (w t)))
    exact H.2
  have hΦ : HasDerivAt (fun y' => c_eps P.p ε * y' ^ (-P.p) * f y' - calpha P.p * J0 y')
      (c_eps P.p ε * (-P.p * y ^ (-P.p - 1)) * f y + c_eps P.p ε * y ^ (-P.p) * deriv f y -
        calpha P.p * ∫ t in Ioi (0 : ℝ), K1 y t * w t) y := by
    have h1 := (Real.hasDerivAt_rpow_const (p := -P.p) (x := y) (Or.inl hy0.ne')).const_mul
      (c_eps P.p ε)
    exact ((h1.fun_mul (hdf y).hasDerivAt).fun_sub (hJd.const_mul (calpha P.p))).congr_deriv
      (by ring)
  have hres : res_DQW P.p ε h y = c_eps P.p ε * (-P.p * y ^ (-P.p - 1)) * f y +
      c_eps P.p ε * y ^ (-P.p) * deriv f y - calpha P.p * ∫ t in Ioi (0 : ℝ), K1 y t * w t := by
    rw [hF2]
    have hGdy : DifferentiableAt ℝ G y := (hGd y hy0).differentiableAt (Ioi_mem_nhds hy0)
    rw [← deriv_const_mul _ hGdy]
    have hev : (fun y' => calpha P.p * G y') =ᶠ[nhds y]
        fun y' => c_eps P.p ε * y' ^ (-P.p) * f y' - calpha P.p * J0 y' := by
      filter_upwards [Ioi_mem_nhds hy0] with x hx using hGeq x hx
    rw [hev.deriv_eq, hΦ.deriv]
  obtain ⟨-, hdrep⟩ := hrep y hy
  have e6 : residual_decomposition_E6 P.p R ε μ y = res_DQW P.p ε h y -
      2 * c_eps P.p ε * y ^ (-P.p) *
        (fam_Z P.p R ε μ y + (c_cubic P.p ε : ℂ) * fam_Z P.p R ε μ y ^ 3).re := rfl
  rw [e6, hres, hcongr]
  have hpow : y ^ (-P.p - 1) = y ^ (-P.p) * y⁻¹ := by
    rw [Real.rpow_sub_one hy0.ne', div_eq_mul_inv]
  have : deriv f y = deriv (c04_linear_seed_low P.p) y - P.p * c_plus P.p ε * y ^ (-P.p - 1) +
      2 * (fam_Z P.p R ε μ y + (c_cubic P.p ε : ℂ) * fam_Z P.p R ε μ y ^ 3).re := by
    rw [← hdrep]; ring
  rw [this]; ring

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E6_remote_term.  The remote wedge interaction
`ℛ₆(y) = c_α ∫₀^∞ ∂_y K_ε(y,t)(f(-t) - t) dt` is `C¹` on `(0,∞)` with
`|∂^j ℛ₆(y)| ≤ C ε y^{-2p-1-j}`. -/
theorem c06_E6_remote_term (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let f := approximate_solution_family P.p R ε μ
        let R6 : ℝ → ℝ := fun y => calpha P.p * ∫ t in Ioi (0 : ℝ),
          deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (f (-t) - t)
        ContDiffOn ℝ 1 R6 (Ioi 0) ∧
        (∀ y : ℝ, 0 < y → deriv R6 y = calpha P.p * ∫ t in Ioi (0 : ℝ),
          iteratedDeriv 2 (fun y' => c06_wedge_kernel P.p ε y' t) y * (f (-t) - t)) ∧
        (∀ y : ℝ, 0 < y → ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j R6 y| ≤ C * ε * y ^ (-2 * P.p - 1 - j)) := by
  obtain ⟨R₀, hR₀, HC⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CK, hCK, HK⟩ := c06_wedge_kernel_bounds P
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 : P.p < 1 := P.hp_hi
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC'⟩ := HC R hR
  set B2 : ℝ := 1 / (1 - P.p) + 1 / (2 + P.p + P.p - 1) with hB2
  set B3 : ℝ := 1 / (1 - P.p) + 1 / (3 + P.p + P.p - 1) with hB3
  have hB2p : 0 < B2 := by
    have : 0 < 1 - P.p := by linarith
    have : 0 < 2 + P.p + P.p - 1 := by linarith
    positivity
  have hB3p : 0 < B3 := by
    have : 0 < 1 - P.p := by linarith
    have : 0 < 3 + P.p + P.p - 1 := by linarith
    positivity
  refine ⟨|calpha P.p| * CK * C₀ * (B2 + B3) + 1, by positivity, fun ε hε μ hμ => ?_⟩
  intro f R6
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, le_trans hε.2 hε₀1⟩
  obtain ⟨hfs, hc1, -, -, -⟩ := HC' ε hε μ hμ
  obtain ⟨-, -, HKb⟩ := HK ε hε1
  obtain ⟨K1, K2, hK1, hK2, cK2y, cK1t, cK2t⟩ := c06_aux_Kder P ε hε1
  clear HC HK HC'
  set w : ℝ → ℝ := fun t => f (-t) - t with hw
  have cw : Continuous w := (hfs.continuous.comp continuous_neg).sub continuous_id
  have bw : ∀ t, 0 ≤ t → |w t| ≤ C₀ * jb t ^ (-P.p) := fun t ht => by
    have h := (hc1 (-t)).2
    have hc : corner (-t) = t := by simp only [corner, neg_neg]; exact max_eq_left ht
    have hj : jb (-t) = jb t := by simp [jb]
    rw [hc, hj] at h; exact h
  have hdK : ∀ y t, 0 < y + t → deriv (fun y' => c06_wedge_kernel P.p ε y' t) y = K1 y t :=
    fun y t h => (hK1 y t h).deriv
  have hddK : ∀ y t, 0 < y + t →
      iteratedDeriv 2 (fun y' => c06_wedge_kernel P.p ε y' t) y = K2 y t := fun y t h => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have : deriv (fun y' => c06_wedge_kernel P.p ε y' t) =ᶠ[nhds y] fun y' => K1 y' t := by
      filter_upwards [isOpen_Ioi.mem_nhds (show y ∈ Ioi (-t) by simp; linarith)] with z hz
      exact hdK z t (by have : -t < z := hz; linarith)
    rw [this.deriv_eq]; exact (hK2 y t h).deriv
  have bK1 : ∀ y t, 0 < y → 0 ≤ t → |K1 y t| ≤ CK * ε * (y + t) ^ (-(2 + P.p)) := by
    intro y t hy ht
    have := (HKb y t hy ht).1 1 (by norm_num)
    rw [iteratedDeriv_one, hdK y t (by linarith)] at this
    rw [show (-(2 + P.p) : ℝ) = -1 - P.p - ((1 : ℕ) : ℝ) by push_cast; ring]; exact this
  have bK2 : ∀ y t, 0 < y → 0 ≤ t → |K2 y t| ≤ CK * ε * (y + t) ^ (-(3 + P.p)) := by
    intro y t hy ht
    have := (HKb y t hy ht).1 2 (by norm_num)
    rw [hddK y t (by linarith)] at this
    rw [show (-(3 + P.p) : ℝ) = -1 - P.p - ((2 : ℕ) : ℝ) by push_cast; ring]; exact this
  have hKc : 0 ≤ CK * ε * C₀ := by positivity
  -- pointwise dominations
  have dom1 : ∀ y, 0 < y → ∀ t, 0 < t →
      |K1 y t * w t| ≤ CK * ε * C₀ * (jb t ^ (-P.p) * (y + t) ^ (-(2 + P.p))) := by
    intro y hy t ht
    rw [abs_mul]
    have h1 := bK1 y t hy ht.le
    have h2 := bw t ht.le
    calc |K1 y t| * |w t| ≤ (CK * ε * (y + t) ^ (-(2 + P.p))) * (C₀ * jb t ^ (-P.p)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have dom2 : ∀ y y₁, 0 < y₁ → y₁ ≤ y → ∀ t, 0 < t →
      |K2 y t * w t| ≤ CK * ε * C₀ * (jb t ^ (-P.p) * (y₁ + t) ^ (-(3 + P.p))) := by
    intro y y₁ hy₁ hyy t ht
    rw [abs_mul]
    have h1 := bK2 y t (by linarith) ht.le
    have h2 := bw t ht.le
    have hm : (y + t) ^ (-(3 + P.p)) ≤ (y₁ + t) ^ (-(3 + P.p)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    calc |K2 y t| * |w t| ≤ (CK * ε * (y₁ + t) ^ (-(3 + P.p))) * (C₀ * jb t ^ (-P.p)) :=
          mul_le_mul (le_trans h1 (by gcongr)) h2 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have meas1 : ∀ y, 0 < y → AEStronglyMeasurable (fun t => K1 y t * w t) (volume.restrict (Ioi 0)) :=
    fun y hy => (((cK1t y).mono (show Ioi (0 : ℝ) ⊆ Ioi (-y) from fun t ht => by
        simp only [mem_Ioi] at ht ⊢; linarith)).mul
      cw.continuousOn).aestronglyMeasurable measurableSet_Ioi
  have meas2 : ∀ y, 0 < y → AEStronglyMeasurable (fun t => K2 y t * w t) (volume.restrict (Ioi 0)) :=
    fun y hy => (((cK2t y).mono (show Ioi (0 : ℝ) ⊆ Ioi (-y) from fun t ht => by
        simp only [mem_Ioi] at ht ⊢; linarith)).mul
      cw.continuousOn).aestronglyMeasurable measurableSet_Ioi
  -- `R₆ = c_α ∫ K₁ w` on `(0,∞)`
  have hR6eq : ∀ y, 0 < y → R6 y = calpha P.p * ∫ t in Ioi (0 : ℝ), K1 y t * w t := fun y hy => by
    show calpha P.p * _ = _
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have : 0 < t := ht
    simp only [hw]
    rw [hdK y t (by linarith)]
  -- differentiation under the integral
  have hderiv : ∀ y₀, 0 < y₀ → HasDerivAt (fun y => ∫ t in Ioi (0 : ℝ), K1 y t * w t)
      (∫ t in Ioi (0 : ℝ), K2 y₀ t * w t) y₀ := by
    intro y₀ hy₀
    have hint : Integrable (fun t => K1 y₀ t * w t) (volume.restrict (Ioi 0)) :=
      (c06_aux_int_bound P.p hp0 hp1 _ _ (2 + P.p) y₀ (by linarith) hy₀ hKc (meas1 y₀ hy₀)
        (dom1 y₀ hy₀)).1
    have hball : ∀ x ∈ Metric.ball y₀ (y₀ / 2), y₀ / 2 ≤ x := fun x hx => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx; linarith
    have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := fun y t => K1 y t * w t) (F' := fun y t => K2 y t * w t) (x₀ := y₀)
      (bound := fun t => CK * ε * C₀ * (jb t ^ (-P.p) * (y₀ / 2 + t) ^ (-(3 + P.p))))
      (s := Metric.ball y₀ (y₀ / 2)) (Metric.ball_mem_nhds _ (by linarith))
      (by filter_upwards [Ioi_mem_nhds hy₀] with x hx using meas1 x hx) hint (meas2 y₀ hy₀)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht x hx => by
        rw [Real.norm_eq_abs]
        exact dom2 x (y₀ / 2) (by linarith) (hball x hx) t ht))
      ((c06_aux_tail4 P.p hp0 hp1 (3 + P.p) (y₀ / 2) (by linarith) (by linarith)).1.const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht x hx =>
        (hK2 x t (by have := hball x hx; have : (0 : ℝ) < t := ht; linarith)).mul_const (w t)))
    exact H.2
  have hR6d : ∀ y, 0 < y → HasDerivAt R6 (calpha P.p * ∫ t in Ioi (0 : ℝ), K2 y t * w t) y :=
    fun y hy => ((hderiv y hy).const_mul (calpha P.p)).congr_of_eventuallyEq
      (by filter_upwards [Ioi_mem_nhds hy] with x hx using hR6eq x hx)
  have hdR6 : ∀ y, 0 < y → deriv R6 y = calpha P.p * ∫ t in Ioi (0 : ℝ), K2 y t * w t :=
    fun y hy => (hR6d y hy).deriv
  -- continuity of `y ↦ ∫ K₂ w`
  have hcont : ∀ y₀, 0 < y₀ → ContinuousAt (fun y => ∫ t in Ioi (0 : ℝ), K2 y t * w t) y₀ := by
    intro y₀ hy₀
    refine continuousAt_of_dominated (μ := volume.restrict (Ioi 0))
      (bound := fun t => CK * ε * C₀ * (jb t ^ (-P.p) * (y₀ / 2 + t) ^ (-(3 + P.p))))
      (by filter_upwards [Ioi_mem_nhds hy₀] with x hx using meas2 x hx) ?_
      ((c06_aux_tail4 P.p hp0 hp1 (3 + P.p) (y₀ / 2) (by linarith) (by linarith)).1.const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht =>
        ((cK2y t).continuousAt (Ioi_mem_nhds (show -t < y₀ by
          have : (0 : ℝ) < t := ht; linarith))).mul continuousAt_const))
    filter_upwards [Ioi_mem_nhds (show y₀ / 2 < y₀ by linarith)] with x hx
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => by
      rw [Real.norm_eq_abs]; exact dom2 x (y₀ / 2) (by linarith) (le_of_lt hx) t ht)
  refine ⟨?_, fun y hy => ?_, fun y hy j hj => ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hR6d y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have : deriv R6 =ᶠ[nhds y] fun y => calpha P.p * ∫ t in Ioi (0 : ℝ), K2 y t * w t := by
      filter_upwards [Ioi_mem_nhds hy0] with x hx using hdR6 x hx
    exact (((hcont y hy0).const_mul (calpha P.p)).congr this.symm).continuousWithinAt
  · rw [hdR6 y hy]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have : 0 < t := ht
    simp only [hw]
    rw [hddK y t (by linarith)]
  · have hpos : 0 ≤ |calpha P.p| * CK * C₀ := by positivity
    interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
      rw [hR6eq y hy, abs_mul]
      have hb := (c06_aux_int_bound P.p hp0 hp1 _ _ (2 + P.p) y (by linarith) hy hKc (meas1 y hy)
        (dom1 y hy)).2
      rw [show 1 - P.p - (2 + P.p) = -2 * P.p - 1 by ring] at hb
      have hy' := Real.rpow_nonneg hy.le (-2 * P.p - 1)
      calc |calpha P.p| * |∫ t in Ioi (0 : ℝ), K1 y t * w t|
          ≤ |calpha P.p| * (CK * ε * C₀ * (B2 * y ^ (-2 * P.p - 1))) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (|calpha P.p| * CK * C₀ * B2) * ε * y ^ (-2 * P.p - 1) := by ring
        _ ≤ (|calpha P.p| * CK * C₀ * (B2 + B3) + 1) * ε * y ^ (-2 * P.p - 1) := by
            gcongr
            nlinarith
    · simp only [iteratedDeriv_one, Nat.cast_one]
      rw [hdR6 y hy, abs_mul]
      have hb := (c06_aux_int_bound P.p hp0 hp1 _ _ (3 + P.p) y (by linarith) hy hKc (meas2 y hy)
        (dom2 y y hy le_rfl)).2
      rw [show 1 - P.p - (3 + P.p) = -2 * P.p - 1 - 1 by ring] at hb
      calc |calpha P.p| * |∫ t in Ioi (0 : ℝ), K2 y t * w t|
          ≤ |calpha P.p| * (CK * ε * C₀ * (B3 * y ^ (-2 * P.p - 1 - 1))) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (|calpha P.p| * CK * C₀ * B3) * ε * y ^ (-2 * P.p - 1 - 1) := by ring
        _ ≤ (|calpha P.p| * CK * C₀ * (B2 + B3) + 1) * ε * y ^ (-2 * P.p - 1 - 1) := by
            gcongr
            nlinarith

-- The bounds of Proposition 5.13 hold on the whole open half-line `y > 2R`; `approx_E6` below states
-- them for `y ≥ 8R`, as in the paper. The two-sided derivative of `ℰ₆` at
-- `y = 2R` is not controlled (the exact decomposition lem:c06_E6_exact_decomposition holds only on
-- `[2R,∞)`; just left of `2R`, `χ_R < 1`), so smoothness is stated on the open half-line `Ioi (2R)`.
set_option maxHeartbeats 800000 in
/-- Helper for prop:approx_E6: the bounds of `ℰ₆` on the open half-line `(2R,∞)`. -/
theorem c06_aux_E6_bounds_gt2R (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiffOn ℝ 1 (residual_decomposition_E6 P.p R ε μ) (Ioi (2 * R)) ∧
        ∀ y : ℝ, 2 * R < y →
          (∀ j : ℕ, j ≤ 1 → |iteratedDeriv j (residual_decomposition_E6 P.p R ε μ) y| ≤
            C * ε * jb y ^ (-2 * P.p - 1 + j / P.p)) ∧
          |residual_decomposition_E6 P.p R ε μ y| ≤ C * ε * y ^ (-2 * P.p - 1) ∧
          |deriv (residual_decomposition_E6 P.p R ε μ) y| ≤
            C * ε * (y ^ (-2 * P.p - 2) + y ^ (-P.p - 1 - beta P.p)) := by
  obtain ⟨R₁, hR₁, HD⟩ := c06_E6_exact_decomposition P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₂, hR₂, HR⟩ := c06_E6_remote_term P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₃, hR₃, HP⟩ := c06_positive_representation P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₄, hR₄, HC⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨-, -, -, -, -, -, hlow, -⟩ := c04_seed_decomposition P.p P.hp_lo P.hp_hi
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 : P.p < 1 := P.hp_hi
  have hβ0 : 0 < beta P.p := by unfold beta; positivity
  have hinv : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hpinv : 1 / P.p < 4 / 3 := by
    rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith [P.hp_lo]
  refine ⟨max (max R₁ R₂) (max R₃ R₄), le_trans hR₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun R hR => ?_⟩
  have hRR₁ : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRR₂ : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRR₃ : R₃ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRR₄ : R₄ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have hR1 : 1 ≤ R := le_trans hR₁ hRR₁
  obtain ⟨CR, hCR, HR'⟩ := HR R hRR₂
  obtain ⟨C₁, hC₁, HP'⟩ := HP R hRR₃
  obtain ⟨C₀, hC₀, HC'⟩ := HC R hRR₄
  set K₁ : ℝ := 2 * C₁ ^ 2 + 2 * C₁ * C₀ + CR with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  refine ⟨54 * K₁ + 1, by positivity, fun ε hε μ hμ => ?_⟩
  have hε0 : 0 ≤ ε := hε.1
  obtain ⟨hR6c, -, hR6b⟩ := HR' ε hε μ hμ
  obtain ⟨-, hce, -, hg3, -⟩ := HP' ε hε μ hμ
  obtain ⟨hfs, -, -, -, hf3⟩ := HC' ε hε μ hμ
  set f := approximate_solution_family P.p R ε μ with hf
  set g : ℝ → ℝ := fun y => c04_linear_seed_low P.p y + c_plus P.p ε * y ^ (-P.p) with hg
  set R6 : ℝ → ℝ := fun y => calpha P.p * ∫ t in Ioi (0 : ℝ),
    deriv (fun y' => c06_wedge_kernel P.p ε y' t) y * (f (-t) - t) with hR6
  set T : ℝ → ℝ := fun y => c_eps P.p ε * y ^ (-P.p) * deriv g y -
    P.p * c_eps P.p ε * y ^ (-P.p - 1) * f y - R6 y with hT
  have hgd : ∀ y, 0 < y → deriv g y = deriv (c04_linear_seed_low P.p) y -
      P.p * c_plus P.p ε * y ^ (-P.p - 1) := fun y hy => by
    have h1 := (hlow.differentiable (by simp) y).hasDerivAt
    have h2 := (Real.hasDerivAt_rpow_const (p := -P.p) (Or.inl hy.ne')).const_mul (c_plus P.p ε)
    have h3 : HasDerivAt g (deriv (c04_linear_seed_low P.p) y +
        c_plus P.p ε * (-P.p * y ^ (-P.p - 1))) y := h1.add h2
    rw [h3.deriv]; ring
  have hEq : ∀ y, 2 * R ≤ y → residual_decomposition_E6 P.p R ε μ y = T y := fun y hy => by
    have hy0 : 0 < y := by linarith
    obtain ⟨-, he⟩ := HD R hRR₁ ε hε μ hμ y hy
    rw [he]
    simp only [hT, hR6, hgd y hy0]
    rfl
  clear HD HR HP HC HR' HP' HC'
  -- smoothness of `T` on `(0,∞)`
  have hgs : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioi 0) :=
    hlow.contDiffOn.add (contDiffOn_const.mul (contDiffOn_id.rpow_const_of_ne
      (fun x hx => (ne_of_gt (show (0 : ℝ) < x from hx)))))
  have hdgs : ContDiffOn ℝ 1 (deriv g) (Ioi 0) :=
    hgs.deriv_of_isOpen isOpen_Ioi (WithTop.coe_le_coe.mpr le_top)
  have hpow : ∀ a : ℝ, ContDiffOn ℝ 1 (fun y : ℝ => y ^ a) (Ioi 0) := fun a =>
    contDiffOn_id.rpow_const_of_ne (fun x hx => (ne_of_gt (show (0 : ℝ) < x from hx)))
  have hTs : ContDiffOn ℝ 1 T (Ioi 0) :=
    ((contDiffOn_const.mul (hpow _)).mul hdgs).sub
      ((contDiffOn_const.mul (hpow _)).mul (hfs.of_le (by exact_mod_cast le_top)).contDiffOn) |>.sub
      hR6c
  have hsub : Ioi (2 * R) ⊆ Ioi 0 := fun x hx => by
    have : 2 * R < x := hx; show (0 : ℝ) < x; linarith
  refine ⟨(hTs.mono hsub).congr (fun y hy => hEq y (le_of_lt hy)), fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hyI : y ∈ Ioi (0 : ℝ) := hy0
  -- the derivative of `ℰ₆` equals that of `T`
  have hEv : residual_decomposition_E6 P.p R ε μ =ᶠ[nhds y] T := by
    filter_upwards [Ioi_mem_nhds hy] with x hx using hEq x (le_of_lt hx)
  have hdiff : ∀ {φ : ℝ → ℝ}, ContDiffOn ℝ 1 φ (Ioi 0) → HasDerivAt φ (deriv φ y) y := fun h =>
    ((h.contDiffAt (Ioi_mem_nhds hy0)).differentiableAt (by norm_num)).hasDerivAt
  have hdT : HasDerivAt T
      (c_eps P.p ε * ((-P.p) * y ^ (-P.p - 1) * deriv g y + y ^ (-P.p) * deriv (deriv g) y) -
        P.p * c_eps P.p ε * ((-P.p - 1) * y ^ (-P.p - 1 - 1) * f y + y ^ (-P.p - 1) * deriv f y) -
        deriv R6 y) y := by
    have h1 := Real.hasDerivAt_rpow_const (p := -P.p) (x := y) (Or.inl hy0.ne')
    have h2 := Real.hasDerivAt_rpow_const (p := -P.p - 1) (x := y) (Or.inl hy0.ne')
    have h3 := hdiff hdgs
    have h4 := ((hfs.differentiable (by simp)) y).hasDerivAt
    have h5 := hdiff hR6c
    refine ((((h1.const_mul (c_eps P.p ε)).fun_mul h3).fun_sub
      ((h2.const_mul (P.p * c_eps P.p ε)).fun_mul h4)).fun_sub h5).congr_deriv ?_
    rw [show -P.p - 1 = -P.p - 1 by ring]; ring
  -- elementary bounds
  have bce : |c_eps P.p ε| ≤ C₁ * ε := by
    have := abs_nonneg (c_plus P.p ε); linarith
  have bg1 : |deriv g y| ≤ C₁ * y ^ (-P.p - 1) := by
    have := hg3 y (by linarith) 1 (by norm_num)
    simpa [iteratedDeriv_one] using this
  have bg2 : |deriv (deriv g) y| ≤ C₁ * y ^ (-P.p - 2) := by
    have := hg3 y (by linarith) 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    convert this using 3
  have bf0 : |f y| ≤ C₀ * y ^ (-P.p) := (hf3 y hy1).1
  have bf1 : |deriv f y| ≤ C₀ * y ^ (-beta P.p) := by
    have := (hf3 y hy1).2 0 (by norm_num)
    simpa [iteratedDeriv_one] using this
  have bR0 : |R6 y| ≤ CR * ε * y ^ (-2 * P.p - 1) := by
    have := hR6b y hy0 0 (by norm_num)
    simpa using this
  have bR1 : |deriv R6 y| ≤ CR * ε * y ^ (-2 * P.p - 1 - 1) := by
    have := hR6b y hy0 1 (by norm_num)
    simpa [iteratedDeriv_one] using this
  have rp : ∀ a b : ℝ, y ^ a * y ^ b = y ^ (a + b) := fun a b => (Real.rpow_add hy0 a b).symm
  have pos : ∀ a : ℝ, 0 ≤ y ^ a := fun a => Real.rpow_nonneg hy0.le a
  -- the "in fact" bounds
  have hV : |T y| ≤ K₁ * ε * y ^ (-2 * P.p - 1) := by
    have t1 : |c_eps P.p ε * y ^ (-P.p) * deriv g y| ≤ C₁ ^ 2 * ε * y ^ (-2 * P.p - 1) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (pos _)]
      calc |c_eps P.p ε| * y ^ (-P.p) * |deriv g y|
          ≤ (C₁ * ε) * y ^ (-P.p) * (C₁ * y ^ (-P.p - 1)) := by gcongr
        _ = C₁ ^ 2 * ε * (y ^ (-P.p) * y ^ (-P.p - 1)) := by ring
        _ = _ := by rw [rp]; ring_nf
    have t2 : |P.p * c_eps P.p ε * y ^ (-P.p - 1) * f y| ≤ C₁ * C₀ * ε * y ^ (-2 * P.p - 1) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pos _), abs_of_pos hp0]
      calc P.p * |c_eps P.p ε| * y ^ (-P.p - 1) * |f y|
          ≤ 1 * (C₁ * ε) * y ^ (-P.p - 1) * (C₀ * y ^ (-P.p)) := by gcongr
        _ = C₁ * C₀ * ε * (y ^ (-P.p - 1) * y ^ (-P.p)) := by ring
        _ = _ := by rw [rp]; ring_nf
    have : |T y| ≤ |c_eps P.p ε * y ^ (-P.p) * deriv g y| +
        |P.p * c_eps P.p ε * y ^ (-P.p - 1) * f y| + |R6 y| := by
      have eT : T y = c_eps P.p ε * y ^ (-P.p) * deriv g y -
          P.p * c_eps P.p ε * y ^ (-P.p - 1) * f y - R6 y := rfl
      rw [eT]
      have h1 := abs_sub (c_eps P.p ε * y ^ (-P.p) * deriv g y -
          P.p * c_eps P.p ε * y ^ (-P.p - 1) * f y) (R6 y)
      have h2 := abs_sub (c_eps P.p ε * y ^ (-P.p) * deriv g y)
          (P.p * c_eps P.p ε * y ^ (-P.p - 1) * f y)
      linarith
    have e : 0 ≤ ε * y ^ (-2 * P.p - 1) := mul_nonneg hε0 (pos _)
    have hk : C₁ ^ 2 + C₁ * C₀ + CR ≤ K₁ := by
      rw [hK₁]; nlinarith [mul_pos hC₁ (by linarith : (0:ℝ) < C₀)]
    calc |T y| ≤ C₁ ^ 2 * ε * y ^ (-2 * P.p - 1) + C₁ * C₀ * ε * y ^ (-2 * P.p - 1) +
          CR * ε * y ^ (-2 * P.p - 1) := by linarith
      _ = (C₁ ^ 2 + C₁ * C₀ + CR) * (ε * y ^ (-2 * P.p - 1)) := by ring
      _ ≤ K₁ * (ε * y ^ (-2 * P.p - 1)) := mul_le_mul_of_nonneg_right hk e
      _ = K₁ * ε * y ^ (-2 * P.p - 1) := by ring
  have hD : |deriv T y| ≤ K₁ * ε * (y ^ (-2 * P.p - 2) + y ^ (-P.p - 1 - beta P.p)) := by
    rw [hdT.deriv]
    have e1 : -P.p - 1 - 1 = -P.p - 2 := by ring
    have e2 : -2 * P.p - 1 - 1 = -2 * P.p - 2 := by ring
    rw [e1] at *
    rw [e2] at bR1
    have t1 : |c_eps P.p ε * ((-P.p) * y ^ (-P.p - 1) * deriv g y + y ^ (-P.p) * deriv (deriv g) y)|
        ≤ 2 * C₁ ^ 2 * ε * y ^ (-2 * P.p - 2) := by
      rw [abs_mul]
      have a1 : |(-P.p) * y ^ (-P.p - 1) * deriv g y| ≤ C₁ * y ^ (-2 * P.p - 2) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hp0, abs_of_nonneg (pos _)]
        calc P.p * y ^ (-P.p - 1) * |deriv g y| ≤ 1 * y ^ (-P.p - 1) * (C₁ * y ^ (-P.p - 1)) := by
              gcongr
          _ = C₁ * (y ^ (-P.p - 1) * y ^ (-P.p - 1)) := by ring
          _ = _ := by rw [rp]; ring_nf
      have a2 : |y ^ (-P.p) * deriv (deriv g) y| ≤ C₁ * y ^ (-2 * P.p - 2) := by
        rw [abs_mul, abs_of_nonneg (pos _)]
        calc y ^ (-P.p) * |deriv (deriv g) y| ≤ y ^ (-P.p) * (C₁ * y ^ (-P.p - 2)) := by gcongr
          _ = C₁ * (y ^ (-P.p) * y ^ (-P.p - 2)) := by ring
          _ = _ := by rw [rp]; ring_nf
      calc |c_eps P.p ε| * |(-P.p) * y ^ (-P.p - 1) * deriv g y + y ^ (-P.p) * deriv (deriv g) y|
          ≤ (C₁ * ε) * (C₁ * y ^ (-2 * P.p - 2) + C₁ * y ^ (-2 * P.p - 2)) := by
            gcongr
            exact le_trans (abs_add_le _ _) (add_le_add a1 a2)
        _ = _ := by ring
    have t2 : |P.p * c_eps P.p ε * ((-P.p - 1) * y ^ (-P.p - 2) * f y + y ^ (-P.p - 1) * deriv f y)|
        ≤ C₁ * ε * (2 * C₀ * y ^ (-2 * P.p - 2) + C₀ * y ^ (-P.p - 1 - beta P.p)) := by
      rw [abs_mul, abs_mul, abs_of_pos hp0]
      have a1 : |(-P.p - 1) * y ^ (-P.p - 2) * f y| ≤ 2 * C₀ * y ^ (-2 * P.p - 2) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pos _), show -P.p - 1 = -(P.p + 1) by ring, abs_neg,
          abs_of_pos (by linarith)]
        calc (P.p + 1) * y ^ (-P.p - 2) * |f y| ≤ 2 * y ^ (-P.p - 2) * (C₀ * y ^ (-P.p)) := by
              gcongr; linarith
          _ = 2 * C₀ * (y ^ (-P.p - 2) * y ^ (-P.p)) := by ring
          _ = _ := by rw [rp]; ring_nf
      have a2 : |y ^ (-P.p - 1) * deriv f y| ≤ C₀ * y ^ (-P.p - 1 - beta P.p) := by
        rw [abs_mul, abs_of_nonneg (pos _)]
        calc y ^ (-P.p - 1) * |deriv f y| ≤ y ^ (-P.p - 1) * (C₀ * y ^ (-beta P.p)) := by gcongr
          _ = C₀ * (y ^ (-P.p - 1) * y ^ (-beta P.p)) := by ring
          _ = _ := by rw [rp]; ring_nf
      calc P.p * |c_eps P.p ε| * |(-P.p - 1) * y ^ (-P.p - 2) * f y + y ^ (-P.p - 1) * deriv f y|
          ≤ 1 * (C₁ * ε) * (2 * C₀ * y ^ (-2 * P.p - 2) + C₀ * y ^ (-P.p - 1 - beta P.p)) := by
            gcongr
            exact le_trans (abs_add_le _ _) (add_le_add a1 a2)
        _ = _ := by ring
    have h3 := abs_sub (c_eps P.p ε * ((-P.p) * y ^ (-P.p - 1) * deriv g y +
        y ^ (-P.p) * deriv (deriv g) y) -
      P.p * c_eps P.p ε * ((-P.p - 1) * y ^ (-P.p - 2) * f y + y ^ (-P.p - 1) * deriv f y))
      (deriv R6 y)
    have h4 := abs_sub (c_eps P.p ε * ((-P.p) * y ^ (-P.p - 1) * deriv g y +
        y ^ (-P.p) * deriv (deriv g) y))
      (P.p * c_eps P.p ε * ((-P.p - 1) * y ^ (-P.p - 2) * f y + y ^ (-P.p - 1) * deriv f y))
    have q1 := mul_nonneg hε0 (pos (-2 * P.p - 2))
    have q2 := mul_nonneg hε0 (pos (-P.p - 1 - beta P.p))
    have hk1 : 2 * C₁ ^ 2 + 2 * C₁ * C₀ + CR ≤ K₁ := le_of_eq hK₁.symm
    have hk2 : C₁ * C₀ ≤ K₁ := by rw [hK₁]; nlinarith [mul_pos hC₁ (by linarith : (0:ℝ) < C₀)]
    calc _ ≤ 2 * C₁ ^ 2 * ε * y ^ (-2 * P.p - 2) +
          C₁ * ε * (2 * C₀ * y ^ (-2 * P.p - 2) + C₀ * y ^ (-P.p - 1 - beta P.p)) +
          CR * ε * y ^ (-2 * P.p - 2) := by linarith
      _ = (2 * C₁ ^ 2 + 2 * C₁ * C₀ + CR) * (ε * y ^ (-2 * P.p - 2)) +
          (C₁ * C₀) * (ε * y ^ (-P.p - 1 - beta P.p)) := by ring
      _ ≤ K₁ * (ε * y ^ (-2 * P.p - 2)) + K₁ * (ε * y ^ (-P.p - 1 - beta P.p)) := by
          gcongr
      _ = K₁ * ε * (y ^ (-2 * P.p - 2) + y ^ (-P.p - 1 - beta P.p)) := by ring
  have hDE : |deriv (residual_decomposition_E6 P.p R ε μ) y| ≤
      K₁ * ε * (y ^ (-2 * P.p - 2) + y ^ (-P.p - 1 - beta P.p)) := by
    rw [hEv.deriv_eq]; exact hD
  have hVE : |residual_decomposition_E6 P.p R ε μ y| ≤ K₁ * ε * y ^ (-2 * P.p - 1) := by
    rw [hEq y hy.le]; exact hV
  have hKC : K₁ ≤ 54 * K₁ + 1 := by linarith
  -- conversion to `⟨y⟩`
  have hsum : y ^ (-2 * P.p - 2) + y ^ (-P.p - 1 - beta P.p) ≤ 2 * y ^ (-2 * P.p - 1 + 1 / P.p) := by
    have hb : beta P.p ≤ 1 / P.p := by
      have e : beta P.p = ((P.p + 1) / 2) * (1 / P.p) := by
        unfold beta; rw [div_mul_div_comm, mul_one]
      rw [e]
      have h1 := one_div_pos.mpr hp0
      calc (P.p + 1) / 2 * (1 / P.p) ≤ 1 * (1 / P.p) :=
            mul_le_mul_of_nonneg_right (by linarith) h1.le
        _ = 1 / P.p := one_mul _
    have u1 := Real.rpow_le_rpow_of_exponent_le hy1 (show -2 * P.p - 2 ≤ -2 * P.p - 1 + 1 / P.p by
      linarith)
    have u2 := Real.rpow_le_rpow_of_exponent_le hy1
      (show -P.p - 1 - beta P.p ≤ -2 * P.p - 1 + 1 / P.p by linarith)
    linarith
  have hconv : ∀ b : ℝ, 0 ≤ b → b ≤ 3 → y ^ (-b) ≤ 27 * jb y ^ (-b) := fun b hb hb3 => by
    have := c06_aux_Y_le_jb b y y hb hy1 le_rfl (by linarith)
    have h3 : (3 : ℝ) ^ b ≤ 27 := by
      calc (3 : ℝ) ^ b ≤ (3 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hb3
        _ = 27 := by norm_num
    have := Real.rpow_nonneg (c06_aux_jb_pos y).le (-b)
    nlinarith
  refine ⟨fun j hj => ?_, le_trans hVE (by gcongr), le_trans hDE (by gcongr)⟩
  have hjb := fun b => Real.rpow_nonneg (c06_aux_jb_pos y).le b
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
    have := hconv (2 * P.p + 1) (by linarith) (by linarith)
    rw [show -(2 * P.p + 1) = -2 * P.p - 1 by ring] at this
    calc _ ≤ K₁ * ε * y ^ (-2 * P.p - 1) := hVE
      _ ≤ K₁ * ε * (27 * jb y ^ (-2 * P.p - 1)) := by gcongr
      _ ≤ (54 * K₁ + 1) * ε * jb y ^ (-2 * P.p - 1) := by
          have := mul_nonneg hε0 (hjb (-2 * P.p - 1))
          nlinarith
  · simp only [iteratedDeriv_one, Nat.cast_one]
    have := hconv (2 * P.p + 1 - 1 / P.p) (by linarith [P.hp_lo]) (by linarith [P.hp_lo])
    rw [show -(2 * P.p + 1 - 1 / P.p) = -2 * P.p - 1 + 1 / P.p by ring] at this
    calc _ ≤ K₁ * ε * (y ^ (-2 * P.p - 2) + y ^ (-P.p - 1 - beta P.p)) := hDE
      _ ≤ K₁ * ε * (2 * (27 * jb y ^ (-2 * P.p - 1 + 1 / P.p))) := by gcongr; linarith
      _ ≤ (54 * K₁ + 1) * ε * jb y ^ (-2 * P.p - 1 + 1 / P.p) := by
          have := mul_nonneg hε0 (hjb (-2 * P.p - 1 + 1 / P.p))
          nlinarith

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
-- Proposition 5.13 of the paper is stated for `y ≥ 8R`, as here; the
-- bounds in fact hold for `y > 2R` (`c06_aux_E6_bounds_gt2R`). The `C¹` regularity on the open
-- half-line `(2R,∞)` makes the derivative bound at `y = 8R` a two-sided statement.
/-- Blueprint: prop:approx_E6.  Control of `ℰ₆`: `|∂ʲℰ₆(y)| ≲ ε⟨y⟩^{-2p-1+j/p}` for `y ≥ 8R`,
`j = 0,1`, with `ℰ₆ ∈ C¹((2R,∞))`. -/
theorem approx_E6 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiffOn ℝ 1 (residual_decomposition_E6 P.p R ε μ) (Ioi (2 * R)) ∧
        ∀ y : ℝ, 8 * R ≤ y →
          (∀ j : ℕ, j ≤ 1 → |iteratedDeriv j (residual_decomposition_E6 P.p R ε μ) y| ≤
            C * ε * jb y ^ (-2 * P.p - 1 + j / P.p)) ∧
          |residual_decomposition_E6 P.p R ε μ y| ≤ C * ε * y ^ (-2 * P.p - 1) ∧
          |deriv (residual_decomposition_E6 P.p R ε μ) y| ≤
            C * ε * (y ^ (-2 * P.p - 2) + y ^ (-P.p - 1 - beta P.p)) := by
  obtain ⟨R₀, hR₀, H⟩ := c06_aux_E6_bounds_gt2R P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C, hC, H'⟩ := H R hR
  exact ⟨C, hC, fun ε hε μ hμ =>
    ⟨(H' ε hε μ hμ).1, fun y hy => (H' ε hε μ hμ).2 y (by linarith)⟩⟩

/-! ## Control of `ℰ₇` -/

/-- Helper: the annulus cutoff is smooth. -/
theorem c06_aux_chiA_smooth : ContDiff ℝ (⊤ : ℕ∞) chiAnnulus := by
  unfold chiAnnulus
  exact (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _))

/-- Helper: `χ_Y` is smooth. -/
theorem c06_aux_chiY_smooth (Y : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (res_chiY Y) :=
  c06_aux_chiA_smooth.comp (contDiff_id.div_const Y)

/-- Helper: `χ_Y = 0` outside `(3Y/10, 7Y/2)`. -/
theorem c06_aux_chiY_zero {Y z : ℝ} (hY : 0 < Y) (hz : z ≤ 3 * Y / 10 ∨ 7 * Y / 2 ≤ z) :
    res_chiY Y z = 0 := by
  unfold res_chiY chiAnnulus
  rcases hz with hz | hz
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    rw [div_nonpos_iff]; right
    refine ⟨?_, by norm_num⟩
    rw [sub_nonpos, div_le_iff₀ hY]; linarith
  · rw [Real.smoothTransition.zero_of_nonpos (x := (7 / 2 - z / Y) / (1 / 2)), mul_zero]
    rw [div_nonpos_iff]; right
    refine ⟨?_, by norm_num⟩
    rw [sub_nonpos, le_div_iff₀ hY]; linarith

/-- Helper: `|χ_Y| ≤ 1`... more precisely bounds `|∂^i χ_Y| ≤ B Y^{-i}` for `i ≤ 3`. -/
theorem c06_aux_chiY_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ Y : ℝ, 0 < Y → ∀ i : ℕ, i ≤ 3 → ∀ z : ℝ,
    |iteratedDeriv i (res_chiY Y) z| ≤ B * Y ^ (-(i : ℝ)) := by
  have hc : ∀ i : ℕ, Continuous (iteratedDeriv i chiAnnulus) := fun i =>
    c06_aux_chiA_smooth.continuous_iteratedDeriv i (by exact_mod_cast le_top)
  have hzero : ∀ i : ℕ, ∀ x, x ∉ Icc (3 / 10 : ℝ) (7 / 2) → iteratedDeriv i chiAnnulus x = 0 := by
    intro i x hx
    have hev : chiAnnulus =ᶠ[nhds x] fun _ => 0 := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · filter_upwards [Iio_mem_nhds hx] with u hu
        have := c06_aux_chiY_zero (Y := 1) (z := u) one_pos (Or.inl (by
          have : u < 3 / 10 := hu; linarith))
        simpa [res_chiY] using this
      · filter_upwards [Ioi_mem_nhds hx] with u hu
        have := c06_aux_chiY_zero (Y := 1) (z := u) one_pos (Or.inr (by
          have : 7 / 2 < u := hu; linarith))
        simpa [res_chiY] using this
    rw [hev.iteratedDeriv_eq]
    have h0 : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by funext; simp
    rw [iteratedDeriv_eq_iterate, Function.iterate_fixed h0]
  choose Bi hBi using fun i : ℕ =>
    (isCompact_Icc (a := (3 / 10 : ℝ)) (b := 7 / 2)).exists_bound_of_continuousOn (hc i).continuousOn
  refine ⟨1 + ∑ i ∈ Finset.range 4, |Bi i|, by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range 4) => abs_nonneg (Bi i)); linarith,
    fun Y hY i hi z => ?_⟩
  have hB : ∀ x, |iteratedDeriv i chiAnnulus x| ≤ 1 + ∑ i ∈ Finset.range 4, |Bi i| := by
    intro x
    have hs : |Bi i| ≤ ∑ i ∈ Finset.range 4, |Bi i| :=
      Finset.single_le_sum (f := fun i => |Bi i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    by_cases hx : x ∈ Icc (3 / 10 : ℝ) (7 / 2)
    · have := hBi i x hx
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (Bi i)]
    · rw [hzero i x hx, abs_zero]
      linarith [abs_nonneg (Bi i)]
  have he : res_chiY Y = fun x => chiAnnulus (Y⁻¹ * x) := by
    funext x; simp only [res_chiY]; rw [div_eq_inv_mul]
  rw [he, iteratedDeriv_comp_const_mul (c06_aux_chiA_smooth.of_le (by exact_mod_cast le_top))]
  simp only
  rw [abs_mul, Real.rpow_neg hY.le, Real.rpow_natCast, abs_of_pos (by positivity), inv_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _) (by positivity)

/-- Helper: Leibniz bound `|∂^k(φψ)| ≤ 2^k M` if every product `|∂^iφ| |∂^{k-i}ψ| ≤ M`. -/
theorem c06_aux_leib (φ ψ : ℝ → ℝ) (z : ℝ) (k : ℕ) (hφ : ContDiffAt ℝ k φ z)
    (hψ : ContDiffAt ℝ k ψ z) (M : ℝ)
    (hM : ∀ i, i ≤ k → |iteratedDeriv i φ z| * |iteratedDeriv (k - i) ψ z| ≤ M) :
    |iteratedDeriv k (φ * ψ) z| ≤ 2 ^ k * M := by
  rw [iteratedDeriv_mul hφ hψ]
  calc _ ≤ ∑ i ∈ Finset.range (k + 1),
        |(k.choose i : ℝ) * iteratedDeriv i φ z * iteratedDeriv (k - i) ψ z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hM i (by simp at hi; omega)) (by positivity)
    _ = 2 ^ k * M := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k

/-- Helper: for `Y/4 ≤ z ≤ 4Y` and `|e| ≤ 5`, `z^e ≤ 4^5 Y^e`. -/
theorem c06_aux_comparable (Y z e : ℝ) (hY : 0 < Y) (h1 : Y / 4 ≤ z) (h2 : z ≤ 4 * Y)
    (he : |e| ≤ 5) : z ^ e ≤ 4 ^ 5 * Y ^ e := by
  have hz : 0 < z := by linarith
  have hYe := Real.rpow_pos_of_pos hY e
  rcases le_total 0 e with h | h
  · have hle : e ≤ 5 := le_trans (le_abs_self e) he
    calc z ^ e ≤ (4 * Y) ^ e := Real.rpow_le_rpow hz.le h2 h
      _ = 4 ^ e * Y ^ e := Real.mul_rpow (by norm_num) hY.le
      _ ≤ (4 : ℝ) ^ (5 : ℝ) * Y ^ e := by
          gcongr
          · norm_num
      _ = 4 ^ 5 * Y ^ e := by norm_num
  · have hle : -e ≤ 5 := by have := neg_abs_le e; linarith
    calc z ^ e ≤ (Y / 4) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) h1 h
      _ = Y ^ e * (4 : ℝ) ^ (-e) := by
          rw [Real.div_rpow hY.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv]
      _ ≤ Y ^ e * (4 : ℝ) ^ (5 : ℝ) := by
          gcongr
          · norm_num
      _ = 4 ^ 5 * Y ^ e := by norm_num; ring

/-- Blueprint: lem:c06_localized_bounds (auxiliary definition).  `h_Y = χ_Y f - v_Y`. -/
def c06_localized_bounds_hY (p R ε : ℝ) (μ : ℂ) (Y z : ℝ) : ℝ :=
  res_chiY Y z * approximate_solution_family p R ε μ z - res_vY p R ε μ Y z

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_localized_bounds.  Support, smoothness and bounds for `χ_Y f`, `v_Y`, `h_Y`. -/
theorem c06_localized_bounds (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let cf : ℝ → ℝ := fun z => res_chiY Y z * approximate_solution_family P.p R ε μ z
        let v : ℝ → ℝ := res_vY P.p R ε μ Y
        let h : ℝ → ℝ := c06_localized_bounds_hY P.p R ε μ Y
        -- (1)
        (ContDiff ℝ (⊤ : ℕ∞) cf ∧ ContDiff ℝ (⊤ : ℕ∞) v ∧ ContDiff ℝ (⊤ : ℕ∞) h) ∧
        (Function.support cf ⊆ Ioo (Y / 4) (4 * Y) ∧ Function.support v ⊆ Ioo (Y / 4) (4 * Y) ∧
          Function.support h ⊆ Ioo (Y / 4) (4 * Y)) ∧
        Ioo (Y / 4) (4 * Y) ⊆ Ioi (2 * R) ∧
        h = (fun z => res_chiY Y z * (c04_linear_seed_low P.p z + c_plus P.p ε * z ^ (-P.p))) ∧
        -- (2)
        ∀ z : ℝ,
          (∀ j : ℕ, j ≤ 3 → |iteratedDeriv j h z| ≤ C₂ * Y ^ (-P.p - j)) ∧
          |cf z| ≤ C₂ * Y ^ (-P.p) ∧
          (∀ j : ℕ, j ≤ 2 → |iteratedDeriv (j + 1) cf z| ≤ C₂ * Y ^ (-beta P.p + j / P.p)) ∧
          (∀ j : ℕ, j ≤ 2 → |iteratedDeriv (j + 1) v z| ≤ C₂ * Y ^ (-beta P.p + j / P.p)) := by
  obtain ⟨R₃, hR₃, HP⟩ := c06_positive_representation P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₄, hR₄, HC⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨B, hB1, HB⟩ := c06_aux_chiY_bound
  obtain ⟨-, -, -, -, -, -, hlow, -⟩ := c04_seed_decomposition P.p P.hp_lo P.hp_hi
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 : P.p < 1 := P.hp_hi
  have hpinv : 1 / P.p < 4 / 3 := by
    rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith [P.hp_lo]
  have hinv : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hβe : beta P.p = (1 + 1 / P.p) / 2 := by
    have := c06_aux_two_beta P.p hp0; linarith
  refine ⟨max R₃ R₄, le_trans hR₃ (le_max_left _ _), fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans hR₃ (le_trans (le_max_left _ _) hR)
  obtain ⟨C₁, hC₁, HP'⟩ := HP R (le_trans (le_max_left _ _) hR)
  obtain ⟨C₀, hC₀, HC'⟩ := HC R (le_trans (le_max_right _ _) hR)
  set K : ℝ := B * (C₀ + C₁) * 4 ^ 5 with hK
  have hK0 : 0 ≤ K := by positivity
  have hKC₀ : B * C₀ * 4 ^ 5 ≤ K := by rw [hK]; nlinarith
  have hKC₁ : B * C₁ * 4 ^ 5 ≤ K := by rw [hK]; nlinarith
  refine ⟨16 * K + 1, by positivity, fun Y hY ε hε μ hμ => ?_⟩
  intro cf v h
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  obtain ⟨hfs, -, -, -, hf3⟩ := HC' ε hε μ hμ
  obtain ⟨-, -, hrep, hg3, -⟩ := HP' ε hε μ hμ
  clear HP HC HP' HC'
  set f := approximate_solution_family P.p R ε μ with hf
  set χ : ℝ → ℝ := res_chiY Y with hχ
  set g : ℝ → ℝ := fun z => c04_linear_seed_low P.p z + c_plus P.p ε * z ^ (-P.p) with hg
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := c06_aux_chiY_smooth Y
  have hχz : ∀ u, (u ≤ 3 * Y / 10 ∨ 7 * Y / 2 ≤ u) → χ u = 0 := fun u hu =>
    c06_aux_chiY_zero hY0 hu
  have hsupp : ∀ z, χ z ≠ 0 → 3 * Y / 10 < z ∧ z < 7 * Y / 2 := fun z hz => by
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    exact hz (c06_aux_chiY_zero hY0 hc)
  have hv : ∀ z, v z = χ z * (f z - g z) := fun z => by
    by_cases h0 : χ z = 0
    · have h0' : res_chiY Y z = 0 := h0
      show res_vY P.p R ε μ Y z = res_chiY Y z * (f z - g z)
      unfold res_vY
      rw [h0']
      split_ifs <;> simp
    · obtain ⟨h1, h2⟩ := hsupp z h0
      have hz : 2 * R ≤ z := by linarith
      show res_vY P.p R ε μ Y z = _
      unfold res_vY
      rw [if_pos (by linarith)]
      have := (hrep z hz).1
      rw [this]
      simp only [hχ, hg]; ring
  have hgA : ∀ z, 0 < z → ContDiffAt ℝ (⊤ : ℕ∞) g z := fun z hz =>
    hlow.contDiffAt.add (contDiffAt_const.mul (contDiffAt_rpow_const_of_ne hz.ne'))
  have hχg : ContDiff ℝ (⊤ : ℕ∞) (fun z => χ z * g z) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge 0 z with hz | hz
    · exact hχs.contDiffAt.mul (hgA z hz)
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (show z < 3 * Y / 10 by linarith)] with u hu
      rw [hχz u (Or.inl (le_of_lt hu)), zero_mul]
  have hhe : h = fun z => χ z * g z := by
    funext z
    show χ z * f z - v z = _
    rw [hv z]; ring
  have hve : v = fun z => χ z * f z - χ z * g z := by
    funext z; rw [hv z]; ring
  have hcfs : ContDiff ℝ (⊤ : ℕ∞) cf := hχs.mul hfs
  have hvs : ContDiff ℝ (⊤ : ℕ∞) v := by rw [hve]; exact hcfs.sub hχg
  -- vanishing of iterated derivatives away from the annulus
  have hzero : ∀ (φ : ℝ → ℝ) (z : ℝ), (z < Y / 4 ∨ 4 * Y < z) → ∀ n : ℕ,
      iteratedDeriv n (fun x => χ x * φ x) z = 0 := by
    intro φ z hz n
    have hev : (fun x => χ x * φ x) =ᶠ[nhds z] fun _ => 0 := by
      rcases hz with hz | hz
      · filter_upwards [Iio_mem_nhds (show z < 3 * Y / 10 by linarith)] with u hu
        rw [hχz u (Or.inl (le_of_lt hu)), zero_mul]
      · filter_upwards [Ioi_mem_nhds (show 7 * Y / 2 < z by linarith)] with u hu
        rw [hχz u (Or.inr (le_of_lt hu)), zero_mul]
    rw [hev.iteratedDeriv_eq]
    have h0 : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by funext; simp
    rw [iteratedDeriv_eq_iterate, Function.iterate_fixed h0]
  have hsub : Ioo (Y / 4) (4 * Y) ⊆ Ioi (2 * R) := fun z hz => by
    have : Y / 4 < z := hz.1; show 2 * R < z; linarith
  have hsuppf : ∀ φ : ℝ → ℝ, Function.support (fun z => χ z * φ z) ⊆ Ioo (Y / 4) (4 * Y) :=
    fun φ z hz => by
      have h0 : χ z ≠ 0 := fun h0 => hz (by simp [h0])
      obtain ⟨h1, h2⟩ := hsupp z h0
      exact ⟨by linarith, by linarith⟩
  -- exponent bookkeeping
  have rp : ∀ a b : ℝ, Y ^ a * Y ^ b = Y ^ (a + b) := fun a b => (Real.rpow_add hY0 a b).symm
  have mono : ∀ a b : ℝ, a ≤ b → Y ^ a ≤ Y ^ b := fun a b hab =>
    Real.rpow_le_rpow_of_exponent_le hY1 hab
  have bχ : ∀ i : ℕ, i ≤ 3 → ∀ z, |iteratedDeriv i χ z| ≤ B * Y ^ (-(i : ℝ)) :=
    fun i hi z => HB Y hY0 i hi z
  -- bounds for `h = χ g`
  have bh : ∀ z, ∀ j : ℕ, j ≤ 3 → |iteratedDeriv j (fun z => χ z * g z) z| ≤ 8 * K * Y ^ (-P.p - j) := by
    intro z j hj
    by_cases hz : Y / 4 ≤ z ∧ z ≤ 4 * Y
    · obtain ⟨hz1, hz2⟩ := hz
      have hz0 : 0 < z := by linarith
      have hL := c06_aux_leib χ g z j (hχs.contDiffAt.of_le (by exact_mod_cast le_top))
        ((hgA z hz0).of_le (by exact_mod_cast le_top)) (K * Y ^ (-P.p - j)) (fun i hi => by
          have e1 := bχ i (by omega) z
          have e2 := hg3 z (by linarith) (j - i) (by omega)
          rw [Nat.cast_sub hi] at e2
          have e3 := c06_aux_comparable Y z (-P.p - ((j : ℝ) - i)) hY0 hz1 hz2 (by
            have : (i : ℝ) ≤ j := by exact_mod_cast hi
            have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
            rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
          have hYi := Real.rpow_nonneg hY0.le (-(i : ℝ))
          calc |iteratedDeriv i χ z| * |iteratedDeriv (j - i) g z|
              ≤ (B * Y ^ (-(i : ℝ))) * (C₁ * (4 ^ 5 * Y ^ (-P.p - ((j : ℝ) - i)))) := by
                apply mul_le_mul e1 (le_trans e2 (by gcongr)) (abs_nonneg _) (by positivity)
            _ = (B * C₁ * 4 ^ 5) * (Y ^ (-(i : ℝ)) * Y ^ (-P.p - ((j : ℝ) - i))) := by ring
            _ = (B * C₁ * 4 ^ 5) * Y ^ (-P.p - j) := by rw [rp]; ring_nf
            _ ≤ K * Y ^ (-P.p - j) := by gcongr)
      have : (2 : ℝ) ^ j ≤ 8 := by
        calc (2 : ℝ) ^ j ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hj
          _ = 8 := by norm_num
      calc _ ≤ 2 ^ j * (K * Y ^ (-P.p - j)) := hL
        _ ≤ 8 * (K * Y ^ (-P.p - j)) := by gcongr
        _ = _ := by ring
    · rw [not_and_or, not_le, not_le] at hz
      rw [hzero g z hz j, abs_zero]; positivity
  -- bounds for `χ f`
  have bcf : ∀ z, ∀ j : ℕ, j ≤ 2 →
      |iteratedDeriv (j + 1) (fun z => χ z * f z) z| ≤ 8 * K * Y ^ (-beta P.p + j / P.p) := by
    intro z j hj
    by_cases hz : Y / 4 ≤ z ∧ z ≤ 4 * Y
    · obtain ⟨hz1, hz2⟩ := hz
      have hz0 : 0 < z := by linarith
      have hz1' : 1 ≤ z := by linarith
      have hL := c06_aux_leib χ f z (j + 1) (hχs.contDiffAt.of_le (by exact_mod_cast le_top))
        (hfs.contDiffAt.of_le (by exact_mod_cast le_top)) (K * Y ^ (-beta P.p + j / P.p))
        (fun i hi => by
          have e1 := bχ i (by omega) z
          have hYi := Real.rpow_nonneg hY0.le (-(i : ℝ))
          rcases Nat.lt_or_ge j i with hij | hij
          · -- `i = j + 1`
            have hi' : i = j + 1 := by omega
            subst hi'
            rw [Nat.sub_self, iteratedDeriv_zero]
            have e2 := (hf3 z hz1').1
            have e3 := c06_aux_comparable Y z (-P.p) hY0 hz1 hz2 (by
              rw [abs_neg, abs_of_pos hp0]; linarith)
            calc |iteratedDeriv (j + 1) χ z| * |f z|
                ≤ (B * Y ^ (-((j + 1 : ℕ) : ℝ))) * (C₀ * (4 ^ 5 * Y ^ (-P.p))) :=
                  mul_le_mul e1 (le_trans e2 (by gcongr)) (abs_nonneg _) (by positivity)
              _ = (B * C₀ * 4 ^ 5) * (Y ^ (-((j + 1 : ℕ) : ℝ)) * Y ^ (-P.p)) := by ring
              _ = (B * C₀ * 4 ^ 5) * Y ^ (-((j + 1 : ℕ) : ℝ) + -P.p) := by rw [rp]
              _ ≤ K * Y ^ (-beta P.p + j / P.p) := by
                  apply mul_le_mul hKC₀ (mono _ _ ?_) (by positivity) hK0
                  push_cast
                  have : (0 : ℝ) ≤ j / P.p := by positivity
                  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
                  linarith [hβe, hpinv, P.hp_lo]
          · have hk : j + 1 - i = (j - i) + 1 := by omega
            rw [hk]
            have e2 := (hf3 z hz1').2 (j - i) (by omega)
            rw [Nat.cast_sub hij] at e2
            have hjr : (j : ℝ) ≤ 2 := by exact_mod_cast hj
            have hir : (i : ℝ) ≤ j := by exact_mod_cast hij
            have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
            have hq : ((j : ℝ) - i) / P.p ≤ 2 * (1 / P.p) := by
              rw [div_le_iff₀ hp0]; field_simp; linarith
            have hq0 : 0 ≤ ((j : ℝ) - i) / P.p := div_nonneg (by linarith) hp0.le
            have e3 := c06_aux_comparable Y z (-beta P.p + ((j : ℝ) - i) / P.p) hY0 hz1 hz2 (by
              rw [abs_le]; constructor <;> nlinarith)
            calc |iteratedDeriv i χ z| * |iteratedDeriv (j - i + 1) f z|
                ≤ (B * Y ^ (-(i : ℝ))) * (C₀ * (4 ^ 5 * Y ^ (-beta P.p + ((j : ℝ) - i) / P.p))) :=
                  mul_le_mul e1 (le_trans e2 (by gcongr)) (abs_nonneg _) (by positivity)
              _ = (B * C₀ * 4 ^ 5) * (Y ^ (-(i : ℝ)) * Y ^ (-beta P.p + ((j : ℝ) - i) / P.p)) := by
                  ring
              _ = (B * C₀ * 4 ^ 5) * Y ^ (-(i : ℝ) + (-beta P.p + ((j : ℝ) - i) / P.p)) := by
                  rw [rp]
              _ ≤ K * Y ^ (-beta P.p + j / P.p) := by
                  apply mul_le_mul hKC₀ (mono _ _ ?_) (by positivity) hK0
                  have : ((j : ℝ) - i) / P.p = j / P.p - i / P.p := sub_div _ _ _
                  have : (0 : ℝ) ≤ i / P.p := div_nonneg hi0 hp0.le
                  linarith)
      have : (2 : ℝ) ^ (j + 1) ≤ 8 := by
        calc (2 : ℝ) ^ (j + 1) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 8 := by norm_num
      calc _ ≤ 2 ^ (j + 1) * (K * Y ^ (-beta P.p + j / P.p)) := hL
        _ ≤ 8 * (K * Y ^ (-beta P.p + j / P.p)) := by gcongr
        _ = _ := by ring
    · rw [not_and_or, not_le, not_le] at hz
      rw [hzero f z hz (j + 1), abs_zero]; positivity
  refine ⟨⟨hcfs, hvs, by rw [hhe]; exact hχg⟩, ⟨hsuppf f, ?_, ?_⟩, hsub, hhe, fun z => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    rw [Function.mem_support, hv z] at hz
    exact hsuppf (fun z => f z - g z) hz
  · rw [hhe]; exact hsuppf g
  · intro j hj
    rw [hhe]
    exact le_trans (bh z j hj) (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hY0.le _))
  · by_cases hz : Y / 4 ≤ z ∧ z ≤ 4 * Y
    · obtain ⟨hz1, hz2⟩ := hz
      have e1 := bχ 0 (by norm_num) z
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at e1
      have e2 := (hf3 z (by linarith)).1
      have e3 := c06_aux_comparable Y z (-P.p) hY0 hz1 hz2 (by
        rw [abs_neg, abs_of_pos hp0]; linarith)
      show |χ z * f z| ≤ _
      rw [abs_mul]
      calc |χ z| * |f z| ≤ B * (C₀ * (4 ^ 5 * Y ^ (-P.p))) :=
            mul_le_mul e1 (le_trans e2 (by gcongr)) (abs_nonneg _) (by positivity)
        _ = (B * C₀ * 4 ^ 5) * Y ^ (-P.p) := by ring
        _ ≤ (16 * K + 1) * Y ^ (-P.p) := by
            gcongr; linarith
    · rw [not_and_or, not_le, not_le] at hz
      have h0 : χ z = 0 := c06_aux_chiY_zero hY0 (by rcases hz with hz | hz; left; linarith; right; linarith)
      show |χ z * f z| ≤ _
      rw [h0, zero_mul, abs_zero]; positivity
  · intro j hj
    exact le_trans (bcf z j hj) (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hY0.le _))
  · intro j hj
    rw [hve]
    have hA : ContDiffAt ℝ (j + 1 : ℕ) (fun z => χ z * f z) z :=
      hcfs.contDiffAt.of_le (by exact_mod_cast le_top)
    have hB' : ContDiffAt ℝ (j + 1 : ℕ) (fun z => χ z * g z) z :=
      hχg.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_fun_sub hA hB']
    have e1 := bcf z j hj
    have e2 := bh z (j + 1) (by omega)
    have e3 : Y ^ (-P.p - ((j + 1 : ℕ) : ℝ)) ≤ Y ^ (-beta P.p + j / P.p) := mono _ _ (by
      push_cast
      have : (0 : ℝ) ≤ j / P.p := by positivity
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith [hβe, hpinv, P.hp_lo])
    have := abs_sub (iteratedDeriv (j + 1) (fun z => χ z * f z) z)
      (iteratedDeriv (j + 1) (fun z => χ z * g z) z)
    have hpos := Real.rpow_nonneg hY0.le (-beta P.p + j / P.p)
    nlinarith

/-- Blueprint: lem:c06_E7_decomposition (auxiliary definition).
`T_{7,1}(y) = ∫ (h'(y)-h'(y-s))/|s|^{1+p} · S_{v+h}(y,y-s)² ds`. -/
def c06_E7_decomposition_T1 (p : ℝ) (v h : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ s, (deriv h y - deriv h (y - s)) / |s| ^ (1 + p) *
    c01_secant (fun x => v x + h x) y (y - s) ^ 2

/-- Blueprint: lem:c06_E7_decomposition (auxiliary definition).
`T_{7,2}(y) = ∫ (v'(y)-v'(y-s))/|s|^{1+p} · S_h(y,y-s) S_{2v+h}(y,y-s) ds`. -/
def c06_E7_decomposition_T2 (p : ℝ) (v h : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ s, (deriv v y - deriv v (y - s)) / |s| ^ (1 + p) *
    c01_secant h y (y - s) * c01_secant (fun x => 2 * v x + h x) y (y - s)

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E7_decomposition.  `ℰ₇ = κ (T_{7,1} + T_{7,2})` with
`κ = -(p+1)εc_α/2`, all integrals absolutely convergent. -/
theorem c06_E7_decomposition (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y : ℝ,
        let cf : ℝ → ℝ := fun z => res_chiY Y z * approximate_solution_family P.p R ε μ z
        let v : ℝ → ℝ := res_vY P.p R ε μ Y
        let h : ℝ → ℝ := c06_localized_bounds_hY P.p R ε μ Y
        residual_decomposition_E7 P.p R ε μ Y y =
          c04_cubic_part_kappa P.p ε *
            (c06_E7_decomposition_T1 P.p v h y + c06_E7_decomposition_T2 P.p v h y) ∧
        Integrable (fun s : ℝ => (deriv h y - deriv h (y - s)) / |s| ^ (1 + P.p) *
          c01_secant (fun x => v x + h x) y (y - s) ^ 2) ∧
        Integrable (fun s : ℝ => (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) *
          c01_secant h y (y - s) * c01_secant (fun x => 2 * v x + h x) y (y - s)) ∧
        Integrable (fun z : ℝ => (deriv cf y - deriv cf z) / |y - z| ^ (P.p + 1) *
          c01_secant cf y z ^ 2) ∧
        Integrable (fun z : ℝ => (deriv v y - deriv v z) / |y - z| ^ (P.p + 1) *
          c01_secant v y z ^ 2) := by
  obtain ⟨R₂, hR₂, HL⟩ := c06_localized_bounds P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨R₂, hR₂, fun R hR => ?_⟩
  obtain ⟨C₂, hC₂, HL'⟩ := HL R hR
  intro Y hY ε hε μ hμ y
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 : P.p < 1 := P.hp_hi
  have hY0 : 0 < Y := by linarith [le_trans hR₂ hR]
  obtain ⟨⟨hcf, hv, hh⟩, -, -, -, hb⟩ := HL' Y hY ε hε μ hμ
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun z => res_chiY Y z * f z with hcfdef
  set v : ℝ → ℝ := res_vY P.p R ε μ Y with hvdef
  set h : ℝ → ℝ := c06_localized_bounds_hY P.p R ε μ Y with hhdef
  have hvh : (fun x => v x + h x) = cf := by
    funext x; simp only [hvdef, hhdef, hcfdef, c06_localized_bounds_hY]; ring
  have htop : ∀ n : ℕ, (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun n => WithTop.coe_le_coe.mpr le_top
  have dcf : Differentiable ℝ cf := hcf.differentiable (by simp)
  have dv : Differentiable ℝ v := hv.differentiable (by simp)
  have dh : Differentiable ℝ h := hh.differentiable (by simp)
  have bh1 : ∀ z, |deriv h z| ≤ C₂ * Y ^ (-P.p - 1) := fun z => by
    simpa using (hb z).1 1 (by norm_num)
  have bh2 : ∀ z, |deriv (deriv h) z| ≤ C₂ * Y ^ (-P.p - 2) := fun z => by
    have := (hb z).1 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bcf : ∀ z, |deriv cf z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.1 0 (by norm_num)
  have bcf2 : ∀ z, |deriv (deriv cf) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.1 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bv1 : ∀ z, |deriv v z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.2 0 (by norm_num)
  have bv2 : ∀ z, |deriv (deriv v) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have hpos : ∀ a : ℝ, 0 < C₂ * Y ^ a := fun a => by positivity
  have mS : ∀ (w : ℝ → ℝ), Continuous w → Measurable (fun s => c01_secant w y (y - s)) :=
    fun w hw => (c06_aux_secant_meas w hw).comp (measurable_const.prodMk measurable_id)
  set g : ℝ → ℝ := fun x => 2 * v x + h x with hgdef
  have dg : Differentiable ℝ g := (dv.const_mul 2).add dh
  have hdg : deriv g = fun x => 2 * deriv v x + deriv h x := by
    funext x; exact (((dv x).hasDerivAt.const_mul 2).add (dh x).hasDerivAt).deriv
  have bg : ∀ x, |deriv g x| ≤ 2 * (C₂ * Y ^ (-beta P.p)) + C₂ * Y ^ (-P.p - 1) := by
    intro x; rw [hdg]
    have h4 := abs_add_le (2 * deriv v x) (deriv h x)
    rw [abs_mul, abs_two] at h4
    linarith [bv1 x, bh1 x]
  -- integrability of the `s`-forms
  have IT1 := c06_aux_frac_integrable P.p hp0 hp1 h (hh.of_le (htop 2)) _ _ (hpos _) (hpos _)
    bh1 bh2 y (fun s => c01_secant (fun x => v x + h x) y (y - s) ^ 2)
    (by rw [hvh]; exact (mS cf dcf.continuous).pow_const 2) _
    (fun s => by
      rw [hvh, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (c06_aux_secant_le cf dcf _ bcf _ _) 2)
  have IT2 := c06_aux_frac_integrable P.p hp0 hp1 v (hv.of_le (htop 2)) _ _ (hpos _) (hpos _)
    bv1 bv2 y (fun s => c01_secant h y (y - s) * c01_secant g y (y - s))
    ((mS h dh.continuous).mul (mS g dg.continuous)) _
    (fun s => by
      rw [abs_mul]
      exact mul_le_mul (c06_aux_secant_le h dh _ bh1 _ _) (c06_aux_secant_le g dg _ bg _ _)
        (abs_nonneg _) (hpos _).le)
  have IT2' : Integrable (fun s : ℝ => (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) *
      c01_secant h y (y - s) * c01_secant (fun x => 2 * v x + h x) y (y - s)) :=
    IT2.congr (ae_of_all _ fun s => by simp only [hgdef]; ring)
  have Icf := c06_aux_frac_integrable P.p hp0 hp1 cf (hcf.of_le (htop 2)) _ _ (hpos _) (hpos _)
    bcf bcf2 y (fun s => c01_secant cf y (y - s) ^ 2) ((mS cf dcf.continuous).pow_const 2) _
    (fun s => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (c06_aux_secant_le cf dcf _ bcf _ _) 2)
  have Iv := c06_aux_frac_integrable P.p hp0 hp1 v (hv.of_le (htop 2)) _ _ (hpos _) (hpos _)
    bv1 bv2 y (fun s => c01_secant v y (y - s) ^ 2) ((mS v dv.continuous).pow_const 2) _
    (fun s => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (c06_aux_secant_le v dv _ bv1 _ _) 2)
  have key : ∀ (w : ℝ → ℝ) z, (deriv w y - deriv w z) / |y - z| ^ (P.p + 1) * c01_secant w y z ^ 2 =
      (fun s => (deriv w y - deriv w (y - s)) / |s| ^ (1 + P.p) * c01_secant w y (y - s) ^ 2)
        (y - z) := by
    intro w z; simp only [sub_sub_cancel, add_comm P.p 1]
  have zcf : Integrable (fun z : ℝ => (deriv cf y - deriv cf z) / |y - z| ^ (P.p + 1) *
      c01_secant cf y z ^ 2) :=
    ((c06_aux_change_var y _).1 Icf).congr (ae_of_all _ fun z => (key cf z).symm)
  have zv : Integrable (fun z : ℝ => (deriv v y - deriv v z) / |y - z| ^ (P.p + 1) *
      c01_secant v y z ^ 2) :=
    ((c06_aux_change_var y _).1 Iv).congr (ae_of_all _ fun z => (key v z).symm)
  refine ⟨?_, IT1, IT2', zcf, zv⟩
  -- the algebraic identity
  obtain ⟨-, -, -, LIN⟩ := c06_secant_calculus v (hv.of_le (htop 1)) ⟨_, bv1⟩
  have hc1 : ContDiff ℝ 1 v := hv.of_le (htop 1)
  have hh1 : ContDiff ℝ 1 h := hh.of_le (htop 1)
  have pt : ∀ s, (deriv cf y - deriv cf (y - s)) / |s| ^ (1 + P.p) * c01_secant cf y (y - s) ^ 2 -
      (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) * c01_secant v y (y - s) ^ 2 =
      (deriv h y - deriv h (y - s)) / |s| ^ (1 + P.p) *
        c01_secant (fun x => v x + h x) y (y - s) ^ 2 +
      (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) * c01_secant h y (y - s) *
        c01_secant (fun x => 2 * v x + h x) y (y - s) := by
    intro s
    have dcf' : ∀ x, deriv cf x = deriv v x + deriv h x := by
      intro x; rw [← hvh]; exact ((dv x).hasDerivAt.add (dh x).hasDerivAt).deriv
    have s1 := (LIN v h hc1 hh1 1 y (y - s)).1
    have s2 := (LIN (fun x => 2 * v x) h (contDiff_const.mul hc1) hh1 1 y (y - s)).1
    have s3 := (LIN v h hc1 hh1 2 y (y - s)).2
    rw [hvh] at s1 ⊢
    rw [s1, s2, s3, dcf', dcf']
    ring
  unfold residual_decomposition_E7 c04_cubic_part c06_E7_decomposition_T1
    c06_E7_decomposition_T2
  rw [← mul_sub, ← integral_sub zcf zv, ← integral_add IT1 IT2']
  congr 1
  have e1 := (c06_aux_change_var y (fun s =>
    (deriv cf y - deriv cf (y - s)) / |s| ^ (1 + P.p) * c01_secant cf y (y - s) ^ 2 -
      (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) * c01_secant v y (y - s) ^ 2)).2
  refine Eq.trans ?_ (e1.trans (integral_congr_ae (ae_of_all _ fun s => pt s)))
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [sub_sub_cancel, add_comm P.p 1]

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E7_value.  `|T_{7,1}| ≤ C Y^{-2p-1-2β}`, `|T_{7,2}| ≤ C Y^{-p-2β}`,
`|ℰ₇| ≤ C ε Y^{-p-2β}`. -/
theorem c06_E7_value (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y : ℝ,
        let v : ℝ → ℝ := res_vY P.p R ε μ Y
        let h : ℝ → ℝ := c06_localized_bounds_hY P.p R ε μ Y
        |c06_E7_decomposition_T1 P.p v h y| ≤ C * Y ^ (-2 * P.p - 1 - 2 * beta P.p) ∧
        |c06_E7_decomposition_T2 P.p v h y| ≤ C * Y ^ (-P.p - 2 * beta P.p) ∧
        |residual_decomposition_E7 P.p R ε μ Y y| ≤ C * ε * Y ^ (-P.p - 2 * beta P.p) := by
  obtain ⟨R₁, hR₁, HD⟩ := c06_E7_decomposition P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₂, hR₂, HL⟩ := c06_localized_bounds P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨max R₁ R₂, le_trans hR₁ (le_max_left _ _), fun R hR => ?_⟩
  have hR1 : R₁ ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : R₂ ≤ R := le_trans (le_max_right _ _) hR
  have hRone : 1 ≤ R := le_trans hR₁ hR1
  obtain ⟨C₂, hC₂, HL'⟩ := HL R hR2
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  set Cp : ℝ := (2 : ℝ) ^ (2 - P.p) * (1 / (1 - P.p) + 1 / P.p) with hCp
  have hCp0 : 0 < Cp := by
    have : 0 < 1 - P.p := by linarith
    positivity
  set K : ℝ := 3 * Cp * C₂ ^ 3 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K * (1 + (P.p + 1) * |calpha P.p|), by positivity, ?_⟩
  intro Y hY ε hε μ hμ y
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  obtain ⟨⟨hcf, hv, hh⟩, -, -, -, hb⟩ := HL' Y hY ε hε μ hμ
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun z => res_chiY Y z * f z with hcfdef
  set v : ℝ → ℝ := res_vY P.p R ε μ Y with hvdef
  set h : ℝ → ℝ := c06_localized_bounds_hY P.p R ε μ Y with hhdef
  have hvh : (fun x => v x + h x) = cf := by
    funext x; simp only [hvdef, hhdef, hcfdef, c06_localized_bounds_hY]; ring
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast WithTop.coe_lt_top _
  have dcf : Differentiable ℝ cf := hcf.differentiable (by simp)
  have dv : Differentiable ℝ v := hv.differentiable (by simp)
  have dh : Differentiable ℝ h := hh.differentiable (by simp)
  have ddv : Differentiable ℝ (deriv v) := by
    simpa using hv.differentiable_iteratedDeriv 1 htop1
  have ddh : Differentiable ℝ (deriv h) := by
    simpa using hh.differentiable_iteratedDeriv 1 htop1
  -- the pointwise bounds
  have bh1 : ∀ z, |deriv h z| ≤ C₂ * Y ^ (-P.p - 1) := fun z => by
    simpa using (hb z).1 1 (by norm_num)
  have bh2 : ∀ z, |deriv (deriv h) z| ≤ C₂ * Y ^ (-P.p - 2) := fun z => by
    have := (hb z).1 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bcf : ∀ z, |deriv cf z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.1 0 (by norm_num)
  have bv1 : ∀ z, |deriv v z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.2 0 (by norm_num)
  have bv2 : ∀ z, |deriv (deriv v) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have hYβ : Y ^ (-P.p - 1) ≤ Y ^ (-beta P.p) := by
    apply Real.rpow_le_rpow_of_exponent_le hY1
    have : beta P.p ≤ P.p + 1 := by
      unfold beta; rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hYb0 : 0 ≤ Y ^ (-beta P.p) := Real.rpow_nonneg hY0.le _
  -- secant bounds
  have sS : ∀ s, |c01_secant (fun x => v x + h x) y (y - s)| ≤ C₂ * Y ^ (-beta P.p) := by
    intro s; rw [hvh]; exact c06_aux_secant_le cf dcf _ bcf _ _
  have sh : ∀ s, |c01_secant h y (y - s)| ≤ C₂ * Y ^ (-P.p - 1) :=
    fun s => c06_aux_secant_le h dh _ bh1 _ _
  have hd2 : ∀ x, |deriv (fun x => 2 * v x + h x) x| ≤ 3 * C₂ * Y ^ (-beta P.p) := by
    intro x
    have : deriv (fun x => 2 * v x + h x) x = 2 * deriv v x + deriv h x :=
      (((dv x).hasDerivAt.const_mul 2).add (dh x).hasDerivAt).deriv
    rw [this]
    have h1 := bv1 x
    have h2 := bh1 x
    have h3 : C₂ * Y ^ (-P.p - 1) ≤ C₂ * Y ^ (-beta P.p) := by gcongr
    have h4 := abs_add_le (2 * deriv v x) (deriv h x)
    rw [abs_mul, abs_two] at h4
    linarith
  have s2 : ∀ s, |c01_secant (fun x => 2 * v x + h x) y (y - s)| ≤ 3 * C₂ * Y ^ (-beta P.p) :=
    fun s => c06_aux_secant_le (fun x => 2 * v x + h x) ((dv.const_mul 2).add dh) _ hd2 _ _
  -- T₁
  have hT1 : |c06_E7_decomposition_T1 P.p v h y| ≤ Cp * C₂ ^ 3 * Y ^ (-2 * P.p - 1 - 2 * beta P.p) := by
    have hA : 0 < C₂ * Y ^ (-P.p - 1) := by positivity
    have hB : 0 < C₂ * Y ^ (-P.p - 2) := by positivity
    have := c06_aux_frac_int_le P.p hp0 hp1 _ _ hA hB (deriv h) bh1
      (c06_aux_lip _ ddh _ bh2) y ((C₂ * Y ^ (-beta P.p)) ^ 2) (by positivity) _
      (fun s => by
        apply c06_aux_pt
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (sS s) 2)
    unfold c06_E7_decomposition_T1
    refine le_trans this (le_of_eq ?_)
    rw [show (2 : ℝ) ^ (2 - P.p) * (1 / (1 - P.p) + 1 / P.p) *
        (C₂ * Y ^ (-P.p - 1)) ^ (1 - P.p) * (C₂ * Y ^ (-P.p - 2)) ^ P.p =
        Cp * ((C₂ * Y ^ (-P.p - 1)) ^ (1 - P.p) * (C₂ * Y ^ (-P.p - 2)) ^ P.p) by
          rw [hCp]; ring]
    rw [c06_aux_interp C₂ Y _ _ P.p hC₂ hY0, mul_pow, ← Real.rpow_natCast (Y ^ (-beta P.p)),
      ← Real.rpow_mul hY0.le]
    have e : Y ^ (-2 * P.p - 1 - 2 * beta P.p) =
        Y ^ (-beta P.p * ((2 : ℕ) : ℝ)) * Y ^ ((-P.p - 1) * (1 - P.p) + (-P.p - 2) * P.p) := by
      rw [← Real.rpow_add hY0]; congr 1; push_cast; ring
    rw [e]; ring
  -- T₂
  have hT2 : |c06_E7_decomposition_T2 P.p v h y| ≤ 3 * Cp * C₂ ^ 3 * Y ^ (-P.p - 2 * beta P.p) := by
    have hA : 0 < C₂ * Y ^ (-beta P.p) := by positivity
    have hB : 0 < C₂ * Y ^ (-beta P.p + 1 / P.p) := by positivity
    have := c06_aux_frac_int_le P.p hp0 hp1 _ _ hA hB (deriv v) bv1
      (c06_aux_lip _ ddv _ bv2) y (C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p)))
      (by positivity) (fun s => (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) *
        c01_secant h y (y - s) * c01_secant (fun x => 2 * v x + h x) y (y - s))
      (fun s => by
        rw [mul_assoc]
        apply c06_aux_pt
        rw [abs_mul]
        exact mul_le_mul (sh s) (s2 s) (abs_nonneg _) (by positivity))
    unfold c06_E7_decomposition_T2
    refine le_trans this (le_of_eq ?_)
    rw [show (2 : ℝ) ^ (2 - P.p) * (1 / (1 - P.p) + 1 / P.p) *
        (C₂ * Y ^ (-beta P.p)) ^ (1 - P.p) * (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ P.p =
        Cp * ((C₂ * Y ^ (-beta P.p)) ^ (1 - P.p) * (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ P.p) by
          rw [hCp]; ring]
    rw [c06_aux_interp C₂ Y _ _ P.p hC₂ hY0]
    have e : Y ^ (-P.p - 2 * beta P.p) =
        Y ^ (-P.p - 1) * Y ^ (-beta P.p) *
          Y ^ (-beta P.p * (1 - P.p) + (-beta P.p + 1 / P.p) * P.p) := by
      rw [← Real.rpow_add hY0, ← Real.rpow_add hY0]; congr 1; field_simp; ring
    rw [e]; ring
  have hYc : Y ^ (-2 * P.p - 1 - 2 * beta P.p) ≤ Y ^ (-P.p - 2 * beta P.p) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hY2 : 0 ≤ Y ^ (-P.p - 2 * beta P.p) := Real.rpow_nonneg hY0.le _
  have hT1' : |c06_E7_decomposition_T1 P.p v h y| ≤ K * Y ^ (-P.p - 2 * beta P.p) := by
    calc _ ≤ Cp * C₂ ^ 3 * Y ^ (-2 * P.p - 1 - 2 * beta P.p) := hT1
      _ ≤ Cp * C₂ ^ 3 * Y ^ (-P.p - 2 * beta P.p) := by gcongr
      _ ≤ K * Y ^ (-P.p - 2 * beta P.p) := by
        rw [hK]; linarith [mul_nonneg (mul_nonneg hCp0.le (pow_nonneg hC₂.le 3)) hY2]
  have hT2' : |c06_E7_decomposition_T2 P.p v h y| ≤ K * Y ^ (-P.p - 2 * beta P.p) := by
    rw [hK]; exact hT2
  have hKY : 0 ≤ K * Y ^ (-P.p - 2 * beta P.p) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc _ ≤ K * Y ^ (-2 * P.p - 1 - 2 * beta P.p) := by
          refine le_trans hT1 ?_
          rw [hK]
          have := Real.rpow_nonneg hY0.le (-2 * P.p - 1 - 2 * beta P.p)
          linarith [mul_nonneg (mul_nonneg hCp0.le (pow_nonneg hC₂.le 3)) this]
      _ ≤ K * (1 + (P.p + 1) * |calpha P.p|) * Y ^ (-2 * P.p - 1 - 2 * beta P.p) := by
          have := Real.rpow_nonneg hY0.le (-2 * P.p - 1 - 2 * beta P.p)
          have : 0 ≤ (P.p + 1) * |calpha P.p| := by positivity
          linarith [mul_nonneg (mul_nonneg hK0.le this) (Real.rpow_nonneg hY0.le
            (-2 * P.p - 1 - 2 * beta P.p))]
  · calc _ ≤ K * Y ^ (-P.p - 2 * beta P.p) := hT2'
      _ ≤ K * (1 + (P.p + 1) * |calpha P.p|) * Y ^ (-P.p - 2 * beta P.p) := by
          have : 0 ≤ (P.p + 1) * |calpha P.p| := by positivity
          linarith [mul_nonneg (mul_nonneg hK0.le this) hY2]
  · have hdec := (HD R hR1 Y hY ε hε μ hμ y).1
    rw [hdec, abs_mul]
    have hκ : |c04_cubic_part_kappa P.p ε| = (P.p + 1) * ε * |calpha P.p| / 2 := by
      unfold c04_cubic_part_kappa
      rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ P.p + 1),
        abs_of_nonneg hε0, abs_two]
    rw [hκ]
    have hsum : |c06_E7_decomposition_T1 P.p v h y + c06_E7_decomposition_T2 P.p v h y| ≤
        2 * (K * Y ^ (-P.p - 2 * beta P.p)) := by
      have := abs_add_le (c06_E7_decomposition_T1 P.p v h y) (c06_E7_decomposition_T2 P.p v h y)
      linarith
    have hc0 : 0 ≤ (P.p + 1) * ε * |calpha P.p| / 2 := by positivity
    calc (P.p + 1) * ε * |calpha P.p| / 2 *
          |c06_E7_decomposition_T1 P.p v h y + c06_E7_decomposition_T2 P.p v h y|
        ≤ (P.p + 1) * ε * |calpha P.p| / 2 * (2 * (K * Y ^ (-P.p - 2 * beta P.p))) :=
          mul_le_mul_of_nonneg_left hsum hc0
      _ = (P.p + 1) * |calpha P.p| * K * ε * Y ^ (-P.p - 2 * beta P.p) := by ring
      _ ≤ K * (1 + (P.p + 1) * |calpha P.p|) * ε * Y ^ (-P.p - 2 * beta P.p) := by
          have h0 : 0 ≤ ε * Y ^ (-P.p - 2 * beta P.p) := by positivity
          have e : K * (1 + (P.p + 1) * |calpha P.p|) * ε * Y ^ (-P.p - 2 * beta P.p) =
              (P.p + 1) * |calpha P.p| * K * ε * Y ^ (-P.p - 2 * beta P.p) +
                K * (ε * Y ^ (-P.p - 2 * beta P.p)) := by ring
          rw [e]; linarith [mul_nonneg hK0.le h0]

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E7_derivative.  `ℰ₇` is differentiable with
`|∂_y ℰ₇| ≤ C ε Y^{-p-2β+1/p}`. -/
theorem c06_E7_derivative (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        Differentiable ℝ (residual_decomposition_E7 P.p R ε μ Y) ∧
        ∀ y : ℝ, |deriv (residual_decomposition_E7 P.p R ε μ Y) y| ≤
          C * ε * Y ^ (-P.p - 2 * beta P.p + 1 / P.p) := by
  obtain ⟨R₁, hR₁, HD⟩ := c06_E7_decomposition P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₂, hR₂, HL⟩ := c06_localized_bounds P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨max R₁ R₂, le_trans hR₁ (le_max_left _ _), fun R hR => ?_⟩
  have hR1 : R₁ ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : R₂ ≤ R := le_trans (le_max_right _ _) hR
  have hRone : 1 ≤ R := le_trans hR₁ hR1
  obtain ⟨C₂, hC₂, HL'⟩ := HL R hR2
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hβ : beta P.p ≤ P.p + 1 := by
    unfold beta; rw [div_le_iff₀ (by linarith)]; nlinarith
  set Cp : ℝ := (2 : ℝ) ^ (2 - P.p) * (1 / (1 - P.p) + 1 / P.p) with hCp
  have hCp0 : 0 < Cp := by
    have : 0 < 1 - P.p := by linarith
    positivity
  refine ⟨12 * Cp * C₂ ^ 3 * ((P.p + 1) * |calpha P.p| + 1), by positivity, ?_⟩
  intro Y hY ε hε μ hμ
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  obtain ⟨⟨hcf, hv, hh⟩, -, -, -, hb⟩ := HL' Y hY ε hε μ hμ
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun z => res_chiY Y z * f z with hcfdef
  set v : ℝ → ℝ := res_vY P.p R ε μ Y with hvdef
  set h : ℝ → ℝ := c06_localized_bounds_hY P.p R ε μ Y with hhdef
  set g : ℝ → ℝ := fun x => 2 * v x + h x with hgdef
  have hvh : (fun x => v x + h x) = cf := by
    funext x; simp only [hvdef, hhdef, hcfdef, c06_localized_bounds_hY]; ring
  have htop : ∀ n : ℕ, (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun n => WithTop.coe_le_coe.mpr le_top
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast WithTop.coe_lt_top _
  have htop2 : ((2 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
  have dcf : Differentiable ℝ cf := hcf.differentiable (by simp)
  have dv : Differentiable ℝ v := hv.differentiable (by simp)
  have dh : Differentiable ℝ h := hh.differentiable (by simp)
  have ddcf : Differentiable ℝ (deriv cf) := by
    simpa using hcf.differentiable_iteratedDeriv 1 htop1
  have ddv : Differentiable ℝ (deriv v) := by
    simpa using hv.differentiable_iteratedDeriv 1 htop1
  have ddh : Differentiable ℝ (deriv h) := by
    simpa using hh.differentiable_iteratedDeriv 1 htop1
  have dddv : Differentiable ℝ (deriv (deriv v)) := by
    have := hv.differentiable_iteratedDeriv 2 htop2
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this; exact this
  have dddh : Differentiable ℝ (deriv (deriv h)) := by
    have := hh.differentiable_iteratedDeriv 2 htop2
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this; exact this
  have dg : Differentiable ℝ g := (dv.const_mul 2).add dh
  have hdg : deriv g = fun x => 2 * deriv v x + deriv h x := by
    funext x; exact (((dv x).hasDerivAt.const_mul 2).add (dh x).hasDerivAt).deriv
  have ddg : Differentiable ℝ (deriv g) := by rw [hdg]; exact (ddv.const_mul 2).add ddh
  have hddg : ∀ x, deriv (deriv g) x = 2 * deriv (deriv v) x + deriv (deriv h) x := by
    intro x; rw [hdg]; exact (((ddv x).hasDerivAt.const_mul 2).add (ddh x).hasDerivAt).deriv
  have hg2 : ContDiff ℝ 2 g := ((contDiff_const.mul (hv.of_le (htop 2))).add (hh.of_le (htop 2)))
  -- the pointwise bounds
  have bh1 : ∀ z, |deriv h z| ≤ C₂ * Y ^ (-P.p - 1) := fun z => by
    simpa using (hb z).1 1 (by norm_num)
  have bh2 : ∀ z, |deriv (deriv h) z| ≤ C₂ * Y ^ (-P.p - 2) := fun z => by
    have := (hb z).1 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bh3 : ∀ z, |deriv (deriv (deriv h)) z| ≤ C₂ * Y ^ (-P.p - 3) := fun z => by
    have := (hb z).1 3 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bcf : ∀ z, |deriv cf z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.1 0 (by norm_num)
  have bcf2 : ∀ z, |deriv (deriv cf) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.1 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bv1 : ∀ z, |deriv v z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.2 0 (by norm_num)
  have bv2 : ∀ z, |deriv (deriv v) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bv3 : ∀ z, |deriv (deriv (deriv v)) z| ≤ C₂ * Y ^ (-beta P.p + 2 / P.p) := fun z => by
    have := (hb z).2.2.2 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have hYβ : Y ^ (-P.p - 1) ≤ Y ^ (-beta P.p) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hYβ' : Y ^ (-P.p - 2) ≤ Y ^ (-beta P.p + 1 / P.p) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have bg1 : ∀ x, |deriv g x| ≤ 3 * C₂ * Y ^ (-beta P.p) := by
    intro x
    rw [hdg]
    have h1 := bv1 x
    have h2 := bh1 x
    have h3 : C₂ * Y ^ (-P.p - 1) ≤ C₂ * Y ^ (-beta P.p) := by gcongr
    have h4 := abs_add_le (2 * deriv v x) (deriv h x)
    rw [abs_mul, abs_two] at h4
    linarith
  have bg2 : ∀ x, |deriv (deriv g) x| ≤ 3 * C₂ * Y ^ (-beta P.p + 1 / P.p) := by
    intro x
    rw [hddg]
    have h1 := bv2 x
    have h2 := bh2 x
    have h3 : C₂ * Y ^ (-P.p - 2) ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := by gcongr
    have h4 := abs_add_le (2 * deriv (deriv v) x) (deriv (deriv h) x)
    rw [abs_mul, abs_two] at h4
    linarith
  -- secants and their derivatives
  have sS := fun y s => c06_aux_secant_le cf dcf _ bcf y (y - s)
  have sS' := fun y s => c06_aux_secant_le _ ddcf _ bcf2 y (y - s)
  have sh := fun y s => c06_aux_secant_le h dh _ bh1 y (y - s)
  have sh' := fun y s => c06_aux_secant_le _ ddh _ bh2 y (y - s)
  have sg := fun y s => c06_aux_secant_le g dg _ bg1 y (y - s)
  have sg' := fun y s => c06_aux_secant_le _ ddg _ bg2 y (y - s)
  have dS := c06_aux_sec_hasDeriv cf (hcf.of_le (htop 2)) _ _ bcf bcf2
  have dSh := c06_aux_sec_hasDeriv h (hh.of_le (htop 2)) _ _ bh1 bh2
  have dSg := c06_aux_sec_hasDeriv g hg2 _ _ bg1 bg2
  have mS := c06_aux_secant_meas cf dcf.continuous
  have mS' := c06_aux_secant_meas _ ddcf.continuous
  have mSh := c06_aux_secant_meas h dh.continuous
  have mSh' := c06_aux_secant_meas _ ddh.continuous
  have mSg := c06_aux_secant_meas g dg.continuous
  have mSg' := c06_aux_secant_meas _ ddg.continuous
  have hpos : ∀ a : ℝ, 0 < C₂ * Y ^ a := fun a => by positivity
  -- T₁
  have TD1 := fun y => c06_aux_TD P.p hp0 hp1 h (hh.of_le (htop 3)) _ _ _ (hpos _) (hpos _)
    (hpos _) bh1 bh2 bh3 (fun y s => c01_secant cf y (y - s) ^ 2)
    (fun y s => 2 * c01_secant cf y (y - s) * c01_secant (deriv cf) y (y - s))
    (mS.pow_const 2) ((mS.const_mul 2).mul mS')
    (fun y s => ((dS y s).pow 2).congr_deriv (by push_cast; ring))
    ((C₂ * Y ^ (-beta P.p)) ^ 2) (2 * (C₂ * Y ^ (-beta P.p)) * (C₂ * Y ^ (-beta P.p + 1 / P.p)))
    (fun y s => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (sS y s) 2)
    (fun y s => by
      rw [abs_mul, abs_mul, abs_two]
      have := sS y s; have := sS' y s
      apply mul_le_mul (mul_le_mul_of_nonneg_left (sS y s) (by norm_num)) (sS' y s)
        (abs_nonneg _) (by positivity)) y
  -- T₂
  have TD2 := fun y => c06_aux_TD P.p hp0 hp1 v (hv.of_le (htop 3)) _ _ _ (hpos _) (hpos _)
    (hpos _) bv1 bv2 bv3 (fun y s => c01_secant h y (y - s) * c01_secant g y (y - s))
    (fun y s => c01_secant (deriv h) y (y - s) * c01_secant g y (y - s) +
      c01_secant h y (y - s) * c01_secant (deriv g) y (y - s))
    (mSh.mul mSg) ((mSh'.mul mSg).add (mSh.mul mSg'))
    (fun y s => (dSh y s).mul (dSg y s))
    (C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p)))
    (C₂ * Y ^ (-P.p - 2) * (3 * C₂ * Y ^ (-beta P.p)) +
      C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p + 1 / P.p)))
    (fun y s => by
      rw [abs_mul]; exact mul_le_mul (sh y s) (sg y s) (abs_nonneg _) (hpos _).le)
    (fun y s => by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul (sh' y s) (sg y s) (abs_nonneg _) (hpos _).le
      · exact mul_le_mul (sh y s) (sg' y s) (abs_nonneg _) (hpos _).le) y
  -- identification of E₇
  have hE : residual_decomposition_E7 P.p R ε μ Y = fun y => c04_cubic_part_kappa P.p ε *
      ((∫ s, (deriv h y - deriv h (y - s)) / |s| ^ (1 + P.p) * c01_secant cf y (y - s) ^ 2) +
       (∫ s, (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) *
          (c01_secant h y (y - s) * c01_secant g y (y - s)))) := by
    funext y
    rw [(HD R hR1 Y hY ε hε μ hμ y).1]
    unfold c06_E7_decomposition_T1 c06_E7_decomposition_T2
    rw [hvh]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hgdef]; ring
  have hderE : ∀ y, HasDerivAt (residual_decomposition_E7 P.p R ε μ Y)
      (c04_cubic_part_kappa P.p ε * ((∫ s, ((deriv (deriv h) y - deriv (deriv h) (y - s)) *
          c01_secant cf y (y - s) ^ 2 + (deriv h y - deriv h (y - s)) *
          (2 * c01_secant cf y (y - s) * c01_secant (deriv cf) y (y - s))) / |s| ^ (1 + P.p)) +
        (∫ s, ((deriv (deriv v) y - deriv (deriv v) (y - s)) *
          (c01_secant h y (y - s) * c01_secant g y (y - s)) +
          (deriv v y - deriv v (y - s)) * (c01_secant (deriv h) y (y - s) *
            c01_secant g y (y - s) + c01_secant h y (y - s) * c01_secant (deriv g) y (y - s))) /
            |s| ^ (1 + P.p)))) y := by
    intro y
    rw [hE]
    exact ((TD1 y).1.add (TD2 y).1).const_mul _
  refine ⟨fun y => (hderE y).differentiableAt, fun y => ?_⟩
  rw [(hderE y).deriv, abs_mul]
  set T := -P.p - 2 * beta P.p + 1 / P.p with hT
  have hYT : 0 ≤ Y ^ T := Real.rpow_nonneg hY0.le _
  have hC3 : 0 ≤ C₂ ^ 3 := by positivity
  -- bound for the first derivative integral
  have b1 := (TD1 y).2
  have e1 : (-P.p - 2) * (1 - P.p) + (-P.p - 3) * P.p = -2 - 2 * P.p := by ring
  have e2 : (-P.p - 1) * (1 - P.p) + (-P.p - 2) * P.p = -1 - 2 * P.p := by ring
  have t11 : (C₂ * Y ^ (-beta P.p)) ^ 2 * (C₂ * Y ^ (-P.p - 2)) ^ (1 - P.p) * (C₂ * Y ^ (-P.p - 3)) ^ P.p ≤ C₂ ^ 3 * Y ^ T := by
    rw [mul_assoc, c06_aux_interp C₂ Y _ _ P.p hC₂ hY0, e1]
    have : (C₂ * Y ^ (-beta P.p)) ^ 2 * (C₂ * Y ^ (-2 - 2 * P.p)) =
        C₂ ^ 3 * (Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-2 - 2 * P.p)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (c06_aux_mono3 _ _ _ _ _ hY1 (by
      have : 0 < 1 / P.p := by positivity
      linarith)) hC3
  have t12 : 2 * (C₂ * Y ^ (-beta P.p)) * (C₂ * Y ^ (-beta P.p + 1 / P.p)) *
      (C₂ * Y ^ (-P.p - 1)) ^ (1 - P.p) * (C₂ * Y ^ (-P.p - 2)) ^ P.p ≤ 2 * (C₂ ^ 3 * Y ^ T) := by
    rw [mul_assoc, c06_aux_interp C₂ Y _ _ P.p hC₂ hY0, e2]
    have : 2 * (C₂ * Y ^ (-beta P.p)) * (C₂ * Y ^ (-beta P.p + 1 / P.p)) *
        (C₂ * Y ^ (-1 - 2 * P.p)) =
        2 * (C₂ ^ 3 * (Y ^ (-beta P.p) * Y ^ (-beta P.p + 1 / P.p) * Y ^ (-1 - 2 * P.p))) := by
      ring
    rw [this]
    gcongr
    exact c06_aux_mono3 _ _ _ _ _ hY1 (by linarith)
  have B1 : |∫ s, ((deriv (deriv h) y - deriv (deriv h) (y - s)) *
          c01_secant cf y (y - s) ^ 2 + (deriv h y - deriv h (y - s)) *
          (2 * c01_secant cf y (y - s) * c01_secant (deriv cf) y (y - s))) / |s| ^ (1 + P.p)| ≤
      3 * Cp * C₂ ^ 3 * Y ^ T := by
    refine le_trans b1 ?_
    rw [← hCp]
    have := mul_le_mul_of_nonneg_left (add_le_add t11 t12) hCp0.le
    linarith
  -- bound for the second derivative integral
  have b2 := (TD2 y).2
  have e3 : (-beta P.p + 1 / P.p) * (1 - P.p) + (-beta P.p + 2 / P.p) * P.p =
      -beta P.p + 1 + 1 / P.p := by field_simp; ring
  have e4 : -beta P.p * (1 - P.p) + (-beta P.p + 1 / P.p) * P.p = -beta P.p + 1 := by
    field_simp; ring
  have t21 : C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p)) *
      (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ (1 - P.p) * (C₂ * Y ^ (-beta P.p + 2 / P.p)) ^ P.p ≤
        3 * (C₂ ^ 3 * Y ^ T) := by
    rw [mul_assoc, c06_aux_interp C₂ Y _ _ P.p hC₂ hY0, e3]
    have : C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p)) *
        (C₂ * Y ^ (-beta P.p + 1 + 1 / P.p)) =
        3 * (C₂ ^ 3 * (Y ^ (-P.p - 1) * Y ^ (-beta P.p) * Y ^ (-beta P.p + 1 + 1 / P.p))) := by
      ring
    rw [this]
    gcongr
    exact c06_aux_mono3 _ _ _ _ _ hY1 (by linarith)
  have t22 : (C₂ * Y ^ (-P.p - 2) * (3 * C₂ * Y ^ (-beta P.p)) +
      C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p + 1 / P.p))) *
      (C₂ * Y ^ (-beta P.p)) ^ (1 - P.p) * (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ P.p ≤
        6 * (C₂ ^ 3 * Y ^ T) := by
    rw [mul_assoc, c06_aux_interp C₂ Y _ _ P.p hC₂ hY0, e4]
    have : (C₂ * Y ^ (-P.p - 2) * (3 * C₂ * Y ^ (-beta P.p)) +
        C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p + 1 / P.p))) *
        (C₂ * Y ^ (-beta P.p + 1)) =
        3 * (C₂ ^ 3 * (Y ^ (-P.p - 2) * Y ^ (-beta P.p) * Y ^ (-beta P.p + 1))) +
        3 * (C₂ ^ 3 * (Y ^ (-P.p - 1) * Y ^ (-beta P.p + 1 / P.p) * Y ^ (-beta P.p + 1))) := by
      ring
    rw [this]
    have k1 : C₂ ^ 3 * (Y ^ (-P.p - 2) * Y ^ (-beta P.p) * Y ^ (-beta P.p + 1)) ≤
        C₂ ^ 3 * Y ^ T := by
      gcongr; exact c06_aux_mono3 _ _ _ _ _ hY1 (by linarith)
    have k2 : C₂ ^ 3 * (Y ^ (-P.p - 1) * Y ^ (-beta P.p + 1 / P.p) * Y ^ (-beta P.p + 1)) ≤
        C₂ ^ 3 * Y ^ T := by
      gcongr; exact c06_aux_mono3 _ _ _ _ _ hY1 (by linarith)
    linarith
  have B2 : |∫ s, ((deriv (deriv v) y - deriv (deriv v) (y - s)) *
          (c01_secant h y (y - s) * c01_secant g y (y - s)) +
          (deriv v y - deriv v (y - s)) * (c01_secant (deriv h) y (y - s) *
            c01_secant g y (y - s) + c01_secant h y (y - s) * c01_secant (deriv g) y (y - s))) /
            |s| ^ (1 + P.p)| ≤ 9 * Cp * C₂ ^ 3 * Y ^ T := by
    refine le_trans b2 ?_
    rw [← hCp]
    have := mul_le_mul_of_nonneg_left (add_le_add t21 t22) hCp0.le
    linarith
  have hκ : |c04_cubic_part_kappa P.p ε| = (P.p + 1) * ε * |calpha P.p| / 2 := by
    unfold c04_cubic_part_kappa
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ P.p + 1),
      abs_of_nonneg hε0, abs_two]
  rw [hκ]
  have hsum := le_trans (abs_add_le _ _) (add_le_add B1 B2)
  have hc0 : 0 ≤ (P.p + 1) * ε * |calpha P.p| / 2 := by positivity
  have hX : 0 ≤ Cp * C₂ ^ 3 * ε * Y ^ T := by positivity
  calc _ ≤ (P.p + 1) * ε * |calpha P.p| / 2 * (3 * Cp * C₂ ^ 3 * Y ^ T + 9 * Cp * C₂ ^ 3 * Y ^ T) :=
        mul_le_mul_of_nonneg_left hsum hc0
    _ = 6 * (P.p + 1) * |calpha P.p| * (Cp * C₂ ^ 3 * ε * Y ^ T) := by ring
    _ ≤ 12 * Cp * C₂ ^ 3 * ((P.p + 1) * |calpha P.p| + 1) * ε * Y ^ T := by
        have e : 12 * Cp * C₂ ^ 3 * ((P.p + 1) * |calpha P.p| + 1) * ε * Y ^ T =
            6 * (P.p + 1) * |calpha P.p| * (Cp * C₂ ^ 3 * ε * Y ^ T) +
            (6 * (P.p + 1) * |calpha P.p| * (Cp * C₂ ^ 3 * ε * Y ^ T) +
              12 * (Cp * C₂ ^ 3 * ε * Y ^ T)) := by ring
        rw [e]
        have : 0 ≤ 6 * (P.p + 1) * |calpha P.p| * (Cp * C₂ ^ 3 * ε * Y ^ T) := by positivity
        linarith

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:approx_E7.  Control of `ℰ₇` on `[Y,2Y]`. -/
theorem approx_E7 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (residual_decomposition_E7 P.p R ε μ Y) y| ≤
            C * ε * jb y ^ (-P.p - 2 * beta P.p + j / P.p) ∧
          C * ε * jb y ^ (-P.p - 2 * beta P.p + j / P.p) ≤
            C * ε * jb y ^ (-2 * P.p - 1 + j / P.p) := by
  obtain ⟨R₁, hR₁, H1⟩ := c06_E7_value P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₂, hR₂, H2⟩ := c06_E7_derivative P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨max R₁ R₂, le_trans hR₁ (le_max_left _ _), fun R hR => ?_⟩
  obtain ⟨C₁, hC₁, h1⟩ := H1 R (le_trans (le_max_left _ _) hR)
  obtain ⟨C₂, hC₂, h2⟩ := H2 R (le_trans (le_max_right _ _) hR)
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  have h2b := c06_aux_two_beta P.p hp0
  have hinv : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  set b := P.p + 2 * beta P.p with hb
  have hb0 : 0 ≤ b - 1 / P.p := by rw [hb, h2b]; linarith
  refine ⟨(3 : ℝ) ^ b * (C₁ + C₂), by positivity, ?_⟩
  intro Y hY ε hε μ hμ y hy j hj
  have hR1 : 1 ≤ R := le_trans hR₁ (le_trans (le_max_left _ _) hR)
  have hY1 : 1 ≤ Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have h3b : (1 : ℝ) ≤ (3 : ℝ) ^ b := Real.one_le_rpow (by norm_num) (by linarith)
  constructor
  · interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
      have := (h1 Y hY ε hε μ hμ y).2.2
      have hc := c06_aux_Y_le_jb b Y y (by linarith) hY1 hy.1 hy.2
      rw [show -P.p - 2 * beta P.p = -b by rw [hb]; ring]
      calc _ ≤ C₁ * ε * Y ^ (-b) := by rw [show -b = -P.p - 2 * beta P.p by rw [hb]; ring]; exact this
        _ ≤ C₁ * ε * ((3 : ℝ) ^ b * jb y ^ (-b)) := by gcongr
        _ ≤ (3 : ℝ) ^ b * (C₁ + C₂) * ε * jb y ^ (-b) := by
          have := Real.rpow_nonneg (c06_aux_jb_pos y).le (-b)
          have : 0 ≤ (3:ℝ) ^ b := by positivity
          nlinarith [mul_nonneg (mul_nonneg this hε0) (Real.rpow_nonneg (c06_aux_jb_pos y).le (-b)),
            mul_nonneg (mul_nonneg (mul_nonneg this hC₂.le) hε0) (Real.rpow_nonneg (c06_aux_jb_pos y).le (-b))]
    · simp only [iteratedDeriv_one, Nat.cast_one]
      have := (h2 Y hY ε hε μ hμ).2 y
      have hc := c06_aux_Y_le_jb (b - 1 / P.p) Y y hb0 hY1 hy.1 hy.2
      have h3' : (3 : ℝ) ^ (b - 1 / P.p) ≤ (3 : ℝ) ^ b :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [show -P.p - 2 * beta P.p + 1 / P.p = -(b - 1 / P.p) by rw [hb]; ring] at this ⊢
      have hj0 := Real.rpow_nonneg (c06_aux_jb_pos y).le (-(b - 1 / P.p))
      calc _ ≤ C₂ * ε * Y ^ (-(b - 1 / P.p)) := this
        _ ≤ C₂ * ε * ((3 : ℝ) ^ (b - 1 / P.p) * jb y ^ (-(b - 1 / P.p))) := by gcongr
        _ ≤ C₂ * ε * ((3 : ℝ) ^ b * jb y ^ (-(b - 1 / P.p))) := by gcongr
        _ ≤ (3 : ℝ) ^ b * (C₁ + C₂) * ε * jb y ^ (-(b - 1 / P.p)) := by
          have : 0 ≤ (3:ℝ) ^ b := by positivity
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg this hC₁.le) hε0) hj0]
  · have : (0 : ℝ) ≤ (3 : ℝ) ^ b * (C₁ + C₂) * ε := by positivity
    apply mul_le_mul_of_nonneg_left _ this
    apply Real.rpow_le_rpow_of_exponent_le (c06_aux_one_le_jb y)
    have : P.p ≤ 1 / P.p := by linarith
    linarith

/-! ## Control of `ℰ₈` -/

/-- Blueprint: lem:c06_quintic_representation.
`𝒬_ε(w) - 𝒬_{ε,3}(w) = ∫ (w'(y)-w'(y-s))/|s|^{1+p} · Ã_ε(S_w(y,y-s)) ds`. -/
theorem c06_quintic_representation (P : parameters) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w) (hw1 : ∃ M, ∀ x, |deriv w x| ≤ M)
    (hw2 : ∃ M, ∀ x, |deriv (deriv w) x| ≤ M) (y : ℝ) :
    Integrable (fun z : ℝ => (deriv w y - deriv w z) / |y - z| ^ (P.p + 1) *
      (A_eps P.p ε (c01_secant w y z) - 1)) ∧
    Integrable (fun z : ℝ => (deriv w y - deriv w z) / |y - z| ^ (P.p + 1) *
      c01_secant w y z ^ 2) ∧
    Integrable (fun s : ℝ => (deriv w y - deriv w (y - s)) / |s| ^ (1 + P.p) *
      c06_A_eps_bounds_quintic P.p ε (c01_secant w y (y - s))) ∧
    c01_Q_eps P.p ε w y - c04_cubic_part P.p ε w y =
      ∫ s, (deriv w y - deriv w (y - s)) / |s| ^ (1 + P.p) *
        c06_A_eps_bounds_quintic P.p ε (c01_secant w y (y - s)) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 : P.p < 1 := P.hp_hi
  obtain ⟨M₁, hM₁⟩ := hw1
  obtain ⟨M₂, hM₂⟩ := hw2
  set B₁ := max M₁ 1 with hB₁
  set B₂ := max M₂ 1 with hB₂
  have b1 : ∀ x, |deriv w x| ≤ B₁ := fun x => le_trans (hM₁ x) (le_max_left _ _)
  have b2 : ∀ x, |deriv (deriv w) x| ≤ B₂ := fun x => le_trans (hM₂ x) (le_max_left _ _)
  have hB₁0 : 0 < B₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB₂0 : 0 < B₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have dw : Differentiable ℝ w := hw.differentiable (by norm_num)
  have mS : Measurable (fun s => c01_secant w y (y - s)) :=
    (c06_aux_secant_meas w dw.continuous).comp (measurable_const.prodMk measurable_id)
  have sS : ∀ s, |c01_secant w y (y - s)| ≤ B₁ := fun s => c06_aux_secant_le w dw _ b1 _ _
  have hAc : Continuous (A_eps P.p ε) := by
    unfold A_eps
    exact (continuous_const.add (continuous_const.mul (continuous_pow 2))).rpow_const
      (fun u => Or.inl (by
        show (1 : ℝ) + ε * u ^ 2 ≠ 0
        exact ne_of_gt (by nlinarith [mul_nonneg hε (sq_nonneg u)])))
  have FI := c06_aux_frac_integrable P.p hp0 hp1 w hw B₁ B₂ hB₁0 hB₂0 b1 b2 y
  -- the three `s`-form integrands
  have IA := FI (fun s => A_eps P.p ε (c01_secant w y (y - s)) - 1)
    ((hAc.measurable.comp mS).sub measurable_const) 1
    (fun s => c06_aux_A_sub_one _ _ _ hp0 hε)
  have I2 := FI (fun s => c01_secant w y (y - s) ^ 2) (mS.pow_const 2) (B₁ ^ 2)
    (fun s => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (sS s) 2)
  have IQ := FI (fun s => c06_A_eps_bounds_quintic P.p ε (c01_secant w y (y - s)))
    (by unfold c06_A_eps_bounds_quintic
        exact measurable_const.mul (((hAc.measurable.comp mS).sub measurable_const).add
          (measurable_const.mul (mS.pow_const 2))))
    (|calpha P.p| * (1 + (P.p + 1) / 2 * ε * B₁ ^ 2))
    (fun s => by
      unfold c06_A_eps_bounds_quintic
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine le_trans (abs_add_le _ _) (add_le_add (c06_aux_A_sub_one _ _ _ hp0 hε) ?_)
      have : 0 ≤ (P.p + 1) / 2 * ε := by positivity
      rw [abs_mul, abs_of_nonneg this, abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (sS s) 2) this)
  -- the `z`-form integrands are the `s`-form ones composed with `z ↦ y - z`
  have key : ∀ (Ψ : ℝ → ℝ) z, (deriv w y - deriv w z) / |y - z| ^ (P.p + 1) * Ψ (c01_secant w y z) =
      (fun s => (deriv w y - deriv w (y - s)) / |s| ^ (1 + P.p) * Ψ (c01_secant w y (y - s)))
        (y - z) := by
    intro Ψ z; simp only [sub_sub_cancel, add_comm P.p 1]
  have zA : Integrable (fun z : ℝ => (deriv w y - deriv w z) / |y - z| ^ (P.p + 1) *
      (A_eps P.p ε (c01_secant w y z) - 1)) := by
    have := (c06_aux_change_var y _).1 IA
    refine this.congr (ae_of_all _ fun z => ?_)
    exact (key (fun u => A_eps P.p ε u - 1) z).symm
  have z2 : Integrable (fun z : ℝ => (deriv w y - deriv w z) / |y - z| ^ (P.p + 1) *
      c01_secant w y z ^ 2) := by
    have := (c06_aux_change_var y _).1 I2
    refine this.congr (ae_of_all _ fun z => ?_)
    exact (key (fun u => u ^ 2) z).symm
  refine ⟨zA, z2, IQ, ?_⟩
  unfold c01_Q_eps c04_cubic_part
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (zA.const_mul _) (z2.const_mul _)]
  rw [← (c06_aux_change_var y _).2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [sub_sub_cancel, add_comm P.p 1, c04_cubic_part_kappa, c06_A_eps_bounds_quintic]
  ring

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:approx_E8.  Control of `ℰ₈`. -/
theorem approx_E8 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        Differentiable ℝ (residual_decomposition_E8 P.p R ε μ Y) ∧
        (∀ y : ℝ,
          |residual_decomposition_E8 P.p R ε μ Y y| ≤ C * ε ^ 2 * Y ^ (1 - 5 * beta P.p) ∧
          |deriv (residual_decomposition_E8 P.p R ε μ Y) y| ≤
            C * ε ^ 2 * Y ^ (1 - 5 * beta P.p + 1 / P.p)) ∧
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (residual_decomposition_E8 P.p R ε μ Y) y| ≤
            C * ε ^ 2 * jb y ^ (-2 * P.p - 1 + j / P.p) := by
  obtain ⟨R₂, hR₂, HL⟩ := c06_localized_bounds P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  obtain ⟨CA, hCA, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₂, hR₂, fun R hR => ?_⟩
  have hRone : 1 ≤ R := le_trans hR₂ hR
  obtain ⟨C₂, hC₂, HL'⟩ := HL R hR
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hinv2 : 1 / P.p < 4 / 3 := by rw [div_lt_iff₀ hp0]; linarith
  have h5b : 1 - 5 * beta P.p ≤ -2 * P.p - 1 := by
    have : 2 * P.p * P.p < 2 := by nlinarith
    have : 2 * P.p < 2 / P.p := by rw [lt_div_iff₀ hp0]; linarith
    have : 2 / P.p = 2 * (1 / P.p) := by ring
    linarith
  set Cp : ℝ := (2 : ℝ) ^ (2 - P.p) * (1 / (1 - P.p) + 1 / P.p) with hCp
  have hCp0 : 0 < Cp := by
    have : 0 < 1 - P.p := by linarith
    positivity
  set K : ℝ := 2 * Cp * CA * C₂ ^ 5 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨(3 : ℝ) ^ (2 * P.p + 1) * K, by positivity, ?_⟩
  intro Y hY ε hε μ hμ
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  obtain ⟨⟨hcf, -, -⟩, -, -, -, hb⟩ := HL' Y hY ε hε μ hμ
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun z => res_chiY Y z * f z with hcfdef
  set Q := c06_A_eps_bounds_quintic P.p ε with hQ
  have htop : ∀ n : ℕ, (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun n => WithTop.coe_le_coe.mpr le_top
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have dA : Differentiable ℝ (A_eps P.p ε) := hAc.differentiable (by simp)
  have dQ : Differentiable ℝ Q := by
    intro u
    simp only [hQ]
    have : DifferentiableAt ℝ (fun u => calpha P.p * (A_eps P.p ε u - 1 + (P.p + 1) / 2 * ε * u ^ 2)) u :=
      (((dA u).sub_const 1).add ((differentiableAt_id.pow 2).const_mul _)).const_mul _
    exact this
  have dcf : Differentiable ℝ cf := hcf.differentiable (by simp)
  have ddcf : Differentiable ℝ (deriv cf) := by
    simpa using hcf.differentiable_iteratedDeriv 1 htop1
  have bcf : ∀ z, |deriv cf z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.1 0 (by norm_num)
  have bcf2 : ∀ z, |deriv (deriv cf) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.1 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bcf3 : ∀ z, |deriv (deriv (deriv cf)) z| ≤ C₂ * Y ^ (-beta P.p + 2 / P.p) := fun z => by
    have := (hb z).2.2.1 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have sS := fun y s => c06_aux_secant_le cf dcf _ bcf y (y - s)
  have sS' := fun y s => c06_aux_secant_le _ ddcf _ bcf2 y (y - s)
  have dS := c06_aux_sec_hasDeriv cf (hcf.of_le (htop 2)) _ _ bcf bcf2
  have mS := c06_aux_secant_meas cf dcf.continuous
  have mS' := c06_aux_secant_meas _ ddcf.continuous
  have hpos : ∀ a : ℝ, 0 < C₂ * Y ^ a := fun a => by positivity
  set m : ℝ := C₂ * Y ^ (-beta P.p) with hm
  have hm0 : 0 ≤ m := (hpos _).le
  have bQ : ∀ y s, |Q (c01_secant cf y (y - s))| ≤ CA * ε ^ 2 * m ^ 4 := by
    intro y s
    refine le_trans (hAb _).2.2.2.1 ?_
    have : c01_secant cf y (y - s) ^ 4 ≤ m ^ 4 := by
      rw [show c01_secant cf y (y - s) ^ 4 = |c01_secant cf y (y - s)| ^ 4 by
        rw [pow_abs]; exact (abs_of_nonneg (by positivity)).symm]
      exact pow_le_pow_left₀ (abs_nonneg _) (sS y s) 4
    gcongr
  have bQ' : ∀ y s, |deriv Q (c01_secant cf y (y - s)) * c01_secant (deriv cf) y (y - s)| ≤
      CA * ε ^ 2 * m ^ 3 * (C₂ * Y ^ (-beta P.p + 1 / P.p)) := by
    intro y s
    rw [abs_mul]
    refine mul_le_mul (le_trans (hAb _).2.2.2.2 ?_) (sS' y s) (abs_nonneg _) (by positivity)
    gcongr
    exact sS y s
  -- identification of `ℰ₈`
  have hE : residual_decomposition_E8 P.p R ε μ Y = fun y =>
      ∫ s, (deriv cf y - deriv cf (y - s)) / |s| ^ (1 + P.p) * Q (c01_secant cf y (y - s)) := by
    funext y
    exact (c06_quintic_representation P ε hε0 hε1 cf (hcf.of_le (htop 2)) ⟨_, bcf⟩ ⟨_, bcf2⟩ y).2.2.2
  have TD := fun y => c06_aux_TD P.p hp0 hp1 cf (hcf.of_le (htop 3)) _ _ _ (hpos _) (hpos _)
    (hpos _) bcf bcf2 bcf3 (fun y s => Q (c01_secant cf y (y - s)))
    (fun y s => deriv Q (c01_secant cf y (y - s)) * c01_secant (deriv cf) y (y - s))
    (dQ.continuous.measurable.comp mS) (((measurable_deriv Q).comp mS).mul mS')
    (fun y s => (dQ _).hasDerivAt.comp y (dS y s)) _ _ bQ bQ' y
  have hderE : ∀ y, HasDerivAt (residual_decomposition_E8 P.p R ε μ Y)
      (∫ s, ((deriv (deriv cf) y - deriv (deriv cf) (y - s)) * Q (c01_secant cf y (y - s)) +
        (deriv cf y - deriv cf (y - s)) * (deriv Q (c01_secant cf y (y - s)) *
          c01_secant (deriv cf) y (y - s))) / |s| ^ (1 + P.p)) y := by
    intro y; rw [hE]; exact (TD y).1
  have hT0 : 0 ≤ Y ^ (1 - 5 * beta P.p) := Real.rpow_nonneg hY0.le _
  have hT1 : 0 ≤ Y ^ (1 - 5 * beta P.p + 1 / P.p) := Real.rpow_nonneg hY0.le _
  have hε2 : 0 ≤ ε ^ 2 := by positivity
  -- value bound
  have V : ∀ y, |residual_decomposition_E8 P.p R ε μ Y y| ≤ K * ε ^ 2 * Y ^ (1 - 5 * beta P.p) := by
    intro y
    rw [hE]
    have := c06_aux_frac_int_le P.p hp0 hp1 _ _ (hpos (-beta P.p)) (hpos (-beta P.p + 1 / P.p))
      (deriv cf) bcf (c06_aux_lip _ ddcf _ bcf2) y _ (by positivity) _
      (fun s => c06_aux_pt _ _ _ _ _ (bQ y s))
    refine le_trans this ?_
    rw [← hCp, show CA * ε ^ 2 * m ^ 4 * (Cp * (C₂ * Y ^ (-beta P.p)) ^ (1 - P.p) *
        (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ P.p) = CA * ε ^ 2 * m ^ 4 * (Cp *
        ((C₂ * Y ^ (-beta P.p)) ^ (1 - P.p) * (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ P.p)) by ring,
      c06_aux_interp C₂ Y _ _ P.p hC₂ hY0]
    have e : -beta P.p * (1 - P.p) + (-beta P.p + 1 / P.p) * P.p = -beta P.p + 1 := by
      field_simp; ring
    rw [e, hm]
    have : (C₂ * Y ^ (-beta P.p)) ^ 4 * (C₂ * Y ^ (-beta P.p + 1)) =
        C₂ ^ 5 * (Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-beta P.p) *
          Y ^ (-beta P.p + 1)) := by ring
    have h5 : Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-beta P.p) *
        Y ^ (-beta P.p + 1) = Y ^ (1 - 5 * beta P.p) := by
      simp only [← Real.rpow_add hY0]; congr 1; ring
    calc CA * ε ^ 2 * (C₂ * Y ^ (-beta P.p)) ^ 4 * (Cp * (C₂ * Y ^ (-beta P.p + 1)))
        = Cp * CA * C₂ ^ 5 * (ε ^ 2 * Y ^ (1 - 5 * beta P.p)) := by
          rw [← h5]; ring
      _ ≤ K * ε ^ 2 * Y ^ (1 - 5 * beta P.p) := by
          rw [hK]
          have : 0 ≤ Cp * CA * C₂ ^ 5 * (ε ^ 2 * Y ^ (1 - 5 * beta P.p)) := by positivity
          nlinarith
  -- derivative bound
  have D : ∀ y, |deriv (residual_decomposition_E8 P.p R ε μ Y) y| ≤
      K * ε ^ 2 * Y ^ (1 - 5 * beta P.p + 1 / P.p) := by
    intro y
    rw [(hderE y).deriv]
    refine le_trans (TD y).2 ?_
    rw [← hCp]
    have e3 : (-beta P.p + 1 / P.p) * (1 - P.p) + (-beta P.p + 2 / P.p) * P.p =
        -beta P.p + 1 + 1 / P.p := by field_simp; ring
    have e4 : -beta P.p * (1 - P.p) + (-beta P.p + 1 / P.p) * P.p = -beta P.p + 1 := by
      field_simp; ring
    have t1 : CA * ε ^ 2 * m ^ 4 * (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ (1 - P.p) *
        (C₂ * Y ^ (-beta P.p + 2 / P.p)) ^ P.p =
        CA * C₂ ^ 5 * (ε ^ 2 * Y ^ (1 - 5 * beta P.p + 1 / P.p)) := by
      rw [mul_assoc, c06_aux_interp C₂ Y _ _ P.p hC₂ hY0, e3, hm]
      have h5 : Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-beta P.p) *
          Y ^ (-beta P.p + 1 + 1 / P.p) = Y ^ (1 - 5 * beta P.p + 1 / P.p) := by
        simp only [← Real.rpow_add hY0]; congr 1; ring
      rw [← h5]; ring
    have t2 : CA * ε ^ 2 * m ^ 3 * (C₂ * Y ^ (-beta P.p + 1 / P.p)) *
        (C₂ * Y ^ (-beta P.p)) ^ (1 - P.p) * (C₂ * Y ^ (-beta P.p + 1 / P.p)) ^ P.p =
        CA * C₂ ^ 5 * (ε ^ 2 * Y ^ (1 - 5 * beta P.p + 1 / P.p)) := by
      rw [mul_assoc, c06_aux_interp C₂ Y _ _ P.p hC₂ hY0, e4, hm]
      have h5 : Y ^ (-beta P.p) * Y ^ (-beta P.p) * Y ^ (-beta P.p) *
          Y ^ (-beta P.p + 1 / P.p) * Y ^ (-beta P.p + 1) = Y ^ (1 - 5 * beta P.p + 1 / P.p) := by
        simp only [← Real.rpow_add hY0]; congr 1; ring
      rw [← h5]; ring
    rw [t1, t2, hK]
    have : 0 ≤ CA * C₂ ^ 5 * (ε ^ 2 * Y ^ (1 - 5 * beta P.p + 1 / P.p)) := by positivity
    nlinarith
  refine ⟨fun y => (hderE y).differentiableAt, fun y => ⟨?_, ?_⟩, ?_⟩
  · refine le_trans (V y) ?_
    have : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * P.p + 1) := Real.one_le_rpow (by norm_num) (by linarith)
    have : 0 ≤ K * ε ^ 2 * Y ^ (1 - 5 * beta P.p) := by positivity
    nlinarith
  · refine le_trans (D y) ?_
    have : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * P.p + 1) := Real.one_le_rpow (by norm_num) (by linarith)
    have : 0 ≤ K * ε ^ 2 * Y ^ (1 - 5 * beta P.p + 1 / P.p) := by positivity
    nlinarith
  · intro y hy j hj
    interval_cases j
    · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
      rw [show -2 * P.p - 1 = -(2 * P.p + 1) by ring]
      apply c06_aux_conv _ _ _ _ Y y _ hK0.le hε2 (by linarith) le_rfl hY1 hy.1 hy.2
      refine le_trans (V y) ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
        (by positivity)
    · simp only [iteratedDeriv_one, Nat.cast_one]
      rw [show -2 * P.p - 1 + 1 / P.p = -(2 * P.p + 1 - 1 / P.p) by ring]
      apply c06_aux_conv _ _ _ _ Y y _ hK0.le hε2 (by linarith) (by linarith) hY1 hy.1 hy.2
      refine le_trans (D y) ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
        (by positivity)

/-! ### `C¹` regularity of `ℰ₇`, `ℰ₈`, `𝒬_{ε,3}(v_Y)` (for prop:approx_residual_positive) -/
/-- Helper: `y ↦ S_w(y, y-s)` is continuous for `w ∈ C¹`. -/
theorem c06_aux_C1T_secc (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (s : ℝ) :
    Continuous (fun y => c01_secant w y (y - s)) := by
  by_cases hs : s = 0
  · subst hs
    have e : (fun y => c01_secant w y (y - 0)) = deriv w := by
      funext y; simp [c01_secant]
    rw [e]; exact hw.continuous_deriv le_rfl
  · have e : (fun y => c01_secant w y (y - s)) = fun y => (w y - w (y - s)) / s := by
      funext y
      have : y ≠ y - s := by intro h; apply hs; linarith
      simp only [c01_secant, if_neg this, sub_sub_cancel]
    rw [e]
    exact ((hw.continuous.sub (hw.continuous.comp (continuous_id.sub continuous_const))).div_const s)

/-- Helper (lem:c06_translated_derivative, `C¹` form): if moreover `y ↦ Φ'(y,s)` is continuous,
the translated integral is `C¹`. -/
theorem c06_translated_C1 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (w : ℝ → ℝ)
    (hw : ContDiff ℝ 3 w) (B₁ B₂ B₃ : ℝ) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hB₃ : 0 < B₃)
    (hw1 : ∀ x, |deriv w x| ≤ B₁) (hw2 : ∀ x, |deriv (deriv w) x| ≤ B₂)
    (hw3 : ∀ x, |deriv (deriv (deriv w)) x| ≤ B₃)
    (Φ Φ' : ℝ → ℝ → ℝ) (hΦm : Measurable (fun q : ℝ × ℝ => Φ q.1 q.2))
    (hΦ'm : Measurable (fun q : ℝ × ℝ => Φ' q.1 q.2))
    (hΦd : ∀ y s, HasDerivAt (fun y' => Φ y' s) (Φ' y s) y)
    (hΦ'c : ∀ s, Continuous (fun y => Φ' y s))
    (M₀ M₁ : ℝ) (hM₀ : ∀ y s, |Φ y s| ≤ M₀) (hM₁ : ∀ y s, |Φ' y s| ≤ M₁) :
    ContDiff ℝ 1 (fun y => ∫ s, (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * Φ y s) := by
  have TD := fun y => c06_aux_TD p hp hp1 w hw B₁ B₂ B₃ hB₁ hB₂ hB₃ hw1 hw2 hw3 Φ Φ' hΦm hΦ'm
    hΦd M₀ M₁ hM₀ hM₁ y
  have hw2' : ContDiff ℝ 2 (deriv w) := (contDiff_succ_iff_deriv.mp hw).2.2
  have hw1' : ContDiff ℝ 1 (deriv (deriv w)) := (contDiff_succ_iff_deriv.mp hw2').2.2
  have dw1 : Differentiable ℝ (deriv w) := hw2'.differentiable (by norm_num)
  have dw2 : Differentiable ℝ (deriv (deriv w)) := hw1'.differentiable (by norm_num)
  have lip1 := c06_aux_lip (deriv w) dw1 B₂ hw2
  have lip2 := c06_aux_lip (deriv (deriv w)) dw2 B₃ hw3
  have hM₀0 : 0 ≤ M₀ := le_trans (abs_nonneg _) (hM₀ 0 0)
  have hM₁0 : 0 ≤ M₁ := le_trans (abs_nonneg _) (hM₁ 0 0)
  set φ₁ := fun t : ℝ => if t ≤ 2 * B₁ / B₂ then B₂ * t ^ (-p) else 2 * B₁ * t ^ (-1 - p)
    with hφ₁
  set φ₂ := fun t : ℝ => if t ≤ 2 * B₂ / B₃ then B₃ * t ^ (-p) else 2 * B₂ * t ^ (-1 - p)
    with hφ₂
  have G₁ := c06_aux_integrable_comp_abs φ₁ (c06_aux_profile_int p hp hp1 B₁ B₂ _ (by positivity)).1
  have G₂ := c06_aux_integrable_comp_abs φ₂ (c06_aux_profile_int p hp hp1 B₂ B₃ _ (by positivity)).1
  have P₁ := fun x s => c06_aux_diff_le_profile p hp B₁ B₂ hB₁ hB₂ (deriv w) hw1 lip1 x s
  have P₂ := fun x s => c06_aux_diff_le_profile p hp B₂ B₃ hB₂ hB₃ (deriv (deriv w)) hw2 lip2 x s
  have mΦ : ∀ x, Measurable (fun s => Φ x s) := fun x =>
    hΦm.comp (measurable_const.prodMk measurable_id)
  have mΦ' : ∀ x, Measurable (fun s => Φ' x s) := fun x =>
    hΦ'm.comp (measurable_const.prodMk measurable_id)
  have mden : Measurable (fun s : ℝ => |s| ^ (1 + p)) := continuous_abs.measurable.pow_const _
  set I' : ℝ → ℝ := fun y => ∫ s, ((deriv (deriv w) y - deriv (deriv w) (y - s)) * Φ y s +
        (deriv w y - deriv w (y - s)) * Φ' y s) / |s| ^ (1 + p) with hI'
  have hcont : Continuous I' := by
    refine continuous_of_dominated (bound := fun s => M₀ * φ₂ |s| + M₁ * φ₁ |s|)
      (fun y => ((((measurable_const.sub (dw2.continuous.measurable.comp
        (measurable_const.sub measurable_id))).mul (mΦ y)).add
        ((measurable_const.sub (dw1.continuous.measurable.comp
        (measurable_const.sub measurable_id))).mul (mΦ' y))).div mden).aestronglyMeasurable)
      (fun y => ae_of_all _ fun s => ?_) ((G₂.const_mul M₀).add (G₁.const_mul M₁))
      (ae_of_all _ fun s => ?_)
    · rw [Real.norm_eq_abs, add_div]
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
      · rw [mul_div_right_comm]
        exact (c06_aux_pt _ _ _ _ _ (hM₀ y s)).trans (mul_le_mul_of_nonneg_left (P₂ y s) hM₀0)
      · rw [mul_div_right_comm]
        exact (c06_aux_pt _ _ _ _ _ (hM₁ y s)).trans (mul_le_mul_of_nonneg_left (P₁ y s) hM₁0)
    · have cΦ : Continuous (fun y => Φ y s) :=
        continuous_iff_continuousAt.mpr fun y => (hΦd y s).continuousAt
      exact ((((dw2.continuous.sub (dw2.continuous.comp (continuous_id.sub continuous_const))).mul
        cΦ).add ((dw1.continuous.sub (dw1.continuous.comp (continuous_id.sub continuous_const))).mul
        (hΦ'c s))).div_const _)
  rw [contDiff_one_iff_deriv]
  refine ⟨fun y => (TD y).1.differentiableAt, ?_⟩
  have : deriv (fun y => ∫ s, (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * Φ y s) = I' :=
    funext fun y => (TD y).1.deriv
  rw [this]; exact hcont

theorem c06_E7_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiff ℝ 1 (residual_decomposition_E7 P.p R ε μ Y) := by
  obtain ⟨R₁, hR₁, HD⟩ := c06_E7_decomposition P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₂, hR₂, HL⟩ := c06_localized_bounds P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨max R₁ R₂, le_trans hR₁ (le_max_left _ _), fun R hR => ?_⟩
  have hR1 : R₁ ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : R₂ ≤ R := le_trans (le_max_right _ _) hR
  have hRone : 1 ≤ R := le_trans hR₁ hR1
  obtain ⟨C₂, hC₂, HL'⟩ := HL R hR2
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hβ : beta P.p ≤ P.p + 1 := by
    unfold beta; rw [div_le_iff₀ (by linarith)]; nlinarith
  set Cp : ℝ := (2 : ℝ) ^ (2 - P.p) * (1 / (1 - P.p) + 1 / P.p) with hCp
  have hCp0 : 0 < Cp := by
    have : 0 < 1 - P.p := by linarith
    positivity
  intro Y hY ε hε μ hμ
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  obtain ⟨⟨hcf, hv, hh⟩, -, -, -, hb⟩ := HL' Y hY ε hε μ hμ
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun z => res_chiY Y z * f z with hcfdef
  set v : ℝ → ℝ := res_vY P.p R ε μ Y with hvdef
  set h : ℝ → ℝ := c06_localized_bounds_hY P.p R ε μ Y with hhdef
  set g : ℝ → ℝ := fun x => 2 * v x + h x with hgdef
  have hvh : (fun x => v x + h x) = cf := by
    funext x; simp only [hvdef, hhdef, hcfdef, c06_localized_bounds_hY]; ring
  have htop : ∀ n : ℕ, (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun n => WithTop.coe_le_coe.mpr le_top
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast WithTop.coe_lt_top _
  have htop2 : ((2 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
  have dcf : Differentiable ℝ cf := hcf.differentiable (by simp)
  have dv : Differentiable ℝ v := hv.differentiable (by simp)
  have dh : Differentiable ℝ h := hh.differentiable (by simp)
  have ddcf : Differentiable ℝ (deriv cf) := by
    simpa using hcf.differentiable_iteratedDeriv 1 htop1
  have ddv : Differentiable ℝ (deriv v) := by
    simpa using hv.differentiable_iteratedDeriv 1 htop1
  have ddh : Differentiable ℝ (deriv h) := by
    simpa using hh.differentiable_iteratedDeriv 1 htop1
  have dddv : Differentiable ℝ (deriv (deriv v)) := by
    have := hv.differentiable_iteratedDeriv 2 htop2
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this; exact this
  have dddh : Differentiable ℝ (deriv (deriv h)) := by
    have := hh.differentiable_iteratedDeriv 2 htop2
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this; exact this
  have dg : Differentiable ℝ g := (dv.const_mul 2).add dh
  have hdg : deriv g = fun x => 2 * deriv v x + deriv h x := by
    funext x; exact (((dv x).hasDerivAt.const_mul 2).add (dh x).hasDerivAt).deriv
  have ddg : Differentiable ℝ (deriv g) := by rw [hdg]; exact (ddv.const_mul 2).add ddh
  have hddg : ∀ x, deriv (deriv g) x = 2 * deriv (deriv v) x + deriv (deriv h) x := by
    intro x; rw [hdg]; exact (((ddv x).hasDerivAt.const_mul 2).add (ddh x).hasDerivAt).deriv
  have hg2 : ContDiff ℝ 2 g := ((contDiff_const.mul (hv.of_le (htop 2))).add (hh.of_le (htop 2)))
  have dI : ∀ {w : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) w → ContDiff ℝ 1 (deriv w) := fun hw =>
    (contDiff_infty_iff_deriv.mp hw).2.of_le (WithTop.coe_le_coe.mpr le_top)
  have ddcf1 := dI hcf
  have ddh1 := dI hh
  have ddv1 := dI hv
  have ddg1 : ContDiff ℝ 1 (deriv g) := by rw [hdg]; exact (contDiff_const.mul ddv1).add ddh1
  -- the pointwise bounds
  have bh1 : ∀ z, |deriv h z| ≤ C₂ * Y ^ (-P.p - 1) := fun z => by
    simpa using (hb z).1 1 (by norm_num)
  have bh2 : ∀ z, |deriv (deriv h) z| ≤ C₂ * Y ^ (-P.p - 2) := fun z => by
    have := (hb z).1 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bh3 : ∀ z, |deriv (deriv (deriv h)) z| ≤ C₂ * Y ^ (-P.p - 3) := fun z => by
    have := (hb z).1 3 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bcf : ∀ z, |deriv cf z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.1 0 (by norm_num)
  have bcf2 : ∀ z, |deriv (deriv cf) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.1 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bv1 : ∀ z, |deriv v z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.2 0 (by norm_num)
  have bv2 : ∀ z, |deriv (deriv v) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bv3 : ∀ z, |deriv (deriv (deriv v)) z| ≤ C₂ * Y ^ (-beta P.p + 2 / P.p) := fun z => by
    have := (hb z).2.2.2 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have hYβ : Y ^ (-P.p - 1) ≤ Y ^ (-beta P.p) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hYβ' : Y ^ (-P.p - 2) ≤ Y ^ (-beta P.p + 1 / P.p) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have bg1 : ∀ x, |deriv g x| ≤ 3 * C₂ * Y ^ (-beta P.p) := by
    intro x
    rw [hdg]
    have h1 := bv1 x
    have h2 := bh1 x
    have h3 : C₂ * Y ^ (-P.p - 1) ≤ C₂ * Y ^ (-beta P.p) := by gcongr
    have h4 := abs_add_le (2 * deriv v x) (deriv h x)
    rw [abs_mul, abs_two] at h4
    linarith
  have bg2 : ∀ x, |deriv (deriv g) x| ≤ 3 * C₂ * Y ^ (-beta P.p + 1 / P.p) := by
    intro x
    rw [hddg]
    have h1 := bv2 x
    have h2 := bh2 x
    have h3 : C₂ * Y ^ (-P.p - 2) ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := by gcongr
    have h4 := abs_add_le (2 * deriv (deriv v) x) (deriv (deriv h) x)
    rw [abs_mul, abs_two] at h4
    linarith
  -- secants and their derivatives
  have sS := fun y s => c06_aux_secant_le cf dcf _ bcf y (y - s)
  have sS' := fun y s => c06_aux_secant_le _ ddcf _ bcf2 y (y - s)
  have sh := fun y s => c06_aux_secant_le h dh _ bh1 y (y - s)
  have sh' := fun y s => c06_aux_secant_le _ ddh _ bh2 y (y - s)
  have sg := fun y s => c06_aux_secant_le g dg _ bg1 y (y - s)
  have sg' := fun y s => c06_aux_secant_le _ ddg _ bg2 y (y - s)
  have dS := c06_aux_sec_hasDeriv cf (hcf.of_le (htop 2)) _ _ bcf bcf2
  have dSh := c06_aux_sec_hasDeriv h (hh.of_le (htop 2)) _ _ bh1 bh2
  have dSg := c06_aux_sec_hasDeriv g hg2 _ _ bg1 bg2
  have mS := c06_aux_secant_meas cf dcf.continuous
  have mS' := c06_aux_secant_meas _ ddcf.continuous
  have mSh := c06_aux_secant_meas h dh.continuous
  have mSh' := c06_aux_secant_meas _ ddh.continuous
  have mSg := c06_aux_secant_meas g dg.continuous
  have mSg' := c06_aux_secant_meas _ ddg.continuous
  have hpos : ∀ a : ℝ, 0 < C₂ * Y ^ a := fun a => by positivity
  -- T₁
  have TD1 := c06_translated_C1 P.p hp0 hp1 h (hh.of_le (htop 3)) _ _ _ (hpos _) (hpos _)
    (hpos _) bh1 bh2 bh3 (fun y s => c01_secant cf y (y - s) ^ 2)
    (fun y s => 2 * c01_secant cf y (y - s) * c01_secant (deriv cf) y (y - s))
    (mS.pow_const 2) ((mS.const_mul 2).mul mS')
    (fun y s => ((dS y s).pow 2).congr_deriv (by push_cast; ring))
    (fun s => (continuous_const.mul (c06_aux_C1T_secc cf (hcf.of_le (htop 1)) s)).mul
      (c06_aux_C1T_secc (deriv cf) (ddcf1) s))
    ((C₂ * Y ^ (-beta P.p)) ^ 2) (2 * (C₂ * Y ^ (-beta P.p)) * (C₂ * Y ^ (-beta P.p + 1 / P.p)))
    (fun y s => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (sS y s) 2)
    (fun y s => by
      rw [abs_mul, abs_mul, abs_two]
      have := sS y s; have := sS' y s
      apply mul_le_mul (mul_le_mul_of_nonneg_left (sS y s) (by norm_num)) (sS' y s)
        (abs_nonneg _) (by positivity))
  -- T₂
  have TD2 := c06_translated_C1 P.p hp0 hp1 v (hv.of_le (htop 3)) _ _ _ (hpos _) (hpos _)
    (hpos _) bv1 bv2 bv3 (fun y s => c01_secant h y (y - s) * c01_secant g y (y - s))
    (fun y s => c01_secant (deriv h) y (y - s) * c01_secant g y (y - s) +
      c01_secant h y (y - s) * c01_secant (deriv g) y (y - s))
    (mSh.mul mSg) ((mSh'.mul mSg).add (mSh.mul mSg'))
    (fun y s => (dSh y s).mul (dSg y s))
    (fun s => ((c06_aux_C1T_secc (deriv h) ddh1 s).mul (c06_aux_C1T_secc g (hg2.of_le (by norm_num)) s)).add
      ((c06_aux_C1T_secc h (hh.of_le (htop 1)) s).mul (c06_aux_C1T_secc (deriv g) ddg1 s)))
    (C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p)))
    (C₂ * Y ^ (-P.p - 2) * (3 * C₂ * Y ^ (-beta P.p)) +
      C₂ * Y ^ (-P.p - 1) * (3 * C₂ * Y ^ (-beta P.p + 1 / P.p)))
    (fun y s => by
      rw [abs_mul]; exact mul_le_mul (sh y s) (sg y s) (abs_nonneg _) (hpos _).le)
    (fun y s => by
      refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul (sh' y s) (sg y s) (abs_nonneg _) (hpos _).le
      · exact mul_le_mul (sh y s) (sg' y s) (abs_nonneg _) (hpos _).le)
  -- identification of E₇
  have hE : residual_decomposition_E7 P.p R ε μ Y = fun y => c04_cubic_part_kappa P.p ε *
      ((∫ s, (deriv h y - deriv h (y - s)) / |s| ^ (1 + P.p) * c01_secant cf y (y - s) ^ 2) +
       (∫ s, (deriv v y - deriv v (y - s)) / |s| ^ (1 + P.p) *
          (c01_secant h y (y - s) * c01_secant g y (y - s)))) := by
    funext y
    rw [(HD R hR1 Y hY ε hε μ hμ y).1]
    unfold c06_E7_decomposition_T1 c06_E7_decomposition_T2
    rw [hvh]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hgdef]; ring
  rw [hE]
  exact contDiff_const.mul (TD1.add TD2)

theorem c06_E8_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiff ℝ 1 (residual_decomposition_E8 P.p R ε μ Y) := by
  obtain ⟨R₂, hR₂, HL⟩ := c06_localized_bounds P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  obtain ⟨CA, hCA, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₂, hR₂, fun R hR => ?_⟩
  have hRone : 1 ≤ R := le_trans hR₂ hR
  obtain ⟨C₂, hC₂, HL'⟩ := HL R hR
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hinv2 : 1 / P.p < 4 / 3 := by rw [div_lt_iff₀ hp0]; linarith
  have h5b : 1 - 5 * beta P.p ≤ -2 * P.p - 1 := by
    have : 2 * P.p * P.p < 2 := by nlinarith
    have : 2 * P.p < 2 / P.p := by rw [lt_div_iff₀ hp0]; linarith
    have : 2 / P.p = 2 * (1 / P.p) := by ring
    linarith
  set Cp : ℝ := (2 : ℝ) ^ (2 - P.p) * (1 / (1 - P.p) + 1 / P.p) with hCp
  have hCp0 : 0 < Cp := by
    have : 0 < 1 - P.p := by linarith
    positivity
  set K : ℝ := 2 * Cp * CA * C₂ ^ 5 with hK
  have hK0 : 0 < K := by positivity
  intro Y hY ε hε μ hμ
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  obtain ⟨⟨hcf, -, -⟩, -, -, -, hb⟩ := HL' Y hY ε hε μ hμ
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun z => res_chiY Y z * f z with hcfdef
  set Q := c06_A_eps_bounds_quintic P.p ε with hQ
  have htop : ∀ n : ℕ, (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun n => WithTop.coe_le_coe.mpr le_top
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have dA : Differentiable ℝ (A_eps P.p ε) := hAc.differentiable (by simp)
  have dQ : Differentiable ℝ Q := by
    intro u
    simp only [hQ]
    have : DifferentiableAt ℝ (fun u => calpha P.p * (A_eps P.p ε u - 1 + (P.p + 1) / 2 * ε * u ^ 2)) u :=
      (((dA u).sub_const 1).add ((differentiableAt_id.pow 2).const_mul _)).const_mul _
    exact this
  have dcf : Differentiable ℝ cf := hcf.differentiable (by simp)
  have hQc : Continuous (deriv Q) := by
    have hQs : ContDiff ℝ 1 Q := by
      simp only [hQ]; unfold c06_A_eps_bounds_quintic
      exact contDiff_const.mul (((hAc.of_le (htop 1)).sub contDiff_const).add
        (contDiff_const.mul (contDiff_id.pow 2)))
    exact hQs.continuous_deriv le_rfl
  have ddcf : Differentiable ℝ (deriv cf) := by
    simpa using hcf.differentiable_iteratedDeriv 1 htop1
  have bcf : ∀ z, |deriv cf z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.1 0 (by norm_num)
  have bcf2 : ∀ z, |deriv (deriv cf) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.1 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bcf3 : ∀ z, |deriv (deriv (deriv cf)) z| ≤ C₂ * Y ^ (-beta P.p + 2 / P.p) := fun z => by
    have := (hb z).2.2.1 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have sS := fun y s => c06_aux_secant_le cf dcf _ bcf y (y - s)
  have sS' := fun y s => c06_aux_secant_le _ ddcf _ bcf2 y (y - s)
  have dS := c06_aux_sec_hasDeriv cf (hcf.of_le (htop 2)) _ _ bcf bcf2
  have mS := c06_aux_secant_meas cf dcf.continuous
  have mS' := c06_aux_secant_meas _ ddcf.continuous
  have hpos : ∀ a : ℝ, 0 < C₂ * Y ^ a := fun a => by positivity
  set m : ℝ := C₂ * Y ^ (-beta P.p) with hm
  have hm0 : 0 ≤ m := (hpos _).le
  have bQ : ∀ y s, |Q (c01_secant cf y (y - s))| ≤ CA * ε ^ 2 * m ^ 4 := by
    intro y s
    refine le_trans (hAb _).2.2.2.1 ?_
    have : c01_secant cf y (y - s) ^ 4 ≤ m ^ 4 := by
      rw [show c01_secant cf y (y - s) ^ 4 = |c01_secant cf y (y - s)| ^ 4 by
        rw [pow_abs]; exact (abs_of_nonneg (by positivity)).symm]
      exact pow_le_pow_left₀ (abs_nonneg _) (sS y s) 4
    gcongr
  have bQ' : ∀ y s, |deriv Q (c01_secant cf y (y - s)) * c01_secant (deriv cf) y (y - s)| ≤
      CA * ε ^ 2 * m ^ 3 * (C₂ * Y ^ (-beta P.p + 1 / P.p)) := by
    intro y s
    rw [abs_mul]
    refine mul_le_mul (le_trans (hAb _).2.2.2.2 ?_) (sS' y s) (abs_nonneg _) (by positivity)
    gcongr
    exact sS y s
  -- identification of `ℰ₈`
  have hE : residual_decomposition_E8 P.p R ε μ Y = fun y =>
      ∫ s, (deriv cf y - deriv cf (y - s)) / |s| ^ (1 + P.p) * Q (c01_secant cf y (y - s)) := by
    funext y
    exact (c06_quintic_representation P ε hε0 hε1 cf (hcf.of_le (htop 2)) ⟨_, bcf⟩ ⟨_, bcf2⟩ y).2.2.2
  have TD := c06_translated_C1 P.p hp0 hp1 cf (hcf.of_le (htop 3)) _ _ _ (hpos _) (hpos _)
    (hpos _) bcf bcf2 bcf3 (fun y s => Q (c01_secant cf y (y - s)))
    (fun y s => deriv Q (c01_secant cf y (y - s)) * c01_secant (deriv cf) y (y - s))
    (dQ.continuous.measurable.comp mS) (((measurable_deriv Q).comp mS).mul mS')
    (fun y s => (dQ _).hasDerivAt.comp y (dS y s))
    (fun s => (hQc.comp (c06_aux_C1T_secc cf (hcf.of_le (htop 1)) s)).mul
      (c06_aux_C1T_secc (deriv cf) ((contDiff_infty_iff_deriv.mp hcf).2.of_le (htop 1)) s))
    _ _ bQ bQ'
  rw [hE]; exact TD


/-- Helper: `𝒬_{ε,3}(w)` in translated form. -/
theorem c06_aux_C1T_cubic_s (p ε : ℝ) (w : ℝ → ℝ) :
    c04_cubic_part p ε w = fun y => c04_cubic_part_kappa p ε *
      ∫ s, (deriv w y - deriv w (y - s)) / |s| ^ (1 + p) * c01_secant w y (y - s) ^ 2 := by
  funext y
  unfold c04_cubic_part
  congr 1
  rw [← integral_sub_left_eq_self (μ := volume)
    (fun z => (deriv w y - deriv w z) / |y - z| ^ (p + 1) * c01_secant w y z ^ 2) y]
  congr 1; funext s
  rw [sub_sub_cancel, add_comm p 1]

/-- `𝒬_{ε,3}(v_Y)` is `C¹` (supports prop:approx_residual_positive through `ℰ₅^Y`). -/
theorem c06_cubic_vY_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiff ℝ 1 (c04_cubic_part P.p ε (res_vY P.p R ε μ Y)) := by
  obtain ⟨R₂, hR₂, HL⟩ := c06_localized_bounds P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  refine ⟨R₂, hR₂, fun R hR => ?_⟩
  obtain ⟨C₂, hC₂, HL'⟩ := HL R hR
  intro Y hY ε hε μ hμ
  have hY0 : 0 < Y := by linarith [le_trans hR₂ hR]
  obtain ⟨⟨-, hv, -⟩, -, -, -, hb⟩ := HL' Y hY ε hε μ hμ
  set v : ℝ → ℝ := res_vY P.p R ε μ Y with hvdef
  have htop : ∀ n : ℕ, (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun n => WithTop.coe_le_coe.mpr le_top
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have dv : Differentiable ℝ v := hv.differentiable (by simp)
  have ddv : Differentiable ℝ (deriv v) := by
    simpa using hv.differentiable_iteratedDeriv 1 htop1
  have ddv1 : ContDiff ℝ 1 (deriv v) :=
    (contDiff_infty_iff_deriv.mp hv).2.of_le (WithTop.coe_le_coe.mpr le_top)
  have bv1 : ∀ z, |deriv v z| ≤ C₂ * Y ^ (-beta P.p) := fun z => by
    simpa using (hb z).2.2.2 0 (by norm_num)
  have bv2 : ∀ z, |deriv (deriv v) z| ≤ C₂ * Y ^ (-beta P.p + 1 / P.p) := fun z => by
    have := (hb z).2.2.2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have bv3 : ∀ z, |deriv (deriv (deriv v)) z| ≤ C₂ * Y ^ (-beta P.p + 2 / P.p) := fun z => by
    have := (hb z).2.2.2 2 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have hpos : ∀ a : ℝ, 0 < C₂ * Y ^ a := fun a => by positivity
  have sS := fun y s => c06_aux_secant_le v dv _ bv1 y (y - s)
  have sS' := fun y s => c06_aux_secant_le _ ddv _ bv2 y (y - s)
  have dS := c06_aux_sec_hasDeriv v (hv.of_le (htop 2)) _ _ bv1 bv2
  have mS := c06_aux_secant_meas v dv.continuous
  have mS' := c06_aux_secant_meas _ ddv.continuous
  have TD := c06_translated_C1 P.p hp0 hp1 v (hv.of_le (htop 3)) _ _ _ (hpos _) (hpos _)
    (hpos _) bv1 bv2 bv3 (fun y s => c01_secant v y (y - s) ^ 2)
    (fun y s => 2 * c01_secant v y (y - s) * c01_secant (deriv v) y (y - s))
    (mS.pow_const 2) ((mS.const_mul 2).mul mS')
    (fun y s => ((dS y s).pow 2).congr_deriv (by push_cast; ring))
    (fun s => (continuous_const.mul (c06_aux_C1T_secc v (hv.of_le (htop 1)) s)).mul
      (c06_aux_C1T_secc (deriv v) ddv1 s))
    ((C₂ * Y ^ (-beta P.p)) ^ 2) (2 * (C₂ * Y ^ (-beta P.p)) * (C₂ * Y ^ (-beta P.p + 1 / P.p)))
    (fun y s => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (sS y s) 2)
    (fun y s => by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (sS y s) (by norm_num)) (sS' y s)
        (abs_nonneg _) (by positivity))
  rw [c06_aux_C1T_cubic_s]
  exact contDiff_const.mul TD

/-! ## Control of `ℰ₉` -/

/-- Blueprint: lem:c06_E9_split (auxiliary definition).  The far positive contribution
`ℰ_{9,+}(y) = c_α ∫_{(0,∞)∖[Y/2,3Y]} [(f'(y)-f'(z))(A_ε(S_f)-1)
 - (f'(y)-(χ_Y f)'(z))(A_ε(S_{χ_Y f})-1)] / |y-z|^{1+p} dz`. -/
def c06_E9_split_plus (p ε : ℝ) (f : ℝ → ℝ) (Y y : ℝ) : ℝ :=
  calpha p * ∫ z in Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y),
    ((deriv f y - deriv f z) * (A_eps p ε (c01_secant f y z) - 1) -
      (deriv f y - deriv (fun x => res_chiY Y x * f x) z) *
        (A_eps p ε (c01_secant (fun x => res_chiY Y x * f x) y z) - 1)) / |y - z| ^ (1 + p)

/-- Blueprint: lem:c06_E9_split (auxiliary definition).  The second-order Taylor term
`ℐ₁(y) = c_α ∫_{-∞}^0 (A_ε(S_f) - A_ε(S_W) - A_ε'(S_W) S_{f-W}) / (y-z)^{1+p} dz`. -/
def c06_E9_split_I1 (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z in Iio (0 : ℝ),
    (A_eps p ε (c01_secant f y z) - A_eps p ε (c01_secant corner y z) -
      deriv (A_eps p ε) (c01_secant corner y z) * c01_secant (fun x => f x - corner x) y z) /
      (y - z) ^ (1 + p)

/-- Blueprint: lem:c06_E9_split (auxiliary definition).  The mixed term
`ℐ₂(y) = c_α ∫_{-∞}^0 (f'(y)-f'(z)-1)(A_ε(S_f) - A_ε(S_W)) / (y-z)^{1+p} dz`. -/
def c06_E9_split_I2 (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z in Iio (0 : ℝ),
    (deriv f y - deriv f z - 1) * (A_eps p ε (c01_secant f y z) - A_eps p ε (c01_secant corner y z)) /
      (y - z) ^ (1 + p)

/-- Blueprint: lem:c06_E9_split (auxiliary definition).  The truncation term
`ℐ₃(y) = -c_α ∫_{-∞}^0 f'(y)/(y-z)^{1+p} · (A_ε(f(y)/(y-z)) - 1) dz`. -/
def c06_E9_split_I3 (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  -(calpha p * ∫ z in Iio (0 : ℝ),
    deriv f y / (y - z) ^ (1 + p) * (A_eps p ε (f y / (y - z)) - 1))

/-! ### Helpers for c06_E9_split -/
/-- Helper: derivative of the corner `W` away from `0`. -/
theorem c06_aux_corner_hasDeriv (z : ℝ) :
    (z < 0 → HasDerivAt corner (-1) z) ∧ (0 < z → HasDerivAt corner 0 z) := by
  constructor
  · intro hz
    refine (hasDerivAt_neg z).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hz] with x hx
    simp only [corner]; exact max_eq_left (by linarith [mem_Iio.mp hx])
  · intro hz
    refine (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hz] with x hx
    simp only [corner]; exact max_eq_right (by linarith [mem_Ioi.mp hx])

/-- Helper: `χ_Y = 1` on `[Y/2, 3Y]`. -/
theorem c06_aux_chiY_one {Y z : ℝ} (hY : 0 < Y) (hz : z ∈ Icc (Y / 2) (3 * Y)) :
    res_chiY Y z = 1 := by
  unfold res_chiY chiAnnulus
  have h1 : Y / 2 / Y ≤ z / Y := div_le_div_of_nonneg_right hz.1 hY.le
  have h2 : z / Y ≤ 3 * Y / Y := div_le_div_of_nonneg_right hz.2 hY.le
  rw [show Y / 2 / Y = 1 / 2 by field_simp] at h1
  rw [show 3 * Y / Y = 3 by field_simp] at h2
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ (by norm_num)]; linarith
  · rw [le_div_iff₀ (by norm_num)]; linarith

/-- Helper: `χ_Y f = f` near points of `(Y/2,3Y)` and `χ_Y f = 0` near points `< 3Y/10`. -/
theorem c06_aux_chiY_local {Y : ℝ} (hY : 0 < Y) (f : ℝ → ℝ) :
    (∀ z ∈ Ioo (Y / 2) (3 * Y), (fun x => res_chiY Y x * f x) =ᶠ[𝓝 z] f) ∧
    (∀ z, z < 3 * Y / 10 → (fun x => res_chiY Y x * f x) =ᶠ[𝓝 z] fun _ => 0) := by
  constructor
  · intro z hz
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with x hx
    rw [c06_aux_chiY_one hY ⟨hx.1.le, hx.2.le⟩, one_mul]
  · intro z hz
    filter_upwards [Iio_mem_nhds hz] with x hx
    rw [c06_aux_chiY_zero hY (Or.inl (le_of_lt hx)), zero_mul]

/-- Helper: measurability of `z ↦ S_w(y,z)` for continuous `w`. -/
theorem c06_aux_secant_meas1 (w : ℝ → ℝ) (hw : Continuous w) (y : ℝ) :
    Measurable (fun z => c01_secant w y z) := by
  unfold c01_secant
  refine Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const ?_
  exact (measurable_const.sub hw.measurable).div (measurable_const.sub measurable_id)


/-- Helper: `∫_ℝ F = ∫_{(-∞,0)} F + ∫_{(0,∞)} F` for integrable `F`. -/
theorem c06_aux_split_line (F : ℝ → ℝ) (hF : Integrable F) :
    ∫ z, F z = (∫ z in Iio (0 : ℝ), F z) + ∫ z in Ioi (0 : ℝ), F z := by
  rw [← integral_Ici_eq_integral_Ioi, ← setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => by
    simp only [mem_Iio, mem_Ici] at hx hx'; linarith) measurableSet_Ici hF.integrableOn
    hF.integrableOn, Iio_union_Ici, setIntegral_univ]

/-- Helper: integrability of the `𝒬_ε` integrand of a Lipschitz `g ∈ C²((0,∞))` at `y > 0`. -/
theorem c06_aux_Qint (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (g : ℝ → ℝ) (L : ℝ≥0)
    (hL : LipschitzWith L g) (hC2 : ContDiffOn ℝ 2 g (Ioi 0)) (y : ℝ) (hy : 0 < y) :
    Integrable (fun z => (deriv g y - deriv g z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant g y z) - 1)) := by
  have hpos : ∀ u : ℝ, 0 < 1 + ε * u ^ 2 := fun u => by nlinarith [mul_nonneg hε (sq_nonneg u)]
  have hA : Continuous (A_eps p ε) := by
    unfold A_eps
    exact (continuous_const.add (continuous_const.mul (continuous_pow 2))).rpow_const
      (fun u => Or.inl (hpos u).ne')
  refine (c06_aux_wfv_Phi p hp hp1 g L hL hC2 y hy).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (((measurable_const.sub (measurable_deriv g)).div
      ((measurable_const.sub measurable_id).abs.pow_const _)).mul
      ((hA.measurable.comp (c06_aux_secant_meas1 g hL.continuous y)).sub measurable_const)
      ).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |y - z| ^ (p + 1))]
    have := c06_aux_A_sub_one p ε (c01_secant g y z) hp hε
    calc _ ≤ |deriv g y - deriv g z| / |y - z| ^ (p + 1) * 1 := by gcongr
      _ = _ := mul_one _

set_option maxHeartbeats 800000 in
-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E9_split.  On `J_Y = (3Y/4, 5Y/2)`,
`ℰ₉ = ℰ_{9,+} + ℐ₁ + ℐ₂ + ℐ₃`, all integrals absolutely convergent. -/
theorem c06_E9_split (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ∀ y ∈ Ioo (3 * Y / 4) (5 * Y / 2),
          let f := approximate_solution_family P.p R ε μ
          let cf : ℝ → ℝ := fun x => res_chiY Y x * f x
          residual_decomposition_E9 P.p R ε μ Y y =
            c06_E9_split_plus P.p ε f Y y + c06_E9_split_I1 P.p ε f y +
              c06_E9_split_I2 P.p ε f y + c06_E9_split_I3 P.p ε f y ∧
          IntegrableOn (fun z => ((deriv f y - deriv f z) * (A_eps P.p ε (c01_secant f y z) - 1) -
              (deriv f y - deriv cf z) * (A_eps P.p ε (c01_secant cf y z) - 1)) /
              |y - z| ^ (1 + P.p)) (Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y)) ∧
          IntegrableOn (fun z => (A_eps P.p ε (c01_secant f y z) -
              A_eps P.p ε (c01_secant corner y z) -
              deriv (A_eps P.p ε) (c01_secant corner y z) *
                c01_secant (fun x => f x - corner x) y z) / (y - z) ^ (1 + P.p)) (Iio 0) ∧
          IntegrableOn (fun z => (deriv f y - deriv f z - 1) *
              (A_eps P.p ε (c01_secant f y z) - A_eps P.p ε (c01_secant corner y z)) /
              (y - z) ^ (1 + P.p)) (Iio 0) ∧
          IntegrableOn (fun z => deriv f y / (y - z) ^ (1 + P.p) *
              (A_eps P.p ε (f y / (y - z)) - 1)) (Iio 0) := by
  obtain ⟨R₀, hR₀, HC⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨B, hB1, HB⟩ := c06_aux_chiY_bound
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  refine ⟨R₀, hR₀, fun R hR Y hY ε hε μ hμ y hy => ?_⟩
  obtain ⟨C₀, hC₀, HC'⟩ := HC R hR
  obtain ⟨hfs, hc1, hc2, -, -⟩ := HC' ε hε μ hμ
  clear HC HC'
  intro f cf
  have hE9 : residual_decomposition_E9 P.p R ε μ Y y = c01_Q_eps P.p ε f y -
      c01_Q_eps P.p ε corner y - res_DQW P.p ε (fun z => f z - corner z) y -
      c01_Q_eps P.p ε cf y := rfl
  rw [hE9]
  replace hfs : ContDiff ℝ (⊤ : ℕ∞) f := hfs
  replace hc1 : ∀ z : ℝ, |deriv f z| ≤ C₀ ∧ |f z - corner z| ≤ C₀ * jb z ^ (-P.p) := hc1
  replace hc2 : ∀ z : ℝ, 0 ≤ z → |f z| ≤ C₀ * jb z ^ (-P.p) ∧ |deriv f z| ≤ C₀ * jb z ^ (-beta P.p) :=
    hc2
  clear_value f
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hy0 : 0 < y := by linarith [hy.1]
  have hε0 : 0 ≤ ε := hε.1
  have hεI : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, le_trans hε.2 hε₀1⟩
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  obtain ⟨hAc, hAb, -, -⟩ := HA ε hεI
  clear HA
  have hAcont : Continuous (A_eps P.p ε) := hAc.continuous
  have hdAcont : Continuous (deriv (A_eps P.p ε)) := hAc.continuous_deriv (by simp)
  have hdf : Differentiable ℝ f := hfs.differentiable (by simp)
  have hdfb : ∀ z, |deriv f z| ≤ C₀ := fun z => (hc1 z).1
  have hC₀0 : 0 ≤ C₀ := by linarith
  have hfL : LipschitzWith (Real.toNNReal C₀) f :=
    lipschitzWith_of_nnnorm_deriv_le hdf (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hC₀0]
      exact hdfb x)
  have hchis : ContDiff ℝ (⊤ : ℕ∞) (res_chiY Y) := c06_aux_chiY_smooth Y
  have hcfs : ContDiff ℝ (⊤ : ℕ∞) cf := hchis.mul hfs
  have hdcf : Differentiable ℝ cf := hcfs.differentiable (by simp)
  have hdchi : Differentiable ℝ (res_chiY Y) := hchis.differentiable (by simp)
  obtain ⟨hloc1, hloc0⟩ := c06_aux_chiY_local hY0 f
  have hdcfb : ∀ z, |deriv cf z| ≤ 2 * B * C₀ := by
    intro z
    rcases lt_or_ge z (3 * Y / 10) with hz | hz
    · rw [(hloc0 z hz).deriv_eq]; simp; positivity
    have hz0 : 0 ≤ z := by linarith
    have e : deriv cf z = deriv (res_chiY Y) z * f z + res_chiY Y z * deriv f z :=
      ((hdchi z).hasDerivAt.mul (hdf z).hasDerivAt).deriv
    have b1 : |deriv (res_chiY Y) z| ≤ B := by
      have := HB Y hY0 1 (by norm_num) z
      rw [iteratedDeriv_one] at this
      refine this.trans ?_
      have : Y ^ (-((1 : ℕ) : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY1 (by norm_num)
      nlinarith
    have b0 : |res_chiY Y z| ≤ B := by
      have := HB Y hY0 0 (by norm_num) z
      rw [iteratedDeriv_zero] at this
      simpa using this
    have bf : |f z| ≤ C₀ := by
      have := (hc2 z hz0).1
      have := c06_aux_jb_rpow_neg_le_one z P.p hp0.le
      nlinarith
    rw [e]
    calc _ ≤ |deriv (res_chiY Y) z * f z| + |res_chiY Y z * deriv f z| := abs_add_le _ _
      _ = |deriv (res_chiY Y) z| * |f z| + |res_chiY Y z| * |deriv f z| := by
          rw [abs_mul, abs_mul]
      _ ≤ B * C₀ + B * C₀ := by gcongr; exact hdfb z
      _ = _ := by ring
  have hBC : 0 ≤ 2 * B * C₀ := by positivity
  have hcfL : LipschitzWith (Real.toNNReal (2 * B * C₀)) cf :=
    lipschitzWith_of_nnnorm_deriv_le hdcf (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ hBC]
      exact hdcfb x)
  -- local identities
  have hyI : y ∈ Ioo (Y / 2) (3 * Y) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcy : cf y = f y := (hloc1 y hyI).eq_of_nhds
  have hdcy : deriv cf y = deriv f y := (hloc1 y hyI).deriv_eq
  have hC2 : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ContDiffOn ℝ 2 g (Ioi 0) := fun g hg =>
    (hg.of_le (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)).contDiffOn
  set Ff : ℝ → ℝ := fun z => (deriv f y - deriv f z) / |y - z| ^ (P.p + 1) *
    (A_eps P.p ε (c01_secant f y z) - 1) with hFf
  set Fc : ℝ → ℝ := fun z => (deriv cf y - deriv cf z) / |y - z| ^ (P.p + 1) *
    (A_eps P.p ε (c01_secant cf y z) - 1) with hFc
  set FW : ℝ → ℝ := fun z => (deriv corner y - deriv corner z) / |y - z| ^ (P.p + 1) *
    (A_eps P.p ε (c01_secant corner y z) - 1) with hFW
  set D : ℝ → ℝ := fun z => ((deriv (fun x => f x - corner x) y -
      deriv (fun x => f x - corner x) z) * (A_eps P.p ε (z / (y - z)) - 1) +
      deriv (A_eps P.p ε) (z / (y - z)) * c01_secant (fun x => f x - corner x) y z) /
      (y - z) ^ (P.p + 1) with hD
  have iFf : Integrable Ff := c06_aux_Qint P.p ε hp0 hp1 hε0 f _ hfL (hC2 f hfs) y hy0
  have iFc : Integrable Fc := c06_aux_Qint P.p ε hp0 hp1 hε0 cf _ hcfL (hC2 cf hcfs) y hy0
  have hWy : deriv corner y = 0 := ((c06_aux_corner_hasDeriv y).2 hy0).deriv
  have hWz : ∀ z, z < 0 → deriv corner z = -1 := fun z hz => ((c06_aux_corner_hasDeriv z).1 hz).deriv
  have hWsec : ∀ z, z < 0 → c01_secant corner y z = z / (y - z) := fun z hz => by
    have hne : y ≠ z := by intro e; linarith
    have hcy : corner y = 0 := by simp only [corner]; exact max_eq_right (by linarith)
    have hcz : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
    simp only [c01_secant, if_neg hne, hcy, hcz]; ring
  have hhy : deriv (fun x => f x - corner x) y = deriv f y := by
    have e := ((hdf y).hasDerivAt.sub ((c06_aux_corner_hasDeriv y).2 hy0)).deriv
    rw [sub_zero] at e; exact e
  have hhz : ∀ z, z < 0 → deriv (fun x => f x - corner x) z = deriv f z + 1 := fun z hz => by
    have e := ((hdf z).hasDerivAt.sub ((c06_aux_corner_hasDeriv z).1 hz)).deriv
    rw [sub_neg_eq_add] at e; exact e
  have hcfz : ∀ z, z < 0 → cf z = 0 ∧ deriv cf z = 0 := fun z hz =>
    ⟨(hloc0 z (by linarith)).eq_of_nhds, by rw [(hloc0 z (by linarith)).deriv_eq]; simp⟩
  -- the pieces on `(-∞,0)`
  set I1f : ℝ → ℝ := fun z => (A_eps P.p ε (c01_secant f y z) -
      A_eps P.p ε (c01_secant corner y z) -
      deriv (A_eps P.p ε) (c01_secant corner y z) *
        c01_secant (fun x => f x - corner x) y z) / (y - z) ^ (1 + P.p) with hI1f
  set I2f : ℝ → ℝ := fun z => (deriv f y - deriv f z - 1) *
      (A_eps P.p ε (c01_secant f y z) - A_eps P.p ε (c01_secant corner y z)) /
      (y - z) ^ (1 + P.p) with hI2f
  set I3f : ℝ → ℝ := fun z => deriv f y / (y - z) ^ (1 + P.p) *
      (A_eps P.p ε (f y / (y - z)) - 1) with hI3f
  have eFc : ∀ z, z < 0 → Fc z = I3f z := fun z hz => by
    have hyz : 0 < y - z := by linarith
    have hne : y ≠ z := by intro e; linarith
    obtain ⟨h0, hd0⟩ := hcfz z hz
    simp only [hFc, hI3f, hdcy, hd0, c01_secant, if_neg hne, hcy, h0, abs_of_pos hyz, sub_zero,
      add_comm (1 : ℝ) P.p]
  have eI1 : ∀ z, z < 0 → I1f z = Ff z - FW z - D z - I2f z := fun z hz => by
    have hyz : 0 < y - z := by linarith
    simp only [hI1f, hI2f, hFf, hFW, hD, hWy, hWz z hz, hhy, hhz z hz, hWsec z hz, abs_of_pos hyz,
      add_comm (1 : ℝ) P.p]
    have : 0 < (y - z) ^ (P.p + 1) := Real.rpow_pos_of_pos hyz _
    field_simp
    ring
  -- integrability on `(-∞,0)`
  have tail := (c06_aux_tail1 (P.p + 1) y (by linarith) hy0).1
  have hk : ∀ z, z < 0 → 1 / (y - z) ^ (P.p + 1) = (y - z) ^ (-(P.p + 1)) := fun z hz => by
    rw [Real.rpow_neg (by linarith), one_div]
  have hk' : ∀ z, z < 0 → 0 < (y - z) ^ (P.p + 1) := fun z hz => Real.rpow_pos_of_pos (by linarith) _
  have hsecm : ∀ g : ℝ → ℝ, Continuous g → Measurable (fun z => c01_secant g y z) :=
    fun g hg => c06_aux_secant_meas1 g hg y
  have hhc : Continuous (fun x => f x - corner x) :=
    hfs.continuous.sub (by unfold corner; fun_prop)
  have hcornc : Continuous corner := by unfold corner; fun_prop
  have iFW : IntegrableOn FW (Iio 0) := by
    refine Integrable.mono' (tail.const_mul 1) ?_
      ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
    · have m : Measurable FW := by
        simp only [hFW]
        exact ((measurable_const.sub (measurable_deriv corner)).div
          ((measurable_const.sub measurable_id).abs.pow_const _)).mul
          ((hAcont.measurable.comp (hsecm corner hcornc)).sub measurable_const)
      exact m.aestronglyMeasurable
    · have hz0 : z < 0 := hz
      have hyz : 0 < y - z := by linarith
      rw [Real.norm_eq_abs]
      simp only [hFW, hWy, hWz z hz0, abs_of_pos hyz]
      rw [show ((0 : ℝ) - -1) = 1 by ring, abs_mul, ← hk z hz0, one_mul,
        abs_of_pos (by simpa using hk' z hz0)]
      have := c06_aux_A_sub_one P.p ε (c01_secant corner y z) hp0 hε0
      calc _ ≤ 1 / (y - z) ^ (P.p + 1) * 1 :=
            mul_le_mul_of_nonneg_left this (one_div_nonneg.mpr (hk' z hz0).le)
        _ = _ := by ring
  have hsech : ∀ z, |c01_secant (fun x => f x - corner x) y z| ≤ C₀ + 1 := fun z => by
    by_cases hyz : y = z
    · subst hyz
      simp only [c01_secant, ↓reduceIte, hhy]; linarith [hdfb y]
    have hpos : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr hyz)
    simp only [c01_secant, if_neg hyz, abs_div]
    rw [div_le_iff₀ hpos]
    have h1 := hfL.dist_le_mul y z
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC₀0] at h1
    have h2 : |corner y - corner z| ≤ |y - z| := by
      unfold corner
      have := abs_max_sub_max_le_abs (-y) (-z) 0
      rwa [show -y - -z = -(y - z) by ring, abs_neg] at this
    have key : ∀ a b c d : ℝ, |a - b - (c - d)| ≤ |a - c| + |b - d| := fun a b c d => by
      rw [show a - b - (c - d) = (a - c) - (b - d) by ring]; exact abs_sub _ _
    calc |f y - corner y - (f z - corner z)| ≤ |f y - f z| + |corner y - corner z| := key _ _ _ _
      _ ≤ C₀ * |y - z| + |y - z| := add_le_add h1 h2
      _ = _ := by ring
  have iD : IntegrableOn D (Iio 0) := by
    refine Integrable.mono' (tail.const_mul ((2 * C₀ + 1) + (P.p + 1) * (C₀ + 1))) ?_
      ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
    · have m : Measurable D := by
        simp only [hD]
        exact (((measurable_const.sub (measurable_deriv (fun x => f x - corner x))).mul
          ((hAcont.measurable.comp (measurable_id.div (measurable_const.sub measurable_id))).sub
            measurable_const)).add
          ((hdAcont.measurable.comp (measurable_id.div (measurable_const.sub measurable_id))).mul
            (hsecm _ hhc))).div
          ((measurable_const.sub measurable_id).pow_const _)
      exact m.aestronglyMeasurable
    · have hz0 : z < 0 := hz
      have hyz : 0 < y - z := by linarith
      rw [Real.norm_eq_abs]
      simp only [hD, hhy, hhz z hz0]
      rw [abs_div, abs_of_pos (hk' z hz0), div_eq_mul_inv, ← one_div, hk z hz0]
      have hu : |z / (y - z)| ≤ 1 := by
        rw [abs_div, abs_of_pos hyz, div_le_one hyz, abs_of_neg hz0]; linarith
      have h1 : |deriv f y - (deriv f z + 1)| ≤ 2 * C₀ + 1 := by
        have := abs_sub (deriv f y) (deriv f z + 1)
        have := abs_add_le (deriv f z) 1
        linarith [hdfb y, hdfb z, (abs_one : |(1 : ℝ)| = 1)]
      have h2 := c06_aux_A_sub_one P.p ε (z / (y - z)) hp0 hε0
      have h3 : |deriv (A_eps P.p ε) (z / (y - z))| ≤ P.p + 1 := by
        calc _ ≤ (P.p + 1) * ε * |z / (y - z)| := (hAb _).2.1
          _ ≤ (P.p + 1) * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hεI.2 (by linarith)) hu (abs_nonneg _)
              (by linarith)
          _ = _ := by ring
      have hrp : 0 ≤ (y - z) ^ (-(P.p + 1)) := Real.rpow_nonneg hyz.le _
      calc _ ≤ (|deriv f y - (deriv f z + 1)| * |A_eps P.p ε (z / (y - z)) - 1| +
            |deriv (A_eps P.p ε) (z / (y - z))| * |c01_secant (fun x => f x - corner x) y z|) *
            (y - z) ^ (-(P.p + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ hrp
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ ((2 * C₀ + 1) * 1 + (P.p + 1) * (C₀ + 1)) * (y - z) ^ (-(P.p + 1)) := by
            refine mul_le_mul_of_nonneg_right (add_le_add ?_ ?_) hrp
            · exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
            · exact mul_le_mul h3 (hsech z) (abs_nonneg _) (by linarith)
        _ = _ := by ring
  have iI2 : IntegrableOn I2f (Iio 0) := by
    refine Integrable.mono' (tail.const_mul (2 * C₀ + 1)) ?_
      ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
    · have m : Measurable I2f := by
        simp only [hI2f]
        exact (((measurable_const.sub (measurable_deriv f)).sub measurable_const).mul
          ((hAcont.measurable.comp (hsecm f hfs.continuous)).sub
            (hAcont.measurable.comp (hsecm corner hcornc)))).div
          ((measurable_const.sub measurable_id).pow_const _)
      exact m.aestronglyMeasurable
    · have hz0 : z < 0 := hz
      have hyz : 0 < y - z := by linarith
      rw [Real.norm_eq_abs]
      simp only [hI2f]
      rw [add_comm (1 : ℝ) P.p, abs_div, abs_of_pos (hk' z hz0), div_eq_mul_inv, ← one_div,
        hk z hz0, abs_mul]
      have h1 : |deriv f y - deriv f z - 1| ≤ 2 * C₀ + 1 := by
        have := abs_sub (deriv f y) (deriv f z + 1)
        have := abs_add_le (deriv f z) 1
        rw [show deriv f y - deriv f z - 1 = deriv f y - (deriv f z + 1) by ring]
        linarith [hdfb y, hdfb z, (abs_one : |(1 : ℝ)| = 1)]
      have h2 : |A_eps P.p ε (c01_secant f y z) - A_eps P.p ε (c01_secant corner y z)| ≤ 1 := by
        obtain ⟨a1, a2⟩ := c06_aux_A_mem P.p ε (c01_secant f y z) hp0 hε0
        obtain ⟨b1, b2⟩ := c06_aux_A_mem P.p ε (c01_secant corner y z) hp0 hε0
        rw [abs_le]; constructor <;> linarith
      calc _ ≤ (2 * C₀ + 1) * 1 * (y - z) ^ (-(P.p + 1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (abs_nonneg _) (by linarith))
              (Real.rpow_nonneg hyz.le _)
        _ = _ := by ring
  have iI3 : IntegrableOn I3f (Iio 0) :=
    iFc.integrableOn.congr_fun (fun z hz => eFc z hz) measurableSet_Iio
  have iI1 : IntegrableOn I1f (Iio 0) :=
    (((iFf.integrableOn.sub iFW).sub iD).sub iI2).congr_fun (fun z hz => (eI1 z hz).symm)
      measurableSet_Iio
  -- the `(0,∞)` part
  set Pf : ℝ → ℝ := fun z => ((deriv f y - deriv f z) * (A_eps P.p ε (c01_secant f y z) - 1) -
      (deriv f y - deriv cf z) * (A_eps P.p ε (c01_secant cf y z) - 1)) / |y - z| ^ (1 + P.p)
    with hPf
  have ePf : ∀ z, Pf z = Ff z - Fc z := fun z => by
    simp only [hPf, hFf, hFc, hdcy, add_comm (1 : ℝ) P.p]; ring
  have iG : Integrable (fun z => Ff z - Fc z) := iFf.sub iFc
  have hGzero : ∀ z ∈ Ioo (Y / 2) (3 * Y), Ff z - Fc z = 0 := by
    intro z hz
    have hcz : cf z = f z := (hloc1 z hz).eq_of_nhds
    have hdz : deriv cf z = deriv f z := (hloc1 z hz).deriv_eq
    have hs : c01_secant cf y z = c01_secant f y z := by
      unfold c01_secant; rw [hdcy, hcy, hcz]
    simp only [hFf, hFc, hdcy, hdz, hs]; ring
  have hIcc : ∫ z in Icc (Y / 2) (3 * Y), (Ff z - Fc z) = 0 := by
    rw [integral_Icc_eq_integral_Ioo]
    exact setIntegral_eq_zero_of_forall_eq_zero (fun z hz => hGzero z hz)
  have hsub : Icc (Y / 2) (3 * Y) ⊆ Ioi (0 : ℝ) := fun z hz => by
    simp only [mem_Icc, mem_Ioi] at hz ⊢; linarith [hz.1]
  have hIoi : ∫ z in Ioi (0 : ℝ), (Ff z - Fc z) =
      ∫ z in Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y), (Ff z - Fc z) := by
    conv_lhs => rw [← diff_union_of_subset hsub]
    rw [setIntegral_union disjoint_sdiff_left measurableSet_Icc iG.integrableOn iG.integrableOn,
      hIcc, add_zero]
  -- `𝒬_ε(W)` only sees `(-∞,0)`
  have hFW0 : ∀ z, 0 < z → FW z = 0 := fun z hz => by
    simp only [hFW, hWy, ((c06_aux_corner_hasDeriv z).2 hz).deriv, sub_self, zero_div, zero_mul]
  have iFWall : Integrable FW := by
    rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ))]
    refine iFW.union ((integrableOn_Ici_iff_integrableOn_Ioi (f := FW)).mpr ?_)
    exact (integrableOn_zero).congr_fun (fun z hz => (hFW0 z hz).symm) measurableSet_Ioi
  have hFWint : ∫ z, FW z = ∫ z in Iio (0 : ℝ), FW z := by
    rw [c06_aux_split_line FW iFWall, setIntegral_eq_zero_of_forall_eq_zero (t := Ioi (0 : ℝ))
      (fun z hz => hFW0 z hz), add_zero]
  -- assemble
  have eQf : c01_Q_eps P.p ε f y = calpha P.p * ∫ z, Ff z := rfl
  have eQc : c01_Q_eps P.p ε cf y = calpha P.p * ∫ z, Fc z := rfl
  have eQW : c01_Q_eps P.p ε corner y = calpha P.p * ∫ z, FW z := rfl
  have eD : res_DQW P.p ε (fun z => f z - corner z) y = calpha P.p * ∫ z in Iio (0 : ℝ), D z := rfl
  have ePlus : c06_E9_split_plus P.p ε f Y y = calpha P.p * ((∫ z in Ioi (0 : ℝ), Ff z) -
      ∫ z in Ioi (0 : ℝ), Fc z) := by
    unfold c06_E9_split_plus
    congr 1
    rw [← integral_sub iFf.integrableOn iFc.integrableOn, hIoi]
    exact setIntegral_congr_fun (measurableSet_Ioi.diff measurableSet_Icc)
      (fun z _ => ePf z)
  have eI1 : c06_E9_split_I1 P.p ε f y = calpha P.p * ((∫ z in Iio (0 : ℝ), Ff z) -
      (∫ z in Iio (0 : ℝ), FW z) - (∫ z in Iio (0 : ℝ), D z) - ∫ z in Iio (0 : ℝ), I2f z) := by
    unfold c06_E9_split_I1
    congr 1
    have h2 : IntegrableOn (fun z => Ff z - FW z) (Iio 0) := iFf.integrableOn.sub iFW
    have h1 : IntegrableOn (fun z => Ff z - FW z - D z) (Iio 0) := h2.sub iD
    have e : ∫ z in Iio (0 : ℝ), I1f z = ∫ z in Iio (0 : ℝ), (Ff z - FW z - D z - I2f z) :=
      setIntegral_congr_fun measurableSet_Iio (fun z hz => eI1 z hz)
    refine e.trans ?_
    rw [integral_sub h1 iI2, integral_sub h2 iD, integral_sub iFf.integrableOn iFW]
  have eI3 : c06_E9_split_I3 P.p ε f y = -(calpha P.p * ∫ z in Iio (0 : ℝ), Fc z) := by
    unfold c06_E9_split_I3
    congr 2
    exact setIntegral_congr_fun measurableSet_Iio (fun z hz => (eFc z hz).symm)
  have eI2 : c06_E9_split_I2 P.p ε f y = calpha P.p * ∫ z in Iio (0 : ℝ), I2f z := rfl
  refine ⟨?_, ?_, iI1, iI2, iI3⟩
  · rw [eQf, eQc, eQW, eD, ePlus, eI1, eI2, eI3, hFWint, c06_aux_split_line Ff iFf,
      c06_aux_split_line Fc iFc]
    ring
  · exact (iG.integrableOn).congr_fun (fun z _ => (ePf z).symm)
      (measurableSet_Ioi.diff measurableSet_Icc)

/-! ### Helpers for c06_E9_positive -/
/-- Helper: `y`-derivative of `|y-z|^{-q}` away from the diagonal. -/
theorem c06_aux_E9pos_kder (q y z : ℝ) (hyz : y ≠ z) :
    HasDerivAt (fun y' => |y' - z| ^ (-q)) (-q * |y - z| ^ (-q) / (y - z)) y := by
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hyz) with h | h
  · have hd : HasDerivAt (fun y' => (z - y') ^ (-q)) (-1 * (-q) * (z - y) ^ (-q - 1)) y :=
      ((hasDerivAt_id y).const_sub z).rpow_const (Or.inl (by simp; linarith)) |>.congr_deriv (by simp)
    refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Iio_mem_nhds (show y < z by linarith)] with x hx
      rw [abs_of_neg (by linarith [mem_Iio.mp hx]), neg_sub]
    · rw [abs_of_neg h, neg_sub, Real.rpow_sub (by linarith), Real.rpow_one]
      have : z - y ≠ 0 := by linarith
      rw [show y - z = -(z - y) by ring]
      field_simp
  · have hd : HasDerivAt (fun y' => (y' - z) ^ (-q)) (1 * (-q) * (y - z) ^ (-q - 1)) y :=
      ((hasDerivAt_id y).sub_const z).rpow_const (Or.inl (by simp; linarith))
    refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [Ioi_mem_nhds (show z < y by linarith)] with x hx
      rw [abs_of_pos (by linarith [mem_Ioi.mp hx])]
    · rw [abs_of_pos h, Real.rpow_sub h, Real.rpow_one]
      ring

set_option maxHeartbeats 800000 in
/-- Helper for lem:c06_E9_positive: pointwise value, `y`-derivative and bounds of
`F_g(y,z) = (f'(y) - g'(z)) (A_ε(S_g(y,z)) - 1) |y-z|^{-1-p}` for `|y-z| ≥ 1`. -/
theorem c06_aux_E9pos_pt (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε)
    (hAd : Differentiable ℝ (A_eps p ε))
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (hAb2 : ∀ w, |deriv (A_eps p ε) w| ≤ (p + 1) * ε * |w|)
    (f g : ℝ → ℝ) (y z G0 G1 : ℝ) (hddf : DifferentiableAt ℝ (deriv f) y)
    (hSd : HasDerivAt (fun y' => c01_secant g y' z) ((deriv g y - c01_secant g y z) / (y - z)) y)
    (hyz : 1 ≤ |y - z|) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (h0 : |g y - g z| ≤ 2 * G0)
    (h1f : |deriv f y| ≤ G1) (h1y : |deriv g y| ≤ G1) (h1z : |deriv g z| ≤ G1) :
    HasDerivAt (fun y' => (deriv f y' - deriv g z) * (A_eps p ε (c01_secant g y' z) - 1) *
        |y' - z| ^ (-(1 + p)))
      (deriv (deriv f) y * (A_eps p ε (c01_secant g y z) - 1) * |y - z| ^ (-(1 + p)) +
        (deriv f y - deriv g z) * (deriv (A_eps p ε) (c01_secant g y z) *
          ((deriv g y - c01_secant g y z) / (y - z))) * |y - z| ^ (-(1 + p)) +
        (deriv f y - deriv g z) * (A_eps p ε (c01_secant g y z) - 1) *
          (-(1 + p) * |y - z| ^ (-(1 + p)) / (y - z))) y ∧
    |(deriv f y - deriv g z) * (A_eps p ε (c01_secant g y z) - 1) * |y - z| ^ (-(1 + p))| ≤
      8 * (p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) * ε * |y - z| ^ (-(3 + p)) ∧
    |deriv (deriv f) y * (A_eps p ε (c01_secant g y z) - 1) * |y - z| ^ (-(1 + p)) +
        (deriv f y - deriv g z) * (deriv (A_eps p ε) (c01_secant g y z) *
          ((deriv g y - c01_secant g y z) / (y - z))) * |y - z| ^ (-(1 + p)) +
        (deriv f y - deriv g z) * (A_eps p ε (c01_secant g y z) - 1) *
          (-(1 + p) * |y - z| ^ (-(1 + p)) / (y - z))| ≤
      8 * (p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) * ε *
        (|deriv (deriv f) y| + 1) * |y - z| ^ (-(3 + p)) := by
  have hu0 : 0 < |y - z| := by linarith
  have hne : y ≠ z := fun e => by rw [e, sub_self, abs_zero] at hyz; linarith
  have hdA : ∀ w, HasDerivAt (A_eps p ε) (deriv (A_eps p ε) w) w := fun w => (hAd w).hasDerivAt
  refine ⟨?_, ?_⟩
  · have h1 := (hddf.hasDerivAt.sub_const (deriv g z))
    have h2 := (HasDerivAt.comp (h₂ := A_eps p ε) y (hdA (c01_secant g y z)) hSd).sub_const 1
    have h3 := c06_aux_E9pos_kder (1 + p) y z hne
    exact ((h1.mul h2).mul h3).congr_deriv (by simp only [Function.comp_apply, Pi.mul_apply]; ring)
  set S := c01_secant g y z with hS
  set u := |y - z| with hu
  set w := u⁻¹ with hw
  have hw0 : 0 < w := inv_pos.mpr hu0
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hyz
  set κ := u ^ (-(1 + p)) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos hu0 _
  have h3p : u ^ (-(3 + p)) = w ^ 2 * κ := by
    rw [show -(3 + p) = -2 + -(1 + p) by ring, Real.rpow_add hu0]
    rw [show u ^ (-2 : ℝ) = w ^ 2 by rw [Real.rpow_neg hu0.le, hw, inv_pow]; norm_num]
  have hSv : |S| ≤ 2 * G0 * w := by
    rw [hS]; unfold c01_secant; rw [if_neg hne, abs_div, ← hu, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h0 hw0.le
  have hS2 : S ^ 2 ≤ (2 * G0 * w) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hSv 2
  have hAm : |A_eps p ε S - 1| ≤ 2 * (p + 1) * G0 ^ 2 * ε * w ^ 2 := by
    rw [abs_sub_comm, abs_of_nonneg (hAb1 S).1]
    calc _ ≤ (p + 1) / 2 * ε * S ^ 2 := (hAb1 S).2
      _ ≤ (p + 1) / 2 * ε * (2 * G0 * w) ^ 2 := by gcongr
      _ = _ := by ring
  have hA' : |deriv (A_eps p ε) S| ≤ (p + 1) * ε * (2 * G0 * w) := by
    calc _ ≤ (p + 1) * ε * |S| := hAb2 S
      _ ≤ _ := by gcongr
  have hdS : |(deriv g y - S) / (y - z)| ≤ (G1 + 2 * G0) * w := by
    rw [abs_div, ← hu, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ hw0.le
    calc |deriv g y - S| ≤ |deriv g y| + |S| := abs_sub _ _
      _ ≤ G1 + 2 * G0 * 1 := by gcongr; exact hSv.trans (by nlinarith)
      _ = _ := by ring
  have hk' : |-(1 + p) * κ / (y - z)| = (1 + p) * κ * w := by
    rw [abs_div, abs_mul, ← hu, abs_neg, abs_of_pos (by linarith : (0:ℝ) < 1 + p),
      abs_of_pos hκ0, div_eq_mul_inv]
  have hfg : |deriv f y - deriv g z| ≤ 2 * G1 := by
    have := abs_sub (deriv f y) (deriv g z); linarith
  set K := 8 * (p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) with hK
  set X := 2 * (p + 2) ^ 2 * (G0 + 1) ^ 2 with hX
  set V := 4 * (G1 + 1) * (G1 + 2 * G0 + 1) with hV
  have hKXV : K = X * V := by rw [hK, hX, hV]; ring
  have hX0 : 0 ≤ X := by positivity
  have hp2 : p + 1 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg (p + 1)]
  have hp2' : (p + 1) * (1 + p) ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg (p + 1)]
  have hG0' : G0 ≤ (G0 + 1) ^ 2 := by nlinarith [sq_nonneg G0]
  have hG0'' : G0 ^ 2 ≤ (G0 + 1) ^ 2 := by nlinarith [sq_nonneg G0]
  have xA : 2 * (p + 1) * G0 ^ 2 ≤ X := by
    have := mul_le_mul hp2 hG0'' (sq_nonneg _) (by positivity); rw [hX]; nlinarith
  have xB : 2 * (p + 1) * G0 ≤ X := by
    have := mul_le_mul hp2 hG0' hG0 (by positivity); rw [hX]; nlinarith
  have xC : 2 * ((p + 1) * (1 + p)) * G0 ^ 2 ≤ X := by
    have := mul_le_mul hp2' hG0'' (sq_nonneg _) (by positivity); rw [hX]; nlinarith
  have vA : 1 ≤ V := by rw [hV]; nlinarith
  have vB : 2 * G1 * (G1 + 2 * G0 + 1) ≤ V := by rw [hV]; nlinarith
  have hc1 : 4 * (p + 1) * G0 ^ 2 * G1 * 1 ≤ K := by
    rw [hKXV]
    have : 2 * G1 ≤ V := by nlinarith
    calc 4 * (p + 1) * G0 ^ 2 * G1 * 1 = (2 * (p + 1) * G0 ^ 2) * (2 * G1) := by ring
      _ ≤ X * V := mul_le_mul xA this (by positivity) hX0
  clear_value K X V
  constructor
  · rw [h3p, abs_mul, abs_mul, abs_of_pos hκ0]
    calc |deriv f y - deriv g z| * |A_eps p ε S - 1| * κ
        ≤ (2 * G1) * (2 * (p + 1) * G0 ^ 2 * ε * w ^ 2) * κ := by gcongr
      _ = (4 * (p + 1) * G0 ^ 2 * G1 * 1) * ε * (w ^ 2 * κ) := by ring
      _ ≤ K * ε * (w ^ 2 * κ) := by gcongr
  · rw [h3p]
    have e1 : |deriv (deriv f) y * (A_eps p ε S - 1) * κ| ≤
        |deriv (deriv f) y| * (2 * (p + 1) * G0 ^ 2 * ε * w ^ 2) * κ := by
      rw [abs_mul, abs_mul, abs_of_pos hκ0]; gcongr
    have e2 : |(deriv f y - deriv g z) * (deriv (A_eps p ε) S * ((deriv g y - S) / (y - z))) * κ| ≤
        (2 * G1) * ((p + 1) * ε * (2 * G0 * w) * ((G1 + 2 * G0) * w)) * κ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hκ0]; gcongr
    have e3 : |(deriv f y - deriv g z) * (A_eps p ε S - 1) * (-(1 + p) * κ / (y - z))| ≤
        (2 * G1) * (2 * (p + 1) * G0 ^ 2 * ε * w ^ 2) * ((1 + p) * κ * w) := by
      rw [abs_mul, abs_mul, hk']; gcongr
    have hfpp := abs_nonneg (deriv (deriv f) y)
    have c1 : 2 * (p + 1) * G0 ^ 2 ≤ K := by
      rw [hKXV]; exact xA.trans (le_mul_of_one_le_right hX0 vA)
    have c2 : 4 * (p + 1) * G0 * G1 * (G1 + 2 * G0) + 4 * (p + 1) * (1 + p) * G0 ^ 2 * G1 ≤ K := by
      rw [hKXV]
      have a1 : 4 * (p + 1) * G0 * G1 * (G1 + 2 * G0) ≤ X * (2 * G1 * (G1 + 2 * G0)) := by
        have := mul_le_mul_of_nonneg_right xB (show 0 ≤ 2 * G1 * (G1 + 2 * G0) by positivity)
        calc _ = 2 * (p + 1) * G0 * (2 * G1 * (G1 + 2 * G0)) := by ring
          _ ≤ _ := this
      have a2 : 4 * (p + 1) * (1 + p) * G0 ^ 2 * G1 ≤ X * (2 * G1) := by
        have := mul_le_mul_of_nonneg_right xC (show 0 ≤ 2 * G1 by positivity)
        calc _ = 2 * ((p + 1) * (1 + p)) * G0 ^ 2 * (2 * G1) := by ring
          _ ≤ _ := this
      have a3 : X * (2 * G1 * (G1 + 2 * G0)) + X * (2 * G1) ≤ X * V := by
        rw [← mul_add]; refine mul_le_mul_of_nonneg_left ?_ hX0
        calc _ = 2 * G1 * (G1 + 2 * G0 + 1) := by ring
          _ ≤ V := vB
      linarith
    have hw3 : w ^ 3 ≤ w ^ 2 := pow_le_pow_of_le_one hw0.le hw1 (by norm_num)
    calc _ ≤ |deriv (deriv f) y * (A_eps p ε S - 1) * κ| +
          |(deriv f y - deriv g z) * (deriv (A_eps p ε) S * ((deriv g y - S) / (y - z))) * κ| +
          |(deriv f y - deriv g z) * (A_eps p ε S - 1) * (-(1 + p) * κ / (y - z))| :=
          abs_add_three _ _ _
      _ ≤ |deriv (deriv f) y| * (2 * (p + 1) * G0 ^ 2 * ε * w ^ 2) * κ +
          (2 * G1) * ((p + 1) * ε * (2 * G0 * w) * ((G1 + 2 * G0) * w)) * κ +
          (2 * G1) * (2 * (p + 1) * G0 ^ 2 * ε * w ^ 2) * ((1 + p) * κ * w) :=
          add_le_add (add_le_add e1 e2) e3
      _ = (2 * (p + 1) * G0 ^ 2) * ε * |deriv (deriv f) y| * (w ^ 2 * κ) +
          (4 * (p + 1) * G0 * G1 * (G1 + 2 * G0)) * ε * (w ^ 2 * κ) +
          (4 * (p + 1) * (1 + p) * G0 ^ 2 * G1) * ε * (w ^ 3 * κ) := by ring
      _ ≤ K * ε * |deriv (deriv f) y| * (w ^ 2 * κ) +
          (4 * (p + 1) * G0 * G1 * (G1 + 2 * G0)) * ε * (w ^ 2 * κ) +
          (4 * (p + 1) * (1 + p) * G0 ^ 2 * G1) * ε * (w ^ 2 * κ) := by gcongr
      _ = K * ε * |deriv (deriv f) y| * (w ^ 2 * κ) +
          (4 * (p + 1) * G0 * G1 * (G1 + 2 * G0) + 4 * (p + 1) * (1 + p) * G0 ^ 2 * G1) *
            (ε * (w ^ 2 * κ)) := by ring
      _ ≤ K * ε * |deriv (deriv f) y| * (w ^ 2 * κ) + K * (ε * (w ^ 2 * κ)) := by gcongr
      _ = K * ε * |deriv (deriv f) y| * (w ^ 2 * κ) + K * ε * (w ^ 2 * κ) := by ring
      _ = K * ε * (|deriv (deriv f) y| + 1) * (w ^ 2 * κ) := by ring

/-- Helper: `y ↦ S_g(y,z)` is differentiable off the diagonal. -/
theorem c06_aux_E9pos_secd (g : ℝ → ℝ) (y z : ℝ) (hyz : y ≠ z) (hg : DifferentiableAt ℝ g y) :
    HasDerivAt (fun y' => c01_secant g y' z) ((deriv g y - c01_secant g y z) / (y - z)) y := by
  have hne : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hd : HasDerivAt (fun y' => (g y' - g z) / (y' - z))
      ((deriv g y * (y - z) - (g y - g z) * 1) / (y - z) ^ 2) y :=
    (hg.hasDerivAt.sub_const (g z)).div ((hasDerivAt_id y).sub_const z) hne
  have hev : (fun y' => c01_secant g y' z) =ᶠ[𝓝 y] fun y' => (g y' - g z) / (y' - z) := by
    filter_upwards [isOpen_ne.mem_nhds hyz] with x hx
    simp only [c01_secant, if_neg (show ¬x = z from hx)]
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [c01_secant, if_neg hyz]
  field_simp

/-- Helper: `z ↦ S_g(y,z)` is measurable for continuous `g`. -/
theorem c06_aux_E9pos_secm (g : ℝ → ℝ) (hg : Continuous g) (y : ℝ) :
    Measurable (fun z => c01_secant g y z) := by
  unfold c01_secant
  exact Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const
    ((measurable_const.sub hg.measurable).div (measurable_const.sub measurable_id))

/-- Helper (lem:c06_E9_positive): `F_g(y,z) = (f'(y) - g'(z)) (A_ε(S_g(y,z)) - 1) |y-z|^{-1-p}`. -/
def c06_aux_E9pos_F (p ε : ℝ) (f g : ℝ → ℝ) (y z : ℝ) : ℝ :=
  (deriv f y - deriv g z) * (A_eps p ε (c01_secant g y z) - 1) * |y - z| ^ (-(1 + p))

/-- Helper (lem:c06_E9_positive): the `y`-derivative of `F_g`. -/
def c06_aux_E9pos_dF (p ε : ℝ) (f g : ℝ → ℝ) (y z : ℝ) : ℝ :=
  deriv (deriv f) y * (A_eps p ε (c01_secant g y z) - 1) * |y - z| ^ (-(1 + p)) +
    (deriv f y - deriv g z) * (deriv (A_eps p ε) (c01_secant g y z) *
      ((deriv g y - c01_secant g y z) / (y - z))) * |y - z| ^ (-(1 + p)) +
    (deriv f y - deriv g z) * (A_eps p ε (c01_secant g y z) - 1) *
      (-(1 + p) * |y - z| ^ (-(1 + p)) / (y - z))

/-- Helper: distances for `z ∈ (0,∞) ∖ [Y/2,3Y]`. -/
theorem c06_aux_E9pos_dist (Y y z : ℝ) (hz : z ∈ Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y))
    (h1 : Y / 2 + Y / 8 ≤ y) (h2 : y ≤ 3 * Y - Y / 8) : Y / 8 ≤ |y - z| := by
  obtain ⟨-, hz2⟩ := hz
  simp only [mem_Icc, not_and_or, not_le] at hz2
  rcases hz2 with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- Helper for lem:c06_E9_positive: differentiation under the integral and bounds for
`∫_{(0,∞)∖[Y/2,3Y]} F_g(y,z) dz`. -/
theorem c06_aux_E9pos_int (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε)
    (hAc : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε))
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (hAb2 : ∀ w, |deriv (A_eps p ε) w| ≤ (p + 1) * ε * |w|)
    (f g : ℝ → ℝ) (hddf : Differentiable ℝ (deriv f)) (hdg : Differentiable ℝ g)
    (Y G0 G1 M2 : ℝ) (hY : 8 ≤ Y) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hM2 : 0 ≤ M2)
    (b0 : ∀ x, 0 ≤ x → |g x| ≤ G0) (b1 : ∀ x, 0 ≤ x → |deriv g x| ≤ G1)
    (b1f : ∀ x, 0 ≤ x → |deriv f x| ≤ G1)
    (b2 : ∀ x, Y / 2 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ M2) :
    (∀ y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2),
      IntegrableOn (fun z => c06_aux_E9pos_F p ε f g y₀ z) (Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y)) ∧
      HasDerivAt (fun y => ∫ z in Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y), c06_aux_E9pos_F p ε f g y z)
        (∫ z in Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y), c06_aux_E9pos_dF p ε f g y₀ z) y₀) ∧
    (∀ y ∈ Icc Y (2 * Y),
      |∫ z in Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y), c06_aux_E9pos_F p ε f g y z| ≤
        8 * (p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) * ε *
          (2 * (Y / 4) ^ (1 - (3 + p)) / (3 + p - 1)) ∧
      |∫ z in Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y), c06_aux_E9pos_dF p ε f g y z| ≤
        8 * (p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) * ε *
          (|deriv (deriv f) y| + 1) * (2 * (Y / 4) ^ (1 - (3 + p)) / (3 + p - 1))) := by
  set D := Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y) with hD
  have hDm : MeasurableSet D := measurableSet_Ioi.diff measurableSet_Icc
  set K := 8 * (p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hY0 : 0 < Y := by linarith
  have hAd : Differentiable ℝ (A_eps p ε) := hAc.differentiable (by simp)
  have hAcont : Continuous (A_eps p ε) := hAc.continuous
  have hdAcont : Continuous (deriv (A_eps p ε)) := hAc.continuous_deriv (by simp)
  have ha : 1 < 3 + p := by linarith
  -- the pointwise facts
  have PT : ∀ y z, z ∈ D → Y / 2 + Y / 8 ≤ y → y ≤ 3 * Y - Y / 8 →
      HasDerivAt (fun y' => c06_aux_E9pos_F p ε f g y' z) (c06_aux_E9pos_dF p ε f g y z) y ∧
      |c06_aux_E9pos_F p ε f g y z| ≤ K * ε * |y - z| ^ (-(3 + p)) ∧
      |c06_aux_E9pos_dF p ε f g y z| ≤ K * ε * (|deriv (deriv f) y| + 1) * |y - z| ^ (-(3 + p)) := by
    intro y z hz h1 h2
    have hd := c06_aux_E9pos_dist Y y z hz h1 h2
    have hyz1 : 1 ≤ |y - z| := le_trans (by linarith) hd
    have hne : y ≠ z := fun e => by rw [e, sub_self, abs_zero] at hyz1; linarith
    have hz0 : 0 ≤ z := le_of_lt hz.1
    have hy0 : 0 ≤ y := by linarith
    have h0 : |g y - g z| ≤ 2 * G0 := by
      have := abs_sub (g y) (g z); linarith [b0 y hy0, b0 z hz0]
    exact c06_aux_E9pos_pt p ε hp hε hAd hAb1 hAb2 f g y z G0 G1 (hddf y)
      (c06_aux_E9pos_secd g y z hne (hdg y)) hyz1 hG0 hG1 h0 (b1f y hy0) (b1 y hy0) (b1 z hz0)
  -- measurability
  have hgc : Continuous g := hdg.continuous
  have mF : ∀ y, Measurable (fun z => c06_aux_E9pos_F p ε f g y z) := fun y => by
    unfold c06_aux_E9pos_F
    exact ((measurable_const.sub (measurable_deriv g)).mul
      ((hAcont.measurable.comp (c06_aux_E9pos_secm g hgc y)).sub measurable_const)).mul
      ((measurable_const.sub measurable_id).abs.pow_const _)
  have mdF : ∀ y, Measurable (fun z => c06_aux_E9pos_dF p ε f g y z) := fun y => by
    unfold c06_aux_E9pos_dF
    have hs := c06_aux_E9pos_secm g hgc y
    have hk : Measurable (fun z : ℝ => |y - z| ^ (-(1 + p))) :=
      (measurable_const.sub measurable_id).abs.pow_const _
    exact ((measurable_const.mul ((hAcont.measurable.comp hs).sub measurable_const)).mul hk).add
      (((measurable_const.sub (measurable_deriv g)).mul ((hdAcont.measurable.comp hs).mul
        ((measurable_const.sub hs).div (measurable_const.sub measurable_id)))).mul hk) |>.add
      (((measurable_const.sub (measurable_deriv g)).mul
        ((hAcont.measurable.comp hs).sub measurable_const)).mul
        ((measurable_const.mul hk).div (measurable_const.sub measurable_id)))
  -- tails
  have hsub : ∀ y, Y / 2 + Y / 8 ≤ y → y ≤ 3 * Y - Y / 8 →
      D ⊆ {z | Y / 8 ≤ |y - z|} := fun y h1 h2 z hz => c06_aux_E9pos_dist Y y z hz h1 h2
  have tailI : ∀ y r, 0 < r → D ⊆ {z | r ≤ |y - z|} →
      IntegrableOn (fun z => |y - z| ^ (-(3 + p))) D := fun y r hr hDs =>
    (c06_aux_tail2 (3 + p) r y ha hr).1.mono_set hDs
  have hsub4 : ∀ y, 3 * Y / 4 ≤ y → y ≤ 5 * Y / 2 → D ⊆ {z | Y / 4 ≤ |y - z|} := by
    intro y h1 h2 z hz
    obtain ⟨-, hz2⟩ := hz
    simp only [mem_Icc, not_and_or, not_le] at hz2
    show Y / 4 ≤ |y - z|
    rcases hz2 with h | h
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  have hY4 : 0 < Y / 4 := by linarith
  refine ⟨fun y₀ hy₀ => ?_, fun y hy => ?_⟩
  · have h1 : 3 * Y / 4 ≤ y₀ := hy₀.1.le
    have h2 : y₀ ≤ 5 * Y / 2 := hy₀.2.le
    have hD4 := hsub4 y₀ h1 h2
    have hT := tailI y₀ (Y / 4) hY4 hD4
    have hy₀a : Y / 2 + Y / 8 ≤ y₀ := by linarith
    have hy₀b : y₀ ≤ 3 * Y - Y / 8 := by linarith
    have iF : IntegrableOn (fun z => c06_aux_E9pos_F p ε f g y₀ z) D :=
      Integrable.mono' (hT.const_mul (K * ε)) (mF y₀).aestronglyMeasurable
        ((ae_restrict_iff' hDm).mpr (ae_of_all _ fun z hz => by
          rw [Real.norm_eq_abs]; exact (PT y₀ z hz hy₀a hy₀b).2.1))
    refine ⟨iF, ?_⟩
    have hball : ∀ y ∈ Metric.ball y₀ (Y / 8), Y / 2 + Y / 8 ≤ y ∧ y ≤ 3 * Y - Y / 8 ∧
        |y - y₀| < Y / 8 := fun y hy => by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_lt.mp hy
      exact ⟨by linarith, by linarith, hy⟩
    have hcmp : ∀ y ∈ Metric.ball y₀ (Y / 8), ∀ z ∈ D,
        |y - z| ^ (-(3 + p)) ≤ 2 ^ (3 + p) * |y₀ - z| ^ (-(3 + p)) := by
      intro y hy z hz
      obtain ⟨-, -, hyy⟩ := hball y hy
      have hz4 : Y / 4 ≤ |y₀ - z| := hD4 hz
      have hge : |y₀ - z| / 2 ≤ |y - z| := by
        have := abs_sub_abs_le_abs_sub (y₀ - z) (y - z)
        rw [show y₀ - z - (y - z) = -(y - y₀) by ring, abs_neg] at this
        linarith
      calc |y - z| ^ (-(3 + p)) ≤ (|y₀ - z| / 2) ^ (-(3 + p)) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) hge (by linarith)
        _ = 2 ^ (3 + p) * |y₀ - z| ^ (-(3 + p)) := by
            rw [Real.div_rpow (abs_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
            field_simp
    have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict D)
      (F := fun y z => c06_aux_E9pos_F p ε f g y z)
      (F' := fun y z => c06_aux_E9pos_dF p ε f g y z) (x₀ := y₀)
      (bound := fun z => K * ε * (M2 + 1) * (2 ^ (3 + p) * |y₀ - z| ^ (-(3 + p))))
      (s := Metric.ball y₀ (Y / 8)) (Metric.ball_mem_nhds _ (by linarith))
      (Eventually.of_forall fun y => (mF y).aestronglyMeasurable) iF
      (mdF y₀).aestronglyMeasurable
      ((ae_restrict_iff' hDm).mpr (ae_of_all _ fun z hz y hy => by
        obtain ⟨ha1, ha2, -⟩ := hball y hy
        rw [Real.norm_eq_abs]
        refine (PT y z hz ha1 ha2).2.2.trans ?_
        have hm : |deriv (deriv f) y| + 1 ≤ M2 + 1 := by
          linarith [b2 y (by linarith) (by linarith)]
        have := hcmp y hy z hz
        have h0 : 0 ≤ |y - z| ^ (-(3 + p)) := by positivity
        calc K * ε * (|deriv (deriv f) y| + 1) * |y - z| ^ (-(3 + p))
            ≤ K * ε * (M2 + 1) * (2 ^ (3 + p) * |y₀ - z| ^ (-(3 + p))) := by gcongr))
      ((hT.const_mul (2 ^ (3 + p))).const_mul (K * ε * (M2 + 1)))
      ((ae_restrict_iff' hDm).mpr (ae_of_all _ fun z hz y hy => by
        obtain ⟨ha1, ha2, -⟩ := hball y hy
        exact (PT y z hz ha1 ha2).1))
    exact H.2
  · have h1 : 3 * Y / 4 ≤ y := by linarith [hy.1]
    have h2 : y ≤ 5 * Y / 2 := by linarith [hy.2]
    have hD4 := hsub4 y h1 h2
    have hT := tailI y (Y / 4) hY4 hD4
    obtain ⟨hTi, hTv⟩ := c06_aux_tail2 (3 + p) (Y / 4) y ha hY4
    have hya : Y / 2 + Y / 8 ≤ y := by linarith
    have hyb : y ≤ 3 * Y - Y / 8 := by linarith
    have hmono : ∫ z in D, |y - z| ^ (-(3 + p)) ≤ 2 * (Y / 4) ^ (1 - (3 + p)) / (3 + p - 1) := by
      rw [← hTv]
      exact setIntegral_mono_set hTi (ae_of_all _ fun z => by positivity)
        (Eventually.of_forall hD4)
    have hI0 : 0 ≤ ∫ z in D, |y - z| ^ (-(3 + p)) :=
      setIntegral_nonneg hDm (fun z _ => by positivity)
    constructor
    · have := norm_integral_le_of_norm_le (hT.const_mul (K * ε))
        ((ae_restrict_iff' hDm).mpr (ae_of_all _ fun z hz => by
          rw [Real.norm_eq_abs]; exact (PT y z hz hya hyb).2.1))
      rw [Real.norm_eq_abs, integral_const_mul] at this
      refine this.trans ?_
      have : 0 ≤ K * ε := by positivity
      gcongr
    · have := norm_integral_le_of_norm_le (hT.const_mul (K * ε * (|deriv (deriv f) y| + 1)))
        ((ae_restrict_iff' hDm).mpr (ae_of_all _ fun z hz => by
          rw [Real.norm_eq_abs]; exact (PT y z hz hya hyb).2.2))
      rw [Real.norm_eq_abs, integral_const_mul] at this
      refine this.trans ?_
      have : 0 ≤ K * ε * (|deriv (deriv f) y| + 1) := by positivity
      gcongr

set_option maxHeartbeats 800000 in
-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E9_positive.  `ℰ_{9,+}` is differentiable on `J_Y` and
`|∂^j ℰ_{9,+}| ≤ C ε Y^{-p-2+j/p}` on `[Y,2Y]`. -/
theorem c06_E9_positive (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let E : ℝ → ℝ := c06_E9_split_plus P.p ε (approximate_solution_family P.p R ε μ) Y
        DifferentiableOn ℝ E (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j E y| ≤ C * ε * Y ^ (-P.p - 2 + j / P.p) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hplo := P.hp_lo
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hinv2 : 1 / P.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have he1 : 1 / P.p - beta P.p ≤ 1 := by
    unfold beta
    rw [show 1 / P.p - (P.p + 1) / (2 * P.p) = (1 - P.p) / (2 * P.p) by field_simp; ring]
    rw [div_le_one (by positivity)]; linarith
  have he0 : 0 ≤ 1 / P.p - beta P.p := by linarith
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  obtain ⟨B, hB1, HB⟩ := c06_aux_chiY_bound
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  have hB0 : 0 ≤ B := by linarith
  set G0 : ℝ := B * C₀ with hG0
  set G1 : ℝ := 2 * B * C₀ with hG1
  have hG00 : 0 ≤ G0 := by positivity
  have hG10 : 0 ≤ G1 := by positivity
  set K := 8 * (P.p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨|calpha P.p| * 128 * K * (2 * C₀ + 1) + 1, by positivity, ?_⟩
  intro Y hY ε hε μ hμ E
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, h1, h2, -, h3⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  have hAb1 : ∀ w, 0 ≤ 1 - A_eps P.p ε w ∧ 1 - A_eps P.p ε w ≤ (P.p + 1) / 2 * ε * w ^ 2 :=
    fun w => (hAb w).1
  have hAb2 : ∀ w, |deriv (A_eps P.p ε) w| ≤ (P.p + 1) * ε * |w| := fun w => (hAb w).2.1
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun x => res_chiY Y x * f x with hcf
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have ddf : Differentiable ℝ (deriv f) := by
    simpa using hfs.differentiable_iteratedDeriv 1 htop1
  have hχd : Differentiable ℝ (res_chiY Y) := (c06_aux_chiY_smooth Y).differentiable (by simp)
  have dcf : Differentiable ℝ cf := hχd.mul df
  have bf2 : ∀ x, 1 ≤ x → |deriv (deriv f) x| ≤ C₀ * x ^ (-beta P.p + 1 / P.p) := fun x hx => by
    have := (h3 x hx).2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have b2 : ∀ x, Y / 2 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y) := fun x hx hx3 => by
    have hx1 : 1 ≤ x := by linarith
    refine le_trans (bf2 x hx1) (mul_le_mul_of_nonneg_left ?_ hC₀0)
    have : x ^ (-beta P.p + 1 / P.p) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_one] at this; linarith
  have bf0 : ∀ x, 0 ≤ x → |f x| ≤ C₀ := fun x hx => le_trans (h2 x hx).1
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos (c06_aux_one_le_jb x)
      (by linarith)))
  have bf1 : ∀ x, |deriv f x| ≤ C₀ := fun x => (h1 x).1
  have bχ0 : ∀ x, |res_chiY Y x| ≤ B := fun x => by
    have := HB Y hY0 0 (by norm_num) x
    simpa using this
  have bχ1 : ∀ x, |deriv (res_chiY Y) x| ≤ B := fun x => by
    have := HB Y hY0 1 (by norm_num) x
    rw [iteratedDeriv_one] at this
    refine this.trans ?_
    have : Y ^ (-((1 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hY1 (by norm_num)
    nlinarith
  have b0f : ∀ x, 0 ≤ x → |f x| ≤ G0 := fun x hx =>
    (bf0 x hx).trans (by rw [hG0]; nlinarith)
  have b1f : ∀ x, 0 ≤ x → |deriv f x| ≤ G1 := fun x _ =>
    (bf1 x).trans (by rw [hG1]; nlinarith)
  have b0c : ∀ x, 0 ≤ x → |cf x| ≤ G0 := fun x hx => by
    simp only [hcf, abs_mul]
    exact mul_le_mul (bχ0 x) (bf0 x hx) (abs_nonneg _) hB0
  have b1c : ∀ x, 0 ≤ x → |deriv cf x| ≤ G1 := fun x hx => by
    have hd : deriv cf x = deriv (res_chiY Y) x * f x + res_chiY Y x * deriv f x :=
      ((hχd x).hasDerivAt.mul (df x).hasDerivAt).deriv
    rw [hd]
    calc _ ≤ |deriv (res_chiY Y) x * f x| + |res_chiY Y x * deriv f x| := abs_add_le _ _
      _ ≤ B * C₀ + B * C₀ := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (bχ1 x) (bf0 x hx) (abs_nonneg _) hB0)
            (mul_le_mul (bχ0 x) (bf1 x) (abs_nonneg _) hB0)
      _ = G1 := by rw [hG1]; ring
  have hM2 : 0 ≤ C₀ * (3 * Y) := by positivity
  obtain ⟨Hf1, Hf2⟩ := c06_aux_E9pos_int P.p ε hp0 hε0 hAc hAb1 hAb2 f f ddf df Y G0 G1
    (C₀ * (3 * Y)) hY8 hG00 hG10 hM2 b0f b1f b1f b2
  obtain ⟨Hc1, Hc2⟩ := c06_aux_E9pos_int P.p ε hp0 hε0 hAc hAb1 hAb2 f cf ddf dcf Y G0 G1
    (C₀ * (3 * Y)) hY8 hG00 hG10 hM2 b0c b1c b1f b2
  set D := Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y) with hD
  have hEq : ∀ y ∈ Ioo (3 * Y / 4) (5 * Y / 2), E y = calpha P.p *
      ((∫ z in D, c06_aux_E9pos_F P.p ε f f y z) - ∫ z in D, c06_aux_E9pos_F P.p ε f cf y z) := by
    intro y hy
    rw [← integral_sub (Hf1 y hy).1 (Hc1 y hy).1]
    show calpha P.p * _ = _
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [c06_aux_E9pos_F]
    rw [Real.rpow_neg (abs_nonneg _), add_comm 1 P.p]
    simp only [hcf]
    ring
  have hderiv : ∀ y ∈ Ioo (3 * Y / 4) (5 * Y / 2), HasDerivAt E (calpha P.p *
      ((∫ z in D, c06_aux_E9pos_dF P.p ε f f y z) - ∫ z in D, c06_aux_E9pos_dF P.p ε f cf y z)) y :=
    fun y hy => (((Hf1 y hy).2.sub (Hc1 y hy).2).const_mul (calpha P.p)).congr_of_eventuallyEq
      (by filter_upwards [isOpen_Ioo.mem_nhds hy] with x hx using hEq x hx)
  refine ⟨fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt, ?_⟩
  intro y hy j hj
  have hyJ : y ∈ Ioo (3 * Y / 4) (5 * Y / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  have f2 : |deriv (deriv f) y| ≤ 2 * C₀ * Y ^ (1 / P.p) := by
    refine le_trans (bf2 y hy1) ?_
    have h1 : y ^ (-beta P.p + 1 / P.p) ≤ (2 * Y) ^ (-beta P.p + 1 / P.p) :=
      Real.rpow_le_rpow hy0.le hy.2 (by linarith)
    rw [Real.mul_rpow (by norm_num) hY0.le] at h1
    have h2 : (2 : ℝ) ^ (-beta P.p + 1 / P.p) ≤ 2 := by
      conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : Y ^ (-beta P.p + 1 / P.p) ≤ Y ^ (1 / P.p) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by
        have : 0 < beta P.p := by unfold beta; positivity
        linarith)
    have h4 : 0 ≤ Y ^ (-beta P.p + 1 / P.p) := Real.rpow_nonneg hY0.le _
    have h5 : (2 : ℝ) ^ (-beta P.p + 1 / P.p) * Y ^ (-beta P.p + 1 / P.p) ≤ 2 * Y ^ (1 / P.p) :=
      mul_le_mul h2 h3 h4 (by norm_num)
    have := mul_le_mul_of_nonneg_left (le_trans h1 h5) hC₀0
    linarith [show C₀ * (2 * Y ^ (1 / P.p)) = 2 * C₀ * Y ^ (1 / P.p) by ring]
  -- the tail constant
  set T := 2 * (Y / 4) ^ (1 - (3 + P.p)) / (3 + P.p - 1) with hT
  have hYv : 0 ≤ Y ^ (-P.p - 2) := Real.rpow_nonneg hY0.le _
  have hTle : T ≤ 64 * Y ^ (-P.p - 2) := by
    have e : (Y / 4) ^ (-P.p - 2) = 4 ^ (P.p + 2) * Y ^ (-P.p - 2) := by
      rw [Real.div_rpow hY0.le (by norm_num), show (-P.p - 2) = -(P.p + 2) by ring,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
      field_simp
    have h4 : (4 : ℝ) ^ (P.p + 2) ≤ 64 := by
      calc (4 : ℝ) ^ (P.p + 2) ≤ 4 ^ (3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 64 := by norm_num
    rw [hT, show 1 - (3 + P.p) = -P.p - 2 by ring, show 3 + P.p - 1 = 2 + P.p by ring, e,
      div_le_iff₀ (by linarith)]
    have h40 : 0 ≤ (4 : ℝ) ^ (P.p + 2) := by positivity
    have := mul_le_mul_of_nonneg_right h4 hYv
    have := mul_nonneg hp0.le hYv
    linarith
  have hT0 : 0 ≤ T := by
    rw [hT]; exact div_nonneg (by positivity) (by linarith)
  have hYp : 1 ≤ Y ^ (1 / P.p) := Real.one_le_rpow hY1 (by positivity)
  have hCa := abs_nonneg (calpha P.p)
  obtain ⟨Bf0, Bf1⟩ := Hf2 y hy
  obtain ⟨Bc0, Bc1⟩ := Hc2 y hy
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
    rw [hEq y hyJ, abs_mul]
    have hI : |(∫ z in D, c06_aux_E9pos_F P.p ε f f y z) - ∫ z in D, c06_aux_E9pos_F P.p ε f cf y z|
        ≤ 2 * K * ε * (64 * Y ^ (-P.p - 2)) := by
      have hKe : 0 ≤ K * ε := by positivity
      calc _ ≤ |∫ z in D, c06_aux_E9pos_F P.p ε f f y z| + |∫ z in D, c06_aux_E9pos_F P.p ε f cf y z| :=
            abs_sub _ _
        _ ≤ K * ε * T + K * ε * T := add_le_add Bf0 Bc0
        _ ≤ K * ε * (64 * Y ^ (-P.p - 2)) + K * ε * (64 * Y ^ (-P.p - 2)) := by gcongr
        _ = _ := by ring
    have h0 : 0 ≤ |calpha P.p| * 128 * K * (2 * C₀) * ε * Y ^ (-P.p - 2) + ε * Y ^ (-P.p - 2) := by
      positivity
    calc |calpha P.p| * _ ≤ |calpha P.p| * (2 * K * ε * (64 * Y ^ (-P.p - 2))) :=
          mul_le_mul_of_nonneg_left hI hCa
      _ ≤ _ := by
          rw [show (|calpha P.p| * 128 * K * (2 * C₀ + 1) + 1) * ε * Y ^ (-P.p - 2) =
            |calpha P.p| * (2 * K * ε * (64 * Y ^ (-P.p - 2))) +
              (|calpha P.p| * 128 * K * (2 * C₀) * ε * Y ^ (-P.p - 2) + ε * Y ^ (-P.p - 2)) by ring]
          exact le_add_of_nonneg_right h0
  · simp only [iteratedDeriv_one, Nat.cast_one]
    rw [(hderiv y hyJ).deriv, abs_mul]
    have hf2' : |deriv (deriv f) y| + 1 ≤ (2 * C₀ + 1) * Y ^ (1 / P.p) := by linarith
    have hI : |(∫ z in D, c06_aux_E9pos_dF P.p ε f f y z) - ∫ z in D, c06_aux_E9pos_dF P.p ε f cf y z|
        ≤ 2 * K * ε * ((2 * C₀ + 1) * Y ^ (1 / P.p)) * (64 * Y ^ (-P.p - 2)) := by
      have hKe : 0 ≤ K * ε := by positivity
      calc _ ≤ |∫ z in D, c06_aux_E9pos_dF P.p ε f f y z| +
            |∫ z in D, c06_aux_E9pos_dF P.p ε f cf y z| := abs_sub _ _
        _ ≤ K * ε * (|deriv (deriv f) y| + 1) * T + K * ε * (|deriv (deriv f) y| + 1) * T :=
            add_le_add Bf1 Bc1
        _ ≤ K * ε * ((2 * C₀ + 1) * Y ^ (1 / P.p)) * (64 * Y ^ (-P.p - 2)) +
            K * ε * ((2 * C₀ + 1) * Y ^ (1 / P.p)) * (64 * Y ^ (-P.p - 2)) := by gcongr
        _ = _ := by ring
    have e : Y ^ (-P.p - 2 + 1 / P.p) = Y ^ (1 / P.p) * Y ^ (-P.p - 2) := by
      rw [Real.rpow_add hY0]; ring
    rw [e]
    have hYq : 0 ≤ Y ^ (1 / P.p) := by positivity
    have h0 : 0 ≤ ε * (Y ^ (1 / P.p) * Y ^ (-P.p - 2)) := by positivity
    calc |calpha P.p| * _ ≤ |calpha P.p| *
          (2 * K * ε * ((2 * C₀ + 1) * Y ^ (1 / P.p)) * (64 * Y ^ (-P.p - 2))) :=
          mul_le_mul_of_nonneg_left hI hCa
      _ ≤ _ := by
          rw [show (|calpha P.p| * 128 * K * (2 * C₀ + 1) + 1) * ε *
              (Y ^ (1 / P.p) * Y ^ (-P.p - 2)) = |calpha P.p| *
              (2 * K * ε * ((2 * C₀ + 1) * Y ^ (1 / P.p)) * (64 * Y ^ (-P.p - 2))) +
              ε * (Y ^ (1 / P.p) * Y ^ (-P.p - 2)) by ring]
          exact le_add_of_nonneg_right h0

/-! ### Helpers for c06_E9_I1 -/
/-- Helper: `(1/s)² s^{-(1+p)} = s^{-(3+p)}` for `s > 0`. -/
theorem c06_aux_rpow3 (p s : ℝ) (hs : 0 < s) :
    (1 / s) ^ 2 * s ^ (-(1 + p)) = s ^ (-(3 + p)) := by
  rw [show -(3 + p) = -(1 + p) + (-2 : ℝ) by ring, Real.rpow_add hs, Real.rpow_neg hs.le,
    Real.rpow_neg hs.le (2 : ℝ), Real.rpow_two]
  field_simp

/-- Helper (lem:c06_E9_I1): mean value bound `|φ(v) - φ(0)| ≤ B|v|` when `|φ'| ≤ B` on `[-|v|,|v|]`. -/
theorem c06_aux_E9I1_mvt (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (v B : ℝ)
    (hB : ∀ t, |t| ≤ |v| → |deriv φ t| ≤ B) : |φ v - φ 0| ≤ B * |v| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc (-|v|) |v|) (f := φ) (C := B)
    (fun x _ => hφ x) (fun x hx => by rw [Real.norm_eq_abs]; exact hB x (abs_le.mpr hx))
    (convex_Icc _ _) (x := 0) (y := v) ⟨by linarith [abs_nonneg v], abs_nonneg v⟩
    ⟨neg_abs_le v, le_abs_self v⟩
  simpa [Real.norm_eq_abs] using h

/-- Helper (lem:c06_E9_I1): first- and second-order Taylor bounds from `|g''| ≤ K`. -/
theorem c06_aux_E9I1_taylor (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (hg' : Differentiable ℝ (deriv g)) (K : ℝ) (hK : ∀ w, |deriv (deriv g) w| ≤ K) (u v : ℝ) :
    |deriv g (u + v) - deriv g u| ≤ K * |v| ∧
    |g (u + v) - g u - deriv g u * v| ≤ K * v ^ 2 := by
  have hin : ∀ s, HasDerivAt (fun s : ℝ => u + s) 1 s := fun s => (hasDerivAt_id' s).const_add u
  have he1 : ∀ s, HasDerivAt (fun s => deriv g (u + s)) (deriv (deriv g) (u + s)) s := fun s =>
    ((hg' (u + s)).hasDerivAt.comp s (hin s)).congr_deriv (mul_one _)
  have h1 : ∀ t, |deriv g (u + t) - deriv g u| ≤ K * |t| := fun t => by
    have := c06_aux_E9I1_mvt (fun s => deriv g (u + s)) (fun s => (he1 s).differentiableAt) t K
      (fun s _ => by rw [(he1 s).deriv]; exact hK (u + s))
    simpa using this
  refine ⟨h1 v, ?_⟩
  have hd : ∀ s, HasDerivAt (fun s => g (u + s) - deriv g u * s) (deriv g (u + s) - deriv g u) s :=
    fun s => (((hg (u + s)).hasDerivAt.comp s (hin s)).sub
      ((hasDerivAt_id' s).const_mul (deriv g u))).congr_deriv (by ring)
  have := c06_aux_E9I1_mvt (fun s => g (u + s) - deriv g u * s) (fun s => (hd s).differentiableAt)
    v (K * |v|) (fun s hs => by
      rw [(hd s).deriv]
      exact (h1 s).trans (mul_le_mul_of_nonneg_left hs (le_trans (abs_nonneg _) (hK 0))))
  simp only [add_zero, mul_zero, sub_zero] at this
  calc _ = |g (u + v) - deriv g u * v - g u| := by ring_nf
    _ ≤ K * |v| * |v| := this
    _ = K * v ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- Helper (lem:c06_E9_I1): the `ℐ₁` integrand for `y > 0 > z`, written with
`u = S_W = z/(y-z)`, `v = S_{f-W} = (f(y)-f(z)-z)/(y-z)`. -/
def c06_aux_E9I1_H (a : ℝ → ℝ) (p : ℝ) (f : ℝ → ℝ) (y z : ℝ) : ℝ :=
  (a (z / (y - z) + (f y - f z - z) / (y - z)) - a (z / (y - z)) -
    deriv a (z / (y - z)) * ((f y - f z - z) / (y - z))) * (y - z) ^ (-(1 + p))

/-- Helper (lem:c06_E9_I1): the `y`-derivative of `c06_aux_E9I1_H`. -/
def c06_aux_E9I1_dH (a : ℝ → ℝ) (p : ℝ) (f : ℝ → ℝ) (y z : ℝ) : ℝ :=
  ((deriv a (z / (y - z) + (f y - f z - z) / (y - z)) - deriv a (z / (y - z)) -
      deriv (deriv a) (z / (y - z)) * ((f y - f z - z) / (y - z))) * (-(z / (y - z)) * (1 / (y - z))) +
    (deriv a (z / (y - z) + (f y - f z - z) / (y - z)) - deriv a (z / (y - z))) *
      ((deriv f y - (f y - f z - z) / (y - z)) * (1 / (y - z))) -
    (1 + p) * (a (z / (y - z) + (f y - f z - z) / (y - z)) - a (z / (y - z)) -
      deriv a (z / (y - z)) * ((f y - f z - z) / (y - z))) * (1 / (y - z))) * (y - z) ^ (-(1 + p))

/-- Helper (lem:c06_E9_I1): `∂_y H = dH`. -/
theorem c06_aux_E9I1_hasDeriv (a : ℝ → ℝ) (p : ℝ) (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (ha : Differentiable ℝ a) (ha' : Differentiable ℝ (deriv a)) (x z : ℝ) (hxz : z < x) :
    HasDerivAt (fun x => c06_aux_E9I1_H a p f x z) (c06_aux_E9I1_dH a p f x z) x := by
  have hs : 0 < x - z := by linarith
  have hne : x - z ≠ 0 := hs.ne'
  have hw : HasDerivAt (fun x => x - z) 1 x := (hasDerivAt_id' x).sub_const z
  have hu : HasDerivAt (fun x => z / (x - z)) ((0 * (x - z) - z * 1) / (x - z) ^ 2) x :=
    (hasDerivAt_const x z).div hw hne
  have hv : HasDerivAt (fun x => (f x - f z - z) / (x - z))
      ((deriv f x * (x - z) - (f x - f z - z) * 1) / (x - z) ^ 2) x :=
    (((hf x).hasDerivAt.sub_const (f z)).sub_const z).div hw hne
  have h1 := (ha _).hasDerivAt.comp x (hu.add hv)
  have h2 := (ha _).hasDerivAt.comp x hu
  have h3 := ((ha' _).hasDerivAt.comp x hu).mul hv
  have hQ : HasDerivAt (fun x => (x - z) ^ (-(1 + p))) (1 * (-(1 + p)) * (x - z) ^ (-(1 + p) - 1)) x :=
    hw.rpow_const (Or.inl hne)
  have hT := ((h1.sub h2).sub h3).mul hQ
  unfold c06_aux_E9I1_H c06_aux_E9I1_dH
  refine hT.congr_deriv ?_
  have eu : (0 * (x - z) - z * 1) / (x - z) ^ 2 = -(z / (x - z)) * (1 / (x - z)) := by
    field_simp; ring
  have ev : (deriv f x * (x - z) - (f x - f z - z) * 1) / (x - z) ^ 2 =
      (deriv f x - (f x - f z - z) / (x - z)) * (1 / (x - z)) := by
    field_simp
  simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  rw [eu, ev, Real.rpow_sub_one hne]
  ring

/-- Helper (lem:c06_E9_I1): the `ℐ₁` integrand equals `H` for `y > 0 > z`. -/
theorem c06_aux_E9I1_pt (p ε : ℝ) (f : ℝ → ℝ) (y z : ℝ) (hy : 0 < y) (hz : z < 0) :
    (A_eps p ε (c01_secant f y z) - A_eps p ε (c01_secant corner y z) -
      deriv (A_eps p ε) (c01_secant corner y z) * c01_secant (fun x => f x - corner x) y z) /
      (y - z) ^ (1 + p) = c06_aux_E9I1_H (A_eps p ε) p f y z := by
  have hs : 0 < y - z := by linarith
  have hne : y ≠ z := by intro e; linarith
  have hcy : corner y = 0 := by simp only [corner]; exact max_eq_right (by linarith)
  have hcz : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
  unfold c06_aux_E9I1_H c01_secant
  simp only [if_neg hne, hcy, hcz]
  have e1 : (f y - f z) / (y - z) = z / (y - z) + (f y - f z - z) / (y - z) := by
    field_simp; ring
  have e2 : (0 - -z) / (y - z) = z / (y - z) := by ring_nf
  have e3 : (f y - 0 - (f z - -z)) / (y - z) = (f y - f z - z) / (y - z) := by ring_nf
  rw [e1, e2, e3, Real.rpow_neg hs.le, div_eq_mul_inv]

/-- Helper (lem:c06_E9_I1): algebraic bound of `dH`. -/
theorem c06_aux_E9I1_alg (K C₀ p d D1 u v T E2 E3 : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C₀) (hp : 0 ≤ p)
    (hd : 0 ≤ d) (hu : |u| ≤ 1) (hv : |v| ≤ 2 * C₀ * d) (hT : |T| ≤ K * v ^ 2)
    (hE2 : |E2| ≤ K * |v|) (hE3 : |E3| ≤ K * v ^ 2) :
    |E3 * (-u * d) + E2 * ((D1 - v) * d) - (1 + p) * T * d| ≤
      K * ((8 + 4 * (1 + p)) * C₀ ^ 2 * d ^ 3 + 2 * C₀ * |D1| * d ^ 2) := by
  have hv2 : v ^ 2 ≤ 4 * C₀ ^ 2 * d ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg v]
  have a1 : |E3 * (-u * d)| ≤ K * (4 * C₀ ^ 2 * d ^ 2) * d := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hd]
    have : |E3| ≤ K * (4 * C₀ ^ 2 * d ^ 2) := hE3.trans (mul_le_mul_of_nonneg_left hv2 hK)
    calc |E3| * (|u| * d) ≤ (K * (4 * C₀ ^ 2 * d ^ 2)) * (1 * d) := by gcongr
      _ = _ := by ring
  have a2 : |E2 * ((D1 - v) * d)| ≤ K * (2 * C₀ * d) * ((|D1| + 2 * C₀ * d) * d) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hd]
    have h1 : |E2| ≤ K * (2 * C₀ * d) := hE2.trans (mul_le_mul_of_nonneg_left hv hK)
    have h2 : |D1 - v| ≤ |D1| + 2 * C₀ * d := (abs_sub _ _).trans (by linarith)
    gcongr
  have a3 : |(1 + p) * T * d| ≤ (1 + p) * (K * (4 * C₀ ^ 2 * d ^ 2)) * d := by
    rw [abs_mul, abs_mul, abs_of_nonneg hd, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + p)]
    have : |T| ≤ K * (4 * C₀ ^ 2 * d ^ 2) := hT.trans (mul_le_mul_of_nonneg_left hv2 hK)
    gcongr
  calc _ ≤ |E3 * (-u * d)| + |E2 * ((D1 - v) * d)| + |(1 + p) * T * d| := by
        refine (abs_sub _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ _ := by nlinarith [a1, a2, a3]

/-- Helper: `(1/s)³ s^{-(1+p)} = s^{-(4+p)}` for `s > 0`. -/
theorem c06_aux_E9I1_rpow4 (p s : ℝ) (hs : 0 < s) :
    (1 / s) ^ 3 * s ^ (-(1 + p)) = s ^ (-(4 + p)) := by
  rw [show -(4 + p) = -(1 + p) + (-3 : ℝ) by ring, Real.rpow_add hs, Real.rpow_neg hs.le,
    Real.rpow_neg hs.le (3 : ℝ), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- Helper (lem:c06_E9_I1): pointwise bounds of `H` and `dH` for `y > 0 > z`. -/
theorem c06_aux_E9I1_bounds (a : ℝ → ℝ) (p : ℝ) (f : ℝ → ℝ) (K C₀ : ℝ)
    (ha : Differentiable ℝ a) (ha' : Differentiable ℝ (deriv a))
    (ha'' : Differentiable ℝ (deriv (deriv a)))
    (hK2 : ∀ w, |deriv (deriv a) w| ≤ K) (hK3 : ∀ w, |deriv (deriv (deriv a)) w| ≤ K)
    (hC₀ : 0 ≤ C₀) (hp : 0 ≤ p) (hg : ∀ x, |f x - corner x| ≤ C₀) (y z : ℝ) (hy : 0 < y)
    (hz : z < 0) :
    |c06_aux_E9I1_H a p f y z| ≤ K * (4 * C₀ ^ 2) * (y - z) ^ (-(3 + p)) ∧
    |c06_aux_E9I1_dH a p f y z| ≤ K * ((8 + 4 * (1 + p)) * C₀ ^ 2 * (y - z) ^ (-(4 + p)) +
      2 * C₀ * |deriv f y| * (y - z) ^ (-(3 + p))) := by
  have hs : 0 < y - z := by linarith
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hK2 0)
  set d := 1 / (y - z) with hd
  have hd0 : 0 ≤ d := by positivity
  set u := z / (y - z) with hu
  set v := (f y - f z - z) / (y - z) with hv
  have hcy : corner y = 0 := by simp only [corner]; exact max_eq_right (by linarith)
  have hcz : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
  have hub : |u| ≤ 1 := by
    rw [hu, abs_div, abs_of_pos hs, div_le_one hs, abs_of_neg hz]; linarith
  have hvb : |v| ≤ 2 * C₀ * d := by
    have e : f y - f z - z = (f y - corner y) - (f z - corner z) := by rw [hcy, hcz]; ring
    have h1 : |f y - f z - z| ≤ 2 * C₀ := by
      rw [e]; have := abs_sub (f y - corner y) (f z - corner z); linarith [hg y, hg z]
    rw [hv, hd, abs_div, abs_of_pos hs]
    rw [div_le_iff₀ hs]; field_simp; linarith
  obtain ⟨-, hT⟩ := c06_aux_E9I1_taylor a ha ha' K hK2 u v
  obtain ⟨hE2, -⟩ := c06_aux_E9I1_taylor a ha ha' K hK2 u v
  obtain ⟨-, hE3⟩ := c06_aux_E9I1_taylor (deriv a) ha' ha'' K hK3 u v
  have hv2 : v ^ 2 ≤ 4 * C₀ ^ 2 * d ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_nonneg v]
  have hQ := Real.rpow_pos_of_pos hs (-(1 + p))
  constructor
  · unfold c06_aux_E9I1_H
    rw [← hu, ← hv, abs_mul, abs_of_pos hQ, ← c06_aux_rpow3 p (y - z) hs, ← hd]
    calc _ ≤ K * v ^ 2 * (y - z) ^ (-(1 + p)) := by gcongr
      _ ≤ K * (4 * C₀ ^ 2 * d ^ 2) * (y - z) ^ (-(1 + p)) := by gcongr
      _ = _ := by ring
  · unfold c06_aux_E9I1_dH
    rw [← hu, ← hv, ← hd, abs_mul, abs_of_pos hQ]
    have halg := c06_aux_E9I1_alg K C₀ p d (deriv f y) u v _ _ _ hK hC₀ hp hd0 hub hvb hT hE2 hE3
    have e : K * ((8 + 4 * (1 + p)) * C₀ ^ 2 * (y - z) ^ (-(4 + p)) +
        2 * C₀ * |deriv f y| * (y - z) ^ (-(3 + p))) =
        K * ((8 + 4 * (1 + p)) * C₀ ^ 2 * d ^ 3 + 2 * C₀ * |deriv f y| * d ^ 2) *
          (y - z) ^ (-(1 + p)) := by
      rw [← c06_aux_rpow3 p (y - z) hs, ← c06_aux_E9I1_rpow4 p (y - z) hs, ← hd]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right halg hQ.le

/-- Helper (lem:c06_E9_I1): differentiation of `∫_{-∞}^0 H(y,z) dz` under the integral sign. -/
theorem c06_aux_E9I1_hasDeriv_int (a : ℝ → ℝ) (p : ℝ) (f : ℝ → ℝ) (K C₀ Y : ℝ)
    (hac : Continuous a) (ha : Differentiable ℝ a) (ha' : Differentiable ℝ (deriv a))
    (ha'' : Differentiable ℝ (deriv (deriv a)))
    (hK2 : ∀ w, |deriv (deriv a) w| ≤ K) (hK3 : ∀ w, |deriv (deriv (deriv a)) w| ≤ K)
    (hC₀ : 0 ≤ C₀) (hp : 0 < p) (hf : Differentiable ℝ f) (hg : ∀ x, |f x - corner x| ≤ C₀)
    (hd1 : ∀ x, |deriv f x| ≤ C₀) (hY : 8 ≤ Y) (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2)) :
    HasDerivAt (fun y => ∫ z in Iio (0 : ℝ), c06_aux_E9I1_H a p f y z)
      (∫ z in Iio (0 : ℝ), c06_aux_E9I1_dH a p f y₀ z) y₀ := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hK2 0)
  have mA : Measurable a := hac.measurable
  have mdA : Measurable (deriv a) := measurable_deriv _
  have mddA : Measurable (deriv (deriv a)) := measurable_deriv _
  have mf : Measurable f := hf.continuous.measurable
  have mG : ∀ x, AEStronglyMeasurable (fun z => c06_aux_E9I1_H a p f x z)
      (volume.restrict (Iio 0)) := fun x => by
    refine Measurable.aestronglyMeasurable ?_
    unfold c06_aux_E9I1_H
    fun_prop
  have mG' : AEStronglyMeasurable (fun z => c06_aux_E9I1_dH a p f y₀ z)
      (volume.restrict (Iio 0)) := by
    refine Measurable.aestronglyMeasurable ?_
    unfold c06_aux_E9I1_dH
    fun_prop
  set x₁ := 5 * Y / 8 with hx₁
  have hx₁1 : 1 ≤ x₁ := by rw [hx₁]; linarith
  set M : ℝ := K * ((8 + 4 * (1 + p)) * C₀ ^ 2 + 2 * C₀ * C₀) with hM
  have hball : ∀ x ∈ Metric.ball y₀ (Y / 8), x₁ ≤ x := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    linarith [hy₀.1]
  have hbd : ∀ x ∈ Metric.ball y₀ (Y / 8), ∀ z, z < 0 →
      |c06_aux_E9I1_dH a p f x z| ≤ M * (x₁ - z) ^ (-(3 + p)) := by
    intro x hx z hz
    have hx1 := hball x hx
    have hs : 1 ≤ x - z := by linarith
    have hs1 : 1 ≤ x₁ - z := by linarith
    have b := (c06_aux_E9I1_bounds a p f K C₀ ha ha' ha'' hK2 hK3 hC₀ hp.le hg x z
      (by linarith) hz).2
    have m1 : (x - z) ^ (-(4 + p)) ≤ (x - z) ^ (-(3 + p)) :=
      Real.rpow_le_rpow_of_exponent_le hs (by linarith)
    have m2 : (x - z) ^ (-(3 + p)) ≤ (x₁ - z) ^ (-(3 + p)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h0 : 0 ≤ (x - z) ^ (-(4 + p)) := Real.rpow_nonneg (by linarith) _
    have h0' : 0 ≤ (x - z) ^ (-(3 + p)) := Real.rpow_nonneg (by linarith) _
    refine b.trans ?_
    rw [hM]
    have e1 : (8 + 4 * (1 + p)) * C₀ ^ 2 * (x - z) ^ (-(4 + p)) ≤
        (8 + 4 * (1 + p)) * C₀ ^ 2 * (x₁ - z) ^ (-(3 + p)) := by
      gcongr; exact m1.trans m2
    have e2 : 2 * C₀ * |deriv f x| * (x - z) ^ (-(3 + p)) ≤ 2 * C₀ * C₀ * (x₁ - z) ^ (-(3 + p)) := by
      gcongr
      · exact hd1 x
    calc _ ≤ K * ((8 + 4 * (1 + p)) * C₀ ^ 2 * (x₁ - z) ^ (-(3 + p)) +
          2 * C₀ * C₀ * (x₁ - z) ^ (-(3 + p))) := by gcongr
      _ = _ := by ring
  have hy₀0 : 0 < y₀ := by linarith [hy₀.1]
  have hintG : Integrable (fun z => c06_aux_E9I1_H a p f y₀ z) (volume.restrict (Iio 0)) := by
    refine Integrable.mono' (((c06_aux_tail1 (3 + p) y₀ (by linarith) hy₀0).1).const_mul
      (K * (4 * C₀ ^ 2))) (mG y₀) ?_
    refine (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_)
    rw [Real.norm_eq_abs]
    exact (c06_aux_E9I1_bounds a p f K C₀ ha ha' ha'' hK2 hK3 hC₀ hp.le hg y₀ z hy₀0 hz).1
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Iio 0))
    (F := fun x z => c06_aux_E9I1_H a p f x z) (F' := fun x z => c06_aux_E9I1_dH a p f x z)
    (x₀ := y₀) (bound := fun z => M * (x₁ - z) ^ (-(3 + p)))
    (s := Metric.ball y₀ (Y / 8)) (Metric.ball_mem_nhds _ (by linarith))
    (Eventually.of_forall mG) hintG mG'
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz x hx => by
      rw [Real.norm_eq_abs]; exact hbd x hx z hz))
    (((c06_aux_tail1 (3 + p) x₁ (by linarith) (by linarith)).1).const_mul _)
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz x hx =>
      c06_aux_E9I1_hasDeriv a p f hf ha ha' x z (by
        have := hball x hx; have : z < 0 := hz; linarith)))
  exact H.2

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E9_I1.  `ℐ₁` is differentiable on `J_Y`, `|ℐ₁| ≤ C ε Y^{-p-2}`,
`|∂_y ℐ₁| ≤ C ε Y^{-p-3}` on `[Y,2Y]`. -/
theorem c06_E9_I1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let E : ℝ → ℝ := c06_E9_split_I1 P.p ε (approximate_solution_family P.p R ε μ)
        DifferentiableOn ℝ E (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ∀ y ∈ Icc Y (2 * Y),
          |E y| ≤ C * ε * Y ^ (-P.p - 2) ∧ |deriv E y| ≤ C * ε * Y ^ (-P.p - 3) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hb1 : 1 ≤ beta P.p := by
    unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, hCA, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  set N : ℝ := (8 + 4 * (1 + P.p)) * C₀ ^ 2 + 2 * C₀ * C₀ with hN
  refine ⟨|calpha P.p| * CA * (4 * C₀ ^ 2 + N) + 1, by positivity, ?_⟩
  intro Y hY ε hε μ hμ E
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, h1, -, -, h3⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  set f := approximate_solution_family P.p R ε μ with hf
  set a := A_eps P.p ε with ha
  set K : ℝ := CA * ε with hK
  have hK0 : 0 ≤ K := by positivity
  have htop : ∀ n : ℕ, ((n : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := fun n =>
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  have da : Differentiable ℝ a := hAc.differentiable (by simp)
  have da' : Differentiable ℝ (deriv a) := by
    simpa using hAc.differentiable_iteratedDeriv 1 (htop 1)
  have da'' : Differentiable ℝ (deriv (deriv a)) := by
    simpa [iteratedDeriv_succ] using hAc.differentiable_iteratedDeriv 2 (htop 2)
  have hK2 : ∀ w, |deriv (deriv a) w| ≤ K := fun w => by
    have := (hAb w).2.2.1
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    linarith [abs_nonneg (deriv (deriv (deriv a)) w)]
  have hK3 : ∀ w, |deriv (deriv (deriv a)) w| ≤ K := fun w => by
    have := (hAb w).2.2.1
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    linarith [abs_nonneg (deriv (deriv a) w)]
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have hg : ∀ x, |f x - corner x| ≤ C₀ := fun x => (h1 x).2.trans
    (mul_le_of_le_one_right hC₀0 (c06_aux_jb_rpow_neg_le_one x P.p hp0.le))
  have hd1 : ∀ x, |deriv f x| ≤ C₀ := fun x => (h1 x).1
  -- `E = c_α ∫ H` on `(0,∞)`
  have hEq : ∀ y, 0 < y → E y = calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I1_H a P.p f y z :=
    fun y hy => by
      show calpha P.p * _ = _
      congr 1
      exact setIntegral_congr_fun measurableSet_Iio (fun z hz => c06_aux_E9I1_pt P.p ε f y z hy hz)
  have hderiv : ∀ y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2), HasDerivAt E
      (calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I1_dH a P.p f y₀ z) y₀ := fun y₀ hy₀ => by
    have hy₀0 : 0 < y₀ := by linarith [hy₀.1]
    exact ((c06_aux_E9I1_hasDeriv_int a P.p f K C₀ Y hAc.continuous da da' da'' hK2 hK3 hC₀0
      hp0 df hg hd1 hY8 y₀ hy₀).const_mul (calpha P.p)).congr_of_eventuallyEq
      (by filter_upwards [Ioi_mem_nhds hy₀0] with y hy using hEq y hy)
  refine ⟨fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt, ?_⟩
  intro y hy
  have hyJ : y ∈ Ioo (3 * Y / 4) (5 * Y / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  have hCa := abs_nonneg (calpha P.p)
  obtain ⟨hti3, htv3⟩ := c06_aux_tail1 (3 + P.p) y (by linarith) hy0
  obtain ⟨hti4, htv4⟩ := c06_aux_tail1 (4 + P.p) y (by linarith) hy0
  have hI3 : ∫ z in Iio (0 : ℝ), (y - z) ^ (-(3 + P.p)) ≤ Y ^ (-P.p - 2) := by
    rw [htv3, show 1 - (3 + P.p) = -P.p - 2 by ring, show 3 + P.p - 1 = 2 + P.p by ring]
    have e1 : y ^ (-P.p - 2) ≤ Y ^ (-P.p - 2) := Real.rpow_le_rpow_of_nonpos hY0 hy.1 (by linarith)
    have e2 : 0 ≤ y ^ (-P.p - 2) := Real.rpow_nonneg hy0.le _
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hI4 : ∫ z in Iio (0 : ℝ), (y - z) ^ (-(4 + P.p)) ≤ Y ^ (-P.p - 3) := by
    rw [htv4, show 1 - (4 + P.p) = -P.p - 3 by ring, show 4 + P.p - 1 = 3 + P.p by ring]
    have e1 : y ^ (-P.p - 3) ≤ Y ^ (-P.p - 3) := Real.rpow_le_rpow_of_nonpos hY0 hy.1 (by linarith)
    have e2 : 0 ≤ y ^ (-P.p - 3) := Real.rpow_nonneg hy0.le _
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hI3n : 0 ≤ ∫ z in Iio (0 : ℝ), (y - z) ^ (-(3 + P.p)) :=
    setIntegral_nonneg measurableSet_Iio (fun z hz => Real.rpow_nonneg (by
      have : z < 0 := hz; linarith) _)
  have hI4n : 0 ≤ ∫ z in Iio (0 : ℝ), (y - z) ^ (-(4 + P.p)) :=
    setIntegral_nonneg measurableSet_Iio (fun z hz => Real.rpow_nonneg (by
      have : z < 0 := hz; linarith) _)
  -- `|f'(y)| ≤ C₀ Y^{-1}`
  have hfy : |deriv f y| ≤ C₀ * Y ^ (-(1 : ℝ)) := by
    have := (h3 y hy1).2 0 (by norm_num)
    simp only [iteratedDeriv_one, Nat.cast_zero, zero_div, add_zero, zero_add] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hC₀0)
    calc y ^ (-beta P.p) ≤ y ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      _ ≤ Y ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_nonpos hY0 hy.1 (by norm_num)
  have hYe : Y ^ (-(1 : ℝ)) * Y ^ (-P.p - 2) = Y ^ (-P.p - 3) := by
    rw [← Real.rpow_add hY0]; ring_nf
  have hY2 : 0 ≤ Y ^ (-P.p - 2) := Real.rpow_nonneg hY0.le _
  have hY3 : 0 ≤ Y ^ (-P.p - 3) := Real.rpow_nonneg hY0.le _
  have hN0 : 0 ≤ N := by positivity
  constructor
  · rw [hEq y hy0, abs_mul]
    have hb : |∫ z in Iio (0 : ℝ), c06_aux_E9I1_H a P.p f y z| ≤
        ∫ z in Iio (0 : ℝ), K * (4 * C₀ ^ 2) * (y - z) ^ (-(3 + P.p)) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (hti3.const_mul _)
        ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
      rw [Real.norm_eq_abs]
      exact (c06_aux_E9I1_bounds a P.p f K C₀ da da' da'' hK2 hK3 hC₀0 hp0.le hg y z hy0 hz).1
    rw [integral_const_mul] at hb
    have hb' : |∫ z in Iio (0 : ℝ), c06_aux_E9I1_H a P.p f y z| ≤
        K * (4 * C₀ ^ 2) * Y ^ (-P.p - 2) :=
      hb.trans (mul_le_mul_of_nonneg_left hI3 (by positivity))
    calc |calpha P.p| * _ ≤ |calpha P.p| * (K * (4 * C₀ ^ 2) * Y ^ (-P.p - 2)) :=
          mul_le_mul_of_nonneg_left hb' hCa
      _ ≤ (|calpha P.p| * CA * (4 * C₀ ^ 2 + N) + 1) * ε * Y ^ (-P.p - 2) := by
          rw [hK]
          have h1 : 0 ≤ |calpha P.p| * CA * N * ε * Y ^ (-P.p - 2) := by positivity
          have h2 : 0 ≤ ε * Y ^ (-P.p - 2) := by positivity
          have e : (|calpha P.p| * CA * (4 * C₀ ^ 2 + N) + 1) * ε * Y ^ (-P.p - 2) =
              |calpha P.p| * (CA * ε * (4 * C₀ ^ 2) * Y ^ (-P.p - 2)) +
                |calpha P.p| * CA * N * ε * Y ^ (-P.p - 2) + ε * Y ^ (-P.p - 2) := by ring
          rw [e]; linarith
  · rw [(hderiv y hyJ).deriv, abs_mul]
    have hb : |∫ z in Iio (0 : ℝ), c06_aux_E9I1_dH a P.p f y z| ≤
        ∫ z in Iio (0 : ℝ), (K * ((8 + 4 * (1 + P.p)) * C₀ ^ 2) * (y - z) ^ (-(4 + P.p)) +
          K * (2 * C₀ * |deriv f y|) * (y - z) ^ (-(3 + P.p))) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hti4.const_mul _).add (hti3.const_mul _))
        ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
      rw [Real.norm_eq_abs]
      refine (c06_aux_E9I1_bounds a P.p f K C₀ da da' da'' hK2 hK3 hC₀0 hp0.le hg y z hy0 hz).2.trans
        (le_of_eq ?_)
      ring
    rw [integral_add (hti4.const_mul _) (hti3.const_mul _), integral_const_mul,
      integral_const_mul] at hb
    have hb' : |∫ z in Iio (0 : ℝ), c06_aux_E9I1_dH a P.p f y z| ≤ K * N * Y ^ (-P.p - 3) := by
      refine hb.trans ?_
      have t1 := mul_le_mul_of_nonneg_left hI4 (by positivity :
        (0 : ℝ) ≤ K * ((8 + 4 * (1 + P.p)) * C₀ ^ 2))
      have t2 : K * (2 * C₀ * |deriv f y|) * ∫ z in Iio (0 : ℝ), (y - z) ^ (-(3 + P.p)) ≤
          K * (2 * C₀ * (C₀ * Y ^ (-(1 : ℝ)))) * Y ^ (-P.p - 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfy (by positivity)) hK0)
          hI3 hI3n (by positivity)
      have e : K * (2 * C₀ * (C₀ * Y ^ (-(1 : ℝ)))) * Y ^ (-P.p - 2) =
          K * (2 * C₀ * C₀) * Y ^ (-P.p - 3) := by rw [← hYe]; ring
      calc _ ≤ K * ((8 + 4 * (1 + P.p)) * C₀ ^ 2) * Y ^ (-P.p - 3) +
            K * (2 * C₀ * C₀) * Y ^ (-P.p - 3) := add_le_add t1 (t2.trans e.le)
        _ = K * N * Y ^ (-P.p - 3) := by rw [hN]; ring
    calc |calpha P.p| * _ ≤ |calpha P.p| * (K * N * Y ^ (-P.p - 3)) :=
          mul_le_mul_of_nonneg_left hb' hCa
      _ ≤ (|calpha P.p| * CA * (4 * C₀ ^ 2 + N) + 1) * ε * Y ^ (-P.p - 3) := by
          rw [hK]
          have h1 : 0 ≤ |calpha P.p| * CA * (4 * C₀ ^ 2) * ε * Y ^ (-P.p - 3) := by positivity
          have h2 : 0 ≤ ε * Y ^ (-P.p - 3) := by positivity
          have e : (|calpha P.p| * CA * (4 * C₀ ^ 2 + N) + 1) * ε * Y ^ (-P.p - 3) =
              |calpha P.p| * (CA * ε * N * Y ^ (-P.p - 3)) +
                |calpha P.p| * CA * (4 * C₀ ^ 2) * ε * Y ^ (-P.p - 3) + ε * Y ^ (-P.p - 3) := by
            ring
          rw [e]; linarith

/-! ### Helpers for c06_E9_I2 -/
/-- Helper (lem:c06_E9_I2): the smooth form of the `ℐ₂` integrand. -/
def c06_aux_E9I2_G (p : ℝ) (A f : ℝ → ℝ) (x z : ℝ) : ℝ :=
  (deriv f x - deriv f z - 1) * (A ((f x - f z) / (x - z)) - A (z / (x - z))) *
    (x - z) ^ (-(1 + p))

/-- Helper (lem:c06_E9_I2): its `x`-derivative. -/
def c06_aux_E9I2_G' (p : ℝ) (A f : ℝ → ℝ) (x z : ℝ) : ℝ :=
  (deriv (deriv f) x * (A ((f x - f z) / (x - z)) - A (z / (x - z))) +
    (deriv f x - deriv f z - 1) * (deriv A ((f x - f z) / (x - z)) *
      (deriv f x - (f x - f z) / (x - z)) + deriv A (z / (x - z)) * (z / (x - z))) / (x - z) -
    (1 + p) * (deriv f x - deriv f z - 1) * (A ((f x - f z) / (x - z)) - A (z / (x - z))) /
      (x - z)) * (x - z) ^ (-(1 + p))

theorem c06_aux_E9I2_hasDeriv (p : ℝ) (A f : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f)) (x z : ℝ) (hxz : z < x) :
    HasDerivAt (fun x => c06_aux_E9I2_G p A f x z) (c06_aux_E9I2_G' p A f x z) x := by
  have hs : 0 < x - z := by linarith
  have hD : HasDerivAt (fun x => deriv f x - deriv f z - 1) (deriv (deriv f) x) x :=
    ((hf2 x).hasDerivAt.sub_const _).sub_const _
  have hSf : HasDerivAt (fun x => (f x - f z) / (x - z))
      ((deriv f x * (x - z) - (f x - f z) * 1) / (x - z) ^ 2) x :=
    ((hf1 x).hasDerivAt.sub_const (f z)).div ((hasDerivAt_id x).sub_const z) hs.ne'
  have hu : HasDerivAt (fun x => z / (x - z)) ((0 * (x - z) - z * 1) / (x - z) ^ 2) x :=
    (hasDerivAt_const x z).div ((hasDerivAt_id x).sub_const z) hs.ne'
  have hDA : HasDerivAt (fun x => A ((f x - f z) / (x - z)) - A (z / (x - z)))
      (deriv A ((f x - f z) / (x - z)) * ((deriv f x * (x - z) - (f x - f z) * 1) / (x - z) ^ 2) -
        deriv A (z / (x - z)) * ((0 * (x - z) - z * 1) / (x - z) ^ 2)) x :=
    ((hA _).hasDerivAt.comp x hSf).sub ((hA _).hasDerivAt.comp x hu)
  have hP : HasDerivAt (fun x' => (x' - z) ^ (-(1 + p))) (1 * (-(1 + p)) * (x - z) ^ (-(1 + p) - 1)) x :=
    ((hasDerivAt_id x).sub_const z).rpow_const (Or.inl hs.ne')
  refine ((hD.mul hDA).mul hP).congr_deriv ?_
  unfold c06_aux_E9I2_G'
  simp only [Pi.mul_apply]
  rw [Real.rpow_sub_one hs.ne']
  generalize A ((f x - f z) / (x - z)) = a1
  generalize A (z / (x - z)) = a2
  generalize deriv A ((f x - f z) / (x - z)) = b1
  generalize deriv A (z / (x - z)) = b2
  field_simp
  ring

/-- Helper (lem:c06_E9_I2): pointwise bounds of the `ℐ₂` integrand and of its `x`-derivative. -/
theorem c06_aux_E9I2_pt (p : ℝ) (hp : 0 < p) (A f : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA' : Differentiable ℝ (deriv A)) (a1 a2 C₀ : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hC₀ : 0 ≤ C₀) (hA1 : ∀ w, |deriv A w| ≤ a1 * |w|) (hA2 : ∀ w, |deriv (deriv A) w| ≤ a2)
    (x z : ℝ) (hx : 1 ≤ x) (hz : z < 0) (hfx : |f x| ≤ C₀) (hfz : |f z + z| ≤ C₀) :
    |c06_aux_E9I2_G p A f x z| ≤ (|deriv f x| + |deriv f z + 1|) *
        (a1 * (1 + 2 * C₀) * (2 * C₀)) * (x - z) ^ (-(2 + p)) ∧
    |c06_aux_E9I2_G' p A f x z| ≤ (|deriv (deriv f) x| * (a1 * (1 + 2 * C₀) * (2 * C₀)) +
        (|deriv f x| + |deriv f z + 1|) * (a1 * (1 + 2 * C₀) * |deriv f x| +
          (a1 * (1 + 2 * C₀) + a2) * (2 * C₀) + (1 + p) * (a1 * (1 + 2 * C₀) * (2 * C₀)))) *
        (x - z) ^ (-(2 + p)) := by
  set s := x - z with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; linarith
  have hs : 0 < s := by linarith
  set K := 1 + 2 * C₀ with hK
  set Sf := (f x - f z) / s with hSf
  set u := z / s with hu
  set d := Sf - u with hd
  have hdnum : d = (f x - (f z + z)) / s := by rw [hd, hSf, hu]; field_simp; ring
  have hnum : |f x - (f z + z)| ≤ 2 * C₀ := by
    have := abs_sub (f x) (f z + z); linarith
  have hd1 : |d| ≤ 2 * C₀ / s := by
    rw [hdnum, abs_div, abs_of_pos hs]; exact div_le_div_of_nonneg_right hnum hs.le
  have hd2 : |d| ≤ 2 * C₀ := le_trans hd1 (div_le_self (by linarith) hs1)
  have hu1 : |u| ≤ 1 := by
    rw [hu, abs_div, abs_of_pos hs, abs_of_neg hz, div_le_one hs, hsdef]; linarith
  have hSfK : |Sf| ≤ K := by
    have : Sf = u + d := by rw [hd]; ring
    rw [this]; have := abs_add_le u d; rw [hK]; linarith
  have huK : |u| ≤ K := by rw [hK]; linarith
  -- mean value bounds
  have hΔ : |A Sf - A u| ≤ a1 * K * |d| := by
    have hbd : ∀ w ∈ Icc (-K) K, ‖deriv A w‖ ≤ a1 * K := fun w hw => by
      rw [Real.norm_eq_abs]
      refine le_trans (hA1 w) (mul_le_mul_of_nonneg_left ?_ ha1)
      exact abs_le.mpr ⟨hw.1, hw.2⟩
    have := (convex_Icc (-K) K).norm_image_sub_le_of_norm_deriv_le (fun w _ => hA w) hbd
      (abs_le.mp huK |> fun h => ⟨h.1, h.2⟩) (abs_le.mp hSfK |> fun h => ⟨h.1, h.2⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    rw [hd]; exact this
  have hΔ' : |deriv A Sf - deriv A u| ≤ a2 * |d| := by
    have := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun w _ => hA' w)
      (fun w _ => by rw [Real.norm_eq_abs]; exact hA2 w) (mem_univ u) (mem_univ Sf)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    rw [hd]; exact this
  set c1 := a1 * K * (2 * C₀) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hΔs : |A Sf - A u| ≤ c1 / s := by
    calc _ ≤ a1 * K * |d| := hΔ
      _ ≤ a1 * K * (2 * C₀ / s) := mul_le_mul_of_nonneg_left hd1 (by positivity)
      _ = _ := by rw [hc1]; ring
  have hD : |deriv f x - deriv f z - 1| ≤ |deriv f x| + |deriv f z + 1| := by
    have := abs_sub (deriv f x) (deriv f z + 1)
    rwa [show deriv f x - (deriv f z + 1) = deriv f x - deriv f z - 1 by ring] at this
  have hP0 : 0 < s ^ (-(1 + p)) := Real.rpow_pos_of_pos hs _
  have hP : s ^ (-(2 + p)) = s ^ (-(1 + p)) / s := by
    rw [show -(2 + p) = -(1 + p) - 1 by ring, Real.rpow_sub_one hs.ne']
  have hDB := add_nonneg (abs_nonneg (deriv f x)) (abs_nonneg (deriv f z + 1))
  constructor
  · unfold c06_aux_E9I2_G
    rw [← hsdef, ← hSf, ← hu, abs_mul, abs_mul, abs_of_pos hP0, hP]
    calc |deriv f x - deriv f z - 1| * |A Sf - A u| * s ^ (-(1 + p))
        ≤ (|deriv f x| + |deriv f z + 1|) * (c1 / s) * s ^ (-(1 + p)) := by gcongr
      _ = _ := by ring
  · unfold c06_aux_E9I2_G'
    rw [← hsdef, ← hSf, ← hu, abs_mul, abs_of_pos hP0, hP]
    set N := deriv A Sf * (deriv f x - Sf) + deriv A u * u with hN
    have hNe : N = deriv A Sf * deriv f x - deriv A Sf * d - (deriv A Sf - deriv A u) * u := by
      rw [hN, hd]; ring
    have hASf : |deriv A Sf| ≤ a1 * K := le_trans (hA1 Sf) (mul_le_mul_of_nonneg_left hSfK ha1)
    set cA := a1 * K * |deriv f x| + (a1 * K + a2) * (2 * C₀) with hcA
    have hNb : |N| ≤ cA := by
      rw [hNe]
      have t1 : |deriv A Sf * deriv f x| ≤ a1 * K * |deriv f x| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hASf (abs_nonneg _)
      have t2 : |deriv A Sf * d| ≤ a1 * K * (2 * C₀) := by
        rw [abs_mul]; exact mul_le_mul hASf hd2 (abs_nonneg _) (by positivity)
      have t3 : |(deriv A Sf - deriv A u) * u| ≤ a2 * (2 * C₀) := by
        rw [abs_mul]
        calc _ ≤ (a2 * |d|) * 1 := mul_le_mul hΔ' hu1 (abs_nonneg _) (by positivity)
          _ ≤ a2 * (2 * C₀) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hd2 ha2
      have := abs_sub (deriv A Sf * deriv f x - deriv A Sf * d) ((deriv A Sf - deriv A u) * u)
      have := abs_sub (deriv A Sf * deriv f x) (deriv A Sf * d)
      rw [hcA]; nlinarith
    have hcA0 : 0 ≤ cA := le_trans (abs_nonneg _) hNb
    set D := deriv f x - deriv f z - 1 with hDdef
    set AB := |deriv f x| + |deriv f z + 1| with hAB
    have e1 : |deriv (deriv f) x * (A Sf - A u)| ≤ |deriv (deriv f) x| * c1 / s := by
      rw [abs_mul, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hΔs (abs_nonneg _)
    have e2 : |D * N / s| ≤ AB * cA / s := by
      rw [abs_div, abs_of_pos hs, abs_mul]
      exact div_le_div_of_nonneg_right (mul_le_mul hD hNb (abs_nonneg _) hDB) hs.le
    have e3 : |(1 + p) * D * (A Sf - A u) / s| ≤ (1 + p) * AB * c1 / s := by
      rw [abs_div, abs_of_pos hs, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + p)]
      refine div_le_div_of_nonneg_right ?_ hs.le
      have h1 : |A Sf - A u| ≤ c1 := le_trans hΔs (div_le_self hc10 hs1)
      have := mul_le_mul hD h1 (abs_nonneg _) hDB
      calc (1 + p) * |D| * |A Sf - A u| = (1 + p) * (|D| * |A Sf - A u|) := by ring
        _ ≤ (1 + p) * (AB * c1) := mul_le_mul_of_nonneg_left this (by linarith)
        _ = _ := by ring
    have hsum := abs_add_le (deriv (deriv f) x * (A Sf - A u)) (D * N / s)
    have hsub := abs_sub (deriv (deriv f) x * (A Sf - A u) + D * N / s)
      ((1 + p) * D * (A Sf - A u) / s)
    have htot : |deriv (deriv f) x * (A Sf - A u) + D * N / s - (1 + p) * D * (A Sf - A u) / s| ≤
        (|deriv (deriv f) x| * c1 + AB * (cA + (1 + p) * c1)) / s := by
      have : (|deriv (deriv f) x| * c1 + AB * (cA + (1 + p) * c1)) / s =
          |deriv (deriv f) x| * c1 / s + AB * cA / s + (1 + p) * AB * c1 / s := by ring
      rw [this]; linarith
    calc _ ≤ (|deriv (deriv f) x| * c1 + AB * (cA + (1 + p) * c1)) / s * s ^ (-(1 + p)) :=
          mul_le_mul_of_nonneg_right htot hP0.le
      _ = _ := by ring

/-- Helper (lem:c06_E9_I2): `∫_{-∞}^0 H` for `|H(z)| ≤ (α + β ⟨z⟩^{-1-p}) (y-z)^{-2-p}`. -/
theorem c06_aux_E9I2_intbound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (H : ℝ → ℝ) (α β y : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hy : 0 < y)
    (hH : AEStronglyMeasurable H (volume.restrict (Iio 0)))
    (hb : ∀ z, z < 0 → |H z| ≤ (α + β * jb z ^ (-1 - p)) * (y - z) ^ (-(2 + p))) :
    |∫ z in Iio (0 : ℝ), H z| ≤ α * y ^ (-1 - p) + β * (1 + 1 / p) * y ^ (-(2 + p)) := by
  obtain ⟨i1, -, i3, -⟩ := c06_tail_integrals p hp hp1
  obtain ⟨hi1, hv1⟩ := i1 (2 + p) y (by linarith) hy
  obtain ⟨hi3, hv3⟩ := i3 (2 + p) y (by linarith) hy
  have hg : IntegrableOn (fun z => α * (y - z) ^ (-(2 + p)) +
      β * (jb z ^ (-1 - p) * (y - z) ^ (-(2 + p)))) (Iio 0) :=
    (hi1.const_mul α).add (hi3.const_mul β)
  have := norm_integral_le_of_norm_le hg ((ae_restrict_iff' measurableSet_Iio).mpr
    (ae_of_all _ fun z hz => by
      rw [Real.norm_eq_abs]
      refine le_trans (hb z hz) (le_of_eq (by ring))))
  rw [Real.norm_eq_abs, integral_add (hi1.const_mul α) (hi3.const_mul β), integral_const_mul,
    integral_const_mul, hv1] at this
  refine le_trans this ?_
  have e : y ^ (1 - (2 + p)) / (2 + p - 1) ≤ y ^ (-1 - p) := by
    rw [show 1 - (2 + p) = -1 - p by ring, div_le_iff₀ (by linarith)]
    have := Real.rpow_nonneg hy.le (-1 - p)
    nlinarith
  have := mul_le_mul_of_nonneg_left e hα
  have := mul_le_mul_of_nonneg_left hv3 hβ
  nlinarith

/-- Helper (lem:c06_E9_I2): differentiation of `∫_{-∞}^0 G` under the integral sign. -/
theorem c06_aux_E9I2_hasDeriv_int (p : ℝ) (hp : 0 < p) (A f : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA' : Differentiable ℝ (deriv A)) (a1 a2 C₀ : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hC₀ : 0 ≤ C₀) (hA1 : ∀ w, |deriv A w| ≤ a1 * |w|) (hA2 : ∀ w, |deriv (deriv A) w| ≤ a2)
    (df : Differentiable ℝ f) (ddf : Differentiable ℝ (deriv f)) (Y : ℝ) (hY : 8 ≤ Y)
    (b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀) (b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀)
    (b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y))
    (bn : ∀ z, z < 0 → |f z + z| ≤ C₀ ∧ |deriv f z + 1| ≤ C₀)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2)) :
    HasDerivAt (fun y => ∫ z in Iio (0 : ℝ), c06_aux_E9I2_G p A f y z)
      (∫ z in Iio (0 : ℝ), c06_aux_E9I2_G' p A f y₀ z) y₀ := by
  have mA : Measurable A := hA.continuous.measurable
  have mdA : Measurable (deriv A) := measurable_deriv _
  have mf : Measurable f := df.continuous.measurable
  have mdf : Measurable (deriv f) := measurable_deriv _
  have mddf : Measurable (deriv (deriv f)) := measurable_deriv _
  have mG : ∀ x, AEStronglyMeasurable (c06_aux_E9I2_G p A f x) (volume.restrict (Iio 0)) :=
    fun x => by
      refine Measurable.aestronglyMeasurable ?_
      unfold c06_aux_E9I2_G
      fun_prop
  have mG' : ∀ x, AEStronglyMeasurable (c06_aux_E9I2_G' p A f x) (volume.restrict (Iio 0)) :=
    fun x => by
      refine Measurable.aestronglyMeasurable ?_
      unfold c06_aux_E9I2_G'
      fun_prop
  set K := 1 + 2 * C₀ with hK
  set c1 := a1 * K * (2 * C₀) with hc1
  set M : ℝ := C₀ * (3 * Y) * c1 + (C₀ + C₀) * (a1 * K * C₀ + (a1 * K + a2) * (2 * C₀) +
    (1 + p) * c1) with hM
  set x₁ := 5 * Y / 8 with hx₁
  have hx₁1 : 1 ≤ x₁ := by rw [hx₁]; linarith
  have hball : ∀ x ∈ Metric.ball y₀ (Y / 8), x₁ ≤ x ∧ x ≤ 3 * Y := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith [hy₀.1, hy₀.2]
  have hc10 : 0 ≤ c1 := by positivity
  have hbd : ∀ x ∈ Metric.ball y₀ (Y / 8), ∀ z, z < 0 →
      |c06_aux_E9I2_G' p A f x z| ≤ M * (x₁ - z) ^ (-(2 + p)) := by
    intro x hx z hz
    obtain ⟨hx1, hx2⟩ := hball x hx
    have hx1' : 1 ≤ x := le_trans hx₁1 hx1
    obtain ⟨-, hpt⟩ := c06_aux_E9I2_pt p hp A f hA hA' a1 a2 C₀ ha1 ha2 hC₀ hA1 hA2 x z hx1' hz
      (b0 x hx1') (bn z hz).1
    refine le_trans hpt ?_
    have e1 := b1 x hx1'
    have e2 := b2 x hx1' hx2
    have e3 := (bn z hz).2
    have hs : 0 < x₁ - z := by linarith
    have hmono : (x - z) ^ (-(2 + p)) ≤ (x₁ - z) ^ (-(2 + p)) :=
      Real.rpow_le_rpow_of_nonpos hs (by linarith) (by linarith)
    have hcoef : |deriv (deriv f) x| * c1 + (|deriv f x| + |deriv f z + 1|) *
        (a1 * K * |deriv f x| + (a1 * K + a2) * (2 * C₀) + (1 + p) * c1) ≤ M := by
      rw [hM]
      have h1 : |deriv (deriv f) x| * c1 ≤ C₀ * (3 * Y) * c1 := mul_le_mul_of_nonneg_right e2 hc10
      have h2 : a1 * K * |deriv f x| ≤ a1 * K * C₀ := mul_le_mul_of_nonneg_left e1 (by positivity)
      have h3 : 0 ≤ a1 * K * |deriv f x| + (a1 * K + a2) * (2 * C₀) + (1 + p) * c1 := by
        positivity
      have h4 := mul_le_mul (add_le_add e1 e3) (by linarith : a1 * K * |deriv f x| +
        (a1 * K + a2) * (2 * C₀) + (1 + p) * c1 ≤ a1 * K * C₀ + (a1 * K + a2) * (2 * C₀) +
        (1 + p) * c1) h3 (by positivity)
      linarith
    have h0 : 0 ≤ |deriv (deriv f) x| * c1 + (|deriv f x| + |deriv f z + 1|) *
        (a1 * K * |deriv f x| + (a1 * K + a2) * (2 * C₀) + (1 + p) * c1) := by positivity
    exact mul_le_mul hcoef hmono (Real.rpow_nonneg (by linarith) _) (le_trans h0 hcoef)
  have hy₀1 : 1 ≤ y₀ := by linarith [hy₀.1]
  have hintG : Integrable (c06_aux_E9I2_G p A f y₀) (volume.restrict (Iio 0)) := by
    refine Integrable.mono' (((c06_aux_tail1 (2 + p) y₀ (by linarith) (by linarith)).1).const_mul
      ((C₀ + C₀) * c1)) (mG y₀) ?_
    refine (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_)
    rw [Real.norm_eq_abs]
    obtain ⟨hpt, -⟩ := c06_aux_E9I2_pt p hp A f hA hA' a1 a2 C₀ ha1 ha2 hC₀ hA1 hA2 y₀ z hy₀1 hz
      (b0 y₀ hy₀1) (bn z hz).1
    refine le_trans hpt ?_
    have := add_le_add (b1 y₀ hy₀1) (bn z hz).2
    have hs : 0 ≤ (y₀ - z) ^ (-(2 + p)) := Real.rpow_nonneg (by linarith [show z < 0 from hz]) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hc10) hs
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Iio 0))
    (F := c06_aux_E9I2_G p A f) (F' := c06_aux_E9I2_G' p A f) (x₀ := y₀)
    (bound := fun z => M * (x₁ - z) ^ (-(2 + p)))
    (s := Metric.ball y₀ (Y / 8)) (Metric.ball_mem_nhds _ (by linarith))
    (Eventually.of_forall mG) hintG (mG' y₀)
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz x hx => by
      rw [Real.norm_eq_abs]; exact hbd x hx z hz))
    (((c06_aux_tail1 (2 + p) x₁ (by linarith) (by linarith)).1).const_mul _)
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz x hx =>
      c06_aux_E9I2_hasDeriv p A f hA df ddf x z (by
        have := (hball x hx).1; have : z < 0 := hz; linarith)))
  exact H.2

/-- Helper (lem:c06_E9_I2): power comparisons on `[Y,∞)`. -/
theorem c06_aux_E9I2_pow (p b Y y : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hb : 1 ≤ b)
    (hY : 1 ≤ Y) (hy : Y ≤ y) :
    y ^ (-b) * y ^ (-1 - p) ≤ Y ^ (-p - 2) ∧
    y ^ (-b + 1 / p) * y ^ (-1 - p) ≤ Y ^ (-p - 2 + 1 / p) ∧
    y ^ (-(2 + p)) ≤ Y ^ (-p - 2) ∧
    Y ^ (-p - 2) ≤ Y ^ (-p - 2 + 1 / p) := by
  have hp0 : 0 < p := by linarith
  have hy1 : 1 ≤ y := le_trans hY hy
  have hy0 : 0 < y := by linarith
  have hY0 : 0 < Y := by linarith
  have hinv : 1 / p < 4 / 3 := by rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith
  have hinv0 : 0 < 1 / p := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_add hy0]
    calc y ^ (-b + (-1 - p)) ≤ y ^ (-p - 2) := Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      _ ≤ Y ^ (-p - 2) := Real.rpow_le_rpow_of_nonpos hY0 hy (by linarith)
  · rw [← Real.rpow_add hy0]
    calc y ^ (-b + 1 / p + (-1 - p)) ≤ y ^ (-p - 2 + 1 / p) :=
          Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      _ ≤ Y ^ (-p - 2 + 1 / p) := Real.rpow_le_rpow_of_nonpos hY0 hy (by linarith)
  · rw [show -(2 + p) = -p - 2 by ring]
    exact Real.rpow_le_rpow_of_nonpos hY0 hy (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)

set_option maxHeartbeats 800000 in
-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E9_I2.  `ℐ₂` is differentiable on `J_Y` and
`|∂^j ℐ₂| ≤ C ε Y^{-p-2+j/p}` on `[Y,2Y]`. -/
theorem c06_E9_I2 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let E : ℝ → ℝ := c06_E9_split_I2 P.p ε (approximate_solution_family P.p R ε μ)
        DifferentiableOn ℝ E (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j E y| ≤ C * ε * Y ^ (-P.p - 2 + j / P.p) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hplo := P.hp_lo
  have hb1 : 1 ≤ beta P.p := by
    unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, hCA, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  set k1 : ℝ := (P.p + 1) * (1 + 2 * C₀) * (2 * C₀) with hk1
  set kA : ℝ := (P.p + 1) * (1 + 2 * C₀) * C₀ + ((P.p + 1) * (1 + 2 * C₀) + CA) * (2 * C₀)
    with hkA
  set q : ℝ := kA + (1 + P.p) * k1 with hq
  have hk10 : 0 ≤ k1 := by positivity
  have hq0 : 0 ≤ q := by positivity
  set C0t : ℝ := k1 * C₀ + k1 * C₀ * (1 + 1 / P.p) with hC0t
  set C1t : ℝ := k1 * C₀ + C₀ * q + C₀ * q * (1 + 1 / P.p) with hC1t
  have hC0t0 : 0 ≤ C0t := by positivity
  have hC1t0 : 0 ≤ C1t := by positivity
  refine ⟨|calpha P.p| * (C0t + C1t) + 1, by positivity, ?_⟩
  intro Y hY ε hε μ hμ E
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, h1, -, h2n, h3⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  set A := A_eps P.p ε with hAdef
  have hA1 : ∀ w, |deriv A w| ≤ ((P.p + 1) * ε) * |w| := fun w => (hAb w).2.1
  have hA2 : ∀ w, |deriv (deriv A) w| ≤ CA * ε := fun w => by
    have := (hAb w).2.2.1
    have e : iteratedDeriv 2 A w = deriv (deriv A) w := by
      simp [iteratedDeriv_succ]
    rw [e] at this; linarith [abs_nonneg (iteratedDeriv 3 A w)]
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have dA : Differentiable ℝ A := hAc.differentiable (by simp)
  have ddA : Differentiable ℝ (deriv A) := by
    simpa using hAc.differentiable_iteratedDeriv 1 htop1
  set f := approximate_solution_family P.p R ε μ with hf
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have ddf : Differentiable ℝ (deriv f) := by
    simpa using hfs.differentiable_iteratedDeriv 1 htop1
  have bf0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ * x ^ (-P.p) := fun x hx => (h3 x hx).1
  have bf1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ * x ^ (-beta P.p) := fun x hx => by
    simpa using (h3 x hx).2 0 (by norm_num)
  have bf2 : ∀ x, 1 ≤ x → |deriv (deriv f) x| ≤ C₀ * x ^ (-beta P.p + 1 / P.p) := fun x hx => by
    have := (h3 x hx).2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ := fun x hx => le_trans (bf0 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)))
  have b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ := fun x hx => le_trans (bf1 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)))
  have b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y) := fun x hx hx3 => by
    refine le_trans (bf2 x hx) (mul_le_mul_of_nonneg_left ?_ hC₀0)
    have hinv : 1 / P.p < 4 / 3 := by rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith
    have : x ^ (-beta P.p + 1 / P.p) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    rw [Real.rpow_one] at this; linarith
  have bnw : ∀ z, z < 0 → |deriv f z + 1| ≤ C₀ * jb z ^ (-1 - P.p) := fun z hz => by
    have := h2n z hz.le
    rwa [show -P.p - 1 = -1 - P.p by ring] at this
  have bn : ∀ z, z < 0 → |f z + z| ≤ C₀ ∧ |deriv f z + 1| ≤ C₀ := fun z hz => by
    constructor
    · have h := (h1 z).2
      have hc : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
      rw [hc, sub_neg_eq_add] at h
      exact le_trans h (mul_le_of_le_one_right hC₀0 (c06_aux_jb_rpow_neg_le_one z P.p hp0.le))
    · refine le_trans (bnw z hz) (mul_le_of_le_one_right hC₀0 ?_)
      have := c06_aux_jb_rpow_neg_le_one z (1 + P.p) (by linarith)
      rwa [show -(1 + P.p) = -1 - P.p by ring] at this
  -- the integrand in smooth form
  have hEeq : ∀ y, 0 < y → E y = calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I2_G P.p A f y z := by
    intro y hy
    show calpha P.p * _ = _
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio (fun z hz => ?_)
    have hz0 : z < 0 := hz
    have hne : y ≠ z := by intro e; linarith
    have hyz : 0 < y - z := by linarith
    have hcy : corner y = 0 := by simp only [corner]; exact max_eq_right (by linarith)
    have hcz : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
    simp only [c06_aux_E9I2_G, c01_secant, if_neg hne, hcy, hcz, zero_sub, neg_neg]
    rw [Real.rpow_neg hyz.le, div_eq_mul_inv]
  have hderiv : ∀ y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2), HasDerivAt E
      (calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I2_G' P.p A f y₀ z) y₀ := by
    intro y₀ hy₀
    have hy0 : 0 < y₀ := by linarith [hy₀.1]
    refine ((c06_aux_E9I2_hasDeriv_int P.p hp0 A f dA ddA ((P.p + 1) * ε) (CA * ε) C₀
      (by positivity) (by positivity) hC₀0 hA1 hA2 df ddf Y hY8 b0 b1 b2 bn y₀ hy₀).const_mul
      (calpha P.p)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy0] with x hx
    exact hEeq x hx
  refine ⟨fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt, ?_⟩
  intro y hy j hj
  have hyJ : y ∈ Ioo (3 * Y / 4) (5 * Y / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  obtain ⟨pw1, pw2, pw3, pw4⟩ := c06_aux_E9I2_pow P.p (beta P.p) Y y hplo hp1 hb1 hY1 hy.1
  have hCa := abs_nonneg (calpha P.p)
  have hfy1 := bf1 y hy1
  have hfy2 := bf2 y hy1
  have hfy1' := b1 y hy1
  set c1 : ℝ := (P.p + 1) * ε * (1 + 2 * C₀) * (2 * C₀) with hc1
  have hc1e : c1 = ε * k1 := by rw [hc1, hk1]; ring
  have hc10 : 0 ≤ c1 := by rw [hc1e]; positivity
  have hyb0 : 0 ≤ y ^ (-beta P.p) := Real.rpow_nonneg hy0.le _
  have hyp0 : 0 ≤ y ^ (-1 - P.p) := Real.rpow_nonneg hy0.le _
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
    rw [hEeq y hy0, abs_mul]
    have hI := c06_aux_E9I2_intbound P.p hp0 hp1 (c06_aux_E9I2_G P.p A f y) (c1 * |deriv f y|)
      (c1 * C₀) y (by positivity) (by positivity) hy0
      ((c06_aux_E9I2_hasDeriv_int P.p hp0 A f dA ddA ((P.p + 1) * ε) (CA * ε) C₀
        (by positivity) (by positivity) hC₀0 hA1 hA2 df ddf Y hY8 b0 b1 b2 bn y hyJ) |> fun _ =>
        (by
          refine Measurable.aestronglyMeasurable ?_
          have mA : Measurable A := dA.continuous.measurable
          have mf : Measurable f := df.continuous.measurable
          have mdf : Measurable (deriv f) := measurable_deriv _
          unfold c06_aux_E9I2_G
          fun_prop))
      (fun z hz => by
        obtain ⟨hpt, -⟩ := c06_aux_E9I2_pt P.p hp0 A f dA ddA ((P.p + 1) * ε) (CA * ε) C₀
          (by positivity) (by positivity) hC₀0 hA1 hA2 y z hy1 hz (b0 y hy1) (bn z hz).1
        refine le_trans hpt (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _))
        have hb := mul_le_mul_of_nonneg_left (bnw z hz) hc10
        calc (|deriv f y| + |deriv f z + 1|) * ((P.p + 1) * ε * (1 + 2 * C₀) * (2 * C₀))
            = c1 * |deriv f y| + c1 * |deriv f z + 1| := by rw [hc1]; ring
          _ ≤ c1 * |deriv f y| + c1 * (C₀ * jb z ^ (-1 - P.p)) := by linarith
          _ = _ := by ring)
    have t1 : c1 * |deriv f y| * y ^ (-1 - P.p) ≤ ε * (k1 * C₀) * Y ^ (-P.p - 2) := by
      have := mul_le_mul_of_nonneg_right hfy1 hyp0
      calc c1 * |deriv f y| * y ^ (-1 - P.p) = c1 * (|deriv f y| * y ^ (-1 - P.p)) := by ring
        _ ≤ c1 * (C₀ * y ^ (-beta P.p) * y ^ (-1 - P.p)) := mul_le_mul_of_nonneg_left this hc10
        _ = ε * (k1 * C₀) * (y ^ (-beta P.p) * y ^ (-1 - P.p)) := by rw [hc1e]; ring
        _ ≤ ε * (k1 * C₀) * Y ^ (-P.p - 2) := mul_le_mul_of_nonneg_left pw1 (by positivity)
    have t2 : c1 * C₀ * (1 + 1 / P.p) * y ^ (-(2 + P.p)) ≤
        ε * (k1 * C₀ * (1 + 1 / P.p)) * Y ^ (-P.p - 2) := by
      rw [hc1e]
      have : 0 ≤ ε * (k1 * C₀ * (1 + 1 / P.p)) := by positivity
      have := mul_le_mul_of_nonneg_left pw3 this
      linarith [show ε * k1 * C₀ * (1 + 1 / P.p) * y ^ (-(2 + P.p)) =
        ε * (k1 * C₀ * (1 + 1 / P.p)) * y ^ (-(2 + P.p)) by ring]
    have hYp : 0 ≤ Y ^ (-P.p - 2) := Real.rpow_nonneg hY0.le _
    calc |calpha P.p| * |∫ z in Iio (0 : ℝ), c06_aux_E9I2_G P.p A f y z|
        ≤ |calpha P.p| * (ε * C0t * Y ^ (-P.p - 2)) := by
          refine mul_le_mul_of_nonneg_left (le_trans hI ?_) hCa
          rw [hC0t]; linarith
      _ ≤ (|calpha P.p| * (C0t + C1t) + 1) * ε * Y ^ (-P.p - 2) := by
          have : 0 ≤ ε * Y ^ (-P.p - 2) := by positivity
          have : 0 ≤ |calpha P.p| * C1t * (ε * Y ^ (-P.p - 2)) := by positivity
          linarith
  · simp only [iteratedDeriv_one, Nat.cast_one]
    rw [(hderiv y hyJ).deriv, abs_mul]
    set Q : ℝ := (P.p + 1) * ε * (1 + 2 * C₀) * |deriv f y| +
      ((P.p + 1) * ε * (1 + 2 * C₀) + CA * ε) * (2 * C₀) + (1 + P.p) * c1 with hQ
    have hQq : Q ≤ ε * q := by
      rw [hQ, hq, hkA, hc1e, hk1]
      have := mul_le_mul_of_nonneg_left hfy1' (by positivity : (0 : ℝ) ≤ (P.p + 1) * ε * (1 + 2 * C₀))
      linarith
    have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
    have hI := c06_aux_E9I2_intbound P.p hp0 hp1 (c06_aux_E9I2_G' P.p A f y)
      (|deriv (deriv f) y| * c1 + |deriv f y| * Q) (C₀ * Q) y (by positivity) (by positivity) hy0
      (by
          refine Measurable.aestronglyMeasurable ?_
          have mA : Measurable A := dA.continuous.measurable
          have mdA : Measurable (deriv A) := measurable_deriv _
          have mf : Measurable f := df.continuous.measurable
          have mdf : Measurable (deriv f) := measurable_deriv _
          have mddf : Measurable (deriv (deriv f)) := measurable_deriv _
          unfold c06_aux_E9I2_G'
          fun_prop)
      (fun z hz => by
        obtain ⟨-, hpt⟩ := c06_aux_E9I2_pt P.p hp0 A f dA ddA ((P.p + 1) * ε) (CA * ε) C₀
          (by positivity) (by positivity) hC₀0 hA1 hA2 y z hy1 hz (b0 y hy1) (bn z hz).1
        refine le_trans hpt (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _))
        have hb := mul_le_mul_of_nonneg_left (bnw z hz) hQ0
        calc |deriv (deriv f) y| * ((P.p + 1) * ε * (1 + 2 * C₀) * (2 * C₀)) +
              (|deriv f y| + |deriv f z + 1|) * ((P.p + 1) * ε * (1 + 2 * C₀) * |deriv f y| +
                ((P.p + 1) * ε * (1 + 2 * C₀) + CA * ε) * (2 * C₀) +
                (1 + P.p) * ((P.p + 1) * ε * (1 + 2 * C₀) * (2 * C₀)))
            = |deriv (deriv f) y| * c1 + |deriv f y| * Q + Q * |deriv f z + 1| := by
              rw [hQ, hc1]; ring
          _ ≤ |deriv (deriv f) y| * c1 + |deriv f y| * Q + Q * (C₀ * jb z ^ (-1 - P.p)) := by
              linarith
          _ = _ := by ring)
    have t1 : (|deriv (deriv f) y| * c1 + |deriv f y| * Q) * y ^ (-1 - P.p) ≤
        ε * (k1 * C₀ + C₀ * q) * Y ^ (-P.p - 2 + 1 / P.p) := by
      have a1 : |deriv (deriv f) y| * c1 * y ^ (-1 - P.p) ≤
          ε * (k1 * C₀) * Y ^ (-P.p - 2 + 1 / P.p) := by
        have := mul_le_mul_of_nonneg_right hfy2 hyp0
        calc |deriv (deriv f) y| * c1 * y ^ (-1 - P.p) =
              c1 * (|deriv (deriv f) y| * y ^ (-1 - P.p)) := by ring
          _ ≤ c1 * (C₀ * y ^ (-beta P.p + 1 / P.p) * y ^ (-1 - P.p)) :=
              mul_le_mul_of_nonneg_left this hc10
          _ = ε * (k1 * C₀) * (y ^ (-beta P.p + 1 / P.p) * y ^ (-1 - P.p)) := by rw [hc1e]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left pw2 (by positivity)
      have a2 : |deriv f y| * Q * y ^ (-1 - P.p) ≤ ε * (C₀ * q) * Y ^ (-P.p - 2 + 1 / P.p) := by
        have := mul_le_mul_of_nonneg_right hfy1 hyp0
        calc |deriv f y| * Q * y ^ (-1 - P.p) = Q * (|deriv f y| * y ^ (-1 - P.p)) := by ring
          _ ≤ (ε * q) * (C₀ * y ^ (-beta P.p) * y ^ (-1 - P.p)) :=
              mul_le_mul hQq this (by positivity) (by positivity)
          _ = ε * (C₀ * q) * (y ^ (-beta P.p) * y ^ (-1 - P.p)) := by ring
          _ ≤ ε * (C₀ * q) * Y ^ (-P.p - 2) := mul_le_mul_of_nonneg_left pw1 (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left pw4 (by positivity)
      linarith
    have t2 : C₀ * Q * (1 + 1 / P.p) * y ^ (-(2 + P.p)) ≤
        ε * (C₀ * q * (1 + 1 / P.p)) * Y ^ (-P.p - 2 + 1 / P.p) := by
      have h1 : C₀ * Q * (1 + 1 / P.p) ≤ ε * (C₀ * q * (1 + 1 / P.p)) := by
        have := mul_le_mul_of_nonneg_left hQq (by positivity : (0 : ℝ) ≤ C₀ * (1 + 1 / P.p))
        linarith
      exact mul_le_mul h1 (le_trans pw3 pw4) (Real.rpow_nonneg (by linarith) _) (by positivity)
    have hYp : 0 ≤ Y ^ (-P.p - 2 + 1 / P.p) := Real.rpow_nonneg hY0.le _
    calc |calpha P.p| * |∫ z in Iio (0 : ℝ), c06_aux_E9I2_G' P.p A f y z|
        ≤ |calpha P.p| * (ε * C1t * Y ^ (-P.p - 2 + 1 / P.p)) := by
          refine mul_le_mul_of_nonneg_left (le_trans hI ?_) hCa
          rw [hC1t]; linarith
      _ ≤ (|calpha P.p| * (C0t + C1t) + 1) * ε * Y ^ (-P.p - 2 + 1 / P.p) := by
          have : 0 ≤ ε * Y ^ (-P.p - 2 + 1 / P.p) := by positivity
          have : 0 ≤ |calpha P.p| * C0t * (ε * Y ^ (-P.p - 2 + 1 / P.p)) := by positivity
          linarith

/-- Helper (algebra for lem:c06_E9_I3): bound of the `y`-derivative of the `ℐ₃` integrand. -/
theorem c06_aux_I3_alg (c ε q F0 F1 F2 D Am Ad : ℝ) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1)
    (hAm : |Am| ≤ c * ε * (F0 * D) ^ 2) (hAd : |Ad| ≤ 2 * c * ε * |F0 * D|) :
    |F2 * Am - q * F1 * D * Am + F1 * Ad * (F1 * D - F0 * D ^ 2)| ≤
      ε * D ^ 2 * (c * F0 ^ 2 * |F2| + q * c * |F1| * F0 ^ 2 + 2 * c * |F1| ^ 2 * |F0| +
        2 * c * |F1| * F0 ^ 2) := by
  have hD2 : D ^ 2 ≤ D := by nlinarith
  have hAm' : |Am| ≤ c * ε * F0 ^ 2 * D ^ 2 := by rw [mul_pow] at hAm; linarith
  have hAd' : |Ad| ≤ 2 * c * ε * |F0| * D := by
    rw [abs_mul, abs_of_nonneg hD0] at hAd; linarith
  have t1 : |F2 * Am| ≤ |F2| * (c * ε * F0 ^ 2 * D ^ 2) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hAm' (abs_nonneg _)
  have t2 : |q * F1 * D * Am| ≤ q * |F1| * D * (c * ε * F0 ^ 2 * D ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_left hAm' (by positivity)
  have t3 : |F1 * D - F0 * D ^ 2| ≤ |F1| * D + |F0| * D ^ 2 := by
    have := abs_sub (F1 * D) (F0 * D ^ 2)
    rw [abs_mul, abs_mul, abs_of_nonneg hD0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ D ^ 2)]
      at this
    exact this
  have t4 : |F1 * Ad * (F1 * D - F0 * D ^ 2)| ≤
      |F1| * (2 * c * ε * |F0| * D) * (|F1| * D + |F0| * D ^ 2) := by
    rw [abs_mul, abs_mul]
    apply mul_le_mul (mul_le_mul_of_nonneg_left hAd' (abs_nonneg _)) t3 (abs_nonneg _)
    positivity
  have := abs_add_le (F2 * Am - q * F1 * D * Am) (F1 * Ad * (F1 * D - F0 * D ^ 2))
  have := abs_sub (F2 * Am) (q * F1 * D * Am)
  -- compare with the target using `D ≤ 1`
  have k1 : q * |F1| * D * (c * ε * F0 ^ 2 * D ^ 2) ≤ ε * D ^ 2 * (q * c * |F1| * F0 ^ 2) := by
    have : 0 ≤ q * |F1| * (c * ε * F0 ^ 2 * D ^ 2) := by positivity
    nlinarith
  have k2 : |F1| * (2 * c * ε * |F0| * D) * (|F1| * D + |F0| * D ^ 2) ≤
      ε * D ^ 2 * (2 * c * |F1| ^ 2 * |F0| + 2 * c * |F1| * F0 ^ 2) := by
    have e : |F1| * (2 * c * ε * |F0| * D) * (|F1| * D + |F0| * D ^ 2) =
        ε * D ^ 2 * (2 * c * |F1| ^ 2 * |F0|) + ε * D ^ 2 * (2 * c * |F1| * |F0| ^ 2) * D := by
      ring
    rw [e]
    simp only [sq_abs]
    have h0 : 0 ≤ ε * D ^ 2 * (2 * c * |F1| * F0 ^ 2) := by positivity
    have := mul_le_of_le_one_right h0 hD1
    nlinarith
  have k0 : |F2| * (c * ε * F0 ^ 2 * D ^ 2) = ε * D ^ 2 * (c * F0 ^ 2 * |F2|) := by ring
  nlinarith

/-- Helper: `y`-derivative of the `ℐ₃` integrand. -/
theorem c06_aux_I3_hasDeriv (p ε : ℝ) (f : ℝ → ℝ) (hf1 : Differentiable ℝ f)
    (hf2 : Differentiable ℝ (deriv f)) (hA : Differentiable ℝ (A_eps p ε)) (x z : ℝ)
    (hxz : z < x) :
    HasDerivAt (fun x => deriv f x / (x - z) ^ (1 + p) * (A_eps p ε (f x / (x - z)) - 1))
      ((deriv (deriv f) x * (A_eps p ε (f x / (x - z)) - 1) -
          (1 + p) * deriv f x * (1 / (x - z)) * (A_eps p ε (f x / (x - z)) - 1) +
          deriv f x * deriv (A_eps p ε) (f x / (x - z)) *
            (deriv f x * (1 / (x - z)) - f x * (1 / (x - z)) ^ 2)) * (x - z) ^ (-(1 + p))) x := by
  have hs : 0 < x - z := by linarith
  have h1 := (hf2 x).hasDerivAt
  have h2 : HasDerivAt (fun x' => (x' - z) ^ (-(1 + p))) (1 * (-(1 + p)) * (x - z) ^ (-(1 + p) - 1)) x :=
    ((hasDerivAt_id x).sub_const z).rpow_const (Or.inl hs.ne')
  have h3 : HasDerivAt (fun x' => f x' / (x' - z)) ((deriv f x * (x - z) - f x * 1) / (x - z) ^ 2) x :=
    (hf1 x).hasDerivAt.div ((hasDerivAt_id x).sub_const z) hs.ne'
  have h4 : HasDerivAt (fun x' => A_eps p ε (f x' / (x' - z)) - 1)
      (deriv (A_eps p ε) (f x / (x - z)) * ((deriv f x * (x - z) - f x * 1) / (x - z) ^ 2)) x :=
    ((hA _).hasDerivAt.comp x h3).sub_const 1
  have hg := (h1.mul h2).mul h4
  have hev : (fun x => deriv f x / (x - z) ^ (1 + p) * (A_eps p ε (f x / (x - z)) - 1)) =ᶠ[nhds x]
      (fun x' => deriv f x' * (x' - z) ^ (-(1 + p)) * (A_eps p ε (f x' / (x' - z)) - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi z from hxz)] with x' hx'
    have : 0 < x' - z := by have : z < x' := hx'; linarith
    rw [Real.rpow_neg this.le, div_eq_mul_inv]
  refine (hg.congr_deriv ?_).congr_of_eventuallyEq hev
  simp only [Pi.mul_apply]
  rw [Real.rpow_sub_one hs.ne']
  field_simp
  ring

/-- Helper: pointwise bound of the `ℐ₃` integrand. -/
theorem c06_aux_I3_bG (p ε c : ℝ) (hc : c = (p + 1) / 2) (f : ℝ → ℝ)
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (x z : ℝ) (hx : 1 ≤ x) (hz : z < 0) :
    |deriv f x / (x - z) ^ (1 + p) * (A_eps p ε (f x / (x - z)) - 1)| ≤
      c * ε * (|deriv f x| * f x ^ 2) * (x - z) ^ (-(3 + p)) := by
  have hs : 0 < x - z := by linarith
  obtain ⟨h0, h1⟩ := hAb1 (f x / (x - z))
  rw [abs_mul, abs_div, abs_of_pos (Real.rpow_pos_of_pos hs _), abs_sub_comm, abs_of_nonneg h0,
    ← c06_aux_rpow3 p (x - z) hs, Real.rpow_neg hs.le]
  have : (f x / (x - z)) ^ 2 = f x ^ 2 * (1 / (x - z)) ^ 2 := by ring
  rw [this] at h1
  have hS := Real.rpow_pos_of_pos hs (1 + p)
  calc |deriv f x| / (x - z) ^ (1 + p) * (1 - A_eps p ε (f x / (x - z)))
      ≤ |deriv f x| / (x - z) ^ (1 + p) * ((p + 1) / 2 * ε * (f x ^ 2 * (1 / (x - z)) ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by rw [hc]; field_simp

/-- Helper: pointwise bound of the `y`-derivative of the `ℐ₃` integrand. -/
theorem c06_aux_I3_bG' (p ε c : ℝ) (hc : c = (p + 1) / 2) (hp : 0 < p) (hε0 : 0 ≤ ε)
    (f : ℝ → ℝ)
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (hAb2 : ∀ w, |deriv (A_eps p ε) w| ≤ (p + 1) * ε * |w|)
    (x z : ℝ) (hx : 1 ≤ x) (hz : z < 0) :
    |(deriv (deriv f) x * (A_eps p ε (f x / (x - z)) - 1) -
      (1 + p) * deriv f x * (1 / (x - z)) * (A_eps p ε (f x / (x - z)) - 1) +
      deriv f x * deriv (A_eps p ε) (f x / (x - z)) *
        (deriv f x * (1 / (x - z)) - f x * (1 / (x - z)) ^ 2)) * (x - z) ^ (-(1 + p))| ≤
      ε * (c * f x ^ 2 * |deriv (deriv f) x| + (1 + p) * c * |deriv f x| * f x ^ 2 +
        2 * c * |deriv f x| ^ 2 * |f x| + 2 * c * |deriv f x| * f x ^ 2) *
        (x - z) ^ (-(3 + p)) := by
  have hs : 0 < x - z := by linarith
  have hD1 : 1 / (x - z) ≤ 1 := by rw [div_le_one hs]; linarith
  obtain ⟨h0, h1⟩ := hAb1 (f x / (x - z))
  have h2 := hAb2 (f x / (x - z))
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hw : f x / (x - z) = f x * (1 / (x - z)) := by ring
  have hAm : |A_eps p ε (f x / (x - z)) - 1| ≤ c * ε * (f x * (1 / (x - z))) ^ 2 := by
    rw [abs_sub_comm, abs_of_nonneg h0, ← hw, hc]; linarith
  have hAd : |deriv (A_eps p ε) (f x / (x - z))| ≤ 2 * c * ε * |f x * (1 / (x - z))| := by
    rw [← hw, hc]; linarith
  have halg := c06_aux_I3_alg c ε (1 + p) (f x) (deriv f x) (deriv (deriv f) x) (1 / (x - z))
    (A_eps p ε (f x / (x - z)) - 1) (deriv (A_eps p ε) (f x / (x - z)))
    hc0 hε0 (by linarith) (by positivity) hD1 hAm hAd
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs _), ← c06_aux_rpow3 p (x - z) hs]
  have hS := Real.rpow_pos_of_pos hs (-(1 + p))
  calc _ ≤ ε * (1 / (x - z)) ^ 2 * (c * f x ^ 2 * |deriv (deriv f) x| +
        (1 + p) * c * |deriv f x| * f x ^ 2 + 2 * c * |deriv f x| ^ 2 * |f x| +
        2 * c * |deriv f x| * f x ^ 2) * (x - z) ^ (-(1 + p)) :=
        mul_le_mul_of_nonneg_right halg hS.le
    _ = _ := by ring

/-- Helper: differentiation of `∫_{-∞}^0 (ℐ₃ integrand) dz` under the integral sign. -/
theorem c06_aux_I3_hasDeriv_int (p ε c : ℝ) (hc : c = (p + 1) / 2) (hp : 0 < p)
    (hε0 : 0 ≤ ε) (f : ℝ → ℝ) (df : Differentiable ℝ f) (ddf : Differentiable ℝ (deriv f))
    (hAc : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε))
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (hAb2 : ∀ w, |deriv (A_eps p ε) w| ≤ (p + 1) * ε * |w|)
    (C₀ Y : ℝ) (hC₀ : 0 ≤ C₀) (hY : 8 ≤ Y)
    (b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀) (b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀)
    (b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y))
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2)) :
    HasDerivAt (fun y => ∫ z in Iio (0 : ℝ), deriv f y / (y - z) ^ (1 + p) *
        (A_eps p ε (f y / (y - z)) - 1))
      (∫ z in Iio (0 : ℝ), (deriv (deriv f) y₀ * (A_eps p ε (f y₀ / (y₀ - z)) - 1) -
        (1 + p) * deriv f y₀ * (1 / (y₀ - z)) * (A_eps p ε (f y₀ / (y₀ - z)) - 1) +
        deriv f y₀ * deriv (A_eps p ε) (f y₀ / (y₀ - z)) *
          (deriv f y₀ * (1 / (y₀ - z)) - f y₀ * (1 / (y₀ - z)) ^ 2)) *
          (y₀ - z) ^ (-(1 + p))) y₀ := by
  have dA : Differentiable ℝ (A_eps p ε) := hAc.differentiable (by simp)
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  set G : ℝ → ℝ → ℝ := fun x z => deriv f x / (x - z) ^ (1 + p) *
    (A_eps p ε (f x / (x - z)) - 1) with hG
  set G' : ℝ → ℝ → ℝ := fun x z =>
    (deriv (deriv f) x * (A_eps p ε (f x / (x - z)) - 1) -
      (1 + p) * deriv f x * (1 / (x - z)) * (A_eps p ε (f x / (x - z)) - 1) +
      deriv f x * deriv (A_eps p ε) (f x / (x - z)) *
        (deriv f x * (1 / (x - z)) - f x * (1 / (x - z)) ^ 2)) * (x - z) ^ (-(1 + p)) with hG'
  have mA : Measurable (A_eps p ε) := hAc.continuous.measurable
  have mdA : Measurable (deriv (A_eps p ε)) := measurable_deriv _
  have mG : ∀ x, AEStronglyMeasurable (G x) (volume.restrict (Iio 0)) := fun x => by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hG]
    fun_prop
  have mG' : ∀ x, AEStronglyMeasurable (G' x) (volume.restrict (Iio 0)) := fun x => by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hG']
    fun_prop
  set x₁ := 5 * Y / 8 with hx₁
  have hx₁1 : 1 ≤ x₁ := by rw [hx₁]; linarith
  set M : ℝ := c * C₀ ^ 2 * (C₀ * (3 * Y)) + (1 + p) * c * C₀ * C₀ ^ 2 + 2 * c * C₀ ^ 2 * C₀ +
    2 * c * C₀ * C₀ ^ 2 with hM
  have hball : ∀ x ∈ Metric.ball y₀ (Y / 8), x₁ ≤ x ∧ x ≤ 3 * Y := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith [hy₀.1, hy₀.2]
  have hbd : ∀ x ∈ Metric.ball y₀ (Y / 8), ∀ z, z < 0 → |G' x z| ≤
      ε * M * (x₁ - z) ^ (-(3 + p)) := by
    intro x hx z hz
    obtain ⟨hx1, hx2⟩ := hball x hx
    have hx1' : 1 ≤ x := le_trans hx₁1 hx1
    refine le_trans (c06_aux_I3_bG' p ε c hc hp hε0 f hAb1 hAb2 x z hx1' hz) ?_
    have e0 := b0 x hx1'
    have e1 := b1 x hx1'
    have e2 := b2 x hx1' hx2
    have ef : f x ^ 2 ≤ C₀ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e0 2
    have hs : 0 < x₁ - z := by linarith
    have hmono : (x - z) ^ (-(3 + p)) ≤ (x₁ - z) ^ (-(3 + p)) :=
      Real.rpow_le_rpow_of_nonpos hs (by linarith) (by linarith)
    have a1 : c * f x ^ 2 * |deriv (deriv f) x| ≤ c * C₀ ^ 2 * (C₀ * (3 * Y)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ef hc0) e2 (abs_nonneg _) (by positivity)
    have a2 : (1 + p) * c * |deriv f x| * f x ^ 2 ≤ (1 + p) * c * C₀ * C₀ ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity)) ef (sq_nonneg _) (by positivity)
    have a3 : 2 * c * |deriv f x| ^ 2 * |f x| ≤ 2 * c * C₀ ^ 2 * C₀ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) e1 2)
        (by positivity)) e0 (abs_nonneg _) (by positivity)
    have a4 : 2 * c * |deriv f x| * f x ^ 2 ≤ 2 * c * C₀ * C₀ ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity)) ef (sq_nonneg _) (by positivity)
    have hMx : c * f x ^ 2 * |deriv (deriv f) x| + (1 + p) * c * |deriv f x| * f x ^ 2 +
        2 * c * |deriv f x| ^ 2 * |f x| + 2 * c * |deriv f x| * f x ^ 2 ≤ M := by
      rw [hM]; linarith
    have hM0 : 0 ≤ c * f x ^ 2 * |deriv (deriv f) x| + (1 + p) * c * |deriv f x| * f x ^ 2 +
        2 * c * |deriv f x| ^ 2 * |f x| + 2 * c * |deriv f x| * f x ^ 2 := by positivity
    have hp0'' := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x - z) (-(3 + p))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hMx hε0) hmono hp0''
      (mul_nonneg hε0 (le_trans hM0 hMx))
  have hy₀1 : 1 ≤ y₀ := by linarith [hy₀.1]
  have hintG : Integrable (G y₀) (volume.restrict (Iio 0)) := by
    refine Integrable.mono' (((c06_aux_tail1 (3 + p) y₀ (by linarith) (by linarith)).1).const_mul
      (c * ε * (|deriv f y₀| * f y₀ ^ 2))) (mG y₀) ?_
    refine (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_)
    rw [Real.norm_eq_abs]; exact c06_aux_I3_bG p ε c hc f hAb1 y₀ z hy₀1 hz
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Iio 0))
    (F := G) (F' := G') (x₀ := y₀) (bound := fun z => ε * M * (x₁ - z) ^ (-(3 + p)))
    (s := Metric.ball y₀ (Y / 8)) (Metric.ball_mem_nhds _ (by linarith))
    (Eventually.of_forall mG) hintG (mG' y₀)
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz x hx => by
      rw [Real.norm_eq_abs]; exact hbd x hx z hz))
    (((c06_aux_tail1 (3 + p) x₁ (by linarith) (by linarith)).1).const_mul _)
    ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz x hx =>
      c06_aux_I3_hasDeriv p ε f df ddf dA x z (by
        have := (hball x hx).1; have : z < 0 := hz; linarith)))
  exact H.2

/-- Helper: the bounds of lem:c06_E9_I3 on `[Y,2Y]` for a generic profile `f`. -/
theorem c06_aux_I3_bounds (p ε c : ℝ) (hc : c = (p + 1) / 2) (hp : 0 < p) (hp1 : p < 1)
    (hε0 : 0 ≤ ε) (f : ℝ → ℝ)
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (hAb2 : ∀ w, |deriv (A_eps p ε) w| ≤ (p + 1) * ε * |w|)
    (C₀ Y y : ℝ) (hC₀ : 0 ≤ C₀) (hY : 1 ≤ Y) (hy : y ∈ Icc Y (2 * Y))
    (f0 : |f y| ≤ C₀) (f1 : |deriv f y| ≤ C₀) (f2 : |deriv (deriv f) y| ≤ 2 * C₀ * Y ^ (1 / p)) :
    |∫ z in Iio (0 : ℝ), deriv f y / (y - z) ^ (1 + p) * (A_eps p ε (f y / (y - z)) - 1)| ≤
      c * C₀ ^ 3 * ε * Y ^ (-p - 2) ∧
    |∫ z in Iio (0 : ℝ), (deriv (deriv f) y * (A_eps p ε (f y / (y - z)) - 1) -
        (1 + p) * deriv f y * (1 / (y - z)) * (A_eps p ε (f y / (y - z)) - 1) +
        deriv f y * deriv (A_eps p ε) (f y / (y - z)) *
          (deriv f y * (1 / (y - z)) - f y * (1 / (y - z)) ^ 2)) * (y - z) ^ (-(1 + p))| ≤
      (c + (1 + p) * c + 2 * c + 2 * c) * (2 * C₀ ^ 3) * ε * Y ^ (-p - 2 + 1 / p) := by
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hY0 : 0 < Y := by linarith
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  obtain ⟨hti, htv⟩ := c06_aux_tail1 (3 + p) y (by linarith) hy0
  have htv' : ∫ z in Iio (0 : ℝ), (y - z) ^ (-(3 + p)) ≤ Y ^ (-p - 2) := by
    rw [htv, show 1 - (3 + p) = -p - 2 by ring, show 3 + p - 1 = 2 + p by ring]
    have h1 : y ^ (-p - 2) ≤ Y ^ (-p - 2) := Real.rpow_le_rpow_of_nonpos hY0 hy.1 (by linarith)
    have h2 : 0 ≤ y ^ (-p - 2) := Real.rpow_nonneg hy0.le _
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hint0 : 0 ≤ ∫ z in Iio (0 : ℝ), (y - z) ^ (-(3 + p)) :=
    setIntegral_nonneg measurableSet_Iio (fun z hz => Real.rpow_nonneg (by
      have : z < 0 := hz; linarith) _)
  have fsq : f y ^ 2 ≤ C₀ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) f0 2
  have hYi : 1 ≤ Y ^ (1 / p) := Real.one_le_rpow hY (by positivity)
  constructor
  · have hb : |∫ z in Iio (0 : ℝ), deriv f y / (y - z) ^ (1 + p) * (A_eps p ε (f y / (y - z)) - 1)|
        ≤ ∫ z in Iio (0 : ℝ), c * ε * (|deriv f y| * f y ^ 2) * (y - z) ^ (-(3 + p)) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (hti.const_mul _)
        ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
      rw [Real.norm_eq_abs]; exact c06_aux_I3_bG p ε c hc f hAb1 y z hy1 hz
    rw [integral_const_mul] at hb
    have hcoef : c * ε * (|deriv f y| * f y ^ 2) ≤ c * C₀ ^ 3 * ε := by
      have := mul_le_mul f1 fsq (sq_nonneg _) hC₀
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hc0 hε0)
      linarith [show c * ε * (C₀ * C₀ ^ 2) = c * C₀ ^ 3 * ε by ring]
    refine le_trans hb ?_
    exact mul_le_mul hcoef htv' hint0 (by positivity)
  · set M₁ := c * f y ^ 2 * |deriv (deriv f) y| + (1 + p) * c * |deriv f y| * f y ^ 2 +
        2 * c * |deriv f y| ^ 2 * |f y| + 2 * c * |deriv f y| * f y ^ 2 with hM₁
    have hb : |∫ z in Iio (0 : ℝ), (deriv (deriv f) y * (A_eps p ε (f y / (y - z)) - 1) -
        (1 + p) * deriv f y * (1 / (y - z)) * (A_eps p ε (f y / (y - z)) - 1) +
        deriv f y * deriv (A_eps p ε) (f y / (y - z)) *
          (deriv f y * (1 / (y - z)) - f y * (1 / (y - z)) ^ 2)) * (y - z) ^ (-(1 + p))| ≤
        ∫ z in Iio (0 : ℝ), ε * M₁ * (y - z) ^ (-(3 + p)) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (hti.const_mul _)
        ((ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_))
      rw [Real.norm_eq_abs]; exact c06_aux_I3_bG' p ε c hc hp hε0 f hAb1 hAb2 y z hy1 hz
    rw [integral_const_mul] at hb
    have C3 : 0 ≤ C₀ ^ 3 := by positivity
    have a1 : c * f y ^ 2 * |deriv (deriv f) y| ≤ c * (2 * C₀ ^ 3) * Y ^ (1 / p) := by
      have := mul_le_mul fsq f2 (abs_nonneg _) (sq_nonneg _)
      have := mul_le_mul_of_nonneg_left this hc0
      have e : c * (C₀ ^ 2 * (2 * C₀ * Y ^ (1 / p))) = c * (2 * C₀ ^ 3) * Y ^ (1 / p) := by ring
      linarith [mul_assoc c (f y ^ 2) (|deriv (deriv f) y|)]
    have k : ∀ K : ℝ, 0 ≤ K → K * C₀ ^ 3 ≤ K * (2 * C₀ ^ 3) * Y ^ (1 / p) := fun K hK => by
      have : 0 ≤ K * C₀ ^ 3 := by positivity
      nlinarith
    have a2 : (1 + p) * c * |deriv f y| * f y ^ 2 ≤ (1 + p) * c * C₀ ^ 3 := by
      have := mul_le_mul f1 fsq (sq_nonneg _) hC₀
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (1 + p) * c)
      linarith [show (1 + p) * c * (C₀ * C₀ ^ 2) = (1 + p) * c * C₀ ^ 3 by ring,
        mul_assoc ((1 + p) * c) (|deriv f y|) (f y ^ 2)]
    have a3 : 2 * c * |deriv f y| ^ 2 * |f y| ≤ 2 * c * C₀ ^ 3 := by
      have := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) f1 2) f0 (abs_nonneg _) (sq_nonneg _)
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * c)
      linarith [show 2 * c * (C₀ ^ 2 * C₀) = 2 * c * C₀ ^ 3 by ring,
        mul_assoc (2 * c) (|deriv f y| ^ 2) (|f y|)]
    have a4 : 2 * c * |deriv f y| * f y ^ 2 ≤ 2 * c * C₀ ^ 3 := by
      have := mul_le_mul f1 fsq (sq_nonneg _) hC₀
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * c)
      linarith [show 2 * c * (C₀ * C₀ ^ 2) = 2 * c * C₀ ^ 3 by ring,
        mul_assoc (2 * c) (|deriv f y|) (f y ^ 2)]
    have hM₁b : M₁ ≤ (c + (1 + p) * c + 2 * c + 2 * c) * (2 * C₀ ^ 3) * Y ^ (1 / p) := by
      have b2 := k ((1 + p) * c) (by positivity)
      have b3 := k (2 * c) (by positivity)
      have e : (c + (1 + p) * c + 2 * c + 2 * c) * (2 * C₀ ^ 3) * Y ^ (1 / p) =
          c * (2 * C₀ ^ 3) * Y ^ (1 / p) + (1 + p) * c * (2 * C₀ ^ 3) * Y ^ (1 / p) +
          2 * c * (2 * C₀ ^ 3) * Y ^ (1 / p) + 2 * c * (2 * C₀ ^ 3) * Y ^ (1 / p) := by ring
      rw [hM₁, e]; linarith
    have hM₁0 : 0 ≤ M₁ := by positivity
    have e : Y ^ (1 / p) * Y ^ (-p - 2) = Y ^ (-p - 2 + 1 / p) := by
      rw [← Real.rpow_add hY0]; ring_nf
    refine le_trans hb ?_
    calc ε * M₁ * ∫ z in Iio (0 : ℝ), (y - z) ^ (-(3 + p))
        ≤ ε * ((c + (1 + p) * c + 2 * c + 2 * c) * (2 * C₀ ^ 3) * Y ^ (1 / p)) * Y ^ (-p - 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hM₁b hε0) htv' hint0 (by positivity)
      _ = _ := by rw [← e]; ring

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:c06_E9_I3.  `ℐ₃` is differentiable on `J_Y` and
`|∂^j ℐ₃| ≤ C ε Y^{-p-2+j/p}` on `[Y,2Y]`. -/
theorem c06_E9_I3 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        let E : ℝ → ℝ := c06_E9_split_I3 P.p ε (approximate_solution_family P.p R ε μ)
        DifferentiableOn ℝ E (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j E y| ≤ C * ε * Y ^ (-P.p - 2 + j / P.p) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hplo := P.hp_lo
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have he1 : 1 / P.p - beta P.p ≤ 1 := by
    unfold beta
    rw [show 1 / P.p - (P.p + 1) / (2 * P.p) = (1 - P.p) / (2 * P.p) by field_simp; ring]
    rw [div_le_one (by positivity)]; linarith
  have he0 : 0 ≤ 1 / P.p - beta P.p := by linarith
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  set c : ℝ := (P.p + 1) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set K₁ : ℝ := (c + (1 + P.p) * c + 2 * c + 2 * c) * (2 * C₀ ^ 3) with hK₁
  refine ⟨|calpha P.p| * (K₁ + c * C₀ ^ 3) + 1, by positivity, ?_⟩
  intro Y hY ε hε μ hμ E
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, -, -, -, h3⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  have hAb1 : ∀ w, 0 ≤ 1 - A_eps P.p ε w ∧ 1 - A_eps P.p ε w ≤ (P.p + 1) / 2 * ε * w ^ 2 :=
    fun w => (hAb w).1
  have hAb2 : ∀ w, |deriv (A_eps P.p ε) w| ≤ (P.p + 1) * ε * |w| := fun w => (hAb w).2.1
  set f := approximate_solution_family P.p R ε μ with hf
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have ddf : Differentiable ℝ (deriv f) := by
    simpa using hfs.differentiable_iteratedDeriv 1 htop1
  have bf0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ * x ^ (-P.p) := fun x hx => (h3 x hx).1
  have bf1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ * x ^ (-beta P.p) := fun x hx => by
    simpa using (h3 x hx).2 0 (by norm_num)
  have bf2 : ∀ x, 1 ≤ x → |deriv (deriv f) x| ≤ C₀ * x ^ (-beta P.p + 1 / P.p) := fun x hx => by
    have := (h3 x hx).2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ := fun x hx => le_trans (bf0 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)))
  have b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ := fun x hx => le_trans (bf1 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by
      have : 0 < beta P.p := by unfold beta; positivity
      linarith)))
  have b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y) := fun x hx hx3 => by
    refine le_trans (bf2 x hx) (mul_le_mul_of_nonneg_left ?_ hC₀0)
    have : x ^ (-beta P.p + 1 / P.p) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    rw [Real.rpow_one] at this; linarith
  have hEdef : E = fun y => -(calpha P.p * ∫ z in Iio (0 : ℝ), deriv f y / (y - z) ^ (1 + P.p) *
      (A_eps P.p ε (f y / (y - z)) - 1)) := rfl
  have hderiv := fun y₀ (hy₀ : y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2)) =>
    ((c06_aux_I3_hasDeriv_int P.p ε c hc hp0 hε0 f df ddf hAc hAb1 hAb2 C₀ Y hC₀0 hY8 b0 b1 b2
      y₀ hy₀).const_mul (calpha P.p)).neg
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [hEdef]; exact (hderiv y hy).differentiableAt.differentiableWithinAt
  intro y hy j hj
  have hyJ : y ∈ Ioo (3 * Y / 4) (5 * Y / 2) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hy1 : 1 ≤ y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  have f2 : |deriv (deriv f) y| ≤ 2 * C₀ * Y ^ (1 / P.p) := by
    refine le_trans (bf2 y hy1) ?_
    have h1 : y ^ (-beta P.p + 1 / P.p) ≤ (2 * Y) ^ (-beta P.p + 1 / P.p) :=
      Real.rpow_le_rpow hy0.le hy.2 (by linarith)
    rw [Real.mul_rpow (by norm_num) hY0.le] at h1
    have h2 : (2 : ℝ) ^ (-beta P.p + 1 / P.p) ≤ 2 := by
      conv_rhs => rw [← Real.rpow_one (2 : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : Y ^ (-beta P.p + 1 / P.p) ≤ Y ^ (1 / P.p) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by
        have : 0 < beta P.p := by unfold beta; positivity
        linarith)
    have h4 : 0 ≤ Y ^ (-beta P.p + 1 / P.p) := Real.rpow_nonneg hY0.le _
    have h5 : (2 : ℝ) ^ (-beta P.p + 1 / P.p) * Y ^ (-beta P.p + 1 / P.p) ≤ 2 * Y ^ (1 / P.p) :=
      mul_le_mul h2 h3 h4 (by norm_num)
    have := mul_le_mul_of_nonneg_left (le_trans h1 h5) hC₀0
    linarith [show C₀ * (2 * Y ^ (1 / P.p)) = 2 * C₀ * Y ^ (1 / P.p) by ring]
  obtain ⟨B0, B1⟩ := c06_aux_I3_bounds P.p ε c hc hp0 hp1 hε0 f hAb1 hAb2 C₀ Y y hC₀0 hY1 hy
    (b0 y hy1) (b1 y hy1) f2
  have hCa := abs_nonneg (calpha P.p)
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
    rw [hEdef]
    simp only
    rw [abs_neg, abs_mul]
    have hY2 : 0 ≤ Y ^ (-P.p - 2) := Real.rpow_nonneg hY0.le _
    calc |calpha P.p| * |_| ≤ |calpha P.p| * (c * C₀ ^ 3 * ε * Y ^ (-P.p - 2)) :=
          mul_le_mul_of_nonneg_left B0 hCa
      _ ≤ (|calpha P.p| * (K₁ + c * C₀ ^ 3) + 1) * ε * Y ^ (-P.p - 2) := by
          have hK₁0 : 0 ≤ |calpha P.p| * K₁ * ε * Y ^ (-P.p - 2) := by positivity
          have : 0 ≤ ε * Y ^ (-P.p - 2) := by positivity
          have e : (|calpha P.p| * (K₁ + c * C₀ ^ 3) + 1) * ε * Y ^ (-P.p - 2) =
              |calpha P.p| * (c * C₀ ^ 3 * ε * Y ^ (-P.p - 2)) +
                (|calpha P.p| * K₁ * ε * Y ^ (-P.p - 2) + ε * Y ^ (-P.p - 2)) := by ring
          rw [e]; linarith
  · simp only [iteratedDeriv_one, Nat.cast_one]
    have hd : HasDerivAt E _ y := hderiv y hyJ
    rw [hd.deriv, abs_neg, abs_mul]
    have hY2 : 0 ≤ Y ^ (-P.p - 2 + 1 / P.p) := Real.rpow_nonneg hY0.le _
    calc |calpha P.p| * |_| ≤ |calpha P.p| * (K₁ * ε * Y ^ (-P.p - 2 + 1 / P.p)) :=
          mul_le_mul_of_nonneg_left B1 hCa
      _ ≤ (|calpha P.p| * (K₁ + c * C₀ ^ 3) + 1) * ε * Y ^ (-P.p - 2 + 1 / P.p) := by
          have h0 : 0 ≤ |calpha P.p| * (c * C₀ ^ 3) * ε * Y ^ (-P.p - 2 + 1 / P.p) := by
            positivity
          have : 0 ≤ ε * Y ^ (-P.p - 2 + 1 / P.p) := by positivity
          have e : (|calpha P.p| * (K₁ + c * C₀ ^ 3) + 1) * ε * Y ^ (-P.p - 2 + 1 / P.p) =
              |calpha P.p| * (K₁ * ε * Y ^ (-P.p - 2 + 1 / P.p)) +
                (|calpha P.p| * (c * C₀ ^ 3) * ε * Y ^ (-P.p - 2 + 1 / P.p) +
                  ε * Y ^ (-P.p - 2 + 1 / P.p)) := by ring
          rw [e]; linarith

/-! ### C¹ of ℐ₁, ℐ₂ on J_Y (for prop:approx_residual_positive) -/
/-- Helper: `C¹` on an open set from a derivative that is continuous there. -/
theorem c06_aux_C1E9b_C1 (E G : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hd : ∀ y ∈ U, HasDerivAt E (G y) y) (hc : ContinuousOn G U) : ContDiffOn ℝ 1 E U := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun y hy => (hd y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hc.congr (fun y hy => (hd y hy).deriv)

/-- Helper: continuity of `y ↦ dH(y,z)` (the `ℐ₁` integrand derivative) for `y > z`. -/
theorem c06_aux_C1E9b_dH_cont (a : ℝ → ℝ) (p : ℝ) (f : ℝ → ℝ) (hac : Continuous a)
    (ha1 : Continuous (deriv a)) (ha2 : Continuous (deriv (deriv a))) (hf : Continuous f)
    (hf1 : Continuous (deriv f)) (y z : ℝ) (hyz : z < y) :
    ContinuousAt (fun x => c06_aux_E9I1_dH a p f x z) y := by
  have hne : y - z ≠ 0 := by linarith
  unfold c06_aux_E9I1_dH
  fun_prop (disch := first | exact hne | exact Or.inl hne)

/-- Helper: continuity of `y ↦ ∫_{-∞}^0 dH(y,z) dz` on `J_Y` (dominated convergence). -/
theorem c06_aux_C1E9b_I1cont (a : ℝ → ℝ) (p : ℝ) (f : ℝ → ℝ) (K C₀ Y : ℝ)
    (hac : Continuous a) (ha : Differentiable ℝ a) (ha' : Differentiable ℝ (deriv a))
    (ha'' : Differentiable ℝ (deriv (deriv a)))
    (hK2 : ∀ w, |deriv (deriv a) w| ≤ K) (hK3 : ∀ w, |deriv (deriv (deriv a)) w| ≤ K)
    (hC₀ : 0 ≤ C₀) (hp : 0 < p) (hf : Differentiable ℝ f) (hf1 : Continuous (deriv f))
    (hg : ∀ x, |f x - corner x| ≤ C₀)
    (hd1 : ∀ x, |deriv f x| ≤ C₀) (hY : 8 ≤ Y) :
    ContinuousOn (fun y => ∫ z in Iio (0 : ℝ), c06_aux_E9I1_dH a p f y z)
      (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  intro y₀ hy₀
  refine ContinuousAt.continuousWithinAt ?_
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hK2 0)
  have mA : Measurable a := hac.measurable
  have mdA : Measurable (deriv a) := measurable_deriv _
  have mddA : Measurable (deriv (deriv a)) := measurable_deriv _
  have mf : Measurable f := hf.continuous.measurable
  have mdf : Measurable (deriv f) := measurable_deriv _
  have mG' : ∀ x, AEStronglyMeasurable (fun z => c06_aux_E9I1_dH a p f x z)
      (volume.restrict (Iio 0)) := fun x => by
    refine Measurable.aestronglyMeasurable ?_
    unfold c06_aux_E9I1_dH
    fun_prop
  set x₁ := 5 * Y / 8 with hx₁
  have hx₁1 : 1 ≤ x₁ := by rw [hx₁]; linarith
  set M : ℝ := K * ((8 + 4 * (1 + p)) * C₀ ^ 2 + 2 * C₀ * C₀) with hM
  have hball : ∀ x ∈ Metric.ball y₀ (Y / 8), x₁ ≤ x := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    linarith [hy₀.1]
  have hbd : ∀ x ∈ Metric.ball y₀ (Y / 8), ∀ z, z < 0 →
      |c06_aux_E9I1_dH a p f x z| ≤ M * (x₁ - z) ^ (-(3 + p)) := by
    intro x hx z hz
    have hx1 := hball x hx
    have hs : 1 ≤ x - z := by linarith
    have b := (c06_aux_E9I1_bounds a p f K C₀ ha ha' ha'' hK2 hK3 hC₀ hp.le hg x z
      (by linarith) hz).2
    have m1 : (x - z) ^ (-(4 + p)) ≤ (x - z) ^ (-(3 + p)) :=
      Real.rpow_le_rpow_of_exponent_le hs (by linarith)
    have m2 : (x - z) ^ (-(3 + p)) ≤ (x₁ - z) ^ (-(3 + p)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    refine b.trans ?_
    rw [hM]
    have e1 : (8 + 4 * (1 + p)) * C₀ ^ 2 * (x - z) ^ (-(4 + p)) ≤
        (8 + 4 * (1 + p)) * C₀ ^ 2 * (x₁ - z) ^ (-(3 + p)) := by
      gcongr; exact m1.trans m2
    have e2 : 2 * C₀ * |deriv f x| * (x - z) ^ (-(3 + p)) ≤ 2 * C₀ * C₀ * (x₁ - z) ^ (-(3 + p)) := by
      gcongr
      · exact hd1 x
    calc _ ≤ K * ((8 + 4 * (1 + p)) * C₀ ^ 2 * (x₁ - z) ^ (-(3 + p)) +
          2 * C₀ * C₀ * (x₁ - z) ^ (-(3 + p))) := by gcongr
      _ = _ := by ring
  refine continuousAt_of_dominated (Eventually.of_forall mG')
    (bound := fun z => M * (x₁ - z) ^ (-(3 + p))) ?_
    (((c06_aux_tail1 (3 + p) x₁ (by linarith) (by linarith)).1).const_mul _) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ (show (0 : ℝ) < Y / 8 by linarith)] with x hx
    exact (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => by
      rw [Real.norm_eq_abs]; exact hbd x hx z hz)
  · exact (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz =>
      c06_aux_C1E9b_dH_cont a p f hac ha'.continuous ha''.continuous hf.continuous
        hf1 y₀ z (by have : z < 0 := hz; linarith [hy₀.1]))

/-- `ℐ₁` is `C¹` on `J_Y` (supports prop:approx_residual_positive). -/
theorem c06_E9_I1_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiffOn ℝ 1 (c06_E9_split_I1 P.p ε (approximate_solution_family P.p R ε μ))
          (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, hCA, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  intro Y hY ε hε μ hμ
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, h1, -, -, -⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  set f := approximate_solution_family P.p R ε μ with hf
  set a := A_eps P.p ε with ha
  set K : ℝ := CA * ε with hK
  have htop : ∀ n : ℕ, ((n : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) := fun n =>
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)
  have da : Differentiable ℝ a := hAc.differentiable (by simp)
  have da' : Differentiable ℝ (deriv a) := by
    simpa using hAc.differentiable_iteratedDeriv 1 (htop 1)
  have da'' : Differentiable ℝ (deriv (deriv a)) := by
    simpa [iteratedDeriv_succ] using hAc.differentiable_iteratedDeriv 2 (htop 2)
  have hK2 : ∀ w, |deriv (deriv a) w| ≤ K := fun w => by
    have := (hAb w).2.2.1
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    linarith [abs_nonneg (deriv (deriv (deriv a)) w)]
  have hK3 : ∀ w, |deriv (deriv (deriv a)) w| ≤ K := fun w => by
    have := (hAb w).2.2.1
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    linarith [abs_nonneg (deriv (deriv a) w)]
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have df1 : Continuous (deriv f) := hfs.continuous_deriv (by simp)
  have hg : ∀ x, |f x - corner x| ≤ C₀ := fun x => (h1 x).2.trans
    (mul_le_of_le_one_right hC₀0 (c06_aux_jb_rpow_neg_le_one x P.p hp0.le))
  have hd1 : ∀ x, |deriv f x| ≤ C₀ := fun x => (h1 x).1
  have hEq : ∀ y, 0 < y → c06_E9_split_I1 P.p ε f y =
      calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I1_H a P.p f y z :=
    fun y hy => by
      show calpha P.p * _ = _
      congr 1
      exact setIntegral_congr_fun measurableSet_Iio (fun z hz => c06_aux_E9I1_pt P.p ε f y z hy hz)
  refine c06_aux_C1E9b_C1 _ (fun y => calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I1_dH a P.p f y z)
    _ isOpen_Ioo (fun y₀ hy₀ => ?_) ((c06_aux_C1E9b_I1cont a P.p f K C₀ Y hAc.continuous da da' da''
      hK2 hK3 hC₀0 hp0 df df1 hg hd1 hY8).const_smul (calpha P.p))
  have hy₀0 : 0 < y₀ := by linarith [hy₀.1]
  exact ((c06_aux_E9I1_hasDeriv_int a P.p f K C₀ Y hAc.continuous da da' da'' hK2 hK3 hC₀0
    hp0 df hg hd1 hY8 y₀ hy₀).const_mul (calpha P.p)).congr_of_eventuallyEq
    (by filter_upwards [Ioi_mem_nhds hy₀0] with y hy using hEq y hy)

/-- Helper: continuity of `x ↦ G'(x,z)` (the `ℐ₂` integrand derivative) for `x > z`. -/
theorem c06_aux_C1E9b_G'_cont (p : ℝ) (A f : ℝ → ℝ) (hA : Continuous A) (hA1 : Continuous (deriv A))
    (hf : Continuous f) (hf1 : Continuous (deriv f)) (hf2 : Continuous (deriv (deriv f)))
    (y z : ℝ) (hyz : z < y) :
    ContinuousAt (fun x => c06_aux_E9I2_G' p A f x z) y := by
  have hne : y - z ≠ 0 := by linarith
  unfold c06_aux_E9I2_G'
  fun_prop (disch := first | exact hne | exact Or.inl hne)

/-- Helper: continuity of `y ↦ ∫_{-∞}^0 G'(y,z) dz` on `J_Y` (dominated convergence). -/
theorem c06_aux_C1E9b_I2cont (p : ℝ) (hp : 0 < p) (A f : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA' : Differentiable ℝ (deriv A)) (a1 a2 C₀ : ℝ) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hC₀ : 0 ≤ C₀) (hA1 : ∀ w, |deriv A w| ≤ a1 * |w|) (hA2 : ∀ w, |deriv (deriv A) w| ≤ a2)
    (df : Differentiable ℝ f) (ddf : Differentiable ℝ (deriv f))
    (cddf : Continuous (deriv (deriv f))) (Y : ℝ) (hY : 8 ≤ Y)
    (b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀) (b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀)
    (b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y))
    (bn : ∀ z, z < 0 → |f z + z| ≤ C₀ ∧ |deriv f z + 1| ≤ C₀) :
    ContinuousOn (fun y => ∫ z in Iio (0 : ℝ), c06_aux_E9I2_G' p A f y z)
      (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  intro y₀ hy₀
  refine ContinuousAt.continuousWithinAt ?_
  have mA : Measurable A := hA.continuous.measurable
  have mdA : Measurable (deriv A) := measurable_deriv _
  have mf : Measurable f := df.continuous.measurable
  have mdf : Measurable (deriv f) := measurable_deriv _
  have mddf : Measurable (deriv (deriv f)) := measurable_deriv _
  have mG' : ∀ x, AEStronglyMeasurable (c06_aux_E9I2_G' p A f x) (volume.restrict (Iio 0)) :=
    fun x => by
      refine Measurable.aestronglyMeasurable ?_
      unfold c06_aux_E9I2_G'
      fun_prop
  set K := 1 + 2 * C₀ with hK
  set c1 := a1 * K * (2 * C₀) with hc1
  set M : ℝ := C₀ * (3 * Y) * c1 + (C₀ + C₀) * (a1 * K * C₀ + (a1 * K + a2) * (2 * C₀) +
    (1 + p) * c1) with hM
  set x₁ := 5 * Y / 8 with hx₁
  have hx₁1 : 1 ≤ x₁ := by rw [hx₁]; linarith
  have hball : ∀ x ∈ Metric.ball y₀ (Y / 8), x₁ ≤ x ∧ x ≤ 3 * Y := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith [hy₀.1, hy₀.2]
  have hc10 : 0 ≤ c1 := by positivity
  have hbd : ∀ x ∈ Metric.ball y₀ (Y / 8), ∀ z, z < 0 →
      |c06_aux_E9I2_G' p A f x z| ≤ M * (x₁ - z) ^ (-(2 + p)) := by
    intro x hx z hz
    obtain ⟨hx1, hx2⟩ := hball x hx
    have hx1' : 1 ≤ x := le_trans hx₁1 hx1
    obtain ⟨-, hpt⟩ := c06_aux_E9I2_pt p hp A f hA hA' a1 a2 C₀ ha1 ha2 hC₀ hA1 hA2 x z hx1' hz
      (b0 x hx1') (bn z hz).1
    refine le_trans hpt ?_
    have e1 := b1 x hx1'
    have e2 := b2 x hx1' hx2
    have e3 := (bn z hz).2
    have hs : 0 < x₁ - z := by linarith
    have hmono : (x - z) ^ (-(2 + p)) ≤ (x₁ - z) ^ (-(2 + p)) :=
      Real.rpow_le_rpow_of_nonpos hs (by linarith) (by linarith)
    have hcoef : |deriv (deriv f) x| * c1 + (|deriv f x| + |deriv f z + 1|) *
        (a1 * K * |deriv f x| + (a1 * K + a2) * (2 * C₀) + (1 + p) * c1) ≤ M := by
      rw [hM]
      have h1 : |deriv (deriv f) x| * c1 ≤ C₀ * (3 * Y) * c1 := mul_le_mul_of_nonneg_right e2 hc10
      have h2 : a1 * K * |deriv f x| ≤ a1 * K * C₀ := mul_le_mul_of_nonneg_left e1 (by positivity)
      have h3 : 0 ≤ a1 * K * |deriv f x| + (a1 * K + a2) * (2 * C₀) + (1 + p) * c1 := by
        positivity
      have h4 := mul_le_mul (add_le_add e1 e3) (by linarith : a1 * K * |deriv f x| +
        (a1 * K + a2) * (2 * C₀) + (1 + p) * c1 ≤ a1 * K * C₀ + (a1 * K + a2) * (2 * C₀) +
        (1 + p) * c1) h3 (by positivity)
      linarith
    have h0 : 0 ≤ |deriv (deriv f) x| * c1 + (|deriv f x| + |deriv f z + 1|) *
        (a1 * K * |deriv f x| + (a1 * K + a2) * (2 * C₀) + (1 + p) * c1) := by positivity
    exact mul_le_mul hcoef hmono (Real.rpow_nonneg (by linarith) _) (le_trans h0 hcoef)
  refine continuousAt_of_dominated (Eventually.of_forall mG')
    (bound := fun z => M * (x₁ - z) ^ (-(2 + p))) ?_
    (((c06_aux_tail1 (2 + p) x₁ (by linarith) (by linarith)).1).const_mul _) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ (show (0 : ℝ) < Y / 8 by linarith)] with x hx
    exact (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => by
      rw [Real.norm_eq_abs]; exact hbd x hx z hz)
  · exact (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz =>
      c06_aux_C1E9b_G'_cont p A f hA.continuous hA'.continuous df.continuous ddf.continuous cddf
        y₀ z (by have : z < 0 := hz; linarith [hy₀.1]))

/-- `ℐ₂` is `C¹` on `J_Y` (supports prop:approx_residual_positive). -/
theorem c06_E9_I2_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiffOn ℝ 1 (c06_E9_split_I2 P.p ε (approximate_solution_family P.p R ε μ))
          (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hplo := P.hp_lo
  have hb1 : 1 ≤ beta P.p := by
    unfold beta; rw [le_div_iff₀ (by linarith)]; linarith
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, hCA, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  set k1 : ℝ := (P.p + 1) * (1 + 2 * C₀) * (2 * C₀) with hk1
  set kA : ℝ := (P.p + 1) * (1 + 2 * C₀) * C₀ + ((P.p + 1) * (1 + 2 * C₀) + CA) * (2 * C₀)
    with hkA
  set q : ℝ := kA + (1 + P.p) * k1 with hq
  have hk10 : 0 ≤ k1 := by positivity
  have hq0 : 0 ≤ q := by positivity
  set C0t : ℝ := k1 * C₀ + k1 * C₀ * (1 + 1 / P.p) with hC0t
  set C1t : ℝ := k1 * C₀ + C₀ * q + C₀ * q * (1 + 1 / P.p) with hC1t
  have hC0t0 : 0 ≤ C0t := by positivity
  have hC1t0 : 0 ≤ C1t := by positivity
  intro Y hY ε hε μ hμ
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, h1, -, h2n, h3⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  set A := A_eps P.p ε with hAdef
  have hA1 : ∀ w, |deriv A w| ≤ ((P.p + 1) * ε) * |w| := fun w => (hAb w).2.1
  have hA2 : ∀ w, |deriv (deriv A) w| ≤ CA * ε := fun w => by
    have := (hAb w).2.2.1
    have e : iteratedDeriv 2 A w = deriv (deriv A) w := by
      simp [iteratedDeriv_succ]
    rw [e] at this; linarith [abs_nonneg (iteratedDeriv 3 A w)]
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have dA : Differentiable ℝ A := hAc.differentiable (by simp)
  have ddA : Differentiable ℝ (deriv A) := by
    simpa using hAc.differentiable_iteratedDeriv 1 htop1
  set f := approximate_solution_family P.p R ε μ with hf
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have ddf : Differentiable ℝ (deriv f) := by
    simpa using hfs.differentiable_iteratedDeriv 1 htop1
  have bf0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ * x ^ (-P.p) := fun x hx => (h3 x hx).1
  have bf1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ * x ^ (-beta P.p) := fun x hx => by
    simpa using (h3 x hx).2 0 (by norm_num)
  have bf2 : ∀ x, 1 ≤ x → |deriv (deriv f) x| ≤ C₀ * x ^ (-beta P.p + 1 / P.p) := fun x hx => by
    have := (h3 x hx).2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ := fun x hx => le_trans (bf0 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)))
  have b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ := fun x hx => le_trans (bf1 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)))
  have b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y) := fun x hx hx3 => by
    refine le_trans (bf2 x hx) (mul_le_mul_of_nonneg_left ?_ hC₀0)
    have hinv : 1 / P.p < 4 / 3 := by rw [div_lt_div_iff₀ hp0 (by norm_num)]; linarith
    have : x ^ (-beta P.p + 1 / P.p) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    rw [Real.rpow_one] at this; linarith
  have bnw : ∀ z, z < 0 → |deriv f z + 1| ≤ C₀ * jb z ^ (-1 - P.p) := fun z hz => by
    have := h2n z hz.le
    rwa [show -P.p - 1 = -1 - P.p by ring] at this
  have bn : ∀ z, z < 0 → |f z + z| ≤ C₀ ∧ |deriv f z + 1| ≤ C₀ := fun z hz => by
    constructor
    · have h := (h1 z).2
      have hc : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
      rw [hc, sub_neg_eq_add] at h
      exact le_trans h (mul_le_of_le_one_right hC₀0 (c06_aux_jb_rpow_neg_le_one z P.p hp0.le))
    · refine le_trans (bnw z hz) (mul_le_of_le_one_right hC₀0 ?_)
      have := c06_aux_jb_rpow_neg_le_one z (1 + P.p) (by linarith)
      rwa [show -(1 + P.p) = -1 - P.p by ring] at this
  -- the integrand in smooth form
  have hEeq : ∀ y, 0 < y → c06_E9_split_I2 P.p ε f y = calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I2_G P.p A f y z := by
    intro y hy
    show calpha P.p * _ = _
    congr 1
    refine setIntegral_congr_fun measurableSet_Iio (fun z hz => ?_)
    have hz0 : z < 0 := hz
    have hne : y ≠ z := by intro e; linarith
    have hyz : 0 < y - z := by linarith
    have hcy : corner y = 0 := by simp only [corner]; exact max_eq_right (by linarith)
    have hcz : corner z = -z := by simp only [corner]; exact max_eq_left (by linarith)
    simp only [c06_aux_E9I2_G, c01_secant, if_neg hne, hcy, hcz, zero_sub, neg_neg]
    rw [Real.rpow_neg hyz.le, div_eq_mul_inv]

  have cddf : Continuous (deriv (deriv f)) := by
    have := hfs.continuous_iteratedDeriv 2 (by simp)
    simpa [iteratedDeriv_succ] using this
  refine c06_aux_C1E9b_C1 _ (fun y => calpha P.p * ∫ z in Iio (0 : ℝ), c06_aux_E9I2_G' P.p A f y z)
    _ isOpen_Ioo (fun y₀ hy₀ => ?_) ((c06_aux_C1E9b_I2cont P.p hp0 A f dA ddA ((P.p + 1) * ε)
      (CA * ε) C₀ (by positivity) (by positivity) hC₀0 hA1 hA2 df ddf cddf Y hY8 b0 b1 b2
      bn).const_smul (calpha P.p))
  have hy0 : 0 < y₀ := by linarith [hy₀.1]
  refine ((c06_aux_E9I2_hasDeriv_int P.p hp0 A f dA ddA ((P.p + 1) * ε) (CA * ε) C₀
    (by positivity) (by positivity) hC₀0 hA1 hA2 df ddf Y hY8 b0 b1 b2 bn y₀ hy₀).const_mul
    (calpha P.p)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hy0] with x hx
  exact hEeq x hx

/-! ### C¹ of ℰ_{9,+}, ℐ₃ on J_Y (for prop:approx_residual_positive) -/
/-- Helper: continuity in `y` of the `y`-derivative integrand of `F_g` (lem:c06_E9_positive). -/
theorem c06_aux_C1E9a_dFcont (p ε : ℝ) (hA : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε))
    (f g : ℝ → ℝ) (hdf : Continuous (deriv f)) (hddf : Continuous (deriv (deriv f)))
    (hdg : Differentiable ℝ g) (hcdg : Continuous (deriv g)) (y₀ z : ℝ) (hne : y₀ ≠ z) :
    ContinuousAt (fun y => c06_aux_E9pos_dF p ε f g y z) y₀ := by
  have hAc : Continuous (A_eps p ε) := hA.continuous
  have hdAc : Continuous (deriv (A_eps p ε)) := hA.continuous_deriv (by simp)
  have hyz : y₀ - z ≠ 0 := sub_ne_zero.mpr hne
  have cs : ContinuousAt (fun y => c01_secant g y z) y₀ :=
    (c06_aux_E9pos_secd g y₀ z hne (hdg y₀)).continuousAt
  have cA : ContinuousAt (fun y => A_eps p ε (c01_secant g y z)) y₀ :=
    ContinuousAt.comp (g := A_eps p ε) hAc.continuousAt cs
  have cdA : ContinuousAt (fun y => deriv (A_eps p ε) (c01_secant g y z)) y₀ :=
    ContinuousAt.comp (g := deriv (A_eps p ε)) hdAc.continuousAt cs
  have cl : ContinuousAt (fun y : ℝ => y - z) y₀ := (continuous_id.sub continuous_const).continuousAt
  have ck : ContinuousAt (fun y : ℝ => |y - z| ^ (-(1 + p))) y₀ :=
    cl.abs.rpow_const (Or.inl (abs_ne_zero.mpr hyz))
  unfold c06_aux_E9pos_dF
  refine ((hddf.continuousAt.mul (cA.sub continuousAt_const)).mul ck).add ?_ |>.add ?_
  · exact ((hdf.continuousAt.sub continuousAt_const).mul
      (cdA.mul ((hcdg.continuousAt.sub cs).div cl hyz))).mul ck
  · exact ((hdf.continuousAt.sub continuousAt_const).mul (cA.sub continuousAt_const)).mul
      ((continuousAt_const.mul ck).div cl hyz)

/-- Helper for lem:c06_E9_positive (C¹): continuity on `J_Y` of
`y ↦ ∫_{(0,∞)∖[Y/2,3Y]} ∂_y F_g(y,z) dz`. -/
theorem c06_aux_C1E9a_int_cont (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε)
    (hAc : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε))
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (hAb2 : ∀ w, |deriv (A_eps p ε) w| ≤ (p + 1) * ε * |w|)
    (f g : ℝ → ℝ) (hddf : Differentiable ℝ (deriv f)) (hdg : Differentiable ℝ g)
    (hcddf : Continuous (deriv (deriv f))) (hcdg : Continuous (deriv g))
    (Y G0 G1 M2 : ℝ) (hY : 8 ≤ Y) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hM2 : 0 ≤ M2)
    (b0 : ∀ x, 0 ≤ x → |g x| ≤ G0) (b1 : ∀ x, 0 ≤ x → |deriv g x| ≤ G1)
    (b1f : ∀ x, 0 ≤ x → |deriv f x| ≤ G1)
    (b2 : ∀ x, Y / 2 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ M2) :
    ContinuousOn (fun y => ∫ z in Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y),
      c06_aux_E9pos_dF p ε f g y z) (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  set D := Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y) with hD
  have hDm : MeasurableSet D := measurableSet_Ioi.diff measurableSet_Icc
  set K := 8 * (p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hY0 : 0 < Y := by linarith
  have hAd : Differentiable ℝ (A_eps p ε) := hAc.differentiable (by simp)
  have hAcont : Continuous (A_eps p ε) := hAc.continuous
  have hdAcont : Continuous (deriv (A_eps p ε)) := hAc.continuous_deriv (by simp)
  have ha : 1 < 3 + p := by linarith
  have PT : ∀ y z, z ∈ D → Y / 2 + Y / 8 ≤ y → y ≤ 3 * Y - Y / 8 →
      |c06_aux_E9pos_dF p ε f g y z| ≤ K * ε * (|deriv (deriv f) y| + 1) * |y - z| ^ (-(3 + p)) := by
    intro y z hz h1 h2
    have hd := c06_aux_E9pos_dist Y y z hz h1 h2
    have hyz1 : 1 ≤ |y - z| := le_trans (by linarith) hd
    have hne : y ≠ z := fun e => by rw [e, sub_self, abs_zero] at hyz1; linarith
    have hz0 : 0 ≤ z := le_of_lt hz.1
    have hy0 : 0 ≤ y := by linarith
    have h0 : |g y - g z| ≤ 2 * G0 := by
      have := abs_sub (g y) (g z); linarith [b0 y hy0, b0 z hz0]
    exact (c06_aux_E9pos_pt p ε hp hε hAd hAb1 hAb2 f g y z G0 G1 (hddf y)
      (c06_aux_E9pos_secd g y z hne (hdg y)) hyz1 hG0 hG1 h0 (b1f y hy0) (b1 y hy0)
        (b1 z hz0)).2.2
  have hgc : Continuous g := hdg.continuous
  have mdF : ∀ y, Measurable (fun z => c06_aux_E9pos_dF p ε f g y z) := fun y => by
    unfold c06_aux_E9pos_dF
    have hs := c06_aux_E9pos_secm g hgc y
    have hk : Measurable (fun z : ℝ => |y - z| ^ (-(1 + p))) :=
      (measurable_const.sub measurable_id).abs.pow_const _
    exact ((measurable_const.mul ((hAcont.measurable.comp hs).sub measurable_const)).mul hk).add
      (((measurable_const.sub (measurable_deriv g)).mul ((hdAcont.measurable.comp hs).mul
        ((measurable_const.sub hs).div (measurable_const.sub measurable_id)))).mul hk) |>.add
      (((measurable_const.sub (measurable_deriv g)).mul
        ((hAcont.measurable.comp hs).sub measurable_const)).mul
        ((measurable_const.mul hk).div (measurable_const.sub measurable_id)))
  have hsub4 : ∀ y, 3 * Y / 4 ≤ y → y ≤ 5 * Y / 2 → D ⊆ {z | Y / 4 ≤ |y - z|} := by
    intro y h1 h2 z hz
    obtain ⟨-, hz2⟩ := hz
    simp only [mem_Icc, not_and_or, not_le] at hz2
    show Y / 4 ≤ |y - z|
    rcases hz2 with h | h
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  have hY4 : 0 < Y / 4 := by linarith
  intro y₀ hy₀
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : 3 * Y / 4 ≤ y₀ := hy₀.1.le
  have h2 : y₀ ≤ 5 * Y / 2 := hy₀.2.le
  have hD4 := hsub4 y₀ h1 h2
  have hT : IntegrableOn (fun z => |y₀ - z| ^ (-(3 + p))) D :=
    (c06_aux_tail2 (3 + p) (Y / 4) y₀ ha hY4).1.mono_set hD4
  have hball : ∀ y ∈ Metric.ball y₀ (Y / 8), Y / 2 + Y / 8 ≤ y ∧ y ≤ 3 * Y - Y / 8 ∧
      |y - y₀| < Y / 8 := fun y hy => by
    rw [Metric.mem_ball, Real.dist_eq] at hy
    have := abs_lt.mp hy
    exact ⟨by linarith, by linarith, hy⟩
  have hcmp : ∀ y ∈ Metric.ball y₀ (Y / 8), ∀ z ∈ D,
      |y - z| ^ (-(3 + p)) ≤ 2 ^ (3 + p) * |y₀ - z| ^ (-(3 + p)) := by
    intro y hy z hz
    obtain ⟨-, -, hyy⟩ := hball y hy
    have hz4 : Y / 4 ≤ |y₀ - z| := hD4 hz
    have hge : |y₀ - z| / 2 ≤ |y - z| := by
      have := abs_sub_abs_le_abs_sub (y₀ - z) (y - z)
      rw [show y₀ - z - (y - z) = -(y - y₀) by ring, abs_neg] at this
      linarith
    calc |y - z| ^ (-(3 + p)) ≤ (|y₀ - z| / 2) ^ (-(3 + p)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hge (by linarith)
      _ = 2 ^ (3 + p) * |y₀ - z| ^ (-(3 + p)) := by
          rw [Real.div_rpow (abs_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
          field_simp
  refine continuousAt_of_dominated (μ := volume.restrict D)
    (bound := fun z => K * ε * (M2 + 1) * (2 ^ (3 + p) * |y₀ - z| ^ (-(3 + p))))
    (Eventually.of_forall fun y => (mdF y).aestronglyMeasurable) ?_
    ((hT.const_mul (2 ^ (3 + p))).const_mul (K * ε * (M2 + 1))) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ (show (0 : ℝ) < Y / 8 by linarith)] with y hy
    refine (ae_restrict_iff' hDm).mpr (ae_of_all _ fun z hz => ?_)
    obtain ⟨ha1, ha2, -⟩ := hball y hy
    rw [Real.norm_eq_abs]
    refine (PT y z hz ha1 ha2).trans ?_
    have hm : |deriv (deriv f) y| + 1 ≤ M2 + 1 := by
      linarith [b2 y (by linarith) (by linarith)]
    have := hcmp y hy z hz
    have h0 : 0 ≤ |y - z| ^ (-(3 + p)) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) this h0 (by positivity)
  · refine (ae_restrict_iff' hDm).mpr (ae_of_all _ fun z hz => ?_)
    have hz4 : Y / 4 ≤ |y₀ - z| := hD4 hz
    have hne : y₀ ≠ z := fun e => by rw [e, sub_self, abs_zero] at hz4; linarith
    exact c06_aux_C1E9a_dFcont p ε hAc f g hddf.continuous hcddf hdg hcdg y₀ z hne

set_option maxHeartbeats 800000 in
/-- `ℰ_{9,+}` is `C¹` on `J_Y` (supports prop:approx_residual_positive). -/
theorem c06_E9_positive_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiffOn ℝ 1 (c06_E9_split_plus P.p ε (approximate_solution_family P.p R ε μ) Y)
          (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hplo := P.hp_lo
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hinv2 : 1 / P.p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have he1 : 1 / P.p - beta P.p ≤ 1 := by
    unfold beta
    rw [show 1 / P.p - (P.p + 1) / (2 * P.p) = (1 - P.p) / (2 * P.p) by field_simp; ring]
    rw [div_le_one (by positivity)]; linarith
  have he0 : 0 ≤ 1 / P.p - beta P.p := by linarith
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  obtain ⟨B, hB1, HB⟩ := c06_aux_chiY_bound
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  have hB0 : 0 ≤ B := by linarith
  set G0 : ℝ := B * C₀ with hG0
  set G1 : ℝ := 2 * B * C₀ with hG1
  have hG00 : 0 ≤ G0 := by positivity
  have hG10 : 0 ≤ G1 := by positivity
  set K := 8 * (P.p + 2) ^ 2 * (G0 + 1) ^ 2 * (G1 + 1) * (G1 + 2 * G0 + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  intro Y hY ε hε μ hμ
  set E : ℝ → ℝ := c06_E9_split_plus P.p ε (approximate_solution_family P.p R ε μ) Y with hEdef
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, h1, h2, -, h3⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  have hAb1 : ∀ w, 0 ≤ 1 - A_eps P.p ε w ∧ 1 - A_eps P.p ε w ≤ (P.p + 1) / 2 * ε * w ^ 2 :=
    fun w => (hAb w).1
  have hAb2 : ∀ w, |deriv (A_eps P.p ε) w| ≤ (P.p + 1) * ε * |w| := fun w => (hAb w).2.1
  set f := approximate_solution_family P.p R ε μ with hf
  set cf : ℝ → ℝ := fun x => res_chiY Y x * f x with hcf
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have ddf : Differentiable ℝ (deriv f) := by
    simpa using hfs.differentiable_iteratedDeriv 1 htop1
  have hχd : Differentiable ℝ (res_chiY Y) := (c06_aux_chiY_smooth Y).differentiable (by simp)
  have dcf : Differentiable ℝ cf := hχd.mul df
  have bf2 : ∀ x, 1 ≤ x → |deriv (deriv f) x| ≤ C₀ * x ^ (-beta P.p + 1 / P.p) := fun x hx => by
    have := (h3 x hx).2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have b2 : ∀ x, Y / 2 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y) := fun x hx hx3 => by
    have hx1 : 1 ≤ x := by linarith
    refine le_trans (bf2 x hx1) (mul_le_mul_of_nonneg_left ?_ hC₀0)
    have : x ^ (-beta P.p + 1 / P.p) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_one] at this; linarith
  have bf0 : ∀ x, 0 ≤ x → |f x| ≤ C₀ := fun x hx => le_trans (h2 x hx).1
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos (c06_aux_one_le_jb x)
      (by linarith)))
  have bf1 : ∀ x, |deriv f x| ≤ C₀ := fun x => (h1 x).1
  have bχ0 : ∀ x, |res_chiY Y x| ≤ B := fun x => by
    have := HB Y hY0 0 (by norm_num) x
    simpa using this
  have bχ1 : ∀ x, |deriv (res_chiY Y) x| ≤ B := fun x => by
    have := HB Y hY0 1 (by norm_num) x
    rw [iteratedDeriv_one] at this
    refine this.trans ?_
    have : Y ^ (-((1 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hY1 (by norm_num)
    nlinarith
  have b0f : ∀ x, 0 ≤ x → |f x| ≤ G0 := fun x hx =>
    (bf0 x hx).trans (by rw [hG0]; nlinarith)
  have b1f : ∀ x, 0 ≤ x → |deriv f x| ≤ G1 := fun x _ =>
    (bf1 x).trans (by rw [hG1]; nlinarith)
  have b0c : ∀ x, 0 ≤ x → |cf x| ≤ G0 := fun x hx => by
    simp only [hcf, abs_mul]
    exact mul_le_mul (bχ0 x) (bf0 x hx) (abs_nonneg _) hB0
  have b1c : ∀ x, 0 ≤ x → |deriv cf x| ≤ G1 := fun x hx => by
    have hd : deriv cf x = deriv (res_chiY Y) x * f x + res_chiY Y x * deriv f x :=
      ((hχd x).hasDerivAt.mul (df x).hasDerivAt).deriv
    rw [hd]
    calc _ ≤ |deriv (res_chiY Y) x * f x| + |res_chiY Y x * deriv f x| := abs_add_le _ _
      _ ≤ B * C₀ + B * C₀ := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (bχ1 x) (bf0 x hx) (abs_nonneg _) hB0)
            (mul_le_mul (bχ0 x) (bf1 x) (abs_nonneg _) hB0)
      _ = G1 := by rw [hG1]; ring
  have hM2 : 0 ≤ C₀ * (3 * Y) := by positivity
  obtain ⟨Hf1, Hf2⟩ := c06_aux_E9pos_int P.p ε hp0 hε0 hAc hAb1 hAb2 f f ddf df Y G0 G1
    (C₀ * (3 * Y)) hY8 hG00 hG10 hM2 b0f b1f b1f b2
  obtain ⟨Hc1, Hc2⟩ := c06_aux_E9pos_int P.p ε hp0 hε0 hAc hAb1 hAb2 f cf ddf dcf Y G0 G1
    (C₀ * (3 * Y)) hY8 hG00 hG10 hM2 b0c b1c b1f b2
  set D := Ioi (0 : ℝ) \ Icc (Y / 2) (3 * Y) with hD
  have hEq : ∀ y ∈ Ioo (3 * Y / 4) (5 * Y / 2), E y = calpha P.p *
      ((∫ z in D, c06_aux_E9pos_F P.p ε f f y z) - ∫ z in D, c06_aux_E9pos_F P.p ε f cf y z) := by
    intro y hy
    rw [← integral_sub (Hf1 y hy).1 (Hc1 y hy).1]
    show calpha P.p * _ = _
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [c06_aux_E9pos_F]
    rw [Real.rpow_neg (abs_nonneg _), add_comm 1 P.p]
    simp only [hcf]
    ring
  have hderiv : ∀ y ∈ Ioo (3 * Y / 4) (5 * Y / 2), HasDerivAt E (calpha P.p *
      ((∫ z in D, c06_aux_E9pos_dF P.p ε f f y z) - ∫ z in D, c06_aux_E9pos_dF P.p ε f cf y z)) y :=
    fun y hy => (((Hf1 y hy).2.sub (Hc1 y hy).2).const_mul (calpha P.p)).congr_of_eventuallyEq
      (by filter_upwards [isOpen_Ioo.mem_nhds hy] with x hx using hEq x hx)
  have htop2 : ((2 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
  have hcddf : Continuous (deriv (deriv f)) := by
    have := hfs.continuous_iteratedDeriv 2 htop2.le
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this
  have hcdf : Continuous (deriv f) := hfs.continuous_deriv (by simp)
  have hcdcf : Continuous (deriv cf) :=
    ((c06_aux_chiY_smooth Y).mul hfs).continuous_deriv (by simp)
  have Cf := c06_aux_C1E9a_int_cont P.p ε hp0 hε0 hAc hAb1 hAb2 f f ddf df hcddf hcdf Y G0 G1
    (C₀ * (3 * Y)) hY8 hG00 hG10 hM2 b0f b1f b1f b2
  have Cc := c06_aux_C1E9a_int_cont P.p ε hp0 hε0 hAc hAb1 hAb2 f cf ddf dcf hcddf hcdcf Y G0 G1
    (C₀ * (3 * Y)) hY8 hG00 hG10 hM2 b0c b1c b1f b2
  have hcont : ContinuousOn (fun y => calpha P.p *
      ((∫ z in D, c06_aux_E9pos_dF P.p ε f f y z) - ∫ z in D, c06_aux_E9pos_dF P.p ε f cf y z))
      (Ioo (3 * Y / 4) (5 * Y / 2)) := continuousOn_const.mul (Cf.sub Cc)
  have hJ : IsOpen (Ioo (3 * Y / 4) (5 * Y / 2)) := isOpen_Ioo
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num]
  refine (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨fun y hy =>
    (hderiv y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  exact contDiffOn_zero.mpr (hcont.congr fun y hy => (hderiv y hy).deriv)

/-- Helper for lem:c06_E9_I3 (C¹): continuity of the derivative integral. -/
theorem c06_aux_C1E9a_I3_cont (p ε c : ℝ) (hc : c = (p + 1) / 2) (hp : 0 < p)
    (hε0 : 0 ≤ ε) (f : ℝ → ℝ) (df : Differentiable ℝ f) (ddf : Differentiable ℝ (deriv f)) (hcddf : Continuous (deriv (deriv f)))
    (hAc : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε))
    (hAb1 : ∀ w, 0 ≤ 1 - A_eps p ε w ∧ 1 - A_eps p ε w ≤ (p + 1) / 2 * ε * w ^ 2)
    (hAb2 : ∀ w, |deriv (A_eps p ε) w| ≤ (p + 1) * ε * |w|)
    (C₀ Y : ℝ) (hC₀ : 0 ≤ C₀) (hY : 8 ≤ Y)
    (b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀) (b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀)
    (b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y))
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2)) :
    ContinuousAt (fun y => ∫ z in Iio (0 : ℝ), (deriv (deriv f) y * (A_eps p ε (f y / (y - z)) - 1) -
        (1 + p) * deriv f y * (1 / (y - z)) * (A_eps p ε (f y / (y - z)) - 1) +
        deriv f y * deriv (A_eps p ε) (f y / (y - z)) *
          (deriv f y * (1 / (y - z)) - f y * (1 / (y - z)) ^ 2)) *
          (y - z) ^ (-(1 + p))) y₀ := by
  have dA : Differentiable ℝ (A_eps p ε) := hAc.differentiable (by simp)
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  set G : ℝ → ℝ → ℝ := fun x z => deriv f x / (x - z) ^ (1 + p) *
    (A_eps p ε (f x / (x - z)) - 1) with hG
  set G' : ℝ → ℝ → ℝ := fun x z =>
    (deriv (deriv f) x * (A_eps p ε (f x / (x - z)) - 1) -
      (1 + p) * deriv f x * (1 / (x - z)) * (A_eps p ε (f x / (x - z)) - 1) +
      deriv f x * deriv (A_eps p ε) (f x / (x - z)) *
        (deriv f x * (1 / (x - z)) - f x * (1 / (x - z)) ^ 2)) * (x - z) ^ (-(1 + p)) with hG'
  have mA : Measurable (A_eps p ε) := hAc.continuous.measurable
  have mdA : Measurable (deriv (A_eps p ε)) := measurable_deriv _
  have mG : ∀ x, AEStronglyMeasurable (G x) (volume.restrict (Iio 0)) := fun x => by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hG]
    fun_prop
  have mG' : ∀ x, AEStronglyMeasurable (G' x) (volume.restrict (Iio 0)) := fun x => by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hG']
    fun_prop
  set x₁ := 5 * Y / 8 with hx₁
  have hx₁1 : 1 ≤ x₁ := by rw [hx₁]; linarith
  set M : ℝ := c * C₀ ^ 2 * (C₀ * (3 * Y)) + (1 + p) * c * C₀ * C₀ ^ 2 + 2 * c * C₀ ^ 2 * C₀ +
    2 * c * C₀ * C₀ ^ 2 with hM
  have hball : ∀ x ∈ Metric.ball y₀ (Y / 8), x₁ ≤ x ∧ x ≤ 3 * Y := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    constructor <;> linarith [hy₀.1, hy₀.2]
  have hbd : ∀ x ∈ Metric.ball y₀ (Y / 8), ∀ z, z < 0 → |G' x z| ≤
      ε * M * (x₁ - z) ^ (-(3 + p)) := by
    intro x hx z hz
    obtain ⟨hx1, hx2⟩ := hball x hx
    have hx1' : 1 ≤ x := le_trans hx₁1 hx1
    refine le_trans (c06_aux_I3_bG' p ε c hc hp hε0 f hAb1 hAb2 x z hx1' hz) ?_
    have e0 := b0 x hx1'
    have e1 := b1 x hx1'
    have e2 := b2 x hx1' hx2
    have ef : f x ^ 2 ≤ C₀ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e0 2
    have hs : 0 < x₁ - z := by linarith
    have hmono : (x - z) ^ (-(3 + p)) ≤ (x₁ - z) ^ (-(3 + p)) :=
      Real.rpow_le_rpow_of_nonpos hs (by linarith) (by linarith)
    have a1 : c * f x ^ 2 * |deriv (deriv f) x| ≤ c * C₀ ^ 2 * (C₀ * (3 * Y)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ef hc0) e2 (abs_nonneg _) (by positivity)
    have a2 : (1 + p) * c * |deriv f x| * f x ^ 2 ≤ (1 + p) * c * C₀ * C₀ ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity)) ef (sq_nonneg _) (by positivity)
    have a3 : 2 * c * |deriv f x| ^ 2 * |f x| ≤ 2 * c * C₀ ^ 2 * C₀ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) e1 2)
        (by positivity)) e0 (abs_nonneg _) (by positivity)
    have a4 : 2 * c * |deriv f x| * f x ^ 2 ≤ 2 * c * C₀ * C₀ ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity)) ef (sq_nonneg _) (by positivity)
    have hMx : c * f x ^ 2 * |deriv (deriv f) x| + (1 + p) * c * |deriv f x| * f x ^ 2 +
        2 * c * |deriv f x| ^ 2 * |f x| + 2 * c * |deriv f x| * f x ^ 2 ≤ M := by
      rw [hM]; linarith
    have hM0 : 0 ≤ c * f x ^ 2 * |deriv (deriv f) x| + (1 + p) * c * |deriv f x| * f x ^ 2 +
        2 * c * |deriv f x| ^ 2 * |f x| + 2 * c * |deriv f x| * f x ^ 2 := by positivity
    have hp0'' := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x - z) (-(3 + p))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hMx hε0) hmono hp0''
      (mul_nonneg hε0 (le_trans hM0 hMx))
  have hAc' : Continuous (A_eps p ε) := hAc.continuous
  have hdAc : Continuous (deriv (A_eps p ε)) := hAc.continuous_deriv (by simp)
  refine continuousAt_of_dominated (μ := volume.restrict (Iio 0))
    (bound := fun z => ε * M * (x₁ - z) ^ (-(3 + p)))
    (Eventually.of_forall mG') ?_
    (((c06_aux_tail1 (3 + p) x₁ (by linarith) (by linarith)).1).const_mul _) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ (show (0 : ℝ) < Y / 8 by linarith)] with x hx
    exact (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => by
      rw [Real.norm_eq_abs]; exact hbd x hx z hz)
  · refine (ae_restrict_iff' measurableSet_Iio).mpr (ae_of_all _ fun z hz => ?_)
    have hz0 : z < 0 := hz
    have hyz : y₀ - z ≠ 0 := by have := hy₀.1; intro h; linarith
    have cl : ContinuousAt (fun y : ℝ => y - z) y₀ :=
      (continuous_id.sub continuous_const).continuousAt
    have cf : ContinuousAt f y₀ := df.continuous.continuousAt
    have cdf : ContinuousAt (deriv f) y₀ := ddf.continuous.continuousAt
    have cu : ContinuousAt (fun y => f y / (y - z)) y₀ := cf.div cl hyz
    have cA : ContinuousAt (fun y => A_eps p ε (f y / (y - z))) y₀ :=
      ContinuousAt.comp (g := A_eps p ε) hAc'.continuousAt cu
    have cdA : ContinuousAt (fun y => deriv (A_eps p ε) (f y / (y - z))) y₀ :=
      ContinuousAt.comp (g := deriv (A_eps p ε)) hdAc.continuousAt cu
    have ci : ContinuousAt (fun y : ℝ => 1 / (y - z)) y₀ := continuousAt_const.div cl hyz
    have ck : ContinuousAt (fun y : ℝ => (y - z) ^ (-(1 + p))) y₀ :=
      cl.rpow_const (Or.inl hyz)
    exact (((hcddf.continuousAt.mul (cA.sub continuousAt_const)).sub
      (((continuousAt_const.mul cdf).mul ci).mul (cA.sub continuousAt_const))).add
      ((cdf.mul cdA).mul ((cdf.mul ci).sub (cf.mul (ci.pow 2))))).mul ck

/-- `ℐ₃` is `C¹` on `J_Y` (supports prop:approx_residual_positive). -/
theorem c06_E9_I3_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiffOn ℝ 1 (c06_E9_split_I3 P.p ε (approximate_solution_family P.p R ε μ))
          (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hplo := P.hp_lo
  have h2b := c06_aux_two_beta P.p hp0
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have he1 : 1 / P.p - beta P.p ≤ 1 := by
    unfold beta
    rw [show 1 / P.p - (P.p + 1) / (2 * P.p) = (1 - P.p) / (2 * P.p) by field_simp; ring]
    rw [div_le_one (by positivity)]; linarith
  have he0 : 0 ≤ 1 / P.p - beta P.p := by linarith
  obtain ⟨R₀, hR₀, HP⟩ := c06_profile_consequences P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨CA, -, HA⟩ := c06_A_eps_bounds P.p hp0 hp1
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨C₀, hC₀, HC⟩ := HP R hR
  have hC₀0 : 0 ≤ C₀ := by linarith
  set c : ℝ := (P.p + 1) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  set K₁ : ℝ := (c + (1 + P.p) * c + 2 * c + 2 * c) * (2 * C₀ ^ 3) with hK₁
  intro Y hY ε hε μ hμ
  set E : ℝ → ℝ := c06_E9_split_I3 P.p ε (approximate_solution_family P.p R ε μ) with hE
  have hRone : 1 ≤ R := le_trans hR₀ hR
  have hY8 : 8 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : ε ≤ 1 := le_trans hε.2 hε₀1
  obtain ⟨hfs, -, -, -, h3⟩ := HC ε hε μ hμ
  obtain ⟨hAc, hAb, -, -⟩ := HA ε ⟨hε0, hε1⟩
  have hAb1 : ∀ w, 0 ≤ 1 - A_eps P.p ε w ∧ 1 - A_eps P.p ε w ≤ (P.p + 1) / 2 * ε * w ^ 2 :=
    fun w => (hAb w).1
  have hAb2 : ∀ w, |deriv (A_eps P.p ε) w| ≤ (P.p + 1) * ε * |w| := fun w => (hAb w).2.1
  set f := approximate_solution_family P.p R ε μ with hf
  have htop1 : ((1 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 1)
  have df : Differentiable ℝ f := hfs.differentiable (by simp)
  have ddf : Differentiable ℝ (deriv f) := by
    simpa using hfs.differentiable_iteratedDeriv 1 htop1
  have bf0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ * x ^ (-P.p) := fun x hx => (h3 x hx).1
  have bf1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ * x ^ (-beta P.p) := fun x hx => by
    simpa using (h3 x hx).2 0 (by norm_num)
  have bf2 : ∀ x, 1 ≤ x → |deriv (deriv f) x| ≤ C₀ * x ^ (-beta P.p + 1 / P.p) := fun x hx => by
    have := (h3 x hx).2 1 (by norm_num)
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at this
    simpa using this
  have b0 : ∀ x, 1 ≤ x → |f x| ≤ C₀ := fun x hx => le_trans (bf0 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)))
  have b1 : ∀ x, 1 ≤ x → |deriv f x| ≤ C₀ := fun x hx => le_trans (bf1 x hx)
    (mul_le_of_le_one_right hC₀0 (Real.rpow_le_one_of_one_le_of_nonpos hx (by
      have : 0 < beta P.p := by unfold beta; positivity
      linarith)))
  have b2 : ∀ x, 1 ≤ x → x ≤ 3 * Y → |deriv (deriv f) x| ≤ C₀ * (3 * Y) := fun x hx hx3 => by
    refine le_trans (bf2 x hx) (mul_le_mul_of_nonneg_left ?_ hC₀0)
    have : x ^ (-beta P.p + 1 / P.p) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    rw [Real.rpow_one] at this; linarith
  have hEdef : E = fun y => -(calpha P.p * ∫ z in Iio (0 : ℝ), deriv f y / (y - z) ^ (1 + P.p) *
      (A_eps P.p ε (f y / (y - z)) - 1)) := rfl
  have hderiv := fun y₀ (hy₀ : y₀ ∈ Ioo (3 * Y / 4) (5 * Y / 2)) =>
    ((c06_aux_I3_hasDeriv_int P.p ε c hc hp0 hε0 f df ddf hAc hAb1 hAb2 C₀ Y hC₀0 hY8 b0 b1 b2
      y₀ hy₀).const_mul (calpha P.p)).neg
  have htop2 : ((2 : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
  have hcddf : Continuous (deriv (deriv f)) := by
    have := hfs.continuous_iteratedDeriv 2 htop2.le
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this
  have hJ : IsOpen (Ioo (3 * Y / 4) (5 * Y / 2)) := isOpen_Ioo
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num]
  refine (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨fun y hy => by
    rw [hEdef]; exact (hderiv y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  refine contDiffOn_zero.mpr fun y hy => ?_
  refine ContinuousAt.continuousWithinAt ?_
  have hc := ((c06_aux_C1E9a_I3_cont P.p ε c hc hp0 hε0 f df ddf hcddf hAc hAb1 hAb2 C₀ Y hC₀0
    hY8 b0 b1 b2 y hy).const_mul (calpha P.p)).neg
  refine hc.congr ?_
  filter_upwards [hJ.mem_nhds hy] with x hx
  rw [hEdef]; exact (hderiv x hx).deriv.symm

/-! ### C¹ of ℰ₉ on J_Y -/
/-- Proposed blueprint node `lem:c06_E9_C1` (supports prop:approx_residual_positive):
`ℰ₉^Y` is `C¹` on `J_Y = (3Y/4, 5Y/2)`. -/
theorem c06_E9_C1 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀,
      ∀ μ ∈ Bbar P.p δ,
        ContDiffOn ℝ 1 (residual_decomposition_E9 P.p R ε μ Y) (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  obtain ⟨R0, hR0, Hs⟩ := c06_E9_split P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R1, hR1, Hp⟩ := c06_E9_positive_C1 P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R2, hR2, H1⟩ := c06_E9_I1_C1 P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R3, hR3, H2⟩ := c06_E9_I2_C1 P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R4, hR4, H3⟩ := c06_E9_I3_C1 P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨max R0 (max R1 (max R2 (max R3 R4))), le_trans hR0 (le_max_left _ _),
    fun R hR Y hY ε hε μ hμ => ?_⟩
  simp only [max_le_iff] at hR
  obtain ⟨a0, a1, a2, a3, a4⟩ := hR
  have hsum : ContDiffOn ℝ 1 (fun y =>
      c06_E9_split_plus P.p ε (approximate_solution_family P.p R ε μ) Y y +
      c06_E9_split_I1 P.p ε (approximate_solution_family P.p R ε μ) y +
      c06_E9_split_I2 P.p ε (approximate_solution_family P.p R ε μ) y +
      c06_E9_split_I3 P.p ε (approximate_solution_family P.p R ε μ) y)
      (Ioo (3 * Y / 4) (5 * Y / 2)) :=
    (((Hp R a1 Y hY ε hε μ hμ).add (H1 R a2 Y hY ε hε μ hμ)).add
      (H2 R a3 Y hY ε hε μ hμ)).add (H3 R a4 Y hY ε hε μ hμ)
  refine hsum.congr (fun y hy => ?_)
  exact (Hs R a0 Y hY ε hε μ hμ y hy).1

-- Smallness: `hε₀s : ε₀ ≤ c06_eps0_star P δ` (see the module docstring).
/-- Blueprint: lem:approx_E9.  Control of `ℰ₉` on `[Y,2Y]`. -/
theorem approx_E9 (P : parameters) (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) (hε₀s : ε₀ ≤ c06_eps0_star P δ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 8 * R ≤ Y → ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        DifferentiableOn ℝ (residual_decomposition_E9 P.p R ε μ Y) (Icc Y (2 * Y)) ∧
        ∀ y ∈ Icc Y (2 * Y), ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (residual_decomposition_E9 P.p R ε μ Y) y| ≤
            C * ε * jb y ^ (-P.p - 2 + j / P.p) := by
  obtain ⟨R₀, hR₀, Hs⟩ := c06_E9_split P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₁, hR₁, Hp⟩ := c06_E9_positive P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₂, hR₂, H1⟩ := c06_E9_I1 P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₃, hR₃, H2⟩ := c06_E9_I2 P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  obtain ⟨R₄, hR₄, H3⟩ := c06_E9_I3 P ε₀ δ hε₀ hε₀1 hδ hδμ hε₀s
  refine ⟨max (max R₀ R₁) (max R₂ (max R₃ R₄)),
    le_trans hR₀ (le_trans (le_max_left _ _) (le_max_left _ _)), fun R hR => ?_⟩
  have hR0 : R₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR1 : R₁ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR2 : R₂ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hR3 : R₃ ≤ R := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hR
  have hR4 : R₄ ≤ R := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hR
  have hRone : 1 ≤ R := le_trans hR₀ hR0
  obtain ⟨Cp, hCp, bp⟩ := Hp R hR1
  obtain ⟨C1, hC1, b1⟩ := H1 R hR2
  obtain ⟨C2, hC2, b2⟩ := H2 R hR3
  obtain ⟨C3, hC3, b3⟩ := H3 R hR4
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  have hinv1 : 1 < 1 / P.p := by rw [lt_div_iff₀ hp0]; linarith
  have hinv2 : 1 / P.p < 2 := by rw [div_lt_iff₀ hp0]; linarith
  refine ⟨(3 : ℝ) ^ (P.p + 2) * (Cp + C1 + C2 + C3), by positivity, ?_⟩
  intro Y hY ε hε μ hμ
  have hε0 : 0 ≤ ε := hε.1
  have hY1 : 1 ≤ Y := by linarith
  set f := approximate_solution_family P.p R ε μ with hf
  set F : ℝ → ℝ := fun y => c06_E9_split_plus P.p ε f Y y + c06_E9_split_I1 P.p ε f y +
    c06_E9_split_I2 P.p ε f y + c06_E9_split_I3 P.p ε f y with hF
  have hJ : IsOpen (Ioo (3 * Y / 4) (5 * Y / 2)) := isOpen_Ioo
  have hsub : Icc Y (2 * Y) ⊆ Ioo (3 * Y / 4) (5 * Y / 2) := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have heq : ∀ y ∈ Icc Y (2 * Y), residual_decomposition_E9 P.p R ε μ Y =ᶠ[nhds y] F := by
    intro y hy
    filter_upwards [hJ.mem_nhds (hsub hy)] with x hx
    exact (Hs R hR0 Y hY ε hε μ hμ x hx).1
  obtain ⟨hdp, bp'⟩ := bp Y hY ε hε μ hμ
  obtain ⟨hd1, b1'⟩ := b1 Y hY ε hε μ hμ
  obtain ⟨hd2, b2'⟩ := b2 Y hY ε hε μ hμ
  obtain ⟨hd3, b3'⟩ := b3 Y hY ε hε μ hμ
  have hdF : ∀ y ∈ Icc Y (2 * Y), DifferentiableAt ℝ (c06_E9_split_plus P.p ε f Y) y ∧
      DifferentiableAt ℝ (c06_E9_split_I1 P.p ε f) y ∧
      DifferentiableAt ℝ (c06_E9_split_I2 P.p ε f) y ∧
      DifferentiableAt ℝ (c06_E9_split_I3 P.p ε f) y := by
    intro y hy
    have hn := hJ.mem_nhds (hsub hy)
    exact ⟨hdp.differentiableAt hn, hd1.differentiableAt hn, hd2.differentiableAt hn,
      hd3.differentiableAt hn⟩
  have hdFF : ∀ y ∈ Icc Y (2 * Y), DifferentiableAt ℝ F y := by
    intro y hy
    obtain ⟨a, b, c, d⟩ := hdF y hy
    exact ((a.add b).add c).add d
  refine ⟨fun y hy => ((heq y hy).differentiableAt_iff.mpr (hdFF y hy)).differentiableWithinAt,
    ?_⟩
  intro y hy j hj
  have hYp : (0 : ℝ) ≤ Y ^ (-(P.p + 2)) := Real.rpow_nonneg (by linarith) _
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero]
    rw [show -P.p - 2 = -(P.p + 2) by ring]
    apply c06_aux_conv _ _ _ _ Y y _ (by positivity) hε0 (by linarith) le_rfl hY1 hy.1 hy.2
    rw [(heq y hy).eq_of_nhds]
    have e0 := bp' y hy 0 (by norm_num)
    have e1 := (b1' y hy).1
    have e2 := b2' y hy 0 (by norm_num)
    have e3 := b3' y hy 0 (by norm_num)
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at e0 e2 e3
    rw [show -P.p - 2 = -(P.p + 2) by ring] at e0 e1 e2 e3
    simp only [hF]
    calc _ ≤ |c06_E9_split_plus P.p ε f Y y| + |c06_E9_split_I1 P.p ε f y| +
          |c06_E9_split_I2 P.p ε f y| + |c06_E9_split_I3 P.p ε f y| := by
          have := abs_add_le (c06_E9_split_plus P.p ε f Y y + c06_E9_split_I1 P.p ε f y +
            c06_E9_split_I2 P.p ε f y) (c06_E9_split_I3 P.p ε f y)
          have := abs_add_le (c06_E9_split_plus P.p ε f Y y + c06_E9_split_I1 P.p ε f y)
            (c06_E9_split_I2 P.p ε f y)
          have := abs_add_le (c06_E9_split_plus P.p ε f Y y) (c06_E9_split_I1 P.p ε f y)
          linarith
      _ ≤ (Cp + C1 + C2 + C3) * ε * Y ^ (-(P.p + 2)) := by linarith
  · simp only [iteratedDeriv_one, Nat.cast_one]
    rw [show -P.p - 2 + 1 / P.p = -(P.p + 2 - 1 / P.p) by ring]
    apply c06_aux_conv _ _ _ _ Y y _ (by positivity) hε0 (by linarith) (by linarith) hY1 hy.1 hy.2
    rw [(heq y hy).deriv_eq]
    obtain ⟨a, b, c, d⟩ := hdF y hy
    have hsum : deriv F y = deriv (c06_E9_split_plus P.p ε f Y) y +
        deriv (c06_E9_split_I1 P.p ε f) y + deriv (c06_E9_split_I2 P.p ε f) y +
        deriv (c06_E9_split_I3 P.p ε f) y := by
      exact (((a.hasDerivAt.add b.hasDerivAt).add c.hasDerivAt).add d.hasDerivAt).deriv
    rw [hsum]
    have e0 := bp' y hy 1 le_rfl
    have e1 := (b1' y hy).2
    have e2 := b2' y hy 1 le_rfl
    have e3 := b3' y hy 1 le_rfl
    simp only [iteratedDeriv_one, Nat.cast_one] at e0 e2 e3
    rw [show -P.p - 2 + 1 / P.p = -(P.p + 2 - 1 / P.p) by ring] at e0 e2 e3
    have hYc : Y ^ (-P.p - 3) ≤ Y ^ (-(P.p + 2 - 1 / P.p)) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have : C1 * ε * Y ^ (-P.p - 3) ≤ C1 * ε * Y ^ (-(P.p + 2 - 1 / P.p)) := by gcongr
    calc _ ≤ |deriv (c06_E9_split_plus P.p ε f Y) y| + |deriv (c06_E9_split_I1 P.p ε f) y| +
          |deriv (c06_E9_split_I2 P.p ε f) y| + |deriv (c06_E9_split_I3 P.p ε f) y| := by
          have := abs_add_le (deriv (c06_E9_split_plus P.p ε f Y) y +
            deriv (c06_E9_split_I1 P.p ε f) y + deriv (c06_E9_split_I2 P.p ε f) y)
            (deriv (c06_E9_split_I3 P.p ε f) y)
          have := abs_add_le (deriv (c06_E9_split_plus P.p ε f Y) y +
            deriv (c06_E9_split_I1 P.p ε f) y) (deriv (c06_E9_split_I2 P.p ε f) y)
          have := abs_add_le (deriv (c06_E9_split_plus P.p ε f Y) y)
            (deriv (c06_E9_split_I1 P.p ε f) y)
          linarith
      _ ≤ (Cp + C1 + C2 + C3) * ε * Y ^ (-(P.p + 2 - 1 / P.p)) := by linarith

end GSQG
