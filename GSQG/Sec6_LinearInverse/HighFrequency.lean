import GSQG.Definitions
import GSQG.Sec3_FixedPoint.FixedPointArgument
import GSQG.Sec6_LinearInverse.ConjugationAndLowFrequency

/-!
# §6.4: linear inverse — high frequency estimate and assembly (blueprint ch. 09)

Statements and proofs for blueprint chapter `09_linear_high.tex` (this file contains no `sorry`;
the `c09_ext_*` lemmas are wrappers around imported results of `FixedPointArgument` and
`ConjugationAndLowFrequency`).

Conventions: `p` is a real with `3/4 < p < 1` (hypotheses `hp`, `hp1`), `γ` admissible
(`admissibleGamma p γ`), `j : ℕ` with `j ≤ 2`.  The cutoff `χ` of the chapter is the shared `rho`.
`T_+` (`c09_T_plus`) is the inverse transform of `𝟙_{ξ>0} (1-ρ) m_G`, i.e. the `ξ > 0` part of the
symbol `(1-ρ) m_G` of the shared `T_high`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal FourierTransform ContDiff Topology

noncomputable section

namespace GSQG

/-! ### Weights -/

/-- Blueprint: def:c09_weights.  `w_{γ,j}(y) = ⟨y⟩^{-γ+j/p}` for `y ≥ 0`, `⟨y⟩^{-γ-j}` for `y < 0`. -/
def c09_weights (p γ : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  if 0 ≤ y then jb y ^ (-γ + (j : ℝ) / p) else jb y ^ (-γ - (j : ℝ))

/-- Blueprint: def:c09_weights.  `w_E(z) = ⟨z⟩^{-1}` for `z ≤ 0`, `⟨z⟩^{(1-p)/(2p)}` for `z > 0`. -/
def c09_weights_E (p : ℝ) (z : ℝ) : ℝ :=
  if z ≤ 0 then jb z ^ (-1 : ℝ) else jb z ^ ((1 - p) / (2 * p))

/-- `⟨y⟩ > 0`. -/
theorem c09_aux_jb_pos (y : ℝ) : 0 < jb y := by
  unfold jb; positivity

/-- `⟨y⟩ ≥ 1`. -/
theorem c09_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := by
  unfold jb; exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg y])

/-- `⟨·⟩` is continuous. -/
theorem c09_aux_jb_continuous : Continuous jb := by
  unfold jb; fun_prop

/-- `⟨y⟩ ≤ ⟨Y⟩` when `|y| ≤ Y`. -/
theorem c09_aux_jb_mono {y Y : ℝ} (h : |y| ≤ Y) : jb y ≤ jb Y := by
  unfold jb
  apply Real.sqrt_le_sqrt
  have : y ^ 2 ≤ Y ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) h 2
  linarith

/-- The weights `w_{γ,j}` are continuous. -/
theorem c09_aux_weights_continuous (p γ : ℝ) (j : ℕ) : Continuous (c09_weights p γ j) := by
  unfold c09_weights
  have hc : ∀ c : ℝ, Continuous fun y => jb y ^ c := fun c =>
    c09_aux_jb_continuous.rpow_const (fun y => Or.inl (c09_aux_jb_pos y).ne')
  refine Continuous.if_le (hc _) (hc _) continuous_const continuous_id ?_
  intro y hy
  subst hy
  simp [jb]

/-- The weights `w_{γ,j}` are positive. -/
theorem c09_aux_weights_pos (p γ : ℝ) (j : ℕ) (y : ℝ) : 0 < c09_weights p γ j y := by
  have := c09_aux_jb_pos y
  unfold c09_weights; split_ifs <;> positivity

/-- A continuous inequality holding a.e. holds everywhere. -/
private theorem c09_aux_ae_le_everywhere {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ᵐ y, f y ≤ g y) : ∀ y, f y ≤ g y := by
  by_contra hc
  simp only [not_forall, not_le] at hc
  obtain ⟨y, hy⟩ := hc
  have hS : IsOpen {y | g y < f y} := isOpen_lt hg hf
  have h0 : volume {y | g y < f y} = 0 := by
    have := ae_iff.mp h
    simpa only [not_le] using this
  have := (hS.measure_eq_zero_iff volume).mp h0
  have hy' : y ∈ {y | g y < f y} := hy
  rw [this] at hy'
  exact hy'

/-- From a bound on an essential supremum of `ofReal ∘ F` to an a.e. bound on `F`. -/
private theorem c09_aux_ae_of_essSup_le {μ : Measure ℝ} {F : ℝ → ℝ} {E : ℝ≥0∞}
    (hE : essSup (fun y => ENNReal.ofReal (F y)) μ ≤ E) (hfin : E ≠ ⊤) :
    ∀ᵐ y ∂μ, F y ≤ E.toReal := by
  filter_upwards [ENNReal.ae_le_essSup (fun y => ENNReal.ofReal (F y))] with y hy
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp (hy.trans hE)

/-- `x^{e₁}(x^{e₂} a) ≤ N` implies `a ≤ N x^{-e₁-e₂}` for `x > 0`. -/
private theorem c09_aux_rpow_div {x : ℝ} (hx : 0 < x) (e1 e2 a N : ℝ)
    (h : x ^ e1 * (x ^ e2 * a) ≤ N) : a ≤ N * x ^ (-e1 - e2) := by
  have ha : a = x ^ (-e1 - e2) * (x ^ e1 * (x ^ e2 * a)) := by
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hx, ← Real.rpow_add hx,
      show -e1 - e2 + e1 + e2 = 0 by ring, Real.rpow_zero, one_mul]
  rw [ha]
  calc x ^ (-e1 - e2) * (x ^ e1 * (x ^ e2 * a)) ≤ x ^ (-e1 - e2) * N :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le _)
    _ = N * x ^ (-e1 - e2) := by ring
    _ = N * x ^ (-e1 - e2) := rfl

/-- Pointwise a.e. bounds from the `X_γ` norm. -/
private theorem c09_aux_X_ae (p γ : ℝ) (r : ℝ → ℝ) (hr : r ∈ X_gamma p γ) :
    (∀ᵐ y, 0 ≤ y → |r y| ≤ xNorm p γ r * jb y ^ (-γ) ∧
      |deriv r y| ≤ xNorm p γ r * jb y ^ (-γ + 1 / p) ∧
      |deriv (deriv r) y| ≤ xNorm p γ r * jb y ^ (-γ + 2 / p)) ∧
    (∀ᵐ y, y < 0 → |r y| ≤ xNorm p γ r * jb y ^ (-γ) ∧
      |deriv r y| ≤ xNorm p γ r * jb y ^ (-γ - 1) ∧
      |deriv (deriv r) y| ≤ xNorm p γ r * jb y ^ (-γ - 2)) := by
  have hfin : X_gamma_norm p γ r ≠ ⊤ := hr.2.ne
  unfold X_gamma_norm at hfin
  set e1 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv r) y‖))) (volume.restrict (Ici 0)) with he1
  set e2 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0)) with he2
  have hN : xNorm p γ r = (e1 + e2).toReal := rfl
  have h1 := c09_aux_ae_of_essSup_le (μ := volume.restrict (Ici 0)) (le_self_add : e1 ≤ e1 + e2) hfin
  have h2 := c09_aux_ae_of_essSup_le (μ := volume.restrict (Iic 0)) (le_add_self : e2 ≤ e1 + e2) hfin
  rw [← hN] at h1 h2
  rw [Measure.restrict_congr_set Iio_ae_eq_Iic.symm] at h2
  rw [ae_restrict_iff' measurableSet_Ici] at h1
  rw [ae_restrict_iff' measurableSet_Iio] at h2
  constructor
  · filter_upwards [h1] with y hy hy0
    have hb := hy hy0
    simp only [Real.norm_eq_abs] at hb
    have hj := c09_aux_jb_pos y
    have a1 : 0 ≤ |r y| := abs_nonneg _
    have a2 : 0 ≤ jb y ^ (-1 / p) * |deriv r y| := by positivity
    have a3 : 0 ≤ jb y ^ (-2 / p) * |deriv (deriv r) y| := by positivity
    have hγp : 0 ≤ jb y ^ γ := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have := c09_aux_rpow_div hj γ 0 (|r y|) (xNorm p γ r) (by
        rw [Real.rpow_zero, one_mul]; nlinarith)
      simpa using this
    · have := c09_aux_rpow_div hj γ (-1 / p) (|deriv r y|) (xNorm p γ r) (by nlinarith)
      rwa [show -γ - -1 / p = -γ + 1 / p by ring] at this
    · have := c09_aux_rpow_div hj γ (-2 / p) (|deriv (deriv r) y|) (xNorm p γ r) (by nlinarith)
      rwa [show -γ - -2 / p = -γ + 2 / p by ring] at this
  · filter_upwards [h2] with y hy hy0
    have hb := hy hy0
    simp only [Real.norm_eq_abs] at hb
    have hj := c09_aux_jb_pos y
    have a1 : 0 ≤ |r y| := abs_nonneg _
    have a2 : 0 ≤ jb y * |deriv r y| := by positivity
    have a3 : 0 ≤ jb y ^ (2 : ℕ) * |deriv (deriv r) y| := by positivity
    have hγp : 0 ≤ jb y ^ γ := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have := c09_aux_rpow_div hj γ 0 (|r y|) (xNorm p γ r) (by
        rw [Real.rpow_zero, one_mul]; nlinarith)
      simpa using this
    · have := c09_aux_rpow_div hj γ 1 (|deriv r y|) (xNorm p γ r) (by
        rw [Real.rpow_one]; nlinarith)
      exact this
    · have := c09_aux_rpow_div hj γ 2 (|deriv (deriv r) y|) (xNorm p γ r) (by
        rw [Real.rpow_two]; nlinarith)
      exact this

/-- Pointwise a.e. bounds from the `Y_γ` norm. -/
private theorem c09_aux_Y_ae (p γ : ℝ) (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) :
    (∀ᵐ y, 0 ≤ y → |G y| ≤ yNorm p γ G * jb y ^ (-γ) ∧
      |deriv G y| ≤ yNorm p γ G * jb y ^ (-γ + 1 / p)) ∧
    (∀ᵐ y, y < 0 → |G y| ≤ yNorm p γ G * jb y ^ (-γ) ∧
      |deriv G y| ≤ yNorm p γ G * jb y ^ (-γ - 1)) := by
  have hfin : Y_gamma_norm p γ G ≠ ⊤ := hG.2.ne
  unfold Y_gamma_norm at hfin
  set e1 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖)))
      (volume.restrict (Ici 0)) with he1
  set e2 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖)))
      (volume.restrict (Iic 0)) with he2
  have hN : yNorm p γ G = (e1 + e2).toReal := rfl
  have h1 := c09_aux_ae_of_essSup_le (μ := volume.restrict (Ici 0)) (le_self_add : e1 ≤ e1 + e2) hfin
  have h2 := c09_aux_ae_of_essSup_le (μ := volume.restrict (Iic 0)) (le_add_self : e2 ≤ e1 + e2) hfin
  rw [← hN] at h1 h2
  rw [Measure.restrict_congr_set Iio_ae_eq_Iic.symm] at h2
  rw [ae_restrict_iff' measurableSet_Ici] at h1
  rw [ae_restrict_iff' measurableSet_Iio] at h2
  constructor
  · filter_upwards [h1] with y hy hy0
    have hb := hy hy0
    simp only [Real.norm_eq_abs] at hb
    have hj := c09_aux_jb_pos y
    have a1 : 0 ≤ |G y| := abs_nonneg _
    have a2 : 0 ≤ jb y ^ (-1 / p) * |deriv G y| := by positivity
    have hγp : 0 ≤ jb y ^ γ := by positivity
    refine ⟨?_, ?_⟩
    · have := c09_aux_rpow_div hj γ 0 (|G y|) (yNorm p γ G) (by
        rw [Real.rpow_zero, one_mul]; nlinarith)
      simpa using this
    · have := c09_aux_rpow_div hj γ (-1 / p) (|deriv G y|) (yNorm p γ G) (by nlinarith)
      rwa [show -γ - -1 / p = -γ + 1 / p by ring] at this
  · filter_upwards [h2] with y hy hy0
    have hb := hy hy0
    simp only [Real.norm_eq_abs] at hb
    have hj := c09_aux_jb_pos y
    have a1 : 0 ≤ |G y| := abs_nonneg _
    have a2 : 0 ≤ jb y * |deriv G y| := by positivity
    have hγp : 0 ≤ jb y ^ γ := by positivity
    refine ⟨?_, ?_⟩
    · have := c09_aux_rpow_div hj γ 0 (|G y|) (yNorm p γ G) (by
        rw [Real.rpow_zero, one_mul]; nlinarith)
      simpa using this
    · have := c09_aux_rpow_div hj γ 1 (|deriv G y|) (yNorm p γ G) (by
        rw [Real.rpow_one]; nlinarith)
      exact this

/-- `x^{e₁}(x^{e₂} a) ≤ A` when `a ≤ A x^{e₃}` and `e₁+e₂+e₃ = 0`. -/
private theorem c09_aux_mul_bound {x : ℝ} (hx : 0 < x) (e1 e2 e3 a A : ℝ) (h : a ≤ A * x ^ e3)
    (he : e1 + e2 + e3 = 0) : x ^ e1 * (x ^ e2 * a) ≤ A := by
  have h1 : 0 ≤ x ^ e1 := Real.rpow_nonneg hx.le _
  have h2 : 0 ≤ x ^ e2 := Real.rpow_nonneg hx.le _
  calc x ^ e1 * (x ^ e2 * a) ≤ x ^ e1 * (x ^ e2 * (A * x ^ e3)) := by gcongr
    _ = A * (x ^ e1 * x ^ e2 * x ^ e3) := by ring
    _ = A := by rw [← Real.rpow_add hx, ← Real.rpow_add hx, he, Real.rpow_zero, mul_one]

/-- The weights on `y ≥ 0`. -/
private theorem c09_aux_w_pos_branch (p γ : ℝ) (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    c09_weights p γ j y = jb y ^ (-γ + (j : ℝ) / p) := by simp [c09_weights, hy]

/-- The weights on `y < 0`. -/
private theorem c09_aux_w_neg_branch (p γ : ℝ) (j : ℕ) {y : ℝ} (hy : y < 0) :
    c09_weights p γ j y = jb y ^ (-γ - (j : ℝ)) := by simp [c09_weights, not_le.mpr hy]

/-- `w_{γ,0} = ⟨·⟩^{-γ}`. -/
private theorem c09_aux_w0 (p γ y : ℝ) : c09_weights p γ 0 y = jb y ^ (-γ) := by
  unfold c09_weights; split_ifs <;> simp

/-- `⟨y⟩^{-s}` is integrable for `s > 1`. -/
private theorem c09_aux_jb_integrable {s : ℝ} (hs : 1 < s) : Integrable (fun z : ℝ => jb z ^ (-s)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := s) (by simpa using hs)
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  unfold jb
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  ring_nf

/-- Peetre: `⟨a+b⟩ ≤ √2 ⟨a⟩⟨b⟩`. -/
private theorem c09_aux_peetre (a b : ℝ) : jb (a + b) ≤ Real.sqrt 2 * jb a * jb b := by
  unfold jb
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a - b), sq_nonneg (a * b)]

/-- Peetre, negative powers: `⟨y-z⟩^{-s} ≤ 2^{s/2} ⟨y⟩^{-s} ⟨z⟩^{s}` for `s ≥ 0`. -/
private theorem c09_aux_peetre_neg (s : ℝ) (hs : 0 ≤ s) (y z : ℝ) :
    jb (y - z) ^ (-s) ≤ 2 ^ (s / 2) * jb y ^ (-s) * jb z ^ s := by
  have hu := c09_aux_jb_pos (y - z)
  have hY := c09_aux_jb_pos y
  have hZ := c09_aux_jb_pos z
  have hP : jb y ≤ Real.sqrt 2 * jb (y - z) * jb z := by
    have := c09_aux_peetre (y - z) z; simpa using this
  have key : jb y ^ s ≤ 2 ^ (s / 2) * jb z ^ s * jb (y - z) ^ s := by
    calc jb y ^ s ≤ (Real.sqrt 2 * jb (y - z) * jb z) ^ s :=
          Real.rpow_le_rpow hY.le hP hs
      _ = Real.sqrt 2 ^ s * jb (y - z) ^ s * jb z ^ s := by
          rw [Real.mul_rpow (by positivity) hZ.le, Real.mul_rpow (by positivity) hu.le]
      _ = 2 ^ (s / 2) * jb z ^ s * jb (y - z) ^ s := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; ring_nf
  have h1 : 0 < jb (y - z) ^ s := Real.rpow_pos_of_pos hu s
  have h2 : 0 < jb y ^ s := Real.rpow_pos_of_pos hY s
  rw [Real.rpow_neg hu.le, Real.rpow_neg hY.le]
  rw [inv_le_iff_one_le_mul₀ h1]
  calc (1 : ℝ) = (jb y ^ s)⁻¹ * jb y ^ s := by field_simp
    _ ≤ (jb y ^ s)⁻¹ * (2 ^ (s / 2) * jb z ^ s * jb (y - z) ^ s) := by gcongr
    _ = jb (y - z) ^ s * (2 ^ (s / 2) * (jb y ^ s)⁻¹ * jb z ^ s) := by ring
    _ ≤ _ := by rw [mul_comm]

/-- `|e^{-ixξ}| = 1`. -/
private theorem c09_aux_norm_exp_neg (x ξ : ℝ) :
    ‖Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- `|e^{ixξ}| = 1`. -/
private theorem c09_aux_norm_exp_pos (x ξ : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Blueprint: lem:c09_weight_facts.  Weights versus the norms of `X_γ`, `Y_γ`; `L¹` bounds;
Peetre's inequality; shifted-derivative bounds. -/
theorem c09_weight_facts (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    -- (1) pointwise bounds for `r ∈ X_γ`, and the converse
    (∀ r ∈ X_gamma p γ,
      (∀ y, |r y| ≤ xNorm p γ r * c09_weights p γ 0 y) ∧
      (∀ y, |deriv r y| ≤ xNorm p γ r * c09_weights p γ 1 y) ∧
      (∀ᵐ y, |deriv (deriv r) y| ≤ xNorm p γ r * c09_weights p γ 2 y)) ∧
    (∀ (r : ℝ → ℝ) (A : ℝ), ContDiff ℝ 1 r → LocallyLipschitz (deriv r) →
      (∀ y, |r y| ≤ A * c09_weights p γ 0 y) →
      (∀ y, |deriv r y| ≤ A * c09_weights p γ 1 y) →
      (∀ᵐ y, |deriv (deriv r) y| ≤ A * c09_weights p γ 2 y) →
      r ∈ X_gamma p γ ∧ xNorm p γ r ≤ 6 * A) ∧
    -- (2) pointwise bounds for `G ∈ Y_γ`
    (∀ G ∈ Y_gamma p γ,
      (∀ y, |G y| ≤ yNorm p γ G * c09_weights p γ 0 y) ∧
      (∀ᵐ y, |deriv G y| ≤ yNorm p γ G * c09_weights p γ 1 y ∧
        |deriv G y| ≤ yNorm p γ G * jb y ^ (-γ + 1 / p) ∧
        jb y ^ (-γ + 1 / p) ≤ 1)) ∧
    -- (3) `L¹` bounds
    (∃ C, 0 < C ∧ ∀ G ∈ Y_gamma p γ,
      Integrable G ∧ Integrable (deriv G) ∧
      Integrable (fun z => |deriv G z| * c09_weights_E p z) ∧
      (∫ z, |G z|) + (∫ z, |deriv G z|) + (∫ z, |deriv G z| * c09_weights_E p z) ≤
        C * yNorm p γ G) ∧
    -- (4) Peetre
    (∀ a b : ℝ, jb (a + b) ≤ Real.sqrt 2 * jb a * jb b) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ y z : ℝ, jb (y - z) ^ (-s) ≤ 2 ^ (s / 2) * jb y ^ (-s) * jb z ^ s) ∧
    -- (5) shifted derivative
    (∃ C, 0 < C ∧ ∀ G ∈ Y_gamma p γ, ∀ y : ℝ, ∀ᵐ z,
      |deriv G (y - z)| ≤ C * yNorm p γ G * jb z ^ (γ + 1) * c09_weights p γ 1 y) ∧
    -- (6) shifted function
    (∀ G ∈ Y_gamma p γ, ∀ y z : ℝ,
      |G (y - z)| ≤ 2 ^ (γ / 2) * yNorm p γ G * jb y ^ (-γ) * jb z ^ γ) := by
  have hp0 : 0 < p := by linarith
  have hγ1 : 1 / p < γ := by
    have := hγ.1; unfold beta at this
    have : 0 < (p + 1) / (2 * p) := by positivity
    linarith
  have hp0' : 0 < 1 / p := by positivity
  -- (1) forward
  have part1 : ∀ r ∈ X_gamma p γ,
      (∀ y, |r y| ≤ xNorm p γ r * c09_weights p γ 0 y) ∧
      (∀ y, |deriv r y| ≤ xNorm p γ r * c09_weights p γ 1 y) ∧
      (∀ᵐ y, |deriv (deriv r) y| ≤ xNorm p γ r * c09_weights p γ 2 y) := by
    intro r hr
    obtain ⟨hA, hB⟩ := c09_aux_X_ae p γ r hr
    have hrc : Continuous r := hr.1.1.continuous
    have hdc : Continuous (deriv r) := hr.1.1.continuous_deriv le_rfl
    refine ⟨c09_aux_ae_le_everywhere hrc.abs
      (continuous_const.mul (c09_aux_weights_continuous p γ 0)) ?_,
      c09_aux_ae_le_everywhere hdc.abs
      (continuous_const.mul (c09_aux_weights_continuous p γ 1)) ?_, ?_⟩
    · filter_upwards [hA, hB] with y h1 h2
      rw [c09_aux_w0]
      rcases le_or_gt 0 y with hy | hy
      · exact (h1 hy).1
      · exact (h2 hy).1
    · filter_upwards [hA, hB] with y h1 h2
      rcases le_or_gt 0 y with hy | hy
      · rw [c09_aux_w_pos_branch p γ 1 hy]; simpa using (h1 hy).2.1
      · rw [c09_aux_w_neg_branch p γ 1 hy]; simpa using (h2 hy).2.1
    · filter_upwards [hA, hB] with y h1 h2
      rcases le_or_gt 0 y with hy | hy
      · rw [c09_aux_w_pos_branch p γ 2 hy]; simpa using (h1 hy).2.2
      · rw [c09_aux_w_neg_branch p γ 2 hy]; simpa using (h2 hy).2.2
  -- (1) converse
  have part1' : ∀ (r : ℝ → ℝ) (A : ℝ), ContDiff ℝ 1 r → LocallyLipschitz (deriv r) →
      (∀ y, |r y| ≤ A * c09_weights p γ 0 y) →
      (∀ y, |deriv r y| ≤ A * c09_weights p γ 1 y) →
      (∀ᵐ y, |deriv (deriv r) y| ≤ A * c09_weights p γ 2 y) →
      r ∈ X_gamma p γ ∧ xNorm p γ r ≤ 6 * A := by
    intro r A hC hL h0 h1 h2
    have hA : 0 ≤ A := by
      have := h0 0
      have hw := c09_aux_weights_pos p γ 0 0
      by_contra hneg; push Not at hneg
      have : A * c09_weights p γ 0 0 < 0 := mul_neg_of_neg_of_pos hneg hw
      linarith [abs_nonneg (r 0)]
    have e1 : essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
        jb y ^ (-2 / p) * ‖deriv (deriv r) y‖))) (volume.restrict (Ici 0)) ≤
        ENNReal.ofReal (3 * A) := by
      refine essSup_le_of_ae_le _ ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ici]
      filter_upwards [h2] with y hy2 hy0
      apply ENNReal.ofReal_le_ofReal
      simp only [Real.norm_eq_abs]
      have hj := c09_aux_jb_pos y
      have b0 := c09_aux_mul_bound hj γ 0 (-γ) (|r y|) A (by
        have := h0 y; rwa [c09_aux_w0] at this) (by ring)
      have b1 := c09_aux_mul_bound hj γ (-1 / p) (-γ + 1 / p) (|deriv r y|) A (by
        have := h1 y; rw [c09_aux_w_pos_branch p γ 1 hy0] at this; simpa using this) (by ring)
      have b2 := c09_aux_mul_bound hj γ (-2 / p) (-γ + 2 / p) (|deriv (deriv r) y|) A (by
        rw [c09_aux_w_pos_branch p γ 2 hy0] at hy2; simpa using hy2) (by ring)
      rw [Real.rpow_zero, one_mul] at b0
      nlinarith
    have e2 : essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
        jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖))) (volume.restrict (Iic 0)) ≤
        ENNReal.ofReal (3 * A) := by
      refine essSup_le_of_ae_le _ ?_
      rw [Measure.restrict_congr_set Iio_ae_eq_Iic.symm, Filter.EventuallyLE,
        ae_restrict_iff' measurableSet_Iio]
      filter_upwards [h2] with y hy2 hy0
      apply ENNReal.ofReal_le_ofReal
      simp only [Real.norm_eq_abs]
      have hj := c09_aux_jb_pos y
      have b0 := c09_aux_mul_bound hj γ 0 (-γ) (|r y|) A (by
        have := h0 y; rwa [c09_aux_w0] at this) (by ring)
      have b1 := c09_aux_mul_bound hj γ 1 (-γ - 1) (|deriv r y|) A (by
        have := h1 y; rw [c09_aux_w_neg_branch p γ 1 hy0] at this; simpa using this) (by ring)
      have b2 := c09_aux_mul_bound hj γ 2 (-γ - 2) (|deriv (deriv r) y|) A (by
        rw [c09_aux_w_neg_branch p γ 2 hy0] at hy2; simpa using hy2) (by ring)
      rw [Real.rpow_zero, one_mul] at b0
      rw [Real.rpow_one] at b1
      rw [Real.rpow_two] at b2
      nlinarith
    have htot : X_gamma_norm p γ r ≤ ENNReal.ofReal (6 * A) := by
      unfold X_gamma_norm
      calc _ ≤ ENNReal.ofReal (3 * A) + ENNReal.ofReal (3 * A) := add_le_add e1 e2
        _ = ENNReal.ofReal (6 * A) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    refine ⟨⟨⟨hC, hL⟩, lt_of_le_of_lt htot ENNReal.ofReal_lt_top⟩, ?_⟩
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) htot
  -- (2)
  have part2 : ∀ G ∈ Y_gamma p γ,
      (∀ y, |G y| ≤ yNorm p γ G * c09_weights p γ 0 y) ∧
      (∀ᵐ y, |deriv G y| ≤ yNorm p γ G * c09_weights p γ 1 y ∧
        |deriv G y| ≤ yNorm p γ G * jb y ^ (-γ + 1 / p) ∧
        jb y ^ (-γ + 1 / p) ≤ 1) := by
    intro G hG
    obtain ⟨hA, hB⟩ := c09_aux_Y_ae p γ G hG
    have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    refine ⟨c09_aux_ae_le_everywhere hG.1.continuous.abs
      (continuous_const.mul (c09_aux_weights_continuous p γ 0)) ?_, ?_⟩
    · filter_upwards [hA, hB] with y h1 h2
      rw [c09_aux_w0]
      rcases le_or_gt 0 y with hy | hy
      · exact (h1 hy).1
      · exact (h2 hy).1
    · filter_upwards [hA, hB] with y h1 h2
      have hle : jb y ^ (-γ + 1 / p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (c09_aux_one_le_jb y) (by linarith)
      rcases le_or_gt 0 y with hy | hy
      · rw [c09_aux_w_pos_branch p γ 1 hy]
        refine ⟨by simpa using (h1 hy).2, (h1 hy).2, hle⟩
      · rw [c09_aux_w_neg_branch p γ 1 hy]
        refine ⟨by simpa using (h2 hy).2, (h2 hy).2.trans ?_, hle⟩
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
          (c09_aux_one_le_jb y) (by linarith)) hN
  have hjb1 := c09_aux_one_le_jb
  -- (4)
  have peetre2 : ∀ s : ℝ, 0 ≤ s → ∀ y z : ℝ,
      jb (y - z) ^ (-s) ≤ 2 ^ (s / 2) * jb y ^ (-s) * jb z ^ s := c09_aux_peetre_neg
  refine ⟨part1, part1', part2, ?_, c09_aux_peetre, peetre2, ?_, ?_⟩
  · -- (3)
    set σ : ℝ := γ - 1 / p - (1 - p) / (2 * p) with hσ
    have hσ1 : 1 < σ := by
      have := hγ.1; unfold beta at this
      have e : (p + 1) / (2 * p) + 1 / p = 1 + 1 / p + (1 - p) / (2 * p) := by
        field_simp; ring
      linarith
    have hq : 0 ≤ (1 - p) / (2 * p) := by
      apply div_nonneg <;> linarith
    have hint := c09_aux_jb_integrable hσ1
    set I := ∫ z, jb z ^ (-σ) with hI
    have hI0 : 0 ≤ I := integral_nonneg fun z => (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
    refine ⟨3 * I + 1, by positivity, fun G hG => ?_⟩
    have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    obtain ⟨hA, hB⟩ := c09_aux_Y_ae p γ G hG
    have hGc : Continuous G := hG.1.continuous
    have hG0 := (part2 G hG).1
    have bG : ∀ z, |G z| ≤ yNorm p γ G * jb z ^ (-σ) := fun z => by
      have := hG0 z; rw [c09_aux_w0] at this
      refine this.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hjb1 z) (by linarith)) hN)
    have bD : ∀ᵐ z, |deriv G z| ≤ yNorm p γ G * jb z ^ (-σ) := by
      filter_upwards [(part2 G hG).2] with z hz
      exact hz.2.1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hjb1 z) (by linarith)) hN)
    have bE : ∀ᵐ z, |deriv G z| * c09_weights_E p z ≤ yNorm p γ G * jb z ^ (-σ) := by
      filter_upwards [hA, bD] with z h1 h2
      have hj := c09_aux_jb_pos z
      unfold c09_weights_E
      split_ifs with hz
      · have : jb z ^ (-1 : ℝ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (hjb1 z) (by norm_num)
        calc |deriv G z| * jb z ^ (-1 : ℝ) ≤ |deriv G z| * 1 := by gcongr
          _ ≤ _ := by rw [mul_one]; exact h2
      · have h3 := (h1 (by linarith)).2
        calc |deriv G z| * jb z ^ ((1 - p) / (2 * p)) ≤
            yNorm p γ G * jb z ^ (-γ + 1 / p) * jb z ^ ((1 - p) / (2 * p)) := by gcongr
          _ = yNorm p γ G * jb z ^ (-σ) := by
            rw [mul_assoc, ← Real.rpow_add hj]; congr 2; rw [hσ]; ring
    have hgi : Integrable (fun z => yNorm p γ G * jb z ^ (-σ)) := hint.const_mul _
    have hmE : Measurable (c09_weights_E p) := by
      unfold c09_weights_E
      refine Measurable.ite measurableSet_Iic ?_ ?_ <;>
        exact (c09_aux_jb_continuous.rpow_const
          (fun y => Or.inl (c09_aux_jb_pos y).ne')).measurable
    have i1 : Integrable G := hgi.mono' hGc.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact bG z)
    have i2 : Integrable (deriv G) := hgi.mono' (measurable_deriv G).aestronglyMeasurable
      (by filter_upwards [bD] with z hz; rw [Real.norm_eq_abs]; exact hz)
    have i3 : Integrable (fun z => |deriv G z| * c09_weights_E p z) :=
      hgi.mono' ((measurable_deriv G).abs.mul hmE).aestronglyMeasurable
        (by
          filter_upwards [bE] with z hz
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
            (by unfold c09_weights_E; split_ifs <;>
              exact (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le))]
          exact hz)
    refine ⟨i1, i2, i3, ?_⟩
    have j1 : ∫ z, |G z| ≤ yNorm p γ G * I := by
      rw [hI, ← integral_const_mul]
      exact integral_mono_ae i1.abs hgi (Eventually.of_forall bG)
    have j2 : ∫ z, |deriv G z| ≤ yNorm p γ G * I := by
      rw [hI, ← integral_const_mul]
      exact integral_mono_ae i2.abs hgi bD
    have j3 : ∫ z, |deriv G z| * c09_weights_E p z ≤ yNorm p γ G * I := by
      rw [hI, ← integral_const_mul]
      exact integral_mono_ae i3 hgi bE
    nlinarith
  · -- (5)
    refine ⟨2 ^ ((γ + 1) / 2), by positivity, fun G hG y => ?_⟩
    have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    have hD := (part2 G hG).2
    have hD' := QuasiMeasurePreserving.ae (μa := volume) (μb := volume)
      (f := fun z : ℝ => y - z) (Measure.measurePreserving_sub_left volume y).quasiMeasurePreserving
      hD
    filter_upwards [hD'] with z hz
    have hw : c09_weights p γ 1 (y - z) ≤
        2 ^ ((γ + 1) / 2) * jb z ^ (γ + 1) * c09_weights p γ 1 y := by
      have h2 : (1 : ℝ) ≤ 2 ^ ((γ + 1) / 2) := Real.one_le_rpow (by norm_num) (by linarith)
      have hz1 : 0 ≤ jb z ^ (γ + 1) := (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
      rcases le_or_gt 0 y with hy | hy
      · -- `y ≥ 0`
        rw [c09_aux_w_pos_branch p γ 1 hy]
        have hle : c09_weights p γ 1 (y - z) ≤ jb (y - z) ^ (-(γ - 1 / p)) := by
          rcases le_or_gt 0 (y - z) with h | h
          · rw [c09_aux_w_pos_branch p γ 1 h]; simp only [Nat.cast_one]; ring_nf; rfl
          · rw [c09_aux_w_neg_branch p γ 1 h]
            exact Real.rpow_le_rpow_of_exponent_le (hjb1 _) (by simp; linarith [inv_pos.mpr hp0])
        refine hle.trans ((peetre2 (γ - 1 / p) (by linarith) y z).trans ?_)
        simp only [Nat.cast_one]
        rw [show -γ + 1 / p = -(γ - 1 / p) by ring]
        have a1 : (2 : ℝ) ^ ((γ - 1 / p) / 2) ≤ 2 ^ ((γ + 1) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have a2 : jb z ^ (γ - 1 / p) ≤ jb z ^ (γ + 1) :=
          Real.rpow_le_rpow_of_exponent_le (hjb1 z) (by linarith)
        have a3 : 0 ≤ jb y ^ (-(γ - 1 / p)) := (Real.rpow_pos_of_pos (c09_aux_jb_pos y) _).le
        have a4 : 0 ≤ jb z ^ (γ - 1 / p) := (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
        calc 2 ^ ((γ - 1 / p) / 2) * jb y ^ (-(γ - 1 / p)) * jb z ^ (γ - 1 / p)
            ≤ 2 ^ ((γ + 1) / 2) * jb y ^ (-(γ - 1 / p)) * jb z ^ (γ + 1) := by gcongr
          _ = _ := by ring
      · rw [c09_aux_w_neg_branch p γ 1 hy]
        simp only [Nat.cast_one]
        rcases le_or_gt 0 (y - z) with h | h
        · -- `y < 0 ≤ y - z`: then `z ≤ y < 0`, `⟨z⟩ ≥ ⟨y⟩`
          have hle1 : c09_weights p γ 1 (y - z) ≤ 1 := by
            rw [c09_aux_w_pos_branch p γ 1 h]; simpa using hz.2.2
          have hzy : jb y ≤ jb z := by
            unfold jb; apply Real.sqrt_le_sqrt; nlinarith
          have hY := c09_aux_jb_pos y
          have e1 : (1 : ℝ) ≤ jb z ^ (γ + 1) * jb y ^ (-γ - 1) := by
            rw [show -γ - 1 = -(γ + 1) by ring, Real.rpow_neg hY.le]
            rw [← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hY _)]
            exact Real.rpow_le_rpow hY.le hzy (by linarith)
          calc c09_weights p γ 1 (y - z) ≤ 1 := hle1
            _ ≤ 2 ^ ((γ + 1) / 2) * (jb z ^ (γ + 1) * jb y ^ (-γ - 1)) := by nlinarith
            _ = _ := by ring
        · rw [c09_aux_w_neg_branch p γ 1 h]
          simp only [Nat.cast_one]
          rw [show -γ - 1 = -(γ + 1) by ring]
          calc jb (y - z) ^ (-(γ + 1)) ≤ 2 ^ ((γ + 1) / 2) * jb y ^ (-(γ + 1)) * jb z ^ (γ + 1) :=
                peetre2 (γ + 1) (by linarith) y z
            _ = _ := by ring
    calc |deriv G (y - z)| ≤ yNorm p γ G * c09_weights p γ 1 (y - z) := hz.1
      _ ≤ yNorm p γ G * (2 ^ ((γ + 1) / 2) * jb z ^ (γ + 1) * c09_weights p γ 1 y) := by gcongr
      _ = _ := by ring
  · -- (6)
    intro G hG y z
    have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    have h := (part2 G hG).1 (y - z)
    rw [c09_aux_w0] at h
    calc |G (y - z)| ≤ yNorm p γ G * jb (y - z) ^ (-γ) := h
      _ ≤ yNorm p γ G * (2 ^ (γ / 2) * jb y ^ (-γ) * jb z ^ γ) := by
          gcongr; exact peetre2 γ (by linarith) y z
      _ = _ := by ring

/-! ### Fourier-analytic helpers -/

/-- The shared `fourierT` versus Mathlib's `𝓕`: `f̂(x) = 𝓕 f (x/2π)`. -/
private theorem c09_aux_fourierT_eq (f : ℝ → ℂ) (x : ℝ) : fourierT f x = 𝓕 f (x / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold fourierT
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

/-- Mathlib's `𝓕⁻` on `ℝ` written with an exponential. -/
private theorem c09_aux_fourierInv_eq (F : ℝ → ℂ) (ξ : ℝ) :
    𝓕⁻ F ξ = ∫ v, F v * Complex.exp (Complex.I * ((2 * π * v : ℝ) : ℂ) * (ξ : ℂ)) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  congr 1; ext v
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

example (φ : SchwartzMap ℝ ℂ) : 𝓕⁻ (𝓕 (⇑φ)) = ⇑φ := by
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe]; simp



/-- Fourier inversion for Schwartz functions (as functions). -/
private theorem c09_aux_fourierInv_fourier (φ : SchwartzMap ℝ ℂ) : 𝓕⁻ (𝓕 (⇑φ)) = ⇑φ := by
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe]; simp

/-- Inversion in the shared convention: `∫ φ̂(x) e^{ixξ} dx = 2π φ(ξ)`. -/
private theorem c09_aux_fourierT_inv (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ∫ x, fourierT (⇑φ) x * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) = (2 * π : ℝ) * φ ξ := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set g : ℝ → ℂ := fun x => fourierT (⇑φ) x * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) with hg
  have hsub := Measure.integral_comp_mul_left g (2 * π)
  have e : ∫ x, g x = ((2 * π : ℝ) : ℂ) * ∫ t, g (2 * π * t) := by
    rw [hsub, abs_inv, abs_of_pos h2π, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ h2π.ne', Complex.ofReal_one, one_mul]
  have e2 : (fun t => g (2 * π * t)) = fun t => 𝓕 (⇑φ) t *
      Complex.exp (Complex.I * ((2 * π * t : ℝ) : ℂ) * (ξ : ℂ)) := by
    ext t
    rw [hg]; dsimp only
    rw [c09_aux_fourierT_eq, show 2 * π * t / (2 * π) = t by field_simp]
  show ∫ x, g x = _
  rw [e, e2, ← c09_aux_fourierInv_eq, c09_aux_fourierInv_fourier]

/-- `φ̂` is integrable for Schwartz `φ`. -/
private theorem c09_aux_fourierT_schwartz_integrable (φ : SchwartzMap ℝ ℂ) : Integrable (fourierT (⇑φ)) := by
  have : fourierT (⇑φ) = fun x => (𝓕 φ) (x / (2 * π)) := by
    ext x; rw [c09_aux_fourierT_eq, SchwartzMap.fourier_coe]
  rw [this]
  exact (SchwartzMap.integrable (𝓕 φ)).comp_div (by positivity)

/-- `φ̂` is continuous for Schwartz `φ`. -/
private theorem c09_aux_fourierT_schwartz_continuous (φ : SchwartzMap ℝ ℂ) : Continuous (fourierT (⇑φ)) := by
  have : fourierT (⇑φ) = fun x => (𝓕 φ) (x / (2 * π)) := by
    ext x; rw [c09_aux_fourierT_eq, SchwartzMap.fourier_coe]
  rw [this]
  exact (SchwartzMap.continuous (𝓕 φ)).comp (continuous_id.div_const _)



/-- For integrable `m`, `(m)^∨` has distributional Fourier transform `m`. -/
private theorem c09_aux_hasDistFourier_invFourierT (m : ℝ → ℂ) (hm : Integrable m) : HasDistFourier (invFourierT m) m := by
  intro φ
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set e : ℝ → ℝ → ℂ := fun x ξ => Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) with he
  have hec : Continuous (fun z : ℝ × ℝ => e z.1 z.2) := by rw [he]; fun_prop
  have hne : ∀ x ξ, ‖e x ξ‖ = 1 := fun x ξ => by rw [he]; dsimp only; rw [Complex.norm_exp]; simp
  set F : ℝ × ℝ → ℂ := fun z => m z.2 * e z.1 z.2 * fourierT (⇑φ) z.1 with hF
  have hFi : Integrable F (volume.prod volume) := by
    refine ((c09_aux_fourierT_schwartz_integrable φ).norm.mul_prod hm.norm).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((hm.aestronglyMeasurable.comp_snd).mul hec.aestronglyMeasurable).mul
        ((c09_aux_fourierT_schwartz_continuous φ).comp continuous_fst).aestronglyMeasurable
    · rw [hF]; dsimp only
      rw [norm_mul, norm_mul, hne, mul_one, mul_comm]
  have hswap := integral_integral_swap (f := fun x ξ => m ξ * e x ξ * fourierT (⇑φ) x) hFi
  calc ∫ x, invFourierT m x * fourierT (⇑φ) x
      = ∫ x, ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, m ξ * e x ξ * fourierT (⇑φ) x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        unfold invFourierT
        rw [mul_assoc, ← integral_mul_const]
    _ = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ x, ∫ ξ, m ξ * e x ξ * fourierT (⇑φ) x := integral_const_mul _ _
    _ = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, ∫ x, m ξ * e x ξ * fourierT (⇑φ) x := by rw [hswap]
    _ = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, m ξ * ((2 * π : ℝ) * φ ξ) := by
        apply congrArg (fun t => ((2 * π : ℝ) : ℂ)⁻¹ * t)
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only
        rw [← c09_aux_fourierT_inv φ ξ, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [he]; ring
    _ = ∫ ξ, m ξ * φ ξ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only
        field_simp


/-- Every real test function is `φ̂` for a Schwartz `φ`. -/
private theorem c09_aux_fourierT_surj (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ x, fourierT (⇑φ) x = (g x : ℂ) := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  set ψ : ℝ → ℂ := fun w => ((g (2 * π * w) : ℝ) : ℂ) with hψ
  have hψc : HasCompactSupport ψ := by
    have h1 : HasCompactSupport (g ∘ (Homeomorph.mulLeft₀ (2 * π) h2π)) :=
      hgc.comp_homeomorph _
    exact h1.comp_left Complex.ofReal_zero
  have hψd : ContDiff ℝ ∞ ψ :=
    Complex.ofRealCLM.contDiff.comp (hg.comp (contDiff_const.mul contDiff_id))
  set Ψ : SchwartzMap ℝ ℂ := hψc.toSchwartzMap hψd
  refine ⟨𝓕⁻ Ψ, fun x => ?_⟩
  rw [c09_aux_fourierT_eq, ← SchwartzMap.fourier_coe]
  simp only [FourierTransform.fourier_fourierInv_eq]
  show ψ (x / (2 * π)) = _
  rw [hψ]; dsimp only
  rw [show 2 * π * (x / (2 * π)) = x by field_simp]

/-- A continuous `u` with `∫ u φ̂ = 0` for all Schwartz `φ` vanishes. -/
private theorem c09_aux_dist_unique0 (u : ℝ → ℂ) (hu : Continuous u)
    (h : ∀ φ : SchwartzMap ℝ ℂ, ∫ x, u x * fourierT (⇑φ) x = 0) : u = 0 := by
  have hae : ∀ᵐ x, u x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable fun g hg hgc => ?_
    obtain ⟨φ, hφ⟩ := c09_aux_fourierT_surj g hg hgc
    rw [← h φ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ, Complex.real_smul]; ring
  have : u =ᵐ[volume] (0 : ℝ → ℂ) := hae
  exact (hu.ae_eq_iff_eq volume continuous_const).mp this


/-- `⟨x⟩ ≤ 2π ⟨x/2π⟩`. -/
private theorem c09_aux_jb_scale (x : ℝ) : jb x ≤ 2 * π * jb (x / (2 * π)) := by
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hpos : 0 < 2 * π := by positivity
  unfold jb
  rw [show 2 * π * Real.sqrt (1 + (x / (2 * π)) ^ 2) =
      Real.sqrt ((2 * π) ^ 2 * (1 + (x / (2 * π)) ^ 2)) by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hpos.le]]
  apply Real.sqrt_le_sqrt
  rw [mul_add, mul_one, div_pow, mul_div_cancel₀ _ (by positivity)]
  nlinarith

/-- A continuous polynomially bounded function times `φ̂` (Schwartz `φ`) is integrable. -/
private theorem c09_aux_polybdd_mul_integrable (r : ℝ → ℂ) (hr : Continuous r)
    (hb : IsPolyBounded r) (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x => r x * fourierT (⇑φ) x) := by
  obtain ⟨C, N, hCN⟩ := hb
  have hC : 0 ≤ C := by
    have := hCN 0
    have h1 : jb 0 ^ N = 1 := by simp [jb]
    rw [h1, mul_one] at this
    exact (norm_nonneg _).trans this
  set M : ℕ := ⌈max N 0⌉₊ with hM
  set F := 𝓕 φ with hF
  have hφ : ∀ x, fourierT (⇑φ) x = F (x / (2 * π)) := fun x => by
    rw [c09_aux_fourierT_eq, hF, SchwartzMap.fourier_coe]
  set h : ℝ → ℝ := fun t => ‖F t‖ + ‖t‖ ^ (2 * M) * ‖F t‖ with hh
  have hi : Integrable h :=
    (SchwartzMap.integrable_pow_mul volume F 0).congr (Eventually.of_forall fun t => by simp)
      |>.add (SchwartzMap.integrable_pow_mul volume F (2 * M))
  have hi' : Integrable (fun x => (C * (2 * π) ^ (2 * M) * 2 ^ M) * h (x / (2 * π))) :=
    (hi.comp_div (by positivity)).const_mul _
  refine hi'.mono' (hr.mul (c09_aux_fourierT_schwartz_continuous φ)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, hφ]
  set t := x / (2 * π)
  have hjb : jb x ^ N ≤ (2 * π) ^ (2 * M) * 2 ^ M * (1 + ‖t‖ ^ (2 * M)) := by
    have hx1 := c09_aux_one_le_jb x
    have e1 : jb x ^ N ≤ jb x ^ ((2 * M : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hx1
      have : max N 0 ≤ (M : ℝ) := Nat.le_ceil _
      push_cast; linarith [le_max_left N 0, le_max_right N 0]
    rw [Real.rpow_natCast] at e1
    refine e1.trans ?_
    have e2 : jb x ^ (2 * M) ≤ (2 * π * jb t) ^ (2 * M) :=
      pow_le_pow_left₀ (c09_aux_jb_pos x).le (c09_aux_jb_scale x) _
    refine e2.trans ?_
    rw [mul_pow, pow_mul, pow_mul (jb t)]
    have ejt : jb t ^ 2 = 1 + t ^ 2 := by unfold jb; rw [Real.sq_sqrt (by positivity)]
    rw [ejt, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (1 + t ^ 2) ≤ 2 * max 1 (t ^ 2) := by
      rcases le_total 1 (t ^ 2) with h1 | h1
      · rw [max_eq_right h1]; linarith
      · rw [max_eq_left h1]; linarith
    calc (1 + t ^ 2) ^ M ≤ (2 * max 1 (t ^ 2)) ^ M := pow_le_pow_left₀ (by positivity) this _
      _ = 2 ^ M * max 1 (t ^ 2) ^ M := by rw [mul_pow]
      _ ≤ 2 ^ M * (1 + ‖t‖ ^ (2 * M)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Real.norm_eq_abs, pow_mul, sq_abs]
          rcases le_total 1 (t ^ 2) with h1 | h1
          · rw [max_eq_right h1]; linarith [pow_nonneg (sq_nonneg t) M]
          · rw [max_eq_left h1, one_pow]; linarith [pow_nonneg (sq_nonneg t) M]
  calc ‖r x‖ * ‖F t‖ ≤ (C * jb x ^ N) * ‖F t‖ := by gcongr; exact hCN x
    _ ≤ (C * ((2 * π) ^ (2 * M) * 2 ^ M * (1 + ‖t‖ ^ (2 * M)))) * ‖F t‖ := by gcongr
    _ = (C * (2 * π) ^ (2 * M) * 2 ^ M) * h t := by rw [hh]; ring

/-- Uniqueness of continuous polynomially bounded functions with a given distributional Fourier
transform. -/
private theorem c09_aux_dist_unique (r₁ r₂ : ℝ → ℂ) (h₁ : Continuous r₁) (h₂ : Continuous r₂)
    (b₁ : IsPolyBounded r₁) (b₂ : IsPolyBounded r₂) (m : ℝ → ℂ)
    (f₁ : HasDistFourier r₁ m) (f₂ : HasDistFourier r₂ m) : r₁ = r₂ := by
  have := c09_aux_dist_unique0 (r₁ - r₂) (h₁.sub h₂) fun φ => by
    have i1 := c09_aux_polybdd_mul_integrable r₁ h₁ b₁ φ
    have i2 := c09_aux_polybdd_mul_integrable r₂ h₂ b₂ φ
    have e : (fun x => (r₁ - r₂) x * fourierT (⇑φ) x) =
        fun x => r₁ x * fourierT (⇑φ) x - r₂ x * fourierT (⇑φ) x := by
      ext x; simp only [Pi.sub_apply]; ring
    rw [e, integral_sub i1 i2, f₁ φ, f₂ φ, sub_self]
  exact sub_eq_zero.mp this

/-- The Fourier transform of an integrable real function is continuous. -/
private theorem c09_aux_fourierT_continuous (G : ℝ → ℝ) (hG : Integrable G) :
    Continuous (fourierT (fun x => (G x : ℂ))) := by
  show Continuous fun ξ : ℝ => ∫ x, (G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))
  have hGc : Integrable (fun x => (G x : ℂ)) := hG.ofReal
  refine continuous_of_dominated
    (F := fun (ξ : ℝ) (x : ℝ) => (G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))))
    (bound := fun x => ‖(G x : ℂ)‖) (fun ξ => ?_) (fun ξ => ?_)
    hGc.norm (Eventually.of_forall fun x => by fun_prop)
  · have hc : Continuous fun x : ℝ => Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) := by
      fun_prop
    exact hGc.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_mul, c09_aux_norm_exp_neg, mul_one]

/-- The inverse Fourier transform of an integrable function is continuous. -/
private theorem c09_aux_invFourierT_continuous (g : ℝ → ℂ) (hg : Integrable g) :
    Continuous (invFourierT g) := by
  unfold invFourierT
  refine continuous_const.mul ?_
  refine continuous_of_dominated
    (F := fun (x : ℝ) (ξ : ℝ) => g ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)))
    (bound := fun ξ => ‖g ξ‖) (fun x => ?_) (fun x => ?_) hg.norm
    (Eventually.of_forall fun ξ => by fun_prop)
  · exact hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun ξ : ℝ =>
      Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))).aestronglyMeasurable
  · exact Eventually.of_forall fun ξ => by rw [norm_mul, c09_aux_norm_exp_pos, mul_one]

/-- `‖ǧ(x)‖ ≤ (2π)⁻¹ ∫ ‖g‖`. -/
private theorem c09_aux_invFourierT_norm_le (g : ℝ → ℂ) (x : ℝ) :
    ‖invFourierT g x‖ ≤ (2 * π)⁻¹ * ∫ ξ, ‖g ξ‖ := by
  unfold invFourierT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext ξ; rw [norm_mul, c09_aux_norm_exp_pos, mul_one]

/-- Linearity of the inverse Fourier transform on integrable symbols. -/
private theorem c09_aux_invFourierT_lin (g h : ℝ → ℂ) (hg : Integrable g) (hh : Integrable h)
    (a b : ℝ) (x : ℝ) :
    invFourierT (fun ξ => (a : ℂ) * g ξ + (b : ℂ) * h ξ) x =
      (a : ℂ) * invFourierT g x + (b : ℂ) * invFourierT h x := by
  unfold invFourierT
  have hc : Continuous fun ξ : ℝ => Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) := by fun_prop
  have ig : Integrable (fun ξ => g ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) :=
    hg.mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun ξ => (c09_aux_norm_exp_pos x ξ).le)
  have ih : Integrable (fun ξ => h ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) :=
    hh.mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun ξ => (c09_aux_norm_exp_pos x ξ).le)
  have : ∫ ξ, ((a : ℂ) * g ξ + (b : ℂ) * h ξ) * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)) =
      (a : ℂ) * (∫ ξ, g ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) +
        (b : ℂ) * (∫ ξ, h ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) := by
    have e : (fun ξ => ((a : ℂ) * g ξ + (b : ℂ) * h ξ) * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)))
        = fun ξ => (a : ℂ) * (g ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) +
          (b : ℂ) * (h ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))) := by
      ext ξ; ring
    rw [e, integral_add (ig.const_mul _) (ih.const_mul _), integral_const_mul, integral_const_mul]
  rw [this]; ring

/-! ### The positive high-frequency part and the tail integrals -/

/-- Blueprint: def:c09_T_plus.  The symbol `\widehat{𝒯₊G}(ξ) = 𝟙_{ξ>0} (1-χ(ξ)) m_G(ξ)`
(`χ = rho`, `m_G = T_0_symbol p G`): the `ξ > 0` part of the symbol of `T_high`. -/
def c09_T_plus_hat (p : ℝ) (G : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  if 0 < ξ then ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ else 0

/-- Blueprint: def:c09_T_plus.  `𝒯₊G(y) = (2π)⁻¹ ∫₀^∞ \widehat{𝒯₊G}(ξ) e^{iyξ} dξ`
(the shared `invFourierT` of `c09_T_plus_hat`, which vanishes on `ξ ≤ 0`). -/
def c09_T_plus (p : ℝ) (G : ℝ → ℝ) : ℝ → ℂ := invFourierT (c09_T_plus_hat p G)

/-- Blueprint: def:c09_tail_integral.  The phase `Ψ_z(η) = Φ₀(η) - zη`. -/
def c09_tail_integral_phase (p z η : ℝ) : ℝ := Phi0 p η - z * η

/-- Blueprint: def:c09_tail_integral.  `E_z(ξ) = lim_{N→∞} ∫_ξ^N e^{iΨ_z(η)} dη`
(`limUnder`; existence is lem:c09_tail_basic). -/
def c09_tail_integral (p z ξ : ℝ) : ℂ :=
  limUnder atTop (fun N : ℝ => ∫ η in ξ..N,
    Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)))

/-- Blueprint: def:c09_tail_integral.  `F_G(ξ) = ∫ G'(z) E_z(ξ) dz`. -/
def c09_tail_integral_F (p : ℝ) (G : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ z, ((deriv G z : ℝ) : ℂ) * c09_tail_integral p z ξ

/-! ### Helpers: symbol calculus and the tail integrals -/

/-- Leibniz bound. -/
theorem c09_aux_leib {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (f g : ℝ → 𝔸) (ξ : ℝ) (hξ : 0 < ξ) (n : ℕ)
    (hf : ContDiffAt ℝ n f ξ) (hg : ContDiffAt ℝ n g ξ) (A B a b : ℝ)
    (hA : ∀ i ≤ n, ‖iteratedDeriv i f ξ‖ ≤ A * ξ ^ (a - i))
    (hB : ∀ i ≤ n, ‖iteratedDeriv i g ξ‖ ≤ B * ξ ^ (b - i)) :
    ‖iteratedDeriv n (fun x => f x * g x) ξ‖ ≤ 2 ^ n * A * B * ξ ^ (a + b - n) := by
  rw [iteratedDeriv_fun_mul hf hg]
  refine (norm_sum_le _ _).trans ?_
  have hsum : ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [← hsum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 := hA i hin
  have h2 := hB (n - i) (Nat.sub_le n i)
  have e : ξ ^ (a - i) * ξ ^ (b - ((n - i : ℕ) : ℝ)) = ξ ^ (a + b - n) := by
    rw [← Real.rpow_add hξ, Nat.cast_sub hin]; congr 1; ring
  have hc : ‖((n.choose i : ℕ) : 𝔸)‖ ≤ (n.choose i : ℝ) := by
    simpa using Nat.norm_cast_le (α := 𝔸) (n.choose i)
  calc ‖((n.choose i : ℕ) : 𝔸) * iteratedDeriv i f ξ * iteratedDeriv (n - i) g ξ‖
      ≤ ‖((n.choose i : ℕ) : 𝔸)‖ * ‖iteratedDeriv i f ξ‖ * ‖iteratedDeriv (n - i) g ξ‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr; exact norm_mul_le _ _
    _ ≤ (n.choose i : ℝ) * (A * ξ ^ (a - i)) * (B * ξ ^ (b - ((n - i : ℕ) : ℝ))) := by
        have h0 : 0 ≤ A * ξ ^ (a - i) := (norm_nonneg _).trans h1
        gcongr
    _ = (n.choose i : ℝ) * A * B * ξ ^ (a + b - n) := by rw [← e]; ring

/-- Bounds for derivatives of `x^s`. -/
theorem c09_aux_rpow_derivs (s : ℝ) (N : ℕ) : ∃ P, 0 ≤ P ∧ ∀ ξ : ℝ, 0 < ξ → ∀ i ≤ N,
    ‖iteratedDeriv i (fun x : ℝ => x ^ s) ξ‖ ≤ P * ξ ^ (s - i) := by
  refine ⟨∑ k ∈ Finset.range (N + 1), |(descPochhammer ℝ k).eval s|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun ξ hξ i hi => ?_⟩
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hξ _)]
  gcongr
  exact Finset.single_le_sum (f := fun k : ℕ => |(descPochhammer ℝ k).eval s|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))

/-- Smoothness of `(y - x^p)⁻¹` away from its pole. -/
theorem c09_aux_psi_smooth (p y ξ : ℝ) (hξ : 0 < ξ) (hne : y - ξ ^ p ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (y - x ^ p)⁻¹) ξ :=
  (contDiffAt_const.sub (Real.contDiffAt_rpow_const_of_ne hξ.ne')).inv hne

/-- Derivative identity `g' = p x^{p-1} g²` for `g = (y - x^p)⁻¹`. -/
theorem c09_aux_psi_deriv (p : ℝ) (hp : 0 < p) (y ξ : ℝ) (hξ : 0 < ξ) (hne : y - ξ ^ p ≠ 0) :
    deriv (fun x : ℝ => (y - x ^ p)⁻¹) =ᶠ[𝓝 ξ]
      fun x => (p * x ^ (p - 1)) * ((y - x ^ p)⁻¹ * (y - x ^ p)⁻¹) := by
  have hU : IsOpen (Ioi (0 : ℝ) ∩ {x : ℝ | y - x ^ p ≠ 0}) :=
    isOpen_Ioi.inter
      (isOpen_ne_fun (continuous_const.sub (Real.continuous_rpow_const hp.le)) continuous_const)
  filter_upwards [hU.mem_nhds ⟨hξ, hne⟩] with x hx
  have h1 : HasDerivAt (fun x : ℝ => y - x ^ p) (-(p * x ^ (p - 1))) x := by
    simpa using (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.1.ne')).const_sub y
  rw [(h1.fun_inv hx.2).deriv]
  field_simp

/-- Bounds for derivatives of `(y - x^p)⁻¹` in the nonstationary region. -/
theorem c09_aux_psi_inv (p : ℝ) (hp : 0 < p) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, 0 < C ∧ ∀ y ξ : ℝ, 0 < ξ → c * (|y| + ξ ^ p) ≤ |y - ξ ^ p| → ∀ i ≤ N,
      ‖iteratedDeriv i (fun x : ℝ => (y - x ^ p)⁻¹) ξ‖ ≤
        C * (|y| + ξ ^ p)⁻¹ * ξ ^ ((0 : ℝ) - i) := by
  induction N with
  | zero =>
    refine ⟨c⁻¹, inv_pos.mpr hc, fun y ξ hξ hgood i hi => ?_⟩
    have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ p; positivity
    obtain rfl : i = 0 := by omega
    simp only [iteratedDeriv_zero, Real.norm_eq_abs, abs_inv, CharP.cast_eq_zero, sub_zero,
      Real.rpow_zero, mul_one]
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) hgood
  | succ N ih =>
    obtain ⟨C, hC, hb⟩ := ih
    obtain ⟨P, hP, hPb⟩ := c09_aux_rpow_derivs (p - 1) N
    refine ⟨C + 4 ^ N * p * P * C ^ 2, by positivity, fun y ξ hξ hgood i hi => ?_⟩
    have hξp := Real.rpow_pos_of_pos hξ p
    have hW : 0 < |y| + ξ ^ p := by positivity
    have hne : y - ξ ^ p ≠ 0 := by
      intro h; rw [h, abs_zero] at hgood; nlinarith
    have hξi : 0 ≤ (|y| + ξ ^ p)⁻¹ * ξ ^ ((0 : ℝ) - i) := by positivity
    rcases Nat.lt_or_ge i (N + 1) with hi' | hi'
    · refine (hb y ξ hξ hgood i (by omega)).trans ?_
      have : 0 ≤ 4 ^ N * p * P * C ^ 2 := by positivity
      nlinarith
    obtain rfl : i = N + 1 := by omega
    rw [iteratedDeriv_succ', (c09_aux_psi_deriv p hp y ξ hξ hne).iteratedDeriv_eq]
    have hsm := c09_aux_psi_smooth p y ξ hξ hne
    have hgg := c09_aux_leib (fun x : ℝ => (y - x ^ p)⁻¹) (fun x : ℝ => (y - x ^ p)⁻¹) ξ hξ
    have hgg' : ∀ i ≤ N, ‖iteratedDeriv i (fun x : ℝ => (y - x ^ p)⁻¹ * (y - x ^ p)⁻¹) ξ‖ ≤
        (2 ^ N * (C * (|y| + ξ ^ p)⁻¹) * (C * (|y| + ξ ^ p)⁻¹)) * ξ ^ ((0 : ℝ) + 0 - i) := by
      intro i hi
      refine (hgg i (hsm.of_le (by exact_mod_cast le_top)) (hsm.of_le (by exact_mod_cast le_top))
        (C * (|y| + ξ ^ p)⁻¹) (C * (|y| + ξ ^ p)⁻¹) 0 0
        (fun k hk => hb y ξ hξ hgood k (by omega))
        (fun k hk => hb y ξ hξ hgood k (by omega))).trans ?_
      have : (2 : ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hi
      gcongr
    have hf1 : ∀ i ≤ N, ‖iteratedDeriv i (fun x : ℝ => p * x ^ (p - 1)) ξ‖ ≤
        (p * P) * ξ ^ ((p - 1) - i) := by
      intro i hi
      rw [iteratedDeriv_const_mul _ ((Real.contDiffAt_rpow_const_of_ne hξ.ne').of_le
        (by exact_mod_cast le_top)), norm_mul, Real.norm_eq_abs, abs_of_pos hp, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hPb ξ hξ i hi) hp.le
    have key := c09_aux_leib (fun x : ℝ => p * x ^ (p - 1))
      (fun x : ℝ => (y - x ^ p)⁻¹ * (y - x ^ p)⁻¹) ξ hξ N
      (contDiffAt_const.mul ((Real.contDiffAt_rpow_const_of_ne hξ.ne').of_le
        (by exact_mod_cast le_top)))
      ((hsm.mul hsm).of_le (by exact_mod_cast le_top)) _ _ _ _ hf1 hgg'
    refine key.trans ?_
    have e : ξ ^ (p - 1 + (0 + 0) - (N : ℝ)) = ξ ^ p * ξ ^ ((0 : ℝ) - ((N + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hξ]; push_cast; ring_nf
    rw [e]
    have hWi : ξ ^ p * (|y| + ξ ^ p)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hW]; linarith [abs_nonneg y]
    have hpos : 0 ≤ ξ ^ ((0 : ℝ) - ((N + 1 : ℕ) : ℝ)) := by positivity
    have hWp : 0 < (|y| + ξ ^ p)⁻¹ := inv_pos.mpr hW
    calc 2 ^ N * (p * P) * (2 ^ N * (C * (|y| + ξ ^ p)⁻¹) * (C * (|y| + ξ ^ p)⁻¹)) *
          (ξ ^ p * ξ ^ ((0 : ℝ) - ((N + 1 : ℕ) : ℝ)))
        = (4 ^ N * p * P * C ^ 2) * (|y| + ξ ^ p)⁻¹ * (ξ ^ p * (|y| + ξ ^ p)⁻¹) *
          ξ ^ ((0 : ℝ) - ((N + 1 : ℕ) : ℝ)) := by
          rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]; ring
      _ ≤ (4 ^ N * p * P * C ^ 2) * (|y| + ξ ^ p)⁻¹ * 1 * ξ ^ ((0 : ℝ) - ((N + 1 : ℕ) : ℝ)) := by
          gcongr
      _ ≤ (C + 4 ^ N * p * P * C ^ 2) * (|y| + ξ ^ p)⁻¹ * ξ ^ ((0 : ℝ) - ((N + 1 : ℕ) : ℝ)) := by
          rw [mul_one]; gcongr; linarith

/-- Leibniz bound with termwise control. -/
theorem c09_aux_leib_terms {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (f g : ℝ → 𝔸) (ξ : ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f ξ) (hg : ContDiffAt ℝ n g ξ) (D : ℝ)
    (hD : ∀ i ≤ n, ‖iteratedDeriv i f ξ‖ * ‖iteratedDeriv (n - i) g ξ‖ ≤ D) :
    ‖iteratedDeriv n (fun x => f x * g x) ξ‖ ≤ 2 ^ n * D := by
  rw [iteratedDeriv_fun_mul hf hg]
  refine (norm_sum_le _ _).trans ?_
  have hsum : ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [← hsum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : ‖((n.choose i : ℕ) : 𝔸)‖ ≤ (n.choose i : ℝ) := by
    simpa using Nat.norm_cast_le (α := 𝔸) (n.choose i)
  calc ‖((n.choose i : ℕ) : 𝔸) * iteratedDeriv i f ξ * iteratedDeriv (n - i) g ξ‖
      ≤ ‖((n.choose i : ℕ) : 𝔸)‖ * (‖iteratedDeriv i f ξ‖ * ‖iteratedDeriv (n - i) g ξ‖) := by
        rw [mul_assoc]; refine (norm_mul_le _ _).trans ?_
        gcongr; exact norm_mul_le _ _
    _ ≤ (n.choose i : ℝ) * D := by
        have := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hD i hin)
        gcongr
        exact hD i hin

/-- Sharp bounds for derivatives of `(y - x^p)⁻¹` (order `≥ 1`). -/
theorem c09_aux_psi_inv_sharp (p : ℝ) (hp : 0 < p) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ C, 0 < C ∧ ∀ y ξ : ℝ, 0 < ξ → c * (|y| + ξ ^ p) ≤ |y - ξ ^ p| → ∀ i, 1 ≤ i → i ≤ N →
      ‖iteratedDeriv i (fun x : ℝ => (y - x ^ p)⁻¹) ξ‖ ≤
        C * ((|y| + ξ ^ p) ^ 2)⁻¹ * ξ ^ (p - i) := by
  obtain ⟨Cg, hCg, hb⟩ := c09_aux_psi_inv p hp c hc N
  obtain ⟨P, hP, hPb⟩ := c09_aux_rpow_derivs (p - 1) N
  refine ⟨4 ^ N * p * P * Cg ^ 2 + 1, by positivity, fun y ξ hξ hgood i hi1 hiN => ?_⟩
  have hξp := Real.rpow_pos_of_pos hξ p
  have hW : 0 < |y| + ξ ^ p := by positivity
  have hne : y - ξ ^ p ≠ 0 := by
    intro h; rw [h, abs_zero] at hgood; nlinarith
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [iteratedDeriv_succ', (c09_aux_psi_deriv p hp y ξ hξ hne).iteratedDeriv_eq]
  have hsm := c09_aux_psi_smooth p y ξ hξ hne
  have hgg' : ∀ i ≤ m, ‖iteratedDeriv i (fun x : ℝ => (y - x ^ p)⁻¹ * (y - x ^ p)⁻¹) ξ‖ ≤
      (2 ^ N * (Cg * (|y| + ξ ^ p)⁻¹) * (Cg * (|y| + ξ ^ p)⁻¹)) * ξ ^ ((0 : ℝ) + 0 - i) := by
    intro i hi
    refine (c09_aux_leib (fun x : ℝ => (y - x ^ p)⁻¹) (fun x : ℝ => (y - x ^ p)⁻¹) ξ hξ i
      (hsm.of_le (by exact_mod_cast le_top)) (hsm.of_le (by exact_mod_cast le_top))
      (Cg * (|y| + ξ ^ p)⁻¹) (Cg * (|y| + ξ ^ p)⁻¹) 0 0
      (fun k hk => hb y ξ hξ hgood k (by omega))
      (fun k hk => hb y ξ hξ hgood k (by omega))).trans ?_
    have : (2 : ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
    gcongr
  have hf1 : ∀ i ≤ m, ‖iteratedDeriv i (fun x : ℝ => p * x ^ (p - 1)) ξ‖ ≤
      (p * P) * ξ ^ ((p - 1) - i) := by
    intro i hi
    rw [iteratedDeriv_const_mul _ ((Real.contDiffAt_rpow_const_of_ne hξ.ne').of_le
      (by exact_mod_cast le_top)), norm_mul, Real.norm_eq_abs, abs_of_pos hp, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hPb ξ hξ i (by omega)) hp.le
  have key := c09_aux_leib (fun x : ℝ => p * x ^ (p - 1))
    (fun x : ℝ => (y - x ^ p)⁻¹ * (y - x ^ p)⁻¹) ξ hξ m
    (contDiffAt_const.mul ((Real.contDiffAt_rpow_const_of_ne hξ.ne').of_le
      (by exact_mod_cast le_top)))
    ((hsm.mul hsm).of_le (by exact_mod_cast le_top)) _ _ _ _ hf1 hgg'
  refine key.trans ?_
  have e : ξ ^ (p - 1 + (0 + 0) - (m : ℝ)) = ξ ^ (p - ((m + 1 : ℕ) : ℝ)) := by
    congr 1; push_cast; ring
  rw [e]
  have hpos : 0 < ξ ^ (p - ((m + 1 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hξ _
  have h2m : (2 : ℝ) ^ m ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
  have hWi : 0 < ((|y| + ξ ^ p) ^ 2)⁻¹ := by positivity
  calc 2 ^ m * (p * P) * (2 ^ N * (Cg * (|y| + ξ ^ p)⁻¹) * (Cg * (|y| + ξ ^ p)⁻¹)) *
        ξ ^ (p - ((m + 1 : ℕ) : ℝ))
      = (2 ^ m * 2 ^ N * p * P * Cg ^ 2) * ((|y| + ξ ^ p) ^ 2)⁻¹ *
          ξ ^ (p - ((m + 1 : ℕ) : ℝ)) := by rw [← inv_pow]; ring
    _ ≤ (4 ^ N * p * P * Cg ^ 2 + 1) * ((|y| + ξ ^ p) ^ 2)⁻¹ * ξ ^ (p - ((m + 1 : ℕ) : ℝ)) := by
        gcongr
        rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
        have : 2 ^ m * 2 ^ N * p * P * Cg ^ 2 ≤ 2 ^ N * 2 ^ N * p * P * Cg ^ 2 := by gcongr
        linarith

/-- The nonstationary constant. -/
theorem c09_aux_cs_pos (p : ℝ) (hp : 0 < p) : 0 < (1 - (100 / 101 : ℝ) ^ p) / 2 := by
  have hq : (100 / 101 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  linarith

/-- Iterated derivatives commute with `ℝ → ℂ` on an open set of smoothness. -/
theorem c09_aux_ofReal_iter (g : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (i : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv i g) U ∧
      ∀ x ∈ U, iteratedDeriv i (fun x => (g x : ℂ)) x = ((iteratedDeriv i g x : ℝ) : ℂ) := by
  induction i with
  | zero => exact ⟨by simpa using hg, fun x _ => by simp⟩
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd := (contDiffOn_infty_iff_deriv_of_isOpen hU).mp h1
    refine ⟨?_, fun x hx => ?_⟩
    · rw [iteratedDeriv_succ]; exact hd.2
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hev : iteratedDeriv i (fun x => (g x : ℂ)) =ᶠ[𝓝 x]
          fun x => ((iteratedDeriv i g x : ℝ) : ℂ) := by
        filter_upwards [hU.mem_nhds hx] with z hz using h2 z hz
      rw [hev.deriv_eq]
      have hdx : DifferentiableAt ℝ (iteratedDeriv i g) x :=
        (hd.1 x hx).differentiableAt (hU.mem_nhds hx)
      exact hdx.hasDerivAt.ofReal_comp.deriv

/-- Smoothness of `(y - x^p)⁻¹` as a complex function. -/
theorem c09_aux_psiC_smooth (p y ξ : ℝ) (hξ : 0 < ξ) (hne : y - ξ ^ p ≠ 0) :
    ContDiffAt ℝ ∞ (fun x : ℝ => (((y - x ^ p)⁻¹ : ℝ) : ℂ)) ξ :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp ξ (c09_aux_psi_smooth p y ξ hξ hne)

/-- Multiplying by `(y - x^p)⁻¹` in the nonstationary region costs `(|y|+ξ^p)⁻¹`. -/
theorem c09_aux_mul_psi (p : ℝ) (hp : 0 < p) (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ Cg, 0 < Cg ∧ ∀ y ξ : ℝ, 0 < ξ → c * (|y| + ξ ^ p) ≤ |y - ξ ^ p| →
      ∀ (F : ℝ → ℂ) (A a : ℝ), 0 ≤ A → ContDiffAt ℝ ∞ F ξ →
      (∀ i ≤ N, ‖iteratedDeriv i F ξ‖ ≤ A * ξ ^ (a - i)) → ∀ ℓ ≤ N,
      ‖iteratedDeriv ℓ (fun x => F x * (((y - x ^ p)⁻¹ : ℝ) : ℂ)) ξ‖ ≤
        2 ^ N * A * Cg * (|y| + ξ ^ p)⁻¹ * ξ ^ (a - ℓ) := by
  obtain ⟨Cg, hCg, hgb⟩ := c09_aux_psi_inv p hp c hc N
  refine ⟨Cg, hCg, fun y ξ hξ hgood F A a hA hF hFb ℓ hℓ => ?_⟩
  have hξp := Real.rpow_pos_of_pos hξ p
  have hW : 0 < |y| + ξ ^ p := by positivity
  have hne : y - ξ ^ p ≠ 0 := by
    intro h; rw [h, abs_zero] at hgood; nlinarith
  have hU : IsOpen (Ioi (0 : ℝ) ∩ {x : ℝ | y - x ^ p ≠ 0}) :=
    isOpen_Ioi.inter
      (isOpen_ne_fun (continuous_const.sub (Real.continuous_rpow_const hp.le)) continuous_const)
  have hgU : ContDiffOn ℝ ∞ (fun x : ℝ => (y - x ^ p)⁻¹) (Ioi (0 : ℝ) ∩ {x : ℝ | y - x ^ p ≠ 0}) :=
    fun x hx => (c09_aux_psi_smooth p y x hx.1 hx.2).contDiffWithinAt
  have key := c09_aux_leib F (fun x : ℝ => (((y - x ^ p)⁻¹ : ℝ) : ℂ)) ξ hξ ℓ
    (hF.of_le (by exact_mod_cast le_top))
    ((c09_aux_psiC_smooth p y ξ hξ hne).of_le (by exact_mod_cast le_top)) A
    (Cg * (|y| + ξ ^ p)⁻¹) a 0 (fun i hi => hFb i (by omega)) (fun i hi => by
      rw [(c09_aux_ofReal_iter _ _ hU hgU i).2 ξ ⟨hξ, hne⟩, Complex.norm_real]
      exact hgb y ξ hξ hgood i (by omega))
  refine key.trans (le_of_eq_of_le (b := 2 ^ ℓ * A * Cg * (|y| + ξ ^ p)⁻¹ * ξ ^ (a - ℓ))
    (by rw [add_zero]; ring) ?_)
  have : (2 : ℝ) ^ ℓ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hℓ
  gcongr

/-- `deriv` commutes with `ℝ → ℂ`. -/
theorem c09_aux_deriv_ofReal (r : ℝ → ℝ) (x : ℝ) :
    deriv (fun x => (r x : ℂ)) x = ((deriv r x : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ r x
  · exact h.hasDerivAt.ofReal_comp.deriv
  · have h' : ¬ DifferentiableAt ℝ (fun x => (r x : ℂ)) x := by
      intro hd
      apply h
      have : DifferentiableAt ℝ (fun x => Complex.reCLM (r x : ℂ)) x :=
        Complex.reCLM.differentiableAt.comp x hd
      simpa using this
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h']
    simp

/-- Blueprint: lem:c09_tail_expansion.  The operators `g₀ = 1/(iψ)`, `D^k g₀` with `Dh = h'/(iψ)`,
`ψ(η) = η^p - z`. -/
def c09_tail_expansion_D (p z : ℝ) : ℕ → ℝ → ℂ
  | 0 => fun η => 1 / (Complex.I * ((η ^ p - z : ℝ) : ℂ))
  | k + 1 => fun η => deriv (c09_tail_expansion_D p z k) η / (Complex.I * ((η ^ p - z : ℝ) : ℂ))

/-- Product form of `g₀ = 1/(iψ)`. -/
theorem c09_aux_D0_eq (p z : ℝ) : c09_tail_expansion_D p z 0 = fun x =>
    Complex.I * (((z - x ^ p)⁻¹ : ℝ) : ℂ) := by
  funext x
  simp only [c09_tail_expansion_D, one_div, mul_inv, Complex.inv_I, Complex.ofReal_inv]
  rw [show z - x ^ p = -(x ^ p - z) by ring, Complex.ofReal_neg, inv_neg]; ring

/-- Product form of `D^{k+1} g₀`. -/
theorem c09_aux_Dsucc_eq (p z : ℝ) (k : ℕ) : c09_tail_expansion_D p z (k + 1) = fun x =>
    (Complex.I * deriv (c09_tail_expansion_D p z k) x) * (((z - x ^ p)⁻¹ : ℝ) : ℂ) := by
  funext x
  simp only [c09_tail_expansion_D, div_eq_mul_inv, mul_inv, Complex.inv_I, Complex.ofReal_inv]
  rw [show z - x ^ p = -(x ^ p - z) by ring, Complex.ofReal_neg, inv_neg]; ring

/-- The open set where `ψ ≠ 0`. -/
theorem c09_aux_U_open (p : ℝ) (hp : 0 < p) (z : ℝ) :
    IsOpen (Ioi (0 : ℝ) ∩ {x : ℝ | z - x ^ p ≠ 0}) :=
  isOpen_Ioi.inter
    (isOpen_ne_fun (continuous_const.sub (Real.continuous_rpow_const hp.le)) continuous_const)

/-- `D^k g₀` is smooth where `ψ ≠ 0`. -/
theorem c09_aux_D_smooth (p : ℝ) (hp : 0 < p) (z : ℝ) (k : ℕ) :
    ContDiffOn ℝ ∞ (c09_tail_expansion_D p z k) (Ioi (0 : ℝ) ∩ {x : ℝ | z - x ^ p ≠ 0}) := by
  have hU := c09_aux_U_open p hp z
  induction k with
  | zero =>
    rw [c09_aux_D0_eq]
    exact fun x hx => (contDiffAt_const.mul (c09_aux_psiC_smooth p z x hx.1 hx.2)).contDiffWithinAt
  | succ k ih =>
    have hd := ((contDiffOn_infty_iff_deriv_of_isOpen hU).mp ih).2
    rw [c09_aux_Dsucc_eq]
    exact fun x hx => ((contDiffAt_const.mul ((hd x hx).contDiffAt (hU.mem_nhds hx))).mul
      (c09_aux_psiC_smooth p z x hx.1 hx.2)).contDiffWithinAt

/-- Symbol bounds for `D^k g₀`. -/
theorem c09_aux_D_bounds (p : ℝ) (hp : 0 < p) (c₁ : ℝ) (hc₁ : 0 < c₁) (k : ℕ) :
    ∀ N : ℕ, ∃ C, 0 < C ∧ ∀ z η : ℝ, 0 < η → c₁ * (|z| + η ^ p) ≤ |z - η ^ p| → ∀ ℓ ≤ N,
      ‖iteratedDeriv ℓ (c09_tail_expansion_D p z k) η‖ ≤
        C * ((|z| + η ^ p) ^ (k + 1))⁻¹ * η ^ (-(k : ℝ) - ℓ) := by
  have hU := c09_aux_U_open p hp
  induction k with
  | zero =>
    intro N
    obtain ⟨Cg, hCg, hm⟩ := c09_aux_mul_psi p hp c₁ hc₁ N
    refine ⟨2 ^ N * 1 * Cg, by positivity, fun z η hη hg ℓ hℓ => ?_⟩
    rw [c09_aux_D0_eq]
    refine (hm z η hη hg (fun _ => Complex.I) 1 0 zero_le_one contDiffAt_const
      (fun i hi => ?_) ℓ hℓ).trans (le_of_eq ?_)
    · rw [iteratedDeriv_const]
      split_ifs with h
      · subst h; simp
      · simp; positivity
    · simp
  | succ k ih =>
    intro N
    obtain ⟨C, hC, hCb⟩ := ih (N + 1)
    obtain ⟨Cg, hCg, hm⟩ := c09_aux_mul_psi p hp c₁ hc₁ N
    refine ⟨2 ^ N * C * Cg, by positivity, fun z η hη hg ℓ hℓ => ?_⟩
    have hηp := Real.rpow_pos_of_pos hη p
    have hW : 0 < |z| + η ^ p := by positivity
    have hne : z - η ^ p ≠ 0 := by
      intro h; rw [h, abs_zero] at hg; nlinarith
    have hd := ((contDiffOn_infty_iff_deriv_of_isOpen (hU z)).mp (c09_aux_D_smooth p hp z k)).2
    have hdA : ContDiffAt ℝ ∞ (deriv (c09_tail_expansion_D p z k)) η :=
      (hd η ⟨hη, hne⟩).contDiffAt ((hU z).mem_nhds ⟨hη, hne⟩)
    rw [c09_aux_Dsucc_eq]
    refine (hm z η hη hg (fun x => Complex.I * deriv (c09_tail_expansion_D p z k) x)
      (C * ((|z| + η ^ p) ^ (k + 1))⁻¹) (-((k + 1 : ℕ) : ℝ)) (by positivity)
      (contDiffAt_const.mul hdA) (fun i hi => ?_) ℓ hℓ).trans (le_of_eq ?_)
    · rw [iteratedDeriv_const_mul _ (hdA.of_le (by exact_mod_cast le_top)), norm_mul,
        Complex.norm_I, one_mul, ← iteratedDeriv_succ']
      refine (hCb z η hη hg (i + 1) (by omega)).trans (le_of_eq ?_)
      congr 2; push_cast; ring
    · rw [pow_succ _ (k + 1), mul_inv]; ring

/-- Propagation of the nonstationary condition. -/
theorem c09_aux_tail_prop (p : ℝ) (hp : 0 < p) (c₁ : ℝ) (hc₁' : c₁ ≤ 1) (z ξ₀ : ℝ)
    (hξ₀ : 0 < ξ₀) (hc : c₁ * (ξ₀ ^ p + |z|) ≤ ξ₀ ^ p - z) (η : ℝ) (hη : ξ₀ ≤ η) :
    c₁ * (η ^ p + |z|) ≤ η ^ p - z := by
  have h1 : ξ₀ ^ p ≤ η ^ p := Real.rpow_le_rpow hξ₀.le hη hp.le
  have h0 : 0 ≤ ξ₀ ^ p := (Real.rpow_pos_of_pos hξ₀ p).le
  nlinarith

/-- Derivative of the phase `Ψ_z`. -/
theorem c09_aux_phase_deriv (p : ℝ) (hp : 0 < p) (z η : ℝ) (hη : 0 < η) :
    HasDerivAt (c09_tail_integral_phase p z) (η ^ p - z) η := by
  have hev : c09_tail_integral_phase p z =ᶠ[𝓝 η] fun x => x ^ (p + 1) / (p + 1) - z * x := by
    filter_upwards [Ioi_mem_nhds hη] with x hx
    unfold c09_tail_integral_phase Phi0
    rw [abs_of_pos hx, Real.rpow_add_one hx.ne']; ring
  have h1 : HasDerivAt (fun x : ℝ => x ^ (p + 1) / (p + 1) - z * x)
      ((p + 1) * η ^ (p + 1 - 1) / (p + 1) - z * 1) η :=
    ((Real.hasDerivAt_rpow_const (Or.inl hη.ne')).div_const _).sub
      ((hasDerivAt_id η).const_mul z)
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq hev
  have : p + 1 ≠ 0 := by linarith
  field_simp; ring_nf

/-- Derivative of `e^{iΨ_z}`. -/
theorem c09_aux_exp_phase_deriv (p : ℝ) (hp : 0 < p) (z η : ℝ) (hη : 0 < η) :
    HasDerivAt (fun x => Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ)))
      (Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
        (Complex.I * ((η ^ p - z : ℝ) : ℂ))) η :=
  ((c09_aux_phase_deriv p hp z η hη).ofReal_comp.const_mul Complex.I).cexp

/-- `|e^{iΨ}| = 1`. -/
theorem c09_aux_norm_exp_phase (a : ℝ) : ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I a

/-- One integration by parts on `[ξ, ∞)`. -/
theorem c09_aux_tail_ibp (p : ℝ) (hp : 0 < p) (z ξ : ℝ) (hξ : 0 < ξ) (h D : ℝ → ℂ)
    (hD : ∀ η, ξ ≤ η → D η * (Complex.I * ((η ^ p - z : ℝ) : ℂ)) = h η)
    (hDd : ∀ η, ξ ≤ η → HasDerivAt D (deriv D η) η)
    (hDc : ContinuousOn (deriv D) (Ici ξ))
    (hlim : Tendsto D atTop (𝓝 0))
    (hint : IntegrableOn (fun η => Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
      deriv D η) (Ioi ξ)) :
    Tendsto (fun N => ∫ η in ξ..N, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
      h η) atTop
      (𝓝 (-(Complex.exp (Complex.I * (c09_tail_integral_phase p z ξ : ℂ)) * D ξ) -
        ∫ η in Ioi ξ, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
          deriv D η)) := by
  set e := fun x => Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ)) with he
  have hec : ContinuousOn e (Ici ξ) := fun x hx =>
    (c09_aux_exp_phase_deriv p hp z x (lt_of_lt_of_le hξ hx)).continuousAt.continuousWithinAt
  have hψc : ContinuousOn (fun x : ℝ => Complex.I * ((x ^ p - z : ℝ) : ℂ)) (Ici ξ) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const hp.le).sub continuous_const))).continuousOn
  have key : ∀ N, ξ ≤ N → ∫ η in ξ..N, e η * h η =
      D N * e N - D ξ * e ξ - ∫ η in ξ..N, deriv D η * e η := by
    intro N hN
    have hsub : uIcc ξ N ⊆ Ici ξ := by rw [uIcc_of_le hN]; exact Icc_subset_Ici_self
    have e1 : ∫ η in ξ..N, e η * h η =
        ∫ η in ξ..N, D η * (e η * (Complex.I * ((η ^ p - z : ℝ) : ℂ))) := by
      refine intervalIntegral.integral_congr fun η hη => ?_
      have hη' := hsub hη
      rw [← hD η hη']; ring
    rw [e1]
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun x hx => hDd x (hsub hx))
      (fun x hx => c09_aux_exp_phase_deriv p hp z x (lt_of_lt_of_le hξ (hsub hx)))
      ((hDc.mono hsub).intervalIntegrable)
      (((hec.mul hψc).mono hsub).intervalIntegrable)
  have hI := intervalIntegral_tendsto_integral_Ioi ξ hint tendsto_id
  have hDe : Tendsto (fun N => D N * e N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun N => ‖D N * e N‖) = fun N => ‖D N‖ := by
      funext N; rw [norm_mul, he]; simp only; rw [c09_aux_norm_exp_phase, mul_one]
    rw [this]; exact tendsto_zero_iff_norm_tendsto_zero.mp hlim
  have hfin : Tendsto (fun N => D N * e N - D ξ * e ξ - ∫ η in ξ..N, deriv D η * e η) atTop
      (𝓝 (-(e ξ * D ξ) - ∫ η in Ioi ξ, e η * deriv D η)) := by
    have h2 := (hDe.sub_const (D ξ * e ξ)).sub hI
    have ef : (fun N => D N * e N - D ξ * e ξ - ∫ η in ξ..N, deriv D η * e η) =
        fun N => D N * e N - D ξ * e ξ - ∫ η in ξ..id N, e η * deriv D η := by
      funext N; congr 1
      exact intervalIntegral.integral_congr fun η _ => by ring
    rw [ef]; convert h2 using 2; ring
  exact hfin.congr' (by filter_upwards [eventually_ge_atTop ξ] with N hN; exact (key N hN).symm)

/-- Continuity of `Ψ_z`. -/
theorem c09_aux_phase_cont (p : ℝ) (hp : 0 < p) (z : ℝ) :
    Continuous (c09_tail_integral_phase p z) := by
  unfold c09_tail_integral_phase Phi0
  have := Continuous.rpow_const continuous_abs (fun _ : ℝ => Or.inr hp.le)
  fun_prop

/-- Domination of the symbol bounds for `η ≥ ξ₀`. -/
theorem c09_aux_tail_dom (p : ℝ) (hp : 0 < p) (z ξ₀ : ℝ) (hξ₀ : 0 < ξ₀) (k j : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (η : ℝ) (hη : ξ₀ ≤ η) :
    C * ((|z| + η ^ p) ^ (k + 1))⁻¹ * η ^ (-(k : ℝ) - j) ≤
      (C * ((ξ₀ ^ p) ^ k)⁻¹ * ξ₀ ^ (-(k : ℝ))) * ((η ^ p)⁻¹ * η ^ (-(j : ℝ))) := by
  have hη0 : 0 < η := lt_of_lt_of_le hξ₀ hη
  have h1 : ξ₀ ^ p ≤ η ^ p := Real.rpow_le_rpow hξ₀.le hη hp.le
  have hξp := Real.rpow_pos_of_pos hξ₀ p
  have hηp := Real.rpow_pos_of_pos hη0 p
  have hW1 : η ^ p ≤ |z| + η ^ p := by linarith [abs_nonneg z]
  have hW2 : ξ₀ ^ p ≤ |z| + η ^ p := by linarith
  have e1 : η ^ (-(k : ℝ) - j) = η ^ (-(k : ℝ)) * η ^ (-(j : ℝ)) := by
    rw [← Real.rpow_add hη0]; ring_nf
  have h2 : η ^ (-(k : ℝ)) ≤ ξ₀ ^ (-(k : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hξ₀ hη (by simp)
  have h3 : ((|z| + η ^ p) ^ (k + 1))⁻¹ ≤ ((ξ₀ ^ p) ^ k)⁻¹ * (η ^ p)⁻¹ := by
    rw [pow_succ, mul_inv]
    gcongr
  rw [e1]
  have : 0 ≤ η ^ (-(j : ℝ)) := (Real.rpow_pos_of_pos hη0 _).le
  have : 0 ≤ η ^ (-(k : ℝ)) := (Real.rpow_pos_of_pos hη0 _).le
  calc C * ((|z| + η ^ p) ^ (k + 1))⁻¹ * (η ^ (-(k : ℝ)) * η ^ (-(j : ℝ)))
      ≤ C * (((ξ₀ ^ p) ^ k)⁻¹ * (η ^ p)⁻¹) * (ξ₀ ^ (-(k : ℝ)) * η ^ (-(j : ℝ))) := by gcongr
    _ = _ := by ring

/-! #### Van der Corput (second derivative test; copied from chapter 03) -/

/-- The derivative of a function monotone on `[c,d]` is nonnegative at interior points. -/
theorem c09_vdc_deriv_nonneg_of_monotoneOn {c d x : ℝ} {g : ℝ → ℝ} {g' : ℝ}
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
theorem c09_vdc_abs_arith (x y : ℝ) (h : 0 ≤ x * y) :
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
derivative `g'` on the open interval (the core estimate behind `c03_vdc_first`). -/
theorem c09_vdc_vdc1 {c d lam : ℝ} (hcd : c < d) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
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
        div_nonneg (c09_vdc_deriv_nonneg_of_monotoneOn hm hx (hgd x hx)) (sq_nonneg _)
      have : ∫ x in c..d, |k x| = ∫ x in c..d, -(-k x) := by
        rw [hIoo, hIoo]
        refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
        simp [abs_of_nonneg (hk0 x hx)]
      rw [this, intervalIntegral.integral_neg, hftc]
      rw [neg_sub]; exact le_abs_self _
    · have hk0 : ∀ x ∈ Ioo c d, k x ≤ 0 := fun x hx => by
        have := c09_vdc_deriv_nonneg_of_monotoneOn (g := fun x => -g x) hm.neg hx (hgd x hx).neg
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
        exact c09_vdc_abs_arith _ _ hsame

/-- `2 max(|x|⁻¹,|y|⁻¹) ≤ 2/λ` when `|x|,|y| ≥ λ`. -/
theorem c09_vdc_max_inv_le {lam x y : ℝ} (hlam : 0 < lam) (hx : lam ≤ |x|) (hy : lam ≤ |y|) :
    2 * max (|x|⁻¹) (|y|⁻¹) ≤ 2 / lam := by
  rw [div_eq_mul_inv]
  gcongr
  exact max_le (inv_anti₀ hlam hx) (inv_anti₀ hlam hy)

/-- First derivative test on `[c,d]`, `c ≤ d`, in the form `≤ 2/λ`. -/
theorem c09_vdc_vdc1' {c d lam : ℝ} (hcd : c ≤ d) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Icc c d)) (hgc : ContinuousOn g (Icc c d))
    (hg'c : ContinuousOn g' (Icc c d))
    (hΦd : ∀ x ∈ Ioo c d, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioo c d, HasDerivAt g (g' x) x)
    (hmono : MonotoneOn g (Icc c d) ∨ AntitoneOn g (Icc c d))
    (hlow : ∀ x ∈ Icc c d, lam ≤ |g x|) :
    ‖∫ x in c..d, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 2 / lam := by
  rcases hcd.lt_or_eq with hcd | rfl
  · exact (c09_vdc_vdc1 hcd hlam hΦc hgc hg'c hΦd hgd hmono hlow).trans
      (c09_vdc_max_inv_le hlam (hlow c ⟨le_rfl, hcd.le⟩) (hlow d ⟨hcd.le, le_rfl⟩))
  · simp; positivity

/-- Regularity data of a `C²` function on a set. -/
theorem c09_vdc_C2_setup {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ s) :
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
theorem c09_vdc_split {a b t : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hgc : ContinuousOn g (Icc a b)) :
    ∃ c ∈ Icc a b, (a < c → g c ≤ t) ∧ (c < b → t ≤ g c) := by
  by_cases h1 : t ≤ g a
  · exact ⟨a, ⟨le_rfl, hab⟩, fun h => absurd h (lt_irrefl a), fun _ => h1⟩
  by_cases h2 : g b ≤ t
  · exact ⟨b, ⟨hab, le_rfl⟩, fun _ => h2, fun h => absurd h (lt_irrefl b)⟩
  push Not at h1 h2
  obtain ⟨c, hc, hct⟩ := intermediate_value_Icc hab hgc ⟨h1.le, h2.le⟩
  exact ⟨c, hc, fun _ => hct.le, fun _ => hct.ge⟩

/-- Second derivative test, increasing case. -/
theorem c09_vdc_vdc2_inc {a b lam : ℝ} (hab : a < b) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
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
  obtain ⟨c₁, hc₁, hc₁a, hc₁b⟩ := c09_vdc_split (t := -s) hab.le hgc
  obtain ⟨c₂, hc₂, hc₂a, hc₂b⟩ := c09_vdc_split (t := s) hc₁.2 (hgc.mono (Icc_subset_Icc hc₁.1 le_rfl))
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
    · apply c09_vdc_vdc1' hc₁.1 hs0 (hΦc.mono hsub1) (hgc.mono hsub1) (hg'c.mono hsub1)
        (fun x hx => hΦd x (Ioo_subset_Ioo le_rfl hc₁.2 hx))
        (fun x hx => hgd x (Ioo_subset_Ioo le_rfl hc₁.2 hx)) (Or.inl (hgmono.mono hsub1))
      intro x hx
      have := hgmono (hsub1 hx) (hsub1 ⟨hc₁.1, le_rfl⟩) hx.2
      have := hc₁a h
      rw [abs_of_neg (by linarith)]; linarith
    · rw [← h]; simp; positivity
  have hp3 : ‖∫ x in c₂..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 2 / s := by
    rcases hc₂.2.lt_or_eq with h | h
    · apply c09_vdc_vdc1' hc₂.2 hs0 (hΦc.mono hsub3) (hgc.mono hsub3) (hg'c.mono hsub3)
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
theorem c09_vdc_sign {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
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
theorem c09_vdc_norm_integral_exp_neg (a b : ℝ) (Φ : ℝ → ℝ) :
    ‖∫ x in a..b, Complex.exp (Complex.I * ((-Φ x : ℝ) : ℂ))‖ =
      ‖∫ x in a..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ := by
  have h : ∀ x, Complex.exp (Complex.I * ((-Φ x : ℝ) : ℂ)) =
      (starRingEnd ℂ) (Complex.exp (Complex.I * (Φ x : ℂ))) := by
    intro x; rw [← Complex.exp_conj]; simp
  simp_rw [h]
  rw [intervalIntegral, intervalIntegral, integral_conj, integral_conj, ← map_sub,
    Complex.norm_conj]


/-- Van der Corput, second derivative test, in terms of explicit derivatives. -/
theorem c09_vdc_vdc2 {a b lam : ℝ} (hab : a < b) (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hg'c : ContinuousOn g' (Icc a b))
    (hΦd : ∀ x ∈ Ioo a b, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hlow : ∀ x ∈ Icc a b, lam ≤ |g' x|) :
    ‖∫ x in a..b, Complex.exp (Complex.I * (Φ x : ℂ))‖ ≤ 6 * lam ^ (-(1 / 2 : ℝ)) := by
  rcases c09_vdc_sign hg'c (fun x hx h => by
      have := hlow x hx; rw [h, abs_zero] at this; linarith) with hpos | hneg
  · exact c09_vdc_vdc2_inc hab hlam hΦc hgc hg'c hΦd hgd (fun x hx => by
      have := hlow x hx; rwa [abs_of_pos (hpos x hx)] at this)
  · rw [← c09_vdc_norm_integral_exp_neg]
    exact c09_vdc_vdc2_inc (Φ := fun x => -Φ x) (g := fun x => -g x) (g' := fun x => -g' x)
      hab hlam hΦc.neg hgc.neg hg'c.neg (fun x hx => (hΦd x hx).neg) (fun x hx => (hgd x hx).neg)
      (fun x hx => by have := hlow x hx; rwa [abs_of_neg (hneg x hx)] at this)

/-! #### The tail integrals `E_z` -/

/-- `f(η) = (z - η^p)⁻¹ → 0`. -/
theorem c09_aux_psi_inv_tendsto (p : ℝ) (hp : 0 < p) (z : ℝ) :
    Tendsto (fun η : ℝ => (z - η ^ p)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun η : ℝ => η ^ p - z) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_rpow_atTop hp)
  have := h1.inv_tendsto_atTop.neg
  rw [neg_zero] at this
  refine this.congr fun η => ?_
  simp only [Pi.inv_apply]; rw [← inv_neg, neg_sub]

/-- The far tail: for `a > 0` with `a^p > z`, the limit exists and is `≤ 2/(a^p - z)`. -/
theorem c09_aux_tail_far (p : ℝ) (hp : 0 < p) (z a : ℝ) (ha : 0 < a) (hψ : 0 < a ^ p - z) :
    ∃ L : ℂ, Tendsto (fun N => ∫ η in a..N,
        Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ))) atTop (𝓝 L) ∧
      ‖L‖ ≤ 2 / (a ^ p - z) := by
  set e := fun x => Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ)) with he
  set D := c09_tail_expansion_D p z 0 with hDdef
  set f := fun η : ℝ => (z - η ^ p)⁻¹ with hf
  have hU := c09_aux_U_open p hp z
  have hψη : ∀ η, a ≤ η → 0 < η ^ p - z := fun η hη => by
    have := Real.rpow_le_rpow ha.le hη hp.le; linarith
  have hmemU : ∀ η, a ≤ η → η ∈ Ioi (0 : ℝ) ∩ {x : ℝ | z - x ^ p ≠ 0} := fun η hη =>
    ⟨lt_of_lt_of_le ha hη, by have := hψη η hη; simp only [mem_ofPred_eq]; linarith⟩
  have hsubU : Ici a ⊆ Ioi (0 : ℝ) ∩ {x : ℝ | z - x ^ p ≠ 0} := fun η hη => hmemU η hη
  have hDd : ∀ η, a ≤ η → HasDerivAt D (deriv D η) η := fun η hη =>
    (((c09_aux_D_smooth p hp z 0) η (hmemU η hη)).differentiableWithinAt (by simp)
      |>.differentiableAt (hU.mem_nhds (hmemU η hη))).hasDerivAt
  have hDc : ContinuousOn (deriv D) (Ici a) :=
    ((c09_aux_D_smooth p hp z 0).continuousOn_deriv_of_isOpen hU (by simp)).mono hsubU
  -- the real derivative
  have hf' : ∀ η, a ≤ η → HasDerivAt f (p * η ^ (p - 1) * (f η * f η)) η := by
    intro η hη
    have hne : z - η ^ p ≠ 0 := (hmemU η hη).2
    have hd := ((c09_aux_psi_smooth p z η (lt_of_lt_of_le ha hη) hne).differentiableAt
      (by simp)).hasDerivAt
    rwa [(c09_aux_psi_deriv p hp z η (lt_of_lt_of_le ha hη) hne).eq_of_nhds] at hd
  have hDeq : ∀ η, a ≤ η → deriv D η = Complex.I * ((p * η ^ (p - 1) * (f η * f η) : ℝ) : ℂ) := by
    intro η hη
    rw [hDdef, c09_aux_D0_eq]
    exact ((hf' η hη).ofReal_comp.const_mul Complex.I).deriv
  have hpos : ∀ η, a ≤ η → 0 ≤ p * η ^ (p - 1) * (f η * f η) := fun η hη => by
    have := Real.rpow_pos_of_pos (lt_of_lt_of_le ha hη) (p - 1)
    have := mul_self_nonneg (f η); positivity
  have hfint : IntegrableOn (fun η => p * η ^ (p - 1) * (f η * f η)) (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun η hη => hf' η hη) (fun η hη => hpos η (le_of_lt hη))
      (c09_aux_psi_inv_tendsto p hp z)
  have hfval : ∫ η in Ioi a, p * η ^ (p - 1) * (f η * f η) = 1 / (a ^ p - z) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun η hη => hf' η hη) hfint
      (c09_aux_psi_inv_tendsto p hp z), hf]
    simp only; rw [zero_sub, ← inv_neg, neg_sub, one_div]
  have hnormD' : ∀ η, a ≤ η → ‖e η * deriv D η‖ = p * η ^ (p - 1) * (f η * f η) := by
    intro η hη
    rw [norm_mul, he]; simp only
    rw [c09_aux_norm_exp_phase, one_mul, hDeq η hη, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos η hη)]
  have hint : IntegrableOn (fun η => e η * deriv D η) (Ioi a) := by
    refine hfint.mono' ?_ ?_
    · exact (((continuous_const.mul (Complex.continuous_ofReal.comp
        (c09_aux_phase_cont p hp z))).cexp.continuousOn.mul hDc).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun η hη => ?_
      rw [hnormD' η (le_of_lt hη)]
  have hlim : Tendsto D atTop (𝓝 0) := by
    rw [hDdef, c09_aux_D0_eq]
    have := ((c09_aux_psi_inv_tendsto p hp z).ofReal).const_mul Complex.I
    simpa using this
  have hD0 : ∀ η, a ≤ η → D η * (Complex.I * ((η ^ p - z : ℝ) : ℂ)) = (fun _ => (1 : ℂ)) η := by
    intro η hη
    have : Complex.I * ((η ^ p - z : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (hψη η hη).ne')
    rw [hDdef]; simp only [c09_tail_expansion_D]; exact one_div_mul_cancel this
  have hbase := c09_aux_tail_ibp p hp z a ha (fun _ => 1) D hD0 hDd hDc hlim hint
  simp only [mul_one] at hbase
  refine ⟨_, hbase, ?_⟩
  have h1 : ‖Complex.exp (Complex.I * (c09_tail_integral_phase p z a : ℂ)) * D a‖ =
      1 / (a ^ p - z) := by
    rw [norm_mul, c09_aux_norm_exp_phase, one_mul, hDdef, c09_aux_D0_eq]
    simp only
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
      abs_sub_comm, abs_of_pos hψ, one_div]
  have h2 : ‖∫ η in Ioi a, e η * deriv D η‖ ≤ 1 / (a ^ p - z) := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← hfval]
    refine setIntegral_congr_fun measurableSet_Ioi fun η hη => hnormD' η (le_of_lt hη)
  calc ‖-(Complex.exp (Complex.I * (c09_tail_integral_phase p z a : ℂ)) * D a) -
        ∫ η in Ioi a, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
          deriv D η‖
      ≤ ‖Complex.exp (Complex.I * (c09_tail_integral_phase p z a : ℂ)) * D a‖ +
        ‖∫ η in Ioi a, e η * deriv D η‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ 1 / (a ^ p - z) + 1 / (a ^ p - z) := by rw [h1]; gcongr
    _ = 2 / (a ^ p - z) := by ring

/-- `e^{iΨ_z}` is continuous. -/
theorem c09_aux_e_cont (p : ℝ) (hp : 0 < p) (z : ℝ) :
    Continuous (fun x => Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ))) :=
  (continuous_const.mul (Complex.continuous_ofReal.comp (c09_aux_phase_cont p hp z))).cexp

/-- Splitting the tail integral at a nonstationary point `a`. -/
theorem c09_aux_tail_split (p : ℝ) (hp : 0 < p) (z a : ℝ) (ha : 0 < a) (hψ : 0 < a ^ p - z)
    (ξ : ℝ) :
    Tendsto (fun N => ∫ η in ξ..N, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)))
      atTop (𝓝 ((∫ η in ξ..a, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ))) +
        c09_tail_integral p z a)) ∧
    c09_tail_integral p z ξ =
      (∫ η in ξ..a, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ))) +
        c09_tail_integral p z a ∧
    ‖c09_tail_integral p z a‖ ≤ 2 / (a ^ p - z) := by
  obtain ⟨L, hL, hb⟩ := c09_aux_tail_far p hp z a ha hψ
  have hEa : c09_tail_integral p z a = L := hL.limUnder_eq
  have hc := c09_aux_e_cont p hp z
  have ht : Tendsto (fun N => ∫ η in ξ..N, Complex.exp (Complex.I *
      (c09_tail_integral_phase p z η : ℂ))) atTop
      (𝓝 ((∫ η in ξ..a, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ))) +
        c09_tail_integral p z a)) := by
    rw [hEa]
    refine (hL.const_add _).congr fun N => ?_
    exact intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
  exact ⟨ht, ht.limUnder_eq, hEa ▸ hb⟩

/-- The point `a_z = (|z|+1)^{1/p}`. -/
theorem c09_aux_az (p : ℝ) (hp : 0 < p) (z : ℝ) :
    0 < (|z| + 1) ^ (1 / p) ∧ ((|z| + 1) ^ (1 / p)) ^ p = |z| + 1 := by
  have h0 : 0 < |z| + 1 := by positivity
  refine ⟨Real.rpow_pos_of_pos h0 _, ?_⟩
  rw [← Real.rpow_mul h0.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- `E_z(ξ)` exists and is given by splitting at `a_z`. -/
theorem c09_aux_tail_exists (p : ℝ) (hp : 0 < p) (z ξ : ℝ) :
    Tendsto (fun N => ∫ η in ξ..N, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)))
      atTop (𝓝 (c09_tail_integral p z ξ)) := by
  obtain ⟨ha, hap⟩ := c09_aux_az p hp z
  have hψ : 0 < ((|z| + 1) ^ (1 / p)) ^ p - z := by rw [hap]; linarith [le_abs_self z]
  obtain ⟨h1, h2, -⟩ := c09_aux_tail_split p hp z _ ha hψ ξ
  rw [h2]; exact h1

/-- `‖E_z(ξ)‖ ≤ 2/(ξ^p - z)` when `ξ > 0`, `ξ^p > z`. -/
theorem c09_aux_tail_le (p : ℝ) (hp : 0 < p) (z ξ : ℝ) (hξ : 0 < ξ) (hψ : 0 < ξ ^ p - z) :
    ‖c09_tail_integral p z ξ‖ ≤ 2 / (ξ ^ p - z) :=
  (c09_aux_tail_split p hp z ξ hξ hψ ξ).2.2

/-- Uniform bound `‖E_z(ξ)‖ ≤ C_E w_E(z)` for `ξ > 0`. -/
theorem c09_aux_tail_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C_E, 0 < C_E ∧ ∀ z ξ : ℝ, 0 < ξ → ‖c09_tail_integral p z ξ‖ ≤ C_E * c09_weights_E p z := by
  have hp0 : 0 < p := by linarith
  set s := (1 - p) / (2 * p) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs, div_le_one (by linarith)]; linarith
  refine ⟨18 * p ^ (-(1 / 2 : ℝ)) + 2 + 3 * Real.sqrt 2, by positivity, fun z ξ hξ => ?_⟩
  have hjb1 : 1 ≤ jb z := c09_aux_one_le_jb z
  have hjbz : |z| ≤ jb z := by
    unfold jb; rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have hsq : 0 < Real.sqrt 2 := by positivity
  have hξp := Real.rpow_pos_of_pos hξ p
  have hc := c09_aux_e_cont p hp0 z
  set P := 18 * p ^ (-(1 / 2 : ℝ)) with hP
  have hP0 : 0 ≤ P := by positivity
  unfold c09_weights_E
  split_ifs with hz
  · -- `z ≤ 0`
    rw [Real.rpow_neg_one]
    have hjinv : 0 < (jb z)⁻¹ := inv_pos.mpr (c09_aux_jb_pos z)
    suffices h : ‖c09_tail_integral p z ξ‖ ≤ 3 * Real.sqrt 2 * (jb z)⁻¹ by
      refine h.trans ?_; nlinarith
    rcases le_or_gt 1 |z| with hz1 | hz1
    · have hψ : 0 < ξ ^ p - z := by linarith
      refine (c09_aux_tail_le p hp0 z ξ hξ hψ).trans ?_
      have hjle : jb z ≤ Real.sqrt 2 * |z| := by
        unfold jb
        rw [← Real.sqrt_sq (abs_nonneg z), ← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by nlinarith [sq_abs z])
      have hzabs : |z| = -z := abs_of_nonpos hz
      rw [div_le_iff₀ hψ]
      have h1 : 1 ≤ Real.sqrt 2 * |z| * (jb z)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (c09_aux_jb_pos z), one_mul]; exact hjle
      have h2 : 3 * Real.sqrt 2 * (jb z)⁻¹ * |z| ≤ 3 * Real.sqrt 2 * (jb z)⁻¹ * (ξ ^ p - z) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc (2 : ℝ) ≤ 3 * (Real.sqrt 2 * |z| * (jb z)⁻¹) := by linarith
        _ = 3 * Real.sqrt 2 * (jb z)⁻¹ * |z| := by ring
        _ ≤ _ := h2
    · have hjle : jb z ≤ Real.sqrt 2 := by
        unfold jb; exact Real.sqrt_le_sqrt (by nlinarith [sq_abs z, abs_nonneg z])
      have h1 : 1 ≤ Real.sqrt 2 * (jb z)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (c09_aux_jb_pos z), one_mul]; exact hjle
      suffices h : ‖c09_tail_integral p z ξ‖ ≤ 3 by nlinarith
      rcases le_or_gt 1 ξ with hξ1 | hξ1
      · have h1p : 1 ≤ ξ ^ p := Real.one_le_rpow hξ1 hp0.le
        refine (c09_aux_tail_le p hp0 z ξ hξ (by linarith)).trans ?_
        rw [div_le_iff₀ (by linarith)]; linarith
      · obtain ⟨-, h2, h3⟩ := c09_aux_tail_split p hp0 z 1 one_pos (by simp; linarith) ξ
        rw [h2]
        refine (norm_add_le _ _).trans ?_
        have h4 : ‖∫ η in ξ..1, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ))‖
            ≤ 1 := by
          refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
            fun x _ => (c09_aux_norm_exp_phase _).le).trans ?_
          rw [abs_of_pos (by linarith)]; linarith
        have h5 : 2 / ((1 : ℝ) ^ p - z) ≤ 2 := by
          rw [Real.one_rpow, div_le_iff₀ (by linarith)]; linarith
        linarith
  · -- `z > 0`
    push Not at hz
    have hjs : 1 ≤ jb z ^ s := Real.one_le_rpow hjb1 hs0
    set a := (2 * z + 1) ^ (1 / p) with ha
    have h2z : 0 < 2 * z + 1 := by linarith
    have ha0 : 0 < a := Real.rpow_pos_of_pos h2z _
    have hap : a ^ p = 2 * z + 1 := by
      rw [ha, ← Real.rpow_mul h2z.le, one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    rcases le_or_gt a ξ with haξ | haξ
    · have h1 : a ^ p ≤ ξ ^ p := Real.rpow_le_rpow ha0.le haξ hp0.le
      refine (c09_aux_tail_le p hp0 z ξ hξ (by linarith)).trans ?_
      have h5 : 1 ≤ ξ ^ p - z := by linarith
      rw [div_le_iff₀ (by linarith)]
      have h6 : 2 ≤ (P + 2 + 3 * Real.sqrt 2) * jb z ^ s := by nlinarith
      calc (2 : ℝ) ≤ (P + 2 + 3 * Real.sqrt 2) * jb z ^ s := h6
        _ = (P + 2 + 3 * Real.sqrt 2) * jb z ^ s * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)
    · obtain ⟨-, h2, h3⟩ := c09_aux_tail_split p hp0 z a ha0 (by rw [hap]; linarith) ξ
      rw [h2]
      refine (norm_add_le _ _).trans ?_
      have h3' : ‖c09_tail_integral p z a‖ ≤ 2 := by
        refine h3.trans ?_; rw [hap, div_le_iff₀ (by linarith)]; linarith
      -- van der Corput
      set lam := p * a ^ (p - 1) with hlam
      have hlam0 : 0 < lam := by positivity
      have hv := c09_vdc_vdc2 (a := ξ) (b := a) haξ hlam0
        (Φ := c09_tail_integral_phase p z) (g := fun x => x ^ p - z)
        (g' := fun x => p * x ^ (p - 1))
        (c09_aux_phase_cont p hp0 z).continuousOn
        ((Real.continuous_rpow_const hp0.le).sub continuous_const).continuousOn
        (fun x hx => (continuousAt_const.mul (Real.continuousAt_rpow_const _ _
          (Or.inl (lt_of_lt_of_le hξ hx.1).ne'))).continuousWithinAt)
        (fun x hx => c09_aux_phase_deriv p hp0 z x (lt_of_lt_of_le hξ hx.1.le))
        (fun x hx => by
          simpa using (Real.hasDerivAt_rpow_const (p := p)
            (Or.inl (lt_of_lt_of_le hξ hx.1.le).ne')).sub_const z)
        (fun x hx => by
          have hx0 : 0 < x := lt_of_lt_of_le hξ hx.1
          rw [abs_of_pos (by positivity)]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith))
            hp0.le)
      have hlamv : lam ^ (-(1 / 2 : ℝ)) = p ^ (-(1 / 2 : ℝ)) * (2 * z + 1) ^ s := by
        rw [hlam, Real.mul_rpow hp0.le (by positivity), ← Real.rpow_mul ha0.le, ha,
          ← Real.rpow_mul h2z.le, hs]
        congr 2; field_simp; ring
      have h3s : (2 * z + 1) ^ s ≤ 3 * jb z ^ s := by
        have e1 : 2 * z + 1 ≤ 3 * jb z := by rw [abs_of_pos hz] at hjbz; linarith
        calc (2 * z + 1) ^ s ≤ (3 * jb z) ^ s := Real.rpow_le_rpow h2z.le e1 hs0
          _ = 3 ^ s * jb z ^ s := Real.mul_rpow (by norm_num) (by linarith)
          _ ≤ 3 * jb z ^ s := by
              gcongr
              calc (3 : ℝ) ^ s ≤ 3 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
                _ = 3 := Real.rpow_one 3
      have hp12 : 0 < p ^ (-(1 / 2 : ℝ)) := by positivity
      rw [hlamv] at hv
      have : 6 * (p ^ (-(1 / 2 : ℝ)) * (2 * z + 1) ^ s) ≤ P * jb z ^ s := by
        rw [hP]; nlinarith
      nlinarith [Real.sqrt_nonneg 2]

/-- Joint continuity of `(z,η) ↦ e^{iΨ_z(η)}`. -/
theorem c09_aux_e_joint (p : ℝ) (hp : 0 < p) :
    Continuous (fun q : ℝ × ℝ =>
      Complex.exp (Complex.I * (c09_tail_integral_phase p q.1 q.2 : ℂ))) := by
  have hPhi : Continuous (Phi0 p) := by
    unfold Phi0
    have := Continuous.rpow_const continuous_abs (fun _ : ℝ => Or.inr hp.le)
    fun_prop
  unfold c09_tail_integral_phase
  have : Continuous (fun q : ℝ × ℝ => Phi0 p q.2 - q.1 * q.2) :=
    (hPhi.comp continuous_snd).sub (continuous_fst.mul continuous_snd)
  exact (continuous_const.mul (Complex.continuous_ofReal.comp this)).cexp

/-- Uncurried form of `c09_aux_e_joint`. -/
theorem c09_aux_e_uncurry (p : ℝ) (hp : 0 < p) :
    Continuous (Function.uncurry fun (q : ℝ × ℝ) (η : ℝ) =>
      Complex.exp (Complex.I * (c09_tail_integral_phase p q.1 η : ℂ))) := by
  have hm : Continuous (fun x : (ℝ × ℝ) × ℝ => (x.1.1, x.2)) := by fun_prop
  have := (c09_aux_e_joint p hp).comp hm
  exact this

/-- Joint continuity of `(z,ξ) ↦ E_z(ξ)`. -/
theorem c09_aux_tail_joint (p : ℝ) (hp : 0 < p) :
    Continuous (fun q : ℝ × ℝ => c09_tail_integral p q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z₀, ξ₀⟩
  set V : Set (ℝ × ℝ) := Metric.ball z₀ 1 ×ˢ univ with hV
  have hVo : IsOpen V := Metric.isOpen_ball.prod isOpen_univ
  have hmem : (z₀, ξ₀) ∈ V := ⟨Metric.mem_ball_self one_pos, mem_univ _⟩
  set F : ℝ → ℝ × ℝ → ℂ := fun N q => ∫ η in q.2..N,
    Complex.exp (Complex.I * (c09_tail_integral_phase p q.1 η : ℂ)) with hF
  have hFc : ∀ N, Continuous (F N) := by
    intro N
    have hj := c09_aux_e_uncurry p hp
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) (a₀ := N) hj (s := fun q : ℝ × ℝ => q.2) continuous_snd
    refine h.neg.congr fun q => ?_
    rw [hF]; simp only; rw [intervalIntegral.integral_symm]; rfl
  have hpow : Tendsto (fun N : ℝ => N ^ p - (|z₀| + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_rpow_atTop hp)
  have hU : TendstoUniformlyOn F (fun q => c09_tail_integral p q.1 q.2) atTop V := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h2 : Tendsto (fun N : ℝ => 2 / (N ^ p - (|z₀| + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hpow
    filter_upwards [h2.eventually (gt_mem_nhds hε), hpow.eventually_gt_atTop 0,
      eventually_gt_atTop 0] with N hN hN1 hN0
    rintro ⟨z, ξ⟩ ⟨hz, -⟩
    have hz' : |z - z₀| < 1 := by simpa [Real.dist_eq] using hz
    have hzle : z ≤ |z₀| + 1 := by
      have := abs_lt.mp hz'; linarith [le_abs_self z₀]
    have hψ : 0 < N ^ p - z := by linarith
    obtain ⟨-, h2, h3⟩ := c09_aux_tail_split p hp z N hN0 hψ ξ
    simp only
    rw [h2, dist_eq_norm, hF]
    simp only
    rw [add_sub_cancel_left]
    refine lt_of_le_of_lt (h3.trans ?_) hN
    exact div_le_div_of_nonneg_left (by norm_num) hN1 (by linarith)
  have hcont := hU.continuousOn (Frequently.of_forall fun N => (hFc N).continuousOn)
  exact hcont.continuousAt (hVo.mem_nhds hmem)

/-- `∂_ξ E_z(ξ) = -e^{iΨ_z(ξ)}`. -/
theorem c09_aux_tail_deriv (p : ℝ) (hp : 0 < p) (z ξ : ℝ) :
    HasDerivAt (c09_tail_integral p z)
      (-Complex.exp (Complex.I * (c09_tail_integral_phase p z ξ : ℂ))) ξ := by
  obtain ⟨ha, hap⟩ := c09_aux_az p hp z
  have hψ : 0 < ((|z| + 1) ^ (1 / p)) ^ p - z := by rw [hap]; linarith [le_abs_self z]
  have hc := c09_aux_e_cont p hp z
  have he : c09_tail_integral p z = fun ξ => (∫ η in ξ..(|z| + 1) ^ (1 / p),
      Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ))) +
        c09_tail_integral p z ((|z| + 1) ^ (1 / p)) :=
    funext fun ξ => (c09_aux_tail_split p hp z _ ha hψ ξ).2.1
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).add_const _

/-- Blueprint: lem:c09_tail_basic.  Existence, continuity, decay and derivative of `E_z`;
the bound `|E_z(ξ)| ≤ C_E w_E(z)`; continuity, boundedness and decay of `F_G`. -/
theorem c09_tail_basic (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    -- (1)
    (∀ z ξ : ℝ, 0 ≤ ξ → Tendsto (fun N : ℝ => ∫ η in ξ..N,
        Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ))) atTop
        (nhds (c09_tail_integral p z ξ))) ∧
    ContinuousOn (fun q : ℝ × ℝ => c09_tail_integral p q.1 q.2) (univ ×ˢ Ici 0) ∧
    (∀ z : ℝ, Tendsto (c09_tail_integral p z) atTop (nhds 0)) ∧
    (∀ z ξ : ℝ, 0 ≤ ξ → HasDerivWithinAt (c09_tail_integral p z)
        (-Complex.exp (Complex.I * (c09_tail_integral_phase p z ξ : ℂ))) (Ici 0) ξ) ∧
    -- (2)
    (∃ C_E, 0 < C_E ∧ ∀ z ξ : ℝ, 0 ≤ ξ → ‖c09_tail_integral p z ξ‖ ≤ C_E * c09_weights_E p z) ∧
    -- (3)
    (∀ γ, admissibleGamma p γ → ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma p γ,
      ContinuousOn (c09_tail_integral_F p G) (Ici 0) ∧
      (∀ ξ, 0 ≤ ξ → ‖c09_tail_integral_F p G ξ‖ ≤ C * yNorm p γ G) ∧
      Tendsto (c09_tail_integral_F p G) atTop (nhds 0)) := by
  have hp0 : 0 < p := by linarith
  have hjoint := c09_aux_tail_joint p hp0
  have hdecay : ∀ z : ℝ, Tendsto (c09_tail_integral p z) atTop (nhds 0) := by
    intro z
    obtain ⟨ha, hap⟩ := c09_aux_az p hp0 z
    have hpow : Tendsto (fun ξ : ℝ => ξ ^ p - z) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_rpow_atTop hp0)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hpow)
    filter_upwards [hpow.eventually_gt_atTop 0, eventually_gt_atTop 0] with ξ h1 h2
    exact c09_aux_tail_le p hp0 z ξ h2 h1
  obtain ⟨C_E, hCE, hCEb⟩ := c09_aux_tail_bound p hp hp1
  have hbound : ∀ z ξ : ℝ, 0 ≤ ξ → ‖c09_tail_integral p z ξ‖ ≤ C_E * c09_weights_E p z := by
    intro z ξ hξ
    rcases hξ.lt_or_eq with hξ | rfl
    · exact hCEb z ξ hξ
    · have hc : Tendsto (fun ξ => ‖c09_tail_integral p z ξ‖) (𝓝[>] 0)
          (𝓝 ‖c09_tail_integral p z 0‖) :=
        ((c09_aux_tail_deriv p hp0 z 0).continuousAt.norm).mono_left nhdsWithin_le_nhds
      exact le_of_tendsto hc (eventually_nhdsWithin_of_forall fun ξ hξ => hCEb z ξ hξ)
  refine ⟨fun z ξ _ => c09_aux_tail_exists p hp0 z ξ, hjoint.continuousOn, hdecay,
    fun z ξ _ => (c09_aux_tail_deriv p hp0 z ξ).hasDerivWithinAt, ⟨C_E, hCE, hbound⟩, ?_⟩
  intro γ hγ
  obtain ⟨-, -, -, ⟨CL, hCL, hL1⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
  refine ⟨C_E * CL, by positivity, fun G hG => ?_⟩
  obtain ⟨iG, iG', iGw, hsum⟩ := hL1 G hG
  set bound : ℝ → ℝ := fun z => C_E * (|deriv G z| * c09_weights_E p z) with hbd
  have ib : Integrable bound := iGw.const_mul C_E
  have hmeas : ∀ ξ, AEStronglyMeasurable
      (fun z => ((deriv G z : ℝ) : ℂ) * c09_tail_integral p z ξ) volume := by
    intro ξ
    refine (Complex.measurable_ofReal.comp (measurable_deriv G)).aestronglyMeasurable.mul ?_
    exact (hjoint.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hb : ∀ ξ, 0 ≤ ξ → ∀ z, ‖((deriv G z : ℝ) : ℂ) * c09_tail_integral p z ξ‖ ≤ bound z := by
    intro ξ hξ z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hbd]
    have := hbound z ξ hξ
    calc |deriv G z| * ‖c09_tail_integral p z ξ‖ ≤ |deriv G z| * (C_E * c09_weights_E p z) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = C_E * (|deriv G z| * c09_weights_E p z) := by ring
  refine ⟨?_, fun ξ hξ => ?_, ?_⟩
  · refine continuousOn_of_dominated (fun ξ _ => hmeas ξ)
      (fun ξ hξ => Eventually.of_forall (hb ξ hξ)) ib (Eventually.of_forall fun z => ?_)
    exact continuousOn_const.mul
      (hjoint.comp (continuous_const.prodMk continuous_id)).continuousOn
  · unfold c09_tail_integral_F
    refine (norm_integral_le_of_norm_le ib (Eventually.of_forall (hb ξ hξ))).trans ?_
    rw [hbd, integral_const_mul]
    have h0 : 0 ≤ ∫ z, |G z| := integral_nonneg fun _ => abs_nonneg _
    have h1 : 0 ≤ ∫ z, |deriv G z| := integral_nonneg fun _ => abs_nonneg _
    have : ∫ z, |deriv G z| * c09_weights_E p z ≤ CL * yNorm p γ G := by linarith
    calc C_E * ∫ z, |deriv G z| * c09_weights_E p z ≤ C_E * (CL * yNorm p γ G) :=
          mul_le_mul_of_nonneg_left this hCE.le
      _ = C_E * CL * yNorm p γ G := by ring
  · have := tendsto_integral_filter_of_dominated_convergence bound
      (Eventually.of_forall hmeas)
      ((eventually_ge_atTop 0).mono fun ξ hξ => Eventually.of_forall (hb ξ hξ)) ib
      (Eventually.of_forall fun z => ((hdecay z).const_mul ((deriv G z : ℝ) : ℂ)))
    unfold c09_tail_integral_F
    simpa using this

/-! #### Helpers for the tail formula -/

/-- Absolute continuity of locally Lipschitz and of smooth real functions on intervals. -/
theorem c09_aux_ac_of_locLip (f : ℝ → ℝ) (hf : LocallyLipschitz f) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := (hf.locallyLipschitzOn (s := uIcc a b)).exists_lipschitzOnWith_of_compact
    isCompact_uIcc
  exact hK.absolutelyContinuousOnInterval

/-- `e^{-ixη} = cos(xη) - i sin(xη)`. -/
theorem c09_aux_exp_cos_sin (x η : ℝ) : Complex.exp (-(Complex.I * (x : ℂ) * (η : ℂ))) =
    ((Real.cos (x * η) : ℝ) : ℂ) - Complex.I * ((Real.sin (x * η) : ℝ) : ℂ) := by
  have : -(Complex.I * (x : ℂ) * (η : ℂ)) = ((-(x * η) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast; ring

/-- Splitting `∫ u e^{-ixη}` into real integrals. -/
theorem c09_aux_split_int (u : ℝ → ℝ) (a b η : ℝ) (hu : IntervalIntegrable u volume a b) :
    ∫ x in a..b, ((u x : ℝ) : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (η : ℂ))) =
      ((∫ x in a..b, u x * Real.cos (x * η) : ℝ) : ℂ) -
        Complex.I * ((∫ x in a..b, u x * Real.sin (x * η) : ℝ) : ℂ) := by
  have hc : IntervalIntegrable (fun x => u x * Real.cos (x * η)) volume a b :=
    hu.mul_continuousOn (by fun_prop)
  have hs : IntervalIntegrable (fun x => u x * Real.sin (x * η)) volume a b :=
    hu.mul_continuousOn (by fun_prop)
  simp_rw [c09_aux_exp_cos_sin]
  have e : (fun x => ((u x : ℝ) : ℂ) * (((Real.cos (x * η) : ℝ) : ℂ) -
      Complex.I * ((Real.sin (x * η) : ℝ) : ℂ))) = fun x =>
      (((u x * Real.cos (x * η) : ℝ)) : ℂ) - Complex.I * (((u x * Real.sin (x * η)) : ℝ) : ℂ) := by
    funext x; push_cast; ring
  have hc' : IntervalIntegrable (fun x => ((u x * Real.cos (x * η) : ℝ) : ℂ)) volume a b :=
    ⟨hc.1.ofReal, hc.2.ofReal⟩
  have hs' : IntervalIntegrable (fun x => Complex.I * ((u x * Real.sin (x * η) : ℝ) : ℂ))
      volume a b := (show IntervalIntegrable (fun x => ((u x * Real.sin (x * η) : ℝ) : ℂ))
        volume a b from ⟨hs.1.ofReal, hs.2.ofReal⟩).const_mul _
  rw [e, intervalIntegral.integral_sub hc' hs',
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]

/-- Finite integration by parts against `e^{-ixη}`. -/
theorem c09_aux_ibp_fourier (G : ℝ → ℝ) (hG : LocallyLipschitz G) (a b η : ℝ) :
    ∫ x in a..b, ((deriv G x : ℝ) : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (η : ℂ))) =
      (G b : ℂ) * Complex.exp (-(Complex.I * (b : ℂ) * (η : ℂ))) -
        (G a : ℂ) * Complex.exp (-(Complex.I * (a : ℂ) * (η : ℂ))) +
      Complex.I * η * ∫ x in a..b, ((G x : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (x : ℂ) * (η : ℂ))) := by
  have hGac := c09_aux_ac_of_locLip G hG a b
  have hsm : ∀ g : ℝ → ℝ, ContDiff ℝ 1 g → AbsolutelyContinuousOnInterval g a b := fun g hg => by
    obtain ⟨K, hK⟩ := hg.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_uIcc a b)
      isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval
  have hcac := hsm (fun x => Real.cos (x * η)) (by fun_prop)
  have hsac := hsm (fun x => Real.sin (x * η)) (by fun_prop)
  have dc : ∀ x, deriv (fun x => Real.cos (x * η)) x = -(Real.sin (x * η) * η) := fun x => by
    have := ((hasDerivAt_id x).mul_const η).cos
    simp
  have ds : ∀ x, deriv (fun x => Real.sin (x * η)) x = Real.cos (x * η) * η := fun x => by
    have := ((hasDerivAt_id x).mul_const η).sin
    simp
  have i1 := hGac.integral_mul_deriv_eq_deriv_mul hcac
  have i2 := hGac.integral_mul_deriv_eq_deriv_mul hsac
  simp only [dc, ds] at i1 i2
  have hGi : IntervalIntegrable G volume a b := hGac.continuousOn.intervalIntegrable
  have hG'i : IntervalIntegrable (deriv G) volume a b := hGac.intervalIntegrable_deriv
  rw [c09_aux_split_int _ a b η hG'i, c09_aux_split_int _ a b η hGi,
    c09_aux_exp_cos_sin, c09_aux_exp_cos_sin]
  have e1 : ∫ x in a..b, G x * -(Real.sin (x * η) * η) = -η * ∫ x in a..b, G x * Real.sin (x * η) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x in a..b, G x * (Real.cos (x * η) * η) = η * ∫ x in a..b, G x * Real.cos (x * η) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  rw [e1] at i1; rw [e2] at i2
  have r1 : ∫ x in a..b, deriv G x * Real.cos (x * η) =
      G b * Real.cos (b * η) - G a * Real.cos (a * η) + η * ∫ x in a..b, G x * Real.sin (x * η) := by
    linarith
  have r2 : ∫ x in a..b, deriv G x * Real.sin (x * η) =
      G b * Real.sin (b * η) - G a * Real.sin (a * η) - η * ∫ x in a..b, G x * Real.cos (x * η) := by
    linarith
  rw [r1, r2]
  push_cast
  linear_combination ((η : ℂ) * ((∫ x in a..b, G x * Real.sin (x * η) : ℝ) : ℂ)) * Complex.I_sq

/-- `|z| ≤ ⟨z⟩`. -/
theorem c09_aux_abs_le_jb' (z : ℝ) : |z| ≤ jb z := by
  unfold jb; exact Real.abs_le_sqrt (by nlinarith)

/-- `G ∈ Y_γ` tends to `0` at `±∞`. -/
theorem c09_aux_Y_tendsto (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) :
    Tendsto G atTop (𝓝 0) ∧ Tendsto G atBot (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hγ0 : 0 < γ := by
    have : 0 < beta p := by unfold beta; positivity
    have : 0 < 1 / p := by positivity
    linarith [hγ.1]
  obtain ⟨-, -, h2, -⟩ := c09_weight_facts p hp hp1 γ hγ
  have hb := (h2 G hG).1
  set M := yNorm p γ G
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have key : ∀ y : ℝ, y ≠ 0 → |G y| ≤ M * |y| ^ (-γ) := by
    intro y hy
    refine (hb y).trans ?_
    rw [c09_aux_w0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hy)
      (c09_aux_abs_le_jb' y) (show -γ ≤ 0 by linarith)) hM
  have hlim : Tendsto (fun t : ℝ => M * t ^ (-γ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hγ0).const_mul M
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with y hy
    have := key y hy.ne'
    rwa [abs_of_pos hy] at this
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (hlim.comp tendsto_abs_atBot_atTop)
    filter_upwards [eventually_lt_atBot 0] with y hy
    exact key y hy.ne

/-- `\widehat{G'}(η) = iη Ĝ(η)` for `G ∈ Y_γ`. -/
theorem c09_aux_fourier_deriv (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (η : ℝ) :
    fourierT (fun x => ((deriv G x : ℝ) : ℂ)) η =
      Complex.I * η * fourierT (fun x => ((G x : ℝ) : ℂ)) η := by
  obtain ⟨-, -, -, ⟨CL, -, hL1⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
  obtain ⟨iG, iG', -, -⟩ := hL1 G hG
  obtain ⟨hGt, hGb⟩ := c09_aux_Y_tendsto p hp hp1 γ hγ G hG
  have hc : Continuous fun x : ℝ => Complex.exp (-(Complex.I * (x : ℂ) * (η : ℂ))) := by fun_prop
  have hint : ∀ u : ℝ → ℝ, Integrable u →
      Integrable (fun x => ((u x : ℝ) : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (η : ℂ)))) :=
    fun u hu => hu.ofReal.mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun x => (c09_aux_norm_exp_neg x η).le)
  have t1 := intervalIntegral_tendsto_integral (hint _ iG') tendsto_neg_atTop_atBot tendsto_id
  have t2 := intervalIntegral_tendsto_integral (hint _ iG) tendsto_neg_atTop_atBot tendsto_id
  have hbd : ∀ (f : ℝ → ℝ) (l : Filter ℝ) (a : ℝ → ℝ), Tendsto f l (𝓝 0) →
      Tendsto (fun R => (f R : ℂ) * Complex.exp (-(Complex.I * (a R : ℂ) * (η : ℂ)))) l (𝓝 0) := by
    intro f l a hf
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun R => ‖(f R : ℂ) * Complex.exp (-(Complex.I * (a R : ℂ) * (η : ℂ)))‖) =
        fun R => ‖f R‖ := by
      funext R; rw [norm_mul, c09_aux_norm_exp_neg, mul_one, Complex.norm_real]
    rw [this]; exact tendsto_zero_iff_norm_tendsto_zero.mp hf
  have t3 := ((hbd G atTop id hGt).sub (hbd (fun R => G (-R)) atTop (fun R => -R)
    (hGb.comp tendsto_neg_atTop_atBot))).add (t2.const_mul (Complex.I * η))
  rw [sub_zero, zero_add] at t3
  refine tendsto_nhds_unique t1 (t3.congr fun R => ?_)
  simp only [id]
  rw [c09_aux_ibp_fourier G hG.1 (-R) R η]

/-- `∫_ξ^Ξ e^{iΨ_z} = E_z(ξ) - E_z(Ξ)`. -/
theorem c09_aux_tail_diff (p : ℝ) (hp : 0 < p) (z ξ Ξ : ℝ) :
    ∫ η in ξ..Ξ, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) =
      c09_tail_integral p z ξ - c09_tail_integral p z Ξ := by
  obtain ⟨ha, hap⟩ := c09_aux_az p hp z
  have hψ : 0 < ((|z| + 1) ^ (1 / p)) ^ p - z := by rw [hap]; linarith [le_abs_self z]
  rw [(c09_aux_tail_split p hp z _ ha hψ ξ).2.1, (c09_aux_tail_split p hp z _ ha hψ Ξ).2.1]
  have hc := c09_aux_e_cont p hp z
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable ξ Ξ)
    (hc.intervalIntegrable Ξ ((|z| + 1) ^ (1 / p)))]
  ring

/-- Swapped joint continuity of `e^{iΨ_z(η)}`. -/
theorem c09_aux_e_swap (p : ℝ) (hp : 0 < p) :
    Continuous (fun q : ℝ × ℝ =>
      Complex.exp (Complex.I * (c09_tail_integral_phase p q.2 q.1 : ℂ))) := by
  have hm : Continuous (fun q : ℝ × ℝ => (q.2, q.1)) := by fun_prop
  have := (c09_aux_e_joint p hp).comp hm
  exact this

/-- Item (1) of the tail formula (Fubini). -/
theorem c09_aux_tail_formula1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (ξ Ξ : ℝ) (hξ : 0 ≤ ξ)
    (hΞ : ξ ≤ Ξ) :
    ∫ η in ξ..Ξ, (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
        fourierT (fun x => (G x : ℂ)) η =
      -Complex.I * (c09_tail_integral_F p G ξ - c09_tail_integral_F p G Ξ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, ⟨CL, -, hL1⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
  obtain ⟨iG, iG', iGw, -⟩ := hL1 G hG
  obtain ⟨-, -, -, -, ⟨C_E, hCE, hEb⟩, -⟩ := c09_tail_basic p hp hp1
  -- integrand rewriting
  have e1 : ∀ η : ℝ, (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
      fourierT (fun x => (G x : ℂ)) η =
      -Complex.I * ∫ z, ((deriv G z : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) := by
    intro η
    have hF := c09_aux_fourier_deriv p hp hp1 γ hγ G hG η
    have h1 : (η : ℂ) * fourierT (fun x => (G x : ℂ)) η =
        -Complex.I * fourierT (fun x => ((deriv G x : ℝ) : ℂ)) η := by
      rw [hF]; ring_nf; rw [Complex.I_sq]; ring
    have h2 : ∫ z, ((deriv G z : ℝ) : ℂ) *
        Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) =
        Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
          fourierT (fun x => ((deriv G x : ℝ) : ℂ)) η := by
      unfold fourierT
      rw [← integral_const_mul]
      congr 1; funext z
      unfold c09_tail_integral_phase
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [h2, mul_right_comm, h1]; ring
  rw [intervalIntegral.integral_congr (fun η _ => e1 η), intervalIntegral.integral_const_mul]
  congr 1
  set f : ℝ → ℝ → ℂ := fun η z => ((deriv G z : ℝ) : ℂ) *
    Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) with hf
  have hfi : Integrable (Function.uncurry f) ((volume.restrict (uIoc ξ Ξ)).prod volume) := by
    have : IsFiniteMeasure (volume.restrict (uIoc ξ Ξ)) :=
      isFiniteMeasure_restrict.mpr (by rw [uIoc_of_le hΞ]; exact measure_Ioc_lt_top.ne)
    refine (iG'.norm.comp_snd (volume.restrict (uIoc ξ Ξ))).mono' ?_
      (Eventually.of_forall fun q => ?_)
    · have hj := c09_aux_e_swap p hp0
      exact ((Complex.measurable_ofReal.comp ((measurable_deriv G).comp measurable_snd)).mul
        hj.measurable).aestronglyMeasurable
    · simp only [Function.uncurry, hf]
      rw [norm_mul, c09_aux_norm_exp_phase, mul_one, Complex.norm_real]
  rw [intervalIntegral_integral_swap hfi]
  have hEint : ∀ t, 0 ≤ t → Integrable (fun z => ((deriv G z : ℝ) : ℂ) * c09_tail_integral p z t) := by
    intro t ht
    refine (iGw.const_mul C_E).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact (Complex.measurable_ofReal.comp (measurable_deriv G)).aestronglyMeasurable.mul
        ((c09_aux_tail_joint p hp0).comp (continuous_id.prodMk continuous_const)
          ).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |deriv G z| * ‖c09_tail_integral p z t‖ ≤ |deriv G z| * (C_E * c09_weights_E p z) :=
            mul_le_mul_of_nonneg_left (hEb z t ht) (abs_nonneg _)
        _ = C_E * (|deriv G z| * c09_weights_E p z) := by ring
  unfold c09_tail_integral_F
  rw [← integral_sub (hEint ξ hξ) (hEint Ξ (hξ.trans hΞ))]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hf]
  rw [intervalIntegral.integral_const_mul, c09_aux_tail_diff p hp0 z ξ Ξ, mul_sub]

/-- Homogeneity `Φ₀(ξt) = t^{p+1} Φ₀(ξ)` for `t ≥ 0`, `ξ > 0`. -/
theorem c09_aux_Phi0_scale (p : ℝ) (hp : 0 < p) (ξ t : ℝ) (hξ : 0 < ξ) (ht : 0 ≤ t) :
    Phi0 p (ξ * t) = t ^ (p + 1) * Phi0 p ξ := by
  unfold Phi0
  rw [abs_of_nonneg (by positivity), abs_of_pos hξ, Real.mul_rpow hξ.le ht,
    Real.rpow_add' ht (by linarith), Real.rpow_one]
  ring

/-- Blueprint: lem:c09_tail_formula.  The tail formula: `∫_ξ^Ξ η e^{iΦ₀} Ĝ = -i(F_G(ξ)-F_G(Ξ))`,
`ℓ(G) = -i F_G(0)` (with existence of the limit), `m_G(ξ) = ξ⁻² e^{-iΦ₀(ξ)}(ℓ(G) + i F_G(ξ))`, and
for `G ∈ Ỹ_γ` the formula and the bound `|\widehat{𝒯₊G}(ξ)| ≤ C‖G‖ 𝟙_{ξ>1} ξ⁻²`. -/
theorem c09_tail_formula (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma p γ,
      -- (1)
      (∀ ξ Ξ : ℝ, 0 ≤ ξ → ξ < Ξ →
        ∫ η in ξ..Ξ, (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
            fourierT (fun x => (G x : ℂ)) η =
          -Complex.I * (c09_tail_integral_F p G ξ - c09_tail_integral_F p G Ξ)) ∧
      -- (2)
      Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
          (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ)
        atTop (nhds (ell p G)) ∧
      ell p G = -Complex.I * c09_tail_integral_F p G 0 ∧
      -- (3)
      (∀ ξ : ℝ, 0 < ξ → T_0_symbol p G ξ =
        ((ξ ^ 2 : ℝ) : ℂ)⁻¹ * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) *
          (ell p G + Complex.I * c09_tail_integral_F p G ξ)) ∧
      -- (4)
      (G ∈ Y_gamma_tilde p γ →
        (∀ ξ : ℝ, 0 < ξ →
          c09_T_plus_hat p G ξ = Complex.I * ((1 - rho ξ : ℝ) : ℂ) * ((ξ ^ 2 : ℝ) : ℂ)⁻¹ *
            Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) * c09_tail_integral_F p G ξ ∧
          ∃ L : ℂ, Tendsto (fun Ξ : ℝ => ∫ η in ξ..Ξ, (η : ℂ) *
              Complex.exp (Complex.I * (Phi0 p η : ℂ)) * fourierT (fun x => (G x : ℂ)) η)
              atTop (nhds L) ∧
            c09_T_plus_hat p G ξ = -((1 - rho ξ : ℝ) : ℂ) *
              Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) * ((ξ ^ 2 : ℝ) : ℂ)⁻¹ * L) ∧
        (∀ ξ : ℝ, ‖c09_T_plus_hat p G ξ‖ ≤
          C * yNorm p γ G * (Set.indicator (Ioi 1) (fun ξ => ξ ^ (-2 : ℝ)) ξ)) ∧
        Integrable (c09_T_plus_hat p G)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, -, -, h3⟩ := c09_tail_basic p hp hp1
  obtain ⟨CF, hCF, hF⟩ := h3 γ hγ
  refine ⟨CF, hCF, fun G hG => ?_⟩
  obtain ⟨hFc, hFb, hFt⟩ := hF G hG
  set F := c09_tail_integral_F p G with hFdef
  have h1 : ∀ ξ Ξ : ℝ, 0 ≤ ξ → ξ ≤ Ξ →
      ∫ η in ξ..Ξ, (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
        fourierT (fun x => (G x : ℂ)) η = -Complex.I * (F ξ - F Ξ) :=
    fun ξ Ξ hξ hΞ => c09_aux_tail_formula1 p hp hp1 γ hγ G hG ξ Ξ hξ hΞ
  have hlimξ : ∀ ξ, 0 ≤ ξ → Tendsto (fun Ξ : ℝ => ∫ η in ξ..Ξ, (η : ℂ) *
      Complex.exp (Complex.I * (Phi0 p η : ℂ)) * fourierT (fun x => (G x : ℂ)) η)
      atTop (𝓝 (-Complex.I * F ξ)) := by
    intro ξ hξ
    have := ((tendsto_const_nhds (x := F ξ)).sub hFt).const_mul (-Complex.I)
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop ξ] with Ξ hΞ
    exact (h1 ξ Ξ hξ hΞ).symm
  have hell : ell p G = -Complex.I * F 0 := (hlimξ 0 le_rfl).limUnder_eq
  have h3' : ∀ ξ : ℝ, 0 < ξ → T_0_symbol p G ξ =
      ((ξ ^ 2 : ℝ) : ℂ)⁻¹ * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) *
        (ell p G + Complex.I * F ξ) := by
    intro ξ hξ
    set h : ℝ → ℂ := fun η => (η : ℂ) * Complex.exp (Complex.I * (Phi0 p η : ℂ)) *
      fourierT (fun x => (G x : ℂ)) η with hh
    have hpt : ∀ t ∈ uIcc (0 : ℝ) 1, (t : ℂ) *
        Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) *
          fourierT (fun x => (G x : ℂ)) (t * ξ) =
        ((ξ ^ 2 : ℝ) : ℂ)⁻¹ * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) *
          ((ξ : ℂ) * h (ξ * t)) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      rw [hh]; simp only
      rw [c09_aux_Phi0_scale p hp0 ξ t hξ ht.1, mul_comm ξ t]
      have hex : Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) =
          Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) *
            Complex.exp (Complex.I * ((t ^ (p + 1) * Phi0 p ξ : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hex]
      have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
      push_cast
      field_simp
    unfold T_0_symbol
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left h hξ.ne', mul_zero, mul_one,
      h1 0 ξ le_rfl hξ.le, hell]
    have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    rw [Complex.real_smul, Complex.ofReal_inv]
    field_simp
    ring
  refine ⟨fun ξ Ξ hξ hΞ => h1 ξ Ξ hξ hΞ.le, hell ▸ hlimξ 0 le_rfl, hell, h3', fun hGt => ?_⟩
  have hell0 : ell p G = 0 := hGt.2
  have hform : ∀ ξ : ℝ, 0 < ξ → c09_T_plus_hat p G ξ = Complex.I * ((1 - rho ξ : ℝ) : ℂ) *
      ((ξ ^ 2 : ℝ) : ℂ)⁻¹ * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) * F ξ := by
    intro ξ hξ
    unfold c09_T_plus_hat
    simp only [hξ, ↓reduceIte]; rw [h3' ξ hξ, hell0]; ring
  refine ⟨fun ξ hξ => ⟨hform ξ hξ, -Complex.I * F ξ, hlimξ ξ hξ.le, ?_⟩, ?_⟩
  · rw [hform ξ hξ]; ring_nf
  have hrho1 : ∀ ξ : ℝ, |ξ| ≤ 1 → rho ξ = 1 := fun ξ h => by
    unfold rho; exact Real.smoothTransition.one_of_one_le (by linarith)
  have hrho01 : ∀ ξ : ℝ, |1 - rho ξ| ≤ 1 := fun ξ => by
    have h0 : 0 ≤ rho ξ := Real.smoothTransition.nonneg _
    have h1 : rho ξ ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_le]; constructor <;> linarith
  have hzero : ∀ ξ : ℝ, ξ ≤ 1 → c09_T_plus_hat p G ξ = 0 := by
    intro ξ hξ
    rcases le_or_gt ξ 0 with h0 | h0
    · unfold c09_T_plus_hat; simp [not_lt.mpr h0]
    · rw [hform ξ h0, hrho1 ξ (by rw [abs_of_pos h0]; exact hξ)]; simp
  have hM : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
  have hbound : ∀ ξ : ℝ, ‖c09_T_plus_hat p G ξ‖ ≤
      CF * yNorm p γ G * (Set.indicator (Ioi 1) (fun ξ => ξ ^ (-2 : ℝ)) ξ) := by
    intro ξ
    rcases le_or_gt ξ 1 with h1 | h1
    · rw [hzero ξ h1, norm_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun x hx =>
        (Real.rpow_pos_of_pos (lt_trans one_pos hx) _).le) ξ)
    · have hξ0 : 0 < ξ := by linarith
      rw [Set.indicator_of_mem (show ξ ∈ Ioi (1 : ℝ) from h1), hform ξ hξ0]
      have hn : ‖Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ)))‖ = 1 := by
        rw [show -(Complex.I * (Phi0 p ξ : ℂ)) = ((-Phi0 p ξ : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < ξ ^ 2), hn, mul_one,
        Real.rpow_neg hξ0.le, Real.rpow_two]
      have hFξ := hFb ξ hξ0.le
      have hi : 0 < (ξ ^ 2)⁻¹ := by positivity
      calc |1 - rho ξ| * (ξ ^ 2)⁻¹ * ‖F ξ‖ ≤ 1 * (ξ ^ 2)⁻¹ * (CF * yNorm p γ G) := by
            gcongr; exact hrho01 ξ
        _ = CF * yNorm p γ G * (ξ ^ 2)⁻¹ := by ring
  refine ⟨hbound, ?_⟩
  have hgi : Integrable (fun ξ => CF * yNorm p γ G * (Set.indicator (Ioi 1)
      (fun ξ : ℝ => ξ ^ (-2 : ℝ)) ξ)) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)).const_mul _
  refine hgi.mono' ?_ (Eventually.of_forall hbound)
  have heq : c09_T_plus_hat p G = Set.indicator (Ioi 0) (fun ξ => Complex.I *
      ((1 - rho ξ : ℝ) : ℂ) * ((ξ ^ 2 : ℝ) : ℂ)⁻¹ *
        Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) * F ξ) := by
    funext ξ
    by_cases hξ : 0 < ξ
    · rw [Set.indicator_of_mem (show ξ ∈ Ioi (0 : ℝ) from hξ), hform ξ hξ]
    · rw [Set.indicator_of_notMem (show ξ ∉ Ioi (0 : ℝ) from hξ), hzero ξ (by linarith)]
  rw [heq, aestronglyMeasurable_indicator_iff measurableSet_Ioi]
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  have hrho : Continuous rho := by
    unfold rho; exact Real.smoothTransition.continuous.comp (by fun_prop)
  have hPhi : Continuous (Phi0 p) := by
    unfold Phi0
    have := Continuous.rpow_const continuous_abs (fun _ : ℝ => Or.inr hp0.le)
    fun_prop
  refine ContinuousOn.mul ?_ (hFc.mono Ioi_subset_Ici_self)
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.sub hrho))).continuousOn
  · intro x hx
    have hx0 : (x : ℝ) ≠ 0 := (show (0 : ℝ) < x from hx).ne'
    exact ((Complex.continuous_ofReal.comp (continuous_pow 2)).continuousAt.inv₀
      (by simp [hx0])).continuousWithinAt
  · exact (continuous_const.mul (Complex.continuous_ofReal.comp hPhi)).neg.cexp.continuousOn

/-- Blueprint: lem:c09_conjugate_symmetry.  `m_G` is bounded, continuous and Hermitian; for
`G ∈ Ỹ_γ`, `(1-χ) m_G ∈ L¹`, `𝒯_h G` is the bounded continuous real function given by the
absolutely convergent inverse transform of `(1-χ)m_G` (it represents `T_high p G`), and
`𝒯_h G = 2 Re 𝒯₊ G`. -/
theorem c09_conjugate_symmetry (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) :
    Continuous (T_0_symbol p G) ∧
    (∀ ξ, ‖T_0_symbol p G ξ‖ ≤ (1 / 2) * ∫ x, |G x|) ∧
    (∀ ξ, T_0_symbol p G (-ξ) = (starRingEnd ℂ) (T_0_symbol p G ξ)) ∧
    (G ∈ Y_gamma_tilde p γ →
      Integrable (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ) ∧
      HasDistFourier (fun x => (T_high p G x : ℂ))
        (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ) ∧
      (∀ y, (T_high p G y : ℂ) =
        invFourierT (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ) y) ∧
      Continuous (T_high p G) ∧ (∃ M, ∀ y, |T_high p G y| ≤ M) ∧
      (∀ y, T_high p G y = 2 * (c09_T_plus p G y).re)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, ⟨CL, -, hL1⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
  have iG : Integrable G := (hL1 G hG).1
  have hFc := c09_aux_fourierT_continuous G iG
  have hPhi : Continuous (Phi0 p) := by
    unfold Phi0
    have := Continuous.rpow_const continuous_abs (fun _ : ℝ => Or.inr (show 0 ≤ p by linarith))
    fun_prop
  have hrp : Continuous fun t : ℝ => t ^ (p + 1) := Real.continuous_rpow_const (by linarith)
  have hexp1 : ∀ r : ℝ, ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := fun r => by
    rw [Complex.norm_exp]; simp
  -- (1) continuity
  have ha : Continuous (T_0_symbol p G) := by
    have hc : Continuous (Function.uncurry fun (ξ t : ℝ) => (t : ℂ) *
        Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) *
          fourierT (fun x => (G x : ℂ)) (t * ξ)) := by
      have h1 : Continuous fun q : ℝ × ℝ => fourierT (fun x => (G x : ℂ)) (q.2 * q.1) :=
        hFc.comp (continuous_snd.mul continuous_fst)
      have h2 : Continuous fun q : ℝ × ℝ => (((1 - q.2 ^ (p + 1)) * Phi0 p q.1 : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp ((continuous_const.sub (hrp.comp continuous_snd)).mul
          (hPhi.comp continuous_fst))
      exact ((Complex.continuous_ofReal.comp continuous_snd).mul
        ((continuous_const.mul h2).neg.cexp)).mul h1
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc 0 1
  -- (2) bound
  have hFb : ∀ η, ‖fourierT (fun x => (G x : ℂ)) η‖ ≤ ∫ x, |G x| := by
    intro η
    unfold fourierT
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; ext x
    rw [norm_mul, c09_aux_norm_exp_neg, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb : ∀ ξ, ‖T_0_symbol p G ξ‖ ≤ (1 / 2) * ∫ x, |G x| := by
    intro ξ
    unfold T_0_symbol
    have hgi : IntervalIntegrable (fun t : ℝ => t * ∫ x, |G x|) volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable _ _
    refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall fun t ht => ?_) hgi).trans (le_of_eq ?_)
    · rw [norm_mul, norm_mul, hexp1, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht.1]
      exact mul_le_mul_of_nonneg_left (hFb _) ht.1.le
    · rw [intervalIntegral.integral_mul_const, integral_id]; ring
  -- (3) Hermitian symmetry
  have hFconj : ∀ η, fourierT (fun x => (G x : ℂ)) (-η) =
      (starRingEnd ℂ) (fourierT (fun x => (G x : ℂ)) η) := by
    intro η
    unfold fourierT
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    have earg : (starRingEnd ℂ) (-(Complex.I * (x : ℂ) * (η : ℂ))) =
        -(Complex.I * (x : ℂ) * ((-η : ℝ) : ℂ)) := by
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, earg]
  have hPhineg : ∀ ξ, Phi0 p (-ξ) = -Phi0 p ξ := fun ξ => by
    unfold Phi0; rw [abs_neg]; ring
  have hc : ∀ ξ, T_0_symbol p G (-ξ) = (starRingEnd ℂ) (T_0_symbol p G ξ) := by
    intro ξ
    unfold T_0_symbol
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    have earg : ∀ a : ℝ, (starRingEnd ℂ) (-(Complex.I * (a : ℂ))) =
        -(Complex.I * ((-a : ℝ) : ℂ)) := fun a => by
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
    rw [map_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hPhineg,
      show t * -ξ = -(t * ξ) by ring, hFconj, earg, mul_neg]
  refine ⟨ha, hb, hc, fun hGt => ?_⟩
  -- (4) the high-frequency part
  obtain ⟨Ct, -, htf⟩ := c09_tail_formula p hp hp1 γ hγ
  obtain ⟨-, -, -, -, h4⟩ := htf G hG
  obtain ⟨-, -, hint⟩ := h4 hGt
  set h := c09_T_plus_hat p G with hh
  set m' : ℝ → ℂ := fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ with hm'
  have hrho_even : ∀ ξ, rho (-ξ) = rho ξ := fun ξ => by unfold rho; rw [abs_neg]
  have hrho0 : rho 0 = 1 := by
    unfold rho; simp only [abs_zero, sub_zero]
    exact Real.smoothTransition.one_of_one_le (by norm_num)
  have hdec : ∀ ξ, m' ξ = h ξ + (starRingEnd ℂ) (h (-ξ)) := by
    intro ξ
    rcases lt_trichotomy ξ 0 with hξ | rfl | hξ
    · have e1 : h ξ = 0 := by rw [hh]; unfold c09_T_plus_hat; simp [not_lt.mpr hξ.le]
      have e2 : h (-ξ) = ((1 - rho (-ξ) : ℝ) : ℂ) * T_0_symbol p G (-ξ) := by
        rw [hh]; unfold c09_T_plus_hat; simp [neg_pos.mpr hξ]
      rw [e1, e2, zero_add, map_mul, Complex.conj_ofReal, hc, Complex.conj_conj,
        hrho_even]
    · have e1 : h 0 = 0 := by rw [hh]; unfold c09_T_plus_hat; simp
      rw [neg_zero, e1, map_zero, add_zero, hm']
      simp [hrho0]
    · have e1 : h (-ξ) = 0 := by
        rw [hh]; unfold c09_T_plus_hat; simp [not_lt.mpr (neg_nonpos.mpr hξ.le)]
      have e2 : h ξ = ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ := by
        rw [hh]; unfold c09_T_plus_hat; simp [hξ]
      rw [e1, e2, map_zero, add_zero]
  have hconjI : Integrable (fun ξ => (starRingEnd ℂ) (h (-ξ))) :=
    hint.comp_neg.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      hint.comp_neg.aestronglyMeasurable) (Eventually.of_forall fun ξ =>
        le_of_eq (by rw [Complex.norm_conj]))
  have im' : Integrable m' := by
    have e : m' = fun ξ => h ξ + (starRingEnd ℂ) (h (-ξ)) := funext hdec
    rw [e]; exact hint.add hconjI
  have hrefl : ∀ y, invFourierT (fun ξ => (starRingEnd ℂ) (h (-ξ))) y =
      (starRingEnd ℂ) (invFourierT h y) := by
    intro y
    unfold invFourierT
    rw [map_mul, map_inv₀, Complex.conj_ofReal, ← integral_conj]
    congr 1
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    have earg : (starRingEnd ℂ) (Complex.I * (y : ℂ) * (ξ : ℂ)) =
        Complex.I * (y : ℂ) * ((-ξ : ℝ) : ℂ) := by
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
    rw [neg_neg, map_mul, ← Complex.exp_conj, earg]
  have hinv : ∀ y, invFourierT m' y = ((2 * (c09_T_plus p G y).re : ℝ) : ℂ) := by
    intro y
    have e : m' = fun ξ => ((1 : ℝ) : ℂ) * h ξ + ((1 : ℝ) : ℂ) * (starRingEnd ℂ) (h (-ξ)) := by
      funext ξ; rw [hdec]; simp
    rw [e, c09_aux_invFourierT_lin _ _ hint hconjI, hrefl]
    simp only [Complex.ofReal_one, one_mul]
    rw [Complex.add_conj]
    rfl
  set u : ℝ → ℝ := fun y => 2 * (c09_T_plus p G y).re with hu
  have huc : Continuous u :=
    continuous_const.mul (Complex.continuous_re.comp (c09_aux_invFourierT_continuous h hint))
  set B : ℝ := 2 * ((2 * π)⁻¹ * ∫ ξ, ‖h ξ‖) with hB
  have hub : ∀ y, |u y| ≤ B := by
    intro y
    rw [hu, hB]; dsimp only
    rw [abs_mul, abs_two]
    gcongr
    exact (Complex.abs_re_le_norm _).trans (c09_aux_invFourierT_norm_le h y)
  have huF : HasDistFourier (fun x => (u x : ℂ)) m' := by
    have := c09_aux_hasDistFourier_invFourierT m' im'
    have e : invFourierT m' = fun x => (u x : ℂ) := funext hinv
    rwa [e] at this
  have hupb : IsPolyBounded u := ⟨B, 0, fun x => by
    rw [Real.rpow_zero, mul_one, Real.norm_eq_abs]; exact hub x⟩
  have hex : ∃ r : ℝ → ℝ, Continuous r ∧ IsPolyBounded r ∧
      HasDistFourier (fun x => (r x : ℂ)) m' := ⟨u, huc, hupb, huF⟩
  have hTh : T_high p G = Classical.choose hex := by
    unfold T_high distFourierInv
    exact dite_eq_left_of_eq_true (eq_true hex)
  obtain ⟨hc1, hpb1, hF1⟩ := Classical.choose_spec hex
  rw [← hTh] at hc1 hpb1 hF1
  have hpbC : ∀ r : ℝ → ℝ, IsPolyBounded r → IsPolyBounded (fun x => (r x : ℂ)) := by
    rintro r ⟨C, N, hCN⟩
    exact ⟨C, N, fun x => by rw [Complex.norm_real]; exact hCN x⟩
  have heq := c09_aux_dist_unique (fun x => (T_high p G x : ℂ)) (fun x => (u x : ℂ))
    (Complex.continuous_ofReal.comp hc1) (Complex.continuous_ofReal.comp huc)
    (hpbC _ hpb1) (hpbC _ hupb) m' hF1 huF
  have hTu : ∀ y, T_high p G y = u y := fun y =>
    Complex.ofReal_injective (congrFun heq y)
  have hTu' : T_high p G = u := funext hTu
  refine ⟨im', hF1, fun y => by rw [hTu, hinv], hTu' ▸ huc, ⟨B, fun y => hTu y ▸ hub y⟩,
    fun y => hTu y⟩

/-! ### Frequency truncation and the kernels `K_{+,j}` -/

/-- Blueprint: def:c09_truncation.  `θ_R(ξ) = χ(ξ/R)`. -/
def c09_truncation_theta (R ξ : ℝ) : ℝ := rho (ξ / R)

/-- Blueprint: def:c09_truncation.  `𝒯₊^R G(y) = (2π)⁻¹ ∫₀^∞ θ_R(ξ) \widehat{𝒯₊G}(ξ) e^{iyξ} dξ`. -/
def c09_truncation (p R : ℝ) (G : ℝ → ℝ) (y : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ in Ioi (0 : ℝ), (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ *
    Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))

/-- Blueprint: def:c09_truncation.  `𝒯_h^R G = 2 Re 𝒯₊^R G`. -/
def c09_truncation_high (p R : ℝ) (G : ℝ → ℝ) (y : ℝ) : ℝ := 2 * (c09_truncation p R G y).re

/-- Blueprint: def:c09_truncation.  `R₀(y) = max{2, ⟨y⟩^{1/p}}`. -/
def c09_truncation_R0 (p y : ℝ) : ℝ := max 2 (jb y ^ (1 / p))

/-- Blueprint: def:c09_positive_kernel.  The amplitude
`a_j^R(ξ) = -(i^{j+1}/2π)(χ(ξ)-1) θ_R(ξ) ξ^{j-2}` for `ξ > 0`, `0` for `ξ ≤ 0`. -/
def c09_positive_kernel_amp (R : ℝ) (j : ℕ) (ξ : ℝ) : ℂ :=
  if 0 < ξ then
    -(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ) *
      ((rho ξ - 1) * c09_truncation_theta R ξ * ξ ^ ((j : ℝ) - 2) : ℝ)
  else 0

/-- Blueprint: def:c09_positive_kernel.
`K_{+,j}^R(y,z) = ∫₁^{2R} a_j^R(ξ) e^{i(yξ-Φ₀(ξ))} E_z(ξ) dξ`. -/
def c09_positive_kernel (p R : ℝ) (j : ℕ) (y z : ℝ) : ℂ :=
  ∫ ξ in (1 : ℝ)..(2 * R), c09_positive_kernel_amp R j ξ *
    Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ

/-! ### Stationary / nonstationary splitting -/

/-- Blueprint: def:c09_stationary_split.  `χ_s(y,ξ) = χ(100(ξ - y^{1/p})/y^{1/p})` for `y > 0`,
`0` for `y ≤ 0`. -/
def c09_stationary_split (p y ξ : ℝ) : ℝ :=
  if 0 < y then rho (100 * (ξ - y ^ (1 / p)) / y ^ (1 / p)) else 0

/-- Blueprint: def:c09_stationary_split.  `χ_ns = 1 - χ_s`. -/
def c09_stationary_split_chi_ns (p y ξ : ℝ) : ℝ := 1 - c09_stationary_split p y ξ

/-- Blueprint: def:c09_stationary_split.  `a_j^{s,R}(y,ξ) = χ_s(y,ξ) a_j^R(ξ)`. -/
def c09_stationary_split_amp_s (p R : ℝ) (j : ℕ) (y ξ : ℝ) : ℂ :=
  (c09_stationary_split p y ξ : ℂ) * c09_positive_kernel_amp R j ξ

/-- Blueprint: def:c09_stationary_split.  `a_j^{ns,R}(y,ξ) = χ_ns(y,ξ) a_j^R(ξ)`. -/
def c09_stationary_split_amp_ns (p R : ℝ) (j : ℕ) (y ξ : ℝ) : ℂ :=
  (c09_stationary_split_chi_ns p y ξ : ℂ) * c09_positive_kernel_amp R j ξ

/-- Blueprint: def:c09_stationary_split.
`K_{+,j}^{s,R}(y,z) = ∫₁^{2R} a_j^{s,R}(y,ξ) e^{i(yξ-Φ₀(ξ))} E_z(ξ) dξ`. -/
def c09_stationary_split_kernel_s (p R : ℝ) (j : ℕ) (y z : ℝ) : ℂ :=
  ∫ ξ in (1 : ℝ)..(2 * R), c09_stationary_split_amp_s p R j y ξ *
    Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ

/-- Blueprint: def:c09_stationary_split.
`K_{+,j}^{ns,R}(y,z) = ∫₁^{2R} a_j^{ns,R}(y,ξ) e^{i(yξ-Φ₀(ξ))} E_z(ξ) dξ`. -/
def c09_stationary_split_kernel_ns (p R : ℝ) (j : ℕ) (y z : ℝ) : ℂ :=
  ∫ ξ in (1 : ℝ)..(2 * R), c09_stationary_split_amp_ns p R j y ξ *
    Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ

/-- Blueprint: def:c09_stationary_split.  `𝒯_{+,j}^{s,R} G(y) = ∫ K_{+,j}^{s,R}(y,z) G'(z) dz`. -/
def c09_stationary_split_op_s (p R : ℝ) (j : ℕ) (G : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ z, c09_stationary_split_kernel_s p R j y z * ((deriv G z : ℝ) : ℂ)

/-- Blueprint: def:c09_stationary_split.  `𝒯_{+,j}^{ns,R} G(y) = ∫ K_{+,j}^{ns,R}(y,z) G'(z) dz`. -/
def c09_stationary_split_op_ns (p R : ℝ) (j : ℕ) (G : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ z, c09_stationary_split_kernel_ns p R j y z * ((deriv G z : ℝ) : ℂ)

/-! #### Helpers for the cutoff bounds -/

/-- `ρ` is smooth. -/
private theorem c09_aux_cut_R1 : ContDiff ℝ ∞ rho := by
  rw [contDiff_iff_contDiffAt]
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

/-- `ρ = 1` on `[-1,1]`. -/
private theorem c09_aux_cut_R2a (u : ℝ) (h : |u| ≤ 1) : rho u = 1 := by
  unfold rho; exact Real.smoothTransition.one_of_one_le (by linarith)
/-- `ρ = 0` off `(-2,2)`. -/
private theorem c09_aux_cut_R2b (u : ℝ) (h : 2 ≤ |u|) : rho u = 0 := by
  unfold rho; exact Real.smoothTransition.zero_of_nonpos (by linarith)
/-- `0 ≤ ρ ≤ 1`. -/
private theorem c09_aux_cut_R2c (u : ℝ) : 0 ≤ rho u ∧ rho u ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Derivatives of `ρ` vanish off `[-2,2]`. -/
private theorem c09_aux_cut_R3 (ℓ : ℕ) (u : ℝ) (h : 2 < |u|) : iteratedDeriv ℓ rho u = 0 := by
  have hev : rho =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    have : ∀ᶠ ξ in 𝓝 u, 2 < |ξ| := (continuous_abs.tendsto u).eventually (lt_mem_nhds h)
    filter_upwards [this] with ξ hξ using c09_aux_cut_R2b ξ hξ.le
  rw [hev.iteratedDeriv_eq]; simp

/-- Derivatives of `ρ` are bounded. -/
private theorem c09_aux_cut_R4 (ℓ : ℕ) : ∃ B, 0 ≤ B ∧ ∀ u, |iteratedDeriv ℓ rho u| ≤ B := by
  have hc : Continuous (iteratedDeriv ℓ rho) := c09_aux_cut_R1.continuous_iteratedDeriv ℓ (by simp)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-3 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun u => ?_⟩
  by_cases hu : |u| ≤ 3
  · exact (hM u (abs_le.mp hu)).trans (le_max_left _ _)
  · rw [c09_aux_cut_R3 ℓ u (by linarith), abs_zero]; exact le_max_right _ _


/-- `χ_s(y,·) = 0` for `y ≤ 0`. -/
private theorem c09_aux_cut_S1 (p y : ℝ) (hy : y ≤ 0) : c09_stationary_split p y = fun _ => 0 := by
  funext ξ; unfold c09_stationary_split; simp [not_lt.mpr hy]

/-- Derivatives of `χ_s(y,·)` for `y > 0`. -/
private theorem c09_aux_cut_S2 (p y : ℝ) (hy : 0 < y) (ℓ : ℕ) (ξ : ℝ) :
    iteratedDeriv ℓ (c09_stationary_split p y) ξ =
      (100 / y ^ (1 / p)) ^ ℓ * iteratedDeriv ℓ rho (100 / y ^ (1 / p) * ξ + -100) := by
  have hc : 0 < y ^ (1 / p) := Real.rpow_pos_of_pos hy _
  have e : c09_stationary_split p y = fun ξ => (fun w => rho (w + -100)) (100 / y ^ (1 / p) * ξ) := by
    funext ξ; unfold c09_stationary_split; simp only [hy, ↓reduceIte]
    congr 1; field_simp; ring
  have hcd : ContDiff ℝ ℓ (fun w : ℝ => rho (w + -100)) :=
    (c09_aux_cut_R1.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)
  rw [e, iteratedDeriv_comp_const_mul hcd, iteratedDeriv_comp_add_const]

/-- Bounds for the derivatives of `χ_s`. -/
private theorem c09_aux_cut_S3 (p : ℝ) (ℓ : ℕ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ u, |iteratedDeriv ℓ rho u| ≤ B)
    (y ξ : ℝ) (hξ : 0 < ξ) :
    |iteratedDeriv ℓ (c09_stationary_split p y) ξ| ≤ B * 102 ^ ℓ * ξ ^ (-(ℓ : ℝ)) := by
  have hξℓ : 0 ≤ ξ ^ (-(ℓ : ℝ)) := (Real.rpow_pos_of_pos hξ _).le
  rcases le_or_gt y 0 with hy | hy
  · rw [c09_aux_cut_S1 p y hy]; simp; positivity
  · rw [c09_aux_cut_S2 p y hy]
    set a := 100 / y ^ (1 / p)
    have ha : 0 < a := by positivity
    by_cases hu : 2 < |a * ξ + -100|
    · rw [c09_aux_cut_R3 ℓ _ hu, mul_zero, abs_zero]; positivity
    · push Not at hu
      have haξ : a ≤ 102 / ξ := by
        rw [le_div_iff₀ hξ]; linarith [(abs_le.mp hu).2]
      rw [abs_mul, abs_pow, abs_of_pos ha]
      calc a ^ ℓ * |iteratedDeriv ℓ rho (a * ξ + -100)| ≤ (102 / ξ) ^ ℓ * B :=
            mul_le_mul (pow_le_pow_left₀ ha.le haξ ℓ) (hB _) (abs_nonneg _) (by positivity)
        _ = B * 102 ^ ℓ * ξ ^ (-(ℓ : ℝ)) := by
            rw [div_pow, Real.rpow_neg hξ.le, Real.rpow_natCast]; ring

/-- `∂^ℓ χ_ns = -∂^ℓ χ_s` for `ℓ ≥ 1`. -/
private theorem c09_aux_cut_S4 (p y : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ξ : ℝ) :
    iteratedDeriv ℓ (c09_stationary_split_chi_ns p y) ξ =
      -iteratedDeriv ℓ (c09_stationary_split p y) ξ := by
  have : c09_stationary_split_chi_ns p y = fun ξ => 1 - c09_stationary_split p y ξ := rfl
  rw [this, iteratedDeriv_const_sub (by omega), iteratedDeriv_neg]


/-- Leibniz bound for iterated derivatives of a product. -/
private theorem c09_aux_cut_L1 (f g : ℝ → ℝ) (ξ : ℝ) (hξ : 0 < ξ) (n : ℕ) (hf : ContDiffAt ℝ n f ξ)
    (hg : ContDiffAt ℝ n g ξ)
    (a b : ℝ) (A B : ℕ → ℝ)
    (hA : ∀ i ≤ n, |iteratedDeriv i f ξ| ≤ A i * ξ ^ (a - i))
    (hB : ∀ i ≤ n, |iteratedDeriv i g ξ| ≤ B i * ξ ^ (b - i)) :
    |iteratedDeriv n (fun x => f x * g x) ξ| ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * B (n - i)) * ξ ^ (a + b - n) := by
  rw [iteratedDeriv_fun_mul hf hg, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [abs_mul, abs_mul, Nat.abs_cast]
  have h1 := hA i hin
  have h2 := hB (n - i) (Nat.sub_le n i)
  have e : ξ ^ (a - i) * ξ ^ (b - ((n - i : ℕ) : ℝ)) = ξ ^ (a + b - n) := by
    rw [← Real.rpow_add hξ, Nat.cast_sub hin]; congr 1; ring
  calc (n.choose i : ℝ) * |iteratedDeriv i f ξ| * |iteratedDeriv (n - i) g ξ|
      ≤ (n.choose i : ℝ) * (A i * ξ ^ (a - i)) * (B (n - i) * ξ ^ (b - ((n - i : ℕ) : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans h1))
    _ = (n.choose i : ℝ) * A i * B (n - i) * ξ ^ (a + b - n) := by rw [← e]; ring

/-- `iteratedDeriv` commutes with `ℝ → ℂ`. -/
private theorem c09_aux_cut_L2 (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun x => (f x : ℂ)) = fun x => ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : DifferentiableAt ℝ (iteratedDeriv n f) x :=
      (hf.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
    rw [hd.hasDerivAt.ofReal_comp.deriv, iteratedDeriv_succ (f := f)]


/-- The real amplitude `(ρ-1)ρ(·/R)ξ^{j-2}` is smooth. -/
private theorem c09_aux_cut_A2 (j : ℕ) (R : ℝ) :
    ContDiff ℝ ∞ (fun ξ : ℝ => (rho ξ - 1) * rho (ξ / R) * ξ ^ ((j : ℝ) - 2)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have : ∀ᶠ ξ in 𝓝 (0 : ℝ), |ξ| < 1 := by
      have := (continuous_abs.tendsto (0 : ℝ)); rw [abs_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [this] with ξ hξ
    rw [c09_aux_cut_R2a ξ hξ.le]; ring
  · exact ((c09_aux_cut_R1.contDiffAt.sub contDiffAt_const).mul
      ((c09_aux_cut_R1.comp (contDiff_id.div_const R)).contDiffAt)).mul (Real.contDiffAt_rpow_const_of_ne hx)

/-- Derivatives of the real amplitude vanish on `[-1,1]`. -/
private theorem c09_aux_cut_A3 (j : ℕ) (R : ℝ) (ℓ : ℕ) (ξ : ℝ) (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
    iteratedDeriv ℓ (fun ξ : ℝ => (rho ξ - 1) * rho (ξ / R) * ξ ^ ((j : ℝ) - 2)) ξ = 0 := by
  set g := fun ξ : ℝ => (rho ξ - 1) * rho (ξ / R) * ξ ^ ((j : ℝ) - 2) with hg
  have hcl : IsClosed {x : ℝ | iteratedDeriv ℓ g x = 0} :=
    isClosed_eq ((c09_aux_cut_A2 j R).continuous_iteratedDeriv ℓ (by simp)) continuous_const
  have hsub : Ioo (-1 : ℝ) 1 ⊆ {x : ℝ | iteratedDeriv ℓ g x = 0} := by
    intro x hx
    have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with ξ hξ
      rw [hg]; dsimp only
      rw [c09_aux_cut_R2a ξ (abs_le.mpr ⟨hξ.1.le, hξ.2.le⟩)]; ring
    show iteratedDeriv ℓ g x = 0
    rw [hev.iteratedDeriv_eq]; simp
  have := hcl.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num)] at this
  exact this hξ

/-- Derivatives of `a_j^R` via the real amplitude. -/
private theorem c09_aux_cut_A4 (j : ℕ) (R : ℝ) (ℓ : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    iteratedDeriv ℓ (c09_positive_kernel_amp R j) ξ =
      (-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)) *
        ((iteratedDeriv ℓ (fun ξ : ℝ => (rho ξ - 1) * rho (ξ / R) * ξ ^ ((j : ℝ) - 2)) ξ : ℝ) : ℂ) := by
  set g := fun ξ : ℝ => (rho ξ - 1) * rho (ξ / R) * ξ ^ ((j : ℝ) - 2) with hg
  have hev : c09_positive_kernel_amp R j =ᶠ[𝓝 ξ]
      fun x => (-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)) * ((g x : ℝ) : ℂ) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show ξ ∈ Ioi 0 from hξ)] with x hx
    unfold c09_positive_kernel_amp c09_truncation_theta
    simp only [show 0 < x from hx, ↓reduceIte]; rfl
  have hcd : ContDiffAt ℝ ℓ (fun x => ((g x : ℝ) : ℂ)) ξ :=
    (Complex.ofRealCLM.contDiff.comp (c09_aux_cut_A2 j R)).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const_mul _ hcd]
  congr 1
  have := c09_aux_cut_L2 g (c09_aux_cut_A2 j R) ℓ
  exact congrFun this ξ

/-- Support of `a_j^R`. -/
private theorem c09_aux_cut_A5 (j : ℕ) (R : ℝ) (hR : 0 < R) (ξ : ℝ) (h : c09_positive_kernel_amp R j ξ ≠ 0) :
    1 ≤ ξ ∧ ξ ≤ 2 * R := by
  unfold c09_positive_kernel_amp c09_truncation_theta at h
  split_ifs at h with hξ
  · constructor
    · by_contra h1; push Not at h1
      apply h; rw [c09_aux_cut_R2a ξ (abs_le.mpr ⟨by linarith, h1.le⟩)]; simp
    · by_contra h1; push Not at h1
      apply h
      rw [c09_aux_cut_R2b (ξ / R) (by rw [abs_of_pos (div_pos hξ hR), le_div_iff₀ hR]; linarith)]; simp
  · exact absurd rfl h


/-- Bounds for derivatives of `ρ - 1`. -/
private theorem c09_aux_cut_F1b (B : ℕ → ℝ) (hB : ∀ i u, |iteratedDeriv i rho u| ≤ B i) (i : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    |iteratedDeriv i (fun ξ => rho ξ - 1) ξ| ≤ (B i * 2 ^ i + 1) * ξ ^ ((0 : ℝ) - i) := by
  have hB0 : 0 ≤ B i := (abs_nonneg _).trans (hB i 0)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one, pow_zero]
    have := c09_aux_cut_R2c ξ
    rw [abs_le]; constructor <;> linarith
  · have e : iteratedDeriv i (fun ξ => rho ξ - 1) ξ = iteratedDeriv i rho ξ := by
      rw [iteratedDeriv_fun_sub (c09_aux_cut_R1.contDiffAt.of_le (by exact_mod_cast le_top))
        contDiffAt_const]
      simp [iteratedDeriv_const, hi.ne']
    rw [e]
    have hpow : (1 : ℝ) ≤ 2 ^ i * ξ ^ ((0 : ℝ) - i) ∨ 2 < ξ := by
      by_cases h2 : 2 < ξ
      · exact Or.inr h2
      · left; push Not at h2
        rw [zero_sub, Real.rpow_neg hξ.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀
          (by positivity), one_mul]
        exact pow_le_pow_left₀ hξ.le h2 i
    rcases hpow with h | h
    · calc |iteratedDeriv i rho ξ| ≤ B i := hB i ξ
        _ ≤ B i * (2 ^ i * ξ ^ ((0 : ℝ) - i)) := le_mul_of_one_le_right hB0 h
        _ ≤ (B i * 2 ^ i + 1) * ξ ^ ((0 : ℝ) - i) := by
            have : 0 ≤ ξ ^ ((0 : ℝ) - i) := (Real.rpow_pos_of_pos hξ _).le
            nlinarith
    · rw [c09_aux_cut_R3 i ξ (by rw [abs_of_pos hξ]; exact h), abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_pos_of_pos hξ _).le

/-- Bounds for derivatives of `ρ(·/R)`. -/
private theorem c09_aux_cut_F2b (B : ℕ → ℝ) (hB : ∀ i u, |iteratedDeriv i rho u| ≤ B i) (R : ℝ) (hR : 0 < R) (i : ℕ)
    (ξ : ℝ) (hξ : 0 < ξ) :
    |iteratedDeriv i (fun ξ => rho (ξ / R)) ξ| ≤ (B i * 2 ^ i + 1) * ξ ^ ((0 : ℝ) - i) := by
  have hB0 : 0 ≤ B i := (abs_nonneg _).trans (hB i 0)
  have e : (fun ξ => rho (ξ / R)) = fun ξ => rho (R⁻¹ * ξ) := by
    funext ξ; rw [div_eq_inv_mul]
  have hcd : ContDiff ℝ i rho := c09_aux_cut_R1.of_le (by exact_mod_cast le_top)
  rw [e, iteratedDeriv_comp_const_mul hcd]
  dsimp only
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.cast_zero, sub_zero, Real.rpow_zero,
      mul_one]
    have := c09_aux_cut_R2c (R⁻¹ * ξ)
    rw [abs_le]; constructor <;> linarith
  · by_cases h2 : 2 < R⁻¹ * ξ
    · rw [c09_aux_cut_R3 i _ (by rw [abs_of_pos (by positivity)]; exact h2), mul_zero, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_pos_of_pos hξ _).le
    · push Not at h2
      have hRξ : R⁻¹ ≤ 2 / ξ := by rw [le_div_iff₀ hξ]; linarith
      rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hR)]
      have hξi : ξ ^ ((0 : ℝ) - i) = (ξ ^ i)⁻¹ := by
        rw [zero_sub, Real.rpow_neg hξ.le, Real.rpow_natCast]
      calc R⁻¹ ^ i * |iteratedDeriv i rho (R⁻¹ * ξ)| ≤ (2 / ξ) ^ i * B i :=
            mul_le_mul (pow_le_pow_left₀ (by positivity) hRξ i) (hB _ _) (abs_nonneg _)
              (by positivity)
        _ = B i * 2 ^ i * ξ ^ ((0 : ℝ) - i) := by rw [hξi, div_pow]; ring
        _ ≤ (B i * 2 ^ i + 1) * ξ ^ ((0 : ℝ) - i) := by
            have : 0 ≤ ξ ^ ((0 : ℝ) - i) := (Real.rpow_pos_of_pos hξ _).le
            nlinarith

/-- Bounds for derivatives of `ξ^{j-2}`. -/
private theorem c09_aux_cut_F3b (j : ℕ) (hj : j ≤ 2) (i : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    |iteratedDeriv i (fun ξ : ℝ => ξ ^ ((j : ℝ) - 2)) ξ| ≤
      (∑ j' ∈ Finset.range 3, |(descPochhammer ℝ i).eval ((j' : ℝ) - 2)|) *
        ξ ^ (((j : ℝ) - 2) - i) := by
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hξ _)]
  gcongr
  exact Finset.single_le_sum (f := fun j' : ℕ => |(descPochhammer ℝ i).eval ((j' : ℝ) - 2)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))


/-- Symbol bounds for `a_j^R`. -/
private theorem c09_aux_cut_A7 (B : ℕ → ℝ) (hB : ∀ i u, |iteratedDeriv i rho u| ≤ B i) (R : ℝ) (hR : 0 < R)
    (j : ℕ) (hj : j ≤ 2) (ℓ : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ‖iteratedDeriv ℓ (c09_positive_kernel_amp R j) ξ‖ ≤
      ((2 * π)⁻¹ * ∑ k ∈ Finset.range (ℓ + 1), (ℓ.choose k : ℝ) *
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (B i * 2 ^ i + 1) *
          (B (k - i) * 2 ^ (k - i) + 1)) *
        (∑ j' ∈ Finset.range 3, |(descPochhammer ℝ (ℓ - k)).eval ((j' : ℝ) - 2)|)) *
      ξ ^ ((j : ℝ) - 2 - ℓ) := by
  rw [c09_aux_cut_A4 j R ℓ ξ hξ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hK : ‖-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)‖ = (2 * π)⁻¹ := by
    rw [norm_div, norm_neg, norm_pow, Complex.norm_I, one_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
  rw [hK, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hf12 : ContDiff ℝ ∞ (fun x : ℝ => (rho x - 1) * rho (x / R)) :=
    (c09_aux_cut_R1.sub contDiff_const).mul (c09_aux_cut_R1.comp (contDiff_id.div_const R))
  have h12 : ∀ i ≤ ℓ, |iteratedDeriv i (fun x : ℝ => (rho x - 1) * rho (x / R)) ξ| ≤
      (∑ i' ∈ Finset.range (i + 1), (i.choose i' : ℝ) * (B i' * 2 ^ i' + 1) *
        (B (i - i') * 2 ^ (i - i') + 1)) * ξ ^ ((0 : ℝ) - i) := by
    intro i _
    have := c09_aux_cut_L1 (fun x => rho x - 1) (fun x => rho (x / R)) ξ hξ i
      ((c09_aux_cut_R1.sub contDiff_const).contDiffAt.of_le (by exact_mod_cast le_top))
      ((c09_aux_cut_R1.comp (contDiff_id.div_const R)).contDiffAt.of_le (by exact_mod_cast le_top))
      0 0 (fun i => B i * 2 ^ i + 1) (fun i => B i * 2 ^ i + 1)
      (fun i' _ => c09_aux_cut_F1b B hB i' ξ hξ) (fun i' _ => c09_aux_cut_F2b B hB R hR i' ξ hξ)
    rwa [zero_add] at this
  have := c09_aux_cut_L1 (fun x : ℝ => (rho x - 1) * rho (x / R)) (fun x : ℝ => x ^ ((j : ℝ) - 2)) ξ hξ ℓ
    (hf12.contDiffAt.of_le (by exact_mod_cast le_top))
    (Real.contDiffAt_rpow_const_of_ne hξ.ne') 0 ((j : ℝ) - 2) _ _ h12
    (fun i _ => c09_aux_cut_F3b j hj i ξ hξ)
  rw [show (0 : ℝ) + ((j : ℝ) - 2) - ℓ = (j : ℝ) - 2 - ℓ by ring] at this
  exact this


/-- `ρ'` is integrable. -/
private theorem c09_aux_cut_I1 : Integrable (fun u => |deriv rho u|) := by
  have hc : Continuous (deriv rho) := c09_aux_cut_R1.continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv rho) := by
    refine HasCompactSupport.intro (K := Icc (-3) 3) isCompact_Icc fun x hx => ?_
    have : 2 < |x| := by
      by_contra h; push Not at h; exact hx (abs_le.mp (by linarith))
    have := c09_aux_cut_R3 1 x this
    rwa [iteratedDeriv_one] at this
  exact (hc.integrable_of_hasCompactSupport hcs).abs

/-- `∫ |∂_ξ χ_ns| ≤ ∫|ρ'|`. -/
private theorem c09_aux_cut_S5 (p y : ℝ) :
    IntegrableOn (fun ξ => |deriv (c09_stationary_split_chi_ns p y) ξ|) (Ioi 0) ∧
      ∫ ξ in Ioi (0 : ℝ), |deriv (c09_stationary_split_chi_ns p y) ξ| ≤
        ∫ u, |deriv rho u| := by
  have hI0 : 0 ≤ ∫ u, |deriv rho u| := integral_nonneg fun _ => abs_nonneg _
  have hd : ∀ ξ, deriv (c09_stationary_split_chi_ns p y) ξ =
      -iteratedDeriv 1 (c09_stationary_split p y) ξ := fun ξ => by
    rw [← c09_aux_cut_S4 p y 1 le_rfl ξ, iteratedDeriv_one]
  simp_rw [hd, abs_neg]
  rcases le_or_gt y 0 with hy | hy
  · rw [c09_aux_cut_S1 p y hy]
    simp only [iteratedDeriv_const, ite_self, abs_zero]
    simp [hI0]
  · simp_rw [c09_aux_cut_S2 p y hy]
    set a := 100 / y ^ (1 / p) with ha
    have ha0 : 0 < a := by positivity
    have hint : Integrable (fun ξ => |a ^ 1 * iteratedDeriv 1 rho (a * ξ + -100)|) := by
      have h1 : Integrable (fun ξ => |deriv rho (a * ξ + -100)|) :=
        (c09_aux_cut_I1.comp_add_right (-100)).comp_mul_left' ha0.ne'
      refine (h1.const_mul a).congr (Eventually.of_forall fun ξ => ?_)
      simp only [pow_one, iteratedDeriv_one, abs_mul, abs_of_pos ha0]
    refine ⟨hint.integrableOn, (setIntegral_le_integral hint
      (Eventually.of_forall fun _ => abs_nonneg _)).trans (le_of_eq ?_)⟩
    simp only [pow_one, iteratedDeriv_one, abs_mul, abs_of_pos ha0]
    rw [integral_const_mul,
      Measure.integral_comp_mul_left (fun w => |deriv rho (w + -100)|) a,
      integral_add_right_eq_self (fun w => |deriv rho w|), abs_inv, abs_of_pos ha0, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]

/-- `∫ |∂((1-ρ)θ_R)| ≤ 2∫|ρ'|`. -/
private theorem c09_aux_cut_S6 (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun ξ => |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ|) (Ioi 0) ∧
      ∫ ξ in Ioi (0 : ℝ), |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ| ≤
        2 * ∫ u, |deriv rho u| := by
  unfold c09_truncation_theta
  have hdiff : Differentiable ℝ rho := c09_aux_cut_R1.differentiable (by simp)
  have hd : ∀ ξ, deriv (fun ξ => (1 - rho ξ) * rho (ξ / R)) ξ =
      -deriv rho ξ * rho (ξ / R) + (1 - rho ξ) * (deriv rho (ξ / R) * R⁻¹) := by
    intro ξ
    have h1 : HasDerivAt (fun ξ => 1 - rho ξ) (-deriv rho ξ) ξ := by
      simpa using ((hdiff ξ).hasDerivAt).const_sub 1
    have h2 : HasDerivAt (fun ξ => rho (ξ / R)) (deriv rho (ξ / R) * R⁻¹) ξ := by
      refine ((hdiff (ξ / R)).hasDerivAt.comp ξ ((hasDerivAt_id ξ).div_const R)).congr_deriv ?_
      simp [div_eq_mul_inv]
    exact (h1.mul h2).deriv
  set D : ℝ → ℝ := fun ξ => |deriv rho ξ| + R⁻¹ * |deriv rho (R⁻¹ * ξ)| with hD
  have iD : Integrable D := c09_aux_cut_I1.add ((c09_aux_cut_I1.comp_mul_left' (inv_pos.mpr hR).ne').const_mul _)
  have hb : ∀ ξ, |deriv (fun ξ => (1 - rho ξ) * rho (ξ / R)) ξ| ≤ D ξ := by
    intro ξ
    rw [hd, hD]; dsimp only
    have r1 := c09_aux_cut_R2c ξ; have r2 := c09_aux_cut_R2c (ξ / R)
    calc |-deriv rho ξ * rho (ξ / R) + (1 - rho ξ) * (deriv rho (ξ / R) * R⁻¹)|
        ≤ |deriv rho ξ| * |rho (ξ / R)| + |1 - rho ξ| * (|deriv rho (ξ / R)| * R⁻¹) := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hR)]
      _ ≤ |deriv rho ξ| * 1 + 1 * (|deriv rho (ξ / R)| * R⁻¹) := by
          gcongr
          · rw [abs_le]; constructor <;> linarith
          · rw [abs_le]; constructor <;> linarith
      _ = _ := by rw [div_eq_inv_mul]; ring
  have hmeas : Measurable (fun ξ => |deriv (fun ξ => (1 - rho ξ) * rho (ξ / R)) ξ|) :=
    (measurable_deriv _).abs
  have hint : Integrable (fun ξ => |deriv (fun ξ => (1 - rho ξ) * rho (ξ / R)) ξ|) :=
    iD.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_abs]; exact hb ξ)
  refine ⟨hint.integrableOn, (setIntegral_le_integral hint
    (Eventually.of_forall fun _ => abs_nonneg _)).trans ?_⟩
  refine (integral_mono hint iD hb).trans (le_of_eq ?_)
  rw [hD, integral_add c09_aux_cut_I1 ((c09_aux_cut_I1.comp_mul_left' (inv_pos.mpr hR).ne').const_mul _),
    integral_const_mul, Measure.integral_comp_mul_left (fun w => |deriv rho w|), inv_inv,
    abs_of_pos hR, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  ring


/-- Support of `χ_s`. -/
private theorem c09_aux_cut_Q1a (p y ξ : ℝ) (h : c09_stationary_split p y ξ ≠ 0) :
    0 < y ∧ |ξ - y ^ (1 / p)| ≤ y ^ (1 / p) / 50 := by
  unfold c09_stationary_split at h
  split_ifs at h with hy
  · refine ⟨hy, ?_⟩
    have hc : 0 < y ^ (1 / p) := Real.rpow_pos_of_pos hy _
    have hu : |100 * (ξ - y ^ (1 / p)) / y ^ (1 / p)| < 2 := by
      by_contra h2; push Not at h2; exact h (c09_aux_cut_R2b _ h2)
    rw [abs_div, abs_mul, abs_of_pos hc, div_lt_iff₀ hc] at hu
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 100)] at hu
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 50)]; linarith
  · exact absurd rfl h

/-- `χ_s = 1` near the stationary point. -/
private theorem c09_aux_cut_Q1b (p y ξ : ℝ) (hy : 0 < y) (h : |ξ - y ^ (1 / p)| ≤ y ^ (1 / p) / 100) :
    c09_stationary_split p y ξ = 1 := by
  unfold c09_stationary_split
  simp only [hy, ↓reduceIte]
  have hc : 0 < y ^ (1 / p) := Real.rpow_pos_of_pos hy _
  apply c09_aux_cut_R2a
  rw [abs_div, abs_mul, abs_of_pos hc, div_le_iff₀ hc, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100)] at h; linarith

/-- Nonstationary lower bound on `tsupport χ_ns`. -/
private theorem c09_aux_cut_Q4a (p : ℝ) (hp : 0 < p) (y ξ : ℝ) (hsupp : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)) :
    (1 - (100 / 101 : ℝ) ^ p) / 2 * (|y| + ξ ^ p) ≤ |y - ξ ^ p| ∨ ξ < 0 := by
  rcases lt_or_ge ξ 0 with hξ | hξ
  · exact Or.inr hξ
  left
  have hq : (100 / 101 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hq0 : 0 ≤ (100 / 101 : ℝ) ^ p := by positivity
  have hξp : 0 ≤ ξ ^ p := Real.rpow_nonneg hξ _
  rcases le_or_gt y 0 with hy | hy
  · rw [abs_of_nonpos hy, abs_of_nonpos (by linarith)]
    nlinarith
  · set c := y ^ (1 / p) with hcdef
    have hc : 0 < c := Real.rpow_pos_of_pos hy _
    have hcp : c ^ p = y := by
      rw [hcdef, ← Real.rpow_mul hy.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
    have hfar : c / 100 ≤ |ξ - c| := by
      by_contra hlt; push Not at hlt
      have hev : c09_stationary_split_chi_ns p y =ᶠ[𝓝 ξ] fun _ => 0 := by
        have hopen : IsOpen {x : ℝ | |x - c| < c / 100} :=
          isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
        filter_upwards [hopen.mem_nhds hlt] with x hx
        unfold c09_stationary_split_chi_ns
        rw [c09_aux_cut_Q1b p y x hy (le_of_lt hx)]; ring
      exact (notMem_tsupport_iff_eventuallyEq.mpr hev) hsupp
    rw [abs_of_pos hy]
    rcases le_or_gt c ξ with hcξ | hcξ
    · rw [abs_of_nonneg (by linarith)] at hfar
      have h1 : c ≤ (100 / 101) * ξ := by linarith
      have h2 : y ≤ (100 / 101 : ℝ) ^ p * ξ ^ p := by
        rw [← hcp, ← Real.mul_rpow (by norm_num) hξ]
        exact Real.rpow_le_rpow hc.le h1 hp.le
      have h3 : (100 / 101 : ℝ) ^ p * ξ ^ p ≤ ξ ^ p := mul_le_of_le_one_left hξp hq.le
      have h4 : (1 - (100 / 101 : ℝ) ^ p) * y ≤ (1 - (100 / 101 : ℝ) ^ p) * ξ ^ p :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_neg (by linarith)] at hfar
      have h1 : ξ ≤ (99 / 100) * c := by linarith
      have h2 : ξ ^ p ≤ (100 / 101 : ℝ) ^ p * y := by
        rw [← hcp]
        calc ξ ^ p ≤ ((99 / 100) * c) ^ p := Real.rpow_le_rpow hξ h1 hp.le
          _ = (99 / 100 : ℝ) ^ p * c ^ p := Real.mul_rpow (by norm_num) hc.le
          _ ≤ (100 / 101 : ℝ) ^ p * c ^ p :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) (by norm_num) hp.le)
                (Real.rpow_nonneg hc.le _)
      have h3 : (100 / 101 : ℝ) ^ p * y ≤ y := mul_le_of_le_one_left hy.le hq.le
      have h4 : (1 - (100 / 101 : ℝ) ^ p) * ξ ^ p ≤ (1 - (100 / 101 : ℝ) ^ p) * y :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- `2^{-1/2}⟨y⟩ ≤ |y| + ξ^p` for `ξ ≥ 1`. -/
private theorem c09_aux_cut_Q4b (p : ℝ) (hp : 0 < p) (y ξ : ℝ) (hξ : 1 ≤ ξ) :
    2 ^ (-(1 / 2 : ℝ)) * jb y ≤ |y| + ξ ^ p := by
  have h1 : 1 ≤ ξ ^ p := Real.one_le_rpow hξ hp.le
  have h2 : jb y ≤ Real.sqrt 2 * (|y| + 1) := by
    unfold jb
    rw [← Real.sqrt_sq (show 0 ≤ |y| + 1 by positivity), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_abs y, abs_nonneg y]
  have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt 2 = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]; norm_num
  calc 2 ^ (-(1 / 2 : ℝ)) * jb y ≤ 2 ^ (-(1 / 2 : ℝ)) * (Real.sqrt 2 * (|y| + 1)) := by
        gcongr
    _ = |y| + 1 := by rw [← mul_assoc, h3, one_mul]
    _ ≤ |y| + ξ ^ p := by linarith

/-- Localisation of `a_j^{s,R}`. -/
private theorem c09_aux_cut_Q5 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (R : ℝ) (hR : 0 < R) (j : ℕ) (y ξ : ℝ)
    (h : c09_stationary_split_amp_s p R j y ξ ≠ 0) :
    (50 / 51 : ℝ) ^ p ≤ y ∧ 49 / 50 * y ^ (1 / p) ≤ ξ ∧ ξ ≤ 51 / 50 * y ^ (1 / p) ∧
      jb y ≤ 3 * y := by
  unfold c09_stationary_split_amp_s at h
  have hs : c09_stationary_split p y ξ ≠ 0 := by
    intro h0; apply h; rw [h0]; simp
  have ha : c09_positive_kernel_amp R j ξ ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  obtain ⟨hy, hξc⟩ := c09_aux_cut_Q1a p y ξ hs
  obtain ⟨hξ1, -⟩ := c09_aux_cut_A5 j R hR ξ ha
  set c := y ^ (1 / p) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hy _
  have hcp : c ^ p = y := by
    rw [hcdef, ← Real.rpow_mul hy.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  rw [abs_le] at hξc
  have hlo : 49 / 50 * c ≤ ξ := by linarith [hξc.1]
  have hhi : ξ ≤ 51 / 50 * c := by linarith [hξc.2]
  have hc5 : 50 / 51 ≤ c := by linarith
  have hy5 : (50 / 51 : ℝ) ^ p ≤ y := by
    rw [← hcp]; exact Real.rpow_le_rpow (by norm_num) hc5 hp.le
  refine ⟨hy5, hlo, hhi, ?_⟩
  have hy1 : (50 / 51 : ℝ) ≤ y := by
    refine le_trans ?_ hy5
    have := Real.rpow_le_rpow_of_exponent_ge (x := (50 / 51 : ℝ)) (by norm_num) (by norm_num)
      hp1.le
    simpa using this
  have hj : jb y ≤ 1 + y := by
    unfold jb; rw [Real.sqrt_le_left (by linarith)]; nlinarith
  linarith

/-- Blueprint: lem:c09_cutoff_bounds.  Support and derivative bounds for `χ_s`, `χ_ns`, `a_j^R`,
the nonstationary lower bound `|y - ξ^p| ≥ c_*(|y| + ξ^p)`, and localisation of `a_j^{s,R}`. -/
theorem c09_cutoff_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ cstar : ℝ, 0 < cstar ∧ cstar < 1 ∧ ∃ C : ℕ → ℝ, (∀ ℓ, 0 < C ℓ) ∧
      -- (1)
      (∀ y ξ : ℝ, 0 < ξ → c09_stationary_split p y ξ ≠ 0 →
        0 < y ∧ |ξ - y ^ (1 / p)| ≤ y ^ (1 / p) / 50) ∧
      (∀ y ξ : ℝ, 0 < y → |ξ - y ^ (1 / p)| ≤ y ^ (1 / p) / 100 →
        c09_stationary_split p y ξ = 1) ∧
      -- (2)
      (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ y ξ : ℝ, 0 < ξ →
        |iteratedDeriv ℓ (c09_stationary_split p y) ξ| +
          |iteratedDeriv ℓ (c09_stationary_split_chi_ns p y) ξ| ≤ C ℓ * ξ ^ (-(ℓ : ℝ))) ∧
      (∀ y ξ : ℝ, 0 ≤ c09_stationary_split p y ξ ∧ c09_stationary_split p y ξ ≤ 1 ∧
        0 ≤ c09_stationary_split_chi_ns p y ξ ∧ c09_stationary_split_chi_ns p y ξ ≤ 1) ∧
      (∀ y : ℝ, IntegrableOn (fun ξ => |deriv (c09_stationary_split_chi_ns p y) ξ|) (Ioi 0) ∧
        ∫ ξ in Ioi (0 : ℝ), |deriv (c09_stationary_split_chi_ns p y) ξ| ≤ C 0) ∧
      -- (3)
      (∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 →
        ContDiffOn ℝ (⊤ : ℕ∞) (c09_positive_kernel_amp R j) (Ioi 0) ∧
        (∀ ℓ : ℕ, ∀ ξ ∈ Ioc (0 : ℝ) 1, iteratedDeriv ℓ (c09_positive_kernel_amp R j) ξ = 0) ∧
        (∀ ξ : ℝ, c09_positive_kernel_amp R j ξ ≠ 0 → 1 ≤ ξ ∧ ξ ≤ 2 * R) ∧
        (∀ ℓ : ℕ, ∀ ξ : ℝ, 0 < ξ →
          ‖iteratedDeriv ℓ (c09_positive_kernel_amp R j) ξ‖ ≤
            C ℓ * ξ ^ ((j : ℝ) - 2 - ℓ))) ∧
      (∀ R : ℝ, 2 ≤ R →
        IntegrableOn (fun ξ => |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ|)
          (Ioi 0) ∧
        ∫ ξ in Ioi (0 : ℝ), |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ| ≤ C 0) ∧
      -- (4)
      (∀ y ξ : ℝ, 1 ≤ ξ → ξ ∈ tsupport (c09_stationary_split_chi_ns p y) →
        cstar * (|y| + ξ ^ p) ≤ |y - ξ ^ p|) ∧
      (∀ y ξ : ℝ, 1 ≤ ξ → 2 ^ (-(1 / 2 : ℝ)) * jb y ≤ |y| + ξ ^ p) ∧
      -- (5)
      (∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y ξ : ℝ, 0 < ξ →
        c09_stationary_split_amp_s p R j y ξ ≠ 0 →
        (50 / 51 : ℝ) ^ p ≤ y ∧ 49 / 50 * y ^ (1 / p) ≤ ξ ∧ ξ ≤ 51 / 50 * y ^ (1 / p) ∧
          jb y ≤ C 0 * y) := by
  have hp0 : 0 < p := by linarith
  choose B hB0 hB using c09_aux_cut_R4
  set Iρ := ∫ u, |deriv rho u| with hIρ
  have hIρ0 : 0 ≤ Iρ := integral_nonneg fun _ => abs_nonneg _
  set Camp : ℕ → ℝ := fun ℓ => (2 * π)⁻¹ * ∑ k ∈ Finset.range (ℓ + 1), (ℓ.choose k : ℝ) *
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (B i * 2 ^ i + 1) *
          (B (k - i) * 2 ^ (k - i) + 1)) *
        (∑ j' ∈ Finset.range 3, |(descPochhammer ℝ (ℓ - k)).eval ((j' : ℝ) - 2)|) with hCamp
  have hCamp0 : ∀ ℓ, 0 ≤ Camp ℓ := by
    intro ℓ
    rw [hCamp]; dsimp only
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => ?_))
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by have := hB0 i; positivity))
      (by have := hB0 (k - i); positivity)
  set C : ℕ → ℝ := fun ℓ => 2 * B ℓ * 102 ^ ℓ + Camp ℓ + 2 * Iρ + 4 with hC
  have hBn : ∀ ℓ, 0 ≤ 2 * B ℓ * 102 ^ ℓ := fun ℓ => by have := hB0 ℓ; positivity
  have hCpos : ∀ ℓ, 0 < C ℓ := fun ℓ => by
    rw [hC]; dsimp only; linarith [hBn ℓ, hCamp0 ℓ]
  have hBR : ∀ i u, |iteratedDeriv i rho u| ≤ B i := hB
  set cs : ℝ := (1 - (100 / 101 : ℝ) ^ p) / 2 with hcs
  have hq : (100 / 101 : ℝ) ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp0
  have hq0 : 0 ≤ (100 / 101 : ℝ) ^ p := by positivity
  refine ⟨cs, by rw [hcs]; linarith, by rw [hcs]; linarith, C, hCpos,
    fun y ξ _ h => c09_aux_cut_Q1a p y ξ h, fun y ξ hy h => c09_aux_cut_Q1b p y ξ hy h, ?_, ?_, ?_, ?_, ?_, ?_,
    fun y ξ hξ => c09_aux_cut_Q4b p hp0 y ξ hξ, ?_⟩
  · -- (2)
    intro ℓ hℓ y ξ hξ
    rw [c09_aux_cut_S4 p y ℓ hℓ ξ, abs_neg]
    have h := c09_aux_cut_S3 p ℓ (B ℓ) (hB0 ℓ) (hB ℓ) y ξ hξ
    have hξℓ : 0 ≤ ξ ^ (-(ℓ : ℝ)) := (Real.rpow_pos_of_pos hξ _).le
    have : 2 * B ℓ * 102 ^ ℓ ≤ C ℓ := by rw [hC]; dsimp only; linarith [hCamp0 ℓ]
    nlinarith
  · -- ranges
    intro y ξ
    have h : 0 ≤ c09_stationary_split p y ξ ∧ c09_stationary_split p y ξ ≤ 1 := by
      unfold c09_stationary_split; split_ifs
      · exact c09_aux_cut_R2c _
      · norm_num
    unfold c09_stationary_split_chi_ns
    exact ⟨h.1, h.2, by linarith [h.2], by linarith [h.1]⟩
  · -- `∫ |χ_ns'|`
    intro y
    obtain ⟨h1, h2⟩ := c09_aux_cut_S5 p y
    refine ⟨h1, h2.trans ?_⟩
    rw [hC]; dsimp only; linarith [hBn 0, hCamp0 0]
  · -- (3)
    intro R hR j hj
    have hR0 : 0 < R := by linarith
    refine ⟨?_, fun ℓ ξ hξ => ?_, fun ξ h => c09_aux_cut_A5 j R hR0 ξ h, fun ℓ ξ hξ => ?_⟩
    · have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)) *
          (((rho x - 1) * rho (x / R) * x ^ ((j : ℝ) - 2) : ℝ) : ℂ)) :=
        contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (c09_aux_cut_A2 j R))
      refine hsm.contDiffOn.congr fun x hx => ?_
      unfold c09_positive_kernel_amp c09_truncation_theta
      simp only [show 0 < x from hx, ↓reduceIte]
    · rw [c09_aux_cut_A4 j R ℓ ξ hξ.1, c09_aux_cut_A3 j R ℓ ξ ⟨by linarith [hξ.1], hξ.2⟩]; simp
    · refine (c09_aux_cut_A7 B hBR R hR0 j hj ℓ ξ hξ).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hξ _).le
      show Camp ℓ ≤ C ℓ
      rw [hC]; dsimp only; linarith [hBn ℓ]
  · -- (3b)
    intro R hR
    obtain ⟨h1, h2⟩ := c09_aux_cut_S6 R (by linarith)
    refine ⟨h1, h2.trans ?_⟩
    rw [hC]; dsimp only; linarith [hBn 0, hCamp0 0]
  · -- (4)
    intro y ξ hξ hs
    rcases c09_aux_cut_Q4a p hp0 y ξ hs with h | h
    · exact h
    · linarith
  · -- (5)
    intro R hR j hj y ξ hξ h
    obtain ⟨h1, h2, h3, h4⟩ := c09_aux_cut_Q5 p hp0 hp1 R (by linarith) j y ξ h
    refine ⟨h1, h2, h3, h4.trans ?_⟩
    have hy : 0 < y := lt_of_lt_of_le (by positivity) h1
    have : 3 ≤ C 0 := by rw [hC]; dsimp only; linarith [hBn 0, hCamp0 0]
    nlinarith

/-! ### Symbol calculus helpers -/

/-- `χ_s(y,·)` is smooth. -/
theorem c09_aux_chi_s_smooth (p y : ℝ) : ContDiff ℝ ∞ (c09_stationary_split p y) := by
  rcases le_or_gt y 0 with hy | hy
  · rw [c09_aux_cut_S1 p y hy]; exact contDiff_const
  · have e : c09_stationary_split p y = fun ξ => rho (100 / y ^ (1 / p) * ξ + -100) := by
      funext ξ; unfold c09_stationary_split; simp only [hy, ↓reduceIte]
      have hc : 0 < y ^ (1 / p) := Real.rpow_pos_of_pos hy _
      congr 1; field_simp; ring
    rw [e]
    exact c09_aux_cut_R1.comp ((contDiff_const.mul contDiff_id).add contDiff_const)

/-- `χ_ns(y,·)` is smooth. -/
theorem c09_aux_chi_ns_smooth (p y : ℝ) : ContDiff ℝ ∞ (c09_stationary_split_chi_ns p y) :=
  contDiff_const.sub (c09_aux_chi_s_smooth p y)

/-- `θ_R` is smooth. -/
theorem c09_aux_theta_smooth (R : ℝ) : ContDiff ℝ ∞ (c09_truncation_theta R) :=
  c09_aux_cut_R1.comp (contDiff_id.div_const R)

/-- Uniform symbol bounds for `θ_R χ_ns(y,·)`. -/
theorem c09_aux_u_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (N : ℕ) :
    ∃ K, 0 < K ∧ ∀ R : ℝ, 0 < R → ∀ y ξ : ℝ, 0 < ξ → ∀ i ≤ N,
      ‖iteratedDeriv i (fun x => c09_truncation_theta R x * c09_stationary_split_chi_ns p y x) ξ‖
        ≤ K * ξ ^ ((0 : ℝ) - i) := by
  choose B hB0 hB using c09_aux_cut_R4
  obtain ⟨-, -, -, C, hCpos, -, -, h2, hr, -⟩ := c09_cutoff_bounds p hp hp1
  set Kθ := ∑ i ∈ Finset.range (N + 1), (B i * 2 ^ i + 1) with hKθ
  set Kχ := ∑ i ∈ Finset.range (N + 1), C i + 1 with hKχ
  have hKθ0 : 0 ≤ Kθ := Finset.sum_nonneg fun i _ => by have := hB0 i; positivity
  have hKχ0 : 0 < Kχ := by
    have := Finset.sum_nonneg (s := Finset.range (N + 1)) fun i _ => (hCpos i).le
    linarith
  refine ⟨2 ^ N * Kθ * Kχ + 1, by positivity, fun R hR y ξ hξ i hi => ?_⟩
  have hθ : ∀ k ≤ i, ‖iteratedDeriv k (c09_truncation_theta R) ξ‖ ≤ Kθ * ξ ^ ((0 : ℝ) - k) := by
    intro k hk
    have := c09_aux_cut_F2b B hB R hR k ξ hξ
    rw [Real.norm_eq_abs]
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hξ _).le)
    exact Finset.single_le_sum (f := fun i => B i * 2 ^ i + 1)
      (fun i _ => by have := hB0 i; positivity) (Finset.mem_range.mpr (by omega))
  have hχ : ∀ k ≤ i, ‖iteratedDeriv k (c09_stationary_split_chi_ns p y) ξ‖ ≤
      Kχ * ξ ^ ((0 : ℝ) - k) := by
    intro k hk
    have hξk : 0 < ξ ^ ((0 : ℝ) - k) := Real.rpow_pos_of_pos hξ _
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero, Real.rpow_zero, mul_one]
      obtain ⟨-, -, h3, h4⟩ := hr y ξ
      have : (0:ℝ) ≤ ∑ i ∈ Finset.range (N + 1), C i :=
        Finset.sum_nonneg fun i _ => (hCpos i).le
      rw [abs_le]; constructor <;> linarith [hKχ0]
    · have := h2 k hk0 y ξ hξ
      have h' : |iteratedDeriv k (c09_stationary_split_chi_ns p y) ξ| ≤ C k * ξ ^ (-(k : ℝ)) := by
        linarith [abs_nonneg (iteratedDeriv k (c09_stationary_split p y) ξ)]
      rw [zero_sub]
      refine h'.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hξ _).le)
      have : C k ≤ ∑ i ∈ Finset.range (N + 1), C i :=
        Finset.single_le_sum (f := C) (fun i _ => (hCpos i).le) (Finset.mem_range.mpr (by omega))
      linarith
  have := c09_aux_leib (c09_truncation_theta R) (c09_stationary_split_chi_ns p y) ξ hξ i
    ((c09_aux_theta_smooth R).contDiffAt.of_le (by exact_mod_cast le_top))
    ((c09_aux_chi_ns_smooth p y).contDiffAt.of_le (by exact_mod_cast le_top)) Kθ Kχ 0 0 hθ hχ
  refine this.trans ?_
  rw [zero_add]
  have : (2 : ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hi
  have hξk : 0 < ξ ^ ((0 : ℝ) - i) := Real.rpow_pos_of_pos hξ _
  have : 2 ^ i * Kθ * Kχ ≤ 2 ^ N * Kθ * Kχ := by gcongr
  nlinarith

/-- The nonstationary lower bound on `tsupport χ_ns`, `ξ > 0`. -/
theorem c09_aux_good (p : ℝ) (hp : 0 < p) (y ξ : ℝ) (hξ : 0 < ξ)
    (hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)) :
    (1 - (100 / 101 : ℝ) ^ p) / 2 * (|y| + ξ ^ p) ≤ |y - ξ ^ p| := by
  rcases c09_aux_cut_Q4a p hp y ξ hs with h | h
  · exact h
  · linarith

/-- Uniform symbol bounds for `χ_ns(y,·)`. -/
theorem c09_aux_chi_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (N : ℕ) :
    ∃ K, 0 < K ∧ ∀ y ξ : ℝ, 0 < ξ → ∀ k ≤ N,
      ‖iteratedDeriv k (c09_stationary_split_chi_ns p y) ξ‖ ≤ K * ξ ^ ((0 : ℝ) - k) := by
  obtain ⟨-, -, -, C, hCpos, -, -, h2, hr, -⟩ := c09_cutoff_bounds p hp hp1
  have hS : (0:ℝ) ≤ ∑ i ∈ Finset.range (N + 1), C i := Finset.sum_nonneg fun i _ => (hCpos i).le
  refine ⟨∑ i ∈ Finset.range (N + 1), C i + 1, by linarith, fun y ξ hξ k hk => ?_⟩
  have hξk : 0 < ξ ^ ((0 : ℝ) - k) := Real.rpow_pos_of_pos hξ _
  rw [Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero, Real.rpow_zero, mul_one]
    obtain ⟨-, -, h3, h4⟩ := hr y ξ
    rw [abs_le]; constructor <;> linarith
  · have := h2 k hk0 y ξ hξ
    have h' : |iteratedDeriv k (c09_stationary_split_chi_ns p y) ξ| ≤ C k * ξ ^ (-(k : ℝ)) := by
      linarith [abs_nonneg (iteratedDeriv k (c09_stationary_split p y) ξ)]
    rw [zero_sub]
    refine h'.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hξ _).le)
    have : C k ≤ ∑ i ∈ Finset.range (N + 1), C i :=
      Finset.single_le_sum (f := C) (fun i _ => (hCpos i).le) (Finset.mem_range.mpr (by omega))
    linarith

/-- `a_j^R` is smooth on `(0,∞)`. -/
theorem c09_aux_amp_smooth (R : ℝ) (j : ℕ) :
    ContDiffOn ℝ ∞ (c09_positive_kernel_amp R j) (Ioi 0) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)) *
      (((rho x - 1) * rho (x / R) * x ^ ((j : ℝ) - 2) : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (c09_aux_cut_A2 j R))
  refine hsm.contDiffOn.congr fun x hx => ?_
  unfold c09_positive_kernel_amp c09_truncation_theta
  simp only [show 0 < x from hx, ↓reduceIte]

/-! #### Helpers: the amplitude `a_j^R` and the kernel integrand -/

/-- `a_j^R = 0` on `(-∞, 1]`. -/
theorem c09_aux_amp_zero_of_le_one (R : ℝ) (j : ℕ) (ξ : ℝ) (hξ : ξ ≤ 1) :
    c09_positive_kernel_amp R j ξ = 0 := by
  unfold c09_positive_kernel_amp
  split_ifs with h
  · rw [c09_aux_cut_R2a ξ (abs_le.mpr ⟨by linarith, hξ⟩)]; simp
  · rfl

/-- `a_j^R` is continuous on `ℝ`. -/
theorem c09_aux_amp_continuous (R : ℝ) (j : ℕ) : Continuous (c09_positive_kernel_amp R j) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · exact ((c09_aux_amp_smooth R j).continuousOn).continuousAt (isOpen_Ioi.mem_nhds hx)
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [isOpen_Iio.mem_nhds (show x ∈ Iio (1 : ℝ) by simp only [mem_Iio]; linarith)]
      with ξ hξ
    exact (c09_aux_amp_zero_of_le_one R j ξ (le_of_lt hξ)).symm

/-- `|a_j^R| ≤ 1` for `j ≤ 2`. -/
theorem c09_aux_amp_norm_le (R : ℝ) (j : ℕ) (hj : j ≤ 2) (ξ : ℝ) :
    ‖c09_positive_kernel_amp R j ξ‖ ≤ 1 := by
  rcases le_or_gt ξ 1 with h | h
  · rw [c09_aux_amp_zero_of_le_one R j ξ h, norm_zero]; norm_num
  · unfold c09_positive_kernel_amp c09_truncation_theta
    rw [if_pos (by linarith)]
    have h1 := c09_aux_cut_R2c ξ
    have h2 := c09_aux_cut_R2c (ξ / R)
    have hj' : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have h3 : ξ ^ ((j : ℝ) - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
    have h4 : 0 < ξ ^ ((j : ℝ) - 2) := Real.rpow_pos_of_pos (by linarith) _
    have hc : ‖-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_neg, norm_pow, Complex.norm_I, one_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by positivity)]
      linarith [Real.pi_gt_three]
    have hx : ‖(((rho ξ - 1) * rho (ξ / R) * ξ ^ ((j : ℝ) - 2) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos h4,
        abs_of_nonneg h2.1, abs_of_nonpos (by linarith [h1.2])]
      have : -(rho ξ - 1) ≤ 1 := by linarith [h1.1]
      have : 0 ≤ -(rho ξ - 1) := by linarith [h1.2]
      exact mul_le_one₀ (mul_le_one₀ (by linarith) h2.1 h2.2) h4.le h3
    calc _ ≤ ‖-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)‖ *
          ‖(((rho ξ - 1) * rho (ξ / R) * ξ ^ ((j : ℝ) - 2) : ℝ) : ℂ)‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num

/-- `w_E > 0`. -/
theorem c09_aux_weightsE_pos (p z : ℝ) : 0 < c09_weights_E p z := by
  unfold c09_weights_E
  have := c09_aux_jb_pos z
  split_ifs <;> exact Real.rpow_pos_of_pos this _

/-- `Φ₀` is continuous. -/
theorem c09_aux_Phi0_continuous (p : ℝ) (hp : 0 < p) : Continuous (Phi0 p) := by
  unfold Phi0
  have := Continuous.rpow_const continuous_abs (fun _ : ℝ => Or.inr hp.le)
  fun_prop

/-- The integrand of `K_{+,j}^R` is jointly continuous in `((y,z),ξ)`. -/
theorem c09_aux_kernel_integrand_cont (p : ℝ) (hp : 0 < p) (R : ℝ) (j : ℕ) :
    Continuous (fun q : (ℝ × ℝ) × ℝ => c09_positive_kernel_amp R j q.2 *
      Complex.exp (Complex.I * ((q.1.1 * q.2 - Phi0 p q.2 : ℝ) : ℂ)) *
        c09_tail_integral p q.1.2 q.2) := by
  have hE := c09_aux_tail_joint p hp
  have hPhi := c09_aux_Phi0_continuous p hp
  have hA := c09_aux_amp_continuous R j
  have h1 : Continuous fun q : (ℝ × ℝ) × ℝ => c09_tail_integral p q.1.2 q.2 :=
    hE.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.2, q.2)) (by fun_prop)
  fun_prop

/-- `θ_R(ξ) = 1` for `|ξ| ≤ R`. -/
theorem c09_aux_theta_one (R ξ : ℝ) (hR : 0 < R) (hξ : |ξ| ≤ R) : c09_truncation_theta R ξ = 1 := by
  unfold c09_truncation_theta
  apply c09_aux_cut_R2a
  rw [abs_div, abs_of_pos hR, div_le_one hR]; exact hξ

/-- `θ_R(ξ) = 0` for `|ξ| ≥ 2R`. -/
theorem c09_aux_theta_zero (R ξ : ℝ) (hR : 0 < R) (hξ : 2 * R ≤ |ξ|) :
    c09_truncation_theta R ξ = 0 := by
  unfold c09_truncation_theta
  apply c09_aux_cut_R2b
  rw [abs_div, abs_of_pos hR, le_div_iff₀ hR]; exact hξ

/-- `0 ≤ θ_R ≤ 1`. -/
theorem c09_aux_theta_bounds (R ξ : ℝ) : 0 ≤ c09_truncation_theta R ξ ∧ c09_truncation_theta R ξ ≤ 1 :=
  c09_aux_cut_R2c _

/-- `θ_R` is continuous. -/
theorem c09_aux_theta_continuous (R : ℝ) : Continuous (c09_truncation_theta R) :=
  (c09_aux_theta_smooth R).continuous

/-- `\widehat{𝒯₊G}(ξ) = 0` for `ξ ≤ 1`. -/
theorem c09_aux_That_zero (p : ℝ) (G : ℝ → ℝ) (ξ : ℝ) (hξ : ξ ≤ 1) : c09_T_plus_hat p G ξ = 0 := by
  unfold c09_T_plus_hat
  split_ifs with h
  · rw [c09_aux_cut_R2a ξ (abs_le.mpr ⟨by linarith, hξ⟩)]; simp
  · rfl

/-- `𝒯₊G(y) = (2π)⁻¹ ∫_{ξ>0} \widehat{𝒯₊G}(ξ) e^{iyξ} dξ`. -/
theorem c09_aux_T_plus_Ioi (p : ℝ) (G : ℝ → ℝ) (y : ℝ) :
    c09_T_plus p G y = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ in Ioi (0 : ℝ), c09_T_plus_hat p G ξ *
      Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) := by
  unfold c09_T_plus invFourierT
  congr 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro ξ hξ
  simp only [mem_Ioi, not_lt] at hξ
  simp [c09_T_plus_hat, not_lt.mpr hξ]

/-- `\widehat{𝒯₊G}` is continuous for `G ∈ Y_γ`. -/
theorem c09_aux_That_continuous (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) :
    Continuous (c09_T_plus_hat p G) := by
  have hT := (c09_conjugate_symmetry p hp hp1 γ hγ G hG).1
  have hc : Continuous fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ :=
    (Complex.continuous_ofReal.comp (continuous_const.sub c09_aux_cut_R1.continuous)).mul hT
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · refine hc.continuousAt.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with ξ hξ
    have hξ' : 0 < ξ := hξ
    simp only [c09_T_plus_hat, hξ', if_true]
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [isOpen_Iio.mem_nhds (show x ∈ Iio (1 : ℝ) by simp only [mem_Iio]; linarith)]
      with ξ hξ
    exact (c09_aux_That_zero p G ξ (le_of_lt hξ)).symm

/-- `HasDerivAt (y ↦ e^{iyξ}) (iξ e^{iyξ})`. -/
theorem c09_aux_hasDerivAt_exp_Iyx (ξ y : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))
      (Complex.I * (ξ : ℂ) * Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) y := by
  have h : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ) * (ξ : ℂ)) (Complex.I * (ξ : ℂ)) y := by
    simpa using (((hasDerivAt_id y).ofReal_comp).const_mul Complex.I).mul_const (ξ : ℂ)
  have h2 := h.cexp
  convert h2 using 1
  ring

/-! ### Truncated kernel representation: analytic sublemmas -/

/-- Blueprint: lem:c09_truncated_smooth.  For `G ∈ Ỹ_γ`, `R ≥ 2`: each
`ξ ↦ (iξ)^j θ_R(ξ) \widehat{𝒯₊G}(ξ)` is integrable and vanishes outside `[1,2R]`; `𝒯₊^R G` is
`C^∞` with `∂_y^j 𝒯₊^R G(y) = (2π)⁻¹ ∫₁^{2R} (iξ)^j θ_R \widehat{𝒯₊G} e^{iyξ} dξ`; and
`|∂_y^j 𝒯₊^R G| ≤ C_{p,γ,R,j} ‖G‖_{Y_γ}`. -/
theorem c09_truncated_smooth (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    (∀ G ∈ Y_gamma_tilde p γ, ∀ R : ℝ, 2 ≤ R →
      (∀ j : ℕ, Integrable (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j *
          (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ)) ∧
      (∀ j : ℕ, ∀ ξ : ℝ, ξ ∉ Icc 1 (2 * R) →
        (Complex.I * (ξ : ℂ)) ^ j * (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) (c09_truncation p R G) ∧
      (∀ j : ℕ, ∀ y : ℝ,
        IntervalIntegrable (fun ξ : ℝ => (Complex.I * (ξ : ℂ)) ^ j *
          (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ *
            Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) volume 1 (2 * R) ∧
        iteratedDeriv j (c09_truncation p R G) y =
          ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ in (1 : ℝ)..(2 * R), (Complex.I * (ξ : ℂ)) ^ j *
            (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ *
              Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)))) ∧
    (∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma_tilde p γ, ∀ y : ℝ,
      ‖iteratedDeriv j (c09_truncation p R G) y‖ ≤ C * yNorm p γ G) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨CT, hCT, hTF⟩ := c09_tail_formula p hp hp1 γ hγ
  -- the integrands
  set f : (ℝ → ℝ) → ℝ → ℕ → ℝ → ℂ := fun G R j ξ =>
    (Complex.I * (ξ : ℂ)) ^ j * (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ with hf
  set e : ℝ → ℝ → ℂ := fun y ξ => Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) with he
  have hen : ∀ y ξ, ‖e y ξ‖ = 1 := fun y ξ => c09_aux_norm_exp_pos y ξ
  have hec : ∀ y, Continuous (e y) := fun y =>
    show Continuous (fun ξ : ℝ => Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ))) by fun_prop
  have hfc : ∀ G ∈ Y_gamma p γ, ∀ R j, Continuous (f G R j) := by
    intro G hG R j
    have := c09_aux_That_continuous p hp hp1 γ hγ G hG
    have hθ := Complex.continuous_ofReal.comp (c09_aux_theta_continuous R)
    simp only [hf]; fun_prop
  have hvan : ∀ G R, 2 ≤ R → ∀ j ξ, ξ ∉ Ioc 1 (2 * R) → f G R j ξ = 0 := by
    intro G R hR j ξ hξ
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hξ
    simp only [hf]
    rcases hξ with h | h
    · rw [c09_aux_That_zero p G ξ h, mul_zero]
    · rw [c09_aux_theta_zero R ξ (by linarith) (by rw [abs_of_pos (by linarith)]; exact h.le)]
      simp
  have hbd : ∀ G ∈ Y_gamma_tilde p γ, ∀ R, 2 ≤ R → ∀ j ξ,
      ‖f G R j ξ‖ ≤ ((2 * R) ^ j * CT * yNorm p γ G) * (Set.indicator (Ioc 1 (2 * R)) (fun _ => (1 : ℝ)) ξ) := by
    intro G hG R hR j ξ
    by_cases hξ : ξ ∈ Ioc 1 (2 * R)
    · rw [Set.indicator_of_mem hξ, mul_one]
      obtain ⟨-, -, -, -, h4⟩ := hTF G hG.1
      have hb := (h4 hG).2.1 ξ
      rw [Set.indicator_of_mem (show ξ ∈ Ioi (1 : ℝ) from hξ.1)] at hb
      have hξ2 : ξ ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hξ.1.le (by norm_num)
      have hyN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
      simp only [hf]
      rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith [hξ.1]),
        abs_of_nonneg (c09_aux_theta_bounds R ξ).1]
      have h1 : ξ ^ j ≤ (2 * R) ^ j := pow_le_pow_left₀ (by linarith [hξ.1]) hξ.2 j
      have h2 := (c09_aux_theta_bounds R ξ).2
      calc ξ ^ j * c09_truncation_theta R ξ * ‖c09_T_plus_hat p G ξ‖
          ≤ (2 * R) ^ j * 1 * (CT * yNorm p γ G * 1) := by
            gcongr
            · exact (c09_aux_theta_bounds R ξ).1
            · exact hb.trans (by gcongr)
        _ = _ := by ring
    · rw [hvan G R hR j ξ hξ, norm_zero, Set.indicator_of_notMem hξ, mul_zero]
  have hgi : ∀ (K : ℝ) (R : ℝ), Integrable (fun ξ : ℝ => K * Set.indicator (Ioc 1 (2 * R)) (fun _ => (1 : ℝ)) ξ) := by
    intro K R
    have : Integrable (Set.indicator (Ioc (1 : ℝ) (2 * R)) (fun _ => (1 : ℝ))) :=
      (continuous_const.integrableOn_Ioc).integrable_indicator measurableSet_Ioc
    exact this.const_mul K
  have hfi : ∀ G ∈ Y_gamma_tilde p γ, ∀ R, 2 ≤ R → ∀ j, Integrable (f G R j) := fun G hG R hR j =>
    (hgi _ R).mono' (hfc G hG.1 R j).aestronglyMeasurable (Eventually.of_forall (hbd G hG R hR j))
  have hfei : ∀ G ∈ Y_gamma_tilde p γ, ∀ R, 2 ≤ R → ∀ j y,
      Integrable (fun ξ => f G R j ξ * e y ξ) := fun G hG R hR j y =>
    (hfi G hG R hR j).mul_bdd (hec y).aestronglyMeasurable
      (Eventually.of_forall fun ξ => (hen y ξ).le)
  -- derivative of `F_j(y) = ∫ f_j e_y`
  have hder : ∀ G ∈ Y_gamma_tilde p γ, ∀ R, 2 ≤ R → ∀ j y,
      HasDerivAt (fun y => ∫ ξ, f G R j ξ * e y ξ) (∫ ξ, f G R (j + 1) ξ * e y ξ) y := by
    intro G hG R hR j y
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := y)
      (F := fun y ξ => f G R j ξ * e y ξ) (F' := fun y ξ => f G R (j + 1) ξ * e y ξ)
      (s := univ) (bound := fun ξ => ‖f G R (j + 1) ξ‖) Filter.univ_mem
      (Eventually.of_forall fun y => (hfei G hG R hR j y).aestronglyMeasurable)
      (hfei G hG R hR j y) (hfei G hG R hR (j + 1) y).aestronglyMeasurable
      (Eventually.of_forall fun ξ x _ => by rw [norm_mul, hen, mul_one])
      (hfi G hG R hR (j + 1)).norm
      (Eventually.of_forall fun ξ x _ => by
        have := (c09_aux_hasDerivAt_exp_Iyx ξ x).const_mul (f G R j ξ)
        convert this using 1
        simp only [hf, he, pow_succ]; ring)
    exact h.2
  have hiter : ∀ G ∈ Y_gamma_tilde p γ, ∀ R, 2 ≤ R → ∀ j,
      iteratedDeriv j (c09_truncation p R G) =
        fun y => ((2 * π : ℝ) : ℂ)⁻¹ * ∫ ξ, f G R j ξ * e y ξ := by
    intro G hG R hR j
    induction j with
    | zero =>
      funext y
      rw [iteratedDeriv_zero]
      unfold c09_truncation
      congr 1
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [hf, he, pow_zero, one_mul]
      · intro ξ hξ
        simp only [mem_Ioi, not_lt] at hξ
        simp [c09_aux_That_zero p G ξ (by linarith)]
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      exact ((hder G hG R hR n y).const_mul _).deriv
  have hdiff : ∀ G ∈ Y_gamma_tilde p γ, ∀ R, 2 ≤ R → ∀ j,
      Differentiable ℝ (iteratedDeriv j (c09_truncation p R G)) := by
    intro G hG R hR j
    rw [hiter G hG R hR j]
    exact fun y => ((hder G hG R hR j y).const_mul _).differentiableAt
  have hint : ∀ G ∈ Y_gamma_tilde p γ, ∀ R, 2 ≤ R → ∀ j y,
      (∫ ξ, f G R j ξ * e y ξ) = ∫ ξ in (1 : ℝ)..(2 * R), f G R j ξ * e y ξ := by
    intro G hG R hR j y
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro ξ hξ
    rw [hvan G R hR j ξ hξ, zero_mul]
  refine ⟨fun G hG R hR => ⟨fun j => hfi G hG R hR j, fun j ξ hξ => hvan G R hR j ξ
    (fun h => hξ ⟨h.1.le, h.2⟩), contDiff_of_differentiable_iteratedDeriv
    (fun m _ => hdiff G hG R hR m), fun j y => ⟨?_, ?_⟩⟩, ?_⟩
  · exact ((hfc G hG.1 R j).mul (hec y)).intervalIntegrable _ _
  · rw [hiter G hG R hR j]; exact congrArg _ (hint G hG R hR j y)
  · intro R hR j
    refine ⟨(2 * R) ^ j * CT * (2 * R) + 1, by positivity, fun G hG y => ?_⟩
    have hyN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    rw [hiter G hG R hR j, norm_mul]
    have hn : ‖∫ ξ, f G R j ξ * e y ξ‖ ≤ ∫ ξ, (2 * R) ^ j * CT * yNorm p γ G *
        Set.indicator (Ioc 1 (2 * R)) (fun _ => (1 : ℝ)) ξ :=
      norm_integral_le_of_norm_le (hgi ((2 * R) ^ j * CT * yNorm p γ G) R)
      (Eventually.of_forall fun ξ => by
        rw [norm_mul, hen y ξ, mul_one]; exact hbd G hG R hR j ξ)
    rw [integral_const_mul] at hn
    have hvol : ∫ ξ, Set.indicator (Ioc 1 (2 * R)) (fun _ => (1 : ℝ)) ξ = 2 * R - 1 := by
      rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, mul_one,
        Real.volume_real_Ioc_of_le (by linarith)]
    rw [hvol] at hn
    have hπ : ‖((2 * π : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
    have h0 : 0 ≤ (2 * R) ^ j * CT * yNorm p γ G * (2 * R - 1) := by
      have : 0 ≤ 2 * R - 1 := by linarith
      positivity
    calc _ ≤ 1 * ((2 * R) ^ j * CT * yNorm p γ G * (2 * R - 1)) := by gcongr
      _ ≤ ((2 * R) ^ j * CT * (2 * R) + 1) * yNorm p γ G := by
        have : 0 ≤ (2 * R) ^ j * CT * yNorm p γ G := by positivity
        nlinarith

/-- Blueprint: lem:c09_kernel_majorant.  For `R ≥ 2` there is `C_{p,R}` (independent of `j,y,z`)
with `∫₁^{2R} |a_j^R E_z| ≤ C_{p,R} w_E(z)` and `|K_{+,j}^R(y,z)| ≤ C_{p,R} w_E(z)`, the defining
integral being absolutely convergent; and `K_{+,j}^R` is jointly continuous. -/
theorem c09_kernel_majorant (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ R : ℝ, 2 ≤ R → ∃ C, 0 < C ∧ ∀ j : ℕ, j ≤ 2 →
      (∀ y z : ℝ,
        IntervalIntegrable (fun ξ => c09_positive_kernel_amp R j ξ *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ)
          volume 1 (2 * R) ∧
        (∫ ξ in (1 : ℝ)..(2 * R), ‖c09_positive_kernel_amp R j ξ * c09_tail_integral p z ξ‖) ≤
          C * c09_weights_E p z ∧
        ‖c09_positive_kernel p R j y z‖ ≤ C * c09_weights_E p z) ∧
      Continuous (fun q : ℝ × ℝ => c09_positive_kernel p R j q.1 q.2) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, -, ⟨CE, hCE, hE⟩, -⟩ := c09_tail_basic p hp hp1
  intro R hR
  refine ⟨2 * R * CE + 1, by positivity, fun j hj => ⟨fun y z => ?_, ?_⟩⟩
  · have hcont : Continuous (fun ξ => c09_positive_kernel_amp R j ξ *
        Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ) :=
      (c09_aux_kernel_integrand_cont p hp0 R j).comp (f := fun ξ : ℝ => ((y, z), ξ))
        (by fun_prop)
    have hw := c09_aux_weightsE_pos p z
    have hpt : ∀ ξ ∈ Set.uIoc (1 : ℝ) (2 * R),
        ‖c09_positive_kernel_amp R j ξ * c09_tail_integral p z ξ‖ ≤ CE * c09_weights_E p z := by
      intro ξ hξ
      rw [uIoc_of_le (by linarith)] at hξ
      rw [norm_mul]
      calc _ ≤ 1 * (CE * c09_weights_E p z) := by
            gcongr
            · exact c09_aux_amp_norm_le R j hj ξ
            · exact hE z ξ (by linarith [hξ.1])
        _ = _ := one_mul _
    have hlen : CE * c09_weights_E p z * |2 * R - 1| ≤ (2 * R * CE + 1) * c09_weights_E p z := by
      rw [abs_of_pos (by linarith)]; nlinarith
    refine ⟨hcont.intervalIntegrable _ _, ?_, ?_⟩
    · have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := 2 * R)
        (f := fun ξ => ‖c09_positive_kernel_amp R j ξ * c09_tail_integral p z ξ‖)
        (C := CE * c09_weights_E p z) (fun ξ hξ => by rw [norm_norm]; exact hpt ξ hξ)
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (h.trans hlen))
    · unfold c09_positive_kernel
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun ξ hξ => ?_)).trans hlen
      rw [norm_mul, norm_mul, c09_aux_norm_exp_phase, mul_one, ← norm_mul]
      exact hpt ξ hξ
  · unfold c09_positive_kernel
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (q : ℝ × ℝ) (ξ : ℝ) => c09_positive_kernel_amp R j ξ *
        Complex.exp (Complex.I * ((q.1 * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p q.2 ξ)
      (c09_aux_kernel_integrand_cont p hp0 R j) 1 (2 * R)

/-- Blueprint: lem:c09_kernel_fubini.  For `G ∈ Y_γ`, `R ≥ 2`, `j ≤ 2`, `y ∈ ℝ`, the function
`(ξ,z) ↦ a_j^R(ξ) e^{i(yξ-Φ₀(ξ))} E_z(ξ) G'(z)` is integrable on `[1,2R] × ℝ` (with the double
integral of its modulus `≤ C_{p,γ,R} ‖G‖_{Y_γ}`), `z ↦ K_{+,j}^R(y,z) G'(z)` is integrable, and
`∫₁^{2R} a_j^R e^{i(yξ-Φ₀)} F_G dξ = ∫ K_{+,j}^R(y,z) G'(z) dz`. -/
theorem c09_kernel_fubini (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∀ R : ℝ, 2 ≤ R → ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma p γ, ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
      Integrable (fun q : ℝ × ℝ => c09_positive_kernel_amp R j q.1 *
          Complex.exp (Complex.I * ((y * q.1 - Phi0 p q.1 : ℝ) : ℂ)) *
            c09_tail_integral p q.2 q.1 * ((deriv G q.2 : ℝ) : ℂ))
        ((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume) ∧
      (∫ q, ‖c09_positive_kernel_amp R j q.1 *
          Complex.exp (Complex.I * ((y * q.1 - Phi0 p q.1 : ℝ) : ℂ)) *
            c09_tail_integral p q.2 q.1 * ((deriv G q.2 : ℝ) : ℂ)‖
        ∂((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume)) ≤ C * yNorm p γ G ∧
      Integrable (fun z => c09_positive_kernel p R j y z * ((deriv G z : ℝ) : ℂ)) ∧
      (∫ ξ in (1 : ℝ)..(2 * R), c09_positive_kernel_amp R j ξ *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral_F p G ξ) =
        ∫ z, c09_positive_kernel p R j y z * ((deriv G z : ℝ) : ℂ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, -, ⟨CE, hCE, hE⟩, -⟩ := c09_tail_basic p hp hp1
  obtain ⟨-, -, -, ⟨CW, hCW, hW⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
  intro R hR
  refine ⟨2 * R * CE * CW + 1, by positivity, fun G hG j hj y => ?_⟩
  obtain ⟨-, -, hGw, hsum⟩ := hW G hG
  have hyN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
  set H : ℝ × ℝ → ℂ := fun q => c09_positive_kernel_amp R j q.1 *
    Complex.exp (Complex.I * ((y * q.1 - Phi0 p q.1 : ℝ) : ℂ)) *
      c09_tail_integral p q.2 q.1 * ((deriv G q.2 : ℝ) : ℂ) with hH
  set B : ℝ × ℝ → ℝ := fun q => (1 : ℝ) * (CE * (|deriv G q.2| * c09_weights_E p q.2)) with hB
  have hbound : ∀ q, ‖H q‖ ≤ B q := by
    intro q
    have hw := c09_aux_weightsE_pos p q.2
    have hB0 : 0 ≤ B q := by simp only [hB]; positivity
    rcases le_or_gt q.1 1 with h | h
    · simp only [hH]; rw [c09_aux_amp_zero_of_le_one R j q.1 h]; simp only [zero_mul, norm_zero]
      exact hB0
    · simp only [hH, hB]
      rw [norm_mul, norm_mul, norm_mul, c09_aux_norm_exp_phase, mul_one, Complex.norm_real,
        Real.norm_eq_abs, one_mul]
      calc ‖c09_positive_kernel_amp R j q.1‖ * ‖c09_tail_integral p q.2 q.1‖ * |deriv G q.2|
          ≤ 1 * (CE * c09_weights_E p q.2) * |deriv G q.2| := by
            gcongr
            · exact c09_aux_amp_norm_le R j hj q.1
            · exact hE q.2 q.1 (by linarith)
        _ = _ := by ring
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc (1 : ℝ) (2 * R))) :=
    continuous_const.integrableOn_Ioc
  have hBi : Integrable B ((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume) := Integrable.mul_prod h1 (hGw.const_mul CE)
  have hcont : Continuous fun q : ℝ × ℝ => c09_positive_kernel_amp R j q.1 *
      Complex.exp (Complex.I * ((y * q.1 - Phi0 p q.1 : ℝ) : ℂ)) * c09_tail_integral p q.2 q.1 :=
    (c09_aux_kernel_integrand_cont p hp0 R j).comp (f := fun q : ℝ × ℝ => ((y, q.2), q.1))
      (by fun_prop)
  have hmeas : AEStronglyMeasurable H ((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume) :=
    hcont.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp ((measurable_deriv G).comp measurable_snd)).aestronglyMeasurable)
  have hHi : Integrable H ((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume) := hBi.mono' hmeas (Eventually.of_forall hbound)
  -- the norm bound
  have hnorm : (∫ q, ‖H q‖ ∂((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume)) ≤ (2 * R * CE * CW + 1) * yNorm p γ G := by
    have hle : (∫ q, ‖H q‖ ∂((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume)) ≤ ∫ q, B q ∂((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume) := integral_mono hHi.norm hBi hbound
    have hBint : ∫ q, B q ∂((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume) = (2 * R - 1) * (CE * ∫ z, |deriv G z| * c09_weights_E p z) := by
      simp only [hB]
      rw [integral_prod_mul (fun _ : ℝ => (1 : ℝ))
        (fun z => CE * (|deriv G z| * c09_weights_E p z)), integral_const_mul, setIntegral_const,
        Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul, mul_one]
    have hw3 : (∫ z, |deriv G z| * c09_weights_E p z) ≤ CW * yNorm p γ G := by
      have a1 : 0 ≤ ∫ z, |G z| := integral_nonneg fun _ => abs_nonneg _
      have a2 : 0 ≤ ∫ z, |deriv G z| := integral_nonneg fun _ => abs_nonneg _
      linarith
    have hw0 : 0 ≤ ∫ z, |deriv G z| * c09_weights_E p z :=
      integral_nonneg fun z => mul_nonneg (abs_nonneg _) (c09_aux_weightsE_pos p z).le
    rw [hBint] at hle
    have : (2 * R - 1) * (CE * ∫ z, |deriv G z| * c09_weights_E p z) ≤
        (2 * R) * (CE * (CW * yNorm p γ G)) := by
      gcongr <;> linarith
    nlinarith
  -- Fubini
  have hK : ∀ z, (∫ ξ, H (ξ, z) ∂(volume.restrict (Ioc (1 : ℝ) (2 * R)))) =
      c09_positive_kernel p R j y z * ((deriv G z : ℝ) : ℂ) := by
    intro z
    unfold c09_positive_kernel
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_mul_const]
  have hF : ∀ ξ, (∫ z, H (ξ, z)) = c09_positive_kernel_amp R j ξ *
      Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral_F p G ξ := by
    intro ξ
    unfold c09_tail_integral_F
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hH]; ring
  refine ⟨hHi, hnorm, ?_, ?_⟩
  · obtain ⟨Cm, hCm, hmaj⟩ := c09_kernel_majorant p hp hp1 R hR
    have hKc : Continuous fun z => c09_positive_kernel p R j y z :=
      (hmaj j hj).2.comp (f := fun z : ℝ => (y, z)) (by fun_prop)
    refine Integrable.mono' (hGw.const_mul Cm)
      (hKc.aestronglyMeasurable.mul
        (Complex.measurable_ofReal.comp (measurable_deriv G)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖c09_positive_kernel p R j y z‖ * |deriv G z|
        ≤ (Cm * c09_weights_E p z) * |deriv G z| := by
          gcongr; exact ((hmaj j hj).1 y z).2.2
      _ = Cm * (|deriv G z| * c09_weights_E p z) := by ring
  · rw [intervalIntegral.integral_of_le (by linarith)]
    calc (∫ ξ in Ioc (1 : ℝ) (2 * R), c09_positive_kernel_amp R j ξ *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral_F p G ξ)
        = ∫ ξ in Ioc (1 : ℝ) (2 * R), ∫ z, H (ξ, z) := by
          refine integral_congr_ae (Eventually.of_forall fun ξ => ?_); exact (hF ξ).symm
      _ = ∫ q, H q ∂((volume.restrict (Ioc (1 : ℝ) (2 * R))).prod volume) := (integral_prod H hHi).symm
      _ = ∫ z, ∫ ξ, H (ξ, z) ∂(volume.restrict (Ioc (1 : ℝ) (2 * R))) := integral_prod_symm H hHi
      _ = _ := integral_congr_ae (Eventually.of_forall hK)

/-- Blueprint: lem:c09_truncated_representation.  For `G ∈ Ỹ_γ`, `R ≥ 2`, `j ≤ 2`:
`∂_y^j 𝒯₊^R G(y) = ∫ K_{+,j}^R(y,z) G'(z) dz`, absolutely convergent. -/
theorem c09_truncated_representation (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∀ G ∈ Y_gamma_tilde p γ, ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
      Integrable (fun z => c09_positive_kernel p R j y z * ((deriv G z : ℝ) : ℂ)) ∧
      iteratedDeriv j (c09_truncation p R G) y =
        ∫ z, c09_positive_kernel p R j y z * ((deriv G z : ℝ) : ℂ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hsm, -⟩ := c09_truncated_smooth p hp hp1 γ hγ
  obtain ⟨CT, hCT, hTF⟩ := c09_tail_formula p hp hp1 γ hγ
  intro G hG R hR j hj y
  obtain ⟨Cf, hCf, hfub⟩ := c09_kernel_fubini p hp hp1 γ hγ R hR
  obtain ⟨-, -, hKi, hid⟩ := hfub G hG.1 j hj y
  refine ⟨hKi, ?_⟩
  obtain ⟨-, -, -, hd⟩ := hsm G hG R hR
  rw [(hd j y).2, ← hid, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun ξ hξ => ?_)
  rw [uIcc_of_le (by linarith)] at hξ
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  obtain ⟨-, -, -, -, h4⟩ := hTF G hG.1
  rw [((h4 hG).1 ξ hξ0).1]
  unfold c09_positive_kernel_amp
  rw [if_pos hξ0]
  have hr : ξ ^ ((j : ℝ) - 2) = ξ ^ j / ξ ^ 2 := by
    rw [Real.rpow_sub hξ0, Real.rpow_natCast, Real.rpow_two]
  rw [hr]
  have he : Complex.exp (Complex.I * (((y * ξ - Phi0 p ξ) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) * Complex.exp (-(Complex.I * (Phi0 p ξ : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [he]
  have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ0.ne'
  have hπ : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  push_cast
  field_simp
  ring

/-- Blueprint: lem:c09_truncation_L1_error.  Uniformly in `G, R, y`:
`|𝒯₊^R G(y) - 𝒯₊G(y)| ≤ C R⁻¹ ‖G‖_{Y_γ}` and `|𝒯_h^R G(y) - 𝒯_h G(y)| ≤ 2C R⁻¹ ‖G‖_{Y_γ}`. -/
theorem c09_truncation_L1_error (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma_tilde p γ, ∀ R : ℝ, 2 ≤ R → ∀ y : ℝ,
      ‖c09_truncation p R G y - c09_T_plus p G y‖ ≤ C * R⁻¹ * yNorm p γ G ∧
      |c09_truncation_high p R G y - T_high p G y| ≤ 2 * C * R⁻¹ * yNorm p γ G := by
  have hp0 : 0 < p := by linarith
  obtain ⟨CT, hCT, hTF⟩ := c09_tail_formula p hp hp1 γ hγ
  refine ⟨CT, hCT, fun G hG R hR y => ?_⟩
  obtain ⟨-, -, -, -, h4⟩ := hTF G hG.1
  obtain ⟨-, hbd, hint⟩ := h4 hG
  obtain ⟨-, -, -, -, -, hre⟩ := (c09_conjugate_symmetry p hp hp1 γ hγ G hG.1).2.2.2 hG
  have hyN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
  have hR0 : 0 < R := by linarith
  set e : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) with he
  have hec : Continuous e := by rw [he]; fun_prop
  have hen : ∀ ξ, ‖e ξ‖ = 1 := fun ξ => c09_aux_norm_exp_pos y ξ
  have hi1 : Integrable (fun ξ => c09_T_plus_hat p G ξ * e ξ) :=
    hint.mul_bdd hec.aestronglyMeasurable (Eventually.of_forall fun ξ => (hen ξ).le)
  have hθc : Continuous fun ξ => (c09_truncation_theta R ξ : ℂ) :=
    Complex.continuous_ofReal.comp (c09_aux_theta_continuous R)
  have hi2 : Integrable (fun ξ => (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ * e ξ) := by
    have := hi1.bdd_mul (c := 1) hθc.aestronglyMeasurable (Eventually.of_forall fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (c09_aux_theta_bounds R ξ).1]
      exact (c09_aux_theta_bounds R ξ).2)
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only; ring
  set g : ℝ → ℝ := fun ξ => CT * yNorm p γ G * (Set.indicator (Ioi R) (fun ξ => ξ ^ (-2 : ℝ)) ξ)
    with hg
  have hgi : Integrable g (volume.restrict (Ioi 0)) := by
    have : Integrable (Set.indicator (Ioi R) (fun ξ : ℝ => ξ ^ (-2 : ℝ))) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hR0).integrable_indicator measurableSet_Ioi
    exact (this.const_mul (CT * yNorm p γ G)).restrict
  have hgint : ∫ ξ in Ioi (0 : ℝ), g ξ = CT * yNorm p γ G * R⁻¹ := by
    rw [hg, integral_const_mul, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
      max_eq_right hR0.le, integral_Ioi_rpow_of_lt (by norm_num) hR0]
    norm_num [Real.rpow_neg_one]
  have hpt : ∀ ξ, ‖(c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ * e ξ -
      c09_T_plus_hat p G ξ * e ξ‖ ≤ g ξ := by
    intro ξ
    have e1 : (c09_truncation_theta R ξ : ℂ) * c09_T_plus_hat p G ξ * e ξ -
        c09_T_plus_hat p G ξ * e ξ =
        ((c09_truncation_theta R ξ - 1 : ℝ) : ℂ) * c09_T_plus_hat p G ξ * e ξ := by
      push_cast; ring
    rw [e1, norm_mul, norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hg0 : 0 ≤ g ξ := mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans hR0 hx)) _) ξ)
    rcases le_or_gt ξ R with h | h
    · by_cases h0 : ξ ≤ 1
      · rw [c09_aux_That_zero p G ξ h0, norm_zero, mul_zero]; exact hg0
      · rw [c09_aux_theta_one R ξ hR0 (abs_le.mpr ⟨by linarith, h⟩)]
        simp only [sub_self, abs_zero, zero_mul]; exact hg0
    · have hb := hbd ξ
      have h1 : Set.indicator (Ioi 1) (fun ξ : ℝ => ξ ^ (-2 : ℝ)) ξ = ξ ^ (-2 : ℝ) :=
        Set.indicator_of_mem (show ξ ∈ Ioi (1 : ℝ) by simp only [mem_Ioi]; linarith) _
      have h2 : Set.indicator (Ioi R) (fun ξ : ℝ => ξ ^ (-2 : ℝ)) ξ = ξ ^ (-2 : ℝ) :=
        Set.indicator_of_mem (show ξ ∈ Ioi R from h) _
      rw [h1] at hb
      rw [hg]; simp only; rw [h2]
      have hθ := c09_aux_theta_bounds R ξ
      have : |c09_truncation_theta R ξ - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc |c09_truncation_theta R ξ - 1| * ‖c09_T_plus_hat p G ξ‖ ≤ 1 * ‖c09_T_plus_hat p G ξ‖ := by
            gcongr
        _ ≤ _ := by rw [one_mul]; exact hb
  have key : ‖c09_truncation p R G y - c09_T_plus p G y‖ ≤ CT * R⁻¹ * yNorm p γ G := by
    rw [c09_aux_T_plus_Ioi]
    unfold c09_truncation
    rw [← mul_sub, ← integral_sub hi2.restrict hi1.restrict, norm_mul]
    have hn := norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)
    rw [hgint] at hn
    have hπ : ‖((2 * π : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
    have h0 : 0 ≤ CT * yNorm p γ G * R⁻¹ := by positivity
    calc _ ≤ 1 * (CT * yNorm p γ G * R⁻¹) := by gcongr
      _ = _ := by ring
  refine ⟨key, ?_⟩
  unfold c09_truncation_high
  rw [hre y, ← mul_sub, ← Complex.sub_re, abs_mul, abs_two]
  have := (Complex.abs_re_le_norm _).trans key
  linarith

/-- Blueprint: lem:c09_kernel_representation.  `𝒯₊^R G` is smooth, `|K_{+,j}^R| ≤ C_R w_E(z)`,
`∂_y^j 𝒯₊^R G(y) = ∫ K_{+,j}^R(y,z) G'(z) dz`, and `𝒯₊^R G → 𝒯₊G`, `𝒯_h^R G → 𝒯_h G`
uniformly as `R → ∞`. -/
theorem c09_kernel_representation (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    (∀ R : ℝ, 2 ≤ R → ∃ C_R, 0 < C_R ∧
      (∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ,
        ‖c09_positive_kernel p R j y z‖ ≤ C_R * c09_weights_E p z) ∧
      ∀ G ∈ Y_gamma_tilde p γ,
        ContDiff ℝ (⊤ : ℕ∞) (c09_truncation p R G) ∧
        ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
          Integrable (fun z => c09_positive_kernel p R j y z * ((deriv G z : ℝ) : ℂ)) ∧
          iteratedDeriv j (c09_truncation p R G) y =
            ∫ z, c09_positive_kernel p R j y z * ((deriv G z : ℝ) : ℂ)) ∧
    (∀ G ∈ Y_gamma_tilde p γ,
      TendstoUniformly (fun R => c09_truncation p R G) (c09_T_plus p G) atTop ∧
      TendstoUniformly (fun R => c09_truncation_high p R G) (T_high p G) atTop) := by
  obtain ⟨hsm, -⟩ := c09_truncated_smooth p hp hp1 γ hγ
  obtain ⟨CL, hCL, hL⟩ := c09_truncation_L1_error p hp hp1 γ hγ
  refine ⟨fun R hR => ?_, fun G hG => ?_⟩
  · obtain ⟨C, hC, hmaj⟩ := c09_kernel_majorant p hp hp1 R hR
    exact ⟨C, hC, fun j hj y z => ((hmaj j hj).1 y z).2.2, fun G hG =>
      ⟨(hsm G hG R hR).2.2.1, fun j hj y =>
        c09_truncated_representation p hp hp1 γ hγ G hG R hR j hj y⟩⟩
  · have hyN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
    have ht : Tendsto (fun R : ℝ => 2 * CL * yNorm p γ G * R⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (2 * CL * yNorm p γ G)
    have hev : ∀ ε > 0, ∀ᶠ R : ℝ in atTop, 2 ≤ R ∧ 2 * CL * yNorm p γ G * R⁻¹ < ε :=
      fun ε hε => (eventually_ge_atTop 2).and (ht.eventually (gt_mem_nhds hε))
    constructor
    · rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [hev ε hε] with R ⟨hR, hlt⟩ y
      rw [dist_comm, dist_eq_norm]
      have h1 := (hL G hG R hR y).1
      have : 0 ≤ CL * R⁻¹ * yNorm p γ G := by
        have : 0 < R := by linarith
        positivity
      nlinarith
    · rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [hev ε hε] with R ⟨hR, hlt⟩ y
      rw [dist_comm, Real.dist_eq]
      have h1 := (hL G hG R hR y).2
      nlinarith

/-! ### Stationary part -/

/-- Blueprint: lem:c09_tail_expansion.  Asymptotic expansion of `E_z(ξ)` in the nonstationary
regime `ξ₀^p - z ≥ c₁(ξ₀^p + |z|)`, with symbol bounds for `D^k g₀`. -/
theorem c09_tail_expansion (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1) :
    (∀ k ℓ : ℕ, ∃ C, 0 < C ∧ ∀ z ξ₀ : ℝ, 0 < ξ₀ → c₁ * (ξ₀ ^ p + |z|) ≤ ξ₀ ^ p - z →
      ∀ η : ℝ, ξ₀ ≤ η → ‖iteratedDeriv ℓ (c09_tail_expansion_D p z k) η‖ ≤
        C * η ^ (-(k : ℝ) - ℓ) * (η ^ p + |z|) ^ (-(k : ℝ) - 1)) ∧
    (∀ z ξ₀ : ℝ, 0 < ξ₀ → c₁ * (ξ₀ ^ p + |z|) ≤ ξ₀ ^ p - z →
      (∀ η : ℝ, ξ₀ ≤ η → c₁ * (η ^ p + |z|) ≤ η ^ p - z) ∧
      ∀ ξ : ℝ, ξ₀ ≤ ξ → ∀ M : ℕ,
        IntegrableOn (fun η => Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
          deriv (c09_tail_expansion_D p z M) η) (Ioi ξ) ∧
        c09_tail_integral p z ξ =
          Complex.exp (Complex.I * (c09_tail_integral_phase p z ξ : ℂ)) *
            (∑ k ∈ Finset.range (M + 1), (-1 : ℂ) ^ (k + 1) * c09_tail_expansion_D p z k ξ) +
          (-1 : ℂ) ^ (M + 1) * ∫ η in Ioi ξ,
            Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
              deriv (c09_tail_expansion_D p z M) η) := by
  have hp0 : 0 < p := by linarith
  have hgoodOf : ∀ z η : ℝ, c₁ * (η ^ p + |z|) ≤ η ^ p - z → c₁ * (|z| + η ^ p) ≤ |z - η ^ p| := by
    intro z η h
    rw [abs_sub_comm]; refine le_trans ?_ (le_abs_self _); linarith
  refine ⟨?_, fun z ξ₀ hξ₀ hc => ⟨c09_aux_tail_prop p hp0 c₁ hc₁' z ξ₀ hξ₀ hc, ?_⟩⟩
  · intro k ℓ
    obtain ⟨C, hC, hb⟩ := c09_aux_D_bounds p hp0 c₁ hc₁ k ℓ
    refine ⟨C, hC, fun z ξ₀ hξ₀ hc η hη => ?_⟩
    have hη0 : 0 < η := lt_of_lt_of_le hξ₀ hη
    refine (hb z η hη0 (hgoodOf z η (c09_aux_tail_prop p hp0 c₁ hc₁' z ξ₀ hξ₀ hc η hη)) ℓ
      le_rfl).trans (le_of_eq ?_)
    have hW : 0 < η ^ p + |z| := by have := Real.rpow_pos_of_pos hη0 p; positivity
    rw [show -(k : ℝ) - 1 = -((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hW.le,
      Real.rpow_natCast, add_comm (η ^ p)]
    ring
  intro ξ hξ
  have hξ0 : 0 < ξ := lt_of_lt_of_le hξ₀ hξ
  have hU := c09_aux_U_open p hp0 z
  set e := fun x => Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ)) with he
  set D := c09_tail_expansion_D p z with hDdef
  have hcond : ∀ η, ξ ≤ η → c₁ * (η ^ p + |z|) ≤ η ^ p - z := fun η hη =>
    c09_aux_tail_prop p hp0 c₁ hc₁' z ξ₀ hξ₀ hc η (hξ.trans hη)
  have hψpos : ∀ η, ξ ≤ η → 0 < η ^ p - z := by
    intro η hη
    have := hcond η hη
    have : 0 < η ^ p := Real.rpow_pos_of_pos (lt_of_lt_of_le hξ0 hη) p
    nlinarith [abs_nonneg z]
  have hmemU : ∀ η, ξ ≤ η → η ∈ Ioi (0 : ℝ) ∩ {x : ℝ | z - x ^ p ≠ 0} := fun η hη =>
    ⟨lt_of_lt_of_le hξ0 hη, by have := hψpos η hη; simp only [mem_ofPred_eq]; linarith⟩
  have hsubU : Ici ξ ⊆ Ioi (0 : ℝ) ∩ {x : ℝ | z - x ^ p ≠ 0} := fun η hη => hmemU η hη
  have hDd : ∀ k η, ξ ≤ η → HasDerivAt (D k) (deriv (D k) η) η := fun k η hη =>
    (((c09_aux_D_smooth p hp0 z k) η (hmemU η hη)).differentiableWithinAt (by simp)
      |>.differentiableAt (hU.mem_nhds (hmemU η hη))).hasDerivAt
  have hDc : ∀ k, ContinuousOn (deriv (D k)) (Ici ξ) := fun k =>
    ((c09_aux_D_smooth p hp0 z k).continuousOn_deriv_of_isOpen hU (by simp)).mono hsubU
  have hint : ∀ k, IntegrableOn (fun η => e η * deriv (D k) η) (Ioi ξ) := by
    intro k
    obtain ⟨C, hC, hb⟩ := c09_aux_D_bounds p hp0 c₁ hc₁ k 1
    set K := C * ((ξ₀ ^ p) ^ k)⁻¹ * ξ₀ ^ (-(k : ℝ))
    have hg : IntegrableOn (fun η : ℝ => K * η ^ (-1 - p)) (Ioi ξ) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hξ0).const_mul K
    refine hg.mono' ?_ ?_
    · exact (((continuous_const.mul (Complex.continuous_ofReal.comp
        (c09_aux_phase_cont p hp0 z))).cexp.continuousOn.mul
        (hDc k)).mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun η hη => ?_
      have hη' : ξ ≤ η := le_of_lt hη
      have hη0 : 0 < η := lt_of_lt_of_le hξ0 hη'
      rw [norm_mul, he]; simp only; rw [c09_aux_norm_exp_phase, one_mul, ← iteratedDeriv_one]
      refine (hb z η hη0 (hgoodOf z η (hcond η hη')) 1 le_rfl).trans ?_
      refine (c09_aux_tail_dom p hp0 z ξ₀ hξ₀ k 1 C hC.le η (hξ.trans hη')).trans (le_of_eq ?_)
      rw [← Real.rpow_neg hη0.le, ← Real.rpow_add hη0]; congr 2; push_cast; ring
  have hlim : ∀ k, Tendsto (D k) atTop (𝓝 0) := by
    intro k
    obtain ⟨C, hC, hb⟩ := c09_aux_D_bounds p hp0 c₁ hc₁ k 0
    set K := C * ((ξ₀ ^ p) ^ k)⁻¹ * ξ₀ ^ (-(k : ℝ))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun η : ℝ => K * ((η ^ p)⁻¹ * η ^ (-((0 : ℕ) : ℝ)))) atTop (𝓝 0) := by
      have : Tendsto (fun η : ℝ => (η ^ p)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hp0)
      simpa using this.const_mul K
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [eventually_ge_atTop ξ] with η hη
    have hη0 : 0 < η := lt_of_lt_of_le hξ0 hη
    have := hb z η hη0 (hgoodOf z η (hcond η hη)) 0 le_rfl
    rw [iteratedDeriv_zero] at this
    exact this.trans (c09_aux_tail_dom p hp0 z ξ₀ hξ₀ k 0 C hC.le η (hξ.trans hη))
  have hψne : ∀ η, ξ ≤ η → Complex.I * ((η ^ p - z : ℝ) : ℂ) ≠ 0 := fun η hη =>
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (hψpos η hη).ne')
  have hD0 : ∀ η, ξ ≤ η → D 0 η * (Complex.I * ((η ^ p - z : ℝ) : ℂ)) = (fun _ => (1 : ℂ)) η :=
    fun η hη => by
      rw [hDdef]; simp only [c09_tail_expansion_D]; exact one_div_mul_cancel (hψne η hη)
  have hDs : ∀ k η, ξ ≤ η → D (k + 1) η * (Complex.I * ((η ^ p - z : ℝ) : ℂ)) =
      deriv (D k) η := fun k η hη => by
    rw [hDdef]; simp only [c09_tail_expansion_D]; exact div_mul_cancel₀ _ (hψne η hη)
  set L := fun k => ∫ η in Ioi ξ, e η * deriv (D k) η with hL
  have hbase := c09_aux_tail_ibp p hp0 z ξ hξ0 (fun _ => 1) (D 0) hD0 (hDd 0) (hDc 0) (hlim 0)
    (hint 0)
  simp only [mul_one] at hbase
  have hE : c09_tail_integral p z ξ = -(e ξ * D 0 ξ) - L 0 := hbase.limUnder_eq
  have hstep : ∀ k, L k = -(e ξ * D (k + 1) ξ) - L (k + 1) := by
    intro k
    have h1 := c09_aux_tail_ibp p hp0 z ξ hξ0 (deriv (D k)) (D (k + 1)) (hDs k) (hDd (k + 1))
      (hDc (k + 1)) (hlim (k + 1)) (hint (k + 1))
    have h2 := intervalIntegral_tendsto_integral_Ioi ξ (hint k) tendsto_id
    exact tendsto_nhds_unique h2 h1
  have hform : ∀ M : ℕ, c09_tail_integral p z ξ =
      e ξ * (∑ k ∈ Finset.range (M + 1), (-1 : ℂ) ^ (k + 1) * D k ξ) + (-1 : ℂ) ^ (M + 1) * L M := by
    intro M
    induction M with
    | zero => rw [hE]; simp only [zero_add, Finset.sum_range_one, pow_one]; ring
    | succ M ih =>
      rw [ih, hstep M, Finset.sum_range_succ _ (M + 1)]
      ring
  exact fun M => ⟨hint M, hform M⟩

/-- Blueprint: lem:linear_nonstationary_symbol_expansion.  The symbols
`m_{j,0}^R = a_j^{ns,R}/(i(y-ξ^p))`, `m_{j,k+1}^R = -∂_ξ m_{j,k}^R/(i(y-ξ^p))`
(at the zero `ξ = y^{1/p}`, where `a_j^{ns,R}(y,·)` vanishes nearby, Lean's `x/0 = 0` gives `0`). -/
def linear_nonstationary_symbol_expansion_m (p R : ℝ) (j : ℕ) (y : ℝ) : ℕ → ℝ → ℂ
  | 0 => fun ξ => c09_stationary_split_amp_ns p R j y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))
  | k + 1 => fun ξ => -deriv (linear_nonstationary_symbol_expansion_m p R j y k) ξ /
      (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))

/-- Blueprint: lem:linear_nonstationary_symbol_expansion.  The remainder kernel
`K_{ℛ_{j,M}}^R(y,z) = -∫₁^{2R} ∂_ξ m_{j,M-1}^R(y,ξ) e^{iΘ_y(ξ)} E_z(ξ) dξ`, `Θ_y(ξ) = yξ - Φ₀(ξ)`. -/
def linear_nonstationary_symbol_expansion_remKernel (p R : ℝ) (j M : ℕ) (y z : ℝ) : ℂ :=
  -∫ ξ in (1 : ℝ)..(2 * R), deriv (linear_nonstationary_symbol_expansion_m p R j y (M - 1)) ξ *
    Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ

/-- Blueprint: lem:linear_nonstationary_symbol_expansion.
`ℛ_{j,M}^R G(y) = ∫ K_{ℛ_{j,M}}^R(y,z) G'(z) dz`. -/
def linear_nonstationary_symbol_expansion_remOp (p R : ℝ) (j M : ℕ) (G : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ z, linear_nonstationary_symbol_expansion_remKernel p R j M y z * ((deriv G z : ℝ) : ℂ)

/-! #### Helpers: the nonstationary symbols `m_{j,k}` -/

/-- The amplitude `a_j^{ns,R}(y,·)`. -/
abbrev c09_aux_ans (p R : ℝ) (j : ℕ) (y : ℝ) : ℝ → ℂ := fun ξ =>
  c09_stationary_split_amp_ns p R j y ξ

/-- Support of `a_j^{ns,R}(y,·)`: `ξ ≥ 1` and nonstationary. -/
theorem c09_aux_ans_tsupport (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 0 < R) (j : ℕ) (y ξ : ℝ)
    (hξ : ξ ∈ tsupport (c09_aux_ans p R j y)) :
    1 ≤ ξ ∧ (1 - (100 / 101 : ℝ) ^ p) / 2 * (|y| + ξ ^ p) ≤ |y - ξ ^ p| := by
  have h1 : tsupport (c09_aux_ans p R j y) ⊆ tsupport (c09_positive_kernel_amp R j) :=
    tsupport_mul_subset_right
  have h2 : tsupport (c09_aux_ans p R j y) ⊆
      tsupport (fun ξ => ((c09_stationary_split_chi_ns p y ξ : ℝ) : ℂ)) :=
    tsupport_mul_subset_left
  have h3 : tsupport (fun ξ => ((c09_stationary_split_chi_ns p y ξ : ℝ) : ℂ)) ⊆
      tsupport (c09_stationary_split_chi_ns p y) :=
    tsupport_comp_subset Complex.ofReal_zero _
  have h4 : tsupport (c09_positive_kernel_amp R j) ⊆ Icc 1 (2 * R) :=
    closure_minimal (fun x hx => c09_aux_cut_A5 j R hR x hx) isClosed_Icc
  have hξ1 := (h4 (h1 hξ)).1
  exact ⟨hξ1, c09_aux_good p hp y ξ (by linarith) (h3 (h2 hξ))⟩

/-- Product form of `m_{j,0}`. -/
theorem c09_aux_m0_eq (p R : ℝ) (j : ℕ) (y : ℝ) :
    linear_nonstationary_symbol_expansion_m p R j y 0 = fun x =>
      (-Complex.I * c09_stationary_split_amp_ns p R j y x) * (((y - x ^ p)⁻¹ : ℝ) : ℂ) := by
  funext x
  simp only [linear_nonstationary_symbol_expansion_m, div_eq_mul_inv, mul_inv, Complex.inv_I,
    Complex.ofReal_inv]
  ring

/-- Product form of `m_{j,k+1}`. -/
theorem c09_aux_msucc_eq (p R : ℝ) (j : ℕ) (y : ℝ) (k : ℕ) :
    linear_nonstationary_symbol_expansion_m p R j y (k + 1) = fun x =>
      (Complex.I * deriv (linear_nonstationary_symbol_expansion_m p R j y k) x) *
        (((y - x ^ p)⁻¹ : ℝ) : ℂ) := by
  funext x
  simp only [linear_nonstationary_symbol_expansion_m, div_eq_mul_inv, mul_inv, Complex.inv_I,
    Complex.ofReal_inv]
  ring

/-- `m_{j,k}` vanishes near points off `tsupport a_j^{ns,R}`. -/
theorem c09_aux_m_vanish (p R : ℝ) (j : ℕ) (y : ℝ) (k : ℕ) (ξ : ℝ)
    (hξ : ξ ∉ tsupport (c09_aux_ans p R j y)) :
    linear_nonstationary_symbol_expansion_m p R j y k =ᶠ[𝓝 ξ] fun _ => 0 := by
  have hopen : IsOpen (tsupport (c09_aux_ans p R j y))ᶜ := (isClosed_tsupport _).isOpen_compl
  induction k generalizing ξ with
  | zero =>
    filter_upwards [hopen.mem_nhds hξ] with x hx
    have : c09_stationary_split_amp_ns p R j y x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [c09_aux_m0_eq]; simp only; rw [this]; simp
  | succ k ih =>
    filter_upwards [hopen.mem_nhds hξ] with x hx
    rw [c09_aux_msucc_eq]
    simp only
    rw [(ih x hx).deriv_eq]; simp

/-- `m_{j,k}` is smooth on `(0,∞)`. -/
theorem c09_aux_m_smooth (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (y : ℝ) (k : ℕ) :
    ContDiffOn ℝ ∞ (linear_nonstationary_symbol_expansion_m p R j y k) (Ioi 0) := by
  have hR0 : 0 < R := by linarith
  have hans : ContDiffOn ℝ ∞ (c09_aux_ans p R j y) (Ioi 0) := by
    have hamp : ContDiffOn ℝ (⊤ : ℕ∞) (c09_positive_kernel_amp R j) (Ioi 0) := by
      have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (-(Complex.I ^ (j + 1)) / ((2 * π : ℝ) : ℂ)) *
          (((rho x - 1) * rho (x / R) * x ^ ((j : ℝ) - 2) : ℝ) : ℂ)) :=
        contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (c09_aux_cut_A2 j R))
      refine hsm.contDiffOn.congr fun x hx => ?_
      unfold c09_positive_kernel_amp c09_truncation_theta
      simp only [show 0 < x from hx, ↓reduceIte]
    exact (Complex.ofRealCLM.contDiff.comp (c09_aux_chi_ns_smooth p y)).contDiffOn.mul hamp
  induction k with
  | zero =>
    intro ξ hξ
    by_cases hs : ξ ∈ tsupport (c09_aux_ans p R j y)
    · obtain ⟨h1, hg⟩ := c09_aux_ans_tsupport p hp R hR0 j y ξ hs
      have hne : y - ξ ^ p ≠ 0 := by
        intro h; rw [h, abs_zero] at hg
        have := c09_aux_cs_pos p hp; have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < ξ) p
        nlinarith [abs_nonneg y]
      rw [c09_aux_m0_eq]
      exact ((contDiffAt_const.mul ((hans ξ hξ).contDiffAt (isOpen_Ioi.mem_nhds hξ))).mul
        (c09_aux_psiC_smooth p y ξ hξ hne)).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (c09_aux_m_vanish p R j y 0 ξ hs)).contDiffWithinAt
  | succ k ih =>
    intro ξ hξ
    by_cases hs : ξ ∈ tsupport (c09_aux_ans p R j y)
    · obtain ⟨h1, hg⟩ := c09_aux_ans_tsupport p hp R hR0 j y ξ hs
      have hne : y - ξ ^ p ≠ 0 := by
        intro h; rw [h, abs_zero] at hg
        have := c09_aux_cs_pos p hp; have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < ξ) p
        nlinarith [abs_nonneg y]
      have hd := ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp ih).2
      rw [c09_aux_msucc_eq]
      exact ((contDiffAt_const.mul ((hd ξ hξ).contDiffAt (isOpen_Ioi.mem_nhds hξ))).mul
        (c09_aux_psiC_smooth p y ξ hξ hne)).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (c09_aux_m_vanish p R j y (k + 1) ξ hs)).contDiffWithinAt

/-- Symbol bounds for `a_j^{ns,R}`. -/
theorem c09_aux_ans_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (j : ℕ) (hj : j ≤ 2) (N : ℕ) :
    ∃ A, 0 < A ∧ ∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ → ∀ ℓ ≤ N,
      ‖iteratedDeriv ℓ (c09_aux_ans p R j y) ξ‖ ≤ A * ξ ^ (((j : ℝ) - 2) - ℓ) := by
  obtain ⟨Kχ, hKχ, hχb⟩ := c09_aux_chi_bounds p hp hp1 N
  obtain ⟨-, -, -, C, hCpos, -, -, -, -, -, h3, -⟩ := c09_cutoff_bounds p hp hp1
  have hS : (0:ℝ) ≤ ∑ i ∈ Finset.range (N + 1), C i := Finset.sum_nonneg fun i _ => (hCpos i).le
  refine ⟨2 ^ N * Kχ * (∑ i ∈ Finset.range (N + 1), C i + 1), by positivity,
    fun R hR y ξ hξ ℓ hℓ => ?_⟩
  obtain ⟨hsm, -, -, hb⟩ := h3 R hR j hj
  have key := c09_aux_leib (fun x => ((c09_stationary_split_chi_ns p y x : ℝ) : ℂ))
    (c09_positive_kernel_amp R j) ξ hξ ℓ
    ((Complex.ofRealCLM.contDiff.comp (c09_aux_chi_ns_smooth p y)).contDiffAt.of_le
      (by exact_mod_cast le_top))
    ((hsm ξ hξ).contDiffAt (isOpen_Ioi.mem_nhds hξ) |>.of_le (by exact_mod_cast le_top))
    Kχ (∑ i ∈ Finset.range (N + 1), C i + 1) 0 ((j : ℝ) - 2)
    (fun i hi => by
      rw [congrFun (c09_aux_cut_L2 _ (c09_aux_chi_ns_smooth p y) i) ξ, Complex.norm_real]
      exact hχb y ξ hξ i (by omega))
    (fun i hi => by
      refine (hb i ξ hξ).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hξ _).le)
      have : C i ≤ ∑ i ∈ Finset.range (N + 1), C i :=
        Finset.single_le_sum (f := C) (fun i _ => (hCpos i).le) (Finset.mem_range.mpr (by omega))
      linarith)
  refine key.trans ?_
  rw [zero_add]
  have : (2 : ℝ) ^ ℓ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hℓ
  have : 0 < ξ ^ (((j : ℝ) - 2) - ℓ) := Real.rpow_pos_of_pos hξ _
  gcongr

/-! #### Helpers for the stationary near estimate -/

/-- `a_j^R` is smooth on `ℝ`. -/
theorem c09_aux_amp_contDiff (R : ℝ) (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (c09_positive_kernel_amp R j) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · exact (c09_aux_amp_smooth R j).contDiffAt (isOpen_Ioi.mem_nhds hx)
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds (show x ∈ Iio (1 : ℝ) by simp only [mem_Iio]; linarith)]
      with ξ hξ
    exact c09_aux_amp_zero_of_le_one R j ξ (le_of_lt hξ)

/-- `Θ_y(t) = yt - Φ₀(t)` has derivative `y - t^p` at `t > 0`. -/
theorem c09_aux_Theta_deriv (p : ℝ) (hp : 0 < p) (y t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x => y * x - Phi0 p x) (y - t ^ p) t := by
  have h := (c09_aux_phase_deriv p hp y t ht).neg
  convert h using 1
  · funext x; simp only [Pi.neg_apply, c09_tail_integral_phase]; ring
  · ring

/-- Second and third derivatives of `Θ_y` at `t > 0`. -/
theorem c09_aux_Theta_iter (p : ℝ) (hp : 0 < p) (y t : ℝ) (ht : 0 < t) :
    iteratedDeriv 2 (fun x => y * x - Phi0 p x) t = -(p * t ^ (p - 1)) ∧
    iteratedDeriv 3 (fun x => y * x - Phi0 p x) t = -(p * ((p - 1) * t ^ (p - 1 - 1))) := by
  set Θ : ℝ → ℝ := fun x => y * x - Phi0 p x with hΘ
  have h1 : deriv Θ =ᶠ[𝓝 t] fun x => y - x ^ p := by
    filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Ioi (0 : ℝ) from ht)] with x hx
    exact (c09_aux_Theta_deriv p hp y x hx).deriv
  have hd1 : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => y - x ^ p) (-(p * x ^ (p - 1))) x :=
    fun x hx => by simpa using (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).const_sub y
  have h2 : deriv (deriv Θ) =ᶠ[𝓝 t] fun x => -(p * x ^ (p - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Ioi (0 : ℝ) from ht)] with x hx
    have h1x : deriv Θ =ᶠ[𝓝 x] fun x => y - x ^ p := by
      filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Ioi (0 : ℝ) from hx)] with u hu
      exact (c09_aux_Theta_deriv p hp y u hu).deriv
    rw [h1x.deriv_eq]; exact (hd1 x hx).deriv
  have hd2 : HasDerivAt (fun x : ℝ => -(p * x ^ (p - 1))) (-(p * ((p - 1) * t ^ (p - 1 - 1)))) t :=
    ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht.ne')).const_mul p).neg
  refine ⟨?_, ?_⟩
  · rw [iteratedDeriv_succ, iteratedDeriv_one, h1.deriv_eq]; exact (hd1 t ht).deriv
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one, h2.deriv_eq]; exact hd2.deriv

/-- `Θ_y` is smooth on `(0,∞)`. -/
theorem c09_aux_Theta_smooth (p : ℝ) (hp : 0 < p) (y : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => y * x - Phi0 p x) (Ioi 0) := by
  have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => y * x - x ^ (p + 1) / (p + 1)) (Ioi 0) := by
    intro x hx
    have : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ (p + 1)) x :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)
    exact ((contDiffAt_const.mul contDiffAt_id).sub (this.div_const _)).contDiffWithinAt
  refine h.congr fun x hx => ?_
  have hx' : 0 < x := hx
  simp only [Phi0, abs_of_pos hx', Real.rpow_add_one hx'.ne']
  ring

/-- `(n : WithTop ℕ∞) ≤ ∞`. -/
theorem c09_aux_le_inf (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- The phase hypotheses of the triangle lemma for `Φ(t) = yt - Φ₀(t)` near `x₀ = y^{1/p}`. -/
theorem c09_aux_sn_phi (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (y x₀ : ℝ) (hx₀0 : 0 < x₀)
    (hx₀p : x₀ ^ p = y) :
    ContDiffOn ℝ 3 (fun t => y * t - Phi0 p t) (Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25)) ∧
    derivWithin (fun t => y * t - Phi0 p t) (Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25)) x₀ = 0 ∧
    ∀ t ∈ Ioo (x₀ - x₀ / 25) (x₀ + x₀ / 25),
      p * (26 / 25 : ℝ) ^ (p - 1) * x₀ ^ (p - 1) ≤
        |iteratedDerivWithin 2 (fun t => y * t - Phi0 p t) (Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25)) t| ∧
      |iteratedDerivWithin 2 (fun t => y * t - Phi0 p t) (Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25)) t| ≤
        p * (24 / 25 : ℝ) ^ (p - 1) * x₀ ^ (p - 1) ∧
      |iteratedDerivWithin 3 (fun t => y * t - Phi0 p t) (Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25)) t| ≤
        p * (1 - p) * (24 / 25 : ℝ) ^ (p - 2) / 25 * x₀ ^ (p - 1) / (x₀ / 25) := by
  have hp0 : 0 < p := by linarith
  set Φ : ℝ → ℝ := fun t => y * t - Phi0 p t with hΦ
  have hIcc : Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25) ⊆ Ioi 0 := by
    intro t ht; simp only [mem_Ioi]; linarith [ht.1]
  have hΦs := c09_aux_Theta_smooth p hp0 y
  have hUD : UniqueDiffOn ℝ (Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25)) := uniqueDiffOn_Icc (by linarith)
  have hiter : ∀ n : ℕ, ∀ t ∈ Ioo (x₀ - x₀ / 25) (x₀ + x₀ / 25),
      iteratedDerivWithin n Φ (Icc (x₀ - x₀ / 25) (x₀ + x₀ / 25)) t = iteratedDeriv n Φ t := by
    intro n t ht
    have ht0 : 0 < t := hIcc (Ioo_subset_Icc_self ht)
    exact iteratedDerivWithin_eq_iteratedDeriv hUD
      ((hΦs.contDiffAt (isOpen_Ioi.mem_nhds ht0)).of_le (by simpa using c09_aux_le_inf n))
      (Ioo_subset_Icc_self ht)
  refine ⟨(hΦs.mono hIcc).of_le (by simpa using c09_aux_le_inf 3), ?_, fun t ht => ?_⟩
  · rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)),
      (c09_aux_Theta_deriv p hp0 y x₀ hx₀0).deriv, hx₀p, sub_self]
  have hl : 24 / 25 * x₀ < t := by linarith [ht.1]
  have hr : t < 26 / 25 * x₀ := by linarith [ht.2]
  have ht0 : 0 < t := by linarith
  obtain ⟨e2, e3⟩ := c09_aux_Theta_iter p hp0 y t ht0
  rw [hiter 2 t ht, hiter 3 t ht, e2, e3]
  have htp : 0 < t ^ (p - 1) := Real.rpow_pos_of_pos ht0 _
  have htp2 : 0 < t ^ (p - 1 - 1) := Real.rpow_pos_of_pos ht0 _
  have lo : (26 / 25 * x₀) ^ (p - 1) ≤ t ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos ht0 hr.le (by linarith)
  have hi : t ^ (p - 1) ≤ (24 / 25 * x₀) ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hl.le (by linarith)
  have hi2 : t ^ (p - 1 - 1) ≤ (24 / 25 * x₀) ^ (p - 1 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hl.le (by linarith)
  rw [Real.mul_rpow (by norm_num) hx₀0.le] at lo hi hi2
  rw [abs_neg, abs_of_pos (by positivity), abs_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_assoc]; gcongr
  · rw [mul_assoc]; gcongr
  · rw [abs_mul, abs_mul, abs_of_pos hp0, abs_of_pos htp2, abs_of_neg (show p - 1 < 0 by linarith)]
    have e : p * (1 - p) * (24 / 25 : ℝ) ^ (p - 2) / 25 * x₀ ^ (p - 1) / (x₀ / 25) =
        p * (1 - p) * ((24 / 25 : ℝ) ^ (p - 1 - 1) * x₀ ^ (p - 1 - 1)) := by
      rw [show p - 1 - 1 = p - 2 by ring, show p - 1 = (p - 2) + 1 by ring,
        Real.rpow_add_one hx₀0.ne']
      field_simp
    rw [e]
    have : 0 < 1 - p := by linarith
    calc p * (-(p - 1) * t ^ (p - 1 - 1)) = p * (1 - p) * t ^ (p - 1 - 1) := by ring
      _ ≤ _ := by gcongr

/-- Amplitude bounds for the stationary near estimate. -/
theorem c09_aux_sn_amp (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ c₄, 0 < c₄ ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ, 0 < y → ∀ j' ≤ 2,
      ∀ t ∈ Ioo (y ^ (1 / p) - y ^ (1 / p) / 25) (y ^ (1 / p) + y ^ (1 / p) / 25),
      ‖iteratedDeriv j' (c09_stationary_split_amp_s p R j y) t‖ ≤
        c₄ * (y ^ (1 / p)) ^ ((j : ℝ) - 2) * (y ^ (1 / p) / 25) ^ (-(j' : ℝ)) := by
  obtain ⟨cstar, -, -, Ccut, hCcut, -, -, -, -, -, h3, -, -, -, -⟩ := c09_cutoff_bounds p hp hp1
  obtain ⟨A0, hA0, hans0⟩ := c09_aux_ans_bounds p hp hp1 0 (by norm_num) 2
  obtain ⟨A1, hA1, hans1⟩ := c09_aux_ans_bounds p hp hp1 1 (by norm_num) 2
  obtain ⟨A2, hA2, hans2⟩ := c09_aux_ans_bounds p hp hp1 2 le_rfl 2
  have hC0 := hCcut 0; have hC1 := hCcut 1; have hC2 := hCcut 2
  refine ⟨(Ccut 0 + Ccut 1 + Ccut 2 + A0 + A1 + A2) * (25 / 24 : ℝ) ^ (4 : ℝ), by positivity,
    fun R hR j hj y hy j' hj' t ht => ?_⟩
  set x₀ : ℝ := y ^ (1 / p) with hx₀
  have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hy _
  have hl : 24 / 25 * x₀ < t := by linarith [ht.1]
  have ht0 : 0 < t := by linarith
  have hamp := c09_aux_amp_contDiff R j
  have hans_sm : ContDiff ℝ (⊤ : ℕ∞) (c09_aux_ans p R j y) := by
    show ContDiff ℝ (⊤ : ℕ∞) (c09_stationary_split_amp_ns p R j y)
    unfold c09_stationary_split_amp_ns
    exact (Complex.ofRealCLM.contDiff.comp (c09_aux_chi_ns_smooth p y)).mul hamp
  have hdiff : c09_stationary_split_amp_s p R j y = c09_positive_kernel_amp R j - c09_aux_ans p R j y := by
    funext t
    simp only [Pi.sub_apply, c09_stationary_split_amp_s]
    show _ = _ - c09_stationary_split_amp_ns p R j y t
    unfold c09_stationary_split_amp_ns c09_stationary_split_chi_ns
    push_cast; ring
  rw [hdiff, iteratedDeriv_sub (hamp.contDiffAt.of_le (by simpa using c09_aux_le_inf j'))
    (hans_sm.contDiffAt.of_le (by simpa using c09_aux_le_inf j'))]
  have b1 := (h3 R hR j hj).2.2.2 j' t ht0
  have hpos : 0 < t ^ (((j : ℝ) - 2) - j') := Real.rpow_pos_of_pos ht0 _
  have hAs : ‖iteratedDeriv j' (c09_aux_ans p R j y) t‖ ≤ (A0 + A1 + A2) * t ^ (((j : ℝ) - 2) - j') := by
    interval_cases j
    · exact (hans0 R hR y t ht0 j' hj').trans (by gcongr; linarith)
    · exact (hans1 R hR y t ht0 j' hj').trans (by gcongr; linarith)
    · exact (hans2 R hR y t ht0 j' hj').trans (by gcongr; linarith)
  have hCc : Ccut j' ≤ Ccut 0 + Ccut 1 + Ccut 2 := by
    interval_cases j' <;> linarith
  have hexp : ((j : ℝ) - 2) - j' ≤ 0 := by
    have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have : (0 : ℝ) ≤ j' := Nat.cast_nonneg _; linarith
  have hexp4 : -4 ≤ ((j : ℝ) - 2) - j' := by
    have : (j' : ℝ) ≤ 2 := by exact_mod_cast hj'
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith
  have hte : t ^ (((j : ℝ) - 2) - j') ≤
      (25 / 24 : ℝ) ^ (4 : ℝ) * (x₀ ^ ((j : ℝ) - 2) * (x₀ / 25) ^ (-(j' : ℝ))) := by
    have e1 : t ^ (((j : ℝ) - 2) - j') ≤ (24 / 25 * x₀) ^ (((j : ℝ) - 2) - j') :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hl.le hexp
    rw [Real.mul_rpow (by norm_num) hx₀0.le] at e1
    have e2 : (24 / 25 : ℝ) ^ (((j : ℝ) - 2) - j') ≤ (25 / 24 : ℝ) ^ (4 : ℝ) := by
      rw [show (25 / 24 : ℝ) = (24 / 25)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
        ← Real.rpow_neg (by norm_num)]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hexp4
    have e3 : x₀ ^ (((j : ℝ) - 2) - j') ≤ x₀ ^ ((j : ℝ) - 2) * (x₀ / 25) ^ (-(j' : ℝ)) := by
      rw [sub_eq_add_neg (((j : ℝ) - 2)), Real.rpow_add hx₀0, Real.div_rpow hx₀0.le (by norm_num)]
      have h25 : (25 : ℝ) ^ (-(j' : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by have : (0 : ℝ) ≤ j' := Nat.cast_nonneg _; linarith)
      have h25p : 0 < (25 : ℝ) ^ (-(j' : ℝ)) := by positivity
      have hxj : 0 < x₀ ^ (-(j' : ℝ)) := Real.rpow_pos_of_pos hx₀0 _
      have : x₀ ^ (-(j' : ℝ)) ≤ x₀ ^ (-(j' : ℝ)) / (25 : ℝ) ^ (-(j' : ℝ)) := by
        rw [le_div_iff₀ h25p]; nlinarith
      have := Real.rpow_pos_of_pos hx₀0 ((j : ℝ) - 2)
      gcongr
    calc _ ≤ (24 / 25 : ℝ) ^ (((j : ℝ) - 2) - j') * x₀ ^ (((j : ℝ) - 2) - j') := e1
      _ ≤ _ := by gcongr
  calc ‖iteratedDeriv j' (c09_positive_kernel_amp R j) t - iteratedDeriv j' (c09_aux_ans p R j y) t‖
      ≤ ‖iteratedDeriv j' (c09_positive_kernel_amp R j) t‖ +
        ‖iteratedDeriv j' (c09_aux_ans p R j y) t‖ := norm_sub_le _ _
    _ ≤ Ccut j' * t ^ ((j : ℝ) - 2 - j') + (A0 + A1 + A2) * t ^ (((j : ℝ) - 2) - j') :=
        add_le_add b1 hAs
    _ = (Ccut j' + (A0 + A1 + A2)) * t ^ (((j : ℝ) - 2) - j') := by ring
    _ ≤ (Ccut 0 + Ccut 1 + Ccut 2 + A0 + A1 + A2) * t ^ (((j : ℝ) - 2) - j') :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ ≤ (Ccut 0 + Ccut 1 + Ccut 2 + A0 + A1 + A2) *
        ((25 / 24 : ℝ) ^ (4 : ℝ) * (x₀ ^ ((j : ℝ) - 2) * (x₀ / 25) ^ (-(j' : ℝ)))) :=
        mul_le_mul_of_nonneg_left hte (by positivity)
    _ = _ := by ring

/-- Final arithmetic of the stationary near estimate. -/
theorem c09_aux_sn_arith (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (CT CE : ℝ) (hCT : 0 < CT)
    (hCE : 0 < CE) (j : ℕ) (hj : j ≤ 2) (y z : ℝ) (hyy : (50 / 51 : ℝ) ^ p ≤ y) (hz : y / 4 ≤ z) :
    CT * (y ^ (1 / p)) ^ ((j : ℝ) - 2) * (CE * jb z ^ ((1 - p) / (2 * p)) *
        ((y ^ (1 / p)) ^ (p - 1)) ^ (-(1 / 2 : ℝ)) + ((y ^ (1 / p)) ^ (p - 1))⁻¹) ≤
      (CT * (CE + 4 ^ ((1 - p) / (2 * p))) * (1 + 1 / (50 / 51 : ℝ) ^ p) ^ (4 : ℝ) + 1) *
        jb y ^ ((j : ℝ) / p - (p + 3) / (2 * p)) * jb z ^ ((1 - p) / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  set ys : ℝ := (50 / 51 : ℝ) ^ p with hys
  have hys0 : 0 < ys := by positivity
  have hy : 0 < y := by linarith
  have hzpos : 0 < z := by linarith
  have hjy := c09_aux_jb_pos y
  have hjz := c09_aux_jb_pos z
  set D : ℝ := 1 + 1 / ys with hD
  have hD1 : 1 ≤ D := by have : 0 < 1 / ys := by positivity
                         linarith
  set s : ℝ := (1 - p) / (2 * p) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
  set x₀ : ℝ := y ^ (1 / p) with hx₀
  have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hy _
  have hxpow : ∀ a : ℝ, x₀ ^ a = y ^ (a / p) := fun a => by
    rw [hx₀, ← Real.rpow_mul hy.le]; congr 1; field_simp
  have hκh : (x₀ ^ (p - 1)) ^ (-(1 / 2 : ℝ)) = y ^ (-((p - 1) / (2 * p))) := by
    rw [← Real.rpow_mul hx₀0.le, hxpow]; congr 1; field_simp
  have hκi : (x₀ ^ (p - 1))⁻¹ = y ^ (-((p - 1) / p)) := by
    rw [← Real.rpow_neg hx₀0.le, hxpow]; congr 1; ring
  have hAy : x₀ ^ ((j : ℝ) - 2) = y ^ (((j : ℝ) - 2) / p) := hxpow _
  set e : ℝ := (j : ℝ) / p - (p + 3) / (2 * p) with he
  have t1 : x₀ ^ ((j : ℝ) - 2) * (CE * jb z ^ s * (x₀ ^ (p - 1)) ^ (-(1 / 2 : ℝ))) =
      CE * (y ^ e * jb z ^ s) := by
    rw [hκh, hAy]
    have : y ^ (((j : ℝ) - 2) / p) * y ^ (-((p - 1) / (2 * p))) = y ^ e := by
      rw [← Real.rpow_add hy]; congr 1; rw [he]; field_simp; ring
    rw [← this]; ring
  have t2 : x₀ ^ ((j : ℝ) - 2) * (x₀ ^ (p - 1))⁻¹ = y ^ e * y ^ s := by
    rw [hκi, hAy, ← Real.rpow_add hy, ← Real.rpow_add hy]; congr 1; rw [he, hs]; field_simp; ring
  have hys4 : y ^ s ≤ 4 ^ s * jb z ^ s := by
    rw [← Real.mul_rpow (by norm_num) hjz.le]
    refine Real.rpow_le_rpow hy.le ?_ hs0
    have := c09_aux_abs_le_jb' z
    rw [abs_of_pos hzpos] at this; linarith
  have hye : y ^ e ≤ D ^ (4 : ℝ) * jb y ^ e := by
    have h1 : jb y ≤ 1 + y := by
      unfold jb; rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have h2 : 1 ≤ y / ys := by rw [le_div_iff₀ hys0]; linarith
    have hjyD : jb y ≤ D * y := by
      calc jb y ≤ 1 + y := h1
        _ ≤ y / ys + y := by linarith
        _ = D * y := by rw [hD]; ring
    rcases le_or_gt 0 e with he0 | he0
    · calc y ^ e ≤ jb y ^ e := Real.rpow_le_rpow hy.le (by
            have := c09_aux_abs_le_jb' y; rw [abs_of_pos hy] at this; exact this) he0
        _ ≤ D ^ (4 : ℝ) * jb y ^ e := by
            have h4 : 1 ≤ D ^ (4 : ℝ) := Real.one_le_rpow hD1 (by norm_num)
            have := Real.rpow_pos_of_pos hjy e
            nlinarith
    · have hjyD' : jb y / D ≤ y := by rw [div_le_iff₀ (by linarith)]; linarith
      calc y ^ e ≤ (jb y / D) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) hjyD' he0.le
        _ = D ^ (-e) * jb y ^ e := by
            rw [Real.div_rpow hjy.le (by linarith), Real.rpow_neg (by linarith)]; ring
        _ ≤ D ^ (4 : ℝ) * jb y ^ e := by
            have hneg : -e ≤ 4 := by
              rw [he]
              have : (p + 3) / (2 * p) ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
              have : 0 ≤ (j : ℝ) / p := by positivity
              linarith
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hD1 hneg)
              (Real.rpow_pos_of_pos hjy e).le
  have hyepos : 0 ≤ y ^ e := (Real.rpow_pos_of_pos hy e).le
  have hjzs : 0 ≤ jb z ^ s := (Real.rpow_pos_of_pos hjz s).le
  rw [mul_assoc CT, mul_add, t1, t2]
  calc CT * (CE * (y ^ e * jb z ^ s) + y ^ e * y ^ s)
      ≤ CT * (CE * (y ^ e * jb z ^ s) + y ^ e * (4 ^ s * jb z ^ s)) := by gcongr
    _ = CT * (CE + 4 ^ s) * (y ^ e * jb z ^ s) := by ring
    _ ≤ CT * (CE + 4 ^ s) * (D ^ (4 : ℝ) * jb y ^ e * jb z ^ s) := by gcongr
    _ ≤ (CT * (CE + 4 ^ s) * D ^ (4 : ℝ) + 1) * jb y ^ e * jb z ^ s := by
        have : 0 ≤ jb y ^ e * jb z ^ s := by positivity
        nlinarith

/-- Blueprint: lem:c09_stationary_near.  For `y > 0`, `z ≥ y/4`:
`|K_{+,j}^{s,R}(y,z)| ≤ C ⟨y⟩^{j/p-(p+3)/(2p)} ⟨z⟩^{(1-p)/(2p)}`. -/
theorem c09_stationary_near (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ, 0 < y → y / 4 ≤ z →
      ‖c09_stationary_split_kernel_s p R j y z‖ ≤
        C * jb y ^ ((j : ℝ) / p - (p + 3) / (2 * p)) * jb z ^ ((1 - p) / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨cstar, -, -, Ccut, hCcut, h1a, -, -, -, -, -, -, -, -, h5⟩ := c09_cutoff_bounds p hp hp1
  obtain ⟨-, -, -, -, ⟨CE, hCE, hE⟩, -⟩ := c09_tail_basic p hp hp1
  have htb := (c09_tail_basic p hp hp1).1
  obtain ⟨c₄, hc₄, hamp4⟩ := c09_aux_sn_amp p hp hp1
  have hc₃p : 0 < p * (1 - p) * (24 / 25 : ℝ) ^ (p - 2) / 25 := by
    have : 0 < 1 - p := by linarith
    positivity
  obtain ⟨CT, hCT, hT⟩ := appendix_triangle (p * (26 / 25 : ℝ) ^ (p - 1)) (p * (24 / 25 : ℝ) ^ (p - 1))
    (p * (1 - p) * (24 / 25 : ℝ) ^ (p - 2) / 25) c₄ (by positivity) (by positivity) hc₃p hc₄
  refine ⟨(CT * (CE + 4 ^ ((1 - p) / (2 * p))) * (1 + 1 / (50 / 51 : ℝ) ^ p) ^ (4 : ℝ) + 1),
    by positivity, fun R hR j hj y z hy hz => ?_⟩
  have hR0 : 0 < R := by linarith
  have hjy := c09_aux_jb_pos y
  have hjz := c09_aux_jb_pos z
  have hzpos : 0 < z := by linarith
  -- vanishing for small `y`
  by_cases hyy : y < (50 / 51 : ℝ) ^ p
  · have : c09_stationary_split_kernel_s p R j y z = 0 := by
      unfold c09_stationary_split_kernel_s
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ))]
      · simp
      · intro ξ hξ
        rw [uIcc_of_le (by linarith)] at hξ
        have : c09_stationary_split_amp_s p R j y ξ = 0 := by
          by_contra hne
          have := (h5 R hR j hj y ξ (by linarith [hξ.1]) hne).1
          linarith
        simp only [this, zero_mul]
    rw [this, norm_zero]
    positivity
  push Not at hyy
  set x₀ : ℝ := y ^ (1 / p) with hx₀
  have hx₀0 : 0 < x₀ := Real.rpow_pos_of_pos hy _
  have hx₀p : x₀ ^ p = y := by
    rw [hx₀, ← Real.rpow_mul hy.le, div_mul_cancel₀ 1 hp0.ne', Real.rpow_one]
  obtain ⟨hΦ3, hΦ'0, hΦ23⟩ := c09_aux_sn_phi p hp hp1 y x₀ hx₀0 hx₀p
  set a : ℝ → ℂ := c09_stationary_split_amp_s p R j y with ha
  have hamp := c09_aux_amp_contDiff R j
  have hasm : ContDiff ℝ (⊤ : ℕ∞) a := by
    simp only [ha]; unfold c09_stationary_split_amp_s
    exact (Complex.ofRealCLM.contDiff.comp (c09_aux_chi_s_smooth p y)).mul hamp
  have hsupp_a : ∀ t, a t ≠ 0 → |t - x₀| ≤ x₀ / 50 := by
    intro t hat
    have hamp0 : c09_positive_kernel_amp R j t ≠ 0 := by
      intro h; apply hat; simp only [ha, c09_stationary_split_amp_s, h, mul_zero]
    have ht1 := (c09_aux_cut_A5 j R hR0 t hamp0).1
    have hχ0 : c09_stationary_split p y t ≠ 0 := by
      intro h; apply hat; simp only [ha, c09_stationary_split_amp_s, h, Complex.ofReal_zero, zero_mul]
    exact (h1a y t (by linarith) hχ0).2
  have hts : tsupport a ⊆ Ioo (x₀ - x₀ / 25) (x₀ + x₀ / 25) := by
    have : tsupport a ⊆ Icc (x₀ - x₀ / 50) (x₀ + x₀ / 50) := by
      refine closure_minimal (fun t ht => ?_) isClosed_Icc
      have := hsupp_a t ht
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    refine this.trans fun t ht => ⟨?_, ?_⟩ <;> linarith [ht.1, ht.2]
  have hEt : ∀ t ∈ Ioo (x₀ - x₀ / 25) (x₀ + x₀ / 25),
      Tendsto (fun R : ℝ => ∫ s in t..R, Complex.exp (Complex.I * (c09_tail_integral_phase p z s : ℂ)))
        atTop (𝓝 (c09_tail_integral p z t)) ∧
      ‖c09_tail_integral p z t‖ ≤ CE * jb z ^ ((1 - p) / (2 * p)) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    refine ⟨htb z t ht0, (hE z t ht0).trans (le_of_eq ?_)⟩
    unfold c09_weights_E; rw [if_neg (not_le.mpr hzpos)]
  have hsum : ∀ t ∈ Ioo (x₀ - x₀ / 25) (x₀ + x₀ / 25),
      (fun t => y * t - Phi0 p t) t + c09_tail_integral_phase p z t = (y - z) * t + 0 := by
    intro t _; simp only [c09_tail_integral_phase]; ring
  have hmain := hT x₀ (x₀ / 25) (x₀ ^ (p - 1)) (x₀ ^ ((j : ℝ) - 2)) (CE * jb z ^ ((1 - p) / (2 * p)))
    (y - z) 0 (by positivity) (Real.rpow_pos_of_pos hx₀0 _) (Real.rpow_pos_of_pos hx₀0 _).le
    (by positivity) (fun t => y * t - Phi0 p t) (c09_tail_integral_phase p z) a
    (c09_tail_integral p z) hΦ3 hΦ'0 (fun t ht => by
      obtain ⟨h1, h2, h3⟩ := hΦ23 t ht
      exact ⟨by linarith, h2, by simpa [mul_div_assoc] using h3⟩)
    (hasm.of_le (by simpa using c09_aux_le_inf 2)) hts
    (fun j' hj' t ht => hamp4 R hR j hj y hy j' hj' t ht) (c09_aux_phase_cont p hp0 z).continuousOn
    hEt hsum
  -- the kernel equals the integral over `Ioo`
  have hK : c09_stationary_split_kernel_s p R j y z =
      ∫ t in Ioo (x₀ - x₀ / 25) (x₀ + x₀ / 25), a t *
        Complex.exp (Complex.I * (((fun t => y * t - Phi0 p t) t : ℝ) : ℂ)) * c09_tail_integral p z t := by
    unfold c09_stationary_split_kernel_s
    rw [intervalIntegral.integral_of_le (by linarith)]
    have hz1 : ∀ t ∉ Ioc (1 : ℝ) (2 * R), a t *
        Complex.exp (Complex.I * (((fun t => y * t - Phi0 p t) t : ℝ) : ℂ)) * c09_tail_integral p z t = 0 := by
      intro t ht
      have : a t = 0 := by
        by_contra hat
        have hamp0 : c09_positive_kernel_amp R j t ≠ 0 := by
          intro h; apply hat; simp only [ha, c09_stationary_split_amp_s, h, mul_zero]
        obtain ⟨h1, h2⟩ := c09_aux_cut_A5 j R hR0 t hamp0
        apply ht
        refine ⟨?_, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · subst h; exact absurd (c09_aux_amp_zero_of_le_one R j 1 le_rfl) hamp0
        · exact h
      rw [this, zero_mul, zero_mul]
    have hz2 : ∀ t ∉ Ioo (x₀ - x₀ / 25) (x₀ + x₀ / 25), a t *
        Complex.exp (Complex.I * (((fun t => y * t - Phi0 p t) t : ℝ) : ℂ)) * c09_tail_integral p z t = 0 := by
      intro t ht
      rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hts h)), zero_mul, zero_mul]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
      setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  rw [hK]
  refine hmain.trans ?_
  exact c09_aux_sn_arith p hp hp1 CT CE hCT hCE j hj y z hyy hz

/-- Iterated derivatives of a compactly supported smooth function are compactly supported. -/
theorem c09_aux_hcs_iter (s : ℝ → ℂ) (hs : HasCompactSupport s) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n s) := by
  induction n with
  | zero => simpa using hs
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- One integration by parts: `(iz) ∫ s e^{izξ} = -∫ s' e^{izξ}`. -/
theorem c09_aux_four_ibp (s : ℝ → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) s) (hsupp : HasCompactSupport s)
    (z : ℝ) :
    (Complex.I * (z : ℂ)) * ∫ ξ, s ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) =
      -∫ ξ, deriv s ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) := by
  have hsc : Continuous s := hs.continuous
  have hdc : Continuous (deriv s) := hs.continuous_deriv (by exact_mod_cast le_top)
  have hez : Continuous fun ξ : ℝ => Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) := by fun_prop
  have hv : ∀ ξ : ℝ, HasDerivAt (fun ξ : ℝ => Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)))
      (Complex.I * (z : ℂ) * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ))) ξ := by
    intro ξ
    have h : HasDerivAt (fun ξ : ℝ => Complex.I * (z : ℂ) * (ξ : ℂ)) (Complex.I * (z : ℂ)) ξ := by
      simpa using ((hasDerivAt_id ξ).ofReal_comp).const_mul (Complex.I * (z : ℂ))
    convert h.cexp using 1; ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := s) (u' := deriv s)
    (v := fun ξ : ℝ => Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)))
    (v' := fun ξ : ℝ => Complex.I * (z : ℂ) * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)))
    (fun x _ => (hs.differentiable (by simp) x).hasDerivAt) (fun x _ => hv x)
    ((hsc.mul (continuous_const.mul hez)).integrable_of_hasCompactSupport (hsupp.mul_right))
    ((hdc.mul hez).integrable_of_hasCompactSupport (hsupp.deriv.mul_right))
    ((hsc.mul hez).integrable_of_hasCompactSupport (hsupp.mul_right))
  rw [← integral_const_mul]
  rw [show (∫ ξ, Complex.I * (z : ℂ) * (s ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)))) =
      ∫ ξ, s ξ * (Complex.I * (z : ℂ) * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ))) by
    congr 1; funext ξ; ring]
  exact h

/-- Iterated: `(iz)^N ∫ s e^{izξ} = (-1)^N ∫ s^{(N)} e^{izξ}`. -/
theorem c09_aux_four_ibp_iter (s : ℝ → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) s) (hsupp : HasCompactSupport s)
    (z : ℝ) (N : ℕ) :
    (Complex.I * (z : ℂ)) ^ N * ∫ ξ, s ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) =
      (-1) ^ N * ∫ ξ, iteratedDeriv N s ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv N s) := by
      rw [iteratedDeriv_eq_iterate]; exact hs.iterate_deriv N
    rw [pow_succ, mul_comm ((Complex.I * (z : ℂ)) ^ N), mul_assoc, ih, mul_left_comm,
      c09_aux_four_ibp _ hN (c09_aux_hcs_iter s hsupp N), iteratedDeriv_succ]
    ring

/-! #### Helpers for the stationary far estimate -/

/-- Geometry of the far region `z < y/4`, `y ≥ (50/51)^p`, with `ξ₀ = (49/50) y^{1/p}`. -/
theorem c09_aux_sf_geom (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (y z : ℝ)
    (hy : (50 / 51 : ℝ) ^ p ≤ y) (hz : z < y / 4) :
    0 < 49 / 50 * y ^ (1 / p) ∧
    (∀ η, 49 / 50 * y ^ (1 / p) ≤ η → 1 / 2 * (|z| + η ^ p) ≤ |z - η ^ p|) ∧
    (1 / 2 * ((49 / 50 * y ^ (1 / p)) ^ p + |z|) ≤ (49 / 50 * y ^ (1 / p)) ^ p - z) ∧
    3 / 5 * (y + |z|) ≤ y - z ∧
    (∀ η, 49 / 50 * y ^ (1 / p) ≤ η → 49 / 50 * (y + |z|) ≤ η ^ p + |z|) := by
  have hp0 : 0 < p := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hx₀ : 0 < y ^ (1 / p) := Real.rpow_pos_of_pos hy0 _
  have hξ₀p : (49 / 50 * y ^ (1 / p)) ^ p = (49 / 50 : ℝ) ^ p * y := by
    rw [Real.mul_rpow (by norm_num) hx₀.le, ← Real.rpow_mul hy0.le, div_mul_cancel₀ 1 hp0.ne',
      Real.rpow_one]
  have hc : (49 / 50 : ℝ) ≤ (49 / 50 : ℝ) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_ge (x := (49 / 50 : ℝ)) (by norm_num) (by norm_num) hp1.le
  have hlow : ∀ η, 49 / 50 * y ^ (1 / p) ≤ η → 49 / 50 * y ≤ η ^ p := by
    intro η hη
    have := Real.rpow_le_rpow (by positivity) hη hp0.le
    rw [hξ₀p] at this
    nlinarith
  refine ⟨by positivity, fun η hη => ?_, ?_, ?_, fun η hη => ?_⟩
  · have h := hlow η hη
    rw [abs_sub_comm]; refine le_trans ?_ (le_abs_self _)
    rcases le_or_gt 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0]; linarith
    · rw [abs_of_neg hz0]; linarith
  · have h : 49 / 50 * y ≤ (49 / 50 * y ^ (1 / p)) ^ p := by rw [hξ₀p]; nlinarith
    rcases le_or_gt 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0]; linarith
    · rw [abs_of_neg hz0]; linarith
  · rcases le_or_gt 0 z with hz0 | hz0
    · rw [abs_of_nonneg hz0]; linarith
    · rw [abs_of_neg hz0]; linarith
  · have h := hlow η hη
    have := abs_nonneg z
    linarith

/-- Uniform symbol bounds for `a_j^{s,R}(y,·)`. -/
theorem c09_aux_sf_amp (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (N : ℕ) :
    ∃ Ca, 0 < Ca ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y t : ℝ, 0 < t → ∀ i ≤ N,
      ‖iteratedDeriv i (c09_stationary_split_amp_s p R j y) t‖ ≤ Ca * t ^ (((j : ℝ) - 2) - i) := by
  obtain ⟨cstar, -, -, Ccut, hCcut, -, -, -, -, -, h3, -, -, -, -⟩ := c09_cutoff_bounds p hp hp1
  obtain ⟨A0, hA0, hans0⟩ := c09_aux_ans_bounds p hp hp1 0 (by norm_num) N
  obtain ⟨A1, hA1, hans1⟩ := c09_aux_ans_bounds p hp hp1 1 (by norm_num) N
  obtain ⟨A2, hA2, hans2⟩ := c09_aux_ans_bounds p hp hp1 2 le_rfl N
  have hS : 0 ≤ ∑ ℓ ∈ Finset.range (N + 1), Ccut ℓ := Finset.sum_nonneg fun ℓ _ => (hCcut ℓ).le
  refine ⟨∑ ℓ ∈ Finset.range (N + 1), Ccut ℓ + A0 + A1 + A2, by positivity,
    fun R hR j hj y t ht i hi => ?_⟩
  have hamp := c09_aux_amp_contDiff R j
  have hans_sm : ContDiff ℝ (⊤ : ℕ∞) (c09_aux_ans p R j y) := by
    show ContDiff ℝ (⊤ : ℕ∞) (c09_stationary_split_amp_ns p R j y)
    unfold c09_stationary_split_amp_ns
    exact (Complex.ofRealCLM.contDiff.comp (c09_aux_chi_ns_smooth p y)).mul hamp
  have hdiff : c09_stationary_split_amp_s p R j y = c09_positive_kernel_amp R j - c09_aux_ans p R j y := by
    funext t
    simp only [Pi.sub_apply, c09_stationary_split_amp_s]
    show _ = _ - c09_stationary_split_amp_ns p R j y t
    unfold c09_stationary_split_amp_ns c09_stationary_split_chi_ns
    push_cast; ring
  rw [hdiff, iteratedDeriv_sub (hamp.contDiffAt.of_le (by simpa using c09_aux_le_inf i))
    (hans_sm.contDiffAt.of_le (by simpa using c09_aux_le_inf i))]
  have b1 := (h3 R hR j hj).2.2.2 i t ht
  have hpos : 0 < t ^ (((j : ℝ) - 2) - i) := Real.rpow_pos_of_pos ht _
  have hAs : ‖iteratedDeriv i (c09_aux_ans p R j y) t‖ ≤ (A0 + A1 + A2) * t ^ (((j : ℝ) - 2) - i) := by
    interval_cases j
    · exact (hans0 R hR y t ht i hi).trans (by gcongr; linarith)
    · exact (hans1 R hR y t ht i hi).trans (by gcongr; linarith)
    · exact (hans2 R hR y t ht i hi).trans (by gcongr; linarith)
  have hCc : Ccut i ≤ ∑ ℓ ∈ Finset.range (N + 1), Ccut ℓ :=
    Finset.single_le_sum (f := Ccut) (fun ℓ _ => (hCcut ℓ).le) (Finset.mem_range.mpr (by omega))
  calc _ ≤ ‖iteratedDeriv i (c09_positive_kernel_amp R j) t‖ + ‖iteratedDeriv i (c09_aux_ans p R j y) t‖ :=
        norm_sub_le _ _
    _ ≤ Ccut i * t ^ ((j : ℝ) - 2 - i) + (A0 + A1 + A2) * t ^ (((j : ℝ) - 2) - i) := add_le_add b1 hAs
    _ = (Ccut i + (A0 + A1 + A2)) * t ^ (((j : ℝ) - 2) - i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpos.le

/-- Support of `a_j^{s,R}(y,·)`: contained in `[(49/50) y^{1/p}, (51/50) y^{1/p}]`, and empty
unless `y ≥ (50/51)^p`. -/
theorem c09_aux_sf_supp (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (R : ℝ) (hR : 2 ≤ R) (j : ℕ)
    (hj : j ≤ 2) (y : ℝ) :
    tsupport (c09_stationary_split_amp_s p R j y) ⊆
      Icc (49 / 50 * y ^ (1 / p)) (51 / 50 * y ^ (1 / p)) := by
  obtain ⟨cs, -, -, Cc, -, -, -, -, -, -, -, -, -, -, h5⟩ := c09_cutoff_bounds p hp hp1
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  have hR0 : 0 < R := by linarith
  have hamp0 : c09_positive_kernel_amp R j t ≠ 0 := by
    intro h; apply ht; simp only [c09_stationary_split_amp_s, h, mul_zero]
  have ht1 := (c09_aux_cut_A5 j R hR0 t hamp0).1
  obtain ⟨-, h1, h2, -⟩ := h5 R hR j hj y t (by linarith) ht
  exact ⟨h1, h2⟩

/-- `ξ₀ = (49/50) y^{1/p} ≥ 49/51` for `y ≥ (50/51)^p`. -/
theorem c09_aux_sf_xi0 (p : ℝ) (hp : 3 / 4 < p) (y : ℝ) (hy : (50 / 51 : ℝ) ^ p ≤ y) :
    (49 / 51 : ℝ) ≤ 49 / 50 * y ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h1 : (50 / 51 : ℝ) ≤ y ^ (1 / p) := by
    have := Real.rpow_le_rpow (by positivity) hy (by positivity : (0 : ℝ) ≤ 1 / p)
    rwa [← Real.rpow_mul (by norm_num), mul_one_div_cancel hp0.ne', Real.rpow_one] at this
  nlinarith

/-- Bound on `∫ ‖g‖` for `g` continuous, vanishing off `[a, a·51/49]`, bounded by `B` there. -/
theorem c09_aux_sf_L1 (g : ℝ → ℂ) (hg : Continuous g) (a B : ℝ) (ha : 0 < a)
    (hz : ∀ ξ ∉ Icc a (51 / 49 * a), g ξ = 0) (hb : ∀ ξ ∈ Icc a (51 / 49 * a), ‖g ξ‖ ≤ B) :
    ∫ ξ, ‖g ξ‖ ≤ B * (2 / 49 * a) := by
  have hz' : ∀ ξ ∉ Icc a (51 / 49 * a), ‖g ξ‖ = 0 := fun ξ hξ => by rw [hz ξ hξ, norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz']
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb a ⟨le_rfl, by linarith⟩)
  calc ∫ ξ in Icc a (51 / 49 * a), ‖g ξ‖ ≤ ∫ ξ in Icc a (51 / 49 * a), B :=
        setIntegral_mono_on hg.norm.integrableOn_Icc (integrableOn_const (by simp)) measurableSet_Icc hb
    _ = B * (2 / 49 * a) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]; ring

/-- The `k`-th term of the far expansion: `|y - z|^{N} ‖∫ a D^k g₀ e^{i(y-z)ξ}‖ ≤ C`. -/
theorem c09_aux_sf_term (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (k N : ℕ) (hN : 1 ≤ N) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ, (50 / 51 : ℝ) ^ p ≤ y → z < y / 4 →
      Integrable (fun ξ => c09_stationary_split_amp_s p R j y ξ * c09_tail_expansion_D p z k ξ *
          Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ))) ∧
      ‖∫ ξ, c09_stationary_split_amp_s p R j y ξ * c09_tail_expansion_D p z k ξ *
          Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ))‖ * |y - z| ^ N ≤ C := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Ca, hCa, hamp⟩ := c09_aux_sf_amp p hp hp1 N
  obtain ⟨CD, hCD, hD⟩ := c09_aux_D_bounds p hp0 (1 / 2) (by norm_num) k N
  set c0 : ℝ := 49 / 51 with hc0
  set K : ℝ := 2 ^ N * (Ca * CD) * c0 ^ (-(1 : ℝ) - k - N) * ((c0 ^ p) ^ (k + 1))⁻¹ * (2 / 49) with hK
  refine ⟨K + 1, by positivity, fun R hR j hj y z hy hz => ?_⟩
  obtain ⟨hξ₀0, hgood, -, -, -⟩ := c09_aux_sf_geom p hp hp1 y z hy hz
  set ξ₀ : ℝ := 49 / 50 * y ^ (1 / p) with hξ₀
  have hc0ξ : c0 ≤ ξ₀ := c09_aux_sf_xi0 p hp y hy
  have hsupp := c09_aux_sf_supp p hp hp1 R hR j hj y
  have hx1 : 51 / 50 * y ^ (1 / p) = 51 / 49 * ξ₀ := by rw [hξ₀]; ring
  rw [hx1] at hsupp
  set a := c09_stationary_split_amp_s p R j y with ha
  set D := c09_tail_expansion_D p z k with hDdef
  set s : ℝ → ℂ := fun ξ => a ξ * D ξ with hs
  have hasm : ContDiff ℝ (⊤ : ℕ∞) a := by
    simp only [ha]; unfold c09_stationary_split_amp_s
    exact (Complex.ofRealCLM.contDiff.comp (c09_aux_chi_s_smooth p y)).mul (c09_aux_amp_contDiff R j)
  have hU := c09_aux_U_open p hp0 z
  have hDsm := c09_aux_D_smooth p hp0 z k
  have hgoodξ : ∀ ξ ∈ Icc ξ₀ (51 / 49 * ξ₀), 0 < ξ ∧ z - ξ ^ p ≠ 0 := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    refine ⟨hξ0, fun h => ?_⟩
    have := hgood ξ hξ.1
    rw [h, abs_zero] at this
    have := Real.rpow_pos_of_pos hξ0 p
    nlinarith [abs_nonneg z]
  have hDat : ∀ ξ ∈ Icc ξ₀ (51 / 49 * ξ₀), ContDiffAt ℝ (⊤ : ℕ∞) D ξ := fun ξ hξ =>
    hDsm.contDiffAt (hU.mem_nhds ⟨(hgoodξ ξ hξ).1, (hgoodξ ξ hξ).2⟩)
  have hs_sm : ContDiff ℝ (⊤ : ℕ∞) s := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases h : ξ ∈ tsupport a
    · exact hasm.contDiffAt.mul (hDat ξ (hsupp h))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h] with x hx
      show a x * D x = 0
      rw [show a x = 0 from hx, zero_mul]
  have hs_supp : HasCompactSupport s := by
    refine HasCompactSupport.intro (isCompact_Icc (a := ξ₀) (b := 51 / 49 * ξ₀)) fun x hx => ?_
    simp only [hs]
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h)), zero_mul]
  have hexpc : Continuous fun ξ : ℝ => Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ)) := by
    fun_prop
  refine ⟨(hs_sm.continuous.mul hexpc).integrable_of_hasCompactSupport hs_supp.mul_right, ?_⟩
  -- `N`-fold integration by parts
  have hibp := c09_aux_four_ibp_iter s hs_sm hs_supp (y - z) N
  have hnorm : ‖∫ ξ, s ξ * Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ))‖ * |y - z| ^ N ≤
      ∫ ξ, ‖iteratedDeriv N s ξ‖ := by
    have hn := congrArg norm hibp
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_neg, norm_one, one_pow, one_mul] at hn
    rw [mul_comm, hn]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext ξ; rw [norm_mul, c09_aux_norm_exp_pos, mul_one]
  have hint_eq : (∫ ξ, a ξ * D ξ * Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ))) =
      ∫ ξ, s ξ * Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ)) := rfl
  rw [hint_eq]
  refine hnorm.trans ?_
  -- pointwise bound of `∂^N s` on the support
  set B : ℝ := 2 ^ N * (Ca * CD) * ξ₀ ^ ((j : ℝ) - 2 - k - N) * ((ξ₀ ^ p) ^ (k + 1))⁻¹ with hB
  have hzero : ∀ ξ ∉ Icc ξ₀ (51 / 49 * ξ₀), iteratedDeriv N s ξ = 0 := by
    intro ξ hξ
    have h : ξ ∉ tsupport a := fun h => hξ (hsupp h)
    have hev : s =ᶠ[𝓝 ξ] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h] with x hx
      show a x * D x = 0
      rw [show a x = 0 from hx, zero_mul]
    rw [hev.iteratedDeriv_eq]; simp
  have hbd : ∀ ξ ∈ Icc ξ₀ (51 / 49 * ξ₀), ‖iteratedDeriv N s ξ‖ ≤ B := by
    intro ξ hξ
    obtain ⟨hξ0, -⟩ := hgoodξ ξ hξ
    have hξp := Real.rpow_pos_of_pos hξ0 p
    have hξ₀p := Real.rpow_pos_of_pos hξ₀0 p
    refine (c09_aux_leib_terms a D ξ N (hasm.contDiffAt.of_le (by simpa using c09_aux_le_inf N))
      ((hDat ξ hξ).of_le (by simpa using c09_aux_le_inf N))
      (Ca * CD * ξ₀ ^ ((j : ℝ) - 2 - k - N) * ((ξ₀ ^ p) ^ (k + 1))⁻¹) (fun i hi => ?_)).trans
      (le_of_eq (by rw [hB]; ring))
    have h1 := hamp R hR j hj y ξ hξ0 i hi
    have h2 := hD z ξ hξ0 (by have := hgood ξ hξ.1; linarith [abs_sub_comm z (ξ ^ p)]) (N - i) (Nat.sub_le N i)
    have hW : ((|z| + ξ ^ p) ^ (k + 1))⁻¹ ≤ ((ξ ^ p) ^ (k + 1))⁻¹ := by
      gcongr; linarith [abs_nonneg z]
    have hW2 : ((ξ ^ p) ^ (k + 1))⁻¹ ≤ ((ξ₀ ^ p) ^ (k + 1))⁻¹ := by
      gcongr; exact hξ.1
    have hexp : ξ ^ (((j : ℝ) - 2) - i) * ξ ^ (-(k : ℝ) - ((N - i : ℕ) : ℝ)) = ξ ^ ((j : ℝ) - 2 - k - N) := by
      rw [← Real.rpow_add hξ0, Nat.cast_sub hi]; congr 1; ring
    have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have hmono : ξ ^ ((j : ℝ) - 2 - k - N) ≤ ξ₀ ^ ((j : ℝ) - 2 - k - N) :=
      Real.rpow_le_rpow_of_nonpos hξ₀0 hξ.1 (by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith)
    calc ‖iteratedDeriv i a ξ‖ * ‖iteratedDeriv (N - i) D ξ‖
        ≤ (Ca * ξ ^ (((j : ℝ) - 2) - i)) * (CD * ((|z| + ξ ^ p) ^ (k + 1))⁻¹ *
            ξ ^ (-(k : ℝ) - ((N - i : ℕ) : ℝ))) := by
          gcongr
      _ = Ca * CD * (ξ ^ (((j : ℝ) - 2) - i) * ξ ^ (-(k : ℝ) - ((N - i : ℕ) : ℝ))) *
            ((|z| + ξ ^ p) ^ (k + 1))⁻¹ := by ring
      _ ≤ Ca * CD * ξ₀ ^ ((j : ℝ) - 2 - k - N) * ((ξ₀ ^ p) ^ (k + 1))⁻¹ := by
          rw [hexp]
          have : 0 ≤ Ca * CD := by positivity
          calc Ca * CD * ξ ^ ((j : ℝ) - 2 - k - N) * ((|z| + ξ ^ p) ^ (k + 1))⁻¹
              ≤ Ca * CD * ξ₀ ^ ((j : ℝ) - 2 - k - N) * ((ξ₀ ^ p) ^ (k + 1))⁻¹ := by
                have hp1' : 0 ≤ ((|z| + ξ ^ p) ^ (k + 1))⁻¹ := by positivity
                have hp2' : 0 ≤ ξ₀ ^ ((j : ℝ) - 2 - k - N) := (Real.rpow_pos_of_pos hξ₀0 _).le
                exact mul_le_mul (mul_le_mul_of_nonneg_left hmono this) (hW.trans hW2) hp1'
                  (mul_nonneg this hp2')
            _ = _ := rfl
  have hcont : Continuous (iteratedDeriv N s) := hs_sm.continuous_iteratedDeriv N (by exact_mod_cast le_top)
  refine (c09_aux_sf_L1 _ hcont ξ₀ B hξ₀0 hzero hbd).trans ?_
  -- uniform constant
  have hξ₀p := Real.rpow_pos_of_pos hξ₀0 p
  have hc0p : 0 < c0 ^ p := by positivity
  have hfin : B * (2 / 49 * ξ₀) ≤ K := by
    rw [hB, hK]
    have e1 : ξ₀ ^ ((j : ℝ) - 2 - k - N) * ξ₀ = ξ₀ ^ ((j : ℝ) - 1 - k - N) := by
      rw [← Real.rpow_add_one hξ₀0.ne']; ring_nf
    have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have e2 : ξ₀ ^ ((j : ℝ) - 1 - k - N) ≤ c0 ^ ((j : ℝ) - 1 - k - N) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hc0ξ (by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have e3 : c0 ^ ((j : ℝ) - 1 - k - N) ≤ c0 ^ (-(1 : ℝ) - k - N) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    have e4 : ((ξ₀ ^ p) ^ (k + 1))⁻¹ ≤ ((c0 ^ p) ^ (k + 1))⁻¹ := by
      gcongr
    calc 2 ^ N * (Ca * CD) * ξ₀ ^ ((j : ℝ) - 2 - k - N) * ((ξ₀ ^ p) ^ (k + 1))⁻¹ * (2 / 49 * ξ₀)
        = 2 ^ N * (Ca * CD) * (ξ₀ ^ ((j : ℝ) - 2 - k - N) * ξ₀) * ((ξ₀ ^ p) ^ (k + 1))⁻¹ * (2 / 49) := by
          ring
      _ = 2 ^ N * (Ca * CD) * ξ₀ ^ ((j : ℝ) - 1 - k - N) * ((ξ₀ ^ p) ^ (k + 1))⁻¹ * (2 / 49) := by
          rw [e1]
      _ ≤ 2 ^ N * (Ca * CD) * c0 ^ (-(1 : ℝ) - k - N) * ((c0 ^ p) ^ (k + 1))⁻¹ * (2 / 49) := by
          gcongr
          exact e2.trans e3
  linarith

/-- The remainder of the far expansion: `‖∫ a e^{iΘ} ∫_ξ^∞ e^{iΨ} ∂D^N‖ ≤ C (y+|z|)^{-N-1}`. -/
theorem c09_aux_sf_rem (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ, (50 / 51 : ℝ) ^ p ≤ y → z < y / 4 →
      ‖∫ ξ, c09_stationary_split_amp_s p R j y ξ *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) *
          ∫ η in Ioi ξ, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
            deriv (c09_tail_expansion_D p z N) η‖ ≤ C * ((y + |z|) ^ (N + 1))⁻¹ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Ca, hCa, hamp⟩ := c09_aux_sf_amp p hp hp1 0
  obtain ⟨CD, hCD, hD⟩ := c09_aux_D_bounds p hp0 (1 / 2) (by norm_num) N 1
  set c0 : ℝ := 49 / 51 with hc0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set K : ℝ := Ca * CD / N * c0 ^ (-(1 : ℝ) - N) * (50 / 49 : ℝ) ^ (N + 1) * (2 / 49) with hK
  refine ⟨K + 1, by positivity, fun R hR j hj y z hy hz => ?_⟩
  obtain ⟨hξ₀0, hgood, -, -, hW⟩ := c09_aux_sf_geom p hp hp1 y z hy hz
  set ξ₀ : ℝ := 49 / 50 * y ^ (1 / p) with hξ₀
  have hc0ξ : c0 ≤ ξ₀ := c09_aux_sf_xi0 p hp y hy
  have hsupp := c09_aux_sf_supp p hp hp1 R hR j hj y
  have hx1 : 51 / 50 * y ^ (1 / p) = 51 / 49 * ξ₀ := by rw [hξ₀]; ring
  rw [hx1] at hsupp
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  set W : ℝ := y + |z| with hWdef
  have hW0 : 0 < W := by have := abs_nonneg z; linarith
  have hWW : 0 < 49 / 50 * W := by positivity
  -- the inner remainder
  have hrem : ∀ ξ, ξ₀ ≤ ξ → ‖∫ η in Ioi ξ, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
      deriv (c09_tail_expansion_D p z N) η‖ ≤ CD * (((49 / 50 * W) ^ (N + 1))⁻¹ * (ξ ^ (-(N : ℝ)) / N)) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_of_lt_of_le hξ₀0 hξ
    have hint : IntegrableOn (fun η : ℝ => CD * ((49 / 50 * W) ^ (N + 1))⁻¹ * η ^ (-(N : ℝ) - 1)) (Ioi ξ) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hξ0).const_mul _
    have hb : ∀ η ∈ Ioi ξ, ‖Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
        deriv (c09_tail_expansion_D p z N) η‖ ≤ CD * ((49 / 50 * W) ^ (N + 1))⁻¹ * η ^ (-(N : ℝ) - 1) := by
      intro η hη
      have hη0 : 0 < η := lt_trans hξ0 hη
      have hηξ : ξ₀ ≤ η := hξ.trans hη.le
      rw [norm_mul, c09_aux_norm_exp_phase, one_mul]
      have h1 := hD z η hη0 (by have := hgood η hηξ; linarith [abs_sub_comm z (η ^ p)]) 1 le_rfl
      rw [iteratedDeriv_one] at h1
      refine h1.trans ?_
      have hW2 := hW η hηξ
      have : ((|z| + η ^ p) ^ (N + 1))⁻¹ ≤ ((49 / 50 * W) ^ (N + 1))⁻¹ := by
        gcongr; linarith
      have := Real.rpow_pos_of_pos hη0 (-(N : ℝ) - ((1 : ℕ) : ℝ))
      push_cast at this ⊢
      gcongr
    refine (norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioi hb)).trans
      (le_of_eq ?_)
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hξ0,
      show -(N : ℝ) - 1 + 1 = -(N : ℝ) by ring]
    field_simp
  -- the outer integral
  set B : ℝ := Ca * CD / N * ξ₀ ^ ((j : ℝ) - 2 - N) * ((49 / 50 * W) ^ (N + 1))⁻¹ with hB
  have hpt : ∀ ξ, ‖c09_stationary_split_amp_s p R j y ξ *
      Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) *
      ∫ η in Ioi ξ, Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
        deriv (c09_tail_expansion_D p z N) η‖ ≤
      Set.indicator (Icc ξ₀ (51 / 49 * ξ₀)) (fun _ => B) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Icc ξ₀ (51 / 49 * ξ₀)
    · rw [Set.indicator_of_mem hξ]
      have hξ0 : 0 < ξ := lt_of_lt_of_le hξ₀0 hξ.1
      rw [norm_mul, norm_mul, c09_aux_norm_exp_phase, mul_one]
      have h1 := hamp R hR j hj y ξ hξ0 0 le_rfl
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at h1
      have h2 := hrem ξ hξ.1
      have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      have hmono : ξ ^ ((j : ℝ) - 2 - N) ≤ ξ₀ ^ ((j : ℝ) - 2 - N) :=
        Real.rpow_le_rpow_of_nonpos hξ₀0 hξ.1 (by linarith)
      have e : ξ ^ ((j : ℝ) - 2) * ξ ^ (-(N : ℝ)) = ξ ^ ((j : ℝ) - 2 - N) := by
        rw [← Real.rpow_add hξ0]; ring_nf
      have hWp : 0 ≤ ((49 / 50 * W) ^ (N + 1))⁻¹ := by positivity
      calc _ ≤ (Ca * ξ ^ ((j : ℝ) - 2)) * (CD * (((49 / 50 * W) ^ (N + 1))⁻¹ * (ξ ^ (-(N : ℝ)) / N))) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = Ca * CD / N * (ξ ^ ((j : ℝ) - 2) * ξ ^ (-(N : ℝ))) * ((49 / 50 * W) ^ (N + 1))⁻¹ := by
            field_simp
        _ ≤ B := by
            rw [e, hB]
            have : 0 ≤ Ca * CD / N := by positivity
            gcongr
    · rw [Set.indicator_of_notMem hξ]
      have : c09_stationary_split_amp_s p R j y ξ = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hξ (hsupp h))
      rw [this, zero_mul, zero_mul, norm_zero]
  have hGi : Integrable (Set.indicator (Icc ξ₀ (51 / 49 * ξ₀)) (fun _ : ℝ => B)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  refine (norm_integral_le_of_norm_le hGi (Eventually.of_forall hpt)).trans ?_
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul]
  have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have e1 : ((49 / 50 * W) ^ (N + 1))⁻¹ = (50 / 49 : ℝ) ^ (N + 1) * (W ^ (N + 1))⁻¹ := by
    rw [mul_pow, mul_inv, ← inv_pow]; norm_num
  have e2 : ξ₀ ^ ((j : ℝ) - 2 - N) * ξ₀ = ξ₀ ^ ((j : ℝ) - 1 - N) := by
    rw [← Real.rpow_add_one hξ₀0.ne']; ring_nf
  have e3 : ξ₀ ^ ((j : ℝ) - 1 - N) ≤ c0 ^ (-(1 : ℝ) - N) := by
    calc ξ₀ ^ ((j : ℝ) - 1 - N) ≤ c0 ^ ((j : ℝ) - 1 - N) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hc0ξ (by linarith)
      _ ≤ c0 ^ (-(1 : ℝ) - N) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hWi : 0 < (W ^ (N + 1))⁻¹ := by positivity
  calc (51 / 49 * ξ₀ - ξ₀) * B = Ca * CD / N * (2 / 49) * (ξ₀ ^ ((j : ℝ) - 2 - N) * ξ₀) *
        ((49 / 50 * W) ^ (N + 1))⁻¹ := by rw [hB]; ring
    _ = Ca * CD / N * (2 / 49) * ξ₀ ^ ((j : ℝ) - 1 - N) * ((50 / 49 : ℝ) ^ (N + 1) * (W ^ (N + 1))⁻¹) := by
        rw [e2, e1]
    _ ≤ Ca * CD / N * (2 / 49) * c0 ^ (-(1 : ℝ) - N) * ((50 / 49 : ℝ) ^ (N + 1) * (W ^ (N + 1))⁻¹) := by
        gcongr
    _ = K * (W ^ (N + 1))⁻¹ := by rw [hK]; ring
    _ ≤ (K + 1) * (W ^ (N + 1))⁻¹ := by nlinarith

/-- Final arithmetic of the far estimate: `(y+|z|)^{-(N+1)} ≤ C ⟨y⟩^{-M}(⟨y⟩+|z|)^{-M}`. -/
theorem c09_aux_sf_arith (p : ℝ) (hp : 3 / 4 < p) (M : ℝ) (hM : 0 ≤ M) (N : ℕ) (hN : 2 * M ≤ N + 1)
    (y z : ℝ) (hy : (50 / 51 : ℝ) ^ p ≤ y) :
    ((y + |z|) ^ (N + 1))⁻¹ ≤ ((50 / 51 : ℝ) ^ p) ^ (2 * M - (N + 1)) *
      (1 + 1 / (50 / 51 : ℝ) ^ p) ^ (2 * M) * (jb y ^ (-M) * (jb y + |z|) ^ (-M)) := by
  have hp0 : 0 < p := by linarith
  set ys : ℝ := (50 / 51 : ℝ) ^ p with hys
  have hys0 : 0 < ys := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le hys0 hy
  set D : ℝ := 1 + 1 / ys with hD
  have hD1 : 1 ≤ D := by have : 0 < 1 / ys := by positivity
                         linarith
  have hjy := c09_aux_jb_pos y
  set W : ℝ := y + |z| with hW
  have hW0 : 0 < W := by have := abs_nonneg z; linarith
  have hyW : ys ≤ W := by have := abs_nonneg z; linarith
  have hjyD : jb y ≤ D * y := by
    have h1 : jb y ≤ 1 + y := by
      unfold jb; rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have h2 : 1 ≤ y / ys := by rw [le_div_iff₀ hys0]; linarith
    calc jb y ≤ 1 + y := h1
      _ ≤ y / ys + y := by linarith
      _ = D * y := by rw [hD]; ring
  have hj1 : jb y ≤ D * W := hjyD.trans (by gcongr; have := abs_nonneg z; linarith)
  have hj2 : jb y + |z| ≤ D * W := by
    have : D * y + |z| ≤ D * W := by rw [hW]; nlinarith [abs_nonneg z]
    linarith
  have hjz : 0 < jb y + |z| := by have := abs_nonneg z; linarith
  -- `W^{-(N+1)} ≤ ys^{2M-(N+1)} W^{-2M}`
  have e1 : (W ^ (N + 1))⁻¹ = W ^ (-(2 * M)) * W ^ (2 * M - (N + 1)) := by
    rw [← Real.rpow_add hW0, ← Real.rpow_natCast, ← Real.rpow_neg hW0.le]; push_cast; ring_nf
  have e2 : W ^ (2 * M - (N + 1)) ≤ ys ^ (2 * M - (N + 1)) :=
    Real.rpow_le_rpow_of_nonpos hys0 hyW (by linarith)
  have e3 : W ^ (-(2 * M)) = D ^ (2 * M) * ((D * W) ^ (-M) * (D * W) ^ (-M)) := by
    have hDp : (0 : ℝ) < D := by linarith
    rw [Real.mul_rpow hDp.le hW0.le]
    have hd : D ^ (2 * M) * (D ^ (-M) * D ^ (-M)) = 1 := by
      rw [← Real.rpow_add hDp, ← Real.rpow_add hDp]; ring_nf; simp
    have hw : W ^ (-M) * W ^ (-M) = W ^ (-(2 * M)) := by
      rw [← Real.rpow_add hW0]; ring_nf
    calc W ^ (-(2 * M)) = (D ^ (2 * M) * (D ^ (-M) * D ^ (-M))) * (W ^ (-M) * W ^ (-M)) := by
          rw [hd, hw, one_mul]
      _ = _ := by ring
  have e4 : (D * W) ^ (-M) ≤ jb y ^ (-M) := Real.rpow_le_rpow_of_nonpos hjy hj1 (by linarith)
  have e5 : (D * W) ^ (-M) ≤ (jb y + |z|) ^ (-M) := Real.rpow_le_rpow_of_nonpos hjz hj2 (by linarith)
  have hDW : 0 < (D * W) ^ (-M) := Real.rpow_pos_of_pos (by positivity) _
  have hDM : 0 < D ^ (2 * M) := Real.rpow_pos_of_pos (by linarith) _
  have hWM : 0 < W ^ (-(2 * M)) := Real.rpow_pos_of_pos hW0 _
  rw [e1]
  calc W ^ (-(2 * M)) * W ^ (2 * M - (N + 1)) ≤ W ^ (-(2 * M)) * ys ^ (2 * M - (N + 1)) := by gcongr
    _ = ys ^ (2 * M - (N + 1)) * (D ^ (2 * M) * ((D * W) ^ (-M) * (D * W) ^ (-M))) := by rw [e3]; ring
    _ ≤ ys ^ (2 * M - (N + 1)) * (D ^ (2 * M) * (jb y ^ (-M) * (jb y + |z|) ^ (-M))) := by
        gcongr
    _ = _ := by ring

/-- Blueprint: lem:c09_stationary_far.  For `y > 0`, `z < y/4`:
`|K_{+,j}^{s,R}(y,z)| ≤ C_M ⟨y⟩^{-M}(⟨y⟩+|z|)^{-M}`. -/
theorem c09_stationary_far (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ, 0 < y → z < y / 4 →
      ‖c09_stationary_split_kernel_s p R j y z‖ ≤ C * jb y ^ (-M) * (jb y + |z|) ^ (-M) := by
  have hp0 : 0 < p := by linarith
  set N : ℕ := ⌈2 * M⌉₊ + 1 with hNdef
  have hN : 1 ≤ N := by omega
  have hNM : 2 * M ≤ N + 1 := by
    rw [hNdef]; push_cast; have := Nat.le_ceil (2 * M); linarith
  have hterm : ∀ k : ℕ, ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ,
      (50 / 51 : ℝ) ^ p ≤ y → z < y / 4 →
      Integrable (fun ξ => c09_stationary_split_amp_s p R j y ξ * c09_tail_expansion_D p z k ξ *
          Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ))) ∧
      ‖∫ ξ, c09_stationary_split_amp_s p R j y ξ * c09_tail_expansion_D p z k ξ *
          Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ))‖ * |y - z| ^ (N + 1) ≤ C :=
    fun k => c09_aux_sf_term p hp hp1 k (N + 1) (by omega)
  choose Ct hCt hT using hterm
  obtain ⟨Cr, hCr, hRem⟩ := c09_aux_sf_rem p hp hp1 N hN
  obtain ⟨cstar, -, -, Ccut, -, -, -, -, -, -, -, -, -, -, h5⟩ := c09_cutoff_bounds p hp hp1
  have htb := (c09_tail_basic p hp hp1)
  have hexpand := (c09_tail_expansion p hp hp1 (1 / 2) (by norm_num) (by norm_num)).2
  set S : ℝ := ∑ k ∈ Finset.range (N + 1), Ct k with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => (hCt k).le
  set ys : ℝ := (50 / 51 : ℝ) ^ p with hys
  set Cfin : ℝ := ((5 / 3 : ℝ) ^ (N + 1) * S + Cr) * (ys ^ (2 * M - (N + 1)) *
    (1 + 1 / ys) ^ (2 * M)) + 1 with hCfin
  have hys0 : 0 < ys := by positivity
  refine ⟨Cfin, by positivity, fun R hR j hj y z hy hz => ?_⟩
  have hR0 : 0 < R := by linarith
  have hjy := c09_aux_jb_pos y
  have hRHS : 0 ≤ Cfin * jb y ^ (-M) * (jb y + |z|) ^ (-M) := by
    have : 0 < jb y + |z| := by have := abs_nonneg z; linarith
    positivity
  by_cases hyy : y < ys
  · have : c09_stationary_split_kernel_s p R j y z = 0 := by
      unfold c09_stationary_split_kernel_s
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ))]
      · simp
      · intro ξ hξ
        rw [uIcc_of_le (by linarith)] at hξ
        have : c09_stationary_split_amp_s p R j y ξ = 0 := by
          by_contra hne
          have := (h5 R hR j hj y ξ (by linarith [hξ.1]) hne).1
          linarith
        simp only [this, zero_mul]
    rw [this, norm_zero]; exact hRHS
  push Not at hyy
  obtain ⟨hξ₀0, hgood, hcond, hω, -⟩ := c09_aux_sf_geom p hp hp1 y z hyy hz
  set ξ₀ : ℝ := 49 / 50 * y ^ (1 / p) with hξ₀
  have hsupp := c09_aux_sf_supp p hp hp1 R hR j hj y
  set a := c09_stationary_split_amp_s p R j y with ha
  -- the integrand and its decomposition
  set e : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) with he
  set Rm : ℝ → ℂ := fun ξ => a ξ * e ξ * ∫ η in Ioi ξ,
    Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
      deriv (c09_tail_expansion_D p z N) η with hRm
  set T : ℕ → ℝ → ℂ := fun k ξ => a ξ * c09_tail_expansion_D p z k ξ *
    Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ)) with hTdef
  have hid : ∀ ξ, a ξ * e ξ * c09_tail_integral p z ξ =
      ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ (k + 1) * T k ξ + (-1 : ℂ) ^ (N + 1) * Rm ξ := by
    intro ξ
    by_cases haξ : a ξ = 0
    · simp [hRm, hTdef, haξ]
    · have hξ : ξ₀ ≤ ξ := (hsupp (subset_tsupport _ haξ)).1
      rw [(hexpand z ξ₀ hξ₀0 hcond).2 ξ hξ N |>.2]
      have hexp : e ξ * Complex.exp (Complex.I * (c09_tail_integral_phase p z ξ : ℂ)) =
          Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ)) := by
        simp only [he]; rw [← Complex.exp_add]; congr 1
        unfold c09_tail_integral_phase; push_cast; ring
      show _ = ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ (k + 1) * (a ξ * c09_tail_expansion_D p z k ξ *
          Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (ξ : ℂ))) +
        (-1 : ℂ) ^ (N + 1) * (a ξ * e ξ * ∫ η in Ioi ξ,
          Complex.exp (Complex.I * (c09_tail_integral_phase p z η : ℂ)) *
            deriv (c09_tail_expansion_D p z N) η)
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hexp]; ring
      · ring
  -- integrability
  have hac : Continuous a := by
    simp only [ha]; unfold c09_stationary_split_amp_s
    exact (Complex.continuous_ofReal.comp (c09_aux_chi_s_smooth p y).continuous).mul
      (c09_aux_amp_continuous R j)
  have hec : Continuous e := by
    simp only [he]
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).sub (c09_aux_Phi0_continuous p hp0)))).cexp
  have hEc : Continuous (c09_tail_integral p z) :=
    (c09_aux_tail_joint p hp0).comp (f := fun ξ : ℝ => (z, ξ)) (by fun_prop)
  have hasupp : HasCompactSupport a :=
    HasCompactSupport.intro (isCompact_Icc (a := ξ₀) (b := 51 / 50 * y ^ (1 / p)))
      fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
  have hFi : Integrable (fun ξ => a ξ * e ξ * c09_tail_integral p z ξ) :=
    ((hac.mul hec).mul hEc).integrable_of_hasCompactSupport (hasupp.mul_right.mul_right)
  have hTi : ∀ k, Integrable (T k) := fun k => (hT k R hR j hj y z hyy hz).1
  have hsumi : Integrable (fun ξ => ∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ (k + 1) * T k ξ) :=
    integrable_finsetSum _ fun k _ => (hTi k).const_mul _
  have hRmi : Integrable (fun ξ => (-1 : ℂ) ^ (N + 1) * Rm ξ) :=
    (hFi.sub hsumi).congr (Eventually.of_forall fun ξ => by simp only [Pi.sub_apply]; rw [hid ξ]; ring)
  -- the kernel as an integral over `ℝ`
  have hK : c09_stationary_split_kernel_s p R j y z = ∫ ξ, a ξ * e ξ * c09_tail_integral p z ξ := by
    unfold c09_stationary_split_kernel_s
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_
    have : a ξ = 0 := by
      by_contra hat
      have hamp0 : c09_positive_kernel_amp R j ξ ≠ 0 := by
        intro h; apply hat; simp only [ha, c09_stationary_split_amp_s, h, mul_zero]
      obtain ⟨h1, h2⟩ := c09_aux_cut_A5 j R hR0 ξ hamp0
      apply hξ
      refine ⟨?_, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · subst h; exact absurd (c09_aux_amp_zero_of_le_one R j 1 le_rfl) hamp0
      · exact h
    show a ξ * e ξ * c09_tail_integral p z ξ = 0
    rw [this, zero_mul, zero_mul]
  rw [hK, integral_congr_ae (Eventually.of_forall hid), integral_add hsumi hRmi,
    integral_finsetSum _ fun k _ => (hTi k).const_mul _, integral_const_mul]
  simp_rw [integral_const_mul]
  -- estimates
  have hW0 : 0 < y + |z| := by have := abs_nonneg z; linarith
  have hyz : 0 < |y - z| := by
    have : 0 < y - z := by nlinarith [abs_nonneg z]
    rw [abs_of_pos this]; exact this
  have hyz' : (3 / 5) * (y + |z|) ≤ |y - z| := by
    rw [abs_of_pos (by nlinarith [abs_nonneg z] : (0 : ℝ) < y - z)]; exact hω
  have hTb : ∀ k, ‖∫ ξ, T k ξ‖ ≤ Ct k * ((5 / 3 : ℝ) ^ (N + 1) * ((y + |z|) ^ (N + 1))⁻¹) := by
    intro k
    have h := (hT k R hR j hj y z hyy hz).2
    have hpow : ((5 / 3 : ℝ) ^ (N + 1))⁻¹ * (y + |z|) ^ (N + 1) ≤ |y - z| ^ (N + 1) := by
      rw [← inv_pow, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hpos : 0 < ((5 / 3 : ℝ) ^ (N + 1))⁻¹ * (y + |z|) ^ (N + 1) := by positivity
    have : ‖∫ ξ, T k ξ‖ * (((5 / 3 : ℝ) ^ (N + 1))⁻¹ * (y + |z|) ^ (N + 1)) ≤ Ct k :=
      (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans h
    rw [← le_div_iff₀ hpos] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  have hRb := hRem R hR j hj y z hyy hz
  have hsumb : ‖∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ (k + 1) * ∫ ξ, T k ξ‖ ≤
      S * ((5 / 3 : ℝ) ^ (N + 1) * ((y + |z|) ^ (N + 1))⁻¹) := by
    refine (norm_sum_le _ _).trans ?_
    rw [hS, Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hTb k
  have harith := c09_aux_sf_arith p hp M hM N hNM y z hyy
  calc ‖(∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ (k + 1) * ∫ ξ, T k ξ) +
        (-1 : ℂ) ^ (N + 1) * ∫ ξ, Rm ξ‖
      ≤ ‖∑ k ∈ Finset.range (N + 1), (-1 : ℂ) ^ (k + 1) * ∫ ξ, T k ξ‖ + ‖∫ ξ, Rm ξ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ S * ((5 / 3 : ℝ) ^ (N + 1) * ((y + |z|) ^ (N + 1))⁻¹) + Cr * ((y + |z|) ^ (N + 1))⁻¹ :=
        add_le_add hsumb hRb
    _ = ((5 / 3 : ℝ) ^ (N + 1) * S + Cr) * ((y + |z|) ^ (N + 1))⁻¹ := by ring
    _ ≤ ((5 / 3 : ℝ) ^ (N + 1) * S + Cr) * (ys ^ (2 * M - (N + 1)) * (1 + 1 / ys) ^ (2 * M) *
          (jb y ^ (-M) * (jb y + |z|) ^ (-M))) := by gcongr
    _ ≤ Cfin * jb y ^ (-M) * (jb y + |z|) ^ (-M) := by
        have hX : 0 ≤ jb y ^ (-M) * (jb y + |z|) ^ (-M) := by
          have : 0 < jb y + |z| := by have := abs_nonneg z; linarith
          positivity
        rw [hCfin]
        have : 0 ≤ ((5 / 3 : ℝ) ^ (N + 1) * S + Cr) * (ys ^ (2 * M - (N + 1)) * (1 + 1 / ys) ^ (2 * M)) := by
          positivity
        nlinarith

/-- Blueprint: prop:linear_stationary.  The stationary kernel vanishes unless `y ≥ (50/51)^p`,
and satisfies the near bound for `z ≥ y/4` and the far bound (any `M`) for `z < y/4`. -/
theorem linear_stationary (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ,
      c09_stationary_split_kernel_s p R j y z ≠ 0 → (50 / 51 : ℝ) ^ p ≤ y) ∧
    (∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ, (1 / 4) * y ≤ z →
      ‖c09_stationary_split_kernel_s p R j y z‖ ≤
        C * jb y ^ ((j : ℝ) / p - (p + 3) / (2 * p)) * jb z ^ ((1 - p) / (2 * p))) ∧
    (∀ M : ℝ, 0 ≤ M → ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ,
      z < (1 / 4) * y →
      ‖c09_stationary_split_kernel_s p R j y z‖ ≤ C * jb y ^ (-M) * (jb y + |z|) ^ (-M)) := by
  obtain ⟨cstar, -, -, C, -, -, -, -, -, -, -, -, -, -, h5⟩ := c09_cutoff_bounds p hp hp1
  have hvan : ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ,
      c09_stationary_split_kernel_s p R j y z ≠ 0 → (50 / 51 : ℝ) ^ p ≤ y := by
    intro R hR j hj y z hK
    by_contra hy
    apply hK
    unfold c09_stationary_split_kernel_s
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ))]
    · simp
    · intro ξ hξ
      have hξ1 : 1 ≤ ξ := by
        rw [Set.uIcc_of_le (by linarith)] at hξ; exact hξ.1
      have : c09_stationary_split_amp_s p R j y ξ = 0 := by
        by_contra hne
        exact hy (h5 R hR j hj y ξ (by linarith) hne).1
      simp [this]
  have hpos : 0 < (50 / 51 : ℝ) ^ p := by positivity
  refine ⟨hvan, ?_, ?_⟩
  · obtain ⟨C, hC, hnear⟩ := c09_stationary_near p hp hp1
    refine ⟨C, hC, fun R hR j hj y z hz => ?_⟩
    by_cases hy : 0 < y
    · exact hnear R hR j hj y z hy (by linarith)
    · have : c09_stationary_split_kernel_s p R j y z = 0 := by
        by_contra hne; have := hvan R hR j hj y z hne; linarith
      rw [this, norm_zero]
      have := c09_aux_jb_pos y; have := c09_aux_jb_pos z
      positivity
  · intro M hM
    obtain ⟨C, hC, hfar⟩ := c09_stationary_far p hp hp1 M hM
    refine ⟨C, hC, fun R hR j hj y z hz => ?_⟩
    by_cases hy : 0 < y
    · exact hfar R hR j hj y z hy (by linarith)
    · have : c09_stationary_split_kernel_s p R j y z = 0 := by
        by_contra hne; have := hvan R hR j hj y z hne; linarith
      rw [this, norm_zero]
      have := c09_aux_jb_pos y
      have : 0 ≤ jb y + |z| := by positivity
      positivity

/-! ### Nonstationary part: symbol expansion -/

/-- Symbol bounds for `m_{j,k}`. -/
theorem c09_aux_m_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (j : ℕ) (hj : j ≤ 2) (k : ℕ) :
    ∀ N : ℕ, ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ → ∀ ℓ ≤ N,
      ‖iteratedDeriv ℓ (linear_nonstationary_symbol_expansion_m p R j y k) ξ‖ ≤
        C * ((|y| + ξ ^ p) ^ (k + 1))⁻¹ * ξ ^ (((j : ℝ) - 2 - k) - ℓ) := by
  have hp0 : 0 < p := by linarith
  induction k with
  | zero =>
    intro N
    obtain ⟨A, hA, hAb⟩ := c09_aux_ans_bounds p hp hp1 j hj N
    obtain ⟨Cg, hCg, hm⟩ := c09_aux_mul_psi p hp0 _ (c09_aux_cs_pos p hp0) N
    refine ⟨2 ^ N * A * Cg, by positivity, fun R hR y ξ hξ ℓ hℓ => ?_⟩
    have hξp := Real.rpow_pos_of_pos hξ p
    by_cases hs : ξ ∈ tsupport (c09_aux_ans p R j y)
    · obtain ⟨-, hg⟩ := c09_aux_ans_tsupport p hp0 R (by linarith) j y ξ hs
      have hans := (c09_aux_m_smooth p hp0 R hR j y 0)
      have hsmA : ContDiffAt ℝ ∞ (c09_aux_ans p R j y) ξ := by
        have := ((c09_aux_amp_smooth R j).mul
          (Complex.ofRealCLM.contDiff.comp (c09_aux_chi_ns_smooth p y)).contDiffOn) ξ hξ
        refine (this.contDiffAt (isOpen_Ioi.mem_nhds hξ)).congr_of_eventuallyEq ?_
        exact Eventually.of_forall fun x => by
          simp only [c09_aux_ans, c09_stationary_split_amp_ns, Function.comp,
            Complex.ofRealCLM_apply]; ring
      rw [c09_aux_m0_eq]
      refine (hm y ξ hξ hg (fun x => -Complex.I * c09_stationary_split_amp_ns p R j y x) A
        ((j : ℝ) - 2) hA.le (contDiffAt_const.mul hsmA) (fun i hi => ?_) ℓ hℓ).trans
        (le_of_eq ?_)
      · rw [iteratedDeriv_const_mul _ (hsmA.of_le (by exact_mod_cast le_top)), norm_mul,
          norm_neg, Complex.norm_I, one_mul]
        exact hAb R hR y ξ hξ i hi
      · simp
    · rw [(c09_aux_m_vanish p R j y 0 ξ hs).iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simp <;> positivity
  | succ k ih =>
    intro N
    obtain ⟨C, hC, hCb⟩ := ih (N + 1)
    obtain ⟨Cg, hCg, hm⟩ := c09_aux_mul_psi p hp0 _ (c09_aux_cs_pos p hp0) N
    refine ⟨2 ^ N * C * Cg, by positivity, fun R hR y ξ hξ ℓ hℓ => ?_⟩
    have hξp := Real.rpow_pos_of_pos hξ p
    have hW : 0 < |y| + ξ ^ p := by positivity
    by_cases hs : ξ ∈ tsupport (c09_aux_ans p R j y)
    · obtain ⟨-, hg⟩ := c09_aux_ans_tsupport p hp0 R (by linarith) j y ξ hs
      have hd := ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp
        (c09_aux_m_smooth p hp0 R hR j y k)).2
      have hdA : ContDiffAt ℝ ∞ (deriv (linear_nonstationary_symbol_expansion_m p R j y k)) ξ :=
        (hd ξ hξ).contDiffAt (isOpen_Ioi.mem_nhds hξ)
      rw [c09_aux_msucc_eq]
      refine (hm y ξ hξ hg (fun x => Complex.I *
        deriv (linear_nonstationary_symbol_expansion_m p R j y k) x)
        (C * ((|y| + ξ ^ p) ^ (k + 1))⁻¹) ((j : ℝ) - 2 - (k + 1 : ℕ)) (by positivity)
        (contDiffAt_const.mul hdA) (fun i hi => ?_) ℓ hℓ).trans (le_of_eq ?_)
      · rw [iteratedDeriv_const_mul _ (hdA.of_le (by exact_mod_cast le_top)), norm_mul,
          Complex.norm_I, one_mul, ← iteratedDeriv_succ']
        refine (hCb R hR y ξ hξ (i + 1) (by omega)).trans (le_of_eq ?_)
        congr 2; push_cast; ring
      · rw [pow_succ _ (k + 1), mul_inv]; ring
    · rw [(c09_aux_m_vanish p R j y (k + 1) ξ hs).iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simp <;> positivity

/-- Explicit form of `m_{j,0}` for `ξ > 0`. -/
theorem c09_aux_m0_formula (p R : ℝ) (j : ℕ) (y x : ℝ) (hx : 0 < x) :
    linear_nonstationary_symbol_expansion_m p R j y 0 x = Complex.I ^ j *
      (((1 - rho x) * c09_stationary_split_chi_ns p y x * c09_truncation_theta R x *
        x ^ ((j : ℝ) - 2) / (2 * π) * (y - x ^ p)⁻¹ : ℝ) : ℂ) := by
  simp only [linear_nonstationary_symbol_expansion_m, c09_stationary_split_amp_ns,
    c09_positive_kernel_amp, hx, ↓reduceIte]
  by_cases h0 : y - x ^ p = 0
  · rw [h0]; simp
  · have h0' : ((y - x ^ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
    have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by
      have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
    push_cast at h0' hπ ⊢
    field_simp
    rw [pow_succ]
    ring_nf

/-- `m_{j,0}` vanishes on `ξ ≤ 0`. -/
theorem c09_aux_m0_nonpos (p R : ℝ) (j : ℕ) (y x : ℝ) (hx : x ≤ 0) :
    linear_nonstationary_symbol_expansion_m p R j y 0 x = 0 := by
  simp [linear_nonstationary_symbol_expansion_m, c09_stationary_split_amp_ns,
    c09_positive_kernel_amp, not_lt.mpr hx]

/-- Reality: `m_{j,k} = i^{j+k} r` with `r` real. -/
theorem c09_aux_m_real (p R : ℝ) (j : ℕ) (y : ℝ) (k : ℕ) :
    ∃ r : ℝ → ℝ, linear_nonstationary_symbol_expansion_m p R j y k =
      fun x => Complex.I ^ (j + k) * ((r x : ℝ) : ℂ) := by
  induction k with
  | zero =>
    refine ⟨fun x => if 0 < x then (1 - rho x) * c09_stationary_split_chi_ns p y x *
      c09_truncation_theta R x * x ^ ((j : ℝ) - 2) / (2 * π) * (y - x ^ p)⁻¹ else 0, ?_⟩
    funext x
    rcases lt_or_ge 0 x with hx | hx
    · rw [c09_aux_m0_formula p R j y x hx]; simp [hx]
    · rw [c09_aux_m0_nonpos p R j y x hx]; simp [not_lt.mpr hx]
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨fun x => deriv r x * (y - x ^ p)⁻¹, ?_⟩
    rw [c09_aux_msucc_eq, hr]
    funext x
    have : deriv (fun x => Complex.I ^ (j + k) * ((r x : ℝ) : ℂ)) x =
        Complex.I ^ (j + k) * ((deriv r x : ℝ) : ℂ) := by
      rw [deriv_const_mul_field, c09_aux_deriv_ofReal]
    rw [this]; push_cast; ring

/-- Blueprint: lem:c09_mjk_bounds.  Symbol-class bounds
`|∂_ξ^ℓ m_{j,k}^R(y,ξ)| ≤ C ξ^{j-2-k-ℓ}(|y|+ξ^p)^{-k-1}`, reality of `i^{-(j+k)} m_{j,k}^R`,
`m_{j,0}^R = (iξ)^j m_{0,0}^R`, and explicit formulas for `m_{2,1}^R`, `ξ m_{1,1}^R`. -/
theorem c09_mjk_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ j : ℕ, j ≤ 2 → ∀ k ℓ : ℕ, ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ →
      ‖iteratedDeriv ℓ (linear_nonstationary_symbol_expansion_m p R j y k) ξ‖ ≤
        C * ξ ^ ((j : ℝ) - 2 - k - ℓ) * (|y| + ξ ^ p) ^ (-(k : ℝ) - 1)) ∧
    (∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ k : ℕ, ∀ y ξ : ℝ,
      ((Complex.I ^ (j + k))⁻¹ * linear_nonstationary_symbol_expansion_m p R j y k ξ).im = 0) ∧
    (∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y ξ : ℝ, 0 < ξ →
      linear_nonstationary_symbol_expansion_m p R j y 0 ξ =
        (Complex.I * (ξ : ℂ)) ^ j * linear_nonstationary_symbol_expansion_m p R 0 y 0 ξ) ∧
    (∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ →
      let b : ℝ → ℝ := fun ξ =>
        (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ
      linear_nonstationary_symbol_expansion_m p R 2 y 1 ξ =
        -(Complex.I / ((2 * π : ℝ) : ℂ)) *
          ((deriv b ξ / (y - ξ ^ p) ^ 2 + p * b ξ * ξ ^ (p - 1) / (y - ξ ^ p) ^ 3 : ℝ) : ℂ) ∧
      (ξ : ℂ) * linear_nonstationary_symbol_expansion_m p R 1 y 1 ξ =
        -Complex.I * linear_nonstationary_symbol_expansion_m p R 2 y 1 ξ +
          ((b ξ / (2 * π * ξ * (y - ξ ^ p) ^ 2) : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj k ℓ
    obtain ⟨C, hC, hb⟩ := c09_aux_m_bounds p hp hp1 j hj k ℓ
    refine ⟨C, hC, fun R hR y ξ hξ => (hb R hR y ξ hξ ℓ le_rfl).trans (le_of_eq ?_)⟩
    have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ p; positivity
    rw [show -(k : ℝ) - 1 = -((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hW.le,
      Real.rpow_natCast]
    ring
  · intro R hR j hj k y ξ
    obtain ⟨r, hr⟩ := c09_aux_m_real p R j y k
    rw [hr]
    simp only
    rw [inv_mul_cancel_left₀ (pow_ne_zero _ Complex.I_ne_zero), Complex.ofReal_im]
  · intro R hR j hj y ξ hξ
    rw [c09_aux_m0_formula p R j y ξ hξ, c09_aux_m0_formula p R 0 y ξ hξ]
    have e : ξ ^ ((j : ℝ) - 2) = ξ ^ j * ξ ^ (((0 : ℕ) : ℝ) - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hξ]; congr 1; push_cast; ring
    rw [e]; push_cast; ring
  · intro R hR y ξ hξ b
    have hbs : ContDiff ℝ ∞ b :=
      ((contDiff_const.sub c09_aux_cut_R1).mul (c09_aux_chi_ns_smooth p y)).mul
        (c09_aux_theta_smooth R)
    have hbd : HasDerivAt b (deriv b ξ) ξ := (hbs.differentiable (by simp) ξ).hasDerivAt
    by_cases h0 : y - ξ ^ p = 0
    · have e1 : linear_nonstationary_symbol_expansion_m p R 2 y 1 ξ = 0 := by
        rw [c09_aux_msucc_eq]; simp [h0]
      have e2 : linear_nonstationary_symbol_expansion_m p R 1 y 1 ξ = 0 := by
        rw [c09_aux_msucc_eq]; simp [h0]
      rw [e1, e2, h0]; simp
    have hψd : HasDerivAt (fun x : ℝ => (y - x ^ p)⁻¹) (p * ξ ^ (p - 1) / (y - ξ ^ p) ^ 2) ξ := by
      have h1 : HasDerivAt (fun x : ℝ => y - x ^ p) (-(p * ξ ^ (p - 1))) ξ := by
        simpa using (Real.hasDerivAt_rpow_const (p := p) (Or.inl hξ.ne')).const_sub y
      convert h1.fun_inv h0 using 1; ring
    -- `m_{2,0}`
    have hev2 : linear_nonstationary_symbol_expansion_m p R 2 y 0 =ᶠ[𝓝 ξ]
        fun x => Complex.I ^ 2 * (((b x / (2 * π)) * (y - x ^ p)⁻¹ : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hξ] with x hx
      rw [c09_aux_m0_formula p R 2 y x hx]
      congr 2
      simp only [b, Nat.cast_ofNat, sub_self, Real.rpow_zero, mul_one]
    have hd2 : HasDerivAt (linear_nonstationary_symbol_expansion_m p R 2 y 0)
        (Complex.I ^ 2 * (((deriv b ξ / (2 * π)) * (y - ξ ^ p)⁻¹ +
          b ξ / (2 * π) * (p * ξ ^ (p - 1) / (y - ξ ^ p) ^ 2) : ℝ) : ℂ)) ξ :=
      (((hbd.div_const (2 * π)).mul hψd).ofReal_comp.const_mul _).congr_of_eventuallyEq hev2
    -- `m_{1,0}`
    have hev1 : linear_nonstationary_symbol_expansion_m p R 1 y 0 =ᶠ[𝓝 ξ]
        fun x => Complex.I ^ 1 * (((b x * x⁻¹ / (2 * π)) * (y - x ^ p)⁻¹ : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds hξ] with x hx
      rw [c09_aux_m0_formula p R 1 y x hx]
      congr 2
      rw [show ((1 : ℕ) : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
    have hd1 : HasDerivAt (linear_nonstationary_symbol_expansion_m p R 1 y 0)
        (Complex.I ^ 1 * ((((deriv b ξ * ξ⁻¹ + b ξ * (-(ξ ^ 2)⁻¹)) / (2 * π)) * (y - ξ ^ p)⁻¹ +
          b ξ * ξ⁻¹ / (2 * π) * (p * ξ ^ (p - 1) / (y - ξ ^ p) ^ 2) : ℝ) : ℂ)) ξ :=
      ((((hbd.mul (hasDerivAt_inv hξ.ne')).div_const (2 * π)).mul hψd).ofReal_comp.const_mul
        _).congr_of_eventuallyEq hev1
    have hπ : π ≠ 0 := Real.pi_ne_zero
    set db := deriv b ξ with hdb
    set bξ := b ξ with hbξ
    set ψ := y - ξ ^ p with hψ
    have e2 : linear_nonstationary_symbol_expansion_m p R 2 y 1 ξ =
        -(Complex.I / ((2 * π : ℝ) : ℂ)) *
          ((db / ψ ^ 2 + p * bξ * ξ ^ (p - 1) / ψ ^ 3 : ℝ) : ℂ) := by
      rw [c09_aux_msucc_eq]; simp only; rw [hd2.deriv]
      set A := (db / (2 * π)) * ψ⁻¹ + bξ / (2 * π) * (p * ξ ^ (p - 1) / ψ ^ 2) with hA
      have hA' : A * ψ⁻¹ = (db / ψ ^ 2 + p * bξ * ξ ^ (p - 1) / ψ ^ 3) / (2 * π) := by
        rw [hA]; field_simp
      calc Complex.I * (Complex.I ^ 2 * (A : ℂ)) * ((ψ⁻¹ : ℝ) : ℂ)
          = -Complex.I * (((A * ψ⁻¹) : ℝ) : ℂ) := by
            rw [Complex.ofReal_mul]
            linear_combination (Complex.I * (A : ℂ) * ((ψ⁻¹ : ℝ) : ℂ)) * Complex.I_sq
        _ = _ := by rw [hA', Complex.ofReal_div]; ring
    refine ⟨e2, ?_⟩
    rw [c09_aux_msucc_eq, e2]; simp only; rw [hd1.deriv]
    set A1 := ((db * ξ⁻¹ + bξ * (-(ξ ^ 2)⁻¹)) / (2 * π)) * ψ⁻¹ +
      bξ * ξ⁻¹ / (2 * π) * (p * ξ ^ (p - 1) / ψ ^ 2) with hA1
    set B := db / ψ ^ 2 + p * bξ * ξ ^ (p - 1) / ψ ^ 3 with hB
    have hreal : -(ξ * (A1 * ψ⁻¹)) = -(B / (2 * π)) + bξ / (2 * π * ξ * ψ ^ 2) := by
      rw [hA1, hB]; field_simp; ring
    calc (ξ : ℂ) * (Complex.I * (Complex.I ^ 1 * (A1 : ℂ)) * ((ψ⁻¹ : ℝ) : ℂ))
        = ((-(ξ * (A1 * ψ⁻¹)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_mul]
          linear_combination ((ξ : ℂ) * (A1 : ℂ) * ((ψ⁻¹ : ℝ) : ℂ)) * Complex.I_sq
      _ = (((-(B / (2 * π)) + bξ / (2 * π * ξ * ψ ^ 2)) : ℝ) : ℂ) := by rw [hreal]
      _ = _ := by
          rw [Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_div (B)]
          linear_combination (-((B : ℂ) / ((2 * π : ℝ) : ℂ))) * Complex.I_sq

/-! ### Nonstationary part: leading kernels -/

/-! #### Helpers for the nonstationary symbol expansion -/

/-- `a_j^{ns,R}(y,·)` vanishes off `(1, 2R)`. -/
theorem c09_aux_nse_ans_zero (p R : ℝ) (hR : 0 < R) (j : ℕ) (y ξ : ℝ) (hξ : ξ ≤ 1 ∨ 2 * R ≤ ξ) :
    c09_aux_ans p R j y ξ = 0 := by
  show c09_stationary_split_amp_ns p R j y ξ = 0
  unfold c09_stationary_split_amp_ns
  rcases hξ with h | h
  · rw [c09_aux_amp_zero_of_le_one R j ξ h, mul_zero]
  · have : c09_positive_kernel_amp R j ξ = 0 := by
      unfold c09_positive_kernel_amp
      split_ifs with h0
      · rw [c09_aux_theta_zero R ξ hR (by rw [abs_of_pos h0]; exact h)]; simp
      · rfl
    rw [this, mul_zero]

/-- Points `ξ < 1` or `ξ > 2R` are outside `tsupport a_j^{ns,R}(y,·)`. -/
theorem c09_aux_nse_not_tsupport (p R : ℝ) (hR : 0 < R) (j : ℕ) (y ξ : ℝ)
    (hξ : ξ < 1 ∨ 2 * R < ξ) : ξ ∉ tsupport (c09_aux_ans p R j y) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  rcases hξ with h | h
  · filter_upwards [isOpen_Iio.mem_nhds (show ξ ∈ Iio (1 : ℝ) from h)] with x hx
    exact c09_aux_nse_ans_zero p R hR j y x (Or.inl (le_of_lt hx))
  · filter_upwards [isOpen_Ioi.mem_nhds (show ξ ∈ Ioi (2 * R) from h)] with x hx
    exact c09_aux_nse_ans_zero p R hR j y x (Or.inr (le_of_lt hx))

/-- `m_{j,k}^R(y,·)` is smooth on all of `ℝ`. -/
theorem c09_aux_nse_m_contDiff (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (y : ℝ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (linear_nonstationary_symbol_expansion_m p R j y k) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hs : ξ ∈ tsupport (c09_aux_ans p R j y)
  · have h1 := (c09_aux_ans_tsupport p hp R (by linarith) j y ξ hs).1
    exact ((c09_aux_m_smooth p hp R hR j y k).of_le (by exact_mod_cast le_top)).contDiffAt
      (isOpen_Ioi.mem_nhds (show ξ ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith))
  · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (c09_aux_m_vanish p R j y k ξ hs)

/-- `m_{j,k}^R(y,ξ) = 0` for `ξ ≤ 1` or `ξ ≥ 2R`. -/
theorem c09_aux_nse_m_zero (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (y : ℝ) (k : ℕ)
    (ξ : ℝ) (hξ : ξ ≤ 1 ∨ 2 * R ≤ ξ) : linear_nonstationary_symbol_expansion_m p R j y k ξ = 0 := by
  have hR0 : 0 < R := by linarith
  set m := linear_nonstationary_symbol_expansion_m p R j y k with hm
  have hc : Continuous m := (c09_aux_nse_m_contDiff p hp R hR j y k).continuous
  have hz : ∀ x, (x < 1 ∨ 2 * R < x) → m x = 0 := fun x hx =>
    (c09_aux_m_vanish p R j y k x (c09_aux_nse_not_tsupport p R hR0 j y x hx)).eq_of_nhds
  rcases hξ with h | h
  · rcases lt_or_eq_of_le h with h | h
    · exact hz ξ (Or.inl h)
    · subst h
      have t1 : Tendsto m (𝓝[<] (1 : ℝ)) (𝓝 (m 1)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have t2 : Tendsto m (𝓝[<] (1 : ℝ)) (𝓝 0) := tendsto_const_nhds.congr'
        (eventually_nhdsWithin_of_forall fun x hx => (hz x (Or.inl hx)).symm)
      exact tendsto_nhds_unique t1 t2
  · rcases lt_or_eq_of_le h with h | h
    · exact hz ξ (Or.inr h)
    · subst h
      have t1 : Tendsto m (𝓝[>] (2 * R)) (𝓝 (m (2 * R))) :=
        hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have t2 : Tendsto m (𝓝[>] (2 * R)) (𝓝 0) := tendsto_const_nhds.congr'
        (eventually_nhdsWithin_of_forall fun x hx => (hz x (Or.inr hx)).symm)
      exact tendsto_nhds_unique t1 t2

/-- `a_j^{ns,R} = m_{j,0} · i(y - ξ^p)` for `ξ > 0`. -/
theorem c09_aux_nse_a_eq (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (y ξ : ℝ) (hξ : 0 < ξ) :
    c09_stationary_split_amp_ns p R j y ξ =
      linear_nonstationary_symbol_expansion_m p R j y 0 ξ * (Complex.I * ((y - ξ ^ p : ℝ) : ℂ)) := by
  by_cases h : y - ξ ^ p = 0
  · have hs : ξ ∉ tsupport (c09_aux_ans p R j y) := by
      intro hs
      obtain ⟨-, hg⟩ := c09_aux_ans_tsupport p hp R (by linarith) j y ξ hs
      rw [h, abs_zero] at hg
      have := c09_aux_cs_pos p hp
      have := Real.rpow_pos_of_pos hξ p
      nlinarith [abs_nonneg y]
    rw [h]; simp only [Complex.ofReal_zero, mul_zero]
    exact image_eq_zero_of_notMem_tsupport hs
  · show _ = (c09_stationary_split_amp_ns p R j y ξ / (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))) * _
    have : Complex.I * ((y - ξ ^ p : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast h)
    exact (div_mul_cancel₀ _ this).symm

/-- `-∂_ξ m_{j,k} = m_{j,k+1} · i(y - ξ^p)` for `ξ > 0`. -/
theorem c09_aux_nse_dm_eq (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (y ξ : ℝ) (hξ : 0 < ξ)
    (k : ℕ) :
    -deriv (linear_nonstationary_symbol_expansion_m p R j y k) ξ =
      linear_nonstationary_symbol_expansion_m p R j y (k + 1) ξ *
        (Complex.I * ((y - ξ ^ p : ℝ) : ℂ)) := by
  by_cases h : y - ξ ^ p = 0
  · have hs : ξ ∉ tsupport (c09_aux_ans p R j y) := by
      intro hs
      obtain ⟨-, hg⟩ := c09_aux_ans_tsupport p hp R (by linarith) j y ξ hs
      rw [h, abs_zero] at hg
      have := c09_aux_cs_pos p hp
      have := Real.rpow_pos_of_pos hξ p
      nlinarith [abs_nonneg y]
    rw [h]; simp only [Complex.ofReal_zero, mul_zero, neg_eq_zero]
    exact (c09_aux_m_vanish p R j y k ξ hs).deriv_eq.trans (by simp)
  · show _ = (-deriv (linear_nonstationary_symbol_expansion_m p R j y k) ξ /
      (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))) * _
    have : Complex.I * ((y - ξ ^ p : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast h)
    exact (div_mul_cancel₀ _ this).symm

/-- Derivative of `e^{iΘ_y}`, `Θ_y(ξ) = yξ - Φ₀(ξ)`, for `ξ > 0`. -/
theorem c09_aux_nse_eTheta_deriv (p : ℝ) (hp : 0 < p) (y ξ : ℝ) (hξ : 0 < ξ) :
    HasDerivAt (fun x : ℝ => Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)))
      (Complex.I * ((y - ξ ^ p : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ))) ξ := by
  have h := (c09_aux_phase_deriv p hp y ξ hξ).neg
  have hΘ : HasDerivAt (fun x => y * x - Phi0 p x) (y - ξ ^ p) ξ := by
    convert h using 1
    · funext x; simp only [Pi.neg_apply, c09_tail_integral_phase]; ring
    · ring
  have := (hΘ.ofReal_comp.const_mul Complex.I).cexp
  convert this using 1
  ring

/-- One integration by parts step on `[1,b]` against a `C¹` factor `F`. -/
theorem c09_aux_nse_step (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 2 ≤ R) (y : ℝ) (j k : ℕ) (b : ℝ)
    (hb : 1 ≤ b) (F F' : ℝ → ℂ) (hF : ∀ x, HasDerivAt F (F' x) x) (hF'c : Continuous F') :
    ∫ x in (1 : ℝ)..b, (linear_nonstationary_symbol_expansion_m p R j y k x *
        (Complex.I * ((y - x ^ p : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * F x =
      linear_nonstationary_symbol_expansion_m p R j y k b *
          Complex.exp (Complex.I * ((y * b - Phi0 p b : ℝ) : ℂ)) * F b -
        (∫ x in (1 : ℝ)..b, linear_nonstationary_symbol_expansion_m p R j y k x *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * F' x) -
        ∫ x in (1 : ℝ)..b, deriv (linear_nonstationary_symbol_expansion_m p R j y k) x *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * F x := by
  set m := linear_nonstationary_symbol_expansion_m p R j y k with hm
  set e : ℝ → ℂ := fun x => Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) with he
  have hms := c09_aux_nse_m_contDiff p hp R hR j y k
  have hmc : Continuous m := hms.continuous
  have hdmc : Continuous (deriv m) := hms.continuous_deriv (by exact_mod_cast le_top)
  have hPhi := c09_aux_Phi0_continuous p hp
  have hec : Continuous e := by
    simp only [he]
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).sub hPhi))).cexp
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have hpc : Continuous fun x : ℝ => x ^ p := Real.continuous_rpow_const hp.le
  have hwc : Continuous fun x : ℝ => Complex.I * ((y - x ^ p : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.sub hpc))
  have hm1 : m 1 = 0 := c09_aux_nse_m_zero p hp R hR j y k 1 (Or.inl le_rfl)
  have hIcc : ∀ x ∈ uIcc (1 : ℝ) b, 0 < x := by
    intro x hx; rw [uIcc_of_le hb] at hx; linarith [hx.1]
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (b := b)
    (u := m) (u' := deriv m) (v := fun x => e x * F x)
    (v' := fun x => Complex.I * ((y - x ^ p : ℝ) : ℂ) * e x * F x + e x * F' x)
    (fun x _ => (hms.differentiable (by simp) x).hasDerivAt)
    (fun x hx => (c09_aux_nse_eTheta_deriv p hp y x (hIcc x hx)).mul (hF x))
    (hdmc.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (μ := volume)
      (u := fun x => Complex.I * ((y - x ^ p : ℝ) : ℂ) * e x * F x + e x * F' x)
      (((hwc.mul hec).mul hFc).add (hec.mul hF'c)) _ _)
  have hsplit : ∫ x in (1 : ℝ)..b, m x * (Complex.I * ((y - x ^ p : ℝ) : ℂ) * e x * F x + e x * F' x) =
      (∫ x in (1 : ℝ)..b, (m x * (Complex.I * ((y - x ^ p : ℝ) : ℂ))) * e x * F x) +
        ∫ x in (1 : ℝ)..b, m x * e x * F' x := by
    have i1 : IntervalIntegrable (fun x => m x * (Complex.I * ((y - x ^ p : ℝ) : ℂ)) * e x * F x)
        volume 1 b := (((hmc.mul hwc).mul hec).mul hFc).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => m x * e x * F' x) volume 1 b :=
      ((hmc.mul hec).mul hF'c).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add i1 i2]
    congr 1; funext x; ring
  rw [hsplit, hm1] at hibp
  have : ∫ x in (1 : ℝ)..b, deriv m x * (e x * F x) = ∫ x in (1 : ℝ)..b, deriv m x * e x * F x := by
    congr 1; funext x; ring
  rw [this] at hibp
  linear_combination hibp

/-- Part (1) of the nonstationary symbol expansion. -/
theorem c09_aux_nse_part1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (R : ℝ) (hR : 2 ≤ R) (y : ℝ) (j : ℕ) : ∀ η : ℝ, 1 ≤ η → ∀ n : ℕ,
      ∫ ξ in (1 : ℝ)..η, c09_stationary_split_amp_ns p R j y ξ *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((y * η - Phi0 p η : ℝ) : ℂ)) *
            (∑ k ∈ Finset.range (n + 1), linear_nonstationary_symbol_expansion_m p R j y k η) -
          ∫ ξ in (1 : ℝ)..η, Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) *
            deriv (linear_nonstationary_symbol_expansion_m p R j y n) ξ := by
  have hp0 : 0 < p := by linarith
  have hR0 : 0 < R := by linarith
  have hPhi := c09_aux_Phi0_continuous p hp0
  have hec : Continuous fun x : ℝ => Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).sub hPhi))).cexp
  have hms := fun k => c09_aux_nse_m_contDiff p hp0 R hR j y k
  intro η hη
  have hpos : ∀ x ∈ uIcc (1 : ℝ) η, 0 < x := by
    intro x hx; rw [uIcc_of_le hη] at hx; linarith [hx.1]
  have step : ∀ k, ∫ ξ in (1 : ℝ)..η, (linear_nonstationary_symbol_expansion_m p R j y k ξ *
        (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) =
      linear_nonstationary_symbol_expansion_m p R j y k η *
        Complex.exp (Complex.I * ((y * η - Phi0 p η : ℝ) : ℂ)) -
      ∫ ξ in (1 : ℝ)..η, Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) *
        deriv (linear_nonstationary_symbol_expansion_m p R j y k) ξ := by
    intro k
    have h := c09_aux_nse_step p hp0 R hR y j k η hη (fun _ => 1) (fun _ => 0)
      (fun x => hasDerivAt_const x 1) continuous_const
    simp only [mul_one, mul_zero, intervalIntegral.integral_zero, sub_zero] at h
    rw [h]; congr 1; congr 1; funext ξ; ring
  intro n
  induction n with
  | zero =>
    have hc : ∫ ξ in (1 : ℝ)..η, c09_stationary_split_amp_ns p R j y ξ *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) =
        ∫ ξ in (1 : ℝ)..η, (linear_nonstationary_symbol_expansion_m p R j y 0 ξ *
          (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) :=
      intervalIntegral.integral_congr fun ξ hξ => by
        rw [c09_aux_nse_a_eq p hp0 R hR j y ξ (hpos ξ hξ)]
    rw [hc, step 0]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]; ring
  | succ n ih =>
    have h2 : ∫ ξ in (1 : ℝ)..η, Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) *
          deriv (linear_nonstationary_symbol_expansion_m p R j y n) ξ =
        -∫ ξ in (1 : ℝ)..η, (linear_nonstationary_symbol_expansion_m p R j y (n + 1) ξ *
          (Complex.I * ((y - ξ ^ p : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun ξ hξ => ?_
      rw [← c09_aux_nse_dm_eq p hp0 R hR j y ξ (hpos ξ hξ) n]; ring
    rw [ih, h2, step (n + 1), Finset.sum_range_succ _ (n + 1)]; ring

/-- Part (2) of the nonstationary symbol expansion. -/
theorem c09_aux_nse_part2 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (R : ℝ) (hR : 2 ≤ R) (y : ℝ) (j : ℕ) : ∀ z, ∀ n : ℕ, c09_stationary_split_kernel_ns p R j y z =
      ((2 * π : ℝ) : ℂ) * (∑ k ∈ Finset.range (n + 1),
          invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) (y - z)) +
        linear_nonstationary_symbol_expansion_remKernel p R j (n + 1) y z := by
  have hp0 : 0 < p := by linarith
  have hR0 : 0 < R := by linarith
  have hPhi := c09_aux_Phi0_continuous p hp0
  have hec : Continuous fun x : ℝ => Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).sub hPhi))).cexp
  have hms := fun k => c09_aux_nse_m_contDiff p hp0 R hR j y k
  -- (2)
  have hEd : ∀ z x, HasDerivAt (c09_tail_integral p z)
      (-Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ))) x :=
    fun z x => c09_aux_tail_deriv p hp0 z x
  have hEc : ∀ z, Continuous fun x => -Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ)) :=
    fun z => (c09_aux_e_cont p hp0 z).neg
  have hfour : ∀ k z, ∫ x in (1 : ℝ)..(2 * R), linear_nonstationary_symbol_expansion_m p R j y k x *
        Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ)) =
      ((2 * π : ℝ) : ℂ) * invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) (y - z) := by
    intro k z
    unfold invFourierT
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)), one_mul]
    have hz : ∀ x ∉ Ioc (1 : ℝ) (2 * R), linear_nonstationary_symbol_expansion_m p R j y k x *
        Complex.exp (Complex.I * ((y - z : ℝ) : ℂ) * (x : ℂ)) = 0 := by
      intro x hx
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
      rw [c09_aux_nse_m_zero p hp0 R hR j y k x (hx.imp id le_of_lt), zero_mul]
    rw [intervalIntegral.integral_of_le (by linarith), ← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    unfold c09_tail_integral_phase; push_cast; ring
  have step2 : ∀ k z, ∫ x in (1 : ℝ)..(2 * R), (linear_nonstationary_symbol_expansion_m p R j y k x *
        (Complex.I * ((y - x ^ p : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * c09_tail_integral p z x =
      ((2 * π : ℝ) : ℂ) * invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) (y - z) -
        ∫ x in (1 : ℝ)..(2 * R), deriv (linear_nonstationary_symbol_expansion_m p R j y k) x *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * c09_tail_integral p z x := by
    intro k z
    rw [c09_aux_nse_step p hp0 R hR y j k (2 * R) (by linarith) _ _ (hEd z) (hEc z),
      c09_aux_nse_m_zero p hp0 R hR j y k (2 * R) (Or.inr le_rfl), ← hfour k z]
    rw [show (∫ x in (1 : ℝ)..(2 * R), linear_nonstationary_symbol_expansion_m p R j y k x *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) *
          -Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ))) =
        -∫ x in (1 : ℝ)..(2 * R), linear_nonstationary_symbol_expansion_m p R j y k x *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (c09_tail_integral_phase p z x : ℂ)) by
      rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring]
    ring
  have hpos2 : ∀ x ∈ uIcc (1 : ℝ) (2 * R), 0 < x := by
    intro x hx; rw [uIcc_of_le (by linarith)] at hx; linarith [hx.1]
  intro z n
  unfold linear_nonstationary_symbol_expansion_remKernel
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero =>
    unfold c09_stationary_split_kernel_ns
    have hc : ∫ x in (1 : ℝ)..(2 * R), c09_stationary_split_amp_ns p R j y x *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * c09_tail_integral p z x =
        ∫ x in (1 : ℝ)..(2 * R), (linear_nonstationary_symbol_expansion_m p R j y 0 x *
          (Complex.I * ((y - x ^ p : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * c09_tail_integral p z x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [c09_aux_nse_a_eq p hp0 R hR j y x (hpos2 x hx)]
    rw [hc, step2 0 z]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]; ring
  | succ n ih =>
    have h2 : -∫ x in (1 : ℝ)..(2 * R), deriv (linear_nonstationary_symbol_expansion_m p R j y n) x *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * c09_tail_integral p z x =
        ∫ x in (1 : ℝ)..(2 * R), (linear_nonstationary_symbol_expansion_m p R j y (n + 1) x *
          (Complex.I * ((y - x ^ p : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * c09_tail_integral p z x := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [← c09_aux_nse_dm_eq p hp0 R hR j y x (hpos2 x hx) n]; ring
    rw [ih, h2, step2 (n + 1) z, Finset.sum_range_succ _ (n + 1)]; ring

/-- Blueprint: lem:linear_nonstationary_symbol_expansion.  Integration-by-parts expansion of
`∫ a_j^{ns,R} e^{iΘ_y}`, of the kernel `K_{+,j}^{ns,R}` and of the operator `𝒯_{+,j}^{ns,R}`. -/
theorem linear_nonstationary_symbol_expansion (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (R : ℝ) (hR : 2 ≤ R) (y : ℝ) (j : ℕ) (hj : j ≤ 2) (M : ℕ) (hM : 1 ≤ M) :
    -- (1)
    (∀ η : ℝ, 1 ≤ η →
      ∫ ξ in (1 : ℝ)..η, c09_stationary_split_amp_ns p R j y ξ *
          Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((y * η - Phi0 p η : ℝ) : ℂ)) *
            (∑ k ∈ Finset.range M, linear_nonstationary_symbol_expansion_m p R j y k η) -
          ∫ ξ in (1 : ℝ)..η, Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) *
            deriv (linear_nonstationary_symbol_expansion_m p R j y (M - 1)) ξ) ∧
    -- (2)
    (∀ z : ℝ, c09_stationary_split_kernel_ns p R j y z =
      ((2 * π : ℝ) : ℂ) * (∑ k ∈ Finset.range M,
          invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) (y - z)) +
        linear_nonstationary_symbol_expansion_remKernel p R j M y z) ∧
    -- (3)
    (∀ γ, admissibleGamma p γ → ∀ G ∈ Y_gamma_tilde p γ,
      Integrable (fun z => c09_stationary_split_kernel_ns p R j y z * ((deriv G z : ℝ) : ℂ)) ∧
      Integrable (fun z => linear_nonstationary_symbol_expansion_remKernel p R j M y z *
        ((deriv G z : ℝ) : ℂ)) ∧
      (∀ k < M, Integrable (fun w =>
        invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w * ((deriv G (y - w) : ℝ) : ℂ))) ∧
      c09_stationary_split_op_ns p R j G y =
        ((2 * π : ℝ) : ℂ) * (∑ k ∈ Finset.range M, ∫ w,
            invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w *
              ((deriv G (y - w) : ℝ) : ℂ)) +
          linear_nonstationary_symbol_expansion_remOp p R j M G y) := by
  have hp0 : 0 < p := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hPhi := c09_aux_Phi0_continuous p hp0
  have hec : Continuous fun x : ℝ => Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).sub hPhi))).cexp
  have hms := fun k => c09_aux_nse_m_contDiff p hp0 R hR j y k
  have part2 := c09_aux_nse_part2 p hp hp1 R hR y j
  refine ⟨fun η hη => c09_aux_nse_part1 p hp hp1 R hR y j η hη n, fun z => part2 z n,
    fun γ hγ G hG => ?_⟩
  -- (3)
  obtain ⟨-, -, -, ⟨CW, hCW, hW⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
  obtain ⟨-, hGi, hGw, -⟩ := hW G hG.1
  obtain ⟨-, -, -, -, ⟨CE, hCE, hE⟩, -⟩ := c09_tail_basic p hp hp1
  have hgi : Integrable (fun z => ((deriv G z : ℝ) : ℂ)) := hGi.ofReal
  have hgm : AEStronglyMeasurable (fun z => ((deriv G z : ℝ) : ℂ)) := hgi.aestronglyMeasurable
  -- the symbols are integrable, their inverse transforms bounded and continuous
  have hmsupp : ∀ k, HasCompactSupport (linear_nonstationary_symbol_expansion_m p R j y k) := by
    intro k
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2 * R)) fun x hx => ?_
    simp only [mem_Icc, not_and_or, not_le] at hx
    exact c09_aux_nse_m_zero p hp0 R hR j y k x (hx.imp le_of_lt le_of_lt)
  have hmi : ∀ k, Integrable (linear_nonstationary_symbol_expansion_m p R j y k) := fun k =>
    (hms k).continuous.integrable_of_hasCompactSupport (hmsupp k)
  have hTk : ∀ k, Integrable (fun z => invFourierT (linear_nonstationary_symbol_expansion_m p R j y k)
      (y - z) * ((deriv G z : ℝ) : ℂ)) := by
    intro k
    refine hgi.bdd_mul (c := (2 * π)⁻¹ * ∫ ξ, ‖linear_nonstationary_symbol_expansion_m p R j y k ξ‖)
      ((c09_aux_invFourierT_continuous _ (hmi k)).comp (continuous_const.sub continuous_id)
        |>.aestronglyMeasurable) (Eventually.of_forall fun z => c09_aux_invFourierT_norm_le _ _)
  have hconv : ∀ k, Integrable (fun w => invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w *
      ((deriv G (y - w) : ℝ) : ℂ)) := by
    intro k
    refine ((hTk k).comp_sub_left y).congr (Eventually.of_forall fun w => ?_)
    simp only [sub_sub_cancel]
  -- the remainder kernel
  have hdm := fun k => (hms k).continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖deriv (linear_nonstationary_symbol_expansion_m p R j y n) x‖ ≤ B :=
    (hdm n).bounded_above_of_compact_support (hmsupp n).deriv
  have hEj := c09_aux_tail_joint p hp0
  have hremc : Continuous fun z => linear_nonstationary_symbol_expansion_remKernel p R j (n + 1) y z := by
    unfold linear_nonstationary_symbol_expansion_remKernel
    simp only [Nat.add_sub_cancel]
    refine Continuous.neg ?_
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (z x : ℝ) => deriv (linear_nonstationary_symbol_expansion_m p R j y n) x *
        Complex.exp (Complex.I * ((y * x - Phi0 p x : ℝ) : ℂ)) * c09_tail_integral p z x) ?_ 1 (2 * R)
    exact ((hdm n).comp continuous_snd |>.mul (hec.comp continuous_snd)).mul
      (hEj.comp (f := fun q : ℝ × ℝ => (q.1, q.2)) (by fun_prop))
  have hremb : ∀ z, ‖linear_nonstationary_symbol_expansion_remKernel p R j (n + 1) y z‖ ≤
      (B * CE * (2 * R)) * c09_weights_E p z := by
    intro z
    unfold linear_nonstationary_symbol_expansion_remKernel
    simp only [Nat.add_sub_cancel, norm_neg]
    have hw := c09_aux_weightsE_pos p z
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B * (CE * c09_weights_E p z))
      fun x hx => ?_).trans ?_
    · rw [uIoc_of_le (by linarith)] at hx
      rw [norm_mul, norm_mul, c09_aux_norm_exp_phase, mul_one]
      exact mul_le_mul (hB x) (hE z x (by linarith [hx.1])) (norm_nonneg _) hB0
    · rw [abs_of_pos (by linarith)]
      have : 0 ≤ B * CE * c09_weights_E p z := by positivity
      nlinarith
  have hrem : Integrable (fun z => linear_nonstationary_symbol_expansion_remKernel p R j (n + 1) y z *
      ((deriv G z : ℝ) : ℂ)) := by
    refine Integrable.mono' (hGw.const_mul (B * CE * (2 * R)))
      (hremc.aestronglyMeasurable.mul hgm) (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ (B * CE * (2 * R)) * c09_weights_E p z * |deriv G z| := by
          gcongr; exact hremb z
      _ = _ := by ring
  have hsum : Integrable (fun z => ((2 * π : ℝ) : ℂ) * (∑ k ∈ Finset.range (n + 1),
      invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) (y - z) * ((deriv G z : ℝ) : ℂ))) :=
    (integrable_finsetSum _ fun k _ => hTk k).const_mul _
  have hKeq : ∀ z, c09_stationary_split_kernel_ns p R j y z * ((deriv G z : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ) * (∑ k ∈ Finset.range (n + 1),
        invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) (y - z) * ((deriv G z : ℝ) : ℂ)) +
      linear_nonstationary_symbol_expansion_remKernel p R j (n + 1) y z * ((deriv G z : ℝ) : ℂ) := by
    intro z
    rw [part2 z n, add_mul, mul_assoc, Finset.sum_mul]
  have hKi : Integrable (fun z => c09_stationary_split_kernel_ns p R j y z * ((deriv G z : ℝ) : ℂ)) :=
    (hsum.add hrem).congr (Eventually.of_forall fun z => (hKeq z).symm)
  have hsumeq : ∀ k, ∫ z, invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) (y - z) *
      ((deriv G z : ℝ) : ℂ) = ∫ w, invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w *
      ((deriv G (y - w) : ℝ) : ℂ) := by
    intro k
    have := integral_sub_left_eq_self (μ := volume) (fun w =>
      invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w *
        ((deriv G (y - w) : ℝ) : ℂ)) y
    simp only [sub_sub_cancel] at this
    exact this
  refine ⟨hKi, hrem, fun k _ => hconv k, ?_⟩
  unfold c09_stationary_split_op_ns linear_nonstationary_symbol_expansion_remOp
  rw [integral_congr_ae (Eventually.of_forall hKeq), integral_add hsum hrem, integral_const_mul,
    integral_finsetSum _ fun k _ => hTk k, Finset.sum_congr rfl fun k _ => hsumeq k]

/-- Blueprint: lem:c09_q_bounds.  `q^R(y,ξ) = -(2π)⁻¹ θ_R(ξ) χ_ns(y,ξ) (y-ξ^p)⁻¹`. -/
def c09_q_bounds_q (p R y ξ : ℝ) : ℝ :=
  -(1 / (2 * π)) * c09_truncation_theta R ξ * c09_stationary_split_chi_ns p y ξ / (y - ξ ^ p)

/-- `q^R` as a product. -/
theorem c09_aux_q_eq (p R y : ℝ) : c09_q_bounds_q p R y = fun x =>
    (-(1 / (2 * π)) * (c09_truncation_theta R x * c09_stationary_split_chi_ns p y x)) *
      (y - x ^ p)⁻¹ := by
  funext x; unfold c09_q_bounds_q; rw [div_eq_mul_inv]; ring

/-- Derivatives of `q^R` vanish off `tsupport χ_ns`. -/
theorem c09_aux_q_vanish (p R y ξ : ℝ) (hξ : ξ ∉ tsupport (c09_stationary_split_chi_ns p y))
    (ℓ : ℕ) : iteratedDeriv ℓ (c09_q_bounds_q p R y) ξ = 0 := by
  have hev := notMem_tsupport_iff_eventuallyEq.mp hξ
  have : c09_q_bounds_q p R y =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with x hx
    unfold c09_q_bounds_q; rw [hx]; simp
  rw [this.iteratedDeriv_eq]; simp

/-- Symbol bounds for `q^R`. -/
theorem c09_aux_q_symbol (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (ℓ : ℕ) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ →
      |iteratedDeriv ℓ (c09_q_bounds_q p R y) ξ| ≤ C * ξ ^ (-(ℓ : ℝ)) * (|y| + ξ ^ p)⁻¹ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨K, hK, hKb⟩ := c09_aux_u_bounds p hp hp1 ℓ
  obtain ⟨Cg, hCg, hgb⟩ := c09_aux_psi_inv p hp0 _ (c09_aux_cs_pos p hp0) ℓ
  set k : ℝ := -(1 / (2 * π)) with hk
  refine ⟨2 ^ ℓ * (|k| * K) * Cg + 1, by positivity, fun R hR y ξ hξ => ?_⟩
  have hξp := Real.rpow_pos_of_pos hξ p
  have hW : 0 < |y| + ξ ^ p := by positivity
  have hpos : 0 ≤ ξ ^ (-(ℓ : ℝ)) * (|y| + ξ ^ p)⁻¹ := by positivity
  by_cases hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)
  swap
  · rw [c09_aux_q_vanish p R y ξ hs, abs_zero]; positivity
  have hgood := c09_aux_good p hp0 y ξ hξ hs
  have hne : y - ξ ^ p ≠ 0 := by
    intro h; rw [h, abs_zero] at hgood
    have := c09_aux_cs_pos p hp0; nlinarith
  have hu : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => c09_truncation_theta R x * c09_stationary_split_chi_ns p y x) ξ :=
    ((c09_aux_theta_smooth R).mul (c09_aux_chi_ns_smooth p y)).contDiffAt.of_le (by simp)
  have hf : ∀ i ≤ ℓ, ‖iteratedDeriv i (fun x => k * (c09_truncation_theta R x *
      c09_stationary_split_chi_ns p y x)) ξ‖ ≤ (|k| * K) * ξ ^ ((0 : ℝ) - i) := by
    intro i hi
    rw [iteratedDeriv_const_mul _ (hu.of_le (by exact_mod_cast le_top)), norm_mul,
      Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hKb R (by linarith) y ξ hξ i hi) (abs_nonneg _)
  have key := c09_aux_leib _ (fun x : ℝ => (y - x ^ p)⁻¹) ξ hξ ℓ
    ((contDiffAt_const.mul hu).of_le (by exact_mod_cast le_top))
    ((c09_aux_psi_smooth p y ξ hξ hne).of_le (by exact_mod_cast le_top)) _ _ 0 0 hf
    (fun i hi => hgb y ξ hξ hgood i hi)
  rw [c09_aux_q_eq, ← Real.norm_eq_abs]
  refine key.trans ?_
  rw [show (0 : ℝ) + 0 - ℓ = -(ℓ : ℝ) by ring]
  have : 0 ≤ 2 ^ ℓ * (|k| * K) * Cg := by positivity
  calc 2 ^ ℓ * (|k| * K) * (Cg * (|y| + ξ ^ p)⁻¹) * ξ ^ (-(ℓ : ℝ))
      = (2 ^ ℓ * (|k| * K) * Cg) * (ξ ^ (-(ℓ : ℝ)) * (|y| + ξ ^ p)⁻¹) := by ring
    _ ≤ (2 ^ ℓ * (|k| * K) * Cg + 1) * (ξ ^ (-(ℓ : ℝ)) * (|y| + ξ ^ p)⁻¹) := by
        gcongr; linarith
    _ = _ := by ring

/-- `R ≥ R₀(y)` gives `R ≥ 2` and `R^p ≥ ⟨y⟩`. -/
theorem c09_aux_R0 (p : ℝ) (hp : 0 < p) (y R : ℝ) (hR : c09_truncation_R0 p y ≤ R) :
    2 ≤ R ∧ jb y ≤ R ^ p := by
  unfold c09_truncation_R0 at hR
  refine ⟨(le_max_left _ _).trans hR, ?_⟩
  have h1 : jb y ^ (1 / p) ≤ R := (le_max_right _ _).trans hR
  have hj := c09_aux_jb_pos y
  calc jb y = (jb y ^ (1 / p)) ^ p := by
        rw [← Real.rpow_mul hj.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
    _ ≤ R ^ p := Real.rpow_le_rpow (by positivity) h1 hp.le

/-- For `R ≥ R₀(y)`, derivatives of `θ_R χ_ns` of order `≥ 1` live where `|y| ≤ 2ξ^p`. -/
theorem c09_aux_u_transition (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (y R : ℝ)
    (hR : c09_truncation_R0 p y ≤ R) (ξ : ℝ) (hξ : 0 < ξ) (i : ℕ) (hi : 1 ≤ i)
    (h : iteratedDeriv i (fun x => c09_truncation_theta R x * c09_stationary_split_chi_ns p y x) ξ
      ≠ 0) : |y| ≤ 2 * ξ ^ p := by
  by_contra hlt
  push Not at hlt
  apply h
  obtain ⟨hR2, hRp⟩ := c09_aux_R0 p hp y R hR
  have hξp := Real.rpow_pos_of_pos hξ p
  have hξR : ξ < R := by
    by_contra hh; push Not at hh
    have : R ^ p ≤ ξ ^ p := Real.rpow_le_rpow (by linarith) hh hp.le
    have : |y| ≤ jb y := by
      unfold jb; rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hχ : ∀ᶠ x in 𝓝 ξ, c09_stationary_split p y x = 0 := by
    rcases le_or_gt y 0 with hy | hy
    · exact Eventually.of_forall fun x => by rw [c09_aux_cut_S1 p y hy]
    · set c := y ^ (1 / p) with hcdef
      have hc : 0 < c := Real.rpow_pos_of_pos hy _
      have hcp : c ^ p = y := by
        rw [hcdef, ← Real.rpow_mul hy.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
      have hξc : ξ < c / 2 := by
        by_contra hh; push Not at hh
        have h1 : (c / 2) ^ p ≤ ξ ^ p := Real.rpow_le_rpow (by positivity) hh hp.le
        have h2 : (c / 2) ^ p = y / 2 ^ p := by rw [Real.div_rpow hc.le (by norm_num), hcp]
        have h3 : (2 : ℝ) ^ p ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hp1.le
        have h4 : y / 2 ≤ y / 2 ^ p := div_le_div_of_nonneg_left hy.le (by positivity) h3
        rw [abs_of_pos hy] at hlt
        linarith
      filter_upwards [Iio_mem_nhds hξc] with x hx
      by_contra hne
      have := (c09_aux_cut_Q1a p y x hne).2
      rw [abs_le] at this
      have : x < c / 2 := hx
      linarith [this]
  have hev : (fun x => c09_truncation_theta R x * c09_stationary_split_chi_ns p y x) =ᶠ[𝓝 ξ]
      fun _ => (1 : ℝ) := by
    filter_upwards [hχ, Ioo_mem_nhds (show -R < ξ by linarith) hξR] with x hx hx2
    unfold c09_stationary_split_chi_ns c09_truncation_theta
    rw [hx, c09_aux_cut_R2a]
    · ring
    · have hR0 : 0 < R := by linarith
      rw [abs_le]
      constructor
      · rw [le_div_iff₀ hR0]; linarith [hx2.1]
      · rw [div_le_iff₀ hR0]; linarith [hx2.2]
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const]
  simp; omega

/-- Sharp bounds for `∂^ℓ q^R`, `ℓ ≥ 1`, `R ≥ R₀(y)`. -/
theorem c09_aux_q_sharp (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (N : ℕ) :
    ∃ C, 0 < C ∧ ∀ y R : ℝ, c09_truncation_R0 p y ≤ R → ∀ ξ : ℝ, 0 < ξ → ∀ ℓ, 1 ≤ ℓ → ℓ ≤ N →
      |iteratedDeriv ℓ (c09_q_bounds_q p R y) ξ| ≤ C * ξ ^ (p - ℓ) * ((|y| + ξ ^ p) ^ 2)⁻¹ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨K, hK, hKb⟩ := c09_aux_u_bounds p hp hp1 N
  obtain ⟨Cg, hCg, hgb⟩ := c09_aux_psi_inv p hp0 _ (c09_aux_cs_pos p hp0) N
  obtain ⟨Cs, hCs, hsb⟩ := c09_aux_psi_inv_sharp p hp0 _ (c09_aux_cs_pos p hp0) N
  set k : ℝ := -(1 / (2 * π)) with hk
  refine ⟨2 ^ N * (|k| * K * (Cs + 3 * Cg)) + 1, by positivity,
    fun y R hR ξ hξ ℓ hℓ1 hℓN => ?_⟩
  obtain ⟨hR2, -⟩ := c09_aux_R0 p hp0 y R hR
  have hξp := Real.rpow_pos_of_pos hξ p
  have hW : 0 < |y| + ξ ^ p := by positivity
  have hpos : 0 ≤ ξ ^ (p - ℓ) * ((|y| + ξ ^ p) ^ 2)⁻¹ := by positivity
  by_cases hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)
  swap
  · rw [c09_aux_q_vanish p R y ξ hs, abs_zero]; positivity
  have hgood := c09_aux_good p hp0 y ξ hξ hs
  have hne : y - ξ ^ p ≠ 0 := by
    intro h; rw [h, abs_zero] at hgood
    have := c09_aux_cs_pos p hp0; nlinarith
  have hu : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => c09_truncation_theta R x * c09_stationary_split_chi_ns p y x) ξ :=
    ((c09_aux_theta_smooth R).mul (c09_aux_chi_ns_smooth p y)).contDiffAt.of_le (by simp)
  have hfe : ∀ i, iteratedDeriv i (fun x => k * (c09_truncation_theta R x *
      c09_stationary_split_chi_ns p y x)) ξ = k * iteratedDeriv i (fun x =>
        c09_truncation_theta R x * c09_stationary_split_chi_ns p y x) ξ := fun i =>
    iteratedDeriv_const_mul _ (hu.of_le (by exact_mod_cast le_top))
  set D := |k| * K * (Cs + 3 * Cg) * (ξ ^ (p - ℓ) * ((|y| + ξ ^ p) ^ 2)⁻¹) with hD
  have hterm : ∀ i ≤ ℓ, ‖iteratedDeriv i (fun x => k * (c09_truncation_theta R x *
      c09_stationary_split_chi_ns p y x)) ξ‖ *
        ‖iteratedDeriv (ℓ - i) (fun x : ℝ => (y - x ^ p)⁻¹) ξ‖ ≤ D := by
    intro i hi
    rw [hfe, norm_mul, Real.norm_eq_abs k]
    have hub := hKb R (by linarith) y ξ hξ i (by omega)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have h1 : ‖iteratedDeriv 0 (fun x => c09_truncation_theta R x *
          c09_stationary_split_chi_ns p y x) ξ‖ ≤ K := by
        simpa using hub
      have h2 := hsb y ξ hξ hgood ℓ hℓ1 hℓN
      rw [Nat.sub_zero]
      calc |k| * ‖iteratedDeriv 0 (fun x => c09_truncation_theta R x *
            c09_stationary_split_chi_ns p y x) ξ‖ * ‖iteratedDeriv ℓ (fun x : ℝ => (y - x ^ p)⁻¹) ξ‖
          ≤ |k| * K * (Cs * ((|y| + ξ ^ p) ^ 2)⁻¹ * ξ ^ (p - ℓ)) := by gcongr
        _ ≤ D := by
          rw [hD]
          have : 0 ≤ |k| * K * (3 * Cg) * (ξ ^ (p - ℓ) * ((|y| + ξ ^ p) ^ 2)⁻¹) := by positivity
          nlinarith
    · by_cases hz : iteratedDeriv i (fun x => c09_truncation_theta R x *
          c09_stationary_split_chi_ns p y x) ξ = 0
      · rw [hz, norm_zero, mul_zero, zero_mul]; rw [hD]; positivity
      have hy2 := c09_aux_u_transition p hp0 hp1 y R hR ξ hξ i hi0 hz
      have h2 := hgb y ξ hξ hgood (ℓ - i) (by omega)
      have e1 : ξ ^ ((0 : ℝ) - i) * ξ ^ ((0 : ℝ) - ((ℓ - i : ℕ) : ℝ)) =
          ξ ^ (p - ℓ) * ξ ^ (-p) := by
        rw [← Real.rpow_add hξ, ← Real.rpow_add hξ, Nat.cast_sub hi]; congr 1; ring
      have hWp : (|y| + ξ ^ p)⁻¹ * ξ ^ (-p) ≤ 3 * ((|y| + ξ ^ p) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hξ.le]
        calc (|y| + ξ ^ p)⁻¹ * (ξ ^ p)⁻¹ = ((|y| + ξ ^ p) * ξ ^ p)⁻¹ := (mul_inv _ _).symm
          _ ≤ ((|y| + ξ ^ p) ^ 2 / 3)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
          _ = 3 * ((|y| + ξ ^ p) ^ 2)⁻¹ := by rw [inv_div]; ring
      calc |k| * ‖iteratedDeriv i (fun x => c09_truncation_theta R x *
            c09_stationary_split_chi_ns p y x) ξ‖ *
              ‖iteratedDeriv (ℓ - i) (fun x : ℝ => (y - x ^ p)⁻¹) ξ‖
          ≤ |k| * (K * ξ ^ ((0 : ℝ) - i)) *
              (Cg * (|y| + ξ ^ p)⁻¹ * ξ ^ ((0 : ℝ) - ((ℓ - i : ℕ) : ℝ))) := by gcongr
        _ = |k| * K * Cg * (ξ ^ (p - ℓ) * ξ ^ (-p)) * (|y| + ξ ^ p)⁻¹ := by
            rw [← e1]; ring
        _ = |k| * K * Cg * ξ ^ (p - ℓ) * ((|y| + ξ ^ p)⁻¹ * ξ ^ (-p)) := by ring
        _ ≤ |k| * K * Cg * ξ ^ (p - ℓ) * (3 * ((|y| + ξ ^ p) ^ 2)⁻¹) := by
            have : 0 ≤ ξ ^ (p - ℓ) := (Real.rpow_pos_of_pos hξ _).le
            gcongr
        _ ≤ D := by
            rw [hD]
            have : 0 ≤ |k| * K * Cs * (ξ ^ (p - ℓ) * ((|y| + ξ ^ p) ^ 2)⁻¹) := by positivity
            nlinarith
  have key := c09_aux_leib_terms _ (fun x : ℝ => (y - x ^ p)⁻¹) ξ ℓ
    ((contDiffAt_const.mul hu).of_le (by exact_mod_cast le_top))
    ((c09_aux_psi_smooth p y ξ hξ hne).of_le (by exact_mod_cast le_top)) D hterm
  rw [c09_aux_q_eq, ← Real.norm_eq_abs]
  refine key.trans ?_
  rw [hD]
  have h2l : (2 : ℝ) ^ ℓ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hℓN
  have : 0 ≤ |k| * K * (Cs + 3 * Cg) := by positivity
  calc 2 ^ ℓ * (|k| * K * (Cs + 3 * Cg) * (ξ ^ (p - ℓ) * ((|y| + ξ ^ p) ^ 2)⁻¹))
      ≤ (2 ^ N * (|k| * K * (Cs + 3 * Cg)) + 1) * (ξ ^ (p - ℓ) * ((|y| + ξ ^ p) ^ 2)⁻¹) := by
        have : 2 ^ ℓ * (|k| * K * (Cs + 3 * Cg)) ≤ 2 ^ N * (|k| * K * (Cs + 3 * Cg)) := by gcongr
        nlinarith
    _ = _ := by ring

/-- Blueprint: lem:c09_q_bounds.  `m_{2,0}^R = (1-χ) q^R`; bounds on `q^R` and its derivatives,
the sharp ones for `R ≥ R₀(y)`. -/
theorem c09_q_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ →
      linear_nonstationary_symbol_expansion_m p R 2 y 0 ξ =
        (((1 - rho ξ) * c09_q_bounds_q p R y ξ : ℝ) : ℂ)) ∧
    (∃ C, 0 < C ∧
      (∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ → |c09_q_bounds_q p R y ξ| ≤ C * (|y| + ξ ^ p)⁻¹) ∧
      (∀ y R : ℝ, c09_truncation_R0 p y ≤ R → ∀ ξ : ℝ, 0 < ξ →
        |deriv (c09_q_bounds_q p R y) ξ| ≤ C * ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 2)⁻¹ ∧
        |iteratedDeriv 2 (c09_q_bounds_q p R y) ξ| ≤ C * ξ ^ (p - 2) * ((|y| + ξ ^ p) ^ 2)⁻¹)) ∧
    (∀ ℓ : ℕ, ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 0 < ξ →
      |iteratedDeriv ℓ (c09_q_bounds_q p R y) ξ| ≤ C * ξ ^ (-(ℓ : ℝ)) * (|y| + ξ ^ p)⁻¹) := by
  refine ⟨?_, ?_, fun ℓ => c09_aux_q_symbol p hp hp1 ℓ⟩
  · intro R hR y ξ hξ
    simp only [linear_nonstationary_symbol_expansion_m, c09_stationary_split_amp_ns,
      c09_positive_kernel_amp, hξ, ↓reduceIte, c09_q_bounds_q]
    rw [show ((2 : ℕ) : ℝ) - 2 = 0 by norm_num, Real.rpow_zero]
    by_cases h0 : y - ξ ^ p = 0
    · rw [h0]; simp
    · have hI : Complex.I ^ (2 + 1) = -Complex.I := by
        rw [pow_succ, Complex.I_sq]; ring
      rw [hI]
      have h0' : ((y - ξ ^ p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
      have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
      push_cast at h0' hπ ⊢
      field_simp
      ring
  · obtain ⟨C0, hC0, h0⟩ := c09_aux_q_symbol p hp hp1 0
    obtain ⟨C2, hC2, h2⟩ := c09_aux_q_sharp p hp hp1 2
    refine ⟨C0 + C2, by positivity, fun R hR y ξ hξ => ?_, fun y R hR ξ hξ => ?_⟩
    · have := h0 R hR y ξ hξ
      simp only [iteratedDeriv_zero, CharP.cast_eq_zero, neg_zero, Real.rpow_zero,
        mul_one] at this
      refine this.trans ?_
      have : 0 ≤ (|y| + ξ ^ p)⁻¹ := by have := Real.rpow_pos_of_pos hξ p; positivity
      nlinarith
    · have hb1 := h2 y R hR ξ hξ 1 le_rfl (by norm_num)
      have hb2 := h2 y R hR ξ hξ 2 (by norm_num) le_rfl
      rw [iteratedDeriv_one] at hb1
      have : 0 ≤ ((|y| + ξ ^ p) ^ 2)⁻¹ := by positivity
      have h1' : 0 ≤ ξ ^ (p - 1) := (Real.rpow_pos_of_pos hξ _).le
      have h2' : 0 ≤ ξ ^ (p - 2) := (Real.rpow_pos_of_pos hξ _).le
      push_cast at hb1 hb2
      constructor
      · refine hb1.trans ?_; gcongr; linarith
      · refine hb2.trans ?_; gcongr; linarith

/-- `∂_z m^∨ = (iξ m)^∨` for a continuous compactly supported symbol `m`. -/
theorem c09_aux_invF_hasDerivAt (m : ℝ → ℂ) (hm : Continuous m) (hs : HasCompactSupport m) (z : ℝ) :
    HasDerivAt (invFourierT m) (invFourierT (fun ξ => Complex.I * (ξ : ℂ) * m ξ) z) z := by
  have hmi : Integrable m := hm.integrable_of_hasCompactSupport hs
  have hm1c : Continuous (fun ξ : ℝ => Complex.I * (ξ : ℂ) * m ξ) := by fun_prop
  have hs1 : HasCompactSupport (fun ξ : ℝ => Complex.I * (ξ : ℂ) * m ξ) :=
    hs.mul_left (f := fun ξ : ℝ => Complex.I * (ξ : ℂ))
  have hm1i : Integrable (fun ξ : ℝ => Complex.I * (ξ : ℂ) * m ξ) :=
    hm1c.integrable_of_hasCompactSupport hs1
  have hez : Continuous fun ξ : ℝ => Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) := by fun_prop
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := z)
    (F := fun (x ξ : ℝ) => m ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)))
    (F' := fun (x ξ : ℝ) => Complex.I * (ξ : ℂ) * m ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)))
    (s := univ) (bound := fun ξ : ℝ => ‖Complex.I * (ξ : ℂ) * m ξ‖) Filter.univ_mem
    (Eventually.of_forall fun x : ℝ => (hm.mul (by fun_prop)).aestronglyMeasurable)
    (hmi.mul_bdd hez.aestronglyMeasurable (Eventually.of_forall fun ξ => (c09_aux_norm_exp_pos z ξ).le))
    ((hm1c.mul hez).aestronglyMeasurable)
    (Eventually.of_forall fun (ξ : ℝ) (x : ℝ) _ => by rw [norm_mul, c09_aux_norm_exp_pos, mul_one])
    hm1i.norm
    (Eventually.of_forall fun (ξ : ℝ) (x : ℝ) _ => by
      have := (c09_aux_hasDerivAt_exp_Iyx ξ x).const_mul (m ξ)
      convert this using 1; ring)
  unfold invFourierT
  exact hd.2.const_mul _

/-! #### Helpers: decay of inverse Fourier transforms of smooth compactly supported symbols -/

/-- `‖ǩ(z)‖ |z|^N ≤ (2π)⁻¹ ∫ ‖s^{(N)}‖`. -/
theorem c09_aux_invF_decay (s : ℝ → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) s) (hsupp : HasCompactSupport s)
    (z : ℝ) (N : ℕ) :
    ‖invFourierT s z‖ * |z| ^ N ≤ (2 * π)⁻¹ * ∫ ξ, ‖iteratedDeriv N s ξ‖ := by
  have h := c09_aux_four_ibp_iter s hs hsupp z N
  have hn := congrArg norm h
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_neg, norm_one, one_pow, one_mul] at hn
  unfold invFourierT
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    mul_assoc, mul_comm _ (|z| ^ N), hn]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext ξ; rw [norm_mul, c09_aux_norm_exp_pos, mul_one]

/-- Combined decay: `‖ǩ(z)‖ ≤ (2π)⁻¹ 2^{N/2} (A₀ + A_N) ⟨z⟩^{-N}`. -/
theorem c09_aux_invF_decay_jb (s : ℝ → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) s) (hsupp : HasCompactSupport s)
    (N : ℕ) (A₀ A : ℝ) (hA₀ : ∫ ξ, ‖s ξ‖ ≤ A₀) (hA : ∫ ξ, ‖iteratedDeriv N s ξ‖ ≤ A) (z : ℝ) :
    ‖invFourierT s z‖ ≤ (2 * π)⁻¹ * (Real.sqrt 2) ^ N * (A₀ + A) * jb z ^ (-(N : ℝ)) := by
  have h0 := c09_aux_invF_decay s hs hsupp z 0
  have hN := c09_aux_invF_decay s hs hsupp z N
  simp only [pow_zero, mul_one, iteratedDeriv_zero] at h0
  have hI0 : 0 ≤ ∫ ξ, ‖s ξ‖ := integral_nonneg fun _ => norm_nonneg _
  have hIN : 0 ≤ ∫ ξ, ‖iteratedDeriv N s ξ‖ := integral_nonneg fun _ => norm_nonneg _
  have hjz := c09_aux_jb_pos z
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hπ : 0 < (2 * π)⁻¹ := by positivity
  have hjN : jb z ^ (-(N : ℝ)) = (jb z ^ N)⁻¹ := by
    rw [Real.rpow_neg hjz.le, Real.rpow_natCast]
  rw [hjN]
  have hjNp : 0 < jb z ^ N := pow_pos hjz N
  rw [← div_eq_mul_inv, le_div_iff₀ hjNp]
  rcases le_or_gt |z| 1 with hz | hz
  · -- `⟨z⟩ ≤ √2`
    have hj2 : jb z ≤ Real.sqrt 2 := by
      unfold jb; apply Real.sqrt_le_sqrt
      have : z ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
      linarith
    have a : ‖invFourierT s z‖ ≤ (2 * π)⁻¹ * A₀ := h0.trans (by gcongr)
    have b : jb z ^ N ≤ Real.sqrt 2 ^ N := pow_le_pow_left₀ hjz.le hj2 N
    have hA : 0 ≤ A := hIN.trans hA
    have hs2 : 0 ≤ Real.sqrt 2 ^ N := by positivity
    have e : (2 * π)⁻¹ * Real.sqrt 2 ^ N * (A₀ + A) =
        (2 * π)⁻¹ * A₀ * Real.sqrt 2 ^ N + (2 * π)⁻¹ * Real.sqrt 2 ^ N * A := by ring
    rw [e]
    have : 0 ≤ (2 * π)⁻¹ * Real.sqrt 2 ^ N * A := by positivity
    have := mul_le_mul a b (by positivity) ((norm_nonneg _).trans a)
    linarith
  · -- `⟨z⟩ ≤ √2 |z|`
    have hj2 : jb z ≤ Real.sqrt 2 * |z| := by
      unfold jb
      rw [show Real.sqrt 2 * |z| = Real.sqrt (2 * z ^ 2) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]]
      apply Real.sqrt_le_sqrt
      have : 1 ≤ z ^ 2 := by rw [← sq_abs]; nlinarith
      linarith
    calc ‖invFourierT s z‖ * jb z ^ N ≤ ‖invFourierT s z‖ * (Real.sqrt 2 ^ N * |z| ^ N) := by
          gcongr
          rw [← mul_pow]; exact pow_le_pow_left₀ hjz.le hj2 N
      _ = Real.sqrt 2 ^ N * (‖invFourierT s z‖ * |z| ^ N) := by ring
      _ ≤ Real.sqrt 2 ^ N * ((2 * π)⁻¹ * A) := by
          have := hN.trans (show (2 * π)⁻¹ * ∫ ξ, ‖iteratedDeriv N s ξ‖ ≤ (2 * π)⁻¹ * A by gcongr)
          gcongr
      _ ≤ _ := by
          have hA0 : 0 ≤ A₀ := hI0.trans hA₀
          have : 0 ≤ (2 * π)⁻¹ * Real.sqrt 2 ^ N * A₀ := by positivity
          have e : (2 * π)⁻¹ * Real.sqrt 2 ^ N * (A₀ + A) =
              (2 * π)⁻¹ * Real.sqrt 2 ^ N * A₀ + Real.sqrt 2 ^ N * ((2 * π)⁻¹ * A) := by ring
          rw [e]; linarith

/-- `L¹` bound for a function vanishing on `(-∞,1)` and bounded by `B ξ^{-2}` on `[1,∞)`. -/
theorem c09_aux_L1_of_bound (g : ℝ → ℂ) (hg : Continuous g) (B : ℝ)
    (h0 : ∀ ξ, ξ < 1 → g ξ = 0) (hb : ∀ ξ, 1 ≤ ξ → ‖g ξ‖ ≤ B * ξ ^ (-2 : ℝ)) :
    ∫ ξ, ‖g ξ‖ ≤ B := by
  have hint : IntegrableOn (fun ξ : ℝ => B * ξ ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul B
  set G : ℝ → ℝ := Set.indicator (Ioi 1) (fun ξ : ℝ => B * ξ ^ (-2 : ℝ)) with hG
  have hGi : Integrable G := hint.integrable_indicator measurableSet_Ioi
  have hle : ∀ᵐ ξ, ‖g ξ‖ ≤ G ξ := by
    have : ∀ᵐ ξ : ℝ, ξ ≠ 1 := by
      have := (measure_singleton (μ := (volume : Measure ℝ)) (1 : ℝ))
      exact compl_mem_ae_iff.mpr this
    filter_upwards [this] with ξ hξ
    rcases lt_or_gt_of_ne hξ with h | h
    · rw [h0 ξ h, norm_zero, hG, Set.indicator_of_notMem (by simp only [mem_Ioi, not_lt]; linarith)]
    · rw [hG, Set.indicator_of_mem (show ξ ∈ Ioi (1 : ℝ) from h)]; exact hb ξ h.le
  have hgi : Integrable (fun ξ => ‖g ξ‖) :=
    hGi.mono' hg.norm.aestronglyMeasurable (hle.mono fun ξ h => by rwa [Real.norm_eq_abs, abs_norm])
  refine (integral_mono_ae hgi hGi hle).trans (le_of_eq ?_)
  rw [hG, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-- `‖∂^i (iξ)‖ ≤ ξ^{1-i}` for `ξ > 0`. -/
theorem c09_aux_iter_Ix (i : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ‖iteratedDeriv i (fun x : ℝ => Complex.I * (x : ℂ)) ξ‖ ≤ ξ ^ ((1 : ℝ) - i) := by
  have hd : deriv (fun x : ℝ => Complex.I * (x : ℂ)) = fun _ => Complex.I := by
    funext x
    simpa using (((hasDerivAt_id x).ofReal_comp).const_mul Complex.I).deriv
  rcases i with _ | i
  · simp [Complex.norm_I, abs_of_pos hξ]
  · rw [iteratedDeriv_succ', hd, iteratedDeriv_const]
    split_ifs with h
    · subst h; simp
    · simp only [norm_zero]; exact (Real.rpow_pos_of_pos hξ _).le

/-- Generic kernel bound: `‖š(z)‖ ≤ (2π)⁻¹ √2^N (2B) ⟨z⟩^{-L}` from symbol bounds `B ξ^{-2}`. -/
theorem c09_aux_kernel_generic (s : ℝ → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) s) (hsupp : HasCompactSupport s)
    (h0 : ∀ ℓ : ℕ, ∀ ξ, ξ < 1 → iteratedDeriv ℓ s ξ = 0) (N : ℕ) (B : ℝ)
    (hb : ∀ ℓ ≤ N, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv ℓ s ξ‖ ≤ B * ξ ^ (-2 : ℝ)) (L : ℝ) (hNL : L ≤ N)
    (z : ℝ) : ‖invFourierT s z‖ ≤ (2 * π)⁻¹ * Real.sqrt 2 ^ N * (2 * B) * jb z ^ (-L) := by
  have hcont : ∀ ℓ : ℕ, Continuous (iteratedDeriv ℓ s) := fun ℓ =>
    hs.continuous_iteratedDeriv ℓ (by exact_mod_cast le_top)
  have hA0 : ∫ ξ, ‖s ξ‖ ≤ B := by
    have := c09_aux_L1_of_bound (iteratedDeriv 0 s) (hcont 0) B (h0 0) (hb 0 (Nat.zero_le _))
    simpa using this
  have hAN := c09_aux_L1_of_bound (iteratedDeriv N s) (hcont N) B (h0 N) (hb N le_rfl)
  have h := c09_aux_invF_decay_jb s hs hsupp N B B hA0 hAN z
  refine h.trans ?_
  have hB : 0 ≤ B := by
    have := hb 0 (Nat.zero_le _) 1 le_rfl
    simp only [Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  have hjz : jb z ^ (-(N : ℝ)) ≤ jb z ^ (-L) :=
    Real.rpow_le_rpow_of_exponent_le (c09_aux_one_le_jb z) (by linarith)
  rw [show B + B = 2 * B by ring]
  gcongr

/-- Symbol bounds for `m_{j,k}` on `ξ ≥ 1` in terms of `⟨y⟩`. -/
theorem c09_aux_mk_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (j : ℕ) (hj : j ≤ 2) (k N : ℕ) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 1 ≤ ξ → ∀ ℓ ≤ N,
      ‖iteratedDeriv ℓ (linear_nonstationary_symbol_expansion_m p R j y k) ξ‖ ≤
        C * jb y ^ (-(k : ℝ) - 1) * ξ ^ (((j : ℝ) - 2 - k) - ℓ) := by
  obtain ⟨C, hC, hm⟩ := c09_aux_m_bounds p hp hp1 j hj k N
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h4b, -⟩ := c09_cutoff_bounds p hp hp1
  refine ⟨C * 2 ^ (((k : ℝ) + 1) / 2), by positivity, fun R hR y ξ hξ ℓ hℓ => ?_⟩
  refine (hm R hR y ξ (by linarith) ℓ hℓ).trans ?_
  have hjy := c09_aux_jb_pos y
  have hb := h4b y ξ hξ
  have h2 : (0 : ℝ) < 2 ^ (-(1 / 2 : ℝ)) := by positivity
  have hpos : 0 < 2 ^ (-(1 / 2 : ℝ)) * jb y := by positivity
  have hξp : 0 < ξ ^ (((j : ℝ) - 2 - k) - ℓ) := Real.rpow_pos_of_pos (by linarith) _
  have key : ((|y| + ξ ^ p) ^ (k + 1))⁻¹ ≤ 2 ^ (((k : ℝ) + 1) / 2) * jb y ^ (-(k : ℝ) - 1) := by
    have e1 : ((|y| + ξ ^ p) ^ (k + 1))⁻¹ ≤ ((2 ^ (-(1 / 2 : ℝ)) * jb y) ^ (k + 1))⁻¹ := by
      gcongr
    refine e1.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.rpow_natCast (2 ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (jb y), mul_inv, ← Real.rpow_neg (by norm_num), ← Real.rpow_neg hjy.le]
    push_cast; congr 1 <;> ring_nf
  calc C * ((|y| + ξ ^ p) ^ (k + 1))⁻¹ * ξ ^ (((j : ℝ) - 2 - k) - ℓ)
      ≤ C * (2 ^ (((k : ℝ) + 1) / 2) * jb y ^ (-(k : ℝ) - 1)) * ξ ^ (((j : ℝ) - 2 - k) - ℓ) := by
        gcongr
    _ = _ := by ring

/-- Symbol bounds for `iξ m_{j,k}` on `ξ ≥ 1`. -/
theorem c09_aux_xmk_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (j : ℕ) (hj : j ≤ 2) (k N : ℕ) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 1 ≤ ξ → ∀ ℓ ≤ N,
      ‖iteratedDeriv ℓ (fun x : ℝ => Complex.I * (x : ℂ) *
          linear_nonstationary_symbol_expansion_m p R j y k x) ξ‖ ≤
        C * jb y ^ (-(k : ℝ) - 1) * ξ ^ (((j : ℝ) - 1 - k) - ℓ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨C, hC, hm⟩ := c09_aux_mk_bound p hp hp1 j hj k N
  refine ⟨2 ^ N * C, by positivity, fun R hR y ξ hξ ℓ hℓ => ?_⟩
  have hξ0 : 0 < ξ := by linarith
  have hsm := c09_aux_nse_m_contDiff p hp0 R hR j y k
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Complex.I * (x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have := c09_aux_leib_terms (fun x : ℝ => Complex.I * (x : ℂ))
    (linear_nonstationary_symbol_expansion_m p R j y k) ξ ℓ
    (hx.contDiffAt.of_le (by exact_mod_cast le_top)) (hsm.contDiffAt.of_le (by exact_mod_cast le_top))
    (C * jb y ^ (-(k : ℝ) - 1) * ξ ^ (((j : ℝ) - 1 - k) - ℓ)) (fun i hi => ?_)
  · refine this.trans ?_
    have : (2 : ℝ) ^ ℓ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hℓ
    have h0 : 0 ≤ C * jb y ^ (-(k : ℝ) - 1) * ξ ^ (((j : ℝ) - 1 - k) - ℓ) := by
      have := c09_aux_jb_pos y; positivity
    calc _ ≤ (2 : ℝ) ^ N * (C * jb y ^ (-(k : ℝ) - 1) * ξ ^ (((j : ℝ) - 1 - k) - ℓ)) := by gcongr
      _ = _ := by ring
  · have h1 := c09_aux_iter_Ix i ξ hξ0
    have h2 := hm R hR y ξ hξ (ℓ - i) (by omega)
    have hjy := c09_aux_jb_pos y
    calc _ ≤ ξ ^ ((1 : ℝ) - i) * (C * jb y ^ (-(k : ℝ) - 1) * ξ ^ (((j : ℝ) - 2 - k) - ((ℓ - i : ℕ) : ℝ))) := by
          gcongr
      _ = C * jb y ^ (-(k : ℝ) - 1) * (ξ ^ ((1 : ℝ) - i) * ξ ^ (((j : ℝ) - 2 - k) - ((ℓ - i : ℕ) : ℝ))) := by
          ring
      _ = _ := by
          rw [← Real.rpow_add hξ0, Nat.cast_sub hi]; congr 2; ring

/-- `m_{j,k}^R(y,·)` and its derivatives vanish on `(-∞,1)`; compact support. -/
theorem c09_aux_mk_supp (p : ℝ) (hp : 0 < p) (R : ℝ) (hR : 2 ≤ R) (j : ℕ) (y : ℝ) (k : ℕ) :
    HasCompactSupport (linear_nonstationary_symbol_expansion_m p R j y k) ∧
    ∀ ξ, ξ < 1 → linear_nonstationary_symbol_expansion_m p R j y k =ᶠ[𝓝 ξ] fun _ => 0 := by
  refine ⟨HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2 * R)) fun x hx => ?_,
    fun ξ hξ => c09_aux_m_vanish p R j y k ξ (c09_aux_nse_not_tsupport p R (by linarith) j y ξ
      (Or.inl hξ))⟩
  simp only [mem_Icc, not_and_or, not_le] at hx
  exact c09_aux_nse_m_zero p hp R hR j y k x (hx.imp le_of_lt le_of_lt)

/-- Blueprint: lem:c09_m20_kernel.  The three-region bound function
`|z|^{p-1}` (`0<|z| ≤ ⟨y⟩^{-1/p}`), `⟨y⟩^{-2}|z|^{-p-1} + ⟨y⟩^{-1}` (`⟨y⟩^{-1/p} < |z| ≤ 1`),
`⟨y⟩^{-1}|z|^{-L}` (`|z| > 1`). -/
def c09_m20_kernel_bound (p L y z : ℝ) : ℝ :=
  if |z| ≤ jb y ^ (-1 / p) then |z| ^ (p - 1)
  else if |z| ≤ 1 then jb y ^ (-2 : ℝ) * |z| ^ (-p - 1) + jb y ^ (-1 : ℝ)
  else jb y ^ (-1 : ℝ) * |z| ^ (-L)

/-! #### Helpers for the `m_{2,0}` kernel -/

/-- `q^R(y,·)` is smooth on `(0,∞)` and vanishes near every point outside `tsupport χ_ns`. -/
theorem c09_aux_q_smooth (p : ℝ) (hp : 0 < p) (R y : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c09_q_bounds_q p R y) (Ioi 0) := by
  intro ξ hξ
  have hξ0 : 0 < ξ := hξ
  by_cases hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)
  · have hne : y - ξ ^ p ≠ 0 := by
      intro h
      have := c09_aux_good p hp y ξ hξ0 hs
      rw [h, abs_zero] at this
      have := Real.rpow_pos_of_pos hξ0 p
      have := c09_aux_cs_pos p hp
      nlinarith [abs_nonneg y]
    rw [c09_aux_q_eq]
    exact ((contDiffAt_const.mul ((c09_aux_theta_smooth R).mul
      (c09_aux_chi_ns_smooth p y)).contDiffAt).mul (c09_aux_psi_smooth p y ξ hξ0 hne)).contDiffWithinAt
  · refine ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hs] with x hx
    unfold c09_q_bounds_q; rw [hx]; simp

/-- `q^R(y,·)` vanishes on `(2R, ∞)`. -/
theorem c09_aux_q_zero_big (p R y ξ : ℝ) (hR : 0 < R) (hξ : 2 * R ≤ ξ) : c09_q_bounds_q p R y ξ = 0 := by
  unfold c09_q_bounds_q
  rw [c09_aux_theta_zero R ξ hR (by rw [abs_of_pos (by linarith)]; exact hξ)]
  ring

/-- `Re (m_{2,0})^∨(z) = (2π)⁻¹ ∫₁^{2R+1} (1-χ) q cos(zξ) dξ`. -/
theorem c09_aux_m20_re (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (R : ℝ) (hR : 2 ≤ R) (y z : ℝ) :
    (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z).re =
      (2 * π)⁻¹ * ∫ ξ in (1 : ℝ)..(2 * R + 1),
        (1 - rho ξ) * c09_q_bounds_q p R y ξ * Real.cos (z * ξ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hq, -, -⟩ := c09_q_bounds p hp hp1
  set m := linear_nonstationary_symbol_expansion_m p R 2 y 0 with hm
  have hmc : Continuous m := (c09_aux_nse_m_contDiff p hp0 R hR 2 y 0).continuous
  have hec : Continuous fun ξ : ℝ => Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) := by fun_prop
  have hz : ∀ ξ ∉ Ioc (1 : ℝ) (2 * R + 1), m ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) = 0 := by
    intro ξ hξ
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hξ
    rw [hm, c09_aux_nse_m_zero p hp0 R hR 2 y 0 ξ (hξ.imp id (fun h => by linarith)), zero_mul]
  have hi : IntegrableOn (fun ξ => m ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)))
      (Ioc 1 (2 * R + 1)) := (hmc.mul hec).integrableOn_Ioc
  unfold invFourierT
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul]
  congr 1
  have := Complex.reCLM.integral_comp_comm hi
  simp only [Complex.reCLM_apply] at this
  rw [← this, intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_congr_fun measurableSet_Ioc fun ξ hξ => ?_
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  rw [hm, hq R hR y ξ hξ0]
  rw [show Complex.I * (z : ℂ) * (ξ : ℂ) = ((z * ξ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  ring

/-- `∫_X^Y ξ^r = (Y^{r+1} - X^{r+1})/(r+1)` for `0 < X ≤ Y`, `r ≠ -1`. -/
theorem c09_aux_int_rpow (r X Y : ℝ) (hr : r ≠ -1) (hX : 0 < X) (hXY : X ≤ Y) :
    ∫ ξ in X..Y, ξ ^ r = (Y ^ (r + 1) - X ^ (r + 1)) / (r + 1) :=
  integral_rpow (Or.inr ⟨hr, by rw [uIcc_of_le hXY]; intro h; linarith [h.1]⟩)

/-- Pointwise facts on `u = (1-χ)q` and its derivative used for the `m_{2,0}` kernel. -/
theorem c09_aux_u20 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ Cq Bρ, 0 < Cq ∧ 0 ≤ Bρ ∧ (∀ u, |deriv rho u| ≤ Bρ) ∧ (∀ u, 2 < u → deriv rho u = 0) ∧
      ∀ R : ℝ, 2 ≤ R → ∀ y : ℝ,
      (∀ ξ, 0 < ξ → |c09_q_bounds_q p R y ξ| ≤ Cq * (|y| + ξ ^ p)⁻¹) ∧
      (∀ ξ, 0 < ξ → |deriv (c09_q_bounds_q p R y) ξ| ≤ Cq * ξ ^ (-(1 : ℝ)) * (|y| + ξ ^ p)⁻¹) ∧
      (∀ ξ, 0 < ξ → HasDerivAt (fun ξ => (1 - rho ξ) * c09_q_bounds_q p R y ξ)
        (-(deriv rho ξ) * c09_q_bounds_q p R y ξ + (1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ) ξ) ∧
      ContinuousOn (fun ξ => (1 - rho ξ) * c09_q_bounds_q p R y ξ) (Ioi 0) ∧
      ContinuousOn (deriv (c09_q_bounds_q p R y)) (Ioi 0) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, ⟨C, hC, hq0, -⟩, hq3⟩ := c09_q_bounds p hp hp1
  obtain ⟨C1, hC1, hq1⟩ := hq3 1
  obtain ⟨B, hB0, hB⟩ := c09_aux_cut_R4 1
  refine ⟨C + C1, B, by positivity, hB0, fun u => by simpa using hB u,
    fun u hu => by simpa using c09_aux_cut_R3 1 u (by rw [abs_of_pos (by linarith)]; exact hu),
    fun R hR y => ⟨fun ξ hξ => ?_, fun ξ hξ => ?_, fun ξ hξ => ?_, ?_, ?_⟩⟩
  · have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ p; positivity
    refine (hq0 R hR y ξ hξ).trans ?_
    have : 0 < (|y| + ξ ^ p)⁻¹ := by positivity
    nlinarith
  · have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ p; positivity
    have := hq1 R hR y ξ hξ
    simp only [iteratedDeriv_one, Nat.cast_one] at this
    refine this.trans ?_
    have : 0 < ξ ^ (-(1 : ℝ)) * (|y| + ξ ^ p)⁻¹ := by
      have := Real.rpow_pos_of_pos hξ (-(1 : ℝ)); positivity
    nlinarith
  · have hqd : HasDerivAt (c09_q_bounds_q p R y) (deriv (c09_q_bounds_q p R y) ξ) ξ :=
      (((c09_aux_q_smooth p hp0 R y).differentiableOn (by simp) ξ hξ).differentiableAt
        (isOpen_Ioi.mem_nhds hξ)).hasDerivAt
    have hρd : HasDerivAt rho (deriv rho ξ) ξ :=
      (c09_aux_cut_R1.differentiable (by simp) ξ).hasDerivAt
    convert ((hρd.const_sub 1).mul hqd) using 1
  · exact (continuous_const.sub c09_aux_cut_R1.continuous).continuousOn.mul
      (c09_aux_q_smooth p hp0 R y).continuousOn
  · exact (c09_aux_q_smooth p hp0 R y).continuousOn_deriv_of_isOpen isOpen_Ioi
      (by simpa using c09_aux_le_inf 1)

/-- First bound: `|∫₁^{2R+1} (1-χ)q cos(zξ)| ≤ C z^{p-1}` for `0 < z ≤ 1`. -/
theorem c09_aux_m20_first (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y z : ℝ, 0 < z → z ≤ 1 →
      |∫ ξ in (1 : ℝ)..(2 * R + 1), (1 - rho ξ) * c09_q_bounds_q p R y ξ * Real.cos (z * ξ)| ≤
        C * z ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Cq, Bρ, hCq, hBρ, hρb, hρz, hu⟩ := c09_aux_u20 p hp hp1
  set Cu : ℝ := 2 * Bρ * Cq + Cq with hCu
  have h1p : 0 < 1 - p := by linarith
  refine ⟨Cq / (1 - p) + Cq + Cu / p + 1, by positivity, fun R hR y z hz hz1 => ?_⟩
  obtain ⟨hq, hq', hud, huc, -⟩ := hu R hR y
  set u : ℝ → ℝ := fun ξ => (1 - rho ξ) * c09_q_bounds_q p R y ξ with hudef
  set T : ℝ := 2 * R + 1 with hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  set A : ℝ := z⁻¹ with hA
  have hA1 : 1 ≤ A := by rw [hA]; exact one_le_inv₀ hz |>.mpr hz1
  have hA0 : 0 < A := by linarith
  have hzA : z = A⁻¹ := by rw [hA, inv_inv]
  have hApow : A ^ (1 - p) = z ^ (p - 1) := by
    rw [hzA, Real.inv_rpow hA0.le, ← Real.rpow_neg hA0.le]; congr 1; ring
  -- pointwise bounds
  have hub : ∀ ξ, 0 < ξ → |u ξ| ≤ Cq * ξ ^ (-p) := by
    intro ξ hξ
    have h1 := c09_aux_cut_R2c ξ
    have hW : ξ ^ p ≤ |y| + ξ ^ p := by linarith [abs_nonneg y]
    have hξp := Real.rpow_pos_of_pos hξ p
    calc |u ξ| = |1 - rho ξ| * |c09_q_bounds_q p R y ξ| := abs_mul _ _
      _ ≤ 1 * (Cq * (|y| + ξ ^ p)⁻¹) := by
          gcongr
          · rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
          · exact hq ξ hξ
      _ ≤ Cq * ξ ^ (-p) := by
          rw [one_mul, Real.rpow_neg hξ.le]; gcongr
  have hu'b : ∀ ξ, 1 ≤ ξ → |-(deriv rho ξ) * c09_q_bounds_q p R y ξ +
      (1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ| ≤ Cu * ξ ^ (-1 - p) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith
    have h1 := c09_aux_cut_R2c ξ
    have hW : ξ ^ p ≤ |y| + ξ ^ p := by linarith [abs_nonneg y]
    have hξp := Real.rpow_pos_of_pos hξ0 p
    have hWi : (|y| + ξ ^ p)⁻¹ ≤ ξ ^ (-p) := by rw [Real.rpow_neg hξ0.le]; gcongr
    have hsplit : ξ ^ (-1 - p) = ξ ^ (-(1 : ℝ)) * ξ ^ (-p) := by
      rw [← Real.rpow_add hξ0]; ring_nf
    have e1 : |deriv rho ξ * c09_q_bounds_q p R y ξ| ≤ 2 * Bρ * Cq * ξ ^ (-1 - p) := by
      rcases le_or_gt ξ 2 with h2 | h2
      · rw [abs_mul]
        have hinv : 1 ≤ 2 * ξ ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hξ0]; linarith
        calc |deriv rho ξ| * |c09_q_bounds_q p R y ξ| ≤ Bρ * (Cq * ξ ^ (-p)) := by
              gcongr
              · exact hρb ξ
              · exact (hq ξ hξ0).trans (by gcongr)
          _ ≤ Bρ * (Cq * ξ ^ (-p)) * (2 * ξ ^ (-(1 : ℝ))) := by
              have : 0 ≤ Bρ * (Cq * ξ ^ (-p)) := by have := Real.rpow_pos_of_pos hξ0 (-p); positivity
              nlinarith
          _ = 2 * Bρ * Cq * ξ ^ (-1 - p) := by rw [hsplit]; ring
      · rw [hρz ξ h2, zero_mul, abs_zero]
        have := Real.rpow_pos_of_pos hξ0 (-1 - p); positivity
    have e2 : |(1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ| ≤ Cq * ξ ^ (-1 - p) := by
      rw [abs_mul]
      calc |1 - rho ξ| * |deriv (c09_q_bounds_q p R y) ξ| ≤ 1 * (Cq * ξ ^ (-(1 : ℝ)) * ξ ^ (-p)) := by
            gcongr
            · rw [abs_le]; constructor <;> linarith [h1.1, h1.2]
            · refine (hq' ξ hξ0).trans ?_
              have := Real.rpow_pos_of_pos hξ0 (-(1 : ℝ))
              gcongr
        _ = Cq * ξ ^ (-1 - p) := by rw [hsplit]; ring
    calc _ ≤ |-(deriv rho ξ) * c09_q_bounds_q p R y ξ| + |(1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ| :=
          abs_add_le _ _
      _ ≤ 2 * Bρ * Cq * ξ ^ (-1 - p) + Cq * ξ ^ (-1 - p) := by
          rw [neg_mul, abs_neg]; exact add_le_add e1 e2
      _ = Cu * ξ ^ (-1 - p) := by rw [hCu]; ring
  have hpos : ∀ a b : ℝ, 1 ≤ a → ∀ x ∈ uIcc a b, a ≤ b → 0 < x := fun a b ha x hx hab => by
    rw [uIcc_of_le hab] at hx; linarith [hx.1]
  have hcos : Continuous fun ξ : ℝ => Real.cos (z * ξ) := by fun_prop
  have hint : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable (fun ξ => u ξ * Real.cos (z * ξ)) volume a b :=
    fun a b ha hab => ((huc.mono fun x hx => hpos a b ha x hx hab).mul hcos.continuousOn).intervalIntegrable
  -- the integral of `|u|` on `[1, X]`
  have hIu : ∀ X, 1 ≤ X → X ≤ A → |∫ ξ in (1 : ℝ)..X, u ξ * Real.cos (z * ξ)| ≤ Cq / (1 - p) * A ^ (1 - p) := by
    intro X hX hXA
    have hb : ∀ ξ ∈ Icc (1 : ℝ) X, ‖u ξ * Real.cos (z * ξ)‖ ≤ Cq * ξ ^ (-p) := by
      intro ξ hξ
      rw [Real.norm_eq_abs, abs_mul]
      have hξ0 : 0 < ξ := by linarith [hξ.1]
      calc |u ξ| * |Real.cos (z * ξ)| ≤ Cq * ξ ^ (-p) * 1 :=
            mul_le_mul (hub ξ hξ0) (Real.abs_cos_le_one _) (abs_nonneg _)
              (mul_pos hCq (Real.rpow_pos_of_pos hξ0 _)).le
        _ = _ := mul_one _
    have := intervalIntegral.norm_integral_le_of_norm_le hX (μ := volume)
      (Eventually.of_forall fun ξ hξ => hb ξ ⟨hξ.1.le, hξ.2⟩)
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr (by
        rw [uIcc_of_le hX]; intro h; linarith [h.1]))).const_mul Cq)
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [intervalIntegral.integral_const_mul, c09_aux_int_rpow _ _ _ (by linarith) one_pos hX,
      Real.one_rpow, show -p + 1 = 1 - p by ring]
    have : X ^ (1 - p) ≤ A ^ (1 - p) := Real.rpow_le_rpow (by linarith) hXA h1p.le
    have : 0 < X ^ (1 - p) := Real.rpow_pos_of_pos (by linarith) _
    rw [mul_div_assoc', div_le_iff₀ h1p,
      show Cq / (1 - p) * A ^ (1 - p) * (1 - p) = Cq * A ^ (1 - p) by field_simp]
    nlinarith
  rcases le_or_gt T A with hTA | hTA
  · refine (hIu T hT1 hTA).trans ?_
    rw [hApow]
    have hzp := Real.rpow_pos_of_pos hz (p - 1)
    have hCu0 : 0 ≤ Cu := by rw [hCu]; positivity
    have : 0 ≤ (Cq + Cu / p + 1) * z ^ (p - 1) := by positivity
    calc Cq / (1 - p) * z ^ (p - 1) ≤ Cq / (1 - p) * z ^ (p - 1) + (Cq + Cu / p + 1) * z ^ (p - 1) :=
          le_add_of_nonneg_right this
      _ = _ := by ring
  · -- split at `A`
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 1 A le_rfl hA1) (hint A T hA1 hTA.le)]
    have h1 := hIu A hA1 le_rfl
    -- integrate by parts on `[A, T]`
    have hv : ∀ x : ℝ, HasDerivAt (fun ξ => Real.sin (z * ξ) / z) (Real.cos (z * x)) x := by
      intro x
      have h := ((hasDerivAt_id x).const_mul z).sin.div_const z
      simp only [id_eq, mul_one] at h
      convert h using 1
      field_simp
    have hu'c : IntervalIntegrable (fun ξ => -(deriv rho ξ) * c09_q_bounds_q p R y ξ +
        (1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ) volume A T := by
      refine ContinuousOn.intervalIntegrable fun x hx => ?_
      have hx0 := hpos A T hA1 x hx hTA.le
      have c1 : ContinuousAt (fun ξ => -(deriv rho ξ)) x :=
        (c09_aux_cut_R1.continuous_deriv (by simpa using c09_aux_le_inf 1)).neg.continuousAt
      have c2 : ContinuousAt (c09_q_bounds_q p R y) x :=
        (c09_aux_q_smooth p hp0 R y).continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx0)
      have c3 : ContinuousAt (deriv (c09_q_bounds_q p R y)) x :=
        (hu R hR y).2.2.2.2.continuousAt (isOpen_Ioi.mem_nhds hx0)
      have c4 : ContinuousAt (fun ξ => 1 - rho ξ) x :=
        (continuous_const.sub c09_aux_cut_R1.continuous).continuousAt
      exact ((c1.mul c2).add (c4.mul c3)).continuousWithinAt
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := A) (b := T) (u := u)
      (u' := fun ξ => -(deriv rho ξ) * c09_q_bounds_q p R y ξ + (1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ)
      (v := fun ξ => Real.sin (z * ξ) / z) (v' := fun ξ => Real.cos (z * ξ))
      (fun x hx => hud x (hpos A T hA1 x hx hTA.le)) (fun x _ => hv x) hu'c
      (hcos.intervalIntegrable A T)
    have huT : u T = 0 := by
      simp only [hudef]; rw [c09_aux_q_zero_big p R y T (by linarith) (by linarith)]; ring
    rw [huT, zero_mul, zero_sub] at hibp
    rw [hibp]
    have hAu : |u A * (Real.sin (z * A) / z)| ≤ Cq * A ^ (1 - p) := by
      rw [abs_mul, abs_div, abs_of_pos hz]
      have hs := Real.abs_sin_le_one (z * A)
      calc |u A| * (|Real.sin (z * A)| / z) ≤ Cq * A ^ (-p) * (1 / z) := by
            gcongr
            exact hub A hA0
        _ = Cq * A ^ (1 - p) := by
            rw [one_div, ← hA, mul_assoc, ← Real.rpow_add_one hA0.ne']; ring_nf
    have hI2 : |∫ ξ in A..T, (-(deriv rho ξ) * c09_q_bounds_q p R y ξ +
        (1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ) * (Real.sin (z * ξ) / z)| ≤ Cu / p * A ^ (1 - p) := by
      have hb : ∀ ξ ∈ Icc A T, ‖(-(deriv rho ξ) * c09_q_bounds_q p R y ξ +
          (1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ) * (Real.sin (z * ξ) / z)‖ ≤
          A * (Cu * ξ ^ (-1 - p)) := by
        intro ξ hξ
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hz, mul_comm]
        have hs := Real.abs_sin_le_one (z * ξ)
        calc |Real.sin (z * ξ)| / z * |_| ≤ 1 / z * (Cu * ξ ^ (-1 - p)) := by
              gcongr
              exact hu'b ξ (by linarith [hξ.1])
          _ = _ := by rw [one_div]
      have := intervalIntegral.norm_integral_le_of_norm_le hTA.le (μ := volume)
        (Eventually.of_forall fun ξ hξ => hb ξ ⟨hξ.1.le, hξ.2⟩)
        (((intervalIntegral.intervalIntegrable_rpow (Or.inr (by
          rw [uIcc_of_le hTA.le]; intro h; linarith [h.1]))).const_mul Cu).const_mul A)
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        c09_aux_int_rpow _ _ _ (by linarith) hA0 hTA.le, show -1 - p + 1 = -p by ring]
      have hT0 : 0 ≤ T ^ (-p) := (Real.rpow_pos_of_pos (by linarith) _).le
      have : (T ^ (-p) - A ^ (-p)) / -p ≤ A ^ (-p) / p := by
        rw [div_neg, ← neg_div, neg_sub]; apply div_le_div_of_nonneg_right _ hp0.le; linarith
      calc A * (Cu * ((T ^ (-p) - A ^ (-p)) / -p)) ≤ A * (Cu * (A ^ (-p) / p)) := by gcongr
        _ = Cu / p * (A * A ^ (-p)) := by ring
        _ = Cu / p * A ^ (1 - p) := by
            rw [show (1 : ℝ) - p = 1 + -p by ring, Real.rpow_add hA0, Real.rpow_one]
    calc _ ≤ |∫ ξ in (1 : ℝ)..A, u ξ * Real.cos (z * ξ)| +
          |-(u A * (Real.sin (z * A) / z)) - ∫ ξ in A..T, (-(deriv rho ξ) * c09_q_bounds_q p R y ξ +
            (1 - rho ξ) * deriv (c09_q_bounds_q p R y) ξ) * (Real.sin (z * ξ) / z)| := abs_add_le _ _
      _ ≤ Cq / (1 - p) * A ^ (1 - p) + (Cq * A ^ (1 - p) + Cu / p * A ^ (1 - p)) := by
          gcongr
          refine (abs_sub _ _).trans ?_
          rw [abs_neg]; exact add_le_add hAu hI2
      _ ≤ _ := by
          rw [hApow]
          have := Real.rpow_pos_of_pos hz (p - 1)
          nlinarith

/-- Generic tail estimate for the second `m_{2,0}` bound (integration by parts on `[A,T]`). -/
theorem c09_aux_m20_tail (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (q : ℝ → ℝ)
    (hqs : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi 0)) (Cs Bρ Y z A T : ℝ) (hCs : 0 < Cs) (hBρ : 0 ≤ Bρ)
    (hY : 0 ≤ Y) (hρb : ∀ u, |deriv rho u| ≤ Bρ) (hρz : ∀ u, 2 < u → deriv rho u = 0)
    (hqs1 : ∀ ξ, 0 < ξ → |deriv q ξ| ≤ Cs * ξ ^ (p - 1) * Y)
    (hqs2 : ∀ ξ, 0 < ξ → |iteratedDeriv 2 q ξ| ≤ Cs * ξ ^ (p - 2) * Y)
    (hq'T : deriv q T = 0) (hz : 0 < z) (hA1 : 1 ≤ A) (hzA : z * A = 1) (hAT : A < T) :
    |∫ ξ in A..T, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)| ≤
      (Cs + (2 * Bρ + 1) * Cs / (1 - p)) * Y * A ^ p := by
  have hp0 : 0 < p := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hA0 : 0 < A := by linarith
  have hzi : 1 / z = A := by rw [div_eq_iff hz.ne']; linarith
  have hpos : ∀ x ∈ uIcc A T, 0 < x := fun x hx => by rw [uIcc_of_le hAT.le] at hx; linarith [hx.1]
  have h1ρ : ∀ ξ, |1 - rho ξ| ≤ 1 := fun ξ => by
    have := c09_aux_cut_R2c ξ; rw [abs_le]; constructor <;> linarith
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv q) (Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp (by simpa using hqs)).2
  have hqd : ∀ ξ, 0 < ξ → HasDerivAt (deriv q) (iteratedDeriv 2 q ξ) ξ := by
    intro ξ hξ
    have := ((hd.differentiableOn (by simp) ξ hξ).differentiableAt (isOpen_Ioi.mem_nhds hξ)).hasDerivAt
    rwa [iteratedDeriv_succ, iteratedDeriv_one]
  have hq'c : ContinuousOn (deriv q) (Ioi 0) := hd.continuousOn
  have hq2c : ContinuousOn (iteratedDeriv 2 q) (Ioi 0) := by
    rw [show iteratedDeriv 2 q = deriv (deriv q) by rw [iteratedDeriv_succ, iteratedDeriv_one]]
    exact hd.continuousOn_deriv_of_isOpen isOpen_Ioi (by simpa using c09_aux_le_inf 1)
  have hρd : ∀ x, HasDerivAt rho (deriv rho x) x := fun x =>
    (c09_aux_cut_R1.differentiable (by simp) x).hasDerivAt
  have hρc : Continuous (deriv rho) := c09_aux_cut_R1.continuous_deriv (by simpa using c09_aux_le_inf 1)
  have hsin : Continuous fun ξ : ℝ => Real.sin (z * ξ) := by fun_prop
  have hw : ∀ x ∈ uIcc A T, HasDerivAt (fun ξ => (1 - rho ξ) * deriv q ξ)
      (-(deriv rho x) * deriv q x + (1 - rho x) * iteratedDeriv 2 q x) x := by
    intro x hx
    convert ((hρd x).const_sub 1).mul (hqd x (hpos x hx)) using 1
  have hw'c : IntervalIntegrable (fun ξ => -(deriv rho ξ) * deriv q ξ + (1 - rho ξ) * iteratedDeriv 2 q ξ)
      volume A T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have hx0 := hpos x hx
    exact (((hρc.neg.continuousAt).mul (hq'c.continuousAt (isOpen_Ioi.mem_nhds hx0))).add
      ((continuous_const.sub c09_aux_cut_R1.continuous).continuousAt.mul
        (hq2c.continuousAt (isOpen_Ioi.mem_nhds hx0)))).continuousWithinAt
  have hvc : ∀ x : ℝ, HasDerivAt (fun ξ => -(Real.cos (z * ξ) / z)) (Real.sin (z * x)) x := by
    intro x
    have h := (((hasDerivAt_id x).const_mul z).cos.div_const z).neg
    simp only [id_eq, mul_one] at h
    convert h using 1
    field_simp
  have hibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := A) (b := T)
    (u := fun ξ => (1 - rho ξ) * deriv q ξ)
    (u' := fun ξ => -(deriv rho ξ) * deriv q ξ + (1 - rho ξ) * iteratedDeriv 2 q ξ)
    (v := fun ξ => -(Real.cos (z * ξ) / z)) (v' := fun ξ => Real.sin (z * ξ))
    hw (fun x _ => hvc x) hw'c (hsin.intervalIntegrable A T)
  simp only [hq'T, mul_zero, zero_mul, zero_sub] at hibp2
  rw [hibp2]
  have hAw : |(1 - rho A) * deriv q A * -(Real.cos (z * A) / z)| ≤ Cs * Y * A ^ p := by
    rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hz]
    have hc := Real.abs_cos_le_one (z * A)
    calc |1 - rho A| * |deriv q A| * (|Real.cos (z * A)| / z) ≤
        1 * (Cs * A ^ (p - 1) * Y) * (1 / z) := by
          gcongr
          · exact h1ρ A
          · exact hqs1 A hA0
      _ = Cs * Y * (A ^ (p - 1) * A) := by rw [hzi]; ring
      _ = _ := by rw [← Real.rpow_add_one hA0.ne']; ring_nf
  have hI : |∫ ξ in A..T, (-(deriv rho ξ) * deriv q ξ + (1 - rho ξ) * iteratedDeriv 2 q ξ) *
      -(Real.cos (z * ξ) / z)| ≤ (2 * Bρ + 1) * Cs / (1 - p) * Y * A ^ p := by
    have hb : ∀ ξ ∈ Icc A T, ‖(-(deriv rho ξ) * deriv q ξ + (1 - rho ξ) * iteratedDeriv 2 q ξ) *
        -(Real.cos (z * ξ) / z)‖ ≤ (A * ((2 * Bρ + 1) * Cs * Y)) * ξ ^ (p - 2) := by
      intro ξ hξ
      have hξ0 : 0 < ξ := by linarith [hξ.1]
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_div, abs_of_pos hz]
      have hc := Real.abs_cos_le_one (z * ξ)
      have hξp2 := Real.rpow_pos_of_pos hξ0 (p - 2)
      have e1 : |-(deriv rho ξ) * deriv q ξ| ≤ 2 * Bρ * Cs * Y * ξ ^ (p - 2) := by
        rcases le_or_gt ξ 2 with h2 | h2
        · rw [abs_mul, abs_neg]
          have hpp : ξ ^ (p - 1) ≤ 2 * ξ ^ (p - 2) := by
            rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one hξ0.ne']; nlinarith
          calc |deriv rho ξ| * |deriv q ξ| ≤ Bρ * (Cs * ξ ^ (p - 1) * Y) := by
                gcongr
                · exact hρb ξ
                · exact hqs1 ξ hξ0
            _ ≤ Bρ * (Cs * (2 * ξ ^ (p - 2)) * Y) := by gcongr
            _ = _ := by ring
        · rw [hρz ξ h2]; simp only [neg_zero, zero_mul, abs_zero]; positivity
      have e2 : |(1 - rho ξ) * iteratedDeriv 2 q ξ| ≤ Cs * Y * ξ ^ (p - 2) := by
        rw [abs_mul]
        calc |1 - rho ξ| * |iteratedDeriv 2 q ξ| ≤ 1 * (Cs * ξ ^ (p - 2) * Y) := by
              gcongr
              · exact h1ρ ξ
              · exact hqs2 ξ hξ0
          _ = _ := by ring
      calc |-(deriv rho ξ) * deriv q ξ + (1 - rho ξ) * iteratedDeriv 2 q ξ| * (|Real.cos (z * ξ)| / z)
          ≤ (2 * Bρ * Cs * Y * ξ ^ (p - 2) + Cs * Y * ξ ^ (p - 2)) * (1 / z) := by
            gcongr
            exact (abs_add_le _ _).trans (add_le_add e1 e2)
        _ = _ := by rw [hzi]; ring
    have := intervalIntegral.norm_integral_le_of_norm_le hAT.le (μ := volume)
      (Eventually.of_forall fun ξ hξ => hb ξ ⟨hξ.1.le, hξ.2⟩)
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr (by
        rw [uIcc_of_le hAT.le]; intro h; linarith [h.1]))).const_mul _)
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [intervalIntegral.integral_const_mul, c09_aux_int_rpow _ _ _ (by linarith) hA0 hAT.le,
      show p - 2 + 1 = p - 1 by ring]
    have hTp : 0 ≤ T ^ (p - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
    have : (T ^ (p - 1) - A ^ (p - 1)) / (p - 1) ≤ A ^ (p - 1) / (1 - p) := by
      have e : (T ^ (p - 1) - A ^ (p - 1)) / (p - 1) = (A ^ (p - 1) - T ^ (p - 1)) / (1 - p) := by
        rw [show p - 1 = -(1 - p) by ring, div_neg, ← neg_div, neg_sub]
      rw [e]; apply div_le_div_of_nonneg_right _ h1p.le; linarith
    calc A * ((2 * Bρ + 1) * Cs * Y) * ((T ^ (p - 1) - A ^ (p - 1)) / (p - 1)) ≤
        A * ((2 * Bρ + 1) * Cs * Y) * (A ^ (p - 1) / (1 - p)) := by gcongr
      _ = (2 * Bρ + 1) * Cs / (1 - p) * Y * (A ^ (p - 1) * A) := by ring
      _ = _ := by rw [← Real.rpow_add_one hA0.ne']; ring_nf
  calc _ ≤ |(1 - rho A) * deriv q A * -(Real.cos (z * A) / z)| +
        |∫ ξ in A..T, (-(deriv rho ξ) * deriv q ξ + (1 - rho ξ) * iteratedDeriv 2 q ξ) *
          -(Real.cos (z * ξ) / z)| := by
        rw [neg_sub_left]; exact (abs_neg _).le.trans ((abs_add_le _ _).trans (le_of_eq (add_comm _ _)))
    _ ≤ Cs * Y * A ^ p + (2 * Bρ + 1) * Cs / (1 - p) * Y * A ^ p := add_le_add hAw hI
    _ = _ := by ring

/-- Generic `χ'` term estimate for the second `m_{2,0}` bound. -/
theorem c09_aux_m20_a (q : ℝ → ℝ) (hqc : ContinuousOn q (Ioi 0)) (Cq Bρ W z T : ℝ) (hCq : 0 < Cq)
    (hW : 0 ≤ W) (hρz : ∀ u, 2 < u → deriv rho u = 0) (hq1 : ∀ ξ, 0 < ξ → |q ξ| ≤ Cq * W)
    (hz : 0 < z) (hT1 : 1 ≤ T) :
    |∫ ξ in (1 : ℝ)..T, -(deriv rho ξ) * q ξ * (Real.sin (z * ξ) / z)| ≤
      2 * Cq * W * ∫ u, |deriv rho u| := by
  have hρc : Continuous (deriv rho) := c09_aux_cut_R1.continuous_deriv (by simpa using c09_aux_le_inf 1)
  have hb : ∀ ξ ∈ Icc (1 : ℝ) T, ‖-(deriv rho ξ) * q ξ * (Real.sin (z * ξ) / z)‖ ≤
      (2 * Cq * W) * |deriv rho ξ| := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    rw [Real.norm_eq_abs]
    rcases le_or_gt ξ 2 with h2 | h2
    · rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_pos hz]
      have hs : |Real.sin (z * ξ)| ≤ z * ξ := by
        exact Real.abs_sin_le_abs.trans (le_of_eq (abs_of_pos (mul_pos hz hξ0)))
      have hs' : |Real.sin (z * ξ)| / z ≤ 2 := by
        rw [div_le_iff₀ hz]; nlinarith
      calc |deriv rho ξ| * |q ξ| * (|Real.sin (z * ξ)| / z) ≤ |deriv rho ξ| * (Cq * W) * 2 := by
            gcongr; exact hq1 ξ hξ0
        _ = _ := by ring
    · rw [hρz ξ h2]; simp
  have := intervalIntegral.norm_integral_le_of_norm_le hT1 (μ := volume)
    (Eventually.of_forall fun ξ hξ => hb ξ ⟨hξ.1.le, hξ.2⟩)
    ((hρc.abs.intervalIntegrable 1 T).const_mul _)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  rw [intervalIntegral.integral_const_mul]
  gcongr
  rw [intervalIntegral.integral_of_le hT1]
  exact setIntegral_le_integral c09_aux_cut_I1 (Eventually.of_forall fun _ => abs_nonneg _)

/-- Generic small-`ξ` estimate for the second `m_{2,0}` bound (`|sin(zξ)| ≤ zξ` on `[1,X]`). -/
theorem c09_aux_m20_small (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (q : ℝ → ℝ)
    (hq'c : ContinuousOn (deriv q) (Ioi 0)) (Cs Y z A X : ℝ) (hCs : 0 < Cs) (hY : 0 ≤ Y)
    (hqs1 : ∀ ξ, 0 < ξ → |deriv q ξ| ≤ Cs * ξ ^ (p - 1) * Y) (hz : 0 < z) (hzA : z * A = 1)
    (hX : 1 ≤ X) (hXA : X ≤ A) :
    |∫ ξ in (1 : ℝ)..X, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)| ≤ Cs / (p + 1) * Y * A ^ p := by
  have hp0 : 0 < p := by linarith
  have hA0 : 0 < A := by linarith
  have h1ρ : ∀ ξ, |1 - rho ξ| ≤ 1 := fun ξ => by
    have := c09_aux_cut_R2c ξ; rw [abs_le]; constructor <;> linarith
  have hb : ∀ ξ ∈ Icc (1 : ℝ) X, ‖(1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)‖ ≤
      (Cs * Y * z) * ξ ^ p := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hs : |Real.sin (z * ξ)| ≤ z * ξ := by
      exact Real.abs_sin_le_abs.trans (le_of_eq (abs_of_pos (mul_pos hz hξ0)))
    calc |1 - rho ξ| * |deriv q ξ| * |Real.sin (z * ξ)| ≤ 1 * (Cs * ξ ^ (p - 1) * Y) * (z * ξ) := by
          gcongr
          · exact h1ρ ξ
          · exact hqs1 ξ hξ0
      _ = (Cs * Y * z) * (ξ ^ (p - 1) * ξ) := by ring
      _ = _ := by rw [← Real.rpow_add_one hξ0.ne']; ring_nf
  have := intervalIntegral.norm_integral_le_of_norm_le hX (μ := volume)
    (Eventually.of_forall fun ξ hξ => hb ξ ⟨hξ.1.le, hξ.2⟩)
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)), Real.one_rpow]
  have hXp : X ^ (p + 1) ≤ A ^ (p + 1) := Real.rpow_le_rpow (by linarith) hXA (by linarith)
  have hAp : z * A ^ (p + 1) = A ^ p := by
    rw [Real.rpow_add_one hA0.ne', ← mul_assoc, mul_comm z, mul_assoc, hzA, mul_one]
  calc Cs * Y * z * ((X ^ (p + 1) - 1) / (p + 1)) ≤ Cs * Y * z * (A ^ (p + 1) / (p + 1)) := by
        gcongr; linarith
    _ = Cs / (p + 1) * Y * (z * A ^ (p + 1)) := by ring
    _ = _ := by rw [hAp]

/-- Second bound: for `|y| ≥ 1`, `R ≥ R₀(y)`, `0 < z ≤ 1`:
`|∫₁^{2R+1} (1-χ)q cos(zξ)| ≤ C (|y|^{-2} z^{-p-1} + |y|^{-1})`. -/
theorem c09_aux_m20_second (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ y R : ℝ, c09_truncation_R0 p y ≤ R → 1 ≤ |y| → ∀ z : ℝ, 0 < z → z ≤ 1 →
      |∫ ξ in (1 : ℝ)..(2 * R + 1), (1 - rho ξ) * c09_q_bounds_q p R y ξ * Real.cos (z * ξ)| ≤
        C * ((|y| ^ 2)⁻¹ * z ^ (-p - 1) + |y|⁻¹) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Cq, Bρ, hCq, hBρ, hρb, hρz, hu⟩ := c09_aux_u20 p hp hp1
  obtain ⟨-, ⟨Cs, hCs, -, hsharp⟩, -⟩ := c09_q_bounds p hp hp1
  set Iρ : ℝ := ∫ u, |deriv rho u| with hIρ
  have hIρ0 : 0 ≤ Iρ := integral_nonneg fun _ => abs_nonneg _
  have h1p : 0 < 1 - p := by linarith
  set K : ℝ := Cs / (p + 1) + Cs + (2 * Bρ + 1) * Cs / (1 - p) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K + 2 * Cq * Iρ + 1, by positivity, fun y R hR hy z hz hz1 => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  obtain ⟨hq, -, hud, huc, hq'c⟩ := hu R hR2 y
  set q := c09_q_bounds_q p R y with hqdef
  set u : ℝ → ℝ := fun ξ => (1 - rho ξ) * q ξ with hudef
  set T : ℝ := 2 * R + 1 with hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hy0 : 0 < |y| := by linarith
  have hy2 : 0 < (|y| ^ 2)⁻¹ := by positivity
  set A : ℝ := z⁻¹ with hA
  have hA1 : 1 ≤ A := by rw [hA]; exact one_le_inv₀ hz |>.mpr hz1
  have hA0 : 0 < A := by linarith
  have hzA : z * A = 1 := by rw [hA]; field_simp
  have hApow : A ^ (p + 1) = z ^ (-p - 1) := by
    rw [hA, Real.inv_rpow hz.le, ← Real.rpow_neg hz.le]; congr 1; ring
  have hpos : ∀ a b : ℝ, 1 ≤ a → ∀ x ∈ uIcc a b, a ≤ b → 0 < x := fun a b ha x hx hab => by
    rw [uIcc_of_le hab] at hx; linarith [hx.1]
  -- smoothness facts
  have hqs := c09_aux_q_smooth p hp0 R y
  have hqd : ∀ ξ, 0 < ξ → HasDerivAt (deriv q) (iteratedDeriv 2 q ξ) ξ := by
    intro ξ hξ
    have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv q) (Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp (by simpa using hqs)).2
    have := ((hd.differentiableOn (by simp) ξ hξ).differentiableAt
      (isOpen_Ioi.mem_nhds hξ)).hasDerivAt
    rwa [iteratedDeriv_succ, iteratedDeriv_one]
  have hq2c : ContinuousOn (iteratedDeriv 2 q) (Ioi 0) := by
    intro ξ hξ
    have hd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv q) (Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp (by simpa using hqs)).2
    rw [show iteratedDeriv 2 q = deriv (deriv q) by rw [iteratedDeriv_succ, iteratedDeriv_one]]
    exact (hd.continuousOn_deriv_of_isOpen isOpen_Ioi (by simpa using c09_aux_le_inf 1)) ξ hξ
  have hρd : ∀ x, HasDerivAt rho (deriv rho x) x := fun x =>
    (c09_aux_cut_R1.differentiable (by simp) x).hasDerivAt
  have hρc : Continuous (deriv rho) := c09_aux_cut_R1.continuous_deriv (by simpa using c09_aux_le_inf 1)
  -- pointwise bounds
  have hq1 : ∀ ξ, 0 < ξ → |q ξ| ≤ Cq * |y|⁻¹ := by
    intro ξ hξ
    refine (hq ξ hξ).trans ?_
    have := Real.rpow_pos_of_pos hξ p
    gcongr; linarith
  have hqs1 : ∀ ξ, 0 < ξ → |deriv q ξ| ≤ Cs * ξ ^ (p - 1) * (|y| ^ 2)⁻¹ := by
    intro ξ hξ
    refine ((hsharp y R hR ξ hξ).1).trans ?_
    have := Real.rpow_pos_of_pos hξ p
    have := Real.rpow_pos_of_pos hξ (p - 1)
    gcongr; linarith
  have hqs2 : ∀ ξ, 0 < ξ → |iteratedDeriv 2 q ξ| ≤ Cs * ξ ^ (p - 2) * (|y| ^ 2)⁻¹ := by
    intro ξ hξ
    refine ((hsharp y R hR ξ hξ).2).trans ?_
    have := Real.rpow_pos_of_pos hξ p
    have := Real.rpow_pos_of_pos hξ (p - 2)
    gcongr; linarith
  have h1ρ : ∀ ξ, |1 - rho ξ| ≤ 1 := fun ξ => by
    have := c09_aux_cut_R2c ξ; rw [abs_le]; constructor <;> linarith
  -- `u(1) = 0`, `u(T) = 0`, `q'(T) = 0`
  have hu1 : u 1 = 0 := by
    simp only [hudef]; rw [c09_aux_cut_R2a 1 (by norm_num)]; ring
  have hqT : q =ᶠ[𝓝 T] fun _ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds (show T ∈ Ioi (2 * R) by simp only [mem_Ioi]; linarith)]
      with x hx
    exact c09_aux_q_zero_big p R y x (by linarith) (le_of_lt hx)
  have huT : u T = 0 := by simp only [hudef]; rw [hqT.eq_of_nhds]; ring
  have hq'T : deriv q T = 0 := by rw [hqT.deriv_eq]; simp
  have hv : ∀ x : ℝ, HasDerivAt (fun ξ => Real.sin (z * ξ) / z) (Real.cos (z * x)) x := by
    intro x
    have h := ((hasDerivAt_id x).const_mul z).sin.div_const z
    simp only [id_eq, mul_one] at h
    convert h using 1
    field_simp
  have hcos : Continuous fun ξ : ℝ => Real.cos (z * ξ) := by fun_prop
  have hsin : Continuous fun ξ : ℝ => Real.sin (z * ξ) := by fun_prop
  -- `u'` continuous on `[1, T]`
  have hu'c : ∀ a b : ℝ, 1 ≤ a → a ≤ b → IntervalIntegrable (fun ξ => -(deriv rho ξ) * q ξ +
      (1 - rho ξ) * deriv q ξ) volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have hx0 := hpos a b ha x hx hab
    exact (((hρc.neg.continuousAt).mul (hqs.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx0))).add
      ((continuous_const.sub c09_aux_cut_R1.continuous).continuousAt.mul
        (hq'c.continuousAt (isOpen_Ioi.mem_nhds hx0)))).continuousWithinAt
  -- first integration by parts on `[1, T]`
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := T) (u := u)
    (u' := fun ξ => -(deriv rho ξ) * q ξ + (1 - rho ξ) * deriv q ξ)
    (v := fun ξ => Real.sin (z * ξ) / z) (v' := fun ξ => Real.cos (z * ξ))
    (fun x hx => hud x (hpos 1 T le_rfl x hx hT1)) (fun x _ => hv x) (hu'c 1 T le_rfl hT1)
    (hcos.intervalIntegrable 1 T)
  rw [huT, hu1, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  show |∫ ξ in (1 : ℝ)..T, u ξ * Real.cos (z * ξ)| ≤ _
  rw [hibp, abs_neg]
  -- split `u' = -χ' q + (1-χ) q'`
  have hia : IntervalIntegrable (fun ξ => -(deriv rho ξ) * q ξ * (Real.sin (z * ξ) / z)) volume 1 T := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have hx0 := hpos 1 T le_rfl x hx hT1
    exact ((hρc.neg.continuousAt.mul (hqs.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx0))).mul
      (hsin.continuousAt.div_const z)).continuousWithinAt
  have hib : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      IntervalIntegrable (fun ξ => (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)) volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have hx0 := hpos a b ha x hx hab
    exact (((continuous_const.sub c09_aux_cut_R1.continuous).continuousAt.mul
      (hq'c.continuousAt (isOpen_Ioi.mem_nhds hx0))).mul hsin.continuousAt).continuousWithinAt
  have hsplit : ∫ ξ in (1 : ℝ)..T, (-(deriv rho ξ) * q ξ + (1 - rho ξ) * deriv q ξ) *
      (Real.sin (z * ξ) / z) = (∫ ξ in (1 : ℝ)..T, -(deriv rho ξ) * q ξ * (Real.sin (z * ξ) / z)) +
        A * ∫ ξ in (1 : ℝ)..T, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hia
      ((hib 1 T le_rfl hT1).const_mul A)]
    congr 1; funext ξ; rw [hA]; ring
  rw [hsplit]
  have ha := c09_aux_m20_a q hqs.continuousOn Cq Bρ |y|⁻¹ z T hCq (by positivity) hρz hq1 hz hT1
  have hsmall : ∀ X, 1 ≤ X → X ≤ A →
      |∫ ξ in (1 : ℝ)..X, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)| ≤ Cs / (p + 1) * (|y| ^ 2)⁻¹ * A ^ p :=
    fun X hX hXA => c09_aux_m20_small p hp hp1 q hq'c Cs (|y| ^ 2)⁻¹ z A X hCs hy2.le
      (fun ξ hξ => by have := hqs1 ξ hξ; linarith) hz hzA hX hXA
  have hb : |∫ ξ in (1 : ℝ)..T, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)| ≤ K * (|y| ^ 2)⁻¹ * A ^ p := by
    rcases le_or_gt T A with hTA | hTA
    · refine (hsmall T hT1 hTA).trans ?_
      have := Real.rpow_pos_of_pos hA0 p
      gcongr
      rw [hK]; have : 0 ≤ Cs + (2 * Bρ + 1) * Cs / (1 - p) := by positivity
      linarith
    · rw [← intervalIntegral.integral_add_adjacent_intervals (hib 1 A le_rfl hA1) (hib A T hA1 hTA.le)]
      have h1 := hsmall A hA1 le_rfl
      have hb2 := c09_aux_m20_tail p hp hp1 q hqs Cs Bρ (|y| ^ 2)⁻¹ z A T hCs hBρ hy2.le hρb hρz
        (fun ξ hξ => by have := hqs1 ξ hξ; linarith) (fun ξ hξ => by have := hqs2 ξ hξ; linarith)
        hq'T hz hA1 hzA hTA
      calc _ ≤ |∫ ξ in (1 : ℝ)..A, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)| +
            |∫ ξ in A..T, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)| := abs_add_le _ _
        _ ≤ Cs / (p + 1) * (|y| ^ 2)⁻¹ * A ^ p +
            (Cs + (2 * Bρ + 1) * Cs / (1 - p)) * (|y| ^ 2)⁻¹ * A ^ p := add_le_add h1 hb2
        _ = K * (|y| ^ 2)⁻¹ * A ^ p := by rw [hK]; ring
  -- conclusion
  have hAp1 : A * A ^ p = z ^ (-p - 1) := by
    rw [← hApow, Real.rpow_add_one hA0.ne']; ring
  calc _ ≤ |∫ ξ in (1 : ℝ)..T, -(deriv rho ξ) * q ξ * (Real.sin (z * ξ) / z)| +
        |A * ∫ ξ in (1 : ℝ)..T, (1 - rho ξ) * deriv q ξ * Real.sin (z * ξ)| := abs_add_le _ _
    _ ≤ 2 * Cq * |y|⁻¹ * Iρ + A * (K * (|y| ^ 2)⁻¹ * A ^ p) := by
        rw [hIρ]
        rw [abs_mul, abs_of_pos hA0]; exact add_le_add ha (by gcongr)
    _ = K * ((|y| ^ 2)⁻¹ * (A * A ^ p)) + 2 * Cq * Iρ * |y|⁻¹ := by ring
    _ ≤ _ := by
        rw [hAp1]
        have h1 : 0 ≤ (|y| ^ 2)⁻¹ * z ^ (-p - 1) := by
          have := Real.rpow_pos_of_pos hz (-p - 1); positivity
        have h2 : 0 ≤ |y|⁻¹ := by positivity
        have e : (K + 2 * Cq * Iρ + 1) * ((|y| ^ 2)⁻¹ * z ^ (-p - 1) + |y|⁻¹) =
            K * ((|y| ^ 2)⁻¹ * z ^ (-p - 1)) + 2 * Cq * Iρ * |y|⁻¹ +
              (K * |y|⁻¹ + 2 * Cq * Iρ * ((|y| ^ 2)⁻¹ * z ^ (-p - 1)) +
                ((|y| ^ 2)⁻¹ * z ^ (-p - 1)) + |y|⁻¹) := by ring
        rw [e]
        have : 0 ≤ K * |y|⁻¹ + 2 * Cq * Iρ * ((|y| ^ 2)⁻¹ * z ^ (-p - 1)) +
            ((|y| ^ 2)⁻¹ * z ^ (-p - 1)) + |y|⁻¹ := by positivity
        linarith

/-- Arithmetic for regions 1 and 2 of the `m_{2,0}` bound. -/
theorem c09_aux_m20_reg12 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (C1 C2 π' Cfin y t F : ℝ)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hπ' : 0 < π') (hCfin : π' * (3 * C1 + 2 * C2) ≤ Cfin)
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hfirst : |F| ≤ C1 * t ^ (p - 1))
    (hsecond : 1 ≤ |y| → |F| ≤ C2 * ((|y| ^ 2)⁻¹ * t ^ (-p - 1) + |y|⁻¹)) :
    (t ≤ jb y ^ (-1 / p) → π' * |F| ≤ Cfin * t ^ (p - 1)) ∧
    (jb y ^ (-1 / p) < t → π' * |F| ≤ Cfin * (jb y ^ (-2 : ℝ) * t ^ (-p - 1) + jb y ^ (-1 : ℝ))) := by
  have hjy := c09_aux_jb_pos y
  have hF0 := abs_nonneg F
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have htp := Real.rpow_pos_of_pos ht0 (p - 1)
    calc π' * |F| ≤ π' * (C1 * t ^ (p - 1)) := by gcongr
      _ ≤ Cfin * t ^ (p - 1) := by
          have : π' * C1 ≤ Cfin := by nlinarith
          nlinarith
  · have hjy2 : jb y ^ (-2 : ℝ) = (jb y ^ 2)⁻¹ := by
      rw [Real.rpow_neg hjy.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hjy1' : jb y ^ (-1 : ℝ) = (jb y)⁻¹ := Real.rpow_neg_one _
    have hjsq : jb y ^ 2 = 1 + y ^ 2 := by unfold jb; rw [Real.sq_sqrt (by positivity)]
    have hB : 0 ≤ jb y ^ (-2 : ℝ) * t ^ (-p - 1) := by
      have := Real.rpow_pos_of_pos ht0 (-p - 1); positivity
    have hB1 : 0 ≤ jb y ^ (-1 : ℝ) := (Real.rpow_pos_of_pos hjy _).le
    have htp := Real.rpow_pos_of_pos ht0 (-p - 1)
    rcases le_or_gt 1 |y| with hy | hy
    · have h2 := hsecond hy
      have hy0 : 0 < |y| := by linarith
      have e1 : (|y| ^ 2)⁻¹ ≤ 2 * jb y ^ (-2 : ℝ) := by
        rw [hjy2, ← div_eq_mul_inv]
        rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by norm_num), hjsq,
          sq_abs]
        nlinarith [sq_abs y]
      have e2 : |y|⁻¹ ≤ 2 * jb y ^ (-1 : ℝ) := by
        rw [hjy1', ← div_eq_mul_inv]
        rw [inv_le_comm₀ hy0 (by positivity), inv_div, div_le_iff₀ (by norm_num)]
        have : jb y ≤ 1 + |y| := by
          unfold jb; rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_abs y, abs_nonneg y]
        linarith
      calc π' * |F| ≤ π' * (C2 * ((|y| ^ 2)⁻¹ * t ^ (-p - 1) + |y|⁻¹)) := by gcongr
        _ ≤ π' * (C2 * (2 * jb y ^ (-2 : ℝ) * t ^ (-p - 1) + 2 * jb y ^ (-1 : ℝ))) := by gcongr
        _ = π' * (2 * C2) * (jb y ^ (-2 : ℝ) * t ^ (-p - 1) + jb y ^ (-1 : ℝ)) := by ring
        _ ≤ Cfin * (jb y ^ (-2 : ℝ) * t ^ (-p - 1) + jb y ^ (-1 : ℝ)) := by
            gcongr; nlinarith
    · have e1 : t ^ (p - 1) ≤ t ^ (-p - 1) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
      have e2 : 1 ≤ 2 * jb y ^ (-2 : ℝ) := by
        rw [hjy2, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul, hjsq]
        nlinarith [sq_abs y, abs_nonneg y]
      have e3 : t ^ (p - 1) ≤ 2 * jb y ^ (-2 : ℝ) * t ^ (-p - 1) := by
        calc t ^ (p - 1) ≤ t ^ (-p - 1) := e1
          _ = 1 * t ^ (-p - 1) := (one_mul _).symm
          _ ≤ 2 * jb y ^ (-2 : ℝ) * t ^ (-p - 1) := by gcongr
      have hc : π' * (2 * C1) ≤ Cfin := by nlinarith
      calc π' * |F| ≤ π' * (C1 * t ^ (p - 1)) := by gcongr
        _ ≤ π' * (C1 * (2 * jb y ^ (-2 : ℝ) * t ^ (-p - 1))) := by gcongr
        _ = π' * (2 * C1) * (jb y ^ (-2 : ℝ) * t ^ (-p - 1)) := by ring
        _ ≤ Cfin * (jb y ^ (-2 : ℝ) * t ^ (-p - 1)) := by gcongr
        _ ≤ _ := by
            have : 0 ≤ Cfin * jb y ^ (-1 : ℝ) := by
              have : 0 ≤ Cfin := le_trans (by positivity) hc
              positivity
            nlinarith

/-- Region 3 of the `m_{2,0}` bound (`|z| > 1`): `N`-fold integration by parts. -/
theorem c09_aux_m20_reg3 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (L : ℝ) (hL : 0 ≤ L) :
    ∃ Cd, 0 < Cd ∧ ∀ y R : ℝ, 2 ≤ R → ∀ z : ℝ, 1 < |z| →
      |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z).re| ≤
        Cd * (jb y ^ (-1 : ℝ) * |z| ^ (-L)) := by
  have hp0 : 0 < p := by linarith
  set N : ℕ := max 2 ⌈L⌉₊ with hN
  have hNL : L ≤ N := by rw [hN]; push_cast; exact (Nat.le_ceil L).trans (le_max_right _ _)
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; push_cast; exact le_max_left _ _
  obtain ⟨Cd, hCd, hmb⟩ := c09_aux_mk_bound p hp hp1 2 le_rfl 0 N
  refine ⟨(2 * π)⁻¹ * Cd, by positivity, fun y R hR2 z hz => ?_⟩
  have hjy := c09_aux_jb_pos y
  have ht0 : 0 < |z| := by linarith
  obtain ⟨hsupp, hvan⟩ := c09_aux_mk_supp p hp0 R hR2 2 y 0
  have hsm := c09_aux_nse_m_contDiff p hp0 R hR2 2 y 0
  have hz0 : ∀ ξ, ξ < 1 → iteratedDeriv N (linear_nonstationary_symbol_expansion_m p R 2 y 0) ξ = 0 :=
    fun ξ hξ => by rw [(hvan ξ hξ).iteratedDeriv_eq]; simp
  have hAN := c09_aux_L1_of_bound _ (hsm.continuous_iteratedDeriv N (by exact_mod_cast le_top))
    (Cd * jb y ^ (-1 : ℝ)) hz0 (fun ξ hξ => (hmb R hR2 y ξ hξ N le_rfl).trans (by
      have : ξ ^ (((2 : ℕ) : ℝ) - 2 - ((0 : ℕ) : ℝ) - N) ≤ ξ ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hξ (by push_cast; linarith)
      have h0 : jb y ^ (-((0 : ℕ) : ℝ) - 1) = jb y ^ (-1 : ℝ) := by norm_num
      rw [h0]
      have := Real.rpow_pos_of_pos hjy (-1 : ℝ)
      gcongr))
  have hdec := c09_aux_invF_decay _ hsm hsupp z N
  have htN : 0 < |z| ^ N := pow_pos ht0 N
  have hle : |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z).re| * |z| ^ N ≤
      (2 * π)⁻¹ * (Cd * jb y ^ (-1 : ℝ)) := by
    calc _ ≤ ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z‖ * |z| ^ N := by
          gcongr; exact Complex.abs_re_le_norm _
      _ ≤ _ := hdec.trans (by gcongr)
  have htL : (|z| ^ N)⁻¹ ≤ |z| ^ (-L) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht0.le]
    exact Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
  calc _ ≤ (2 * π)⁻¹ * (Cd * jb y ^ (-1 : ℝ)) * (|z| ^ N)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ htN]; exact hle
    _ ≤ (2 * π)⁻¹ * (Cd * jb y ^ (-1 : ℝ)) * |z| ^ (-L) := by
        have := Real.rpow_pos_of_pos hjy (-1 : ℝ)
        gcongr
    _ = _ := by ring

/-- Blueprint: lem:c09_m20_kernel.  Three-region bound for `Re (m_{2,0}^R(y,·))^∨(z)`, `R ≥ R₀(y)`. -/
theorem c09_m20_kernel (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C, 0 < C ∧ ∀ y R : ℝ, c09_truncation_R0 p y ≤ R → ∀ z : ℝ, z ≠ 0 →
      |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z).re| ≤
        C * c09_m20_kernel_bound p L y z := by
  obtain ⟨C1, hC1, hfirst⟩ := c09_aux_m20_first p hp hp1
  obtain ⟨C2, hC2, hsecond⟩ := c09_aux_m20_second p hp hp1
  obtain ⟨Cd, hCd, hreg3⟩ := c09_aux_m20_reg3 p hp hp1 L hL
  set π' : ℝ := (2 * π)⁻¹ with hπ'
  have hπ'0 : 0 < π' := by positivity
  refine ⟨π' * (3 * C1 + 2 * C2) + Cd + 1, by positivity, fun y R hR z hz => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hjy := c09_aux_jb_pos y
  have ht0 : 0 < |z| := abs_pos.mpr hz
  set Cfin : ℝ := π' * (3 * C1 + 2 * C2) + Cd + 1 with hCfin
  have hre := c09_aux_m20_re p hp hp1 R hR2 y z
  have hcos : ∀ ξ, Real.cos (z * ξ) = Real.cos (|z| * ξ) := by
    intro ξ
    rcases abs_choice z with h | h
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  have hF : (∫ ξ in (1 : ℝ)..(2 * R + 1), (1 - rho ξ) * c09_q_bounds_q p R y ξ * Real.cos (z * ξ)) =
      ∫ ξ in (1 : ℝ)..(2 * R + 1), (1 - rho ξ) * c09_q_bounds_q p R y ξ * Real.cos (|z| * ξ) :=
    intervalIntegral.integral_congr fun ξ _ => by
      show _ * Real.cos (z * ξ) = _ * Real.cos (|z| * ξ)
      rw [hcos]
  unfold c09_m20_kernel_bound
  split_ifs with h1 h2
  · rw [hre, hF, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
    have h11 : |z| ≤ 1 := h1.trans (Real.rpow_le_one_of_one_le_of_nonpos (c09_aux_one_le_jb y) (by
      rw [neg_div]; have : 0 < 1 / p := by positivity
      linarith))
    exact (c09_aux_m20_reg12 p hp hp1 C1 C2 π' Cfin y |z| _ hC1 hC2 hπ'0 (by rw [hCfin]; linarith)
      ht0 h11 (hfirst R hR2 y |z| ht0 h11) (fun hy => hsecond y R hR hy |z| ht0 h11)).1 h1
  · rw [hre, hF, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
    exact (c09_aux_m20_reg12 p hp hp1 C1 C2 π' Cfin y |z| _ hC1 hC2 hπ'0 (by rw [hCfin]; linarith)
      ht0 h2 (hfirst R hR2 y |z| ht0 h2) (fun hy => hsecond y R hR hy |z| ht0 h2)).2 (not_le.mp h1)
  · push Not at h2
    refine (hreg3 y R hR2 z h2).trans ?_
    have : 0 ≤ jb y ^ (-1 : ℝ) * |z| ^ (-L) := by
      have := Real.rpow_pos_of_pos hjy (-1 : ℝ); have := Real.rpow_pos_of_pos ht0 (-L); positivity
    gcongr
    rw [hCfin]; have : 0 ≤ π' * (3 * C1 + 2 * C2) := by positivity
    linarith

/-- Integral over `[0,1]` of a function dominated by the three-region bound (first two regions). -/
theorem c09_aux_m20_int (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (L C y : ℝ) (hC : 0 ≤ C)
    (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hb : ∀ t, 0 < t → t ≤ 1 → φ t ≤ C * c09_m20_kernel_bound p L y t) :
    ∫ t in (0 : ℝ)..1, φ t ≤ C * (2 / p + 1) * jb y ^ (-1 : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hjy := c09_aux_jb_pos y
  have hj1 := c09_aux_one_le_jb y
  set a : ℝ := jb y ^ (-1 / p) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hjy _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hj1 (by
    have : 0 < 1 / p := by positivity
    rw [neg_div]; linarith)
  have hap : a ^ p = jb y ^ (-1 : ℝ) := by
    rw [ha, ← Real.rpow_mul hjy.le]; congr 1; field_simp
  have hamp : a ^ (-p) = jb y := by
    rw [ha, ← Real.rpow_mul hjy.le]
    rw [show (-1 / p) * -p = (1 : ℝ) by field_simp]; simp
  have hφi : ∀ u v : ℝ, IntervalIntegrable φ volume u v := fun u v => hφ.intervalIntegrable u v
  rw [← intervalIntegral.integral_add_adjacent_intervals (hφi 0 a) (hφi a 1)]
  -- region 1
  have h1 : ∫ t in (0 : ℝ)..a, φ t ≤ ∫ t in (0 : ℝ)..a, C * t ^ (p - 1) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo ha0.le (hφi 0 a)
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C) fun t ht => ?_
    refine (hb t ht.1 (ht.2.le.trans ha1)).trans (le_of_eq ?_)
    unfold c09_m20_kernel_bound
    rw [abs_of_pos ht.1, if_pos ht.2.le]
  have h1' : ∫ t in (0 : ℝ)..a, C * t ^ (p - 1) = C * (a ^ p / p) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
    rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp0.ne']; ring
  -- region 2
  have hcont2 : ContinuousOn (fun t : ℝ => C * (jb y ^ (-2 : ℝ) * t ^ (-p - 1) + jb y ^ (-1 : ℝ)))
      (uIcc a 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_)
      continuousOn_const)
    exact fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (by
      rw [uIcc_of_le ha1] at ht; linarith [ht.1]))).continuousWithinAt
  have h2 : ∫ t in a..1, φ t ≤ ∫ t in a..1, C * (jb y ^ (-2 : ℝ) * t ^ (-p - 1) + jb y ^ (-1 : ℝ)) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo ha1 (hφi a 1)
      (hcont2.intervalIntegrable) fun t ht => ?_
    refine (hb t (ha0.trans ht.1) ht.2.le).trans (le_of_eq ?_)
    unfold c09_m20_kernel_bound
    rw [abs_of_pos (ha0.trans ht.1), if_neg (not_le.mpr ht.1), if_pos ht.2.le]
  have hnot0 : (0 : ℝ) ∉ uIcc a 1 := by rw [uIcc_of_le ha1]; intro h; linarith [h.1]
  have h2' : ∫ t in a..1, C * (jb y ^ (-2 : ℝ) * t ^ (-p - 1) + jb y ^ (-1 : ℝ)) =
      C * (jb y ^ (-2 : ℝ) * ((1 - a ^ (-p)) / (-p)) + jb y ^ (-1 : ℝ) * (1 - a)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr hnot0)).const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, hnot0⟩),
      intervalIntegral.integral_const]
    rw [show -p - 1 + 1 = -p by ring, Real.one_rpow, smul_eq_mul]; ring
  rw [hamp] at h2'
  rw [hap] at h1'
  have hj2 : jb y ^ (-2 : ℝ) * jb y = jb y ^ (-1 : ℝ) := by
    rw [show (-1 : ℝ) = -2 + 1 by norm_num, Real.rpow_add hjy, Real.rpow_one]
  have hj1' : 0 < jb y ^ (-1 : ℝ) := Real.rpow_pos_of_pos hjy _
  have hj2' : 0 < jb y ^ (-2 : ℝ) := Real.rpow_pos_of_pos hjy _
  have e2 : C * (jb y ^ (-2 : ℝ) * ((1 - jb y) / (-p)) + jb y ^ (-1 : ℝ) * (1 - a)) ≤
      C * (jb y ^ (-1 : ℝ) / p + jb y ^ (-1 : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    have : jb y ^ (-2 : ℝ) * ((1 - jb y) / (-p)) = (jb y ^ (-1 : ℝ) - jb y ^ (-2 : ℝ)) / p := by
      rw [← hj2]; field_simp; ring
    rw [this]
    have : jb y ^ (-1 : ℝ) * (1 - a) ≤ jb y ^ (-1 : ℝ) := by nlinarith
    have : (jb y ^ (-1 : ℝ) - jb y ^ (-2 : ℝ)) / p ≤ jb y ^ (-1 : ℝ) / p := by
      apply div_le_div_of_nonneg_right _ hp0.le; linarith
    linarith
  calc _ ≤ C * (jb y ^ (-1 : ℝ) / p) + C * (jb y ^ (-1 : ℝ) / p + jb y ^ (-1 : ℝ)) := by
        linarith
    _ = C * (2 / p + 1) * jb y ^ (-1 : ℝ) := by ring

/-- Blueprint: lem:c09_m10_m00_kernel.  `∂_z m_{1,0}^∨ = m_{2,0}^∨`, `∂_z m_{0,0}^∨ = m_{1,0}^∨`,
and `|Re ∂_z m_{0,0}^∨(z)| ≤ C_L ⟨y⟩^{-1} ⟨z⟩^{-L}` for `R ≥ R₀(y)`. -/
theorem c09_m10_m00_kernel (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ y R : ℝ, 2 ≤ R → ∀ z : ℝ,
      HasDerivAt (invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0))
        (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z) z ∧
      HasDerivAt (invFourierT (linear_nonstationary_symbol_expansion_m p R 0 y 0))
        (invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0) z) z) ∧
    (∀ L : ℝ, 0 ≤ L → ∃ C, 0 < C ∧ ∀ y R : ℝ, c09_truncation_R0 p y ≤ R → ∀ z : ℝ,
      |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 0 y 0)) z).re| ≤
        C * jb y ^ (-1 : ℝ) * jb z ^ (-L)) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, hrel, -⟩ := c09_mjk_bounds p hp hp1
  -- `iξ m_{j,0} = m_{j+1,0}`
  have hrel' : ∀ y R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 1 →
      (fun ξ : ℝ => Complex.I * (ξ : ℂ) * linear_nonstationary_symbol_expansion_m p R j y 0 ξ) =
        linear_nonstationary_symbol_expansion_m p R (j + 1) y 0 := by
    intro y R hR j hj
    funext ξ
    rcases le_or_gt ξ 0 with hξ | hξ
    · rw [c09_aux_m0_nonpos p R j y ξ hξ, c09_aux_m0_nonpos p R (j + 1) y ξ hξ, mul_zero]
    · rw [hrel R hR j (by omega) y ξ hξ, hrel R hR (j + 1) (by omega) y ξ hξ, pow_succ]; ring
  have hder : ∀ y R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 1 → ∀ z : ℝ,
      HasDerivAt (invFourierT (linear_nonstationary_symbol_expansion_m p R j y 0))
        (invFourierT (linear_nonstationary_symbol_expansion_m p R (j + 1) y 0) z) z := by
    intro y R hR j hj z
    obtain ⟨hsupp, -⟩ := c09_aux_mk_supp p hp0 R hR j y 0
    have := c09_aux_invF_hasDerivAt _ (c09_aux_nse_m_contDiff p hp0 R hR j y 0).continuous hsupp z
    rwa [hrel' y R hR j hj] at this
  refine ⟨fun y R hR z => ⟨hder y R hR 1 le_rfl z, hder y R hR 0 (by norm_num) z⟩, fun L hL => ?_⟩
  obtain ⟨C2, hC2, hm20⟩ := c09_m20_kernel p hp hp1 L hL
  set N : ℕ := ⌈L⌉₊ + 1 with hN
  have hNL : L ≤ N := by rw [hN]; push_cast; linarith [Nat.le_ceil L]
  have hN1 : 1 ≤ N := by omega
  obtain ⟨Cm, hCm, hmb⟩ := c09_aux_mk_bound p hp hp1 1 (by norm_num) 0 N
  set K1 : ℝ := 2 * C2 * (2 / p + 1) * 2 ^ (L / 2) with hK1
  set K2 : ℝ := (2 * π)⁻¹ * Cm * Real.sqrt 2 ^ N with hK2
  refine ⟨K1 + K2, by positivity, fun y R hR z => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hjy := c09_aux_jb_pos y
  have hjz := c09_aux_jb_pos z
  have hjy1 : 0 < jb y ^ (-1 : ℝ) := Real.rpow_pos_of_pos hjy _
  have hjzL : 0 < jb z ^ (-L) := Real.rpow_pos_of_pos hjz _
  rw [(hder y R hR2 0 (by norm_num) z).deriv]
  simp only [zero_add]
  set F : ℝ → ℝ := fun t => (invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0) t).re
    with hF
  have hFd : ∀ t, HasDerivAt F (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) t).re t :=
    fun t => (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder y R hR2 1 le_rfl t))
  obtain ⟨hsupp2, -⟩ := c09_aux_mk_supp p hp0 R hR2 2 y 0
  have hm2i : Integrable (linear_nonstationary_symbol_expansion_m p R 2 y 0) :=
    (c09_aux_nse_m_contDiff p hp0 R hR2 2 y 0).continuous.integrable_of_hasCompactSupport hsupp2
  have hF'c : Continuous fun t => (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) t).re :=
    Complex.continuous_re.comp (c09_aux_invFourierT_continuous _ hm2i)
  rcases le_or_gt |z| 1 with hz | hz
  · -- `|z| ≤ 1`: `F(0) = 0` and integrate the `m_{2,0}` bound
    have hF0 : F 0 = 0 := by
      obtain ⟨r, hr⟩ := c09_aux_m_real p R 1 y 0
      simp only [hF]
      unfold invFourierT
      rw [hr]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, add_zero, pow_one]
      rw [integral_const_mul]
      have hI : ∫ a, ((r a : ℝ) : ℂ) = ((∫ a, r a : ℝ) : ℂ) := integral_ofReal
      rw [hI]
      simp [Complex.mul_re]
    have hFz : F z = ∫ t in (0 : ℝ)..z,
        (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) t).re := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFd t)
        (hF'c.intervalIntegrable _ _), hF0, sub_zero]
    set φ : ℝ → ℝ := fun t => |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) t).re|
      with hφ
    have hφc : Continuous φ := hF'c.abs
    have hφ0 : ∀ t, 0 ≤ φ t := fun t => abs_nonneg _
    have hb1 : ∀ t, 0 < t → t ≤ 1 → φ t ≤ C2 * c09_m20_kernel_bound p L y t :=
      fun t ht _ => hm20 y R hR t ht.ne'
    have hb2 : ∀ t, 0 < t → t ≤ 1 → φ (-t) ≤ C2 * c09_m20_kernel_bound p L y t := by
      intro t ht _
      have := hm20 y R hR (-t) (by linarith)
      unfold c09_m20_kernel_bound at this ⊢
      rwa [abs_neg] at this
    have i1 := c09_aux_m20_int p hp hp1 L C2 y hC2.le φ hφc hb1
    have i2 := c09_aux_m20_int p hp hp1 L C2 y hC2.le (fun t => φ (-t)) (hφc.comp continuous_neg) hb2
    rw [intervalIntegral.integral_comp_neg (f := φ), neg_zero] at i2
    have hmono : |∫ t in (0 : ℝ)..z, φ t| ≤ |∫ t in (-1 : ℝ)..1, φ t| :=
      intervalIntegral.abs_integral_mono_interval (by
        intro t ht
        rcases le_total 0 z with h0 | h0
        · rw [uIoc_of_le h0] at ht; rw [uIoc_of_le (by norm_num)]
          exact ⟨by linarith [ht.1], ht.2.trans (abs_le.mp hz).2⟩
        · rw [uIoc_of_ge h0] at ht; rw [uIoc_of_le (by norm_num)]
          exact ⟨by linarith [ht.1, (abs_le.mp hz).1], by linarith [ht.2]⟩)
        (Eventually.of_forall hφ0) (hφc.intervalIntegrable _ _)
    have hsplit : ∫ t in (-1 : ℝ)..1, φ t = (∫ t in (-1 : ℝ)..0, φ t) + ∫ t in (0 : ℝ)..1, φ t :=
      (intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable _ _)
        (hφc.intervalIntegrable _ _)).symm
    have hnn : 0 ≤ ∫ t in (-1 : ℝ)..1, φ t :=
      intervalIntegral.integral_nonneg (by norm_num) fun t _ => hφ0 t
    have hFbound : |F z| ≤ 2 * C2 * (2 / p + 1) * jb y ^ (-1 : ℝ) := by
      rw [hFz]
      have h1 := intervalIntegral.norm_integral_le_abs_integral_norm (a := 0) (b := z) (μ := volume)
        (f := fun t => (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) t).re)
      simp only [Real.norm_eq_abs] at h1
      refine h1.trans (hmono.trans ?_)
      rw [abs_of_nonneg hnn, hsplit]
      linarith
    have hjzL' : 1 ≤ 2 ^ (L / 2) * jb z ^ (-L) := by
      have hj2 : jb z ≤ Real.sqrt 2 := by
        unfold jb; apply Real.sqrt_le_sqrt
        have : z ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
        linarith
      have h1 : jb z ^ L ≤ 2 ^ (L / 2) := by
        calc jb z ^ L ≤ Real.sqrt 2 ^ L := Real.rpow_le_rpow hjz.le hj2 hL
          _ = 2 ^ (L / 2) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; ring_nf
      rw [Real.rpow_neg hjz.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hjz _), one_mul]
      exact h1
    calc |F z| ≤ 2 * C2 * (2 / p + 1) * jb y ^ (-1 : ℝ) * 1 := by rw [mul_one]; exact hFbound
      _ ≤ 2 * C2 * (2 / p + 1) * jb y ^ (-1 : ℝ) * (2 ^ (L / 2) * jb z ^ (-L)) := by gcongr
      _ = K1 * jb y ^ (-1 : ℝ) * jb z ^ (-L) := by rw [hK1]; ring
      _ ≤ (K1 + K2) * jb y ^ (-1 : ℝ) * jb z ^ (-L) := by
          gcongr; rw [hK2]; linarith [show 0 < (2 * π)⁻¹ * Cm * Real.sqrt 2 ^ N by positivity]
  · -- `|z| > 1`: integrate by parts `N` times
    obtain ⟨hsupp1, hvan1⟩ := c09_aux_mk_supp p hp0 R hR2 1 y 0
    have hsm1 := c09_aux_nse_m_contDiff p hp0 R hR2 1 y 0
    have hz0 : ∀ ξ, ξ < 1 → iteratedDeriv N (linear_nonstationary_symbol_expansion_m p R 1 y 0) ξ = 0 :=
      fun ξ hξ => by rw [(hvan1 ξ hξ).iteratedDeriv_eq]; simp
    have hL1 := c09_aux_L1_of_bound _ (hsm1.continuous_iteratedDeriv N (by exact_mod_cast le_top))
      (Cm * jb y ^ (-((0 : ℕ) : ℝ) - 1)) hz0 (fun ξ hξ => (hmb R hR2 y ξ hξ N le_rfl).trans (by
        have : ξ ^ (((1 : ℕ) : ℝ) - 2 - ((0 : ℕ) : ℝ) - N) ≤ ξ ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hξ (by
            have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
            push_cast; linarith)
        have := c09_aux_jb_pos y
        gcongr))
    have hdec := c09_aux_invF_decay _ hsm1 hsupp1 z N
    simp only [CharP.cast_eq_zero, neg_zero, zero_sub] at hL1
    have hzN : 0 < |z| ^ N := pow_pos (by linarith) N
    have hj2 : jb z ≤ Real.sqrt 2 * |z| := by
      unfold jb
      rw [show Real.sqrt 2 * |z| = Real.sqrt (2 * z ^ 2) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]]
      apply Real.sqrt_le_sqrt
      have : 1 ≤ z ^ 2 := by rw [← sq_abs]; nlinarith
      linarith
    have hjN : jb z ^ N ≤ Real.sqrt 2 ^ N * |z| ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hjz.le hj2 N
    have hnorm : ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0) z‖ * jb z ^ N ≤
        (2 * π)⁻¹ * (Cm * jb y ^ (-1 : ℝ)) * Real.sqrt 2 ^ N := by
      calc _ ≤ ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0) z‖ *
            (Real.sqrt 2 ^ N * |z| ^ N) := by gcongr
        _ = Real.sqrt 2 ^ N * (‖invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0) z‖ *
            |z| ^ N) := by ring
        _ ≤ Real.sqrt 2 ^ N * ((2 * π)⁻¹ * (Cm * jb y ^ (-1 : ℝ))) :=
            mul_le_mul_of_nonneg_left (hdec.trans (by gcongr)) (by positivity)
        _ = _ := by ring
    have hjNp : 0 < jb z ^ N := pow_pos hjz N
    have hzL : (jb z ^ N)⁻¹ ≤ jb z ^ (-L) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hjz.le]
      exact Real.rpow_le_rpow_of_exponent_le (c09_aux_one_le_jb z) (by linarith)
    have hre : |F z| ≤ ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0) z‖ :=
      Complex.abs_re_le_norm _
    have hle : ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0) z‖ ≤
        K2 * jb y ^ (-1 : ℝ) * (jb z ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hjNp]
      refine hnorm.trans (le_of_eq ?_); rw [hK2]; ring
    calc |F z| ≤ K2 * jb y ^ (-1 : ℝ) * (jb z ^ N)⁻¹ := hre.trans hle
      _ ≤ K2 * jb y ^ (-1 : ℝ) * jb z ^ (-L) := by gcongr
      _ ≤ (K1 + K2) * jb y ^ (-1 : ℝ) * jb z ^ (-L) := by
          gcongr; rw [hK1]; linarith [show 0 < 2 * C2 * (2 / p + 1) * 2 ^ (L / 2) by positivity]

/-- Sine integral on `[A,B] ⊆ [1,∞)` (integration by parts). -/
private theorem c09_aux_sinA {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) : |∫ t in A..B, Real.sin t / t| ≤ 3 := by
  have hpos : ∀ x ∈ uIcc A B, 0 < x := by
    intro x hx; rw [uIcc_of_le hAB] at hx; linarith [hx.1]
  have hu : ∀ x ∈ uIcc A B, HasDerivAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) x :=
    fun x hx => hasDerivAt_inv (hpos x hx).ne'
  have hv : ∀ x ∈ uIcc A B, HasDerivAt (fun t : ℝ => -Real.cos t) (Real.sin x) x := by
    intro x _; simpa using (Real.hasDerivAt_cos x).fun_neg
  have hcont1 : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (uIcc A B) := by
    apply ContinuousOn.neg; apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro x hx; exact pow_ne_zero 2 (hpos x hx).ne'
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hcont1.intervalIntegrable (Real.continuous_sin.intervalIntegrable _ _)
  have e : ∫ t in A..B, Real.sin t / t = ∫ t in A..B, t⁻¹ * Real.sin t := by
    congr 1; ext t; rw [div_eq_inv_mul]
  rw [e, hibp]
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have h1 : |B⁻¹ * -Real.cos B| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hB0]
    calc B⁻¹ * |Real.cos B| ≤ 1 * 1 := by
          gcongr
          · exact inv_le_one_of_one_le₀ (by linarith)
          · exact Real.abs_cos_le_one B
      _ = 1 := by ring
  have h2 : |A⁻¹ * -Real.cos A| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos hA0]
    calc A⁻¹ * |Real.cos A| ≤ 1 * 1 := by
          gcongr
          · exact inv_le_one_of_one_le₀ hA
          · exact Real.abs_cos_le_one A
      _ = 1 := by ring
  have h3 : |∫ x in A..B, -(x ^ 2)⁻¹ * -Real.cos x| ≤ 1 := by
    have hg : ∀ x ∈ uIcc A B, HasDerivAt (fun t : ℝ => -t⁻¹) ((x ^ 2)⁻¹) x := by
      intro x hx; simpa using (hasDerivAt_inv (hpos x hx).ne').fun_neg
    have hgi : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume A B :=
      (hcont1.neg.congr (fun x _ => by simp)).intervalIntegrable
    have hint : ∫ x in A..B, (x ^ 2)⁻¹ = -B⁻¹ - -A⁻¹ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hg hgi
    have := intervalIntegral.norm_integral_le_of_norm_le hAB
      (f := fun x : ℝ => -(x ^ 2)⁻¹ * -Real.cos x) (g := fun x : ℝ => (x ^ 2)⁻¹)
      (Filter.Eventually.of_forall fun x _ => by
        rw [Real.norm_eq_abs, neg_mul_neg, abs_mul, abs_of_nonneg (by positivity)]
        calc (x ^ 2)⁻¹ * |Real.cos x| ≤ (x ^ 2)⁻¹ * 1 := by
              gcongr; exact Real.abs_cos_le_one x
          _ = _ := by ring) hgi
    rw [Real.norm_eq_abs, hint] at this
    have : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
    have : 0 < B⁻¹ := inv_pos.mpr hB0
    linarith
  calc _ ≤ |B⁻¹ * -Real.cos B| + |A⁻¹ * -Real.cos A| + |∫ x in A..B, -(x ^ 2)⁻¹ * -Real.cos x| := by
        have := abs_sub (B⁻¹ * -Real.cos B - A⁻¹ * -Real.cos A) (∫ x in A..B, -(x ^ 2)⁻¹ * -Real.cos x)
        have := abs_sub (B⁻¹ * -Real.cos B) (A⁻¹ * -Real.cos A)
        linarith
    _ ≤ 3 := by linarith

/-- Sine integral on `[a,b] ⊆ (0,1]`. -/
private theorem c09_aux_sinB {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) : |∫ t in a..b, Real.sin t / t| ≤ 1 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun t => Real.sin t / t) (fun x hx => by
      rw [uIoc_of_le hab] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0]
      rw [div_le_one hx0]
      exact (Real.abs_sin_le_abs).trans (le_of_eq (abs_of_pos hx0)))
  rw [Real.norm_eq_abs] at this
  rw [abs_of_nonneg (by linarith : 0 ≤ b - a)] at this
  linarith

-- Not in Mathlib: uniform bound for the sine integral (proved here by integration by
-- parts, `c09_aux_sinA`, `c09_aux_sinB`).
/-- Blueprint: lem:c09_sine_integral_bounded.  `|∫_a^b sin t / t dt| ≤ C_Si` for `0 < a < b`, and
`|∫₁^ξ sin(zη)/η dη| ≤ C_Si` for `ξ ≥ 1`. -/
theorem c09_sine_integral_bounded :
    ∃ C, 0 < C ∧
      (∀ a b : ℝ, 0 < a → a < b → |∫ t in a..b, Real.sin t / t| ≤ C) ∧
      (∀ z ξ : ℝ, 1 ≤ ξ → |∫ η in (1 : ℝ)..ξ, Real.sin (z * η) / η| ≤ C) := by
  have hcont : ∀ a b : ℝ, 0 < a → a ≤ b →
      IntervalIntegrable (fun t => Real.sin t / t) volume a b := by
    intro a b ha hab
    refine ContinuousOn.intervalIntegrable ?_
    refine Real.continuous_sin.continuousOn.div continuousOn_id fun x hx => ?_
    rw [uIcc_of_le hab] at hx; exact (lt_of_lt_of_le ha hx.1).ne'
  have partA : ∀ a b : ℝ, 0 < a → a ≤ b → |∫ t in a..b, Real.sin t / t| ≤ 4 := by
    intro a b ha hab
    rcases le_total b 1 with hb | hb
    · exact (c09_aux_sinB ha hab hb).trans (by norm_num)
    · rcases le_total 1 a with ha1 | ha1
      · exact (c09_aux_sinA ha1 hab).trans (by norm_num)
      · rw [← intervalIntegral.integral_add_adjacent_intervals (hcont a 1 ha ha1)
          (hcont 1 b one_pos hb)]
        have h1 := c09_aux_sinB ha ha1 le_rfl
        have h2 := c09_aux_sinA le_rfl hb
        calc _ ≤ |∫ t in a..1, Real.sin t / t| + |∫ t in (1:ℝ)..b, Real.sin t / t| := abs_add_le _ _
          _ ≤ 4 := by linarith
  have hposz : ∀ z : ℝ, 0 < z → ∀ ξ : ℝ, 1 ≤ ξ →
      |∫ η in (1 : ℝ)..ξ, Real.sin (z * η) / η| ≤ 4 := by
    intro z hz ξ hξ
    have e : ∫ η in (1 : ℝ)..ξ, Real.sin (z * η) / η =
        ∫ η in (1 : ℝ)..ξ, z * (Real.sin (z * η) / (z * η)) := by
      refine intervalIntegral.integral_congr fun η hη => ?_
      rw [uIcc_of_le hξ] at hη
      have : η ≠ 0 := (lt_of_lt_of_le one_pos hη.1).ne'
      field_simp
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun t => Real.sin t / t) hz.ne', smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hz.ne', one_mul, mul_one]
    exact partA z (z * ξ) hz (by nlinarith)
  refine ⟨4, by norm_num, fun a b ha hab => partA a b ha hab.le, fun z ξ hξ => ?_⟩
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have e : ∫ η in (1 : ℝ)..ξ, Real.sin (z * η) / η =
        -∫ η in (1 : ℝ)..ξ, Real.sin ((-z) * η) / η := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun η _ => ?_
      simp only [neg_mul, Real.sin_neg, neg_div, neg_neg]
    rw [e, abs_neg]; exact hposz (-z) (by linarith) ξ hξ
  · subst hz; simp
  · exact hposz z hz ξ hξ

/-! #### Helpers for the `k = 1` kernels -/

/-- `∫₁^X ξ^{p-1}(|y|+ξ^p)^{-3} dξ ≤ ⟨y⟩^{-2}/p`. -/
theorem c09_aux_int_pow3 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (y X : ℝ) (hX : 1 ≤ X) :
    ∫ ξ in (1 : ℝ)..X, ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹ ≤ (jb y ^ 2)⁻¹ / p := by
  have hp0 : 0 < p := by linarith
  have hW : ∀ ξ : ℝ, 0 < ξ → 0 < |y| + ξ ^ p := fun ξ hξ => by
    have := Real.rpow_pos_of_pos hξ p; positivity
  have hd : ∀ ξ ∈ uIcc (1 : ℝ) X, HasDerivAt (fun ξ : ℝ => -(((|y| + ξ ^ p) ^ 2)⁻¹) / (2 * p))
      (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹) ξ := by
    intro ξ hξ
    rw [uIcc_of_le hX] at hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have h1 : HasDerivAt (fun ξ : ℝ => |y| + ξ ^ p) (p * ξ ^ (p - 1)) ξ := by
      simpa using (Real.hasDerivAt_rpow_const (p := p) (Or.inl hξ0.ne')).const_add |y|
    have h2 := ((h1.pow 2).inv (pow_ne_zero 2 (hW ξ hξ0).ne')).neg.div_const (2 * p)
    convert h2 using 1
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hcont : ContinuousOn (fun ξ : ℝ => ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹) (uIcc 1 X) := by
    intro ξ hξ
    rw [uIcc_of_le hX] at hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have c1 : ContinuousAt (fun ξ : ℝ => ξ ^ (p - 1)) ξ :=
      Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne')
    have c2 : ContinuousAt (fun ξ : ℝ => |y| + ξ ^ p) ξ :=
      continuousAt_const.add (Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne'))
    exact (c1.mul ((c2.pow 3).inv₀ (pow_ne_zero 3 (hW ξ hξ0).ne'))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
  have hX0 : 0 < X := by linarith
  have a1 : 0 ≤ ((|y| + X ^ p) ^ 2)⁻¹ := by have := hW X hX0; positivity
  have a2 : ((|y| + (1 : ℝ) ^ p) ^ 2)⁻¹ ≤ (jb y ^ 2)⁻¹ := by
    rw [Real.one_rpow]
    have hj := c09_aux_jb_pos y
    apply inv_anti₀ (by positivity)
    have : jb y ^ 2 = 1 + y ^ 2 := by unfold jb; rw [Real.sq_sqrt (by positivity)]
    rw [this]; nlinarith [abs_nonneg y, sq_abs y]
  have : -((|y| + X ^ p) ^ 2)⁻¹ / (2 * p) - -((|y| + (1 : ℝ) ^ p) ^ 2)⁻¹ / (2 * p) ≤
      ((|y| + (1 : ℝ) ^ p) ^ 2)⁻¹ / (2 * p) := by
    have : 0 ≤ ((|y| + X ^ p) ^ 2)⁻¹ / (2 * p) := by positivity
    rw [neg_div, neg_div]; linarith
  refine this.trans ?_
  calc ((|y| + (1 : ℝ) ^ p) ^ 2)⁻¹ / (2 * p) ≤ (jb y ^ 2)⁻¹ / (2 * p) := by gcongr
    _ ≤ (jb y ^ 2)⁻¹ / p := by
        apply div_le_div_of_nonneg_left (by have := c09_aux_jb_pos y; positivity) hp0 (by linarith)

/-- The function `b = (1-χ)χ_ns θ_R` and its derivative. -/
theorem c09_aux_bfun (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ Cb, 0 < Cb ∧ ∀ R : ℝ, 2 ≤ R → ∀ y : ℝ,
      let b : ℝ → ℝ := fun ξ => (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ
      ContDiff ℝ (⊤ : ℕ∞) b ∧ (∀ ξ, |b ξ| ≤ 1) ∧
      (∀ ξ, 0 < ξ → (ξ < 1 ∨ 2 * R < ξ ∨ ξ ∉ tsupport (c09_stationary_split_chi_ns p y)) →
        b =ᶠ[𝓝 ξ] fun _ => 0) ∧
      ∫ ξ in (1 : ℝ)..(2 * R), |deriv b ξ| ≤ Cb := by
  obtain ⟨cstar, -, -, C, hC, -, -, -, hr, h2c, -, h3b, -, -, -⟩ := c09_cutoff_bounds p hp hp1
  refine ⟨2 * C 0 + 1, by have := hC 0; positivity, fun R hR y => ?_⟩
  intro b
  have hR0 : 0 < R := by linarith
  have hρ := c09_aux_cut_R1
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) :=
    (contDiff_const.sub hρ).mul (c09_aux_theta_smooth R)
  have hχ := c09_aux_chi_ns_smooth p y
  have hbeq : b = fun ξ => ((1 - rho ξ) * c09_truncation_theta R ξ) * c09_stationary_split_chi_ns p y ξ := by
    funext ξ; simp only [b]; ring
  have hbs : ContDiff ℝ (⊤ : ℕ∞) b := by rw [hbeq]; exact hu.mul hχ
  refine ⟨hbs, fun ξ => ?_, fun ξ hξ h => ?_, ?_⟩
  · obtain ⟨-, -, h3, h4⟩ := hr y ξ
    have := c09_aux_cut_R2c ξ; have := c09_aux_theta_bounds R ξ
    simp only [b]
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h3, abs_of_nonneg this.1]
    calc (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ ≤ 1 * 1 * 1 := by
          gcongr <;> linarith
      _ = 1 := by norm_num
  · rcases h with h | h | h
    · filter_upwards [isOpen_Ioo.mem_nhds (show ξ ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith)]
        with x hx
      simp only [b]; rw [c09_aux_cut_R2a x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)]; ring
    · filter_upwards [isOpen_Ioi.mem_nhds (show ξ ∈ Ioi (2 * R) from h)] with x hx
      simp only [b]
      rw [c09_aux_theta_zero R x hR0 (by rw [abs_of_pos (by linarith [mem_Ioi.mp hx])]; exact (mem_Ioi.mp hx).le)]
      ring
    · rw [notMem_tsupport_iff_eventuallyEq] at h
      filter_upwards [h] with x hx
      simp only [b]; rw [hx]; simp
  · -- `|b'| ≤ |((1-χ)θ)'| + |χ_ns'|`
    have hd : ∀ ξ, |deriv b ξ| ≤ |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ| +
        |deriv (c09_stationary_split_chi_ns p y) ξ| := by
      intro ξ
      rw [hbeq, deriv_fun_mul (hu.differentiable (by simp) ξ) (hχ.differentiable (by simp) ξ)]
      obtain ⟨-, -, h3, h4⟩ := hr y ξ
      have := c09_aux_cut_R2c ξ; have := c09_aux_theta_bounds R ξ
      have hu1 : |(1 - rho ξ) * c09_truncation_theta R ξ| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg this.1]
        calc (1 - rho ξ) * c09_truncation_theta R ξ ≤ 1 * 1 := by gcongr <;> linarith
          _ = 1 := by norm_num
      calc _ ≤ |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ *
              c09_stationary_split_chi_ns p y ξ| +
            |(1 - rho ξ) * c09_truncation_theta R ξ * deriv (c09_stationary_split_chi_ns p y) ξ| :=
            abs_add_le _ _
        _ ≤ _ := by
            rw [abs_mul, abs_mul, abs_of_nonneg h3]
            gcongr
            · calc _ ≤ |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ| * 1 := by gcongr
                _ = _ := mul_one _
            · calc _ ≤ 1 * |deriv (c09_stationary_split_chi_ns p y) ξ| := by gcongr
                _ = _ := one_mul _
    obtain ⟨i1, b1⟩ := h3b R hR
    obtain ⟨i2, b2⟩ := h2c y
    have hsub : Ioc (1 : ℝ) (2 * R) ⊆ Ioi 0 := fun ξ hξ => lt_trans one_pos hξ.1
    have hdc : Continuous (deriv b) := hbs.continuous_deriv (by simpa using c09_aux_le_inf 1)
    rw [intervalIntegral.integral_of_le (by linarith)]
    calc ∫ ξ in Ioc (1 : ℝ) (2 * R), |deriv b ξ|
        ≤ ∫ ξ in Ioc (1 : ℝ) (2 * R), (|deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ| +
            |deriv (c09_stationary_split_chi_ns p y) ξ|) :=
          setIntegral_mono_on (hdc.abs.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
            ((i1.mono_set hsub).add (i2.mono_set hsub)) measurableSet_Ioc fun ξ _ => hd ξ
      _ = (∫ ξ in Ioc (1 : ℝ) (2 * R), |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ|) +
            ∫ ξ in Ioc (1 : ℝ) (2 * R), |deriv (c09_stationary_split_chi_ns p y) ξ| :=
          integral_add (i1.mono_set hsub) (i2.mono_set hsub)
      _ ≤ (∫ ξ in Ioi (0 : ℝ), |deriv (fun ξ => (1 - rho ξ) * c09_truncation_theta R ξ) ξ|) +
            ∫ ξ in Ioi (0 : ℝ), |deriv (c09_stationary_split_chi_ns p y) ξ| :=
          add_le_add (setIntegral_mono_set i1 (Eventually.of_forall fun _ => abs_nonneg _)
              hsub.eventuallyLE)
            (setIntegral_mono_set i2 (Eventually.of_forall fun _ => abs_nonneg _)
              hsub.eventuallyLE)
      _ ≤ 2 * C 0 + 1 := by linarith

/-- Lower bound `|y - ξ^p| ≥ c(|y|+ξ^p)` and `(|y|+ξ^p)^2 ≥ ⟨y⟩^2/2` packaged for `ξ ≥ 1` in the
nonstationary support. -/
theorem c09_aux_ns_lower (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (y ξ : ℝ) (hξ : 1 ≤ ξ)
    (hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)) :
    let c : ℝ := (1 - (100 / 101 : ℝ) ^ p) / 2
    c * (|y| + ξ ^ p) ≤ |y - ξ ^ p| ∧ ((|y| + ξ ^ p) ^ 2)⁻¹ ≤ 2 * (jb y ^ 2)⁻¹ ∧
      0 < |y| + ξ ^ p := by
  intro c
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h4b, -⟩ := c09_cutoff_bounds p hp hp1
  have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < ξ) p; positivity
  refine ⟨c09_aux_good p hp0 y ξ (by linarith) hs, ?_, hW⟩
  have hb := h4b y ξ hξ
  have hjy := c09_aux_jb_pos y
  have h2 : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num [Real.rpow_neg_one]
  have : jb y ^ 2 / 2 ≤ (|y| + ξ ^ p) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hb 2
    rw [mul_pow, h2] at this; linarith
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have hj2 : 0 < jb y ^ 2 := by positivity
  rw [show 2 * (jb y ^ 2)⁻¹ * (|y| + ξ ^ p) ^ 2 = 2 * (|y| + ξ ^ p) ^ 2 / jb y ^ 2 by field_simp,
    le_div_iff₀ hj2]
  linarith

/-- `L¹` bound for `m_{2,1}`, uniform in `R`. -/
theorem c09_aux_m21_L1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y : ℝ,
      ∫ ξ, ‖linear_nonstationary_symbol_expansion_m p R 2 y 1 ξ‖ ≤ C * (jb y ^ 2)⁻¹ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Cb, hCb, hbf⟩ := c09_aux_bfun p hp hp1
  obtain ⟨-, -, -, h4⟩ := c09_mjk_bounds p hp hp1
  set c : ℝ := (1 - (100 / 101 : ℝ) ^ p) / 2 with hc
  have hc0 : 0 < c := c09_aux_cs_pos p hp0
  refine ⟨(2 * π)⁻¹ * (2 * (c ^ 2)⁻¹ * Cb + (c ^ 3)⁻¹) + 1, by positivity, fun R hR y => ?_⟩
  obtain ⟨hbs, hb1, hbz, hbint⟩ := hbf R hR y
  set b : ℝ → ℝ := fun ξ => (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ
    with hb
  have hjy := c09_aux_jb_pos y
  set m := linear_nonstationary_symbol_expansion_m p R 2 y 1 with hm
  have hmc : Continuous m := (c09_aux_nse_m_contDiff p hp0 R hR 2 y 1).continuous
  have hdbc : Continuous (deriv b) := hbs.continuous_deriv (by simpa using c09_aux_le_inf 1)
  set g : ℝ → ℝ := fun ξ => (2 * π)⁻¹ * (2 * (c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| +
    p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹)) with hg
  have hpt : ∀ ξ ∈ Icc (1 : ℝ) (2 * R), ‖m ξ‖ ≤ g ξ := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hgn : 0 ≤ g ξ := by
      have := Real.rpow_pos_of_pos hξ0 (p - 1)
      have : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; positivity
      simp only [hg]; positivity
    by_cases hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)
    · obtain ⟨hl, hW2, hW⟩ := c09_aux_ns_lower p hp hp1 y ξ hξ.1 hs
      rw [hm, (h4 R hR y ξ hξ0).1]
      rw [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have hne : 0 < |y - ξ ^ p| := lt_of_lt_of_le (by positivity) hl
      have e1 : |deriv b ξ / (y - ξ ^ p) ^ 2| ≤ 2 * (c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| := by
        rw [abs_div, abs_pow, div_eq_mul_inv]
        have : (|y - ξ ^ p| ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((|y| + ξ ^ p) ^ 2)⁻¹ := by
          rw [← mul_inv, ← mul_pow]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 2)
        calc |deriv b ξ| * (|y - ξ ^ p| ^ 2)⁻¹ ≤ |deriv b ξ| * ((c ^ 2)⁻¹ * ((|y| + ξ ^ p) ^ 2)⁻¹) := by
              gcongr
          _ ≤ |deriv b ξ| * ((c ^ 2)⁻¹ * (2 * (jb y ^ 2)⁻¹)) := by gcongr
          _ = _ := by ring
      have e2 : |p * b ξ * ξ ^ (p - 1) / (y - ξ ^ p) ^ 3| ≤
          p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹) := by
        rw [abs_div, abs_pow, abs_mul, abs_mul, abs_of_pos hp0,
          abs_of_pos (Real.rpow_pos_of_pos hξ0 _), div_eq_mul_inv]
        have : (|y - ξ ^ p| ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * ((|y| + ξ ^ p) ^ 3)⁻¹ := by
          rw [← mul_inv, ← mul_pow]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 3)
        have hb1' := hb1 ξ
        have hξp := Real.rpow_pos_of_pos hξ0 (p - 1)
        calc p * |b ξ| * ξ ^ (p - 1) * (|y - ξ ^ p| ^ 3)⁻¹
            ≤ p * 1 * ξ ^ (p - 1) * ((c ^ 3)⁻¹ * ((|y| + ξ ^ p) ^ 3)⁻¹) := by gcongr
          _ = _ := by ring
      calc 1 / (2 * π) * |deriv b ξ / (y - ξ ^ p) ^ 2 + p * b ξ * ξ ^ (p - 1) / (y - ξ ^ p) ^ 3|
          ≤ 1 / (2 * π) * (|deriv b ξ / (y - ξ ^ p) ^ 2| + |p * b ξ * ξ ^ (p - 1) / (y - ξ ^ p) ^ 3|) := by
            gcongr; exact abs_add_le _ _
        _ ≤ 1 / (2 * π) * (2 * (c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| +
            p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹)) := by gcongr
        _ = g ξ := by simp only [hg]; ring
    · have hev := hbz ξ hξ0 (Or.inr (Or.inr hs))
      have hb0 : b ξ = 0 := hev.eq_of_nhds
      have hdb0 : deriv b ξ = 0 := by rw [hev.deriv_eq]; simp
      have hb0' : (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ = 0 := hb0
      rw [hm, (h4 R hR y ξ hξ0).1]
      beta_reduce
      rw [hdb0, hb0']; simp only [zero_div, mul_zero, zero_mul, add_zero, Complex.ofReal_zero,
        norm_zero]
      exact hgn
  -- `m` vanishes off `(1, 2R)`
  have hz : ∀ ξ ∉ Ioc (1 : ℝ) (2 * R), ‖m ξ‖ = 0 := by
    intro ξ hξ
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hξ
    rw [hm, c09_aux_nse_m_zero p hp0 R hR 2 y 1 ξ (hξ.imp id le_of_lt), norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← intervalIntegral.integral_of_le (by linarith)]
  have hgc : ContinuousOn g (uIcc 1 (2 * R)) := by
    intro ξ hξ
    rw [uIcc_of_le (by linarith)] at hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; positivity
    have c1 : ContinuousAt (fun ξ : ℝ => ξ ^ (p - 1)) ξ := Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne')
    have c2 : ContinuousAt (fun ξ : ℝ => |y| + ξ ^ p) ξ :=
      continuousAt_const.add (Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne'))
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hg]
    exact continuousAt_const.mul ((continuousAt_const.mul hdbc.abs.continuousAt).add
      (continuousAt_const.mul (c1.mul ((c2.pow 3).inv₀ (pow_ne_zero 3 hW.ne')))))
  refine (intervalIntegral.integral_mono_on (by linarith) (hmc.norm.intervalIntegrable _ _)
    hgc.intervalIntegrable hpt).trans ?_
  have hi1 : IntervalIntegrable (fun ξ => |deriv b ξ|) volume 1 (2 * R) := hdbc.abs.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun ξ : ℝ => ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹) volume 1 (2 * R) := by
    refine ContinuousOn.intervalIntegrable fun ξ hξ => ?_
    rw [uIcc_of_le (by linarith)] at hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; positivity
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne')).mul
      (((continuousAt_const.add (Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne'))).pow 3).inv₀
        (pow_ne_zero 3 hW.ne'))).continuousWithinAt
  have hI := c09_aux_int_pow3 p hp hp1 y (2 * R) (by linarith)
  simp only [hg]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi1.const_mul _)
    (hi2.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hjy2 : 0 < (jb y ^ 2)⁻¹ := by positivity
  have e : p * (c ^ 3)⁻¹ * ((jb y ^ 2)⁻¹ / p) = (c ^ 3)⁻¹ * (jb y ^ 2)⁻¹ := by field_simp
  calc _ ≤ (2 * π)⁻¹ * (2 * (c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * Cb + p * (c ^ 3)⁻¹ * ((jb y ^ 2)⁻¹ / p)) := by
        gcongr
    _ ≤ _ := by
        rw [e]
        have : 0 ≤ (jb y ^ 2)⁻¹ := hjy2.le
        have h2π : 0 < (2 * π)⁻¹ := by positivity
        have : (2 * π)⁻¹ * (2 * (c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * Cb + (c ^ 3)⁻¹ * (jb y ^ 2)⁻¹) =
            (2 * π)⁻¹ * (2 * (c ^ 2)⁻¹ * Cb + (c ^ 3)⁻¹) * (jb y ^ 2)⁻¹ := by ring
        rw [this]
        nlinarith

/-- `B = b/(y-ξ^p)²` is smooth on `(0,∞)` with the derivative bound used for the `k = 1` kernels. -/
theorem c09_aux_Bfun (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (R : ℝ) (y : ℝ)
    (b : ℝ → ℝ) (hbs : ContDiff ℝ (⊤ : ℕ∞) b) (hb1 : ∀ ξ, |b ξ| ≤ 1)
    (hbz : ∀ ξ, 0 < ξ → (ξ < 1 ∨ 2 * R < ξ ∨ ξ ∉ tsupport (c09_stationary_split_chi_ns p y)) →
      b =ᶠ[𝓝 ξ] fun _ => 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => b ξ / (y - ξ ^ p) ^ 2) (Ioi 0) ∧
    ∀ ξ, 1 ≤ ξ → |deriv (fun ξ => b ξ / (y - ξ ^ p) ^ 2) ξ| ≤
      2 * ((((1 - (100 / 101 : ℝ) ^ p) / 2) ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| +
        p * (((1 - (100 / 101 : ℝ) ^ p) / 2) ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹)) := by
  have hp0 : 0 < p := by linarith
  set c : ℝ := (1 - (100 / 101 : ℝ) ^ p) / 2 with hc
  have hc0 : 0 < c := c09_aux_cs_pos p hp0
  have hne : ∀ ξ, 0 < ξ → ξ ∈ tsupport (c09_stationary_split_chi_ns p y) → y - ξ ^ p ≠ 0 := by
    intro ξ hξ hs h
    have := c09_aux_good p hp0 y ξ hξ hs
    rw [h, abs_zero] at this
    have := Real.rpow_pos_of_pos hξ p
    nlinarith [abs_nonneg y]
  have hd : ∀ ξ, 0 < ξ → HasDerivAt (fun x : ℝ => (y - x ^ p) ^ 2)
      (2 * (y - ξ ^ p) * -(p * ξ ^ (p - 1))) ξ := by
    intro ξ hξ
    have h1 : HasDerivAt (fun x : ℝ => y - x ^ p) (-(p * ξ ^ (p - 1))) ξ := by
      simpa using (Real.hasDerivAt_rpow_const (p := p) (Or.inl hξ.ne')).const_sub y
    convert h1.pow 2 using 1
    norm_num
  refine ⟨fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · have hξ0 : 0 < ξ := hξ
    by_cases hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)
    · exact (hbs.contDiffAt.div ((contDiffAt_const.sub (Real.contDiffAt_rpow_const_of_ne
        hξ0.ne')).pow 2) (pow_ne_zero 2 (hne ξ hξ0 hs))).contDiffWithinAt
    · refine ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [hbz ξ hξ0 (Or.inr (Or.inr hs))] with x hx
      show b x / _ = 0
      rw [show b x = 0 from hx, zero_div]
  · have hξ0 : 0 < ξ := by linarith
    have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; positivity
    have hξp := Real.rpow_pos_of_pos hξ0 (p - 1)
    have hrhs : 0 ≤ 2 * ((c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| +
        p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹)) := by
      have := c09_aux_jb_pos y; positivity
    by_cases hs : ξ ∈ tsupport (c09_stationary_split_chi_ns p y)
    · have hn := hne ξ hξ0 hs
      obtain ⟨hl, hW2, -⟩ := c09_aux_ns_lower p hp hp1 y ξ hξ hs
      have hder : HasDerivAt (fun ξ => b ξ / (y - ξ ^ p) ^ 2)
          ((deriv b ξ * (y - ξ ^ p) ^ 2 - b ξ * (2 * (y - ξ ^ p) * -(p * ξ ^ (p - 1)))) /
            ((y - ξ ^ p) ^ 2) ^ 2) ξ :=
        ((hbs.differentiable (by simp) ξ).hasDerivAt).div (hd ξ hξ0) (pow_ne_zero 2 hn)
      rw [hder.deriv]
      have e : (deriv b ξ * (y - ξ ^ p) ^ 2 - b ξ * (2 * (y - ξ ^ p) * -(p * ξ ^ (p - 1)))) /
          ((y - ξ ^ p) ^ 2) ^ 2 =
          deriv b ξ / (y - ξ ^ p) ^ 2 + 2 * p * b ξ * ξ ^ (p - 1) / (y - ξ ^ p) ^ 3 := by
        field_simp; ring
      rw [e]
      have hne' : 0 < |y - ξ ^ p| := lt_of_lt_of_le (by positivity) hl
      have e1 : |deriv b ξ / (y - ξ ^ p) ^ 2| ≤ 2 * (c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| := by
        rw [abs_div, abs_pow, div_eq_mul_inv]
        have : (|y - ξ ^ p| ^ 2)⁻¹ ≤ (c ^ 2)⁻¹ * ((|y| + ξ ^ p) ^ 2)⁻¹ := by
          rw [← mul_inv, ← mul_pow]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 2)
        calc |deriv b ξ| * (|y - ξ ^ p| ^ 2)⁻¹ ≤ |deriv b ξ| * ((c ^ 2)⁻¹ * ((|y| + ξ ^ p) ^ 2)⁻¹) := by
              gcongr
          _ ≤ |deriv b ξ| * ((c ^ 2)⁻¹ * (2 * (jb y ^ 2)⁻¹)) := by gcongr
          _ = _ := by ring
      have e2 : |2 * p * b ξ * ξ ^ (p - 1) / (y - ξ ^ p) ^ 3| ≤
          2 * p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹) := by
        rw [abs_div, abs_pow, abs_mul, abs_mul, abs_mul, abs_of_pos hp0, abs_two,
          abs_of_pos hξp, div_eq_mul_inv]
        have : (|y - ξ ^ p| ^ 3)⁻¹ ≤ (c ^ 3)⁻¹ * ((|y| + ξ ^ p) ^ 3)⁻¹ := by
          rw [← mul_inv, ← mul_pow]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hl 3)
        have hb1' := hb1 ξ
        calc 2 * p * |b ξ| * ξ ^ (p - 1) * (|y - ξ ^ p| ^ 3)⁻¹
            ≤ 2 * p * 1 * ξ ^ (p - 1) * ((c ^ 3)⁻¹ * ((|y| + ξ ^ p) ^ 3)⁻¹) := by gcongr
          _ = _ := by ring
      calc _ ≤ |deriv b ξ / (y - ξ ^ p) ^ 2| + |2 * p * b ξ * ξ ^ (p - 1) / (y - ξ ^ p) ^ 3| :=
            abs_add_le _ _
        _ ≤ 2 * (c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| +
            2 * p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹) := add_le_add e1 e2
        _ = _ := by ring
    · have hev : (fun ξ => b ξ / (y - ξ ^ p) ^ 2) =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) := by
        filter_upwards [hbz ξ hξ0 (Or.inr (Or.inr hs))] with x hx
        show b x / _ = 0
        rw [show b x = 0 from hx, zero_div]
      rw [hev.deriv_eq, deriv_const, abs_zero]
      exact hrhs

/-- `|∫₁^{2R} B(ξ) sin(zξ)/ξ dξ| ≤ C ⟨y⟩^{-2}` (integration by parts against the sine integral). -/
theorem c09_aux_Bsine (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y z : ℝ,
      |∫ ξ in (1 : ℝ)..(2 * R),
          (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ /
            (y - ξ ^ p) ^ 2 * (Real.sin (z * ξ) / ξ)| ≤ C * (jb y ^ 2)⁻¹ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Cb, hCb, hbf⟩ := c09_aux_bfun p hp hp1
  obtain ⟨CS, hCS, -, hSi⟩ := c09_sine_integral_bounded
  set c : ℝ := (1 - (100 / 101 : ℝ) ^ p) / 2 with hc
  have hc0 : 0 < c := c09_aux_cs_pos p hp0
  refine ⟨CS * (2 * ((c ^ 2)⁻¹ * Cb + (c ^ 3)⁻¹)) + 1, by positivity, fun R hR y z => ?_⟩
  obtain ⟨hbs, hb1, hbz, hbint⟩ := hbf R hR y
  set b : ℝ → ℝ := fun ξ => (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ
    with hb
  obtain ⟨hBs, hBd⟩ := c09_aux_Bfun p hp hp1 R y b hbs hb1 hbz
  set B : ℝ → ℝ := fun ξ => b ξ / (y - ξ ^ p) ^ 2 with hB
  have hjy := c09_aux_jb_pos y
  have hR1 : (1 : ℝ) ≤ 2 * R := by linarith
  have hpos : ∀ x ∈ uIcc (1 : ℝ) (2 * R), 0 < x := fun x hx => by
    rw [uIcc_of_le hR1] at hx; linarith [hx.1]
  -- the sine integral `S`
  set S : ℝ → ℝ := fun ξ => ∫ η in (1 : ℝ)..ξ, Real.sin (z * η) / η with hS
  have hsc : ContinuousOn (fun η : ℝ => Real.sin (z * η) / η) (Ioi 0) := fun η hη =>
    ((by fun_prop : Continuous fun η : ℝ => Real.sin (z * η)).continuousAt.div continuousAt_id
      (ne_of_gt hη)).continuousWithinAt
  have hSd : ∀ ξ, 0 < ξ → HasDerivAt S (Real.sin (z * ξ) / ξ) ξ := by
    intro ξ hξ
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
    · refine (hsc.mono fun x hx => ?_).intervalIntegrable
      rcases le_total 1 ξ with h | h
      · rw [uIcc_of_le h] at hx; exact lt_of_lt_of_le one_pos hx.1
      · rw [uIcc_of_ge h] at hx; exact lt_of_lt_of_le hξ hx.1
    · exact hsc.stronglyMeasurableAtFilter isOpen_Ioi ξ hξ
    · exact hsc.continuousAt (isOpen_Ioi.mem_nhds hξ)
  have hS1 : S 1 = 0 := by simp [hS]
  have hb2R : b (2 * R) = 0 := by
    show (1 - rho (2 * R)) * c09_stationary_split_chi_ns p y (2 * R) * c09_truncation_theta R (2 * R) = 0
    rw [c09_aux_theta_zero R (2 * R) (by linarith) (by rw [abs_of_pos (by linarith)])]
    ring
  have hB2R : B (2 * R) = 0 := by
    show b (2 * R) / _ = 0
    rw [hb2R, zero_div]
  have hBdc : ContinuousOn (deriv B) (Ioi 0) :=
    hBs.continuousOn_deriv_of_isOpen isOpen_Ioi (by simpa using c09_aux_le_inf 1)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (b := 2 * R)
    (u := B) (u' := deriv B) (v := S) (v' := fun ξ => Real.sin (z * ξ) / ξ)
    (fun x hx => ((hBs.differentiableOn (by simp) x (hpos x hx)).differentiableAt
      (isOpen_Ioi.mem_nhds (hpos x hx))).hasDerivAt)
    (fun x hx => hSd x (hpos x hx))
    ((hBdc.mono fun x hx => hpos x hx).intervalIntegrable)
    ((hsc.mono fun x hx => hpos x hx).intervalIntegrable)
  rw [hB2R, hS1, zero_mul, mul_zero, sub_self, zero_sub] at hibp
  have e : (∫ ξ in (1 : ℝ)..(2 * R), (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ *
      c09_truncation_theta R ξ / (y - ξ ^ p) ^ 2 * (Real.sin (z * ξ) / ξ)) =
      ∫ x in (1 : ℝ)..(2 * R), B x * (Real.sin (z * x) / x) := rfl
  rw [e, hibp, abs_neg]
  -- bound `|∫ B' S|`
  set g : ℝ → ℝ := fun ξ => CS * (2 * ((c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| +
    p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹))) with hg
  have hdbc : Continuous (deriv b) := hbs.continuous_deriv (by simpa using c09_aux_le_inf 1)
  have hi1 : IntervalIntegrable (fun ξ => |deriv b ξ|) volume 1 (2 * R) := hdbc.abs.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun ξ : ℝ => ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹) volume 1 (2 * R) := by
    refine ContinuousOn.intervalIntegrable fun ξ hξ => ?_
    have hξ0 := hpos ξ hξ
    have hW : 0 < |y| + ξ ^ p := by have := Real.rpow_pos_of_pos hξ0 p; positivity
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne')).mul
      (((continuousAt_const.add (Real.continuousAt_rpow_const _ _ (Or.inl hξ0.ne'))).pow 3).inv₀
        (pow_ne_zero 3 hW.ne'))).continuousWithinAt
  have hgi : IntervalIntegrable g volume 1 (2 * R) :=
    (((hi1.const_mul _).add (hi2.const_mul _)).const_mul 2).const_mul CS
  have hn := intervalIntegral.norm_integral_le_of_norm_le hR1 (μ := volume)
    (f := fun ξ => deriv B ξ * S ξ) (g := g) (Eventually.of_forall fun ξ hξ => by
      have hξ1 : 1 ≤ ξ := hξ.1.le
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hS' : |S ξ| ≤ CS := hSi z ξ hξ1
      calc |deriv B ξ| * |S ξ| ≤ (2 * ((c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * |deriv b ξ| +
          p * (c ^ 3)⁻¹ * (ξ ^ (p - 1) * ((|y| + ξ ^ p) ^ 3)⁻¹))) * CS := by
            gcongr
            · exact hBd ξ hξ1
        _ = g ξ := by simp only [hg]; ring) hgi
  rw [Real.norm_eq_abs] at hn
  refine hn.trans ?_
  have hI := c09_aux_int_pow3 p hp hp1 y (2 * R) hR1
  simp only [hg]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hjy2 : 0 < (jb y ^ 2)⁻¹ := by positivity
  calc _ ≤ CS * (2 * ((c ^ 2)⁻¹ * (jb y ^ 2)⁻¹ * Cb + p * (c ^ 3)⁻¹ * ((jb y ^ 2)⁻¹ / p))) := by
        gcongr
    _ = CS * (2 * ((c ^ 2)⁻¹ * Cb + (c ^ 3)⁻¹)) * (jb y ^ 2)⁻¹ := by field_simp
    _ ≤ _ := by nlinarith

/-- Combining a small-`z` bound and a large-`z` decay bound into `⟨z⟩^{-L}`. -/
theorem c09_aux_combine (f X Y L : ℝ) (N : ℕ) (hL : 0 ≤ L) (hNL : L ≤ N) (z : ℝ) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (h1 : |z| ≤ 1 → f ≤ X) (h2 : 1 < |z| → f * |z| ^ N ≤ Y) :
    f ≤ (X * 2 ^ (L / 2) + Y * Real.sqrt 2 ^ N) * jb z ^ (-L) := by
  have hjz := c09_aux_jb_pos z
  have hjzL : 0 < jb z ^ (-L) := Real.rpow_pos_of_pos hjz _
  have hs2 : 0 ≤ Real.sqrt 2 ^ N := by positivity
  rcases le_or_gt |z| 1 with hz | hz
  · have hj2 : jb z ≤ Real.sqrt 2 := by
      unfold jb; apply Real.sqrt_le_sqrt
      have : z ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
      linarith
    have h1' : jb z ^ L ≤ 2 ^ (L / 2) := by
      calc jb z ^ L ≤ Real.sqrt 2 ^ L := Real.rpow_le_rpow hjz.le hj2 hL
        _ = 2 ^ (L / 2) := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]; ring_nf
    have hk : 1 ≤ 2 ^ (L / 2) * jb z ^ (-L) := by
      rw [Real.rpow_neg hjz.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hjz _), one_mul]
      exact h1'
    have := h1 hz
    have : 0 ≤ Y * Real.sqrt 2 ^ N * jb z ^ (-L) := by positivity
    nlinarith
  · have hzN : 0 < |z| ^ N := pow_pos (by linarith) N
    have hj2 : jb z ≤ Real.sqrt 2 * |z| := by
      unfold jb
      rw [show Real.sqrt 2 * |z| = Real.sqrt (2 * z ^ 2) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]]
      apply Real.sqrt_le_sqrt
      have : 1 ≤ z ^ 2 := by rw [← sq_abs]; nlinarith
      linarith
    have hjN : jb z ^ N ≤ Real.sqrt 2 ^ N * |z| ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hjz.le hj2 N
    have hzL : (jb z ^ N)⁻¹ ≤ jb z ^ (-L) := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hjz.le]
      exact Real.rpow_le_rpow_of_exponent_le (c09_aux_one_le_jb z) (by linarith)
    have hf : f ≤ Y / |z| ^ N := by rw [le_div_iff₀ hzN]; exact h2 hz
    have hinv : (|z| ^ N)⁻¹ ≤ Real.sqrt 2 ^ N * (jb z ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hjz N)]
      calc (|z| ^ N)⁻¹ * jb z ^ N ≤ (|z| ^ N)⁻¹ * (Real.sqrt 2 ^ N * |z| ^ N) := by gcongr
        _ = Real.sqrt 2 ^ N := by field_simp
    calc f ≤ Y * (|z| ^ N)⁻¹ := by rw [← div_eq_mul_inv]; exact hf
      _ ≤ Y * (Real.sqrt 2 ^ N * jb z ^ (-L)) := by
          gcongr; exact hinv.trans (by gcongr)
      _ ≤ _ := by
          have : 0 ≤ X * 2 ^ (L / 2) * jb z ^ (-L) := by positivity
          nlinarith

/-- Decomposition of `Re ∂_z m_{1,1}^∨`: `Re (iξ m_{1,1})^∨ = Re m_{2,1}^∨ - (2π)⁻² ∫ B sin(zξ)/ξ`. -/
theorem c09_aux_k1_decomp (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (R : ℝ) (hR : 2 ≤ R) (y z : ℝ) :
    (invFourierT (fun ξ => Complex.I * (ξ : ℂ) * linear_nonstationary_symbol_expansion_m p R 1 y 1 ξ) z).re =
      (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 1) z).re -
        (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ ξ in (1 : ℝ)..(2 * R),
          (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ /
            (y - ξ ^ p) ^ 2 * (Real.sin (z * ξ) / ξ) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, h4⟩ := c09_mjk_bounds p hp hp1
  obtain ⟨Cb, hCb, hbf⟩ := c09_aux_bfun p hp hp1
  obtain ⟨hbs, hb1, hbz, -⟩ := hbf R hR y
  set b : ℝ → ℝ := fun ξ => (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ
    with hb
  obtain ⟨hBs, -⟩ := c09_aux_Bfun p hp hp1 R y b hbs hb1 hbz
  set B : ℝ → ℝ := fun ξ => b ξ / (y - ξ ^ p) ^ 2 with hB
  set m1 := linear_nonstationary_symbol_expansion_m p R 1 y 1 with hm1
  set m2 := linear_nonstationary_symbol_expansion_m p R 2 y 1 with hm2
  set e : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ)) with he
  have hec : Continuous e := by simp only [he]; fun_prop
  have hm1c : Continuous m1 := (c09_aux_nse_m_contDiff p hp0 R hR 1 y 1).continuous
  have hm2c : Continuous m2 := (c09_aux_nse_m_contDiff p hp0 R hR 2 y 1).continuous
  have hR1 : (1 : ℝ) ≤ 2 * R := by linarith
  -- pointwise identity on `(1, 2R]`
  have hid : ∀ ξ ∈ Ioc (1 : ℝ) (2 * R), Complex.I * (ξ : ℂ) * m1 ξ * e ξ =
      m2 ξ * e ξ + Complex.I * ((B ξ / (2 * π * ξ) : ℝ) : ℂ) * e ξ := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have h5 := (h4 R hR y ξ hξ0).2
    have hr : b ξ / (2 * π * ξ * (y - ξ ^ p) ^ 2) = B ξ / (2 * π * ξ) := by
      simp only [hB]; rw [div_div]; ring_nf
    rw [hr] at h5
    rw [mul_assoc Complex.I, h5]
    ring_nf
    simp only [Complex.I_sq]; ring
  have hz1 : ∀ ξ ∉ Ioc (1 : ℝ) (2 * R), Complex.I * (ξ : ℂ) * m1 ξ * e ξ = 0 := by
    intro ξ hξ
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hξ
    rw [hm1, c09_aux_nse_m_zero p hp0 R hR 1 y 1 ξ (hξ.imp id le_of_lt)]; ring
  have hz2 : ∀ ξ ∉ Ioc (1 : ℝ) (2 * R), m2 ξ * e ξ = 0 := by
    intro ξ hξ
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hξ
    rw [hm2, c09_aux_nse_m_zero p hp0 R hR 2 y 1 ξ (hξ.imp id le_of_lt), zero_mul]
  have hBc : ContinuousOn (fun ξ => Complex.I * ((B ξ / (2 * π * ξ) : ℝ) : ℂ) * e ξ) (Icc 1 (2 * R)) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hBat : ContinuousAt B ξ :=
      (hBs.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hξ0))
    exact (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
      (hBat.div (continuousAt_const.mul continuousAt_id) (mul_pos (by positivity) hξ0).ne')) |>.mul
        hec.continuousAt).continuousWithinAt
  have hi1 : IntegrableOn (fun ξ => m2 ξ * e ξ) (Ioc 1 (2 * R)) :=
    (hm2c.mul hec).integrableOn_Ioc
  have hi2 : IntegrableOn (fun ξ => Complex.I * ((B ξ / (2 * π * ξ) : ℝ) : ℂ) * e ξ) (Ioc 1 (2 * R)) :=
    (hBc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint : ∫ ξ : ℝ, Complex.I * (ξ : ℂ) * m1 ξ * e ξ =
      (∫ ξ : ℝ, m2 ξ * e ξ) + ∫ ξ in Ioc (1 : ℝ) (2 * R), Complex.I * ((B ξ / (2 * π * ξ) : ℝ) : ℂ) * e ξ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hz2,
      setIntegral_congr_fun measurableSet_Ioc hid, integral_add hi1 hi2]
  have hre : (∫ ξ in Ioc (1 : ℝ) (2 * R), Complex.I * ((B ξ / (2 * π * ξ) : ℝ) : ℂ) * e ξ).re =
      -((2 * π)⁻¹ * ∫ ξ in (1 : ℝ)..(2 * R), B ξ * (Real.sin (z * ξ) / ξ)) := by
    have := Complex.reCLM.integral_comp_comm hi2
    simp only [Complex.reCLM_apply] at this
    rw [← this, intervalIntegral.integral_of_le hR1, ← integral_const_mul, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun ξ _ => ?_
    have hexp : e ξ = ((Real.cos (z * ξ) : ℝ) : ℂ) + ((Real.sin (z * ξ) : ℝ) : ℂ) * Complex.I := by
      simp only [he]
      rw [show Complex.I * (z : ℂ) * (ξ : ℂ) = ((z * ξ : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hexp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_im]
    ring
  unfold invFourierT
  rw [show (∫ ξ : ℝ, Complex.I * (ξ : ℂ) * m1 ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ))) =
    ∫ ξ : ℝ, Complex.I * (ξ : ℂ) * m1 ξ * e ξ from rfl, hint]
  rw [show (∫ ξ : ℝ, m2 ξ * Complex.exp (Complex.I * (z : ℂ) * (ξ : ℂ))) = ∫ ξ, m2 ξ * e ξ from rfl]
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.add_re, hre]
  ring

/-- Blueprint: lem:c09_k1_kernels.  `Σ_{j≤1} |Re ∂_z m_{j,1}^∨| + |Re m_{2,1}^∨| ≤ C_L ⟨y⟩⁻² ⟨z⟩^{-L}`. -/
theorem c09_k1_kernels (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y z : ℝ,
      (∑ j ∈ Finset.range 2,
          |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R j y 1)) z).re|) +
        |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 1) z).re| ≤
        C * jb y ^ (-2 : ℝ) * jb z ^ (-L) := by
  have hp0 : 0 < p := by linarith
  set N : ℕ := ⌈L⌉₊ + 1 with hN
  have hNL : L ≤ N := by rw [hN]; push_cast; linarith [Nat.le_ceil L]
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈L⌉₊]
  obtain ⟨C0, hC0, h0⟩ := c09_aux_xmk_bound p hp hp1 0 (by norm_num) 1 N
  obtain ⟨C1, hC1, h1⟩ := c09_aux_xmk_bound p hp hp1 1 (by norm_num) 1 N
  obtain ⟨C2, hC2, h2⟩ := c09_aux_mk_bound p hp hp1 2 le_rfl 1 N
  obtain ⟨Cm, hCm, hm21⟩ := c09_aux_m21_L1 p hp hp1
  obtain ⟨CB, hCB, hBs⟩ := c09_aux_Bsine p hp hp1
  set π' : ℝ := (2 * π)⁻¹ with hπ'
  have hπ'0 : 0 < π' := by positivity
  set K0 : ℝ := π' * Real.sqrt 2 ^ N * (2 * C0) with hK0
  set K2 : ℝ := π' * Real.sqrt 2 ^ N * (Cm + C2) with hK2
  set K1 : ℝ := (π' * Cm + π' * π' * CB) * 2 ^ (L / 2) + π' * C1 * Real.sqrt 2 ^ N with hK1
  refine ⟨K0 + K1 + K2, by positivity, fun R hR y z => ?_⟩
  have hjy := c09_aux_jb_pos y
  have hy2 : jb y ^ (-2 : ℝ) = (jb y ^ 2)⁻¹ := by
    rw [Real.rpow_neg hjy.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hk1 : jb y ^ (-((1 : ℕ) : ℝ) - 1) = (jb y ^ 2)⁻¹ := by
    rw [← hy2]; norm_num
  have hjy2 : 0 < (jb y ^ 2)⁻¹ := by positivity
  have hjzL : 0 < jb z ^ (-L) := Real.rpow_pos_of_pos (c09_aux_jb_pos z) _
  have hexp : ∀ (a : ℝ) (ℓ : ℕ) (ξ : ℝ), 1 ≤ ξ → a ≤ -1 → (ℓ = N ∨ a ≤ -2) →
      ξ ^ ((a - ((1 : ℕ) : ℝ)) - ℓ + 1) ≤ ξ ^ (-2 : ℝ) := by
    intro a ℓ ξ hξ ha hℓ
    refine Real.rpow_le_rpow_of_exponent_le hξ ?_
    rcases hℓ with h | h
    · subst h; push_cast; linarith
    · have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ; push_cast; linarith
  -- term `j = 0`
  have t0 : |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 0 y 1)) z).re| ≤
      K0 * (jb y ^ 2)⁻¹ * jb z ^ (-L) := by
    obtain ⟨hsupp, hvan⟩ := c09_aux_mk_supp p hp0 R hR 0 y 1
    have hsm := c09_aux_nse_m_contDiff p hp0 R hR 0 y 1
    rw [(c09_aux_invF_hasDerivAt _ hsm.continuous hsupp z).deriv]
    refine (Complex.abs_re_le_norm _).trans ?_
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Complex.I * (x : ℂ) *
        linear_nonstationary_symbol_expansion_m p R 0 y 1 x) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).mul hsm
    have hz0 : ∀ ℓ : ℕ, ∀ ξ, ξ < 1 → iteratedDeriv ℓ (fun x : ℝ => Complex.I * (x : ℂ) *
        linear_nonstationary_symbol_expansion_m p R 0 y 1 x) ξ = 0 := by
      intro ℓ ξ hξ
      have hev : (fun x : ℝ => Complex.I * (x : ℂ) * linear_nonstationary_symbol_expansion_m p R 0 y 1 x)
          =ᶠ[𝓝 ξ] fun _ => 0 := (hvan ξ hξ).mono fun x hx => by simp only at hx ⊢; rw [hx, mul_zero]
      rw [hev.iteratedDeriv_eq]; simp
    have := c09_aux_kernel_generic _ hs (hsupp.mul_left (f := fun x : ℝ => Complex.I * (x : ℂ))) hz0 N
      (C0 * (jb y ^ 2)⁻¹) (fun ℓ hℓ ξ hξ => (h0 R hR y ξ hξ ℓ hℓ).trans (by
        rw [hk1]
        have : ξ ^ (((0 : ℕ) : ℝ) - 1 - ((1 : ℕ) : ℝ) - ℓ) ≤ ξ ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hξ (by
            have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ; push_cast; linarith)
        gcongr)) L hNL z
    refine this.trans (le_of_eq ?_)
    rw [hK0, hπ']; ring
  -- term `j = 2`
  obtain ⟨hsupp2, hvan2⟩ := c09_aux_mk_supp p hp0 R hR 2 y 1
  have hsm2 := c09_aux_nse_m_contDiff p hp0 R hR 2 y 1
  have hm21' : ∫ ξ, ‖linear_nonstationary_symbol_expansion_m p R 2 y 1 ξ‖ ≤ Cm * (jb y ^ 2)⁻¹ :=
    hm21 R hR y
  have t2n : ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 1) z‖ ≤
      K2 * (jb y ^ 2)⁻¹ * jb z ^ (-L) := by
    have hz0 : ∀ ξ, ξ < 1 → iteratedDeriv N (linear_nonstationary_symbol_expansion_m p R 2 y 1) ξ = 0 :=
      fun ξ hξ => by rw [(hvan2 ξ hξ).iteratedDeriv_eq]; simp
    have hAN := c09_aux_L1_of_bound _ (hsm2.continuous_iteratedDeriv N (by exact_mod_cast le_top))
      (C2 * (jb y ^ 2)⁻¹) hz0 (fun ξ hξ => (h2 R hR y ξ hξ N le_rfl).trans (by
        rw [hk1]
        have : ξ ^ (((2 : ℕ) : ℝ) - 2 - ((1 : ℕ) : ℝ) - N) ≤ ξ ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hξ (by push_cast; linarith)
        gcongr))
    have := c09_aux_invF_decay_jb _ hsm2 hsupp2 N _ _ hm21' hAN z
    refine this.trans ?_
    have hjN : jb z ^ (-(N : ℝ)) ≤ jb z ^ (-L) :=
      Real.rpow_le_rpow_of_exponent_le (c09_aux_one_le_jb z) (by linarith)
    calc (2 * π)⁻¹ * Real.sqrt 2 ^ N * (Cm * (jb y ^ 2)⁻¹ + C2 * (jb y ^ 2)⁻¹) * jb z ^ (-(N : ℝ))
        ≤ (2 * π)⁻¹ * Real.sqrt 2 ^ N * (Cm * (jb y ^ 2)⁻¹ + C2 * (jb y ^ 2)⁻¹) * jb z ^ (-L) := by
          gcongr
      _ = _ := by rw [hK2, hπ']; ring
  have t2 : |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 1) z).re| ≤
      K2 * (jb y ^ 2)⁻¹ * jb z ^ (-L) := (Complex.abs_re_le_norm _).trans t2n
  -- term `j = 1`
  have t1 : |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 1)) z).re| ≤
      K1 * (jb y ^ 2)⁻¹ * jb z ^ (-L) := by
    obtain ⟨hsupp1, hvan1⟩ := c09_aux_mk_supp p hp0 R hR 1 y 1
    have hsm1 := c09_aux_nse_m_contDiff p hp0 R hR 1 y 1
    rw [(c09_aux_invF_hasDerivAt _ hsm1.continuous hsupp1 z).deriv]
    set s : ℝ → ℂ := fun x : ℝ => Complex.I * (x : ℂ) * linear_nonstationary_symbol_expansion_m p R 1 y 1 x
      with hsdef
    have hs : ContDiff ℝ (⊤ : ℕ∞) s := (contDiff_const.mul Complex.ofRealCLM.contDiff).mul hsm1
    have hss : HasCompactSupport s := hsupp1.mul_left (f := fun x : ℝ => Complex.I * (x : ℂ))
    have hz0 : ∀ ξ, ξ < 1 → iteratedDeriv N s ξ = 0 := by
      intro ξ hξ
      have hev : s =ᶠ[𝓝 ξ] fun _ => 0 :=
        (hvan1 ξ hξ).mono fun x hx => by simp only [hsdef] at hx ⊢; rw [hx, mul_zero]
      rw [hev.iteratedDeriv_eq]; simp
    have hAN := c09_aux_L1_of_bound _ (hs.continuous_iteratedDeriv N (by exact_mod_cast le_top))
      (C1 * (jb y ^ 2)⁻¹) hz0 (fun ξ hξ => (h1 R hR y ξ hξ N le_rfl).trans (by
        rw [hk1]
        have : ξ ^ (((1 : ℕ) : ℝ) - 1 - ((1 : ℕ) : ℝ) - N) ≤ ξ ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hξ (by push_cast; linarith)
        gcongr))
    have hdec := c09_aux_invF_decay s hs hss z N
    have hsmall : |(invFourierT s z).re| ≤ (π' * Cm + π' * π' * CB) * (jb y ^ 2)⁻¹ := by
      rw [hsdef, c09_aux_k1_decomp p hp hp1 R hR y z]
      have a1 := (Complex.abs_re_le_norm _).trans
        ((c09_aux_invFourierT_norm_le (linear_nonstationary_symbol_expansion_m p R 2 y 1) z).trans
          (mul_le_mul_of_nonneg_left hm21' (by positivity)))
      have a2 := hBs R hR y z
      calc _ ≤ |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 1) z).re| +
            |(2 * π)⁻¹ * (2 * π)⁻¹ * ∫ ξ in (1 : ℝ)..(2 * R),
              (1 - rho ξ) * c09_stationary_split_chi_ns p y ξ * c09_truncation_theta R ξ /
                (y - ξ ^ p) ^ 2 * (Real.sin (z * ξ) / ξ)| := abs_sub _ _
        _ ≤ (2 * π)⁻¹ * (Cm * (jb y ^ 2)⁻¹) + (2 * π)⁻¹ * (2 * π)⁻¹ * (CB * (jb y ^ 2)⁻¹) := by
            gcongr
            rw [abs_mul, abs_of_pos (by positivity)]
            gcongr
        _ = _ := by rw [hπ']; ring
    have := c09_aux_combine (|(invFourierT s z).re|) ((π' * Cm + π' * π' * CB) * (jb y ^ 2)⁻¹)
      (π' * (C1 * (jb y ^ 2)⁻¹)) L N hL hNL z (by positivity) (by positivity)
      (fun _ => hsmall) (fun _ => by
        calc |(invFourierT s z).re| * |z| ^ N ≤ ‖invFourierT s z‖ * |z| ^ N := by
              gcongr; exact Complex.abs_re_le_norm _
          _ ≤ (2 * π)⁻¹ * ∫ ξ, ‖iteratedDeriv N s ξ‖ := hdec
          _ ≤ π' * (C1 * (jb y ^ 2)⁻¹) := by rw [hπ']; gcongr)
    refine this.trans (le_of_eq ?_)
    rw [hK1]; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hy2]
  have : (K0 + K1 + K2) * (jb y ^ 2)⁻¹ * jb z ^ (-L) =
      K0 * (jb y ^ 2)⁻¹ * jb z ^ (-L) + K1 * (jb y ^ 2)⁻¹ * jb z ^ (-L) +
        K2 * (jb y ^ 2)⁻¹ * jb z ^ (-L) := by ring
  rw [this]
  linarith

/-- Blueprint: lem:c09_k2_kernels.  For `k ≥ 2`:
`Σ_{j≤1} |∂_z m_{j,k}^∨| + |m_{2,k}^∨| ≤ C_{k,L} ⟨y⟩^{-k-1} ⟨z⟩^{-L}`. -/
theorem c09_k2_kernels (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (k : ℕ) (hk : 2 ≤ k)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ y z : ℝ,
      (∑ j ∈ Finset.range 2,
          ‖deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R j y k)) z‖) +
        ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y k) z‖ ≤
        C * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L) := by
  have hp0 : 0 < p := by linarith
  set N : ℕ := ⌈L⌉₊ with hN
  have hNL : L ≤ N := Nat.le_ceil L
  obtain ⟨C0, hC0, h0⟩ := c09_aux_xmk_bound p hp hp1 0 (by norm_num) k N
  obtain ⟨C1, hC1, h1⟩ := c09_aux_xmk_bound p hp hp1 1 (by norm_num) k N
  obtain ⟨C2, hC2, h2⟩ := c09_aux_mk_bound p hp hp1 2 le_rfl k N
  set K : ℝ := (2 * π)⁻¹ * Real.sqrt 2 ^ N * 2 with hK
  refine ⟨K * (C0 + C1 + C2), by positivity, fun R hR y z => ?_⟩
  have hjy := c09_aux_jb_pos y
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp : ∀ (a : ℝ) (ℓ : ℕ) (ξ : ℝ), 1 ≤ ξ → a ≤ 0 →
      ξ ^ ((a - k) - ℓ) ≤ ξ ^ (-2 : ℝ) := fun a ℓ ξ hξ ha =>
    Real.rpow_le_rpow_of_exponent_le hξ (by have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ; linarith)
  -- kernels for `j = 0, 1`
  have hx : ∀ j : ℕ, j ≤ 1 → ∀ Cj : ℝ, 0 < Cj →
      (∀ R : ℝ, 2 ≤ R → ∀ y ξ : ℝ, 1 ≤ ξ → ∀ ℓ ≤ N,
        ‖iteratedDeriv ℓ (fun x : ℝ => Complex.I * (x : ℂ) *
          linear_nonstationary_symbol_expansion_m p R j y k x) ξ‖ ≤
          Cj * jb y ^ (-(k : ℝ) - 1) * ξ ^ (((j : ℝ) - 1 - k) - ℓ)) →
      ‖deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R j y k)) z‖ ≤
        K * Cj * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L) := by
    intro j hj Cj hCj hb
    obtain ⟨hsupp, hvan⟩ := c09_aux_mk_supp p hp0 R hR j y k
    have hsm := c09_aux_nse_m_contDiff p hp0 R hR j y k
    rw [(c09_aux_invF_hasDerivAt _ hsm.continuous hsupp z).deriv]
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Complex.I * (x : ℂ) *
        linear_nonstationary_symbol_expansion_m p R j y k x) := by
      have hx : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Complex.I * (x : ℂ)) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      exact hx.mul hsm
    have hss : HasCompactSupport (fun x : ℝ => Complex.I * (x : ℂ) *
        linear_nonstationary_symbol_expansion_m p R j y k x) :=
      hsupp.mul_left (f := fun x : ℝ => Complex.I * (x : ℂ))
    have hz0 : ∀ ℓ : ℕ, ∀ ξ, ξ < 1 → iteratedDeriv ℓ (fun x : ℝ => Complex.I * (x : ℂ) *
        linear_nonstationary_symbol_expansion_m p R j y k x) ξ = 0 := by
      intro ℓ ξ hξ
      have hev : (fun x : ℝ => Complex.I * (x : ℂ) * linear_nonstationary_symbol_expansion_m p R j y k x)
          =ᶠ[𝓝 ξ] fun _ => 0 := (hvan ξ hξ).mono fun x hx => by simp only at hx ⊢; rw [hx, mul_zero]
      rw [hev.iteratedDeriv_eq]; simp
    have := c09_aux_kernel_generic _ hs hss hz0 N (Cj * jb y ^ (-(k : ℝ) - 1))
      (fun ℓ hℓ ξ hξ => (hb R hR y ξ hξ ℓ hℓ).trans (by
        have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
        have := hexp ((j : ℝ) - 1) ℓ ξ hξ (by linarith)
        gcongr)) L hNL z
    refine this.trans (le_of_eq ?_)
    rw [hK]; ring
  have k0 := hx 0 (by norm_num) C0 hC0 h0
  have k1 := hx 1 le_rfl C1 hC1 h1
  -- kernel for `j = 2`
  have k2 : ‖invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y k) z‖ ≤
      K * C2 * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L) := by
    obtain ⟨hsupp, hvan⟩ := c09_aux_mk_supp p hp0 R hR 2 y k
    have hsm := c09_aux_nse_m_contDiff p hp0 R hR 2 y k
    have hz0 : ∀ ℓ : ℕ, ∀ ξ, ξ < 1 →
        iteratedDeriv ℓ (linear_nonstationary_symbol_expansion_m p R 2 y k) ξ = 0 := by
      intro ℓ ξ hξ
      rw [(hvan ξ hξ).iteratedDeriv_eq]; simp
    have := c09_aux_kernel_generic _ hsm hsupp hz0 N (C2 * jb y ^ (-(k : ℝ) - 1))
      (fun ℓ hℓ ξ hξ => (h2 R hR y ξ hξ ℓ hℓ).trans (by
        have := hexp ((2 : ℕ) - 2 : ℝ) ℓ ξ hξ (by norm_num)
        gcongr)) L hNL z
    refine this.trans (le_of_eq ?_)
    rw [hK]; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have : K * (C0 + C1 + C2) * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L) =
      K * C0 * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L) + K * C1 * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L) +
        K * C2 * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L) := by ring
  rw [this]
  push_cast at k0 k1
  linarith

/-- Blueprint: lem:linear_nonstationary_leading_kernels.  Symbol bounds: the `k = 0` kernels
(`R ≥ R₀(y)`) and the `k ≥ 1` kernels (`R ≥ 2`). -/
theorem linear_nonstationary_leading_kernels (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (L : ℝ) (hL : 0 ≤ L) :
    (∃ C, 0 < C ∧ ∀ y R : ℝ, c09_truncation_R0 p y ≤ R →
      (∀ z : ℝ, |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 0 y 0)) z).re| ≤
        C * jb y ^ (-1 : ℝ) * jb z ^ (-L)) ∧
      (∀ z : ℝ, z ≠ 0 →
        |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0)) z).re| +
          |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z).re| ≤
          2 * C * c09_m20_kernel_bound p L y z)) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ C, 0 < C ∧ ∀ y R : ℝ, 2 ≤ R → ∀ z : ℝ,
      (∑ j ∈ Finset.range 2,
          |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R j y k)) z).re|) +
        |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y k) z).re| ≤
        C * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-L)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hder, h00⟩ := c09_m10_m00_kernel p hp hp1
    obtain ⟨C0, hC0, h0⟩ := h00 L hL
    obtain ⟨C2, hC2, h2⟩ := c09_m20_kernel p hp hp1 L hL
    refine ⟨max C0 C2, lt_of_lt_of_le hC0 (le_max_left _ _), fun y R hR => ⟨fun z => ?_, ?_⟩⟩
    · calc _ ≤ C0 * jb y ^ (-1 : ℝ) * jb z ^ (-L) := h0 y R hR z
        _ ≤ max C0 C2 * jb y ^ (-1 : ℝ) * jb z ^ (-L) := by
          have := c09_aux_jb_pos y; have := c09_aux_jb_pos z
          gcongr; exact le_max_left _ _
    · intro z hz
      have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
      rw [(hder y R hR2 z).1.deriv]
      have hb : 0 ≤ c09_m20_kernel_bound p L y z := by
        have := c09_aux_jb_pos y
        unfold c09_m20_kernel_bound; split_ifs <;> positivity
      have := h2 y R hR z hz
      have : C2 * c09_m20_kernel_bound p L y z ≤ max C0 C2 * c09_m20_kernel_bound p L y z :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hb
      linarith
  · intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      obtain ⟨C, hC, h⟩ := c09_k1_kernels p hp hp1 L hL
      refine ⟨C, hC, fun y R hR z => ?_⟩
      have := h R hR y z
      norm_num at this ⊢
      exact this
    · obtain ⟨C, hC, h⟩ := c09_k2_kernels p hp hp1 k hk2 L hL
      refine ⟨C, hC, fun y R hR z => le_trans ?_ (h R hR y z)⟩
      gcongr with j hj
      · exact Complex.abs_re_le_norm _
      · exact Complex.abs_re_le_norm _

/-- Blueprint: lem:c09_weighted_kernel_L1.  `h_{j,k}^R(y,z) = Re ∂_z (m_{j,k}^R(y,·))^∨(z)` for
`j = 0,1` and `Re (m_{2,k}^R(y,·))^∨(z)` for `j = 2`. -/
def c09_weighted_kernel_L1_h (p R : ℝ) (j k : ℕ) (y z : ℝ) : ℝ :=
  if j ≤ 1 then (deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R j y k)) z).re
  else (invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y k) z).re

/-- The inverse Fourier transform is continuous or identically zero; in particular measurable. -/
private theorem c09_aux_invFourierT_aesm (g : ℝ → ℂ) : Measurable (invFourierT g) := by
  by_cases hg : Integrable g
  · have : Continuous (invFourierT g) := by
      unfold invFourierT
      refine continuous_const.mul ?_
      refine continuous_of_dominated
        (F := fun (x : ℝ) (ξ : ℝ) => g ξ * Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ)))
        (bound := fun ξ => ‖g ξ‖) (fun x => ?_) (fun x => ?_) hg.norm
        (Eventually.of_forall fun ξ => by fun_prop)
      · exact hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun ξ : ℝ =>
          Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))).aestronglyMeasurable
      · exact Eventually.of_forall fun ξ => by
          rw [norm_mul, c09_aux_norm_exp_pos, mul_one]
    exact this.measurable
  · have : invFourierT g = fun _ => 0 := by
      funext x
      unfold invFourierT
      rw [integral_undef, mul_zero]
      intro hi
      apply hg
      have hc : Continuous fun ξ : ℝ => Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) := by
        fun_prop
      refine (hi.mul_bdd hc.aestronglyMeasurable
        (Eventually.of_forall fun ξ => (c09_aux_norm_exp_neg x ξ).le)).congr
        (Eventually.of_forall fun ξ => ?_)
      simp only [mul_assoc, ← Complex.exp_add]
      simp
    rw [this]; exact measurable_const

/-- `⟨z⟩^s ≤ 2^{s/2}` for `|z| ≤ 1`, `s ≥ 0`. -/
private theorem c09_aux_jb_rpow_le_small {z s : ℝ} (hz : |z| ≤ 1) (hs : 0 ≤ s) :
    jb z ^ s ≤ 2 ^ (s / 2) := by
  have h : jb z ≤ 2 ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; unfold jb; apply Real.sqrt_le_sqrt
    have : z ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
    linarith
  calc jb z ^ s ≤ (2 ^ (1 / 2 : ℝ)) ^ s := Real.rpow_le_rpow (c09_aux_jb_pos z).le h hs
    _ = 2 ^ (s / 2) := by rw [← Real.rpow_mul (by norm_num)]; ring_nf

/-- `⟨z⟩ ≤ √2 |z|` for `|z| ≥ 1`. -/
private theorem c09_aux_jb_le_large {z : ℝ} (hz : 1 ≤ |z|) : jb z ≤ Real.sqrt 2 * |z| := by
  unfold jb
  rw [← Real.sqrt_sq (abs_nonneg z), ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  rw [sq_abs]; nlinarith [sq_abs z]

/-- Domination: a nonnegative measurable function below an integrable one. -/
private theorem c09_aux_dom {f D : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hD : Integrable D) (h : ∀ᵐ z, f z ≤ D z) : Integrable f ∧ ∫ z, f z ≤ ∫ z, D z := by
  have hi : Integrable f := hD.mono' hf.aestronglyMeasurable (by
    filter_upwards [h] with z hz; rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hz)
  exact ⟨hi, integral_mono_ae hi hD h⟩

/-- Pointwise domination of the three-region kernel bound (with `L = γ+3`, weight `⟨z⟩^{γ+1}`). -/
private theorem c09_aux_B3_dom (p γ y z : ℝ) (hp0 : 0 < p) (hγ : 0 ≤ γ) (hz : z ≠ 0) :
    jb z ^ (γ + 1) * c09_m20_kernel_bound p (γ + 3) y z ≤
      (2 * 2 ^ ((γ + 3) / 2)) *
        ((Ioc 0 (jb y ^ (-1 / p))).indicator (fun x => x ^ (p - 1)) z +
          (Ioc 0 (jb y ^ (-1 / p))).indicator (fun x => x ^ (p - 1)) (-z) +
          jb y ^ (-2 : ℝ) * ((Ioc (jb y ^ (-1 / p)) 1).indicator (fun x => x ^ (-p - 1)) z +
            (Ioc (jb y ^ (-1 / p)) 1).indicator (fun x => x ^ (-p - 1)) (-z)) +
          jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ)) := by
  set a := jb y ^ (-1 / p) with ha
  have hY := c09_aux_jb_pos y
  have hZ := c09_aux_jb_pos z
  have ha0 : 0 < a := Real.rpow_pos_of_pos hY _
  have hza : 0 < |z| := abs_pos.mpr hz
  set g1 := (Ioc 0 a).indicator (fun x : ℝ => x ^ (p - 1)) with hg1
  set g2 := (Ioc a 1).indicator (fun x : ℝ => x ^ (-p - 1)) with hg2
  have g1n : ∀ x, 0 ≤ g1 x := fun x =>
    Set.indicator_nonneg (s := Ioc 0 a) (f := fun x : ℝ => x ^ (p - 1))
      (fun x (hx : x ∈ Ioc 0 a) => Real.rpow_nonneg hx.1.le _) x
  have g2n : ∀ x, 0 ≤ g2 x := fun x =>
    Set.indicator_nonneg (s := Ioc a 1) (f := fun x : ℝ => x ^ (-p - 1))
      (fun x (hx : x ∈ Ioc a 1) => Real.rpow_nonneg (ha0.trans hx.1).le _) x
  have hK1 : (2 : ℝ) ^ ((γ + 1) / 2) ≤ 2 * 2 ^ ((γ + 3) / 2) := by
    have : (2 : ℝ) ^ ((γ + 1) / 2) ≤ 2 ^ ((γ + 3) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have : (0 : ℝ) ≤ 2 ^ ((γ + 3) / 2) := by positivity
    linarith
  have hz2 : (1 : ℝ) ≤ 2 * jb z ^ (-2 : ℝ) → True := fun _ => trivial
  have t1n : 0 ≤ jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)) := by
    have := g2n z; have := g2n (-z); positivity
  have t2n : 0 ≤ jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ) := by positivity
  have t0n : 0 ≤ g1 z + g1 (-z) := by have := g1n z; have := g1n (-z); positivity
  unfold c09_m20_kernel_bound
  rw [← ha]
  split_ifs with h1 h2
  · -- `|z| ≤ a`
    have hs : g1 z + g1 (-z) = |z| ^ (p - 1) := by
      rcases lt_or_gt_of_ne hz with hn | hn
      · rw [hg1, Set.indicator_of_notMem (by simp; intro h; linarith),
          Set.indicator_of_mem (show -z ∈ Ioc 0 a by
            constructor <;> [linarith; (rw [abs_of_neg hn] at h1; exact h1)]),
          abs_of_neg hn, zero_add]
      · rw [hg1, Set.indicator_of_mem (show z ∈ Ioc 0 a by
            constructor <;> [linarith; (rw [abs_of_pos hn] at h1; exact h1)]),
          Set.indicator_of_notMem (by simp; intro h; linarith), abs_of_pos hn, add_zero]
    have hz1 : |z| ≤ 1 := h1.trans (Real.rpow_le_one_of_one_le_of_nonpos
      (c09_aux_one_le_jb y) (by rw [neg_div]; exact neg_nonpos.mpr (by positivity)))
    have hw := c09_aux_jb_rpow_le_small hz1 (show 0 ≤ γ + 1 by linarith)
    have hpos : 0 ≤ |z| ^ (p - 1) := Real.rpow_nonneg (abs_nonneg _) _
    calc jb z ^ (γ + 1) * |z| ^ (p - 1) ≤ 2 ^ ((γ + 1) / 2) * |z| ^ (p - 1) := by gcongr
      _ ≤ (2 * 2 ^ ((γ + 3) / 2)) * (g1 z + g1 (-z)) := by rw [hs]; gcongr
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  · -- `a < |z| ≤ 1`
    push Not at h1
    have hs : g2 z + g2 (-z) = |z| ^ (-p - 1) := by
      rcases lt_or_gt_of_ne hz with hn | hn
      · rw [hg2, Set.indicator_of_notMem (by simp; intro h; linarith [ha0]),
          Set.indicator_of_mem (show -z ∈ Ioc a 1 by
            rw [abs_of_neg hn] at h1 h2; exact ⟨h1, h2⟩),
          abs_of_neg hn, zero_add]
      · rw [hg2, Set.indicator_of_mem (show z ∈ Ioc a 1 by
            rw [abs_of_pos hn] at h1 h2; exact ⟨h1, h2⟩),
          Set.indicator_of_notMem (by simp; intro h; linarith [ha0]), abs_of_pos hn, add_zero]
    have hw := c09_aux_jb_rpow_le_small h2 (show 0 ≤ γ + 1 by linarith)
    have hjz : (1 : ℝ) ≤ 2 * jb z ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hZ.le, Real.rpow_two]
      have : jb z ^ 2 ≤ 2 := by
        unfold jb; rw [Real.sq_sqrt (by positivity)]
        have : z ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
        linarith
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
    have hpos : 0 ≤ jb y ^ (-2 : ℝ) * |z| ^ (-p - 1) + jb y ^ (-1 : ℝ) := by positivity
    calc jb z ^ (γ + 1) * (jb y ^ (-2 : ℝ) * |z| ^ (-p - 1) + jb y ^ (-1 : ℝ))
        ≤ 2 ^ ((γ + 1) / 2) * (jb y ^ (-2 : ℝ) * |z| ^ (-p - 1) + jb y ^ (-1 : ℝ)) := by gcongr
      _ ≤ 2 ^ ((γ + 1) / 2) * (jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)) +
            2 * (jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ))) := by
          rw [hs]; gcongr; nlinarith [Real.rpow_pos_of_pos hY (-1 : ℝ)]
      _ ≤ _ := by
          have hu : (2 : ℝ) ^ ((γ + 3) / 2) = 2 ^ ((γ + 1) / 2) * 2 := by
            rw [show (γ + 3) / 2 = (γ + 1) / 2 + 1 by ring, Real.rpow_add (by norm_num),
              Real.rpow_one]
          rw [hu]
          have hu0 : (0 : ℝ) < 2 ^ ((γ + 1) / 2) := by positivity
          set X := jb y ^ (-2 : ℝ) * (g2 z + g2 (-z))
          set Yv := jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ)
          nlinarith [mul_nonneg hu0.le t0n, mul_nonneg hu0.le t1n, mul_nonneg hu0.le t2n]
  · -- `|z| > 1`
    push Not at h2
    have hl := c09_aux_jb_le_large h2.le
    have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have hzl : jb z / Real.sqrt 2 ≤ |z| := by rw [div_le_iff₀ hs2]; linarith
    have e1 : |z| ^ (-(γ + 3)) ≤ 2 ^ ((γ + 3) / 2) * jb z ^ (-(γ + 3)) := by
      calc |z| ^ (-(γ + 3)) ≤ (jb z / Real.sqrt 2) ^ (-(γ + 3)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hzl (by linarith)
        _ = 2 ^ ((γ + 3) / 2) * jb z ^ (-(γ + 3)) := by
            rw [Real.div_rpow hZ.le hs2.le, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num),
              div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
            ring_nf
    have e2 : jb z ^ (γ + 1) * jb z ^ (-(γ + 3)) = jb z ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hZ]; congr 1; ring
    have hpos : 0 ≤ jb y ^ (-1 : ℝ) := by positivity
    calc jb z ^ (γ + 1) * (jb y ^ (-1 : ℝ) * |z| ^ (-(γ + 3)))
        ≤ jb z ^ (γ + 1) * (jb y ^ (-1 : ℝ) * (2 ^ ((γ + 3) / 2) * jb z ^ (-(γ + 3)))) := by
          gcongr
      _ = 2 ^ ((γ + 3) / 2) * (jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ)) := by rw [← e2]; ring
      _ ≤ (2 * 2 ^ ((γ + 3) / 2)) * (jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ)) := by
          have : (0 : ℝ) ≤ 2 ^ ((γ + 3) / 2) := by positivity
          nlinarith
      _ ≤ _ := by gcongr; linarith

/-- Blueprint: lem:c09_weighted_kernel_L1.  `∫ ⟨z⟩^{γ+1} |h_{j,k}^R(y,z)| dz ≤ C ⟨y⟩^{-k-1}`
for `k ≤ 4`, `R ≥ R₀(y)`. -/
theorem c09_weighted_kernel_L1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧ ∀ k : ℕ, k ≤ 4 → ∀ j : ℕ, j ≤ 2 → ∀ y R : ℝ, c09_truncation_R0 p y ≤ R →
      Integrable (fun z => jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z|) ∧
      ∫ z, jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z| ≤
        C * jb y ^ (-(k : ℝ) - 1) := by
  have hp0 : 0 < p := by linarith
  have hγ0 : 0 ≤ γ := by
    have := hγ.1; unfold beta at this
    have : 0 < (p + 1) / (2 * p) := by positivity
    have : 0 < 1 / p := by positivity
    linarith
  obtain ⟨⟨C0, hC0, h0⟩, hk⟩ := linear_nonstationary_leading_kernels p hp hp1 (γ + 3)
    (by linarith)
  obtain ⟨C1, hC1, h1⟩ := hk 1 le_rfl
  obtain ⟨C2, hC2, h2⟩ := hk 2 (by norm_num)
  obtain ⟨C3, hC3, h3⟩ := hk 3 (by norm_num)
  obtain ⟨C4, hC4, h4⟩ := hk 4 (by norm_num)
  have hI2i := c09_aux_jb_integrable (s := 2) (by norm_num)
  set I2 := ∫ z, jb z ^ (-2 : ℝ) with hI2d
  have hI2 : 0 ≤ I2 := integral_nonneg fun z => (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
  set K : ℝ := 2 * 2 ^ ((γ + 3) / 2) with hK
  have hK0 : 0 < K := by positivity
  have hdec : ∀ z, jb z ^ (γ + 1) * jb z ^ (-(γ + 3)) = jb z ^ (-2 : ℝ) := fun z => by
    rw [← Real.rpow_add (c09_aux_jb_pos z)]; congr 1; ring
  refine ⟨C0 * I2 + 2 * C0 * K * (4 / p + I2) + (C1 + C2 + C3 + C4) * I2 + 1, by positivity,
    fun k hk4 j hj y R hR => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hY := c09_aux_jb_pos y
  set Cs := C0 * I2 + 2 * C0 * K * (4 / p + I2) + (C1 + C2 + C3 + C4) * I2 + 1 with hCs
  have hmeas : Measurable (fun z => jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z|) := by
    refine ((c09_aux_jb_continuous.rpow_const
      (fun y => Or.inl (c09_aux_jb_pos y).ne')).measurable).mul ?_
    refine Measurable.abs ?_
    unfold c09_weighted_kernel_L1_h
    split_ifs
    · exact Complex.measurable_re.comp (measurable_deriv _)
    · exact Complex.measurable_re.comp (c09_aux_invFourierT_aesm _)
  have hnn : ∀ z, 0 ≤ jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z| := fun z =>
    mul_nonneg (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le (abs_nonneg _)
  -- the `jb^{-L}` case
  have decay_case : ∀ Cx : ℝ, 0 ≤ Cx → Cx * I2 ≤ Cs →
      (∀ z, |c09_weighted_kernel_L1_h p R j k y z| ≤
        Cx * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-(γ + 3))) →
      Integrable (fun z => jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z|) ∧
      ∫ z, jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z| ≤
        Cs * jb y ^ (-(k : ℝ) - 1) := by
    intro Cx hCx hCxs hb
    have hD : Integrable (fun z => (Cx * jb y ^ (-(k : ℝ) - 1)) * jb z ^ (-2 : ℝ)) :=
      hI2i.const_mul _
    obtain ⟨hi, hint⟩ := c09_aux_dom hmeas hnn hD (Eventually.of_forall fun z => by
      calc jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z|
          ≤ jb z ^ (γ + 1) * (Cx * jb y ^ (-(k : ℝ) - 1) * jb z ^ (-(γ + 3))) :=
            mul_le_mul_of_nonneg_left (hb z) (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
        _ = (Cx * jb y ^ (-(k : ℝ) - 1)) * jb z ^ (-2 : ℝ) := by rw [← hdec z]; ring)
    refine ⟨hi, hint.trans ?_⟩
    rw [integral_const_mul]
    have hyk : 0 ≤ jb y ^ (-(k : ℝ) - 1) := (Real.rpow_pos_of_pos hY _).le
    calc Cx * jb y ^ (-(k : ℝ) - 1) * I2 = (Cx * I2) * jb y ^ (-(k : ℝ) - 1) := by ring
      _ ≤ Cs * jb y ^ (-(k : ℝ) - 1) := mul_le_mul_of_nonneg_right hCxs hyk
  -- `h` versus the summed kernels
  have hsum : ∀ (k : ℕ) (z : ℝ), |c09_weighted_kernel_L1_h p R j k y z| ≤
      (∑ i ∈ Finset.range 2,
        |(deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R i y k)) z).re|) +
      |(invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y k) z).re| := by
    intro k z
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    unfold c09_weighted_kernel_L1_h
    have a0 := abs_nonneg
      ((deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 0 y k)) z).re)
    have a1 := abs_nonneg
      ((deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y k)) z).re)
    have a2 := abs_nonneg ((invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y k) z).re)
    split_ifs with hj1
    · interval_cases j <;> linarith
    · linarith
  have hCsum : 0 ≤ C1 + C2 + C3 + C4 := by positivity
  have hCs1 : C0 * I2 ≤ Cs := by
    rw [hCs]; nlinarith [mul_nonneg (mul_nonneg hC0.le hK0.le)
      (show 0 ≤ 4 / p + I2 by positivity), mul_nonneg hCsum hI2]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · -- `j = k = 0`
      refine decay_case C0 hC0.le hCs1 fun z => ?_
      unfold c09_weighted_kernel_L1_h
      simp only [show (0 : ℕ) ≤ 1 by norm_num, ↓reduceIte, Nat.cast_zero, neg_zero, zero_sub]
      exact (h0 y R hR).1 z
    · -- `k = 0`, `j ∈ {1, 2}`: the three-region bound
      set a := jb y ^ (-1 / p) with ha
      have ha0 : 0 < a := Real.rpow_pos_of_pos hY _
      have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (c09_aux_one_le_jb y)
        (by rw [neg_div]; exact neg_nonpos.mpr (by positivity))
      set g1 := (Ioc 0 a).indicator (fun x : ℝ => x ^ (p - 1)) with hg1
      set g2 := (Ioc a 1).indicator (fun x : ℝ => x ^ (-p - 1)) with hg2
      have ig1 : Integrable g1 := by
        rw [hg1, integrable_indicator_iff measurableSet_Ioc]
        exact (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a)
          (show -1 < p - 1 by linarith)).1
      have ig2 : Integrable g2 := by
        rw [hg2, integrable_indicator_iff measurableSet_Ioc]
        refine (ContinuousOn.intervalIntegrable (a := a) (b := 1) ?_).1
        refine ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl ?_
        rw [uIcc_of_le ha1] at hx; exact (lt_of_lt_of_le ha0 hx.1).ne'
      have Ig1 : ∫ x, g1 x = jb y ^ (-1 : ℝ) / p := by
        rw [hg1, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le ha0.le,
          integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith), sub_zero]
        rw [show p - 1 + 1 = p by ring, ha, ← Real.rpow_mul hY.le]
        congr 2; field_simp
      have Ig2 : ∫ x, g2 x ≤ jb y / p := by
        rw [hg2, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le ha1,
          integral_rpow (Or.inr ⟨by intro h; linarith, by
            rw [uIcc_of_le ha1]; intro h; linarith [h.1]⟩)]
        rw [show -p - 1 + 1 = -p by ring, Real.one_rpow, ha, ← Real.rpow_mul hY.le,
          show -1 / p * -p = (1 : ℝ) by field_simp, Real.rpow_one]
        rw [div_neg, ← neg_div, neg_sub]
        exact div_le_div_of_nonneg_right (by linarith) hp0.le
      set D : ℝ → ℝ := fun z => (2 * C0 * K) * (g1 z + g1 (-z) +
        jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)) + jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ)) with hD
      have I12 : Integrable (fun z => g1 z + g1 (-z)) := ig1.add ig1.comp_neg
      have I3 : Integrable (fun z => jb y ^ (-2 : ℝ) * (g2 z + g2 (-z))) :=
        (ig2.add ig2.comp_neg).const_mul _
      have I123 : Integrable (fun z => g1 z + g1 (-z) + jb y ^ (-2 : ℝ) * (g2 z + g2 (-z))) :=
        I12.add I3
      have I4 : Integrable (fun z => jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ)) := hI2i.const_mul _
      have iD : Integrable D := (I123.add I4).const_mul _
      have hbd : ∀ᵐ z, jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j 0 y z| ≤ D z := by
        have hne : ∀ᵐ z : ℝ, z ≠ 0 := by
          rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
        filter_upwards [hne] with z hz
        have hb3 := (h0 y R hR).2 z hz
        have hh : |c09_weighted_kernel_L1_h p R j 0 y z| ≤
            2 * C0 * c09_m20_kernel_bound p (γ + 3) y z := by
          unfold c09_weighted_kernel_L1_h
          have a1 := abs_nonneg
            ((deriv (invFourierT (linear_nonstationary_symbol_expansion_m p R 1 y 0)) z).re)
          have a2 := abs_nonneg
            ((invFourierT (linear_nonstationary_symbol_expansion_m p R 2 y 0) z).re)
          split_ifs with hj1
          · obtain rfl : j = 1 := by omega
            linarith
          · obtain rfl : j = 2 := by omega
            linarith
        have hdom := c09_aux_B3_dom p γ y z hp0 hγ0 hz
        have hw0 : 0 ≤ jb z ^ (γ + 1) := (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
        calc jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j 0 y z|
            ≤ jb z ^ (γ + 1) * (2 * C0 * c09_m20_kernel_bound p (γ + 3) y z) := by gcongr
          _ = 2 * C0 * (jb z ^ (γ + 1) * c09_m20_kernel_bound p (γ + 3) y z) := by ring
          _ ≤ 2 * C0 * (K * (g1 z + g1 (-z) + jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)) +
                jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ))) := by gcongr
          _ = D z := by rw [hD]; ring
      obtain ⟨hi, hint⟩ := c09_aux_dom hmeas hnn iD hbd
      refine ⟨hi, hint.trans ?_⟩
      have s1 : ∫ z, (g1 z + g1 (-z) + jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)) +
          jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ)) =
          (∫ z, (g1 z + g1 (-z) + jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)))) +
            ∫ z, jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ) := integral_add I123 I4
      have s2 : ∫ z, (g1 z + g1 (-z) + jb y ^ (-2 : ℝ) * (g2 z + g2 (-z))) =
          (∫ z, (g1 z + g1 (-z))) + ∫ z, jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)) := integral_add I12 I3
      have s3 : ∫ z, (g1 z + g1 (-z)) = (∫ z, g1 z) + ∫ z, g1 (-z) :=
        integral_add ig1 ig1.comp_neg
      have s4 : ∫ z, jb y ^ (-2 : ℝ) * (g2 z + g2 (-z)) =
          jb y ^ (-2 : ℝ) * ∫ z, (g2 z + g2 (-z)) := integral_const_mul _ _
      have s5 : ∫ z, (g2 z + g2 (-z)) = (∫ z, g2 z) + ∫ z, g2 (-z) :=
        integral_add ig2 ig2.comp_neg
      have s6 : ∫ z, jb y ^ (-1 : ℝ) * jb z ^ (-2 : ℝ) = jb y ^ (-1 : ℝ) * I2 :=
        integral_const_mul _ _
      have n1 : ∫ z, g1 (-z) = ∫ z, g1 z := integral_neg_eq_self g1 volume
      have n2 : ∫ z, g2 (-z) = ∫ z, g2 z := integral_neg_eq_self g2 volume
      have IDe : ∫ z, D z = (2 * C0 * K) * ((∫ x, g1 x) + (∫ x, g1 x) +
          jb y ^ (-2 : ℝ) * ((∫ x, g2 x) + (∫ x, g2 x)) + jb y ^ (-1 : ℝ) * I2) := by
        rw [hD, integral_const_mul, s1, s2, s3, s4, s5, s6, n1, n2]
      rw [IDe, Ig1]
      have hy2 : jb y ^ (-2 : ℝ) * jb y = jb y ^ (-1 : ℝ) := by
        rw [show (-1 : ℝ) = -2 + 1 by norm_num, Real.rpow_add hY, Real.rpow_one]
      have hyk : jb y ^ (-((0 : ℕ) : ℝ) - 1) = jb y ^ (-1 : ℝ) := by norm_num
      rw [hyk]
      have hy1 : 0 < jb y ^ (-1 : ℝ) := Real.rpow_pos_of_pos hY _
      have hy2' : 0 ≤ jb y ^ (-2 : ℝ) := (Real.rpow_pos_of_pos hY _).le
      have b2 : jb y ^ (-2 : ℝ) * ((∫ x, g2 x) + (∫ x, g2 x)) ≤ 2 * (jb y ^ (-1 : ℝ) / p) := by
        rw [← hy2]
        calc jb y ^ (-2 : ℝ) * ((∫ x, g2 x) + (∫ x, g2 x)) ≤
            jb y ^ (-2 : ℝ) * (jb y / p + jb y / p) := by gcongr
          _ = 2 * (jb y ^ (-2 : ℝ) * jb y / p) := by ring
      have htot : (jb y ^ (-1 : ℝ) / p + jb y ^ (-1 : ℝ) / p +
          jb y ^ (-2 : ℝ) * ((∫ x, g2 x) + (∫ x, g2 x)) + jb y ^ (-1 : ℝ) * I2) ≤
          (4 / p + I2) * jb y ^ (-1 : ℝ) := by
        have : jb y ^ (-1 : ℝ) / p + jb y ^ (-1 : ℝ) / p + 2 * (jb y ^ (-1 : ℝ) / p) +
            jb y ^ (-1 : ℝ) * I2 = (4 / p + I2) * jb y ^ (-1 : ℝ) := by ring
        linarith
      calc (2 * C0 * K) * (jb y ^ (-1 : ℝ) / p + jb y ^ (-1 : ℝ) / p +
            jb y ^ (-2 : ℝ) * ((∫ x, g2 x) + (∫ x, g2 x)) + jb y ^ (-1 : ℝ) * I2)
          ≤ (2 * C0 * K) * ((4 / p + I2) * jb y ^ (-1 : ℝ)) := by gcongr
        _ ≤ Cs * jb y ^ (-1 : ℝ) := by
          rw [← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ hy1.le
          rw [hCs]
          nlinarith [mul_nonneg hC0.le hI2, mul_nonneg hCsum hI2]
  · -- `k ≥ 1`
    have hle : ∀ c : ℝ, c ≤ C1 + C2 + C3 + C4 → c * I2 ≤ Cs := by
      intro c hc'
      rw [hCs]
      nlinarith [mul_le_mul_of_nonneg_right hc' hI2, mul_nonneg hC0.le hI2,
        mul_nonneg (mul_nonneg hC0.le hK0.le) (show 0 ≤ 4 / p + I2 by positivity)]
    interval_cases k
    · exact decay_case C1 hC1.le (hle _ (by linarith)) fun z =>
        (hsum 1 z).trans (h1 y R hR2 z)
    · exact decay_case C2 hC2.le (hle _ (by linarith)) fun z =>
        (hsum 2 z).trans (h2 y R hR2 z)
    · exact decay_case C3 hC3.le (hle _ (by linarith)) fun z =>
        (hsum 3 z).trans (h3 y R hR2 z)
    · exact decay_case C4 hC4.le (hle _ (by linarith)) fun z =>
        (hsum 4 z).trans (h4 y R hR2 z)

/-! ### Nonstationary part: remainder -/

/-- Blueprint: lem:linear_nonstationary_remainder.  `|K_{ℛ_{j,M}}^R(y,z)| ≤ C_M ⟨y⟩^{-M} w_E(z)`
for `M ≥ 2`. -/
theorem linear_nonstationary_remainder (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (M : ℕ)
    (hM : 2 ≤ M) :
    ∃ C, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y z : ℝ,
      ‖linear_nonstationary_symbol_expansion_remKernel p R j M y z‖ ≤
        C * jb y ^ (-(M : ℝ)) * c09_weights_E p z := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hmjk, -⟩ := c09_mjk_bounds p hp hp1
  obtain ⟨C0, hC0, h0⟩ := hmjk 0 (by norm_num) (M - 1) 1
  obtain ⟨C1, hC1, h1⟩ := hmjk 1 (by norm_num) (M - 1) 1
  obtain ⟨C2, hC2, h2⟩ := hmjk 2 le_rfl (M - 1) 1
  obtain ⟨-, -, -, -, ⟨CE, hCE, hE⟩, -⟩ := c09_tail_basic p hp hp1
  obtain ⟨cstar, -, -, Cc, -, -, -, -, -, -, -, -, -, h4b, -⟩ := c09_cutoff_bounds p hp hp1
  set Cm := max C0 (max C1 C2) with hCm
  have hCm0 : 0 < Cm := lt_of_lt_of_le hC0 (le_max_left _ _)
  have hmb : ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y ξ : ℝ, 0 < ξ →
      ‖deriv (linear_nonstationary_symbol_expansion_m p R j y (M - 1)) ξ‖ ≤
        Cm * ξ ^ ((j : ℝ) - 2 - ((M - 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) *
          (|y| + ξ ^ p) ^ (-((M - 1 : ℕ) : ℝ) - 1) := by
    intro R hR j hj y ξ hξ
    have hpos : 0 ≤ ξ ^ ((j : ℝ) - 2 - ((M - 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) *
        (|y| + ξ ^ p) ^ (-((M - 1 : ℕ) : ℝ) - 1) := by
      have : 0 < |y| + ξ ^ p := by positivity
      positivity
    rw [← iteratedDeriv_one]
    interval_cases j
    · exact (h0 R hR y ξ hξ).trans (by rw [mul_assoc, mul_assoc]; gcongr; exact le_max_left _ _)
    · exact (h1 R hR y ξ hξ).trans (by
        rw [mul_assoc, mul_assoc]; gcongr; exact (le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 R hR y ξ hξ).trans (by
        rw [mul_assoc, mul_assoc]; gcongr; exact (le_max_right _ _).trans (le_max_right _ _))
  have hMc : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  refine ⟨Cm * 2 ^ ((M : ℝ) / 2) * CE, by positivity, fun R hR j hj y z => ?_⟩
  have hwE : 0 ≤ c09_weights_E p z := by
    unfold c09_weights_E; split_ifs <;> exact (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
  have hY := c09_aux_jb_pos y
  set K : ℝ := Cm * 2 ^ ((M : ℝ) / 2) * CE * jb y ^ (-(M : ℝ)) * c09_weights_E p z with hK
  have hK0 : 0 ≤ K := by positivity
  have hbd : ∀ ξ ∈ Ioc (1 : ℝ) (2 * R),
      ‖deriv (linear_nonstationary_symbol_expansion_m p R j y (M - 1)) ξ *
        Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ‖ ≤
        K * ξ ^ (-2 : ℝ) := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_trans one_pos hξ.1
    have hξ1 : 1 ≤ ξ := hξ.1.le
    rw [norm_mul, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hm := hmb R hR j hj y ξ hξ0
    have hE' := hE z ξ hξ0.le
    have hyξ : 0 < |y| + ξ ^ p := by positivity
    have e1 : ξ ^ ((j : ℝ) - 2 - ((M - 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) ≤ ξ ^ (-2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hξ1
      rw [hMc]
      have : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      push_cast; linarith
    have e2 : (|y| + ξ ^ p) ^ (-((M - 1 : ℕ) : ℝ) - 1) ≤ 2 ^ ((M : ℝ) / 2) * jb y ^ (-(M : ℝ)) := by
      rw [hMc, show -((M : ℝ) - 1) - 1 = -(M : ℝ) by ring]
      have hlow := h4b y ξ hξ1
      calc (|y| + ξ ^ p) ^ (-(M : ℝ)) ≤ (2 ^ (-(1 / 2 : ℝ)) * jb y) ^ (-(M : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by simp)
        _ = 2 ^ ((M : ℝ) / 2) * jb y ^ (-(M : ℝ)) := by
            rw [Real.mul_rpow (by positivity) hY.le, ← Real.rpow_mul (by norm_num)]
            congr 2; ring
    have hp1' : 0 ≤ ξ ^ (-2 : ℝ) := (Real.rpow_pos_of_pos hξ0 _).le
    calc ‖deriv (linear_nonstationary_symbol_expansion_m p R j y (M - 1)) ξ‖ *
          ‖c09_tail_integral p z ξ‖
        ≤ (Cm * ξ ^ ((j : ℝ) - 2 - ((M - 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ)) *
            (|y| + ξ ^ p) ^ (-((M - 1 : ℕ) : ℝ) - 1)) * (CE * c09_weights_E p z) :=
          mul_le_mul hm hE' (norm_nonneg _) (by positivity)
      _ ≤ (Cm * ξ ^ (-2 : ℝ) * (2 ^ ((M : ℝ) / 2) * jb y ^ (-(M : ℝ)))) *
            (CE * c09_weights_E p z) := by gcongr
      _ = K * ξ ^ (-2 : ℝ) := by rw [hK]; ring
  have hR1 : (1 : ℝ) ≤ 2 * R := by linarith
  have hgi : IntervalIntegrable (fun ξ : ℝ => K * ξ ^ (-2 : ℝ)) volume 1 (2 * R) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun x hx => ?_)
    rw [uIcc_of_le hR1] at hx; exact Or.inl (by simp; linarith [hx.1])
  have hint := intervalIntegral.norm_integral_le_of_norm_le hR1
    (Eventually.of_forall fun ξ hξ => hbd ξ hξ) hgi
  have hcomp : ∫ ξ in (1 : ℝ)..(2 * R), K * ξ ^ (-2 : ℝ) ≤ K := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, by
      rw [uIcc_of_le hR1]; intro h; linarith [h.1]⟩)]
    have : 0 < (2 * R) ^ ((-2 : ℝ) + 1) := Real.rpow_pos_of_pos (by linarith) _
    have e : ((2 * R) ^ ((-2 : ℝ) + 1) - (1 : ℝ) ^ ((-2 : ℝ) + 1)) / ((-2 : ℝ) + 1) =
        1 - (2 * R) ^ ((-2 : ℝ) + 1) := by
      rw [Real.one_rpow]; norm_num; ring
    rw [e]; nlinarith
  unfold linear_nonstationary_symbol_expansion_remKernel
  rw [norm_neg]
  exact hint.trans hcomp

/-! ### The high-frequency estimate -/

/-- `|z| ≤ ⟨z⟩`. -/
theorem c09_aux_abs_le_jb (z : ℝ) : |z| ≤ jb z := by
  unfold jb; exact Real.abs_le_sqrt (by nlinarith)

/-- `∫_{z ≥ c} ⟨z⟩^{-σ} dz ≤ c^{1-σ}/(σ-1)` for `σ > 1`, `c > 0`. -/
private theorem c09_aux_tail_int {σ c : ℝ} (hσ : 1 < σ) (hc : 0 < c) :
    ∫ z, (Ici c).indicator (fun z => jb z ^ (-σ)) z ≤ c ^ (1 - σ) / (σ - 1) := by
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hi : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  calc ∫ z in Ioi c, jb z ^ (-σ) ≤ ∫ z in Ioi c, z ^ (-σ) := by
        refine setIntegral_mono_on ?_ hi measurableSet_Ioi fun z hz => ?_
        · refine hi.mono' ?_ ?_
          · exact (c09_aux_jb_continuous.rpow_const
              (fun y => Or.inl (c09_aux_jb_pos y).ne')).aestronglyMeasurable
          · rw [ae_restrict_iff' measurableSet_Ioi]
            refine Eventually.of_forall fun z (hz : c < z) => ?_
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le]
            refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by linarith)
            exact c09_aux_abs_le_jb z |>.trans' (le_abs_self z)
        · have hz' : 0 < z := lt_trans hc hz
          refine Real.rpow_le_rpow_of_nonpos hz' ?_ (by linarith)
          exact c09_aux_abs_le_jb z |>.trans' (le_abs_self z)
    _ = c ^ (1 - σ) / (σ - 1) := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hc]
        rw [show -σ + 1 = 1 - σ by ring, neg_div, ← div_neg]; congr 1; ring

/-- Blueprint: lem:c09_stationary_contribution.
`|𝒯_{+,j}^{s,R} G(y)| ≤ C ‖G‖_{Y_γ} w_{γ,j}(y)`. -/
theorem c09_stationary_contribution (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma_tilde p γ, ∀ R : ℝ, 2 ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
      ‖c09_stationary_split_op_s p R j G y‖ ≤ C * yNorm p γ G * c09_weights p γ j y := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hvan, ⟨C1, hC1, hnear⟩, hfar⟩ := linear_stationary p hp hp1
  obtain ⟨C3, hC3, hfar3⟩ := hfar 3 (by norm_num)
  obtain ⟨-, -, hpart2, ⟨CL, hCL, hL1⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
  set σ : ℝ := γ - 1 / p - (1 - p) / (2 * p) with hσ
  have hσ1 : 1 < σ := by
    have := hγ.1; unfold beta at this
    have e : (p + 1) / (2 * p) + 1 / p = 1 + 1 / p + (1 - p) / (2 * p) := by
      field_simp; ring
    linarith
  set K1 : ℝ := C1 * (12 : ℝ) ^ (σ - 1) / (σ - 1) with hK1
  have hK1p : 0 < K1 := by
    have : 0 < σ - 1 := by linarith
    positivity
  refine ⟨K1 + C3 * CL, by positivity, fun G hG R hR j hj y => ?_⟩
  have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
  have hw := c09_aux_weights_pos p γ j y
  set ys : ℝ := (50 / 51 : ℝ) ^ p with hys
  have hys1 : (50 / 51 : ℝ) ≤ ys := by
    have := Real.rpow_le_rpow_of_exponent_ge (x := (50 / 51 : ℝ)) (by norm_num) (by norm_num)
      hp1.le
    simpa using this
  by_cases hy : y < ys
  · have : c09_stationary_split_op_s p R j G y = 0 := by
      unfold c09_stationary_split_op_s
      rw [show (fun z => c09_stationary_split_kernel_s p R j y z * ((deriv G z : ℝ) : ℂ)) =
          fun _ => (0 : ℂ) by
        ext z
        have : c09_stationary_split_kernel_s p R j y z = 0 := by
          by_contra hne; exact absurd (hvan R hR j hj y z hne) (not_le.mpr hy)
        rw [this, zero_mul]]
      simp
    rw [this, norm_zero]; positivity
  push Not at hy
  have hy0 : 0 < y := by linarith
  have hjy : jb y ≤ 3 * y := by
    have h1 : jb y ≤ 1 + y := by
      unfold jb
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  have hY := c09_aux_jb_pos y
  set a : ℝ := (j : ℝ) / p - (p + 3) / (2 * p) with ha
  have hG2 := (hpart2 G hG.1).2
  obtain ⟨-, iD, -, hLb⟩ := hL1 G hG.1
  set B : ℝ → ℝ := fun z => (C1 * yNorm p γ G * jb y ^ a) *
      (Ici (y / 4)).indicator (fun z => jb z ^ (-σ)) z +
    (C3 * jb y ^ (-3 : ℝ)) * |deriv G z| with hB
  have iInd : Integrable ((Ici (y / 4)).indicator (fun z => jb z ^ (-σ))) :=
    (c09_aux_jb_integrable hσ1).indicator measurableSet_Ici
  have iB : Integrable B := (iInd.const_mul _).add (iD.abs.const_mul _)
  have hbound : ∀ᵐ z, ‖c09_stationary_split_kernel_s p R j y z * ((deriv G z : ℝ) : ℂ)‖ ≤ B z := by
    filter_upwards [hG2] with z hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hZ := c09_aux_jb_pos z
    have t1 : 0 ≤ (C1 * yNorm p γ G * jb y ^ a) *
        (Ici (y / 4)).indicator (fun z => jb z ^ (-σ)) z := by
      apply mul_nonneg (by positivity)
      exact Set.indicator_nonneg (fun z _ => (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le) z
    have t2 : 0 ≤ (C3 * jb y ^ (-3 : ℝ)) * |deriv G z| := by positivity
    by_cases hz4 : y / 4 ≤ z
    · have hk := hnear R hR j hj y z (by linarith)
      rw [hB]; dsimp only
      rw [Set.indicator_of_mem (show z ∈ Ici (y / 4) from hz4)]
      have e : jb z ^ ((1 - p) / (2 * p)) * jb z ^ (-γ + 1 / p) = jb z ^ (-σ) := by
        rw [← Real.rpow_add hZ]; congr 1; rw [hσ]; ring
      calc ‖c09_stationary_split_kernel_s p R j y z‖ * |deriv G z|
          ≤ (C1 * jb y ^ ((j : ℝ) / p - (p + 3) / (2 * p)) * jb z ^ ((1 - p) / (2 * p))) *
              (yNorm p γ G * jb z ^ (-γ + 1 / p)) :=
            mul_le_mul hk hz.2.1 (abs_nonneg _) (by positivity)
        _ = C1 * yNorm p γ G * jb y ^ a * jb z ^ (-σ) := by rw [← e, ha]; ring
        _ ≤ _ := by linarith
    · push Not at hz4
      have hk := hfar3 R hR j hj y z (by linarith)
      have hle1 : (jb y + |z|) ^ (-3 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [c09_aux_one_le_jb y, abs_nonneg z])
          (by norm_num)
      have hk' : ‖c09_stationary_split_kernel_s p R j y z‖ ≤ C3 * jb y ^ (-3 : ℝ) := by
        calc _ ≤ C3 * jb y ^ (-3 : ℝ) * (jb y + |z|) ^ (-3 : ℝ) := hk
          _ ≤ C3 * jb y ^ (-3 : ℝ) * 1 := by gcongr
          _ = _ := by ring
      calc ‖c09_stationary_split_kernel_s p R j y z‖ * |deriv G z|
          ≤ (C3 * jb y ^ (-3 : ℝ)) * |deriv G z| := by gcongr
        _ ≤ B z := by rw [hB]; dsimp only; linarith
  have hint : ∫ z, B z = (C1 * yNorm p γ G * jb y ^ a) *
      (∫ z, (Ici (y / 4)).indicator (fun z => jb z ^ (-σ)) z) +
      (C3 * jb y ^ (-3 : ℝ)) * ∫ z, |deriv G z| := by
    rw [hB, integral_add (iInd.const_mul _) (iD.abs.const_mul _), integral_const_mul,
      integral_const_mul]
  have htail := c09_aux_tail_int hσ1 (show 0 < y / 4 by linarith)
  have hpow : (y / 4) ^ (1 - σ) ≤ (12 : ℝ) ^ (σ - 1) * jb y ^ (1 - σ) := by
    calc (y / 4) ^ (1 - σ) ≤ (jb y / 12) ^ (1 - σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ = (12 : ℝ) ^ (σ - 1) * jb y ^ (1 - σ) := by
          rw [Real.div_rpow hY.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
          ring_nf
  have hw' : c09_weights p γ j y = jb y ^ (-γ + (j : ℝ) / p) := c09_aux_w_pos_branch p γ j hy0.le
  have e1 : jb y ^ a * jb y ^ (1 - σ) = c09_weights p γ j y := by
    rw [hw', ← Real.rpow_add hY]; congr 1; rw [ha, hσ]; field_simp; ring
  have e3 : jb y ^ (-3 : ℝ) ≤ c09_weights p γ j y := by
    rw [hw']
    apply Real.rpow_le_rpow_of_exponent_le (c09_aux_one_le_jb y)
    have : (0 : ℝ) ≤ (j : ℝ) / p := by positivity
    linarith [hγ.2]
  have hDN : ∫ z, |deriv G z| ≤ CL * yNorm p γ G := by
    have h0 : 0 ≤ ∫ z, |G z| := integral_nonneg fun z => abs_nonneg _
    have h3 : 0 ≤ ∫ z, |deriv G z| * c09_weights_E p z := by
      refine integral_nonneg fun z => mul_nonneg (abs_nonneg _) ?_
      unfold c09_weights_E; split_ifs <;> exact (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le
    linarith
  have hI0 : 0 ≤ ∫ z, (Ici (y / 4)).indicator (fun z => jb z ^ (-σ)) z :=
    integral_nonneg fun z =>
      Set.indicator_nonneg (fun z _ => (Real.rpow_pos_of_pos (c09_aux_jb_pos z) _).le) z
  have hσ' : 0 < σ - 1 := by linarith
  calc ‖c09_stationary_split_op_s p R j G y‖
      ≤ ∫ z, ‖c09_stationary_split_kernel_s p R j y z * ((deriv G z : ℝ) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, B z := integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) iB hbound
    _ = _ := hint
    _ ≤ (C1 * yNorm p γ G * jb y ^ a) * ((12 : ℝ) ^ (σ - 1) * jb y ^ (1 - σ) / (σ - 1)) +
        (C3 * jb y ^ (-3 : ℝ)) * (CL * yNorm p γ G) := by
        gcongr
        · exact htail.trans (div_le_div_of_nonneg_right hpow hσ'.le)
    _ ≤ (C1 * yNorm p γ G * jb y ^ a) * ((12 : ℝ) ^ (σ - 1) * jb y ^ (1 - σ) / (σ - 1)) +
        (C3 * c09_weights p γ j y) * (CL * yNorm p γ G) := by gcongr
    _ = (K1 + C3 * CL) * yNorm p γ G * c09_weights p γ j y := by
        rw [← e1, hK1]; field_simp

/-! #### Helpers for the nonstationary contribution -/

/-- Integration by parts on `ℝ` against `G ∈ Y_γ`:
`∫ f(w) G'(y-w) dw = ∫ f'(w) G(y-w) dw` for `f ∈ C¹` bounded. -/
theorem c09_aux_ibp_conv (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ) (hγ : admissibleGamma p γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (B : ℝ)
    (hfB : ∀ w, |f w| ≤ B) (y : ℝ) (h1 : Integrable (fun w => f w * deriv G (y - w)))
    (h2 : Integrable (fun w => deriv f w * G (y - w))) :
    ∫ w, f w * deriv G (y - w) = ∫ w, deriv f w * G (y - w) := by
  have hGl : LocallyLipschitz G := hG.1
  have hGt := c09_aux_Y_tendsto p hp hp1 γ hγ G hG
  have hdF : ∀ u, HasDerivAt (fun u => f (y - u)) (deriv f (y - u) * -1) u := fun u =>
    ((hf.differentiable (by norm_num) (y - u)).hasDerivAt).comp u ((hasDerivAt_id u).const_sub y)
  have hFc : ContDiff ℝ 1 (fun u => f (y - u)) := hf.comp (contDiff_const.sub contDiff_id)
  have hFac : ∀ a b, AbsolutelyContinuousOnInterval (fun u => f (y - u)) a b := fun a b => by
    obtain ⟨K, hK⟩ := hFc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_uIcc a b)
      isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval
  have key : ∀ a b, ∫ u in a..b, deriv G u * f (y - u) =
      G b * f (y - b) - G a * f (y - a) + ∫ u in a..b, G u * deriv f (y - u) := by
    intro a b
    have h := (c09_aux_ac_of_locLip G hGl a b).integral_mul_deriv_eq_deriv_mul (hFac a b)
    simp only [fun u => (hdF u).deriv] at h
    have e : ∫ u in a..b, G u * (deriv f (y - u) * -1) = -∫ u in a..b, G u * deriv f (y - u) := by
      rw [← intervalIntegral.integral_neg]; congr 1; funext u; ring
    rw [e] at h; linarith
  have i1 : Integrable (fun u => deriv G u * f (y - u)) :=
    (h1.comp_sub_left y).congr (Eventually.of_forall fun u => by simp only [sub_sub_cancel, mul_comm])
  have i2 : Integrable (fun u => G u * deriv f (y - u)) :=
    (h2.comp_sub_left y).congr (Eventually.of_forall fun u => by simp only [sub_sub_cancel, mul_comm])
  have t1 := intervalIntegral_tendsto_integral i1 tendsto_neg_atTop_atBot tendsto_id
  have t2 := intervalIntegral_tendsto_integral i2 tendsto_neg_atTop_atBot tendsto_id
  have tb : Tendsto (fun i : ℝ => G (id i) * f (y - id i) - G (-i) * f (y - -i)) atTop (𝓝 0) := by
    have g1 : Tendsto (fun i : ℝ => |G i| * B + |G (-i)| * B) atTop (𝓝 0) := by
      have a1 : Tendsto (fun i : ℝ => |G i|) atTop (𝓝 0) := by
        simpa using hGt.1.abs
      have a2 : Tendsto (fun i : ℝ => |G (-i)|) atTop (𝓝 0) := by
        simpa using (hGt.2.comp tendsto_neg_atTop_atBot).abs
      simpa using (a1.mul_const B).add (a2.mul_const B)
    refine squeeze_zero_norm (fun i => ?_) g1
    rw [Real.norm_eq_abs]
    calc |G (id i) * f (y - id i) - G (-i) * f (y - -i)|
        ≤ |G i| * |f (y - i)| + |G (-i)| * |f (y + i)| := by
          simp only [id, sub_neg_eq_add]
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ |G i| * B + |G (-i)| * B := by
          gcongr
          · exact hfB _
          · exact hfB _
  have t3 : Tendsto (fun i : ℝ => ∫ u in (-i)..(id i), deriv G u * f (y - u)) atTop
      (𝓝 (0 + ∫ u, G u * deriv f (y - u))) := by
    refine (tb.add t2).congr fun i => ?_
    rw [key]
  have heq : ∫ u, deriv G u * f (y - u) = ∫ u, G u * deriv f (y - u) := by
    rw [tendsto_nhds_unique t1 t3, zero_add]
  have c1 := integral_sub_left_eq_self (μ := volume) (fun w => f w * deriv G (y - w)) y
  have c2 := integral_sub_left_eq_self (μ := volume) (fun w => deriv f w * G (y - w)) y
  simp only [sub_sub_cancel] at c1 c2
  rw [← c1, ← c2]
  calc ∫ x, f (y - x) * deriv G x = ∫ u, deriv G u * f (y - u) := by
        congr 1; funext u; ring
    _ = ∫ u, G u * deriv f (y - u) := heq
    _ = ∫ x, deriv f (y - x) * G x := by congr 1; funext u; ring

/-- Weight comparisons used in the nonstationary contribution. -/
theorem c09_aux_w_compare (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) (y : ℝ) :
    (∀ j : ℕ, j ≤ 2 → jb y ^ (-(5 : ℝ)) ≤ c09_weights p γ j y) ∧
    (∀ j : ℕ, j ≤ 1 → ∀ k : ℕ, jb y ^ (-γ) * jb y ^ (-(k : ℝ) - 1) ≤ c09_weights p γ j y) ∧
    (∀ k : ℕ, c09_weights p γ 1 y * jb y ^ (-(k : ℝ) - 1) ≤ c09_weights p γ 2 y) := by
  have hp0 : 0 < p := by linarith
  have h1 := c09_aux_one_le_jb y
  have h0 := c09_aux_jb_pos y
  have hγ3 : γ < 3 := by linarith [hγ.2]
  have hγ0 : 0 < γ := by
    have := hγ.1; unfold beta at this
    have : 0 < (p + 1) / (2 * p) := by positivity
    have : 0 < 1 / p := by positivity
    linarith
  have hip : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
  have mono : ∀ a b : ℝ, a ≤ b → jb y ^ a ≤ jb y ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le h1 h
  have hjp : ∀ j : ℕ, 0 ≤ (j : ℝ) / p := fun j => by positivity
  refine ⟨fun j hj => ?_, fun j hj k => ?_, fun k => ?_⟩
  · have hj' : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have := hjp j
    unfold c09_weights
    split_ifs
    · exact mono _ _ (by linarith)
    · exact mono _ _ (by linarith)
  · have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have := hjp j
    rw [← Real.rpow_add h0]
    unfold c09_weights
    split_ifs
    · exact mono _ _ (by linarith)
    · exact mono _ _ (by linarith)
  · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e2 : (2 : ℝ) / p = 1 / p + 1 / p := by ring
    unfold c09_weights
    split_ifs
    · rw [← Real.rpow_add h0]
      exact mono _ _ (by push_cast; linarith)
    · rw [← Real.rpow_add h0]
      exact mono _ _ (by push_cast; linarith)

/-- Blueprint: lem:c09_nonstationary_contribution.
`|Re 𝒯_{+,j}^{ns,R} G(y)| ≤ C ‖G‖_{Y_γ} w_{γ,j}(y)` for `R ≥ R₀(y)`. -/
theorem c09_nonstationary_contribution (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma_tilde p γ, ∀ j : ℕ, j ≤ 2 → ∀ y R : ℝ,
      c09_truncation_R0 p y ≤ R →
      |(c09_stationary_split_op_ns p R j G y).re| ≤ C * yNorm p γ G * c09_weights p γ j y := by
  have hp0 : 0 < p := by linarith
  obtain ⟨CW, hCW, hWK⟩ := c09_weighted_kernel_L1 p hp hp1 γ hγ
  obtain ⟨Crem, hCrem, hRem⟩ := linear_nonstationary_remainder p hp hp1 5 (by norm_num)
  obtain ⟨-, -, -, ⟨CL, hCL, hL1⟩, -, -, ⟨C5, hC5, hW5⟩, hW6⟩ := c09_weight_facts p hp hp1 γ hγ
  set K : ℝ := C5 * CW + 2 ^ (γ / 2) * CW with hK
  have hK0 : 0 < K := by positivity
  refine ⟨2 * π * 5 * K + Crem * CL + 1, by positivity, fun G hG j hj y R hR => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
  have hw := c09_aux_weights_pos p γ j y
  have hjy := c09_aux_jb_pos y
  obtain ⟨hw5, hwj, hw12⟩ := c09_aux_w_compare p hp hp1 γ hγ y
  obtain ⟨-, -, hexp⟩ := linear_nonstationary_symbol_expansion p hp hp1 R hR2 y j hj 5 (by norm_num)
  obtain ⟨-, hremi, hconvi, hid⟩ := hexp γ hγ G hG
  obtain ⟨hGi, hG'i, hGw, hsum⟩ := hL1 G hG.1
  have hint : ∫ z, |deriv G z| * c09_weights_E p z ≤ CL * yNorm p γ G := by
    have a1 : 0 ≤ ∫ z, |G z| := integral_nonneg fun _ => abs_nonneg _
    have a2 : 0 ≤ ∫ z, |deriv G z| := integral_nonneg fun _ => abs_nonneg _
    linarith
  -- remainder
  have hremb : ‖linear_nonstationary_symbol_expansion_remOp p R j 5 G y‖ ≤
      Crem * CL * yNorm p γ G * c09_weights p γ j y := by
    unfold linear_nonstationary_symbol_expansion_remOp
    calc _ ≤ ∫ z, Crem * jb y ^ (-(5 : ℝ)) * (|deriv G z| * c09_weights_E p z) := by
          refine norm_integral_le_of_norm_le (hGw.const_mul _) (Eventually.of_forall fun z => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have := hRem R hR2 j hj y z
          push_cast at this
          calc _ ≤ (Crem * jb y ^ (-(5 : ℝ)) * c09_weights_E p z) * |deriv G z| := by
                gcongr
            _ = _ := by ring
      _ = Crem * jb y ^ (-(5 : ℝ)) * ∫ z, |deriv G z| * c09_weights_E p z := integral_const_mul _ _
      _ ≤ Crem * c09_weights p γ j y * (CL * yNorm p γ G) := by
          have hI0 : 0 ≤ ∫ z, |deriv G z| * c09_weights_E p z :=
            integral_nonneg fun z => mul_nonneg (abs_nonneg _) (c09_aux_weightsE_pos p z).le
          have h5 := hw5 j hj
          calc Crem * jb y ^ (-(5 : ℝ)) * ∫ z, |deriv G z| * c09_weights_E p z
              ≤ Crem * c09_weights p γ j y * ∫ z, |deriv G z| * c09_weights_E p z := by gcongr
            _ ≤ _ := by gcongr
      _ = _ := by ring
  -- convolution terms
  have hterm : ∀ k < 5, |(∫ w, invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w *
      ((deriv G (y - w) : ℝ) : ℂ)).re| ≤ K * yNorm p γ G * c09_weights p γ j y := by
    intro k hk5
    have hk4 : k ≤ 4 := by omega
    set mk := linear_nonstationary_symbol_expansion_m p R j y k with hmk
    have hmc : Continuous mk := (c09_aux_nse_m_contDiff p hp0 R hR2 j y k).continuous
    have hms : HasCompactSupport mk := by
      refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2 * R)) fun x hx => ?_
      simp only [mem_Icc, not_and_or, not_le] at hx
      exact c09_aux_nse_m_zero p hp0 R hR2 j y k x (hx.imp le_of_lt le_of_lt)
    have hmi : Integrable mk := hmc.integrable_of_hasCompactSupport hms
    have hic : Continuous (invFourierT mk) := c09_aux_invFourierT_continuous _ hmi
    set Bk : ℝ := (2 * π)⁻¹ * ∫ ξ, ‖mk ξ‖ with hBk
    have hib : ∀ w, ‖invFourierT mk w‖ ≤ Bk := fun w => c09_aux_invFourierT_norm_le _ _
    have hre : (∫ w, invFourierT mk w * ((deriv G (y - w) : ℝ) : ℂ)).re =
        ∫ w, (invFourierT mk w).re * deriv G (y - w) := by
      have := Complex.reCLM.integral_comp_comm (hconvi k hk5)
      simp only [Complex.reCLM_apply] at this
      rw [← this]
      congr 1; funext w
      simp [Complex.mul_re, hmk]
    rw [hre]
    have hG'y : Integrable (fun w => deriv G (y - w)) := hG'i.comp_sub_left y
    obtain ⟨hWi, hWb⟩ := hWK k hk4 j hj y R hR
    have hWb' : ∫ z, jb z ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y z| ≤
        CW * jb y ^ (-(k : ℝ) - 1) := hWb
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · -- `j ≤ 1`: integrate by parts
      have hj1' : j ≤ 1 := by omega
      have hd := c09_aux_invF_hasDerivAt mk hmc hms
      have hderiv : deriv (invFourierT mk) = invFourierT (fun ξ => Complex.I * (ξ : ℂ) * mk ξ) :=
        funext fun w => (hd w).deriv
      have hm1i : Integrable (fun ξ : ℝ => Complex.I * (ξ : ℂ) * mk ξ) :=
        (by fun_prop : Continuous fun ξ : ℝ => Complex.I * (ξ : ℂ) * mk ξ).integrable_of_hasCompactSupport
          (hms.mul_left (f := fun ξ : ℝ => Complex.I * (ξ : ℂ)))
      have hdc : Continuous (deriv (invFourierT mk)) := by
        rw [hderiv]; exact c09_aux_invFourierT_continuous _ hm1i
      have hcd : ContDiff ℝ 1 (invFourierT mk) :=
        contDiff_one_iff_deriv.2 ⟨fun w => (hd w).differentiableAt, hdc⟩
      set f : ℝ → ℝ := fun w => (invFourierT mk w).re with hf
      have hfc : ContDiff ℝ 1 f := Complex.reCLM.contDiff.comp hcd
      have hdf : ∀ w, deriv f w = c09_weighted_kernel_L1_h p R j k y w := by
        intro w
        unfold c09_weighted_kernel_L1_h
        rw [if_pos hj1']
        have := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt w
          ((hcd.differentiable (by norm_num) w).hasDerivAt))
        exact this.deriv
      have hG6 : ∀ w, |G (y - w)| ≤ 2 ^ (γ / 2) * yNorm p γ G * jb y ^ (-γ) * jb w ^ (γ + 1) := by
        intro w
        refine (hW6 G hG.1 y w).trans ?_
        have := c09_aux_jb_pos w
        have : jb w ^ γ ≤ jb w ^ (γ + 1) :=
          Real.rpow_le_rpow_of_exponent_le (c09_aux_one_le_jb w) (by linarith)
        gcongr
      have hGc : Continuous G := hG.1.1.continuous
      have h1 : Integrable (fun w => f w * deriv G (y - w)) :=
        hG'y.bdd_mul (c := Bk) (Complex.continuous_re.comp hic).aestronglyMeasurable
          (Eventually.of_forall fun w => by
            rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hib w))
      have hdom : Integrable (fun w => (2 ^ (γ / 2) * yNorm p γ G * jb y ^ (-γ)) *
          (jb w ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y w|)) := hWi.const_mul _
      have hbound : ∀ w, ‖deriv f w * G (y - w)‖ ≤ (2 ^ (γ / 2) * yNorm p γ G * jb y ^ (-γ)) *
          (jb w ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y w|) := by
        intro w
        rw [Real.norm_eq_abs, abs_mul, hdf w]
        calc |c09_weighted_kernel_L1_h p R j k y w| * |G (y - w)|
            ≤ |c09_weighted_kernel_L1_h p R j k y w| *
              (2 ^ (γ / 2) * yNorm p γ G * jb y ^ (-γ) * jb w ^ (γ + 1)) := by
              gcongr; exact hG6 w
          _ = _ := by ring
      have h2 : Integrable (fun w => deriv f w * G (y - w)) :=
        hdom.mono' ((hfc.continuous_deriv le_rfl).mul (hGc.comp (continuous_const.sub
          continuous_id))).aestronglyMeasurable (Eventually.of_forall hbound)
      rw [c09_aux_ibp_conv p hp hp1 γ hγ G hG.1 f hfc Bk (fun w => (Complex.abs_re_le_norm _).trans
        (hib w)) y h1 h2]
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall hbound)).trans ?_
      rw [integral_const_mul]
      calc 2 ^ (γ / 2) * yNorm p γ G * jb y ^ (-γ) *
            ∫ w, jb w ^ (γ + 1) * |c09_weighted_kernel_L1_h p R j k y w|
          ≤ 2 ^ (γ / 2) * yNorm p γ G * jb y ^ (-γ) * (CW * jb y ^ (-(k : ℝ) - 1)) := by
            gcongr
        _ = 2 ^ (γ / 2) * CW * yNorm p γ G * (jb y ^ (-γ) * jb y ^ (-(k : ℝ) - 1)) := by ring
        _ ≤ 2 ^ (γ / 2) * CW * yNorm p γ G * c09_weights p γ j y := by
            gcongr; exact hwj j hj1' k
        _ ≤ K * yNorm p γ G * c09_weights p γ j y := by
            gcongr; rw [hK]; nlinarith [mul_pos hC5 hCW]
    · -- `j = 2`
      obtain rfl : j = 2 := by omega
      have hh : ∀ w, (invFourierT mk w).re = c09_weighted_kernel_L1_h p R 2 k y w := by
        intro w; unfold c09_weighted_kernel_L1_h; rw [if_neg (by norm_num)]
      have hW5' := hW5 G hG.1 y
      have hdom : Integrable (fun w => (C5 * yNorm p γ G * c09_weights p γ 1 y) *
          (jb w ^ (γ + 1) * |c09_weighted_kernel_L1_h p R 2 k y w|)) := hWi.const_mul _
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hdom (hW5'.mono fun w hwb => ?_)).trans ?_
      · rw [Real.norm_eq_abs, abs_mul, hh w]
        calc |c09_weighted_kernel_L1_h p R 2 k y w| * |deriv G (y - w)|
            ≤ |c09_weighted_kernel_L1_h p R 2 k y w| *
              (C5 * yNorm p γ G * jb w ^ (γ + 1) * c09_weights p γ 1 y) := by gcongr
          _ = _ := by ring
      · rw [integral_const_mul]
        have hw1 := c09_aux_weights_pos p γ 1 y
        calc C5 * yNorm p γ G * c09_weights p γ 1 y *
              ∫ w, jb w ^ (γ + 1) * |c09_weighted_kernel_L1_h p R 2 k y w|
            ≤ C5 * yNorm p γ G * c09_weights p γ 1 y * (CW * jb y ^ (-(k : ℝ) - 1)) := by
              gcongr
          _ = C5 * CW * yNorm p γ G * (c09_weights p γ 1 y * jb y ^ (-(k : ℝ) - 1)) := by ring
          _ ≤ C5 * CW * yNorm p γ G * c09_weights p γ 2 y := by
              gcongr; exact hw12 k
          _ ≤ K * yNorm p γ G * c09_weights p γ 2 y := by
              gcongr; rw [hK]; have : 0 < 2 ^ (γ / 2) * CW := by positivity
              linarith
  -- assemble
  rw [hid, Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum]
  have hs : |∑ k ∈ Finset.range 5, (∫ w, invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w *
      ((deriv G (y - w) : ℝ) : ℂ)).re| ≤ 5 * (K * yNorm p γ G * c09_weights p γ j y) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ k ∈ Finset.range 5, K * yNorm p γ G * c09_weights p γ j y :=
          Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.mp hk)
      _ = _ := by simp
  have hr := (Complex.abs_re_le_norm (linear_nonstationary_symbol_expansion_remOp p R j 5 G y)).trans hremb
  calc _ ≤ |2 * π * ∑ k ∈ Finset.range 5, (∫ w, invFourierT (linear_nonstationary_symbol_expansion_m p R j y k) w *
        ((deriv G (y - w) : ℝ) : ℂ)).re| + |(linear_nonstationary_symbol_expansion_remOp p R j 5 G y).re| :=
        abs_add_le _ _
    _ ≤ 2 * π * (5 * (K * yNorm p γ G * c09_weights p γ j y)) +
        Crem * CL * yNorm p γ G * c09_weights p γ j y := by
        rw [abs_mul, abs_of_pos (by positivity)]
        gcongr
    _ ≤ _ := by
        have : 0 ≤ yNorm p γ G * c09_weights p γ j y := by positivity
        nlinarith

/-- `∂^n (2 Re f) = 2 Re ∂^n f` for smooth `f : ℝ → ℂ`. -/
private theorem c09_aux_iteratedDeriv_two_re (f : ℝ → ℂ) (n : ℕ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    iteratedDeriv n (fun y => 2 * (f y).re) = fun y => 2 * (iteratedDeriv n f y).re := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext y
    have hd : DifferentiableAt ℝ (iteratedDeriv n f) y :=
      (hf.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)).differentiableAt
    have := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hd.hasDerivAt).const_mul 2)
    rw [iteratedDeriv_succ]
    simpa using this.deriv

/-- `χ_s(y,·)` is continuous. -/
private theorem c09_aux_split_continuous (p y : ℝ) : Continuous (c09_stationary_split p y) := by
  unfold c09_stationary_split rho
  split_ifs <;> fun_prop

/-- def:c09_stationary_split (3): `K_{+,j}^R = K_{+,j}^{s,R} + K_{+,j}^{ns,R}`. -/
private theorem c09_aux_kernel_split (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (R : ℝ) (hR : 2 ≤ R)
    (j : ℕ) (hj : j ≤ 2) (y z : ℝ) :
    c09_positive_kernel p R j y z =
      c09_stationary_split_kernel_s p R j y z + c09_stationary_split_kernel_ns p R j y z := by
  obtain ⟨-, -, -, C, -, -, -, -, -, -, h3, -⟩ := c09_cutoff_bounds p hp hp1
  obtain ⟨-, hEc, -⟩ := c09_tail_basic p hp hp1
  set f : ℝ → ℂ := fun ξ => c09_positive_kernel_amp R j ξ *
    Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) * c09_tail_integral p z ξ with hfdef
  have hsub : Set.uIcc (1 : ℝ) (2 * R) ⊆ Ioi 0 := by
    rw [Set.uIcc_of_le (by linarith)]; intro x hx; exact lt_of_lt_of_le one_pos hx.1
  have hsub' : Set.uIcc (1 : ℝ) (2 * R) ⊆ Ici 0 := hsub.trans Set.Ioi_subset_Ici_self
  have hfc : ContinuousOn f (Set.uIcc 1 (2 * R)) := by
    have ha := ((h3 R hR j hj).1.continuousOn).mono hsub
    have hE : ContinuousOn (c09_tail_integral p z) (Ici 0) := by
      have := hEc.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
        (fun ξ (hξ : ξ ∈ Ici (0:ℝ)) => Set.mk_mem_prod (Set.mem_univ z) hξ)
      exact this
    have hexp : Continuous fun ξ : ℝ => Complex.exp (Complex.I * ((y * ξ - Phi0 p ξ : ℝ) : ℂ)) := by
      unfold Phi0
      have : Continuous fun ξ : ℝ => |ξ| ^ p := by
        exact Continuous.rpow_const continuous_abs (fun _ => Or.inr (by linarith))
      fun_prop
    exact (ha.mul hexp.continuousOn).mul (hE.mono hsub')
  have hχ := c09_aux_split_continuous p y
  have h1 : IntervalIntegrable (fun ξ => (c09_stationary_split p y ξ : ℂ) * f ξ) volume 1 (2 * R) :=
    ((Complex.continuous_ofReal.comp hχ).continuousOn.mul hfc).intervalIntegrable
  have h2 : IntervalIntegrable (fun ξ => ((1 - c09_stationary_split p y ξ : ℝ) : ℂ) * f ξ)
      volume 1 (2 * R) :=
    ((Complex.continuous_ofReal.comp (continuous_const.sub hχ)).continuousOn.mul
      hfc).intervalIntegrable
  have es : c09_stationary_split_kernel_s p R j y z =
      ∫ ξ in (1 : ℝ)..(2 * R), (c09_stationary_split p y ξ : ℂ) * f ξ := by
    unfold c09_stationary_split_kernel_s c09_stationary_split_amp_s
    congr 1; ext ξ; simp only [hfdef]; ring
  have ens : c09_stationary_split_kernel_ns p R j y z =
      ∫ ξ in (1 : ℝ)..(2 * R), ((1 - c09_stationary_split p y ξ : ℝ) : ℂ) * f ξ := by
    unfold c09_stationary_split_kernel_ns c09_stationary_split_amp_ns
      c09_stationary_split_chi_ns
    congr 1; ext ξ; simp only [hfdef]; ring
  rw [es, ens, ← intervalIntegral.integral_add h1 h2]
  unfold c09_positive_kernel
  congr 1; ext ξ; simp only [hfdef]; push_cast; ring

/-- Blueprint: lem:c09_truncated_high_bound.
`|∂_y^j 𝒯_h^R G(y)| ≤ C ‖G‖_{Y_γ} w_{γ,j}(y)` for `R ≥ R₀(y)`. -/
theorem c09_truncated_high_bound (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma_tilde p γ, ∀ j : ℕ, j ≤ 2 → ∀ y R : ℝ,
      c09_truncation_R0 p y ≤ R →
      |iteratedDeriv j (c09_truncation_high p R G) y| ≤ C * yNorm p γ G * c09_weights p γ j y := by
  obtain ⟨C1, hC1, hs⟩ := c09_stationary_contribution p hp hp1 γ hγ
  obtain ⟨C2, hC2, hns⟩ := c09_nonstationary_contribution p hp hp1 γ hγ
  obtain ⟨hrep, -⟩ := c09_kernel_representation p hp hp1 γ hγ
  refine ⟨2 * (C1 + C2), by positivity, fun G hG j hj y R hR => ?_⟩
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  obtain ⟨C_R, -, -, hG'⟩ := hrep R hR2
  obtain ⟨hsm, hder⟩ := hG' G hG
  obtain ⟨hint, heq⟩ := hder j hj y
  have hint_ns := ((linear_nonstationary_symbol_expansion p hp hp1 R hR2 y j hj 1 le_rfl).2.2
    γ hγ G hG).1
  have hint_s : Integrable (fun z => c09_stationary_split_kernel_s p R j y z *
      ((deriv G z : ℝ) : ℂ)) := by
    have := hint.sub hint_ns
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply, c09_aux_kernel_split p hp hp1 R hR2 j hj y z]; ring
  have hsplit : iteratedDeriv j (c09_truncation p R G) y =
      c09_stationary_split_op_s p R j G y + c09_stationary_split_op_ns p R j G y := by
    rw [heq]
    unfold c09_stationary_split_op_s c09_stationary_split_op_ns
    rw [← integral_add hint_s hint_ns]
    congr 1; ext z
    rw [c09_aux_kernel_split p hp hp1 R hR2 j hj y z]; ring
  have hfun : c09_truncation_high p R G = fun y => 2 * (c09_truncation p R G y).re := rfl
  rw [hfun, c09_aux_iteratedDeriv_two_re _ j hsm]
  dsimp only
  rw [hsplit, Complex.add_re]
  have b1 := hs G hG R hR2 j hj y
  have b2 := hns G hG j hj y R hR
  have b1' := le_trans (Complex.abs_re_le_norm (c09_stationary_split_op_s p R j G y)) b1
  have hw := c09_aux_weights_pos p γ j y
  have hN : 0 ≤ yNorm p γ G := ENNReal.toReal_nonneg
  rw [abs_mul, abs_two]
  calc 2 * |(c09_stationary_split_op_s p R j G y).re + (c09_stationary_split_op_ns p R j G y).re|
      ≤ 2 * (|(c09_stationary_split_op_s p R j G y).re| +
          |(c09_stationary_split_op_ns p R j G y).re|) := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * (C1 * yNorm p γ G * c09_weights p γ j y + C2 * yNorm p γ G * c09_weights p γ j y) := by
        gcongr
    _ = 2 * (C1 + C2) * yNorm p γ G * c09_weights p γ j y := by ring

/-- Mean value inequality on a segment. -/
private theorem c09_aux_mvt {f : ℝ → ℝ} {a b C : ℝ} (hf : Differentiable ℝ f)
    (hC : ∀ t ∈ uIcc a b, |deriv f t| ≤ C) : |f b - f a| ≤ C * |b - a| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (s := uIcc a b)
    (fun x _ => hf.differentiableAt) (fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx)
    (convex_uIcc a b) left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

/-- Blueprint: lem:c09_truncation_limit.  Passing to the limit `R → ∞`: uniform limits of `C²`
functions with locally uniform weighted bounds on `r_R, r_R', r_R''` are `W^{2,∞}_loc` with the
same bounds (`r''` a.e.). -/
theorem c09_truncation_limit (w : ℕ → ℝ → ℝ) (hw : ∀ j ≤ 2, Continuous (w j))
    (hwpos : ∀ j ≤ 2, ∀ y, 0 < w j y) (A : ℝ) (hA : 0 ≤ A) (r : ℝ → ℝ → ℝ) (rlim : ℝ → ℝ)
    (hr : ∀ R : ℝ, 2 ≤ R → ContDiff ℝ 2 (r R))
    (hlim : TendstoUniformly r rlim atTop)
    (hbd : ∀ Y : ℝ, 0 < Y → ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ, |y| ≤ Y →
      |iteratedDeriv j (r R) y| ≤ A * w j y) :
    ContDiff ℝ 1 rlim ∧ LocallyLipschitz (deriv rlim) ∧ W2inftyLoc rlim ∧
      (∀ y, |rlim y| ≤ A * w 0 y) ∧ (∀ y, |deriv rlim y| ≤ A * w 1 y) ∧
      (∀ᵐ y, |deriv (deriv rlim) y| ≤ A * w 2 y) := by
  -- smoothness of the approximants
  have hreg : ∀ R : ℝ, 2 ≤ R → Differentiable ℝ (r R) ∧ Differentiable ℝ (deriv (r R)) ∧
      Continuous (deriv (r R)) := by
    intro R hR
    have h2 : ContDiff ℝ (1 + 1) (r R) := hr R hR
    rw [contDiff_succ_iff_deriv] at h2
    exact ⟨h2.1, h2.2.2.differentiable (by norm_num), h2.2.2.continuous⟩
  have hid1 : ∀ R : ℝ, iteratedDeriv 1 (r R) = deriv (r R) := fun R => iteratedDeriv_one
  have hid2 : ∀ R : ℝ, iteratedDeriv 2 (r R) = deriv (deriv (r R)) := fun R => by
    simp [iteratedDeriv_succ]
  -- Step 1: Lipschitz bounds on `r_R'` with any local bound for `w₂`
  have step1 : ∀ Y : ℝ, 0 < Y → ∃ R₂ : ℝ, 2 ≤ R₂ ∧ ∀ R : ℝ, R₂ ≤ R → ∀ a b : ℝ,
      |a| ≤ Y → |b| ≤ Y → ∀ K : ℝ, (∀ t ∈ uIcc a b, w 2 t ≤ K) →
        |deriv (r R) b - deriv (r R) a| ≤ A * K * |b - a| := by
    intro Y hY
    obtain ⟨R₁, hR₁⟩ := hbd Y hY
    refine ⟨max 2 R₁, le_max_left _ _, fun R hR a b ha hb K hK => ?_⟩
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    apply c09_aux_mvt (hreg R hR2).2.1
    intro t ht
    have htY : |t| ≤ Y := by
      rw [abs_le] at ha hb ⊢
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at ht; constructor <;> linarith [ht.1, ht.2]
      · rw [uIcc_of_ge h] at ht; constructor <;> linarith [ht.1, ht.2]
    have := hR₁ R (le_trans (le_max_right _ _) hR) 2 le_rfl t htY
    rw [hid2] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hK t ht) hA)
  -- local bound for `w₂`
  have hM : ∀ Y : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |t| ≤ Y → w 2 t ≤ M := by
    intro Y
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -Y) (b := Y)).exists_bound_of_continuousOn
      (hw 2 le_rfl).continuousOn
    refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
    have := hM t (abs_le.mp ht)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  -- Step 2: Taylor estimate
  have step2 : ∀ Y : ℝ, 0 < Y → ∃ R₂ : ℝ, 2 ≤ R₂ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, R₂ ≤ R →
      ∀ y : ℝ, |y| ≤ Y → ∀ h : ℝ, 0 < h → h ≤ 1 →
        |r R (y + h) - r R y - h * deriv (r R) y| ≤ A * M * h * h := by
    intro Y hY
    obtain ⟨R₂, hR₂, h1⟩ := step1 (Y + 1) (by linarith)
    obtain ⟨M, hM0, hMb⟩ := hM (Y + 1)
    refine ⟨R₂, hR₂, M, hM0, fun R hR y hy h hh0 hh1 => ?_⟩
    have hR2 : 2 ≤ R := le_trans hR₂ hR
    set φ : ℝ → ℝ := fun t => r R t - t * deriv (r R) y with hφ
    have hφd : ∀ t, HasDerivAt φ (deriv (r R) t - deriv (r R) y) t := by
      intro t
      have h := ((hreg R hR2).1 t).hasDerivAt.sub ((hasDerivAt_id t).mul_const (deriv (r R) y))
      simp only [hφ]
      convert h using 1
      · ext u; simp
      · simp
    have hφdiff : Differentiable ℝ φ := fun t => (hφd t).differentiableAt
    have := c09_aux_mvt (a := y) (b := y + h) (C := A * M * h) hφdiff (by
      intro t ht
      rw [(hφd t).deriv]
      rw [uIcc_of_le (by linarith)] at ht
      have hty : |t| ≤ Y + 1 := by rw [abs_le] at hy ⊢; constructor <;> linarith [ht.1, ht.2]
      have := h1 R hR y t (by linarith) hty M (fun u hu => hMb u (by
        rw [uIcc_of_le ht.1] at hu
        rw [abs_le] at hy ⊢; constructor <;> linarith [hu.1, hu.2, ht.2]))
      calc |deriv (r R) t - deriv (r R) y| ≤ A * M * |t - y| := this
        _ ≤ A * M * h := by
          gcongr
          rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2])
    simp only [hφ] at this
    rw [show y + h - y = h by ring, abs_of_pos hh0] at this
    calc |r R (y + h) - r R y - h * deriv (r R) y|
        = |r R (y + h) - (y + h) * deriv (r R) y - (r R y - y * deriv (r R) y)| := by ring_nf
      _ ≤ A * M * h * h := this
  -- the limit of the derivatives
  set g : ℝ → ℝ := fun y => limUnder atTop (fun R => deriv (r R) y) with hg
  -- Step 3: uniform convergence of `r_R'` on `[-Y, Y]`
  have step3 : ∀ Y : ℝ, 0 < Y →
      TendstoUniformlyOn (fun R => deriv (r R)) g atTop (Icc (-Y) Y) := by
    intro Y hY
    obtain ⟨R₂, hR₂, M, hM0, hT⟩ := step2 Y hY
    have hUC : UniformCauchySeqOn (fun R => deriv (r R)) atTop (Icc (-Y) Y) := by
      rw [Metric.uniformCauchySeqOn_iff]
      intro ε hε
      set h : ℝ := min 1 (ε / (4 * (A * M + 1))) with hh
      have hh0 : 0 < h := lt_min one_pos (by positivity)
      have hh1 : h ≤ 1 := min_le_left _ _
      have hhε : A * M * h ≤ ε / 4 := by
        have : h ≤ ε / (4 * (A * M + 1)) := min_le_right _ _
        have hAM : 0 ≤ A * M := mul_nonneg hA hM0
        calc A * M * h ≤ (A * M + 1) * h := by nlinarith
          _ ≤ (A * M + 1) * (ε / (4 * (A * M + 1))) := by gcongr
          _ = ε / 4 := by field_simp
      have hu := Metric.tendstoUniformly_iff.mp hlim (ε * h / 8) (by positivity)
      rw [eventually_atTop] at hu
      obtain ⟨N, hN⟩ := hu
      refine ⟨max N R₂, fun m hm n hn y hy => ?_⟩
      have hy' : |y| ≤ Y := abs_le.mpr ⟨hy.1, hy.2⟩
      have hmN := hN m (le_trans (le_max_left _ _) hm)
      have hnN := hN n (le_trans (le_max_left _ _) hn)
      have tm := hT m (le_trans (le_max_right _ _) hm) y hy' h hh0 hh1
      have tn := hT n (le_trans (le_max_right _ _) hn) y hy' h hh0 hh1
      have d1 := hmN (y + h); have d2 := hmN y; have d3 := hnN (y + h); have d4 := hnN y
      rw [Real.dist_eq] at d1 d2 d3 d4 ⊢
      rw [abs_lt] at d1 d2 d3 d4
      rw [abs_le] at tm tn
      have key : |h * (deriv (r m) y - deriv (r n) y)| < h * ε := by
        rw [abs_lt]; constructor <;> nlinarith
      rw [abs_mul, abs_of_pos hh0] at key
      exact lt_of_mul_lt_mul_left key hh0.le
    refine hUC.tendstoUniformlyOn_of_tendsto fun y hy => ?_
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hUC.cauchySeq hy)
    rw [hg]; simp only; rw [hL.limUnder_eq]; exact hL
  -- pointwise convergence of `r_R`
  have hpt : ∀ y, Tendsto (fun R => r R y) atTop (nhds (rlim y)) := fun y => hlim.tendsto_at y
  have hev2 : ∀ᶠ R in atTop, (2 : ℝ) ≤ R := eventually_ge_atTop 2
  -- Step 4: `rlim' = g`
  have hderiv : ∀ x, HasDerivAt rlim (g x) x := by
    intro x
    have hY : 0 < |x| + 1 := by positivity
    refine hasDerivAt_of_tendstoUniformlyOn (s := Ioo (-(|x| + 1)) (|x| + 1)) isOpen_Ioo
      ((step3 _ hY).mono Ioo_subset_Icc_self) ?_ (fun y _ => hpt y) ?_
    · filter_upwards [hev2] with R hR y _ using ((hreg R hR).1 y).hasDerivAt
    · constructor <;> linarith [neg_abs_le x, le_abs_self x]
  have hdg : deriv rlim = g := funext fun x => (hderiv x).deriv
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hY : 0 < |x| + 1 := by positivity
    have hco : ContinuousOn g (Ioo (-(|x| + 1)) (|x| + 1)) :=
      ((step3 _ hY).mono Ioo_subset_Icc_self).continuousOn
        (Filter.Eventually.frequently (by
          filter_upwards [hev2] with R hR using (hreg R hR).2.2.continuousOn))
    exact hco.continuousAt (isOpen_Ioo.mem_nhds
      (by constructor <;> linarith [neg_abs_le x, le_abs_self x]))
  have hC1 : ContDiff ℝ 1 rlim := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun x => (hderiv x).differentiableAt, hdg ▸ hgc⟩
  -- pointwise convergence of the derivatives
  have hptd : ∀ y, Tendsto (fun R => deriv (r R) y) atTop (nhds (g y)) := by
    intro y
    have hY : 0 < |y| + 1 := by positivity
    exact (step3 _ hY).tendsto_at
      (by constructor <;> linarith [neg_abs_le y, le_abs_self y])
  -- Step 7: Lipschitz bounds for `g` from those of the `r_R'`
  have glip : ∀ Y : ℝ, 0 < Y → ∀ a b : ℝ, |a| ≤ Y → |b| ≤ Y → ∀ K : ℝ,
      (∀ t ∈ uIcc a b, w 2 t ≤ K) → |g b - g a| ≤ A * K * |b - a| := by
    intro Y hY a b ha hb K hK
    obtain ⟨R₂, -, h1⟩ := step1 Y hY
    have ht : Tendsto (fun R => |deriv (r R) b - deriv (r R) a|) atTop (nhds (|g b - g a|)) :=
      ((hptd b).sub (hptd a)).abs
    exact le_of_tendsto ht (by
      filter_upwards [eventually_ge_atTop R₂] with R hR using h1 R hR a b ha hb K hK)
  have hLL : LocallyLipschitz (deriv rlim) := by
    rw [hdg]
    intro x
    have hY : 0 < |x| + 1 := by positivity
    obtain ⟨M, hM0, hMb⟩ := hM (|x| + 1)
    refine ⟨Real.toNNReal (A * M), Ioo (-(|x| + 1)) (|x| + 1),
      isOpen_Ioo.mem_nhds (by constructor <;> linarith [neg_abs_le x, le_abs_self x]), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have ha' : |a| ≤ |x| + 1 := abs_le.mpr ⟨ha.1.le, ha.2.le⟩
    have hb' : |b| ≤ |x| + 1 := abs_le.mpr ⟨hb.1.le, hb.2.le⟩
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hA hM0), abs_sub_comm,
      abs_sub_comm a b]
    exact glip _ hY a b ha' hb' M (fun t ht => hMb t (by
      rw [abs_le] at ha' hb' ⊢
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at ht; constructor <;> linarith [ht.1, ht.2]
      · rw [uIcc_of_ge h] at ht; constructor <;> linarith [ht.1, ht.2]))
  refine ⟨hC1, hLL, ⟨hC1, hLL⟩, fun y => ?_, fun y => ?_, Eventually.of_forall fun y => ?_⟩
  · -- `|r| ≤ A w₀`
    have hY : 0 < |y| + 1 := by positivity
    obtain ⟨R₁, hR₁⟩ := hbd _ hY
    exact le_of_tendsto (hpt y).abs (by
      filter_upwards [eventually_ge_atTop R₁] with R hR
      have := hR₁ R hR 0 (by norm_num) y (by linarith)
      simpa using this)
  · -- `|r'| ≤ A w₁`
    have hY : 0 < |y| + 1 := by positivity
    obtain ⟨R₁, hR₁⟩ := hbd _ hY
    rw [hdg]
    exact le_of_tendsto (hptd y).abs (by
      filter_upwards [eventually_ge_atTop R₁] with R hR
      have := hR₁ R hR 1 (by norm_num) y (by linarith)
      rwa [hid1] at this)
  · -- `|r''| ≤ A w₂` (everywhere)
    rw [hdg]
    have hw2 := hwpos 2 le_rfl y
    by_cases hd : DifferentiableAt ℝ g y
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      have hε' : 0 < ε / (2 * (A + 1)) := by positivity
      obtain ⟨δ, hδ, hδw⟩ := Metric.continuousAt_iff.mp (hw 2 le_rfl).continuousAt _ hε'
      set δ' := min δ 1 with hδ'
      have hδ'0 : 0 < δ' := lt_min hδ one_pos
      have hY : 0 < |y| + 1 := by positivity
      have hlip : LipschitzOnWith (Real.toNNReal (A * (w 2 y + ε / (2 * (A + 1)))))
          g (Ioo (y - δ') (y + δ')) := by
        refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity), abs_sub_comm,
          abs_sub_comm a b]
        have hab : ∀ t ∈ uIcc a b, |t - y| < δ' := by
          intro t ht
          rcases le_total a b with h | h
          · rw [uIcc_of_le h] at ht
            rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ha.1, hb.2]
          · rw [uIcc_of_ge h] at ht
            rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, hb.1, ha.2]
        have hδ'1 : δ' ≤ 1 := min_le_right _ _
        have hδ'δ : δ' ≤ δ := min_le_left _ _
        refine glip (|y| + 1) hY a b ?_ ?_ _ fun t ht => ?_
        · rw [abs_le]; constructor <;> linarith [ha.1, ha.2, neg_abs_le y, le_abs_self y]
        · rw [abs_le]; constructor <;> linarith [hb.1, hb.2, neg_abs_le y, le_abs_self y]
        · have := hδw (show dist t y < δ by rw [Real.dist_eq]; linarith [hab t ht])
          rw [Real.dist_eq, abs_lt] at this
          linarith [this.2]
      have := hd.hasDerivAt.le_of_lipschitzOn
        (Ioo_mem_nhds (by linarith) (by linarith)) hlip
      rw [Real.norm_eq_abs, Real.coe_toNNReal _ (by positivity)] at this
      calc |deriv g y| ≤ A * (w 2 y + ε / (2 * (A + 1))) := this
        _ = A * w 2 y + A / (A + 1) * (ε / 2) := by field_simp
        _ < A * w 2 y + ε := by
          have : A / (A + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
          nlinarith
    · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
      positivity

/-- Blueprint: prop:linear_high_frequency.  For admissible `γ` and `G ∈ Ỹ_γ`: `𝒯_h G ∈ X_γ` and
`‖𝒯_h G‖_{X_γ} ≤ C_h(γ) ‖G‖_{Y_γ}`.  (We also record that `T_high p G` is a genuine representative,
`\widehat{𝒯_h G} = (1-χ) m_G`, so that the statement is not satisfied by the junk value `0`.) -/
theorem linear_high_frequency (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧ ∀ G ∈ Y_gamma_tilde p γ,
      HasDistFourier (fun x => (T_high p G x : ℂ))
        (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ) ∧
      T_high p G ∈ X_gamma p γ ∧ xNorm p γ (T_high p G) ≤ C * yNorm p γ G := by
  obtain ⟨C, hC, hbd⟩ := c09_truncated_high_bound p hp hp1 γ hγ
  obtain ⟨hrep, hconv⟩ := c09_kernel_representation p hp hp1 γ hγ
  obtain ⟨-, hX, -⟩ := c09_weight_facts p hp hp1 γ hγ
  refine ⟨6 * C, by positivity, fun G hG => ?_⟩
  have hF := (c09_conjugate_symmetry p hp hp1 γ hγ G hG.1).2.2.2 hG
  have hA : 0 ≤ C * yNorm p γ G := mul_nonneg hC.le ENNReal.toReal_nonneg
  have hsmooth : ∀ R : ℝ, 2 ≤ R → ContDiff ℝ 2 (c09_truncation_high p R G) := by
    intro R hR
    obtain ⟨C_R, -, -, hG'⟩ := hrep R hR
    have h := (hG' G hG).1
    have h2 : ContDiff ℝ 2 (c09_truncation p R G) := h.of_le (by simp)
    exact contDiff_const.mul (Complex.reCLM.contDiff.comp h2)
  have hlim := (hconv G hG).2
  have hb : ∀ Y : ℝ, 0 < Y → ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R → ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ, |y| ≤ Y →
      |iteratedDeriv j (c09_truncation_high p R G) y| ≤
        (C * yNorm p γ G) * c09_weights p γ j y := by
    intro Y hY
    refine ⟨max 2 (jb Y ^ (1 / p)), fun R hR j hj y hy => hbd G hG j hj y R ?_⟩
    refine le_trans ?_ hR
    unfold c09_truncation_R0
    apply max_le_max le_rfl
    have hp0 : 0 < p := by linarith
    exact Real.rpow_le_rpow (c09_aux_jb_pos y).le (c09_aux_jb_mono hy) (by positivity)
  obtain ⟨h1, h2, -, h3, h4, h5⟩ := c09_truncation_limit (c09_weights p γ)
    (fun j _ => c09_aux_weights_continuous p γ j) (fun j _ y => c09_aux_weights_pos p γ j y)
    (C * yNorm p γ G) hA (fun R => c09_truncation_high p R G) (T_high p G) hsmooth hlim hb
  obtain ⟨hmem, hnorm⟩ := hX (T_high p G) (C * yNorm p γ G) h1 h2 h3 h4 h5
  exact ⟨hF.2.1, hmem, by linarith⟩

/-! ### Chapter 02 and 08 results used in the assembly

Wrappers (subsets of conjuncts) of statements of `GSQG/Sec6_LinearInverse/ConjugationAndLowFrequency.lean` and `GSQG/Sec3_FixedPoint/FixedPointArgument.lean`, proved
from the declarations named in their docstrings. -/

/-- Wrapper for `ConjugationAndLowFrequency` `GSQG.linear_ell_continuity` (prop:linear_ell_continuity), first two items
(the integral representation of `ℓ` and the closedness of `Ỹ_γ` omitted): for `γ > β + 1/p` the
limit defining `ℓ(G)` exists, `|ℓ(G)| ≤ C‖G‖_{Y_γ}`, and `ℓ` is `ℝ`-linear on `Y_γ`. -/
theorem c09_ext_linear_ell_continuity (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : beta p + 1 / p < γ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ G ∈ Y_gamma p γ,
        Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
            (ξ : ℂ) * Complex.exp (Complex.I * (Phi0 p ξ : ℂ)) * fourierT (fun x => (G x : ℂ)) ξ)
          atTop (nhds (ell p G)) ∧
        ‖ell p G‖ ≤ C * yNorm p γ G) ∧
      (∀ G ∈ Y_gamma p γ, ∀ H ∈ Y_gamma p γ, ∀ a : ℝ,
        ell p (a • G + H) = (a : ℂ) * ell p G + ell p H) := by
  obtain ⟨C, hC, h1, h2, -⟩ := linear_ell_continuity p γ hp hp1 hγ
  exact ⟨C, hC, fun G hG => ⟨(h1 G hG).1, (h1 G hG).2.2.2⟩, h2⟩

/-- Wrapper for `ConjugationAndLowFrequency` `GSQG.c08_T0_right_inverse` (lem:c08_T0_right_inverse):
if `r ∈ X_γ` has `r̂ = m_G` then `ℒ₀ r = G` pointwise. -/
theorem c09_ext_T0_right_inverse (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 + 1 / p < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ) (r : ℝ → ℝ) (hr : r ∈ X_gamma p γ)
    (hrG : HasDistFourier (fun x => (r x : ℂ)) (T_0_symbol p G)) :
    ∀ y, L0 p r y = G y :=
  c08_T0_right_inverse p γ hp hp1 hγ G hG r hr hrG

/-- Wrapper for `ConjugationAndLowFrequency` `GSQG.linear_conjugation` (lem:linear_conjugation), items (1), (3), (5)
(the linearity conjuncts of (1) and items (2), (4) omitted; the remaining conjuncts are verbatim). -/
theorem c09_ext_linear_conjugation (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, admissibleGamma p γ → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
        -- (1)
        (Function.LeftInverse (U_eps_inv p ε) (U_eps p ε) ∧
          Function.RightInverse (U_eps_inv p ε) (U_eps p ε) ∧
          Function.LeftInverse (V_eps_inv p ε) (V_eps p ε) ∧
          Function.RightInverse (V_eps_inv p ε) (V_eps p ε) ∧
          Set.BijOn (U_eps p ε) (X_gamma p γ) (X_gamma p γ) ∧
          Set.BijOn (V_eps p ε) (Y_gamma p γ) (Y_gamma p γ) ∧
          Set.MapsTo (U_eps_inv p ε) (X_gamma p γ) (X_gamma p γ) ∧
          Set.MapsTo (V_eps_inv p ε) (Y_gamma p γ) (Y_gamma p γ) ∧
          (∀ r ∈ X_gamma p γ, xNorm p γ (U_eps p ε r) ≤ C * xNorm p γ r ∧
            xNorm p γ (U_eps_inv p ε r) ≤ C * xNorm p γ r) ∧
          (∀ G ∈ Y_gamma p γ, yNorm p γ (V_eps p ε G) ≤ C * yNorm p γ G ∧
            yNorm p γ (V_eps_inv p ε G) ≤ C * yNorm p γ G)) ∧
        -- (3)
        (∀ r ∈ X_gamma p γ, ∀ y : ℝ, V_eps p ε (L0 p (U_eps p ε r)) y = L_eps p ε r y) ∧
        -- (5)
        (∀ δ : ℝ, 0 < δ → ∀ μ ∈ Bbar p δ,
          V_eps_inv p ε (G_mu p μ) - G_mu p μ ∈ Y_gamma p γ ∧
          yNorm p γ (V_eps_inv p ε (G_mu p μ) - G_mu p μ) ≤ C * ε * δ / ‖mu_star p‖) := by
  obtain ⟨εc, hεc, h⟩ := linear_conjugation p hp hp1
  refine ⟨εc, hεc, fun γ hγ => ?_⟩
  obtain ⟨C, hC, h⟩ := h γ hγ
  refine ⟨C, hC, fun ε hε hε' => ?_⟩
  obtain ⟨⟨-, -, h1⟩, -, h3, -, h5⟩ := h ε hε hε'
  exact ⟨h1, h3, h5⟩

/-- Admissible exponents satisfy `1 + 1/p < γ ≤ p + 2` (as `β > 1` and `2p+1 < p+2`). -/
private theorem c09_aux_admissible_range (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) : 1 + 1 / p < γ ∧ γ ≤ p + 2 := by
  obtain ⟨h1, h2⟩ := hγ
  have hp0 : 0 < p := by linarith
  have hβ : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by positivity)]; linarith
  constructor <;> linarith

/-- Wrapper for `ConjugationAndLowFrequency` `GSQG.linear_low_frequency` (prop:linear_low_frequency). -/
theorem c09_ext_linear_low_frequency (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (hγ' : γ < p + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ G ∈ Y_gamma p γ,
      ContDiff ℝ (⊤ : ℕ∞) (T_low p G) ∧ T_low p G ∈ X_gamma p γ ∧
      xNorm p γ (T_low p G) ≤ C * yNorm p γ G ∧
      HasDistFourier (fun y => (T_low p G y : ℂ)) (fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ) :=
  linear_low_frequency p γ hp hp1 hγ hγ'

/-- Wrapper for `ConjugationAndLowFrequency` `GSQG.c08_frequency_split_sum` (lem:c08_frequency_split_sum). -/
theorem c09_ext_frequency_split_sum (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : 1 < γ)
    (G : ℝ → ℝ) (hG : G ∈ Y_gamma p γ)
    (hl : T_low p G ∈ X_gamma p γ) (hh : T_high p G ∈ X_gamma p γ)
    (hhF : HasDistFourier (fun x => (T_high p G x : ℂ))
      (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ)) :
    T_0 p G = T_low p G + T_high p G ∧
    HasDistFourier (fun x => (T_0 p G x : ℂ)) (T_0_symbol p G) ∧
    T_0 p G ∈ X_gamma p γ ∧
    xNorm p γ (T_0 p G) ≤ xNorm p γ (T_low p G) + xNorm p γ (T_high p G) :=
  c08_frequency_split_sum p γ hp hp1 hγ G hG hl hh hhF

/-- Wrapper for `FixedPointArgument` `GSQG.c02_Y_gamma_banach` (lem:c02_Y_gamma_banach), the two closure items:
`Y_γ` is closed under sums and scalar multiples. -/
theorem c09_ext_Y_gamma_banach (P : parameters) (γ : ℝ) :
    (∀ G ∈ Y_gamma P.p γ, ∀ H ∈ Y_gamma P.p γ,
      G + H ∈ Y_gamma P.p γ ∧ yNorm P.p γ (G + H) ≤ yNorm P.p γ G + yNorm P.p γ H) ∧
    (∀ c : ℝ, ∀ G ∈ Y_gamma P.p γ, c • G ∈ Y_gamma P.p γ ∧
      yNorm P.p γ (c • G) = |c| * yNorm P.p γ G) :=
  ⟨(c02_Y_gamma_banach P γ).2.1, (c02_Y_gamma_banach P γ).2.2.1⟩

/-! ### Assembly -/

/-- Linearity of the Fourier transform on integrable real functions. -/
private theorem c09_aux_fourierT_lin (G H : ℝ → ℝ) (hG : Integrable G) (hH : Integrable H)
    (a b : ℝ) (ξ : ℝ) :
    fourierT (fun x => (((a • G + b • H) x : ℝ) : ℂ)) ξ =
      (a : ℂ) * fourierT (fun x => (G x : ℂ)) ξ + (b : ℂ) * fourierT (fun x => (H x : ℂ)) ξ := by
  unfold fourierT
  have hc : Continuous fun x : ℝ => Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ))) := by fun_prop
  have iG : Integrable (fun x => (G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) :=
    hG.ofReal.mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun x => (c09_aux_norm_exp_neg x ξ).le)
  have iH : Integrable (fun x => (H x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) :=
    hH.ofReal.mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall fun x => (c09_aux_norm_exp_neg x ξ).le)
  have e : (fun x => (((a • G + b • H) x : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) =
      fun x => (a : ℂ) * ((G x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) +
        (b : ℂ) * ((H x : ℂ) * Complex.exp (-(Complex.I * (x : ℂ) * (ξ : ℂ)))) := by
    ext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  rw [e, integral_add (iG.const_mul _) (iH.const_mul _), integral_const_mul, integral_const_mul]

/-- Linearity of the symbol `m_G` on integrable `G`. -/
private theorem c09_aux_T0_symbol_lin (p : ℝ) (hp : 3 / 4 < p) (G H : ℝ → ℝ) (hG : Integrable G)
    (hH : Integrable H) (a b : ℝ) :
    T_0_symbol p (a • G + b • H) =
      fun ξ => (a : ℂ) * T_0_symbol p G ξ + (b : ℂ) * T_0_symbol p H ξ := by
  funext ξ
  unfold T_0_symbol
  have hrp : Continuous fun t : ℝ => t ^ (p + 1) := Real.continuous_rpow_const (by linarith)
  have hcont : ∀ K : ℝ → ℝ, Integrable K → Continuous fun t : ℝ => (t : ℂ) *
      Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) *
        fourierT (fun x => (K x : ℂ)) (t * ξ) := by
    intro K hK
    have hF := c09_aux_fourierT_continuous K hK
    have h1 : Continuous fun t : ℝ => fourierT (fun x => (K x : ℂ)) (t * ξ) :=
      hF.comp (continuous_id.mul continuous_const)
    have h2 : Continuous fun t : ℝ => (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_const.sub hrp).mul continuous_const)
    exact (Complex.continuous_ofReal.mul ((continuous_const.mul h2).neg.cexp)).mul h1
  have iG := (hcont G hG).intervalIntegrable (μ := volume) 0 1
  have iH := (hcont H hH).intervalIntegrable (μ := volume) 0 1
  have e : (fun t : ℝ => (t : ℂ) *
      Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) *
        fourierT (fun x => (((a • G + b • H) x : ℝ) : ℂ)) (t * ξ)) =
      fun t : ℝ => (a : ℂ) * ((t : ℂ) *
        Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) *
          fourierT (fun x => (G x : ℂ)) (t * ξ)) + (b : ℂ) * ((t : ℂ) *
        Complex.exp (-(Complex.I * (((1 - t ^ (p + 1)) * Phi0 p ξ : ℝ) : ℂ))) *
          fourierT (fun x => (H x : ℂ)) (t * ξ)) := by
    ext t; rw [c09_aux_fourierT_lin G H hG hH a b]; ring
  rw [e, intervalIntegral.integral_add (iG.const_mul _) (iH.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- `ρ` is continuous with compact support. -/
private theorem c09_aux_rho_props : Continuous rho ∧ HasCompactSupport rho := by
  refine ⟨by unfold rho; fun_prop, ?_⟩
  refine HasCompactSupport.intro (K := Icc (-2) 2) isCompact_Icc fun x hx => ?_
  unfold rho
  apply Real.smoothTransition.zero_of_nonpos
  have : 2 < |x| := by
    by_contra h; exact hx (abs_le.mp (not_lt.mp h))
  linarith

/-- For `G ∈ Ỹ_γ`: `𝒯₀ G = Re (χ m_G)^∨ + Re ((1-χ) m_G)^∨`. -/
private theorem c09_aux_T0_formula (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) (G : ℝ → ℝ) (hG : G ∈ Y_gamma_tilde p γ) :
    T_0 p G = fun y => (invFourierT (fun ξ => (rho ξ : ℂ) * T_0_symbol p G ξ) y).re +
      (invFourierT (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ) y).re := by
  have hp0 : 0 < p := by linarith
  have h1 : 1 < γ := by
    have := hγ.1; unfold beta at this
    have : 1 < 1 / p := by rw [lt_div_iff₀ hp0]; linarith
    have : 0 < (p + 1) / (2 * p) := by positivity
    linarith
  have h2 : γ < p + 2 := by linarith [hγ.2]
  obtain ⟨Cl, -, hl⟩ := c09_ext_linear_low_frequency p γ hp hp1 h1 h2
  obtain ⟨Ch, -, hh⟩ := linear_high_frequency p hp hp1 γ hγ
  obtain ⟨-, hlX, -, -⟩ := hl G hG.1
  obtain ⟨hhF, hhX, -⟩ := hh G hG
  obtain ⟨hsum, -⟩ := c09_ext_frequency_split_sum p γ hp hp1 h1 G hG.1 hlX hhX hhF
  have hcs := (c09_conjugate_symmetry p hp hp1 γ hγ G hG.1).2.2.2 hG
  rw [hsum]
  funext y
  simp only [Pi.add_apply]
  congr 1
  have := congrArg Complex.re (hcs.2.2.1 y)
  simpa using this

/-- `Y_{γ'} ⊆ Y_γ` for `γ ≤ γ'`. -/
private theorem c09_aux_Y_mono (p : ℝ) {γ γ' : ℝ} (h : γ ≤ γ') (G : ℝ → ℝ)
    (hG : G ∈ Y_gamma p γ') : G ∈ Y_gamma p γ := by
  refine ⟨hG.1, lt_of_le_of_lt ?_ hG.2⟩
  have hw : ∀ y : ℝ, jb y ^ γ ≤ jb y ^ γ' := fun y =>
    Real.rpow_le_rpow_of_exponent_le (c09_aux_one_le_jb y) h
  unfold Y_gamma_norm
  gcongr
  · refine essSup_mono_ae (Eventually.of_forall fun y => ?_)
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ ‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖ := by
      have := c09_aux_jb_pos y; positivity
    exact mul_le_mul_of_nonneg_right (hw y) this
  · refine essSup_mono_ae (Eventually.of_forall fun y => ?_)
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ ‖G y‖ + jb y * ‖deriv G y‖ := by
      have := c09_aux_jb_pos y; positivity
    exact mul_le_mul_of_nonneg_right (hw y) this

/-- Blueprint: lem:c09_T0_bounded.  For `G ∈ Ỹ_γ`, `r = 𝒯_l G + 𝒯_h G ∈ X_γ` has `r̂ = m_G`, so
it is `𝒯₀ G`; `‖𝒯₀ G‖_{X_γ} ≤ C_T(γ) ‖G‖_{Y_γ}`; `𝒯₀` is `ℝ`-linear on `Ỹ_γ`; and
`Ỹ_{γ'} ⊆ Ỹ_γ` for admissible `γ ≤ γ'` (the formula for `𝒯₀` does not involve `γ`). -/
theorem c09_T0_bounded (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (γ : ℝ)
    (hγ : admissibleGamma p γ) :
    ∃ C, 0 < C ∧
      (∀ G ∈ Y_gamma_tilde p γ,
        (fun y => T_low p G y + T_high p G y) ∈ X_gamma p γ ∧
        HasDistFourier (fun y => ((T_low p G y + T_high p G y : ℝ) : ℂ)) (T_0_symbol p G) ∧
        T_0 p G = (fun y => T_low p G y + T_high p G y) ∧
        HasDistFourier (fun y => (T_0 p G y : ℂ)) (T_0_symbol p G) ∧
        xNorm p γ (T_0 p G) ≤ C * yNorm p γ G) ∧
      (∀ G ∈ Y_gamma_tilde p γ, ∀ H ∈ Y_gamma_tilde p γ, ∀ a b : ℝ,
        T_0 p (a • G + b • H) = a • T_0 p G + b • T_0 p H) ∧
      (∀ γ', admissibleGamma p γ' → γ ≤ γ' → Y_gamma_tilde p γ' ⊆ Y_gamma_tilde p γ) := by
  have hp0 : 0 < p := by linarith
  have h1 : 1 < γ := by
    have := hγ.1; unfold beta at this
    have : 1 < 1 / p := by rw [lt_div_iff₀ hp0]; linarith
    have : 0 < (p + 1) / (2 * p) := by positivity
    linarith
  have h2 : γ < p + 2 := by linarith [hγ.2]
  obtain ⟨Cl, hCl, hl⟩ := c09_ext_linear_low_frequency p γ hp hp1 h1 h2
  obtain ⟨Ch, hCh, hh⟩ := linear_high_frequency p hp hp1 γ hγ
  refine ⟨Cl + Ch, by positivity, fun G hG => ?_, fun G hG H hH a b => ?_,
    fun γ' _ hle G hG => ⟨c09_aux_Y_mono p hle G hG.1, hG.2⟩⟩
  · obtain ⟨-, hlX, hln, -⟩ := hl G hG.1
    obtain ⟨hhF, hhX, hhn⟩ := hh G hG
    obtain ⟨hsum, hF, hX, hn⟩ := c09_ext_frequency_split_sum p γ hp hp1 h1 G hG.1 hlX hhX hhF
    have e : (fun y => T_low p G y + T_high p G y) = T_0 p G := by rw [hsum]; rfl
    have e' : (fun y => ((T_low p G y + T_high p G y : ℝ) : ℂ)) = fun y => (T_0 p G y : ℂ) := by
      rw [hsum]; rfl
    refine ⟨e ▸ hX, e' ▸ hF, e.symm, hF, ?_⟩
    linarith
  · -- linearity
    let P : parameters :=
      { p := p, γ₁ := γ, γ₂ := (γ + (2 * p + 1)) / 2, hp_lo := hp, hp_hi := hp1,
        hγ₁ := hγ.1, hγ₁₂ := by linarith [hγ.2], hγ₂ := by linarith [hγ.2] }
    have hYc := c09_ext_Y_gamma_banach P γ
    have hbH : b • H ∈ Y_gamma p γ := (hYc.2 b H hH.1).1
    have hK : a • G + b • H ∈ Y_gamma p γ := (hYc.1 _ (hYc.2 a G hG.1).1 _ hbH).1
    have h0Y : (0 : ℝ → ℝ) ∈ Y_gamma p γ := by
      have := (hYc.2 0 G hG.1).1; simpa using this
    obtain ⟨-, -, -, hlin⟩ := c09_ext_linear_ell_continuity p γ hp hp1 hγ.1
    have hell0 : ell p 0 = 0 := by
      have := hlin 0 h0Y 0 h0Y 1
      simp only [smul_zero, add_zero, Complex.ofReal_one, one_mul] at this
      have h' : ell p 0 + ell p 0 - ell p 0 = ell p 0 - ell p 0 := by rw [← this]
      simpa using h'
    have hellbH : ell p (b • H) = 0 := by
      have := hlin H hH.1 0 h0Y b
      rw [add_zero] at this
      rw [this, hH.2, hell0]; ring
    have hKt : a • G + b • H ∈ Y_gamma_tilde p γ := by
      refine ⟨hK, ?_⟩
      rw [hlin G hG.1 (b • H) hbH a, hG.2, hellbH]; ring
    obtain ⟨-, -, -, ⟨C3, -, h3⟩, -⟩ := c09_weight_facts p hp hp1 γ hγ
    have iG := (h3 G hG.1).1
    have iH := (h3 H hH.1).1
    have hρ := c09_aux_rho_props
    have intlow : ∀ F ∈ Y_gamma_tilde p γ,
        Integrable (fun ξ => (rho ξ : ℂ) * T_0_symbol p F ξ) := by
      intro F hF
      have hc := (c09_conjugate_symmetry p hp hp1 γ hγ F hF.1).1
      have hcs : HasCompactSupport (fun ξ => (rho ξ : ℂ)) :=
        hρ.2.comp_left Complex.ofReal_zero
      exact ((Complex.continuous_ofReal.comp hρ.1).mul hc).integrable_of_hasCompactSupport
        (hcs.mul_right (f' := T_0_symbol p F))
    have inthigh : ∀ F ∈ Y_gamma_tilde p γ,
        Integrable (fun ξ => ((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p F ξ) := fun F hF =>
      ((c09_conjugate_symmetry p hp hp1 γ hγ F hF.1).2.2.2 hF).1
    rw [c09_aux_T0_formula p hp hp1 γ hγ _ hKt, c09_aux_T0_formula p hp hp1 γ hγ G hG,
      c09_aux_T0_formula p hp hp1 γ hγ H hH, c09_aux_T0_symbol_lin p hp G H iG iH a b]
    funext y
    have e1 : (fun ξ => (rho ξ : ℂ) * ((a : ℂ) * T_0_symbol p G ξ + (b : ℂ) * T_0_symbol p H ξ)) =
        fun ξ => (a : ℂ) * ((rho ξ : ℂ) * T_0_symbol p G ξ) +
          (b : ℂ) * ((rho ξ : ℂ) * T_0_symbol p H ξ) := by ext ξ; ring
    have e2 : (fun ξ => ((1 - rho ξ : ℝ) : ℂ) *
        ((a : ℂ) * T_0_symbol p G ξ + (b : ℂ) * T_0_symbol p H ξ)) =
        fun ξ => (a : ℂ) * (((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p G ξ) +
          (b : ℂ) * (((1 - rho ξ : ℝ) : ℂ) * T_0_symbol p H ξ) := by ext ξ; ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, c09_aux_invFourierT_lin _ _ (intlow G hG) (intlow H hH),
      c09_aux_invFourierT_lin _ _ (inthigh G hG) (inthigh H hH)]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring

-- Encoding: "ε₀, δ, B̄ as in thm:fixed_point_approximation" is encoded as in chapter 02:
-- there is ε₀ > 0 (the linear threshold, ≤ ε_c of lem:linear_conjugation) such that the
-- conclusion holds for every δ > 0 (B̄ = Bbar p δ); combined with thm:fixed_point_approximation by
-- taking the minimum of the ε₀'s.
/-- Blueprint: lem:linear_inverse_assembly (= the conclusion of thm:fixed_point_linear_inverse,
the shared predicate `fixed_point_linear_inverse_statement`): (1) `ℓ` bounded on `Y_γ`; (2) `𝒯₀`
linear and bounded `Ỹ_γ → X_γ` with `ℒ₀ 𝒯₀ G = G`; (3) `𝒰_ε, 𝒱_ε` bijections with uniform bounds
and `ℒ_ε = 𝒱_ε ℒ₀ 𝒰_ε`; (4) `‖(𝒱_ε⁻¹ - I) G_μ‖_{Y_γ} ≤ C_G(γ) ε`. -/
theorem linear_inverse_assembly (P : parameters) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ : ℝ, 0 < δ → fixed_point_linear_inverse_statement P δ ε₀ := by
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  obtain ⟨εc, hεc, hconj⟩ := c09_ext_linear_conjugation P.p hp hp1
  have hγ₁ : P.admissible P.γ₁ := ⟨P.hγ₁, by linarith [P.hγ₁₂, P.hγ₂]⟩
  refine ⟨εc, hεc, fun δ hδ => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1)
    intro γ hγ
    obtain ⟨C, hC, h, -⟩ := c09_ext_linear_ell_continuity P.p γ hp hp1 hγ.1
    exact ⟨C, hC, h⟩
  · -- (2)
    intro γ hγ
    obtain ⟨hγa, -⟩ := c09_aux_admissible_range P.p γ hp hp1 hγ
    obtain ⟨C, hC, hT, hlin, -⟩ := c09_T0_bounded P.p hp hp1 γ hγ
    refine ⟨C, hC, fun G hG => ?_, hlin⟩
    obtain ⟨-, -, -, hF, hn⟩ := hT G hG
    obtain ⟨hX, -⟩ := hT G hG
    have hX' : T_0 P.p G ∈ X_gamma P.p γ := by
      rw [(hT G hG).2.2.1]; exact hX
    exact ⟨hX', hF, hn, c09_ext_T0_right_inverse P.p γ hp hp1 hγa G hG.1 _ hX' hF⟩
  · -- (3) bijections
    intro ε hε
    obtain ⟨C, -, h⟩ := hconj P.γ₁ hγ₁
    obtain ⟨⟨h1, h2, h3, h4, -⟩, -⟩ := h ε hε.1 hε.2
    exact ⟨h1, h2, h3, h4⟩
  · -- (3) bounds and conjugation identity
    intro γ hγ
    obtain ⟨C, hC, h⟩ := hconj γ hγ
    refine ⟨C, hC, fun ε hε => ?_⟩
    obtain ⟨⟨-, -, -, -, hU, hV, hUi, hVi, hUn, hVn⟩, hid, -⟩ := h ε hε.1 hε.2
    refine ⟨fun r hr => ⟨hU.mapsTo hr, (hUn r hr).1, hUi hr, (hUn r hr).2⟩,
      fun G hG => ⟨hV.mapsTo hG, (hVn G hG).1, hVi hG, (hVn G hG).2⟩,
      fun r hr y => (hid r hr y).symm⟩
  · -- (4)
    intro γ hγ
    obtain ⟨C, hC, h⟩ := hconj γ hγ
    refine ⟨max (C * δ / ‖mu_star P.p‖) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun ε hε μ hμ => ?_⟩
    obtain ⟨-, -, h5⟩ := h ε hε.1 hε.2
    calc yNorm P.p γ (V_eps_inv P.p ε (G_mu P.p μ) - G_mu P.p μ)
        ≤ C * ε * δ / ‖mu_star P.p‖ := (h5 δ hδ μ hμ).2
      _ = (C * δ / ‖mu_star P.p‖) * ε := by ring
      _ ≤ max (C * δ / ‖mu_star P.p‖) 1 * ε :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hε.1

end GSQG
