import GSQG.Definitions
import GSQG.Sec4_Analysis.Equation
import GSQG.AppendixAB.Statements
import GSQG.Sec5_ApproximateSolution.FamilyAndE1toE4
import GSQG.Sec5_ApproximateSolution.ResidualBounds
import GSQG.Sec6_LinearInverse.ConjugationAndLowFrequency

/-!
# §7: Nonlinear estimates (blueprint ch. 10)

Statements and proofs for blueprint chapter 10 (`blueprint/src/chapters/10_nonlinear.tex`):
the decomposition `𝒩_{ε,f̄} = 𝒩₁ + 𝒩₂ + 𝒩₃ - ℛ_ε`, admissible profiles, the Lipschitz bounds
N1–N3, continuity in the profile and the assembly `nonlinear_assembly`
(= conclusion of thm:fixed_point_nonlinear_estimates).

The kernel function `Γ_ε` and the operator `ℐ_ε` of chapter 03 (def:c03_Gamma_eps,
def:c03_I_eps) are not in `GSQG/Definitions`; they are re-declared here (same formulas) as helpers of
def:c10_N_pieces: `c10_N_pieces_Gamma`, `c10_N_pieces_I`, with partial derivatives
`c10_N_pieces_Gamma_d1`, `_d2`, `_d11`, `_d12`, `_d22`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal

noncomputable section

namespace GSQG

/-! ### Elementary helpers (weights, `Y_γ`/`X_γ` algebra) -/

/-- Helper: `⟨y⟩ > 0`. -/
theorem c10_aux_jb_pos (y : ℝ) : 0 < jb y := by
  unfold jb; positivity

/-- Helper: `⟨y⟩ ≥ 1`. -/
theorem c10_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := by
  unfold jb; rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg y]

/-- Helper: elementary consequences of `3/4 < p < 1` and admissibility of `γ`
(eq:c10_parameter_facts). -/
theorem c10_aux_gamma_facts (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : admissibleGamma p γ) :
    0 < p ∧ 1 / p < γ ∧ 1 < γ ∧ 1 + 1 / p < γ ∧ γ ≤ p + 2 := by
  obtain ⟨h1, h2⟩ := hγ
  have hp0 : 0 < p := by linarith
  have hb : 1 < beta p := by
    unfold beta; rw [lt_div_iff₀ (by linarith)]; linarith
  have hip : 1 < 1 / p := by rw [lt_div_iff₀ hp0]; linarith
  refine ⟨hp0, by linarith, by linarith, by linarith, by linarith⟩

/-- Helper (Rademacher on `ℝ`): a locally Lipschitz function is differentiable a.e. -/
theorem c10_aux_ae_differentiableAt {f : ℝ → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  have h : ∀ n : ℕ, ∀ᵐ x, x ∈ Ioo (-(n:ℝ)) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨K, hK⟩ :=
      (hf.locallyLipschitzOn (s := Icc (-(n:ℝ)) n)).exists_lipschitzOnWith_of_compact isCompact_Icc
    have h2 := (hK.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem (μ := volume)
    filter_upwards [h2] with x hx hxs
    exact (hx hxs).differentiableAt (isOpen_Ioo.mem_nhds hxs)
  filter_upwards [ae_all_iff.2 h] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  exact hx n ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- Helper: subadditivity of `essSup ∘ ofReal` under an a.e. pointwise bound. -/
theorem c10_aux_essSup_ofReal_le (μ : Measure ℝ) (a b c : ℝ → ℝ) (hb : ∀ y, 0 ≤ b y)
    (hc : ∀ y, 0 ≤ c y) (h : ∀ᵐ y ∂μ, a y ≤ b y + c y) :
    essSup (fun y => ENNReal.ofReal (a y)) μ ≤
      essSup (fun y => ENNReal.ofReal (b y)) μ + essSup (fun y => ENNReal.ofReal (c y)) μ := by
  refine le_trans (essSup_mono_ae ?_) (ENNReal.essSup_add_le _ _)
  filter_upwards [h] with y hy
  simp only [Pi.add_apply]
  rw [← ENNReal.ofReal_add (hb y) (hc y)]
  exact ENNReal.ofReal_le_ofReal hy

/-- Helper: the `Y_γ` norm is subadditive under a.e. pointwise bounds on values and derivatives. -/
theorem c10_aux_Y_norm_le (p γ : ℝ) (F G H : ℝ → ℝ)
    (hd : ∀ᵐ y, ‖H y‖ ≤ ‖F y‖ + ‖G y‖ ∧ ‖deriv H y‖ ≤ ‖deriv F y‖ + ‖deriv G y‖) :
    Y_gamma_norm p γ H ≤ Y_gamma_norm p γ F + Y_gamma_norm p γ G := by
  unfold Y_gamma_norm
  have key : ∀ (w : ℝ → ℝ), (∀ y, 0 ≤ w y) → ∀ y,
      ‖H y‖ ≤ ‖F y‖ + ‖G y‖ ∧ ‖deriv H y‖ ≤ ‖deriv F y‖ + ‖deriv G y‖ →
      jb y ^ γ * (‖H y‖ + w y * ‖deriv H y‖) ≤
        jb y ^ γ * (‖F y‖ + w y * ‖deriv F y‖) + jb y ^ γ * (‖G y‖ + w y * ‖deriv G y‖) := by
    intro w hw y hy
    have hj : 0 ≤ jb y ^ γ := Real.rpow_nonneg (c10_aux_jb_pos y).le _
    have hwy := hw y
    have h1 : ‖H y‖ + w y * ‖deriv H y‖ ≤
        (‖F y‖ + w y * ‖deriv F y‖) + (‖G y‖ + w y * ‖deriv G y‖) := by
      nlinarith [hy.1, hy.2]
    nlinarith
  have hw1 : ∀ y, 0 ≤ jb y ^ (-1 / p) := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
  have hw2 : ∀ y, 0 ≤ jb y := fun y => (c10_aux_jb_pos y).le
  have hj : ∀ y, 0 ≤ jb y ^ γ := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
  have h1 := c10_aux_essSup_ofReal_le (volume.restrict (Ici 0))
    (fun y => jb y ^ γ * (‖H y‖ + jb y ^ (-1 / p) * ‖deriv H y‖))
    (fun y => jb y ^ γ * (‖F y‖ + jb y ^ (-1 / p) * ‖deriv F y‖))
    (fun y => jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖))
    (fun y => mul_nonneg (hj y) (by have := hw1 y; positivity))
    (fun y => mul_nonneg (hj y) (by have := hw1 y; positivity))
    (ae_restrict_of_ae (hd.mono fun y hy => key _ hw1 y hy))
  have h2 := c10_aux_essSup_ofReal_le (volume.restrict (Iic 0))
    (fun y => jb y ^ γ * (‖H y‖ + jb y * ‖deriv H y‖))
    (fun y => jb y ^ γ * (‖F y‖ + jb y * ‖deriv F y‖))
    (fun y => jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖))
    (fun y => mul_nonneg (hj y) (by have := hw2 y; positivity))
    (fun y => mul_nonneg (hj y) (by have := hw2 y; positivity))
    (ae_restrict_of_ae (hd.mono fun y hy => key _ hw2 y hy))
  calc _ ≤ _ := add_le_add h1 h2
    _ = _ := add_add_add_comm _ _ _ _

/-- Helper: `Y_γ` is closed under addition and `‖F + G‖_{Y_γ} ≤ ‖F‖_{Y_γ} + ‖G‖_{Y_γ}`. -/
theorem c10_aux_Y_add (p γ : ℝ) {F G : ℝ → ℝ} (hF : F ∈ Y_gamma p γ) (hG : G ∈ Y_gamma p γ) :
    F + G ∈ Y_gamma p γ ∧ yNorm p γ (F + G) ≤ yNorm p γ F + yNorm p γ G := by
  have hd : ∀ᵐ y, ‖(F + G) y‖ ≤ ‖F y‖ + ‖G y‖ ∧
      ‖deriv (F + G) y‖ ≤ ‖deriv F y‖ + ‖deriv G y‖ := by
    filter_upwards [c10_aux_ae_differentiableAt hF.1, c10_aux_ae_differentiableAt hG.1] with y h1 h2
    rw [deriv_add h1 h2]
    exact ⟨norm_add_le _ _, norm_add_le _ _⟩
  have hle := c10_aux_Y_norm_le p γ F G (F + G) hd
  have hfin : Y_gamma_norm p γ (F + G) < ⊤ :=
    lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨hF.2, hG.2⟩)
  refine ⟨⟨hF.1.add hG.1, hfin⟩, ?_⟩
  unfold yNorm
  rw [← ENNReal.toReal_add hF.2.ne hG.2.ne]
  exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hF.2, hG.2⟩).ne hle

/-- Helper: `‖-F‖_{Y_γ} = ‖F‖_{Y_γ}`, and `Y_γ` is closed under negation. -/
theorem c10_aux_Y_neg (p γ : ℝ) {F : ℝ → ℝ} (hF : F ∈ Y_gamma p γ) :
    -F ∈ Y_gamma p γ ∧ yNorm p γ (-F) = yNorm p γ F := by
  have hn : Y_gamma_norm p γ (-F) = Y_gamma_norm p γ F := by
    unfold Y_gamma_norm
    have : deriv (-F) = -deriv F := by
      funext y; exact deriv.neg
    simp [this]
  exact ⟨⟨hF.1.neg, hn ▸ hF.2⟩, by unfold yNorm; rw [hn]⟩

/-- Helper: `⟨·⟩` is continuous. -/
theorem c10_aux_jb_continuous : Continuous jb := by
  unfold jb; fun_prop

/-- Helper: a continuous bound holding a.e. on an open set holds on its closure. -/
theorem c10_aux_closure_of_ae (φ : ℝ → ℝ) (hφ : Continuous φ) (B : ℝ) (s : Set ℝ) (hs : IsOpen s)
    (h : ∀ᵐ y, y ∈ s → φ y ≤ B) : ∀ y ∈ closure s, φ y ≤ B := by
  have hE : IsClosed {y | φ y ≤ B} := isClosed_le hφ continuous_const
  have hU : IsOpen (s ∩ {y | φ y ≤ B}ᶜ) := hs.inter hE.isOpen_compl
  have h0 : volume (s ∩ {y | φ y ≤ B}ᶜ) = 0 := by
    rw [ae_iff] at h
    refine le_antisymm (le_trans (measure_mono ?_) h.le) (by positivity)
    intro y ⟨hy1, hy2⟩; exact fun h' => hy2 (h' hy1)
  have hempty := (hU.measure_eq_zero_iff volume).1 h0
  have hsub : s ⊆ {y | φ y ≤ B} := by
    intro y hy; by_contra hc
    have : y ∈ s ∩ {y | φ y ≤ B}ᶜ := ⟨hy, hc⟩
    rw [hempty] at this; exact this
  intro y hy
  exact (closure_minimal hsub hE) hy

/-- Helper: the pointwise content of `‖h‖_{X_γ}` (values and first derivatives everywhere, by
continuity; second derivatives a.e.). -/
theorem c10_aux_X_bounds (p γ : ℝ) {h : ℝ → ℝ} (hh : h ∈ X_gamma p γ) :
    (∀ y : ℝ, 0 ≤ y → jb y ^ γ * (|h y| + jb y ^ (-1 / p) * |deriv h y|) ≤ xNorm p γ h) ∧
    (∀ y : ℝ, y ≤ 0 → jb y ^ γ * (|h y| + jb y * |deriv h y|) ≤ xNorm p γ h) ∧
    (∀ᵐ y, 0 ≤ y → jb y ^ γ * (jb y ^ (-2 / p) * |deriv (deriv h) y|) ≤ xNorm p γ h) ∧
    (∀ᵐ y, y ≤ 0 → jb y ^ γ * (jb y ^ (2 : ℕ) * |deriv (deriv h) y|) ≤ xNorm p γ h) := by
  obtain ⟨hW, hfin⟩ := hh
  have hfin' := hfin
  unfold X_gamma_norm at hfin
  set f1 := fun y => ENNReal.ofReal (jb y ^ γ * (‖h y‖ + jb y ^ (-1 / p) * ‖deriv h y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv h) y‖)) with hf1
  set f2 := fun y => ENNReal.ofReal (jb y ^ γ * (‖h y‖ + jb y * ‖deriv h y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv h) y‖)) with hf2
  have hB1 : essSup f1 (volume.restrict (Ici 0)) ≠ ⊤ := (ENNReal.add_lt_top.1 hfin).1.ne
  have hB2 : essSup f2 (volume.restrict (Iic 0)) ≠ ⊤ := (ENNReal.add_lt_top.1 hfin).2.ne
  have hxn : xNorm p γ h = (essSup f1 (volume.restrict (Ici 0))).toReal +
      (essSup f2 (volume.restrict (Iic 0))).toReal := by
    unfold xNorm X_gamma_norm; rw [ENNReal.toReal_add hB1 hB2]
  have hb1 : 0 ≤ (essSup f1 (volume.restrict (Ici 0))).toReal := ENNReal.toReal_nonneg
  have hb2 : 0 ≤ (essSup f2 (volume.restrict (Iic 0))).toReal := ENNReal.toReal_nonneg
  have h1 : ∀ᵐ y, y ∈ Ici (0:ℝ) → f1 y ≤ essSup f1 (volume.restrict (Ici 0)) :=
    (ae_restrict_iff' measurableSet_Ici).1 (ENNReal.ae_le_essSup f1)
  have h2 : ∀ᵐ y, y ∈ Iic (0:ℝ) → f2 y ≤ essSup f2 (volume.restrict (Iic 0)) :=
    (ae_restrict_iff' measurableSet_Iic).1 (ENNReal.ae_le_essSup f2)
  have h1' : ∀ᵐ y, 0 ≤ y → jb y ^ γ * (|h y| + jb y ^ (-1 / p) * |deriv h y| +
      jb y ^ (-2 / p) * |deriv (deriv h) y|) ≤ xNorm p γ h := by
    filter_upwards [h1] with y hy hy0
    have := hy hy0
    rw [hf1, ENNReal.ofReal_le_iff_le_toReal hB1] at this
    simp only [Real.norm_eq_abs] at this
    linarith
  have h2' : ∀ᵐ y, y ≤ 0 → jb y ^ γ * (|h y| + jb y * |deriv h y| +
      jb y ^ (2 : ℕ) * |deriv (deriv h) y|) ≤ xNorm p γ h := by
    filter_upwards [h2] with y hy hy0
    have := hy hy0
    rw [hf2, ENNReal.ofReal_le_iff_le_toReal hB2] at this
    simp only [Real.norm_eq_abs] at this
    linarith
  have hc : Continuous h := hW.1.continuous
  have hc' : Continuous (deriv h) := hW.2.continuous
  have hjγ : Continuous fun y => jb y ^ γ :=
    c10_aux_jb_continuous.rpow_const fun y => Or.inl (c10_aux_jb_pos y).ne'
  have hj1 : Continuous fun y => jb y ^ (-1 / p) :=
    c10_aux_jb_continuous.rpow_const fun y => Or.inl (c10_aux_jb_pos y).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    have key := c10_aux_closure_of_ae
      (fun y => jb y ^ γ * (|h y| + jb y ^ (-1 / p) * |deriv h y|))
      (hjγ.mul ((continuous_abs.comp hc).add (hj1.mul (continuous_abs.comp hc'))))
      (xNorm p γ h) (Ioi 0) isOpen_Ioi (by
        filter_upwards [h1'] with x hx hx0
        have := hx (le_of_lt hx0)
        have : 0 ≤ jb x ^ γ * (jb x ^ (-2 / p) * |deriv (deriv h) x|) := by
          have := c10_aux_jb_pos x; positivity
        nlinarith)
    exact key y (by rw [closure_Ioi]; exact hy)
  · intro y hy
    have key := c10_aux_closure_of_ae
      (fun y => jb y ^ γ * (|h y| + jb y * |deriv h y|))
      (hjγ.mul ((continuous_abs.comp hc).add (c10_aux_jb_continuous.mul (continuous_abs.comp hc'))))
      (xNorm p γ h) (Iio 0) isOpen_Iio (by
        filter_upwards [h2'] with x hx hx0
        have := hx (le_of_lt hx0)
        have : 0 ≤ jb x ^ γ * (jb x ^ (2 : ℕ) * |deriv (deriv h) x|) := by
          have := c10_aux_jb_pos x; positivity
        nlinarith)
    exact key y (by rw [closure_Iio]; exact hy)
  · filter_upwards [h1'] with y hy hy0
    have := hy hy0
    have : 0 ≤ jb y ^ γ * (|h y| + jb y ^ (-1 / p) * |deriv h y|) := by
      have := c10_aux_jb_pos y; positivity
    nlinarith
  · filter_upwards [h2'] with y hy hy0
    have := hy hy0
    have : 0 ≤ jb y ^ γ * (|h y| + jb y * |deriv h y|) := by
      have := c10_aux_jb_pos y; positivity
    nlinarith

/-- Helper: `x^a (x^b c) ≤ X → c ≤ X x^{-a-b}` for `x > 0`. -/
theorem c10_aux_rpow_div {x a b c X : ℝ} (hx : 0 < x) (h : x ^ a * (x ^ b * c) ≤ X) :
    c ≤ X * x ^ (-a - b) := by
  have e : c = x ^ (-a - b) * (x ^ a * (x ^ b * c)) := by
    rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hx, ← Real.rpow_add hx,
      show -a - b + a + b = 0 by ring, Real.rpow_zero, one_mul]
  rw [e, mul_comm X]
  exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le _)

/-- Helper: pointwise bounds for `h ∈ X_γ` in terms of `‖h‖_{X_γ}`
(lem:c10_profile_consequences, item 4, first part). -/
theorem c10_aux_X_simple (p γ : ℝ) {h : ℝ → ℝ} (hh : h ∈ X_gamma p γ) :
    (∀ y, |h y| ≤ xNorm p γ h * jb y ^ (-γ)) ∧
    (∀ y : ℝ, 0 ≤ y → |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ + 1 / p)) ∧
    (∀ y : ℝ, y ≤ 0 → |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ - 1)) ∧
    (∀ᵐ y, 0 ≤ y → |deriv (deriv h) y| ≤ xNorm p γ h * jb y ^ (-γ + 2 / p)) ∧
    (∀ᵐ y, y ≤ 0 → |deriv (deriv h) y| ≤ xNorm p γ h * jb y ^ (-γ - 2)) := by
  obtain ⟨b1, b2, b3, b4⟩ := c10_aux_X_bounds p γ hh
  have hj := c10_aux_jb_pos
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩
  · have hjy := hj y
    have hu : jb y ^ γ * (jb y ^ (0:ℝ) * |h y|) ≤ xNorm p γ h := by
      rcases le_total 0 y with hy | hy
      · have := b1 y hy
        have : 0 ≤ jb y ^ γ * (jb y ^ (-1 / p) * |deriv h y|) := by positivity
        rw [Real.rpow_zero, one_mul]; nlinarith
      · have := b2 y hy
        have : 0 ≤ jb y ^ γ * (jb y * |deriv h y|) := by positivity
        rw [Real.rpow_zero, one_mul]; nlinarith
    have := c10_aux_rpow_div hjy hu
    simpa using this
  · have hjy := hj y
    have := b1 y hy
    have hu : jb y ^ γ * (jb y ^ (-1 / p) * |deriv h y|) ≤ xNorm p γ h := by
      have : 0 ≤ jb y ^ γ * |h y| := by positivity
      nlinarith
    have := c10_aux_rpow_div hjy hu
    convert this using 3; ring
  · have hjy := hj y
    have := b2 y hy
    have hu : jb y ^ γ * (jb y ^ (1:ℝ) * |deriv h y|) ≤ xNorm p γ h := by
      have : 0 ≤ jb y ^ γ * |h y| := by positivity
      rw [Real.rpow_one]; nlinarith
    have := c10_aux_rpow_div hjy hu
    convert this using 3
  · filter_upwards [b3] with y hy hy0
    have := c10_aux_rpow_div (hj y) (hy hy0)
    convert this using 3; ring
  · filter_upwards [b4] with y hy hy0
    have hu := hy hy0
    rw [show jb y ^ (2 : ℕ) = jb y ^ (2 : ℝ) by rw [Real.rpow_two]] at hu
    have := c10_aux_rpow_div (hj y) hu
    convert this using 3

/-- Helper: `⟨y⟩^{-γ} ∈ L¹` for `γ > 1`. -/
theorem c10_aux_jb_integrable {γ : ℝ} (hγ : 1 < γ) : Integrable (fun z : ℝ => jb z ^ (-γ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := γ)
    (by simpa using hγ)
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [jb, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1; ring

/-- Helper: `⟨y⟩ ≤ 4` for `|y| ≤ 3`. -/
theorem c10_aux_jb_le_four {y : ℝ} (hy : |y| ≤ 3) : jb y ≤ 4 := by
  unfold jb
  rw [Real.sqrt_le_left (by norm_num)]
  have := sq_abs y; have := abs_nonneg y; nlinarith

/-- Helper: `⟨y⟩^e ≤ 1` for `e ≤ 0`. -/
theorem c10_aux_jb_rpow_le_one (y : ℝ) {e : ℝ} (he : e ≤ 0) : jb y ^ e ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (c10_aux_one_le_jb y) he

/-- Helper: monotonicity of `e ↦ ⟨y⟩^e`. -/
theorem c10_aux_jb_rpow_mono (y : ℝ) {a b : ℝ} (hab : a ≤ b) : jb y ^ a ≤ jb y ^ b :=
  Real.rpow_le_rpow_of_exponent_le (c10_aux_one_le_jb y) hab

/-- Helper: elements of `X_γ` (`γ ≥ 1/p`, `γ ≥ 0`) have bounded derivative (everywhere, by
continuity of `r'`). -/
theorem c10_aux_X_deriv_bdd (p γ : ℝ) (hγ : 1 / p ≤ γ) (hγ0 : 0 ≤ γ) {r : ℝ → ℝ}
    (hr : r ∈ X_gamma p γ) : ∃ K, ∀ y, |deriv r y| ≤ K := by
  obtain ⟨hW, hfin⟩ := hr
  unfold X_gamma_norm at hfin
  set f1 := fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ +
      jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)) with hf1
  set f2 := fun y => ENNReal.ofReal (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ +
      jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖)) with hf2
  have hB1 : essSup f1 (volume.restrict (Ici 0)) ≠ ⊤ := (ENNReal.add_lt_top.1 hfin).1.ne
  have hB2 : essSup f2 (volume.restrict (Iic 0)) ≠ ⊤ := (ENNReal.add_lt_top.1 hfin).2.ne
  set K := max (essSup f1 (volume.restrict (Ici 0))).toReal
    (essSup f2 (volume.restrict (Iic 0))).toReal
  have h1 : ∀ᵐ y, y ∈ Ici (0:ℝ) → f1 y ≤ essSup f1 (volume.restrict (Ici 0)) :=
    (ae_restrict_iff' measurableSet_Ici).1 (ENNReal.ae_le_essSup f1)
  have h2 : ∀ᵐ y, y ∈ Iic (0:ℝ) → f2 y ≤ essSup f2 (volume.restrict (Iic 0)) :=
    (ae_restrict_iff' measurableSet_Iic).1 (ENNReal.ae_le_essSup f2)
  have hae : ∀ᵐ y, |deriv r y| ≤ K := by
    filter_upwards [h1, h2] with y hy1 hy2
    have hj := c10_aux_jb_pos y
    have hj1 := c10_aux_one_le_jb y
    rcases le_total 0 y with hy | hy
    · have := hy1 hy
      rw [hf1, ENNReal.ofReal_le_iff_le_toReal hB1] at this
      have hw : 1 ≤ jb y ^ γ * jb y ^ (-1 / p) := by
        rw [← Real.rpow_add hj]; exact Real.one_le_rpow hj1 (by rw [neg_div]; linarith)
      have a1 : 0 ≤ jb y ^ γ := by positivity
      have a2 : 0 ≤ jb y ^ (-2 / p) * ‖deriv (deriv r) y‖ := by positivity
      have a3 : 0 ≤ jb y ^ (-1 / p) := by positivity
      have : |deriv r y| ≤ (essSup f1 (volume.restrict (Ici 0))).toReal := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
        nlinarith [abs_nonneg (r y), abs_nonneg (deriv r y)]
      exact this.trans (le_max_left _ _)
    · have := hy2 hy
      rw [hf2, ENNReal.ofReal_le_iff_le_toReal hB2] at this
      have hw : 1 ≤ jb y ^ γ * jb y := by
        nlinarith [Real.one_le_rpow hj1 hγ0]
      have a1 : 0 ≤ jb y ^ γ := by positivity
      have a2 : 0 ≤ jb y ^ (2:ℕ) * ‖deriv (deriv r) y‖ := by positivity
      have : |deriv r y| ≤ (essSup f2 (volume.restrict (Iic 0))).toReal := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
        nlinarith [abs_nonneg (r y), abs_nonneg (deriv r y)]
      exact this.trans (le_max_right _ _)
  refine ⟨K, fun y => ?_⟩
  have hc : Continuous (deriv r) := hW.2.continuous
  have hcl : IsClosed {y | |deriv r y| ≤ K} :=
    isClosed_le (continuous_abs.comp hc) continuous_const
  have hd : Dense {y | |deriv r y| ≤ K} := Measure.dense_of_ae hae
  have : {y | |deriv r y| ≤ K} = univ := by rw [← hd.closure_eq, hcl.closure_eq]
  exact (this.symm ▸ mem_univ y : y ∈ {y | |deriv r y| ≤ K})

/-- Helper: for admissible `γ`, `X_γ ⊆ 𝒜` (the class of def:c01_admissible_class). -/
theorem c10_aux_X_admissible_class (p γ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) {r : ℝ → ℝ} (hr : r ∈ X_gamma p γ) : r ∈ c01_admissible_class := by
  obtain ⟨hp0, h1, h2, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  exact ⟨hr.1.1, c10_aux_X_deriv_bdd p γ h1.le (by linarith) hr, hr.1.2⟩

/-- Helper: a `C²` function with bounded derivative is in `𝒜`. -/
theorem c10_aux_C2_admissible_class {fbar : ℝ → ℝ} (h2 : ContDiff ℝ 2 fbar)
    (hb : ∃ K : ℝ, ∀ y, |deriv fbar y| ≤ K) : fbar ∈ c01_admissible_class := by
  refine ⟨h2.of_le (by norm_num), hb, ?_⟩
  have : ContDiff ℝ 1 (deriv fbar) := ((contDiff_succ_iff_deriv (n := 1)).1 h2).2.2
  exact this.locallyLipschitz

/-- Helper: `X_γ` is closed under subtraction. -/
theorem c10_aux_X_sub (p γ : ℝ) {r₁ r₂ : ℝ → ℝ} (h₁ : r₁ ∈ X_gamma p γ) (h₂ : r₂ ∈ X_gamma p γ) :
    r₁ - r₂ ∈ X_gamma p γ := by
  have hd1 : Differentiable ℝ r₁ := h₁.1.1.differentiable (by norm_num)
  have hd2 : Differentiable ℝ r₂ := h₂.1.1.differentiable (by norm_num)
  have hD : deriv (r₁ - r₂) = deriv r₁ - deriv r₂ := funext fun y => deriv_sub (hd1 y) (hd2 y)
  have hDD : ∀ᵐ y, deriv (deriv (r₁ - r₂)) y = deriv (deriv r₁) y - deriv (deriv r₂) y := by
    filter_upwards [c10_aux_ae_differentiableAt h₁.1.2, c10_aux_ae_differentiableAt h₂.1.2]
      with y a1 a2
    rw [hD]; exact deriv_sub a1 a2
  refine ⟨⟨h₁.1.1.sub h₂.1.1, hD ▸ h₁.1.2.sub h₂.1.2⟩, ?_⟩
  have hle : X_gamma_norm p γ (r₁ - r₂) ≤ X_gamma_norm p γ r₁ + X_gamma_norm p γ r₂ := by
    unfold X_gamma_norm
    have hj : ∀ y, 0 ≤ jb y ^ γ := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
    have key : ∀ (w₁ w₂ : ℝ → ℝ), (∀ y, 0 ≤ w₁ y) → (∀ y, 0 ≤ w₂ y) →
        ∀ᵐ y, jb y ^ γ * (‖(r₁ - r₂) y‖ + w₁ y * ‖deriv (r₁ - r₂) y‖ +
            w₂ y * ‖deriv (deriv (r₁ - r₂)) y‖) ≤
          jb y ^ γ * (‖r₁ y‖ + w₁ y * ‖deriv r₁ y‖ + w₂ y * ‖deriv (deriv r₁) y‖) +
          jb y ^ γ * (‖r₂ y‖ + w₁ y * ‖deriv r₂ y‖ + w₂ y * ‖deriv (deriv r₂) y‖) := by
      intro w₁ w₂ hw₁ hw₂
      filter_upwards [hDD] with y hy
      rw [hy, hD]
      simp only [Pi.sub_apply]
      have e1 := norm_sub_le (r₁ y) (r₂ y)
      have e2 := norm_sub_le (deriv r₁ y) (deriv r₂ y)
      have e3 := norm_sub_le (deriv (deriv r₁) y) (deriv (deriv r₂) y)
      have := hj y; have := hw₁ y; have := hw₂ y
      have : ‖r₁ y - r₂ y‖ + w₁ y * ‖deriv r₁ y - deriv r₂ y‖ +
          w₂ y * ‖deriv (deriv r₁) y - deriv (deriv r₂) y‖ ≤
          (‖r₁ y‖ + w₁ y * ‖deriv r₁ y‖ + w₂ y * ‖deriv (deriv r₁) y‖) +
          (‖r₂ y‖ + w₁ y * ‖deriv r₂ y‖ + w₂ y * ‖deriv (deriv r₂) y‖) := by
        nlinarith
      nlinarith
    have hw1 : ∀ y, 0 ≤ jb y ^ (-1 / p) := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
    have hw2 : ∀ y, 0 ≤ jb y ^ (-2 / p) := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
    have hw3 : ∀ y, 0 ≤ jb y := fun y => (c10_aux_jb_pos y).le
    have hw4 : ∀ y, 0 ≤ jb y ^ (2 : ℕ) := fun y => by positivity
    have h1 := c10_aux_essSup_ofReal_le (volume.restrict (Ici 0)) _ _ _
      (fun y => mul_nonneg (hj y) (by have := hw1 y; have := hw2 y; positivity))
      (fun y => mul_nonneg (hj y) (by have := hw1 y; have := hw2 y; positivity))
      (ae_restrict_of_ae (key _ _ hw1 hw2))
    have h2 := c10_aux_essSup_ofReal_le (volume.restrict (Iic 0)) _ _ _
      (fun y => mul_nonneg (hj y) (by have := hw3 y; have := hw4 y; positivity))
      (fun y => mul_nonneg (hj y) (by have := hw3 y; have := hw4 y; positivity))
      (ae_restrict_of_ae (key _ _ hw3 hw4))
    calc _ ≤ _ := add_le_add h1 h2
      _ = _ := add_add_add_comm _ _ _ _
  exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨h₁.2, h₂.2⟩)

/-- Helper: `0 ∈ X_γ` with norm `0`. -/
theorem c10_aux_X_zero (p γ : ℝ) : (0 : ℝ → ℝ) ∈ X_gamma p γ ∧ xNorm p γ (0 : ℝ → ℝ) = 0 := by
  have hn : X_gamma_norm p γ (0 : ℝ → ℝ) = 0 := by
    simp [X_gamma_norm]
    exact ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  refine ⟨⟨⟨contDiff_const, ?_⟩, by rw [hn]; exact ENNReal.zero_lt_top⟩, by simp [xNorm, hn]⟩
  have : deriv (0 : ℝ → ℝ) = fun _ => 0 := by funext y; simp
  rw [this]; exact LocallyLipschitz.const _


/-! ### The kernel function `Γ_ε`, the operator `ℐ_ε` and the three pieces -/

/-- Blueprint: def:c10_N_pieces (helper; = def:c03_Gamma_eps, eq:G_epsilon).
`Γ_ε(u,v) = c_α [p ∫_u^v (1 - A_ε(s)/A_ε(u)) ds + (v-u)(1 - A_ε(v)/A_ε(u))]`. -/
abbrev c10_N_pieces_Gamma (p ε u v : ℝ) : ℝ := c03_Gamma_eps p ε u v

/-- Blueprint: def:c10_N_pieces (helper).  `∂₁Γ_ε(u,v)`. -/
def c10_N_pieces_Gamma_d1 (p ε u v : ℝ) : ℝ := deriv (fun u' => c10_N_pieces_Gamma p ε u' v) u

/-- Blueprint: def:c10_N_pieces (helper).  `∂₂Γ_ε(u,v)`. -/
def c10_N_pieces_Gamma_d2 (p ε u v : ℝ) : ℝ := deriv (fun v' => c10_N_pieces_Gamma p ε u v') v

/-- Blueprint: def:c10_N_pieces (helper).  `∂₁₁Γ_ε(u,v)`. -/
def c10_N_pieces_Gamma_d11 (p ε u v : ℝ) : ℝ := deriv (fun u' => c10_N_pieces_Gamma_d1 p ε u' v) u

/-- Blueprint: def:c10_N_pieces (helper).  `∂₁₂Γ_ε(u,v) = ∂₂∂₁Γ_ε(u,v)`. -/
def c10_N_pieces_Gamma_d12 (p ε u v : ℝ) : ℝ := deriv (fun v' => c10_N_pieces_Gamma_d1 p ε u v') v

/-- Blueprint: def:c10_N_pieces (helper).  `∂₂₂Γ_ε(u,v)`. -/
def c10_N_pieces_Gamma_d22 (p ε u v : ℝ) : ℝ := deriv (fun v' => c10_N_pieces_Gamma_d2 p ε u v') v

/-- Blueprint: def:c10_N_pieces (helper; = def:c03_I_eps).
`ℐ_ε(g)(y) = ∫ Γ_ε(g'(y), S_g(y,z)) |y-z|^{-α} dz`. -/
abbrev c10_N_pieces_I (p ε : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := c03_I_eps p ε g y

/-- Blueprint: def:c10_N_pieces.  `𝒩₁(r) = (B_ε(f̄'+r') - B_ε(f̄'))(f̄ - y f̄')`. -/
def c10_N_pieces_N1 (p ε : ℝ) (fbar r : ℝ → ℝ) (y : ℝ) : ℝ :=
  (A_eps_B p ε (deriv fbar y + deriv r y) - A_eps_B p ε (deriv fbar y)) *
    (fbar y - y * deriv fbar y)

/-- Blueprint: def:c10_N_pieces.  `𝒩₂(r) = (B_ε(f̄'+r') - 1)(r - y r')`. -/
def c10_N_pieces_N2 (p ε : ℝ) (fbar r : ℝ → ℝ) (y : ℝ) : ℝ :=
  (A_eps_B p ε (deriv fbar y + deriv r y) - 1) * (r y - y * deriv r y)

/-- Blueprint: def:c10_N_pieces.  `𝒩₃(r) = ℐ_ε(f̄+r) - ℐ_ε(f̄) - b_ε r'`. -/
def c10_N_pieces_N3 (p ε : ℝ) (fbar r : ℝ → ℝ) (y : ℝ) : ℝ :=
  c10_N_pieces_I p ε (fbar + r) y - c10_N_pieces_I p ε fbar y - b_eps p ε y * deriv r y

/-- Blueprint: def:c10_N_pieces.  The three nonlinear pieces `𝒩_j = 𝒩_j^{ε,f̄}(r)`,
indexed by `j : Fin 3` (`0 ↦ 𝒩₁`, `1 ↦ 𝒩₂`, `2 ↦ 𝒩₃`). -/
def c10_N_pieces (p ε : ℝ) (fbar r : ℝ → ℝ) : Fin 3 → ℝ → ℝ :=
  ![c10_N_pieces_N1 p ε fbar r, c10_N_pieces_N2 p ε fbar r, c10_N_pieces_N3 p ε fbar r]

/-! ### The decomposition -/

/-- Blueprint: lem:c10_N_decomposition (helper).  The hypotheses on `f̄` under which the
decomposition applies: `f̄ ∈ C²`, `f̄' ∈ L^∞` (then `f̄'' ∈ L^∞_loc`), and `|D|^p f̄'` is defined
(absolutely convergent) at every point in the sense of def:frac_multiplier. -/
def c10_N_decomposition_hyp (p : ℝ) (fbar : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 fbar ∧ (∃ K : ℝ, ∀ y, |deriv fbar y| ≤ K) ∧
    ∀ y, Integrable (fun z => (deriv fbar y - deriv fbar z) / |y - z| ^ (p + 1))

-- Encoding: (a) `ε₀` (that of lem:linear_conjugation) is independent of `γ`, so `∃ ε₀` precedes
-- `∀ γ`, as needed in lem:c10_N_admissible_bounds; (b) the identity holds for every `y`, which
-- determines `deriv` and hence the `Y_γ` norm.
/-- Blueprint: lem:c10_N_decomposition.  For `0 ≤ ε ≤ min(1, ε₀)` (`ε₀` of lem:linear_conjugation),
`ℰ_ε(f̄+r)`, `ℰ_ε(f̄)` are defined (the integrals in `|D|^p ∂_y` and `𝒥̃_ε` converge absolutely) and
`𝒩_{ε,f̄}(r) = 𝒩₁(r) + 𝒩₂(r) + 𝒩₃(r) - ℛ_ε r` (pointwise); moreover `𝒩_{ε,f̄}(0) = 0`. -/
theorem c10_N_decomposition (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ ε₀ > 0, ∀ γ : ℝ, admissibleGamma p γ → ∀ ε : ℝ, 0 ≤ ε → ε ≤ min 1 ε₀ →
      ∀ fbar : ℝ → ℝ, c10_N_decomposition_hyp p fbar →
      ∀ r ∈ X_gamma p γ,
        (∀ g ∈ ({fbar, fbar + r} : Set (ℝ → ℝ)), ∀ y,
          Integrable (fun z => (deriv g y - deriv g z) / |y - z| ^ (p + 1)) ∧
          Integrable (fun z => (deriv g y - deriv g z) / |y - z| ^ (p + 1) *
            (A_eps p ε (c01_secant g y z) - A_eps p ε (deriv g y)))) ∧
        (∀ y, N_eps p ε fbar r y =
          c10_N_pieces_N1 p ε fbar r y + c10_N_pieces_N2 p ε fbar r y +
            c10_N_pieces_N3 p ε fbar r y - R_eps p ε r y) ∧
        (∀ y, N_eps p ε fbar 0 y = 0) := by
  refine ⟨1, one_pos, fun γ hγ ε hε _ fbar hf r hr => ?_⟩
  have hp0 : 0 < p := by linarith
  have hfA : fbar ∈ c01_admissible_class := c10_aux_C2_admissible_class hf.1 hf.2.1
  have hrA : r ∈ c01_admissible_class := c10_aux_X_admissible_class p γ hp hp1 hγ hr
  have hdf : Differentiable ℝ fbar := hfA.1.differentiable (by norm_num)
  have hdr : Differentiable ℝ r := hrA.1.differentiable (by norm_num)
  have hdy : ∀ y, deriv (fbar + r) y = deriv fbar y + deriv r y := fun y =>
    deriv_add (hdf y) (hdr y)
  have hgA : fbar + r ∈ c01_admissible_class := by
    obtain ⟨K1, hK1⟩ := hfA.2.1
    obtain ⟨K2, hK2⟩ := hrA.2.1
    refine ⟨hfA.1.add hrA.1, ⟨K1 + K2, fun y => ?_⟩, ?_⟩
    · rw [hdy]; exact (abs_add_le _ _).trans (add_le_add (hK1 y) (hK2 y))
    · have : deriv (fbar + r) = deriv fbar + deriv r := funext hdy
      rw [this]; exact hfA.2.2.add hrA.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg y
    have hgA' : g ∈ c01_admissible_class := by
      rcases hg with rfl | hg
      · exact hfA
      · rw [mem_singleton_iff] at hg; rw [hg]; exact hgA
    have W := c03_I_well_defined p ε hp0 hp1 hε g hgA'
    exact ⟨W.1 y, W.2.2.1 y⟩
  · intro y
    have k1 := (analysis_semilinear_kernel p ε hp0 hp1 hε _ hgA).2 y
    have k2 := (analysis_semilinear_kernel p ε hp0 hp1 hε _ hfA).2 y
    have i1 := (c03_I_well_defined p ε hp0 hp1 hε _ hfA).1 y
    have i2 := (c03_I_well_defined p ε hp0 hp1 hε _ hrA).1 y
    have hfr : fracDdy p (fbar + r) y = fracDdy p fbar y + fracDdy p r y := by
      unfold fracDdy fracD
      rw [← mul_add, ← integral_add i1 i2]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hdy]; ring
    simp only [N_eps, L_eps, L0, c10_N_pieces_N1, c10_N_pieces_N2, c10_N_pieces_N3,
      c10_N_pieces_I, k1, k2, hfr, hdy, Pi.add_apply]
    ring
  · intro y
    simp [N_eps, L_eps, L0, fracDdy, fracD, R_eps, R_eps_one, R_eps_two]



/-! ### Results of other chapters (wrappers around imported theorems) -/

/-- Wrapper for lem:linear_conjugation, item (2) (chapter 08, `GSQG.linear_conjugation`):
`‖ℛ_ε r‖_{Y_γ} ≤ C ε ‖r‖_{X_γ}` for admissible `γ`, `0 ≤ ε ≤ ε_c`. -/
theorem c10_ext_linear_conjugation_R (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ γ : ℝ, admissibleGamma p γ → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc →
        ∀ r ∈ X_gamma p γ, R_eps p ε r ∈ Y_gamma p γ ∧
          yNorm p γ (R_eps p ε r) ≤ C * ε * xNorm p γ r := by
  obtain ⟨εc, hεc, h⟩ := linear_conjugation p hp hp1
  refine ⟨εc, hεc, fun γ hγ => ?_⟩
  obtain ⟨C, hC, h⟩ := h γ hγ
  exact ⟨C, hC, fun ε hε hε' => (h ε hε hε').2.1⟩

/-- Wrapper for lem:c08_conj_nonlocal (chapter 08, `GSQG.c08_conj_nonlocal`), integrability
part: `z ↦ K_ε(y,z) r'(z)` is integrable for `r ∈ C¹` with bounded, locally Lipschitz `r'`. -/
theorem c10_ext_conj_nonlocal_integrable (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ εc : ℝ, 0 < εc ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ εc → ∀ r : ℝ → ℝ, ContDiff ℝ 1 r →
      (∃ M : ℝ, ∀ y, |deriv r y| ≤ M) → LocallyLipschitz (deriv r) →
      ∀ y : ℝ, Integrable (fun z => R_eps_kernel p ε y z * deriv r z) := by
  obtain ⟨εc, hεc, h⟩ := c08_conj_nonlocal p hp hp1
  exact ⟨εc, hεc, fun ε hε hε' r hr hM hL y => ((h ε hε hε' r hr hM hL).2.2.2 y).2.2.1⟩

/-- Helper: linearity of `ℛ_ε` on `𝒜` (given integrability of `K_ε(y,·) r'`). -/
theorem c10_aux_R_eps_sub (p ε : ℝ)
    (hint : ∀ r ∈ c01_admissible_class, ∀ y,
      Integrable (fun z => R_eps_kernel p ε y z * deriv r z))
    {r₁ r₂ : ℝ → ℝ} (h₁ : r₁ ∈ c01_admissible_class) (h₂ : r₂ ∈ c01_admissible_class) (y : ℝ) :
    R_eps p ε r₁ y - R_eps p ε r₂ y = R_eps p ε (r₁ - r₂) y := by
  have hD : deriv (r₁ - r₂) = fun z => deriv r₁ z - deriv r₂ z := funext fun z =>
    deriv_sub (h₁.1.differentiable (by norm_num) z) (h₂.1.differentiable (by norm_num) z)
  have hI : (∫ z, R_eps_kernel p ε y z * (deriv r₁ z - deriv r₂ z)) =
      (∫ z, R_eps_kernel p ε y z * deriv r₁ z) - ∫ z, R_eps_kernel p ε y z * deriv r₂ z := by
    rw [← integral_sub (hint _ h₁ y) (hint _ h₂ y)]
    congr 1; funext z; ring
  simp only [R_eps, R_eps_one, R_eps_two, hD, Pi.sub_apply, hI]
  ring

/-! ### Admissible profiles and elementary bounds -/

/-- Blueprint: def:nonlinear_admissible_profile.  `f̄ ∈ C²` is admissible with constant `M` if
for `y ≥ 0`: `|f̄| ≤ M⟨y⟩^{-p}`, `|f̄'| ≤ M⟨y⟩^{-β}`, `|f̄''| ≤ M⟨y⟩^{-β+1/p}`, and for `y ≤ 0`:
`|f̄+y| ≤ M⟨y⟩^{-p}`, `|f̄'+1| ≤ M⟨y⟩^{-p-1}`, `|f̄''| ≤ M⟨y⟩^{-p-2}`. -/
def nonlinear_admissible_profile (p M : ℝ) (fbar : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 fbar ∧
  (∀ y : ℝ, 0 ≤ y → |fbar y| ≤ M * jb y ^ (-p) ∧ |deriv fbar y| ≤ M * jb y ^ (-beta p) ∧
      |deriv (deriv fbar) y| ≤ M * jb y ^ (-beta p + 1 / p)) ∧
  (∀ y : ℝ, y ≤ 0 → |fbar y + y| ≤ M * jb y ^ (-p) ∧ |deriv fbar y + 1| ≤ M * jb y ^ (-p - 1) ∧
      |deriv (deriv fbar) y| ≤ M * jb y ^ (-p - 2))

/-- Helper: an admissible profile has bounded derivative. -/
theorem c10_aux_admissible_deriv_bdd (p M : ℝ) (hp : 0 < p)
    {fbar : ℝ → ℝ} (h : nonlinear_admissible_profile p M fbar) :
    ∃ K : ℝ, ∀ y, |deriv fbar y| ≤ K := by
  have hM : 0 ≤ M := by
    have h0 := (h.2.1 0 le_rfl).1
    have : 0 < jb 0 ^ (-p) := Real.rpow_pos_of_pos (c10_aux_jb_pos 0) _
    nlinarith [abs_nonneg (fbar 0)]
  have hβ : 0 ≤ beta p := by unfold beta; positivity
  have hb : ∃ K : ℝ, ∀ y, |deriv fbar y| ≤ K := by
    refine ⟨M + 1, fun y => ?_⟩
    rcases le_total 0 y with hy | hy
    · have h1 := (h.2.1 y hy).2.1
      have : jb y ^ (-beta p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (c10_aux_one_le_jb y) (by linarith)
      nlinarith
    · have h1 := (h.2.2 y hy).2.1
      have : jb y ^ (-p - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (c10_aux_one_le_jb y) (by linarith)
      have h2 : |deriv fbar y + 1| ≤ M := by nlinarith
      have h3 := abs_sub (deriv fbar y + 1) 1
      simp only [add_sub_cancel_right, abs_one] at h3
      linarith
  exact hb

/-- Helper: an admissible profile satisfies the hypotheses of lem:c10_N_decomposition
(`f̄' ∈ L^∞` from the profile bounds; absolute convergence of `|D|^p f̄'` from
lem:c03_I_well_defined). -/
theorem c10_aux_admissible_decomposition_hyp (p M : ℝ) (hp : 0 < p) (hp1 : p < 1)
    {fbar : ℝ → ℝ} (h : nonlinear_admissible_profile p M fbar) : c10_N_decomposition_hyp p fbar := by
  have hb := c10_aux_admissible_deriv_bdd p M hp h
  have hA := c10_aux_C2_admissible_class h.1 hb
  exact ⟨h.1, hb, (c03_I_well_defined p 0 hp hp1 le_rfl fbar hA).1⟩

/-- Blueprint: lem:c10_admissible_closed (helper).  `f_k → f` in `C²_loc(ℝ)`: `f ∈ C²` and
`∂^j f_k → ∂^j f` uniformly on every `[-R,R]`, `j = 0,1,2`. -/
def c10_admissible_closed_C2loc (fk : ℕ → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ j : ℕ, j ≤ 2 → ∀ R : ℝ,
    TendstoUniformlyOn (fun k => iteratedDeriv j (fk k)) (iteratedDeriv j f) atTop (Icc (-R) R)

/-- Blueprint: lem:c10_admissible_closed.  Admissibility with constant `M` is closed under
`C²_loc` limits. -/
theorem c10_admissible_closed (p M : ℝ) (fk : ℕ → ℝ → ℝ) (fbar : ℝ → ℝ)
    (hk : ∀ k, nonlinear_admissible_profile p M (fk k)) (hconv : c10_admissible_closed_C2loc fk fbar) :
    nonlinear_admissible_profile p M fbar := by
  obtain ⟨hC2, hU⟩ := hconv
  have pt : ∀ j ≤ 2, ∀ y, Tendsto (fun k => iteratedDeriv j (fk k) y) atTop
      (nhds (iteratedDeriv j fbar y)) := fun j hj y =>
    (hU j hj |y|).tendsto_at ⟨neg_abs_le y, le_abs_self y⟩
  have e2 : ∀ g : ℝ → ℝ, iteratedDeriv 2 g = deriv (deriv g) := fun g => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have p0 : ∀ y, Tendsto (fun k => fk k y) atTop (nhds (fbar y)) := fun y => by
    simpa using pt 0 (by norm_num) y
  have p1 : ∀ y, Tendsto (fun k => deriv (fk k) y) atTop (nhds (deriv fbar y)) := fun y => by
    simpa using pt 1 (by norm_num) y
  have p2 : ∀ y, Tendsto (fun k => deriv (deriv (fk k)) y) atTop (nhds (deriv (deriv fbar) y)) :=
    fun y => by simpa [e2] using pt 2 le_rfl y
  have lim : ∀ (a : ℕ → ℝ) (b c : ℝ), Tendsto a atTop (nhds b) → (∀ k, |a k| ≤ c) → |b| ≤ c :=
    fun a b c ha hc => le_of_tendsto' ((continuous_abs.tendsto b).comp ha) hc
  refine ⟨hC2, fun y hy => ⟨?_, ?_, ?_⟩, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact lim _ _ _ (p0 y) fun k => ((hk k).2.1 y hy).1
  · exact lim _ _ _ (p1 y) fun k => ((hk k).2.1 y hy).2.1
  · exact lim _ _ _ (p2 y) fun k => ((hk k).2.1 y hy).2.2
  · exact lim _ _ _ ((p0 y).add_const y) fun k => ((hk k).2.2 y hy).1
  · exact lim _ _ _ ((p1 y).add_const 1) fun k => ((hk k).2.2 y hy).2.1
  · exact lim _ _ _ (p2 y) fun k => ((hk k).2.2 y hy).2.2

/-- Wrapper for prop:approx_profile_bounds (chapter 04, `GSQG.approx_profile_bounds`). -/
theorem c10_ext_approx_profile_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ j : ℕ, ∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        (∀ y ≥ (0 : ℝ), |approximate_solution_family p R ε μ y| ≤ C * jb y ^ (-p) ∧
          |iteratedDeriv (j + 1) (approximate_solution_family p R ε μ) y| ≤
            C * jb y ^ (-beta p + j / p)) ∧
        (∀ y ≤ (0 : ℝ),
          |iteratedDeriv j (fun t => approximate_solution_family p R ε μ t + t) y| ≤
            C * jb y ^ (-p - j))) ∧
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀,
        (∀ μ ∈ Bbar p δ, ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family p R ε μ)) ∧
        ∀ (k : ℕ) (K : Set ℝ), IsCompact K → ∀ μ₀ ∈ Bbar p δ,
          TendstoUniformlyOn
            (fun (μ : ℂ) (y : ℝ) => iteratedDeriv k (approximate_solution_family p R ε μ) y)
            (iteratedDeriv k (approximate_solution_family p R ε μ₀)) (nhdsWithin μ₀ (Bbar p δ)) K) :=
  approx_profile_bounds p hp hp1

/-- Helper: `‖μ_*‖ > 0`. -/
theorem c10_aux_mu_star_norm_pos (p : ℝ) (hp : 0 < p) : 0 < ‖mu_star p‖ := by
  unfold mu_star
  rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have : 0 < Real.sqrt (2 * π * p) := Real.sqrt_pos.2 (by positivity)
  rw [abs_of_pos this]; positivity

-- Encoding: "the parameters ε₀, δ of thm:fixed_point_approximation" (and the fixed cutoff
-- scale `R ≥ R₀` of def:approximate_solution_family) are not Lean objects; they are existentially
-- quantified here (any smaller ε₀, δ and any larger R₀ also work, so the statement can be combined
-- with the other chapters by taking minima/maxima).
/-- Blueprint: lem:c10_approx_admissible.  There is `M₀` such that all `f̄_{ε,μ}`,
`0 ≤ ε ≤ ε₀`, `μ ∈ B̄(μ_*,δ)`, are admissible with constant `M₀`. -/
theorem c10_approx_admissible (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ ε₀ > 0, ∃ δ > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∃ M₀ > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ μ ∈ Bbar p δ, nonlinear_admissible_profile p M₀ (approximate_solution_family p R ε μ) := by
  have hp0 : 0 < p := by linarith
  have hμ := c10_aux_mu_star_norm_pos p hp0
  obtain ⟨ε₀, hε₀, R₀, -, hB, hS⟩ :=
    c10_ext_approx_profile_bounds p hp hp1 (‖mu_star p‖ / 2) (by positivity) le_rfl
  obtain ⟨C0, hC0, h0⟩ := hB 0
  obtain ⟨C1, hC1, h1⟩ := hB 1
  obtain ⟨C2, hC2, h2⟩ := hB 2
  refine ⟨ε₀, hε₀.1, ‖mu_star p‖ / 2, by positivity, R₀, fun R hR => ⟨max C0 (max C1 C2),
    lt_max_of_lt_left hC0, fun ε hε hεle μ hμB => ?_⟩⟩
  have hεI : ε ∈ Icc (0 : ℝ) ε₀ := ⟨hε, hεle⟩
  set f := approximate_solution_family p R ε μ with hf
  have hsm : ContDiff ℝ (⊤ : ℕ∞) f := (hS R hR ε hεI).1 μ hμB
  have hC2f : ContDiff ℝ 2 f := hsm.of_le (WithTop.coe_le_coe.2 (le_top : ((2 : ℕ∞) ≤ ⊤)))
  have hd : Differentiable ℝ f := hC2f.differentiable (by norm_num)
  have hdg : deriv (fun t => f t + t) = fun t => deriv f t + 1 := funext fun t => by
    exact ((hd t).hasDerivAt.add (hasDerivAt_id' t)).deriv
  have hdd : deriv (deriv (fun t => f t + t)) = deriv (deriv f) := by
    rw [hdg]; funext t
    rw [deriv_add_const]
  have e2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e2' : iteratedDeriv 2 (fun t => f t + t) = deriv (deriv (fun t => f t + t)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  set M := max C0 (max C1 C2)
  have m0 : C0 ≤ M := le_max_left _ _
  have m1 : C1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have m2 : C2 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have hj : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e => (Real.rpow_pos_of_pos (c10_aux_jb_pos y) e).le
  have up : ∀ {a C : ℝ} (y e : ℝ), C ≤ M → a ≤ C * jb y ^ e → a ≤ M * jb y ^ e :=
    fun y e hCM ha => ha.trans (mul_le_mul_of_nonneg_right hCM (hj y e))
  refine ⟨hC2f, fun y hy => ⟨?_, ?_, ?_⟩, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact up y _ m0 ((h0 R hR ε hεI μ hμB).1 y hy).1
  · have := ((h0 R hR ε hεI μ hμB).1 y hy).2
    simp only [zero_add, iteratedDeriv_one, CharP.cast_eq_zero, zero_div, add_zero] at this
    exact up y _ m0 this
  · have := ((h1 R hR ε hεI μ hμB).1 y hy).2
    simp only [Nat.reduceAdd, Nat.cast_one] at this
    rw [e2] at this
    exact up y _ m1 this
  · have := (h0 R hR ε hεI μ hμB).2 y hy
    simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero] at this
    exact up y _ m0 this
  · have := (h1 R hR ε hεI μ hμB).2 y hy
    simp only [iteratedDeriv_one, Nat.cast_one] at this
    rw [hdg] at this
    exact up y _ m1 this
  · have := (h2 R hR ε hεI μ hμB).2 y hy
    rw [e2', hdd] at this
    simp only [Nat.cast_ofNat] at this
    exact up y _ m2 this

/-- Blueprint: lem:c10_profile_consequences.  Consequences of admissibility of `f̄` and of
`‖r‖_{X_γ} ≤ N` for `f = f̄ + r` (items 1–3), and pointwise/`L¹` bounds for `h ∈ X_γ` (item 4). -/
theorem c10_profile_consequences (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N →
      -- item 1, for `f = f̄ + r` and for `f̄`
      (∀ g ∈ ({fbar + r, fbar} : Set (ℝ → ℝ)),
        (∀ y, |deriv g y| ≤ C) ∧ (∀ y ∈ Icc (-3 : ℝ) 3, |g y| ≤ C) ∧
        (∀ᵐ y, y ∈ Icc (-3 : ℝ) 3 → |deriv (deriv g) y| ≤ C) ∧
        (∀ y, |g y - corner y| ≤ C * jb y ^ (-p))) ∧
      -- item 2
      (∀ y : ℝ, 0 ≤ y → |deriv (fbar + r) y| ≤ C * jb y ^ (-beta p)) ∧
      (∀ᵐ y, 0 ≤ y → |deriv (deriv (fbar + r)) y| ≤ C * jb y ^ (-beta p + 1 / p)) ∧
      -- item 3
      (∀ y : ℝ, y ≤ 0 → |deriv (fbar + r) y + 1| ≤ C * jb y ^ (-p - 1)) ∧
      (∀ᵐ y, y ≤ 0 → |deriv (deriv (fbar + r)) y| ≤ C * jb y ^ (-p - 2)) ∧
      -- item 4
      (Integrable (fun z : ℝ => jb z ^ (-γ)) ∧
        ∀ h ∈ X_gamma p γ,
          (∀ y, |h y| ≤ xNorm p γ h) ∧
          (Integrable h ∧ ∫ y, |h y| ≤ (∫ z, jb z ^ (-γ)) * xNorm p γ h) ∧
          (∀ y : ℝ, 0 ≤ y → |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ + 1 / p)) ∧
          (∀ y : ℝ, y ≤ 0 → |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ - 1)) ∧
          (∀ᵐ y, 0 ≤ y → |deriv (deriv h) y| ≤ xNorm p γ h * jb y ^ (-γ + 2 / p)) ∧
          (∀ᵐ y, y ≤ 0 → |deriv (deriv h) y| ≤ xNorm p γ h * jb y ^ (-γ - 2)) ∧
          (∀ y, |deriv h y| ≤ xNorm p γ h) ∧
          (∀ᵐ y, y ∈ Icc (-3 : ℝ) 3 → |deriv (deriv h) y| ≤ (10 : ℝ) ^ (2 / p) * xNorm p γ h)) := by
  obtain ⟨hp0, hγp, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  have hβ1 : 1 < beta p := by unfold beta; rw [lt_div_iff₀ (by linarith)]; linarith
  have hβγ : beta p + 1 / p < γ := hγ.1
  have hip : 1 < 1 / p := by rw [lt_div_iff₀ hp0]; linarith
  have hβp : -beta p + 1 / p ≤ 1 := by
    have : 1 / p < 1 + p := by
      rw [div_lt_iff₀ hp0]; nlinarith
    unfold beta; rw [show -((p + 1) / (2 * p)) + 1 / p = (1 - p) / (2 * p) by field_simp; ring]
    rw [div_le_one (by linarith)]; linarith
  set T : ℝ := (10 : ℝ) ^ (2 / p) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow (by norm_num) (by positivity)
  have h4T : ∀ y : ℝ, |y| ≤ 3 → jb y ^ (2 / p) ≤ T := fun y hy =>
    (Real.rpow_le_rpow (c10_aux_jb_pos y).le (c10_aux_jb_le_four hy) (by positivity)).trans
      (Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity))
  have hjle1 := c10_aux_jb_rpow_le_one
  have hjmono := c10_aux_jb_rpow_mono
  have hjpos := c10_aux_jb_pos
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e => (Real.rpow_pos_of_pos (hjpos y) e).le
  have h2p : 2 / p = 2 * (1 / p) := by ring
  -- item 4 (for any `h ∈ X_γ`)
  have item4 : ∀ h ∈ X_gamma p γ,
      (∀ y, |h y| ≤ xNorm p γ h) ∧
      (Integrable h ∧ ∫ y, |h y| ≤ (∫ z, jb z ^ (-γ)) * xNorm p γ h) ∧
      (∀ y : ℝ, 0 ≤ y → |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ + 1 / p)) ∧
      (∀ y : ℝ, y ≤ 0 → |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ - 1)) ∧
      (∀ᵐ y, 0 ≤ y → |deriv (deriv h) y| ≤ xNorm p γ h * jb y ^ (-γ + 2 / p)) ∧
      (∀ᵐ y, y ≤ 0 → |deriv (deriv h) y| ≤ xNorm p γ h * jb y ^ (-γ - 2)) ∧
      (∀ y, |deriv h y| ≤ xNorm p γ h) ∧
      (∀ᵐ y, y ∈ Icc (-3 : ℝ) 3 → |deriv (deriv h) y| ≤ T * xNorm p γ h) := by
    intro h hh
    obtain ⟨s0, s1, s2, s3, s4⟩ := c10_aux_X_simple p γ hh
    have hx : 0 ≤ xNorm p γ h := ENNReal.toReal_nonneg
    have hint := c10_aux_jb_integrable hγ1
    have hbd : ∀ y, |h y| ≤ xNorm p γ h * jb y ^ (-γ) := s0
    refine ⟨fun y => (s0 y).trans ?_, ⟨?_, ?_⟩, s1, s2, s3, s4, fun y => ?_, ?_⟩
    · exact mul_le_of_le_one_right hx (hjle1 y (by linarith))
    · refine (hint.const_mul (xNorm p γ h)).mono' hh.1.1.continuous.aestronglyMeasurable
        (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs]; exact hbd y
    · calc (∫ y, |h y|) ≤ ∫ y, xNorm p γ h * jb y ^ (-γ) :=
            integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
              (hint.const_mul _) (ae_of_all _ hbd)
        _ = _ := by rw [integral_const_mul, mul_comm]
    · rcases le_total 0 y with hy | hy
      · exact (s1 y hy).trans (mul_le_of_le_one_right hx (hjle1 y (by linarith)))
      · exact (s2 y hy).trans (mul_le_of_le_one_right hx (hjle1 y (by linarith)))
    · filter_upwards [s3, s4] with y h3 h4 hy
      have hy3 : |y| ≤ 3 := abs_le.2 ⟨hy.1, hy.2⟩
      rcases le_total 0 y with hy0 | hy0
      · refine (h3 hy0).trans ?_
        rw [mul_comm T]
        refine mul_le_mul_of_nonneg_left ?_ hx
        exact (hjmono y (by linarith)).trans (h4T y hy3)
      · refine (h4 hy0).trans ?_
        rw [mul_comm T]
        exact mul_le_mul_of_nonneg_left ((hjle1 y (by linarith)).trans hT1) hx
  set C : ℝ := 4 * (M + N + 4) * T with hC
  have hCpos : 0 < C := by positivity
  have hCbig : M + N + 4 ≤ C := by
    have : 0 ≤ M + N + 4 := by linarith
    rw [hC]; nlinarith
  have hMNC : M + N ≤ C := by linarith
  refine ⟨C, hCpos, fun fbar hf r hr hrN => ?_⟩
  have hdf : Differentiable ℝ fbar := hf.1.differentiable (by norm_num)
  have hdf' : Differentiable ℝ (deriv fbar) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hf.1).2.2.differentiable (by norm_num)
  -- items 1–3 for `f̄ + s`
  have gen : ∀ s ∈ X_gamma p γ, xNorm p γ s ≤ N →
      ((∀ y, |deriv (fbar + s) y| ≤ C) ∧ (∀ y ∈ Icc (-3 : ℝ) 3, |(fbar + s) y| ≤ C) ∧
        (∀ᵐ y, y ∈ Icc (-3 : ℝ) 3 → |deriv (deriv (fbar + s)) y| ≤ C) ∧
        (∀ y, |(fbar + s) y - corner y| ≤ C * jb y ^ (-p))) ∧
      (∀ y : ℝ, 0 ≤ y → |deriv (fbar + s) y| ≤ C * jb y ^ (-beta p)) ∧
      (∀ᵐ y, 0 ≤ y → |deriv (deriv (fbar + s)) y| ≤ C * jb y ^ (-beta p + 1 / p)) ∧
      (∀ y : ℝ, y ≤ 0 → |deriv (fbar + s) y + 1| ≤ C * jb y ^ (-p - 1)) ∧
      (∀ᵐ y, y ≤ 0 → |deriv (deriv (fbar + s)) y| ≤ C * jb y ^ (-p - 2)) := by
    intro s hs hsN
    obtain ⟨s0, s1, s2, s3, s4⟩ := c10_aux_X_simple p γ hs
    obtain ⟨-, -, -, -, -, -, s5, s6⟩ := item4 s hs
    have hx : 0 ≤ xNorm p γ s := ENNReal.toReal_nonneg
    have hds : Differentiable ℝ s := hs.1.1.differentiable (by norm_num)
    have hD : ∀ y, deriv (fbar + s) y = deriv fbar y + deriv s y := fun y =>
      deriv_add (hdf y) (hds y)
    have hDD : ∀ᵐ y, deriv (deriv (fbar + s)) y = deriv (deriv fbar) y + deriv (deriv s) y := by
      filter_upwards [c10_aux_ae_differentiableAt hs.1.2] with y hy
      rw [show deriv (fbar + s) = fun x => deriv fbar x + deriv s x from funext hD]
      exact deriv_add (hdf' y) hy
    have fpos := hf.2.1
    have fneg := hf.2.2
    have hMj : ∀ y {e : ℝ}, e ≤ 0 → M * jb y ^ e ≤ M := fun y e he =>
      mul_le_of_le_one_right hM.le (hjle1 y he)
    have hNj : ∀ y {e e' : ℝ}, e ≤ e' → xNorm p γ s * jb y ^ e ≤ N * jb y ^ e' := fun y e e' he =>
      mul_le_mul hsN (hjmono y he) (hjnn y e) hN.le
    have hCj : ∀ y (e : ℝ), (M + N) * jb y ^ e ≤ C * jb y ^ e := fun y e =>
      mul_le_mul_of_nonneg_right hMNC (hjnn y e)
    -- `|f̄'| ≤ M + 1`
    have hf1 : ∀ y, |deriv fbar y| ≤ M + 1 := by
      intro y
      rcases le_total 0 y with hy | hy
      · have := (fpos y hy).2.1
        have := hMj y (show -beta p ≤ 0 by linarith)
        linarith
      · have h1 := (fneg y hy).2.1
        have := hMj y (show -p - 1 ≤ 0 by linarith)
        have h3 := abs_sub (deriv fbar y + 1) 1
        simp only [add_sub_cancel_right, abs_one] at h3
        linarith
    refine ⟨⟨fun y => ?_, fun y hy => ?_, ?_, fun y => ?_⟩, fun y hy => ?_, ?_, fun y hy => ?_, ?_⟩
    · rw [hD]
      have := abs_add_le (deriv fbar y) (deriv s y)
      have := hf1 y; have := s5 y
      linarith
    · have hy3 : |y| ≤ 3 := abs_le.2 ⟨hy.1, hy.2⟩
      simp only [Pi.add_apply]
      have hsb : |s y| ≤ N := by
        have := s0 y
        have := mul_le_of_le_one_right hx (hjle1 y (show -γ ≤ 0 by linarith))
        linarith
      have hfb : |fbar y| ≤ M + 3 := by
        rcases le_total 0 y with hy0 | hy0
        · have := (fpos y hy0).1; have := hMj y (show -p ≤ 0 by linarith)
          linarith
        · have h1 := (fneg y hy0).1; have := hMj y (show -p ≤ 0 by linarith)
          have h2 := abs_sub (fbar y + y) y
          simp only [add_sub_cancel_right] at h2
          linarith
      have := abs_add_le (fbar y) (s y)
      linarith
    · filter_upwards [hDD, s6] with y hy h6 hyI
      have hy3 : |y| ≤ 3 := abs_le.2 ⟨hyI.1, hyI.2⟩
      rw [hy]
      have hfb : |deriv (deriv fbar) y| ≤ 4 * M := by
        rcases le_total 0 y with hy0 | hy0
        · have := (fpos y hy0).2.2
          have : jb y ^ (-beta p + 1 / p) ≤ 4 :=
            (hjmono y hβp).trans (by rw [Real.rpow_one]; exact c10_aux_jb_le_four hy3)
          have := mul_le_mul_of_nonneg_left this hM.le
          linarith
        · have := (fneg y hy0).2.2; have := hMj y (show -p - 2 ≤ 0 by linarith)
          linarith
      have := h6 hyI
      have := abs_add_le (deriv (deriv fbar) y) (deriv (deriv s) y)
      have : T * xNorm p γ s ≤ T * N := mul_le_mul_of_nonneg_left hsN (by linarith)
      have : 4 * M + T * N ≤ C := by
        rw [hC]; nlinarith
      linarith
    · simp only [Pi.add_apply]
      have hsb : |s y| ≤ N * jb y ^ (-p) := (s0 y).trans (hNj y (by linarith))
      have := hCj y (-p)
      rcases le_total 0 y with hy0 | hy0
      · have hc : corner y = 0 := by unfold corner; simp [hy0]
        rw [hc, sub_zero]
        have := (fpos y hy0).1
        have := abs_add_le (fbar y) (s y)
        linarith
      · have hc : corner y = -y := by unfold corner; simp [hy0]
        rw [hc, show fbar y + s y - -y = (fbar y + y) + s y by ring]
        have := (fneg y hy0).1
        have := abs_add_le (fbar y + y) (s y)
        linarith
    · rw [hD]
      have h1 := (fpos y hy).2.1
      have h2 : |deriv s y| ≤ N * jb y ^ (-beta p) := (s1 y hy).trans (hNj y (by linarith))
      have := abs_add_le (deriv fbar y) (deriv s y)
      have := hCj y (-beta p)
      linarith
    · filter_upwards [hDD, s3] with y hy h3 hy0
      rw [hy]
      have h1 := (fpos y hy0).2.2
      have h2 : |deriv (deriv s) y| ≤ N * jb y ^ (-beta p + 1 / p) :=
        (h3 hy0).trans (hNj y (by linarith))
      have := abs_add_le (deriv (deriv fbar) y) (deriv (deriv s) y)
      have := hCj y (-beta p + 1 / p)
      linarith
    · rw [hD, show deriv fbar y + deriv s y + 1 = (deriv fbar y + 1) + deriv s y by ring]
      have h1 := (fneg y hy).2.1
      have h2 : |deriv s y| ≤ N * jb y ^ (-p - 1) := (s2 y hy).trans (hNj y (by linarith))
      have := abs_add_le (deriv fbar y + 1) (deriv s y)
      have := hCj y (-p - 1)
      linarith
    · filter_upwards [hDD, s4] with y hy h4 hy0
      rw [hy]
      have h1 := (fneg y hy0).2.2
      have h2 : |deriv (deriv s) y| ≤ N * jb y ^ (-p - 2) := (h4 hy0).trans (hNj y (by linarith))
      have := abs_add_le (deriv (deriv fbar) y) (deriv (deriv s) y)
      have := hCj y (-p - 2)
      linarith
  obtain ⟨g1, g2, g3, g4, g5⟩ := gen r hr hrN
  obtain ⟨hz, hz0⟩ := c10_aux_X_zero p γ
  obtain ⟨z1, -⟩ := gen 0 hz (by rw [hz0]; exact hN.le)
  rw [add_zero] at z1
  refine ⟨fun g hg => ?_, g2, g3, g4, g5, c10_aux_jb_integrable hγ1, item4⟩
  rcases hg with rfl | hg
  · exact g1
  · rw [mem_singleton_iff] at hg; rw [hg]; exact z1

/-- Helper: `|y| ≤ ⟨y⟩`. -/
theorem c10_aux_abs_le_jb (y : ℝ) : |y| ≤ jb y := by
  unfold jb; exact Real.abs_le_sqrt (by linarith)

/-- Helper: `⟨y⟩ · ⟨y⟩^e = ⟨y⟩^{1+e}`. -/
theorem c10_aux_jb_mul (y e : ℝ) : jb y * jb y ^ e = jb y ^ (1 + e) := by
  rw [Real.rpow_add (c10_aux_jb_pos y), Real.rpow_one]

/-- Helper: `|y| · |a| ≤ X ⟨y⟩^{1+e}` from `|a| ≤ X ⟨y⟩^e`. -/
theorem c10_aux_mul_y_bound {y a X e : ℝ} (_hX : 0 ≤ X) (h : |a| ≤ X * jb y ^ e) :
    |y * a| ≤ X * jb y ^ (1 + e) := by
  rw [abs_mul, ← c10_aux_jb_mul, show X * (jb y * jb y ^ e) = jb y * (X * jb y ^ e) by ring]
  exact mul_le_mul (c10_aux_abs_le_jb y) h (abs_nonneg _) (c10_aux_jb_pos y).le

/-- Helper: `∂_y(g - y g') = -y g''` at points where `g` and `g'` are differentiable. -/
theorem c10_aux_transport_deriv {g : ℝ → ℝ} {y : ℝ} (h1 : DifferentiableAt ℝ g y)
    (h2 : DifferentiableAt ℝ (deriv g) y) :
    deriv (fun x => g x - x * deriv g x) y = -(y * deriv (deriv g) y) := by
  have : HasDerivAt (fun x => g x - x * deriv g x)
      (deriv g y - (1 * deriv g y + y * deriv (deriv g) y)) y :=
    h1.hasDerivAt.sub ((hasDerivAt_id' y).mul h2.hasDerivAt)
  rw [this.deriv]; ring

/-- Blueprint: lem:c10_transport_factors.  Bounds for the transport factors `f̄ - y f̄'`,
`r - y r'` and their derivatives `-y f̄''`, `-y r''`. -/
theorem c10_transport_factors (p γ M : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) :
    ∃ C > 0, ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      (∀ y : ℝ, 0 ≤ y → |fbar y - y * deriv fbar y| ≤ C * jb y ^ (1 - beta p)) ∧
      (∀ y : ℝ, y ≤ 0 → |fbar y - y * deriv fbar y| ≤ C * jb y ^ (-p)) ∧
      (∀ y, deriv (fun x => fbar x - x * deriv fbar x) y = -(y * deriv (deriv fbar) y)) ∧
      (∀ y : ℝ, 0 ≤ y → |y * deriv (deriv fbar) y| ≤ C * jb y ^ (1 - beta p + 1 / p)) ∧
      (∀ y : ℝ, y ≤ 0 → |y * deriv (deriv fbar) y| ≤ C * jb y ^ (-p - 1)) ∧
      ∀ r ∈ X_gamma p γ,
        (∀ y : ℝ, 0 ≤ y → |r y - y * deriv r y| ≤ 2 * xNorm p γ r * jb y ^ (1 - γ + 1 / p)) ∧
        (∀ y : ℝ, y ≤ 0 → |r y - y * deriv r y| ≤ 2 * xNorm p γ r * jb y ^ (-γ)) ∧
        (∀ᵐ y, deriv (fun x => r x - x * deriv r x) y = -(y * deriv (deriv r) y)) ∧
        (∀ᵐ y, 0 ≤ y → |y * deriv (deriv r) y| ≤ xNorm p γ r * jb y ^ (1 - γ + 2 / p)) ∧
        (∀ᵐ y, y ≤ 0 → |y * deriv (deriv r) y| ≤ xNorm p γ r * jb y ^ (-γ - 1)) := by
  obtain ⟨hp0, hγp, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  have hβp : beta p ≤ 1 + p := by
    unfold beta; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hjmono := c10_aux_jb_rpow_mono
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e =>
    (Real.rpow_pos_of_pos (c10_aux_jb_pos y) e).le
  have hip : 0 < 1 / p := by positivity
  refine ⟨2 * M, by positivity, fun fbar hf => ⟨fun y hy => ?_, fun y hy => ?_, fun y => ?_,
    fun y hy => ?_, fun y hy => ?_, fun r hr => ?_⟩⟩
  · obtain ⟨f0, f1, -⟩ := hf.2.1 y hy
    have a := c10_aux_mul_y_bound (y := y) hM.le f1
    have b : M * jb y ^ (-p) ≤ M * jb y ^ (1 - beta p) :=
      mul_le_mul_of_nonneg_left (hjmono y (by linarith)) hM.le
    have c := abs_sub (fbar y) (y * deriv fbar y)
    rw [show 1 + -beta p = 1 - beta p by ring] at a
    linarith
  · obtain ⟨f0, f1, -⟩ := hf.2.2 y hy
    have a := c10_aux_mul_y_bound (y := y) hM.le f1
    rw [show 1 + (-p - 1) = -p by ring] at a
    have c := abs_sub (fbar y + y) (y * (deriv fbar y + 1))
    rw [show fbar y + y - y * (deriv fbar y + 1) = fbar y - y * deriv fbar y by ring] at c
    linarith
  · exact c10_aux_transport_deriv (hf.1.differentiable (by norm_num) y)
      (((contDiff_succ_iff_deriv (n := 1)).1 hf.1).2.2.differentiable (by norm_num) y)
  · have a := c10_aux_mul_y_bound (y := y) hM.le (hf.2.1 y hy).2.2
    rw [show 1 + (-beta p + 1 / p) = 1 - beta p + 1 / p by ring] at a
    have := mul_le_mul_of_nonneg_right (show M ≤ 2 * M by linarith) (hjnn y (1 - beta p + 1 / p))
    linarith
  · have a := c10_aux_mul_y_bound (y := y) hM.le (hf.2.2 y hy).2.2
    rw [show 1 + (-p - 2) = -p - 1 by ring] at a
    have := mul_le_mul_of_nonneg_right (show M ≤ 2 * M by linarith) (hjnn y (-p - 1))
    linarith
  · obtain ⟨s0, s1, s2, s3, s4⟩ := c10_aux_X_simple p γ hr
    have hx : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg
    refine ⟨fun y hy => ?_, fun y hy => ?_, ?_, ?_, ?_⟩
    · have a := c10_aux_mul_y_bound (y := y) hx (s1 y hy)
      rw [show 1 + (-γ + 1 / p) = 1 - γ + 1 / p by ring] at a
      have b : xNorm p γ r * jb y ^ (-γ) ≤ xNorm p γ r * jb y ^ (1 - γ + 1 / p) :=
        mul_le_mul_of_nonneg_left (hjmono y (by linarith)) hx
      have c := abs_sub (r y) (y * deriv r y)
      have := s0 y
      linarith
    · have a := c10_aux_mul_y_bound (y := y) hx (s2 y hy)
      rw [show 1 + (-γ - 1) = -γ by ring] at a
      have c := abs_sub (r y) (y * deriv r y)
      have := s0 y
      linarith
    · filter_upwards [c10_aux_ae_differentiableAt hr.1.2] with y hy
      exact c10_aux_transport_deriv (hr.1.1.differentiable (by norm_num) y) hy
    · filter_upwards [s3] with y hy hy0
      have a := c10_aux_mul_y_bound (y := y) hx (hy hy0)
      rwa [show 1 + (-γ + 2 / p) = 1 - γ + 2 / p by ring] at a
    · filter_upwards [s4] with y hy hy0
      have a := c10_aux_mul_y_bound (y := y) hx (hy hy0)
      rwa [show 1 + (-γ - 2) = -γ - 1 by ring] at a

/-- Helper: the derivative of `B_ε`: `B_ε'(u) = 2εu · (α/2) · (1+εu²)^{α/2-1}`. -/
theorem c10_aux_B_hasDeriv (p ε : ℝ) (hε : 0 ≤ ε) (u : ℝ) :
    HasDerivAt (A_eps_B p ε)
      (2 * ε * u * ((p + 1) / 2) * (1 + ε * u ^ 2) ^ ((p + 1) / 2 - 1)) u := by
  have hg : HasDerivAt (fun u => 1 + ε * u ^ 2) (2 * ε * u) u := by
    have := ((hasDerivAt_pow 2 u).const_mul ε).const_add 1
    convert this using 1; push_cast; ring
  have hpos : 0 < 1 + ε * u ^ 2 := by positivity
  exact hg.rpow_const (Or.inl hpos.ne')

/-- Helper: `deriv B_ε` as an explicit function. -/
theorem c10_aux_B_deriv (p ε : ℝ) (hε : 0 ≤ ε) :
    deriv (A_eps_B p ε) =
      fun u => 2 * ε * u * ((p + 1) / 2) * (1 + ε * u ^ 2) ^ ((p + 1) / 2 - 1) :=
  funext fun u => (c10_aux_B_hasDeriv p ε hε u).deriv

/-- Blueprint: lem:c10_B_bounds.  For `0 ≤ ε ≤ 1`, `R > 0`, `|u| ≤ R`:
`|B_ε(u) - 1| ≤ (α/2) ε u²`, `|B_ε'(u)| ≤ α ε |u|`, `|B_ε''(u)| ≤ α (1+R²) ε`. -/
theorem c10_B_bounds (p ε R : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (u : ℝ) (hu : |u| ≤ R) :
    |A_eps_B p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 ∧
    |deriv (A_eps_B p ε) u| ≤ (p + 1) * ε * |u| ∧
    |deriv (deriv (A_eps_B p ε)) u| ≤ (p + 1) * (1 + R ^ 2) * ε := by
  set a := (p + 1) / 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have hx0 : 0 ≤ ε * u ^ 2 := by positivity
  have hg1 : 1 ≤ 1 + ε * u ^ 2 := by linarith
  have hgpos : 0 < 1 + ε * u ^ 2 := by linarith
  have hu2 : u ^ 2 ≤ R ^ 2 := by
    have := abs_nonneg u; nlinarith [sq_abs u]
  have hεu : ε * u ^ 2 ≤ R ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (1 + ε * u ^ 2) ^ a ≤ 1 + a * (ε * u ^ 2) :=
      rpow_one_add_le_one_add_mul_self (by linarith) ha0 ha1
    have h2 : 1 ≤ (1 + ε * u ^ 2) ^ a := Real.one_le_rpow hg1 ha0
    unfold A_eps_B
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  · rw [c10_aux_B_deriv p ε hε]
    have h3 : (1 + ε * u ^ 2) ^ (a - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hg1 (by linarith)
    have h4 : 0 ≤ (1 + ε * u ^ 2) ^ (a - 1) := Real.rpow_nonneg hgpos.le _
    simp only
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2),
      abs_of_nonneg hε, abs_of_nonneg ha0, abs_of_nonneg h4]
    have := abs_nonneg u
    have e : (p + 1) * ε * |u| = 2 * ε * |u| * a * 1 := by rw [ha]; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left h3 (by positivity)
  · -- second derivative
    have hd2 : HasDerivAt (fun u => 2 * ε * u * a * (1 + ε * u ^ 2) ^ (a - 1))
        (2 * ε * a * ((1 + ε * u ^ 2) ^ (a - 2) * (1 + ε * u ^ 2 + 2 * (a - 1) * (ε * u ^ 2)))) u := by
      have hg : HasDerivAt (fun u => 1 + ε * u ^ 2) (2 * ε * u) u := by
        have := ((hasDerivAt_pow 2 u).const_mul ε).const_add 1
        convert this using 1; push_cast; ring
      have hr := hg.rpow_const (p := a - 1) (Or.inl hgpos.ne')
      have hl : HasDerivAt (fun u => 2 * ε * u * a) (2 * ε * a) u := by
        have := ((hasDerivAt_id u).const_mul (2 * ε)).mul_const a
        convert this using 1 <;> simp
      have := hl.mul hr
      convert this using 1
      have e : (1 + ε * u ^ 2) ^ (a - 1) = (1 + ε * u ^ 2) ^ (a - 2) * (1 + ε * u ^ 2) := by
        rw [show a - 1 = (a - 2) + 1 by ring, Real.rpow_add hgpos, Real.rpow_one]
      rw [show a - 1 - 1 = a - 2 by ring, e]
      ring
    rw [c10_aux_B_deriv p ε hε, hd2.deriv]
    have h3 : (1 + ε * u ^ 2) ^ (a - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hg1 (by linarith)
    have h4 : 0 ≤ (1 + ε * u ^ 2) ^ (a - 2) := Real.rpow_nonneg hgpos.le _
    have hin : 0 ≤ 1 + ε * u ^ 2 + 2 * (a - 1) * (ε * u ^ 2) := by
      rw [ha]; nlinarith
    have hin2 : 1 + ε * u ^ 2 + 2 * (a - 1) * (ε * u ^ 2) ≤ 1 + R ^ 2 := by
      rw [ha]; nlinarith
    rw [abs_of_nonneg (by positivity)]
    have : (1 + ε * u ^ 2) ^ (a - 2) * (1 + ε * u ^ 2 + 2 * (a - 1) * (ε * u ^ 2)) ≤ 1 + R ^ 2 := by
      calc _ ≤ 1 * (1 + R ^ 2) := mul_le_mul h3 hin2 hin zero_le_one
        _ = _ := one_mul _
    have e : (p + 1) * (1 + R ^ 2) * ε = 2 * ε * a * (1 + R ^ 2) := by rw [ha]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left this (by positivity)

/-- Helper: `Y_γ` membership and norm bound from a.e. weighted pointwise bounds. -/
theorem c10_aux_Y_of_decay (p γ A : ℝ) {G : ℝ → ℝ} (hW : W1inftyLoc G) (hA : 0 ≤ A)
    (h1 : ∀ᵐ y, 0 ≤ y → |G y| ≤ A * jb y ^ (-γ) ∧ |deriv G y| ≤ A * jb y ^ (-γ + 1 / p))
    (h2 : ∀ᵐ y, y ≤ 0 → |G y| ≤ A * jb y ^ (-γ) ∧ |deriv G y| ≤ A * jb y ^ (-γ - 1)) :
    G ∈ Y_gamma p γ ∧ yNorm p γ G ≤ 4 * A := by
  have hj := c10_aux_jb_pos
  have e1 : ∀ y, jb y ^ γ * (A * jb y ^ (-γ) + jb y ^ (-1 / p) * (A * jb y ^ (-γ + 1 / p))) =
      2 * A := by
    intro y
    have a : jb y ^ γ * jb y ^ (-γ) = 1 := by
      rw [← Real.rpow_add (hj y)]; simp
    have b : jb y ^ γ * (jb y ^ (-1 / p) * jb y ^ (-γ + 1 / p)) = 1 := by
      rw [← Real.rpow_add (hj y), ← Real.rpow_add (hj y)]
      rw [show γ + (-1 / p + (-γ + 1 / p)) = 0 by ring]; simp
    linear_combination A * a + A * b
  have e2 : ∀ y, jb y ^ γ * (A * jb y ^ (-γ) + jb y * (A * jb y ^ (-γ - 1))) = 2 * A := by
    intro y
    have a : jb y ^ γ * jb y ^ (-γ) = 1 := by
      rw [← Real.rpow_add (hj y)]; simp
    have b : jb y ^ γ * (jb y * jb y ^ (-γ - 1)) = 1 := by
      rw [c10_aux_jb_mul, ← Real.rpow_add (hj y)]
      rw [show γ + (1 + (-γ - 1)) = 0 by ring]; simp
    linear_combination A * a + A * b
  have hle1 : essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖)))
      (volume.restrict (Ici 0)) ≤ ENNReal.ofReal (2 * A) := by
    refine essSup_le_of_ae_le _ ?_
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [h1] with y hy hy0
    obtain ⟨a, b⟩ := hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← e1 y]
    simp only [Real.norm_eq_abs]
    have := hj y
    gcongr
  have hle2 : essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖)))
      (volume.restrict (Iic 0)) ≤ ENNReal.ofReal (2 * A) := by
    refine essSup_le_of_ae_le _ ?_
    refine (ae_restrict_iff' measurableSet_Iic).2 ?_
    filter_upwards [h2] with y hy hy0
    obtain ⟨a, b⟩ := hy hy0
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← e2 y]
    simp only [Real.norm_eq_abs]
    have := hj y
    gcongr
  have hle : Y_gamma_norm p γ G ≤ ENNReal.ofReal (2 * A) + ENNReal.ofReal (2 * A) :=
    add_le_add hle1 hle2
  have hfin : Y_gamma_norm p γ G < ⊤ :=
    lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  refine ⟨⟨hW, hfin⟩, ?_⟩
  unfold yNorm
  calc (Y_gamma_norm p γ G).toReal ≤ (ENNReal.ofReal (2 * A) + ENNReal.ofReal (2 * A)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hle
    _ = 4 * A := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (by linarith)]; ring

/-- Helper: the product of two real locally Lipschitz functions is locally Lipschitz. -/
theorem c10_aux_locLip_mul {f g : ℝ → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => f x * g x) := by
  intro x
  set s := Icc (x - 1) (x + 1)
  obtain ⟨Kf, hKf⟩ := (hf.locallyLipschitzOn (s := s)).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  obtain ⟨Kg, hKg⟩ := (hg.locallyLipschitzOn (s := s)).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  obtain ⟨Bf, hBf⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuous.continuousOn (s := s))
  obtain ⟨Bg, hBg⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuous.continuousOn (s := s))
  refine ⟨_, s, Icc_mem_nhds (by linarith) (by linarith),
    LipschitzOnWith.of_dist_le' (K := Bf * Kg + Bg * Kf) fun y hy z hz => ?_⟩
  have h1 := hKf.dist_le_mul y hy z hz
  have h2 := hKg.dist_le_mul y hy z hz
  have b1 := hBf y hy
  have b2 := hBg z hz
  simp only [Real.dist_eq, Real.norm_eq_abs] at *
  have e : f y * g y - f z * g z = f y * (g y - g z) + g z * (f y - f z) := by ring
  rw [e]
  have hd : 0 ≤ |y - z| := abs_nonneg _
  have hKf0 : (0 : ℝ) ≤ Kf := Kf.2
  have hKg0 : (0 : ℝ) ≤ Kg := Kg.2
  calc |f y * (g y - g z) + g z * (f y - f z)|
      ≤ |f y| * |g y - g z| + |g z| * |f y - f z| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Bf * (Kg * |y - z|) + Bg * (Kf * |y - z|) := by
        apply add_le_add
        · exact mul_le_mul b1 h2 (abs_nonneg _) ((abs_nonneg _).trans b1)
        · exact mul_le_mul b2 h1 (abs_nonneg _) ((abs_nonneg _).trans b2)
    _ = (Bf * Kg + Bg * Kf) * |y - z| := by ring

/-- Helper: `B_ε` is `C^∞`, hence locally Lipschitz. -/
theorem c10_aux_B_contDiff (p ε : ℝ) (hε : 0 ≤ ε) : ContDiff ℝ 1 (A_eps_B p ε) := by
  unfold A_eps_B
  exact (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).rpow_const_of_ne
    fun x => by positivity

/-- Helper: chain rule for `y ↦ B_ε(u(y))` at a point where `u` is differentiable. -/
theorem c10_aux_B_comp_deriv (p ε : ℝ) (hε : 0 ≤ ε) {u : ℝ → ℝ} {y : ℝ}
    (hu : DifferentiableAt ℝ u y) :
    deriv (fun x => A_eps_B p ε (u x)) y = deriv (A_eps_B p ε) (u y) * deriv u y := by
  have : HasDerivAt (fun x => A_eps_B p ε (u x)) _ y :=
    ((c10_aux_B_hasDeriv p ε hε (u y))).comp y hu.hasDerivAt
  rw [this.deriv, (c10_aux_B_hasDeriv p ε hε (u y)).deriv]

/-! ### The local pieces `𝒩₁`, `𝒩₂` -/

/-- Helper: `B_ε ∈ C²`. -/
theorem c10_aux_B_contDiff2 (p ε : ℝ) (hε : 0 ≤ ε) : ContDiff ℝ 2 (A_eps_B p ε) := by
  unfold A_eps_B
  exact (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).rpow_const_of_ne
    fun x => by positivity

/-- Helper: Lipschitz bounds for `B_ε` and `B_ε'` on `[-ρ, ρ]`. -/
theorem c10_aux_B_lip (p ε ρ : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hρ : 0 < ρ) {a b : ℝ} (ha : |a| ≤ ρ) (hb : |b| ≤ ρ) :
    |A_eps_B p ε a - A_eps_B p ε b| ≤ (p + 1) * ε * ρ * |a - b| ∧
    |deriv (A_eps_B p ε) a - deriv (A_eps_B p ε) b| ≤ (p + 1) * (1 + ρ ^ 2) * ε * |a - b| := by
  have hB2 := c10_aux_B_contDiff2 p ε hε
  have hBd : Differentiable ℝ (A_eps_B p ε) := hB2.differentiable (by norm_num)
  have hB'd : Differentiable ℝ (deriv (A_eps_B p ε)) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hB2).2.2.differentiable (by norm_num)
  have hs : Convex ℝ (Icc (-ρ) ρ) := convex_Icc _ _
  have ma : a ∈ Icc (-ρ) ρ := abs_le.1 ha
  have mb : b ∈ Icc (-ρ) ρ := abs_le.1 hb
  constructor
  · have := hs.norm_image_sub_le_of_norm_deriv_le (f := A_eps_B p ε) (C := (p + 1) * ε * ρ)
      (fun x _ => hBd x) (fun x hx => by
        rw [Real.norm_eq_abs]
        have hx' : |x| ≤ ρ := abs_le.2 hx
        have := (c10_B_bounds p ε ρ hp hp1 hε hε1 hρ x hx').2.1
        have : 0 ≤ (p + 1) * ε := by have : 0 < p + 1 := by linarith
                                     positivity
        nlinarith) mb ma
    simpa [Real.norm_eq_abs] using this
  · have := hs.norm_image_sub_le_of_norm_deriv_le (f := deriv (A_eps_B p ε))
      (C := (p + 1) * (1 + ρ ^ 2) * ε)
      (fun x _ => hB'd x) (fun x hx => by
        rw [Real.norm_eq_abs]
        exact (c10_B_bounds p ε ρ hp hp1 hε hε1 hρ x (abs_le.2 hx)).2.2) mb ma
    simpa [Real.norm_eq_abs] using this

/-- Blueprint: lem:c10_delta_B.  `ΔB_ε = B_ε(f̄'+r₁') - B_ε(f̄'+r₂') ∈ W^{1,∞}_loc` with the weighted
bounds on `ΔB_ε` and `∂_y ΔB_ε`. -/
theorem c10_delta_B (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r₁ ∈ X_gamma p γ, ∀ r₂ ∈ X_gamma p γ, xNorm p γ r₁ ≤ N → xNorm p γ r₂ ≤ N →
      W1inftyLoc (fun y => A_eps_B p ε (deriv fbar y + deriv r₁ y) -
          A_eps_B p ε (deriv fbar y + deriv r₂ y)) ∧
      (∀ᵐ y, 0 ≤ y → |A_eps_B p ε (deriv fbar y + deriv r₁ y) -
          A_eps_B p ε (deriv fbar y + deriv r₂ y)| ≤
            C * ε * xNorm p γ (r₁ - r₂) * jb y ^ (-beta p - γ + 1 / p)) ∧
      (∀ᵐ y, y ≤ 0 → |A_eps_B p ε (deriv fbar y + deriv r₁ y) -
          A_eps_B p ε (deriv fbar y + deriv r₂ y)| ≤
            C * ε * xNorm p γ (r₁ - r₂) * jb y ^ (-γ - 1)) ∧
      (∀ᵐ y, 0 ≤ y → |deriv (fun x => A_eps_B p ε (deriv fbar x + deriv r₁ x) -
          A_eps_B p ε (deriv fbar x + deriv r₂ x)) y| ≤
            C * ε * xNorm p γ (r₁ - r₂) * jb y ^ (-beta p - γ + 2 / p)) ∧
      (∀ᵐ y, y ≤ 0 → |deriv (fun x => A_eps_B p ε (deriv fbar x + deriv r₁ x) -
          A_eps_B p ε (deriv fbar x + deriv r₂ x)) y| ≤
            C * ε * xNorm p γ (r₁ - r₂) * jb y ^ (-γ - 2)) := by
  obtain ⟨hp0, -, -, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨CP, hCP, hPC⟩ := c10_profile_consequences p γ M N hp hp1 hγ hM hN
  have hp1' : 0 < p + 1 := by linarith
  set K := (p + 1) * CP * (2 + CP ^ 2) with hK
  have hKpos : 0 < K := by positivity
  have hK1 : (p + 1) * CP ≤ K := by
    rw [hK]; have : 0 ≤ (p + 1) * CP := by positivity
    nlinarith [sq_nonneg CP]
  refine ⟨K, hKpos, fun ε hε hε1 fbar hf r₁ hr₁ r₂ hr₂ hN₁ hN₂ => ?_⟩
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e =>
    (Real.rpow_pos_of_pos (c10_aux_jb_pos y) e).le
  have hjpos : ∀ y (e : ℝ), 0 < jb y ^ e := fun y e => Real.rpow_pos_of_pos (c10_aux_jb_pos y) e
  obtain ⟨P1, P1a, P1b, -, P1c, -⟩ := hPC fbar hf r₁ hr₁ hN₁
  obtain ⟨P2, P2a, P2b, -, P2c, -⟩ := hPC fbar hf r₂ hr₂ hN₂
  obtain ⟨u1b, -, -, -⟩ := P1 (fbar + r₁) (by simp)
  obtain ⟨u2b, -, -, -⟩ := P2 (fbar + r₂) (by simp)
  have hh := c10_aux_X_sub p γ hr₁ hr₂
  obtain ⟨-, H1, H2, H3, H4⟩ := c10_aux_X_simple p γ hh
  set h := r₁ - r₂ with hhdef
  set xh := xNorm p γ h with hxh
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  have hdf : Differentiable ℝ fbar := hf.1.differentiable (by norm_num)
  have hd1 : Differentiable ℝ r₁ := hr₁.1.1.differentiable (by norm_num)
  have hd2 : Differentiable ℝ r₂ := hr₂.1.1.differentiable (by norm_num)
  have hu1 : (fun x => deriv fbar x + deriv r₁ x) = deriv (fbar + r₁) :=
    funext fun x => (deriv_add (hdf x) (hd1 x)).symm
  have hu2 : (fun x => deriv fbar x + deriv r₂ x) = deriv (fbar + r₂) :=
    funext fun x => (deriv_add (hdf x) (hd2 x)).symm
  have hdh : deriv h = fun x => deriv (fbar + r₁) x - deriv (fbar + r₂) x := by
    funext x
    rw [hhdef, deriv_sub (hd1 x) (hd2 x), ← congrFun hu1 x, ← congrFun hu2 x]; ring
  set u1 := deriv (fbar + r₁)
  set u2 := deriv (fbar + r₂)
  have hfA := c10_aux_C2_admissible_class hf.1
    (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have hu1L : LocallyLipschitz u1 := by rw [← hu1]; exact hfA.2.2.add hr₁.1.2
  have hu2L : LocallyLipschitz u2 := by rw [← hu2]; exact hfA.2.2.add hr₂.1.2
  have hv1 : ∀ y, deriv fbar y + deriv r₁ y = u1 y := fun y => congrFun hu1 y
  have hv2 : ∀ y, deriv fbar y + deriv r₂ y = u2 y := fun y => congrFun hu2 y
  simp only [hv1, hv2]
  have hBL : LocallyLipschitz (A_eps_B p ε) := (c10_aux_B_contDiff p ε hε).locallyLipschitz
  -- the derivative of `ΔB` at points where `u₁, u₂` are differentiable
  have hderiv : ∀ y, DifferentiableAt ℝ u1 y → DifferentiableAt ℝ u2 y →
      |deriv (fun y => A_eps_B p ε (u1 y) - A_eps_B p ε (u2 y)) y| ≤
        |deriv (A_eps_B p ε) (u1 y)| * |deriv (deriv h) y| +
          |deriv (A_eps_B p ε) (u1 y) - deriv (A_eps_B p ε) (u2 y)| * |deriv u2 y| := by
    intro y a1 a2
    have e1 : HasDerivAt (fun x => A_eps_B p ε (u1 x)) _ y :=
      (c10_aux_B_hasDeriv p ε hε (u1 y)).comp y a1.hasDerivAt
    have e2 : HasDerivAt (fun x => A_eps_B p ε (u2 x)) _ y :=
      (c10_aux_B_hasDeriv p ε hε (u2 y)).comp y a2.hasDerivAt
    have e3 : HasDerivAt (fun y => A_eps_B p ε (u1 y) - A_eps_B p ε (u2 y)) _ y := e1.sub e2
    rw [e3.deriv, ← (c10_aux_B_hasDeriv p ε hε (u1 y)).deriv,
      ← (c10_aux_B_hasDeriv p ε hε (u2 y)).deriv]
    have hdd : deriv (deriv h) y = deriv u1 y - deriv u2 y := by
      rw [hdh]; exact deriv_sub a1 a2
    rw [hdd]
    have : deriv (A_eps_B p ε) (u1 y) * deriv u1 y - deriv (A_eps_B p ε) (u2 y) * deriv u2 y =
        deriv (A_eps_B p ε) (u1 y) * (deriv u1 y - deriv u2 y) +
          (deriv (A_eps_B p ε) (u1 y) - deriv (A_eps_B p ε) (u2 y)) * deriv u2 y := by ring
    rw [this, ← abs_mul, ← abs_mul]
    exact abs_add_le _ _
  have hdiff1 := c10_aux_ae_differentiableAt hu1L
  have hdiff2 := c10_aux_ae_differentiableAt hu2L
  have hhy : ∀ y, deriv h y = u1 y - u2 y := fun y => congrFun hdh y
  refine ⟨(hBL.comp hu1L).sub (hBL.comp hu2L), ae_of_all _ fun y hy => ?_,
    ae_of_all _ fun y hy => ?_, ?_, ?_⟩
  · have hρ := hjpos y (-beta p)
    have l := (c10_aux_B_lip p ε (CP * jb y ^ (-beta p)) hp hp1 hε hε1 (by positivity)
      (P1a y hy) (P2a y hy)).1
    rw [← hhy] at l
    have hH := H1 y hy
    have e : jb y ^ (-beta p) * jb y ^ (-γ + 1 / p) = jb y ^ (-beta p - γ + 1 / p) := by
      rw [← Real.rpow_add (c10_aux_jb_pos y)]; ring_nf
    calc _ ≤ (p + 1) * ε * (CP * jb y ^ (-beta p)) * |deriv h y| := l
      _ ≤ (p + 1) * ε * (CP * jb y ^ (-beta p)) * (xh * jb y ^ (-γ + 1 / p)) := by
          gcongr
          all_goals (apply_rules [mul_nonneg, add_nonneg, hjnn, abs_nonneg, hx, hε, hCP.le, hp1'.le,
            sq_nonneg, zero_le_one])
      _ = ((p + 1) * CP) * ε * xh * (jb y ^ (-beta p) * jb y ^ (-γ + 1 / p)) := by ring
      _ ≤ K * ε * xh * jb y ^ (-beta p - γ + 1 / p) := by
          rw [e]; gcongr
          all_goals (apply_rules [mul_nonneg, add_nonneg, hjnn, abs_nonneg, hx, hε, hCP.le, hp1'.le,
            sq_nonneg, zero_le_one])
  · have l := (c10_aux_B_lip p ε CP hp hp1 hε hε1 hCP (u1b y) (u2b y)).1
    rw [← hhy] at l
    have hH := H2 y hy
    calc _ ≤ (p + 1) * ε * CP * |deriv h y| := l
      _ ≤ (p + 1) * ε * CP * (xh * jb y ^ (-γ - 1)) := by
          gcongr
          all_goals (apply_rules [mul_nonneg, add_nonneg, hjnn, abs_nonneg, hx, hε, hCP.le, hp1'.le,
            sq_nonneg, zero_le_one])
      _ = ((p + 1) * CP) * ε * xh * jb y ^ (-γ - 1) := by ring
      _ ≤ K * ε * xh * jb y ^ (-γ - 1) := by
          gcongr
          all_goals (apply_rules [mul_nonneg, add_nonneg, hjnn, abs_nonneg, hx, hε, hCP.le, hp1'.le,
            sq_nonneg, zero_le_one])
  · filter_upwards [hdiff1, hdiff2, H3, P2b] with y a1 a2 h3 p2 hy
    have d := hderiv y a1 a2
    have b1 : |deriv (A_eps_B p ε) (u1 y)| ≤ (p + 1) * ε * (CP * jb y ^ (-beta p)) :=
      (c10_B_bounds p ε CP hp hp1 hε hε1 hCP _ (u1b y)).2.1.trans
        (mul_le_mul_of_nonneg_left (P1a y hy) (by positivity))
    have b2 := (c10_aux_B_lip p ε CP hp hp1 hε hε1 hCP (u1b y) (u2b y)).2
    rw [← hhy] at b2
    have hH := H1 y hy
    have hh3 := h3 hy
    have hp2 := p2 hy
    have e1 : jb y ^ (-beta p) * jb y ^ (-γ + 2 / p) = jb y ^ (-beta p - γ + 2 / p) := by
      rw [← Real.rpow_add (c10_aux_jb_pos y)]; ring_nf
    have e2 : jb y ^ (-γ + 1 / p) * jb y ^ (-beta p + 1 / p) = jb y ^ (-beta p - γ + 2 / p) := by
      rw [← Real.rpow_add (c10_aux_jb_pos y)]; ring_nf
    have := hjnn y (-beta p); have := hjnn y (-γ + 1 / p)
    calc _ ≤ _ := d
      _ ≤ (p + 1) * ε * (CP * jb y ^ (-beta p)) * (xh * jb y ^ (-γ + 2 / p)) +
          (p + 1) * (1 + CP ^ 2) * ε * (xh * jb y ^ (-γ + 1 / p)) * (CP * jb y ^ (-beta p + 1 / p)) := by
          gcongr
          all_goals first
            | exact b2.trans (mul_le_mul_of_nonneg_left hH (by positivity))
            | (apply_rules [mul_nonneg, add_nonneg, hjnn, abs_nonneg, hx, hε, hCP.le, hp1'.le,
                sq_nonneg, zero_le_one])
      _ = ((p + 1) * CP) * ε * xh * (jb y ^ (-beta p) * jb y ^ (-γ + 2 / p)) +
          ((p + 1) * (1 + CP ^ 2) * CP) * ε * xh * (jb y ^ (-γ + 1 / p) * jb y ^ (-beta p + 1 / p)) := by
          ring
      _ = K * ε * xh * jb y ^ (-beta p - γ + 2 / p) := by
          rw [e1, e2, hK]; ring
  · filter_upwards [hdiff1, hdiff2, H4, P2c] with y a1 a2 h4 p2 hy
    have d := hderiv y a1 a2
    have b1 : |deriv (A_eps_B p ε) (u1 y)| ≤ (p + 1) * ε * CP :=
      (c10_B_bounds p ε CP hp hp1 hε hε1 hCP _ (u1b y)).2.1.trans
        (mul_le_mul_of_nonneg_left (u1b y) (by positivity))
    have b2 := (c10_aux_B_lip p ε CP hp hp1 hε hε1 hCP (u1b y) (u2b y)).2
    rw [← hhy] at b2
    have hH := H2 y hy
    have hh4 := h4 hy
    have hp2 := p2 hy
    have e2 : jb y ^ (-γ - 1) * jb y ^ (-p - 2) ≤ jb y ^ (-γ - 2) := by
      rw [← Real.rpow_add (c10_aux_jb_pos y)]
      exact c10_aux_jb_rpow_mono y (by linarith)
    have := hjnn y (-γ - 1)
    calc _ ≤ _ := d
      _ ≤ (p + 1) * ε * CP * (xh * jb y ^ (-γ - 2)) +
          (p + 1) * (1 + CP ^ 2) * ε * (xh * jb y ^ (-γ - 1)) * (CP * jb y ^ (-p - 2)) := by
          gcongr
          all_goals first
            | exact b2.trans (mul_le_mul_of_nonneg_left hH (by positivity))
            | (apply_rules [mul_nonneg, add_nonneg, hjnn, abs_nonneg, hx, hε, hCP.le, hp1'.le,
                sq_nonneg, zero_le_one])
      _ = ((p + 1) * CP) * ε * xh * jb y ^ (-γ - 2) +
          ((p + 1) * (1 + CP ^ 2) * CP) * ε * xh * (jb y ^ (-γ - 1) * jb y ^ (-p - 2)) := by ring
      _ ≤ ((p + 1) * CP) * ε * xh * jb y ^ (-γ - 2) +
          ((p + 1) * (1 + CP ^ 2) * CP) * ε * xh * jb y ^ (-γ - 2) := by
          gcongr
          all_goals (apply_rules [mul_nonneg, add_nonneg, hjnn, abs_nonneg, hx, hε, hCP.le, hp1'.le,
            sq_nonneg, zero_le_one])
      _ = K * ε * xh * jb y ^ (-γ - 2) := by rw [hK]; ring

/-- Helper: product of two weighted bounds. -/
theorem c10_aux_prod_bound {X Y a b y e₁ e₂ e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : |X| ≤ a * jb y ^ e₁) (hY : |Y| ≤ b * jb y ^ e₂) (he : e₁ + e₂ ≤ e) :
    |X * Y| ≤ a * b * jb y ^ e := by
  rw [abs_mul]
  have hj := c10_aux_jb_pos y
  calc |X| * |Y| ≤ (a * jb y ^ e₁) * (b * jb y ^ e₂) :=
        mul_le_mul hX hY (abs_nonneg _) (mul_nonneg ha (Real.rpow_nonneg hj.le _))
    _ = a * b * jb y ^ (e₁ + e₂) := by rw [Real.rpow_add hj]; ring
    _ ≤ a * b * jb y ^ e :=
        mul_le_mul_of_nonneg_left (c10_aux_jb_rpow_mono y he) (mul_nonneg ha hb)

/-- Helper: `2β = 1 + 1/p`. -/
theorem c10_aux_two_beta (p : ℝ) (hp : 0 < p) : 2 * beta p = 1 + 1 / p := by
  unfold beta; field_simp

/-- Helper: the transport factor `f̄ - y f̄'` of an admissible profile is `C¹`. -/
theorem c10_aux_transport_C1 {fbar : ℝ → ℝ} (h2 : ContDiff ℝ 2 fbar) :
    ContDiff ℝ 1 (fun x => fbar x - x * deriv fbar x) := by
  have : ContDiff ℝ 1 (deriv fbar) := ((contDiff_succ_iff_deriv (n := 1)).1 h2).2.2
  exact (h2.of_le (by norm_num)).sub (contDiff_id.mul this)

/-- Blueprint: lem:N1.  `‖𝒩₁(r₁) - 𝒩₁(r₂)‖_{Y_γ} ≤ C ε ‖r₁ - r₂‖_{X_γ}`, `C = C(p,γ,M,N)`. -/
theorem N1 (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r₁ ∈ X_gamma p γ, ∀ r₂ ∈ X_gamma p γ, xNorm p γ r₁ ≤ N → xNorm p γ r₂ ≤ N →
      (fun y => c10_N_pieces_N1 p ε fbar r₁ y - c10_N_pieces_N1 p ε fbar r₂ y) ∈ Y_gamma p γ ∧
      yNorm p γ (fun y => c10_N_pieces_N1 p ε fbar r₁ y - c10_N_pieces_N1 p ε fbar r₂ y) ≤
        C * ε * xNorm p γ (r₁ - r₂) := by
  obtain ⟨hp0, -, -, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  have h2β := c10_aux_two_beta p hp0
  have h2p : 2 / p = 2 * (1 / p) := by ring
  obtain ⟨CD, hCD, hD⟩ := c10_delta_B p γ M N hp hp1 hγ hM hN
  obtain ⟨CT, hCT, hT⟩ := c10_transport_factors p γ M hp hp1 hγ hM
  refine ⟨8 * CD * CT, by positivity, fun ε hε hε1 fbar hf r₁ hr₁ r₂ hr₂ hN₁ hN₂ => ?_⟩
  obtain ⟨DW, D1, D2, D3, D4⟩ := hD ε hε hε1 fbar hf r₁ hr₁ r₂ hr₂ hN₁ hN₂
  obtain ⟨T1, T2, T3, T4, T5, -⟩ := hT fbar hf
  set xh := xNorm p γ (r₁ - r₂)
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  set ΔB : ℝ → ℝ := fun y => A_eps_B p ε (deriv fbar y + deriv r₁ y) -
    A_eps_B p ε (deriv fbar y + deriv r₂ y) with hΔB
  set T : ℝ → ℝ := fun x => fbar x - x * deriv fbar x with hTdef
  have hG : (fun y => c10_N_pieces_N1 p ε fbar r₁ y - c10_N_pieces_N1 p ε fbar r₂ y) =
      fun y => ΔB y * T y := by
    funext y; simp only [c10_N_pieces_N1, hΔB, hTdef]; ring
  rw [hG]
  have hTC := c10_aux_transport_C1 hf.1
  have hTd : ∀ y, DifferentiableAt ℝ T y := fun y => hTC.differentiable (by norm_num) y
  have hderiv : ∀ y, DifferentiableAt ℝ ΔB y →
      deriv (fun y => ΔB y * T y) y = deriv ΔB y * T y + ΔB y * (-(y * deriv (deriv fbar) y)) := by
    intro y hy
    have h3 : HasDerivAt (fun y => ΔB y * T y) _ y := hy.hasDerivAt.mul (hTd y).hasDerivAt
    rw [h3.deriv]
    have h4 : deriv T y = -(y * deriv (deriv fbar) y) := T3 y
    rw [h4]
  have hdiff := c10_aux_ae_differentiableAt DW
  set A := 2 * CD * CT * ε * xh with hA
  have hA0 : 0 ≤ A := by positivity
  have hCDe : 0 ≤ CD * ε * xh := by positivity
  have hle : yNorm p γ (fun y => ΔB y * T y) ≤ 4 * A ∧
      (fun y => ΔB y * T y) ∈ Y_gamma p γ := by
    have := c10_aux_Y_of_decay p γ A (c10_aux_locLip_mul DW hTC.locallyLipschitz) hA0
      (by
        filter_upwards [D1, D3, hdiff] with y d1 d3 hdy hy
        have d1 := d1 hy; have d3 := d3 hy
        refine ⟨?_, ?_⟩
        · have := c10_aux_prod_bound hCDe hCT.le d1 (T1 y hy)
            (show -beta p - γ + 1 / p + (1 - beta p) ≤ -γ by linarith)
          calc _ ≤ _ := this
            _ ≤ A * jb y ^ (-γ) := by
                apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (c10_aux_jb_pos y).le _)
                rw [hA]; nlinarith
        · rw [hderiv y hdy]
          have a := c10_aux_prod_bound hCDe hCT.le d3 (T1 y hy)
            (show -beta p - γ + 2 / p + (1 - beta p) ≤ -γ + 1 / p by linarith)
          have b := c10_aux_prod_bound hCDe hCT.le d1 (by rw [abs_neg]; exact T4 y hy)
            (show -beta p - γ + 1 / p + (1 - beta p + 1 / p) ≤ -γ + 1 / p by linarith)
          calc _ ≤ |deriv ΔB y * T y| + |ΔB y * -(y * deriv (deriv fbar) y)| := abs_add_le _ _
            _ ≤ CD * ε * xh * CT * jb y ^ (-γ + 1 / p) + CD * ε * xh * CT * jb y ^ (-γ + 1 / p) :=
                add_le_add a b
            _ = A * jb y ^ (-γ + 1 / p) := by rw [hA]; ring)
      (by
        filter_upwards [D2, D4, hdiff] with y d2 d4 hdy hy
        have d2 := d2 hy; have d4 := d4 hy
        refine ⟨?_, ?_⟩
        · have := c10_aux_prod_bound hCDe hCT.le d2 (T2 y hy)
            (show -γ - 1 + -p ≤ -γ by linarith)
          calc _ ≤ _ := this
            _ ≤ A * jb y ^ (-γ) := by
                apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (c10_aux_jb_pos y).le _)
                rw [hA]; nlinarith
        · rw [hderiv y hdy]
          have a := c10_aux_prod_bound hCDe hCT.le d4 (T2 y hy)
            (show -γ - 2 + -p ≤ -γ - 1 by linarith)
          have b := c10_aux_prod_bound hCDe hCT.le d2 (by rw [abs_neg]; exact T5 y hy)
            (show -γ - 1 + (-p - 1) ≤ -γ - 1 by linarith)
          calc _ ≤ |deriv ΔB y * T y| + |ΔB y * -(y * deriv (deriv fbar) y)| := abs_add_le _ _
            _ ≤ CD * ε * xh * CT * jb y ^ (-γ - 1) + CD * ε * xh * CT * jb y ^ (-γ - 1) :=
                add_le_add a b
            _ = A * jb y ^ (-γ - 1) := by rw [hA]; ring)
    exact ⟨this.2, this.1⟩
  refine ⟨hle.2, hle.1.trans (le_of_eq ?_)⟩
  rw [hA]; ring

/-- Blueprint: lem:c10_N2_coefficient.  Bounds for `B_ε(f̄'+r') - 1` and its derivative. -/
theorem c10_N2_coefficient (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N →
      (∀ᵐ y, 0 ≤ y → |A_eps_B p ε (deriv fbar y + deriv r y) - 1| ≤
          C * ε * jb y ^ (-2 * beta p)) ∧
      (∀ᵐ y, y ≤ 0 → |A_eps_B p ε (deriv fbar y + deriv r y) - 1| ≤ C * ε) ∧
      (∀ᵐ y, 0 ≤ y → |deriv (fun x => A_eps_B p ε (deriv fbar x + deriv r x) - 1) y| ≤
          C * ε * jb y ^ (-2 * beta p + 1 / p)) ∧
      (∀ᵐ y, y ≤ 0 → |deriv (fun x => A_eps_B p ε (deriv fbar x + deriv r x) - 1) y| ≤
          C * ε * jb y ^ (-p - 2)) := by
  obtain ⟨hp0, -, -, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨CP, hCP, hPC⟩ := c10_profile_consequences p γ M N hp hp1 hγ hM hN
  set K := (p + 1) * CP ^ 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K, hKpos, fun ε hε hε1 fbar hf r hr hrN => ?_⟩
  obtain ⟨i1, i2a, i2b, i3a, i3b, -⟩ := hPC fbar hf r hr hrN
  obtain ⟨u0, -, -, -⟩ := i1 (fbar + r) (by simp)
  have hdf : Differentiable ℝ fbar := hf.1.differentiable (by norm_num)
  have hdr : Differentiable ℝ r := hr.1.1.differentiable (by norm_num)
  have hu : (fun x => deriv fbar x + deriv r x) = deriv (fbar + r) :=
    funext fun x => (deriv_add (hdf x) (hdr x)).symm
  have hfA := c10_aux_C2_admissible_class hf.1 (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have huL : LocallyLipschitz (deriv (fbar + r)) := by
    rw [← hu]; exact hfA.2.2.add hr.1.2
  have hdiff := c10_aux_ae_differentiableAt huL
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e =>
    (Real.rpow_pos_of_pos (c10_aux_jb_pos y) e).le
  have hp1' : 0 < p + 1 := by linarith
  -- value bound: `|B(u) - 1| ≤ (α/2) ε u²`
  have hval : ∀ y, |A_eps_B p ε (deriv fbar y + deriv r y) - 1| ≤
      (p + 1) * ε * (deriv (fbar + r) y) ^ 2 := by
    intro y
    have hy : deriv fbar y + deriv r y = deriv (fbar + r) y := congrFun hu y
    rw [hy]
    have := (c10_B_bounds p ε CP hp hp1 hε hε1 hCP _ (u0 y)).1
    have : 0 ≤ ε * (deriv (fbar + r) y) ^ 2 := by positivity
    nlinarith
  -- derivative formula
  have hder : ∀ y, DifferentiableAt ℝ (deriv (fbar + r)) y →
      |deriv (fun x => A_eps_B p ε (deriv fbar x + deriv r x) - 1) y| ≤
        (p + 1) * ε * |deriv (fbar + r) y| * |deriv (deriv (fbar + r)) y| := by
    intro y hy
    have e : (fun x => A_eps_B p ε (deriv fbar x + deriv r x) - 1) =
        fun x => A_eps_B p ε (deriv (fbar + r) x) - 1 := by rw [← hu]
    rw [e, deriv_sub_const, c10_aux_B_comp_deriv p ε hε hy, abs_mul]
    exact mul_le_mul_of_nonneg_right (c10_B_bounds p ε CP hp hp1 hε hε1 hCP _ (u0 y)).2.1
      (abs_nonneg _)
  refine ⟨ae_of_all _ fun y hy => ?_, ae_of_all _ fun y hy => ?_, ?_, ?_⟩
  · have h1 := i2a y hy
    have h2 : (deriv (fbar + r) y) ^ 2 ≤ (CP * jb y ^ (-beta p)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have e : (CP * jb y ^ (-beta p)) ^ 2 = CP ^ 2 * jb y ^ (-2 * beta p) := by
      have : (jb y ^ (-beta p)) ^ 2 = jb y ^ (-2 * beta p) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (c10_aux_jb_pos y).le]; norm_num; ring_nf
      rw [mul_pow, this]
    rw [e] at h2
    have := hval y
    have hK' : (p + 1) * CP ^ 2 ≤ K := by linarith
    calc _ ≤ (p + 1) * ε * (CP ^ 2 * jb y ^ (-2 * beta p)) :=
          this.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = ((p + 1) * CP ^ 2) * ε * jb y ^ (-2 * beta p) := by ring
      _ ≤ K * ε * jb y ^ (-2 * beta p) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK' hε) (hjnn _ _)
  · have h2 : (deriv (fbar + r) y) ^ 2 ≤ CP ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (u0 y) 2
    have := hval y
    calc _ ≤ (p + 1) * ε * CP ^ 2 := this.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ ≤ K * ε := by nlinarith
  · filter_upwards [hdiff, i2b] with y hy h2 hy0
    have h1 := i2a y hy0
    have h2 := h2 hy0
    have := hder y hy
    have e : jb y ^ (-beta p) * jb y ^ (-beta p + 1 / p) = jb y ^ (-2 * beta p + 1 / p) := by
      rw [← Real.rpow_add (c10_aux_jb_pos y)]; ring_nf
    calc _ ≤ (p + 1) * ε * |deriv (fbar + r) y| * |deriv (deriv (fbar + r)) y| := this
      _ ≤ (p + 1) * ε * (CP * jb y ^ (-beta p)) * (CP * jb y ^ (-beta p + 1 / p)) := by
          have := hjnn y (-beta p)
          have : 0 ≤ (p + 1) * ε * (CP * jb y ^ (-beta p)) := by positivity
          gcongr
      _ = ((p + 1) * CP ^ 2) * ε * (jb y ^ (-beta p) * jb y ^ (-beta p + 1 / p)) := by ring
      _ ≤ K * ε * jb y ^ (-2 * beta p + 1 / p) := by
          rw [e]
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε) (hjnn _ _)
  · filter_upwards [hdiff, i3b] with y hy h2 hy0
    have h1 := u0 y
    have h2 := h2 hy0
    have := hder y hy
    calc _ ≤ (p + 1) * ε * |deriv (fbar + r) y| * |deriv (deriv (fbar + r)) y| := this
      _ ≤ (p + 1) * ε * CP * (CP * jb y ^ (-p - 2)) := by gcongr
      _ = ((p + 1) * CP ^ 2) * ε * jb y ^ (-p - 2) := by ring
      _ ≤ K * ε * jb y ^ (-p - 2) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε) (hjnn _ _)


/-- Helper: the transport factor `r - y r'` of `r ∈ X_γ` is locally Lipschitz. -/
theorem c10_aux_transport_locLip {r : ℝ → ℝ} (hr : W2inftyLoc r) :
    LocallyLipschitz (fun x => r x - x * deriv r x) := by
  have h1 : LocallyLipschitz r := hr.1.locallyLipschitz
  have h2 : LocallyLipschitz (fun x : ℝ => x) := LipschitzWith.id.locallyLipschitz
  exact h1.sub (c10_aux_locLip_mul h2 hr.2)

/-- Blueprint: lem:N2.  `‖𝒩₂(r₁) - 𝒩₂(r₂)‖_{Y_γ} ≤ C ε ‖r₁ - r₂‖_{X_γ}`, `C = C(p,γ,M,N)`. -/
theorem N2 (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r₁ ∈ X_gamma p γ, ∀ r₂ ∈ X_gamma p γ, xNorm p γ r₁ ≤ N → xNorm p γ r₂ ≤ N →
      (fun y => c10_N_pieces_N2 p ε fbar r₁ y - c10_N_pieces_N2 p ε fbar r₂ y) ∈ Y_gamma p γ ∧
      yNorm p γ (fun y => c10_N_pieces_N2 p ε fbar r₁ y - c10_N_pieces_N2 p ε fbar r₂ y) ≤
        C * ε * xNorm p γ (r₁ - r₂) := by
  obtain ⟨hp0, -, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  have h2β := c10_aux_two_beta p hp0
  have h2p : 2 / p = 2 * (1 / p) := by ring
  have hβγ := hγ.1
  obtain ⟨Cc, hCc, hcoef⟩ := c10_N2_coefficient p γ M N hp hp1 hγ hM hN
  obtain ⟨CD, hCD, hD⟩ := c10_delta_B p γ M N hp hp1 hγ hM hN
  obtain ⟨CT, hCT, hT⟩ := c10_transport_factors p γ M hp hp1 hγ hM
  refine ⟨12 * (Cc + CD * N), by positivity,
    fun ε hε hε1 fbar hf r₁ hr₁ r₂ hr₂ hN₁ hN₂ => ?_⟩
  have hh := c10_aux_X_sub p γ hr₁ hr₂
  obtain ⟨DW, D1, D2, D3, D4⟩ := hD ε hε hε1 fbar hf r₁ hr₁ r₂ hr₂ hN₁ hN₂
  obtain ⟨c1, c2, c3, c4⟩ := hcoef ε hε hε1 fbar hf r₁ hr₁ hN₁
  obtain ⟨-, -, -, -, -, hTr⟩ := hT fbar hf
  obtain ⟨Q1, Q2, Q3, Q4, Q5⟩ := hTr _ hh
  obtain ⟨S1, S2', S3, S4, S5⟩ := hTr _ hr₂
  set h := r₁ - r₂ with hhdef
  set xh := xNorm p γ h
  set x2 := xNorm p γ r₂
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  have hx2 : 0 ≤ x2 := ENNReal.toReal_nonneg
  have hd1 : Differentiable ℝ r₁ := hr₁.1.1.differentiable (by norm_num)
  have hd2 : Differentiable ℝ r₂ := hr₂.1.1.differentiable (by norm_num)
  have hdh : ∀ y, deriv h y = deriv r₁ y - deriv r₂ y := fun y => deriv_sub (hd1 y) (hd2 y)
  set Bm : ℝ → ℝ := fun x => A_eps_B p ε (deriv fbar x + deriv r₁ x) - 1 with hBm
  set ΔB : ℝ → ℝ := fun y => A_eps_B p ε (deriv fbar y + deriv r₁ y) -
    A_eps_B p ε (deriv fbar y + deriv r₂ y) with hΔB
  set Q : ℝ → ℝ := fun x => h x - x * deriv h x with hQ
  set S : ℝ → ℝ := fun x => r₂ x - x * deriv r₂ x with hS
  have hG : (fun y => c10_N_pieces_N2 p ε fbar r₁ y - c10_N_pieces_N2 p ε fbar r₂ y) =
      fun y => Bm y * Q y + ΔB y * S y := by
    funext y; simp only [c10_N_pieces_N2, hBm, hΔB, hQ, hS, hdh]
    simp only [hhdef, Pi.sub_apply]; ring
  rw [hG]
  -- local Lipschitz properties
  have hfA := c10_aux_C2_admissible_class hf.1
    (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have hBL : LocallyLipschitz (A_eps_B p ε) := (c10_aux_B_contDiff p ε hε).locallyLipschitz
  have hBmL : LocallyLipschitz Bm := by
    have : LocallyLipschitz (fun x => deriv fbar x + deriv r₁ x) := hfA.2.2.add hr₁.1.2
    exact (hBL.comp this).sub (LocallyLipschitz.const _)
  have hQL : LocallyLipschitz Q := c10_aux_transport_locLip hh.1
  have hSL : LocallyLipschitz S := c10_aux_transport_locLip hr₂.1
  have hW : W1inftyLoc (fun y => Bm y * Q y + ΔB y * S y) :=
    (c10_aux_locLip_mul hBmL hQL).add (c10_aux_locLip_mul DW hSL)
  have hderiv : ∀ y, DifferentiableAt ℝ Bm y → DifferentiableAt ℝ Q y →
      DifferentiableAt ℝ ΔB y → DifferentiableAt ℝ S y →
      deriv (fun y => Bm y * Q y + ΔB y * S y) y =
        deriv Bm y * Q y + Bm y * deriv Q y + (deriv ΔB y * S y + ΔB y * deriv S y) := by
    intro y a b c d
    have e : HasDerivAt (fun y => Bm y * Q y + ΔB y * S y) _ y :=
      (a.hasDerivAt.mul b.hasDerivAt).add (c.hasDerivAt.mul d.hasDerivAt)
    exact e.deriv
  have hd := fun {g : ℝ → ℝ} (hg : LocallyLipschitz g) => c10_aux_ae_differentiableAt hg
  set A := 3 * (Cc + CD * N) * ε * xh with hA
  have hA0 : 0 ≤ A := by positivity
  have hCce : 0 ≤ Cc * ε := by positivity
  have hCDe : 0 ≤ CD * ε * xh := by positivity
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e =>
    (Real.rpow_pos_of_pos (c10_aux_jb_pos y) e).le
  have hNx : 2 * x2 ≤ 2 * N := by linarith
  have key := c10_aux_Y_of_decay p γ A hW hA0
    (by
      filter_upwards [c1, c3, D1, D3, Q4, S4, Q3, S3, hd hBmL, hd hQL, hd DW, hd hSL]
        with y c1 c3 d1 d3 q4 s4 q3 s3 a b c d hy
      have c1 := c1 hy; have c3 := c3 hy; have d1 := d1 hy; have d3 := d3 hy
      have q4 := q4 hy; have s4 := s4 hy
      have s1 : |S y| ≤ (2 * N) * jb y ^ (1 - γ + 1 / p) :=
        (S1 y hy).trans (mul_le_mul_of_nonneg_right hNx (hjnn _ _))
      have s4' : |y * deriv (deriv r₂) y| ≤ N * jb y ^ (1 - γ + 2 / p) :=
        s4.trans (mul_le_mul_of_nonneg_right hN₂ (hjnn _ _))
      refine ⟨?_, ?_⟩
      · have e1 := c10_aux_prod_bound hCce (by positivity) c1 (Q1 y hy)
          (show -2 * beta p + (1 - γ + 1 / p) ≤ -γ by linarith)
        have e2 := c10_aux_prod_bound hCDe (by positivity) d1 s1
          (show -beta p - γ + 1 / p + (1 - γ + 1 / p) ≤ -γ by linarith)
        calc _ ≤ |Bm y * Q y| + |ΔB y * S y| := abs_add_le _ _
          _ ≤ Cc * ε * (2 * xh) * jb y ^ (-γ) + CD * ε * xh * (2 * N) * jb y ^ (-γ) :=
              add_le_add e1 e2
          _ ≤ A * jb y ^ (-γ) := by
              rw [hA]; have := hjnn y (-γ)
              nlinarith [mul_nonneg (mul_nonneg hCce hx) this,
                mul_nonneg (mul_nonneg (mul_nonneg hCD.le hε) hx) (mul_nonneg hN.le this)]
      · rw [hderiv y a b c d, q3, s3]
        have e1 := c10_aux_prod_bound hCce (by positivity) c3 (Q1 y hy)
          (show -2 * beta p + 1 / p + (1 - γ + 1 / p) ≤ -γ + 1 / p by linarith)
        have e2 := c10_aux_prod_bound hCce hx c1 (by rw [abs_neg]; exact q4)
          (show -2 * beta p + (1 - γ + 2 / p) ≤ -γ + 1 / p by linarith)
        have e3 := c10_aux_prod_bound hCDe (by positivity) d3 s1
          (show -beta p - γ + 2 / p + (1 - γ + 1 / p) ≤ -γ + 1 / p by linarith)
        have e4 := c10_aux_prod_bound hCDe hN.le d1 (by rw [abs_neg]; exact s4')
          (show -beta p - γ + 1 / p + (1 - γ + 2 / p) ≤ -γ + 1 / p by linarith)
        have := hjnn y (-γ + 1 / p)
        calc _ ≤ |deriv Bm y * Q y| + |Bm y * -(y * deriv (deriv h) y)| +
              (|deriv ΔB y * S y| + |ΔB y * -(y * deriv (deriv r₂) y)|) :=
              (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
          _ ≤ Cc * ε * (2 * xh) * jb y ^ (-γ + 1 / p) + Cc * ε * xh * jb y ^ (-γ + 1 / p) +
              (CD * ε * xh * (2 * N) * jb y ^ (-γ + 1 / p) + CD * ε * xh * N * jb y ^ (-γ + 1 / p)) :=
              add_le_add (add_le_add e1 e2) (add_le_add e3 e4)
          _ = A * jb y ^ (-γ + 1 / p) := by rw [hA]; ring)
    (by
      filter_upwards [c2, c4, D2, D4, Q5, S5, Q3, S3, hd hBmL, hd hQL, hd DW, hd hSL]
        with y c2 c4 d2 d4 q5 s5 q3 s3 a b c d hy
      have c2 := c2 hy; have c4 := c4 hy; have d2 := d2 hy; have d4 := d4 hy
      have q5 := q5 hy; have s5 := s5 hy
      have c2' : |Bm y| ≤ Cc * ε * jb y ^ (0 : ℝ) := by rw [Real.rpow_zero, mul_one]; exact c2
      have s2 : |S y| ≤ (2 * N) * jb y ^ (-γ) :=
        (S2' y hy).trans (mul_le_mul_of_nonneg_right hNx (hjnn _ _))
      have s5' : |y * deriv (deriv r₂) y| ≤ N * jb y ^ (-γ - 1) :=
        s5.trans (mul_le_mul_of_nonneg_right hN₂ (hjnn _ _))
      refine ⟨?_, ?_⟩
      · have e1 := c10_aux_prod_bound hCce (by positivity) c2' (Q2 y hy)
          (show (0 : ℝ) + -γ ≤ -γ by linarith)
        have e2 := c10_aux_prod_bound hCDe (by positivity) d2 s2
          (show -γ - 1 + -γ ≤ -γ by linarith)
        calc _ ≤ |Bm y * Q y| + |ΔB y * S y| := abs_add_le _ _
          _ ≤ Cc * ε * (2 * xh) * jb y ^ (-γ) + CD * ε * xh * (2 * N) * jb y ^ (-γ) :=
              add_le_add e1 e2
          _ ≤ A * jb y ^ (-γ) := by
              rw [hA]; have := hjnn y (-γ)
              nlinarith [mul_nonneg (mul_nonneg hCce hx) this,
                mul_nonneg (mul_nonneg (mul_nonneg hCD.le hε) hx) (mul_nonneg hN.le this)]
      · rw [hderiv y a b c d, q3, s3]
        have e1 := c10_aux_prod_bound hCce (by positivity) c4 (Q2 y hy)
          (show -p - 2 + -γ ≤ -γ - 1 by linarith)
        have e2 := c10_aux_prod_bound hCce hx c2' (by rw [abs_neg]; exact q5)
          (show (0 : ℝ) + (-γ - 1) ≤ -γ - 1 by linarith)
        have e3 := c10_aux_prod_bound hCDe (by positivity) d4 s2
          (show -γ - 2 + -γ ≤ -γ - 1 by linarith)
        have e4 := c10_aux_prod_bound hCDe hN.le d2 (by rw [abs_neg]; exact s5')
          (show -γ - 1 + (-γ - 1) ≤ -γ - 1 by linarith)
        calc _ ≤ |deriv Bm y * Q y| + |Bm y * -(y * deriv (deriv h) y)| +
              (|deriv ΔB y * S y| + |ΔB y * -(y * deriv (deriv r₂) y)|) :=
              (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
          _ ≤ Cc * ε * (2 * xh) * jb y ^ (-γ - 1) + Cc * ε * xh * jb y ^ (-γ - 1) +
              (CD * ε * xh * (2 * N) * jb y ^ (-γ - 1) + CD * ε * xh * N * jb y ^ (-γ - 1)) :=
              add_le_add (add_le_add e1 e2) (add_le_add e3 e4)
          _ = A * jb y ^ (-γ - 1) := by rw [hA]; ring)
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  rw [hA]; ring

/-! ### The nonlocal piece `𝒩₃`: linearization -/

/-- Blueprint: def:c10_N3_linearization (helper).  The integrand (for the profile `f = f̄ + r`)
`K_{f,h}(y,z) = ∂₁Γ_ε(f'(y),S_f(y,z)) h'(y) + ∂₂Γ_ε(f'(y),S_f(y,z)) S_h(y,z)`. -/
def c10_N3_linearization_K (p ε : ℝ) (f h : ℝ → ℝ) (y z : ℝ) : ℝ :=
  c10_N_pieces_Gamma_d1 p ε (deriv f y) (c01_secant f y z) * deriv h y +
    c10_N_pieces_Gamma_d2 p ε (deriv f y) (c01_secant f y z) * c01_secant h y z

/-- Blueprint: def:c10_N3_linearization (helper).  The `y`-derivative integrand
`∂_y K_{f,h}(y,z) - α K_{f,h}(y,z)/(y-z)` (`∂_y` with `z` fixed). -/
def c10_N3_linearization_dK (p ε : ℝ) (f h : ℝ → ℝ) (y z : ℝ) : ℝ :=
  deriv (fun y' => c10_N3_linearization_K p ε f h y' z) y -
    (p + 1) * c10_N3_linearization_K p ε f h y z / (y - z)

/-- Blueprint: def:c10_N3_linearization.
`D𝒩₃(r)[h](y) = ∫ K_{f̄+r,h}(y,z) |y-z|^{-α} dz - b_ε(y) h'(y)`. -/
def c10_N3_linearization (p ε : ℝ) (fbar r h : ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫ z, c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
    b_eps p ε y * deriv h y

/-- Helper: an a.e. bound `|φ'| ≤ L` on `[a,b]` for a locally Lipschitz `φ` gives
`|φ(b) - φ(a)| ≤ L|b-a|` (FTC for absolutely continuous functions). -/
theorem c10_aux_lip_of_ae_deriv {φ : ℝ → ℝ} (hφ : LocallyLipschitz φ) {a b L : ℝ}
    (h : ∀ᵐ w, w ∈ uIcc a b → |deriv φ w| ≤ L) : |φ b - φ a| ≤ L * |b - a| := by
  obtain ⟨K, hK⟩ := (hφ.locallyLipschitzOn (s := uIcc a b)).exists_lipschitzOnWith_of_compact
    isCompact_uIcc
  have hAC := hK.absolutelyContinuousOnInterval
  rw [← hAC.integral_deriv_eq_sub]
  have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b) (C := L)
    (f := deriv φ) (by
      filter_upwards [h] with w hw hw'
      rw [Real.norm_eq_abs]; exact hw (uIoc_subset_uIcc hw'))
  rwa [Real.norm_eq_abs] at this

/-- Helper: mean value theorem for the secant: `S_g(y,z) = g'(ξ)` for some `ξ ∈ [y,z]`. -/
theorem c10_aux_secant_mvt {g : ℝ → ℝ} (hg : Differentiable ℝ g) {y z : ℝ} (hyz : y ≠ z) :
    ∃ ξ ∈ uIcc y z, deriv g ξ = c01_secant g y z := by
  rw [c01_secant, if_neg hyz]
  rcases lt_or_gt_of_ne hyz with h | h
  · obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope g h hg.continuous.continuousOn
      (fun x _ => (hg x).differentiableWithinAt)
    refine ⟨c, Ioo_subset_Icc_self.trans Icc_subset_uIcc hc, ?_⟩
    rw [hc', div_eq_div_iff (by linarith) (by linarith)]; ring
  · obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope g h hg.continuous.continuousOn
      (fun x _ => (hg x).differentiableWithinAt)
    exact ⟨c, Ioo_subset_Icc_self.trans Icc_subset_uIcc' hc, hc'⟩

/-- Blueprint: lem:c10_secant_identities.  For `g ∈ W^{2,∞}_loc`, `y ≠ z`: the integral formula
for `S_g`, the derivative `∂_y S_g = (g'(y) - S_g)/(y-z)` (`C¹` off the diagonal), and the bounds
(with `L ≥ ‖g''‖_{L^∞(I_{y,z})}`, `L' ≥ ‖g'‖_{L^∞}`). -/
theorem c10_secant_identities (g : ℝ → ℝ) (hg : W2inftyLoc g) (y z : ℝ) (hyz : y ≠ z) :
    c01_secant g y z = ∫ t in (0 : ℝ)..1, deriv g (z + t * (y - z)) ∧
    ContDiffOn ℝ 1 (fun y' => c01_secant g y' z) {z}ᶜ ∧
    HasDerivAt (fun y' => c01_secant g y' z) ((deriv g y - c01_secant g y z) / (y - z)) y ∧
    (∀ L : ℝ, (∀ᵐ w, w ∈ uIcc y z → |deriv (deriv g) w| ≤ L) →
      |deriv g y - c01_secant g y z| ≤ |y - z| * L ∧
      |deriv (fun y' => c01_secant g y' z) y| ≤ L) ∧
    (∀ L' : ℝ, (∀ w, |deriv g w| ≤ L') →
      |deriv (fun y' => c01_secant g y' z) y| ≤ 2 * L' / |y - z| ∧
      |c01_secant g y z| ≤ min L' ((|g y| + |g z|) / |y - z|)) := by
  have hd : Differentiable ℝ g := hg.1.differentiable (by norm_num)
  have hc' : Continuous (deriv g) := hg.2.continuous
  have hyz' : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hS : c01_secant g y z = (g y - g z) / (y - z) := by rw [c01_secant, if_neg hyz]
  -- the quotient form on `{z}ᶜ`
  set q : ℝ → ℝ := fun y' => (g y' - g z) / (y' - z) with hq
  have hEq : ∀ y' ∈ ({z}ᶜ : Set ℝ), c01_secant g y' z = q y' := fun y' hy' => by
    rw [c01_secant, if_neg (mem_compl_singleton_iff.1 hy')]
  have hqd0 : HasDerivAt q ((deriv g y * (y - z) - (g y - g z) * 1) / (y - z) ^ 2) y := by
    have := ((hd y).hasDerivAt.sub_const (g z)).div ((hasDerivAt_id' y).sub_const z) hyz'
    exact this
  have hqd : HasDerivAt q ((deriv g y - c01_secant g y z) / (y - z)) y := by
    convert hqd0 using 1
    rw [hS]; field_simp
  have hev : (fun y' => c01_secant g y' z) =ᶠ[nhds y] q :=
    Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds hyz) hEq
  have hder : HasDerivAt (fun y' => c01_secant g y' z)
      ((deriv g y - c01_secant g y z) / (y - z)) y := hqd.congr_of_eventuallyEq hev
  have hderiv : deriv (fun y' => c01_secant g y' z) y = (deriv g y - c01_secant g y z) / (y - z) :=
    hder.deriv
  have hpos : 0 < |y - z| := abs_pos.2 hyz'
  refine ⟨?_, ?_, hder, fun L hL => ?_, fun L' hL' => ?_⟩
  · -- integral formula
    have h1 := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (deriv g) hyz' z
    have h2 : (∫ x in (y - z) * 0 + z..(y - z) * 1 + z, deriv g x) = g y - g z := by
      simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hd x).hasDerivAt)
        (hc'.intervalIntegrable _ _)
    have h3 : (∫ t in (0 : ℝ)..1, deriv g (z + t * (y - z))) =
        ∫ t in (0 : ℝ)..1, deriv g ((y - z) * t + z) := by
      congr 1; funext t; ring_nf
    rw [h3, h1, h2, hS, smul_eq_mul]; field_simp
  · exact ContDiffOn.congr (((hg.1.sub contDiff_const).contDiffOn).div
      ((contDiff_id.sub contDiff_const).contDiffOn) fun x hx => sub_ne_zero.2 hx) hEq
  · obtain ⟨ξ, hξ, hξe⟩ := c10_aux_secant_mvt hd hyz
    have hsub : uIcc ξ y ⊆ uIcc y z := uIcc_subset_uIcc hξ left_mem_uIcc
    have hL1 := c10_aux_lip_of_ae_deriv hg.2 (a := ξ) (b := y) (L := L)
      (by filter_upwards [hL] with w hw hw' using hw (hsub hw'))
    have hyξ : |y - ξ| ≤ |y - z| := by
      rcases le_total y z with h | h
      · rw [uIcc_of_le h] at hξ
        rw [abs_of_nonpos (by linarith [hξ.1]), abs_of_nonpos (by linarith)]; linarith [hξ.2]
      · rw [uIcc_of_ge h] at hξ
        rw [abs_of_nonneg (by linarith [hξ.2]), abs_of_nonneg (by linarith)]; linarith [hξ.1]
    have hL0 : 0 ≤ L := by
      by_contra hneg
      push_neg at hneg
      have hnull : ∀ᵐ w, w ∉ uIcc y z := by
        filter_upwards [hL] with w hw hw'
        exact absurd ((abs_nonneg _).trans (hw hw')) (not_le.2 hneg)
      have h0 := measure_eq_zero_iff_ae_notMem.2 hnull
      rw [Real.volume_interval, ENNReal.ofReal_eq_zero] at h0
      have : 0 < |z - y| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hyz))
      linarith
    have e1 : |deriv g y - c01_secant g y z| ≤ |y - z| * L := by
      rw [← hξe, abs_sub_comm]
      calc |deriv g ξ - deriv g y| = |deriv g y - deriv g ξ| := abs_sub_comm _ _
        _ ≤ L * |y - ξ| := hL1
        _ ≤ L * |y - z| := mul_le_mul_of_nonneg_left hyξ hL0
        _ = |y - z| * L := mul_comm _ _
    refine ⟨e1, ?_⟩
    rw [hderiv, abs_div, div_le_iff₀ hpos]; linarith
  · obtain ⟨ξ, -, hξe⟩ := c10_aux_secant_mvt hd hyz
    have hS1 : |c01_secant g y z| ≤ L' := hξe ▸ hL' ξ
    refine ⟨?_, le_min hS1 ?_⟩
    · rw [hderiv, abs_div, div_le_div_iff_of_pos_right hpos]
      have := abs_sub (deriv g y) (c01_secant g y z)
      linarith [hL' y]
    · rw [hS, abs_div]
      exact div_le_div_of_nonneg_right (abs_sub _ _) hpos.le

/-! ### Elementary integrals -/

/-- Helper: integrability of `x ↦ f |x|` from integrability of `f` on `(0,∞)`. -/
theorem c10_aux_integrable_comp_abs {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos (show (0:ℝ) < x from hx)]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  have := int_Iic.union hf'
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- Helper: integrals of radial functions over radial sets. -/
theorem c10_aux_radial {g : ℝ → ℝ} {S T : Set ℝ} (hT : MeasurableSet T)
    (hS : ∀ ρ, ρ ∈ S ↔ |ρ| ∈ T) (hg : IntegrableOn g (Ioi 0 ∩ T)) :
    IntegrableOn (fun ρ => g |ρ|) S ∧
      ∫ ρ in S, g |ρ| = 2 * ∫ t in Ioi 0 ∩ T, g t := by
  have hSm : S = (fun ρ => |ρ|) ⁻¹' T := by ext ρ; exact hS ρ
  have hSm' : MeasurableSet S := hSm ▸ measurable_abs hT
  have hind : S.indicator (fun ρ => g |ρ|) = fun ρ => T.indicator g |ρ| := by
    funext ρ; by_cases h : ρ ∈ S
    · rw [indicator_of_mem h, indicator_of_mem ((hS ρ).1 h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h ((hS ρ).2 h'))]
  have hI : IntegrableOn (T.indicator g) (Ioi 0) := by
    rw [IntegrableOn, integrable_indicator_iff hT, IntegrableOn, Measure.restrict_restrict hT,
      inter_comm]; exact hg
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff hSm', hind]; exact c10_aux_integrable_comp_abs hI
  · rw [← integral_indicator hSm', hind, integral_comp_abs (f := T.indicator g),
      setIntegral_indicator hT]

/-- Helper: `∫_{|ρ|≥a} |ρ|^{-q} = 2a^{1-q}/(q-1)`. -/
theorem c10_aux_tail (q a : ℝ) (hq : 1 < q) (ha : 0 < a) :
    IntegrableOn (fun ρ : ℝ => |ρ| ^ (-q)) {ρ | a ≤ |ρ|} ∧
      ∫ ρ in {ρ | a ≤ |ρ|}, |ρ| ^ (-q) = 2 / (q - 1) * a ^ (1 - q) := by
  have hT : Ioi (0:ℝ) ∩ Ici a = Ici a := inter_eq_right.2 (Ici_subset_Ioi.2 ha)
  have hi : IntegrableOn (fun t : ℝ => t ^ (-q)) (Ici a) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_Ioi_rpow_of_lt (by linarith) ha)
  obtain ⟨h1, h2⟩ := c10_aux_radial (g := fun t => t ^ (-q)) (S := {ρ | a ≤ |ρ|}) (T := Ici a)
    measurableSet_Ici (fun ρ => Iff.rfl) (by rw [hT]; exact hi)
  refine ⟨h1, ?_⟩
  rw [h2, hT, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) ha]
  have : 1 - q ≠ 0 := by linarith
  have : q - 1 ≠ 0 := by linarith
  rw [show -q + 1 = 1 - q by ring]
  field_simp
  ring

/-- Helper: `∫_{-a}^a |ρ|^s = 2a^{s+1}/(s+1)`. -/
theorem c10_aux_ball (s a : ℝ) (hs : -1 < s) (ha : 0 < a) :
    IntegrableOn (fun ρ : ℝ => |ρ| ^ s) (Icc (-a) a) ∧
      ∫ ρ in Icc (-a) a, |ρ| ^ s = 2 * a ^ (s + 1) / (s + 1) := by
  have hT : Ioi (0:ℝ) ∩ Iic a = Ioc 0 a := Ioi_inter_Iic
  have hi : IntegrableOn (fun t : ℝ => t ^ s) (Ioc 0 a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1 (intervalIntegral.intervalIntegrable_rpow' hs)
  obtain ⟨h1, h2⟩ := c10_aux_radial (g := fun t => t ^ s) (S := Icc (-a) a) (T := Iic a)
    measurableSet_Iic (fun ρ => by simp [abs_le]) (by rw [hT]; exact hi)
  refine ⟨h1, ?_⟩
  rw [h2, hT, ← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl hs),
    Real.zero_rpow (by linarith)]
  ring

/-- Helper: `∫_0^∞ min(1,t)^k t^{-1-p} dt = 1/(k-p) + 1/p`. -/
theorem c10_aux_minpow (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : 1 ≤ k) :
    IntegrableOn (fun t : ℝ => min 1 t ^ k / t ^ (1 + p)) (Ioi 0) ∧
      ∫ t in Ioi 0, min 1 t ^ k / t ^ (1 + p) = 1 / ((k:ℝ) - p) + 1 / p := by
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have e1 : EqOn (fun t : ℝ => min 1 t ^ k / t ^ (1 + p)) (fun t => t ^ ((k:ℝ) - (1 + p)))
      (Ioc 0 1) := fun t ht => by
    simp only
    rw [min_eq_right ht.2, Real.rpow_sub ht.1, Real.rpow_natCast]
  have e2 : EqOn (fun t : ℝ => min 1 t ^ k / t ^ (1 + p)) (fun t => t ^ (-(1 + p)))
      (Ioi 1) := fun t ht => by
    simp only
    rw [min_eq_left (le_of_lt ht), one_pow, Real.rpow_neg (by linarith [show (1:ℝ) < t from ht]),
      one_div]
  have i1 : IntegrableOn (fun t : ℝ => t ^ ((k:ℝ) - (1 + p))) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have i2 : IntegrableOn (fun t : ℝ => t ^ (-(1 + p))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have j1 := i1.congr_fun e1.symm measurableSet_Ioc
  have j2 := i2.congr_fun e2.symm measurableSet_Ioi
  have hU : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  refine ⟨hU ▸ j1.union j2, ?_⟩
  rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi j1 j2,
    setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
    ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith)),
    integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
  rw [Real.zero_rpow (by linarith), Real.one_rpow, Real.one_rpow]
  have : (k:ℝ) - p ≠ 0 := by linarith
  have : p ≠ 0 := by linarith
  rw [show (k:ℝ) - (1 + p) + 1 = k - p by ring, show -(1 + p) + 1 = -p by ring]
  field_simp
  ring

/-- Helper: scaling of `∫ min(1,λ|ρ|)^k |ρ|^{-1-p}`. -/
theorem c10_aux_scaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C, 0 < C ∧ ∀ lam : ℝ, 1 ≤ lam →
      Integrable (fun ρ : ℝ => min 1 (lam * |ρ|) ^ k / |ρ| ^ (1 + p)) ∧
        ∫ ρ, min 1 (lam * |ρ|) ^ k / |ρ| ^ (1 + p) = C * lam ^ p := by
  obtain ⟨hi, hv⟩ := c10_aux_minpow p hp hp1 k hk
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  set g := fun t : ℝ => min 1 t ^ k / t ^ (1 + p)
  have hG : Integrable (fun s => g |s|) := c10_aux_integrable_comp_abs hi
  have hGv : ∫ s, g |s| = 2 * (1 / ((k:ℝ) - p) + 1 / p) := by
    rw [integral_comp_abs (f := g), hv]
  refine ⟨2 * (1 / ((k:ℝ) - p) + 1 / p), by
    have : 0 < (k:ℝ) - p := by linarith
    positivity, fun lam hlam => ?_⟩
  have hl0 : 0 < lam := by linarith
  have heq : (fun ρ : ℝ => min 1 (lam * |ρ|) ^ k / |ρ| ^ (1 + p)) =
      fun ρ => lam ^ (1 + p) * g |lam * ρ| := by
    funext ρ
    simp only [g]
    rw [abs_mul, abs_of_pos hl0, Real.mul_rpow hl0.le (abs_nonneg _)]
    have : lam ^ (1 + p) ≠ 0 := (Real.rpow_pos_of_pos hl0 _).ne'
    rw [mul_div_assoc', mul_div_mul_left _ _ this]
  rw [heq]
  refine ⟨(hG.comp_mul_left' hl0.ne').const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun s => g |s|), hGv, smul_eq_mul,
    abs_of_pos (inv_pos.2 hl0)]
  rw [show lam ^ (1 + p) = lam * lam ^ p by rw [Real.rpow_add hl0, Real.rpow_one]]
  field_simp
/-- Helper: far-region decay integral (third part of lem:c10_elementary_integrals). -/
theorem c10_aux_far_decay (p γ : ℝ) (hp : 0 < p) (hγ : 1 < γ) (y : ℝ) (hy : 2 ≤ |y|) (k : ℕ) :
      IntegrableOn (fun z => jb z ^ (-γ) / |y - z| ^ (1 + p + k)) {z | |y| / 2 ≤ |y - z|} ∧
      (∫ z in {z | |y| / 2 ≤ |y - z|}, jb z ^ (-γ) / |y - z| ^ (1 + p + k)) ≤
        2 ^ (1 + p + k) * (∫ z, jb z ^ (-γ)) * |y| ^ (-(1 + p) - k) ∧
      2 ^ (1 + p + k) * (∫ z, jb z ^ (-γ)) * |y| ^ (-(1 + p) - k) ≤
        2 ^ (2 * (1 + p) + 2 * k) * (∫ z, jb z ^ (-γ)) * jb y ^ (-(1 + p) - k) := by
  set q : ℝ := 1 + p + k with hqdef
  have hq : 0 < q := by positivity
  have hy0 : 0 < |y| := by linarith
  have hJ := c10_aux_jb_integrable hγ
  have hI0 : 0 ≤ ∫ z, jb z ^ (-γ) :=
    integral_nonneg fun z => (Real.rpow_pos_of_pos (c10_aux_jb_pos z) _).le
  have hS : MeasurableSet {z : ℝ | |y| / 2 ≤ |y - z|} :=
    measurableSet_le measurable_const (by fun_prop)
  set B : ℝ := (|y| / 2) ^ q with hB
  have hBpos : 0 < B := by positivity
  have hbd : ∀ z ∈ {z : ℝ | |y| / 2 ≤ |y - z|},
      jb z ^ (-γ) / |y - z| ^ q ≤ jb z ^ (-γ) / B := fun z hz => by
    apply div_le_div_of_nonneg_left (Real.rpow_pos_of_pos (c10_aux_jb_pos z) _).le hBpos
    exact Real.rpow_le_rpow (by positivity) hz hq.le
  have hmeas : AEStronglyMeasurable (fun z => jb z ^ (-γ) / |y - z| ^ q)
      (volume.restrict {z | |y| / 2 ≤ |y - z|}) := by
    apply Measurable.aestronglyMeasurable
    unfold jb; fun_prop
  have hint : IntegrableOn (fun z => jb z ^ (-γ) / |y - z| ^ q) {z | |y| / 2 ≤ |y - z|} := by
    refine Integrable.mono' ((hJ.div_const B).integrableOn) hmeas ?_
    refine (ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_pos_of_pos (c10_aux_jb_pos z) _).le
      (by positivity))]
    exact hbd z hz
  have hBinv : 1 / B = 2 ^ q * |y| ^ (-(1 + p) - k) := by
    rw [hB, Real.div_rpow hy0.le (by norm_num), show -(1 + p) - (k:ℝ) = -q by rw [hqdef]; ring,
      Real.rpow_neg hy0.le]
    field_simp
  refine ⟨hint, ?_, ?_⟩
  · calc (∫ z in {z | |y| / 2 ≤ |y - z|}, jb z ^ (-γ) / |y - z| ^ q)
        ≤ ∫ z in {z | |y| / 2 ≤ |y - z|}, jb z ^ (-γ) / B :=
          setIntegral_mono_on hint (hJ.div_const B).integrableOn hS hbd
      _ ≤ ∫ z, jb z ^ (-γ) / B := setIntegral_le_integral (hJ.div_const B)
          (ae_of_all _ fun z => div_nonneg (Real.rpow_pos_of_pos (c10_aux_jb_pos z) _).le hBpos.le)
      _ = 2 ^ q * (∫ z, jb z ^ (-γ)) * |y| ^ (-(1 + p) - k) := by
          rw [integral_div, div_eq_mul_one_div, hBinv]; ring
  · have hjb : jb y / 2 ≤ |y| := by
      have : jb y ≤ 2 * |y| := by
        unfold jb
        rw [Real.sqrt_le_left (by positivity)]
        have := sq_abs y; nlinarith
      linarith
    have hj0 := c10_aux_jb_pos y
    have h1 : |y| ^ (-(1 + p) - k) ≤ (jb y / 2) ^ (-(1 + p) - k) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hjb (by rw [show -(1 + p) - (k:ℝ) = -q by rw [hqdef]; ring]; linarith)
    have h2 : (jb y / 2) ^ (-(1 + p) - k) = 2 ^ q * jb y ^ (-(1 + p) - k) := by
      rw [Real.div_rpow hj0.le (by norm_num), show -(1 + p) - (k:ℝ) = -q by rw [hqdef]; ring,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    have h3 : (2:ℝ) ^ (2 * (1 + p) + 2 * k) = 2 ^ q * 2 ^ q := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; rw [hqdef]; ring
    rw [h3]
    calc 2 ^ q * (∫ z, jb z ^ (-γ)) * |y| ^ (-(1 + p) - k)
        ≤ 2 ^ q * (∫ z, jb z ^ (-γ)) * (jb y / 2) ^ (-(1 + p) - k) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by rw [h2]; ring

/-- Blueprint: lem:c10_elementary_integrals.  The elementary one-dimensional integrals used in
the near/far field estimates (`α = 1 + p`). -/
theorem c10_elementary_integrals (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ lam : ℝ, 1 ≤ lam →
      (Integrable (fun ρ : ℝ => min 1 (lam * |ρ|) ^ 2 / |ρ| ^ (1 + p)) ∧
        ∫ ρ, min 1 (lam * |ρ|) ^ 2 / |ρ| ^ (1 + p) = C₂ * lam ^ p) ∧
      (Integrable (fun ρ : ℝ => min 1 (lam * |ρ|) / |ρ| ^ (1 + p)) ∧
        ∫ ρ, min 1 (lam * |ρ|) / |ρ| ^ (1 + p) = C₁ * lam ^ p)) ∧
    (∀ a : ℝ, 0 < a →
      (∫ ρ in Icc (-a) a, |ρ| ^ (1 - p)) = 2 * a ^ (2 - p) / (2 - p) ∧
      (IntegrableOn (fun ρ : ℝ => |ρ| ^ (-p)) (Icc (-a) a) ∧
        (∫ ρ in Icc (-a) a, |ρ| ^ (-p)) = 2 * a ^ (1 - p) / (1 - p)) ∧
      (IntegrableOn (fun ρ : ℝ => |ρ| ^ (-(1 + p))) {ρ | a ≤ |ρ|} ∧
        (∫ ρ in {ρ | a ≤ |ρ|}, |ρ| ^ (-(1 + p))) = 2 / p * a ^ (-p)) ∧
      (IntegrableOn (fun ρ : ℝ => |ρ| ^ (-(1 + p) - 1)) {ρ | a ≤ |ρ|} ∧
        (∫ ρ in {ρ | a ≤ |ρ|}, |ρ| ^ (-(1 + p) - 1)) = 2 / (1 + p) * a ^ (-1 - p)) ∧
      (IntegrableOn (fun ρ : ℝ => |ρ| ^ (-(1 + p) - 2)) {ρ | a ≤ |ρ|} ∧
        (∫ ρ in {ρ | a ≤ |ρ|}, |ρ| ^ (-(1 + p) - 2)) = 2 / (2 + p) * a ^ (-2 - p))) ∧
    (∀ γ : ℝ, 1 < γ → ∀ y : ℝ, 2 ≤ |y| → ∀ k : ℕ, k = 1 ∨ k = 2 →
      IntegrableOn (fun z => jb z ^ (-γ) / |y - z| ^ (1 + p + k)) {z | |y| / 2 ≤ |y - z|} ∧
      (∫ z in {z | |y| / 2 ≤ |y - z|}, jb z ^ (-γ) / |y - z| ^ (1 + p + k)) ≤
        2 ^ (1 + p + k) * (∫ z, jb z ^ (-γ)) * |y| ^ (-(1 + p) - k) ∧
      2 ^ (1 + p + k) * (∫ z, jb z ^ (-γ)) * |y| ^ (-(1 + p) - k) ≤
        2 ^ (2 * (1 + p) + 2 * k) * (∫ z, jb z ^ (-γ)) * jb y ^ (-(1 + p) - k)) := by
  obtain ⟨C₂, hC₂, h2⟩ := c10_aux_scaled p hp hp1 2 (by norm_num)
  obtain ⟨C₁, hC₁, h1⟩ := c10_aux_scaled p hp hp1 1 le_rfl
  refine ⟨⟨C₁, C₂, hC₁, hC₂, fun lam hlam => ⟨h2 lam hlam, by simpa using h1 lam hlam⟩⟩,
    fun a ha => ?_, fun γ hγ y hy k _ => c10_aux_far_decay p γ hp hγ y hy k⟩
  have b1 := c10_aux_ball (1 - p) a (by linarith) ha
  have b2 := c10_aux_ball (-p) a (by linarith) ha
  have t1 := c10_aux_tail (1 + p) a (by linarith) ha
  have t2 := c10_aux_tail (2 + p) a (by linarith) ha
  have t3 := c10_aux_tail (3 + p) a (by linarith) ha
  rw [show -(1 + p) - 1 = -(2 + p) by ring, show -(1 + p) - 2 = -(3 + p) by ring]
  refine ⟨?_, ⟨b2.1, ?_⟩, ⟨t1.1, ?_⟩, ⟨t2.1, ?_⟩, ⟨t3.1, ?_⟩⟩
  · rw [b1.2, show 1 - p + 1 = 2 - p by ring]
  · rw [b2.2, show -p + 1 = 1 - p by ring]
  · rw [t1.2, show 1 + p - 1 = p by ring, show 1 - (1 + p) = -p by ring]
  · rw [t2.2, show 2 + p - 1 = 1 + p by ring, show 1 - (2 + p) = -1 - p by ring]
  · rw [t3.2, show 3 + p - 1 = 2 + p by ring, show 1 - (3 + p) = -2 - p by ring]

/-! ### Kernel helpers (`Γ_ε` derivatives, far-field algebra) -/

/-- Helper: translation `z ↦ y - z` for set integrals and integrability. -/
theorem c10_aux_translate (F : ℝ → ℝ) (y : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ z in {z | y - z ∈ s}, F (y - z)) = ∫ ρ in s, F ρ ∧
    (IntegrableOn F s → IntegrableOn (fun z => F (y - z)) {z | y - z ∈ s}) := by
  have hs' : MeasurableSet {z : ℝ | y - z ∈ s} := (measurable_const.sub measurable_id) hs
  have hind : {z : ℝ | y - z ∈ s}.indicator (fun z => F (y - z)) =
      fun z => s.indicator F (y - z) := by
    funext z; by_cases hz : y - z ∈ s <;> simp [indicator, hz]
  constructor
  · rw [← integral_indicator hs', ← integral_indicator hs, hind]
    exact integral_sub_left_eq_self (s.indicator F) volume y
  · intro hF
    have : Integrable (s.indicator F) := (integrable_indicator_iff hs).2 hF
    have h2 := this.comp_sub_left y
    rw [← hind] at h2
    exact (integrable_indicator_iff hs').1 h2

/-- Helper: `Γ_ε` as a function on `ℝ × ℝ`. -/
def c10_aux_G (p ε : ℝ) : ℝ × ℝ → ℝ := fun q => c03_Gamma_eps p ε q.1 q.2

/-- Helper: kernel toolkit (`c10_aux_G_smooth`). -/
theorem c10_aux_G_smooth (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) :
    ContDiff ℝ (⊤ : ℕ∞) (c10_aux_G p ε) := (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.1

/-- Helper: kernel toolkit (`c10_aux_G_fderiv_smooth`). -/
theorem c10_aux_G_fderiv_smooth (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) :
    ContDiff ℝ 2 (fderiv ℝ (c10_aux_G p ε)) :=
  (c10_aux_G_smooth p ε hp hp1 hε).fderiv_right (m := 2) (WithTop.coe_le_coe.2 le_top)

theorem c10_aux_curve {a b : ℝ → ℝ} {y a' b' : ℝ} (ha : HasDerivAt a a' y) (hb : HasDerivAt b b' y) :
    HasDerivAt (fun t => (a t, b t)) (a', b') y := ha.prodMk hb

/-- Helper: kernel toolkit (`c10_aux_d_eq`). -/
theorem c10_aux_d_eq (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (u v : ℝ) :
    c10_N_pieces_Gamma_d1 p ε u v = fderiv ℝ (c10_aux_G p ε) (u, v) (1, 0) ∧
    c10_N_pieces_Gamma_d2 p ε u v = fderiv ℝ (c10_aux_G p ε) (u, v) (0, 1) := by
  have hG := c10_aux_G_smooth p ε hp hp1 hε
  have hd : ∀ q, HasFDerivAt (c10_aux_G p ε) (fderiv ℝ (c10_aux_G p ε) q) q := fun q =>
    (hG.differentiable (by simp)).differentiableAt.hasFDerivAt
  constructor
  · have := (hd (u, v)).comp_hasDerivAt u (c10_aux_curve (hasDerivAt_id u) (hasDerivAt_const u v))
    exact this.deriv
  · have := (hd (u, v)).comp_hasDerivAt v (c10_aux_curve (hasDerivAt_const v u) (hasDerivAt_id v))
    exact this.deriv

/-- Helper: kernel toolkit (`c10_aux_D2_curve`). -/
theorem c10_aux_D2_curve (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    {a b : ℝ → ℝ} {y a' b' : ℝ} (ha : HasDerivAt a a' y) (hb : HasDerivAt b b' y) (w : ℝ × ℝ) :
    HasDerivAt (fun t => fderiv ℝ (c10_aux_G p ε) (a t, b t) w)
      (fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (a y, b y) (a', b') w) y := by
  have hF := c10_aux_G_fderiv_smooth p ε hp hp1 hε
  have hd : HasFDerivAt (fderiv ℝ (c10_aux_G p ε))
      (fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (a y, b y)) (a y, b y) :=
    (hF.differentiable two_ne_zero).differentiableAt.hasFDerivAt
  have h1 : HasDerivAt (fun t => fderiv ℝ (c10_aux_G p ε) (a t, b t))
      (fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (a y, b y) (a', b')) y :=
    hd.comp_hasDerivAt (x := y) (f := fun t => (a t, b t)) (c10_aux_curve ha hb)
  have h2 := h1.clm_apply (hasDerivAt_const y w)
  rw [map_zero, add_zero] at h2
  exact h2

/-- Helper: kernel toolkit (`c10_aux_D2_symm`). -/
theorem c10_aux_D2_symm (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (q v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) q v w = fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) q w v :=
  ((c10_aux_G_smooth p ε hp hp1 hε).contDiffAt (x := q)).isSymmSndFDerivAt (by simp) v w

/-- Helper: kernel toolkit (`c10_aux_dd_eq`). -/
theorem c10_aux_dd_eq (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (u v : ℝ) :
    c10_N_pieces_Gamma_d11 p ε u v = fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) (1, 0) (1, 0) ∧
    c10_N_pieces_Gamma_d12 p ε u v = fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) (0, 1) (1, 0) ∧
    c10_N_pieces_Gamma_d22 p ε u v = fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) (0, 1) (0, 1) := by
  have e1 : ∀ u v, c10_N_pieces_Gamma_d1 p ε u v = fderiv ℝ (c10_aux_G p ε) (u, v) (1, 0) :=
    fun u v => (c10_aux_d_eq p ε hp hp1 hε u v).1
  have e2 : ∀ u v, c10_N_pieces_Gamma_d2 p ε u v = fderiv ℝ (c10_aux_G p ε) (u, v) (0, 1) :=
    fun u v => (c10_aux_d_eq p ε hp hp1 hε u v).2
  refine ⟨?_, ?_, ?_⟩
  · unfold c10_N_pieces_Gamma_d11; simp_rw [e1]
    exact (c10_aux_D2_curve p ε hp hp1 hε (hasDerivAt_id u) (hasDerivAt_const u v) _).deriv
  · unfold c10_N_pieces_Gamma_d12; simp_rw [e1]
    exact (c10_aux_D2_curve p ε hp hp1 hε (hasDerivAt_const v u) (hasDerivAt_id v) _).deriv
  · unfold c10_N_pieces_Gamma_d22; simp_rw [e2]
    exact (c10_aux_D2_curve p ε hp hp1 hε (hasDerivAt_const v u) (hasDerivAt_id v) _).deriv

/-- Helper: chain rule for `∂₁Γ_ε`, `∂₂Γ_ε` along curves. -/
theorem c10_aux_d_chain (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    {a b : ℝ → ℝ} {y a' b' : ℝ} (ha : HasDerivAt a a' y) (hb : HasDerivAt b b' y) :
    HasDerivAt (fun t => c10_N_pieces_Gamma_d1 p ε (a t) (b t))
      (c10_N_pieces_Gamma_d11 p ε (a y) (b y) * a' + c10_N_pieces_Gamma_d12 p ε (a y) (b y) * b') y ∧
    HasDerivAt (fun t => c10_N_pieces_Gamma_d2 p ε (a t) (b t))
      (c10_N_pieces_Gamma_d12 p ε (a y) (b y) * a' + c10_N_pieces_Gamma_d22 p ε (a y) (b y) * b') y := by
  obtain ⟨f11, f12, f22⟩ := c10_aux_dd_eq p ε hp hp1 hε (a y) (b y)
  have hab : ((a', b') : ℝ × ℝ) = a' • ((1 : ℝ), (0 : ℝ)) + b' • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hs := c10_aux_D2_symm p ε hp hp1 hε (a y, b y) (1, 0) (0, 1)
  constructor
  · have := c10_aux_D2_curve p ε hp hp1 hε ha hb (1, 0)
    simp_rw [fun u v => (c10_aux_d_eq p ε hp hp1 hε u v).1]
    convert this using 1
    rw [f11, f12, hab, map_add, map_smul, map_smul]; simp [mul_comm]
  · have := c10_aux_D2_curve p ε hp hp1 hε ha hb (0, 1)
    simp_rw [fun u v => (c10_aux_d_eq p ε hp hp1 hε u v).2]
    convert this using 1
    rw [f12, f22, hab, map_add, map_smul, map_smul, ← hs]; simp [mul_comm]


/-- Helper: kernel toolkit (`c10_aux_D2_le`). -/
theorem c10_aux_D2_le (p ε : ℝ) (q v w : ℝ × ℝ) :
    |fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) q v w| ≤
      ‖iteratedFDeriv ℝ 2 (c10_aux_G p ε) q‖ * (‖v‖ * ‖w‖) := by
  have := (iteratedFDeriv ℝ 2 (c10_aux_G p ε) q).le_opNorm ![v, w]
  rw [iteratedFDeriv_two_apply] at this
  simpa [Fin.prod_univ_two] using this

/-- Helper: kernel toolkit (`c10_aux_kernel_bounds`). -/
theorem c10_aux_kernel_bounds (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 1 ≤ R) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ u v : ℝ, |u| ≤ R → |v| ≤ R →
      |c10_N_pieces_Gamma_d1 p ε u v| ≤ C * ε ∧ |c10_N_pieces_Gamma_d2 p ε u v| ≤ C * ε ∧
      |c10_N_pieces_Gamma_d11 p ε u v| ≤ C * ε ∧ |c10_N_pieces_Gamma_d12 p ε u v| ≤ C * ε ∧
      |c10_N_pieces_Gamma_d22 p ε u v| ≤ C * ε ∧
      |c10_N_pieces_Gamma_d2 p ε u v| ≤ C * ε * |u - v| ∧
      |c10_N_pieces_Gamma_d1 p ε u v + c10_N_pieces_Gamma_d2 p ε u v| ≤ C * ε * (u - v) ^ 2 ∧
      |c10_N_pieces_Gamma_d11 p ε u v + c10_N_pieces_Gamma_d12 p ε u v| ≤ C * ε * |u - v| ∧
      |c10_N_pieces_Gamma_d12 p ε u v + c10_N_pieces_Gamma_d22 p ε u v| ≤ C * ε * |u - v| := by
  obtain ⟨⟨C, hC, hb⟩, -⟩ := analysis_vanishing_diagonal p R hp hp1 hR
  have hR0 : 0 ≤ R := by linarith
  refine ⟨C 1 * (4 * R ^ 2) + C 1 * (2 * R) + C 1 + C 2, by
    have := hC 1; have := hC 2; positivity, fun ε hε hε1 u v hu hv => ?_⟩
  obtain ⟨-, -, h2a, -, hj, h3a, h3b⟩ := hb ε hε hε1 u v hu hv
  change ‖fderiv ℝ (c10_aux_G p ε) (u, v)‖ ≤ _ at h2a
  change ∀ j, ‖iteratedFDeriv ℝ j (c10_aux_G p ε) (u, v)‖ ≤ C j * ε at hj
  change ∀ j, |iteratedFDeriv ℝ j (c10_aux_G p ε) (u, v) (fun _ => ((1 : ℝ), (1 : ℝ)))| ≤ _ at h3a
  change ∀ w : ℝ × ℝ, |iteratedFDeriv ℝ 2 (c10_aux_G p ε) (u, v) ![((1 : ℝ), (1 : ℝ)), w]| ≤ _
    at h3b
  obtain ⟨e1, e2⟩ := c10_aux_d_eq p ε hp (by linarith) hε u v
  obtain ⟨f11, f12, f22⟩ := c10_aux_dd_eq p ε hp hp1 hε u v
  have hs := c10_aux_D2_symm p ε hp hp1 hε (u, v) (1, 0) (0, 1)
  have n10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have n01 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have huv : |u - v| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
  have huv' : |u| + |v| ≤ 2 * R := by linarith
  have c1 := hC 1; have c2 := hC 2
  have Lb : ∀ w : ℝ × ℝ, ‖w‖ = 1 → |fderiv ℝ (c10_aux_G p ε) (u, v) w| ≤ C 1 * ε * |u - v| * (2 * R) := by
    intro w hw
    have := (fderiv ℝ (c10_aux_G p ε) (u, v)).le_opNorm w
    rw [hw, mul_one, Real.norm_eq_abs] at this
    refine this.trans (h2a.trans ?_)
    exact mul_le_mul_of_nonneg_left huv' (by positivity)
  have Lc : ∀ w : ℝ × ℝ, ‖w‖ = 1 → |fderiv ℝ (c10_aux_G p ε) (u, v) w| ≤ C 1 * (4 * R ^ 2) * ε := by
    intro w hw
    refine (Lb w hw).trans ?_
    have : C 1 * ε * |u - v| * (2 * R) ≤ C 1 * ε * (2 * R) * (2 * R) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left huv (by positivity)
    nlinarith
  have Dc : ∀ v' w : ℝ × ℝ, ‖v'‖ = 1 → ‖w‖ = 1 →
      |fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) v' w| ≤ C 2 * ε := by
    intro v' w hv' hw
    have := c10_aux_D2_le p ε (u, v) v' w
    rw [hv', hw, mul_one, mul_one] at this
    exact this.trans (hj 2)
  have hCe : ∀ X : ℝ, X ≤ C 1 * (4 * R ^ 2) * ε ∨ X ≤ C 2 * ε ∨ X ≤ C 1 * ε →
      X ≤ (C 1 * (4 * R ^ 2) + C 1 * (2 * R) + C 1 + C 2) * ε := by
    intro X hX
    have : 0 ≤ C 1 * (2 * R) * ε := by positivity
    have : 0 ≤ C 1 * ε := by positivity
    have : 0 ≤ C 2 * ε := by positivity
    have : 0 ≤ C 1 * (4 * R ^ 2) * ε := by positivity
    rcases hX with h | h | h <;> nlinarith
  have hsum : ((1 : ℝ), (1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by simp
  set K := C 1 * (4 * R ^ 2) + C 1 * (2 * R) + C 1 + C 2 with hK
  have hKa : C 1 * (2 * R) ≤ K := by
    have : 0 ≤ C 1 * (4 * R ^ 2) := by positivity
    linarith
  have hKb : C 1 ≤ K := by
    have : 0 ≤ C 1 * (4 * R ^ 2) := by positivity
    have : 0 ≤ C 1 * (2 * R) := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; exact hCe _ (Or.inl (Lc _ n10))
  · rw [e2]; exact hCe _ (Or.inl (Lc _ n01))
  · rw [f11]; exact hCe _ (Or.inr (Or.inl (Dc _ _ n10 n10)))
  · rw [f12]; exact hCe _ (Or.inr (Or.inl (Dc _ _ n01 n10)))
  · rw [f22]; exact hCe _ (Or.inr (Or.inl (Dc _ _ n01 n01)))
  · rw [e2]
    refine (Lb _ n01).trans ?_
    have := mul_le_mul_of_nonneg_right hKa (show 0 ≤ ε * |u - v| by positivity)
    nlinarith [abs_nonneg (u - v)]
  · rw [e1, e2, ← map_add, ← hsum]
    have := h3a 1
    rw [iteratedFDeriv_one_apply] at this
    refine this.trans ?_
    rw [sq_abs]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKb hε) (sq_nonneg _)
  · rw [f11, f12, ← ContinuousLinearMap.add_apply, ← map_add, ← hsum]
    have := h3b (1, 0)
    rw [iteratedFDeriv_two_apply, n10, mul_one] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKb hε) (abs_nonneg _)
  · rw [f12, f22, ← hs, ← ContinuousLinearMap.add_apply, ← map_add, ← hsum]
    have := h3b (0, 1)
    rw [iteratedFDeriv_two_apply, n01, mul_one] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKb hε) (abs_nonneg _)

/-- Helper: the explicit `y`-derivative of `K_{f,h}(·,z)`. -/
def c10_aux_DK (p ε : ℝ) (f h : ℝ → ℝ) (y z : ℝ) : ℝ :=
  (c10_N_pieces_Gamma_d11 p ε (deriv f y) (c01_secant f y z) * deriv (deriv f) y +
      c10_N_pieces_Gamma_d12 p ε (deriv f y) (c01_secant f y z) *
        ((deriv f y - c01_secant f y z) / (y - z))) * deriv h y +
    c10_N_pieces_Gamma_d1 p ε (deriv f y) (c01_secant f y z) * deriv (deriv h) y +
    (c10_N_pieces_Gamma_d12 p ε (deriv f y) (c01_secant f y z) * deriv (deriv f) y +
      c10_N_pieces_Gamma_d22 p ε (deriv f y) (c01_secant f y z) *
        ((deriv f y - c01_secant f y z) / (y - z))) * c01_secant h y z +
    c10_N_pieces_Gamma_d2 p ε (deriv f y) (c01_secant f y z) *
      ((deriv h y - c01_secant h y z) / (y - z))

/-- Helper: kernel toolkit (`c10_aux_K_hasDeriv`). -/
theorem c10_aux_K_hasDeriv (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    {f h : ℝ → ℝ} (hf : W2inftyLoc f) (hh : W2inftyLoc h) {y z : ℝ} (hyz : y ≠ z)
    (hf2 : DifferentiableAt ℝ (deriv f) y) (hh2 : DifferentiableAt ℝ (deriv h) y) :
    HasDerivAt (fun y' => c10_N3_linearization_K p ε f h y' z) (c10_aux_DK p ε f h y z) y := by
  have sf := (c10_secant_identities f hf y z hyz).2.2.1
  have sh := (c10_secant_identities h hh y z hyz).2.2.1
  obtain ⟨c1, c2⟩ := c10_aux_d_chain p ε hp hp1 hε hf2.hasDerivAt sf
  have := (c1.mul hh2.hasDerivAt).add (c2.mul sh)
  unfold c10_N3_linearization_K c10_aux_DK
  convert this using 1
  ring

/-- Helper: kernel toolkit (`c10_aux_secant_meas`). -/
theorem c10_aux_secant_meas {g : ℝ → ℝ} (hg : Continuous g) (y : ℝ) :
    Measurable (fun z => c01_secant g y z) := by
  unfold c01_secant
  refine Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const ?_
  exact (measurable_const.sub hg.measurable).div (measurable_const.sub measurable_id)

/-- Helper: kernel toolkit (`c10_aux_d_cont`). -/
theorem c10_aux_d_cont (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (u : ℝ) :
    Continuous (c10_N_pieces_Gamma_d1 p ε u) ∧ Continuous (c10_N_pieces_Gamma_d2 p ε u) ∧
    Continuous (c10_N_pieces_Gamma_d11 p ε u) ∧ Continuous (c10_N_pieces_Gamma_d12 p ε u) ∧
    Continuous (c10_N_pieces_Gamma_d22 p ε u) := by
  have hF := c10_aux_G_fderiv_smooth p ε hp hp1 hε
  have c1 : Continuous (fderiv ℝ (c10_aux_G p ε)) := hF.continuous
  have c2 : Continuous (fderiv ℝ (fderiv ℝ (c10_aux_G p ε))) := hF.continuous_fderiv (by norm_num)
  have cv : Continuous (fun v : ℝ => ((u, v) : ℝ × ℝ)) := continuous_const.prodMk continuous_id
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp_rw [show c10_N_pieces_Gamma_d1 p ε u = fun v => fderiv ℝ (c10_aux_G p ε) (u, v) (1, 0) from
      funext fun v => (c10_aux_d_eq p ε hp hp1 hε u v).1]
    exact (c1.comp cv).clm_apply continuous_const
  · simp_rw [show c10_N_pieces_Gamma_d2 p ε u = fun v => fderiv ℝ (c10_aux_G p ε) (u, v) (0, 1) from
      funext fun v => (c10_aux_d_eq p ε hp hp1 hε u v).2]
    exact (c1.comp cv).clm_apply continuous_const
  · simp_rw [show c10_N_pieces_Gamma_d11 p ε u = fun v =>
      fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) (1, 0) (1, 0) from
      funext fun v => (c10_aux_dd_eq p ε hp hp1 hε u v).1]
    exact ((c2.comp cv).clm_apply continuous_const).clm_apply continuous_const
  · simp_rw [show c10_N_pieces_Gamma_d12 p ε u = fun v =>
      fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) (0, 1) (1, 0) from
      funext fun v => (c10_aux_dd_eq p ε hp hp1 hε u v).2.1]
    exact ((c2.comp cv).clm_apply continuous_const).clm_apply continuous_const
  · simp_rw [show c10_N_pieces_Gamma_d22 p ε u = fun v =>
      fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) (0, 1) (0, 1) from
      funext fun v => (c10_aux_dd_eq p ε hp hp1 hε u v).2.2]
    exact ((c2.comp cv).clm_apply continuous_const).clm_apply continuous_const

/-- Helper: kernel toolkit (`c10_aux_K_meas`). -/
theorem c10_aux_K_meas (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h) (y : ℝ) :
    Measurable (fun z => c10_N3_linearization_K p ε f h y z) ∧
    Measurable (fun z => c10_aux_DK p ε f h y z) := by
  obtain ⟨c1, c2, c11, c12, c22⟩ := c10_aux_d_cont p ε hp hp1 hε (deriv f y)
  have sf := c10_aux_secant_meas hf y
  have sh := c10_aux_secant_meas hh y
  have m1 := c1.measurable.comp sf; have m2 := c2.measurable.comp sf
  have m11 := c11.measurable.comp sf; have m12 := c12.measurable.comp sf
  have m22 := c22.measurable.comp sf
  have hyz : Measurable (fun z : ℝ => y - z) := measurable_const.sub measurable_id
  constructor
  · unfold c10_N3_linearization_K
    exact (m1.mul measurable_const).add (m2.mul sh)
  · unfold c10_aux_DK
    exact (((((m11.mul measurable_const).add (m12.mul ((measurable_const.sub sf).div hyz))).mul
      measurable_const).add (m1.mul measurable_const)).add
      (((m12.mul measurable_const).add (m22.mul ((measurable_const.sub sf).div hyz))).mul sh)).add
        (m2.mul ((measurable_const.sub sh).div hyz))

/-- Helper: far-region integral bound for `|y| ≥ 2`. -/
theorem c10_aux_far_int (p γ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hγ : 1 < γ) {y : ℝ} (hy : 2 ≤ |y|)
    {F : ℝ → ℝ} (hF : AEStronglyMeasurable F (volume.restrict {z | |y| / 2 ≤ |y - z|}))
    {c W V U : ℝ} (hc : 0 ≤ c) (hW : 0 ≤ W) (hV : 0 ≤ V) (hU : 0 ≤ U)
    (hb : ∀ z, |y| / 2 ≤ |y - z| → |F z| ≤ c * (W * |y - z| ^ (-(1 + p)) +
      V * |y - z| ^ (-(2 + p)) + U * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1)))) :
    IntegrableOn F {z | |y| / 2 ≤ |y - z|} ∧
      ∫ z in {z | |y| / 2 ≤ |y - z|}, F z ≤ c * (W * (2 / p) + V * 2 +
        U * (2 ^ (2 * (1 + p) + 2) * (∫ z, jb z ^ (-γ)) * jb y ^ (-(1 + p) - 1))) := by
  set S := {z : ℝ | |y| / 2 ≤ |y - z|} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  set a := |y| / 2 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have ha0 : 0 < a := by linarith
  have hT : MeasurableSet {ρ : ℝ | a ≤ |ρ|} := measurableSet_le measurable_const (by fun_prop)
  obtain ⟨t1i, t1v⟩ := c10_aux_tail (1 + p) a (by linarith) ha0
  obtain ⟨t2i, t2v⟩ := c10_aux_tail (2 + p) a (by linarith) ha0
  obtain ⟨tr1, tr1i⟩ := c10_aux_translate (fun ρ => |ρ| ^ (-(1 + p))) y hT
  obtain ⟨tr2, tr2i⟩ := c10_aux_translate (fun ρ => |ρ| ^ (-(2 + p))) y hT
  have I1 : IntegrableOn (fun z => |y - z| ^ (-(1 + p))) S := tr1i t1i
  have I2 : IntegrableOn (fun z => |y - z| ^ (-(2 + p))) S := tr2i t2i
  obtain ⟨-, -, E3⟩ := c10_elementary_integrals p hp hp1
  obtain ⟨I3, I3v, I3w⟩ := E3 γ hγ y hy 1 (Or.inl rfl)
  simp only [Nat.cast_one] at I3 I3v I3w
  have hG : IntegrableOn (fun z => c * (W * |y - z| ^ (-(1 + p)) + V * |y - z| ^ (-(2 + p)) +
      U * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1)))) S :=
    (((I1.const_mul W).add (I2.const_mul V)).add (I3.const_mul U)).const_mul c
  have hFi : IntegrableOn F S := by
    refine Integrable.mono' hG hF ((ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_))
    rw [Real.norm_eq_abs]; exact hb z hz
  refine ⟨hFi, ?_⟩
  have hjnn : ∀ z, 0 ≤ jb z ^ (-γ) := fun z => (Real.rpow_pos_of_pos (c10_aux_jb_pos z) _).le
  have hIγ : 0 ≤ ∫ z, jb z ^ (-γ) := integral_nonneg hjnn
  calc ∫ z in S, F z ≤ ∫ z in S, c * (W * |y - z| ^ (-(1 + p)) + V * |y - z| ^ (-(2 + p)) +
        U * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1))) :=
        setIntegral_mono_on hFi hG hS fun z hz => (le_abs_self _).trans (hb z hz)
    _ = c * (W * (2 / (1 + p - 1) * a ^ (1 - (1 + p))) + V * (2 / (2 + p - 1) * a ^ (1 - (2 + p))) +
        U * ∫ z in S, jb z ^ (-γ) / |y - z| ^ (1 + p + 1)) := by
        have J12 : IntegrableOn (fun z => W * |y - z| ^ (-(1 + p)) + V * |y - z| ^ (-(2 + p))) S :=
          (I1.const_mul W).add (I2.const_mul V)
        have J3 : IntegrableOn (fun z => U * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1))) S :=
          I3.const_mul U
        have J1 : IntegrableOn (fun z => W * |y - z| ^ (-(1 + p))) S := I1.const_mul W
        have J2 : IntegrableOn (fun z => V * |y - z| ^ (-(2 + p))) S := I2.const_mul V
        rw [integral_const_mul, integral_add J12 J3, integral_add J1 J2, integral_const_mul,
          integral_const_mul, integral_const_mul, ← t1v, ← t2v, ← tr1, ← tr2]
        rfl
    _ ≤ _ := by
        have e1 : a ^ (1 - (1 + p)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
        have e2 : a ^ (1 - (2 + p)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1 (by linarith)
        have e3 : 2 / (2 + p - 1) ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        have q1 : 2 / (1 + p - 1) * a ^ (1 - (1 + p)) ≤ 2 / p := by
          rw [show 1 + p - 1 = p by ring]
          calc _ ≤ 2 / p * 1 := mul_le_mul_of_nonneg_left e1 (by positivity)
            _ = _ := mul_one _
        have q2 : 2 / (2 + p - 1) * a ^ (1 - (2 + p)) ≤ 2 :=
          (mul_le_mul_of_nonneg_left e2 (by apply div_nonneg <;> linarith)).trans (by linarith)
        apply mul_le_mul_of_nonneg_left _ hc
        have := I3v.trans I3w
        have A1 := mul_le_mul_of_nonneg_left q1 hW
        have A2 := mul_le_mul_of_nonneg_left q2 hV
        have A3 := mul_le_mul_of_nonneg_left this hU
        rw [show -(1 + p) - (1 : ℝ) = -(1 + p) - 1 by ring] at A3
        linarith

/-- Helper: the algebra of the far-field integrand bounds. -/
theorem c10_aux_far_alg {d1 d2 d11 d12 d22 a b h1 h2 S S' t e c x J W1 Q : ℝ}
    (he : 0 ≤ e) (hc : 0 ≤ c) (hx : 0 ≤ x) (hJ : 0 ≤ J) (hW : 0 ≤ W1) (hQ : 0 ≤ Q)
    (b1 : |d1| ≤ e) (b2 : |d2| ≤ e) (b11 : |d11| ≤ e) (b12 : |d12| ≤ e) (b22 : |d22| ≤ e)
    (ha : |a| ≤ c * J) (hb : |b| ≤ 8 * c * J) (hh1 : |h1| ≤ x * W1) (hh2 : |h2| ≤ x * (J * W1))
    (hS : |S| ≤ x * Q) (hS' : |S'| ≤ 4 * J * (|h1| + |S|)) (ht0 : 0 ≤ t) (ht : t ≤ 4 * J) :
    |d1 * h1 + d2 * S| ≤ e * x * (W1 + Q) ∧
    |(d11 * a + d12 * b) * h1 + d1 * h2 + (d12 * a + d22 * b) * S + d2 * S'| +
      |d1 * h1 + d2 * S| * t ≤ (9 * c + 9) * e * x * (J * W1 + J * Q) := by
  have P : ∀ {u v U V : ℝ}, |u| ≤ U → |v| ≤ V → |u * v| ≤ U * V := fun hu hv => by
    rw [abs_mul]; exact mul_le_mul hu hv (abs_nonneg _) ((abs_nonneg _).trans hu)
  have k1 : |d1 * h1 + d2 * S| ≤ e * (x * W1) + e * (x * Q) :=
    (abs_add_le _ _).trans (add_le_add (P b1 hh1) (P b2 hS))
  have m1 : |d11 * a + d12 * b| ≤ e * (c * J) + e * (8 * c * J) :=
    (abs_add_le _ _).trans (add_le_add (P b11 ha) (P b12 hb))
  have m2 : |d12 * a + d22 * b| ≤ e * (c * J) + e * (8 * c * J) :=
    (abs_add_le _ _).trans (add_le_add (P b12 ha) (P b22 hb))
  have T1 := P m1 hh1
  have T2 := P b1 hh2
  have T3 := P m2 hS
  have hS'' : |S'| ≤ 4 * J * (x * W1 + x * Q) :=
    hS'.trans (mul_le_mul_of_nonneg_left (add_le_add hh1 hS) (by positivity))
  have T4 := P b2 hS''
  have T5 : |d1 * h1 + d2 * S| * t ≤ (e * (x * W1) + e * (x * Q)) * (4 * J) :=
    mul_le_mul k1 ht ht0 (by positivity)
  have s1 := abs_add_le ((d11 * a + d12 * b) * h1 + d1 * h2 + (d12 * a + d22 * b) * S) (d2 * S')
  have s2 := abs_add_le ((d11 * a + d12 * b) * h1 + d1 * h2) ((d12 * a + d22 * b) * S)
  have s3 := abs_add_le ((d11 * a + d12 * b) * h1) (d1 * h2)
  have n1 : 0 ≤ e * x * J * W1 := by positivity
  have n2 : 0 ≤ e * x * J * Q := by positivity
  have n3 : 0 ≤ c * e * x * J * W1 := by positivity
  have n4 : 0 ≤ c * e * x * J * Q := by positivity
  constructor
  · linarith
  · linarith

/-- Helper: splitting the far-field bound. -/
theorem c10_aux_far_split {t : ℝ} (ht : 0 < t) (p W V U : ℝ) :
    (W + (V + U) / t) / t ^ (p + 1) =
      W * t ^ (-(1 + p)) + V * t ^ (-(2 + p)) + U * (1 / t ^ (1 + p + 1)) := by
  have e1 : t ^ (1 + p + 1) = t ^ (p + 1) * t := by
    rw [Real.rpow_add ht, Real.rpow_one, add_comm 1 p]
  have e2 : t ^ (2 + p) = t ^ (p + 1) * t := by
    rw [← e1]; ring_nf
  rw [Real.rpow_neg ht.le, Real.rpow_neg ht.le, e2, e1, add_comm 1 p]
  have : t ^ (p + 1) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  field_simp
  ring

/-- Helper: `⟨y⟩ ≤ 2|y|` for `|y| ≥ 1`. -/
theorem c10_aux_jb_le_two_abs {y : ℝ} (hy : 1 ≤ |y|) : jb y ≤ 2 * |y| := by
  unfold jb
  rw [Real.sqrt_le_left (by positivity)]
  have := sq_abs y; nlinarith

/-- Helper: mean value bound `|∂₁Γ_ε(u,v) - ∂₁Γ_ε(u₀,w)| ≤ C ε (|u-u₀| + |v-w|)` on a box. -/
theorem c10_aux_d1_lip (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 1 ≤ R) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ u v u₀ w : ℝ, |u| ≤ R → |v| ≤ R → |u₀| ≤ R → |w| ≤ R →
      |c10_N_pieces_Gamma_d1 p ε u v - c10_N_pieces_Gamma_d1 p ε u₀ w| ≤
        C * ε * (|u - u₀| + |v - w|) := by
  obtain ⟨Cg, hCg, hK⟩ := c10_aux_kernel_bounds p R hp hp1 hR
  refine ⟨Cg, hCg, fun ε hε hε1 u v u₀ w hu hv hu₀ hw => ?_⟩
  set a : ℝ → ℝ := fun t => u₀ + t * (u - u₀)
  set b : ℝ → ℝ := fun t => w + t * (v - w)
  have ha : ∀ t, HasDerivAt a (u - u₀) t := fun t => by
    have := ((hasDerivAt_id t).mul_const (u - u₀)).const_add u₀
    rw [one_mul] at this; exact this
  have hb : ∀ t, HasDerivAt b (v - w) t := fun t => by
    have := ((hasDerivAt_id t).mul_const (v - w)).const_add w
    rw [one_mul] at this; exact this
  have hbox : ∀ {x y : ℝ} {t : ℝ}, |x| ≤ R → |y| ≤ R → t ∈ Icc (0 : ℝ) 1 →
      |x + t * (y - x)| ≤ R := by
    intro x y t hx hy ht
    have : x + t * (y - x) = (1 - t) * x + t * y := by ring
    rw [this]
    calc _ ≤ |(1 - t) * x| + |t * y| := abs_add_le _ _
      _ = (1 - t) * |x| + t * |y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * R + t * R := add_le_add (mul_le_mul_of_nonneg_left hx (by linarith [ht.2]))
          (mul_le_mul_of_nonneg_left hy ht.1)
      _ = R := by ring
  have hd := fun t => (c10_aux_d_chain p ε hp hp1 hε (ha t) (hb t)).1
  have := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (f := fun t => c10_N_pieces_Gamma_d1 p ε (a t) (b t)) (C := Cg * ε * (|u - u₀| + |v - w|))
    (fun t _ => (hd t).differentiableAt) (fun t ht => by
      rw [(hd t).deriv, Real.norm_eq_abs]
      obtain ⟨-, -, b11, b12, -⟩ := hK ε hε hε1 (a t) (b t) (hbox hu₀ hu ht) (hbox hw hv ht)
      calc _ ≤ |c10_N_pieces_Gamma_d11 p ε (a t) (b t)| * |u - u₀| +
            |c10_N_pieces_Gamma_d12 p ε (a t) (b t)| * |v - w| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ Cg * ε * |u - u₀| + Cg * ε * |v - w| :=
            add_le_add (mul_le_mul_of_nonneg_right b11 (abs_nonneg _))
              (mul_le_mul_of_nonneg_right b12 (abs_nonneg _))
        _ = _ := by ring)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  simp only [a, b, Real.norm_eq_abs] at this
  simpa using this

/-- Helper: the algebra of the far-field (`y ≥ 2`) integrand bounds. -/
theorem c10_aux_farp_alg {Dd d2 d11 d12 d22 e12 a b bW h1 h2 S S' t e eL c x J P G Q : ℝ}
    (he : 0 ≤ e) (heL : 0 ≤ eL) (hc : 0 ≤ c) (hx : 0 ≤ x) (hJ : 0 ≤ J) (hJ1 : J ≤ 1)
    (hP : 1 ≤ P) (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (bD : |Dd| ≤ eL * J) (b2 : |d2| ≤ e) (b11 : |d11| ≤ e) (b12 : |d12| ≤ e) (b22 : |d22| ≤ e)
    (be : |e12| ≤ e) (ha : |a| ≤ c * (J * P)) (hb : |b| ≤ 8 * c * J) (hbW : |bW| ≤ 4 * J)
    (hh1 : |h1| ≤ x * (G * P)) (hh2 : |h2| ≤ x * (G * P * P))
    (hS : |S| ≤ x * Q) (hS' : |S'| ≤ 4 * J * (|h1| + |S|)) (ht0 : 0 ≤ t) (ht : t ≤ 4 * J) :
    |Dd * h1 + d2 * S| ≤ eL * x * (J * G * P) + e * x * Q ∧
    |Dd * h2 + (d11 * a + d12 * b - e12 * bW) * h1 + (d12 * a + d22 * b) * S + d2 * S'| +
      |Dd * h1 + d2 * S| * t ≤
      (5 * eL + e * (9 * c + 8)) * x * (G * P * P * J + J * P * Q) := by
  have P' : ∀ {u v U V : ℝ}, |u| ≤ U → |v| ≤ V → |u * v| ≤ U * V := fun hu hv => by
    rw [abs_mul]; exact mul_le_mul hu hv (abs_nonneg _) ((abs_nonneg _).trans hu)
  have hP0 : 0 ≤ P := by linarith
  have JP : J ≤ J * P := le_mul_of_one_le_right hJ hP
  have PP : P ≤ P * P := le_mul_of_one_le_right hP0 hP
  have JJ : J * J ≤ J := mul_le_of_le_one_right hJ hJ1
  set K := G * P * P * J with hK
  set L := J * P * Q with hL
  have hK0 : 0 ≤ K := by positivity
  have hL0 : 0 ≤ L := by positivity
  -- monomial comparisons
  have m1 : J * (G * P) ≤ K := by
    rw [hK]; have := mul_le_mul_of_nonneg_left PP (mul_nonneg hJ hG); linarith [this]
  have m2 : J * Q ≤ L := by rw [hL]; exact mul_le_mul_of_nonneg_right JP hQ
  have m3 : J * J * (G * P) ≤ K := le_trans (mul_le_mul_of_nonneg_right JJ (by positivity)) m1
  have k1 : |Dd * h1 + d2 * S| ≤ eL * J * (x * (G * P)) + e * (x * Q) :=
    (abs_add_le _ _).trans (add_le_add (P' bD hh1) (P' b2 hS))
  have m4 : |d11 * a + d12 * b - e12 * bW| ≤ e * (c * (J * P)) + e * (8 * c * J) + e * (4 * J) :=
    (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (P' b11 ha) (P' b12 hb)))
      (P' be hbW))
  have m5 : |d12 * a + d22 * b| ≤ e * (c * (J * P)) + e * (8 * c * J) :=
    (abs_add_le _ _).trans (add_le_add (P' b12 ha) (P' b22 hb))
  have T1 := P' bD hh2
  have T2 := P' m4 hh1
  have T3 := P' m5 hS
  have hS'' : |S'| ≤ 4 * J * (x * (G * P) + x * Q) :=
    hS'.trans (mul_le_mul_of_nonneg_left (add_le_add hh1 hS) (by positivity))
  have T4 := P' b2 hS''
  have T5 : |Dd * h1 + d2 * S| * t ≤ (eL * J * (x * (G * P)) + e * (x * Q)) * (4 * J) :=
    mul_le_mul k1 ht ht0 (by positivity)
  have s1 := abs_add_le (Dd * h2 + (d11 * a + d12 * b - e12 * bW) * h1 + (d12 * a + d22 * b) * S)
    (d2 * S')
  have s2 := abs_add_le (Dd * h2 + (d11 * a + d12 * b - e12 * bW) * h1) ((d12 * a + d22 * b) * S)
  have s3 := abs_add_le (Dd * h2) ((d11 * a + d12 * b - e12 * bW) * h1)
  -- bound each right-hand side by multiples of `x K`, `x L`
  have r1 : eL * J * (x * (G * P * P)) = eL * x * K := by rw [hK]; ring
  have r2 : (e * (c * (J * P)) + e * (8 * c * J) + e * (4 * J)) * (x * (G * P)) ≤
      e * (9 * c + 4) * x * K := by
    have q1 : J * P * (G * P) = K := by rw [hK]; ring
    have q2 : J * (G * P) ≤ K := m1
    have := mul_le_mul_of_nonneg_left q2 (show 0 ≤ e * x * (8 * c + 4) by positivity)
    have e1 : (e * (c * (J * P)) + e * (8 * c * J) + e * (4 * J)) * (x * (G * P)) =
        e * c * x * (J * P * (G * P)) + e * x * (8 * c + 4) * (J * (G * P)) := by ring
    rw [e1, q1]; linarith [this]
  have r3 : (e * (c * (J * P)) + e * (8 * c * J)) * (x * Q) ≤ e * (9 * c) * x * L := by
    have e1 : (e * (c * (J * P)) + e * (8 * c * J)) * (x * Q) =
        e * c * x * L + e * (8 * c) * x * (J * Q) := by rw [hL]; ring
    have := mul_le_mul_of_nonneg_left m2 (show 0 ≤ e * (8 * c) * x by positivity)
    rw [e1]; linarith [this]
  have r4 : e * (4 * J * (x * (G * P) + x * Q)) ≤ 4 * e * x * K + 4 * e * x * L := by
    have e1 : e * (4 * J * (x * (G * P) + x * Q)) = 4 * e * x * (J * (G * P)) + 4 * e * x * (J * Q) := by
      ring
    have a1 := mul_le_mul_of_nonneg_left m1 (show 0 ≤ 4 * e * x by positivity)
    have a2 := mul_le_mul_of_nonneg_left m2 (show 0 ≤ 4 * e * x by positivity)
    rw [e1]; linarith
  have r5 : (eL * J * (x * (G * P)) + e * (x * Q)) * (4 * J) ≤ 4 * eL * x * K + 4 * e * x * L := by
    have e1 : (eL * J * (x * (G * P)) + e * (x * Q)) * (4 * J) =
        4 * eL * x * (J * J * (G * P)) + 4 * e * x * (J * Q) := by ring
    have a1 := mul_le_mul_of_nonneg_left m3 (show 0 ≤ 4 * eL * x by positivity)
    have a2 := mul_le_mul_of_nonneg_left m2 (show 0 ≤ 4 * e * x by positivity)
    rw [e1]; linarith
  have k1' : eL * J * (x * (G * P)) + e * (x * Q) = eL * x * (J * G * P) + e * x * Q := by ring
  refine ⟨k1.trans (le_of_eq k1'), ?_⟩
  have hfin : (5 * eL + e * (9 * c + 8)) * x * (G * P * P * J + J * P * Q) =
      5 * eL * x * K + e * (9 * c + 8) * x * K + 5 * eL * x * L + e * (9 * c + 8) * x * L := by
    rw [hK, hL]; ring
  rw [hfin]
  have n1 : 0 ≤ eL * x * L := by positivity
  have n2 : 0 ≤ eL * x * K := by positivity
  have n3 : 0 ≤ e * x * K := by positivity
  have n4 : 0 ≤ e * x * L := by positivity
  rw [r1] at T1
  have T2' := T2.trans r2
  have T3' := T3.trans r3
  have T4' := T4.trans r4
  have T5' := T5.trans r5
  linarith [T1, T2', T3', T4', T5', s1, s2, s3, n1, n2, n3, n4]

/-! ### Local singular-integral interfaces -/

/-- Blueprint: def:c10_local_kernel_pair.  The value envelope
`ω₀(s) = min(|s|², 1) / |s|^α` for `s ≠ 0`, `ω₀(0) = 0`. -/
def c10_local_kernel_pair_omega0 (α s : ℝ) : ℝ :=
  if s = 0 then 0 else min (|s| ^ 2) 1 / |s| ^ α

/-- Blueprint: def:c10_local_kernel_pair.  The derivative envelope
`ω₁(s) = min(|s|, 1) / |s|^α` for `s ≠ 0`, `ω₁(0) = 0`. -/
def c10_local_kernel_pair_omega1 (α s : ℝ) : ℝ :=
  if s = 0 then 0 else min |s| 1 / |s| ^ α

/-- Blueprint: def:c10_local_kernel_pair.  `(H, J)` is a dominated kernel pair on `U` with
constant `A` (exponent `α`): both are Borel on `ℝ²`; they vanish on the diagonal over `U`; for each
fixed `z`, `H(·,z)` is locally Lipschitz on `U \ {z}` with `∂_y H(y,z) = J(y,z)` for a.e.
`y ∈ U \ {z}`; `|H(y,z)| ≤ A ω₀(y-z)` for `y ∈ U`, `z ≠ y`; and outside one null set `E` of `y`
(independent of `z`), `|J(y,z)| ≤ A ω₁(y-z)` for all `z ≠ y`.
(The standing assumptions `1 < α < 2`, `U` a nonempty open interval, `A ≥ 0` are hypotheses of
the lemmas using this predicate.) -/
def c10_local_kernel_pair (α : ℝ) (U : Set ℝ) (A : ℝ) (H J : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry H) ∧ Measurable (Function.uncurry J) ∧
  (∀ y ∈ U, H y y = 0 ∧ J y y = 0) ∧
  (∀ z : ℝ, LocallyLipschitzOn (U \ {z}) (fun y => H y z) ∧
    ∀ᵐ y, y ∈ U \ {z} → HasDerivAt (fun y' => H y' z) (J y z) y) ∧
  (∀ y ∈ U, ∀ z : ℝ, z ≠ y → |H y z| ≤ A * c10_local_kernel_pair_omega0 α (y - z)) ∧
  (∃ E : Set ℝ, volume E = 0 ∧
    ∀ y ∈ U \ E, ∀ z : ℝ, z ≠ y → |J y z| ≤ A * c10_local_kernel_pair_omega1 α (y - z))

/-- Helper: closed forms of the envelopes (the diagonal convention is automatic). -/
theorem c10_aux_omega_eq (α s : ℝ) (hα : 0 < α) :
    c10_local_kernel_pair_omega0 α s = min (|s| ^ 2) 1 / |s| ^ α ∧
    c10_local_kernel_pair_omega1 α s = min |s| 1 / |s| ^ α := by
  unfold c10_local_kernel_pair_omega0 c10_local_kernel_pair_omega1
  split_ifs with h
  · subst h; simp [Real.zero_rpow hα.ne']
  · exact ⟨rfl, rfl⟩

/-- Helper: radial profile of the envelopes on `(0, r)` (`r ≤ 1`) and on `(1,∞)`. -/
theorem c10_aux_omega_radial (α : ℝ) (hα : 1 < α) (hα2 : α < 2) (k : ℕ) (hk : k = 1 ∨ k = 2)
    (T : Set ℝ) (hT : MeasurableSet T) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hTs : Ioi 0 ∩ T = Ioo 0 r ∨ Ioi 0 ∩ T = Ioi 0) :
    IntegrableOn (fun t : ℝ => min (t ^ k) 1 / t ^ α) (Ioi 0 ∩ T) ∧
    (∫ t in Ioi 0 ∩ T, min (t ^ k) 1 / t ^ α) =
      if Ioi 0 ∩ T = Ioo 0 r then r ^ ((k : ℝ) + 1 - α) / ((k : ℝ) + 1 - α)
      else 1 / ((k : ℝ) + 1 - α) + 1 / (α - 1) := by
  have hk1 : (1 : ℝ) ≤ k := by rcases hk with h | h <;> subst h <;> norm_num
  have hk2 : (k : ℝ) ≤ 2 := by rcases hk with h | h <;> subst h <;> norm_num
  have hpos : 0 < (k : ℝ) + 1 - α := by linarith
  have e1 : ∀ s : ℝ, 0 < s → s ≤ 1 → min (s ^ k) 1 / s ^ α = s ^ ((k : ℝ) - α) := fun s hs hs1 => by
    rw [min_eq_left (pow_le_one₀ hs.le hs1), Real.rpow_sub hs, Real.rpow_natCast]
  have i1 : ∀ b, 0 < b → b ≤ 1 → IntegrableOn (fun t : ℝ => min (t ^ k) 1 / t ^ α) (Ioc 0 b) ∧
      (∫ t in Ioc 0 b, min (t ^ k) 1 / t ^ α) = b ^ ((k : ℝ) + 1 - α) / ((k : ℝ) + 1 - α) := by
    intro b hb hb1
    have eq : EqOn (fun t : ℝ => min (t ^ k) 1 / t ^ α) (fun t => t ^ ((k : ℝ) - α)) (Ioc 0 b) :=
      fun t ht => e1 t ht.1 (ht.2.trans hb1)
    have ii : IntegrableOn (fun t : ℝ => t ^ ((k : ℝ) - α)) (Ioc 0 b) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine ⟨ii.congr_fun eq.symm measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc eq, ← intervalIntegral.integral_of_le hb.le,
      integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
    rw [show (k : ℝ) - α + 1 = (k : ℝ) + 1 - α by ring]; ring
  rcases hTs with h | h
  · rw [if_pos h, h]
    have hae : (Ioo (0 : ℝ) r) =ᵐ[volume] Ioc 0 r := Ioo_ae_eq_Ioc
    obtain ⟨a, b⟩ := i1 r hr hr1
    exact ⟨a.congr_set_ae hae, by rw [setIntegral_congr_set hae, b]⟩
  · have hne : Ioi (0 : ℝ) ∩ T ≠ Ioo 0 r := by
      rw [h]; intro he
      have : (r + 1) ∈ Ioi (0 : ℝ) := by simp; linarith
      rw [he] at this; exact absurd this.2 (by linarith)
    rw [if_neg hne, h]
    obtain ⟨a, b⟩ := i1 1 one_pos le_rfl
    have e2 : EqOn (fun t : ℝ => min (t ^ k) 1 / t ^ α) (fun t => t ^ (-α)) (Ioi 1) :=
      fun t ht => by
        have ht' : (1 : ℝ) < t := ht
        simp only
        rw [min_eq_right (one_le_pow₀ ht'.le), Real.rpow_neg (by linarith), one_div]
    have i2 : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    have j2 := i2.congr_fun e2.symm measurableSet_Ioi
    have hU : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
    refine ⟨hU ▸ a.union j2, ?_⟩
    rw [← hU, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi a j2, b,
      setIntegral_congr_fun measurableSet_Ioi e2, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
      Real.one_rpow, Real.one_rpow]
    have : α - 1 ≠ 0 := by linarith
    rw [show -α + 1 = -(α - 1) by ring]
    field_simp

/-- Blueprint: lem:c10_kernel_envelopes.  `ω₀, ω₁` are nonnegative, Borel and integrable, with
`∫ ω₀ = 2/(3-α) + 2/(α-1)`, `∫ ω₁ = 2/(2-α) + 2/(α-1)`, and for `0 < r ≤ 1`
`∫_{|s|<r} ω₀ = 2 r^{3-α}/(3-α)`, `∫_{|s|<r} ω₁ = 2 r^{2-α}/(2-α)`. -/
theorem c10_kernel_envelopes (α : ℝ) (hα : 1 < α) (hα2 : α < 2) :
    (∀ s, 0 ≤ c10_local_kernel_pair_omega0 α s) ∧ (∀ s, 0 ≤ c10_local_kernel_pair_omega1 α s) ∧
    Measurable (c10_local_kernel_pair_omega0 α) ∧ Measurable (c10_local_kernel_pair_omega1 α) ∧
    Integrable (c10_local_kernel_pair_omega0 α) ∧ Integrable (c10_local_kernel_pair_omega1 α) ∧
    (∫ s, c10_local_kernel_pair_omega0 α s) = 2 / (3 - α) + 2 / (α - 1) ∧
    (∫ s, c10_local_kernel_pair_omega1 α s) = 2 / (2 - α) + 2 / (α - 1) ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∫ s in {s : ℝ | |s| < r}, c10_local_kernel_pair_omega0 α s) = 2 * r ^ (3 - α) / (3 - α) ∧
      (∫ s in {s : ℝ | |s| < r}, c10_local_kernel_pair_omega1 α s) = 2 * r ^ (2 - α) / (2 - α) := by
  have hα0 : 0 < α := by linarith
  have h0 : c10_local_kernel_pair_omega0 α = fun s => (fun t : ℝ => min (t ^ 2) 1 / t ^ α) |s| :=
    funext fun s => (c10_aux_omega_eq α s hα0).1
  have h1 : c10_local_kernel_pair_omega1 α = fun s => (fun t : ℝ => min (t ^ 1) 1 / t ^ α) |s| :=
    funext fun s => by
      show _ = min (|s| ^ 1) 1 / |s| ^ α
      rw [(c10_aux_omega_eq α s hα0).2, pow_one]
  have full : ∀ k : ℕ, (k = 1 ∨ k = 2) →
      Integrable (fun s : ℝ => (fun t : ℝ => min (t ^ k) 1 / t ^ α) |s|) ∧
      (∫ s, (fun t : ℝ => min (t ^ k) 1 / t ^ α) |s|) =
        2 * (1 / ((k : ℝ) + 1 - α) + 1 / (α - 1)) := by
    intro k hk
    obtain ⟨a, b⟩ := c10_aux_omega_radial α hα hα2 k hk univ MeasurableSet.univ 1 one_pos le_rfl
      (Or.inr (inter_univ _))
    have hne : Ioi (0 : ℝ) ∩ univ ≠ Ioo 0 1 := by
      rw [inter_univ]; intro he
      have : (2 : ℝ) ∈ Ioi (0 : ℝ) := by simp
      rw [he] at this; exact absurd this.2 (by norm_num)
    rw [if_neg hne, inter_univ] at b
    rw [inter_univ] at a
    obtain ⟨c, d⟩ := c10_aux_radial (g := fun t : ℝ => min (t ^ k) 1 / t ^ α) (S := univ)
      (T := univ) MeasurableSet.univ (fun _ => by simp) (by rw [inter_univ]; exact a)
    rw [integrableOn_univ] at c
    rw [setIntegral_univ, inter_univ, b] at d
    exact ⟨c, d⟩
  have trunc : ∀ k : ℕ, (k = 1 ∨ k = 2) → ∀ r : ℝ, 0 < r → r ≤ 1 →
      (∫ s in {s : ℝ | |s| < r}, (fun t : ℝ => min (t ^ k) 1 / t ^ α) |s|) =
        2 * (r ^ ((k : ℝ) + 1 - α) / ((k : ℝ) + 1 - α)) := by
    intro k hk r hr hr1
    have hT : Ioi (0 : ℝ) ∩ Iio r = Ioo 0 r := Ioi_inter_Iio
    obtain ⟨a, b⟩ := c10_aux_omega_radial α hα hα2 k hk (Iio r) measurableSet_Iio r hr hr1
      (Or.inl hT)
    rw [if_pos hT] at b
    obtain ⟨_, d⟩ := c10_aux_radial (g := fun t : ℝ => min (t ^ k) 1 / t ^ α)
      (S := {s : ℝ | |s| < r}) (T := Iio r) measurableSet_Iio (fun _ => Iff.rfl) a
    rw [d, b]
  have nn : ∀ k : ℕ, ∀ s : ℝ, 0 ≤ (fun t : ℝ => min (t ^ k) 1 / t ^ α) |s| := fun k s =>
    div_nonneg (le_min (pow_nonneg (abs_nonneg _) _) zero_le_one)
      (Real.rpow_nonneg (abs_nonneg _) _)
  have meas : ∀ k : ℕ, Measurable (fun s : ℝ => (fun t : ℝ => min (t ^ k) 1 / t ^ α) |s|) :=
    fun k => by fun_prop
  obtain ⟨I2, V2⟩ := full 2 (Or.inr rfl)
  obtain ⟨I1, V1⟩ := full 1 (Or.inl rfl)
  refine ⟨fun s => h0 ▸ nn 2 s, fun s => h1 ▸ nn 1 s, h0 ▸ meas 2, h1 ▸ meas 1, h0 ▸ I2,
    h1 ▸ I1, ?_, ?_, fun r hr hr1 => ⟨?_, ?_⟩⟩
  · rw [h0, V2]; push_cast; rw [show (2 : ℝ) + 1 - α = 3 - α by ring]; ring
  · rw [h1, V1]; push_cast; rw [show (1 : ℝ) + 1 - α = 2 - α by ring]; ring
  · rw [h0, trunc 2 (Or.inr rfl) r hr hr1]; push_cast
    rw [show (2 : ℝ) + 1 - α = 3 - α by ring]; ring
  · rw [h1, trunc 1 (Or.inl rfl) r hr hr1]; push_cast
    rw [show (1 : ℝ) + 1 - α = 2 - α by ring]; ring

/-- Helper: a measurable function essentially bounded on `[a,b]` is interval integrable there and
`|∫_a^b g| ≤ ‖g‖_{L^∞[a,b]} |b-a|`; moreover `|g| ≤ ‖g‖_{L^∞[a,b]}` a.e. on `[a,b]`. -/
theorem c10_aux_Linf_interval {g : ℝ → ℝ} (hg : AEStronglyMeasurable g volume) {a b : ℝ}
    (hab : a ≤ b) (hb : eLpNorm g ⊤ (volume.restrict (Icc a b)) < ⊤) :
    IntervalIntegrable g volume a b ∧
    (∀ᵐ x, x ∈ Icc a b → |g x| ≤ (eLpNorm g ⊤ (volume.restrict (Icc a b))).toReal) ∧
    |∫ x in a..b, g x| ≤ (eLpNorm g ⊤ (volume.restrict (Icc a b))).toReal * |b - a| := by
  set e := eLpNorm g ⊤ (volume.restrict (Icc a b))
  have hmem : MemLp g ⊤ (volume.restrict (Icc a b)) := hb
  have hint : IntegrableOn g (Icc a b) := hmem.integrable le_top
  have hII : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hint
  have hae : ∀ᵐ x, x ∈ Icc a b → |g x| ≤ e.toReal := by
    have h1 : ∀ᵐ x ∂(volume.restrict (Icc a b)), ‖g x‖ₑ ≤ e := by
      have := ae_le_eLpNormEssSup (f := g) (μ := volume.restrict (Icc a b))
      simp only [e, eLpNorm_exponent_top hg.restrict]; exact this
    rw [ae_restrict_iff' measurableSet_Icc] at h1
    filter_upwards [h1] with x hx hxm
    have := hx hxm
    rw [Real.enorm_eq_ofReal_abs] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hb.ne).1 this
  refine ⟨hII, hae, ?_⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := a) (b := b) (C := e.toReal)
    (f := g) (by
      filter_upwards [hae] with x hx hx'
      rw [Real.norm_eq_abs]; exact hx (uIoc_subset_uIcc hx' |> fun h => by
        rwa [uIcc_of_le hab] at h))
  rwa [Real.norm_eq_abs] at this

/-- Helper: for `F` locally Lipschitz on an open `U ⊇ [a,b]` with `F' = G` a.e. on `U`,
`F(b) - F(a) = ∫_a^b G`. -/
theorem c10_aux_ftc_locLip {U : Set ℝ} (hU : IsOpen U) {F G : ℝ → ℝ} (hF : LocallyLipschitzOn U F)
    (hFG : ∀ᵐ y, y ∈ U → HasDerivAt F (G y) y) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U) :
    F b - F a = ∫ y in a..b, G y := by
  obtain ⟨K, hK⟩ := (hF.mono hsub).exists_lipschitzOnWith_of_compact isCompact_Icc
  have hK' : LipschitzOnWith K F (uIcc a b) := by rwa [uIcc_of_le hab]
  rw [← hK'.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hFG] with y hy hy'
  have : y ∈ Icc a b := by
    rw [uIoc_of_le hab] at hy'; exact Ioc_subset_Icc_self hy'
  exact (hy (hsub this)).deriv

/-- Blueprint: lem:c10_local_weak_limit.  Let `U` be an open interval, `F_n` locally Lipschitz on
`U`, `G_n, G` measurable and locally essentially bounded on `U`, `F_n' = G_n` a.e. on `U`. If
`F_n → F` locally uniformly on `U` and `‖G_n - G‖_{L^∞(I)} → 0` on every compact interval
`I ⊆ U`, then `F` is locally Lipschitz on `U`, `F' = G` a.e. on `U`, and for `[a,b] ⊆ U`:
`F(b) - F(a) = ∫_a^b G` and `|F(b) - F(a)| ≤ ‖G‖_{L^∞([a,b])} |b - a|`. -/
theorem c10_local_weak_limit (U : Set ℝ) (hU : IsOpen U) (hUc : U.OrdConnected)
    (F G : ℕ → ℝ → ℝ) (F₀ G₀ : ℝ → ℝ)
    (hF : ∀ n, LocallyLipschitzOn U (F n))
    (hGm : ∀ n, Measurable (G n)) (hG₀m : Measurable G₀)
    (hGb : ∀ n, ∀ a b : ℝ, Icc a b ⊆ U → eLpNorm (G n) ⊤ (volume.restrict (Icc a b)) < ⊤)
    (hG₀b : ∀ a b : ℝ, Icc a b ⊆ U → eLpNorm G₀ ⊤ (volume.restrict (Icc a b)) < ⊤)
    (hFG : ∀ n, ∀ᵐ y, y ∈ U → HasDerivAt (F n) (G n y) y)
    (hFconv : TendstoLocallyUniformlyOn F F₀ atTop U)
    (hGconv : ∀ a b : ℝ, Icc a b ⊆ U →
      Tendsto (fun n => eLpNorm (fun y => G n y - G₀ y) ⊤ (volume.restrict (Icc a b))) atTop
        (nhds 0)) :
    LocallyLipschitzOn U F₀ ∧ (∀ᵐ y, y ∈ U → HasDerivAt F₀ (G₀ y) y) ∧
    ∀ a b : ℝ, a < b → Icc a b ⊆ U →
      IntervalIntegrable G₀ volume a b ∧ F₀ b - F₀ a = (∫ y in a..b, G₀ y) ∧
      |F₀ b - F₀ a| ≤ (eLpNorm G₀ ⊤ (volume.restrict (Icc a b))).toReal * |b - a| := by
  -- pointwise convergence on `U`
  have hpt : ∀ x ∈ U, Tendsto (fun n => F n x) atTop (nhds (F₀ x)) := fun x hx =>
    hFconv.tendsto_at hx
  -- the increment identity on every compact subinterval (with `a ≤ b`)
  have key : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → F₀ b - F₀ a = ∫ y in a..b, G₀ y := by
    intro a b hab hsub
    have ha : a ∈ U := hsub (left_mem_Icc.2 hab)
    have hb : b ∈ U := hsub (right_mem_Icc.2 hab)
    have hn : ∀ n, F n b - F n a = ∫ y in a..b, G n y := fun n =>
      c10_aux_ftc_locLip hU (hF n) (hFG n) hab hsub
    have hlim1 : Tendsto (fun n => F n b - F n a) atTop (nhds (F₀ b - F₀ a)) :=
      (hpt b hb).sub (hpt a ha)
    have hlim2 : Tendsto (fun n => ∫ y in a..b, G n y) atTop (nhds (∫ y in a..b, G₀ y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hconv := hGconv a b hsub
      have hfin : ∀ᶠ n in atTop, eLpNorm (fun y => G n y - G₀ y) ⊤ (volume.restrict (Icc a b)) < ⊤ :=
        (ENNReal.tendsto_nhds_zero.1 hconv) 1 one_pos |>.mono fun n hn =>
          lt_of_le_of_lt hn ENNReal.one_lt_top
      have htr : Tendsto (fun n =>
          (eLpNorm (fun y => G n y - G₀ y) ⊤ (volume.restrict (Icc a b))).toReal * |b - a|)
          atTop (nhds 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
        simpa using this.mul_const |b - a|
      refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ htr
      filter_upwards [hfin] with n hn
      have hI0 := (c10_aux_Linf_interval hG₀m.aestronglyMeasurable hab (hG₀b a b hsub)).1
      have hIn := (c10_aux_Linf_interval (hGm n).aestronglyMeasurable hab (hGb n a b hsub)).1
      rw [← intervalIntegral.integral_sub hIn hI0, Real.norm_eq_abs]
      exact (c10_aux_Linf_interval ((hGm n).sub hG₀m).aestronglyMeasurable hab hn).2.2
    rw [← funext hn] at hlim2
    exact tendsto_nhds_unique hlim1 hlim2
  -- the Lipschitz increment bound
  have bnd : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → ∀ c d : ℝ, c ∈ Icc a b → d ∈ Icc a b →
      |F₀ d - F₀ c| ≤ (eLpNorm G₀ ⊤ (volume.restrict (Icc a b))).toReal * |d - c| := by
    intro a b hab hsub c d hc hd
    wlog hcd : c ≤ d generalizing c d
    · have := this d c hd hc (le_of_not_ge hcd)
      rwa [abs_sub_comm, abs_sub_comm c d] at this
    have hsub' : Icc c d ⊆ Icc a b := Icc_subset_Icc hc.1 hd.2
    rw [key c d hcd (hsub'.trans hsub)]
    have hfin : eLpNorm G₀ ⊤ (volume.restrict (Icc c d)) ≤
        eLpNorm G₀ ⊤ (volume.restrict (Icc a b)) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hsub' le_rfl)
    have h := (c10_aux_Linf_interval hG₀m.aestronglyMeasurable hcd
      (lt_of_le_of_lt hfin (hG₀b a b hsub))).2.2
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    exact ENNReal.toReal_mono (hG₀b a b hsub).ne hfin
  refine ⟨?_, ?_, fun a b hab hsub => ⟨(c10_aux_Linf_interval hG₀m.aestronglyMeasurable hab.le
    (hG₀b a b hsub)).1, key a b hab.le hsub, bnd a b hab.le hsub a b (left_mem_Icc.2 hab.le)
      (right_mem_Icc.2 hab.le)⟩⟩
  · -- local Lipschitz
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hsub : Icc (x - δ / 2) (x + δ / 2) ⊆ U := fun y hy => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])
    refine ⟨(eLpNorm G₀ ⊤ (volume.restrict (Icc (x - δ / 2) (x + δ / 2)))).toNNReal,
      Icc (x - δ / 2) (x + δ / 2), ?_, ?_⟩
    · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    · refine LipschitzOnWith.of_dist_le_mul fun c hc d hd => ?_
      rw [Real.dist_eq, Real.dist_eq]
      have := bnd _ _ (by linarith) hsub d c hd hc
      simpa [ENNReal.coe_toNNReal_eq_toReal] using this
  · -- a.e. derivative: Lebesgue differentiation on countably many rational intervals
    have hq : ∀ q : ℚ × ℚ, ∀ᵐ y, Icc (q.1 : ℝ) q.2 ⊆ U → y ∈ Ioo (q.1 : ℝ) q.2 →
        HasDerivAt F₀ (G₀ y) y := by
      intro q
      by_cases hsub : Icc (q.1 : ℝ) q.2 ⊆ U
      · by_cases hle : (q.1 : ℝ) ≤ q.2
        · have hII := (c10_aux_Linf_interval hG₀m.aestronglyMeasurable hle (hG₀b _ _ hsub)).1
          filter_upwards [hII.ae_hasDerivAt_integral] with y hy _ hyI
          have hyc : y ∈ uIcc (q.1 : ℝ) q.2 := by
            rw [uIcc_of_le hle]; exact Ioo_subset_Icc_self hyI
          have hd := hy hyc (q.1 : ℝ) (by rw [uIcc_of_le hle]; exact left_mem_Icc.2 hle)
          have hd' := hd.const_add (F₀ q.1)
          refine hd'.congr_of_eventuallyEq ?_
          filter_upwards [Ioo_mem_nhds hyI.1 hyI.2] with w hw
          have := key q.1 w hw.1.le ((Icc_subset_Icc le_rfl hw.2.le).trans hsub)
          linarith
        · exact Eventually.of_forall fun y _ hy => absurd (hy.1.trans hy.2).le hle
      · exact Eventually.of_forall fun y h => absurd h hsub
    filter_upwards [ae_all_iff.2 hq] with y hy hyU
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU y hyU
    obtain ⟨q1, hq1, hq1'⟩ := exists_rat_btwn (show y - δ / 2 < y by linarith)
    obtain ⟨q2, hq2, hq2'⟩ := exists_rat_btwn (show y < y + δ / 2 by linarith)
    refine hy (q1, q2) (fun w hw => hball ?_) ⟨hq1', hq2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2]

/-- Helper: properties of the diagonal cutoff `ϑ`. -/
theorem c10_aux_theta {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθ0 : ∀ x ∈ Icc (-1 : ℝ) 1, θ x = 0) (hθ1 : ∀ x, x ∉ Ioo (-2 : ℝ) 2 → θ x = 1)
    {Mθ : ℝ} (hMθ : ∀ x, |deriv θ x| ≤ Mθ) :
    Differentiable ℝ θ ∧ Continuous θ ∧ Continuous (deriv θ) ∧ 0 ≤ Mθ ∧
    (∀ x, |x| ≤ 1 → θ x = 0) ∧ (∀ x, 2 ≤ |x| → θ x = 1) ∧
    (∀ x, deriv θ x ≠ 0 → 1 ≤ |x| ∧ |x| ≤ 2) := by
  have hd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hc' : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  have z0 : ∀ x, |x| ≤ 1 → θ x = 0 := fun x hx => hθ0 x (abs_le.1 hx)
  have z1 : ∀ x, 2 ≤ |x| → θ x = 1 := fun x hx => hθ1 x (fun h => by
    have := abs_lt.2 h; linarith)
  refine ⟨hd, hd.continuous, hc', (abs_nonneg _).trans (hMθ 0), z0, z1, fun x hx => ?_⟩
  by_contra hcon
  rcases not_and_or.1 hcon with h | h
  · push_neg at h
    have hev : θ =ᶠ[nhds x] fun _ => 0 := by
      have : {y : ℝ | |y| < 1} ∈ nhds x :=
        (isOpen_lt continuous_abs continuous_const).mem_nhds h
      filter_upwards [this] with y hy using z0 y (le_of_lt hy)
    exact hx (by rw [hev.deriv_eq]; simp)
  · push_neg at h
    have hev : θ =ᶠ[nhds x] fun _ => 1 := by
      have : {y : ℝ | 2 < |y|} ∈ nhds x :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds h
      filter_upwards [this] with y hy using z1 y (le_of_lt hy)
    exact hx (by rw [hev.deriv_eq]; simp)

/-- Helper: off the origin the envelopes are dominated by pure powers. -/
theorem c10_aux_omega_le_pow (α s : ℝ) (hs : s ≠ 0) :
    c10_local_kernel_pair_omega0 α s ≤ |s| ^ (2 - α) ∧
    c10_local_kernel_pair_omega1 α s ≤ |s| ^ (1 - α) := by
  have hp : 0 < |s| := abs_pos.2 hs
  unfold c10_local_kernel_pair_omega0 c10_local_kernel_pair_omega1
  rw [if_neg hs, if_neg hs]
  have hd : 0 < |s| ^ α := Real.rpow_pos_of_pos hp α
  constructor
  · rw [Real.rpow_sub hp, Real.rpow_two]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hd.le
  · rw [Real.rpow_sub hp, Real.rpow_one]
    exact div_le_div_of_nonneg_right (min_le_left _ _) hd.le

/-- Helper: integral of a truncated power, translated. -/
theorem c10_aux_ind_int (c q y : ℝ) (hc : 0 < c) (hq : -1 < q) :
    Integrable (fun z => (Icc (-c) c).indicator (fun s : ℝ => |s| ^ q) (y - z)) ∧
    (∫ z, (Icc (-c) c).indicator (fun s : ℝ => |s| ^ q) (y - z)) = 2 * c ^ (q + 1) / (q + 1) := by
  obtain ⟨hi, hv⟩ := c10_aux_ball q c hq hc
  have hI : Integrable ((Icc (-c) c).indicator (fun s : ℝ => |s| ^ q)) :=
    (integrable_indicator_iff measurableSet_Icc).2 hi
  refine ⟨hI.comp_sub_left y, ?_⟩
  rw [integral_sub_left_eq_self (fun s => (Icc (-c) c).indicator (fun s : ℝ => |s| ^ q) s) volume y,
    integral_indicator measurableSet_Icc, hv]

/-- Helper: an increment identity with an essentially bounded measurable derivative on an open
set gives local Lipschitz regularity and the a.e. derivative. -/
theorem c10_aux_primitive {U : Set ℝ} (hU : IsOpen U) {F G : ℝ → ℝ} (hG : Measurable G) {C : ℝ}
    (hC : ∀ᵐ y, y ∈ U → |G y| ≤ C)
    (hinc : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → F b - F a = ∫ y in a..b, G y) :
    LocallyLipschitzOn U F ∧ ∀ᵐ y, y ∈ U → HasDerivAt F (G y) y := by
  have hII : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U → IntervalIntegrable G volume a b := by
    intro a b hab hsub
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    refine Integrable.of_bound hG.aestronglyMeasurable C ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hC] with y hy hyI
    rw [Real.norm_eq_abs]; exact hy (hsub hyI)
  have bnd : ∀ c d : ℝ, c ≤ d → Icc c d ⊆ U → |F d - F c| ≤ C * |d - c| := by
    intro c d hcd hsub
    rw [hinc c d hcd hsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := c) (b := d) (C := C)
      (f := G) (by
        filter_upwards [hC] with y hy hy'
        rw [Real.norm_eq_abs]
        refine hy (hsub ?_)
        rw [uIoc_of_le hcd] at hy'; exact Ioc_subset_Icc_self hy')
    rwa [Real.norm_eq_abs] at this
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hsub : Icc (x - δ / 2) (x + δ / 2) ⊆ U := fun y hy => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])
    refine ⟨C.toNNReal, Icc (x - δ / 2) (x + δ / 2),
      mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun c hc d hd => ?_
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total d c with h | h
    · have := bnd d c h ((Icc_subset_Icc hd.1 hc.2).trans hsub)
      calc |F c - F d| ≤ C * |c - d| := this
        _ ≤ (C.toNNReal : ℝ) * |c - d| :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (abs_nonneg _)
    · have := bnd c d h ((Icc_subset_Icc hc.1 hd.2).trans hsub)
      rw [abs_sub_comm (F c), abs_sub_comm c]
      calc |F d - F c| ≤ C * |d - c| := this
        _ ≤ (C.toNNReal : ℝ) * |d - c| :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (abs_nonneg _)
  · have hq : ∀ q : ℚ × ℚ, ∀ᵐ y, Icc (q.1 : ℝ) q.2 ⊆ U → y ∈ Ioo (q.1 : ℝ) q.2 →
        HasDerivAt F (G y) y := by
      intro q
      by_cases hsub : Icc (q.1 : ℝ) q.2 ⊆ U
      · by_cases hle : (q.1 : ℝ) ≤ q.2
        · filter_upwards [(hII _ _ hle hsub).ae_hasDerivAt_integral] with y hy _ hyI
          have hyc : y ∈ uIcc (q.1 : ℝ) q.2 := by
            rw [uIcc_of_le hle]; exact Ioo_subset_Icc_self hyI
          have hd := (hy hyc (q.1 : ℝ) (by rw [uIcc_of_le hle]; exact left_mem_Icc.2 hle)).const_add
            (F q.1)
          refine hd.congr_of_eventuallyEq ?_
          filter_upwards [Ioo_mem_nhds hyI.1 hyI.2] with w hw
          have := hinc q.1 w hw.1.le ((Icc_subset_Icc le_rfl hw.2.le).trans hsub)
          linarith
        · exact Eventually.of_forall fun y _ hy => absurd (hy.1.trans hy.2).le hle
      · exact Eventually.of_forall fun y h => absurd h hsub
    filter_upwards [ae_all_iff.2 hq] with y hy hyU
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU y hyU
    obtain ⟨q1, hq1, hq1'⟩ := exists_rat_btwn (show y - δ / 2 < y by linarith)
    obtain ⟨q2, hq2, hq2'⟩ := exists_rat_btwn (show y < y + δ / 2 by linarith)
    refine hy (q1, q2) (fun w hw => hball ?_) ⟨hq1', hq2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hw.1, hw.2]

/-- Helper: a product of two bounded Lipschitz functions on a set is Lipschitz there. -/
theorem c10_aux_lipOn_mul {f g : ℝ → ℝ} {s : Set ℝ} {Kf Kg : NNReal} {Bf Bg : ℝ}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
    (hBf : ∀ x ∈ s, |f x| ≤ Bf) (hBg : ∀ x ∈ s, |g x| ≤ Bg) :
    LipschitzOnWith (Bf * Kg + Bg * Kf).toNNReal (fun x => f x * g x) s := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  have h1 := hf.dist_le_mul y hy z hz
  have h2 := hg.dist_le_mul y hy z hz
  have b1 := hBf y hy
  have b2 := hBg z hz
  simp only [Real.dist_eq] at *
  have e : f y * g y - f z * g z = f y * (g y - g z) + g z * (f y - f z) := by ring
  rw [e]
  have hKf0 : (0 : ℝ) ≤ Kf := Kf.2
  have hKg0 : (0 : ℝ) ≤ Kg := Kg.2
  calc |f y * (g y - g z) + g z * (f y - f z)|
      ≤ |f y| * |g y - g z| + |g z| * |f y - f z| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Bf * (Kg * |y - z|) + Bg * (Kf * |y - z|) := by
        apply add_le_add
        · exact mul_le_mul b1 h2 (abs_nonneg _) ((abs_nonneg _).trans b1)
        · exact mul_le_mul b2 h1 (abs_nonneg _) ((abs_nonneg _).trans b2)
    _ = (Bf * Kg + Bg * Kf) * |y - z| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _)

/-- Helper: common pointwise facts for the cutoff integrands of a dominated kernel pair. -/
theorem c10_aux_cutoff_setup (α : ℝ) (hα : 1 < α) (hα2 : α < 2) (U : Set ℝ) (A : ℝ) (hA : 0 ≤ A)
    (H J : ℝ → ℝ → ℝ) (hHJ : c10_local_kernel_pair α U A H J)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ01 : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ x ∈ Icc (-1 : ℝ) 1, θ x = 0) (hθ1 : ∀ x, x ∉ Ioo (-2 : ℝ) 2 → θ x = 1)
    (Mθ : ℝ) (hMθ : ∀ x, |deriv θ x| ≤ Mθ) (η : ℝ) (hη : 0 < η) :
    -- cutoff-derivative term
    (∀ y ∈ U, ∀ z, |η⁻¹ * deriv θ ((y - z) / η) * H y z| ≤
      η⁻¹ * Mθ * A * (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ (2 - α)) (y - z)) ∧
    -- removed value term
    (∀ y ∈ U, ∀ z, |(θ ((y - z) / η) - 1) * H y z| ≤
      A * (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ (2 - α)) (y - z)) ∧
    -- removed derivative term
    (∀ y ∈ U \ (Classical.choose hHJ.2.2.2.2.2), ∀ z, |(θ ((y - z) / η) - 1) * J y z| ≤
      A * (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ (1 - α)) (y - z)) ∧
    -- dominations by the envelopes
    (∀ y ∈ U, ∀ z, |θ ((y - z) / η) * H y z| ≤ A * c10_local_kernel_pair_omega0 α (y - z)) ∧
    (∀ y ∈ U, ∀ z, |H y z| ≤ A * c10_local_kernel_pair_omega0 α (y - z)) ∧
    (∀ y ∈ U \ (Classical.choose hHJ.2.2.2.2.2), ∀ z,
      |θ ((y - z) / η) * J y z| ≤ A * c10_local_kernel_pair_omega1 α (y - z) ∧
      |J y z| ≤ A * c10_local_kernel_pair_omega1 α (y - z)) ∧
    volume (Classical.choose hHJ.2.2.2.2.2) = 0 := by
  obtain ⟨hHm, hJm, hdiag, hloc, hHb, hE⟩ := hHJ
  set E := Classical.choose hE
  have hE0 : volume E = 0 := (Classical.choose_spec hE).1
  have hJb := (Classical.choose_spec hE).2
  obtain ⟨hθd, hθc, hθ'c, hM0, hθz, hθo, hθs⟩ := c10_aux_theta hθ hθ0 hθ1 hMθ
  obtain ⟨o0, o1, -⟩ := c10_kernel_envelopes α hα hα2
  have habs : ∀ y z : ℝ, |(y - z) / η| = |y - z| / η := fun y z => by
    rw [abs_div, abs_of_pos hη]
  have hind_nn : ∀ (q : ℝ) (s : ℝ), 0 ≤ (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ q) s :=
    fun q s => indicator_nonneg (fun s _ => Real.rpow_nonneg (abs_nonneg _) _) s
  have hind_eq : ∀ (q : ℝ) (s : ℝ), |s| ≤ 2 * η →
      (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ q) s = |s| ^ q := fun q s hs =>
    indicator_of_mem (abs_le.1 hs) _
  have hθabs : ∀ x, |θ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hθ01 x).1]; exact (hθ01 x).2
  have hθm1 : ∀ x, |θ x - 1| ≤ 1 := fun x => by
    rw [abs_le]; constructor <;> linarith [(hθ01 x).1, (hθ01 x).2]
  have hHle : ∀ y ∈ U, ∀ z, |H y z| ≤ A * c10_local_kernel_pair_omega0 α (y - z) := by
    intro y hy z
    by_cases hz : z = y
    · subst hz; rw [(hdiag z hy).1, abs_zero]
      exact mul_nonneg hA (o0 _)
    · exact hHb y hy z hz
  refine ⟨fun y hy z => ?_, fun y hy z => ?_, fun y hy z => ?_, fun y hy z => ?_, hHle,
    fun y hy z => ?_, hE0⟩
  · by_cases hd : deriv θ ((y - z) / η) = 0
    · rw [hd, mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hη.le) hM0) hA) (hind_nn _ _)
    · obtain ⟨h1, h2⟩ := hθs _ hd
      rw [habs, le_div_iff₀ hη, one_mul] at h1
      rw [habs, div_le_iff₀ hη] at h2
      have hz : z ≠ y := fun h => by subst h; simp at h1; linarith
      have hs0 : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
      rw [hind_eq _ _ (by linarith), abs_mul, abs_mul, abs_of_pos (inv_pos.2 hη)]
      have hH := (hHb y hy z hz).trans
        (mul_le_mul_of_nonneg_left (c10_aux_omega_le_pow α _ hs0).1 hA)
      have := mul_le_mul (hMθ ((y - z) / η)) hH (abs_nonneg _) hM0
      calc η⁻¹ * |deriv θ ((y - z) / η)| * |H y z|
          = η⁻¹ * (|deriv θ ((y - z) / η)| * |H y z|) := by ring
        _ ≤ η⁻¹ * (Mθ * (A * |y - z| ^ (2 - α))) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 hη.le)
        _ = _ := by ring
  · by_cases hs : |y - z| ≤ 2 * η
    · rw [hind_eq _ _ hs, abs_mul]
      by_cases hz : z = y
      · subst hz; rw [(hdiag z hy).1, abs_zero, mul_zero]
        exact mul_nonneg hA (Real.rpow_nonneg (abs_nonneg _) _)
      · have hs0 : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
        have hH := (hHb y hy z hz).trans
          (mul_le_mul_of_nonneg_left (c10_aux_omega_le_pow α _ hs0).1 hA)
        calc |θ ((y - z) / η) - 1| * |H y z| ≤ 1 * |H y z| :=
              mul_le_mul_of_nonneg_right (hθm1 _) (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hH
    · push_neg at hs
      rw [hθo _ (by rw [habs, le_div_iff₀ hη]; linarith), sub_self, zero_mul, abs_zero]
      exact mul_nonneg hA (hind_nn _ _)
  · by_cases hs : |y - z| ≤ 2 * η
    · rw [hind_eq _ _ hs, abs_mul]
      by_cases hz : z = y
      · subst hz; rw [(hdiag z hy.1).2, abs_zero, mul_zero]
        exact mul_nonneg hA (Real.rpow_nonneg (abs_nonneg _) _)
      · have hs0 : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
        have hJ := (hJb y hy z hz).trans
          (mul_le_mul_of_nonneg_left (c10_aux_omega_le_pow α _ hs0).2 hA)
        calc |θ ((y - z) / η) - 1| * |J y z| ≤ 1 * |J y z| :=
              mul_le_mul_of_nonneg_right (hθm1 _) (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hJ
    · push_neg at hs
      rw [hθo _ (by rw [habs, le_div_iff₀ hη]; linarith), sub_self, zero_mul, abs_zero]
      exact mul_nonneg hA (hind_nn _ _)
  · rw [abs_mul]
    calc |θ ((y - z) / η)| * |H y z| ≤ 1 * |H y z| :=
          mul_le_mul_of_nonneg_right (hθabs _) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hHle y hy z
  · have hJle : |J y z| ≤ A * c10_local_kernel_pair_omega1 α (y - z) := by
      by_cases hz : z = y
      · subst hz; rw [(hdiag z hy.1).2, abs_zero]; exact mul_nonneg hA (o1 _)
      · exact hJb y hy z hz
    refine ⟨?_, hJle⟩
    rw [abs_mul]
    calc |θ ((y - z) / η)| * |J y z| ≤ 1 * |J y z| :=
          mul_le_mul_of_nonneg_right (hθabs _) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hJle

/-- Helper: the power identities for the cutoff constants. -/
theorem c10_aux_cut_consts (α η : ℝ) (hη : 0 < η) :
    2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1) = 2 ^ (4 - α) / (3 - α) * η ^ (3 - α) ∧
    η⁻¹ * (2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1)) = 2 ^ (4 - α) / (3 - α) * η ^ (2 - α) ∧
    2 * (2 * η) ^ (1 - α + 1) / (1 - α + 1) = 2 ^ (3 - α) / (2 - α) * η ^ (2 - α) := by
  have h1 : ∀ q : ℝ, (2 * η) ^ q = 2 ^ q * η ^ q := fun q =>
    Real.mul_rpow (by norm_num) hη.le
  have h2 : ∀ q : ℝ, (2 : ℝ) ^ (q + 1) = 2 * 2 ^ q := fun q => by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have h3 : η ^ (3 - α) = η ^ (2 - α) * η := by
    rw [show (3 : ℝ) - α = (2 - α) + 1 by ring, Real.rpow_add hη, Real.rpow_one]
  have e1 : 2 - α + 1 = 3 - α := by ring
  have e2 : 1 - α + 1 = 2 - α := by ring
  have e4 : (4 : ℝ) - α = (3 - α) + 1 := by ring
  have e3 : (3 : ℝ) - α = (2 - α) + 1 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, h1, e4, h2]; ring
  · rw [e1, h1, e4, h2, h3]; field_simp
  · rw [e2, h1, e3, h2]; ring

/-- Blueprint: lem:c10_cutoff_weak_derivative.  For a dominated kernel pair `(H,J)` on `U`
(constant `A`, exponent `1 < α < 2`), a smooth cutoff `ϑ : ℝ → [0,1]`, `ϑ = 0` on `[-1,1]`,
`ϑ = 1` off `(-2,2)`, `|ϑ'| ≤ M_ϑ`, and `0 < η < 1/2`, the truncation
`F_η(y) = ∫ ϑ((y-z)/η) H(y,z) dz` converges absolutely on `U`, the two summands of
`G_η(y) = ∫ [ϑ((y-z)/η) J(y,z) + η⁻¹ ϑ'((y-z)/η) H(y,z)] dz` converge absolutely for a.e.
`y ∈ U`, `F_η` is locally Lipschitz on `U` with `F_η' = G_η` a.e. on `U`,
`‖G_η‖_{L^∞(U)} ≤ A (2/(2-α) + 2/(α-1) + 2^{4-α} M_ϑ η^{2-α}/(3-α))`, and
`F_η(b) - F_η(a) = ∫_a^b G_η` for `[a,b] ⊆ U`.
(`M_ϑ = ‖ϑ'‖_∞` is encoded by any upper bound `Mθ` for `|ϑ'|`.) -/
theorem c10_cutoff_weak_derivative (α : ℝ) (hα : 1 < α) (hα2 : α < 2) (U : Set ℝ)
    (hU : IsOpen U) (hUc : U.OrdConnected) (hUne : U.Nonempty) (A : ℝ) (hA : 0 ≤ A)
    (H J : ℝ → ℝ → ℝ) (hHJ : c10_local_kernel_pair α U A H J)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ01 : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ x ∈ Icc (-1 : ℝ) 1, θ x = 0) (hθ1 : ∀ x, x ∉ Ioo (-2 : ℝ) 2 → θ x = 1)
    (Mθ : ℝ) (hMθ : ∀ x, |deriv θ x| ≤ Mθ) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2) :
    (∀ y ∈ U, Integrable (fun z => θ ((y - z) / η) * H y z)) ∧
    (∀ᵐ y, y ∈ U → Integrable (fun z => θ ((y - z) / η) * J y z) ∧
      Integrable (fun z => η⁻¹ * deriv θ ((y - z) / η) * H y z)) ∧
    LocallyLipschitzOn U (fun y => ∫ z, θ ((y - z) / η) * H y z) ∧
    (∀ᵐ y, y ∈ U → HasDerivAt (fun y' => ∫ z, θ ((y' - z) / η) * H y' z)
      (∫ z, (θ ((y - z) / η) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z)) y) ∧
    (∀ᵐ y, y ∈ U →
      |∫ z, (θ ((y - z) / η) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z)| ≤
        A * (2 / (2 - α) + 2 / (α - 1) + 2 ^ (4 - α) * Mθ / (3 - α) * η ^ (2 - α))) ∧
    ∀ a b : ℝ, a < b → Icc a b ⊆ U →
      (∫ z, θ ((b - z) / η) * H b z) - (∫ z, θ ((a - z) / η) * H a z) =
        ∫ y in a..b, ∫ z, (θ ((y - z) / η) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z) := by
  obtain ⟨Bcut, -, -, Bθ, -, BJ, hE0⟩ :=
    c10_aux_cutoff_setup α hα hα2 U A hA H J hHJ θ hθ hθ01 hθ0 hθ1 Mθ hMθ η hη
  have hHm := hHJ.1
  have hJm := hHJ.2.1
  have hloc := hHJ.2.2.2.1
  set E := Classical.choose hHJ.2.2.2.2.2
  obtain ⟨o0, o1, mo0, mo1, io0, io1, -, v1, -⟩ := c10_kernel_envelopes α hα hα2
  obtain ⟨hθd, hθc, hθ'c, hM0, hθz, -, hθs⟩ := c10_aux_theta hθ hθ0 hθ1 hMθ
  have hθ00 : θ 0 = 0 := hθz 0 (by simp)
  have hθ'0 : deriv θ 0 = 0 := by
    by_contra h; have := (hθs 0 h).1; simp at this; linarith
  set ind := fun s : ℝ => (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ (2 - α)) s
    with hind
  set cst := η⁻¹ * Mθ * A with hcst
  have hcst0 : 0 ≤ cst := mul_nonneg (mul_nonneg (inv_nonneg.2 hη.le) hM0) hA
  have iind : ∀ y, Integrable (fun z => ind (y - z)) := fun y =>
    (c10_aux_ind_int (2 * η) (2 - α) y (by linarith) (by linarith)).1
  have vind : ∀ y, (∫ z, ind (y - z)) = 2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1) := fun y =>
    (c10_aux_ind_int (2 * η) (2 - α) y (by linarith) (by linarith)).2
  have hind_nn : ∀ s, 0 ≤ ind s :=
    fun s => indicator_nonneg (fun s _ => Real.rpow_nonneg (abs_nonneg _) _) s
  -- the dominating function
  set g : ℝ → ℝ → ℝ := fun y z => A * c10_local_kernel_pair_omega1 α (y - z) + cst * ind (y - z)
    with hg
  have hg_nn : ∀ y z, 0 ≤ g y z := fun y z => add_nonneg (mul_nonneg hA (o1 _))
    (mul_nonneg hcst0 (hind_nn _))
  have hg_int : ∀ y, Integrable (fun z => g y z) := fun y =>
    ((io1.comp_sub_left y).const_mul A).add ((iind y).const_mul cst)
  have hg_val : ∀ y, (∫ z, g y z) = A * (2 / (2 - α) + 2 / (α - 1)) +
      cst * (2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1)) := fun y => by
    simp only [hg]
    rw [integral_add ((io1.comp_sub_left y).const_mul A) ((iind y).const_mul cst),
      integral_const_mul, integral_const_mul, vind y,
      integral_sub_left_eq_self (fun s => c10_local_kernel_pair_omega1 α s) volume y, v1]
  have hgm : Measurable (fun q : ℝ × ℝ => g q.1 q.2) := by
    have h1 : Measurable (fun q : ℝ × ℝ => q.1 - q.2) := by fun_prop
    have hi : Measurable ind := by
      refine (Measurable.indicator ?_ measurableSet_Icc)
      fun_prop
    exact (measurable_const.mul (mo1.comp h1)).add (measurable_const.mul (hi.comp h1))
  -- the integrands
  set psi : ℝ → ℝ → ℝ := fun y z =>
    θ ((y - z) / η) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z with hpsi
  have hψm : Measurable (fun q : ℝ × ℝ => psi q.1 q.2) := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 - q.2) / η) := by fun_prop
    have hJ' : Measurable (fun q : ℝ × ℝ => J q.1 q.2) := hJm
    have hH' : Measurable (fun q : ℝ × ℝ => H q.1 q.2) := hHm
    exact ((hθc.comp h1).measurable.mul hJ').add
      ((measurable_const.mul (hθ'c.comp h1).measurable).mul hH')
  have hpsi_bd : ∀ y ∈ U \ E, ∀ z, |psi y z| ≤ g y z := by
    intro y hy z
    simp only [hpsi, hg]
    exact (abs_add_le _ _).trans (add_le_add (BJ y hy z).1 (Bcut y hy.1 z))
  have hHy : ∀ y, Measurable (H y) := fun y => hHm.comp measurable_prodMk_left
  have hJy : ∀ y, Measurable (J y) := fun y => hJm.comp measurable_prodMk_left
  have hφm : ∀ y, Measurable (fun z => θ ((y - z) / η) * H y z) := fun y =>
    ((hθc.comp (by fun_prop : Continuous fun z : ℝ => (y - z) / η)).measurable).mul (hHy y)
  have hφint : ∀ y ∈ U, Integrable (fun z => θ ((y - z) / η) * H y z) := fun y hy =>
    Integrable.mono' ((io0.comp_sub_left y).const_mul A) (hφm y).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact Bθ y hy z)
  have hnotE : ∀ᵐ y, y ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
  have hψy : ∀ y, Measurable (psi y) := fun y => by
    have h1 : Continuous (fun z : ℝ => (y - z) / η) := by fun_prop
    exact ((hθc.comp h1).measurable.mul (hJy y)).add
      ((measurable_const.mul (hθ'c.comp h1).measurable).mul (hHy y))
  have hψint : ∀ y ∈ U \ E, Integrable (psi y) := fun y hy =>
    Integrable.mono' (hg_int y) (hψy y).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hpsi_bd y hy z)
  have hGm : Measurable (fun y => ∫ z, psi y z) := by
    have h' : StronglyMeasurable (Function.uncurry psi) := hψm.stronglyMeasurable
    exact (h'.integral_prod_right (ν := volume)).measurable
  set K := A * (2 / (2 - α) + 2 / (α - 1)) + cst * (2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1))
    with hK
  have hGb : ∀ᵐ y, y ∈ U → |∫ z, psi y z| ≤ K := by
    filter_upwards [hnotE] with y hyE hyU
    rw [← hg_val y, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hg_int y)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hpsi_bd y ⟨hyU, hyE⟩ z)
  have hKeq : K = A * (2 / (2 - α) + 2 / (α - 1) + 2 ^ (4 - α) * Mθ / (3 - α) * η ^ (2 - α)) := by
    rw [hK, hcst, show η⁻¹ * Mθ * A * (2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1)) =
      Mθ * A * (η⁻¹ * (2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1))) by ring,
      (c10_aux_cut_consts α η hη).2.1]
    ring
  -- per-`z` regularity of the truncated integrand
  have hθL : ∀ z, LipschitzWith (Mθ / η).toNNReal (fun y => θ ((y - z) / η)) := by
    intro z
    have hL : LipschitzWith Mθ.toNNReal θ := lipschitzWith_of_nnnorm_deriv_le hθd fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0, Real.norm_eq_abs]
      exact hMθ x
    refine LipschitzWith.of_dist_le_mul fun y1 y2 => ?_
    have := hL.dist_le_mul ((y1 - z) / η) ((y2 - z) / η)
    rw [Real.coe_toNNReal _ hM0] at this
    rw [Real.coe_toNNReal _ (div_nonneg hM0 hη.le)]
    refine this.trans (le_of_eq ?_)
    rw [Real.dist_eq, Real.dist_eq, show (y1 - z) / η - (y2 - z) / η = (y1 - y2) / η by ring,
      abs_div, abs_of_pos hη]
    ring
  have hφloc : ∀ z, LocallyLipschitzOn U (fun y => θ ((y - z) / η) * H y z) := by
    intro z y0 hy0
    by_cases hyz : y0 = z
    · subst hyz
      refine ⟨0, Ioo (y0 - η) (y0 + η), mem_nhdsWithin_of_mem_nhds
        (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
      have h0 : ∀ y ∈ Ioo (y0 - η) (y0 + η), θ ((y - y0) / η) * H y y0 = 0 := fun y hy => by
        have : |(y - y0) / η| ≤ 1 := by
          rw [abs_div, abs_of_pos hη, div_le_one hη, abs_le]
          constructor <;> linarith [hy.1, hy.2]
        rw [hθz _ this, zero_mul]
      refine LipschitzOnWith.of_dist_le_mul fun y1 h1 y2 h2 => ?_
      rw [h0 y1 h1, h0 y2 h2, dist_self]; positivity
    · obtain ⟨K', t, ht, hK'⟩ := (hloc z).1 ⟨hy0, hyz⟩
      have ht' : t ∈ nhds y0 := by
        rwa [(hU.sdiff isClosed_singleton).nhdsWithin_eq ⟨hy0, hyz⟩] at ht
      obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.1 ht'
      have hs : Icc (y0 - δ / 2) (y0 + δ / 2) ⊆ t := fun y hy => hδt (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])
      have hy0s : y0 ∈ Icc (y0 - δ / 2) (y0 + δ / 2) := ⟨by linarith, by linarith⟩
      have hHs := hK'.mono hs
      refine ⟨_, Icc (y0 - δ / 2) (y0 + δ / 2), mem_nhdsWithin_of_mem_nhds
        (Icc_mem_nhds (by linarith) (by linarith)),
        c10_aux_lipOn_mul (Bf := 1) (Bg := |H y0 z| + K' * δ) (hθL z).lipschitzOnWith hHs
          (fun x _ => by rw [abs_of_nonneg (hθ01 _).1]; exact (hθ01 _).2) (fun x hx => ?_)⟩
      have := hHs.dist_le_mul x hx y0 hy0s
      rw [Real.dist_eq, Real.dist_eq] at this
      have hxy : |x - y0| ≤ δ := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
      have hK0 : (0 : ℝ) ≤ K' := K'.2
      have := abs_sub_abs_le_abs_sub (H x z) (H y0 z)
      nlinarith [mul_le_mul_of_nonneg_left hxy hK0]
  have hne : ∀ z : ℝ, ∀ᵐ y, y ≠ z := fun z => by
    rw [ae_iff]; simp [measure_singleton]
  have hφd : ∀ z, ∀ᵐ y, y ∈ U → HasDerivAt (fun y => θ ((y - z) / η) * H y z) (psi y z) y := by
    intro z
    filter_upwards [(hloc z).2, hne z] with y hy hyz hyU
    have hH := hy ⟨hyU, hyz⟩
    have hl : HasDerivAt (fun y => (y - z) / η) (1 / η) y :=
      ((hasDerivAt_id' y).sub_const z).div_const η
    have hc := ((hθd ((y - z) / η)).hasDerivAt.comp y hl).mul hH
    have hc' : HasDerivAt (fun y => θ ((y - z) / η) * H y z)
        (deriv θ ((y - z) / η) * (1 / η) * H y z + θ ((y - z) / η) * J y z) y := hc
    refine hc'.congr_deriv ?_
    show _ = θ ((y - z) / η) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z
    ring
  -- the increment identity (Fubini)
  have hinc : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ U →
      (∫ z, θ ((b - z) / η) * H b z) - (∫ z, θ ((a - z) / η) * H a z) =
        ∫ y in a..b, ∫ z, psi y z := by
    intro a b hab hsub
    have ha := hsub (left_mem_Icc.2 hab)
    have hb := hsub (right_mem_Icc.2 hab)
    rw [← integral_sub (hφint b hb) (hφint a ha)]
    have step : ∀ z, θ ((b - z) / η) * H b z - θ ((a - z) / η) * H a z =
        ∫ y in Ioc a b, psi y z := fun z => by
      rw [c10_aux_ftc_locLip hU (hφloc z) (hφd z) hab hsub, intervalIntegral.integral_of_le hab]
    simp_rw [step]
    rw [intervalIntegral.integral_of_le hab]
    have hA' : ∀ᵐ y ∂(volume.restrict (Ioc a b)), y ∈ U \ E := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hnotE] with y hyE hy using ⟨hsub (Ioc_subset_Icc_self hy), hyE⟩
    have hprodae : ∀ᵐ q ∂((volume.restrict (Ioc a b)).prod volume), q.1 ∈ U \ E :=
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioc a b))
        (ν := (volume : Measure ℝ))).ae (p := fun y => y ∈ U \ E) hA'
    have hgprod : Integrable (fun q : ℝ × ℝ => g q.1 q.2)
        ((volume.restrict (Ioc a b)).prod volume) := by
      rw [integrable_prod_iff hgm.aestronglyMeasurable]
      refine ⟨Eventually.of_forall fun y => hg_int y, ?_⟩
      have : (fun y => ∫ z, ‖g y z‖) = fun _ => A * (2 / (2 - α) + 2 / (α - 1)) +
          cst * (2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1)) := by
        funext y
        simp_rw [Real.norm_of_nonneg (hg_nn y _)]
        exact hg_val y
      simp only [this]
      exact integrable_const _
    have hprod : Integrable (Function.uncurry psi) ((volume.restrict (Ioc a b)).prod volume) :=
      Integrable.mono' hgprod hψm.aestronglyMeasurable (by
        filter_upwards [hprodae] with q hq
        rw [Real.norm_eq_abs]; exact hpsi_bd q.1 hq q.2)
    exact (integral_integral_swap hprod).symm
  obtain ⟨hLL, hDer⟩ := c10_aux_primitive hU hGm hGb hinc
  refine ⟨hφint, ?_, hLL, hDer, ?_, fun a b hab hsub => hinc a b hab.le hsub⟩
  · filter_upwards [hnotE] with y hyE hyU
    refine ⟨Integrable.mono' ((io1.comp_sub_left y).const_mul A)
      ((hθc.comp (by fun_prop : Continuous fun z : ℝ => (y - z) / η)).measurable.mul
        (hJy y)).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (BJ y ⟨hyU, hyE⟩ z).1), ?_⟩
    exact Integrable.mono' ((iind y).const_mul cst)
      ((measurable_const.mul (hθ'c.comp (by fun_prop : Continuous fun z : ℝ => (y - z) / η)).measurable).mul
        (hHy y)).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact Bcut y hyU z)
  · filter_upwards [hGb] with y hy hyU
    rw [← hKeq]; exact hy hyU

/-- Blueprint: lem:c10_cutoff_errors.  Under the hypotheses of lem:c10_cutoff_weak_derivative,
with `F(y) = ∫ H(y,z) dz` (absolutely convergent on `U`) and `G(y) = ∫ J(y,z) dz` (absolutely
convergent a.e. on `U`): `sup_U |F_η - F| ≤ 2^{4-α} A η^{3-α}/(3-α)` and
`‖G_η - G‖_{L^∞(U)} ≤ A (2^{3-α}/(2-α) + 2^{4-α} M_ϑ/(3-α)) η^{2-α}`. -/
theorem c10_cutoff_errors (α : ℝ) (hα : 1 < α) (hα2 : α < 2) (U : Set ℝ)
    (hU : IsOpen U) (hUc : U.OrdConnected) (hUne : U.Nonempty) (A : ℝ) (hA : 0 ≤ A)
    (H J : ℝ → ℝ → ℝ) (hHJ : c10_local_kernel_pair α U A H J)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ01 : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hθ0 : ∀ x ∈ Icc (-1 : ℝ) 1, θ x = 0) (hθ1 : ∀ x, x ∉ Ioo (-2 : ℝ) 2 → θ x = 1)
    (Mθ : ℝ) (hMθ : ∀ x, |deriv θ x| ≤ Mθ) (η : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2) :
    (∀ y ∈ U, Integrable (H y)) ∧ (∀ᵐ y, y ∈ U → Integrable (J y)) ∧
    (∀ y ∈ U, |(∫ z, θ ((y - z) / η) * H y z) - ∫ z, H y z| ≤
      2 ^ (4 - α) / (3 - α) * A * η ^ (3 - α)) ∧
    (∀ᵐ y, y ∈ U →
      |(∫ z, (θ ((y - z) / η) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z)) - ∫ z, J y z| ≤
        A * (2 ^ (3 - α) / (2 - α) + 2 ^ (4 - α) * Mθ / (3 - α)) * η ^ (2 - α)) := by
  obtain ⟨Bcut, Bval, Bder, Bθ, BH, BJ, hE0⟩ :=
    c10_aux_cutoff_setup α hα hα2 U A hA H J hHJ θ hθ hθ01 hθ0 hθ1 Mθ hMθ η hη
  have hHm := hHJ.1
  have hJm := hHJ.2.1
  set E := Classical.choose hHJ.2.2.2.2.2
  obtain ⟨o0, o1, mo0, mo1, io0, io1, -⟩ := c10_kernel_envelopes α hα hα2
  obtain ⟨hθd, hθc, hθ'c, hM0, -⟩ := c10_aux_theta hθ hθ0 hθ1 hMθ
  have hHy : ∀ y, Measurable (H y) := fun y => hHm.comp measurable_prodMk_left
  have hJy : ∀ y, Measurable (J y) := fun y => hJm.comp measurable_prodMk_left
  have hnotE : ∀ᵐ y, y ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
  have I2 := fun y => c10_aux_ind_int (2 * η) (2 - α) y (by linarith) (by linarith)
  have I1 := fun y => c10_aux_ind_int (2 * η) (1 - α) y (by linarith) (by linarith)
  have hcl : ∀ y, Continuous (fun z : ℝ => (y - z) / η) := fun y => by fun_prop
  have hHint : ∀ y ∈ U, Integrable (H y) := fun y hy =>
    Integrable.mono' ((io0.comp_sub_left y).const_mul A) (hHy y).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact BH y hy z)
  have hJint : ∀ y ∈ U \ E, Integrable (J y) := fun y hy =>
    Integrable.mono' ((io1.comp_sub_left y).const_mul A) (hJy y).aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (BJ y hy z).2)
  obtain ⟨c1, c2, c3⟩ := c10_aux_cut_consts α η hη
  refine ⟨hHint, ?_, fun y hy => ?_, ?_⟩
  · filter_upwards [hnotE] with y hyE hyU using hJint y ⟨hyU, hyE⟩
  · have hφi : Integrable (fun z => θ ((y - z) / η) * H y z) :=
      Integrable.mono' ((io0.comp_sub_left y).const_mul A)
        (((hθc.comp (hcl y)).measurable).mul (hHy y)).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact Bθ y hy z)
    rw [← integral_sub hφi (hHint y hy), ← Real.norm_eq_abs]
    calc ‖∫ z, (θ ((y - z) / η) * H y z - H y z)‖
        ≤ ∫ z, A * (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ (2 - α)) (y - z) :=
          norm_integral_le_of_norm_le ((I2 y).1.const_mul A) (Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs, show θ ((y - z) / η) * H y z - H y z =
              (θ ((y - z) / η) - 1) * H y z by ring]
            exact Bval y hy z)
      _ = _ := by rw [integral_const_mul, (I2 y).2, c1]; ring
  · filter_upwards [hnotE] with y hyE hyU
    have hy : y ∈ U \ E := ⟨hyU, hyE⟩
    have hθJ : Integrable (fun z => θ ((y - z) / η) * J y z) :=
      Integrable.mono' ((io1.comp_sub_left y).const_mul A)
        (((hθc.comp (hcl y)).measurable).mul (hJy y)).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (BJ y hy z).1)
    have hcut : Integrable (fun z => η⁻¹ * deriv θ ((y - z) / η) * H y z) :=
      Integrable.mono' ((I2 y).1.const_mul (η⁻¹ * Mθ * A))
        ((measurable_const.mul (hθ'c.comp (hcl y)).measurable).mul (hHy y)).aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact Bcut y hyU z)
    have hsum : Integrable (fun z => θ ((y - z) / η) * J y z +
        η⁻¹ * deriv θ ((y - z) / η) * H y z) := hθJ.add hcut
    rw [← integral_sub hsum (hJint y hy), ← Real.norm_eq_abs]
    calc ‖∫ z, (θ ((y - z) / η) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z - J y z)‖
        ≤ ∫ z, (A * (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ (1 - α)) (y - z) +
            η⁻¹ * Mθ * A *
              (Icc (-(2 * η)) (2 * η)).indicator (fun s : ℝ => |s| ^ (2 - α)) (y - z)) :=
          norm_integral_le_of_norm_le (((I1 y).1.const_mul A).add ((I2 y).1.const_mul _))
            (Eventually.of_forall fun z => by
              rw [Real.norm_eq_abs, show θ ((y - z) / η) * J y z +
                η⁻¹ * deriv θ ((y - z) / η) * H y z - J y z =
                (θ ((y - z) / η) - 1) * J y z + η⁻¹ * deriv θ ((y - z) / η) * H y z by ring]
              exact (abs_add_le _ _).trans (add_le_add (Bder y hy z) (Bcut y hyU z)))
      _ = A * (2 * (2 * η) ^ (1 - α + 1) / (1 - α + 1)) +
            Mθ * A * (η⁻¹ * (2 * (2 * η) ^ (2 - α + 1) / (2 - α + 1))) := by
          rw [integral_add ((I1 y).1.const_mul A) ((I2 y).1.const_mul _), integral_const_mul,
            integral_const_mul, (I1 y).2, (I2 y).2]; ring
      _ = _ := by rw [c3, c2]; ring

theorem c10_aux_abs_mul2_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem c10_aux_abs_mul3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C :=
  c10_aux_abs_mul2_le (c10_aux_abs_mul2_le ha hb) hc

set_option maxHeartbeats 800000 in
/-- Helper (pure algebra): pointwise bounds for the linearized kernel `K = d₁h' + d₂S_h` and its
`y`-derivative `DK`, near (`|w| ≤ 1`) and far from the diagonal, `w = y - z`. -/
theorem c10_aux_var_alg {X L B H0 d1 d2 d11 d12 d22 u v h1 S f2 h2 w : ℝ}
    (hX : 0 ≤ X) (hL : 1 ≤ L) (hB : 1 ≤ B) (hH : 0 ≤ H0) (hw : w ≠ 0)
    (b1 : |d1| ≤ X) (b2 : |d2| ≤ X) (b12 : |d12| ≤ X) (b22 : |d22| ≤ X)
    (b2v : |d2| ≤ X * |u - v|) (bs : |d1 + d2| ≤ X * (u - v) ^ 2)
    (bs1 : |d11 + d12| ≤ X * |u - v|) (bs2 : |d12 + d22| ≤ X * |u - v|)
    (hu : |u| ≤ B) (hv : |v| ≤ B) (hh1 : |h1| ≤ H0) (hS : |S| ≤ H0) (hh2 : |h2| ≤ H0)
    (hf2 : |f2| ≤ L) (b11 : |d11| ≤ X)
    (hnear : |w| ≤ 1 → |u - v| ≤ |w| * L ∧ |h1 - S| ≤ |w| * H0) :
    |d1 * h1 + d2 * S| ≤ X * (8 * L ^ 2 + 8 * L + 8 * B + 16) * H0 * min (|w| ^ 2) 1 ∧
    |(d11 * f2 + d12 * ((u - v) / w)) * h1 + d1 * h2 +
        (d12 * f2 + d22 * ((u - v) / w)) * S + d2 * ((h1 - S) / w)| +
      2 * |d1 * h1 + d2 * S| / |w| ≤
      X * (8 * L ^ 2 + 8 * L + 8 * B + 16) * H0 * min |w| 1 := by
  set r := |w| with hr
  have hr0 : 0 < r := abs_pos.2 hw
  have hL0 : 0 ≤ L := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hC : 0 ≤ X * H0 := mul_nonneg hX hH
  rcases le_or_gt r 1 with hr1 | hr1
  · obtain ⟨huv, hhs⟩ := hnear hr1
    have hr2' : r ^ 2 ≤ 1 := by rw [sq]; nlinarith [abs_nonneg w]
    rw [min_eq_left hr2', min_eq_left hr1]
    have hsf : |(u - v) / w| ≤ L := by
      rw [abs_div, div_le_iff₀ hr0]; linarith
    have hsh : |(h1 - S) / w| ≤ H0 := by
      rw [abs_div, div_le_iff₀ hr0]; linarith
    have huv2 : |u - v| ≤ r * L := huv
    have e1 : (u - v) ^ 2 ≤ (r * L) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) huv2 2
    -- value
    have hK : |d1 * h1 + d2 * S| ≤ X * H0 * r ^ 2 * (L ^ 2 + L) := by
      have eK : d1 * h1 + d2 * S = (d1 + d2) * h1 + d2 * (S - h1) := by ring
      have t1 : |(d1 + d2) * h1| ≤ (X * (r * L) ^ 2) * H0 :=
        c10_aux_abs_mul2_le (bs.trans (mul_le_mul_of_nonneg_left e1 hX)) hh1
      have t2 : |d2 * (S - h1)| ≤ (X * (r * L)) * (r * H0) :=
        c10_aux_abs_mul2_le (b2v.trans (mul_le_mul_of_nonneg_left huv2 hX))
          (by rw [abs_sub_comm]; linarith)
      rw [eK]
      calc _ ≤ |(d1 + d2) * h1| + |d2 * (S - h1)| := abs_add_le _ _
        _ ≤ (X * (r * L) ^ 2) * H0 + (X * (r * L)) * (r * H0) := add_le_add t1 t2
        _ = X * H0 * r ^ 2 * (L ^ 2 + L) := by ring
    -- derivative
    have eD : (d11 * f2 + d12 * ((u - v) / w)) * h1 + d1 * h2 +
        (d12 * f2 + d22 * ((u - v) / w)) * S + d2 * ((h1 - S) / w) =
        (d11 + d12) * f2 * h1 + (d12 + d22) * ((u - v) / w) * h1 + (d1 + d2) * h2 +
          d12 * f2 * (S - h1) + d22 * ((u - v) / w) * (S - h1) +
          d2 * ((h1 - S) / w - h2) := by ring
    have bX : |d11 + d12| ≤ X * (r * L) := bs1.trans (mul_le_mul_of_nonneg_left huv2 hX)
    have bY : |d12 + d22| ≤ X * (r * L) := bs2.trans (mul_le_mul_of_nonneg_left huv2 hX)
    have bZ : |d2| ≤ X * (r * L) := b2v.trans (mul_le_mul_of_nonneg_left huv2 hX)
    have hSh : |S - h1| ≤ r * H0 := by rw [abs_sub_comm]; exact hhs
    have hshh : |(h1 - S) / w - h2| ≤ 2 * H0 := by
      calc _ ≤ |(h1 - S) / w| + |h2| := abs_sub _ _
        _ ≤ 2 * H0 := by linarith
    have T1 := c10_aux_abs_mul3_le bX hf2 hh1
    have T2 := c10_aux_abs_mul3_le bY hsf hh1
    have T3 := c10_aux_abs_mul2_le (bs.trans (mul_le_mul_of_nonneg_left e1 hX)) hh2
    have T4 := c10_aux_abs_mul3_le b12 hf2 hSh
    have T5 := c10_aux_abs_mul3_le b22 hsf hSh
    have T6 := c10_aux_abs_mul2_le bZ hshh
    have hD : |(d11 + d12) * f2 * h1 + (d12 + d22) * ((u - v) / w) * h1 + (d1 + d2) * h2 +
          d12 * f2 * (S - h1) + d22 * ((u - v) / w) * (S - h1) +
          d2 * ((h1 - S) / w - h2)| ≤ X * H0 * r * (5 * L ^ 2 + 4 * L) := by
      have hr2 : r ^ 2 ≤ r := by rw [sq]; exact mul_le_of_le_one_left hr0.le hr1
      have hq : X * (r * L) ^ 2 * H0 ≤ X * H0 * r * L ^ 2 := by
        calc X * (r * L) ^ 2 * H0 = (X * H0 * L ^ 2) * r ^ 2 := by ring
          _ ≤ (X * H0 * L ^ 2) * r := mul_le_mul_of_nonneg_left hr2 (mul_nonneg hC (sq_nonneg L))
          _ = X * H0 * r * L ^ 2 := by ring
      have hq2 : 0 ≤ X * H0 * r * L ^ 2 := mul_nonneg (mul_nonneg hC hr0.le) (sq_nonneg L)
      calc _ ≤ |(d11 + d12) * f2 * h1| + |(d12 + d22) * ((u - v) / w) * h1| + |(d1 + d2) * h2| +
            |d12 * f2 * (S - h1)| + |d22 * ((u - v) / w) * (S - h1)| +
            |d2 * ((h1 - S) / w - h2)| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            exact abs_add_le _ _
        _ ≤ X * (r * L) * L * H0 + X * (r * L) * L * H0 + X * (r * L) ^ 2 * H0 +
            X * L * (r * H0) + X * L * (r * H0) + X * (r * L) * (2 * H0) := by
            linarith [T1, T2, T3, T4, T5, T6]
        _ = X * H0 * r * (2 * L ^ 2 + 4 * L) + X * (r * L) ^ 2 * H0 := by ring
        _ ≤ X * H0 * r * (5 * L ^ 2 + 4 * L) := by linarith
    have hK2 : 2 * |d1 * h1 + d2 * S| / r ≤ 2 * (X * H0 * r * (L ^ 2 + L)) := by
      rw [div_le_iff₀ hr0]
      calc 2 * |d1 * h1 + d2 * S| ≤ 2 * (X * H0 * r ^ 2 * (L ^ 2 + L)) := by linarith
        _ = 2 * (X * H0 * r * (L ^ 2 + L)) * r := by ring
    rw [eD]
    constructor
    · calc _ ≤ X * H0 * r ^ 2 * (L ^ 2 + L) := hK
        _ ≤ _ := by
          have h8 : L ^ 2 + L ≤ 8 * L ^ 2 + 8 * L + 8 * B + 16 := by
            have := sq_nonneg L; linarith
          calc X * H0 * r ^ 2 * (L ^ 2 + L) = (X * H0 * r ^ 2) * (L ^ 2 + L) := by ring
            _ ≤ (X * H0 * r ^ 2) * (8 * L ^ 2 + 8 * L + 8 * B + 16) :=
              mul_le_mul_of_nonneg_left h8 (mul_nonneg hC (sq_nonneg r))
            _ = _ := by ring
    · have h8 : 5 * L ^ 2 + 4 * L + 2 * (L ^ 2 + L) ≤ 8 * L ^ 2 + 8 * L + 8 * B + 16 := by
        have := sq_nonneg L; linarith
      calc _ ≤ X * H0 * r * (5 * L ^ 2 + 4 * L) + 2 * (X * H0 * r * (L ^ 2 + L)) :=
            add_le_add hD hK2
        _ = (X * H0 * r) * (5 * L ^ 2 + 4 * L + 2 * (L ^ 2 + L)) := by ring
        _ ≤ (X * H0 * r) * (8 * L ^ 2 + 8 * L + 8 * B + 16) :=
            mul_le_mul_of_nonneg_left h8 (mul_nonneg hC hr0.le)
        _ = _ := by ring
  · have hr2' : 1 ≤ r ^ 2 := by rw [sq]; nlinarith
    rw [min_eq_right hr2', min_eq_right hr1.le, mul_one]
    have hK : |d1 * h1 + d2 * S| ≤ 2 * (X * H0) := by
      calc _ ≤ |d1 * h1| + |d2 * S| := abs_add_le _ _
        _ ≤ X * H0 + X * H0 := add_le_add (c10_aux_abs_mul2_le b1 hh1) (c10_aux_abs_mul2_le b2 hS)
        _ = _ := by ring
    have hsf : |(u - v) / w| ≤ 2 * B := by
      rw [abs_div, div_le_iff₀ hr0]
      calc |u - v| ≤ |u| + |v| := abs_sub _ _
        _ ≤ 2 * B := by linarith
        _ ≤ 2 * B * r := le_mul_of_one_le_right (by linarith) hr1.le
    have hsh : |(h1 - S) / w| ≤ 2 * H0 := by
      rw [abs_div, div_le_iff₀ hr0]
      calc |h1 - S| ≤ |h1| + |S| := abs_sub _ _
        _ ≤ 2 * H0 := by linarith
        _ ≤ 2 * H0 * r := le_mul_of_one_le_right (by linarith) hr1.le
    have T1 := c10_aux_abs_mul3_le b11 hf2 hh1
    have T2 := c10_aux_abs_mul3_le b12 hsf hh1
    have T3 := c10_aux_abs_mul2_le b1 hh2
    have T4 := c10_aux_abs_mul3_le b12 hf2 hS
    have T5 := c10_aux_abs_mul3_le b22 hsf hS
    have T6 := c10_aux_abs_mul2_le b2 hsh
    have hD : |(d11 * f2 + d12 * ((u - v) / w)) * h1 + d1 * h2 +
        (d12 * f2 + d22 * ((u - v) / w)) * S + d2 * ((h1 - S) / w)| ≤
        X * H0 * (2 * L + 4 * B + 3) := by
      have e : (d11 * f2 + d12 * ((u - v) / w)) * h1 + d1 * h2 +
          (d12 * f2 + d22 * ((u - v) / w)) * S + d2 * ((h1 - S) / w) =
          d11 * f2 * h1 + d12 * ((u - v) / w) * h1 + d1 * h2 + d12 * f2 * S +
            d22 * ((u - v) / w) * S + d2 * ((h1 - S) / w) := by ring
      rw [e]
      calc _ ≤ |d11 * f2 * h1| + |d12 * ((u - v) / w) * h1| + |d1 * h2| + |d12 * f2 * S| +
            |d22 * ((u - v) / w) * S| + |d2 * ((h1 - S) / w)| := by
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
            exact abs_add_le _ _
        _ ≤ X * L * H0 + X * (2 * B) * H0 + X * H0 + X * L * H0 + X * (2 * B) * H0 +
            X * (2 * H0) := by linarith [T1, T2, T3, T4, T5, T6]
        _ = _ := by ring
    have hK2 : 2 * |d1 * h1 + d2 * S| / r ≤ 4 * (X * H0) := by
      rw [div_le_iff₀ hr0]
      have : 4 * (X * H0) ≤ 4 * (X * H0) * r := le_mul_of_one_le_right (by linarith) hr1.le
      linarith
    constructor
    · have h8 : (2 : ℝ) ≤ 8 * L ^ 2 + 8 * L + 8 * B + 16 := by
        have := sq_nonneg L; linarith
      calc _ ≤ 2 * (X * H0) := hK
        _ = (X * H0) * 2 := by ring
        _ ≤ (X * H0) * (8 * L ^ 2 + 8 * L + 8 * B + 16) := mul_le_mul_of_nonneg_left h8 hC
        _ = _ := by ring
    · have h8 : 2 * L + 4 * B + 3 + 4 ≤ 8 * L ^ 2 + 8 * L + 8 * B + 16 := by
        have := sq_nonneg L; linarith
      calc _ ≤ X * H0 * (2 * L + 4 * B + 3) + 4 * (X * H0) := add_le_add hD hK2
        _ = (X * H0) * (2 * L + 4 * B + 3 + 4) := by ring
        _ ≤ (X * H0) * (8 * L ^ 2 + 8 * L + 8 * B + 16) := mul_le_mul_of_nonneg_left h8 hC
        _ = _ := by ring


/-- Helper: a function that is `C¹` at every point of `V` is locally Lipschitz on `V`. -/
theorem c10_aux_llo_of_contDiffAt {V : Set ℝ} {f : ℝ → ℝ} (h : ∀ x ∈ V, ContDiffAt ℝ 1 f x) :
    LocallyLipschitzOn V f := by
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := ((h x hx).contDiffWithinAt (s := univ)).exists_lipschitzOnWith
    convex_univ
  rw [nhdsWithin_univ] at ht
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- Helper: products of locally Lipschitz functions on a set. -/
theorem c10_aux_llo_mul {V : Set ℝ} {f g : ℝ → ℝ} (hf : LocallyLipschitzOn V f)
    (hg : LocallyLipschitzOn V g) : LocallyLipschitzOn V (fun x => f x * g x) := by
  intro x hx
  obtain ⟨Kf, t1, ht1, h1⟩ := hf hx
  obtain ⟨Kg, t2, ht2, h2⟩ := hg hx
  have hx1 : x ∈ t1 := mem_of_mem_nhdsWithin hx ht1
  have hx2 : x ∈ t2 := mem_of_mem_nhdsWithin hx ht2
  set s := t1 ∩ t2 ∩ Metric.ball x 1
  have hs : s ∈ nhdsWithin x V :=
    inter_mem (inter_mem ht1 ht2) (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos))
  have b1 : ∀ y ∈ s, |f y| ≤ |f x| + Kf := fun y hy => by
    have := h1.dist_le_mul y hy.1.1 x hx1
    rw [Real.dist_eq, Real.dist_eq] at this
    have hd : |y - x| < 1 := by have := hy.2; rwa [Metric.mem_ball, Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (f y) (f x)
    nlinarith [Kf.2]
  have b2 : ∀ y ∈ s, |g y| ≤ |g x| + Kg := fun y hy => by
    have := h2.dist_le_mul y hy.1.2 x hx2
    rw [Real.dist_eq, Real.dist_eq] at this
    have hd : |y - x| < 1 := by have := hy.2; rwa [Metric.mem_ball, Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (g y) (g x)
    nlinarith [Kg.2]
  exact ⟨_, s, hs, c10_aux_lipOn_mul (h1.mono fun y hy => hy.1.1) (h2.mono fun y hy => hy.1.2)
    b1 b2⟩

/-- Helper: composition of a locally Lipschitz function of two variables with two locally
Lipschitz functions on a set. -/
theorem c10_aux_llo_comp2 {V : Set ℝ} {φ : ℝ × ℝ → ℝ} (hφ : LocallyLipschitz φ) {a b : ℝ → ℝ}
    (ha : LocallyLipschitzOn V a) (hb : LocallyLipschitzOn V b) :
    LocallyLipschitzOn V (fun x => φ (a x, b x)) := by
  intro x hx
  obtain ⟨K, W, hW, hφW⟩ := hφ (a x, b x)
  obtain ⟨Ka, t1, ht1, h1⟩ := ha hx
  obtain ⟨Kb, t2, ht2, h2⟩ := hb hx
  have hx12 : x ∈ t1 ∩ t2 := ⟨mem_of_mem_nhdsWithin hx ht1, mem_of_mem_nhdsWithin hx ht2⟩
  have hpair : LipschitzOnWith (max Ka Kb) (fun y => (a y, b y)) (t1 ∩ t2) :=
    (h1.mono inter_subset_left).prodMk (h2.mono inter_subset_right)
  have hcont : ContinuousWithinAt (fun y => (a y, b y)) (t1 ∩ t2) x :=
    hpair.continuousOn x hx12
  have hpre : {y | (a y, b y) ∈ W} ∈ nhdsWithin x (t1 ∩ t2) := hcont hW
  have h12 : t1 ∩ t2 ∈ nhdsWithin x V := inter_mem ht1 ht2
  refine ⟨K * max Ka Kb, t1 ∩ t2 ∩ {y | (a y, b y) ∈ W},
    inter_mem h12 (nhdsWithin_le_of_mem h12 hpre), ?_⟩
  exact hφW.comp (hpair.mono inter_subset_left) fun y hy => hy.2


/-- Helper: derivative of `y ↦ |y - z|^α` off the diagonal. -/
theorem c10_aux_pow_hasDeriv (α y z : ℝ) (hyz : y ≠ z) :
    HasDerivAt (fun y' => |y' - z| ^ α) (α * |y - z| ^ α / (y - z)) y := by
  have hw : y - z ≠ 0 := sub_ne_zero.2 hyz
  have ha := hasDerivAt_abs hw
  have h1 : HasDerivAt ((fun x : ℝ => |x|) ∘ fun y' => y' - z) ((SignType.sign (y - z) : ℝ) * 1) y :=
    ha.comp y ((hasDerivAt_id' y).sub_const z)
  have h2 := h1.rpow_const (p := α) (Or.inl (abs_ne_zero.2 hw))
  refine h2.congr_deriv ?_
  have hp : 0 < |y - z| := abs_pos.2 hw
  show (SignType.sign (y - z) : ℝ) * 1 * α * |y - z| ^ (α - 1) = α * |y - z| ^ α / (y - z)
  rw [Real.rpow_sub_one hp.ne']
  rcases lt_or_gt_of_ne hw with h | h
  · rw [sign_neg h, abs_of_neg h]
    simp only [SignType.coe_neg, SignType.coe_one]
    have : -(y - z) ≠ 0 := by linarith
    field_simp
  · rw [sign_pos h, abs_of_pos h]
    simp only [SignType.coe_one]
    field_simp

/-- Helper: quotient rule against `|y - z|^α`. -/
theorem c10_aux_div_pow_hasDeriv {F : ℝ → ℝ} {F' α y z : ℝ} (hF : HasDerivAt F F' y)
    (hyz : y ≠ z) :
    HasDerivAt (fun y' => F y' / |y' - z| ^ α) ((F' - α * F y / (y - z)) / |y - z| ^ α) y := by
  have hw : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hp : 0 < |y - z| ^ α := Real.rpow_pos_of_pos (abs_pos.2 hw) α
  refine (hF.div (c10_aux_pow_hasDeriv α y z hyz) hp.ne').congr_deriv ?_
  field_simp

/-- Helper: `y ↦ (|y - z|^α)⁻¹` is `C¹` off the diagonal. -/
theorem c10_aux_invpow_contDiffAt (α y z : ℝ) (hyz : y ≠ z) :
    ContDiffAt ℝ 1 (fun y' => (|y' - z| ^ α)⁻¹) y := by
  have hw : y - z ≠ 0 := sub_ne_zero.2 hyz
  have h0 : ContDiffAt ℝ 1 (fun y' : ℝ => y' - z) y := contDiffAt_id.sub contDiffAt_const
  have hab : ContDiffAt ℝ 1 (fun x : ℝ => |x|) (y - z) := contDiffAt_abs hw
  have ha : ContDiffAt ℝ 1 ((fun x : ℝ => |x|) ∘ fun y' => y' - z) y := hab.comp y h0
  have hr : ContDiffAt ℝ 1 ((fun x : ℝ => x ^ α) ∘ ((fun x : ℝ => |x|) ∘ fun y' => y' - z)) y :=
    (Real.contDiffAt_rpow_const_of_ne (p := α) (abs_ne_zero.2 hw)).comp y ha
  exact hr.inv (Real.rpow_pos_of_pos (abs_pos.2 hw) α).ne'

/-- Helper: the `Γ_ε`-derivatives as `C¹` functions of both variables. -/
theorem c10_aux_d_contDiff (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) :
    ContDiff ℝ 1 (fun q : ℝ × ℝ => c10_N_pieces_Gamma_d1 p ε q.1 q.2) ∧
    ContDiff ℝ 1 (fun q : ℝ × ℝ => c10_N_pieces_Gamma_d2 p ε q.1 q.2) ∧
    ContDiff ℝ 1 (fun q : ℝ × ℝ => c10_N_pieces_Gamma p ε q.1 q.2) := by
  have hF := c10_aux_G_fderiv_smooth p ε hp hp1 hε
  have e1 : (fun q : ℝ × ℝ => c10_N_pieces_Gamma_d1 p ε q.1 q.2) =
      fun q => fderiv ℝ (c10_aux_G p ε) q (1, 0) :=
    funext fun q => (c10_aux_d_eq p ε hp hp1 hε q.1 q.2).1
  have e2 : (fun q : ℝ × ℝ => c10_N_pieces_Gamma_d2 p ε q.1 q.2) =
      fun q => fderiv ℝ (c10_aux_G p ε) q (0, 1) :=
    funext fun q => (c10_aux_d_eq p ε hp hp1 hε q.1 q.2).2
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact (hF.clm_apply contDiff_const).of_le (by norm_num)
  · rw [e2]; exact (hF.clm_apply contDiff_const).of_le (by norm_num)
  · exact (c10_aux_G_smooth p ε hp hp1 hε).of_le (by simp)

/-- Helper: joint continuity of the linearized kernel. -/
theorem c10_aux_K_cont (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) {f h : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h) :
    Continuous (fun q : ℝ × ℝ => c10_N3_linearization_K p ε f h q.1 q.2) := by
  obtain ⟨c1, c2, -⟩ := c10_aux_d_contDiff p ε hp hp1 hε
  have sf : Continuous (fun q : ℝ × ℝ => c01_secant f q.1 q.2) := (c03_secant_continuous_bound f hf).1
  have sh : Continuous (fun q : ℝ × ℝ => c01_secant h q.1 q.2) := (c03_secant_continuous_bound h hh).1
  have df : Continuous (fun q : ℝ × ℝ => deriv f q.1) := (hf.continuous_deriv le_rfl).comp continuous_fst
  have dh : Continuous (fun q : ℝ × ℝ => deriv h q.1) := (hh.continuous_deriv le_rfl).comp continuous_fst
  unfold c10_N3_linearization_K
  exact ((c1.continuous.comp (df.prodMk sf)).mul dh).add ((c2.continuous.comp (df.prodMk sf)).mul sh)

/-- Helper: `K_{f,h}(·,z)` is locally Lipschitz off `z`. -/
theorem c10_aux_K_locLip (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) {f h : ℝ → ℝ}
    (hf : W2inftyLoc f) (hh : W2inftyLoc h) (z : ℝ) :
    LocallyLipschitzOn {z}ᶜ (fun y => c10_N3_linearization_K p ε f h y z) := by
  obtain ⟨c1, c2, -⟩ := c10_aux_d_contDiff p ε hp hp1 hε
  have sec : ∀ g : ℝ → ℝ, W2inftyLoc g → LocallyLipschitzOn {z}ᶜ (fun y => c01_secant g y z) :=
    fun g hg => c10_aux_llo_of_contDiffAt fun y hy =>
      (c10_secant_identities g hg y z hy).2.1.contDiffAt (isOpen_compl_singleton.mem_nhds hy)
  have df := hf.2.locallyLipschitzOn (s := {z}ᶜ)
  have dh := hh.2.locallyLipschitzOn (s := {z}ᶜ)
  unfold c10_N3_linearization_K
  exact (c10_aux_llo_mul (c10_aux_llo_comp2 c1.locallyLipschitz df (sec f hf)) dh).add
    (c10_aux_llo_mul (c10_aux_llo_comp2 c2.locallyLipschitz df (sec f hf)) (sec h hh))

/-- Helper: dividing a function locally Lipschitz off `z` by `|y - z|^α`. -/
theorem c10_aux_llo_div_pow {F : ℝ → ℝ} {z : ℝ} (α : ℝ) (hF : LocallyLipschitzOn {z}ᶜ F) :
    LocallyLipschitzOn {z}ᶜ (fun y => F y / |y - z| ^ α) := by
  simp_rw [div_eq_mul_inv]
  exact c10_aux_llo_mul hF (c10_aux_llo_of_contDiffAt fun y hy => c10_aux_invpow_contDiffAt α y z hy)

/-- Helper: joint measurability of a partial derivative of a jointly continuous kernel. -/
theorem c10_aux_meas_deriv_param {K : ℝ → ℝ → ℝ} (hK : Continuous (fun q : ℝ × ℝ => K q.1 q.2)) :
    Measurable (fun q : ℝ × ℝ => deriv (fun y' => K y' q.2) q.1) := by
  have hc : Continuous (Function.uncurry fun (z y : ℝ) => K y z) := hK.comp continuous_swap
  have := measurable_deriv_with_param hc
  exact this.comp measurable_swap

/-- Helper: secant data near and far for `y` in `[-R,R]`. -/
theorem c10_aux_secant_local {g : ℝ → ℝ} (hg : W2inftyLoc g) {R L B : ℝ}
    (hgB : ∀ x, |deriv g x| ≤ B) (hg2 : ∀ᵐ x, x ∈ Icc (-R - 2) (R + 2) → |deriv (deriv g) x| ≤ L)
    {y z : ℝ} (hy : y ∈ Icc (-R) R) (hyz : y ≠ z) :
    |c01_secant g y z| ≤ B ∧
    (|y - z| ≤ 1 → |deriv g y - c01_secant g y z| ≤ |y - z| * L) := by
  obtain ⟨-, -, -, hnear, hfar⟩ := c10_secant_identities g hg y z hyz
  refine ⟨((hfar B hgB).2).trans (min_le_left _ _), fun h1 => (hnear L ?_).1⟩
  filter_upwards [hg2] with w hw hwI
  refine hw ⟨?_, ?_⟩
  · rcases le_total y z with h | h
    · rw [uIcc_of_le h] at hwI; linarith [hwI.1, hy.1]
    · rw [uIcc_of_ge h] at hwI
      have : y - z ≤ 1 := by rw [abs_of_nonneg (by linarith)] at h1; exact h1
      linarith [hwI.1, hy.1]
  · rcases le_total y z with h | h
    · rw [uIcc_of_le h] at hwI
      have : z - y ≤ 1 := by rw [abs_of_nonpos (by linarith)] at h1; linarith
      linarith [hwI.2, hy.2]
    · rw [uIcc_of_ge h] at hwI; linarith [hwI.2, hy.2]

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_variation_kernel_bounds.  For `0 < p < 1`, `α = 1+p`, `B, L ≥ 1` there is
`C = C(p,B,L)` such that for `R ≥ 1`, `0 ≤ ε ≤ 1`, `H₀ ≥ 0` and `f, h ∈ W^{2,∞}_loc` with
`‖f'‖_∞ ≤ B`, `‖h'‖_∞ ≤ H₀`, `‖f''‖_{L^∞[-R-2,R+2]} ≤ L`, `‖h''‖_{L^∞[-R-2,R+2]} ≤ H₀`, the kernels
`H = K_{f,h}/|y-z|^α` and `J = (∂_y K_{f,h} - α K_{f,h}/(y-z))/|y-z|^α` (both zero on the diagonal,
`∂_y` the classical derivative with `z` fixed) form a dominated kernel pair on `(-R,R)` with
constant `C ε H₀`; explicitly `|K| ≤ C ε H₀ min(|y-z|²,1)` on `(-R,R)` and, for a.e. `y ∈ (-R,R)`
and all `z ≠ y`, `|∂_y K| + α|K|/|y-z| ≤ C ε H₀ min(|y-z|,1)`.
(Lean: `J` uses `deriv` of `K(·,z)`, which is the chain-rule expression at every `y` where
`f''(y), h''(y)` exist, i.e. off one null set; the values on that null set are immaterial.) -/
theorem c10_variation_kernel_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (B L : ℝ) (hB : 1 ≤ B)
    (hL : 1 ≤ L) :
    ∃ C > 0, ∀ R : ℝ, 1 ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ H₀ : ℝ, 0 ≤ H₀ →
      ∀ f h : ℝ → ℝ, W2inftyLoc f → W2inftyLoc h →
      (∀ y, |deriv f y| ≤ B) → (∀ y, |deriv h y| ≤ H₀) →
      (∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv f) y| ≤ L) →
      (∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv h) y| ≤ H₀) →
      c10_local_kernel_pair (p + 1) (Ioo (-R) R) (C * ε * H₀)
        (fun y z => c10_N3_linearization_K p ε f h y z / |y - z| ^ (p + 1))
        (fun y z => c10_N3_linearization_dK p ε f h y z / |y - z| ^ (p + 1)) ∧
      (∀ y ∈ Ioo (-R) R, ∀ z : ℝ, z ≠ y →
        |c10_N3_linearization_K p ε f h y z| ≤ C * ε * H₀ * min (|y - z| ^ 2) 1) ∧
      (∀ᵐ y, y ∈ Ioo (-R) R → ∀ z : ℝ, z ≠ y →
        |deriv (fun y' => c10_N3_linearization_K p ε f h y' z) y| +
            (p + 1) * |c10_N3_linearization_K p ε f h y z| / |y - z| ≤
          C * ε * H₀ * min |y - z| 1) := by
  obtain ⟨Ck, hCk, hk⟩ := c10_aux_kernel_bounds p B hp hp1 hB
  refine ⟨Ck * (8 * L ^ 2 + 8 * L + 8 * B + 16), by positivity, ?_⟩
  intro R hR ε hε hε1 H₀ hH₀ f h hf hh hfB hhH hf2 hh2
  set C := Ck * (8 * L ^ 2 + 8 * L + 8 * B + 16) with hC
  have hα : (p + 1) ≠ 0 := by linarith
  have alg : ∀ y ∈ Icc (-R) R, ∀ z : ℝ, z ≠ y → ∀ f2 h2 : ℝ, |f2| ≤ L → |h2| ≤ H₀ →
      |c10_N3_linearization_K p ε f h y z| ≤ C * ε * H₀ * min (|y - z| ^ 2) 1 ∧
      |(c10_N_pieces_Gamma_d11 p ε (deriv f y) (c01_secant f y z) * f2 +
          c10_N_pieces_Gamma_d12 p ε (deriv f y) (c01_secant f y z) *
            ((deriv f y - c01_secant f y z) / (y - z))) * deriv h y +
        c10_N_pieces_Gamma_d1 p ε (deriv f y) (c01_secant f y z) * h2 +
        (c10_N_pieces_Gamma_d12 p ε (deriv f y) (c01_secant f y z) * f2 +
          c10_N_pieces_Gamma_d22 p ε (deriv f y) (c01_secant f y z) *
            ((deriv f y - c01_secant f y z) / (y - z))) * c01_secant h y z +
        c10_N_pieces_Gamma_d2 p ε (deriv f y) (c01_secant f y z) *
          ((deriv h y - c01_secant h y z) / (y - z))| + 2 * |c10_N3_linearization_K p ε f h y z| / |y - z| ≤
        C * ε * H₀ * min |y - z| 1 := by
    intro y hy z hzy f2 h2 hf2' hh2'
    have hyz : y ≠ z := Ne.symm hzy
    obtain ⟨sfB, sfN⟩ := c10_aux_secant_local hf hfB hf2 hy hyz
    obtain ⟨shB, shN⟩ := c10_aux_secant_local hh hhH hh2 hy hyz
    obtain ⟨b1, b2, b11, b12, b22, b2v, bs, bs1, bs2⟩ :=
      hk ε hε hε1 (deriv f y) (c01_secant f y z) (hfB y) sfB
    have := c10_aux_var_alg (X := Ck * ε) (L := L) (B := B) (H0 := H₀) (f2 := f2) (h2 := h2)
      (w := y - z) (mul_nonneg hCk.le hε) hL hB hH₀ (sub_ne_zero.2 hyz) b1 b2 b12 b22 b2v bs
      bs1 bs2 (hfB y) sfB (hhH y) shB hh2' hf2' b11 (fun h1 => ⟨sfN h1, shN h1⟩)
    simp only [c10_N3_linearization_K]
    rw [hC]
    constructor
    · refine this.1.trans (le_of_eq ?_); ring
    · refine this.2.trans (le_of_eq ?_); ring
  -- the good set
  set P : ℝ → Prop := fun y => DifferentiableAt ℝ (deriv f) y ∧ DifferentiableAt ℝ (deriv h) y ∧
    (y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv f) y| ≤ L) ∧
    (y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv h) y| ≤ H₀) with hP
  have hPae : ∀ᵐ y, P y := by
    filter_upwards [c10_aux_ae_differentiableAt hf.2, c10_aux_ae_differentiableAt hh.2, hf2, hh2]
      with y a b c d using ⟨a, b, c, d⟩
  have hIcc : ∀ y ∈ Ioo (-R) R, y ∈ Icc (-R - 2) (R + 2) := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hIcc' : ∀ y ∈ Ioo (-R) R, y ∈ Icc (-R) R := fun y hy => Ioo_subset_Icc_self hy
  -- derivative at good points
  have hder : ∀ y, P y → ∀ z, z ≠ y →
      HasDerivAt (fun y' => c10_N3_linearization_K p ε f h y' z) (c10_aux_DK p ε f h y z) y := fun y hPy z hzy =>
    c10_aux_K_hasDeriv p ε hp hp1 hε hf hh (Ne.symm hzy) hPy.1 hPy.2.1
  have hDbd : ∀ y ∈ Ioo (-R) R, P y → ∀ z, z ≠ y →
      |deriv (fun y' => c10_N3_linearization_K p ε f h y' z) y| + (p + 1) * |c10_N3_linearization_K p ε f h y z| / |y - z| ≤
        C * ε * H₀ * min |y - z| 1 := by
    intro y hy hPy z hzy
    rw [(hder y hPy z hzy).deriv]
    have h2 := (alg y (hIcc' y hy) z hzy _ _ (hPy.2.2.1 (hIcc y hy)) (hPy.2.2.2 (hIcc y hy))).2
    have hpos : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hzy))
    have : (p + 1) * |c10_N3_linearization_K p ε f h y z| / |y - z| ≤ 2 * |c10_N3_linearization_K p ε f h y z| / |y - z| :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
        hpos.le
    unfold c10_aux_DK; linarith
  have hKmeas : Measurable (fun q : ℝ × ℝ => c10_N3_linearization_K p ε f h q.1 q.2) :=
    (c10_aux_K_cont p ε hp hp1 hε hf.1 hh.1).measurable
  have hDmeas : Measurable (fun q : ℝ × ℝ =>
      deriv (fun y' => c10_N3_linearization_K p ε f h y' q.2) q.1) :=
    c10_aux_meas_deriv_param (K := fun y z => c10_N3_linearization_K p ε f h y z)
      (c10_aux_K_cont p ε hp hp1 hε hf.1 hh.1)
  have hpowm : Measurable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (p + 1)) := by fun_prop
  have hdiag0 : ∀ y : ℝ, |y - y| ^ (p + 1) = 0 := fun y => by
    rw [sub_self, abs_zero, Real.zero_rpow hα]
  have homega : ∀ y z : ℝ, z ≠ y → ∀ (A t : ℝ), |t| ≤ A * min (|y - z| ^ 2) 1 →
      |t / |y - z| ^ (p + 1)| ≤ A * c10_local_kernel_pair_omega0 (p + 1) (y - z) := by
    intro y z hzy A t ht
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hpos : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.2 hw) _
    rw [abs_div, abs_of_pos hpos, c10_local_kernel_pair_omega0, if_neg hw, mul_div_assoc']
    exact div_le_div_of_nonneg_right ht hpos.le
  have homega1 : ∀ y z : ℝ, z ≠ y → ∀ (A t : ℝ), |t| ≤ A * min |y - z| 1 →
      |t / |y - z| ^ (p + 1)| ≤ A * c10_local_kernel_pair_omega1 (p + 1) (y - z) := by
    intro y z hzy A t ht
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hpos : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.2 hw) _
    rw [abs_div, abs_of_pos hpos, c10_local_kernel_pair_omega1, if_neg hw, mul_div_assoc']
    exact div_le_div_of_nonneg_right ht hpos.le
  have hdK : ∀ y z, c10_N3_linearization_dK p ε f h y z =
      deriv (fun y' => c10_N3_linearization_K p ε f h y' z) y - (p + 1) * c10_N3_linearization_K p ε f h y z / (y - z) := fun _ _ => rfl
  refine ⟨⟨?_, ?_, fun y _ => ?_, fun z => ⟨?_, ?_⟩, fun y hy z hzy => ?_, ?_⟩,
    fun y hy z hzy => (alg y (hIcc' y hy) z hzy 0 0 (by simp; linarith) (by simp [hH₀])).1, ?_⟩
  · exact hKmeas.div hpowm
  · simp only [hdK]
    exact ((hDmeas.sub ((measurable_const.mul hKmeas).div (by fun_prop))).div hpowm)
  · have h0 : (0 : ℝ) ^ (p + 1) = 0 := Real.zero_rpow hα
    simp [h0]
  · exact (c10_aux_llo_div_pow (p + 1) (c10_aux_K_locLip p ε hp hp1 hε hf hh z)).mono
      (fun y hy => hy.2)
  · filter_upwards [hPae] with y hPy hy
    have hzy : y ≠ z := hy.2
    have hd := c10_aux_div_pow_hasDeriv (α := p + 1) (hder y hPy z (Ne.symm hzy)) hzy
    rw [← (hder y hPy z (Ne.symm hzy)).deriv] at hd
    exact hd
  · exact homega y z hzy _ _ (by
      have := (alg y (hIcc' y hy) z hzy 0 0 (by simp; linarith) (by simp [hH₀])).1
      exact this)
  · refine ⟨{y | ¬ P y}, ae_iff.1 hPae, fun y hy z hzy => ?_⟩
    have hPy : P y := not_not.1 hy.2
    refine homega1 y z hzy _ _ ?_
    rw [hdK]
    calc _ ≤ |deriv (fun y' => c10_N3_linearization_K p ε f h y' z) y| + |(p + 1) * c10_N3_linearization_K p ε f h y z / (y - z)| := abs_sub _ _
      _ = |deriv (fun y' => c10_N3_linearization_K p ε f h y' z) y| + (p + 1) * |c10_N3_linearization_K p ε f h y z| / |y - z| := by
          rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < p + 1)]
      _ ≤ _ := hDbd y hy.1 hPy z hzy
  · filter_upwards [hPae] with y hPy hy z hzy using hDbd y hy hPy z hzy

/-- Blueprint: lem:c10_Ieps_local (helper).  The derivative kernel
`K⁽¹⁾_g(y,z) = ∂₁Γ_ε g''(y) + ∂₂Γ_ε (g'(y) - S_g)/(y-z) - (1+p) Γ_ε/(y-z)`
(all at `(g'(y), S_g(y,z))`). -/
def c10_Ieps_local_K1 (p ε : ℝ) (g : ℝ → ℝ) (y z : ℝ) : ℝ :=
  c10_N_pieces_Gamma_d1 p ε (deriv g y) (c01_secant g y z) * deriv (deriv g) y +
    c10_N_pieces_Gamma_d2 p ε (deriv g y) (c01_secant g y z) *
      ((deriv g y - c01_secant g y z) / (y - z)) -
    (1 + p) * c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / (y - z)

set_option maxHeartbeats 800000 in
/-- Helper (pure algebra): pointwise bounds for the profile kernel numerators. -/
theorem c10_aux_prof_alg {X L B d1 d2 G u v g2 w p : ℝ} (hX : 0 ≤ X) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (hw : w ≠ 0) (hp0 : 0 < p) (hp1 : p < 1)
    (b1 : |d1| ≤ X) (b2v : |d2| ≤ X * |u - v|) (bs : |d1 + d2| ≤ X * (u - v) ^ 2)
    (bG : |G| ≤ X * (u - v) ^ 2) (hu : |u| ≤ B) (hv : |v| ≤ B) (hg2 : |g2| ≤ L)
    (hnear : |w| ≤ 1 → |u - v| ≤ |w| * L) :
    |G| ≤ X * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) * min (|w| ^ 2) 1 ∧
    |d1 * g2 + d2 * ((u - v) / w) - (1 + p) * G / w| ≤
      X * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) * min |w| 1 := by
  have hr0 : 0 < |w| := abs_pos.2 hw
  have hL0 : 0 ≤ L := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hp2 : |1 + p| ≤ 2 := by rw [abs_of_pos (by linarith)]; linarith
  have hT3 : ∀ M : ℝ, |G| ≤ M → |(1 + p) * G / w| ≤ 2 * M / |w| := fun M hM => by
    rw [abs_div, abs_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul hp2 hM (abs_nonneg _) (by norm_num)) hr0.le
  have hsplit : |d1 * g2 + d2 * ((u - v) / w) - (1 + p) * G / w| ≤
      |d1 * g2| + |d2 * ((u - v) / w)| + |(1 + p) * G / w| :=
    (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rcases le_or_gt |w| 1 with hr1 | hr1
  · have huv := hnear hr1
    have hr2 : |w| ^ 2 ≤ |w| := by rw [sq]; exact mul_le_of_le_one_left hr0.le hr1
    rw [min_eq_left (hr2.trans hr1), min_eq_left hr1]
    have e1 : (u - v) ^ 2 ≤ (|w| * L) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) huv 2
    have hGb : |G| ≤ X * L ^ 2 * |w| ^ 2 := by
      calc |G| ≤ X * (u - v) ^ 2 := bG
        _ ≤ X * (|w| * L) ^ 2 := mul_le_mul_of_nonneg_left e1 hX
        _ = X * L ^ 2 * |w| ^ 2 := by ring
    have hd1 : |d1| ≤ X * (L ^ 2 + L) * |w| := by
      have h1 : |d1| ≤ |d1 + d2| + |d2| := by
        have := abs_sub (d1 + d2) d2; simpa using this
      have h2 : |d1 + d2| ≤ X * L ^ 2 * |w| ^ 2 := by
        calc |d1 + d2| ≤ X * (u - v) ^ 2 := bs
          _ ≤ X * (|w| * L) ^ 2 := mul_le_mul_of_nonneg_left e1 hX
          _ = X * L ^ 2 * |w| ^ 2 := by ring
      have h3 : |d2| ≤ X * L * |w| := by
        calc |d2| ≤ X * |u - v| := b2v
          _ ≤ X * (|w| * L) := mul_le_mul_of_nonneg_left huv hX
          _ = X * L * |w| := by ring
      have h4 : X * L ^ 2 * |w| ^ 2 ≤ X * L ^ 2 * |w| :=
        mul_le_mul_of_nonneg_left hr2 (mul_nonneg hX (sq_nonneg L))
      calc |d1| ≤ X * L ^ 2 * |w| + X * L * |w| := by linarith
        _ = X * (L ^ 2 + L) * |w| := by ring
    have T1 : |d1 * g2| ≤ X * (L ^ 2 + L) * |w| * L := c10_aux_abs_mul2_le hd1 hg2
    have hsf : |(u - v) / w| ≤ L := by rw [abs_div, div_le_iff₀ hr0]; linarith
    have T2 : |d2 * ((u - v) / w)| ≤ X * (|w| * L) * L :=
      c10_aux_abs_mul2_le (b2v.trans (mul_le_mul_of_nonneg_left huv hX)) hsf
    have T3 := hT3 _ hGb
    have T3' : 2 * (X * L ^ 2 * |w| ^ 2) / |w| = 2 * X * L ^ 2 * |w| := by
      field_simp
    rw [T3'] at T3
    have hcp : L ^ 3 + 4 * L ^ 2 ≤ L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2 := by
      have := sq_nonneg B; linarith
    have hcp2 : L ^ 2 ≤ L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2 := by
      have := pow_nonneg hL0 3; have := sq_nonneg B; have := sq_nonneg L; linarith
    constructor
    · calc |G| ≤ X * L ^ 2 * |w| ^ 2 := hGb
        _ = (X * |w| ^ 2) * L ^ 2 := by ring
        _ ≤ (X * |w| ^ 2) * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hcp2 (mul_nonneg hX (sq_nonneg _))
        _ = _ := by ring
    · calc _ ≤ |d1 * g2| + |d2 * ((u - v) / w)| + |(1 + p) * G / w| := hsplit
        _ ≤ X * (L ^ 2 + L) * |w| * L + X * (|w| * L) * L + 2 * X * L ^ 2 * |w| := by linarith
        _ = (X * |w|) * (L ^ 3 + 4 * L ^ 2) := by ring
        _ ≤ (X * |w|) * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hcp (mul_nonneg hX hr0.le)
        _ = _ := by ring
  · have hr2 : 1 ≤ |w| ^ 2 := by rw [sq]; nlinarith
    rw [min_eq_right hr2, min_eq_right hr1.le]
    simp only [mul_one]
    have huv : |u - v| ≤ 2 * B := (abs_sub _ _).trans (by linarith)
    have e1 : (u - v) ^ 2 ≤ (2 * B) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) huv 2
    have hGb : |G| ≤ X * (4 * B ^ 2) := by
      calc |G| ≤ X * (u - v) ^ 2 := bG
        _ ≤ X * (2 * B) ^ 2 := mul_le_mul_of_nonneg_left e1 hX
        _ = X * (4 * B ^ 2) := by ring
    have T1 : |d1 * g2| ≤ X * L := c10_aux_abs_mul2_le b1 hg2
    have hsf : |(u - v) / w| ≤ 2 * B := by
      rw [abs_div, div_le_iff₀ hr0]
      calc |u - v| ≤ 2 * B := huv
        _ ≤ 2 * B * |w| := le_mul_of_one_le_right (by linarith) hr1.le
    have T2 : |d2 * ((u - v) / w)| ≤ X * (2 * B) * (2 * B) :=
      c10_aux_abs_mul2_le (b2v.trans (mul_le_mul_of_nonneg_left huv hX)) hsf
    have T3 := hT3 _ hGb
    have T3' : 2 * (X * (4 * B ^ 2)) / |w| ≤ 2 * (X * (4 * B ^ 2)) := by
      rw [div_le_iff₀ hr0]
      exact le_mul_of_one_le_right (by positivity) hr1.le
    have hcp : L + 12 * B ^ 2 ≤ L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2 := by
      have := pow_nonneg hL0 3; have := sq_nonneg L; linarith
    have hcp2 : 4 * B ^ 2 ≤ L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2 := by
      have := pow_nonneg hL0 3; have := sq_nonneg L; have := sq_nonneg B; linarith
    constructor
    · calc |G| ≤ X * (4 * B ^ 2) := hGb
        _ ≤ X * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) := mul_le_mul_of_nonneg_left hcp2 hX
    · calc _ ≤ |d1 * g2| + |d2 * ((u - v) / w)| + |(1 + p) * G / w| := hsplit
        _ ≤ X * L + X * (2 * B) * (2 * B) + 2 * (X * (4 * B ^ 2)) := by linarith
        _ = X * (L + 12 * B ^ 2) := by ring
        _ ≤ X * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) := mul_le_mul_of_nonneg_left hcp hX

/-- Helper: chain rule for `Γ_ε` along a curve. -/
theorem c10_aux_Gamma_chain (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    {a b : ℝ → ℝ} {y a' b' : ℝ} (ha : HasDerivAt a a' y) (hb : HasDerivAt b b' y) :
    HasDerivAt (fun t => c10_N_pieces_Gamma p ε (a t) (b t))
      (c10_N_pieces_Gamma_d1 p ε (a y) (b y) * a' + c10_N_pieces_Gamma_d2 p ε (a y) (b y) * b') y := by
  have hG := c10_aux_G_smooth p ε hp hp1 hε
  have hd : HasFDerivAt (c10_aux_G p ε) (fderiv ℝ (c10_aux_G p ε) (a y, b y)) (a y, b y) :=
    (hG.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := hd.comp_hasDerivAt y (c10_aux_curve ha hb)
  obtain ⟨e1, e2⟩ := c10_aux_d_eq p ε hp hp1 hε (a y) (b y)
  have hab : ((a', b') : ℝ × ℝ) = a' • ((1 : ℝ), (0 : ℝ)) + b' • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have h' : HasDerivAt (fun t => c10_N_pieces_Gamma p ε (a t) (b t))
      (fderiv ℝ (c10_aux_G p ε) (a y, b y) (a', b')) y := h
  refine h'.congr_deriv ?_
  rw [e1, e2, hab, map_add, map_smul, map_smul]; simp [mul_comm]

/-- Helper: `Γ_ε` vanishes on the diagonal. -/
theorem c10_aux_Gamma_diag (p ε u : ℝ) : c10_N_pieces_Gamma p ε u u = 0 := by
  simp [c10_N_pieces_Gamma, c03_Gamma_eps, c03_P_eps]

/-- Helper: quadratic vanishing `|Γ_ε(u,v)| ≤ C ε (u-v)²` on `[-B,B]²` (constant of
`c10_aux_kernel_bounds`). -/
theorem c10_aux_Gamma_quad (p B : ℝ) (hp : 0 < p) (hp1 : p < 1) (hB : 1 ≤ B) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ u v : ℝ, |u| ≤ B → |v| ≤ B →
      |c10_N_pieces_Gamma_d1 p ε u v| ≤ C * ε ∧
      |c10_N_pieces_Gamma_d2 p ε u v| ≤ C * ε * |u - v| ∧
      |c10_N_pieces_Gamma_d1 p ε u v + c10_N_pieces_Gamma_d2 p ε u v| ≤ C * ε * (u - v) ^ 2 ∧
      |c10_N_pieces_Gamma p ε u v| ≤ C * ε * (u - v) ^ 2 := by
  obtain ⟨Ck, hCk, hk⟩ := c10_aux_kernel_bounds p B hp hp1 hB
  refine ⟨Ck, hCk, fun ε hε hε1 u v hu hv => ?_⟩
  obtain ⟨b1, -, -, -, -, b2v, bs, -, -⟩ := hk ε hε hε1 u v hu hv
  refine ⟨b1, b2v, bs, ?_⟩
  have hder : ∀ w, HasDerivAt (fun w' => c10_N_pieces_Gamma p ε u w')
      (c10_N_pieces_Gamma_d2 p ε u w) w := fun w => by
    have := c10_aux_Gamma_chain p ε hp hp1 hε (hasDerivAt_const w u) (hasDerivAt_id w)
    simpa using this
  have hbound : ∀ w ∈ uIcc u v, ‖c10_N_pieces_Gamma_d2 p ε u w‖ ≤ Ck * ε * |u - v| := by
    intro w hw
    have hwB : |w| ≤ B := by
      rcases le_total u v with h | h
      · rw [uIcc_of_le h] at hw; rw [abs_le] at hu hv ⊢; constructor <;> linarith [hw.1, hw.2]
      · rw [uIcc_of_ge h] at hw; rw [abs_le] at hu hv ⊢; constructor <;> linarith [hw.1, hw.2]
    have hw' : |u - w| ≤ |u - v| := by
      rcases le_total u v with h | h
      · rw [uIcc_of_le h] at hw
        rw [abs_of_nonpos (by linarith [hw.1]), abs_of_nonpos (by linarith)]; linarith [hw.2]
      · rw [uIcc_of_ge h] at hw
        rw [abs_of_nonneg (by linarith [hw.2]), abs_of_nonneg (by linarith)]; linarith [hw.1]
    rw [Real.norm_eq_abs]
    exact ((hk ε hε hε1 u w hu hwB).2.2.2.2.2.1).trans
      (mul_le_mul_of_nonneg_left hw' (mul_nonneg hCk.le hε))
  have := (convex_uIcc u v).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (hder w).hasDerivWithinAt) hbound left_mem_uIcc right_mem_uIcc
  rw [c10_aux_Gamma_diag, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
  calc _ ≤ Ck * ε * |u - v| * |v - u| := this
    _ = Ck * ε * (u - v) ^ 2 := by rw [abs_sub_comm v u, mul_assoc, ← sq, sq_abs]

/-- Helper: secant data near and far (second-derivative bound on `[-R-1,R+1]`). -/
theorem c10_aux_secant_local1 {g : ℝ → ℝ} (hg : W2inftyLoc g) {R L B : ℝ}
    (hgB : ∀ x, |deriv g x| ≤ B) (hg2 : ∀ᵐ x, x ∈ Icc (-R - 1) (R + 1) → |deriv (deriv g) x| ≤ L)
    {y z : ℝ} (hy : y ∈ Icc (-R) R) (hyz : y ≠ z) :
    |c01_secant g y z| ≤ B ∧
    (|y - z| ≤ 1 → |deriv g y - c01_secant g y z| ≤ |y - z| * L) := by
  obtain ⟨-, -, -, hnear, hfar⟩ := c10_secant_identities g hg y z hyz
  refine ⟨((hfar B hgB).2).trans (min_le_left _ _), fun h1 => (hnear L ?_).1⟩
  have h1' := abs_le.1 h1
  filter_upwards [hg2] with w hw hwI
  refine hw ⟨?_, ?_⟩
  · rcases le_total y z with h | h
    · rw [uIcc_of_le h] at hwI; linarith [hwI.1, hy.1]
    · rw [uIcc_of_ge h] at hwI; linarith [hwI.1, hy.1, h1'.2]
  · rcases le_total y z with h | h
    · rw [uIcc_of_le h] at hwI; linarith [hwI.2, hy.2, h1'.1]
    · rw [uIcc_of_ge h] at hwI; linarith [hwI.2, hy.2]

/-- Helper: joint continuity of the profile value numerator. -/
theorem c10_aux_Gamma_cont (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) :
    Continuous (fun q : ℝ × ℝ => c10_N_pieces_Gamma p ε (deriv g q.1) (c01_secant g q.1 q.2)) := by
  have sg : Continuous (fun q : ℝ × ℝ => c01_secant g q.1 q.2) := (c03_secant_continuous_bound g hg).1
  have dg : Continuous (fun q : ℝ × ℝ => deriv g q.1) := (hg.continuous_deriv le_rfl).comp continuous_fst
  have := (c10_aux_G_smooth p ε hp hp1 hε).continuous.comp (dg.prodMk sg)
  exact this

/-- Helper: measurability of the profile derivative numerator. -/
theorem c10_aux_K1_meas (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) :
    Measurable (fun q : ℝ × ℝ => c10_Ieps_local_K1 p ε g q.1 q.2) := by
  obtain ⟨c1, c2, c0⟩ := c10_aux_d_contDiff p ε hp hp1 hε
  have sg : Continuous (fun q : ℝ × ℝ => c01_secant g q.1 q.2) := (c03_secant_continuous_bound g hg).1
  have dg : Continuous (fun q : ℝ × ℝ => deriv g q.1) := (hg.continuous_deriv le_rfl).comp continuous_fst
  have d2g : Measurable (fun q : ℝ × ℝ => deriv (deriv g) q.1) :=
    (measurable_deriv (deriv g)).comp measurable_fst
  have m1 : Measurable (fun q : ℝ × ℝ => c10_N_pieces_Gamma_d1 p ε (deriv g q.1) (c01_secant g q.1 q.2)) :=
    (c1.continuous.comp (dg.prodMk sg)).measurable
  have m2 : Measurable (fun q : ℝ × ℝ => c10_N_pieces_Gamma_d2 p ε (deriv g q.1) (c01_secant g q.1 q.2)) :=
    (c2.continuous.comp (dg.prodMk sg)).measurable
  have m0 : Measurable (fun q : ℝ × ℝ => c10_N_pieces_Gamma p ε (deriv g q.1) (c01_secant g q.1 q.2)) :=
    (c0.continuous.comp (dg.prodMk sg)).measurable
  have hw : Measurable (fun q : ℝ × ℝ => q.1 - q.2) := by fun_prop
  unfold c10_Ieps_local_K1
  exact ((m1.mul d2g).add (m2.mul ((dg.measurable.sub sg.measurable).div hw))).sub
    ((measurable_const.mul m0).div hw)

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_profile_kernel_bounds.  For `0 < p < 1`, `α = 1+p`, `B, L ≥ 1` there is
`C = C(p,B,L)` such that for `R ≥ 1`, `0 ≤ ε ≤ 1`, `g ∈ W^{2,∞}_loc` with `‖g'‖_∞ ≤ B` and
`‖g''‖_{L^∞} ≤ L` on `[-R-2,R+2]` (or, alternatively, on `[-2R,2R]`), the pair
`H_g = Γ_ε(g'(y),S_g)/|y-z|^α`, `J_g = K⁽¹⁾_g/|y-z|^α` (`g''` the classical derivative where it
exists, zero otherwise = Lean's `deriv`) is a dominated kernel pair on `(-R,R)` with constant
`C ε`; the envelope inequalities also hold for `|y| ≤ R` (pointwise for `H_g`, a.e. for `J_g`). -/
theorem c10_profile_kernel_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (B L : ℝ) (hB : 1 ≤ B)
    (hL : 1 ≤ L) :
    ∃ C > 0, ∀ R : ℝ, 1 ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ g : ℝ → ℝ, W2inftyLoc g → (∀ y, |deriv g y| ≤ B) →
      ((∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv g) y| ≤ L) ∨
        (∀ᵐ y, y ∈ Icc (-2 * R) (2 * R) → |deriv (deriv g) y| ≤ L)) →
      c10_local_kernel_pair (p + 1) (Ioo (-R) R) (C * ε)
        (fun y z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / |y - z| ^ (p + 1))
        (fun y z => c10_Ieps_local_K1 p ε g y z / |y - z| ^ (p + 1)) ∧
      (∀ y ∈ Icc (-R) R, ∀ z : ℝ, z ≠ y →
        |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / |y - z| ^ (p + 1)| ≤
          C * ε * c10_local_kernel_pair_omega0 (p + 1) (y - z)) ∧
      (∀ᵐ y, y ∈ Icc (-R) R → ∀ z : ℝ, z ≠ y →
        |c10_Ieps_local_K1 p ε g y z / |y - z| ^ (p + 1)| ≤
          C * ε * c10_local_kernel_pair_omega1 (p + 1) (y - z)) := by
  obtain ⟨Ck, hCk, hk⟩ := c10_aux_Gamma_quad p B hp hp1 hB
  refine ⟨Ck * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2), by positivity, ?_⟩
  intro R hR ε hε hε1 g hg hgB hg2
  have hα : (p + 1) ≠ 0 := by linarith
  have hg1 : ∀ᵐ x, x ∈ Icc (-R - 1) (R + 1) → |deriv (deriv g) x| ≤ L := by
    rcases hg2 with h | h
    · filter_upwards [h] with x hx hxI
      exact hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
    · filter_upwards [h] with x hx hxI
      exact hx ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  have alg : ∀ y ∈ Icc (-R) R, ∀ z : ℝ, z ≠ y → ∀ g2 : ℝ, |g2| ≤ L →
      |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)| ≤
        Ck * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) * ε * min (|y - z| ^ 2) 1 ∧
      |c10_N_pieces_Gamma_d1 p ε (deriv g y) (c01_secant g y z) * g2 +
          c10_N_pieces_Gamma_d2 p ε (deriv g y) (c01_secant g y z) *
            ((deriv g y - c01_secant g y z) / (y - z)) -
          (1 + p) * c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / (y - z)| ≤
        Ck * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) * ε * min |y - z| 1 := by
    intro y hy z hzy g2 hg2'
    have hyz : y ≠ z := Ne.symm hzy
    obtain ⟨sB, sN⟩ := c10_aux_secant_local1 hg hgB hg1 hy hyz
    obtain ⟨b1, b2v, bs, bG⟩ := hk ε hε hε1 (deriv g y) (c01_secant g y z) (hgB y) sB
    have := c10_aux_prof_alg (X := Ck * ε) (g2 := g2) (w := y - z) (p := p)
      (mul_nonneg hCk.le hε) hL hB (sub_ne_zero.2 hyz) hp hp1 b1 b2v bs bG (hgB y) sB hg2' sN
    constructor
    · refine this.1.trans (le_of_eq ?_); ring
    · refine this.2.trans (le_of_eq ?_); ring
  have hPae : ∀ᵐ y, DifferentiableAt ℝ (deriv g) y ∧
      (y ∈ Icc (-R - 1) (R + 1) → |deriv (deriv g) y| ≤ L) := by
    filter_upwards [c10_aux_ae_differentiableAt hg.2, hg1] with y a b using ⟨a, b⟩
  have hIcc : ∀ y ∈ Icc (-R) R, y ∈ Icc (-R - 1) (R + 1) := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hpowm : Measurable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (p + 1)) := by fun_prop
  have homega : ∀ y z : ℝ, z ≠ y → ∀ (A t : ℝ), |t| ≤ A * min (|y - z| ^ 2) 1 →
      |t / |y - z| ^ (p + 1)| ≤ A * c10_local_kernel_pair_omega0 (p + 1) (y - z) := by
    intro y z hzy A t ht
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hpos : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.2 hw) _
    rw [abs_div, abs_of_pos hpos, c10_local_kernel_pair_omega0, if_neg hw, mul_div_assoc']
    exact div_le_div_of_nonneg_right ht hpos.le
  have homega1 : ∀ y z : ℝ, z ≠ y → ∀ (A t : ℝ), |t| ≤ A * min |y - z| 1 →
      |t / |y - z| ^ (p + 1)| ≤ A * c10_local_kernel_pair_omega1 (p + 1) (y - z) := by
    intro y z hzy A t ht
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hpos : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.2 hw) _
    rw [abs_div, abs_of_pos hpos, c10_local_kernel_pair_omega1, if_neg hw, mul_div_assoc']
    exact div_le_div_of_nonneg_right ht hpos.le
  have Hb : ∀ y ∈ Icc (-R) R, ∀ z : ℝ, z ≠ y →
      |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / |y - z| ^ (p + 1)| ≤
        Ck * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) * ε *
          c10_local_kernel_pair_omega0 (p + 1) (y - z) := fun y hy z hzy =>
    homega y z hzy _ _ (alg y hy z hzy 0 (by simp; linarith)).1
  have Jb : ∀ y ∈ Icc (-R) R, (DifferentiableAt ℝ (deriv g) y ∧
      (y ∈ Icc (-R - 1) (R + 1) → |deriv (deriv g) y| ≤ L)) → ∀ z : ℝ, z ≠ y →
      |c10_Ieps_local_K1 p ε g y z / |y - z| ^ (p + 1)| ≤
        Ck * (L ^ 3 + 4 * L ^ 2 + L + 12 * B ^ 2) * ε *
          c10_local_kernel_pair_omega1 (p + 1) (y - z) := fun y hy hPy z hzy =>
    homega1 y z hzy _ _ (by unfold c10_Ieps_local_K1; exact (alg y hy z hzy _ (hPy.2 (hIcc y hy))).2)
  refine ⟨⟨?_, ?_, fun y _ => ?_, fun z => ⟨?_, ?_⟩, fun y hy z hzy => Hb y
    (Ioo_subset_Icc_self hy) z hzy, ?_⟩, Hb, ?_⟩
  · exact (c10_aux_Gamma_cont p ε hp hp1 hε hg.1).measurable.div hpowm
  · exact (c10_aux_K1_meas p ε hp hp1 hε hg.1).div hpowm
  · have h0 : (0 : ℝ) ^ (p + 1) = 0 := Real.zero_rpow hα
    simp [h0]
  · have hsec : LocallyLipschitzOn {z}ᶜ (fun y => c01_secant g y z) :=
      c10_aux_llo_of_contDiffAt fun y hy =>
        (c10_secant_identities g hg y z hy).2.1.contDiffAt (isOpen_compl_singleton.mem_nhds hy)
    exact (c10_aux_llo_div_pow (p + 1) (c10_aux_llo_comp2
      (c10_aux_d_contDiff p ε hp hp1 hε).2.2.locallyLipschitz (hg.2.locallyLipschitzOn) hsec)).mono
      (fun y hy => hy.2)
  · filter_upwards [hPae] with y hPy hy
    have hzy : y ≠ z := hy.2
    have hc := c10_aux_Gamma_chain p ε hp hp1 hε hPy.1.hasDerivAt
      (c10_secant_identities g hg y z hzy).2.2.1
    have hd := c10_aux_div_pow_hasDeriv (α := p + 1) hc hzy
    refine hd.congr_deriv ?_
    unfold c10_Ieps_local_K1; ring
  · refine ⟨{y | ¬ (DifferentiableAt ℝ (deriv g) y ∧
      (y ∈ Icc (-R - 1) (R + 1) → |deriv (deriv g) y| ≤ L))}, ae_iff.1 hPae, fun y hy z hzy => ?_⟩
    exact Jb y (Ioo_subset_Icc_self hy.1) (not_not.1 hy.2) z hzy
  · filter_upwards [hPae] with y hPy hy z hzy using Jb y hy hPy z hzy

/-- Helper: `f + t h` stays in `W^{2,∞}_loc`, with the linear formulas for its derivatives and
secants. -/
theorem c10_aux_lin_W2 {f h : ℝ → ℝ} (hf : W2inftyLoc f) (hh : W2inftyLoc h) (t : ℝ) :
    W2inftyLoc (f + t • h) ∧ (∀ y, deriv (f + t • h) y = deriv f y + t * deriv h y) ∧
    (∀ y z, c01_secant (f + t • h) y z = c01_secant f y z + t * c01_secant h y z) ∧
    (∀ y, DifferentiableAt ℝ (deriv f) y → DifferentiableAt ℝ (deriv h) y →
      deriv (deriv (f + t • h)) y = deriv (deriv f) y + t * deriv (deriv h) y) := by
  have df : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  have dh : Differentiable ℝ h := hh.1.differentiable (by norm_num)
  have hd : deriv (f + t • h) = fun y => deriv f y + t * deriv h y := by
    funext y
    rw [deriv_add (df y) ((dh y).const_smul t), deriv_const_smul t (dh y), smul_eq_mul]
  refine ⟨⟨hf.1.add (hh.1.const_smul t), ?_⟩, fun y => by rw [hd], fun y z => ?_, fun y h1 h2 => ?_⟩
  · rw [hd]
    have : LocallyLipschitz (fun y => t * deriv h y) :=
      c10_aux_locLip_mul (LipschitzWith.const t).locallyLipschitz hh.2
    exact hf.2.add this
  · unfold c01_secant
    split_ifs with hyz
    · rw [hd]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · rw [hd]
    exact ((h1.hasDerivAt).add (h2.hasDerivAt.const_mul t)).deriv

/-- Helper: recover the numerator bound from an envelope bound. -/
theorem c10_aux_of_omega0 {α t A y z : ℝ} (hzy : z ≠ y)
    (h : |t / |y - z| ^ α| ≤ A * c10_local_kernel_pair_omega0 α (y - z)) :
    |t| ≤ A * min (|y - z| ^ 2) 1 := by
  have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
  have hpos : 0 < |y - z| ^ α := Real.rpow_pos_of_pos (abs_pos.2 hw) _
  rw [abs_div, abs_of_pos hpos, c10_local_kernel_pair_omega0, if_neg hw, mul_div_assoc',
    div_le_div_iff_of_pos_right hpos] at h
  exact h

/-- Helper: `|deriv φ| ≤ K` on the interior of an interval where `φ` is `K`-Lipschitz. -/
theorem c10_aux_loc_deriv_bound {φ : ℝ → ℝ} (hφ : LocallyLipschitz φ) (a : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x ∈ Ioo (-a) a, |deriv φ x| ≤ K := by
  obtain ⟨K, hK⟩ := (hφ.locallyLipschitzOn (s := Icc (-a) a)).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  refine ⟨max K 1, le_max_right _ _, fun x hx => ?_⟩
  have := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hK
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_parameter_differentiation.  For `f, h ∈ W^{2,∞}_loc` with bounded first
derivatives and every `y`, `t ↦ ℐ_ε(f+th)(y)` is `C¹`, its defining integrals and the derivative
integrals converge absolutely, and `d/dt ℐ_ε(f+th)(y) = ∫ K_{f+th,h}(y,z)|y-z|^{-α} dz`.
Quantitatively, for `B, L ≥ 1`, `T ≥ 0` there is `C = C(p,B,L,T)` such that for `R ≥ 1`,
`‖f'‖_∞, ‖h'‖_∞ ≤ B`, `‖f''‖, ‖h''‖ ≤ L` on `[-R-2,R+2]`, `|y| < R`, `|t| ≤ T`, `z ≠ y`:
`|Γ_ε((f+th)'(y), S_{f+th}(y,z))| + |K_{f+th,h}(y,z)| ≤ C ε min(|y-z|², 1)`. -/
theorem c10_parameter_differentiation (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ f h : ℝ → ℝ, W2inftyLoc f → W2inftyLoc h →
      (∃ B : ℝ, ∀ y, |deriv f y| ≤ B) → (∃ B : ℝ, ∀ y, |deriv h y| ≤ B) → ∀ y : ℝ,
      ContDiff ℝ 1 (fun t : ℝ => c10_N_pieces_I p ε (f + t • h) y) ∧
      (∀ t : ℝ, Integrable (fun z => c10_N_pieces_Gamma p ε (deriv (f + t • h) y)
        (c01_secant (f + t • h) y z) / |y - z| ^ (p + 1))) ∧
      (∀ t : ℝ, Integrable (fun z => c10_N3_linearization_K p ε (f + t • h) h y z /
        |y - z| ^ (p + 1))) ∧
      ∀ t : ℝ, HasDerivAt (fun t : ℝ => c10_N_pieces_I p ε (f + t • h) y)
        (∫ z, c10_N3_linearization_K p ε (f + t • h) h y z / |y - z| ^ (p + 1)) t) ∧
    ∀ B L : ℝ, 1 ≤ B → 1 ≤ L → ∀ T : ℝ, 0 ≤ T → ∃ C > 0, ∀ R : ℝ, 1 ≤ R →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ f h : ℝ → ℝ, W2inftyLoc f → W2inftyLoc h →
      (∀ y, |deriv f y| ≤ B) → (∀ y, |deriv h y| ≤ B) →
      (∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv f) y| ≤ L) →
      (∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv h) y| ≤ L) →
      ∀ y : ℝ, |y| < R → ∀ t : ℝ, |t| ≤ T → ∀ z : ℝ, z ≠ y →
        |c10_N_pieces_Gamma p ε (deriv (f + t • h) y) (c01_secant (f + t • h) y z)| +
            |c10_N3_linearization_K p ε (f + t • h) h y z| ≤
          C * ε * min (|y - z| ^ 2) 1 := by
  have part2 : ∀ B L : ℝ, 1 ≤ B → 1 ≤ L → ∀ T : ℝ, 0 ≤ T → ∃ C > 0, ∀ R : ℝ, 1 ≤ R →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ f h : ℝ → ℝ, W2inftyLoc f → W2inftyLoc h →
      (∀ y, |deriv f y| ≤ B) → (∀ y, |deriv h y| ≤ B) →
      (∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv f) y| ≤ L) →
      (∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv h) y| ≤ L) →
      ∀ y : ℝ, |y| < R → ∀ t : ℝ, |t| ≤ T → ∀ z : ℝ, z ≠ y →
        |c10_N_pieces_Gamma p ε (deriv (f + t • h) y) (c01_secant (f + t • h) y z)| +
            |c10_N3_linearization_K p ε (f + t • h) h y z| ≤
          C * ε * min (|y - z| ^ 2) 1 := by
    intro B L hB hL T hT
    have hB' : 1 ≤ B * (1 + T) := by nlinarith
    have hL' : 1 ≤ L * (1 + T) := by nlinarith
    obtain ⟨Cp, hCp, hP⟩ := c10_profile_kernel_bounds p hp hp1 _ _ hB' hL'
    obtain ⟨Cv, hCv, hV⟩ := c10_variation_kernel_bounds p hp hp1 _ _ hB' hL'
    refine ⟨Cp + Cv * (B + L), by positivity, ?_⟩
    intro R hR ε hε hε1 f h hf hh hfB hhB hf2 hh2 y hy t ht z hzy
    obtain ⟨hW, hd, -, hd2⟩ := c10_aux_lin_W2 hf hh t
    have hfB' : ∀ x, |deriv (f + t • h) x| ≤ B * (1 + T) := fun x => by
      rw [hd]
      calc |deriv f x + t * deriv h x| ≤ |deriv f x| + |t| * |deriv h x| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ B + T * B := add_le_add (hfB x) (mul_le_mul ht (hhB x) (abs_nonneg _) hT)
        _ = B * (1 + T) := by ring
    have hf2' : ∀ᵐ x, x ∈ Icc (-R - 2) (R + 2) → |deriv (deriv (f + t • h)) x| ≤ L * (1 + T) := by
      filter_upwards [hf2, hh2, c10_aux_ae_differentiableAt hf.2,
        c10_aux_ae_differentiableAt hh.2] with x h1 h2 h3 h4 hx
      rw [hd2 x h3 h4]
      calc |deriv (deriv f) x + t * deriv (deriv h) x| ≤
            |deriv (deriv f) x| + |t| * |deriv (deriv h) x| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ L + T * L := add_le_add (h1 hx) (mul_le_mul ht (h2 hx) (abs_nonneg _) hT)
        _ = L * (1 + T) := by ring
    have hyI : y ∈ Ioo (-R) R := abs_lt.1 hy
    have hΓ := c10_aux_of_omega0 hzy ((hP R hR ε hε hε1 (f + t • h) hW hfB' (Or.inl hf2')).2.1 y
      (Ioo_subset_Icc_self hyI) z hzy)
    have hK := (hV R hR ε hε hε1 (B + L) (by linarith) (f + t • h) h hW hh hfB'
      (fun x => (hhB x).trans (by linarith))
      hf2' (by filter_upwards [hh2] with x hx hxI using (hx hxI).trans (by linarith))).2.1 y hyI
      z hzy
    have hm : 0 ≤ min (|y - z| ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    calc _ ≤ Cp * ε * min (|y - z| ^ 2) 1 + Cv * ε * (B + L) * min (|y - z| ^ 2) 1 :=
          add_le_add hΓ hK
      _ = (Cp + Cv * (B + L)) * ε * min (|y - z| ^ 2) 1 := by ring
  refine ⟨?_, part2⟩
  intro ε hε hε1 f h hf hh ⟨Bf, hBf⟩ ⟨Bh, hBh⟩ y
  set B := max (max Bf Bh) 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hfB : ∀ x, |deriv f x| ≤ B := fun x => (hBf x).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hhB : ∀ x, |deriv h x| ≤ B := fun x => (hBh x).trans ((le_max_right _ _).trans (le_max_left _ _))
  set R := |y| + 1 with hRdef
  have hR : 1 ≤ R := by have := abs_nonneg y; linarith
  have hyR : |y| < R := by linarith
  obtain ⟨Kf, hKf1, hKf⟩ := c10_aux_loc_deriv_bound hf.2 (R + 3)
  obtain ⟨Kh, hKh1, hKh⟩ := c10_aux_loc_deriv_bound hh.2 (R + 3)
  set L := max Kf Kh
  have hL1 : 1 ≤ L := hKf1.trans (le_max_left _ _)
  have hf2 : ∀ᵐ x, x ∈ Icc (-R - 2) (R + 2) → |deriv (deriv f) x| ≤ L := Eventually.of_forall
    fun x hx => (hKf x ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans (le_max_left _ _)
  have hh2 : ∀ᵐ x, x ∈ Icc (-R - 2) (R + 2) → |deriv (deriv h) x| ≤ L := Eventually.of_forall
    fun x hx => (hKh x ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans (le_max_right _ _)
  have hα : (p + 1) ≠ 0 := by linarith
  obtain ⟨-, -, -, -, io0, -⟩ := c10_kernel_envelopes (p + 1) (by linarith) (by linarith)
  -- explicit forms
  have hlin := fun t : ℝ => c10_aux_lin_W2 hf hh t
  set u0 := deriv f y
  set u1 := deriv h y
  set S0 := fun z => c01_secant f y z
  set S1 := fun z => c01_secant h y z
  have hS0 : Continuous S0 := ((c03_secant_continuous_bound f hf.1).1).comp
    (continuous_const.prodMk continuous_id)
  have hS1 : Continuous S1 := ((c03_secant_continuous_bound h hh.1).1).comp
    (continuous_const.prodMk continuous_id)
  have eF : ∀ t z, c10_N_pieces_Gamma p ε (deriv (f + t • h) y) (c01_secant (f + t • h) y z) /
      |y - z| ^ (p + 1) = c10_N_pieces_Gamma p ε (u0 + t * u1) (S0 z + t * S1 z) / |y - z| ^ (p + 1) :=
    fun t z => by rw [(hlin t).2.1 y, (hlin t).2.2.1 y z]
  have eF' : ∀ t z, c10_N3_linearization_K p ε (f + t • h) h y z / |y - z| ^ (p + 1) =
      (c10_N_pieces_Gamma_d1 p ε (u0 + t * u1) (S0 z + t * S1 z) * u1 +
        c10_N_pieces_Gamma_d2 p ε (u0 + t * u1) (S0 z + t * S1 z) * S1 z) / |y - z| ^ (p + 1) :=
    fun t z => by unfold c10_N3_linearization_K; rw [(hlin t).2.1 y, (hlin t).2.2.1 y z]
  obtain ⟨c1, c2, c0⟩ := c10_aux_d_contDiff p ε hp hp1 hε
  have hpowm : Measurable (fun z : ℝ => |y - z| ^ (p + 1)) := by fun_prop
  have hFm : ∀ t, AEStronglyMeasurable (fun z => c10_N_pieces_Gamma p ε (deriv (f + t • h) y)
      (c01_secant (f + t • h) y z) / |y - z| ^ (p + 1)) volume := fun t => by
    rw [show (fun z => c10_N_pieces_Gamma p ε (deriv (f + t • h) y) (c01_secant (f + t • h) y z) /
      |y - z| ^ (p + 1)) = fun z => c10_N_pieces_Gamma p ε (u0 + t * u1) (S0 z + t * S1 z) /
      |y - z| ^ (p + 1) from funext (eF t)]
    have : Continuous (fun z => c10_N_pieces_Gamma p ε (u0 + t * u1) (S0 z + t * S1 z)) := by
      have := (c10_aux_G_smooth p ε hp hp1 hε).continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => u0 + t * u1).prodMk
          (hS0.add ((continuous_const : Continuous fun _ : ℝ => t).mul hS1)))
      exact this
    exact (this.measurable.div hpowm).aestronglyMeasurable
  have hF'cont : ∀ z, Continuous (fun t : ℝ =>
      (c10_N_pieces_Gamma_d1 p ε (u0 + t * u1) (S0 z + t * S1 z) * u1 +
        c10_N_pieces_Gamma_d2 p ε (u0 + t * u1) (S0 z + t * S1 z) * S1 z) / |y - z| ^ (p + 1)) := by
    intro z
    have hab : Continuous (fun t : ℝ => ((u0 + t * u1, S0 z + t * S1 z) : ℝ × ℝ)) := by fun_prop
    exact (((c1.continuous.comp hab).mul continuous_const).add
      ((c2.continuous.comp hab).mul continuous_const)).div_const _
  have hF'm : ∀ t, AEStronglyMeasurable (fun z => c10_N3_linearization_K p ε (f + t • h) h y z /
      |y - z| ^ (p + 1)) volume := fun t => by
    rw [show (fun z => c10_N3_linearization_K p ε (f + t • h) h y z / |y - z| ^ (p + 1)) =
      fun z => (c10_N_pieces_Gamma_d1 p ε (u0 + t * u1) (S0 z + t * S1 z) * u1 +
        c10_N_pieces_Gamma_d2 p ε (u0 + t * u1) (S0 z + t * S1 z) * S1 z) / |y - z| ^ (p + 1)
      from funext (eF' t)]
    have hab : Continuous (fun z : ℝ => ((u0 + t * u1, S0 z + t * S1 z) : ℝ × ℝ)) :=
      (continuous_const : Continuous fun _ : ℝ => u0 + t * u1).prodMk
        (hS0.add ((continuous_const : Continuous fun _ : ℝ => t).mul hS1))
    exact ((((c1.continuous.comp hab).mul continuous_const).add
      ((c2.continuous.comp hab).mul hS1)).measurable.div hpowm).aestronglyMeasurable
  -- uniform bounds on `|t| ≤ T`
  have bounds : ∀ T : ℝ, 0 ≤ T → ∃ C > 0, ∀ t : ℝ, |t| ≤ T → ∀ z : ℝ,
      |c10_N_pieces_Gamma p ε (deriv (f + t • h) y) (c01_secant (f + t • h) y z) /
          |y - z| ^ (p + 1)| ≤ C * ε * c10_local_kernel_pair_omega0 (p + 1) (y - z) ∧
      |c10_N3_linearization_K p ε (f + t • h) h y z / |y - z| ^ (p + 1)| ≤
          C * ε * c10_local_kernel_pair_omega0 (p + 1) (y - z) := by
    intro T hT
    obtain ⟨C, hC, hb⟩ := part2 B L hB1 hL1 T hT
    refine ⟨C, hC, fun t ht z => ?_⟩
    by_cases hzy : z = y
    · subst hzy
      have h0 : |z - z| ^ (p + 1) = 0 := by rw [sub_self, abs_zero, Real.zero_rpow hα]
      have hω : 0 ≤ c10_local_kernel_pair_omega0 (p + 1) (z - z) := by
        simp [c10_local_kernel_pair_omega0]
      rw [h0, div_zero, div_zero, abs_zero]
      exact ⟨mul_nonneg (mul_nonneg hC.le hε) hω, mul_nonneg (mul_nonneg hC.le hε) hω⟩
    · have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
      have hpos : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.2 hw) _
      have := hb R hR ε hε hε1 f h hf hh hfB hhB hf2 hh2 y hyR t ht z hzy
      rw [abs_div, abs_div, abs_of_pos hpos, c10_local_kernel_pair_omega0, if_neg hw,
        mul_div_assoc']
      have k1 := abs_nonneg (c10_N3_linearization_K p ε (f + t • h) h y z)
      have k2 := abs_nonneg (c10_N_pieces_Gamma p ε (deriv (f + t • h) y) (c01_secant (f + t • h) y z))
      constructor
      · exact div_le_div_of_nonneg_right (by linarith) hpos.le
      · exact div_le_div_of_nonneg_right (by linarith) hpos.le
  have hbint : ∀ C : ℝ, Integrable (fun z => C * ε * c10_local_kernel_pair_omega0 (p + 1) (y - z)) :=
    fun C => (io0.comp_sub_left y).const_mul _
  have hFint : ∀ t : ℝ, Integrable (fun z => c10_N_pieces_Gamma p ε (deriv (f + t • h) y)
      (c01_secant (f + t • h) y z) / |y - z| ^ (p + 1)) := fun t => by
    obtain ⟨C, -, hb⟩ := bounds |t| (abs_nonneg t)
    exact Integrable.mono' (hbint C) (hFm t) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact (hb t le_rfl z).1)
  have hF'int : ∀ t : ℝ, Integrable (fun z => c10_N3_linearization_K p ε (f + t • h) h y z /
      |y - z| ^ (p + 1)) := fun t => by
    obtain ⟨C, -, hb⟩ := bounds |t| (abs_nonneg t)
    exact Integrable.mono' (hbint C) (hF'm t) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact (hb t le_rfl z).2)
  have hderiv : ∀ t0 : ℝ, HasDerivAt (fun t : ℝ => c10_N_pieces_I p ε (f + t • h) y)
      (∫ z, c10_N3_linearization_K p ε (f + t0 • h) h y z / |y - z| ^ (p + 1)) t0 := by
    intro t0
    obtain ⟨C, -, hb⟩ := bounds (|t0| + 1) (by positivity)
    have hball : ∀ t ∈ Metric.ball t0 1, |t| ≤ |t0| + 1 := fun t ht => by
      rw [Metric.mem_ball, Real.dist_eq] at ht
      have := abs_sub_abs_le_abs_sub t t0; linarith
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun t z => c10_N_pieces_Gamma p ε (deriv (f + t • h) y) (c01_secant (f + t • h) y z) /
        |y - z| ^ (p + 1))
      (F' := fun t z => c10_N3_linearization_K p ε (f + t • h) h y z / |y - z| ^ (p + 1))
      (x₀ := t0) (bound := fun z => C * ε * c10_local_kernel_pair_omega0 (p + 1) (y - z))
      (Metric.ball_mem_nhds t0 one_pos) (Eventually.of_forall hFm) (hFint t0) (hF'm t0)
      (Eventually.of_forall fun z t ht => by
        rw [Real.norm_eq_abs]; exact (hb t (hball t ht) z).2) (hbint C)
      (Eventually.of_forall fun z t _ => by
        have hc := c10_aux_Gamma_chain p ε hp hp1 hε (a := fun t => u0 + t * u1)
          (b := fun t => S0 z + t * S1 z) (y := t) (a' := u1) (b' := S1 z)
          (by simpa using ((hasDerivAt_id t).mul_const u1).const_add u0)
          (by simpa using ((hasDerivAt_id t).mul_const (S1 z)).const_add (S0 z))
        have hc' := hc.div_const (|y - z| ^ (p + 1))
        simp only [eF, eF']
        exact hc')
    exact key.2
  refine ⟨?_, hFint, hF'int, hderiv⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hderiv t).differentiableAt, ?_⟩
  have hd : deriv (fun t : ℝ => c10_N_pieces_I p ε (f + t • h) y) =
      fun t => ∫ z, c10_N3_linearization_K p ε (f + t • h) h y z / |y - z| ^ (p + 1) :=
    funext fun t => (hderiv t).deriv
  rw [hd, continuous_iff_continuousAt]
  intro t0
  obtain ⟨C, -, hb⟩ := bounds (|t0| + 1) (by positivity)
  refine continuousAt_of_dominated (Eventually.of_forall hF'm) ?_ (hbint C)
    (Eventually.of_forall fun z => by simp only [eF']; exact (hF'cont z).continuousAt)
  filter_upwards [Metric.ball_mem_nhds t0 one_pos] with t ht
  have : |t| ≤ |t0| + 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t0; linarith
  exact Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hb t this z).2

/-- Helper: a concrete smooth diagonal cutoff `ϑ(x) = ψ((x²-1)/3)` (`ψ` the smooth transition). -/
theorem c10_aux_theta_exists : ∃ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ x, θ x ∈ Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Icc (-1 : ℝ) 1, θ x = 0) ∧ (∀ x, x ∉ Ioo (-2 : ℝ) 2 → θ x = 1) ∧
    ∃ M : ℝ, ∀ x, |deriv θ x| ≤ M := by
  set θ : ℝ → ℝ := fun x => Real.smoothTransition ((x ^ 2 - 1) / 3) with hθdef
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.pow 2).sub contDiff_const |>.div_const 3)
  have h1 : ∀ x, x ∉ Ioo (-2 : ℝ) 2 → θ x = 1 := fun x hx => by
    apply Real.smoothTransition.one_of_one_le
    have : 2 ≤ |x| := by
      by_contra h; push_neg at h; exact hx (abs_lt.1 h)
    have : 4 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hθ.continuous_deriv (by simp)).continuousOn (s := Icc (-2 : ℝ) 2))
  refine ⟨θ, hθ, fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun x hx => ?_, h1, max M 0, fun x => ?_⟩
  · apply Real.smoothTransition.zero_of_nonpos
    have : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    linarith
  · by_cases hx : x ∈ Icc (-2 : ℝ) 2
    · rw [← Real.norm_eq_abs]; exact (hM x hx).trans (le_max_left _ _)
    · have hev : θ =ᶠ[nhds x] fun _ => 1 := by
        have hopen : IsOpen {y : ℝ | y ∉ Icc (-2 : ℝ) 2} := isClosed_Icc.isOpen_compl
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact h1 y (fun h => hy (Ioo_subset_Icc_self h))
      rw [hev.deriv_eq]; simp

/-- Helper: the untruncated value integral of a dominated kernel pair is locally Lipschitz on `U`
with a.e. derivative given by the (a.e. absolutely convergent) derivative integral. Assembled from
lem:c10_cutoff_weak_derivative, lem:c10_cutoff_errors and lem:c10_local_weak_limit. -/
theorem c10_aux_pair_integral (α : ℝ) (hα : 1 < α) (hα2 : α < 2) (U : Set ℝ) (hU : IsOpen U)
    (hUc : U.OrdConnected) (hUne : U.Nonempty) (A : ℝ) (hA : 0 ≤ A) (H J : ℝ → ℝ → ℝ)
    (hHJ : c10_local_kernel_pair α U A H J) :
    (∀ y ∈ U, Integrable (H y)) ∧ (∀ᵐ y, y ∈ U → Integrable (J y)) ∧
    (∀ᵐ y, y ∈ U → |∫ z, J y z| ≤ A * (2 / (2 - α) + 2 / (α - 1))) ∧
    LocallyLipschitzOn U (fun y => ∫ z, H y z) ∧
    ∀ᵐ y, y ∈ U → HasDerivAt (fun y => ∫ z, H y z) (∫ z, J y z) y := by
  obtain ⟨θ, hθ, hθ01, hθ0, hθ1, Mθ, hMθ⟩ := c10_aux_theta_exists
  have hθc : Continuous θ := hθ.continuous
  have hθ'c : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  have hHm : Measurable (fun q : ℝ × ℝ => H q.1 q.2) := hHJ.1
  have hJm : Measurable (fun q : ℝ × ℝ => J q.1 q.2) := hHJ.2.1
  obtain ⟨-, -, -, -, -, io1, -, v1, -⟩ := c10_kernel_envelopes α hα hα2
  set η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3) with hη
  have hηpos : ∀ n, 0 < η n := fun n => by simp only [hη]; positivity
  have hη2 : ∀ n, η n < 1 / 2 := fun n => by
    simp only [hη]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [n.cast_nonneg (α := ℝ)]
  have hηt : Tendsto η atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have CW := fun n => c10_cutoff_weak_derivative α hα hα2 U hU hUc hUne A hA H J hHJ θ hθ hθ01 hθ0 hθ1
    Mθ hMθ (η n) (hηpos n) (hη2 n)
  have CE := fun n => c10_cutoff_errors α hα hα2 U hU hUc hUne A hA H J hHJ θ hθ hθ01 hθ0 hθ1
    Mθ hMθ (η n) (hηpos n) (hη2 n)
  obtain ⟨hHi, hJi, -, -⟩ := CE 0
  -- measurability of the truncated derivative integrals and of `∫ J`
  have hGm : ∀ n, Measurable (fun y => ∫ z, (θ ((y - z) / η n) * J y z +
      (η n)⁻¹ * deriv θ ((y - z) / η n) * H y z)) := fun n => by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 - q.2) / η n) := by fun_prop
    have hm : Measurable (fun q : ℝ × ℝ => θ ((q.1 - q.2) / η n) * J q.1 q.2 +
        (η n)⁻¹ * deriv θ ((q.1 - q.2) / η n) * H q.1 q.2) :=
      ((hθc.comp h1).measurable.mul hJm).add
        ((measurable_const.mul (hθ'c.comp h1).measurable).mul hHm)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hG₀m : Measurable (fun y => ∫ z, J y z) :=
    hJm.stronglyMeasurable.integral_prod_right'.measurable
  -- the a.e. bound for `∫ J`
  have hG₀b : ∀ᵐ y, y ∈ U → |∫ z, J y z| ≤ A * (2 / (2 - α) + 2 / (α - 1)) := by
    obtain ⟨E, hE0, hJb⟩ := hHJ.2.2.2.2.2
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE0] with y hyE hyU
    rw [← Real.norm_eq_abs]
    calc ‖∫ z, J y z‖ ≤ ∫ z, A * c10_local_kernel_pair_omega1 α (y - z) :=
          norm_integral_le_of_norm_le ((io1.comp_sub_left y).const_mul A)
            (Eventually.of_forall fun z => by
              rw [Real.norm_eq_abs]
              by_cases hz : z = y
              · subst hz; rw [(hHJ.2.2.1 z hyU).2, abs_zero]
                exact mul_nonneg hA ((c10_kernel_envelopes α hα hα2).2.1 _)
              · exact hJb y ⟨hyU, hyE⟩ z hz)
      _ = A * (2 / (2 - α) + 2 / (α - 1)) := by
          rw [integral_const_mul,
            integral_sub_left_eq_self (fun s => c10_local_kernel_pair_omega1 α s) volume y, v1]
  have hLinf : ∀ (g : ℝ → ℝ) (C : ℝ), Measurable g → (∀ᵐ y, y ∈ U → |g y| ≤ C) →
      ∀ a b : ℝ, Icc a b ⊆ U → eLpNorm g ⊤ (volume.restrict (Icc a b)) ≤ ENNReal.ofReal C := by
    intro g C hgm hg a b hsub
    rw [eLpNorm_exponent_top hgm.aestronglyMeasurable.restrict]
    apply eLpNormEssSup_le_of_ae_bound
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hg] with y hy hyI
    rw [Real.norm_eq_abs]; exact hy (hsub hyI)
  have hpow : ∀ q : ℝ, 0 < q → Tendsto (fun n => η n ^ q) atTop (nhds 0) := fun q hq => by
    have := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto.comp hηt
    rwa [Real.zero_rpow hq.ne'] at this
  have hFconv : TendstoLocallyUniformlyOn (fun n y => ∫ z, θ ((y - z) / η n) * H y z)
      (fun y => ∫ z, H y z) atTop U := by
    refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
    rw [Metric.tendstoUniformlyOn_iff]
    intro e he
    have hc : Tendsto (fun n => 2 ^ (4 - α) / (3 - α) * A * η n ^ (3 - α)) atTop (nhds 0) := by
      have := (hpow (3 - α) (by linarith)).const_mul (2 ^ (4 - α) / (3 - α) * A)
      rwa [mul_zero] at this
    filter_upwards [(tendsto_order.1 hc).2 e he] with n hn y hy
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt ((CE n).2.2.1 y hy) hn
  have hGconv : ∀ a b : ℝ, Icc a b ⊆ U →
      Tendsto (fun n => eLpNorm (fun y => (∫ z, (θ ((y - z) / η n) * J y z +
        (η n)⁻¹ * deriv θ ((y - z) / η n) * H y z)) - ∫ z, J y z) ⊤
          (volume.restrict (Icc a b))) atTop (nhds 0) := by
    intro a b hsub
    have hd : Tendsto (fun n => A * (2 ^ (3 - α) / (2 - α) + 2 ^ (4 - α) * Mθ / (3 - α)) *
        η n ^ (2 - α)) atTop (nhds 0) := by
      have := (hpow (2 - α) (by linarith)).const_mul (A * (2 ^ (3 - α) / (2 - α) +
        2 ^ (4 - α) * Mθ / (3 - α)))
      rwa [mul_zero] at this
    have hd' := ENNReal.tendsto_ofReal hd
    rw [ENNReal.ofReal_zero] at hd'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd'
      (fun _ => bot_le) (fun n => hLinf _ _ ((hGm n).sub hG₀m) (CE n).2.2.2 a b hsub)
  have WL := c10_local_weak_limit U hU hUc (fun n y => ∫ z, θ ((y - z) / η n) * H y z)
    (fun n y => ∫ z, (θ ((y - z) / η n) * J y z + (η n)⁻¹ * deriv θ ((y - z) / η n) * H y z))
    (fun y => ∫ z, H y z) (fun y => ∫ z, J y z) (fun n => (CW n).2.2.1) hGm hG₀m
    (fun n a b hsub => lt_of_le_of_lt (hLinf _ _ (hGm n) (CW n).2.2.2.2.1 a b hsub)
      ENNReal.ofReal_lt_top)
    (fun a b hsub => lt_of_le_of_lt (hLinf _ _ hG₀m hG₀b a b hsub) ENNReal.ofReal_lt_top)
    (fun n => (CW n).2.2.2.1) hFconv hGconv
  exact ⟨hHi, hJi, hG₀b, WL.1, WL.2.1⟩

/-- Helper: slices of a jointly measurable kernel are measurable. -/
theorem c10_aux_meas_slice {F : ℝ → ℝ → ℝ} (hF : Measurable (fun q : ℝ × ℝ => F q.1 q.2)) (y : ℝ) :
    Measurable (F y) :=
  hF.comp measurable_prodMk_left

/-- Helper: an a.e. bound for `g''` on `[a,b]` holds at every interior point. -/
theorem c10_aux_d2_bound {g : ℝ → ℝ} (hg : W2inftyLoc g) {a b L : ℝ} (hL : 0 ≤ L)
    (h2 : ∀ᵐ x, x ∈ Icc a b → |deriv (deriv g) x| ≤ L) :
    ∀ y ∈ Ioo a b, |deriv (deriv g) y| ≤ L := by
  intro y hy
  have hlip : LipschitzOnWith L.toNNReal (deriv g) (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun c hc d hd => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL]
    refine c10_aux_lip_of_ae_deriv hg.2 ?_
    filter_upwards [h2] with x hx hxI
    exact hx (uIcc_subset_Icc hd hc hxI)
  have := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hy.1 hy.2) hlip
  rwa [Real.norm_eq_abs, Real.coe_toNNReal _ hL] at this

/-- Helper: local Lipschitz regularity on all intervals `(-(n+1), n+1)` gives global local
Lipschitz regularity. -/
theorem c10_aux_locLip_of_Ioo {F : ℝ → ℝ} (h : ∀ n : ℕ, LocallyLipschitzOn
    (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)) F) : LocallyLipschitz F := by
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  have hx : x ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    constructor <;> linarith [neg_abs_le x, le_abs_self x]
  obtain ⟨K, t, ht, hK⟩ := h n hx
  rw [isOpen_Ioo.nhdsWithin_eq hx] at ht
  exact ⟨K, t, ht, hK⟩

/-- Helper: `b_ε` is `C¹` (it vanishes on `(-∞,1]` and equals `c_ε χ₊(y) y^{-p}` on `(1/2,∞)`). -/
theorem c10_aux_b_eps_contDiff (p ε : ℝ) : ContDiff ℝ 1 (b_eps p ε) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hχ : ContDiff ℝ 1 chiPlus := by
    unfold chiPlus
    exact (Real.smoothTransition.contDiff (n := 1)).comp (contDiff_id.sub contDiff_const)
  rcases lt_or_ge y 1 with hy | hy
  · have hev : b_eps p ε =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hy] with x hx
      simp only [b_eps, c08_phi_b]
      rw [if_neg (not_lt.2 (le_of_lt hx))]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : b_eps p ε =ᶠ[nhds y] fun x => c_eps p ε * chiPlus x * x ^ (-p) := by
      filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < y by linarith)] with x hx
      simp only [b_eps, c08_phi_b]
      split_ifs with h
      · rfl
      · have : chiPlus x = 0 := by
          unfold chiPlus; exact Real.smoothTransition.zero_of_nonpos (by linarith [not_lt.1 h])
        rw [this]; ring
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (contDiffAt_const.mul hχ.contDiffAt).mul
      (Real.contDiffAt_rpow_const_of_ne (by linarith))

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_N3_variation.  (1) absolute convergence of the integral defining
`D𝒩₃(r)[h](y)`; (2) `t ↦ 𝒩₃(r+th)(y)` is `C¹` with derivative `D𝒩₃(r+th)[h](y)`;
(3) `D𝒩₃(r)[h] ∈ W^{1,∞}_loc` with derivative given by the absolutely convergent (a.e.) integral of
`(∂_y K - α K/(y-z))|y-z|^{-α}` minus `∂_y(b_ε h')`. -/
-- Proof: a cutoff in `y-z` is used, keeping `z` fixed and retaining its derivative term.
-- Differentiating the shifted integrand `K y (y-t)` instead gives `(∂_y+∂_z)K`.
theorem c10_N3_variation (p γ M ε : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (fbar : ℝ → ℝ) (hfbar : nonlinear_admissible_profile p M fbar)
    (r : ℝ → ℝ) (hr : r ∈ X_gamma p γ) (h : ℝ → ℝ) (hh : h ∈ X_gamma p γ) :
    (∀ y, Integrable (fun z => c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1))) ∧
    (∀ y, ContDiff ℝ 1 (fun t : ℝ => c10_N_pieces_N3 p ε fbar (r + t • h) y) ∧
      ∀ t : ℝ, HasDerivAt (fun t : ℝ => c10_N_pieces_N3 p ε fbar (r + t • h) y)
        (c10_N3_linearization p ε fbar (r + t • h) h y) t) ∧
    (W1inftyLoc (c10_N3_linearization p ε fbar r h) ∧
      ∀ᵐ y, Integrable (fun z => c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1)) ∧
        deriv (c10_N3_linearization p ε fbar r h) y =
          (∫ z, c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
            deriv (fun x => b_eps p ε x * deriv h x) y) := by
  have hp0 : 0 < p := by linarith
  have hα : 1 < p + 1 := by linarith
  have hα2 : p + 1 < 2 := by linarith
  have hfA : fbar ∈ c01_admissible_class :=
    c10_aux_C2_admissible_class hfbar.1 (c10_aux_admissible_deriv_bdd p M hp0 hfbar)
  have hrA := c10_aux_X_admissible_class p γ hp hp1 hγ hr
  have hhA := c10_aux_X_admissible_class p γ hp hp1 hγ hh
  have hfbW : W2inftyLoc fbar := ⟨hfA.1, hfA.2.2⟩
  have hrW : W2inftyLoc r := ⟨hrA.1, hrA.2.2⟩
  have hhW : W2inftyLoc h := ⟨hhA.1, hhA.2.2⟩
  obtain ⟨hfW, hdf, -, -⟩ := c10_aux_lin_W2 hfbW hrW 1
  have e1 : fbar + (1 : ℝ) • r = fbar + r := by rw [one_smul]
  rw [e1] at hfW hdf
  obtain ⟨Bf0, hBf0⟩ := hfA.2.1
  obtain ⟨Br0, hBr0⟩ := hrA.2.1
  obtain ⟨Bh0, hBh0⟩ := hhA.2.1
  have hfB : ∀ y, |deriv (fbar + r) y| ≤ Bf0 + Br0 := fun y => by
    rw [hdf y, one_mul]; exact (abs_add_le _ _).trans (add_le_add (hBf0 y) (hBr0 y))
  have PD := (c10_parameter_differentiation p hp0 hp1).1 ε hε hε1 (fbar + r) h hfW hhW
    ⟨_, hfB⟩ ⟨_, hBh0⟩
  have e0 : fbar + r + (0 : ℝ) • h = fbar + r := by rw [zero_smul, add_zero]
  have eA : ∀ t : ℝ, fbar + (r + t • h) = fbar + r + t • h := fun t => (add_assoc _ _ _).symm
  refine ⟨fun y => ?_, fun y => ?_, ?_⟩
  · have := (PD y).2.2.1 0
    rwa [e0] at this
  · have hdr : ∀ t : ℝ, deriv (r + t • h) y = deriv r y + t * deriv h y := fun t =>
      (c10_aux_lin_W2 hrW hhW t).2.1 y
    have eN : (fun t : ℝ => c10_N_pieces_N3 p ε fbar (r + t • h) y) = fun t =>
        c10_N_pieces_I p ε (fbar + r + t • h) y - c10_N_pieces_I p ε fbar y -
          b_eps p ε y * (deriv r y + t * deriv h y) := by
      funext t; unfold c10_N_pieces_N3; rw [eA t, hdr t]
    rw [eN]
    refine ⟨((PD y).1.sub contDiff_const).sub (by fun_prop), fun t => ?_⟩
    have haff : HasDerivAt (fun t : ℝ => b_eps p ε y * (deriv r y + t * deriv h y))
        (b_eps p ε y * deriv h y) t := by
      have := (((hasDerivAt_id t).mul_const (deriv h y)).const_add (deriv r y)).const_mul
        (b_eps p ε y)
      simpa using this
    have := (((PD y).2.2.2 t).sub_const (c10_N_pieces_I p ε fbar y)).sub haff
    unfold c10_N3_linearization
    rw [eA t]
    exact this
  · -- (3): local assembly on `(-(n+1), n+1)`
    set f := fbar + r with hfdef
    have hbL : LocallyLipschitz (fun x => b_eps p ε x * deriv h x) :=
      c10_aux_locLip_mul (c10_aux_b_eps_contDiff p ε).locallyLipschitz hhW.2
    have per : ∀ n : ℕ, LocallyLipschitzOn (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))
          (fun y => ∫ z, c10_N3_linearization_K p ε f h y z / |y - z| ^ (p + 1)) ∧
        ∀ᵐ y, y ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) →
          Integrable (fun z => c10_N3_linearization_dK p ε f h y z / |y - z| ^ (p + 1)) ∧
          HasDerivAt (fun y => ∫ z, c10_N3_linearization_K p ε f h y z / |y - z| ^ (p + 1))
            (∫ z, c10_N3_linearization_dK p ε f h y z / |y - z| ^ (p + 1)) y := by
      intro n
      set R : ℝ := (n : ℝ) + 1
      have hR : 1 ≤ R := by simp only [R]; linarith [n.cast_nonneg (α := ℝ)]
      obtain ⟨Kf, hKf1, hKf⟩ := c10_aux_loc_deriv_bound hfW.2 (R + 3)
      obtain ⟨Kh, hKh1, hKh⟩ := c10_aux_loc_deriv_bound hhW.2 (R + 3)
      set B := max (Bf0 + Br0) 1
      have hB : 1 ≤ B := le_max_right _ _
      set H0 := max Bh0 Kh
      have hH0 : 0 ≤ H0 := (zero_le_one.trans hKh1).trans (le_max_right _ _)
      obtain ⟨Cv, hCv, hV⟩ := c10_variation_kernel_bounds p hp0 hp1 B Kf hB hKf1
      have hpair := (hV R hR ε hε hε1 H0 hH0 f h hfW hhW
        (fun y => (hfB y).trans (le_max_left _ _)) (fun y => (hBh0 y).trans (le_max_left _ _))
        (Eventually.of_forall fun x hx => hKf x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (Eventually.of_forall fun x hx => (hKh x ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans
          (le_max_right _ _))).1
      have hU : (Ioo (-R) R).Nonempty := ⟨0, by constructor <;> linarith⟩
      obtain ⟨-, hJi, -, hLL, hD⟩ := c10_aux_pair_integral (p + 1) hα hα2 (Ioo (-R) R) isOpen_Ioo
        ordConnected_Ioo hU (Cv * ε * H0) (by positivity) _ _ hpair
      refine ⟨hLL, ?_⟩
      filter_upwards [hJi, hD] with y h1 h2 hy using ⟨h1 hy, h2 hy⟩
    have hlin : c10_N3_linearization p ε fbar r h = fun y =>
        (∫ z, c10_N3_linearization_K p ε f h y z / |y - z| ^ (p + 1)) -
          b_eps p ε y * deriv h y := rfl
    refine ⟨?_, ?_⟩
    · rw [W1inftyLoc, hlin]
      exact (c10_aux_locLip_of_Ioo fun n => (per n).1).sub hbL
    · have hall := ae_all_iff.2 fun n => (per n).2
      filter_upwards [hall, c10_aux_ae_differentiableAt hbL] with y hy hbd
      obtain ⟨n, hn⟩ := exists_nat_gt |y|
      have hyI : y ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
        constructor <;> linarith [neg_abs_le y, le_abs_self y]
      obtain ⟨hi, hd⟩ := hy n hyI
      refine ⟨hi, ?_⟩
      rw [hlin]
      exact (hd.sub hbd.hasDerivAt).deriv

/-- Helper: `X_γ` is closed under linear combinations, with the triangle/homogeneity bound. -/
theorem c10_aux_X_lin (p γ : ℝ) {f g : ℝ → ℝ} (hf : f ∈ X_gamma p γ) (hg : g ∈ X_gamma p γ)
    (a b : ℝ) :
    a • f + b • g ∈ X_gamma p γ ∧
    X_gamma_norm p γ (a • f + b • g) ≤
      ENNReal.ofReal |a| * X_gamma_norm p γ f + ENNReal.ofReal |b| * X_gamma_norm p γ g := by
  have hd1 : Differentiable ℝ f := hf.1.1.differentiable (by norm_num)
  have hd2 : Differentiable ℝ g := hg.1.1.differentiable (by norm_num)
  have hD : deriv (a • f + b • g) = fun y => a * deriv f y + b * deriv g y := funext fun y => by
    rw [deriv_add ((hd1 y).const_smul a) ((hd2 y).const_smul b), deriv_const_smul a (hd1 y),
      deriv_const_smul b (hd2 y), smul_eq_mul, smul_eq_mul]
  have hDD : ∀ᵐ y, deriv (deriv (a • f + b • g)) y =
      a * deriv (deriv f) y + b * deriv (deriv g) y := by
    filter_upwards [c10_aux_ae_differentiableAt hf.1.2, c10_aux_ae_differentiableAt hg.1.2]
      with y a1 a2
    rw [hD]; exact ((a1.hasDerivAt.const_mul a).add (a2.hasDerivAt.const_mul b)).deriv
  have hloc : LocallyLipschitz (deriv (a • f + b • g)) := by
    rw [hD]
    exact (c10_aux_locLip_mul (LipschitzWith.const a).locallyLipschitz hf.1.2).add
      (c10_aux_locLip_mul (LipschitzWith.const b).locallyLipschitz hg.1.2)
  have hle : X_gamma_norm p γ (a • f + b • g) ≤
      ENNReal.ofReal |a| * X_gamma_norm p γ f + ENNReal.ofReal |b| * X_gamma_norm p γ g := by
    unfold X_gamma_norm
    have hj : ∀ y, 0 ≤ jb y ^ γ := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
    have key : ∀ (s : Set ℝ) (w₁ w₂ : ℝ → ℝ), (∀ y, 0 ≤ w₁ y) → (∀ y, 0 ≤ w₂ y) →
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖(a • f + b • g) y‖ +
            w₁ y * ‖deriv (a • f + b • g) y‖ + w₂ y * ‖deriv (deriv (a • f + b • g)) y‖)))
            (volume.restrict s) ≤
          ENNReal.ofReal |a| * essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖f y‖ +
            w₁ y * ‖deriv f y‖ + w₂ y * ‖deriv (deriv f) y‖))) (volume.restrict s) +
          ENNReal.ofReal |b| * essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖g y‖ +
            w₁ y * ‖deriv g y‖ + w₂ y * ‖deriv (deriv g) y‖))) (volume.restrict s) := by
      intro s w₁ w₂ hw₁ hw₂
      rw [← ENNReal.essSup_const_mul, ← ENNReal.essSup_const_mul]
      refine le_trans (essSup_mono_ae ?_) (ENNReal.essSup_add_le _ _)
      filter_upwards [ae_restrict_of_ae hDD] with y hy
      simp only [Pi.add_apply]
      rw [hy, hD]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
      have hJ := hj y; have h1 := hw₁ y; have h2 := hw₂ y
      set X := jb y ^ γ * (|f y| + w₁ y * |deriv f y| + w₂ y * |deriv (deriv f) y|)
      set Y := jb y ^ γ * (|g y| + w₁ y * |deriv g y| + w₂ y * |deriv (deriv g) y|)
      have hX : 0 ≤ X := by positivity
      have hY : 0 ≤ Y := by positivity
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have e1 : |a * f y + b * g y| ≤ |a| * |f y| + |b| * |g y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      have e2 : |a * deriv f y + b * deriv g y| ≤ |a| * |deriv f y| + |b| * |deriv g y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      have e3 : |a * deriv (deriv f) y + b * deriv (deriv g) y| ≤
          |a| * |deriv (deriv f) y| + |b| * |deriv (deriv g) y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      have : |a * f y + b * g y| + w₁ y * |a * deriv f y + b * deriv g y| +
          w₂ y * |a * deriv (deriv f) y + b * deriv (deriv g) y| ≤
          |a| * (|f y| + w₁ y * |deriv f y| + w₂ y * |deriv (deriv f) y|) +
          |b| * (|g y| + w₁ y * |deriv g y| + w₂ y * |deriv (deriv g) y|) := by
        have := mul_le_mul_of_nonneg_left e2 h1
        have := mul_le_mul_of_nonneg_left e3 h2
        nlinarith
      calc _ ≤ jb y ^ γ * (|a| * (|f y| + w₁ y * |deriv f y| + w₂ y * |deriv (deriv f) y|) +
            |b| * (|g y| + w₁ y * |deriv g y| + w₂ y * |deriv (deriv g) y|)) :=
            mul_le_mul_of_nonneg_left this hJ
        _ = |a| * X + |b| * Y := by simp only [X, Y]; ring
    have hw1 : ∀ y, 0 ≤ jb y ^ (-1 / p) := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
    have hw2 : ∀ y, 0 ≤ jb y ^ (-2 / p) := fun y => Real.rpow_nonneg (c10_aux_jb_pos y).le _
    have hw3 : ∀ y, 0 ≤ jb y := fun y => (c10_aux_jb_pos y).le
    have hw4 : ∀ y, 0 ≤ jb y ^ (2 : ℕ) := fun y => by positivity
    have k1 := key (Ici 0) _ _ hw1 hw2
    have k2 := key (Iic 0) _ _ hw3 hw4
    calc _ ≤ _ := add_le_add k1 k2
      _ = _ := by ring
  exact ⟨⟨⟨(hf.1.1.const_smul a).add (hg.1.1.const_smul b), hloc⟩,
    lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.2⟩)⟩, hle⟩

/-- Helper: an a.e.–a.e. bound on `a(y) + b(y')` bounds the sum of essential suprema. -/
theorem c10_aux_essSup_pair {μ ν : Measure ℝ} (hμ : μ ≠ 0) (hν : ν ≠ 0) {a b : ℝ → ℝ} {c : ℝ}
    (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y)
    (h : ∀ᵐ y ∂μ, ∀ᵐ y' ∂ν, a y + b y' ≤ c) :
    essSup (fun y => ENNReal.ofReal (a y)) μ + essSup (fun y => ENNReal.ofReal (b y)) ν ≤
      ENNReal.ofReal c := by
  haveI : (ae μ).NeBot := ae_neBot.2 hμ
  haveI : (ae ν).NeBot := ae_neBot.2 hν
  obtain ⟨y0, hy0⟩ := h.exists
  set Sb := essSup (fun y => ENNReal.ofReal (b y)) ν
  have hSb : Sb ≤ ENNReal.ofReal c := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hy0] with y' hy'
    exact ENNReal.ofReal_le_ofReal (by linarith [ha y0])
  have hSbt : Sb ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSb
  have hSa : essSup (fun y => ENNReal.ofReal (a y)) μ ≤ ENNReal.ofReal c - Sb := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [h] with y hy
    obtain ⟨y1, hy1⟩ := hy.exists
    have hac : a y ≤ c := by linarith [hb y1]
    have hS : Sb ≤ ENNReal.ofReal (c - a y) := by
      refine essSup_le_of_ae_le _ ?_
      filter_upwards [hy] with y' hy'
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine ENNReal.le_sub_of_add_le_right hSbt ?_
    calc ENNReal.ofReal (a y) + Sb ≤ ENNReal.ofReal (a y) + ENNReal.ofReal (c - a y) :=
          add_le_add le_rfl hS
      _ = ENNReal.ofReal c := by
          rw [← ENNReal.ofReal_add (ha y) (by linarith)]; ring_nf
  calc _ ≤ (ENNReal.ofReal c - Sb) + Sb := add_le_add hSa le_rfl
    _ = ENNReal.ofReal c := tsub_add_cancel_of_le hSb

/-- Helper: the difference-quotient `limsup` recovers the derivative. -/
theorem c10_aux_limsup_deriv {φ : ℝ → ℝ} {d y : ℝ} (h : HasDerivAt φ d y) :
    limsup (fun n : ℕ => ((n : ℝ) + 1) * (φ (y + 1 / ((n : ℝ) + 1)) - φ y)) atTop = d := by
  have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  have := h.tendsto_slope_zero_right.comp hs
  have e : (fun n : ℕ => ((n : ℝ) + 1) * (φ (y + 1 / ((n : ℝ) + 1)) - φ y)) =
      (fun t => t⁻¹ • (φ (y + t) - φ y)) ∘ fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n; simp [smul_eq_mul]
  rw [e]; exact this.limsup_eq

/-- Helper: per-slice null sets of a measurable set in `ℝ × β` are jointly null; hence, after
exchanging the order, a.e. in the second variable the property holds a.e. in the first. -/
theorem c10_aux_slices {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
    {P : ℝ → β → Prop} (hP : MeasurableSet {q : ℝ × β | P q.1 q.2})
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ x ∂ν, P t x) :
    ∀ᵐ x ∂ν, ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → P t x := by
  have hm : MeasurableSet {q : ℝ × β | q.1 ∈ Icc (0 : ℝ) 1 → P q.1 q.2} :=
    (measurableSet_Icc.preimage measurable_fst).compl.union hP |>.congr (by
      ext q; simp only [mem_union, mem_compl_iff, mem_preimage, mem_setOf_eq]; tauto)
  have hall : ∀ᵐ t, ∀ᵐ x ∂ν, t ∈ Icc (0 : ℝ) 1 → P t x := Eventually.of_forall fun t => by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · filter_upwards [h t ht] with x hx _ using hx
    · exact Eventually.of_forall fun x h' => absurd h' ht
  exact (Measure.ae_ae_comm (μ := volume) (ν := ν) hm).1 hall

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_N3_mean_value.  If `‖D𝒩₃(r)[h]‖_{Y_γ} ≤ A ‖h‖_{X_γ}` for all `‖r‖ ≤ N`,
`h ∈ X_γ`, then `‖𝒩₃(r₁) - 𝒩₃(r₂)‖_{Y_γ} ≤ A ‖r₁ - r₂‖_{X_γ}` for `‖r_j‖ ≤ N`.
(Norms in `[0,∞]`, so the hypothesis includes `D𝒩₃(r)[h] ∈ Y_γ`-finiteness.) -/
-- Proof: the sum of the two half-line norms is integrated in the path parameter before it is
-- bounded by `A * ‖h‖` (bounding two separate parameter suprema would lose a factor of two).
theorem c10_N3_mean_value (p γ M ε N A : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hN : 0 < N) (hA : 0 ≤ A)
    (fbar : ℝ → ℝ) (hfbar : nonlinear_admissible_profile p M fbar)
    (hD : ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      Y_gamma_norm p γ (c10_N3_linearization p ε fbar r h) ≤ ENNReal.ofReal (A * xNorm p γ h))
    (r₁ r₂ : ℝ → ℝ) (hr₁ : r₁ ∈ X_gamma p γ) (hr₂ : r₂ ∈ X_gamma p γ)
    (hr₁N : xNorm p γ r₁ ≤ N) (hr₂N : xNorm p γ r₂ ≤ N) :
    Y_gamma_norm p γ (fun y => c10_N_pieces_N3 p ε fbar r₁ y - c10_N_pieces_N3 p ε fbar r₂ y) ≤
      ENNReal.ofReal (A * xNorm p γ (r₁ - r₂)) := by
  obtain ⟨hp0, hγp, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  set h := r₁ - r₂ with hhdef
  have hhX : h ∈ X_gamma p γ := c10_aux_X_sub p γ hr₁ hr₂
  set xh := xNorm p γ h
  have hxh : 0 ≤ xh := ENNReal.toReal_nonneg
  set K := A * xh
  have hK : 0 ≤ K := mul_nonneg hA hxh
  -- the segment
  set ρ : ℝ → ℝ → ℝ := fun t => r₂ + t • h with hρdef
  have hρX : ∀ t, ρ t ∈ X_gamma p γ := fun t => by
    have := (c10_aux_X_lin p γ hr₂ hhX 1 t).1; rwa [one_smul] at this
  have hρN : ∀ t ∈ Icc (0 : ℝ) 1, xNorm p γ (ρ t) ≤ N := by
    intro t ht
    have e : ρ t = (1 - t) • r₂ + t • r₁ := by
      funext y; simp only [hρdef, hhdef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    have hb := (c10_aux_X_lin p γ hr₂ hr₁ (1 - t) t).2
    rw [← e] at hb
    unfold xNorm
    have h1 : |1 - t| = 1 - t := abs_of_nonneg (by linarith [ht.2])
    have h2 : |t| = t := abs_of_nonneg ht.1
    rw [h1, h2] at hb
    have hfin : ENNReal.ofReal (1 - t) * X_gamma_norm p γ r₂ + ENNReal.ofReal t * X_gamma_norm p γ r₁ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr₂.2.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr₁.2.ne⟩
    refine (ENNReal.toReal_mono hfin hb).trans ?_
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr₂.2.ne)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hr₁.2.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith [ht.2]), ENNReal.toReal_ofReal ht.1]
    have a1 := mul_le_mul_of_nonneg_left (show (X_gamma_norm p γ r₂).toReal ≤ N from hr₂N)
      (show 0 ≤ 1 - t by linarith [ht.2])
    have a2 := mul_le_mul_of_nonneg_left (show (X_gamma_norm p γ r₁).toReal ≤ N from hr₁N) ht.1
    nlinarith
  -- the path of linearizations (kept opaque to avoid expensive unfolding)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ → ℝ,
      Φ = fun t y => c10_N3_linearization p ε fbar (ρ t) h y := ⟨_, rfl⟩
  have NV0 := c10_N3_variation p γ M ε hp hp1 hγ hM hε hε1 fbar hfbar r₂ hr₂ h hhX
  have NVt := fun t => c10_N3_variation p γ M ε hp hp1 hγ hM hε hε1 fbar hfbar (ρ t) (hρX t) h hhX
  have hΦt : ∀ y, Continuous (fun t => Φ t y) := by
    intro y
    obtain ⟨hC, hHD⟩ := NV0.2.1 y
    have hd : deriv (fun t : ℝ => c10_N_pieces_N3 p ε fbar (r₂ + t • h) y) = fun t => Φ t y :=
      funext fun t => by rw [(hHD t).deriv, hΦdef]
    rw [← hd]; exact hC.continuous_deriv le_rfl
  have hΦloc : ∀ t, LocallyLipschitz (Φ t) := fun t => by rw [hΦdef]; exact (NVt t).2.2.1
  have hΦm : Measurable (Function.uncurry Φ) :=
    measurable_uncurry_of_continuous_of_measurable hΦt fun t => (hΦloc t).continuous.measurable
  -- the joint derivative representative
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ → ℝ → ℝ, D = fun t y =>
      limsup (fun n : ℕ => ((n : ℝ) + 1) * (Φ t (y + 1 / ((n : ℝ) + 1)) - Φ t y)) atTop := ⟨_, rfl⟩
  have hDm : Measurable (Function.uncurry D) := by
    rw [hDdef]
    refine Measurable.limsup fun n => ?_
    have h1 : Measurable (fun q : ℝ × ℝ => Φ q.1 (q.2 + 1 / ((n : ℝ) + 1))) :=
      hΦm.comp (measurable_fst.prodMk (measurable_snd.add_const _))
    have h2 : Measurable (fun q : ℝ × ℝ => Φ q.1 q.2) := hΦm
    exact measurable_const.mul (h1.sub h2)
  have hDder : ∀ t, ∀ᵐ y, HasDerivAt (Φ t) (D t y) y := fun t => by
    filter_upwards [c10_aux_ae_differentiableAt (hΦloc t)] with y hy
    have := c10_aux_limsup_deriv hy.hasDerivAt
    rw [hDdef]; simp only; rw [this]; exact hy.hasDerivAt
  -- quantities controlled by the hypothesis
  obtain ⟨qp, hqp⟩ : ∃ qp : ℝ → ℝ → ℝ, qp = fun t y =>
      jb y ^ γ * (|Φ t y| + jb y ^ (-1 / p) * |D t y|) := ⟨_, rfl⟩
  obtain ⟨qm, hqm⟩ : ∃ qm : ℝ → ℝ → ℝ, qm = fun t y =>
      jb y ^ γ * (|Φ t y| + jb y * |D t y|) := ⟨_, rfl⟩
  have hjb : ∀ y, 0 < jb y := c10_aux_jb_pos
  have hqp0 : ∀ t y, 0 ≤ qp t y := fun t y => by
    rw [hqp]; have := hjb y; positivity
  have hqm0 : ∀ t y, 0 ≤ qm t y := fun t y => by
    rw [hqm]; have := hjb y; positivity
  have hYt : ∀ t ∈ Icc (0 : ℝ) 1, ∃ e1 e2 : ℝ, e1 + e2 ≤ K ∧
      (∀ᵐ y ∂(volume.restrict (Ici 0)), qp t y ≤ e1) ∧
      (∀ᵐ y ∂(volume.restrict (Iic 0)), qm t y ≤ e2) := by
    intro t ht
    have hY : Y_gamma_norm p γ (Φ t) ≤ ENNReal.ofReal K := by
      rw [hΦdef]; exact hD (ρ t) (hρX t) (hρN t ht) h hhX
    unfold Y_gamma_norm at hY
    set E1 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖Φ t y‖ + jb y ^ (-1 / p) *
      ‖deriv (Φ t) y‖))) (volume.restrict (Ici 0))
    set E2 := essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖Φ t y‖ + jb y * ‖deriv (Φ t) y‖)))
      (volume.restrict (Iic 0))
    have hE : E1 + E2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY
    have hE1 : E1 ≠ ⊤ := fun h0 => hE (by rw [h0, top_add])
    have hE2 : E2 ≠ ⊤ := fun h0 => hE (by rw [h0, add_top])
    refine ⟨E1.toReal, E2.toReal, ?_, ?_, ?_⟩
    · rw [← ENNReal.toReal_add hE1 hE2]
      exact (ENNReal.toReal_le_toReal hE ENNReal.ofReal_ne_top).2 hY |>.trans
        (by rw [ENNReal.toReal_ofReal hK])
    · filter_upwards [ae_le_essSup (f := fun y => ENNReal.ofReal (jb y ^ γ * (‖Φ t y‖ +
        jb y ^ (-1 / p) * ‖deriv (Φ t) y‖))) (μ := volume.restrict (Ici 0)),
        ae_restrict_of_ae (hDder t)] with y hy hd
      rw [hd.deriv, ENNReal.ofReal_le_iff_le_toReal hE1] at hy
      rw [hqp]; simpa only [Real.norm_eq_abs] using hy
    · filter_upwards [ae_le_essSup (f := fun y => ENNReal.ofReal (jb y ^ γ * (‖Φ t y‖ +
        jb y * ‖deriv (Φ t) y‖))) (μ := volume.restrict (Iic 0)),
        ae_restrict_of_ae (hDder t)] with y hy hd
      rw [hd.deriv, ENNReal.ofReal_le_iff_le_toReal hE2] at hy
      rw [hqm]; simpa only [Real.norm_eq_abs] using hy
  -- pointwise a.e. bound for `D`
  have hDK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ y, |D t y| ≤ K := by
    intro t ht
    obtain ⟨e1, e2, he, h1, h2⟩ := hYt t ht
    have he1 : e1 ≤ K := by
      have : 0 ≤ e2 := by
        haveI : (ae (volume.restrict (Iic (0 : ℝ)))).NeBot := ae_neBot.2 (by
          rw [Ne, Measure.restrict_eq_zero, Real.volume_Iic]; exact ENNReal.top_ne_zero)
        obtain ⟨y, hy⟩ := h2.exists; exact (hqm0 t y).trans hy
      linarith
    have he2 : e2 ≤ K := by
      have : 0 ≤ e1 := by
        haveI : (ae (volume.restrict (Ici (0 : ℝ)))).NeBot := ae_neBot.2 (by
          rw [Ne, Measure.restrict_eq_zero, Real.volume_Ici]; exact ENNReal.top_ne_zero)
        obtain ⟨y, hy⟩ := h1.exists; exact (hqp0 t y).trans hy
      linarith
    rw [ae_restrict_iff' measurableSet_Ici] at h1
    rw [ae_restrict_iff' measurableSet_Iic] at h2
    filter_upwards [h1, h2] with y hy1 hy2
    rcases le_total 0 y with hy | hy
    · have := hy1 hy
      rw [hqp] at this; simp only at this
      have hw : 1 ≤ jb y ^ γ * jb y ^ (-1 / p) := by
        rw [← Real.rpow_add (hjb y)]
        exact Real.one_le_rpow (c10_aux_one_le_jb y) (by
          have : 1 / p < γ := hγp
          rw [neg_div]; linarith [show 1 / p = 1 / p from rfl])
      have hj := Real.rpow_nonneg (hjb y).le γ
      have hΦ0 := abs_nonneg (Φ t y)
      have hD0 := abs_nonneg (D t y)
      nlinarith [mul_nonneg hj hΦ0]
    · have := hy2 hy
      rw [hqm] at this; simp only at this
      have hw : 1 ≤ jb y ^ γ * jb y := by
        have := Real.one_le_rpow (c10_aux_one_le_jb y) (by linarith : (0 : ℝ) ≤ γ)
        nlinarith [c10_aux_one_le_jb y]
      have hj := Real.rpow_nonneg (hjb y).le γ
      have hΦ0 := abs_nonneg (Φ t y)
      have hD0 := abs_nonneg (D t y)
      nlinarith [mul_nonneg hj hΦ0]
  have hDKm : MeasurableSet {q : ℝ × ℝ | |D q.1 q.2| ≤ K} :=
    measurableSet_le hDm.abs measurable_const
  have hslD := c10_aux_slices (ν := volume) (P := fun t y => |D t y| ≤ K) hDKm hDK
  -- `G` and its representation
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun y =>
      c10_N_pieces_N3 p ε fbar r₁ y - c10_N_pieces_N3 p ε fbar r₂ y := ⟨_, rfl⟩
  have hGrep : ∀ y, G y = ∫ t in (0 : ℝ)..1, Φ t y := by
    intro y
    obtain ⟨-, hHD⟩ := NV0.2.1 y
    have e1 : r₂ + (1 : ℝ) • h = r₁ := by
      funext x; simp only [hhdef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have e0 : r₂ + (0 : ℝ) • h = r₂ := by rw [zero_smul, add_zero]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ =>
      c10_N_pieces_N3 p ε fbar (r₂ + t • h) y) (fun t _ => by rw [hΦdef]; exact hHD t)
      ((hΦt y).intervalIntegrable _ _), hGdef]
    simp only [e1, e0]
  -- `Ψ`
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun y => ∫ t in (0 : ℝ)..1, D t y := ⟨_, rfl⟩
  have hΨm : Measurable Ψ := by
    have : Ψ = fun y => ∫ t, (Function.uncurry D ∘ Prod.swap) (y, t) ∂(volume.restrict (Ioc 0 1)) := by
      rw [hΨdef]; funext y; rw [intervalIntegral.integral_of_le zero_le_one]; rfl
    rw [this]
    exact ((hDm.comp measurable_swap).stronglyMeasurable.integral_prod_right').measurable
  have hΨK : ∀ᵐ y, |Ψ y| ≤ K := by
    filter_upwards [hslD] with y hy
    rw [hΨdef]
    have := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := 0) (b := 1) (C := K)
      (f := fun t => D t y) (by
        filter_upwards [hy] with t ht ht'
        rw [Real.norm_eq_abs]; refine ht ?_
        rw [uIoc_of_le zero_le_one] at ht'; exact Ioc_subset_Icc_self ht')
    simpa using this
  -- the increment identity (Fubini)
  have hinc : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ univ → G b - G a = ∫ y in a..b, Ψ y := by
    intro a b hab _
    rw [hGrep, hGrep, ← intervalIntegral.integral_sub ((hΦt b).intervalIntegrable _ _)
      ((hΦt a).intervalIntegrable _ _)]
    have hstep : ∀ t, Φ t b - Φ t a = ∫ y in a..b, D t y := fun t =>
      c10_aux_ftc_locLip isOpen_univ (hΦloc t).locallyLipschitzOn
        (by filter_upwards [hDder t] with y hy _ using hy) hab (subset_univ _)
    simp_rw [hstep]
    rw [hΨdef]
    simp only
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hab]
    simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le zero_le_one]
    have hint : Integrable (Function.uncurry D)
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc a b))) := by
      refine Integrable.of_bound hDm.aestronglyMeasurable K ?_
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hDm.norm measurable_const)]
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        filter_upwards [ae_restrict_of_ae (hDK t (Ioc_subset_Icc_self ht))] with y hy
        simpa [Real.norm_eq_abs] using hy
    exact integral_integral_swap hint
  obtain ⟨hGloc, hGder⟩ := c10_aux_primitive isOpen_univ hΨm (C := K)
    (by filter_upwards [hΨK] with y hy _ using hy) hinc
  -- joint measurability of the controlled quantities
  have hjm : Measurable jb := c10_aux_jb_continuous.measurable
  have hΦm' : Measurable (fun q : ℝ × ℝ => Φ q.1 q.2) := hΦm
  have hDm' : Measurable (fun q : ℝ × ℝ => D q.1 q.2) := hDm
  have hqpm : Measurable (fun q : ℝ × ℝ => qp q.1 q.2) := by
    rw [hqp]
    exact ((hjm.comp measurable_snd).pow_const γ).mul (hΦm'.abs.add
      (((hjm.comp measurable_snd).pow_const _).mul hDm'.abs))
  have hqmm : Measurable (fun q : ℝ × ℝ => qm q.1 q.2) := by
    rw [hqm]
    exact ((hjm.comp measurable_snd).pow_const γ).mul (hΦm'.abs.add
      ((hjm.comp measurable_snd).mul hDm'.abs))
  set μp := volume.restrict (Ici (0 : ℝ))
  set μm := volume.restrict (Iic (0 : ℝ))
  have hpairm : MeasurableSet {q : ℝ × (ℝ × ℝ) | qp q.1 q.2.1 + qm q.1 q.2.2 ≤ K} := by
    refine measurableSet_le ?_ measurable_const
    exact (hqpm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
      (hqmm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hper : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ q ∂(μp.prod μm), qp t q.1 + qm t q.2 ≤ K := by
    intro t ht
    obtain ⟨e1, e2, he, h1, h2⟩ := hYt t ht
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
      Measure.quasiMeasurePreserving_snd.ae h2] with q hq1 hq2
    linarith
  have hsl2 := c10_aux_slices (ν := μp.prod μm) (P := fun t q => qp t q.1 + qm t q.2 ≤ K)
    hpairm hper
  have hsl2' := Measure.ae_ae_of_ae_prod hsl2
  -- interval integrability of the slices
  have hDi : ∀ y, (∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → |D t y| ≤ K) →
      IntervalIntegrable (fun t => D t y) volume 0 1 := by
    intro y hy
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    refine Integrable.of_bound (hDm'.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      K ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hy] with t ht htI
    rw [Real.norm_eq_abs]; exact ht htI
  -- the pointwise estimate along the path
  have hpt : ∀ y, (∀ᵐ t, t ∈ Icc (0 : ℝ) 1 → |D t y| ≤ K) → HasDerivAt G (Ψ y) y →
      ∀ (w : ℝ), 0 ≤ w →
      jb y ^ γ * (|G y| + w * |deriv G y|) ≤
        ∫ t in (0 : ℝ)..1, jb y ^ γ * (|Φ t y| + w * |D t y|) := by
    intro y hy hGy w hw
    rw [hGy.deriv, hGrep y, hΨdef]
    have i1 : IntervalIntegrable (fun t => |Φ t y|) volume 0 1 :=
      (hΦt y).abs.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => |D t y|) volume 0 1 := (hDi y hy).abs
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 (i2.const_mul w),
      intervalIntegral.integral_const_mul]
    have hj := Real.rpow_nonneg (hjb y).le γ
    apply mul_le_mul_of_nonneg_left _ hj
    exact add_le_add (intervalIntegral.abs_integral_le_integral_abs zero_le_one)
      (mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs zero_le_one) hw)
  -- conclusion
  have hgoal : (fun y => c10_N_pieces_N3 p ε fbar r₁ y - c10_N_pieces_N3 p ε fbar r₂ y) = G :=
    hGdef.symm
  rw [hgoal]
  unfold Y_gamma_norm
  simp only [Real.norm_eq_abs]
  have hμp : μp ≠ 0 := by
    simp only [μp]; rw [Ne, Measure.restrict_eq_zero, Real.volume_Ici]; exact ENNReal.top_ne_zero
  have hμm : μm ≠ 0 := by
    simp only [μm]; rw [Ne, Measure.restrict_eq_zero, Real.volume_Iic]; exact ENNReal.top_ne_zero
  refine c10_aux_essSup_pair hμp hμm (fun y => by have := hjb y; positivity)
    (fun y => by have := hjb y; positivity) ?_
  filter_upwards [hsl2', ae_restrict_of_ae hGder, ae_restrict_of_ae hslD] with y hy hGy hDy
  filter_upwards [hy, ae_restrict_of_ae hGder, ae_restrict_of_ae hslD] with y' hy' hGy' hDy'
  have a1 := hpt y hDy (hGy (mem_univ y)) (jb y ^ (-1 / p)) (Real.rpow_nonneg (hjb y).le _)
  have a2 := hpt y' hDy' (hGy' (mem_univ y')) (jb y') (hjb y').le
  have i1 : IntervalIntegrable (fun t => jb y ^ γ * (|Φ t y| + jb y ^ (-1 / p) * |D t y|))
      volume 0 1 :=
    (((hΦt y).abs.intervalIntegrable _ _).add ((hDi y hDy).abs.const_mul _)).const_mul _
  have i2 : IntervalIntegrable (fun t => jb y' ^ γ * (|Φ t y'| + jb y' * |D t y'|)) volume 0 1 :=
    (((hΦt y').abs.intervalIntegrable _ _).add ((hDi y' hDy').abs.const_mul _)).const_mul _
  have hle : (∫ t in (0 : ℝ)..1, jb y ^ γ * (|Φ t y| + jb y ^ (-1 / p) * |D t y|)) +
      (∫ t in (0 : ℝ)..1, jb y' ^ γ * (|Φ t y'| + jb y' * |D t y'|)) ≤ K := by
    rw [← intervalIntegral.integral_add i1 i2]
    have := intervalIntegral.integral_mono_ae_restrict (a := 0) (b := 1) (μ := volume)
      (f := fun t => jb y ^ γ * (|Φ t y| + jb y ^ (-1 / p) * |D t y|) +
        jb y' ^ γ * (|Φ t y'| + jb y' * |D t y'|)) (g := fun _ => K) zero_le_one (i1.add i2)
      intervalIntegrable_const (by
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hy'] with t ht htI
        have := ht htI
        rw [hqp, hqm] at this
        exact this)
    simpa using this
  linarith

/-! ### Near field: `|y| ≥ 2`, `|y-z| ≤ |y|/2` -/

/-- Helper: geometry of the near region. -/
theorem c10_aux_near_geom {y z : ℝ} (hy : 2 ≤ |y|) (hz : |y - z| ≤ |y| / 2) :
    0 < y * z ∧ ∀ w ∈ uIcc y z, |y| / 2 ≤ |w| ∧ jb y / 2 ≤ jb w ∧ jb w ≤ 2 * jb y := by
  have hy0 : 0 < |y| := by linarith
  refine ⟨?_, fun w hw => ?_⟩
  · rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h] at hy hz
      have := (abs_le.1 hz); nlinarith
    · rw [abs_of_neg h] at hy hz
      have := (abs_le.1 hz); nlinarith
  · have hwy : |w - y| ≤ |y - z| := by
      rw [abs_sub_comm y z]; exact abs_sub_left_of_mem_uIcc hw
    have h1 : |y| / 2 ≤ |w| := by
      have := abs_sub_abs_le_abs_sub y w; rw [abs_sub_comm] at this; linarith
    have h2 : |w| ≤ 3 * |y| / 2 := by
      have := abs_sub_abs_le_abs_sub w y; linarith
    have sw : y ^ 2 / 4 ≤ w ^ 2 := by
      have := mul_le_mul h1 h1 (by positivity) (abs_nonneg _)
      rw [← sq_abs w]; nlinarith [sq_abs y]
    have sw2 : w ^ 2 ≤ 4 * y ^ 2 := by
      have := mul_le_mul h2 h2 (abs_nonneg _) (by positivity)
      rw [← sq_abs w, ← sq_abs y]; nlinarith
    refine ⟨h1, ?_, ?_⟩
    · unfold jb
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), ← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2),
        ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    · unfold jb
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2), ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by nlinarith)

/-- Helper: comparison `⟨w⟩^e ≤ 32 ⟨y⟩^e` when `⟨y⟩/2 ≤ ⟨w⟩ ≤ 2⟨y⟩` and `|e| ≤ 5`. -/
theorem c10_aux_jb_compare {y w e : ℝ} (h1 : jb y / 2 ≤ jb w) (h2 : jb w ≤ 2 * jb y)
    (he : |e| ≤ 5) : jb w ^ e ≤ 32 * jb y ^ e := by
  have hy := c10_aux_jb_pos y
  have hw := c10_aux_jb_pos w
  have h32 : (2 : ℝ) ^ |e| ≤ 32 := by
    calc (2 : ℝ) ^ |e| ≤ 2 ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
      _ = 32 := by norm_num
  rcases le_or_gt 0 e with h | h
  · calc jb w ^ e ≤ (2 * jb y) ^ e := Real.rpow_le_rpow hw.le h2 h
      _ = 2 ^ e * jb y ^ e := Real.mul_rpow (by norm_num) hy.le
      _ ≤ 32 * jb y ^ e := by
          rw [abs_of_nonneg h] at h32
          exact mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg hy.le _)
  · calc jb w ^ e ≤ (jb y / 2) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) h1 h.le
      _ = 2 ^ (-e) * jb y ^ e := by
          rw [Real.div_rpow hy.le (by norm_num), Real.rpow_neg (by norm_num)]; field_simp
      _ ≤ 32 * jb y ^ e := by
          rw [abs_of_neg h] at h32
          exact mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg hy.le _)

/-- Blueprint: lem:c10_near_increments.  Increment bounds for `f = f̄ + r` and `h` in the near
region, with `m(y,z) = min{1, ⟨y⟩^{1/p}|y-z|}` (second-derivative statements for a.e. `y`). -/
theorem c10_near_increments (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      -- geometry of the near region
      (∀ y z : ℝ, 2 ≤ |y| → |y - z| ≤ |y| / 2 →
        0 < y * z ∧ ∀ w ∈ uIcc y z, jb y / 2 ≤ jb w ∧ jb w ≤ 2 * jb y) ∧
      -- `y ≥ 2`, values
      (∀ y z : ℝ, 2 ≤ y → |y - z| ≤ |y| / 2 →
        |deriv (fbar + r) y| + |c01_secant (fbar + r) y z| ≤ C * jb y ^ (-beta p) ∧
        |deriv (fbar + r) y - c01_secant (fbar + r) y z| ≤
          C * jb y ^ (-beta p) * min 1 (jb y ^ (1 / p) * |y - z|) ∧
        |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ + 1 / p) ∧
        |deriv h y - c01_secant h y z| ≤
          C * xNorm p γ h * jb y ^ (-γ + 1 / p) * min 1 (jb y ^ (1 / p) * |y - z|)) ∧
      -- `y ≥ 2`, second derivatives (a.e. `y`)
      (∀ᵐ y, ∀ z : ℝ, 2 ≤ y → |y - z| ≤ |y| / 2 → z ≠ y →
        |deriv (deriv (fbar + r)) y| + |deriv (fun y' => c01_secant (fbar + r) y' z) y| ≤
          C * jb y ^ (-beta p + 1 / p) ∧
        |deriv (deriv h) y| + |deriv (fun y' => c01_secant h y' z) y| ≤
          C * xNorm p γ h * jb y ^ (-γ + 2 / p)) ∧
      -- `y ≤ -2`, values
      (∀ y z : ℝ, y ≤ -2 → |y - z| ≤ |y| / 2 →
        |deriv (fbar + r) y| + |c01_secant (fbar + r) y z| ≤ C ∧
        |deriv (fbar + r) y - c01_secant (fbar + r) y z| ≤ C * jb y ^ (-p - 2) * |y - z| ∧
        |deriv h y| ≤ xNorm p γ h * jb y ^ (-γ - 1) ∧
        |deriv h y - c01_secant h y z| ≤ C * xNorm p γ h * jb y ^ (-γ - 2) * |y - z|) ∧
      -- `y ≤ -2`, second derivatives (a.e. `y`)
      (∀ᵐ y, ∀ z : ℝ, y ≤ -2 → |y - z| ≤ |y| / 2 → z ≠ y →
        |deriv (deriv (fbar + r)) y| + |deriv (fun y' => c01_secant (fbar + r) y' z) y| ≤
          C * jb y ^ (-p - 2) ∧
        |deriv (deriv h) y| + |deriv (fun y' => c01_secant h y' z) y| ≤
          C * xNorm p γ h * jb y ^ (-γ - 2)) := by
  obtain ⟨hp0, -, hγ1, -, hγ2⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨CP, hCP, hPC⟩ := c10_profile_consequences p γ M N hp hp1 hγ hM hN
  have hβ1 : 1 < beta p := by unfold beta; rw [lt_div_iff₀ (by linarith)]; linarith
  have hβ2 : beta p ≤ 2 := by unfold beta; rw [div_le_iff₀ (by linarith)]; linarith
  have hip : 1 / p < 2 := by rw [div_lt_iff₀ hp0]; linarith
  have hβp : -beta p + 1 / p ≤ 1 := by
    have : 2 * beta p = 1 + 1 / p := c10_aux_two_beta p hp0
    linarith
  have hγb := hγ.1
  have hip0 : 0 < 1 / p := by positivity
  have h2p : 2 / p = 2 * (1 / p) := by ring
  refine ⟨33 * CP + 33, by positivity, fun fbar hf r hr hrN h hh => ?_⟩
  obtain ⟨P1, P2a, P2b, P3a, P3b, -, -⟩ := hPC fbar hf r hr hrN
  obtain ⟨u0, -, -, -⟩ := P1 (fbar + r) (by simp)
  obtain ⟨s0, s1, s2, s3, s4⟩ := c10_aux_X_simple p γ hh
  set xh := xNorm p γ h
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  have hjpos := c10_aux_jb_pos
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e => (Real.rpow_pos_of_pos (hjpos y) e).le
  -- `f = f̄ + r ∈ W^{2,∞}_loc`
  have hfA := c10_aux_C2_admissible_class hf.1
    (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have hdf : Differentiable ℝ fbar := hf.1.differentiable (by norm_num)
  have hdr : Differentiable ℝ r := hr.1.1.differentiable (by norm_num)
  have hW : W2inftyLoc (fbar + r) := by
    refine ⟨hfA.1.add hr.1.1, ?_⟩
    have : deriv (fbar + r) = deriv fbar + deriv r := funext fun x => deriv_add (hdf x) (hdr x)
    rw [this]; exact hfA.2.2.add hr.1.2
  have hdW : Differentiable ℝ (fbar + r) := hW.1.differentiable (by norm_num)
  have hdh : Differentiable ℝ h := hh.1.1.differentiable (by norm_num)
  have hC1 : CP ≤ 33 * CP + 33 := by linarith
  have hC2 : (33 : ℝ) ≤ 33 * CP + 33 := by linarith
  -- a generic "min" combination
  have hmin : ∀ {X A t : ℝ}, 0 ≤ A → X ≤ A → X ≤ A * t → X ≤ A * min 1 t := by
    intro X A t hA h1 h2
    rcases le_total 1 t with ht | ht
    · rw [min_eq_left ht, mul_one]; exact h1
    · rw [min_eq_right ht]; exact h2
  -- geometry helpers for the sign of `w ∈ [y,z]`
  have wsign : ∀ y z : ℝ, 2 ≤ |y| → |y - z| ≤ |y| / 2 → ∀ w ∈ uIcc y z,
      (0 ≤ y → 0 ≤ w) ∧ (y ≤ 0 → w ≤ 0) := by
    intro y z hy hz w hw
    obtain ⟨hyz, geo⟩ := c10_aux_near_geom hy hz
    constructor
    · intro hy0
      have hy0' : 0 < y := by
        rcases eq_or_lt_of_le hy0 with h | h
        · rw [← h] at hyz; simp at hyz
        · exact h
      have hz0 : 0 < z := by nlinarith
      rcases le_total y z with hle | hle
      · rw [uIcc_of_le hle] at hw; linarith [hw.1]
      · rw [uIcc_of_ge hle] at hw; linarith [hw.1]
    · intro hy0
      have hy0' : y < 0 := by
        rcases eq_or_lt_of_le hy0 with h | h
        · rw [h] at hyz; simp at hyz
        · exact h
      have hz0 : z < 0 := by nlinarith
      rcases le_total y z with hle | hle
      · rw [uIcc_of_le hle] at hw; linarith [hw.2]
      · rw [uIcc_of_ge hle] at hw; linarith [hw.2]
  -- the a.e. second-derivative bounds on `[y,z]`
  have Lgen : ∀ (g : ℝ → ℝ) (K e : ℝ), 0 ≤ K → |e| ≤ 5 → ∀ (S : Set ℝ),
      (∀ᵐ w, w ∈ S → |deriv (deriv g) w| ≤ K * jb w ^ e) →
      ∀ y z : ℝ, 2 ≤ |y| → |y - z| ≤ |y| / 2 → (∀ w ∈ uIcc y z, w ∈ S) →
      ∀ᵐ w, w ∈ uIcc y z → |deriv (deriv g) w| ≤ 32 * K * jb y ^ e := by
    intro g K e hK he S hS y z hy hz hsub
    obtain ⟨-, geo⟩ := c10_aux_near_geom hy hz
    filter_upwards [hS] with w hw hwI
    refine (hw (hsub w hwI)).trans ?_
    rw [mul_assoc, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (c10_aux_jb_compare (geo w hwI).2.1 (geo w hwI).2.2 he) hK
  have P2b' : ∀ᵐ w, w ∈ Ici (0 : ℝ) → |deriv (deriv (fbar + r)) w| ≤
      CP * jb w ^ (-beta p + 1 / p) := by
    filter_upwards [P2b] with w hw hw' using hw hw'
  have P3b' : ∀ᵐ w, w ∈ Iic (0 : ℝ) → |deriv (deriv (fbar + r)) w| ≤ CP * jb w ^ (-p - 2) := by
    filter_upwards [P3b] with w hw hw' using hw hw'
  have s3' : ∀ᵐ w, w ∈ Ici (0 : ℝ) → |deriv (deriv h) w| ≤ xh * jb w ^ (-γ + 2 / p) := by
    filter_upwards [s3] with w hw hw' using hw hw'
  have s4' : ∀ᵐ w, w ∈ Iic (0 : ℝ) → |deriv (deriv h) w| ≤ xh * jb w ^ (-γ - 2) := by
    filter_upwards [s4] with w hw hw' using hw hw'
  have eb1 : |-beta p + 1 / p| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have eb2 : |-γ + 2 / p| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have eb3 : |-p - 2| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have eb4 : |-γ - 2| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  refine ⟨fun y z hy hz => ⟨(c10_aux_near_geom hy hz).1,
      fun w hw => ((c10_aux_near_geom hy hz).2 w hw).2⟩, ?_, ?_, ?_, ?_⟩
  · -- `y ≥ 2`, values
    intro y z hy hz
    have hy' : 2 ≤ |y| := by rwa [abs_of_nonneg (by linarith)]
    obtain ⟨-, geo⟩ := c10_aux_near_geom hy' hz
    have wpos : ∀ w ∈ uIcc y z, 0 ≤ w := fun w hw => by
      have := (geo w hw).1
      have hyz : 0 < y * z := (c10_aux_near_geom hy' hz).1
      have hz0 : 0 < z := by nlinarith
      rcases le_total y z with hle | hle
      · rw [uIcc_of_le hle] at hw; linarith [hw.1]
      · rw [uIcc_of_ge hle] at hw; linarith [hw.1]
    by_cases hyz : z = y
    · subst hyz
      have hs : c01_secant (fbar + r) z z = deriv (fbar + r) z := if_pos rfl
      have hs' : c01_secant h z z = deriv h z := if_pos rfl
      have hm : 0 ≤ min 1 (jb z ^ (1 / p) * |z - z|) :=
        le_min zero_le_one (mul_nonneg (hjnn _ _) (abs_nonneg _))
      refine ⟨?_, ?_, s1 z (by linarith), ?_⟩
      · rw [hs]; have h1 := P2a z (by linarith); have h2 := hjnn z (-beta p)
        have h3 : 2 * CP * jb z ^ (-beta p) ≤ (33 * CP + 33) * jb z ^ (-beta p) :=
          mul_le_mul_of_nonneg_right (by linarith) h2
        linarith
      · rw [hs, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg (by positivity) (hjnn _ _)) hm
      · rw [hs', sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hx) (hjnn _ _)) hm
    have hyz' : y ≠ z := Ne.symm hyz
    obtain ⟨ξ, hξ, hξe⟩ := c10_aux_secant_mvt hdW hyz'
    obtain ⟨η, hη, hηe⟩ := c10_aux_secant_mvt hdh hyz'
    have Sf : |c01_secant (fbar + r) y z| ≤ 32 * CP * jb y ^ (-beta p) := by
      rw [← hξe]
      refine (P2a ξ (wpos ξ hξ)).trans ?_
      rw [mul_assoc, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (c10_aux_jb_compare (geo ξ hξ).2.1 (geo ξ hξ).2.2
        (by rw [abs_le]; constructor <;> linarith)) hCP.le
    have Sh : |c01_secant h y z| ≤ 32 * xh * jb y ^ (-γ + 1 / p) := by
      rw [← hηe]
      refine (s1 η (wpos η hη)).trans ?_
      rw [mul_assoc, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (c10_aux_jb_compare (geo η hη).2.1 (geo η hη).2.2
        (by rw [abs_le]; constructor <;> linarith)) hx
    have f1 := P2a y (by linarith)
    have h1 := s1 y (by linarith)
    -- second-derivative bounds on `[y,z]`
    have Lf : ∀ᵐ w, w ∈ uIcc y z → |deriv (deriv (fbar + r)) w| ≤ 32 * CP * jb y ^ (-beta p + 1 / p) := by
      filter_upwards [P2b] with w hw hwI
      refine (hw (wpos w hwI)).trans ?_
      rw [mul_assoc, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (c10_aux_jb_compare (geo w hwI).2.1 (geo w hwI).2.2
        (by rw [abs_le]; constructor <;> linarith)) hCP.le
    have Lh : ∀ᵐ w, w ∈ uIcc y z → |deriv (deriv h) w| ≤ 32 * xh * jb y ^ (-γ + 2 / p) := by
      filter_upwards [s3] with w hw hwI
      refine (hw (wpos w hwI)).trans ?_
      rw [mul_assoc, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (c10_aux_jb_compare (geo w hwI).2.1 (geo w hwI).2.2
        (by rw [abs_le]; constructor <;> linarith)) hx
    obtain ⟨-, -, -, secf, -⟩ := c10_secant_identities (fbar + r) hW y z hyz'
    obtain ⟨-, -, -, sech, -⟩ := c10_secant_identities h hh.1 y z hyz'
    have df := (secf _ Lf).1
    have dh := (sech _ Lh).1
    have e1 : jb y ^ (-beta p + 1 / p) = jb y ^ (-beta p) * jb y ^ (1 / p) := by
      rw [← Real.rpow_add (hjpos y)]
    have e2 : jb y ^ (-γ + 2 / p) = jb y ^ (-γ + 1 / p) * jb y ^ (1 / p) := by
      rw [← Real.rpow_add (hjpos y)]; ring_nf
    have hj1 := hjnn y (-beta p); have hj2 := hjnn y (-γ + 1 / p); have hj3 := hjnn y (1 / p)
    refine ⟨?_, ?_, h1, ?_⟩
    · calc _ ≤ CP * jb y ^ (-beta p) + 32 * CP * jb y ^ (-beta p) := add_le_add f1 Sf
        _ = 33 * CP * jb y ^ (-beta p) := by ring
        _ ≤ (33 * CP + 33) * jb y ^ (-beta p) := mul_le_mul_of_nonneg_right (by linarith) hj1
    · have A0 : 0 ≤ (33 * CP + 33) * jb y ^ (-beta p) := by positivity
      refine hmin A0 ?_ ?_
      · calc _ ≤ |deriv (fbar + r) y| + |c01_secant (fbar + r) y z| := abs_sub _ _
          _ ≤ CP * jb y ^ (-beta p) + 32 * CP * jb y ^ (-beta p) := add_le_add f1 Sf
          _ = 33 * CP * jb y ^ (-beta p) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hj1
      · calc _ ≤ |y - z| * (32 * CP * jb y ^ (-beta p + 1 / p)) := df
          _ = 32 * CP * jb y ^ (-beta p) * (jb y ^ (1 / p) * |y - z|) := by rw [e1]; ring
          _ ≤ _ := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg hj3 (abs_nonneg _))
              exact mul_le_mul_of_nonneg_right (by linarith) hj1
    · have A0 : 0 ≤ (33 * CP + 33) * xh * jb y ^ (-γ + 1 / p) := by positivity
      refine hmin A0 ?_ ?_
      · calc _ ≤ |deriv h y| + |c01_secant h y z| := abs_sub _ _
          _ ≤ xh * jb y ^ (-γ + 1 / p) + 32 * xh * jb y ^ (-γ + 1 / p) := add_le_add h1 Sh
          _ = 33 * xh * jb y ^ (-γ + 1 / p) := by ring
          _ ≤ _ := by
              apply mul_le_mul_of_nonneg_right _ hj2
              exact mul_le_mul_of_nonneg_right hC2 hx
      · calc _ ≤ |y - z| * (32 * xh * jb y ^ (-γ + 2 / p)) := dh
          _ = 32 * xh * jb y ^ (-γ + 1 / p) * (jb y ^ (1 / p) * |y - z|) := by rw [e2]; ring
          _ ≤ _ := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              apply mul_le_mul_of_nonneg_right _ hj2
              exact mul_le_mul_of_nonneg_right (by linarith) hx
  · -- `y ≥ 2`, second derivatives
    filter_upwards [P2b, s3] with y fy hy3 z hy hz hzy
    have hy' : 2 ≤ |y| := by rwa [abs_of_nonneg (by linarith)]
    have hsub : ∀ w ∈ uIcc y z, w ∈ Ici (0:ℝ) := fun w hw =>
      (wsign y z hy' hz w hw).1 (by linarith)
    have Lf := Lgen _ _ _ hCP.le eb1 _ P2b' y z hy' hz hsub
    have Lh := Lgen _ _ _ hx eb2 _ s3' y z hy' hz hsub
    obtain ⟨-, -, -, secf, -⟩ := c10_secant_identities (fbar + r) hW y z (Ne.symm hzy)
    obtain ⟨-, -, -, sech, -⟩ := c10_secant_identities h hh.1 y z (Ne.symm hzy)
    have hj1 := hjnn y (-beta p + 1 / p); have hj2 := hjnn y (-γ + 2 / p)
    constructor
    · calc _ ≤ CP * jb y ^ (-beta p + 1 / p) + 32 * CP * jb y ^ (-beta p + 1 / p) :=
            add_le_add (fy (by linarith)) (secf _ Lf).2
        _ = 33 * CP * jb y ^ (-beta p + 1 / p) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hj1
    · calc _ ≤ xh * jb y ^ (-γ + 2 / p) + 32 * xh * jb y ^ (-γ + 2 / p) :=
            add_le_add (hy3 (by linarith)) (sech _ Lh).2
        _ = 33 * xh * jb y ^ (-γ + 2 / p) := by ring
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ hj2
            exact mul_le_mul_of_nonneg_right hC2 hx
  · -- `y ≤ -2`, values
    intro y z hy hz
    have hy' : 2 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    have hsub : ∀ w ∈ uIcc y z, w ∈ Iic (0:ℝ) := fun w hw =>
      (wsign y z hy' hz w hw).2 (by linarith)
    have hj1 := hjnn y (-p - 2); have hj2 := hjnn y (-γ - 2)
    by_cases hyz : z = y
    · subst hyz
      have hs : c01_secant (fbar + r) z z = deriv (fbar + r) z := if_pos rfl
      have hs' : c01_secant h z z = deriv h z := if_pos rfl
      refine ⟨?_, ?_, s2 z (by linarith), ?_⟩
      · rw [hs]; have := u0 z; linarith
      · rw [hs, sub_self, abs_zero, sub_self, abs_zero, mul_zero]
      · rw [hs', sub_self, abs_zero, sub_self, abs_zero, mul_zero]
    have hyz' : y ≠ z := Ne.symm hyz
    obtain ⟨ξ, -, hξe⟩ := c10_aux_secant_mvt hdW hyz'
    have Lf := Lgen _ _ _ hCP.le eb3 _ P3b' y z hy' hz hsub
    have Lh := Lgen _ _ _ hx eb4 _ s4' y z hy' hz hsub
    obtain ⟨-, -, -, secf, -⟩ := c10_secant_identities (fbar + r) hW y z hyz'
    obtain ⟨-, -, -, sech, -⟩ := c10_secant_identities h hh.1 y z hyz'
    refine ⟨?_, ?_, s2 y (by linarith), ?_⟩
    · rw [← hξe]; have := u0 y; have := u0 ξ; linarith
    · calc _ ≤ |y - z| * (32 * CP * jb y ^ (-p - 2)) := (secf _ Lf).1
        _ = (32 * CP) * jb y ^ (-p - 2) * |y - z| := by ring
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_right (by linarith) hj1
    · calc _ ≤ |y - z| * (32 * xh * jb y ^ (-γ - 2)) := (sech _ Lh).1
        _ = 32 * xh * jb y ^ (-γ - 2) * |y - z| := by ring
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            apply mul_le_mul_of_nonneg_right _ hj2
            exact mul_le_mul_of_nonneg_right (by linarith) hx
  · -- `y ≤ -2`, second derivatives
    filter_upwards [P3b, s4] with y fy hy4 z hy hz hzy
    have hy' : 2 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    have hsub : ∀ w ∈ uIcc y z, w ∈ Iic (0:ℝ) := fun w hw =>
      (wsign y z hy' hz w hw).2 (by linarith)
    have Lf := Lgen _ _ _ hCP.le eb3 _ P3b' y z hy' hz hsub
    have Lh := Lgen _ _ _ hx eb4 _ s4' y z hy' hz hsub
    obtain ⟨-, -, -, secf, -⟩ := c10_secant_identities (fbar + r) hW y z (Ne.symm hzy)
    obtain ⟨-, -, -, sech, -⟩ := c10_secant_identities h hh.1 y z (Ne.symm hzy)
    have hj1 := hjnn y (-p - 2); have hj2 := hjnn y (-γ - 2)
    constructor
    · calc _ ≤ CP * jb y ^ (-p - 2) + 32 * CP * jb y ^ (-p - 2) :=
            add_le_add (fy (by linarith)) (secf _ Lf).2
        _ = 33 * CP * jb y ^ (-p - 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hj1
    · calc _ ≤ xh * jb y ^ (-γ - 2) + 32 * xh * jb y ^ (-γ - 2) :=
            add_le_add (hy4 (by linarith)) (sech _ Lh).2
        _ = 33 * xh * jb y ^ (-γ - 2) := by ring
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ hj2
            exact mul_le_mul_of_nonneg_right hC2 hx

/-- Helper: refined kernel bounds `|∇Γ_ε| ≤ C ε |u-v| (|u|+|v|)`, `|∇²Γ_ε| ≤ C ε (|u|+|v|)`
(rmk:analysis_vanishing_diagonal). -/
theorem c10_aux_kernel_bounds2 (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 1 ≤ R) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ u v : ℝ, |u| ≤ R → |v| ≤ R →
      |c10_N_pieces_Gamma_d1 p ε u v| ≤ C * ε * (|u - v| * (|u| + |v|)) ∧
      |c10_N_pieces_Gamma_d2 p ε u v| ≤ C * ε * (|u - v| * (|u| + |v|)) ∧
      |c10_N_pieces_Gamma_d12 p ε u v| ≤ C * ε * (|u| + |v|) ∧
      |c10_N_pieces_Gamma_d22 p ε u v| ≤ C * ε * (|u| + |v|) := by
  obtain ⟨⟨C, hC, hb⟩, -⟩ := analysis_vanishing_diagonal p R hp hp1 hR
  refine ⟨C 1 + C 2, by have := hC 1; have := hC 2; positivity, fun ε hε hε1 u v hu hv => ?_⟩
  obtain ⟨-, -, h2a, h2b, -, -, -⟩ := hb ε hε hε1 u v hu hv
  change ‖fderiv ℝ (c10_aux_G p ε) (u, v)‖ ≤ _ at h2a
  change ‖iteratedFDeriv ℝ 2 (c10_aux_G p ε) (u, v)‖ ≤ _ at h2b
  obtain ⟨e1, e2⟩ := c10_aux_d_eq p ε hp (by linarith) hε u v
  obtain ⟨-, f12, f22⟩ := c10_aux_dd_eq p ε hp hp1 hε u v
  have n10 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have n01 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have c1 := hC 1; have c2 := hC 2
  have hX : 0 ≤ ε * (|u - v| * (|u| + |v|)) := by positivity
  have hY : 0 ≤ ε * (|u| + |v|) := by positivity
  have L : ∀ w : ℝ × ℝ, ‖w‖ = 1 → |fderiv ℝ (c10_aux_G p ε) (u, v) w| ≤
      (C 1 + C 2) * ε * (|u - v| * (|u| + |v|)) := by
    intro w hw
    have := (fderiv ℝ (c10_aux_G p ε) (u, v)).le_opNorm w
    rw [hw, mul_one, Real.norm_eq_abs] at this
    refine this.trans (h2a.trans ?_)
    have : C 1 * ε * |u - v| * (|u| + |v|) = C 1 * (ε * (|u - v| * (|u| + |v|))) := by ring
    rw [this, mul_assoc]; nlinarith
  have D : ∀ v' w : ℝ × ℝ, ‖v'‖ = 1 → ‖w‖ = 1 →
      |fderiv ℝ (fderiv ℝ (c10_aux_G p ε)) (u, v) v' w| ≤ (C 1 + C 2) * ε * (|u| + |v|) := by
    intro v' w hv' hw
    have := c10_aux_D2_le p ε (u, v) v' w
    rw [hv', hw, mul_one, mul_one] at this
    refine this.trans (h2b.trans ?_)
    have : C 2 * ε * (|u| + |v|) = C 2 * (ε * (|u| + |v|)) := by ring
    rw [this, mul_assoc]; nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1]; exact L _ n10
  · rw [e2]; exact L _ n01
  · rw [f12]; exact D _ _ n01 n10
  · rw [f22]; exact D _ _ n01 n01

set_option maxHeartbeats 800000 in
/-- Helper (pure algebra): near-field bounds for `y ≥ 2`, in terms of `a = ⟨y⟩^{-β}`,
`b = ⟨y⟩^{1/p}`, `c = ‖h‖⟨y⟩^{-γ+1/p}` and `m = min(1, b|y-z|)`. -/
theorem c10_aux_near_alg_plus {X Cn a b c m w u v h1 S f2 sf h2 sh d1 d2 d11 d12 d22 : ℝ}
    (hX : 0 ≤ X) (hCn : 0 ≤ Cn) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (hw : w ≠ 0) (hmw : m ≤ b * |w|)
    (huv : |u| + |v| ≤ Cn * a) (hd : |u - v| ≤ Cn * a * m) (hh1 : |h1| ≤ c)
    (hhS : |h1 - S| ≤ Cn * c * m) (hf2 : |f2| + |sf| ≤ Cn * (a * b)) (hh2 : |h2| + |sh| ≤ Cn * (c * b))
    (k1 : |d1 + d2| ≤ X * (u - v) ^ 2) (k2 : |d2| ≤ X * (|u - v| * (|u| + |v|)))
    (k3 : |d11 + d12| ≤ X * |u - v|) (k4 : |d12 + d22| ≤ X * |u - v|)
    (k5 : |d12| ≤ X * (|u| + |v|)) (k6 : |d22| ≤ X * (|u| + |v|)) :
    |(d1 + d2) * h1 + d2 * (S - h1)| ≤ X * (2 * (Cn + 1) ^ 3) * (a ^ 2 * c) * m ^ 2 ∧
    |(d11 + d12) * f2 * h1 + (d12 + d22) * sf * h1 + (d1 + d2) * h2 +
        (d12 * f2 + d22 * sf) * (S - h1) + d2 * (sh - h2)| +
      |(d1 + d2) * h1 + d2 * (S - h1)| / |w| ≤ X * (10 * (Cn + 1) ^ 3) * (a ^ 2 * c * b) * m := by
  have hw0 : 0 < |w| := abs_pos.2 hw
  have hC1 : Cn ≤ (Cn + 1) := by linarith
  have hd2 : (u - v) ^ 2 ≤ (Cn * a * m) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hP : 0 ≤ Cn * a * m := by positivity
  set P := a ^ 2 * c with hPdef
  have hP0 : 0 ≤ P := by positivity
  -- elementary factor bounds
  have F1 : |d1 + d2| ≤ X * Cn ^ 2 * a ^ 2 * m ^ 2 := by
    calc |d1 + d2| ≤ X * (u - v) ^ 2 := k1
      _ ≤ X * (Cn * a * m) ^ 2 := mul_le_mul_of_nonneg_left hd2 hX
      _ = _ := by ring
  have F2 : |d2| ≤ X * Cn ^ 2 * a ^ 2 * m := by
    calc |d2| ≤ X * (|u - v| * (|u| + |v|)) := k2
      _ ≤ X * ((Cn * a * m) * (Cn * a)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hd huv (by positivity) hP) hX
      _ = _ := by ring
  have F3 : |d11 + d12| ≤ X * Cn * a * m := by
    calc _ ≤ X * |u - v| := k3
      _ ≤ X * (Cn * a * m) := mul_le_mul_of_nonneg_left hd hX
      _ = _ := by ring
  have F4 : |d12 + d22| ≤ X * Cn * a * m := by
    calc _ ≤ X * |u - v| := k4
      _ ≤ X * (Cn * a * m) := mul_le_mul_of_nonneg_left hd hX
      _ = _ := by ring
  have F5 : |d12| ≤ X * Cn * a := (k5.trans (mul_le_mul_of_nonneg_left huv hX)).trans (le_of_eq (by ring))
  have F6 : |d22| ≤ X * Cn * a := (k6.trans (mul_le_mul_of_nonneg_left huv hX)).trans (le_of_eq (by ring))
  have hf2' : |f2| ≤ Cn * (a * b) := le_trans (by linarith [abs_nonneg sf]) hf2
  have hsf' : |sf| ≤ Cn * (a * b) := le_trans (by linarith [abs_nonneg f2]) hf2
  have hh2' : |h2| ≤ Cn * (c * b) := le_trans (by linarith [abs_nonneg sh]) hh2
  have hSh : |S - h1| ≤ Cn * c * m := by rw [abs_sub_comm]; exact hhS
  have hshh : |sh - h2| ≤ Cn * (c * b) := (abs_sub _ _).trans (by linarith [abs_nonneg sh])
  have hm2 : m ^ 2 ≤ m := by rw [sq]; exact mul_le_of_le_one_left hm0 hm1
  -- value
  have V1 : |(d1 + d2) * h1| ≤ X * Cn ^ 2 * a ^ 2 * m ^ 2 * c := c10_aux_abs_mul2_le F1 hh1
  have V2 : |d2 * (S - h1)| ≤ X * Cn ^ 2 * a ^ 2 * m * (Cn * c * m) := c10_aux_abs_mul2_le F2 hSh
  have hV : |(d1 + d2) * h1 + d2 * (S - h1)| ≤ X * (Cn ^ 2 + Cn ^ 3) * P * m ^ 2 := by
    calc _ ≤ |(d1 + d2) * h1| + |d2 * (S - h1)| := abs_add_le _ _
      _ ≤ _ := add_le_add V1 V2
      _ = _ := by simp only [hPdef]; ring
  have hcub : Cn ^ 2 + Cn ^ 3 ≤ 2 * (Cn + 1) ^ 3 := by nlinarith [sq_nonneg Cn, pow_nonneg hCn 3]
  have hXP : 0 ≤ X * P * m ^ 2 := by positivity
  refine ⟨hV.trans ?_, ?_⟩
  · calc X * (Cn ^ 2 + Cn ^ 3) * P * m ^ 2 = (Cn ^ 2 + Cn ^ 3) * (X * P * m ^ 2) := by ring
      _ ≤ 2 * (Cn + 1) ^ 3 * (X * P * m ^ 2) := mul_le_mul_of_nonneg_right hcub hXP
      _ = _ := by ring
  -- derivative
  have T1 : |(d11 + d12) * f2 * h1| ≤ X * Cn * a * m * (Cn * (a * b)) * c :=
    c10_aux_abs_mul3_le F3 hf2' hh1
  have T2 : |(d12 + d22) * sf * h1| ≤ X * Cn * a * m * (Cn * (a * b)) * c :=
    c10_aux_abs_mul3_le F4 hsf' hh1
  have T3 : |(d1 + d2) * h2| ≤ X * Cn ^ 2 * a ^ 2 * m ^ 2 * (Cn * (c * b)) :=
    c10_aux_abs_mul2_le F1 hh2'
  have T4 : |(d12 * f2 + d22 * sf) * (S - h1)| ≤
      (X * Cn * a * (Cn * (a * b)) + X * Cn * a * (Cn * (a * b))) * (Cn * c * m) :=
    c10_aux_abs_mul2_le ((abs_add_le _ _).trans (add_le_add (c10_aux_abs_mul2_le F5 hf2')
      (c10_aux_abs_mul2_le F6 hsf'))) hSh
  have T5 : |d2 * (sh - h2)| ≤ X * Cn ^ 2 * a ^ 2 * m * (Cn * (c * b)) := c10_aux_abs_mul2_le F2 hshh
  have T6 : |(d1 + d2) * h1 + d2 * (S - h1)| / |w| ≤ X * (Cn ^ 2 + Cn ^ 3) * P * m * b := by
    rw [div_le_iff₀ hw0]
    calc _ ≤ X * (Cn ^ 2 + Cn ^ 3) * P * m ^ 2 := hV
      _ = X * (Cn ^ 2 + Cn ^ 3) * P * m * m := by ring
      _ ≤ X * (Cn ^ 2 + Cn ^ 3) * P * m * (b * |w|) :=
          mul_le_mul_of_nonneg_left hmw (by positivity)
      _ = _ := by ring
  have hT3 : X * Cn ^ 2 * a ^ 2 * m ^ 2 * (Cn * (c * b)) ≤ X * Cn ^ 3 * (P * b) * m := by
    have : X * Cn ^ 2 * a ^ 2 * m ^ 2 * (Cn * (c * b)) = (X * Cn ^ 3 * (P * b)) * m ^ 2 := by
      simp only [hPdef]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hm2 (by positivity)
  have hsum : |(d11 + d12) * f2 * h1 + (d12 + d22) * sf * h1 + (d1 + d2) * h2 +
      (d12 * f2 + d22 * sf) * (S - h1) + d2 * (sh - h2)| ≤
      X * (2 * Cn ^ 2 + 4 * Cn ^ 3) * (P * b) * m := by
    calc _ ≤ |(d11 + d12) * f2 * h1| + |(d12 + d22) * sf * h1| + |(d1 + d2) * h2| +
          |(d12 * f2 + d22 * sf) * (S - h1)| + |d2 * (sh - h2)| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact abs_add_le _ _
      _ ≤ X * Cn * a * m * (Cn * (a * b)) * c + X * Cn * a * m * (Cn * (a * b)) * c +
          X * Cn ^ 3 * (P * b) * m +
          (X * Cn * a * (Cn * (a * b)) + X * Cn * a * (Cn * (a * b))) * (Cn * c * m) +
          X * Cn ^ 2 * a ^ 2 * m * (Cn * (c * b)) := by linarith
      _ = _ := by simp only [hPdef]; ring
  have hc10 : 2 * Cn ^ 2 + 4 * Cn ^ 3 + (Cn ^ 2 + Cn ^ 3) ≤ 10 * (Cn + 1) ^ 3 := by
    nlinarith [sq_nonneg Cn, pow_nonneg hCn 3]
  have hXPb : 0 ≤ X * (P * b) * m := by positivity
  calc _ ≤ X * (2 * Cn ^ 2 + 4 * Cn ^ 3) * (P * b) * m + X * (Cn ^ 2 + Cn ^ 3) * P * m * b :=
        add_le_add hsum T6
    _ = (2 * Cn ^ 2 + 4 * Cn ^ 3 + (Cn ^ 2 + Cn ^ 3)) * (X * (P * b) * m) := by ring
    _ ≤ 10 * (Cn + 1) ^ 3 * (X * (P * b) * m) := mul_le_mul_of_nonneg_right hc10 hXPb
    _ = _ := by simp only [hPdef]; ring

set_option maxHeartbeats 800000 in
/-- Helper (pure algebra): near-field bounds for `y ≤ -2`, with `A = ⟨y⟩^{-p-2}`,
`c₁ = ‖h‖⟨y⟩^{-γ-1}`, `c₂ = ‖h‖⟨y⟩^{-γ-2}`, `Q = ‖h‖⟨y⟩^{-γ-p-4}`. -/
theorem c10_aux_near_alg_minus {X Cn A c1 c2 Q w u v h1 S f2 sf h2 sh d1 d2 d11 d12 d22 : ℝ}
    (hX : 0 ≤ X) (hCn : 0 ≤ Cn) (hA : 0 ≤ A) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hQ : 0 ≤ Q)
    (hw : w ≠ 0) (hA1 : A ≤ 1) (hAw : A * |w| ≤ 1) (hAc1 : A ^ 2 * c1 ≤ Q) (hAc2 : A * c2 ≤ Q)
    (huv : |u| + |v| ≤ Cn) (hd : |u - v| ≤ Cn * A * |w|) (hh1 : |h1| ≤ c1)
    (hhS : |h1 - S| ≤ Cn * c2 * |w|) (hf2 : |f2| + |sf| ≤ Cn * A) (hh2 : |h2| + |sh| ≤ Cn * c2)
    (k1 : |d1 + d2| ≤ X * (u - v) ^ 2) (k2 : |d2| ≤ X * (|u - v| * (|u| + |v|)))
    (k3 : |d11 + d12| ≤ X * |u - v|) (k4 : |d12 + d22| ≤ X * |u - v|)
    (k5 : |d12| ≤ X * (|u| + |v|)) (k6 : |d22| ≤ X * (|u| + |v|)) :
    |(d1 + d2) * h1 + d2 * (S - h1)| ≤ X * (2 * (Cn + 1) ^ 3) * Q * |w| ^ 2 ∧
    |(d11 + d12) * f2 * h1 + (d12 + d22) * sf * h1 + (d1 + d2) * h2 +
        (d12 * f2 + d22 * sf) * (S - h1) + d2 * (sh - h2)| +
      |(d1 + d2) * h1 + d2 * (S - h1)| / |w| ≤ X * (10 * (Cn + 1) ^ 3) * Q * |w| := by
  have hw0 : 0 < |w| := abs_pos.2 hw
  set r := |w|
  have hd2 : (u - v) ^ 2 ≤ (Cn * A * r) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have F1 : |d1 + d2| ≤ X * Cn ^ 2 * A ^ 2 * r ^ 2 :=
    (k1.trans (mul_le_mul_of_nonneg_left hd2 hX)).trans (le_of_eq (by ring))
  have F2 : |d2| ≤ X * Cn ^ 2 * A * r :=
    (k2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hd huv (by positivity) (by positivity)) hX)).trans
      (le_of_eq (by ring))
  have F3 : |d11 + d12| ≤ X * Cn * A * r :=
    (k3.trans (mul_le_mul_of_nonneg_left hd hX)).trans (le_of_eq (by ring))
  have F4 : |d12 + d22| ≤ X * Cn * A * r :=
    (k4.trans (mul_le_mul_of_nonneg_left hd hX)).trans (le_of_eq (by ring))
  have F5 : |d12| ≤ X * Cn := k5.trans (mul_le_mul_of_nonneg_left huv hX)
  have F6 : |d22| ≤ X * Cn := k6.trans (mul_le_mul_of_nonneg_left huv hX)
  have hf2' : |f2| ≤ Cn * A := le_trans (by linarith [abs_nonneg sf]) hf2
  have hsf' : |sf| ≤ Cn * A := le_trans (by linarith [abs_nonneg f2]) hf2
  have hh2' : |h2| ≤ Cn * c2 := le_trans (by linarith [abs_nonneg sh]) hh2
  have hSh : |S - h1| ≤ Cn * c2 * r := by rw [abs_sub_comm]; exact hhS
  have hshh : |sh - h2| ≤ Cn * c2 := (abs_sub _ _).trans (by linarith [abs_nonneg sh])
  -- auxiliary comparisons
  have q1 : A ^ 2 * c1 ≤ Q := hAc1
  have q2 : A ^ 2 * c2 * r ≤ Q := by
    calc A ^ 2 * c2 * r = (A * r) * (A * c2) := by ring
      _ ≤ 1 * Q := mul_le_mul hAw hAc2 (by positivity) zero_le_one
      _ = Q := one_mul Q
  have V1 : |(d1 + d2) * h1| ≤ X * Cn ^ 2 * Q * r ^ 2 := by
    refine (c10_aux_abs_mul2_le F1 hh1).trans ?_
    have : X * Cn ^ 2 * A ^ 2 * r ^ 2 * c1 = (X * Cn ^ 2 * r ^ 2) * (A ^ 2 * c1) := by ring
    rw [this]
    calc _ ≤ (X * Cn ^ 2 * r ^ 2) * Q := mul_le_mul_of_nonneg_left q1 (by positivity)
      _ = _ := by ring
  have V2 : |d2 * (S - h1)| ≤ X * Cn ^ 3 * Q * r ^ 2 := by
    refine (c10_aux_abs_mul2_le F2 hSh).trans ?_
    have : X * Cn ^ 2 * A * r * (Cn * c2 * r) = (X * Cn ^ 3 * r ^ 2) * (A * c2) := by ring
    rw [this]
    calc _ ≤ (X * Cn ^ 3 * r ^ 2) * Q := mul_le_mul_of_nonneg_left hAc2 (by positivity)
      _ = _ := by ring
  have hV : |(d1 + d2) * h1 + d2 * (S - h1)| ≤ X * (Cn ^ 2 + Cn ^ 3) * Q * r ^ 2 :=
    ((abs_add_le _ _).trans (add_le_add V1 V2)).trans (le_of_eq (by ring))
  have hcub : Cn ^ 2 + Cn ^ 3 ≤ 2 * (Cn + 1) ^ 3 := by nlinarith [sq_nonneg Cn, pow_nonneg hCn 3]
  refine ⟨hV.trans ?_, ?_⟩
  · calc X * (Cn ^ 2 + Cn ^ 3) * Q * r ^ 2 = (Cn ^ 2 + Cn ^ 3) * (X * Q * r ^ 2) := by ring
      _ ≤ 2 * (Cn + 1) ^ 3 * (X * Q * r ^ 2) := mul_le_mul_of_nonneg_right hcub (by positivity)
      _ = _ := by ring
  have T1 : |(d11 + d12) * f2 * h1| ≤ X * Cn ^ 2 * Q * r := by
    refine (c10_aux_abs_mul3_le F3 hf2' hh1).trans ?_
    have : X * Cn * A * r * (Cn * A) * c1 = (X * Cn ^ 2 * r) * (A * (A * c1)) := by ring
    rw [this]
    have : A * (A * c1) ≤ Q := by linarith [hAc1, show A * (A * c1) = A ^ 2 * c1 by ring]
    calc _ ≤ (X * Cn ^ 2 * r) * Q := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have T2 : |(d12 + d22) * sf * h1| ≤ X * Cn ^ 2 * Q * r := by
    refine (c10_aux_abs_mul3_le F4 hsf' hh1).trans ?_
    have : X * Cn * A * r * (Cn * A) * c1 = (X * Cn ^ 2 * r) * (A * (A * c1)) := by ring
    rw [this]
    have : A * (A * c1) ≤ Q := by linarith [hAc1, show A * (A * c1) = A ^ 2 * c1 by ring]
    calc _ ≤ (X * Cn ^ 2 * r) * Q := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have T3 : |(d1 + d2) * h2| ≤ X * Cn ^ 3 * Q * r := by
    refine (c10_aux_abs_mul2_le F1 hh2').trans ?_
    have : X * Cn ^ 2 * A ^ 2 * r ^ 2 * (Cn * c2) = (X * Cn ^ 3 * r) * (A ^ 2 * c2 * r) := by ring
    rw [this]
    calc _ ≤ (X * Cn ^ 3 * r) * Q := mul_le_mul_of_nonneg_left q2 (by positivity)
      _ = _ := by ring
  have T4 : |(d12 * f2 + d22 * sf) * (S - h1)| ≤ 2 * (X * Cn ^ 3 * Q * r) := by
    refine (c10_aux_abs_mul2_le ((abs_add_le _ _).trans (add_le_add (c10_aux_abs_mul2_le F5 hf2')
      (c10_aux_abs_mul2_le F6 hsf'))) hSh).trans ?_
    have : (X * Cn * (Cn * A) + X * Cn * (Cn * A)) * (Cn * c2 * r) =
        2 * (X * Cn ^ 3 * r) * (A * c2) := by ring
    rw [this]
    calc _ ≤ 2 * (X * Cn ^ 3 * r) * Q := mul_le_mul_of_nonneg_left hAc2 (by positivity)
      _ = _ := by ring
  have T5 : |d2 * (sh - h2)| ≤ X * Cn ^ 3 * Q * r := by
    refine (c10_aux_abs_mul2_le F2 hshh).trans ?_
    have : X * Cn ^ 2 * A * r * (Cn * c2) = (X * Cn ^ 3 * r) * (A * c2) := by ring
    rw [this]
    calc _ ≤ (X * Cn ^ 3 * r) * Q := mul_le_mul_of_nonneg_left hAc2 (by positivity)
      _ = _ := by ring
  have T6 : |(d1 + d2) * h1 + d2 * (S - h1)| / r ≤ X * (Cn ^ 2 + Cn ^ 3) * Q * r := by
    rw [div_le_iff₀ hw0]; exact hV.trans (le_of_eq (by ring))
  have hsum : |(d11 + d12) * f2 * h1 + (d12 + d22) * sf * h1 + (d1 + d2) * h2 +
      (d12 * f2 + d22 * sf) * (S - h1) + d2 * (sh - h2)| ≤
      X * (2 * Cn ^ 2 + 4 * Cn ^ 3) * Q * r := by
    calc _ ≤ |(d11 + d12) * f2 * h1| + |(d12 + d22) * sf * h1| + |(d1 + d2) * h2| +
          |(d12 * f2 + d22 * sf) * (S - h1)| + |d2 * (sh - h2)| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          exact abs_add_le _ _
      _ ≤ _ := by linarith
  have hc10 : 2 * Cn ^ 2 + 4 * Cn ^ 3 + (Cn ^ 2 + Cn ^ 3) ≤ 10 * (Cn + 1) ^ 3 := by
    nlinarith [sq_nonneg Cn, pow_nonneg hCn 3]
  calc _ ≤ X * (2 * Cn ^ 2 + 4 * Cn ^ 3) * Q * r + X * (Cn ^ 2 + Cn ^ 3) * Q * r :=
        add_le_add hsum T6
    _ = (2 * Cn ^ 2 + 4 * Cn ^ 3 + (Cn ^ 2 + Cn ^ 3)) * (X * Q * r) := by ring
    _ ≤ 10 * (Cn + 1) ^ 3 * (X * Q * r) := mul_le_mul_of_nonneg_right hc10 (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_N3_near_integrand.  The decomposition of `K_{f,h}`, its `y`-derivative
(chain rule; all `Γ_ε`-derivatives at `(f'(y), S_f(y,z))`), and the near-field bounds. -/
theorem c10_N3_near_integrand (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      -- decomposition (paper eq:N3_near_decomposition)
      (∀ y z : ℝ, c10_N3_linearization_K p ε (fbar + r) h y z =
        (c10_N_pieces_Gamma_d1 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) +
          c10_N_pieces_Gamma_d2 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z)) * deriv h y +
        c10_N_pieces_Gamma_d2 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) *
          (c01_secant h y z - deriv h y)) ∧
      -- `y`-derivative (paper eq:N3_near_integrand_derivative)
      (∀ᵐ y, ∀ z : ℝ, 2 ≤ |y| → |y - z| ≤ |y| / 2 → z ≠ y →
        deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y =
          (c10_N_pieces_Gamma_d11 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) +
              c10_N_pieces_Gamma_d12 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z)) *
            deriv (deriv (fbar + r)) y * deriv h y +
          (c10_N_pieces_Gamma_d12 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) +
              c10_N_pieces_Gamma_d22 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z)) *
            deriv (fun y' => c01_secant (fbar + r) y' z) y * deriv h y +
          (c10_N_pieces_Gamma_d1 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) +
              c10_N_pieces_Gamma_d2 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z)) *
            deriv (deriv h) y +
          (c10_N_pieces_Gamma_d12 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) *
              deriv (deriv (fbar + r)) y +
            c10_N_pieces_Gamma_d22 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) *
              deriv (fun y' => c01_secant (fbar + r) y' z) y) *
            (c01_secant h y z - deriv h y) +
          c10_N_pieces_Gamma_d2 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) *
            (deriv (fun y' => c01_secant h y' z) y - deriv (deriv h) y)) ∧
      -- bounds (paper eq:N3_near_integrand_bound)
      (∀ y z : ℝ, 2 ≤ y → |y - z| ≤ |y| / 2 →
        |c10_N3_linearization_K p ε (fbar + r) h y z| ≤
          C * ε * xNorm p γ h * jb y ^ (-2 * beta p - γ + 1 / p) *
            min 1 (jb y ^ (1 / p) * |y - z|) ^ 2) ∧
      (∀ y z : ℝ, y ≤ -2 → |y - z| ≤ |y| / 2 →
        |c10_N3_linearization_K p ε (fbar + r) h y z| ≤
          C * ε * xNorm p γ h * jb y ^ (-γ - p - 4) * |y - z| ^ 2) ∧
      -- bounds (paper eq:N3_near_integrand_derivative_bound)
      (∀ᵐ y, ∀ z : ℝ, 2 ≤ y → |y - z| ≤ |y| / 2 → z ≠ y →
        |deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y| +
            |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ≤
          C * ε * xNorm p γ h * jb y ^ (-2 * beta p - γ + 2 / p) *
            min 1 (jb y ^ (1 / p) * |y - z|)) ∧
      (∀ᵐ y, ∀ z : ℝ, y ≤ -2 → |y - z| ≤ |y| / 2 → z ≠ y →
        |deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y| +
            |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ≤
          C * ε * xNorm p γ h * jb y ^ (-γ - p - 4) * |y - z|) := by
  obtain ⟨hp0, -, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨Cn, hCn, hNI⟩ := c10_near_increments p γ M N hp hp1 hγ hM hN
  have hBk : 1 ≤ Cn + 1 := by linarith
  obtain ⟨Ck1, hCk1, hk1⟩ := c10_aux_kernel_bounds p (Cn + 1) hp0 hp1 hBk
  obtain ⟨Ck2, hCk2, hk2⟩ := c10_aux_kernel_bounds2 p (Cn + 1) hp0 hp1 hBk
  set Ck := Ck1 + Ck2
  refine ⟨Ck * (10 * (Cn + 1) ^ 3), by positivity, ?_⟩
  intro ε hε hε1 fbar hf r hr hrN h hh
  obtain ⟨-, Vp, D2p, Vm, D2m⟩ := hNI fbar hf r hr hrN h hh
  have hfA : fbar ∈ c01_admissible_class :=
    c10_aux_C2_admissible_class hf.1 (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have hrA := c10_aux_X_admissible_class p γ hp hp1 hγ hr
  obtain ⟨hfW, -, -, -⟩ := c10_aux_lin_W2 (f := fbar) (h := r) ⟨hfA.1, hfA.2.2⟩ ⟨hrA.1, hrA.2.2⟩ 1
  rw [one_smul] at hfW
  set f := fbar + r with hfdef
  set xh := xNorm p γ h
  have hxh : 0 ≤ xh := ENNReal.toReal_nonneg
  have hX : 0 ≤ Ck * ε := by positivity
  -- kernel bounds at the relevant arguments
  have KB : ∀ u v : ℝ, |u| ≤ Cn + 1 → |v| ≤ Cn + 1 →
      |c10_N_pieces_Gamma_d1 p ε u v + c10_N_pieces_Gamma_d2 p ε u v| ≤ Ck * ε * (u - v) ^ 2 ∧
      |c10_N_pieces_Gamma_d2 p ε u v| ≤ Ck * ε * (|u - v| * (|u| + |v|)) ∧
      |c10_N_pieces_Gamma_d11 p ε u v + c10_N_pieces_Gamma_d12 p ε u v| ≤ Ck * ε * |u - v| ∧
      |c10_N_pieces_Gamma_d12 p ε u v + c10_N_pieces_Gamma_d22 p ε u v| ≤ Ck * ε * |u - v| ∧
      |c10_N_pieces_Gamma_d12 p ε u v| ≤ Ck * ε * (|u| + |v|) ∧
      |c10_N_pieces_Gamma_d22 p ε u v| ≤ Ck * ε * (|u| + |v|) := by
    intro u v hu hv
    obtain ⟨-, -, -, -, -, -, a1, a2, a3⟩ := hk1 ε hε.le hε1 u v hu hv
    obtain ⟨-, b2, b3, b4⟩ := hk2 ε hε.le hε1 u v hu hv
    have e1 : Ck1 ≤ Ck := by simp only [Ck]; linarith
    have e2 : Ck2 ≤ Ck := by simp only [Ck]; linarith
    have m1 : ∀ (c c' t : ℝ), c ≤ c' → 0 ≤ t → c * ε * t ≤ c' * ε * t := fun c c' t hc ht =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hε.le) ht
    exact ⟨a1.trans (m1 _ _ _ e1 (sq_nonneg _)), b2.trans (m1 _ _ _ e2 (by positivity)),
      a2.trans (m1 _ _ _ e1 (abs_nonneg _)), a3.trans (m1 _ _ _ e1 (abs_nonneg _)),
      b3.trans (m1 _ _ _ e2 (by positivity)), b4.trans (m1 _ _ _ e2 (by positivity))⟩
  have decomp : ∀ y z : ℝ, c10_N3_linearization_K p ε f h y z =
      (c10_N_pieces_Gamma_d1 p ε (deriv f y) (c01_secant f y z) +
        c10_N_pieces_Gamma_d2 p ε (deriv f y) (c01_secant f y z)) * deriv h y +
      c10_N_pieces_Gamma_d2 p ε (deriv f y) (c01_secant f y z) * (c01_secant h y z - deriv h y) :=
    fun y z => by unfold c10_N3_linearization_K; ring
  have hKK : ∀ y : ℝ, |deriv f y| ≤ Cn + 1 → c10_N3_linearization_K p ε f h y y = 0 := by
    intro y hy
    obtain ⟨-, -, -, -, -, b2v, bs, -, -⟩ := hk1 ε hε.le hε1 (deriv f y) (deriv f y) hy hy
    simp only [sub_self, abs_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at b2v bs
    have d2 := abs_nonpos_iff.1 b2v
    have d1 : c10_N_pieces_Gamma_d1 p ε (deriv f y) (deriv f y) = 0 := by
      have := abs_nonpos_iff.1 bs; linarith
    unfold c10_N3_linearization_K
    have hs : c01_secant f y y = deriv f y := by simp [c01_secant]
    rw [hs, d1, d2]; ring
  have dform : ∀ᵐ y, ∀ z : ℝ, z ≠ y →
      deriv (fun y' => c10_N3_linearization_K p ε f h y' z) y =
        (c10_N_pieces_Gamma_d11 p ε (deriv f y) (c01_secant f y z) +
            c10_N_pieces_Gamma_d12 p ε (deriv f y) (c01_secant f y z)) *
          deriv (deriv f) y * deriv h y +
        (c10_N_pieces_Gamma_d12 p ε (deriv f y) (c01_secant f y z) +
            c10_N_pieces_Gamma_d22 p ε (deriv f y) (c01_secant f y z)) *
          deriv (fun y' => c01_secant f y' z) y * deriv h y +
        (c10_N_pieces_Gamma_d1 p ε (deriv f y) (c01_secant f y z) +
            c10_N_pieces_Gamma_d2 p ε (deriv f y) (c01_secant f y z)) * deriv (deriv h) y +
        (c10_N_pieces_Gamma_d12 p ε (deriv f y) (c01_secant f y z) * deriv (deriv f) y +
          c10_N_pieces_Gamma_d22 p ε (deriv f y) (c01_secant f y z) *
            deriv (fun y' => c01_secant f y' z) y) * (c01_secant h y z - deriv h y) +
        c10_N_pieces_Gamma_d2 p ε (deriv f y) (c01_secant f y z) *
          (deriv (fun y' => c01_secant h y' z) y - deriv (deriv h) y) := by
    filter_upwards [c10_aux_ae_differentiableAt hfW.2, c10_aux_ae_differentiableAt hh.1.2]
      with y h1 h2 z hzy
    have hyz : y ≠ z := Ne.symm hzy
    rw [(c10_aux_K_hasDeriv p ε hp0 hp1 hε.le hfW hh.1 hyz h1 h2).deriv,
      (c10_secant_identities f hfW y z hyz).2.2.1.deriv,
      (c10_secant_identities h hh.1 y z hyz).2.2.1.deriv]
    unfold c10_aux_DK; ring
  have hj : ∀ y : ℝ, 0 < jb y := c10_aux_jb_pos
  have rp : ∀ y a b : ℝ, jb y ^ a * jb y ^ b = jb y ^ (a + b) := fun y a b =>
    (Real.rpow_add (hj y) a b).symm
  refine ⟨decomp, ?_, fun y z hy hz => ?_, fun y z hy hz => ?_, ?_, ?_⟩
  · filter_upwards [dform] with y hy z _ _ hzy using hy z hzy
  · -- value, `y ≥ 2`
    have hjy : 0 < jb y := hj y
    obtain ⟨V1, V2, V3, V4⟩ := Vp y z hy hz
    set a := jb y ^ (-beta p)
    set b := jb y ^ (1 / p)
    set c := xh * jb y ^ (-γ + 1 / p)
    set m := min 1 (jb y ^ (1 / p) * |y - z|)
    have ha : a ≤ 1 := c10_aux_jb_rpow_le_one y (by
      have : 0 < beta p := by unfold beta; positivity
      linarith)
    have hu : |deriv f y| ≤ Cn + 1 := by
      have := mul_le_mul_of_nonneg_left ha hCn.le; nlinarith [abs_nonneg (c01_secant f y z)]
    have hv : |c01_secant f y z| ≤ Cn + 1 := by
      have := mul_le_mul_of_nonneg_left ha hCn.le; nlinarith [abs_nonneg (deriv f y)]
    by_cases hzy : z = y
    · subst hzy; rw [hKK z hu, abs_zero]; positivity
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := KB _ _ hu hv
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have := (c10_aux_near_alg_plus (X := Ck * ε) (Cn := Cn) (a := a) (b := b) (c := c) (m := m)
      (w := y - z) (f2 := 0) (sf := 0) (h2 := 0) (sh := 0) hX hCn.le (by positivity) (by positivity)
      (by positivity) (le_min zero_le_one (by positivity)) (min_le_left _ _) hw (min_le_right _ _)
      V1 V2 V3 (by rw [show c = xh * jb y ^ (-γ + 1 / p) from rfl]; linarith [V4])
      (by simp; positivity) (by simp; positivity) k1 k2 k3 k4 k5 k6).1
    have key : a ^ 2 * c = xh * jb y ^ (-2 * beta p - γ + 1 / p) := by
      simp only [a, c]
      rw [show (jb y ^ (-beta p)) ^ 2 * (xh * jb y ^ (-γ + 1 / p)) =
        xh * (jb y ^ (-beta p) * jb y ^ (-beta p) * jb y ^ (-γ + 1 / p)) by ring, rp, rp]
      rw [show -beta p + -beta p + (-γ + 1 / p) = -2 * beta p - γ + 1 / p by ring]
    rw [decomp]
    refine this.trans ?_
    rw [key]
    have h0 : 0 ≤ Ck * ε * (Cn + 1) ^ 3 * (xh * jb y ^ (-2 * beta p - γ + 1 / p)) * m ^ 2 := by
      positivity
    nlinarith
  · -- value, `y ≤ -2`
    have hjy : 0 < jb y := hj y
    obtain ⟨V1, V2, V3, V4⟩ := Vm y z hy hz
    have hu : |deriv f y| ≤ Cn + 1 := by linarith [abs_nonneg (c01_secant f y z)]
    have hv : |c01_secant f y z| ≤ Cn + 1 := by linarith [abs_nonneg (deriv f y)]
    by_cases hzy : z = y
    · subst hzy; rw [hKK z hu, abs_zero]; positivity
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := KB _ _ hu hv
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hwJ : |y - z| ≤ jb y := by
      have := c10_aux_abs_le_jb y; linarith [abs_nonneg y]
    have hA1 : jb y ^ (-p - 2) ≤ 1 := c10_aux_jb_rpow_le_one y (by linarith)
    have hAw : jb y ^ (-p - 2) * |y - z| ≤ 1 := by
      calc jb y ^ (-p - 2) * |y - z| ≤ jb y ^ (-p - 2) * jb y :=
            mul_le_mul_of_nonneg_left hwJ (by positivity)
        _ = jb y ^ (-p - 1) := by rw [mul_comm, c10_aux_jb_mul]; ring_nf
        _ ≤ 1 := c10_aux_jb_rpow_le_one y (by linarith)
    have hAc1 : (jb y ^ (-p - 2)) ^ 2 * (xh * jb y ^ (-γ - 1)) ≤ xh * jb y ^ (-γ - p - 4) := by
      rw [sq, ← mul_assoc, rp, mul_comm _ xh, mul_assoc, rp]
      exact mul_le_mul_of_nonneg_left (c10_aux_jb_rpow_mono y (by linarith)) hxh
    have hAc2 : jb y ^ (-p - 2) * (xh * jb y ^ (-γ - 2)) ≤ xh * jb y ^ (-γ - p - 4) := by
      rw [mul_left_comm, rp]; ring_nf; exact le_rfl
    have := (c10_aux_near_alg_minus (X := Ck * ε) (Cn := Cn) (A := jb y ^ (-p - 2))
      (c1 := xh * jb y ^ (-γ - 1)) (c2 := xh * jb y ^ (-γ - 2)) (Q := xh * jb y ^ (-γ - p - 4))
      (w := y - z) (f2 := 0) (sf := 0) (h2 := 0) (sh := 0) hX hCn.le (by positivity)
      (by positivity) (by positivity) (by positivity) hw hA1 hAw hAc1 hAc2 V1
      (by linarith [V2]) V3 (by linarith [V4]) (by simp; positivity) (by simp; positivity)
      k1 k2 k3 k4 k5 k6).1
    rw [decomp]
    refine this.trans ?_
    have h0 : 0 ≤ Ck * ε * (Cn + 1) ^ 3 * (xh * jb y ^ (-γ - p - 4)) * |y - z| ^ 2 := by
      positivity
    nlinarith
  · filter_upwards [dform, D2p] with y hdf hD2 z hy hz hzy
    have hjy : 0 < jb y := hj y
    obtain ⟨E1, E2⟩ := hD2 z hy hz hzy
    obtain ⟨V1, V2, V3, V4⟩ := Vp y z hy hz
    set a := jb y ^ (-beta p)
    set b := jb y ^ (1 / p)
    set c := xh * jb y ^ (-γ + 1 / p)
    set m := min 1 (jb y ^ (1 / p) * |y - z|)
    have ha : a ≤ 1 := c10_aux_jb_rpow_le_one y (by
      have : 0 < beta p := by unfold beta; positivity
      linarith)
    have hu : |deriv f y| ≤ Cn + 1 := by
      have := mul_le_mul_of_nonneg_left ha hCn.le; nlinarith [abs_nonneg (c01_secant f y z)]
    have hv : |c01_secant f y z| ≤ Cn + 1 := by
      have := mul_le_mul_of_nonneg_left ha hCn.le; nlinarith [abs_nonneg (deriv f y)]
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := KB _ _ hu hv
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hab : jb y ^ (-beta p + 1 / p) = a * b := (rp y _ _).symm
    have hcb : xh * jb y ^ (-γ + 2 / p) = c * b := by
      simp only [c, b]; rw [mul_assoc, rp]; ring_nf
    have := (c10_aux_near_alg_plus (X := Ck * ε) (Cn := Cn) (a := a) (b := b) (c := c) (m := m)
      (w := y - z) (f2 := deriv (deriv f) y) (sf := deriv (fun y' => c01_secant f y' z) y)
      (h2 := deriv (deriv h) y) (sh := deriv (fun y' => c01_secant h y' z) y)
      hX hCn.le (by positivity) (by positivity) (by positivity)
      (le_min zero_le_one (by positivity)) (min_le_left _ _) hw (min_le_right _ _)
      V1 V2 V3 (by linarith [V4]) (by rw [← hab]; exact E1)
      (by rw [← hcb]; linarith [E2]) k1 k2 k3 k4 k5 k6).2
    rw [hdf z hzy, decomp y z]
    refine this.trans (le_of_eq ?_)
    have key : a ^ 2 * c * b = xh * jb y ^ (-2 * beta p - γ + 2 / p) := by
      simp only [a, c, b]
      rw [show (jb y ^ (-beta p)) ^ 2 * (xh * jb y ^ (-γ + 1 / p)) * jb y ^ (1 / p) =
        xh * (jb y ^ (-beta p) * jb y ^ (-beta p) * jb y ^ (-γ + 1 / p) * jb y ^ (1 / p)) by ring,
        rp, rp, rp]
      rw [show -beta p + -beta p + (-γ + 1 / p) + 1 / p = -2 * beta p - γ + 2 / p by ring]
    rw [key]; ring
  · filter_upwards [dform, D2m] with y hdf hD2 z hy hz hzy
    have hjy : 0 < jb y := hj y
    obtain ⟨E1, E2⟩ := hD2 z hy hz hzy
    obtain ⟨V1, V2, V3, V4⟩ := Vm y z hy hz
    have hu : |deriv f y| ≤ Cn + 1 := by linarith [abs_nonneg (c01_secant f y z)]
    have hv : |c01_secant f y z| ≤ Cn + 1 := by linarith [abs_nonneg (deriv f y)]
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := KB _ _ hu hv
    have hw : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hwJ : |y - z| ≤ jb y := by
      have := c10_aux_abs_le_jb y; linarith [abs_nonneg y]
    have hA1 : jb y ^ (-p - 2) ≤ 1 := c10_aux_jb_rpow_le_one y (by linarith)
    have hAw : jb y ^ (-p - 2) * |y - z| ≤ 1 := by
      calc jb y ^ (-p - 2) * |y - z| ≤ jb y ^ (-p - 2) * jb y :=
            mul_le_mul_of_nonneg_left hwJ (by positivity)
        _ = jb y ^ (-p - 1) := by rw [mul_comm, c10_aux_jb_mul]; ring_nf
        _ ≤ 1 := c10_aux_jb_rpow_le_one y (by linarith)
    have hAc1 : (jb y ^ (-p - 2)) ^ 2 * (xh * jb y ^ (-γ - 1)) ≤ xh * jb y ^ (-γ - p - 4) := by
      rw [sq, ← mul_assoc, rp, mul_comm _ xh, mul_assoc, rp]
      exact mul_le_mul_of_nonneg_left (c10_aux_jb_rpow_mono y (by linarith)) hxh
    have hAc2 : jb y ^ (-p - 2) * (xh * jb y ^ (-γ - 2)) ≤ xh * jb y ^ (-γ - p - 4) := by
      rw [mul_left_comm, rp]; ring_nf; exact le_rfl
    have := (c10_aux_near_alg_minus (X := Ck * ε) (Cn := Cn) (A := jb y ^ (-p - 2))
      (c1 := xh * jb y ^ (-γ - 1)) (c2 := xh * jb y ^ (-γ - 2)) (Q := xh * jb y ^ (-γ - p - 4))
      (w := y - z) (f2 := deriv (deriv f) y) (sf := deriv (fun y' => c01_secant f y' z) y)
      (h2 := deriv (deriv h) y) (sh := deriv (fun y' => c01_secant h y' z) y) hX hCn.le
      (by positivity)
      (by positivity) (by positivity) (by positivity) hw hA1 hAw hAc1 hAc2 V1
      (by linarith [V2]) V3 (by linarith [V4]) E1 (by linarith [E2])
      k1 k2 k3 k4 k5 k6).2
    rw [hdf z hzy, decomp y z]
    refine this.trans (le_of_eq ?_)
    ring

/-- Helper: translating a set integral over `{z | |y-z| ≤ a}` to one over `[-a,a]`. -/
theorem c10_aux_near_translate (F : ℝ → ℝ) (y a : ℝ) :
    ∫ z in {z | |y - z| ≤ a}, F (y - z) = ∫ ρ in Icc (-a) a, F ρ := by
  have hs : MeasurableSet {z : ℝ | |y - z| ≤ a} := measurableSet_le (by fun_prop) measurable_const
  rw [← integral_indicator hs, ← integral_indicator measurableSet_Icc]
  rw [← integral_sub_left_eq_self (fun ρ => (Icc (-a) a).indicator F ρ) volume y]
  congr 1; funext z
  simp only [indicator, mem_setOf_eq, mem_Icc, ← abs_le]

/-- Blueprint: lem:c10_N3_near.  Near-field estimates (`|y| ≥ 2`, region `|y-z| ≤ |y|/2`). -/
theorem c10_N3_near (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      (∀ y : ℝ, 2 ≤ |y| →
        IntegrableOn (fun z => |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1))
          {z | |y - z| ≤ |y| / 2}) ∧
      (∀ y : ℝ, 2 ≤ y →
        (∫ z in {z | |y - z| ≤ |y| / 2},
          |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ≤
          C * ε * xNorm p γ h * jb y ^ (-γ)) ∧
      (∀ y : ℝ, y ≤ -2 →
        (∫ z in {z | |y - z| ≤ |y| / 2},
          |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ≤
          C * ε * xNorm p γ h * jb y ^ (-γ - 2 * p - 2)) ∧
      (∀ᵐ y, 2 ≤ |y| →
        IntegrableOn (fun z => |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1))
          {z | |y - z| ≤ |y| / 2}) ∧
      (∀ᵐ y, 2 ≤ y →
        (∫ z in {z | |y - z| ≤ |y| / 2},
          |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ≤
          C * ε * xNorm p γ h * jb y ^ (-γ + 1 / p)) ∧
      (∀ᵐ y, y ≤ -2 →
        (∫ z in {z | |y - z| ≤ |y| / 2},
          |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ≤
          C * ε * xNorm p γ h * jb y ^ (-γ - 2 * p - 3)) := by
  obtain ⟨hp0, -, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  have h2β := c10_aux_two_beta p hp0
  obtain ⟨Ci, hCi, hint⟩ := c10_N3_near_integrand p γ M N hp hp1 hγ hM hN
  obtain ⟨⟨C₁, C₂, hC₁, hC₂, hlam⟩, hI2, -⟩ := c10_elementary_integrals p hp0 hp1
  have hp1' : 0 < p + 1 := by linarith
  set C := (p + 1) * Ci * (C₁ + C₂ + 2 / (2 - p) + 2 / (1 - p)) with hC
  have h2p : 0 < 2 - p := by linarith
  have h1p : 0 < 1 - p := by linarith
  refine ⟨C, by positivity, fun ε hε hε1 fbar hf r hr hrN h hh => ?_⟩
  obtain ⟨V1, -, ⟨-, V3⟩⟩ := c10_N3_variation p γ M ε hp hp1 hγ hM hε.le hε1 fbar hf r hr h hh
  obtain ⟨-, -, b1, b2, b3, b4⟩ := hint ε hε hε1 fbar hf r hr hrN h hh
  set xh := xNorm p γ h
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  have hjpos := c10_aux_jb_pos
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e => (Real.rpow_pos_of_pos (hjpos y) e).le
  have hmeas : ∀ y a : ℝ, MeasurableSet {z : ℝ | |y - z| ≤ a} := fun y a =>
    measurableSet_le (by fun_prop) measurable_const
  have hrpow : ∀ x : ℝ, 0 ≤ |x| ^ (p + 1) := fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hcomm : ∀ x : ℝ, |x| ^ (p + 1) = |x| ^ (1 + p) := fun x => by rw [add_comm]
  -- integrability
  have intK : ∀ y, Integrable (fun z => |c10_N3_linearization_K p ε (fbar + r) h y z| /
      |y - z| ^ (p + 1)) := fun y => by
    refine (V1 y).abs.congr (ae_of_all _ fun z => ?_)
    simp only; rw [abs_div, abs_of_nonneg (hrpow _)]
  have intdK : ∀ᵐ y, Integrable (fun z => |c10_N3_linearization_dK p ε (fbar + r) h y z| /
      |y - z| ^ (p + 1)) := by
    filter_upwards [V3] with y hy
    refine hy.1.abs.congr (ae_of_all _ fun z => ?_)
    simp only; rw [abs_div, abs_of_nonneg (hrpow _)]
  -- `|dK| ≤ (p+1)(|∂_y K| + |K|/|y-z|)`
  have hdK : ∀ y z, |c10_N3_linearization_dK p ε (fbar + r) h y z| ≤
      (p + 1) * (|deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y| +
        |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z|) := by
    intro y z
    unfold c10_N3_linearization_dK
    have e : |(p + 1) * c10_N3_linearization_K p ε (fbar + r) h y z / (y - z)| =
        (p + 1) * (|c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z|) := by
      rw [mul_div_assoc, abs_mul, abs_of_pos hp1', abs_div]
    have := abs_sub (deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y)
      ((p + 1) * c10_N3_linearization_K p ε (fbar + r) h y z / (y - z))
    rw [e] at this
    have h0 : 0 ≤ |deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y| :=
      abs_nonneg _
    nlinarith
  have hne : ∀ y : ℝ, ∀ᵐ z ∂(volume : Measure ℝ), z ≠ y := fun y => by rw [ae_iff]; simp
  -- generic bound: `∫_near F ≤ c ∫ g(y - ·)` when `F ≤ c g(y - ·)` a.e. on near
  have gen : ∀ (y a c : ℝ) (F g : ℝ → ℝ), Integrable F → (∀ ρ, 0 ≤ g ρ) →
      IntegrableOn g (Icc (-a) a) →
      (∀ z, z ≠ y → |y - z| ≤ a → F z ≤ c * g (y - z)) →
      ∫ z in {z | |y - z| ≤ a}, F z ≤ c * ∫ ρ in Icc (-a) a, g ρ := by
    intro y a c F g hF hg hgi hFg
    rw [← c10_aux_near_translate, ← integral_const_mul]
    have hgi' : IntegrableOn (fun z => c * g (y - z)) {z | |y - z| ≤ a} := by
      have : Integrable ((Icc (-a) a).indicator g) := (integrable_indicator_iff measurableSet_Icc).2 hgi
      have h2 := (this.comp_sub_left y).const_mul c
      refine (integrable_indicator_iff (hmeas y a)).1 (h2.congr (ae_of_all _ fun z => ?_))
      simp only [indicator, mem_setOf_eq, mem_Icc, ← abs_le]
      split_ifs <;> simp
    refine setIntegral_mono_on_ae hF.integrableOn hgi' (hmeas y a) ?_
    filter_upwards [hne y] with z hz hza
    exact hFg z hz hza
  have hlamp : ∀ y : ℝ, (jb y ^ (1 / p)) ^ p = jb y := fun y => by
    rw [← Real.rpow_mul (hjpos y).le, one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hjmul : ∀ (y e e' : ℝ), e + 1 = e' → jb y ^ e * jb y = jb y ^ e' := fun y e e' he => by
    rw [mul_comm, c10_aux_jb_mul]; congr 1; linarith
  have hfin : ∀ (K₀ : ℝ) (y e : ℝ), K₀ ≤ C → 0 ≤ K₀ →
      K₀ * ε * xh * jb y ^ e ≤ C * ε * xh * jb y ^ e := fun K₀ y e hK hK0 =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK hε.le) hx) (hjnn y e)
  have hsum : 0 ≤ C₁ + C₂ + 2 / (2 - p) + 2 / (1 - p) := by positivity
  have hCiC : ∀ t, 0 ≤ t → t ≤ C₁ + C₂ + 2 / (2 - p) + 2 / (1 - p) → (p + 1) * Ci * t ≤ C :=
    fun t ht htle => mul_le_mul_of_nonneg_left htle (by positivity)
  have hCi1 : ∀ t, 0 ≤ t → t ≤ C₁ + C₂ + 2 / (2 - p) + 2 / (1 - p) → Ci * t ≤ C := fun t ht htle =>
    (show Ci * t ≤ (p + 1) * Ci * t by nlinarith [mul_nonneg hCi.le ht]).trans (hCiC t ht htle)
  -- pointwise forms
  have hpt : ∀ (y z c m : ℝ), z ≠ y → |c10_N3_linearization_K p ε (fbar + r) h y z| ≤ c * m →
      |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1) ≤
        c * (m / |y - z| ^ (1 + p)) := fun y z c m hz hb => by
    rw [← mul_div_assoc, ← hcomm]
    exact div_le_div_of_nonneg_right hb (hrpow _)
  have hsq : ∀ (y z : ℝ), z ≠ y → |y - z| ^ 2 / |y - z| ^ (1 + p) = |y - z| ^ (1 - p) := by
    intro y z hz
    have hpos : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hz))
    rw [← Real.rpow_natCast, ← Real.rpow_sub hpos]; norm_num; ring_nf
  have hlin : ∀ (y z : ℝ), z ≠ y → |y - z| / |y - z| ^ (1 + p) = |y - z| ^ (-p) := by
    intro y z hz
    have hpos : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hz))
    rw [div_eq_iff (Real.rpow_pos_of_pos hpos _).ne', ← Real.rpow_add hpos]
    ring_nf; rw [Real.rpow_one]
  have hdpt : ∀ (y z c m : ℝ), z ≠ y →
      |deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y| +
        |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ≤ c * m →
      |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1) ≤
        ((p + 1) * c) * (m / |y - z| ^ (1 + p)) := fun y z c m hz hb => by
    rw [← mul_div_assoc, ← hcomm]
    refine div_le_div_of_nonneg_right ((hdK y z).trans ?_) (hrpow _)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hp1'.le
  refine ⟨fun y hy => (intK y).integrableOn, fun y hy => ?_, fun y hy => ?_, ?_, ?_, ?_⟩
  · -- `y ≥ 2`, values
    have hlam1 : 1 ≤ jb y ^ (1 / p) := Real.one_le_rpow (c10_aux_one_le_jb y) (by positivity)
    obtain ⟨⟨gi, gv⟩, -⟩ := hlam (jb y ^ (1 / p)) hlam1
    set c := Ci * ε * xh * jb y ^ (-2 * beta p - γ + 1 / p)
    have hc0 : 0 ≤ c := by have := hjnn y (-2 * beta p - γ + 1 / p); positivity
    have step := gen y (|y| / 2) c _ (fun ρ => min 1 (jb y ^ (1 / p) * |ρ|) ^ 2 / |ρ| ^ (1 + p))
      (intK y) (fun ρ => by positivity) gi.integrableOn (fun z hz hza =>
        hpt y z c _ hz (b1 y z hy hza))
    have hle : (∫ ρ in Icc (-(|y| / 2)) (|y| / 2),
        min 1 (jb y ^ (1 / p) * |ρ|) ^ 2 / |ρ| ^ (1 + p)) ≤
        ∫ ρ, min 1 (jb y ^ (1 / p) * |ρ|) ^ 2 / |ρ| ^ (1 + p) :=
      setIntegral_le_integral gi (ae_of_all _ fun ρ => by positivity)
    rw [gv, hlamp] at hle
    calc _ ≤ _ := step
      _ ≤ c * (C₂ * jb y) := mul_le_mul_of_nonneg_left hle hc0
      _ = (Ci * C₂) * ε * xh * (jb y ^ (-2 * beta p - γ + 1 / p) * jb y) := by ring
      _ = (Ci * C₂) * ε * xh * jb y ^ (-γ) := by
          rw [hjmul y (-2 * beta p - γ + 1 / p) (-γ) (by linarith)]
      _ ≤ _ := hfin _ y _ (hCi1 C₂ hC₂.le (by linarith [div_pos two_pos h2p, div_pos two_pos h1p]))
          (by positivity)
  · -- `y ≤ -2`, values
    have ha : 0 < |y| / 2 := by have : 0 < |y| := abs_pos.2 (by linarith); positivity
    have hay : |y| / 2 ≤ jb y := by
      have := c10_aux_abs_le_jb y; have := abs_nonneg y; linarith
    set c := Ci * ε * xh * jb y ^ (-γ - p - 4)
    have hc0 : 0 ≤ c := by have := hjnn y (-γ - p - 4); positivity
    have gcont : Continuous (fun ρ : ℝ => |ρ| ^ (1 - p)) :=
      continuous_abs.rpow_const fun _ => Or.inr h1p.le
    have step := gen y (|y| / 2) c _ (fun ρ => |ρ| ^ (1 - p)) (intK y)
      (fun ρ => Real.rpow_nonneg (abs_nonneg _) _) gcont.integrableOn_Icc (fun z hz hza => by
        have := hpt y z c _ hz (b2 y z hy hza)
        rwa [hsq y z hz] at this)
    rw [(hI2 _ ha).1] at step
    have hpow : (|y| / 2) ^ (2 - p) ≤ jb y ^ (2 - p) :=
      Real.rpow_le_rpow ha.le hay h2p.le
    calc _ ≤ _ := step
      _ ≤ c * (2 * jb y ^ (2 - p) / (2 - p)) := by
          apply mul_le_mul_of_nonneg_left _ hc0
          exact div_le_div_of_nonneg_right (by linarith) h2p.le
      _ = (Ci * (2 / (2 - p))) * ε * xh * (jb y ^ (-γ - p - 4) * jb y ^ (2 - p)) := by ring
      _ = (Ci * (2 / (2 - p))) * ε * xh * jb y ^ (-γ - 2 * p - 2) := by
          rw [← Real.rpow_add (hjpos y)]; ring_nf
      _ ≤ _ := hfin _ y _ (hCi1 _ (by positivity) (by
            linarith [div_pos two_pos h1p, hC₁, hC₂])) (by positivity)
  · filter_upwards [intdK] with y hy _ using hy.integrableOn
  · -- `y ≥ 2`, derivative
    filter_upwards [intdK, b3] with y hiy hb3 hy
    have hlam1 : 1 ≤ jb y ^ (1 / p) := Real.one_le_rpow (c10_aux_one_le_jb y) (by positivity)
    obtain ⟨-, ⟨gi, gv⟩⟩ := hlam (jb y ^ (1 / p)) hlam1
    set c := Ci * ε * xh * jb y ^ (-2 * beta p - γ + 2 / p)
    have hc0 : 0 ≤ c := by have := hjnn y (-2 * beta p - γ + 2 / p); positivity
    have step := gen y (|y| / 2) ((p + 1) * c) _
      (fun ρ => min 1 (jb y ^ (1 / p) * |ρ|) / |ρ| ^ (1 + p))
      hiy (fun ρ => by positivity) gi.integrableOn (fun z hz hza =>
        hdpt y z c _ hz (hb3 z hy hza hz))
    have hle : (∫ ρ in Icc (-(|y| / 2)) (|y| / 2),
        min 1 (jb y ^ (1 / p) * |ρ|) / |ρ| ^ (1 + p)) ≤
        ∫ ρ, min 1 (jb y ^ (1 / p) * |ρ|) / |ρ| ^ (1 + p) :=
      setIntegral_le_integral gi (ae_of_all _ fun ρ => by positivity)
    rw [gv, hlamp] at hle
    calc _ ≤ _ := step
      _ ≤ (p + 1) * c * (C₁ * jb y) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ((p + 1) * Ci * C₁) * ε * xh * (jb y ^ (-2 * beta p - γ + 2 / p) * jb y) := by ring
      _ = ((p + 1) * Ci * C₁) * ε * xh * jb y ^ (-γ + 1 / p) := by
          rw [hjmul y (-2 * beta p - γ + 2 / p) (-γ + 1 / p) (by
            have : 2 / p = 2 * (1 / p) := by ring
            linarith)]
      _ ≤ _ := hfin _ y _ (hCiC C₁ hC₁.le (by linarith [div_pos two_pos h2p, div_pos two_pos h1p]))
          (by positivity)
  · -- `y ≤ -2`, derivative
    filter_upwards [intdK, b4] with y hiy hb4 hy
    have ha : 0 < |y| / 2 := by have : 0 < |y| := abs_pos.2 (by linarith); positivity
    have hay : |y| / 2 ≤ jb y := by
      have := c10_aux_abs_le_jb y; have := abs_nonneg y; linarith
    set c := Ci * ε * xh * jb y ^ (-γ - p - 4)
    have hc0 : 0 ≤ c := by have := hjnn y (-γ - p - 4); positivity
    obtain ⟨-, ⟨gi, gv⟩, -⟩ := hI2 _ ha
    have step := gen y (|y| / 2) ((p + 1) * c) _ (fun ρ => |ρ| ^ (-p)) hiy
      (fun ρ => Real.rpow_nonneg (abs_nonneg _) _) gi (fun z hz hza => by
        have := hdpt y z c _ hz (hb4 z hy hza hz)
        rwa [hlin y z hz] at this)
    rw [gv] at step
    have hpow : (|y| / 2) ^ (1 - p) ≤ jb y ^ (1 - p) :=
      Real.rpow_le_rpow ha.le hay h1p.le
    calc _ ≤ _ := step
      _ ≤ (p + 1) * c * (2 * jb y ^ (1 - p) / (1 - p)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right (by linarith) h1p.le
      _ = ((p + 1) * Ci * (2 / (1 - p))) * ε * xh * (jb y ^ (-γ - p - 4) * jb y ^ (1 - p)) := by
          ring
      _ = ((p + 1) * Ci * (2 / (1 - p))) * ε * xh * jb y ^ (-γ - 2 * p - 3) := by
          rw [← Real.rpow_add (hjpos y)]; ring_nf
      _ ≤ _ := hfin _ y _ (hCiC _ (by positivity) (by
            linarith [div_pos two_pos h2p, hC₁, hC₂])) (by positivity)

/-! ### Far field for `y ≥ 2` (continued) -/

/-- Helper: `y' ↦ S_W(y',z)` near `y > 0`. -/
theorem c10_aux_SW_hasDeriv {y z : ℝ} (hy : 0 < y) (hyz : y ≠ z) :
    HasDerivAt (fun y' => c01_secant corner y' z) (-(c01_secant corner y z) / (y - z)) y ∧
    c01_secant corner y z = -corner z / (y - z) ∧ |c01_secant corner y z| ≤ 1 := by
  have hW : ∀ y' : ℝ, 0 < y' → corner y' = 0 := fun y' h => by
    simp [corner]; linarith
  have e : ∀ y', 0 < y' → y' ≠ z → c01_secant corner y' z = -corner z / (y' - z) := fun y' h1 h2 => by
    rw [c01_secant, if_neg h2, hW y' h1]; ring
  have hyz' : y - z ≠ 0 := sub_ne_zero.2 hyz
  refine ⟨?_, e y hy hyz, ?_⟩
  · have hd := (hasDerivAt_const y (-corner z)).div ((hasDerivAt_id y).sub_const z) hyz'
    have hev : (fun y' => c01_secant corner y' z) =ᶠ[nhds y] fun y' => -corner z / (id y' - z) := by
      filter_upwards [Ioi_mem_nhds hy, isOpen_compl_singleton.mem_nhds hyz] with y' h1 h2
      exact e y' h1 h2
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [e y hy hyz]; simp only [id]; field_simp; ring
  · rw [e y hy hyz, abs_div, abs_neg, div_le_one (abs_pos.2 hyz')]
    simp only [corner]
    rcases le_or_gt 0 z with hz | hz
    · rw [max_eq_right (by linarith)]; simp
    · rw [max_eq_left (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith

/-- Blueprint: lem:c10_far_subtraction (helper).  The subtracted integrand
`K̃(y,z) = K_{f,h}(y,z) - ∂₁Γ_ε(0, S_W(y,z)) h'(y)`. -/
def c10_far_subtraction_Ktilde (p ε : ℝ) (f h : ℝ → ℝ) (y z : ℝ) : ℝ :=
  c10_N3_linearization_K p ε f h y z -
    c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) * deriv h y

/-- Helper: the model kernel `G(y,z) = ∂₁Γ_ε(0,S_W(y,z)) / |y-z|^α` for `y > 1`: its integral is
`c_ε y^{-p}` (lem:analysis_coefficient) and it vanishes for `z ≥ 0`. -/
theorem c10_aux_model_kernel (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∀ y : ℝ, 0 < y → ∀ z : ℝ, 0 ≤ z →
      c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) / |y - z| ^ (p + 1) = 0) ∧
    (∀ y : ℝ, 1 < y →
      Integrable (fun z => c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) / |y - z| ^ (p + 1)) ∧
      (∫ z, c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) / |y - z| ^ (p + 1)) =
        c_eps p ε * y ^ (-p)) := by
  obtain ⟨Ck, hCk, hk⟩ := c10_aux_kernel_bounds p 1 hp hp1 le_rfl
  have hd0 : c10_N_pieces_Gamma_d1 p ε 0 0 = 0 := by
    obtain ⟨-, -, -, -, -, b2v, bs, -, -⟩ := hk ε hε hε1 0 0 (by simp) (by simp)
    simp only [sub_self, abs_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at b2v bs
    have := abs_nonpos_iff.1 b2v
    have := abs_nonpos_iff.1 bs; linarith
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · by_cases hzy : z = y
    · subst hzy; rw [sub_self, abs_zero, Real.zero_rpow (by linarith), div_zero]
    · have hc : corner z = 0 := by simp [corner]; linarith
      rw [(c10_aux_SW_hasDeriv hy (Ne.symm hzy)).2.1, hc, neg_zero, zero_div, hd0, zero_div]
  · have hW : deriv corner y = 0 := by
      have hev : corner =ᶠ[nhds y] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < y by linarith)] with x hx
        simp [corner]; linarith [show (0 : ℝ) < x from hx]
      rw [hev.deriv_eq]; simp
    obtain ⟨hi, hv⟩ := (analysis_coefficient p ε hp hp1 hε hε1).1 y hy
    rw [hW] at hi hv
    exact ⟨hi, hv⟩

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_far_subtraction.  Secant of the corner `W` for `y ≥ 2`; the model
coefficient `b_ε(y) = ∫_{z<0} ∂₁Γ_ε(0,S_W(y,z)) |y-z|^{-α} dz = ∫_{|y-z| ≥ y/2} (same)`; and the
resulting subtraction identities for the far-field integrals. -/
theorem c10_far_subtraction (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∀ y : ℝ, 2 ≤ y → ∀ z : ℝ, z < 0 →
        c01_secant corner y z = z / (y - z) ∧ c01_secant corner y z ∈ Ioo (-1 : ℝ) 0 ∧
        deriv (fun y' => c01_secant corner y' z) y = -(c01_secant corner y z / (y - z))) ∧
      (∀ y : ℝ, 2 ≤ y → ∀ z : ℝ, 0 ≤ z → z ≠ y → c01_secant corner y z = 0) ∧
      (∀ y : ℝ, 2 ≤ y →
        b_eps p ε y = ∫ z in Iio (0 : ℝ),
          c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) / |y - z| ^ (p + 1) ∧
        b_eps p ε y = ∫ z in {z | y / 2 ≤ |y - z|},
          c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) / |y - z| ^ (p + 1)) ∧
      ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
        (∀ y : ℝ, 2 ≤ y →
          (∫ z in {z | y / 2 ≤ |y - z|},
              c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
            b_eps p ε y * deriv h y =
          ∫ z in {z | y / 2 ≤ |y - z|},
            c10_far_subtraction_Ktilde p ε (fbar + r) h y z / |y - z| ^ (p + 1)) ∧
        (∀ᵐ y, 2 < y →
          (∫ z in {z | y / 2 ≤ |y - z|},
              c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
            deriv (fun x => b_eps p ε x * deriv h x) y =
          ∫ z in {z | y / 2 ≤ |y - z|}, (1 / |y - z| ^ (p + 1)) *
            (deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y -
              (p + 1) / (y - z) * c10_far_subtraction_Ktilde p ε (fbar + r) h y z)) := by
  intro ε hε hε1
  have hp0 : 0 < p := by linarith
  obtain ⟨hG0, hGi⟩ := c10_aux_model_kernel p ε hp0 hp1 hε.le hε1
  set G : ℝ → ℝ → ℝ := fun y z =>
    c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) / |y - z| ^ (p + 1) with hGdef
  have hfar : ∀ y : ℝ, 0 < y → MeasurableSet {z : ℝ | y / 2 ≤ |y - z|} := fun y _ =>
    measurableSet_le measurable_const (by fun_prop)
  have hfar0 : ∀ y : ℝ, 0 < y → ∀ z : ℝ, z ∉ {z : ℝ | y / 2 ≤ |y - z|} → 0 ≤ z := by
    intro y hy z hz
    simp only [mem_setOf_eq, not_le] at hz
    have := (abs_lt.1 hz).2; linarith
  have hb : ∀ y : ℝ, 2 ≤ y → b_eps p ε y = c_eps p ε * y ^ (-p) := by
    intro y hy
    simp only [b_eps, c08_phi_b]
    rw [if_pos (by linarith)]
    have : chiPlus y = 1 := by
      unfold chiPlus; exact Real.smoothTransition.one_of_one_le (by linarith)
    rw [this, mul_one]
  have partC : ∀ y : ℝ, 2 ≤ y →
      b_eps p ε y = (∫ z in Iio (0 : ℝ), G y z) ∧ b_eps p ε y = ∫ z in {z | y / 2 ≤ |y - z|}, G y z := by
    intro y hy
    obtain ⟨-, hv⟩ := hGi y (by linarith)
    rw [hb y hy, ← hv]
    constructor
    · refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
      exact hG0 y (by linarith) z (not_lt.1 hz)
    · refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
      exact hG0 y (by linarith) z (hfar0 y (by linarith) z hz)
  refine ⟨fun y hy z hz => ?_, fun y hy z hz hzy => ?_, partC, ?_⟩
  · have hyz : y ≠ z := by intro h; linarith
    obtain ⟨hd, he, -⟩ := c10_aux_SW_hasDeriv (show 0 < y by linarith) hyz
    have hc : corner z = -z := by simp [corner]; linarith
    have hpos : 0 < y - z := by linarith
    refine ⟨by rw [he, hc]; ring, ?_, by rw [hd.deriv, neg_div]⟩
    rw [he, hc, neg_neg]
    constructor
    · rw [lt_div_iff₀ hpos]; linarith
    · exact div_neg_of_neg_of_pos hz hpos
  · obtain ⟨-, he, -⟩ := c10_aux_SW_hasDeriv (show 0 < y by linarith) (Ne.symm hzy)
    have hc : corner z = 0 := by simp [corner]; linarith
    rw [he, hc, neg_zero, zero_div]
  intro fbar hf r hr hrN h hh
  have NV := c10_N3_variation p γ M ε hp hp1 hγ hM hε.le hε1 fbar hf r hr h hh
  refine ⟨fun y hy => ?_, ?_⟩
  · have hiK := (NV.1 y).integrableOn (s := {z | y / 2 ≤ |y - z|})
    have hiG := ((hGi y (by linarith)).1.integrableOn (s := {z | y / 2 ≤ |y - z|})).mul_const
      (deriv h y)
    have e : ∀ z, c10_far_subtraction_Ktilde p ε (fbar + r) h y z / |y - z| ^ (p + 1) =
        c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1) - G y z * deriv h y := by
      intro z; simp only [c10_far_subtraction_Ktilde, hGdef]; ring
    simp_rw [e]
    rw [integral_sub hiK hiG, integral_mul_const, ← (partC y hy).2]
  · -- derivative identity
    have hfA : fbar ∈ c01_admissible_class :=
      c10_aux_C2_admissible_class hf.1 (c10_aux_admissible_deriv_bdd p M hp0 hf)
    have hrA := c10_aux_X_admissible_class p γ hp hp1 hγ hr
    obtain ⟨hfW, -, -, -⟩ := c10_aux_lin_W2 (f := fbar) (h := r) ⟨hfA.1, hfA.2.2⟩ ⟨hrA.1, hrA.2.2⟩ 1
    rw [one_smul] at hfW
    obtain ⟨Ck, hCk, hk⟩ := c10_aux_kernel_bounds p 1 hp0 hp1 le_rfl
    have hcor : Continuous corner := by unfold corner; fun_prop
    obtain ⟨c1, c2, -, c12, -⟩ := c10_aux_d_cont p ε hp0 hp1 hε.le 0
    set Gd : ℝ → ℝ → ℝ := fun y z =>
      (c10_N_pieces_Gamma_d12 p ε 0 (c01_secant corner y z) * (-(c01_secant corner y z) / (y - z)) -
        (p + 1) * c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) / (y - z)) /
          |y - z| ^ (p + 1) with hGd
    have hd00 : c10_N_pieces_Gamma_d1 p ε 0 0 = 0 := by
      obtain ⟨-, -, -, -, -, b2v, bs, -, -⟩ := hk ε hε.le hε1 0 0 (by simp) (by simp)
      simp only [sub_self, abs_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] at b2v bs
      have := abs_nonpos_iff.1 b2v
      have := abs_nonpos_iff.1 bs; linarith
    -- derivative of the model kernel in `y`
    have hGder : ∀ y z : ℝ, 0 < y → z ≠ y → HasDerivAt (fun y' => G y' z) (Gd y z) y := by
      intro y z hy hzy
      obtain ⟨hS, -, -⟩ := c10_aux_SW_hasDeriv hy (Ne.symm hzy)
      have h1 := (c10_aux_d_chain p ε hp0 hp1 hε.le (hasDerivAt_const y (0 : ℝ)) hS).1
      have h2 := c10_aux_div_pow_hasDeriv (α := p + 1) h1 (Ne.symm hzy)
      refine h2.congr_deriv ?_
      simp only [hGd]; ring
    have hGd0 : ∀ y z : ℝ, 0 < y → 0 ≤ z → Gd y z = 0 := by
      intro y z hy hz
      by_cases hzy : z = y
      · subst hzy; simp only [hGd]; rw [sub_self, abs_zero, Real.zero_rpow (by linarith), div_zero]
      · obtain ⟨-, he, -⟩ := c10_aux_SW_hasDeriv hy (Ne.symm hzy)
        have hc : corner z = 0 := by simp [corner]; linarith
        simp only [hGd]; rw [he, hc, neg_zero, zero_div, hd00]; ring
    have hGm : ∀ y : ℝ, Measurable (G y) := fun y =>
      ((c1.measurable.comp (c10_aux_secant_meas hcor y)).div (by fun_prop))
    have hGdm : ∀ y : ℝ, Measurable (Gd y) := fun y => by
      have hs := c10_aux_secant_meas hcor y
      exact (((c12.measurable.comp hs).mul (hs.neg.div (by fun_prop))).sub
        ((measurable_const.mul (c1.measurable.comp hs)).div (by fun_prop))).div (by fun_prop)
    -- `b_ε` is differentiable on `(2,∞)` with derivative `∫ Gd`
    have hbder : ∀ y : ℝ, 2 < y → HasDerivAt (b_eps p ε) (∫ z, Gd y z) y ∧ Integrable (Gd y) := by
      intro y hy
      set δ := (y - 2) / 2
      have hδ : 0 < δ := by simp only [δ]; linarith
      have hball : ∀ y' ∈ Metric.ball y δ, 2 < y' := fun y' hy' => by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy'; simp only [δ] at hy'; linarith
      have hbound : ∀ y' : ℝ, 2 < y' → ∀ z : ℝ, z < 0 →
          |Gd y' z| ≤ 3 * Ck * ε * jb z ^ (-(p + 2)) := by
        intro y' hy' z hz
        have hzy : y' ≠ z := by intro h; linarith
        obtain ⟨-, he, hS1⟩ := c10_aux_SW_hasDeriv (show 0 < y' by linarith) hzy
        obtain ⟨b1, -, -, b12, -⟩ := hk ε hε.le hε1 0 (c01_secant corner y' z) (by simp) hS1
        have hw : y' - z = |y' - z| := (abs_of_pos (by linarith)).symm
        have hwj : jb z ≤ |y' - z| := by
          have := c10_aux_abs_le_jb z
          have hj : jb z ≤ 1 + |z| := by
            unfold jb; rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_abs z, abs_nonneg z]
          rw [← hw, abs_of_neg hz] at *; linarith
        have hw1 : 1 ≤ |y' - z| := (c10_aux_one_le_jb z).trans hwj
        have hw0 : 0 < |y' - z| := by linarith
        simp only [hGd]
        rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hw0 _), div_le_iff₀ (Real.rpow_pos_of_pos hw0 _)]
        have hnum : |c10_N_pieces_Gamma_d12 p ε 0 (c01_secant corner y' z) *
            (-(c01_secant corner y' z) / (y' - z)) -
            (p + 1) * c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y' z) / (y' - z)| ≤
            3 * Ck * ε / |y' - z| := by
          have t1 : |c10_N_pieces_Gamma_d12 p ε 0 (c01_secant corner y' z) *
              (-(c01_secant corner y' z) / (y' - z))| ≤ Ck * ε * (1 / |y' - z|) := by
            rw [abs_mul, abs_div, abs_neg]
            exact mul_le_mul b12 (div_le_div_of_nonneg_right hS1 hw0.le) (by positivity)
              (by positivity)
          have t2 : |(p + 1) * c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y' z) / (y' - z)| ≤
              2 * (Ck * ε) / |y' - z| := by
            rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < p + 1)]
            exact div_le_div_of_nonneg_right (mul_le_mul (by linarith) b1 (abs_nonneg _)
              (by norm_num)) hw0.le
          calc _ ≤ _ := abs_sub _ _
            _ ≤ Ck * ε * (1 / |y' - z|) + 2 * (Ck * ε) / |y' - z| := add_le_add t1 t2
            _ = 3 * Ck * ε / |y' - z| := by ring
        refine hnum.trans ?_
        rw [div_le_iff₀ hw0]
        have hpow : jb z ^ (-(p + 2)) * |y' - z| ^ (p + 1) * |y' - z| ≥ 1 := by
          rw [mul_assoc, ← Real.rpow_add_one hw0.ne', show p + 1 + 1 = p + 2 by ring,
            Real.rpow_neg (c10_aux_jb_pos z).le, inv_mul_eq_div, ge_iff_le,
            one_le_div (Real.rpow_pos_of_pos (c10_aux_jb_pos z) _)]
          exact Real.rpow_le_rpow (c10_aux_jb_pos z).le hwj (by linarith)
        have h3 : 0 ≤ 3 * Ck * ε := by positivity
        nlinarith
      have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Iio 0))
        (F := fun y' z => G y' z) (F' := fun y' z => Gd y' z) (x₀ := y)
        (bound := fun z => 3 * Ck * ε * jb z ^ (-(p + 2)))
        (Metric.ball_mem_nhds y hδ) (Eventually.of_forall fun y' => (hGm y').aestronglyMeasurable)
        ((hGi y (by linarith)).1.integrableOn) (hGdm y).aestronglyMeasurable
        (by
          rw [ae_restrict_iff' measurableSet_Iio]
          exact Eventually.of_forall fun z hz y' hy' => by
            rw [Real.norm_eq_abs]; exact hbound y' (hball y' hy') z hz)
        ((c10_aux_jb_integrable (γ := p + 2) (by linarith)).const_mul _).integrableOn
        (by
          rw [ae_restrict_iff' measurableSet_Iio]
          exact Eventually.of_forall fun z (hz : z < 0) y' hy' =>
            hGder y' z (by linarith [hball y' hy']) (by intro h; linarith [hball y' hy']))
      have hint : Integrable (Gd y) :=
        IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Iio 0) key.1
          fun z hz => hGd0 y z (by linarith) (not_lt.1 hz)
      have hev : (fun y' => ∫ z in Iio (0 : ℝ), G y' z) =ᶠ[nhds y] b_eps p ε := by
        filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < y from hy)] with y' hy'
        exact ((partC y' (le_of_lt hy')).1).symm
      refine ⟨(key.2.congr_of_eventuallyEq hev.symm).congr_deriv ?_, hint⟩
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        hGd0 y z (by linarith) (not_lt.1 hz)
    filter_upwards [NV.2.2.2, c10_aux_ae_differentiableAt hfW.2, c10_aux_ae_differentiableAt hh.1.2]
      with y hNVy hf' hh' hy
    obtain ⟨hdKi, -⟩ := hNVy
    obtain ⟨hbd, hGdi⟩ := hbder y hy
    have hy0 : 0 < y := by linarith
    have hFm := hfar y hy0
    -- derivative of `b_ε h'`
    have hbh : deriv (fun x => b_eps p ε x * deriv h x) y =
        (∫ z, Gd y z) * deriv h y + b_eps p ε y * deriv (deriv h) y :=
      (hbd.mul hh'.hasDerivAt).deriv
    -- the integrand identity on the far set
    have hzid : ∀ z ∈ {z : ℝ | y / 2 ≤ |y - z|}, (1 / |y - z| ^ (p + 1)) *
        (deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y -
          (p + 1) / (y - z) * c10_far_subtraction_Ktilde p ε (fbar + r) h y z) =
        c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1) -
          deriv h y * Gd y z - deriv (deriv h) y * G y z := by
      intro z hz
      have hzy : z ≠ y := by
        intro h0; rw [h0, mem_setOf_eq, sub_self, abs_zero] at hz; linarith
      have hyz : y ≠ z := Ne.symm hzy
      obtain ⟨hS, -, -⟩ := c10_aux_SW_hasDeriv hy0 hyz
      have hK := c10_aux_K_hasDeriv p ε hp0 hp1 hε.le hfW hh.1 hyz hf' hh'
      have hD1 := (c10_aux_d_chain p ε hp0 hp1 hε.le (hasDerivAt_const y (0 : ℝ)) hS).1
      have hKt : HasDerivAt (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z)
          (c10_aux_DK p ε (fbar + r) h y z -
            ((c10_N_pieces_Gamma_d11 p ε 0 (c01_secant corner y z) * 0 +
              c10_N_pieces_Gamma_d12 p ε 0 (c01_secant corner y z) *
                (-(c01_secant corner y z) / (y - z))) * deriv h y +
              c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) * deriv (deriv h) y)) y :=
        hK.sub (hD1.mul hh'.hasDerivAt)
      rw [hKt.deriv]
      have hdK : c10_N3_linearization_dK p ε (fbar + r) h y z =
          c10_aux_DK p ε (fbar + r) h y z -
            (p + 1) * c10_N3_linearization_K p ε (fbar + r) h y z / (y - z) := by
        simp only [c10_N3_linearization_dK, hK.deriv]
      rw [hdK]
      have hw : y - z ≠ 0 := sub_ne_zero.2 hyz
      have hW : |y - z| ^ (p + 1) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.2 hw) _).ne'
      simp only [hGd, hGdef, c10_far_subtraction_Ktilde]
      field_simp
      ring
    rw [setIntegral_congr_fun hFm hzid, hbh]
    have i1 : IntegrableOn (fun z => c10_N3_linearization_dK p ε (fbar + r) h y z /
        |y - z| ^ (p + 1)) {z | y / 2 ≤ |y - z|} := hdKi.integrableOn
    have i2 : IntegrableOn (fun z => deriv h y * Gd y z) {z | y / 2 ≤ |y - z|} :=
      (hGdi.const_mul _).integrableOn
    have i3 : IntegrableOn (fun z => deriv (deriv h) y * G y z) {z | y / 2 ≤ |y - z|} :=
      ((hGi y (by linarith)).1.const_mul _).integrableOn
    have i12 : IntegrableOn (fun z => c10_N3_linearization_dK p ε (fbar + r) h y z /
        |y - z| ^ (p + 1) - deriv h y * Gd y z) {z | y / 2 ≤ |y - z|} := i1.sub i2
    rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
      ← (partC y hy.le).2]
    have hGdfar : (∫ z in {z | y / 2 ≤ |y - z|}, Gd y z) = ∫ z, Gd y z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hGd0 y z hy0 (hfar0 y hy0 z hz)
    rw [hGdfar]; ring

/-- Blueprint: lem:c10_far_plus_integrand.  Far-field integrand bounds for `y ≥ 2`,
`|y-z| ≥ y/2` (the last one for a.e. `y`). -/
theorem c10_far_plus_integrand (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      (∀ y z : ℝ, 2 ≤ y → y / 2 ≤ |y - z| →
        |c10_N_pieces_Gamma_d1 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) -
            c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z)| ≤ C * ε * jb y ^ (-1 : ℝ) ∧
        |c10_far_subtraction_Ktilde p ε (fbar + r) h y z| ≤
          C * ε * xNorm p γ h * (jb y ^ (-γ + 1 / p - 1) +
            (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|)) ∧
      (∀ᵐ y, ∀ z : ℝ, 2 ≤ y → y / 2 ≤ |y - z| →
        |deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y| +
            |c10_far_subtraction_Ktilde p ε (fbar + r) h y z| / |y - z| ≤
          C * ε * xNorm p γ h * (jb y ^ (-γ + 2 / p - 1) +
            jb y ^ (1 / p - 1) * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|))) := by
  obtain ⟨hp0, hγp, hγ1, -, hγ2⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  have hβ1 : 1 < beta p := by unfold beta; rw [lt_div_iff₀ (by linarith)]; linarith
  obtain ⟨CP, hCP, hPC⟩ := c10_profile_consequences p γ M N hp hp1 hγ hM hN
  obtain ⟨Cg, hCg, hKb⟩ := c10_aux_kernel_bounds p (max CP 1) hp0 hp1 (le_max_right _ _)
  obtain ⟨CL, hCL, hLip⟩ := c10_aux_d1_lip p (max CP 1) hp0 hp1 (le_max_right _ _)
  have hjpos := c10_aux_jb_pos
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e => (Real.rpow_pos_of_pos (hjpos y) e).le
  have hjm := c10_aux_jb_rpow_mono
  have hjadd : ∀ y a b : ℝ, jb y ^ a * jb y ^ b = jb y ^ (a + b) := fun y a b =>
    (Real.rpow_add (hjpos y) a b).symm
  have Ea : ∀ y, jb y ^ (-beta p) ≤ jb y ^ (-1 : ℝ) := fun y => hjm y (by linarith)
  have Eb : ∀ y, jb y ^ (-beta p + 1 / p) ≤ jb y ^ (-1 : ℝ) * jb y ^ (1 / p) := fun y => by
    rw [hjadd]; exact hjm y (by linarith)
  have Ec : ∀ y : ℝ, jb y ^ (-γ + 1 / p) = jb y ^ (-γ) * jb y ^ (1 / p) := fun y => by
    rw [hjadd]
  have Ed : ∀ y : ℝ, jb y ^ (-γ + 2 / p) = jb y ^ (-γ) * jb y ^ (1 / p) * jb y ^ (1 / p) :=
    fun y => by rw [hjadd, hjadd]; congr 1; ring
  have Ee : ∀ y : ℝ, jb y ^ (-1 : ℝ) * jb y ^ (-γ) * jb y ^ (1 / p) = jb y ^ (-γ + 1 / p - 1) :=
    fun y => by rw [hjadd, hjadd]; congr 1; ring
  have Ef : ∀ y : ℝ, jb y ^ (-γ) * jb y ^ (1 / p) * jb y ^ (1 / p) * jb y ^ (-1 : ℝ) =
      jb y ^ (-γ + 2 / p - 1) := fun y => by rw [hjadd, hjadd, hjadd]; congr 1; ring
  have Eg : ∀ y : ℝ, jb y ^ (-1 : ℝ) * jb y ^ (1 / p) = jb y ^ (1 / p - 1) := fun y => by
    rw [hjadd]; congr 1; ring
  have EJ1 : ∀ y, jb y ^ (-1 : ℝ) ≤ 1 := fun y => c10_aux_jb_rpow_le_one y (by norm_num)
  have EP1 : ∀ y, 1 ≤ jb y ^ (1 / p) := fun y =>
    Real.one_le_rpow (c10_aux_one_le_jb y) (by positivity)
  set C := 45 * CL * CP + Cg * (9 * CP + 9) + 1 with hC
  refine ⟨C, by positivity, fun ε hε hε1 fbar hf r hr hrN h hh => ?_⟩
  obtain ⟨I1, P2a, P2b, -, -, -⟩ := hPC fbar hf r hr hrN
  obtain ⟨hfd, -, -, hfW⟩ := I1 (fbar + r) (Set.mem_insert _ _)
  obtain ⟨hv, hd0, -, hdd0, -⟩ := c10_aux_X_simple p γ hh
  have hfA := c10_aux_C2_admissible_class hf.1 (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have hW : W2inftyLoc (fbar + r) := by
    refine ⟨hfA.1.add hr.1.1, ?_⟩
    have : deriv (fbar + r) = deriv fbar + deriv r := funext fun x =>
      deriv_add (hfA.1.differentiable (by norm_num) x) (hr.1.1.differentiable (by norm_num) x)
    rw [this]; exact hfA.2.2.add hr.1.2
  set xh := xNorm p γ h with hxh
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  have core : ∀ y z : ℝ, 2 ≤ y → y / 2 ≤ |y - z| →
      |c10_N_pieces_Gamma_d1 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) -
          c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z)| ≤ CL * ε * (9 * CP) * jb y ^ (-1 : ℝ) ∧
      |c10_far_subtraction_Ktilde p ε (fbar + r) h y z| ≤
        CL * ε * (9 * CP) * xh * (jb y ^ (-1 : ℝ) * jb y ^ (-γ) * jb y ^ (1 / p)) +
          Cg * ε * xh * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|) ∧
      (DifferentiableAt ℝ (deriv (fbar + r)) y → DifferentiableAt ℝ (deriv h) y →
        |deriv (deriv (fbar + r)) y| ≤ CP * jb y ^ (-beta p + 1 / p) →
        |deriv (deriv h) y| ≤ xh * jb y ^ (-γ + 2 / p) →
        |deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y| +
          |c10_far_subtraction_Ktilde p ε (fbar + r) h y z| * (1 / |y - z|) ≤
          (5 * (CL * ε * (9 * CP)) + Cg * ε * (9 * CP + 8)) * xh *
            (jb y ^ (-γ) * jb y ^ (1 / p) * jb y ^ (1 / p) * jb y ^ (-1 : ℝ) +
              jb y ^ (-1 : ℝ) * jb y ^ (1 / p) * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|))) := by
    intro y z hy hz
    have ht : 0 < |y - z| := by linarith
    have hyz : y ≠ z := fun e => by rw [e, sub_self, abs_zero] at ht; exact lt_irrefl _ ht
    have hinv : 1 / |y - z| ≤ 4 * jb y ^ (-1 : ℝ) := by
      have hj := c10_aux_jb_le_two_abs (show 1 ≤ |y| by rw [abs_of_pos (by linarith)]; linarith)
      rw [abs_of_pos (by linarith)] at hj
      rw [Real.rpow_neg_one, div_le_iff₀ ht]
      have : jb y ≤ 4 * |y - z| := by linarith
      calc (1 : ℝ) = (jb y)⁻¹ * jb y := (inv_mul_cancel₀ (hjpos y).ne').symm
        _ ≤ (jb y)⁻¹ * (4 * |y - z|) := mul_le_mul_of_nonneg_left this (inv_pos.2 (hjpos y)).le
        _ = _ := by ring
    obtain ⟨-, -, sfD, -, sf5⟩ := c10_secant_identities (fbar + r) hW y z hyz
    obtain ⟨-, -, shD, -, -⟩ := c10_secant_identities h hh.1 y z hyz
    obtain ⟨sWD, -, sW1⟩ := c10_aux_SW_hasDeriv (show 0 < y by linarith) hyz
    have hR1 : CP ≤ max CP 1 := le_max_left _ _
    have hu : |deriv (fbar + r) y| ≤ CP * jb y ^ (-1 : ℝ) :=
      (P2a y (by linarith)).trans (mul_le_mul_of_nonneg_left (Ea y) hCP.le)
    have hvC : |c01_secant (fbar + r) y z| ≤ CP := ((sf5 CP hfd).2).trans (min_le_left _ _)
    have hvw : |c01_secant (fbar + r) y z - c01_secant corner y z| ≤ 8 * CP * jb y ^ (-1 : ℝ) := by
      rw [c01_secant, c01_secant, if_neg hyz, if_neg hyz, ← sub_div, abs_div]
      have h1 : |(fbar + r) y - (fbar + r) z - (corner y - corner z)| ≤ 2 * CP := by
        have a1 := (hfW y).trans (mul_le_of_le_one_right hCP.le
          (c10_aux_jb_rpow_le_one y (by linarith)))
        have a2 := (hfW z).trans (mul_le_of_le_one_right hCP.le
          (c10_aux_jb_rpow_le_one z (by linarith)))
        have := abs_sub ((fbar + r) y - corner y) ((fbar + r) z - corner z)
        calc _ = |((fbar + r) y - corner y) - ((fbar + r) z - corner z)| := by ring_nf
          _ ≤ _ := this
          _ ≤ _ := by linarith
      rw [div_eq_mul_one_div]
      calc _ ≤ 2 * CP * (4 * jb y ^ (-1 : ℝ)) :=
            mul_le_mul h1 hinv (by positivity) (by positivity)
        _ = _ := by ring
    have hlip := hLip ε hε.le hε1 _ _ 0 _ ((hfd y).trans hR1) (hvC.trans hR1) (by simp)
      (sW1.trans (le_max_right _ _))
    have hdiff : |c10_N_pieces_Gamma_d1 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) -
        c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z)| ≤ CL * ε * (9 * CP) * jb y ^ (-1 : ℝ) := by
      refine hlip.trans ?_
      rw [sub_zero]
      calc CL * ε * (|deriv (fbar + r) y| + |c01_secant (fbar + r) y z - c01_secant corner y z|)
          ≤ CL * ε * (CP * jb y ^ (-1 : ℝ) + 8 * CP * jb y ^ (-1 : ℝ)) :=
            mul_le_mul_of_nonneg_left (add_le_add hu hvw) (by positivity)
        _ = _ := by ring
    obtain ⟨-, b2, b11, b12, b22, -⟩ := hKb ε hε.le hε1 _ _ ((hfd y).trans hR1) (hvC.trans hR1)
    obtain ⟨-, -, -, e12, -, -⟩ := hKb ε hε.le hε1 0 (c01_secant corner y z) (by simp)
      (sW1.trans (le_max_right _ _))
    have hQ0 : 0 ≤ (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z| := by
      have := hjnn y (-γ); have := hjnn z (-γ); positivity
    have hSh : |c01_secant h y z| ≤ xh * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|) := by
      rw [c01_secant, if_neg hyz, abs_div, ← mul_div_assoc, div_le_div_iff_of_pos_right ht]
      calc |h y - h z| ≤ |h y| + |h z| := abs_sub _ _
        _ ≤ xh * jb y ^ (-γ) + xh * jb z ^ (-γ) := add_le_add (hv y) (hv z)
        _ = _ := by ring
    have hh1 : |deriv h y| ≤ xh * (jb y ^ (-γ) * jb y ^ (1 / p)) := by
      rw [← Ec]; exact hd0 y (by linarith)
    have hK : c10_far_subtraction_Ktilde p ε (fbar + r) h y z =
        (c10_N_pieces_Gamma_d1 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) -
          c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z)) * deriv h y +
        c10_N_pieces_Gamma_d2 p ε (deriv (fbar + r) y) (c01_secant (fbar + r) y z) *
          c01_secant h y z := by
      unfold c10_far_subtraction_Ktilde c10_N3_linearization_K; ring
    have alg := fun (a b h2 S' : ℝ) (ha : |a| ≤ CP * (jb y ^ (-1 : ℝ) * jb y ^ (1 / p)))
        (hb : |b| ≤ 8 * CP * jb y ^ (-1 : ℝ))
        (hbW : |-(c01_secant corner y z) / (y - z)| ≤ 4 * jb y ^ (-1 : ℝ))
        (hh2 : |h2| ≤ xh * (jb y ^ (-γ) * jb y ^ (1 / p) * jb y ^ (1 / p)))
        (hS' : |S'| ≤ 4 * jb y ^ (-1 : ℝ) * (|deriv h y| + |c01_secant h y z|)) =>
      c10_aux_farp_alg (a := a) (b := b) (h2 := h2) (S' := S') (t := 1 / |y - z|)
        (mul_nonneg hCg.le hε.le) (by positivity) hCP.le hx (hjnn y _) (EJ1 y) (EP1 y)
        (hjnn y _) hQ0 hdiff b2 b11 b12 b22 e12 ha hb hbW hh1 hh2 hSh hS' (by positivity) hinv
    have hbW : |-(c01_secant corner y z) / (y - z)| ≤ 4 * jb y ^ (-1 : ℝ) := by
      rw [abs_div, abs_neg, div_eq_mul_one_div]
      calc _ ≤ 1 * (4 * jb y ^ (-1 : ℝ)) := mul_le_mul sW1 hinv (by positivity) zero_le_one
        _ = _ := one_mul _
    refine ⟨hdiff, ?_, fun hf2 hh2 hf2b hh2b => ?_⟩
    · rw [hK]
      have hj1 := hjnn y (-1 : ℝ); have hj2 := hjnn y (1 / p); have hj3 := hjnn y (-γ)
      have := (alg 0 0 0 0 (by simp only [abs_zero]; exact mul_nonneg hCP.le (mul_nonneg hj1 hj2))
        (by simp only [abs_zero]; exact mul_nonneg (by linarith) hj1) hbW
        (by simp only [abs_zero]; exact mul_nonneg hx (mul_nonneg (mul_nonneg hj3 hj2) hj2))
        (by simp only [abs_zero]; exact mul_nonneg (mul_nonneg (by norm_num) hj1) (add_nonneg (abs_nonneg _) (abs_nonneg _)))).1
      calc _ ≤ _ := this
        _ = _ := by ring
    · have hKd := c10_aux_K_hasDeriv p ε hp0 hp1 hε.le hW hh.1 hyz hf2 hh2
      have hc0 := (c10_aux_d_chain p ε hp0 hp1 hε.le (hasDerivAt_const y (0 : ℝ)) sWD).1
      have hKt : HasDerivAt (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z)
          (c10_aux_DK p ε (fbar + r) h y z -
            ((c10_N_pieces_Gamma_d11 p ε 0 (c01_secant corner y z) * 0 +
              c10_N_pieces_Gamma_d12 p ε 0 (c01_secant corner y z) *
                (-(c01_secant corner y z) / (y - z))) * deriv h y +
             c10_N_pieces_Gamma_d1 p ε 0 (c01_secant corner y z) * deriv (deriv h) y)) y :=
        hKd.sub (hc0.mul hh2.hasDerivAt)
      rw [hKt.deriv]
      have ha : |deriv (deriv (fbar + r)) y| ≤ CP * (jb y ^ (-1 : ℝ) * jb y ^ (1 / p)) :=
        hf2b.trans (mul_le_mul_of_nonneg_left (Eb y) hCP.le)
      have hb : |(deriv (fbar + r) y - c01_secant (fbar + r) y z) / (y - z)| ≤
          8 * CP * jb y ^ (-1 : ℝ) := by
        rw [abs_div, div_eq_mul_one_div]
        have h1 : |deriv (fbar + r) y - c01_secant (fbar + r) y z| ≤ 2 * CP := by
          have := abs_sub (deriv (fbar + r) y) (c01_secant (fbar + r) y z)
          linarith [hfd y]
        calc _ ≤ 2 * CP * (4 * jb y ^ (-1 : ℝ)) :=
              mul_le_mul h1 hinv (by positivity) (by positivity)
          _ = _ := by ring
      have hh2' : |deriv (deriv h) y| ≤ xh * (jb y ^ (-γ) * jb y ^ (1 / p) * jb y ^ (1 / p)) := by
        rw [← Ed]; exact hh2b
      have hS' : |(deriv h y - c01_secant h y z) / (y - z)| ≤
          4 * jb y ^ (-1 : ℝ) * (|deriv h y| + |c01_secant h y z|) := by
        rw [abs_div, div_eq_mul_one_div, mul_comm]
        exact mul_le_mul hinv (abs_sub _ _) (abs_nonneg _) (mul_nonneg (by norm_num) (hjnn y _))
      have := (alg _ _ _ _ ha hb hbW hh2' hS').2
      rw [hK]
      unfold c10_aux_DK
      calc _ = _ := by ring_nf
        _ ≤ _ := this
        _ = _ := by ring
  have hCa : CL * (9 * CP) ≤ C := by
    have : 0 ≤ Cg * (9 * CP + 9) := by positivity
    have : 0 ≤ CL * CP := by positivity
    rw [hC]; nlinarith
  have hCb : Cg ≤ C := by
    have : 0 ≤ CL * CP := by positivity
    rw [hC]; nlinarith
  have hCc : 5 * (CL * (9 * CP)) + Cg * (9 * CP + 8) ≤ C := by
    rw [hC]; nlinarith
  refine ⟨fun y z hy hz => ⟨?_, ?_⟩, ?_⟩
  · refine (core y z hy hz).1.trans ?_
    have := hjnn y (-1 : ℝ)
    calc CL * ε * (9 * CP) * jb y ^ (-1 : ℝ) = CL * (9 * CP) * ε * jb y ^ (-1 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCa hε.le) this
  · refine (core y z hy hz).2.1.trans ?_
    rw [Ee]
    have hX := hjnn y (-γ + 1 / p - 1)
    have hQ : 0 ≤ (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z| := by
      have := hjnn y (-γ); have := hjnn z (-γ); positivity
    have h1 : CL * (9 * CP) * (ε * xh * jb y ^ (-γ + 1 / p - 1)) ≤
        C * (ε * xh * jb y ^ (-γ + 1 / p - 1)) := mul_le_mul_of_nonneg_right hCa (by positivity)
    have h2 : Cg * (ε * xh * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|)) ≤
        C * (ε * xh * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|)) :=
      mul_le_mul_of_nonneg_right hCb (by positivity)
    linarith
  · filter_upwards [c10_aux_ae_differentiableAt hW.2, c10_aux_ae_differentiableAt hh.1.2, P2b,
      hdd0] with y d1 d2 b1 b2 z hy hz
    have := (core y z hy hz).2.2 d1 d2 (b1 (by linarith)) (b2 (by linarith))
    rw [div_eq_mul_one_div (|c10_far_subtraction_Ktilde p ε (fbar + r) h y z|)]
    refine this.trans ?_
    rw [Ef, Eg]
    have hX : 0 ≤ jb y ^ (-γ + 2 / p - 1) + jb y ^ (1 / p - 1) *
        ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|) := by
      have := hjnn y (-γ); have := hjnn z (-γ); have := hjnn y (-γ + 2 / p - 1)
      have := hjnn y (1 / p - 1); positivity
    calc (5 * (CL * ε * (9 * CP)) + Cg * ε * (9 * CP + 8)) * xh * _ =
        (5 * (CL * (9 * CP)) + Cg * (9 * CP + 8)) * ε * xh * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCc hε.le) hx) hX

/-- Blueprint: lem:c10_N3_far_plus.  Far-field estimates for `y ≥ 2` (the second for a.e. `y`). -/
theorem c10_N3_far_plus (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      (∀ y : ℝ, 2 ≤ y →
        IntegrableOn (fun z => c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1))
          {z | y / 2 ≤ |y - z|} ∧
        |(∫ z in {z | y / 2 ≤ |y - z|},
            c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
          b_eps p ε y * deriv h y| ≤ C * ε * xNorm p γ h * jb y ^ (-γ)) ∧
      (∀ᵐ y, 2 ≤ y →
        IntegrableOn (fun z => c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1))
          {z | y / 2 ≤ |y - z|} ∧
        |(∫ z in {z | y / 2 ≤ |y - z|},
            c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
          deriv (fun x => b_eps p ε x * deriv h x) y| ≤
          C * ε * xNorm p γ h * jb y ^ (-γ + 1 / p)) := by
  obtain ⟨hp0, -, hγ1, -, hγ2⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨Ci, hCi, hint⟩ := c10_far_plus_integrand p γ M N hp hp1 hγ hM hN
  obtain ⟨-, hI2, hI3⟩ := c10_elementary_integrals p hp0 hp1
  have hjpos := c10_aux_jb_pos
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e => (Real.rpow_pos_of_pos (hjpos y) e).le
  set Iγ := ∫ z, jb z ^ (-γ) with hIγ
  have hIγ0 : 0 ≤ Iγ := integral_nonneg fun z => hjnn z _
  set T := (2 : ℝ) ^ (2 * (1 + p) + 2 * (1 : ℕ)) with hT
  have hT0 : 0 ≤ T := by positivity
  set S := 8 / p + 2 / (1 + p) + T * Iγ with hS
  have hS0 : 0 ≤ S := by positivity
  have hp1' : 0 < p + 1 := by linarith
  have hip : 1 / p ≤ 1 + p := by
    rw [div_le_iff₀ hp0]; nlinarith
  refine ⟨(p + 1) * Ci * S + 1, by positivity, fun ε hε hε1 fbar hf r hr hrN h hh => ?_⟩
  obtain ⟨V1, -, ⟨-, V3⟩⟩ := c10_N3_variation p γ M ε hp hp1 hγ hM hε.le hε1 fbar hf r hr h hh
  obtain ⟨-, -, -, hsubf⟩ := c10_far_subtraction p γ M N hp hp1 hγ hM hN ε hε hε1
  obtain ⟨s1, s2⟩ := hsubf fbar hf r hr hrN h hh
  obtain ⟨i1, i2⟩ := hint ε hε hε1 fbar hf r hr hrN h hh
  set xh := xNorm p γ h
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  set c := Ci * ε * xh with hc
  have hc0 : 0 ≤ c := by positivity
  -- the elementary far-field integrals at `y ≥ 2`
  have farI : ∀ y : ℝ, 2 ≤ y →
      (IntegrableOn (fun z => |y - z| ^ (-(1 + p))) {z | y / 2 ≤ |y - z|} ∧
        ∫ z in {z | y / 2 ≤ |y - z|}, |y - z| ^ (-(1 + p)) ≤ 8 / p * jb y ^ (-p)) ∧
      (IntegrableOn (fun z => |y - z| ^ (-(1 + p) - 1)) {z | y / 2 ≤ |y - z|} ∧
        ∫ z in {z | y / 2 ≤ |y - z|}, |y - z| ^ (-(1 + p) - 1) ≤ 2 / (1 + p)) ∧
      (IntegrableOn (fun z => jb z ^ (-γ) / |y - z| ^ (1 + p + 1)) {z | y / 2 ≤ |y - z|} ∧
        ∫ z in {z | y / 2 ≤ |y - z|}, jb z ^ (-γ) / |y - z| ^ (1 + p + 1) ≤
          T * Iγ * jb y ^ (-(1 + p) - 1)) := by
    intro y hy
    have ha : 0 < y / 2 := by linarith
    have hms : MeasurableSet {ρ : ℝ | y / 2 ≤ |ρ|} := measurableSet_le measurable_const (by fun_prop)
    obtain ⟨-, -, ⟨t1i, t1v⟩, ⟨t2i, t2v⟩, -⟩ := hI2 (y / 2) ha
    have tr1 := c10_aux_translate (fun ρ => |ρ| ^ (-(1 + p))) y hms
    have tr2 := c10_aux_translate (fun ρ => |ρ| ^ (-(1 + p) - 1)) y hms
    have hy' : 2 ≤ |y| := by rwa [abs_of_nonneg (by linarith)]
    obtain ⟨t3i, t3a, t3b⟩ := hI3 γ hγ1 y hy' 1 (Or.inl rfl)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y)] at t3i t3a t3b
    push_cast at t3i t3a t3b
    rw [← hIγ] at t3a t3b
    -- `(y/2)^{-p} ≤ 4 ⟨y⟩^{-p}`
    have hjy : jb y / 4 ≤ y / 2 := by
      have : jb y ≤ 2 * y := by
        unfold jb; rw [Real.sqrt_le_left (by linarith)]; nlinarith
      linarith
    have hq : (y / 2) ^ (-p) ≤ 4 * jb y ^ (-p) := by
      calc (y / 2) ^ (-p) ≤ (jb y / 4) ^ (-p) :=
            Real.rpow_le_rpow_of_nonpos (by have := hjpos y; positivity) hjy (by linarith)
        _ = (4 : ℝ) ^ p * jb y ^ (-p) := by
            rw [Real.div_rpow (hjpos y).le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
            field_simp
        _ ≤ 4 * jb y ^ (-p) := by
            apply mul_le_mul_of_nonneg_right _ (hjnn y _)
            calc (4 : ℝ) ^ p ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
              _ = 4 := Real.rpow_one 4
    have hq2 : (y / 2) ^ (-1 - p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    refine ⟨⟨tr1.2 t1i, ?_⟩, ⟨tr2.2 t2i, ?_⟩, ⟨t3i, ?_⟩⟩
    · show (∫ z in {z | y - z ∈ {ρ : ℝ | y / 2 ≤ |ρ|}}, |y - z| ^ (-(1 + p))) ≤ _
      rw [tr1.1, t1v]
      calc 2 / p * (y / 2) ^ (-p) ≤ 2 / p * (4 * jb y ^ (-p)) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = 8 / p * jb y ^ (-p) := by ring
    · show (∫ z in {z | y - z ∈ {ρ : ℝ | y / 2 ≤ |ρ|}}, |y - z| ^ (-(1 + p) - 1)) ≤ _
      rw [tr2.1, t2v]
      calc 2 / (1 + p) * (y / 2) ^ (-1 - p) ≤ 2 / (1 + p) * 1 :=
            mul_le_mul_of_nonneg_left hq2 (by positivity)
        _ = _ := mul_one _
    · refine t3a.trans (t3b.trans (le_of_eq ?_))
      rw [hT]; push_cast; ring_nf
  have hmeas : ∀ y : ℝ, MeasurableSet {z : ℝ | y / 2 ≤ |y - z|} := fun y =>
    measurableSet_le measurable_const (by fun_prop)
  -- algebraic identities for powers of `d = |y-z| > 0`
  have hid : ∀ d : ℝ, 0 < d → d ^ (-(1 + p)) = 1 / d ^ (p + 1) ∧
      d ^ (-(1 + p) - 1) = 1 / (d ^ (p + 1) * d) ∧ d ^ (1 + p + 1) = d ^ (p + 1) * d := by
    intro d hd
    refine ⟨?_, ?_, ?_⟩
    · rw [Real.rpow_neg hd.le, add_comm, one_div]
    · rw [Real.rpow_sub_one hd.ne', Real.rpow_neg hd.le, add_comm]; field_simp
    · rw [Real.rpow_add_one hd.ne', add_comm]
  have hdist : ∀ y z : ℝ, 2 ≤ y → y / 2 ≤ |y - z| → 0 < |y - z| := fun y z hy hz => by linarith
  have hfinal : ∀ (y e : ℝ), c * S * jb y ^ e ≤ ((p + 1) * Ci * S + 1) * ε * xh * jb y ^ e := by
    intro y e
    have : c * S ≤ ((p + 1) * Ci * S + 1) * ε * xh := by
      rw [hc]
      have h1 : Ci * S ≤ (p + 1) * Ci * S + 1 := by nlinarith [mul_nonneg hCi.le hS0]
      calc Ci * ε * xh * S = (Ci * S) * ε * xh := by ring
        _ ≤ ((p + 1) * Ci * S + 1) * ε * xh := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hε.le) hx
    exact mul_le_mul_of_nonneg_right this (hjnn y e)
  refine ⟨fun y hy => ⟨(V1 y).integrableOn, ?_⟩, ?_⟩
  · obtain ⟨⟨I1i, I1v⟩, ⟨I2i, I2v⟩, ⟨I3i, I3v⟩⟩ := farI y hy
    rw [s1 y hy]
    set e1 := -γ + 1 / p - 1
    have hgi : IntegrableOn (fun z => c * jb y ^ e1 * |y - z| ^ (-(1 + p)) +
        c * jb y ^ (-γ) * |y - z| ^ (-(1 + p) - 1) +
        c * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1))) {z | y / 2 ≤ |y - z|} :=
      ((I1i.const_mul _).add (I2i.const_mul _)).add (I3i.const_mul _)
    have hpt : ∀ z, y / 2 ≤ |y - z| →
        |c10_far_subtraction_Ktilde p ε (fbar + r) h y z / |y - z| ^ (p + 1)| ≤
          c * jb y ^ e1 * |y - z| ^ (-(1 + p)) + c * jb y ^ (-γ) * |y - z| ^ (-(1 + p) - 1) +
            c * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1)) := by
      intro z hz
      have hd := hdist y z hy hz
      obtain ⟨q1, q2, q3⟩ := hid _ hd
      have hP : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos hd _
      rw [abs_div, abs_of_pos hP, q1, q2, q3]
      have hb := (i1 y z hy hz).2
      calc _ ≤ c * (jb y ^ e1 + (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|) / |y - z| ^ (p + 1) :=
            div_le_div_of_nonneg_right hb hP.le
        _ = _ := by field_simp; ring
    have hint1 : ∫ z in {z | y / 2 ≤ |y - z|},
        |c10_far_subtraction_Ktilde p ε (fbar + r) h y z / |y - z| ^ (p + 1)| ≤
        ∫ z in {z | y / 2 ≤ |y - z|}, (c * jb y ^ e1 * |y - z| ^ (-(1 + p)) +
          c * jb y ^ (-γ) * |y - z| ^ (-(1 + p) - 1) +
          c * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1))) :=
      integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hgi
        ((ae_restrict_iff' (hmeas y)).2 (ae_of_all _ hpt))
    have J1 : IntegrableOn (fun z => c * jb y ^ e1 * |y - z| ^ (-(1 + p)))
        {z | y / 2 ≤ |y - z|} := I1i.const_mul _
    have J2 : IntegrableOn (fun z => c * jb y ^ (-γ) * |y - z| ^ (-(1 + p) - 1))
        {z | y / 2 ≤ |y - z|} := I2i.const_mul _
    have J3 : IntegrableOn (fun z => c * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1)))
        {z | y / 2 ≤ |y - z|} := I3i.const_mul _
    have J12 : IntegrableOn (fun z => c * jb y ^ e1 * |y - z| ^ (-(1 + p)) +
        c * jb y ^ (-γ) * |y - z| ^ (-(1 + p) - 1)) {z | y / 2 ≤ |y - z|} := J1.add J2
    rw [integral_add J12 J3, integral_add J1 J2, integral_const_mul, integral_const_mul,
      integral_const_mul] at hint1
    have a1 : jb y ^ e1 * jb y ^ (-p) ≤ jb y ^ (-γ) := by
      rw [← Real.rpow_add (hjpos y)]; exact c10_aux_jb_rpow_mono y (by linarith)
    have a3 : jb y ^ (-(1 + p) - 1) ≤ jb y ^ (-γ) := c10_aux_jb_rpow_mono y (by linarith)
    have hj1 := hjnn y e1; have hj2 := hjnn y (-γ)
    calc _ ≤ _ := abs_integral_le_integral_abs
      _ ≤ _ := hint1
      _ ≤ c * jb y ^ e1 * (8 / p * jb y ^ (-p)) + c * jb y ^ (-γ) * (2 / (1 + p)) +
          c * (T * Iγ * jb y ^ (-(1 + p) - 1)) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left I1v (mul_nonneg hc0 hj1))
            (mul_le_mul_of_nonneg_left I2v (mul_nonneg hc0 hj2)))
            (mul_le_mul_of_nonneg_left I3v hc0)
      _ = c * (8 / p) * (jb y ^ e1 * jb y ^ (-p)) + c * jb y ^ (-γ) * (2 / (1 + p)) +
          c * (T * Iγ) * jb y ^ (-(1 + p) - 1) := by ring
      _ ≤ c * (8 / p) * jb y ^ (-γ) + c * jb y ^ (-γ) * (2 / (1 + p)) +
          c * (T * Iγ) * jb y ^ (-γ) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left a1 (by positivity)) le_rfl)
            (mul_le_mul_of_nonneg_left a3 (by positivity))
      _ = c * S * jb y ^ (-γ) := by rw [hS]; ring
      _ ≤ _ := hfinal y _
  · have hne2 : ∀ᵐ y : ℝ, y ≠ 2 := by rw [ae_iff]; simp
    filter_upwards [V3, s2, i2, hne2] with y v3 s2y i2y hy2 hy
    have hy' : 2 < y := lt_of_le_of_ne hy (Ne.symm hy2)
    refine ⟨v3.1.integrableOn, ?_⟩
    obtain ⟨⟨I1i, I1v⟩, ⟨I2i, I2v⟩, ⟨I3i, I3v⟩⟩ := farI y hy
    rw [s2y hy']
    set e2 := -γ + 2 / p - 1
    set c' := (p + 1) * c with hc'
    have hc'0 : 0 ≤ c' := by positivity
    have hgi : IntegrableOn (fun z => c' * jb y ^ e2 * |y - z| ^ (-(1 + p)) +
        c' * (jb y ^ (1 / p - 1) * jb y ^ (-γ)) * |y - z| ^ (-(1 + p) - 1) +
        c' * jb y ^ (1 / p - 1) * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1))) {z | y / 2 ≤ |y - z|} :=
      ((I1i.const_mul _).add (I2i.const_mul _)).add (I3i.const_mul _)
    have hpt : ∀ z, y / 2 ≤ |y - z| →
        |1 / |y - z| ^ (p + 1) *
          (deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y -
            (p + 1) / (y - z) * c10_far_subtraction_Ktilde p ε (fbar + r) h y z)| ≤
          c' * jb y ^ e2 * |y - z| ^ (-(1 + p)) +
          c' * (jb y ^ (1 / p - 1) * jb y ^ (-γ)) * |y - z| ^ (-(1 + p) - 1) +
          c' * jb y ^ (1 / p - 1) * (jb z ^ (-γ) / |y - z| ^ (1 + p + 1)) := by
      intro z hz
      have hd := hdist y z hy hz
      obtain ⟨q1, q2, q3⟩ := hid _ hd
      have hP : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos hd _
      rw [q1, q2, q3]
      have hb := i2y z hy hz
      set A := |deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y|
      set B := |c10_far_subtraction_Ktilde p ε (fbar + r) h y z|
      have hAB : |deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y -
            (p + 1) / (y - z) * c10_far_subtraction_Ktilde p ε (fbar + r) h y z| ≤
          (p + 1) * (A + B / |y - z|) := by
        have e : |(p + 1) / (y - z) * c10_far_subtraction_Ktilde p ε (fbar + r) h y z| =
            (p + 1) * (B / |y - z|) := by
          rw [abs_mul, abs_div, abs_of_pos hp1']; ring
        have := abs_sub (deriv (fun y' => c10_far_subtraction_Ktilde p ε (fbar + r) h y' z) y)
          ((p + 1) / (y - z) * c10_far_subtraction_Ktilde p ε (fbar + r) h y z)
        rw [e] at this
        have : 0 ≤ A := abs_nonneg _
        nlinarith
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / |y - z| ^ (p + 1))]
      calc _ ≤ 1 / |y - z| ^ (p + 1) * ((p + 1) * (A + B / |y - z|)) :=
            mul_le_mul_of_nonneg_left hAB (by positivity)
        _ ≤ 1 / |y - z| ^ (p + 1) * ((p + 1) * (c * (jb y ^ e2 +
            jb y ^ (1 / p - 1) * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|)))) := by
            gcongr
        _ = _ := by rw [hc']; field_simp; ring
    have hint1 := integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hgi
        ((ae_restrict_iff' (hmeas y)).2 (ae_of_all _ hpt))
    have J1 : IntegrableOn (fun z => c' * jb y ^ e2 * |y - z| ^ (-(1 + p)))
        {z | y / 2 ≤ |y - z|} := I1i.const_mul _
    have J2 : IntegrableOn (fun z => c' * (jb y ^ (1 / p - 1) * jb y ^ (-γ)) *
        |y - z| ^ (-(1 + p) - 1)) {z | y / 2 ≤ |y - z|} := I2i.const_mul _
    have J3 : IntegrableOn (fun z => c' * jb y ^ (1 / p - 1) *
        (jb z ^ (-γ) / |y - z| ^ (1 + p + 1))) {z | y / 2 ≤ |y - z|} := I3i.const_mul _
    have J12 : IntegrableOn (fun z => c' * jb y ^ e2 * |y - z| ^ (-(1 + p)) +
        c' * (jb y ^ (1 / p - 1) * jb y ^ (-γ)) * |y - z| ^ (-(1 + p) - 1))
        {z | y / 2 ≤ |y - z|} := J1.add J2
    rw [integral_add J12 J3, integral_add J1 J2, integral_const_mul, integral_const_mul,
      integral_const_mul] at hint1
    have a1 : jb y ^ e2 * jb y ^ (-p) ≤ jb y ^ (-γ + 1 / p) := by
      rw [← Real.rpow_add (hjpos y)]; exact c10_aux_jb_rpow_mono y (by
        have : 2 / p = 2 * (1 / p) := by ring
        linarith)
    have a2 : jb y ^ (1 / p - 1) * jb y ^ (-γ) ≤ jb y ^ (-γ + 1 / p) := by
      rw [← Real.rpow_add (hjpos y)]; exact c10_aux_jb_rpow_mono y (by linarith)
    have a3 : jb y ^ (1 / p - 1) * jb y ^ (-(1 + p) - 1) ≤ jb y ^ (-γ + 1 / p) := by
      rw [← Real.rpow_add (hjpos y)]; exact c10_aux_jb_rpow_mono y (by linarith)
    have hj1 := hjnn y e2; have hj2 := hjnn y (1 / p - 1); have hj3 := hjnn y (-γ)
    calc _ ≤ _ := abs_integral_le_integral_abs
      _ ≤ _ := hint1
      _ ≤ c' * jb y ^ e2 * (8 / p * jb y ^ (-p)) +
          c' * (jb y ^ (1 / p - 1) * jb y ^ (-γ)) * (2 / (1 + p)) +
          c' * jb y ^ (1 / p - 1) * (T * Iγ * jb y ^ (-(1 + p) - 1)) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left I1v (mul_nonneg hc'0 hj1))
            (mul_le_mul_of_nonneg_left I2v (mul_nonneg hc'0 (mul_nonneg hj2 hj3))))
            (mul_le_mul_of_nonneg_left I3v (mul_nonneg hc'0 hj2))
      _ = c' * (8 / p) * (jb y ^ e2 * jb y ^ (-p)) +
          c' * (2 / (1 + p)) * (jb y ^ (1 / p - 1) * jb y ^ (-γ)) +
          c' * (T * Iγ) * (jb y ^ (1 / p - 1) * jb y ^ (-(1 + p) - 1)) := by ring
      _ ≤ c' * (8 / p) * jb y ^ (-γ + 1 / p) + c' * (2 / (1 + p)) * jb y ^ (-γ + 1 / p) +
          c' * (T * Iγ) * jb y ^ (-γ + 1 / p) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left a1 (by positivity))
            (mul_le_mul_of_nonneg_left a2 (by positivity)))
            (mul_le_mul_of_nonneg_left a3 (by positivity))
      _ = (p + 1) * Ci * S * ε * xh * jb y ^ (-γ + 1 / p) := by rw [hc', hc, hS]; ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (hjnn y _)
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hε.le) hx

/-! ### Far field for `y ≤ -2` and the compact region -/

/-- Blueprint: lem:c10_N3_far_minus.  Far-field integrand bounds and estimates for `y ≤ -2`
(derivative statements for a.e. `y`), and `b_ε = 0` on `y ≤ 1`. -/
theorem c10_N3_far_minus (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      (∀ y z : ℝ, y ≤ -2 → |y| / 2 ≤ |y - z| →
        |c10_N3_linearization_K p ε (fbar + r) h y z| ≤
          C * ε * xNorm p γ h * (jb y ^ (-γ - 1) + (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|)) ∧
      (∀ᵐ y, ∀ z : ℝ, y ≤ -2 → |y| / 2 ≤ |y - z| →
        |deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y| +
            |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ≤
          C * ε * xNorm p γ h * (jb y ^ (-γ - 2) +
            jb y ^ (-1 : ℝ) * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|))) ∧
      (∀ y : ℝ, y ≤ -2 →
        IntegrableOn (fun z => |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1))
          {z | |y| / 2 ≤ |y - z|} ∧
        (∫ z in {z | |y| / 2 ≤ |y - z|},
          |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ≤
          C * ε * xNorm p γ h * jb y ^ (-γ)) ∧
      (∀ᵐ y, y ≤ -2 →
        IntegrableOn (fun z => |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1))
          {z | |y| / 2 ≤ |y - z|} ∧
        (∫ z in {z | |y| / 2 ≤ |y - z|},
          |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ≤
          C * ε * xNorm p γ h * jb y ^ (-γ - 1)) ∧
      (∀ y : ℝ, y ≤ 1 → b_eps p ε y = 0) := by
  obtain ⟨hp0, -, hγ1, -, hγ2⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨CP, hCP, hPC⟩ := c10_profile_consequences p γ M N hp hp1 hγ hM hN
  obtain ⟨Cg, hCg, hKb⟩ := c10_aux_kernel_bounds p (max CP 1) hp0 hp1 (le_max_right _ _)
  set Iγ := ∫ z, jb z ^ (-γ) with hIγ
  have hjpos := c10_aux_jb_pos
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e => (Real.rpow_pos_of_pos (hjpos y) e).le
  have hIγ0 : 0 ≤ Iγ := integral_nonneg fun z => hjnn z _
  set A := Cg * (9 * CP + 9) with hA
  have hA0 : 0 < A := by positivity
  have hCgA : Cg ≤ A := by rw [hA]; nlinarith
  set T := (2:ℝ) ^ (2 * (1 + p) + 2) with hT
  set S := 2 / p + 2 + T * Iγ with hS
  have hS0 : 0 ≤ S := by positivity
  have hTI : 0 ≤ T * Iγ := by positivity
  have h2p : 0 ≤ 2 / p := by positivity
  have hS1 : 2 / p ≤ S ∧ 2 ≤ S := ⟨by rw [hS]; linarith, by rw [hS]; linarith⟩
  have hjm := c10_aux_jb_rpow_mono
  have hjadd : ∀ y a b : ℝ, jb y ^ a * jb y ^ b = jb y ^ (a + b) := fun y a b =>
    (Real.rpow_add (hjpos y) a b).symm
  have E1 : ∀ y, jb y ^ (-γ - 2) ≤ jb y ^ (-γ - 1) := fun y => hjm y (by linarith)
  have E2 : ∀ y, jb y ^ (-γ - 1) ≤ jb y ^ (-γ) := fun y => hjm y (by linarith)
  have E3 : ∀ y, jb y ^ ((-1 : ℝ) + (-(1 + p) - 1)) ≤ jb y ^ (-γ - 1) := fun y => hjm y (by linarith)
  have E4 : ∀ y, jb y ^ (-(1 + p) - 1) ≤ jb y ^ (-γ) := fun y => hjm y (by linarith)
  have E5 : ∀ y : ℝ, jb y ^ (-1 : ℝ) * jb y ^ (-γ) = jb y ^ (-γ - 1) := fun y => by
    rw [hjadd]; congr 1; ring
  have hJW : ∀ y : ℝ, jb y ^ (-1 : ℝ) * jb y ^ (-γ - 1) = jb y ^ (-γ - 2) := fun y => by
    rw [hjadd]; congr 1; ring
  refine ⟨(p + 2) * A * S + A, by positivity, fun ε hε hε1 fbar hf r hr hrN h hh => ?_⟩
  obtain ⟨I1, -, -, -, P3b, -⟩ := hPC fbar hf r hr hrN
  have hfd : ∀ y, |deriv (fbar + r) y| ≤ CP := (I1 (fbar + r) (Set.mem_insert _ _)).1
  obtain ⟨hv, -, hd0, -, hdd0⟩ := c10_aux_X_simple p γ hh
  have hfA := c10_aux_C2_admissible_class hf.1 (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have hW : W2inftyLoc (fbar + r) := by
    refine ⟨hfA.1.add hr.1.1, ?_⟩
    have : deriv (fbar + r) = deriv fbar + deriv r := funext fun x =>
      deriv_add (hfA.1.differentiable (by norm_num) x) (hr.1.1.differentiable (by norm_num) x)
    rw [this]; exact hfA.2.2.add hr.1.2
  set xh := xNorm p γ h with hxh
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  have hC0 : (p + 2) * A * S + A ≥ A := by
    have : 0 ≤ (p + 2) * A * S := by positivity
    linarith
  -- geometry
  have geo : ∀ y z : ℝ, y ≤ -2 → |y| / 2 ≤ |y - z| →
      2 ≤ |y| ∧ y ≠ z ∧ 0 < |y - z| ∧ 1 / |y - z| ≤ 4 * jb y ^ (-1 : ℝ) := by
    intro y z hy hz
    have hy2 : 2 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    have ht : 0 < |y - z| := by linarith
    refine ⟨hy2, fun e => by rw [e, sub_self, abs_zero] at ht; exact lt_irrefl _ ht, ht, ?_⟩
    have hj := c10_aux_jb_le_two_abs (show 1 ≤ |y| by linarith)
    rw [Real.rpow_neg_one, div_le_iff₀ ht]
    have : jb y ≤ 4 * |y - z| := by linarith
    calc (1 : ℝ) = (jb y)⁻¹ * jb y := (inv_mul_cancel₀ (hjpos y).ne').symm
      _ ≤ (jb y)⁻¹ * (4 * |y - z|) := mul_le_mul_of_nonneg_left this (inv_pos.2 (hjpos y)).le
      _ = _ := by ring
  -- pointwise core
  have core : ∀ y z : ℝ, y ≤ -2 → |y| / 2 ≤ |y - z| →
      |c10_N3_linearization_K p ε (fbar + r) h y z| ≤ Cg * ε * xh * (jb y ^ (-γ - 1) +
        (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|) ∧
      (DifferentiableAt ℝ (deriv (fbar + r)) y → DifferentiableAt ℝ (deriv h) y →
        |deriv (deriv (fbar + r)) y| ≤ CP * jb y ^ (-p - 2) →
        |deriv (deriv h) y| ≤ xh * jb y ^ (-γ - 2) →
        deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y =
          c10_aux_DK p ε (fbar + r) h y z ∧
        |c10_aux_DK p ε (fbar + r) h y z| +
          |c10_N3_linearization_K p ε (fbar + r) h y z| * (1 / |y - z|) ≤
          A * ε * xh * (jb y ^ (-1 : ℝ) * jb y ^ (-γ - 1) +
            jb y ^ (-1 : ℝ) * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|))) := by
    intro y z hy hz
    obtain ⟨hy2, hyz, ht, hinv⟩ := geo y z hy hz
    obtain ⟨-, -, -, -, sf5⟩ := c10_secant_identities (fbar + r) hW y z hyz
    have hu : |deriv (fbar + r) y| ≤ max CP 1 := (hfd y).trans (le_max_left _ _)
    have hvC : |c01_secant (fbar + r) y z| ≤ CP := ((sf5 CP hfd).2).trans (min_le_left _ _)
    have hv' : |c01_secant (fbar + r) y z| ≤ max CP 1 := hvC.trans (le_max_left _ _)
    obtain ⟨b1, b2, b11, b12, b22, -⟩ := hKb ε hε.le hε1 _ _ hu hv'
    have hQ0 : 0 ≤ (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z| := by
      have := hjnn y (-γ); have := hjnn z (-γ); positivity
    have hSh : |c01_secant h y z| ≤ xh * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|) := by
      rw [c01_secant, if_neg hyz, abs_div, ← mul_div_assoc, div_le_div_iff_of_pos_right ht]
      calc |h y - h z| ≤ |h y| + |h z| := abs_sub _ _
        _ ≤ xh * jb y ^ (-γ) + xh * jb z ^ (-γ) := add_le_add (hv y) (hv z)
        _ = _ := by ring
    have hh1 : |deriv h y| ≤ xh * jb y ^ (-γ - 1) := hd0 y (by linarith)
    have hJ0 := hjnn y (-1 : ℝ)
    have hW1 := hjnn y (-γ - 1)
    have alg := fun (a b h2 S' : ℝ) (ha : |a| ≤ CP * jb y ^ (-1 : ℝ))
        (hb : |b| ≤ 8 * CP * jb y ^ (-1 : ℝ))
        (hh2 : |h2| ≤ xh * (jb y ^ (-1 : ℝ) * jb y ^ (-γ - 1)))
        (hS' : |S'| ≤ 4 * jb y ^ (-1 : ℝ) * (|deriv h y| + |c01_secant h y z|)) =>
      c10_aux_far_alg (a := a) (b := b) (h2 := h2) (S' := S') (t := 1 / |y - z|)
        (mul_nonneg hCg.le hε.le) hCP.le hx hJ0 hW1 hQ0 b1 b2 b11 b12 b22 ha hb hh1 hh2 hSh hS'
        (by positivity) hinv
    refine ⟨?_, fun hf2 hh2 hf2b hh2b => ?_⟩
    · have := (alg 0 0 0 0 (by simp; positivity) (by simp; positivity) (by simp; positivity)
        (by simp; positivity)).1
      unfold c10_N3_linearization_K
      calc _ ≤ _ := this
        _ = _ := by ring
    · refine ⟨(c10_aux_K_hasDeriv p ε hp0 hp1 hε.le hW hh.1 hyz hf2 hh2).deriv, ?_⟩
      have ha : |deriv (deriv (fbar + r)) y| ≤ CP * jb y ^ (-1 : ℝ) :=
        hf2b.trans (mul_le_mul_of_nonneg_left (hjm y (by linarith)) hCP.le)
      have hb : |(deriv (fbar + r) y - c01_secant (fbar + r) y z) / (y - z)| ≤
          8 * CP * jb y ^ (-1 : ℝ) := by
        rw [abs_div, div_eq_mul_one_div]
        have h1 : |deriv (fbar + r) y - c01_secant (fbar + r) y z| ≤ 2 * CP := by
          have := abs_sub (deriv (fbar + r) y) (c01_secant (fbar + r) y z)
          linarith [hfd y]
        calc _ ≤ 2 * CP * (4 * jb y ^ (-1 : ℝ)) :=
              mul_le_mul h1 hinv (by positivity) (by positivity)
          _ = _ := by ring
      have hh2' : |deriv (deriv h) y| ≤ xh * (jb y ^ (-1 : ℝ) * jb y ^ (-γ - 1)) := by
        rw [hjadd, show (-1 : ℝ) + (-γ - 1) = -γ - 2 by ring]; exact hh2b
      have hS' : |(deriv h y - c01_secant h y z) / (y - z)| ≤
          4 * jb y ^ (-1 : ℝ) * (|deriv h y| + |c01_secant h y z|) := by
        rw [abs_div, div_eq_mul_one_div, mul_comm]
        exact mul_le_mul hinv (abs_sub _ _) (abs_nonneg _) (by positivity)
      have := (alg _ _ _ _ ha hb hh2' hS').2
      unfold c10_aux_DK
      unfold c10_N3_linearization_K
      calc _ ≤ _ := this
        _ = _ := by rw [hA]; ring
  have hmono : ∀ X, 0 ≤ X → ∀ c, c ≤ (p + 2) * A * S + A →
      c * ε * xh * X ≤ ((p + 2) * A * S + A) * ε * xh * X := fun X hX c hc =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc hε.le) hx) hX
  have hgood : ∀ᵐ y, DifferentiableAt ℝ (deriv (fbar + r)) y ∧ DifferentiableAt ℝ (deriv h) y ∧
      (y ≤ 0 → |deriv (deriv (fbar + r)) y| ≤ CP * jb y ^ (-p - 2)) ∧
      (y ≤ 0 → |deriv (deriv h) y| ≤ xh * jb y ^ (-γ - 2)) := by
    filter_upwards [c10_aux_ae_differentiableAt hW.2, c10_aux_ae_differentiableAt hh.1.2, P3b,
      hdd0] with y a b c d using ⟨a, b, c, d⟩
  have hSm : ∀ y : ℝ, MeasurableSet {z : ℝ | |y| / 2 ≤ |y - z|} := fun y =>
    measurableSet_le measurable_const (by fun_prop)
  have Km := fun y => c10_aux_K_meas p ε hp0 hp1 hε.le hW.1.continuous hh.1.1.continuous y
  have hden : ∀ y : ℝ, Measurable (fun z : ℝ => |y - z| ^ (p + 1)) := fun y => by fun_prop
  have hpow := E4
  refine ⟨fun y z hy hz => ?_, ?_, fun y hy => ?_, ?_, fun y hy => ?_⟩
  · have := (core y z hy hz).1
    refine this.trans (hmono _ ?_ _ (hCgA.trans hC0))
    have := hjnn y (-γ - 1); have := hjnn y (-γ); have := hjnn z (-γ)
    have := (geo y z hy hz).2.2.1; positivity
  · filter_upwards [hgood] with y ⟨d1, d2, b1, b2⟩ z hy hz
    obtain ⟨hD, hb⟩ := (core y z hy hz).2 d1 d2 (b1 (by linarith only [hy])) (b2 (by linarith only [hy]))
    rw [hD, div_eq_mul_one_div (|c10_N3_linearization_K p ε (fbar + r) h y z|), ← hJW y]
    refine hb.trans (hmono _ ?_ _ hC0)
    have := hjnn y (-γ - 1); have := hjnn y (-γ); have := hjnn z (-γ); have := hjnn y (-1 : ℝ)
    have := (geo y z hy hz).2.2.1; positivity
  · have hy2 : 2 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    have hFm : AEStronglyMeasurable
        (fun z => |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1))
        (volume.restrict {z | |y| / 2 ≤ |y - z|}) :=
      ((continuous_abs.measurable.comp (Km y).1).div (hden y)).aestronglyMeasurable
    have c0 : 0 ≤ Cg * ε * xh := by positivity
    obtain ⟨hI, hv⟩ := c10_aux_far_int p γ hp0 hp1 hγ1 hy2 hFm c0 (hjnn y (-γ - 1)) (hjnn y (-γ))
      zero_le_one (U := 1) (fun z hz => by
        obtain ⟨-, -, ht, -⟩ := geo y z hy hz
        rw [abs_of_nonneg (by positivity)]
        calc _ ≤ Cg * ε * xh * (jb y ^ (-γ - 1) + (jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|) /
              |y - z| ^ (p + 1) :=
              div_le_div_of_nonneg_right ((core y z hy hz).1) (by positivity)
          _ = _ := by rw [mul_div_assoc, c10_aux_far_split ht]; ring)
    refine ⟨hI, hv.trans ?_⟩
    have e1 : jb y ^ (-γ - 1) * (2 / p) ≤ 2 / p * jb y ^ (-γ) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (E2 y) h2p
    have e3 := mul_le_mul_of_nonneg_left (hpow y) hTI
    have hS' : Cg * ε * xh * S ≤ ((p + 2) * A * S + A) * ε * xh := by
      have : Cg * S ≤ (p + 2) * A * S + A := by
        have : Cg * S ≤ A * S := mul_le_mul_of_nonneg_right hCgA hS0
        have : A * S ≤ (p + 2) * A * S := by nlinarith
        linarith
      calc Cg * ε * xh * S = Cg * S * ε * xh := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hε.le) hx
    calc _ ≤ Cg * ε * xh * (S * jb y ^ (-γ)) := by
          apply mul_le_mul_of_nonneg_left _ c0
          rw [hS]
          have := hjnn y (-γ)
          nlinarith
      _ = Cg * ε * xh * S * jb y ^ (-γ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hS' (hjnn y _)
  · filter_upwards [hgood] with y ⟨d1, d2, b1, b2⟩ hy
    have hy2 : 2 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    have hp1' : 0 < p + 1 := by linarith
    set G := fun z => |c10_aux_DK p ε (fbar + r) h y z -
      (p + 1) * c10_N3_linearization_K p ε (fbar + r) h y z / (y - z)| / |y - z| ^ (p + 1)
    have hGm : Measurable G :=
      (continuous_abs.measurable.comp ((Km y).2.sub ((measurable_const.mul (Km y).1).div
        (measurable_const.sub measurable_id)))).div (hden y)
    have hFG : ∀ z, |y| / 2 ≤ |y - z| →
        |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1) = G z := by
      intro z hz
      obtain ⟨hD, -⟩ := (core y z hy hz).2 d1 d2 (b1 (by linarith only [hy])) (b2 (by linarith only [hy]))
      simp only [G, c10_N3_linearization_dK, hD]
    have hFm : AEStronglyMeasurable
        (fun z => |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1))
        (volume.restrict {z | |y| / 2 ≤ |y - z|}) :=
      hGm.aestronglyMeasurable.congr ((ae_restrict_iff' (hSm y)).2
        (ae_of_all _ fun z hz => (hFG z hz).symm))
    have c0 : 0 ≤ (p + 1) * A * ε * xh := by positivity
    have hJ0 := hjnn y (-1 : ℝ)
    obtain ⟨hI, hv⟩ := c10_aux_far_int p γ hp0 hp1 hγ1 hy2 hFm c0
      (mul_nonneg hJ0 (hjnn y (-γ - 1))) (mul_nonneg hJ0 (hjnn y (-γ))) hJ0 (fun z hz => by
        obtain ⟨-, -, ht, -⟩ := geo y z hy hz
        obtain ⟨hD, hb⟩ := (core y z hy hz).2 d1 d2 (b1 (by linarith only [hy])) (b2 (by linarith only [hy]))
        rw [abs_of_nonneg (by positivity)]
        have hdK : |c10_N3_linearization_dK p ε (fbar + r) h y z| ≤ (p + 1) *
            (|c10_aux_DK p ε (fbar + r) h y z| +
              |c10_N3_linearization_K p ε (fbar + r) h y z| * (1 / |y - z|)) := by
          unfold c10_N3_linearization_dK
          rw [hD]
          have h1 := abs_sub (c10_aux_DK p ε (fbar + r) h y z)
            ((p + 1) * c10_N3_linearization_K p ε (fbar + r) h y z / (y - z))
          have h2 : |(p + 1) * c10_N3_linearization_K p ε (fbar + r) h y z / (y - z)| =
              (p + 1) * (|c10_N3_linearization_K p ε (fbar + r) h y z| * (1 / |y - z|)) := by
            rw [abs_div, abs_mul, abs_of_pos hp1']; ring
          have h3 : 0 ≤ |c10_N3_linearization_K p ε (fbar + r) h y z| * (1 / |y - z|) := by
            positivity
          have h4 := abs_nonneg (c10_aux_DK p ε (fbar + r) h y z)
          have h5 : |c10_aux_DK p ε (fbar + r) h y z| ≤ (p + 1) * |c10_aux_DK p ε (fbar + r) h y z| :=
            le_mul_of_one_le_left h4 (by linarith only [hp0])
          rw [h2] at h1
          rw [mul_add]
          linarith only [h1, h5]
        calc _ ≤ (p + 1) * (A * ε * xh * (jb y ^ (-1 : ℝ) * jb y ^ (-γ - 1) +
              jb y ^ (-1 : ℝ) * ((jb y ^ (-γ) + jb z ^ (-γ)) / |y - z|))) / |y - z| ^ (p + 1) :=
              div_le_div_of_nonneg_right (hdK.trans (mul_le_mul_of_nonneg_left hb hp1'.le))
                (by positivity)
          _ = (p + 1) * A * ε * xh * ((jb y ^ (-1 : ℝ) * jb y ^ (-γ - 1) +
              (jb y ^ (-1 : ℝ) * jb y ^ (-γ) + jb y ^ (-1 : ℝ) * jb z ^ (-γ)) / |y - z|) /
                |y - z| ^ (p + 1)) := by ring
          _ = _ := by rw [c10_aux_far_split ht]; ring)
    refine ⟨hI, hv.trans ?_⟩
    have e1 : jb y ^ (-1 : ℝ) * jb y ^ (-γ - 1) ≤ jb y ^ (-γ - 1) := by
      rw [hJW]; exact E1 y
    have e2 := E5 y
    have e3 : jb y ^ (-1 : ℝ) * jb y ^ (-(1 + p) - 1) ≤ jb y ^ (-γ - 1) := by
      rw [hjadd]; exact E3 y
    have hS' : (p + 1) * A * ε * xh * S ≤ ((p + 2) * A * S + A) * ε * xh := by
      have : (p + 1) * A * S ≤ (p + 2) * A * S + A := by
        have := mul_nonneg hA0.le hS0
        linarith only [this, hA0]
      calc (p + 1) * A * ε * xh * S = (p + 1) * A * S * ε * xh := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hε.le) hx
    have hj1 := hjnn y (-γ - 1)
    calc _ ≤ (p + 1) * A * ε * xh * (S * jb y ^ (-γ - 1)) := by
          apply mul_le_mul_of_nonneg_left _ c0
          rw [hS, e2]
          have t1 := mul_le_mul_of_nonneg_left e1 h2p
          have t2 := mul_le_mul_of_nonneg_left e3 hTI
          linarith only [t1, t2]
      _ = (p + 1) * A * ε * xh * S * jb y ^ (-γ - 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hS' hj1
  · simp only [b_eps, c08_phi_b]
    rw [if_neg (by linarith)]

/-- Helper: `c08_phi_b p c` is `C¹`. -/
theorem c10_aux_phi_b_contDiff (p c : ℝ) : ContDiff ℝ 1 (c08_phi_b p c) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hχ : ContDiff ℝ 1 chiPlus := by
    unfold chiPlus
    exact (Real.smoothTransition.contDiff (n := 1)).comp (contDiff_id.sub contDiff_const)
  rcases lt_or_ge y 1 with hy | hy
  · have hev : c08_phi_b p c =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hy] with x hx
      simp only [c08_phi_b]
      rw [if_neg (not_lt.2 (le_of_lt hx))]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : c08_phi_b p c =ᶠ[nhds y] fun x => c * chiPlus x * x ^ (-p) := by
      filter_upwards [Ioi_mem_nhds (show (1 / 2 : ℝ) < y by linarith)] with x hx
      simp only [c08_phi_b]
      split_ifs with h
      · rfl
      · have : chiPlus x = 0 := by
          unfold chiPlus; exact Real.smoothTransition.zero_of_nonpos (by linarith [not_lt.1 h])
        rw [this]; ring
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (contDiffAt_const.mul hχ.contDiffAt).mul
      (Real.contDiffAt_rpow_const_of_ne (by linarith))

/-- Helper: bounds for `b_ε h'` and its derivative on `(-2,2)`. -/
theorem c10_aux_b_compact (p : ℝ) :
    ∃ Mb > 0, ∀ ε : ℝ, ∀ h : ℝ → ℝ, W2inftyLoc h → ∀ y ∈ Ioo (-2 : ℝ) 2,
      |b_eps p ε y| ≤ Mb * |c_eps p ε| ∧ (DifferentiableAt ℝ (deriv h) y →
      |b_eps p ε y * deriv h y| + |deriv (fun x => b_eps p ε x * deriv h x) y| ≤
        Mb * |c_eps p ε| * (|deriv h y| + |deriv (deriv h) y|)) := by
  have hφ := c10_aux_phi_b_contDiff p 1
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hφ.continuous.continuousOn (s := Icc (-2 : ℝ) 2))
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hφ.continuous_deriv le_rfl).continuousOn (s := Icc (-2 : ℝ) 2))
  have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 ⟨by norm_num, by norm_num⟩)
  have hM2' : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨2 * (M1 + M2) + 1, by positivity, fun ε h hh y hy => ?_⟩
  set c := c_eps p ε
  have hb : b_eps p ε = fun x => c * c08_phi_b p 1 x := by
    funext x; simp only [b_eps, c08_phi_b, c]; split_ifs <;> ring
  have hyI : y ∈ Icc (-2 : ℝ) 2 := Ioo_subset_Icc_self hy
  have b1 : |c08_phi_b p 1 y| ≤ M1 := by have := hM1 y hyI; rwa [Real.norm_eq_abs] at this
  have b2 : |deriv (c08_phi_b p 1) y| ≤ M2 := by have := hM2 y hyI; rwa [Real.norm_eq_abs] at this
  refine ⟨by
    rw [hb]; simp only; rw [abs_mul]
    calc |c| * |c08_phi_b p 1 y| ≤ |c| * M1 := mul_le_mul_of_nonneg_left b1 (abs_nonneg _)
      _ ≤ (2 * (M1 + M2) + 1) * |c| := by nlinarith [abs_nonneg c], fun hd => ?_⟩
  have hder : HasDerivAt (fun x => b_eps p ε x * deriv h x)
      (c * deriv (c08_phi_b p 1) y * deriv h y + c * c08_phi_b p 1 y * deriv (deriv h) y) y := by
    rw [hb]
    have h1 : HasDerivAt (fun x => c * c08_phi_b p 1 x) (c * deriv (c08_phi_b p 1) y) y :=
      ((hφ.differentiable one_ne_zero) y).hasDerivAt.const_mul c
    have h2 : HasDerivAt (fun x => c * c08_phi_b p 1 x * deriv h x)
        (c * deriv (c08_phi_b p 1) y * deriv h y + c * c08_phi_b p 1 y * deriv (deriv h) y) y :=
      h1.mul hd.hasDerivAt
    exact h2
  rw [hder.deriv, hb]
  simp only
  have hc := abs_nonneg c
  have ha := abs_nonneg (deriv h y)
  have ha2 := abs_nonneg (deriv (deriv h) y)
  calc |c * c08_phi_b p 1 y * deriv h y| +
        |c * deriv (c08_phi_b p 1) y * deriv h y + c * c08_phi_b p 1 y * deriv (deriv h) y|
      ≤ |c| * M1 * |deriv h y| + (|c| * M2 * |deriv h y| + |c| * M1 * |deriv (deriv h) y|) := by
        refine add_le_add ?_ ((abs_add_le _ _).trans (add_le_add ?_ ?_))
        · rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b1 hc) ha
        · rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b2 hc) ha
        · rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b1 hc) ha2
    _ ≤ (2 * (M1 + M2) + 1) * |c| * (|deriv h y| + |deriv (deriv h) y|) := by
        have := mul_nonneg hc ha; have := mul_nonneg hc ha2
        have := mul_nonneg (mul_nonneg hc ha) hM1'; have := mul_nonneg (mul_nonneg hc ha) hM2'
        have := mul_nonneg (mul_nonneg hc ha2) hM1'; have := mul_nonneg (mul_nonneg hc ha2) hM2'
        nlinarith

/-- Helper: a kernel dominated by a translated envelope is integrable, with integral bound. -/
theorem c10_aux_env_int {F ω : ℝ → ℝ} (hF : Measurable F) (hω : Integrable ω) {A y : ℝ}
    (hb : ∀ z, |F z| ≤ A * ω (y - z)) :
    Integrable F ∧ (∫ z, |F z|) ≤ A * ∫ s, ω s := by
  have hi : Integrable (fun z => A * ω (y - z)) := (hω.comp_sub_left y).const_mul A
  have hFi : Integrable F := Integrable.mono' hi hF.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)
  refine ⟨hFi, ?_⟩
  calc (∫ z, |F z|) ≤ ∫ z, A * ω (y - z) := integral_mono hFi.abs hi hb
    _ = A * ∫ s, ω s := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun s => ω s) volume y]

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_N3_compact.  The compact region `|y| < 2` (derivative statements for
a.e. `y`): integrand bounds, integral bounds, bounds on `b_ε h'`, and the resulting bounds on
`D𝒩₃(r)[h]` and its derivative. -/
theorem c10_N3_compact (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      (∀ y z : ℝ, |y| < 2 →
        |c10_N3_linearization_K p ε (fbar + r) h y z| ≤
          C * ε * xNorm p γ h * min (|y - z| ^ 2) 1) ∧
      (∀ᵐ y, ∀ z : ℝ, |y| < 2 → z ≠ y →
        |deriv (fun y' => c10_N3_linearization_K p ε (fbar + r) h y' z) y| +
            |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ≤
          C * ε * xNorm p γ h * min |y - z| 1) ∧
      (∀ᵐ y, |y| < 2 →
        Integrable (fun z => |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ∧
        Integrable (fun z => |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ∧
        (∫ z, |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) +
            (∫ z, |c10_N3_linearization_dK p ε (fbar + r) h y z| / |y - z| ^ (p + 1)) ≤
          C * ε * xNorm p γ h) ∧
      (∀ᵐ y, |y| < 2 →
        |b_eps p ε y * deriv h y| + |deriv (fun x => b_eps p ε x * deriv h x) y| ≤
          C * ε * xNorm p γ h) ∧
      (∀ y : ℝ, |y| < 2 →
        |c10_N3_linearization p ε fbar r h y| ≤ C * ε * xNorm p γ h * jb y ^ (-γ)) ∧
      (∀ᵐ y, |y| < 2 →
        |deriv (c10_N3_linearization p ε fbar r h) y| ≤
          C * ε * xNorm p γ h * min (jb y ^ (-γ + 1 / p)) (jb y ^ (-γ - 1))) := by
  obtain ⟨hp0, hγp, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨Cpc, hCpc, hPC⟩ := c10_profile_consequences p γ M N hp hp1 hγ hM hN
  set B := Cpc + 1
  set L := 5 * Cpc + 1
  have hB : 1 ≤ B := by simp only [B]; linarith
  have hL : 1 ≤ L := by simp only [L]; linarith
  obtain ⟨Cv, hCv, hV⟩ := c10_variation_kernel_bounds p hp0 hp1 B L hB hL
  obtain ⟨Ck, hCk, hk⟩ := c10_aux_kernel_bounds p B hp0 hp1 hB
  obtain ⟨o0, o1, -, -, io0, io1, -⟩ := c10_kernel_envelopes (p + 1) (by linarith) (by linarith)
  obtain ⟨Mb, hMb, hbB⟩ := c10_aux_b_compact p
  set I0 := ∫ s, c10_local_kernel_pair_omega0 (p + 1) s
  set I1 := ∫ s, c10_local_kernel_pair_omega1 (p + 1) s
  have hI0 : 0 ≤ I0 := integral_nonneg o0
  have hI1 : 0 ≤ I1 := integral_nonneg o1
  set K0 := Cv * 125
  have hK0 : 0 < K0 := by positivity
  set Mbh := Mb * (1 + 10 ^ (2 / p))
  have hMbh : 0 < Mbh := by positivity
  set Q := K0 * (I0 + I1 + 1) + Mbh
  have hQ : 0 < Q := by positivity
  have h4 : (0 : ℝ) < 4 ^ (γ + 1) := by positivity
  refine ⟨Q * 4 ^ (γ + 1) + 1, by positivity, ?_⟩
  set C := Q * 4 ^ (γ + 1) + 1
  have h41 : 1 ≤ (4 : ℝ) ^ (γ + 1) := Real.one_le_rpow (by norm_num) (by linarith)
  have hCQ : Q ≤ C := by simp only [C]; nlinarith
  have hCK : K0 ≤ C := by
    have : K0 ≤ Q := by simp only [Q]; nlinarith
    linarith
  intro ε hε hε1 fbar hf r hr hrN h hh
  obtain ⟨item1, -, i2b, -, i3b, -, item4⟩ := hPC fbar hf r hr hrN
  obtain ⟨hf1, -, -, -⟩ := item1 (fbar + r) (by simp)
  obtain ⟨-, -, -, -, hh2p, hh2m, hh1, hh2loc⟩ := item4 h hh
  set xh := xNorm p γ h
  have hxh : 0 ≤ xh := ENNReal.toReal_nonneg
  set H0 := 125 * xh
  have hH0 : 0 ≤ H0 := by positivity
  -- regularity of `f = f̄ + r`
  have hfA : fbar ∈ c01_admissible_class :=
    c10_aux_C2_admissible_class hf.1 (c10_aux_admissible_deriv_bdd p M hp0 hf)
  have hrA := c10_aux_X_admissible_class p γ hp hp1 hγ hr
  obtain ⟨hfW, -, -, -⟩ := c10_aux_lin_W2 (f := fbar) (h := r) ⟨hfA.1, hfA.2.2⟩ ⟨hrA.1, hrA.2.2⟩ 1
  rw [one_smul] at hfW
  have hfB : ∀ y, |deriv (fbar + r) y| ≤ B := fun y => (hf1 y).trans (by simp only [B]; linarith)
  have hjb4 : ∀ y : ℝ, |y| ≤ 4 → jb y ≤ 5 := fun y hy => by
    unfold jb
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith [sq_abs y, abs_nonneg y]
  have hβ : -beta p + 1 / p ≤ 1 := by
    unfold beta; rw [show -((p + 1) / (2 * p)) + 1 / p = (1 - p) / (2 * p) by field_simp; ring]
    rw [div_le_one (by linarith)]; linarith
  have hf2 : ∀ᵐ y, y ∈ Icc (-2 - 2 : ℝ) (2 + 2) → |deriv (deriv (fbar + r)) y| ≤ L := by
    filter_upwards [i2b, i3b] with y h1 h2 hy
    have hy4 : |y| ≤ 4 := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rcases le_total 0 y with hy0 | hy0
    · calc _ ≤ Cpc * jb y ^ (-beta p + 1 / p) := h1 hy0
        _ ≤ Cpc * jb y ^ (1 : ℝ) := mul_le_mul_of_nonneg_left (c10_aux_jb_rpow_mono y hβ) hCpc.le
        _ ≤ Cpc * 5 := by rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left (hjb4 y hy4) hCpc.le
        _ ≤ L := by simp only [L]; linarith
    · calc _ ≤ Cpc * jb y ^ (-p - 2) := h2 hy0
        _ ≤ Cpc * 1 := mul_le_mul_of_nonneg_left (c10_aux_jb_rpow_le_one y (by linarith)) hCpc.le
        _ ≤ L := by simp only [L]; linarith
  have hh2 : ∀ᵐ y, y ∈ Icc (-2 - 2 : ℝ) (2 + 2) → |deriv (deriv h) y| ≤ H0 := by
    filter_upwards [hh2p, hh2m] with y h1 h2 hy
    have hy4 : |y| ≤ 4 := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hj5 := hjb4 y hy4
    have hj3 : jb y ^ (3 : ℝ) ≤ 125 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc jb y ^ 3 ≤ 5 ^ 3 := pow_le_pow_left₀ (c10_aux_jb_pos y).le hj5 3
        _ = 125 := by norm_num
    rcases le_total 0 y with hy0 | hy0
    · have he : -γ + 2 / p ≤ 3 := by
        have : 2 / p ≤ 8 / 3 := by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
        linarith
      calc _ ≤ xh * jb y ^ (-γ + 2 / p) := h1 hy0
        _ ≤ xh * jb y ^ (3 : ℝ) := mul_le_mul_of_nonneg_left (c10_aux_jb_rpow_mono y he) hxh
        _ ≤ xh * 125 := mul_le_mul_of_nonneg_left hj3 hxh
        _ = H0 := by simp only [H0]; ring
    · calc _ ≤ xh * jb y ^ (-γ - 2) := h2 hy0
        _ ≤ xh * 1 := mul_le_mul_of_nonneg_left (c10_aux_jb_rpow_le_one y (by linarith)) hxh
        _ ≤ H0 := by simp only [H0]; linarith
  have hhH : ∀ y, |deriv h y| ≤ H0 := fun y => (hh1 y).trans (by simp only [H0]; linarith)
  obtain ⟨hpair, hKb, hDb⟩ := hV 2 (by norm_num) ε hε.le hε1 H0 hH0 (fbar + r) h hfW hh.1 hfB
    hhH hf2 hh2
  have hK0e : Cv * ε * H0 = K0 * ε * xh := by simp only [H0, K0]; ring
  rw [hK0e] at hpair hKb hDb
  obtain ⟨-, -, hdiag, -, hHb, E, hE0, hJb⟩ := hpair
  have hIoo : ∀ y : ℝ, |y| < 2 → y ∈ Ioo (-2 : ℝ) 2 := fun y hy => abs_lt.1 hy
  have hKK : ∀ y : ℝ, c10_N3_linearization_K p ε (fbar + r) h y y = 0 := fun y => by
    obtain ⟨-, -, -, -, -, b2v, bs, -, -⟩ := hk ε hε.le hε1 (deriv (fbar + r) y)
      (deriv (fbar + r) y) (hfB y) (hfB y)
    simp only [sub_self, abs_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at b2v bs
    have d2 := abs_nonpos_iff.1 b2v
    have d1 : c10_N_pieces_Gamma_d1 p ε (deriv (fbar + r) y) (deriv (fbar + r) y) = 0 := by
      have := abs_nonpos_iff.1 bs; linarith
    unfold c10_N3_linearization_K
    have hs : c01_secant (fbar + r) y y = deriv (fbar + r) y := by simp [c01_secant]
    rw [hs, d1, d2]; ring
  have hcε : |c_eps p ε| ≤ ε := (c08_aux_c_eps_bound p ε hp hp1 hε.le).2
  -- integrability and integral bounds of the value and derivative kernels
  have hHall : ∀ y : ℝ, |y| < 2 → ∀ z, |c10_N3_linearization_K p ε (fbar + r) h y z /
      |y - z| ^ (p + 1)| ≤ K0 * ε * xh * c10_local_kernel_pair_omega0 (p + 1) (y - z) := by
    intro y hy z
    by_cases hz : z = y
    · subst hz; rw [hKK, zero_div, abs_zero]
      exact mul_nonneg (by positivity) (o0 _)
    · exact hHb y (hIoo y hy) z hz
  have hJall : ∀ y : ℝ, |y| < 2 → y ∉ E → ∀ z, |c10_N3_linearization_dK p ε (fbar + r) h y z /
      |y - z| ^ (p + 1)| ≤ K0 * ε * xh * c10_local_kernel_pair_omega1 (p + 1) (y - z) := by
    intro y hy hyE z
    by_cases hz : z = y
    · subst hz
      have h0 : |z - z| ^ (p + 1) = 0 := by rw [sub_self, abs_zero, Real.zero_rpow (by linarith)]
      rw [h0, div_zero, abs_zero]
      exact mul_nonneg (by positivity) (o1 _)
    · exact hJb y ⟨hIoo y hy, hyE⟩ z hz
  have hKm : ∀ y, Measurable (fun z => c10_N3_linearization_K p ε (fbar + r) h y z) := fun y =>
    (c10_aux_K_meas p ε hp0 hp1 hε.le hfW.1.continuous hh.1.1.continuous y).1
  have hDm : ∀ y, Measurable (fun z => c10_N3_linearization_dK p ε (fbar + r) h y z) := fun y => by
    have hd := c10_aux_meas_slice (F := fun y z => deriv (fun y' =>
      c10_N3_linearization_K p ε (fbar + r) h y' z) y)
      (c10_aux_meas_deriv_param (K := fun y z => c10_N3_linearization_K p ε (fbar + r) h y z)
        (c10_aux_K_cont p ε hp0 hp1 hε.le hfW.1 hh.1.1)) y
    exact hd.sub ((measurable_const.mul (hKm y)).div (by fun_prop))
  have hpm : Measurable (fun z : ℝ => |0 - z|) := by fun_prop
  have intH := fun y hy => c10_aux_env_int (F := fun z => c10_N3_linearization_K p ε (fbar + r) h y z /
    |y - z| ^ (p + 1)) ((hKm y).div (by fun_prop)) io0 (hHall y hy)
  have hnotE : ∀ᵐ y, y ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
  have hab : ∀ (t : ℝ) (y z : ℝ), |t| / |y - z| ^ (p + 1) = |t / |y - z| ^ (p + 1)| := fun t y z => by
    rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  -- the `b_ε h'` bounds
  have hbh : ∀ᵐ y, |y| < 2 →
      |b_eps p ε y * deriv h y| + |deriv (fun x => b_eps p ε x * deriv h x) y| ≤ Mbh * ε * xh := by
    filter_upwards [c10_aux_ae_differentiableAt hh.1.2, hh2loc] with y hd h2 hy
    have hyI := hIoo y hy
    have hy3 : y ∈ Icc (-3 : ℝ) 3 := ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
    refine ((hbB ε h hh.1 y hyI).2 hd).trans ?_
    have e1 := hh1 y
    have e2 := h2 hy3
    calc Mb * |c_eps p ε| * (|deriv h y| + |deriv (deriv h) y|)
        ≤ Mb * ε * (xh + 10 ^ (2 / p) * xh) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hcε hMb.le) (add_le_add e1 e2)
            (by positivity) (by positivity)
      _ = Mbh * ε * xh := by simp only [Mbh]; ring
  -- variation formula
  have NV := c10_N3_variation p γ M ε hp hp1 hγ hM hε.le hε1 fbar hf r hr h hh
  -- lower bound for the weights on `|y| < 2`
  have hw : ∀ y : ℝ, |y| < 2 → (4 : ℝ) ^ (-γ - 1) ≤ min (jb y ^ (-γ + 1 / p)) (jb y ^ (-γ - 1)) ∧
      (4 : ℝ) ^ (-γ - 1) ≤ jb y ^ (-γ) := by
    intro y hy
    have hj : jb y ≤ 4 := c10_aux_jb_le_four (by linarith)
    have hj1 := c10_aux_one_le_jb y
    have a : (4 : ℝ) ^ (-γ - 1) ≤ jb y ^ (-γ - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hj (by linarith)
    refine ⟨le_min (a.trans (c10_aux_jb_rpow_mono y (by
      have : 0 < 1 / p := by positivity
      linarith))) a, a.trans (c10_aux_jb_rpow_mono y (by linarith))⟩
  have hCw : Q ≤ C * (4 : ℝ) ^ (-γ - 1) := by
    have e : (4 : ℝ) ^ (γ + 1) * (4 : ℝ) ^ (-γ - 1) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have : C * (4 : ℝ) ^ (-γ - 1) = Q + (4 : ℝ) ^ (-γ - 1) := by
      simp only [C]; rw [add_mul, mul_assoc, e]; ring
    rw [this]; linarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 4 by norm_num) (-γ - 1)]
  have hεx : 0 ≤ ε * xh := mul_nonneg hε.le hxh
  refine ⟨fun y z hy => ?_, ?_, ?_, ?_, fun y hy => ?_, ?_⟩
  · -- (1)
    by_cases hz : z = y
    · subst hz; rw [hKK]; simp
    · calc _ ≤ K0 * ε * xh * min (|y - z| ^ 2) 1 := hKb y (hIoo y hy) z hz
        _ ≤ C * ε * xh * min (|y - z| ^ 2) 1 := by
          apply mul_le_mul_of_nonneg_right _ (le_min (sq_nonneg _) zero_le_one)
          nlinarith
  · -- (2)
    filter_upwards [hDb] with y hy z hy2 hz
    have h1 := hy (hIoo y hy2) z hz
    have hpos : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hz))
    have h2 : |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| ≤
        (p + 1) * |c10_N3_linearization_K p ε (fbar + r) h y z| / |y - z| :=
      div_le_div_of_nonneg_right (by nlinarith [abs_nonneg (c10_N3_linearization_K p ε (fbar + r) h y z)])
        hpos.le
    calc _ ≤ K0 * ε * xh * min |y - z| 1 := by linarith
      _ ≤ C * ε * xh * min |y - z| 1 := by
          apply mul_le_mul_of_nonneg_right _ (le_min (abs_nonneg _) zero_le_one)
          nlinarith
  · -- (3)
    filter_upwards [hnotE] with y hyE hy
    obtain ⟨iH, bH⟩ := intH y hy
    obtain ⟨iJ, bJ⟩ := c10_aux_env_int (F := fun z => c10_N3_linearization_dK p ε (fbar + r) h y z /
      |y - z| ^ (p + 1)) ((hDm y).div (by fun_prop)) io1 (hJall y hy hyE)
    simp_rw [hab]
    refine ⟨iH.abs, iJ.abs, ?_⟩
    calc _ ≤ K0 * ε * xh * I0 + K0 * ε * xh * I1 := add_le_add bH bJ
      _ = K0 * (I0 + I1) * (ε * xh) := by ring
      _ ≤ C * (ε * xh) := by
          apply mul_le_mul_of_nonneg_right _ hεx
          have : K0 * (I0 + I1) ≤ Q := by simp only [Q]; nlinarith
          linarith
      _ = _ := by ring
  · -- (4)
    filter_upwards [hbh] with y hy hy2
    refine (hy hy2).trans ?_
    have h1 : Mbh ≤ Q := by simp only [Q]; nlinarith
    have h2 : Mbh ≤ C := by linarith
    nlinarith
  · -- (5)
    have hyI := hIoo y hy
    unfold c10_N3_linearization
    obtain ⟨iH, bH⟩ := intH y hy
    have hb1 := (hbB ε h hh.1 y hyI).1
    have hbv : |b_eps p ε y * deriv h y| ≤ Mbh * ε * xh := by
      rw [abs_mul]
      calc |b_eps p ε y| * |deriv h y| ≤ (Mb * ε) * xh :=
            mul_le_mul (hb1.trans (mul_le_mul_of_nonneg_left hcε hMb.le)) (hh1 y) (abs_nonneg _)
              (by positivity)
        _ ≤ Mbh * ε * xh := by
            have : Mb ≤ Mbh := by simp only [Mbh]; nlinarith [Real.rpow_nonneg (show (0:ℝ) ≤ 10 by norm_num) (2 / p)]
            nlinarith
    calc _ ≤ |∫ z, c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1)| +
          |b_eps p ε y * deriv h y| := abs_sub _ _
      _ ≤ K0 * ε * xh * I0 + Mbh * ε * xh :=
          add_le_add ((abs_integral_le_integral_abs).trans bH) hbv
      _ ≤ Q * (ε * xh) := by
          have : K0 * I0 + Mbh ≤ Q := by simp only [Q]; nlinarith
          nlinarith
      _ ≤ C * (4 : ℝ) ^ (-γ - 1) * (ε * xh) := mul_le_mul_of_nonneg_right hCw hεx
      _ ≤ C * jb y ^ (-γ) * (ε * xh) := by
          apply mul_le_mul_of_nonneg_right _ hεx
          exact mul_le_mul_of_nonneg_left (hw y hy).2 (by positivity)
      _ = _ := by ring
  · -- (6)
    filter_upwards [NV.2.2.2, hnotE, hbh] with y hNV hyE hb hy
    obtain ⟨-, hdeq⟩ := hNV
    rw [hdeq]
    obtain ⟨iJ, bJ⟩ := c10_aux_env_int (F := fun z => c10_N3_linearization_dK p ε (fbar + r) h y z /
      |y - z| ^ (p + 1)) ((hDm y).div (by fun_prop)) io1 (hJall y hy hyE)
    have hb' := hb hy
    calc _ ≤ |∫ z, c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1)| +
          |deriv (fun x => b_eps p ε x * deriv h x) y| := abs_sub _ _
      _ ≤ K0 * ε * xh * I1 + Mbh * ε * xh := by
          refine add_le_add ((abs_integral_le_integral_abs).trans bJ) ?_
          linarith [abs_nonneg (b_eps p ε y * deriv h y)]
      _ ≤ Q * (ε * xh) := by
          have : K0 * I1 + Mbh ≤ Q := by simp only [Q]; nlinarith
          nlinarith
      _ ≤ C * (4 : ℝ) ^ (-γ - 1) * (ε * xh) := mul_le_mul_of_nonneg_right hCw hεx
      _ ≤ C * min (jb y ^ (-γ + 1 / p)) (jb y ^ (-γ - 1)) * (ε * xh) := by
          apply mul_le_mul_of_nonneg_right _ hεx
          exact mul_le_mul_of_nonneg_left (hw y hy).1 (by positivity)
      _ = _ := by ring

/-! ### Conclusion for `𝒩₃` -/

/-- Helper: splitting an integral into the near region `|y-z| ≤ c` and the far region
`c ≤ |y-z|` (they overlap in a null set). -/
theorem c10_aux_split (F : ℝ → ℝ) (hF : Integrable F) (y c : ℝ) :
    ∫ z, F z = (∫ z in {z | |y - z| ≤ c}, F z) + ∫ z in {z | c ≤ |y - z|}, F z := by
  have hs : MeasurableSet {z : ℝ | |y - z| ≤ c} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [← integral_add_compl hs hF]
  congr 1
  refine setIntegral_congr_set ?_
  rw [ae_eq_set]
  constructor
  · have : {z : ℝ | |y - z| ≤ c}ᶜ \ {z | c ≤ |y - z|} = ∅ := by
      ext z; simp only [mem_diff, mem_compl_iff, mem_setOf_eq, not_le, mem_empty_iff_false,
        iff_false, not_and]
      intro h; exact not_lt.2 h.le
    rw [this, measure_empty]
  · refine measure_mono_null (t := {y - c, y + c}) ?_ ((Set.toFinite _).measure_zero _)
    intro z ⟨h1, h2⟩
    simp only [mem_compl_iff, mem_setOf_eq, not_not] at h1 h2
    have : |y - z| = c := le_antisymm h2 h1
    rcases abs_eq (by linarith [abs_nonneg (y - z)] : 0 ≤ c) |>.1 this with h | h
    · left; linarith
    · right; simp only [mem_singleton_iff]; linarith

/-- Helper: at `ε = 0` the kernel `Γ_0` vanishes identically. -/
theorem c10_aux_Gamma_zero (p u v : ℝ) : c10_N_pieces_Gamma p 0 u v = 0 := by
  simp [c10_N_pieces_Gamma, c03_Gamma_eps, c03_P_eps, A_eps]

/-- Helper: at `ε = 0`, `D𝒩₃(r)[h] = 0`. -/
theorem c10_aux_linearization_zero (p : ℝ) (fbar r h : ℝ → ℝ) :
    c10_N3_linearization p 0 fbar r h = 0 := by
  have hG : ∀ u v, c10_N_pieces_Gamma_d1 p 0 u v = 0 ∧ c10_N_pieces_Gamma_d2 p 0 u v = 0 := by
    intro u v
    simp only [c10_N_pieces_Gamma_d1, c10_N_pieces_Gamma_d2, c10_aux_Gamma_zero, deriv_const',
      and_self]
  have hb : ∀ y, b_eps p 0 y = 0 := by
    intro y
    simp [b_eps, c08_phi_b, c_eps, A_eps]
  funext y
  simp [c10_N3_linearization, c10_N3_linearization_K, hG, hb]

/-- Blueprint: lem:c10_N3_linearized_bound.  `D𝒩₃(r)[h] ∈ Y_γ` and
`‖D𝒩₃(r)[h]‖_{Y_γ} ≤ C ε ‖h‖_{X_γ}`, `C = C(p,γ,M,N)`. -/
theorem c10_N3_linearized_bound (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N → ∀ h ∈ X_gamma p γ,
      c10_N3_linearization p ε fbar r h ∈ Y_gamma p γ ∧
      yNorm p γ (c10_N3_linearization p ε fbar r h) ≤ C * ε * xNorm p γ h := by
  obtain ⟨hp0, -, hγ1, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨Cn, hCn, hnear⟩ := c10_N3_near p γ M N hp hp1 hγ hM hN
  obtain ⟨Cf, hCf, hfar⟩ := c10_N3_far_plus p γ M N hp hp1 hγ hM hN
  obtain ⟨Cm, hCm, hfarm⟩ := c10_N3_far_minus p γ M N hp hp1 hγ hM hN
  obtain ⟨Cc, hCc, hcomp⟩ := c10_N3_compact p γ M N hp hp1 hγ hM hN
  refine ⟨4 * (Cn + Cf + Cm + Cc), by positivity, fun ε hε hε1 fbar hf r hr hrN h hh => ?_⟩
  rcases eq_or_lt_of_le hε with h0 | hεpos
  · -- `ε = 0`
    subst h0
    rw [c10_aux_linearization_zero]
    have hz : Y_gamma_norm p γ (0 : ℝ → ℝ) = 0 := by
      simp [Y_gamma_norm]
      exact ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
    refine ⟨⟨LocallyLipschitz.const 0, by rw [hz]; exact ENNReal.zero_lt_top⟩, ?_⟩
    simp [yNorm, hz]
  obtain ⟨V1, -, ⟨VW, V3⟩⟩ := c10_N3_variation p γ M ε hp hp1 hγ hM hε hε1 fbar hf r hr h hh
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := hnear ε hεpos hε1 fbar hf r hr hrN h hh
  obtain ⟨f1, f2⟩ := hfar ε hεpos hε1 fbar hf r hr hrN h hh
  obtain ⟨-, -, m1, m2, m3⟩ := hfarm ε hεpos hε1 fbar hf r hr hrN h hh
  obtain ⟨-, -, -, -, k1, k2⟩ := hcomp ε hεpos hε1 fbar hf r hr hrN h hh
  set xh := xNorm p γ h
  have hx : 0 ≤ xh := ENNReal.toReal_nonneg
  set D := c10_N3_linearization p ε fbar r h with hD
  set A := (Cn + Cf + Cm + Cc) * ε * xh with hA
  have hA0 : 0 ≤ A := by positivity
  have hjnn : ∀ y (e : ℝ), 0 ≤ jb y ^ e := fun y e =>
    (Real.rpow_pos_of_pos (c10_aux_jb_pos y) e).le
  have hpow : ∀ y : ℝ, |y - y| ^ (p + 1) = 0 := fun y => by
    simp [Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  -- absolute value of a set integral of `F/|y-z|^α`
  have habs : ∀ (s : Set ℝ) (F : ℝ → ℝ) (y : ℝ),
      |∫ z in s, F z / |y - z| ^ (p + 1)| ≤ ∫ z in s, |F z| / |y - z| ^ (p + 1) := by
    intro s F y
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    congr 1; funext z; rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  -- bounds on `D` and `D'` in the three regions
  have b_pos : ∀ y : ℝ, 2 ≤ y → |D y| ≤ (Cn + Cf) * ε * xh * jb y ^ (-γ) := by
    intro y hy
    have hy' : 2 ≤ |y| := by rw [abs_of_nonneg (by linarith)]; exact hy
    have hsplit := c10_aux_split _ (V1 y) y (|y| / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y)] at hsplit
    simp only [hD, c10_N3_linearization]
    rw [hsplit]
    have e1 := habs {z | |y - z| ≤ y / 2} (c10_N3_linearization_K p ε (fbar + r) h y) y
    have e2 := n1 y hy
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y)] at e2
    have e3 := (f1 y hy).2
    calc _ = |(∫ z in {z | |y - z| ≤ y / 2}, c10_N3_linearization_K p ε (fbar + r) h y z /
            |y - z| ^ (p + 1)) + ((∫ z in {z | y / 2 ≤ |y - z|},
            c10_N3_linearization_K p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
            b_eps p ε y * deriv h y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ Cn * ε * xh * jb y ^ (-γ) + Cf * ε * xh * jb y ^ (-γ) := add_le_add (e1.trans e2) e3
      _ = _ := by ring
  have hb0 : ∀ y : ℝ, y ≤ -2 → deriv (fun x => b_eps p ε x * deriv h x) y = 0 := by
    intro y hy
    have hev : (fun x => b_eps p ε x * deriv h x) =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show y < 1 by linarith)] with x hx
      rw [m3 x hx.le, zero_mul]
    rw [hev.deriv_eq]; simp
  have b_neg : ∀ y : ℝ, y ≤ -2 → |D y| ≤ (Cn + Cm) * ε * xh * jb y ^ (-γ) := by
    intro y hy
    have hy' : 2 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    have hsplit := c10_aux_split _ (V1 y) y (|y| / 2)
    simp only [hD, c10_N3_linearization]
    rw [hsplit, m3 y (by linarith), zero_mul, sub_zero]
    have e1 := habs {z | |y - z| ≤ |y| / 2} (c10_N3_linearization_K p ε (fbar + r) h y) y
    have e2 := n2 y hy
    have e3 := habs {z | |y| / 2 ≤ |y - z|} (c10_N3_linearization_K p ε (fbar + r) h y) y
    have e4 := (m1 y hy).2
    have e5 : jb y ^ (-γ - 2 * p - 2) ≤ jb y ^ (-γ) := c10_aux_jb_rpow_mono y (by linarith)
    have e6 := mul_le_mul_of_nonneg_left e5 (by positivity : (0:ℝ) ≤ Cn * ε * xh)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ Cn * ε * xh * jb y ^ (-γ - 2 * p - 2) + Cm * ε * xh * jb y ^ (-γ) :=
          add_le_add (e1.trans e2) (e3.trans e4)
      _ ≤ Cn * ε * xh * jb y ^ (-γ) + Cm * ε * xh * jb y ^ (-γ) := by linarith
      _ = _ := by ring
  have d_pos : ∀ᵐ y, 2 ≤ y → |deriv D y| ≤ (Cn + Cf) * ε * xh * jb y ^ (-γ + 1 / p) := by
    filter_upwards [V3, n4, f2] with y v3 n4 f2 hy
    obtain ⟨vi, vd⟩ := v3
    have hsplit := c10_aux_split _ vi y (|y| / 2)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y)] at hsplit
    rw [hD, vd, hsplit]
    have e1 := habs {z | |y - z| ≤ y / 2} (c10_N3_linearization_dK p ε (fbar + r) h y) y
    have e2 := n4 hy
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y)] at e2
    have e3 := (f2 hy).2
    calc _ = |(∫ z in {z | |y - z| ≤ y / 2}, c10_N3_linearization_dK p ε (fbar + r) h y z /
            |y - z| ^ (p + 1)) + ((∫ z in {z | y / 2 ≤ |y - z|},
            c10_N3_linearization_dK p ε (fbar + r) h y z / |y - z| ^ (p + 1)) -
            deriv (fun x => b_eps p ε x * deriv h x) y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ Cn * ε * xh * jb y ^ (-γ + 1 / p) + Cf * ε * xh * jb y ^ (-γ + 1 / p) :=
          add_le_add (e1.trans e2) e3
      _ = _ := by ring
  have d_neg : ∀ᵐ y, y ≤ -2 → |deriv D y| ≤ (Cn + Cm) * ε * xh * jb y ^ (-γ - 1) := by
    filter_upwards [V3, n5, m2] with y v3 n5 m2 hy
    obtain ⟨vi, vd⟩ := v3
    have hsplit := c10_aux_split _ vi y (|y| / 2)
    rw [hD, vd, hsplit, hb0 y hy, sub_zero]
    have e1 := habs {z | |y - z| ≤ |y| / 2} (c10_N3_linearization_dK p ε (fbar + r) h y) y
    have e2 := n5 hy
    have e3 := habs {z | |y| / 2 ≤ |y - z|} (c10_N3_linearization_dK p ε (fbar + r) h y) y
    have e4 := (m2 hy).2
    have e5 : jb y ^ (-γ - 2 * p - 3) ≤ jb y ^ (-γ - 1) := c10_aux_jb_rpow_mono y (by linarith)
    have e6 := mul_le_mul_of_nonneg_left e5 (by positivity : (0:ℝ) ≤ Cn * ε * xh)
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ Cn * ε * xh * jb y ^ (-γ - 2 * p - 3) + Cm * ε * xh * jb y ^ (-γ - 1) :=
          add_le_add (e1.trans e2) (e3.trans e4)
      _ ≤ Cn * ε * xh * jb y ^ (-γ - 1) + Cm * ε * xh * jb y ^ (-γ - 1) := by linarith
      _ = _ := by ring
  have up : ∀ (B : ℝ) (y e : ℝ), 0 ≤ B → B ≤ Cn + Cf + Cm + Cc →
      B * ε * xh * jb y ^ e ≤ A * jb y ^ e := fun B y e hB hBle => by
    rw [hA]
    apply mul_le_mul_of_nonneg_right _ (hjnn y e)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBle hε) hx
  have key := c10_aux_Y_of_decay p γ A VW hA0
    (by
      filter_upwards [d_pos, k2] with y dp k2 hy
      rcases le_or_gt 2 y with h2 | h2
      · exact ⟨(b_pos y h2).trans (up _ y _ (by positivity) (by linarith)),
          (dp h2).trans (up _ y _ (by positivity) (by linarith))⟩
      · have hy2 : |y| < 2 := by rw [abs_lt]; constructor <;> linarith
        exact ⟨(k1 y hy2).trans (up _ y _ hCc.le (by linarith)),
          (k2 hy2).trans ((mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans
            (up _ y _ hCc.le (by linarith)))⟩)
    (by
      filter_upwards [d_neg, k2] with y dn k2 hy
      rcases le_or_gt y (-2) with h2 | h2
      · exact ⟨(b_neg y h2).trans (up _ y _ (by positivity) (by linarith)),
          (dn h2).trans (up _ y _ (by positivity) (by linarith))⟩
      · have hy2 : |y| < 2 := by rw [abs_lt]; constructor <;> linarith
        exact ⟨(k1 y hy2).trans (up _ y _ hCc.le (by linarith)),
          (k2 hy2).trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
            (up _ y _ hCc.le (by linarith)))⟩)
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  rw [hA]; ring

/-! ### Continuity in the profile -/

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_Ieps_local.  `ℐ_ε(g) ∈ W^{1,∞}_loc` with derivative
`∫ K⁽¹⁾_g(y,z)|y-z|^{-α} dz` (absolutely convergent a.e.), and the local bounds near the diagonal
and far away (with `‖g'‖_{L^∞} ≤ L`, `‖g''‖_{L^∞([-2R,2R])} ≤ L`). -/
theorem c10_Ieps_local (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    (∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ g : ℝ → ℝ, W2inftyLoc g → (∃ L : ℝ, ∀ y, |deriv g y| ≤ L) →
      W1inftyLoc (c10_N_pieces_I p ε g) ∧
      ∀ᵐ y, Integrable (fun z => c10_Ieps_local_K1 p ε g y z / |y - z| ^ (p + 1)) ∧
        deriv (c10_N_pieces_I p ε g) y = ∫ z, c10_Ieps_local_K1 p ε g y z / |y - z| ^ (p + 1)) ∧
    (∀ R : ℝ, 1 ≤ R → ∀ L : ℝ, 0 ≤ L → ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ g : ℝ → ℝ, W2inftyLoc g → (∀ y, |deriv g y| ≤ L) →
      (∀ᵐ y, y ∈ Icc (-2 * R) (2 * R) → |deriv (deriv g) y| ≤ L) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        (∀ y ∈ Icc (-R) R,
          IntegrableOn (fun z => |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)| /
            |y - z| ^ (p + 1)) {z | |y - z| < δ} ∧
          (∫ z in {z | |y - z| < δ},
            |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)| / |y - z| ^ (p + 1)) ≤
            C * ε * δ ^ (3 - (p + 1))) ∧
        (∀ᵐ y, y ∈ Icc (-R) R →
          IntegrableOn (fun z => |c10_Ieps_local_K1 p ε g y z| / |y - z| ^ (p + 1))
            {z | |y - z| < δ} ∧
          (∫ z in {z | |y - z| < δ}, |c10_Ieps_local_K1 p ε g y z| / |y - z| ^ (p + 1)) ≤
            C * ε * δ ^ (2 - (p + 1))) ∧
        (∀ y ∈ Icc (-R) R, ∀ z : ℝ, 4 * R < |y - z| →
          |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)| +
              |c10_Ieps_local_K1 p ε g y z| ≤ C * ε ∧
          2 / 3 * |z| ≤ |y - z|)) := by
  have hp0 : 0 < p := by linarith
  have hα : 1 < p + 1 := by linarith
  have hα2 : p + 1 < 2 := by linarith
  obtain ⟨o0, o1, mo0, mo1, io0, io1, -, -, vtr⟩ := c10_kernel_envelopes (p + 1) hα hα2
  constructor
  · intro ε hε hε1 g hg ⟨L0, hL0⟩
    set B := max L0 1
    have hB : 1 ≤ B := le_max_right _ _
    have hgB : ∀ y, |deriv g y| ≤ B := fun y => (hL0 y).trans (le_max_left _ _)
    have hI : c10_N_pieces_I p ε g = fun y => ∫ z, c10_N_pieces_Gamma p ε (deriv g y)
        (c01_secant g y z) / |y - z| ^ (p + 1) := by funext y; rfl
    have per : ∀ n : ℕ, LocallyLipschitzOn (Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1))
          (fun y => ∫ z, c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / |y - z| ^ (p + 1)) ∧
        ∀ᵐ y, y ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) →
          Integrable (fun z => c10_Ieps_local_K1 p ε g y z / |y - z| ^ (p + 1)) ∧
          HasDerivAt (fun y => ∫ z, c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) /
            |y - z| ^ (p + 1)) (∫ z, c10_Ieps_local_K1 p ε g y z / |y - z| ^ (p + 1)) y := by
      intro n
      set R : ℝ := (n : ℝ) + 1
      have hR : 1 ≤ R := by simp only [R]; linarith [n.cast_nonneg (α := ℝ)]
      obtain ⟨K, hK1, hK⟩ := c10_aux_loc_deriv_bound hg.2 (R + 3)
      have h2 : ∀ᵐ y, y ∈ Icc (-R - 2) (R + 2) → |deriv (deriv g) y| ≤ K :=
        Eventually.of_forall fun x hx => hK x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      obtain ⟨Cp, hCp, hP⟩ := c10_profile_kernel_bounds p hp0 hp1 B K hB hK1
      have hpair := (hP R hR ε hε hε1 g hg hgB (Or.inl h2)).1
      have hU : (Ioo (-R) R).Nonempty := ⟨0, by constructor <;> linarith⟩
      obtain ⟨-, hJi, -, hLL, hD⟩ := c10_aux_pair_integral (p + 1) hα hα2 (Ioo (-R) R) isOpen_Ioo
        ordConnected_Ioo hU (Cp * ε) (mul_nonneg hCp.le hε) _ _ hpair
      refine ⟨hLL, ?_⟩
      filter_upwards [hJi, hD] with y h1 h2 hy using ⟨h1 hy, h2 hy⟩
    refine ⟨?_, ?_⟩
    · rw [W1inftyLoc, hI]; exact c10_aux_locLip_of_Ioo fun n => (per n).1
    · have hall := ae_all_iff.2 fun n => (per n).2
      filter_upwards [hall] with y hy
      obtain ⟨n, hn⟩ := exists_nat_gt |y|
      have hyI : y ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
        constructor <;> linarith [neg_abs_le y, le_abs_self y]
      obtain ⟨hi, hd⟩ := hy n hyI
      exact ⟨hi, by rw [hI]; exact hd.deriv⟩
  · intro R hR L hL
    set B := max L 1
    have hB : 1 ≤ B := le_max_right _ _
    obtain ⟨Cp, hCp, hP⟩ := c10_profile_kernel_bounds p hp0 hp1 B B hB hB
    obtain ⟨Ck, hCk, hk⟩ := c10_aux_Gamma_quad p B hp0 hp1 hB
    set Cst := B ^ 3 + 4 * B ^ 2 + B + 12 * B ^ 2
    have hCst : 0 ≤ Cst := by positivity
    have h2p : 0 < 2 - p := by linarith
    have h1p : 0 < 1 - p := by linarith
    refine ⟨Cp * 2 / (2 - p) + Cp * 2 / (1 - p) + 2 * Ck * Cst + 1, by positivity, ?_⟩
    intro ε hε hε1 g hg hgL hg2 δ hδ hδ1
    have hgB : ∀ y, |deriv g y| ≤ B := fun y => (hgL y).trans (le_max_left _ _)
    have hg2B : ∀ᵐ y, y ∈ Icc (-2 * R) (2 * R) → |deriv (deriv g) y| ≤ B := by
      filter_upwards [hg2] with y hy hyI using (hy hyI).trans (le_max_left _ _)
    obtain ⟨-, Hb, Jb⟩ := hP R hR ε hε hε1 g hg hgB (Or.inr hg2B)
    have hpow : ∀ y z : ℝ, 0 ≤ |y - z| ^ (p + 1) := fun y z => Real.rpow_nonneg (abs_nonneg _) _
    have hS : MeasurableSet {s : ℝ | |s| < δ} := measurableSet_lt (by fun_prop) measurable_const
    have hSz : ∀ y : ℝ, MeasurableSet {z : ℝ | |y - z| < δ} := fun y =>
      measurableSet_lt (by fun_prop) measurable_const
    -- generic estimate over the near set
    have near : ∀ (y : ℝ) (F : ℝ → ℝ) (ω : ℝ → ℝ) (A : ℝ), Measurable F → Integrable ω →
        (∀ z, z ≠ y → |F z / |y - z| ^ (p + 1)| ≤ A * ω (y - z)) → (∀ s, 0 ≤ ω s) → 0 ≤ A →
        (∀ z, |F z| / |y - z| ^ (p + 1) = |F z / |y - z| ^ (p + 1)|) →
        IntegrableOn (fun z => |F z| / |y - z| ^ (p + 1)) {z | |y - z| < δ} ∧
        (∫ z in {z | |y - z| < δ}, |F z| / |y - z| ^ (p + 1)) ≤
          A * ∫ s in {s : ℝ | |s| < δ}, ω s := by
      intro y F ω A hFm hω hb hω0 hA heq
      have hb' : ∀ z, |F z| / |y - z| ^ (p + 1) ≤ A * ω (y - z) := by
        intro z
        by_cases hz : z = y
        · subst hz
          rw [sub_self, abs_zero, Real.zero_rpow (by linarith), div_zero]
          exact mul_nonneg hA (hω0 _)
        · rw [heq]; exact hb z hz
      have hint : Integrable (fun z => A * ω (y - z)) := (hω.comp_sub_left y).const_mul A
      have hmeas : Measurable (fun z => |F z| / |y - z| ^ (p + 1)) :=
        hFm.abs.div (by fun_prop)
      have hI1 : Integrable (fun z => |F z| / |y - z| ^ (p + 1)) :=
        Integrable.mono' hint hmeas.aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) (hpow y z))]; exact hb' z)
      refine ⟨hI1.integrableOn, ?_⟩
      calc (∫ z in {z | |y - z| < δ}, |F z| / |y - z| ^ (p + 1))
          ≤ ∫ z in {z | |y - z| < δ}, A * ω (y - z) :=
            setIntegral_mono_on hI1.integrableOn hint.integrableOn (hSz y) fun z _ => hb' z
        _ = A * ∫ s in {s : ℝ | |s| < δ}, ω s := by
            rw [integral_const_mul]
            congr 1
            exact (c10_aux_translate ω y hS).1
    have hδp : ∀ q : ℝ, 0 ≤ δ ^ q := fun q => Real.rpow_nonneg hδ.le q
    refine ⟨fun y hy => ?_, ?_, fun y hy z hz => ?_⟩
    · have hFm : Measurable (fun z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)) :=
        c10_aux_meas_slice (F := fun y z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z))
          (c10_aux_Gamma_cont p ε hp0 hp1 hε hg.1).measurable y
      obtain ⟨hi, hle⟩ := near y _ _ (Cp * ε) hFm io0 (fun z hz => Hb y hy z hz) o0
        (mul_nonneg hCp.le hε) (fun z => by rw [abs_div, abs_of_nonneg (hpow y z)])
      refine ⟨hi, hle.trans ?_⟩
      rw [(vtr δ hδ hδ1.le).1, show (3 : ℝ) - (p + 1) = 2 - p by ring]
      have hc : Cp * 2 / (2 - p) ≤ Cp * 2 / (2 - p) + Cp * 2 / (1 - p) + 2 * Ck * Cst + 1 := by
        have : 0 ≤ Cp * 2 / (1 - p) := by positivity
        have : 0 ≤ 2 * Ck * Cst := by positivity
        linarith
      calc Cp * ε * (2 * δ ^ (2 - p) / (2 - p)) = Cp * 2 / (2 - p) * (ε * δ ^ (2 - p)) := by
            field_simp
        _ ≤ (Cp * 2 / (2 - p) + Cp * 2 / (1 - p) + 2 * Ck * Cst + 1) * (ε * δ ^ (2 - p)) :=
            mul_le_mul_of_nonneg_right hc (mul_nonneg hε (hδp _))
        _ = _ := by ring
    · filter_upwards [Jb] with y hJ hy
      have hFm : Measurable (fun z => c10_Ieps_local_K1 p ε g y z) :=
        c10_aux_meas_slice (F := fun y z => c10_Ieps_local_K1 p ε g y z)
          (c10_aux_K1_meas p ε hp0 hp1 hε hg.1) y
      obtain ⟨hi, hle⟩ := near y _ _ (Cp * ε) hFm io1 (fun z hz => hJ hy z hz) o1
        (mul_nonneg hCp.le hε) (fun z => by rw [abs_div, abs_of_nonneg (hpow y z)])
      refine ⟨hi, hle.trans ?_⟩
      rw [(vtr δ hδ hδ1.le).2, show (2 : ℝ) - (p + 1) = 1 - p by ring]
      have hc : Cp * 2 / (1 - p) ≤ Cp * 2 / (2 - p) + Cp * 2 / (1 - p) + 2 * Ck * Cst + 1 := by
        have : 0 ≤ Cp * 2 / (2 - p) := by positivity
        have : 0 ≤ 2 * Ck * Cst := by positivity
        linarith
      calc Cp * ε * (2 * δ ^ (1 - p) / (1 - p)) = Cp * 2 / (1 - p) * (ε * δ ^ (1 - p)) := by
            field_simp
        _ ≤ (Cp * 2 / (2 - p) + Cp * 2 / (1 - p) + 2 * Ck * Cst + 1) * (ε * δ ^ (1 - p)) :=
            mul_le_mul_of_nonneg_right hc (mul_nonneg hε (hδp _))
        _ = _ := by ring
    · have hw : 1 < |y - z| := by linarith
      have hyz : y ≠ z := fun h => by rw [h, sub_self, abs_zero] at hw; linarith
      have sB : |c01_secant g y z| ≤ B :=
        ((c10_secant_identities g hg y z hyz).2.2.2.2 B hgB).2.trans (min_le_left _ _)
      obtain ⟨b1, b2v, bs, bG⟩ := hk ε hε hε1 (deriv g y) (c01_secant g y z) (hgB y) sB
      have hg2y : |deriv (deriv g) y| ≤ B :=
        c10_aux_d2_bound hg (zero_le_one.trans hB) hg2B y
          ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have := c10_aux_prof_alg (X := Ck * ε) (g2 := deriv (deriv g) y) (w := y - z) (p := p)
        (mul_nonneg hCk.le hε) hB hB (sub_ne_zero.2 hyz) hp0 hp1 b1 b2v bs bG (hgB y) sB hg2y
        (fun h => absurd h (not_le.2 hw))
      rw [min_eq_right (by nlinarith), min_eq_right hw.le] at this
      have hX : 0 ≤ Ck * ε * Cst := by positivity
      constructor
      · have e : c10_Ieps_local_K1 p ε g y z =
            c10_N_pieces_Gamma_d1 p ε (deriv g y) (c01_secant g y z) * deriv (deriv g) y +
              c10_N_pieces_Gamma_d2 p ε (deriv g y) (c01_secant g y z) *
                ((deriv g y - c01_secant g y z) / (y - z)) -
              (1 + p) * c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / (y - z) := rfl
        rw [e]
        have hc : 2 * Ck * Cst ≤ Cp * 2 / (2 - p) + Cp * 2 / (1 - p) + 2 * Ck * Cst + 1 := by
          have : 0 ≤ Cp * 2 / (2 - p) := by positivity
          have : 0 ≤ Cp * 2 / (1 - p) := by positivity
          linarith
        calc _ ≤ Ck * ε * Cst * 1 + Ck * ε * Cst * 1 := add_le_add this.1 this.2
          _ = 2 * Ck * Cst * ε := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hc hε
      · have h1 : |z| ≤ |y - z| + R := by
          have := abs_sub_abs_le_abs_sub z y
          rw [abs_sub_comm z y] at this
          linarith [abs_le.2 ⟨by linarith [hy.1], hy.2⟩, abs_nonneg y,
            (abs_le.2 ⟨by linarith [hy.1], hy.2⟩ : |y| ≤ R)]
        linarith

/-- Helper: two-variable Lipschitz bound from bounded partial derivatives on a square. -/
theorem c10_aux_lip2 {F Fu Fv : ℝ → ℝ → ℝ} {B M : ℝ}
    (hu : ∀ u v, |u| ≤ B → |v| ≤ B → HasDerivAt (fun u' => F u' v) (Fu u v) u)
    (hv : ∀ u v, |u| ≤ B → |v| ≤ B → HasDerivAt (fun v' => F u v') (Fv u v) v)
    (bu : ∀ u v, |u| ≤ B → |v| ≤ B → |Fu u v| ≤ M) (bv : ∀ u v, |u| ≤ B → |v| ≤ B → |Fv u v| ≤ M)
    {u0 u1 v0 v1 : ℝ} (hu0 : |u0| ≤ B) (hu1 : |u1| ≤ B) (hv0 : |v0| ≤ B) (hv1 : |v1| ≤ B) :
    |F u1 v1 - F u0 v0| ≤ M * (|u1 - u0| + |v1 - v0|) := by
  have hI : ∀ x, x ∈ Icc (-B) B ↔ |x| ≤ B := fun x => by rw [abs_le]; exact Iff.rfl
  have e1 : ‖F u1 v1 - F u0 v1‖ ≤ M * ‖u1 - u0‖ :=
    (convex_Icc (-B) B).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun u' => F u' v1)
      (f' := fun u => Fu u v1) (fun x hx => (hu x v1 ((hI x).1 hx) hv1).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact bu x v1 ((hI x).1 hx) hv1)
      ((hI u0).2 hu0) ((hI u1).2 hu1)
  have e2 : ‖F u0 v1 - F u0 v0‖ ≤ M * ‖v1 - v0‖ :=
    (convex_Icc (-B) B).norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun v' => F u0 v')
      (f' := fun v => Fv u0 v) (fun x hx => (hv u0 x hu0 ((hI x).1 hx)).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact bv u0 x hu0 ((hI x).1 hx))
      ((hI v0).2 hv0) ((hI v1).2 hv1)
  simp only [Real.norm_eq_abs] at e1 e2
  calc |F u1 v1 - F u0 v0| ≤ |F u1 v1 - F u0 v1| + |F u0 v1 - F u0 v0| := abs_sub_le _ _ _
    _ ≤ M * |u1 - u0| + M * |v1 - v0| := add_le_add e1 e2
    _ = _ := by ring

/-- Helper: Lipschitz bounds of `Γ_ε, ∂₁Γ_ε, ∂₂Γ_ε` on `[-B,B]²`. -/
theorem c10_aux_Gamma_lip (p B : ℝ) (hp : 0 < p) (hp1 : p < 1) (hB : 1 ≤ B) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ u0 u1 v0 v1 : ℝ, |u0| ≤ B → |u1| ≤ B → |v0| ≤ B →
      |v1| ≤ B →
      |c10_N_pieces_Gamma p ε u1 v1 - c10_N_pieces_Gamma p ε u0 v0| ≤
          C * ε * (|u1 - u0| + |v1 - v0|) ∧
      |c10_N_pieces_Gamma_d1 p ε u1 v1 - c10_N_pieces_Gamma_d1 p ε u0 v0| ≤
          C * ε * (|u1 - u0| + |v1 - v0|) ∧
      |c10_N_pieces_Gamma_d2 p ε u1 v1 - c10_N_pieces_Gamma_d2 p ε u0 v0| ≤
          C * ε * (|u1 - u0| + |v1 - v0|) ∧
      |c10_N_pieces_Gamma_d1 p ε u0 v0| ≤ C * ε ∧ |c10_N_pieces_Gamma_d2 p ε u0 v0| ≤ C * ε := by
  obtain ⟨Ck, hCk, hk⟩ := c10_aux_kernel_bounds p B hp hp1 hB
  refine ⟨Ck, hCk, fun ε hε hε1 u0 u1 v0 v1 hu0 hu1 hv0 hv1 => ?_⟩
  have cu : ∀ u v : ℝ, HasDerivAt (fun t => t) 1 u ∧ HasDerivAt (fun _ : ℝ => v) 0 u :=
    fun u v => ⟨hasDerivAt_id u, hasDerivAt_const u v⟩
  have Gu : ∀ u v, HasDerivAt (fun u' => c10_N_pieces_Gamma p ε u' v)
      (c10_N_pieces_Gamma_d1 p ε u v) u := fun u v => by
    have := c10_aux_Gamma_chain p ε hp hp1 hε (hasDerivAt_id u) (hasDerivAt_const u v)
    simpa using this
  have Gv : ∀ u v, HasDerivAt (fun v' => c10_N_pieces_Gamma p ε u v')
      (c10_N_pieces_Gamma_d2 p ε u v) v := fun u v => by
    have := c10_aux_Gamma_chain p ε hp hp1 hε (hasDerivAt_const v u) (hasDerivAt_id v)
    simpa using this
  have Du : ∀ u v, HasDerivAt (fun u' => c10_N_pieces_Gamma_d1 p ε u' v)
      (c10_N_pieces_Gamma_d11 p ε u v) u ∧ HasDerivAt (fun u' => c10_N_pieces_Gamma_d2 p ε u' v)
      (c10_N_pieces_Gamma_d12 p ε u v) u := fun u v => by
    obtain ⟨a, b⟩ := c10_aux_d_chain p ε hp hp1 hε (hasDerivAt_id u) (hasDerivAt_const u v)
    exact ⟨by simpa using a, by simpa using b⟩
  have Dv : ∀ u v, HasDerivAt (fun v' => c10_N_pieces_Gamma_d1 p ε u v')
      (c10_N_pieces_Gamma_d12 p ε u v) v ∧ HasDerivAt (fun v' => c10_N_pieces_Gamma_d2 p ε u v')
      (c10_N_pieces_Gamma_d22 p ε u v) v := fun u v => by
    obtain ⟨a, b⟩ := c10_aux_d_chain p ε hp hp1 hε (hasDerivAt_const v u) (hasDerivAt_id v)
    exact ⟨by simpa using a, by simpa using b⟩
  have K := fun u v (hu : |u| ≤ B) (hv : |v| ≤ B) => hk ε hε hε1 u v hu hv
  refine ⟨c10_aux_lip2 (fun u v _ _ => Gu u v) (fun u v _ _ => Gv u v)
      (fun u v hu hv => (K u v hu hv).1) (fun u v hu hv => (K u v hu hv).2.1) hu0 hu1 hv0 hv1,
    c10_aux_lip2 (fun u v _ _ => (Du u v).1) (fun u v _ _ => (Dv u v).1)
      (fun u v hu hv => (K u v hu hv).2.2.1) (fun u v hu hv => (K u v hu hv).2.2.2.1)
      hu0 hu1 hv0 hv1,
    c10_aux_lip2 (fun u v _ _ => (Du u v).2) (fun u v _ _ => (Dv u v).2)
      (fun u v hu hv => (K u v hu hv).2.2.2.1) (fun u v hu hv => (K u v hu hv).2.2.2.2.1)
      hu0 hu1 hv0 hv1, (K u0 v0 hu0 hv0).1, (K u0 v0 hu0 hv0).2.1⟩

/-- Helper: an a.e. bound on `[a,b]` makes the restricted `L^∞` norm finite. -/
theorem c10_aux_eLp_fin {φ : ℝ → ℝ} (hφ : Measurable φ) {a b C : ℝ}
    (h : ∀ᵐ x, x ∈ Icc a b → |φ x| ≤ C) : eLpNorm φ ⊤ (volume.restrict (Icc a b)) < ⊤ := by
  rw [eLpNorm_exponent_top hφ.aestronglyMeasurable.restrict]
  refine lt_of_le_of_lt (eLpNormEssSup_le_of_ae_bound (C := C) ?_) ENNReal.ofReal_lt_top
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h] with x hx hxI; rw [Real.norm_eq_abs]; exact hx hxI

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_Ieps_compact_difference.  For `0 < p < 1`, `R ≥ 1`, `S ≥ 5R`,
`0 < δ < 1`, `B, L ≥ 1` there is `C = C(p,R,S,δ,B,L)` such that for `0 ≤ ε ≤ 1` and
`g₀, g₁ ∈ W^{2,∞}_loc` with `‖g_j'‖_∞ ≤ B`, `‖g_j''‖_{L^∞[-S,S]} ≤ L`, writing
`e_S = ‖g₁-g₀‖_{L^∞[-S,S]} + ‖g₁'-g₀'‖_{L^∞[-S,S]} + ‖g₁''-g₀''‖_{L^∞[-S,S]}` and
`E_y = {z : |z| ≤ S, |y-z| ≥ δ}`: for every `|y| ≤ R` (resp. a.e. `|y| ≤ R`) and every measurable
`T ⊆ E_y`, the value-difference (resp. derivative-difference) absolute integrand is integrable on
`T` with integral `≤ C ε e_S`. (`T = E_y` gives the displayed sup/ess sup bounds.) -/
theorem c10_Ieps_compact_difference (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (R S δ B L : ℝ)
    (hR : 1 ≤ R) (hS : 5 * R ≤ S) (hδ : 0 < δ) (hδ1 : δ < 1) (hB : 1 ≤ B) (hL : 1 ≤ L) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ g₀ g₁ : ℝ → ℝ, W2inftyLoc g₀ → W2inftyLoc g₁ →
      (∀ y, |deriv g₀ y| ≤ B) → (∀ y, |deriv g₁ y| ≤ B) →
      (∀ᵐ y, y ∈ Icc (-S) S → |deriv (deriv g₀) y| ≤ L) →
      (∀ᵐ y, y ∈ Icc (-S) S → |deriv (deriv g₁) y| ≤ L) →
      (∀ y ∈ Icc (-R) R, ∀ T : Set ℝ, MeasurableSet T → T ⊆ {z | |z| ≤ S ∧ δ ≤ |y - z|} →
        IntegrableOn (fun z => |c10_N_pieces_Gamma p ε (deriv g₁ y) (c01_secant g₁ y z) -
            c10_N_pieces_Gamma p ε (deriv g₀ y) (c01_secant g₀ y z)| / |y - z| ^ (p + 1)) T ∧
        (∫ z in T, |c10_N_pieces_Gamma p ε (deriv g₁ y) (c01_secant g₁ y z) -
            c10_N_pieces_Gamma p ε (deriv g₀ y) (c01_secant g₀ y z)| / |y - z| ^ (p + 1)) ≤
          C * ε * (eLpNorm (fun x => g₁ x - g₀ x) ⊤ (volume.restrict (Icc (-S) S)) +
            eLpNorm (fun x => deriv g₁ x - deriv g₀ x) ⊤ (volume.restrict (Icc (-S) S)) +
            eLpNorm (fun x => deriv (deriv g₁) x - deriv (deriv g₀) x) ⊤
              (volume.restrict (Icc (-S) S))).toReal) ∧
      (∀ᵐ y, y ∈ Icc (-R) R → ∀ T : Set ℝ, MeasurableSet T →
        T ⊆ {z | |z| ≤ S ∧ δ ≤ |y - z|} →
        IntegrableOn (fun z => |c10_Ieps_local_K1 p ε g₁ y z - c10_Ieps_local_K1 p ε g₀ y z| /
            |y - z| ^ (p + 1)) T ∧
        (∫ z in T, |c10_Ieps_local_K1 p ε g₁ y z - c10_Ieps_local_K1 p ε g₀ y z| /
            |y - z| ^ (p + 1)) ≤
          C * ε * (eLpNorm (fun x => g₁ x - g₀ x) ⊤ (volume.restrict (Icc (-S) S)) +
            eLpNorm (fun x => deriv g₁ x - deriv g₀ x) ⊤ (volume.restrict (Icc (-S) S)) +
            eLpNorm (fun x => deriv (deriv g₁) x - deriv (deriv g₀) x) ⊤
              (volume.restrict (Icc (-S) S))).toReal) := by
  obtain ⟨Cg, hCg, hG⟩ := c10_aux_Gamma_lip p B hp hp1 hB
  have hS0 : 0 < S := by linarith
  have hδα : 0 < δ ^ (p + 1) := Real.rpow_pos_of_pos hδ _
  set c1 := Cg * (2 * L + 2 + (4 * B + 6) / δ) with hc1
  have hc1p : 0 < c1 := by positivity
  refine ⟨c1 / δ ^ (p + 1) * (2 * S), by positivity, ?_⟩
  intro ε hε hε1 g₀ g₁ hg₀ hg₁ hB₀ hB₁ hL₀ hL₁
  set μS := volume.restrict (Icc (-S) S)
  -- the three `L^∞` norms
  have hm0 : Measurable (fun x => g₁ x - g₀ x) := (hg₁.1.continuous.sub hg₀.1.continuous).measurable
  have hc1' : Continuous (fun x => deriv g₁ x - deriv g₀ x) :=
    (hg₁.1.continuous_deriv le_rfl).sub (hg₀.1.continuous_deriv le_rfl)
  have hm2 : Measurable (fun x => deriv (deriv g₁) x - deriv (deriv g₀) x) :=
    (measurable_deriv _).sub (measurable_deriv _)
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hg₁.1.continuous.sub hg₀.1.continuous).continuousOn (s := Icc (-S) S))
  have f0 : eLpNorm (fun x => g₁ x - g₀ x) ⊤ μS < ⊤ :=
    c10_aux_eLp_fin hm0 (C := M0) (Eventually.of_forall fun x hx => by
      have := hM0 x hx; rwa [Real.norm_eq_abs] at this)
  have f1 : eLpNorm (fun x => deriv g₁ x - deriv g₀ x) ⊤ μS < ⊤ :=
    c10_aux_eLp_fin hc1'.measurable (C := 2 * B) (Eventually.of_forall fun x _ =>
      (abs_sub _ _).trans (by linarith [hB₀ x, hB₁ x]))
  have f2 : eLpNorm (fun x => deriv (deriv g₁) x - deriv (deriv g₀) x) ⊤ μS < ⊤ :=
    c10_aux_eLp_fin hm2 (C := 2 * L) (by
      filter_upwards [hL₀, hL₁] with x h0 h1 hx
      exact (abs_sub _ _).trans (by linarith [h0 hx, h1 hx]))
  set e0 := (eLpNorm (fun x => g₁ x - g₀ x) ⊤ μS).toReal
  set e1 := (eLpNorm (fun x => deriv g₁ x - deriv g₀ x) ⊤ μS).toReal
  set e2 := (eLpNorm (fun x => deriv (deriv g₁) x - deriv (deriv g₀) x) ⊤ μS).toReal
  have hes : (eLpNorm (fun x => g₁ x - g₀ x) ⊤ μS +
      eLpNorm (fun x => deriv g₁ x - deriv g₀ x) ⊤ μS +
      eLpNorm (fun x => deriv (deriv g₁) x - deriv (deriv g₀) x) ⊤ μS).toReal = e0 + e1 + e2 := by
    rw [ENNReal.toReal_add (ENNReal.add_lt_top.2 ⟨f0, f1⟩).ne f2.ne,
      ENNReal.toReal_add f0.ne f1.ne]
  have he0 : 0 ≤ e0 := ENNReal.toReal_nonneg
  have he1 : 0 ≤ e1 := ENNReal.toReal_nonneg
  have he2 : 0 ≤ e2 := ENNReal.toReal_nonneg
  rw [hes]
  -- pointwise bounds on the differences
  have hSle : -S ≤ S := by linarith
  have hd1 : ∀ x ∈ Icc (-S) S, |deriv g₁ x - deriv g₀ x| ≤ e1 := by
    have hae := (c10_aux_Linf_interval hc1'.measurable.aestronglyMeasurable hSle f1).2.1
    have := c10_aux_closure_of_ae (fun x => |deriv g₁ x - deriv g₀ x|) hc1'.abs e1 (Ioo (-S) S)
      isOpen_Ioo (by filter_upwards [hae] with x hx hxI using hx (Ioo_subset_Icc_self hxI))
    rwa [closure_Ioo (by linarith)] at this
  have hd2 : ∀ᵐ x, x ∈ Icc (-S) S → |deriv (deriv g₁) x - deriv (deriv g₀) x| ≤ e2 :=
    (c10_aux_Linf_interval hm2.aestronglyMeasurable hSle f2).2.1
  have hdiff : Differentiable ℝ (fun x => g₁ x - g₀ x) :=
    (hg₁.1.differentiable (by norm_num)).sub (hg₀.1.differentiable (by norm_num))
  -- secant data on the compact region
  have sec : ∀ y ∈ Icc (-R) R, ∀ z, |z| ≤ S → z ≠ y →
      |c01_secant g₁ y z - c01_secant g₀ y z| ≤ e1 ∧ |c01_secant g₁ y z| ≤ B ∧
      |c01_secant g₀ y z| ≤ B := by
    intro y hy z hz hzy
    have hyz : y ≠ z := Ne.symm hzy
    have e : c01_secant g₁ y z - c01_secant g₀ y z = c01_secant (fun x => g₁ x - g₀ x) y z := by
      unfold c01_secant; rw [if_neg hyz, if_neg hyz, if_neg hyz]; ring
    obtain ⟨ξ, hξ, hξe⟩ := c10_aux_secant_mvt hdiff hyz
    have hξS : ξ ∈ Icc (-S) S := by
      have hy' : y ∈ Icc (-S) S := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hz' : z ∈ Icc (-S) S := abs_le.1 hz
      exact uIcc_subset_Icc hy' hz' hξ
    have hdξ : deriv (fun x => g₁ x - g₀ x) ξ = deriv g₁ ξ - deriv g₀ ξ :=
      deriv_sub (hg₁.1.differentiable (by norm_num) ξ) (hg₀.1.differentiable (by norm_num) ξ)
    refine ⟨?_, ((c10_secant_identities g₁ hg₁ y z hyz).2.2.2.2 B hB₁).2.trans (min_le_left _ _),
      ((c10_secant_identities g₀ hg₀ y z hyz).2.2.2.2 B hB₀).2.trans (min_le_left _ _)⟩
    rw [e, ← hξe, hdξ]; exact hd1 ξ hξS
  -- the generic integration step
  have integ : ∀ (y : ℝ) (F : ℝ → ℝ) (T : Set ℝ), Measurable F → MeasurableSet T →
      T ⊆ {z | |z| ≤ S ∧ δ ≤ |y - z|} → (∀ z ∈ T, |F z| ≤ c1 * ε * (e0 + e1 + e2)) →
      IntegrableOn (fun z => |F z| / |y - z| ^ (p + 1)) T ∧
      (∫ z in T, |F z| / |y - z| ^ (p + 1)) ≤
        c1 / δ ^ (p + 1) * (2 * S) * ε * (e0 + e1 + e2) := by
    intro y F T hFm hT hTs hFb
    have hTv : volume T ≤ volume (Icc (-S) S) := measure_mono fun z hz => abs_le.1 (hTs hz).1
    have hTfin : volume T < ⊤ := lt_of_le_of_lt hTv measure_Icc_lt_top
    have hX : 0 ≤ c1 * ε * (e0 + e1 + e2) := by positivity
    have hb : ∀ z ∈ T, ‖|F z| / |y - z| ^ (p + 1)‖ ≤ c1 * ε * (e0 + e1 + e2) / δ ^ (p + 1) := by
      intro z hz
      have hw : δ ≤ |y - z| := (hTs hz).2
      have hwα : δ ^ (p + 1) ≤ |y - z| ^ (p + 1) := Real.rpow_le_rpow hδ.le hw (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (abs_nonneg _) _))]
      exact div_le_div₀ hX (hFb z hz) hδα hwα
    have hmeas : Measurable (fun z => |F z| / |y - z| ^ (p + 1)) := hFm.abs.div (by fun_prop)
    have hI : IntegrableOn (fun z => |F z| / |y - z| ^ (p + 1)) T :=
      IntegrableOn.of_bound hTfin hmeas.aestronglyMeasurable.restrict _
        ((ae_restrict_iff' hT).2 (Eventually.of_forall hb))
    refine ⟨hI, ?_⟩
    have hn := norm_setIntegral_le_of_norm_le_const hTfin hb
    have hreal : volume.real T ≤ 2 * S := by
      have := ENNReal.toReal_mono measure_Icc_lt_top.ne hTv
      rw [Real.volume_Icc] at this
      simp only [measureReal_def]
      rw [ENNReal.toReal_ofReal (by linarith)] at this
      linarith
    calc (∫ z in T, |F z| / |y - z| ^ (p + 1))
        ≤ ‖∫ z in T, |F z| / |y - z| ^ (p + 1)‖ := le_abs_self _
      _ ≤ c1 * ε * (e0 + e1 + e2) / δ ^ (p + 1) * volume.real T := hn
      _ ≤ c1 * ε * (e0 + e1 + e2) / δ ^ (p + 1) * (2 * S) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = _ := by ring
  have hpdiag : ∀ y z : ℝ, z ∈ {z | |z| ≤ S ∧ δ ≤ |y - z|} → z ≠ y := fun y z hz h => by
    subst h; have h2 := hz.2; simp only [sub_self, abs_zero] at h2; linarith
  have Gm : ∀ (g : ℝ → ℝ), W2inftyLoc g → ∀ y,
      Measurable (fun z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)) := fun g hg y =>
    c10_aux_meas_slice (F := fun y z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z))
      (c10_aux_Gamma_cont p ε hp hp1 hε hg.1).measurable y
  have Km : ∀ (g : ℝ → ℝ), W2inftyLoc g → ∀ y, Measurable (fun z => c10_Ieps_local_K1 p ε g y z) :=
    fun g hg y => c10_aux_meas_slice (F := fun y z => c10_Ieps_local_K1 p ε g y z)
      (c10_aux_K1_meas p ε hp hp1 hε hg.1) y
  have hc1b : 2 * Cg ≤ c1 := by
    have : 0 ≤ (4 * B + 6) / δ := by positivity
    simp only [hc1]; nlinarith
  refine ⟨fun y hy T hT hTs => ?_, ?_⟩
  · have := integ y _ T ((Gm g₁ hg₁ y).sub (Gm g₀ hg₀ y)) hT hTs (fun z hz => ?_)
    · refine ⟨this.1, this.2.trans (le_of_eq (by ring))⟩
    obtain ⟨hs, hs1, hs0⟩ := sec y hy z (hTs hz).1 (hpdiag y z (hTs hz))
    obtain ⟨l0, -, -, -, -⟩ := hG ε hε hε1 (deriv g₀ y) (deriv g₁ y) (c01_secant g₀ y z)
      (c01_secant g₁ y z) (hB₀ y) (hB₁ y) hs0 hs1
    have hu : |deriv g₁ y - deriv g₀ y| ≤ e1 := hd1 y ⟨by linarith [hy.1], by linarith [hy.2]⟩
    calc _ ≤ Cg * ε * (|deriv g₁ y - deriv g₀ y| + |c01_secant g₁ y z - c01_secant g₀ y z|) := l0
      _ ≤ Cg * ε * (e1 + e1) := mul_le_mul_of_nonneg_left (add_le_add hu hs) (by positivity)
      _ = (2 * Cg) * ε * e1 := by ring
      _ ≤ c1 * ε * (e0 + e1 + e2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hc1b hε) (by linarith) he1 (by positivity)
  · filter_upwards [hd2, hL₁] with y hy2 hyL hy T hT hTs
    have hyS : y ∈ Icc (-S) S := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have := integ y _ T ((Km g₁ hg₁ y).sub (Km g₀ hg₀ y)) hT hTs (fun z hz => ?_)
    · refine ⟨this.1, this.2.trans (le_of_eq (by ring))⟩
    have hzy := hpdiag y z (hTs hz)
    have hw : δ ≤ |y - z| := (hTs hz).2
    have hw0 : 0 < |y - z| := lt_of_lt_of_le hδ hw
    obtain ⟨hs, hs1, hs0⟩ := sec y hy z (hTs hz).1 hzy
    obtain ⟨l0, l1, l2, b1, b2⟩ := hG ε hε hε1 (deriv g₀ y) (deriv g₁ y) (c01_secant g₀ y z)
      (c01_secant g₁ y z) (hB₀ y) (hB₁ y) hs0 hs1
    have hu : |deriv g₁ y - deriv g₀ y| ≤ e1 := hd1 y hyS
    have hΔ : |deriv g₁ y - deriv g₀ y| + |c01_secant g₁ y z - c01_secant g₀ y z| ≤ 2 * e1 := by
      linarith
    set X := Cg * ε
    have hX : 0 ≤ X := by positivity
    have L0' := l0.trans (mul_le_mul_of_nonneg_left hΔ hX)
    have L1' := l1.trans (mul_le_mul_of_nonneg_left hΔ hX)
    have L2' := l2.trans (mul_le_mul_of_nonneg_left hΔ hX)
    have hg1 := hyL hyS
    have hg2 := hy2 hyS
    -- the three pieces
    set A1 := c10_N_pieces_Gamma_d1 p ε (deriv g₁ y) (c01_secant g₁ y z)
    set A0 := c10_N_pieces_Gamma_d1 p ε (deriv g₀ y) (c01_secant g₀ y z)
    set D1 := c10_N_pieces_Gamma_d2 p ε (deriv g₁ y) (c01_secant g₁ y z)
    set D0 := c10_N_pieces_Gamma_d2 p ε (deriv g₀ y) (c01_secant g₀ y z)
    set G1 := c10_N_pieces_Gamma p ε (deriv g₁ y) (c01_secant g₁ y z)
    set G0 := c10_N_pieces_Gamma p ε (deriv g₀ y) (c01_secant g₀ y z)
    set a1 := deriv g₁ y - c01_secant g₁ y z
    set a0 := deriv g₀ y - c01_secant g₀ y z
    have ha1 : |a1| ≤ 2 * B := (abs_sub _ _).trans (by linarith [hB₁ y])
    have ha : |a1 - a0| ≤ 2 * e1 := by
      have : a1 - a0 = (deriv g₁ y - deriv g₀ y) - (c01_secant g₁ y z - c01_secant g₀ y z) := by
        simp only [a1, a0]; ring
      rw [this]; exact (abs_sub _ _).trans hΔ
    have e : c10_Ieps_local_K1 p ε g₁ y z - c10_Ieps_local_K1 p ε g₀ y z =
        ((A1 - A0) * deriv (deriv g₁) y + A0 * (deriv (deriv g₁) y - deriv (deriv g₀) y)) +
        ((D1 - D0) * a1 + D0 * (a1 - a0)) / (y - z) - (1 + p) * (G1 - G0) / (y - z) := by
      unfold c10_Ieps_local_K1
      have hyz : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
      field_simp
      ring
    show |c10_Ieps_local_K1 p ε g₁ y z - c10_Ieps_local_K1 p ε g₀ y z| ≤ _
    rw [e]
    have t1 : |(A1 - A0) * deriv (deriv g₁) y + A0 * (deriv (deriv g₁) y - deriv (deriv g₀) y)| ≤
        X * (2 * e1) * L + X * e2 :=
      (abs_add_le _ _).trans (add_le_add (c10_aux_abs_mul2_le L1' hg1) (c10_aux_abs_mul2_le b1 hg2))
    have t2 : |((D1 - D0) * a1 + D0 * (a1 - a0)) / (y - z)| ≤
        (X * (2 * e1) * (2 * B) + X * (2 * e1)) / δ := by
      rw [abs_div]
      exact div_le_div₀ (by positivity) ((abs_add_le _ _).trans (add_le_add
        (c10_aux_abs_mul2_le L2' ha1) (c10_aux_abs_mul2_le b2 ha))) hδ hw
    have t3 : |(1 + p) * (G1 - G0) / (y - z)| ≤ 2 * (X * (2 * e1)) / δ := by
      rw [abs_div, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + p)]
      exact div_le_div₀ (by positivity) (mul_le_mul (by linarith) L0' (abs_nonneg _) (by norm_num))
        hδ hw
    have hsum := (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)
    refine hsum.trans ?_
    have hBδ : 0 ≤ (4 * B + 6) / δ := by positivity
    have key : X * (2 * e1) * L + X * e2 + (X * (2 * e1) * (2 * B) + X * (2 * e1)) / δ +
        2 * (X * (2 * e1)) / δ = X * ((2 * L) * e1 + e2 + (4 * B + 6) / δ * e1) := by
      field_simp; ring
    rw [key]
    simp only [hc1, X]
    have : (2 * L) * e1 + e2 + (4 * B + 6) / δ * e1 ≤
        (2 * L + 2 + (4 * B + 6) / δ) * (e0 + e1 + e2) := by
      have h1 : (2 * L) * e1 ≤ (2 * L) * (e0 + e1 + e2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h2 : (4 * B + 6) / δ * e1 ≤ (4 * B + 6) / δ * (e0 + e1 + e2) :=
        mul_le_mul_of_nonneg_left (by linarith) hBδ
      nlinarith
    calc Cg * ε * ((2 * L) * e1 + e2 + (4 * B + 6) / δ * e1)
        ≤ Cg * ε * ((2 * L + 2 + (4 * B + 6) / δ) * (e0 + e1 + e2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

/-- Helper: far from the diagonal (`|y - z| > 1`) the profile numerators are `O(ε)`. -/
theorem c10_aux_profile_far (p B : ℝ) (hp : 0 < p) (hp1 : p < 1) (hB : 1 ≤ B) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ g : ℝ → ℝ, W2inftyLoc g → (∀ x, |deriv g x| ≤ B) →
      ∀ y z : ℝ, |deriv (deriv g) y| ≤ B → 1 < |y - z| →
        |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)| ≤ C * ε ∧
        |c10_Ieps_local_K1 p ε g y z| ≤ C * ε := by
  obtain ⟨Ck, hCk, hk⟩ := c10_aux_Gamma_quad p B hp hp1 hB
  refine ⟨Ck * (B ^ 3 + 4 * B ^ 2 + B + 12 * B ^ 2), by positivity, ?_⟩
  intro ε hε hε1 g hg hgB y z hg2 hw
  have hyz : y ≠ z := fun h => by rw [h, sub_self, abs_zero] at hw; linarith
  have sB : |c01_secant g y z| ≤ B :=
    ((c10_secant_identities g hg y z hyz).2.2.2.2 B hgB).2.trans (min_le_left _ _)
  obtain ⟨b1, b2v, bs, bG⟩ := hk ε hε hε1 (deriv g y) (c01_secant g y z) (hgB y) sB
  have := c10_aux_prof_alg (X := Ck * ε) (g2 := deriv (deriv g) y) (w := y - z) (p := p)
    (mul_nonneg hCk.le hε) hB hB (sub_ne_zero.2 hyz) hp hp1 b1 b2v bs bG (hgB y) sB hg2
    (fun h => absurd h (not_le.2 hw))
  have h2 : 1 ≤ |y - z| ^ 2 := by nlinarith
  rw [min_eq_right h2, min_eq_right hw.le] at this
  constructor
  · calc _ ≤ _ := this.1
      _ = _ := by ring
  · calc |c10_Ieps_local_K1 p ε g y z| ≤ _ := this.2
      _ = _ := by ring

set_option maxHeartbeats 800000 in
/-- Blueprint: lem:c10_Ieps_uniform_tail.  For `0 < p < 1`, `B, L ≥ 1` there is `C = C(p,B,L)`
such that for `R ≥ 1`, `S ≥ 5R`, `0 ≤ ε ≤ 1` and `g ∈ W^{2,∞}_loc` with `‖g'‖_∞ ≤ B`,
`‖g''‖_{L^∞[-2R,2R]} ≤ L`: the tail integrals over `|z| > S` of the absolute value and derivative
kernels are finite (the latter for a.e. `|y| ≤ R`) and
`sup_{|y|≤R} ∫_{|z|>S} |Γ_ε|/|y-z|^α + ess sup_{|y|≤R} ∫_{|z|>S} |K⁽¹⁾_g|/|y-z|^α ≤ C ε S^{-p}`
(encoded as: for every `|y| ≤ R` and a.e. `|y'| ≤ R`, the sum of the two integrals is bounded). -/
theorem c10_Ieps_uniform_tail (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (B L : ℝ) (hB : 1 ≤ B)
    (hL : 1 ≤ L) :
    ∃ C > 0, ∀ R S : ℝ, 1 ≤ R → 5 * R ≤ S → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ g : ℝ → ℝ, W2inftyLoc g → (∀ y, |deriv g y| ≤ B) →
      (∀ᵐ y, y ∈ Icc (-2 * R) (2 * R) → |deriv (deriv g) y| ≤ L) →
      (∀ y ∈ Icc (-R) R, IntegrableOn (fun z =>
        |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)| / |y - z| ^ (p + 1))
          {z | S < |z|}) ∧
      (∀ᵐ y, y ∈ Icc (-R) R → IntegrableOn (fun z =>
        |c10_Ieps_local_K1 p ε g y z| / |y - z| ^ (p + 1)) {z | S < |z|}) ∧
      ∀ y ∈ Icc (-R) R, ∀ᵐ y', y' ∈ Icc (-R) R →
        (∫ z in {z | S < |z|},
            |c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)| / |y - z| ^ (p + 1)) +
          (∫ z in {z | S < |z|}, |c10_Ieps_local_K1 p ε g y' z| / |y' - z| ^ (p + 1)) ≤
          C * ε * S ^ (-p) := by
  set Bm := max B L
  have hBm : 1 ≤ Bm := hB.trans (le_max_left _ _)
  obtain ⟨Cf, hCf, hF⟩ := c10_aux_profile_far p Bm hp hp1 hBm
  refine ⟨2 * (Cf * (2 * (2 / p))) + 1, by positivity, ?_⟩
  intro R S hR hS ε hε hε1 g hg hgB hg2
  have hgB' : ∀ x, |deriv g x| ≤ Bm := fun x => (hgB x).trans (le_max_left _ _)
  have hg2' : ∀ᵐ x, x ∈ Icc (-2 * R) (2 * R) → |deriv (deriv g) x| ≤ Bm := by
    filter_upwards [hg2] with x hx hxI using (hx hxI).trans (le_max_right _ _)
  have hd2 : ∀ y ∈ Icc (-R) R, |deriv (deriv g) y| ≤ Bm := fun y hy =>
    c10_aux_d2_bound hg (zero_le_one.trans hBm) hg2' y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hS0 : 0 < S := by linarith
  have hT := c10_aux_tail (p + 1) S (by linarith) hS0
  have hTm : MeasurableSet {z : ℝ | S < |z|} := measurableSet_lt measurable_const (by fun_prop)
  -- pointwise far geometry
  have geo : ∀ y ∈ Icc (-R) R, ∀ z : ℝ, S < |z| → 4 / 5 * |z| ≤ |y - z| ∧ 1 < |y - z| := by
    intro y hy z hz
    have hyR : |y| ≤ R := abs_le.2 ⟨by linarith [hy.1], hy.2⟩
    have := abs_sub_abs_le_abs_sub z y
    rw [abs_sub_comm z y] at this
    constructor <;> nlinarith
  -- the generic tail estimate
  have tail : ∀ (y : ℝ) (F : ℝ → ℝ), y ∈ Icc (-R) R → Measurable F →
      (∀ z, S < |z| → |F z| ≤ Cf * ε) →
      IntegrableOn (fun z => |F z| / |y - z| ^ (p + 1)) {z | S < |z|} ∧
      (∫ z in {z | S < |z|}, |F z| / |y - z| ^ (p + 1)) ≤ Cf * ε * (2 * (2 / p * S ^ (-p))) := by
    intro y F hy hFm hFb
    have hb : ∀ z ∈ {z : ℝ | S < |z|}, |F z| / |y - z| ^ (p + 1) ≤ Cf * ε * 2 * |z| ^ (-(p + 1)) := by
      intro z hz
      obtain ⟨g1, g2⟩ := geo y hy z hz
      have hz0 : 0 < |z| := lt_of_le_of_lt hS0.le hz
      have hw0 : 0 < |y - z| := by linarith
      have hpow : (4 / 5 * |z|) ^ (p + 1) ≤ |y - z| ^ (p + 1) :=
        Real.rpow_le_rpow (by positivity) g1 (by linarith)
      have h45 : (1 / 2 : ℝ) ≤ (4 / 5) ^ (p + 1) := by
        have : (4 / 5 : ℝ) ^ (2 : ℝ) ≤ (4 / 5) ^ (p + 1) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        have e : (4 / 5 : ℝ) ^ (2 : ℝ) = 16 / 25 := by norm_num
        linarith
      have hzp : 0 < |z| ^ (p + 1) := Real.rpow_pos_of_pos hz0 _
      have hden : 1 / 2 * |z| ^ (p + 1) ≤ |y - z| ^ (p + 1) := by
        rw [Real.mul_rpow (by norm_num) hz0.le] at hpow
        nlinarith
      rw [Real.rpow_neg hz0.le, div_le_iff₀ (Real.rpow_pos_of_pos hw0 _)]
      have hC0 : 0 ≤ Cf * ε := mul_nonneg hCf.le hε
      calc |F z| ≤ Cf * ε := hFb z hz
        _ = Cf * ε * 2 * (|z| ^ (p + 1))⁻¹ * (1 / 2 * |z| ^ (p + 1)) := by
            field_simp
        _ ≤ Cf * ε * 2 * (|z| ^ (p + 1))⁻¹ * |y - z| ^ (p + 1) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
    have hint : IntegrableOn (fun z => Cf * ε * 2 * |z| ^ (-(p + 1))) {z | S < |z|} :=
      ((hT.1.mono_set (show {z : ℝ | S < |z|} ⊆ {ρ | S ≤ |ρ|} from
        fun z hz => by simp only [Set.mem_setOf_eq] at hz ⊢; exact hz.le)).const_mul (Cf * ε * 2))
    have hmeas : Measurable (fun z => |F z| / |y - z| ^ (p + 1)) := hFm.abs.div (by fun_prop)
    have hI : IntegrableOn (fun z => |F z| / |y - z| ^ (p + 1)) {z | S < |z|} :=
      Integrable.mono' hint hmeas.aestronglyMeasurable.restrict (by
        rw [ae_restrict_iff' hTm]
        exact Eventually.of_forall fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _)
            (Real.rpow_nonneg (abs_nonneg _) _))]
          exact hb z hz)
    refine ⟨hI, ?_⟩
    calc (∫ z in {z | S < |z|}, |F z| / |y - z| ^ (p + 1))
        ≤ ∫ z in {z | S < |z|}, Cf * ε * 2 * |z| ^ (-(p + 1)) :=
          setIntegral_mono_on hI hint hTm hb
      _ ≤ ∫ z in {z | S ≤ |z|}, Cf * ε * 2 * |z| ^ (-(p + 1)) := by
          apply setIntegral_mono_set (hT.1.const_mul _)
          · exact Eventually.of_forall fun z => by positivity
          · exact Eventually.of_forall fun z hz => by
              simp only [Set.mem_setOf_eq] at hz ⊢; exact hz.le
      _ = Cf * ε * (2 * (2 / p * S ^ (-p))) := by
          rw [integral_const_mul, hT.2]
          rw [show (p + 1) - 1 = p by ring, show 1 - (p + 1) = -p by ring]; ring
  have hΓm : ∀ y, Measurable (fun z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z)) :=
    fun y => c10_aux_meas_slice (F := fun y z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z))
      (c10_aux_Gamma_cont p ε hp hp1 hε hg.1).measurable y
  have hKm : ∀ y, Measurable (fun z => c10_Ieps_local_K1 p ε g y z) := fun y =>
    c10_aux_meas_slice (F := fun y z => c10_Ieps_local_K1 p ε g y z)
      (c10_aux_K1_meas p ε hp hp1 hε hg.1) y
  have tΓ := fun y hy => tail y _ hy (hΓm y) fun z hz =>
    (hF ε hε hε1 g hg hgB' y z (hd2 y hy) (geo y hy z hz).2).1
  have tK := fun y hy => tail y _ hy (hKm y) fun z hz =>
    (hF ε hε hε1 g hg hgB' y z (hd2 y hy) (geo y hy z hz).2).2
  refine ⟨fun y hy => (tΓ y hy).1, Eventually.of_forall fun y hy => (tK y hy).1,
    fun y hy => Eventually.of_forall fun y' hy' => ?_⟩
  have hSp : 0 ≤ S ^ (-p) := Real.rpow_nonneg hS0.le _
  calc _ ≤ Cf * ε * (2 * (2 / p * S ^ (-p))) + Cf * ε * (2 * (2 / p * S ^ (-p))) :=
        add_le_add (tΓ y hy).2 (tK y' hy').2
    _ = 2 * (Cf * (2 * (2 / p))) * ε * S ^ (-p) := by ring
    _ ≤ (2 * (Cf * (2 * (2 / p))) + 1) * ε * S ^ (-p) := by
        have : 0 ≤ ε * S ^ (-p) := mul_nonneg hε hSp
        nlinarith

/-- Helper: `N3(r₁) - N3(r₂) ∈ W^{1,∞}_loc` (from lem:c10_Ieps_local and `b_ε ∈ C¹`). -/
theorem c10_aux_N3_W1 (p γ ε : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hγ : admissibleGamma p γ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (fbar : ℝ → ℝ) (hf : fbar ∈ c01_admissible_class)
    {r₁ r₂ : ℝ → ℝ} (hr₁ : r₁ ∈ X_gamma p γ) (hr₂ : r₂ ∈ X_gamma p γ) :
    W1inftyLoc (fun y => c10_N_pieces_N3 p ε fbar r₁ y - c10_N_pieces_N3 p ε fbar r₂ y) := by
  have hI := (c10_Ieps_local p hp hp1).1 ε hε hε1
  have hb : LocallyLipschitz (b_eps p ε) := (c10_aux_b_eps_contDiff p ε).locallyLipschitz
  have hsum : ∀ r ∈ X_gamma p γ, LocallyLipschitz (c10_N_pieces_I p ε (fbar + r)) := by
    intro r hr
    have hrA := c10_aux_X_admissible_class p γ hp hp1 hγ hr
    have hd : deriv (fbar + r) = deriv fbar + deriv r := funext fun y =>
      deriv_add (hf.1.differentiable (by norm_num) y) (hrA.1.differentiable (by norm_num) y)
    obtain ⟨K1, hK1⟩ := hf.2.1
    obtain ⟨K2, hK2⟩ := hrA.2.1
    refine (hI (fbar + r) ⟨hf.1.add hrA.1, hd ▸ hf.2.2.add hrA.2.2⟩ ⟨K1 + K2, fun y => ?_⟩).1
    rw [hd, Pi.add_apply]; exact (abs_add_le _ _).trans (add_le_add (hK1 y) (hK2 y))
  have h1 := hsum r₁ hr₁
  have h2 := hsum r₂ hr₂
  have hb1 : LocallyLipschitz (fun y => b_eps p ε y * deriv r₁ y) := c10_aux_locLip_mul hb hr₁.1.2
  have hb2 : LocallyLipschitz (fun y => b_eps p ε y * deriv r₂ y) := c10_aux_locLip_mul hb hr₂.1.2
  have := ((h1.sub hb1).sub (h2.sub hb2))
  unfold W1inftyLoc
  convert this using 1
  funext y; simp only [c10_N_pieces_N3]; ring

/-- Blueprint: lem:N3.  `‖𝒩₃(r₁) - 𝒩₃(r₂)‖_{Y_γ} ≤ C ε ‖r₁ - r₂‖_{X_γ}`, `C = C(p,γ,M,N)`. -/
theorem N3 (p γ M N : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hN : 0 < N) :
    ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar →
      ∀ r₁ ∈ X_gamma p γ, ∀ r₂ ∈ X_gamma p γ, xNorm p γ r₁ ≤ N → xNorm p γ r₂ ≤ N →
      (fun y => c10_N_pieces_N3 p ε fbar r₁ y - c10_N_pieces_N3 p ε fbar r₂ y) ∈ Y_gamma p γ ∧
      yNorm p γ (fun y => c10_N_pieces_N3 p ε fbar r₁ y - c10_N_pieces_N3 p ε fbar r₂ y) ≤
        C * ε * xNorm p γ (r₁ - r₂) := by
  obtain ⟨C, hC, hD⟩ := c10_N3_linearized_bound p γ M N hp hp1 hγ hM hN
  refine ⟨C, hC, fun ε hε hε1 fbar hf r₁ hr₁ r₂ hr₂ h₁ h₂ => ?_⟩
  have hA : 0 ≤ C * ε := by positivity
  have hmv := c10_N3_mean_value p γ M ε N (C * ε) hp hp1 hγ hM hε hε1 hN hA fbar hf
    (fun r hr hrN h hh => by
      obtain ⟨hm, hb⟩ := hD ε hε hε1 fbar hf r hr hrN h hh
      rw [← ENNReal.ofReal_toReal hm.2.ne]
      exact ENNReal.ofReal_le_ofReal hb)
    r₁ r₂ hr₁ hr₂ h₁ h₂
  have hx : 0 ≤ C * ε * xNorm p γ (r₁ - r₂) := mul_nonneg hA ENNReal.toReal_nonneg
  have hfin := lt_of_le_of_lt hmv ENNReal.ofReal_lt_top
  have hfA : fbar ∈ c01_admissible_class :=
    c10_aux_C2_admissible_class hf.1 (c10_aux_admissible_deriv_bdd p M (by linarith) hf)
  refine ⟨⟨c10_aux_N3_W1 p γ ε hp hp1 hγ hε hε1 fbar hfA hr₁ hr₂, hfin⟩, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal hx hmv

/-- Blueprint: lem:c10_Ieps_local_continuity (helper).  `u_k → u` in `W^{1,∞}([-R,R])`. -/
def c10_Ieps_local_continuity_W1inf (uk : ℕ → ℝ → ℝ) (u : ℝ → ℝ) (R : ℝ) : Prop :=
  Tendsto (fun k => eLpNorm (fun y => uk k y - u y) ⊤ (volume.restrict (Icc (-R) R)) +
    eLpNorm (fun y => deriv (uk k) y - deriv u y) ⊤ (volume.restrict (Icc (-R) R))) atTop (nhds 0)

/-- Helper: splitting a difference of singular integrals into the near region, a compact region
away from the diagonal, and the tail. -/
theorem c10_aux_split3 (p y δ S R : ℝ) (hR : 1 ≤ R) (hy : y ∈ Icc (-R) R) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hS : 5 * R ≤ S) (N0 N1 : ℝ → ℝ)
    (hi0 : Integrable (fun z => N0 z / |y - z| ^ (p + 1)))
    (hi1 : Integrable (fun z => N1 z / |y - z| ^ (p + 1))) :
    |(∫ z, N1 z / |y - z| ^ (p + 1)) - ∫ z, N0 z / |y - z| ^ (p + 1)| ≤
      (∫ z in {z | |y - z| < δ}, |N1 z| / |y - z| ^ (p + 1)) +
      (∫ z in {z | |y - z| < δ}, |N0 z| / |y - z| ^ (p + 1)) +
      (∫ z in {z | |z| ≤ S ∧ δ ≤ |y - z|}, |N1 z - N0 z| / |y - z| ^ (p + 1)) +
      (∫ z in {z | S < |z|}, |N1 z| / |y - z| ^ (p + 1)) +
      (∫ z in {z | S < |z|}, |N0 z| / |y - z| ^ (p + 1)) := by
  set A := {z : ℝ | |y - z| < δ}
  set Bs := {z : ℝ | |z| ≤ S ∧ δ ≤ |y - z|}
  set C := {z : ℝ | S < |z|}
  have hAm : MeasurableSet A := measurableSet_lt (by fun_prop) measurable_const
  have hBm : MeasurableSet Bs :=
    (measurableSet_le (f := fun z : ℝ => |z|) (by fun_prop) measurable_const).inter
      (measurableSet_le (g := fun z : ℝ => |y - z|) measurable_const (by fun_prop))
  have hCm : MeasurableSet C := measurableSet_lt measurable_const (by fun_prop)
  have hyR : |y| ≤ R := abs_le.2 ⟨by linarith [hy.1], hy.2⟩
  have hAB : Disjoint A Bs := Set.disjoint_left.2 fun z h1 h2 => by
    have := h2.2; simp only [A, mem_setOf_eq] at h1; linarith
  have hABC : Disjoint (A ∪ Bs) C := by
    rw [Set.disjoint_union_left]
    constructor
    · refine Set.disjoint_left.2 fun z h1 h2 => ?_
      simp only [A, C, mem_setOf_eq] at h1 h2
      have := abs_sub_abs_le_abs_sub z y
      rw [abs_sub_comm z y] at this
      linarith
    · refine Set.disjoint_left.2 fun z h1 h2 => ?_
      simp only [Bs, C, mem_setOf_eq] at h1 h2; linarith [h1.1]
  have hcov : A ∪ Bs ∪ C = univ := by
    ext z; simp only [A, Bs, C, mem_union, mem_setOf_eq, mem_univ, iff_true]
    by_cases h1 : |y - z| < δ
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : |z| ≤ S
      · exact Or.inl (Or.inr ⟨h2, not_lt.1 h1⟩)
      · exact Or.inr (not_le.1 h2)
  set F0 := fun z => N0 z / |y - z| ^ (p + 1)
  set F1 := fun z => N1 z / |y - z| ^ (p + 1)
  have hD : Integrable (fun z => F1 z - F0 z) := hi1.sub hi0
  have hab : ∀ (N : ℝ → ℝ) z, |N z / |y - z| ^ (p + 1)| = |N z| / |y - z| ^ (p + 1) := fun N z => by
    rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hsplit : (∫ z, F1 z) - ∫ z, F0 z =
      (∫ z in A, (F1 z - F0 z)) + (∫ z in Bs, (F1 z - F0 z)) + ∫ z in C, (F1 z - F0 z) := by
    rw [← integral_sub hi1 hi0, ← setIntegral_univ, ← hcov,
      setIntegral_union hABC hCm hD.integrableOn hD.integrableOn,
      setIntegral_union hAB hBm hD.integrableOn hD.integrableOn]
  rw [hsplit]
  have I1 : Integrable (fun z => |N1 z| / |y - z| ^ (p + 1)) :=
    hi1.abs.congr (Eventually.of_forall fun z => hab N1 z)
  have I0 : Integrable (fun z => |N0 z| / |y - z| ^ (p + 1)) :=
    hi0.abs.congr (Eventually.of_forall fun z => hab N0 z)
  have gen : ∀ T : Set ℝ, MeasurableSet T → |∫ z in T, (F1 z - F0 z)| ≤
      (∫ z in T, |N1 z| / |y - z| ^ (p + 1)) + (∫ z in T, |N0 z| / |y - z| ^ (p + 1)) := by
    intro T hT
    rw [← integral_add I1.integrableOn I0.integrableOn]
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hD.abs.integrableOn
      (I1.integrableOn.add I0.integrableOn) hT fun z _ => ?_)
    rw [← hab N1 z, ← hab N0 z]; exact abs_sub _ _
  have bA := gen A hAm
  have bC := gen C hCm
  have bB : |∫ z in Bs, (F1 z - F0 z)| ≤ ∫ z in Bs, |N1 z - N0 z| / |y - z| ^ (p + 1) := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq (setIntegral_congr_fun hBm fun z _ => ?_))
    simp only [F0, F1]
    rw [← sub_div, hab (fun z => N1 z - N0 z) z]
  calc _ ≤ |∫ z in A, (F1 z - F0 z)| + |∫ z in Bs, (F1 z - F0 z)| + |∫ z in C, (F1 z - F0 z)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- Helper: the value integrand of `ℐ_ε(g)` is integrable at every point. -/
theorem c10_aux_I_integrable (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    {g : ℝ → ℝ} (hg : W2inftyLoc g) {L : ℝ} (hgL : ∀ y, |deriv g y| ≤ L) (y : ℝ) :
    Integrable (fun z => c10_N_pieces_Gamma p ε (deriv g y) (c01_secant g y z) / |y - z| ^ (p + 1)) := by
  set R := |y| + 1
  have hR : 1 ≤ R := by have := abs_nonneg y; simp only [R]; linarith
  obtain ⟨K, hK1, hK⟩ := c10_aux_loc_deriv_bound hg.2 (R + 3)
  obtain ⟨Cp, hCp, hP⟩ := c10_profile_kernel_bounds p hp hp1 (max L 1) K (le_max_right _ _) hK1
  have hpair := (hP R hR ε hε hε1 g hg (fun x => (hgL x).trans (le_max_left _ _))
    (Or.inl (Eventually.of_forall fun x hx => hK x ⟨by linarith [hx.1], by linarith [hx.2]⟩))).1
  have hU : (Ioo (-R) R).Nonempty := ⟨0, by constructor <;> linarith⟩
  exact (c10_aux_pair_integral (p + 1) (by linarith) (by linarith) (Ioo (-R) R) isOpen_Ioo
    ordConnected_Ioo hU (Cp * ε) (mul_nonneg hCp.le hε) _ _ hpair).1 y
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩

/-- Helper: eventual a.e. bound of `g_k''` on `[-a,a]` from `L^∞` convergence. -/
theorem c10_aux_eventually_d2 {gk : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hg : W2inftyLoc g) {a : ℝ}
    (ha : 0 < a)
    (hc : Tendsto (fun k => eLpNorm (fun y => deriv (deriv (gk k)) y - deriv (deriv g) y) ⊤
        (volume.restrict (Icc (-a) a))) atTop (nhds 0)) :
    ∃ L : ℝ, 1 ≤ L ∧ (∀ᵐ x, x ∈ Icc (-a) a → |deriv (deriv g) x| ≤ L) ∧
      ∀ᶠ k in atTop, ∀ᵐ x, x ∈ Icc (-a) a → |deriv (deriv (gk k)) x| ≤ L := by
  obtain ⟨K, hK1, hK⟩ := c10_aux_loc_deriv_bound hg.2 (a + 1)
  refine ⟨K + 1, by linarith, Eventually.of_forall fun x hx =>
    (hK x ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans (by linarith), ?_⟩
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hc) 1 one_pos] with k hk
  have hfin : eLpNorm (fun y => deriv (deriv (gk k)) y - deriv (deriv g) y) ⊤
      (volume.restrict (Icc (-a) a)) < ⊤ := lt_of_le_of_lt hk ENNReal.one_lt_top
  have hae := (c10_aux_Linf_interval ((measurable_deriv _).sub (measurable_deriv _)).aestronglyMeasurable
    (by linarith : -a ≤ a) hfin).2.1
  have h1 : (eLpNorm (fun y => deriv (deriv (gk k)) y - deriv (deriv g) y) ⊤
      (volume.restrict (Icc (-a) a))).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top hk; simpa using this
  filter_upwards [hae] with x hx hxI
  have := hx hxI
  have hgx := hK x ⟨by linarith [hxI.1], by linarith [hxI.2]⟩
  calc |deriv (deriv (gk k)) x| ≤ |deriv (deriv (gk k)) x - deriv (deriv g) x| +
        |deriv (deriv g) x| := by
        have := abs_sub_abs_le_abs_sub (deriv (deriv (gk k)) x) (deriv (deriv g) x); linarith
    _ ≤ 1 + K := add_le_add (this.trans h1) hgx
    _ = K + 1 := by ring


/-- Helper: an a.e. bound on `[a,b]` bounds the restricted `L^∞` norm. -/
theorem c10_aux_eLp_le {φ : ℝ → ℝ} (hφ : Measurable φ) {a b C : ℝ}
    (h : ∀ᵐ x, x ∈ Icc a b → |φ x| ≤ C) :
    eLpNorm φ ⊤ (volume.restrict (Icc a b)) ≤ ENNReal.ofReal C := by
  rw [eLpNorm_exponent_top hφ.aestronglyMeasurable.restrict]
  refine eLpNormEssSup_le_of_ae_bound ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h] with x hx hxI; rw [Real.norm_eq_abs]; exact hx hxI

/-- Helper: extract one summand from an a.e.-in-`y'` bound on a sum with nonnegative second term. -/
theorem c10_aux_exists_ae_Icc {R : ℝ} (hR : 1 ≤ R) {P : ℝ → Prop}
    (h : ∀ᵐ y, y ∈ Icc (-R) R → P y) : ∃ y ∈ Icc (-R) R, P y := by
  by_contra hne
  push_neg at hne
  have : volume (Icc (-R) R) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with y hy hyI using hne y hyI (hy hyI)
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero] at this
  linarith

/-- Helper: choice of the near radius `δ` and the tail radius `S`. -/
theorem c10_aux_choose_dS (p C1 C2 R e : ℝ) (hp : 0 < p) (hp1 : p < 1) (he : 0 < e) :
    ∃ δ S : ℝ, 0 < δ ∧ δ < 1 ∧ 5 * R ≤ S ∧ 0 < S ∧
      2 * C1 * (δ ^ (3 - (p + 1)) + δ ^ (2 - (p + 1))) ≤ e ∧ 2 * C2 * S ^ (-p) ≤ e := by
  have h1 : Tendsto (fun δ : ℝ => 2 * C1 * (δ ^ (3 - (p + 1)) + δ ^ (2 - (p + 1))))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt (fun δ : ℝ => 2 * C1 * (δ ^ (3 - (p + 1)) + δ ^ (2 - (p + 1)))) 0 :=
      continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).add
        (Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have e0 : 2 * C1 * ((0 : ℝ) ^ (3 - (p + 1)) + (0 : ℝ) ^ (2 - (p + 1))) = 0 := by
      rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]; ring
    rwa [e0] at this
  obtain ⟨δ, hδ1, hδ2⟩ := ((h1.eventually (Iic_mem_nhds he)).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  have h2 : Tendsto (fun S : ℝ => 2 * C2 * S ^ (-p)) atTop (nhds 0) := by
    have := (tendsto_rpow_neg_atTop hp).const_mul (2 * C2)
    simpa using this
  obtain ⟨S, hS1, hS3⟩ := ((eventually_ge_atTop (max (5 * R) 1)).and (h2.eventually (Iic_mem_nhds he))).exists
  have hS2 : 0 < S := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hS1)
  exact ⟨δ, S, hδ2.1, hδ2.2, (le_max_left _ _).trans hS1, hS2, hδ1, hS3⟩

set_option maxHeartbeats 800000 in
/-- Helper: local uniform convergence of the values in lem:c10_Ieps_local_continuity. -/
theorem c10_aux_cont_val (p ε : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (gk : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (hgk : ∀ k, W2inftyLoc (gk k)) (hg : W2inftyLoc g)
    (Bm : ℝ) (hBm : 1 ≤ Bm) (hgkB : ∀ k y, |deriv (gk k) y| ≤ Bm) (hgB : ∀ y, |deriv g y| ≤ Bm)
    (hconv : ∀ R : ℝ, 0 < R → c10_Ieps_local_continuity_W1inf gk g R ∧
      Tendsto (fun k => eLpNorm (fun y => deriv (deriv (gk k)) y - deriv (deriv g) y) ⊤
        (volume.restrict (Icc (-R) R))) atTop (nhds 0))
    (R : ℝ) (hR : 1 ≤ R) (mode : Bool) :
    ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop,
      (mode = true → ∀ y ∈ Icc (-R) R,
        |c10_N_pieces_I p ε (gk k) y - c10_N_pieces_I p ε g y| ≤ e) ∧
      (mode = false → ∀ᵐ y, y ∈ Icc (-R) R →
        |deriv (c10_N_pieces_I p ε (gk k)) y - deriv (c10_N_pieces_I p ε g) y| ≤ e) := by
  intro e he
  have hp0 : 0 < p := by linarith
  have h2R : (0 : ℝ) < 2 * R := by linarith
  obtain ⟨L1, hL1, hg2R, hk2R⟩ := c10_aux_eventually_d2 hg h2R (hconv (2 * R) h2R).2
  rw [show -(2 * R) = -2 * R by ring] at hg2R hk2R
  set Lm := max Bm L1
  have hLm : 1 ≤ Lm := hBm.trans (le_max_left _ _)
  obtain ⟨C1, hC1, hloc⟩ := (c10_Ieps_local p hp hp1).2 R hR Lm (by linarith)
  obtain ⟨C2, hC2, htail⟩ := c10_Ieps_uniform_tail p hp0 hp1 Bm Lm hBm hLm
  obtain ⟨δ, S, hδ, hδ1, hS, hS0, hδe, hSe⟩ := c10_aux_choose_dS p C1 C2 R (e / 3) hp0 hp1
    (by linarith)
  obtain ⟨LS, hLS, hgS, hkS⟩ := c10_aux_eventually_d2 hg hS0 (hconv S hS0).2
  obtain ⟨C3, hC3, hcomp⟩ := c10_Ieps_compact_difference p hp0 hp1 R S δ Bm LS hR hS hδ hδ1
    hBm hLS
  have heS : Tendsto (fun k => (eLpNorm (fun x => gk k x - g x) ⊤ (volume.restrict (Icc (-S) S)) +
      eLpNorm (fun x => deriv (gk k) x - deriv g x) ⊤ (volume.restrict (Icc (-S) S)) +
      eLpNorm (fun x => deriv (deriv (gk k)) x - deriv (deriv g) x) ⊤
        (volume.restrict (Icc (-S) S))).toReal) atTop (nhds 0) := by
    have := ((hconv S hS0).1.add (hconv S hS0).2)
    rw [add_zero] at this
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
    rw [ENNReal.toReal_zero] at this
    exact this
  have hgL : ∀ᵐ y, y ∈ Icc (-2 * R) (2 * R) → |deriv (deriv g) y| ≤ Lm := by
    filter_upwards [hg2R] with y hy hyI using (hy hyI).trans (le_max_right _ _)
  have hgBL : ∀ y, |deriv g y| ≤ Lm := fun y => (hgB y).trans (le_max_left _ _)
  have hgkBL : ∀ k y, |deriv (gk k) y| ≤ Lm := fun k y => (hgkB k y).trans (le_max_left _ _)
  -- derivative representations
  have hD0 := ((c10_Ieps_local p hp hp1).1 ε hε hε1 g hg ⟨Bm, hgB⟩).2
  have hDk := ae_all_iff.2 fun k => ((c10_Ieps_local p hp hp1).1 ε hε hε1 (gk k) (hgk k)
    ⟨Bm, hgkB k⟩).2
  have hIeq : ∀ (f : ℝ → ℝ) y, c10_N_pieces_I p ε f y =
      ∫ z, c10_N_pieces_Gamma p ε (deriv f y) (c01_secant f y z) / |y - z| ^ (p + 1) :=
    fun _ _ => rfl
  have hεS : 0 ≤ ε * S ^ (-p) := mul_nonneg hε (Real.rpow_nonneg hS0.le _)
  filter_upwards [hk2R, hkS, (tendsto_order.1 heS).2 (e / 3 / (C3 + 1)) (by positivity)]
    with k hk2 hkS' hes
  have hk2' : ∀ᵐ y, y ∈ Icc (-2 * R) (2 * R) → |deriv (deriv (gk k)) y| ≤ Lm := by
    filter_upwards [hk2] with y hy hyI using (hy hyI).trans (le_max_right _ _)
  obtain ⟨hl0v, hl0d, -⟩ := hloc ε hε hε1 g hg hgBL hgL δ hδ hδ1
  obtain ⟨hlkv, hlkd, -⟩ := hloc ε hε hε1 (gk k) (hgk k) (hgkBL k) hk2' δ hδ hδ1
  obtain ⟨-, -, ht0⟩ := htail R S hR hS ε hε hε1 g hg hgB hgL
  obtain ⟨-, -, htk⟩ := htail R S hR hS ε hε hε1 (gk k) (hgk k) (hgkB k) hk2'
  obtain ⟨hcv, hcd⟩ := hcomp ε hε hε1 g (gk k) hg (hgk k) hgB (hgkB k) hgS hkS'
  set eS := (eLpNorm (fun x => gk k x - g x) ⊤ (volume.restrict (Icc (-S) S)) +
      eLpNorm (fun x => deriv (gk k) x - deriv g x) ⊤ (volume.restrict (Icc (-S) S)) +
      eLpNorm (fun x => deriv (deriv (gk k)) x - deriv (deriv g) x) ⊤
        (volume.restrict (Icc (-S) S))).toReal with heSd
  have heS0 : 0 ≤ eS := ENNReal.toReal_nonneg
  have hC3e : C3 * ε * eS ≤ e / 3 := by
    have : C3 * eS ≤ e / 3 := by
      have h := lt_of_lt_of_le hes (le_refl _)
      rw [lt_div_iff₀ (by linarith)] at h
      nlinarith
    nlinarith
  have hsum : ∀ a b c d : ℝ, a ≤ C1 * ε * δ ^ (3 - (p + 1)) + C1 * ε * δ ^ (3 - (p + 1)) →
      True := fun _ _ _ _ _ => trivial
  clear hsum
  constructor
  · intro _ y hy
    have tails : ∀ (f : ℝ → ℝ) (hf : W2inftyLoc f), (∀ᵐ y', y' ∈ Icc (-R) R →
        (∫ z in {z | S < |z|}, |c10_N_pieces_Gamma p ε (deriv f y) (c01_secant f y z)| /
          |y - z| ^ (p + 1)) + (∫ z in {z | S < |z|}, |c10_Ieps_local_K1 p ε f y' z| /
          |y' - z| ^ (p + 1)) ≤ C2 * ε * S ^ (-p)) →
        (∫ z in {z | S < |z|}, |c10_N_pieces_Gamma p ε (deriv f y) (c01_secant f y z)| /
          |y - z| ^ (p + 1)) ≤ C2 * ε * S ^ (-p) := by
      intro f hf h
      obtain ⟨y', -, hy'⟩ := c10_aux_exists_ae_Icc hR h
      have : 0 ≤ ∫ z in {z | S < |z|}, |c10_Ieps_local_K1 p ε f y' z| / |y' - z| ^ (p + 1) :=
        setIntegral_nonneg (measurableSet_lt measurable_const (by fun_prop)) fun z _ =>
          div_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
      linarith
    have T0 := tails g hg (ht0 y hy)
    have Tk := tails (gk k) (hgk k) (htk y hy)
    have hspl := c10_aux_split3 p y δ S R hR hy hδ hδ1 hS _ _
      (c10_aux_I_integrable p ε hp0 hp1 hε hε1 hg hgB y)
      (c10_aux_I_integrable p ε hp0 hp1 hε hε1 (hgk k) (hgkB k) y)
    rw [hIeq (gk k), hIeq g]
    refine hspl.trans ?_
    beta_reduce
    have n0 := (hl0v y hy).2
    have nk := (hlkv y hy).2
    have hBm : MeasurableSet {z : ℝ | |z| ≤ S ∧ δ ≤ |y - z|} :=
      (measurableSet_le (f := fun z : ℝ => |z|) (by fun_prop) measurable_const).inter
        (measurableSet_le (g := fun z : ℝ => |y - z|) measurable_const (by fun_prop))
    have cv := (hcv y hy {z : ℝ | |z| ≤ S ∧ δ ≤ |y - z|} hBm subset_rfl).2
    have hδε : 2 * C1 * ε * (δ ^ (3 - (p + 1))) ≤ e / 3 := by
      have : 2 * C1 * (δ ^ (3 - (p + 1))) ≤ e / 3 := by
        have := Real.rpow_nonneg hδ.le (2 - (p + 1)); nlinarith
      have h0 : 0 ≤ 2 * C1 * δ ^ (3 - (p + 1)) := by
        have := Real.rpow_nonneg hδ.le (3 - (p + 1)); positivity
      nlinarith
    have hSε : 2 * C2 * ε * S ^ (-p) ≤ e / 3 := by
      have h0 : 0 ≤ 2 * C2 * S ^ (-p) := by have := Real.rpow_nonneg hS0.le (-p); positivity
      nlinarith
    linarith
  · intro _
    obtain ⟨y0, hy0, hty0⟩ : ∃ y0 ∈ Icc (-R) R, True := ⟨0, ⟨by linarith, by linarith⟩, trivial⟩
    have tl : ∀ (f : ℝ → ℝ), (∀ᵐ y', y' ∈ Icc (-R) R →
        (∫ z in {z | S < |z|}, |c10_N_pieces_Gamma p ε (deriv f y0) (c01_secant f y0 z)| /
          |y0 - z| ^ (p + 1)) + (∫ z in {z | S < |z|}, |c10_Ieps_local_K1 p ε f y' z| /
          |y' - z| ^ (p + 1)) ≤ C2 * ε * S ^ (-p)) →
        ∀ᵐ y', y' ∈ Icc (-R) R → (∫ z in {z | S < |z|}, |c10_Ieps_local_K1 p ε f y' z| /
          |y' - z| ^ (p + 1)) ≤ C2 * ε * S ^ (-p) := by
      intro f h
      filter_upwards [h] with y' hy' hyI
      have : 0 ≤ ∫ z in {z | S < |z|}, |c10_N_pieces_Gamma p ε (deriv f y0) (c01_secant f y0 z)| /
          |y0 - z| ^ (p + 1) :=
        setIntegral_nonneg (measurableSet_lt measurable_const (by fun_prop)) fun z _ =>
          div_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
      linarith [hy' hyI]
    filter_upwards [hD0, hDk, hl0d, hlkd, hcd, tl g (ht0 y0 hy0), tl (gk k) (htk y0 hy0)]
      with y d0 dk n0 nk cd t0 tk hy
    obtain ⟨i0, e0⟩ := d0
    obtain ⟨ik, ek⟩ := dk k
    rw [e0, ek]
    have hspl := c10_aux_split3 p y δ S R hR hy hδ hδ1 hS _ _ i0 ik
    refine hspl.trans ?_
    beta_reduce
    have hBm : MeasurableSet {z : ℝ | |z| ≤ S ∧ δ ≤ |y - z|} :=
      (measurableSet_le (f := fun z : ℝ => |z|) (by fun_prop) measurable_const).inter
        (measurableSet_le (g := fun z : ℝ => |y - z|) measurable_const (by fun_prop))
    have cv := (cd hy {z : ℝ | |z| ≤ S ∧ δ ≤ |y - z|} hBm subset_rfl).2
    have hδε : 2 * C1 * ε * (δ ^ (2 - (p + 1))) ≤ e / 3 := by
      have : 2 * C1 * (δ ^ (2 - (p + 1))) ≤ e / 3 := by
        have := Real.rpow_nonneg hδ.le (3 - (p + 1)); nlinarith
      have h0 : 0 ≤ 2 * C1 * δ ^ (2 - (p + 1)) := by
        have := Real.rpow_nonneg hδ.le (2 - (p + 1)); positivity
      nlinarith
    have hSε : 2 * C2 * ε * S ^ (-p) ≤ e / 3 := by
      have h0 : 0 ≤ 2 * C2 * S ^ (-p) := by have := Real.rpow_nonneg hS0.le (-p); positivity
      nlinarith
    linarith [(n0 hy).2, (nk hy).2, t0 hy, tk hy]

/-- Blueprint: lem:c10_Ieps_local_continuity.  If `g_k, g ∈ W^{2,∞}_loc` with `g_k', g'` uniformly
bounded and `g_k → g` in `W^{2,∞}_loc`, then `ℐ_ε(g_k) → ℐ_ε(g)` in `W^{1,∞}([-R,R])` for all `R`. -/
-- Proof: second derivatives converge in essential supremum norm, not pointwise uniformly.
-- For the far region, `z` is first restricted to a compact set, and the remaining tail is bounded
-- by `C ε ∫_{|z| > S} |z|^(-1-p)`. This avoids a measurability claim for a pointwise supremum
-- over `y` of an integrand containing the merely measurable functions `deriv (deriv gk)`.
theorem c10_Ieps_local_continuity (p ε : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (gk : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (hgk : ∀ k, W2inftyLoc (gk k)) (hg : W2inftyLoc g)
    (hbd : ∃ L : ℝ, (∀ k y, |deriv (gk k) y| ≤ L) ∧ ∀ y, |deriv g y| ≤ L)
    (hconv : ∀ R : ℝ, 0 < R → c10_Ieps_local_continuity_W1inf gk g R ∧
      Tendsto (fun k => eLpNorm (fun y => deriv (deriv (gk k)) y - deriv (deriv g) y) ⊤
        (volume.restrict (Icc (-R) R))) atTop (nhds 0)) :
    ∀ R : ℝ, 0 < R → c10_Ieps_local_continuity_W1inf (fun k => c10_N_pieces_I p ε (gk k)) (c10_N_pieces_I p ε g) R := by
  obtain ⟨L, hLk, hLg⟩ := hbd
  set Bm := max L 1
  have hBm : 1 ≤ Bm := le_max_right _ _
  have hgkB : ∀ k y, |deriv (gk k) y| ≤ Bm := fun k y => (hLk k y).trans (le_max_left _ _)
  have hgB : ∀ y, |deriv g y| ≤ Bm := fun y => (hLg y).trans (le_max_left _ _)
  intro R hR
  set R1 := max R 1
  have hR1 : 1 ≤ R1 := le_max_right _ _
  have hsub : Icc (-R) R ⊆ Icc (-R1) R1 := Icc_subset_Icc (by simp [R1]) (le_max_left _ _)
  have hcI : ∀ (f : ℝ → ℝ), W2inftyLoc f → (∀ y, |deriv f y| ≤ Bm) →
      Continuous (c10_N_pieces_I p ε f) := fun f hf hfB =>
    ((c10_Ieps_local p hp hp1).1 ε hε hε1 f hf ⟨Bm, hfB⟩).1.continuous
  rw [c10_Ieps_local_continuity_W1inf, ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases htop : e = ⊤
  · exact Eventually.of_forall fun _ => by rw [htop]; exact le_top
  have he' : 0 < e.toReal / 2 := by
    have := ENNReal.toReal_pos he.ne' htop; linarith
  have V := c10_aux_cont_val p ε hp hp1 hε hε1 gk g hgk hg Bm hBm hgkB hgB hconv R1 hR1 true
    (e.toReal / 2) he'
  have D := c10_aux_cont_val p ε hp hp1 hε hε1 gk g hgk hg Bm hBm hgkB hgB hconv R1 hR1 false
    (e.toReal / 2) he'
  filter_upwards [V, D] with k hv hd
  have hv' := hv.1 rfl
  have hd' := hd.2 rfl
  have m1 : Measurable (fun y => c10_N_pieces_I p ε (gk k) y - c10_N_pieces_I p ε g y) :=
    ((hcI _ (hgk k) (hgkB k)).sub (hcI _ hg hgB)).measurable
  have m2 : Measurable (fun y => deriv (c10_N_pieces_I p ε (gk k)) y -
      deriv (c10_N_pieces_I p ε g) y) := (measurable_deriv _).sub (measurable_deriv _)
  have b1 := c10_aux_eLp_le m1 (a := -R) (b := R) (C := e.toReal / 2)
    (Eventually.of_forall fun y hy => hv' y (hsub hy))
  have b2 := c10_aux_eLp_le m2 (a := -R) (b := R) (C := e.toReal / 2) (by
    filter_upwards [hd'] with y hy hyI using hy (hsub hyI))
  calc _ ≤ ENNReal.ofReal (e.toReal / 2) + ENNReal.ofReal (e.toReal / 2) := add_le_add b1 b2
    _ = ENNReal.ofReal (e.toReal) := by
        rw [← ENNReal.ofReal_add he'.le he'.le]; ring_nf
    _ = e := ENNReal.ofReal_toReal htop

/-- Helper: `u k → v` uniformly a.e. on `S`, with `v` a.e. bounded on `S`. -/
def c10_aux_Conv (S : Set ℝ) (u : ℕ → ℝ → ℝ) (v : ℝ → ℝ) : Prop :=
  (∃ B, ∀ᵐ y, y ∈ S → |v y| ≤ B) ∧ ∀ δ > 0, ∀ᶠ k in atTop, ∀ᵐ y, y ∈ S → |u k y - v y| ≤ δ

/-- Helper: a constant sequence converges (Conv). -/
theorem c10_aux_Conv_const {S : Set ℝ} {v : ℝ → ℝ} (h : ∃ B, ∀ᵐ y, y ∈ S → |v y| ≤ B) :
    c10_aux_Conv S (fun _ => v) v :=
  ⟨h, fun δ hδ => Eventually.of_forall fun k => ae_of_all _ fun y _ => by simp; linarith⟩

/-- Helper: a Conv-convergent sequence is eventually a.e. uniformly bounded. -/
theorem c10_aux_Conv_bdd {S : Set ℝ} {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ} (h : c10_aux_Conv S u v) :
    ∃ B, 0 ≤ B ∧ (∀ᵐ y, y ∈ S → |v y| ≤ B) ∧ ∀ᶠ k in atTop, ∀ᵐ y, y ∈ S → |u k y| ≤ B := by
  obtain ⟨⟨B, hB⟩, hc⟩ := h
  refine ⟨|B| + 1, by positivity, ?_, ?_⟩
  · filter_upwards [hB] with y hy hyS
    linarith [hy hyS, le_abs_self B]
  · filter_upwards [hc 1 one_pos] with k hk
    filter_upwards [hk, hB] with y h1 h2 hyS
    have := abs_sub_abs_le_abs_sub (u k y) (v y)
    linarith [h1 hyS, h2 hyS, le_abs_self B]

/-- Helper: Conv is closed under sums. -/
theorem c10_aux_Conv_add {S : Set ℝ} {u u' : ℕ → ℝ → ℝ} {v v' : ℝ → ℝ}
    (h : c10_aux_Conv S u v) (h' : c10_aux_Conv S u' v') :
    c10_aux_Conv S (fun k y => u k y + u' k y) (fun y => v y + v' y) := by
  obtain ⟨⟨B, hB⟩, hc⟩ := h
  obtain ⟨⟨B', hB'⟩, hc'⟩ := h'
  refine ⟨⟨B + B', ?_⟩, fun δ hδ => ?_⟩
  · filter_upwards [hB, hB'] with y h1 h2 hyS
    exact (abs_add_le _ _).trans (add_le_add (h1 hyS) (h2 hyS))
  · filter_upwards [hc (δ / 2) (by positivity), hc' (δ / 2) (by positivity)] with k hk hk'
    filter_upwards [hk, hk'] with y h1 h2 hyS
    calc |u k y + u' k y - (v y + v' y)| = |(u k y - v y) + (u' k y - v' y)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add (h1 hyS) (h2 hyS)
      _ = δ := by ring

/-- Helper: Conv is closed under negation. -/
theorem c10_aux_Conv_neg {S : Set ℝ} {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ}
    (h : c10_aux_Conv S u v) : c10_aux_Conv S (fun k y => -u k y) (fun y => -v y) := by
  obtain ⟨⟨B, hB⟩, hc⟩ := h
  refine ⟨⟨B, ?_⟩, fun δ hδ => ?_⟩
  · filter_upwards [hB] with y h1 hyS; rw [abs_neg]; exact h1 hyS
  · filter_upwards [hc δ hδ] with k hk
    filter_upwards [hk] with y h1 hyS
    rw [show -u k y - -v y = -(u k y - v y) by ring, abs_neg]; exact h1 hyS

/-- Helper: Conv is closed under differences. -/
theorem c10_aux_Conv_sub {S : Set ℝ} {u u' : ℕ → ℝ → ℝ} {v v' : ℝ → ℝ}
    (h : c10_aux_Conv S u v) (h' : c10_aux_Conv S u' v') :
    c10_aux_Conv S (fun k y => u k y - u' k y) (fun y => v y - v' y) := by
  have := c10_aux_Conv_add h (c10_aux_Conv_neg h')
  simpa [sub_eq_add_neg] using this

/-- Helper: Conv is closed under products. -/
theorem c10_aux_Conv_mul {S : Set ℝ} {u u' : ℕ → ℝ → ℝ} {v v' : ℝ → ℝ}
    (h : c10_aux_Conv S u v) (h' : c10_aux_Conv S u' v') :
    c10_aux_Conv S (fun k y => u k y * u' k y) (fun y => v y * v' y) := by
  obtain ⟨B, hB0, hBv, hBu⟩ := c10_aux_Conv_bdd h
  obtain ⟨B', hB0', hBv', hBu'⟩ := c10_aux_Conv_bdd h'
  refine ⟨⟨B * B', ?_⟩, fun δ hδ => ?_⟩
  · filter_upwards [hBv, hBv'] with y h1 h2 hyS
    rw [abs_mul]; exact mul_le_mul (h1 hyS) (h2 hyS) (abs_nonneg _) hB0
  · set e := δ / (2 * (B + B' + 1)) with he
    have hd : 0 < 2 * (B + B' + 1) := by positivity
    have he0 : 0 < e := div_pos hδ hd
    filter_upwards [h.2 e he0, h'.2 e he0, hBu'] with k hk hk' hku'
    filter_upwards [hk, hk', hku', hBv] with y h1 h2 h3 h4 hyS
    have h1 := h1 hyS; have h2 := h2 hyS; have h3 := h3 hyS; have h4 := h4 hyS
    calc |u k y * u' k y - v y * v' y| = |(u k y - v y) * u' k y + v y * (u' k y - v' y)| := by
          ring_nf
      _ ≤ |u k y - v y| * |u' k y| + |v y| * |u' k y - v' y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ e * B' + B * e := add_le_add (mul_le_mul h1 h3 (abs_nonneg _) he0.le)
          (mul_le_mul h4 h2 (abs_nonneg _) hB0)
      _ ≤ e * (2 * (B + B' + 1)) := by nlinarith
      _ = δ := by rw [he]; field_simp

/-- Helper: Conv is preserved by composition with a locally Lipschitz map. -/
theorem c10_aux_Conv_comp {S : Set ℝ} {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ} {φ : ℝ → ℝ}
    (hφ : LocallyLipschitz φ) (h : c10_aux_Conv S u v) :
    c10_aux_Conv S (fun k y => φ (u k y)) (fun y => φ (v y)) := by
  obtain ⟨B, hB0, hBv, hBu⟩ := c10_aux_Conv_bdd h
  obtain ⟨K, hK⟩ := (hφ.locallyLipschitzOn (s := Icc (-B) B)).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  refine ⟨⟨|φ 0| + K * B, ?_⟩, fun δ hδ => ?_⟩
  · filter_upwards [hBv] with y h1 hyS
    have hv := abs_le.1 (h1 hyS)
    have := hK.dist_le_mul (v y) ⟨hv.1, hv.2⟩ 0 ⟨by linarith, hB0⟩
    rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
    have := abs_sub_abs_le_abs_sub (φ (v y)) (φ 0)
    have : (K : ℝ) * |v y| ≤ K * B := mul_le_mul_of_nonneg_left (h1 hyS) K.2
    linarith
  · set e := δ / ((K : ℝ) + 1) with he
    have he0 : 0 < e := div_pos hδ (by positivity)
    filter_upwards [h.2 e he0, hBu] with k hk hku
    filter_upwards [hk, hku, hBv] with y h1 h2 h3 hyS
    have a := abs_le.1 (h2 hyS); have b := abs_le.1 (h3 hyS)
    have := hK.dist_le_mul (u k y) ⟨a.1, a.2⟩ (v y) ⟨b.1, b.2⟩
    rw [Real.dist_eq, Real.dist_eq] at this
    calc _ ≤ (K : ℝ) * |u k y - v y| := this
      _ ≤ (K : ℝ) * e := mul_le_mul_of_nonneg_left (h1 hyS) K.2
      _ ≤ ((K : ℝ) + 1) * e := by nlinarith
      _ = δ := by rw [he]; field_simp

/-- Helper: Conv is invariant under a.e. modification on `S`. -/
theorem c10_aux_Conv_congr {S : Set ℝ} {u u' : ℕ → ℝ → ℝ} {v v' : ℝ → ℝ}
    (h : c10_aux_Conv S u v) (hu : ∀ k, ∀ᵐ y, y ∈ S → u' k y = u k y)
    (hv : ∀ᵐ y, y ∈ S → v' y = v y) : c10_aux_Conv S u' v' := by
  obtain ⟨⟨B, hB⟩, hc⟩ := h
  refine ⟨⟨B, ?_⟩, fun δ hδ => ?_⟩
  · filter_upwards [hB, hv] with y h1 h2 hyS; rw [h2 hyS]; exact h1 hyS
  · filter_upwards [hc δ hδ] with k hk
    filter_upwards [hk, hu k, hv] with y h1 h2 h3 hyS
    rw [h2 hyS, h3 hyS]; exact h1 hyS

/-- Helper: uniform convergence on a compact set to a continuous limit gives Conv. -/
theorem c10_aux_Conv_of_unif {S : Set ℝ} {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ}
    (hS : IsCompact S) (hv : ContinuousOn v S) (h : TendstoUniformlyOn u v atTop S) :
    c10_aux_Conv S u v := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hv
  refine ⟨⟨B, ae_of_all _ fun y hy => hB y hy⟩, fun δ hδ => ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 h) δ hδ] with k hk
  exact ae_of_all _ fun y hy => by
    have := (hk y hy).le
    rwa [Real.dist_eq, abs_sub_comm] at this

/-- Helper: Conv gives convergence in `L^∞(S)`. -/
theorem c10_aux_Conv_tendsto {S : Set ℝ} {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ}
    (hSm : MeasurableSet S) (h : c10_aux_Conv S u v)
    (hm : ∀ k, AEStronglyMeasurable (fun y => u k y - v y) (volume.restrict S)) :
    Tendsto (fun k => eLpNorm (fun y => u k y - v y) ⊤ (volume.restrict S)) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases het : e = ⊤
  · exact Eventually.of_forall fun _ => by rw [het]; exact le_top
  have hpos : 0 < e.toReal := ENNReal.toReal_pos he.ne' het
  filter_upwards [h.2 e.toReal hpos] with k hk
  have hb : ∀ᵐ y ∂(volume.restrict S), ‖u k y - v y‖ ≤ e.toReal :=
    (ae_restrict_iff' hSm).2 hk
  calc eLpNorm (fun y => u k y - v y) ⊤ (volume.restrict S)
      ≤ (volume.restrict S) univ ^ (⊤ : ENNReal).toReal⁻¹ * ENNReal.ofReal e.toReal :=
        eLpNorm_le_of_ae_bound (hm k) hb
    _ = e := by simp [ENNReal.ofReal_toReal het]


/-- Helper: the derivative of `𝒩₁` (where `r'` is differentiable). -/
theorem c10_aux_N1_hasDeriv (p ε : ℝ) (hε : 0 ≤ ε) {g r : ℝ → ℝ} {y : ℝ}
    (hg : DifferentiableAt ℝ g y) (hg' : DifferentiableAt ℝ (deriv g) y)
    (hr' : DifferentiableAt ℝ (deriv r) y) :
    deriv (c10_N_pieces_N1 p ε g r) y =
      (deriv (A_eps_B p ε) (deriv g y + deriv r y) * (deriv (deriv g) y + deriv (deriv r) y) -
          deriv (A_eps_B p ε) (deriv g y) * deriv (deriv g) y) * (g y - y * deriv g y) +
        (A_eps_B p ε (deriv g y + deriv r y) - A_eps_B p ε (deriv g y)) *
          (deriv g y - (1 * deriv g y + y * deriv (deriv g) y)) := by
  have hB : ∀ x, HasDerivAt (A_eps_B p ε) (deriv (A_eps_B p ε) x) x := fun x =>
    (c10_aux_B_hasDeriv p ε hε x).differentiableAt.hasDerivAt
  have h1 := (hB _).comp y (hg'.hasDerivAt.add hr'.hasDerivAt)
  have h2 := (hB _).comp y hg'.hasDerivAt
  have h3 := hg.hasDerivAt.sub ((hasDerivAt_id y).mul hg'.hasDerivAt)
  exact ((h1.sub h2).mul h3).deriv

/-- Helper: the derivative of `𝒩₂` (where `r'` is differentiable). -/
theorem c10_aux_N2_hasDeriv (p ε : ℝ) (hε : 0 ≤ ε) {g r : ℝ → ℝ} {y : ℝ}
    (hg' : DifferentiableAt ℝ (deriv g) y) (hr : DifferentiableAt ℝ r y)
    (hr' : DifferentiableAt ℝ (deriv r) y) :
    deriv (c10_N_pieces_N2 p ε g r) y =
      deriv (A_eps_B p ε) (deriv g y + deriv r y) * (deriv (deriv g) y + deriv (deriv r) y) *
          (r y - y * deriv r y) +
        (A_eps_B p ε (deriv g y + deriv r y) - 1) *
          (deriv r y - (1 * deriv r y + y * deriv (deriv r) y)) := by
  have hB : ∀ x, HasDerivAt (A_eps_B p ε) (deriv (A_eps_B p ε) x) x := fun x =>
    (c10_aux_B_hasDeriv p ε hε x).differentiableAt.hasDerivAt
  have h1 := (hB _).comp y (hg'.hasDerivAt.add hr'.hasDerivAt)
  have h3 := hr.hasDerivAt.sub ((hasDerivAt_id y).mul hr'.hasDerivAt)
  exact ((h1.sub_const 1).mul h3).deriv

/-- Helper: `|f̄'| ≤ M + 1` for an admissible profile with constant `M`. -/
theorem c10_aux_admissible_deriv_le (p M : ℝ) (hp : 0 < p)
    {fbar : ℝ → ℝ} (h : nonlinear_admissible_profile p M fbar) (y : ℝ) :
    |deriv fbar y| ≤ M + 1 := by
  have hM : 0 ≤ M := by
    have h0 := (h.2.1 0 le_rfl).1
    have : 0 < jb 0 ^ (-p) := Real.rpow_pos_of_pos (c10_aux_jb_pos 0) _
    nlinarith [abs_nonneg (fbar 0)]
  have hβ : 0 ≤ beta p := by unfold beta; positivity
  rcases le_total 0 y with hy | hy
  · have h1 := (h.2.1 y hy).2.1
    have : jb y ^ (-beta p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c10_aux_one_le_jb y) (by linarith)
    nlinarith
  · have h1 := (h.2.2 y hy).2.1
    have : jb y ^ (-p - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c10_aux_one_le_jb y) (by linarith)
    have h2 : |deriv fbar y + 1| ≤ M := by nlinarith
    have h3 := abs_sub (deriv fbar y + 1) 1
    simp only [add_sub_cancel_right, abs_one] at h3
    linarith

/-- Helper: a constant sequence with continuous value converges on a compact set. -/
theorem c10_aux_Conv_cont {S : Set ℝ} {v : ℝ → ℝ} (hS : IsCompact S) (hv : ContinuousOn v S) :
    c10_aux_Conv S (fun _ => v) v := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hv
  exact c10_aux_Conv_const ⟨B, ae_of_all _ fun y hy => hB y hy⟩

/-- Helper: Conv of values and derivatives gives `W^{1,∞}([-R,R])` convergence. -/
theorem c10_aux_W1inf_of_Conv {R : ℝ} {u : ℕ → ℝ → ℝ} {v : ℝ → ℝ}
    (hV : c10_aux_Conv (Icc (-R) R) u v)
    (hD : c10_aux_Conv (Icc (-R) R) (fun k => deriv (u k)) (deriv v))
    (hm : ∀ k, AEStronglyMeasurable (fun y => u k y - v y) (volume.restrict (Icc (-R) R))) :
    c10_Ieps_local_continuity_W1inf u v R := by
  have h1 := c10_aux_Conv_tendsto measurableSet_Icc hV hm
  have h2 := c10_aux_Conv_tendsto measurableSet_Icc hD fun k =>
    ((measurable_deriv _).sub (measurable_deriv _)).aestronglyMeasurable
  unfold c10_Ieps_local_continuity_W1inf
  simpa using h1.add h2

/-- Helper: `r'` locally Lipschitz gives `r''` bounded on `[-R,R]`. -/
theorem c10_aux_deriv2_bdd {r : ℝ → ℝ} (hr : LocallyLipschitz (deriv r)) (R : ℝ) :
    ∃ B, ∀ y ∈ Icc (-R) R, |deriv (deriv r) y| ≤ B := by
  obtain ⟨K, hK⟩ := (hr.locallyLipschitzOn (s := Icc (-R - 1) (R + 1))).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  refine ⟨K, fun y hy => ?_⟩
  have := norm_deriv_le_of_lipschitzOn (x₀ := y)
    (Icc_mem_nhds (by linarith [hy.1]) (by linarith [hy.2])) hK
  simpa using this

/-- Blueprint: lem:c10_N_local_convergence.  For admissible `f̄_k → f̄` in `C²_loc` (common
constant `M`), `𝒩_j^{ε,f̄_k}(r) → 𝒩_j^{ε,f̄}(r)` in `W^{1,∞}([-R,R])`, `j = 1,2,3`, all `R > 0`. -/
theorem c10_N_local_convergence (p γ M ε : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1)
    (hγ : admissibleGamma p γ) (hM : 0 < M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (r : ℝ → ℝ) (hr : r ∈ X_gamma p γ) (fk : ℕ → ℝ → ℝ) (fbar : ℝ → ℝ)
    (hk : ∀ k, nonlinear_admissible_profile p M (fk k)) (hconv : c10_admissible_closed_C2loc fk fbar) :
    ∀ j : Fin 3, ∀ R : ℝ, 0 < R →
      c10_Ieps_local_continuity_W1inf (fun k => c10_N_pieces p ε (fk k) r j) (c10_N_pieces p ε fbar r j) R := by
  intro j R hR
  have hf := c10_admissible_closed p M fk fbar hk hconv
  obtain ⟨hC2, hU⟩ := hconv
  have e2 : ∀ g : ℝ → ℝ, iteratedDeriv 2 g = deriv (deriv g) := fun g => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have dk : ∀ k, ContDiff ℝ 1 (deriv (fk k)) := fun k =>
    ((contDiff_succ_iff_deriv (n := 1)).1 (hk k).1).2.2
  have df : ContDiff ℝ 1 (deriv fbar) := ((contDiff_succ_iff_deriv (n := 1)).1 hC2).2.2
  have F0 : ∀ R', c10_aux_Conv (Icc (-R') R') fk fbar := fun R' =>
    c10_aux_Conv_of_unif isCompact_Icc hC2.continuous.continuousOn (by simpa using hU 0 (by norm_num) R')
  have F1 : ∀ R', c10_aux_Conv (Icc (-R') R') (fun k => deriv (fk k)) (deriv fbar) := fun R' =>
    c10_aux_Conv_of_unif isCompact_Icc df.continuous.continuousOn (by simpa using hU 1 (by norm_num) R')
  have F2 : ∀ R', c10_aux_Conv (Icc (-R') R') (fun k => deriv (deriv (fk k))) (deriv (deriv fbar)) :=
    fun R' => c10_aux_Conv_of_unif isCompact_Icc (df.continuous_deriv le_rfl).continuousOn
      (by simpa [e2] using hU 2 le_rfl R')
  have rc : Continuous r := hr.1.1.continuous
  have r'c : Continuous (deriv r) := hr.1.1.continuous_deriv le_rfl
  have R0 : ∀ R', c10_aux_Conv (Icc (-R') R') (fun _ => r) r := fun R' =>
    c10_aux_Conv_cont isCompact_Icc rc.continuousOn
  have R1 : ∀ R', c10_aux_Conv (Icc (-R') R') (fun _ => deriv r) (deriv r) := fun R' =>
    c10_aux_Conv_cont isCompact_Icc r'c.continuousOn
  have R2 : ∀ R', c10_aux_Conv (Icc (-R') R') (fun _ => deriv (deriv r)) (deriv (deriv r)) := fun R' => by
    obtain ⟨B, hB⟩ := c10_aux_deriv2_bdd hr.1.2 R'
    exact c10_aux_Conv_const ⟨B, ae_of_all _ hB⟩
  have Y : c10_aux_Conv (Icc (-R) R) (fun _ y => y) (fun y => y) :=
    c10_aux_Conv_cont isCompact_Icc continuousOn_id
  have One : c10_aux_Conv (Icc (-R) R) (fun _ _ => (1:ℝ)) (fun _ => 1) :=
    c10_aux_Conv_cont isCompact_Icc continuousOn_const
  have hBl : LocallyLipschitz (A_eps_B p ε) := (c10_aux_B_contDiff p ε hε).locallyLipschitz
  have hB'l : LocallyLipschitz (deriv (A_eps_B p ε)) :=
    (((contDiff_succ_iff_deriv (n := 1)).1 (c10_aux_B_contDiff2 p ε hε)).2.2).locallyLipschitz
  have hBc : Continuous (A_eps_B p ε) := (c10_aux_B_contDiff p ε hε).continuous
  have hr'd : ∀ᵐ y, DifferentiableAt ℝ (deriv r) y := c10_aux_ae_differentiableAt hr.1.2
  have gd : ∀ k y, DifferentiableAt ℝ (fk k) y := fun k y => (hk k).1.differentiable (by norm_num) y
  have gd' : ∀ k y, DifferentiableAt ℝ (deriv (fk k)) y := fun k y => (dk k).differentiable one_ne_zero y
  have fd : ∀ y, DifferentiableAt ℝ fbar y := fun y => hC2.differentiable (by norm_num) y
  have fd' : ∀ y, DifferentiableAt ℝ (deriv fbar) y := fun y => df.differentiable one_ne_zero y
  fin_cases j
  · show c10_Ieps_local_continuity_W1inf (fun k => c10_N_pieces_N1 p ε (fk k) r)
      (c10_N_pieces_N1 p ε fbar r) R
    refine c10_aux_W1inf_of_Conv ?_ ?_ fun k => ?_
    · exact c10_aux_Conv_mul (c10_aux_Conv_sub (c10_aux_Conv_comp hBl (c10_aux_Conv_add (F1 R) (R1 R)))
        (c10_aux_Conv_comp hBl (F1 R))) (c10_aux_Conv_sub (F0 R) (c10_aux_Conv_mul Y (F1 R)))
    · refine c10_aux_Conv_congr (c10_aux_Conv_add
        (c10_aux_Conv_mul (c10_aux_Conv_sub (c10_aux_Conv_mul (c10_aux_Conv_comp hB'l
          (c10_aux_Conv_add (F1 R) (R1 R))) (c10_aux_Conv_add (F2 R) (R2 R)))
          (c10_aux_Conv_mul (c10_aux_Conv_comp hB'l (F1 R)) (F2 R)))
          (c10_aux_Conv_sub (F0 R) (c10_aux_Conv_mul Y (F1 R))))
        (c10_aux_Conv_mul (c10_aux_Conv_sub (c10_aux_Conv_comp hBl (c10_aux_Conv_add (F1 R) (R1 R)))
          (c10_aux_Conv_comp hBl (F1 R)))
          (c10_aux_Conv_sub (F1 R) (c10_aux_Conv_add (c10_aux_Conv_mul One (F1 R))
            (c10_aux_Conv_mul Y (F2 R)))))) (fun k => ?_) ?_
      · filter_upwards [hr'd] with y hy _
        exact c10_aux_N1_hasDeriv p ε hε (gd k y) (gd' k y) hy
      · filter_upwards [hr'd] with y hy _
        exact c10_aux_N1_hasDeriv p ε hε (fd y) (fd' y) hy
    · apply Continuous.aestronglyMeasurable
      have := (dk k).continuous; have := (hk k).1.continuous; have := df.continuous
      have := hC2.continuous
      unfold c10_N_pieces_N1; fun_prop
  · show c10_Ieps_local_continuity_W1inf (fun k => c10_N_pieces_N2 p ε (fk k) r)
      (c10_N_pieces_N2 p ε fbar r) R
    refine c10_aux_W1inf_of_Conv ?_ ?_ fun k => ?_
    · exact c10_aux_Conv_mul (c10_aux_Conv_sub (c10_aux_Conv_comp hBl (c10_aux_Conv_add (F1 R) (R1 R)))
        One) (c10_aux_Conv_sub (R0 R) (c10_aux_Conv_mul Y (R1 R)))
    · refine c10_aux_Conv_congr (c10_aux_Conv_add
        (c10_aux_Conv_mul (c10_aux_Conv_mul (c10_aux_Conv_comp hB'l
          (c10_aux_Conv_add (F1 R) (R1 R))) (c10_aux_Conv_add (F2 R) (R2 R)))
          (c10_aux_Conv_sub (R0 R) (c10_aux_Conv_mul Y (R1 R))))
        (c10_aux_Conv_mul (c10_aux_Conv_sub (c10_aux_Conv_comp hBl (c10_aux_Conv_add (F1 R) (R1 R)))
          One)
          (c10_aux_Conv_sub (R1 R) (c10_aux_Conv_add (c10_aux_Conv_mul One (R1 R))
            (c10_aux_Conv_mul Y (R2 R)))))) (fun k => ?_) ?_
      · filter_upwards [hr'd] with y hy _
        exact c10_aux_N2_hasDeriv p ε hε (gd' k y) (hr.1.1.differentiable one_ne_zero y) hy
      · filter_upwards [hr'd] with y hy _
        exact c10_aux_N2_hasDeriv p ε hε (fd' y) (hr.1.1.differentiable one_ne_zero y) hy
    · apply Continuous.aestronglyMeasurable
      have := (dk k).continuous; have := df.continuous
      unfold c10_N_pieces_N2; fun_prop
  · show c10_Ieps_local_continuity_W1inf (fun k => c10_N_pieces_N3 p ε (fk k) r)
      (c10_N_pieces_N3 p ε fbar r) R
    obtain ⟨hp0, h1γ, -, -, -⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
    obtain ⟨Kr, hKr⟩ := c10_aux_X_deriv_bdd p γ h1γ.le (by linarith [show 0 < 1 / p by positivity]) hr
    have bk : ∀ k y, |deriv (fk k) y| ≤ M + 1 := fun k y => c10_aux_admissible_deriv_le p M hp0 (hk k) y
    have bf : ∀ y, |deriv fbar y| ≤ M + 1 := fun y => c10_aux_admissible_deriv_le p M hp0 hf y
    have Wk : ∀ k, W2inftyLoc (fk k) := fun k => ⟨(hk k).1.of_le (by norm_num), (dk k).locallyLipschitz⟩
    have Wf : W2inftyLoc fbar := ⟨hC2.of_le (by norm_num), df.locallyLipschitz⟩
    have dadd : ∀ g : ℝ → ℝ, (∀ y, DifferentiableAt ℝ g y) → deriv (g + r) = deriv g + deriv r :=
      fun g hg => funext fun y => deriv_add (hg y) (hr.1.1.differentiable one_ne_zero y)
    have Wadd : ∀ g : ℝ → ℝ, W2inftyLoc g → W2inftyLoc (g + r) := fun g hg => by
      refine ⟨hg.1.add hr.1.1, ?_⟩
      rw [dadd g fun y => hg.1.differentiable one_ne_zero y]
      exact hg.2.add hr.1.2
    have badd : ∀ g : ℝ → ℝ, (∀ y, DifferentiableAt ℝ g y) → (∀ y, |deriv g y| ≤ M + 1) →
        ∀ y, |deriv (g + r) y| ≤ M + 1 + Kr := fun g hg hb y => by
      rw [dadd g hg, Pi.add_apply]; exact (abs_add_le _ _).trans (add_le_add (hb y) (hKr y))
    -- the two applications of lem:c10_Ieps_local_continuity
    have IA := c10_Ieps_local_continuity p ε hp hp1 hε hε1 (fun k => fk k + r) (fbar + r)
      (fun k => Wadd _ (Wk k)) (Wadd _ Wf)
      ⟨M + 1 + Kr, fun k => badd _ (gd k) (bk k), badd _ fd bf⟩ (fun R' hR' => by
        refine ⟨c10_aux_W1inf_of_Conv (c10_aux_Conv_add (F0 R') (R0 R'))
          (c10_aux_Conv_congr (c10_aux_Conv_add (F1 R') (R1 R'))
            (fun k => ae_of_all _ fun y _ => by rw [dadd _ (gd k)]; rfl)
            (ae_of_all _ fun y _ => by rw [dadd _ fd]; rfl)) fun k => ?_, ?_⟩
        · exact (((hk k).1.continuous.add rc).sub (hC2.continuous.add rc)).aestronglyMeasurable
        · refine c10_aux_Conv_tendsto measurableSet_Icc (c10_aux_Conv_congr
            (c10_aux_Conv_add (F2 R') (R2 R')) (fun k => ?_) ?_) fun k =>
            ((measurable_deriv _).sub (measurable_deriv _)).aestronglyMeasurable
          · filter_upwards [hr'd] with y hy _
            rw [dadd _ (gd k)]; exact deriv_add (gd' k y) hy
          · filter_upwards [hr'd] with y hy _
            rw [dadd _ fd]; exact deriv_add (fd' y) hy) R hR
    have IB := c10_Ieps_local_continuity p ε hp hp1 hε hε1 fk fbar Wk Wf ⟨M + 1, bk, bf⟩
      (fun R' hR' => ⟨c10_aux_W1inf_of_Conv (F0 R') (F1 R')
        (fun k => ((hk k).1.continuous.sub hC2.continuous).aestronglyMeasurable),
        c10_aux_Conv_tendsto measurableSet_Icc (F2 R') fun k =>
          ((measurable_deriv _).sub (measurable_deriv _)).aestronglyMeasurable⟩) R hR
    -- regularity of the four `ℐ_ε` terms
    have hloc := (c10_Ieps_local p hp hp1).1 ε hε hε1
    have LA : ∀ k, W1inftyLoc (c10_N_pieces_I p ε (fk k + r)) := fun k =>
      (hloc _ (Wadd _ (Wk k)) ⟨_, badd _ (gd k) (bk k)⟩).1
    have LB : ∀ k, W1inftyLoc (c10_N_pieces_I p ε (fk k)) := fun k => (hloc _ (Wk k) ⟨_, bk k⟩).1
    have LA' : W1inftyLoc (c10_N_pieces_I p ε (fbar + r)) := (hloc _ (Wadd _ Wf) ⟨_, badd _ fd bf⟩).1
    have LB' : W1inftyLoc (c10_N_pieces_I p ε fbar) := (hloc _ Wf ⟨_, bf⟩).1
    have hb : ∀ᵐ y, DifferentiableAt ℝ (fun x => b_eps p ε x * deriv r x) y := by
      filter_upwards [hr'd] with y hy
      exact ((c10_aux_b_eps_contDiff p ε).differentiable one_ne_zero y).mul hy
    have dA := ae_all_iff.2 fun k => c10_aux_ae_differentiableAt (LA k)
    have dB := ae_all_iff.2 fun k => c10_aux_ae_differentiableAt (LB k)
    have dA' := c10_aux_ae_differentiableAt LA'
    have dB' := c10_aux_ae_differentiableAt LB'
    have hder : ∀ g : ℝ → ℝ, ∀ y, DifferentiableAt ℝ (c10_N_pieces_I p ε (g + r)) y →
        DifferentiableAt ℝ (c10_N_pieces_I p ε g) y →
        DifferentiableAt ℝ (fun x => b_eps p ε x * deriv r x) y →
        deriv (c10_N_pieces_N3 p ε g r) y = deriv (c10_N_pieces_I p ε (g + r)) y -
          deriv (c10_N_pieces_I p ε g) y - deriv (fun x => b_eps p ε x * deriv r x) y :=
      fun g y h1 h2 h3 => ((h1.hasDerivAt.sub h2.hasDerivAt).sub h3.hasDerivAt).deriv
    unfold c10_Ieps_local_continuity_W1inf at IA IB ⊢
    have hsum := IA.add IB
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun k => zero_le) fun k => ?_
    have top : (1 : ℝ≥0∞) ≤ ⊤ := le_top
    have ev : (fun y => c10_N_pieces_N3 p ε (fk k) r y - c10_N_pieces_N3 p ε fbar r y) =
        (fun y => c10_N_pieces_I p ε (fk k + r) y - c10_N_pieces_I p ε (fbar + r) y) -
          (fun y => c10_N_pieces_I p ε (fk k) y - c10_N_pieces_I p ε fbar y) := by
      funext y; simp only [c10_N_pieces_N3, Pi.sub_apply]; ring
    have ed : (fun y => deriv (c10_N_pieces_N3 p ε (fk k) r) y -
        deriv (c10_N_pieces_N3 p ε fbar r) y) =ᵐ[volume.restrict (Icc (-R) R)]
        (fun y => deriv (c10_N_pieces_I p ε (fk k + r)) y -
            deriv (c10_N_pieces_I p ε (fbar + r)) y) -
          (fun y => deriv (c10_N_pieces_I p ε (fk k)) y - deriv (c10_N_pieces_I p ε fbar) y) := by
      refine ae_restrict_of_ae ?_
      filter_upwards [dA, dB, dA', dB', hb] with y h1 h2 h3 h4 h5
      simp only [Pi.sub_apply]
      rw [hder _ y (h1 k) (h2 k) h5, hder _ y h3 h4 h5]; ring
    simp only at ev ed ⊢
    rw [ev, eLpNorm_congr_ae ed]
    calc _ ≤ (eLpNorm (fun y => c10_N_pieces_I p ε (fk k + r) y -
            c10_N_pieces_I p ε (fbar + r) y) ⊤ (volume.restrict (Icc (-R) R)) +
          eLpNorm (fun y => c10_N_pieces_I p ε (fk k) y - c10_N_pieces_I p ε fbar y) ⊤
            (volume.restrict (Icc (-R) R))) +
          (eLpNorm (fun y => deriv (c10_N_pieces_I p ε (fk k + r)) y -
            deriv (c10_N_pieces_I p ε (fbar + r)) y) ⊤ (volume.restrict (Icc (-R) R)) +
          eLpNorm (fun y => deriv (c10_N_pieces_I p ε (fk k)) y -
            deriv (c10_N_pieces_I p ε fbar) y) ⊤ (volume.restrict (Icc (-R) R))) :=
          add_le_add (eLpNorm_sub_le top) (eLpNorm_sub_le top)
      _ = _ := by ring

/-! ### Assembly -/

/-- Blueprint: lem:c10_N_admissible_bounds.  For `0 ≤ ε ≤ min(1,ε₀)` (`ε₀` of
lem:linear_conjugation) and `f̄` admissible with constant `M` (satisfying the hypotheses of
lem:c10_N_decomposition): `𝒩_{ε,f̄}(r) ∈ Y_γ`, and the Lipschitz and size bounds with
`C = C(p,γ,M,N)` independent of `ε`, `f̄`. -/
theorem c10_N_admissible_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ ε₀ > 0, ∀ γ M N : ℝ, admissibleGamma p γ → 0 < M → 0 < N →
      ∃ C > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ min 1 ε₀ →
        ∀ fbar : ℝ → ℝ, nonlinear_admissible_profile p M fbar → c10_N_decomposition_hyp p fbar →
        (∀ r ∈ X_gamma p γ, xNorm p γ r ≤ N →
          N_eps p ε fbar r ∈ Y_gamma p γ ∧ yNorm p γ (N_eps p ε fbar r) ≤ C * ε * xNorm p γ r) ∧
        (∀ r₁ ∈ X_gamma p γ, ∀ r₂ ∈ X_gamma p γ, xNorm p γ r₁ ≤ N → xNorm p γ r₂ ≤ N →
          yNorm p γ (fun y => N_eps p ε fbar r₁ y - N_eps p ε fbar r₂ y) ≤
            C * ε * xNorm p γ (r₁ - r₂)) := by
  obtain ⟨ε₁, hε₁, hdec⟩ := c10_N_decomposition p hp hp1
  obtain ⟨ε₂, hε₂, hR⟩ := c10_ext_linear_conjugation_R p hp hp1
  obtain ⟨ε₃, hε₃, hRi⟩ := c10_ext_conj_nonlocal_integrable p hp hp1
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), fun γ M N hγ hM hN => ?_⟩
  obtain ⟨hp0, -, -, hγa, hγb⟩ := c10_aux_gamma_facts p γ hp hp1 hγ
  obtain ⟨C₁, hC₁, h₁⟩ := N1 p γ M N hp hp1 hγ hM hN
  obtain ⟨C₂, hC₂, h₂⟩ := N2 p γ M N hp hp1 hγ hM hN
  obtain ⟨C₃, hC₃, h₃⟩ := N3 p γ M N hp hp1 hγ hM hN
  obtain ⟨CR, hCR, hR'⟩ := hR γ hγ
  refine ⟨C₁ + C₂ + C₃ + CR, by positivity, fun ε hε hεle fbar hadm hhyp => ?_⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
  have hεm : ε ≤ min 1 ε₁ :=
    le_min hε1 (hεle.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε2 : ε ≤ ε₂ := hεle.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hε3 : ε ≤ ε₃ := hεle.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hint : ∀ r ∈ c01_admissible_class, ∀ y,
      Integrable (fun z => R_eps_kernel p ε y z * deriv r z) := fun r hr =>
    hRi ε hε hε3 r hr.1 hr.2.1 hr.2.2
  have lip : ∀ r₁ ∈ X_gamma p γ, ∀ r₂ ∈ X_gamma p γ, xNorm p γ r₁ ≤ N → xNorm p γ r₂ ≤ N →
      (fun y => N_eps p ε fbar r₁ y - N_eps p ε fbar r₂ y) ∈ Y_gamma p γ ∧
      yNorm p γ (fun y => N_eps p ε fbar r₁ y - N_eps p ε fbar r₂ y) ≤
        (C₁ + C₂ + C₃ + CR) * ε * xNorm p γ (r₁ - r₂) := by
    intro r₁ hr₁ r₂ hr₂ hN₁ hN₂
    obtain ⟨-, e₁, -⟩ := hdec γ hγ ε hε hεm fbar hhyp r₁ hr₁
    obtain ⟨-, e₂, -⟩ := hdec γ hγ ε hε hεm fbar hhyp r₂ hr₂
    have hsub := c10_aux_X_sub p γ hr₁ hr₂
    obtain ⟨m₁, b₁⟩ := h₁ ε hε hε1 fbar hadm r₁ hr₁ r₂ hr₂ hN₁ hN₂
    obtain ⟨m₂, b₂⟩ := h₂ ε hε hε1 fbar hadm r₁ hr₁ r₂ hr₂ hN₁ hN₂
    obtain ⟨m₃, b₃⟩ := h₃ ε hε hε1 fbar hadm r₁ hr₁ r₂ hr₂ hN₁ hN₂
    obtain ⟨mR, bR⟩ := hR' ε hε hε2 (r₁ - r₂) hsub
    obtain ⟨mR', bR'⟩ := c10_aux_Y_neg p γ mR
    obtain ⟨m12, b12⟩ := c10_aux_Y_add p γ m₁ m₂
    obtain ⟨m123, b123⟩ := c10_aux_Y_add p γ m12 m₃
    obtain ⟨mall, ball⟩ := c10_aux_Y_add p γ m123 mR'
    have heq : (fun y => N_eps p ε fbar r₁ y - N_eps p ε fbar r₂ y) =
        (fun y => c10_N_pieces_N1 p ε fbar r₁ y - c10_N_pieces_N1 p ε fbar r₂ y) +
          (fun y => c10_N_pieces_N2 p ε fbar r₁ y - c10_N_pieces_N2 p ε fbar r₂ y) +
          (fun y => c10_N_pieces_N3 p ε fbar r₁ y - c10_N_pieces_N3 p ε fbar r₂ y) +
          -R_eps p ε (r₁ - r₂) := by
      funext y
      have hRs := c10_aux_R_eps_sub p ε hint (c10_aux_X_admissible_class p γ hp hp1 hγ hr₁)
        (c10_aux_X_admissible_class p γ hp hp1 hγ hr₂) y
      simp only [Pi.add_apply, Pi.neg_apply, e₁ y, e₂ y, ← hRs]
      ring
    rw [heq]
    refine ⟨mall, ?_⟩
    have hx : 0 ≤ xNorm p γ (r₁ - r₂) := ENNReal.toReal_nonneg
    rw [bR'] at ball
    nlinarith
  refine ⟨fun r hr hrN => ?_, fun r₁ hr₁ r₂ hr₂ hN₁ hN₂ => (lip r₁ hr₁ r₂ hr₂ hN₁ hN₂).2⟩
  obtain ⟨hz, hz0⟩ := c10_aux_X_zero p γ
  obtain ⟨-, -, e0⟩ := hdec γ hγ ε hε hεm fbar hhyp r hr
  have heq : N_eps p ε fbar r = fun y => N_eps p ε fbar r y - N_eps p ε fbar 0 y := by
    funext y; rw [e0 y, sub_zero]
  have := lip r hr 0 hz hrN (by rw [hz0]; exact hN.le)
  rw [sub_zero] at this
  rw [heq]; exact this

/-- Statement of thm:fixed_point_approximation (`GSQG.fixed_point_approximation`), proved here from
the identical chapter-07 statement `GSQG.approx_assembly`. -/
theorem c10_ext_fixed_point_approximation (P : parameters) :
    ∃ R₀ > 0, ∃ δ₀ > 0, ∀ R ≥ R₀, ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ ε₀ > 0, fixed_point_approximation_statement P R δ ε₀ :=
  approx_assembly P

/-- Helper: `‖v‖_∞ ≤ ‖u₁‖_∞ + ‖u₂‖_∞ + ‖u₃‖_∞` under an a.e. pointwise bound (`v` measurable). -/
theorem c10_aux_eLpNorm_top_le3 {μ : Measure ℝ} {v u₁ u₂ u₃ : ℝ → ℝ}
    (hv : AEStronglyMeasurable v μ) (h : ∀ᵐ y ∂μ, ‖v y‖ ≤ ‖u₁ y‖ + ‖u₂ y‖ + ‖u₃ y‖) :
    eLpNorm v ⊤ μ ≤ eLpNorm u₁ ⊤ μ + eLpNorm u₂ ⊤ μ + eLpNorm u₃ ⊤ μ := by
  by_cases h₁ : AEStronglyMeasurable u₁ μ
  · by_cases h₂ : AEStronglyMeasurable u₂ μ
    · by_cases h₃ : AEStronglyMeasurable u₃ μ
      · rw [eLpNorm_exponent_top hv, eLpNorm_exponent_top h₁, eLpNorm_exponent_top h₂,
          eLpNorm_exponent_top h₃]
        unfold eLpNormEssSup
        refine le_trans (essSup_mono_ae ?_) (le_trans (ENNReal.essSup_add_le _ _)
          (add_le_add (ENNReal.essSup_add_le _ _) le_rfl))
        filter_upwards [h] with y hy
        simp only [Pi.add_apply]
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
          ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hy
      · rw [eLpNorm_of_not_aestronglyMeasurable h₃]; simp
    · rw [eLpNorm_of_not_aestronglyMeasurable h₂]; simp
  · rw [eLpNorm_of_not_aestronglyMeasurable h₁]; simp

/-- Blueprint: prop:nonlinear_continuity.  For `0 ≤ ε ≤ min(1,ε₀)` (`ε₀` of
lem:linear_conjugation), `β + 1/p < γ' < γ < 2p+1`, `r ∈ X_γ`, admissible `f̄_k → f̄` in `C²_loc`
with common constant `M` (all satisfying the hypotheses of lem:c10_N_decomposition):
`𝒩_{ε,f̄_k}(r) → 𝒩_{ε,f̄}(r)` in `Y_{γ'}`. -/
theorem nonlinear_continuity (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ min 1 ε₀ → ∀ γ γ' : ℝ, beta p + 1 / p < γ' → γ' < γ →
      γ < 2 * p + 1 → ∀ r ∈ X_gamma p γ, ∀ M : ℝ, 0 < M →
      ∀ (fk : ℕ → ℝ → ℝ) (fbar : ℝ → ℝ),
        (∀ k, nonlinear_admissible_profile p M (fk k)) → c10_admissible_closed_C2loc fk fbar →
        (∀ k, c10_N_decomposition_hyp p (fk k)) → c10_N_decomposition_hyp p fbar →
        Tendsto (fun k => Y_gamma_norm p γ' (fun y => N_eps p ε (fk k) r y - N_eps p ε fbar r y))
          atTop (nhds 0) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨εB, hεB, hB⟩ := c10_N_admissible_bounds p hp hp1
  obtain ⟨εD, hεD, hdec⟩ := c10_N_decomposition p hp hp1
  refine ⟨min εB εD, lt_min hεB hεD,
    fun ε hε hεle γ γ' h1 h2 h3 r hr M hM fk fbar hk hconv hkd hfd => ?_⟩
  have hγ : admissibleGamma p γ := ⟨by linarith, h3⟩
  have hγ'pos : 0 < γ' := by
    have : 0 < beta p := by unfold beta; positivity
    have : 0 < 1 / p := by positivity
    linarith
  have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
  have hεB' : ε ≤ min 1 εB := le_min hε1 (hεle.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεD' : ε ≤ min 1 εD :=
    le_min hε1 (hεle.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hf := c10_admissible_closed p M fk fbar hk hconv
  set N := xNorm p γ r + 1 with hNdef
  have hN : 0 < N := by have : 0 ≤ xNorm p γ r := ENNReal.toReal_nonneg; linarith
  have hrN : xNorm p γ r ≤ N := by linarith
  obtain ⟨C, hC, hCb⟩ := hB γ M N hγ hM hN
  obtain ⟨C1, -, n1⟩ := N1 p γ M N hp hp1 hγ hM hN
  obtain ⟨C2, -, n2⟩ := N2 p γ M N hp hp1 hγ hM hN
  obtain ⟨C3, -, n3⟩ := N3 p γ M N hp hp1 hγ hM hN
  obtain ⟨hz, hz0⟩ := c10_aux_X_zero p γ
  have hz0N : xNorm p γ (0 : ℝ → ℝ) ≤ N := by rw [hz0]; exact hN.le
  -- each piece is in `Y_γ`
  have piece : ∀ g, nonlinear_admissible_profile p M g → ∀ j : Fin 3,
      c10_N_pieces p ε g r j ∈ Y_gamma p γ := by
    intro g hg j
    fin_cases j
    · have := (n1 ε hε hε1 g hg r hr 0 hz hrN hz0N).1
      convert this using 1; funext y; simp [c10_N_pieces, c10_N_pieces_N1]
    · have := (n2 ε hε hε1 g hg r hr 0 hz hrN hz0N).1
      convert this using 1; funext y; simp [c10_N_pieces, c10_N_pieces_N2]
    · have := (n3 ε hε hε1 g hg r hr 0 hz hrN hz0N).1
      convert this using 1; funext y; simp [c10_N_pieces, c10_N_pieces_N3]
  set G : ℕ → ℝ → ℝ := fun k => N_eps p ε (fk k) r with hG
  set Gl : ℝ → ℝ := N_eps p ε fbar r with hGl
  have hGY : ∀ k, G k ∈ Y_gamma p γ := fun k => ((hCb ε hε hεB' _ (hk k) (hkd k)).1 r hr hrN).1
  have hGlY : Gl ∈ Y_gamma p γ := ((hCb ε hε hεB' _ hf hfd).1 r hr hrN).1
  have hbd : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ k, Y_gamma_norm p γ (G k) ≤ B := by
    refine ⟨ENNReal.ofReal (C * ε * xNorm p γ r), ENNReal.ofReal_ne_top, fun k => ?_⟩
    rw [← ENNReal.ofReal_toReal (hGY k).2.ne]
    exact ENNReal.ofReal_le_ofReal ((hCb ε hε hεB' _ (hk k) (hkd k)).1 r hr hrN).2
  -- the difference as a sum of the three piece differences
  set d : Fin 3 → ℕ → ℝ → ℝ := fun j k y => c10_N_pieces p ε (fk k) r j y - c10_N_pieces p ε fbar r j y
    with hd
  have hsplit : ∀ k y, G k y - Gl y = d 0 k y + d 1 k y + d 2 k y := by
    intro k y
    have e1 := (hdec γ hγ ε hε hεD' (fk k) (hkd k) r hr).2.1 y
    have e2 := (hdec γ hγ ε hε hεD' fbar hfd r hr).2.1 y
    simp only [hG, hGl, hd, e1, e2, c10_N_pieces]
    simp
    ring
  have hloc : ∀ R : ℝ, Tendsto (fun k =>
      eLpNorm (G k - Gl) ⊤ (volume.restrict (Ioo (-R) R)) +
      eLpNorm (deriv (G k) - deriv Gl) ⊤ (volume.restrict (Ioo (-R) R))) atTop (nhds 0) := by
    intro R
    set R' := |R| + 1 with hR'
    have hR'pos : 0 < R' := by positivity
    have hsub : Ioo (-R) R ⊆ Icc (-R') R' := fun x hx =>
      ⟨by linarith [hx.1, le_abs_self R, hR'], by linarith [hx.2, le_abs_self R, hR']⟩
    have hμ : volume.restrict (Ioo (-R) R) ≤ volume.restrict (Icc (-R') R') :=
      Measure.restrict_mono hsub le_rfl
    have hconvj := fun j => c10_N_local_convergence p γ M ε hp hp1 hγ hM hε hε1 r hr fk fbar hk hconv
      j R' hR'pos
    set a : Fin 3 → ℕ → ℝ≥0∞ := fun j k =>
      eLpNorm (fun y => c10_N_pieces p ε (fk k) r j y - c10_N_pieces p ε fbar r j y) ⊤
          (volume.restrict (Icc (-R') R')) +
        eLpNorm (fun y => deriv (c10_N_pieces p ε (fk k) r j) y - deriv (c10_N_pieces p ε fbar r j) y) ⊤
          (volume.restrict (Icc (-R') R')) with ha
    have hlim : Tendsto (fun k => a 0 k + a 1 k + a 2 k) atTop (nhds 0) := by
      have := ((hconvj 0).add (hconvj 1)).add (hconvj 2)
      simpa [ha] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => bot_le) (fun k => ?_)
    -- pointwise bounds
    have hcont : ∀ g, nonlinear_admissible_profile p M g → ∀ j : Fin 3,
        LocallyLipschitz (c10_N_pieces p ε g r j) := fun g hg j => (piece g hg j).1
    have hv1 : AEStronglyMeasurable (G k - Gl) (volume.restrict (Icc (-R') R')) :=
      ((hGY k).1.continuous.sub hGlY.1.continuous).aestronglyMeasurable
    have hv2 : AEStronglyMeasurable (deriv (G k) - deriv Gl) (volume.restrict (Icc (-R') R')) :=
      ((measurable_deriv _).sub (measurable_deriv _)).aestronglyMeasurable
    have b1 := c10_aux_eLpNorm_top_le3 (u₁ := d 0 k) (u₂ := d 1 k) (u₃ := d 2 k) hv1
      (ae_of_all _ fun y => by
        simp only [Pi.sub_apply]; rw [hsplit k y]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
    have hDiff : ∀ g, nonlinear_admissible_profile p M g → ∀ j : Fin 3,
        ∀ᵐ y, DifferentiableAt ℝ (c10_N_pieces p ε g r j) y := fun g hg j =>
      c10_aux_ae_differentiableAt (hcont g hg j)
    have hDGl := c10_aux_ae_differentiableAt hGlY.1
    have b2 := c10_aux_eLpNorm_top_le3 (μ := volume.restrict (Icc (-R') R'))
      (u₁ := fun y => deriv (c10_N_pieces p ε (fk k) r 0) y - deriv (c10_N_pieces p ε fbar r 0) y)
      (u₂ := fun y => deriv (c10_N_pieces p ε (fk k) r 1) y - deriv (c10_N_pieces p ε fbar r 1) y)
      (u₃ := fun y => deriv (c10_N_pieces p ε (fk k) r 2) y - deriv (c10_N_pieces p ε fbar r 2) y)
      hv2 (ae_restrict_of_ae (by
        filter_upwards [hDiff _ (hk k) 0, hDiff _ (hk k) 1, hDiff _ (hk k) 2, hDiff _ hf 0,
          hDiff _ hf 1, hDiff _ hf 2, hDGl] with y a0 a1 a2 c0 c1 c2 cg
        have hGk : G k = fun x => Gl x + (d 0 k x + d 1 k x + d 2 k x) := by
          funext x; rw [← hsplit k x]; ring
        have : deriv (G k) y - deriv Gl y =
            (deriv (c10_N_pieces p ε (fk k) r 0) y - deriv (c10_N_pieces p ε fbar r 0) y) +
            (deriv (c10_N_pieces p ε (fk k) r 1) y - deriv (c10_N_pieces p ε fbar r 1) y) +
            (deriv (c10_N_pieces p ε (fk k) r 2) y - deriv (c10_N_pieces p ε fbar r 2) y) := by
          rw [hGk]
          have := cg.hasDerivAt.add (((a0.hasDerivAt.sub c0.hasDerivAt).add
            (a1.hasDerivAt.sub c1.hasDerivAt)).add (a2.hasDerivAt.sub c2.hasDerivAt))
          have e : deriv (fun x => Gl x + (d 0 k x + d 1 k x + d 2 k x)) y = _ := this.deriv
          rw [e]; ring
        simp only [Pi.sub_apply]; rw [this]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)))
    calc eLpNorm (G k - Gl) ⊤ (volume.restrict (Ioo (-R) R)) +
          eLpNorm (deriv (G k) - deriv Gl) ⊤ (volume.restrict (Ioo (-R) R))
        ≤ eLpNorm (G k - Gl) ⊤ (volume.restrict (Icc (-R') R')) +
          eLpNorm (deriv (G k) - deriv Gl) ⊤ (volume.restrict (Icc (-R') R')) :=
          add_le_add (eLpNorm_mono_measure _ hμ) (eLpNorm_mono_measure _ hμ)
      _ ≤ _ := add_le_add b1 b2
      _ = a 0 k + a 1 k + a 2 k := by simp only [ha, hd]; ring
  exact ((appendix_convergence p γ γ' hp0 hγ'pos h2).2 G Gl hGY hbd hGlY.1 hloc).2

-- Encoding: "ε₀, δ, B̄, f̄_{ε,μ} as in thm:fixed_point_approximation" is encoded exactly as
-- in chapter 02's thm:fixed_point_nonlinear_estimates: for all `R ≥ R₀`, `δ ∈ (0,δ₀]` there is
-- `ε₀ > 0` with the shared predicate `fixed_point_nonlinear_estimates_statement P R δ ε₀`.
/-- Blueprint: lem:nonlinear_assembly (= conclusion of thm:fixed_point_nonlinear_estimates,
via the shared predicate `fixed_point_nonlinear_estimates_statement`).
(1)–(2): for admissible `γ` and `N > 0` there is `C_𝒩(γ,N)` with, for `0 ≤ ε ≤ ε₀`, `μ ∈ B̄`,
`‖r‖, ‖r₁‖, ‖r₂‖ ≤ N`: `𝒩_{ε,f̄}(r) ∈ Y_γ`, `‖𝒩_{ε,f̄}(r)‖_{Y_γ} ≤ C_𝒩 ε ‖r‖_{X_γ}` and
`‖𝒩_{ε,f̄}(r₁) - 𝒩_{ε,f̄}(r₂)‖_{Y_γ} ≤ C_𝒩 ε ‖r₁ - r₂‖_{X_γ}`;
(3): for `r ∈ X_{γ₂}`, `μ ↦ 𝒩_{ε,f̄_{ε,μ}}(r)` is continuous `B̄ → Y_{γ₁}`. -/
theorem nonlinear_assembly (P : parameters) :
    ∃ R₀ > 0, ∃ δ₀ > 0, ∀ R ≥ R₀, ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ ε₀ > 0, fixed_point_nonlinear_estimates_statement P R δ ε₀ := by
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  obtain ⟨RF, hRF, δF, hδF, hF⟩ := c10_ext_fixed_point_approximation P
  obtain ⟨εA, hεA, δA, hδA, RA, hA⟩ := c10_approx_admissible P.p hp hp1
  obtain ⟨εB, hεB, hB⟩ := c10_N_admissible_bounds P.p hp hp1
  obtain ⟨εC, hεC, hC⟩ := nonlinear_continuity P.p hp hp1
  refine ⟨max RF RA, lt_max_of_lt_left hRF, min δF δA, lt_min hδF hδA,
    fun R hR δ hδ hδle => ?_⟩
  obtain ⟨εF, hεF, hFs⟩ := hF R ((le_max_left _ _).trans hR) δ hδ (hδle.trans (min_le_left _ _))
  obtain ⟨M₀, hM₀, hadm⟩ := hA R ((le_max_right _ _).trans hR)
  have hBsub : Bbar P.p δ ⊆ Bbar P.p δA :=
    Metric.closedBall_subset_closedBall (hδle.trans (min_le_right _ _))
  refine ⟨min (min εF εA) (min 1 (min εB εC)),
    lt_min (lt_min hεF hεA) (lt_min one_pos (lt_min hεB hεC)), ?_, ?_⟩
  · intro γ hγ N hN
    obtain ⟨C, hCpos, hCb⟩ := hB γ M₀ N hγ hM₀ hN
    refine ⟨C, hCpos, fun ε hε μ hμ => ?_⟩
    have hεA' : ε ≤ εA := hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hεB' : ε ≤ min 1 εB := le_min (hε.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hε.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have had := hadm ε hε.1 hεA' μ (hBsub hμ)
    have hb := hCb ε hε.1 hεB' _ had (c10_aux_admissible_decomposition_hyp P.p M₀ hp0 hp1 had)
    exact ⟨hb.1, fun r₁ hr₁ r₂ hr₂ h₁ h₂ => hb.2 r₁ hr₁ r₂ hr₂ h₁ h₂⟩
  · intro ε hε r hr μ hμ
    have hεF' : ε ≤ εF := hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hεA' : ε ≤ εA := hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hεC' : ε ≤ min 1 εC := le_min (hε.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hε.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have h4 := (hFs.2.2.2.2.2 ε ⟨hε.1, hεF'⟩ μ hμ).1
    have hadμ := hadm ε hε.1 hεA' μ (hBsub hμ)
    rw [tendsto_iff_seq_tendsto]
    intro x hx
    obtain ⟨K, hK⟩ := eventually_atTop.1 (tendsto_nhdsWithin_iff.1 hx).2
    rw [← tendsto_add_atTop_iff_nat K]
    set x' : ℕ → ℂ := fun n => x (n + K) with hx'
    have hx'B : ∀ n, x' n ∈ Bbar P.p δ := fun n => hK _ (Nat.le_add_left K n)
    have hx'T : Tendsto x' atTop (nhdsWithin μ (Bbar P.p δ)) :=
      hx.comp (tendsto_add_atTop_nat K)
    have hadk : ∀ n, nonlinear_admissible_profile P.p M₀
        (approximate_solution_family P.p R ε (x' n)) := fun n =>
      hadm ε hε.1 hεA' (x' n) (hBsub (hx'B n))
    have hconv : c10_admissible_closed_C2loc
        (fun n => approximate_solution_family P.p R ε (x' n))
        (approximate_solution_family P.p R ε μ) := by
      refine ⟨hadμ.1, fun j hj R' => ?_⟩
      have hu := h4 (Icc (-R') R') isCompact_Icc j hj
      exact fun u hu' => hx'T.eventually (hu u hu')
    have hlim := hC ε hε.1 hεC' P.γ₂ P.γ₁ P.hγ₁ P.hγ₁₂ P.hγ₂ r hr M₀ hM₀
      (fun n => approximate_solution_family P.p R ε (x' n))
      (approximate_solution_family P.p R ε μ) hadk hconv
      (fun n => c10_aux_admissible_decomposition_hyp P.p M₀ hp0 hp1 (hadk n))
      (c10_aux_admissible_decomposition_hyp P.p M₀ hp0 hp1 hadμ)
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    simp only [ENNReal.toReal_zero, Function.comp_def] at this
    exact this

end GSQG
