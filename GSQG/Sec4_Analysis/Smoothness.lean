import GSQG.SchauderEstimate.Reconstruction
import GSQG.SchauderEstimate.Commutator

/-!
# §4: Schauder estimate, linear gain and the smoothness bootstrap (Theorem 3.5)

Blueprint ch. 03 (second part). This file is separate from `Sec4_Analysis/Equation.lean` so that
`c03_schauder_RS` can be proved from the `SchauderEstimate/` modules (which import
`Sec4_Analysis/Equation`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

-- Cited in the paper (§4) as Ros-Oton–Serra, Cor. 2.4; this is Prop. 2.2 of the arXiv version with
-- n = 1, stated for smooth `w` and β, β+p ∉ ℕ. Proved from the `SchauderEstimate/` modules
-- (`c12_compact_schauder`, `c12_localized_rhs`, `c12_holder_translation`).
/-- Blueprint: lem:c03_schauder_RS.  Interior Schauder estimate for `|D|^p`:
`‖w‖_{C^{β+p}([-½,½])} ≤ C(‖w‖_{C^β(ℝ)} + ‖|D|^p w‖_{C^β([-1,1])})` for smooth `w ∈ C^β(ℝ)`. -/
theorem c03_schauder_RS (p β : ℝ) (hp : 0 < p) (hp1 : p < 1) (hβ : 0 < β)
    (hβN : ∀ n : ℕ, β ≠ n) (hβpN : ∀ n : ℕ, β + p ≠ n) :
    ∃ C, 0 < C ∧ ∀ w : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) w → w ∈ c03_holder β univ →
      c03_holder_normR (β + p) (Icc (-1 / 2) (1 / 2)) w ≤
        C * (c03_holder_normR β univ w + c03_holder_normR β (Icc (-1) 1) (fracD p w)) := by
  obtain ⟨C1, hC1, hloc⟩ := c12_localized_rhs p β hp hp1 hβ hβN
  obtain ⟨C2, hC2, hcs⟩ := c12_compact_schauder p β hp hp1 hβ hβN hβpN
  refine ⟨C2 * (1 + C1), by positivity, fun w hw hwβ => ?_⟩
  obtain ⟨hvs, hvc, hh, hhb, hvb⟩ := hloc w hw hwβ
  obtain ⟨hvmem, hvb2⟩ := hcs _ hvs hvc hh
  have hglob := hvb2 _ hvb
  have hres := ((c12_holder_translation (β + p) (by linarith) hβpN 0 _ hvmem).2.2
    (-1 / 2) (1 / 2) (by norm_num)).2
  have hcongr : c03_holder_normR (β + p) (Icc (-1 / 2) (1 / 2)) w =
      c03_holder_normR (β + p) (Icc (-1 / 2) (1 / 2)) (fun x => c12_eta x * w x) :=
    (c03_aux_holder_congr fun x hx => by rw [c12r_aux_eta_one x hx, one_mul]).2.2.1
  have hW := c03_aux_normR_nonneg β univ w
  have hF := c03_aux_normR_nonneg β (Icc (-1) 1) (fracD p w)
  rw [hcongr]
  calc _ ≤ _ := hres
    _ ≤ _ := hglob
    _ ≤ C2 * (c03_holder_normR β univ w +
          C1 * (c03_holder_normR β univ w + c03_holder_normR β (Icc (-1) 1) (fracD p w))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hhb) hC2.le
    _ ≤ _ := by
        have : 0 ≤ C2 * C1 * c03_holder_normR β (Icc (-1) 1) (fracD p w) := by positivity
        nlinarith

/-- Blueprint: lem:c03_gain_localization.  The tail term
`T(y) = -c_p ∫ (1-η(z)) g(z) |z-y|^{-1-p} dz`. -/
def c03_gain_localization_T (p : ℝ) (η g : ℝ → ℝ) (y : ℝ) : ℝ :=
  -(c03_cp p) * ∫ z, (1 - η z) * g z / |z - y| ^ (1 + p)

/-- `(1+|z-y|)^{-r} ≤ 2^r (1+|z-y₀|)^{-r}` for `|y - y₀| ≤ 1`. -/
theorem c03_aux_peetre_shift {r : ℝ} (hr : 0 ≤ r) {y y₀ : ℝ} (hy : |y - y₀| ≤ 1) (z : ℝ) :
    (1 + |z - y|) ^ (-r) ≤ 2 ^ r * (1 + |z - y₀|) ^ (-r) := by
  have h1 : (1 + |z - y₀|) / 2 ≤ 1 + |z - y| := by
    have h2 : |z - y₀| ≤ |z - y| + |y - y₀| := abs_sub_le z y y₀
    have h3 := abs_nonneg (z - y)
    linarith
  calc (1 + |z - y|) ^ (-r) ≤ ((1 + |z - y₀|) / 2) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    _ = 2 ^ r * (1 + |z - y₀|) ^ (-r) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          div_eq_mul_inv, inv_inv]; ring

/-- Smoothness of `y ↦ ∫ G(z) κ(z-y) dz` for bounded measurable `G` and a smooth kernel with
integrable derivative decay. -/
theorem c03_aux_conv_smooth {κ : ℝ → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) {r : ℝ} (hr : 1 < r)
    (D : ℕ → ℝ) (hD : ∀ j t, |iteratedDeriv j κ t| ≤ D j * (1 + |t|) ^ (-r)) {G : ℝ → ℝ}
    (hG : Measurable G) {M : ℝ} (hM : ∀ z, |G z| ≤ M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ∫ z, G z * κ (z - y)) ∧
    ∀ j y, iteratedDeriv j (fun y => ∫ z, G z * κ (z - y)) y =
      (-1) ^ j * ∫ z, G z * iteratedDeriv j κ (z - y) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hint0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-r)) volume :=
    integrable_one_add_norm (by simp; linarith)
  have hintsh : ∀ y₀ : ℝ, Integrable (fun z : ℝ => (1 + |z - y₀|) ^ (-r)) := fun y₀ => by
    simpa [Real.norm_eq_abs] using hint0.comp_sub_right y₀
  have hcj : ∀ j, Continuous (iteratedDeriv j κ) := fun j =>
    hκ.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  set F : ℕ → ℝ → ℝ := fun j y => ∫ z, G z * iteratedDeriv j κ (z - y) with hF
  have hmeas : ∀ j y, AEStronglyMeasurable (fun z => G z * iteratedDeriv j κ (z - y)) volume :=
    fun j y => (hG.mul ((hcj j).measurable.comp (measurable_id.sub_const y))).aestronglyMeasurable
  have hderiv : ∀ j y₀, HasDerivAt (F j) (-(F (j + 1) y₀)) y₀ := by
    intro j y₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun y z => G z * iteratedDeriv j κ (z - y))
      (F' := fun y z => -(G z * iteratedDeriv (j + 1) κ (z - y)))
      (bound := fun z => M * D (j + 1) * (2 ^ r * (1 + |z - y₀|) ^ (-r)))
      (x₀ := y₀) (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ one_pos)
      (Eventually.of_forall fun y => hmeas j y)
      (by
        refine (((hintsh y₀).const_mul (M * D j))).mono' (hmeas j y₀)
          (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        calc |G z| * |iteratedDeriv j κ (z - y₀)| ≤ M * (D j * (1 + |z - y₀|) ^ (-r)) :=
              mul_le_mul (hM z) (hD j _) (abs_nonneg _) hM0
          _ = M * D j * (1 + |z - y₀|) ^ (-r) := by ring)
      ((hmeas (j + 1) y₀).neg)
      (Eventually.of_forall fun z y hy => by
        rw [norm_neg, Real.norm_eq_abs, abs_mul]
        have hy' : |y - y₀| ≤ 1 := by
          rw [Metric.mem_ball, Real.dist_eq] at hy; exact hy.le
        calc |G z| * |iteratedDeriv (j + 1) κ (z - y)|
            ≤ M * (D (j + 1) * (1 + |z - y|) ^ (-r)) :=
              mul_le_mul (hM z) (hD (j + 1) _) (abs_nonneg _) hM0
          _ ≤ M * (D (j + 1) * (2 ^ r * (1 + |z - y₀|) ^ (-r))) := by
              have hD0 : 0 ≤ D (j + 1) := by
                have := hD (j + 1) 0
                have h1 : 0 < (1 + |(0:ℝ)|) ^ (-r) := by positivity
                exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans this) h1
              gcongr
              exact c03_aux_peetre_shift (by linarith) hy' z
          _ = M * D (j + 1) * (2 ^ r * (1 + |z - y₀|) ^ (-r)) := by ring)
      (((hintsh y₀).const_mul (2 ^ r)).const_mul (M * D (j + 1)))
      (Eventually.of_forall fun z y _ => by
        have h1 : HasDerivAt (iteratedDeriv j κ) (iteratedDeriv (j + 1) κ (z - y)) (z - y) := by
          have := ((hκ.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _))
            (z - y)).hasDerivAt
          rwa [← iteratedDeriv_succ] at this
        have h2 : HasDerivAt (fun y => z - y) (-1) y := by
          simpa using (hasDerivAt_id y).const_sub z
        have h3 := (h1.comp y h2).const_mul (G z)
        simpa [mul_neg, neg_mul, mul_one] using h3)
    have h := key.2
    simpa [F, integral_neg] using h
  have hiter : ∀ j y, iteratedDeriv j (F 0) y = (-1) ^ j * F j y := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
      intro y
      rw [iteratedDeriv_succ]
      have : iteratedDeriv j (F 0) = fun y => (-1) ^ j * F j y := funext ih
      rw [this, ((hderiv j y).const_mul ((-1 : ℝ) ^ j)).deriv]
      ring
  have hF0 : (fun y => ∫ z, G z * κ (z - y)) = F 0 := by
    funext y; simp [F]
  rw [hF0]
  refine ⟨contDiff_of_differentiable_iteratedDeriv fun m _ => ?_, fun j y => hiter j y⟩
  have : iteratedDeriv m (F 0) = fun y => (-1) ^ m * F m y := funext (hiter m)
  rw [this]
  exact fun y => ((hderiv m y).differentiableAt).const_mul _


/-- Rescaled smooth kernel equal to `|t|^{-(p+1)}` for `|t| > 2c`. -/
def c03_aux_glkernel (p : ℝ) (η : ℝ → ℝ) (c t : ℝ) : ℝ :=
  c ^ (-(p + 1)) * c03_aux_faromega p (fun u => η (3 * u / 2)) (c⁻¹ * t)

theorem c03_aux_glkernel_props (p : ℝ) (hp : 0 < p) {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη1 : ∀ x ∈ Icc (-2 : ℝ) 2, η x = 1) (hη3 : ∀ x, 3 < |x| → η x = 0) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c03_aux_glkernel p η c) ∧
    (∀ j, ∃ D, ∀ t, |iteratedDeriv j (c03_aux_glkernel p η c) t| ≤ D * (1 + |t|) ^ (-(p + 1))) ∧
    (∀ t, 2 * c < |t| → c03_aux_glkernel p η c t = 1 / |t| ^ (p + 1)) := by
  set χ' : ℝ → ℝ := fun u => η (3 * u / 2)
  have hχ' : ContDiff ℝ (⊤ : ℕ∞) χ' := hη.comp (by fun_prop)
  have hχ'1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ' t = 1 := fun t ht =>
    hη1 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hχ'2 : ∀ t, 2 < |t| → χ' t = 0 := fun t ht => hη3 _ (by
    rw [show 3 * t / 2 = (3 / 2) * t by ring, abs_mul]; norm_num; linarith)
  have hω := c03_aux_faromega_smooth p hχ' hχ'1
  refine ⟨contDiff_const.mul (hω.comp (contDiff_const.mul contDiff_id)), fun j => ?_, fun t ht => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := c03_aux_faromega_decay p hp hχ' hχ'1 hχ'2 j
    refine ⟨c ^ (-(p + 1)) * c⁻¹ ^ j * C, fun t => ?_⟩
    have e : iteratedDeriv j (c03_aux_glkernel p η c) t =
        c ^ (-(p + 1)) * (c⁻¹ ^ j * iteratedDeriv j (c03_aux_faromega p χ') (c⁻¹ * t)) := by
      unfold c03_aux_glkernel
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul
        (hω.of_le (by exact_mod_cast le_top))]
    rw [e, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc0 _), abs_pow,
      abs_of_pos (inv_pos.2 hc0)]
    have h1 := hC (c⁻¹ * t)
    rw [Real.norm_eq_abs] at h1
    have h2 : (1 + |c⁻¹ * t|) ^ (-(p + 1)) ≤ (1 + |t|) ^ (-(p + 1)) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      rw [abs_mul, abs_of_pos (inv_pos.2 hc0)]
      have : |t| ≤ c⁻¹ * |t| := le_mul_of_one_le_left (abs_nonneg _) (one_le_inv_iff₀.2 ⟨hc0, hc1⟩)
      linarith
    calc c ^ (-(p + 1)) * (c⁻¹ ^ j * |iteratedDeriv j (c03_aux_faromega p χ') (c⁻¹ * t)|)
        ≤ c ^ (-(p + 1)) * (c⁻¹ ^ j * (C * (1 + |t|) ^ (-(p + 1)))) := by
          gcongr; exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)
      _ = c ^ (-(p + 1)) * c⁻¹ ^ j * C * (1 + |t|) ^ (-(p + 1)) := by ring
  · unfold c03_aux_glkernel c03_aux_faromega
    have hct : 2 < |c⁻¹ * t| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hc0), ← div_eq_inv_mul, lt_div_iff₀ hc0]; linarith
    have hz : (fun u => η (3 * u / 2)) (c⁻¹ * t) = 0 := hχ'2 _ hct
    rw [hz, abs_mul, abs_of_pos (inv_pos.2 hc0),
      Real.mul_rpow (inv_pos.2 hc0).le (abs_nonneg _), Real.inv_rpow hc0.le,
      Real.rpow_neg hc0.le]
    have h1 : 0 < c ^ (p + 1) := Real.rpow_pos_of_pos hc0 _
    have h2 : 0 < |t| ^ (p + 1) := Real.rpow_pos_of_pos (by linarith [mul_pos zero_lt_two hc0]) _
    field_simp
    ring



theorem c03_aux_T_eq (p : ℝ) {η g : ℝ → ℝ} (hη1 : ∀ x ∈ Icc (-2 : ℝ) 2, η x = 1)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hp : 0 < p) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη3 : ∀ x, 3 < |x| → η x = 0) {y : ℝ} (hy : |y| < 2 - 2 * c) :
    c03_gain_localization_T p η g y =
      -(c03_cp p) * ∫ z, ((1 - η z) * g z) * c03_aux_glkernel p η c (z - y) := by
  unfold c03_gain_localization_T
  congr 2; funext z
  by_cases hz : |z| ≤ 2
  · rw [hη1 z (abs_le.1 hz)]; simp
  · push Not at hz
    have hzy : 2 * c < |z - y| := by
      have := abs_sub_abs_le_abs_sub z y; linarith
    rw [(c03_aux_glkernel_props p hp hη hη1 hη3 hc0 hc1).2.2 _ hzy, add_comm 1 p]
    ring

theorem c03_aux_T_smooth (p : ℝ) (hp : 0 < p) {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη1 : ∀ x ∈ Icc (-2 : ℝ) 2, η x = 1) (hη3 : ∀ x, 3 < |x| → η x = 0)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃ Dk : ℕ → ℝ, (∀ j, 0 ≤ Dk j) ∧ ∀ g : ℝ → ℝ, Continuous g → ∀ M : ℝ, (∀ x, |g x| ≤ M) →
      ∃ F : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      (∀ y, |y| < 2 - 2 * c → c03_gain_localization_T p η g y = F y) ∧
      ∀ j y, |iteratedDeriv j F y| ≤ Dk j * |c03_cp p| * M := by
  obtain ⟨hκ, hD, -⟩ := c03_aux_glkernel_props p hp hη hη1 hη3 hc0 hc1
  choose D hDb using hD
  set I0 := ∫ t : ℝ, (1 + |t|) ^ (-(p + 1))
  have hint0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(p + 1))) volume :=
    integrable_one_add_norm (by simp; linarith)
  have hI0 : 0 ≤ I0 := integral_nonneg fun t => by positivity
  refine ⟨fun j => |D j| * I0, fun j => by positivity, fun g hg M hM => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set G : ℝ → ℝ := fun z => (1 - η z) * g z
  have hGm : Measurable G := (continuous_const.sub hη.continuous).measurable.mul hg.measurable
  have hGM : ∀ z, |G z| ≤ M := fun z => by
    simp only [G, abs_mul]
    have : |1 - η z| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hη01 z]
    calc |1 - η z| * |g z| ≤ 1 * M := mul_le_mul this (hM z) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  obtain ⟨hcs, hcd⟩ := c03_aux_conv_smooth hκ (by linarith : 1 < p + 1) D hDb hGm hGM
  refine ⟨fun y => -(c03_cp p) * ∫ z, G z * c03_aux_glkernel p η c (z - y),
    contDiff_const.mul hcs, fun y hy => c03_aux_T_eq p hη1 hc0 hc1 hp hη hη3 hy, fun j y => ?_⟩
  rw [iteratedDeriv_const_mul_field, hcd j y, abs_mul, abs_mul, abs_neg, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  have hb : |∫ z, G z * iteratedDeriv j (c03_aux_glkernel p η c) (z - y)| ≤ M * (|D j| * I0) := by
    have hsh : Integrable (fun z : ℝ => (1 + |z - y|) ^ (-(p + 1))) := by
      simpa [Real.norm_eq_abs] using hint0.comp_sub_right y
    have h1 : ∀ z, ‖G z * iteratedDeriv j (c03_aux_glkernel p η c) (z - y)‖ ≤
        M * |D j| * (1 + |z - y|) ^ (-(p + 1)) := fun z => by
      rw [Real.norm_eq_abs, abs_mul, mul_assoc]
      refine mul_le_mul (hGM z) ((hDb j _).trans ?_) (abs_nonneg _) hM0
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h2 := norm_integral_le_of_norm_le (hsh.const_mul (M * |D j|)) (Eventually.of_forall h1)
    rw [Real.norm_eq_abs, integral_const_mul] at h2
    have h3 : ∫ z : ℝ, (1 + |z - y|) ^ (-(p + 1)) = I0 :=
      integral_sub_right_eq_self (fun t : ℝ => (1 + |t|) ^ (-(p + 1))) y
    rw [h3] at h2
    linarith
  calc |c03_cp p| * |∫ z, G z * iteratedDeriv j (c03_aux_glkernel p η c) (z - y)|
      ≤ |c03_cp p| * (M * (|D j| * I0)) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = |D j| * I0 * |c03_cp p| * M := by ring


/-- A cutoff `η` supported in `[-3,3]` times `g ∈ C^s([-4,4])` lies in the global `C^s(ℝ)`. -/
theorem c03_aux_cutoff_holder_univ (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη3 : ∀ x, 3 < |x| → η x = 0) {g : ℝ → ℝ}
    (hgk : ContDiff ℝ ⌊s⌋₊ g) (hg4 : g ∈ c03_holder s (Icc (-4) 4)) :
    (fun x => η x * g x) ∈ c03_holder s univ := by
  set k := ⌊s⌋₊
  set v : ℝ → ℝ := fun x => η x * g x
  set J := Icc (-4 : ℝ) 4
  have hUJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc (by norm_num)
  have hvk : ContDiff ℝ k v := (hη.of_le (by exact_mod_cast le_top)).mul hgk
  -- `v ∈ C^s(J)` via complexification and the product estimate
  have hηJ : (fun x => ((η x : ℝ) : ℂ)) ∈ c03_holder s J :=
    c03_aux_holder_smooth s _ ((Complex.ofRealCLM.contDiff.comp hη).of_le
      (by exact_mod_cast le_top)) (-4) 4
  obtain ⟨hgJ, -, -⟩ := c03_aux_holder_clm_norm (by norm_num : (-4 : ℝ) < 4) Complex.ofRealCLM
    (by rw [Complex.ofRealCLM_norm]) hg4
  obtain ⟨Cp, -, hCp⟩ := c03_holder_product_tame s hs hsN
  obtain ⟨hP, -⟩ := hCp (-4) 4 (by norm_num) _ _ hηJ hgJ
  obtain ⟨hvJ, -, -⟩ := c03_aux_holder_clm_norm (by norm_num : (-4 : ℝ) < 4) Complex.reCLM
    (by rw [Complex.reCLM_norm]) hP
  have hre : (fun x => Complex.reCLM (((fun x => ((η x : ℝ) : ℂ)) *
      fun x => Complex.ofRealCLM (g x)) x)) = v := by
    funext x; simp [v]
  rw [hre] at hvJ
  obtain ⟨hb, CH, hCH⟩ := c03_aux_holder_bounds s J v hvJ
  have heqJ : ∀ i ≤ k, ∀ x ∈ J, iteratedDerivWithin i v J x = iteratedDeriv i v x :=
    fun i hi x hx => iteratedDerivWithin_eq_iteratedDeriv hUJ
      ((hvk.of_le (by exact_mod_cast hi)).contDiffAt) hx
  have hzero : ∀ i, ∀ x, 3 < |x| → iteratedDeriv i v x = 0 := by
    intro i x hx
    have hev : v =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs : IsOpen {u : ℝ | 3 < |u|}).mem_nhds
        (show x ∈ {u : ℝ | 3 < |u|} from hx)] with u hu
      simp only [v, hη3 u hu, zero_mul]
    rw [c03_aux_iteratedDeriv_congr hev]
    simp
  choose A hA using hb
  set A' : ℕ → ℝ := fun i => if h : i ≤ k then max (A i h) 0 else 0
  have hAb : ∀ i ≤ k, ∀ x, ‖iteratedDeriv i v x‖ ≤ A' i := by
    intro i hi x
    simp only [A', dif_pos hi]
    by_cases hx : x ∈ J
    · rw [← heqJ i hi x hx]; exact (hA i hi x hx).trans (le_max_left _ _)
    · have : 3 < |x| := by
        simp only [J, mem_Icc, not_and_or, not_le] at hx
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hzero i x this, norm_zero]; exact le_max_right _ _
  have hA'0 : ∀ i, 0 ≤ A' i := fun i => by
    simp only [A']; split_ifs <;> simp
  have hB : HolderOnWith (CH + Real.toNNReal (2 * A' k)) (Real.toNNReal (s - ⌊s⌋₊))
      (iteratedDerivWithin ⌊s⌋₊ v univ) univ := by
    refine c03_aux_holderOnWith_of_dist fun x _ y _ => ?_
    rw [iteratedDerivWithin_univ]
    set θr := ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ)
    have hθr0 : 0 ≤ θr := NNReal.coe_nonneg _
    have hdθ : 0 ≤ dist x y ^ θr := Real.rpow_nonneg dist_nonneg _
    push_cast [Real.coe_toNNReal _ (by linarith [hA'0 k] : (0:ℝ) ≤ 2 * A' k)]
    by_cases hxy : x ∈ J ∧ y ∈ J
    · rw [← heqJ k le_rfl x hxy.1, ← heqJ k le_rfl y hxy.2]
      have := hCH.dist_le hxy.1 hxy.2
      nlinarith [hA'0 k]
    · -- one point is far out; the derivative vanishes there and the other is either far or
      -- at distance `≥ 1`
      have key : ∀ x y : ℝ, y ∉ J → dist (iteratedDeriv k v x) (iteratedDeriv k v y) ≤
          2 * A' k * dist x y ^ θr := by
        intro x y hy
        have hy3 : 3 < |y| := by
          simp only [J, mem_Icc, not_and_or, not_le] at hy
          rcases hy with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have hy4 : 4 < |y| := by
          simp only [J, mem_Icc, not_and_or, not_le] at hy
          rcases hy with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        rw [hzero k y hy3, dist_zero_right]
        by_cases hx3 : 3 < |x|
        · rw [hzero k x hx3, norm_zero]
          exact mul_nonneg (mul_nonneg zero_le_two (hA'0 k)) (Real.rpow_nonneg dist_nonneg _)
        · push Not at hx3
          have hd : 1 ≤ dist x y := by
            rw [Real.dist_eq]
            have := abs_sub_abs_le_abs_sub y x
            rw [abs_sub_comm] at this; linarith
          have h1 : 1 ≤ dist x y ^ θr := Real.one_le_rpow hd hθr0
          have := hAb k le_rfl x
          nlinarith [hA'0 k]
      rw [not_and_or] at hxy
      rcases hxy with hx | hy
      · rw [dist_comm, dist_comm x y]
        have := key y x hx
        have h0 : (0 : ℝ) ≤ CH * dist y x ^ θr := by positivity
        linarith
      · have := key x y hy
        have h0 : (0 : ℝ) ≤ CH * dist x y ^ θr := by positivity
        linarith
  exact (c03_aux_normR_le s univ v hvk.contDiffOn A' (fun i _ => hA'0 i)
    (fun i hi x _ => by rw [iteratedDerivWithin_univ]; exact hAb i hi x) _ hB).1


-- Encoding: "all `y` derivatives of the displayed integral converge absolutely on
-- `[-1,1]`" is encoded by the integrable majorants `(1-η(z)) g(z) |z-y|^{-1-p-j}`; the constant
-- `C(p,j,η)` is quantified before `g`, and `‖g‖_∞` is any bound `M` of `|g|`.
/-- Blueprint: lem:c03_gain_localization.  For `v = ηg`: `v` is compactly supported, Lipschitz,
in `C^s(ℝ)`, and on `[-1,1]`, `|D|^p v = |D|^p g - T` with `T` smooth on `(-2,2)`,
`sup_{|y|≤1} |T^{(j)}| ≤ C(p,j,η)‖g‖_∞`; in particular `|D|^p v ∈ C^s([-1,1])`. -/
theorem c03_gain_localization (p s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) (hη1 : ∀ x ∈ Icc (-2 : ℝ) 2, η x = 1)
    (hη3 : ∀ x, 3 < |x| → η x = 0) :
    (∀ j : ℕ, ∃ C, 0 < C ∧ ∀ g : ℝ → ℝ, ∀ M : ℝ, (∀ x, |g x| ≤ M) → LocallyLipschitz g →
      ∀ y ∈ Icc (-1 : ℝ) 1, |iteratedDeriv j (c03_gain_localization_T p η g) y| ≤ C * M) ∧
    ∀ g : ℝ → ℝ, (∃ M, ∀ x, |g x| ≤ M) → LocallyLipschitz g → g ∈ c03_holder_loc s univ →
      (∀ y, Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1))) →
      fracD p g ∈ c03_holder_loc s univ →
      HasCompactSupport (fun x => η x * g x) ∧
      (∃ L, LipschitzWith L (fun x => η x * g x)) ∧
      (fun x => η x * g x) ∈ c03_holder s univ ∧
      (∀ y ∈ Icc (-1 : ℝ) 1, ∀ j : ℕ,
        Integrable (fun z => (1 - η z) * g z / |z - y| ^ (1 + p + j))) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c03_gain_localization_T p η g) (Ioo (-2) 2) ∧
      (∀ y ∈ Icc (-1 : ℝ) 1,
        Integrable (fun z => (η y * g y - η z * g z) / |y - z| ^ (p + 1)) ∧
        fracD p (fun x => η x * g x) y = fracD p g y - c03_gain_localization_T p η g y) ∧
      fracD p (fun x => η x * g x) ∈ c03_holder s (Icc (-1) 1) := by
  have hcp : c03_cp p = calpha p := (c03_frac_kernel_formula p hp hp1).2.2.2.2.1
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨Dk, hDk0, hT⟩ := c03_aux_T_smooth p hp hη hη1 hη3 hη01 hq (by norm_num)
  have hT14 : ∀ y : ℝ, |y| < 3 / 2 → |y| < 2 - 2 * (1 / 4 : ℝ) := fun y hy => by linarith
  have hnbhd : ∀ y ∈ Icc (-1 : ℝ) 1, {u : ℝ | |u| < 3 / 2} ∈ 𝓝 y := fun y hy =>
    (isOpen_lt continuous_abs continuous_const).mem_nhds
      (show |y| < 3 / 2 from (abs_le.2 ⟨hy.1, hy.2⟩).trans_lt (by norm_num))
  refine ⟨fun j => ⟨Dk j * |c03_cp p| + 1,
    add_pos_of_nonneg_of_pos (mul_nonneg (hDk0 j) (abs_nonneg _)) one_pos, fun g M hM hg y hy => ?_⟩,
    fun g hgb hg hgs hint hDg => ?_⟩
  · obtain ⟨F, hF, hTF, hFb⟩ := hT g hg.continuous M hM
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hev : c03_gain_localization_T p η g =ᶠ[𝓝 y] F := by
      filter_upwards [hnbhd y hy] with u hu using hTF u (hT14 u hu)
    rw [c03_aux_iteratedDeriv_congr hev]
    refine (hFb j y).trans ?_
    nlinarith
  obtain ⟨M, hM⟩ := hgb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hgc : Continuous g := hg.continuous
  set v : ℝ → ℝ := fun x => η x * g x with hv
  have hη3' : ∀ x, x ∉ Icc (-3 : ℝ) 3 → η x = 0 := fun x hx => hη3 x (by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith)
  -- (b1) compact support
  have hvc : HasCompactSupport v :=
    HasCompactSupport.intro (isCompact_Icc (a := -3) (b := 3)) fun x hx => by
      simp [v, hη3' x hx]
  -- (b2) Lipschitz
  have hvL : ∃ L, LipschitzWith L v := by
    have hηc : HasCompactSupport η := HasCompactSupport.intro (isCompact_Icc (a := -3) (b := 3))
      fun x hx => hη3' x hx
    obtain ⟨Lη, hLη⟩ := (hη.continuous_deriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      hηc.deriv
    have hηL : ∀ x y, |η x - η y| ≤ max Lη 0 * |x - y| := by
      intro x y
      have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := η) (f' := deriv η) (C := max Lη 0)
        (fun u _ => ((hη.differentiable (by simp)) u).hasDerivAt.hasDerivWithinAt)
        (fun u _ => (hLη u).trans (le_max_left _ _)) (mem_univ y) (mem_univ x)
      simpa [Real.norm_eq_abs] using this
    obtain ⟨L, hL⟩ := (hg.locallyLipschitzOn (s := Icc (-3) 3)).exists_lipschitzOnWith_of_compact
      isCompact_Icc
    set C := (L : ℝ) + M * max Lη 0
    have hC0 : 0 ≤ C := by positivity
    have hηb : ∀ x, |η x| ≤ 1 := fun x => by rw [abs_le]; constructor <;> linarith [hη01 x]
    have key : ∀ x y, y ∈ Icc (-3 : ℝ) 3 → |v x - v y| ≤ C * |x - y| := by
      intro x y hy
      by_cases hx : x ∈ Icc (-3 : ℝ) 3
      · have h1 : |g x - g y| ≤ L * |x - y| := by
          have := hL.dist_le_mul x hx y hy; rwa [Real.dist_eq, Real.dist_eq] at this
        have e : v x - v y = η x * (g x - g y) + g y * (η x - η y) := by simp only [v]; ring
        rw [e]
        calc |η x * (g x - g y) + g y * (η x - η y)| ≤ |η x| * |g x - g y| + |g y| * |η x - η y| := by
              refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
          _ ≤ 1 * (L * |x - y|) + M * (max Lη 0 * |x - y|) := by
              gcongr
              · exact hηb x
              · exact hM y
              · exact hηL x y
          _ = C * |x - y| := by simp only [C]; ring
      · have hx0 : η x = 0 := hη3' x hx
        have e : v x - v y = g y * (η x - η y) := by simp only [v, hx0]; ring
        rw [e, abs_mul]
        calc |g y| * |η x - η y| ≤ M * (max Lη 0 * |x - y|) :=
              mul_le_mul (hM y) (hηL x y) (abs_nonneg _) hM0
          _ ≤ C * |x - y| := by
              have : (0:ℝ) ≤ L * |x - y| := by positivity
              simp only [C]; nlinarith
    refine ⟨Real.toNNReal C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC0]
    by_cases hy : y ∈ Icc (-3 : ℝ) 3
    · exact key x y hy
    · by_cases hx : x ∈ Icc (-3 : ℝ) 3
      · rw [abs_sub_comm, abs_sub_comm x]; exact key y x hx
      · simp only [v, hη3' x hx, hη3' y hy, zero_mul, sub_self, abs_zero]; positivity
  -- (b3) global Hölder
  have hgk : ContDiff ℝ ⌊s⌋₊ g := contDiffOn_univ.1 hgs.1
  have hvs : v ∈ c03_holder s univ :=
    c03_aux_cutoff_holder_univ s hs hsN hη hη3 hgk (hgs.2 _ _ (subset_univ _))
  -- (b4) integrability of the tail
  have htail : ∀ y ∈ Icc (-1 : ℝ) 1, ∀ j : ℕ,
      Integrable (fun z => (1 - η z) * g z / |z - y| ^ (1 + p + j)) := by
    intro y hy j
    have hint0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(1 + p))) volume :=
      integrable_one_add_norm (by simp; linarith)
    refine ((hint0.const_mul (M * 3 ^ (1 + p)))).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((continuous_const.sub hη.continuous).measurable.mul hgc.measurable).div
        ((continuous_abs.measurable.comp (measurable_id.sub_const y)).pow_const _)
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs]
      by_cases hz : |z| ≤ 2
      · rw [hη1 z (abs_le.1 hz)]
        simp only [sub_self, zero_mul, zero_div, abs_zero]
        positivity
      · push Not at hz
        have hzy1 : 1 ≤ |z - y| := by
          have := abs_sub_abs_le_abs_sub z y
          have : |y| ≤ 1 := abs_le.2 ⟨hy.1, hy.2⟩
          linarith
        have hzy : (1 + |z|) / 3 ≤ |z - y| := by
          have := abs_sub_abs_le_abs_sub z y
          have : |y| ≤ 1 := abs_le.2 ⟨hy.1, hy.2⟩
          linarith
        have hpos : 0 < |z - y| := by linarith
        have h1 : |z - y| ^ (1 + p) ≤ |z - y| ^ (1 + p + j) :=
          Real.rpow_le_rpow_of_exponent_le hzy1 (le_add_of_nonneg_right (Nat.cast_nonneg j))
        have h2 : ((1 + |z|) / 3) ^ (1 + p) ≤ |z - y| ^ (1 + p) :=
          Real.rpow_le_rpow (by positivity) hzy (by linarith)
        have h3 : ((1 + |z|) / 3) ^ (1 + p) = (1 + |z|) ^ (1 + p) / 3 ^ (1 + p) :=
          Real.div_rpow (by positivity) (by norm_num) _
        have hnum : |(1 - η z) * g z| ≤ M := by
          rw [abs_mul]
          have : |1 - η z| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hη01 z]
          calc |1 - η z| * |g z| ≤ 1 * M := mul_le_mul this (hM z) (abs_nonneg _) zero_le_one
            _ = M := one_mul M
        have hden : 0 < |z - y| ^ (1 + p + j) := Real.rpow_pos_of_pos hpos _
        rw [abs_div, abs_of_pos hden, Real.rpow_neg (by positivity), div_le_iff₀ hden]
        have h4 : (1 + |z|) ^ (1 + p) ≤ 3 ^ (1 + p) * |z - y| ^ (1 + p + j) := by
          have h5 : 0 < (3 : ℝ) ^ (1 + p) := by positivity
          rw [h3, div_le_iff₀ h5] at h2
          nlinarith
        have h6 : 0 < (1 + |z|) ^ (1 + p) := by positivity
        calc |(1 - η z) * g z| ≤ M := hnum
          _ = M * 3 ^ (1 + p) * ((1 + |z|) ^ (1 + p))⁻¹ * ((1 + |z|) ^ (1 + p) / 3 ^ (1 + p)) := by
              field_simp
          _ ≤ M * 3 ^ (1 + p) * ((1 + |z|) ^ (1 + p))⁻¹ * |z - y| ^ (1 + p + j) := by
              gcongr
              rw [div_le_iff₀ (by positivity)]; linarith
  -- (b5) smoothness of `T` on `(-2,2)`
  have hTs : ContDiffOn ℝ (⊤ : ℕ∞) (c03_gain_localization_T p η g) (Ioo (-2) 2) := by
    intro y0 hy0
    have hy0' : |y0| < 2 := abs_lt.2 ⟨hy0.1, hy0.2⟩
    set c := (2 - |y0|) / 4
    have hc0 : 0 < c := by simp only [c]; linarith
    have hc1 : c ≤ 1 := by simp only [c]; linarith [abs_nonneg y0]
    obtain ⟨Dk', -, hT'⟩ := c03_aux_T_smooth p hp hη hη1 hη3 hη01 hc0 hc1
    obtain ⟨F, hF, hTF, -⟩ := hT' g hgc M hM
    have hlt : |y0| < 2 - 2 * c := by simp only [c]; linarith
    have hev : c03_gain_localization_T p η g =ᶠ[𝓝 y0] F := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const : IsOpen {u : ℝ | |u| < 2 - 2 * c}).mem_nhds
        (show y0 ∈ {u : ℝ | |u| < 2 - 2 * c} from hlt)] with u hu using hTF u hu
    exact (hF.contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt
  -- (b6) the identity
  have hid : ∀ y ∈ Icc (-1 : ℝ) 1,
      Integrable (fun z => (η y * g y - η z * g z) / |y - z| ^ (p + 1)) ∧
      fracD p v y = fracD p g y - c03_gain_localization_T p η g y := by
    intro y hy
    have hηy : η y = 1 := hη1 y ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hB := htail y hy 0
    simp only [Nat.cast_zero, add_zero] at hB
    have hB' : Integrable (fun z => (1 - η z) * g z / |y - z| ^ (p + 1)) := by
      refine hB.congr (Eventually.of_forall fun z => ?_)
      simp only [abs_sub_comm z y, add_comm 1 p]
    have hsplit : (fun z => (η y * g y - η z * g z) / |y - z| ^ (p + 1)) =
        fun z => (g y - g z) / |y - z| ^ (p + 1) + (1 - η z) * g z / |y - z| ^ (p + 1) := by
      funext z; rw [hηy]; ring
    refine ⟨by rw [hsplit]; exact (hint y).add hB', ?_⟩
    unfold fracD c03_gain_localization_T
    simp only [v]
    rw [hsplit, integral_add (hint y) hB', hcp]
    have e : (∫ z, (1 - η z) * g z / |z - y| ^ (1 + p)) =
        ∫ z, (1 - η z) * g z / |y - z| ^ (p + 1) := by
      congr 1; funext z; simp only [abs_sub_comm z y, add_comm 1 p]
    rw [e]; ring
  -- (b7) `|D|^p v ∈ C^s([-1,1])`
  have hDv : fracD p v ∈ c03_holder s (Icc (-1) 1) := by
    obtain ⟨F, hF, hTF, -⟩ := hT g hgc M hM
    have hFI : F ∈ c03_holder s (Icc (-1) 1) :=
      c03_aux_holder_smooth s F (hF.of_le (by exact_mod_cast le_top)) (-1) 1
    obtain ⟨hnF, -, -⟩ := c03_aux_holder_clm_norm (by norm_num : (-1 : ℝ) < 1)
      (-ContinuousLinearMap.id ℝ ℝ) (by rw [norm_neg]; exact ContinuousLinearMap.norm_id_le) hFI
    have hsum := c03_aux_holder_add s (-1) 1 _ _ (hDg.2 (-1) 1 (subset_univ _)) hnF
    refine ((c03_aux_holder_congr (s := s) (I := Icc (-1) 1) (f := fracD p v)
      (g := fun x => fracD p g x + (-ContinuousLinearMap.id ℝ ℝ) (F x)) fun x hx => ?_).2.1).2 hsum
    rw [(hid x hx).2, hTF x (hT14 x ((abs_le.2 ⟨hx.1, hx.2⟩).trans_lt (by norm_num)))]
    simp [sub_eq_add_neg]
  exact ⟨hvc, hvL, hvs, htail, hTs, hid, hDv⟩

/-- Blueprint: lem:c03_gain_mollification.  The mollification
`w_δ(x) = (v * ρ_δ)(x) = ∫ v(x-y) δ⁻¹ ρ(y/δ) dy`. -/
def c03_gain_mollify (ρ v : ℝ → ℝ) (δ : ℝ) (x : ℝ) : ℝ :=
  ∫ y, v (x - y) * (δ⁻¹ * ρ (y / δ))

/-- Basic properties of `ρ_δ(y) = δ⁻¹ ρ(y/δ)`. -/
theorem c03_aux_moll_basic {ρ : ℝ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρsupp : tsupport ρ ⊆ Ioo (-1) 1) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => δ⁻¹ * ρ (y / δ)) ∧
    HasCompactSupport (fun y => δ⁻¹ * ρ (y / δ)) ∧
    (∀ y, 0 ≤ δ⁻¹ * ρ (y / δ)) ∧
    (∀ y, δ ≤ |y| → δ⁻¹ * ρ (y / δ) = 0) ∧
    Integrable (fun y => δ⁻¹ * ρ (y / δ)) ∧ ∫ y, δ⁻¹ * ρ (y / δ) = 1 := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => δ⁻¹ * ρ (y / δ)) :=
    contDiff_const.mul (hρ.comp (contDiff_id.div_const δ))
  have hzero : ∀ y, δ ≤ |y| → δ⁻¹ * ρ (y / δ) = 0 := by
    intro y hy
    have : ρ (y / δ) = 0 := by
      by_contra h
      have hmem := hρsupp (subset_tsupport ρ h)
      have : |y / δ| < 1 := abs_lt.2 ⟨hmem.1, hmem.2⟩
      rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at this
      linarith
    rw [this, mul_zero]
  have hcs : HasCompactSupport (fun y => δ⁻¹ * ρ (y / δ)) :=
    HasCompactSupport.intro (isCompact_Icc (a := -δ) (b := δ)) fun y hy => hzero y (by
      simp only [mem_Icc, not_and_or, not_le] at hy
      rcases hy with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  refine ⟨hsm, hcs, fun y => mul_nonneg (inv_nonneg.2 hδ.le) (hρ0 _), hzero,
    hsm.continuous.integrable_of_hasCompactSupport hcs, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_div, abs_of_pos hδ, smul_eq_mul, hρ1]
  field_simp


/-- Derivatives of `x ↦ ∫ g(x-y) m(y) dy` for `g ∈ C^k` with bounded derivatives. -/
theorem c03_aux_moll_deriv {g : ℝ → ℝ} {k : ℕ} (hg : ContDiff ℝ k g) (S : ℕ → ℝ)
    (hS : ∀ i ≤ k, ∀ x, |iteratedDeriv i g x| ≤ S i) {m : ℝ → ℝ} (hm : Integrable m) :
    ∀ i ≤ k, ∀ x, iteratedDeriv i (fun x => ∫ y, g (x - y) * m y) x =
      ∫ y, iteratedDeriv i g (x - y) * m y := by
  have hc : ∀ i ≤ k, Continuous (iteratedDeriv i g) := fun i hi =>
    hg.continuous_iteratedDeriv i (by exact_mod_cast hi)
  have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun y => iteratedDeriv i g (x - y) * m y) volume :=
    fun i hi x => ((hc i hi).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable
  have hint : ∀ i ≤ k, ∀ x, Integrable (fun y => iteratedDeriv i g (x - y) * m y) := fun i hi x =>
    (hm.norm.const_mul (S i)).mono' (hmeas i hi x) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hS i hi _) (abs_nonneg _))
  intro i
  induction i with
  | zero => intro _ x; simp
  | succ i ih =>
    intro hi x
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv i (fun x => ∫ y, g (x - y) * m y) =
        fun x => ∫ y, iteratedDeriv i g (x - y) * m y := funext (ih (by omega))
    rw [hfun]
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun x y => iteratedDeriv i g (x - y) * m y)
      (F' := fun x y => iteratedDeriv (i + 1) g (x - y) * m y)
      (bound := fun y => S (i + 1) * ‖m y‖) (x₀ := x) (s := univ) univ_mem
      (Eventually.of_forall fun x => hmeas i (by omega) x) (hint i (by omega) x)
      (hmeas (i + 1) hi x)
      (Eventually.of_forall fun y x _ => by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hS (i + 1) hi _) (abs_nonneg _))
      (hm.norm.const_mul _)
      (Eventually.of_forall fun y x _ => by
        have hd : HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g (x - y)) (x - y) := by
          have := ((hg.differentiable_iteratedDeriv i (by exact_mod_cast hi)) (x - y)).hasDerivAt
          rwa [← iteratedDeriv_succ] at this
        have h2 : HasDerivAt (fun x => x - y) 1 x := (hasDerivAt_id x).sub_const y
        have := (hd.comp x h2).mul_const (m y)
        simpa using this)
    exact key.2.deriv

/-- Averaging against a probability density does not increase the global `C^s` norm. -/
theorem c03_aux_moll_norm (s : ℝ) {v : ℝ → ℝ} (hv : v ∈ c03_holder s univ) {m : ℝ → ℝ}
    (hm : Integrable m) (hm0 : ∀ y, 0 ≤ m y) (hm1 : ∫ y, m y = 1)
    (hw : ContDiff ℝ ⌊s⌋₊ (fun x => ∫ y, v (x - y) * m y)) :
    (fun x => ∫ y, v (x - y) * m y) ∈ c03_holder s univ ∧
      c03_holder_normR s univ (fun x => ∫ y, v (x - y) * m y) ≤ c03_holder_normR s univ v := by
  set k := ⌊s⌋₊
  have hvk : ContDiff ℝ k v := contDiffOn_univ.1 hv.1
  set A : ℕ → ℝ := fun i => (c03_aux_supD i univ v).toReal
  have hA : ∀ i ≤ k, ∀ x, |iteratedDeriv i v x| ≤ A i := fun i hi x => by
    have := c03_aux_le_supD hv hi (mem_univ x)
    rwa [iteratedDerivWithin_univ, Real.norm_eq_abs] at this
  have hder := c03_aux_moll_deriv hvk A hA hm
  have hmint : ∀ i ≤ k, ∀ x, Integrable (fun y => iteratedDeriv i v (x - y) * m y) := fun i hi x =>
    (hm.const_mul (A i)).mono' (((hvk.continuous_iteratedDeriv i (by exact_mod_cast hi)).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hm.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm0 y)]
        exact mul_le_mul_of_nonneg_right (hA i hi _) (hm0 y))
  have hB := c03_aux_semi_holder hv
  rw [iteratedDerivWithin_univ] at hB
  set B := (c03_aux_semi s univ v).toNNReal
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s univ _ hw.contDiffOn A (fun _ _ => ENNReal.toReal_nonneg)
    (fun i hi x _ => by
      rw [iteratedDerivWithin_univ, hder i hi x, Real.norm_eq_abs]
      calc |∫ y, iteratedDeriv i v (x - y) * m y| ≤ ∫ y, A i * m y := by
            refine (abs_integral_le_integral_abs).trans (integral_mono (hmint i hi x).abs
              (hm.const_mul _) fun y => ?_)
            simp only [abs_mul, abs_of_nonneg (hm0 y)]
            exact mul_le_mul_of_nonneg_right (hA i hi _) (hm0 y)
        _ = A i := by rw [integral_const_mul, hm1, mul_one]) B
    (by
      rw [iteratedDerivWithin_univ]
      refine c03_aux_holderOnWith_of_dist fun x _ x' _ => ?_
      rw [hder k le_rfl x, hder k le_rfl x', dist_eq_norm, ← integral_sub (hmint k le_rfl x)
        (hmint k le_rfl x'), Real.norm_eq_abs]
      have hd : ∀ y, |iteratedDeriv k v (x - y) * m y - iteratedDeriv k v (x' - y) * m y| ≤
          (B : ℝ) * dist x x' ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) * m y := fun y => by
        rw [← sub_mul, abs_mul, abs_of_nonneg (hm0 y)]
        refine mul_le_mul_of_nonneg_right ?_ (hm0 y)
        have := hB.dist_le (mem_univ (x - y)) (mem_univ (x' - y))
        rw [Real.dist_eq] at this
        rwa [show dist (x - y) (x' - y) = dist x x' by simp [Real.dist_eq]] at this
      calc |∫ y, (iteratedDeriv k v (x - y) * m y - iteratedDeriv k v (x' - y) * m y)|
          ≤ ∫ y, (B : ℝ) * dist x x' ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) * m y :=
            (abs_integral_le_integral_abs).trans (integral_mono
              ((hmint k le_rfl x).sub (hmint k le_rfl x')).abs (hm.const_mul _) hd)
        _ = (B : ℝ) * dist x x' ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) := by
            rw [integral_const_mul, hm1, mul_one])
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hv, ENNReal.coe_toNNReal_eq_toReal]


open scoped Pointwise in
theorem c03_aux_vadd_Icc (y c d : ℝ) : (-y) +ᵥ Icc c d = Icc (c - y) (d - y) := by
  ext u
  simp only [Set.mem_vadd_set, vadd_eq_add, mem_Icc]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; exact ⟨u + y, ⟨by linarith, by linarith⟩, by ring⟩

open scoped Pointwise in
/-- Translation and restriction for a function that is only `C^s` on `[a,b]`. -/
theorem c03_aux_holder_shift_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℝ} {g : ℝ → E} {a b c d y : ℝ} (hab : a < b) (hcd : c < d)
    (hsub : Icc (c - y) (d - y) ⊆ Icc a b) (hg : g ∈ c03_holder s (Icc a b)) :
    (fun x => g (x - y)) ∈ c03_holder s (Icc c d) ∧
      c03_holder_normR s (Icc c d) (fun x => g (x - y)) ≤ c03_holder_normR s (Icc a b) g := by
  set k := ⌊s⌋₊
  have hU1 : UniqueDiffOn ℝ (Icc (c - y) (d - y)) := uniqueDiffOn_Icc (by linarith)
  have hU2 : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ x ∈ Icc c d, iteratedDerivWithin i (fun x => g (x - y)) (Icc c d) x =
      iteratedDerivWithin i g (Icc a b) (x - y) := by
    intro i hi x hx
    rw [iteratedDerivWithin_comp_sub_const, c03_aux_vadd_Icc]
    have hx' : x - y ∈ Icc (c - y) (d - y) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    show iteratedDerivWithin i g (Icc (c - y) (d - y)) (x - y) = _
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_subset hsub hU1 hU2 (hg.1.of_le (by exact_mod_cast hi)) hx']
  have hmaps : MapsTo (fun x => x - y) (Icc c d) (Icc a b) := fun x hx =>
    hsub ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcd' : ContDiffOn ℝ k (fun x => g (x - y)) (Icc c d) :=
    hg.1.comp (contDiffOn_id.sub contDiffOn_const) hmaps
  have hH := c03_aux_semi_holder hg
  obtain ⟨hm, hle⟩ := c03_aux_normR_le s (Icc c d) _ hcd'
    (fun i => (c03_aux_supD i (Icc a b) g).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i hi x hx => by rw [heq i hi x hx]; exact c03_aux_le_supD hg hi (hmaps hx))
    (c03_aux_semi s (Icc a b) g).toNNReal
    (c03_aux_holderOnWith_of_dist fun x hx x' hx' => by
      rw [heq k le_rfl x hx, heq k le_rfl x' hx']
      have := hH.dist_le (hmaps hx) (hmaps hx')
      rwa [show dist (x - y) (x' - y) = dist x x' by simp [Real.dist_eq]] at this)
  refine ⟨hm, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hg, ENNReal.coe_toNNReal_eq_toReal]


/-- Kernel quotient bound for a Lipschitz bounded function. -/
theorem c03_aux_quot_bound (p : ℝ) (hp : 0 < p) {u : ℝ → ℝ} {Λ U : ℝ} (hΛ : 0 ≤ Λ) (hU : 0 ≤ U)
    (hLu : ∀ a b, |u a - u b| ≤ Λ * |a - b|) (hUu : ∀ a, |u a| ≤ U) (a b x z : ℝ)
    (hab : a - b = x - z) :
    |u a - u b| / |x - z| ^ (p + 1) ≤ c03_aux_psi p Λ (2 * U) (z - x) := by
  rw [abs_sub_comm x z]
  refine c03_aux_psi_bound p hp hΛ (by linarith) (z - x) (u a - u b) (fun _ => ?_) ?_
  · rw [abs_sub_comm z x, ← hab]; exact hLu a b
  · calc |u a - u b| ≤ |u a| + |u b| := abs_sub _ _
      _ ≤ 2 * U := by linarith [hUu a, hUu b]

/-- Integrability of the singular quotient of a Lipschitz bounded continuous function. -/
theorem c03_aux_quot_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) {u : ℝ → ℝ}
    (hu : Continuous u) {Λ U : ℝ} (hΛ : 0 ≤ Λ) (hU : 0 ≤ U)
    (hLu : ∀ a b, |u a - u b| ≤ Λ * |a - b|) (hUu : ∀ a, |u a| ≤ U) (x : ℝ) :
    Integrable (fun z => (u x - u z) / |x - z| ^ (p + 1)) := by
  have hψ : Integrable (fun z => c03_aux_psi p Λ (2 * U) (z - x)) :=
    (c03_aux_psi_integrable p Λ (2 * U) hp hp1).comp_sub_right x
  refine hψ.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((measurable_const.sub hu.measurable).div
      ((continuous_abs.measurable.comp (measurable_const.sub measurable_id)).pow_const _)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact c03_aux_quot_bound p hp hΛ hU hLu hUu x z x z rfl


/-- `|D|^p` commutes with averaging: `|D|^p (v ⋆ m) = (|D|^p v) ⋆ m`, absolutely convergent. -/
theorem c03_aux_frac_conv (p : ℝ) (hp : 0 < p) (hp1 : p < 1) {v : ℝ → ℝ} (hvc : Continuous v)
    {L V : ℝ} (hL0 : 0 ≤ L) (hV0 : 0 ≤ V) (hLv : ∀ a b, |v a - v b| ≤ L * |a - b|)
    (hVv : ∀ a, |v a| ≤ V) {m : ℝ → ℝ} (hm : Integrable m) (hm0 : ∀ y, 0 ≤ m y)
    (hmc : Continuous m) (x : ℝ) :
    Integrable (fun y => fracD p v (x - y) * m y) ∧
      fracD p (fun x => ∫ y, v (x - y) * m y) x = ∫ y, fracD p v (x - y) * m y := by
  have hca : 0 < calpha p := c03_aux_calpha_pos p hp hp1
  set Φ : ℝ → ℝ → ℝ := fun z y => (v (x - y) - v (z - y)) * m y / |x - z| ^ (p + 1)
  have hψ : Integrable (fun z => c03_aux_psi p L (2 * V) (z - x)) :=
    (c03_aux_psi_integrable p L (2 * V) hp hp1).comp_sub_right x
  have hΦm : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable (fun q : ℝ × ℝ => v (x - q.2) - v (q.1 - q.2)) :=
      (hvc.measurable.comp (measurable_const.sub measurable_snd)).sub
        (hvc.measurable.comp (measurable_fst.sub measurable_snd))
    have h2 : Measurable (fun q : ℝ × ℝ => m q.2) := hmc.measurable.comp measurable_snd
    have h3 : Measurable (fun q : ℝ × ℝ => |x - q.1| ^ (p + 1)) :=
      (continuous_abs.measurable.comp (measurable_const.sub measurable_fst)).pow_const _
    exact (h1.mul h2).div h3
  have hΦi : Integrable (Function.uncurry Φ) (volume.prod volume) := by
    refine (hψ.mul_prod hm).mono' hΦm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, Φ, Real.norm_eq_abs]
    rw [mul_div_right_comm, abs_mul, abs_of_nonneg (hm0 q.2), abs_div,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right (c03_aux_quot_bound p hp hL0 hV0 hLv hVv _ _ x q.1
      (by ring)) (hm0 q.2)
  -- inner integrals
  have hvm : ∀ a, Integrable (fun y => v (a - y) * m y) := fun a =>
    (hm.const_mul V).mono' ((hvc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm0 y)]
        exact mul_le_mul_of_nonneg_right (hVv _) (hm0 y))
  have hz : ∀ z, ((∫ y, v (x - y) * m y) - ∫ y, v (z - y) * m y) / |x - z| ^ (p + 1) =
      ∫ y, Φ z y := by
    intro z
    rw [← integral_sub (hvm x) (hvm z), ← integral_div]
    congr 1; funext y; simp only [Φ]; ring
  have hy : ∀ y, ∫ z, Φ z y = m y * (fracD p v (x - y) / calpha p) := by
    intro y
    unfold fracD
    rw [mul_div_cancel_left₀ _ hca.ne', ← integral_const_mul]
    have := integral_sub_right_eq_self
      (fun u => m y * ((v (x - y) - v u) / |x - y - u| ^ (p + 1))) y (μ := volume)
    rw [← this]
    congr 1; funext z
    simp only [Φ, sub_sub_sub_cancel_right]
    ring
  have hint := hΦi.integral_prod_right
  simp only [Function.uncurry] at hint
  have hint' : Integrable (fun y => fracD p v (x - y) * m y) := by
    have h := hint.const_mul (calpha p)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [hy y]; field_simp
  refine ⟨hint', ?_⟩
  unfold fracD
  simp_rw [hz]
  rw [integral_integral_swap hΦi]
  simp_rw [hy]
  rw [← integral_const_mul]
  congr 1; funext y
  field_simp
  unfold fracD
  ring


theorem c03_aux_fracD_measurable (p : ℝ) {v : ℝ → ℝ} (hv : Continuous v) :
    Measurable (fracD p v) := by
  have hF : Measurable (fun q : ℝ × ℝ => (v q.1 - v q.2) / |q.1 - q.2| ^ (p + 1)) :=
    ((hv.measurable.comp measurable_fst).sub (hv.measurable.comp measurable_snd)).div
      ((continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)).pow_const _)
  have := (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  exact measurable_const.mul this

/-- Averaging a function that is `C^s` on `[-1,1]` against a density supported in `(-1/2,1/2)`. -/
theorem c03_aux_moll_local_norm (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) {G : ℝ → ℝ}
    (hGm : Measurable G) (hG : G ∈ c03_holder s (Icc (-1) 1)) {m : ℝ → ℝ} (hm : Integrable m)
    (hm0 : ∀ y, 0 ≤ m y) (hm1 : ∫ y, m y = 1) (hmc : Continuous m)
    (hsupp : ∀ y, 1 / 2 ≤ |y| → m y = 0) :
    (fun x => ∫ y, G (x - y) * m y) ∈ c03_holder s (Icc (-1 / 2) (1 / 2)) ∧
      c03_holder_normR s (Icc (-1 / 2) (1 / 2)) (fun x => ∫ y, G (x - y) * m y) ≤
        c03_holder_normR s (Icc (-1) 1) G := by
  set N := c03_holder_normR s (Icc (-1) 1) G
  have hN0 : 0 ≤ N := c03_aux_normR_nonneg _ _ _
  have hab : (-1 / 2 : ℝ) < 1 / 2 := by norm_num
  have hper : ∀ y, (fun x => ((G (x - y) * m y : ℝ) : ℂ)) ∈ c03_holder s (Icc (-1 / 2) (1 / 2)) ∧
      c03_holder_normR s (Icc (-1 / 2) (1 / 2)) (fun x => ((G (x - y) * m y : ℝ) : ℂ)) ≤
        N * m y := by
    intro y
    by_cases hy : 1 / 2 ≤ |y|
    · obtain ⟨hz, hzn⟩ := c03_aux_holder_zero (E := ℂ) s hab
      have hc := c03_aux_holder_congr (s := s) (I := Icc (-1 / 2) (1 / 2))
        (f := fun x => ((G (x - y) * m y : ℝ) : ℂ)) (g := fun _ => (0 : ℂ))
        (fun x _ => by simp [hsupp y hy])
      exact ⟨hc.2.1.2 hz, by rw [hc.2.2.1]; exact hzn.trans (mul_nonneg hN0 (hm0 y))⟩
    push Not at hy
    obtain ⟨hsh, hshn⟩ := c03_aux_holder_shift_restrict (y := y) (by norm_num : (-1 : ℝ) < 1) hab
      (Icc_subset_Icc (by linarith [(abs_lt.1 hy).2]) (by linarith [(abs_lt.1 hy).1])) hG
    obtain ⟨hc, hcn, -⟩ := c03_aux_holder_clm_norm hab Complex.ofRealCLM
      (by rw [Complex.ofRealCLM_norm]) hsh
    obtain ⟨hcm, hcmn⟩ := c03_aux_normR_const_mul hab ((m y : ℝ) : ℂ) hc
    have hcg := c03_aux_holder_congr (s := s) (I := Icc (-1 / 2) (1 / 2))
      (f := fun x => ((G (x - y) * m y : ℝ) : ℂ))
      (g := fun x => ((m y : ℝ) : ℂ) * Complex.ofRealCLM (G (x - y)))
      (fun x _ => by simp [mul_comm])
    refine ⟨hcg.2.1.2 hcm, ?_⟩
    rw [hcg.2.2.1]
    refine hcmn.trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm0 y), mul_comm N]
    exact mul_le_mul_of_nonneg_left (hcn.trans hshn) (hm0 y)
  have hmeas : Measurable (fun q : ℝ × ℝ => G (q.1 - q.2) * m q.2) :=
    (hGm.comp (measurable_fst.sub measurable_snd)).mul (hmc.measurable.comp measurable_snd)
  obtain ⟨h1, h2⟩ := c03_aux_param_real s hs hsN hab (fun x y => G (x - y) * m y) hmeas
    (fun y => N * m y) (fun y => mul_nonneg hN0 (hm0 y)) (hm.const_mul N) hper
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [integral_const_mul, hm1, mul_one]


theorem c03_aux_moll_facts {v : ℝ → ℝ} (hvcont : Continuous v) {L V : ℝ} (hL0 : 0 ≤ L)
    (hLv : ∀ a b, |v a - v b| ≤ L * |a - b|) (hVv : ∀ a, |v a| ≤ V) {m : ℝ → ℝ}
    (hmi : Integrable m) (hm0 : ∀ y, 0 ≤ m y) (hm1 : ∫ y, m y = 1) {δ : ℝ}
    (hmz : ∀ y, δ ≤ |y| → m y = 0) :
    (∀ x, Integrable (fun y => v (x - y) * m y)) ∧
    (∀ x, |(∫ y, v (x - y) * m y) - v x| ≤ L * δ) ∧
    (∀ a b, |(∫ y, v (a - y) * m y) - ∫ y, v (b - y) * m y| ≤ L * |a - b|) ∧
    (∀ a, |∫ y, v (a - y) * m y| ≤ V) := by
  have hvm : ∀ x, Integrable (fun y => v (x - y) * m y) := fun x =>
    (hmi.const_mul V).mono' ((hvcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hmi.aestronglyMeasurable) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm0 y)]
        exact mul_le_mul_of_nonneg_right (hVv _) (hm0 y))
  refine ⟨hvm, fun x => ?_, fun a b => ?_, fun a => ?_⟩
  · have h1 : v x = ∫ y, v x * m y := by rw [integral_const_mul, hm1, mul_one]
    have e : (∫ y, v (x - y) * m y) - v x = ∫ y, (v (x - y) - v x) * m y := by
      conv_lhs => rw [h1]
      rw [← integral_sub (hvm x) (hmi.const_mul _)]
      congr 1; funext y; ring
    rw [e]
    have hI : Integrable (fun y => (v (x - y) - v x) * m y) := by
      have := (hvm x).sub (hmi.const_mul (v x))
      refine this.congr (Eventually.of_forall fun y => ?_)
      simp only [Pi.sub_apply]; ring
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |(v (x - y) - v x) * m y| ≤ ∫ y, L * δ * m y := by
          refine integral_mono hI.abs (hmi.const_mul _) fun y => ?_
          show |(v (x - y) - v x) * m y| ≤ L * δ * m y
          rw [abs_mul, abs_of_nonneg (hm0 y)]
          by_cases hy : δ ≤ |y|
          · rw [hmz y hy]; simp
          · push Not at hy
            refine mul_le_mul_of_nonneg_right ?_ (hm0 y)
            refine (hLv _ _).trans ?_
            rw [show x - y - x = -y by ring, abs_neg]
            exact mul_le_mul_of_nonneg_left hy.le hL0
      _ = L * δ := by rw [integral_const_mul, hm1, mul_one]
  · rw [← integral_sub (hvm a) (hvm b)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |v (a - y) * m y - v (b - y) * m y| ≤ ∫ y, L * |a - b| * m y := by
          refine integral_mono ((hvm a).sub (hvm b)).abs (hmi.const_mul _) fun y => ?_
          show |v (a - y) * m y - v (b - y) * m y| ≤ L * |a - b| * m y
          rw [← sub_mul, abs_mul, abs_of_nonneg (hm0 y)]
          refine mul_le_mul_of_nonneg_right ((hLv _ _).trans (le_of_eq ?_)) (hm0 y)
          congr 2; ring
      _ = L * |a - b| := by rw [integral_const_mul, hm1, mul_one]
  · refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |v (a - y) * m y| ≤ ∫ y, V * m y := by
          refine integral_mono (hvm a).abs (hmi.const_mul _) fun y => ?_
          show |v (a - y) * m y| ≤ V * m y
          rw [abs_mul, abs_of_nonneg (hm0 y)]
          exact mul_le_mul_of_nonneg_right (hVv _) (hm0 y)
      _ = V := by rw [integral_const_mul, hm1, mul_one]

open scoped Convolution in
/-- Blueprint: lem:c03_gain_mollification.  `w_δ = v * ρ_δ ∈ C_c^∞`, `w_δ → v` uniformly,
`|D|^p w_δ = (|D|^p v) * ρ_δ` (absolutely convergent), `‖w_δ‖_{C^s(ℝ)} ≤ ‖v‖_{C^s(ℝ)}` and
`‖|D|^p w_δ‖_{C^s([-1/2,1/2])} ≤ ‖|D|^p v‖_{C^s([-1,1])}` for `0 < δ < 1/2`. -/
theorem c03_gain_mollification (p s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρsupp : tsupport ρ ⊆ Ioo (-1) 1) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (v : ℝ → ℝ) (hvc : HasCompactSupport v) (hvL : ∃ L, LipschitzWith L v)
    (hvs : v ∈ c03_holder s univ) (hDv : fracD p v ∈ c03_holder s (Icc (-1) 1)) :
    TendstoUniformly (c03_gain_mollify ρ v) v (𝓝[>] 0) ∧
    ∀ δ ∈ Ioo (0 : ℝ) (1 / 2),
      ContDiff ℝ (⊤ : ℕ∞) (c03_gain_mollify ρ v δ) ∧ HasCompactSupport (c03_gain_mollify ρ v δ) ∧
      (∀ x, Integrable (fun y => v (x - y) * (δ⁻¹ * ρ (y / δ)))) ∧
      (∀ x, Integrable (fun z => (v x - v z) / |x - z| ^ (p + 1))) ∧
      (∀ x, Integrable (fun z => (c03_gain_mollify ρ v δ x - c03_gain_mollify ρ v δ z) /
        |x - z| ^ (p + 1))) ∧
      (∀ x, Integrable (fun y => fracD p v (x - y) * (δ⁻¹ * ρ (y / δ)))) ∧
      (∀ x, fracD p (c03_gain_mollify ρ v δ) x = ∫ y, fracD p v (x - y) * (δ⁻¹ * ρ (y / δ))) ∧
      c03_holder_normR s univ (c03_gain_mollify ρ v δ) ≤ c03_holder_normR s univ v ∧
      c03_holder_normR s (Icc (-1 / 2) (1 / 2)) (fracD p (c03_gain_mollify ρ v δ)) ≤
        c03_holder_normR s (Icc (-1) 1) (fracD p v) := by
  obtain ⟨L, hL⟩ := hvL
  have hvcont : Continuous v := hL.continuous
  obtain ⟨V, hV⟩ := hvcont.bounded_above_of_compact_support hvc
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hVv : ∀ a, |v a| ≤ max V 0 := fun a => by
    have := hV a; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hLv : ∀ a b, |v a - v b| ≤ L * |a - b| := fun a b => by
    have := hL.dist_le_mul a b; rwa [Real.dist_eq, Real.dist_eq] at this
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / (L + 1) by positivity)] with δ hδ x
    obtain ⟨-, -, hm0, hmz, hmi, hm1⟩ := c03_aux_moll_basic hρ hρc hρsupp hρ0 hρ1 hδ.1
    have h := (c03_aux_moll_facts hvcont hL0 hLv hVv hmi hm0 hm1 hmz).2.1 x
    rw [Real.dist_eq, abs_sub_comm]
    refine (show |c03_gain_mollify ρ v δ x - v x| ≤ L * δ from h).trans_lt ?_
    calc (L : ℝ) * δ ≤ (L + 1) * δ := by nlinarith [hδ.1]
      _ < (L + 1) * (ε / (L + 1)) := by gcongr; exact hδ.2
      _ = ε := by field_simp
  obtain ⟨hδ0, hδ1⟩ := hδ
  obtain ⟨hmsm, hmcs, hm0, hmz, hmi, hm1⟩ := c03_aux_moll_basic hρ hρc hρsupp hρ0 hρ1 hδ0
  obtain ⟨hvm, -, hwL, hwV⟩ := c03_aux_moll_facts hvcont hL0 hLv hVv hmi hm0 hm1 hmz
  have hconv : c03_gain_mollify ρ v δ =
      ((fun y => δ⁻¹ * ρ (y / δ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) := by
    funext x
    rw [convolution_def]
    unfold c03_gain_mollify
    congr 1; funext y
    simp [mul_comm]
  have hwsm : ContDiff ℝ (⊤ : ℕ∞) (c03_gain_mollify ρ v δ) := by
    rw [hconv]
    exact hmcs.contDiff_convolution_left _ hmsm hvcont.locallyIntegrable
  have hwcs : HasCompactSupport (c03_gain_mollify ρ v δ) := by
    rw [hconv]; exact hmcs.convolution _ hvc
  have hfc := fun x => c03_aux_frac_conv p hp hp1 hvcont hL0 hV0 hLv hVv hmi hm0
    hmsm.continuous x
  have hid : fracD p (c03_gain_mollify ρ v δ) =
      fun x => ∫ y, fracD p v (x - y) * (δ⁻¹ * ρ (y / δ)) := by
    funext x; exact (hfc x).2
  have hloc := c03_aux_moll_local_norm s hs hsN (c03_aux_fracD_measurable p hvcont) hDv hmi hm0
    hm1 hmsm.continuous (fun y hy => hmz y (by linarith))
  refine ⟨hwsm, hwcs, hvm, c03_aux_quot_integrable p hp hp1 hvcont hL0 hV0 hLv hVv,
    c03_aux_quot_integrable p hp hp1 hwsm.continuous hL0 hV0 hwL hwV, fun x => (hfc x).1,
    fun x => (hfc x).2, ?_, ?_⟩
  · exact (c03_aux_moll_norm s hvs hmi hm0 hm1 (hwsm.of_le (by exact_mod_cast le_top))).2
  · rw [hid]; exact hloc.2


/-- A concrete cutoff: `η = 1` on `[-2,2]`, `η = 0` off `[-3,3]`. -/
def c03_aux_eta (x : ℝ) : ℝ := Real.smoothTransition (3 - |x|)

theorem c03_aux_eta_props : ContDiff ℝ (⊤ : ℕ∞) c03_aux_eta ∧ (∀ x, 0 ≤ c03_aux_eta x ∧ c03_aux_eta x ≤ 1) ∧
    (∀ x ∈ Icc (-2 : ℝ) 2, c03_aux_eta x = 1) ∧ (∀ x, 3 < |x| → c03_aux_eta x = 0) := by
  refine ⟨?_, fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun x hx => Real.smoothTransition.one_of_one_le (by have := abs_le.2 ⟨hx.1, hx.2⟩; linarith),
    fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith)⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    have : ∀ᶠ ξ in 𝓝 (0 : ℝ), |ξ| < 1 := by
      have := (continuous_abs.tendsto (0 : ℝ)); rw [abs_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [this] with ξ hξ
    exact Real.smoothTransition.one_of_one_le (by linarith)
  · exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.sub (contDiffAt_abs hx))

/-- Blueprint: lem:c03_frac_translate.  Translation invariance of `|D|^p`. -/
theorem c03_frac_translate (p : ℝ) (g : ℝ → ℝ) (x₀ y : ℝ) :
    fracD p (fun x => g (x + x₀)) y = fracD p g (y + x₀) := by
  unfold fracD
  congr 1
  rw [← integral_add_right_eq_self (fun z => (g (y + x₀) - g z) / |y + x₀ - z| ^ (p + 1)) x₀]
  congr 1; funext z
  congr 2; ring_nf

/-- Translation preserves `C^s_loc(ℝ)`. -/
theorem c03_aux_loc_translate {s : ℝ} {G : ℝ → ℝ} (hG : G ∈ c03_holder_loc s univ) (x₀ : ℝ) :
    (fun x => G (x + x₀)) ∈ c03_holder_loc s univ := by
  have hGk : ContDiff ℝ ⌊s⌋₊ G := contDiffOn_univ.1 hG.1
  have hk : ContDiff ℝ ⌊s⌋₊ (fun x => G (x + x₀)) := hGk.comp (contDiff_id.add contDiff_const)
  refine ⟨hk.contDiffOn, fun a b _ => ?_⟩
  rcases lt_or_ge a b with hab | hab
  · have h := (c03_aux_holder_shift_restrict (y := -x₀) (by linarith : a + x₀ < b + x₀) hab
      (by rw [sub_neg_eq_add, sub_neg_eq_add]) (hG.2 (a + x₀) (b + x₀) (subset_univ _))).1
    simpa [sub_neg_eq_add] using h
  · exact c03_aux_holder_degen s a b hab _ hk.contDiffOn


/-- Blueprint: lem:c03_holder_glue.  Gluing: `C^{s'}` on every interval `[x₀-1/2, x₀+1/2]` implies `C^{s'}_loc`. -/
theorem c03_holder_glue (s' : ℝ) (hs' : 0 < s') (hs'N : ∀ n : ℕ, s' ≠ n) (g : ℝ → ℝ)
    (h : ∀ x₀ : ℝ, g ∈ c03_holder s' (Icc (x₀ - 1 / 2) (x₀ + 1 / 2))) :
    g ∈ c03_holder_loc s' univ := by
  set k := ⌊s'⌋₊
  have hgk : ContDiff ℝ k g := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    exact (h x).1.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  refine ⟨hgk.contDiffOn, fun a b _ => ?_⟩
  rcases le_or_gt b a with hab | hab
  · exact c03_aux_holder_degen s' a b hab g hgk.contDiffOn
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ c d : ℝ, c < d → ∀ x ∈ Icc c d,
      iteratedDerivWithin i g (Icc c d) x = iteratedDeriv i g x := fun i hi c d hcd x hx =>
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hcd)
      ((hgk.of_le (by exact_mod_cast hi)).contDiffAt) hx
  have hcont : ∀ i ≤ k, Continuous (iteratedDeriv i g) := fun i hi =>
    hgk.continuous_iteratedDeriv i (by exact_mod_cast hi)
  refine c03_aux_holder_of s' _ g hgk.contDiffOn (fun i hi => ?_) ?_
  · obtain ⟨Mb, hMb⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      (hcont i hi).continuousOn
    exact ⟨Mb, fun x hx => by rw [heq i hi a b hab x hx]; exact hMb x hx⟩
  · obtain ⟨S, hS⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      (hcont k le_rfl).continuousOn
    have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS a (left_mem_Icc.2 hab.le))
    choose C hC using fun c : ℝ => (c03_aux_holder_bounds s' _ g (h c)).2
    set N := ⌈(b - a) * 8⌉₊
    set cen : ℕ → ℝ := fun j => a + j / 8
    set Ctot : ℝ≥0 := ∑ j ∈ Finset.range (N + 1), C (cen j) + Real.toNNReal (8 * S)
    set θr := ((Real.toNNReal (s' - ⌊s'⌋₊) : ℝ≥0) : ℝ)
    have hθr0 : 0 ≤ θr := NNReal.coe_nonneg _
    have hθr1 : θr ≤ 1 := by
      have : Real.toNNReal (s' - ⌊s'⌋₊) ≤ 1 := by
        rw [Real.toNNReal_le_one]; linarith [Nat.lt_floor_add_one s']
      exact_mod_cast this
    refine ⟨Ctot, c03_aux_holderOnWith_of_dist fun x hx y hy => ?_⟩
    rw [heq k le_rfl a b hab x hx, heq k le_rfl a b hab y hy]
    have hd0 : 0 ≤ dist x y ^ θr := Real.rpow_nonneg dist_nonneg _
    have hCtot : (8 * S) ≤ (Ctot : ℝ) ∧ ∀ j ≤ N, (C (cen j) : ℝ) ≤ Ctot := by
      constructor
      · simp only [Ctot]; push_cast
        rw [Real.coe_toNNReal _ (by positivity)]
        have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1), (C (cen j) : ℝ) :=
          Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
        linarith
      · intro j hj
        simp only [Ctot]; push_cast
        have h1 := Finset.single_le_sum (f := fun j => (C (cen j) : ℝ))
          (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
        have : (0 : ℝ) ≤ ((Real.toNNReal (8 * S) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
        linarith
    rcases le_or_gt (dist x y) (1 / 4) with hxy | hxy
    · set j := ⌊(x - a) * 8⌋₊
      have hxa : 0 ≤ (x - a) * 8 := by nlinarith [hx.1]
      have hj1 : (j : ℝ) ≤ (x - a) * 8 := Nat.floor_le hxa
      have hj2 : (x - a) * 8 < j + 1 := Nat.lt_floor_add_one _
      have hjN : j ≤ N := by
        apply Nat.floor_le_of_le
        calc (x - a) * 8 ≤ (b - a) * 8 := by nlinarith [hx.2]
          _ ≤ N := Nat.le_ceil _
      set c := cen j
      have hc1 : c ≤ x := by simp only [c, cen]; linarith
      have hc2 : x - c ≤ 1 / 8 := by simp only [c, cen]; linarith
      have hyc : |y - x| ≤ 1 / 4 := by rw [← Real.dist_eq, dist_comm]; exact hxy
      have hxI : x ∈ Icc (c - 1 / 2) (c + 1 / 2) := ⟨by linarith, by linarith⟩
      have hyI : y ∈ Icc (c - 1 / 2) (c + 1 / 2) :=
        ⟨by linarith [(abs_le.1 hyc).1], by linarith [(abs_le.1 hyc).2]⟩
      have hcd : c - 1 / 2 < c + 1 / 2 := by linarith
      have := (hC c).dist_le hxI hyI
      rw [heq k le_rfl _ _ hcd x hxI, heq k le_rfl _ _ hcd y hyI] at this
      exact this.trans (mul_le_mul_of_nonneg_right (hCtot.2 j hjN) hd0)
    · have h1 : (1 / 4 : ℝ) ≤ dist x y ^ θr := by
        calc (1 / 4 : ℝ) = (1 / 4) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (1 / 4) ^ θr := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hθr1
          _ ≤ dist x y ^ θr := Real.rpow_le_rpow (by norm_num) hxy.le hθr0
      calc dist (iteratedDeriv k g x) (iteratedDeriv k g y)
          ≤ ‖iteratedDeriv k g x‖ + ‖iteratedDeriv k g y‖ := dist_le_norm_add_norm _ _
        _ ≤ S + S := add_le_add (hS x hx) (hS y hy)
        _ ≤ 8 * S * dist x y ^ θr := by nlinarith
        _ ≤ Ctot * dist x y ^ θr := mul_le_mul_of_nonneg_right hCtot.1 hd0

/-- Blueprint: lem:c03_gain_localization_wide.  Localization on the wider interval `[-3/2,3/2]`. -/
theorem c03_gain_localization_wide (p s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) (hη1 : ∀ x ∈ Icc (-2 : ℝ) 2, η x = 1)
    (hη3 : ∀ x, 3 < |x| → η x = 0) (g : ℝ → ℝ) (hgb : ∃ M, ∀ x, |g x| ≤ M)
    (hg : LocallyLipschitz g) (hgs : g ∈ c03_holder_loc s univ)
    (hint : ∀ y, Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)))
    (hDg : fracD p g ∈ c03_holder_loc s univ) :
    fracD p (fun x => η x * g x) ∈ c03_holder s (Icc (-3 / 2) (3 / 2)) := by
  have hcp : c03_cp p = calpha p := (c03_frac_kernel_formula p hp hp1).2.2.2.2.1
  obtain ⟨M, hM⟩ := hgb
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hgc : Continuous g := hg.continuous
  obtain ⟨Dk, -, hT⟩ := c03_aux_T_smooth p hp hη hη1 hη3 hη01 (c := 1 / 8) (by norm_num)
    (by norm_num)
  obtain ⟨F, hF, hTF, -⟩ := hT g hgc M hM
  set I := Icc (-3 / 2 : ℝ) (3 / 2)
  have hyI : ∀ y ∈ I, |y| ≤ 3 / 2 := fun y hy => abs_le.2 ⟨by linarith [hy.1], hy.2⟩
  -- tail integrability
  have htail : ∀ y ∈ I, Integrable (fun z => (1 - η z) * g z / |y - z| ^ (p + 1)) := by
    intro y hy
    have hint0 : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(p + 1))) volume :=
      integrable_one_add_norm (by simp; linarith)
    refine ((hint0.const_mul (M * 6 ^ (p + 1)))).mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((continuous_const.sub hη.continuous).measurable.mul hgc.measurable).div
        ((continuous_abs.measurable.comp (measurable_const.sub measurable_id)).pow_const _)
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs]
      by_cases hz : |z| ≤ 2
      · rw [hη1 z (abs_le.1 hz)]
        simp only [sub_self, zero_mul, zero_div, abs_zero]
        positivity
      · push Not at hz
        have hyb := hyI y hy
        have hzy : (1 + |z|) / 6 ≤ |y - z| := by
          have := abs_sub_abs_le_abs_sub z y
          rw [abs_sub_comm z y] at this; linarith
        have hpos : 0 < |y - z| := by linarith
        have h2 : ((1 + |z|) / 6) ^ (p + 1) ≤ |y - z| ^ (p + 1) :=
          Real.rpow_le_rpow (by positivity) hzy (by linarith)
        have h3 : ((1 + |z|) / 6) ^ (p + 1) = (1 + |z|) ^ (p + 1) / 6 ^ (p + 1) :=
          Real.div_rpow (by positivity) (by norm_num) _
        have hnum : |(1 - η z) * g z| ≤ M := by
          rw [abs_mul]
          have : |1 - η z| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hη01 z]
          calc |1 - η z| * |g z| ≤ 1 * M := mul_le_mul this (hM z) (abs_nonneg _) zero_le_one
            _ = M := one_mul M
        have hden : 0 < |y - z| ^ (p + 1) := Real.rpow_pos_of_pos hpos _
        have h6 : 0 < (1 + |z|) ^ (p + 1) := by positivity
        rw [abs_div, abs_of_pos hden, Real.rpow_neg (by positivity), div_le_iff₀ hden]
        calc |(1 - η z) * g z| ≤ M := hnum
          _ = M * 6 ^ (p + 1) * ((1 + |z|) ^ (p + 1))⁻¹ * ((1 + |z|) ^ (p + 1) / 6 ^ (p + 1)) := by
              field_simp
          _ ≤ M * 6 ^ (p + 1) * ((1 + |z|) ^ (p + 1))⁻¹ * |y - z| ^ (p + 1) := by
              gcongr
              rw [← h3]; exact h2
  -- the identity on `I`
  have hid : ∀ y ∈ I, fracD p (fun x => η x * g x) y = fracD p g y - F y := by
    intro y hy
    have hyb := hyI y hy
    have hηy : η y = 1 := hη1 y ⟨by linarith [(abs_le.1 hyb).1], by linarith [(abs_le.1 hyb).2]⟩
    have hB := htail y hy
    have hsplit : (fun z => (η y * g y - η z * g z) / |y - z| ^ (p + 1)) =
        fun z => (g y - g z) / |y - z| ^ (p + 1) + (1 - η z) * g z / |y - z| ^ (p + 1) := by
      funext z; rw [hηy]; ring
    rw [← hTF y (by linarith)]
    unfold fracD c03_gain_localization_T
    rw [hsplit, integral_add (hint y) hB, hcp]
    have e : (∫ z, (1 - η z) * g z / |z - y| ^ (1 + p)) =
        ∫ z, (1 - η z) * g z / |y - z| ^ (p + 1) := by
      congr 1; funext z; simp only [abs_sub_comm z y, add_comm 1 p]
    rw [e]; ring
  have hFI : F ∈ c03_holder s I :=
    c03_aux_holder_smooth s F (hF.of_le (by exact_mod_cast le_top)) _ _
  obtain ⟨hnF, -, -⟩ := c03_aux_holder_clm_norm (by norm_num : (-3 / 2 : ℝ) < 3 / 2)
    (-ContinuousLinearMap.id ℝ ℝ) (by rw [norm_neg]; exact ContinuousLinearMap.norm_id_le) hFI
  have hsum := c03_aux_holder_add s (-3 / 2) (3 / 2) _ _ (hDg.2 _ _ (subset_univ _)) hnF
  refine ((c03_aux_holder_congr (s := s) (I := I) (f := fracD p (fun x => η x * g x))
    (g := fun x => fracD p g x + (-ContinuousLinearMap.id ℝ ℝ) (F x)) fun x hx => ?_).2.1).2 hsum
  rw [hid x hx]
  simp [sub_eq_add_neg]

/-- Averaging a function that is `C^s` on `[-3/2,3/2]` against a density supported in `(-1/2,1/2)`. -/
theorem c03_aux_moll_local_norm_wide (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) {G : ℝ → ℝ}
    (hGm : Measurable G) (hG : G ∈ c03_holder s (Icc (-3 / 2) (3 / 2))) {m : ℝ → ℝ} (hm : Integrable m)
    (hm0 : ∀ y, 0 ≤ m y) (hm1 : ∫ y, m y = 1) (hmc : Continuous m)
    (hsupp : ∀ y, 1 / 2 ≤ |y| → m y = 0) :
    (fun x => ∫ y, G (x - y) * m y) ∈ c03_holder s (Icc (-1) 1) ∧
      c03_holder_normR s (Icc (-1) 1) (fun x => ∫ y, G (x - y) * m y) ≤
        c03_holder_normR s (Icc (-3 / 2) (3 / 2)) G := by
  set N := c03_holder_normR s (Icc (-3 / 2) (3 / 2)) G
  have hN0 : 0 ≤ N := c03_aux_normR_nonneg _ _ _
  have hab : (-1 : ℝ) < 1 := by norm_num
  have hper : ∀ y, (fun x => ((G (x - y) * m y : ℝ) : ℂ)) ∈ c03_holder s (Icc (-1) 1) ∧
      c03_holder_normR s (Icc (-1) 1) (fun x => ((G (x - y) * m y : ℝ) : ℂ)) ≤
        N * m y := by
    intro y
    by_cases hy : 1 / 2 ≤ |y|
    · obtain ⟨hz, hzn⟩ := c03_aux_holder_zero (E := ℂ) s hab
      have hc := c03_aux_holder_congr (s := s) (I := Icc (-1) 1)
        (f := fun x => ((G (x - y) * m y : ℝ) : ℂ)) (g := fun _ => (0 : ℂ))
        (fun x _ => by simp [hsupp y hy])
      exact ⟨hc.2.1.2 hz, by rw [hc.2.2.1]; exact hzn.trans (mul_nonneg hN0 (hm0 y))⟩
    push Not at hy
    obtain ⟨hsh, hshn⟩ := c03_aux_holder_shift_restrict (y := y) (by norm_num : (-3 / 2 : ℝ) < 3 / 2) hab
      (Icc_subset_Icc (by linarith [(abs_lt.1 hy).2]) (by linarith [(abs_lt.1 hy).1])) hG
    obtain ⟨hc, hcn, -⟩ := c03_aux_holder_clm_norm hab Complex.ofRealCLM
      (by rw [Complex.ofRealCLM_norm]) hsh
    obtain ⟨hcm, hcmn⟩ := c03_aux_normR_const_mul hab ((m y : ℝ) : ℂ) hc
    have hcg := c03_aux_holder_congr (s := s) (I := Icc (-1) 1)
      (f := fun x => ((G (x - y) * m y : ℝ) : ℂ))
      (g := fun x => ((m y : ℝ) : ℂ) * Complex.ofRealCLM (G (x - y)))
      (fun x _ => by simp [mul_comm])
    refine ⟨hcg.2.1.2 hcm, ?_⟩
    rw [hcg.2.2.1]
    refine hcmn.trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm0 y), mul_comm N]
    exact mul_le_mul_of_nonneg_left (hcn.trans hshn) (hm0 y)
  have hmeas : Measurable (fun q : ℝ × ℝ => G (q.1 - q.2) * m q.2) :=
    (hGm.comp (measurable_fst.sub measurable_snd)).mul (hmc.measurable.comp measurable_snd)
  obtain ⟨h1, h2⟩ := c03_aux_param_real s hs hsN hab (fun x y => G (x - y) * m y) hmeas
    (fun y => N * m y) (fun y => mul_nonneg hN0 (hm0 y)) (hm.const_mul N) hper
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [integral_const_mul, hm1, mul_one]



/-- Blueprint: lem:c03_gain_mollification_wide.  Mollification estimate from `[-3/2,3/2]` to `[-1,1]`. -/
theorem c03_gain_mollification_wide (p s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρsupp : tsupport ρ ⊆ Ioo (-1) 1) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (v : ℝ → ℝ) (hvc : HasCompactSupport v) (hvL : ∃ L, LipschitzWith L v)
    (hvs : v ∈ c03_holder s univ) (hDv : fracD p v ∈ c03_holder s (Icc (-3 / 2) (3 / 2))) :
    ∀ δ ∈ Ioo (0 : ℝ) (1 / 2),
      c03_gain_mollify ρ v δ ∈ c03_holder s univ ∧
      fracD p (c03_gain_mollify ρ v δ) ∈ c03_holder s (Icc (-1) 1) ∧
      c03_holder_normR s (Icc (-1) 1) (fracD p (c03_gain_mollify ρ v δ)) ≤
        c03_holder_normR s (Icc (-3 / 2) (3 / 2)) (fracD p v) := by
  intro δ hδ
  have hDv1 : fracD p v ∈ c03_holder s (Icc (-1) 1) := by
    have := (c03_aux_holder_shift_restrict (y := 0) (by norm_num : (-3 / 2 : ℝ) < 3 / 2)
      (by norm_num : (-1 : ℝ) < 1) (Icc_subset_Icc (by norm_num) (by norm_num)) hDv).1
    simpa using this
  obtain ⟨-, hmoll⟩ := c03_gain_mollification p s hp hp1 hs hsN ρ hρ hρc hρsupp hρ0 hρ1 v hvc hvL
    hvs hDv1
  obtain ⟨hsm, -, -, -, -, -, hid, -, -⟩ := hmoll δ hδ
  obtain ⟨hmsm, -, hm0, hmz, hmi, hm1⟩ := c03_aux_moll_basic hρ hρc hρsupp hρ0 hρ1 hδ.1
  obtain ⟨L, hL⟩ := hvL
  have hmem := (c03_aux_moll_norm s hvs hmi hm0 hm1 (hsm.of_le (by exact_mod_cast le_top))).1
  have hloc := c03_aux_moll_local_norm_wide s hs hsN (c03_aux_fracD_measurable p hL.continuous)
    hDv hmi hm0 hm1 hmsm.continuous (fun y hy => hmz y (by linarith [hδ.2]))
  have e : fracD p (c03_gain_mollify ρ v δ) = fun x => ∫ y, fracD p v (x - y) * (δ⁻¹ * ρ (y / δ)) :=
    funext hid
  refine ⟨hmem, ?_, ?_⟩
  · rw [e]; exact hloc.1
  · rw [e]; exact hloc.2

/-- Blueprint: lem:c03_linear_gain.  If `g ∈ L^∞ ∩ W^{1,∞}_loc ∩ C^s_loc` and the (pointwise,
absolutely convergent) `|D|^p g ∈ C^s_loc`, then `g ∈ C^{s+p}_loc`. -/
theorem c03_linear_gain (p s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (hspN : ∀ n : ℕ, s + p ≠ n) (g : ℝ → ℝ)
    (hgb : ∃ M, ∀ x, |g x| ≤ M) (hgW : W1inftyLoc g) (hgs : g ∈ c03_holder_loc s univ)
    (hint : ∀ y, Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)))
    (hh : fracD p g ∈ c03_holder_loc s univ) :
    g ∈ c03_holder_loc (s + p) univ := by
  obtain ⟨hη, hη01, hη1, hη3⟩ := c03_aux_eta_props
  -- the mollifier
  set B : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  set ρ : ℝ → ℝ := B.normed volume
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := B.contDiff_normed
  have hρc : HasCompactSupport ρ := B.hasCompactSupport_normed
  have hρsupp : tsupport ρ ⊆ Ioo (-1) 1 := by
    rw [B.tsupport_normed_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    have : |x| ≤ 1 / 2 := hx
    exact ⟨by linarith [(abs_le.1 this).1], by linarith [(abs_le.1 this).2]⟩
  have hρ0 : ∀ x, 0 ≤ ρ x := B.nonneg_normed
  have hρ1 : ∫ x, ρ x = 1 := B.integral_normed
  obtain ⟨CS, hCS0, hCS⟩ := c03_schauder_RS p s hp hp1 hs hsN hspN
  have hsp : 0 < s + p := by linarith
  -- the local statement at a centre `x₀`
  have hlocal : ∀ x₀ : ℝ, g ∈ c03_holder (s + p) (Icc (x₀ - 1 / 2) (x₀ + 1 / 2)) := by
    intro x₀
    set h : ℝ → ℝ := fun x => g (x + x₀)
    have hhb : ∃ M, ∀ x, |h x| ≤ M := by
      obtain ⟨M, hM⟩ := hgb; exact ⟨M, fun x => hM _⟩
    have hhL : LocallyLipschitz h := by
      have ht : LipschitzWith 1 (fun x : ℝ => x + x₀) :=
        LipschitzWith.of_dist_le_mul fun a b => by simp [Real.dist_eq]
      exact hgW.comp ht.locallyLipschitz
    have hhs : h ∈ c03_holder_loc s univ := c03_aux_loc_translate hgs x₀
    have hhint : ∀ y, Integrable (fun z => (h y - h z) / |y - z| ^ (p + 1)) := by
      intro y
      have := (hint (y + x₀)).comp_add_right x₀
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [h]; congr 2; ring_nf
    have hDh : fracD p h ∈ c03_holder_loc s univ := by
      have e : fracD p h = fun x => fracD p g (x + x₀) := funext fun y => c03_frac_translate p g x₀ y
      rw [e]; exact c03_aux_loc_translate hh x₀
    obtain ⟨-, hloc⟩ := c03_gain_localization p s hp hp1 hs hsN c03_aux_eta hη hη01 hη1 hη3
    obtain ⟨hvc, hvL, hvs, -, -, -, hDv1⟩ := hloc h hhb hhL hhs hhint hDh
    have hDvw := c03_gain_localization_wide p s hp hp1 hs hsN c03_aux_eta hη hη01 hη1 hη3 h hhb hhL
      hhs hhint hDh
    set v : ℝ → ℝ := fun x => c03_aux_eta x * h x
    obtain ⟨hunif, hmoll⟩ := c03_gain_mollification p s hp hp1 hs hsN ρ hρ hρc hρsupp hρ0 hρ1 v
      hvc hvL hvs hDv1
    have hmw := c03_gain_mollification_wide p s hp hp1 hs hsN ρ hρ hρc hρsupp hρ0 hρ1 v hvc hvL hvs
      hDvw
    set Nv := c03_holder_normR s univ v
    set Nw := c03_holder_normR s (Icc (-3 / 2) (3 / 2)) (fracD p v)
    have hNv : 0 ≤ Nv := c03_aux_normR_nonneg _ _ _
    have hNw : 0 ≤ Nw := c03_aux_normR_nonneg _ _ _
    set δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 3)
    have hδn : ∀ n, δn n ∈ Ioo (0 : ℝ) (1 / 2) := fun n => by
      simp only [δn, mem_Ioo]
      constructor
      · positivity
      · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hδlim : Tendsto δn atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hδn n).1⟩
      simpa [δn] using (tendsto_one_div_add_atTop_nhds_zero_nat.comp
        (tendsto_add_atTop_nat 2)).congr fun n => by simp [δn]; ring_nf
    set wn : ℕ → ℝ → ℝ := fun n => c03_gain_mollify ρ v (δn n)
    have hwn : ∀ n, wn n ∈ c03_holder (s + p) (Icc (-1 / 2) (1 / 2)) ∧
        c03_holder_normR (s + p) (Icc (-1 / 2) (1 / 2)) (wn n) ≤ CS * (Nv + Nw) := by
      intro n
      obtain ⟨hsm, -, -, -, -, -, -, hnv, -⟩ := hmoll (δn n) (hδn n)
      obtain ⟨hwu, -, hwn1⟩ := hmw (δn n) (hδn n)
      refine ⟨c03_aux_holder_smooth (s + p) _ (hsm.of_le (by exact_mod_cast le_top)) _ _, ?_⟩
      refine (hCS (wn n) hsm hwu).trans ?_
      gcongr
    have hconv : TendstoUniformlyOn wn v atTop (Icc (-1 / 2) (1 / 2)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have := (Metric.tendstoUniformly_iff.1 hunif ε hε)
      filter_upwards [hδlim.eventually this] with n hn x _ using hn x
    obtain ⟨hvsp, -⟩ := c03_holder_closed_ball (E := ℝ) (s + p) hsp hspN (-1 / 2) (1 / 2)
      (by norm_num) (CS * (Nv + Nw)) (by positivity) wn v (fun n => (hwn n).1)
      (fun n => (hwn n).2) hconv
    have hhsp : h ∈ c03_holder (s + p) (Icc (-1 / 2) (1 / 2)) :=
      ((c03_aux_holder_congr (s := s + p) (I := Icc (-1 / 2) (1 / 2)) (f := h) (g := v)
        fun x hx => by
          simp only [v]; rw [hη1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩, one_mul]).2.1).2 hvsp
    have := (c03_aux_holder_shift_restrict (y := x₀) (by norm_num : (-1 / 2 : ℝ) < 1 / 2)
      (by linarith : x₀ - 1 / 2 < x₀ + 1 / 2) (by rw [show x₀ - 1 / 2 - x₀ = -1 / 2 by ring,
        show x₀ + 1 / 2 - x₀ = 1 / 2 by ring]) hhsp).1
    simpa [h] using this
  exact c03_holder_glue (s + p) hsp hspN g hlocal

/-- `C^s_loc` (real-valued) is closed under linear combinations. -/
theorem c03_aux_holder_lincomb {s : ℝ} (a b : ℝ) {X Y : ℝ → ℝ}
    (hX : X ∈ c03_holder_loc s univ) (hY : Y ∈ c03_holder_loc s univ) :
    (fun y => a * X y + b * Y y) ∈ c03_holder_loc s univ := by
  set k := ⌊s⌋₊
  refine ⟨(contDiffOn_const.mul hX.1).add (contDiffOn_const.mul hY.1), fun a₀ b₀ _ => ?_⟩
  have hXI := hX.2 a₀ b₀ (subset_univ _)
  have hYI := hY.2 a₀ b₀ (subset_univ _)
  refine ⟨(contDiffOn_const.mul hXI.1).add (contDiffOn_const.mul hYI.1), ?_⟩
  set I := Icc a₀ b₀
  set F : ℝ → ℝ := fun y => a * X y + b * Y y with hF
  rcases lt_or_ge a₀ b₀ with hab | hab
  · have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
    have hiter : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i F I x =
        a * iteratedDerivWithin i X I x + b * iteratedDerivWithin i Y I x := by
      intro i hi x hx
      have hXi : ContDiffWithinAt ℝ i X I x := (hXI.1.of_le (by exact_mod_cast hi)) x hx
      have hYi : ContDiffWithinAt ℝ i Y I x := (hYI.1.of_le (by exact_mod_cast hi)) x hx
      rw [show F = (fun y => a * X y) + (fun y => b * Y y) from rfl,
        iteratedDerivWithin_add hx hU (contDiffWithinAt_const.mul hXi)
          (contDiffWithinAt_const.mul hYi),
        iteratedDerivWithin_const_mul hx hU a hXi, iteratedDerivWithin_const_mul hx hU b hYi]
    have hXn := hXI.2; have hYn := hYI.2
    unfold c03_holder_norm at hXn hYn ⊢
    obtain ⟨hXC, hXH⟩ := ENNReal.add_lt_top.1 hXn
    obtain ⟨hYC, hYH⟩ := ENNReal.add_lt_top.1 hYn
    obtain ⟨CX, hCX⟩ := iInf_lt_iff.1 hXH
    obtain ⟨hHX, -⟩ := iInf_lt_iff.1 hCX
    obtain ⟨CY, hCY⟩ := iInf_lt_iff.1 hYH
    obtain ⟨hHY, -⟩ := iInf_lt_iff.1 hCY
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · unfold c03_Ck_norm at hXC hYC ⊢
      refine lt_of_le_of_lt (b := ‖a‖ₑ * (∑ i ∈ Finset.range (k + 1),
        ⨆ x ∈ I, ‖iteratedDerivWithin i X I x‖ₑ) + ‖b‖ₑ * (∑ i ∈ Finset.range (k + 1),
        ⨆ x ∈ I, ‖iteratedDerivWithin i Y I x‖ₑ)) ?_ ?_
      · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i hi => iSup₂_le fun x hx => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [hiter i hik x hx]
        refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [enorm_mul]
          exact mul_le_mul_right (le_iSup₂ (f := fun x _ => ‖iteratedDerivWithin i X I x‖ₑ) x hx) _
        · rw [enorm_mul]
          exact mul_le_mul_right (le_iSup₂ (f := fun x _ => ‖iteratedDerivWithin i Y I x‖ₑ) x hx) _
      · exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top enorm_lt_top hXC,
          ENNReal.mul_lt_top enorm_lt_top hYC⟩
    · have hH : HolderOnWith (‖a‖₊ * CX + ‖b‖₊ * CY) (Real.toNNReal (s - k))
          (iteratedDerivWithin k F I) I := by
        intro x hx y hy
        rw [hiter k le_rfl x hx, hiter k le_rfl y hy]
        refine (edist_add_add_le _ _ _ _).trans ?_
        rw [ENNReal.coe_add, add_mul]
        refine add_le_add ?_ ?_
        · rw [← smul_eq_mul, ← smul_eq_mul (a := a), edist_smul₀, ENNReal.smul_def, smul_eq_mul,
            ENNReal.coe_mul, mul_assoc]
          exact mul_le_mul_right (hHX x hx y hy) _
        · rw [← smul_eq_mul, ← smul_eq_mul (a := b), edist_smul₀, ENNReal.smul_def, smul_eq_mul,
            ENNReal.coe_mul, mul_assoc]
          exact mul_le_mul_right (hHY x hx y hy) _
      exact lt_of_le_of_lt (iInf_le_of_le _ (iInf_le_of_le hH le_rfl)) ENNReal.coe_lt_top
  · have hsub : I.Subsingleton := Set.subsingleton_Icc_of_ge hab
    unfold c03_holder_norm c03_Ck_norm
    refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 fun i _ => ?_, ?_⟩
    · refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_) (enorm_lt_top (x := iteratedDerivWithin i F I a₀))
      have : x = a₀ := le_antisymm (hx.2.trans hab) hx.1
      rw [this]
    · exact lt_of_le_of_lt (iInf_le_of_le 0 (iInf_le_of_le (hsub.holderOnWith 0 _ _) le_rfl))
        ENNReal.coe_lt_top


/-- `C^s_loc` membership of a globally `C^k` function from `C^s` on all intervals of length
`≥ 1` (by restriction). -/
theorem c03_aux_holder_loc_of_long (s : ℝ) (g : ℝ → ℝ) (hg : ContDiff ℝ ⌊s⌋₊ g)
    (h : ∀ a b : ℝ, 1 ≤ b - a → g ∈ c03_holder s (Icc a b)) : g ∈ c03_holder_loc s univ := by
  set k := ⌊s⌋₊
  refine ⟨hg.contDiffOn, fun a b _ => ?_⟩
  rcases le_or_gt b a with hab | hab
  · exact c03_aux_holder_degen s a b hab g hg.contDiffOn
  set c := max b (a + 1)
  have hJ := h a c (by simp only [c]; linarith [le_max_right b (a + 1)])
  have hIJ : Icc a b ⊆ Icc a c := Icc_subset_Icc le_rfl (le_max_left _ _)
  have hUI : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hUJ : UniqueDiffOn ℝ (Icc a c) := uniqueDiffOn_Icc (by
    simp only [c]; linarith [le_max_right b (a + 1)])
  have heq : ∀ i ≤ k, ∀ x ∈ Icc a b,
      iteratedDerivWithin i g (Icc a b) x = iteratedDerivWithin i g (Icc a c) x := by
    intro i hi x hx
    have hca : ContDiffAt ℝ i g x := (hg.of_le (by exact_mod_cast hi)).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv hUI hca hx,
      iteratedDerivWithin_eq_iteratedDeriv hUJ hca (hIJ hx)]
  obtain ⟨hb, C, hC⟩ := c03_aux_holder_bounds s _ g hJ
  refine c03_aux_holder_of s _ g hg.contDiffOn (fun i hi => ?_) ⟨C, fun x hx y hy => ?_⟩
  · obtain ⟨M, hM⟩ := hb i hi
    exact ⟨M, fun x hx => by rw [heq i hi x hx]; exact hM x (hIJ hx)⟩
  · rw [heq k le_rfl x hx, heq k le_rfl y hy]
    exact hC x (hIJ hx) y (hIJ hy)


/-- `ρ` is smooth. -/
theorem c03_aux_rho_smooth : ContDiff ℝ (⊤ : ℕ∞) rho := by
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

/-- The cutoff properties of `ρ`. -/
theorem c03_aux_rho_props : HasCompactSupport rho ∧ (∀ t ∈ Icc (-1 : ℝ) 1, rho t = 1) ∧
    (∀ t : ℝ, 2 < |t| → rho t = 0) ∧ (∀ t, 0 ≤ rho t ∧ rho t ≤ 1) := by
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_, fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  · refine HasCompactSupport.intro (K := Icc (-2) 2) isCompact_Icc fun x hx => ?_
    unfold rho
    apply Real.smoothTransition.zero_of_nonpos
    have : 2 < |x| := by
      by_contra h; exact hx (abs_le.mp (not_lt.mp h))
    linarith
  · unfold rho; exact Real.smoothTransition.one_of_one_le (by linarith [abs_le.2 ⟨ht.1, ht.2⟩])
  · unfold rho; exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Blueprint: lem:c03_I_regularity.  If `f' ∈ C^s_loc` then `ℐ_ε(f) ∈ C^s_loc` and
`B_ε(f')(f - y f') ∈ C^s_loc`. -/
theorem c03_I_regularity (p ε s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class)
    (hf' : deriv f ∈ c03_holder_loc s univ) :
    c03_I_eps p ε f ∈ c03_holder_loc s univ ∧
    (fun y => A_eps_B p ε (deriv f y) * (f y - y * deriv f y)) ∈ c03_holder_loc s univ := by
  obtain ⟨hRc, hR1, hR2, hR01⟩ := c03_aux_rho_props
  constructor
  · obtain ⟨hid, hfar⟩ := (c03_I_far p ε s hp hp1 hε hs hsN rho c03_aux_rho_smooth hRc hR1 hR2
      hR01).1 f hf hf'
    have hnear := (c03_I_near p ε s hp hp1 hε hs hsN).1 rho c03_aux_rho_smooth hRc hR1 hR2 hR01
      f hf hf'
    have he : c03_I_eps p ε f = fun y => 1 * c03_I_far_op p ε rho f y +
        1 * c03_I_near_op p ε rho f y := by
      funext y; rw [hid y]; ring
    rw [he]
    exact c03_aux_holder_lincomb 1 1 hfar hnear
  · obtain ⟨hcalc1, hcalc2⟩ := c03_holder_calculus s hs hsN
    obtain ⟨hC1, ⟨K0, hK0⟩, -⟩ := hf
    set k := ⌊s⌋₊
    have hfk : ContDiff ℝ k (deriv f) := contDiffOn_univ.1 hf'.1
    have hf1 : ContDiff ℝ (k + 1) f :=
      contDiff_succ_iff_deriv.2 ⟨hC1.differentiable one_ne_zero, by simp, hfk⟩
    have hfk0 : ContDiff ℝ k f := hf1.of_le (by exact_mod_cast Nat.le_succ k)
    have hB : ContDiff ℝ (⊤ : ℕ∞) (A_eps_B p ε) := c03_aux_B_contDiff p hε
    have hFk : ContDiff ℝ k (fun y => A_eps_B p ε (deriv f y) * (f y - y * deriv f y)) :=
      ((hB.of_le (by exact_mod_cast le_top)).comp hfk).mul (hfk0.sub (contDiff_id.mul hfk))
    refine c03_aux_holder_loc_of_long s _ hFk fun a b hab1 => ?_
    have hu : deriv f ∈ c03_holder s (Icc a b) := hf'.2 a b (subset_univ _)
    have hid : (fun y : ℝ => y) ∈ c03_holder s (Icc a b) :=
      c03_aux_holder_smooth s _ (contDiff_id.of_le le_top) a b
    have hfI : f ∈ c03_holder s (Icc a b) := c03_aux_holder_smooth s f hf1 a b
    obtain ⟨Mf, hMf⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      hC1.continuous.continuousOn
    set K := |K0| + |a| + |b| + |Mf| + 1
    have hK : 0 < K := by positivity
    have hyK : ∀ y ∈ Icc a b, |y| ≤ K := fun y hy => by
      have : |y| ≤ |a| + |b| := by
        rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
          linarith [hy.1, hy.2]
      linarith [abs_nonneg K0, abs_nonneg Mf]
    have hdK : ∀ y, |deriv f y| ≤ K := fun y => by
      linarith [hK0 y, le_abs_self K0, abs_nonneg a, abs_nonneg b, abs_nonneg Mf]
    have hfK : ∀ y ∈ Icc a b, |f y| ≤ K := fun y hy => by
      have := hMf y hy; rw [Real.norm_eq_abs] at this
      linarith [le_abs_self Mf, abs_nonneg K0, abs_nonneg a, abs_nonneg b]
    -- compositions
    have hcomp : ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → ∀ u v : ℝ → ℝ,
        u ∈ c03_holder s (Icc a b) → v ∈ c03_holder s (Icc a b) →
        (∀ x ∈ Icc a b, |u x| ≤ K ∧ |v x| ≤ K) →
        (fun x => G (u x, v x)) ∈ c03_holder s (Icc a b) := by
      intro G hG u v hu hv huv
      obtain ⟨M, hM0, hM⟩ := c03_aux_G_bound G hG (⌈s⌉₊ + 1) K
      obtain ⟨C', -, hC'⟩ := hcalc2 K M hK hM0
      exact (hC' a b hab1 G hG hM u v hu hv huv).1
    have hX := hcomp (fun q => ((A_eps_B p ε q.1 : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hB.comp contDiff_fst)) (deriv f) (fun y => y) hu hid
      (fun x hx => ⟨hdK x, hyK x hx⟩)
    have hP := hcomp (fun q => ((q.2 * q.1 : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (contDiff_snd.mul contDiff_fst)) (deriv f) (fun y => y)
      hu hid (fun x hx => ⟨hdK x, hyK x hx⟩)
    have hFc := hcomp (fun q => ((q.1 : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp contDiff_fst)
      f f hfI hfI (fun x hx => ⟨hfK x hx, hfK x hx⟩)
    have hnP := c03_aux_holder_clm s a b (-ContinuousLinearMap.id ℝ ℂ)
      (by rw [norm_neg]; exact ContinuousLinearMap.norm_id_le) _ hP
    have hY := c03_aux_holder_add s a b _ _ hFc hnP
    obtain ⟨Cp, -, hprod⟩ := hcalc1
    have hXY := (hprod a b hab1 _ _ hX hY).1
    have hre := c03_aux_holder_clm s a b Complex.reCLM (by rw [Complex.reCLM_norm]) _ hXY
    convert hre using 1
    funext y
    simp [Complex.mul_re]
    ring_nf
    simp

-- Encoding: the "in particular" part refers to the profile of thm:fixed_point_correction
-- and the family of thm:fixed_point_approximation (other chapters); it is stated conditionally:
-- for any `C^∞` profile `f̄` with bounded derivative and any `r ∈ X_γ` with `γ > 1/p` solving
-- `ℒ_ε r + 𝒩_{ε,f̄}(r) = -ℰ_ε(f̄)` (eqn:fixed_point_correction), `f̄ + r` and `r` are `C^∞`.
/-- Blueprint: thm:fixed_point_smoothness.  Every `W^{2,∞}_loc` solution with bounded derivative
of `ℰ_ε(f) = 0` in `𝒟'` is `C^∞`; in particular the corrected profiles are smooth. -/
theorem fixed_point_smoothness (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ ε, 0 ≤ ε → ∀ f : ℝ → ℝ, f ∈ c01_admissible_class →
      c03_distrib_zero (residual p ε f) → ContDiff ℝ (⊤ : ℕ∞) f) ∧
    (∀ ε γ, 0 ≤ ε → 1 / p < γ → ∀ fbar r : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) fbar →
      (∃ M, ∀ x, |deriv fbar x| ≤ M) → r ∈ X_gamma p γ →
      (∀ y, L_eps p ε r y + N_eps p ε fbar r y = -residual p ε fbar y) →
      ContDiff ℝ (⊤ : ℕ∞) (fbar + r) ∧ ContDiff ℝ (⊤ : ℕ∞) r) := by
  have part1 : ∀ ε, 0 ≤ ε → ∀ f : ℝ → ℝ, f ∈ c01_admissible_class →
      c03_distrib_zero (residual p ε f) → ContDiff ℝ (⊤ : ℕ∞) f := by
    intro ε hε f hf hdz
    obtain ⟨hint, -, -, -, -, -, -, -, -, hiff⟩ := c03_I_well_defined p ε hp hp1 hε f hf
    have hres0 := hiff.1 hdz
    have hsk := (analysis_semilinear_kernel p ε hp hp1 hε f hf).2
    have hfrac : fracD p (deriv f) = fun y => (-1) * (A_eps_B p ε (deriv f y) *
        (f y - y * deriv f y)) + (-1) * c03_I_eps p ε f y := by
      funext y
      have := hsk y
      rw [hres0 y] at this
      unfold fracDdy at this
      linarith
    -- choice of `s₀` with `s₀ + n p ∉ ℕ`
    have hcount : (Set.range (fun kn : ℕ × ℕ => (kn.1 : ℝ) - kn.2 * p)).Countable :=
      Set.countable_range _
    have hnot : ¬ (Ioo (0 : ℝ) 1 ⊆ Set.range (fun kn : ℕ × ℕ => (kn.1 : ℝ) - kn.2 * p)) := by
      intro hsub
      have h1 := measure_mono (μ := volume) hsub
      rw [hcount.measure_zero, Real.volume_Ioo] at h1
      norm_num at h1
    obtain ⟨s₀, hs₀, hs₀N⟩ := Set.not_subset.1 hnot
    have hN : ∀ n k : ℕ, s₀ + n * p ≠ k := fun n k h =>
      hs₀N ⟨(k, n), by simp only; linarith⟩
    have hstep : ∀ n : ℕ, deriv f ∈ c03_holder_loc (s₀ + n * p) univ := by
      intro n
      induction n with
      | zero => simpa using c03_holder_loc_of_locallyLipschitz s₀ hs₀.1 hs₀.2 (deriv f) hf.2.2
      | succ n ih =>
        have hsn : 0 < s₀ + n * p := by have := hs₀.1; positivity
        have hsnN : ∀ m : ℕ, s₀ + n * p ≠ m := hN n
        have hsn1N : ∀ m : ℕ, s₀ + n * p + p ≠ m := fun m h => hN (n + 1) m (by push_cast; linarith)
        obtain ⟨hIreg, hBreg⟩ := c03_I_regularity p ε (s₀ + n * p) hp hp1 hε hsn hsnN f hf ih
        have hh : fracD p (deriv f) ∈ c03_holder_loc (s₀ + n * p) univ := by
          rw [hfrac]; exact c03_aux_holder_lincomb (-1) (-1) hBreg hIreg
        have := c03_linear_gain p (s₀ + n * p) hp hp1 hsn hsnN hsn1N (deriv f) hf.2.1 hf.2.2 ih
          hint hh
        convert this using 2; push_cast; ring
    have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := by
      rw [contDiff_infty]
      intro m
      obtain ⟨n, hn⟩ := exists_nat_gt ((m : ℝ) / p)
      have hm : m ≤ ⌊s₀ + n * p⌋₊ := by
        rw [Nat.le_floor_iff (by have := hs₀.1; positivity)]
        have : (m : ℝ) < n * p := by rwa [div_lt_iff₀ hp] at hn
        linarith [hs₀.1]
      exact (contDiffOn_univ.1 (hstep n).1).of_le (by exact_mod_cast hm)
    exact contDiff_infty_iff_deriv.2 ⟨hf.1.differentiable one_ne_zero, hd⟩
  refine ⟨part1, ?_⟩
  intro ε γ hε hγ fbar r hfbar hMb hr hL
  obtain ⟨M, hM⟩ := hMb
  have hres : ∀ y, residual p ε (fbar + r) y = 0 := fun y => by
    have := hL y; unfold N_eps at this; linarith
  obtain ⟨⟨hr1, hr2⟩, hrn⟩ := hr
  -- `r'` is bounded
  set N := (X_gamma_norm p γ r).toReal
  have hjb : ∀ y, 1 ≤ jb y := fun y => Real.one_le_sqrt.2 (by nlinarith [sq_nonneg y])
  have hγp : 0 ≤ γ - 1 / p := by linarith
  have hae : ∀ᵐ y ∂volume, |deriv r y| ≤ N := by
    have h1 := ENNReal.ae_le_essSup (μ := volume.restrict (Ici 0)) (fun y => ENNReal.ofReal
      (jb y ^ γ * (‖r y‖ + jb y ^ (-1 / p) * ‖deriv r y‖ + jb y ^ (-2 / p) * ‖deriv (deriv r) y‖)))
    have h2 := ENNReal.ae_le_essSup (μ := volume.restrict (Iic 0)) (fun y => ENNReal.ofReal
      (jb y ^ γ * (‖r y‖ + jb y * ‖deriv r y‖ + jb y ^ (2 : ℕ) * ‖deriv (deriv r) y‖)))
    rw [ae_restrict_iff' measurableSet_Ici] at h1
    rw [ae_restrict_iff' measurableSet_Iic] at h2
    filter_upwards [h1, h2] with y hy1 hy2
    have hj := hjb y
    have hj0 : 0 < jb y := by linarith
    rcases le_total 0 y with hy | hy
    · have := (ENNReal.ofReal_le_iff_le_toReal hrn.ne).1
        ((hy1 hy).trans (le_add_right le_rfl : _ ≤ X_gamma_norm p γ r))
      have he : 1 ≤ jb y ^ γ * jb y ^ (-1 / p) := by
        rw [← Real.rpow_add hj0]; exact Real.one_le_rpow hj (by rw [neg_div]; linarith)
      have hg0 : 0 ≤ jb y ^ γ := Real.rpow_nonneg hj0.le _
      have hg1 : 0 ≤ jb y ^ (-2 / p) := Real.rpow_nonneg hj0.le _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this
      have : |deriv r y| ≤ jb y ^ γ * jb y ^ (-1 / p) * |deriv r y| :=
        le_mul_of_one_le_left (abs_nonneg _) he
      nlinarith [abs_nonneg (r y), abs_nonneg (deriv (deriv r) y), abs_nonneg (deriv r y),
        mul_nonneg hg0 (abs_nonneg (r y)), mul_nonneg hg0 (mul_nonneg hg1
          (abs_nonneg (deriv (deriv r) y)))]
    · have := (ENNReal.ofReal_le_iff_le_toReal hrn.ne).1
        ((hy2 hy).trans (le_add_left le_rfl : _ ≤ X_gamma_norm p γ r))
      have hg0 : 1 ≤ jb y ^ γ := Real.one_le_rpow hj (by
        have : 0 < 1 / p := by positivity
        linarith)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at this
      have h3 : |deriv r y| ≤ jb y * |deriv r y| := le_mul_of_one_le_left (abs_nonneg _) hj
      have h4 : 0 ≤ jb y ^ (2 : ℕ) * |deriv (deriv r) y| := by positivity
      have h5 : |deriv r y| ≤ |r y| + jb y * |deriv r y| + jb y ^ (2 : ℕ) * |deriv (deriv r) y| := by
        linarith [abs_nonneg (r y)]
      have h6 : 0 ≤ |r y| + jb y * |deriv r y| + jb y ^ (2 : ℕ) * |deriv (deriv r) y| := by
        positivity
      nlinarith
  have hrbound : ∀ y, |deriv r y| ≤ N := by
    intro y
    by_contra hc
    push Not at hc
    have hcont : Continuous (fun y => |deriv r y|) := (hr1.continuous_deriv le_rfl).abs
    have hopen : IsOpen {x | N < |deriv r x|} := isOpen_lt continuous_const hcont
    have hpos := hopen.measure_pos volume ⟨y, hc⟩
    rw [ae_iff] at hae
    simp only [not_le] at hae
    exact hpos.ne' hae
  -- admissibility of `fbar + r`
  have hd1 : ∀ x, deriv (fbar + r) x = deriv fbar x + deriv r x := fun x =>
    deriv_add (hfbar.differentiable (by simp) x) (hr1.differentiable one_ne_zero x)
  have hadm : fbar + r ∈ c01_admissible_class := by
    refine ⟨(hfbar.of_le (by exact_mod_cast le_top)).add hr1, ⟨M + N, fun x => ?_⟩, ?_⟩
    · rw [hd1]; exact (abs_add_le _ _).trans (add_le_add (hM x) (hrbound x))
    · have h1 : LocallyLipschitz (deriv fbar) :=
        ((contDiff_infty_iff_deriv.1 hfbar).2.of_le (by exact_mod_cast le_top)).locallyLipschitz
      rw [show deriv (fbar + r) = fun x => deriv fbar x + deriv r x from funext hd1]
      exact h1.add hr2
  have hdz : c03_distrib_zero (residual p ε (fbar + r)) := by
    intro φ _ _; simp [hres]
  have hsm := part1 ε hε (fbar + r) hadm hdz
  refine ⟨hsm, ?_⟩
  have := hsm.sub hfbar
  simpa using this

end GSQG
