import GSQG.PatchEquation.Velocity

/-!
# Beyond the paper (2D patch derivation): normal speed integrability, normal trace, flat-graph check
(blueprint ch. 13)

Helpers are named `c13n_aux_*`.

Blueprint: lem:c13_normal_speed_integrable, lem:c13_normal_trace, lem:c13_flat_graph_check.
Standing assumptions of the chapter: `1 < α < 2`, `0 < c`.

The normal trace is formed from the *combined* quantity `U₂ − F_x U₁` evaluated at the off-graph
point `(x, F(x,t) + d)`, `d ≠ 0`; the values of `c13_graph_velocity` on the (null) graph are never
used.  The flat-graph lemma records that the tangential component itself diverges.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### Pure helpers (`c13n_aux_*`, all fully proved) -/
lemma c13n_aux_pt_zero (x y : ℝ) : c13_pt x y 0 = x := by simp [c13_pt]
lemma c13n_aux_pt_one (x y : ℝ) : c13_pt x y 1 = y := by simp [c13_pt]
lemma c13n_aux_pt_sub (a b x y : ℝ) : c13_pt a b - c13_pt x y = c13_pt (a - x) (b - y) := by
  ext i; fin_cases i <;> simp [c13_pt]
lemma c13n_aux_norm_pt (x y : ℝ) : ‖c13_pt x y‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [EuclideanSpace.norm_eq]; simp [c13_pt, Fin.sum_univ_two, sq_abs]
lemma c13n_aux_norm_pt_rpow (x y r : ℝ) : ‖c13_pt x y‖ ^ r = (x ^ 2 + y ^ 2) ^ (r / 2) := by
  rw [c13n_aux_norm_pt, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; ring_nf
lemma c13n_aux_abs_le_norm_pt (x y : ℝ) : |x| ≤ ‖c13_pt x y‖ := by
  rw [c13n_aux_norm_pt]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg y])

lemma c13n_aux_rpow_le_abs {p h B : ℝ} (hp : 0 ≤ p) (hh : h ≠ 0) (hB : h ^ 2 ≤ B) :
    B ^ (-p / 2) ≤ |h| ^ (-p) := by
  have h2 : 0 < h ^ 2 := by positivity
  calc B ^ (-p / 2) ≤ (h ^ 2) ^ (-p / 2) := Real.rpow_le_rpow_of_nonpos h2 hB (by linarith)
    _ = |h| ^ (-p) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; congr 1; push_cast; ring

lemma c13n_aux_kernel_diff {α : ℝ} (hα : 0 < α) {h : ℝ} (hh : h ≠ 0) (e δ : ℝ) :
    |(h ^ 2 + (δ - e) ^ 2) ^ (-α / 2) - (h ^ 2 + (0 - e) ^ 2) ^ (-α / 2)| ≤
      α * |h| ^ (-α - 1) * |δ| := by
  have hpos : ∀ u : ℝ, 0 < h ^ 2 + (u - e) ^ 2 := fun u => by positivity
  set g : ℝ → ℝ := fun u => (h ^ 2 + (u - e) ^ 2) ^ (-α / 2)
  set g' : ℝ → ℝ := fun u => (-α / 2) * (h ^ 2 + (u - e) ^ 2) ^ (-α / 2 - 1) * (2 * (u - e))
  have hd : ∀ u, HasDerivAt g (g' u) u := by
    intro u
    have h1 : HasDerivAt (fun u => h ^ 2 + (u - e) ^ 2) (2 * (u - e)) u := by
      have := ((hasDerivAt_id u).sub_const e).pow 2
      simpa using this.const_add (h ^ 2)
    have := h1.rpow_const (p := -α / 2) (Or.inl (hpos u).ne')
    simpa [g, g', mul_comm, mul_assoc, mul_left_comm] using this
  have hb : ∀ u, ‖g' u‖ ≤ α * |h| ^ (-α - 1) := by
    intro u
    set B := h ^ 2 + (u - e) ^ 2
    have hB := hpos u
    have hue : |u - e| ≤ B ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg h])
    have hpow : B ^ (-α / 2 - 1) * B ^ (1 / 2 : ℝ) = B ^ (-(α + 1) / 2) := by
      rw [← Real.rpow_add hB]; congr 1; ring
    have hle := c13n_aux_rpow_le_abs (p := α + 1) (by linarith) hh (by nlinarith [sq_nonneg (u - e)] : h ^ 2 ≤ B)
    rw [Real.norm_eq_abs]
    simp only [g']
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hB.le _),
      abs_of_nonpos (by linarith : -α / 2 ≤ 0), abs_of_pos (two_pos)]
    calc -(-α / 2) * B ^ (-α / 2 - 1) * (2 * |u - e|)
        = α * (B ^ (-α / 2 - 1) * |u - e|) := by ring
      _ ≤ α * (B ^ (-α / 2 - 1) * B ^ (1 / 2 : ℝ)) := by gcongr
      _ = α * B ^ (-(α + 1) / 2) := by rw [hpow]
      _ ≤ α * |h| ^ (-(α + 1)) := by gcongr
      _ = α * |h| ^ (-α - 1) := by ring_nf
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (s := univ)
    (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hb u) convex_univ (mem_univ 0) (mem_univ δ)
  simpa [g, Real.norm_eq_abs] using this

/-- The scale-free profile `|r|^{1-α}` near zero and `|r|^{-α}` at infinity. -/
def c13n_aux_profile (α r : ℝ) : ℝ := if |r| ≤ 1 then |r| ^ (1 - α) else |r| ^ (-α)

lemma c13n_aux_profile_nonneg (α r : ℝ) : 0 ≤ c13n_aux_profile α r := by
  unfold c13n_aux_profile; split_ifs <;> positivity

lemma c13n_aux_abs_rpow_intervalIntegrable {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun r : ℝ => |r| ^ p) volume (-1) 1 := by
  have h01 : IntervalIntegrable (fun r : ℝ => |r| ^ p) volume 0 1 := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hp
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this ⊢
    refine this.congr_fun (fun r hr => ?_) measurableSet_Ioc
    simp [abs_of_pos hr.1]
  have hm : IntervalIntegrable (fun r : ℝ => |r| ^ p) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa using h01.symm
  exact hm.trans h01

lemma c13n_aux_profile_integrable {α : ℝ} (hα : 1 < α) (hα2 : α < 2) :
    Integrable (c13n_aux_profile α) := by
  have hS : MeasurableSet {r : ℝ | |r| ≤ 1} := measurableSet_le (by fun_prop) (by fun_prop)
  have hnear : IntegrableOn (c13n_aux_profile α) {r : ℝ | |r| ≤ 1} := by
    have h1 := c13n_aux_abs_rpow_intervalIntegrable (p := 1 - α) (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h1
    have hset : {r : ℝ | |r| ≤ 1} = Icc (-1) 1 := by ext r; simp [abs_le]
    rw [hset]
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Icc
    have : |r| ≤ 1 := abs_le.mpr hr
    simp [c13n_aux_profile, this]
  have hfar : IntegrableOn (c13n_aux_profile α) {r : ℝ | |r| ≤ 1}ᶜ := by
    have hj : Integrable (fun r : ℝ => (2 : ℝ) ^ (α / 2) * (1 + r ^ 2) ^ (-α / 2)) := by
      have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := α)
        (by simp; linarith)
      exact (by simpa [Real.norm_eq_abs, sq_abs] using this : Integrable
        (fun r : ℝ => (1 + r ^ 2) ^ (-α / 2))).const_mul _
    refine (hj.integrableOn).mono' ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_).restrict
      unfold c13n_aux_profile
      exact Measurable.ite hS (by fun_prop) (by fun_prop)
    · refine (ae_restrict_iff' hS.compl).mpr (Eventually.of_forall fun r hr => ?_)
      have hr' : ¬ |r| ≤ 1 := hr
      have hr1 : 1 < |r| := lt_of_not_ge hr'
      simp only [c13n_aux_profile, hr', ite_false, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      have h0 : 0 < |r| := by linarith
      -- |r|^{-α} = (r²)^{-α/2} ≤ 2^{α/2} (1+r²)^{-α/2} since 1 + r² ≤ 2 r²
      have e1 : |r| ^ (-α) = (r ^ 2) ^ (-α / 2) := by
        rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul h0.le]; congr 1; push_cast; ring
      have e2 : (2 : ℝ) ^ (α / 2) * (1 + r ^ 2) ^ (-α / 2) = ((1 + r ^ 2) / 2) ^ (-α / 2) := by
        rw [Real.div_rpow (by positivity) (by norm_num), show (-α / 2) = -(α / 2) by ring,
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
      rw [e1, e2]
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      have : 1 ≤ r ^ 2 := by nlinarith [sq_abs r]
      linarith
  have := hnear.union hfar
  rwa [union_compl_self, integrableOn_univ] at this


lemma c13n_aux_abs_mul_rpow {u α : ℝ} (hu : 0 < u) : u * u ^ (-α) = u ^ (1 - α) := by
  rw [show 1 - α = 1 + -α by ring, Real.rpow_add hu, Real.rpow_one]

lemma c13n_aux_abs_mul_rpow' {u α : ℝ} (hu : 0 < u) : u * u ^ (-α - 1) = u ^ (-α) := by
  rw [show -α - 1 = -α + -1 by ring, Real.rpow_add hu, Real.rpow_neg_one]; field_simp

lemma c13n_aux_scale_near {a u α : ℝ} (ha : 0 < a) (hu : 0 < u) :
    a ^ (1 - α) * (u / a) ^ (1 - α) = u ^ (1 - α) := by
  rw [Real.div_rpow hu.le ha.le]; field_simp

lemma c13n_aux_scale_far {a u α : ℝ} (ha : 0 < a) (hu : 0 < u) :
    a ^ (1 - α) * (u / a) ^ (-α) = a * u ^ (-α) := by
  rw [Real.div_rpow hu.le ha.le, show 1 - α = 1 + -α by ring, Real.rpow_add ha, Real.rpow_one]
  have : 0 < a ^ (-α) := Real.rpow_pos_of_pos ha _
  field_simp

/-- Pointwise near/far bound for the normal-speed integrand at every vertical offset `δ`. -/
lemma c13n_aux_pointwise {α L M : ℝ} (hα : 0 < α) {φ e : ℝ → ℝ}
    (hφ1 : ∀ h, |h| ≤ 1 → |φ h| ≤ L * |h|) (hφ2 : ∀ h, |φ h| ≤ 2 * M) (δ : ℝ) {h : ℝ}
    (hh : h ≠ 0) :
    |φ h * (h ^ 2 + (δ - e h) ^ 2) ^ (-α / 2)| ≤
      (if |h| ≤ 1 then L * |h| ^ (1 - α) else 2 * M * |h| ^ (-α)) := by
  have hk := c13n_aux_rpow_le_abs (p := α) (B := h ^ 2 + (δ - e h) ^ 2) hα.le hh
    (by nlinarith [sq_nonneg (δ - e h)])
  have hk0 : 0 ≤ (h ^ 2 + (δ - e h) ^ 2) ^ (-α / 2) := by positivity
  have hu : 0 < |h| := abs_pos.mpr hh
  rw [abs_mul, abs_of_nonneg hk0]
  split_ifs with h1
  · calc |φ h| * (h ^ 2 + (δ - e h) ^ 2) ^ (-α / 2) ≤ (L * |h|) * |h| ^ (-α) :=
          mul_le_mul (hφ1 h h1) hk hk0 (by nlinarith [abs_nonneg (φ h), hφ1 h h1])
      _ = L * |h| ^ (1 - α) := by rw [mul_assoc, c13n_aux_abs_mul_rpow hu]
  · exact mul_le_mul (hφ2 h) hk hk0 (by nlinarith [abs_nonneg (φ h), hφ2 h])

lemma c13n_aux_ite_le_profile {α L M h : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) :
    (if |h| ≤ 1 then L * |h| ^ (1 - α) else 2 * M * |h| ^ (-α)) ≤
      (L + 2 * M) * c13n_aux_profile α h := by
  unfold c13n_aux_profile
  split_ifs
  · have : 0 ≤ |h| ^ (1 - α) := by positivity
    nlinarith
  · have : 0 ≤ |h| ^ (-α) := by positivity
    nlinarith


lemma c13n_aux_diff_pointwise {α L M : ℝ} (hα0 : 0 < α) (hL : 0 ≤ L) (hM : 0 ≤ M)
    {φ e : ℝ → ℝ} (hφ1 : ∀ h, |h| ≤ 1 → |φ h| ≤ L * |h|) (hφ2 : ∀ h, |φ h| ≤ 2 * M)
    {d : ℝ} (hd : d ≠ 0) (hd1 : |d| ≤ 1) (h : ℝ) :
    |φ h * (h ^ 2 + (d - e h) ^ 2) ^ (-α / 2) - φ h * (h ^ 2 + (0 - e h) ^ 2) ^ (-α / 2)| ≤
      (2 * L + α * L + 2 * α * M) * |d| ^ (1 - α) * c13n_aux_profile α (|d|⁻¹ * h) := by
  have ha : 0 < |d| := abs_pos.mpr hd
  have hPn := c13n_aux_profile_nonneg α (|d|⁻¹ * h)
  have hφ0 : φ 0 = 0 := by
    have := hφ1 0 (by simp); simpa using this
  have hK0L : 2 * L ≤ 2 * L + α * L + 2 * α * M := by nlinarith
  have hK0L' : α * L ≤ 2 * L + α * L + 2 * α * M := by nlinarith
  have hK0M : 2 * α * M ≤ 2 * L + α * L + 2 * α * M := by nlinarith
  by_cases hh : h = 0
  · subst hh; rw [hφ0]; simp only [zero_mul, sub_self, abs_zero]
    have : 0 ≤ |d| ^ (1 - α) := Real.rpow_nonneg ha.le _
    have : 0 ≤ 2 * L + α * L + 2 * α * M := by linarith
    positivity
  have hu : 0 < |h| := abs_pos.mpr hh
  have hah : |(|d|)⁻¹ * h| = |h| / |d| := by
    rw [abs_mul, abs_inv, abs_abs, inv_mul_eq_div]
  have hk := fun δ : ℝ => c13n_aux_rpow_le_abs (p := α) (B := h ^ 2 + (δ - e h) ^ 2) hα0.le hh
    (by nlinarith [sq_nonneg (δ - e h)])
  have hkd := c13n_aux_kernel_diff hα0 hh (e h) d
  rw [← mul_sub, abs_mul]
  set D := (h ^ 2 + (d - e h) ^ 2) ^ (-α / 2) - (h ^ 2 + (0 - e h) ^ 2) ^ (-α / 2) with hD
  set K0 := 2 * L + α * L + 2 * α * M
  by_cases h1 : |h| ≤ |d|
  · have hP' : c13n_aux_profile α (|d|⁻¹ * h) = (|h| / |d|) ^ (1 - α) := by
      simp only [c13n_aux_profile, hah, div_le_one ha, h1, ite_true]
    rw [hP', mul_assoc, c13n_aux_scale_near ha hu]
    have hdiff : |D| ≤ 2 * |h| ^ (-α) := by
      have h0d : 0 ≤ (h ^ 2 + (d - e h) ^ 2) ^ (-α / 2) := by positivity
      have h00 : 0 ≤ (h ^ 2 + (0 - e h) ^ 2) ^ (-α / 2) := by positivity
      rw [abs_le]; constructor <;> linarith [hk d, hk 0]
    have hφh : |φ h| ≤ L * |h| := hφ1 h (h1.trans hd1)
    have hp0 : 0 ≤ |h| ^ (1 - α) := by positivity
    calc |φ h| * |D| ≤ (L * |h|) * (2 * |h| ^ (-α)) :=
          mul_le_mul hφh hdiff (abs_nonneg _) (by positivity)
      _ = 2 * L * (|h| * |h| ^ (-α)) := by ring
      _ = 2 * L * |h| ^ (1 - α) := by rw [c13n_aux_abs_mul_rpow hu]
      _ ≤ K0 * |h| ^ (1 - α) := mul_le_mul_of_nonneg_right hK0L hp0
  · have hP' : c13n_aux_profile α (|d|⁻¹ * h) = (|h| / |d|) ^ (-α) := by
      have : ¬ |h| / |d| ≤ 1 := by rw [div_le_one ha]; exact h1
      simp only [c13n_aux_profile, hah, this, ite_false]
    rw [hP', mul_assoc, c13n_aux_scale_far ha hu]
    have hp0 : 0 ≤ |d| * |h| ^ (-α) := by positivity
    by_cases h2 : |h| ≤ 1
    · calc |φ h| * |D| ≤ (L * |h|) * (α * |h| ^ (-α - 1) * |d|) :=
            mul_le_mul (hφ1 h h2) hkd (abs_nonneg _) (by positivity)
        _ = α * L * |d| * (|h| * |h| ^ (-α - 1)) := by ring
        _ = α * L * (|d| * |h| ^ (-α)) := by rw [c13n_aux_abs_mul_rpow' hu]; ring
        _ ≤ K0 * (|d| * |h| ^ (-α)) := mul_le_mul_of_nonneg_right hK0L' hp0
    · have h2' : 1 < |h| := lt_of_not_ge h2
      have hle : |h| ^ (-α - 1) ≤ |h| ^ (-α) :=
        Real.rpow_le_rpow_of_exponent_le h2'.le (by linarith)
      calc |φ h| * |D| ≤ (2 * M) * (α * |h| ^ (-α - 1) * |d|) :=
            mul_le_mul (hφ2 h) hkd (abs_nonneg _) (by positivity)
        _ ≤ (2 * M) * (α * |h| ^ (-α) * |d|) := by gcongr
        _ = 2 * α * M * (|d| * |h| ^ (-α)) := by ring
        _ ≤ K0 * (|d| * |h| ^ (-α)) := mul_le_mul_of_nonneg_right hK0M hp0

/-- The one-dimensional core of the normal-trace argument: uniform integrability in the vertical offset and
the `|d|^{2-α}` trace estimate, for a numerator with `|φ(h)| ≤ L|h|` near `0` and `|φ| ≤ 2M`. -/
lemma c13n_aux_core {α : ℝ} (hα : 1 < α) (hα2 : α < 2) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ e : ℝ → ℝ, Measurable φ → Measurable e →
      (∀ h, |h| ≤ 1 → |φ h| ≤ L * |h|) → (∀ h, |φ h| ≤ 2 * M) →
      (∀ δ : ℝ, Integrable (fun h => φ h * (h ^ 2 + (δ - e h) ^ 2) ^ (-α / 2))) ∧
      (∀ d : ℝ, d ≠ 0 → |d| ≤ 1 →
        |(∫ h, φ h * (h ^ 2 + (d - e h) ^ 2) ^ (-α / 2)) -
            ∫ h, φ h * (h ^ 2 + (0 - e h) ^ 2) ^ (-α / 2)| ≤ K * |d| ^ (2 - α)) := by
  have hP := c13n_aux_profile_integrable hα hα2
  have hα0 : 0 < α := by linarith
  have hK0 : 0 ≤ 2 * L + α * L + 2 * α * M := by positivity
  have hIP : 0 ≤ ∫ r, c13n_aux_profile α r := integral_nonneg (c13n_aux_profile_nonneg α)
  refine ⟨(2 * L + α * L + 2 * α * M) * (∫ r, c13n_aux_profile α r) + 1, by have := mul_nonneg hK0 hIP; linarith, ?_⟩
  intro φ e hφm hem hφ1 hφ2
  have hφ0 : φ 0 = 0 := by
    have := hφ1 0 (by simp); simpa using this
  have hint : ∀ δ : ℝ, Integrable (fun h => φ h * (h ^ 2 + (δ - e h) ^ 2) ^ (-α / 2)) := by
    intro δ
    refine (hP.const_mul (L + 2 * M)).mono' (by fun_prop) (Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs]
    by_cases hh : h = 0
    · subst hh; rw [hφ0, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (c13n_aux_profile_nonneg α 0)
    · exact (c13n_aux_pointwise hα0 hφ1 hφ2 δ hh).trans (c13n_aux_ite_le_profile hL hM)
  refine ⟨hint, fun d hd hd1 => ?_⟩
  have ha : 0 < |d| := abs_pos.mpr hd
  have hmaj : Integrable (fun h => (2 * L + α * L + 2 * α * M) * |d| ^ (1 - α) *
      c13n_aux_profile α (|d|⁻¹ * h)) :=
    (hP.comp_mul_left' (inv_ne_zero ha.ne')).const_mul _
  have hpw := c13n_aux_diff_pointwise (e := e) hα0 hL hM hφ1 hφ2 hd hd1
  have h2a : 0 ≤ |d| ^ (2 - α) := Real.rpow_nonneg ha.le _
  have hab : Integrable (fun h => |φ h * (h ^ 2 + (d - e h) ^ 2) ^ (-α / 2) -
        φ h * (h ^ 2 + (0 - e h) ^ 2) ^ (-α / 2)|) := ((hint d).sub (hint 0)).abs
  rw [← integral_sub (hint d) (hint 0)]
  calc |∫ h, (φ h * (h ^ 2 + (d - e h) ^ 2) ^ (-α / 2) -
        φ h * (h ^ 2 + (0 - e h) ^ 2) ^ (-α / 2))|
      ≤ ∫ h, |φ h * (h ^ 2 + (d - e h) ^ 2) ^ (-α / 2) -
        φ h * (h ^ 2 + (0 - e h) ^ 2) ^ (-α / 2)| := abs_integral_le_integral_abs
    _ ≤ ∫ h, (2 * L + α * L + 2 * α * M) * |d| ^ (1 - α) * c13n_aux_profile α (|d|⁻¹ * h) :=
        integral_mono hab hmaj (fun h => hpw h)
    _ = (2 * L + α * L + 2 * α * M) * (∫ r, c13n_aux_profile α r) * |d| ^ (2 - α) := by
        rw [integral_const_mul, Measure.integral_comp_mul_left, inv_inv, abs_abs,
          smul_eq_mul, show 2 - α = 1 + (1 - α) by ring, Real.rpow_add ha, Real.rpow_one]
        ring
    _ ≤ ((2 * L + α * L + 2 * α * M) * (∫ r, c13n_aux_profile α r) + 1) * |d| ^ (2 - α) := by
        exact mul_le_mul_of_nonneg_right (by linarith) h2a

/-- Joint continuity of the first two spatial partial derivatives of an admissible graph on
`ℝ × I`, and their identification with the slice derivatives. -/
lemma c13n_aux_partials {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    ∃ D1 D2 : ℝ × ℝ → ℝ, ContinuousOn D1 (univ ×ˢ I) ∧ ContinuousOn D2 (univ ×ˢ I) ∧
      ∀ t ∈ I, (∀ x, deriv (fun x => F x t) x = D1 (x, t)) ∧
        (∀ x, deriv (deriv (fun x => F x t)) x = D2 (x, t)) := by
  set G : ℝ × ℝ → ℝ := fun q => F q.1 q.2
  have hU : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hF.1
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G (univ ×ˢ I) := hF.2.2.1
  set D1 : ℝ × ℝ → ℝ := fun q => fderiv ℝ G q ((1 : ℝ), (0 : ℝ))
  have hD1 : ContDiffOn ℝ 1 D1 (univ ×ˢ I) :=
    (hG.fderiv_of_isOpen hU (m := 1) (by exact WithTop.coe_le_coe.mpr (le_top : ((1 + 1 : ℕ) : ℕ∞) ≤ ⊤))).clm_apply contDiffOn_const
  set D2 : ℝ × ℝ → ℝ := fun q => fderiv ℝ D1 q ((1 : ℝ), (0 : ℝ))
  have hD2 : ContinuousOn D2 (univ ×ˢ I) :=
    (hD1.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hline : ∀ x t : ℝ, HasDerivAt (fun x : ℝ => ((x, t) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) x :=
    fun x t => (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
  have h1 : ∀ t ∈ I, ∀ x, deriv (fun x => F x t) x = D1 (x, t) := by
    intro t ht x
    have hd : DifferentiableAt ℝ G (x, t) :=
      (hG.contDiffAt (hU.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt (by simp)
    exact (hd.hasFDerivAt.comp_hasDerivAt x (hline x t)).deriv
  refine ⟨D1, D2, hD1.continuousOn, hD2, fun t ht => ⟨h1 t ht, fun x => ?_⟩⟩
  have hfun : deriv (fun x => F x t) = fun x => D1 (x, t) := funext (h1 t ht)
  rw [hfun]
  have hd : DifferentiableAt ℝ D1 (x, t) :=
    (hD1.contDiffAt (hU.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt one_ne_zero
  exact (hd.hasFDerivAt.comp_hasDerivAt x (hline x t)).deriv

/-- Mean-value bounds for the normal-speed numerator `F_x(x) - F_x(x+h)`. -/
lemma c13n_aux_numer {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M L R : ℝ}
    (hM : ∀ x, |deriv f x| ≤ M) (hL : ∀ z ∈ Icc (-R - 1) (R + 1), |deriv (deriv f) z| ≤ L)
    {x : ℝ} (hx : |x| ≤ R) :
    (∀ h, |h| ≤ 1 → |deriv f x - deriv f (x + h)| ≤ L * |h|) ∧
    (∀ h, |deriv f x - deriv f (x + h)| ≤ 2 * M) := by
  refine ⟨fun h hh => ?_, fun h => ?_⟩
  · have hd : Differentiable ℝ (deriv f) := by
      have := (contDiff_succ_iff_deriv (n := 1)).mp (hf.of_le (le_of_eq (by norm_num)))
      exact this.2.2.differentiable one_ne_zero
    have hx' := abs_le.mp hx
    have hh' := abs_le.mp hh
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (s := Icc (-R - 1) (R + 1))
      (fun z _ => hd z) (fun z hz => by rw [Real.norm_eq_abs]; exact hL z hz) (convex_Icc _ _)
      (⟨by linarith, by linarith⟩ : x + h ∈ Icc (-R - 1) (R + 1))
      (⟨by linarith, by linarith⟩ : x ∈ Icc (-R - 1) (R + 1))
    simpa [Real.norm_eq_abs] using this
  · calc |deriv f x - deriv f (x + h)| ≤ |deriv f x| + |deriv f (x + h)| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM x, hM (x + h)]

lemma c13n_aux_norm_shift (α x h a b : ℝ) :
    ‖c13_pt x a - c13_pt (x + h) b‖ ^ (-α) = (h ^ 2 + (a - b) ^ 2) ^ (-α / 2) := by
  rw [c13n_aux_pt_sub, c13n_aux_norm_pt_rpow]; congr 1; ring

/-- Combine the two velocity components inside their absolutely convergent off-graph integrals:
`U₂ − F_x U₁` at `(x, F(x,t) + d)` equals `c ∫ (F_x(x) − F_x(s)) |X − γ(s)|^{-α} ds`. -/
lemma c13n_aux_combine {α : ℝ} (hα : 1 < α) (c : ℝ) {F : ℝ → ℝ → ℝ} {t M : ℝ} (hM : 0 ≤ M)
    (hd : Differentiable ℝ (fun x => F x t)) (hslope : ∀ x, |deriv (fun x => F x t) x| ≤ M)
    (x d : ℝ) (hd0 : d ≠ 0) :
    (c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 1 -
        deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 0 =
      c * ∫ s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) *
        ‖c13_pt x (F x t + d) - c13_pt s (F s t)‖ ^ (-α) := by
  obtain ⟨C, -, hC⟩ := c13_velocity_bound hα c M hM
  set X := c13_pt x (F x t + d)
  have hX : X 1 ≠ F (X 0) t := by
    simp only [X, c13n_aux_pt_one, c13n_aux_pt_zero]; intro h; apply hd0; linarith
  have hint := (hC F t hd hslope X hX).1
  set f' := deriv (fun x => F x t)
  set k : ℝ → ℝ := fun s => ‖X - c13_pt s (F s t)‖ ^ (-α)
  have hcomp : ∀ i : Fin 2, (∫ s : ℝ, k s • c13_pt 1 (f' s)) i = ∫ s : ℝ, (k s • c13_pt 1 (f' s)) i := by
    intro i
    have := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint
    simpa using this.symm
  have hint_i : ∀ i : Fin 2, Integrable (fun s : ℝ => (k s • c13_pt 1 (f' s)) i) := by
    intro i
    have := (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hint
    simpa using this
  have h0 := hint_i 0
  have h1 := hint_i 1
  simp only [PiLp.smul_apply, c13n_aux_pt_zero, c13n_aux_pt_one, smul_eq_mul, mul_one] at h0 h1
  unfold c13_graph_velocity
  simp only [hX, ↓reduceIte]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [hcomp 0, hcomp 1]
  simp only [PiLp.smul_apply, c13n_aux_pt_zero, c13n_aux_pt_one, smul_eq_mul, mul_one]
  have e1 : ∫ s : ℝ, (f' x - f' s) * k s = f' x * (∫ s, k s) - ∫ s, k s * f' s := by
    rw [← integral_const_mul, ← integral_sub (h0.const_mul (f' x)) h1]
    congr 1; funext s; ring
  change _ = c * ∫ s : ℝ, (f' x - f' s) * k s
  rw [e1]; ring

lemma c13n_aux_shift_form (α : ℝ) (F : ℝ → ℝ → ℝ) (t x δ : ℝ) :
    ∫ s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) *
        ‖c13_pt x (F x t + δ) - c13_pt s (F s t)‖ ^ (-α) =
      ∫ h : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h)) *
        (h ^ 2 + (δ - (F (x + h) t - F x t)) ^ 2) ^ (-α / 2) := by
  rw [← integral_add_left_eq_self _ x]
  congr 1; funext h
  rw [c13n_aux_norm_shift]; congr 3; ring

lemma c13n_aux_speed_form (α c : ℝ) (F : ℝ → ℝ → ℝ) (x t : ℝ) :
    c13_normal_speed α c F x t =
      c * ∫ h : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h)) *
        (h ^ 2 + (0 - (F (x + h) t - F x t)) ^ 2) ^ (-α / 2) := by
  rw [← c13n_aux_shift_form, c13_normal_speed]; simp only [add_zero]

/-- Local curvature constants on `[-R-1, R+1] × J₀`. -/
lemma c13n_aux_local_curv {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) (R : ℝ)
    {J₀ : Set ℝ} (hJI : J₀ ⊆ I) (hJ : IsCompact J₀) :
    ∃ L, 0 ≤ L ∧ ∀ x ∈ Icc (-R - 1) (R + 1), ∀ t ∈ J₀,
      |deriv (deriv (fun x => F x t)) x| ≤ L := by
  obtain ⟨D1, D2, -, hD2, hDt⟩ := c13n_aux_partials hF
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hJ).exists_bound_of_continuousOn
    (hD2.mono (prod_mono (subset_univ _) hJI))
  refine ⟨max C 0, le_max_right _ _, fun x hx t ht => ?_⟩
  rw [(hDt t (hJI ht)).2 x]
  have := hC (x, t) ⟨hx, ht⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma c13n_aux_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ 2 f :=
  hf.of_le (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))

/-- Blueprint: lem:c13_normal_speed_integrable.  The integrand of `W[F](x,t)` is absolutely
integrable for every `x` and `t ∈ I`, `W` is continuous on `ℝ × I`, and for `|x| ≤ R`, `t ∈ J₀`
the integrand at `s = x + h`, `h ≠ 0`, is bounded by `c L |h|^{1-α}` for `|h| ≤ 1` and by
`2 c M |h|^{-α}` for `|h| > 1`, where `M` is a slope bound on `ℝ × J₀` and `L` bounds `|F_xx|` on
`[-R-1, R+1] × J₀`. -/
theorem c13_normal_speed_integrable {α c : ℝ} (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    (∀ x : ℝ, ∀ t ∈ I, Integrable (fun s : ℝ =>
        (deriv (fun x => F x t) x - deriv (fun x => F x t) s) *
          ‖c13_pt x (F x t) - c13_pt s (F s t)‖ ^ (-α))) ∧
    ContinuousOn (fun p : ℝ × ℝ => c13_normal_speed α c F p.1 p.2) (univ ×ˢ I) ∧
    (∀ (R : ℝ) (J₀ : Set ℝ) (M L : ℝ), J₀ ⊆ I → IsCompact J₀ →
      (∀ x, ∀ t ∈ J₀, |deriv (fun x => F x t) x| ≤ M) →
      (∀ x ∈ Icc (-R - 1) (R + 1), ∀ t ∈ J₀, |deriv (deriv (fun x => F x t)) x| ≤ L) →
      ∀ x, |x| ≤ R → ∀ t ∈ J₀, ∀ h : ℝ, h ≠ 0 →
        |c * ((deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h)) *
            ‖c13_pt x (F x t) - c13_pt (x + h) (F (x + h) t)‖ ^ (-α))| ≤
          (if |h| ≤ 1 then c * L * |h| ^ (1 - α) else 2 * c * M * |h| ^ (-α))) := by
  have hα0 : 0 < α := by linarith
  -- the pointwise bound (third assertion)
  have hbound : ∀ (R : ℝ) (J₀ : Set ℝ) (M L : ℝ), J₀ ⊆ I → IsCompact J₀ →
      (∀ x, ∀ t ∈ J₀, |deriv (fun x => F x t) x| ≤ M) →
      (∀ x ∈ Icc (-R - 1) (R + 1), ∀ t ∈ J₀, |deriv (deriv (fun x => F x t)) x| ≤ L) →
      ∀ x, |x| ≤ R → ∀ t ∈ J₀, ∀ h : ℝ, h ≠ 0 →
        |c * ((deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h)) *
            ‖c13_pt x (F x t) - c13_pt (x + h) (F (x + h) t)‖ ^ (-α))| ≤
          (if |h| ≤ 1 then c * L * |h| ^ (1 - α) else 2 * c * M * |h| ^ (-α)) := by
    intro R J₀ M L hJI _ hM hL x hx t ht h hh
    have hf := c13n_aux_contDiff_two (c13g_aux_slice_contDiff hF (hJI ht))
    obtain ⟨hn1, hn2⟩ := c13n_aux_numer hf (fun x => hM x t ht) (fun z hz => hL z hz t ht) hx
    have hp := c13n_aux_pointwise hα0
      (φ := fun h => deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h))
      (e := fun h => F (x + h) t) hn1 hn2 (F x t) hh
    rw [c13n_aux_norm_shift, abs_mul, abs_of_pos hc]
    calc c * |(deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h)) *
          (h ^ 2 + (F x t - F (x + h) t) ^ 2) ^ (-α / 2)|
        ≤ c * (if |h| ≤ 1 then L * |h| ^ (1 - α) else 2 * M * |h| ^ (-α)) :=
          mul_le_mul_of_nonneg_left hp hc.le
      _ = _ := by split_ifs <;> ring
  -- integrability (first assertion)
  have hint : ∀ x : ℝ, ∀ t ∈ I, Integrable (fun s : ℝ =>
      (deriv (fun x => F x t) x - deriv (fun x => F x t) s) *
        ‖c13_pt x (F x t) - c13_pt s (F s t)‖ ^ (-α)) := by
    intro x t ht
    have htI : ({t} : Set ℝ) ⊆ I := by simpa using ht
    obtain ⟨M, hM0, hM⟩ := hF.2.2.2 {t} htI isCompact_singleton
    obtain ⟨L, hL0, hL⟩ := c13n_aux_local_curv hF |x| htI isCompact_singleton
    obtain ⟨K, -, hK⟩ := c13n_aux_core hα hα2 hL0 hM0
    have hf := c13n_aux_contDiff_two (c13g_aux_slice_contDiff hF ht)
    obtain ⟨hn1, hn2⟩ := c13n_aux_numer hf (fun x => hM x t rfl) (fun z hz => hL z hz t rfl) le_rfl
    have hcd := hf.continuous_deriv (by norm_num)
    have hcf := hf.continuous
    have hcore := (hK (fun h => deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h))
      (fun h => F (x + h) t - F x t)
      (by fun_prop) (by fun_prop) hn1 hn2).1 0
    refine (hcore.comp_sub_right x).congr (Eventually.of_forall fun s => ?_)
    have := c13n_aux_norm_shift α x (s - x) (F x t) (F s t)
    simp only [add_sub_cancel] at this ⊢
    rw [this]; congr 2; ring
  refine ⟨hint, ?_, hbound⟩
  -- continuity (second assertion): dominated convergence in the shifted variable
  rintro ⟨x₀, t₀⟩ hp₀
  obtain ⟨D1, D2, hD1, -, hDt⟩ := c13n_aux_partials hF
  have hU : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hF.1
  have hFc : ContinuousOn (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I) := hF.2.2.1.continuousOn
  have ht₀ : t₀ ∈ I := hp₀.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hF.1 t₀ ht₀
  have hJI : Icc (t₀ - ε / 2) (t₀ + ε / 2) ⊆ I := fun t ht => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨M, hM0, hM⟩ := hF.2.2.2 _ hJI isCompact_Icc
  obtain ⟨L, hL0, hL⟩ := c13n_aux_local_curv hF (|x₀| + 1) hJI isCompact_Icc
  have hP := c13n_aux_profile_integrable hα hα2
  set G : ℝ × ℝ → ℝ → ℝ := fun p h => c * ((D1 p - D1 (p.1 + h, p.2)) *
    ‖c13_pt p.1 (F p.1 p.2) - c13_pt (p.1 + h) (F (p.1 + h) p.2)‖ ^ (-α)) with hG
  have hN : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, t₀), |p.1| ≤ |x₀| + 1 ∧ p.2 ∈ Icc (t₀ - ε / 2) (t₀ + ε / 2) := by
    have h1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, t₀), p.1 ∈ Icc (x₀ - 1) (x₀ + 1) :=
      (continuous_fst.tendsto _).eventually (Icc_mem_nhds (by simp) (by simp))
    have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (x₀, t₀), p.2 ∈ Icc (t₀ - ε / 2) (t₀ + ε / 2) :=
      (continuous_snd.tendsto _).eventually (Icc_mem_nhds (by simp; linarith) (by simp; linarith))
    filter_upwards [h1, h2] with p hp1 hp2
    refine ⟨?_, hp2⟩
    rw [abs_le]; constructor <;> linarith [neg_abs_le x₀, le_abs_self x₀, hp1.1, hp1.2]
  have hEq : (fun p : ℝ × ℝ => ∫ h, G p h) =ᶠ[𝓝 (x₀, t₀)]
      (fun p : ℝ × ℝ => c13_normal_speed α c F p.1 p.2) := by
    filter_upwards [hN] with p hp
    have ht : p.2 ∈ I := hJI hp.2
    simp only [c13_normal_speed]
    conv_rhs => rw [← integral_const_mul, ← integral_add_left_eq_self _ p.1]
    congr 1; funext h
    simp only [G, (hDt p.2 ht).1]
  refine ContinuousAt.continuousWithinAt (ContinuousAt.congr ?_ hEq)
  have hae : ∀ᵐ h : ℝ, h ≠ 0 := by
    have : (volume : Measure ℝ) {(0 : ℝ)} = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.mpr this] with h hh
    simpa using hh
  have hlineD : ∀ p : ℝ × ℝ, p.2 ∈ I → Continuous (fun h : ℝ => D1 (p.1 + h, p.2)) := fun p hp =>
    hD1.comp_continuous (by fun_prop) (fun h => ⟨mem_univ _, hp⟩)
  have hlineF : ∀ p : ℝ × ℝ, p.2 ∈ I → Continuous (fun h : ℝ => F (p.1 + h) p.2) := fun p hp =>
    hFc.comp_continuous (f := fun h : ℝ => ((p.1 + h, p.2) : ℝ × ℝ)) (by fun_prop)
      (fun h => ⟨mem_univ _, hp⟩)
  refine continuousAt_of_dominated (bound := fun h => c * (L + 2 * M) * c13n_aux_profile α h)
    ?_ ?_ (hP.const_mul _) ?_
  · filter_upwards [hN] with p hp
    have ht : p.2 ∈ I := hJI hp.2
    have c3 : Continuous (fun h : ℝ =>
        ‖c13_pt p.1 (F p.1 p.2) - c13_pt (p.1 + h) (F (p.1 + h) p.2)‖) :=
      (continuous_const.sub (c13g_aux_continuous_pt.comp
        ((continuous_const.add continuous_id).prodMk (hlineF p ht)))).norm
    have m4 : Measurable (fun h : ℝ =>
        ‖c13_pt p.1 (F p.1 p.2) - c13_pt (p.1 + h) (F (p.1 + h) p.2)‖ ^ (-α)) :=
      c3.measurable.pow_const _
    exact (measurable_const.mul ((measurable_const.sub (hlineD p ht).measurable).mul m4)).aestronglyMeasurable
  · filter_upwards [hN] with p hp
    have ht : p.2 ∈ I := hJI hp.2
    filter_upwards [hae] with h hh
    have hb := hbound (|x₀| + 1) _ M L hJI isCompact_Icc hM hL p.1 hp.1 p.2 hp.2 h hh
    rw [Real.norm_eq_abs]
    simp only [G, ← (hDt p.2 ht).1]
    refine hb.trans ?_
    have := mul_le_mul_of_nonneg_left (c13n_aux_ite_le_profile (α := α) (h := h) hL0 hM0) hc.le
    calc (if |h| ≤ 1 then c * L * |h| ^ (1 - α) else 2 * c * M * |h| ^ (-α))
        = c * (if |h| ≤ 1 then L * |h| ^ (1 - α) else 2 * M * |h| ^ (-α)) := by
          split_ifs <;> ring
      _ ≤ c * ((L + 2 * M) * c13n_aux_profile α h) := this
      _ = c * (L + 2 * M) * c13n_aux_profile α h := by ring
  · filter_upwards [hae] with h hh
    have hU0 : (x₀, t₀) ∈ univ ×ˢ I := hp₀
    have hUh : (x₀ + h, t₀) ∈ univ ×ˢ I := ⟨mem_univ _, ht₀⟩
    have hsh : Continuous (fun p : ℝ × ℝ => ((p.1 + h, p.2) : ℝ × ℝ)) := by fun_prop
    have cD0 : ContinuousAt D1 (x₀, t₀) := hD1.continuousAt (hU.mem_nhds hU0)
    have cDh : ContinuousAt (fun p : ℝ × ℝ => D1 (p.1 + h, p.2)) (x₀, t₀) :=
      ContinuousAt.comp (f := fun p : ℝ × ℝ => ((p.1 + h, p.2) : ℝ × ℝ)) (g := D1)
        (x := (x₀, t₀)) (hD1.continuousAt (hU.mem_nhds hUh)) hsh.continuousAt
    have cF0 : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (x₀, t₀) :=
      hFc.continuousAt (hU.mem_nhds hU0)
    have cFh : ContinuousAt (fun p : ℝ × ℝ => F (p.1 + h) p.2) (x₀, t₀) :=
      ContinuousAt.comp (f := fun p : ℝ × ℝ => ((p.1 + h, p.2) : ℝ × ℝ))
        (g := fun q : ℝ × ℝ => F q.1 q.2) (x := (x₀, t₀)) (hFc.continuousAt (hU.mem_nhds hUh))
        hsh.continuousAt
    have cN : ContinuousAt (fun p : ℝ × ℝ =>
        ‖c13_pt p.1 (F p.1 p.2) - c13_pt (p.1 + h) (F (p.1 + h) p.2)‖) (x₀, t₀) := by
      refine ContinuousAt.norm (ContinuousAt.sub ?_ ?_)
      · exact c13g_aux_continuous_pt.continuousAt.comp (continuousAt_fst.prodMk cF0)
      · exact c13g_aux_continuous_pt.continuousAt.comp
          ((continuousAt_fst.add continuousAt_const).prodMk cFh)
    have hne : ‖c13_pt x₀ (F x₀ t₀) - c13_pt (x₀ + h) (F (x₀ + h) t₀)‖ ≠ 0 := by
      have := c13n_aux_abs_le_norm_pt (x₀ - (x₀ + h)) (F x₀ t₀ - F (x₀ + h) t₀)
      rw [← c13n_aux_pt_sub] at this
      have h0 : 0 < |x₀ - (x₀ + h)| := by
        rw [show x₀ - (x₀ + h) = -h by ring, abs_neg]; exact abs_pos.mpr hh
      exact (lt_of_lt_of_le h0 this).ne'
    exact continuousAt_const.mul ((cD0.sub cDh).mul (cN.rpow_const (Or.inl hne)))

/-- Blueprint: lem:c13_normal_trace.  For `d ≠ 0` let
`W_d(x,t) = U₂(x, F(x,t)+d, t) − F_x(x,t) U₁(x, F(x,t)+d, t)` (off-graph values only).
For every `R > 0` and compact `J₀ ⊆ I` there is `C > 0` with
`|W_d(x,t) − W(x,t)| ≤ C |d|^{2-α}` for `|x| ≤ R`, `t ∈ J₀`, `0 < |d| ≤ 1`.
Consequently both vertical normal traces exist and equal `W`. -/
theorem c13_normal_trace {α c : ℝ} (hα : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    (∀ R : ℝ, 0 < R → ∀ J₀ ⊆ I, IsCompact J₀ → ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, |x| ≤ R → ∀ t ∈ J₀, ∀ d : ℝ, d ≠ 0 → |d| ≤ 1 →
        |((c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 1 -
            deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 0) -
          c13_normal_speed α c F x t| ≤ C * |d| ^ (2 - α)) ∧
    (∀ x : ℝ, ∀ t ∈ I, Tendsto (fun d : ℝ =>
        (c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 1 -
          deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 0)
        (𝓝[≠] 0) (𝓝 (c13_normal_speed α c F x t))) := by
  have hA : ∀ R : ℝ, 0 < R → ∀ J₀ ⊆ I, IsCompact J₀ → ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, |x| ≤ R → ∀ t ∈ J₀, ∀ d : ℝ, d ≠ 0 → |d| ≤ 1 →
        |((c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 1 -
            deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + d)) t) 0) -
          c13_normal_speed α c F x t| ≤ C * |d| ^ (2 - α) := by
    intro R _ J₀ hJI hJ
    obtain ⟨M, hM0, hM⟩ := hF.2.2.2 J₀ hJI hJ
    obtain ⟨L, hL0, hL⟩ := c13n_aux_local_curv hF R hJI hJ
    obtain ⟨K, hK0, hK⟩ := c13n_aux_core hα hα2 hL0 hM0
    refine ⟨c * K, mul_pos hc hK0, fun x hx t ht d hd hd1 => ?_⟩
    have hf := c13n_aux_contDiff_two (c13g_aux_slice_contDiff hF (hJI ht))
    obtain ⟨hn1, hn2⟩ := c13n_aux_numer hf (fun x => hM x t ht) (fun z hz => hL z hz t ht) hx
    have hcd := hf.continuous_deriv (by norm_num)
    have hcf := hf.continuous
    have hk := (hK (fun h => deriv (fun x => F x t) x - deriv (fun x => F x t) (x + h))
      (fun h => F (x + h) t - F x t) (by fun_prop) (by fun_prop) hn1 hn2).2 d hd hd1
    rw [c13n_aux_combine hα c hM0 (hf.differentiable (by norm_num)) (fun x => hM x t ht) x d hd,
      c13n_aux_shift_form, c13n_aux_speed_form, ← mul_sub, abs_mul, abs_of_pos hc, mul_assoc]
    exact mul_le_mul_of_nonneg_left hk hc.le
  refine ⟨hA, fun x t ht => ?_⟩
  obtain ⟨C, -, hC⟩ := hA (|x| + 1) (by positivity) {t} (by simpa using ht) isCompact_singleton
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun d : ℝ => C * |d| ^ (2 - α)) (𝓝[≠] 0) (𝓝 0) := by
    have h0 : Tendsto (fun d : ℝ => C * |d| ^ (2 - α)) (𝓝 0) (𝓝 (C * |(0:ℝ)| ^ (2 - α))) :=
      ((continuous_abs.rpow_const (fun _ => Or.inr (by linarith))).tendsto 0).const_mul C
    rw [abs_zero, Real.zero_rpow (by linarith), mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun d => norm_nonneg _) ?_ hlim
  have hball : ∀ᶠ d in 𝓝[≠] (0:ℝ), d ∈ Metric.closedBall (0:ℝ) 1 :=
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 one_pos)
  filter_upwards [self_mem_nhdsWithin, hball] with d hd hd1
  rw [Real.norm_eq_abs]
  exact hC x (by linarith [abs_nonneg x]) t rfl d hd (by simpa using hd1)

lemma c13n_aux_flat_scaling {α : ℝ} (x d : ℝ) (hd : d ≠ 0) :
    ∫ s : ℝ, ((x - s) ^ 2 + d ^ 2) ^ (-α / 2) =
      |d| ^ (1 - α) * ∫ s : ℝ, (1 + s ^ 2) ^ (-α / 2) := by
  have had : 0 < |d| := abs_pos.mpr hd
  rw [integral_sub_left_eq_self (fun s => (s ^ 2 + d ^ 2) ^ (-α / 2)) volume x]
  have h2 := Measure.integral_comp_mul_left (fun s : ℝ => (s ^ 2 + d ^ 2) ^ (-α / 2)) (|d|)
  have h3 : ∀ r : ℝ, ((|d| * r) ^ 2 + d ^ 2) ^ (-α / 2) = |d| ^ (-α) * (1 + r ^ 2) ^ (-α / 2) := by
    intro r
    have : (|d| * r) ^ 2 + d ^ 2 = |d| ^ (2:ℝ) * (1 + r ^ 2) := by
      rw [Real.rpow_two, mul_pow, sq_abs]; ring
    rw [this, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul had.le]
    ring_nf
  simp only [h3] at h2
  rw [integral_const_mul, smul_eq_mul, abs_inv, abs_abs] at h2
  have : ∫ s : ℝ, (s ^ 2 + d ^ 2) ^ (-α / 2) = |d| * (|d| ^ (-α) * ∫ s : ℝ, (1 + s ^ 2) ^ (-α / 2)) := by
    rw [h2]; field_simp
  rw [this, ← mul_assoc, show 1 - α = 1 + -α by ring, Real.rpow_add had, Real.rpow_one]

/-- Blueprint: lem:c13_flat_graph_check.  For the flat graph `F = 0` and `d ≠ 0`,
`U(x,d) = -c C_α |d|^{1-α} (1,0)` with `C_α = ∫ (1+s²)^{-α/2} ds ∈ (0,∞)`, and `W = 0`.
The tangential velocity diverges in magnitude at the boundary, while any modification of `U` on the
null graph `{y = 0}` is a.e. equal to `U` and has the same pairings with every vector test. -/
theorem c13_flat_graph_check {α c : ℝ} (hα : 1 < α) (_hα2 : α < 2) (hc : 0 < c) :
    Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-α / 2)) ∧
    0 < ∫ s : ℝ, (1 + s ^ 2) ^ (-α / 2) ∧
    (∀ x d t : ℝ, d ≠ 0 →
      c13_graph_velocity α c (fun _ _ => 0) (c13_pt x d) t =
        (-c * (∫ s : ℝ, (1 + s ^ 2) ^ (-α / 2)) * |d| ^ (1 - α)) • c13_pt 1 0) ∧
    (∀ x t : ℝ, c13_normal_speed α c (fun _ _ => 0) x t = 0) ∧
    (∀ x t : ℝ, Tendsto (fun d : ℝ => ‖c13_graph_velocity α c (fun _ _ => 0) (c13_pt x d) t‖)
      (𝓝[≠] 0) atTop) ∧
    (∀ t : ℝ, ∀ V : c13_E → c13_E,
      (∀ X : c13_E, X 1 ≠ 0 → V X = c13_graph_velocity α c (fun _ _ => 0) X t) →
      V =ᵐ[volume] (fun X => c13_graph_velocity α c (fun _ _ => 0) X t) ∧
      ∀ Φ : c13_E → c13_E, ∫ X, inner ℝ (V X) (Φ X) =
        ∫ X, inner ℝ (c13_graph_velocity α c (fun _ _ => 0) X t) (Φ X)) := by
  have hint : Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-α / 2)) := by
    have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := α)
      (by simp; linarith)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hpos : 0 < ∫ s : ℝ, (1 + s ^ 2) ^ (-α / 2) := by
    rw [integral_pos_iff_support_of_nonneg (fun s => by positivity) hint]
    have : Function.support (fun s : ℝ => (1 + s ^ 2) ^ (-α / 2)) = univ := by
      ext s; simp only [Function.mem_support, mem_univ, iff_true]; positivity
    rw [this]; simp
  have hU : ∀ x d t : ℝ, d ≠ 0 →
      c13_graph_velocity α c (fun _ _ => 0) (c13_pt x d) t =
        (-c * (∫ s : ℝ, (1 + s ^ 2) ^ (-α / 2)) * |d| ^ (1 - α)) • c13_pt 1 0 := by
    intro x d t hd
    unfold c13_graph_velocity
    simp only [show ¬ (c13_pt x d) 1 = (0:ℝ) by simpa [c13n_aux_pt_one] using hd, ↓reduceIte]
    simp only [deriv_const, c13n_aux_pt_sub, c13n_aux_norm_pt_rpow, sub_zero]
    rw [integral_smul_const, c13n_aux_flat_scaling x d hd, smul_smul]
    congr 1; ring_nf
  refine ⟨hint, hpos, hU, ?_, ?_, ?_⟩
  · intro x t; simp [c13_normal_speed]
  · intro x t
    have hcont : Tendsto (fun d : ℝ => |d|) (𝓝[≠] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_abs.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0:ℝ)}ᶜ))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with d hd
        exact abs_pos.mpr hd
    have hlim := ((tendsto_rpow_neg_nhdsGT_zero (y := 1 - α) (by linarith)).comp hcont).const_mul_atTop
      (mul_pos hc hpos)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    have hp := Real.rpow_pos_of_pos (abs_pos.mpr hd) (1 - α)
    have hneg : (-c * (∫ s : ℝ, (1 + s ^ 2) ^ (-α / 2))) * |d| ^ (1 - α) < 0 := by
      nlinarith [mul_pos (mul_pos hc hpos) hp]
    rw [hU x d t hd, norm_smul, c13n_aux_norm_pt, Real.norm_eq_abs, abs_of_neg hneg]
    simp only [Function.comp]
    norm_num
  · intro t V hV
    have hnull : (volume : Measure c13_E) {X : c13_E | X 1 = 0} = 0 := by
      have := Measure.addHaar_submodule (volume : Measure c13_E)
        (LinearMap.ker (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).toLinearMap) ?_
      · convert this using 2
        ext X; simp
      · intro h
        have : (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) ∈
            LinearMap.ker (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).toLinearMap := by
          rw [h]; trivial
        simp at this
    have hae : V =ᵐ[volume] (fun X => c13_graph_velocity α c (fun _ _ => 0) X t) := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun X hX => ?_) hnull
      by_contra h
      exact hX (hV X h)
    refine ⟨hae, fun Φ => integral_congr_ae ?_⟩
    filter_upwards [hae] with X hX
    rw [hX]

end GSQG
