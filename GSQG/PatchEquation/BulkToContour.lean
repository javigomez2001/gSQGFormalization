import GSQG.PatchEquation.Velocity

/-!
# Beyond the paper (2D patch derivation): truncation boundary error, bulk-to-contour identity, principal value
(blueprint ch. 13)

Helpers are named `c13c_aux_*`.

Conventions.  A vector test is `Φ : c13_E → c13_E` with `ContDiff ℝ (⊤ : ℕ∞) Φ` and
`HasCompactSupport Φ`.  Its test potential is written out explicitly as
`A_Φ(Y) = ∫ X, c13_potential_kernel α c (X - Y) • Φ X` and the flux field is `Q = J A_Φ`
(`c13_rotation`), so `Q 0 = -(A_Φ 1)` and `Q 1 = A_Φ 0`.  The density is
`θ_F = (c13_patch F t).indicator 1`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### Pure helpers -/

theorem c13c_aux_norm_pt (x y : ℝ) : ‖c13_pt x y‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  simp [c13_pt, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem c13c_aux_abs_le_norm_pt (x y : ℝ) : |x| ≤ ‖c13_pt x y‖ ∧ |y| ≤ ‖c13_pt x y‖ := by
  rw [c13c_aux_norm_pt]
  exact ⟨Real.abs_le_sqrt (by nlinarith [sq_nonneg y]), Real.abs_le_sqrt (by nlinarith [sq_nonneg x])⟩

theorem c13c_aux_abs_apply_le (v : c13_E) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i; simpa using this

theorem c13c_aux_rotation_apply_le (v : c13_E) (i : Fin 2) : |c13_rotation v i| ≤ ‖v‖ := by
  fin_cases i
  · simpa [c13_rotation] using c13c_aux_abs_apply_le v 1
  · simpa [c13_rotation] using c13c_aux_abs_apply_le v 0

/-- Far-field decay of the test potential (pure helper). -/
theorem c13c_aux_potential_decay {α c L : ℝ} (hα : 0 < α) (hL : 0 < L) (Φ : c13_E → c13_E)
    (hΦi : Integrable Φ) (hsupp : ∀ X, L < ‖X‖ → Φ X = 0) (Y : c13_E) (hY : 2 * L ≤ ‖Y‖) :
    ‖∫ X, c13_potential_kernel α c (X - Y) • Φ X‖ ≤
      |c| * 2 ^ α * ‖Y‖ ^ (-α) * ∫ X, ‖Φ X‖ := by
  have hYpos : 0 < ‖Y‖ := by linarith
  calc ‖∫ X, c13_potential_kernel α c (X - Y) • Φ X‖
      ≤ ∫ X, ‖c13_potential_kernel α c (X - Y) • Φ X‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ X, (|c| * 2 ^ α * ‖Y‖ ^ (-α)) * ‖Φ X‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun X => norm_nonneg _)
          (hΦi.norm.const_mul _) (Eventually.of_forall fun X => ?_)
        simp only [norm_smul, Real.norm_eq_abs]
        by_cases hX : Φ X = 0
        · simp [hX]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hXL : ‖X‖ ≤ L := by
          by_contra h; exact hX (hsupp X (lt_of_not_ge h))
        have hd : ‖Y‖ / 2 ≤ ‖X - Y‖ := by
          have := norm_sub_norm_le Y X
          rw [norm_sub_rev] at this; linarith
        have hne : X - Y ≠ 0 := by
          intro h; rw [h, norm_zero] at hd; linarith
        simp only [c13_potential_kernel, hne, ite_false, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc ‖X - Y‖ ^ (-α) ≤ (‖Y‖ / 2) ^ (-α) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hd (by linarith)
          _ = 2 ^ α * ‖Y‖ ^ (-α) := by
              rw [Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
              field_simp
    _ = |c| * 2 ^ α * ‖Y‖ ^ (-α) * ∫ X, ‖Φ X‖ := integral_const_mul _ _

/-- Support radius of a compactly supported field (pure helper). -/
theorem c13c_aux_support_radius (Φ : c13_E → c13_E) (hΦc : HasCompactSupport Φ) :
    ∃ L : ℝ, 1 ≤ L ∧ tsupport Φ ⊆ Metric.closedBall 0 L ∧ ∀ X, L < ‖X‖ → Φ X = 0 := by
  obtain ⟨r, hr⟩ := hΦc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max r 1, le_max_right _ _, hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _)),
    fun X hX => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  have := hr hm
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left r 1]

/-- Blueprint: lem:c13_truncation_boundary_error.  For a fixed-time graph `F` with `|F'| ≤ M`,
`H_R = |F 0| + (M+1)R + 1` and the domain `D_R = {|x| < R, -H_R < y < F x}`, the three
artificial-boundary terms of the finite graph flux formula (bottom, right wall, left wall,
with the signs of `lem:c13_finite_graph_flux`) for `Q = J A_Φ` are `O(R^{1-α})`, with constant
and threshold independent of `R`. -/
theorem c13_truncation_boundary_error {α c M : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hM : ∀ x, |deriv F x| ≤ M)
    (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ C R₀ : ℝ, 0 < C ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      |(-(∫ s in (-R)..R,
            c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt s (-(|F 0| + (M + 1) * R + 1)))
              • Φ X) 1))
        + (∫ y in (-(|F 0| + (M + 1) * R + 1))..(F R),
            c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt R y) • Φ X) 0)
        - (∫ y in (-(|F 0| + (M + 1) * R + 1))..(F (-R)),
            c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt (-R) y) • Φ X) 0)|
        ≤ C * R ^ (1 - α) := by
  obtain ⟨L, hL1, -, hsupp⟩ := c13c_aux_support_radius Φ hΦc
  have hΦi : Integrable Φ := hΦ.continuous.integrable_of_hasCompactSupport hΦc
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set N := ∫ X, ‖Φ X‖
  have hN : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  set K := |c| * 2 ^ α * N + 1 with hK
  have hK0 : 0 < K := by positivity
  -- pointwise bound on any point of norm ≥ R ≥ 2L
  have hpt : ∀ R : ℝ, 2 * L ≤ R → ∀ Y : c13_E, R ≤ ‖Y‖ → ∀ i : Fin 2,
      ‖c13_rotation (∫ X, c13_potential_kernel α c (X - Y) • Φ X) i‖ ≤ K * R ^ (-α) := by
    intro R hR Y hY i
    have hRpos : 0 < R := by linarith
    rw [Real.norm_eq_abs]
    refine (c13c_aux_rotation_apply_le _ i).trans ?_
    refine (c13c_aux_potential_decay (by linarith) (by linarith) Φ hΦi hsupp Y (hR.trans hY)).trans ?_
    have h1 : ‖Y‖ ^ (-α) ≤ R ^ (-α) := Real.rpow_le_rpow_of_nonpos hRpos hY (by linarith)
    have h2 : 0 ≤ |c| * 2 ^ α := by positivity
    calc |c| * 2 ^ α * ‖Y‖ ^ (-α) * N ≤ |c| * 2 ^ α * R ^ (-α) * N := by gcongr
      _ = (|c| * 2 ^ α * N) * R ^ (-α) := by ring
      _ ≤ K * R ^ (-α) := by gcongr; linarith
  have hlip : ∀ x, |F x - F 0| ≤ M * |x| := by
    intro x
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := univ) (x := 0) (y := x)
      (fun z _ => (hF.differentiable (by norm_num)).differentiableAt) (fun z _ => hM z)
      convex_univ (mem_univ _) (mem_univ _)
    simpa using this
  refine ⟨K * (4 * |F 0| + 4 * M + 6), max 1 (2 * L), by positivity, by positivity, ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRL : 2 * L ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := by linarith
  set H := |F 0| + (M + 1) * R + 1 with hH
  have hHR : R ≤ H := by nlinarith [abs_nonneg (F 0)]
  -- bottom
  have hb : ‖∫ s in (-R)..R, c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt s (-H))
      • Φ X) 1‖ ≤ K * R ^ (-α) * |R - -R| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hpt R hRL _ ?_ 1
    have := (c13c_aux_abs_le_norm_pt s (-H)).2
    rw [abs_neg, abs_of_pos (by linarith)] at this; linarith
  have hw : ∀ x : ℝ, |x| = R → ‖∫ y in (-H)..(F x),
      c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt x y) • Φ X) 0‖ ≤
        K * R ^ (-α) * |F x - -H| := by
    intro x hx
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun y _ => hpt R hRL _ ?_ 0
    have := (c13c_aux_abs_le_norm_pt x y).1
    linarith
  have hlen : ∀ x : ℝ, |x| = R → |F x - -H| ≤ 2 * |F 0| + (2 * M + 1) * R + 1 := by
    intro x hx
    have h1 := hlip x
    rw [hx] at h1
    have h2 : |F x| ≤ |F 0| + M * R := by
      have := abs_sub_abs_le_abs_sub (F x) (F 0); linarith
    calc |F x - -H| ≤ |F x| + |H| := by
          rw [sub_neg_eq_add]; exact abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos (show 0 < H by linarith)]; rw [hH]; nlinarith
  have hwR := hw R (abs_of_pos hRpos)
  have hwL := hw (-R) (by rw [abs_neg, abs_of_pos hRpos])
  have hlR := hlen R (abs_of_pos hRpos)
  have hlL := hlen (-R) (by rw [abs_neg, abs_of_pos hRpos])
  rw [Real.norm_eq_abs] at hb hwR hwL
  have hKR : 0 ≤ K * R ^ (-α) := by positivity
  have hsplit : R ^ (1 - α) = R * R ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hRpos, Real.rpow_one]
  have hRR : |R - -R| = 2 * R := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
  rw [hRR] at hb
  calc _ ≤ |∫ s in (-R)..R, c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt s (-H))
              • Φ X) 1| +
          |∫ y in (-H)..(F R), c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt R y) • Φ X) 0| +
          |∫ y in (-H)..(F (-R)),
              c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt (-R) y) • Φ X) 0| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ K * R ^ (-α) * (2 * R) + K * R ^ (-α) * (2 * |F 0| + (2 * M + 1) * R + 1) +
          K * R ^ (-α) * (2 * |F 0| + (2 * M + 1) * R + 1) := by
        gcongr
        · exact hwR.trans (mul_le_mul_of_nonneg_left hlR hKR)
        · exact hwL.trans (mul_le_mul_of_nonneg_left hlL hKR)
    _ ≤ K * R ^ (-α) * (R * (4 * |F 0| + 4 * M + 6)) := by
        rw [← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hKR
        nlinarith [abs_nonneg (F 0)]
    _ = K * (4 * |F 0| + 4 * M + 6) * R ^ (1 - α) := by rw [hsplit]; ring

/-! ### Helpers for the bulk-to-contour identity -/

/-- The rotation `J` as a continuous linear map (pure helper). -/
def c13c_aux_rotL : c13_E →L[ℝ] c13_E :=
  LinearMap.toContinuousLinearMap
    { toFun := c13_rotation
      map_add' := fun a b => by ext i; fin_cases i <;> simp [c13_rotation]; ring
      map_smul' := fun r a => by ext i; fin_cases i <;> simp [c13_rotation] }

theorem c13c_aux_rotL_apply (v : c13_E) : c13c_aux_rotL v = c13_rotation v := rfl

theorem c13c_aux_inner_eq (a b : c13_E) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem c13c_aux_pt_apply0 (x y : ℝ) : c13_pt x y 0 = x := by simp [c13_pt]
theorem c13c_aux_pt_apply1 (x y : ℝ) : c13_pt x y 1 = y := by simp [c13_pt]

theorem c13c_aux_pt_single0 : (c13_pt 1 0 : c13_E) = EuclideanSpace.single 0 1 := by
  ext i; fin_cases i <;> simp [c13_pt]
theorem c13c_aux_pt_single1 : (c13_pt 0 1 : c13_E) = EuclideanSpace.single 1 1 := by
  ext i; fin_cases i <;> simp [c13_pt]

theorem c13c_aux_continuous_pt {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun s => c13_pt (f s) (g s) := by unfold c13_pt; fun_prop

theorem c13c_aux_norm_tau_le {m M : ℝ} (hm : |m| ≤ M) : ‖c13_pt 1 m‖ ≤ 1 + M := by
  rw [c13c_aux_norm_pt, Real.sqrt_le_left (by linarith [abs_nonneg m])]
  nlinarith [abs_nonneg m, sq_abs m]

/-- Fixed-time slice of an admissible graph: smooth, with a global slope bound (pure helper). -/
theorem c13c_aux_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t : ℝ}
    (ht : t ∈ I) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => F x t) ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv (fun x => F x t) x| ≤ M := by
  obtain ⟨-, -, hsm, hsl⟩ := hF
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x, t)) := contDiff_id.prodMk contDiff_const
    have := hsm.comp (s := univ) h1.contDiffOn (fun x _ => ⟨mem_univ _, ht⟩)
    exact contDiffOn_univ.mp this
  · obtain ⟨M, hM0, hM⟩ := hsl {t} (by simpa using ht) isCompact_singleton
    exact ⟨M, hM0, fun x => hM x t rfl⟩

/-- Global decay `‖A_Φ(Y)‖ ≤ K (1 + |Y|)^{-α}` for a continuous test potential (pure helper). -/
theorem c13c_aux_potential_global_decay {α c : ℝ} (hα : 0 < α) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hA : Continuous fun Y : c13_E => ∫ X, c13_potential_kernel α c (X - Y) • Φ X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : c13_E,
      ‖∫ X, c13_potential_kernel α c (X - Y) • Φ X‖ ≤ K * (1 + ‖Y‖) ^ (-α) := by
  obtain ⟨L, hL1, -, hsupp⟩ := c13c_aux_support_radius Φ hΦc
  have hΦi : Integrable Φ := hΦ.continuous.integrable_of_hasCompactSupport hΦc
  set N := ∫ X, ‖Φ X‖
  have hN : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨K1, hK1⟩ := (isCompact_closedBall (0 : c13_E) (2 * L)).exists_bound_of_continuousOn
    hA.continuousOn
  refine ⟨|K1| * (1 + 2 * L) ^ α + |c| * 2 ^ α * N * 2 ^ α, by positivity, fun Y => ?_⟩
  have hp : 0 < 1 + ‖Y‖ := by positivity
  by_cases hY : ‖Y‖ ≤ 2 * L
  · have h1 := hK1 Y (by simpa using hY)
    have h2 : (1 + 2 * L) ^ α * (1 + ‖Y‖) ^ (-α) ≥ 1 := by
      have : (1 + 2 * L) ^ (-α) ≤ (1 + ‖Y‖) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos hp (by linarith) (by linarith)
      have h3 : (1 + 2 * L) ^ α * (1 + 2 * L) ^ (-α) = 1 := by
        rw [← Real.rpow_add (by linarith)]; simp
      calc (1:ℝ) = (1 + 2 * L) ^ α * (1 + 2 * L) ^ (-α) := h3.symm
        _ ≤ _ := by gcongr
    have h4 : 0 ≤ |c| * 2 ^ α * N * 2 ^ α * (1 + ‖Y‖) ^ (-α) := by positivity
    calc _ ≤ |K1| := h1.trans (le_abs_self _)
      _ ≤ |K1| * ((1 + 2 * L) ^ α * (1 + ‖Y‖) ^ (-α)) := le_mul_of_one_le_right (abs_nonneg _) h2
      _ ≤ _ := by rw [add_mul]; linarith [mul_assoc |K1| ((1 + 2 * L) ^ α) ((1 + ‖Y‖) ^ (-α))]
  · push Not at hY
    have h1 := c13c_aux_potential_decay (c := c) hα (by linarith) Φ hΦi hsupp Y hY.le
    have hYp : 0 < ‖Y‖ := by linarith
    have h2 : ‖Y‖ ^ (-α) ≤ 2 ^ α * (1 + ‖Y‖) ^ (-α) := by
      have : (1 + ‖Y‖) / 2 ≤ ‖Y‖ := by linarith
      calc ‖Y‖ ^ (-α) ≤ ((1 + ‖Y‖) / 2) ^ (-α) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) this (by linarith)
        _ = 2 ^ α * (1 + ‖Y‖) ^ (-α) := by
            rw [Real.div_rpow hp.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
            field_simp
    have h5 : 0 ≤ |K1| * (1 + 2 * L) ^ α * (1 + ‖Y‖) ^ (-α) := by positivity
    calc _ ≤ |c| * 2 ^ α * ‖Y‖ ^ (-α) * N := h1
      _ ≤ |c| * 2 ^ α * (2 ^ α * (1 + ‖Y‖) ^ (-α)) * N := by gcongr
      _ ≤ _ := by rw [add_mul]; nlinarith

/-- Integrability of the contour integrand `s ↦ A_Φ(γ(s)) · τ(s)` (pure helper, modulo the
continuity hypothesis on `A_Φ`). -/
theorem c13c_aux_contour_integrable {α c M : ℝ} (hα1 : 1 < α) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hM : ∀ x, |deriv f x| ≤ M) (Φ : c13_E → c13_E)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hA : Continuous fun Y : c13_E => ∫ X, c13_potential_kernel α c (X - Y) • Φ X) :
    Integrable (fun s : ℝ =>
      inner ℝ (∫ X, c13_potential_kernel α c (X - c13_pt s (f s)) • Φ X) (c13_pt 1 (deriv f s))) := by
  obtain ⟨K, hK0, hK⟩ := c13c_aux_potential_global_decay (by linarith) Φ hΦ hΦc hA
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hcont : Continuous fun s : ℝ =>
      inner ℝ (∫ X, c13_potential_kernel α c (X - c13_pt s (f s)) • Φ X) (c13_pt 1 (deriv f s)) := by
    have h1 := hA.comp (c13c_aux_continuous_pt continuous_id hf.continuous)
    have h2 := c13c_aux_continuous_pt (f := fun _ => (1:ℝ)) continuous_const (hf.continuous_deriv le_rfl)
    exact h1.inner h2
  have hint : Integrable (fun s : ℝ => (K * (1 + M)) * (1 + ‖s‖) ^ (-α)) :=
    (integrable_one_add_norm (by simpa using hα1)).const_mul _
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 := hK (c13_pt s (f s))
  have h2 : (1 + ‖c13_pt s (f s)‖) ^ (-α) ≤ (1 + ‖s‖) ^ (-α) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    have := (c13c_aux_abs_le_norm_pt s (f s)).1
    rw [Real.norm_eq_abs]; linarith
  have h3 := c13c_aux_norm_tau_le (hM s)
  calc _ ≤ (K * (1 + ‖c13_pt s (f s)‖) ^ (-α)) * (1 + M) := by gcongr
    _ ≤ (K * (1 + ‖s‖) ^ (-α)) * (1 + M) := by gcongr
    _ = _ := by ring


theorem c13c_aux_bulk_flux_identity {α c M : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hM : ∀ x, |deriv f x| ≤ M)
    (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    (∫ Y, {X : c13_E | X 1 < f (X 0)}.indicator (fun _ => (1 : ℝ)) Y * c13_adjoint α c Φ Y) =
      -(∫ s : ℝ, inner ℝ (∫ X, c13_potential_kernel α c (X - c13_pt s (f s)) • Φ X)
        (c13_pt 1 (deriv f s))) := by
  obtain ⟨Cp, -, hTP, -⟩ := c13_test_potential hα1 hα2 c
  obtain ⟨-, hAC1, hadj, -⟩ := hTP Φ hΦ hΦc
  obtain ⟨Cad, -, hAD⟩ := c13_adjoint_integrable hα1 hα2 c
  have hBint : Integrable (c13_adjoint α c Φ) := (hAD Φ hΦ hΦc).2.2.1
  set A : c13_E → c13_E := fun Y => ∫ X, c13_potential_kernel α c (X - Y) • Φ X with hAdef
  set Q : c13_E → c13_E := fun W => c13_rotation (A W) with hQdef
  have hQ : ContDiff ℝ 1 Q := c13c_aux_rotL.contDiff.comp hAC1
  have hdiv : ∀ Y, c13_adjoint α c Φ Y = -c13g_aux_div Q Y := by
    intro Y; rw [hadj Y, c13g_aux_div, c13c_aux_pt_single0, c13c_aux_pt_single1]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hlip : ∀ x, |f x - f 0| ≤ M * |x| := by
    intro x
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := univ) (x := 0) (y := x)
      (fun z _ => (hf.differentiable (by norm_num)).differentiableAt) (fun z _ => hM z)
      convex_univ (mem_univ _) (mem_univ _)
    simpa using this
  obtain ⟨Ct, R₀, -, -, htr⟩ := c13_truncation_boundary_error hα1 hα2 f hf hM Φ hΦ hΦc
  set Ω : Set c13_E := {X : c13_E | X 1 < f (X 0)} with hΩ
  have hc0 : Continuous fun X : c13_E => X 0 := by fun_prop
  have hc1 : Continuous fun X : c13_E => X 1 := by fun_prop
  have hΩm : MeasurableSet Ω :=
    (isOpen_lt hc1 (hf.continuous.comp hc0)).measurableSet
  set D : ℝ → Set c13_E := fun R =>
    {X | |X 0| < R ∧ -(|f 0| + (M + 1) * R + 1) < X 1 ∧ X 1 < f (X 0)} with hDdef
  have hDm : ∀ R, MeasurableSet (D R) := fun R =>
    ((isOpen_lt (continuous_abs.comp hc0) continuous_const).inter
      ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 (hf.continuous.comp hc0)))).measurableSet
  have hDmono : Monotone D := by
    intro R R' hRR' X ⟨h1, h2, h3⟩
    exact ⟨h1.trans_le hRR', lt_of_le_of_lt (by nlinarith) h2, h3⟩
  have hDU : (⋃ R, D R) = Ω := by
    ext X; simp only [mem_iUnion, hDdef, mem_ofPred_eq, hΩ]
    constructor
    · rintro ⟨R, -, -, h⟩; exact h
    · intro h
      refine ⟨|X 0| + |X 1| + 1, by linarith [abs_nonneg (X 1)], ?_, h⟩
      have := neg_abs_le (X 1)
      nlinarith [abs_nonneg (f 0), abs_nonneg (X 0), abs_nonneg (X 1)]
  have hlim1 : Tendsto (fun R => ∫ X in D R, c13_adjoint α c Φ X) atTop
      (𝓝 (∫ X in Ω, c13_adjoint α c Φ X)) := by
    rw [← hDU]; exact tendsto_setIntegral_of_monotone hDm hDmono hBint.integrableOn
  have hcint := c13c_aux_contour_integrable hα1 f hf hM Φ hΦ hΦc hAC1.continuous
  have hlim2 : Tendsto (fun R : ℝ => ∫ s in (-R)..R,
      inner ℝ (A (c13_pt s (f s))) (c13_pt 1 (deriv f s))) atTop
      (𝓝 (∫ s, inner ℝ (A (c13_pt s (f s))) (c13_pt 1 (deriv f s)))) :=
    intervalIntegral_tendsto_integral hcint tendsto_neg_atTop_atBot tendsto_id
  set T : ℝ → ℝ := fun R =>
      (-(∫ s in (-R)..R,
            c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt s (-(|f 0| + (M + 1) * R + 1)))
              • Φ X) 1))
        + (∫ y in (-(|f 0| + (M + 1) * R + 1))..(f R),
            c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt R y) • Φ X) 0)
        - (∫ y in (-(|f 0| + (M + 1) * R + 1))..(f (-R)),
            c13_rotation (∫ X, c13_potential_kernel α c (X - c13_pt (-R) y) • Φ X) 0) with hT
  have hlim3 : Tendsto T atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ => Ct * R ^ (1 - α)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := α - 1) (by linarith)).const_mul Ct
      simpa [neg_sub] using this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop R₀] with R hR
    rw [Real.norm_eq_abs]; exact htr R hR
  have heq : ∀ᶠ R in atTop, (∫ X in D R, c13_adjoint α c Φ X) =
      -(∫ s in (-R)..R, inner ℝ (A (c13_pt s (f s))) (c13_pt 1 (deriv f s))) - T R := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    have hRpos : 0 < R := by linarith
    have hH : 0 < |f 0| + (M + 1) * R + 1 := by positivity
    have hFH : ∀ s ∈ Icc (-R) R, -(|f 0| + (M + 1) * R + 1) < f s := by
      intro s hs
      have h1 := hlip s
      have h2 : |s| ≤ R := abs_le.mpr hs
      have h3 := neg_abs_le (f 0)
      have h4 : -(M * R) ≤ f s - f 0 := by
        have := neg_abs_le (f s - f 0); nlinarith
      nlinarith
    have hflux := (c13_finite_graph_flux hRpos hH hf hFH (Q := Q)
      ⟨univ, isOpen_univ, subset_univ _, hQ.contDiffOn⟩).2.2.2.2.2
    have hG : (∫ s in (-R)..R, (Q (c13_pt s (f s)) 1 - deriv f s * Q (c13_pt s (f s)) 0)) =
        ∫ s in (-R)..R, inner ℝ (A (c13_pt s (f s))) (c13_pt 1 (deriv f s)) := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hQdef, c13c_aux_inner_eq, c13_rotation, c13_pt]
      simp; ring
    have hB : (∫ X in D R, c13_adjoint α c Φ X) = -(∫ X in D R, c13g_aux_div Q X) := by
      rw [← integral_neg]; exact setIntegral_congr_fun (hDm R) fun X _ => hdiv X
    rw [hB, hflux, hG, hT]
    simp only [hQdef]
    ring
  have hfin := tendsto_nhds_unique hlim1 ((hlim2.neg.sub hlim3).congr' (heq.mono fun _ h => h.symm))
  have hind : (fun Y => Ω.indicator (fun _ => (1 : ℝ)) Y * c13_adjoint α c Φ Y) =
      Ω.indicator (c13_adjoint α c Φ) := by
    ext Y; by_cases hY : Y ∈ Ω <;> simp [hY]
  rw [hind, integral_indicator hΩm, hfin, sub_zero]


theorem c13c_aux_potential_kernel_eq {α : ℝ} (hα : α ≠ 0) (c : ℝ) (z : c13_E) :
    c13_potential_kernel α c z = c * ‖z‖ ^ (-α) := by
  unfold c13_potential_kernel
  split_ifs with h
  · rw [h, norm_zero, Real.zero_rpow (neg_ne_zero.mpr hα), mul_zero]
  · rfl

/-- Blueprint: lem:c13_bulk_contour_identity.  For an admissible graph at a time `t ∈ I` and
every vector test `Φ`,
`∫ θ_F B*Φ = -∫ A_Φ(γ_t(s)) · τ_t(s) ds = ∫ U[F](X,t) · Φ(X) dX`, all absolutely convergent;
`U[F](·,t)` is locally integrable, hence a representative of `B θ_F`. -/
theorem c13_bulk_contour_identity {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t : ℝ} (ht : t ∈ I)
    (Φ : c13_E → c13_E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    Integrable (fun Y => (c13_patch F t).indicator (fun _ => (1 : ℝ)) Y * c13_adjoint α c Φ Y) ∧
    Integrable (fun s : ℝ =>
      inner ℝ (∫ X, c13_potential_kernel α c (X - c13_pt s (F s t)) • Φ X)
        (c13_pt 1 (deriv (fun x => F x t) s))) ∧
    Integrable (fun X => inner ℝ (c13_graph_velocity α c F X t) (Φ X)) ∧
    LocallyIntegrable (fun X => c13_graph_velocity α c F X t) ∧
    (∫ Y, (c13_patch F t).indicator (fun _ => (1 : ℝ)) Y * c13_adjoint α c Φ Y) =
      -(∫ s : ℝ, inner ℝ (∫ X, c13_potential_kernel α c (X - c13_pt s (F s t)) • Φ X)
        (c13_pt 1 (deriv (fun x => F x t) s))) ∧
    -(∫ s : ℝ, inner ℝ (∫ X, c13_potential_kernel α c (X - c13_pt s (F s t)) • Φ X)
        (c13_pt 1 (deriv (fun x => F x t) s))) =
      ∫ X, inner ℝ (c13_graph_velocity α c F X t) (Φ X) := by
  obtain ⟨hf, M, hM0, hM⟩ := c13c_aux_slice hF ht
  have hf1 : ContDiff ℝ 1 (fun x => F x t) := hf.of_le (by simp)
  obtain ⟨Cp, -, hTP, -⟩ := c13_test_potential hα1 hα2 c
  obtain ⟨hAint, hAC1, -, -⟩ := hTP Φ hΦ hΦc
  obtain ⟨Cad, -, hAD⟩ := c13_adjoint_integrable hα1 hα2 c
  have hBint : Integrable (c13_adjoint α c Φ) := (hAD Φ hΦ hΦc).2.2.1
  have hbulk := c13c_aux_bulk_flux_identity (c := c) hα1 hα2 (fun x => F x t) hf1 hM Φ hΦ hΦc
  have hcint := c13c_aux_contour_integrable (c := c) hα1 (fun x => F x t) hf1 hM Φ hΦ hΦc hAC1.continuous
  have hc0 : Continuous fun X : c13_E => X 0 := by fun_prop
  have hc1 : Continuous fun X : c13_E => X 1 := by fun_prop
  have hFc : Continuous fun x => F x t := hf.continuous
  have hΩm : MeasurableSet (c13_patch F t) :=
    (isOpen_lt hc1 (hFc.comp hc0)).measurableSet
  have hθB : Integrable (fun Y => (c13_patch F t).indicator (fun _ => (1 : ℝ)) Y *
      c13_adjoint α c Φ Y) := by
    have : (fun Y => (c13_patch F t).indicator (fun _ => (1 : ℝ)) Y * c13_adjoint α c Φ Y) =
        (c13_patch F t).indicator (c13_adjoint α c Φ) := by
      ext Y; by_cases hY : Y ∈ c13_patch F t <;> simp [hY]
    rw [this]; exact hBint.indicator hΩm
  -- geometry of the contour
  set γ : ℝ → c13_E := fun s => c13_pt s (F s t) with hγdef
  set τ : ℝ → c13_E := fun s => c13_pt 1 (deriv (fun x => F x t) s) with hτdef
  have hγ : Continuous γ := c13c_aux_continuous_pt continuous_id hFc
  have hτ : Continuous τ :=
    c13c_aux_continuous_pt (f := fun _ => (1:ℝ)) continuous_const (hf.continuous_deriv (by simp))
  have hdist : Measurable fun q : ℝ × c13_E => ‖q.2 - γ q.1‖ ^ (-α) :=
    ((continuous_snd.sub (hγ.comp continuous_fst)).norm.measurable).pow_const _
  have hgraph := (c13_graph_geometry hF).2.1 t ht
  have hoff : ∀ᵐ X : c13_E, X 1 ≠ F (X 0) t := by
    rw [ae_iff]; simpa using hgraph
  obtain ⟨-, -, -, hVL⟩ := c13_velocity_local_integrable hα1 hα2 c I F hF
  -- the joint contour-test function
  set g : ℝ → c13_E → ℝ := fun s X => c * ‖X - γ s‖ ^ (-α) * inner ℝ (τ s) (Φ X) with hgdef
  have hgm : Measurable (Function.uncurry g) := by
    have h3 : Continuous fun q : ℝ × c13_E => inner ℝ (τ q.1) (Φ q.2) :=
      (hτ.comp continuous_fst).inner (hΦ.continuous.comp continuous_snd)
    exact (measurable_const.mul hdist).mul h3.measurable
  obtain ⟨Cv, -, hCv⟩ := hVL {t} (singleton_subset_iff.mpr ht) isCompact_singleton (tsupport Φ) hΦc
  obtain ⟨B0, hB0⟩ : ∃ B, ∀ X, ‖Φ X‖ ≤ B := hΦ.continuous.bounded_above_of_compact_support hΦc
  have hmaj := (hCv t rfl (fun X => ‖Φ X‖) hΦ.continuous.norm.aestronglyMeasurable
    (fun X hX => by simp [image_eq_zero_of_notMem_tsupport hX]) B0
    (fun X => by simpa using hB0 X)).1
  rw [Measure.volume_eq_prod] at hmaj
  have hg : Integrable (Function.uncurry g) (volume.prod volume) := by
    refine (hmaj.const_mul |c|).mono' hgm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, hgdef, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have := abs_real_inner_le_norm (τ q.1) (Φ q.2)
    have h0 : 0 ≤ ‖q.2 - γ q.1‖ ^ (-α) := Real.rpow_nonneg (norm_nonneg _) _
    calc |c| * ‖q.2 - γ q.1‖ ^ (-α) * |inner ℝ (τ q.1) (Φ q.2)|
        ≤ |c| * ‖q.2 - γ q.1‖ ^ (-α) * (‖τ q.1‖ * ‖Φ q.2‖) := by gcongr
      _ = _ := by simp only [abs_norm]; ring
  -- side 1: the contour integrand is the X-integral of g
  have hside1 : ∀ s, inner ℝ (∫ X, c13_potential_kernel α c (X - γ s) • Φ X) (τ s) =
      ∫ X, g s X := by
    intro s
    rw [real_inner_comm, ← integral_inner (hAint (γ s)) (τ s)]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [hgdef, real_inner_smul_right, c13c_aux_potential_kernel_eq (by linarith : α ≠ 0)]
  -- side 2: the velocity pairing is minus the s-integral of g, off the null graph
  have hmajX := hmaj.prod_left_ae
  have hside2 : (fun X => inner ℝ (c13_graph_velocity α c F X t) (Φ X)) =ᵐ[volume]
      fun X => -∫ s, g s X := by
    filter_upwards [hoff, hmajX] with X hX hXi
    by_cases hΦX : Φ X = 0
    · simp [hgdef, hΦX]
    have hnp : 0 < ‖Φ X‖ := norm_pos_iff.mpr hΦX
    have hhi : Integrable (fun s : ℝ => (‖X - γ s‖ ^ (-α)) • τ s) := by
      refine ((hXi.div_const ‖Φ X‖)).mono' ?_ (Eventually.of_forall fun s => ?_)
      · exact ((hdist.comp (measurable_id.prodMk measurable_const)).smul
          hτ.measurable).aestronglyMeasurable
      · simp only [norm_smul, Real.norm_eq_abs, abs_norm,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        rw [le_div_iff₀ hnp]
        simp only [hτdef, hγdef]; nlinarith [norm_nonneg (c13_pt 1 (deriv (fun x => F x t) s)),
          Real.rpow_nonneg (norm_nonneg (X - c13_pt s (F s t))) (-α)]
    have hU : c13_graph_velocity α c F X t = (-c) • ∫ s, (‖X - γ s‖ ^ (-α)) • τ s := by
      simp only [c13_graph_velocity, hX, ite_false, hγdef, hτdef]
    rw [hU, real_inner_smul_left, real_inner_comm, ← integral_inner hhi (Φ X)]
    simp only [real_inner_smul_right, hgdef]
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [real_inner_comm (τ s)]; ring
  have hUΦ : Integrable (fun X => inner ℝ (c13_graph_velocity α c F X t) (Φ X)) :=
    (hg.integral_prod_right.neg).congr hside2.symm
  -- local integrability of the velocity
  have hLI : LocallyIntegrable (fun X => c13_graph_velocity α c F X t) := by
    rw [locallyIntegrable_iff]
    intro K' hK'
    obtain ⟨Cv', -, hCv'⟩ := hVL {t} (singleton_subset_iff.mpr ht) isCompact_singleton K' hK'
    have hm' := (hCv' t rfl (K'.indicator fun _ => (1 : ℝ))
      ((measurable_const.indicator hK'.measurableSet).aestronglyMeasurable)
      (fun X hX => by simp [hX]) 1 (fun X => by
        by_cases hX : X ∈ K' <;> simp [hX])).1
    rw [Measure.volume_eq_prod] at hm'
    have hmX := hm'.integral_prod_right
    have hhm : StronglyMeasurable (Function.uncurry
        fun (X : c13_E) (s : ℝ) => (‖X - γ s‖ ^ (-α)) • τ s) := by
      have h1 : Measurable fun p : c13_E × ℝ => ‖p.1 - γ p.2‖ ^ (-α) :=
        ((continuous_fst.sub (hγ.comp continuous_snd)).norm.measurable).pow_const _
      have h2 : Measurable fun p : c13_E × ℝ => τ p.2 := hτ.measurable.comp measurable_snd
      have h3 : Measurable fun p : c13_E × ℝ => (‖p.1 - γ p.2‖ ^ (-α)) • τ p.2 := h1.smul h2
      exact h3.stronglyMeasurable
    have hmeas : AEStronglyMeasurable (fun X => c13_graph_velocity α c F X t) volume := by
      refine ((hhm.integral_prod_right (ν := (volume : Measure ℝ))).const_smul (-c)).aestronglyMeasurable.congr ?_
      filter_upwards [hoff] with X hX
      simp only [c13_graph_velocity, hX, ite_false, hγdef, hτdef, Pi.smul_apply]
    refine (hmX.const_mul |c|).integrableOn.mono' hmeas.restrict ?_
    refine (ae_restrict_iff' hK'.measurableSet).mpr (Eventually.of_forall fun X hXK => ?_)
    have hnn : 0 ≤ ∫ s, ‖τ s‖ * ‖X - γ s‖ ^ (-α) * |K'.indicator (fun _ => (1 : ℝ)) X| :=
      integral_nonneg fun s => by positivity
    by_cases hX : X 1 = F (X 0) t
    · simp only [c13_graph_velocity, hX, ite_true, norm_zero]
      exact mul_nonneg (abs_nonneg _) hnn
    simp only [c13_graph_velocity, hX, ite_false, norm_smul, Real.norm_eq_abs, abs_neg]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (abs_nonneg _)
    refine le_of_eq (integral_congr_ae (Eventually.of_forall fun s => ?_))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      indicator_of_mem hXK, abs_one, mul_one]
    ring
  refine ⟨hθB, hcint, hUΦ, hLI, hbulk, ?_⟩
  rw [integral_congr_ae hside2, integral_neg, ← integral_integral_swap hg]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun s => hside1 s)


/-! ### Helpers for the principal value -/

theorem c13c_aux_norm_rotation (z : c13_E) : ‖c13_rotation z‖ = ‖z‖ := by
  simp [c13_rotation, EuclideanSpace.norm_eq, Fin.sum_univ_two, add_comm]

theorem c13c_aux_eta (X : c13_E) : X = c13_pt (X 0) (X 1) := by
  ext i; fin_cases i <;> simp [c13_pt]

theorem c13c_aux_norm_pt_le (a b : ℝ) : ‖c13_pt a b‖ ≤ |a| + |b| := by
  rw [c13c_aux_norm_pt, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]

theorem c13c_aux_one_le_norm_tau (m : ℝ) : 1 ≤ ‖c13_pt 1 m‖ := by
  simpa using (c13c_aux_abs_le_norm_pt 1 m).1

theorem c13c_aux_norm_kernel {α : ℝ} (hα : 0 < α) (c : ℝ) (z : c13_E) :
    ‖c13_velocity_kernel α c z‖ = |α * c| * ‖z‖ ^ (-α - 1) := by
  unfold c13_velocity_kernel
  split_ifs with h
  · rw [h, norm_zero, Real.zero_rpow (by linarith), mul_zero]
  · have hz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr h
    rw [norm_smul, c13c_aux_norm_rotation, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), mul_assoc]
    congr 1
    rw [show -α - 1 = (-α - 2) + 1 by ring, Real.rpow_add_one hz]

theorem c13c_aux_kernel_neg (α c : ℝ) (z : c13_E) :
    c13_velocity_kernel α c (-z) = -c13_velocity_kernel α c z := by
  unfold c13_velocity_kernel
  by_cases h : z = 0
  · simp [h]
  · have h' : -z ≠ 0 := neg_ne_zero.mpr h
    simp only [h, h', ite_false, norm_neg]
    rw [← smul_neg]; congr 1
    ext i; fin_cases i <;> simp [c13_rotation]

theorem c13c_aux_kernel_measurable (α c : ℝ) : Measurable (c13_velocity_kernel α c) := by
  unfold c13_velocity_kernel
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  have hr : Continuous c13_rotation := c13c_aux_rotL.continuous
  exact ((measurable_const.mul (measurable_norm.pow_const _))).smul hr.measurable

/-- Oddness: the kernel has zero integral over every symmetric exterior region. -/
theorem c13c_aux_kernel_odd_integral (α c ε : ℝ) :
    ∫ z in {z : c13_E | ε < ‖z‖}, c13_velocity_kernel α c z = 0 := by
  rw [← integral_indicator (measurableSet_lt measurable_const measurable_norm)]
  set g := {z : c13_E | ε < ‖z‖}.indicator (c13_velocity_kernel α c)
  have hg : ∀ z, g (-z) = -g z := by
    intro z
    simp only [g, indicator, mem_ofPred_eq, norm_neg]
    split_ifs <;> simp [c13c_aux_kernel_neg]
  have h := integral_neg_eq_self g (volume : Measure c13_E)
  simp only [hg, integral_neg] at h
  have h2 : (2 : ℝ) • (∫ z, g z) = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero


theorem c13c_aux_sub_pt (X : c13_E) (a b : ℝ) : X - c13_pt a b = c13_pt (X 0 - a) (X 1 - b) := by
  ext i; fin_cases i <;> simp [c13_pt]

/-- Off the graph, the density is constant on a ball of radius comparable to the vertical gap. -/
theorem c13c_aux_ball_const {f : ℝ → ℝ} {M : ℝ}
    (hlip : ∀ a b, |f a - f b| ≤ M * |a - b|) (X z : c13_E)
    (hz : (1 + M) * ‖z‖ < |X 1 - f (X 0)|) :
    {Y : c13_E | Y 1 < f (Y 0)}.indicator (fun _ => (1 : ℝ)) (X - z) =
      {Y : c13_E | Y 1 < f (Y 0)}.indicator (fun _ => (1 : ℝ)) X := by
  have h0 := c13c_aux_abs_apply_le z 0
  have h1 := c13c_aux_abs_apply_le z 1
  have hl := hlip (X 0 - z 0) (X 0)
  rw [show X 0 - z 0 - X 0 = -z 0 by ring, abs_neg] at hl
  have hM : 0 ≤ M := by
    have := hlip 1 0; norm_num at this; linarith [abs_nonneg (f 1 - f 0)]
  have key : |((X 1 - z 1) - f (X 0 - z 0)) - (X 1 - f (X 0))| < |X 1 - f (X 0)| := by
    calc _ = |-(z 1) - (f (X 0 - z 0) - f (X 0))| := by ring_nf
      _ ≤ |z 1| + |f (X 0 - z 0) - f (X 0)| := by
          refine (abs_sub _ _).trans ?_; rw [abs_neg]
      _ ≤ (1 + M) * ‖z‖ := by nlinarith
      _ < _ := hz
  have e0 : (X - z) 0 = X 0 - z 0 := rfl
  have e1 : (X - z) 1 = X 1 - z 1 := rfl
  simp only [indicator, mem_ofPred_eq, e0, e1]
  have := abs_lt.mp key
  split_ifs with hA hB hB <;> first | rfl | (exfalso; cases abs_cases (X 1 - f (X 0)) <;> linarith)

/-- Lower bound of the gap power by the scalar contour majorant. -/
theorem c13c_aux_gap_lower {α M : ℝ} (hα : 0 < α) (f : ℝ → ℝ) (hM : 0 ≤ M)
    (hlip : ∀ a b, |f a - f b| ≤ M * |a - b|) (X : c13_E) (hX : X 1 ≠ f (X 0))
    (hi : Integrable (fun s : ℝ => ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α))) :
    |X 1 - f (X 0)| ^ (1 - α) ≤
      (2 + M) ^ α / 2 * ∫ s : ℝ, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α) := by
  set δ := |X 1 - f (X 0)| with hδ
  have hδp : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hX)
  set S : Set ℝ := Icc (X 0 - δ) (X 0 + δ)
  have hpt : ∀ s ∈ S, ((2 + M) * δ) ^ (-α) ≤
      ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α) := by
    intro s hs
    have hs' : |X 0 - s| ≤ δ := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hpos : 0 < ‖X - c13_pt s (f s)‖ := by
      rw [norm_pos_iff, c13c_aux_sub_pt]; intro h
      have h0 := congrArg (fun v : c13_E => v 0) h
      have h1 := congrArg (fun v : c13_E => v 1) h
      simp [c13_pt] at h0 h1
      apply hX; rw [show X 0 = s by linarith]; linarith
    have hup : ‖X - c13_pt s (f s)‖ ≤ (2 + M) * δ := by
      rw [c13c_aux_sub_pt]
      refine (c13c_aux_norm_pt_le _ _).trans ?_
      have h1 : |X 1 - f s| ≤ δ + M * δ := by
        have := hlip (X 0) s
        calc |X 1 - f s| = |(X 1 - f (X 0)) + (f (X 0) - f s)| := by ring_nf
          _ ≤ δ + |f (X 0) - f s| := abs_add_le _ _
          _ ≤ δ + M * δ := by nlinarith
      nlinarith
    have := Real.rpow_le_rpow_of_nonpos hpos hup (by linarith : -α ≤ 0)
    calc ((2 + M) * δ) ^ (-α) ≤ ‖X - c13_pt s (f s)‖ ^ (-α) := this
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg (norm_nonneg _) _)
          (c13c_aux_one_le_norm_tau _)
  have hS : (∫ s in S, ((2 + M) * δ) ^ (-α)) ≤
      ∫ s in S, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α) :=
    setIntegral_mono_on (integrableOn_const (by simp [S, Real.volume_Icc]))
      hi.integrableOn measurableSet_Icc hpt
  have hS2 : (∫ s in S, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α)) ≤
      ∫ s, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α) :=
    setIntegral_le_integral hi (Eventually.of_forall fun s => by positivity)
  have hc : (∫ s in S, ((2 + M) * δ) ^ (-α)) = 2 * (2 + M) ^ (-α) * δ ^ (1 - α) := by
    rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
      Real.mul_rpow (by linarith) hδp.le, show X 0 + δ - (X 0 - δ) = 2 * δ by ring,
      max_eq_left (by linarith)]
    rw [show (1 - α) = 1 + (-α) by ring, Real.rpow_add hδp, Real.rpow_one]; ring
  have h2M : 0 < (2 + M) ^ α := by positivity
  have hinv : (2 + M) ^ α * (2 + M) ^ (-α) = 1 := by
    rw [← Real.rpow_add (by linarith)]; simp
  calc δ ^ (1 - α) = (2 + M) ^ α / 2 * (2 * (2 + M) ^ (-α) * δ ^ (1 - α)) := by
        have : (2 + M) ^ α / 2 * (2 * (2 + M) ^ (-α) * δ ^ (1 - α)) =
            ((2 + M) ^ α * (2 + M) ^ (-α)) * δ ^ (1 - α) := by ring
        rw [this, hinv, one_mul]
    _ ≤ _ := by rw [← hc]; gcongr; exact hS.trans hS2


theorem c13c_aux_trunc_integrable {α c ε : ℝ} (hα : 0 < α)
    (hint : IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α - 1)) {z | ε < ‖z‖})
    (θ : c13_E → ℝ) (hθm : Measurable θ) (hθb : ∀ Y, |θ Y| ≤ 1) (X : c13_E) :
    IntegrableOn (fun z => θ (X - z) • c13_velocity_kernel α c z) {z | ε < ‖z‖} ∧
    IntegrableOn (c13_velocity_kernel α c) {z | ε < ‖z‖} ∧
    ‖∫ z in {z : c13_E | ε < ‖z‖}, θ (X - z) • c13_velocity_kernel α c z‖ ≤
      |α * c| * ∫ z in {z : c13_E | ε < ‖z‖}, ‖z‖ ^ (-α - 1) := by
  have hK := c13c_aux_kernel_measurable α c
  have hKi : IntegrableOn (c13_velocity_kernel α c) {z | ε < ‖z‖} :=
    (hint.const_mul |α * c|).mono' hK.aestronglyMeasurable
      (Eventually.of_forall fun z => (c13c_aux_norm_kernel hα c z).le)
  have hθz : Measurable fun z => θ (X - z) := hθm.comp (measurable_const.sub measurable_id)
  have hb : ∀ z, ‖θ (X - z) • c13_velocity_kernel α c z‖ ≤ |α * c| * ‖z‖ ^ (-α - 1) := by
    intro z
    rw [norm_smul, Real.norm_eq_abs, c13c_aux_norm_kernel hα c z]
    have := hθb (X - z)
    have h0 : 0 ≤ |α * c| * ‖z‖ ^ (-α - 1) := by positivity
    nlinarith
  refine ⟨(hint.const_mul |α * c|).mono' (hθz.smul hK).aestronglyMeasurable
    (Eventually.of_forall hb), hKi, ?_⟩
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (hint.const_mul _) (Eventually.of_forall hb)

theorem c13c_aux_desing {α c : ℝ} (hα : 0 < α)
    (hint : ∀ r, 0 < r → IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α - 1)) {z | r < ‖z‖})
    (θ : c13_E → ℝ) (hθm : Measurable θ) (hθb : ∀ Y, |θ Y| ≤ 1) (X : c13_E) (r : ℝ) (hr : 0 < r)
    (hball : ∀ z : c13_E, ‖z‖ < r → θ (X - z) = θ X) :
    Integrable (fun z => (θ (X - z) - θ X) • c13_velocity_kernel α c z) ∧
    (∀ ε, 0 < ε → ‖(∫ z in {z : c13_E | ε < ‖z‖}, θ (X - z) • c13_velocity_kernel α c z) -
        ∫ z, (θ (X - z) - θ X) • c13_velocity_kernel α c z‖ ≤
          2 * |α * c| * ∫ z in {z : c13_E | r / 2 < ‖z‖}, ‖z‖ ^ (-α - 1)) ∧
    (∀ ε, 0 < ε → ε < r → (∫ z in {z : c13_E | ε < ‖z‖}, θ (X - z) • c13_velocity_kernel α c z) =
        ∫ z, (θ (X - z) - θ X) • c13_velocity_kernel α c z) ∧
    ‖∫ z, (θ (X - z) - θ X) • c13_velocity_kernel α c z‖ ≤
          2 * |α * c| * ∫ z in {z : c13_E | r / 2 < ‖z‖}, ‖z‖ ^ (-α - 1) := by
  set d : c13_E → c13_E := fun z => (θ (X - z) - θ X) • c13_velocity_kernel α c z with hd
  set T : Set c13_E := {z | r / 2 < ‖z‖} with hT
  have hTm : MeasurableSet T := measurableSet_lt measurable_const measurable_norm
  have hK := c13c_aux_kernel_measurable α c
  have hθz : Measurable fun z => θ (X - z) := hθm.comp (measurable_const.sub measurable_id)
  have hdm : Measurable d := (hθz.sub measurable_const).smul hK
  have hd0 : ∀ z, ‖z‖ < r → d z = 0 := by
    intro z hz; simp [hd, hball z hz]
  set g : c13_E → ℝ := T.indicator fun z => 2 * |α * c| * ‖z‖ ^ (-α - 1) with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff hTm]; exact (hint (r / 2) (by linarith)).const_mul _
  have hdb : ∀ z, ‖d z‖ ≤ g z := by
    intro z
    by_cases hz : ‖z‖ < r
    · rw [hd0 z hz, norm_zero]
      exact indicator_nonneg (fun _ _ => by positivity) _
    · have hzT : z ∈ T := by simp only [hT, mem_ofPred_eq]; linarith
      rw [hg, indicator_of_mem hzT, hd, norm_smul, Real.norm_eq_abs, c13c_aux_norm_kernel hα c z]
      have h1 := hθb (X - z); have h2 := hθb X
      have h3 : |θ (X - z) - θ X| ≤ 2 := by
        calc _ ≤ |θ (X - z)| + |θ X| := abs_sub _ _
          _ ≤ 2 := by linarith
      have h0 : 0 ≤ |α * c| * ‖z‖ ^ (-α - 1) := by positivity
      nlinarith
  have hdi : Integrable d := hgi.mono' hdm.aestronglyMeasurable (Eventually.of_forall hdb)
  have hgval : ∫ z, g z = 2 * |α * c| * ∫ z in T, ‖z‖ ^ (-α - 1) := by
    rw [hg, integral_indicator hTm, integral_const_mul]
  have hnorm : ‖∫ z, d z‖ ≤ 2 * |α * c| * ∫ z in T, ‖z‖ ^ (-α - 1) := by
    rw [← hgval]
    exact (norm_integral_le_integral_norm _).trans (integral_mono hdi.norm hgi hdb)
  -- u_ε = ∫_{S_ε} d
  have hu : ∀ ε, 0 < ε → (∫ z in {z : c13_E | ε < ‖z‖}, θ (X - z) • c13_velocity_kernel α c z) =
      ∫ z in {z : c13_E | ε < ‖z‖}, d z := by
    intro ε hε
    obtain ⟨-, hKi, -⟩ := c13c_aux_trunc_integrable (c := c) hα (hint ε hε) θ hθm hθb X
    have : (fun z => θ (X - z) • c13_velocity_kernel α c z) =
        fun z => d z + θ X • c13_velocity_kernel α c z := by
      ext z; simp only [hd, sub_smul, sub_add_cancel]
    rw [this, integral_add (f := d) (g := fun z => θ X • c13_velocity_kernel α c z)
      hdi.integrableOn (hKi.smul (θ X)), integral_smul,
      c13c_aux_kernel_odd_integral, smul_zero, add_zero]
  have hcompl : ∀ ε, (∫ z in {z : c13_E | ε < ‖z‖}, d z) - ∫ z, d z =
      -∫ z in {z : c13_E | ε < ‖z‖}ᶜ, d z := by
    intro ε
    rw [← integral_add_compl (measurableSet_lt measurable_const measurable_norm) hdi]; abel
  refine ⟨hdi, fun ε hε => ?_, fun ε hε hεr => ?_, hnorm⟩
  · rw [hu ε hε, hcompl, norm_neg, ← hgval]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_le_integral hdi.norm (Eventually.of_forall fun _ => norm_nonneg _)).trans ?_
    exact integral_mono hdi.norm hgi hdb
  · rw [hu ε hε, ← sub_eq_zero, hcompl, neg_eq_zero]
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => hd0 z ?_
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hz; linarith


theorem c13c_aux_trunc_pairing {α c ε : ℝ} (hα : 0 < α)
    (hint : IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α - 1)) {z | ε < ‖z‖})
    (θ : c13_E → ℝ) (hθm : Measurable θ) (hθb : ∀ Y, |θ Y| ≤ 1)
    (Φ : c13_E → c13_E) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    (∫ X, inner ℝ (∫ z in {z : c13_E | ε < ‖z‖}, θ (X - z) • c13_velocity_kernel α c z) (Φ X)) =
      ∫ Y, θ Y * ∫ z in {z : c13_E | ε < ‖z‖},
        inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y) := by
  set S : Set c13_E := {z | ε < ‖z‖} with hS
  set ν : Measure c13_E := volume.restrict S with hν
  have hK := c13c_aux_kernel_measurable α c
  obtain ⟨-, hKi, -⟩ := c13c_aux_trunc_integrable (c := c) hα hint θ hθm hθb 0
  have hKi' : Integrable (c13_velocity_kernel α c) ν := hKi
  have hΦi : Integrable Φ := hΦ.integrable_of_hasCompactSupport hΦc
  obtain ⟨B, hB⟩ : ∃ B, ∀ X, ‖Φ X‖ ≤ B := hΦ.bounded_above_of_compact_support hΦc
  set H : c13_E → c13_E → ℝ := fun X z => θ (X - z) * inner ℝ (c13_velocity_kernel α c z) (Φ X)
    with hH
  have hHm : Measurable (Function.uncurry H) := by
    have h1 : Measurable fun p : c13_E × c13_E => θ (p.1 - p.2) :=
      hθm.comp (measurable_fst.sub measurable_snd)
    have h2 : Measurable fun p : c13_E × c13_E =>
        inner ℝ (c13_velocity_kernel α c p.2) (Φ p.1) :=
      (hK.comp measurable_snd).inner (hΦ.measurable.comp measurable_fst)
    exact h1.mul h2
  have hHb : ∀ p : c13_E × c13_E, ‖Function.uncurry H p‖ ≤ ‖Φ p.1‖ * ‖c13_velocity_kernel α c p.2‖ := by
    intro p
    simp only [Function.uncurry, hH, norm_mul, Real.norm_eq_abs]
    have := abs_real_inner_le_norm (c13_velocity_kernel α c p.2) (Φ p.1)
    have h1 := hθb (p.1 - p.2)
    have h0 : 0 ≤ ‖c13_velocity_kernel α c p.2‖ * ‖Φ p.1‖ := by positivity
    calc |θ (p.1 - p.2)| * |inner ℝ (c13_velocity_kernel α c p.2) (Φ p.1)|
        ≤ 1 * (‖c13_velocity_kernel α c p.2‖ * ‖Φ p.1‖) := by gcongr
      _ = _ := by ring
  have hHi : Integrable (Function.uncurry H) (volume.prod ν) :=
    (hΦi.norm.mul_prod hKi'.norm).mono' hHm.aestronglyMeasurable (Eventually.of_forall hHb)
  -- step 1
  have h1 : ∀ X, inner ℝ (∫ z in S, θ (X - z) • c13_velocity_kernel α c z) (Φ X) =
      ∫ z, H X z ∂ν := by
    intro X
    obtain ⟨hXi, -, -⟩ := c13c_aux_trunc_integrable (c := c) hα hint θ hθm hθb X
    rw [real_inner_comm, ← integral_inner hXi (Φ X)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hH, real_inner_smul_right]
    rw [real_inner_comm]
  -- step 2: shear
  set H' : c13_E → c13_E → ℝ := fun Y z => θ Y * inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z))
    with hH'
  have hshear : Function.uncurry H' = Function.uncurry H ∘ fun p : c13_E × c13_E => (p.1 + p.2, p.2) := by
    ext p; simp [hH, hH', Function.uncurry]
  have hmp := measurePreserving_add_prod (volume : Measure c13_E) ν
  have hH'i : Integrable (Function.uncurry H') (volume.prod ν) := by
    rw [hshear]; exact (hmp.integrable_comp hHm.aestronglyMeasurable).mpr hHi
  have h3 : ∀ z, ∫ X, H X z = ∫ Y, H' Y z := by
    intro z
    rw [← integral_add_right_eq_self (fun X => H X z) z]
    simp [hH, hH']
  -- step 3: odd part vanishes
  have h4 : ∀ Y, ∫ z, H' Y z ∂ν = θ Y * ∫ z in S,
      inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y) := by
    intro Y
    have hi1 : Integrable (fun z => inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z))) ν := by
      refine (hKi'.norm.mul_const B).mono'
        ((hK.inner (hΦ.measurable.comp (measurable_const.add measurable_id))).aestronglyMeasurable)
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hB _)
    have hi2 : Integrable (fun z => inner ℝ (c13_velocity_kernel α c z) (Φ Y)) ν :=
      hKi'.inner_const (Φ Y)
    have h0 : ∫ z, inner ℝ (c13_velocity_kernel α c z) (Φ Y) ∂ν = 0 := by
      have hc : ∀ z, inner ℝ (c13_velocity_kernel α c z) (Φ Y) =
          inner ℝ (Φ Y) (c13_velocity_kernel α c z) := fun z => real_inner_comm _ _
      simp only [hc]
      rw [integral_inner hKi' (Φ Y), hν, hS, c13c_aux_kernel_odd_integral, inner_zero_right]
    simp only [hH']
    rw [integral_const_mul]
    congr 1
    simp only [inner_sub_right]
    rw [integral_sub hi1 hi2, h0, sub_zero]
  calc (∫ X, inner ℝ (∫ z in S, θ (X - z) • c13_velocity_kernel α c z) (Φ X))
      = ∫ X, (∫ z, H X z ∂ν) := integral_congr_ae (Eventually.of_forall h1)
    _ = ∫ z, (∫ X, H X z) ∂ν := integral_integral_swap hHi
    _ = ∫ z, (∫ Y, H' Y z) ∂ν := integral_congr_ae (Eventually.of_forall h3)
    _ = ∫ Y, (∫ z, H' Y z ∂ν) := (integral_integral_swap hH'i).symm
    _ = _ := integral_congr_ae (Eventually.of_forall h4)


theorem c13c_aux_ae_ne_zero : ∀ᵐ z : c13_E, z ≠ 0 := by
  rw [ae_iff]; simp

theorem c13c_aux_adjoint_limit {α c : ℝ}
    (θ : c13_E → ℝ) (hθm : Measurable θ) (hθb : ∀ Y, |θ Y| ≤ 1)
    (Φ : c13_E → c13_E) (hΦ : Continuous Φ)
    (hprod : Integrable (fun p : c13_E × c13_E =>
        inner ℝ (c13_velocity_kernel α c p.2) (Φ (p.1 + p.2) - Φ p.1)))
    (hY : ∀ Y : c13_E, Integrable (fun z : c13_E =>
        inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y))) :
    Tendsto (fun ε : ℝ => ∫ Y, θ Y * ∫ z in {z : c13_E | ε < ‖z‖},
        inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y)) (𝓝[>] 0)
      (𝓝 (∫ Y, θ Y * c13_adjoint α c Φ Y)) := by
  set g : c13_E → c13_E → ℝ := fun Y z =>
    inner ℝ (c13_velocity_kernel α c z) (Φ (Y + z) - Φ Y) with hg
  have hK := c13c_aux_kernel_measurable α c
  have hgm : Measurable (Function.uncurry g) :=
    (hK.comp measurable_snd).inner
      ((hΦ.measurable.comp (measurable_fst.add measurable_snd)).sub (hΦ.measurable.comp measurable_fst))
  rw [Measure.volume_eq_prod] at hprod
  have hβ : Integrable (fun Y => ∫ z, ‖g Y z‖) := hprod.norm.integral_prod_left
  have hSm : ∀ ε : ℝ, MeasurableSet {z : c13_E | ε < ‖z‖} := fun ε =>
    measurableSet_lt measurable_const measurable_norm
  refine tendsto_integral_filter_of_dominated_convergence (fun Y => ∫ z, ‖g Y z‖)
    (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => ?_) hβ ?_
  · exact (hθm.mul (hgm.stronglyMeasurable.integral_prod_right
      (ν := volume.restrict {z : c13_E | ε < ‖z‖})).measurable).aestronglyMeasurable
  · refine Eventually.of_forall fun Y => ?_
    rw [norm_mul, Real.norm_eq_abs]
    have h1 := hθb Y
    have h2 : ‖∫ z in {z : c13_E | ε < ‖z‖}, g Y z‖ ≤ ∫ z, ‖g Y z‖ :=
      (norm_integral_le_integral_norm _).trans
        (setIntegral_le_integral (hY Y).norm (Eventually.of_forall fun _ => norm_nonneg _))
    have h3 : 0 ≤ ‖∫ z in {z : c13_E | ε < ‖z‖}, g Y z‖ := norm_nonneg _
    nlinarith [abs_nonneg (θ Y)]
  · refine Eventually.of_forall fun Y => (Tendsto.const_mul (θ Y) ?_)
    have : (fun ε : ℝ => ∫ z in {z : c13_E | ε < ‖z‖}, g Y z) =
        fun ε => ∫ z, {z : c13_E | ε < ‖z‖}.indicator (g Y) z := by
      ext ε; rw [integral_indicator (hSm ε)]
    rw [this]
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖g Y z‖)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => ?_) (hY Y).norm ?_
    · exact ((hgm.comp (measurable_const.prodMk measurable_id)).indicator (hSm ε)).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ {z : c13_E | ε < ‖z‖}
      · rw [indicator_of_mem hz]
      · rw [indicator_of_notMem hz, norm_zero]; exact norm_nonneg _
    · filter_upwards [c13c_aux_ae_ne_zero] with z hz
      have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hzp)] with ε hε
      rw [indicator_of_mem (show z ∈ {z : c13_E | ε < ‖z‖} from hε)]


/-- Truncated velocity `u_ε` (pure helper definition). -/
def c13c_aux_u (α c : ℝ) (θ : c13_E → ℝ) (ε : ℝ) (X : c13_E) : c13_E :=
  ∫ z in {z : c13_E | ε < ‖z‖}, θ (X - z) • c13_velocity_kernel α c z

/-- Desingularized velocity (pure helper definition). -/
def c13c_aux_u0 (α c : ℝ) (θ : c13_E → ℝ) (X : c13_E) : c13_E :=
  ∫ z, (θ (X - z) - θ X) • c13_velocity_kernel α c z

theorem c13c_aux_u_meas (α c : ℝ) {θ : c13_E → ℝ} (hθm : Measurable θ) (ε : ℝ) :
    StronglyMeasurable (c13c_aux_u α c θ ε) := by
  have : Measurable fun p : c13_E × c13_E => θ (p.1 - p.2) • c13_velocity_kernel α c p.2 :=
    (hθm.comp (measurable_fst.sub measurable_snd)).smul
      ((c13c_aux_kernel_measurable α c).comp measurable_snd)
  exact this.stronglyMeasurable.integral_prod_right (ν := volume.restrict {z : c13_E | ε < ‖z‖})

theorem c13c_aux_u0_meas (α c : ℝ) {θ : c13_E → ℝ} (hθm : Measurable θ) :
    StronglyMeasurable (c13c_aux_u0 α c θ) := by
  have : Measurable fun p : c13_E × c13_E =>
      (θ (p.1 - p.2) - θ p.1) • c13_velocity_kernel α c p.2 :=
    ((hθm.comp (measurable_fst.sub measurable_snd)).sub (hθm.comp measurable_fst)).smul
      ((c13c_aux_kernel_measurable α c).comp measurable_snd)
  exact this.stronglyMeasurable.integral_prod_right (ν := volume)

theorem c13c_aux_rpow_div {δ A p : ℝ} (hδ : 0 ≤ δ) (hA : 0 < A) :
    (δ / A) ^ p = δ ^ p * A ^ (-p) := by
  rw [Real.div_rpow hδ hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]

/-- Local `L¹` control of the truncations, modulo the scalar contour majorant (pure helper). -/
theorem c13c_aux_pv_local {α c M : ℝ} (hα1 : 1 < α) (f : ℝ → ℝ) (hM0 : 0 ≤ M)
    (hlip : ∀ a b, |f a - f b| ≤ M * |a - b|)
    (θ : c13_E → ℝ) (hθm : Measurable θ) (hθb : ∀ Y, |θ Y| ≤ 1)
    (hball : ∀ X z : c13_E, (1 + M) * ‖z‖ < |X 1 - f (X 0)| → θ (X - z) = θ X)
    (hrad : ∀ r : ℝ, 0 < r →
      IntegrableOn (fun z : c13_E => ‖z‖ ^ (-α - 1)) {z | r < ‖z‖} ∧
      ∫ z in {z : c13_E | r < ‖z‖}, ‖z‖ ^ (-α - 1) = 2 * π / (α - 1) * r ^ (1 - α))
    (hoff : ∀ᵐ X : c13_E, X 1 ≠ f (X 0))
    (Q : Set c13_E) (hQ : IsCompact Q)
    (hmaj : Integrable (fun q : ℝ × c13_E => ‖c13_pt 1 (deriv f q.1)‖ *
        ‖q.2 - c13_pt q.1 (f q.1)‖ ^ (-α) * |Q.indicator (fun _ => (1 : ℝ)) q.2|)
        (volume.prod volume)) :
    (∀ ε, 0 < ε → IntegrableOn (c13c_aux_u α c θ ε) Q) ∧
    IntegrableOn (c13c_aux_u0 α c θ) Q ∧
    Tendsto (fun ε => ∫ X in Q, ‖c13c_aux_u α c θ ε X - c13c_aux_u0 α c θ X‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hQm : MeasurableSet Q := hQ.measurableSet
  set A : ℝ := 2 * (1 + M) with hA
  have hAp : 0 < A := by positivity
  set Cmaj : ℝ := 2 * |α * c| * (2 * π / (α - 1)) * A ^ (α - 1) * ((2 + M) ^ α / 2) with hCmaj
  set m : c13_E → ℝ := fun X => ∫ s, ‖c13_pt 1 (deriv f s)‖ *
      ‖X - c13_pt s (f s)‖ ^ (-α) * |Q.indicator (fun _ => (1 : ℝ)) X| with hmdef
  have hm : Integrable m := hmaj.integral_prod_right
  have hmX := hmaj.prod_left_ae
  have hkey : ∀ᵐ X : c13_E, X ∈ Q →
      (∀ ε, 0 < ε → ‖c13c_aux_u α c θ ε X - c13c_aux_u0 α c θ X‖ ≤ Cmaj * m X) ∧
      ‖c13c_aux_u0 α c θ X‖ ≤ Cmaj * m X ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), c13c_aux_u α c θ ε X = c13c_aux_u0 α c θ X) := by
    filter_upwards [hoff, hmX] with X hX hXi hXQ
    set δ := |X 1 - f (X 0)| with hδ
    have hδp : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hX)
    set r := δ / (1 + M) with hr
    have hrp : 0 < r := by positivity
    have hball' : ∀ z : c13_E, ‖z‖ < r → θ (X - z) = θ X := by
      intro z hz
      refine hball X z ?_
      have : (1 + M) * ‖z‖ < (1 + M) * r := by gcongr
      rwa [hr, mul_div_cancel₀ _ (by positivity : (1 + M) ≠ 0)] at this
    obtain ⟨-, h2, h3, h4⟩ := c13c_aux_desing (c := c) hα0 (fun r hr => (hrad r hr).1) θ hθm hθb
      X r hrp hball'
    have hval := (hrad (r / 2) (by positivity)).2
    have hr2 : r / 2 = δ / A := by rw [hr, hA]; field_simp
    have hXi' : Integrable (fun s : ℝ => ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α)) := by
      simpa [indicator_of_mem hXQ] using hXi
    have hmval : m X = ∫ s, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α) := by
      simp [hmdef, indicator_of_mem hXQ]
    have hgap := c13c_aux_gap_lower hα0 f hM0 hlip X hX hXi'
    have hbound : 2 * |α * c| * ∫ z in {z : c13_E | r / 2 < ‖z‖}, ‖z‖ ^ (-α - 1) ≤ Cmaj * m X := by
      rw [hval, hr2, c13c_aux_rpow_div hδp.le hAp, neg_sub, hmval]
      have h0 : 0 ≤ 2 * |α * c| * (2 * π / (α - 1)) * A ^ (α - 1) := by
        have : 0 < α - 1 := by linarith
        positivity
      calc 2 * |α * c| * (2 * π / (α - 1) * (δ ^ (1 - α) * A ^ (α - 1)))
          = (2 * |α * c| * (2 * π / (α - 1)) * A ^ (α - 1)) * δ ^ (1 - α) := by ring
        _ ≤ (2 * |α * c| * (2 * π / (α - 1)) * A ^ (α - 1)) *
            ((2 + M) ^ α / 2 * ∫ s, ‖c13_pt 1 (deriv f s)‖ * ‖X - c13_pt s (f s)‖ ^ (-α)) :=
          mul_le_mul_of_nonneg_left hgap h0
        _ = _ := by rw [hCmaj]; ring
    refine ⟨fun ε hε => (h2 ε hε).trans hbound, h4.trans hbound, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hrp] with ε hε
    exact h3 ε hε.1 hε.2
  have hkeyQ : ∀ᵐ X ∂(volume.restrict Q), (∀ ε, 0 < ε →
      ‖c13c_aux_u α c θ ε X - c13c_aux_u0 α c θ X‖ ≤ Cmaj * m X) ∧
      ‖c13c_aux_u0 α c θ X‖ ≤ Cmaj * m X ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), c13c_aux_u α c θ ε X = c13c_aux_u0 α c θ X) :=
    (ae_restrict_iff' hQm).mpr hkey
  have hbi : Integrable (fun X => Cmaj * m X) (volume.restrict Q) := (hm.const_mul Cmaj).integrableOn
  have hu : ∀ ε, 0 < ε → IntegrableOn (c13c_aux_u α c θ ε) Q := by
    intro ε hε
    obtain ⟨-, -, h3⟩ := c13c_aux_trunc_integrable (c := c) hα0 (hrad ε hε).1 θ hθm hθb 0
    refine (integrableOn_const (C := |α * c| * ∫ z in {z : c13_E | ε < ‖z‖}, ‖z‖ ^ (-α - 1))
      hQ.measure_lt_top.ne).mono' (c13c_aux_u_meas α c hθm ε).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    exact (c13c_aux_trunc_integrable (c := c) hα0 (hrad ε hε).1 θ hθm hθb X).2.2
  refine ⟨hu, hbi.mono' (c13c_aux_u0_meas α c hθm).aestronglyMeasurable
    (hkeyQ.mono fun X h => h.2.1), ?_⟩
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict Q)
    (l := 𝓝[>] (0 : ℝ)) (f := fun _ => (0 : ℝ))
    (F := fun ε X => ‖c13c_aux_u α c θ ε X - c13c_aux_u0 α c θ X‖)
    (fun X => Cmaj * m X)
    (Eventually.of_forall fun ε => ((c13c_aux_u_meas α c hθm ε).sub
      (c13c_aux_u0_meas α c hθm)).norm.aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [hkeyQ] with X hX
      rw [norm_norm]; exact hX.1 ε hε)
    hbi
    (by
      filter_upwards [hkeyQ] with X hX
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hX.2.2] with ε hε
      rw [hε, sub_self, norm_zero])
  simpa using this


theorem c13c_aux_locInt_apply {v : c13_E → c13_E} (hv : LocallyIntegrable v) (i : Fin 2) :
    LocallyIntegrable (fun X => v X i) := by
  rw [locallyIntegrable_iff] at hv ⊢
  intro k hk
  have := (EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).integrable_comp (hv k hk)
  exact this

/-- Blueprint: lem:c13_bulk_principal_value.  With
`u_ε(X) = ∫_{|z|>ε} K(z) θ_F(X - z) dz`: each truncated integral converges absolutely; off the
graph the desingularized integral `∫ K(z)(θ_F(X-z) - θ_F(X)) dz` converges absolutely and is the
limit of `u_ε(X)` as `ε ↓ 0`; `u_ε → U[F](·,t)` in `L¹_loc` (each `u_ε` integrable on compacts);
and the desingularized expression agrees with `U[F](·,t)` almost everywhere.  No vector principal
value on the graph is asserted. -/
theorem c13_bulk_principal_value {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t : ℝ} (ht : t ∈ I) :
    (∀ ε : ℝ, 0 < ε → ∀ X : c13_E,
      IntegrableOn (fun z => (c13_patch F t).indicator (fun _ => (1 : ℝ)) (X - z) •
        c13_velocity_kernel α c z) {z | ε < ‖z‖}) ∧
    (∀ X : c13_E, X 1 ≠ F (X 0) t →
      Integrable (fun z => ((c13_patch F t).indicator (fun _ => (1 : ℝ)) (X - z) -
          (c13_patch F t).indicator (fun _ => (1 : ℝ)) X) • c13_velocity_kernel α c z) ∧
      Tendsto (fun ε : ℝ => ∫ z in {z : c13_E | ε < ‖z‖},
          (c13_patch F t).indicator (fun _ => (1 : ℝ)) (X - z) • c13_velocity_kernel α c z)
        (𝓝[>] 0)
        (𝓝 (∫ z, ((c13_patch F t).indicator (fun _ => (1 : ℝ)) (X - z) -
          (c13_patch F t).indicator (fun _ => (1 : ℝ)) X) • c13_velocity_kernel α c z))) ∧
    (∀ Q : Set c13_E, IsCompact Q →
      (∀ ε : ℝ, 0 < ε → IntegrableOn (fun X => ∫ z in {z : c13_E | ε < ‖z‖},
          (c13_patch F t).indicator (fun _ => (1 : ℝ)) (X - z) • c13_velocity_kernel α c z) Q) ∧
      Tendsto (fun ε : ℝ => ∫ X in Q, ‖(∫ z in {z : c13_E | ε < ‖z‖},
          (c13_patch F t).indicator (fun _ => (1 : ℝ)) (X - z) • c13_velocity_kernel α c z) -
          c13_graph_velocity α c F X t‖) (𝓝[>] 0) (𝓝 0)) ∧
    (fun X => ∫ z, ((c13_patch F t).indicator (fun _ => (1 : ℝ)) (X - z) -
        (c13_patch F t).indicator (fun _ => (1 : ℝ)) X) • c13_velocity_kernel α c z)
      =ᵐ[volume] (fun X => c13_graph_velocity α c F X t) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨hf, M, hM0, hM⟩ := c13c_aux_slice hF ht
  have hlip : ∀ a b, |F a t - F b t| ≤ M * |a - b| := by
    intro a b
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x => F x t) (s := univ) (x := b)
      (y := a) (fun z _ => (hf.differentiable (by simp)).differentiableAt) (fun z _ => hM z)
      convex_univ (mem_univ _) (mem_univ _)
    simpa using this
  set θ : c13_E → ℝ := (c13_patch F t).indicator (fun _ => (1 : ℝ)) with hθ
  have hc0 : Continuous fun X : c13_E => X 0 := by fun_prop
  have hc1 : Continuous fun X : c13_E => X 1 := by fun_prop
  have hΩm : MeasurableSet (c13_patch F t) :=
    (isOpen_lt hc1 (hf.continuous.comp hc0)).measurableSet
  have hθm : Measurable θ := measurable_const.indicator hΩm
  have hθb : ∀ Y, |θ Y| ≤ 1 := by
    intro Y; by_cases hY : Y ∈ c13_patch F t <;> simp [hθ, hY]
  have hball : ∀ X z : c13_E, (1 + M) * ‖z‖ < |X 1 - F (X 0) t| → θ (X - z) = θ X :=
    fun X z h => c13c_aux_ball_const (f := fun x => F x t) hlip X z h
  obtain ⟨-, -, -, hrad, -⟩ := c13_radial_majorants hα1 hα2 c
  have hoff : ∀ᵐ X : c13_E, X 1 ≠ F (X 0) t := by
    rw [ae_iff]; simpa using (c13_graph_geometry hF).2.1 t ht
  obtain ⟨-, -, -, hVL⟩ := c13_velocity_local_integrable hα1 hα2 c I F hF
  have hmajQ : ∀ Q : Set c13_E, IsCompact Q →
      Integrable (fun q : ℝ × c13_E => ‖c13_pt 1 (deriv (fun x => F x t) q.1)‖ *
        ‖q.2 - c13_pt q.1 (F q.1 t)‖ ^ (-α) * |Q.indicator (fun _ => (1 : ℝ)) q.2|)
        (volume.prod volume) := by
    intro Q hQ
    obtain ⟨Cv', -, hCv'⟩ := hVL {t} (singleton_subset_iff.mpr ht) isCompact_singleton Q hQ
    have hm' := (hCv' t rfl (Q.indicator fun _ => (1 : ℝ))
      ((measurable_const.indicator hQ.measurableSet).aestronglyMeasurable)
      (fun X hX => by simp [hX]) 1 (fun X => by
        by_cases hX : X ∈ Q <;> simp [hX])).1
    rwa [Measure.volume_eq_prod] at hm'
  have hloc := fun Q hQ => c13c_aux_pv_local (c := c) hα1 (fun x => F x t) hM0 hlip θ hθm hθb
    hball hrad hoff Q hQ (hmajQ Q hQ)
  -- pairing identity for the desingularized velocity
  have hpair : ∀ Φ : c13_E → c13_E, ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
      (∫ X, inner ℝ (c13c_aux_u0 α c θ X) (Φ X)) =
        ∫ X, inner ℝ (c13_graph_velocity α c F X t) (Φ X) := by
    intro Φ hΦ hΦc
    obtain ⟨-, -, -, -, e1, e2⟩ := c13_bulk_contour_identity hα1 hα2 (c := c) hF ht Φ hΦ hΦc
    obtain ⟨Cad, -, hAD⟩ := c13_adjoint_integrable hα1 hα2 c
    obtain ⟨hprod, hY, -⟩ := hAD Φ hΦ hΦc
    have hlimR := c13c_aux_adjoint_limit θ hθm hθb Φ hΦ.continuous hprod hY
    obtain ⟨hu, hu0, hT⟩ := hloc (tsupport Φ) hΦc
    obtain ⟨B, hB⟩ : ∃ B, ∀ X, ‖Φ X‖ ≤ B := hΦ.continuous.bounded_above_of_compact_support hΦc
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    have hint : ∀ w : c13_E → c13_E, IntegrableOn w (tsupport Φ) →
        Integrable (fun X => inner ℝ (w X) (Φ X)) := by
      intro w hw
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport Φ) ?_
        fun X hX => by simp [image_eq_zero_of_notMem_tsupport hX]
      refine (hw.norm.mul_const B).mono'
        (hw.aestronglyMeasurable.inner hΦ.continuous.aestronglyMeasurable.restrict)
        (Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact hB X)
    have hlimL : Tendsto (fun ε => ∫ X, inner ℝ (c13c_aux_u α c θ ε X) (Φ X)) (𝓝[>] 0)
        (𝓝 (∫ X, inner ℝ (c13c_aux_u0 α c θ X) (Φ X))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 := hT.const_mul B
      rw [mul_zero] at h0
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hw : IntegrableOn (fun X => c13c_aux_u α c θ ε X - c13c_aux_u0 α c θ X) (tsupport Φ) :=
        (hu ε hε).sub hu0
      rw [← integral_sub (hint _ (hu ε hε)) (hint _ hu0)]
      have : (fun X => inner ℝ (c13c_aux_u α c θ ε X) (Φ X) - inner ℝ (c13c_aux_u0 α c θ X) (Φ X)) =
          fun X => inner ℝ (c13c_aux_u α c θ ε X - c13c_aux_u0 α c θ X) (Φ X) := by
        ext X; rw [inner_sub_left]
      rw [this, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport Φ)
        (fun X hX => by simp [image_eq_zero_of_notMem_tsupport hX]), ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hw.norm.const_mul B)
        (Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [mul_comm B]; gcongr; exact hB X
    have hlimR' : Tendsto (fun ε => ∫ X, inner ℝ (c13c_aux_u α c θ ε X) (Φ X)) (𝓝[>] 0)
        (𝓝 (∫ Y, θ Y * c13_adjoint α c Φ Y)) := by
      refine hlimR.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (c13c_aux_trunc_pairing (c := c) hα0 (hrad ε hε).1 θ hθm hθb Φ hΦ.continuous hΦc).symm
    rw [tendsto_nhds_unique hlimL hlimR', e1, e2]
  -- almost-everywhere identification
  have hU_li : LocallyIntegrable (fun X => c13_graph_velocity α c F X t) :=
    (c13_bulk_contour_identity hα1 hα2 (c := c) hF ht 0 contDiff_const
      HasCompactSupport.zero).2.2.2.1
  have hu0_li : LocallyIntegrable (c13c_aux_u0 α c θ) :=
    locallyIntegrable_iff.mpr fun Q hQ => (hloc Q hQ).2.1
  have hcomp : ∀ i : Fin 2, ∀ᵐ X : c13_E, c13c_aux_u0 α c θ X i = c13_graph_velocity α c F X t i := by
    intro i
    refine ae_eq_of_integral_contDiff_smul_eq (c13c_aux_locInt_apply hu0_li i)
      (c13c_aux_locInt_apply hU_li i) fun g hg hgc => ?_
    have h := hpair (fun X => g X • EuclideanSpace.single i (1 : ℝ)) (hg.smul contDiff_const)
      hgc.smul_right
    simp only [real_inner_smul_right, EuclideanSpace.inner_single_right] at h
    simpa [smul_eq_mul, mul_comm] using h
  have hae : (c13c_aux_u0 α c θ) =ᵐ[volume] (fun X => c13_graph_velocity α c F X t) := by
    filter_upwards [hcomp 0, hcomp 1] with X h0 h1
    ext i; fin_cases i
    · exact h0
    · exact h1
  refine ⟨fun ε hε X => (c13c_aux_trunc_integrable (c := c) hα0 (hrad ε hε).1 θ hθm hθb X).1,
    fun X hX => ?_, fun Q hQ => ?_, hae⟩
  · set δ := |X 1 - F (X 0) t| with hδ
    have hδp : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hX)
    set r := δ / (1 + M) with hr
    have hrp : 0 < r := by positivity
    have hball' : ∀ z : c13_E, ‖z‖ < r → θ (X - z) = θ X := by
      intro z hz
      refine hball X z ?_
      have : (1 + M) * ‖z‖ < (1 + M) * r := by gcongr
      rwa [hr, mul_div_cancel₀ _ (by positivity : (1 + M) ≠ 0)] at this
    obtain ⟨h1, -, h3, -⟩ := c13c_aux_desing (c := c) hα0 (fun r hr => (hrad r hr).1) θ hθm hθb
      X r hrp hball'
    refine ⟨h1, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hrp] with ε hε
    exact (h3 ε hε.1 hε.2).symm
  · obtain ⟨hu, -, hT⟩ := hloc Q hQ
    refine ⟨hu, hT.congr' (Eventually.of_forall fun ε => ?_)⟩
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae] with X hX
    simp only [c13c_aux_u, hX]


end GSQG
