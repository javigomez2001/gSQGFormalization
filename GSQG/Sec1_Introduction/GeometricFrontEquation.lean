import GSQG.Sec3_FixedPoint.MainTheorem

/-!
# Bridges to the literal equations in the paper

The analytic development uses the secant-factored kernel. These lemmas identify it with
`eqn:front_equation` of the paper, including absolute convergence. They add no axioms and
use only elementary facts about the kernel; in particular they do not depend on the analytic
estimates behind `GSQG.main` (which is itself fully proved).
-/

open MeasureTheory Set Filter Real

noncomputable section
namespace GSQG

/-- The factored integrand agrees with the geometric denominator, including on the diagonal. -/
private theorem c01_paper_kernel_eq (p ε : ℝ) (hε : 0 ≤ ε) (f : ℝ → ℝ) (y z : ℝ) :
    (deriv f y - deriv f z) / |y - z| ^ (p + 1) * A_eps p ε (c01_secant f y z) =
      (deriv f y - deriv f z) /
        ((y - z) ^ 2 + ε * (f y - f z) ^ 2) ^ ((p + 1) / 2) := by
  by_cases hyz : y = z
  · subst z; simp
  have hd : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have ha : 0 < |y - z| := abs_pos.mpr hd
  have hb : 0 < 1 + ε * ((f y - f z) / (y - z)) ^ 2 := by positivity
  have he : (y - z) ^ 2 + ε * (f y - f z) ^ 2 =
      |y - z| ^ 2 * (1 + ε * ((f y - f z) / (y - z)) ^ 2) := by
    rw [sq_abs]; field_simp
  have hpw : (|y - z| ^ 2) ^ ((p + 1) / 2) = |y - z| ^ (p + 1) := by
    rw [← Real.rpow_natCast_mul ha.le]
    congr 1
    ring
  simp only [c01_secant, ite_eq_right_iff.mpr (fun h => (hyz h).elim), A_eps]
  rw [show -(p + 1) / 2 = -((p + 1) / 2) by ring, he,
    Real.mul_rpow (sq_nonneg _) hb.le, hpw, Real.rpow_neg hb.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Blueprint: lem:c01_paper_front_equation. The operator in Lean is the absolutely convergent
geometric integral of the paper for every admissible profile. -/
theorem c01_Jfull_paper_kernel (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) (y : ℝ) :
    Integrable (fun z => (deriv f y - deriv f z) /
      ((y - z) ^ 2 + ε * (f y - f z) ^ 2) ^ ((p + 1) / 2)) ∧
    c01_Jfull_eps p ε f y = calpha p * ∫ z,
      (deriv f y - deriv f z) /
        ((y - z) ^ 2 + ε * (f y - f z) ^ 2) ^ ((p + 1) / 2) := by
  obtain ⟨M, hM⟩ := hf.2.1
  obtain ⟨Λ, hΛ, hLip⟩ := c01_aux_lip f hf y
  have hint := (c01_J_well_defined p hp hp1 ε hε f hf M hM y Λ hΛ hLip).1
  have heq := funext (c01_paper_kernel_eq p ε hε f y)
  exact ⟨heq ▸ hint, by unfold c01_Jfull_eps; rw [heq]⟩

/-- Blueprint: lem:c01_paper_front_equation. Every formal classical front solution satisfies the
literal geometric PDE `eqn:front_equation` of the paper, with an absolutely convergent integral. -/
theorem c01_front_equation_paper (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (I : Set ℝ) (F : ℝ → ℝ → ℝ) (hF : gsqg_front_equation p I F) :
    ∀ t ∈ I, ∀ x : ℝ,
      Integrable (fun z => (deriv (fun y => F y t) x - deriv (fun y => F y t) z) /
        ((x - z) ^ 2 + (F x t - F z t) ^ 2) ^ ((p + 1) / 2)) ∧
      deriv (fun s => F x s) t = calpha p * ∫ z,
        (deriv (fun y => F y t) x - deriv (fun y => F y t) z) /
          ((x - z) ^ 2 + (F x t - F z t) ^ 2) ^ ((p + 1) / 2) := by
  intro t ht x
  have h2 := hF.2.1 t ht
  have hf : (fun y => F y t) ∈ c01_admissible_class :=
    ⟨h2.of_le (by norm_num), hF.2.2.2.1 t ht,
      (contDiff_succ_iff_deriv.mp h2).2.2.locallyLipschitz⟩
  obtain ⟨hi, he⟩ := c01_Jfull_paper_kernel p 1 hp hp1 zero_le_one _ hf x
  simpa only [one_mul] using And.intro hi ((hF.2.2.2.2 t ht x).trans he)

end GSQG
