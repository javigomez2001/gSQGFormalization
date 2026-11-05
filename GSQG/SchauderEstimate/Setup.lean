import GSQG.Sec4_Analysis.Equation
import GSQG.AppendixAB.Statements

/-!
# Beyond the paper (Schauder estimate cited in §4): fixed data (blueprint ch. 12)

Blueprint `12_schauder.tex`, def:c12_schauder_data. Cutoffs, the annular symbol, the inverse
kernel, the dyadic blocks and the cutoff commutator. These are total formulas; convergence and
mapping properties are separate lemmas. Fourier convention: `fourierT` (`e^{-ixξ}`) and
`invFourierT` (factor `(2π)⁻¹`), as in `GSQG/Definitions`. The constant of `|D|^p` is `calpha p`, the constant of
`fracD` (equal to `c_p` by `c03_frac_kernel_formula`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-- Blueprint: def:c12_schauder_data.  `η(x) = smoothTransition((49 - 64x²)/13)`: equal to one on
`[-3/4,3/4]`, supported in `[-7/8,7/8]`. -/
def c12_eta (x : ℝ) : ℝ := Real.smoothTransition ((49 - 64 * x ^ 2) / 13)

/-- Blueprint: def:c12_schauder_data.  `φ(ξ) = χ(ξ/2) - χ(ξ)` with `χ = rho`. -/
def c12_annulus (ξ : ℝ) : ℝ := rho (ξ / 2) - rho ξ

/-- Blueprint: def:c12_schauder_data.  `q_p(ξ) = φ(ξ)|ξ|^{-p}` for `ξ ≠ 0`, `q_p(0) = 0`. -/
def c12_inverse_symbol (p ξ : ℝ) : ℝ := if ξ = 0 then 0 else c12_annulus ξ * |ξ| ^ (-p)

/-- Blueprint: def:c12_schauder_data.  `K_p = Re (q_p)^∨`. -/
def c12_kernel (p x : ℝ) : ℝ := (invFourierT (fun ξ => (c12_inverse_symbol p ξ : ℂ)) x).re

/-- Blueprint: def:c12_schauder_data.  `K_{p,j}(x) = 2^{(1-p)j} K_p(2^j x)`. -/
def c12_scaled_kernel (p : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ ((1 - p) * (j : ℝ)) * c12_kernel p ((2 : ℝ) ^ j * x)

/-- Blueprint: def:c12_schauder_data.  `S₀ v = Re (χ v̂)^∨`. -/
def c12_low_block (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (invFourierT (fun ξ => (rho ξ : ℂ) * fourierT (fun y => (v y : ℂ)) ξ) x).re

/-- Blueprint: def:c12_schauder_data.  `Δ_j v = Re (φ(2^{-j}·) v̂)^∨`. -/
def c12_block (j : ℕ) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  (invFourierT (fun ξ => (c12_annulus (ξ / (2 : ℝ) ^ j) : ℂ) * fourierT (fun y => (v y : ℂ)) ξ) x).re

/-- Blueprint: def:c12_schauder_data.  `C_{η,p} w(x) = c_p ∫ (η(x) - η(x-z)) w(x-z) |z|^{-1-p} dz`,
integrand zero at `z = 0`. -/
def c12_commutator (p : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  calpha p * ∫ z, if z = 0 then 0 else (c12_eta x - c12_eta (x - z)) * w (x - z) / |z| ^ (1 + p)

/-! ### Helpers for `c12_cutoffs` -/

theorem c12k_aux_rho_one (ξ : ℝ) (h : |ξ| ≤ 1) : rho ξ = 1 := by
  unfold rho; exact Real.smoothTransition.one_of_one_le (by linarith)

theorem c12k_aux_rho_zero (ξ : ℝ) (h : 2 ≤ |ξ|) : rho ξ = 0 := by
  unfold rho; exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem c12k_aux_rho_smooth : ContDiff ℝ (⊤ : ℕ∞) rho := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    have : ∀ᶠ ξ in 𝓝 (0 : ℝ), |ξ| < 1 := by
      have := (continuous_abs.tendsto (0 : ℝ)); rw [abs_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    filter_upwards [this] with ξ hξ
    exact c12k_aux_rho_one ξ hξ.le
  · unfold rho
    exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.sub (contDiffAt_abs hx))

theorem c12k_aux_near_zero : ∀ᶠ ξ in 𝓝 (0 : ℝ), |ξ| < 1 := by
  have := (continuous_abs.tendsto (0 : ℝ)); rw [abs_zero] at this
  exact this.eventually (gt_mem_nhds one_pos)

theorem c12k_aux_annulus_zero (ξ : ℝ) (h : |ξ| ≤ 1 ∨ 4 ≤ |ξ|) : c12_annulus ξ = 0 := by
  unfold c12_annulus
  rcases h with h | h
  · rw [c12k_aux_rho_one ξ h, c12k_aux_rho_one (ξ / 2) (by rw [abs_div]; norm_num; linarith)]
    ring
  · rw [c12k_aux_rho_zero ξ (by linarith),
      c12k_aux_rho_zero (ξ / 2) (by rw [abs_div, abs_two]; linarith)]
    ring

theorem c12k_aux_tsupport {f : ℝ → ℝ} {S : Set ℝ} (hS : IsClosed S) (h : ∀ x, x ∉ S → f x = 0) :
    tsupport f ⊆ S :=
  closure_minimal (fun x hx => by by_contra hxS; exact hx (h x hxS)) hS

theorem c12k_aux_annulus_set_closed : IsClosed {ξ : ℝ | 1 ≤ |ξ| ∧ |ξ| ≤ 4} :=
  (isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const)

theorem c12k_aux_annulus_set_compact : IsCompact {ξ : ℝ | 1 ≤ |ξ| ∧ |ξ| ≤ 4} :=
  (isCompact_Icc (a := (-4 : ℝ)) (b := 4)).of_isClosed_subset c12k_aux_annulus_set_closed
    (fun _ hξ => abs_le.mp hξ.2)

theorem c12k_aux_out_annulus (ξ : ℝ) (h : ξ ∉ {ξ : ℝ | 1 ≤ |ξ| ∧ |ξ| ≤ 4}) :
    |ξ| ≤ 1 ∨ 4 ≤ |ξ| := by
  simp only [mem_ofPred_eq, not_and_or, not_le] at h
  rcases h with h | h
  · exact Or.inl h.le
  · exact Or.inr h.le

/-- Blueprint: lem:c12_cutoffs.  Properties of `η`, `χ = rho`, `φ` and `q_p`: smoothness, evenness,
range, plateau and support, and vanishing of all derivatives of `φ` and `q_p` at `0`. -/
theorem c12_cutoffs :
    (ContDiff ℝ (⊤ : ℕ∞) c12_eta ∧ (∀ x, c12_eta (-x) = c12_eta x) ∧
      (∀ x, 0 ≤ c12_eta x ∧ c12_eta x ≤ 1) ∧ (∀ x, |x| ≤ 3 / 4 → c12_eta x = 1) ∧
      (∀ x, 7 / 8 ≤ |x| → c12_eta x = 0) ∧ tsupport c12_eta ⊆ Icc (-(7 / 8)) (7 / 8) ∧
      HasCompactSupport c12_eta) ∧
    (ContDiff ℝ (⊤ : ℕ∞) rho ∧ (∀ ξ, rho (-ξ) = rho ξ) ∧ (∀ ξ, 0 ≤ rho ξ ∧ rho ξ ≤ 1) ∧
      (∀ ξ, |ξ| ≤ 1 → rho ξ = 1) ∧ (∀ ξ, 2 ≤ |ξ| → rho ξ = 0) ∧
      tsupport rho ⊆ Icc (-2) 2 ∧ HasCompactSupport rho) ∧
    (ContDiff ℝ (⊤ : ℕ∞) c12_annulus ∧ (∀ ξ, c12_annulus (-ξ) = c12_annulus ξ) ∧
      (∀ ξ, 0 ≤ c12_annulus ξ ∧ c12_annulus ξ ≤ 1) ∧
      (∀ ξ, (|ξ| ≤ 1 ∨ 4 ≤ |ξ|) → c12_annulus ξ = 0) ∧
      tsupport c12_annulus ⊆ {ξ | 1 ≤ |ξ| ∧ |ξ| ≤ 4} ∧ HasCompactSupport c12_annulus ∧
      ∀ m : ℕ, iteratedDeriv m c12_annulus 0 = 0) ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      ContDiff ℝ (⊤ : ℕ∞) (c12_inverse_symbol p) ∧
      (∀ ξ, c12_inverse_symbol p (-ξ) = c12_inverse_symbol p ξ) ∧
      (∀ ξ, (|ξ| ≤ 1 ∨ 4 ≤ |ξ|) → c12_inverse_symbol p ξ = 0) ∧
      tsupport (c12_inverse_symbol p) ⊆ {ξ | 1 ≤ |ξ| ∧ |ξ| ≤ 4} ∧
      HasCompactSupport (c12_inverse_symbol p) ∧
      ∀ m : ℕ, iteratedDeriv m (c12_inverse_symbol p) 0 = 0) := by
  have heta0 : ∀ x : ℝ, 7 / 8 ≤ |x| → c12_eta x = 0 := by
    intro x hx
    unfold c12_eta
    apply Real.smoothTransition.zero_of_nonpos
    have : (7 / 8 : ℝ) ^ 2 ≤ x ^ 2 := by rw [← sq_abs x]; gcongr
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num); nlinarith
  have hetaS : ∀ x : ℝ, x ∉ Icc (-(7 / 8 : ℝ)) (7 / 8) → c12_eta x = 0 := by
    intro x hx
    refine heta0 x ?_
    by_contra h; exact hx (abs_le.mp (not_le.mp h).le)
  have hrhoS : ∀ x : ℝ, x ∉ Icc (-2 : ℝ) 2 → rho x = 0 := by
    intro x hx
    refine c12k_aux_rho_zero x ?_
    by_contra h; exact hx (abs_le.mp (not_le.mp h).le)
  have hphi_sm : ContDiff ℝ (⊤ : ℕ∞) c12_annulus :=
    (c12k_aux_rho_smooth.comp (contDiff_id.div_const 2)).sub c12k_aux_rho_smooth
  have hphiS : ∀ x : ℝ, x ∉ {ξ : ℝ | 1 ≤ |ξ| ∧ |ξ| ≤ 4} → c12_annulus x = 0 :=
    fun x hx => c12k_aux_annulus_zero x (c12k_aux_out_annulus x hx)
  have hphi_loc : c12_annulus =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [c12k_aux_near_zero] with ξ hξ
    exact c12k_aux_annulus_zero ξ (Or.inl hξ.le)
  refine ⟨⟨?_, ?_, ?_, ?_, heta0, c12k_aux_tsupport isClosed_Icc hetaS,
    HasCompactSupport.intro isCompact_Icc hetaS⟩,
    ⟨c12k_aux_rho_smooth, ?_, ?_, c12k_aux_rho_one, c12k_aux_rho_zero,
      c12k_aux_tsupport isClosed_Icc hrhoS, HasCompactSupport.intro isCompact_Icc hrhoS⟩,
    ⟨hphi_sm, ?_, ?_, c12k_aux_annulus_zero,
      c12k_aux_tsupport c12k_aux_annulus_set_closed hphiS,
      HasCompactSupport.intro c12k_aux_annulus_set_compact hphiS, ?_⟩, ?_⟩
  · unfold c12_eta
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub
      (contDiff_const.mul (contDiff_id.pow 2))).div_const _)
  · intro x; simp [c12_eta]
  · exact fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x hx
    unfold c12_eta
    apply Real.smoothTransition.one_of_one_le
    have : x ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by rw [← sq_abs x]; gcongr
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  · intro ξ; simp [rho]
  · exact fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro ξ; simp [c12_annulus, rho, neg_div]
  · intro ξ
    unfold c12_annulus
    have h1 : rho ξ ≤ rho (ξ / 2) := by
      unfold rho
      apply Real.smoothTransition.monotone
      rw [abs_div, abs_two]; linarith [abs_nonneg ξ]
    have h2 : rho (ξ / 2) ≤ 1 := Real.smoothTransition.le_one _
    have h3 : 0 ≤ rho ξ := Real.smoothTransition.nonneg _
    constructor <;> linarith
  · intro m
    rw [hphi_loc.iteratedDeriv_eq]; simp
  · intro p _ _
    have hqS : ∀ x : ℝ, x ∉ {ξ : ℝ | 1 ≤ |ξ| ∧ |ξ| ≤ 4} → c12_inverse_symbol p x = 0 := by
      intro x hx; unfold c12_inverse_symbol; split_ifs <;> simp [hphiS x hx]
    have hq_loc : c12_inverse_symbol p =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [c12k_aux_near_zero] with ξ hξ
      unfold c12_inverse_symbol
      split_ifs <;> simp [c12k_aux_annulus_zero ξ (Or.inl hξ.le)]
    refine ⟨?_, ?_, fun ξ hξ => ?_, c12k_aux_tsupport c12k_aux_annulus_set_closed hqS,
      HasCompactSupport.intro c12k_aux_annulus_set_compact hqS, fun m => ?_⟩
    · rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x = 0
      · subst hx
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hq_loc
      · have hev : c12_inverse_symbol p =ᶠ[𝓝 x] fun ξ => c12_annulus ξ * |ξ| ^ (-p) := by
          filter_upwards [isOpen_ne.mem_nhds hx] with ξ hξ
          simp [c12_inverse_symbol, hξ]
        refine ContDiffAt.congr_of_eventuallyEq ?_ hev
        exact hphi_sm.contDiffAt.mul ((contDiffAt_abs hx).rpow_const_of_ne (abs_ne_zero.mpr hx))
    · simp [c12_inverse_symbol, c12_annulus, rho, neg_div]
    · unfold c12_inverse_symbol; split_ifs <;> simp [c12k_aux_annulus_zero ξ hξ]
    · rw [hq_loc.iteratedDeriv_eq]; simp

end GSQG
