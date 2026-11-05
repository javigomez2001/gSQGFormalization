import GSQG.Sec4_Analysis.Equation

/-!
# Appendices A and B: elementary estimates; stationary and nonstationary phase

The paper, Appendix A (Propositions A.1, A.2) and Appendix B (Lemmas B.1–B.5).
The public statements are proved from the toolbox modules in `GSQG/AppendixAB/`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ## Appendix: elementary estimates -/


/-- Blueprint: lem:c03_nonsmooth_symbol_bounds.  Regularity, support, vanishing at `0` and the
bounds `|∂^l a_{k,j}(ξ)| ≤ C₁ C^k |ξ|^{p+1+j-l}` (`C = C(p)`, `C₁ = C₁(p,χ)`). -/
theorem c03_nonsmooth_symbol_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → (∀ ξ, 2 < |ξ| → χ ξ = 0) →
      (∀ ξ ∈ Icc (-1) 1, χ ξ = 1) → ∃ C₁, 0 < C₁ ∧ ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j ≤ 2 →
      ContDiff ℝ (j + 1 : ℕ) (c03_symbol_akj p χ k j) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c03_symbol_akj p χ k j) {0}ᶜ ∧
      (∀ ξ, 2 < |ξ| → c03_symbol_akj p χ k j ξ = 0) ∧
      (∀ l ≤ j + 1, iteratedDeriv l (c03_symbol_akj p χ k j) 0 = 0) ∧
      ∀ ξ, 0 < |ξ| → |ξ| ≤ 2 → ∀ l ≤ j + 3,
        ‖iteratedDeriv l (c03_symbol_akj p χ k j) ξ‖ ≤ C₁ * C ^ k * |ξ| ^ (p + 1 + j - l) := by
  apply c03c_c03_nonsmooth_symbol_bounds <;> assumption

/-- Blueprint: lem:c03_power_singularity_decay.  If `supp a ⊆ [-2,2]`, `a ∈ C^{n-1}`,
`a ∈ C^{n+1}(ℝ∖0)`, `∂^l a(0) = 0` (`l ≤ n-1`) and `|∂^l a(ξ)| ≤ M|ξ|^{n-1+p-l}`, then
`|ǎ(y)| ≤ C M |y|^{-n-p}` for `|y| ≥ 1` and `|ǎ| ≤ C M`, with `C = C(n,p)`. -/
theorem c03_power_singularity_decay (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C, 0 < C ∧ ∀ M : ℝ, 0 ≤ M → ∀ a : ℝ → ℂ, (∀ ξ, 2 < |ξ| → a ξ = 0) →
      ContDiff ℝ (n - 1 : ℕ) a → ContDiffOn ℝ (n + 1 : ℕ) a {0}ᶜ →
      (∀ l < n, iteratedDeriv l a 0 = 0) →
      (∀ ξ, 0 < |ξ| → |ξ| ≤ 2 → ∀ l ≤ n + 1,
        ‖iteratedDeriv l a ξ‖ ≤ M * |ξ| ^ ((n : ℝ) - 1 + p - l)) →
      (∀ y, 1 ≤ |y| → ‖invFourierT a y‖ ≤ C * M * |y| ^ (-(n : ℝ) - p)) ∧
      ∀ y, ‖invFourierT a y‖ ≤ C * M := by
  apply c03c_c03_power_singularity_decay <;> assumption


/-- Blueprint: prop:appendix_nonsmooth_fourier_inverse.  `m̌_k ∈ C^∞` and
`|∂^j m̌_k(y)| ≤ C₀ C^k ⟨y⟩^{-p-2-j}` for `j ≤ 2`, `k ≥ 0` (`C = C(p)`, `C₀ = C₀(p,χ)`). -/
theorem appendix_nonsmooth_fourier_inverse (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → (∀ ξ, 2 < |ξ| → χ ξ = 0) →
      (∀ ξ ∈ Icc (-1) 1, χ ξ = 1) → ∃ C₀, 0 < C₀ ∧ ∀ k : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (invFourierT (c03_symbol_mk p χ k)) ∧
      ∀ j : ℕ, j ≤ 2 → ∀ y : ℝ,
        ‖iteratedDeriv j (invFourierT (c03_symbol_mk p χ k)) y‖ ≤
          C₀ * C ^ k * jb y ^ (-p - 2 - j) := by
  apply c03c_appendix_nonsmooth_fourier_inverse <;> assumption

/-- `⟨y⟩` is monotone in `|y|`. -/
theorem c03_aux_jb_mono {y R : ℝ} (h : |y| ≤ R) : jb y ≤ jb R := by
  unfold jb
  apply Real.sqrt_le_sqrt
  have : y ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

/-- `⟨y⟩ > 0`. -/
theorem c03_aux_jb_pos (y : ℝ) : 0 < jb y :=
  Real.sqrt_pos.2 (by positivity)

/-- Blueprint: lem:c03_weighted_tail.  Uniform weighted bounds plus local uniform convergence
give the weighted bound for the limit and convergence in the weaker weight. -/
theorem c03_weighted_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (γ γ' : ℝ) (hγ' : 0 < γ') (hγγ' : γ' < γ) (ω : ℝ → ℝ) (hω : ∀ y, 0 < ω y)
    (hωb : ∀ R : ℝ, ∃ B, ∀ y ∈ Icc (-R) R, ω y ≤ B)
    (h : ℕ → ℝ → E) (hlim : ℝ → E)
    (hloc : ∀ R : ℝ, (∀ k, MemLp (h k) ∞ (volume.restrict (Ioo (-R) R))) ∧
      MemLp hlim ∞ (volume.restrict (Ioo (-R) R)))
    (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hbd : ∀ k, eLpNorm (fun y => (jb y ^ γ * ω y) • h k y) ∞ volume ≤ M)
    (hconv : ∀ R : ℝ, Tendsto (fun k => eLpNorm (h k - hlim) ∞ (volume.restrict (Ioo (-R) R)))
      atTop (𝓝 0)) :
    eLpNorm (fun y => (jb y ^ γ * ω y) • hlim y) ∞ volume ≤ M ∧
    Tendsto (fun k => eLpNorm (fun y => (jb y ^ γ' * ω y) • (h k y - hlim y)) ∞ volume)
      atTop (𝓝 0) := by
  set w : ℝ → ℝ := fun y => jb y ^ γ * ω y with hw
  have hwpos : ∀ y, 0 < w y := fun y => mul_pos (Real.rpow_pos_of_pos (c03_aux_jb_pos y) _) (hω y)
  set e : ℝ → ℕ → ℝ≥0∞ := fun R k => eLpNorm (h k - hlim) ∞ (volume.restrict (Ioo (-R) R))
  -- local a.e. bounds
  have hlocae : ∀ R : ℝ, ∀ᵐ y ∂volume, y ∈ Ioo (-R) R → ∀ k, ‖h k y - hlim y‖ₑ ≤ e R k := by
    intro R
    rw [← ae_restrict_iff' measurableSet_Ioo, ae_all_iff]
    intro k
    filter_upwards [ae_le_eLpNormEssSup (f := h k - hlim)
      (μ := volume.restrict (Ioo (-R) R))] with y hy
    exact hy.trans eLpNormEssSup_le_eLpNorm_top
  have hlocae' : ∀ᵐ y ∂volume, ∀ n : ℕ, y ∈ Ioo (-(n : ℝ)) n → ∀ k, ‖h k y - hlim y‖ₑ ≤ e n k :=
    ae_all_iff.2 fun n => hlocae n
  have hbdae : ∀ᵐ y ∂volume, ∀ k, ‖w y • h k y‖ₑ ≤ M := by
    rw [ae_all_iff]; intro k
    filter_upwards [ae_le_eLpNormEssSup (f := fun y => w y • h k y) (μ := volume)] with y hy
    exact hy.trans (eLpNormEssSup_le_eLpNorm_top.trans (hbd k))
  -- pointwise a.e. convergence
  have hptw : ∀ᵐ y ∂volume, Tendsto (fun k => h k y) atTop (𝓝 (hlim y)) := by
    filter_upwards [hlocae'] with y hy
    obtain ⟨n, hn⟩ := exists_nat_gt |y|
    have hmem : y ∈ Ioo (-(n : ℝ)) n := ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv n)
      (fun _ => zero_le) (fun k => ?_)
    rw [edist_eq_enorm_sub]; exact hy n hmem k
  have hmeas : ∀ k, AEStronglyMeasurable (fun y => w y • h k y) volume := by
    intro k; by_contra hc
    have := hbd k
    rw [eLpNorm_of_not_aestronglyMeasurable hc] at this
    exact hM (top_le_iff.1 this)
  have hmeaslim : AEStronglyMeasurable (fun y => w y • hlim y) volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop hmeas ?_
    filter_upwards [hptw] with y hy
    exact hy.const_smul (w y)
  have hlimae : ∀ᵐ y ∂volume, ‖w y • hlim y‖ₑ ≤ M := by
    filter_upwards [hptw, hbdae] with y hy hb
    exact le_of_tendsto' ((hy.const_smul (w y)).enorm) hb
  have part1 : eLpNorm (fun y => w y • hlim y) ∞ volume ≤ M := by
    rw [eLpNorm_exponent_top hmeaslim]
    exact essSup_le_of_ae_le M hlimae
  refine ⟨part1, ?_⟩
  -- part 2
  set w' : ℝ → ℝ := fun y => jb y ^ γ' * ω y with hw'
  have hsplit : ∀ y, w' y = jb y ^ (γ' - γ) * w y := by
    intro y; simp only [hw', hw]
    rw [← mul_assoc, ← Real.rpow_add (c03_aux_jb_pos y)]; ring_nf
  have hcj : Continuous (fun y => jb y ^ (γ' - γ)) := by
    unfold jb
    exact (Real.continuous_sqrt.comp (by fun_prop)).rpow_const
      (fun y => Or.inl (Real.sqrt_pos.2 (by positivity)).ne')
  have hmeas2 : ∀ k, AEStronglyMeasurable (fun y => w' y • (h k y - hlim y)) volume := by
    intro k
    have : (fun y => w' y • (h k y - hlim y)) =
        fun y => jb y ^ (γ' - γ) • (w y • h k y - w y • hlim y) := by
      funext y; rw [hsplit, mul_smul, smul_sub]
    rw [this]
    exact hcj.aestronglyMeasurable.smul ((hmeas k).sub hmeaslim)
  -- the key bound
  have hkey : ∀ R : ℝ, 0 ≤ R → ∀ k, eLpNorm (fun y => w' y • (h k y - hlim y)) ∞ volume ≤
      ENNReal.ofReal (jb R ^ γ' * (hωb R).choose) * e R k +
        ENNReal.ofReal (jb R ^ (γ' - γ)) * (M + M) := by
    intro R hR k
    rw [eLpNorm_exponent_top (hmeas2 k)]
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hlocae R, hbdae, hlimae] with y hy hb hl
    rw [enorm_smul, Real.enorm_eq_ofReal (le_of_lt (by
      simp only [hw']; exact mul_pos (Real.rpow_pos_of_pos (c03_aux_jb_pos y) _) (hω y)))]
    by_cases hyR : y ∈ Ioo (-R) R
    · refine le_add_right ?_
      have hy' : |y| ≤ R := abs_le.2 ⟨hyR.1.le, hyR.2.le⟩
      have hwle : w' y ≤ jb R ^ γ' * (hωb R).choose := by
        simp only [hw']
        exact mul_le_mul (Real.rpow_le_rpow (c03_aux_jb_pos y).le (c03_aux_jb_mono hy') hγ'.le)
          ((hωb R).choose_spec y (Ioo_subset_Icc_self hyR)) (hω y).le
          (Real.rpow_nonneg (c03_aux_jb_pos R).le _)
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hwle) (hy hyR k)
    · refine le_add_left ?_
      have hy' : R ≤ |y| := by
        by_contra hc; push Not at hc
        exact hyR ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
      have hjb : jb R ≤ jb y := by
        have := c03_aux_jb_mono (y := R) (R := |y|) (by rw [abs_of_nonneg hR]; exact hy')
        unfold jb at this ⊢; rwa [sq_abs] at this
      rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg (c03_aux_jb_pos y).le _), mul_assoc,
        ← Real.enorm_eq_ofReal (hwpos y).le, ← enorm_smul, smul_sub]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos (c03_aux_jb_pos R) hjb (by linarith))) ?_
      exact enorm_sub_le.trans (add_le_add (hb k) hl)
  -- conclude
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hRt : Tendsto (fun R : ℝ => ENNReal.ofReal (jb R ^ (γ' - γ)) * (M + M)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => jb R ^ (γ' - γ)) atTop (𝓝 0) := by
      have hjbt : Tendsto jb atTop atTop := by
        refine tendsto_atTop_mono (fun R => ?_) tendsto_id
        exact (le_abs_self R).trans (by unfold jb; exact Real.abs_le_sqrt (by linarith [sq_nonneg R]))
      exact (tendsto_rpow_neg_atTop (by linarith : 0 < γ - γ')).comp hjbt |>.congr
        (fun R => by simp [neg_sub])
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr (ENNReal.add_ne_top.2 ⟨hM, hM⟩))
  obtain ⟨R, hR, hR0⟩ := ((ENNReal.tendsto_nhds_zero.1 hRt (ε / 2)
    (ENNReal.half_pos hε.ne')).and (eventually_ge_atTop (0 : ℝ))).exists
  have hkt : Tendsto (fun k => ENNReal.ofReal (jb R ^ γ' * (hωb R).choose) * e R k) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hconv R) (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hkt (ε / 2) (ENNReal.half_pos hε.ne')] with k hk
  exact (hkey R hR0 k).trans ((add_le_add hk hR).trans (ENNReal.add_halves ε).le)

/-- `[0,∞]`-valued weighted tail lemma (the version used for the `X_γ`, `Y_γ` norms):
uniform `⟨y⟩^γ`-bounds, triangle inequalities and local convergence of the differences give
the bound for the limit and convergence of the differences in the weight `⟨y⟩^{γ'}`. -/
theorem c03_aux_tail (μ : Measure ℝ) (γ γ' : ℝ) (hγ' : 0 < γ') (hγγ' : γ' < γ)
    (A : ℕ → ℝ → ℝ≥0∞) (Al : ℝ → ℝ≥0∞) (D : ℕ → ℝ → ℝ≥0∞) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbd : ∀ k, essSup (fun y => ENNReal.ofReal (jb y ^ γ) * A k y) μ ≤ B)
    (htri1 : ∀ k, ∀ᵐ y ∂μ, Al y ≤ A k y + D k y)
    (htri2 : ∀ k, ∀ᵐ y ∂μ, D k y ≤ A k y + Al y)
    (hloc : ∀ R : ℝ, ∃ e : ℕ → ℝ≥0∞, Tendsto e atTop (𝓝 0) ∧
      ∀ k, ∀ᵐ y ∂μ, |y| < R → D k y ≤ e k) :
    essSup (fun y => ENNReal.ofReal (jb y ^ γ) * Al y) μ ≤ B ∧
    Tendsto (fun k => essSup (fun y => ENNReal.ofReal (jb y ^ γ') * D k y) μ) atTop (𝓝 0) := by
  choose e he hle using hloc
  set W : ℝ → ℝ → ℝ≥0∞ := fun g y => ENNReal.ofReal (jb y ^ g) with hW
  have hbdae : ∀ᵐ y ∂μ, ∀ k, W γ y * A k y ≤ B := by
    rw [ae_all_iff]; intro k
    filter_upwards [ENNReal.ae_le_essSup (fun y => ENNReal.ofReal (jb y ^ γ) * A k y) (μ := μ)]
      with y hy
    exact hy.trans (hbd k)
  have hlocae : ∀ᵐ y : ℝ ∂μ, ∀ n : ℕ, ∀ k, |y| < n → D k y ≤ e n k := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; exact fun k => hle n k
  have hD0 : ∀ᵐ y ∂μ, Tendsto (fun k => D k y) atTop (𝓝 0) := by
    filter_upwards [hlocae] with y hy
    obtain ⟨n, hn⟩ := exists_nat_gt |y|
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (he n)
      (fun _ => bot_le) (fun k => hy n k hn)
  have hlimae : ∀ᵐ y ∂μ, W γ y * Al y ≤ B := by
    rw [← ae_all_iff] at htri1
    filter_upwards [hbdae, htri1, hD0] with y hb ht hd
    have hT : Tendsto (fun k => B + W γ y * D k y) atTop (𝓝 (B + W γ y * 0)) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hd (Or.inr ENNReal.ofReal_ne_top))
    rw [mul_zero, add_zero] at hT
    refine ge_of_tendsto' hT (fun k => ?_)
    calc W γ y * Al y ≤ W γ y * (A k y + D k y) := by gcongr; exact ht k
      _ = W γ y * A k y + W γ y * D k y := mul_add _ _ _
      _ ≤ B + W γ y * D k y := add_le_add (hb k) le_rfl
  have part1 : essSup (fun y => W γ y * Al y) μ ≤ B := essSup_le_of_ae_le B hlimae
  refine ⟨part1, ?_⟩
  have hsplit : ∀ y, W γ' y = W (γ' - γ) y * W γ y := by
    intro y; simp only [hW]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (c03_aux_jb_pos y).le _),
      ← Real.rpow_add (c03_aux_jb_pos y)]; ring_nf
  have hkey : ∀ R : ℝ, 0 ≤ R → ∀ k, essSup (fun y => W γ' y * D k y) μ ≤
      W γ' R * e R k + W (γ' - γ) R * (B + B) := by
    intro R hR k
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hle R k, hbdae, hlimae, htri2 k] with y hy hb hl ht
    by_cases hyR : |y| < R
    · refine le_add_right ?_
      have hwle : W γ' y ≤ W γ' R := ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (c03_aux_jb_pos y).le
          (c03_aux_jb_mono hyR.le)
          hγ'.le)
      exact mul_le_mul' hwle (hy hyR)
    · refine le_add_left ?_
      push Not at hyR
      have hjb : jb R ≤ jb y := by
        have := c03_aux_jb_mono (y := R) (R := |y|) (by rw [abs_of_nonneg hR]; exact hyR)
        unfold jb at this ⊢; rwa [sq_abs] at this
      rw [hsplit, mul_assoc]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos (c03_aux_jb_pos R) hjb (by linarith))) ?_
      calc W γ y * D k y ≤ W γ y * (A k y + Al y) := by gcongr
        _ = W γ y * A k y + W γ y * Al y := mul_add _ _ _
        _ ≤ B + B := add_le_add (hb k) hl
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hRt : Tendsto (fun R : ℝ => W (γ' - γ) R * (B + B)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => jb R ^ (γ' - γ)) atTop (𝓝 0) := by
      have hjbt : Tendsto jb atTop atTop := by
        refine tendsto_atTop_mono (fun R => ?_) tendsto_id
        exact (le_abs_self R).trans (by unfold jb; exact Real.abs_le_sqrt (by linarith [sq_nonneg R]))
      exact (tendsto_rpow_neg_atTop (by linarith : 0 < γ - γ')).comp hjbt |>.congr
        (fun R => by simp [neg_sub])
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr (ENNReal.add_ne_top.2 ⟨hB, hB⟩))
  obtain ⟨R, hR, hR0⟩ := ((ENNReal.tendsto_nhds_zero.1 hRt (ε / 2)
    (ENNReal.half_pos hε.ne')).and (eventually_ge_atTop (0 : ℝ))).exists
  have hkt : Tendsto (fun k => W γ' R * e R k) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (he R) (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hkt (ε / 2) (ENNReal.half_pos hε.ne')] with k hk
  exact (hkey R hR0 k).trans ((add_le_add hk hR).trans (ENNReal.add_halves ε).le)

/-- Local a.e. bound from an `L^∞(-R,R)` norm. -/
theorem c03_aux_loc_ae (f : ℝ → ℝ) (R : ℝ) :
    ∀ᵐ y ∂volume, |y| < R → ‖f y‖ₑ ≤ eLpNorm f ∞ (volume.restrict (Ioo (-R) R)) := by
  have h := ae_le_eLpNormEssSup (f := f) (μ := volume.restrict (Ioo (-R) R))
  rw [ae_restrict_iff' measurableSet_Ioo] at h
  filter_upwards [h] with y hy hyR
  exact (hy (abs_lt.1 hyR)).trans eLpNormEssSup_le_eLpNorm_top

/-- One half-line of the `X_γ`/`Y_γ` norm: the convergence statement of
prop:appendix_convergence for `‖u₀‖ + w₁‖u₁‖ + w₂‖u₂‖`. -/
theorem c03_aux_conv_half (H : Set ℝ) (γ γ' : ℝ) (hγ' : 0 < γ') (hγγ' : γ' < γ)
    (w1 w2 : ℝ → ℝ) (hw0 : ∀ y, 0 ≤ w1 y ∧ 0 ≤ w2 y)
    (hwb : ∀ R : ℝ, ∃ C, 0 ≤ C ∧ ∀ y, |y| < R → w1 y ≤ C ∧ w2 y ≤ C)
    (u0 u1 u2 d0 d1 d2 : ℕ → ℝ → ℝ) (v0 v1 v2 : ℝ → ℝ)
    (hd : ∀ k, ∀ᵐ y ∂volume, d0 k y = u0 k y - v0 y ∧ d1 k y = u1 k y - v1 y ∧
      d2 k y = u2 k y - v2 y)
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbd : ∀ k, essSup (fun y => ENNReal.ofReal (jb y ^ γ *
      (‖u0 k y‖ + w1 y * ‖u1 k y‖ + w2 y * ‖u2 k y‖))) (volume.restrict H) ≤ B)
    (hconv : ∀ R : ℝ, Tendsto (fun k =>
      eLpNorm (fun y => u0 k y - v0 y) ∞ (volume.restrict (Ioo (-R) R)) +
      eLpNorm (fun y => u1 k y - v1 y) ∞ (volume.restrict (Ioo (-R) R)) +
      eLpNorm (fun y => u2 k y - v2 y) ∞ (volume.restrict (Ioo (-R) R))) atTop (𝓝 0)) :
    essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖v0 y‖ + w1 y * ‖v1 y‖ + w2 y * ‖v2 y‖)))
      (volume.restrict H) ≤ B ∧
    Tendsto (fun k => essSup (fun y => ENNReal.ofReal (jb y ^ γ' *
      (‖d0 k y‖ + w1 y * ‖d1 k y‖ + w2 y * ‖d2 k y‖))) (volume.restrict H)) atTop (𝓝 0) := by
  have hmul : ∀ (g y X : ℝ), ENNReal.ofReal (jb y ^ g * X) =
      ENNReal.ofReal (jb y ^ g) * ENNReal.ofReal X := fun g y X =>
    ENNReal.ofReal_mul (Real.rpow_nonneg (c03_aux_jb_pos y).le _)
  simp only [hmul] at hbd ⊢
  have htri : ∀ a b : ℝ, |b| ≤ |a| + |a - b| ∧ |a - b| ≤ |a| + |b| := fun a b => by
    constructor
    · have := abs_sub a (a - b); rwa [sub_sub_cancel] at this
    · exact abs_sub _ _
  have hS : ∀ (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ) (y : ℝ), c0 = a0 - b0 → c1 = a1 - b1 → c2 = a2 - b2 →
      ENNReal.ofReal (‖b0‖ + w1 y * ‖b1‖ + w2 y * ‖b2‖) ≤
        ENNReal.ofReal (‖a0‖ + w1 y * ‖a1‖ + w2 y * ‖a2‖) +
          ENNReal.ofReal (‖c0‖ + w1 y * ‖c1‖ + w2 y * ‖c2‖) ∧
      ENNReal.ofReal (‖c0‖ + w1 y * ‖c1‖ + w2 y * ‖c2‖) ≤
        ENNReal.ofReal (‖a0‖ + w1 y * ‖a1‖ + w2 y * ‖a2‖) +
          ENNReal.ofReal (‖b0‖ + w1 y * ‖b1‖ + w2 y * ‖b2‖) := by
    intro a0 a1 a2 b0 b1 b2 c0 c1 c2 y h0 h1 h2
    subst h0 h1 h2
    simp only [Real.norm_eq_abs]
    obtain ⟨hw1, hw2⟩ := hw0 y
    have t0 := htri a0 b0; have t1 := htri a1 b1; have t2 := htri a2 b2
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    constructor <;> apply ENNReal.ofReal_le_ofReal <;> nlinarith
  refine c03_aux_tail (volume.restrict H) γ γ' hγ' hγγ'
    (fun k y => ENNReal.ofReal (‖u0 k y‖ + w1 y * ‖u1 k y‖ + w2 y * ‖u2 k y‖))
    (fun y => ENNReal.ofReal (‖v0 y‖ + w1 y * ‖v1 y‖ + w2 y * ‖v2 y‖))
    (fun k y => ENNReal.ofReal (‖d0 k y‖ + w1 y * ‖d1 k y‖ + w2 y * ‖d2 k y‖)) B hB hbd
    (fun k => ae_restrict_of_ae ((hd k).mono fun y hy => (hS _ _ _ _ _ _ _ _ _ y hy.1 hy.2.1 hy.2.2).1))
    (fun k => ae_restrict_of_ae ((hd k).mono fun y hy => (hS _ _ _ _ _ _ _ _ _ y hy.1 hy.2.1 hy.2.2).2))
    (fun R => ?_)
  obtain ⟨C, hC0, hC⟩ := hwb R
  set E : ℕ → ℝ≥0∞ := fun k =>
      eLpNorm (fun y => u0 k y - v0 y) ∞ (volume.restrict (Ioo (-R) R)) +
      eLpNorm (fun y => u1 k y - v1 y) ∞ (volume.restrict (Ioo (-R) R)) +
      eLpNorm (fun y => u2 k y - v2 y) ∞ (volume.restrict (Ioo (-R) R))
  refine ⟨fun k => ENNReal.ofReal (1 + C) * E k, ?_, fun k => ae_restrict_of_ae ?_⟩
  · simpa using ENNReal.Tendsto.const_mul (hconv R) (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [hd k, c03_aux_loc_ae (fun y => u0 k y - v0 y) R,
    c03_aux_loc_ae (fun y => u1 k y - v1 y) R, c03_aux_loc_ae (fun y => u2 k y - v2 y) R]
    with y hy h0 h1 h2 hyR
  obtain ⟨e0, e1, e2⟩ := hy
  obtain ⟨hw1, hw2⟩ := hw0 y
  obtain ⟨hC1, hC2⟩ := hC y hyR
  simp only [Real.norm_eq_abs]
  rw [e0, e1, e2]
  have h0' := h0 hyR; have h1' := h1 hyR; have h2' := h2 hyR
  rw [Real.enorm_eq_ofReal_abs] at h0' h1' h2'
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + C) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hCle : ENNReal.ofReal C ≤ ENNReal.ofReal (1 + C) := ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (|u0 k y - v0 y| + w1 y * |u1 k y - v1 y| + w2 y * |u2 k y - v2 y|)
      ≤ ENNReal.ofReal (|u0 k y - v0 y|) + ENNReal.ofReal C * ENNReal.ofReal |u1 k y - v1 y| +
          ENNReal.ofReal C * ENNReal.ofReal |u2 k y - v2 y| := by
        rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_mul hC0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        gcongr
    _ ≤ ENNReal.ofReal (1 + C) * eLpNorm (fun y => u0 k y - v0 y) ∞ (volume.restrict (Ioo (-R) R)) +
          ENNReal.ofReal (1 + C) * eLpNorm (fun y => u1 k y - v1 y) ∞ (volume.restrict (Ioo (-R) R)) +
          ENNReal.ofReal (1 + C) * eLpNorm (fun y => u2 k y - v2 y) ∞ (volume.restrict (Ioo (-R) R)) := by
        gcongr
        exact h0'.trans (le_mul_of_one_le_left bot_le hone)
    _ = ENNReal.ofReal (1 + C) * E k := by simp only [E]; ring

/-- Rademacher on `ℝ`: a locally Lipschitz function is differentiable a.e. -/
theorem c03_aux_ae_differentiable {f : ℝ → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ f x := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIcc (-(n:ℝ)) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨K, hK⟩ := (hf.locallyLipschitzOn (s := uIcc (-(n:ℝ)) n)).exists_lipschitzOnWith_of_compact
      isCompact_uIcc
    exact hK.absolutelyContinuousOnInterval.ae_differentiableAt
  rw [← ae_all_iff] at h
  filter_upwards [h] with x hx
  apply hx (Nat.ceil |x|)
  have h1 := Nat.le_ceil |x|
  rw [uIcc_of_le (by linarith [abs_nonneg x])]
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

/-- `⟨y⟩ ≥ 1`. -/
theorem c03_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := by
  unfold jb
  have h : (1 : ℝ) ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg y]
  calc (1 : ℝ) = Real.sqrt 1 := by simp
    _ ≤ Real.sqrt (1 + y ^ 2) := Real.sqrt_le_sqrt h

/-- Blueprint: prop:appendix_convergence.  Bounded sequences in `X_γ` (resp. `Y_γ`) converging
in `W^{2,∞}_loc` (resp. `W^{1,∞}_loc`) converge in `X_{γ'}` (resp. `Y_{γ'}`), `γ' < γ`, and the
limit is in `X_γ` (resp. `Y_γ`). -/
theorem appendix_convergence (p γ γ' : ℝ) (hp : 0 < p) (hγ' : 0 < γ') (hγγ' : γ' < γ) :
    (∀ (g : ℕ → ℝ → ℝ) (glim : ℝ → ℝ), (∀ k, g k ∈ X_gamma p γ) →
      (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ k, X_gamma_norm p γ (g k) ≤ B) → W2inftyLoc glim →
      (∀ R : ℝ, Tendsto (fun k =>
        eLpNorm (g k - glim) ∞ (volume.restrict (Ioo (-R) R)) +
        eLpNorm (deriv (g k) - deriv glim) ∞ (volume.restrict (Ioo (-R) R)) +
        eLpNorm (deriv (deriv (g k)) - deriv (deriv glim)) ∞ (volume.restrict (Ioo (-R) R)))
        atTop (𝓝 0)) →
      glim ∈ X_gamma p γ ∧ Tendsto (fun k => X_gamma_norm p γ' (g k - glim)) atTop (𝓝 0)) ∧
    (∀ (G : ℕ → ℝ → ℝ) (Glim : ℝ → ℝ), (∀ k, G k ∈ Y_gamma p γ) →
      (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ k, Y_gamma_norm p γ (G k) ≤ B) → W1inftyLoc Glim →
      (∀ R : ℝ, Tendsto (fun k =>
        eLpNorm (G k - Glim) ∞ (volume.restrict (Ioo (-R) R)) +
        eLpNorm (deriv (G k) - deriv Glim) ∞ (volume.restrict (Ioo (-R) R)))
        atTop (𝓝 0)) →
      Glim ∈ Y_gamma p γ ∧ Tendsto (fun k => Y_gamma_norm p γ' (G k - Glim)) atTop (𝓝 0)) := by
  have hjb0 : ∀ y, 0 ≤ jb y := fun y => (c03_aux_jb_pos y).le
  have hwP : ∀ R : ℝ, ∃ C, 0 ≤ C ∧ ∀ y, |y| < R →
      jb y ^ (-1 / p) ≤ C ∧ jb y ^ (-2 / p) ≤ C := fun R =>
    ⟨1, zero_le_one, fun y _ => ⟨Real.rpow_le_one_of_one_le_of_nonpos (c03_aux_one_le_jb y)
      (by rw [neg_div]; exact neg_nonpos.2 (by positivity)),
      Real.rpow_le_one_of_one_le_of_nonpos (c03_aux_one_le_jb y)
      (by rw [neg_div]; exact neg_nonpos.2 (by positivity))⟩⟩
  have hwM : ∀ R : ℝ, ∃ C, 0 ≤ C ∧ ∀ y, |y| < R → jb y ≤ C ∧ jb y ^ (2 : ℕ) ≤ C := fun R =>
    ⟨jb R + jb R ^ 2, by positivity [hjb0 R], fun y hy => by
      have h1 : jb y ≤ jb R := c03_aux_jb_mono hy.le
      have h2 : jb y ^ 2 ≤ jb R ^ 2 := pow_le_pow_left₀ (hjb0 y) h1 2
      constructor <;> nlinarith [hjb0 R, hjb0 y]⟩
  constructor
  · intro g glim hg ⟨B, hB, hbdB⟩ hgl hconv
    have hd : ∀ k, ∀ᵐ y ∂volume, (g k - glim) y = g k y - glim y ∧
        deriv (g k - glim) y = deriv (g k) y - deriv glim y ∧
        deriv (deriv (g k - glim)) y = deriv (deriv (g k)) y - deriv (deriv glim) y := by
      intro k
      have hgk := (hg k).1
      have he : deriv (g k - glim) = fun y => deriv (g k) y - deriv glim y := funext fun y =>
        deriv_sub (hgk.1.differentiable one_ne_zero y) (hgl.1.differentiable one_ne_zero y)
      filter_upwards [c03_aux_ae_differentiable hgk.2, c03_aux_ae_differentiable hgl.2]
        with y h1 h2
      refine ⟨rfl, by rw [he], ?_⟩
      rw [he]; exact deriv_sub h1 h2
    have hP := c03_aux_conv_half (Ici 0) γ γ' hγ' hγγ' (fun y => jb y ^ (-1 / p))
      (fun y => jb y ^ (-2 / p)) (fun y => ⟨by positivity [hjb0 y], by positivity [hjb0 y]⟩) hwP
      g (fun k => deriv (g k)) (fun k => deriv (deriv (g k)))
      (fun k => g k - glim) (fun k => deriv (g k - glim)) (fun k => deriv (deriv (g k - glim)))
      glim (deriv glim) (deriv (deriv glim)) hd B hB
      (fun k => le_trans le_self_add (hbdB k)) hconv
    have hM := c03_aux_conv_half (Iic 0) γ γ' hγ' hγγ' (fun y => jb y)
      (fun y => jb y ^ (2 : ℕ)) (fun y => ⟨hjb0 y, by positivity⟩) hwM
      g (fun k => deriv (g k)) (fun k => deriv (deriv (g k)))
      (fun k => g k - glim) (fun k => deriv (g k - glim)) (fun k => deriv (deriv (g k - glim)))
      glim (deriv glim) (deriv (deriv glim)) hd B hB
      (fun k => le_trans le_add_self (hbdB k)) hconv
    refine ⟨⟨hgl, ?_⟩, ?_⟩
    · unfold X_gamma_norm
      exact lt_of_le_of_lt (add_le_add hP.1 hM.1) (ENNReal.add_lt_top.2 ⟨hB.lt_top, hB.lt_top⟩)
    · unfold X_gamma_norm
      simpa using hP.2.add hM.2
  · intro G Glim hG ⟨B, hB, hbdB⟩ hGl hconv
    have hd : ∀ k, ∀ᵐ y ∂volume, (G k - Glim) y = G k y - Glim y ∧
        deriv (G k - Glim) y = deriv (G k) y - deriv Glim y ∧
        (fun (_ : ℕ) (_ : ℝ) => (0 : ℝ)) k y = (fun (_ : ℕ) (_ : ℝ) => (0 : ℝ)) k y -
          (fun (_ : ℝ) => (0 : ℝ)) y := by
      intro k
      filter_upwards [c03_aux_ae_differentiable (hG k).1, c03_aux_ae_differentiable hGl]
        with y h1 h2
      exact ⟨rfl, deriv_sub h1 h2, by simp⟩
    have hwP' : ∀ R : ℝ, ∃ C, 0 ≤ C ∧ ∀ y, |y| < R →
        jb y ^ (-1 / p) ≤ C ∧ (fun _ : ℝ => (0 : ℝ)) y ≤ C := fun R => by
      obtain ⟨C, hC0, hC⟩ := hwP R
      exact ⟨C, hC0, fun y hy => ⟨(hC y hy).1, hC0⟩⟩
    have hwM' : ∀ R : ℝ, ∃ C, 0 ≤ C ∧ ∀ y, |y| < R → jb y ≤ C ∧ (fun _ : ℝ => (0 : ℝ)) y ≤ C :=
      fun R => by
      obtain ⟨C, hC0, hC⟩ := hwM R
      exact ⟨C, hC0, fun y hy => ⟨(hC y hy).1, hC0⟩⟩
    have hconv' : ∀ R : ℝ, Tendsto (fun k =>
        eLpNorm (fun y => G k y - Glim y) ∞ (volume.restrict (Ioo (-R) R)) +
        eLpNorm (fun y => deriv (G k) y - deriv Glim y) ∞ (volume.restrict (Ioo (-R) R)) +
        eLpNorm (fun y => (fun (_ : ℕ) (_ : ℝ) => (0 : ℝ)) k y - (fun (_ : ℝ) => (0 : ℝ)) y) ∞
          (volume.restrict (Ioo (-R) R))) atTop (𝓝 0) := fun R => by
      refine (hconv R).congr (fun k => ?_)
      rw [show (fun y : ℝ => (fun (_ : ℕ) (_ : ℝ) => (0:ℝ)) k y - (fun (_ : ℝ) => (0:ℝ)) y) =
        fun _ => (0:ℝ) from funext fun _ => sub_self 0, eLpNorm_fun_zero, add_zero]
      rfl
    have hP := c03_aux_conv_half (Ici 0) γ γ' hγ' hγγ' (fun y => jb y ^ (-1 / p))
      (fun _ => 0) (fun y => ⟨by positivity [hjb0 y], le_rfl⟩) hwP'
      G (fun k => deriv (G k)) (fun _ _ => 0)
      (fun k => G k - Glim) (fun k => deriv (G k - Glim)) (fun _ _ => 0)
      Glim (deriv Glim) (fun _ => 0) hd B hB
      (fun k => by simpa using le_trans le_self_add (hbdB k)) hconv'
    have hM := c03_aux_conv_half (Iic 0) γ γ' hγ' hγγ' (fun y => jb y)
      (fun _ => 0) (fun y => ⟨hjb0 y, le_rfl⟩) hwM'
      G (fun k => deriv (G k)) (fun _ _ => 0)
      (fun k => G k - Glim) (fun k => deriv (G k - Glim)) (fun _ _ => 0)
      Glim (deriv Glim) (fun _ => 0) hd B hB
      (fun k => by simpa using le_trans le_add_self (hbdB k)) hconv'
    simp only [norm_zero, mul_zero, add_zero] at hP hM
    refine ⟨⟨hGl, ?_⟩, ?_⟩
    · unfold Y_gamma_norm
      exact lt_of_le_of_lt (add_le_add hP.1 hM.1) (ENNReal.add_lt_top.2 ⟨hB.lt_top, hB.lt_top⟩)
    · unfold Y_gamma_norm
      simpa using hP.2.add hM.2

/-! ## Appendix: stationary and nonstationary phase -/

/-! ### Van der Corput -/

/-! The van der Corput helpers live in `GSQG/AppendixAB/PhaseToolbox.lean` (`c03sp_v_aux_*`). -/

/-- Blueprint: lem:c03_vdc_first.  Van der Corput, first derivative test on `[a,b]`:
`|∫_a^b e^{iΦ}| ≤ 2 max(|Φ'(a)|⁻¹, |Φ'(b)|⁻¹) ≤ 2/λ` when `Φ'` is monotone and `|Φ'| ≥ λ`. -/
theorem c03_vdc_first (a b lam : ℝ) (hab : a < b) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Icc a b))
    (hmono : MonotoneOn (derivWithin Φ (Icc a b)) (Icc a b) ∨
      AntitoneOn (derivWithin Φ (Icc a b)) (Icc a b))
    (hlow : ∀ ξ ∈ Icc a b, lam ≤ |derivWithin Φ (Icc a b) ξ|) :
    ‖∫ ξ in a..b, Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
      2 * max (|derivWithin Φ (Icc a b) a|⁻¹) (|derivWithin Φ (Icc a b) b|⁻¹) ∧
    2 * max (|derivWithin Φ (Icc a b) a|⁻¹) (|derivWithin Φ (Icc a b) b|⁻¹) ≤ 2 / lam := by
  apply c03sp_v_vdc_first <;> assumption

/-- Blueprint: lem:c03_vdc_second.  Van der Corput, second derivative test:
`|Φ''| ≥ λ` on `[a,b]` implies `|∫_a^b e^{iΦ}| ≤ 6 λ^{-1/2}`. -/
theorem c03_vdc_second (a b lam : ℝ) (hab : a < b) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Icc a b))
    (hlow : ∀ ξ ∈ Icc a b, lam ≤ |iteratedDerivWithin 2 Φ (Icc a b) ξ|) :
    ‖∫ ξ in a..b, Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤ 6 * lam ^ (-(1 / 2 : ℝ)) := by
  apply c03sp_v_vdc_second <;> assumption

/-- Blueprint: lem:c03_vdc_interval_amplitude.  Van der Corput with a `C¹` amplitude on `[a,b]`
(`k = 1`: constant `2`, `λ⁻¹`; `k = 2`: constant `6`, `λ^{-1/2}`), with `|ψ(b)|`, `|ψ(a)|` or a
sup bound `B` for `ψ`, plus `∫_a^b |ψ'|`. -/
theorem c03_vdc_interval_amplitude (a b lam : ℝ) (hab : a < b) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Icc a b)) (ψ : ℝ → ℂ) (hψ : ContDiffOn ℝ 1 ψ (Icc a b)) :
    (((MonotoneOn (derivWithin Φ (Icc a b)) (Icc a b) ∨
        AntitoneOn (derivWithin Φ (Icc a b)) (Icc a b)) ∧
        ∀ ξ ∈ Icc a b, lam ≤ |derivWithin Φ (Icc a b) ξ|) →
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          2 * lam⁻¹ * (‖ψ b‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          2 * lam⁻¹ * (‖ψ a‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ∀ B : ℝ, (∀ ξ ∈ Icc a b, ‖ψ ξ‖ ≤ B) →
        ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          2 * lam⁻¹ * (B + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖)) ∧
    ((∀ ξ ∈ Icc a b, lam ≤ |iteratedDerivWithin 2 Φ (Icc a b) ξ|) →
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          6 * lam ^ (-(1 / 2 : ℝ)) * (‖ψ b‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          6 * lam ^ (-(1 / 2 : ℝ)) * (‖ψ a‖ + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖) ∧
      ∀ B : ℝ, (∀ ξ ∈ Icc a b, ‖ψ ξ‖ ≤ B) →
        ‖∫ ξ in a..b, ψ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
          6 * lam ^ (-(1 / 2 : ℝ)) * (B + ∫ ξ in a..b, ‖derivWithin ψ (Icc a b) ξ‖)) := by
  apply c03sp_v_vdc_interval_amplitude <;> assumption

/-- Van der Corput on a half-line, with explicit derivatives `g = Φ'`, `g' = Φ''`. -/
theorem c03_aux_vdc_half {a lam : ℝ} (hlam : 0 < lam) {Φ g g' : ℝ → ℝ}
    (hΦc : ContinuousOn Φ (Ici a)) (hgc : ContinuousOn g (Ici a))
    (hg'c : ContinuousOn g' (Ici a))
    (hΦd : ∀ x ∈ Ioi a, HasDerivAt Φ (g x) x) (hgd : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hmono : MonotoneOn g (Ici a) ∨ AntitoneOn g (Ici a))
    (hlow : ∀ ξ ∈ Ici a, lam ≤ |g ξ|)
    (hinf : Tendsto (fun ξ => |g ξ|) atTop atTop) :
    ∃ L : ℂ, Tendsto (fun R => ∫ ξ in a..R, Complex.exp (Complex.I * (Φ ξ : ℂ))) atTop (𝓝 L) ∧
      ‖L‖ ≤ 2 * |g a|⁻¹ := by
  set e : ℝ → ℂ := fun ξ => Complex.exp (Complex.I * (Φ ξ : ℂ)) with he_def
  have he : ContinuousOn e (Ici a) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hΦc))
  have hsub : ∀ c d, a ≤ c → c ≤ d → ‖∫ ξ in c..d, e ξ‖ ≤ 2 * max (|g c|⁻¹) (|g d|⁻¹) := by
    intro c d hc hcd
    rcases hcd.lt_or_eq with hcd | rfl
    · have hs : Icc c d ⊆ Ici a := fun x hx => le_trans hc hx.1
      have hs' : ∀ x ∈ Ioo c d, x ∈ Ioi a := fun x hx => lt_of_le_of_lt hc hx.1
      exact c03sp_v_aux_vdc1 hcd hlam (hΦc.mono hs) (hgc.mono hs) (hg'c.mono hs)
        (fun x hx => hΦd x (hs' x hx)) (fun x hx => hgd x (hs' x hx))
        (hmono.elim (fun h => Or.inl (h.mono hs)) (fun h => Or.inr (h.mono hs)))
        (fun x hx => hlow x (hs hx))
    · simp only [intervalIntegral.integral_same, norm_zero]
      have := abs_nonneg (g c); positivity
  have hii : ∀ c d, a ≤ c → a ≤ d → IntervalIntegrable e volume c d := fun c d hc hd =>
    (he.mono (fun x hx => by
      rcases hx with ⟨h1, _⟩; exact le_trans (le_min hc hd) h1)).intervalIntegrable
  have hinv : Tendsto (fun ξ => |g ξ|⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
  have hcauchy : CauchySeq (fun R : ℝ => ∫ ξ in a..R, e ξ) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev : ∀ᶠ ξ in atTop, |g ξ|⁻¹ < ε / 4 := hinv.eventually (gt_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨max N a, fun n hn => ?_⟩
    have hNa : a ≤ max N a := le_max_right _ _
    rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left (hii a n le_rfl (hNa.trans hn))
      (hii a _ le_rfl hNa)]
    refine lt_of_le_of_lt (hsub _ _ hNa hn) ?_
    have h1 := hN _ (le_max_left N a)
    have h2 := hN n ((le_max_left N a).trans hn)
    have : max (|g (max N a)|⁻¹) (|g n|⁻¹) < ε / 4 := max_lt h1 h2
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, hL, ?_⟩
  have hR : Tendsto (fun R => 2 * max (|g a|⁻¹) (|g R|⁻¹)) atTop (𝓝 (2 * |g a|⁻¹)) := by
    have := (tendsto_const_nhds (x := |g a|⁻¹)).max hinv
    rw [max_eq_left (inv_nonneg.2 (abs_nonneg _))] at this
    exact this.const_mul 2
  refine le_of_tendsto_of_tendsto hL.norm hR ?_
  filter_upwards [eventually_ge_atTop a] with R hR
  exact hsub a R le_rfl hR

-- Not in Mathlib; proved in this file.
/-- Blueprint: lem:c03_vdc_halfline.  Van der Corput on `[a,∞)`: if `Φ'` is monotone,
`|Φ'| ≥ λ` and `|Φ'| → ∞`, the improper integral `∫_a^∞ e^{iΦ}` exists and has modulus
`≤ 2|Φ'(a)|⁻¹ ≤ 2/λ`. -/
theorem c03_vdc_halfline (a lam : ℝ) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Ici a))
    (hmono : MonotoneOn (derivWithin Φ (Ici a)) (Ici a) ∨
      AntitoneOn (derivWithin Φ (Ici a)) (Ici a))
    (hlow : ∀ ξ ∈ Ici a, lam ≤ |derivWithin Φ (Ici a) ξ|)
    (hinf : Tendsto (fun ξ => |derivWithin Φ (Ici a) ξ|) atTop atTop) :
    ∃ L : ℂ, Tendsto (fun R => ∫ ξ in a..R, Complex.exp (Complex.I * (Φ ξ : ℂ))) atTop (𝓝 L) ∧
      ‖L‖ ≤ 2 * |derivWithin Φ (Ici a) a|⁻¹ ∧ 2 * |derivWithin Φ (Ici a) a|⁻¹ ≤ 2 / lam := by
  obtain ⟨hΦc, hgc, hg'c, hder⟩ := c03sp_v_aux_C2_setup (uniqueDiffOn_Ici a) hΦ
  obtain ⟨L, hL, hLb⟩ := c03_aux_vdc_half hlam hΦc hgc hg'c
    (fun x hx => (hder x (Ici_mem_nhds hx)).1) (fun x hx => (hder x (Ici_mem_nhds hx)).2)
    hmono hlow hinf
  refine ⟨L, hL, hLb, ?_⟩
  rw [div_eq_mul_inv]
  gcongr
  exact hlow a (mem_Ici.2 le_rfl)

-- Not in Mathlib; proved in this file.
/-- Blueprint: lem:van_der_Corput.  Paper form: `χ ∈ C¹(ℝ;ℂ)` supported in the compact interval
`I = [a,b]`; (1) `Φ'` monotone, `|Φ'| ≥ λ` on `I`: `|∫ χ e^{iΦ}| ≤ 2λ⁻¹(‖χ‖_∞ + ‖χ'‖_{L¹})`;
(2) `|Φ''| ≥ λ` on `I`: `|∫ χ e^{iΦ}| ≤ 6λ^{-1/2}(‖χ‖_∞ + ‖χ'‖_{L¹})`. -/
theorem van_der_Corput (a b lam : ℝ) (hab : a < b) (hlam : 0 < lam) (Φ : ℝ → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ (Icc a b)) (χ : ℝ → ℂ) (hχ : ContDiff ℝ 1 χ)
    (hχs : tsupport χ ⊆ Icc a b) :
    (((MonotoneOn (derivWithin Φ (Icc a b)) (Icc a b) ∨
        AntitoneOn (derivWithin Φ (Icc a b)) (Icc a b)) ∧
        ∀ ξ ∈ Icc a b, lam ≤ |derivWithin Φ (Icc a b) ξ|) →
      ‖∫ ξ, χ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
        2 * lam⁻¹ * ((⨆ ξ, ‖χ ξ‖) + ∫ ξ, ‖deriv χ ξ‖)) ∧
    ((∀ ξ ∈ Icc a b, lam ≤ |iteratedDerivWithin 2 Φ (Icc a b) ξ|) →
      ‖∫ ξ, χ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ))‖ ≤
        6 * lam ^ (-(1 / 2 : ℝ)) * ((⨆ ξ, ‖χ ξ‖) + ∫ ξ, ‖deriv χ ξ‖)) := by
  have hcs : HasCompactSupport χ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hzero : ∀ ξ ∉ Icc a b, χ ξ = 0 := fun ξ h =>
    image_eq_zero_of_notMem_tsupport (fun h' => h (hχs h'))
  have hint : ∫ ξ, χ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ)) =
      ∫ ξ in a..b, χ ξ * Complex.exp (Complex.I * (Φ ξ : ℂ)) := by
    rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro ξ h; simp [hzero ξ h]
  have hbdd : BddAbove (range fun ξ => ‖χ ξ‖) :=
    hχ.continuous.norm.bddAbove_range_of_hasCompactSupport hcs.norm
  have hB : ∀ ξ ∈ Icc a b, ‖χ ξ‖ ≤ ⨆ ξ, ‖χ ξ‖ := fun ξ _ => le_ciSup hbdd ξ
  have hderiv : ∫ ξ in a..b, ‖derivWithin χ (Icc a b) ξ‖ ≤ ∫ ξ, ‖deriv χ ξ‖ := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (fun ξ hξ => by
        rw [derivWithin_of_mem_nhds (Icc_mem_nhds hξ.1 hξ.2)])]
    apply setIntegral_le_integral
    · exact (hχ.continuous_deriv le_rfl).norm.integrable_of_hasCompactSupport hcs.deriv.norm
    · exact Eventually.of_forall (fun _ => norm_nonneg _)
  have hamp := c03_vdc_interval_amplitude a b lam hab hlam Φ hΦ χ hχ.contDiffOn
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hint]
    refine ((hamp.1 h).2.2 _ hB).trans ?_
    gcongr
  · rw [hint]
    refine ((hamp.2 h).2.2 _ hB).trans ?_
    gcongr

/-! ### The model integral `∫_η^∞ e^{i(Φ₀ - yξ)}` -/

/-- Blueprint: lem:c03_stationary_existence.  The tail integral
`E_y(η) = ∫_η^∞ e^{i(Φ₀(ξ) - yξ)} dξ` (improper; `limUnder`, existence is the lemma). -/
def c03_tailE (p y η : ℝ) : ℂ :=
  limUnder atTop (fun R : ℝ => ∫ ξ in η..R, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ)))

/-- The phase `φ_y(ξ) = Φ₀(ξ) - yξ`: continuity and the derivatives `φ_y' = ξ^p - y`,
`φ_y'' = p ξ^{p-1}` on `ξ > 0`. -/
theorem c03_aux_phase (p y : ℝ) (hp : 0 < p) :
    Continuous (fun ξ => Phi0 p ξ - y * ξ) ∧
    (∀ ξ, 0 < ξ → HasDerivAt (fun ξ => Phi0 p ξ - y * ξ) (ξ ^ p - y) ξ) ∧
    (∀ ξ, 0 < ξ → HasDerivAt (fun ξ => ξ ^ p - y) (p * ξ ^ (p - 1)) ξ) := by
  refine ⟨?_, fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · unfold Phi0
    exact ((continuous_id.mul (continuous_abs.rpow_const (fun _ => Or.inr hp.le))).div_const _).sub
      (continuous_const.mul continuous_id)
  · have heq : (fun ξ => Phi0 p ξ) =ᶠ[𝓝 ξ] fun x => x ^ (p + 1) / (p + 1) := by
      filter_upwards [lt_mem_nhds hξ] with x hx
      simp only [Phi0, abs_of_pos hx]
      rw [Real.rpow_add_one hx.ne', mul_comm]
    have h1 : HasDerivAt (fun x : ℝ => x ^ (p + 1) / (p + 1)) (ξ ^ p) ξ := by
      have := (Real.hasDerivAt_rpow_const (p := p + 1) (Or.inl hξ.ne')).div_const (p + 1)
      convert this using 1
      rw [add_sub_cancel_right]; field_simp
    have h2 : HasDerivAt (fun ξ => Phi0 p ξ - y * ξ) (ξ ^ p - y * 1) ξ :=
      HasDerivAt.sub (h1.congr_of_eventuallyEq heq) ((hasDerivAt_id ξ).const_mul y)
    simpa using h2
  · have := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hξ.ne')).sub_const y
    exact this

/-- The tail integrand `e^{i(Φ₀(ξ) - yξ)}` is continuous. -/
theorem c03_aux_tail_cont (p y : ℝ) (hp : 0 < p) :
    Continuous (fun ξ => Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) :=
  Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (c03_aux_phase p y hp).1))

/-- Van der Corput on `[a,∞)`, `a > 0`, for the phase `Φ₀(ξ) - yξ`, given `|ξ^p - y| ≥ λ`. -/
theorem c03_aux_tail_half (p y : ℝ) (hp : 0 < p) {a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam)
    (hlow : ∀ ξ, a ≤ ξ → lam ≤ |ξ ^ p - y|) :
    ∃ L : ℂ, Tendsto (fun R => ∫ ξ in a..R,
        Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) atTop (𝓝 L) ∧
      ‖L‖ ≤ 2 * |a ^ p - y|⁻¹ := by
  obtain ⟨hc, hd1, hd2⟩ := c03_aux_phase p y hp
  have hpos : ∀ x ∈ Ici a, 0 < x := fun x hx => lt_of_lt_of_le ha hx
  exact c03_aux_vdc_half (Φ := fun ξ => Phi0 p ξ - y * ξ) (g := fun ξ => ξ ^ p - y)
    (g' := fun ξ => p * ξ ^ (p - 1)) hlam hc.continuousOn
    (fun x hx => (hd2 x (hpos x hx)).continuousAt.continuousWithinAt)
    (fun x hx => ((Real.continuousAt_rpow_const x (p - 1)
      (Or.inl (hpos x hx).ne')).const_mul p).continuousWithinAt)
    (fun x hx => hd1 x (lt_trans ha hx)) (fun x hx => hd2 x (lt_trans ha hx))
    (Or.inl (fun x hx x' hx' hxx' => by
      simp only
      linarith [Real.rpow_le_rpow (hpos x hx).le hxx' hp.le]))
    (fun ξ hξ => hlow ξ hξ)
    (tendsto_atTop_mono (fun ξ => le_abs_self _) (by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-y) (tendsto_rpow_atTop hp)))

/-- If the truncated tail integrals from `η` converge to `L`, then `E_y(η) = L`. -/
theorem c03_aux_tailE_eq {p y η : ℝ} {L : ℂ}
    (h : Tendsto (fun R : ℝ => ∫ ξ in η..R,
      Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) atTop (𝓝 L)) :
    c03_tailE p y η = L := by
  rw [c03_tailE]; exact h.limUnder_eq

/-- Shifting the base point of the truncated tail integrals. -/
theorem c03_aux_tail_shift (p y : ℝ) (hp : 0 < p) {η c : ℝ} {L : ℂ}
    (h : Tendsto (fun R : ℝ => ∫ ξ in c..R,
      Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) atTop (𝓝 L)) :
    Tendsto (fun R : ℝ => ∫ ξ in η..R,
      Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) atTop
      (𝓝 ((∫ ξ in η..c, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) + L)) := by
  have hcont := c03_aux_tail_cont p y hp
  have := h.const_add (∫ ξ in η..c, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ)))
  refine this.congr (fun R => ?_)
  exact intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)

/-- Existence of the tail integrals (the first part of `c03_stationary_existence`). -/
theorem c03_aux_tail_exists (p y : ℝ) (hp : 0 < p) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun R : ℝ => ∫ ξ in η..R,
      Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) atTop (𝓝 (c03_tailE p y η)) := by
  set ξ₁ := max η ((|y| + 1) ^ (1 / p))
  have hξ₁ : 0 < ξ₁ := lt_of_lt_of_le hη (le_max_left _ _)
  have hpow : ((|y| + 1) ^ (1 / p)) ^ p = |y| + 1 := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp.ne', Real.rpow_one]
  obtain ⟨L, hL, -⟩ := c03_aux_tail_half p y hp hξ₁ one_pos (fun ξ hξ => by
    have h1 : (|y| + 1) ≤ ξ ^ p := by
      rw [← hpow]
      exact Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hξ) hp.le
    have h2 : 1 ≤ ξ ^ p - y := by linarith [le_abs_self y]
    exact h2.trans (le_abs_self _))
  have := c03_aux_tail_shift p y hp (η := η) hL
  rw [c03_aux_tailE_eq this]; exact this

/-- `E_y(η) = ∫_η^c e^{iφ_y} + E_y(c)` for `η, c > 0`. -/
theorem c03_aux_tailE_shift (p y : ℝ) (hp : 0 < p) {η c : ℝ} (_hη : 0 < η) (hc : 0 < c) :
    c03_tailE p y η = (∫ ξ in η..c, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) +
      c03_tailE p y c :=
  c03_aux_tailE_eq (c03_aux_tail_shift p y hp (c03_aux_tail_exists p y hp c hc))

/-- `|y|⁻¹ ≤ 2⟨y⟩⁻¹` for `|y| ≥ 1`, and `1 ≤ 2⟨y⟩⁻¹` for `|y| ≤ 1`; `|y| ≤ ⟨y⟩`, `1 ≤ ⟨y⟩`. -/
theorem c03_aux_jb_facts (y : ℝ) :
    1 ≤ jb y ∧ |y| ≤ jb y ∧ (1 ≤ |y| → |y|⁻¹ ≤ 2 * (jb y)⁻¹) ∧ (|y| ≤ 1 → 1 ≤ 2 * (jb y)⁻¹) := by
  have hj : jb y ^ 2 = 1 + y ^ 2 := by rw [jb, Real.sq_sqrt (by positivity)]
  have hj0 : 0 ≤ jb y := Real.sqrt_nonneg _
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  have h1 : 1 ≤ jb y := by nlinarith
  have h2 : |y| ≤ jb y := by nlinarith [abs_nonneg y]
  refine ⟨h1, h2, fun hy => ?_, fun hy => ?_⟩
  · have hjy : jb y ≤ 2 * |y| := by nlinarith [abs_nonneg y]
    rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_eq_div, div_le_iff₀ (by linarith)]
    linarith
  · have hjy : jb y ≤ 2 := by nlinarith [abs_nonneg y]
    rw [← div_eq_mul_inv, le_div_iff₀ (by linarith)]; linarith

/-- First and second derivative tests for the phase `Φ₀(ξ) - yξ` on `[c,d] ⊆ (0,∞)`. -/
theorem c03_aux_phase_vdc (p y : ℝ) (hp : 0 < p) {c d lam : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hlam : 0 < lam) :
    ((∀ ξ ∈ Icc c d, lam ≤ |ξ ^ p - y|) →
      ‖∫ ξ in c..d, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))‖ ≤ 2 / lam) ∧
    ((∀ ξ ∈ Icc c d, lam ≤ |p * ξ ^ (p - 1)|) →
      ‖∫ ξ in c..d, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))‖ ≤
        6 * lam ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨hcont, hd1, hd2⟩ := c03_aux_phase p y hp
  have hpos : ∀ x ∈ Icc c d, 0 < x := fun x hx => lt_of_lt_of_le hc hx.1
  have hgc : ContinuousOn (fun ξ : ℝ => ξ ^ p - y) (Icc c d) :=
    fun x hx => (hd2 x (hpos x hx)).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn (fun ξ : ℝ => p * ξ ^ (p - 1)) (Icc c d) :=
    fun x hx => ((Real.continuousAt_rpow_const x (p - 1)
      (Or.inl (hpos x hx).ne')).const_mul p).continuousWithinAt
  have hΦd : ∀ x ∈ Ioo c d, HasDerivAt (fun ξ => Phi0 p ξ - y * ξ) (x ^ p - y) x :=
    fun x hx => hd1 x (hpos x (Ioo_subset_Icc_self hx))
  have hgd : ∀ x ∈ Ioo c d, HasDerivAt (fun ξ : ℝ => ξ ^ p - y) (p * x ^ (p - 1)) x :=
    fun x hx => hd2 x (hpos x (Ioo_subset_Icc_self hx))
  refine ⟨fun hlow => ?_, fun hlow => ?_⟩
  · exact c03sp_v_aux_vdc1' (Φ := fun ξ => Phi0 p ξ - y * ξ) hcd hlam hcont.continuousOn hgc hg'c
      hΦd hgd (Or.inl (fun x hx x' hx' hxx' => by
        simp only
        linarith [Real.rpow_le_rpow (hpos x hx).le hxx' hp.le])) hlow
  · exact c03sp_v_aux_vdc2' (Φ := fun ξ => Phi0 p ξ - y * ξ) hcd hlam hcont.continuousOn hgc hg'c
      hΦd hgd hlow

/-- Blueprint: lem:c03_stationary_existence.  `E_y(η)` exists for `η > 0`, and is `C¹` on
`(0,∞)` with `∂_η E_y(η) = -e^{i(Φ₀(η) - yη)}`. -/
theorem c03_stationary_existence (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (y : ℝ) :
    (∀ η, 0 < η → Tendsto (fun R : ℝ => ∫ ξ in η..R,
      Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) atTop (𝓝 (c03_tailE p y η))) ∧
    ContDiffOn ℝ 1 (c03_tailE p y) (Ioi 0) ∧
    ∀ η, 0 < η → HasDerivAt (c03_tailE p y)
      (-Complex.exp (Complex.I * ((Phi0 p η - y * η : ℝ) : ℂ))) η := by
  have hcont := c03_aux_tail_cont p y hp
  refine ⟨fun η hη => c03_aux_tail_exists p y hp η hη, ?_, ?_⟩
  all_goals
    have hderiv : ∀ η, 0 < η → HasDerivAt (c03_tailE p y)
        (-Complex.exp (Complex.I * ((Phi0 p η - y * η : ℝ) : ℂ))) η := by
      intro η hη
      have hev : (fun η' => (∫ ξ in η'..1, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) +
          c03_tailE p y 1) =ᶠ[𝓝 η] c03_tailE p y := by
        filter_upwards [lt_mem_nhds hη] with η' hη'
        exact (c03_aux_tailE_shift p y hp hη' one_pos).symm
      refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
      exact (intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable _ _)
        (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).add_const _
  · have h := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := 0)
      (f := c03_tailE p y) isOpen_Ioi).2 ⟨fun η (hη : η ∈ Ioi (0 : ℝ)) =>
        (hderiv η hη).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
    · simpa using h
    · rw [contDiffOn_zero]
      refine ContinuousOn.congr (f := fun η => -Complex.exp (Complex.I * ((Phi0 p η - y * η : ℝ) : ℂ)))
        hcont.neg.continuousOn (fun η (hη : η ∈ Ioi (0 : ℝ)) => (hderiv η hη).deriv)
  · exact hderiv

/-- Blueprint: lem:c03_stationary_negative.  `|E_y(η)| ≤ 2|y|⁻¹` for `y ≤ -1`, `η > 0`. -/
theorem c03_stationary_negative (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (y η : ℝ) (hy : y ≤ -1)
    (hη : 0 < η) : ‖c03_tailE p y η‖ ≤ 2 * |y|⁻¹ := by
  have hy0 : 0 < |y| := by rw [abs_of_neg (by linarith)]; linarith
  obtain ⟨L, hL, hLb⟩ := c03_aux_tail_half p y hp hη hy0 (fun ξ hξ => by
    have h1 : 0 ≤ ξ ^ p := Real.rpow_nonneg (by linarith) p
    rw [abs_of_neg (by linarith : y < 0), abs_of_pos (by linarith)]; linarith)
  rw [c03_aux_tailE_eq hL]
  refine hLb.trans (mul_le_mul_of_nonneg_left (inv_anti₀ hy0 ?_) (by norm_num))
  have h1 : 0 ≤ η ^ p := Real.rpow_nonneg hη.le p
  rw [abs_of_neg (by linarith : y < 0), abs_of_pos (by linarith)]; linarith

/-- Blueprint: lem:c03_stationary_positive.  `|E_y(η)| ≤ C y^{(1-p)/(2p)}` for `y ≥ 1`, `η > 0`,
`C = C(p)`. -/
theorem c03_stationary_positive (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ y η : ℝ, 1 ≤ y → 0 < η → ‖c03_tailE p y η‖ ≤ C * y ^ ((1 - p) / (2 * p)) := by
  have hδ1 : 0 < 1 - (1 / 2 : ℝ) ^ p := by
    have := Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hp; linarith
  have hδ3 : 0 < (3 / 2 : ℝ) ^ p - 1 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3 / 2) hp; linarith
  set K2 := (p * (3 / 2 : ℝ) ^ (p - 1)) ^ (-(1 / 2 : ℝ)) with hK2
  have hK2pos : 0 < K2 := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨2 / (1 - (1 / 2 : ℝ) ^ p) + 6 * K2 + 2 / ((3 / 2 : ℝ) ^ p - 1), by positivity, ?_⟩
  intro y η hy hη
  have hy0 : 0 < y := by linarith
  set e := (1 - p) / (2 * p) with he
  have he0 : 0 ≤ e := div_nonneg (by linarith) (by linarith)
  have hye : 1 ≤ y ^ e := Real.one_le_rpow hy he0
  set ξ₀ := y ^ (1 / p) with hξ₀
  have hξ₀pos : 0 < ξ₀ := Real.rpow_pos_of_pos hy0 _
  have hξ₀p : ξ₀ ^ p = y := by
    rw [hξ₀, ← Real.rpow_mul hy0.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  set A := ξ₀ * (1 / 2) with hA
  set B := ξ₀ * (3 / 2) with hB
  have hApos : 0 < A := by positivity
  have hAB : A ≤ B := by rw [hA, hB]; nlinarith
  have hAp : A ^ p = y * (1 / 2 : ℝ) ^ p := by
    rw [hA, Real.mul_rpow hξ₀pos.le (by norm_num), hξ₀p]
  have hBp : B ^ p = y * (3 / 2 : ℝ) ^ p := by
    rw [hB, Real.mul_rpow hξ₀pos.le (by norm_num), hξ₀p]
  set η₁ := max η A with hη₁
  set η₂ := max η₁ B with hη₂
  have hη₁pos : 0 < η₁ := lt_of_lt_of_le hη (le_max_left _ _)
  have hη₂pos : 0 < η₂ := lt_of_lt_of_le hη₁pos (le_max_left _ _)
  rw [c03_aux_tailE_shift p y hp hη hη₁pos, c03_aux_tailE_shift p y hp hη₁pos hη₂pos]
  -- piece 1
  have hp1' : ‖∫ ξ in η..η₁, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))‖ ≤
      2 / (1 - (1 / 2 : ℝ) ^ p) := by
    rcases le_total η A with h | h
    · refine (c03_aux_phase_vdc p y hp hη (le_max_left _ _) hδ1).1 (fun ξ hξ => ?_)
      have hξA : ξ ≤ A := by have := hξ.2; rwa [max_eq_right h] at this
      have h1 : ξ ^ p ≤ A ^ p := Real.rpow_le_rpow (by linarith [hξ.1]) hξA hp.le
      have h2 : ξ ^ p - y < 0 := by nlinarith
      rw [abs_of_neg h2]; nlinarith
    · rw [hη₁, max_eq_left h, intervalIntegral.integral_same, norm_zero]; positivity
  -- piece 2
  have hp2' : ‖∫ ξ in η₁..η₂, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))‖ ≤
      6 * K2 * y ^ e := by
    rcases (le_max_left η₁ B).lt_or_eq with h | h
    · have hη₂B : η₂ = B := by
        rcases le_total η₁ B with h' | h'
        · show max η₁ B = B; rw [max_eq_right h']
        · rw [max_eq_left h'] at h; exact absurd h (lt_irrefl _)
      set lam := p * B ^ (p - 1) with hlam
      have hlampos : 0 < lam := by positivity
      have hbound := (c03_aux_phase_vdc p y hp hη₁pos (le_max_left _ _) hlampos).2 (fun ξ hξ => by
        have hξpos : 0 < ξ := lt_of_lt_of_le hη₁pos hξ.1
        have hξB : ξ ≤ B := hη₂B ▸ hξ.2
        rw [abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hξpos hξB (by linarith)) hp.le)
      refine hbound.trans (le_of_eq ?_)
      have hBe : B ^ (p - 1) = (3 / 2 : ℝ) ^ (p - 1) * y ^ (1 / p * (p - 1)) := by
        rw [hB, Real.mul_rpow hξ₀pos.le (by norm_num), hξ₀, ← Real.rpow_mul hy0.le, mul_comm]
      rw [hlam, hBe, ← mul_assoc, Real.mul_rpow (by positivity) (by positivity), hK2,
        ← Real.rpow_mul hy0.le]
      have : 1 / p * (p - 1) * (-(1 / 2 : ℝ)) = e := by rw [he]; field_simp; ring
      rw [this]; ring
    · have h2 : η₂ = η₁ := h.symm
      rw [h2, intervalIntegral.integral_same, norm_zero]; positivity
  -- piece 3
  have hp3' : ‖c03_tailE p y η₂‖ ≤ 2 / ((3 / 2 : ℝ) ^ p - 1) := by
    have hlow : ∀ ξ, η₂ ≤ ξ → (3 / 2 : ℝ) ^ p - 1 ≤ |ξ ^ p - y| := by
      intro ξ hξ
      have h1 : B ^ p ≤ ξ ^ p :=
        Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hξ) hp.le
      have h2 : (3 / 2 : ℝ) ^ p - 1 ≤ ξ ^ p - y := by nlinarith
      exact h2.trans (le_abs_self _)
    obtain ⟨L, hL, hLb⟩ := c03_aux_tail_half p y hp hη₂pos hδ3 hlow
    rw [c03_aux_tailE_eq hL]
    refine hLb.trans ?_
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) hδ3 (hlow η₂ le_rfl)
  calc _ ≤ ‖∫ ξ in η..η₁, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))‖ +
        (‖∫ ξ in η₁..η₂, Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))‖ +
          ‖c03_tailE p y η₂‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 2 / (1 - (1 / 2 : ℝ) ^ p) + (6 * K2 * y ^ e + 2 / ((3 / 2 : ℝ) ^ p - 1)) := by gcongr
    _ ≤ _ := by
        have h1 : 0 ≤ 2 / (1 - (1 / 2 : ℝ) ^ p) := by positivity
        have h3 : 0 ≤ 2 / ((3 / 2 : ℝ) ^ p - 1) := by positivity
        nlinarith

/-- Blueprint: lem:c03_stationary_small.  `|E_y(η)| ≤ 2 + 2/(2^p - 1)` for `|y| ≤ 1`, `η > 0`. -/
theorem c03_stationary_small (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (y η : ℝ) (hy : |y| ≤ 1)
    (hη : 0 < η) : ‖c03_tailE p y η‖ ≤ 2 + 2 / ((2 : ℝ) ^ p - 1) := by
  have h2p : 1 < (2 : ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
  set η' := max η 2 with hη'
  have hη'2 : 2 ≤ η' := le_max_right _ _
  have hlow : ∀ ξ, η' ≤ ξ → (2 : ℝ) ^ p - 1 ≤ |ξ ^ p - y| := by
    intro ξ hξ
    have h1 : (2 : ℝ) ^ p ≤ ξ ^ p := Real.rpow_le_rpow (by norm_num) (hη'2.trans hξ) hp.le
    have h2 : y ≤ 1 := (le_abs_self y).trans hy
    exact le_trans (by linarith) (le_abs_self _)
  obtain ⟨L, hL, hLb⟩ := c03_aux_tail_half p y hp (by linarith) (by linarith) hlow
  rw [c03_aux_tailE_shift p y hp hη (by linarith : (0 : ℝ) < η'), c03_aux_tailE_eq hL]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (fun x _ => ?_)).trans ?_
    · rw [Complex.norm_exp]; simp
    · rw [one_mul, abs_of_nonneg (by linarith [le_max_left η 2])]
      rcases le_total η 2 with h | h
      · rw [hη', max_eq_right h]; linarith
      · rw [hη', max_eq_left h]; linarith
  · refine hLb.trans ?_
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (hlow η' le_rfl)

/-- Blueprint: lem:appendix_stationary.  The tail integrals exist and
`sup_{η>0} |E_y(η)| ≤ C⟨y⟩⁻¹` (`y ≤ 0`), `≤ C⟨y⟩^{(1-p)/(2p)}` (`y ≥ 0`), `C = C(p)`. -/
theorem appendix_stationary (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ y : ℝ,
      (∀ η, 0 < η → Tendsto (fun R : ℝ => ∫ ξ in η..R,
        Complex.exp (Complex.I * ((Phi0 p ξ - y * ξ : ℝ) : ℂ))) atTop (𝓝 (c03_tailE p y η))) ∧
      (y ≤ 0 → ∀ η, 0 < η → ‖c03_tailE p y η‖ ≤ C * (jb y)⁻¹) ∧
      (0 ≤ y → ∀ η, 0 < η → ‖c03_tailE p y η‖ ≤ C * jb y ^ ((1 - p) / (2 * p))) := by
  obtain ⟨C1, hC1, hposC⟩ := c03_stationary_positive p hp hp1
  have h2p : 1 < (2 : ℝ) ^ p := Real.one_lt_rpow (by norm_num) hp
  set S := 2 + 2 / ((2 : ℝ) ^ p - 1) with hS
  have hS0 : 0 < S := by have : 0 < (2 : ℝ) ^ p - 1 := by linarith
                         positivity
  refine ⟨4 + 2 * S + C1, by positivity, fun y => ⟨fun η hη =>
    (c03_stationary_existence p hp hp1 y).1 η hη, fun hy η hη => ?_, fun hy η hη => ?_⟩⟩
  · obtain ⟨-, -, h3, h4⟩ := c03_aux_jb_facts y
    have hjinv : 0 ≤ (jb y)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    rcases le_or_gt y (-1) with h | h
    · have hb := c03_stationary_negative p hp hp1 y η h hη
      have hy1 : 1 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
      have := h3 hy1
      nlinarith
    · have hb := c03_stationary_small p hp hp1 y η (abs_le.2 ⟨h.le, by linarith⟩) hη
      have := h4 (abs_le.2 ⟨h.le, by linarith⟩)
      nlinarith
  · obtain ⟨h1, h2, -, -⟩ := c03_aux_jb_facts y
    have he0 : 0 ≤ (1 - p) / (2 * p) := div_nonneg (by linarith) (by linarith)
    have hje : 1 ≤ jb y ^ ((1 - p) / (2 * p)) := Real.one_le_rpow h1 he0
    rcases le_or_gt 1 y with h | h
    · have hb := hposC y η h hη
      have : y ^ ((1 - p) / (2 * p)) ≤ jb y ^ ((1 - p) / (2 * p)) :=
        Real.rpow_le_rpow hy (by rw [abs_of_nonneg hy] at h2; exact h2) he0
      nlinarith
    · have hb := c03_stationary_small p hp hp1 y η (abs_le.2 ⟨by linarith, h.le⟩) hη
      nlinarith

/-! ### Stationary phase with a homogeneous phase -/



/-- Blueprint: lem:c03_fresnel_expansion.  For `e ∈ C³` supported in `[-L,L]`:
`|∫ e(w) e^{-iνw²/2} dw - (2π/ν)^{1/2} e^{-iπ/4} e(0)| ≤ C L ν^{-3/2} ‖e‖_{C³(ℝ)}`. -/
theorem c03_fresnel_expansion :
    ∃ C, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ L : ℝ, 1 ≤ L → ∀ e : ℝ → ℂ, ContDiff ℝ 3 e →
      (∀ w, L < |w| → e w = 0) →
      ‖(∫ w : ℝ, e w * Complex.exp (-(Complex.I * (ν : ℂ) * (w : ℂ) ^ 2 / 2))) -
          (Real.sqrt (2 * π / ν) : ℂ) * Complex.exp (-(Complex.I * (π / 4 : ℝ))) * e 0‖ ≤
        C * L * ν ^ (-(3 / 2 : ℝ)) * c03_Ck_normR 3 univ e := by
  apply c03sp_c03_fresnel_expansion <;> assumption

/-- Blueprint: lem:c03_morse_h.  The Morse coordinate
`w(s) = (s-1) ((2/p) ∫₀¹ (1-t) p (1+t(s-1))^{p-1} dt)^{1/2}`. -/
def c03_morse_w (p s : ℝ) : ℝ :=
  (s - 1) * Real.sqrt (2 / p * ∫ t in (0 : ℝ)..1, (1 - t) * p * (1 + t * (s - 1)) ^ (p - 1))

/-- `1 + t(s-1) > 0` for `s > 0`, `t ∈ [0,1]`. -/
theorem c03_aux_morse_base {s t : ℝ} (hs : 0 < s) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + t * (s - 1) := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]; linarith
  · nlinarith [ht.1]

/-- The integral `I(s) = ∫₀¹ (1-t) p (1+t(s-1))^{p-1} dt` of the Morse coordinate. -/
def c03_aux_morseI (p s : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (1 - t) * p * (1 + t * (s - 1)) ^ (p - 1)

/-- `I` is smooth and positive on `(0,∞)`, and `I(1) = p/2`. -/
theorem c03_aux_morseI_props (p : ℝ) (hp : 0 < p) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03_aux_morseI p) (Ioi 0) ∧ (∀ s, 0 < s → 0 < c03_aux_morseI p s) ∧
    c03_aux_morseI p 1 = p / 2 := by
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · unfold c03_aux_morseI
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    apply ContDiffOn.parametric_integral (μ := volume) isOpen_Ioi isCompact_Icc
      Ioc_subset_Icc_self ?_ (by simp)
    have hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ => (1 + x.2 * (x.1 - 1)) ^ (p - 1))
        (Ioi 0 ×ˢ Icc 0 1) :=
      ContDiffOn.rpow_const_of_ne (by fun_prop) (fun x hx => (c03_aux_morse_base hx.1 hx.2).ne')
    exact ((contDiffOn_const.sub contDiffOn_snd).mul contDiffOn_const).mul hb
  · unfold c03_aux_morseI
    have hc : ContinuousOn (fun t => (1 - t) * p * (1 + t * (s - 1)) ^ (p - 1)) (Icc 0 1) :=
      ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).mul
        (ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (c03_aux_morse_base hs ht).ne'))
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc.intervalIntegrable_of_Icc zero_le_one) _ zero_lt_one
    intro t ht
    have := c03_aux_morse_base hs (Ioo_subset_Icc_self ht)
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have h2 : 0 < (1 + t * (s - 1)) ^ (p - 1) := Real.rpow_pos_of_pos this _
    positivity
  · unfold c03_aux_morseI
    simp only [sub_self, mul_zero, add_zero, Real.one_rpow, mul_one]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, integral_id]
    simp; ring

/-- `h(s) - h(1) = -(s-1)² I(s)` for `s > 0` (Taylor with integral remainder). -/
theorem c03_aux_morse_taylor (p : ℝ) (hp : 0 < p) {s : ℝ} (hs : 0 < s) :
    c03_h p s - c03_h p 1 = -(s - 1) ^ 2 * c03_aux_morseI p s := by
  have hx : ∀ t ∈ uIcc (0 : ℝ) 1, 0 < 1 + t * (s - 1) := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht; exact c03_aux_morse_base hs ht
  -- `G(t) = (1-t)(s-1)(1 - x^p) + h(x)`, `x = 1 + t(s-1)`
  have hG : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t => (1 - t) * (s - 1) * (1 - (1 + t * (s - 1)) ^ p) + c03_h p (1 + t * (s - 1)))
      (-((s - 1) ^ 2 * ((1 - t) * p * (1 + t * (s - 1)) ^ (p - 1)))) t := by
    intro t ht
    have hxt := hx t ht
    have hlin : HasDerivAt (fun t => 1 + t * (s - 1)) (s - 1) t := by
      simpa using ((hasDerivAt_id t).mul_const (s - 1)).const_add 1
    have hpow := hlin.rpow_const (p := p) (Or.inl hxt.ne')
    have hpow1 := hlin.rpow_const (p := p + 1) (Or.inl hxt.ne')
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) * (s - 1)) (-(s - 1)) t := by
      simpa using ((hasDerivAt_id t).const_sub 1).mul_const (s - 1)
    have hh : HasDerivAt (fun t => c03_h p (1 + t * (s - 1)))
        ((s - 1) - (s - 1) * (p + 1) * (1 + t * (s - 1)) ^ (p + 1 - 1) / (p + 1)) t := by
      unfold c03_h
      exact hlin.sub (hpow1.div_const (p + 1))
    have := (h1.mul (hpow.const_sub 1)).add hh
    refine this.congr_deriv ?_
    rw [add_sub_cancel_right]
    have e : (1 + t * (s - 1)) ^ p = (1 + t * (s - 1)) ^ (p - 1) * (1 + t * (s - 1)) := by
      rw [← Real.rpow_add_one hxt.ne', sub_add_cancel]
    rw [e]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => -((s - 1) ^ 2 * ((1 - t) * p * (1 + t * (s - 1)) ^ (p - 1))))
      (uIcc 0 1) :=
    (continuousOn_const.mul (((continuousOn_const.sub continuousOn_id).mul continuousOn_const).mul
      (ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (hx t ht).ne')))).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hftc
  simp only [sub_self, zero_mul, add_zero, Real.one_rpow, mul_zero, one_mul, sub_zero,
    zero_add] at hftc
  rw [show 1 + (s - 1) = s by ring] at hftc
  unfold c03_aux_morseI
  linarith

/-- Blueprint: lem:c03_morse_h.  `w ∈ C^∞(0,∞)`, `h(s) - h(1) = -(p/2) w(s)²`, `w(1) = 0`,
`w'(1) = 1`, `w' > 0`; `w` is a diffeomorphism of `[½,2]` onto `[w(½),w(2)]` whose inverse has
bounded `C^k` norms. -/
theorem c03_morse_h (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03_morse_w p) (Ioi 0) ∧
    (∀ s, 0 < s → c03_h p s - c03_h p 1 = -(p / 2) * c03_morse_w p s ^ 2) ∧
    c03_morse_w p 1 = 0 ∧ deriv (c03_morse_w p) 1 = 1 ∧
    (∀ s, 0 < s → 0 < deriv (c03_morse_w p) s) ∧
    StrictMonoOn (c03_morse_w p) (Icc (1 / 2) 2) ∧
    c03_morse_w p '' Icc (1 / 2) 2 = Icc (c03_morse_w p (1 / 2)) (c03_morse_w p 2) ∧
    ∃ sinv : ℝ → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) sinv (Icc (c03_morse_w p (1 / 2)) (c03_morse_w p 2)) ∧
      (∀ s ∈ Icc (1 / 2 : ℝ) 2, sinv (c03_morse_w p s) = s) ∧
      (∀ x ∈ Icc (c03_morse_w p (1 / 2)) (c03_morse_w p 2), c03_morse_w p (sinv x) = x) ∧
      ∀ k : ℕ, ∃ C, ∀ x ∈ Icc (c03_morse_w p (1 / 2)) (c03_morse_w p 2),
        |iteratedDerivWithin k sinv (Icc (c03_morse_w p (1 / 2)) (c03_morse_w p 2)) x| ≤ C := by
  obtain ⟨hIs, hIpos, hI1⟩ := c03_aux_morseI_props p hp
  set w := c03_morse_w p with hwdef
  set q : ℝ → ℝ := fun s => Real.sqrt (2 / p * c03_aux_morseI p s) with hqdef
  have hw_eq : w = fun s => (s - 1) * q s := rfl
  have hq : ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi 0) :=
    (contDiffOn_const.mul hIs).sqrt (fun s hs => (mul_pos (by positivity) (hIpos s hs)).ne')
  have hqpos : ∀ s, 0 < s → 0 < q s := fun s hs =>
    Real.sqrt_pos.2 (mul_pos (by positivity) (hIpos s hs))
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) w (Ioi 0) := by
    rw [hw_eq]; exact (contDiffOn_id.sub contDiffOn_const).mul hq
  have hsq : ∀ s, 0 < s → c03_h p s - c03_h p 1 = -(p / 2) * w s ^ 2 := by
    intro s hs
    rw [c03_aux_morse_taylor p hp hs, hw_eq]
    simp only [hqdef]
    rw [mul_pow, Real.sq_sqrt (mul_pos (by positivity) (hIpos s hs)).le]
    field_simp
  have hw1 : w 1 = 0 := by simp [hw_eq]
  have hdiff : ∀ s, 0 < s → HasDerivAt w (deriv w s) s := fun s hs =>
    ((hw.contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hq1 : q 1 = 1 := by
    simp only [hqdef, hI1]
    rw [show 2 / p * (p / 2) = 1 by field_simp, Real.sqrt_one]
  have hd1 : deriv w 1 = 1 := by
    have hqd : HasDerivAt q (deriv q 1) 1 :=
      ((hq.contDiffAt (Ioi_mem_nhds one_pos)).differentiableAt (by simp)).hasDerivAt
    have := ((hasDerivAt_id (1 : ℝ)).sub_const 1).mul hqd
    rw [hw_eq]
    exact this.deriv.trans (by simp [hq1])
  have hdpos : ∀ s, 0 < s → 0 < deriv w s := by
    intro s hs
    have h1 : HasDerivAt (fun s => w s ^ 2) (2 * w s * deriv w s) s := by
      have := (hdiff s hs).fun_pow 2
      exact this.congr_deriv (by push_cast; ring)
    have h2 : HasDerivAt (fun s => -(2 / p) * (c03_h p s - c03_h p 1))
        (-(2 / p) * (1 - s ^ p)) s := by
      unfold c03_h
      have hr := (Real.hasDerivAt_rpow_const (p := p + 1) (Or.inl hs.ne'))
      have := (((hasDerivAt_id s).sub (hr.div_const (p + 1))).sub_const
        (1 - 1 ^ (p + 1) / (p + 1))).const_mul (-(2 / p))
      refine this.congr_deriv ?_
      rw [add_sub_cancel_right]; field_simp
    have heq : (fun s => w s ^ 2) =ᶠ[𝓝 s] (fun s => -(2 / p) * (c03_h p s - c03_h p 1)) := by
      filter_upwards [Ioi_mem_nhds hs] with x hx
      rw [hsq x hx]; field_simp
    have key := h1.unique (h2.congr_of_eventuallyEq heq)
    rcases lt_trichotomy s 1 with hlt | rfl | hgt
    · have hwneg : w s < 0 := by
        rw [hw_eq]; exact mul_neg_of_neg_of_pos (by linarith) (hqpos s hs)
      have hsp : s ^ p < 1 := Real.rpow_lt_one hs.le hlt hp
      have hR : -(2 / p) * (1 - s ^ p) < 0 := by
        have : 0 < 2 / p := by positivity
        nlinarith
      by_contra hc; push Not at hc
      nlinarith
    · rw [hd1]; exact one_pos
    · have hwpos : 0 < w s := by
        rw [hw_eq]; exact mul_pos (by linarith) (hqpos s hs)
      have hsp : 1 < s ^ p := Real.one_lt_rpow hgt hp
      have hR : 0 < -(2 / p) * (1 - s ^ p) := by
        have : 0 < 2 / p := by positivity
        nlinarith
      by_contra hc; push Not at hc
      nlinarith
  have hmono : StrictMonoOn w (Ioi 0) :=
    strictMonoOn_of_deriv_pos (convex_Ioi 0) hw.continuousOn (by rw [interior_Ioi]; exact hdpos)
  have hsub : Icc (1 / 2 : ℝ) 2 ⊆ Ioi 0 := fun x hx => by
    simp only [mem_Ioi]; linarith [hx.1]
  have hmonoI : StrictMonoOn w (Icc (1 / 2) 2) := hmono.mono hsub
  have himg : w '' Icc (1 / 2) 2 = Icc (w (1 / 2)) (w 2) := by
    ext x; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hmonoI.monotoneOn ⟨le_rfl, by norm_num⟩ hs hs.1,
        hmonoI.monotoneOn hs ⟨by norm_num, le_rfl⟩ hs.2⟩
    · intro hx
      exact intermediate_value_Icc (by norm_num) (hw.continuousOn.mono hsub) hx
  refine ⟨hw, hsq, hw1, hd1, hdpos, hmonoI, himg, ?_⟩
  -- the inverse
  set g := Function.invFunOn w (Ioi 0) with hgdef
  have hinj : InjOn w (Ioi 0) := hmono.injOn
  have hg_left : ∀ s ∈ Ioi (0 : ℝ), g (w s) = s := fun s hs => hinj.leftInvOn_invFunOn hs
  have hJ : ∀ x ∈ Icc (w (1 / 2)) (w 2), ∃ a ∈ Icc (1 / 2 : ℝ) 2, w a = x := by
    rw [← himg]; intro x hx; exact hx
  have hgcd : ∀ x ∈ Icc (w (1 / 2)) (w 2), ContDiffAt ℝ (⊤ : ℕ∞) g x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hJ x hx
    have ha0 : 0 < a := hsub ha
    have hca : ContDiffAt ℝ (⊤ : ℕ∞) w a := hw.contDiffAt (Ioi_mem_nhds ha0)
    have hf' := (hdiff a ha0).hasFDerivAt_equiv (hdpos a ha0).ne'
    have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hL := hca.to_localInverse hf' hn
    have hS := hca.hasStrictFDerivAt hf' hn
    refine hL.congr_of_eventuallyEq ?_
    have hLa : hca.localInverse hf' hn (w a) = a := hca.localInverse_apply_image hf' hn
    have hev1 : ∀ᶠ y in 𝓝 (w a), hca.localInverse hf' hn y ∈ Ioi 0 :=
      hL.continuousAt.preimage_mem_nhds (by rw [hLa]; exact Ioi_mem_nhds ha0)
    filter_upwards [hev1, hS.eventually_right_inverse] with y hy1 hy2
    have hy : ∃ b ∈ Ioi (0 : ℝ), w b = y := ⟨_, hy1, hy2⟩
    exact hinj (Function.invFunOn_mem hy) hy1 ((Function.invFunOn_eq hy).trans hy2.symm)
  have hgcon : ContDiffOn ℝ (⊤ : ℕ∞) g (Icc (w (1 / 2)) (w 2)) :=
    fun x hx => (hgcd x hx).contDiffWithinAt
  have hlt : w (1 / 2) < w 2 := hmonoI ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num)
  refine ⟨g, hgcon, fun s hs => hg_left s (hsub hs), fun x hx => ?_, fun k => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hJ x hx
    rw [hg_left a (hsub ha)]
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (w (1 / 2)) (w 2))).exists_bound_of_continuousOn
      (hgcon.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) (uniqueDiffOn_Icc hlt))
    exact ⟨C, fun x hx => by rw [← Real.norm_eq_abs]; exact hC x hx⟩

/-- Blueprint: lem:c03_sp_compact.  `|ρ(μ;c)| ≤ C μ⁻¹ ‖c‖_{C³}` for `c ∈ C³`,
`supp c ⊆ (½,2)`, `C = C(p)`. -/
theorem c03_sp_compact (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C, 0 < C ∧ ∀ μ : ℝ, 0 < μ → ∀ c : ℝ → ℂ, ContDiff ℝ 3 c → tsupport c ⊆ Ioo (1 / 2) 2 →
      ‖c03_sp_rho p μ c‖ ≤ C * μ⁻¹ * c03_Ck_normR 3 univ c := by
  apply c03s_c03_sp_compact <;> assumption



/-- Blueprint: lem:c03_sp_euler.  `q ∈ C^∞(0,∞)`, `q'(1) = ½`; `T` preserves the support
condition, `Tc(1) = 0`, `‖Tc‖_{C^k} ≤ C_k ‖c‖_{C^{k+1}}`, `ρ(·;c) ∈ C^∞(0,∞)` and
`μ ∂_μ ρ(μ;c) = ρ(μ;Tc)`. -/
theorem c03_sp_euler (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_q p) (Ioi 0) ∧ deriv (c03_sp_q p) 1 = 1 / 2 ∧
    (∀ k : ℕ, ∃ C, 0 < C ∧ ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      c03_Ck_normR k univ (c03_sp_T p c) ≤ C * c03_Ck_normR (k + 1) univ c) ∧
    ∀ c : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) c → tsupport c ⊆ Ioo (1 / 2) 2 →
      tsupport (c03_sp_T p c) ⊆ Ioo (1 / 2) 2 ∧ c03_sp_T p c 1 = 0 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun μ => c03_sp_rho p μ c) (Ioi 0) ∧
      ∀ μ : ℝ, 0 < μ → (μ : ℂ) * deriv (fun μ => c03_sp_rho p μ c) μ = c03_sp_rho p μ (c03_sp_T p c) := by
  apply c03s_c03_sp_euler <;> assumption








/-- Blueprint: lem:c03_sp_near.  (1) `b_y` has the same symbol bounds and `y∂_y b_y = 𝔈 b_y`;
(2) `I_near/P - a(λ₀) = λ₀^m ρ(μ;c_y)`, `c_y = χ_sp b_y`; (3) `|∂_y^j[λ₀^m ρ(μ;c_y)]| ≤
C λ₀^{m-p-1} y^{-j}` for `y ≥ 1`, `C` depending on `p, m, j, C_0,…,C_{j+4}` (and the fixed
`χ_sp`). -/
-- The conjunct `ContDiffOn ℝ ⊤ (y ↦ λ₀^m ρ(μ(y); χ b_y)) (Ioi 0)` records the smoothness of the
-- remainder (established in the proof of (3)), which `appendix_homogeneous_stationary_phase`
-- needs (`c03_hsp_r ∈ C^∞(0,∞)`).
theorem c03_sp_near (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) :
    (∀ Ck : ℕ → ℝ, ∀ a ∈ c03_sp_symbol m,
      (∀ k : ℕ, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) → ∀ y, 0 < y →
      (∀ k : ℕ, ∀ s, 0 < s → ‖iteratedDeriv k (c03_sp_b p m a y) s‖ ≤ Ck k * s ^ (m - k)) ∧
      (∀ s, 0 < s → (y : ℂ) * deriv (fun y' => c03_sp_b p m a y' s) y =
        (1 / p : ℂ) * (-(m : ℂ) * c03_sp_b p m a y s + (s : ℂ) * deriv (c03_sp_b p m a y) s))) ∧
    (∀ a ∈ c03_sp_symbol m, ∀ y, 0 < y →
      c03_sp_Inear p χ a y / c03_sp_P p y - a (lambda0 p y) =
        ((lambda0 p y ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) ∧
    (∀ a ∈ c03_sp_symbol m, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ((lambda0 p y ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y) (fun s => (χ s : ℂ) * c03_sp_b p m a y s)) (Ioi 0)) ∧
    ∀ j : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ k ≤ j + 4, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ y, 1 ≤ y → ‖iteratedDeriv j (fun y' => ((lambda0 p y' ^ m : ℝ) : ℂ) *
          c03_sp_rho p (c03_sp_mu p y') (fun s => (χ s : ℂ) * c03_sp_b p m a y' s)) y‖ ≤
        C * lambda0 p y ^ (m - p - 1) * y ^ (-(j : ℝ)) := by
  apply c03s_c03_sp_near <;> assumption

/-- Blueprint: lem:c03_sp_far.  For `m < p` the improper integral `I_far(y)` exists, is `C^∞` on
`(0,∞)` and `|∂_y^j I_far(y)| ≤ C y^{-M}` for `y ≥ 1`, `C` depending on `p, m, j, M`, finitely
many `C_k` (and the fixed `χ_sp`). -/
theorem c03_sp_far (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (hm : m < p) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo (1 / 2) 2)
    (hχ1 : ∀ s ∈ Icc (3 / 4 : ℝ) (3 / 2), χ s = 1) (hχ01 : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) :
    (∀ a ∈ c03_sp_symbol m,
      (∀ y, 0 < y → Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
        a ξ * ((1 - χ (ξ / lambda0 p y) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) atTop (𝓝 (c03_sp_Ifar p χ a y))) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c03_sp_Ifar p χ a) (Ioi 0)) ∧
    ∀ j : ℕ, ∀ M : ℝ, 0 ≤ M → ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ k ≤ k₀, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ y, 1 ≤ y → ‖iteratedDeriv j (c03_sp_Ifar p χ a) y‖ ≤ C * y ^ (-M) := by
  apply c03f_c03_sp_far <;> assumption



/-- Blueprint: lem:appendix_homogeneous_stationary_phase.  For `m ≤ 0` and `a` in the symbol
class, the improper integral exists for `y > 0`,
`I(y) = e^{i(Ψ₀(y)-π/4)} (2π/(pλ₀^{p-1}))^{1/2} [a(λ₀(y)) + r(y)]` with `r ∈ C^∞(0,∞)` and
`|∂_y^j r(y)| ≤ C λ₀(y)^{m-(p+1)} y^{-j}` for `y ≥ 1`, `C` depending on `p, m, j` and finitely
many `C_k`. -/
-- As in Lemma B.3 of the paper, `m ≤ 0`. The proof holds for
-- every `m < p`, the range in which the improper integral `I(y) = lim_R ∫_0^R a e^{iφ_y}` converges
-- (`c03f_appendix_homogeneous_stationary_phase`). The only use (proof of Lemma 5.1,
-- `approx_linear_seed`) has `a = χ₊(ξ)/ξ`, `m = -1`.
theorem appendix_homogeneous_stationary_phase (p m : ℝ) (hp : 0 < p) (hp1 : p < 1) (hm : m ≤ 0) :
    (∀ a ∈ c03_sp_symbol m,
      (∀ y, 0 < y → Tendsto (fun R : ℝ => ∫ ξ in (0 : ℝ)..R,
        a ξ * Complex.exp (Complex.I * (c03_sp_phi p y ξ : ℂ))) atTop (𝓝 (c03_hsp_I p a y))) ∧
      (∀ y, 0 < y → c03_hsp_I p a y = c03_sp_P p y * (a (lambda0 p y) + c03_hsp_r p a y)) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (c03_hsp_r p a) (Ioi 0)) ∧
    ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ a ∈ c03_sp_symbol m,
      (∀ k ≤ k₀, ∀ ξ, 1 ≤ ξ → ‖iteratedDeriv k a ξ‖ ≤ Ck k * ξ ^ (m - k)) →
      ∀ y, 1 ≤ y → ‖iteratedDeriv j (c03_hsp_r p a) y‖ ≤
        C * lambda0 p y ^ (m - (p + 1)) * y ^ (-(j : ℝ)) := by
  exact c03f_appendix_homogeneous_stationary_phase p m hp hp1 (lt_of_le_of_lt hm hp)

/-! ### An oscillatory integral against a tail integral -/

/-- Blueprint: lem:appendix_triangle.  `|∫_I a e^{iΦ} E| ≤ C A (M κ^{-1/2} + κ⁻¹)` with
`C = C(c₁,…,c₄)`, where `E(t) = ∫_t^∞ e^{iΨ}` (improper) and `Φ + Ψ` is affine on `I`. -/
theorem appendix_triangle (c₁ c₂ c₃ c₄ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hc₄ : 0 < c₄) :
    ∃ C, 0 < C ∧ ∀ x₀ L κ A M ω ω₀ : ℝ, 0 < L → 0 < κ → 0 ≤ A → 0 ≤ M →
      ∀ (Φ Ψ : ℝ → ℝ) (a E : ℝ → ℂ),
      ContDiffOn ℝ 3 Φ (Icc (x₀ - L) (x₀ + L)) →
      derivWithin Φ (Icc (x₀ - L) (x₀ + L)) x₀ = 0 →
      (∀ t ∈ Ioo (x₀ - L) (x₀ + L),
        c₁ * κ ≤ |iteratedDerivWithin 2 Φ (Icc (x₀ - L) (x₀ + L)) t| ∧
        |iteratedDerivWithin 2 Φ (Icc (x₀ - L) (x₀ + L)) t| ≤ c₂ * κ ∧
        |iteratedDerivWithin 3 Φ (Icc (x₀ - L) (x₀ + L)) t| ≤ c₃ * κ / L) →
      ContDiff ℝ 2 a → tsupport a ⊆ Ioo (x₀ - L) (x₀ + L) →
      (∀ j ≤ 2, ∀ t ∈ Ioo (x₀ - L) (x₀ + L),
        ‖iteratedDeriv j a t‖ ≤ c₄ * A * L ^ (-(j : ℝ))) →
      ContinuousOn Ψ (Ici (x₀ - L)) →
      (∀ t ∈ Ioo (x₀ - L) (x₀ + L),
        Tendsto (fun R : ℝ => ∫ s in t..R, Complex.exp (Complex.I * (Ψ s : ℂ))) atTop
          (𝓝 (E t)) ∧ ‖E t‖ ≤ M) →
      (∀ t ∈ Ioo (x₀ - L) (x₀ + L), Φ t + Ψ t = ω * t + ω₀) →
      ‖∫ t in Ioo (x₀ - L) (x₀ + L), a t * Complex.exp (Complex.I * (Φ t : ℂ)) * E t‖ ≤
        C * A * (M * κ ^ (-(1 / 2 : ℝ)) + κ⁻¹) := by
  apply c03sp_appendix_triangle <;> assumption

/-! ### Oscillatory multiplier expansion for `|D|^p` -/

/-- Blueprint: lem:c03_ibp_homogeneous.  Integration by parts against `|z|^{-1-p}`:
`|∫ e^{iφ} e^{-ηz²} b |z|^{-1-p} dz| ≤ C B Λ^{p-K}` for `η ≥ 0`, continuous in `η ≥ 0`;
`C` depends on `p, K, c₀` and finitely many `C_s`. -/
theorem c03_ibp_homogeneous (p K c₀ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hK : p < K)
    (hc₀ : 0 < c₀) :
    ∃ s₀ : ℕ, ∀ Cs : ℕ → ℝ, ∃ C, 0 < C ∧ ∀ (Λ B : ℝ) (U : Set ℝ) (b : ℝ → ℂ) (φ : ℝ → ℝ),
      0 < Λ → 0 ≤ B → IsOpen U → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b →
      tsupport b ⊆ U → ContDiffOn ℝ (⊤ : ℕ∞) φ U →
      (∀ z ∈ U, z ≠ 0 → ∀ s ≤ s₀, ‖iteratedDeriv s b z‖ ≤ Cs s * B * |z| ^ (K - s)) →
      (∀ z ∈ U, c₀⁻¹ * Λ ≤ |deriv φ z| ∧ |deriv φ z| ≤ c₀ * Λ) →
      (∀ z ∈ U, z ≠ 0 → ∀ s ≤ s₀,
        |iteratedDeriv s (fun z => 1 / deriv φ z) z| ≤ Cs s * Λ⁻¹ * |z| ^ (-(s : ℝ))) →
      (∀ η : ℝ, 0 ≤ η → ‖∫ z : ℝ, Complex.exp (Complex.I * (φ z : ℂ)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ)‖ ≤
        C * B * Λ ^ (p - K)) ∧
      ContinuousOn (fun η : ℝ => ∫ z : ℝ, Complex.exp (Complex.I * (φ z : ℂ)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) * b z / ((|z| ^ (1 + p) : ℝ) : ℂ)) (Ici 0) := by
  apply c03c_c03_ibp_homogeneous <;> assumption

/-- Blueprint: lem:c03_frac_moments.  For `k ≥ 1`, `-c_p ∫^osc e^{iλz} z^k |z|^{-1-p} dz =
(-i)^k m^{(k)}(λ)` (`m(ξ) = ξ^p`), the Gaussian-regularised integrals converging locally uniformly
in `λ ∈ (0,∞)`; and `c_p ∫^osc (1-e^{iλz})|z|^{-1-p} = c_p ∫ (1-e^{iλz})|z|^{-1-p} = λ^p`. -/
theorem c03_frac_moments (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ lam₁ lam₂ : ℝ, 0 < lam₁ →
      TendstoUniformlyOn
        (fun (η lam : ℝ) => -(c03_cp p : ℂ) * ∫ z : ℝ, Complex.exp (Complex.I * lam * z) *
          (z : ℂ) ^ k * Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ))
        (fun lam => (-Complex.I) ^ k * ((iteratedDeriv k (fun ξ : ℝ => ξ ^ p) lam : ℝ) : ℂ))
        (𝓝[>] 0) (Icc lam₁ lam₂)) ∧
    ∀ lam : ℝ, 0 < lam →
      Tendsto (fun η : ℝ => (c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) *
          Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 ((c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) /
          ((|z| ^ (1 + p) : ℝ) : ℂ))) ∧
      (c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) /
          ((|z| ^ (1 + p) : ℝ) : ℂ) = ((lam ^ p : ℝ) : ℂ) := by
  apply c03m_c03_frac_moments <;> assumption















/-- Blueprint: lem:c03_mult_expansion.  Kernel representation of
`e^{-iΨ}|D|^p(ae^{iΨ}) - λ^p a`, the oscillatory-integral representation of `ℛ_{mult,N}` and
the Taylor remainder formula (eqn:appendix_oscillatory_multiplier_taylor_remainder). -/
theorem c03_mult_expansion (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Y Λ : ℝ) (hY : 1 ≤ Y)
    (hΛ : 1 ≤ Λ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (has : tsupport a ⊆ Ioo (Y / 4) (4 * Y)) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Ioo (Y / 4) (4 * Y)))
    (hlam : ∀ y ∈ Ioo (Y / 4) (4 * Y), 0 < deriv Ψ y) (y : ℝ) (hy : y ∈ Icc Y (2 * Y)) :
    ContDiff ℝ (⊤ : ℕ∞) (c03_mult_F Y a Ψ y) ∧ HasCompactSupport (c03_mult_F Y a Ψ y) ∧
    Integrable (fun z : ℝ => Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
      (c03_mult_F Y a Ψ y z - a y) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    Complex.exp (-(Complex.I * (Ψ y : ℂ))) *
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y -
        ((deriv Ψ y ^ p : ℝ) : ℂ) * a y =
      -(c03_cp p : ℂ) * ∫ z : ℝ, Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) *
        (c03_mult_F Y a Ψ y z - a y) / ((|z| ^ (1 + p) : ℝ) : ℂ) ∧
    ∀ N : ℕ, 1 ≤ N →
      Tendsto (fun η : ℝ => -(c03_cp p : ℂ) * ∫ z : ℝ,
          Complex.exp (Complex.I * ((deriv Ψ y : ℝ) : ℂ) * z) * c03_mult_taylorR Y a Ψ N y z *
            Complex.exp (-((η * z ^ 2 : ℝ) : ℂ)) / ((|z| ^ (1 + p) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 (c03_mult_R p Y a Ψ N y)) ∧
      ∀ z : ℝ, c03_mult_taylorR Y a Ψ N y z =
        ((2 * N - 1 : ℕ) : ℂ) * ∑ rq ∈ c03_mult_index N, c03_mult_coeff rq.1 rq.2 *
          ∫ t in (0 : ℝ)..1, (((1 - t) ^ (2 * N - 2) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (c03_mult_Theta Ψ y (t * z) : ℂ)) *
            c03_mult_bt Y a Ψ N rq.1 rq.2 y t z := by
  apply c03m_c03_mult_expansion <;> assumption

/-- Blueprint: lem:c03_mult_summand.  Symbol bounds for `b_t`, the phase bounds for `φ_t`, and
the bound `|∂_y^j I_η(y,t)| ≤ C B Y^{-j} Λ^{p-K} ≤ C A Y^{-N-j} Λ^{p-N}` (`K = 2N-1+q₁`),
uniformly in `t ∈ (0,1]`, `y ∈ [Y,2Y]`, `η ≥ 0`; constants depend on `p, N, s, j, c₀` and finitely
many `C_k`. -/
theorem c03_mult_summand (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ)
    (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    (∀ s : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∀ z : ℝ, z ≠ 0 → ‖iteratedDeriv s (c03_mult_bt Y a Ψ N r q y t) z‖ ≤
        C * c03_mult_size N q Y Λ A t * |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s)) ∧
      (∀ z : ℝ, y + t * z ∈ Ioo (Y / 4) (4 * Y) →
        deriv (c03_mult_phit Ψ y t) z = (1 - t) * deriv Ψ y + t * deriv Ψ (y + t * z) ∧
        c₀⁻¹ * Λ ≤ deriv (c03_mult_phit Ψ y t) z ∧ deriv (c03_mult_phit Ψ y t) z ≤ c₀ * Λ ∧
        |iteratedDeriv s (fun z => 1 / deriv (c03_mult_phit Ψ y t) z) z| ≤
          C * Λ⁻¹ * (t / Y) ^ s ∧
        (z ≠ 0 → |iteratedDeriv s (fun z => 1 / deriv (c03_mult_phit Ψ y t) z) z| ≤
          C * Λ⁻¹ * |z| ^ (-(s : ℝ))))) ∧
    (∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1,
      ∀ η : ℝ, 0 ≤ η →
        ‖iteratedDeriv j (fun y' => c03_mult_I p Y a Ψ N r q η y' t) y‖ ≤
          C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) ∧
        C * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) ≤
          C * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by
  apply c03m_c03_mult_summand <;> assumption

/-- Blueprint: lem:c03_mult_difference.  For two data `(a_ν, Ψ_ν)` with `δ`-close derivatives:
difference bounds for the amplitudes and phases, the interpolation identity
(eqn:appendix_oscillatory_multiplier_difference_integrals) and
`|∂_y^j(I₁ - I₀)| ≤ C δ B Y^{-j} Λ^{p-K} + C δ B Y^{-j-1} Λ^{p-K-1} ≤ 2 C δ A Y^{-N-j} Λ^{p-N}`. -/
-- The interpolation identity is stated for smooth, compactly supported data and `y, t` in the
-- stated domain; the phase-difference bounds are stated where `y + t z` lies in the phase domain;
-- the final sum carries the constant `2 C`.
theorem c03_mult_difference (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ) (hc₀ : 0 < c₀) (N : ℕ)
    (hN : 1 ≤ N) (r : ℕ) (q : Fin (2 * N - 1) → ℕ)
    (hrq : r + ∑ i, (i.val + 1) * q i = 2 * N - 1) :
    -- the interpolation identity
    (∀ (Y : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ) (η y t : ℝ), 0 < Y →
      ContDiff ℝ (⊤ : ℕ∞) a₀ → tsupport a₀ ⊆ Ioo (Y / 4) (4 * Y) →
      ContDiff ℝ (⊤ : ℕ∞) a₁ → tsupport a₁ ⊆ Ioo (Y / 4) (4 * Y) →
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ₀ (Ioo (Y / 4) (4 * Y)) →
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ₁ (Ioo (Y / 4) (4 * Y)) →
      y ∈ Icc Y (2 * Y) → t ∈ Ioc (0 : ℝ) 1 → 0 < η →
      c03_mult_I p Y a₁ Ψ₁ N r q η y t - c03_mult_I p Y a₀ Ψ₀ N r q η y t =
        (∫ z : ℝ, Complex.exp (Complex.I * (c03_mult_phit Ψ₁ y t z : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
          (c03_mult_bt Y a₁ Ψ₁ N r q y t z - c03_mult_bt Y a₀ Ψ₀ N r q y t z) /
            ((|z| ^ (1 + p) : ℝ) : ℂ)) +
        Complex.I * ∫ σ in (0 : ℝ)..1, ∫ z : ℝ,
          Complex.exp (Complex.I * (((1 - σ) * c03_mult_phit Ψ₀ y t z +
              σ * c03_mult_phit Ψ₁ y t z : ℝ) : ℂ) - ((η * z ^ 2 : ℝ) : ℂ)) *
            ((c03_mult_phit Ψ₁ y t z - c03_mult_phit Ψ₀ y t z : ℝ) : ℂ) *
            c03_mult_bt Y a₀ Ψ₀ N r q y t z / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    -- the bounds
    ∀ j s : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ → δ ≤ 1 →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a₀ Ψ₀ → c03_mult_hyp Y Λ A c₀ Ck k₀ a₁ Ψ₁ →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ k₀,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
      ∀ y ∈ Icc Y (2 * Y), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∀ z : ℝ, z ≠ 0 →
        ‖iteratedDeriv j (fun y' => iteratedDeriv s (fun z' =>
            c03_mult_bt Y a₁ Ψ₁ N r q y' t z' - c03_mult_bt Y a₀ Ψ₀ N r q y' t z') z) y‖ ≤
          C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
            |z| ^ (((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - s) ∧
        (y + t * z ∈ Ioo (Y / 4) (4 * Y) →
        |iteratedDeriv j (fun y' => iteratedDeriv s (fun z' =>
            c03_mult_phit Ψ₁ y' t z' - c03_mult_phit Ψ₀ y' t z') z) y| ≤
          C * δ * Y ^ (-(j : ℝ) - 1) * |z| ^ (1 - (s : ℝ)))) ∧
      ∀ η : ℝ, 0 ≤ η →
        ‖iteratedDeriv j (fun y' => c03_mult_I p Y a₁ Ψ₁ N r q η y' t -
            c03_mult_I p Y a₀ Ψ₀ N r q η y' t) y‖ ≤
          C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
            C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) ∧
        C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ)) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ)) +
            C * δ * c03_mult_size N q Y Λ A t * Y ^ (-(j : ℝ) - 1) *
              Λ ^ (p - ((2 * N - 1 + c03_mult_q1 q : ℕ) : ℝ) - 1) ≤
          2 * C * δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N) := by
  apply c03m_c03_mult_difference <;> assumption


/-- Blueprint: lem:appendix_oscillatory_multiplier.  Oscillatory multiplier expansion
`|D|^p(ae^{iΨ}) = e^{iΨ}[∑_{k=0}^{2N-2} B_k + ℛ_{mult,N}]` with
`|∂_y^j ℛ_{mult,N}| ≤ C A Y^{-N-j} Λ^{p-N}` (`j = 0,1`), the two-term form, and the difference
estimate `|∂_y^j(ℛ_{mult,N,1} - ℛ_{mult,N,0})| ≤ C min(1,δ) A Y^{-N-j} Λ^{p-N}` (all `j`);
`C = C(p, N, j, c₀, (C_k)_{k ≤ k₀(N,j)})`. -/
theorem appendix_oscillatory_multiplier (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (c₀ : ℝ)
    (hc₀ : 0 < c₀) :
    -- the expansion (eqn:appendix_oscillatory_multiplier_expansion) and the remainder bound
    (∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, j ≤ 1 → ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y),
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y =
          Complex.exp (Complex.I * (Ψ y : ℂ)) *
            ((∑ k ∈ Finset.range (2 * N - 1), c03_mult_B p Y a Ψ k y) + c03_mult_R p Y a Ψ N y) ∧
        ‖iteratedDeriv j (c03_mult_R p Y a Ψ N) y‖ ≤
          C * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) ∧
    -- the two-term expansion
    (∀ j : ℕ, j ≤ 1 → ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A : ℝ) (a : ℝ → ℂ) (Ψ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a Ψ → ∀ y ∈ Icc Y (2 * Y),
        fracDC p (fun x => a x * Complex.exp (Complex.I * (Ψ x : ℂ))) y =
          Complex.exp (Complex.I * (Ψ y : ℂ)) *
            (((deriv Ψ y ^ p : ℝ) : ℂ) * a y -
              Complex.I * ((p * deriv Ψ y ^ (p - 1) : ℝ) : ℂ) * deriv a y -
              Complex.I * ((p * (p - 1) / 2 * deriv Ψ y ^ (p - 2) * deriv (deriv Ψ) y : ℝ) : ℂ) *
                a y +
              c03_mult_R2tilde p Y a Ψ y) ∧
        ‖iteratedDeriv j (c03_mult_R2tilde p Y a Ψ) y‖ ≤
          C * A * Y ^ (-(2 : ℝ) - j) * Λ ^ (p - 2)) ∧
    -- the difference estimate
    (∀ N : ℕ, 1 ≤ N → ∀ j : ℕ, ∃ k₀ : ℕ, ∀ Ck : ℕ → ℝ, ∃ C, 0 < C ∧
      ∀ (Y Λ A δ : ℝ) (a₀ a₁ : ℝ → ℂ) (Ψ₀ Ψ₁ : ℝ → ℝ), 1 ≤ Y → 1 ≤ Λ → 0 < A → 0 ≤ δ →
      c03_mult_hyp Y Λ A c₀ Ck k₀ a₀ Ψ₀ → c03_mult_hyp Y Λ A c₀ Ck k₀ a₁ Ψ₁ →
      (∀ x ∈ Ioo (Y / 4) (4 * Y), ∀ k ≤ k₀,
        ‖iteratedDeriv k (fun x => a₁ x - a₀ x) x‖ ≤ Ck k * δ * A * Y ^ (-(k : ℝ)) ∧
        |iteratedDeriv k (fun x => Ψ₁ x - Ψ₀ x) x| ≤ Ck k * δ * Y ^ (-(k : ℝ))) →
      ∀ y ∈ Icc Y (2 * Y),
        ‖iteratedDeriv j (fun y' => c03_mult_R p Y a₁ Ψ₁ N y' - c03_mult_R p Y a₀ Ψ₀ N y') y‖ ≤
          C * min 1 δ * A * Y ^ (-((N : ℝ) + j)) * Λ ^ (p - N)) := by
  apply c03m_appendix_oscillatory_multiplier <;> assumption

end GSQG
