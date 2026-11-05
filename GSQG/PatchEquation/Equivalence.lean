import GSQG.PatchEquation.WeakFormulation
import GSQG.PatchEquation.NormalTrace
import GSQG.PatchEquation.BulkToContour

/-!
# Beyond the paper (2D patch derivation): spatial flux, velocity-law uniqueness, initial trace, weak patch
equation ⇔ front equation (blueprint ch. 13)

Helpers are named `c13t_aux_*`.

Blueprint: lem:c13_spatial_flux, lem:c13_velocity_law_unique, lem:c13_patch_time_trace,
thm:c13_patch_front_equivalence.  Conventions follow `PatchEquation/WeakFormulation` (spacetime tests on `E × I`,
curried densities/velocities, pairings as set integrals over `univ ×ˢ I` with explicit
integrability).  The patch density is `θ_F X t = (c13_patch F t).indicator 1 X`.
Standing assumptions: `1 < α < 2`, `0 < c`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### Pure helpers -/

/-- The volume-preserving coordinate map `ℝ × ℝ ≃ᵐ E`, `(x, y) ↦ c13_pt x y`. -/
def c13t_aux_coord : ℝ × ℝ ≃ᵐ c13_E :=
  (MeasurableEquiv.finTwoArrow).symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem c13t_aux_coord_mp : MeasurePreserving c13t_aux_coord volume volume :=
  (volume_preserving_finTwoArrow ℝ).symm.trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm

@[simp] theorem c13t_aux_coord_apply (p : ℝ × ℝ) : c13t_aux_coord p = c13_pt p.1 p.2 := by
  ext i; fin_cases i <;> rfl

@[simp] theorem c13t_aux_pt0 (x y : ℝ) : (c13_pt x y) 0 = x := rfl
@[simp] theorem c13t_aux_pt1 (x y : ℝ) : (c13_pt x y) 1 = y := rfl


theorem c13t_aux_indicator_diff (a b y : ℝ) :
    |(Iio a).indicator (fun _ => (1:ℝ)) y - (Iio b).indicator (fun _ => (1:ℝ)) y| =
      (Ico (min a b) (max a b)).indicator (fun _ => (1:ℝ)) y := by
  simp only [indicator, mem_Iio, mem_Ico, min_le_iff, lt_max_iff]
  by_cases ha : y < a <;> by_cases hb : y < b <;> simp [ha, hb]

theorem c13t_aux_slice_bound (R a b : ℝ) :
    ∫ y in Icc (-R) R, |(Iio a).indicator (fun _ => (1:ℝ)) y - (Iio b).indicator (fun _ => (1:ℝ)) y|
      ≤ |a - b| := by
  simp_rw [c13t_aux_indicator_diff]
  rw [integral_indicator_const _ measurableSet_Ico, smul_eq_mul, mul_one,
    measureReal_restrict_apply measurableSet_Ico]
  calc volume.real (Ico (min a b) (max a b) ∩ Icc (-R) R)
      ≤ volume.real (Ico (min a b) (max a b)) := measureReal_mono inter_subset_left (by simp)
    _ = |a - b| := by rw [Real.volume_real_Ico, max_sub_min_eq_abs, abs_sub_comm]; exact max_eq_left (abs_nonneg _)


theorem c13t_aux_patch_isOpen {F : ℝ → ℝ → ℝ} {t : ℝ} (h : Continuous (fun x => F x t)) :
    IsOpen (c13_patch F t) := by
  have h0 : Continuous (fun X : c13_E => X 0) := by fun_prop
  have h1 : Continuous (fun X : c13_E => X 1) := by fun_prop
  exact isOpen_lt h1 (h.comp h0)

theorem c13t_aux_coord_preimage_patch (F : ℝ → ℝ → ℝ) (t : ℝ) (p : ℝ × ℝ) :
    (c13_patch F t).indicator (1 : c13_E → ℝ) (c13t_aux_coord p) =
      (Iio (F p.1 t)).indicator (fun _ => (1:ℝ)) p.2 := by
  simp [indicator, c13_patch]

theorem c13t_aux_square_L1 {F : ℝ → ℝ → ℝ} {s t R : ℝ} (hR : 0 ≤ R)
    (hs : Continuous (fun x => F x s)) (ht : Continuous (fun x => F x t)) :
    IntegrableOn (fun X : c13_E => |(c13_patch F t).indicator 1 X -
          (c13_patch F s).indicator (1 : c13_E → ℝ) X|) {X | |X 0| ≤ R ∧ |X 1| ≤ R} ∧
      (∫ X in {X : c13_E | |X 0| ≤ R ∧ |X 1| ≤ R},
          |(c13_patch F t).indicator 1 X - (c13_patch F s).indicator (1 : c13_E → ℝ) X|) ≤
        ∫ x in (-R)..R, |F x t - F x s| := by
  set g : c13_E → ℝ := fun X => |(c13_patch F t).indicator 1 X -
          (c13_patch F s).indicator (1 : c13_E → ℝ) X| with hg
  have hpre : c13t_aux_coord ⁻¹' {X : c13_E | |X 0| ≤ R ∧ |X 1| ≤ R} = Icc (-R) R ×ˢ Icc (-R) R := by
    ext p; simp only [mem_preimage, c13t_aux_coord_apply, c13t_aux_pt0, c13t_aux_pt1, mem_ofPred_eq,
      mem_prod, mem_Icc, abs_le]
  have hmeas : Measurable g := by
    refine (Measurable.sub ?_ ?_).abs
    · exact (measurable_const.indicator (c13t_aux_patch_isOpen ht).measurableSet)
    · exact (measurable_const.indicator (c13t_aux_patch_isOpen hs).measurableSet)
  have hbd : ∀ X, ‖g X‖ ≤ 1 := by
    intro X; simp only [hg, Real.norm_eq_abs, abs_abs]
    simp only [indicator]; split_ifs <;> norm_num
  have hgp : ∀ p, g (c13t_aux_coord p) =
      |(Iio (F p.1 t)).indicator (fun _ => (1:ℝ)) p.2 - (Iio (F p.1 s)).indicator (fun _ => (1:ℝ)) p.2| := by
    intro p; simp only [hg, c13t_aux_coord_preimage_patch]
  have hSm : MeasurableSet {X : c13_E | |X 0| ≤ R ∧ |X 1| ≤ R} := by
    have h0 : Continuous (fun X : c13_E => X 0) := by fun_prop
    have h1 : Continuous (fun X : c13_E => X 1) := by fun_prop
    exact (isClosed_le (continuous_abs.comp h0) continuous_const).measurableSet.inter
      (isClosed_le (continuous_abs.comp h1) continuous_const).measurableSet
  have hfin : volume {X : c13_E | |X 0| ≤ R ∧ |X 1| ≤ R} < ⊤ := by
    rw [← c13t_aux_coord_mp.measure_preimage hSm.nullMeasurableSet, hpre, Measure.volume_eq_prod,
      Measure.prod_prod]
    simp [ENNReal.mul_lt_top]
  have hint : IntegrableOn g {X | |X 0| ≤ R ∧ |X 1| ≤ R} :=
    Measure.integrableOn_of_bounded hfin.ne hmeas.aestronglyMeasurable (Eventually.of_forall hbd)
  refine ⟨hint, ?_⟩
  rw [← c13t_aux_coord_mp.setIntegral_preimage_emb c13t_aux_coord.measurableEmbedding, hpre]
  simp_rw [c13t_aux_coord_preimage_patch]
  have hint2 : IntegrableOn (fun p : ℝ × ℝ => |(Iio (F p.1 t)).indicator (fun _ => (1:ℝ)) p.2 -
      (Iio (F p.1 s)).indicator (fun _ => (1:ℝ)) p.2|) (Icc (-R) R ×ˢ Icc (-R) R) := by
    have := (c13t_aux_coord_mp.integrableOn_comp_preimage
      c13t_aux_coord.measurableEmbedding).2 hint
    rw [hpre] at this
    refine this.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Function.comp_apply, hgp]
  rw [Measure.volume_eq_prod] at hint2 ⊢
  have hint3 : Integrable (fun p : ℝ × ℝ => |(Iio (F p.1 t)).indicator (fun _ => (1:ℝ)) p.2 -
      (Iio (F p.1 s)).indicator (fun _ => (1:ℝ)) p.2|)
      ((volume.restrict (Icc (-R) R)).prod (volume.restrict (Icc (-R) R))) := by
    rw [Measure.prod_restrict]; exact hint2
  rw [setIntegral_prod _ hint2]
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Icc (fun x _ => c13t_aux_slice_bound R (F x t) (F x s))
  · exact hint3.integral_prod_left
  · exact ((ht.sub hs).abs).integrableOn_Icc


theorem c13t_aux_F_contOn {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    ContinuousOn (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I) :=
  hF.2.2.1.continuousOn

theorem c13t_aux_F_cont_slice {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t : ℝ}
    (ht : t ∈ I) : Continuous (fun x => F x t) :=
  (c13t_aux_F_contOn hF).comp_continuous (continuous_id.prodMk continuous_const)
    (fun _x => ⟨mem_univ _, ht⟩)

theorem c13t_aux_L1loc_cont {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F)
    (K : Set c13_E) (hK : IsCompact K) (t : ℝ) (ht : t ∈ I) :
    Tendsto (fun s => ∫ X in K,
        |(c13_patch F s).indicator 1 X - (c13_patch F t).indicator (1 : c13_E → ℝ) X|)
      (𝓝[I] t) (𝓝 0) := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKsq : K ⊆ {X : c13_E | |X 0| ≤ R ∧ |X 1| ≤ R} := by
    intro X hX
    have hX' : ‖X‖ ≤ R := le_trans (by simpa using hR₀ hX) (le_max_left _ _)
    have h0 : |X 0| ≤ ‖X‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 0
    have h1 : |X 1| ≤ ‖X‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 1
    exact ⟨h0.trans hX', h1.trans hX'⟩
  set g : ℝ → ℝ := fun s => ∫ x in (-R)..R, |F x s - F x t|
  have hg : ContinuousOn g I := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun p : I × ℝ => |F p.2 (p.1 : ℝ) - F p.2 t|) := by
      refine (Continuous.sub ?_ ?_).abs
      · exact (c13t_aux_F_contOn hF).comp_continuous
          (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
          (fun p : I × ℝ => ⟨mem_univ _, p.1.2⟩)
      · exact (c13t_aux_F_cont_slice hF ht).comp continuous_snd
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun (s : I) (x : ℝ) => |F x (s : ℝ) - F x t|) hc (-R) R
  have hg0 : Tendsto g (𝓝[I] t) (𝓝 0) := by
    have := hg t ht
    simpa [g] using this.tendsto
  refine squeeze_zero' ?_ ?_ hg0
  · exact Eventually.of_forall (fun s => integral_nonneg (fun X => abs_nonneg _))
  · filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨hint, hle⟩ := c13t_aux_square_L1 (F := F) (s := t) (t := s) hR.le
      (c13t_aux_F_cont_slice hF ht) (c13t_aux_F_cont_slice hF hs)
    refine le_trans ?_ (hle.trans (le_of_eq ?_))
    · exact setIntegral_mono_set hint (Eventually.of_forall (fun X => abs_nonneg _))
        (Eventually.of_forall hKsq)
    · rfl


theorem c13t_aux_slice_contDiff {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t : ℝ}
    (ht : t ∈ I) : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x t) := by
  have h := hF.2.2.1.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun x => ⟨mem_univ x, ht⟩)
  exact h

theorem c13t_aux_slope {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t : ℝ}
    (ht : t ∈ I) : ∃ M, 0 ≤ M ∧ ∀ x, |deriv (fun x => F x t) x| ≤ M := by
  obtain ⟨M, hM, h⟩ := hF.2.2.2 {t} (by simpa using ht) isCompact_singleton
  exact ⟨M, hM, fun x => h x t rfl⟩

theorem c13t_aux_U_eq_indicator (α c : ℝ) (F : ℝ → ℝ → ℝ) (t : ℝ) :
    (fun X => c13_graph_velocity α c F X t) =
      {X : c13_E | X 1 ≠ F (X 0) t}.indicator (fun X => c13_graph_velocity α c F X t) := by
  funext X
  by_cases h : X 1 = F (X 0) t
  · simp [indicator, h, c13_graph_velocity]
  · simp [indicator, h]

theorem c13t_aux_offgraph_isOpen {F : ℝ → ℝ → ℝ} {t : ℝ} (h : Continuous (fun x => F x t)) :
    IsOpen {X : c13_E | X 1 ≠ F (X 0) t} := by
  have h0 : Continuous (fun X : c13_E => X 0) := by fun_prop
  have h1 : Continuous (fun X : c13_E => X 1) := by fun_prop
  exact isOpen_ne_fun h1 (h.comp h0)

theorem c13t_aux_U_aesm {α c : ℝ} (hα1 : 1 < α) {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hF : c13_graph_class I F) {t : ℝ} (ht : t ∈ I) :
    AEStronglyMeasurable (fun X => c13_graph_velocity α c F X t) volume := by
  have hS := c13t_aux_offgraph_isOpen (c13t_aux_slice_contDiff hF ht).continuous
  rw [c13t_aux_U_eq_indicator]
  exact (aestronglyMeasurable_indicator_iff hS.measurableSet).2
    (((c13_velocity_divergence hα1 c I F hF).1 t ht).continuousOn.aestronglyMeasurable
      hS.measurableSet)

theorem c13t_aux_U_norm_le (α c : ℝ) (F : ℝ → ℝ → ℝ) (X : c13_E) (t : ℝ) :
    ‖c13_graph_velocity α c F X t‖ ≤
      |c| * ∫ s : ℝ, ‖c13_pt 1 (deriv (fun x => F x t) s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α) := by
  have hnn : 0 ≤ ∫ s : ℝ, ‖c13_pt 1 (deriv (fun x => F x t) s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α) :=
    integral_nonneg (fun s => mul_nonneg (norm_nonneg _) (rpow_nonneg (norm_nonneg _) _))
  unfold c13_graph_velocity
  split_ifs
  · simpa using mul_nonneg (abs_nonneg c) hnn
  · rw [norm_smul, norm_neg, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
      (abs_nonneg c)
    congr 1; funext s
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (norm_nonneg _) _), mul_comm]

theorem c13t_aux_U_weighted {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {J₀ : Set ℝ} (hJ₀ : J₀ ⊆ I) (hJc : IsCompact J₀)
    {K : Set c13_E} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ J₀, ∀ Φ : c13_E → ℝ, AEStronglyMeasurable Φ volume →
      (∀ X, X ∉ K → Φ X = 0) → ∀ B : ℝ, (∀ X, |Φ X| ≤ B) →
      Integrable (fun X => ‖c13_graph_velocity α c F X t‖ * |Φ X|) ∧
      (∫ X, ‖c13_graph_velocity α c F X t‖ * |Φ X|) ≤ C * B := by
  obtain ⟨C₀, hC₀, h⟩ := (c13_velocity_local_integrable hα1 hα2 c I F hF).2.2.2 J₀ hJ₀ hJc K hK
  refine ⟨|c| * C₀, mul_nonneg (abs_nonneg c) hC₀, fun t ht Φ hΦm hΦK B hB => ?_⟩
  obtain ⟨hGi, hGle⟩ := h t ht Φ hΦm hΦK B hB
  set G : ℝ × c13_E → ℝ := fun q => ‖c13_pt 1 (deriv (fun x => F x t) q.1)‖ *
      ‖q.2 - c13_pt q.1 (F q.1 t)‖ ^ (-α) * |Φ q.2| with hG
  rw [Measure.volume_eq_prod] at hGi hGle
  have hh : Integrable (fun X => ∫ s, G (s, X)) volume := hGi.integral_prod_right
  have hpt : ∀ X, ‖c13_graph_velocity α c F X t‖ * |Φ X| ≤ |c| * ∫ s, G (s, X) := by
    intro X
    calc ‖c13_graph_velocity α c F X t‖ * |Φ X|
        ≤ (|c| * ∫ s : ℝ, ‖c13_pt 1 (deriv (fun x => F x t) s)‖ * ‖X - c13_pt s (F s t)‖ ^ (-α))
            * |Φ X| := mul_le_mul_of_nonneg_right (c13t_aux_U_norm_le α c F X t) (abs_nonneg _)
      _ = |c| * ∫ s, G (s, X) := by rw [mul_assoc, ← integral_mul_const]
  have hmeas : AEStronglyMeasurable (fun X => ‖c13_graph_velocity α c F X t‖ * |Φ X|) volume :=
    (c13t_aux_U_aesm hα1 hF (hJ₀ ht)).norm.mul hΦm.norm
  have hint : Integrable (fun X => ‖c13_graph_velocity α c F X t‖ * |Φ X|) volume :=
    (hh.const_mul |c|).mono' hmeas (Eventually.of_forall (fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _))]
      exact hpt X))
  refine ⟨hint, ?_⟩
  calc (∫ X, ‖c13_graph_velocity α c F X t‖ * |Φ X|) ≤ ∫ X, |c| * ∫ s, G (s, X) :=
        integral_mono hint (hh.const_mul _) hpt
    _ = |c| * ∫ q, G q ∂(volume.prod volume) := by
        rw [integral_const_mul, integral_prod_symm _ hGi]
    _ ≤ |c| * (C₀ * B) := mul_le_mul_of_nonneg_left hGle (abs_nonneg c)
    _ = |c| * C₀ * B := by ring


theorem c13t_aux_basis0 : c13_pt 1 0 = EuclideanSpace.single 0 1 := by
  ext i; fin_cases i <;> simp [c13_pt]

theorem c13t_aux_basis1 : c13_pt 0 1 = EuclideanSpace.single 1 1 := by
  ext i; fin_cases i <;> simp [c13_pt]

theorem c13t_aux_decomp (v : c13_E) : v = v 0 • c13_pt 1 0 + v 1 • c13_pt 0 1 := by
  ext i; fin_cases i <;> simp [c13_pt]

/-- The vertical-gap cutoff: `0` for gap `≤ d/2`, `1` for gap `≥ d`. -/
def c13t_aux_cut (f : ℝ → ℝ) (d : ℝ) (X : c13_E) : ℝ :=
  Real.smoothTransition (2 * (f (X 0) - X 1) / d - 1)

theorem c13t_aux_cut_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (c13t_aux_cut f d) := by
  unfold c13t_aux_cut
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun X : c13_E => X 0) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun X : c13_E => X 1) := by fun_prop
  exact Real.smoothTransition.contDiff.comp
    ((((contDiff_const.mul ((hf.comp h0).sub h1)).div_const d).sub contDiff_const))

theorem c13t_aux_cut_zero {f : ℝ → ℝ} {d : ℝ} (hd : 0 < d) {X : c13_E}
    (hX : f (X 0) - X 1 ≤ d / 2) : c13t_aux_cut f d X = 0 := by
  unfold c13t_aux_cut
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, div_le_one hd]; linarith

theorem c13t_aux_cut_one {f : ℝ → ℝ} {d : ℝ} (hd : 0 < d) {X : c13_E}
    (hX : d ≤ f (X 0) - X 1) : c13t_aux_cut f d X = 1 := by
  unfold c13t_aux_cut
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le, one_add_one_eq_two, le_div_iff₀ hd]; linarith


theorem c13t_aux_shifted_flux {α c : ℝ} (hα1 : 1 < α) {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hF : c13_graph_class I F) {t : ℝ} (ht : t ∈ I) (ζ : c13_E → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun X => fderiv ℝ ζ X (c13_graph_velocity α c F X t))
        {X : c13_E | X 1 < F (X 0) t - d} ∧
    Integrable (fun x => ζ (c13_pt x (F x t - d)) *
        ((c13_graph_velocity α c F (c13_pt x (F x t + -d)) t) 1 -
          deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + -d)) t) 0)) ∧
    (∫ X in {X : c13_E | X 1 < F (X 0) t - d}, fderiv ℝ ζ X (c13_graph_velocity α c F X t)) =
      ∫ x, ζ (c13_pt x (F x t - d)) *
        ((c13_graph_velocity α c F (c13_pt x (F x t + -d)) t) 1 -
          deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + -d)) t) 0) := by
  set f : ℝ → ℝ := fun x => F x t with hfdef
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := c13t_aux_slice_contDiff hF ht
  set U : c13_E → c13_E := fun X => c13_graph_velocity α c F X t with hUdef
  obtain ⟨hU1, hUdiv, -, -⟩ := c13_velocity_divergence hα1 c I F hF
  have hUC : ContDiffOn ℝ 1 U {X : c13_E | X 1 ≠ f (X 0)} := hU1 t ht
  have hS : IsOpen {X : c13_E | X 1 ≠ f (X 0)} := c13t_aux_offgraph_isOpen hf.continuous
  have h0 : Continuous (fun X : c13_E => X 0) := by fun_prop
  have h1 : Continuous (fun X : c13_E => X 1) := by fun_prop
  have hgap : Continuous (fun X : c13_E => f (X 0) - X 1) := (hf.continuous.comp h0).sub h1
  set Q : c13_E → c13_E := fun X => (c13t_aux_cut f d X * ζ X) • U X with hQdef
  have hcut := c13t_aux_cut_contDiff hf d
  have hQ : ContDiff ℝ 1 Q := by
    rw [contDiff_iff_contDiffAt]
    intro X
    by_cases hX : d / 4 < f (X 0) - X 1
    · have hXS : X ∈ {X : c13_E | X 1 ≠ f (X 0)} := by
        simp only [mem_ofPred_eq]; intro h; rw [h] at hX; linarith
      have hUat : ContDiffAt ℝ 1 U X := hUC.contDiffAt (hS.mem_nhds hXS)
      exact ((hcut.contDiffAt.mul hζ.contDiffAt).of_le (by simp)).smul hUat
    · have hev : Q =ᶠ[𝓝 X] fun _ => 0 := by
        have hB : IsOpen {Y : c13_E | f (Y 0) - Y 1 < d / 2} := isOpen_lt hgap continuous_const
        filter_upwards [hB.mem_nhds (show f (X 0) - X 1 < d / 2 by linarith [not_lt.1 hX])]
          with Y hY
        simp only [hQdef, c13t_aux_cut_zero hd (le_of_lt hY), zero_mul, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hQc : HasCompactSupport Q := by
    refine hζc.mono ?_
    intro X hX; contrapose hX
    have h' : ζ X = 0 := Function.notMem_support.1 hX
    simp [hQdef, h']
  have hFd : ContDiff ℝ 1 (fun x => f x - d) := (hf.of_le (by simp)).sub contDiff_const
  obtain ⟨hi1, hi2, heq⟩ := c13_compact_graph_flux hFd hQ hQc
  -- divergence on the shifted subgraph
  have hdiv : ∀ X ∈ {X : c13_E | X 1 < f (X 0) - d}, c13g_aux_div Q X = fderiv ℝ ζ X (U X) := by
    intro X hX
    simp only [mem_ofPred_eq] at hX
    have hXS : X ∈ {X : c13_E | X 1 ≠ f (X 0)} := by
      simp only [mem_ofPred_eq]; intro h; linarith
    have hev : Q =ᶠ[𝓝 X] fun Y => ζ Y • U Y := by
      have hB : IsOpen {Y : c13_E | d < f (Y 0) - Y 1} := isOpen_lt continuous_const hgap
      filter_upwards [hB.mem_nhds (show d < f (X 0) - X 1 by linarith)] with Y hY
      simp only [hQdef, c13t_aux_cut_one hd (le_of_lt hY), one_mul]
    have hUd : DifferentiableAt ℝ U X :=
      (hUC.contDiffAt (hS.mem_nhds hXS)).differentiableAt one_ne_zero
    have hζd : DifferentiableAt ℝ ζ X := hζ.differentiable (by simp) X
    have hdU := hUdiv t ht X hXS
    unfold c13g_aux_div
    rw [hev.fderiv_eq, fderiv_fun_smul hζd hUd]
    rw [← c13t_aux_basis0, ← c13t_aux_basis1] at hdU
    conv_rhs => rw [c13t_aux_decomp (U X)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      map_add, map_smul]
    have : ζ X * (fderiv ℝ U X (c13_pt 1 0)) 0 + ζ X * (fderiv ℝ U X (c13_pt 0 1)) 1 = 0 := by
      rw [← mul_add]; simp [hUdef, hdU]
    linear_combination this
  have hmeasS : MeasurableSet {X : c13_E | X 1 < f (X 0) - d} :=
    (isOpen_lt h1 ((hf.continuous.comp h0).sub continuous_const)).measurableSet
  have hbdry : (fun x => Q (c13_pt x (f x - d)) 1 - deriv (fun x => f x - d) x *
      Q (c13_pt x (f x - d)) 0) = fun x => ζ (c13_pt x (F x t - d)) *
        ((c13_graph_velocity α c F (c13_pt x (F x t + -d)) t) 1 -
          deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + -d)) t) 0) := by
    funext x
    have hval : Q (c13_pt x (f x - d)) = ζ (c13_pt x (f x - d)) • U (c13_pt x (f x - d)) := by
      simp only [hQdef]
      rw [c13t_aux_cut_one hd (by simp [c13_pt]), one_mul]
    rw [hval, deriv_sub_const, ← sub_eq_add_neg]
    simp only [PiLp.smul_apply, smul_eq_mul, hUdef, hfdef]
    ring
  simp only at hi2 heq
  refine ⟨hi1.congr_fun hdiv hmeasS, ?_, ?_⟩
  · rw [← hbdry]; exact hi2
  · rw [← setIntegral_congr_fun hmeasS hdiv, heq, ← hbdry]


theorem c13t_aux_abs_le_norm_pt (x y : ℝ) : |x| ≤ ‖c13_pt x y‖ := by
  simpa [Real.norm_eq_abs, c13_pt] using PiLp.norm_apply_le (c13_pt x y) 0

theorem c13t_aux_abs1_le_norm (X : c13_E) : |X 1| ≤ ‖X‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 1

theorem c13t_aux_abs0_le_norm (X : c13_E) : |X 0| ≤ ‖X‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 0

theorem c13t_aux_clm_apply_aesm {μ : Measure c13_E} {L : c13_E → (c13_E →L[ℝ] ℝ)}
    {v : c13_E → c13_E} (hL : Continuous L) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun X => L X (v X)) μ :=
  Continuous.comp_aestronglyMeasurable₂ (g := fun (A : c13_E →L[ℝ] ℝ) (w : c13_E) => A w)
    (by fun_prop) hL.aestronglyMeasurable hv

theorem c13t_aux_cont_slice {I : Set ℝ} {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (univ ×ˢ I)) {t : ℝ} (ht : t ∈ I) :
    Continuous (fun x => G x t) :=
  hG.comp_continuous (continuous_id.prodMk continuous_const) (fun _x => ⟨mem_univ _, ht⟩)

theorem c13t_aux_pt_continuous : Continuous (fun p : ℝ × ℝ => c13_pt p.1 p.2) := by
  have : (fun p : ℝ × ℝ => c13_pt p.1 p.2) =
      fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2] := by
    funext p; rfl
  rw [this]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp (by fun_prop)

theorem c13t_aux_flux_fixed {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t : ℝ} (ht : t ∈ I)
    (ζ : c13_E → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) :
    Integrable (fun X => fderiv ℝ ζ X (c13_graph_velocity α c F X t)) ∧
      Integrable (fun x => c13_normal_speed α c F x t * ζ (c13_pt x (F x t))) ∧
      (∫ X in c13_patch F t, fderiv ℝ ζ X (c13_graph_velocity α c F X t)) =
        ∫ x, c13_normal_speed α c F x t * ζ (c13_pt x (F x t)) := by
  set f : ℝ → ℝ := fun x => F x t with hfdef
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := c13t_aux_slice_contDiff hF ht
  set U : c13_E → c13_E := fun X => c13_graph_velocity α c F X t with hUdef
  set g : c13_E → ℝ := fun X => fderiv ℝ ζ X (U X) with hgdef
  have htI : ({t} : Set ℝ) ⊆ I := by simpa using ht
  -- integrability of the volume integrand
  obtain ⟨Cw, -, hw⟩ := c13t_aux_U_weighted (c := c) hα1 hα2 hF htI isCompact_singleton
    hζc.isCompact
  have hDζc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv (by simp)
  obtain ⟨BD, hBD⟩ := hDζc.bounded_above_of_compact_support (hζc.fderiv (𝕜 := ℝ))
  obtain ⟨hwi, -⟩ := hw t rfl (fun X => ‖fderiv ℝ ζ X‖) hDζc.norm.aestronglyMeasurable
    (fun X hX => by simp [fderiv_of_notMem_tsupport ℝ hX]) BD (fun X => by simpa using hBD X)
  have hgm : AEStronglyMeasurable g volume :=
    c13t_aux_clm_apply_aesm hDζc (c13t_aux_U_aesm hα1 hF ht)
  have hgi : Integrable g := hwi.mono' hgm (Eventually.of_forall (fun X => by
    simp only [hgdef, Real.norm_eq_abs, abs_norm]
    rw [mul_comm]; exact (fderiv ℝ ζ X).le_opNorm (U X)))
  -- the normal speed
  obtain ⟨-, hWc, -⟩ := c13_normal_speed_integrable hα1 hα2 hc hF
  have hWt : Continuous (fun x => c13_normal_speed α c F x t) := c13t_aux_cont_slice hWc ht
  obtain ⟨R₀, hR₀⟩ := hζc.isCompact.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hζout : ∀ x y, R < |x| → ζ (c13_pt x y) = 0 := by
    intro x y hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR₀ hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    have := c13t_aux_abs_le_norm_pt x y
    have : R₀ ≤ R := le_max_left _ _
    linarith
  have hζpt : Continuous (fun p : ℝ × ℝ => ζ (c13_pt p.1 p.2)) := by
    exact hζ.continuous.comp c13t_aux_pt_continuous
  have hgraph : Continuous (fun x => c13_pt x (f x)) :=
    c13t_aux_pt_continuous.comp (continuous_id.prodMk hf.continuous)
  have hWζi : Integrable (fun x => c13_normal_speed α c F x t * ζ (c13_pt x (F x t))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hWt.mul (hζ.continuous.comp hgraph)
    · refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) (fun x hx => ?_)
      have : R < |x| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact hx
      simp [hζout x _ this]
  refine ⟨hgi, hWζi, ?_⟩
  set d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hddef
  have hdpos : ∀ n, 0 < d n := fun n => by simp only [hddef]; positivity
  have hdle : ∀ n, d n ≤ 1 := fun n => by
    simp only [hddef]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdanti : Antitone d := fun m n hmn => by
    simp only [hddef]
    apply one_div_le_one_div_of_le (by positivity)
    have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    linarith
  -- volume side
  set S : ℕ → Set c13_E := fun n => {X | X 1 < F (X 0) t - d n} with hSdef
  have h0 : Continuous (fun X : c13_E => X 0) := by fun_prop
  have h1 : Continuous (fun X : c13_E => X 1) := by fun_prop
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (isOpen_lt h1 ((hf.continuous.comp h0).sub continuous_const)).measurableSet
  have hSmono : Monotone S := fun m n hmn X hX => by
    simp only [hSdef, mem_ofPred_eq] at hX ⊢
    linarith [hdanti hmn]
  have hSU : (⋃ n, S n) = c13_patch F t := by
    ext X
    simp only [hSdef, mem_iUnion, mem_ofPred_eq, c13_patch]
    constructor
    · rintro ⟨n, hn⟩; linarith [hdpos n]
    · intro hX
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hX)
      exact ⟨n, by simp only [hddef]; linarith⟩
  have hL := tendsto_setIntegral_of_monotone hSm hSmono hgi.integrableOn
  rw [hSU] at hL
  -- boundary side
  obtain ⟨Ctr, hCtr, htr⟩ := (c13_normal_trace hα1 hα2 hc hF).1 R hR {t} htI isCompact_singleton
  have htr2 := (c13_normal_trace hα1 hα2 hc hF).2 
  obtain ⟨Wm, hWm⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hWt.continuousOn
  obtain ⟨Bz, hBz⟩ := hζ.continuous.bounded_above_of_compact_support hζc
  have hBz0 : 0 ≤ Bz := (norm_nonneg _).trans (hBz 0)
  have hWm0 : 0 ≤ Wm := (norm_nonneg _).trans (hWm 0 ⟨by linarith, by linarith⟩)
  have hfl := fun n => c13t_aux_shifted_flux (c := c) hα1 hF ht ζ hζ hζc (hdpos n)
  have hR' := tendsto_integral_of_dominated_convergence
    (fun x => (Icc (-R) R).indicator (fun _ => Bz * (Wm + Ctr)) x)
    (fun n => (hfl n).2.1.aestronglyMeasurable)
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp)))
    (fun n => Eventually.of_forall (fun x => by
      by_cases hx : |x| ≤ R
      · rw [indicator_of_mem (show x ∈ Icc (-R) R from abs_le.1 hx), norm_mul]
        refine mul_le_mul (hBz _) ?_ (norm_nonneg _) hBz0
        have h1 := htr x hx t rfl (-d n) (neg_ne_zero.2 (hdpos n).ne')
          (by rw [abs_neg, abs_of_pos (hdpos n)]; exact hdle n)
        have h2 : |-d n| ^ (2 - α) ≤ 1 :=
          rpow_le_one (abs_nonneg _) (by rw [abs_neg, abs_of_pos (hdpos n)]; exact hdle n)
            (by linarith)
        have h3 := hWm x (abs_le.1 hx)
        rw [Real.norm_eq_abs] at h3 ⊢
        have h4 := abs_sub_abs_le_abs_sub
          ((c13_graph_velocity α c F (c13_pt x (F x t + -d n)) t) 1 -
            deriv (fun x => F x t) x * (c13_graph_velocity α c F (c13_pt x (F x t + -d n)) t) 0)
          (c13_normal_speed α c F x t)
        nlinarith
      · have hx' : R < |x| := lt_of_not_ge hx
        rw [hζout x _ hx', zero_mul, norm_zero]
        exact indicator_nonneg (fun _ _ => mul_nonneg hBz0 (by linarith)) _))
    (Eventually.of_forall (fun x => by
      have hA : Tendsto (fun n => ζ (c13_pt x (F x t - d n))) atTop (𝓝 (ζ (c13_pt x (F x t)))) := by
        have hc' : Continuous (fun e : ℝ => ζ (c13_pt x (F x t - e))) :=
          hζ.continuous.comp (c13t_aux_pt_continuous.comp
            (continuous_const.prodMk (continuous_const.sub continuous_id)))
        have := (hc'.tendsto 0).comp hdlim
        simp only [sub_zero] at this
        exact this
      have hB := (htr2 x t ht).comp (tendsto_nhdsWithin_iff.2
        ⟨by simpa using hdlim.neg, Eventually.of_forall (fun n => neg_ne_zero.2 (hdpos n).ne')⟩)
      exact hA.mul hB))
  have heq : ∀ n, (∫ X in S n, g X) = ∫ x, ζ (c13_pt x (F x t - d n)) *
        ((c13_graph_velocity α c F (c13_pt x (F x t + -d n)) t) 1 -
          deriv (fun x => F x t) x *
            (c13_graph_velocity α c F (c13_pt x (F x t + -d n)) t) 0) := fun n => (hfl n).2.2
  have hR'' : Tendsto (fun n => ∫ X in S n, g X) atTop
      (𝓝 (∫ x, ζ (c13_pt x (F x t)) * c13_normal_speed α c F x t)) := by
    simp_rw [heq]; exact hR'
  rw [tendsto_nhds_unique hL hR'']
  congr 1; funext x; ring

theorem c13t_aux_test_tsupport {V : Type*} [NormedAddCommGroup V] {I : Set ℝ}
    {Φ : c13_E × ℝ → V} (hc : HasCompactSupport Φ) (hs : tsupport Φ ⊆ univ ×ˢ I) :
    IsCompact (Prod.fst '' tsupport Φ) ∧ IsCompact (Prod.snd '' tsupport Φ) ∧
      Prod.snd '' tsupport Φ ⊆ I ∧
      tsupport Φ ⊆ (Prod.fst '' tsupport Φ) ×ˢ (Prod.snd '' tsupport Φ) := by
  refine ⟨hc.image continuous_fst, hc.image continuous_snd, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩; exact (hs hp).2
  · intro p hp; exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩

theorem c13t_aux_slice_test {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : c13_E × ℝ → V} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun Y => Φ (Y, t)) ∧ HasCompactSupport (fun Y => Φ (Y, t)) ∧
      ∀ Y, Y ∉ Prod.fst '' tsupport Φ → Φ (Y, t) = 0 := by
  have h0 : ∀ Y, Y ∉ Prod.fst '' tsupport Φ → Φ (Y, t) = 0 := fun Y hY =>
    image_eq_zero_of_notMem_tsupport (fun h => hY ⟨(Y, t), h, rfl⟩)
  exact ⟨hΦ.comp (contDiff_id.prodMk contDiff_const),
    HasCompactSupport.intro (hc.image continuous_fst) h0, h0⟩


theorem c13t_aux_rotation_continuous : Continuous c13_rotation := by
  have : c13_rotation = fun z : c13_E => c13_pt (-(z 1)) (z 0) := rfl
  rw [this]
  exact c13t_aux_pt_continuous.comp (f := fun z : c13_E => (-(z 1), z 0)) (by fun_prop)

theorem c13t_aux_kernel_measurable (α c : ℝ) : Measurable (c13_velocity_kernel α c) := by
  unfold c13_velocity_kernel
  refine Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const ?_
  exact (measurable_const.mul (measurable_norm.pow_const _)).smul
    c13t_aux_rotation_continuous.measurable

theorem c13t_aux_adjoint_sm (α c : ℝ) {Φ : c13_E × ℝ → c13_E} (hΦ : Continuous Φ) :
    StronglyMeasurable (fun p : c13_E × ℝ => c13_adjoint α c (fun Y => Φ (Y, p.2)) p.1) := by
  unfold c13_adjoint
  have hH : StronglyMeasurable (fun q : (c13_E × ℝ) × c13_E =>
      inner ℝ (c13_velocity_kernel α c q.2) (Φ (q.1.1 + q.2, q.1.2) - Φ (q.1.1, q.1.2))) := by
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.inner ((c13t_aux_kernel_measurable α c).comp measurable_snd) ?_
    exact (hΦ.comp (by fun_prop)).measurable.sub (hΦ.comp (by fun_prop)).measurable
  exact hH.integral_prod_right' (ν := volume)

theorem c13t_aux_theta_set {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    ∃ A : Set (c13_E × ℝ), MeasurableSet A ∧ ∀ p ∈ (univ ×ˢ I : Set (c13_E × ℝ)),
      (c13_patch F p.2).indicator (1 : c13_E → ℝ) p.1 = A.indicator 1 p := by
  have hI : IsOpen I := hF.1
  have hc : ContinuousOn (fun p : c13_E × ℝ => F (p.1 0) p.2 - p.1 1) (univ ×ˢ I) := by
    refine ContinuousOn.sub ?_ (by fun_prop)
    exact (c13t_aux_F_contOn hF).comp (f := fun p : c13_E × ℝ => (p.1 0, p.2)) (by fun_prop)
      (fun p hp => ⟨mem_univ _, hp.2⟩)
  refine ⟨(univ ×ˢ I) ∩ (fun p : c13_E × ℝ => F (p.1 0) p.2 - p.1 1) ⁻¹' Ioi 0,
    (hc.isOpen_inter_preimage (isOpen_univ.prod hI) isOpen_Ioi).measurableSet, ?_⟩
  intro p hp
  by_cases h : p.1 1 < F (p.1 0) p.2
  · rw [indicator_of_mem (show p.1 ∈ c13_patch F p.2 from h),
      indicator_of_mem (show p ∈ (univ ×ˢ I) ∩
        (fun p : c13_E × ℝ => F (p.1 0) p.2 - p.1 1) ⁻¹' Ioi 0 from ⟨hp, by simp [h]⟩)]; rfl
  · rw [indicator_of_notMem (show p.1 ∉ c13_patch F p.2 from h),
      indicator_of_notMem (show p ∉ (univ ×ˢ I) ∩
        (fun p : c13_E × ℝ => F (p.1 0) p.2 - p.1 1) ⁻¹' Ioi 0 from
          fun h' => h (by simpa using h'.2))]

theorem c13t_aux_theta_aesm {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F)
    {S : Set (c13_E × ℝ)} (hS : S ⊆ univ ×ˢ I) (hSm : MeasurableSet S) :
    AEStronglyMeasurable (fun p : c13_E × ℝ => (c13_patch F p.2).indicator (1 : c13_E → ℝ) p.1)
      ((volume : Measure (c13_E × ℝ)).restrict S) := by
  obtain ⟨A, hA, hAeq⟩ := c13t_aux_theta_set hF
  refine (measurable_one.indicator hA).aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem hSm] with p hp
  exact (hAeq p (hS hp)).symm


theorem c13t_aux_slice_fderiv_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : c13_E × ℝ → V} (hΦ : Differentiable ℝ Φ) (Y : c13_E) (t : ℝ) :
    ‖fderiv ℝ (fun Y => Φ (Y, t)) Y‖ ≤ ‖fderiv ℝ Φ (Y, t)‖ := by
  have h : HasFDerivAt (fun Y => Φ (Y, t))
      ((fderiv ℝ Φ (Y, t)).comp ((ContinuousLinearMap.id ℝ c13_E).prod 0)) Y :=
    (hΦ (Y, t)).hasFDerivAt.comp Y ((hasFDerivAt_id Y).prodMk (hasFDerivAt_const t Y))
  rw [h.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have : ‖(ContinuousLinearMap.id ℝ c13_E).prod (0 : c13_E →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simp [Prod.norm_def])
  calc ‖fderiv ℝ Φ (Y, t)‖ * ‖(ContinuousLinearMap.id ℝ c13_E).prod (0 : c13_E →L[ℝ] ℝ)‖
      ≤ ‖fderiv ℝ Φ (Y, t)‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

/-- `L¹` bounds for the slices of a spacetime test, uniform in time. -/
theorem c13t_aux_slice_L1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : c13_E × ℝ → V} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) :
    ∃ B, 0 ≤ B ∧ ∀ t, (∫ Y, ‖Φ (Y, t)‖) + (∫ Y, ‖fderiv ℝ (fun Y => Φ (Y, t)) Y‖) ≤ B := by
  set Q := Prod.fst '' tsupport Φ
  have hQ : IsCompact Q := hc.image continuous_fst
  obtain ⟨B1, hB1⟩ := hΦ.continuous.bounded_above_of_compact_support hc
  obtain ⟨B2, hB2⟩ := (hΦ.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  refine ⟨B1 * volume.real Q + B2 * volume.real Q, by positivity, fun t => ?_⟩
  obtain ⟨-, -, h0⟩ := c13t_aux_slice_test hΦ hc t
  have hts : tsupport (fun Y => Φ (Y, t)) ⊆ Q :=
    closure_minimal (fun Y hY => by_contra fun h => hY (h0 Y h)) hQ.isClosed
  have hd0 : ∀ Y, Y ∉ Q → fderiv ℝ (fun Y => Φ (Y, t)) Y = 0 := fun Y hY =>
    fderiv_of_notMem_tsupport ℝ (fun h => hY (hts h))
  have e1 : (∫ Y, ‖Φ (Y, t)‖) = ∫ Y in Q, ‖Φ (Y, t)‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun Y hY => by simp [h0 Y hY])).symm
  have e2 : (∫ Y, ‖fderiv ℝ (fun Y => Φ (Y, t)) Y‖) =
      ∫ Y in Q, ‖fderiv ℝ (fun Y => Φ (Y, t)) Y‖ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun Y hY => by simp [hd0 Y hY])).symm
  rw [e1, e2]
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  refine add_le_add ?_ ?_
  · refine le_trans (le_abs_self _) ?_
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const hQ.measure_lt_top
      (fun Y _ => by rw [norm_norm]; exact hB1 _)
  · refine le_trans (le_abs_self _) ?_
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const hQ.measure_lt_top
      (fun Y _ => by rw [norm_norm]; exact (c13t_aux_slice_fderiv_norm hdiff Y t).trans (hB2 _))


theorem c13t_aux_adjoint_zero (α c : ℝ) : c13_adjoint α c (fun _ => (0 : c13_E)) = 0 := by
  funext Y; simp [c13_adjoint]

theorem c13t_aux_adjoint_spacetime {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {Φ : c13_E × ℝ → c13_E}
    (hΦ : c13_vector_test I Φ) :
    IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
      c13_adjoint α c (fun Y => Φ (Y, p.2)) p.1) (univ ×ˢ I) := by
  obtain ⟨hΦs, hΦc, hΦI⟩ := hΦ
  obtain ⟨-, hJ, hJI, -⟩ := c13t_aux_test_tsupport hΦc hΦI
  set J := Prod.snd '' tsupport Φ
  obtain ⟨C, hC, hadj⟩ := c13_adjoint_integrable hα1 hα2 c
  obtain ⟨B, hB0, hB⟩ := c13t_aux_slice_L1 hΦs hΦc
  set f : c13_E × ℝ → ℝ := fun p => (c13_patch F p.2).indicator 1 p.1 *
      c13_adjoint α c (fun Y => Φ (Y, p.2)) p.1 with hfdef
  have hzero : ∀ p : c13_E × ℝ, p ∉ univ ×ˢ J → f p = 0 := by
    intro p hp
    have ht : p.2 ∉ J := fun h => hp ⟨mem_univ _, h⟩
    have : (fun Y => Φ (Y, p.2)) = fun _ => 0 := funext fun Y =>
      image_eq_zero_of_notMem_tsupport (fun h => ht ⟨(Y, p.2), h, rfl⟩)
    simp only [hfdef, this, c13t_aux_adjoint_zero, Pi.zero_apply, mul_zero]
  have hfm : AEStronglyMeasurable f ((volume : Measure (c13_E × ℝ)).restrict (univ ×ˢ J)) :=
    (c13t_aux_theta_aesm hF (Set.prod_mono subset_rfl hJI) (MeasurableSet.univ.prod
      hJ.measurableSet)).mul (c13t_aux_adjoint_sm α c hΦs.continuous).aestronglyMeasurable
  have hfJ : IntegrableOn f (univ ×ˢ J) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hfm
    refine (integrable_prod_iff' hfm).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem hJ.measurableSet] with t ht
      obtain ⟨hs1, hs2, -⟩ := c13t_aux_slice_test hΦs hΦc t
      exact (hadj _ hs1 hs2).2.2.2.2 _ (measurable_one.indicator (c13t_aux_patch_isOpen
        (c13t_aux_F_cont_slice hF (hJI ht))).measurableSet) 1
        (fun Y => by simp only [indicator]; split_ifs <;> norm_num)
    · have : IsFiniteMeasure (volume.restrict J) :=
        isFiniteMeasure_restrict.2 hJ.measure_lt_top.ne
      refine Integrable.mono' (integrable_const (C * B)) hfm.norm.prod_swap.integral_prod_right'
        (ae_of_all _ fun t => ?_)
      obtain ⟨hs1, hs2, -⟩ := c13t_aux_slice_test hΦs hΦc t
      obtain ⟨-, -, hai, hale, -⟩ := hadj _ hs1 hs2
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc (∫ Y, ‖f (Y, t)‖) ≤ ∫ Y, |c13_adjoint α c (fun Y => Φ (Y, t)) Y| := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hai.abs
              (ae_of_all _ fun Y => ?_)
            simp only [hfdef, Real.norm_eq_abs, abs_mul]
            refine mul_le_of_le_one_left (abs_nonneg _) ?_
            simp only [indicator]; split_ifs <;> norm_num
        _ ≤ C * ((∫ Y, ‖Φ (Y, t)‖) + ∫ Y, ‖fderiv ℝ (fun Y => Φ (Y, t)) Y‖) := hale
        _ ≤ C * B := mul_le_mul_of_nonneg_left (hB t) hC.le
  exact (hfJ.integrable_of_forall_notMem_eq_zero hzero).integrableOn


theorem c13t_aux_pairing_integrable {I : Set ℝ} {u : c13_E → ℝ → c13_E}
    (hu : LocallyIntegrableOn (Function.uncurry u) (univ ×ˢ I)) {Φ : c13_E × ℝ → c13_E}
    (hΦ : c13_vector_test I Φ) :
    Integrable (fun p : c13_E × ℝ => inner ℝ (u p.1 p.2) (Φ p)) := by
  obtain ⟨hΦs, hΦc, hΦI⟩ := hΦ
  have hK : IntegrableOn (Function.uncurry u) (tsupport Φ) :=
    (hu.mono_set hΦI).integrableOn_isCompact hΦc
  obtain ⟨B, hB⟩ := hΦs.continuous.bounded_above_of_compact_support hΦc
  have hint : IntegrableOn (fun p : c13_E × ℝ => inner ℝ (u p.1 p.2) (Φ p)) (tsupport Φ) := by
    refine Integrable.mono' (hK.norm.mul_const B)
      (hK.aestronglyMeasurable.inner hΦs.continuous.aestronglyMeasurable)
      (ae_of_all _ fun p => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (hB p) (norm_nonneg _)
  exact hint.integrable_of_forall_notMem_eq_zero (fun p hp => by
    simp [image_eq_zero_of_notMem_tsupport hp])

theorem c13t_aux_fubini {I : Set ℝ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : c13_E × ℝ → V} (hf : IntegrableOn f (univ ×ˢ I)) :
    (∫ p in univ ×ˢ I, f p) = ∫ t in I, ∫ Y, f (Y, t) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  exact integral_prod_symm f hf

theorem c13t_aux_velocity_law {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X)
      (c13_graph_velocity α c F) := by
  have hI : IsOpen I := hF.1
  obtain ⟨-, hvl, -, -⟩ := c13_velocity_local_integrable hα1 hα2 c I F hF
  refine ⟨c13t_aux_theta_aesm hF subset_rfl (MeasurableSet.univ.prod hI.measurableSet),
    ⟨1, fun X t _ => by simp only [indicator]; split_ifs <;> norm_num⟩, hvl,
    fun Φ hΦ => ?_⟩
  have hpair := (c13t_aux_pairing_integrable (u := c13_graph_velocity α c F) hvl hΦ).integrableOn
    (s := univ ×ˢ I)
  have hadj := c13t_aux_adjoint_spacetime (c := c) hα1 hα2 hF hΦ
  refine ⟨hpair, hadj, ?_⟩
  rw [c13t_aux_fubini hpair, c13t_aux_fubini hadj]
  refine setIntegral_congr_fun hI.measurableSet (fun t ht => ?_)
  obtain ⟨hs1, hs2, -⟩ := c13t_aux_slice_test hΦ.1 hΦ.2.1 t
  obtain ⟨-, -, -, -, h5, h6⟩ := c13_bulk_contour_identity hα1 hα2 hF ht (fun Y => Φ (Y, t)) hs1 hs2
  exact (h5.trans h6).symm


theorem c13t_aux_slice_fderiv_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : c13_E × ℝ → V} (hΦ : Differentiable ℝ Φ) (Y : c13_E) (t : ℝ) :
    fderiv ℝ (fun Y => Φ (Y, t)) Y =
      (fderiv ℝ Φ (Y, t)).comp ((ContinuousLinearMap.id ℝ c13_E).prod 0) :=
  ((hΦ (Y, t)).hasFDerivAt.comp Y ((hasFDerivAt_id Y).prodMk (hasFDerivAt_const t Y))).fderiv

theorem c13t_aux_grad_test {I : Set ℝ} {ζ : c13_E × ℝ → ℝ} (hζ : c13_scalar_test I ζ) :
    c13_vector_test I (fun p => gradient (fun Y => ζ (Y, p.2)) p.1) := by
  obtain ⟨hs, hc, hI⟩ := hζ
  have hd : Differentiable ℝ ζ := hs.differentiable (by simp)
  have heq : (fun p : c13_E × ℝ => gradient (fun Y => ζ (Y, p.2)) p.1) = fun p =>
      (InnerProductSpace.toDual ℝ c13_E).symm
        ((fderiv ℝ ζ p).comp ((ContinuousLinearMap.id ℝ c13_E).prod 0)) := by
    funext p; simp only [gradient, c13t_aux_slice_fderiv_eq hd]
  have h0 : ∀ p, p ∉ tsupport ζ → gradient (fun Y => ζ (Y, p.2)) p.1 = 0 := by
    intro p hp
    have := congrFun heq p
    rw [this, fderiv_of_notMem_tsupport ℝ hp, ContinuousLinearMap.zero_comp, map_zero]
  have hsub : tsupport (fun p : c13_E × ℝ => gradient (fun Y => ζ (Y, p.2)) p.1) ⊆ tsupport ζ :=
    closure_minimal (fun p hp => by_contra fun h => hp (h0 p h)) (isClosed_tsupport ζ)
  refine ⟨?_, hc.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans hI⟩
  rw [heq]
  exact (InnerProductSpace.toDual ℝ c13_E).symm.contDiff.comp
    ((hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_comp contDiff_const)

theorem c13t_aux_unique {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) (u : c13_E → ℝ → c13_E)
    (hu : c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X) u) :
    ∀ᵐ p ∂((volume : Measure (c13_E × ℝ)).restrict (univ ×ˢ I)),
      u p.1 p.2 = c13_graph_velocity α c F p.1 p.2 := by
  have hI : IsOpen I := hF.1
  have hU := c13t_aux_velocity_law (c := c) hα1 hα2 hF
  set w : c13_E × ℝ → c13_E := fun p => u p.1 p.2 - c13_graph_velocity α c F p.1 p.2 with hwdef
  have hw : LocallyIntegrableOn w (univ ×ˢ I) := hu.2.2.1.sub hU.2.2.1
  have hS : IsOpen (univ ×ˢ I : Set (c13_E × ℝ)) := isOpen_univ.prod hI
  have key := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero hw (fun g hg hgc hgs => ?_)
  · rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards [key] with p hp hpS
    exact sub_eq_zero.1 (hp hpS)
  -- the integral of `g • w` vanishes
  have hgw : Integrable (fun p => g p • w p) := by
    have h1 : IntegrableOn w (tsupport g) := (hw.mono_set hgs).integrableOn_isCompact hgc
    exact (h1.continuousOn_smul hg.continuous.continuousOn hgc).integrable_of_forall_notMem_eq_zero
      (fun p hp => by simp [image_eq_zero_of_notMem_tsupport hp])
  have hinner : ∀ v : c13_E, inner ℝ (∫ p, g p • w p) v = 0 := by
    intro v
    have hΦ : c13_vector_test I (fun p => g p • v) :=
      ⟨hg.smul contDiff_const, hgc.smul_right, (tsupport_smul_subset_left _ _).trans hgs⟩
    obtain ⟨hi1, -, he1⟩ := hu.2.2.2 _ hΦ
    obtain ⟨hi2, -, he2⟩ := hU.2.2.2 _ hΦ
    have hdiff : (∫ p in univ ×ˢ I, inner ℝ (u p.1 p.2) (g p • v)) -
        (∫ p in univ ×ˢ I, inner ℝ (c13_graph_velocity α c F p.1 p.2) (g p • v)) = 0 := by
      rw [he1, he2, sub_self]
    rw [← integral_sub hi1 hi2] at hdiff
    rw [real_inner_comm, ← integral_inner hgw]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := univ ×ˢ I) (fun p hp => by
      have : g p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hgs h))
      simp [this])]
    rw [← hdiff]
    refine setIntegral_congr_fun hS.measurableSet (fun p _ => ?_)
    simp only [hwdef]
    rw [inner_smul_right, inner_smul_right, inner_smul_right, inner_sub_right,
      real_inner_comm v (u p.1 p.2), real_inner_comm v (c13_graph_velocity α c F p.1 p.2)]
    ring
  have := hinner (∫ p, g p • w p)
  rwa [inner_self_eq_zero] at this

theorem c13t_aux_divfree {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (u : c13_E → ℝ → c13_E)
    (hu : c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X) u)
    (ζ : c13_E × ℝ → ℝ) (hζ : c13_scalar_test I ζ) :
    IntegrableOn (fun p : c13_E × ℝ => fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2))
      (univ ×ˢ I) ∧
    (∫ p in univ ×ˢ I, fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2)) = 0 := by
  obtain ⟨hi, -, he⟩ := hu.2.2.2 _ (c13t_aux_grad_test hζ)
  have hfun : (fun p : c13_E × ℝ => inner ℝ (u p.1 p.2) (gradient (fun Y => ζ (Y, p.2)) p.1)) =
      fun p => fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2) := by
    funext p
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  rw [hfun] at hi he
  refine ⟨hi, he.trans ?_⟩
  obtain ⟨-, -, -, hpot⟩ := c13_test_potential hα1 hα2 c
  have : ∀ p : c13_E × ℝ,
      c13_adjoint α c (fun Y => gradient (fun Y => ζ (Y, p.2)) Y) p.1 = 0 := by
    intro p
    obtain ⟨hs1, hs2, -⟩ := c13t_aux_slice_test hζ.1 hζ.2.1 p.2
    exact hpot _ hs1 hs2 p.1
  simp [this]

/-- Blueprint: lem:c13_spatial_flux.  For every `t ∈ I` and scalar spatial test `ζ`,
`∫_{Ω_t} U(X,t) · ∇ζ(X) dX = ∫_ℝ W(x,t) ζ(x, F(x,t)) dx`, both absolutely convergent; and the
absolute integrals are bounded uniformly for `t` in a compact `J₀ ⊆ I` and tests supported in a
fixed compact `K` with `|ζ| ≤ B`, `‖Dζ‖ ≤ B`.  (`U · ∇ζ` is written `Dζ(X) (U(X,t))`.) -/
theorem c13_spatial_flux {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    (∀ t ∈ I, ∀ ζ : c13_E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      IntegrableOn (fun X => fderiv ℝ ζ X (c13_graph_velocity α c F X t)) (c13_patch F t) ∧
      Integrable (fun x => c13_normal_speed α c F x t * ζ (c13_pt x (F x t))) ∧
      (∫ X in c13_patch F t, fderiv ℝ ζ X (c13_graph_velocity α c F X t)) =
        ∫ x, c13_normal_speed α c F x t * ζ (c13_pt x (F x t))) ∧
    (∀ J₀ ⊆ I, IsCompact J₀ → ∀ K : Set c13_E, IsCompact K → ∀ B : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ J₀, ∀ ζ : c13_E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → tsupport ζ ⊆ K →
        (∀ X, |ζ X| ≤ B) → (∀ X, ‖fderiv ℝ ζ X‖ ≤ B) →
        (∫ X in c13_patch F t, |fderiv ℝ ζ X (c13_graph_velocity α c F X t)|) ≤ C ∧
        (∫ x, |c13_normal_speed α c F x t * ζ (c13_pt x (F x t))|) ≤ C) := by
  refine ⟨fun t ht ζ hζ hζc => ?_, fun J₀ hJ₀ hJc K hK B => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := c13t_aux_flux_fixed hα1 hα2 hc hF ht ζ hζ hζc
    exact ⟨h1.integrableOn, h2, h3⟩
  obtain ⟨Cw, -, hw⟩ := c13t_aux_U_weighted (c := c) hα1 hα2 hF hJ₀ hJc hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨-, hWc, -⟩ := c13_normal_speed_integrable hα1 hα2 hc hF
  have hsub : Icc (-R) R ×ˢ J₀ ⊆ univ ×ˢ I := prod_mono (subset_univ _) hJ₀
  obtain ⟨Wm, hWm⟩ := (isCompact_Icc.prod hJc).exists_bound_of_continuousOn (hWc.mono hsub)
  refine ⟨max (max (Cw * B) (2 * R * Wm * B)) 0, le_max_right _ _, ?_⟩
  intro t ht ζ hζ hζK hζB hDB
  have hζc : HasCompactSupport ζ := hK.of_isClosed_subset (isClosed_tsupport ζ) hζK
  constructor
  · have hDζc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv (by simp)
    obtain ⟨hwi, hwle⟩ := hw t ht (fun X => ‖fderiv ℝ ζ X‖) hDζc.norm.aestronglyMeasurable
      (fun X hX => by simp [fderiv_of_notMem_tsupport ℝ (fun h => hX (hζK h))]) B
      (fun X => by simpa using hDB X)
    have hpt : ∀ X, |fderiv ℝ ζ X (c13_graph_velocity α c F X t)| ≤
        ‖c13_graph_velocity α c F X t‖ * |‖fderiv ℝ ζ X‖| := fun X => by
      rw [abs_norm, mul_comm]; exact (fderiv ℝ ζ X).le_opNorm _
    calc (∫ X in c13_patch F t, |fderiv ℝ ζ X (c13_graph_velocity α c F X t)|)
        ≤ ∫ X in c13_patch F t, ‖c13_graph_velocity α c F X t‖ * |‖fderiv ℝ ζ X‖| :=
          integral_mono_of_nonneg (Eventually.of_forall (fun X => abs_nonneg _))
            hwi.integrableOn (Eventually.of_forall hpt)
      _ ≤ ∫ X, ‖c13_graph_velocity α c F X t‖ * |‖fderiv ℝ ζ X‖| :=
          setIntegral_le_integral hwi (Eventually.of_forall (fun X =>
            mul_nonneg (norm_nonneg _) (abs_nonneg _)))
      _ ≤ Cw * B := hwle
      _ ≤ _ := (le_max_left _ _).trans (le_max_left _ _)
  · have hpt : ∀ x, |c13_normal_speed α c F x t * ζ (c13_pt x (F x t))| ≤
        (Icc (-R) R).indicator (fun _ => Wm * B) x := by
      intro x
      by_cases hx : |x| ≤ R
      · rw [indicator_of_mem (abs_le.1 hx), abs_mul]
        have h1 := hWm (x, t) ⟨abs_le.1 hx, ht⟩
        rw [Real.norm_eq_abs] at h1
        exact mul_le_mul h1 (hζB _) (abs_nonneg _) ((abs_nonneg _).trans h1)
      · have hx' : R < |x| := lt_of_not_ge hx
        have : ζ (c13_pt x (F x t)) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          have := hR₀ (hζK hmem)
          rw [Metric.mem_closedBall, dist_zero_right] at this
          have := c13t_aux_abs_le_norm_pt x (F x t)
          have : R₀ ≤ R := le_max_left _ _
          linarith
        rw [this, mul_zero, abs_zero, indicator_of_notMem (fun h => hx (abs_le.2 h))]
    calc (∫ x, |c13_normal_speed α c F x t * ζ (c13_pt x (F x t))|)
        ≤ ∫ x, (Icc (-R) R).indicator (fun _ => Wm * B) x :=
          integral_mono_of_nonneg (Eventually.of_forall (fun x => abs_nonneg _))
            ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp)))
            (Eventually.of_forall hpt)
      _ = 2 * R * Wm * B := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul]
          rw [max_eq_left (by linarith)]; ring
      _ ≤ _ := (le_max_right _ _).trans (le_max_left _ _)

/-- Blueprint: lem:c13_velocity_law_unique.  `U[F]` satisfies the coefficient-`c` velocity law
for `θ_F` on `E × I`; every velocity satisfying that law for `θ_F` agrees with `U[F]` a.e. on
`E × I`; and every such velocity is distributionally divergence-free in space:
`∫_I∫_E u · ∇_X ζ = 0` (absolutely convergent) for every scalar spacetime test `ζ`. -/
theorem c13_velocity_law_unique {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X)
      (c13_graph_velocity α c F) ∧
    (∀ u : c13_E → ℝ → c13_E,
      c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X) u →
      ∀ᵐ p ∂((volume : Measure (c13_E × ℝ)).restrict (univ ×ˢ I)),
        u p.1 p.2 = c13_graph_velocity α c F p.1 p.2) ∧
    (∀ u : c13_E → ℝ → c13_E,
      c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X) u →
      ∀ ζ : c13_E × ℝ → ℝ, c13_scalar_test I ζ →
        IntegrableOn (fun p : c13_E × ℝ => fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2))
          (univ ×ˢ I) ∧
        (∫ p in univ ×ˢ I, fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2)) = 0) := by
  exact ⟨c13t_aux_velocity_law hα1 hα2 hF, fun u hu => c13t_aux_unique hα1 hα2 hF u hu,
    fun u hu ζ hζ => c13t_aux_divfree hα1 hα2 u hu ζ hζ⟩

/-! ### Helpers for the initial-value formulation -/

/-- Time cutoff: `0` for `t ≤ t₀ + h`, `1` for `t ≥ t₀ + 2h`. -/
def c13t_aux_tcut (t₀ h t : ℝ) : ℝ := Real.smoothTransition ((t - t₀) / h - 1)

theorem c13t_aux_tcut_contDiff (t₀ h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (c13t_aux_tcut t₀ h) :=
  Real.smoothTransition.contDiff.comp (((contDiff_id.sub contDiff_const).div_const h).sub
    contDiff_const)

theorem c13t_aux_tcut_zero {t₀ h t : ℝ} (hh : 0 < h) (ht : t ≤ t₀ + h) :
    c13t_aux_tcut t₀ h t = 0 := by
  unfold c13t_aux_tcut; apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, div_le_one hh]; linarith

theorem c13t_aux_tcut_one {t₀ h t : ℝ} (hh : 0 < h) (ht : t₀ + 2 * h ≤ t) :
    c13t_aux_tcut t₀ h t = 1 := by
  unfold c13t_aux_tcut; apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le, one_add_one_eq_two, le_div_iff₀ hh]; linarith

theorem c13t_aux_tcut_mono {t₀ h : ℝ} (hh : 0 < h) : Monotone (c13t_aux_tcut t₀ h) := by
  intro a b hab
  unfold c13t_aux_tcut
  apply Real.smoothTransition.monotone
  have : (a - t₀) / h ≤ (b - t₀) / h := div_le_div_of_nonneg_right (by linarith) hh.le
  linarith

theorem c13t_aux_tcut_bounds (t₀ h t : ℝ) : 0 ≤ c13t_aux_tcut t₀ h t ∧ c13t_aux_tcut t₀ h t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem c13t_aux_tcut_deriv_zero {t₀ h t : ℝ} (hh : 0 < h) (ht : t < t₀ + h ∨ t₀ + 2 * h < t) :
    deriv (c13t_aux_tcut t₀ h) t = 0 := by
  rcases ht with ht | ht
  · have : c13t_aux_tcut t₀ h =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs using c13t_aux_tcut_zero hh (le_of_lt hs)
    rw [this.deriv_eq]; simp
  · have : c13t_aux_tcut t₀ h =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using c13t_aux_tcut_one hh (le_of_lt hs)
    rw [this.deriv_eq]; simp

theorem c13t_aux_tcut_integral {t₀ h a b : ℝ} (hh : 0 < h) (ha : a ≤ t₀ + h)
    (hb : t₀ + 2 * h ≤ b) : ∫ t in a..b, deriv (c13t_aux_tcut t₀ h) t = 1 := by
  have hc := c13t_aux_tcut_contDiff t₀ h
  rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hc.differentiable (by simp) x)
    ((hc.continuous_deriv (by simp)).intervalIntegrable _ _),
    c13t_aux_tcut_one hh hb, c13t_aux_tcut_zero hh ha, sub_zero]


/-- The cut-off test `χ_h(t) ζ(X,t)` on `t ∈ (t₀, t₁)`, extended by zero. -/
def c13t_aux_ztest (t₀ t₁ h : ℝ) (ζ : c13_E × ℝ → ℝ) (p : c13_E × ℝ) : ℝ :=
  if p.2 ∈ Ioo t₀ t₁ then c13t_aux_tcut t₀ h p.2 * ζ p else 0

/-- Standing hypotheses on an initial-value test on `[t₀, t₁]`. -/
structure c13t_aux_ivtest (t₀ t₁ : ℝ) (ζ : c13_E × ℝ → ℝ) (K : Set c13_E) (δ : ℝ) : Prop where
  lt : t₀ < t₁
  open_nhd : ∃ O : Set (c13_E × ℝ), IsOpen O ∧ univ ×ˢ Icc t₀ t₁ ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ζ O
  compact : IsCompact K
  supp : ∀ t ∈ Icc t₀ t₁, ∀ X, X ∉ K → ζ (X, t) = 0
  dpos : 0 < δ
  vanish : ∀ t ∈ Icc (t₁ - δ) t₁, ∀ X, ζ (X, t) = 0

theorem c13t_aux_ivtest.contDiffAt {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) {p : c13_E × ℝ} (hp : p.2 ∈ Icc t₀ t₁) :
    ContDiffAt ℝ (⊤ : ℕ∞) ζ p := by
  obtain ⟨O, hO, hOS, hζ⟩ := hz.open_nhd
  exact hζ.contDiffAt (hO.mem_nhds (hOS ⟨mem_univ _, hp⟩))

theorem c13t_aux_ztest_zero_low {t₀ t₁ h : ℝ} (hh : 0 < h) {ζ : c13_E × ℝ → ℝ} {p : c13_E × ℝ}
    (hp : p.2 < t₀ + h) : c13t_aux_ztest t₀ t₁ h ζ p = 0 := by
  unfold c13t_aux_ztest; split_ifs
  · rw [c13t_aux_tcut_zero hh hp.le, zero_mul]
  · rfl

theorem c13t_aux_ztest_zero_high {t₀ t₁ h : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) {p : c13_E × ℝ}
    (hp : t₁ - δ < p.2) : c13t_aux_ztest t₀ t₁ h ζ p = 0 := by
  unfold c13t_aux_ztest; split_ifs with h1
  · rw [hz.vanish p.2 ⟨hp.le, h1.2.le⟩ p.1, mul_zero]
  · rfl

theorem c13t_aux_ztest_test {I : Set ℝ} {t₀ t₁ h : ℝ} (hh : 0 < h) {ζ : c13_E × ℝ → ℝ}
    {K : Set c13_E} {δ : ℝ} (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) (hI : Ioo t₀ t₁ ⊆ I) :
    c13_scalar_test I (c13t_aux_ztest t₀ t₁ h ζ) := by
  have hsupp : Function.support (c13t_aux_ztest t₀ t₁ h ζ) ⊆ K ×ˢ Icc (t₀ + h) (t₁ - δ) := by
    intro p hp
    have hlow : ¬ p.2 < t₀ + h := fun h' => hp (c13t_aux_ztest_zero_low hh h')
    have hhigh : ¬ t₁ - δ < p.2 := fun h' => hp (c13t_aux_ztest_zero_high hz h')
    have hin : p.2 ∈ Ioo t₀ t₁ := by
      by_contra hc; exact hp (by unfold c13t_aux_ztest; rw [if_neg hc])
    refine ⟨?_, not_lt.1 hlow, not_lt.1 hhigh⟩
    by_contra hK
    exact hp (by unfold c13t_aux_ztest; rw [if_pos hin, hz.supp p.2 (Ioo_subset_Icc_self hin)
      p.1 hK, mul_zero])
  have hcl : IsClosed (K ×ˢ Icc (t₀ + h) (t₁ - δ)) := hz.compact.isClosed.prod isClosed_Icc
  have hts : tsupport (c13t_aux_ztest t₀ t₁ h ζ) ⊆ K ×ˢ Icc (t₀ + h) (t₁ - δ) :=
    closure_minimal hsupp hcl
  refine ⟨?_, (hz.compact.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans (Set.prod_mono (subset_univ _) (fun t ht => hI ⟨by linarith [ht.1],
      by linarith [ht.2, hz.dpos]⟩))⟩
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases h1 : p.2 < t₀ + h
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds h1] with q hq
    exact c13t_aux_ztest_zero_low hh hq
  by_cases h2 : t₁ - δ < p.2
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds h2] with q hq
    exact c13t_aux_ztest_zero_high hz hq
  have hin : p.2 ∈ Ioo t₀ t₁ := ⟨by linarith [not_lt.1 h1], by linarith [not_lt.1 h2, hz.dpos]⟩
  have hev : c13t_aux_ztest t₀ t₁ h ζ =ᶠ[𝓝 p] fun q => c13t_aux_tcut t₀ h q.2 * ζ q := by
    filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds hin] with q hq
    unfold c13t_aux_ztest; rw [if_pos (show q.2 ∈ Ioo t₀ t₁ from hq)]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact ((c13t_aux_tcut_contDiff t₀ h).comp contDiff_snd).contDiffAt.mul
    (hz.contDiffAt (Ioo_subset_Icc_self hin))


theorem c13t_aux_ztest_derivs {t₀ t₁ h : ℝ} (hh : 0 < h) {ζ : c13_E × ℝ → ℝ}
    {K : Set c13_E} {δ : ℝ} (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) (p : c13_E × ℝ) :
    deriv (fun s => c13t_aux_ztest t₀ t₁ h ζ (p.1, s)) p.2 =
      (if p.2 ∈ Ioo t₀ t₁ then deriv (c13t_aux_tcut t₀ h) p.2 * ζ p +
        c13t_aux_tcut t₀ h p.2 * deriv (fun s => ζ (p.1, s)) p.2 else 0) ∧
    fderiv ℝ (fun Y => c13t_aux_ztest t₀ t₁ h ζ (Y, p.2)) p.1 =
      (if p.2 ∈ Ioo t₀ t₁ then c13t_aux_tcut t₀ h p.2 • fderiv ℝ (fun Y => ζ (Y, p.2)) p.1
        else 0) := by
  by_cases hin : p.2 ∈ Ioo t₀ t₁
  · rw [if_pos hin, if_pos hin]
    have hζp := hz.contDiffAt (Ioo_subset_Icc_self hin)
    have hd1 : DifferentiableAt ℝ (fun s => ζ (p.1, s)) p.2 :=
      (hζp.differentiableAt (by simp)).comp p.2
        ((differentiableAt_const _).prodMk differentiableAt_id)
    have hd2 : DifferentiableAt ℝ (fun Y => ζ (Y, p.2)) p.1 :=
      (hζp.differentiableAt (by simp)).comp p.1
        (differentiableAt_id.prodMk (differentiableAt_const _))
    constructor
    · have hev : (fun s => c13t_aux_ztest t₀ t₁ h ζ (p.1, s)) =ᶠ[𝓝 p.2]
          fun s => c13t_aux_tcut t₀ h s * ζ (p.1, s) := by
        filter_upwards [isOpen_Ioo.mem_nhds hin] with s hs
        unfold c13t_aux_ztest; rw [if_pos (show (p.1, s).2 ∈ Ioo t₀ t₁ from hs)]
      rw [hev.deriv_eq, deriv_fun_mul ((c13t_aux_tcut_contDiff t₀ h).differentiable (by simp) _) hd1]
    · have hfun : (fun Y => c13t_aux_ztest t₀ t₁ h ζ (Y, p.2)) =
          fun Y => c13t_aux_tcut t₀ h p.2 * ζ (Y, p.2) := by
        funext Y; unfold c13t_aux_ztest; rw [if_pos (show (Y, p.2).2 ∈ Ioo t₀ t₁ from hin)]
      rw [hfun, fderiv_const_mul hd2]
  · rw [if_neg hin, if_neg hin]
    constructor
    · rcases not_and_or.1 hin with h1 | h1
      · have hev : (fun s => c13t_aux_ztest t₀ t₁ h ζ (p.1, s)) =ᶠ[𝓝 p.2] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds (show p.2 < t₀ + h by linarith [not_lt.1 h1])] with s hs
          exact c13t_aux_ztest_zero_low hh hs
        rw [hev.deriv_eq]; simp
      · have hev : (fun s => c13t_aux_ztest t₀ t₁ h ζ (p.1, s)) =ᶠ[𝓝 p.2] fun _ => 0 := by
          filter_upwards [Ioi_mem_nhds (show t₁ - δ < p.2 by linarith [not_lt.1 h1, hz.dpos])]
            with s hs
          exact c13t_aux_ztest_zero_high hz hs
        rw [hev.deriv_eq]; simp
    · have hfun : (fun Y => c13t_aux_ztest t₀ t₁ h ζ (Y, p.2)) = fun _ => 0 := by
        funext Y; unfold c13t_aux_ztest; rw [if_neg (show ¬ (Y, p.2).2 ∈ Ioo t₀ t₁ from hin)]
      rw [hfun]; simp


theorem c13t_aux_tcut_deriv_nonneg {t₀ h : ℝ} (hh : 0 < h) (t : ℝ) :
    0 ≤ deriv (c13t_aux_tcut t₀ h) t := (c13t_aux_tcut_mono hh).deriv_nonneg

theorem c13t_aux_tcut_Ioo_integral {t₀ t₁ h : ℝ} (hh : 0 < h) (h2 : t₀ + 2 * h ≤ t₁) :
    ∫ t in Ioo t₀ t₁, deriv (c13t_aux_tcut t₀ h) t = 1 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  exact c13t_aux_tcut_integral hh (by linarith) h2

theorem c13t_aux_tcut_deriv_integrableOn (t₀ h a b : ℝ) :
    IntegrableOn (deriv (c13t_aux_tcut t₀ h)) (Ioo a b) :=
  (((c13t_aux_tcut_contDiff t₀ h).continuous_deriv (by simp)).integrableOn_Icc).mono_set
    Ioo_subset_Icc_self

/-- The mollified initial term converges to the trace value. -/
theorem c13t_aux_initial_limit {t₀ t₁ : ℝ} (ht : t₀ < t₁) {g : ℝ → ℝ} {g₀ : ℝ}
    (hg : Tendsto g (𝓝[>] t₀) (𝓝 g₀))
    (hint : ∀ n : ℕ, IntegrableOn (fun t => deriv (c13t_aux_tcut t₀
      ((t₁ - t₀) / (4 * ((n : ℝ) + 1)))) t * g t) (Ioo t₀ t₁)) :
    Tendsto (fun n : ℕ => ∫ t in Ioo t₀ t₁, deriv (c13t_aux_tcut t₀
      ((t₁ - t₀) / (4 * ((n : ℝ) + 1)))) t * g t) atTop (𝓝 g₀) := by
  set hs : ℕ → ℝ := fun n => (t₁ - t₀) / (4 * ((n : ℝ) + 1)) with hsdef
  have hpos : ∀ n, 0 < hs n := fun n => by simp only [hsdef]; apply div_pos <;> [linarith; positivity]
  have h2 : ∀ n, t₀ + 2 * hs n ≤ t₁ := fun n => by
    simp only [hsdef]
    have : (t₁ - t₀) / (4 * ((n : ℝ) + 1)) ≤ (t₁ - t₀) / 4 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num)
        (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    linarith
  have hlim0 : Tendsto hs atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((t₁ - t₀) / 4) * (1 / ((n : ℝ) + 1))) atTop (𝓝 (((t₁ - t₀) / 4) * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    simp only [hsdef]; field_simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hgη⟩ := Metric.mem_nhdsWithin_iff.1 (Metric.tendsto_nhds.1 hg (ε / 2) (by linarith))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim0 (η / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hhn := hN n hn
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (hpos n)] at hhn
  set χ' := deriv (c13t_aux_tcut t₀ (hs n))
  have hχi : IntegrableOn χ' (Ioo t₀ t₁) := c13t_aux_tcut_deriv_integrableOn _ _ _ _
  have h1 : (∫ t in Ioo t₀ t₁, χ' t * g t) - g₀ = ∫ t in Ioo t₀ t₁, χ' t * (g t - g₀) := by
    have : (∫ t in Ioo t₀ t₁, χ' t * g t) - g₀ =
        (∫ t in Ioo t₀ t₁, χ' t * g t) - ∫ t in Ioo t₀ t₁, χ' t * g₀ := by
      rw [integral_mul_const, c13t_aux_tcut_Ioo_integral (hpos n) (h2 n), one_mul]
    rw [this, ← integral_sub (hint n) (hχi.mul_const g₀)]
    congr 1; funext t; ring
  rw [Real.dist_eq, h1]
  have hbd : ∀ t ∈ Ioo t₀ t₁, ‖χ' t * (g t - g₀)‖ ≤ ε / 2 * χ' t := by
    intro t ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (c13t_aux_tcut_deriv_nonneg (hpos n) t)]
    by_cases hcase : t < t₀ + hs n ∨ t₀ + 2 * hs n < t
    · simp [χ', c13t_aux_tcut_deriv_zero (hpos n) hcase]
    · rw [not_or, not_lt, not_lt] at hcase
      have hmem : t ∈ Metric.ball t₀ η ∩ Ioi t₀ := by
        refine ⟨?_, ht.1⟩
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith [ht.1])]
        linarith [hcase.2]
      have := hgη hmem
      simp only [mem_ofPred_eq, Real.dist_eq] at this
      rw [mul_comm (ε / 2)]
      exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact this.le)
        (c13t_aux_tcut_deriv_nonneg (hpos n) t)
  calc |∫ t in Ioo t₀ t₁, χ' t * (g t - g₀)| ≤ ∫ t in Ioo t₀ t₁, ε / 2 * χ' t := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (hχi.const_mul _)
          ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ hbd))
    _ = ε / 2 := by rw [integral_const_mul, c13t_aux_tcut_Ioo_integral (hpos n) (h2 n), mul_one]
    _ < ε := by linarith


theorem c13t_aux_ivtest.bound {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) :
    ∃ B, 0 ≤ B ∧ ∀ t ∈ Icc t₀ t₁, ∀ X, |ζ (X, t)| ≤ B := by
  have hcont : ContinuousOn ζ (K ×ˢ Icc t₀ t₁) := fun p hp =>
    (hz.contDiffAt hp.2).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := (hz.compact.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, fun t ht X => ?_⟩
  by_cases hX : X ∈ K
  · exact (hB (X, t) ⟨hX, ht⟩).trans (le_max_left _ _)
  · rw [hz.supp t ht X hX, abs_zero]; exact le_max_right _ _

theorem c13t_aux_ivtest.slice_cont {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    Continuous (fun X => ζ (X, t)) :=
  continuous_iff_continuousAt.2 fun X =>
    ContinuousAt.comp (g := ζ) (f := fun Y : c13_E => (Y, t))
      (hz.contDiffAt (p := (X, t)) ht).continuousAt
      (continuous_id.prodMk continuous_const).continuousAt

theorem c13t_aux_g_tendsto {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) (θ : c13_E → ℝ → ℝ)
    (hθm : ∀ t ∈ Ioo t₀ t₁, Measurable (fun X => θ X t)) (hθb : ∀ X t, |θ X t| ≤ 1)
    (θ₀ : c13_E → ℝ) (hθ₀m : Measurable θ₀) (hθ₀b : ∀ X, |θ₀ X| ≤ 1)
    (hlim : Tendsto (fun t => ∫ X in K, |θ X t - θ₀ X|) (𝓝[>] t₀) (𝓝 0)) :
    Tendsto (fun t => ∫ X, θ X t * ζ (X, t)) (𝓝[>] t₀) (𝓝 (∫ X, θ₀ X * ζ (X, t₀))) := by
  obtain ⟨B, hB0, hB⟩ := hz.bound
  have hKf : volume K < ⊤ := hz.compact.measure_lt_top
  have ht₀ : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, hz.lt.le⟩
  have hev : Ioo t₀ t₁ ∈ 𝓝[>] t₀ := Ioo_mem_nhdsGT hz.lt
  -- convergence of the test slices on `K`
  have hζlim : Tendsto (fun t => ∫ X in K, |ζ (X, t) - ζ (X, t₀)|) (𝓝[>] t₀) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K)
      (F := fun t X => |ζ (X, t) - ζ (X, t₀)|) (f := fun _ => 0) (fun _ => 2 * B)
      (by filter_upwards [hev] with t ht
          exact (((hz.slice_cont (Ioo_subset_Icc_self ht)).sub
            (hz.slice_cont ht₀)).abs).aestronglyMeasurable)
      (by filter_upwards [hev] with t ht
          refine ae_of_all _ fun X => ?_
          rw [Real.norm_eq_abs, abs_abs]
          refine (abs_sub _ _).trans ?_
          linarith [hB t (Ioo_subset_Icc_self ht) X, hB t₀ ht₀ X])
      (integrableOn_const hKf.ne)
      (ae_of_all _ fun X => by
        have hc : ContinuousAt (fun t => ζ (X, t)) t₀ :=
          ContinuousAt.comp (g := ζ) (f := fun s : ℝ => (X, s))
            (hz.contDiffAt (p := (X, t₀)) ht₀).continuousAt
            (continuous_const.prodMk continuous_id).continuousAt
        have h3 : ContinuousAt (fun t => |ζ (X, t) - ζ (X, t₀)|) t₀ :=
          (hc.sub continuousAt_const).abs
        have := h3.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi t₀))
        simpa using this)
    simpa using this
  -- the main estimate
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Tendsto (fun t => B * (∫ X in K, |θ X t - θ₀ X|) +
      ∫ X in K, |ζ (X, t) - ζ (X, t₀)|) (𝓝[>] t₀) (𝓝 0) := by
    simpa using (hlim.const_mul B).add hζlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsum
  · filter_upwards [hev] with t ht
    have htI := Ioo_subset_Icc_self ht
    have hc1 := hz.slice_cont htI
    have hc0 := hz.slice_cont ht₀
    have hz1 : ∀ X, X ∉ K → θ X t * ζ (X, t) = 0 := fun X hX => by rw [hz.supp t htI X hX, mul_zero]
    have hz0 : ∀ X, X ∉ K → θ₀ X * ζ (X, t₀) = 0 := fun X hX => by
      rw [hz.supp t₀ ht₀ X hX, mul_zero]
    have hi1 : IntegrableOn (fun X => θ X t * ζ (X, t)) K :=
      Measure.integrableOn_of_bounded (M := B) hKf.ne
        ((hθm t ht).aestronglyMeasurable.mul hc1.aestronglyMeasurable)
        (ae_of_all _ fun X => by
          rw [Real.norm_eq_abs, abs_mul]
          nlinarith [hθb X t, hB t htI X, abs_nonneg (θ X t), abs_nonneg (ζ (X, t))])
    have hi0 : IntegrableOn (fun X => θ₀ X * ζ (X, t₀)) K :=
      Measure.integrableOn_of_bounded (M := B) hKf.ne
        (hθ₀m.aestronglyMeasurable.mul hc0.aestronglyMeasurable)
        (ae_of_all _ fun X => by
          rw [Real.norm_eq_abs, abs_mul]
          nlinarith [hθ₀b X, hB t₀ ht₀ X, abs_nonneg (θ₀ X), abs_nonneg (ζ (X, t₀))])
    have hiθ : IntegrableOn (fun X => |θ X t - θ₀ X|) K :=
      Measure.integrableOn_of_bounded (M := 2) hKf.ne
        (((hθm t ht).sub hθ₀m).abs.aestronglyMeasurable)
        (ae_of_all _ fun X => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (by linarith [hθb X t, hθ₀b X]))
    have hiζ : IntegrableOn (fun X => |ζ (X, t) - ζ (X, t₀)|) K :=
      Measure.integrableOn_of_bounded (M := 2 * B) hKf.ne
        ((hc1.sub hc0).abs.aestronglyMeasurable)
        (ae_of_all _ fun X => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (by linarith [hB t htI X, hB t₀ ht₀ X]))
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz1,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hz0, ← integral_sub hi1 hi0,
      ← integral_const_mul, ← integral_add (hiθ.const_mul B) hiζ]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ => norm_nonneg _) ((hiθ.const_mul B).add hiζ) (ae_of_all _ fun X => ?_))
    simp only [Real.norm_eq_abs]
    have e : θ X t * ζ (X, t) - θ₀ X * ζ (X, t₀) =
        (θ X t - θ₀ X) * ζ (X, t) + θ₀ X * (ζ (X, t) - ζ (X, t₀)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := hB t htI X
    have h2 := hθ₀b X
    nlinarith [abs_nonneg (θ X t - θ₀ X), abs_nonneg (ζ (X, t) - ζ (X, t₀)),
      abs_nonneg (θ₀ X), abs_nonneg (ζ (X, t))]


theorem c13t_aux_hs {t₀ t₁ : ℝ} (ht : t₀ < t₁) :
    (∀ n : ℕ, 0 < (t₁ - t₀) / (4 * ((n : ℝ) + 1))) ∧
    Tendsto (fun n : ℕ => (t₁ - t₀) / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
  refine ⟨fun n => div_pos (by linarith) (by positivity), ?_⟩
  have : Tendsto (fun n : ℕ => ((t₁ - t₀) / 4) * (1 / ((n : ℝ) + 1))) atTop
      (𝓝 (((t₁ - t₀) / 4) * 0)) := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
  rw [mul_zero] at this
  refine this.congr (fun n => ?_)
  field_simp

theorem c13t_aux_fubini_int {J : Set ℝ} {f : c13_E × ℝ → ℝ} (hf : IntegrableOn f (univ ×ˢ J)) :
    IntegrableOn (fun t => ∫ X, f (X, t)) J := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hf
  exact hf.integral_prod_right

theorem c13t_aux_initial_core {α c : ℝ} {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hF : c13_graph_class I F) {u : c13_E → ℝ → c13_E}
    (hw : c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X) u)
    {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) (hI : Ioo t₀ t₁ ⊆ I)
    (θ₀ : c13_E → ℝ) (hθ₀m : Measurable θ₀) (hθ₀b : ∀ X, |θ₀ X| ≤ 1)
    (hlim : Tendsto (fun t => ∫ X in K, |(c13_patch F t).indicator 1 X - θ₀ X|) (𝓝[>] t₀) (𝓝 0))
    (hG : IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2)))
      (univ ×ˢ Ioo t₀ t₁)) :
    (∫ p in univ ×ˢ Ioo t₀ t₁, (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2))) +
      (∫ X, θ₀ X * ζ (X, t₀)) = 0 := by
  set G : c13_E × ℝ → ℝ := fun p => (c13_patch F p.2).indicator 1 p.1 *
      (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2)) with hGdef
  set θ : c13_E × ℝ → ℝ := fun p => (c13_patch F p.2).indicator 1 p.1 with hθdef
  have hθb : ∀ p, |θ p| ≤ 1 := fun p => by
    simp only [hθdef, indicator]; split_ifs <;> norm_num
  obtain ⟨hpos, hlim0⟩ := c13t_aux_hs hz.lt
  set hs : ℕ → ℝ := fun n => (t₁ - t₀) / (4 * ((n : ℝ) + 1)) with hsdef
  set S : Set (c13_E × ℝ) := univ ×ˢ Ioo t₀ t₁ with hSdef
  have hSm : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioo
  have hSI : S ⊆ univ ×ˢ I := Set.prod_mono subset_rfl hI
  have hθm := c13t_aux_theta_aesm hF hSI hSm
  obtain ⟨Bζ, hBζ0, hBζ⟩ := hz.bound
  have hζS : ContinuousOn ζ S := fun p hp =>
    (hz.contDiffAt (Ioo_subset_Icc_self hp.2)).continuousAt.continuousWithinAt
  set A : ℕ → c13_E × ℝ → ℝ := fun n p => θ p * (deriv (c13t_aux_tcut t₀ (hs n)) p.2 * ζ p)
    with hAdef
  set B : ℕ → c13_E × ℝ → ℝ := fun n p => c13t_aux_tcut t₀ (hs n) p.2 * G p with hBdef
  have hBi : ∀ n, IntegrableOn (B n) S := fun n =>
    Integrable.bdd_mul (c := 1) hG
      (((c13t_aux_tcut_contDiff t₀ (hs n)).continuous.comp continuous_snd).aestronglyMeasurable)
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (c13t_aux_tcut_bounds _ _ _).1]
        exact (c13t_aux_tcut_bounds _ _ _).2)
  have hAi : ∀ n, IntegrableOn (A n) S := by
    intro n
    have hdc := (c13t_aux_tcut_contDiff t₀ (hs n)).continuous_deriv (n := (⊤ : ℕ∞)) (by simp)
    obtain ⟨D, hD⟩ := hdc.bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := t₀ + hs n) (b := t₀ + 2 * hs n))
        (fun t ht => by
          rw [mem_Icc, not_and_or, not_le, not_le] at ht
          exact c13t_aux_tcut_deriv_zero (hpos n) ht))
    have hKI : IsCompact (K ×ˢ Icc t₀ t₁) := hz.compact.prod isCompact_Icc
    refine Integrable.mono' (g := (K ×ˢ Icc t₀ t₁).indicator (fun _ => D * Bζ))
      ((integrable_indicator_iff hKI.measurableSet).2
        (integrableOn_const hKI.measure_lt_top.ne)).integrableOn
      (hθm.mul ((hdc.comp continuous_snd).aestronglyMeasurable.mul
        (hζS.aestronglyMeasurable hSm)))
      ((ae_restrict_iff' hSm).2 (ae_of_all _ fun p hp => ?_))
    have hpI := Ioo_subset_Icc_self hp.2
    rw [Real.norm_eq_abs]
    by_cases hK : p.1 ∈ K
    · rw [indicator_of_mem (show p ∈ K ×ˢ Icc t₀ t₁ from ⟨hK, hpI⟩), hAdef]
      simp only
      rw [abs_mul, abs_mul]
      have h1 := hθb p
      have h2 : |deriv (c13t_aux_tcut t₀ (hs n)) p.2| ≤ D := by
        have := hD p.2; rwa [Real.norm_eq_abs] at this
      have h3 := hBζ p.2 hpI p.1
      have hD0 : 0 ≤ D := (abs_nonneg _).trans h2
      calc |θ p| * (|deriv (c13t_aux_tcut t₀ (hs n)) p.2| * |ζ p|) ≤ 1 * (D * Bζ) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) hD0) (by positivity) zero_le_one
        _ = D * Bζ := one_mul _
    · have : ζ p = 0 := hz.supp p.2 hpI p.1 hK
      simp only [hAdef, this, mul_zero, abs_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hD 0)) hBζ0) _
  -- the weak law applied to the cut-off tests
  have hsplit : ∀ n, (∫ p in S, A n p) + (∫ p in S, B n p) = 0 := by
    intro n
    have hlaw := (hw.2 _ (c13t_aux_ztest_test (I := I) (hpos n) hz hI)).2
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (MeasurableSet.univ.prod hF.1.measurableSet)
      hSI (fun p hp => ?_)] at hlaw
    · rw [← integral_add (hAi n) (hBi n), ← hlaw]
      refine setIntegral_congr_fun hSm (fun p hp => ?_)
      obtain ⟨h1, h2⟩ := c13t_aux_ztest_derivs (hpos n) hz p
      simp only [h1, h2, if_pos hp.2, hAdef, hBdef, hGdef, hθdef, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      ring
    · obtain ⟨h1, h2⟩ := c13t_aux_ztest_derivs (t₁ := t₁) (hpos n) hz p
      have hnot : p.2 ∉ Ioo t₀ t₁ := fun h => hp.2 ⟨mem_univ _, h⟩
      simp only [h1, h2, if_neg hnot, ContinuousLinearMap.zero_apply, add_zero, mul_zero]
  -- the initial term
  set g : ℝ → ℝ := fun t => ∫ X, θ (X, t) * ζ (X, t) with hgdef
  have hAeq : ∀ n, (∫ p in S, A n p) =
      ∫ t in Ioo t₀ t₁, deriv (c13t_aux_tcut t₀ (hs n)) t * g t := by
    intro n
    rw [c13t_aux_fubini (hAi n)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
    simp only [hgdef]
    rw [← integral_const_mul]
    congr 1; funext X; simp only [hAdef]; ring
  have hAint : ∀ n, IntegrableOn (fun t => deriv (c13t_aux_tcut t₀ (hs n)) t * g t)
      (Ioo t₀ t₁) := by
    intro n
    refine (c13t_aux_fubini_int (hAi n)).congr_fun (fun t _ => ?_) measurableSet_Ioo
    simp only [hgdef]
    rw [← integral_const_mul]
    congr 1; funext X; simp only [hAdef]; ring
  have hgl : Tendsto g (𝓝[>] t₀) (𝓝 (∫ X, θ₀ X * ζ (X, t₀))) :=
    c13t_aux_g_tendsto hz (fun X t => (c13_patch F t).indicator 1 X)
      (fun t ht => measurable_one.indicator
        (c13t_aux_patch_isOpen (c13t_aux_F_cont_slice hF (hI ht))).measurableSet)
      (fun X t => hθb (X, t)) θ₀ hθ₀m hθ₀b hlim
  have hLA : Tendsto (fun n => ∫ p in S, A n p) atTop (𝓝 (∫ X, θ₀ X * ζ (X, t₀))) := by
    simp_rw [hAeq]
    exact c13t_aux_initial_limit hz.lt hgl hAint
  -- the bulk term
  have hLB : Tendsto (fun n => ∫ p in S, B n p) atTop (𝓝 (∫ p in S, G p)) := by
    refine tendsto_integral_of_dominated_convergence (fun p => ‖G p‖)
      (fun n => (hBi n).aestronglyMeasurable) hG.norm (fun n => ae_of_all _ fun p => ?_)
      ((ae_restrict_iff' hSm).2 (ae_of_all _ fun p hp => ?_))
    · simp only [hBdef, norm_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (c13t_aux_tcut_bounds _ _ _).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (c13t_aux_tcut_bounds _ _ _).2
    · have hgap : 0 < (p.2 - t₀) / 2 := by linarith [hp.2.1]
      have hev : ∀ᶠ n in atTop, B n p = G p := by
        filter_upwards [(tendsto_order.1 hlim0).2 _ hgap] with n hn
        simp only [hBdef]
        rw [c13t_aux_tcut_one (hpos n) (by linarith), one_mul]
      exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  have hz0 : Tendsto (fun n => (∫ p in S, A n p) + ∫ p in S, B n p) atTop (𝓝 0) := by
    simp_rw [hsplit]; exact tendsto_const_nhds
  have := tendsto_nhds_unique (hLA.add hLB) hz0
  linarith


theorem c13t_aux_ivtest.dt_zero {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) {X : c13_E} (hX : X ∉ K) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    deriv (fun s => ζ (X, s)) t = 0 := by
  have hd : DifferentiableAt ℝ (fun s => ζ (X, s)) t :=
    ((hz.contDiffAt (p := (X, t)) ht).differentiableAt (by simp)).comp t
      ((differentiableAt_const _).prodMk differentiableAt_id)
  rw [← hd.derivWithin (uniqueDiffOn_Icc hz.lt t ht)]
  rw [derivWithin_congr (f := fun _ => (0 : ℝ)) (fun s hs => hz.supp s hs X hX)
    (hz.supp t ht X hX)]
  simp

theorem c13t_aux_ivtest.dX_zero {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ} {K : Set c13_E} {δ : ℝ}
    (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) {X : c13_E} (hX : X ∉ K) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    fderiv ℝ (fun Y => ζ (Y, t)) X = 0 := by
  have hev : (fun Y => ζ (Y, t)) =ᶠ[𝓝 X] fun _ => 0 := by
    filter_upwards [hz.compact.isClosed.isOpen_compl.mem_nhds hX] with Y hY
    exact hz.supp t ht Y hY
  rw [hev.fderiv_eq]; simp

/-- Integrability of the transport integrand on `E × [t₀, t₁]` when `[t₀, t₁] ⊆ I`. -/
theorem c13t_aux_ivtest_integrable {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ}
    {K : Set c13_E} {δ : ℝ} (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) (hI : Icc t₀ t₁ ⊆ I) :
    IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)))
      (univ ×ˢ Icc t₀ t₁) := by
  obtain ⟨O, hO, hOS, hζO⟩ := hz.open_nhd
  set S : Set (c13_E × ℝ) := univ ×ˢ Icc t₀ t₁
  have hSm : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Icc
  have hSI : S ⊆ univ ×ˢ I := Set.prod_mono subset_rfl hI
  have hKI : IsCompact (K ×ˢ Icc t₀ t₁) := hz.compact.prod isCompact_Icc
  have hθm := c13t_aux_theta_aesm hF hSI hSm
  have hθb : ∀ p : c13_E × ℝ, |(c13_patch F p.2).indicator (1 : c13_E → ℝ) p.1| ≤ 1 := fun p => by
    simp only [indicator]; split_ifs <;> norm_num
  have hDc : ContinuousOn (fderiv ℝ ζ) O := hζO.continuousOn_fderiv_of_isOpen hO (by simp)
  have hdiff : ∀ p ∈ O, DifferentiableAt ℝ ζ p := fun p hp =>
    (hζO.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
  -- time derivative
  have hdt_eq : ∀ p ∈ O, deriv (fun s => ζ (p.1, s)) p.2 = fderiv ℝ ζ p (0, 1) := by
    intro p hp
    have h := (hdiff p hp).hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk
      (hasDerivAt_id p.2))
    simp only [Function.comp_def] at h
    exact h.deriv
  have hdX_eq : ∀ p ∈ O, fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 =
      (fderiv ℝ ζ p).comp ((ContinuousLinearMap.id ℝ c13_E).prod 0) := by
    intro p hp
    exact ((hdiff p hp).hasFDerivAt.comp p.1 ((hasFDerivAt_id p.1).prodMk
      (hasFDerivAt_const p.2 p.1))).fderiv
  have hdtc : ContinuousOn (fun p : c13_E × ℝ => deriv (fun s => ζ (p.1, s)) p.2) S :=
    ((hDc.clm_apply continuousOn_const).mono hOS).congr (fun p hp => hdt_eq p (hOS hp))
  have hdXc : ContinuousOn (fun p : c13_E × ℝ => fderiv ℝ (fun Y => ζ (Y, p.2)) p.1) S :=
    ((hDc.clm_comp continuousOn_const).mono hOS).congr (fun p hp => hdX_eq p (hOS hp))
  obtain ⟨D1, hD1⟩ := hKI.exists_bound_of_continuousOn (hdtc.mono (Set.prod_mono (subset_univ _)
    subset_rfl))
  obtain ⟨D2, hD2⟩ := hKI.exists_bound_of_continuousOn (hdXc.mono (Set.prod_mono (subset_univ _)
    subset_rfl))
  -- first piece
  have h1 : IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
      deriv (fun s => ζ (p.1, s)) p.2) S := by
    refine Integrable.mono' (g := (K ×ˢ Icc t₀ t₁).indicator (fun _ => max D1 0))
      ((integrable_indicator_iff hKI.measurableSet).2
        (integrableOn_const hKI.measure_lt_top.ne)).integrableOn
      (hθm.mul (hdtc.aestronglyMeasurable hSm))
      ((ae_restrict_iff' hSm).2 (ae_of_all _ fun p hp => ?_))
    rw [norm_mul]
    by_cases hK : p.1 ∈ K
    · rw [indicator_of_mem (show p ∈ K ×ˢ Icc t₀ t₁ from ⟨hK, hp.2⟩)]
      have := hD1 p ⟨hK, hp.2⟩
      rw [Real.norm_eq_abs] at this ⊢
      exact (mul_le_of_le_one_left (norm_nonneg _) (hθb p)).trans (this.trans (le_max_left _ _))
    · rw [hz.dt_zero hK hp.2, norm_zero, mul_zero]
      exact indicator_nonneg (fun _ _ => le_max_right _ _) _
  -- second piece
  obtain ⟨hUm, -, hUi, -⟩ := c13_velocity_local_integrable hα1 hα2 c I F hF
  have hUK := hUi K hz.compact (Icc t₀ t₁) hI isCompact_Icc
  have hUS : AEStronglyMeasurable (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2)
      ((volume : Measure (c13_E × ℝ)).restrict S) :=
    hUm.mono_measure (Measure.restrict_mono hSI le_rfl)
  have h2 : IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
      fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)) S := by
    refine Integrable.mono' (g := (K ×ˢ Icc t₀ t₁).indicator
        (fun p => max D2 0 * ‖c13_graph_velocity α c F p.1 p.2‖))
      ((integrable_indicator_iff hKI.measurableSet).2 (hUK.norm.const_mul _)).integrableOn
      (hθm.mul (Continuous.comp_aestronglyMeasurable₂
        (g := fun (A : c13_E →L[ℝ] ℝ) (w : c13_E) => A w) (by fun_prop)
        (hdXc.aestronglyMeasurable hSm) hUS))
      ((ae_restrict_iff' hSm).2 (ae_of_all _ fun p hp => ?_))
    rw [norm_mul]
    by_cases hK : p.1 ∈ K
    · rw [indicator_of_mem (show p ∈ K ×ˢ Icc t₀ t₁ from ⟨hK, hp.2⟩)]
      have := hD2 p ⟨hK, hp.2⟩
      refine (mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hθb p)).trans ?_
      refine ((fderiv ℝ (fun Y => ζ (Y, p.2)) p.1).le_opNorm _).trans ?_
      exact mul_le_mul_of_nonneg_right (this.trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hz.dX_zero hK hp.2, ContinuousLinearMap.zero_apply, norm_zero, mul_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)) _
  refine (h1.add h2).congr_fun (fun p _ => ?_) hSm
  simp only [Pi.add_apply, mul_add]


theorem c13t_aux_time_trace_interior {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F)
    (hw : c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X)
      (c13_graph_velocity α c F))
    (t₀ t₁ : ℝ) (hlt : t₀ < t₁) (hI : Icc t₀ t₁ ⊆ I) (ζ : c13_E × ℝ → ℝ)
    (O : Set (c13_E × ℝ)) (hO : IsOpen O) (hOS : univ ×ˢ Icc t₀ t₁ ⊆ O)
    (hζ : ContDiffOn ℝ (⊤ : ℕ∞) ζ O) (K : Set c13_E) (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc t₀ t₁, ∀ X ∉ K, ζ (X, t) = 0)
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (t₁ - δ) t₁, ∀ X, ζ (X, t) = 0) :
    IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)))
      (univ ×ˢ Icc t₀ t₁) ∧
    (∫ p in univ ×ˢ Icc t₀ t₁, (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2))) +
      (∫ X, (c13_patch F t₀).indicator 1 X * ζ (X, t₀)) = 0 := by
  obtain ⟨δ, hδ0, hvan⟩ := hδ
  have hz : c13t_aux_ivtest t₀ t₁ ζ K δ :=
    ⟨hlt, ⟨O, hO, hOS, hζ⟩, hK, fun t ht X hX => hsupp t ht X hX, hδ0, hvan⟩
  have hGi := c13t_aux_ivtest_integrable (c := c) hα1 hα2 hF hz hI
  refine ⟨hGi, ?_⟩
  have hGo := hGi.mono_set (Set.prod_mono subset_rfl Ioo_subset_Icc_self)
  have ht₀ : t₀ ∈ I := hI ⟨le_rfl, hlt.le⟩
  have hlim : Tendsto (fun t => ∫ X in K, |(c13_patch F t).indicator 1 X -
      (c13_patch F t₀).indicator (1 : c13_E → ℝ) X|) (𝓝[>] t₀) (𝓝 0) := by
    have h := c13t_aux_L1loc_cont hF K hK t₀ ht₀
    rw [nhdsWithin_eq_nhds.2 (hF.1.mem_nhds ht₀)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hcore := c13t_aux_initial_core hF hw hz (Ioo_subset_Icc_self.trans hI)
    (fun X => (c13_patch F t₀).indicator 1 X)
    (measurable_one.indicator (c13t_aux_patch_isOpen (c13t_aux_F_cont_slice hF ht₀)).measurableSet)
    (fun X => by simp only [indicator]; split_ifs <;> norm_num) hlim hGo
  rw [c13t_aux_fubini hGi, integral_Icc_eq_integral_Ioo, ← c13t_aux_fubini hGo]
  exact hcore

/-! ### Helpers for the boundary initial time -/

/-- Integrability of `U` on `Q × J` for a measurable finite-measure time set `J ⊆ I` (not
necessarily compact) carrying a common global slope bound. -/
theorem c13t_aux_U_slope_integrable {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {J : Set ℝ} (hJ : J ⊆ I) (hJm : MeasurableSet J)
    (hJf : volume J < ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x, ∀ t ∈ J, |deriv (fun x => F x t) x| ≤ M) {Q : Set c13_E} (hQ : IsCompact Q) :
    IntegrableOn (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2) (Q ×ˢ J) := by
  have hp1 : -1 < 1 - α := by linarith
  have hp0 : 1 - α ≤ 0 := by linarith
  obtain ⟨hA, -⟩ := c13_velocity_local_integrable hα1 hα2 c I F hF
  obtain ⟨Cb, hCb, hbd⟩ := c13_velocity_bound hα1 c M hM0
  have hpt : ∀ t ∈ J, ∀ X : c13_E,
      ‖c13_graph_velocity α c F X t‖ ≤ Cb * |X 1 - F (X 0) t| ^ (1 - α) := by
    intro t ht X
    by_cases hX : X 1 = F (X 0) t
    · simp only [c13_graph_velocity, hX, ↓reduceIte, norm_zero]; positivity
    · exact (hbd F t ((c13t_aux_slice_contDiff hF (hJ ht)).differentiable (by simp))
        (fun x => hM x t ht) X hX).2.2
  obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall 0
  obtain ⟨Cx, hCx, hbox⟩ := c13v_aux_box hp1 hp0 R
  refine ⟨hA.mono_measure (Measure.restrict_mono (prod_mono (subset_univ _) hJ) le_rfl), ?_⟩
  rw [HasFiniteIntegral, Measure.volume_eq_prod, ← Measure.prod_restrict,
    ← lintegral_prod_swap]
  refine lt_of_le_of_lt (lintegral_prod_le _) ?_
  have hin : ∀ t ∈ J, ∫⁻ X in Q, ‖c13_graph_velocity α c F X t‖ₑ ≤
      ENNReal.ofReal Cb * Cx := by
    intro t ht
    calc _ ≤ ∫⁻ X in Metric.closedBall (0 : c13_E) R, ‖c13_graph_velocity α c F X t‖ₑ :=
          lintegral_mono_set hR
      _ ≤ ∫⁻ X in Metric.closedBall (0 : c13_E) R,
            ENNReal.ofReal Cb * ENNReal.ofReal (|X 1 - F (X 0) t| ^ (1 - α)) := by
          refine lintegral_mono fun X => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_mul hCb.le]
          exact ENNReal.ofReal_le_ofReal (hpt t ht X)
      _ = ENNReal.ofReal Cb * ∫⁻ X in Metric.closedBall (0 : c13_E) R,
            ENNReal.ofReal (|X 1 - F (X 0) t| ^ (1 - α)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact hbox (fun x => F x t)
  calc _ ≤ ∫⁻ t in J, ENNReal.ofReal Cb * Cx := setLIntegral_mono' hJm hin
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCx) hJf

/-- Integrability of the transport integrand on `E × J` for a measurable `J ⊆ [t₀, t₁] ∩ I`,
given integrability of `U` on `K × J`. -/
theorem c13t_aux_ivtest_integrable_on {α c : ℝ} {I : Set ℝ}
    {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t₀ t₁ : ℝ} {ζ : c13_E × ℝ → ℝ}
    {K : Set c13_E} {δ : ℝ} (hz : c13t_aux_ivtest t₀ t₁ ζ K δ) {J : Set ℝ}
    (hJ : J ⊆ Icc t₀ t₁) (hJI : J ⊆ I) (hJm : MeasurableSet J)
    (hUK : IntegrableOn (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2) (K ×ˢ J)) :
    IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)))
      (univ ×ˢ J) := by
  obtain ⟨O, hO, hOS, hζO⟩ := hz.open_nhd
  set S' : Set (c13_E × ℝ) := univ ×ˢ Icc t₀ t₁
  set S : Set (c13_E × ℝ) := univ ×ˢ J
  have hSm : MeasurableSet S := MeasurableSet.univ.prod hJm
  have hSS : S ⊆ S' := Set.prod_mono subset_rfl hJ
  have hSI : S ⊆ univ ×ˢ I := Set.prod_mono subset_rfl hJI
  have hKI : IsCompact (K ×ˢ Icc t₀ t₁) := hz.compact.prod isCompact_Icc
  have hKJm : MeasurableSet (K ×ˢ J) := hz.compact.measurableSet.prod hJm
  have hθm := c13t_aux_theta_aesm hF hSI hSm
  have hθb : ∀ p : c13_E × ℝ, |(c13_patch F p.2).indicator (1 : c13_E → ℝ) p.1| ≤ 1 := fun p => by
    simp only [indicator]; split_ifs <;> norm_num
  have hDc : ContinuousOn (fderiv ℝ ζ) O := hζO.continuousOn_fderiv_of_isOpen hO (by simp)
  have hdiff : ∀ p ∈ O, DifferentiableAt ℝ ζ p := fun p hp =>
    (hζO.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
  have hdt_eq : ∀ p ∈ O, deriv (fun s => ζ (p.1, s)) p.2 = fderiv ℝ ζ p (0, 1) := by
    intro p hp
    have h := (hdiff p hp).hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk
      (hasDerivAt_id p.2))
    simp only [Function.comp_def] at h
    exact h.deriv
  have hdX_eq : ∀ p ∈ O, fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 =
      (fderiv ℝ ζ p).comp ((ContinuousLinearMap.id ℝ c13_E).prod 0) := by
    intro p hp
    exact ((hdiff p hp).hasFDerivAt.comp p.1 ((hasFDerivAt_id p.1).prodMk
      (hasFDerivAt_const p.2 p.1))).fderiv
  have hdtc : ContinuousOn (fun p : c13_E × ℝ => deriv (fun s => ζ (p.1, s)) p.2) S' :=
    ((hDc.clm_apply continuousOn_const).mono hOS).congr (fun p hp => hdt_eq p (hOS hp))
  have hdXc : ContinuousOn (fun p : c13_E × ℝ => fderiv ℝ (fun Y => ζ (Y, p.2)) p.1) S' :=
    ((hDc.clm_comp continuousOn_const).mono hOS).congr (fun p hp => hdX_eq p (hOS hp))
  obtain ⟨D1, hD1⟩ := hKI.exists_bound_of_continuousOn (hdtc.mono (Set.prod_mono (subset_univ _)
    subset_rfl))
  obtain ⟨D2, hD2⟩ := hKI.exists_bound_of_continuousOn (hdXc.mono (Set.prod_mono (subset_univ _)
    subset_rfl))
  have h1 : IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
      deriv (fun s => ζ (p.1, s)) p.2) S := by
    refine Integrable.mono' (g := (K ×ˢ Icc t₀ t₁).indicator (fun _ => max D1 0))
      ((integrable_indicator_iff hKI.measurableSet).2
        (integrableOn_const hKI.measure_lt_top.ne)).integrableOn
      (hθm.mul ((hdtc.mono hSS).aestronglyMeasurable hSm))
      ((ae_restrict_iff' hSm).2 (ae_of_all _ fun p hp => ?_))
    rw [norm_mul]
    have hp2 := hJ hp.2
    by_cases hK : p.1 ∈ K
    · rw [indicator_of_mem (show p ∈ K ×ˢ Icc t₀ t₁ from ⟨hK, hp2⟩)]
      have := hD1 p ⟨hK, hp2⟩
      rw [Real.norm_eq_abs] at this ⊢
      exact (mul_le_of_le_one_left (norm_nonneg _) (hθb p)).trans (this.trans (le_max_left _ _))
    · rw [hz.dt_zero hK hp2, norm_zero, mul_zero]
      exact indicator_nonneg (fun _ _ => le_max_right _ _) _
  have hUS : AEStronglyMeasurable (fun p : c13_E × ℝ => c13_graph_velocity α c F p.1 p.2)
      ((volume : Measure (c13_E × ℝ)).restrict S) := by
    obtain ⟨U', hU'm, hU'⟩ := c13v_aux_measurable α c hF
    refine hU'm.aestronglyMeasurable.congr ?_
    exact (ae_restrict_iff' hSm).2 (ae_of_all _ fun p hp => hU' p (hJI hp.2))
  have h2 : IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
      fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)) S := by
    refine Integrable.mono' (g := (K ×ˢ J).indicator
        (fun p => max D2 0 * ‖c13_graph_velocity α c F p.1 p.2‖))
      ((integrable_indicator_iff hKJm).2 (hUK.norm.const_mul _)).integrableOn
      (hθm.mul (Continuous.comp_aestronglyMeasurable₂
        (g := fun (A : c13_E →L[ℝ] ℝ) (w : c13_E) => A w) (by fun_prop)
        ((hdXc.mono hSS).aestronglyMeasurable hSm) hUS))
      ((ae_restrict_iff' hSm).2 (ae_of_all _ fun p hp => ?_))
    rw [norm_mul]
    have hp2 := hJ hp.2
    by_cases hK : p.1 ∈ K
    · rw [indicator_of_mem (show p ∈ K ×ˢ J from ⟨hK, hp.2⟩)]
      have := hD2 p ⟨hK, hp2⟩
      refine (mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact hθb p)).trans ?_
      refine ((fderiv ℝ (fun Y => ζ (Y, p.2)) p.1).le_opNorm _).trans ?_
      exact mul_le_mul_of_nonneg_right (this.trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hz.dX_zero hK hp2, ContinuousLinearMap.zero_apply, norm_zero, mul_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)) _
  refine (h1.add h2).congr_fun (fun p _ => ?_) hSm
  simp only [Pi.add_apply, mul_add]

/-- A locally uniform limit (as `t ↓ t₀`) of continuous graphs is continuous. -/
theorem c13t_aux_limit_continuous {F : ℝ → ℝ → ℝ} {I : Set ℝ} {t₀ t₁ : ℝ} (hlt : t₀ < t₁)
    (hI : Ioc t₀ t₁ ⊆ I) (hcont : ∀ t ∈ I, Continuous (fun x => F x t)) {F₀ : ℝ → ℝ}
    (hu : ∀ R : ℝ, TendstoUniformlyOn (fun t x => F x t) F₀ (𝓝[>] t₀) (Icc (-R) R)) :
    Continuous F₀ := by
  rw [continuous_iff_continuousAt]
  intro x
  have hev : ∀ᶠ t in 𝓝[>] t₀, ContinuousOn (fun x => F x t) (Icc (-(|x| + 1)) (|x| + 1)) := by
    filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
    exact (hcont t (hI (Ioo_subset_Ioc_self ht))).continuousOn
  have hc := (hu (|x| + 1)).continuousOn hev.frequently
  exact hc.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x]))

/-- `L¹_loc` convergence `θ_F(t) → 1_{y < F₀(x)}` as `t ↓ t₀` from the locally uniform graph
limit. -/
theorem c13t_aux_L1loc_limit {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) {t₀ t₁ : ℝ}
    (hlt : t₀ < t₁) (hI : Ioc t₀ t₁ ⊆ I) {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hu : ∀ R : ℝ, TendstoUniformlyOn (fun t x => F x t) F₀ (𝓝[>] t₀) (Icc (-R) R))
    (K : Set c13_E) (hK : IsCompact K) :
    Tendsto (fun t => ∫ X in K, |(c13_patch F t).indicator 1 X -
      {X : c13_E | X 1 < F₀ (X 0)}.indicator (1 : c13_E → ℝ) X|) (𝓝[>] t₀) (𝓝 0) := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKsq : K ⊆ {X : c13_E | |X 0| ≤ R ∧ |X 1| ≤ R} := by
    intro X hX
    have hX' : ‖X‖ ≤ R := le_trans (by simpa using hR₀ hX) (le_max_left _ _)
    have h0 : |X 0| ≤ ‖X‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 0
    have h1 : |X 1| ≤ ‖X‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 1
    exact ⟨h0.trans hX', h1.trans hX'⟩
  set g : ℝ → ℝ := fun t => ∫ x in (-R)..R, |F x t - F₀ x| with hgdef
  have hg0 : Tendsto g (𝓝[>] t₀) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε' : 0 < ε / (2 * R + 1) := by positivity
    filter_upwards [(Metric.tendstoUniformlyOn_iff.1 (hu R)) _ hε'] with t ht
    rw [Real.dist_eq, sub_zero]
    have hb : ‖∫ x in (-R)..R, |F x t - F₀ x|‖ ≤ ε / (2 * R + 1) * |R - -R| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
      have hx' : x ∈ Icc (-R) R := by
        rw [uIoc_of_le (by linarith)] at hx; exact Ioc_subset_Icc_self hx
      have := ht x hx'
      rw [Real.dist_eq, abs_sub_comm] at this
      rw [Real.norm_eq_abs, abs_abs]; exact this.le
    rw [Real.norm_eq_abs] at hb
    refine hb.trans_lt ?_
    rw [show |R - -R| = 2 * R by rw [abs_of_pos (by linarith)]; ring]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  refine squeeze_zero' ?_ ?_ hg0
  · exact Eventually.of_forall (fun s => integral_nonneg (fun X => abs_nonneg _))
  · filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
    have htI : t ∈ I := hI (Ioo_subset_Ioc_self ht)
    set G : ℝ → ℝ → ℝ := fun x τ => if τ = t₀ then F₀ x else F x τ with hG
    have hne : t ≠ t₀ := ne_of_gt ht.1
    have e1 : c13_patch G t = c13_patch F t := by ext X; simp [c13_patch, hG, hne]
    have e0 : c13_patch G t₀ = {X : c13_E | X 1 < F₀ (X 0)} := by ext X; simp [c13_patch, hG]
    have hc1 : Continuous (fun x => G x t) := by
      simpa [hG, hne] using c13t_aux_F_cont_slice hF htI
    have hc0 : Continuous (fun x => G x t₀) := by simpa [hG] using hF₀
    obtain ⟨hint, hle⟩ := c13t_aux_square_L1 (F := G) (s := t₀) (t := t) hR.le hc0 hc1
    rw [e1, e0] at hint hle
    have hgt : (∫ x in (-R)..R, |G x t - G x t₀|) = g t := by simp [hG, hne, hgdef]
    rw [hgt] at hle
    refine le_trans ?_ hle
    exact setIntegral_mono_set hint (Eventually.of_forall (fun X => abs_nonneg _))
      (Eventually.of_forall hKsq)

/-- Blueprint: lem:c13_patch_time_trace.
(1) For `R > 0`, `s, t ∈ I`: `∫_{[-R,R]²} |θ_F(t) - θ_F(s)| ≤ ∫_{-R}^{R} |F(x,t) - F(x,s)| dx`.
(2) `t ↦ θ_F(t)` is continuous into `L¹_loc(E)` on `I`.
(3) If `(θ_F, U)` solves the weak patch system on `E × I` and `[t₀, t₁] ⊆ I`, `t₀ < t₁`, then for every
`ζ` smooth on an open neighbourhood `O` of `E × [t₀, t₁]`, with a common compact spatial support
`K` there and vanishing for `t` near `t₁` (but possibly nonzero at `t₀`):
`∫_{t₀}^{t₁}∫_E θ_F(∂_tζ + U·∇ζ) + ∫_E θ_F(X,t₀) ζ(X,t₀) dX = 0`, absolutely convergent.
(4) Boundary initial time: if `t₀ ∉ I` but `(t₀, t₁] ⊆ I`, with an additional common global
slope bound on `(t₀, t₁]` and a locally uniform graph limit `F(·,t) → F₀` as `t ↓ t₀`, the same
identity holds with initial density `1_{y < F₀(x)}`. -/
theorem c13_patch_time_trace {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    (∀ R : ℝ, 0 < R → ∀ s ∈ I, ∀ t ∈ I,
      IntegrableOn (fun X : c13_E => |(c13_patch F t).indicator 1 X -
          (c13_patch F s).indicator (1 : c13_E → ℝ) X|) {X | |X 0| ≤ R ∧ |X 1| ≤ R} ∧
      (∫ X in {X : c13_E | |X 0| ≤ R ∧ |X 1| ≤ R},
          |(c13_patch F t).indicator 1 X - (c13_patch F s).indicator (1 : c13_E → ℝ) X|) ≤
        ∫ x in (-R)..R, |F x t - F x s|) ∧
    (∀ K : Set c13_E, IsCompact K → ∀ t ∈ I,
      Tendsto (fun s => ∫ X in K,
          |(c13_patch F s).indicator 1 X - (c13_patch F t).indicator (1 : c13_E → ℝ) X|)
        (𝓝[I] t) (𝓝 0)) ∧
    (c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X)
        (c13_graph_velocity α c F) →
      ∀ t₀ t₁ : ℝ, t₀ < t₁ → Icc t₀ t₁ ⊆ I →
      ∀ (ζ : c13_E × ℝ → ℝ) (O : Set (c13_E × ℝ)), IsOpen O → univ ×ˢ Icc t₀ t₁ ⊆ O →
        ContDiffOn ℝ (⊤ : ℕ∞) ζ O →
        ∀ K : Set c13_E, IsCompact K → (∀ t ∈ Icc t₀ t₁, ∀ X ∉ K, ζ (X, t) = 0) →
        (∃ δ > 0, ∀ t ∈ Icc (t₁ - δ) t₁, ∀ X, ζ (X, t) = 0) →
        IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
            (deriv (fun s => ζ (p.1, s)) p.2 +
              fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)))
          (univ ×ˢ Icc t₀ t₁) ∧
        (∫ p in univ ×ˢ Icc t₀ t₁, (c13_patch F p.2).indicator 1 p.1 *
            (deriv (fun s => ζ (p.1, s)) p.2 +
              fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2))) +
          (∫ X, (c13_patch F t₀).indicator 1 X * ζ (X, t₀)) = 0) ∧
    (c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X)
        (c13_graph_velocity α c F) →
      ∀ t₀ t₁ : ℝ, t₀ < t₁ → t₀ ∉ I → Ioc t₀ t₁ ⊆ I →
      ∀ M : ℝ, (∀ x, ∀ t ∈ Ioc t₀ t₁, |deriv (fun x => F x t) x| ≤ M) →
      ∀ F₀ : ℝ → ℝ, (∀ R : ℝ, TendstoUniformlyOn (fun t x => F x t) F₀ (𝓝[>] t₀) (Icc (-R) R)) →
      ∀ (ζ : c13_E × ℝ → ℝ) (O : Set (c13_E × ℝ)), IsOpen O → univ ×ˢ Icc t₀ t₁ ⊆ O →
        ContDiffOn ℝ (⊤ : ℕ∞) ζ O →
        ∀ K : Set c13_E, IsCompact K → (∀ t ∈ Icc t₀ t₁, ∀ X ∉ K, ζ (X, t) = 0) →
        (∃ δ > 0, ∀ t ∈ Icc (t₁ - δ) t₁, ∀ X, ζ (X, t) = 0) →
        IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
            (deriv (fun s => ζ (p.1, s)) p.2 +
              fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)))
          (univ ×ˢ Ioc t₀ t₁) ∧
        (∫ p in univ ×ˢ Ioc t₀ t₁, (c13_patch F p.2).indicator 1 p.1 *
            (deriv (fun s => ζ (p.1, s)) p.2 +
              fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2))) +
          (∫ X, {X : c13_E | X 1 < F₀ (X 0)}.indicator 1 X * ζ (X, t₀)) = 0) := by
  refine ⟨fun R hR s hs t ht => c13t_aux_square_L1 hR.le (c13t_aux_F_cont_slice hF hs)
      (c13t_aux_F_cont_slice hF ht),
    fun K hK t ht => c13t_aux_L1loc_cont hF K hK t ht,
    fun hw t₀ t₁ hlt hI ζ O hO hOS hζ K hK hsupp hδ =>
      c13t_aux_time_trace_interior hα1 hα2 hF hw t₀ t₁ hlt hI ζ O hO hOS hζ K hK hsupp hδ, ?_⟩
  intro hw t₀ t₁ hlt _ht₀ hI M hM F₀ hu ζ O hO hOS hζ K hK hsupp hδ
  obtain ⟨δ, hδ0, hvan⟩ := hδ
  have hz : c13t_aux_ivtest t₀ t₁ ζ K δ :=
    ⟨hlt, ⟨O, hO, hOS, hζ⟩, hK, fun t ht X hX => hsupp t ht X hX, hδ0, hvan⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 t₁ ⟨hlt, le_rfl⟩)
  have hUK := c13t_aux_U_slope_integrable (c := c) hα1 hα2 hF hI measurableSet_Ioc
    measure_Ioc_lt_top hM0 hM hK
  have hGi := c13t_aux_ivtest_integrable_on hF hz Ioc_subset_Icc_self hI measurableSet_Ioc hUK
  refine ⟨hGi, ?_⟩
  have hGo := hGi.mono_set (Set.prod_mono subset_rfl Ioo_subset_Ioc_self)
  have hF₀ := c13t_aux_limit_continuous hlt hI (fun t ht => c13t_aux_F_cont_slice hF ht) hu
  have hlim := c13t_aux_L1loc_limit hF hlt hI hF₀ hu K hK
  have hcore := c13t_aux_initial_core hF hw hz (Ioo_subset_Ioc_self.trans hI)
    (fun X => {X : c13_E | X 1 < F₀ (X 0)}.indicator 1 X)
    (measurable_one.indicator
      (isOpen_lt (by fun_prop) (hF₀.comp (by fun_prop))).measurableSet)
    (fun X => by simp only [indicator]; split_ifs <;> norm_num) hlim hGo
  rw [c13t_aux_fubini hGi, integral_Ioc_eq_integral_Ioo, ← c13t_aux_fubini hGo]
  exact hcore

/-! ### Helpers for the patch/front equivalence -/

theorem c13t_aux_norm_rpow (α x a s b : ℝ) :
    ‖c13_pt x a - c13_pt s b‖ ^ (-α) = (((x - s) ^ 2 + (a - b) ^ 2) ^ (α / 2))⁻¹ := by
  have hq : 0 ≤ (x - s) ^ 2 + (a - b) ^ 2 := by positivity
  have hn : ‖c13_pt x a - c13_pt s b‖ = Real.sqrt ((x - s) ^ 2 + (a - b) ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [c13_pt, Real.norm_eq_abs, sq_abs]
  rw [hn, Real.sqrt_eq_rpow, ← rpow_mul hq, ← rpow_neg hq]
  congr 1; ring

theorem c13t_aux_Ft_cont {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    ContinuousOn (fun q : ℝ × ℝ => deriv (fun s => F q.1 s) q.2) (univ ×ˢ I) := by
  have hO : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hF.1
  have hG := hF.2.2.1
  have hcont := (hG.continuousOn_fderiv_of_isOpen hO (by simp)).clm_apply
    (continuousOn_const (c := ((0 : ℝ), (1 : ℝ))))
  refine hcont.congr (fun q hq => ?_)
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => F q.1 q.2) q :=
    (hG.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp_hasDerivAt q.2 ((hasDerivAt_const q.2 q.1).prodMk
    (hasDerivAt_id q.2))
  simp only [Function.comp_def] at h
  exact h.deriv

theorem c13t_aux_trace_integrable {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F)
    {r : ℝ × ℝ → ℝ} (hr : ContinuousOn r (univ ×ˢ I)) {ζ : c13_E × ℝ → ℝ}
    (hζ : c13_scalar_test I ζ) :
    IntegrableOn (fun q : ℝ × ℝ => r q * ζ (c13_pt q.1 (F q.1 q.2), q.2)) (univ ×ˢ I) := by
  obtain ⟨hs, hc, hI⟩ := hζ
  obtain ⟨-, hJ, hJI, -⟩ := c13t_aux_test_tsupport hc hI
  obtain ⟨R, hR⟩ := (hc.image continuous_fst).isBounded.subset_closedBall 0
  set K' : Set (ℝ × ℝ) := Icc (-R) R ×ˢ (Prod.snd '' tsupport ζ)
  have hK' : IsCompact K' := isCompact_Icc.prod hJ
  have hK'sub : K' ⊆ univ ×ˢ I := Set.prod_mono (subset_univ _) hJI
  have hT : ContinuousOn (fun q : ℝ × ℝ => ζ (c13_pt q.1 (F q.1 q.2), q.2)) (univ ×ˢ I) := by
    refine hs.continuous.comp_continuousOn ?_
    refine ContinuousOn.prodMk ?_ continuous_snd.continuousOn
    exact c13t_aux_pt_continuous.comp_continuousOn
      (continuous_fst.continuousOn.prodMk (c13t_aux_F_contOn hF))
  have hint : IntegrableOn (fun q : ℝ × ℝ => r q * ζ (c13_pt q.1 (F q.1 q.2), q.2)) K' :=
    ((hr.mul hT).mono hK'sub).integrableOn_compact hK'
  refine (hint.integrable_of_forall_notMem_eq_zero (fun q hq => ?_)).integrableOn
  have : ζ (c13_pt q.1 (F q.1 q.2), q.2) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hq
    refine ⟨?_, ⟨_, hmem, rfl⟩⟩
    have h1 := hR ⟨_, hmem, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    exact abs_le.1 ((c13t_aux_abs_le_norm_pt q.1 _).trans h1)
  simp [this]

theorem c13t_aux_fubini2 {I : Set ℝ} {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f (univ ×ˢ I)) :
    (∫ q in univ ×ˢ I, f q) = ∫ t in I, ∫ x, f (x, t) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  exact integral_prod_symm f hf


theorem c13t_aux_transport_pairing {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) (ζ : c13_E × ℝ → ℝ)
    (hζ : c13_scalar_test I ζ) :
    IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2))) (univ ×ˢ I) ∧
    (∫ p in univ ×ˢ I, (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2))) =
      ∫ q in univ ×ˢ I, (c13_normal_speed α c F q.1 q.2 - deriv (fun s => F q.1 s) q.2) *
        ζ (c13_pt q.1 (F q.1 q.2), q.2) := by
  have hI : IsOpen I := hF.1
  have hO : MeasurableSet (univ ×ˢ I : Set (c13_E × ℝ)) := MeasurableSet.univ.prod hI.measurableSet
  obtain ⟨hm1, hm2, hm3⟩ := c13_moving_patch_pairing I F hF ζ hζ
  obtain ⟨hlaw, -, hdiv⟩ := c13_velocity_law_unique hα1 hα2 hc hF
  obtain ⟨hdi, -⟩ := hdiv _ hlaw ζ hζ
  have hθm := c13t_aux_theta_aesm hF subset_rfl hO
  have hθDU : IntegrableOn (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
      fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)) (univ ×ˢ I) :=
    Integrable.bdd_mul (c := 1) hdi hθm (ae_of_all _ fun p => by
      simp only [indicator, Real.norm_eq_abs]; split_ifs <;> norm_num)
  have hsum : (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2))) =
      fun p => (c13_patch F p.2).indicator 1 p.1 * deriv (fun s => ζ (p.1, s)) p.2 +
        (c13_patch F p.2).indicator 1 p.1 *
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2) := by
    funext p; ring
  rw [hsum]
  refine ⟨hm1.add hθDU, ?_⟩
  rw [integral_add hm1 hθDU, hm3]
  have hW := c13t_aux_trace_integrable hF
    (c13_normal_speed_integrable hα1 hα2 hc hF).2.1 hζ
  have hFt := c13t_aux_trace_integrable hF (c13t_aux_Ft_cont hF) hζ
  have hsub : (fun q : ℝ × ℝ => (c13_normal_speed α c F q.1 q.2 - deriv (fun s => F q.1 s) q.2) *
        ζ (c13_pt q.1 (F q.1 q.2), q.2)) = fun q =>
      c13_normal_speed α c F q.1 q.2 * ζ (c13_pt q.1 (F q.1 q.2), q.2) -
        deriv (fun s => F q.1 s) q.2 * ζ (c13_pt q.1 (F q.1 q.2), q.2) := by
    funext q; ring
  rw [hsub, integral_sub hW hFt]
  suffices h : (∫ p in univ ×ˢ I, (c13_patch F p.2).indicator 1 p.1 *
      fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2)) =
      ∫ q in univ ×ˢ I, c13_normal_speed α c F q.1 q.2 * ζ (c13_pt q.1 (F q.1 q.2), q.2) by
    rw [h]; ring
  rw [c13t_aux_fubini hθDU, c13t_aux_fubini2 hW]
  refine setIntegral_congr_fun hI.measurableSet (fun t ht => ?_)
  obtain ⟨hs1, hs2, -⟩ := c13t_aux_slice_test hζ.1 hζ.2.1 t
  obtain ⟨-, -, hflux⟩ := (c13_spatial_flux hα1 hα2 hc hF).1 t ht _ hs1 hs2
  simp only
  rw [← hflux, ← integral_indicator (c13t_aux_patch_isOpen
    (c13t_aux_F_cont_slice hF ht)).measurableSet]
  congr 1; funext Y
  simp only [indicator]; split_ifs <;> simp


theorem c13t_aux_weak_iff_U {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) (u : c13_E → ℝ → c13_E)
    (hu : c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X) u) :
    c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X) u ↔
      c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X)
        (c13_graph_velocity α c F) := by
  obtain ⟨hlaw, huniq, -⟩ := c13_velocity_law_unique hα1 hα2 hc hF
  have hae := huniq u hu
  have key : ∀ ζ : c13_E × ℝ → ℝ,
      (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 + fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2))) =ᵐ[
        (volume : Measure (c13_E × ℝ)).restrict (univ ×ˢ I)]
      (fun p : c13_E × ℝ => (c13_patch F p.2).indicator 1 p.1 *
        (deriv (fun s => ζ (p.1, s)) p.2 +
          fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (c13_graph_velocity α c F p.1 p.2))) := by
    intro ζ
    filter_upwards [hae] with p hp
    rw [hp]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hlaw, fun ζ hζ => ?_⟩
    obtain ⟨h1, h2⟩ := h ζ hζ
    exact ⟨h1.congr (key ζ), (integral_congr_ae (key ζ)).symm.trans h2⟩
  · rintro ⟨-, h⟩
    refine ⟨hu, fun ζ hζ => ?_⟩
    obtain ⟨h1, h2⟩ := h ζ hζ
    exact ⟨h1.congr (key ζ).symm, (integral_congr_ae (key ζ)).trans h2⟩

/-- Blueprint: thm:c13_patch_front_equivalence.  For admissible `F`: every front integral
converges absolutely; `(θ_F, U[F])` solves the coefficient-`c` weak patch system on `E × I` iff
`F_t(x,t) = c ∫ (F_x(x,t) - F_x(s,t)) / ((x-s)² + (F(x,t) - F(s,t))²)^{α/2} ds` for all
`x ∈ ℝ`, `t ∈ I`; and the same equivalence holds for any velocity `u` satisfying the velocity law
for `θ_F` (such `u` agree with `U[F]` a.e.). -/
theorem c13_patch_front_equivalence {α c : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hc : 0 < c)
    {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    (∀ x : ℝ, ∀ t ∈ I, Integrable (fun s : ℝ =>
        (deriv (fun x => F x t) x - deriv (fun x => F x t) s) /
          ((x - s) ^ 2 + (F x t - F s t) ^ 2) ^ (α / 2))) ∧
    (c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X)
        (c13_graph_velocity α c F) ↔
      ∀ x : ℝ, ∀ t ∈ I, deriv (fun s => F x s) t =
        c * ∫ s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) /
          ((x - s) ^ 2 + (F x t - F s t) ^ 2) ^ (α / 2)) ∧
    (∀ u : c13_E → ℝ → c13_E,
      c13_velocity_law α c I (fun X t => (c13_patch F t).indicator 1 X) u →
      (c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X) u ↔
        ∀ x : ℝ, ∀ t ∈ I, deriv (fun s => F x s) t =
          c * ∫ s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) /
            ((x - s) ^ 2 + (F x t - F s t) ^ 2) ^ (α / 2))) := by
  obtain ⟨hWi, hWc, -⟩ := c13_normal_speed_integrable hα1 hα2 hc hF
  have hfrac : ∀ x t s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) /
      ((x - s) ^ 2 + (F x t - F s t) ^ 2) ^ (α / 2) =
      (deriv (fun x => F x t) x - deriv (fun x => F x t) s) *
        ‖c13_pt x (F x t) - c13_pt s (F s t)‖ ^ (-α) := by
    intro x t s; rw [c13t_aux_norm_rpow, div_eq_mul_inv]
  have hWeq : ∀ x t : ℝ, c13_normal_speed α c F x t =
      c * ∫ s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) /
        ((x - s) ^ 2 + (F x t - F s t) ^ 2) ^ (α / 2) := by
    intro x t; unfold c13_normal_speed; simp_rw [hfrac]
  obtain ⟨hlaw, -, -⟩ := c13_velocity_law_unique hα1 hα2 hc hF
  have hmain : c13_weak_patch_system α c I (fun X t => (c13_patch F t).indicator 1 X)
        (c13_graph_velocity α c F) ↔
      ∀ x : ℝ, ∀ t ∈ I, deriv (fun s => F x s) t =
        c * ∫ s : ℝ, (deriv (fun x => F x t) x - deriv (fun x => F x t) s) /
          ((x - s) ^ 2 + (F x t - F s t) ^ 2) ^ (α / 2) := by
    simp_rw [← hWeq]
    constructor
    · intro hw x t ht
      have h0 := (c13_trace_tests I F hF).2
        (fun q => c13_normal_speed α c F q.1 q.2 - deriv (fun s => F q.1 s) q.2)
        (hWc.sub (c13t_aux_Ft_cont hF))
        (fun ζ hζ => by
          rw [← (c13t_aux_transport_pairing hα1 hα2 hc hF ζ hζ).2]
          exact (hw.2 ζ hζ).2) x t ht
      simp only at h0
      linarith
    · intro h
      refine ⟨hlaw, fun ζ hζ => ⟨(c13t_aux_transport_pairing hα1 hα2 hc hF ζ hζ).1, ?_⟩⟩
      rw [(c13t_aux_transport_pairing hα1 hα2 hc hF ζ hζ).2]
      rw [setIntegral_congr_fun ((isOpen_univ.prod hF.1).measurableSet) (g := fun _ => (0 : ℝ))
        (fun q hq => by simp only; rw [h q.1 q.2 hq.2, sub_self, zero_mul])]
      simp
  refine ⟨fun x t ht => (hWi x t ht).congr (ae_of_all _ fun s => (hfrac x t s).symm), hmain,
    fun u hu => (c13t_aux_weak_iff_U hα1 hα2 hc hF u hu).trans hmain⟩

end GSQG
