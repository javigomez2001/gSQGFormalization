import GSQG.PatchEquation.Setup

/-!
# Beyond the paper (2D patch derivation): graph geometry, finite and compact graph flux (FTC) (blueprint ch. 13)

Helpers are named `c13g_aux_*`.

Conventions: the divergence of a vector field `Q : c13_E → c13_E` is `c13g_aux_div Q`, the trace
of its Fréchet derivative in the coordinate basis `c13_pt 1 0`, `c13_pt 0 1`.  The coordinate
bridge between `c13_E` and `ℝ × ℝ` is `c13g_aux_equiv` (`(x, y) ↦ c13_pt x y`), which is
measure preserving (`c13g_aux_mp`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ### Coordinate and measure bridge between `c13_E` and `ℝ × ℝ` -/

/-- The coordinate map `(x, y) ↦ c13_pt x y` as a measurable equivalence `ℝ × ℝ ≃ᵐ c13_E`. -/
def c13g_aux_equiv : ℝ × ℝ ≃ᵐ c13_E :=
  (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

theorem c13g_aux_equiv_apply (p : ℝ × ℝ) : c13g_aux_equiv p = c13_pt p.1 p.2 := by
  ext i; fin_cases i <;> rfl

/-- `c13g_aux_equiv` is volume preserving (Euclidean volume on `c13_E`, product Lebesgue on `ℝ × ℝ`). -/
theorem c13g_aux_mp : MeasurePreserving c13g_aux_equiv :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

@[simp] theorem c13g_aux_pt_zero (x y : ℝ) : c13_pt x y 0 = x := rfl
@[simp] theorem c13g_aux_pt_one (x y : ℝ) : c13_pt x y 1 = y := rfl

theorem c13g_aux_pt_eta (X : c13_E) : c13_pt (X 0) (X 1) = X := by
  ext i; fin_cases i <;> rfl

theorem c13g_aux_norm_sq (X : c13_E) : ‖X‖ ^ 2 = X 0 ^ 2 + X 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]; simp [sq_abs]

theorem c13g_aux_norm_pt_sq (x y : ℝ) : ‖c13_pt x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [c13g_aux_norm_sq]; rfl

theorem c13g_aux_pt_sub (a b c d : ℝ) : c13_pt a b - c13_pt c d = c13_pt (a - c) (b - d) := by
  ext i; fin_cases i <;> rfl

theorem c13g_aux_pt_add (a b c d : ℝ) : c13_pt a b + c13_pt c d = c13_pt (a + c) (b + d) := by
  ext i; fin_cases i <;> rfl

theorem c13g_aux_pt_smul (r a b : ℝ) : r • c13_pt a b = c13_pt (r * a) (r * b) := by
  ext i; fin_cases i <;> rfl

theorem c13g_aux_continuous_pt : Continuous (fun p : ℝ × ℝ => c13_pt p.1 p.2) := by
  have : (fun p : ℝ × ℝ => c13_pt p.1 p.2) = c13g_aux_equiv := by
    funext p; rw [c13g_aux_equiv_apply]
  rw [this]
  exact (PiLp.continuous_toLp 2 _).comp (Homeomorph.finTwoArrow (X := ℝ)).symm.continuous

/-- Set integrals over `c13_E` as set integrals over `ℝ × ℝ`. -/
theorem c13g_aux_setIntegral (f : c13_E → ℝ) (S : Set c13_E) :
    ∫ X in S, f X = ∫ p in {p : ℝ × ℝ | c13_pt p.1 p.2 ∈ S}, f (c13_pt p.1 p.2) := by
  have h := c13g_aux_mp.setIntegral_preimage_emb c13g_aux_equiv.measurableEmbedding f S
  simp only [c13g_aux_equiv_apply] at h
  rw [← h]; rfl

theorem c13g_aux_integrableOn_iff (f : c13_E → ℝ) (S : Set c13_E) :
    IntegrableOn f S ↔ IntegrableOn (fun p : ℝ × ℝ => f (c13_pt p.1 p.2))
      {p : ℝ × ℝ | c13_pt p.1 p.2 ∈ S} := by
  have h := c13g_aux_mp.integrableOn_comp_preimage c13g_aux_equiv.measurableEmbedding (f := f) (s := S)
  rw [← h]; simp only [Function.comp_def, c13g_aux_equiv_apply]; rfl

theorem c13g_aux_volume (S : Set c13_E) :
    volume S = volume {p : ℝ × ℝ | c13_pt p.1 p.2 ∈ S} := by
  have h := c13g_aux_mp.measure_preimage_equiv S
  rw [← h]; congr 1

/-! ### Graph slices and slope bounds -/

theorem c13g_aux_slice_contDiff {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F)
    {t : ℝ} (ht : t ∈ I) : ContDiff ℝ (⊤ : ℕ∞) (fun x => F x t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) (x, t) :=
    hF.2.2.1.contDiffAt ((isOpen_univ.prod hF.1).mem_nhds ⟨mem_univ _, ht⟩)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => (x, t)) x :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  exact h1.comp x h2

theorem c13g_aux_continuousOn {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    ContinuousOn (fun p : c13_E × ℝ => F (p.1 0) p.2) {p | p.2 ∈ I} := by
  have h := hF.2.2.1.continuousOn
  have hc : Continuous (fun p : c13_E × ℝ => ((p.1 0, p.2) : ℝ × ℝ)) :=
    ((PiLp.continuous_apply 2 _ 0).comp continuous_fst).prodMk continuous_snd
  refine h.comp hc.continuousOn ?_
  intro p hp; exact ⟨mem_univ _, hp⟩

theorem c13g_aux_slope_lip {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ}
    (hM : ∀ x, |deriv f x| ≤ M) (x s : ℝ) : |f s - f x| ≤ M * |s - x| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun z _ => hf z)
    (fun z _ => by simpa [Real.norm_eq_abs] using hM z) convex_univ (mem_univ x) (mem_univ s)
  simpa [Real.norm_eq_abs] using this

theorem c13g_aux_dist_bound {f : ℝ → ℝ} (hf : Differentiable ℝ f) {M : ℝ}
    (hM : ∀ x, |deriv f x| ≤ M) (x s y : ℝ) :
    (s - x) ^ 2 + (y - f x) ^ 2 ≤ 2 * (1 + M ^ 2) * ((s - x) ^ 2 + (y - f s) ^ 2) := by
  have hL := c13g_aux_slope_lip hf hM x s
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hsq : (f s - f x) ^ 2 ≤ M ^ 2 * (s - x) ^ 2 := by
    have h0 : 0 ≤ |f s - f x| := abs_nonneg _
    have := mul_le_mul hL hL h0 (by positivity)
    rw [← sq_abs (f s - f x), ← sq_abs (s - x)]; nlinarith [this]
  nlinarith [sq_nonneg ((y - f s) - (f s - f x)), sq_nonneg (s - x), sq_nonneg (y - f s),
    mul_nonneg (sq_nonneg M) (sq_nonneg (y - f s))]

theorem c13g_aux_graph_null_prod (f : ℝ → ℝ) (hf : Continuous f) :
    volume {p : ℝ × ℝ | p.2 = f p.1} = 0 := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 = f p.1} :=
    (isClosed_eq continuous_snd (hf.comp continuous_fst)).measurableSet
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hS]
  refine Filter.Eventually.of_forall (fun x => ?_)
  have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 = f p.1} = {f x} := by ext y; simp
  simp [this]

theorem c13g_aux_graph_null (f : ℝ → ℝ) (hf : Continuous f) :
    volume {X : c13_E | X 1 = f (X 0)} = 0 := by
  rw [c13g_aux_volume]; exact c13g_aux_graph_null_prod f hf

/-! ### Chain rule along coordinate curves and continuity of derivatives -/

theorem c13g_aux_pt_basis (u v : ℝ) : c13_pt u v = u • c13_pt 1 0 + v • c13_pt 0 1 := by
  ext i; fin_cases i <;> simp [c13_pt]

theorem c13g_aux_pt_hasDerivAt {a b : ℝ → ℝ} {a' b' x : ℝ} (ha : HasDerivAt a a' x)
    (hb : HasDerivAt b b' x) : HasDerivAt (fun x => c13_pt (a x) (b x)) (c13_pt a' b') x := by
  have h := (ha.smul_const (c13_pt 1 0)).add (hb.smul_const (c13_pt 0 1))
  rw [← c13g_aux_pt_basis] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall (fun y => c13g_aux_pt_basis _ _))

theorem c13g_aux_comp_hasDerivAt {Q : c13_E → c13_E} {a b : ℝ → ℝ} {a' b' x : ℝ}
    (hQ : DifferentiableAt ℝ Q (c13_pt (a x) (b x))) (ha : HasDerivAt a a' x)
    (hb : HasDerivAt b b' x) (i : Fin 2) :
    HasDerivAt (fun x => Q (c13_pt (a x) (b x)) i)
      (fderiv ℝ Q (c13_pt (a x) (b x)) (c13_pt a' b') i) x := by
  have h := hQ.hasFDerivAt.comp_hasDerivAt x (c13g_aux_pt_hasDerivAt ha hb)
  exact (EuclideanSpace.proj i : c13_E →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt x h

theorem c13g_aux_fderiv_pt (L : c13_E →L[ℝ] c13_E) (u v : ℝ) (i : Fin 2) :
    L (c13_pt u v) i = u * L (c13_pt 1 0) i + v * L (c13_pt 0 1) i := by
  conv_lhs => rw [c13g_aux_pt_basis]
  simp

theorem c13g_aux_cov (g : ℝ → ℝ) (b H : ℝ) :
    ∫ τ in (0 : ℝ)..1, g ((b + H) * τ + -H) * (b + H) = ∫ y in (-H)..b, g y := by
  rw [intervalIntegral.integral_mul_const, mul_comm, ← smul_eq_mul,
    intervalIntegral.smul_integral_comp_mul_add]
  congr 1 <;> ring

theorem c13g_aux_cont_fderiv {α : Type*} [TopologicalSpace α] {Q : c13_E → c13_E}
    {U : Set c13_E} (hD : ContinuousOn (fderiv ℝ Q) U) {Ψ : α → c13_E} {S : Set α}
    (hΨ : ContinuousOn Ψ S) (hm : MapsTo Ψ S U) (v : c13_E) (i : Fin 2) :
    ContinuousOn (fun a => fderiv ℝ Q (Ψ a) v i) S := by
  have h1 : Continuous (fun L : c13_E →L[ℝ] c13_E => L v i) :=
    (PiLp.continuous_apply 2 _ i).comp (continuous_id.clm_apply continuous_const)
  exact h1.comp_continuousOn (hD.comp hΨ hm)

theorem c13g_aux_cont_val {α : Type*} [TopologicalSpace α] {Q : c13_E → c13_E}
    {U : Set c13_E} (hC : ContinuousOn Q U) {Ψ : α → c13_E} {S : Set α}
    (hΨ : ContinuousOn Ψ S) (hm : MapsTo Ψ S U) (i : Fin 2) :
    ContinuousOn (fun a => Q (Ψ a) i) S :=
  (PiLp.continuous_apply 2 _ i).comp_continuousOn (hC.comp hΨ hm)

theorem c13g_aux_cont_fderiv' {α : Type*} [TopologicalSpace α] {Q : c13_E → c13_E}
    {U : Set c13_E} (hD : ContinuousOn (fderiv ℝ Q) U) {Ψ V : α → c13_E} {S : Set α}
    (hΨ : ContinuousOn Ψ S) (hm : MapsTo Ψ S U) (hV : ContinuousOn V S) (i : Fin 2) :
    ContinuousOn (fun a => fderiv ℝ Q (Ψ a) (V a) i) S :=
  (PiLp.continuous_apply 2 _ i).comp_continuousOn ((hD.comp hΨ hm).clm_apply hV)

/-! ### One-dimensional FTC and Fubini tools -/

/-- Iterated integral over a rectangle of an `x`-derivative (Fubini + FTC in `x`). -/
theorem c13g_aux_rect_ftc {f f' : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hder : ∀ x ∈ Icc a b, ∀ τ ∈ Icc c d, HasDerivAt (fun x => f x τ) (f' x τ) x)
    (hcont : ContinuousOn (Function.uncurry f') (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ τ in c..d, f' x τ = ∫ τ in c..d, (f b τ - f a τ) := by
  have hint : IntegrableOn (Function.uncurry f') (uIoc a b ×ˢ uIoc c d) := by
    refine (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
    rw [uIoc_of_le hab, uIoc_of_le hcd]
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  rw [intervalIntegral_intervalIntegral_swap (E := ℝ) (F := f') hint]
  refine intervalIntegral.integral_congr (fun τ hτ => ?_)
  show ∫ x in a..b, f' x τ = f b τ - f a τ
  rw [uIcc_of_le hcd] at hτ
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => f x τ) (f' := fun x => f' x τ) (fun x hx => ?_) ?_
  · rw [uIcc_of_le hab] at hx; exact hder x hx τ hτ
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact hcont.comp (f := fun x : ℝ => (x, τ)) (Continuous.continuousOn (by fun_prop)) (fun x hx => ⟨hx, hτ⟩)

/-- A parametric interval integral of a function continuous on a rectangle is continuous on the
parameter interval, hence interval integrable. -/
theorem c13g_aux_param_continuousOn {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hcont : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) :
    ContinuousOn (fun x => ∫ τ in c..d, f x τ) (Icc a b) := by
  have hmaps : ∀ p : ℝ × ℝ, ((projIcc a b hab p.1 : ℝ), (projIcc c d hcd p.2 : ℝ)) ∈
      Icc a b ×ˢ Icc c d := fun p => ⟨(projIcc a b hab p.1).2, (projIcc c d hcd p.2).2⟩
  have hg : Continuous (fun p : ℝ × ℝ => f (projIcc a b hab p.1) (projIcc c d hcd p.2)) := by
    have hc : Continuous (fun p : ℝ × ℝ => ((projIcc a b hab p.1 : ℝ), (projIcc c d hcd p.2 : ℝ))) :=
      ((continuous_subtype_val.comp continuous_projIcc).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_projIcc).comp continuous_snd)
    exact hcont.comp_continuous hc hmaps
  have hG : Continuous (fun x => ∫ τ in c..d, f (projIcc a b hab x) (projIcc c d hcd τ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x τ => f (projIcc a b hab x) (projIcc c d hcd τ)) hg c d
  refine hG.continuousOn.congr (fun x hx => ?_)
  refine intervalIntegral.integral_congr (fun τ hτ => ?_)
  rw [uIcc_of_le hcd] at hτ
  simp only [projIcc_of_mem hab hx, projIcc_of_mem hcd hτ]

theorem c13g_aux_param_intervalIntegrable {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hcont : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) :
    IntervalIntegrable (fun x => ∫ τ in c..d, f x τ) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]; exact c13g_aux_param_continuousOn hab hcd hcont

/-- Fubini on a subgraph domain `{|x| < R, -H < y < F x}` of `ℝ × ℝ`. -/
theorem c13g_aux_subgraph_fubini {R H : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : Continuous F)
    (hFH : ∀ s ∈ Icc (-R) R, -H ≤ F s) {g : ℝ × ℝ → ℝ}
    (hg : IntegrableOn g {p : ℝ × ℝ | |p.1| < R ∧ -H < p.2 ∧ p.2 < F p.1}) :
    ∫ p in {p : ℝ × ℝ | |p.1| < R ∧ -H < p.2 ∧ p.2 < F p.1}, g p =
      ∫ x in (-R)..R, ∫ y in (-H)..(F x), g (x, y) := by
  set D := {p : ℝ × ℝ | |p.1| < R ∧ -H < p.2 ∧ p.2 < F p.1}
  have hDm : MeasurableSet D := by
    have : IsOpen D := by
      refine (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd (hF.comp continuous_fst)))
    exact this.measurableSet
  rw [← integral_indicator hDm, Measure.volume_eq_prod,
    integral_prod _ ((integrable_indicator_iff hDm).mpr hg),
    intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
    ← integral_indicator measurableSet_Ioo]
  congr 1; funext x
  by_cases hx : x ∈ Ioo (-R) R
  · rw [indicator_of_mem hx, intervalIntegral.integral_of_le (hFH x (Ioo_subset_Icc_self hx)),
      integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
    congr 1; funext y
    have hxa : |x| < R := abs_lt.mpr hx
    by_cases hy : y ∈ Ioo (-H) (F x)
    · rw [indicator_of_mem hy, indicator_of_mem (s := D) (show (x, y) ∈ D from ⟨hxa, hy⟩)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (s := D) (fun h => hy ⟨h.2.1, h.2.2⟩)]
  · rw [indicator_of_notMem hx]
    refine (integral_eq_zero_of_ae (Eventually.of_forall (fun y => ?_)))
    exact indicator_of_notMem (s := D) (fun h => hx (abs_lt.mp h.1)) _

/-- The divergence `div Q = ∂₁Q₁ + ∂₂Q₂` of a vector field on the Euclidean plane, written with
the Fréchet derivative (meaningful where `Q` is differentiable). -/
def c13g_aux_div (Q : c13_E → c13_E) (X : c13_E) : ℝ :=
  fderiv ℝ Q X (c13_pt 1 0) 0 + fderiv ℝ Q X (c13_pt 0 1) 1

/-- Blueprint: lem:c13_graph_geometry.  Patches are open (hence measurable), each graph is
Lebesgue-null in the plane, the spacetime patch over `I` is measurable and the spacetime graph
over `I` is null in `E × ℝ`; and the distance bound
`h² + δ² ≤ 2(1+M²)(h² + (y - F(s,t))²)`, `h = s - x`, `δ = y - F(x,t)`, for a fixed-time slope
bound `M`, and uniformly on compact time intervals with a common slope bound. -/
theorem c13_graph_geometry {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hF : c13_graph_class I F) :
    (∀ t ∈ I, IsOpen (c13_patch F t) ∧ MeasurableSet (c13_patch F t)) ∧
    (∀ t ∈ I, volume {X : c13_E | X 1 = F (X 0) t} = 0) ∧
    MeasurableSet {p : c13_E × ℝ | p.2 ∈ I ∧ p.1 ∈ c13_patch F p.2} ∧
    volume {p : c13_E × ℝ | p.2 ∈ I ∧ p.1 1 = F (p.1 0) p.2} = 0 ∧
    (∀ t ∈ I, ∀ M : ℝ, (∀ x, |deriv (fun x => F x t) x| ≤ M) →
      ∀ x s y : ℝ, (s - x) ^ 2 + (y - F x t) ^ 2 ≤
        2 * (1 + M ^ 2) * ((s - x) ^ 2 + (y - F s t) ^ 2)) ∧
    (∀ J₀ ⊆ I, IsCompact J₀ → ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ J₀, ∀ x s y : ℝ,
      (s - x) ^ 2 + (y - F x t) ^ 2 ≤ 2 * (1 + M ^ 2) * ((s - x) ^ 2 + (y - F s t) ^ 2)) := by
  have hc0 : Continuous (fun X : c13_E => X 0) := PiLp.continuous_apply 2 _ 0
  have hc1 : Continuous (fun X : c13_E => X 1) := PiLp.continuous_apply 2 _ 1
  have hslice : ∀ t ∈ I, Continuous (fun x => F x t) := fun t ht =>
    (c13g_aux_slice_contDiff hF ht).continuous
  have hdiff : ∀ t ∈ I, Differentiable ℝ (fun x => F x t) := fun t ht =>
    (c13g_aux_slice_contDiff hF ht).differentiable (by simp)
  have hsI : IsOpen {p : c13_E × ℝ | p.2 ∈ I} := hF.1.preimage continuous_snd
  have hG := c13g_aux_continuousOn hF
  have hpair : ContinuousOn (fun p : c13_E × ℝ => ((p.1 1, F (p.1 0) p.2) : ℝ × ℝ))
      {p | p.2 ∈ I} := ((hc1.comp continuous_fst).continuousOn).prodMk hG
  have hdist : ∀ t ∈ I, ∀ M : ℝ, (∀ x, |deriv (fun x => F x t) x| ≤ M) →
      ∀ x s y : ℝ, (s - x) ^ 2 + (y - F x t) ^ 2 ≤
        2 * (1 + M ^ 2) * ((s - x) ^ 2 + (y - F s t) ^ 2) :=
    fun t ht M hM x s y => c13g_aux_dist_bound (hdiff t ht) hM x s y
  have hnull : ∀ t ∈ I, volume {X : c13_E | X 1 = F (X 0) t} = 0 := fun t ht =>
    c13g_aux_graph_null (fun x => F x t) (hslice t ht)
  refine ⟨fun t ht => ?_, hnull, ?_, ?_, hdist, ?_⟩
  · have : IsOpen (c13_patch F t) := isOpen_lt hc1 ((hslice t ht).comp hc0)
    exact ⟨this, this.measurableSet⟩
  · have h := hpair.isOpen_inter_preimage hsI (isOpen_lt continuous_fst continuous_snd)
    convert h.measurableSet using 1
    ext p; simp only [c13_patch, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  · have hopen := hpair.isOpen_inter_preimage hsI (isOpen_ne_fun continuous_fst continuous_snd)
    have hmeas : MeasurableSet {p : c13_E × ℝ | p.2 ∈ I ∧ p.1 1 = F (p.1 0) p.2} := by
      have : {p : c13_E × ℝ | p.2 ∈ I ∧ p.1 1 = F (p.1 0) p.2} =
          {p : c13_E × ℝ | p.2 ∈ I} \ ({p : c13_E × ℝ | p.2 ∈ I} ∩
            (fun p : c13_E × ℝ => ((p.1 1, F (p.1 0) p.2) : ℝ × ℝ)) ⁻¹' {q | q.1 ≠ q.2}) := by
        ext p; simp only [Set.mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff, mem_preimage]; constructor <;> intro h <;> simp_all
      rw [this]; exact hsI.measurableSet.diff hopen.measurableSet
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
    refine (lintegral_congr (fun y => ?_)).trans lintegral_zero
    by_cases hy : y ∈ I
    · convert hnull y hy using 2
      ext X; simp only [mem_preimage, mem_ofPred_eq]; tauto
    · convert measure_empty (μ := (volume : Measure c13_E)) using 2
      ext X; simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]; tauto
  · intro J₀ hJ hJc
    obtain ⟨M, hM0, hM⟩ := hF.2.2.2 J₀ hJ hJc
    exact ⟨M, hM0, fun t ht x s y => hdist t (hJ ht) M (fun x => hM x t ht) x s y⟩

/-- Blueprint: lem:c13_finite_graph_flux.  Divergence theorem on the finite graph domain
`D = {(s, y) : |s| < R, -H < y < F(s)}` for `Q` of class `C¹` on a neighbourhood of `D̄`,
with the top (graph), bottom and two wall terms; all integrals absolutely convergent. -/
theorem c13_finite_graph_flux {R H : ℝ} (hR : 0 < R) (hH : 0 < H) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hFH : ∀ s ∈ Icc (-R) R, -H < F s) {Q : c13_E → c13_E}
    (hQ : ∃ U : Set c13_E, IsOpen U ∧
      {X : c13_E | |X 0| ≤ R ∧ -H ≤ X 1 ∧ X 1 ≤ F (X 0)} ⊆ U ∧ ContDiffOn ℝ 1 Q U) :
    IntegrableOn (c13g_aux_div Q) {X : c13_E | |X 0| < R ∧ -H < X 1 ∧ X 1 < F (X 0)} ∧
    IntervalIntegrable (fun s => Q (c13_pt s (F s)) 1 - deriv F s * Q (c13_pt s (F s)) 0)
      volume (-R) R ∧
    IntervalIntegrable (fun s => Q (c13_pt s (-H)) 1) volume (-R) R ∧
    IntervalIntegrable (fun y => Q (c13_pt R y) 0) volume (-H) (F R) ∧
    IntervalIntegrable (fun y => Q (c13_pt (-R) y) 0) volume (-H) (F (-R)) ∧
    ∫ X in {X : c13_E | |X 0| < R ∧ -H < X 1 ∧ X 1 < F (X 0)}, c13g_aux_div Q X =
      (∫ s in (-R)..R, (Q (c13_pt s (F s)) 1 - deriv F s * Q (c13_pt s (F s)) 0)) -
      (∫ s in (-R)..R, Q (c13_pt s (-H)) 1) +
      (∫ y in (-H)..(F R), Q (c13_pt R y) 0) - (∫ y in (-H)..(F (-R)), Q (c13_pt (-R) y) 0) := by
  obtain ⟨U, hUo, hKU, hQU⟩ := hQ
  have hUpt : ∀ x y, |x| ≤ R → -H ≤ y → y ≤ F x → c13_pt x y ∈ U :=
    fun x y h1 h2 h3 => hKU ⟨h1, h2, h3⟩
  have hdQ : ∀ X ∈ U, DifferentiableAt ℝ Q X := fun X hX =>
    (hQU.contDiffAt (hUo.mem_nhds hX)).differentiableAt one_ne_zero
  have hCQ : ContinuousOn Q U := hQU.continuousOn
  have hCD : ContinuousOn (fderiv ℝ Q) U := hQU.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hFc : Continuous F := hF.continuous
  have hFd : ∀ x, HasDerivAt F (deriv F x) x := fun x =>
    ((hF.differentiable one_ne_zero) x).hasDerivAt
  have hF'c : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hRR : -R ≤ R := by linarith
  have habs : ∀ x ∈ Icc (-R) R, |x| ≤ R := fun x hx => abs_le.mpr hx
  have hFH' : ∀ x ∈ Icc (-R) R, -H ≤ F x := fun x hx => (hFH x hx).le
  have hRmem : R ∈ Icc (-R) R := ⟨hRR, le_rfl⟩
  have hmRmem : -R ∈ Icc (-R) R := ⟨le_rfl, hRR⟩
  -- vertical segments, top and bottom
  have hvert : ∀ x ∈ Icc (-R) R, MapsTo (fun y => c13_pt x y) (uIcc (-H) (F x)) U := by
    intro x hx y hy
    rw [uIcc_of_le (hFH' x hx)] at hy
    exact hUpt x y (habs x hx) hy.1 hy.2
  have hvc : ∀ x : ℝ, ContinuousOn (fun y => c13_pt x y) (uIcc (-H) (F x)) := fun x =>
    (c13g_aux_continuous_pt.comp (continuous_const.prodMk continuous_id)).continuousOn
  have htop : MapsTo (fun x => c13_pt x (F x)) (Icc (-R) R) U := fun x hx =>
    hUpt x _ (habs x hx) (hFH' x hx) le_rfl
  have hbot : MapsTo (fun x => c13_pt x (-H)) (Icc (-R) R) U := fun x hx =>
    hUpt x _ (habs x hx) le_rfl (hFH' x hx)
  have htc : Continuous (fun x => c13_pt x (F x)) :=
    c13g_aux_continuous_pt.comp (continuous_id.prodMk hFc)
  have hbc : Continuous (fun x => c13_pt x (-H)) :=
    c13g_aux_continuous_pt.comp (continuous_id.prodMk continuous_const)
  -- rectangle parametrization
  set L : ℝ → ℝ := fun x => F x + H with hL
  set φ : ℝ → ℝ → ℝ := fun x τ => L x * τ + -H with hφ
  have hφmem : ∀ x ∈ Icc (-R) R, ∀ τ ∈ Icc (0:ℝ) 1, -H ≤ φ x τ ∧ φ x τ ≤ F x := by
    intro x hx τ hτ
    have hL0 : 0 ≤ L x := by have := hFH' x hx; simp only [hL]; linarith
    constructor
    · simp only [hφ]; nlinarith [hτ.1]
    · simp only [hφ, hL] at hL0 ⊢; nlinarith [hτ.2]
  have hrect : MapsTo (fun p : ℝ × ℝ => c13_pt p.1 (φ p.1 p.2)) (Icc (-R) R ×ˢ Icc 0 1) U :=
    fun p hp => hUpt _ _ (habs _ hp.1) (hφmem _ hp.1 _ hp.2).1 (hφmem _ hp.1 _ hp.2).2
  have hrect' : ∀ x ∈ Icc (-R) R, ∀ τ ∈ Icc (0:ℝ) 1, c13_pt x (φ x τ) ∈ U :=
    fun x hx τ hτ => hrect (show (x, τ) ∈ Icc (-R) R ×ˢ Icc 0 1 from ⟨hx, hτ⟩)
  have hΨc : Continuous (fun p : ℝ × ℝ => c13_pt p.1 (φ p.1 p.2)) := by
    have : Continuous (fun p : ℝ × ℝ => (p.1, φ p.1 p.2)) := by
      simp only [hφ, hL]; fun_prop
    exact c13g_aux_continuous_pt.comp this
  -- derivative fields on the rectangle
  set hx' : ℝ → ℝ → ℝ := fun x τ =>
    fderiv ℝ Q (c13_pt x (φ x τ)) (c13_pt 1 (deriv F x * τ)) 0 * L x +
      Q (c13_pt x (φ x τ)) 0 * deriv F x with hhx'
  set kτ' : ℝ → ℝ → ℝ := fun x τ =>
    deriv F x * Q (c13_pt x (φ x τ)) 0 +
      τ * deriv F x * fderiv ℝ Q (c13_pt x (φ x τ)) (c13_pt 0 (L x)) 0 with hkτ'
  have hφx : ∀ x τ, HasDerivAt (fun x => φ x τ) (deriv F x * τ) x := fun x τ =>
    (((hFd x).add_const H).mul_const τ).add_const (-H)
  have hφτ : ∀ x τ, HasDerivAt (fun τ => φ x τ) (L x) τ := fun x τ =>
    (((hasDerivAt_id τ).const_mul (L x)).add_const (-H)).congr_deriv (mul_one _)
  have hder_h : ∀ x ∈ Icc (-R) R, ∀ τ ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun x => Q (c13_pt x (φ x τ)) 0 * L x) (hx' x τ) x := by
    intro x hx τ hτ
    have h1 := c13g_aux_comp_hasDerivAt (a := id) (b := fun x => φ x τ)
      (hdQ _ (hrect' x hx τ hτ)) (hasDerivAt_id x) (hφx x τ) 0
    exact h1.mul ((hFd x).add_const H)
  have hder_k : ∀ x ∈ Icc (-R) R, ∀ τ ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun τ => τ * deriv F x * Q (c13_pt x (φ x τ)) 0) (kτ' x τ) τ := by
    intro x hx τ hτ
    have h1 := c13g_aux_comp_hasDerivAt (a := fun _ => x) (b := fun τ => φ x τ)
      (hdQ _ (hrect' x hx τ hτ)) (hasDerivAt_const τ x) (hφτ x τ) 0
    have h0 : HasDerivAt (fun τ : ℝ => τ * deriv F x) (1 * deriv F x) τ :=
      (hasDerivAt_id' τ).mul_const _
    exact (h0.mul h1).congr_deriv (by simp only [hkτ']; ring)
  have hpoint : ∀ x τ,
      fderiv ℝ Q (c13_pt x (φ x τ)) (c13_pt 1 0) 0 * L x = hx' x τ - kτ' x τ := by
    intro x τ
    simp only [hhx', hkτ']
    rw [c13g_aux_fderiv_pt _ 1 (deriv F x * τ), c13g_aux_fderiv_pt _ 0 (L x)]
    ring
  -- continuity on the rectangle
  have hLc : Continuous L := by simp only [hL]; fun_prop
  have hΨr : ContinuousOn (fun p : ℝ × ℝ => c13_pt p.1 (φ p.1 p.2)) (Icc (-R) R ×ˢ Icc 0 1) :=
    hΨc.continuousOn
  have hcont_hx' : ContinuousOn (Function.uncurry hx') (Icc (-R) R ×ˢ Icc 0 1) := by
    have hV : Continuous (fun p : ℝ × ℝ => c13_pt 1 (deriv F p.1 * p.2)) :=
      c13g_aux_continuous_pt.comp (continuous_const.prodMk
        ((hF'c.comp continuous_fst).mul continuous_snd))
    have h1 := c13g_aux_cont_fderiv' hCD hΨr hrect hV.continuousOn 0
    have h2 := c13g_aux_cont_val hCQ hΨr hrect 0
    exact (h1.mul (hLc.comp continuous_fst).continuousOn).add
      (h2.mul (hF'c.comp continuous_fst).continuousOn)
  -- the rectangle FTC in `x`
  have hS5 : ∫ x in (-R)..R, ∫ τ in (0:ℝ)..1, hx' x τ =
      ∫ τ in (0:ℝ)..1, (Q (c13_pt R (φ R τ)) 0 * L R - Q (c13_pt (-R) (φ (-R) τ)) 0 * L (-R)) :=
    c13g_aux_rect_ftc (f := fun x τ => Q (c13_pt x (φ x τ)) 0 * L x) (f' := hx') hRR zero_le_one
      hder_h hcont_hx'
  have hwallc : ∀ x ∈ Icc (-R) R, IntervalIntegrable (fun τ => Q (c13_pt x (φ x τ)) 0 * L x)
      volume 0 1 := by
    intro x hx
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (c13g_aux_cont_val hCQ hΨr hrect 0).comp (f := fun τ : ℝ => (x, τ))
      (Continuous.continuousOn (by fun_prop)) (fun τ hτ => ⟨hx, hτ⟩)
  have hwall : ∀ x : ℝ, ∫ τ in (0:ℝ)..1, Q (c13_pt x (φ x τ)) 0 * L x =
      ∫ y in (-H)..(F x), Q (c13_pt x y) 0 := fun x =>
    c13g_aux_cov (fun y => Q (c13_pt x y) 0) (F x) H
  rw [intervalIntegral.integral_sub (hwallc R hRmem) (hwallc (-R) hmRmem), hwall, hwall] at hS5
  have hcont_k : ContinuousOn (Function.uncurry kτ') (Icc (-R) R ×ˢ Icc 0 1) := by
    have hV : Continuous (fun p : ℝ × ℝ => c13_pt 0 (L p.1)) :=
      c13g_aux_continuous_pt.comp (continuous_const.prodMk (hLc.comp continuous_fst))
    have h1 := c13g_aux_cont_fderiv' hCD hΨr hrect hV.continuousOn 0
    have h2 := c13g_aux_cont_val hCQ hΨr hrect 0
    exact ((hF'c.comp continuous_fst).continuousOn.mul h2).add
      ((continuous_snd.mul (hF'c.comp continuous_fst)).continuousOn.mul h1)
  have hslice : ∀ g : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry g) (Icc (-R) R ×ˢ Icc 0 1) →
      ∀ x ∈ Icc (-R) R, IntervalIntegrable (g x) volume 0 1 := by
    intro g hg x hx
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact hg.comp (f := fun τ : ℝ => (x, τ)) (Continuous.continuousOn (by fun_prop))
      (fun τ hτ => ⟨hx, hτ⟩)
  -- inner integrals for fixed `x`
  have hAint : ∀ x ∈ Icc (-R) R, ∫ y in (-H)..(F x), fderiv ℝ Q (c13_pt x y) (c13_pt 1 0) 0 =
      (∫ τ in (0:ℝ)..1, hx' x τ) - deriv F x * Q (c13_pt x (F x)) 0 := by
    intro x hx
    rw [← c13g_aux_cov (fun y => fderiv ℝ Q (c13_pt x y) (c13_pt 1 0) 0) (F x) H]
    have hcongr : ∫ τ in (0:ℝ)..1,
        fderiv ℝ Q (c13_pt x ((F x + H) * τ + -H)) (c13_pt 1 0) 0 * (F x + H) =
          ∫ τ in (0:ℝ)..1, (hx' x τ - kτ' x τ) :=
      intervalIntegral.integral_congr (fun τ _ => hpoint x τ)
    rw [hcongr]
    have hi1 := hslice hx' hcont_hx' x hx
    have hi2 := hslice kτ' hcont_k x hx
    rw [intervalIntegral.integral_sub hi1 hi2]
    have hk := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun τ => τ * deriv F x * Q (c13_pt x (φ x τ)) 0) (f' := kτ' x)
      (fun τ hτ => hder_k x hx τ (by rwa [uIcc_of_le zero_le_one] at hτ)) hi2
    rw [hk]
    have h1 : φ x 1 = F x := by simp only [hφ, hL]; ring
    simp only [h1]; ring
  have hBint : ∀ x ∈ Icc (-R) R, ∫ y in (-H)..(F x), fderiv ℝ Q (c13_pt x y) (c13_pt 0 1) 1 =
      Q (c13_pt x (F x)) 1 - Q (c13_pt x (-H)) 1 := by
    intro x hx
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => Q (c13_pt x y) 1)
      (fun y hy => ?_) ?_
    · exact c13g_aux_comp_hasDerivAt (a := fun _ => x) (b := id) (hdQ _ (hvert x hx hy))
        (hasDerivAt_const y x) (hasDerivAt_id y) 1
    · exact (c13g_aux_cont_fderiv hCD (hvc x) (hvert x hx) _ 1).intervalIntegrable
  have hinner : ∀ x ∈ Icc (-R) R, ∫ y in (-H)..(F x), c13g_aux_div Q (c13_pt x y) =
      (∫ τ in (0:ℝ)..1, hx' x τ) - deriv F x * Q (c13_pt x (F x)) 0 +
        (Q (c13_pt x (F x)) 1 - Q (c13_pt x (-H)) 1) := by
    intro x hx
    rw [← hAint x hx, ← hBint x hx]
    exact intervalIntegral.integral_add
      (c13g_aux_cont_fderiv hCD (hvc x) (hvert x hx) _ 0).intervalIntegrable
      (c13g_aux_cont_fderiv hCD (hvc x) (hvert x hx) _ 1).intervalIntegrable
  -- compact closed domain and the 2D Fubini step
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).bddAbove_image hFc.continuousOn
  set K2 : Set (ℝ × ℝ) := {p | |p.1| ≤ R ∧ -H ≤ p.2 ∧ p.2 ≤ F p.1} with hK2
  have hK2c : IsCompact K2 := by
    refine ((isCompact_Icc (a := -R) (b := R)).prod (isCompact_Icc (a := -H) (b := B))).of_isClosed_subset ?_ ?_
    · exact (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).inter
        ((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd (hFc.comp continuous_fst)))
    · intro p hp
      have hp1 : p.1 ∈ Icc (-R) R := abs_le.mp hp.1
      exact ⟨hp1, hp.2.1, hp.2.2.trans (hB ⟨p.1, hp1, rfl⟩)⟩
  have hK2U : MapsTo (fun p : ℝ × ℝ => c13_pt p.1 p.2) K2 U := fun p hp =>
    hUpt _ _ hp.1 hp.2.1 hp.2.2
  have hgc : ContinuousOn (fun p : ℝ × ℝ => c13g_aux_div Q (c13_pt p.1 p.2)) K2 :=
    (c13g_aux_cont_fderiv hCD c13g_aux_continuous_pt.continuousOn hK2U _ 0).add
      (c13g_aux_cont_fderiv hCD c13g_aux_continuous_pt.continuousOn hK2U _ 1)
  have hint2 : IntegrableOn (fun p : ℝ × ℝ => c13g_aux_div Q (c13_pt p.1 p.2))
      {p : ℝ × ℝ | |p.1| < R ∧ -H < p.2 ∧ p.2 < F p.1} :=
    (hgc.integrableOn_compact hK2c).mono_set (fun p hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩)
  have hS1 : ∫ X in {X : c13_E | |X 0| < R ∧ -H < X 1 ∧ X 1 < F (X 0)}, c13g_aux_div Q X =
      ∫ x in (-R)..R, ∫ y in (-H)..(F x), c13g_aux_div Q (c13_pt x y) := by
    rw [c13g_aux_setIntegral]
    exact c13g_aux_subgraph_fubini hR hFc hFH' (g := fun p => c13g_aux_div Q (c13_pt p.1 p.2))
      hint2
  -- one-dimensional integrability
  have hII : ∀ g : ℝ → ℝ, ContinuousOn g (Icc (-R) R) → IntervalIntegrable g volume (-R) R :=
    fun g hg => by refine ContinuousOn.intervalIntegrable ?_; rwa [uIcc_of_le hRR]
  have hT0 : ContinuousOn (fun x => Q (c13_pt x (F x)) 0) (Icc (-R) R) :=
    c13g_aux_cont_val hCQ htc.continuousOn htop 0
  have hT1 : ContinuousOn (fun x => Q (c13_pt x (F x)) 1) (Icc (-R) R) :=
    c13g_aux_cont_val hCQ htc.continuousOn htop 1
  have hB1 : ContinuousOn (fun x => Q (c13_pt x (-H)) 1) (Icc (-R) R) :=
    c13g_aux_cont_val hCQ hbc.continuousOn hbot 1
  have hFT0 : ContinuousOn (fun x => deriv F x * Q (c13_pt x (F x)) 0) (Icc (-R) R) :=
    hF'c.continuousOn.mul hT0
  have hP : IntervalIntegrable (fun x => ∫ τ in (0:ℝ)..1, hx' x τ) volume (-R) R :=
    c13g_aux_param_intervalIntegrable hRR zero_le_one hcont_hx'
  have hwR : IntervalIntegrable (fun y => Q (c13_pt R y) 0) volume (-H) (F R) :=
    (c13g_aux_cont_val hCQ (hvc R) (hvert R hRmem) 0).intervalIntegrable
  have hwmR : IntervalIntegrable (fun y => Q (c13_pt (-R) y) 0) volume (-H) (F (-R)) :=
    (c13g_aux_cont_val hCQ (hvc (-R)) (hvert (-R) hmRmem) 0).intervalIntegrable
  refine ⟨(c13g_aux_integrableOn_iff _ _).mpr hint2, (hII _ hT1).sub (hII _ hFT0), hII _ hB1,
    hwR, hwmR, ?_⟩
  rw [hS1, intervalIntegral.integral_congr
    (fun x hx => hinner x (by rwa [uIcc_of_le hRR] at hx))]
  rw [intervalIntegral.integral_add (hP.sub (hII _ hFT0)) ((hII _ hT1).sub (hII _ hB1)),
    intervalIntegral.integral_sub hP (hII _ hFT0),
    intervalIntegral.integral_sub (hII _ hT1) (hII _ hB1),
    intervalIntegral.integral_sub (hII _ hT1) (hII _ hFT0), hS5]
  ring

/-- Blueprint: lem:c13_compact_graph_flux.  For a `C¹` graph and a compactly supported `C¹`
vector field, `∫_{y < F(x)} div Q = ∫ (Q₂ - F' Q₁)(x, F(x)) dx`, both absolutely convergent.
No slope bound on `F` is needed: the compact support of `Q` confines everything to a bounded
box. -/
theorem c13_compact_graph_flux {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {Q : c13_E → c13_E}
    (hQ : ContDiff ℝ 1 Q) (hQc : HasCompactSupport Q) :
    IntegrableOn (c13g_aux_div Q) {X : c13_E | X 1 < F (X 0)} ∧
    Integrable (fun x => Q (c13_pt x (F x)) 1 - deriv F x * Q (c13_pt x (F x)) 0) ∧
    ∫ X in {X : c13_E | X 1 < F (X 0)}, c13g_aux_div Q X =
      ∫ x, (Q (c13_pt x (F x)) 1 - deriv F x * Q (c13_pt x (F x)) 0) := by
  obtain ⟨r, hr⟩ := hQc.isCompact.isBounded.subset_closedBall 0
  set ρ := max r 1 with hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : ∀ X : c13_E, ρ < ‖X‖ → X ∉ tsupport Q := by
    intro X hX hmem
    have := hr hmem
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left r 1]
  have hQ0 : ∀ X : c13_E, ρ < ‖X‖ → Q X = 0 := fun X hX =>
    Function.notMem_support.mp (fun h => hsupp X hX (subset_tsupport _ h))
  have hdiv0 : ∀ X : c13_E, ρ < ‖X‖ → c13g_aux_div Q X = 0 := by
    intro X hX
    simp [c13g_aux_div, fderiv_of_notMem_tsupport (𝕜 := ℝ) (hsupp X hX)]
  have hc0 : ∀ X : c13_E, |X 0| ≤ ‖X‖ := fun X => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 0
  have hc1 : ∀ X : c13_E, |X 1| ≤ ‖X‖ := fun X => by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le X 1
  set R := ρ + 1 with hRdef
  have hR : 0 < R := by linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hF.continuous.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by linarith, by linarith⟩)
  set H := ρ + 1 + C with hHdef
  have hH : 0 < H := by linarith
  have hFH : ∀ s ∈ Icc (-R) R, -H < F s := by
    intro s hs
    have := hC s hs
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (F s)]
  have hfin := c13_finite_graph_flux hR hH hF hFH
    ⟨univ, isOpen_univ, subset_univ _, hQ.contDiffOn⟩
  obtain ⟨-, -, -, -, -, hEq⟩ := hfin
  -- artificial sides vanish
  have hbot : ∀ s, Q (c13_pt s (-H)) 1 = 0 := fun s => by
    rw [hQ0 _ (lt_of_lt_of_le (by rw [c13g_aux_pt_one, abs_neg, abs_of_pos hH]; linarith) (hc1 _))]; rfl
  have hwall : ∀ x y, |x| = R → Q (c13_pt x y) 0 = 0 := fun x y hx => by
    rw [hQ0 _ (lt_of_lt_of_le (by simp only [c13g_aux_pt_zero, hx]; linarith) (hc0 _))]; rfl
  have hwR : (∫ y in (-H)..(F R), Q (c13_pt R y) 0) = 0 := by
    simp [hwall R _ (abs_of_pos hR)]
  have hwmR : (∫ y in (-H)..(F (-R)), Q (c13_pt (-R) y) 0) = 0 := by
    simp [hwall (-R) _ (by rw [abs_neg, abs_of_pos hR])]
  have hbI : (∫ s in (-R)..R, Q (c13_pt s (-H)) 1) = 0 := by simp [hbot]
  rw [hwR, hwmR, hbI] at hEq
  -- the top integrand
  set g : ℝ → ℝ := fun x => Q (c13_pt x (F x)) 1 - deriv F x * Q (c13_pt x (F x)) 0 with hg
  have hg0 : ∀ x, ρ < |x| → g x = 0 := by
    intro x hx
    simp only [hg, hQ0 _ (lt_of_lt_of_le (by simpa using hx) (hc0 (c13_pt x (F x))))]
    simp
  have hgc : Continuous g := by
    have hpt : Continuous (fun x => c13_pt x (F x)) :=
      c13g_aux_continuous_pt.comp (continuous_id.prodMk hF.continuous)
    have hq : ∀ i : Fin 2, Continuous (fun x => Q (c13_pt x (F x)) i) := fun i =>
      (PiLp.continuous_apply 2 _ i).comp (hQ.continuous.comp hpt)
    exact (hq 1).sub ((hF.continuous_deriv le_rfl).mul (hq 0))
  have hgsupp : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -ρ) (b := ρ)) (fun x hx => hg0 x ?_)
    by_contra h
    exact hx (abs_le.mp (not_lt.mp h))
  have hgI : Integrable g := hgc.integrable_of_hasCompactSupport hgsupp
  -- the divergence
  have hdc : Continuous (c13g_aux_div Q) := by
    have hD := hQ.continuous_fderiv one_ne_zero
    have h1 : ∀ (v : c13_E) (i : Fin 2), Continuous (fun X => fderiv ℝ Q X v i) := fun v i =>
      (PiLp.continuous_apply 2 _ i).comp (hD.clm_apply continuous_const)
    exact (h1 _ 0).add (h1 _ 1)
  have hdsupp : HasCompactSupport (c13g_aux_div Q) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : c13_E) ρ) (fun X hX => hdiv0 X ?_)
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hX; exact hX
  have hdI : Integrable (c13g_aux_div Q) := hdc.integrable_of_hasCompactSupport hdsupp
  refine ⟨hdI.integrableOn, hgI, ?_⟩
  -- reduce both sides to the finite box
  have hSm : MeasurableSet {X : c13_E | X 1 < F (X 0)} :=
    (isOpen_lt (PiLp.continuous_apply 2 _ 1)
      (hF.continuous.comp (PiLp.continuous_apply 2 _ 0))).measurableSet
  have hDm : MeasurableSet {X : c13_E | |X 0| < R ∧ -H < X 1 ∧ X 1 < F (X 0)} := by
    have h0 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
    have h1 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
    exact ((isOpen_lt (continuous_abs.comp h0) continuous_const).inter
      ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 (hF.continuous.comp h0)))).measurableSet
  have hL : ∫ X in {X : c13_E | X 1 < F (X 0)}, c13g_aux_div Q X =
      ∫ X in {X : c13_E | |X 0| < R ∧ -H < X 1 ∧ X 1 < F (X 0)}, c13g_aux_div Q X := by
    rw [← integral_indicator hSm, ← integral_indicator hDm]
    congr 1; funext X
    by_cases hX : ρ < ‖X‖
    · simp [indicator, hdiv0 X hX]
    · push Not at hX
      have hx0 : |X 0| < R := by linarith [hc0 X]
      have hx1 : -H < X 1 := by linarith [neg_abs_le (X 1), hc1 X]
      by_cases hS : X 1 < F (X 0)
      · rw [indicator_of_mem (show X ∈ {X : c13_E | X 1 < F (X 0)} from hS),
          indicator_of_mem (show X ∈ {X : c13_E | |X 0| < R ∧ -H < X 1 ∧ X 1 < F (X 0)} from
            ⟨hx0, hx1, hS⟩)]
      · rw [indicator_of_notMem (show X ∉ {X : c13_E | X 1 < F (X 0)} from hS),
          indicator_of_notMem (show X ∉ {X : c13_E | |X 0| < R ∧ -H < X 1 ∧ X 1 < F (X 0)} from
            fun h => hS h.2.2)]
  have hRint : ∫ x, g x = ∫ x in (-R)..R, g x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hg0 x ?_)).symm
    by_contra h
    push Not at h
    apply hx
    have := abs_le.mp h
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  rw [hL, hEq, hRint]
  ring

end GSQG
