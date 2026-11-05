import GSQG.PatchEquation.GraphFlux

/-!
# Beyond the paper (2D patch derivation): the weak patch system, moving-patch pairing, trace tests
(blueprint ch. 13)

Helpers are named `c13w_aux_*`.

## Conventions fixed here for all `PatchEquation/` modules

* Spacetime is `c13_E × ℝ` with the product (volume) measure; a spacetime point is `p = (X, t)`.
* A *scalar spacetime test* on `E × I` (`c13_scalar_test I ζ`) is a function
  `ζ : c13_E × ℝ → ℝ` that is `C^∞` on all of `c13_E × ℝ`, has compact support, and whose
  topological support lies in `univ ×ˢ I`.  For open `I` this is exactly `C_c^∞(E × I)` extended
  by zero.  A *vector spacetime test* (`c13_vector_test I Φ`) is the same with values in `c13_E`.
* Densities and velocities are curried like `c13_graph_velocity`: `θ : c13_E → ℝ → ℝ`,
  `u : c13_E → ℝ → c13_E`, written `θ X t`, `u X t`.  The patch density is
  `θ_F X t = (c13_patch F t).indicator 1 X`.
* `∂_t ζ (X, t) = deriv (fun s => ζ (X, s)) t` and
  `u · ∇_X ζ = fderiv ℝ (fun Y => ζ (Y, t)) X (u X t)` (the spatial derivative applied to `u`).
* Spacetime pairings `∫_I ∫_E` are written as set integrals over `univ ×ˢ I` for the product
  measure, and every pairing carries an explicit `IntegrableOn` conjunct (absolute convergence).
* `u ∈ L¹_loc(E × I)` is `LocallyIntegrableOn (Function.uncurry u) (univ ×ˢ I)`.  The product
  `θ u` only appears inside the transport pairing, after this representative is given.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-- Blueprint: def:c13_weak_patch_system (test-function convention).  A scalar spacetime test on
`E × I`: smooth on `c13_E × ℝ`, compactly supported, with topological support in `univ ×ˢ I`.
(Smooth extension by zero of `C_c^∞(E × I)`; there is no condition at the ends of `I`.) -/
def c13_scalar_test (I : Set ℝ) (ζ : c13_E × ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ univ ×ˢ I

/-- Blueprint: def:c13_weak_patch_system (test-function convention).  A vector spacetime test on
`E × I`: smooth `c13_E`-valued, compactly supported, with topological support in `univ ×ˢ I`. -/
def c13_vector_test (I : Set ℝ) (Φ : c13_E × ℝ → c13_E) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ univ ×ˢ I

/-- Blueprint: def:c13_weak_patch_system.  The coefficient-`c` velocity law on `E × I`:
`θ` is a.e.-strongly measurable and bounded on `E × I`, `u ∈ L¹_loc(E × I; E)`, and for every
vector spacetime test `Φ` both pairings are absolutely integrable on `E × I` and
`∫_I∫_E u · Φ = ∫_I∫_E θ(Y,t) B*_{α,c}(Φ(·,t))(Y)`. -/
def c13_velocity_law (α c : ℝ) (I : Set ℝ) (θ : c13_E → ℝ → ℝ) (u : c13_E → ℝ → c13_E) :
    Prop :=
  AEStronglyMeasurable (Function.uncurry θ) (volume.restrict (univ ×ˢ I)) ∧
  (∃ M : ℝ, ∀ X : c13_E, ∀ t ∈ I, |θ X t| ≤ M) ∧
  LocallyIntegrableOn (Function.uncurry u) (univ ×ˢ I) ∧
  ∀ Φ : c13_E × ℝ → c13_E, c13_vector_test I Φ →
    IntegrableOn (fun p : c13_E × ℝ => inner ℝ (u p.1 p.2) (Φ p)) (univ ×ˢ I) ∧
    IntegrableOn (fun p : c13_E × ℝ =>
      θ p.1 p.2 * c13_adjoint α c (fun Y => Φ (Y, p.2)) p.1) (univ ×ˢ I) ∧
    (∫ p in univ ×ˢ I, inner ℝ (u p.1 p.2) (Φ p)) =
      ∫ p in univ ×ˢ I, θ p.1 p.2 * c13_adjoint α c (fun Y => Φ (Y, p.2)) p.1

/-- Blueprint: def:c13_weak_patch_system.  The coefficient-`c` weak patch system on `E × I`:
the velocity law together with conservative weak transport — for every scalar spacetime test `ζ`
the pairing `θ (∂_t ζ + u · ∇_X ζ)` is absolutely integrable on `E × I` with integral zero. -/
def c13_weak_patch_system (α c : ℝ) (I : Set ℝ) (θ : c13_E → ℝ → ℝ)
    (u : c13_E → ℝ → c13_E) : Prop :=
  c13_velocity_law α c I θ u ∧
  ∀ ζ : c13_E × ℝ → ℝ, c13_scalar_test I ζ →
    IntegrableOn (fun p : c13_E × ℝ =>
      θ p.1 p.2 * (deriv (fun s => ζ (p.1, s)) p.2 +
        fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2))) (univ ×ˢ I) ∧
    (∫ p in univ ×ˢ I, θ p.1 p.2 * (deriv (fun s => ζ (p.1, s)) p.2 +
        fderiv ℝ (fun Y => ζ (Y, p.2)) p.1 (u p.1 p.2))) = 0

/-! ### Helpers (`c13w_aux_*`) -/

theorem c13w_aux_pt_eta (X : c13_E) : c13_pt (X 0) (X 1) = X := by
  ext i; fin_cases i <;> simp [c13_pt]

@[simp] theorem c13w_aux_pt_apply0 (x y : ℝ) : (c13_pt x y) 0 = x := by simp [c13_pt]
@[simp] theorem c13w_aux_pt_apply1 (x y : ℝ) : (c13_pt x y) 1 = y := by simp [c13_pt]

theorem c13w_aux_continuous_pt : Continuous (fun q : ℝ × ℝ => c13_pt q.1 q.2) := by
  unfold c13_pt
  fun_prop

/-- A continuous function on an open set vanishing a.e. on it vanishes everywhere on it. -/
theorem c13w_aux_eq_zero_of_ae {U : Set (ℝ × ℝ)} (hU : IsOpen U) {r : ℝ × ℝ → ℝ}
    (hr : ContinuousOn r U) (h : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), x ∈ U → r x = 0) :
    ∀ x ∈ U, r x = 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨x0, hx0, hr0⟩ := hc
  have hV : IsOpen (U ∩ r ⁻¹' {0}ᶜ) := hr.isOpen_inter_preimage hU isOpen_compl_singleton
  have hpos : 0 < volume (U ∩ r ⁻¹' {0}ᶜ) := hV.measure_pos _ ⟨x0, hx0, hr0⟩
  have hzero : volume (U ∩ r ⁻¹' {0}ᶜ) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with x hx
    rintro ⟨h1, h2⟩
    exact h2 (hx h1)
  exact hpos.ne' hzero

/-- The fixed bump `η` used to lift graph tests. -/
def c13w_aux_bump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem c13w_aux_lift (I : Set ℝ) (F : ℝ → ℝ → ℝ) (hF : c13_graph_class I F)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ univ ×ˢ I) :
    ∃ ζ : c13_E × ℝ → ℝ, c13_scalar_test I ζ ∧
        ∀ x t : ℝ, ζ (c13_pt x (F x t), t) = ψ (x, t) := by
  obtain ⟨hI, -, hFs, -⟩ := hF
  have hU : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hI
  set η := c13w_aux_bump
  set g : c13_E × ℝ → ℝ × ℝ := fun p => (p.1 0, p.2) with hg
  have h0 : ContDiff ℝ (⊤ : ℕ∞) g := by rw [hg]; fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : c13_E × ℝ => p.1 1) := by fun_prop
  refine ⟨fun p => ψ (g p) * η (p.1 1 - F (p.1 0) p.2), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.2 ∈ I
    · have hFa : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) (g p) :=
        hFs.contDiffAt (hU.mem_nhds ⟨mem_univ _, hp⟩)
      exact (hψ.contDiffAt.comp p h0.contDiffAt).mul
        (η.contDiff.contDiffAt.comp p (h1.contDiffAt.sub (hFa.comp p h0.contDiffAt)))
    · have hgp : g p ∉ tsupport ψ := fun h => hp (hψs h).2
      rw [notMem_tsupport_iff_eventuallyEq] at hgp
      have : (fun p => ψ (g p) * η (p.1 1 - F (p.1 0) p.2)) =ᶠ[𝓝 p] fun _ => 0 := by
        have := h0.continuous.continuousAt.tendsto.eventually hgp
        filter_upwards [this] with q hq
        simp [hq]
      exact contDiffAt_const.congr_of_eventuallyEq this
  · have hFc : ContinuousOn (fun q : ℝ × ℝ => F q.1 q.2) (tsupport ψ) :=
      hFs.continuousOn.mono hψs
    set G : (ℝ × ℝ) × ℝ → c13_E × ℝ :=
      fun w => (c13_pt w.1.1 (F w.1.1 w.1.2 + w.2), w.1.2) with hG
    have hGc : ContinuousOn G (tsupport ψ ×ˢ Icc (-1) 1) := by
      have hF' : ContinuousOn (fun w : (ℝ × ℝ) × ℝ => F w.1.1 w.1.2)
          (tsupport ψ ×ˢ Icc (-1) 1) :=
        hFc.comp continuous_fst.continuousOn (fun w hw => hw.1)
      refine ContinuousOn.prodMk ?_ (continuous_snd.comp continuous_fst).continuousOn
      exact c13w_aux_continuous_pt.comp_continuousOn
        ((continuous_fst.comp continuous_fst).continuousOn.prodMk
          (hF'.add continuous_snd.continuousOn))
    refine HasCompactSupport.intro ((hψc.prod isCompact_Icc).image_of_continuousOn hGc) ?_
    intro p hpK
    by_contra hne
    have hψne : ψ (g p) ≠ 0 := left_ne_zero_of_mul hne
    have hηne : η (p.1 1 - F (p.1 0) p.2) ≠ 0 := right_ne_zero_of_mul hne
    have hmem : p.1 1 - F (p.1 0) p.2 ∈ Icc (-1 : ℝ) 1 := by
      have : p.1 1 - F (p.1 0) p.2 ∈ Function.support η := hηne
      rw [η.support_eq] at this
      have h2 := Metric.mem_ball.mp this
      rw [Real.dist_eq, sub_zero] at h2
      have : η.rOut = 1 := rfl
      rw [this] at h2
      exact ⟨by linarith [neg_abs_le (p.1 1 - F (p.1 0) p.2)],
        by linarith [le_abs_self (p.1 1 - F (p.1 0) p.2)]⟩
    apply hpK
    refine ⟨(g p, p.1 1 - F (p.1 0) p.2), ⟨subset_tsupport _ hψne, hmem⟩, ?_⟩
    simp only [hG, hg, add_sub_cancel]
    rw [c13w_aux_pt_eta]
  · refine (tsupport_mul_subset_left).trans ?_
    refine (tsupport_comp_subset_preimage ψ h0.continuous).trans ?_
    intro p hp
    exact ⟨mem_univ _, (hψs hp).2⟩
  · intro x t
    simp only [hg, c13w_aux_pt_apply0, c13w_aux_pt_apply1, sub_self]
    rw [η.one_of_mem_closedBall (by simpa using η.rIn_pos.le), mul_one]

/-- Coordinates `(X, t) ↦ (X 0, (t, X 1))` on spacetime, as a measurable equivalence. -/
def c13w_aux_coord : c13_E × ℝ ≃ᵐ ℝ × (ℝ × ℝ) :=
  (((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow).prodCongr
    (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodComm))

theorem c13w_aux_coord_mp : MeasurePreserving c13w_aux_coord volume volume := by
  unfold c13w_aux_coord
  have h1 : MeasurePreserving (((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans
      MeasurableEquiv.finTwoArrow).prodCongr (MeasurableEquiv.refl ℝ))
      (volume : Measure (c13_E × ℝ)) (volume : Measure ((ℝ × ℝ) × ℝ)) :=
    ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
      (volume_preserving_finTwoArrow ℝ)).prod (MeasurePreserving.id volume)
  have h2 : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × (ℝ × ℝ))
      volume volume := measurePreserving_prodAssoc volume volume volume
  have h3 : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)) volume volume :=
    (MeasurePreserving.id volume).prod (Measure.measurePreserving_swap)
  exact h1.trans (h2.trans h3)

theorem c13w_aux_coord_symm (w : ℝ × (ℝ × ℝ)) :
    c13w_aux_coord.symm w = (c13_pt w.1 w.2.2, w.2.1) := by
  rcases w with ⟨x, t, y⟩
  apply c13w_aux_coord.injective
  rw [MeasurableEquiv.apply_symm_apply]
  simp [c13w_aux_coord, c13_pt, MeasurableEquiv.finTwoArrow, MeasurableEquiv.prodCongr,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm, MeasurableEquiv.piFinTwo]

theorem c13w_aux_integral_coord (f : c13_E × ℝ → ℝ) :
    (∫ p, f p) = ∫ w : ℝ × (ℝ × ℝ), f (c13_pt w.1 w.2.2, w.2.1) := by
  rw [← c13w_aux_coord_mp.symm.integral_comp']
  simp only [c13w_aux_coord_symm]

theorem c13w_aux_integrable_coord {f : c13_E × ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun w : ℝ × (ℝ × ℝ) => f (c13_pt w.1 w.2.2, w.2.1)) := by
  have := (c13w_aux_coord_mp.symm.integrable_comp_emb
    c13w_aux_coord.symm.measurableEmbedding).mpr hf
  simpa [Function.comp_def, c13w_aux_coord_symm] using this
/-- The time partial derivative `∂_t ζ` of a spacetime function, as a directional derivative. -/
def c13w_aux_dt (ζ : c13_E × ℝ → ℝ) (p : c13_E × ℝ) : ℝ := fderiv ℝ ζ p (0, 1)

/-- The vertical partial derivative `∂_y ζ` of a spacetime function. -/
def c13w_aux_dy (ζ : c13_E × ℝ → ℝ) (p : c13_E × ℝ) : ℝ := fderiv ℝ ζ p (c13_pt 0 1, 0)

theorem c13w_aux_hasDerivAt_dt {ζ : c13_E × ℝ → ℝ} (hζ : Differentiable ℝ ζ) (X : c13_E)
    (t : ℝ) : HasDerivAt (fun s => ζ (X, s)) (c13w_aux_dt ζ (X, t)) t := by
  have hc : HasDerivAt (fun s : ℝ => (X, s)) ((0 : c13_E), (1 : ℝ)) t :=
    (hasDerivAt_const t X).prodMk (hasDerivAt_id t)
  exact (hζ (X, t)).hasFDerivAt.comp_hasDerivAt t hc

theorem c13w_aux_deriv_dt {ζ : c13_E × ℝ → ℝ} (hζ : Differentiable ℝ ζ) (X : c13_E) (t : ℝ) :
    deriv (fun s => ζ (X, s)) t = c13w_aux_dt ζ (X, t) :=
  (c13w_aux_hasDerivAt_dt hζ X t).deriv

theorem c13w_aux_dt_dy_zero {ζ : c13_E × ℝ → ℝ} {p : c13_E × ℝ} (hp : p ∉ tsupport ζ) :
    c13w_aux_dt ζ p = 0 ∧ c13w_aux_dy ζ p = 0 := by
  have : fderiv ℝ ζ p = 0 := by
    by_contra h
    exact hp (support_fderiv_subset (𝕜 := ℝ) h)
  simp [c13w_aux_dt, c13w_aux_dy, this]

theorem c13w_aux_continuous_dt_dy {ζ : c13_E × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) :
    Continuous (c13w_aux_dt ζ) ∧ Continuous (c13w_aux_dy ζ) := by
  have h := hζ.continuous_fderiv (by simp)
  exact ⟨h.clm_apply continuous_const, h.clm_apply continuous_const⟩

theorem c13w_aux_pt_add (x a b : ℝ) : c13_pt x (a + b) = c13_pt x b + a • c13_pt 0 1 := by
  ext i; fin_cases i <;> simp [c13_pt]; ring

theorem c13w_aux_pt_add' (x a b : ℝ) : c13_pt x (a + b) = c13_pt x a + b • c13_pt 0 1 := by
  ext i; fin_cases i <;> simp [c13_pt]

/-- `F_t` exists and is continuous on `ℝ × I`. -/
theorem c13w_aux_Ft {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hI : IsOpen I)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I)) :
    (∀ x, ∀ t ∈ I, HasDerivAt (fun t => F x t) (deriv (fun t => F x t) t) t) ∧
    ContinuousOn (fun q : ℝ × ℝ => deriv (fun t => F q.1 t) q.2) (univ ×ˢ I) := by
  have hU : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hI
  have hd : ∀ q ∈ (univ ×ˢ I : Set (ℝ × ℝ)),
      HasDerivAt (fun t => F q.1 t) (fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) q (0, 1)) q.2 := by
    intro q hq
    have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ => F q.1 q.2) q :=
      ((hFs.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
    have hc : HasDerivAt (fun s : ℝ => (q.1, s)) ((0 : ℝ), (1 : ℝ)) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    exact hdiff.hasFDerivAt.comp_hasDerivAt q.2 hc
  refine ⟨fun x t ht => ?_, ?_⟩
  · exact (hd (x, t) ⟨mem_univ _, ht⟩).differentiableAt.hasDerivAt
  · have hcf := (hFs.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
      (continuousOn_const (c := ((0 : ℝ), (1 : ℝ))))
    refine hcf.congr (fun q hq => ?_)
    exact (hd q hq).deriv

theorem c13w_aux_box {I : Set ℝ} {F : ℝ → ℝ → ℝ}
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I))
    {ζ : c13_E × ℝ → ℝ} (hζc : HasCompactSupport ζ) (hζs : tsupport ζ ⊆ univ ×ˢ I) :
    ∃ R, ∀ x s t : ℝ, (c13_pt x (F x t + s), t) ∈ tsupport ζ →
      |x| ≤ R ∧ |s| ≤ R ∧ |t| ≤ R := by
  have hK : IsCompact (tsupport ζ) := hζc
  obtain ⟨R1, hR1⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  set Kt := Prod.snd '' tsupport ζ
  have hKt : IsCompact Kt := hK.image continuous_snd
  have hC : IsCompact (Icc (-R1) R1 ×ˢ Kt) := isCompact_Icc.prod hKt
  have hCsub : Icc (-R1) R1 ×ˢ Kt ⊆ (univ ×ˢ I : Set (ℝ × ℝ)) := by
    rintro ⟨x, t⟩ ⟨-, ⟨p, hp, rfl⟩⟩
    exact ⟨mem_univ _, (hζs hp).2⟩
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hFs.continuousOn.mono hCsub)
  refine ⟨R1 + M, fun x s t hP => ?_⟩
  have hn := hR1 _ hP
  rw [Prod.norm_def] at hn
  have hX : ‖c13_pt x (F x t + s)‖ ≤ R1 := le_trans (le_max_left _ _) hn
  have ht : |t| ≤ R1 := by
    have := le_trans (le_max_right _ _) hn; rwa [Real.norm_eq_abs] at this
  have hx : |x| ≤ R1 := by
    have := (PiLp.norm_apply_le (c13_pt x (F x t + s)) 0).trans hX
    simpa [Real.norm_eq_abs] using this
  have hy : |F x t + s| ≤ R1 := by
    have := (PiLp.norm_apply_le (c13_pt x (F x t + s)) 1).trans hX
    simpa [Real.norm_eq_abs] using this
  have hFb : |F x t| ≤ M := by
    have := hM (x, t) ⟨⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩,
      ⟨(c13_pt x (F x t + s), t), hP, rfl⟩⟩
    simpa [Real.norm_eq_abs] using this
  have h0M : 0 ≤ M := (abs_nonneg _).trans hFb
  refine ⟨by linarith, ?_, by linarith⟩
  calc |s| = |(F x t + s) - F x t| := by ring_nf
    _ ≤ |F x t + s| + |F x t| := abs_sub _ _
    _ ≤ R1 + M := by linarith

/-- Continuity of `h(x,t) φ(x, F(x,t)+s, t)` on `ℝ³` when `φ` vanishes off `tsupport ζ`. -/
theorem c13w_aux_cont {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hI : IsOpen I)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I))
    {ζ : c13_E × ℝ → ℝ} (hζc : HasCompactSupport ζ) (hζs : tsupport ζ ⊆ univ ×ˢ I)
    {φ : c13_E × ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ p ∉ tsupport ζ, φ p = 0)
    {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h (univ ×ˢ I)) :
    Continuous (fun w : ℝ × ℝ × ℝ =>
      h (w.1, w.2.2) * φ (c13_pt w.1 (F w.1 w.2.2 + w.2.1), w.2.2)) := by
  have hU : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hI
  have hK : IsCompact (tsupport ζ) := hζc
  have hKt : IsClosed (Prod.snd '' tsupport ζ) := (hK.image continuous_snd).isClosed
  rw [continuous_iff_continuousAt]
  rintro ⟨x, s, t⟩
  by_cases ht : t ∈ I
  · have hq : ((x, t) : ℝ × ℝ) ∈ (univ ×ˢ I : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
    have hg : ContinuousAt (fun w : ℝ × ℝ × ℝ => ((w.1, w.2.2) : ℝ × ℝ)) (x, s, t) := by
      fun_prop
    have hhc : ContinuousAt h (x, t) := hh.continuousAt (hU.mem_nhds hq)
    have hFc : ContinuousAt (fun q : ℝ × ℝ => F q.1 q.2) (x, t) :=
      hFs.continuousOn.continuousAt (hU.mem_nhds hq)
    have h1 := hhc.comp (x := (x, s, t)) hg
    have h2 := hFc.comp (x := (x, s, t)) hg
    refine h1.mul (hφ.continuousAt.comp (x := (x, s, t)) ?_)
    refine ContinuousAt.prodMk ?_ (by fun_prop)
    exact c13w_aux_continuous_pt.continuousAt.comp (x := (x, s, t))
      ((continuous_fst.continuousAt).prodMk (h2.add (by fun_prop)))
  · have htK : t ∉ Prod.snd '' tsupport ζ := fun ⟨p, hp, hpt⟩ => ht (hpt ▸ (hζs hp).2)
    have hev : ∀ᶠ w : ℝ × ℝ × ℝ in 𝓝 (x, s, t), w.2.2 ∉ Prod.snd '' tsupport ζ :=
      (continuous_snd.comp continuous_snd).continuousAt.eventually
        (hKt.isOpen_compl.mem_nhds (x := ((Prod.snd ∘ Prod.snd) ((x, s, t) : ℝ × ℝ × ℝ))) htK)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hev] with w hw
    rw [hφ0 _ (fun hP => hw ⟨_, hP, rfl⟩), mul_zero]

theorem c13w_aux_hasDerivAt_t {I : Set ℝ} {F : ℝ → ℝ → ℝ} (hI : IsOpen I)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) (univ ×ˢ I))
    {ζ : c13_E × ℝ → ℝ} (hζ : c13_scalar_test I ζ) (x s t : ℝ) :
    HasDerivAt (fun t => ζ (c13_pt x (F x t + s), t))
      (c13w_aux_dt ζ (c13_pt x (F x t + s), t) +
        deriv (fun t => F x t) t * c13w_aux_dy ζ (c13_pt x (F x t + s), t)) t := by
  obtain ⟨hζd, hζc, hζs⟩ := hζ
  have hdiff : Differentiable ℝ ζ := hζd.differentiable (by simp)
  by_cases ht : t ∈ I
  · have hFt := (c13w_aux_Ft hI hFs).1 x t ht
    have hc : HasDerivAt (fun t' => ((c13_pt x (F x t' + s), t') : c13_E × ℝ))
        ((deriv (fun t => F x t) t • c13_pt 0 1, (1 : ℝ))) t := by
      have he : (fun t' => ((c13_pt x (F x t' + s), t') : c13_E × ℝ)) =
          fun t' => (c13_pt x s + F x t' • c13_pt 0 1, t') := by
        funext t'; rw [c13w_aux_pt_add]
      rw [he]
      exact ((hFt.smul_const (c13_pt 0 1)).const_add (c13_pt x s)).prodMk (hasDerivAt_id t)
    have := (hdiff _).hasFDerivAt.comp_hasDerivAt t hc
    refine this.congr_deriv ?_
    have hv : ((deriv (fun t => F x t) t • c13_pt 0 1, (1 : ℝ)) : c13_E × ℝ) =
        deriv (fun t => F x t) t • ((c13_pt 0 1, (0 : ℝ)) : c13_E × ℝ) + ((0 : c13_E), (1 : ℝ)) := by
      ext <;> simp
    rw [hv, map_add, map_smul, smul_eq_mul, c13w_aux_dt, c13w_aux_dy]
    ring
  · have hK : IsCompact (tsupport ζ) := hζc
    have hKt : IsClosed (Prod.snd '' tsupport ζ) := (hK.image continuous_snd).isClosed
    have htK : t ∉ Prod.snd '' tsupport ζ := fun ⟨p, hp, hpt⟩ => ht (hpt ▸ (hζs hp).2)
    have hP : (c13_pt x (F x t + s), t) ∉ tsupport ζ := fun hP => htK ⟨_, hP, rfl⟩
    obtain ⟨h1, h2⟩ := c13w_aux_dt_dy_zero hP
    rw [h1, h2, mul_zero, add_zero]
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hKt.isOpen_compl.mem_nhds htK] with t' ht'
    exact image_eq_zero_of_notMem_tsupport (fun hP => ht' ⟨_, hP, rfl⟩)

theorem c13w_aux_hasDerivAt_s {ζ : c13_E × ℝ → ℝ} (hζ : Differentiable ℝ ζ) (F : ℝ → ℝ → ℝ)
    (x s t : ℝ) :
    HasDerivAt (fun s => ζ (c13_pt x (F x t + s), t))
      (c13w_aux_dy ζ (c13_pt x (F x t + s), t)) s := by
  have hc : HasDerivAt (fun s' => ((c13_pt x (F x t + s'), t) : c13_E × ℝ))
      ((c13_pt 0 1, (0 : ℝ))) s := by
    have he : (fun s' => ((c13_pt x (F x t + s'), t) : c13_E × ℝ)) =
        fun s' => (c13_pt x (F x t) + s' • c13_pt 0 1, t) := by
      funext s'; rw [c13w_aux_pt_add']
    rw [he]
    simpa using (((hasDerivAt_id s).smul_const (c13_pt 0 1)).const_add
      (c13_pt x (F x t))).prodMk (hasDerivAt_const s t)
  exact (hζ _).hasFDerivAt.comp_hasDerivAt s hc

theorem c13w_aux_integrable_of_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [IsFiniteMeasureOnCompacts μ] {g : V → ℝ} (hg : Continuous g) (R : ℝ)
    (h : ∀ v, R < ‖v‖ → g v = 0) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall 0 R)
      (fun v hv => h v (by simpa using hv)))

/-- Blueprint: lem:c13_moving_patch_pairing.  For admissible `F` and every scalar spacetime test
`ζ`, `∫_I∫_E θ_F ∂_t ζ = -∫_I∫_ℝ F_t(x,t) ζ(x, F(x,t), t) dx dt`, both absolutely convergent. -/
theorem c13_moving_patch_pairing (I : Set ℝ) (F : ℝ → ℝ → ℝ) (hF : c13_graph_class I F)
    (ζ : c13_E × ℝ → ℝ) (hζ : c13_scalar_test I ζ) :
    IntegrableOn (fun p : c13_E × ℝ =>
      (c13_patch F p.2).indicator 1 p.1 * deriv (fun s => ζ (p.1, s)) p.2) (univ ×ˢ I) ∧
    IntegrableOn (fun q : ℝ × ℝ =>
      deriv (fun s => F q.1 s) q.2 * ζ (c13_pt q.1 (F q.1 q.2), q.2)) (univ ×ˢ I) ∧
    (∫ p in univ ×ˢ I,
      (c13_patch F p.2).indicator 1 p.1 * deriv (fun s => ζ (p.1, s)) p.2) =
      -∫ q in univ ×ˢ I, deriv (fun s => F q.1 s) q.2 * ζ (c13_pt q.1 (F q.1 q.2), q.2) := by
  obtain ⟨hI, -, hFs, -⟩ := hF
  have hζ' := hζ
  obtain ⟨hζd, hζc, hζs⟩ := hζ'
  have hdiff : Differentiable ℝ ζ := hζd.differentiable (by simp)
  have hUE : IsOpen (univ ×ˢ I : Set (c13_E × ℝ)) := isOpen_univ.prod hI
  obtain ⟨hcdt, hcdy⟩ := c13w_aux_continuous_dt_dy hζd
  obtain ⟨-, hFtc⟩ := c13w_aux_Ft hI hFs
  obtain ⟨R, hR⟩ := c13w_aux_box hFs hζc hζs
  -- vanishing off the box
  have hoff : ∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) →
      (c13_pt x (F x t + s), t) ∉ tsupport ζ := by
    intro x s t h hP
    obtain ⟨h1, h2, h3⟩ := hR x s t hP
    rcases h with h | h | h <;> linarith
  have hz0 : ∀ p, p ∉ tsupport ζ → ζ p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport hp
  have hA0 : ∀ p, p ∉ tsupport ζ → c13w_aux_dt ζ p = 0 := fun p hp => (c13w_aux_dt_dy_zero hp).1
  have hB0 : ∀ p, p ∉ tsupport ζ → c13w_aux_dy ζ p = 0 := fun p hp => (c13w_aux_dt_dy_zero hp).2
  set Ft : ℝ → ℝ → ℝ := fun x t => deriv (fun t => F x t) t with hFt
  -- the functions on ℝ³, w = (x, s, t)
  set Zt : ℝ → ℝ → ℝ → ℝ := fun x s t =>
    c13w_aux_dt ζ (c13_pt x (F x t + s), t) + Ft x t * c13w_aux_dy ζ (c13_pt x (F x t + s), t)
    with hZt
  have cont1 : ∀ {φ : c13_E × ℝ → ℝ}, Continuous φ → (∀ p ∉ tsupport ζ, φ p = 0) →
      Continuous (fun w : ℝ × ℝ × ℝ => φ (c13_pt w.1 (F w.1 w.2.2 + w.2.1), w.2.2)) := by
    intro φ hφ hφ0
    have := c13w_aux_cont hI hFs hζc hζs hφ hφ0 (h := fun _ => (1 : ℝ)) continuousOn_const
    simpa using this
  have contFt : ∀ {φ : c13_E × ℝ → ℝ}, Continuous φ → (∀ p ∉ tsupport ζ, φ p = 0) →
      Continuous (fun w : ℝ × ℝ × ℝ =>
        Ft w.1 w.2.2 * φ (c13_pt w.1 (F w.1 w.2.2 + w.2.1), w.2.2)) := by
    intro φ hφ hφ0
    exact c13w_aux_cont hI hFs hζc hζs hφ hφ0 hFtc
  have cA := cont1 hcdt hA0
  have cB := cont1 hcdy hB0
  have cZ := cont1 hζd.continuous hz0
  have cG := contFt hcdy hB0
  have cZt : Continuous (fun w : ℝ × ℝ × ℝ => Zt w.1 w.2.1 w.2.2) := cA.add cG
  have cr := contFt hζd.continuous hz0
  -- vanishing of each function off the box
  have vA : ∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) →
      c13w_aux_dt ζ (c13_pt x (F x t + s), t) = 0 := fun x s t h => hA0 _ (hoff x s t h)
  have vB : ∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) →
      c13w_aux_dy ζ (c13_pt x (F x t + s), t) = 0 := fun x s t h => hB0 _ (hoff x s t h)
  have vZ : ∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) →
      ζ (c13_pt x (F x t + s), t) = 0 := fun x s t h => hz0 _ (hoff x s t h)
  have vZt : ∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) → Zt x s t = 0 := by
    intro x s t h; simp only [hZt, vA x s t h, vB x s t h, mul_zero, add_zero]
  -- slices
  have sl_s : ∀ {g : ℝ × ℝ × ℝ → ℝ}, Continuous g →
      (∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) → g (x, s, t) = 0) →
      ∀ x t, Integrable (fun s => g (x, s, t)) := by
    intro g hg hv x t
    refine c13w_aux_integrable_of_vanish volume (hg.comp (by fun_prop)) R (fun s hs => ?_)
    exact hv x s t (Or.inr (Or.inl (by simpa [Real.norm_eq_abs] using hs)))
  have sl_t : ∀ {g : ℝ × ℝ × ℝ → ℝ}, Continuous g →
      (∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) → g (x, s, t) = 0) →
      ∀ x s, Integrable (fun t => g (x, s, t)) := by
    intro g hg hv x s
    refine c13w_aux_integrable_of_vanish volume (hg.comp (by fun_prop)) R (fun t ht => ?_)
    exact hv x s t (Or.inr (Or.inr (by simpa [Real.norm_eq_abs] using ht)))
  have sl_ts : ∀ {g : ℝ × ℝ × ℝ → ℝ}, Continuous g →
      (∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) → g (x, s, t) = 0) →
      ∀ x, Integrable (fun ts : ℝ × ℝ => g (x, ts.2, ts.1)) := by
    intro g hg hv x
    refine c13w_aux_integrable_of_vanish volume (hg.comp (by fun_prop)) R (fun ts hts => ?_)
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, lt_max_iff] at hts
    rcases hts with h | h
    · exact hv x _ _ (Or.inr (Or.inr h))
    · exact hv x _ _ (Or.inr (Or.inl h))
  have sl_xt : ∀ {g : ℝ × ℝ × ℝ → ℝ}, Continuous g →
      (∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) → g (x, s, t) = 0) →
      Integrable (fun q : ℝ × ℝ => g (q.1, 0, q.2)) := by
    intro g hg hv
    refine c13w_aux_integrable_of_vanish volume (hg.comp (by fun_prop)) R (fun q hq => ?_)
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, lt_max_iff] at hq
    rcases hq with h | h
    · exact hv _ _ _ (Or.inl h)
    · exact hv _ _ _ (Or.inr (Or.inr h))
  -- the right-hand side integrand
  set r : ℝ × ℝ → ℝ := fun q => deriv (fun s => F q.1 s) q.2 * ζ (c13_pt q.1 (F q.1 q.2), q.2)
    with hr
  have hr_eq : r = fun q : ℝ × ℝ => Ft q.1 q.2 * ζ (c13_pt q.1 (F q.1 q.2 + 0), q.2) := by
    funext q; simp [hr, hFt]
  have vr : ∀ x s t : ℝ, (R < |x| ∨ R < |s| ∨ R < |t|) →
      Ft x t * ζ (c13_pt x (F x t + s), t) = 0 := fun x s t h => by rw [vZ x s t h, mul_zero]
  have hrint : Integrable r := by
    rw [hr_eq]; exact sl_xt (g := fun w => Ft w.1 w.2.2 * ζ (c13_pt w.1 (F w.1 w.2.2 + w.2.1), w.2.2)) cr vr
  have hr0 : ∀ q ∉ (univ ×ˢ I : Set (ℝ × ℝ)), r q = 0 := by
    intro q hq
    have hq2 : q.2 ∉ I := fun h => hq ⟨mem_univ _, h⟩
    simp only [hr]
    rw [hz0 _ (fun hP => hq2 (hζs hP).2), mul_zero]
  -- the left-hand side integrand
  set S : Set (c13_E × ℝ) := {p | p.2 ∈ I ∧ p.1 1 < F (p.1 0) p.2} with hS
  have hSm : MeasurableSet S := by
    have hco : ContinuousOn (fun p : c13_E × ℝ => ((p.1 1, F (p.1 0) p.2) : ℝ × ℝ))
        (univ ×ˢ I) := by
      refine ContinuousOn.prodMk (by fun_prop) ?_
      refine hFs.continuousOn.comp (Continuous.continuousOn
        (by fun_prop : Continuous (fun p : c13_E × ℝ => ((p.1 0, p.2) : ℝ × ℝ)))) ?_
      intro p hp; exact ⟨mem_univ _, hp.2⟩
    have hop := hco.isOpen_inter_preimage hUE (isOpen_lt continuous_fst continuous_snd)
    have : S = (univ ×ˢ I) ∩ (fun p : c13_E × ℝ => ((p.1 1, F (p.1 0) p.2) : ℝ × ℝ)) ⁻¹'
        {v : ℝ × ℝ | v.1 < v.2} := by
      ext p; simp [hS]
    rw [this]; exact hop.measurableSet
  set ℓ : c13_E × ℝ → ℝ := S.indicator (c13w_aux_dt ζ) with hℓ
  have hdtc : HasCompactSupport (c13w_aux_dt ζ) := by
    refine hζc.mono' (fun p hp => ?_)
    by_contra h; exact hp (hA0 p h)
  have hℓint : Integrable ℓ := (hcdt.integrable_of_hasCompactSupport hdtc).indicator hSm
  have hℓeq : ∀ p ∈ (univ ×ˢ I : Set (c13_E × ℝ)),
      (c13_patch F p.2).indicator 1 p.1 * deriv (fun s => ζ (p.1, s)) p.2 = ℓ p := by
    rintro ⟨X, t⟩ ⟨-, ht⟩
    rw [c13w_aux_deriv_dt hdiff]
    by_cases hX : X 1 < F (X 0) t
    · have h1 : X ∈ c13_patch F t := hX
      have h2 : (X, t) ∈ S := ⟨ht, hX⟩
      simp [hℓ, h1, h2]
    · have h1 : X ∉ c13_patch F t := hX
      have h2 : (X, t) ∉ S := fun h => hX h.2
      simp [hℓ, h1, h2]
  have hℓ0 : ∀ p ∉ (univ ×ˢ I : Set (c13_E × ℝ)), ℓ p = 0 := by
    intro p hp
    have : p ∉ S := fun h => hp ⟨mem_univ _, h.1⟩
    simp [hℓ, this]
  -- inner integral in `y`: translate `y = F(x,t) + s`
  have hinner : ∀ x t : ℝ, ∫ y, ℓ (c13_pt x y, t) =
      ∫ s in Iic 0, c13w_aux_dt ζ (c13_pt x (F x t + s), t) := by
    intro x t
    by_cases ht : t ∈ I
    · have h1 : (fun y => ℓ (c13_pt x y, t)) =
          (Iio (F x t)).indicator (fun y => c13w_aux_dt ζ (c13_pt x y, t)) := by
        funext y
        by_cases hy : y < F x t
        · have : (c13_pt x y, t) ∈ S := ⟨ht, by simpa using hy⟩
          simp [hℓ, this, hy]
        · have : (c13_pt x y, t) ∉ S := fun h => hy (by simpa using h.2)
          simp [hℓ, this, hy]
      rw [h1, ← integral_add_left_eq_self _ (F x t)]
      have h2 : (fun s => (Iio (F x t)).indicator
          (fun y => c13w_aux_dt ζ (c13_pt x y, t)) (F x t + s)) =
          (Iio 0).indicator (fun s => c13w_aux_dt ζ (c13_pt x (F x t + s), t)) := by
        funext s
        by_cases hs : s < 0
        · have : F x t + s < F x t := by linarith
          simp [indicator, hs, this]
        · have : ¬ F x t + s < F x t := by linarith
          simp [indicator, hs, this]
      rw [h2, integral_indicator measurableSet_Iio, integral_Iic_eq_integral_Iio]
    · have h1 : (fun y => ℓ (c13_pt x y, t)) = fun _ => 0 := by
        funext y
        have : (c13_pt x y, t) ∉ S := fun h => ht h.1
        simp [hℓ, this]
      rw [h1, integral_zero]
      symm
      refine setIntegral_eq_zero_of_forall_eq_zero (fun s _ => hA0 _ (fun hP => ht (hζs hP).2))
  -- split `∂_t ζ = ∂_t Z - F_t ∂_s Z` and integrate the second term in `s`
  have hsplit : ∀ x t : ℝ, ∫ s in Iic 0, c13w_aux_dt ζ (c13_pt x (F x t + s), t) =
      (∫ s in Iic 0, Zt x s t) - r (x, t) := by
    intro x t
    have hG := sl_s (g := fun w => Ft w.1 w.2.2 *
      c13w_aux_dy ζ (c13_pt w.1 (F w.1 w.2.2 + w.2.1), w.2.2)) cG
      (fun x s t h => by simp only [vB x s t h, mul_zero]) x t
    have hZti := sl_s (g := fun w => Zt w.1 w.2.1 w.2.2) cZt vZt x t
    dsimp only at hG hZti
    have heq : (fun s => c13w_aux_dt ζ (c13_pt x (F x t + s), t)) =
        fun s => Zt x s t - Ft x t * c13w_aux_dy ζ (c13_pt x (F x t + s), t) := by
      funext s; simp only [hZt]; ring
    rw [heq, integral_sub hZti.integrableOn hG.integrableOn, integral_const_mul]
    have hB := sl_s (g := fun w => c13w_aux_dy ζ (c13_pt w.1 (F w.1 w.2.2 + w.2.1), w.2.2))
      cB vB x t
    dsimp only at hB
    have hftc := integral_Iic_of_hasDerivAt_of_tendsto (a := 0) (m := 0)
      (f := fun s => ζ (c13_pt x (F x t + s), t))
      (c13w_aux_hasDerivAt_s hdiff F x 0 t).continuousAt.continuousWithinAt
      (fun s _ => c13w_aux_hasDerivAt_s hdiff F x s t) hB.integrableOn
      (by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_le_atBot (-R - 1)] with s hs
        exact (vZ x s t (Or.inr (Or.inl
          (lt_of_lt_of_le (by linarith) (neg_le_abs s))))).symm)
    rw [hftc]
    simp [hr, hFt]
  -- per-`x` time integral
  have hxint : ∀ x : ℝ, ∫ t, ((∫ s in Iic 0, Zt x s t) - r (x, t)) = -∫ t, r (x, t) := by
    intro x
    have hfi : Integrable (fun ts : ℝ × ℝ => Zt x ts.2 ts.1)
        (volume.prod (volume.restrict (Iic (0 : ℝ)))) := by
      have := (sl_ts (g := fun w => Zt w.1 w.2.1 w.2.2) cZt vZt x).integrableOn
        (s := univ ×ˢ Iic (0 : ℝ))
      rwa [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
        Measure.restrict_univ] at this
    have hrx : Integrable (fun t => r (x, t)) := by
      have h := sl_t (g := fun w => Ft w.1 w.2.2 *
        ζ (c13_pt w.1 (F w.1 w.2.2 + w.2.1), w.2.2)) cr vr x 0
      refine h.congr (Eventually.of_forall fun t => ?_)
      simp [hr, hFt]
    rw [integral_sub hfi.integral_prod_left hrx]
    have h0 : ∫ t, ∫ s in Iic 0, Zt x s t = 0 := by
      rw [integral_integral_swap (f := fun t s => Zt x s t) hfi]
      refine setIntegral_eq_zero_of_forall_eq_zero (fun s _ => ?_)
      have := integral_of_hasDerivAt_of_tendsto (m := 0) (n := 0)
        (f := fun t => ζ (c13_pt x (F x t + s), t))
        (fun t => c13w_aux_hasDerivAt_t hI hFs hζ x s t)
        (sl_t (g := fun w => Zt w.1 w.2.1 w.2.2) cZt vZt x s)
        (by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_le_atBot (-R - 1)] with t ht
          exact (vZ x s t (Or.inr (Or.inr
            (lt_of_lt_of_le (by linarith) (neg_le_abs t))))).symm)
        (by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop (R + 1)] with t ht
          exact (vZ x s t (Or.inr (Or.inr
            (lt_of_lt_of_le (by linarith) (le_abs_self t))))).symm)
      simpa using this
    rw [h0, zero_sub]
  -- assemble
  have hℓw := c13w_aux_integrable_coord hℓint
  have hmain : (∫ p in univ ×ˢ I,
      (c13_patch F p.2).indicator 1 p.1 * deriv (fun s => ζ (p.1, s)) p.2) = -∫ q, r q := by
    rw [setIntegral_congr_fun hUE.measurableSet hℓeq,
      setIntegral_eq_integral_of_forall_compl_eq_zero hℓ0, c13w_aux_integral_coord]
    rw [Measure.volume_eq_prod] at hℓw ⊢
    rw [integral_prod _ hℓw]
    have h1 : ∀ᵐ x : ℝ, ∫ ty : ℝ × ℝ, ℓ (c13_pt (x, ty).1 (x, ty).2.2, (x, ty).2.1) =
        -∫ t, r (x, t) := by
      filter_upwards [hℓw.prod_right_ae] with x hx
      rw [Measure.volume_eq_prod] at hx
      rw [Measure.volume_eq_prod, integral_prod _ hx]
      simp only
      rw [← hxint x]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [hinner x t, hsplit x t]
    rw [integral_congr_ae h1, integral_neg, Measure.volume_eq_prod,
      ← integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hrint)]
  refine ⟨hℓint.integrableOn.congr_fun (fun p hp => (hℓeq p hp).symm) hUE.measurableSet,
    hrint.integrableOn, ?_⟩
  rw [hmain, setIntegral_eq_integral_of_forall_compl_eq_zero hr0]

/-- Blueprint: lem:c13_trace_tests.  (1) Every `ψ ∈ C_c^∞(ℝ × I)` (smooth on `ℝ × ℝ`, compact
support, `tsupport ψ ⊆ univ ×ˢ I`) is the graph trace `ζ(x, F(x,t), t)` of a scalar spacetime
test `ζ`.  (2) Consequently, a function `r` continuous on `ℝ × I` whose pairing on `ℝ × I` with
the graph trace of every scalar spacetime test vanishes is zero at every point of `ℝ × I`. -/
theorem c13_trace_tests (I : Set ℝ) (F : ℝ → ℝ → ℝ) (hF : c13_graph_class I F) :
    (∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ univ ×ˢ I →
      ∃ ζ : c13_E × ℝ → ℝ, c13_scalar_test I ζ ∧
        ∀ x t : ℝ, ζ (c13_pt x (F x t), t) = ψ (x, t)) ∧
    (∀ r : ℝ × ℝ → ℝ, ContinuousOn r (univ ×ˢ I) →
      (∀ ζ : c13_E × ℝ → ℝ, c13_scalar_test I ζ →
        (∫ q in univ ×ˢ I, r q * ζ (c13_pt q.1 (F q.1 q.2), q.2)) = 0) →
      ∀ x : ℝ, ∀ t ∈ I, r (x, t) = 0) := by
  refine ⟨fun ψ hψ hψc hψs => c13w_aux_lift I F hF ψ hψ hψc hψs, ?_⟩
  intro r hr h x t ht
  have hU : IsOpen (univ ×ˢ I : Set (ℝ × ℝ)) := isOpen_univ.prod hF.1
  refine c13w_aux_eq_zero_of_ae hU hr ?_ (x, t) ⟨mem_univ _, ht⟩
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hr.locallyIntegrableOn hU.measurableSet) ?_
  intro ψ hψ hψc hψs
  obtain ⟨ζ, hζ, htr⟩ := c13w_aux_lift I F hF ψ hψ hψc hψs
  have h1 := h ζ hζ
  simp only [htr] at h1
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := univ ×ˢ I)]
  · rw [← h1]
    refine setIntegral_congr_fun hU.measurableSet (fun q _ => ?_)
    simp [smul_eq_mul, mul_comm]
  · intro q hq
    have : ψ q = 0 := image_eq_zero_of_notMem_tsupport (fun h => hq (hψs h))
    simp [this]


end GSQG
