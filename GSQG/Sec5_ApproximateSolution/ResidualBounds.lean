import GSQG.Definitions
import GSQG.Sec4_Analysis.Equation
import GSQG.AppendixAB.Statements
import GSQG.Sec5_ApproximateSolution.FamilyAndE1toE4
import GSQG.Sec3_FixedPoint.FixedPointArgument
import GSQG.Sec5_ApproximateSolution.E5
import GSQG.Sec5_ApproximateSolution.E6toE9

/-!
# §5: residual bounds (blueprint ch. 07) for `y ≤ -8R` and `|y| ≤ 8R`, and the assembly of
thm:fixed_point_approximation

Conventions of this file.

* The parameters `p, β` are those of `GSQG.parameters` (`P.p`, `P.β = beta P.p`); results that the
  blueprint states for a general `p` (e.g. `0 < p < 1`) take a bare `p` with these hypotheses.
* **Standing choices of `R, ε₀, δ`.**  The blueprint fixes `δ ∈ (0, |μ_*|/2]`, a small `ε₀ ∈ (0,1]`
  and a large `R ≥ R₀` (chosen in chapter 04, possibly modified later).  Statements about the
  family `f̄_{ε,μ} = approximate_solution_family p R ε μ` are therefore written as
  `∀ δ, 0 < δ → δ ≤ ‖μ_*‖/2 → ∃ R₀ ε₀, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R ≥ R₀, ∃ C > 0,
   ∀ ε ∈ [0,ε₀], ∀ μ ∈ B̄(μ_*,δ), …`
  ("admissible" constants depend on `p, R, δ` and the fixed cutoffs, never on `ε, μ, y`).
* The chapter-local objects of def:c07_divided_residual that coincide with shared objects are the
  shared ones (`GSQG/Definitions`): `S_f = c01_secant`, `ℒ₀ = L0`, `𝒬_ε = c01_Q_eps`, `W = corner`.  The divided residual
  `ℰ̃_ε(f) := A_ε(f') ℰ_ε(f)` is defined here (`c07_divided_residual`) exactly as in the chapter;
  lem:c07_divided_residual_identity shows it equals the shared `c01_quasilinear_residual = ℒ₀ + 𝒬_ε`.
* `C^k([-M,M])` norms on the right of estimates are `c07_CkNorm`; norms on the *left* of an
  estimate `‖u‖_{C^k([-M,M])} ≤ X` are written pointwise (`|∂^i u(y)| ≤ X` for `i ≤ k`,
  `|y| ≤ M`), which is equivalent up to the factor `k+1` absorbed in the constant and avoids
  junk values.  Convergence in `C^k_loc` is `c07_TendstoCkLoc` (uniform convergence of all
  derivatives of order `≤ k` on every `[-M,M]`).
* `Y_γ` estimates are stated with the `ℝ≥0∞`-valued norm `Y_gamma_norm` (so they also imply
  finiteness).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal Topology

noncomputable section

namespace GSQG

/-! ### Auxiliary objects of the standing conventions -/

/-- Blueprint: chapter 07 standing conventions.  `θ = 1/p - β = (1-p)/(2p)`. -/
def c07_theta (p : ℝ) : ℝ := 1 / p - beta p

/-- Blueprint: chapter 07 standing conventions.  The fixed even cutoff `χ ∈ C_c^∞((-1/2,1/2))`,
`0 ≤ χ ≤ 1`, `χ = 1` on `[-1/4,1/4]`; explicitly `χ(x) = smoothTransition((7 - 16|x|)/3)`
(support in `[-7/16, 7/16]`, smooth since it is constant near `0`). -/
def c07_chi (x : ℝ) : ℝ := Real.smoothTransition ((7 - 16 * |x|) / 3)

/-- Blueprint: chapter 07 standing conventions.
`‖u‖_{C^k([-M,M])} = ∑_{i ≤ k} sup_{|y| ≤ M} |u^{(i)}(y)|`. -/
def c07_CkNorm (k : ℕ) (M : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), sSup ((fun y => |iteratedDeriv i u y|) '' Icc (-M) M)

/-- Blueprint: chapter 07 standing conventions.  `‖u‖_{L^∞(ℝ)} = sup_y |u(y)|`
(for bounded continuous `u`). -/
def c07_supNorm (u : ℝ → ℝ) : ℝ := sSup (range fun y => |u y|)

/-- Blueprint: chapter 07 standing conventions.  `u_n → v` in `C^k_loc` along the filter `l`:
for every `i ≤ k` and `M > 0`, `∂^i u_n → ∂^i v` uniformly on `[-M,M]`.  (With `l = atTop` this
is convergence of sequences; with `l = 𝓝[B̄] μ` it is continuity at `μ` of a map into `C^k_loc`.) -/
def c07_TendstoCkLoc {ι : Type*} (k : ℕ) (u : ι → ℝ → ℝ) (l : Filter ι) (v : ℝ → ℝ) : Prop :=
  ∀ i ≤ k, ∀ M : ℝ, 0 < M →
    TendstoUniformlyOn (fun n => iteratedDeriv i (u n)) (iteratedDeriv i v) l (Icc (-M) M)

/-! ### Chapter-local definitions -/

/-- Blueprint: def:c07_divided_residual (item 4).  The divided residual
`ℰ̃_ε(f) = A_ε(f') ℰ_ε(f)`.  (Items 1, 2, 3, 5 of the node are the shared objects `c01_secant`,
`L0`, `c01_Q_eps`, `corner`.) -/
def c07_divided_residual (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  A_eps p ε (deriv f y) * residual p ε f y

/-- Blueprint: def:c07_kernel_operator.  The secant kernel operator
`𝒯_Γ(f)(y) = c_α ∫ (f'(y) - f'(y-s))/|s|^α · Γ(S_f(y,y-s)) ds`. -/
def c07_kernel_operator (p : ℝ) (Γ : ℝ → ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ s, (deriv f y - deriv f (y - s)) / |s| ^ (p + 1) * Γ (c01_secant f y (y - s))

/-- Blueprint: def:c07_kernel_operator.  `‖Γ‖_K = sup_{|u| ≤ K} (|Γ(u)| + |Γ'(u)|)`. -/
def c07_kernel_operator_norm (Γ : ℝ → ℝ) (K : ℝ) : ℝ :=
  sSup ((fun u => |Γ u| + |deriv Γ u|) '' Icc (-K) K)

/-- Blueprint: def:c07_profile_class.  `𝒫(K)`: `f ∈ C³` with `|f'| ≤ K`,
`|f''(y)| ≤ K⟨y⟩^θ` (`y ≥ 0`), `|f''(y)| ≤ K⟨y⟩^{-1}` (`y ≤ 0`), `|f'''(y)| ≤ K⟨y⟩^{2/p}`. -/
def c07_profile_class (p K : ℝ) : Set (ℝ → ℝ) :=
  {f | ContDiff ℝ 3 f ∧ ∀ y : ℝ,
    |deriv f y| ≤ K ∧
    (0 ≤ y → |iteratedDeriv 2 f y| ≤ K * jb y ^ c07_theta p) ∧
    (y ≤ 0 → |iteratedDeriv 2 f y| ≤ K * jb y ^ (-1 : ℝ)) ∧
    |iteratedDeriv 3 f y| ≤ K * jb y ^ (2 / p)}

/-! ### Auxiliary lemmas (not blueprint nodes) -/

/-- `|y| ≤ ⟨y⟩`. -/
theorem c07_aux_abs_le_jb (y : ℝ) : |y| ≤ jb y :=
  Real.abs_le_sqrt (by linarith)

/-- `⟨y⟩^{-a} → 0` as `y → ±∞` for `a > 0`. -/
theorem c07_aux_jb_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun y => jb y ^ (-a)) atTop (𝓝 0) ∧ Tendsto (fun y => jb y ^ (-a)) atBot (𝓝 0) := by
  have h1 : Tendsto jb atTop atTop :=
    tendsto_atTop_mono c07_aux_abs_le_jb tendsto_abs_atTop_atTop
  have h2 : Tendsto jb atBot atTop :=
    tendsto_atTop_mono c07_aux_abs_le_jb tendsto_abs_atBot_atTop
  exact ⟨(tendsto_rpow_neg_atTop ha).comp h1, (tendsto_rpow_neg_atTop ha).comp h2⟩

/-- A compact subset of `ℝ` lies in some `[-M,M]` with `M > 0`. -/
theorem c07_aux_compact_subset_Icc (K : Set ℝ) (hK : IsCompact K) :
    ∃ M : ℝ, 0 < M ∧ K ⊆ Icc (-M) M := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hK.isBounded
  refine ⟨max r 1, by positivity, fun x hx => ?_⟩
  have := hr hx
  rw [Real.closedBall_eq_Icc] at this
  constructor <;> linarith [this.1, this.2, le_max_left r 1]

/-- Restricting a uniform convergence on `S` to a subset `K` and to a finer filter. -/
theorem c07_aux_TUO_restrict {F : ℂ → ℝ → ℝ} {f : ℝ → ℝ} {l l' : Filter ℂ} (hl : l' ≤ l)
    {K S : Set ℝ} (hKS : K ⊆ S) (h : TendstoUniformlyOn F f l S) :
    TendstoUniformlyOn F f l' K :=
  fun u hu => ((h u hu).filter_mono hl).mono fun _ hn x hx => hn x (hKS hx)

/-- `A_ε ∈ C¹` (`ε ≥ 0`). -/
theorem c07_aux_A_eps_contDiff (p ε : ℝ) (hε : 0 ≤ ε) : ContDiff ℝ 1 (A_eps p ε) := by
  unfold A_eps
  exact ContDiff.rpow_const_of_ne (by fun_prop) fun u => by positivity

/-- `𝒬_ε(f) = 𝒯_{A_ε - 1}(f)` (substitution `z = y - s`). -/
theorem c07_aux_Q_eq_kernel (p ε : ℝ) (f : ℝ → ℝ) :
    c01_Q_eps p ε f = c07_kernel_operator p (fun u => A_eps p ε u - 1) f := by
  funext y
  unfold c01_Q_eps c07_kernel_operator
  congr 1
  have := integral_sub_left_eq_self (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
    (A_eps p ε (c01_secant f y z) - 1)) volume y
  simp only [sub_sub_cancel] at this
  exact this.symm

/-- `ℒ₀ u ∈ C¹` when `u ∈ C^∞` and `|D|^p u' ∈ C¹`. -/
theorem c07_aux_L0_contDiff (p : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hfr : ContDiff ℝ 1 (fracDdy p u)) : ContDiff ℝ 1 (L0 p u) := by
  have h1 : ContDiff ℝ 1 (deriv u) := (hu.of_le (m := 1 + 1) (by simp)).deriv'
  show ContDiff ℝ 1 (fun y => fracDdy p u y + u y - y * deriv u y)
  exact (hfr.add (hu.of_le (by simp))).sub (contDiff_id.mul h1)

/-- `⟨y⟩^{-a} ≤ 1` for `a ≥ 0`. -/
theorem c07_aux_jb_rpow_neg_le_one (y a : ℝ) (ha : 0 ≤ a) : jb y ^ (-a) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_sqrt.2 (by nlinarith)) (by linarith)

/-- `‖u‖_{C^k([-M,M])} ≤ (k+1) X` from pointwise bounds `|∂^i u| ≤ X` on `[-M,M]`, `i ≤ k`. -/
theorem c07_aux_CkNorm_le (k : ℕ) (M X : ℝ) (hX : 0 ≤ X) (u : ℝ → ℝ)
    (h : ∀ i ≤ k, ∀ y ∈ Icc (-M) M, |iteratedDeriv i u y| ≤ X) :
    c07_CkNorm k M u ≤ (k + 1) * X := by
  unfold c07_CkNorm
  calc ∑ i ∈ Finset.range (k + 1), sSup ((fun y => |iteratedDeriv i u y|) '' Icc (-M) M)
      ≤ ∑ _i ∈ Finset.range (k + 1), X := by
        refine Finset.sum_le_sum fun i hi => Real.sSup_le ?_ hX
        rintro _ ⟨y, hy, rfl⟩
        exact h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) y hy
    _ = (k + 1) * X := by simp

/-- Triangle inequality for the `Y_γ` norm (differentiable summands). -/
theorem c07_aux_Ynorm_add_le (p γ : ℝ) (F G : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) :
    Y_gamma_norm p γ (fun y => F y + G y) ≤ Y_gamma_norm p γ F + Y_gamma_norm p γ G := by
  have hd : ∀ y, deriv (fun y => F y + G y) y = deriv F y + deriv G y :=
    fun y => deriv_add (hF y) (hG y)
  have hjb : ∀ y, 0 ≤ jb y := fun y => Real.sqrt_nonneg _
  have key : ∀ (w v : ℝ), 0 ≤ w → 0 ≤ v → ∀ y,
      ENNReal.ofReal (w * (‖F y + G y‖ + v * ‖deriv (fun y => F y + G y) y‖)) ≤
        ENNReal.ofReal (w * (‖F y‖ + v * ‖deriv F y‖)) +
          ENNReal.ofReal (w * (‖G y‖ + v * ‖deriv G y‖)) := by
    intro w v hw hv y
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), hd]
    apply ENNReal.ofReal_le_ofReal
    have h1 := norm_add_le (F y) (G y)
    have h2 := norm_add_le (deriv F y) (deriv G y)
    have : v * ‖deriv F y + deriv G y‖ ≤ v * ‖deriv F y‖ + v * ‖deriv G y‖ := by nlinarith
    nlinarith
  unfold Y_gamma_norm
  calc _ ≤ (essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖F y‖ + jb y ^ (-1 / p) * ‖deriv F y‖)))
          (volume.restrict (Ici 0)) +
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y ^ (-1 / p) * ‖deriv G y‖)))
          (volume.restrict (Ici 0))) +
        (essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖F y‖ + jb y * ‖deriv F y‖)))
          (volume.restrict (Iic 0)) +
        essSup (fun y => ENNReal.ofReal (jb y ^ γ * (‖G y‖ + jb y * ‖deriv G y‖)))
          (volume.restrict (Iic 0))) := by
        gcongr
        · exact (essSup_mono_ae (Eventually.of_forall fun y =>
            key _ _ (by have := hjb y; positivity) (by have := hjb y; positivity) y)).trans
            (ENNReal.essSup_add_le _ _)
        · exact (essSup_mono_ae (Eventually.of_forall fun y =>
            key _ _ (by have := hjb y; positivity) (hjb y) y)).trans
            (ENNReal.essSup_add_le _ _)
    _ = _ := by ring

/-- Uniform convergence on `[-M,M]` gives `L^∞(-R,R)` convergence (`R ≤ M`). -/
theorem c07_aux_eLpNorm_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {M R : ℝ} (hRM : R ≤ M)
    (h : TendstoUniformlyOn F f atTop (Icc (-M) M))
    (hm : ∀ k, AEStronglyMeasurable (F k - f) (volume.restrict (Ioo (-R) R))) :
    Tendsto (fun k => eLpNorm (F k - f) ∞ (volume.restrict (Ioo (-R) R))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hne
  · exact Eventually.of_forall fun _ => le_top
  have hpos : 0 < e.toReal := ENNReal.toReal_pos he.ne' hne
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h _ hpos] with k hk
  rw [eLpNorm_exponent_top (hm k)]
  refine (eLpNormEssSup_le_of_ae_bound (C := e.toReal) ?_).trans (ENNReal.ofReal_toReal hne).le
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
  have := hk x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [Real.dist_eq] at this
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_sub_comm]; exact this.le

/-- `1 ≤ ⟨y⟩`. -/
theorem c07_aux_one_le_jb (y : ℝ) : 1 ≤ jb y := Real.one_le_sqrt.2 (by nlinarith)

/-- `|y|^b ≤ 16 ⟨y⟩^b` for `|y| ≥ 1`, `-4 ≤ b ≤ 0`. -/
theorem c07_aux_abs_rpow_le_jb (y b : ℝ) (hy : 1 ≤ |y|) (hb : b ≤ 0) (hb4 : -4 ≤ b) :
    |y| ^ b ≤ 16 * jb y ^ b := by
  have hy0 : 0 < |y| := by linarith
  have hjb : 0 < jb y := lt_of_lt_of_le hy0 (c07_aux_abs_le_jb y)
  have h2 : jb y ≤ 2 * |y| := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [sq_abs y]⟩
  have h3 : (2 * |y|) ^ b ≤ jb y ^ b := Real.rpow_le_rpow_of_nonpos hjb h2 hb
  have h4 : (2 * |y|) ^ b = 2 ^ b * |y| ^ b := Real.mul_rpow (by norm_num) hy0.le
  have h5 : (2 : ℝ) ^ (-b) * 2 ^ b = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h6 : (2 : ℝ) ^ (-b) ≤ 16 := by
    calc (2 : ℝ) ^ (-b) ≤ 2 ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 16 := by norm_num
  have h7 : |y| ^ b = 2 ^ (-b) * (2 * |y|) ^ b := by
    rw [h4, ← mul_assoc, h5, one_mul]
  rw [h7]
  have h8 : 0 ≤ (2 * |y|) ^ b := Real.rpow_nonneg (by positivity) _
  have h9 : 0 ≤ jb y ^ b := Real.rpow_nonneg hjb.le _
  calc (2 : ℝ) ^ (-b) * (2 * |y|) ^ b ≤ 2 ^ (-b) * jb y ^ b :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 16 * jb y ^ b := mul_le_mul_of_nonneg_right h6 h9

/-- `|a+b+c+d+e| ≤ |a|+|b|+|c|+|d|+|e|`. -/
theorem c07_aux_abs_add5 (a b c d e : ℝ) : |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  linarith

/-- Monotonicity of `C ⟨y⟩^a` in `C` and `a`. -/
theorem c07_aux_bound_mono (C K a b y : ℝ) (hCK : C ≤ K) (hC : 0 ≤ C) (hab : a ≤ b) :
    C * jb y ^ a ≤ K * jb y ^ b :=
  mul_le_mul hCK (Real.rpow_le_rpow_of_exponent_le (c07_aux_one_le_jb y) hab)
    (Real.rpow_nonneg (by linarith [c07_aux_one_le_jb y]) _) (hC.trans hCK)

/-- Derivatives of `f + y`: `(f+y)' = f' + 1` and `∂^{k+2}(f+y) = ∂^{k+2} f`. -/
theorem c07_aux_iteratedDeriv_add_id (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (∀ y, deriv (fun z => f z + z) y = deriv f y + 1) ∧
    ∀ k : ℕ, iteratedDeriv (k + 2) (fun z => f z + z) = iteratedDeriv (k + 2) f := by
  have h1 : ∀ y, deriv (fun z => f z + z) y = deriv f y + 1 := fun y =>
    ((hf.differentiable (by simp) y).hasDerivAt.add (hasDerivAt_id' y)).deriv
  refine ⟨h1, fun k => ?_⟩
  have h2 : deriv (deriv (fun z => f z + z)) = deriv (deriv f) := by
    rw [funext h1]; funext y; exact deriv_add_const 1
  show iteratedDeriv (k + 1 + 1) _ = iteratedDeriv (k + 1 + 1) _
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', h2]

/-- `y^{-p} χ_R(y)` is smooth (`χ_R` vanishes near `(-∞,R]`). -/
theorem c07_aux_rpow_chiR_smooth (p R : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ (-p) * fam_chiR R y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge y R with hy | hy
  · have hev : (fun y : ℝ => y ^ (-p) * fam_chiR R y) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hy] with t ht
      have : t / R - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one hR]; exact (mem_Iio.1 ht).le
      simp [fam_chiR, chiPlus, Real.smoothTransition.zero_of_nonpos this]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hy0 : y ≠ 0 := by linarith
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ (-p)) y :=
      contDiffAt_rpow_const_of_ne hy0
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fam_chiR R) := by
      unfold fam_chiR chiPlus
      exact Real.smoothTransition.contDiff.comp (by fun_prop)
    exact h1.mul h2.contDiffAt
/-- `f_slow` is smooth. -/
theorem c07_aux_slow_smooth (p R ε : ℝ) (hR : 0 < R) :
    ContDiff ℝ (⊤ : ℕ∞) (fam_slow p R ε) := by
  have hg := c07_aux_rpow_chiR_smooth p R hR
  have heq : (fun y : ℝ => |y| ^ (-p) * fam_chiR R (-y)) =
      fun y => (fun y : ℝ => y ^ (-p) * fam_chiR R y) (-y) := by
    funext y
    rcases le_or_gt (-y) R with hy | hy
    · have : -y / R - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hR]; exact hy
      simp [fam_chiR, chiPlus, Real.smoothTransition.zero_of_nonpos this]
    · rw [abs_of_neg (by linarith)]
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => |y| ^ (-p) * fam_chiR R (-y)) := by
    rw [heq]; exact hg.comp contDiff_neg
  have : fam_slow p R ε = fun y => c_plus p ε * (y ^ (-p) * fam_chiR R y) +
      c_minus p ε * (|y| ^ (-p) * fam_chiR R (-y)) := by
    funext y; unfold fam_slow; ring
  rw [this]
  exact (contDiff_const.mul hg).add (contDiff_const.mul h2)

/-- Derivative of `A_ε`: `A_ε'(u) = -(p+1) ε u (1+εu²)^{-(p+1)/2-1}`. -/
theorem c07_aux_A_hasDeriv (p ε u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (A_eps p ε) (-(p + 1) * ε * u * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1)) u := by
  have ht : 0 < 1 + ε * u ^ 2 := by positivity
  have h := (((hasDerivAt_pow 2 u).const_mul ε).const_add 1).rpow_const
    (p := -(p + 1) / 2) (Or.inl ht.ne')
  unfold A_eps
  convert h using 1
  push_cast; ring

/-- Derivative of `B_ε`: `B_ε'(u) = (p+1) ε u (1+εu²)^{(p+1)/2-1}`. -/
theorem c07_aux_B_hasDeriv (p ε u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (A_eps_B p ε) ((p + 1) * ε * u * (1 + ε * u ^ 2) ^ ((p + 1) / 2 - 1)) u := by
  have ht : 0 < 1 + ε * u ^ 2 := by positivity
  have h := (((hasDerivAt_pow 2 u).const_mul ε).const_add 1).rpow_const
    (p := (p + 1) / 2) (Or.inl ht.ne')
  unfold A_eps_B
  convert h using 1
  push_cast; ring

/-- Second derivative of `A_ε`. -/
theorem c07_aux_A_hasDeriv2 (p ε u : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (deriv (A_eps p ε))
      (-(p + 1) * ε * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) +
        (p + 1) * (p + 3) * ε ^ 2 * u ^ 2 * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1)) u := by
  have hd : deriv (A_eps p ε) = fun u =>
      -(p + 1) * ε * u * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) :=
    funext fun u => (c07_aux_A_hasDeriv p ε u hε).deriv
  rw [hd]
  have ht : 0 < 1 + ε * u ^ 2 := by positivity
  have h1 := (((hasDerivAt_pow 2 u).const_mul ε).const_add 1).rpow_const
    (p := -(p + 1) / 2 - 1) (Or.inl ht.ne')
  have h2 := ((hasDerivAt_id u).const_mul (-(p + 1) * ε)).mul h1
  convert h2 using 1
  · funext x; simp only [Pi.mul_apply, id]
  · simp only [id]; push_cast; ring

/-- `Y_γ` norm bound from pointwise bounds on `[0,∞)` and `(-∞,0]`. -/
theorem c07_aux_Ynorm_le_of_pointwise (p γ : ℝ) (F : ℝ → ℝ) (A1 A2 : ℝ)
    (h1 : ∀ y, 0 ≤ y → jb y ^ γ * (|F y| + jb y ^ (-1 / p) * |deriv F y|) ≤ A1)
    (h2 : ∀ y, y ≤ 0 → jb y ^ γ * (|F y| + jb y * |deriv F y|) ≤ A2) :
    Y_gamma_norm p γ F ≤ ENNReal.ofReal A1 + ENNReal.ofReal A2 := by
  unfold Y_gamma_norm
  gcongr
  · exact essSup_le_of_ae_le _ (ae_restrict_of_forall_mem measurableSet_Ici fun y hy =>
      ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using h1 y hy))
  · exact essSup_le_of_ae_le _ (ae_restrict_of_forall_mem measurableSet_Iic fun y hy =>
      ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using h2 y hy))

/-- `‖F‖_{Y_γ} ≤ c ‖H‖_{Y_γ}` from pointwise comparison of the weights. -/
theorem c07_aux_Ynorm_le_mul (p γ : ℝ) (F H : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h1 : ∀ y, 0 ≤ y → jb y ^ γ * (|F y| + jb y ^ (-1 / p) * |deriv F y|) ≤
      c * (jb y ^ γ * (|H y| + jb y ^ (-1 / p) * |deriv H y|)))
    (h2 : ∀ y, y ≤ 0 → jb y ^ γ * (|F y| + jb y * |deriv F y|) ≤
      c * (jb y ^ γ * (|H y| + jb y * |deriv H y|))) :
    Y_gamma_norm p γ F ≤ ENNReal.ofReal c * Y_gamma_norm p γ H := by
  unfold Y_gamma_norm
  rw [mul_add, ← ENNReal.essSup_const_mul, ← ENNReal.essSup_const_mul]
  gcongr
  · refine essSup_mono_ae (ae_restrict_of_forall_mem measurableSet_Ici fun y hy => ?_)
    exact (ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using h1 y hy)).trans_eq
      (ENNReal.ofReal_mul hc)
  · refine essSup_mono_ae (ae_restrict_of_forall_mem measurableSet_Iic fun y hy => ?_)
    exact (ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using h2 y hy)).trans_eq
      (ENNReal.ofReal_mul hc)

/-- `∂_y S_f(y,z) = (f'(y) - S_f(y,z))/(y-z)` (`y ≠ z`, `f` differentiable at `y`). -/
theorem c07_aux_secant_dy (f : ℝ → ℝ) (y z : ℝ) (hyz : y ≠ z) (hd : DifferentiableAt ℝ f y) :
    HasDerivAt (fun y' => c01_secant f y' z) ((deriv f y - c01_secant f y z) / (y - z)) y := by
  have hne : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hev : (fun y' => c01_secant f y' z) =ᶠ[𝓝 y] fun y' => (f y' - f z) / (y' - z) := by
    filter_upwards [eventually_ne_nhds hyz] with y' hy'
    simp [c01_secant, hy']
  have h := (hd.hasDerivAt.sub_const (f z)).div ((hasDerivAt_id' y).sub_const z) hne
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [c01_secant, hyz, ↓reduceIte]
  field_simp

/-- `∂_z S_f(y,z) = (S_f(y,z) - f'(z))/(y-z)` (`y ≠ z`, `f` differentiable at `z`). -/
theorem c07_aux_secant_dz (f : ℝ → ℝ) (y z : ℝ) (hyz : y ≠ z) (hd : DifferentiableAt ℝ f z) :
    HasDerivAt (fun z' => c01_secant f y z') ((c01_secant f y z - deriv f z) / (y - z)) z := by
  have hne : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hev : (fun z' => c01_secant f y z') =ᶠ[𝓝 z] fun z' => (f y - f z') / (y - z') := by
    filter_upwards [eventually_ne_nhds hyz.symm] with z' hz'
    simp [c01_secant, hz'.symm]
  have h := (hd.hasDerivAt.const_sub (f y)).div ((hasDerivAt_id' z).const_sub y) hne
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [c01_secant, hyz, ↓reduceIte]
  field_simp
  ring

/-- `∂_y ∂_z S_f(y,z) = (f'(y) + f'(z) - 2S_f(y,z))/(y-z)²`. -/
theorem c07_aux_secant_dydz (f : ℝ → ℝ) (y z : ℝ) (hyz : y ≠ z) (hdy : DifferentiableAt ℝ f y)
    (hdz : DifferentiableAt ℝ f z) :
    HasDerivAt (fun y' => deriv (fun z' => c01_secant f y' z') z)
      ((deriv f y + deriv f z - 2 * c01_secant f y z) / (y - z) ^ 2) y := by
  have hne : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hev : (fun y' => deriv (fun z' => c01_secant f y' z') z) =ᶠ[𝓝 y]
      fun y' => (c01_secant f y' z - deriv f z) / (y' - z) := by
    filter_upwards [eventually_ne_nhds hyz] with y' hy'
    exact (c07_aux_secant_dz f y' z hy' hdz).deriv
  have h := ((c07_aux_secant_dy f y z hyz hdy).sub_const (deriv f z)).div
    ((hasDerivAt_id' y).sub_const z) hne
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  field_simp
  ring

/-- The corner is differentiable away from `0`. -/
theorem c07_aux_corner_diff (y : ℝ) (hy : y ≠ 0) : DifferentiableAt ℝ corner y := by
  rcases lt_or_gt_of_ne hy with h | h
  · have hev : corner =ᶠ[𝓝 y] fun x => -x := by
      filter_upwards [Iio_mem_nhds h] with x hx
      simp only [corner]; exact max_eq_left (by linarith [mem_Iio.1 hx])
    exact (differentiableAt_id.neg).congr_of_eventuallyEq hev
  · have hev : corner =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp only [corner]; exact max_eq_right (by linarith [mem_Ioi.1 hx])
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hev

/-- Products of uniformly convergent real functions with bounded limits. -/
theorem c07_aux_TUO_mul {ι : Type*} {l : Filter ι} {S : Set ℝ} {F G : ι → ℝ → ℝ}
    {f g : ℝ → ℝ} (hF : TendstoUniformlyOn F f l S) (hG : TendstoUniformlyOn G g l S) (A : ℝ)
    (hf : ∀ x ∈ S, |f x| ≤ A) (hg : ∀ x ∈ S, |g x| ≤ A) :
    TendstoUniformlyOn (fun n x => F n x * G n x) (fun x => f x * g x) l S := by
  rw [Metric.tendstoUniformlyOn_iff] at *
  intro e he
  set A' := max A 0 with hA'
  have hA0 : 0 ≤ A' := le_max_right _ _
  set η := min 1 (e / (2 * A' + 2)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η * (2 * A' + 2) ≤ e := by
    have := min_le_right 1 (e / (2 * A' + 2))
    rw [← hη] at this
    calc η * (2 * A' + 2) ≤ e / (2 * A' + 2) * (2 * A' + 2) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = e := div_mul_cancel₀ _ (by positivity)
  filter_upwards [hF η hη0, hG η hη0] with n h1 h2 x hx
  have k1 := h1 x hx; have k2 := h2 x hx
  rw [Real.dist_eq] at k1 k2 ⊢
  have hfx : |f x| ≤ A' := (hf x hx).trans (le_max_left _ _)
  have hgx : |g x| ≤ A' := (hg x hx).trans (le_max_left _ _)
  have hGx : |G n x| ≤ A' + η := by
    have := abs_sub_abs_le_abs_sub (G n x) (g x)
    rw [abs_sub_comm] at k2; linarith
  have e1 : f x * g x - F n x * G n x = (f x - F n x) * G n x + f x * (g x - G n x) := by ring
  rw [e1]
  calc |(f x - F n x) * G n x + f x * (g x - G n x)|
      ≤ |f x - F n x| * |G n x| + |f x| * |g x - G n x| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ η * (A' + η) + A' * η := by
        gcongr
    _ ≤ η * (2 * A' + 2) - η := by nlinarith
    _ < e := by linarith

/-- Post-composition with a continuous function, values in `[-K,K]`. -/
theorem c07_aux_TUO_comp {ι : Type*} {l : Filter ι} {S : Set ℝ} {F : ι → ℝ → ℝ}
    {f : ℝ → ℝ} (φ : ℝ → ℝ) (hφ : Continuous φ) (K : ℝ) (hF : TendstoUniformlyOn F f l S)
    (hFK : ∀ᶠ n in l, ∀ x ∈ S, |F n x| ≤ K) (hfK : ∀ x ∈ S, |f x| ≤ K) :
    TendstoUniformlyOn (fun n x => φ (F n x)) (fun x => φ (f x)) l S := by
  have hu := (isCompact_Icc (a := -K) (b := K)).uniformContinuousOn_of_continuous
    hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  rw [Metric.tendstoUniformlyOn_iff] at *
  intro e he
  obtain ⟨δ, hδ, hδ'⟩ := hu e he
  filter_upwards [hF δ hδ, hFK] with n h1 h2 x hx
  exact hδ' _ (abs_le.1 (hfK x hx) |> fun h => ⟨h.1, h.2⟩) _
    (abs_le.1 (h2 x hx) |> fun h => ⟨h.1, h.2⟩) (h1 x hx)

/-! ### General lemmas -/

/-- Blueprint: lem:c07_A_B_bounds.  Elementary bounds on `A_ε`, `B_ε = A_ε⁻¹` for `0 ≤ ε ≤ 1`,
and the consequences `‖A_ε - 1‖_K + ‖A_ε'‖_K ≤ CK²ε`, `‖A_ε‖_K ≤ 1 + CK²` for `K ≥ 1`. -/
theorem c07_A_B_bounds (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) 1,
      (∀ u : ℝ,
        |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 ∧
        |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| ∧
        |deriv (deriv (A_eps p ε)) u| ≤ C * ε ∧
        0 ≤ A_eps_B p ε u - 1 ∧ A_eps_B p ε u - 1 ≤ (p + 1) / 2 * ε * u ^ 2 ∧
        |deriv (A_eps_B p ε) u| ≤ (p + 1) * ε * |u|) ∧
      ∀ K : ℝ, 1 ≤ K →
        c07_kernel_operator_norm (fun u => A_eps p ε u - 1) K +
            c07_kernel_operator_norm (deriv (A_eps p ε)) K ≤ C * K ^ 2 * ε ∧
        c07_kernel_operator_norm (A_eps p ε) K ≤ 1 + C * K ^ 2 := by
  refine ⟨(p + 1) * (p + 4) + 3 * (p + 1), by positivity, fun ε hε => ?_⟩
  have hε0 := hε.1
  have hpw : ∀ u : ℝ, 1 ≤ 1 + ε * u ^ 2 := fun u => by nlinarith [sq_nonneg u]
  have hle1 : ∀ (u e : ℝ), e ≤ 0 → (1 + ε * u ^ 2) ^ e ≤ 1 := fun u e he =>
    Real.rpow_le_one_of_one_le_of_nonpos (hpw u) he
  have hnn : ∀ (u e : ℝ), 0 ≤ (1 + ε * u ^ 2) ^ e := fun u e =>
    Real.rpow_nonneg (by linarith [hpw u]) e
  -- pointwise bounds
  have hA1 : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 := by
    intro u
    have hx : 0 ≤ ε * u ^ 2 := by positivity
    have hA : A_eps p ε u ≤ 1 := hle1 u _ (by linarith)
    have hA0 : 0 < A_eps p ε u := Real.rpow_pos_of_pos (by linarith [hpw u]) _
    -- Bernoulli: (1+x)^a ≤ 1 + a x, a = (p+1)/2 ∈ [0,1]
    have hB := rpow_one_add_le_one_add_mul_self (s := ε * u ^ 2) (by linarith)
      (p := (p + 1) / 2) (by linarith) (by linarith)
    have hprod : A_eps p ε u * (1 + ε * u ^ 2) ^ ((p + 1) / 2) = 1 := by
      unfold A_eps
      rw [← Real.rpow_add (by linarith [hpw u])]
      rw [show -(p + 1) / 2 + (p + 1) / 2 = 0 by ring, Real.rpow_zero]
    rw [abs_of_nonpos (by linarith)]
    -- 1 = A·(1+x)^a ≤ A (1 + a x) ≤ A + a x
    have : 1 ≤ A_eps p ε u * (1 + (p + 1) / 2 * (ε * u ^ 2)) := by
      calc (1 : ℝ) = A_eps p ε u * (1 + ε * u ^ 2) ^ ((p + 1) / 2) := hprod.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hB hA0.le
    nlinarith
  have hA' : ∀ u, |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| := by
    intro u
    rw [(c07_aux_A_hasDeriv p ε u hε0).deriv]
    have h1 := hle1 u (-(p + 1) / 2 - 1) (by linarith)
    have h2 := hnn u (-(p + 1) / 2 - 1)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h2, abs_neg, abs_of_pos (by linarith : 0 < p + 1),
      abs_of_nonneg hε0]
    have : 0 ≤ (p + 1) * ε * |u| := by positivity
    nlinarith
  have hA'' : ∀ u, |deriv (deriv (A_eps p ε)) u| ≤ (p + 1) * (p + 4) * ε := by
    intro u
    rw [(c07_aux_A_hasDeriv2 p ε u hε0).deriv]
    have ht := hpw u
    have h1 := hle1 u (-(p + 1) / 2 - 1) (by linarith)
    have h2 := hnn u (-(p + 1) / 2 - 1)
    have h3 := hnn u (-(p + 1) / 2 - 1 - 1)
    have h4 : (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1) * (1 + ε * u ^ 2) =
        (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1) := by
      rw [Real.rpow_sub_one (by linarith), div_mul_cancel₀ _ (by linarith)]
    have h5 : ε * u ^ 2 * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1) ≤ 1 := by
      have : ε * u ^ 2 * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1) ≤
          (1 + ε * u ^ 2) * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) h3
      nlinarith
    have hx : 0 ≤ ε * u ^ 2 * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1) := by positivity
    have hX : (p + 1) * (p + 3) * ε ^ 2 * u ^ 2 * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1) =
        (p + 1) * (p + 3) * ε * (ε * u ^ 2 * (1 + ε * u ^ 2) ^ (-(p + 1) / 2 - 1 - 1)) := by ring
    have hpe : 0 ≤ (p + 1) * ε := by positivity
    have hpe3 : 0 ≤ (p + 1) * (p + 3) * ε := by positivity
    have k1 := mul_le_mul_of_nonneg_left h1 hpe
    have k2 := mul_le_mul_of_nonneg_left h5 hpe3
    have k3 := mul_nonneg hpe h2
    have k4 := mul_nonneg hpe3 hx
    rw [hX, abs_le]
    constructor <;> nlinarith
  have hB1 : ∀ u, 0 ≤ A_eps_B p ε u - 1 ∧ A_eps_B p ε u - 1 ≤ (p + 1) / 2 * ε * u ^ 2 := by
    intro u
    have hx : 0 ≤ ε * u ^ 2 := by positivity
    constructor
    · have := Real.one_le_rpow (hpw u) (by linarith : 0 ≤ (p + 1) / 2)
      unfold A_eps_B; linarith
    · have hB := rpow_one_add_le_one_add_mul_self (s := ε * u ^ 2) (by linarith)
        (p := (p + 1) / 2) (by linarith) (by linarith)
      unfold A_eps_B; linarith
  have hB' : ∀ u, |deriv (A_eps_B p ε) u| ≤ (p + 1) * ε * |u| := by
    intro u
    rw [(c07_aux_B_hasDeriv p ε u hε0).deriv]
    have h1 := hle1 u ((p + 1) / 2 - 1) (by linarith)
    have h2 := hnn u ((p + 1) / 2 - 1)
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h2, abs_of_pos (by linarith : 0 < p + 1),
      abs_of_nonneg hε0]
    have : 0 ≤ (p + 1) * ε * |u| := by positivity
    nlinarith
  refine ⟨fun u => ⟨hA1 u, hA' u, ?_, (hB1 u).1, (hB1 u).2, hB' u⟩, fun K hK => ⟨?_, ?_⟩⟩
  · exact (hA'' u).trans (by nlinarith)
  · have hdsub : deriv (fun u => A_eps p ε u - 1) = deriv (A_eps p ε) := by
      funext u; exact deriv_sub_const 1
    have hu : ∀ u ∈ Icc (-K) K, |u| ≤ K ∧ u ^ 2 ≤ K ^ 2 := fun u hu =>
      ⟨abs_le.2 ⟨hu.1, hu.2⟩, by nlinarith [hu.1, hu.2]⟩
    have n1 : c07_kernel_operator_norm (fun u => A_eps p ε u - 1) K ≤
        ((p + 1) / 2 * K ^ 2 + (p + 1) * K) * ε := by
      unfold c07_kernel_operator_norm
      refine Real.sSup_le ?_ (by positivity)
      rintro _ ⟨u, hu', rfl⟩
      rw [hdsub]
      have k0 := hA1 u; have k1 := hA' u
      obtain ⟨hu1, hu2⟩ := hu u hu'
      have k2 := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ (p + 1) / 2 * ε by positivity)
      have k3 := mul_le_mul_of_nonneg_left hu1 (show 0 ≤ (p + 1) * ε by positivity)
      dsimp only
      nlinarith
    have n2 : c07_kernel_operator_norm (deriv (A_eps p ε)) K ≤
        ((p + 1) * K + (p + 1) * (p + 4)) * ε := by
      unfold c07_kernel_operator_norm
      refine Real.sSup_le ?_ (by positivity)
      rintro _ ⟨u, hu', rfl⟩
      have k0 := hA' u; have k1 := hA'' u
      obtain ⟨hu1, hu2⟩ := hu u hu'
      have k3 := mul_le_mul_of_nonneg_left hu1 (show 0 ≤ (p + 1) * ε by positivity)
      dsimp only
      nlinarith
    have hK2 : K ≤ K ^ 2 := by nlinarith
    have hc : (p + 1) / 2 * K ^ 2 + 2 * (p + 1) * K + (p + 1) * (p + 4) ≤
        ((p + 1) * (p + 4) + 3 * (p + 1)) * K ^ 2 := by
      have h1 : (1 : ℝ) ≤ K ^ 2 := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left hK2 (by linarith : (0 : ℝ) ≤ p + 1)
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (p + 1) * (p + 4))
      have h4 : 0 ≤ (p + 1) * K ^ 2 := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hc hε0
    nlinarith
  · unfold c07_kernel_operator_norm
    refine Real.sSup_le ?_ (by positivity)
    rintro _ ⟨u, hu', rfl⟩
    have hA : |A_eps p ε u| ≤ 1 := by
      unfold A_eps
      rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith [hpw u]) _)]
      exact hle1 u _ (by linarith)
    have := hA' u
    have hu : |u| ≤ K := abs_le.2 ⟨hu'.1, hu'.2⟩
    have hK2 : K ≤ K ^ 2 := by nlinarith
    dsimp only
    have : (p + 1) * ε * |u| ≤ (p + 1) * K := by
      have := mul_le_mul hε.2 hu (abs_nonneg u) zero_le_one
      nlinarith
    have k := mul_le_mul_of_nonneg_left hK2 (by linarith : (0 : ℝ) ≤ p + 1)
    have k' : 0 ≤ ((p + 1) * (p + 4) + 2 * (p + 1)) * K ^ 2 := by positivity
    nlinarith

/-- Blueprint: lem:c07_secant_calculus.  Secant calculus for `f ∈ C¹` with bounded derivative:
`|S_f| ≤ ‖f'‖_∞`, the formulas for `∂_y S_f`, `∂_z S_f`, `∂_y∂_z S_f` (for `y ≠ z`),
`S_f(y,y-s) = ∫₀¹ f'(y-ts) dt`, `∂_y[S_f(y,y-s)] = (f'(y)-f'(y-s))/s` (`s ≠ 0`), and linearity
`S_f - S_g = S_{f-g}` (for `y ≠ z`, any `f, g`). -/
theorem c07_secant_calculus (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (L : ℝ)
    (hL : ∀ x, |deriv f x| ≤ L) :
    (∀ y z : ℝ, y ≠ z → |c01_secant f y z| ≤ L) ∧
    (∀ y z : ℝ, y ≠ z →
      HasDerivAt (fun y' => c01_secant f y' z) ((deriv f y - c01_secant f y z) / (y - z)) y) ∧
    (∀ y z : ℝ, y ≠ z →
      HasDerivAt (fun z' => c01_secant f y z') ((c01_secant f y z - deriv f z) / (y - z)) z) ∧
    (∀ y z : ℝ, y ≠ z →
      HasDerivAt (fun y' => deriv (fun z' => c01_secant f y' z') z)
        ((deriv f y + deriv f z - 2 * c01_secant f y z) / (y - z) ^ 2) y) ∧
    (∀ y s : ℝ, c01_secant f y (y - s) = ∫ t in (0 : ℝ)..1, deriv f (y - t * s)) ∧
    (∀ y s : ℝ, s ≠ 0 →
      HasDerivAt (fun y' => c01_secant f y' (y' - s)) ((deriv f y - deriv f (y - s)) / s) y) ∧
    (∀ g : ℝ → ℝ, ∀ y z : ℝ, y ≠ z →
      c01_secant f y z - c01_secant g y z = c01_secant (fun x => f x - g x) y z) := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  refine ⟨fun y z hyz => ?_, fun y z hyz => c07_aux_secant_dy f y z hyz (hd y),
    fun y z hyz => c07_aux_secant_dz f y z hyz (hd z),
    fun y z hyz => c07_aux_secant_dydz f y z hyz (hd y) (hd z), fun y s => ?_,
    fun y s hs => ?_, fun g y z hyz => ?_⟩
  · have hne : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 hyz)
    simp only [c01_secant, hyz, ↓reduceIte]
    rw [abs_div, div_le_iff₀ hne]
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun x _ => hd x)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hL x) convex_univ (mem_univ z) (mem_univ y)
    simpa [Real.norm_eq_abs] using this
  · rcases eq_or_ne s 0 with rfl | hs
    · simp [c01_secant]
    · have hne : y ≠ y - s := by intro h; apply hs; linarith
      have hc : Continuous (deriv f) := hf.continuous_deriv le_rfl
      have h1 : ∫ t in (0 : ℝ)..1, deriv f (y - t * s) =
          s⁻¹ • ∫ x in y - s * 1..y - s * 0, deriv f x := by
        simp_rw [mul_comm _ s]; exact intervalIntegral.integral_comp_sub_mul _ hs y
      have h2 : ∫ x in y - s * 1..y - s * 0, deriv f x = f (y - s * 0) - f (y - s * 1) :=
        intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) (hc.intervalIntegrable _ _)
      rw [h1, h2]
      simp only [c01_secant, hne, ↓reduceIte, sub_sub_cancel, mul_zero, sub_zero, mul_one,
        smul_eq_mul]
      field_simp
  · have heq : (fun y' => c01_secant f y' (y' - s)) = fun y' => (f y' - f (y' - s)) / s := by
      funext y'
      have hne : y' ≠ y' - s := by intro h; apply hs; linarith
      simp only [c01_secant, hne, ↓reduceIte, sub_sub_cancel]
    rw [heq]
    have h := ((hd y).hasDerivAt.sub ((hd (y - s)).hasDerivAt.comp y
      ((hasDerivAt_id' y).sub_const s))).div_const s
    exact h.congr_deriv (by simp)
  · simp only [c01_secant, hyz, ↓reduceIte]
    ring

/-- Blueprint: lem:c07_secant_calculus (last sentence: the piecewise `C¹` case `f = W`).
For the corner `W`: `|S_W| ≤ 1` and the derivative formulas hold wherever the derivatives of `W`
exist (`y, z ≠ 0`, `y ≠ z`). -/
theorem c07_secant_calculus_W :
    (∀ y z : ℝ, y ≠ z → |c01_secant corner y z| ≤ 1) ∧
    (∀ y z : ℝ, y ≠ z → y ≠ 0 →
      HasDerivAt (fun y' => c01_secant corner y' z)
        ((deriv corner y - c01_secant corner y z) / (y - z)) y) ∧
    (∀ y z : ℝ, y ≠ z → z ≠ 0 →
      HasDerivAt (fun z' => c01_secant corner y z')
        ((c01_secant corner y z - deriv corner z) / (y - z)) z) ∧
    (∀ y z : ℝ, y ≠ z → y ≠ 0 → z ≠ 0 →
      HasDerivAt (fun y' => deriv (fun z' => c01_secant corner y' z') z)
        ((deriv corner y + deriv corner z - 2 * c01_secant corner y z) / (y - z) ^ 2) y) := by
  refine ⟨fun y z hyz => ?_, fun y z hyz hy => c07_aux_secant_dy _ y z hyz (c07_aux_corner_diff y hy),
    fun y z hyz hz => c07_aux_secant_dz _ y z hyz (c07_aux_corner_diff z hz),
    fun y z hyz hy hz => c07_aux_secant_dydz _ y z hyz (c07_aux_corner_diff y hy)
      (c07_aux_corner_diff z hz)⟩
  have hne : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 hyz)
  simp only [c01_secant, hyz, ↓reduceIte]
  rw [abs_div, div_le_iff₀ hne, one_mul]
  have := abs_max_sub_max_le_abs (-y) (-z) 0
  simp only [corner]
  calc |max (-y) 0 - max (-z) 0| ≤ |-y - -z| := this
    _ = |y - z| := by rw [← abs_neg]; ring_nf

/-- Even extension: if `F` is integrable and vanishes on `(-∞,0]`, then `F(|x|)` is integrable
with integral `2 ∫ F`. -/
theorem c07_aux_abs_sym {F : ℝ → ℝ} (hF : Integrable F) (h0 : ∀ x ≤ 0, F x = 0) :
    Integrable (fun x => F |x|) ∧ ∫ x, F |x| = 2 * ∫ x, F x := by
  have heq : (fun x => F |x|) = fun x => F x + F (-x) := by
    funext x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [abs_of_neg hx, h0 x hx.le, zero_add]
    · subst hx; simp [h0 0 le_rfl]
    · rw [abs_of_pos hx, h0 (-x) (by linarith), add_zero]
  rw [heq]
  refine ⟨hF.add hF.comp_neg, ?_⟩
  rw [integral_add hF hF.comp_neg, integral_neg_eq_self]; ring

/-- `∫_{|y-z| ≥ a} |y-z|^{-q} dz = 2a^{1-q}/(q-1)` (`a > 0`, `q > 1`). -/
theorem c07_aux_far_int (a q y : ℝ) (ha : 0 < a) (hq : 1 < q) :
    Integrable ({z : ℝ | a ≤ |y - z|}.indicator (fun z => |y - z| ^ (-q))) ∧
    ∫ z, {z : ℝ | a ≤ |y - z|}.indicator (fun z => |y - z| ^ (-q)) z = 2 * (a ^ (1 - q) / (q - 1)) := by
  set F : ℝ → ℝ := (Ici a).indicator (fun t => t ^ (-q)) with hFd
  have hF : Integrable F := by
    rw [hFd, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hF0 : ∀ x ≤ 0, F x = 0 := fun x hx => by
    rw [hFd, indicator_of_notMem]; simp only [mem_Ici, not_le]; linarith
  have hFint : ∫ x, F x = a ^ (1 - q) / (q - 1) := by
    rw [hFd, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_Ioi_rpow_of_lt (by linarith) ha]
    rw [show -q + 1 = 1 - q by ring, show 1 - q = -(q - 1) by ring, div_neg, neg_div, neg_neg]
  obtain ⟨h1, h2⟩ := c07_aux_abs_sym hF hF0
  have heq : {z : ℝ | a ≤ |y - z|}.indicator (fun z => |y - z| ^ (-q)) = fun z => F |y - z| := by
    funext z
    simp only [hFd, indicator, mem_ofPred_eq, mem_Ici]
  rw [heq]
  refine ⟨h1.comp_sub_left y, ?_⟩
  rw [integral_sub_left_eq_self (fun x => F |x|), h2, hFint]

/-- `∫_{|s| ≤ b} |s|^{-p} ds = 2b^{1-p}/(1-p)` (`b > 0`, `0 < p < 1`). -/
theorem c07_aux_near_int (b p : ℝ) (hb : 0 < b) (hp : 0 < p) (hp1 : p < 1) :
    Integrable ({s : ℝ | |s| ≤ b}.indicator (fun s => |s| ^ (-p))) ∧
    ∫ s, {s : ℝ | |s| ≤ b}.indicator (fun s => |s| ^ (-p)) s = 2 * (b ^ (1 - p) / (1 - p)) := by
  set F : ℝ → ℝ := (Ioc 0 b).indicator (fun t => t ^ (-p)) with hFd
  have hii : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioc 0 b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hF : Integrable F := by
    rw [hFd, integrable_indicator_iff measurableSet_Ioc]; exact hii
  have hF0 : ∀ x ≤ 0, F x = 0 := fun x hx => by
    rw [hFd, indicator_of_notMem]; simp only [mem_Ioc, not_and, not_le]; intro h; linarith
  have hFint : ∫ x, F x = b ^ (1 - p) / (1 - p) := by
    rw [hFd, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hb.le,
      integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
    rw [show -p + 1 = 1 - p by ring, sub_zero]
  obtain ⟨h1, h2⟩ := c07_aux_abs_sym hF hF0
  have heq : {s : ℝ | |s| ≤ b}.indicator (fun s => |s| ^ (-p)) = fun s => F |s| := by
    funext s
    simp only [hFd, indicator, mem_ofPred_eq, mem_Ioc]
    rcases eq_or_ne s 0 with rfl | hs
    · simp [Real.zero_rpow (show -p ≠ 0 by linarith)]
    · have : 0 < |s| := abs_pos.2 hs
      simp [this]
  rw [heq]
  exact ⟨h1, by rw [h2, hFint]⟩

/-- `(Y/c)^r = c^{-r} Y^r` and `(cY)^r = c^r Y^r` for `Y, c > 0`. -/
theorem c07_aux_rpow_div (Y c r : ℝ) (hY : 0 ≤ Y) (hc : 0 < c) :
    (Y / c) ^ r = c ^ (-r) * Y ^ r ∧ (c * Y) ^ r = c ^ r * Y ^ r := by
  refine ⟨?_, Real.mul_rpow hc.le hY⟩
  rw [div_eq_mul_inv, Real.mul_rpow hY (inv_nonneg.2 hc.le), Real.inv_rpow hc.le,
    ← Real.rpow_neg hc.le, mul_comm]

/-- Pointwise majorant for item (1) of lem:c07_tail_integrals. -/
theorem c07_aux_tail_pt (p q y z : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 ≤ q) (hy : 0 < |y|) (hz : z ≠ 0)
    (hS : |y| / 4 ≤ |y - z|) :
    jb z ^ (-p) * |y - z| ^ (-q) ≤
      (|y| / 4) ^ (-q) * {s : ℝ | |s| ≤ 2 * |y|}.indicator (fun s => |s| ^ (-p)) z +
        2 * {z : ℝ | |y| / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + q))) z := by
  have hz0 : 0 < |z| := abs_pos.2 hz
  have hyz0 : 0 < |y - z| := lt_of_lt_of_le (by positivity) hS
  have hjb : jb z ^ (-p) ≤ |z| ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hz0 (c07_aux_abs_le_jb z) (by linarith)
  have hpos1 : 0 ≤ |y - z| ^ (-q) := Real.rpow_nonneg hyz0.le _
  have hi2 : {z : ℝ | |y| / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + q))) z =
      |y - z| ^ (-(p + q)) := indicator_of_mem hS _
  rw [hi2]
  rcases le_or_gt |z| (2 * |y|) with hz2 | hz2
  · rw [indicator_of_mem (show z ∈ {s : ℝ | |s| ≤ 2 * |y|} from hz2)]
    have h1 : |y - z| ^ (-q) ≤ (|y| / 4) ^ (-q) := by
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hS (by linarith)
    have h3 : 0 ≤ 2 * |y - z| ^ (-(p + q)) := by positivity
    calc jb z ^ (-p) * |y - z| ^ (-q) ≤ |z| ^ (-p) * (|y| / 4) ^ (-q) :=
          mul_le_mul hjb h1 hpos1 (Real.rpow_nonneg hz0.le _)
      _ ≤ _ := by linarith
  · rw [indicator_of_notMem (show z ∉ {s : ℝ | |s| ≤ 2 * |y|} by simp; linarith)]
    have htri : |y - z| ≤ |y| + |z| := abs_sub _ _
    have hle : |y - z| / 2 ≤ |z| := by linarith
    have h1 : |z| ^ (-p) ≤ (|y - z| / 2) ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    have h2 : (|y - z| / 2) ^ (-p) ≤ 2 * |y - z| ^ (-p) := by
      rw [(c07_aux_rpow_div _ 2 _ hyz0.le two_pos).1, neg_neg]
      have : (2 : ℝ) ^ p ≤ 2 := by
        calc (2 : ℝ) ^ p ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1.le
          _ = 2 := by simp
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hyz0.le _)
    have h4 : |y - z| ^ (-p) * |y - z| ^ (-q) = |y - z| ^ (-(p + q)) := by
      rw [← Real.rpow_add hyz0]; ring_nf
    have h5 : 0 ≤ (|y| / 4) ^ (-q) * 0 := by simp
    calc jb z ^ (-p) * |y - z| ^ (-q) ≤ (2 * |y - z| ^ (-p)) * |y - z| ^ (-q) :=
          mul_le_mul_of_nonneg_right (hjb.trans (h1.trans h2)) hpos1
      _ = 2 * |y - z| ^ (-(p + q)) := by rw [mul_assoc, h4]
      _ ≤ _ := by linarith

/-- Item (3) of lem:c07_tail_integrals for `a = |y| > 0`. -/
theorem c07_aux_tail_three (p q a : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 1 < q) (ha : 0 < a) :
    IntegrableOn (fun z => (a ^ (-p) + jb z ^ (-p)) * (a + z) ^ (-q)) (Ioi 0) ∧
    ∫ z in Ioi (0 : ℝ), (a ^ (-p) + jb z ^ (-p)) * (a + z) ^ (-q) ≤
      (1 + 1 / (1 - p) + 1 / (q - 1) + 1 / (p + q - 1)) * a ^ (1 - p - q) := by
  set f : ℝ → ℝ := fun z => (a ^ (-p) + jb z ^ (-p)) * (a + z) ^ (-q) with hf
  set h1 : ℝ → ℝ := fun z => (a ^ (-p) + z ^ (-p)) * a ^ (-q) with hh1
  set h2 : ℝ → ℝ := fun z => a ^ (-p) * z ^ (-q) + z ^ (-(p + q)) with hh2
  set H : ℝ → ℝ := fun z => (Ioc 0 a).indicator h1 z + (Ioi a).indicator h2 z with hH
  have hpw : ∀ u v : ℝ, a ^ u * a ^ v = a ^ (u + v) := fun u v => (Real.rpow_add ha u v).symm
  -- integrability of the pieces
  have hi1 : IntegrableOn h1 (Ioc 0 a) := by
    have : IntervalIntegrable h1 volume 0 a :=
      ((intervalIntegrable_const).add (intervalIntegral.intervalIntegrable_rpow' (by linarith))).mul_const _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1 this
  have hr1 : IntegrableOn (fun z : ℝ => z ^ (-q)) (Ioi a) := integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hr2 : IntegrableOn (fun z : ℝ => z ^ (-(p + q))) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  have hi2 : IntegrableOn h2 (Ioi a) := (hr1.const_mul _).add hr2
  have hHi : Integrable H :=
    ((integrable_indicator_iff measurableSet_Ioc).2 hi1).add
      ((integrable_indicator_iff measurableSet_Ioi).2 hi2)
  -- value of ∫ H
  have hI1 : ∫ z, (Ioc 0 a).indicator h1 z = a ^ (-q) * (a ^ (-p) * a + a ^ (1 - p) / (1 - p)) := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le ha.le, hh1,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_add intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_rpow' (by linarith)),
      intervalIntegral.integral_const, integral_rpow (Or.inl (by linarith)),
      Real.zero_rpow (by linarith)]
    rw [show -p + 1 = 1 - p by ring]; simp; ring
  have hI2 : ∫ z, (Ioi a).indicator h2 z = a ^ (-p) * (a ^ (1 - q) / (q - 1)) +
      a ^ (1 - (p + q)) / (p + q - 1) := by
    rw [integral_indicator measurableSet_Ioi, hh2, integral_add (hr1.const_mul _) hr2,
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha,
      integral_Ioi_rpow_of_lt (by linarith) ha]
    have e1 : -a ^ (-q + 1) / (-q + 1) = a ^ (1 - q) / (q - 1) := by
      rw [show -q + 1 = -(q - 1) by ring, div_neg, neg_div, neg_neg, show -(q - 1) = 1 - q by ring]
    have e2 : -a ^ (-(p + q) + 1) / (-(p + q) + 1) = a ^ (1 - (p + q)) / (p + q - 1) := by
      rw [show -(p + q) + 1 = -(p + q - 1) by ring, div_neg, neg_div, neg_neg,
        show -(p + q - 1) = 1 - (p + q) by ring]
    rw [e1, e2]
  have hIH : ∫ z, H z = (1 + 1 / (1 - p) + 1 / (q - 1) + 1 / (p + q - 1)) * a ^ (1 - p - q) := by
    rw [hH, integral_add ((integrable_indicator_iff measurableSet_Ioc).2 hi1)
      ((integrable_indicator_iff measurableSet_Ioi).2 hi2), hI1, hI2]
    have k1 : a ^ (-q) * (a ^ (-p) * a) = a ^ (1 - p - q) := by
      have : a ^ (-p) * a = a ^ (-p + 1) := by rw [Real.rpow_add ha, Real.rpow_one]
      rw [this, hpw]; ring_nf
    have k2 : a ^ (-q) * a ^ (1 - p) = a ^ (1 - p - q) := by rw [hpw]; ring_nf
    have k3 : a ^ (-p) * a ^ (1 - q) = a ^ (1 - p - q) := by rw [hpw]; ring_nf
    have k4 : a ^ (1 - (p + q)) = a ^ (1 - p - q) := by ring_nf
    have : a ^ (-q) * (a ^ (-p) * a + a ^ (1 - p) / (1 - p)) +
        (a ^ (-p) * (a ^ (1 - q) / (q - 1)) + a ^ (1 - (p + q)) / (p + q - 1)) =
        a ^ (-q) * (a ^ (-p) * a) + (a ^ (-q) * a ^ (1 - p)) / (1 - p) +
          (a ^ (-p) * a ^ (1 - q)) / (q - 1) + a ^ (1 - (p + q)) / (p + q - 1) := by ring
    rw [this, k1, k2, k3, k4]; ring
  -- pointwise bound on `Ioi 0`
  have hpt : ∀ z ∈ Ioi (0 : ℝ), f z ≤ H z := by
    intro z hz
    have hz0 : 0 < z := hz
    have hjb : jb z ^ (-p) ≤ z ^ (-p) := by
      have := Real.rpow_le_rpow_of_nonpos hz0 (by simpa [abs_of_pos hz0] using c07_aux_abs_le_jb z)
        (show -p ≤ 0 by linarith)
      exact this
    have hnn : 0 ≤ (a + z) ^ (-q) := Real.rpow_nonneg (by linarith) _
    have hap : 0 ≤ a ^ (-p) := Real.rpow_nonneg ha.le _
    have hf1 : f z ≤ (a ^ (-p) + z ^ (-p)) * (a + z) ^ (-q) :=
      mul_le_mul_of_nonneg_right (by linarith) hnn
    rcases le_or_gt z a with hza | hza
    · rw [hH]
      simp only
      rw [indicator_of_mem (show z ∈ Ioc 0 a from ⟨hz0, hza⟩),
        indicator_of_notMem (show z ∉ Ioi a by simp [hza]), add_zero]
      refine hf1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.rpow_le_rpow_of_nonpos ha (by linarith) (by linarith)
    · rw [hH]
      simp only
      rw [indicator_of_notMem (show z ∉ Ioc 0 a by simp; intro; linarith),
        indicator_of_mem (show z ∈ Ioi a from hza), zero_add]
      refine hf1.trans ?_
      have h3 : (a + z) ^ (-q) ≤ z ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos hz0 (by linarith) (by linarith)
      have h4 : z ^ (-p) * z ^ (-q) = z ^ (-(p + q)) := by
        rw [← Real.rpow_add hz0]; ring_nf
      simp only [hh2]
      rw [add_mul, ← h4]
      have := mul_le_mul_of_nonneg_left h3 hap
      have := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hz0.le (-p))
      linarith
  have hfm : Measurable f := by simp only [hf, jb]; fun_prop
  have hfi : IntegrableOn f (Ioi 0) := by
    refine Integrable.mono' hHi.integrableOn hfm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun z hz => ?_)
    have hz0 : 0 < z := hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      have : 0 ≤ jb z ^ (-p) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      have : 0 ≤ a ^ (-p) := Real.rpow_nonneg ha.le _
      have : 0 ≤ (a + z) ^ (-q) := Real.rpow_nonneg (by linarith) _
      positivity)]
    exact hpt z hz
  refine ⟨hfi, ?_⟩
  calc ∫ z in Ioi (0 : ℝ), f z ≤ ∫ z in Ioi (0 : ℝ), H z :=
        setIntegral_mono_on hfi hHi.integrableOn measurableSet_Ioi hpt
    _ = ∫ z, H z := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
        have hz' : z ≤ 0 := not_lt.1 hz
        rw [hH]; simp only
        rw [indicator_of_notMem (show z ∉ Ioc 0 a by simp; intro h; linarith),
          indicator_of_notMem (show z ∉ Ioi a by simp; linarith)]; simp
    _ = _ := hIH

/-- Properties of the cutoff `χ`. -/
theorem c07_aux_chi_props :
    (∀ x, 0 ≤ c07_chi x ∧ c07_chi x ≤ 1) ∧ (∀ x, 7 / 16 ≤ |x| → c07_chi x = 0) ∧
    (∀ x, |x| ≤ 1 / 4 → c07_chi x = 1) ∧ Continuous c07_chi := by
  refine ⟨fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith),
    fun x hx => Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith),
    Real.smoothTransition.continuous.comp (by fun_prop)⟩

/-- `0 < A_ε ≤ 1` (`ε ≥ 0`, `p > -1`). -/
theorem c07_aux_A_mem (p ε u : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) : 0 < A_eps p ε u ∧ A_eps p ε u ≤ 1 := by
  have h1 : 1 ≤ 1 + ε * u ^ 2 := by nlinarith [sq_nonneg u]
  exact ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)⟩

/-- The secant is measurable in the second variable (continuous `f`). -/
theorem c07_aux_secant_meas (f : ℝ → ℝ) (hf : Continuous f) (y : ℝ) :
    Measurable (fun z => c01_secant f y z) := by
  unfold c01_secant
  refine Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const ?_
  have := hf.measurable
  fun_prop

/-- The basic singular integral `z ↦ (f'(y)-f'(z))/|y-z|^{p+1}` is integrable for `f ∈ C²` with
bounded `f'`. -/
theorem c07_aux_D_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (L : ℝ) (hL : ∀ x, |deriv f x| ≤ L) (y : ℝ) :
    Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1)) := by
  have hd1 : ContDiff ℝ 1 (deriv f) := (hf.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hd1d : Differentiable ℝ (deriv f) := hd1.differentiable one_ne_zero
  have hdd : deriv (deriv f) = iteratedDeriv 2 f := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hc2 : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := y - 1) (b := y + 1)).exists_bound_of_continuousOn
    hc2.continuousOn
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y ⟨by linarith, by linarith⟩)
  obtain ⟨hn1, -⟩ := c07_aux_near_int 1 p one_pos hp hp1
  obtain ⟨hfar, -⟩ := c07_aux_far_int 1 (p + 1) y one_pos (by linarith)
  set H : ℝ → ℝ := fun z => M * {s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) (y - z) +
    2 * L * {z : ℝ | 1 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + 1))) z with hH
  have hHi : Integrable H := ((hn1.comp_sub_left y).const_mul M).add (hfar.const_mul _)
  have hm : Measurable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1)) := by
    have := measurable_deriv f; fun_prop
  refine hHi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  have hi1 : 0 ≤ {s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) (y - z) :=
    indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  have hi2 : 0 ≤ {z : ℝ | 1 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + 1))) z :=
    indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  rcases eq_or_ne z y with rfl | hzy
  · simp only [sub_self, zero_div, norm_zero]; positivity
  have hyz0 : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 hzy.symm)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hyz0 _), div_eq_mul_inv,
    ← Real.rpow_neg hyz0.le]
  by_cases hz : |y - z| ≤ 1
  · have hzI : z ∈ Icc (y - 1) (y + 1) := by
      rw [abs_le] at hz; constructor <;> linarith [hz.1, hz.2]
    have hmv : |deriv f y - deriv f z| ≤ M * |y - z| := by
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (C := M)
        (s := Icc (y - 1) (y + 1)) (fun x _ => hd1d x)
        (fun x hx => by rw [hdd]; exact hM x hx) (convex_Icc _ _) hzI
        (show y ∈ Icc (y - 1) (y + 1) from ⟨by linarith, by linarith⟩)
      simpa [Real.norm_eq_abs] using this
    have h3 : |y - z| * |y - z| ^ (-(p + 1)) = |y - z| ^ (-p) := by
      have : |y - z| * |y - z| ^ (-(p + 1)) = |y - z| ^ ((1:ℝ) + -(p + 1)) := by
        rw [Real.rpow_add hyz0, Real.rpow_one]
      rw [this]; ring_nf
    rw [hH]; simp only
    rw [indicator_of_mem (show y - z ∈ {s : ℝ | |s| ≤ 1} from hz)]
    calc |deriv f y - deriv f z| * |y - z| ^ (-(p + 1)) ≤ M * |y - z| * |y - z| ^ (-(p + 1)) :=
          mul_le_mul_of_nonneg_right hmv (Real.rpow_nonneg (abs_nonneg _) _)
      _ = M * |y - z| ^ (-p) := by rw [mul_assoc, h3]
      _ ≤ _ := by linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL0) hi2]
  · push_neg at hz
    rw [hH]; simp only
    rw [indicator_of_mem (show z ∈ {z : ℝ | 1 ≤ |y - z|} from hz.le)]
    have : |deriv f y - deriv f z| ≤ 2 * L := by
      have := abs_sub (deriv f y) (deriv f z); linarith [hL y, hL z]
    calc |deriv f y - deriv f z| * |y - z| ^ (-(p + 1)) ≤ 2 * L * |y - z| ^ (-(p + 1)) :=
          mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ _ := by linarith [mul_nonneg hM0 hi1]

/-- Blueprint: lem:c07_divided_residual_identity.  For `0 ≤ ε ≤ 1`, `f ∈ C²` with `f'` bounded:
the integrals defining `|D|^p f'(y)`, `𝒬_ε(f)(y)`, `𝒥̃_ε(f)(y)`, `𝒯_{A_ε}(f)(y)` converge
absolutely, `ℰ̃_ε(f) = ℒ₀(f) + 𝒬_ε(f) = f - yf' + 𝒯_{A_ε}(f)` and `ℰ_ε(f) = B_ε(f') ℰ̃_ε(f)`. -/
theorem c07_divided_residual_identity (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ε : ℝ)
    (hε : ε ∈ Icc (0 : ℝ) 1) (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hf' : ∃ L, ∀ x, |deriv f x| ≤ L)
    (y : ℝ) :
    Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1)) ∧
    Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant f y z) - 1)) ∧
    Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))) ∧
    Integrable (fun s => (deriv f y - deriv f (y - s)) / |s| ^ (p + 1) *
      A_eps p ε (c01_secant f y (y - s))) ∧
    c07_divided_residual p ε f y = L0 p f y + c01_Q_eps p ε f y ∧
    c07_divided_residual p ε f y = c01_quasilinear_residual p ε f y ∧
    c07_divided_residual p ε f y = f y - y * deriv f y + c07_kernel_operator p (A_eps p ε) f y ∧
    residual p ε f y = A_eps_B p ε (deriv f y) * c07_divided_residual p ε f y := by
  obtain ⟨L, hL⟩ := hf'
  have hD := c07_aux_D_integrable p hp hp1 f hf L hL y
  have hAm := fun u => c07_aux_A_mem p ε u hp hε.1
  have hAc : Continuous (A_eps p ε) := c04_aux_A_cont p ε hε.1
  have hmS : Measurable (fun z => c01_secant f y z) :=
    c07_aux_secant_meas f (hf.continuous) y
  have hmA : Measurable (A_eps p ε) := hAc.measurable
  set D : ℝ → ℝ := fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) with hDd
  have hmD : Measurable D := by have := measurable_deriv f; simp only [hDd]; fun_prop
  have hmul : ∀ g : ℝ → ℝ, Measurable g → (∀ z, |g z| ≤ 1) → Integrable (fun z => D z * g z) := by
    intro g hg hg1
    refine hD.mono (hmD.mul hg).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hg1 z)
  have h2 : Integrable (fun z => D z * (A_eps p ε (c01_secant f y z) - 1)) :=
    hmul _ (by fun_prop) fun z => by
      rw [abs_le]; constructor <;> linarith [(hAm (c01_secant f y z)).1, (hAm (c01_secant f y z)).2]
  have h3 : Integrable (fun z => D z * (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))) :=
    hmul _ (by fun_prop) fun z => by
      rw [abs_le]; constructor <;> linarith [(hAm (c01_secant f y z)).1, (hAm (c01_secant f y z)).2,
        (hAm (deriv f y)).1, (hAm (deriv f y)).2]
  have h4' : Integrable (fun z => D z * A_eps p ε (c01_secant f y z)) :=
    hmul _ (by fun_prop) fun z => by
      rw [abs_of_pos (hAm _).1]; exact (hAm _).2
  have h4 : Integrable (fun s => (deriv f y - deriv f (y - s)) / |s| ^ (p + 1) *
      A_eps p ε (c01_secant f y (y - s))) := by
    have := h4'.comp_sub_left y
    simpa [hDd, sub_sub_cancel] using this
  have hA0 : A_eps p ε (deriv f y) ≠ 0 := (hAm _).1.ne'
  -- `ℰ̃ = ℒ₀ + 𝒬`
  have e5 : c07_divided_residual p ε f y = L0 p f y + c01_Q_eps p ε f y := by
    unfold c07_divided_residual residual L0 J_eps c01_Q_eps fracDdy fracD
    have hJQ : (∫ z, (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
        (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y))) =
        (∫ z, (deriv f y - deriv f z) / |y - z| ^ (p + 1) * (A_eps p ε (c01_secant f y z) - 1)) +
        (1 - A_eps p ε (deriv f y)) * ∫ z, (deriv f y - deriv f z) / |y - z| ^ (p + 1) := by
      rw [← integral_const_mul, ← integral_add h2 (hD.const_mul _)]
      congr 1; funext z; ring
    rw [hJQ]
    field_simp
    ring
  have e7 : c07_kernel_operator p (A_eps p ε) f y =
      calpha p * ∫ z, D z * A_eps p ε (c01_secant f y z) := by
    unfold c07_kernel_operator
    congr 1
    have := integral_sub_left_eq_self (fun z => D z * A_eps p ε (c01_secant f y z)) volume y
    simpa [hDd, sub_sub_cancel] using this
  refine ⟨hD, h2, h3, h4, e5, e5, ?_, ?_⟩
  · rw [e5, e7]
    unfold L0 c01_Q_eps fracDdy fracD
    have : (∫ z, D z * A_eps p ε (c01_secant f y z)) =
        (∫ z, D z) + ∫ z, D z * (A_eps p ε (c01_secant f y z) - 1) := by
      rw [← integral_add hD h2]; congr 1; funext z; ring
    rw [this]; simp only [hDd]; ring
  · unfold c07_divided_residual A_eps_B
    have hB : (1 + ε * deriv f y ^ 2) ^ ((p + 1) / 2) * A_eps p ε (deriv f y) = 1 := by
      unfold A_eps
      rw [← Real.rpow_add (by nlinarith [sq_nonneg (deriv f y), hε.1])]
      rw [show (p + 1) / 2 + -(p + 1) / 2 = 0 by ring, Real.rpow_zero]
    rw [← mul_assoc, hB, one_mul]

/-- `θ = (1-p)/(2p)`. -/
theorem c07_aux_theta_eq (p : ℝ) (hp : 0 < p) : c07_theta p = (1 - p) / (2 * p) := by
  unfold c07_theta beta; field_simp; ring

/-- Bounds of `Γ`, `Γ'` on `[-K,K]` by `‖Γ‖_K`, and `‖Γ‖_K ≥ 0`. -/
theorem c07_aux_Gamma_norm (Γ : ℝ → ℝ) (hΓ : ContDiff ℝ 1 Γ) (K : ℝ) (hK : 0 ≤ K) :
    0 ≤ c07_kernel_operator_norm Γ K ∧ ∀ u ∈ Icc (-K) K,
      |Γ u| ≤ c07_kernel_operator_norm Γ K ∧ |deriv Γ u| ≤ c07_kernel_operator_norm Γ K := by
  have hc : Continuous (fun u => |Γ u| + |deriv Γ u|) :=
    hΓ.continuous.abs.add (hΓ.continuous_deriv le_rfl).abs
  have hbdd : BddAbove ((fun u => |Γ u| + |deriv Γ u|) '' Icc (-K) K) :=
    (isCompact_Icc.image_of_continuousOn hc.continuousOn).bddAbove
  have hle : ∀ u ∈ Icc (-K) K, |Γ u| + |deriv Γ u| ≤ c07_kernel_operator_norm Γ K :=
    fun u hu => le_csSup hbdd ⟨u, hu, rfl⟩
  refine ⟨(by positivity : (0:ℝ) ≤ |Γ 0| + |deriv Γ 0|).trans (hle 0 ⟨by linarith, hK⟩),
    fun u hu => ⟨?_, ?_⟩⟩
  · linarith [hle u hu, abs_nonneg (deriv Γ u)]
  · linarith [hle u hu, abs_nonneg (Γ u)]

/-- Majorant `D_e(s) = 1_{|s|≤1}|s|^{-p} + 1_{|s|≥1}|s|^{-e}`: integrable with integral
`2/(1-p) + 2/(e-1)`. -/
theorem c07_aux_kernel_majorant (p e : ℝ) (hp : 0 < p) (hp1 : p < 1) (he : 1 < e) :
    Integrable (fun s : ℝ => {s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s +
      {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-e)) s) ∧
    ∫ s, ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s +
      {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-e)) s) = 2 / (1 - p) + 2 / (e - 1) := by
  obtain ⟨hni, hnI⟩ := c07_aux_near_int 1 p one_pos hp hp1
  obtain ⟨hfi, hfI⟩ := c07_aux_far_int 1 e 0 one_pos he
  refine ⟨hni.add hfi, ?_⟩
  rw [integral_add hni hfi, hnI, hfI, Real.one_rpow, Real.one_rpow]; ring

/-- Pointwise domination of the kernel integrands of lem:c07_kernel_C1 on `|y| ≤ R`. -/
theorem c07_aux_kernel_pt (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (K R : ℝ) (hK : 1 ≤ K)
    (hR : 1 ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f ∈ c07_profile_class p K, ∀ Γ : ℝ → ℝ, ContDiff ℝ 1 Γ →
      ∀ y : ℝ, |y| ≤ R → ∀ s : ℝ,
      |(deriv f y - deriv f (y - s)) / |s| ^ (p + 1) * Γ (c01_secant f y (y - s))| ≤
        A * c07_kernel_operator_norm Γ K *
          ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s +
            {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(p + 1 - c07_theta p))) s) ∧
      |(iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (p + 1) *
          Γ (c01_secant f y (y - s)) +
        (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (p + 1)) *
          deriv Γ (c01_secant f y (y - s))| ≤
        A * c07_kernel_operator_norm Γ K *
          ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s +
            {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(p + 1 - c07_theta p))) s) := by
  have hp0 : 0 < p := by linarith
  have hθ := c07_aux_theta_eq p hp0
  set θ := c07_theta p with hθd
  have hθ0 : 0 ≤ θ := by rw [hθ]; apply div_nonneg <;> linarith
  have hθp : θ < p := by
    rw [hθ, div_lt_iff₀ (by linarith)]; nlinarith
  set e := p + 1 - θ with he
  have hjR : 1 ≤ jb (R + 1) := c07_aux_one_le_jb _
  set K2 := K * jb (R + 1) ^ θ with hK2
  set K3 := K * jb (R + 1) ^ (2 / p) with hK3
  have hK2a : K ≤ K2 := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hjR hθ0)
  have hK3a : K ≤ K3 := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hjR (by positivity))
  have hR2 : 1 ≤ (R + 2) ^ θ := Real.one_le_rpow (by linarith) hθ0
  refine ⟨K2 + K3 + K2 ^ 2 + 2 * K * (R + 2) ^ θ + 4 * K ^ 2, by positivity, ?_⟩
  intro f hf Γ hΓ y hy s
  obtain ⟨hf3, hfb⟩ := hf
  obtain ⟨hN0, hNb⟩ := c07_aux_Gamma_norm Γ hΓ K (by linarith)
  set Nn := c07_kernel_operator_norm Γ K with hNn
  have hi2 : ∀ x, iteratedDeriv 2 f x = deriv (deriv f) x := fun x => by
    simp [iteratedDeriv_succ]
  have hi3 : ∀ x, iteratedDeriv 3 f x = deriv (deriv (deriv f)) x := fun x => by
    simp [iteratedDeriv_succ]
  simp only [hi2]
  have hd1 : ContDiff ℝ 2 (deriv f) := (hf3.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hd2 : ContDiff ℝ 1 (deriv (deriv f)) := (hd1.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hfd : Differentiable ℝ f := hf3.differentiable (by norm_num)
  have hd1d : Differentiable ℝ (deriv f) := hd1.differentiable (by norm_num)
  have hd2d : Differentiable ℝ (deriv (deriv f)) := hd2.differentiable (by norm_num)
  have hf1 : ∀ x, |deriv f x| ≤ K := fun x => (hfb x).1
  have hf2 : ∀ x, |deriv (deriv f) x| ≤ K * jb x ^ θ := by
    intro x
    rcases le_total 0 x with hx | hx
    · have := (hfb x).2.1 hx; rwa [hi2] at this
    · have := (hfb x).2.2.1 hx
      rw [hi2] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      exact (Real.rpow_le_one_of_one_le_of_nonpos (c07_aux_one_le_jb x) (by norm_num)).trans
        (Real.one_le_rpow (c07_aux_one_le_jb x) hθ0)
  have hjb_mono : ∀ x, |x| ≤ R + 1 → jb x ≤ jb (R + 1) := fun x hx => by
    unfold jb
    exact Real.sqrt_le_sqrt (by nlinarith [sq_abs x, abs_nonneg x])
  have hjb0 : ∀ x, 0 ≤ jb x := fun x => Real.sqrt_nonneg _
  have hf2l : ∀ x ∈ Icc (-(R + 1)) (R + 1), |deriv (deriv f) x| ≤ K2 := fun x hx =>
    (hf2 x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hjb0 x) (hjb_mono x (abs_le.2 hx)) hθ0) (by linarith))
  have hf3l : ∀ x ∈ Icc (-(R + 1)) (R + 1), |deriv (deriv (deriv f)) x| ≤ K3 := fun x hx => by
    have := (hfb x).2.2.2; rw [hi3] at this
    exact this.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hjb0 x) (hjb_mono x (abs_le.2 hx)) (by positivity)) (by linarith))
  -- secant in `[-K,K]`
  have hS : c01_secant f y (y - s) ∈ Icc (-K) K := by
    rw [mem_Icc, ← abs_le]
    rcases eq_or_ne s 0 with rfl | hs
    · simp only [c01_secant, sub_zero, ↓reduceIte]; exact hf1 y
    · exact (c07_secant_calculus f (hf3.of_le (by norm_num)) K hf1).1 y (y - s)
        (by intro h; apply hs; linarith)
  obtain ⟨hG0, hG1⟩ := hNb _ hS
  set Sv := c01_secant f y (y - s)
  set D1 := {s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s
  set D2 := {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-e)) s
  have hD1 : 0 ≤ D1 := indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  have hD2 : 0 ≤ D2 := indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  set A := K2 + K3 + K2 ^ 2 + 2 * K * (R + 2) ^ θ + 4 * K ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hK2s : 0 ≤ K2 ^ 2 := sq_nonneg _
  have hK2p : 0 ≤ K2 := by linarith
  have hK3p : 0 ≤ K3 := by linarith
  have hRθp : 0 ≤ 2 * K * (R + 2) ^ θ := by positivity
  have hK4 : 0 ≤ 4 * K ^ 2 := by positivity
  have hK2A : K2 ≤ A := by rw [hA]; linarith
  have hK3A : K3 + K2 ^ 2 ≤ A := by rw [hA]; linarith
  have h2KA : 2 * K ≤ A := by rw [hA]; nlinarith
  have hfarA : 2 * K * (R + 2) ^ θ + 4 * K ^ 2 ≤ A := by rw [hA]; linarith
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [sub_zero, sub_self, zero_div, zero_mul, abs_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero]
    have : 0 ≤ A * Nn * (D1 + D2) := by positivity
    exact ⟨this, this⟩
  set a := |s| with ha
  have ha0 : 0 < a := abs_pos.2 hs
  set w := a ^ (p + 1) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos ha0 _
  have hsw : |s * w| = a * w := by rw [abs_mul, abs_of_pos hw0]
  rw [abs_mul, abs_div, abs_of_pos hw0]
  have habs2 : |(deriv f y - deriv f (y - s)) ^ 2 / (s * w) * deriv Γ Sv| =
      (deriv f y - deriv f (y - s)) ^ 2 / (a * w) * |deriv Γ Sv| := by
    rw [abs_mul, abs_div, hsw, abs_of_nonneg (sq_nonneg _)]
  by_cases h1 : a ≤ 1
  · -- near region
    have hD1e : D1 = a ^ (-p) := indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ 1} from h1) _
    have haw : a / w = a ^ (-p) := by
      rw [div_eq_iff hw0.ne', hw, ← Real.rpow_add ha0]; ring_nf; rw [Real.rpow_one]
    have hyI : y ∈ Icc (-(R + 1)) (R + 1) := ⟨by linarith [(abs_le.1 hy).1], by linarith [(abs_le.1 hy).2]⟩
    have hysI : y - s ∈ Icc (-(R + 1)) (R + 1) := by
      have := abs_le.1 hy; have := abs_le.1 h1
      exact ⟨by linarith, by linarith⟩
    have mv1 : |deriv f y - deriv f (y - s)| ≤ K2 * a := by
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (C := K2)
        (fun x _ => hd1d x) (fun x hx => by rw [Real.norm_eq_abs]; exact hf2l x hx) (convex_Icc _ _)
        hysI hyI
      simpa [Real.norm_eq_abs, ha] using this
    have mv2 : |deriv (deriv f) y - deriv (deriv f) (y - s)| ≤ K3 * a := by
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv f)) (C := K3)
        (fun x _ => hd2d x) (fun x hx => by rw [Real.norm_eq_abs]; exact hf3l x hx) (convex_Icc _ _)
        hysI hyI
      simpa [Real.norm_eq_abs, ha] using this
    have hap : 0 ≤ a ^ (-p) := Real.rpow_nonneg ha0.le _
    have key1 : |deriv f y - deriv f (y - s)| / w ≤ K2 * a ^ (-p) := by
      rw [← haw, mul_div_assoc']; exact div_le_div_of_nonneg_right mv1 hw0.le
    have key2 : |deriv (deriv f) y - deriv (deriv f) (y - s)| / w ≤ K3 * a ^ (-p) := by
      rw [← haw, mul_div_assoc']; exact div_le_div_of_nonneg_right mv2 hw0.le
    have key3 : (deriv f y - deriv f (y - s)) ^ 2 / (a * w) ≤ K2 ^ 2 * a ^ (-p) := by
      rw [← haw, div_le_iff₀ (by positivity)]
      have : (deriv f y - deriv f (y - s)) ^ 2 ≤ (K2 * a) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) mv1 2
      calc _ ≤ (K2 * a) ^ 2 := this
        _ = K2 ^ 2 * (a / w) * (a * w) := by field_simp
    have hAD : ∀ c, 0 ≤ c → c ≤ A → c * Nn * a ^ (-p) ≤ A * Nn * (D1 + D2) := by
      intro c hc hcA
      rw [hD1e]
      calc c * Nn * a ^ (-p) ≤ A * Nn * a ^ (-p) := by gcongr
        _ ≤ A * Nn * (a ^ (-p) + D2) := by gcongr; linarith
    have hK20 : 0 ≤ K2 := by linarith
    have hK30 : 0 ≤ K3 := by linarith
    constructor
    · calc |deriv f y - deriv f (y - s)| / w * |Γ Sv| ≤ K2 * a ^ (-p) * Nn :=
            mul_le_mul key1 hG0 (abs_nonneg _) (by positivity)
        _ = K2 * Nn * a ^ (-p) := by ring
        _ ≤ _ := hAD K2 hK20 hK2A
    · refine (abs_add_le _ _).trans ?_
      rw [habs2, abs_mul, abs_div, abs_of_pos hw0]
      calc |deriv (deriv f) y - deriv (deriv f) (y - s)| / w * |Γ Sv| +
            (deriv f y - deriv f (y - s)) ^ 2 / (a * w) * |deriv Γ Sv|
          ≤ K3 * a ^ (-p) * Nn + K2 ^ 2 * a ^ (-p) * Nn := by
            gcongr
        _ = (K3 + K2 ^ 2) * Nn * a ^ (-p) := by ring
        _ ≤ _ := hAD _ (by positivity) hK3A
  · -- far region
    push_neg at h1
    have hD2e : D2 = a ^ (-e) := by
      show {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-e)) s = a ^ (-e)
      rw [indicator_of_mem (show s ∈ {z : ℝ | 1 ≤ |0 - z|} by
        show 1 ≤ |0 - s|; rw [zero_sub, abs_neg]; exact h1.le)]
      show |0 - s| ^ (-e) = a ^ (-e)
      rw [zero_sub, abs_neg]
    have hae : 0 ≤ a ^ (-e) := Real.rpow_nonneg ha0.le _
    -- `1/w ≤ a^{-e}`, `a^θ / w = a^{-e}`, `1/(a w) ≤ a^{-e}`
    have hw_e : 1 / w ≤ a ^ (-e) := by
      rw [hw, one_div, ← Real.rpow_neg ha0.le]
      exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have hθw : a ^ θ / w = a ^ (-e) := by
      rw [div_eq_iff hw0.ne', hw, ← Real.rpow_add ha0]; congr 1; ring
    have haw_e : 1 / (a * w) ≤ a ^ (-e) := by
      calc 1 / (a * w) ≤ 1 / w := by
            apply one_div_le_one_div_of_le hw0; nlinarith
        _ ≤ _ := hw_e
    have hd1b : |deriv f y - deriv f (y - s)| ≤ 2 * K := by
      have := abs_sub (deriv f y) (deriv f (y - s)); linarith [hf1 y, hf1 (y - s)]
    have hjbs : ∀ x, |x| ≤ R + a → jb x ^ θ ≤ (R + 2) ^ θ * a ^ θ := by
      intro x hx
      rw [← Real.mul_rpow (by linarith) ha0.le]
      refine Real.rpow_le_rpow (hjb0 x) ?_ hθ0
      have hx2 : x ^ 2 ≤ (R + a) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      have hRa : R * 1 ≤ R * a := mul_le_mul_of_nonneg_left h1.le (by linarith)
      have h3 : (R + a) ^ 2 ≤ ((R + 1) * a) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith [show (R + 1) * a = R * a + a by ring]) 2
      have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ h1.le
      have ha3 : a ^ 2 ≤ (2 * R + 3) * a ^ 2 := le_mul_of_one_le_left (by positivity) (by linarith)
      have e1 : ((R + 2) * a) ^ 2 = ((R + 1) * a) ^ 2 + (2 * R + 3) * a ^ 2 := by ring
      have hpos : 0 ≤ (R + 2) * a := by positivity
      calc jb x = Real.sqrt (1 + x ^ 2) := rfl
        _ ≤ Real.sqrt (((R + 2) * a) ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = (R + 2) * a := Real.sqrt_sq hpos
    have hd2b : |deriv (deriv f) y - deriv (deriv f) (y - s)| ≤ 2 * K * (R + 2) ^ θ * a ^ θ := by
      have h1' := (hf2 y).trans (mul_le_mul_of_nonneg_left (hjbs y (by linarith)) (by linarith))
      have h2' := (hf2 (y - s)).trans (mul_le_mul_of_nonneg_left (hjbs (y - s) (by
        have := abs_sub y s; rw [← ha] at this; linarith)) (by linarith))
      have := abs_sub (deriv (deriv f) y) (deriv (deriv f) (y - s))
      linarith
    have key1 : |deriv f y - deriv f (y - s)| / w ≤ 2 * K * a ^ (-e) := by
      calc _ = |deriv f y - deriv f (y - s)| * (1 / w) := by ring
        _ ≤ 2 * K * a ^ (-e) := mul_le_mul hd1b hw_e (by positivity) (by linarith)
    have key2 : |deriv (deriv f) y - deriv (deriv f) (y - s)| / w ≤
        2 * K * (R + 2) ^ θ * a ^ (-e) := by
      rw [← hθw, mul_div_assoc']; exact div_le_div_of_nonneg_right hd2b hw0.le
    have key3 : (deriv f y - deriv f (y - s)) ^ 2 / (a * w) ≤ 4 * K ^ 2 * a ^ (-e) := by
      have : (deriv f y - deriv f (y - s)) ^ 2 ≤ 4 * K ^ 2 := by
        rw [← sq_abs]
        calc |deriv f y - deriv f (y - s)| ^ 2 ≤ (2 * K) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) hd1b 2
          _ = 4 * K ^ 2 := by ring
      calc _ = (deriv f y - deriv f (y - s)) ^ 2 * (1 / (a * w)) := by ring
        _ ≤ 4 * K ^ 2 * a ^ (-e) :=
          mul_le_mul this haw_e (one_div_pos.2 (mul_pos ha0 hw0)).le hK4
    have hAD : ∀ c, 0 ≤ c → c ≤ A → c * Nn * a ^ (-e) ≤ A * Nn * (D1 + D2) := by
      intro c hc hcA
      rw [hD2e]
      calc c * Nn * a ^ (-e) ≤ A * Nn * a ^ (-e) := by gcongr
        _ ≤ A * Nn * (D1 + a ^ (-e)) := by gcongr; linarith
    constructor
    · calc |deriv f y - deriv f (y - s)| / w * |Γ Sv| ≤ 2 * K * a ^ (-e) * Nn :=
            mul_le_mul key1 hG0 (abs_nonneg _) (by positivity)
        _ = 2 * K * Nn * a ^ (-e) := by ring
        _ ≤ _ := hAD _ (by positivity) h2KA
    · refine (abs_add_le _ _).trans ?_
      rw [habs2, abs_mul, abs_div, abs_of_pos hw0]
      calc |deriv (deriv f) y - deriv (deriv f) (y - s)| / w * |Γ Sv| +
            (deriv f y - deriv f (y - s)) ^ 2 / (a * w) * |deriv Γ Sv|
          ≤ 2 * K * (R + 2) ^ θ * a ^ (-e) * Nn + 4 * K ^ 2 * a ^ (-e) * Nn := by
            gcongr
        _ = (2 * K * (R + 2) ^ θ + 4 * K ^ 2) * Nn * a ^ (-e) := by ring
        _ ≤ _ := hAD _ (by positivity) hfarA

/-- Part 1 of lem:c07_kernel_C1 for a fixed `f ∈ 𝒫(K)` and `Γ ∈ C¹`. -/
theorem c07_aux_kernel_C1_main (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) (K : ℝ) (hK : 1 ≤ K)
    (f : ℝ → ℝ) (hf : f ∈ c07_profile_class p K) (Γ : ℝ → ℝ) (hΓ : ContDiff ℝ 1 Γ) :
      (∀ y : ℝ, Integrable (fun s => (deriv f y - deriv f (y - s)) / |s| ^ (p + 1) *
        Γ (c01_secant f y (y - s)))) ∧
      ContDiff ℝ 1 (c07_kernel_operator p Γ f) ∧
      ∀ y : ℝ,
        Integrable (fun s =>
          (iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (p + 1) *
              Γ (c01_secant f y (y - s)) +
            (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (p + 1)) *
              deriv Γ (c01_secant f y (y - s))) ∧
        HasDerivAt (c07_kernel_operator p Γ f)
          (calpha p * ∫ s,
            ((iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (p + 1) *
                Γ (c01_secant f y (y - s)) +
              (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (p + 1)) *
                deriv Γ (c01_secant f y (y - s)))) y := by
  have hp0 : 0 < p := by linarith
  have hθ := c07_aux_theta_eq p hp0
  have he : 1 < p + 1 - c07_theta p := by
    rw [hθ]; have : (1 - p) / (2 * p) < p := by rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  obtain ⟨hDi, -⟩ := c07_aux_kernel_majorant p (p + 1 - c07_theta p) hp0 hp1 he
  set D : ℝ → ℝ := fun s => {s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s +
      {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(p + 1 - c07_theta p))) s with hD
  set Nn := c07_kernel_operator_norm Γ K
  have hf3 := hf.1
  have hi2 : ∀ x, iteratedDeriv 2 f x = deriv (deriv f) x := fun x => by
    simp [iteratedDeriv_succ]
  have hd1 : ContDiff ℝ 2 (deriv f) := (hf3.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hd2 : ContDiff ℝ 1 (deriv (deriv f)) := (hd1.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hfc : Continuous f := hf3.continuous
  have hd1c : Continuous (deriv f) := hd1.continuous
  have hd2c : Continuous (deriv (deriv f)) := hd2.continuous
  have hd1d : Differentiable ℝ (deriv f) := hd1.differentiable (by norm_num)
  have hΓc : Continuous Γ := hΓ.continuous
  have hΓ'c : Continuous (deriv Γ) := hΓ.continuous_deriv le_rfl
  have hΓd : Differentiable ℝ Γ := hΓ.differentiable (by norm_num)
  have hsec := c07_secant_calculus f (hf3.of_le (by norm_num)) K (fun x => (hf.2 x).1)
  have hdiff : ∀ s, s ≠ 0 → ∀ y, HasDerivAt (fun y' => (deriv f y' - deriv f (y' - s)) / |s| ^ (p + 1) *
      Γ (c01_secant f y' (y' - s)))
      ((iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (p + 1) * Γ (c01_secant f y (y - s)) +
      (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (p + 1)) * deriv Γ (c01_secant f y (y - s))) y := by
    intro s hs y
    have hS := hsec.2.2.2.2.2.1 y s hs
    have hw : |s| ^ (p + 1) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.2 hs) _).ne'
    have a := ((hd1d y).hasDerivAt.sub ((hd1d (y - s)).hasDerivAt.comp y
      ((hasDerivAt_id' y).sub_const s))).div_const (|s| ^ (p + 1))
    have b := HasDerivAt.comp (h₂ := Γ) y (hΓd _).hasDerivAt hS
    refine (a.mul b).congr_deriv ?_
    rw [hi2, hi2]
    simp only [mul_one, Function.comp, Pi.sub_apply]
    field_simp
  have hk1c : ∀ s, s ≠ 0 → Continuous (fun y => ((iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (p + 1) * Γ (c01_secant f y (y - s)) +
      (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (p + 1)) * deriv Γ (c01_secant f y (y - s)))) := by
    intro s hs
    have hne : ∀ y' : ℝ, ¬ (y' = y' - s) := fun y' h => hs (by linarith)
    have h5 := hf3.continuous_iteratedDeriv 2 (by norm_num)
    simp only [c01_secant, hne, ite_false, sub_sub_cancel]
    fun_prop
  set k : ℝ → ℝ → ℝ := fun y s => (deriv f y - deriv f (y - s)) / |s| ^ (p + 1) *
    Γ (c01_secant f y (y - s)) with hk
  set k1 : ℝ → ℝ → ℝ := fun y s =>
    (iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (p + 1) * Γ (c01_secant f y (y - s)) +
      (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (p + 1)) * deriv Γ (c01_secant f y (y - s))
    with hk1
  have hSm : ∀ y, Measurable (fun s => c01_secant f y (y - s)) := fun y =>
    (c07_aux_secant_meas f hfc y).comp (by fun_prop)
  have hkm : ∀ y, Measurable (k y) := fun y => by
    have h1 := hSm y; have h2 := hΓc.measurable; have h3 := hd1c.measurable
    simp only [hk]; fun_prop
  have hk1m : ∀ y, Measurable (k1 y) := fun y => by
    have h1 := hSm y; have h2 := hΓc.measurable; have h3 := hd1c.measurable
    have h4 := hΓ'c.measurable; have h5 := (hf3.continuous_iteratedDeriv 2 (by norm_num)).measurable
    simp only [hk1]; fun_prop
  -- local domination around `y₀`
  have hloc : ∀ y₀ : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∀ y ∈ Metric.ball y₀ 1, ∀ s,
      ‖k y s‖ ≤ A * Nn * D s ∧ ‖k1 y s‖ ≤ A * Nn * D s := by
    intro y₀
    obtain ⟨A, hA0, hA⟩ := c07_aux_kernel_pt p hp hp1 K (|y₀| + 1) hK (by linarith [abs_nonneg y₀])
    refine ⟨A, hA0, fun y hy s => ?_⟩
    have hy' : |y| ≤ |y₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub y y₀; linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hA f hf Γ hΓ y hy' s
  have hint : ∀ y, Integrable (k y) ∧ Integrable (k1 y) := by
    intro y
    obtain ⟨A, -, hA⟩ := hloc y
    exact ⟨(hDi.const_mul (A * Nn)).mono' (hkm y).aestronglyMeasurable
        (Eventually.of_forall fun s => (hA y (Metric.mem_ball_self one_pos) s).1),
      (hDi.const_mul (A * Nn)).mono' (hk1m y).aestronglyMeasurable
        (Eventually.of_forall fun s => (hA y (Metric.mem_ball_self one_pos) s).2)⟩
  have hder : ∀ y, HasDerivAt (c07_kernel_operator p Γ f) (calpha p * ∫ s, k1 y s) y := by
    intro y₀
    obtain ⟨A, -, hA⟩ := hloc y₀
    obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := k) (F' := k1) (x₀ := y₀) (bound := fun s => A * Nn * D s)
      (Metric.ball_mem_nhds y₀ one_pos)
      (Eventually.of_forall fun y => (hkm y).aestronglyMeasurable) (hint y₀).1
      (hk1m y₀).aestronglyMeasurable
      (Eventually.of_forall fun s y hy => (hA y hy s).2) (hDi.const_mul _)
      ((Measure.ae_ne volume 0).mono fun s hs y _ => hdiff s hs y)
    exact hd.const_mul (calpha p)
  refine ⟨fun y => (hint y).1, ?_, fun y => ⟨(hint y).2, hder y⟩⟩
  refine contDiff_one_iff_deriv.2 ⟨fun y => (hder y).differentiableAt, ?_⟩
  rw [show deriv (c07_kernel_operator p Γ f) = fun y => calpha p * ∫ s, k1 y s from
    funext fun y => (hder y).deriv]
  refine continuous_const.mul (continuous_iff_continuousAt.2 fun y₀ => ?_)
  obtain ⟨A, -, hA⟩ := hloc y₀
  exact continuousAt_of_dominated (bound := fun s => A * Nn * D s)
    (Eventually.of_forall fun y => (hk1m y).aestronglyMeasurable)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ one_pos) fun y hy =>
      Eventually.of_forall fun s => (hA y hy s).2)
    (hDi.const_mul _) ((Measure.ae_ne volume 0).mono fun s hs => (hk1c s hs).continuousAt)

/-- Blueprint: lem:c07_kernel_C1.  For `K ≥ 1`, `f ∈ 𝒫(K)`, `Γ ∈ C¹`: `𝒯_Γ(f)` is given by an
absolutely convergent integral, is `C¹`, with the stated (absolutely convergent) derivative
formula; and for every `M ≥ 1` there is `C = C(p,K,M)` with
`‖𝒯_Γ(f)‖_{C¹([-M,M])} ≤ C ‖Γ‖_K`. -/
theorem c07_kernel_C1 (P : parameters) :
    (∀ K : ℝ, 1 ≤ K → ∀ f ∈ c07_profile_class P.p K, ∀ Γ : ℝ → ℝ, ContDiff ℝ 1 Γ →
      (∀ y : ℝ, Integrable (fun s => (deriv f y - deriv f (y - s)) / |s| ^ (P.p + 1) *
        Γ (c01_secant f y (y - s)))) ∧
      ContDiff ℝ 1 (c07_kernel_operator P.p Γ f) ∧
      ∀ y : ℝ,
        Integrable (fun s =>
          (iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (P.p + 1) *
              Γ (c01_secant f y (y - s)) +
            (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (P.p + 1)) *
              deriv Γ (c01_secant f y (y - s))) ∧
        HasDerivAt (c07_kernel_operator P.p Γ f)
          (calpha P.p * ∫ s,
            ((iteratedDeriv 2 f y - iteratedDeriv 2 f (y - s)) / |s| ^ (P.p + 1) *
                Γ (c01_secant f y (y - s)) +
              (deriv f y - deriv f (y - s)) ^ 2 / (s * |s| ^ (P.p + 1)) *
                deriv Γ (c01_secant f y (y - s)))) y) ∧
    (∀ K : ℝ, 1 ≤ K → ∀ M : ℝ, 1 ≤ M → ∃ C : ℝ, 0 < C ∧
      ∀ f ∈ c07_profile_class P.p K, ∀ Γ : ℝ → ℝ, ContDiff ℝ 1 Γ → ∀ y ∈ Icc (-M) M,
        |c07_kernel_operator P.p Γ f y| ≤ C * c07_kernel_operator_norm Γ K ∧
        |deriv (c07_kernel_operator P.p Γ f) y| ≤ C * c07_kernel_operator_norm Γ K) := by
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  have hc := c03_aux_calpha_pos P.p hp0 hp1
  refine ⟨fun K hK f hf Γ hΓ => c07_aux_kernel_C1_main P.p hp hp1 K hK f hf Γ hΓ,
    fun K hK M hM => ?_⟩
  have hθ := c07_aux_theta_eq P.p hp0
  have he : 1 < P.p + 1 - c07_theta P.p := by
    rw [hθ]; have : (1 - P.p) / (2 * P.p) < P.p := by rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  obtain ⟨hDi, hDI⟩ := c07_aux_kernel_majorant P.p (P.p + 1 - c07_theta P.p) hp0 hp1 he
  set I := 2 / (1 - P.p) + 2 / (P.p + 1 - c07_theta P.p - 1) with hI
  have hI0 : 0 ≤ I := by
    have : 0 < 1 - P.p := by linarith
    have : 0 < P.p + 1 - c07_theta P.p - 1 := by linarith
    positivity
  obtain ⟨A, hA0, hA⟩ := c07_aux_kernel_pt P.p hp hp1 K M hK hM
  refine ⟨calpha P.p * A * I + 1, by positivity, fun f hf Γ hΓ y hy => ?_⟩
  have hy' : |y| ≤ M := abs_le.2 hy
  obtain ⟨hN0, -⟩ := c07_aux_Gamma_norm Γ hΓ K (by linarith)
  obtain ⟨-, -, hd⟩ := c07_aux_kernel_C1_main P.p hp hp1 K hK f hf Γ hΓ
  have hbound : ∀ F : ℝ → ℝ, (∀ s, |F s| ≤ A * c07_kernel_operator_norm Γ K *
      ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-P.p)) s +
        {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(P.p + 1 - c07_theta P.p))) s)) →
      |calpha P.p * ∫ s, F s| ≤ (calpha P.p * A * I + 1) * c07_kernel_operator_norm Γ K := by
    intro F hF
    rw [abs_mul, abs_of_pos hc]
    have h1 : |∫ s, F s| ≤ A * c07_kernel_operator_norm Γ K * I := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le (hDi.const_mul _)
        (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hF s)).trans (le_of_eq ?_)
      rw [integral_const_mul, hDI]
    calc calpha P.p * |∫ s, F s| ≤ calpha P.p * (A * c07_kernel_operator_norm Γ K * I) :=
          mul_le_mul_of_nonneg_left h1 hc.le
      _ = calpha P.p * A * I * c07_kernel_operator_norm Γ K := by ring
      _ ≤ _ := by nlinarith
  refine ⟨hbound _ fun s => (hA f hf Γ hΓ y hy' s).1, ?_⟩
  rw [((hd y).2).deriv]
  exact hbound _ fun s => (hA f hf Γ hΓ y hy' s).2

/-- Uniform convergence on a set `S` plus a converging argument gives convergence along the
product filter. -/
theorem c07_aux_tuo_tendsto (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (S : Set ℝ) (hF : TendstoUniformlyOn F f atTop S)
    (hf : Continuous f) (x' : ℝ) (hS : S ∈ 𝓝 x') (L : Filter ℝ) (g : ℕ × ℝ → ℝ)
    (hg : Tendsto g (atTop ×ˢ L) (𝓝 x')) :
    Tendsto (fun q : ℕ × ℝ => F q.1 (g q)) (atTop ×ˢ L) (𝓝 (f x')) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 : ∀ᶠ n in atTop, ∀ y ∈ S, dist (f y) (F n y) < ε / 2 :=
    Metric.tendstoUniformlyOn_iff.1 hF (ε / 2) (half_pos hε)
  have h2 : ∀ᶠ q in atTop ×ˢ L, g q ∈ S := hg hS
  have h3 : ∀ᶠ q in atTop ×ˢ L, dist (f (g q)) (f x') < ε / 2 :=
    (hf.continuousAt.tendsto.comp hg) (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [h1.prod_inl L, h2, h3] with q hq1 hq2 hq3
  have := hq1 (g q) hq2
  calc dist (F q.1 (g q)) (f x') ≤ dist (F q.1 (g q)) (f (g q)) + dist (f (g q)) (f x') :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm] at this; exact add_lt_add this hq3
    _ = ε := by ring

/-- Uniform convergence on a compact set from convergence along `atTop ×ˢ 𝓝[S] x`. -/
theorem c07_aux_tuo_of_tendsto (Gn : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (hG : Continuous G) (S : Set ℝ)
    (hS : IsCompact S)
    (h : ∀ x ∈ S, Tendsto (fun q : ℕ × ℝ => Gn q.1 q.2) (atTop ×ˢ 𝓝[S] x) (𝓝 (G x))) :
    TendstoUniformlyOn Gn G atTop S := by
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS,
    tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  have h1 : Tendsto (fun q : ℕ × ℝ => G q.2) (atTop ×ˢ 𝓝[S] x) (𝓝 (G x)) :=
    hG.continuousAt.tendsto.comp (tendsto_snd.mono_right nhdsWithin_le_nhds)
  exact (h1.prodMk_nhds (h x hx)).mono_right (nhds_le_uniformity _)

/-- Blueprint: lem:c07_kernel_continuity.  If `f_n, f ∈ 𝒫(K)` and `f_n → f` in `C²_loc`, then
`𝒯_Γ(f_n) → 𝒯_Γ(f)` in `C¹_loc` (`Γ ∈ C¹`). -/
theorem c07_kernel_continuity (P : parameters) (K : ℝ) (hK : 1 ≤ K) (Γ : ℝ → ℝ)
    (hΓ : ContDiff ℝ 1 Γ) (fn : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfn : ∀ n, fn n ∈ c07_profile_class P.p K) (hf : f ∈ c07_profile_class P.p K)
    (hconv : c07_TendstoCkLoc 2 fn atTop f) :
    c07_TendstoCkLoc 1 (fun n => c07_kernel_operator P.p Γ (fn n)) atTop
      (c07_kernel_operator P.p Γ f) := by
  have hp := P.hp_lo
  have hp1 := P.hp_hi
  have hp0 : 0 < P.p := by linarith
  have hθ := c07_aux_theta_eq P.p hp0
  have he : 1 < P.p + 1 - c07_theta P.p := by
    rw [hθ]; have : (1 - P.p) / (2 * P.p) < P.p := by rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  obtain ⟨hDi, -⟩ := c07_aux_kernel_majorant P.p (P.p + 1 - c07_theta P.p) hp0 hp1 he
  have hΓc : Continuous Γ := hΓ.continuous
  have hΓ'c : Continuous (deriv Γ) := hΓ.continuous_deriv le_rfl
  obtain ⟨hN0, -⟩ := c07_aux_Gamma_norm Γ hΓ K (by linarith)
  -- iterated derivatives converge along the product filter
  have hcont_i : ∀ i ≤ 2, Continuous (iteratedDeriv i f) := fun i hi =>
    hf.1.continuous_iteratedDeriv i (by exact_mod_cast (hi.trans (by norm_num : 2 ≤ 3)))
  have hlim_i : ∀ i ≤ 2, ∀ (L : Filter ℝ) (g : ℕ × ℝ → ℝ) (x' : ℝ),
      Tendsto g (atTop ×ˢ L) (𝓝 x') →
      Tendsto (fun q : ℕ × ℝ => iteratedDeriv i (fn q.1) (g q)) (atTop ×ˢ L)
        (𝓝 (iteratedDeriv i f x')) := by
    intro i hi L g x' hg
    exact c07_aux_tuo_tendsto (fun n => iteratedDeriv i (fn n)) (iteratedDeriv i f)
      (Icc (-(|x'| + 1)) (|x'| + 1)) (hconv i hi _ (by positivity)) (hcont_i i hi) x'
      (Icc_mem_nhds (by linarith [neg_abs_le x']) (by linarith [le_abs_self x'])) L g hg
  have hi0 : ∀ g : ℝ → ℝ, iteratedDeriv 0 g = g := fun g => iteratedDeriv_zero
  have hi1 : ∀ g : ℝ → ℝ, iteratedDeriv 1 g = deriv g := fun g => iteratedDeriv_one
  intro i hi M hM
  -- the two integrands
  set k : (ℝ → ℝ) → ℝ → ℝ → ℝ := fun g y s => (deriv g y - deriv g (y - s)) / |s| ^ (P.p + 1) *
    Γ (c01_secant g y (y - s)) with hk
  set k1 : (ℝ → ℝ) → ℝ → ℝ → ℝ := fun g y s =>
    (iteratedDeriv 2 g y - iteratedDeriv 2 g (y - s)) / |s| ^ (P.p + 1) * Γ (c01_secant g y (y - s)) +
      (deriv g y - deriv g (y - s)) ^ 2 / (s * |s| ^ (P.p + 1)) * deriv Γ (c01_secant g y (y - s))
    with hk1
  -- generic DCT step
  have hgen : ∀ (Kf : (ℝ → ℝ) → ℝ → ℝ → ℝ),
      (∀ x : ℝ, ∃ A : ℝ, ∀ g ∈ c07_profile_class P.p K, ∀ y ∈ Metric.ball x 1, ∀ s,
        ‖Kf g y s‖ ≤ A * c07_kernel_operator_norm Γ K *
          ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-P.p)) s +
            {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(P.p + 1 - c07_theta P.p))) s)) →
      (∀ g ∈ c07_profile_class P.p K, ∀ y, Measurable (Kf g y)) →
      (∀ s, s ≠ 0 → ∀ x, Tendsto (fun q : ℕ × ℝ => Kf (fn q.1) q.2 s)
        (atTop ×ˢ 𝓝[Icc (-M) M] x) (𝓝 (Kf f x s))) →
      Continuous (fun y => calpha P.p * ∫ s, Kf f y s) →
      TendstoUniformlyOn (fun n y => calpha P.p * ∫ s, Kf (fn n) y s)
        (fun y => calpha P.p * ∫ s, Kf f y s) atTop (Icc (-M) M) := by
    intro Kf hdom hmeas hlim hc
    refine c07_aux_tuo_of_tendsto _ _ hc _ isCompact_Icc fun x _ => ?_
    obtain ⟨A, hA⟩ := hdom x
    refine Tendsto.const_mul _ (tendsto_integral_filter_of_dominated_convergence
      (fun s => A * c07_kernel_operator_norm Γ K *
          ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-P.p)) s +
            {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(P.p + 1 - c07_theta P.p))) s))
      (Eventually.of_forall fun q => (hmeas _ (hfn q.1) q.2).aestronglyMeasurable) ?_
      (hDi.const_mul _) ((Measure.ae_ne volume 0).mono fun s hs => hlim s hs x))
    have hball : ∀ᶠ y in 𝓝[Icc (-M) M] x, y ∈ Metric.ball x 1 :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds x one_pos)
    filter_upwards [hball.prod_inr atTop] with q hq
    exact Eventually.of_forall fun s => hA (fn q.1) (hfn q.1) q.2 hq s
  -- domination
  have hdomk : ∀ x : ℝ, ∃ A : ℝ, ∀ g ∈ c07_profile_class P.p K, ∀ y ∈ Metric.ball x 1, ∀ s,
      ‖k g y s‖ ≤ A * c07_kernel_operator_norm Γ K *
        ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-P.p)) s +
          {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(P.p + 1 - c07_theta P.p))) s) ∧
      ‖k1 g y s‖ ≤ A * c07_kernel_operator_norm Γ K *
        ({s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-P.p)) s +
          {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(P.p + 1 - c07_theta P.p))) s) := by
    intro x
    obtain ⟨A, -, hA⟩ := c07_aux_kernel_pt P.p hp hp1 K (|x| + 1) hK (by linarith [abs_nonneg x])
    refine ⟨A, fun g hg y hy s => ?_⟩
    have hy' : |y| ≤ |x| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub y x; linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hA g hg Γ hΓ y hy' s
  -- measurability
  have hmeas : ∀ g ∈ c07_profile_class P.p K, ∀ y, Measurable (k g y) ∧ Measurable (k1 g y) := by
    intro g hg y
    have hg3 := hg.1
    have hd1c : Continuous (deriv g) := (hg3.of_le (m := 2 + 1) (by norm_num)).deriv'.continuous
    have h1 : Measurable (fun s : ℝ => c01_secant g y (y - s)) :=
      (c07_aux_secant_meas g hg3.continuous y).comp (by fun_prop)
    have h2 := hΓc.measurable
    have h3 := hd1c.measurable
    have h4 := hΓ'c.measurable
    have h5 := (hg3.continuous_iteratedDeriv 2 (by norm_num)).measurable
    refine ⟨?_, ?_⟩
    · simp only [hk]; fun_prop
    · simp only [hk1]; fun_prop
  -- pointwise limits
  have hsec_eq : ∀ (g : ℝ → ℝ) (y s : ℝ), s ≠ 0 → c01_secant g y (y - s) = (g y - g (y - s)) / s := by
    intro g y s hs
    have hne : y ≠ y - s := by intro h; apply hs; linarith
    simp only [c01_secant, hne, ite_false, sub_sub_cancel]
  have hlims : ∀ s, s ≠ 0 → ∀ x,
      Tendsto (fun q : ℕ × ℝ => k (fn q.1) q.2 s) (atTop ×ˢ 𝓝[Icc (-M) M] x) (𝓝 (k f x s)) ∧
      Tendsto (fun q : ℕ × ℝ => k1 (fn q.1) q.2 s) (atTop ×ˢ 𝓝[Icc (-M) M] x) (𝓝 (k1 f x s)) := by
    intro s hs x
    have hsnd : Tendsto (fun q : ℕ × ℝ => q.2) (atTop ×ˢ 𝓝[Icc (-M) M] x) (𝓝 x) :=
      tendsto_snd.mono_right nhdsWithin_le_nhds
    have hsh : Tendsto (fun q : ℕ × ℝ => q.2 - s) (atTop ×ˢ 𝓝[Icc (-M) M] x) (𝓝 (x - s)) :=
      hsnd.sub_const s
    have a0 := hlim_i 0 (by norm_num) _ _ _ hsnd
    have a0s := hlim_i 0 (by norm_num) _ _ _ hsh
    have a1 := hlim_i 1 (by norm_num) _ _ _ hsnd
    have a1s := hlim_i 1 (by norm_num) _ _ _ hsh
    have a2 := hlim_i 2 le_rfl _ _ _ hsnd
    have a2s := hlim_i 2 le_rfl _ _ _ hsh
    simp only [hi0, hi1] at a0 a0s a1 a1s
    have hsec : Tendsto (fun q : ℕ × ℝ => c01_secant (fn q.1) q.2 (q.2 - s))
        (atTop ×ˢ 𝓝[Icc (-M) M] x) (𝓝 (c01_secant f x (x - s))) := by
      simp only [hsec_eq _ _ s hs]
      exact (a0.sub a0s).div_const s
    have hG := hΓc.continuousAt.tendsto.comp hsec
    have hG' := hΓ'c.continuousAt.tendsto.comp hsec
    refine ⟨?_, ?_⟩
    · exact ((a1.sub a1s).div_const _).mul hG
    · exact (((a2.sub a2s).div_const _).mul hG).add ((((a1.sub a1s).pow 2).div_const _).mul hG')
  -- continuity of the limits
  obtain ⟨-, hC1f, hdf⟩ := c07_aux_kernel_C1_main P.p hp hp1 K hK f hf Γ hΓ
  have hTeq : ∀ g, c07_kernel_operator P.p Γ g = fun y => calpha P.p * ∫ s, k g y s := fun g => rfl
  have hdeq : ∀ g ∈ c07_profile_class P.p K,
      deriv (c07_kernel_operator P.p Γ g) = fun y => calpha P.p * ∫ s, k1 g y s := by
    intro g hg
    obtain ⟨-, -, hd⟩ := c07_aux_kernel_C1_main P.p hp hp1 K hK g hg Γ hΓ
    exact funext fun y => (hd y).2.deriv
  interval_cases i
  · simp only [hi0]
    rw [hTeq f]
    simp only [hTeq]
    refine hgen k (fun x => ?_) (fun g hg y => (hmeas g hg y).1) (fun s hs x => (hlims s hs x).1) ?_
    · obtain ⟨A, hA⟩ := hdomk x
      exact ⟨A, fun g hg y hy s => (hA g hg y hy s).1⟩
    · rw [← hTeq f]; exact hC1f.continuous
  · simp only [hi1]
    rw [hdeq f hf]
    have : (fun n => deriv (c07_kernel_operator P.p Γ (fn n))) =
        fun n y => calpha P.p * ∫ s, k1 (fn n) y s := funext fun n => hdeq (fn n) (hfn n)
    rw [this]
    refine hgen k1 (fun x => ?_) (fun g hg y => (hmeas g hg y).2) (fun s hs x => (hlims s hs x).2) ?_
    · obtain ⟨A, hA⟩ := hdomk x
      exact ⟨A, fun g hg y hy s => (hA g hg y hy s).2⟩
    · rw [← hdeq f hf]; exact hC1f.continuous_deriv le_rfl

/-- Blueprint: lem:c07_tail_integrals.  Elementary weighted integrals, for `0 < p < 1`, `q > 1`,
`|y| ≥ 1` (integrability included). -/
theorem c07_tail_integrals (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ |y| →
      (IntegrableOn (fun z => jb z ^ (-p) * |y - z| ^ (-q)) {z | |y| / 4 ≤ |y - z|} ∧
        ∫ z in {z | |y| / 4 ≤ |y - z|}, jb z ^ (-p) * |y - z| ^ (-q) ≤ C * |y| ^ (1 - p - q)) ∧
      (IntegrableOn (fun z => |y - z| ^ (-q)) {z | |y| / 4 ≤ |y - z|} ∧
        ∫ z in {z | |y| / 4 ≤ |y - z|}, |y - z| ^ (-q) ≤ C * |y| ^ (1 - q)) ∧
      (IntegrableOn (fun s => |s| ^ (-p)) {s | |s| ≤ |y| / 2} ∧
        ∫ s in {s | |s| ≤ |y| / 2}, |s| ^ (-p) ≤ C * |y| ^ (1 - p)) ∧
      (y < 0 →
        IntegrableOn (fun z => (|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-q)) (Ioi 0) ∧
        ∫ z in Ioi (0 : ℝ), (|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-q) ≤
          C * |y| ^ (1 - p - q)) := by
  set Ca : ℝ := (4 : ℝ) ^ q * (2 * ((2 : ℝ) ^ (1 - p) / (1 - p))) +
    2 * (2 * ((4 : ℝ) ^ (-(1 - (p + q))) / (p + q - 1))) with hCa
  set Cb : ℝ := 2 * ((4 : ℝ) ^ (-(1 - q)) / (q - 1)) with hCb
  set Cc : ℝ := 2 * ((2 : ℝ) ^ (-(1 - p)) / (1 - p)) with hCc
  set Cd : ℝ := 1 + 1 / (1 - p) + 1 / (q - 1) + 1 / (p + q - 1) with hCd
  have hp1' : 0 < 1 - p := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hpq : 0 < p + q - 1 := by linarith
  have hCa0 : 0 < Ca := by positivity
  have hCb0 : 0 < Cb := by positivity
  have hCc0 : 0 < Cc := by positivity
  have hCd0 : 0 < Cd := by positivity
  refine ⟨Ca + Cb + Cc + Cd, by positivity, fun y hy => ?_⟩
  set Y := |y| with hYd
  have hY : 0 < Y := by linarith
  have hle : ∀ (Ci e : ℝ), 0 ≤ Ci → Ci ≤ Ca + Cb + Cc + Cd → Ci * Y ^ e ≤ (Ca + Cb + Cc + Cd) * Y ^ e :=
    fun Ci e _ h => mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hY.le _)
  have hSm : MeasurableSet {z : ℝ | Y / 4 ≤ |y - z|} :=
    measurableSet_le measurable_const (by fun_prop)
  refine ⟨?_, ?_, ?_, fun hy0 => ?_⟩
  · -- (1)
    set f : ℝ → ℝ := fun z => jb z ^ (-p) * |y - z| ^ (-q) with hf
    obtain ⟨hn1, hn2⟩ := c07_aux_near_int (2 * Y) p (by positivity) hp hp1
    obtain ⟨hf1, hf2⟩ := c07_aux_far_int (Y / 4) (p + q) y (by positivity) (by linarith)
    set H : ℝ → ℝ := fun z => (Y / 4) ^ (-q) * {s : ℝ | |s| ≤ 2 * Y}.indicator (fun s => |s| ^ (-p)) z +
        2 * {z : ℝ | Y / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + q))) z with hH
    have hHi : Integrable H := (hn1.const_mul _).add (hf1.const_mul _)
    have hfm : Measurable f := by simp only [hf, jb]; fun_prop
    have hae : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton _)
    have hbd : ∀ᵐ z ∂(volume : Measure ℝ),
        ‖{z : ℝ | Y / 4 ≤ |y - z|}.indicator f z‖ ≤ H z := by
      filter_upwards [hae] with z hz
      by_cases hzS : z ∈ {z : ℝ | Y / 4 ≤ |y - z|}
      · rw [indicator_of_mem hzS, Real.norm_eq_abs, abs_of_nonneg (by
          simp only [hf]; exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
            (Real.rpow_nonneg (abs_nonneg _) _))]
        exact c07_aux_tail_pt p q y z hp hp1 (by linarith) hY hz hzS
      · rw [indicator_of_notMem hzS, norm_zero]
        simp only [hH]
        have : 0 ≤ {s : ℝ | |s| ≤ 2 * Y}.indicator (fun s => |s| ^ (-p)) z :=
          indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
        have : 0 ≤ {z : ℝ | Y / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + q))) z :=
          indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
        have : 0 ≤ (Y / 4) ^ (-q) := Real.rpow_nonneg (by positivity) _
        positivity
    have hint : Integrable ({z : ℝ | Y / 4 ≤ |y - z|}.indicator f) :=
      hHi.mono' (hfm.indicator hSm).aestronglyMeasurable hbd
    refine ⟨(integrable_indicator_iff hSm).1 hint, ?_⟩
    rw [← integral_indicator hSm]
    calc ∫ z, {z : ℝ | Y / 4 ≤ |y - z|}.indicator f z ≤ ∫ z, H z :=
          integral_mono_ae hint hHi (hbd.mono fun z hz => (le_abs_self _).trans hz)
      _ = Ca * Y ^ (1 - p - q) := by
          rw [hH, integral_add (hn1.const_mul _) (hf1.const_mul _), integral_const_mul,
            integral_const_mul, hn2, hf2, (c07_aux_rpow_div Y 4 _ hY.le (by norm_num)).1,
            (c07_aux_rpow_div Y 4 _ hY.le (by norm_num)).1,
            (c07_aux_rpow_div Y 2 _ hY.le (by norm_num)).2, neg_neg]
          have k1 : Y ^ (-q) * Y ^ (1 - p) = Y ^ (1 - p - q) := by
            rw [← Real.rpow_add hY]; ring_nf
          have k2 : Y ^ (1 - (p + q)) = Y ^ (1 - p - q) := by ring_nf
          rw [hCa, k2, ← k1]; ring
      _ ≤ _ := hle Ca _ hCa0.le (by linarith)
  · -- (2a)
    obtain ⟨hf1, hf2⟩ := c07_aux_far_int (Y / 4) q y (by positivity) hq
    refine ⟨(integrable_indicator_iff hSm).1 hf1, ?_⟩
    rw [← integral_indicator hSm, hf2, (c07_aux_rpow_div Y 4 _ hY.le (by norm_num)).1]
    calc 2 * ((4 : ℝ) ^ (-(1 - q)) * Y ^ (1 - q) / (q - 1)) = Cb * Y ^ (1 - q) := by
          rw [hCb]; ring
      _ ≤ _ := hle Cb _ hCb0.le (by linarith)
  · -- (2b)
    have hSm' : MeasurableSet {s : ℝ | |s| ≤ Y / 2} := measurableSet_le (by fun_prop) measurable_const
    obtain ⟨hn1, hn2⟩ := c07_aux_near_int (Y / 2) p (by positivity) hp hp1
    refine ⟨(integrable_indicator_iff hSm').1 hn1, ?_⟩
    rw [← integral_indicator hSm', hn2, (c07_aux_rpow_div Y 2 _ hY.le (by norm_num)).1]
    calc 2 * ((2 : ℝ) ^ (-(1 - p)) * Y ^ (1 - p) / (1 - p)) = Cc * Y ^ (1 - p) := by
          rw [hCc]; ring
      _ ≤ _ := hle Cc _ hCc0.le (by linarith)
  · -- (3)
    obtain ⟨h1, h2⟩ := c07_aux_tail_three p q Y hp hp1 hq hY
    exact ⟨h1, h2.trans (hle Cd _ hCd0.le (by linarith))⟩


/-- Symmetrized form of `|D|^p g(y)` (`φ` integrable). -/
theorem c07_aux_frac_symm (p : ℝ) (g : ℝ → ℝ) (y : ℝ)
    (hi : Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1))) :
    ∫ z, (g y - g z) / |y - z| ^ (p + 1) =
      ∫ s in Ioi (0 : ℝ), (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1) := by
  set φ : ℝ → ℝ := fun s => (g y - g (y - s)) / |s| ^ (p + 1) with hφ
  have h1 : ∫ z, (g y - g z) / |y - z| ^ (p + 1) = ∫ s, φ s := by
    rw [← integral_sub_left_eq_self _ volume y]; simp [hφ, sub_sub_cancel]
  have hφi : Integrable φ := by
    have := hi.comp_sub_left y; simpa [hφ, sub_sub_cancel] using this
  have h2 : ∫ s, φ s = (1 / 2) * ∫ s, (fun t => φ t + φ (-t)) |s| := by
    have e : (fun s => (fun t => φ t + φ (-t)) |s|) = fun s => φ s + φ (-s) := by
      funext s
      rcases le_total 0 s with h | h
      · simp [abs_of_nonneg h]
      · simp [abs_of_nonpos h]; ring
    rw [e, integral_add hφi hφi.comp_neg, integral_neg_eq_self]; ring
  rw [h1, h2, integral_comp_abs (f := fun t => φ t + φ (-t))]
  rw [← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  simp only [hφ, abs_neg, abs_of_pos hs0, sub_neg_eq_add]
  ring

/-- Integration by parts on `(r,∞)` against `s^{-q}`. -/
theorem c07_aux_ibp_Ioi (q r : ℝ) (hq : 1 < q) (hr : 0 < r) (F F' : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (F' s) s) (hF'c : Continuous F') (B0 B1 : ℝ)
    (hB0 : ∀ s, |F s| ≤ B0) (hB1 : ∀ s, |F' s| ≤ B1) :
    IntegrableOn (fun s => s ^ (-q) * F' s) (Ioi r) ∧
    IntegrableOn (fun s => s ^ (-q - 1) * F s) (Ioi r) ∧
    ∫ s in Ioi r, s ^ (-q) * F' s = -(r ^ (-q) * F r) + q * ∫ s in Ioi r, s ^ (-q - 1) * F s := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun s => (hF s).continuousAt
  have i1 : IntegrableOn (fun s : ℝ => s ^ (-q)) (Ioi r) := integrableOn_Ioi_rpow_of_lt (by linarith) hr
  have i2 : IntegrableOn (fun s : ℝ => s ^ (-q - 1)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr
  have hpos : ∀ s ∈ Ioi r, 0 < s := fun s hs => lt_trans hr hs
  have hm1 : Measurable (fun s : ℝ => s ^ (-q) * F' s) := by have := hF'c.measurable; fun_prop
  have hm2 : Measurable (fun s : ℝ => s ^ (-q - 1) * F s) := by have := hFc.measurable; fun_prop
  have j1 : IntegrableOn (fun s => s ^ (-q) * F' s) (Ioi r) :=
    (i1.mul_const B1).mono' hm1.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hpos s hs).le _)]
        exact mul_le_mul_of_nonneg_left (hB1 s) (Real.rpow_nonneg (hpos s hs).le _)))
  have j2 : IntegrableOn (fun s => s ^ (-q - 1) * F s) (Ioi r) :=
    (i2.mul_const B0).mono' hm2.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hpos s hs).le _)]
        exact mul_le_mul_of_nonneg_left (hB0 s) (Real.rpow_nonneg (hpos s hs).le _)))
  refine ⟨j1, j2, ?_⟩
  have hu : ∀ s ∈ Ioi r, HasDerivAt (fun s : ℝ => s ^ (-q)) (-q * s ^ (-q - 1)) s := fun s hs =>
    Real.hasDerivAt_rpow_const (Or.inl (hpos s hs).ne')
  have hv : ∀ s ∈ Ioi r, HasDerivAt F (F' s) s := fun s _ => hF s
  have j2' : IntegrableOn ((fun s : ℝ => -q * s ^ (-q - 1)) * F) (Ioi r) := by
    have := j2.const_mul (-q)
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have h0 : Tendsto ((fun s : ℝ => s ^ (-q)) * F) (𝓝[>] r) (𝓝 (r ^ (-q) * F r)) := by
    have : ContinuousAt ((fun s : ℝ => s ^ (-q)) * F) r :=
      ((continuousAt_id.rpow_const (Or.inl hr.ne')).mul hFc.continuousAt)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun s : ℝ => s ^ (-q)) * F) atTop (𝓝 0) := by
    have ht : Tendsto (fun s : ℝ => B0 * s ^ (-q)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < q)).const_mul B0
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg hs.le _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB0 s) (Real.rpow_nonneg hs.le _)
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hv j1 j2' h0 hinf
  rw [this]
  have e : ∫ s in Ioi r, -q * s ^ (-q - 1) * F s = -q * ∫ s in Ioi r, s ^ (-q - 1) * F s := by
    rw [← integral_const_mul]; congr 1; funext s; ring
  rw [e]; ring

/-- Half-line version of lem:c07_tail_integrals (1). -/
theorem c07_aux_tail_half (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ |y| →
      IntegrableOn (fun s => s ^ (-q) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p))) (Ioi (|y| / 2)) ∧
      ∫ s in Ioi (|y| / 2), s ^ (-q) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p)) ≤
        C * |y| ^ (1 - p - q) := by
  obtain ⟨C, hC, hT⟩ := c07_tail_integrals p q hp hp1 hq
  refine ⟨C, hC, fun y hy => ?_⟩
  obtain ⟨⟨i1, b1⟩, -⟩ := hT y hy
  have hY : 0 < |y| := by linarith
  set S := {z : ℝ | |y| / 4 ≤ |y - z|} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  set Ψ := S.indicator (fun z => jb z ^ (-p) * |y - z| ^ (-q)) with hΨ
  have hΨi : Integrable Ψ := (integrable_indicator_iff hSm).2 i1
  have hΨ0 : ∀ z, 0 ≤ Ψ z := fun z => indicator_nonneg (fun z _ =>
    mul_nonneg (Real.rpow_nonneg (by linarith [c07_aux_one_le_jb z]) _)
      (Real.rpow_nonneg (abs_nonneg _) _)) z
  set Θ : ℝ → ℝ := fun s => Ψ (y - s) with hΘ
  have hΘi : Integrable Θ := hΨi.comp_sub_left y
  have hΘint : ∫ s, Θ s = ∫ z in S, jb z ^ (-p) * |y - z| ^ (-q) := by
    rw [integral_sub_left_eq_self Ψ volume y, hΨ, integral_indicator hSm]
  -- `∫_{Ioi 0} (Θ s + Θ (-s)) = ∫ Θ`
  have hsym : ∫ s in Ioi (0 : ℝ), (Θ s + Θ (-s)) = ∫ s, Θ s := by
    have e : (fun s => (fun t => Θ t + Θ (-t)) |s|) = fun s => Θ s + Θ (-s) := by
      funext s
      rcases le_total 0 s with h | h
      · simp [abs_of_nonneg h]
      · simp [abs_of_nonpos h]; ring
    have := integral_comp_abs (f := fun t => Θ t + Θ (-t))
    rw [e, integral_add hΘi hΘi.comp_neg, integral_neg_eq_self] at this
    linarith
  have hpt : ∀ s ∈ Ioi (|y| / 2), s ^ (-q) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p)) =
      Θ s + Θ (-s) := by
    intro s hs
    have hs' : |y| / 2 < s := hs
    have hs0 : 0 < s := by linarith
    have m1 : y - s ∈ S := by
      show |y| / 4 ≤ |y - (y - s)|; rw [sub_sub_cancel, abs_of_pos hs0]; linarith
    have m2 : y - -s ∈ S := by
      show |y| / 4 ≤ |y - (y - -s)|; rw [sub_sub_cancel, abs_neg, abs_of_pos hs0]; linarith
    simp only [hΘ, hΨ, indicator_of_mem m1, indicator_of_mem m2]
    have e1 : |y - (y - s)| = s := by rw [sub_sub_cancel, abs_of_pos hs0]
    have e2 : |y - (y - -s)| = s := by rw [sub_sub_cancel, abs_neg, abs_of_pos hs0]
    rw [e1, e2, sub_neg_eq_add]; ring
  have hsum : Integrable (fun s => Θ s + Θ (-s)) := hΘi.add hΘi.comp_neg
  refine ⟨IntegrableOn.congr_fun hsum.integrableOn (fun s hs => (hpt s hs).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  calc ∫ s in Ioi (|y| / 2), (Θ s + Θ (-s)) ≤ ∫ s in Ioi (0 : ℝ), (Θ s + Θ (-s)) := by
        refine setIntegral_mono_set hsum.integrableOn
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s _ =>
            add_nonneg (hΨ0 _) (hΨ0 _))) ?_
        exact (Ioi_subset_Ioi (by positivity)).eventuallyLE
    _ = _ := by rw [hsym, hΘint]
    _ ≤ _ := b1

/-- Near/far splitting estimate for `|D|^p g(y)` at scale `w`. -/
theorem c07_aux_frac_core (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (hgd : Differentiable ℝ g)
    (y w K J Bf : ℝ) (hw : 0 < w) (hK : 0 ≤ K)
    (hi : Integrable (fun z => (g y - g z) / |y - z| ^ (p + 1)))
    (hgy : |g y| ≤ K * w ^ (-(p + 1 + J)))
    (hg' : ∀ x ∈ Icc (y - w) (y + w), |deriv g x| ≤ K * w ^ (-(p + 2 + J)))
    (hfar : IntegrableOn (fun s => s ^ (-(p + 1)) * (g (y + s) + g (y - s))) (Ioi w))
    (hfarb : |∫ s in Ioi w, s ^ (-(p + 1)) * (g (y + s) + g (y - s))| ≤
      K * Bf * w ^ (-(2 * p + 1 + J))) :
    |fracD p g y| ≤ calpha p * K * (2 / (1 - p) + 2 / p + Bf) * w ^ (-(2 * p + 1 + J)) := by
  have hc := c03_aux_calpha_pos p hp hp1
  set ψ : ℝ → ℝ := fun s => (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1) with hψ
  -- integrability on `Ioi 0`
  set φ : ℝ → ℝ := fun s => (g y - g (y - s)) / |s| ^ (p + 1) with hφ
  have hφi : Integrable φ := by
    have := hi.comp_sub_left y; simpa [hφ, sub_sub_cancel] using this
  have hψi : IntegrableOn ψ (Ioi 0) := by
    refine IntegrableOn.congr_fun (hφi.add hφi.comp_neg).integrableOn (fun s hs => ?_)
      measurableSet_Ioi
    have hs0 : 0 < s := hs
    simp only [hφ, hψ, Pi.add_apply, sub_neg_eq_add, abs_neg]; rw [abs_of_pos hs0]; ring
  have hsplit : ∫ s in Ioi (0 : ℝ), ψ s = (∫ s in Ioc 0 w, ψ s) + ∫ s in Ioi w, ψ s := by
    rw [← Ioc_union_Ioi_eq_Ioi hw.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hψi.mono_set Ioc_subset_Ioi_self) (hψi.mono_set (Ioi_subset_Ioi hw.le))]
  -- far part
  have hr1 : IntegrableOn (fun s : ℝ => s ^ (-(p + 1))) (Ioi w) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hw
  have hfareq : ∫ s in Ioi w, ψ s = 2 * g y * (w ^ (-p) / p) -
      ∫ s in Ioi w, s ^ (-(p + 1)) * (g (y + s) + g (y - s)) := by
    have e : ∀ s ∈ Ioi w, ψ s = 2 * g y * s ^ (-(p + 1)) - s ^ (-(p + 1)) * (g (y + s) + g (y - s)) := by
      intro s hs
      have hs0 : 0 < s := lt_trans hw hs
      simp only [hψ]; rw [Real.rpow_neg hs0.le, div_eq_mul_inv]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_sub (hr1.const_mul _) hfar,
      integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hw]
    rw [show -(p + 1) + 1 = -p by ring, div_neg, neg_div, neg_neg]
  -- near part
  have hnear : |∫ s in Ioc 0 w, ψ s| ≤ 2 * K * w ^ (-(p + 2 + J)) * (w ^ (1 - p) / (1 - p)) := by
    have hii : IntegrableOn (fun s : ℝ => s ^ (-p)) (Ioc 0 w) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hw.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hv : ∫ s in Ioc 0 w, s ^ (-p) = w ^ (1 - p) / (1 - p) := by
      rw [← intervalIntegral.integral_of_le hw.le, integral_rpow (Or.inl (by linarith)),
        Real.zero_rpow (by linarith)]
      rw [show -p + 1 = 1 - p by ring, sub_zero]
    have hmv : ∀ x ∈ Icc (y - w) (y + w), |g y - g x| ≤ K * w ^ (-(p + 2 + J)) * |y - x| := by
      intro x hx
      have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc (y - w) (y + w)) (f := g)
        (fun t _ => hgd t) (fun t ht => by rw [Real.norm_eq_abs]; exact hg' t ht) (convex_Icc _ _)
        hx (show y ∈ Icc (y - w) (y + w) from ⟨by linarith, by linarith⟩)
      simpa [Real.norm_eq_abs, abs_sub_comm] using this
    have hb : ∀ s ∈ Ioc (0 : ℝ) w, ‖ψ s‖ ≤ 2 * K * w ^ (-(p + 2 + J)) * s ^ (-p) := by
      intro s hs
      have hs0 : 0 < s := hs.1
      have h1 := hmv (y - s) ⟨by linarith [hs.2], by linarith⟩
      have h2 := hmv (y + s) ⟨by linarith, by linarith [hs.2]⟩
      rw [sub_sub_cancel, abs_of_pos hs0] at h1
      rw [show y - (y + s) = -s by ring, abs_neg, abs_of_pos hs0] at h2
      simp only [hψ, Real.norm_eq_abs]
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hs0 _), div_le_iff₀ (Real.rpow_pos_of_pos hs0 _)]
      have e : s ^ (-p) * s ^ (p + 1) = s := by
        rw [← Real.rpow_add hs0]; ring_nf; exact Real.rpow_one s
      have : |2 * g y - g (y - s) - g (y + s)| ≤ |g y - g (y - s)| + |g y - g (y + s)| := by
        have := abs_add_le (g y - g (y - s)) (g y - g (y + s)); ring_nf at this ⊢; linarith
      calc |2 * g y - g (y - s) - g (y + s)| ≤ 2 * (K * w ^ (-(p + 2 + J)) * s) := by linarith
        _ = 2 * K * w ^ (-(p + 2 + J)) * (s ^ (-p) * s ^ (p + 1)) := by rw [e]; ring
        _ = _ := by ring
    calc |∫ s in Ioc 0 w, ψ s| = ‖∫ s in Ioc 0 w, ψ s‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in Ioc 0 w, 2 * K * w ^ (-(p + 2 + J)) * s ^ (-p) :=
          norm_integral_le_of_norm_le (hii.const_mul _)
            ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hb))
      _ = _ := by rw [integral_const_mul, hv]
  -- assemble
  have hrep : fracD p g y = calpha p * ((∫ s in Ioc 0 w, ψ s) + (2 * g y * (w ^ (-p) / p) -
      ∫ s in Ioi w, s ^ (-(p + 1)) * (g (y + s) + g (y - s)))) := by
    unfold fracD; rw [c07_aux_frac_symm p g y hi, hsplit, hfareq]
  have e1 : w ^ (-(p + 2 + J)) * w ^ (1 - p) = w ^ (-(2 * p + 1 + J)) := by
    rw [← Real.rpow_add hw]; ring_nf
  have e2 : w ^ (-(p + 1 + J)) * w ^ (-p) = w ^ (-(2 * p + 1 + J)) := by
    rw [← Real.rpow_add hw]; ring_nf
  have hW : 0 ≤ w ^ (-(2 * p + 1 + J)) := Real.rpow_nonneg hw.le _
  have hwp : 0 ≤ w ^ (-p) := Real.rpow_nonneg hw.le _
  rw [hrep, abs_mul, abs_of_pos hc]
  have hfar1 : |2 * g y * (w ^ (-p) / p)| ≤ 2 * K / p * w ^ (-(2 * p + 1 + J)) := by
    rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (div_nonneg hwp hp.le)]
    calc 2 * |g y| * (w ^ (-p) / p) ≤ 2 * (K * w ^ (-(p + 1 + J))) * (w ^ (-p) / p) := by gcongr
      _ = 2 * K / p * (w ^ (-(p + 1 + J)) * w ^ (-p)) := by ring
      _ = _ := by rw [e2]
  have hnear' : |∫ s in Ioc 0 w, ψ s| ≤ 2 * K / (1 - p) * w ^ (-(2 * p + 1 + J)) := by
    refine hnear.trans (le_of_eq ?_)
    rw [← e1]; ring
  have htri : |(∫ s in Ioc 0 w, ψ s) + (2 * g y * (w ^ (-p) / p) -
      ∫ s in Ioi w, s ^ (-(p + 1)) * (g (y + s) + g (y - s)))| ≤
      |∫ s in Ioc 0 w, ψ s| + |2 * g y * (w ^ (-p) / p)| +
        |∫ s in Ioi w, s ^ (-(p + 1)) * (g (y + s) + g (y - s))| := by
    have := abs_add_le (∫ s in Ioc 0 w, ψ s) (2 * g y * (w ^ (-p) / p) -
      ∫ s in Ioi w, s ^ (-(p + 1)) * (g (y + s) + g (y - s)))
    have := abs_sub (2 * g y * (w ^ (-p) / p)) (∫ s in Ioi w, s ^ (-(p + 1)) * (g (y + s) + g (y - s)))
    linarith
  calc calpha p * |_| ≤ calpha p * (2 * K / (1 - p) * w ^ (-(2 * p + 1 + J)) +
        2 * K / p * w ^ (-(2 * p + 1 + J)) + K * Bf * w ^ (-(2 * p + 1 + J))) := by
        refine mul_le_mul_of_nonneg_left (htri.trans ?_) hc.le
        linarith
    _ = _ := by field_simp

/-- Pointwise bounds for `h, h', h'', h'''` from the `iteratedDeriv` hypotheses. -/
theorem c07_aux_h_bounds (p K : ℝ) (h : ℝ → ℝ)
    (hb : ∀ i ≤ 3, ∀ y : ℝ, |iteratedDeriv i h y| ≤ K * jb y ^ (-p - i)) (x : ℝ) :
    |h x| ≤ K * jb x ^ (-p) ∧ |deriv h x| ≤ K * jb x ^ (-(p + 1)) ∧
    |deriv (deriv h) x| ≤ K * jb x ^ (-(p + 2)) ∧
    |deriv (deriv (deriv h)) x| ≤ K * jb x ^ (-(p + 3)) := by
  have e2 : deriv (deriv h) = iteratedDeriv 2 h := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e3 : deriv (deriv (deriv h)) = iteratedDeriv 3 h := by rw [iteratedDeriv_succ, e2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hb 0 (by norm_num) x
  · have := hb 1 (by norm_num) x; rw [iteratedDeriv_one] at this
    rwa [show -p - ((1 : ℕ) : ℝ) = -(p + 1) by push_cast; ring] at this
  · have := hb 2 (by norm_num) x; rw [← e2] at this
    rwa [show -p - ((2 : ℕ) : ℝ) = -(p + 2) by push_cast; ring] at this
  · have := hb 3 (by norm_num) x; rw [← e3] at this
    rwa [show -p - ((3 : ℕ) : ℝ) = -(p + 3) by push_cast; ring] at this

/-- `⟨x⟩^{-e} ≤ w^{-e}` when `0 < w ≤ |x|`, `e ≥ 0`. -/
theorem c07_aux_jb_le_w (x w e : ℝ) (hw : 0 < w) (hx : w ≤ |x|) (he : 0 ≤ e) :
    jb x ^ (-e) ≤ w ^ (-e) :=
  Real.rpow_le_rpow_of_nonpos hw (hx.trans (c07_aux_abs_le_jb x)) (by linarith)

/-- Far-field estimate for `g = h'` (`j = 0`). -/
theorem c07_aux_far0 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Ch : ℝ) (hCh : 0 < Ch)
    (hT : ∀ y : ℝ, 1 ≤ |y| →
      IntegrableOn (fun s => s ^ (-(p + 2)) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p))) (Ioi (|y| / 2)) ∧
      ∫ s in Ioi (|y| / 2), s ^ (-(p + 2)) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p)) ≤
        Ch * |y| ^ (1 - p - (p + 2)))
    (K : ℝ) (hK : 0 ≤ K) (h : ℝ → ℝ) (hh : ContDiff ℝ 3 h)
    (hb : ∀ i ≤ 3, ∀ y : ℝ, |iteratedDeriv i h y| ≤ K * jb y ^ (-p - i)) (y : ℝ) (hy : 1 ≤ |y|) :
    IntegrableOn (fun s => s ^ (-(p + 1)) * (deriv h (y + s) + deriv h (y - s))) (Ioi (|y| / 2)) ∧
    |∫ s in Ioi (|y| / 2), s ^ (-(p + 1)) * (deriv h (y + s) + deriv h (y - s))| ≤
      K * (2 + (p + 1) * Ch) * (|y| / 2) ^ (-(2 * p + 1 + 0)) := by
  set w := |y| / 2 with hwd
  have hw : 0 < w := by linarith
  have hbd := c07_aux_h_bounds p K h hb
  have hle1 : ∀ x e : ℝ, 0 ≤ e → jb x ^ (-e) ≤ 1 := fun x e he => c07_aux_jb_rpow_neg_le_one x e he
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hdc : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
  set F : ℝ → ℝ := fun s => h (y + s) - h (y - s) with hF
  set F' : ℝ → ℝ := fun s => deriv h (y + s) + deriv h (y - s) with hF'
  have hFd : ∀ s, HasDerivAt F (F' s) s := fun s => by
    have h1 := (hhd (y + s)).hasDerivAt.comp s ((hasDerivAt_id s).const_add y)
    have h2 := (hhd (y - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub y)
    convert h1.sub h2 using 1
    · rfl
    · simp only [hF']; ring
  have hB0 : ∀ s, |F s| ≤ 2 * K := fun s => by
    have := abs_sub (h (y + s)) (h (y - s))
    have a1 := (hbd (y + s)).1; have a2 := (hbd (y - s)).1
    have := mul_le_mul_of_nonneg_left (hle1 (y + s) p hp.le) hK
    have := mul_le_mul_of_nonneg_left (hle1 (y - s) p hp.le) hK
    simp only [hF]; linarith
  have hB1 : ∀ s, |F' s| ≤ 2 * K := fun s => by
    have := abs_add_le (deriv h (y + s)) (deriv h (y - s))
    have a1 := (hbd (y + s)).2.1; have a2 := (hbd (y - s)).2.1
    have := mul_le_mul_of_nonneg_left (hle1 (y + s) (p + 1) (by linarith)) hK
    have := mul_le_mul_of_nonneg_left (hle1 (y - s) (p + 1) (by linarith)) hK
    simp only [hF']; linarith
  obtain ⟨j1, j2, hibp⟩ := c07_aux_ibp_Ioi (p + 1) w (by linarith) hw F F' hFd
    (by simp only [hF']; fun_prop) _ _ hB0 hB1
  refine ⟨j1, ?_⟩
  rw [show (fun s => s ^ (-(p + 1)) * (deriv h (y + s) + deriv h (y - s))) =
    fun s => s ^ (-(p + 1)) * F' s from rfl, hibp]
  obtain ⟨-, hT2⟩ := hT y hy
  -- boundary term
  have hyw1 : w ≤ |y + w| := by
    have := abs_sub_abs_le_abs_sub y (-w); rw [sub_neg_eq_add, abs_neg, abs_of_pos hw] at this
    rw [hwd] at this ⊢; linarith
  have hyw2 : w ≤ |y - w| := by
    have := abs_sub_abs_le_abs_sub y w; rw [abs_of_pos hw] at this
    rw [hwd] at this ⊢; linarith
  have hFw : |F w| ≤ 2 * K * w ^ (-p) := by
    have := abs_sub (h (y + w)) (h (y - w))
    have a1 := (hbd (y + w)).1; have a2 := (hbd (y - w)).1
    have := mul_le_mul_of_nonneg_left (c07_aux_jb_le_w _ w p hw hyw1 hp.le) hK
    have := mul_le_mul_of_nonneg_left (c07_aux_jb_le_w _ w p hw hyw2 hp.le) hK
    simp only [hF]; linarith
  -- integral term
  have hint : |∫ s in Ioi w, s ^ (-(p + 1) - 1) * F s| ≤ K * (Ch * w ^ (-(2 * p + 1))) := by
    have hb : ∀ s ∈ Ioi w, ‖s ^ (-(p + 1) - 1) * F s‖ ≤
        K * (s ^ (-(p + 2)) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p))) := by
      intro s hs
      have hs0 : 0 < s := lt_trans hw hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        show -(p + 1) - 1 = -(p + 2) by ring]
      have := abs_sub (h (y + s)) (h (y - s))
      have a1 := (hbd (y + s)).1; have a2 := (hbd (y - s)).1
      have hF1 : |F s| ≤ K * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p)) := by
        simp only [hF]; linarith
      calc s ^ (-(p + 2)) * |F s| ≤ s ^ (-(p + 2)) * (K * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p))) :=
            mul_le_mul_of_nonneg_left hF1 (Real.rpow_nonneg hs0.le _)
        _ = _ := by ring
    obtain ⟨hTi, -⟩ := hT y hy
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hTi.const_mul K)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb))).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left (hT2.trans ?_) hK
    refine mul_le_mul_of_nonneg_left ?_ hCh.le
    rw [show 1 - p - (p + 2) = -(2 * p + 1) by ring]
    exact Real.rpow_le_rpow_of_nonpos hw (by rw [hwd]; linarith) (by linarith)
  have e1 : w ^ (-(p + 1)) * w ^ (-p) = w ^ (-(2 * p + 1 + 0)) := by
    rw [← Real.rpow_add hw]; ring_nf
  have hwp : 0 ≤ w ^ (-(p + 1)) := Real.rpow_nonneg hw.le _
  calc |-(w ^ (-(p + 1)) * F w) + (p + 1) * ∫ s in Ioi w, s ^ (-(p + 1) - 1) * F s|
      ≤ w ^ (-(p + 1)) * |F w| + (p + 1) * |∫ s in Ioi w, s ^ (-(p + 1) - 1) * F s| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hwp, abs_of_pos (by linarith : (0:ℝ) < p + 1)]
    _ ≤ w ^ (-(p + 1)) * (2 * K * w ^ (-p)) + (p + 1) * (K * (Ch * w ^ (-(2 * p + 1)))) := by
        gcongr
    _ = K * (2 + (p + 1) * Ch) * (w ^ (-(2 * p + 1 + 0))) := by
        rw [show -(2 * p + 1) = -(2 * p + 1 + 0) by ring, ← e1]; ring

/-- Far-field estimate for `g = h''` (`j = 1`). -/
theorem c07_aux_far1 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (Ch : ℝ) (hCh : 0 < Ch)
    (hT : ∀ y : ℝ, 1 ≤ |y| →
      IntegrableOn (fun s => s ^ (-(p + 3)) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p))) (Ioi (|y| / 2)) ∧
      ∫ s in Ioi (|y| / 2), s ^ (-(p + 3)) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p)) ≤
        Ch * |y| ^ (1 - p - (p + 3)))
    (K : ℝ) (hK : 0 ≤ K) (h : ℝ → ℝ) (hh : ContDiff ℝ 3 h)
    (hb : ∀ i ≤ 3, ∀ y : ℝ, |iteratedDeriv i h y| ≤ K * jb y ^ (-p - i)) (y : ℝ) (hy : 1 ≤ |y|) :
    IntegrableOn (fun s => s ^ (-(p + 1)) * (deriv (deriv h) (y + s) + deriv (deriv h) (y - s)))
      (Ioi (|y| / 2)) ∧
    |∫ s in Ioi (|y| / 2), s ^ (-(p + 1)) * (deriv (deriv h) (y + s) + deriv (deriv h) (y - s))| ≤
      K * (2 + 2 * (p + 1) + (p + 1) * (p + 2) * Ch) * (|y| / 2) ^ (-(2 * p + 1 + 1)) := by
  set w := |y| / 2 with hwd
  have hw : 0 < w := by linarith
  have hbd := c07_aux_h_bounds p K h hb
  have hle1 : ∀ x e : ℝ, 0 ≤ e → jb x ^ (-e) ≤ 1 := fun x e he => c07_aux_jb_rpow_neg_le_one x e he
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 2 (deriv h) := (hh.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hd1d : Differentiable ℝ (deriv h) := hd1.differentiable (by norm_num)
  have hd2c : Continuous (deriv (deriv h)) := hd1.continuous_deriv (by norm_num)
  have hd1c : Continuous (deriv h) := hd1.continuous
  -- first integration by parts
  set F : ℝ → ℝ := fun s => deriv h (y + s) - deriv h (y - s) with hF
  set F' : ℝ → ℝ := fun s => deriv (deriv h) (y + s) + deriv (deriv h) (y - s) with hF'
  have hFd : ∀ s, HasDerivAt F (F' s) s := fun s => by
    have h1 := (hd1d (y + s)).hasDerivAt.comp s ((hasDerivAt_id s).const_add y)
    have h2 := (hd1d (y - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub y)
    convert h1.sub h2 using 1
    · rfl
    · simp only [hF']; ring
  have hB0 : ∀ s, |F s| ≤ 2 * K := fun s => by
    have := abs_sub (deriv h (y + s)) (deriv h (y - s))
    have a1 := (hbd (y + s)).2.1; have a2 := (hbd (y - s)).2.1
    have := mul_le_mul_of_nonneg_left (hle1 (y + s) (p + 1) (by linarith)) hK
    have := mul_le_mul_of_nonneg_left (hle1 (y - s) (p + 1) (by linarith)) hK
    simp only [hF]; linarith
  have hB1 : ∀ s, |F' s| ≤ 2 * K := fun s => by
    have := abs_add_le (deriv (deriv h) (y + s)) (deriv (deriv h) (y - s))
    have a1 := (hbd (y + s)).2.2.1; have a2 := (hbd (y - s)).2.2.1
    have := mul_le_mul_of_nonneg_left (hle1 (y + s) (p + 2) (by linarith)) hK
    have := mul_le_mul_of_nonneg_left (hle1 (y - s) (p + 2) (by linarith)) hK
    simp only [hF']; linarith
  obtain ⟨j1, -, hibp⟩ := c07_aux_ibp_Ioi (p + 1) w (by linarith) hw F F' hFd
    (by simp only [hF']; fun_prop) _ _ hB0 hB1
  -- second integration by parts
  set G : ℝ → ℝ := fun s => h (y + s) + h (y - s) with hG
  have hGd : ∀ s, HasDerivAt G (F s) s := fun s => by
    have h1 := (hhd (y + s)).hasDerivAt.comp s ((hasDerivAt_id s).const_add y)
    have h2 := (hhd (y - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub y)
    convert h1.add h2 using 1
    · rfl
    · simp only [hF]; ring
  have hG0 : ∀ s, |G s| ≤ 2 * K := fun s => by
    have := abs_add_le (h (y + s)) (h (y - s))
    have a1 := (hbd (y + s)).1; have a2 := (hbd (y - s)).1
    have := mul_le_mul_of_nonneg_left (hle1 (y + s) p hp.le) hK
    have := mul_le_mul_of_nonneg_left (hle1 (y - s) p hp.le) hK
    simp only [hG]; linarith
  obtain ⟨-, -, hibp2⟩ := c07_aux_ibp_Ioi (p + 2) w (by linarith) hw G F hGd
    (by simp only [hF]; fun_prop) _ _ hG0 hB0
  refine ⟨j1, ?_⟩
  rw [show (fun s => s ^ (-(p + 1)) * (deriv (deriv h) (y + s) + deriv (deriv h) (y - s))) =
    fun s => s ^ (-(p + 1)) * F' s from rfl, hibp,
    show -(p + 1) - 1 = -(p + 2) by ring, hibp2]
  obtain ⟨hTi, hT2⟩ := hT y hy
  have hyw1 : w ≤ |y + w| := by
    have := abs_sub_abs_le_abs_sub y (-w); rw [sub_neg_eq_add, abs_neg, abs_of_pos hw] at this
    rw [hwd] at this ⊢; linarith
  have hyw2 : w ≤ |y - w| := by
    have := abs_sub_abs_le_abs_sub y w; rw [abs_of_pos hw] at this
    rw [hwd] at this ⊢; linarith
  have hFw : |F w| ≤ 2 * K * w ^ (-(p + 1)) := by
    have := abs_sub (deriv h (y + w)) (deriv h (y - w))
    have a1 := (hbd (y + w)).2.1; have a2 := (hbd (y - w)).2.1
    have := mul_le_mul_of_nonneg_left (c07_aux_jb_le_w _ w (p + 1) hw hyw1 (by linarith)) hK
    have := mul_le_mul_of_nonneg_left (c07_aux_jb_le_w _ w (p + 1) hw hyw2 (by linarith)) hK
    simp only [hF]; linarith
  have hGw : |G w| ≤ 2 * K * w ^ (-p) := by
    have := abs_add_le (h (y + w)) (h (y - w))
    have a1 := (hbd (y + w)).1; have a2 := (hbd (y - w)).1
    have := mul_le_mul_of_nonneg_left (c07_aux_jb_le_w _ w p hw hyw1 hp.le) hK
    have := mul_le_mul_of_nonneg_left (c07_aux_jb_le_w _ w p hw hyw2 hp.le) hK
    simp only [hG]; linarith
  have hint : |∫ s in Ioi w, s ^ (-(p + 2) - 1) * G s| ≤ K * (Ch * w ^ (-(2 * p + 2))) := by
    have hb : ∀ s ∈ Ioi w, ‖s ^ (-(p + 2) - 1) * G s‖ ≤
        K * (s ^ (-(p + 3)) * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p))) := by
      intro s hs
      have hs0 : 0 < s := lt_trans hw hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
        show -(p + 2) - 1 = -(p + 3) by ring]
      have := abs_add_le (h (y + s)) (h (y - s))
      have a1 := (hbd (y + s)).1; have a2 := (hbd (y - s)).1
      have hG1 : |G s| ≤ K * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p)) := by
        simp only [hG]; linarith
      calc s ^ (-(p + 3)) * |G s| ≤ s ^ (-(p + 3)) * (K * (jb (y + s) ^ (-p) + jb (y - s) ^ (-p))) :=
            mul_le_mul_of_nonneg_left hG1 (Real.rpow_nonneg hs0.le _)
        _ = _ := by ring
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hTi.const_mul K)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb))).trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left (hT2.trans ?_) hK
    refine mul_le_mul_of_nonneg_left ?_ hCh.le
    rw [show 1 - p - (p + 3) = -(2 * p + 2) by ring]
    exact Real.rpow_le_rpow_of_nonpos hw (by rw [hwd]; linarith) (by linarith)
  have e1 : w ^ (-(p + 1)) * w ^ (-(p + 1)) = w ^ (-(2 * p + 1 + 1)) := by
    rw [← Real.rpow_add hw]; ring_nf
  have e2 : w ^ (-(p + 2)) * w ^ (-p) = w ^ (-(2 * p + 1 + 1)) := by
    rw [← Real.rpow_add hw]; ring_nf
  have e3 : w ^ (-(2 * p + 2)) = w ^ (-(2 * p + 1 + 1)) := by ring_nf
  have hwp : 0 ≤ w ^ (-(p + 1)) := Real.rpow_nonneg hw.le _
  have hwp2 : 0 ≤ w ^ (-(p + 2)) := Real.rpow_nonneg hw.le _
  have hp1' : (0:ℝ) < p + 1 := by linarith
  have hp2' : (0:ℝ) < p + 2 := by linarith
  calc |-(w ^ (-(p + 1)) * F w) + (p + 1) * (-(w ^ (-(p + 2)) * G w) +
        (p + 2) * ∫ s in Ioi w, s ^ (-(p + 2) - 1) * G s)|
      ≤ w ^ (-(p + 1)) * |F w| + (p + 1) * (w ^ (-(p + 2)) * |G w| +
          (p + 2) * |∫ s in Ioi w, s ^ (-(p + 2) - 1) * G s|) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hwp, abs_of_pos hp1']
        gcongr
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hwp2, abs_of_pos hp2']
    _ ≤ w ^ (-(p + 1)) * (2 * K * w ^ (-(p + 1))) + (p + 1) * (w ^ (-(p + 2)) * (2 * K * w ^ (-p)) +
          (p + 2) * (K * (Ch * w ^ (-(2 * p + 2))))) := by gcongr
    _ = K * (2 + 2 * (p + 1) + (p + 1) * (p + 2) * Ch) * w ^ (-(2 * p + 1 + 1)) := by
        rw [e3]
        have : w ^ (-(p + 1)) * (2 * K * w ^ (-(p + 1))) = 2 * K * w ^ (-(2 * p + 1 + 1)) := by
          rw [← e1]; ring
        have h2 : w ^ (-(p + 2)) * (2 * K * w ^ (-p)) = 2 * K * w ^ (-(2 * p + 1 + 1)) := by
          rw [← e2]; ring
        rw [this, h2]; ring

/-- `C¹` regularity of `|D|^p h'` and `∂_y |D|^p h' = |D|^p h''`. -/
theorem c07_aux_frac_C1 (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (K : ℝ) (hK : 0 ≤ K) (h : ℝ → ℝ)
    (hh : ContDiff ℝ 3 h) (hb : ∀ i ≤ 3, ∀ y : ℝ, |iteratedDeriv i h y| ≤ K * jb y ^ (-p - i)) :
    ContDiff ℝ 1 (fracDdy p h) ∧ deriv (fracDdy p h) = fracDdy p (deriv h) := by
  have hbd := c07_aux_h_bounds p K h hb
  have hle1 : ∀ x e : ℝ, 0 ≤ e → jb x ^ (-e) ≤ 1 := fun x e he => c07_aux_jb_rpow_neg_le_one x e he
  have hd1 : ContDiff ℝ 2 (deriv h) := (hh.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hd1d : Differentiable ℝ (deriv h) := hd1.differentiable (by norm_num)
  have hd2 : ContDiff ℝ 1 (deriv (deriv h)) := (hd1.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hd2d : Differentiable ℝ (deriv (deriv h)) := hd2.differentiable (by norm_num)
  have hd2c : Continuous (deriv (deriv h)) := hd2.continuous
  have hd1c : Continuous (deriv h) := hd1.continuous
  have hB1 : ∀ x, |deriv h x| ≤ K := fun x =>
    (hbd x).2.1.trans (by have := mul_le_mul_of_nonneg_left (hle1 x (p + 1) (by linarith)) hK; linarith)
  have hB2 : ∀ x, |deriv (deriv h) x| ≤ K := fun x =>
    (hbd x).2.2.1.trans (by have := mul_le_mul_of_nonneg_left (hle1 x (p + 2) (by linarith)) hK; linarith)
  have hB3 : ∀ x, |deriv (deriv (deriv h)) x| ≤ K := fun x =>
    (hbd x).2.2.2.trans (by have := mul_le_mul_of_nonneg_left (hle1 x (p + 3) (by linarith)) hK; linarith)
  set D : ℝ → ℝ → ℝ := fun y s => (deriv h y - deriv h (y - s)) / |s| ^ (p + 1) with hD
  set D' : ℝ → ℝ → ℝ := fun y s => (deriv (deriv h) y - deriv (deriv h) (y - s)) / |s| ^ (p + 1)
    with hD'
  have hrep : ∀ (g : ℝ → ℝ) y, fracD p g y = calpha p * ∫ s, (g y - g (y - s)) / |s| ^ (p + 1) := by
    intro g y
    unfold fracD; congr 1
    rw [← integral_sub_left_eq_self _ volume y]; simp [sub_sub_cancel]
  obtain ⟨hni, -⟩ := c07_aux_near_int 1 p one_pos hp hp1
  obtain ⟨hfi, -⟩ := c07_aux_far_int 1 (p + 1) 0 one_pos (by linarith)
  set bound : ℝ → ℝ := fun s => K * {s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s +
    2 * K * {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(p + 1))) s with hbound
  have hbi : Integrable bound := (hni.const_mul K).add (hfi.const_mul _)
  have hbb : ∀ y s, ‖D' y s‖ ≤ bound s := by
    intro y s
    have n1 : 0 ≤ {s : ℝ | |s| ≤ 1}.indicator (fun s => |s| ^ (-p)) s :=
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
    have n2 : 0 ≤ {z : ℝ | 1 ≤ |0 - z|}.indicator (fun z => |0 - z| ^ (-(p + 1))) s :=
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
    rcases eq_or_ne s 0 with rfl | hs
    · simp only [hD', sub_zero, sub_self, zero_div, norm_zero, hbound]; positivity
    have hsa : 0 < |s| := abs_pos.2 hs
    rw [Real.norm_eq_abs]
    simp only [hD', hbound]
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hsa _), div_eq_mul_inv, ← Real.rpow_neg hsa.le]
    by_cases h1 : |s| ≤ 1
    · rw [indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ 1} from h1)]
      have hmv : |deriv (deriv h) y - deriv (deriv h) (y - s)| ≤ K * |s| := by
        have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := deriv (deriv h)) (C := K)
          (fun x _ => hd2d x) (fun x _ => by rw [Real.norm_eq_abs]; exact hB3 x) convex_univ
          (mem_univ (y - s)) (mem_univ y)
        simpa [Real.norm_eq_abs] using this
      have e : |s| * |s| ^ (-(p + 1)) = |s| ^ (-p) := by
        have : |s| * |s| ^ (-(p + 1)) = |s| ^ ((1:ℝ) + -(p + 1)) := by
          rw [Real.rpow_add hsa, Real.rpow_one]
        rw [this]; ring_nf
      calc |deriv (deriv h) y - deriv (deriv h) (y - s)| * |s| ^ (-(p + 1))
          ≤ K * |s| * |s| ^ (-(p + 1)) := mul_le_mul_of_nonneg_right hmv (Real.rpow_nonneg hsa.le _)
        _ = K * |s| ^ (-p) := by rw [mul_assoc, e]
        _ ≤ _ := by have := mul_nonneg (by positivity : (0:ℝ) ≤ 2 * K) n2; linarith
    · push_neg at h1
      rw [indicator_of_mem (show s ∈ {z : ℝ | 1 ≤ |0 - z|} by
        show 1 ≤ |0 - s|; rw [zero_sub, abs_neg]; exact h1.le), zero_sub, abs_neg]
      have : |deriv (deriv h) y - deriv (deriv h) (y - s)| ≤ 2 * K := by
        have := abs_sub (deriv (deriv h) y) (deriv (deriv h) (y - s)); linarith [hB2 y, hB2 (y - s)]
      calc _ ≤ 2 * K * |s| ^ (-(p + 1)) := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hsa.le _)
        _ ≤ _ := by have := mul_nonneg hK n1; linarith
  have hmD : ∀ y, Measurable (D y) := fun y => by
    have := hd1c.measurable; simp only [hD]; fun_prop
  have hmD' : ∀ y, Measurable (D' y) := fun y => by
    have := hd2c.measurable; simp only [hD']; fun_prop
  have hDi : ∀ y, Integrable (D y) := fun y => by
    have := (c07_aux_D_integrable p hp hp1 h (hh.of_le (by norm_num)) K hB1 y).comp_sub_left y
    simpa [hD, sub_sub_cancel] using this
  have hdiff : ∀ y s, HasDerivAt (fun y' => D y' s) (D' y s) y := by
    intro y s
    have := ((hd1d y).hasDerivAt.sub ((hd1d (y - s)).hasDerivAt.comp y
      ((hasDerivAt_id y).sub_const s))).div_const (|s| ^ (p + 1))
    simpa [hD, hD'] using this
  have hderiv : ∀ y, HasDerivAt (fracDdy p h) (fracDdy p (deriv h) y) y := by
    intro y
    obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := D)
      (F' := D') (x₀ := y) (bound := bound) (Metric.ball_mem_nhds y one_pos)
      (Eventually.of_forall fun y' => (hmD y').aestronglyMeasurable) (hDi y)
      (hmD' y).aestronglyMeasurable (Eventually.of_forall fun s y' _ => hbb y' s) hbi
      (Eventually.of_forall fun s y' _ => hdiff y' s)
    have e1 : fracDdy p h = fun y' => calpha p * ∫ s, D y' s := funext fun y' => hrep _ y'
    have e2 : fracDdy p (deriv h) y = calpha p * ∫ s, D' y s := hrep _ y
    rw [e1, e2]; exact hd.const_mul _
  have hdeq : deriv (fracDdy p h) = fracDdy p (deriv h) := funext fun y => (hderiv y).deriv
  refine ⟨contDiff_one_iff_deriv.2 ⟨fun y => (hderiv y).differentiableAt, ?_⟩, hdeq⟩
  rw [hdeq]
  have e2 : fracDdy p (deriv h) = fun y => calpha p * ∫ s, D' y s := funext fun y => hrep _ y
  rw [e2]
  refine continuous_const.mul (continuous_of_dominated (fun y => (hmD' y).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun s => hbb y s) hbi (Eventually.of_forall fun s => ?_))
  simp only [hD']; fun_prop

/-- Blueprint: lem:c07_fractional_decay.  If `h ∈ C³` with `|h^{(i)}(y)| ≤ K⟨y⟩^{-p-i}`
(`i ≤ 3`), then `|D|^p h' ∈ C¹`, `∂_y |D|^p h' = |D|^p h''`, and
`|∂^j_y |D|^p h'(y)| ≤ C K ⟨y⟩^{-2p-1-j}` for `|y| ≥ 1`, `j ∈ {0,1}`, with `C = C(p)`. -/
theorem c07_fractional_decay (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 0 ≤ K → ∀ h : ℝ → ℝ, ContDiff ℝ 3 h →
      (∀ i ≤ 3, ∀ y : ℝ, |iteratedDeriv i h y| ≤ K * jb y ^ (-p - i)) →
      ContDiff ℝ 1 (fracDdy p h) ∧
      deriv (fracDdy p h) = fracDdy p (deriv h) ∧
      ∀ j ≤ 1, ∀ y : ℝ, 1 ≤ |y| →
        |iteratedDeriv j (fracDdy p h) y| ≤ C * K * jb y ^ (-2 * p - 1 - j) := by
  obtain ⟨Ch2, hCh2, hT2⟩ := c07_aux_tail_half p (p + 2) hp hp1 (by linarith)
  obtain ⟨Ch3, hCh3, hT3⟩ := c07_aux_tail_half p (p + 3) hp hp1 (by linarith)
  have hc := c03_aux_calpha_pos p hp hp1
  set A := 2 / (1 - p) + 2 / p with hA
  have hA0 : 0 < A := by have : 0 < 1 - p := by linarith
                         positivity
  set B0 := 2 + (p + 1) * Ch2 with hB0
  set B1 := 2 + 2 * (p + 1) + (p + 1) * (p + 2) * Ch3 with hB1
  have hB00 : 0 < B0 := by positivity
  have hB10 : 0 < B1 := by positivity
  refine ⟨256 * calpha p * (A + B0 + B1), by positivity, fun K hK h hh hb => ?_⟩
  obtain ⟨hC1, hdeq⟩ := c07_aux_frac_C1 p hp hp1 K hK h hh hb
  refine ⟨hC1, hdeq, fun j hj y hy => ?_⟩
  have hbd := c07_aux_h_bounds p K h hb
  have hle1 : ∀ x e : ℝ, 0 ≤ e → jb x ^ (-e) ≤ 1 := fun x e he => c07_aux_jb_rpow_neg_le_one x e he
  set w := |y| / 2 with hwd
  have hw : 0 < w := by linarith
  have hd1 : ContDiff ℝ 2 (deriv h) := (hh.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hd2 : ContDiff ℝ 1 (deriv (deriv h)) := (hd1.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hywx : ∀ x ∈ Icc (y - w) (y + w), w ≤ |x| := by
    intro x hx
    have := abs_sub_abs_le_abs_sub y x
    have : |y - x| ≤ w := abs_le.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rw [hwd] at *; linarith
  have hyw : w ≤ |y| := by rw [hwd]; linarith
  -- convert `w^{-e}` to `⟨y⟩^{-e}`
  have hconv : ∀ e : ℝ, 0 ≤ e → e ≤ 4 → w ^ (-e) ≤ 256 * jb y ^ (-e) := by
    intro e he0 he4
    rw [hwd, (c07_aux_rpow_div |y| 2 (-e) (abs_nonneg _) two_pos).1, neg_neg]
    have h2 : (2 : ℝ) ^ e ≤ 16 := by
      calc (2 : ℝ) ^ e ≤ 2 ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he4
        _ = 16 := by norm_num
    have h3 := c07_aux_abs_rpow_le_jb y (-e) hy (by linarith) (by linarith)
    have : 0 ≤ |y| ^ (-e) := Real.rpow_nonneg (abs_nonneg _) _
    calc 2 ^ e * |y| ^ (-e) ≤ 16 * (16 * jb y ^ (-e)) := mul_le_mul h2 h3 this (by norm_num)
      _ = _ := by ring
  have hjbw : ∀ x e : ℝ, 0 ≤ e → w ≤ |x| → jb x ^ (-e) ≤ w ^ (-e) := fun x e he hx =>
    c07_aux_jb_le_w x w e hw hx he
  have hfin : ∀ (J : ℝ) (Bf : ℝ), 0 ≤ J → J ≤ 1 → Bf ≤ B0 + B1 →
      |iteratedDeriv j (fracDdy p h) y| ≤ calpha p * K * (A + Bf) * w ^ (-(2 * p + 1 + J)) →
      J = j → |iteratedDeriv j (fracDdy p h) y| ≤ 256 * calpha p * (A + B0 + B1) * K *
        jb y ^ (-2 * p - 1 - j) := by
    intro J Bf hJ0 hJ1 hBf hle hJ
    have e : -(2 * p + 1 + J) = -2 * p - 1 - j := by rw [← hJ]; ring
    rw [e] at hle
    have hc2 := hconv (2 * p + 1 + J) (by linarith) (by linarith)
    rw [e] at hc2
    refine hle.trans ?_
    have hW : 0 ≤ w ^ (-2 * p - 1 - (j : ℝ)) := Real.rpow_nonneg hw.le _
    calc calpha p * K * (A + Bf) * w ^ (-2 * p - 1 - (j : ℝ))
        ≤ calpha p * K * (A + B0 + B1) * w ^ (-2 * p - 1 - (j : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hW
      _ ≤ calpha p * K * (A + B0 + B1) * (256 * jb y ^ (-2 * p - 1 - (j : ℝ))) := by gcongr
      _ = _ := by ring
  interval_cases j
  · -- `j = 0`, `g = h'`
    refine hfin 0 B0 le_rfl zero_le_one (by linarith) ?_ (by simp)
    rw [iteratedDeriv_zero]
    obtain ⟨hfi, hfb⟩ := c07_aux_far0 p hp hp1 Ch2 hCh2 hT2 K hK h hh hb y hy
    have := c07_aux_frac_core p hp hp1 (deriv h) (hd1.differentiable (by norm_num)) y w K 0 B0 hw hK
      (c07_aux_D_integrable p hp hp1 h (hh.of_le (by norm_num)) K
        (fun x => (hbd x).2.1.trans (by
          have := mul_le_mul_of_nonneg_left (hle1 x (p + 1) (by linarith)) hK; linarith)) y)
      ((hbd y).2.1.trans (by
        have := mul_le_mul_of_nonneg_left (hjbw y (p + 1) (by linarith) hyw) hK
        rw [add_zero]; exact this))
      (fun x hx => (hbd x).2.2.1.trans (by
        have := mul_le_mul_of_nonneg_left (hjbw x (p + 2) (by linarith) (hywx x hx)) hK
        rw [add_zero]; exact this))
      hfi (by rw [hwd]; exact hfb)
    simpa [fracDdy] using this
  · -- `j = 1`, `g = h''`
    refine hfin 1 B1 zero_le_one le_rfl (by linarith) ?_ (by simp)
    rw [iteratedDeriv_one, hdeq]
    obtain ⟨hfi, hfb⟩ := c07_aux_far1 p hp hp1 Ch3 hCh3 hT3 K hK h hh hb y hy
    have hB2 : ∀ x, |deriv (deriv h) x| ≤ K := fun x => (hbd x).2.2.1.trans (by
      have := mul_le_mul_of_nonneg_left (hle1 x (p + 2) (by linarith)) hK; linarith)
    have := c07_aux_frac_core p hp hp1 (deriv (deriv h)) (hd2.differentiable (by norm_num)) y w K 1 B1
      hw hK
      (c07_aux_D_integrable p hp hp1 (deriv h) hd1 K hB2 y)
      ((hbd y).2.2.1.trans (by
        have := mul_le_mul_of_nonneg_left (hjbw y (p + 2) (by linarith) hyw) hK
        rw [show p + 1 + 1 = p + 2 by ring]; exact this))
      (fun x hx => (hbd x).2.2.2.trans (by
        have := mul_le_mul_of_nonneg_left (hjbw x (p + 3) (by linarith) (hywx x hx)) hK
        rw [show p + 2 + 1 = p + 3 by ring]; exact this))
      hfi (by rw [hwd]; exact hfb)
    simpa [fracDdy] using this


/-- `∫_{(0,1]} s^{-p} ds = 1/(1-p)` and integrability. -/
theorem c07_aux_Ioc_rpow (p : ℝ) (hp1 : p < 1) :
    IntegrableOn (fun s : ℝ => s ^ (-p)) (Ioc 0 1) ∧ ∫ s in Ioc (0:ℝ) 1, s ^ (-p) = 1 / (1 - p) := by
  have hr : -1 < -p := by linarith
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
    (intervalIntegral.intervalIntegrable_rpow' hr), ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith)]
  have : (1 - p) ≠ 0 := by linarith
  rw [show -p + 1 = 1 - p by ring]; field_simp; norm_num

/-- Bounded measurable `w` against `s^{-q}` on `(1,∞)`. -/
theorem c07_aux_Ioi_one_bound (q : ℝ) (hq : 1 < q) (w : ℝ → ℝ) (hw : Measurable w) (B : ℝ)
    (hB : ∀ s, |w s| ≤ B) :
    IntegrableOn (fun s => s ^ (-q) * w s) (Ioi 1) ∧
      |∫ s in Ioi (1:ℝ), s ^ (-q) * w s| ≤ B / (q - 1) := by
  have i1 : IntegrableOn (fun s : ℝ => s ^ (-q)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hpos : ∀ s ∈ Ioi (1:ℝ), 0 < s := fun s hs => lt_trans one_pos hs
  have hle : ∀ s ∈ Ioi (1:ℝ), ‖s ^ (-q) * w s‖ ≤ s ^ (-q) * B := fun s hs => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hpos s hs).le _)]
    exact mul_le_mul_of_nonneg_left (hB s) (Real.rpow_nonneg (hpos s hs).le _)
  have j : IntegrableOn (fun s => s ^ (-q) * w s) (Ioi 1) :=
    (i1.mul_const B).mono' (by fun_prop)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hle))
  refine ⟨j, ?_⟩
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (i1.mul_const B)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hle))).trans (le_of_eq ?_)
  rw [integral_mul_const, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
  have : (-q + 1) ≠ 0 := by linarith
  have : (q - 1) ≠ 0 := by linarith
  rw [show -q + 1 = -(q - 1) by ring]; field_simp


/-- Pointwise bound for the near symmetric difference quotient. -/
theorem c07_aux_near_pt (p : ℝ) (g : ℝ → ℝ) (y B s : ℝ)
    (hd : ∀ x ∈ Icc (y - 1) (y + 1), DifferentiableAt ℝ g x)
    (hB : ∀ x ∈ Icc (y - 1) (y + 1), |deriv g x| ≤ B) (hs : s ∈ Ioc (0:ℝ) 1) :
    |(2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1)| ≤ 2 * B * s ^ (-p) := by
  obtain ⟨hs0, hs1⟩ := hs
  have hmv : ∀ x ∈ Icc (y - 1) (y + 1), |g y - g x| ≤ B * |y - x| := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (C := B)
      (fun x hx => hd x hx) (fun x hx => by rw [Real.norm_eq_abs]; exact hB x hx) (convex_Icc _ _)
      hx (show y ∈ Icc (y - 1) (y + 1) from ⟨by linarith, by linarith⟩)
    simpa [Real.norm_eq_abs] using this
  have h1 := hmv (y - s) ⟨by linarith, by linarith⟩
  have h2 := hmv (y + s) ⟨by linarith, by linarith⟩
  rw [show y - (y - s) = s by ring, abs_of_pos hs0] at h1
  rw [show y - (y + s) = -s by ring, abs_neg, abs_of_pos hs0] at h2
  have hnum : |2 * g y - g (y - s) - g (y + s)| ≤ 2 * B * s := by
    have := abs_add_le (g y - g (y - s)) (g y - g (y + s))
    rw [show g y - g (y - s) + (g y - g (y + s)) = 2 * g y - g (y - s) - g (y + s) by ring] at this
    linarith
  have hsp : 0 < s ^ (p + 1) := Real.rpow_pos_of_pos hs0 _
  rw [abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
  have e : s ^ (-p) * s ^ (p + 1) = s := by
    rw [← Real.rpow_add hs0]; simp
  calc |2 * g y - g (y - s) - g (y + s)| ≤ 2 * B * s := hnum
    _ = 2 * B * s ^ (-p) * s ^ (p + 1) := by rw [mul_assoc (2 * B) (s ^ (-p)), e]

/-- The near part `N_g(y) = ∫_{(0,1]} (2g(y)-g(y-s)-g(y+s)) s^{-1-p} ds` for `g ∈ C¹`:
integrability, the bound `2B/(1-p)`, continuity. -/
theorem c07_aux_near_C0 (p : ℝ) (hp1 : p < 1) (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    (∀ y, IntegrableOn (fun s => (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1)) (Ioc 0 1)) ∧
    (∀ y B, (∀ x ∈ Icc (y - 1) (y + 1), |deriv g x| ≤ B) →
      |∫ s in Ioc (0:ℝ) 1, (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1)| ≤ 2 * B / (1 - p)) ∧
    Continuous (fun y => ∫ s in Ioc (0:ℝ) 1, (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1)) := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hgc : Continuous g := hg.continuous
  have hdc : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  obtain ⟨hi, hI⟩ := c07_aux_Ioc_rpow p hp1
  set F : ℝ → ℝ → ℝ := fun y s => (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1) with hF
  have hmeas : ∀ y, Measurable (F y) := fun y => by
    have := hgc.measurable; simp only [hF]; fun_prop
  -- local bound: on `ball y₀ 1`, `|g'| ≤ B(y₀)` on the relevant intervals
  have hloc : ∀ y₀ : ℝ, ∃ B, 0 ≤ B ∧ ∀ y ∈ Metric.ball y₀ 1, ∀ s ∈ Ioc (0:ℝ) 1,
      ‖F y s‖ ≤ 2 * B * s ^ (-p) := by
    intro y₀
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := y₀ - 2) (b := y₀ + 2)).exists_bound_of_continuousOn
      hdc.continuousOn
    refine ⟨max B 0, le_max_right _ _, fun y hy s hs => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    rw [Real.norm_eq_abs]
    refine c07_aux_near_pt p g y _ s (fun x _ => hgd x) (fun x hx => ?_) hs
    have := hB x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hint : ∀ y, IntegrableOn (F y) (Ioc 0 1) := by
    intro y
    obtain ⟨B, hB0, hB⟩ := hloc y
    exact ((hi.const_mul (2 * B))).mono' (hmeas y).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs =>
        hB y (Metric.mem_ball_self one_pos) s hs))
  refine ⟨hint, fun y B hB => ?_, ?_⟩
  · rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hi.const_mul (2 * B))
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_))).trans
      (le_of_eq ?_)
    · rw [Real.norm_eq_abs]
      exact c07_aux_near_pt p g y B s (fun x _ => hgd x) hB hs
    · rw [integral_const_mul, hI]; ring
  · refine continuous_iff_continuousAt.2 fun y₀ => ?_
    obtain ⟨B, hB0, hB⟩ := hloc y₀
    refine continuousAt_of_dominated (bound := fun s => 2 * B * s ^ (-p))
      (Eventually.of_forall fun y => (hmeas y).aestronglyMeasurable)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ one_pos) fun y hy =>
        (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => hB y hy s hs))
      (hi.const_mul (2 * B)) (Eventually.of_forall fun s => ?_)
    exact (by fun_prop : Continuous fun y => (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1)).continuousAt

/-- Differentiation of the near part (`g ∈ C²`). -/
theorem c07_aux_near_deriv (p : ℝ) (hp1 : p < 1) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ s in Ioc (0:ℝ) 1, (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1))
      (∫ s in Ioc (0:ℝ) 1, (2 * deriv g y₀ - deriv g (y₀ - s) - deriv g (y₀ + s)) / s ^ (p + 1))
      y₀ := by
  have hg1 : ContDiff ℝ 1 (deriv g) := (hg.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg1d : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  have hd2c : Continuous (deriv (deriv g)) := hg1.continuous_deriv (by norm_num)
  obtain ⟨hi, -⟩ := c07_aux_Ioc_rpow p hp1
  obtain ⟨hint0, -, -⟩ := c07_aux_near_C0 p hp1 g (hg.of_le (by norm_num))
  obtain ⟨hint1, -, -⟩ := c07_aux_near_C0 p hp1 (deriv g) hg1
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := y₀ - 2) (b := y₀ + 2)).exists_bound_of_continuousOn
    hd2c.continuousOn
  have hgc : Continuous g := hg.continuous
  have hg1c : Continuous (deriv g) := hg1.continuous
  have hm1 : Measurable (fun s : ℝ =>
      (2 * deriv g y₀ - deriv g (y₀ - s) - deriv g (y₀ + s)) / s ^ (p + 1)) := by
    have := hg1c.measurable; fun_prop
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0:ℝ) 1))
    (F := fun y s => (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1))
    (F' := fun y s => (2 * deriv g y - deriv g (y - s) - deriv g (y + s)) / s ^ (p + 1))
    (x₀ := y₀) (bound := fun s => 2 * B * s ^ (-p)) (Metric.ball_mem_nhds y₀ one_pos)
    (Eventually.of_forall fun y => (by have := hgc.measurable; fun_prop :
      Measurable (fun s : ℝ => (2 * g y - g (y - s) - g (y + s)) / s ^ (p + 1))).aestronglyMeasurable)
    (hint0 y₀) hm1.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs y hy => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
      rw [Real.norm_eq_abs]
      refine c07_aux_near_pt p (deriv g) y B s (fun x _ => hg1d x) (fun x hx => ?_) hs
      have := hB x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rwa [Real.norm_eq_abs] at this))
    (hi.const_mul (2 * B))
    (Eventually.of_forall fun s y _ => by
      have a := (hgd y).hasDerivAt.const_mul 2
      have b := (hgd (y - s)).hasDerivAt.comp y ((hasDerivAt_id y).sub_const s)
      have c := (hgd (y + s)).hasDerivAt.comp y ((hasDerivAt_id y).add_const s)
      have hA : HasDerivAt (fun x => 2 * g x - g (x - s) - g (x + s))
          (2 * deriv g y - deriv g (y - s) - deriv g (y + s)) y := by
        convert (a.sub b).sub c using 1 <;> first | (funext x; simp) | simp
      exact hA.div_const _)
  exact hd


/-- The far part `G(y) = ∫_{(1,∞)} s^{-α-1}(u(y+s)-u(y-s)) ds` for bounded `u ∈ C¹` with bounded `u'`:
derivative, continuity of the derivative and bounds. -/
theorem c07_aux_far_part (p : ℝ) (hp : 0 < p) (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (S L : ℝ)
    (hS : ∀ y, |u y| ≤ S) (hL : ∀ y, |deriv u y| ≤ L) :
    (∀ y, HasDerivAt (fun y => ∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (u (y + s) - u (y - s)))
      (∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (deriv u (y + s) - deriv u (y - s))) y) ∧
    Continuous (fun y => ∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (deriv u (y + s) - deriv u (y - s))) ∧
    (∀ y, |∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (u (y + s) - u (y - s))| ≤ 2 * S / (p + 1)) ∧
    (∀ y, |∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (deriv u (y + s) - deriv u (y - s))| ≤
      |u (y + 1)| + |u (y - 1)| + 2 * S) := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have huc : Continuous u := hu.continuous
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hq : (1:ℝ) < p + 1 + 1 := by linarith
  have e1 : -(p + 1) - 1 = -(p + 1 + 1) := by ring
  have i1 : IntegrableOn (fun s : ℝ => s ^ (-(p + 1) - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hpos : ∀ s ∈ Ioi (1:ℝ), 0 < s := fun s hs => lt_trans one_pos hs
  have hderb : ∀ y s, s ∈ Ioi (1:ℝ) →
      ‖s ^ (-(p + 1) - 1) * (deriv u (y + s) - deriv u (y - s))‖ ≤ s ^ (-(p + 1) - 1) * (2 * L) := by
    intro y s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hpos s hs).le _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hpos s hs).le _)
    have := abs_sub (deriv u (y + s)) (deriv u (y - s)); linarith [hL (y + s), hL (y - s)]
  have hm : ∀ y, Measurable (fun s : ℝ => s ^ (-(p + 1) - 1) * (u (y + s) - u (y - s))) := fun y => by
    have := huc.measurable; fun_prop
  have hm' : ∀ y, Measurable (fun s : ℝ => s ^ (-(p + 1) - 1) * (deriv u (y + s) - deriv u (y - s))) :=
    fun y => by have := hdc.measurable; fun_prop
  refine ⟨fun y₀ => ?_, ?_, fun y => ?_, fun y => ?_⟩
  · obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1:ℝ)))
      (F := fun y s => s ^ (-(p + 1) - 1) * (u (y + s) - u (y - s)))
      (F' := fun y s => s ^ (-(p + 1) - 1) * (deriv u (y + s) - deriv u (y - s)))
      (x₀ := y₀) (bound := fun s => s ^ (-(p + 1) - 1) * (2 * L)) (Metric.ball_mem_nhds y₀ one_pos)
      (Eventually.of_forall fun y => (hm y).aestronglyMeasurable)
      ((c07_aux_Ioi_one_bound (p + 1 + 1) hq (fun s => u (y₀ + s) - u (y₀ - s)) (by have := huc.measurable; fun_prop) (2 * S)
        (fun s => by have := abs_sub (u (y₀ + s)) (u (y₀ - s)); linarith [hS (y₀ + s), hS (y₀ - s)])).1
        |>.congr_fun (fun s _ => by rw [e1]) measurableSet_Ioi)
      (hm' y₀).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs y _ => hderb y s hs))
      (i1.mul_const _)
      (Eventually.of_forall fun s y _ => by
        have b := (hud (y + s)).hasDerivAt.comp y ((hasDerivAt_id y).add_const s)
        have c := (hud (y - s)).hasDerivAt.comp y ((hasDerivAt_id y).sub_const s)
        have hA : HasDerivAt (fun x => u (x + s) - u (x - s)) (deriv u (y + s) - deriv u (y - s)) y := by
          convert b.sub c using 1 <;> first | (funext x; simp) | simp
        exact hA.const_mul _)
    exact hd
  · refine continuous_of_dominated (bound := fun s => s ^ (-(p + 1) - 1) * (2 * L))
      (fun y => (hm' y).aestronglyMeasurable)
      (fun y => (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => hderb y s hs))
      (i1.mul_const _) (Eventually.of_forall fun s => by fun_prop)
  · have := (c07_aux_Ioi_one_bound (p + 1 + 1) hq (fun s => u (y + s) - u (y - s))
      (by have := huc.measurable; fun_prop) (2 * S)
      (fun s => by have := abs_sub (u (y + s)) (u (y - s)); linarith [hS (y + s), hS (y - s)])).2
    rw [e1]; convert this using 2; ring
  · obtain ⟨-, -, hibp⟩ := c07_aux_ibp_Ioi (p + 1 + 1) 1 hq one_pos (fun s => u (y + s) + u (y - s))
      (fun s => deriv u (y + s) - deriv u (y - s))
      (fun s => by
        have b := (hud (y + s)).hasDerivAt.comp s ((hasDerivAt_id s).const_add y)
        have c := (hud (y - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub y)
        convert b.add c using 1 <;> first | (funext x; simp) | simp; ring)
      (by fun_prop) (2 * S) (2 * L)
      (fun s => by have := abs_add_le (u (y + s)) (u (y - s)); linarith [hS (y + s), hS (y - s)])
      (fun s => by have := abs_sub (deriv u (y + s)) (deriv u (y - s)); linarith [hL (y + s), hL (y - s)])
    rw [e1, hibp, Real.one_rpow, one_mul]
    have hb := (c07_aux_Ioi_one_bound (p + 1 + 1 + 1) (by linarith) (fun s => u (y + s) + u (y - s))
      (by have := huc.measurable; fun_prop) (2 * S)
      (fun s => by have := abs_add_le (u (y + s)) (u (y - s)); linarith [hS (y + s), hS (y - s)])).2
    rw [show -(p + 1 + 1) - 1 = -(p + 1 + 1 + 1) by ring]
    have hq0 : 0 < p + 1 + 1 := by linarith
    calc |-(u (y + 1) + u (y - 1)) + (p + 1 + 1) *
          ∫ s in Ioi (1:ℝ), s ^ (-(p + 1 + 1 + 1)) * (u (y + s) + u (y - s))|
        ≤ |u (y + 1) + u (y - 1)| + (p + 1 + 1) *
          |∫ s in Ioi (1:ℝ), s ^ (-(p + 1 + 1 + 1)) * (u (y + s) + u (y - s))| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_neg, abs_mul, abs_of_pos hq0]
      _ ≤ |u (y + 1)| + |u (y - 1)| + (p + 1 + 1) * (2 * S / (p + 1 + 1 + 1 - 1)) := by
          gcongr
          exact abs_add_le _ _
      _ = _ := by rw [show p + 1 + 1 + 1 - 1 = p + 1 + 1 by ring]; field_simp


/-- Representation of `|D|^p u'` for bounded `u ∈ C²` with bounded `u'`:
`|D|^p u'(y) = c_α (N(y) + (2/p) u'(y) + u(y+1) - u(y-1) - α G(y))`. -/
theorem c07_aux_frac_rep (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (S L : ℝ) (hS : ∀ y, |u y| ≤ S) (hL : ∀ y, |deriv u y| ≤ L) (y : ℝ) :
    fracDdy p u y = calpha p *
      ((∫ s in Ioc (0:ℝ) 1, (2 * deriv u y - deriv u (y - s) - deriv u (y + s)) / s ^ (p + 1)) +
        2 / p * deriv u y + (u (y + 1) - u (y - 1)) -
        (p + 1) * ∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (u (y + s) - u (y - s))) := by
  have hu1 : ContDiff ℝ 1 (deriv u) := (hu.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdc : Continuous (deriv u) := hu1.continuous
  have hfr : fracDdy p u y = calpha p * ∫ z, (deriv u y - deriv u z) / |y - z| ^ (p + 1) := rfl
  rw [hfr, c07_aux_frac_symm p (deriv u) y (c07_aux_D_integrable p hp hp1 u hu L hL y)]
  congr 1
  set φ : ℝ → ℝ := fun s => (2 * deriv u y - deriv u (y - s) - deriv u (y + s)) / s ^ (p + 1)
    with hφ
  have hnear := (c07_aux_near_C0 p hp1 (deriv u) hu1).1 y
  have i0 : IntegrableOn (fun s : ℝ => s ^ (-(p + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  obtain ⟨j1, -, hibp⟩ := c07_aux_ibp_Ioi (p + 1) 1 (by linarith) one_pos
    (fun s => u (y + s) - u (y - s)) (fun s => deriv u (y + s) + deriv u (y - s))
    (fun s => by
      have b := (hud (y + s)).hasDerivAt.comp s ((hasDerivAt_id s).const_add y)
      have c := (hud (y - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub y)
      convert b.sub c using 1 <;> first | (funext x; simp) | simp)
    (by fun_prop) (2 * S) (2 * L)
    (fun s => by have := abs_sub (u (y + s)) (u (y - s)); linarith [hS (y + s), hS (y - s)])
    (fun s => by have := abs_add_le (deriv u (y + s)) (deriv u (y - s)); linarith [hL (y + s), hL (y - s)])
  have hφeq : EqOn φ (fun s => 2 * deriv u y * s ^ (-(p + 1)) -
      s ^ (-(p + 1)) * (deriv u (y + s) + deriv u (y - s))) (Ioi 1) := by
    intro s hs
    have hs0 : 0 < s := lt_trans one_pos hs
    simp only [hφ]
    rw [div_eq_mul_inv, ← Real.rpow_neg hs0.le]; ring
  have hfar : IntegrableOn φ (Ioi 1) :=
    IntegrableOn.congr_fun (by exact (i0.const_mul (2 * deriv u y)).sub j1 :
      IntegrableOn (fun s => 2 * deriv u y * s ^ (-(p + 1)) -
        s ^ (-(p + 1)) * (deriv u (y + s) + deriv u (y - s))) (Ioi (1:ℝ)))
      hφeq.symm measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    hnear hfar, setIntegral_congr_fun measurableSet_Ioi hφeq,
    integral_sub (i0.const_mul _) j1, integral_const_mul, hibp,
    integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow, Real.one_rpow]
  have hp0 : p ≠ 0 := hp.ne'
  rw [show -(p + 1) + 1 = -p by ring]
  field_simp
  ring


/-- Pointwise bound by `‖u‖_{C^k([-M,M])}`. -/
theorem c07_aux_le_CkNorm (k : ℕ) (M : ℝ) (u : ℝ → ℝ) (hu : ContDiff ℝ k u) (i : ℕ) (hi : i ≤ k)
    (x : ℝ) (hx : x ∈ Icc (-M) M) : |iteratedDeriv i u x| ≤ c07_CkNorm k M u := by
  have hc : Continuous (fun y => |iteratedDeriv i u y|) :=
    (hu.continuous_iteratedDeriv i (by exact_mod_cast hi)).abs
  have hbdd : BddAbove ((fun y => |iteratedDeriv i u y|) '' Icc (-M) M) :=
    (isCompact_Icc.image_of_continuousOn hc.continuousOn).bddAbove
  unfold c07_CkNorm
  calc |iteratedDeriv i u x| ≤ sSup ((fun y => |iteratedDeriv i u y|) '' Icc (-M) M) :=
        le_csSup hbdd ⟨x, hx, rfl⟩
    _ ≤ _ := Finset.single_le_sum (f := fun i => sSup ((fun y => |iteratedDeriv i u y|) '' Icc (-M) M))
        (fun j _ => Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- Pointwise bound by `‖u‖_∞`. -/
theorem c07_aux_le_supNorm (u : ℝ → ℝ) (L : ℝ) (hL : ∀ y, |u y| ≤ L) (x : ℝ) :
    |u x| ≤ c07_supNorm u :=
  le_csSup ⟨L, by rintro _ ⟨y, rfl⟩; exact hL y⟩ ⟨x, rfl⟩

/-- Blueprint: lem:c07_local_fractional.  For `u ∈ C³` with `u, u'` bounded and `M ≥ 1`:
`|D|^p u' ∈ C¹` and
`‖|D|^p u'‖_{C¹([-M,M])} ≤ C(‖u‖_{C³([-M-1,M+1])} + ‖u‖_∞)`,
`‖ℒ₀ u‖_{C¹([-M,M])} ≤ C(1+M)(‖u‖_{C³([-M-1,M+1])} + ‖u‖_∞)`, `C = C(p)`. -/
theorem c07_local_fractional (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M → ∀ u : ℝ → ℝ, ContDiff ℝ 3 u →
      (∃ L, ∀ y, |u y| ≤ L) → (∃ L, ∀ y, |deriv u y| ≤ L) →
      ContDiff ℝ 1 (fracDdy p u) ∧
      ∀ i ≤ 1, ∀ y ∈ Icc (-M) M,
        |iteratedDeriv i (fracDdy p u) y| ≤
          C * (c07_CkNorm 3 (M + 1) u + c07_supNorm u) ∧
        |iteratedDeriv i (L0 p u) y| ≤
          C * (1 + M) * (c07_CkNorm 3 (M + 1) u + c07_supNorm u) := by
  have hc := c03_aux_calpha_pos p hp hp1
  have h1p : 0 < 1 - p := by linarith
  set C0 := calpha p * (2 / (1 - p) + 2 / p + 10) with hC0
  have hC00 : 0 < C0 := by positivity
  refine ⟨C0 + 1, by linarith, fun M hM u hu ⟨S0, hS0⟩ ⟨L, hL⟩ => ?_⟩
  set Sn := c07_supNorm u with hSn
  set X := c07_CkNorm 3 (M + 1) u + Sn with hX
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hu1 : ContDiff ℝ 2 (deriv u) := (hu.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hu11 : ContDiff ℝ 1 (deriv (deriv u)) := (hu1.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hu1d : Differentiable ℝ (deriv u) := hu1.differentiable (by norm_num)
  have hu11d : Differentiable ℝ (deriv (deriv u)) := hu11.differentiable (by norm_num)
  have hS : ∀ x, |u x| ≤ Sn := c07_aux_le_supNorm u S0 hS0
  have hSn0 : 0 ≤ Sn := (abs_nonneg _).trans (hS 0)
  have hCk : ∀ i ≤ 3, ∀ x ∈ Icc (-(M + 1)) (M + 1), |iteratedDeriv i u x| ≤ X := fun i hi x hx =>
    (c07_aux_le_CkNorm 3 (M + 1) u hu i hi x hx).trans (by linarith)
  have hSnX : Sn ≤ X := by
    have := (abs_nonneg _).trans
      (c07_aux_le_CkNorm 3 (M + 1) u hu 0 (by norm_num) 0 ⟨by linarith, by linarith⟩)
    linarith
  have hX0 : 0 ≤ X := (abs_nonneg _).trans (hCk 0 (by norm_num) 0 ⟨by linarith, by linarith⟩)
  have b0 : ∀ x ∈ Icc (-(M + 1)) (M + 1), |u x| ≤ X := fun x hx => by
    simpa using hCk 0 (by norm_num) x hx
  have b1 : ∀ x ∈ Icc (-(M + 1)) (M + 1), |deriv u x| ≤ X := fun x hx => by
    simpa using hCk 1 (by norm_num) x hx
  have b2 : ∀ x ∈ Icc (-(M + 1)) (M + 1), |deriv (deriv u) x| ≤ X := fun x hx => by
    simpa [iteratedDeriv_succ] using hCk 2 (by norm_num) x hx
  have b3 : ∀ x ∈ Icc (-(M + 1)) (M + 1), |deriv (deriv (deriv u)) x| ≤ X := fun x hx => by
    simpa [iteratedDeriv_succ] using hCk 3 (by norm_num) x hx
  -- the pieces
  obtain ⟨-, hN1b, -⟩ := c07_aux_near_C0 p hp1 (deriv u) (hu1.of_le (by norm_num))
  obtain ⟨-, hN2b, hN2c⟩ := c07_aux_near_C0 p hp1 (deriv (deriv u)) hu11
  obtain ⟨hGd, hG1c, hGb, hG1b⟩ := c07_aux_far_part p hp u (hu.of_le (by norm_num)) Sn L hS hL
  have hrep := fun y => c07_aux_frac_rep p hp hp1 u hu2 Sn L hS hL y
  obtain ⟨N, hN⟩ : ∃ N : ℝ → ℝ, N = fun y =>
      ∫ s in Ioc (0:ℝ) 1, (2 * deriv u y - deriv u (y - s) - deriv u (y + s)) / s ^ (p + 1) :=
    ⟨_, rfl⟩
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℝ → ℝ, N2 = fun y => ∫ s in Ioc (0:ℝ) 1,
      (2 * deriv (deriv u) y - deriv (deriv u) (y - s) - deriv (deriv u) (y + s)) / s ^ (p + 1) :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = fun y =>
      ∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (u (y + s) - u (y - s)) := ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ → ℝ, G1 = fun y =>
      ∫ s in Ioi (1:ℝ), s ^ (-(p + 1) - 1) * (deriv u (y + s) - deriv u (y - s)) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, D = fun y => calpha p * (N2 y + 2 / p * deriv (deriv u) y +
      (deriv u (y + 1) - deriv u (y - 1)) - (p + 1) * G1 y) := ⟨_, rfl⟩
  have hfeq : fracDdy p u = fun y => calpha p * (N y + 2 / p * deriv u y + (u (y + 1) - u (y - 1)) -
      (p + 1) * G y) := by
    funext y; rw [hrep y, hN, hG]
  have hN1b' : ∀ y B, (∀ x ∈ Icc (y - 1) (y + 1), |deriv (deriv u) x| ≤ B) → |N y| ≤ 2 * B / (1 - p) :=
    by rw [hN]; exact hN1b
  have hN2b' : ∀ y B, (∀ x ∈ Icc (y - 1) (y + 1), |deriv (deriv (deriv u)) x| ≤ B) →
      |N2 y| ≤ 2 * B / (1 - p) := by rw [hN2]; exact hN2b
  have hN2c' : Continuous N2 := by rw [hN2]; exact hN2c
  have hGd' : ∀ y, HasDerivAt G (G1 y) y := by rw [hG, hG1]; exact hGd
  have hG1c' : Continuous G1 := by rw [hG1]; exact hG1c
  have hGb' : ∀ y, |G y| ≤ 2 * Sn / (p + 1) := by rw [hG]; exact hGb
  have hG1b' : ∀ y, |G1 y| ≤ |u (y + 1)| + |u (y - 1)| + 2 * Sn := by rw [hG1]; exact hG1b
  have hNd : ∀ y, HasDerivAt N (N2 y) y := by
    rw [hN, hN2]; exact c07_aux_near_deriv p hp1 (deriv u) hu1
  clear hN1b hN2b hN2c hGd hG1c hGb hG1b hrep
  have hsh : ∀ (g : ℝ → ℝ) (c y : ℝ), DifferentiableAt ℝ g (y + c) →
      HasDerivAt (fun x => g (x + c)) (deriv g (y + c)) y := by
    intro g c y hg
    have := hg.hasDerivAt.comp y ((hasDerivAt_id y).add_const c)
    simpa [Function.comp_def] using this
  have hder : ∀ y, HasDerivAt (fracDdy p u) (D y) y := by
    intro y
    rw [hfeq, hD]
    have c1 := hsh u 1 y (hud _)
    have c2 := hsh u (-1) y (hud _)
    simp only [← sub_eq_add_neg] at c1 c2
    exact ((((hNd y).add ((hu1d y).hasDerivAt.const_mul (2 / p))).add (c1.sub c2)).sub
      ((hGd' y).const_mul (p + 1))).const_mul (calpha p)
  have hdeq : deriv (fracDdy p u) = D := funext fun y => (hder y).deriv
  have hDc : Continuous D := by
    rw [hD]
    exact continuous_const.mul ((((hN2c'.add (continuous_const.mul hu11.continuous)).add
      ((hu1.continuous.comp (continuous_id.add continuous_const)).sub
        (hu1.continuous.comp (continuous_id.sub continuous_const)))).sub
      (continuous_const.mul hG1c')))
  have hC1 : ContDiff ℝ 1 (fracDdy p u) :=
    contDiff_one_iff_deriv.2 ⟨fun y => (hder y).differentiableAt, hdeq ▸ hDc⟩
  -- bounds
  have hmem : ∀ y ∈ Icc (-M) M, ∀ x ∈ Icc (y - 1) (y + 1), x ∈ Icc (-(M + 1)) (M + 1) :=
    fun y hy x hx => ⟨by linarith [hy.1, hx.1], by linarith [hy.2, hx.2]⟩
  have hfb : ∀ y ∈ Icc (-M) M, |fracDdy p u y| ≤ C0 * X := by
    intro y hy
    have e1 := hN1b' y X fun x hx => b2 x (hmem y hy x hx)
    have e2 := b1 y (hmem y hy y ⟨by linarith, by linarith⟩)
    have e3 := b0 (y + 1) (hmem y hy _ ⟨by linarith, by linarith⟩)
    have e4 := b0 (y - 1) (hmem y hy _ ⟨by linarith, by linarith⟩)
    have e5 := hGb' y
    rw [hfeq]; simp only []
    rw [abs_mul, abs_of_pos hc, hC0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have t1 := abs_sub (N y + 2 / p * deriv u y + (u (y + 1) - u (y - 1))) ((p + 1) * G y)
    have t2 := abs_add_le (N y + 2 / p * deriv u y) (u (y + 1) - u (y - 1))
    have t3 := abs_add_le (N y) (2 / p * deriv u y)
    have t4 := abs_sub (u (y + 1)) (u (y - 1))
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / p)] at t3
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < p + 1)] at t1
    have t5 : (p + 1) * |G y| ≤ 2 * X := by
      have := mul_le_mul_of_nonneg_left e5 (by linarith : (0:ℝ) ≤ p + 1)
      rw [mul_div_cancel₀ _ (by linarith : (p + 1) ≠ 0)] at this
      linarith
    have t6 : 2 / p * |deriv u y| ≤ 2 / p * X := mul_le_mul_of_nonneg_left e2 (by positivity)
    have t7 : 2 * X / (1 - p) = 2 / (1 - p) * X := by ring
    have t8 : 2 / (1 - p) * X + 2 / p * X + 10 * X = (2 / (1 - p) + 2 / p + 10) * X := by ring
    nlinarith
  have hdb : ∀ y ∈ Icc (-M) M, |D y| ≤ C0 * X := by
    intro y hy
    have e1 := hN2b' y X fun x hx => b3 x (hmem y hy x hx)
    have e2 := b2 y (hmem y hy y ⟨by linarith, by linarith⟩)
    have e3 := b1 (y + 1) (hmem y hy _ ⟨by linarith, by linarith⟩)
    have e4 := b1 (y - 1) (hmem y hy _ ⟨by linarith, by linarith⟩)
    have e5 := hG1b' y
    have e6 := b0 (y + 1) (hmem y hy _ ⟨by linarith, by linarith⟩)
    have e7 := b0 (y - 1) (hmem y hy _ ⟨by linarith, by linarith⟩)
    rw [hD]; simp only []
    rw [abs_mul, abs_of_pos hc, hC0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have t1 := abs_sub (N2 y + 2 / p * deriv (deriv u) y + (deriv u (y + 1) - deriv u (y - 1)))
      ((p + 1) * G1 y)
    have t2 := abs_add_le (N2 y + 2 / p * deriv (deriv u) y) (deriv u (y + 1) - deriv u (y - 1))
    have t3 := abs_add_le (N2 y) (2 / p * deriv (deriv u) y)
    have t4 := abs_sub (deriv u (y + 1)) (deriv u (y - 1))
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / p)] at t3
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < p + 1)] at t1
    have t5 : (p + 1) * |G1 y| ≤ 8 * X := by
      have h4 : |G1 y| ≤ 4 * X := by linarith
      have := mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ p + 1)
      nlinarith
    have t6 : 2 / p * |deriv (deriv u) y| ≤ 2 / p * X := mul_le_mul_of_nonneg_left e2 (by positivity)
    have t7 : 2 * X / (1 - p) = 2 / (1 - p) * X := by ring
    have t8 : 2 / (1 - p) * X + 2 / p * X + 10 * X = (2 / (1 - p) + 2 / p + 10) * X := by ring
    nlinarith
  -- `ℒ₀`
  have hL0der : ∀ y, HasDerivAt (L0 p u) (D y - y * deriv (deriv u) y) y := by
    intro y
    have := ((hder y).add (hud y).hasDerivAt).sub ((hasDerivAt_id y).mul (hu1d y).hasDerivAt)
    convert this using 1
    · rfl
    · simp only [id]; ring
  refine ⟨hC1, fun i hi y hy => ?_⟩
  have hyM : |y| ≤ M := abs_le.2 ⟨hy.1, hy.2⟩
  have hyin : y ∈ Icc (-(M + 1)) (M + 1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hMX : 0 ≤ M * X := by positivity
  interval_cases i
  · simp only [iteratedDeriv_zero]
    have hf := hfb y hy
    refine ⟨by nlinarith, ?_⟩
    show |fracDdy p u y + u y - y * deriv u y| ≤ _
    have t1 := abs_sub (fracDdy p u y + u y) (y * deriv u y)
    have t2 := abs_add_le (fracDdy p u y) (u y)
    have t3 : |y * deriv u y| ≤ M * X := by
      rw [abs_mul]; exact mul_le_mul hyM (b1 y hyin) (abs_nonneg _) (by linarith)
    have := b0 y hyin
    nlinarith
  · simp only [iteratedDeriv_one]
    rw [hdeq, (hL0der y).deriv]
    have hf := hdb y hy
    refine ⟨by nlinarith, ?_⟩
    have t1 := abs_sub (D y) (y * deriv (deriv u) y)
    have t3 : |y * deriv (deriv u) y| ≤ M * X := by
      rw [abs_mul]; exact mul_le_mul hyM (b2 y hyin) (abs_nonneg _) (by linarith)
    nlinarith

/-! ### Results of other chapters (wrappers around the imported chapter-03/04 theorems) -/

/-- Wrapper for prop:approx_profile_bounds (chapter 04, `GSQG.approx_profile_bounds`), stated
verbatim; proved by the chapter 04 result. -/
theorem c07_ext_approx_profile_bounds (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
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
            (iteratedDeriv k (approximate_solution_family p R ε μ₀)) (𝓝[Bbar p δ] μ₀) K) :=
  approx_profile_bounds p hp hp1

/-- Wrapper for lem:approx_linear_seed (chapter 04, `GSQG.approx_linear_seed`), stated
verbatim; proved by the chapter 04 result. -/
theorem c07_ext_approx_linear_seed (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed p) ∧ c04_linear_seed p ∈ c01_admissible_class ∧
    (∀ y, L0 p (c04_linear_seed p) y = 0) ∧
    Tendsto (deriv (c04_linear_seed p)) atBot (𝓝 (-1)) ∧
    Tendsto (deriv (c04_linear_seed p)) atTop (𝓝 0) ∧
    (∃ y₀ ≥ (2 : ℝ), ∀ j : ℕ, ∃ C > (0 : ℝ),
      -- (1)
      (∀ y ≥ y₀, ‖iteratedDeriv j (fun t => astar p t - 1) y‖ ≤ C * y ^ (-2 * beta p - j)) ∧
      -- (2)
      (∀ y : ℝ, 1 ≤ |y| →
        |iteratedDeriv j (fun t => c04_linear_seed_low p t - corner t) y| ≤ C * |y| ^ (-p - j)) ∧
      (∀ y ≤ (-1 : ℝ),
        |iteratedDeriv j (fun t => c04_linear_seed p t + t) y| ≤ C * |y| ^ (-p - j))) ∧
    -- (3)
    (∀ μ : ℂ, ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_mu p μ) ∧
      c04_linear_seed_mu p μ ∈ c01_admissible_class ∧
      ∀ y, L0 p (c04_linear_seed_mu p μ) y = G_mu p μ y) :=
  approx_linear_seed p hp hp1

/-- Wrapper for lem:approx_phase_differences (chapter 04, `GSQG.approx_phase_differences`),
stated verbatim; proved by the chapter 04 result. -/
theorem c07_ext_approx_phase_differences (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ),
      (∀ j : ℕ, ∃ C > (0 : ℝ),
        ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≥ R,
          |iteratedDeriv j (fun t => fam_Psi p R ε μ t - Psi0 p t) y| ≤
            C * ε * y ^ (1 / p - p - j) ∧
          |iteratedDeriv j (fun t => fam_lambda p ε μ t - lambda0 p t) y| ≤
            C * ε * y ^ (1 / p - p - 1 - j) ∧
          ‖iteratedDeriv j (fun t => fam_Z p R ε μ t - μ / mu_star p * fam_Z0 p R t) y‖ ≤
            C * ε * y ^ (1 / p - p - beta p + j / p) ∧
          |iteratedDeriv j (fam_osc p R ε μ) y| ≤
            C * min (ε * jb y ^ (-p - beta p + j / p)) (jb y ^ (-beta p + ((j : ℝ) - 1) / p))) ∧
      (∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ, ∀ y ≤ R, fam_osc p R ε μ y = 0) ∧
      (∃ C > (0 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        Integrable (fam_osc p R ε μ) ∧
        ∫ y, |fam_osc p R ε μ y| ≤ C * ε * R ^ (1 - p - beta p) ∧
        C * ε * R ^ (1 - p - beta p) ≤ C * ε) :=
  approx_phase_differences p hp hp1

/-! ### Uniform properties of the approximate family -/

/-- Blueprint: lem:c07_f0plus_smooth.  The integral defining `f_{0,+}` converges absolutely and
`f_{0,+} ∈ C^∞(ℝ;ℂ)`. -/
theorem c07_f0plus_smooth (P : parameters) :
    (∀ y : ℝ, IntegrableOn (fun ξ => ((chiPlus ξ / ξ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((y * ξ - Phi0 P.p ξ : ℝ) : ℂ))) (Ioi 0)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_plus P.p) := by
  obtain ⟨h1, -, h3, -⟩ := c04_seed_decomposition P.p P.hp_lo P.hp_hi
  exact ⟨fun y => (h1 y).2, h3⟩

/-- Blueprint: lem:c07_family_smooth.  `f̄_{ε,μ}`, `f_{0,μ}`, `f_slow`, `f_osc` are (real and)
`C^∞`; `f_osc = 0` on `(-∞,R]` and `f_slow = 0` on `[-R,R]`. -/
theorem c07_family_smooth (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        ContDiff ℝ (⊤ : ℕ∞) (approximate_solution_family P.p R ε μ) ∧
        ContDiff ℝ (⊤ : ℕ∞) (c04_linear_seed_mu P.p μ) ∧
        ContDiff ℝ (⊤ : ℕ∞) (fam_slow P.p R ε) ∧
        ContDiff ℝ (⊤ : ℕ∞) (fam_osc P.p R ε μ) ∧
        (∀ y ≤ R, fam_osc P.p R ε μ y = 0) ∧
        (∀ y ∈ Icc (-R) R, fam_slow P.p R ε y = 0) := by
  intro δ hδ hδ'
  obtain ⟨ε₀, ⟨he0, he1⟩, R₀, hR₀, -, hC⟩ :=
    c07_ext_approx_profile_bounds P.p P.hp_lo P.hp_hi δ hδ hδ'
  have hmu := (c07_ext_approx_linear_seed P.p P.hp_lo P.hp_hi).2.2.2.2.2.2
  refine ⟨R₀, ε₀, by linarith, he0, he1, fun R hR ε hε μ hμ => ?_⟩
  have hR0 : 0 < R := by linarith
  have hf := (hC R hR ε hε).1 μ hμ
  have h0 := (hmu μ).1
  have hs := c07_aux_slow_smooth P.p R ε hR0
  have ho : fam_osc P.p R ε μ = fun y => approximate_solution_family P.p R ε μ y -
      c04_linear_seed_mu P.p μ y - fam_slow P.p R ε y := by
    funext y; unfold approximate_solution_family; ring
  refine ⟨hf, h0, hs, by rw [ho]; exact (hf.sub h0).sub hs, fun y hy => ?_, fun y hy => ?_⟩
  · unfold fam_osc; simp [not_lt.2 hy]
  · have h1 : y / R - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hR0]; exact hy.2
    have h2 : -y / R - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hR0]; linarith [hy.1]
    simp [fam_slow, fam_chiR, chiPlus, Real.smoothTransition.zero_of_nonpos h1,
      Real.smoothTransition.zero_of_nonpos h2]

/-- Blueprint: lem:c07_family_uniform_bounds.  There is an admissible `K₀ ≥ 1` with, for
`f = f̄_{ε,μ}`, `g = f - W`: `f ∈ 𝒫(K₀)`, `|g(y)| ≤ K₀⟨y⟩^{-p}`, and
`|g^{(i)}(y)| ≤ K₀⟨y⟩^{-p-i}` for `y ≤ 0`, `i ≤ 3`.
On `(-∞,0]` the derivatives of `g` are those of `f(y) + y` (the blueprint's "`g = f + y` on
`(-∞,0]`"); we state (3) for `fun z => f z + z`, which avoids Mathlib's junk derivative of the
corner at `0`. -/
theorem c07_family_uniform_bounds (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
      approximate_solution_family P.p R ε μ ∈ c07_profile_class P.p K₀ ∧
      (∀ y : ℝ, |approximate_solution_family P.p R ε μ y - corner y| ≤ K₀ * jb y ^ (-P.p)) ∧
      (∀ i ≤ 3, ∀ y ≤ 0,
        |iteratedDeriv i (fun z => approximate_solution_family P.p R ε μ z + z) y| ≤
          K₀ * jb y ^ (-P.p - i)) := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hβ : 0 < beta P.p := by unfold beta; positivity
  obtain ⟨ε₀, ⟨he0, he1⟩, R₀, hR₀, hB, hC⟩ :=
    c07_ext_approx_profile_bounds P.p P.hp_lo P.hp_hi δ hδ hδ'
  refine ⟨R₀, ε₀, by linarith, he0, he1, fun R hR => ?_⟩
  obtain ⟨C0, hC0, h0⟩ := hB 0
  obtain ⟨C1, hC1, h1⟩ := hB 1
  obtain ⟨C2, hC2, h2⟩ := hB 2
  obtain ⟨C3, hC3, h3⟩ := hB 3
  refine ⟨C0 + C1 + C2 + C3 + 1, by linarith, fun ε hε μ hμ => ?_⟩
  have hfs := (hC R hR ε hε).1 μ hμ
  obtain ⟨a0, b0⟩ := h0 R hR ε hε μ hμ
  obtain ⟨a1, b1⟩ := h1 R hR ε hε μ hμ
  obtain ⟨a2, b2⟩ := h2 R hR ε hε μ hμ
  obtain ⟨-, b3⟩ := h3 R hR ε hε μ hμ
  obtain ⟨hd1, hdk⟩ := c07_aux_iteratedDeriv_add_id _ hfs
  set f := approximate_solution_family P.p R ε μ with hf_def
  set K := C0 + C1 + C2 + C3 + 1 with hK
  have F1 : ∀ y ≥ 0, |deriv f y| ≤ C0 * jb y ^ (-beta P.p) := fun y hy => by
    simpa using (a0 y hy).2
  have F2 : ∀ y ≥ 0, |iteratedDeriv 2 f y| ≤ C1 * jb y ^ (-beta P.p + 1 / P.p) := fun y hy => by
    simpa using (a1 y hy).2
  have F3 : ∀ y ≥ 0, |iteratedDeriv 3 f y| ≤ C2 * jb y ^ (-beta P.p + 2 / P.p) := fun y hy => by
    have := (a2 y hy).2; norm_num at this ⊢; exact this
  have G0 : ∀ y ≤ 0, |f y + y| ≤ C0 * jb y ^ (-P.p) := fun y hy => by
    simpa using b0 y hy
  have G1 : ∀ y ≤ 0, |deriv f y + 1| ≤ C1 * jb y ^ (-P.p - 1) := fun y hy => by
    have := b1 y hy; rw [iteratedDeriv_one, hd1] at this; simpa using this
  have G2 : ∀ y ≤ 0, |iteratedDeriv 2 f y| ≤ C2 * jb y ^ (-P.p - 2) := fun y hy => by
    have := b2 y hy; rw [show (2 : ℕ) = 0 + 2 from rfl, hdk 0] at this; simpa using this
  have G3 : ∀ y ≤ 0, |iteratedDeriv 3 f y| ≤ C3 * jb y ^ (-P.p - 3) := fun y hy => by
    have := b3 y hy; rw [show (3 : ℕ) = 1 + 2 from rfl, hdk 1] at this; simpa using this
  refine ⟨⟨hfs.of_le (by simp), fun y => ⟨?_, fun hy => ?_, fun hy => ?_, ?_⟩⟩, fun y => ?_,
    fun i hi y hy => ?_⟩
  · rcases le_total 0 y with hy | hy
    · have := (F1 y hy).trans (c07_aux_bound_mono C0 K _ 0 y (by linarith) hC0.le (by linarith))
      simpa using this
    · have h := (G1 y hy).trans (c07_aux_bound_mono C1 (C1) _ 0 y le_rfl hC1.le (by linarith))
      rw [Real.rpow_zero, mul_one] at h
      rw [abs_le] at h ⊢
      constructor <;> linarith [h.1, h.2]
  · have hθ : c07_theta P.p = -beta P.p + 1 / P.p := by unfold c07_theta; ring
    rw [hθ]
    exact (F2 y hy).trans (c07_aux_bound_mono C1 K _ _ y (by linarith) hC1.le le_rfl)
  · exact (G2 y hy).trans (c07_aux_bound_mono C2 K _ _ y (by linarith) hC2.le (by linarith))
  · rcases le_total 0 y with hy | hy
    · exact (F3 y hy).trans (c07_aux_bound_mono C2 K _ _ y (by linarith) hC2.le (by linarith))
    · have : 0 < 2 / P.p := by positivity
      exact (G3 y hy).trans (c07_aux_bound_mono C3 K _ _ y (by linarith) hC3.le (by linarith))
  · rcases le_total 0 y with hy | hy
    · have hc : corner y = 0 := by unfold corner; simp [hy]
      rw [hc, sub_zero]
      exact ((a0 y hy).1).trans (c07_aux_bound_mono C0 K _ _ y (by linarith) hC0.le le_rfl)
    · have hc : corner y = -y := by unfold corner; simp [hy]
      rw [hc, sub_neg_eq_add]
      exact (G0 y hy).trans (c07_aux_bound_mono C0 K _ _ y (by linarith) hC0.le le_rfl)
  · interval_cases i
    · exact (b0 y hy).trans (c07_aux_bound_mono C0 K _ _ y (by linarith) hC0.le le_rfl)
    · exact (b1 y hy).trans (c07_aux_bound_mono C1 K _ _ y (by linarith) hC1.le le_rfl)
    · exact (b2 y hy).trans (c07_aux_bound_mono C2 K _ _ y (by linarith) hC2.le le_rfl)
    · exact (b3 y hy).trans (c07_aux_bound_mono C3 K _ _ y (by linarith) hC3.le le_rfl)

/-- Blueprint: lem:c07_family_continuity.  For fixed `ε` and every `k`, `μ ↦ f̄_{ε,μ}` is
continuous from `B̄` into `C^k_loc`. -/
theorem c07_family_continuity (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ k : ℕ, ∀ μ ∈ Bbar P.p δ,
        c07_TendstoCkLoc k (fun ν => approximate_solution_family P.p R ε ν)
          (nhdsWithin μ (Bbar P.p δ)) (approximate_solution_family P.p R ε μ) := by
  intro δ hδ hδ'
  obtain ⟨ε₀, ⟨he0, he1⟩, R₀, hR₀, -, hC⟩ :=
    c07_ext_approx_profile_bounds P.p P.hp_lo P.hp_hi δ hδ hδ'
  refine ⟨R₀, ε₀, by linarith, he0, he1, fun R hR ε hε k μ hμ i hi M hM => ?_⟩
  exact (hC R hR ε hε).2 i (Icc (-M) M) isCompact_Icc μ hμ

/-- `|c₊| + |c₋| ≤ C ε` for `0 ≤ ε ≤ 1`. -/
theorem c07_aux_cpm_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, |c_plus p ε| + |c_minus p ε| ≤ C * ε := by
  have hc := c03_aux_calpha_pos p hp hp1
  refine ⟨calpha p * (p + 1) / (2 * p) / (p + 1) + calpha p / (p + 1) * (1 / p), by positivity,
    fun ε hε => ?_⟩
  have h1 := (analysis_coefficient p ε hp hp1 hε.1 hε.2).2.2.1
  have hplus : |c_plus p ε| ≤ calpha p * (p + 1) / (2 * p) / (p + 1) * ε := by
    unfold c_plus
    rw [abs_div, abs_neg, abs_of_pos (by linarith : (0:ℝ) < p + 1)]
    rw [div_le_iff₀ (by linarith)]
    calc |c_eps p ε| ≤ calpha p * (p + 1) / (2 * p) * ε := h1
      _ = _ := by field_simp
  have hint : ‖∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * t ^ (p - 1)‖ ≤
      ∫ t in (0 : ℝ)..1, ε * t ^ (p - 1) := by
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · refine Eventually.of_forall (fun t ht => ?_)
      have h0 : 0 ≤ t ^ (p - 1) := Real.rpow_nonneg (by linarith [ht.1]) _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
      have ht' : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      exact mul_le_mul_of_nonneg_right (c04_aux_A_sub_one p ε t hp hp1.le hε.1 ht') h0
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  have hval : ∫ t in (0 : ℝ)..1, ε * t ^ (p - 1) = ε * (1 / p) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
      sub_add_cancel, Real.one_rpow, Real.zero_rpow hp.ne', sub_zero]
  rw [hval, Real.norm_eq_abs] at hint
  have hminus : |c_minus p ε| ≤ calpha p / (p + 1) * (1 / p) * ε := by
    unfold c_minus
    rw [abs_mul, abs_of_pos (by positivity : 0 < calpha p / (p + 1))]
    calc calpha p / (p + 1) * |∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * t ^ (p - 1)|
        ≤ calpha p / (p + 1) * (ε * (1 / p)) := mul_le_mul_of_nonneg_left hint (by positivity)
      _ = _ := by ring
  linarith

/-- Derivative bounds for `y^{-p} χ_R(y)` (constant depending on `R`). -/
theorem c07_aux_rpow_chiR_bounds (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ 3, ∀ y : ℝ,
      |iteratedDeriv i (fun y : ℝ => y ^ (-p) * fam_chiR R y) y| ≤ C * jb y ^ (-p - i) := by
  set g : ℝ → ℝ := fun y : ℝ => y ^ (-p) * fam_chiR R y with hg
  have hR0 : 0 < R := by linarith
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := c07_aux_rpow_chiR_smooth p R hR0
  -- compact part
  have hcomp : ∀ i : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Icc (-(3 * R)) (3 * R), |iteratedDeriv i g y| ≤ M := by
    intro i
    have hc : Continuous (iteratedDeriv i g) := hgs.continuous_iteratedDeriv i (by simp)
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -(3 * R)) (b := 3 * R)).exists_bound_of_continuousOn
      hc.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun y hy => by
      have := hM y hy; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)⟩
  obtain ⟨M0, hM0, h0⟩ := hcomp 0
  obtain ⟨M1, hM1, h1⟩ := hcomp 1
  obtain ⟨M2, hM2, h2⟩ := hcomp 2
  obtain ⟨M3, hM3, h3⟩ := hcomp 3
  set D : ℝ := ∑ i ∈ Finset.range 4, |(descPochhammer ℝ i).eval (-p)| with hD
  have hDi : ∀ i < 4, |(descPochhammer ℝ i).eval (-p)| ≤ D := fun i hi =>
    Finset.single_le_sum (f := fun i => |(descPochhammer ℝ i).eval (-p)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hi)
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set B : ℝ := (1 + 3 * R) ^ 4 with hB
  refine ⟨(M0 + M1 + M2 + M3) * B + 16 * D + 1, by positivity, fun i hi y => ?_⟩
  have hjb1 := c07_aux_one_le_jb y
  have hjb0 : 0 < jb y := by linarith
  have hi' : (i : ℝ) ≤ 3 := by exact_mod_cast hi
  have hpos : 0 ≤ jb y ^ (-p - i) := Real.rpow_nonneg hjb0.le _
  rcases lt_or_ge (3 * R) |y| with hy | hy
  · rcases lt_or_gt_of_ne (show y ≠ 0 by intro h; rw [h] at hy; simp at hy; linarith) with hneg | hpos'
    · -- y < -3R : g = 0 near y
      have hev : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds (show y < R by rw [abs_of_neg hneg] at hy; linarith)]
          with t ht
        have : t / R - 1 ≤ 0 := by
          rw [sub_nonpos, div_le_one hR0]; exact (mem_Iio.1 ht).le
        simp [hg, fam_chiR, chiPlus, Real.smoothTransition.zero_of_nonpos this]
      rw [hev.iteratedDeriv_eq]
      have : iteratedDeriv i (fun _ : ℝ => (0 : ℝ)) y = 0 := by
        rcases i with _ | i
        · simp
        · simp [iteratedDeriv_succ']
      rw [this, abs_zero]; positivity
    · -- y > 3R : g = y^{-p} near y
      rw [abs_of_pos hpos'] at hy
      have hev : g =ᶠ[𝓝 y] fun t => t ^ (-p) := by
        filter_upwards [Ioi_mem_nhds (show 2 * R < y by linarith)] with t ht
        have : 1 ≤ t / R - 1 := by
          rw [le_sub_iff_add_le, le_div_iff₀ hR0]; linarith [mem_Ioi.1 ht]
        simp [hg, fam_chiR, chiPlus, Real.smoothTransition.one_of_one_le this]
      rw [hev.iteratedDeriv_eq, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, abs_mul]
      have hy1 : 1 ≤ |y| := by rw [abs_of_pos hpos']; linarith
      have hyb := c07_aux_abs_rpow_le_jb y (-p - i) hy1 (by linarith) (by linarith)
      rw [abs_of_pos hpos'] at hyb
      rw [abs_of_nonneg (Real.rpow_nonneg hpos'.le _)]
      have hc := hDi i (by omega)
      calc |(descPochhammer ℝ i).eval (-p)| * y ^ (-p - i) ≤ D * (16 * jb y ^ (-p - i)) :=
            mul_le_mul hc hyb (Real.rpow_nonneg hpos'.le _) hD0
        _ ≤ _ := by
            have : 0 ≤ (M0 + M1 + M2 + M3) * B := by positivity
            nlinarith
  · have hyI : y ∈ Icc (-(3 * R)) (3 * R) := abs_le.1 hy
    have hM : |iteratedDeriv i g y| ≤ M0 + M1 + M2 + M3 := by
      interval_cases i
      · have := h0 y hyI; linarith
      · have := h1 y hyI; linarith
      · have := h2 y hyI; linarith
      · have := h3 y hyI; linarith
    -- 1 ≤ B * jb^{-p-i}
    have hjbB : jb y ≤ 1 + 3 * R := by
      unfold jb
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_abs y, abs_nonneg y]
    have hkey : 1 ≤ B * jb y ^ (-p - i) := by
      have e : jb y ^ (p + i) * jb y ^ (-p - i) = 1 := by
        rw [← Real.rpow_add hjb0]; simp
      have h1' : jb y ^ (p + i) ≤ jb y ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hjb1 (by linarith)
      have h2' : jb y ^ (4 : ℝ) ≤ B := by
        rw [hB, show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact pow_le_pow_left₀ hjb0.le hjbB 4
      nlinarith
    have hS : 0 ≤ M0 + M1 + M2 + M3 := by positivity
    calc |iteratedDeriv i g y| ≤ (M0 + M1 + M2 + M3) * 1 := by linarith
      _ ≤ (M0 + M1 + M2 + M3) * (B * jb y ^ (-p - i)) := mul_le_mul_of_nonneg_left hkey hS
      _ ≤ _ := by
          have : 0 ≤ (16 * D + 1) * jb y ^ (-p - i) := by positivity
          nlinarith

/-- Blueprint: lem:c07_slow_bounds.  `|c₊| + |c₋| ≤ Cε`,
`|f_slow^{(i)}(y)| ≤ Cε⟨y⟩^{-p-i}` (`i ≤ 3`), and `f_slow(y) = c₋|y|^{-p}` for `y ≤ -2R`. -/
theorem c07_slow_bounds (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀,
      |c_plus P.p ε| + |c_minus P.p ε| ≤ C * ε ∧
      (∀ i ≤ 3, ∀ y : ℝ, |iteratedDeriv i (fam_slow P.p R ε) y| ≤ C * ε * jb y ^ (-P.p - i)) ∧
      (∀ y ≤ -2 * R, fam_slow P.p R ε y = c_minus P.p ε * |y| ^ (-P.p)) := by
  intro δ _ _
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨Cc, hCc, hc⟩ := c07_aux_cpm_bound P.p hp P.hp_hi
  refine ⟨1, 1, le_rfl, one_pos, le_rfl, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  obtain ⟨CR, hCR, hb⟩ := c07_aux_rpow_chiR_bounds P.p R hp P.hp_hi hR
  refine ⟨Cc * CR + Cc, by positivity, fun ε hε => ⟨(hc ε hε).trans ?_, fun i hi y => ?_,
    fun y hy => ?_⟩⟩
  · nlinarith [hε.1, mul_pos hCc hCR]
  · set g : ℝ → ℝ := fun y : ℝ => y ^ (-P.p) * fam_chiR R y with hg
    have hgs : ContDiff ℝ (⊤ : ℕ∞) g := c07_aux_rpow_chiR_smooth P.p R hR0
    have heq : fam_slow P.p R ε = fun y => c_plus P.p ε * g y + c_minus P.p ε * g (-y) := by
      funext y
      unfold fam_slow
      simp only [hg]
      rcases le_or_gt (-y) R with hy | hy
      · have : -y / R - 1 ≤ 0 := by rw [sub_nonpos, div_le_one hR0]; exact hy
        simp [fam_chiR, chiPlus, Real.smoothTransition.zero_of_nonpos this]; ring
      · rw [abs_of_neg (by linarith)]; ring
    have hgn : ContDiff ℝ (⊤ : ℕ∞) (fun y => g (-y)) := hgs.comp contDiff_neg
    rw [heq, iteratedDeriv_fun_add ((contDiff_const.mul hgs).contDiffAt.of_le (by exact_mod_cast le_top))
      ((contDiff_const.mul hgn).contDiffAt.of_le (by exact_mod_cast le_top)),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field (f := fun y => g (-y)),
      iteratedDeriv_comp_neg]
    have b1 := hb i hi y
    have b2 := hb i hi (-y)
    have hjn : jb (-y) = jb y := by simp [jb]
    rw [hjn] at b2
    have hpw : |((-1 : ℝ) ^ i)| = 1 := by simp
    have hcε := hc ε hε
    have hpos : 0 ≤ jb y ^ (-P.p - i) := Real.rpow_nonneg (by linarith [c07_aux_one_le_jb y]) _
    calc |c_plus P.p ε * iteratedDeriv i g y +
          c_minus P.p ε * ((-1 : ℝ) ^ i • iteratedDeriv i g (-y))|
        ≤ |c_plus P.p ε| * |iteratedDeriv i g y| + |c_minus P.p ε| * |iteratedDeriv i g (-y)| := by
          rw [smul_eq_mul]
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_mul, hpw, one_mul]
      _ ≤ |c_plus P.p ε| * (CR * jb y ^ (-P.p - i)) +
          |c_minus P.p ε| * (CR * jb y ^ (-P.p - i)) := by gcongr
      _ = (|c_plus P.p ε| + |c_minus P.p ε|) * (CR * jb y ^ (-P.p - i)) := by ring
      _ ≤ (Cc * ε) * (CR * jb y ^ (-P.p - i)) := by gcongr
      _ ≤ _ := by
          have : 0 ≤ Cc * ε * jb y ^ (-P.p - i) := by
            have := hε.1; positivity
          nlinarith
  · unfold fam_slow
    have h1 : y / R - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hR0]; linarith
    have h2 : 1 ≤ -y / R - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hR0]; linarith
    simp [fam_chiR, chiPlus, Real.smoothTransition.zero_of_nonpos h1,
      Real.smoothTransition.one_of_one_le h2]

/-- Blueprint: lem:c07_residual_split.  `f, f_{0,μ}, f_slow, f_osc` are `C^∞` with bounded first
derivative, and `ℰ̃_ε(f) - G_μ = ℒ₀(f_slow) + ℒ₀(f_osc) + 𝒬_ε(f)` pointwise. -/
theorem c07_residual_split (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        (∀ u ∈ ({approximate_solution_family P.p R ε μ, c04_linear_seed_mu P.p μ,
            fam_slow P.p R ε, fam_osc P.p R ε μ} : Set (ℝ → ℝ)),
          ContDiff ℝ (⊤ : ℕ∞) u ∧ ∃ L, ∀ y, |deriv u y| ≤ L) ∧
        ∀ y : ℝ,
          c07_divided_residual P.p ε (approximate_solution_family P.p R ε μ) y - G_mu P.p μ y =
            L0 P.p (fam_slow P.p R ε) y + L0 P.p (fam_osc P.p R ε μ) y +
              c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ) y := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨R1, e1, hR1, he1, he11, hS⟩ := c07_family_smooth P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  obtain ⟨R3, e3, -, he3, -, hB⟩ := c07_slow_bounds P δ hδ hδ'
  have hseed := (c07_ext_approx_linear_seed P.p P.hp_lo P.hp_hi).2.2.2.2.2.2
  refine ⟨max R1 (max R2 R3), min e1 (min e2 e3), le_trans hR1 (le_max_left _ _), by simp [*],
    (min_le_left _ _).trans he11, fun R hR ε hε μ hμ => ?_⟩
  have hεa : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεb : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεc : ε ∈ Icc (0 : ℝ) e3 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans he11⟩
  obtain ⟨hf, h0, hs, ho, -, -⟩ := hS R (le_trans (by simp) hR) ε hεa μ hμ
  obtain ⟨K₀, -, hU'⟩ := hU R (le_trans (by simp) hR)
  obtain ⟨Cs, hCs, hB'⟩ := hB R (le_trans (by simp) hR)
  obtain ⟨-, ⟨-, ⟨M0, hM0⟩, -⟩, hL0⟩ := hseed μ
  set f := approximate_solution_family P.p R ε μ with hf_def
  set a := c04_linear_seed_mu P.p μ with ha_def
  set b := fam_slow P.p R ε with hb_def
  set c := fam_osc P.p R ε μ with hc_def
  have hfabc : f = fun y => a y + b y + c y := by
    funext y; simp only [hf_def, ha_def, hb_def, hc_def, approximate_solution_family]
  have hda : Differentiable ℝ a := h0.differentiable (by simp)
  have hdb : Differentiable ℝ b := hs.differentiable (by simp)
  have hdc : Differentiable ℝ c := ho.differentiable (by simp)
  have hderiv : ∀ y, deriv f y = deriv a y + deriv b y + deriv c y := fun y => by
    rw [hfabc]; exact (((hda y).hasDerivAt.add (hdb y).hasDerivAt).add (hdc y).hasDerivAt).deriv
  have hbf : ∀ y, |deriv f y| ≤ K₀ := fun y => ((hU' ε hεb μ hμ).1.2 y).1
  have hbb : ∀ y, |deriv b y| ≤ Cs * ε := fun y => by
    have h := (hB' ε hεc).2.1 1 (by norm_num) y
    rw [iteratedDeriv_one] at h
    have h1 := c07_aux_jb_rpow_neg_le_one y (P.p + 1) (by linarith)
    have h2 : 0 ≤ Cs * ε := mul_nonneg hCs.le hε.1
    rw [show -P.p - ((1 : ℕ) : ℝ) = -(P.p + 1) by push_cast; ring] at h
    nlinarith
  have hbc : ∀ y, |deriv c y| ≤ K₀ + M0 + Cs * ε := fun y => by
    have e : deriv c y = deriv f y - deriv a y - deriv b y := by rw [hderiv]; ring
    rw [e]
    have := abs_sub (deriv f y - deriv a y) (deriv b y)
    have := abs_sub (deriv f y) (deriv a y)
    linarith [hbf y, hM0 y, hbb y]
  refine ⟨?_, fun y => ?_⟩
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨hf, K₀, hbf⟩
    · exact ⟨h0, M0, hM0⟩
    · exact ⟨hs, Cs * ε, hbb⟩
    · exact ⟨ho, _, hbc⟩
  have hid := c07_divided_residual_identity P.p hp P.hp_hi ε hε1
  have hI : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → (∃ L, ∀ x, |deriv g x| ≤ L) →
      Integrable (fun z => (deriv g y - deriv g z) / |y - z| ^ (P.p + 1)) :=
    fun g hg hL => (hid g (hg.of_le (by simp)) hL y).1
  have hIa := hI a h0 ⟨M0, hM0⟩
  have hIb := hI b hs ⟨_, hbb⟩
  have hIc := hI c ho ⟨_, hbc⟩
  have hfr : fracDdy P.p f y = fracDdy P.p a y + fracDdy P.p b y + fracDdy P.p c y := by
    unfold fracDdy fracD
    have : (fun z => (deriv f y - deriv f z) / |y - z| ^ (P.p + 1)) =
        fun z => (deriv a y - deriv a z) / |y - z| ^ (P.p + 1) +
          (deriv b y - deriv b z) / |y - z| ^ (P.p + 1) +
          (deriv c y - deriv c z) / |y - z| ^ (P.p + 1) := by
      funext z; rw [hderiv, hderiv]; ring
    rw [this, integral_add, integral_add]
    all_goals first | exact hIa | exact hIb | exact hIc | exact hIa.add hIb | ring
  rw [(hid f (hf.of_le (by simp)) ⟨K₀, hbf⟩ y).2.2.2.2.1, ← hL0 y]
  simp only [L0]
  rw [hfr, hderiv, hfabc]
  ring

/-- Weighted `C¹` bound for `a G₊ + b G₋`. -/
theorem c07_aux_Gpm_comb_bound (P : parameters) (A : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b r : ℝ, |a| ≤ r → |b| ≤ r → ∀ y : ℝ,
      jb y ^ A * (|a * G_plus P.p y + b * G_minus P.p y| +
        |deriv (fun y' => a * G_plus P.p y' + b * G_minus P.p y') y|) ≤ r * K := by
  obtain ⟨-, -, ⟨Sp, hSp⟩, ⟨Sm, hSm⟩, -⟩ := c02_G_pm_properties P
  obtain ⟨Kp, hKp⟩ := c02_aux_schwartz_bound Sp A
  obtain ⟨Km, hKm⟩ := c02_aux_schwartz_bound Sm A
  have hjb : ∀ y, 0 < jb y ^ A := fun y => Real.rpow_pos_of_pos (c02_aux_jb_pos y) _
  have hKp0 : 0 ≤ Kp := le_trans (by have := hjb 0; positivity) (hKp 0)
  have hKm0 : 0 ≤ Km := le_trans (by have := hjb 0; positivity) (hKm 0)
  refine ⟨Kp + Km, by positivity, fun a b r ha hb y => ?_⟩
  rw [← hSp, ← hSm]
  have hdp : DifferentiableAt ℝ (⇑Sp) y := Sp.differentiableAt
  have hdm : DifferentiableAt ℝ (⇑Sm) y := Sm.differentiableAt
  have hd : deriv (fun y' => a * Sp y' + b * Sm y') y = a * deriv (⇑Sp) y + b * deriv (⇑Sm) y :=
    ((hdp.hasDerivAt.const_mul a).add (hdm.hasDerivAt.const_mul b)).deriv
  rw [hd]
  have h1 := hKp y
  have h2 := hKm y
  have hr : 0 ≤ r := (abs_nonneg a).trans ha
  have e1 : |a * Sp y + b * Sm y| + |a * deriv (⇑Sp) y + b * deriv (⇑Sm) y| ≤
      r * (|Sp y| + |deriv (⇑Sp) y|) + r * (|Sm y| + |deriv (⇑Sm) y|) := by
    have k1 := abs_add_le (a * Sp y) (b * Sm y)
    have k2 := abs_add_le (a * deriv (⇑Sp) y) (b * deriv (⇑Sm) y)
    rw [abs_mul, abs_mul] at k1 k2
    have k3 : |a| * |Sp y| ≤ r * |Sp y| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    have k4 : |b| * |Sm y| ≤ r * |Sm y| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    have k5 : |a| * |deriv (⇑Sp) y| ≤ r * |deriv (⇑Sp) y| :=
      mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    have k6 : |b| * |deriv (⇑Sm) y| ≤ r * |deriv (⇑Sm) y| :=
      mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    linarith
  have hw := hjb y
  calc jb y ^ A * (|a * Sp y + b * Sm y| + |a * deriv (⇑Sp) y + b * deriv (⇑Sm) y|)
      ≤ jb y ^ A * (r * (|Sp y| + |deriv (⇑Sp) y|) + r * (|Sm y| + |deriv (⇑Sm) y|)) :=
        mul_le_mul_of_nonneg_left e1 hw.le
    _ = r * (jb y ^ A * (|Sp y| + |deriv (⇑Sp) y|)) + r * (jb y ^ A * (|Sm y| + |deriv (⇑Sm) y|)) := by
        ring
    _ ≤ r * Kp + r * Km := by gcongr
    _ = r * (Kp + Km) := by ring

/-- Blueprint: lem:c07_G_mu_properties.  Properties of `G_μ`: (1) `μ_* ≠ 0`; `Ĝ_μ` is the
explicit Hermitian `C_c^∞` symbol supported in `[-2,-1] ∪ [1,2]`; `G_μ` is a real Schwartz
function (it has no `ε` argument); (2) `G_μ = Re(1-μ/μ_*) G₊ + Im(1-μ/μ_*) G₋`, `G_{μ_*} = 0`;
(3) weighted, `Y_γ` and Lipschitz-in-`μ` bounds. -/
theorem c07_G_mu_properties (P : parameters) :
    mu_star P.p ≠ 0 ∧
    (∀ μ : ℂ,
      (∀ ξ : ℝ, 0 < ξ → fourierT (fun x => (G_mu P.p μ x : ℂ)) ξ =
        (1 - μ / mu_star P.p) * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (Phi0 P.p ξ : ℂ)))) ∧
      (∀ ξ : ℝ, ξ < 0 → fourierT (fun x => (G_mu P.p μ x : ℂ)) ξ =
        (starRingEnd ℂ) (fourierT (fun x => (G_mu P.p μ x : ℂ)) (-ξ))) ∧
      fourierT (fun x => (G_mu P.p μ x : ℂ)) 0 = 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) (fourierT (fun x => (G_mu P.p μ x : ℂ))) ∧
      Function.support (fourierT (fun x => (G_mu P.p μ x : ℂ))) ⊆
        Icc (-2) (-1) ∪ Icc 1 2 ∧
      (∃ φ : SchwartzMap ℝ ℝ, ∀ x, φ x = G_mu P.p μ x)) ∧
    (∀ μ : ℂ, ∀ y : ℝ, G_mu P.p μ y =
      (1 - μ / mu_star P.p).re * G_plus P.p y + (1 - μ / mu_star P.p).im * G_minus P.p y) ∧
    (∀ y : ℝ, G_mu P.p (mu_star P.p) y = 0) ∧
    (∀ γ : ℝ, 0 < γ → ∀ N : ℝ, 0 ≤ N → ∃ C : ℝ, 0 < C ∧ ∀ μ ν : ℂ,
      (∀ y : ℝ, jb y ^ N * (|G_mu P.p μ y| + |deriv (G_mu P.p μ) y|) ≤
        C * ‖1 - μ / mu_star P.p‖) ∧
      G_mu P.p μ ∈ Y_gamma P.p γ ∧
      Y_gamma_norm P.p γ (G_mu P.p μ) ≤ ENNReal.ofReal (C * ‖1 - μ / mu_star P.p‖) ∧
      Y_gamma_norm P.p γ (fun y => G_mu P.p μ y - G_mu P.p ν y) ≤
        ENNReal.ofReal (C * ‖μ - ν‖ / ‖mu_star P.p‖) ∧
      ∀ y : ℝ, |G_mu P.p μ y - G_mu P.p ν y| +
          |deriv (fun y' => G_mu P.p μ y' - G_mu P.p ν y') y| ≤
        C * ‖μ - ν‖ / ‖mu_star P.p‖) := by
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hms := c02_aux_mu_star_ne P
  obtain ⟨hdec, hsch, hstar, -, hY⟩ := c02_G_mu_decomposition P
  have hF : ∀ μ : ℂ, fourierT (fun x => (G_mu P.p μ x : ℂ)) = G_pm_hat P.p (1 - μ / mu_star P.p) :=
    fun μ => funext fun ξ => c02_aux_fourierT_G_pm P.p _ ξ
  refine ⟨hms, fun μ => ⟨fun ξ hξ => ?_, fun ξ hξ => ?_, ?_, ?_, ?_, ?_⟩, fun μ y => ?_, fun y => ?_,
    fun γ hγ N hN => ?_⟩
  · rw [hF]; simp [G_pm_hat, hξ.le]
  · rw [hF]; simp [G_pm_hat, hξ.not_ge, show 0 ≤ -ξ by linarith]
  · rw [hF]; simp [G_pm_hat]
  · rw [hF]; exact c02_aux_G_pm_hat_smooth _
  · intro ξ hξ
    rw [hF] at hξ
    by_contra hc
    apply hξ
    rw [c02_aux_G_pm_hat_split]
    simp only [mem_union, mem_Icc, not_or, not_and_or, not_le] at hc
    have h1 : deriv chiPlus ξ / ξ = 0 := c02_aux_g_zero (by
      simp only [mem_Icc, not_and_or, not_le]
      rcases hc.2 with h | h
      · left; exact h
      · right; exact h)
    have h2 : deriv chiPlus (-ξ) / (-ξ) = 0 := c02_aux_g_zero (by
      simp only [mem_Icc, not_and_or, not_le]
      rcases hc.1 with h | h
      · right; linarith
      · left; linarith)
    simp [h1, h2]
  · obtain ⟨S, hS⟩ := (hsch μ).1
    exact ⟨S, fun x => congrFun hS x⟩
  · exact congrFun (hdec μ) y
  · rw [hstar]; rfl
  -- quantitative bounds
  obtain ⟨K, hK0, hK⟩ := c07_aux_Gpm_comb_bound P (N + γ + 1)
  have hjb1 := c07_aux_one_le_jb
  have hw : ∀ y : ℝ, ∀ e : ℝ, e ≤ N + γ + 1 → jb y ^ e ≤ jb y ^ (N + γ + 1) := fun y e he =>
    Real.rpow_le_rpow_of_exponent_le (hjb1 y) he
  -- generic combination `F = a G₊ + b G₋`
  have hgen : ∀ a b r : ℝ, |a| ≤ r → |b| ≤ r →
      (∀ y, jb y ^ N * (|a * G_plus P.p y + b * G_minus P.p y| +
        |deriv (fun y' => a * G_plus P.p y' + b * G_minus P.p y') y|) ≤ r * K) ∧
      Y_gamma_norm P.p γ (fun y => a * G_plus P.p y + b * G_minus P.p y) ≤
        ENNReal.ofReal (2 * (r * K)) ∧
      (∀ y, |a * G_plus P.p y + b * G_minus P.p y| +
        |deriv (fun y' => a * G_plus P.p y' + b * G_minus P.p y') y| ≤ r * K) := by
    intro a b r ha hb
    have hr : 0 ≤ r := (abs_nonneg a).trans ha
    set F := fun y => a * G_plus P.p y + b * G_minus P.p y with hFd
    have hb' : ∀ y e, e ≤ N + γ + 1 → jb y ^ e * (|F y| + |deriv F y|) ≤ r * K := fun y e he =>
      (mul_le_mul_of_nonneg_right (hw y e he) (by positivity)).trans (hK a b r ha hb y)
    refine ⟨fun y => hb' y N (by linarith), ?_, fun y => ?_⟩
    · have hle := c07_aux_Ynorm_le_of_pointwise P.p γ F (r * K) (r * K) (fun y _ => ?_) (fun y _ => ?_)
      · rw [show 2 * (r * K) = r * K + r * K by ring,
          ENNReal.ofReal_add (by positivity) (by positivity)]
        exact hle
      · have h1 : jb y ^ (-1 / P.p) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (hjb1 y) (by
            have : 0 < 1 / P.p := by positivity
            rw [neg_div]; linarith)
        have := hb' y γ (by linarith)
        have hd : jb y ^ (-1 / P.p) * |deriv F y| ≤ |deriv F y| :=
          mul_le_of_le_one_left (abs_nonneg _) h1
        calc jb y ^ γ * (|F y| + jb y ^ (-1 / P.p) * |deriv F y|)
            ≤ jb y ^ γ * (|F y| + |deriv F y|) :=
              mul_le_mul_of_nonneg_left (by linarith)
                (Real.rpow_nonneg (by linarith [hjb1 y]) _)
          _ ≤ r * K := this
      · have := hb' y (γ + 1) (by linarith)
        have hj0 : 0 < jb y := by linarith [hjb1 y]
        rw [Real.rpow_add hj0, Real.rpow_one] at this
        have h2 : jb y ^ γ * (|F y| + jb y * |deriv F y|) ≤ jb y ^ γ * jb y * (|F y| + |deriv F y|) := by
          have hg : 0 ≤ jb y ^ γ := Real.rpow_nonneg hj0.le _
          have : |F y| ≤ jb y * |F y| := le_mul_of_one_le_left (abs_nonneg _) (hjb1 y)
          nlinarith [abs_nonneg (F y), abs_nonneg (deriv F y)]
        linarith
    · have := hb' y 0 (by linarith)
      rwa [Real.rpow_zero, one_mul] at this
  set z := fun μ : ℂ => 1 - μ / mu_star P.p with hz
  have hGF : ∀ μ, G_mu P.p μ = fun y => (z μ).re * G_plus P.p y + (z μ).im * G_minus P.p y := hdec
  have hdiff : ∀ μ ν : ℂ, (fun y => G_mu P.p μ y - G_mu P.p ν y) =
      fun y => (z μ - z ν).re * G_plus P.p y + (z μ - z ν).im * G_minus P.p y := by
    intro μ ν; funext y; rw [hGF μ, hGF ν]; simp only [Complex.sub_re, Complex.sub_im]; ring
  have hzz : ∀ μ ν : ℂ, ‖z μ - z ν‖ = ‖μ - ν‖ / ‖mu_star P.p‖ := by
    intro μ ν
    simp only [hz]
    rw [show 1 - μ / mu_star P.p - (1 - ν / mu_star P.p) = -((μ - ν) / mu_star P.p) by ring,
      norm_neg, norm_div]
  refine ⟨2 * K + 1, by positivity, fun μ ν => ?_⟩
  obtain ⟨g1, g2, -⟩ := hgen (z μ).re (z μ).im ‖z μ‖ (Complex.abs_re_le_norm _)
    (Complex.abs_im_le_norm _)
  obtain ⟨-, d2, d3⟩ := hgen (z μ - z ν).re (z μ - z ν).im ‖z μ - z ν‖
    (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
  have hn1 : 0 ≤ ‖z μ‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖z μ - z ν‖ := norm_nonneg _
  refine ⟨fun y => ?_, (hY γ).1 μ, ?_, ?_, fun y => ?_⟩
  · rw [hGF μ]
    refine (g1 y).trans ?_
    show ‖z μ‖ * K ≤ (2 * K + 1) * ‖z μ‖
    nlinarith
  · rw [hGF μ]
    refine g2.trans (ENNReal.ofReal_le_ofReal ?_)
    show 2 * (‖z μ‖ * K) ≤ (2 * K + 1) * ‖z μ‖
    nlinarith
  · rw [hdiff μ ν]
    refine d2.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_assoc, ← hzz]
    nlinarith
  · have e := congrFun (hdiff μ ν) y
    rw [hdiff μ ν, e]
    refine (d3 y).trans ?_
    rw [mul_div_assoc, ← hzz]
    nlinarith


/-! ### Residual bounds for `y ≤ -8R` -/

/-- Blueprint: lem:c07_QW_negative.  For `0 ≤ ε ≤ 1`, `y < 0`: the integral defining
`𝒬_ε(W)(y)` converges absolutely and
`𝒬_ε(W)(y) = -c_α|y|^{-p} ∫₀¹ (A_ε(t)-1) t^{p-1} dt = -(p+1) c₋ |y|^{-p}`. -/
theorem c07_QW_negative (P : parameters) (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) (y : ℝ) (hy : y < 0) :
    Integrable (fun z => (deriv corner y - deriv corner z) / |y - z| ^ (P.p + 1) *
      (A_eps P.p ε (c01_secant corner y z) - 1)) ∧
    c01_Q_eps P.p ε corner y =
      -calpha P.p * |y| ^ (-P.p) * ∫ t in (0 : ℝ)..1, (A_eps P.p ε t - 1) * t ^ (P.p - 1) ∧
    c01_Q_eps P.p ε corner y = -(P.p + 1) * c_minus P.p ε * |y| ^ (-P.p) := by
  set p := P.p with hpdef
  have hp0 : 0 < p := by linarith [P.hp_lo]
  have hp1 : p < 1 := P.hp_hi
  set a := -y with ha
  have ha0 : 0 < a := by linarith
  have hya : |y| = a := by rw [abs_of_neg hy]
  set G : ℝ → ℝ := fun t => (A_eps p ε t - 1) * t ^ (p - 1) with hG
  set g : ℝ → ℝ := fun z => -((A_eps p ε (a / (a + z)) - 1) / (a + z) ^ (p + 1)) with hg
  set ψ : ℝ → ℝ := fun z => a / (a + z) with hψ
  set ψ' : ℝ → ℝ := fun z => -a / (a + z) ^ 2 with hψ'
  have hae : (fun z => (deriv corner y - deriv corner z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant corner y z) - 1)) =ᵐ[volume] (Ioi (0:ℝ)).indicator g := by
    have hfin : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 ∧ z ≠ y := by
      have h1 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton _)
      have h2 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ y := compl_mem_ae_iff.mpr (measure_singleton _)
      filter_upwards [h1, h2] with z h1 h2 using ⟨h1, h2⟩
    filter_upwards [hfin] with z ⟨hz0, hzy⟩
    rw [c04_aux_deriv_corner y hy.ne, c04_aux_deriv_corner z hz0]
    simp only [hy, ite_true]
    by_cases hz : z < 0
    · simp only [hz, ite_true]
      rw [indicator_of_notMem (by simp; linarith)]
      simp
    · simp only [hz, ite_false]
      have hz' : 0 < z := lt_of_le_of_ne (not_lt.1 hz) (Ne.symm hz0)
      rw [indicator_of_mem (mem_Ioi.mpr hz')]
      have hyz : y - z < 0 := by linarith
      simp only [hg, c01_secant, show ¬ (y = z) from Ne.symm hzy, ite_false, corner,
        abs_of_neg hyz]
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      have e1 : -y - 0 = a := by rw [ha]; ring
      have e2 : -(y - z) = a + z := by rw [ha]; ring
      have e3 : (-y - 0) / (y - z) = -(a / (a + z)) := by
        rw [e1, show y - z = -(a + z) by rw [← e2]; ring, div_neg]
      rw [e2, e3, c04_aux_A_even]
      ring
  have himg : ψ '' Ioi 0 = Ioo 0 1 := by
    ext t; simp only [mem_image, mem_Ioi, mem_Ioo, hψ]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨div_pos ha0 (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
    · rintro ⟨h0, h1⟩
      refine ⟨a * (1 - t) / t, div_pos (mul_pos ha0 (by linarith)) h0, ?_⟩
      field_simp
      ring
  have hder : ∀ z ∈ Ioi (0:ℝ), HasDerivWithinAt ψ (ψ' z) (Ioi 0) z := by
    intro z hz
    have hz' : a + z ≠ 0 := by linarith [mem_Ioi.mp hz]
    have := (hasDerivAt_const z a).div ((hasDerivAt_const z a).add (hasDerivAt_id' z)) hz'
    refine HasDerivWithinAt.congr_deriv (this.hasDerivWithinAt) ?_
    show _ = -a / (a + z) ^ 2
    simp only [Pi.add_apply]
    field_simp; ring
  have hinj : InjOn ψ (Ioi 0) := by
    intro u hu v hv huv
    have hu' : a + u ≠ 0 := by linarith [mem_Ioi.mp hu]
    have hv' : a + v ≠ 0 := by linarith [mem_Ioi.mp hv]
    simp only [hψ] at huv
    rw [div_eq_div_iff hu' hv'] at huv
    have : a * (u - v) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have e1 : a ^ (-p) * a * a ^ (p - 1) = 1 := by
    have : a ^ (-p) * a ^ (1:ℝ) * a ^ (p - 1) = a ^ ((-p) + 1 + (p - 1)) := by
      rw [rpow_add ha0, rpow_add ha0]
    rw [rpow_one] at this; rw [this]; norm_num
  have hpt : ∀ z ∈ Ioi (0:ℝ), g z = -(a ^ (-p) * (|ψ' z| • G (ψ z))) := by
    intro z hz
    have hz' : 0 < z := hz
    have hu0 : 0 < a + z := by linarith
    have e2 : (a + z) ^ (2:ℕ) * (a + z) ^ (p - 1) = (a + z) ^ (p + 1) := by
      rw [← rpow_natCast, ← rpow_add hu0]; norm_num; ring_nf
    have h2 : |-a / (a + z) ^ 2| = a / (a + z) ^ 2 := by
      rw [abs_div, abs_neg, abs_of_pos ha0, abs_of_pos (by positivity)]
    simp only [hg, smul_eq_mul, hG, hψ, hψ']
    rw [h2, div_rpow ha0.le hu0.le]
    congr 1
    calc (A_eps p ε (a / (a + z)) - 1) / (a + z) ^ (p + 1)
        = (A_eps p ε (a / (a + z)) - 1) * (a ^ (-p) * a * a ^ (p - 1)) /
            ((a + z) ^ (2:ℕ) * (a + z) ^ (p - 1)) := by rw [e1, e2, mul_one]
      _ = _ := by
        generalize (a + z) ^ (2:ℕ) = U2
        generalize (a + z) ^ (p - 1) = U3
        generalize A_eps p ε (a / (a + z)) = b
        ring
  have hw : IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hGint : IntegrableOn G (Ioo 0 1) := by
    refine Integrable.mono' (hw.const_mul ε) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((c04_aux_A_cont p ε hε.1).continuousOn.sub continuousOn_const).mul ?_
      exact ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inl (by linarith [ht.1]))
    · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
      have hpos : 0 ≤ t ^ (p - 1) := rpow_nonneg (by linarith [ht.1]) _
      simp only [hG, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
      have ht' : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      exact mul_le_mul_of_nonneg_right (c04_aux_A_sub_one p ε t hp0 hp1.le hε.1 ht') hpos
  have hint2 : IntegrableOn (fun z => |ψ' z| • G (ψ z)) (Ioi 0) := by
    rw [← integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj, himg]
    exact hGint
  have hgint : IntegrableOn g (Ioi 0) := by
    exact IntegrableOn.congr_fun ((Integrable.const_mul hint2 (a ^ (-p))).neg)
      (fun z hz => (hpt z hz).symm) measurableSet_Ioi
  have hgval : ∫ z in Ioi 0, g z = -(a ^ (-p) * ∫ t in (0:ℝ)..1, G t) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_neg, integral_const_mul,
      ← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj, himg,
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hQ : c01_Q_eps p ε corner y =
      -calpha p * |y| ^ (-p) * ∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * t ^ (p - 1) := by
    unfold c01_Q_eps
    rw [integral_congr_ae hae, integral_indicator measurableSet_Ioi, hgval, hya]
    ring
  refine ⟨(integrable_congr hae).mpr ((integrable_indicator_iff measurableSet_Ioi).mpr hgint),
    hQ, ?_⟩
  rw [hQ]
  unfold c_minus
  field_simp

/-- Blueprint: lem:c07_negative_slow.  For `y ≤ -8R`:
`ℒ₀(f_slow) + 𝒬_ε(W) = |D|^p f_slow'` and
`|∂^j(ℒ₀(f_slow) + 𝒬_ε(W))(y)| ≤ Cε⟨y⟩^{-2p-1-j}`, `j ∈ {0,1}`. -/
theorem c07_negative_slow (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y ≤ -8 * R,
      L0 P.p (fam_slow P.p R ε) y + c01_Q_eps P.p ε corner y = fracDdy P.p (fam_slow P.p R ε) y ∧
      ∀ j ≤ 1, |iteratedDeriv j (fun y' => L0 P.p (fam_slow P.p R ε) y' +
          c01_Q_eps P.p ε corner y') y| ≤ C * ε * jb y ^ (-2 * P.p - 1 - j) := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨R₀, ε₀, hR₀, he0, he1, hS⟩ := c07_slow_bounds P δ hδ hδ'
  obtain ⟨Cf, hCf, hF⟩ := c07_fractional_decay P.p hp P.hp_hi
  refine ⟨R₀, ε₀, hR₀, he0, he1, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans hR₀ hR
  have hR0 : 0 < R := by linarith
  obtain ⟨Cs, hCs, hB⟩ := hS R hR
  refine ⟨Cf * Cs, by positivity, fun ε hε μ _ y hy => ?_⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans he1⟩
  obtain ⟨-, hder, heqn⟩ := hB ε hε
  set f := fam_slow P.p R ε with hf
  -- the identity on `(-∞, -2R)`
  have hid : ∀ y' < -2 * R, L0 P.p f y' + c01_Q_eps P.p ε corner y' = fracDdy P.p f y' := by
    intro y' hy'
    have hy'0 : y' < 0 := by linarith
    have hev : f =ᶠ[𝓝 y'] fun t => c_minus P.p ε * (-t) ^ (-P.p) := by
      filter_upwards [Iio_mem_nhds hy'] with t ht
      rw [heqn t (mem_Iio.1 ht).le, abs_of_neg (by linarith [mem_Iio.1 ht])]
    have hd : HasDerivAt (fun t => c_minus P.p ε * (-t) ^ (-P.p))
        (c_minus P.p ε * (-P.p * (-y') ^ (-P.p - 1) * (-1))) y' := by
      have h1 := (Real.hasDerivAt_rpow_const (p := -P.p) (Or.inl (show -y' ≠ 0 by linarith))).comp
        y' (hasDerivAt_neg y')
      exact h1.const_mul _
    have hfd : deriv f y' = c_minus P.p ε * (-P.p * (-y') ^ (-P.p - 1) * (-1)) := by
      rw [hev.deriv_eq]; exact hd.deriv
    have hfv : f y' = c_minus P.p ε * (-y') ^ (-P.p) := by
      rw [heqn y' (by linarith), abs_of_neg hy'0]
    have hQ := (c07_QW_negative P ε hε1 y' hy'0).2.2
    rw [abs_of_neg hy'0] at hQ
    have ha : 0 < -y' := by linarith
    have hpow : (-y') ^ (-P.p - 1) * (-y') = (-y') ^ (-P.p) := by
      rw [Real.rpow_sub_one ha.ne', div_mul_cancel₀ _ ha.ne']
    unfold L0
    rw [hfd, hfv, hQ]
    have : y' * (c_minus P.p ε * (-P.p * (-y') ^ (-P.p - 1) * (-1))) =
        -(c_minus P.p ε * P.p * ((-y') ^ (-P.p - 1) * (-y'))) := by ring
    rw [this, hpow]
    ring
  refine ⟨hid y (by linarith), fun j hj => ?_⟩
  have hev : (fun y' => L0 P.p f y' + c01_Q_eps P.p ε corner y') =ᶠ[𝓝 y] fracDdy P.p f := by
    filter_upwards [Iio_mem_nhds (show y < -2 * R by linarith)] with t ht
    exact hid t ht
  rw [hev.iteratedDeriv_eq]
  have hK : 0 ≤ Cs * ε := mul_nonneg hCs.le hε.1
  have hsm : ContDiff ℝ 3 f := (c07_aux_slow_smooth P.p R ε hR0).of_le (by simp)
  have hy1 : 1 ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
  have := (hF (Cs * ε) hK f hsm (fun i hi y => by
    have := hder i hi y; rw [mul_assoc] at this ⊢; linarith)).2.2 j hj y hy1
  calc _ ≤ Cf * (Cs * ε) * jb y ^ (-2 * P.p - 1 - j) := this
    _ = _ := by ring

/-- For `f ∈ C¹` vanishing on `(-∞,R]`, bounded with bounded derivative, and `y < 0`:
`ℒ₀ f(y) = -c_α (p+1) ∫_R^∞ f(z)(z-y)^{-p-2} dz`. -/
theorem c07_aux_osc_identity (p : ℝ) (hp : 0 < p) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (R : ℝ)
    (hR : 0 < R) (hz : ∀ y ≤ R, f y = 0) (B0 B1 : ℝ) (hB0 : ∀ y, |f y| ≤ B0)
    (hB1 : ∀ y, |deriv f y| ≤ B1) (y : ℝ) (hy : y < 0) :
    IntegrableOn (fun z => f z / (z - y) ^ (p + 2)) (Ioi R) ∧
    L0 p f y = -calpha p * (p + 1) * ∫ z in Ioi R, f z / (z - y) ^ (p + 2) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  have hB10 : 0 ≤ B1 := (abs_nonneg _).trans (hB1 0)
  -- `f = f' = 0` on `(-∞,R)`
  have hzero' : ∀ x < R, deriv f x = 0 := fun x hx => by
    have : f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with t ht using hz t (mem_Iio.1 ht).le
    rw [this.deriv_eq]; simp
  have hzy : ∀ z ∈ Ioi R, 0 < z - y := fun z hz => by linarith [mem_Ioi.1 hz]
  -- integrability of the rpow majorants
  have hr1 : IntegrableOn (fun z : ℝ => z ^ (-(p + 1))) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hR
  have hr2 : IntegrableOn (fun z : ℝ => z ^ (-(p + 2))) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hR
  have hcmp : ∀ (r : ℝ), 0 ≤ r → ∀ z ∈ Ioi R, (z - y) ^ (-r) ≤ z ^ (-r) := fun r hr z hz =>
    Real.rpow_le_rpow_of_nonpos (by linarith [mem_Ioi.1 hz]) (by linarith) (by linarith)
  set u : ℝ → ℝ := fun z => (z - y) ^ (-(p + 1)) with hu
  set u' : ℝ → ℝ := fun z => -(p + 1) * (z - y) ^ (-(p + 1) - 1) with hu'
  have hud : ∀ z ∈ Ioi R, HasDerivAt u (u' z) z := by
    intro z hz
    have := (Real.hasDerivAt_rpow_const (p := -(p + 1)) (Or.inl (hzy z hz).ne')).comp z
      ((hasDerivAt_id z).sub_const y)
    convert this using 1
    · funext x; simp only [hu, Function.comp_apply, id]
    · simp only [hu']; ring_nf
  have hvd : ∀ z ∈ Ioi R, HasDerivAt f (deriv f z) z := fun z _ => (hfd z).hasDerivAt
  have hmu : Measurable u := by simp only [hu]; fun_prop
  have hmu' : Measurable u' := by simp only [hu']; fun_prop
  have huv' : IntegrableOn (u * deriv f) (Ioi R) := by
    refine (hr1.const_mul B1).mono' (hmu.mul (measurable_deriv f)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun z hz => ?_)
    simp only [Pi.mul_apply, hu, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg (hzy z hz).le _), mul_comm]
    exact mul_le_mul (hB1 z) (hcmp _ (by linarith) z hz) (Real.rpow_nonneg (hzy z hz).le _) hB10
  have hu'v : IntegrableOn (u' * f) (Ioi R) := by
    refine (hr2.const_mul ((p + 1) * B0)).mono' (hmu'.mul hfc.measurable).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun z hz => ?_)
    simp only [Pi.mul_apply, hu', Real.norm_eq_abs, abs_mul, abs_neg]
    rw [abs_of_nonneg (Real.rpow_nonneg (hzy z hz).le _), abs_of_pos (by linarith : 0 < p + 1),
      show -(p + 1) - 1 = -(p + 2) by ring]
    have h1 := hcmp (p + 2) (by linarith) z hz
    have h2 := hB0 z
    have h3 : 0 ≤ (z - y) ^ (-(p + 2)) := Real.rpow_nonneg (hzy z hz).le _
    have h4 : 0 ≤ z ^ (-(p + 2)) := Real.rpow_nonneg (by linarith [mem_Ioi.1 hz]) _
    calc (p + 1) * (z - y) ^ (-(p + 2)) * |f z| ≤ (p + 1) * z ^ (-(p + 2)) * B0 := by gcongr
      _ = (p + 1) * B0 * z ^ (-(p + 2)) := by ring
  have h0 : Tendsto (u * f) (𝓝[>] R) (𝓝 0) := by
    have hc : ContinuousAt (u * f) R := by
      refine ContinuousAt.mul ?_ hfc.continuousAt
      exact (continuousAt_id.sub continuousAt_const).rpow_const (Or.inl (by simp; linarith))
    have : (u * f) R = 0 := by simp [hz R le_rfl]
    rw [← this]; exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (u * f) atTop (𝓝 0) := by
    have ht : Tendsto (fun z => (z - y) ^ (-(p + 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have ht2 : Tendsto (fun z => B0 * (z - y) ^ (-(p + 1))) atTop (𝓝 0) := by
      simpa using ht.const_mul B0
    refine squeeze_zero_norm' ?_ ht2
    filter_upwards [eventually_gt_atTop y] with z hz
    simp only [Pi.mul_apply, hu, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB0 z) (Real.rpow_nonneg (by linarith) _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd huv' hu'v h0 hinf
  -- the target integrand
  have hgoal_eq : ∀ z ∈ Ioi R, f z / (z - y) ^ (p + 2) = -(1 / (p + 1)) * (u' z * f z) := by
    intro z hz
    simp only [hu']
    rw [show -(p + 1) - 1 = -(p + 2) by ring, Real.rpow_neg (hzy z hz).le]
    field_simp
  have hint : IntegrableOn (fun z => f z / (z - y) ^ (p + 2)) (Ioi R) :=
    IntegrableOn.congr_fun (hu'v.const_mul (-(1 / (p + 1))))
      (fun z hz => (hgoal_eq z hz).symm) measurableSet_Ioi
  refine ⟨hint, ?_⟩
  -- `ℒ₀ f(y) = |D|^p f'(y)`
  have hfy : f y = 0 := hz y (by linarith)
  have hdy : deriv f y = 0 := hzero' y (by linarith)
  have hae : (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1)) =ᵐ[volume]
      (Ioi R).indicator (fun z => -(u z * deriv f z)) := by
    have hR' : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ R := compl_mem_ae_iff.mpr (measure_singleton _)
    filter_upwards [hR'] with z hzR
    rcases lt_or_gt_of_ne hzR with h | h
    · rw [indicator_of_notMem (by simp; linarith), hdy, hzero' z h]; simp
    · rw [indicator_of_mem (mem_Ioi.2 h), hdy, abs_sub_comm, abs_of_pos (by linarith)]
      simp only [hu]
      rw [Real.rpow_neg (by linarith)]
      ring
  unfold L0 fracDdy fracD
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioi, integral_neg]
  rw [hibp, hfy, hdy, setIntegral_congr_fun measurableSet_Ioi hgoal_eq, integral_const_mul]
  field_simp
  ring

/-- Decay of `Φ(y) = ∫_R^∞ f(z)(z-y)^{-p-2} dz` and of its derivative for `y < 0`, `R ≥ 1`. -/
theorem c07_aux_osc_Phi (p : ℝ) (hp : 0 < p) (f : ℝ → ℝ) (hfc : Continuous f) (hfi : Integrable f)
    (R : ℝ) (hR : 1 ≤ R) (y : ℝ) (hy : y < 0) :
    |∫ z in Ioi R, f z / (z - y) ^ (p + 2)| ≤ (∫ z, |f z|) * |y| ^ (-(p + 2)) ∧
    ∃ D : ℝ, HasDerivAt (fun y' => ∫ z in Ioi R, f z / (z - y') ^ (p + 2)) D y ∧
      |D| ≤ (p + 2) * (∫ z, |f z|) * |y| ^ (-(p + 3)) := by
  have hY : 0 < |y| := abs_pos.2 hy.ne
  have hYe : |y| = -y := abs_of_neg hy
  set μR := (volume : Measure ℝ).restrict (Ioi R) with hμR
  have hL1 : (∫ z in Ioi R, |f z|) ≤ ∫ z, |f z| :=
    setIntegral_le_integral hfi.abs (Eventually.of_forall fun z => abs_nonneg _)
  have hL0 : 0 ≤ ∫ z, |f z| := integral_nonneg fun z => abs_nonneg _
  set F : ℝ → ℝ → ℝ := fun y' z => f z * (z - y') ^ (-(p + 2)) with hF
  set F' : ℝ → ℝ → ℝ := fun y' z => f z * ((p + 2) * (z - y') ^ (-(p + 3))) with hF'
  have hrw : ∀ y' < R, ∫ z in Ioi R, f z / (z - y') ^ (p + 2) = ∫ z in Ioi R, F y' z := by
    intro y' hy'
    refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    simp only [hF]
    rw [Real.rpow_neg (by linarith [mem_Ioi.1 hz]), div_eq_mul_inv]
  -- bound for `F y`
  have hFb : ∀ z ∈ Ioi R, ‖F y z‖ ≤ |f z| * |y| ^ (-(p + 2)) := by
    intro z hz
    have hz' : R < z := hz
    simp only [hF, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hY (by rw [hYe]; linarith)
      (by linarith)) (abs_nonneg _)
  have hmF : ∀ y', Measurable (F y') := fun y' => by
    have := hfc.measurable; simp only [hF]; fun_prop
  have hmF' : ∀ y', Measurable (F' y') := fun y' => by
    have := hfc.measurable; simp only [hF']; fun_prop
  have hFi : Integrable (F y) μR :=
    (hfi.abs.mul_const _).integrableOn.mono' (hmF y).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hFb))
  refine ⟨?_, ?_⟩
  · rw [hrw y (by linarith)]
    calc |∫ z in Ioi R, F y z| = ‖∫ z in Ioi R, F y z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z in Ioi R, |f z| * |y| ^ (-(p + 2)) :=
          norm_integral_le_of_norm_le (hfi.abs.mul_const _).integrableOn
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hFb))
      _ = (∫ z in Ioi R, |f z|) * |y| ^ (-(p + 2)) := integral_mul_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hL1 (Real.rpow_nonneg hY.le _)
  -- derivative
  set bound : ℝ → ℝ := fun z => |f z| * ((p + 2) * |y| ^ (-(p + 3))) with hbound
  have hball : ∀ y' ∈ Metric.ball y (1 / 2), ∀ z ∈ Ioi R, |y| < z - y' := by
    intro y' hy' z hz
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy'
    have : R < z := hz
    rw [hYe]; linarith
  have hdiff : ∀ z ∈ Ioi R, ∀ y' ∈ Metric.ball y (1 / 2),
      HasDerivAt (fun y'' => F y'' z) (F' y' z) y' := by
    intro z hz y' hy'
    have hpos : 0 < z - y' := lt_trans hY (hball y' hy' z hz)
    have h1 := (Real.hasDerivAt_rpow_const (p := -(p + 2)) (Or.inl hpos.ne')).comp y'
      ((hasDerivAt_const y' z).sub (hasDerivAt_id y'))
    have h2 := h1.const_mul (f z)
    convert h2 using 1
    · rfl
    · simp only [hF']; rw [show -(p + 2) - 1 = -(p + 3) by ring]; ring
  have hbd : ∀ z ∈ Ioi R, ∀ y' ∈ Metric.ball y (1 / 2), ‖F' y' z‖ ≤ bound z := by
    intro z hz y' hy'
    have hlt := hball y' hy' z hz
    simp only [hF', hbound, Real.norm_eq_abs, abs_mul]
    rw [abs_of_pos (by linarith : (0:ℝ) < p + 2),
      abs_of_nonneg (Real.rpow_nonneg (show (0:ℝ) ≤ z - y' by linarith) _)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hY hlt.le (show -(p + 3) ≤ 0 by linarith)) (by linarith)) (abs_nonneg _)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μR) (F := F) (F' := F')
    (x₀ := y) (bound := bound) (Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1 / 2))
    (Eventually.of_forall fun y' => (hmF y').aestronglyMeasurable) hFi
    (hmF' y).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbd))
    (hfi.abs.mul_const _).integrableOn
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hdiff))
  refine ⟨∫ z in Ioi R, F' y z, ?_, ?_⟩
  · have hev : (fun y' => ∫ z in Ioi R, f z / (z - y') ^ (p + 2)) =ᶠ[𝓝 y]
        fun y' => ∫ z in Ioi R, F y' z := by
      filter_upwards [Iio_mem_nhds (show y < R by linarith)] with y' hy'
      exact hrw y' hy'
    exact hD.congr_of_eventuallyEq hev
  · have hb : ∀ z ∈ Ioi R, ‖F' y z‖ ≤ bound z := fun z hz =>
      hbd z hz y (Metric.mem_ball_self (by norm_num))
    calc |∫ z in Ioi R, F' y z| = ‖∫ z in Ioi R, F' y z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z in Ioi R, bound z :=
          norm_integral_le_of_norm_le (hfi.abs.mul_const _).integrableOn
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb))
      _ = (∫ z in Ioi R, |f z|) * ((p + 2) * |y| ^ (-(p + 3))) := integral_mul_const _ _
      _ ≤ (∫ z, |f z|) * ((p + 2) * |y| ^ (-(p + 3))) :=
          mul_le_mul_of_nonneg_right hL1 (by positivity)
      _ = _ := by ring

/-- Blueprint: lem:c07_negative_osc.  For `y ≤ -8R`:
`ℒ₀(f_osc)(y) = -c_α α ∫_R^∞ f_osc(z)/(z-y)^{α+1} dz` (absolutely convergent) and
`|∂^j ℒ₀(f_osc)(y)| ≤ Cε⟨y⟩^{-p-2-j} ≤ Cε⟨y⟩^{-2p-1-j}`. -/
theorem c07_negative_osc (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y ≤ -8 * R,
      IntegrableOn (fun z => fam_osc P.p R ε μ z / (z - y) ^ (P.p + 2)) (Ioi R) ∧
      L0 P.p (fam_osc P.p R ε μ) y =
        -calpha P.p * (P.p + 1) * ∫ z in Ioi R, fam_osc P.p R ε μ z / (z - y) ^ (P.p + 2) ∧
      ∀ j ≤ 1,
        |iteratedDeriv j (L0 P.p (fam_osc P.p R ε μ)) y| ≤ C * ε * jb y ^ (-P.p - 2 - j) ∧
        |iteratedDeriv j (L0 P.p (fam_osc P.p R ε μ)) y| ≤ C * ε * jb y ^ (-2 * P.p - 1 - j) := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  have hβ : 0 < beta P.p := by unfold beta; positivity
  have hc := c03_aux_calpha_pos P.p hp hp1
  obtain ⟨e1, ⟨he1, he11⟩, R1, hR1, hPD, hzero, CL, hCL, hL1⟩ :=
    c07_ext_approx_phase_differences P.p P.hp_lo P.hp_hi δ hδ hδ'
  obtain ⟨R2, e2, hR2, he2, -, hS⟩ := c07_family_smooth P δ hδ hδ'
  obtain ⟨C0, hC0, h0⟩ := hPD 0
  obtain ⟨C1, hC1, h1⟩ := hPD 1
  refine ⟨max R1 R2, min e1 e2, le_trans hR2 (le_max_right _ _), lt_min he1 he2,
    (min_le_left _ _).trans he11, fun R hR => ?_⟩
  have hRa : R1 ≤ R := le_trans (le_max_left _ _) hR
  have hRb : R2 ≤ R := le_trans (le_max_right _ _) hR
  have hR1' : 1 ≤ R := le_trans hR2 hRb
  set K := calpha P.p * (P.p + 1) * (P.p + 2) * CL with hK
  refine ⟨16 * K + 1, by positivity, fun ε hε μ hμ y hy => ?_⟩
  have hεa : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεb : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  obtain ⟨-, -, -, hfs, -, -⟩ := hS R hRb ε hεb μ hμ
  obtain ⟨hfi, hfL1, hfL1'⟩ := hL1 R hRa ε hεa μ hμ
  set f := fam_osc P.p R ε μ with hfdef
  have hz : ∀ y ≤ R, f y = 0 := fun y hy => hzero R hRa ε hεa μ hμ y hy
  have hf1 : ContDiff ℝ 1 f := hfs.of_le (by simp)
  have hzero' : ∀ x < R, deriv f x = 0 := fun x hx => by
    have : f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with t ht using hz t (mem_Iio.1 ht).le
    rw [this.deriv_eq]; simp
  have hB0 : ∀ x, |f x| ≤ C0 := by
    intro x
    rcases le_or_gt R x with hx | hx
    · have := (h0 R hRa ε hεa μ hμ x hx).2.2.2
      simp only [iteratedDeriv_zero] at this
      refine this.trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) hC0.le).trans ?_)
      have : jb x ^ (-beta P.p + (((0 : ℕ) : ℝ) - 1) / P.p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (c07_aux_one_le_jb x) (by
          have : 0 < 1 / P.p := by positivity
          push_cast; rw [zero_sub, neg_div]; linarith)
      nlinarith
    · rw [hz x hx.le, abs_zero]; exact hC0.le
  have hB1 : ∀ x, |deriv f x| ≤ C1 := by
    intro x
    rcases le_or_gt R x with hx | hx
    · have := (h1 R hRa ε hεa μ hμ x hx).2.2.2
      simp only [iteratedDeriv_one] at this
      refine this.trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) hC1.le).trans ?_)
      have : jb x ^ (-beta P.p + (((1 : ℕ) : ℝ) - 1) / P.p) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (c07_aux_one_le_jb x) (by
          push_cast; rw [sub_self, zero_div]; linarith)
      nlinarith
    · rw [hzero' x hx, abs_zero]; exact hC1.le
  have hy0 : y < 0 := by linarith
  have hid := fun y' (hy' : y' < 0) => c07_aux_osc_identity P.p hp f hf1 R (by linarith) hz C0 C1
    hB0 hB1 y' hy'
  obtain ⟨hint, heq⟩ := hid y hy0
  refine ⟨hint, heq, fun j hj => ?_⟩
  have hL1e : (∫ z, |f z|) ≤ CL * ε := hfL1.trans hfL1'
  obtain ⟨hΦ0, D, hD, hDb⟩ := c07_aux_osc_Phi P.p hp f hfs.continuous hfi R hR1' y hy0
  have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; linarith
  have hfirst : |iteratedDeriv j (L0 P.p f) y| ≤ (16 * K + 1) * ε * jb y ^ (-P.p - 2 - j) := by
    have hjb := c07_aux_abs_rpow_le_jb y (-P.p - 2 - j) hy1 (by
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith) (by
      have : (j:ℝ) ≤ 1 := by exact_mod_cast hj
      linarith)
    have hw0 : 0 ≤ jb y ^ (-P.p - 2 - j) := Real.rpow_nonneg (by linarith [c07_aux_one_le_jb y]) _
    have hεK : 0 ≤ K * ε := by have := hε.1; positivity
    have key : |iteratedDeriv j (L0 P.p f) y| ≤ K * ε * |y| ^ (-P.p - 2 - j) := by
      interval_cases j
      · simp only [iteratedDeriv_zero, heq, CharP.cast_eq_zero, sub_zero]
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hc, abs_of_pos (by linarith : (0:ℝ) < P.p + 1)]
        rw [show -P.p - 2 = -(P.p + 2) by ring]
        calc calpha P.p * (P.p + 1) * |∫ z in Ioi R, f z / (z - y) ^ (P.p + 2)|
            ≤ calpha P.p * (P.p + 1) * ((CL * ε) * |y| ^ (-(P.p + 2))) := by
              gcongr
              exact hΦ0.trans (mul_le_mul_of_nonneg_right hL1e (Real.rpow_nonneg (abs_nonneg _) _))
          _ ≤ K * ε * |y| ^ (-(P.p + 2)) := by
              rw [hK]
              have : 0 ≤ calpha P.p * (P.p + 1) * CL * ε * |y| ^ (-(P.p + 2)) := by
                have := hε.1; positivity
              nlinarith
      · simp only [iteratedDeriv_one, Nat.cast_one]
        have hev : L0 P.p f =ᶠ[𝓝 y] fun y' => -calpha P.p * (P.p + 1) *
            ∫ z in Ioi R, f z / (z - y') ^ (P.p + 2) := by
          filter_upwards [Iio_mem_nhds hy0] with y' hy'
          exact (hid y' hy').2
        rw [hev.deriv_eq, (hD.const_mul (-calpha P.p * (P.p + 1))).deriv]
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos hc, abs_of_pos (by linarith : (0:ℝ) < P.p + 1)]
        rw [show -P.p - 2 - 1 = -(P.p + 3) by ring]
        calc calpha P.p * (P.p + 1) * |D|
            ≤ calpha P.p * (P.p + 1) * ((P.p + 2) * (CL * ε) * |y| ^ (-(P.p + 3))) := by
              gcongr
              refine hDb.trans ?_
              gcongr
          _ = K * ε * |y| ^ (-(P.p + 3)) := by rw [hK]; ring
    calc |iteratedDeriv j (L0 P.p f) y| ≤ K * ε * |y| ^ (-P.p - 2 - j) := key
      _ ≤ K * ε * (16 * jb y ^ (-P.p - 2 - j)) := mul_le_mul_of_nonneg_left hjb hεK
      _ ≤ (16 * K + 1) * ε * jb y ^ (-P.p - 2 - j) := by
          have : 0 ≤ ε * jb y ^ (-P.p - 2 - j) := by have := hε.1; positivity
          nlinarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  have hεC : 0 ≤ (16 * K + 1) * ε := by have := hε.1; positivity
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (c07_aux_one_le_jb y)
    (by linarith)) hεC


/-- Core of lem:c07_negative_Q_split for a general `f ∈ C²` with `|f'| ≤ K`, `|f''| ≤ K` on
`(-∞,0]`. -/
theorem c07_aux_Q_split_core (P : parameters) (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (K : ℝ) (hK : ∀ z, |deriv f z| ≤ K)
    (hK2 : ∀ z ≤ 0, |iteratedDeriv 2 f z| ≤ K) (y : ℝ) (hy : y < 0) :
    Integrable (fun z => c07_chi ((y - z) / |y|) *
      ((deriv f y - deriv f z) / |y - z| ^ (P.p + 1)) * (A_eps P.p ε (c01_secant f y z) - 1)) ∧
    Integrable (fun z => (1 - c07_chi ((y - z) / |y|)) *
      ((deriv (fun x => f x - corner x) y - deriv (fun x => f x - corner x) z) /
        |y - z| ^ (P.p + 1)) * (A_eps P.p ε (c01_secant f y z) - 1)) ∧
    IntegrableOn (fun z => (A_eps P.p ε (c01_secant f y z) - A_eps P.p ε (c01_secant corner y z)) /
      (z - y) ^ (P.p + 1)) (Ioi 0) ∧
    c01_Q_eps P.p ε f y - c01_Q_eps P.p ε corner y =
      calpha P.p * (∫ z, c07_chi ((y - z) / |y|) *
        ((deriv f y - deriv f z) / |y - z| ^ (P.p + 1)) * (A_eps P.p ε (c01_secant f y z) - 1)) +
      calpha P.p * (∫ z, (1 - c07_chi ((y - z) / |y|)) *
        ((deriv (fun x => f x - corner x) y - deriv (fun x => f x - corner x) z) /
          |y - z| ^ (P.p + 1)) * (A_eps P.p ε (c01_secant f y z) - 1)) +
      -calpha P.p * ∫ z in Ioi (0 : ℝ),
        (A_eps P.p ε (c01_secant f y z) - A_eps P.p ε (c01_secant corner y z)) /
          (z - y) ^ (P.p + 1) := by
  set p := P.p with hpdef
  have hp : 0 < p := by linarith [P.hp_lo]
  have hp1 : p < 1 := P.hp_hi
  obtain ⟨hχ01, hχ0, -, hχc⟩ := c07_aux_chi_props
  have hY : 0 < |y| := abs_pos.2 hy.ne
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv f) := (hf.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hd1d : Differentiable ℝ (deriv f) := hd1.differentiable one_ne_zero
  have hdd : deriv (deriv f) = iteratedDeriv 2 f := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hAm := fun u => c07_aux_A_mem p ε u hp hε.1
  have hAc : Continuous (A_eps p ε) := c04_aux_A_cont p ε hε.1
  -- measurability
  have hmf : Measurable (deriv f) := measurable_deriv f
  have hmW : Measurable (deriv corner) := measurable_deriv corner
  have hmg : Measurable (deriv (fun x => f x - corner x)) := measurable_deriv _
  have hmSf : Measurable (fun z => c01_secant f y z) := c07_aux_secant_meas f hfd.continuous y
  have hmSW : Measurable (fun z => c01_secant corner y z) :=
    c07_aux_secant_meas corner (by unfold corner; fun_prop) y
  have hmA : Measurable (A_eps p ε) := hAc.measurable
  have hmχ : Measurable c07_chi := hχc.measurable
  -- majorants
  obtain ⟨hn1, -⟩ := c07_aux_near_int (|y| / 2) p (by positivity) hp hp1
  obtain ⟨hfar, -⟩ := c07_aux_far_int (|y| / 4) (p + 1) y (by positivity) (by linarith)
  set M1 : ℝ → ℝ := fun z => K * {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) (y - z)
    with hM1
  set M2 : ℝ → ℝ := fun z => (2 * K + 2) *
    {z : ℝ | |y| / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + 1))) z with hM2
  have hM1i : Integrable M1 := (hn1.comp_sub_left y).const_mul K
  have hM2i : Integrable M2 := hfar.const_mul _
  have hrp : ∀ z, z ≠ y → ∀ x : ℝ, x / |y - z| ^ (p + 1) = x * |y - z| ^ (-(p + 1)) := by
    intro z _ x; rw [Real.rpow_neg (abs_nonneg _), div_eq_mul_inv]
  -- (I1) integrability
  set F1 : ℝ → ℝ := fun z => c07_chi ((y - z) / |y|) *
      ((deriv f y - deriv f z) / |y - z| ^ (p + 1)) * (A_eps p ε (c01_secant f y z) - 1) with hF1
  have hF1m : Measurable F1 := by simp only [hF1]; fun_prop
  have hF1b : ∀ z, ‖F1 z‖ ≤ M1 z := by
    intro z
    have hind : 0 ≤ {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) (y - z) :=
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
    rcases eq_or_ne z y with rfl | hzy
    · simp only [hF1, M1, sub_self, zero_div, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg hK0 (indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _)
    by_cases hz : |y - z| ≤ |y| / 2
    · have hyz0 : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 hzy.symm)
      simp only [hM1]
      rw [indicator_of_mem (show y - z ∈ {s : ℝ | |s| ≤ |y| / 2} from hz)]
      -- mean value on `(-∞,0]`
      have hzneg : z ≤ 0 := by
        have := neg_abs_le (y - z); rw [abs_of_neg hy] at hz; linarith
      have hmv : |deriv f y - deriv f z| ≤ K * |y - z| := by
        have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f) (C := K) (s := Iic 0)
          (fun x _ => hd1d x) (fun x hx => by rw [hdd, Real.norm_eq_abs]; exact hK2 x hx)
          (convex_Iic 0) (show z ∈ Iic (0:ℝ) from hzneg) (show y ∈ Iic (0:ℝ) from hy.le)
        simpa [Real.norm_eq_abs] using this
      simp only [hF1, Real.norm_eq_abs]
      rw [hrp z hzy, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      have h1 : |c07_chi ((y - z) / |y|)| ≤ 1 := by
        rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
      have h2 : |A_eps p ε (c01_secant f y z) - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [(hAm (c01_secant f y z)).1, (hAm (c01_secant f y z)).2]
      have h3 : |y - z| * |y - z| ^ (-(p + 1)) = |y - z| ^ (-p) := by
        have : |y - z| * |y - z| ^ (-(p + 1)) = |y - z| ^ ((1:ℝ) + -(p + 1)) := by
          rw [Real.rpow_add hyz0, Real.rpow_one]
        rw [this]; ring_nf
      have h4 : |deriv f y - deriv f z| * |y - z| ^ (-(p + 1)) ≤ K * |y - z| ^ (-p) := by
        rw [← h3, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hmv (Real.rpow_nonneg (abs_nonneg _) _)
      have h5 : 0 ≤ |deriv f y - deriv f z| * |y - z| ^ (-(p + 1)) := by positivity
      calc |c07_chi ((y - z) / |y|)| * (|deriv f y - deriv f z| * |y - z| ^ (-(p + 1))) *
            |A_eps p ε (c01_secant f y z) - 1|
          ≤ 1 * (K * |y - z| ^ (-p)) * 1 := by gcongr
        _ = _ := by ring
    · have hχz : c07_chi ((y - z) / |y|) = 0 := by
        apply hχ0
        rw [abs_div, abs_abs, le_div_iff₀ hY]; push_neg at hz; linarith
      simp only [hF1, hχz, zero_mul, norm_zero]
      exact mul_nonneg hK0 hind
  have hF1i : Integrable F1 := hM1i.mono' hF1m.aestronglyMeasurable (Eventually.of_forall hF1b)
  -- (I2) integrability
  set F2 : ℝ → ℝ := fun z => (1 - c07_chi ((y - z) / |y|)) *
      ((deriv (fun x => f x - corner x) y - deriv (fun x => f x - corner x) z) /
        |y - z| ^ (p + 1)) * (A_eps p ε (c01_secant f y z) - 1) with hF2
  have hF2m : Measurable F2 := by simp only [hF2]; fun_prop
  have hgd : ∀ z, z ≠ 0 → |deriv (fun x => f x - corner x) z| ≤ K + 1 := by
    intro z hz
    rw [show deriv (fun x => f x - corner x) z = deriv f z - deriv corner z from
      deriv_sub (hfd z) (c07_aux_corner_diff z hz), c04_aux_deriv_corner z hz]
    have := hK z
    split_ifs <;> rw [abs_le] at this ⊢ <;> constructor <;> linarith [this.1, this.2]
  have hae0 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton _)
  have hF2b : ∀ᵐ z ∂(volume : Measure ℝ), ‖F2 z‖ ≤ M2 z := by
    filter_upwards [hae0] with z hz
    have hind : 0 ≤ {z : ℝ | |y| / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + 1))) z :=
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
    by_cases hz4 : |y| / 4 ≤ |y - z|
    · have hyz0 : 0 < |y - z| := lt_of_lt_of_le (by positivity) hz4
      have hzy : z ≠ y := fun h => by rw [h, sub_self, abs_zero] at hyz0; exact lt_irrefl _ hyz0
      simp only [hM2]
      rw [indicator_of_mem (show z ∈ {z : ℝ | |y| / 4 ≤ |y - z|} from hz4)]
      simp only [hF2, Real.norm_eq_abs]
      rw [hrp z hzy, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      have h1 : |1 - c07_chi ((y - z) / |y|)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hχ01 ((y - z) / |y|)]
      have h2 : |A_eps p ε (c01_secant f y z) - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [(hAm (c01_secant f y z)).1, (hAm (c01_secant f y z)).2]
      have h3 : |deriv (fun x => f x - corner x) y - deriv (fun x => f x - corner x) z| ≤
          2 * K + 2 := by
        have := abs_sub (deriv (fun x => f x - corner x) y) (deriv (fun x => f x - corner x) z)
        linarith [hgd y hy.ne, hgd z hz]
      calc |1 - c07_chi ((y - z) / |y|)| *
            (|deriv (fun x => f x - corner x) y - deriv (fun x => f x - corner x) z| *
              |y - z| ^ (-(p + 1))) * |A_eps p ε (c01_secant f y z) - 1|
          ≤ 1 * ((2 * K + 2) * |y - z| ^ (-(p + 1))) * 1 := by gcongr
        _ = _ := by ring
    · have hχz : c07_chi ((y - z) / |y|) = 1 := by
        apply (c07_aux_chi_props).2.2.1
        rw [abs_div, abs_abs, div_le_iff₀ hY]; push_neg at hz4; linarith
      simp only [hF2, hχz, sub_self, zero_mul, norm_zero]
      exact mul_nonneg (by linarith) hind
  have hF2i : Integrable F2 := hM2i.mono' hF2m.aestronglyMeasurable hF2b
  -- (I3) integrability
  set F3 : ℝ → ℝ := fun z => (A_eps p ε (c01_secant f y z) - A_eps p ε (c01_secant corner y z)) /
      (z - y) ^ (p + 1) with hF3
  have hF3m : Measurable F3 := by simp only [hF3]; fun_prop
  have hF3b : ∀ z ∈ Ioi (0 : ℝ), ‖F3 z‖ ≤
      {z : ℝ | |y| / 4 ≤ |y - z|}.indicator (fun z => |y - z| ^ (-(p + 1))) z := by
    intro z hz
    have hz0 : 0 < z := hz
    have hyz : |y - z| = z - y := by rw [abs_sub_comm, abs_of_pos (by linarith)]
    have hz4 : |y| / 4 ≤ |y - z| := by rw [hyz, abs_of_neg hy]; linarith
    rw [indicator_of_mem (show z ∈ {z : ℝ | |y| / 4 ≤ |y - z|} from hz4), hyz]
    simp only [hF3, Real.norm_eq_abs]
    rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), div_eq_mul_inv,
      ← Real.rpow_neg (by linarith)]
    have h2 : |A_eps p ε (c01_secant f y z) - A_eps p ε (c01_secant corner y z)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(hAm (c01_secant f y z)).1, (hAm (c01_secant f y z)).2,
        (hAm (c01_secant corner y z)).1, (hAm (c01_secant corner y z)).2]
    calc _ ≤ 1 * (z - y) ^ (-(p + 1)) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _)
      _ = _ := one_mul _
  have hF3i : IntegrableOn F3 (Ioi 0) :=
    hfar.integrableOn.mono' hF3m.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hF3b))
  refine ⟨hF1i, hF2i, hF3i, ?_⟩
  -- the identity
  obtain ⟨hGi, -, -⟩ := c07_QW_negative P ε hε y hy
  set F : ℝ → ℝ := fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant f y z) - 1) with hF
  set G : ℝ → ℝ := fun z => (deriv corner y - deriv corner z) / |y - z| ^ (p + 1) *
      (A_eps p ε (c01_secant corner y z) - 1) with hG
  have hF3i' : Integrable ((Ioi (0 : ℝ)).indicator (fun z => -F3 z)) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hF3i.neg
  have hfin : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 ∧ z ≠ y := by
    have h2 : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ y := compl_mem_ae_iff.mpr (measure_singleton _)
    filter_upwards [hae0, h2] with z h1 h2 using ⟨h1, h2⟩
  have hae : F =ᵐ[volume] fun z => G z + F1 z + F2 z + (Ioi (0 : ℝ)).indicator (fun z => -F3 z) z := by
    filter_upwards [hfin] with z ⟨hz0, hzy⟩
    have hgy : deriv (fun x => f x - corner x) y = deriv f y - deriv corner y :=
      deriv_sub (hfd y) (c07_aux_corner_diff y hy.ne)
    have hgz : deriv (fun x => f x - corner x) z = deriv f z - deriv corner z :=
      deriv_sub (hfd z) (c07_aux_corner_diff z hz0)
    simp only [hF, hG, hF1, hF2, hF3]
    rw [hgy, hgz, c04_aux_deriv_corner y hy.ne, c04_aux_deriv_corner z hz0]
    simp only [hy, ite_true]
    rcases lt_or_gt_of_ne hz0 with hz | hz
    · simp only [hz, ite_true]
      rw [indicator_of_notMem (show z ∉ Ioi (0:ℝ) by simp; linarith)]
      ring
    · simp only [show ¬ z < 0 by linarith, ite_false]
      rw [indicator_of_mem (show z ∈ Ioi (0:ℝ) from hz)]
      have hχz : c07_chi ((y - z) / |y|) = 0 := by
        have hyz : |y - z| = z - y := by rw [abs_sub_comm, abs_of_pos (by linarith)]
        apply hχ0
        rw [abs_div, abs_abs, le_div_iff₀ hY, hyz, abs_of_neg hy]
        linarith
      have hyz : |y - z| = z - y := by rw [abs_sub_comm, abs_of_pos (by linarith)]
      rw [hχz, hyz]
      ring
  have hFi : Integrable F := by
    rw [integrable_congr hae]
    exact ((hGi.add hF1i).add hF2i).add hF3i'
  unfold c01_Q_eps
  rw [integral_congr_ae hae, integral_add (f := fun z => G z + F1 z + F2 z)
    ((hGi.add hF1i).add hF2i) hF3i',
    integral_add (f := fun z => G z + F1 z) (hGi.add hF1i) hF2i, integral_add hGi hF1i,
    integral_indicator measurableSet_Ioi, integral_neg]
  rw [show (∫ z, (deriv corner y - deriv corner z) / |y - z| ^ (p + 1) *
    (A_eps p ε (c01_secant corner y z) - 1)) = ∫ z, G z from rfl]
  ring

/-- Blueprint: lem:c07_negative_Q_split.  The near term
`𝓘₁(y) = c_α ∫ χ_y(z) (f'(y)-f'(z))/|y-z|^α [A_ε(S_f(y,z)) - 1] dz`,
`χ_y(z) = χ((y-z)/|y|)`, `f = f̄_{ε,μ}`. -/
def c07_negative_Q_split_I1 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, c07_chi ((y - z) / |y|) *
    ((deriv (approximate_solution_family p R ε μ) y -
        deriv (approximate_solution_family p R ε μ) z) / |y - z| ^ (p + 1)) *
    (A_eps p ε (c01_secant (approximate_solution_family p R ε μ) y z) - 1)

/-- Blueprint: lem:c07_negative_Q_split.  The far term
`𝓘₂(y) = c_α ∫ (1-χ_y(z)) (g'(y)-g'(z))/|y-z|^α [A_ε(S_f(y,z)) - 1] dz`, `g = f - W`. -/
def c07_negative_Q_split_I2 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, (1 - c07_chi ((y - z) / |y|)) *
    ((deriv (fun x => approximate_solution_family p R ε μ x - corner x) y -
        deriv (fun x => approximate_solution_family p R ε μ x - corner x) z) / |y - z| ^ (p + 1)) *
    (A_eps p ε (c01_secant (approximate_solution_family p R ε μ) y z) - 1)

/-- Blueprint: lem:c07_negative_Q_split.  The corner term
`𝓘₃(y) = -c_α ∫₀^∞ (A_ε(S_f(y,z)) - A_ε(S_W(y,z)))/(z-y)^α dz`. -/
def c07_negative_Q_split_I3 (p R ε : ℝ) (μ : ℂ) (y : ℝ) : ℝ :=
  -calpha p * ∫ z in Ioi (0 : ℝ),
    (A_eps p ε (c01_secant (approximate_solution_family p R ε μ) y z) -
      A_eps p ε (c01_secant corner y z)) / (z - y) ^ (p + 1)

/-- Blueprint: lem:c07_negative_Q_split.  For `y < 0`:
`𝒬_ε(f)(y) - 𝒬_ε(W)(y) = 𝓘₁(y) + 𝓘₂(y) + 𝓘₃(y)`, all absolutely convergent. -/
theorem c07_negative_Q_split (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y : ℝ, y < 0 →
        Integrable (fun z => c07_chi ((y - z) / |y|) *
          ((deriv (approximate_solution_family P.p R ε μ) y -
              deriv (approximate_solution_family P.p R ε μ) z) / |y - z| ^ (P.p + 1)) *
          (A_eps P.p ε (c01_secant (approximate_solution_family P.p R ε μ) y z) - 1)) ∧
        Integrable (fun z => (1 - c07_chi ((y - z) / |y|)) *
          ((deriv (fun x => approximate_solution_family P.p R ε μ x - corner x) y -
              deriv (fun x => approximate_solution_family P.p R ε μ x - corner x) z) /
            |y - z| ^ (P.p + 1)) *
          (A_eps P.p ε (c01_secant (approximate_solution_family P.p R ε μ) y z) - 1)) ∧
        IntegrableOn (fun z =>
          (A_eps P.p ε (c01_secant (approximate_solution_family P.p R ε μ) y z) -
            A_eps P.p ε (c01_secant corner y z)) / (z - y) ^ (P.p + 1)) (Ioi 0) ∧
        c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ) y - c01_Q_eps P.p ε corner y =
          c07_negative_Q_split_I1 P.p R ε μ y + c07_negative_Q_split_I2 P.p R ε μ y +
            c07_negative_Q_split_I3 P.p R ε μ y := by
  intro δ hδ hδ'
  obtain ⟨R1, e1, hR1, he1, he11, hS⟩ := c07_family_smooth P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  refine ⟨max R1 R2, min e1 e2, le_trans hR1 (le_max_left _ _), lt_min he1 he2,
    (min_le_left _ _).trans he11, fun R hR ε hε μ hμ y hy => ?_⟩
  have hεa : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεb : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans he11⟩
  obtain ⟨hf, -⟩ := hS R (le_trans (le_max_left _ _) hR) ε hεa μ hμ
  obtain ⟨K₀, -, hU'⟩ := hU R (le_trans (le_max_right _ _) hR)
  obtain ⟨⟨-, hcl⟩, -, -⟩ := hU' ε hεb μ hμ
  have hK2 : ∀ z ≤ 0, |iteratedDeriv 2 (approximate_solution_family P.p R ε μ) z| ≤ K₀ := by
    intro z hz
    have h := (hcl z).2.2.1 hz
    have h1 := c07_aux_jb_rpow_neg_le_one z 1 zero_le_one
    have hK : 0 ≤ K₀ := (abs_nonneg _).trans (hcl z).1
    calc _ ≤ K₀ * jb z ^ (-1 : ℝ) := h
      _ ≤ K₀ * 1 := mul_le_mul_of_nonneg_left h1 hK
      _ = K₀ := mul_one _
  obtain ⟨i1, i2, i3, hid⟩ := c07_aux_Q_split_core P ε hε1 _ (hf.of_le (by simp)) K₀
    (fun z => (hcl z).1) hK2 y hy
  refine ⟨i1, i2, i3, ?_⟩
  rw [hid]
  rfl


/-- `χ` is `C¹`, with bounded derivative vanishing for `|x| ≥ 1/2`. -/
theorem c07_aux_chi_C1 :
    ContDiff ℝ 1 c07_chi ∧ (∀ x, 1 / 2 ≤ |x| → deriv c07_chi x = 0) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv c07_chi x| ≤ M := by
  have hcd : ContDiff ℝ 1 c07_chi := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have hev : c07_chi =ᶠ[𝓝 0] fun _ => 1 := by
        have : Ioo (-(1/4 : ℝ)) (1/4) ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
        filter_upwards [this] with t ht
        exact (c07_aux_chi_props).2.2.1 t (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · unfold c07_chi
      exact Real.smoothTransition.contDiff.contDiffAt.comp x
        ((contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_abs hx))).div_const _)
  have hz : ∀ x, 1 / 2 ≤ |x| → deriv c07_chi x = 0 := by
    intro x hx
    have hev : c07_chi =ᶠ[𝓝 x] fun _ => 0 := by
      have hc : Continuous (fun t : ℝ => |t|) := continuous_abs
      have : {t : ℝ | 7 / 16 < |t|} ∈ 𝓝 x :=
        (isOpen_lt continuous_const hc).mem_nhds (show 7 / 16 < |x| by linarith)
      filter_upwards [this] with t ht
      exact (c07_aux_chi_props).2.1 t (le_of_lt ht)
    rw [hev.deriv_eq]; simp
  refine ⟨hcd, hz, ?_⟩
  have hc : Continuous (deriv c07_chi) := hcd.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : |x| ≤ 1
  · have := hM x (abs_le.1 hx); rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · rw [hz x (by linarith [not_le.1 hx])]; simp

/-- The integrand of `𝓘₁` in the variable `s = y - z`. -/
def c07_aux_I1_G (p ε : ℝ) (f : ℝ → ℝ) (y s : ℝ) : ℝ :=
  c07_chi (s / |y|) * ((deriv f y - deriv f (y - s)) / |s| ^ (p + 1)) *
    (A_eps p ε (c01_secant f y (y - s)) - 1)

/-- Its `y`-derivative (for `y < 0`, `s ≠ 0`). -/
def c07_aux_I1_dG (p ε : ℝ) (f : ℝ → ℝ) (y s : ℝ) : ℝ :=
  deriv c07_chi (s / |y|) * (s / y ^ 2) * ((deriv f y - deriv f (y - s)) / |s| ^ (p + 1)) *
      (A_eps p ε (c01_secant f y (y - s)) - 1) +
    c07_chi (s / |y|) * ((deriv (deriv f) y - deriv (deriv f) (y - s)) / |s| ^ (p + 1)) *
      (A_eps p ε (c01_secant f y (y - s)) - 1) +
    c07_chi (s / |y|) * ((deriv f y - deriv f (y - s)) / |s| ^ (p + 1)) *
      (deriv (A_eps p ε) (c01_secant f y (y - s)) * ((deriv f y - deriv f (y - s)) / s))

/-- Pointwise facts for the integrand of `𝓘₁` (`y < 0`, `s ≠ 0`, `|y| ≥ 2`). -/
theorem c07_aux_I1_pt (p ε K Mχ : ℝ) (hp : 0 < p) (hε : ε ∈ Icc (0 : ℝ) 1) (hK1 : 1 ≤ K)
    (hMχ : ∀ x, |deriv c07_chi x| ≤ Mχ)
    (hA1 : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2)
    (hA' : ∀ u, |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u|)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hK : ∀ z, |deriv f z| ≤ K)
    (h2 : ∀ t ≤ 0, |iteratedDeriv 2 f t| ≤ K * jb t ^ (-p - 2))
    (h3 : ∀ t ≤ 0, |iteratedDeriv 3 f t| ≤ K * jb t ^ (-p - 3))
    (y s : ℝ) (hy : y < 0) (hs : s ≠ 0) (hw : 1 ≤ |y| / 2) :
    HasDerivAt (fun t => c07_aux_I1_G p ε f t s) (c07_aux_I1_dG p ε f y s) y ∧
    |c07_aux_I1_G p ε f y s| ≤ ε * ((p + 1) / 2 * K ^ 3) * (|y| / 2) ^ (-p - 2) *
      {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) s ∧
    |c07_aux_I1_dG p ε f y s| ≤ ε * (K ^ 3 * (p + 1) * (Mχ / 8 + 3 / 2)) * (|y| / 2) ^ (-p - 3) *
      {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) s := by
  obtain ⟨hχC1, hχ0', -⟩ := c07_aux_chi_C1
  obtain ⟨hχ01, hχ0, -, -⟩ := c07_aux_chi_props
  have hε0 := hε.1
  have hK0 : 0 ≤ K := by linarith
  have hY : 0 < |y| := abs_pos.2 hy.ne
  set w := |y| / 2 with hwd
  have hw0 : 0 < w := by linarith
  have hsa : 0 < |s| := abs_pos.2 hs
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 2 (deriv f) := (hf.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hd1d : Differentiable ℝ (deriv f) := hd1.differentiable (by norm_num)
  have hd2 : ContDiff ℝ 1 (deriv (deriv f)) := (hd1.of_le (m := 1 + 1) (by norm_num)).deriv'
  have hd2d : Differentiable ℝ (deriv (deriv f)) := hd2.differentiable (by norm_num)
  have hdd2 : deriv (deriv f) = iteratedDeriv 2 f := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hdd3 : deriv (deriv (deriv f)) = iteratedDeriv 3 f := by
    rw [iteratedDeriv_succ, hdd2]
  set S := c01_secant f y (y - s) with hSd
  have hSK : |S| ≤ K := (c07_secant_calculus f (hf.of_le (by norm_num)) K hK).1 y (y - s)
    (by intro h; apply hs; linarith)
  refine ⟨?_, ?_⟩
  · -- derivative
    have hev : (fun t => c07_aux_I1_G p ε f t s) =ᶠ[𝓝 y] fun t =>
        c07_chi (s / (-t)) * ((deriv f t - deriv f (t - s)) / |s| ^ (p + 1)) *
          (A_eps p ε (c01_secant f t (t - s)) - 1) := by
      filter_upwards [Iio_mem_nhds hy] with t ht
      simp only [c07_aux_I1_G, abs_of_neg (mem_Iio.1 ht)]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    have hq : HasDerivAt (fun t : ℝ => s / (-t)) (s / y ^ 2) y := by
      have := (hasDerivAt_const y s).div ((hasDerivAt_id y).neg) (by simpa using hy.ne)
      convert this using 1
      · rfl
      · simp only [Pi.neg_apply, id]; rw [neg_sq]; ring
    have hχd : HasDerivAt c07_chi (deriv c07_chi (s / (-y))) (s / (-y)) :=
      (hχC1.differentiable one_ne_zero _).hasDerivAt
    have hc1 := hχd.comp y hq
    have hN : HasDerivAt (fun t => (deriv f t - deriv f (t - s)) / |s| ^ (p + 1))
        ((deriv (deriv f) y - deriv (deriv f) (y - s)) / |s| ^ (p + 1)) y := by
      have := ((hd1d y).hasDerivAt.sub ((hd1d (y - s)).hasDerivAt.comp y
        ((hasDerivAt_id y).sub_const s))).div_const (|s| ^ (p + 1))
      simpa using this
    have hSd' := (c07_secant_calculus f (hf.of_le (by norm_num)) K hK).2.2.2.2.2.1 y s hs
    have hA := ((c07_aux_A_hasDeriv p ε S hε0).differentiableAt.hasDerivAt.comp y hSd').sub_const 1
    have := (hc1.mul hN).mul hA
    convert this using 1
    · rfl
    · simp only [c07_aux_I1_dG, abs_of_neg hy, Function.comp_apply, hSd, Pi.mul_apply]
      ring
  -- bounds
  have hseg : ∀ t, |s| ≤ w → t ∈ uIcc (y - s) y → t ≤ 0 ∧ w ≤ |t| := by
    intro t hsw ht
    have hya : |y| = -y := abs_of_neg hy
    rw [abs_le] at hsw
    rcases le_total (y - s) y with h | h
    · rw [uIcc_of_le h] at ht
      have : t < 0 := by linarith [ht.2]
      refine ⟨this.le, ?_⟩; rw [abs_of_neg this]; rw [hwd, hya] at hsw ⊢; linarith [ht.1, ht.2]
    · rw [uIcc_of_ge h] at ht
      have : t < 0 := by rw [hwd, hya] at hsw; linarith [ht.2]
      refine ⟨this.le, ?_⟩; rw [abs_of_neg this]; rw [hwd, hya] at hsw ⊢; linarith [ht.1, ht.2]
  have hjbw : ∀ t r : ℝ, 0 ≤ r → w ≤ |t| → jb t ^ (-r) ≤ w ^ (-r) := fun t r hr ht =>
    Real.rpow_le_rpow_of_nonpos hw0 (ht.trans (c07_aux_abs_le_jb t)) (by linarith)
  -- mean value bounds on the segment
  have hmv : ∀ (g : ℝ → ℝ) (B : ℝ), Differentiable ℝ g →
      (∀ t ∈ uIcc (y - s) y, |deriv g t| ≤ B) → |g y - g (y - s)| ≤ B * |s| := by
    intro g B hg hb
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := uIcc (y - s) y) (f := g) (C := B)
      (fun x _ => hg x) (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx) (convex_uIcc (y - s) y)
      left_mem_uIcc right_mem_uIcc
    simpa [Real.norm_eq_abs] using this
  have hX : ∀ x : ℝ, x / |s| ^ (p + 1) = x * |s| ^ (-(p + 1)) := fun x => by
    rw [Real.rpow_neg hsa.le, div_eq_mul_inv]
  have hsp : |s| * |s| ^ (-(p + 1)) = |s| ^ (-p) := by
    have : |s| * |s| ^ (-(p + 1)) = |s| ^ ((1:ℝ) + -(p + 1)) := by
      rw [Real.rpow_add hsa, Real.rpow_one]
    rw [this]; ring_nf
  have hXn : 0 ≤ |s| ^ (-(p + 1)) := Real.rpow_nonneg hsa.le _
  have hAm1 : |A_eps p ε S - 1| ≤ (p + 1) / 2 * ε * K ^ 2 := by
    refine (hA1 S).trans ?_
    have : S ^ 2 ≤ K ^ 2 := by nlinarith [abs_nonneg S, sq_abs S]
    gcongr
  have hw2 : w ^ (-p - 2) * w⁻¹ = w ^ (-p - 3) := by
    rw [show -p - 3 = (-p - 2) - 1 by ring, Real.rpow_sub_one hw0.ne', div_eq_mul_inv]
  have hw4 : w ^ (-p - 2) * w ^ (-p - 2) ≤ w ^ (-p - 3) := by
    rw [← Real.rpow_add hw0]
    exact Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  by_cases hsw : |s| ≤ w
  swap
  · -- outside the support everything vanishes
    have hx : 1 / 2 ≤ |(s / |y|)| := by
      rw [abs_div, abs_abs, le_div_iff₀ hY]; push_neg at hsw; linarith
    have hc0 : c07_chi (s / |y|) = 0 := hχ0 _ (by linarith)
    have hd0 : deriv c07_chi (s / |y|) = 0 := hχ0' _ hx
    rw [indicator_of_notMem (show s ∉ {s : ℝ | |s| ≤ |y| / 2} from hsw)]
    simp [c07_aux_I1_G, c07_aux_I1_dG, hc0, hd0]
  rw [indicator_of_mem (show s ∈ {s : ℝ | |s| ≤ |y| / 2} from hsw)]
  have hN1 : |deriv f y - deriv f (y - s)| ≤ K * w ^ (-p - 2) * |s| := by
    refine hmv (deriv f) _ hd1d fun t ht => ?_
    obtain ⟨t0, tw⟩ := hseg t hsw ht
    rw [hdd2]
    exact (h2 t t0).trans (mul_le_mul_of_nonneg_left
      (by have := hjbw t (p + 2) (by linarith) tw; rwa [show -(p + 2) = -p - 2 by ring] at this) hK0)
  have hN2 : |deriv (deriv f) y - deriv (deriv f) (y - s)| ≤ K * w ^ (-p - 3) * |s| := by
    refine hmv (deriv (deriv f)) _ hd2d fun t ht => ?_
    obtain ⟨t0, tw⟩ := hseg t hsw ht
    rw [hdd3]
    exact (h3 t t0).trans (mul_le_mul_of_nonneg_left
      (by have := hjbw t (p + 3) (by linarith) tw; rwa [show -(p + 3) = -p - 3 by ring] at this) hK0)
  have hwn2 : 0 ≤ w ^ (-p - 2) := Real.rpow_nonneg hw0.le _
  have hwn3 : 0 ≤ w ^ (-p - 3) := Real.rpow_nonneg hw0.le _
  have hc1 : |c07_chi (s / |y|)| ≤ 1 := by rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
  have hspn : 0 ≤ |s| ^ (-p) := Real.rpow_nonneg hsa.le _
  -- `|N| X ≤ K w^{-p-2} |s|^{-p}`
  have hNX : |deriv f y - deriv f (y - s)| * |s| ^ (-(p + 1)) ≤ K * w ^ (-p - 2) * |s| ^ (-p) := by
    rw [← hsp]
    calc _ ≤ K * w ^ (-p - 2) * |s| * |s| ^ (-(p + 1)) := mul_le_mul_of_nonneg_right hN1 hXn
      _ = _ := by ring
  have hpe : 0 ≤ (p + 1) / 2 * ε * K ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [c07_aux_I1_G]
    rw [hX, abs_mul, abs_mul, abs_mul, abs_of_nonneg hXn]
    calc |c07_chi (s / |y|)| * (|deriv f y - deriv f (y - s)| * |s| ^ (-(p + 1))) *
          |A_eps p ε S - 1| ≤ 1 * (K * w ^ (-p - 2) * |s| ^ (-p)) * ((p + 1) / 2 * ε * K ^ 2) := by
          gcongr
      _ = _ := by ring
  · simp only [c07_aux_I1_dG]
    rw [hX, hX]
    refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl) |>.trans ?_
    simp only [abs_mul, abs_div, abs_of_nonneg hXn]
    have hyy : |y| ^ 2 = 4 * w ^ 2 := by rw [hwd]; ring
    have hsy : |s| / |y ^ 2| ≤ w⁻¹ / 4 := by
      rw [abs_pow, hyy, div_le_iff₀ (by positivity)]
      have : w⁻¹ / 4 * (4 * w ^ 2) = w := by field_simp
      rw [this]; exact hsw
    have hS' : |deriv (A_eps p ε) S| ≤ (p + 1) * ε * K :=
      (hA' S).trans (mul_le_mul_of_nonneg_left hSK (by positivity))
    have hNs : |deriv f y - deriv f (y - s)| / |s| ≤ K * w ^ (-p - 2) := by
      rw [div_le_iff₀ hsa]; exact hN1
    have hN2X : |deriv (deriv f) y - deriv (deriv f) (y - s)| * |s| ^ (-(p + 1)) ≤
        K * w ^ (-p - 3) * |s| ^ (-p) := by
      rw [← hsp]
      calc _ ≤ K * w ^ (-p - 3) * |s| * |s| ^ (-(p + 1)) := mul_le_mul_of_nonneg_right hN2 hXn
        _ = _ := by ring
    have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
    calc _ ≤ Mχ * (w⁻¹ / 4) * (K * w ^ (-p - 2) * |s| ^ (-p)) * ((p + 1) / 2 * ε * K ^ 2) +
          1 * (K * w ^ (-p - 3) * |s| ^ (-p)) * ((p + 1) / 2 * ε * K ^ 2) +
          1 * (K * w ^ (-p - 2) * |s| ^ (-p)) * ((p + 1) * ε * K * (K * w ^ (-p - 2))) := by
          gcongr
          all_goals first | exact hMχ _ | (rw [← abs_div]; exact hNs)
      _ = ε * (K ^ 3 * (p + 1)) * |s| ^ (-p) * (Mχ / 8 * (w ^ (-p - 2) * w⁻¹) +
            1 / 2 * w ^ (-p - 3) + w ^ (-p - 2) * w ^ (-p - 2)) := by ring
      _ ≤ ε * (K ^ 3 * (p + 1)) * |s| ^ (-p) * (Mχ / 8 * w ^ (-p - 3) +
            1 / 2 * w ^ (-p - 3) + w ^ (-p - 3)) := by
          rw [hw2]; gcongr
      _ = _ := by ring

/-- Core of lem:c07_negative_I1 for a general profile `f` (`y ≤ -8`). -/
theorem c07_aux_I1_core (p ε K Mχ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hK1 : 1 ≤ K) (hMχ : ∀ x, |deriv c07_chi x| ≤ Mχ)
    (hA1 : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2)
    (hA' : ∀ u, |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u|)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hK : ∀ z, |deriv f z| ≤ K)
    (h2 : ∀ t ≤ 0, |iteratedDeriv 2 f t| ≤ K * jb t ^ (-p - 2))
    (h3 : ∀ t ≤ 0, |iteratedDeriv 3 f t| ≤ K * jb t ^ (-p - 3)) (y : ℝ) (hy : y ≤ -8) :
    let I := fun y' => calpha p * ∫ z, c07_chi ((y' - z) / |y'|) *
      ((deriv f y' - deriv f z) / |y' - z| ^ (p + 1)) * (A_eps p ε (c01_secant f y' z) - 1)
    DifferentiableAt ℝ I y ∧
    |I y| ≤ calpha p * ((p + 1) / 2 * K ^ 3) * (2 / (1 - p)) * 2 ^ (2 * p + 1) * ε *
      |y| ^ (-2 * p - 1) ∧
    |deriv I y| ≤ calpha p * (K ^ 3 * (p + 1) * (Mχ / 8 + 3 / 2)) * (2 / (1 - p)) *
      2 ^ (2 * p + 2) * ε * |y| ^ (-2 * p - 2) := by
  intro I
  have hc := c03_aux_calpha_pos p hp hp1
  have hε0 := hε.1
  have hy0 : y < 0 := by linarith
  have hY : 8 ≤ |y| := by rw [abs_of_neg hy0]; linarith
  have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
  set M0 := (p + 1) / 2 * K ^ 3 with hM0
  set M1 := K ^ 3 * (p + 1) * (Mχ / 8 + 3 / 2) with hM1
  have hM00 : 0 ≤ M0 := by positivity
  have hM10 : 0 ≤ M1 := by positivity
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfc : Continuous f := hfd.continuous
  have hAc : Continuous (A_eps p ε) := c04_aux_A_cont p ε hε0
  have hχc := (c07_aux_chi_props).2.2.2
  -- change of variables
  have hcv : ∀ y', I y' = calpha p * ∫ s, c07_aux_I1_G p ε f y' s := by
    intro y'
    simp only [I]
    congr 1
    have := integral_sub_left_eq_self (fun z => c07_chi ((y' - z) / |y'|) *
      ((deriv f y' - deriv f z) / |y' - z| ^ (p + 1)) * (A_eps p ε (c01_secant f y' z) - 1))
      volume y'
    rw [← this]
    simp only [sub_sub_cancel, c07_aux_I1_G]
  have hmG : ∀ y', Measurable (c07_aux_I1_G p ε f y') := fun y' => by
    have h1 : Measurable (fun s => c01_secant f y' (y' - s)) :=
      (c07_aux_secant_meas f hfc y').comp (by fun_prop)
    have := measurable_deriv f; have := hAc.measurable; have := hχc.measurable
    unfold c07_aux_I1_G; fun_prop
  have hmdG : ∀ y', Measurable (c07_aux_I1_dG p ε f y') := fun y' => by
    have h1 : Measurable (fun s => c01_secant f y' (y' - s)) :=
      (c07_aux_secant_meas f hfc y').comp (by fun_prop)
    have := measurable_deriv f; have := hAc.measurable; have := hχc.measurable
    have : Measurable (deriv c07_chi) := measurable_deriv _
    have : Measurable (deriv (deriv f)) := measurable_deriv _
    have : Measurable (deriv (A_eps p ε)) := measurable_deriv _
    unfold c07_aux_I1_dG; fun_prop
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton _)
  have hpt := fun y' (hy' : y' < 0) s (hs : s ≠ 0) (hw : 1 ≤ |y'| / 2) =>
    c07_aux_I1_pt p ε K Mχ hp hε hK1 hMχ hA1 hA' f hf hK h2 h3 y' s hy' hs hw
  -- domination on `ball y (|y|/4)`
  set b := 3 * |y| / 8 with hb
  have hb1 : 1 ≤ b := by rw [hb]; linarith
  have hb0 : 0 < b := by linarith
  have hball : ∀ y' ∈ Metric.ball y (|y| / 4), y' < 0 ∧ b ≤ |y'| / 2 ∧ |y'| / 2 ≤ 5 * |y| / 8 := by
    intro y' hy'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy'
    have hya : |y| = -y := abs_of_neg hy0
    rw [hya] at hy'
    have : y' < 0 := by linarith
    refine ⟨this, ?_, ?_⟩
    · rw [abs_of_neg this, hb, hya]; linarith
    · rw [abs_of_neg this, hya]; linarith
  obtain ⟨hni, -⟩ := c07_aux_near_int (5 * |y| / 8) p (by positivity) hp hp1
  set bound : ℝ → ℝ := fun s => ε * M1 * b ^ (-p - 3) *
    {s : ℝ | |s| ≤ 5 * |y| / 8}.indicator (fun s => |s| ^ (-p)) s with hbound
  have hbi : Integrable bound := hni.const_mul _
  have hdb : ∀ s, s ≠ 0 → ∀ y' ∈ Metric.ball y (|y| / 4), ‖c07_aux_I1_dG p ε f y' s‖ ≤ bound s := by
    intro s hs y' hy'
    obtain ⟨hy'0, hb', hb''⟩ := hball y' hy'
    have k := (hpt y' hy'0 s hs (hb1.trans hb')).2.2
    rw [Real.norm_eq_abs]; refine k.trans ?_
    simp only [hbound]
    have e1 : (|y'| / 2) ^ (-p - 3) ≤ b ^ (-p - 3) :=
      Real.rpow_le_rpow_of_nonpos hb0 hb' (by linarith)
    have e2 : {s : ℝ | |s| ≤ |y'| / 2}.indicator (fun s => |s| ^ (-p)) s ≤
        {s : ℝ | |s| ≤ 5 * |y| / 8}.indicator (fun s => |s| ^ (-p)) s :=
      indicator_le_indicator_of_subset (fun s (hs : s ∈ {s : ℝ | |s| ≤ |y'| / 2}) =>
        show |s| ≤ 5 * |y| / 8 from le_trans hs hb'')
        (fun _ => Real.rpow_nonneg (abs_nonneg _) _) s
    have n1 : 0 ≤ {s : ℝ | |s| ≤ |y'| / 2}.indicator (fun s => |s| ^ (-p)) s :=
      indicator_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
    have n2 : 0 ≤ (|y'| / 2) ^ (-p - 3) := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ ε * M1 := by positivity
    calc ε * M1 * (|y'| / 2) ^ (-p - 3) * {s : ℝ | |s| ≤ |y'| / 2}.indicator (fun s => |s| ^ (-p)) s
        ≤ ε * M1 * b ^ (-p - 3) * {s : ℝ | |s| ≤ 5 * |y| / 8}.indicator (fun s => |s| ^ (-p)) s := by
          gcongr
      _ = _ := rfl
  -- integrability of `G y`
  have hw : 1 ≤ |y| / 2 := by linarith
  obtain ⟨hni2, hnv2⟩ := c07_aux_near_int (|y| / 2) p (by positivity) hp hp1
  have hGb : ∀ s, s ≠ 0 → ‖c07_aux_I1_G p ε f y s‖ ≤ ε * M0 * (|y| / 2) ^ (-p - 2) *
      {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) s := fun s hs => by
    rw [Real.norm_eq_abs]; exact (hpt y hy0 s hs hw).2.1
  have hGi : Integrable (c07_aux_I1_G p ε f y) :=
    (hni2.const_mul _).mono' (hmG y).aestronglyMeasurable (hae.mono fun s hs => hGb s hs)
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := c07_aux_I1_G p ε f) (F' := c07_aux_I1_dG p ε f) (x₀ := y) (bound := bound)
    (Metric.ball_mem_nhds y (by positivity))
    (Eventually.of_forall fun y' => (hmG y').aestronglyMeasurable) hGi
    (hmdG y).aestronglyMeasurable (hae.mono fun s hs y' hy' => hdb s hs y' hy') hbi
    (hae.mono fun s hs y' hy' =>
      (hpt y' (hball y' hy').1 s hs (hb1.trans (hball y' hy').2.1)).1)
  have hDI : HasDerivAt I (calpha p * ∫ s, c07_aux_I1_dG p ε f y s) y := by
    rw [show I = fun y' => calpha p * ∫ s, c07_aux_I1_G p ε f y' s from funext hcv]
    exact hD.const_mul _
  -- the integral of the majorant
  set w := |y| / 2 with hwd
  have hw0 : 0 < w := by linarith
  have hwpow : ∀ r : ℝ, w ^ (-r) = 2 ^ r * |y| ^ (-r) := fun r => by
    rw [hwd, (c07_aux_rpow_div |y| 2 (-r) (abs_nonneg _) two_pos).1, neg_neg]
  have hint : ∀ r : ℝ, w ^ (-r) * (2 * (w ^ (1 - p) / (1 - p))) =
      2 / (1 - p) * w ^ (-(r + p - 1)) := fun r => by
    rw [show -(r + p - 1) = -r + (1 - p) by ring, Real.rpow_add hw0]; ring
  refine ⟨hDI.differentiableAt, ?_, ?_⟩
  · rw [hcv, abs_mul, abs_of_pos hc]
    have hb1' : |∫ s, c07_aux_I1_G p ε f y s| ≤ ∫ s, ε * M0 * w ^ (-p - 2) *
        {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) s := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le (hni2.const_mul _) (hae.mono fun s hs => hGb s hs)
    rw [integral_const_mul, hnv2, show -p - 2 = -(p + 2) by ring, mul_assoc, hint,
      show -(p + 2 + p - 1) = -(2 * p + 1) by ring, hwpow,
      show -(2 * p + 1) = -2 * p - 1 by ring] at hb1'
    calc calpha p * |∫ s, c07_aux_I1_G p ε f y s| ≤
        calpha p * (ε * M0 * (2 / (1 - p) * (2 ^ (2 * p + 1) * |y| ^ (-2 * p - 1)))) :=
          mul_le_mul_of_nonneg_left hb1' hc.le
      _ = _ := by ring
  · rw [hDI.deriv, abs_mul, abs_of_pos hc]
    have hb2 : ∀ s, s ≠ 0 → ‖c07_aux_I1_dG p ε f y s‖ ≤ ε * M1 * w ^ (-p - 3) *
        {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) s := fun s hs => by
      rw [Real.norm_eq_abs]; exact (hpt y hy0 s hs hw).2.2
    have hb1' : |∫ s, c07_aux_I1_dG p ε f y s| ≤ ∫ s, ε * M1 * w ^ (-p - 3) *
        {s : ℝ | |s| ≤ |y| / 2}.indicator (fun s => |s| ^ (-p)) s := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le (hni2.const_mul _) (hae.mono fun s hs => hb2 s hs)
    rw [integral_const_mul, hnv2, show -p - 3 = -(p + 3) by ring, mul_assoc, hint,
      show -(p + 3 + p - 1) = -(2 * p + 2) by ring, hwpow,
      show -(2 * p + 2) = -2 * p - 2 by ring] at hb1'
    calc calpha p * |∫ s, c07_aux_I1_dG p ε f y s| ≤
        calpha p * (ε * M1 * (2 / (1 - p) * (2 ^ (2 * p + 2) * |y| ^ (-2 * p - 2)))) :=
          mul_le_mul_of_nonneg_left hb1' hc.le
      _ = _ := by ring

/-- Blueprint: lem:c07_negative_I1.  `|∂^j 𝓘₁(y)| ≤ Cε|y|^{-2p-1-j}` for `y ≤ -8R`,
`j ∈ {0,1}`. -/
-- The conclusion includes `DifferentiableAt ℝ 𝓘ₖ y` (`y ≤ -8R`), so that the bound on
-- `iteratedDeriv 1` is a bound on the classical derivative; the bounds are summed in
-- prop:approx_residual_negative.
theorem c07_negative_I1 (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y ≤ -8 * R,
      DifferentiableAt ℝ (c07_negative_Q_split_I1 P.p R ε μ) y ∧ ∀ j ≤ 1,
      |iteratedDeriv j (c07_negative_Q_split_I1 P.p R ε μ) y| ≤
        C * ε * |y| ^ (-2 * P.p - 1 - j) := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  obtain ⟨R1, e1, hR1, he1, he11, hS⟩ := c07_family_smooth P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  obtain ⟨CB, hCB, hAB⟩ := c07_A_B_bounds P.p hp hp1
  obtain ⟨-, -, Mχ, hMχ0, hMχ⟩ := c07_aux_chi_C1
  refine ⟨max R1 R2, min e1 e2, le_trans hR1 (le_max_left _ _), lt_min he1 he2,
    (min_le_left _ _).trans he11, fun R hR => ?_⟩
  obtain ⟨K₀, hK₀, hU'⟩ := hU R (le_trans (le_max_right _ _) hR)
  have hR1' : 1 ≤ R := le_trans hR1 (le_trans (le_max_left _ _) hR)
  have hc := c03_aux_calpha_pos P.p hp hp1
  set C1 := calpha P.p * ((P.p + 1) / 2 * K₀ ^ 3) * (2 / (1 - P.p)) * 2 ^ (2 * P.p + 1) with hC1
  set C2 := calpha P.p * (K₀ ^ 3 * (P.p + 1) * (Mχ / 8 + 3 / 2)) * (2 / (1 - P.p)) *
    2 ^ (2 * P.p + 2) with hC2
  have h1p : 0 < 1 - P.p := by linarith
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨C1 + C2 + 1, by positivity, fun ε hε μ hμ y hy => ?_⟩
  have hεa : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεb : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans he11⟩
  obtain ⟨hf, -⟩ := hS R (le_trans (le_max_left _ _) hR) ε hεa μ hμ
  obtain ⟨⟨-, hcl⟩, -, hg3⟩ := hU' ε hεb μ hμ
  set f := approximate_solution_family P.p R ε μ with hfdef
  obtain ⟨-, hdk⟩ := c07_aux_iteratedDeriv_add_id f hf
  have h2 : ∀ t ≤ 0, |iteratedDeriv 2 f t| ≤ K₀ * jb t ^ (-P.p - 2) := fun t ht => by
    have := hg3 2 (by norm_num) t ht
    rw [show (2 : ℕ) = 0 + 2 from rfl, hdk 0] at this; simpa using this
  have h3 : ∀ t ≤ 0, |iteratedDeriv 3 f t| ≤ K₀ * jb t ^ (-P.p - 3) := fun t ht => by
    have := hg3 3 (by norm_num) t ht
    rw [show (3 : ℕ) = 1 + 2 from rfl, hdk 1] at this; simpa using this
  have hy8 : y ≤ -8 := by linarith
  obtain ⟨hdiff, hb0, hb1⟩ := c07_aux_I1_core P.p ε K₀ Mχ hp hp1 hε1 hK₀ hMχ
    (fun u => ((hAB ε hε1).1 u).1) (fun u => ((hAB ε hε1).1 u).2.1) f (hf.of_le (by simp))
    (fun z => (hcl z).1) h2 h3 y hy8
  have hI : c07_negative_Q_split_I1 P.p R ε μ = fun y' => calpha P.p * ∫ z, c07_chi ((y' - z) / |y'|) *
      ((deriv f y' - deriv f z) / |y' - z| ^ (P.p + 1)) * (A_eps P.p ε (c01_secant f y' z) - 1) := rfl
  rw [hI]
  refine ⟨hdiff, fun j hj => ?_⟩
  interval_cases j
  · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero]
    refine hb0.trans ?_
    have : 0 ≤ ε * |y| ^ (-2 * P.p - 1) := by have := hε.1; positivity
    rw [← hC1]; nlinarith
  · simp only [iteratedDeriv_one, Nat.cast_one]
    rw [show -2 * P.p - 1 - 1 = -2 * P.p - 2 by ring]
    refine hb1.trans ?_
    have : 0 ≤ ε * |y| ^ (-2 * P.p - 2) := by have := hε.1; positivity
    rw [← hC2]; nlinarith


/-- Blueprint: lem:c07_negative_I2.  The kernel
`κ(y,z) = (1-χ_y(z)) [A_ε(S_f(y,z)) - 1] |y-z|^{-α}`. -/
def c07_negative_I2_kappa (p R ε : ℝ) (μ : ℂ) (y z : ℝ) : ℝ :=
  (1 - c07_chi ((y - z) / |y|)) *
    (A_eps p ε (c01_secant (approximate_solution_family p R ε μ) y z) - 1) / |y - z| ^ (p + 1)

/-- `χ` is smooth; `χ'`, `χ''` are bounded and vanish for `|x| ≥ 1/2`. -/
theorem c07_aux_negI2_chi :
    ContDiff ℝ (⊤ : ℕ∞) c07_chi ∧
    (∀ x, 1 / 2 ≤ |x| → deriv c07_chi x = 0 ∧ deriv (deriv c07_chi) x = 0) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv c07_chi x| ≤ M ∧ |deriv (deriv c07_chi) x| ≤ M := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) c07_chi := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have hev : c07_chi =ᶠ[𝓝 0] fun _ => 1 := by
        have : Ioo (-(1/4 : ℝ)) (1/4) ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
        filter_upwards [this] with t ht
        exact (c07_aux_chi_props).2.2.1 t (abs_le.2 ⟨ht.1.le, ht.2.le⟩)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · unfold c07_chi
      exact Real.smoothTransition.contDiff.contDiffAt.comp x
        ((contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_abs hx))).div_const _)
  have hz : ∀ x, 7 / 16 < |x| → (deriv c07_chi) =ᶠ[𝓝 x] fun _ => 0 := by
    intro x hx
    have hc : Continuous (fun t : ℝ => |t|) := continuous_abs
    have hS : {t : ℝ | 7 / 16 < |t|} ∈ 𝓝 x := (isOpen_lt continuous_const hc).mem_nhds hx
    filter_upwards [hS] with t ht
    have hev : c07_chi =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds (show t ∈ {b : ℝ | (7/16:ℝ) < |b|} from ht)] with s hs
      exact (c07_aux_chi_props).2.1 s (le_of_lt hs)
    rw [hev.deriv_eq]; simp
  have hzz : ∀ x, 1 / 2 ≤ |x| → deriv c07_chi x = 0 ∧ deriv (deriv c07_chi) x = 0 := by
    intro x hx
    have h := hz x (by linarith)
    exact ⟨h.eq_of_nhds, by rw [h.deriv_eq]; simp⟩
  refine ⟨hcd, hzz, ?_⟩
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv c07_chi) := hcd.iterate_deriv 1
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv c07_chi)) := hcd.iterate_deriv 2
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    h1.continuous.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    h2.continuous.continuousOn
  refine ⟨max (max M1 M2) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : |x| ≤ 1
  · have a1 := hM1 x (abs_le.1 hx); have a2 := hM2 x (abs_le.1 hx)
    rw [Real.norm_eq_abs] at a1 a2
    exact ⟨a1.trans ((le_max_left _ _).trans (le_max_left _ _)),
      a2.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · obtain ⟨e1, e2⟩ := hzz x (by linarith [not_le.1 hx])
    rw [e1, e2]; simp


/-- Generic form of the kernel `κ(y,z)` of lem:c07_negative_I2 (for a profile `f`). -/
def c07_aux_negI2_kap (p ε : ℝ) (f : ℝ → ℝ) (y z : ℝ) : ℝ :=
  (1 - c07_chi ((y - z) / |y|)) * (A_eps p ε (c01_secant f y z) - 1) / |y - z| ^ (p + 1)

/-- Joint differentiability data of a function of `(y,z)` at a point. -/
def c07_aux_negI2_J (φ φy φz φyz : ℝ → ℝ → ℝ) (y z : ℝ) : Prop :=
  (∀ᶠ y' in 𝓝 y, HasDerivAt (fun z' => φ y' z') (φz y' z) z) ∧
  HasDerivAt (fun y' => φ y' z) (φy y z) y ∧
  HasDerivAt (fun y' => φz y' z) (φyz y z) y

/-- Symbol-type bounds of a function of `(y,z)` at a point. -/
def c07_aux_negI2_Sb (φ φy φz φyz : ℝ → ℝ → ℝ) (y z a t : ℝ) : Prop :=
  |φ y z| ≤ a ∧ |φy y z| ≤ a * t ∧ |φz y z| ≤ a * t ∧ |φyz y z| ≤ a * t ^ 2

theorem c07_aux_negI2_J_mul {φ φy φz φyz ψ ψy ψz ψyz : ℝ → ℝ → ℝ} {y z : ℝ}
    (h1 : c07_aux_negI2_J φ φy φz φyz y z) (h2 : c07_aux_negI2_J ψ ψy ψz ψyz y z) :
    c07_aux_negI2_J (fun a b => φ a b * ψ a b) (fun a b => φy a b * ψ a b + φ a b * ψy a b)
      (fun a b => φz a b * ψ a b + φ a b * ψz a b)
      (fun a b => φyz a b * ψ a b + φz a b * ψy a b + (φy a b * ψz a b + φ a b * ψyz a b))
      y z :=
  ⟨(h1.1.and h2.1).mono fun _ h => h.1.mul h.2, h1.2.1.mul h2.2.1,
    (h1.2.2.mul h2.2.1).add (h1.2.1.mul h2.2.2)⟩

theorem c07_aux_negI2_Sb_mul {φ φy φz φyz ψ ψy ψz ψyz : ℝ → ℝ → ℝ} {y z a b t : ℝ}
    (ht : 0 ≤ t)
    (h1 : c07_aux_negI2_Sb φ φy φz φyz y z a t) (h2 : c07_aux_negI2_Sb ψ ψy ψz ψyz y z b t) :
    c07_aux_negI2_Sb (fun a b => φ a b * ψ a b) (fun a b => φy a b * ψ a b + φ a b * ψy a b)
      (fun a b => φz a b * ψ a b + φ a b * ψz a b)
      (fun a b => φyz a b * ψ a b + φz a b * ψy a b + (φy a b * ψz a b + φ a b * ψyz a b))
      y z (4 * a * b) t := by
  obtain ⟨a0, a1, a2, a3⟩ := h1
  obtain ⟨b0, b1, b2, b3⟩ := h2
  have ha : 0 ≤ a := (abs_nonneg _).trans a0
  have hb : 0 ≤ b := (abs_nonneg _).trans b0
  have hab : 0 ≤ a * b * t := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · show |φ y z * ψ y z| ≤ 4 * a * b
    rw [abs_mul]
    have := mul_le_mul a0 b0 (abs_nonneg _) ha
    nlinarith [mul_nonneg ha hb]
  · show |φy y z * ψ y z + φ y z * ψy y z| ≤ 4 * a * b * t
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have := mul_le_mul a1 b0 (abs_nonneg _) (by positivity)
    have := mul_le_mul a0 b1 (abs_nonneg _) ha
    nlinarith
  · show |φz y z * ψ y z + φ y z * ψz y z| ≤ 4 * a * b * t
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have := mul_le_mul a2 b0 (abs_nonneg _) (by positivity)
    have := mul_le_mul a0 b2 (abs_nonneg _) ha
    nlinarith
  · show |φyz y z * ψ y z + φz y z * ψy y z + (φy y z * ψz y z + φ y z * ψyz y z)| ≤
      4 * a * b * t ^ 2
    calc _ ≤ |φyz y z| * |ψ y z| + |φz y z| * |ψy y z| +
          (|φy y z| * |ψz y z| + |φ y z| * |ψyz y z|) := by
          rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
      _ ≤ (a * t ^ 2) * b + (a * t) * (b * t) + ((a * t) * (b * t) + a * (b * t ^ 2)) := by
          gcongr
      _ = 4 * a * b * t ^ 2 := by ring

/-- The cutoff factor `1 - χ((y-z)/|y|)`. -/
theorem c07_aux_negI2_cut (M : ℝ) (hM : 0 ≤ M)
    (hMb : ∀ x, |deriv c07_chi x| ≤ M ∧ |deriv (deriv c07_chi) x| ≤ M)
    (y z : ℝ) (hy : y < 0) (hyz : y ≠ z) :
    c07_aux_negI2_J (fun a b => 1 - c07_chi ((a - b) / |a|))
      (fun a b => deriv c07_chi ((a - b) / |a|) * (b / a ^ 2))
      (fun a b => deriv c07_chi ((a - b) / |a|) * |a|⁻¹)
      (fun a b => deriv (deriv c07_chi) ((a - b) / |a|) * (-b / a ^ 2) * |a|⁻¹ +
        deriv c07_chi ((a - b) / |a|) * (a ^ 2)⁻¹) y z ∧
    c07_aux_negI2_Sb (fun a b => 1 - c07_chi ((a - b) / |a|))
      (fun a b => deriv c07_chi ((a - b) / |a|) * (b / a ^ 2))
      (fun a b => deriv c07_chi ((a - b) / |a|) * |a|⁻¹)
      (fun a b => deriv (deriv c07_chi) ((a - b) / |a|) * (-b / a ^ 2) * |a|⁻¹ +
        deriv c07_chi ((a - b) / |a|) * (a ^ 2)⁻¹) y z (1 + 3 * M) |y - z|⁻¹ := by
  obtain ⟨hcd, hzz, -⟩ := c07_aux_negI2_chi
  have hd1 : ∀ x, HasDerivAt c07_chi (deriv c07_chi x) x := fun x =>
    (hcd.differentiable (by simp) x).hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv c07_chi) (deriv (deriv c07_chi) x) x := fun x =>
    ((hcd.iterate_deriv 1).differentiable (by simp) x).hasDerivAt
  have hY : 0 < |y| := abs_pos.2 hy.ne
  have hab : HasDerivAt (fun a : ℝ => |a|) (-1) y := hasDerivAt_abs_neg hy
  have hw : HasDerivAt (fun a => (a - z) / |a|) (-z / y ^ 2) y := by
    refine (((hasDerivAt_id y).sub_const z).div hab hY.ne').congr_deriv ?_
    rw [abs_of_neg hy]; simp only [id]; field_simp; ring
  refine ⟨⟨Eventually.of_forall fun y' => ?_, ?_, ?_⟩, ?_⟩
  · have hw' : HasDerivAt (fun b => (y' - b) / |y'|) (-1 / |y'|) z := by
      simpa using ((hasDerivAt_id z).const_sub y').div_const |y'|
    refine (((hd1 ((y' - z) / |y'|)).comp z hw').const_sub 1).congr_deriv ?_
    simp only [div_eq_mul_inv]; ring
  · refine (((hd1 ((y - z) / |y|)).comp y hw).const_sub 1).congr_deriv ?_
    simp only [div_eq_mul_inv]; ring
  · have h1 := (hd2 _).comp y hw
    have h2 := hab.inv hY.ne'
    have h := h1.mul h2
    refine h.congr_deriv ?_
    simp only [Pi.inv_apply, Function.comp_apply, sq_abs, neg_neg, one_div]
  · -- bounds
    set e := |y - z| with he
    have he0 : 0 < e := abs_pos.2 (sub_ne_zero.2 hyz)
    set t := e⁻¹ with ht
    have ht0 : 0 < t := inv_pos.2 he0
    have hχ := (c07_aux_chi_props).1 ((y - z) / |y|)
    by_cases hw2 : 1 / 2 ≤ |((y - z) / |y|)|
    · obtain ⟨e1, e2⟩ := hzz _ hw2
      refine ⟨?_, ?_, ?_, ?_⟩
      · show |1 - c07_chi ((y - z) / |y|)| ≤ 1 + 3 * M
        rw [abs_le]; constructor <;> linarith
      all_goals
        simp only [e1, e2, zero_mul, zero_add, abs_zero]
        positivity
    · push Not at hw2
      rw [abs_div, abs_abs, div_lt_iff₀ hY] at hw2
      set u := |y|⁻¹ with hu
      have hu0 : 0 ≤ u := inv_nonneg.2 hY.le
      have hut : u ≤ t / 2 := by
        rw [hu, ht, ← one_div, ← one_div, div_div, one_div_le_one_div hY (by positivity)]
        linarith
      have hzb : |z| ≤ 3 / 2 * |y| := by
        have := abs_sub_abs_le_abs_sub z y
        rw [abs_sub_comm z y] at this
        linarith
      have hzy : |z / y ^ 2| ≤ 3 / 2 * u := by
        rw [abs_div, abs_pow, div_le_iff₀ (by positivity), hu]
        have : 3 / 2 * |y|⁻¹ * |y| ^ 2 = 3 / 2 * |y| := by field_simp
        linarith
      have hy2 : |(y ^ 2)⁻¹| = u ^ 2 := by
        rw [abs_inv, abs_pow, hu, inv_pow]
      obtain ⟨m1, m2⟩ := hMb ((y - z) / |y|)
      refine ⟨?_, ?_, ?_, ?_⟩
      · show |1 - c07_chi ((y - z) / |y|)| ≤ 1 + 3 * M
        rw [abs_le]; constructor <;> linarith
      · show |deriv c07_chi ((y - z) / |y|) * (z / y ^ 2)| ≤ (1 + 3 * M) * t
        rw [abs_mul]
        calc _ ≤ M * (3 / 2 * u) := mul_le_mul m1 hzy (abs_nonneg _) hM
          _ ≤ (1 + 3 * M) * t := by nlinarith
      · show |deriv c07_chi ((y - z) / |y|) * |y|⁻¹| ≤ (1 + 3 * M) * t
        rw [abs_mul, abs_inv, abs_abs, ← hu]
        calc _ ≤ M * u := mul_le_mul_of_nonneg_right m1 hu0
          _ ≤ (1 + 3 * M) * t := by nlinarith
      · show |deriv (deriv c07_chi) ((y - z) / |y|) * (-z / y ^ 2) * |y|⁻¹ +
            deriv c07_chi ((y - z) / |y|) * (y ^ 2)⁻¹| ≤ (1 + 3 * M) * t ^ 2
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, hy2, abs_inv, abs_abs, ← hu, neg_div, abs_neg]
        calc _ ≤ M * (3 / 2 * u) * u + M * u ^ 2 := by gcongr
          _ ≤ (1 + 3 * M) * t ^ 2 := by
            have h1 : u * u ≤ t / 2 * (t / 2) := mul_le_mul hut hut hu0 (by positivity)
            have h2 := mul_le_mul_of_nonneg_left h1 hM
            nlinarith [sq_nonneg t]


/-- The factor `A_ε(S_f(y,z)) - 1`. -/
theorem c07_aux_negI2_sec (p ε K CA : ℝ) (hε : 0 ≤ ε)
    (hAB : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 ∧
      |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| ∧ |deriv (deriv (A_eps p ε)) u| ≤ CA * ε)
    (hp : 0 < p) (hCA : 0 ≤ CA)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hK : ∀ x, |deriv f x| ≤ K) (y z : ℝ) (hyz : y ≠ z) :
    c07_aux_negI2_J (fun a b => A_eps p ε (c01_secant f a b) - 1)
      (fun a b => deriv (A_eps p ε) (c01_secant f a b) * ((deriv f a - c01_secant f a b) / (a - b)))
      (fun a b => deriv (A_eps p ε) (c01_secant f a b) * ((c01_secant f a b - deriv f b) / (a - b)))
      (fun a b => deriv (deriv (A_eps p ε)) (c01_secant f a b) *
          ((deriv f a - c01_secant f a b) / (a - b)) * ((c01_secant f a b - deriv f b) / (a - b)) +
        deriv (A_eps p ε) (c01_secant f a b) *
          ((deriv f a + deriv f b - 2 * c01_secant f a b) / (a - b) ^ 2)) y z ∧
    c07_aux_negI2_Sb (fun a b => A_eps p ε (c01_secant f a b) - 1)
      (fun a b => deriv (A_eps p ε) (c01_secant f a b) * ((deriv f a - c01_secant f a b) / (a - b)))
      (fun a b => deriv (A_eps p ε) (c01_secant f a b) * ((c01_secant f a b - deriv f b) / (a - b)))
      (fun a b => deriv (deriv (A_eps p ε)) (c01_secant f a b) *
          ((deriv f a - c01_secant f a b) / (a - b)) * ((c01_secant f a b - deriv f b) / (a - b)) +
        deriv (A_eps p ε) (c01_secant f a b) *
          ((deriv f a + deriv f b - 2 * c01_secant f a b) / (a - b) ^ 2)) y z
      (4 * (CA + p + 1) * ε * K ^ 2) |y - z|⁻¹ := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hA1 : ∀ u, HasDerivAt (A_eps p ε) (deriv (A_eps p ε) u) u := fun u =>
    (c07_aux_A_hasDeriv p ε u hε).differentiableAt.hasDerivAt
  have hA2 : ∀ u, HasDerivAt (deriv (A_eps p ε)) (deriv (deriv (A_eps p ε)) u) u := fun u =>
    (c07_aux_A_hasDeriv2 p ε u hε).differentiableAt.hasDerivAt
  have hne : y - z ≠ 0 := sub_ne_zero.2 hyz
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · filter_upwards [eventually_ne_nhds hyz] with y' hy'
    exact ((hA1 _).comp z (c07_aux_secant_dz f y' z hy' (hfd z))).sub_const 1
  · exact ((hA1 _).comp y (c07_aux_secant_dy f y z hyz (hfd y))).sub_const 1
  · have h1 := (hA2 _).comp y (c07_aux_secant_dy f y z hyz (hfd y))
    have h2 := ((c07_aux_secant_dy f y z hyz (hfd y)).sub_const (deriv f z)).div
      ((hasDerivAt_id' y).sub_const z) hne
    refine (h1.mul h2).congr_deriv ?_
    simp only [Function.comp_apply, Pi.div_apply]
    field_simp
    ring
  · have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK y)
    set S := c01_secant f y z with hS
    have hSK : |S| ≤ K := (c07_secant_calculus f hf K hK).1 y z hyz
    set e := |y - z| with he
    have he0 : 0 < e := abs_pos.2 hne
    set t := e⁻¹ with ht
    have ht0 : 0 < t := inv_pos.2 he0
    have hdiv : ∀ X : ℝ, |X / (y - z)| = |X| * t := fun X => by
      rw [abs_div, div_eq_mul_inv]
    have hdiv2 : ∀ X : ℝ, |X / (y - z) ^ 2| = |X| * t ^ 2 := fun X => by
      rw [abs_div, abs_pow, div_eq_mul_inv, ← he, inv_pow]
    have hSy : |(deriv f y - S) / (y - z)| ≤ 2 * K * t := by
      rw [hdiv]
      have := abs_sub (deriv f y) S
      have := hK y
      exact mul_le_mul_of_nonneg_right (by linarith) ht0.le
    have hSz : |(S - deriv f z) / (y - z)| ≤ 2 * K * t := by
      rw [hdiv]
      have := abs_sub S (deriv f z)
      have := hK z
      exact mul_le_mul_of_nonneg_right (by linarith) ht0.le
    have hSyz : |(deriv f y + deriv f z - 2 * S) / (y - z) ^ 2| ≤ 4 * K * t ^ 2 := by
      rw [hdiv2]
      have h1 := abs_add_le (deriv f y + deriv f z) (-(2 * S))
      have h2 := abs_add_le (deriv f y) (deriv f z)
      rw [abs_neg, abs_mul, abs_two] at h1
      have := hK y
      have := hK z
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [show deriv f y + deriv f z - 2 * S = deriv f y + deriv f z + -(2 * S) by ring]
      linarith
    obtain ⟨b0, b1, b2⟩ := hAB S
    have hS2 : S ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hSK 2
    have hA1b : |deriv (A_eps p ε) S| ≤ (p + 1) * ε * K :=
      b1.trans (mul_le_mul_of_nonneg_left hSK (by positivity))
    have hpe : 0 ≤ (p + 1) * ε := by positivity
    refine ⟨?_, ?_, ?_, ?_⟩
    · show |A_eps p ε S - 1| ≤ 4 * (CA + p + 1) * ε * K ^ 2
      refine b0.trans ?_
      have : (p + 1) / 2 * ε * S ^ 2 ≤ (p + 1) / 2 * ε * K ^ 2 :=
        mul_le_mul_of_nonneg_left hS2 (by positivity)
      nlinarith [mul_nonneg (mul_nonneg hCA hε) (sq_nonneg K), mul_nonneg hpe (sq_nonneg K)]
    · show |deriv (A_eps p ε) S * ((deriv f y - S) / (y - z))| ≤ 4 * (CA + p + 1) * ε * K ^ 2 * t
      rw [abs_mul]
      calc _ ≤ ((p + 1) * ε * K) * (2 * K * t) := mul_le_mul hA1b hSy (abs_nonneg _) (by positivity)
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCA hε) (sq_nonneg K)) ht0.le,
                      mul_nonneg (mul_nonneg hpe (sq_nonneg K)) ht0.le]
    · show |deriv (A_eps p ε) S * ((S - deriv f z) / (y - z))| ≤ 4 * (CA + p + 1) * ε * K ^ 2 * t
      rw [abs_mul]
      calc _ ≤ ((p + 1) * ε * K) * (2 * K * t) := mul_le_mul hA1b hSz (abs_nonneg _) (by positivity)
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCA hε) (sq_nonneg K)) ht0.le,
                      mul_nonneg (mul_nonneg hpe (sq_nonneg K)) ht0.le]
    · show |deriv (deriv (A_eps p ε)) S * ((deriv f y - S) / (y - z)) * ((S - deriv f z) / (y - z)) +
          deriv (A_eps p ε) S * ((deriv f y + deriv f z - 2 * S) / (y - z) ^ 2)| ≤
          4 * (CA + p + 1) * ε * K ^ 2 * t ^ 2
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul]
      calc _ ≤ (CA * ε) * (2 * K * t) * (2 * K * t) + ((p + 1) * ε * K) * (4 * K * t ^ 2) := by
            gcongr
        _ = 4 * (CA + p + 1) * ε * K ^ 2 * t ^ 2 := by ring

/-- The kernel factor `((y-z)²)^{-(p+1)/2} = |y-z|^{-(p+1)}`. -/
theorem c07_aux_negI2_ker (p : ℝ) (hp : 0 < p) (y z : ℝ) (hyz : y ≠ z) :
    c07_aux_negI2_J (fun a b => ((a - b) ^ 2) ^ (-(p + 1) / 2))
      (fun a b => -(p + 1) * (a - b) * ((a - b) ^ 2) ^ (-(p + 1) / 2 - 1))
      (fun a b => (p + 1) * (a - b) * ((a - b) ^ 2) ^ (-(p + 1) / 2 - 1))
      (fun a b => -((p + 1) * (p + 2)) * ((a - b) ^ 2) ^ (-(p + 1) / 2 - 1)) y z ∧
    c07_aux_negI2_Sb (fun a b => ((a - b) ^ 2) ^ (-(p + 1) / 2))
      (fun a b => -(p + 1) * (a - b) * ((a - b) ^ 2) ^ (-(p + 1) / 2 - 1))
      (fun a b => (p + 1) * (a - b) * ((a - b) ^ 2) ^ (-(p + 1) / 2 - 1))
      (fun a b => -((p + 1) * (p + 2)) * ((a - b) ^ 2) ^ (-(p + 1) / 2 - 1)) y z
      ((p + 1) * (p + 2) * |y - z| ^ (-(p + 1))) |y - z|⁻¹ := by
  set r := -(p + 1) / 2 with hr
  have hne : y - z ≠ 0 := sub_ne_zero.2 hyz
  have hq : 0 < (y - z) ^ 2 := by positivity
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · filter_upwards [eventually_ne_nhds hyz] with y' hy'
    have hq' : (y' - z) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hy')
    have h := (((hasDerivAt_id z).const_sub y').pow 2).rpow_const (p := r) (Or.inl hq')
    refine h.congr_deriv ?_
    simp only [id, Pi.pow_apply, hr]; push_cast; ring
  · have h := (((hasDerivAt_id y).sub_const z).pow 2).rpow_const (p := r) (Or.inl hq.ne')
    refine h.congr_deriv ?_
    simp only [id, Pi.pow_apply, hr]; push_cast; ring
  · have h1 := ((hasDerivAt_id y).sub_const z).const_mul (p + 1)
    have h2 := (((hasDerivAt_id y).sub_const z).pow 2).rpow_const (p := r - 1) (Or.inl hq.ne')
    refine (h1.mul h2).congr_deriv ?_
    simp only [id, Pi.pow_apply]
    rw [Real.rpow_sub_one hq.ne' (r - 1)]
    push_cast
    field_simp
    rw [hr]; ring
  · set e := |y - z| with he
    have he0 : 0 < e := abs_pos.2 hne
    set t := e⁻¹ with ht
    have ht0 : 0 < t := inv_pos.2 he0
    set E := e ^ (-(p + 1)) with hE
    have hE0 : 0 ≤ E := Real.rpow_nonneg he0.le _
    have hqe : (y - z) ^ 2 = e ^ 2 := (sq_abs _).symm
    have hqr : ((y - z) ^ 2) ^ r = E := by
      rw [hqe, ← Real.rpow_natCast, ← Real.rpow_mul he0.le, hE, hr]; congr 1; push_cast; ring
    have hqr1 : ((y - z) ^ 2) ^ (r - 1) = E * t ^ 2 := by
      rw [Real.rpow_sub_one hq.ne', hqr, hqe, ht, inv_pow, div_eq_mul_inv]
    have het : e * t = 1 := mul_inv_cancel₀ he0.ne'
    have hpp : 1 ≤ (p + 1) * (p + 2) := by nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · show |((y - z) ^ 2) ^ r| ≤ (p + 1) * (p + 2) * E
      rw [hqr, abs_of_nonneg hE0]; nlinarith
    · show |-(p + 1) * (y - z) * ((y - z) ^ 2) ^ (r - 1)| ≤ (p + 1) * (p + 2) * E * t
      rw [hqr1, abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : (0:ℝ) < p + 1), ← he,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ E * t ^ 2)]
      have : (p + 1) * e * (E * t ^ 2) = (p + 1) * E * t := by
        rw [show (p + 1) * e * (E * t ^ 2) = (p + 1) * E * t * (e * t) by ring, het, mul_one]
      rw [this]
      have : 0 ≤ E * t := by positivity
      have h1 : (0:ℝ) ≤ p + 1 := by linarith
      nlinarith [mul_nonneg (mul_nonneg h1 h1) this]
    · show |(p + 1) * (y - z) * ((y - z) ^ 2) ^ (r - 1)| ≤ (p + 1) * (p + 2) * E * t
      rw [hqr1, abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < p + 1), ← he,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ E * t ^ 2)]
      have : (p + 1) * e * (E * t ^ 2) = (p + 1) * E * t := by
        rw [show (p + 1) * e * (E * t ^ 2) = (p + 1) * E * t * (e * t) by ring, het, mul_one]
      rw [this]
      have : 0 ≤ E * t := by positivity
      have h1 : (0:ℝ) ≤ p + 1 := by linarith
      nlinarith [mul_nonneg (mul_nonneg h1 h1) this]
    · show |-((p + 1) * (p + 2)) * ((y - z) ^ 2) ^ (r - 1)| ≤ (p + 1) * (p + 2) * E * t ^ 2
      rw [hqr1, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < (p + 1) * (p + 2)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ E * t ^ 2)]
      ring_nf; rfl


theorem c07_aux_negI2_conseq {F Φ Φy Φz Φyz : ℝ → ℝ → ℝ} {y z a t : ℝ}
    (hF : ∀ a b, F a b = Φ a b) (hJ : c07_aux_negI2_J Φ Φy Φz Φyz y z)
    (hS : c07_aux_negI2_Sb Φ Φy Φz Φyz y z a t) :
    DifferentiableAt ℝ (F y) z ∧ DifferentiableAt ℝ (fun y' => F y' z) y ∧
    DifferentiableAt ℝ (fun y' => deriv (F y') z) y ∧
    ∀ j ≤ 1, ∀ l ≤ 1,
      |iteratedDeriv j (fun y' => iteratedDeriv l (fun z' => F y' z') z) y| ≤ a * t ^ (j + l) := by
  obtain rfl : F = Φ := funext fun a => funext fun b => hF a b
  have h0 : HasDerivAt (fun z' => F y z') (Φz y z) z := hJ.1.self_of_nhds
  have hev : (fun y' => deriv (fun z' => F y' z') z) =ᶠ[𝓝 y] fun y' => Φz y' z :=
    hJ.1.mono fun y' h => h.deriv
  have h2 : HasDerivAt (fun y' => deriv (F y') z) (Φyz y z) y := hJ.2.2.congr_of_eventuallyEq hev
  obtain ⟨s0, s1, s2, s3⟩ := hS
  refine ⟨h0.differentiableAt, hJ.2.1.differentiableAt, h2.differentiableAt, fun j hj l hl => ?_⟩
  interval_cases j <;> interval_cases l
  · simpa using s0
  · simp only [iteratedDeriv_zero, iteratedDeriv_one, h0.deriv]; simpa using s2
  · simp only [iteratedDeriv_zero, iteratedDeriv_one, hJ.2.1.deriv]; simpa using s1
  · simp only [iteratedDeriv_one]
    rw [h2.deriv]; simpa using s3

/-- `((y-z)²)^{-(p+1)/2} = |y-z|^{-(p+1)}` (also at `y = z`). -/
theorem c07_aux_negI2_powq (p d : ℝ) :
    (d ^ 2) ^ (-(p + 1) / 2) = (|d| ^ (p + 1))⁻¹ := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]
  congr 1; push_cast; ring

/-- `κ` vanishes where `|y-z| < |y|/4`. -/
theorem c07_aux_negI2_vanish (p ε : ℝ) (f : ℝ → ℝ) (y z : ℝ) (hyz : |y - z| < |y| / 4) :
    (∀ᶠ z' in 𝓝 z, c07_aux_negI2_kap p ε f y z' = 0) ∧
    (∀ᶠ y' in 𝓝 y, c07_aux_negI2_kap p ε f y' z = 0) ∧
    (∀ᶠ y' in 𝓝 y, deriv (c07_aux_negI2_kap p ε f y') z = 0) := by
  have h0 : ∀ a b : ℝ, |a - b| < |a| / 4 → c07_aux_negI2_kap p ε f a b = 0 := by
    intro a b hq
    have hq1 : 0 < |a| := by have := abs_nonneg (a - b); linarith
    have : c07_chi ((a - b) / |a|) = 1 := by
      apply (c07_aux_chi_props).2.2.1
      rw [abs_div, abs_abs, div_le_iff₀ hq1]
      linarith
    simp [c07_aux_negI2_kap, this]
  have hz : ∀ᶠ z' in 𝓝 z, |y - z'| < |y| / 4 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (show z ∈ {z' : ℝ | |y - z'| < |y| / 4} from hyz)
  have hy : ∀ᶠ y' in 𝓝 y, |y' - z| < |y'| / 4 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (show y ∈ {y' : ℝ | |y' - z| < |y'| / 4} from hyz)
  refine ⟨hz.mono fun z' h => h0 _ _ h, hy.mono fun y' h => h0 _ _ h, hy.mono fun y' h => ?_⟩
  have hz' : ∀ᶠ z' in 𝓝 z, |y' - z'| < |y'| / 4 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (show z ∈ {z' : ℝ | |y' - z'| < |y'| / 4} from h)
  have hev : c07_aux_negI2_kap p ε f y' =ᶠ[𝓝 z] fun _ => 0 := hz'.mono fun z' h => h0 _ _ h
  rw [hev.deriv_eq]; simp

/-- Pointwise derivatives and bounds for `κ` (lem:c07_negative_I2 (2)). -/
theorem c07_aux_negI2_pt (p ε K CA M : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (hCA : 0 ≤ CA)
    (hAB : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 ∧
      |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| ∧ |deriv (deriv (A_eps p ε)) u| ≤ CA * ε)
    (hM : 0 ≤ M) (hMb : ∀ x, |deriv c07_chi x| ≤ M ∧ |deriv (deriv c07_chi) x| ≤ M)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hK : ∀ x, |deriv f x| ≤ K) (y z : ℝ) (hy : y < 0) :
    DifferentiableAt ℝ (c07_aux_negI2_kap p ε f y) z ∧
    DifferentiableAt ℝ (fun y' => c07_aux_negI2_kap p ε f y' z) y ∧
    DifferentiableAt ℝ (fun y' => deriv (c07_aux_negI2_kap p ε f y') z) y ∧
    ∀ j ≤ 1, ∀ l ≤ 1,
      |iteratedDeriv j (fun y' => iteratedDeriv l (fun z' => c07_aux_negI2_kap p ε f y' z') z) y| ≤
        64 * (1 + 3 * M) * (CA + p + 1) * K ^ 2 * ((p + 1) * (p + 2)) * ε *
          Set.indicator {z' : ℝ | |y| / 4 ≤ |y - z'|} (fun z' => |y - z'| ^ (-p - 1 - j - l)) z := by
  have hY : 0 < |y| := abs_pos.2 hy.ne
  by_cases hreg : |y| / 4 ≤ |y - z|
  · have hyz : y ≠ z := by
      intro h
      have : |y - z| = 0 := by rw [h, sub_self, abs_zero]
      linarith
    have he0 : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 hyz)
    obtain ⟨Jc, Sc⟩ := c07_aux_negI2_cut M hM hMb y z hy hyz
    obtain ⟨Ja, Sa⟩ := c07_aux_negI2_sec p ε K CA hε hAB hp hCA f hf hK y z hyz
    obtain ⟨Jk, Sk⟩ := c07_aux_negI2_ker p hp y z hyz
    have ht : (0:ℝ) ≤ |y - z|⁻¹ := inv_nonneg.2 he0.le
    have J := c07_aux_negI2_J_mul (c07_aux_negI2_J_mul Jc Ja) Jk
    have S := c07_aux_negI2_Sb_mul ht (c07_aux_negI2_Sb_mul ht Sc Sa) Sk
    obtain ⟨d1, d2, d3, hb⟩ := c07_aux_negI2_conseq (F := c07_aux_negI2_kap p ε f)
      (fun a b => by
        simp only [c07_aux_negI2_kap]; rw [div_eq_mul_inv, c07_aux_negI2_powq]) J S
    refine ⟨d1, d2, d3, fun j hj l hl => ?_⟩
    refine (hb j hj l hl).trans (le_of_eq ?_)
    rw [Set.indicator_of_mem (show z ∈ {z' : ℝ | |y| / 4 ≤ |y - z'|} from hreg)]
    have key : |y - z| ^ (-(p + 1)) * (|y - z|⁻¹) ^ (j + l) = |y - z| ^ (-p - 1 - j - l) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg he0.le, ← Real.rpow_add he0]
      congr 1; push_cast; ring
    rw [← key]; ring
  · push Not at hreg
    obtain ⟨vz, vy, vyz⟩ := c07_aux_negI2_vanish p ε f y z hreg
    have ez : c07_aux_negI2_kap p ε f y =ᶠ[𝓝 z] fun _ => 0 := vz
    have ey : (fun y' => c07_aux_negI2_kap p ε f y' z) =ᶠ[𝓝 y] fun _ => 0 := vy
    have eyz : (fun y' => deriv (c07_aux_negI2_kap p ε f y') z) =ᶠ[𝓝 y] fun _ => 0 := vyz
    refine ⟨(differentiableAt_const (0:ℝ)).congr_of_eventuallyEq ez,
      (differentiableAt_const (0:ℝ)).congr_of_eventuallyEq ey,
      (differentiableAt_const (0:ℝ)).congr_of_eventuallyEq eyz, fun j hj l hl => ?_⟩
    rw [Set.indicator_of_notMem (show z ∉ {z' : ℝ | |y| / 4 ≤ |y - z'|} by
      simp only [Set.mem_ofPred_eq, not_le]; exact hreg), mul_zero]
    have hval : c07_aux_negI2_kap p ε f y z = 0 := vz.self_of_nhds
    have hd0 : deriv (c07_aux_negI2_kap p ε f y) z = 0 := by rw [ez.deriv_eq]; simp
    interval_cases j <;> interval_cases l
    · simp [hval]
    · simp [hd0]
    · simp only [iteratedDeriv_zero, iteratedDeriv_one]; rw [ey.deriv_eq]; simp
    · simp only [iteratedDeriv_one]; rw [eyz.deriv_eq]; simp


theorem c07_aux_negI2_win (y y' z : ℝ) (hy1 : 1 ≤ |y|) (hyy : |y' - y| < |y| / 16)
    (hz : |y'| / 4 ≤ |y' - z|) : 1 + |y - z| ≤ 7 * |y' - z| := by
  have h1 := abs_sub_abs_le_abs_sub y y'
  rw [abs_sub_comm y y'] at h1
  have h2 := abs_sub_le y y' z
  rw [abs_sub_comm y y'] at h2
  linarith

theorem c07_aux_negI2_winpow (y y' z q : ℝ) (hq : 0 ≤ q) (hy1 : 1 ≤ |y|)
    (hyy : |y' - y| < |y| / 16) (hz : |y'| / 4 ≤ |y' - z|) :
    |y' - z| ^ (-q) ≤ 7 ^ q * (1 + |y - z|) ^ (-q) := by
  have hw := c07_aux_negI2_win y y' z hy1 hyy hz
  have he : 0 < |y' - z| := by
    have : (0:ℝ) < 1 + |y - z| := by positivity
    linarith
  have h1 : (7 * |y' - z|) ^ (-q) ≤ (1 + |y - z|) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hw (by linarith)
  rw [Real.mul_rpow (by norm_num) he.le] at h1
  have h7 : (7:ℝ) ^ q * (7:ℝ) ^ (-q) = 1 := by
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  calc |y' - z| ^ (-q) = 7 ^ q * ((7:ℝ) ^ (-q) * |y' - z| ^ (-q)) := by
        rw [← mul_assoc, h7, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem c07_aux_negI2_majint (y e : ℝ) (he : e < -1) :
    Integrable (fun z => (1 + |y - z|) ^ e) := by
  have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := -e)
    (by simp; linarith)).comp_sub_left y
  simpa [Real.norm_eq_abs] using h

theorem c07_aux_negI2_tend (y e : ℝ) (he : e < 0) :
    Tendsto (fun z => (1 + |y - z|) ^ e) atTop (𝓝 0) ∧
    Tendsto (fun z => (1 + |y - z|) ^ e) atBot (𝓝 0) := by
  have hT := tendsto_rpow_neg_atTop (y := -e) (by linarith)
  rw [neg_neg] at hT
  constructor
  · refine hT.comp (tendsto_atTop_mono (fun z => ?_) (tendsto_atTop_add_const_right atTop (-y) tendsto_id))
    simp only [id]
    have := neg_abs_le (y - z); linarith
  · refine hT.comp (tendsto_atTop_mono (fun z => ?_)
      (tendsto_atTop_add_const_right atBot y tendsto_neg_atBot_atTop))
    have := le_abs_self (y - z); linarith

theorem c07_aux_negI2_meas (p ε : ℝ) (hε : 0 ≤ ε) (f : ℝ → ℝ) (hf : Continuous f) (y : ℝ) :
    Measurable (c07_aux_negI2_kap p ε f y) := by
  have h1 := c07_aux_secant_meas f hf y
  have h2 := (c04_aux_A_cont p ε hε).measurable
  have h3 := (c07_aux_chi_props).2.2.2.measurable
  unfold c07_aux_negI2_kap
  fun_prop

theorem c07_aux_negI2_meas_deriv (G : ℝ → ℝ → ℝ) (y : ℝ) (hG : ∀ y', Measurable (G y'))
    (hd : ∀ z, DifferentiableAt ℝ (fun y' => G y' z) y) :
    Measurable (fun z => deriv (fun y' => G y' z) y) := by
  set u : ℕ → ℝ := fun n => y + 1 / ((n : ℝ) + 1) with hu
  have hu1 : Tendsto u atTop (𝓝[≠] y) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add y
      simpa [hu] using this
    · refine Eventually.of_forall fun n => ?_
      simp only [hu, mem_compl_iff, mem_singleton_iff, add_eq_left]
      positivity
  refine measurable_of_tendsto_metrizable (f := fun n z => slope (fun y' => G y' z) y (u n))
    (fun n => ?_) (tendsto_pi_nhds.2 fun z => ?_)
  · simp only [slope_def_field]
    have := hG (u n); have := hG y
    fun_prop
  · exact (hasDerivAt_iff_tendsto_slope.1 (hd z).hasDerivAt).comp hu1


/-- Generic form of `𝓘₂` (for a profile `f`, `g = f - W`). -/
def c07_aux_negI2_I (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  calpha p * ∫ z, (1 - c07_chi ((y - z) / |y|)) *
    ((deriv (fun x => f x - corner x) y - deriv (fun x => f x - corner x) z) / |y - z| ^ (p + 1)) *
    (A_eps p ε (c01_secant f y z) - 1)

/-- Indicator majorant on a window around `y`. -/
theorem c07_aux_negI2_indmaj (x y z e : ℝ) (he : e ≤ 0) (hy1 : 1 ≤ |y|)
    (hxy : |x - y| < |y| / 16) :
    Set.indicator {z' : ℝ | |x| / 4 ≤ |x - z'|} (fun z' => |x - z'| ^ e) z ≤
      7 ^ (-e) * (1 + |y - z|) ^ e := by
  by_cases hz : |x| / 4 ≤ |x - z|
  · rw [Set.indicator_of_mem (show z ∈ {z' : ℝ | |x| / 4 ≤ |x - z'|} from hz)]
    have := c07_aux_negI2_winpow y x z (-e) (by linarith) hy1 hxy hz
    simpa using this
  · rw [Set.indicator_of_notMem (show z ∉ {z' : ℝ | |x| / 4 ≤ |x - z'|} from hz)]
    positivity

theorem c07_aux_negI2_deriv_g (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    (∀ z, z ≠ 0 → HasDerivAt (fun x => f x - corner x) (deriv (fun x => f x - corner x) z) z) ∧
    (∀ z, z ≠ 0 → |deriv (fun x => f x - corner x) z| ≤ |deriv f z| + 1) ∧
    (∀ z, z < 0 → deriv (fun x => f x - corner x) z = deriv f z + 1) := by
  have hc : ∀ z, z ≠ 0 → HasDerivAt corner (if z < 0 then -1 else 0) z := fun z hz => by
    rw [← c04_aux_deriv_corner z hz]; exact (c07_aux_corner_diff z hz).hasDerivAt
  have hd : ∀ z, z ≠ 0 → HasDerivAt (fun x => f x - corner x)
      (deriv f z - if z < 0 then -1 else 0) z := fun z hz => (hf z).hasDerivAt.sub (hc z hz)
  refine ⟨fun z hz => (hd z hz).differentiableAt.hasDerivAt, fun z hz => ?_, fun z hz => ?_⟩
  · rw [(hd z hz).deriv]
    refine (abs_sub _ _).trans ?_
    split_ifs <;> simp
  · rw [(hd z hz.ne).deriv]; simp [hz]

/-- Integrability and the integration-by-parts formula (lem:c07_negative_I2 (1)) at `x < 0`,
`|x| ≥ 1`, for a generic profile. -/
theorem c07_aux_negI2_formula (p ε K CA M : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (hCA : 0 ≤ CA)
    (hAB : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 ∧
      |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| ∧ |deriv (deriv (A_eps p ε)) u| ≤ CA * ε)
    (hM : 0 ≤ M) (hMb : ∀ x, |deriv c07_chi x| ≤ M ∧ |deriv (deriv c07_chi) x| ≤ M)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hK : ∀ x, |deriv f x| ≤ K)
    (hg : ∀ z, |f z - corner z| ≤ K) (x : ℝ) (hx : x < 0) (hx1 : 1 ≤ |x|) :
    Integrable (c07_aux_negI2_kap p ε f x) ∧
    Integrable (fun z => (f z - corner z) * deriv (fun z' => c07_aux_negI2_kap p ε f x z') z) ∧
    c07_aux_negI2_I p ε f x =
      calpha p * deriv (fun x => f x - corner x) x * (∫ z, c07_aux_negI2_kap p ε f x z) +
        calpha p * ∫ z, (f z - corner z) * deriv (fun z' => c07_aux_negI2_kap p ε f x z') z := by
  set κ := c07_aux_negI2_kap p ε f x with hκ
  set g : ℝ → ℝ := fun x => f x - corner x with hgdef
  set Cκ := 64 * (1 + 3 * M) * (CA + p + 1) * K ^ 2 * ((p + 1) * (p + 2)) with hCκ
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hCκ0 : 0 ≤ Cκ := by positivity
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hpt := fun z => c07_aux_negI2_pt p ε K CA M hp hε hCA hAB hM hMb f hf hK x z hx
  have hxx : |x - x| < |x| / 16 := by rw [sub_self, abs_zero]; positivity
  have hb0 : ∀ z, |κ z| ≤ Cκ * ε * (7 ^ (p + 1) * (1 + |x - z|) ^ (-p - 1)) := by
    intro z
    have h := (hpt z).2.2.2 0 zero_le_one 0 zero_le_one
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := c07_aux_negI2_indmaj x x z (-p - 1) (by linarith) hx1 hxx
    rwa [show -(-p - 1) = p + 1 by ring] at this
  have hb1 : ∀ z, |deriv κ z| ≤ Cκ * ε * (7 ^ (p + 2) * (1 + |x - z|) ^ (-p - 1 - 1)) := by
    intro z
    have h := (hpt z).2.2.2 0 zero_le_one 1 le_rfl
    simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one, sub_zero] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := c07_aux_negI2_indmaj x x z (-p - 1 - 1) (by linarith) hx1 hxx
    rwa [show -(-p - 1 - 1) = p + 2 by ring] at this
  have hκm : Measurable κ := c07_aux_negI2_meas p ε hε f hf.continuous x
  have hκd : ∀ z, HasDerivAt κ (deriv κ z) z := fun z => (hpt z).1.hasDerivAt
  have hκc : Continuous κ := continuous_iff_continuousAt.2 fun z => (hκd z).continuousAt
  have hgc : Continuous g := by
    have : Continuous corner := by unfold corner; fun_prop
    exact hf.continuous.sub this
  have i1 : Integrable κ :=
    ((c07_aux_negI2_majint x (-p - 1) (by linarith)).const_mul (Cκ * ε * 7 ^ (p + 1))).mono'
      hκm.aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; refine (hb0 z).trans (le_of_eq ?_); ring)
  have i2 : Integrable (fun z => g z * deriv κ z) := by
    refine ((c07_aux_negI2_majint x (-p - 1 - 1) (by linarith)).const_mul
      (K * (Cκ * ε * 7 ^ (p + 2)))).mono'
      (hgc.measurable.mul (measurable_deriv κ)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |g z| * |deriv κ z| ≤ K * (Cκ * ε * (7 ^ (p + 2) * (1 + |x - z|) ^ (-p - 1 - 1))) :=
          mul_le_mul (hg z) (hb1 z) (abs_nonneg _) hK0
      _ = _ := by ring
  obtain ⟨hgd, hgb, -⟩ := c07_aux_negI2_deriv_g f hfd
  have hae : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [ae_iff]; simp
  have i3 : Integrable (fun z => deriv g z * κ z) := by
    refine i1.bdd_mul (c := K + 1) (measurable_deriv g).aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs]; have := hgb z hz; have := hK z; linarith
  refine ⟨i1, i2, ?_⟩
  -- the integrand splits
  have hsplit : (fun z => (1 - c07_chi ((x - z) / |x|)) *
      ((deriv g x - deriv g z) / |x - z| ^ (p + 1)) * (A_eps p ε (c01_secant f x z) - 1)) =
      fun z => deriv g x * κ z - deriv g z * κ z := by
    funext z; simp only [hκ, c07_aux_negI2_kap]; ring
  -- integration by parts on the two half-lines
  have hmaj0 := (c07_aux_negI2_tend x (-p - 1) (by linarith))
  have hbnd : ∀ z, ‖(g * κ) z‖ ≤ K * (Cκ * ε * 7 ^ (p + 1)) * (1 + |x - z|) ^ (-p - 1) := by
    intro z
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    calc |g z| * |κ z| ≤ K * (Cκ * ε * (7 ^ (p + 1) * (1 + |x - z|) ^ (-p - 1))) :=
          mul_le_mul (hg z) (hb0 z) (abs_nonneg _) hK0
      _ = _ := by ring
  have htop : Tendsto (g * κ) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbnd ?_
    simpa using hmaj0.1.const_mul (K * (Cκ * ε * 7 ^ (p + 1)))
  have hbot : Tendsto (g * κ) atBot (𝓝 0) := by
    refine squeeze_zero_norm hbnd ?_
    simpa using hmaj0.2.const_mul (K * (Cκ * ε * 7 ^ (p + 1)))
  have h0 : Tendsto (g * κ) (𝓝 0) (𝓝 (g 0 * κ 0)) := (hgc.mul hκc).tendsto 0
  have IR := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (u := g) (v := κ) (u' := deriv g)
    (v' := deriv κ) (a' := g 0 * κ 0) (b' := 0)
    (fun z hz => hgd z (ne_of_gt hz)) (fun z _ => hκd z) i2.integrableOn i3.integrableOn
    (h0.mono_left nhdsWithin_le_nhds) htop
  have IL := integral_Iic_mul_deriv_eq_deriv_mul (a := 0) (u := g) (v := κ) (u' := deriv g)
    (v' := deriv κ) (a' := g 0 * κ 0) (b' := 0)
    (fun z hz => hgd z (ne_of_lt hz)) (fun z _ => hκd z) i2.integrableOn i3.integrableOn
    (h0.mono_left nhdsWithin_le_nhds) hbot
  have hS2 := integral_add_compl (measurableSet_Iic (a := (0:ℝ))) i2
  have hS3 := integral_add_compl (measurableSet_Iic (a := (0:ℝ))) i3
  rw [compl_Iic] at hS2 hS3
  have hibp : ∫ z, g z * deriv κ z = -∫ z, deriv g z * κ z := by
    rw [← hS2, ← hS3, IR, IL]; ring
  show calpha p * _ = _
  rw [hsplit, integral_sub (i1.const_mul _) i3, integral_const_mul]
  have e2 : ∫ z, (f z - corner z) * deriv (fun z' => κ z') z = ∫ z, g z * deriv κ z := rfl
  rw [e2, hibp]; ring


/-- The four pointwise bounds of lem:c07_negative_I2 (2), in explicit form. -/
theorem c07_aux_negI2_pt4 (p ε K CA M : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (hCA : 0 ≤ CA)
    (hAB : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 ∧
      |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| ∧ |deriv (deriv (A_eps p ε)) u| ≤ CA * ε)
    (hM : 0 ≤ M) (hMb : ∀ x, |deriv c07_chi x| ≤ M ∧ |deriv (deriv c07_chi) x| ≤ M)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hK : ∀ x, |deriv f x| ≤ K) (x z : ℝ) (hx : x < 0) :
    let Cκ := 64 * (1 + 3 * M) * (CA + p + 1) * K ^ 2 * ((p + 1) * (p + 2))
    let S := {z' : ℝ | |x| / 4 ≤ |x - z'|}
    |c07_aux_negI2_kap p ε f x z| ≤ Cκ * ε * S.indicator (fun z' => |x - z'| ^ (-p - 1)) z ∧
    |deriv (c07_aux_negI2_kap p ε f x) z| ≤
      Cκ * ε * S.indicator (fun z' => |x - z'| ^ (-p - 1 - 1)) z ∧
    |deriv (fun y' => c07_aux_negI2_kap p ε f y' z) x| ≤
      Cκ * ε * S.indicator (fun z' => |x - z'| ^ (-p - 1 - 1)) z ∧
    |deriv (fun y' => deriv (c07_aux_negI2_kap p ε f y') z) x| ≤
      Cκ * ε * S.indicator (fun z' => |x - z'| ^ (-p - 1 - 1 - 1)) z := by
  intro Cκ S
  have h := (c07_aux_negI2_pt p ε K CA M hp hε hCA hAB hM hMb f hf hK x z hx).2.2.2
  have h00 := h 0 zero_le_one 0 zero_le_one
  have h01 := h 0 zero_le_one 1 le_rfl
  have h10 := h 1 le_rfl 0 zero_le_one
  have h11 := h 1 le_rfl 1 le_rfl
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.cast_zero, Nat.cast_one, sub_zero]
    at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩


/-- Differentiability of `𝓘₂` and the bounds lem:c07_negative_I2 (3), generic profile. -/
theorem c07_aux_negI2_main (p ε K CA M T1 T2 T3 : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (hCA : 0 ≤ CA)
    (hAB : ∀ u, |A_eps p ε u - 1| ≤ (p + 1) / 2 * ε * u ^ 2 ∧
      |deriv (A_eps p ε) u| ≤ (p + 1) * ε * |u| ∧ |deriv (deriv (A_eps p ε)) u| ≤ CA * ε)
    (hM : 0 ≤ M) (hMb : ∀ x, |deriv c07_chi x| ≤ M ∧ |deriv (deriv c07_chi) x| ≤ M)
    (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hK1 : 1 ≤ K) (hK : ∀ x, |deriv f x| ≤ K)
    (hg : ∀ z, |f z - corner z| ≤ K * jb z ^ (-p))
    (hg1 : ∀ z ≤ 0, |deriv f z + 1| ≤ K * jb z ^ (-p - 1))
    (hg2 : ∀ z ≤ 0, |deriv (deriv f) z| ≤ K * jb z ^ (-p - 2))
    (y : ℝ) (hy : y < 0) (hy2 : 2 ≤ |y|)
    (hS1i : IntegrableOn (fun z => |y - z| ^ (-(p + 1))) {z | |y| / 4 ≤ |y - z|})
    (hS1 : ∫ z in {z | |y| / 4 ≤ |y - z|}, |y - z| ^ (-(p + 1)) ≤ T1 * |y| ^ (1 - (p + 1)))
    (hS2i : IntegrableOn (fun z => |y - z| ^ (-(p + 2))) {z | |y| / 4 ≤ |y - z|})
    (hS2 : ∫ z in {z | |y| / 4 ≤ |y - z|}, |y - z| ^ (-(p + 2)) ≤ T2 * |y| ^ (1 - (p + 2)))
    (hJ2i : IntegrableOn (fun z => jb z ^ (-p) * |y - z| ^ (-(p + 2))) {z | |y| / 4 ≤ |y - z|})
    (hJ2 : ∫ z in {z | |y| / 4 ≤ |y - z|}, jb z ^ (-p) * |y - z| ^ (-(p + 2)) ≤
      T2 * |y| ^ (1 - p - (p + 2)))
    (hJ3i : IntegrableOn (fun z => jb z ^ (-p) * |y - z| ^ (-(p + 3))) {z | |y| / 4 ≤ |y - z|})
    (hJ3 : ∫ z in {z | |y| / 4 ≤ |y - z|}, jb z ^ (-p) * |y - z| ^ (-(p + 3)) ≤
      T3 * |y| ^ (1 - p - (p + 3))) :
    DifferentiableAt ℝ (c07_aux_negI2_I p ε f) y ∧
    |c07_aux_negI2_I p ε f y| ≤
      calpha p * K * (64 * (1 + 3 * M) * (CA + p + 1) * K ^ 2 * ((p + 1) * (p + 2))) *
        (T1 + T2) * ε * |y| ^ (-2 * p - 1) ∧
    |deriv (c07_aux_negI2_I p ε f) y| ≤
      calpha p * K * (64 * (1 + 3 * M) * (CA + p + 1) * K ^ 2 * ((p + 1) * (p + 2))) *
        (T1 + T2 + T3) * ε * |y| ^ (-2 * p - 2) := by
  set Cκ := 64 * (1 + 3 * M) * (CA + p + 1) * K ^ 2 * ((p + 1) * (p + 2)) with hCκ
  have hSm : MeasurableSet {z : ℝ | |y| / 4 ≤ |y - z|} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [show -(p + 1) = -p - 1 by ring] at hS1i hS1
  rw [show -(p + 2) = -p - 1 - 1 by ring] at hS2i hS2 hJ2i hJ2
  rw [show -(p + 3) = -p - 1 - 1 - 1 by ring] at hJ3i hJ3
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hfd : Differentiable ℝ f := hf1.differentiable one_ne_zero
  have hK0 : 0 ≤ K := by linarith
  have hCκ0 : 0 ≤ Cκ := by positivity
  have hc := c03_aux_calpha_pos p hp hp1
  have hY : 0 < |y| := by linarith
  have hy1 : 1 ≤ |y| := by linarith
  have hgK : ∀ z, |f z - corner z| ≤ K := fun z =>
    (hg z).trans (by
      have := c07_aux_jb_rpow_neg_le_one z p hp.le
      nlinarith)
  have hpt := fun x z (hx : x < 0) =>
    c07_aux_negI2_pt p ε K CA M hp hε hCA hAB hM hMb f hf1 hK x z hx
  have hpt4 := fun x z (hx : x < 0) =>
    c07_aux_negI2_pt4 p ε K CA M hp hε hCA hAB hM hMb f hf1 hK x z hx
  have hfor := fun x (hx : x < 0) (hx1 : 1 ≤ |x|) =>
    c07_aux_negI2_formula p ε K CA M hp hε hCA hAB hM hMb f hf1 hK hgK x hx hx1
  set κ := c07_aux_negI2_kap p ε f with hκ
  set g : ℝ → ℝ := fun x => f x - corner x with hgdef
  have hgc : Continuous g := by
    have : Continuous corner := by unfold corner; fun_prop
    exact hf.continuous.sub this
  set s := Metric.ball y (|y| / 16) with hsdef
  have hs : s ∈ 𝓝 y := Metric.ball_mem_nhds y (by positivity)
  have hball : ∀ x ∈ s, x < 0 ∧ 1 ≤ |x| ∧ |x - y| < |y| / 16 := by
    intro x hx
    rw [hsdef, Metric.mem_ball, Real.dist_eq] at hx
    have hyy : |y| = -y := abs_of_neg hy
    have h := abs_lt.1 hx
    have hx0 : x < 0 := by linarith
    refine ⟨hx0, ?_, hx⟩
    rw [abs_of_neg hx0]; linarith
  have hκm : ∀ x, Measurable (κ x) := fun x => c07_aux_negI2_meas p ε hε f hf1.continuous x
  -- derivative of `F(x) = ∫ κ(x,z) dz`
  obtain ⟨-, hF⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x z => κ x z) (F' := fun x z => deriv (fun y' => κ y' z) x) (x₀ := y)
    (bound := fun z => Cκ * ε * (7 ^ (p + 2) * (1 + |y - z|) ^ (-p - 1 - 1))) hs
    (Eventually.of_forall fun x => (hκm x).aestronglyMeasurable) (hfor y hy hy1).1
    (c07_aux_negI2_meas_deriv κ y hκm (fun z => (hpt y z hy).2.1)).aestronglyMeasurable
    (Eventually.of_forall fun z x hx => by
      obtain ⟨hx0, -, hxy⟩ := hball x hx
      rw [Real.norm_eq_abs]
      refine (hpt4 x z hx0).2.2.1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have := c07_aux_negI2_indmaj x y z (-p - 1 - 1) (by linarith) hy1 hxy
      rwa [show -(-p - 1 - 1) = p + 2 by ring] at this)
    (((c07_aux_negI2_majint y (-p - 1 - 1) (by linarith)).const_mul (7 ^ (p + 2))).const_mul
      (Cκ * ε))
    (Eventually.of_forall fun z x hx => ((hpt x z (hball x hx).1).2.1).hasDerivAt)
  -- derivative of `H(x) = ∫ g(z) ∂_z κ(x,z) dz`
  obtain ⟨-, hH⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x z => g z * deriv (κ x) z)
    (F' := fun x z => g z * deriv (fun y' => deriv (κ y') z) x) (x₀ := y)
    (bound := fun z => K * (Cκ * ε * (7 ^ (p + 3) * (1 + |y - z|) ^ (-p - 1 - 1 - 1)))) hs
    (Eventually.of_forall fun x => (hgc.measurable.mul (measurable_deriv _)).aestronglyMeasurable)
    (hfor y hy hy1).2.1
    ((hgc.measurable.mul (c07_aux_negI2_meas_deriv (fun y' z => deriv (κ y') z) y
      (fun y' => measurable_deriv _) (fun z => (hpt y z hy).2.2.1))).aestronglyMeasurable)
    (Eventually.of_forall fun z x hx => by
      obtain ⟨hx0, -, hxy⟩ := hball x hx
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hgK z) ((hpt4 x z hx0).2.2.2.trans
        (mul_le_mul_of_nonneg_left ?_ (by positivity))) (abs_nonneg _) hK0
      have := c07_aux_negI2_indmaj x y z (-p - 1 - 1 - 1) (by linarith) hy1 hxy
      rwa [show -(-p - 1 - 1 - 1) = p + 3 by ring] at this)
    ((((c07_aux_negI2_majint y (-p - 1 - 1 - 1) (by linarith)).const_mul (7 ^ (p + 3))).const_mul
      (Cκ * ε)).const_mul K)
    (Eventually.of_forall fun z x hx =>
      ((hpt x z (hball x hx).1).2.2.1.hasDerivAt.const_mul (g z)))
  -- `𝓘₂` near `y`
  have hdg := c07_aux_negI2_deriv_g f hfd
  have hIeq : ∀ x ∈ s, c07_aux_negI2_I p ε f x = calpha p * (deriv f x + 1) * (∫ z, κ x z) +
      calpha p * ∫ z, g z * deriv (κ x) z := by
    intro x hx
    obtain ⟨hx0, hx1, -⟩ := hball x hx
    rw [(hfor x hx0 hx1).2.2, hdg.2.2 x hx0]
  have hev : c07_aux_negI2_I p ε f =ᶠ[𝓝 y] fun x => calpha p * (deriv f x + 1) * (∫ z, κ x z) +
      calpha p * ∫ z, g z * deriv (κ x) z := Filter.eventually_of_mem hs hIeq
  have hf2 : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := hf.iterate_deriv 1
  have hdf : HasDerivAt (fun x => deriv f x + 1) (deriv (deriv f) y) y :=
    ((hf2.differentiable (by simp) y).hasDerivAt).add_const 1
  have hDI := ((((hdf.const_mul (calpha p)).mul hF).add (hH.const_mul (calpha p)))).congr_of_eventuallyEq hev
  -- integral bounds at `y`
  have F0b : |∫ z, κ y z| ≤ Cκ * ε * (T1 * |y| ^ (1 - (p + 1))) := by
    have h := norm_integral_le_of_norm_le ((hS1i.integrable_indicator hSm).const_mul (Cκ * ε))
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hpt4 y z hy).1)
    rw [integral_const_mul, integral_indicator hSm, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hS1 (by positivity))
  have DFb : |∫ z, deriv (fun y' => κ y' z) y| ≤ Cκ * ε * (T2 * |y| ^ (1 - (p + 2))) := by
    have h := norm_integral_le_of_norm_le ((hS2i.integrable_indicator hSm).const_mul (Cκ * ε))
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hpt4 y z hy).2.2.1)
    rw [integral_const_mul, integral_indicator hSm, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hS2 (by positivity))
  have hgprod : ∀ z (Dv e : ℝ),
      |Dv| ≤ Cκ * ε * Set.indicator {z' : ℝ | |y| / 4 ≤ |y - z'|} (fun z' => |y - z'| ^ e) z →
      |g z * Dv| ≤ K * Cκ * ε *
        Set.indicator {z' : ℝ | |y| / 4 ≤ |y - z'|} (fun z' => jb z' ^ (-p) * |y - z'| ^ e) z := by
    intro z Dv e hD
    by_cases hz : z ∈ {z' : ℝ | |y| / 4 ≤ |y - z'|}
    · rw [Set.indicator_of_mem hz] at hD ⊢
      rw [abs_mul]
      have hj : 0 ≤ jb z ^ (-p) := Real.rpow_nonneg (by linarith [c07_aux_one_le_jb z]) _
      calc |g z| * |Dv| ≤ (K * jb z ^ (-p)) * (Cκ * ε * |y - z| ^ e) :=
            mul_le_mul (hg z) hD (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hz] at hD ⊢
      have : Dv = 0 := abs_nonpos_iff.1 (by simpa using hD)
      simp [this]
  have H0b : |∫ z, g z * deriv (κ y) z| ≤ K * Cκ * ε * (T2 * |y| ^ (1 - p - (p + 2))) := by
    have h := norm_integral_le_of_norm_le ((hJ2i.integrable_indicator hSm).const_mul (K * Cκ * ε))
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hgprod z _ _ (hpt4 y z hy).2.1)
    rw [integral_const_mul, integral_indicator hSm, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hJ2 (by positivity))
  have DHb : |∫ z, g z * deriv (fun y' => deriv (κ y') z) y| ≤
      K * Cκ * ε * (T3 * |y| ^ (1 - p - (p + 3))) := by
    have h := norm_integral_le_of_norm_le ((hJ3i.integrable_indicator hSm).const_mul (K * Cκ * ε))
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact hgprod z _ _ (hpt4 y z hy).2.2.2)
    rw [integral_const_mul, integral_indicator hSm, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hJ3 (by positivity))
  have hG1 : |deriv f y + 1| ≤ K * |y| ^ (-p - 1) := (hg1 y hy.le).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hY (c07_aux_abs_le_jb y)
      (by linarith)) hK0)
  have hG2 : |deriv (deriv f) y| ≤ K * |y| ^ (-p - 2) := (hg2 y hy.le).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hY (c07_aux_abs_le_jb y)
      (by linarith)) hK0)
  have pw : ∀ a b : ℝ, |y| ^ a * |y| ^ b = |y| ^ (a + b) := fun a b => (Real.rpow_add hY a b).symm
  have hyb : y ∈ s := Metric.mem_ball_self (by positivity)
  have hc0 := hc.le
  set F0 := ∫ z, κ y z with hF0
  set DF := ∫ z, deriv (fun y' => κ y' z) y with hDF
  set H0 := ∫ z, g z * deriv (κ y) z with hH0
  set DH := ∫ z, g z * deriv (fun y' => deriv (κ y') z) y with hDH
  have n1 := (abs_nonneg _).trans F0b
  have n2 := (abs_nonneg _).trans DFb
  refine ⟨hDI.differentiableAt, ?_, ?_⟩
  · rw [hIeq y hyb]
    calc |calpha p * (deriv f y + 1) * F0 + calpha p * H0|
        ≤ calpha p * (|deriv f y + 1| * |F0|) + calpha p * |H0| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hc]; ring
      _ ≤ calpha p * ((K * |y| ^ (-p - 1)) * (Cκ * ε * (T1 * |y| ^ (1 - (p + 1))))) +
          calpha p * (K * Cκ * ε * (T2 * |y| ^ (1 - p - (p + 2)))) := by
          gcongr
      _ = calpha p * K * Cκ * ε * (T1 * (|y| ^ (-p - 1) * |y| ^ (1 - (p + 1))) +
          T2 * |y| ^ (1 - p - (p + 2))) := by ring
      _ = _ := by
          rw [pw, show -p - 1 + (1 - (p + 1)) = -2 * p - 1 by ring,
            show 1 - p - (p + 2) = -2 * p - 1 by ring]; ring
  · have hd : deriv (c07_aux_negI2_I p ε f) y =
        calpha p * (deriv (deriv f) y * F0 + (deriv f y + 1) * DF + DH) := by
      rw [hDI.deriv]; ring
    rw [hd]
    calc |calpha p * (deriv (deriv f) y * F0 + (deriv f y + 1) * DF + DH)|
        ≤ calpha p * (|deriv (deriv f) y| * |F0| + |deriv f y + 1| * |DF| + |DH|) := by
          rw [abs_mul, abs_of_pos hc]
          refine mul_le_mul_of_nonneg_left ?_ hc0
          refine (abs_add_le _ _).trans ?_
          linarith [abs_add_le (deriv (deriv f) y * F0) ((deriv f y + 1) * DF),
            abs_mul (deriv (deriv f) y) F0, abs_mul (deriv f y + 1) DF]
      _ ≤ calpha p * ((K * |y| ^ (-p - 2)) * (Cκ * ε * (T1 * |y| ^ (1 - (p + 1)))) +
          (K * |y| ^ (-p - 1)) * (Cκ * ε * (T2 * |y| ^ (1 - (p + 2)))) +
          K * Cκ * ε * (T3 * |y| ^ (1 - p - (p + 3)))) := by
          gcongr
      _ = calpha p * K * Cκ * ε * (T1 * (|y| ^ (-p - 2) * |y| ^ (1 - (p + 1))) +
          T2 * (|y| ^ (-p - 1) * |y| ^ (1 - (p + 2))) + T3 * |y| ^ (1 - p - (p + 3))) := by ring
      _ = _ := by
          rw [pw, pw, show -p - 2 + (1 - (p + 1)) = -2 * p - 2 by ring,
            show -p - 1 + (1 - (p + 2)) = -2 * p - 2 by ring,
            show 1 - p - (p + 3) = -2 * p - 2 by ring]; ring

/-- Blueprint: lem:c07_negative_I2.  For `y ≤ -8R`: (1) the integration by parts formula
`𝓘₂(y) = c_α g'(y) ∫ κ(y,z) dz + c_α ∫ g(z) ∂_zκ(y,z) dz` (absolutely convergent);
(2) `|∂_y^j ∂_z^l κ(y,z)| ≤ Cε 𝟙_{|y-z| ≥ |y|/4} |y-z|^{-p-1-j-l}`, `j, l ∈ {0,1}`;
(3) `|∂^j 𝓘₂(y)| ≤ Cε|y|^{-2p-1-j}` (and `𝓘₂` is differentiable at `y`). -/
-- The conclusion includes `DifferentiableAt ℝ 𝓘ₖ y` (`y ≤ -8R`), so that the bound on
-- `iteratedDeriv 1` is a bound on the classical derivative; the bounds are summed in
-- prop:approx_residual_negative.
theorem c07_negative_I2 (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y ≤ -8 * R,
      (Integrable (fun z => c07_negative_I2_kappa P.p R ε μ y z) ∧
        Integrable (fun z => (approximate_solution_family P.p R ε μ z - corner z) *
          deriv (fun z' => c07_negative_I2_kappa P.p R ε μ y z') z) ∧
        c07_negative_Q_split_I2 P.p R ε μ y =
          calpha P.p * deriv (fun x => approximate_solution_family P.p R ε μ x - corner x) y *
              (∫ z, c07_negative_I2_kappa P.p R ε μ y z) +
            calpha P.p * ∫ z, (approximate_solution_family P.p R ε μ z - corner z) *
              deriv (fun z' => c07_negative_I2_kappa P.p R ε μ y z') z) ∧
      (∀ j ≤ 1, ∀ l ≤ 1, ∀ z : ℝ,
        |iteratedDeriv j (fun y' => iteratedDeriv l (fun z' =>
            c07_negative_I2_kappa P.p R ε μ y' z') z) y| ≤
          C * ε * Set.indicator {z' : ℝ | |y| / 4 ≤ |y - z'|}
            (fun z' => |y - z'| ^ (-P.p - 1 - j - l)) z) ∧
      (∀ j ≤ 1, |iteratedDeriv j (c07_negative_Q_split_I2 P.p R ε μ) y| ≤
        C * ε * |y| ^ (-2 * P.p - 1 - j)) ∧
      DifferentiableAt ℝ (c07_negative_Q_split_I2 P.p R ε μ) y := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  obtain ⟨R1, e1, hR1, he1, he11, hS⟩ := c07_family_smooth P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  obtain ⟨CA, hCA, hABall⟩ := c07_A_B_bounds P.p hp hp1
  obtain ⟨-, -, M, hM, hMb⟩ := c07_aux_negI2_chi
  obtain ⟨T1, hT1, hT1'⟩ := c07_tail_integrals P.p (P.p + 1) hp hp1 (by linarith)
  obtain ⟨T2, hT2, hT2'⟩ := c07_tail_integrals P.p (P.p + 2) hp hp1 (by linarith)
  obtain ⟨T3, hT3, hT3'⟩ := c07_tail_integrals P.p (P.p + 3) hp hp1 (by linarith)
  refine ⟨max R1 R2, min e1 e2, le_trans hR1 (le_max_left _ _), lt_min he1 he2,
    (min_le_left _ _).trans he11, fun R hR => ?_⟩
  obtain ⟨K₀, hK₀, hU'⟩ := hU R (le_trans (le_max_right _ _) hR)
  have hR0 : 1 ≤ R := le_trans hR1 (le_trans (le_max_left R1 R2) hR)
  have hc := c03_aux_calpha_pos P.p hp hp1
  set Cκ := 64 * (1 + 3 * M) * (CA + P.p + 1) * K₀ ^ 2 * ((P.p + 1) * (P.p + 2)) with hCκ
  have hCκ0 : 0 ≤ Cκ := by positivity
  set C2 := calpha P.p * K₀ * Cκ * (T1 + T2 + T3) with hC2
  have hC20 : 0 ≤ C2 := by have : (0:ℝ) ≤ K₀ := by linarith
                           positivity
  refine ⟨Cκ + C2 + 1, by positivity, fun ε hε μ hμ y hy => ?_⟩
  have hεa : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεb : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans he11⟩
  have hε0 := hε.1
  obtain ⟨hf, -⟩ := hS R (le_trans (le_max_left _ _) hR) ε hεa μ hμ
  obtain ⟨⟨-, hcl⟩, hg, hg3⟩ := hU' ε hεb μ hμ
  set f := approximate_solution_family P.p R ε μ with hfdef
  have hAB : ∀ u, |A_eps P.p ε u - 1| ≤ (P.p + 1) / 2 * ε * u ^ 2 ∧
      |deriv (A_eps P.p ε) u| ≤ (P.p + 1) * ε * |u| ∧
      |deriv (deriv (A_eps P.p ε)) u| ≤ CA * ε := fun u => by
    obtain ⟨a, b, c, -⟩ := (hABall ε hε1).1 u
    exact ⟨a, b, c⟩
  have hK : ∀ x, |deriv f x| ≤ K₀ := fun x => (hcl x).1
  have hg1 : ∀ z ≤ 0, |deriv f z + 1| ≤ K₀ * jb z ^ (-P.p - 1) := by
    intro z hz
    have := hg3 1 (by norm_num) z hz
    rw [iteratedDeriv_one, (c07_aux_iteratedDeriv_add_id f hf).1] at this
    simpa using this
  have hg2 : ∀ z ≤ 0, |deriv (deriv f) z| ≤ K₀ * jb z ^ (-P.p - 2) := by
    intro z hz
    have := hg3 2 (by norm_num) z hz
    rw [show (2 : ℕ) = 0 + 2 from rfl, (c07_aux_iteratedDeriv_add_id f hf).2 0,
      show (0 + 2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at this
    simpa using this
  have hy0 : y < 0 := by linarith
  have hY : |y| = -y := abs_of_neg hy0
  have hy2 : 2 ≤ |y| := by rw [hY]; linarith
  have hy1 : 1 ≤ |y| := by linarith
  obtain ⟨-, ⟨hS1i, hS1⟩, -, -⟩ := hT1' y hy1
  obtain ⟨⟨hJ2i, hJ2⟩, ⟨hS2i, hS2⟩, -, -⟩ := hT2' y hy1
  obtain ⟨⟨hJ3i, hJ3⟩, -, -, -⟩ := hT3' y hy1
  rw [show 1 - P.p - (P.p + 2) = 1 - P.p - (P.p + 2) from rfl] at hJ2
  have hK0 : 0 ≤ K₀ := by linarith
  have hgK : ∀ z, |f z - corner z| ≤ K₀ := fun z =>
    (hg z).trans (by
      have := c07_aux_jb_rpow_neg_le_one z P.p hp.le
      nlinarith)
  have hfor := c07_aux_negI2_formula P.p ε K₀ CA M hp hε0 hCA.le hAB hM hMb f (hf.of_le (by simp))
    hK hgK y hy0 hy1
  have hpt := fun z => c07_aux_negI2_pt P.p ε K₀ CA M hp hε0 hCA.le hAB hM hMb f
    (hf.of_le (by simp)) hK y z hy0
  obtain ⟨hdiff, hb0, hb1⟩ := c07_aux_negI2_main P.p ε K₀ CA M T1 T2 T3 hp hp1 hε0 hCA.le hAB hM
    hMb f hf hK₀ hK hg hg1 hg2 y hy0 hy2 hS1i hS1 hS2i hS2 hJ2i hJ2 hJ3i hJ3
  have hIe : c07_negative_Q_split_I2 P.p R ε μ = c07_aux_negI2_I P.p ε f := rfl
  have hκe : c07_negative_I2_kappa P.p R ε μ = c07_aux_negI2_kap P.p ε f := rfl
  rw [hIe, hκe]
  have hCl : Cκ ≤ Cκ + C2 + 1 := by linarith
  have hT12 : calpha P.p * K₀ * Cκ * (T1 + T2) ≤ Cκ + C2 + 1 := by
    have : calpha P.p * K₀ * Cκ * (T1 + T2) ≤ C2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hT123 : calpha P.p * K₀ * Cκ * (T1 + T2 + T3) ≤ Cκ + C2 + 1 := by linarith
  refine ⟨hfor, fun j hj l hl z => ?_, fun j hj => ?_, hdiff⟩
  · have h1 := (hpt z).2.2.2 j hj l hl
    have hX : 0 ≤ Set.indicator {z' : ℝ | |y| / 4 ≤ |y - z'|}
        (fun z' => |y - z'| ^ (-P.p - 1 - j - l)) z :=
      Set.indicator_nonneg (fun z' _ => Real.rpow_nonneg (abs_nonneg _) _) z
    have h2 : Cκ * ε * Set.indicator {z' : ℝ | |y| / 4 ≤ |y - z'|}
        (fun z' => |y - z'| ^ (-P.p - 1 - j - l)) z ≤
        (Cκ + C2 + 1) * ε * Set.indicator {z' : ℝ | |y| / 4 ≤ |y - z'|}
        (fun z' => |y - z'| ^ (-P.p - 1 - j - l)) z := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCl hε0) hX
    exact h1.trans h2
  · have hy0' : 0 < |y| := by linarith
    interval_cases j
    · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero]
      refine hb0.trans ?_
      have : 0 ≤ ε * |y| ^ (-2 * P.p - 1) := mul_nonneg hε0 (Real.rpow_nonneg hy0'.le _)
      calc _ = calpha P.p * K₀ * Cκ * (T1 + T2) * (ε * |y| ^ (-2 * P.p - 1)) := by ring
        _ ≤ (Cκ + C2 + 1) * (ε * |y| ^ (-2 * P.p - 1)) := mul_le_mul_of_nonneg_right hT12 this
        _ = _ := by ring
    · simp only [iteratedDeriv_one, Nat.cast_one]
      rw [show -2 * P.p - 1 - 1 = -2 * P.p - 2 by ring]
      refine hb1.trans ?_
      have : 0 ≤ ε * |y| ^ (-2 * P.p - 2) := mul_nonneg hε0 (Real.rpow_nonneg hy0'.le _)
      calc _ = calpha P.p * K₀ * Cκ * (T1 + T2 + T3) * (ε * |y| ^ (-2 * P.p - 2)) := by ring
        _ ≤ (Cκ + C2 + 1) * (ε * |y| ^ (-2 * P.p - 2)) := mul_le_mul_of_nonneg_right hT123 this
        _ = _ := by ring


/-- Lipschitz bounds for `A_ε` on `[-K,K]` and for `A_ε'`. -/
theorem c07_aux_A_lip (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ ε ∈ Icc (0:ℝ) 1, ∀ K : ℝ, 0 ≤ K → ∀ a b : ℝ, |a| ≤ K → |b| ≤ K →
      |A_eps p ε a - A_eps p ε b| ≤ (p + 1) * ε * K * |a - b| ∧
      |deriv (A_eps p ε) a - deriv (A_eps p ε) b| ≤ CA * ε * |a - b| ∧
      |deriv (A_eps p ε) a| ≤ (p + 1) * ε * K := by
  obtain ⟨C, hC, hAB⟩ := c07_A_B_bounds p hp hp1
  refine ⟨C, hC.le, fun ε hε K hK a b ha hb => ?_⟩
  have hpt := (hAB ε hε).1
  have hd : ∀ u, DifferentiableAt ℝ (A_eps p ε) u := fun u =>
    (c07_aux_A_hasDeriv p ε u hε.1).differentiableAt
  have hd2 : ∀ u, DifferentiableAt ℝ (deriv (A_eps p ε)) u := fun u =>
    (c07_aux_A_hasDeriv2 p ε u hε.1).differentiableAt
  have hpe : 0 ≤ (p + 1) * ε := by have := hε.1; positivity
  have hA' : ∀ x, |x| ≤ K → |deriv (A_eps p ε) x| ≤ (p + 1) * ε * K := fun x hx =>
    (hpt x).2.1.trans (mul_le_mul_of_nonneg_left hx hpe)
  refine ⟨?_, ?_, hA' a ha⟩
  · have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc (-K) K) (f := A_eps p ε)
      (C := (p + 1) * ε * K) (fun x _ => hd x)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hA' x (abs_le.2 ⟨hx.1, hx.2⟩))
      (convex_Icc _ _) (show b ∈ Icc (-K) K from abs_le.1 hb) (show a ∈ Icc (-K) K from abs_le.1 ha)
    simpa [Real.norm_eq_abs] using this
  · have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := deriv (A_eps p ε))
      (C := C * ε) (fun x _ => hd2 x)
      (fun x _ => by rw [Real.norm_eq_abs]; exact (hpt x).2.2.1)
      convex_univ (mem_univ b) (mem_univ a)
    simpa [Real.norm_eq_abs] using this

/-- The `y`-derivative of the integrand of `𝓘₃`. -/
def c07_aux_I3_dh (p ε : ℝ) (f : ℝ → ℝ) (y z : ℝ) : ℝ :=
  (deriv (A_eps p ε) (c01_secant f y z) * ((deriv f y - c01_secant f y z) / (y - z)) -
      deriv (A_eps p ε) (c01_secant corner y z) * ((deriv corner y - c01_secant corner y z) / (y - z))) *
      (z - y) ^ (-(p + 1)) +
    (A_eps p ε (c01_secant f y z) - A_eps p ε (c01_secant corner y z)) * ((p + 1) * (z - y) ^ (-(p + 2)))

/-- Pointwise facts for the integrand of `𝓘₃` (`y < 0 < z`). -/
theorem c07_aux_I3_pt (p ε K CA : ℝ) (hp : 0 < p) (hε : ε ∈ Icc (0 : ℝ) 1) (hK1 : 1 ≤ K)
    (hCA0 : 0 ≤ CA)
    (hlip : ∀ a b : ℝ, |a| ≤ K → |b| ≤ K →
      |A_eps p ε a - A_eps p ε b| ≤ (p + 1) * ε * K * |a - b| ∧
      |deriv (A_eps p ε) a - deriv (A_eps p ε) b| ≤ CA * ε * |a - b| ∧
      |deriv (A_eps p ε) a| ≤ (p + 1) * ε * K)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hK : ∀ z, |deriv f z| ≤ K)
    (hg : ∀ z, |f z - corner z| ≤ K * jb z ^ (-p))
    (hg' : ∀ z ≤ 0, |deriv f z + 1| ≤ K * jb z ^ (-p - 1)) (y z : ℝ) (hy : y < 0) (hz : 0 < z) :
    HasDerivAt (fun y' => (A_eps p ε (c01_secant f y' z) - A_eps p ε (c01_secant corner y' z)) *
      (z - y') ^ (-(p + 1))) (c07_aux_I3_dh p ε f y z) y ∧
    |(A_eps p ε (c01_secant f y z) - A_eps p ε (c01_secant corner y z)) * (z - y) ^ (-(p + 1))| ≤
      ε * ((p + 1) * K ^ 2) * ((|y| ^ (-p) + jb z ^ (-p)) * (z - y) ^ (-(p + 2))) ∧
    |c07_aux_I3_dh p ε f y z| ≤
      ε * ((p + 1) * K ^ 2 * (|y| ^ (-p - 1) * (z - y) ^ (-(p + 2))) +
        K * (2 * (p + 1) * K + 2 * CA + (p + 1) ^ 2 * K) *
          ((|y| ^ (-p) + jb z ^ (-p)) * (z - y) ^ (-(p + 3)))) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hyz : y ≠ z := by intro h; linarith
  have hD : 0 < z - y := by linarith
  have hY : 0 < |y| := abs_pos.2 hy.ne
  have hε0 := hε.1
  have hK0 : 0 ≤ K := by linarith
  set Sf := c01_secant f y z with hSf
  set SW := c01_secant corner y z with hSW
  have hcy : corner y = -y := by unfold corner; exact max_eq_left (by linarith)
  have hcz : corner z = 0 := by unfold corner; exact max_eq_right (by linarith)
  have hdcy : deriv corner y = -1 := by rw [c04_aux_deriv_corner y hy.ne]; simp [hy]
  -- secant facts
  have hSfK : |Sf| ≤ K := (c07_secant_calculus f hf K hK).1 y z hyz
  have hSW1 : |SW| ≤ 1 := c07_secant_calculus_W.1 y z hyz
  have hSWK : |SW| ≤ K := hSW1.trans hK1
  have hSWe : SW = -y / (y - z) := by
    simp only [hSW, c01_secant, hyz, ↓reduceIte, hcy, hcz, sub_zero]
  have hSg : Sf - SW = ((f y - corner y) - (f z - corner z)) / (y - z) := by
    simp only [hSf, hSW, c01_secant, hyz, ↓reduceIte]; ring
  have hyzabs : |y - z| = z - y := by rw [abs_sub_comm, abs_of_pos hD]
  have hjy : jb y ^ (-p) ≤ |y| ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hY (c07_aux_abs_le_jb y) (by linarith)
  have hjy1 : jb y ^ (-p - 1) ≤ |y| ^ (-p - 1) :=
    Real.rpow_le_rpow_of_nonpos hY (c07_aux_abs_le_jb y) (by linarith)
  set u := |y| ^ (-p) + jb z ^ (-p) with hu
  have hu0 : 0 ≤ u := by
    have := Real.rpow_nonneg hY.le (-p)
    have := Real.rpow_nonneg (show 0 ≤ jb z by linarith [c07_aux_one_le_jb z]) (-p)
    positivity
  have hSgb : |Sf - SW| ≤ K * u * (z - y)⁻¹ := by
    rw [hSg, abs_div, hyzabs, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hD.le)
    have h1 := abs_sub (f y - corner y) (f z - corner z)
    have h2 := hg y
    have h3 := hg z
    have : K * jb y ^ (-p) ≤ K * |y| ^ (-p) := mul_le_mul_of_nonneg_left hjy hK0
    rw [hu]; nlinarith
  obtain ⟨hl1, hl2, hl3⟩ := hlip Sf SW hSfK hSWK
  have hl4 := (hlip SW Sf hSWK hSfK).2.2
  -- rpow bookkeeping
  set X := (z - y) ^ (-(p + 1)) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg hD.le _
  have hI0 : 0 ≤ (z - y)⁻¹ := inv_nonneg.2 hD.le
  have hX2 : (z - y) ^ (-(p + 2)) = X * (z - y)⁻¹ := by
    rw [hX, show -(p + 2) = -(p + 1) - 1 by ring, Real.rpow_sub_one hD.ne', div_eq_mul_inv]
  have hX3 : (z - y) ^ (-(p + 3)) = X * (z - y)⁻¹ * (z - y)⁻¹ := by
    rw [hX, show -(p + 3) = -(p + 1) - 1 - 1 by ring, Real.rpow_sub_one hD.ne',
      Real.rpow_sub_one hD.ne', div_eq_mul_inv, div_eq_mul_inv]
  refine ⟨?_, ?_, ?_⟩
  · -- derivative
    have hS1 := c07_aux_secant_dy f y z hyz (hfd y)
    have hS2 := c07_aux_secant_dy corner y z hyz (c07_aux_corner_diff y hy.ne)
    have hdA : ∀ u, HasDerivAt (A_eps p ε) (deriv (A_eps p ε) u) u := fun u =>
      (c07_aux_A_hasDeriv p ε u hε0).differentiableAt.hasDerivAt
    have hA1 := (hdA Sf).comp y hS1
    have hA2 := (hdA SW).comp y hS2
    have hR := (Real.hasDerivAt_rpow_const (p := -(p + 1)) (Or.inl hD.ne')).comp y
      ((hasDerivAt_const y z).sub (hasDerivAt_id y))
    have := (hA1.sub hA2).mul hR
    convert this using 1
    · rfl
    · simp only [c07_aux_I3_dh, hSf, hSW, Function.comp_apply, id, Pi.sub_apply]
      rw [show -(p + 1) - 1 = -(p + 2) by ring]
      ring
  · rw [abs_mul, abs_of_nonneg hX0, hX2]
    calc |A_eps p ε Sf - A_eps p ε SW| * X ≤ ((p + 1) * ε * K * (K * u * (z - y)⁻¹)) * X := by
          gcongr; exact hl1.trans (mul_le_mul_of_nonneg_left hSgb (by positivity))
      _ = _ := by ring
  · have hfy := hg' y hy.le
    have hfy' : |deriv f y + 1| ≤ K * |y| ^ (-p - 1) := hfy.trans (mul_le_mul_of_nonneg_left hjy1 hK0)
    have hW2 : |deriv corner y - SW| ≤ 2 := by
      rw [hdcy]; have := abs_sub (-1) SW; simp at this; linarith
    -- rewrite the derivative numerator
    have hnum : deriv (A_eps p ε) Sf * ((deriv f y - Sf) / (y - z)) -
        deriv (A_eps p ε) SW * ((deriv corner y - SW) / (y - z)) =
        (deriv (A_eps p ε) Sf * ((deriv f y + 1) - (Sf - SW)) +
          (deriv (A_eps p ε) Sf - deriv (A_eps p ε) SW) * (deriv corner y - SW)) / (y - z) := by
      rw [hdcy]; field_simp; ring
    have hnb : |(deriv (A_eps p ε) Sf * ((deriv f y + 1) - (Sf - SW)) +
          (deriv (A_eps p ε) Sf - deriv (A_eps p ε) SW) * (deriv corner y - SW)) / (y - z)| ≤
        ((p + 1) * ε * K * (K * |y| ^ (-p - 1) + K * u * (z - y)⁻¹) +
          CA * ε * (K * u * (z - y)⁻¹) * 2) * (z - y)⁻¹ := by
      rw [abs_div, hyzabs, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ hI0
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have e1 : |deriv f y + 1 - (Sf - SW)| ≤ K * |y| ^ (-p - 1) + K * u * (z - y)⁻¹ := by
        have := abs_sub (deriv f y + 1) (Sf - SW); linarith
      have e2 : |deriv (A_eps p ε) Sf - deriv (A_eps p ε) SW| ≤ CA * ε * (K * u * (z - y)⁻¹) :=
        hl2.trans (mul_le_mul_of_nonneg_left hSgb (by positivity))
      gcongr
    have hAb : |A_eps p ε Sf - A_eps p ε SW| ≤ (p + 1) * ε * K * (K * u * (z - y)⁻¹) :=
      hl1.trans (mul_le_mul_of_nonneg_left hSgb (by positivity))
    simp only [c07_aux_I3_dh, ← hSf, ← hSW]
    rw [hnum]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hX0, abs_mul, abs_of_pos (by linarith : (0:ℝ) < p + 1),
      abs_of_nonneg (Real.rpow_nonneg hD.le _), hX2, hX3]
    have hy1 : 0 ≤ |y| ^ (-p - 1) := Real.rpow_nonneg hY.le _
    calc _ ≤ (((p + 1) * ε * K * (K * |y| ^ (-p - 1) + K * u * (z - y)⁻¹) +
            CA * ε * (K * u * (z - y)⁻¹) * 2) * (z - y)⁻¹) * X +
          ((p + 1) * ε * K * (K * u * (z - y)⁻¹)) * ((p + 1) * (X * (z - y)⁻¹)) := by
          gcongr
      _ = ε * ((p + 1) * K ^ 2 * (|y| ^ (-p - 1) * (X * (z - y)⁻¹)) +
            K * (2 * (p + 1) * K + 2 * CA + (p + 1) ^ 2 * K) * (u * (X * (z - y)⁻¹ * (z - y)⁻¹))) -
          ε * ((p + 1) * K * K * u * (z - y)⁻¹ * (z - y)⁻¹ * X) := by ring
      _ ≤ _ := by
          have : 0 ≤ ε * ((p + 1) * K * K * u * (z - y)⁻¹ * (z - y)⁻¹ * X) := by positivity
          linarith

/-- `∫₀^∞ (a+z)^{-q} dz ≤ T a^{1-q}` with the constant of `c07_aux_tail_three`. -/
theorem c07_aux_tail_pow (p q a : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 1 < q) (ha : 0 < a) :
    IntegrableOn (fun z => (a + z) ^ (-q)) (Ioi 0) ∧
    ∫ z in Ioi (0 : ℝ), (a + z) ^ (-q) ≤
      (1 + 1 / (1 - p) + 1 / (q - 1) + 1 / (p + q - 1)) * a ^ (1 - q) := by
  obtain ⟨h1, h2⟩ := c07_aux_tail_three p q a hp hp1 hq ha
  have hap : 0 < a ^ (-p) := Real.rpow_pos_of_pos ha _
  have hpt : ∀ z ∈ Ioi (0 : ℝ), (a + z) ^ (-q) ≤
      a ^ p * ((a ^ (-p) + jb z ^ (-p)) * (a + z) ^ (-q)) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    have e : a ^ p * a ^ (-p) = 1 := by rw [← Real.rpow_add ha]; simp
    have hj : 0 ≤ jb z ^ (-p) := Real.rpow_nonneg (by linarith [c07_aux_one_le_jb z]) _
    have hr : 0 ≤ (a + z) ^ (-q) := Real.rpow_nonneg (by linarith) _
    have happ : 0 ≤ a ^ p := (Real.rpow_pos_of_pos ha _).le
    calc (a + z) ^ (-q) = a ^ p * a ^ (-p) * (a + z) ^ (-q) := by rw [e, one_mul]
      _ ≤ _ := by nlinarith [mul_nonneg happ (mul_nonneg hj hr)]
  have hm : Measurable (fun z : ℝ => (a + z) ^ (-q)) := by fun_prop
  have hint : IntegrableOn (fun z => (a + z) ^ (-q)) (Ioi 0) :=
    (h1.const_mul (a ^ p)).mono' hm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [mem_Ioi.1 hz]) _)]
        exact hpt z hz))
  refine ⟨hint, ?_⟩
  calc ∫ z in Ioi (0 : ℝ), (a + z) ^ (-q)
      ≤ ∫ z in Ioi (0 : ℝ), a ^ p * ((a ^ (-p) + jb z ^ (-p)) * (a + z) ^ (-q)) :=
        setIntegral_mono_on hint (h1.const_mul _) measurableSet_Ioi hpt
    _ = a ^ p * ∫ z in Ioi (0 : ℝ), (a ^ (-p) + jb z ^ (-p)) * (a + z) ^ (-q) := integral_const_mul _ _
    _ ≤ a ^ p * ((1 + 1 / (1 - p) + 1 / (q - 1) + 1 / (p + q - 1)) * a ^ (1 - p - q)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos ha _).le
    _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add ha]; ring_nf

/-- Core of lem:c07_negative_I3 for a general profile `f`. -/
theorem c07_aux_I3_core (p ε K CA : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : ε ∈ Icc (0 : ℝ) 1)
    (hK1 : 1 ≤ K) (hCA0 : 0 ≤ CA)
    (hlip : ∀ a b : ℝ, |a| ≤ K → |b| ≤ K →
      |A_eps p ε a - A_eps p ε b| ≤ (p + 1) * ε * K * |a - b| ∧
      |deriv (A_eps p ε) a - deriv (A_eps p ε) b| ≤ CA * ε * |a - b| ∧
      |deriv (A_eps p ε) a| ≤ (p + 1) * ε * K)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hK : ∀ z, |deriv f z| ≤ K)
    (hg : ∀ z, |f z - corner z| ≤ K * jb z ^ (-p))
    (hg' : ∀ z ≤ 0, |deriv f z + 1| ≤ K * jb z ^ (-p - 1)) (y : ℝ) (hy : y < 0) :
    let I := fun y' => -calpha p * ∫ z in Ioi (0 : ℝ),
      (A_eps p ε (c01_secant f y' z) - A_eps p ε (c01_secant corner y' z)) / (z - y') ^ (p + 1)
    let T := fun q : ℝ => 1 + 1 / (1 - p) + 1 / (q - 1) + 1 / (p + q - 1)
    DifferentiableAt ℝ I y ∧
    |I y| ≤ calpha p * ((p + 1) * K ^ 2 * T (p + 2)) * ε * |y| ^ (-2 * p - 1) ∧
    |deriv I y| ≤ calpha p * ((p + 1) * K ^ 2 * T (p + 2) +
      K * (2 * (p + 1) * K + 2 * CA + (p + 1) ^ 2 * K) * T (p + 3)) * ε * |y| ^ (-2 * p - 2) := by
  intro I T
  have hc := c03_aux_calpha_pos p hp hp1
  have hε0 := hε.1
  have hY : 0 < |y| := abs_pos.2 hy.ne
  set M1 := (p + 1) * K ^ 2 with hM1
  set M2 := K * (2 * (p + 1) * K + 2 * CA + (p + 1) ^ 2 * K) with hM2
  have hM10 : 0 ≤ M1 := by positivity
  have hM20 : 0 ≤ M2 := by have : (0:ℝ) ≤ K := by linarith
                           positivity
  set H : ℝ → ℝ → ℝ := fun y' z => (A_eps p ε (c01_secant f y' z) -
    A_eps p ε (c01_secant corner y' z)) * (z - y') ^ (-(p + 1)) with hH
  have hfc : Continuous f := hf.continuous
  have hAc : Continuous (A_eps p ε) := c04_aux_A_cont p ε hε0
  have hcc : Continuous corner := by unfold corner; fun_prop
  have hmH : ∀ y', Measurable (H y') := fun y' => by
    have h1 := c07_aux_secant_meas f hfc y'
    have h2 := c07_aux_secant_meas corner hcc y'
    have h3 := hAc.measurable
    simp only [hH]; fun_prop
  have hmdH : ∀ y', Measurable (c07_aux_I3_dh p ε f y') := fun y' => by
    have h1 := c07_aux_secant_meas f hfc y'
    have h2 := c07_aux_secant_meas corner hcc y'
    have h3 := hAc.measurable
    have h4 : Measurable (deriv (A_eps p ε)) := measurable_deriv _
    unfold c07_aux_I3_dh; fun_prop
  have hrw : ∀ y' < 0, (∫ z in Ioi (0 : ℝ),
      (A_eps p ε (c01_secant f y' z) - A_eps p ε (c01_secant corner y' z)) / (z - y') ^ (p + 1)) =
      ∫ z in Ioi (0 : ℝ), H y' z := by
    intro y' hy'
    refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    simp only [hH]
    rw [Real.rpow_neg (by linarith [mem_Ioi.1 hz]), div_eq_mul_inv]
  have hev : I =ᶠ[𝓝 y] fun y' => -calpha p * ∫ z in Ioi (0 : ℝ), H y' z := by
    filter_upwards [Iio_mem_nhds hy] with y' hy'
    simp only [I]; rw [hrw y' hy']
  have hpt := fun y' (hy' : y' < 0) z (hz : 0 < z) =>
    c07_aux_I3_pt p ε K CA hp hε hK1 hCA0 hlip f hf hK hg hg' y' z hy' hz
  -- tail integrals at `a = |y|` and `b = |y|/2`
  have hyz : ∀ z, z - y = |y| + z := fun z => by rw [abs_of_neg hy]; ring
  obtain ⟨t2i, t2⟩ := c07_aux_tail_three p (p + 2) |y| hp hp1 (by linarith) hY
  obtain ⟨t3i, t3⟩ := c07_aux_tail_three p (p + 3) |y| hp hp1 (by linarith) hY
  obtain ⟨s2i, s2⟩ := c07_aux_tail_pow p (p + 2) |y| hp hp1 (by linarith) hY
  set b := |y| / 2 with hb
  have hb0 : 0 < b := by positivity
  obtain ⟨u3i, -⟩ := c07_aux_tail_three p (p + 3) b hp hp1 (by linarith) hb0
  obtain ⟨v2i, -⟩ := c07_aux_tail_pow p (p + 2) b hp hp1 (by linarith) hb0
  -- integrability of `H y`
  have hHb : ∀ z ∈ Ioi (0 : ℝ), ‖H y z‖ ≤
      ε * M1 * ((|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-(p + 2))) := by
    intro z hz
    have := (hpt y hy z hz).2.1
    rw [hyz] at this
    simpa [Real.norm_eq_abs, hH, hyz] using this
  have hHi : IntegrableOn (H y) (Ioi 0) :=
    (t2i.const_mul (ε * M1)).mono' (hmH y).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hHb))
  -- domination of the derivative on `ball y b`
  set bound : ℝ → ℝ := fun z => ε * (M1 * (b ^ (-p - 1) * (b + z) ^ (-(p + 2))) +
    M2 * ((b ^ (-p) + jb z ^ (-p)) * (b + z) ^ (-(p + 3)))) with hbound
  have hboundi : IntegrableOn bound (Ioi 0) :=
    (((v2i.const_mul (b ^ (-p - 1))).const_mul M1).add (u3i.const_mul M2)).const_mul ε
  have hball : ∀ y' ∈ Metric.ball y b, y' < 0 ∧ b ≤ |y'| := by
    intro y' hy'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy'
    have hb' : b = -y / 2 := by rw [hb, abs_of_neg hy]
    rw [hb'] at hy'
    have : y' < 0 := by linarith
    refine ⟨this, ?_⟩
    rw [abs_of_neg this, hb']; linarith
  have hdb : ∀ z ∈ Ioi (0 : ℝ), ∀ y' ∈ Metric.ball y b, ‖c07_aux_I3_dh p ε f y' z‖ ≤ bound z := by
    intro z hz y' hy'
    obtain ⟨hy'0, hby'⟩ := hball y' hy'
    have hz0 : (0:ℝ) < z := hz
    have hzy' : b + z ≤ z - y' := by
      have : |y'| = -y' := abs_of_neg hy'0
      linarith
    have k := (hpt y' hy'0 z hz).2.2
    rw [Real.norm_eq_abs]
    refine k.trans ?_
    simp only [hbound]
    have e1 : |y'| ^ (-p - 1) ≤ b ^ (-p - 1) := Real.rpow_le_rpow_of_nonpos hb0 hby' (by linarith)
    have e2 : |y'| ^ (-p) ≤ b ^ (-p) := Real.rpow_le_rpow_of_nonpos hb0 hby' (by linarith)
    have e3 : (z - y') ^ (-(p + 2)) ≤ (b + z) ^ (-(p + 2)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hzy' (by linarith)
    have e4 : (z - y') ^ (-(p + 3)) ≤ (b + z) ^ (-(p + 3)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hzy' (by linarith)
    have n1 : 0 ≤ (z - y') ^ (-(p + 2)) := Real.rpow_nonneg (by linarith) _
    have n2 : 0 ≤ (z - y') ^ (-(p + 3)) := Real.rpow_nonneg (by linarith) _
    have n3 : 0 ≤ |y'| ^ (-p - 1) := Real.rpow_nonneg (abs_nonneg _) _
    have n4 : 0 ≤ |y'| ^ (-p) + jb z ^ (-p) := by
      have := Real.rpow_nonneg (abs_nonneg y') (-p)
      have := Real.rpow_nonneg (show 0 ≤ jb z by linarith [c07_aux_one_le_jb z]) (-p)
      positivity
    have n5 : 0 ≤ b ^ (-p - 1) := Real.rpow_nonneg hb0.le _
    have f1 : |y'| ^ (-p - 1) * (z - y') ^ (-(p + 2)) ≤ b ^ (-p - 1) * (b + z) ^ (-(p + 2)) :=
      mul_le_mul e1 e3 n1 n5
    have f2 : (|y'| ^ (-p) + jb z ^ (-p)) * (z - y') ^ (-(p + 3)) ≤
        (b ^ (-p) + jb z ^ (-p)) * (b + z) ^ (-(p + 3)) :=
      mul_le_mul (by linarith) e4 n2 (by linarith)
    gcongr
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ))) (F := H) (F' := c07_aux_I3_dh p ε f) (x₀ := y)
    (bound := bound) (Metric.ball_mem_nhds y hb0)
    (Eventually.of_forall fun y' => (hmH y').aestronglyMeasurable) hHi
    (hmdH y).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun z hz y' hy' => hdb z hz y' hy'))
    hboundi
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun z hz y' hy' =>
      (hpt y' (hball y' hy').1 z hz).1))
  have hDI : HasDerivAt I (-calpha p * ∫ z in Ioi (0 : ℝ), c07_aux_I3_dh p ε f y z) y :=
    (hD.const_mul (-calpha p)).congr_of_eventuallyEq hev
  have hTpos : ∀ q, 1 < q → 0 ≤ T q := fun q hq => by
    simp only [T]
    have : 0 < 1 - p := by linarith
    have : 0 < q - 1 := by linarith
    have : 0 < p + q - 1 := by linarith
    positivity
  have hT2 := hTpos (p + 2) (by linarith)
  have hT3 := hTpos (p + 3) (by linarith)
  have pw : ∀ a b : ℝ, |y| ^ a * |y| ^ b = |y| ^ (a + b) := fun a b => (Real.rpow_add hY a b).symm
  refine ⟨hDI.differentiableAt, ?_, ?_⟩
  · simp only [I]
    rw [hrw y hy, abs_mul, abs_neg, abs_of_pos hc]
    have hb1 : |∫ z in Ioi (0 : ℝ), H y z| ≤
        ∫ z in Ioi (0 : ℝ), ε * M1 * ((|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-(p + 2))) := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le (t2i.const_mul _)
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hHb))
    rw [integral_const_mul] at hb1
    have : ε * M1 * ∫ z in Ioi (0 : ℝ), (|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-(p + 2)) ≤
        ε * M1 * (T (p + 2) * |y| ^ (1 - p - (p + 2))) :=
      mul_le_mul_of_nonneg_left t2 (by positivity)
    rw [show 1 - p - (p + 2) = -2 * p - 1 by ring] at this
    calc calpha p * |∫ z in Ioi (0 : ℝ), H y z| ≤ calpha p * (ε * M1 * (T (p + 2) * |y| ^ (-2 * p - 1))) :=
          mul_le_mul_of_nonneg_left (hb1.trans this) hc.le
      _ = _ := by ring
  · rw [hDI.deriv, abs_mul, abs_neg, abs_of_pos hc]
    have hdb' : ∀ z ∈ Ioi (0 : ℝ), ‖c07_aux_I3_dh p ε f y z‖ ≤
        ε * (M1 * |y| ^ (-p - 1)) * (|y| + z) ^ (-(p + 2)) +
          ε * M2 * ((|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-(p + 3))) := by
      intro z hz
      have k := (hpt y hy z hz).2.2
      rw [hyz] at k
      rw [Real.norm_eq_abs]; refine k.trans (le_of_eq ?_); ring
    have hi : IntegrableOn (fun z => ε * (M1 * |y| ^ (-p - 1)) * (|y| + z) ^ (-(p + 2)) +
          ε * M2 * ((|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-(p + 3)))) (Ioi 0) :=
      (s2i.const_mul _).add (t3i.const_mul _)
    have hb1 := norm_integral_le_of_norm_le hi
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hdb'))
    rw [integral_add (s2i.const_mul _) (t3i.const_mul _), integral_const_mul,
      integral_const_mul, Real.norm_eq_abs] at hb1
    have k1 : ε * (M1 * |y| ^ (-p - 1)) * ∫ z in Ioi (0 : ℝ), (|y| + z) ^ (-(p + 2)) ≤
        ε * (M1 * |y| ^ (-p - 1)) * (T (p + 2) * |y| ^ (1 - (p + 2))) :=
      mul_le_mul_of_nonneg_left s2 (by have := Real.rpow_nonneg hY.le (-p - 1); positivity)
    have k2 : ε * M2 * ∫ z in Ioi (0 : ℝ), (|y| ^ (-p) + jb z ^ (-p)) * (|y| + z) ^ (-(p + 3)) ≤
        ε * M2 * (T (p + 3) * |y| ^ (1 - p - (p + 3))) :=
      mul_le_mul_of_nonneg_left t3 (by positivity)
    have e1 : |y| ^ (-p - 1) * |y| ^ (1 - (p + 2)) = |y| ^ (-2 * p - 2) := by rw [pw]; ring_nf
    have e2 : 1 - p - (p + 3) = -2 * p - 2 := by ring
    rw [e2] at k2
    calc calpha p * |∫ z in Ioi (0 : ℝ), c07_aux_I3_dh p ε f y z|
        ≤ calpha p * (ε * (M1 * |y| ^ (-p - 1)) * (T (p + 2) * |y| ^ (1 - (p + 2))) +
            ε * M2 * (T (p + 3) * |y| ^ (-2 * p - 2))) :=
          mul_le_mul_of_nonneg_left (hb1.trans (add_le_add k1 k2)) hc.le
      _ = calpha p * (ε * M1 * T (p + 2) * (|y| ^ (-p - 1) * |y| ^ (1 - (p + 2))) +
            ε * M2 * (T (p + 3) * |y| ^ (-2 * p - 2))) := by ring
      _ = _ := by rw [e1]; ring

/-- Blueprint: lem:c07_negative_I3.  `|∂^j 𝓘₃(y)| ≤ Cε|y|^{-2p-1-j}` for `y ≤ -8R`,
`j ∈ {0,1}`. -/
-- The conclusion includes `DifferentiableAt ℝ 𝓘ₖ y` (`y ≤ -8R`), so that the bound on
-- `iteratedDeriv 1` is a bound on the classical derivative; the bounds are summed in
-- prop:approx_residual_negative.
theorem c07_negative_I3 (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y ≤ -8 * R,
      DifferentiableAt ℝ (c07_negative_Q_split_I3 P.p R ε μ) y ∧ ∀ j ≤ 1,
      |iteratedDeriv j (c07_negative_Q_split_I3 P.p R ε μ) y| ≤
        C * ε * |y| ^ (-2 * P.p - 1 - j) := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hp1 := P.hp_hi
  obtain ⟨R1, e1, hR1, he1, he11, hS⟩ := c07_family_smooth P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  obtain ⟨CA, hCA0, hlip⟩ := c07_aux_A_lip P.p hp hp1
  refine ⟨max R1 R2, min e1 e2, le_trans hR1 (le_max_left _ _), lt_min he1 he2,
    (min_le_left _ _).trans he11, fun R hR => ?_⟩
  obtain ⟨K₀, hK₀, hU'⟩ := hU R (le_trans (le_max_right _ _) hR)
  have hR0 : 0 < R := by linarith [le_trans hR1 (le_max_left R1 R2)]
  set T := fun q : ℝ => 1 + 1 / (1 - P.p) + 1 / (q - 1) + 1 / (P.p + q - 1) with hT
  have hTpos : ∀ q, 1 < q → 0 ≤ T q := fun q hq => by
    simp only [hT]
    have : 0 < 1 - P.p := by linarith
    have : 0 < q - 1 := by linarith
    have : 0 < P.p + q - 1 := by linarith
    positivity
  have hT2 := hTpos (P.p + 2) (by linarith)
  have hT3 := hTpos (P.p + 3) (by linarith)
  have hc := c03_aux_calpha_pos P.p hp hp1
  set C1 := calpha P.p * ((P.p + 1) * K₀ ^ 2 * T (P.p + 2)) with hC1
  set C2 := calpha P.p * ((P.p + 1) * K₀ ^ 2 * T (P.p + 2) +
      K₀ * (2 * (P.p + 1) * K₀ + 2 * CA + (P.p + 1) ^ 2 * K₀) * T (P.p + 3)) with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by have : (0:ℝ) ≤ K₀ := by linarith
                           positivity
  refine ⟨C1 + C2 + 1, by positivity, fun ε hε μ hμ y hy => ?_⟩
  have hεa : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hεb : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans he11⟩
  obtain ⟨hf, -⟩ := hS R (le_trans (le_max_left _ _) hR) ε hεa μ hμ
  obtain ⟨⟨-, hcl⟩, hg, hg3⟩ := hU' ε hεb μ hμ
  set f := approximate_solution_family P.p R ε μ with hfdef
  have hg' : ∀ z ≤ 0, |deriv f z + 1| ≤ K₀ * jb z ^ (-P.p - 1) := by
    intro z hz
    have := hg3 1 (by norm_num) z hz
    rw [iteratedDeriv_one, (c07_aux_iteratedDeriv_add_id f hf).1] at this
    simpa using this
  have hy0 : y < 0 := by linarith
  obtain ⟨hdiff, hb0, hb1⟩ := c07_aux_I3_core P.p ε K₀ CA hp hp1 hε1 hK₀ hCA0
    (fun a b ha hb => hlip ε hε1 K₀ (by linarith) a b ha hb) f (hf.of_le (by simp))
    (fun z => (hcl z).1) hg hg' y hy0
  have hI : c07_negative_Q_split_I3 P.p R ε μ = fun y' => -calpha P.p * ∫ z in Ioi (0 : ℝ),
      (A_eps P.p ε (c01_secant f y' z) - A_eps P.p ε (c01_secant corner y' z)) /
        (z - y') ^ (P.p + 1) := rfl
  rw [hI]
  refine ⟨hdiff, fun j hj => ?_⟩
  have hw : 0 ≤ ε * |y| ^ (-2 * P.p - 1 - j) := by have := hε.1; positivity
  interval_cases j
  · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, sub_zero]
    refine hb0.trans ?_
    have : 0 ≤ ε * |y| ^ (-2 * P.p - 1) := by have := hε.1; positivity
    nlinarith
  · simp only [iteratedDeriv_one, Nat.cast_one]
    rw [show -2 * P.p - 1 - 1 = -2 * P.p - 2 by ring]
    refine hb1.trans ?_
    have : 0 ≤ ε * |y| ^ (-2 * P.p - 2) := by have := hε.1; positivity
    nlinarith


/-! ### Residual bounds for `|y| ≤ 8R` -/

/-- Blueprint: lem:c07_compact_linear.
`‖f_osc‖_{L^∞} + ‖f_osc‖_{C³([-8R-1,8R+1])} ≤ Cε` and
`‖ℒ₀(f_slow)‖_{C¹([-8R,8R])} + ‖ℒ₀(f_osc)‖_{C¹([-8R,8R])} ≤ Cε` (written pointwise). -/
theorem c07_compact_linear (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
      (∀ y : ℝ, |fam_osc P.p R ε μ y| ≤ C * ε) ∧
      (∀ i ≤ 3, ∀ y ∈ Icc (-8 * R - 1) (8 * R + 1),
        |iteratedDeriv i (fam_osc P.p R ε μ) y| ≤ C * ε) ∧
      (∀ i ≤ 1, ∀ y ∈ Icc (-8 * R) (8 * R),
        |iteratedDeriv i (L0 P.p (fam_slow P.p R ε)) y| ≤ C * ε ∧
        |iteratedDeriv i (L0 P.p (fam_osc P.p R ε μ)) y| ≤ C * ε) := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨e1, ⟨he1, he11⟩, R1, hR1, hPD, -, -⟩ :=
    c07_ext_approx_phase_differences P.p P.hp_lo P.hp_hi δ hδ hδ'
  obtain ⟨R2, e2, hR2, he2, -, hS⟩ := c07_family_smooth P δ hδ hδ'
  obtain ⟨R3, e3, -, he3, -, hB⟩ := c07_slow_bounds P δ hδ hδ'
  obtain ⟨Cf, hCf, hLF⟩ := c07_local_fractional P.p hp P.hp_hi
  obtain ⟨D0, hD0, hd0⟩ := hPD 0
  obtain ⟨D1, hD1, hd1⟩ := hPD 1
  obtain ⟨D2, hD2, hd2⟩ := hPD 2
  obtain ⟨D3, hD3, hd3⟩ := hPD 3
  refine ⟨max R1 (max R2 (max R3 1)), min e1 (min e2 e3), by simp, by simp [*],
    (min_le_left _ _).trans he11, fun R hR => ?_⟩
  have hR1' : R1 ≤ R := le_trans (by simp) hR
  have hR2' : R2 ≤ R := le_trans (by simp) hR
  have hR3' : R3 ≤ R := le_trans (by simp) hR
  have hRone : 1 ≤ R := le_trans (by simp) hR
  obtain ⟨Cs, hCs, hB'⟩ := hB R hR3'
  set Dsum := D0 + D1 + D2 + D3 with hDsum
  set J := jb (8 * R + 1) ^ (3 / P.p) with hJ
  have hJ1 : 1 ≤ J := Real.one_le_rpow (c07_aux_one_le_jb _) (by positivity)
  set M := 8 * R with hM
  refine ⟨Dsum * J + 5 * Cf * (1 + M) * Cs + Cf * (1 + M) * (5 * Dsum * J), by positivity,
    fun ε hε μ hμ => ?_⟩
  have hε1 : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε3 : ε ∈ Icc (0 : ℝ) e3 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε0 := hε.1
  obtain ⟨-, -, hss, hos, hoz, -⟩ := hS R hR2' ε hε2 μ hμ
  -- pointwise bounds on `f_osc`
  have hosc : ∀ i ≤ 3, ∀ y, |iteratedDeriv i (fam_osc P.p R ε μ) y| ≤
      Dsum * ε * jb y ^ (-P.p - beta P.p + i / P.p) := by
    intro i hi y
    rcases lt_or_ge y R with hy | hy
    · have hev : fam_osc P.p R ε μ =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hy] with t ht using hoz t (le_of_lt ht)
      have h0 : iteratedDeriv i (fun _ : ℝ => (0 : ℝ)) y = 0 := by simp
      rw [hev.iteratedDeriv_eq, h0, abs_zero]
      exact mul_nonneg (mul_nonneg (by positivity) hε0)
        (Real.rpow_nonneg (by linarith [c07_aux_one_le_jb y]) _)
    · have key : ∀ (Dj : ℝ), 0 < Dj → Dj ≤ Dsum →
          |iteratedDeriv i (fam_osc P.p R ε μ) y| ≤
            Dj * min (ε * jb y ^ (-P.p - beta P.p + i / P.p))
              (jb y ^ (-beta P.p + ((i : ℝ) - 1) / P.p)) →
          |iteratedDeriv i (fam_osc P.p R ε μ) y| ≤
            Dsum * ε * jb y ^ (-P.p - beta P.p + i / P.p) := by
        intro Dj hDj hDjs h
        refine h.trans ?_
        have h1 := mul_le_mul_of_nonneg_left (min_le_left (ε * jb y ^ (-P.p - beta P.p + i / P.p))
          (jb y ^ (-beta P.p + ((i : ℝ) - 1) / P.p))) hDj.le
        have h2 : 0 ≤ ε * jb y ^ (-P.p - beta P.p + i / P.p) :=
          mul_nonneg hε0 (Real.rpow_nonneg (by linarith [c07_aux_one_le_jb y]) _)
        have h3 := mul_le_mul_of_nonneg_right hDjs h2
        nlinarith
      interval_cases i
      · exact key D0 hD0 (by linarith) (hd0 R hR1' ε hε1 μ hμ y hy).2.2.2
      · exact key D1 hD1 (by linarith) (hd1 R hR1' ε hε1 μ hμ y hy).2.2.2
      · exact key D2 hD2 (by linarith) (hd2 R hR1' ε hε1 μ hμ y hy).2.2.2
      · exact key D3 hD3 (by linarith) (hd3 R hR1' ε hε1 μ hμ y hy).2.2.2
  have hβ : 1 / P.p - P.p - beta P.p ≤ 0 := by
    unfold beta
    have h2p : 0 < 2 * P.p := by positivity
    have : 1 / P.p - P.p - (P.p + 1) / (2 * P.p) = (1 - P.p - 2 * P.p ^ 2) / (2 * P.p) := by
      field_simp; ring
    rw [this]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [P.hp_lo]) h2p.le
  have hβ0 : 0 < beta P.p := by unfold beta; positivity
  have hDs0 : 0 ≤ Dsum := by positivity
  have hjnn : ∀ y (s : ℝ), 0 ≤ jb y ^ s := fun y s =>
    Real.rpow_nonneg (by linarith [c07_aux_one_le_jb y]) s
  have hDe : 0 ≤ Dsum * ε := mul_nonneg hDs0 hε0
  have hosup : ∀ y, |fam_osc P.p R ε μ y| ≤ Dsum * ε := fun y => by
    have h := hosc 0 (by norm_num) y
    simp only [iteratedDeriv_zero, Nat.cast_zero, zero_div, add_zero] at h
    have : jb y ^ (-P.p - beta P.p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c07_aux_one_le_jb y) (by linarith)
    exact h.trans (mul_le_of_le_one_right hDe this)
  have hod : ∀ y, |deriv (fam_osc P.p R ε μ) y| ≤ Dsum * ε := fun y => by
    have h := hosc 1 (by norm_num) y
    simp only [iteratedDeriv_one, Nat.cast_one] at h
    have : jb y ^ (-P.p - beta P.p + 1 / P.p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c07_aux_one_le_jb y) (by linarith)
    exact h.trans (mul_le_of_le_one_right hDe this)
  have hocpt : ∀ i ≤ 3, ∀ y ∈ Icc (-(M + 1)) (M + 1),
      |iteratedDeriv i (fam_osc P.p R ε μ) y| ≤ Dsum * J * ε := by
    intro i hi y hy
    refine (hosc i hi y).trans ?_
    have hjy : jb y ≤ jb (8 * R + 1) := Real.sqrt_le_sqrt (by nlinarith [hy.1, hy.2])
    have hi' : (i : ℝ) / P.p ≤ 3 / P.p :=
      div_le_div_of_nonneg_right (by exact_mod_cast hi) hp.le
    have e1 : jb y ^ (-P.p - beta P.p + i / P.p) ≤ jb y ^ (3 / P.p) :=
      Real.rpow_le_rpow_of_exponent_le (c07_aux_one_le_jb y) (by linarith)
    have e2 : jb y ^ (3 / P.p) ≤ J :=
      Real.rpow_le_rpow (by linarith [c07_aux_one_le_jb y]) hjy (by positivity)
    have := mul_le_mul_of_nonneg_left (e1.trans e2) hDe
    linarith
  have hsl : ∀ i ≤ 3, ∀ y, |iteratedDeriv i (fam_slow P.p R ε) y| ≤ Cs * ε := fun i hi y => by
    have h := (hB' ε hε3).2.1 i hi y
    have : jb y ^ (-P.p - i) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (c07_aux_one_le_jb y)
        (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
    exact h.trans (mul_le_of_le_one_right (mul_nonneg hCs.le hε0) this)
  have hsl0 : ∀ y, |fam_slow P.p R ε y| ≤ Cs * ε := fun y => by
    simpa using hsl 0 (by norm_num) y
  have hsl1 : ∀ y, |deriv (fam_slow P.p R ε) y| ≤ Cs * ε := fun y => by
    simpa using hsl 1 (by norm_num) y
  have hCse : 0 ≤ Cs * ε := mul_nonneg hCs.le hε0
  have hCks : c07_CkNorm 3 (M + 1) (fam_slow P.p R ε) ≤ 4 * (Cs * ε) := by
    have := c07_aux_CkNorm_le 3 (M + 1) (Cs * ε) hCse _ (fun i hi y _ => hsl i hi y)
    norm_num at this ⊢; linarith
  have hsups : c07_supNorm (fam_slow P.p R ε) ≤ Cs * ε :=
    Real.sSup_le (by rintro _ ⟨y, rfl⟩; exact hsl0 y) hCse
  have hDJ : 0 ≤ Dsum * J * ε := by positivity
  have hCko : c07_CkNorm 3 (M + 1) (fam_osc P.p R ε μ) ≤ 4 * (Dsum * J * ε) := by
    have := c07_aux_CkNorm_le 3 (M + 1) (Dsum * J * ε) hDJ _ (fun i hi y hy => hocpt i hi y hy)
    norm_num at this ⊢; linarith
  have hsupo : c07_supNorm (fam_osc P.p R ε μ) ≤ Dsum * ε :=
    Real.sSup_le (by rintro _ ⟨y, rfl⟩; exact hosup y) hDe
  have hDJ' : Dsum * ε ≤ Dsum * J * ε := by nlinarith
  have hLs := hLF M (by linarith) _ (hss.of_le (by simp)) ⟨_, hsl0⟩ ⟨_, hsl1⟩
  have hLo := hLF M (by linarith) _ (hos.of_le (by simp)) ⟨_, hosup⟩ ⟨_, hod⟩
  have hA : 0 ≤ Cf * (1 + M) := by positivity
  have hCexp : (Dsum * J + 5 * Cf * (1 + M) * Cs + Cf * (1 + M) * (5 * Dsum * J)) * ε =
      Dsum * J * ε + Cf * (1 + M) * (5 * (Cs * ε)) + Cf * (1 + M) * (5 * (Dsum * J * ε)) := by
    ring
  have hn1 : 0 ≤ Cf * (1 + M) * (5 * (Cs * ε)) := mul_nonneg hA (by linarith)
  have hn2 : 0 ≤ Cf * (1 + M) * (5 * (Dsum * J * ε)) := mul_nonneg hA (by linarith)
  refine ⟨fun y => ?_, fun i hi y hy => ?_, fun i hi y hy => ⟨?_, ?_⟩⟩
  · refine (hosup y).trans ?_; rw [hCexp]; linarith
  · refine (hocpt i hi y ⟨by linarith [hy.1], by linarith [hy.2]⟩).trans ?_
    rw [hCexp]; linarith
  · refine ((hLs.2 i hi y ⟨by linarith [hy.1], hy.2⟩).2).trans ?_
    have := mul_le_mul_of_nonneg_left (show c07_CkNorm 3 (M + 1) (fam_slow P.p R ε) +
      c07_supNorm (fam_slow P.p R ε) ≤ 5 * (Cs * ε) by linarith) hA
    rw [hCexp]; linarith
  · refine ((hLo.2 i hi y ⟨by linarith [hy.1], hy.2⟩).2).trans ?_
    have := mul_le_mul_of_nonneg_left (show c07_CkNorm 3 (M + 1) (fam_osc P.p R ε μ) +
      c07_supNorm (fam_osc P.p R ε μ) ≤ 5 * (Dsum * J * ε) by linarith) hA
    rw [hCexp]; linarith

/-- Blueprint: lem:c07_compact_Q.  For every `M ≥ 1`:
`‖𝒬_ε(f̄_{ε,μ})‖_{C¹([-M,M])} ≤ C(M) ε` (written pointwise). -/
theorem c07_compact_Q (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R → ∀ M : ℝ, 1 ≤ M →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ i ≤ 1, ∀ y ∈ Icc (-M) M,
      |iteratedDeriv i (c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ)) y| ≤ C * ε := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨Ru, eu, hRu1, heu, heu1, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  obtain ⟨CA, hCA, hAB⟩ := c07_A_B_bounds P.p hp P.hp_hi
  refine ⟨Ru, eu, hRu1, heu, heu1, fun R hR M hM => ?_⟩
  obtain ⟨K₀, hK₀, hU'⟩ := hU R hR
  obtain ⟨Ck, hCk, hk⟩ := (c07_kernel_C1 P).2 K₀ hK₀ M hM
  refine ⟨Ck * (CA * K₀ ^ 2), by positivity, fun ε hε μ hμ i hi y hy => ?_⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans heu1⟩
  have hnorm := ((hAB ε hε1).2 K₀ hK₀).1
  have hn2 : 0 ≤ c07_kernel_operator_norm (deriv (A_eps P.p ε)) K₀ :=
    Real.sSup_nonneg (by rintro _ ⟨u, -, rfl⟩; positivity)
  have hb := hk _ (hU' ε hε μ hμ).1 (fun u => A_eps P.p ε u - 1)
    ((c07_aux_A_eps_contDiff P.p ε hε.1).sub contDiff_const) y hy
  have hle : Ck * c07_kernel_operator_norm (fun u => A_eps P.p ε u - 1) K₀ ≤
      Ck * (CA * K₀ ^ 2) * ε := by
    have := mul_le_mul_of_nonneg_left (show c07_kernel_operator_norm
      (fun u => A_eps P.p ε u - 1) K₀ ≤ CA * K₀ ^ 2 * ε by linarith) hCk.le
    linarith
  rw [c07_aux_Q_eq_kernel]
  interval_cases i
  · simp only [iteratedDeriv_zero]; exact hb.1.trans hle
  · simp only [iteratedDeriv_one]; exact hb.2.trans hle

/-- Blueprint: prop:approx_residual_negative.  For `y ≤ -8R`, `j ∈ {0,1}`:
`|∂^j(ℰ̃_ε(f̄_{ε,μ}) - G_μ)(y)| ≤ Cε⟨y⟩^{-2p-1-j}`, hence `≤ Cε⟨y⟩^{-γ-j}` for every
`γ ≤ 2p+1`. -/
theorem approx_residual_negative (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ, ∀ y ≤ -8 * R, ∀ j ≤ 1,
      |iteratedDeriv j (fun y' => c07_divided_residual P.p ε
          (approximate_solution_family P.p R ε μ) y' - G_mu P.p μ y') y| ≤
        C * ε * jb y ^ (-2 * P.p - 1 - j) ∧
      ∀ γ : ℝ, γ ≤ 2 * P.p + 1 →
        |iteratedDeriv j (fun y' => c07_divided_residual P.p ε
            (approximate_solution_family P.p R ε μ) y' - G_mu P.p μ y') y| ≤
          C * ε * jb y ^ (-γ - j) := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨Rs, es, -, hes, hes1, hSp⟩ := c07_residual_split P δ hδ hδ'
  obtain ⟨Rq, eq, -, heq, -, hQs⟩ := c07_negative_Q_split P δ hδ hδ'
  obtain ⟨R1, e1, -, he1, -, hS1⟩ := c07_negative_slow P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hO⟩ := c07_negative_osc P δ hδ hδ'
  obtain ⟨R3, e3, -, he3, -, hI1⟩ := c07_negative_I1 P δ hδ hδ'
  obtain ⟨R4, e4, -, he4, -, hI2⟩ := c07_negative_I2 P δ hδ hδ'
  obtain ⟨R5, e5, -, he5, -, hI3⟩ := c07_negative_I3 P δ hδ hδ'
  obtain ⟨Rl, el, -, hel, -, hL⟩ := c07_compact_linear P δ hδ hδ'
  obtain ⟨Rb, eb, -, heb, -, hB⟩ := c07_slow_bounds P δ hδ hδ'
  obtain ⟨Cf, -, hLF⟩ := c07_local_fractional P.p hp P.hp_hi
  refine ⟨max Rs (max Rq (max R1 (max R2 (max R3 (max R4 (max R5 (max Rl (max Rb 1)))))))),
    min es (min eq (min e1 (min e2 (min e3 (min e4 (min e5 (min el eb))))))),
    by simp, by simp [*], (min_le_left _ _).trans hes1, fun R hR => ?_⟩
  have hRs : Rs ≤ R := le_trans (by simp) hR
  have hRq : Rq ≤ R := le_trans (by simp) hR
  have hR1 : R1 ≤ R := le_trans (by simp) hR
  have hR2 : R2 ≤ R := le_trans (by simp) hR
  have hR3 : R3 ≤ R := le_trans (by simp) hR
  have hR4 : R4 ≤ R := le_trans (by simp) hR
  have hR5 : R5 ≤ R := le_trans (by simp) hR
  have hRl : Rl ≤ R := le_trans (by simp) hR
  have hRb : Rb ≤ R := le_trans (by simp) hR
  have hR1' : 1 ≤ R := le_trans (by simp) hR
  obtain ⟨C1, hC1, hS1'⟩ := hS1 R hR1
  obtain ⟨C2, hC2, hO'⟩ := hO R hR2
  obtain ⟨C3, hC3, hI1'⟩ := hI1 R hR3
  obtain ⟨C4, hC4, hI2'⟩ := hI2 R hR4
  obtain ⟨C5, hC5, hI3'⟩ := hI3 R hR5
  obtain ⟨Cl, hCl, hL'⟩ := hL R hRl
  obtain ⟨Cb, hCb, hB'⟩ := hB R hRb
  refine ⟨C1 + C2 + 16 * (C3 + C4 + C5), by positivity, fun ε hε μ hμ y hy j hj => ?_⟩
  have hεs : ε ∈ Icc (0 : ℝ) es := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεq : ε ∈ Icc (0 : ℝ) eq := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε3 : ε ∈ Icc (0 : ℝ) e3 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε4 : ε ∈ Icc (0 : ℝ) e4 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε5 : ε ∈ Icc (0 : ℝ) e5 := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεl : ε ∈ Icc (0 : ℝ) el := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεb : ε ∈ Icc (0 : ℝ) eb := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεone : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεs.2.trans hes1⟩
  have hy0 : y < 0 := by linarith
  have hy1 : 1 ≤ |y| := by rw [abs_of_neg hy0]; linarith
  -- regularity of the pieces
  obtain ⟨hreg, hid⟩ := hSp R hRs ε hεs μ hμ
  obtain ⟨hssm, Ls, hLs⟩ := hreg (fam_slow P.p R ε) (by simp)
  obtain ⟨hosm, Lo, hLo⟩ := hreg (fam_osc P.p R ε μ) (by simp)
  have hslow_sup : ∀ y, |fam_slow P.p R ε y| ≤ Cb * ε := by
    intro y
    have h := (hB' ε hεb).2.1 0 (Nat.zero_le _) y
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
    have h1 := c07_aux_jb_rpow_neg_le_one y P.p hp.le
    have h2 : 0 ≤ Cb * ε := mul_nonneg hCb.le hε.1
    nlinarith
  have hslowC : ContDiff ℝ 1 (L0 P.p (fam_slow P.p R ε)) :=
    c07_aux_L0_contDiff _ _ hssm
      (hLF 1 le_rfl _ (hssm.of_le (by simp)) ⟨Cb * ε, hslow_sup⟩ ⟨Ls, hLs⟩).1
  have hoscC : ContDiff ℝ 1 (L0 P.p (fam_osc P.p R ε μ)) :=
    c07_aux_L0_contDiff _ _ hosm
      (hLF 1 le_rfl _ (hosm.of_le (by simp)) ⟨Cl * ε, (hL' ε hεl μ hμ).1⟩ ⟨Lo, hLo⟩).1
  have hQWd : DifferentiableAt ℝ (c01_Q_eps P.p ε corner) y := by
    have hev : c01_Q_eps P.p ε corner =ᶠ[𝓝 y]
        fun y' => -(P.p + 1) * c_minus P.p ε * (-y') ^ (-P.p) := by
      filter_upwards [Iio_mem_nhds hy0] with y' hy'
      rw [(c07_QW_negative P ε hεone y' hy').2.2, abs_of_neg hy']
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    exact (DifferentiableAt.rpow_const (f := fun y' : ℝ => -y') (by fun_prop)
      (Or.inl (neg_ne_zero.2 hy0.ne))).const_mul _
  set E1 : ℝ → ℝ := fun y' => L0 P.p (fam_slow P.p R ε) y' + c01_Q_eps P.p ε corner y'
    with hE1
  have hE1d : DifferentiableAt ℝ E1 y := (hslowC.differentiable one_ne_zero y).add hQWd
  have hI1d := (hI1' ε hε3 μ hμ y hy).1
  have hI2d := (hI2' ε hε4 μ hμ y hy).2.2.2
  have hI3d := (hI3' ε hε5 μ hμ y hy).1
  have hev : (fun y' => c07_divided_residual P.p ε (approximate_solution_family P.p R ε μ) y' -
      G_mu P.p μ y') =ᶠ[𝓝 y] E1 + L0 P.p (fam_osc P.p R ε μ) + c07_negative_Q_split_I1 P.p R ε μ +
        c07_negative_Q_split_I2 P.p R ε μ + c07_negative_Q_split_I3 P.p R ε μ := by
    filter_upwards [Iio_mem_nhds hy0] with y' hy'
    have h1 := hid y'
    have h2 := (hQs R hRq ε hεq μ hμ y' hy').2.2.2
    simp only [Pi.add_apply, hE1]
    linarith
  have hd := (((hE1d.hasDerivAt.add (hoscC.differentiable one_ne_zero y).hasDerivAt).add
    hI1d.hasDerivAt).add hI2d.hasDerivAt).add hI3d.hasDerivAt
  have key : iteratedDeriv j (fun y' => c07_divided_residual P.p ε
      (approximate_solution_family P.p R ε μ) y' - G_mu P.p μ y') y =
      iteratedDeriv j E1 y + iteratedDeriv j (L0 P.p (fam_osc P.p R ε μ)) y +
        iteratedDeriv j (c07_negative_Q_split_I1 P.p R ε μ) y +
        iteratedDeriv j (c07_negative_Q_split_I2 P.p R ε μ) y +
        iteratedDeriv j (c07_negative_Q_split_I3 P.p R ε μ) y := by
    interval_cases j
    · simp only [iteratedDeriv_zero]; rw [hev.eq_of_nhds]; rfl
    · simp only [iteratedDeriv_one]; exact (hd.congr_of_eventuallyEq hev).deriv
  have b1 := (hS1' ε hε1 μ hμ y hy).2 j hj
  have b2 := ((hO' ε hε2 μ hμ y hy).2.2 j hj).2
  have b3 := (hI1' ε hε3 μ hμ y hy).2 j hj
  have b4 := (hI2' ε hε4 μ hμ y hy).2.2.1 j hj
  have b5 := (hI3' ε hε5 μ hμ y hy).2 j hj
  have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hyb := c07_aux_abs_rpow_le_jb y (-2 * P.p - 1 - j) hy1 (by linarith)
    (by linarith [P.hp_hi])
  have hε0 := hε.1
  have e3 : C3 * ε * |y| ^ (-2 * P.p - 1 - j) ≤ 16 * C3 * ε * jb y ^ (-2 * P.p - 1 - j) := by
    have := mul_le_mul_of_nonneg_left hyb (mul_nonneg hC3.le hε0)
    linarith
  have e4 : C4 * ε * |y| ^ (-2 * P.p - 1 - j) ≤ 16 * C4 * ε * jb y ^ (-2 * P.p - 1 - j) := by
    have := mul_le_mul_of_nonneg_left hyb (mul_nonneg hC4.le hε0)
    linarith
  have e5 : C5 * ε * |y| ^ (-2 * P.p - 1 - j) ≤ 16 * C5 * ε * jb y ^ (-2 * P.p - 1 - j) := by
    have := mul_le_mul_of_nonneg_left hyb (mul_nonneg hC5.le hε0)
    linarith
  have hmain : |iteratedDeriv j (fun y' => c07_divided_residual P.p ε
      (approximate_solution_family P.p R ε μ) y' - G_mu P.p μ y') y| ≤
      (C1 + C2 + 16 * (C3 + C4 + C5)) * ε * jb y ^ (-2 * P.p - 1 - j) := by
    rw [key]
    refine (c07_aux_abs_add5 _ _ _ _ _).trans ?_
    have : (C1 + C2 + 16 * (C3 + C4 + C5)) * ε * jb y ^ (-2 * P.p - 1 - j) =
        C1 * ε * jb y ^ (-2 * P.p - 1 - j) + C2 * ε * jb y ^ (-2 * P.p - 1 - j) +
        16 * C3 * ε * jb y ^ (-2 * P.p - 1 - j) + 16 * C4 * ε * jb y ^ (-2 * P.p - 1 - j) +
        16 * C5 * ε * jb y ^ (-2 * P.p - 1 - j) := by ring
    rw [this]
    linarith
  refine ⟨hmain, fun γ hγ => hmain.trans ?_⟩
  refine mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (c07_aux_one_le_jb y) (by linarith)) ?_
  positivity

/-- Blueprint: prop:approx_residual_compact.  `ℰ̃_ε(f̄_{ε,μ}) - G_μ ∈ C¹(ℝ)` and
`‖ℰ̃_ε(f̄_{ε,μ}) - G_μ‖_{C¹([-8R,8R])} ≤ Cε` (written pointwise). -/
theorem approx_residual_compact (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
      ContDiff ℝ 1 (fun y => c07_divided_residual P.p ε (approximate_solution_family P.p R ε μ) y -
        G_mu P.p μ y) ∧
      ∀ i ≤ 1, ∀ y ∈ Icc (-8 * R) (8 * R),
        |iteratedDeriv i (fun y' => c07_divided_residual P.p ε
          (approximate_solution_family P.p R ε μ) y' - G_mu P.p μ y') y| ≤ C * ε := by
  intro δ hδ hδ'
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨Rs, es, -, hes, hes1, hSp⟩ := c07_residual_split P δ hδ hδ'
  obtain ⟨Rl, el, -, hel, -, hL⟩ := c07_compact_linear P δ hδ hδ'
  obtain ⟨Rq, eq, -, heq, -, hQ⟩ := c07_compact_Q P δ hδ hδ'
  obtain ⟨Ru, eu, -, heu, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  obtain ⟨Rb, eb, -, heb, -, hB⟩ := c07_slow_bounds P δ hδ hδ'
  obtain ⟨Cf, -, hLF⟩ := c07_local_fractional P.p hp P.hp_hi
  have hkC1 := (c07_kernel_C1 P).1
  refine ⟨max Rs (max Rl (max Rq (max Ru (max Rb 1)))), min es (min el (min eq (min eu eb))),
    by simp, by simp [*], (min_le_left _ _).trans hes1, fun R hR => ?_⟩
  have hRs : Rs ≤ R := le_trans (by simp) hR
  have hRl : Rl ≤ R := le_trans (by simp) hR
  have hRq : Rq ≤ R := le_trans (by simp) hR
  have hRu : Ru ≤ R := le_trans (by simp) hR
  have hRb : Rb ≤ R := le_trans (by simp) hR
  have hR1 : 1 ≤ R := le_trans (by simp) hR
  obtain ⟨Cl, hCl, hL'⟩ := hL R hRl
  obtain ⟨Cq, hCq, hQ'⟩ := hQ R hRq (8 * R) (by linarith)
  obtain ⟨K₀, hK₀, hU'⟩ := hU R hRu
  obtain ⟨Cb, hCb, hB'⟩ := hB R hRb
  refine ⟨2 * Cl + Cq, by positivity, fun ε hε μ hμ => ?_⟩
  have hεs : ε ∈ Icc (0 : ℝ) es := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεl : ε ∈ Icc (0 : ℝ) el := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεq : ε ∈ Icc (0 : ℝ) eq := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεu : ε ∈ Icc (0 : ℝ) eu := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεb : ε ∈ Icc (0 : ℝ) eb := ⟨hε.1, hε.2.trans (by simp)⟩
  obtain ⟨hreg, hid⟩ := hSp R hRs ε hεs μ hμ
  obtain ⟨hssm, Ls, hLs⟩ := hreg (fam_slow P.p R ε) (by simp)
  obtain ⟨hosm, Lo, hLo⟩ := hreg (fam_osc P.p R ε μ) (by simp)
  obtain ⟨hosc_sup, -, hLbd⟩ := hL' ε hεl μ hμ
  have hslow_sup : ∀ y, |fam_slow P.p R ε y| ≤ Cb * ε := by
    intro y
    have h := (hB' ε hεb).2.1 0 (Nat.zero_le _) y
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h
    have h1 := c07_aux_jb_rpow_neg_le_one y P.p hp.le
    have h2 : 0 ≤ Cb * ε := mul_nonneg hCb.le hε.1
    nlinarith
  have hslowC : ContDiff ℝ 1 (L0 P.p (fam_slow P.p R ε)) :=
    c07_aux_L0_contDiff _ _ hssm
      (hLF 1 le_rfl _ (hssm.of_le (by simp)) ⟨Cb * ε, hslow_sup⟩ ⟨Ls, hLs⟩).1
  have hoscC : ContDiff ℝ 1 (L0 P.p (fam_osc P.p R ε μ)) :=
    c07_aux_L0_contDiff _ _ hosm
      (hLF 1 le_rfl _ (hosm.of_le (by simp)) ⟨Cl * ε, hosc_sup⟩ ⟨Lo, hLo⟩).1
  have hQC : ContDiff ℝ 1 (c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ)) := by
    rw [c07_aux_Q_eq_kernel]
    exact (hkC1 K₀ hK₀ _ (hU' ε hεu μ hμ).1 _
      ((c07_aux_A_eps_contDiff _ _ hε.1).sub contDiff_const)).2.1
  have hfun : (fun y => c07_divided_residual P.p ε (approximate_solution_family P.p R ε μ) y -
      G_mu P.p μ y) = fun y => L0 P.p (fam_slow P.p R ε) y + L0 P.p (fam_osc P.p R ε μ) y +
        c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ) y := funext hid
  refine ⟨by rw [hfun]; exact (hslowC.add hoscC).add hQC, fun i hi y hy => ?_⟩
  rw [hfun]
  have hs := (hLbd i hi y hy).1
  have ho := (hLbd i hi y hy).2
  have hq := hQ' ε hεq μ hμ i hi y ⟨by linarith [hy.1], hy.2⟩
  interval_cases i
  · simp only [iteratedDeriv_zero] at hs ho hq ⊢
    have := abs_add_three (L0 P.p (fam_slow P.p R ε) y) (L0 P.p (fam_osc P.p R ε μ) y)
      (c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ) y)
    linarith
  · simp only [iteratedDeriv_one] at hs ho hq ⊢
    rw [show (fun y => L0 P.p (fam_slow P.p R ε) y + L0 P.p (fam_osc P.p R ε μ) y +
        c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ) y) =
        L0 P.p (fam_slow P.p R ε) + L0 P.p (fam_osc P.p R ε μ) +
        c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ) from rfl,
      (((hslowC.differentiable one_ne_zero y).hasDerivAt.add
      (hoscC.differentiable one_ne_zero y).hasDerivAt).add
      (hQC.differentiable one_ne_zero y).hasDerivAt).deriv]
    have := abs_add_three (deriv (L0 P.p (fam_slow P.p R ε)) y)
      (deriv (L0 P.p (fam_osc P.p R ε μ)) y)
      (deriv (c01_Q_eps P.p ε (approximate_solution_family P.p R ε μ)) y)
    linarith

/-! ### Assembly -/

/-- Blueprint: lem:c07_Y_gamma_patching.  If `H ∈ C¹` satisfies `|H^{(j)}(y)| ≤ a⟨y⟩^{-γ+j/p}`
for `y ≥ ρ`, `|H^{(j)}(y)| ≤ a⟨y⟩^{-γ-j}` for `y ≤ -ρ` (`j = 0,1`) and
`‖H‖_{C¹([-ρ,ρ])} ≤ b`, then `H ∈ Y_γ` and `‖H‖_{Y_γ} ≤ 4a + 4⟨ρ⟩^{γ+1} b`. -/
theorem c07_Y_gamma_patching (p : ℝ) (hp : 0 < p) (γ ρ a b : ℝ) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (H : ℝ → ℝ) (hH : ContDiff ℝ 1 H)
    (hpos : ∀ j ≤ 1, ∀ y : ℝ, ρ ≤ y → |iteratedDeriv j H y| ≤ a * jb y ^ (-γ + j / p))
    (hneg : ∀ j ≤ 1, ∀ y : ℝ, y ≤ -ρ → |iteratedDeriv j H y| ≤ a * jb y ^ (-γ - j))
    (hcpt : c07_CkNorm 1 ρ H ≤ b) :
    H ∈ Y_gamma p γ ∧ Y_gamma_norm p γ H ≤ ENNReal.ofReal (4 * a + 4 * jb ρ ^ (γ + 1) * b) := by
  have hjb : ∀ y, 0 < jb y := fun y => lt_of_lt_of_le one_pos (c07_aux_one_le_jb y)
  have hmul : ∀ y (s t : ℝ), jb y ^ s * jb y ^ t = jb y ^ (s + t) :=
    fun y s t => (Real.rpow_add (hjb y) s t).symm
  have hnn : ∀ y (s : ℝ), 0 ≤ jb y ^ s := fun y s => Real.rpow_nonneg (hjb y).le s
  have hP0 : ∀ y, ρ ≤ y → |H y| ≤ a * jb y ^ (-γ) := fun y hy => by
    simpa using hpos 0 (Nat.zero_le _) y hy
  have hP1 : ∀ y, ρ ≤ y → |deriv H y| ≤ a * jb y ^ (-γ + 1 / p) := fun y hy => by
    simpa using hpos 1 le_rfl y hy
  have hN0 : ∀ y, y ≤ -ρ → |H y| ≤ a * jb y ^ (-γ) := fun y hy => by
    simpa using hneg 0 (Nat.zero_le _) y hy
  have hN1 : ∀ y, y ≤ -ρ → |deriv H y| ≤ a * jb y ^ (-γ - 1) := fun y hy => by
    simpa using hneg 1 le_rfl y hy
  have hc : ∀ y ∈ Icc (-ρ) ρ, |H y| ≤ b ∧ |deriv H y| ≤ b := by
    intro y hy
    have hcont0 : Continuous H := hH.continuous
    have hcont1 : Continuous (deriv H) := hH.continuous_deriv le_rfl
    have hs : c07_CkNorm 1 ρ H = sSup ((fun y => |H y|) '' Icc (-ρ) ρ) +
        sSup ((fun y => |deriv H y|) '' Icc (-ρ) ρ) := by
      simp [c07_CkNorm, Finset.sum_range_succ]
    have hb0 : BddAbove ((fun y => |H y|) '' Icc (-ρ) ρ) :=
      isCompact_Icc.bddAbove_image (continuous_abs.comp hcont0).continuousOn
    have hb1 : BddAbove ((fun y => |deriv H y|) '' Icc (-ρ) ρ) :=
      isCompact_Icc.bddAbove_image (continuous_abs.comp hcont1).continuousOn
    have hn0 : 0 ≤ sSup ((fun y => |H y|) '' Icc (-ρ) ρ) :=
      Real.sSup_nonneg (by rintro _ ⟨_, _, rfl⟩; exact abs_nonneg _)
    have hn1 : 0 ≤ sSup ((fun y => |deriv H y|) '' Icc (-ρ) ρ) :=
      Real.sSup_nonneg (by rintro _ ⟨_, _, rfl⟩; exact abs_nonneg _)
    have h0 : |H y| ≤ sSup ((fun y => |H y|) '' Icc (-ρ) ρ) := le_csSup hb0 ⟨y, hy, rfl⟩
    have h1 : |deriv H y| ≤ sSup ((fun y => |deriv H y|) '' Icc (-ρ) ρ) :=
      le_csSup hb1 ⟨y, hy, rfl⟩
    constructor <;> linarith
  have hjbρ : ∀ y ∈ Icc (-ρ) ρ, jb y ≤ jb ρ := fun y hy =>
    Real.sqrt_le_sqrt (by nlinarith [hy.1, hy.2])
  have hρ1 : 1 ≤ jb ρ := c07_aux_one_le_jb ρ
  have hJγ : ∀ y ∈ Icc (-ρ) ρ, jb y ^ γ ≤ jb ρ ^ γ := fun y hy =>
    Real.rpow_le_rpow (hjb y).le (hjbρ y hy) hγ.le
  have hJγ1 : jb ρ ^ γ ≤ jb ρ ^ (γ + 1) := Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith)
  have hJ : jb ρ ^ (γ + 1) = jb ρ ^ γ * jb ρ := by rw [Real.rpow_add (hjb ρ), Real.rpow_one]
  have hJb : 0 ≤ jb ρ ^ (γ + 1) * b := mul_nonneg (hnn ρ _) hb
  have hpos_bd : ∀ y, 0 ≤ y → jb y ^ γ * (‖H y‖ + jb y ^ (-1 / p) * ‖deriv H y‖) ≤
      2 * a + 2 * jb ρ ^ (γ + 1) * b := by
    intro y hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total ρ y with hy | hy
    · have e1 : jb y ^ γ * (a * jb y ^ (-γ)) = a := by
        rw [mul_left_comm, hmul, add_neg_cancel, Real.rpow_zero, mul_one]
      have e2 : jb y ^ γ * (jb y ^ (-1 / p) * (a * jb y ^ (-γ + 1 / p))) = a := by
        have : jb y ^ γ * (jb y ^ (-1 / p) * (a * jb y ^ (-γ + 1 / p))) =
            a * (jb y ^ γ * jb y ^ (-1 / p) * jb y ^ (-γ + 1 / p)) := by ring
        rw [this, hmul, hmul, show γ + -1 / p + (-γ + 1 / p) = 0 by ring, Real.rpow_zero, mul_one]
      calc jb y ^ γ * (|H y| + jb y ^ (-1 / p) * |deriv H y|)
          = jb y ^ γ * |H y| + jb y ^ γ * (jb y ^ (-1 / p) * |deriv H y|) := by ring
        _ ≤ jb y ^ γ * (a * jb y ^ (-γ)) +
            jb y ^ γ * (jb y ^ (-1 / p) * (a * jb y ^ (-γ + 1 / p))) :=
          add_le_add (mul_le_mul_of_nonneg_left (hP0 y hy) (hnn y _))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hP1 y hy) (hnn y _))
              (hnn y _))
        _ ≤ 2 * a + 2 * jb ρ ^ (γ + 1) * b := by rw [e1, e2]; linarith
    · obtain ⟨c0, c1⟩ := hc y ⟨by linarith, hy⟩
      have hw : jb y ^ (-1 / p) ≤ 1 := by
        rw [show -1 / p = -(1 / p) by ring]
        exact c07_aux_jb_rpow_neg_le_one y _ (by positivity)
      have t1 : |H y| + jb y ^ (-1 / p) * |deriv H y| ≤ 2 * b := by
        have := mul_le_mul hw c1 (abs_nonneg _) zero_le_one
        linarith
      calc jb y ^ γ * (|H y| + jb y ^ (-1 / p) * |deriv H y|) ≤ jb ρ ^ γ * (2 * b) :=
            mul_le_mul (hJγ y ⟨by linarith, hy⟩) t1
              (add_nonneg (abs_nonneg _) (mul_nonneg (hnn y _) (abs_nonneg _))) (hnn ρ _)
        _ ≤ jb ρ ^ (γ + 1) * (2 * b) := mul_le_mul_of_nonneg_right hJγ1 (by linarith)
        _ ≤ 2 * a + 2 * jb ρ ^ (γ + 1) * b := by linarith
  have hneg_bd : ∀ y, y ≤ 0 → jb y ^ γ * (‖H y‖ + jb y * ‖deriv H y‖) ≤
      2 * a + 2 * jb ρ ^ (γ + 1) * b := by
    intro y hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total y (-ρ) with hy | hy
    · have e1 : jb y ^ γ * (a * jb y ^ (-γ)) = a := by
        rw [mul_left_comm, hmul, add_neg_cancel, Real.rpow_zero, mul_one]
      have e2 : jb y ^ γ * (jb y * (a * jb y ^ (-γ - 1))) = a := by
        have : jb y ^ γ * (jb y * (a * jb y ^ (-γ - 1))) =
            a * (jb y ^ γ * jb y ^ (1 : ℝ) * jb y ^ (-γ - 1)) := by rw [Real.rpow_one]; ring
        rw [this, hmul, hmul, show γ + 1 + (-γ - 1) = 0 by ring, Real.rpow_zero, mul_one]
      calc jb y ^ γ * (|H y| + jb y * |deriv H y|)
          = jb y ^ γ * |H y| + jb y ^ γ * (jb y * |deriv H y|) := by ring
        _ ≤ jb y ^ γ * (a * jb y ^ (-γ)) + jb y ^ γ * (jb y * (a * jb y ^ (-γ - 1))) :=
          add_le_add (mul_le_mul_of_nonneg_left (hN0 y hy) (hnn y _))
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hN1 y hy) (hjb y).le)
              (hnn y _))
        _ ≤ 2 * a + 2 * jb ρ ^ (γ + 1) * b := by rw [e1, e2]; linarith
    · have hyI : y ∈ Icc (-ρ) ρ := ⟨hy, by linarith⟩
      obtain ⟨c0, c1⟩ := hc y hyI
      have t1 : |H y| + jb y * |deriv H y| ≤ b + jb ρ * b := by
        have := mul_le_mul (hjbρ y hyI) c1 (abs_nonneg _) (by linarith)
        linarith
      have t2 : jb ρ ^ γ * (b + jb ρ * b) ≤ 2 * jb ρ ^ (γ + 1) * b := by
        have : jb ρ ^ γ * b ≤ jb ρ ^ (γ + 1) * b := mul_le_mul_of_nonneg_right hJγ1 hb
        nlinarith
      calc jb y ^ γ * (|H y| + jb y * |deriv H y|) ≤ jb ρ ^ γ * (b + jb ρ * b) :=
            mul_le_mul (hJγ y hyI) t1
              (add_nonneg (abs_nonneg _) (mul_nonneg (hjb y).le (abs_nonneg _))) (hnn ρ _)
        _ ≤ 2 * a + 2 * jb ρ ^ (γ + 1) * b := by linarith
  have key : Y_gamma_norm p γ H ≤ ENNReal.ofReal (2 * a + 2 * jb ρ ^ (γ + 1) * b) +
      ENNReal.ofReal (2 * a + 2 * jb ρ ^ (γ + 1) * b) := by
    unfold Y_gamma_norm
    gcongr
    · exact essSup_le_of_ae_le _ (ae_restrict_of_forall_mem measurableSet_Ici
        fun y hy => ENNReal.ofReal_le_ofReal (hpos_bd y hy))
    · exact essSup_le_of_ae_le _ (ae_restrict_of_forall_mem measurableSet_Iic
        fun y hy => ENNReal.ofReal_le_ofReal (hneg_bd y hy))
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)] at key
  have key' : Y_gamma_norm p γ H ≤ ENNReal.ofReal (4 * a + 4 * jb ρ ^ (γ + 1) * b) :=
    key.trans (le_of_eq (by ring_nf))
  exact ⟨⟨hH.locallyLipschitz, lt_of_le_of_lt key' ENNReal.ofReal_lt_top⟩, key'⟩

/-! ### prop:approx_residual_positive (blueprint chapter 04)

Stated here rather than in `GSQG/Sec5_ApproximateSolution/FamilyAndE1toE4.lean` because its proof needs the bounds on `ℰ₅`–`ℰ₉`
(chapters 05 and 06, which import chapter 04); this file imports chapters 05 and 06 for it. -/

/-! ### Helpers for approx_residual_positive -/
/-- Helper: the smallness thresholds `ε₀*(δ)` of chapters 05 and 06 are positive. -/
theorem c07_aux_eps0_pos (P : parameters) (δ : ℝ) (hδ : 0 < δ) (hδμ : δ ≤ ‖mu_star P.p‖ / 2) :
    0 < c06_eps0_star P δ ∧ 0 < c05_eps0_star P.p δ := by
  constructor
  · unfold c06_eps0_star
    rw [dif_pos ⟨hδ, hδμ⟩]
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))
    · exact (Classical.choose_spec (approx_profile_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_family_regions P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_primitive P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
  · unfold c05_eps0_star
    rw [dif_pos ⟨P.hp_lo, P.hp_hi, hδ, hδμ⟩]
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))))))
    · exact (Classical.choose_spec (c04_lambda_psi_difference P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_bounds P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_difference_products P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_difference P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_lambda_taylor P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_primitive P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec
        (c04_phase_exponential_difference P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (approx_phase_differences P.p P.hp_lo P.hp_hi δ hδ hδμ)).1.1

/-- Helper: `∂^j(f+g) = ∂^j f + ∂^j g` for `j ≤ 1` at a point where both are differentiable. -/
theorem c07_aux_iter_add {f g : ℝ → ℝ} {y : ℝ} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) {j : ℕ} (hj : j ≤ 1) :
    iteratedDeriv j (fun t => f t + g t) y = iteratedDeriv j f y + iteratedDeriv j g y := by
  interval_cases j
  · simp
  · simp only [iteratedDeriv_one]; exact deriv_add hf hg

/-- Helper: `‖z‖² = (Re z)² + (Im z)²` as functions. -/
theorem c07_aux_locC1_normsq (Z : ℝ → ℂ) :
    (fun y => ‖Z y‖ ^ 2) = fun y => (Z y).re * (Z y).re + (Z y).im * (Z y).im := by
  funext y; rw [Complex.sq_norm, Complex.normSq_apply]

/-- Helper: `ℰ₂, ℰ₃, ℰ₄` are `C¹` on `(R,∞)`. -/
theorem c07_aux_residual_local_C1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
      ContDiffOn ℝ 1 (residual_decomposition_E2 p R ε μ) (Ioi R) ∧
      ContDiffOn ℝ 1 (residual_decomposition_E3 p R ε μ) (Ioi R) ∧
      ContDiffOn ℝ 1 (residual_decomposition_E4 p R ε μ) (Ioi R) := by
  intro δ hδ hδμ
  obtain ⟨ε₁, hε₁, R₁, hR₁, H1⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hbasic, -, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  refine ⟨min ε₁ ε₂, ⟨lt_min hε₁.1 hε₂.1, (min_le_left _ _).trans hε₁.2⟩, max R₁ R₂,
    le_trans hR₁ (le_max_left _ _), fun R hR ε hε μ hμ => ?_⟩
  have hRa : R ≥ R₁ := le_trans (le_max_left _ _) hR
  have hRb : R ≥ R₂ := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hZ := (H1 R hRa ε hε1 μ hμ).1
  -- pointwise `C¹` at `y > R`
  have key : ∀ y, R < y →
      ContDiffAt ℝ 1 (fun t => (fam_Z p R ε μ t).re) y ∧
      ContDiffAt ℝ 1 (fun t => (fam_Z p R ε μ t ^ 3).re) y ∧
      ContDiffAt ℝ 1 (fun t => ‖fam_Z p R ε μ t‖ ^ 2) y ∧
      ContDiffAt ℝ 1 (fun t => fam_lambda p ε μ t ^ p) y ∧
      ContDiffAt ℝ 1 (fun t => lambda0 p t ^ (p - 1)) y ∧
      ContDiffAt ℝ 1 (fun t => t ^ (-p)) y := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hZy : ContDiffAt ℝ 1 (fam_Z p R ε μ) y :=
      ((hZ.contDiffAt (Ioi_mem_nhds (by linarith : R / 2 < y))).of_le
        (WithTop.coe_le_coe.mpr le_top))
    obtain ⟨g1, g2, -, -⟩ := hbasic R hRb ε hε2 μ hμ y (by linarith)
    have hlam := (c04_aux_lam_pos p ε μ y hy0 g1 g2).1
    have hre : ContDiffAt ℝ 1 (fun z : ℂ => z.re) (fam_Z p R ε μ y) :=
      Complex.reCLM.contDiff.contDiffAt
    have him : ContDiffAt ℝ 1 (fun z : ℂ => z.im) (fam_Z p R ε μ y) :=
      Complex.imCLM.contDiff.contDiffAt
    have hZre : ContDiffAt ℝ 1 (fun t => (fam_Z p R ε μ t).re) y := hre.comp y hZy
    have hZim : ContDiffAt ℝ 1 (fun t => (fam_Z p R ε μ t).im) y := him.comp y hZy
    have hl : ContDiffAt ℝ 1 (fam_lambda p ε μ) y :=
      (c04_aux_lambda_contDiffOn p ε μ 1).contDiffAt (Ioi_mem_nhds hy0)
    refine ⟨hZre, ?_, ?_, hl.rpow_const_of_ne hlam.ne', ?_, contDiffAt_rpow_const_of_ne hy0.ne'⟩
    · have h3 : ContDiffAt ℝ 1 (fun z : ℂ => (z ^ 3).re) (fam_Z p R ε μ y) :=
        Complex.reCLM.contDiff.contDiffAt.comp _ (contDiffAt_id.pow 3)
      exact h3.comp y hZy
    · rw [c07_aux_locC1_normsq]
      exact (hZre.mul hZre).add (hZim.mul hZim)
    · have h0 : ContDiffAt ℝ 1 (lambda0 p) y := by
        unfold lambda0; exact contDiffAt_rpow_const_of_ne hy0.ne'
      exact h0.rpow_const_of_ne (by unfold lambda0; exact (rpow_pos_of_pos hy0 _).ne')
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  all_goals
    obtain ⟨a1, a3, an, al, a0, ap⟩ := key y hy
    have hy0 : (y : ℝ) ≠ 0 := by have : R < y := hy; linarith
    have aq : ContDiffAt ℝ 1 (fun t => p * lambda0 p t ^ (p - 1) * c_log p ε μ / t) y :=
      ((contDiffAt_const.mul a0).mul contDiffAt_const).div contDiffAt_id hy0
    have ac : ContDiffAt ℝ 1 (fun t => c_eps p ε * t ^ (-p)) y := contDiffAt_const.mul ap
    have alt : ContDiffAt ℝ 1 (fun t => fam_lambda p ε μ t ^ p - t) y := al.sub contDiffAt_id
  · have h := ((contDiffAt_const (c := (2 : ℝ))).mul ((alt.sub aq).add ac)).mul a1
    exact h.contDiffWithinAt
  · have h := ((contDiffAt_const (c := (2 : ℝ))).mul
      (aq.add ((contDiffAt_const (c := n_eps p ε)).mul al |>.mul an))).mul a1
    exact h.contDiffWithinAt
  · have h := ((contDiffAt_const (c := 2 * c_cubic p ε)).mul (alt.add ac)).mul a3
    exact h.contDiffWithinAt

/-- Helper: `ℰ₅^Y` is `C¹` at `y ∈ [Y,2Y]` once the cubic part `𝒬_{ε,3}(v_Y)` is. -/
theorem c07_aux_E5_C1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
      ∀ Y ≥ 8 * R, ∀ y ∈ Icc Y (2 * Y),
        ContDiffAt ℝ 1 (c04_cubic_part p ε (res_vY p R ε μ Y)) y →
        ContDiffAt ℝ 1 (residual_decomposition_E5 p R ε μ Y) y := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hpos5 : 0 < c05_eps0_star p δ := by
    unfold c05_eps0_star
    rw [dif_pos ⟨hp, hp1, hδ, hδμ⟩]
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))))))
    · exact (Classical.choose_spec (c04_lambda_psi_difference p hp hp1 δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_bounds p hp hp1 δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_difference_products p hp hp1 δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_difference p hp hp1 δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_lambda_taylor p hp hp1 δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_Z_primitive p hp hp1 δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (c04_phase_exponential_difference p hp hp1 δ hδ hδμ)).1.1
    · exact (Classical.choose_spec (approx_phase_differences p hp hp1 δ hδ hδμ)).1.1
  set e5 : ℝ := min 1 (c05_eps0_star p δ) with he5def
  have he5 : 0 < e5 := lt_min one_pos hpos5
  let S : c05_standing := ⟨p, e5, δ, hp, hp1, he5, min_le_left _ _, hδ, hδμ, min_le_right _ _⟩
  obtain ⟨Ra, hRa, Ha⟩ := c05_E5_split S
  obtain ⟨Rb, hRb, Cb, -, Hb⟩ := approx_E5_linear S
  obtain ⟨ε₁, hε₁, R₁, hR₁, H1⟩ := c04_aux_std p hp hp1 δ hδ hδμ
  obtain ⟨ε₂, hε₂, R₂, hR₂, hbasic, -, -, -⟩ := c04_phase_basic p hp hp1 δ hδ hδμ
  refine ⟨min e5 (min ε₁ ε₂), ⟨lt_min he5 (lt_min hε₁.1 hε₂.1), (min_le_left _ _).trans
    (min_le_left _ _)⟩, max 2 (max Ra (max Rb (max R₁ R₂))), le_max_left _ _,
    fun R hR ε hε μ hμ Y hY y hy hcub => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hR
  obtain ⟨h2R, hRRa, hRRb, hRR1, hRR2⟩ := hR
  have hεS : ε ≤ e5 := hε.2.trans (min_le_left _ _)
  have hε1 : ε ∈ Icc (0 : ℝ) ε₁ := ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε2 : ε ∈ Icc (0 : ℝ) ε₂ := ⟨hε.1, hε.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have ht : c05_standing_tuple S Ra ε μ R Y := ⟨hε.1, hεS, hμ, hRRa, hY⟩
  have ht' : c05_standing_tuple S Rb ε μ R Y := ⟨hε.1, hεS, hμ, hRRb, hY⟩
  have hy2R : 2 * R < y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  -- `ℰ₅ = ℛ_lin + ℛ_cub` near `y`
  have hev : residual_decomposition_E5 p R ε μ Y =ᶠ[𝓝 y]
      fun t => c05_E5_remainders_Rlin p R ε μ t + c05_E5_remainders_Rcub p R ε μ Y t := by
    filter_upwards [Ioi_mem_nhds hy2R] with t ht2 using (Ha ε μ R Y ht t ht2).1
  have hlin : ContDiffAt ℝ 1 (c05_E5_remainders_Rlin p R ε μ) y := (Hb ε μ R Y ht' y hy).1
  -- the local terms of `ℛ_cub`
  have hZ := (H1 R hRR1 ε hε1 μ hμ).1
  have hZy : ContDiffAt ℝ 1 (fam_Z p R ε μ) y :=
    ((hZ.contDiffAt (Ioi_mem_nhds (by linarith : R / 2 < y))).of_le
      (WithTop.coe_le_coe.mpr le_top))
  obtain ⟨g1, g2, -, -⟩ := hbasic R hRR2 ε hε2 μ hμ y (by linarith)
  have hlam := (c04_aux_lam_pos p ε μ y hy0 g1 g2).1
  have hZre : ContDiffAt ℝ 1 (fun t => (fam_Z p R ε μ t).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hZy
  have hZim : ContDiffAt ℝ 1 (fun t => (fam_Z p R ε μ t).im) y :=
    Complex.imCLM.contDiff.contDiffAt.comp y hZy
  have hZ3 : ContDiffAt ℝ 1 (fun t => (fam_Z p R ε μ t ^ 3).re) y :=
    (Complex.reCLM.contDiff.contDiffAt.comp _ (contDiffAt_id.pow 3)).comp y hZy
  have hn : ContDiffAt ℝ 1 (fun t => ‖fam_Z p R ε μ t‖ ^ 2) y := by
    have e : (fun t => ‖fam_Z p R ε μ t‖ ^ 2) =
        fun t => (fam_Z p R ε μ t).re * (fam_Z p R ε μ t).re +
          (fam_Z p R ε μ t).im * (fam_Z p R ε μ t).im := by
      funext t; rw [Complex.sq_norm, Complex.normSq_apply]
    rw [e]; exact (hZre.mul hZre).add (hZim.mul hZim)
  have hl : ContDiffAt ℝ 1 (fun t => fam_lambda p ε μ t ^ p) y :=
    ((c04_aux_lambda_contDiffOn p ε μ 1).contDiffAt (Ioi_mem_nhds hy0)).rpow_const_of_ne hlam.ne'
  have hcub' : ContDiffAt ℝ 1 (c05_E5_remainders_Rcub p R ε μ Y) y := by
    have := (hcub.sub (((contDiffAt_const (c := 2 * n_eps p ε)).mul hl).mul hn |>.mul hZre)).add
      (((contDiffAt_const (c := 2 * c_cubic p ε * ((3 : ℝ) ^ p - 1))).mul hl).mul hZ3)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [c05_E5_remainders_Rcub]
  exact (hlin.add hcub').congr_of_eventuallyEq hev

/-- Helper (proposed blueprint node `lem:c04_residual_terms_C1`, nonlocal part; supports
prop:approx_residual_positive): `ℰ₅^Y` is `C¹` at every `y ∈ [Y,2Y]` and `ℰ₇^Y, ℰ₈^Y, ℰ₉^Y` are
`C¹` on `J_Y = (3Y/4, 5Y/2) ⊃ [Y, 2Y]`. -/
theorem c07_aux_residual_nonlocal_C1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
      ∀ Y ≥ 8 * R,
        (∀ y ∈ Icc Y (2 * Y), ContDiffAt ℝ 1 (residual_decomposition_E5 p R ε μ Y) y) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E7 p R ε μ Y) (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E8 p R ε μ Y) (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E9 p R ε μ Y) (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hab : beta p + 1 / p < 2 * p + 1 := by
    unfold beta
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (mul_pos (show (0 : ℝ) < 4 * p - 3 by linarith)
      (show (0 : ℝ) < p + 1 by linarith)) hp0]
  let P : parameters := ⟨p, (2 * (beta p + 1 / p) + (2 * p + 1)) / 3,
    ((beta p + 1 / p) + 2 * (2 * p + 1)) / 3, hp, hp1, by linarith, by linarith, by linarith⟩
  obtain ⟨hpos6, -⟩ := c07_aux_eps0_pos P δ hδ hδμ
  set e6 : ℝ := min 1 (c06_eps0_star P δ) with he6def
  have he6 : 0 < e6 := lt_min one_pos hpos6
  obtain ⟨εa, hεa, Ra, hRa, HA⟩ := c07_aux_E5_C1 p hp hp1 δ hδ hδμ
  obtain ⟨Rc, -, HC⟩ := c06_cubic_vY_C1 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  obtain ⟨R7, -, H7⟩ := c06_E7_C1 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  obtain ⟨R8, -, H8⟩ := c06_E8_C1 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  obtain ⟨R9, -, H9⟩ := c06_E9_C1 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  refine ⟨min εa e6, ⟨lt_min hεa.1 he6, (min_le_left _ _).trans hεa.2⟩,
    max Ra (max Rc (max R7 (max R8 R9))), le_trans hRa (le_max_left _ _),
    fun R hR ε hε μ hμ Y hY => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hR
  obtain ⟨ha, hc, h7, h8, h9⟩ := hR
  have hεa' : ε ∈ Icc (0 : ℝ) εa := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε6 : ε ∈ Icc (0 : ℝ) e6 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  exact ⟨fun y hy => HA R ha ε hεa' μ hμ Y hY y hy (HC R hc Y hY ε hε6 μ hμ).contDiffAt,
    (H7 R h7 Y hY ε hε6 μ hμ).contDiffOn, (H8 R h8 Y hY ε hε6 μ hμ).contDiffOn,
    H9 R h9 Y hY ε hε6 μ hμ⟩

/-- Helper: the summands `ℰ₂,…,ℰ₅^Y, ℰ₇^Y,…,ℰ₉^Y` are `C¹` near `[Y,2Y]` (from
`c07_aux_residual_local_C1` and `c07_aux_residual_nonlocal_C1`). -/
theorem c07_aux_residual_terms_C1 (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
      ∀ Y ≥ 8 * R,
        ContDiffOn ℝ 1 (residual_decomposition_E2 p R ε μ) (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E3 p R ε μ) (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E4 p R ε μ) (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        (∀ y ∈ Icc Y (2 * Y), ContDiffAt ℝ 1 (residual_decomposition_E5 p R ε μ Y) y) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E7 p R ε μ Y) (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E8 p R ε μ Y) (Ioo (3 * Y / 4) (5 * Y / 2)) ∧
        ContDiffOn ℝ 1 (residual_decomposition_E9 p R ε μ Y) (Ioo (3 * Y / 4) (5 * Y / 2)) := by
  intro δ hδ hδμ
  obtain ⟨ea, hea, Ra, hRa, Ha⟩ := c07_aux_residual_local_C1 p hp hp1 δ hδ hδμ
  obtain ⟨eb, heb, Rb, hRb, Hb⟩ := c07_aux_residual_nonlocal_C1 p hp hp1 δ hδ hδμ
  refine ⟨min ea eb, ⟨lt_min hea.1 heb.1, (min_le_left _ _).trans hea.2⟩, max Ra Rb,
    le_trans hRa (le_max_left _ _), fun R hR ε hε μ hμ Y hY => ?_⟩
  have hR1 : Ra ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : Rb ≤ R := le_trans (le_max_right _ _) hR
  obtain ⟨a2, a3, a4⟩ := Ha R hR1 ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩ μ hμ
  have h2R : (2 : ℝ) ≤ R := le_trans hRa hR1
  have hsub : Ioo (3 * Y / 4) (5 * Y / 2) ⊆ Ioi R := fun t ht => by
    have := ht.1; simp only [mem_Ioi]; linarith
  exact ⟨a2.mono hsub, a3.mono hsub, a4.mono hsub,
    Hb R hR2 ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩ μ hμ Y hY⟩

/-- Helper: `C ε² a + ... ≤ C ε J` bookkeeping. -/
theorem c07_aux_eps_sq_le (C ε a J : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a)
    (haJ : a ≤ J) : C * ε ^ 2 * a ≤ C * ε * J := by
  have h1 : ε ^ 2 ≤ ε := by nlinarith
  calc C * ε ^ 2 * a ≤ C * ε * a := by gcongr
    _ ≤ C * ε * J := by gcongr

/-- Blueprint: prop:approx_residual_positive.  For `y ≥ 8R`, `ℰ̃_ε(f̄_{ε,μ}) - G_μ` is `C¹` on
`(8R,∞)` and `|∂^j(ℰ̃_ε(f̄) - G_μ)(y)| ≤ C ε ⟨y⟩^{-2p-1+j/p}` (`j = 0,1`), hence
`≤ C ε ⟨y⟩^{-γ+j/p}` for every `γ ≤ 2p+1`.  (`C` may depend on `R`.)
(Blueprint chapter 04; stated in this file, see above.) -/
theorem approx_residual_positive (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∃ C > (0 : ℝ),
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        ContDiffOn ℝ 1 (fun y => c01_quasilinear_residual p ε (approximate_solution_family p R ε μ) y -
          G_mu p μ y) (Ioi (8 * R)) ∧
        ∀ y ≥ 8 * R, ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (fun t => c01_quasilinear_residual p ε
              (approximate_solution_family p R ε μ) t - G_mu p μ t) y| ≤
            C * ε * jb y ^ (-2 * p - 1 + j / p) ∧
          ∀ γ : ℝ, γ ≤ 2 * p + 1 →
            |iteratedDeriv j (fun t => c01_quasilinear_residual p ε
                (approximate_solution_family p R ε μ) t - G_mu p μ t) y| ≤
              C * ε * jb y ^ (-γ + j / p) := by
  intro δ hδ hδμ
  have hp0 : 0 < p := by linarith
  have hβ1 : (p + 1) / 2 ≤ beta p := by
    unfold beta; rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hab : beta p + 1 / p < 2 * p + 1 := by
    unfold beta
    rw [div_add_div _ _ (by positivity) (by positivity), div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (mul_pos (show (0 : ℝ) < 4 * p - 3 by linarith)
      (show (0 : ℝ) < p + 1 by linarith)) hp0]
  let P : parameters := ⟨p, (2 * (beta p + 1 / p) + (2 * p + 1)) / 3,
    ((beta p + 1 / p) + 2 * (2 * p + 1)) / 3, hp, hp1, by linarith, by linarith, by linarith⟩
  obtain ⟨hpos6, hpos5⟩ := c07_aux_eps0_pos P δ hδ hδμ
  set e6 : ℝ := min 1 (c06_eps0_star P δ) with he6def
  set e5 : ℝ := min 1 (c05_eps0_star p δ) with he5def
  have he6 : 0 < e6 := lt_min one_pos hpos6
  have he5 : 0 < e5 := lt_min one_pos hpos5
  let S : c05_standing := ⟨p, e5, δ, hp, hp1, he5, min_le_left _ _, hδ, hδμ, min_le_right _ _⟩
  obtain ⟨ε1, hε1, R1, hR1, C1, hC1, H1⟩ := approx_E1 p hp hp1 δ hδ hδμ
  obtain ⟨ε2, hε2, R2, hR2, C2, hC2, H2⟩ := approx_E2 p hp hp1 δ hδ hδμ
  obtain ⟨ε3, hε3, R3, hR3, C3, hC3, H3⟩ := approx_E3 p hp hp1 δ hδ hδμ
  obtain ⟨ε4, hε4, R4, hR4, C4, hC4, H4⟩ := approx_E4 p hp hp1 δ hδ hδμ
  obtain ⟨εf, hεf, Rf, hRf, HF, -⟩ := c04_E1_formula p hp hp1 δ hδ hδμ
  obtain ⟨εi, hεi, Ri, hRi, HI⟩ := c04_residual_identity p hp hp1 δ hδ hδμ
  obtain ⟨εr, hεr, Rr, hRr, HR⟩ := c07_aux_residual_terms_C1 p hp hp1 δ hδ hδμ
  obtain ⟨R5, hR5, C5, hC5, H5⟩ := approx_E5_cubic S
  obtain ⟨R6, hR6, H6⟩ := approx_E6 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  obtain ⟨R7, hR7, H7⟩ := approx_E7 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  obtain ⟨R8, hR8, H8⟩ := approx_E8 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  obtain ⟨R9, hR9, H9⟩ := approx_E9 P e6 δ he6 (min_le_left _ _) hδ hδμ (min_le_right _ _)
  set ε₀ : ℝ := min ε1 (min ε2 (min ε3 (min ε4 (min εf (min εi (min εr (min e6 e5))))))) with hε₀
  have hε₀pos : 0 < ε₀ := by
    simp only [hε₀, lt_min_iff]
    exact ⟨hε1.1, hε2.1, hε3.1, hε4.1, hεf.1, hεi.1, hεr.1, he6, he5⟩
  have hε₀1 : ε₀ ≤ 1 := (min_le_left _ _).trans hε1.2
  have hmin : ε₀ ≤ ε1 ∧ ε₀ ≤ ε2 ∧ ε₀ ≤ ε3 ∧ ε₀ ≤ ε4 ∧ ε₀ ≤ εf ∧ ε₀ ≤ εi ∧ ε₀ ≤ εr ∧
      ε₀ ≤ e6 ∧ ε₀ ≤ e5 := by
    simp only [hε₀, min_le_iff, le_refl, true_or, or_true, and_self]
  set R₀ : ℝ := max 2 (max R1 (max R2 (max R3 (max R4 (max Rf (max Ri (max Rr
    (max R5 (max R6 (max R7 (max R8 R9))))))))))) with hR₀
  refine ⟨ε₀, ⟨hε₀pos, hε₀1⟩, R₀, le_max_left _ _, fun R hR => ?_⟩
  have hRs : 2 ≤ R ∧ R1 ≤ R ∧ R2 ≤ R ∧ R3 ≤ R ∧ R4 ≤ R ∧ Rf ≤ R ∧ Ri ≤ R ∧ Rr ≤ R ∧ R5 ≤ R ∧
      R6 ≤ R ∧ R7 ≤ R ∧ R8 ≤ R ∧ R9 ≤ R := by
    simp only [hR₀, ge_iff_le, max_le_iff] at hR
    tauto
  obtain ⟨hR2', hRR1, hRR2, hRR3, hRR4, hRRf, hRRi, hRRr, hRR5, hRR6, hRR7, hRR8, hRR9⟩ := hRs
  obtain ⟨C6, hC6, H6'⟩ := H6 R hRR6
  obtain ⟨C7, hC7, H7'⟩ := H7 R hRR7
  obtain ⟨C8, hC8, H8'⟩ := H8 R hRR8
  obtain ⟨C9, hC9, H9'⟩ := H9 R hRR9
  refine ⟨C1 + C2 + 2 * C3 + C4 + C5 + C6 + C7 + C8 + C9, by positivity, fun ε hε μ hμ => ?_⟩
  obtain ⟨m1, m2, m3, m4, mf, mi, mr, m6, m5⟩ := hmin
  have hε0 : 0 ≤ ε := hε.1
  have hεle : ∀ e, ε₀ ≤ e → ε ∈ Icc (0 : ℝ) e := fun e he => ⟨hε.1, hε.2.trans he⟩
  have hε1' : ε ≤ 1 := hε.2.trans hε₀1
  have hεε : ε ^ 2 ≤ ε := by nlinarith
  have hR0 : 0 < R := by linarith
  -- the residual identity
  have hId : ∀ Y ≥ 8 * R, ∀ t > R, c01_quasilinear_residual p ε (approximate_solution_family p R ε μ) t -
      G_mu p μ t = residual_decomposition p R ε μ Y t := fun Y hY t ht => by
    obtain ⟨-, -, -, -, e1, e2⟩ := HI R hRRi ε (hεle εi mi) μ hμ Y hY t ht
    exact e1.trans e2
  have hloc : ∀ y ≥ 8 * R, (fun t => c01_quasilinear_residual p ε
      (approximate_solution_family p R ε μ) t - G_mu p μ t) =ᶠ[𝓝 y]
      residual_decomposition p R ε μ y := fun y hy => by
    filter_upwards [Ioi_mem_nhds (show R < y by linarith)] with t ht using hId y hy t ht
  -- regularity of the nine summands at `y` (with `Y = y`)
  have hreg : ∀ y ≥ 8 * R,
      ContDiffAt ℝ 1 (residual_decomposition_E1 p R ε) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E2 p R ε μ) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E3 p R ε μ) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E4 p R ε μ) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E5 p R ε μ y) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E6 p R ε μ) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E7 p R ε μ y) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E8 p R ε μ y) y ∧
      ContDiffAt ℝ 1 (residual_decomposition_E9 p R ε μ y) y := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have hJ : Ioo (3 * y / 4) (5 * y / 2) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
    obtain ⟨r2, r3, r4, r5, r7, r8, r9⟩ := HR R hRRr ε (hεle εr mr) μ hμ y hy
    exact ⟨(HF R hRRf ε (hεle εf mf)).2.1.contDiffAt (Ioi_mem_nhds (by linarith)),
      r2.contDiffAt hJ, r3.contDiffAt hJ, r4.contDiffAt hJ, r5 y ⟨le_rfl, by linarith⟩,
      (H6' ε (hεle e6 m6) μ hμ).1.contDiffAt (Ioi_mem_nhds (by linarith)),
      r7.contDiffAt hJ, r8.contDiffAt hJ, r9.contDiffAt hJ⟩
  have hsum : ∀ Y, residual_decomposition p R ε μ Y = fun t =>
      residual_decomposition_E1 p R ε t + residual_decomposition_E2 p R ε μ t +
      residual_decomposition_E3 p R ε μ t + residual_decomposition_E4 p R ε μ t +
      residual_decomposition_E5 p R ε μ Y t + residual_decomposition_E6 p R ε μ t +
      residual_decomposition_E7 p R ε μ Y t + residual_decomposition_E8 p R ε μ Y t +
      residual_decomposition_E9 p R ε μ Y t := fun Y => rfl
  have hC1sum : ∀ y ≥ 8 * R, ContDiffAt ℝ 1 (residual_decomposition p R ε μ y) y := by
    intro y hy
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hreg y hy
    rw [hsum]
    exact ((((((((c1.add c2).add c3).add c4).add c5).add c6).add c7).add c8).add c9)
  refine ⟨fun y hy => ((hC1sum y (le_of_lt hy)).congr_of_eventuallyEq
    (hloc y (le_of_lt hy))).contDiffWithinAt, fun y hy j hj => ?_⟩
  -- the derivative splits
  have hy0 : 0 < y := by linarith
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hreg y hy
  have d1 := c1.differentiableAt one_ne_zero
  have d2 := c2.differentiableAt one_ne_zero
  have d3 := c3.differentiableAt one_ne_zero
  have d4 := c4.differentiableAt one_ne_zero
  have d5 := c5.differentiableAt one_ne_zero
  have d6 := c6.differentiableAt one_ne_zero
  have d7 := c7.differentiableAt one_ne_zero
  have d8 := c8.differentiableAt one_ne_zero
  have d9 := c9.differentiableAt one_ne_zero
  have hit : iteratedDeriv j (fun t => c01_quasilinear_residual p ε
      (approximate_solution_family p R ε μ) t - G_mu p μ t) y =
      iteratedDeriv j (residual_decomposition p R ε μ y) y := by
    interval_cases j
    · simp only [iteratedDeriv_zero]; exact (hloc y hy).eq_of_nhds
    · simp only [iteratedDeriv_one]; exact (hloc y hy).deriv_eq
  have hspl : iteratedDeriv j (residual_decomposition p R ε μ y) y =
      iteratedDeriv j (residual_decomposition_E1 p R ε) y +
      iteratedDeriv j (residual_decomposition_E2 p R ε μ) y +
      iteratedDeriv j (residual_decomposition_E3 p R ε μ) y +
      iteratedDeriv j (residual_decomposition_E4 p R ε μ) y +
      iteratedDeriv j (residual_decomposition_E5 p R ε μ y) y +
      iteratedDeriv j (residual_decomposition_E6 p R ε μ) y +
      iteratedDeriv j (residual_decomposition_E7 p R ε μ y) y +
      iteratedDeriv j (residual_decomposition_E8 p R ε μ y) y +
      iteratedDeriv j (residual_decomposition_E9 p R ε μ y) y := by
    rw [hsum, c07_aux_iter_add (((((((d1.fun_add d2).fun_add d3).fun_add d4).fun_add d5).fun_add d6).fun_add d7).fun_add d8)
      d9 hj, c07_aux_iter_add ((((((d1.fun_add d2).fun_add d3).fun_add d4).fun_add d5).fun_add d6).fun_add d7) d8 hj,
      c07_aux_iter_add (((((d1.fun_add d2).fun_add d3).fun_add d4).fun_add d5).fun_add d6) d7 hj,
      c07_aux_iter_add ((((d1.fun_add d2).fun_add d3).fun_add d4).fun_add d5) d6 hj,
      c07_aux_iter_add (((d1.fun_add d2).fun_add d3).fun_add d4) d5 hj,
      c07_aux_iter_add ((d1.fun_add d2).fun_add d3) d4 hj, c07_aux_iter_add (d1.fun_add d2) d3 hj,
      c07_aux_iter_add d1 d2 hj]
  -- exponents
  set J : ℝ := jb y ^ (-2 * p - 1 + j / p) with hJdef
  have hjb : 1 ≤ jb y := c06_aux_one_le_jb y
  have hJ : ∀ e : ℝ, e ≤ -2 * p - 1 + j / p → jb y ^ e ≤ J := fun e he =>
    Real.rpow_le_rpow_of_exponent_le hjb he
  have hJ0 : 0 ≤ J := Real.rpow_nonneg (by linarith) _
  have hβ0 : 0 < beta p := by linarith
  have hy2R : y ≥ 2 * R := by linarith
  have hyI : y ∈ Icc y (2 * y) := ⟨le_rfl, by linarith⟩
  -- the nine bounds
  have b1 : |iteratedDeriv j (residual_decomposition_E1 p R ε) y| ≤ C1 * ε * J := by
    have := (H1 R hRR1 ε (hεle ε1 m1) y hy2R j hj).2 (2 * p + 1) le_rfl
    rw [show -(2 * p + 1) + (j : ℝ) / p = -2 * p - 1 + j / p by ring] at this; exact this
  have b2 : |iteratedDeriv j (residual_decomposition_E2 p R ε μ) y| ≤ C2 * ε * J :=
    (H2 R hRR2 ε (hεle ε2 m2) μ hμ y hy2R j hj).trans (c07_aux_eps_sq_le _ _ _ _ hC2.le hε0 hε1'
      (Real.rpow_nonneg (by linarith) _) (hJ _ (by linarith)))
  have b3 : |iteratedDeriv j (residual_decomposition_E3 p R ε μ) y| ≤ 2 * C3 * ε * J := by
    refine (H3 R hRR3 ε (hεle ε3 m3) μ hμ y hy2R j hj).trans ?_
    have h1 := c07_aux_eps_sq_le _ _ _ _ hC3.le hε0 hε1' (Real.rpow_nonneg (by linarith) _)
      (hJ (-p - 3 * beta p + j / p) (by linarith))
    have h2 : C3 * ε * jb y ^ (1 - 5 * beta p + j / p) ≤ C3 * ε * J :=
      mul_le_mul_of_nonneg_left (hJ _ (by linarith)) (by positivity)
    calc _ ≤ C3 * ε * J + C3 * ε * J := add_le_add h1 h2
      _ = 2 * C3 * ε * J := by ring
  have b4 : |iteratedDeriv j (residual_decomposition_E4 p R ε μ) y| ≤ C4 * ε * J :=
    (H4 R hRR4 ε (hεle ε4 m4) μ hμ y hy2R j hj).trans (c07_aux_eps_sq_le _ _ _ _ hC4.le hε0 hε1'
      (Real.rpow_nonneg (by linarith) _) (hJ _ (by linarith)))
  have b5 : |iteratedDeriv j (residual_decomposition_E5 p R ε μ y) y| ≤ C5 * ε * J :=
    (H5 ε μ R y ⟨hε0, hε.2.trans m5, hμ, hRR5, hy⟩ y hyI j hj).2
  have b6 : |iteratedDeriv j (residual_decomposition_E6 p R ε μ) y| ≤ C6 * ε * J :=
    ((H6' ε (hεle e6 m6) μ hμ).2 y (by linarith)).1 j hj
  have b7 : |iteratedDeriv j (residual_decomposition_E7 p R ε μ y) y| ≤ C7 * ε * J := by
    obtain ⟨h1, h2⟩ := H7' y hy ε (hεle e6 m6) μ hμ y hyI j hj
    exact h1.trans h2
  have b8 : |iteratedDeriv j (residual_decomposition_E8 p R ε μ y) y| ≤ C8 * ε * J :=
    ((H8' y hy ε (hεle e6 m6) μ hμ).2.2 y hyI j hj).trans
      (c07_aux_eps_sq_le _ _ _ _ hC8.le hε0 hε1' hJ0 le_rfl)
  have b9 : |iteratedDeriv j (residual_decomposition_E9 p R ε μ y) y| ≤ C9 * ε * J :=
    ((H9' y hy ε (hεle e6 m6) μ hμ).2 y hyI j hj).trans
      (mul_le_mul_of_nonneg_left (hJ _ (by linarith)) (by positivity))
  have hmain : |iteratedDeriv j (fun t => c01_quasilinear_residual p ε
      (approximate_solution_family p R ε μ) t - G_mu p μ t) y| ≤
      (C1 + C2 + 2 * C3 + C4 + C5 + C6 + C7 + C8 + C9) * ε * J := by
    rw [hit, hspl]
    set K := (C1 + C2 + 2 * C3 + C4 + C5 + C6 + C7 + C8 + C9) * ε * J
    have hK : K = C1 * ε * J + C2 * ε * J + 2 * C3 * ε * J + C4 * ε * J + C5 * ε * J +
        C6 * ε * J + C7 * ε * J + C8 * ε * J + C9 * ε * J := by ring
    rw [hK]
    refine (abs_add_le _ _).trans (add_le_add ?_ b9)
    refine (abs_add_le _ _).trans (add_le_add ?_ b8)
    refine (abs_add_le _ _).trans (add_le_add ?_ b7)
    refine (abs_add_le _ _).trans (add_le_add ?_ b6)
    refine (abs_add_le _ _).trans (add_le_add ?_ b5)
    refine (abs_add_le _ _).trans (add_le_add ?_ b4)
    refine (abs_add_le _ _).trans (add_le_add ?_ b3)
    exact (abs_add_le _ _).trans (add_le_add b1 b2)
  refine ⟨hmain, fun γ hγ => hmain.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hjb (by linarith))
    (by positivity)

/-- Wrapper for prop:approx_residual_positive (`GSQG.approx_residual_positive`, stated above),
stated verbatim; proved by it. -/
theorem c07_ext_approx_residual_positive (p : ℝ) (hp : 3 / 4 < p) (hp1 : p < 1) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star p‖ / 2 →
    ∃ ε₀ ∈ Ioc (0 : ℝ) 1, ∃ R₀ ≥ (2 : ℝ), ∀ R ≥ R₀, ∃ C > (0 : ℝ),
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar p δ,
        ContDiffOn ℝ 1 (fun y => c01_quasilinear_residual p ε (approximate_solution_family p R ε μ) y -
          G_mu p μ y) (Ioi (8 * R)) ∧
        ∀ y ≥ 8 * R, ∀ j : ℕ, j ≤ 1 →
          |iteratedDeriv j (fun t => c01_quasilinear_residual p ε
              (approximate_solution_family p R ε μ) t - G_mu p μ t) y| ≤
            C * ε * jb y ^ (-2 * p - 1 + j / p) ∧
          ∀ γ : ℝ, γ ≤ 2 * p + 1 →
            |iteratedDeriv j (fun t => c01_quasilinear_residual p ε
                (approximate_solution_family p R ε μ) t - G_mu p μ t) y| ≤
              C * ε * jb y ^ (-γ + j / p) :=
  approx_residual_positive p hp hp1

/-- Blueprint: lem:c07_tilde_residual_Y.  For every admissible `γ`:
`ℰ̃_ε(f̄_{ε,μ}) - G_μ ∈ Y_γ` and `‖ℰ̃_ε(f̄_{ε,μ}) - G_μ‖_{Y_γ} ≤ C(γ) ε`. -/
theorem c07_tilde_residual_Y (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R → ∀ γ : ℝ, P.admissible γ →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
      (fun y => c07_divided_residual P.p ε (approximate_solution_family P.p R ε μ) y -
        G_mu P.p μ y) ∈ Y_gamma P.p γ ∧
      Y_gamma_norm P.p γ (fun y => c07_divided_residual P.p ε
        (approximate_solution_family P.p R ε μ) y - G_mu P.p μ y) ≤ ENNReal.ofReal (C * ε) := by
  intro δ hδ hδ'
  obtain ⟨Ra, ea, -, hea, hea1, hA⟩ := approx_residual_compact P δ hδ hδ'
  obtain ⟨Rb, eb, -, heb, -, hNeg⟩ := approx_residual_negative P δ hδ hδ'
  obtain ⟨ec, ⟨hec, -⟩, Rc, -, hPos⟩ :=
    c07_ext_approx_residual_positive P.p P.hp_lo P.hp_hi δ hδ hδ'
  obtain ⟨Rd, ed, -, hed, -, hSp⟩ := c07_residual_split P δ hδ hδ'
  refine ⟨max Ra (max Rb (max Rc (max Rd 1))), min ea (min eb (min ec ed)), by simp,
    by simp [*], (min_le_left _ _).trans hea1, fun R hR γ hγ => ?_⟩
  have hRa : Ra ≤ R := le_trans (by simp) hR
  have hRb : Rb ≤ R := le_trans (by simp) hR
  have hRc : Rc ≤ R := le_trans (by simp) hR
  have hRd : Rd ≤ R := le_trans (by simp) hR
  have hR1 : 1 ≤ R := le_trans (by simp) hR
  obtain ⟨Ca, hCa, hA'⟩ := hA R hRa
  obtain ⟨Cb, hCb, hNeg'⟩ := hNeg R hRb
  obtain ⟨Cc, hCc, hPos'⟩ := hPos R hRc
  have hγ0 : 0 < γ := by
    have h1 : 0 < beta P.p := by unfold beta; have := P.hp_lo; positivity
    have h2 : 0 < 1 / P.p := by have := P.hp_lo; positivity
    linarith [hγ.1]
  refine ⟨4 * (Cb + Cc) + 4 * jb (8 * R) ^ (γ + 1) * (2 * Ca), by unfold jb; positivity,
    fun ε hε μ hμ => ?_⟩
  have hεa : ε ∈ Icc (0 : ℝ) ea := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεb : ε ∈ Icc (0 : ℝ) eb := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεc : ε ∈ Icc (0 : ℝ) ec := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεd : ε ∈ Icc (0 : ℝ) ed := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεa.2.trans hea1⟩
  set f := approximate_solution_family P.p R ε μ with hf_def
  obtain ⟨hC1, hcpt⟩ := hA' ε hεa μ hμ
  obtain ⟨hfsm, L, hL⟩ := (hSp R hRd ε hεd μ hμ).1 f (by simp [hf_def])
  have hid : (fun t => c01_quasilinear_residual P.p ε f t - G_mu P.p μ t) =
      fun t => c07_divided_residual P.p ε f t - G_mu P.p μ t := by
    funext t
    rw [(c07_divided_residual_identity P.p (by linarith [P.hp_lo]) P.hp_hi ε hε1 f
      (hfsm.of_le (by simp)) ⟨L, hL⟩ t).2.2.2.2.2.1]
  have hp0 : 0 < P.p := by linarith [P.hp_lo]
  have key := c07_Y_gamma_patching P.p hp0 γ (8 * R) ((Cb + Cc) * ε) (2 * (Ca * ε)) hγ0
    (by positivity) (by nlinarith [hε.1]) (by nlinarith [hε.1])
    (fun t => c07_divided_residual P.p ε f t - G_mu P.p μ t) hC1
    (fun j hj y hy => by
      have := ((hPos' ε hεc μ hμ).2 y hy j hj).2 γ hγ.2.le
      rw [hid] at this
      refine this.trans ?_
      have : 0 ≤ jb y ^ (-γ + j / P.p) := by unfold jb; positivity
      nlinarith [mul_nonneg (mul_nonneg hCb.le hε.1) this])
    (fun j hj y hy => by
      refine ((hNeg' ε hεb μ hμ y (by linarith) j hj).2 γ hγ.2.le).trans ?_
      have : 0 ≤ jb y ^ (-γ - j) := by unfold jb; positivity
      nlinarith [mul_nonneg (mul_nonneg hCc.le hε.1) this])
    (by
      have := c07_aux_CkNorm_le 1 (8 * R) (Ca * ε) (by nlinarith [hε.1]) _
        (fun i hi y hy => hcpt i hi y ⟨by linarith [hy.1], hy.2⟩)
      norm_num at this ⊢
      linarith)
  refine ⟨key.1, key.2.trans (ENNReal.ofReal_le_ofReal (le_of_eq (by ring)))⟩

/-- Blueprint: lem:c07_B_conversion.  For `γ > 0`, `K ≥ 1`, `0 ≤ ε ≤ 1`, `f ∈ 𝒫(K)`, with
`C = C(p,K)`: (1) `H ∈ Y_γ ∩ C¹ ⟹ B_ε(f')H ∈ Y_γ ∩ C¹`, `‖B_ε(f')H‖_{Y_γ} ≤ C‖H‖_{Y_γ}`;
(2) if `G ∈ C¹` with `N_γ(G) = sup ⟨y⟩^{γ+1}(|G|+|G'|) ≤ N`, then
`‖(B_ε(f') - 1)G‖_{Y_γ} ≤ CεN`. -/
theorem c07_B_conversion (P : parameters) :
    ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ f ∈ c07_profile_class P.p K,
        (∀ H : ℝ → ℝ, H ∈ Y_gamma P.p γ → ContDiff ℝ 1 H →
          (fun y => A_eps_B P.p ε (deriv f y) * H y) ∈ Y_gamma P.p γ ∧
          ContDiff ℝ 1 (fun y => A_eps_B P.p ε (deriv f y) * H y) ∧
          Y_gamma_norm P.p γ (fun y => A_eps_B P.p ε (deriv f y) * H y) ≤
            ENNReal.ofReal C * Y_gamma_norm P.p γ H) ∧
        (∀ G : ℝ → ℝ, ContDiff ℝ 1 G → ∀ N : ℝ,
          (∀ y : ℝ, jb y ^ (γ + 1) * (|G y| + |deriv G y|) ≤ N) →
          Y_gamma_norm P.p γ (fun y => (A_eps_B P.p ε (deriv f y) - 1) * G y) ≤
            ENNReal.ofReal (C * ε * N)) := by
  intro K hK
  have hp : 0 < P.p := by linarith [P.hp_lo]
  obtain ⟨CAB, -, hAB⟩ := c07_A_B_bounds P.p hp P.hp_hi
  refine ⟨1 + 6 * K ^ 2, by positivity, fun γ hγ ε hε f hf => ?_⟩
  obtain ⟨hf3, hfb⟩ := hf
  have hε0 := hε.1
  have hjb : ∀ y, 0 < jb y := fun y => lt_of_lt_of_le one_pos (c07_aux_one_le_jb y)
  have hnn : ∀ y (s : ℝ), 0 ≤ jb y ^ s := fun y s => Real.rpow_nonneg (hjb y).le s
  set b : ℝ → ℝ := fun y => A_eps_B P.p ε (deriv f y) with hb_def
  have hf2 : ContDiff ℝ 2 (deriv f) := (hf3.of_le (m := 2 + 1) (by norm_num)).deriv'
  have hi2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hbd : ∀ y, HasDerivAt b (deriv (A_eps_B P.p ε) (deriv f y) * iteratedDeriv 2 f y) y := by
    intro y
    have h1 : HasDerivAt (deriv f) (iteratedDeriv 2 f y) y := by
      rw [hi2]; exact (hf2.differentiable (by simp) y).hasDerivAt
    exact (c07_aux_B_hasDeriv P.p ε (deriv f y) hε0).differentiableAt.hasDerivAt.comp y h1
  have hbC : ContDiff ℝ 1 b := by
    have hB : ContDiff ℝ 1 (A_eps_B P.p ε) := by
      unfold A_eps_B
      exact ContDiff.rpow_const_of_ne (by fun_prop) fun u => by positivity
    exact hB.comp (hf2.of_le (by norm_num))
  have hK2 : ∀ y, (deriv f y) ^ 2 ≤ K ^ 2 := fun y => by
    have := (hfb y).1; nlinarith [abs_nonneg (deriv f y), sq_abs (deriv f y)]
  have hb1 : ∀ y, |b y - 1| ≤ K ^ 2 * ε := fun y => by
    obtain ⟨-, -, -, h0, h1, -⟩ := (hAB ε hε).1 (deriv f y)
    show |A_eps_B P.p ε (deriv f y) - 1| ≤ K ^ 2 * ε
    rw [abs_of_nonneg h0]
    have := mul_le_mul_of_nonneg_left (hK2 y) (show 0 ≤ (P.p + 1) / 2 * ε by positivity)
    have h3 : (P.p + 1) / 2 * ε * K ^ 2 ≤ K ^ 2 * ε := by
      have : (P.p + 1) / 2 ≤ 1 := by linarith [P.hp_hi]
      nlinarith [mul_nonneg hε0 (sq_nonneg K)]
    linarith
  have hb : ∀ y, |b y| ≤ 1 + K ^ 2 := fun y => by
    have := hb1 y
    have : K ^ 2 * ε ≤ K ^ 2 := by nlinarith [hε.2, sq_nonneg K]
    have := abs_sub_abs_le_abs_sub (b y) 1
    rw [abs_one] at this; linarith
  have hB' : ∀ y, |deriv (A_eps_B P.p ε) (deriv f y)| ≤ 2 * K * ε := fun y => by
    obtain ⟨-, -, -, -, -, h⟩ := (hAB ε hε).1 (deriv f y)
    have := mul_le_mul_of_nonneg_left (hfb y).1 (show 0 ≤ (P.p + 1) * ε by positivity)
    have : (P.p + 1) * ε * K ≤ 2 * K * ε := by nlinarith [P.hp_hi, mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ K)]
    linarith
  have hdb : ∀ y, deriv b y = deriv (A_eps_B P.p ε) (deriv f y) * iteratedDeriv 2 f y :=
    fun y => (hbd y).deriv
  have hbp : ∀ y, 0 ≤ y → jb y ^ (-1 / P.p) * |deriv b y| ≤ 2 * K ^ 2 * ε := fun y hy => by
    rw [hdb, abs_mul]
    have h2 := ((hfb y).2.1 hy)
    have hw : jb y ^ (-1 / P.p) * (K * jb y ^ c07_theta P.p) ≤ K := by
      have : jb y ^ (-1 / P.p) * jb y ^ c07_theta P.p ≤ 1 := by
        rw [← Real.rpow_add (hjb y)]
        apply Real.rpow_le_one_of_one_le_of_nonpos (c07_aux_one_le_jb y)
        unfold c07_theta beta
        have : 0 < (P.p + 1) / (2 * P.p) := by positivity
        have : -1 / P.p = -(1 / P.p) := by ring
        linarith
      rw [show jb y ^ (-1 / P.p) * (K * jb y ^ c07_theta P.p) =
        K * (jb y ^ (-1 / P.p) * jb y ^ c07_theta P.p) by ring]
      exact mul_le_of_le_one_right (by linarith) this
    have := mul_le_mul_of_nonneg_left h2 (hnn y (-1 / P.p))
    have h4 : jb y ^ (-1 / P.p) * |iteratedDeriv 2 f y| ≤ K := by linarith
    calc jb y ^ (-1 / P.p) * (|deriv (A_eps_B P.p ε) (deriv f y)| * |iteratedDeriv 2 f y|)
        = |deriv (A_eps_B P.p ε) (deriv f y)| * (jb y ^ (-1 / P.p) * |iteratedDeriv 2 f y|) := by
          ring
      _ ≤ (2 * K * ε) * K := mul_le_mul (hB' y) h4
          (mul_nonneg (hnn _ _) (abs_nonneg _)) (mul_nonneg (by linarith) hε0)
      _ = 2 * K ^ 2 * ε := by ring
  have hbn : ∀ y, y ≤ 0 → jb y * |deriv b y| ≤ 2 * K ^ 2 * ε := fun y hy => by
    rw [hdb, abs_mul]
    have h2 := ((hfb y).2.2.1 hy)
    have h4 : jb y * |iteratedDeriv 2 f y| ≤ K := by
      have := mul_le_mul_of_nonneg_left h2 (hjb y).le
      have e : jb y * (K * jb y ^ (-1 : ℝ)) = K := by
        rw [Real.rpow_neg_one]; field_simp [(hjb y).ne']
      linarith
    calc jb y * (|deriv (A_eps_B P.p ε) (deriv f y)| * |iteratedDeriv 2 f y|)
        = |deriv (A_eps_B P.p ε) (deriv f y)| * (jb y * |iteratedDeriv 2 f y|) := by ring
      _ ≤ (2 * K * ε) * K := mul_le_mul (hB' y) h4
          (mul_nonneg (hjb y).le (abs_nonneg _)) (mul_nonneg (by linarith) hε0)
      _ = 2 * K ^ 2 * ε := by ring
  have hwle : ∀ y, 0 ≤ y → jb y ^ (-1 / P.p) ≤ 1 := fun y _ => by
    rw [show -1 / P.p = -(1 / P.p) by ring]
    exact c07_aux_jb_rpow_neg_le_one y _ (by positivity)
  refine ⟨fun H hHY hHC => ?_, fun G hGC N hN => ?_⟩
  · have hd : ∀ y, deriv (fun y => b y * H y) y = deriv b y * H y + b y * deriv H y := fun y =>
      ((hbd y).differentiableAt.hasDerivAt.mul (hHC.differentiable one_ne_zero y).hasDerivAt).deriv
    have hC1 : ContDiff ℝ 1 (fun y => b y * H y) := hbC.mul hHC
    have hle : Y_gamma_norm P.p γ (fun y => b y * H y) ≤
        ENNReal.ofReal (1 + 6 * K ^ 2) * Y_gamma_norm P.p γ H := by
      refine c07_aux_Ynorm_le_mul P.p γ _ H _ (by positivity) (fun y hy => ?_) (fun y hy => ?_)
      · rw [hd]
        have e1 : |b y * H y| ≤ (1 + K ^ 2) * |H y| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb y) (abs_nonneg _)
        have e2 : jb y ^ (-1 / P.p) * |deriv b y * H y + b y * deriv H y| ≤
            2 * K ^ 2 * |H y| + (1 + K ^ 2) * (jb y ^ (-1 / P.p) * |deriv H y|) := by
          have := abs_add_le (deriv b y * H y) (b y * deriv H y)
          rw [abs_mul, abs_mul] at this
          have k1 := mul_le_mul_of_nonneg_left this (hnn y (-1 / P.p))
          have k2 := mul_le_mul_of_nonneg_right (hbp y hy) (abs_nonneg (H y))
          have k3 := mul_le_mul_of_nonneg_left (hb y)
            (mul_nonneg (hnn y (-1 / P.p)) (abs_nonneg (deriv H y)))
          have k4 : 2 * K ^ 2 * ε * |H y| ≤ 2 * K ^ 2 * |H y| := by
            have := mul_nonneg (sq_nonneg K) (abs_nonneg (H y)); nlinarith [hε.2]
          nlinarith
        have : |b y * H y| + jb y ^ (-1 / P.p) * |deriv b y * H y + b y * deriv H y| ≤
            (1 + 6 * K ^ 2) * (|H y| + jb y ^ (-1 / P.p) * |deriv H y|) := by
          have := mul_nonneg (hnn y (-1 / P.p)) (abs_nonneg (deriv H y))
          nlinarith [abs_nonneg (H y), sq_nonneg K]
        calc _ ≤ jb y ^ γ * ((1 + 6 * K ^ 2) * (|H y| + jb y ^ (-1 / P.p) * |deriv H y|)) :=
              mul_le_mul_of_nonneg_left this (hnn y γ)
          _ = _ := by ring
      · rw [hd]
        have e1 : |b y * H y| ≤ (1 + K ^ 2) * |H y| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb y) (abs_nonneg _)
        have e2 : jb y * |deriv b y * H y + b y * deriv H y| ≤
            2 * K ^ 2 * |H y| + (1 + K ^ 2) * (jb y * |deriv H y|) := by
          have := abs_add_le (deriv b y * H y) (b y * deriv H y)
          rw [abs_mul, abs_mul] at this
          have k1 := mul_le_mul_of_nonneg_left this (hjb y).le
          have k2 := mul_le_mul_of_nonneg_right (hbn y hy) (abs_nonneg (H y))
          have k3 := mul_le_mul_of_nonneg_left (hb y)
            (mul_nonneg (hjb y).le (abs_nonneg (deriv H y)))
          have k4 : 2 * K ^ 2 * ε * |H y| ≤ 2 * K ^ 2 * |H y| := by
            have := mul_nonneg (sq_nonneg K) (abs_nonneg (H y)); nlinarith [hε.2]
          nlinarith
        have : |b y * H y| + jb y * |deriv b y * H y + b y * deriv H y| ≤
            (1 + 6 * K ^ 2) * (|H y| + jb y * |deriv H y|) := by
          have := mul_nonneg (hjb y).le (abs_nonneg (deriv H y))
          nlinarith [abs_nonneg (H y), sq_nonneg K]
        calc _ ≤ jb y ^ γ * ((1 + 6 * K ^ 2) * (|H y| + jb y * |deriv H y|)) :=
              mul_le_mul_of_nonneg_left this (hnn y γ)
          _ = _ := by ring
    exact ⟨⟨hC1.locallyLipschitz, lt_of_le_of_lt hle
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hHY.2)⟩, hC1, hle⟩
  · have hN0 : 0 ≤ N := le_trans (by
      have := hnn 0 (γ + 1); positivity) (hN 0)
    have hd : ∀ y, deriv (fun y => (b y - 1) * G y) y =
        deriv b y * G y + (b y - 1) * deriv G y := fun y =>
      (((hbd y).differentiableAt.hasDerivAt.sub_const 1).mul
        (hGC.differentiable one_ne_zero y).hasDerivAt).deriv
    have hG1 : ∀ y, jb y ^ γ * (|G y| + |deriv G y|) ≤ N := fun y => by
      have h := hN y
      have : jb y ^ γ ≤ jb y ^ (γ + 1) :=
        Real.rpow_le_rpow_of_exponent_le (c07_aux_one_le_jb y) (by linarith)
      have := mul_le_mul_of_nonneg_right this (add_nonneg (abs_nonneg (G y)) (abs_nonneg (deriv G y)))
      linarith
    have hle := c07_aux_Ynorm_le_of_pointwise P.p γ (fun y => (b y - 1) * G y)
      (3 * K ^ 2 * ε * N) (3 * K ^ 2 * ε * N) (fun y hy => ?_) (fun y hy => ?_)
    · refine hle.trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : 0 ≤ ε * N := mul_nonneg hε0 hN0
      nlinarith
    · rw [hd]
      have k0 : |(b y - 1) * G y| ≤ K ^ 2 * ε * |G y| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb1 y) (abs_nonneg _)
      have k1 : jb y ^ (-1 / P.p) * |deriv b y * G y + (b y - 1) * deriv G y| ≤
          2 * K ^ 2 * ε * |G y| + K ^ 2 * ε * |deriv G y| := by
        have := abs_add_le (deriv b y * G y) ((b y - 1) * deriv G y)
        rw [abs_mul, abs_mul] at this
        have k1 := mul_le_mul_of_nonneg_left this (hnn y (-1 / P.p))
        have k2 := mul_le_mul_of_nonneg_right (hbp y hy) (abs_nonneg (G y))
        have k3 : jb y ^ (-1 / P.p) * (|b y - 1| * |deriv G y|) ≤ K ^ 2 * ε * |deriv G y| := by
          have := mul_le_mul (hwle y hy)
            (mul_le_mul_of_nonneg_right (hb1 y) (abs_nonneg (deriv G y)))
            (by positivity) zero_le_one
          linarith
        nlinarith
      have : |(b y - 1) * G y| + jb y ^ (-1 / P.p) * |deriv b y * G y + (b y - 1) * deriv G y| ≤
          3 * K ^ 2 * ε * (|G y| + |deriv G y|) := by
        have := mul_nonneg (mul_nonneg (sq_nonneg K) hε0) (abs_nonneg (deriv G y))
        nlinarith
      calc _ ≤ jb y ^ γ * (3 * K ^ 2 * ε * (|G y| + |deriv G y|)) :=
            mul_le_mul_of_nonneg_left this (hnn y γ)
        _ = 3 * K ^ 2 * ε * (jb y ^ γ * (|G y| + |deriv G y|)) := by ring
        _ ≤ 3 * K ^ 2 * ε * N := mul_le_mul_of_nonneg_left (hG1 y) (by positivity)
    · rw [hd]
      have k0 : |(b y - 1) * G y| ≤ K ^ 2 * ε * |G y| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hb1 y) (abs_nonneg _)
      have k1 : jb y * |deriv b y * G y + (b y - 1) * deriv G y| ≤
          2 * K ^ 2 * ε * |G y| + K ^ 2 * ε * (jb y * |deriv G y|) := by
        have := abs_add_le (deriv b y * G y) ((b y - 1) * deriv G y)
        rw [abs_mul, abs_mul] at this
        have k1 := mul_le_mul_of_nonneg_left this (hjb y).le
        have k2 := mul_le_mul_of_nonneg_right (hbn y hy) (abs_nonneg (G y))
        have k3 := mul_le_mul_of_nonneg_left (hb1 y) (mul_nonneg (hjb y).le (abs_nonneg (deriv G y)))
        nlinarith
      have hj1 := c07_aux_one_le_jb y
      have : |(b y - 1) * G y| + jb y * |deriv b y * G y + (b y - 1) * deriv G y| ≤
          3 * K ^ 2 * ε * (jb y * (|G y| + |deriv G y|)) := by
        have := mul_nonneg (mul_nonneg (sq_nonneg K) hε0) (abs_nonneg (G y))
        have := mul_nonneg (mul_nonneg (sq_nonneg K) hε0) (mul_nonneg (hjb y).le (abs_nonneg (deriv G y)))
        have : K ^ 2 * ε * |G y| ≤ K ^ 2 * ε * (jb y * |G y|) := by
          have := mul_le_mul_of_nonneg_right hj1 (abs_nonneg (G y))
          exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (sq_nonneg K) hε0)
        nlinarith
      have hw : jb y ^ γ * jb y = jb y ^ (γ + 1) := by
        rw [Real.rpow_add (hjb y), Real.rpow_one]
      calc _ ≤ jb y ^ γ * (3 * K ^ 2 * ε * (jb y * (|G y| + |deriv G y|))) :=
            mul_le_mul_of_nonneg_left this (hnn y γ)
        _ = 3 * K ^ 2 * ε * (jb y ^ (γ + 1) * (|G y| + |deriv G y|)) := by rw [← hw]; ring
        _ ≤ 3 * K ^ 2 * ε * N := mul_le_mul_of_nonneg_left (hN y) (by positivity)

/-- Blueprint: lem:c07_residual_Y.  For every admissible `γ`:
`ℰ_ε(f̄_{ε,μ}) ∈ Y_γ ∩ C¹`, `‖ℰ_ε(f̄_{ε,μ}) - G_μ‖_{Y_γ} ≤ Cε`, `‖ℰ_ε(f̄_{ε,μ})‖_{Y_γ} ≤ C`. -/
theorem c07_residual_Y (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R → ∀ γ : ℝ, P.admissible γ →
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
      residual P.p ε (approximate_solution_family P.p R ε μ) ∈ Y_gamma P.p γ ∧
      ContDiff ℝ 1 (residual P.p ε (approximate_solution_family P.p R ε μ)) ∧
      Y_gamma_norm P.p γ (fun y => residual P.p ε (approximate_solution_family P.p R ε μ) y -
        G_mu P.p μ y) ≤ ENNReal.ofReal (C * ε) ∧
      Y_gamma_norm P.p γ (residual P.p ε (approximate_solution_family P.p R ε μ)) ≤
        ENNReal.ofReal C := by
  intro δ hδ hδ'
  have hmu : mu_star P.p ≠ 0 := (c07_G_mu_properties P).1
  obtain ⟨Rt, et, -, het, het1, hT⟩ := c07_tilde_residual_Y P δ hδ hδ'
  obtain ⟨Ru, eu, -, heu, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  obtain ⟨Rd, ed, -, hed, -, hSp⟩ := c07_residual_split P δ hδ hδ'
  obtain ⟨Ra, ea, -, hea, -, hA⟩ := approx_residual_compact P δ hδ hδ'
  refine ⟨max Rt (max Ru (max Rd (max Ra 1))), min et (min eu (min ed ea)), by simp,
    by simp [*], (min_le_left _ _).trans het1, fun R hR γ hγ => ?_⟩
  have hRt : Rt ≤ R := le_trans (by simp) hR
  have hRu : Ru ≤ R := le_trans (by simp) hR
  have hRd : Rd ≤ R := le_trans (by simp) hR
  have hRa : Ra ≤ R := le_trans (by simp) hR
  have hγ0 : 0 < γ := by
    have h1 : 0 < beta P.p := by unfold beta; have := P.hp_lo; positivity
    have h2 : 0 < 1 / P.p := by have := P.hp_lo; positivity
    linarith [hγ.1]
  obtain ⟨Ct, hCt, hT'⟩ := hT R hRt γ hγ
  obtain ⟨K₀, hK₀, hU'⟩ := hU R hRu
  obtain ⟨CB, hCB, hBc⟩ := c07_B_conversion P K₀ hK₀
  obtain ⟨CG, hCG, hGp⟩ := (c07_G_mu_properties P).2.2.2.2 γ hγ0 (γ + 1) (by linarith)
  refine ⟨CB * Ct + CB * CG + CG, by positivity, fun ε hε μ hμ => ?_⟩
  have hεt : ε ∈ Icc (0 : ℝ) et := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεu : ε ∈ Icc (0 : ℝ) eu := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεd : ε ∈ Icc (0 : ℝ) ed := ⟨hε.1, hε.2.trans (by simp)⟩
  have hεa : ε ∈ Icc (0 : ℝ) ea := ⟨hε.1, hε.2.trans (by simp)⟩
  have hε1 : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hεt.2.trans het1⟩
  set f := approximate_solution_family P.p R ε μ with hf_def
  set G := G_mu P.p μ with hG_def
  set H : ℝ → ℝ := fun y => c07_divided_residual P.p ε f y - G y with hH_def
  set B : ℝ → ℝ := fun y => A_eps_B P.p ε (deriv f y) with hB_def
  obtain ⟨hHY, hHn⟩ := hT' ε hεt μ hμ
  obtain ⟨Ca, -, hA'⟩ := hA R hRa
  have hHC : ContDiff ℝ 1 H := (hA' ε hεa μ hμ).1
  have hfP := (hU' ε hεu μ hμ).1
  obtain ⟨hfsm, L, hL⟩ := (hSp R hRd ε hεd μ hμ).1 f (by simp [hf_def])
  have hres : ∀ y, residual P.p ε f y = B y * H y + B y * G y := by
    intro y
    rw [(c07_divided_residual_identity P.p (by linarith [P.hp_lo]) P.hp_hi ε hε1 f
      (hfsm.of_le (by simp)) ⟨L, hL⟩ y).2.2.2.2.2.2.2]
    simp only [hH_def, hB_def]
    ring
  obtain ⟨hGbd, hGY, hGn, -, -⟩ := hGp μ μ
  obtain ⟨φ, hφ⟩ := ((c07_G_mu_properties P).2.1 μ).2.2.2.2.2
  have hGC : ContDiff ℝ 1 G := by
    have : G = φ := funext fun x => (hφ x).symm
    rw [this]; exact φ.smooth 1
  obtain ⟨hBH_Y, hBH_C, hBH_n⟩ := (hBc γ hγ0 ε hε1 f hfP).1 H hHY hHC
  obtain ⟨hBG_Y, hBG_C, -⟩ := (hBc γ hγ0 ε hε1 f hfP).1 G hGY hGC
  set m := ‖1 - μ / mu_star P.p‖ with hm_def
  have hm0 : 0 ≤ m := norm_nonneg _
  have hm : m ≤ 1 := by
    rw [hm_def, one_sub_div hmu, norm_div, div_le_one (norm_pos_iff.2 hmu)]
    have : ‖mu_star P.p - μ‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact hμ
    linarith
  have hBG2 := (hBc γ hγ0 ε hε1 f hfP).2 G hGC (CG * m) hGbd
  have hdecomp : (fun y => residual P.p ε f y - G y) = fun y => B y * H y + (B y - 1) * G y := by
    funext y; rw [hres]; ring
  have hD1 : Differentiable ℝ (fun y => B y * H y) := hBH_C.differentiable one_ne_zero
  have hD2 : Differentiable ℝ (fun y => (B y - 1) * G y) := by
    have : (fun y => (B y - 1) * G y) = fun y => B y * G y - G y := by funext y; ring
    rw [this]; exact (hBG_C.differentiable one_ne_zero).sub (hGC.differentiable one_ne_zero)
  have hnorm1 : Y_gamma_norm P.p γ (fun y => residual P.p ε f y - G y) ≤
      ENNReal.ofReal ((CB * Ct + CB * CG) * ε) := by
    rw [hdecomp]
    refine (c07_aux_Ynorm_add_le _ _ _ _ hD1 hD2).trans ?_
    have h1 : CB * ε * (CG * m) ≤ CB * ε * CG := by
      have := mul_nonneg (mul_nonneg hCB.le hε.1) hCG.le; nlinarith
    calc _ ≤ ENNReal.ofReal CB * ENNReal.ofReal (Ct * ε) +
          ENNReal.ofReal (CB * ε * (CG * m)) := add_le_add (hBH_n.trans (by gcongr)) hBG2
      _ ≤ ENNReal.ofReal (CB * (Ct * ε)) + ENNReal.ofReal (CB * ε * CG) := by
          rw [← ENNReal.ofReal_mul hCB.le]
          exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal h1)
      _ = ENNReal.ofReal ((CB * Ct + CB * CG) * ε) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hCB.le (mul_nonneg hCt.le hε.1)) (mul_nonneg (mul_nonneg hCB.le hε.1) hCG.le)]
          ring_nf
  have hres' : residual P.p ε f = fun y => B y * H y + B y * G y := funext hres
  have hCres : ContDiff ℝ 1 (residual P.p ε f) := by rw [hres']; exact hBH_C.add hBG_C
  have hnorm2 : Y_gamma_norm P.p γ (residual P.p ε f) ≤
      ENNReal.ofReal (CB * Ct + CB * CG + CG) := by
    have he : residual P.p ε f = fun y => (residual P.p ε f y - G y) + G y := by
      funext y; ring
    rw [he]
    refine (c07_aux_Ynorm_add_le _ _ _ _
      ((hCres.differentiable one_ne_zero).sub (hGC.differentiable one_ne_zero))
      (hGC.differentiable one_ne_zero)).trans ?_
    refine (add_le_add hnorm1 hGn).trans ?_
    rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) hε.1) (mul_nonneg hCG.le hm0)]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ CB * Ct + CB * CG := by positivity
    nlinarith [hε1.2]
  refine ⟨⟨hCres.locallyLipschitz, lt_of_le_of_lt hnorm2 ENNReal.ofReal_lt_top⟩, hCres,
    hnorm1.trans (ENNReal.ofReal_le_ofReal ?_), hnorm2⟩
  nlinarith [hε.1, hCG]

/-- Blueprint: lem:c07_residual_continuity_C1loc.  For fixed `ε`, `μ ↦ ℰ̃_ε(f̄_{ε,μ})` and
`μ ↦ ℰ_ε(f̄_{ε,μ})` are continuous from `B̄` into `C¹_loc`. -/
theorem c07_residual_continuity_C1loc (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ μ ∈ Bbar P.p δ,
        c07_TendstoCkLoc 1
          (fun ν => c07_divided_residual P.p ε (approximate_solution_family P.p R ε ν))
          (nhdsWithin μ (Bbar P.p δ))
          (c07_divided_residual P.p ε (approximate_solution_family P.p R ε μ)) ∧
        c07_TendstoCkLoc 1
          (fun ν => residual P.p ε (approximate_solution_family P.p R ε ν))
          (nhdsWithin μ (Bbar P.p δ))
          (residual P.p ε (approximate_solution_family P.p R ε μ)) := by
  intro δ hδ hδ'
  obtain ⟨R1, e1, hR1, he1, he11, hC⟩ := c07_family_continuity P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hU⟩ := c07_family_uniform_bounds P δ hδ hδ'
  refine ⟨max R1 R2, min e1 e2, le_trans hR1 (le_max_left _ _), lt_min he1 he2,
    (min_le_left _ _).trans he11, fun R hR ε hε μ hμ => ?_⟩
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hε1 : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hεone : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1, hε1.2.trans he11⟩
  obtain ⟨K₀, hK₀, hU'⟩ := hU R (le_trans (le_max_right _ _) hR)
  set Bs := Bbar P.p δ with hBs
  set F : ℂ → ℝ → ℝ := fun ν => approximate_solution_family P.p R ε ν with hF
  have hP : ∀ ν ∈ Bs, F ν ∈ c07_profile_class P.p K₀ := fun ν hν => (hU' ε hε2 ν hν).1
  have hconv : c07_TendstoCkLoc 2 F (𝓝[Bs] μ) (F μ) :=
    hC R (le_trans (le_max_left _ _) hR) ε hε1 2 μ hμ
  have hevB : ∀ᶠ ν in 𝓝[Bs] μ, ν ∈ Bs := self_mem_nhdsWithin
  have hAC := c07_aux_A_eps_contDiff P.p ε hε.1
  have hkC1 := (c07_kernel_C1 P).1
  set T : ℂ → ℝ → ℝ := fun ν => c07_kernel_operator P.p (A_eps P.p ε) (F ν) with hT
  have hTC : ∀ ν ∈ Bs, ContDiff ℝ 1 (T ν) := fun ν hν =>
    (hkC1 K₀ hK₀ (F ν) (hP ν hν) (A_eps P.p ε) hAC).2.1
  -- helper: bounds of continuous functions on `[-M,M]`
  have hbd : ∀ (h : ℝ → ℝ), Continuous h → ∀ M : ℝ, ∃ A, ∀ x ∈ Icc (-M) M, |h x| ≤ A := by
    intro h hc M
    obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨A, fun x hx => by simpa [Real.norm_eq_abs] using hA x hx⟩
  have hid : ∀ M : ℝ, TendstoUniformlyOn (fun (_ : ℂ) (y : ℝ) => y) (fun y => y)
      (𝓝[Bs] μ) (Icc (-M) M) :=
    fun M s hs => Eventually.of_forall fun _ x _ => refl_mem_uniformity hs
  have hidb : ∀ M : ℝ, ∀ x ∈ Icc (-M) M, |x| ≤ M := fun M x hx => abs_le.2 ⟨hx.1, hx.2⟩
  -- (i) the kernel part
  have hTc : c07_TendstoCkLoc 1 T (𝓝[Bs] μ) (T μ) := by
    intro i hi M hM
    rw [tendstoUniformlyOn_iff_seq_tendstoUniformlyOn]
    intro u hu
    classical
    let v : ℕ → ℂ := fun n => if u n ∈ Bs then u n else μ
    have hvB : ∀ n, v n ∈ Bs := fun n => by
      by_cases h : u n ∈ Bs
      · simp only [v, h, ↓reduceIte]
      · simp only [v, h, ↓reduceIte]; exact hμ
    have huv : ∀ᶠ n in atTop, u n = v n :=
      (tendsto_nhdsWithin_iff.1 hu).2.mono fun n hn => by simp [v, hn]
    have hv : Tendsto v atTop (𝓝[Bs] μ) := hu.congr' huv
    have h2 : c07_TendstoCkLoc 2 (fun n => F (v n)) atTop (F μ) :=
      fun k hk M hM s hs => hv.eventually (hconv k hk M hM s hs)
    have hk := c07_kernel_continuity P K₀ hK₀ (A_eps P.p ε) hAC (fun n => F (v n)) (F μ)
      (fun n => hP _ (hvB n)) (hP μ hμ) h2 i hi M hM
    refine fun s hs => (hk s hs).mp (huv.mono fun n hn h => ?_)
    simp only [hT, hn]; exact h
  -- (ii) the local part `g = f - y f'`
  set g : ℂ → ℝ → ℝ := fun ν y => F ν y - y * deriv (F ν) y with hg
  have hD2 : ∀ ν ∈ Bs, ∀ y, HasDerivAt (deriv (F ν)) (iteratedDeriv 2 (F ν) y) y := by
    intro ν hν y
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (((hP ν hν).1.of_le (m := 2 + 1) (by norm_num)).deriv'.differentiable
      (by simp) y).hasDerivAt
  have hgd : ∀ ν ∈ Bs, ∀ y, HasDerivAt (g ν) (-(y * iteratedDeriv 2 (F ν) y)) y := by
    intro ν hν y
    have hd1 : HasDerivAt (F ν) (deriv (F ν) y) y :=
      ((hP ν hν).1.differentiable (by simp) y).hasDerivAt
    exact (hd1.sub ((hasDerivAt_id' y).mul (hD2 ν hν y))).congr_deriv (by ring)
  have hF2c : Continuous (iteratedDeriv 2 (F μ)) :=
    (hP μ hμ).1.continuous_iteratedDeriv 2 (by norm_num)
  have hF1c : Continuous (deriv (F μ)) := (hP μ hμ).1.continuous_deriv (by norm_num)
  have hgc : c07_TendstoCkLoc 1 g (𝓝[Bs] μ) (g μ) := by
    intro i hi M hM
    interval_cases i
    · simp only [iteratedDeriv_zero]
      have h0 := hconv 0 (by norm_num) M hM
      have h1 := hconv 1 (by norm_num) M hM
      simp only [iteratedDeriv_zero, iteratedDeriv_one] at h0 h1
      have hm := c07_aux_TUO_mul (hid M) h1 (max M K₀)
        (fun x hx => (hidb M x hx).trans (le_max_left _ _))
        (fun x _ => ((hP μ hμ).2 x).1.trans (le_max_right _ _))
      exact h0.sub hm
    · simp only [iteratedDeriv_one]
      have h2 := hconv 2 (by norm_num) M hM
      obtain ⟨A2, hA2⟩ := hbd _ hF2c M
      have hm := (c07_aux_TUO_mul (hid M) h2 (max M A2)
        (fun x hx => (hidb M x hx).trans (le_max_left _ _))
        (fun x hx => (hA2 x hx).trans (le_max_right _ _))).neg
      have hlim : deriv (g μ) = fun y => -(y * iteratedDeriv 2 (F μ) y) :=
        funext fun y => (hgd μ hμ y).deriv
      rw [hlim]
      refine hm.congr (hevB.mono fun ν hν x _ => ?_)
      simp only [Pi.neg_apply]
      exact ((hgd ν hν x).deriv).symm
  -- (iii) the divided residual
  have hEeq : ∀ ν ∈ Bs, c07_divided_residual P.p ε (F ν) = g ν + T ν := fun ν hν =>
    funext fun y => by
      rw [(c07_divided_residual_identity P.p hp P.hp_hi ε hεone (F ν)
        ((hP ν hν).1.of_le (by norm_num)) ⟨K₀, fun x => ((hP ν hν).2 x).1⟩ y).2.2.2.2.2.2.1]
      rfl
  have hEd : ∀ ν ∈ Bs, ∀ y, HasDerivAt (c07_divided_residual P.p ε (F ν))
      (deriv (g ν) y + deriv (T ν) y) y := fun ν hν y => by
    rw [hEeq ν hν]
    exact (hgd ν hν y).differentiableAt.hasDerivAt.add
      ((hTC ν hν).differentiable one_ne_zero y).hasDerivAt
  have hEc : c07_TendstoCkLoc 1 (fun ν => c07_divided_residual P.p ε (F ν)) (𝓝[Bs] μ)
      (c07_divided_residual P.p ε (F μ)) := by
    intro i hi M hM
    have hs := (hgc i hi M hM).add (hTc i hi M hM)
    have hadd : ∀ ν ∈ Bs, iteratedDeriv i (c07_divided_residual P.p ε (F ν)) =
        iteratedDeriv i (g ν) + iteratedDeriv i (T ν) := by
      intro ν hν
      interval_cases i
      · simp only [iteratedDeriv_zero]; exact hEeq ν hν
      · simp only [iteratedDeriv_one]; funext y; exact (hEd ν hν y).deriv
    rw [hadd μ hμ]
    exact hs.congr (hevB.mono fun ν hν x _ => by rw [hadd ν hν]; rfl)
  refine ⟨hEc, ?_⟩
  -- (iv) the residual `ℰ = B_ε(f') ℰ̃`
  set b : ℂ → ℝ → ℝ := fun ν y => A_eps_B P.p ε (deriv (F ν) y) with hb
  have hBC : ContDiff ℝ 2 (A_eps_B P.p ε) := by
    unfold A_eps_B
    exact ContDiff.rpow_const_of_ne (by fun_prop) fun u => by have := hε.1; positivity
  have hBc : Continuous (A_eps_B P.p ε) := hBC.continuous
  have hB'c : Continuous (deriv (A_eps_B P.p ε)) := hBC.continuous_deriv (by norm_num)
  have hbd' : ∀ ν ∈ Bs, ∀ y, HasDerivAt (b ν)
      (deriv (A_eps_B P.p ε) (deriv (F ν) y) * iteratedDeriv 2 (F ν) y) y := fun ν hν y =>
    (hBC.differentiable (by simp) _).hasDerivAt.comp y (hD2 ν hν y)
  have hReq : ∀ ν ∈ Bs, residual P.p ε (F ν) = b ν * c07_divided_residual P.p ε (F ν) :=
    fun ν hν => funext fun y => by
      rw [(c07_divided_residual_identity P.p hp P.hp_hi ε hεone (F ν)
        ((hP ν hν).1.of_le (by norm_num)) ⟨K₀, fun x => ((hP ν hν).2 x).1⟩ y).2.2.2.2.2.2.2]
      rfl
  have hRd : ∀ ν ∈ Bs, ∀ y, deriv (residual P.p ε (F ν)) y =
      deriv (A_eps_B P.p ε) (deriv (F ν) y) * iteratedDeriv 2 (F ν) y *
        c07_divided_residual P.p ε (F ν) y +
      b ν y * deriv (c07_divided_residual P.p ε (F ν)) y := fun ν hν y => by
    rw [hReq ν hν]
    exact ((hbd' ν hν y).mul (hEd ν hν y).differentiableAt.hasDerivAt).deriv
  have hEμc : Continuous (c07_divided_residual P.p ε (F μ)) := by
    rw [hEeq μ hμ]
    exact ((continuous_iff_continuousAt.2 fun y => (hgd μ hμ y).continuousAt)).add
      (hTC μ hμ).continuous
  have hE'μc : Continuous (deriv (c07_divided_residual P.p ε (F μ))) := by
    have : deriv (c07_divided_residual P.p ε (F μ)) =
        fun y => -(y * iteratedDeriv 2 (F μ) y) + deriv (T μ) y := by
      funext y; rw [(hEd μ hμ y).deriv, (hgd μ hμ y).deriv]
    rw [this]
    exact (continuous_id.mul hF2c).neg.add ((hTC μ hμ).continuous_deriv le_rfl)
  intro i hi M hM
  have h1 := hconv 1 (by norm_num) M hM
  have h2 := hconv 2 (by norm_num) M hM
  simp only [iteratedDeriv_one] at h1
  have hE0 := hEc 0 (by norm_num) M hM
  have hE1 := hEc 1 (by norm_num) M hM
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at hE0 hE1
  have hK : ∀ᶠ ν in 𝓝[Bs] μ, ∀ x ∈ Icc (-M) M, |deriv (F ν) x| ≤ K₀ :=
    hevB.mono fun ν hν x _ => ((hP ν hν).2 x).1
  have hKμ : ∀ x ∈ Icc (-M) M, |deriv (F μ) x| ≤ K₀ := fun x _ => ((hP μ hμ).2 x).1
  have hb0 := c07_aux_TUO_comp (A_eps_B P.p ε) hBc K₀ h1 hK hKμ
  have hb1 := c07_aux_TUO_comp (deriv (A_eps_B P.p ε)) hB'c K₀ h1 hK hKμ
  obtain ⟨Ab, hAb⟩ := hbd _ (hBc.comp hF1c) M
  obtain ⟨Ab', hAb'⟩ := hbd _ (hB'c.comp hF1c) M
  obtain ⟨A2, hA2⟩ := hbd _ hF2c M
  obtain ⟨AE, hAE⟩ := hbd _ hEμc M
  obtain ⟨AE', hAE'⟩ := hbd _ hE'μc M
  interval_cases i
  · simp only [iteratedDeriv_zero]
    have hm := c07_aux_TUO_mul hb0 hE0 (max Ab AE)
      (fun x hx => (hAb x hx).trans (le_max_left _ _))
      (fun x hx => (hAE x hx).trans (le_max_right _ _))
    rw [hReq μ hμ]
    exact hm.congr (hevB.mono fun ν hν x _ => by rw [hReq ν hν]; rfl)
  · simp only [iteratedDeriv_one]
    have hbp := c07_aux_TUO_mul hb1 h2 (max Ab' A2)
      (fun x hx => (hAb' x hx).trans (le_max_left _ _))
      (fun x hx => (hA2 x hx).trans (le_max_right _ _))
    obtain ⟨Ap, hAp⟩ := hbd _ ((hB'c.comp hF1c).mul hF2c) M
    have hm1 := c07_aux_TUO_mul hbp hE0 (max Ap AE)
      (fun x hx => (hAp x hx).trans (le_max_left _ _))
      (fun x hx => (hAE x hx).trans (le_max_right _ _))
    have hm2 := c07_aux_TUO_mul hb0 hE1 (max Ab AE')
      (fun x hx => (hAb x hx).trans (le_max_left _ _))
      (fun x hx => (hAE' x hx).trans (le_max_right _ _))
    have hlim : deriv (residual P.p ε (F μ)) = fun y =>
        deriv (A_eps_B P.p ε) (deriv (F μ) y) * iteratedDeriv 2 (F μ) y *
          c07_divided_residual P.p ε (F μ) y +
        b μ y * deriv (c07_divided_residual P.p ε (F μ)) y := funext (hRd μ hμ)
    rw [hlim]
    exact (hm1.add hm2).congr (hevB.mono fun ν hν x _ => by rw [hRd ν hν x]; rfl)

/-- Wrapper for prop:appendix_convergence (chapter 03, `GSQG.appendix_convergence`), stated
verbatim; proved by the chapter 03 result. -/
theorem c07_ext_appendix_convergence (p γ γ' : ℝ) (hp : 0 < p) (hγ' : 0 < γ') (hγγ' : γ' < γ) :
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
      Glim ∈ Y_gamma p γ ∧ Tendsto (fun k => Y_gamma_norm p γ' (G k - Glim)) atTop (𝓝 0)) :=
  appendix_convergence p γ γ' hp hγ' hγγ'

/-- Blueprint: lem:c07_residual_continuity_Y.  For fixed `ε` and admissible `γ`,
`μ ↦ ℰ_ε(f̄_{ε,μ})` is continuous from `B̄` into `Y_γ` (norm topology). -/
theorem c07_residual_continuity_Y (P : parameters) :
    ∀ δ : ℝ, 0 < δ → δ ≤ ‖mu_star P.p‖ / 2 →
    ∃ R₀ ε₀ : ℝ, 1 ≤ R₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ ε ∈ Icc (0 : ℝ) ε₀, ∀ γ : ℝ, P.admissible γ → ∀ μ ∈ Bbar P.p δ,
        Tendsto (fun ν => Y_gamma_norm P.p γ (fun y =>
            residual P.p ε (approximate_solution_family P.p R ε ν) y -
              residual P.p ε (approximate_solution_family P.p R ε μ) y))
          (nhdsWithin μ (Bbar P.p δ)) (nhds 0) := by
  intro δ hδ hδ'
  obtain ⟨R1, e1, hR1, he1, he11, hY⟩ := c07_residual_Y P δ hδ hδ'
  obtain ⟨R2, e2, -, he2, -, hC⟩ := c07_residual_continuity_C1loc P δ hδ hδ'
  refine ⟨max R1 R2, min e1 e2, le_trans hR1 (le_max_left _ _), lt_min he1 he2,
    (min_le_left _ _).trans he11, fun R hR ε hε γ hγ μ hμ => ?_⟩
  have hε1 : ε ∈ Icc (0 : ℝ) e1 := ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hε2 : ε ∈ Icc (0 : ℝ) e2 := ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hp : 0 < P.p := by linarith [P.hp_lo]
  have hγ0 : 0 < γ := by
    have h1 : 0 < beta P.p := by unfold beta; positivity
    have h2 : 0 < 1 / P.p := by positivity
    linarith [hγ.1]
  have hγ'' : P.admissible ((γ + (2 * P.p + 1)) / 2) :=
    ⟨by linarith [hγ.1, hγ.2], by linarith [hγ.2]⟩
  obtain ⟨C, -, hYC⟩ := hY R (le_trans (le_max_left _ _) hR) _ hγ''
  have hcont := (hC R (le_trans (le_max_right _ _) hR) ε hε2 μ hμ).2
  set u : ℂ → ℝ → ℝ := fun ν => residual P.p ε (approximate_solution_family P.p R ε ν) with hu
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_nhdsWithin_iff.1 hx).2)
  rw [← tendsto_add_atTop_iff_nat N]
  have hxN : Tendsto (fun n => x (n + N)) atTop (𝓝[Bbar P.p δ] μ) :=
    (tendsto_add_atTop_iff_nat N).2 hx
  have hmem : ∀ n, x (n + N) ∈ Bbar P.p δ := fun n => hN _ (by omega)
  have hCu : ∀ ν ∈ Bbar P.p δ, ContDiff ℝ 1 (u ν) := fun ν hν => (hYC ε hε1 ν hν).2.1
  have key := (c07_ext_appendix_convergence P.p _ γ hp hγ0 (by linarith [hγ.2])).2
    (fun n => u (x (n + N))) (u μ) (fun n => (hYC ε hε1 _ (hmem n)).1)
    ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n => (hYC ε hε1 _ (hmem n)).2.2.2⟩
    (hYC ε hε1 μ hμ).1.1 (fun Rr => ?_)
  · exact key.2
  have h0 := hcont 0 (Nat.zero_le _) (max Rr 1) (by positivity)
  have h1 := hcont 1 le_rfl (max Rr 1) (by positivity)
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at h0 h1
  have h0' : TendstoUniformlyOn (fun n => u (x (n + N))) (u μ) atTop (Icc (-max Rr 1) (max Rr 1)) :=
    fun s hs => hxN.eventually (h0 s hs)
  have h1' : TendstoUniformlyOn (fun n => deriv (u (x (n + N)))) (deriv (u μ)) atTop
      (Icc (-max Rr 1) (max Rr 1)) :=
    fun s hs => hxN.eventually (h1 s hs)
  have := (c07_aux_eLpNorm_tendsto (le_max_left _ _) h0' fun n =>
      ((hCu _ (hmem n)).continuous.sub (hCu μ hμ).continuous).aestronglyMeasurable).add
    (c07_aux_eLpNorm_tendsto (le_max_left _ _) h1' fun n =>
      (((hCu _ (hmem n)).continuous_deriv le_rfl).sub
        ((hCu μ hμ).continuous_deriv le_rfl)).aestronglyMeasurable)
  rwa [add_zero] at this

/-- Blueprint: lem:approx_assembly (= the conclusion of thm:fixed_point_approximation).
There are `ε₀ > 0`, `δ > 0` and (the cutoff scale `R` of) the family
`f̄_{ε,μ} = approximate_solution_family p R ε μ` of def:approximate_solution_family,
`0 ≤ ε ≤ ε₀`, `μ ∈ B̄ = B̄(μ_*,δ)`, such that every `f̄_{ε,μ}` is `C^∞` and:
(1) `f̄(y) + y → 0` as `y → -∞`, `f̄(y) → 0` as `y → +∞`;
(2) for every `j` a uniform `C_j` with `|f̄| ≤ C_j⟨y⟩^{-p}`, `|∂^{j+1} f̄| ≤ C_j⟨y⟩^{-β+j/p}`
(`y ≥ 0`), `|∂^j(f̄ + y)| ≤ C_j⟨y⟩^{-p-j}` (`y ≤ 0`);
(3) for every admissible `γ`, `ℰ_ε(f̄) ∈ Y_γ` and `‖ℰ_ε(f̄) - G_μ‖_{Y_γ} ≤ C_γ ε`;
(4) for each `ε`, `μ ↦ f̄_{ε,μ}` is continuous into `C²_loc` (uniform convergence of
`∂^k`, `k ≤ 2`, on compacts), and `μ ↦ ℰ_ε(f̄_{ε,μ})` is continuous into `Y_γ` (every admissible
`γ`, norm topology) and into `C¹_loc`.
The remaining claims of the node (`μ_* ≠ 0` and the properties of `G_μ`) are
`approx_assembly_G_mu`. -/
theorem approx_assembly (P : parameters) :
    ∃ R₀ > 0, ∃ δ₀ > 0, ∀ R ≥ R₀, ∀ δ, 0 < δ → δ ≤ δ₀ →
      ∃ ε₀ > 0, fixed_point_approximation_statement P R δ ε₀ := by
  have hmu : mu_star P.p ≠ 0 := (c07_G_mu_properties P).1
  have hδ₀ : 0 < ‖mu_star P.p‖ / 2 := by positivity
  obtain ⟨R1, e1, -, he1, -, hS⟩ := c07_family_smooth P _ hδ₀ le_rfl
  obtain ⟨e2, ⟨he2, -⟩, R2, -, hB, -⟩ :=
    c07_ext_approx_profile_bounds P.p P.hp_lo P.hp_hi _ hδ₀ le_rfl
  obtain ⟨R3, e3, -, he3, -, hC2⟩ := c07_family_continuity P _ hδ₀ le_rfl
  obtain ⟨R4, e4, -, he4, -, hY⟩ := c07_residual_Y P _ hδ₀ le_rfl
  obtain ⟨R5, e5, -, he5, -, -⟩ := c07_residual_continuity_C1loc P _ hδ₀ le_rfl
  obtain ⟨R6, e6, -, he6, -, hCY⟩ := c07_residual_continuity_Y P _ hδ₀ le_rfl
  obtain ⟨R₀, h1, h2, h3, h4, h5, h6, hR₀⟩ : ∃ R₀ : ℝ, R1 ≤ R₀ ∧ R2 ≤ R₀ ∧ R3 ≤ R₀ ∧ R4 ≤ R₀ ∧
      R5 ≤ R₀ ∧ R6 ≤ R₀ ∧ 0 < R₀ :=
    ⟨max R1 (max R2 (max R3 (max R4 (max R5 (max R6 1))))), by simp, by simp, by simp, by simp,
      by simp, by simp, by simp⟩
  refine ⟨R₀, hR₀, ‖mu_star P.p‖ / 2, hδ₀, fun R hR δ hδ hδδ => ?_⟩
  obtain ⟨ε₀, k1, k2, k3, k4, k5, k6, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ ≤ e1 ∧ ε₀ ≤ e2 ∧ ε₀ ≤ e3 ∧ ε₀ ≤ e4 ∧
      ε₀ ≤ e5 ∧ ε₀ ≤ e6 ∧ 0 < ε₀ :=
    ⟨min e1 (min e2 (min e3 (min e4 (min e5 e6)))), by simp, by simp, by simp, by simp,
      by simp, by simp, by simp [*]⟩
  have hBB : Bbar P.p δ ⊆ Bbar P.p (‖mu_star P.p‖ / 2) :=
    Metric.closedBall_subset_closedBall hδδ
  have hl : ∀ μ, 𝓝[Bbar P.p δ] μ ≤ 𝓝[Bbar P.p (‖mu_star P.p‖ / 2)] μ :=
    fun μ => nhdsWithin_mono μ hBB
  have hE : ∀ e, ε₀ ≤ e → ∀ ε ∈ Icc (0 : ℝ) ε₀, ε ∈ Icc (0 : ℝ) e :=
    fun e he ε hε => ⟨hε.1, hε.2.trans he⟩
  refine ⟨ε₀, hε₀, hmu, ?_, ?_, ?_, ?_, ?_⟩
  · -- (0) smoothness
    intro ε hε μ hμ
    exact (hS R (h1.trans hR) ε (hE _ k1 ε hε) μ (hBB hμ)).1
  · -- (1) limits, from the profile bounds with `j = 0`
    intro ε hε μ hμ
    obtain ⟨C, -, hC⟩ := hB 0
    have hb := hC R (h2.trans hR) ε (hE _ k2 ε hε) μ (hBB hμ)
    have hp : 0 < P.p := by linarith [P.hp_lo]
    obtain ⟨hT, hBot⟩ := c07_aux_jb_rpow_tendsto P.p hp
    constructor
    · refine squeeze_zero_norm' ?_ (by simpa using hBot.const_mul C)
      filter_upwards [eventually_le_atBot 0] with y hy
      have := hb.2 y hy
      simpa [Real.norm_eq_abs] using this
    · refine squeeze_zero_norm' ?_ (by simpa using hT.const_mul C)
      filter_upwards [eventually_ge_atTop 0] with y hy
      simpa [Real.norm_eq_abs] using (hb.1 y hy).1
  · -- (2) symbol bounds
    intro j
    obtain ⟨C, hC0, hC⟩ := hB j
    exact ⟨C, hC0, fun ε hε μ hμ => hC R (h2.trans hR) ε (hE _ k2 ε hε) μ (hBB hμ)⟩
  · -- (3) residual bound
    intro γ hγ
    obtain ⟨C, hC0, hC⟩ := hY R (h4.trans hR) γ hγ
    refine ⟨C, hC0, fun ε hε μ hμ => ?_⟩
    obtain ⟨hmem, -, hnorm, -⟩ := hC ε (hE _ k4 ε hε) μ (hBB hμ)
    exact ⟨hmem, ENNReal.toReal_le_of_le_ofReal (by nlinarith [hε.1]) hnorm⟩
  · -- (4) continuity
    intro ε hε μ hμ
    refine ⟨fun K hK k hk => ?_, fun γ hγ => ?_⟩
    · obtain ⟨M, hM, hKM⟩ := c07_aux_compact_subset_Icc K hK
      exact c07_aux_TUO_restrict (hl μ) hKM
        (hC2 R (h3.trans hR) ε (hE _ k3 ε hε) 2 μ (hBB hμ) k hk M hM)
    · have := (hCY R (h6.trans hR) ε (hE _ k6 ε hε) γ hγ μ (hBB hμ)).mono_left (hl μ)
      have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
      exact h0

/-- Blueprint: lem:approx_assembly (the remaining claims).  `μ_* ≠ 0`; each `G_μ` is a real
Schwartz function (independent of `ε`: it has no `ε` argument) with
`Ĝ_μ(ξ) = (1-μ/μ_*) χ₊'(ξ)/ξ · e^{-iΦ₀(ξ)}` for `ξ > 0`, `Ĝ_μ(ξ) = conj Ĝ_μ(-ξ)` for `ξ < 0`;
and `G_{μ_*} = 0`. -/
theorem approx_assembly_G_mu (P : parameters) :
    mu_star P.p ≠ 0 ∧
    (∀ μ : ℂ,
      (∃ φ : SchwartzMap ℝ ℝ, ∀ x, φ x = G_mu P.p μ x) ∧
      (∀ ξ : ℝ, 0 < ξ → fourierT (fun x => (G_mu P.p μ x : ℂ)) ξ =
        (1 - μ / mu_star P.p) * ((deriv chiPlus ξ / ξ : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (Phi0 P.p ξ : ℂ)))) ∧
      (∀ ξ : ℝ, ξ < 0 → fourierT (fun x => (G_mu P.p μ x : ℂ)) ξ =
        (starRingEnd ℂ) (fourierT (fun x => (G_mu P.p μ x : ℂ)) (-ξ)))) ∧
    (∀ y : ℝ, G_mu P.p (mu_star P.p) y = 0) := by
  obtain ⟨h0, h1, -, h3, -⟩ := c07_G_mu_properties P
  exact ⟨h0, fun μ => ⟨(h1 μ).2.2.2.2.2, (h1 μ).1, (h1 μ).2.1⟩, h3⟩

end GSQG
