import GSQG.Definitions
import GSQG.AppendixAB.PhaseToolbox
import GSQG.AppendixAB.OscillatoryMultiplier

/-!
# §4: Analysis of the equation (blueprint ch. 03, first part)

* Hölder spaces `C^s(I)`, `C^s_loc(U)` (`c03_holder`, `c03_holder_norm`, `c03_holder_loc`),
  built on Mathlib's `HolderOnWith`.
* The kernel function `Γ_ε` and the semilinear form `ℐ_ε` of the profile equation;
  Proposition 4.1, Remark 4.2, Lemma 4.3.
* `c03_frac_kernel_formula` (the constant `calpha` and the singular-integral form of `|D|^p`).

The smoothness theorem (Theorem 3.5) is in `Sec4_Analysis/Smoothness.lean`; Appendices A–B are in
`AppendixAB/`. Helpers are named `c03_aux_*`.
-/

open MeasureTheory Set Filter Real
open scoped ENNReal NNReal Topology

noncomputable section

namespace GSQG

/-! ## Notation specific to this chapter -/

section Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



/-- Blueprint: def:c03_holder.  The Hölder norm `‖g‖_{C^s(I)}` (in `[0,∞]`), `s = k + θ`,
`k = ⌊s⌋`, `θ = s - k`:
`∑_{i≤k} sup_I |g^{(i)}| + sup_{x≠x'∈I} |g^{(k)}(x)-g^{(k)}(x')|/|x-x'|^θ`, where the Hölder
seminorm is written as the least `C` with `HolderOnWith C θ g^{(k)} I`. -/
def c03_holder_norm (s : ℝ) (I : Set ℝ) (g : ℝ → E) : ℝ≥0∞ :=
  c03_Ck_norm ⌊s⌋₊ I g +
    ⨅ (C : ℝ≥0) (_ : HolderOnWith C (Real.toNNReal (s - ⌊s⌋₊))
      (iteratedDerivWithin ⌊s⌋₊ g I) I), (C : ℝ≥0∞)

/-- Blueprint: def:c03_holder.  Real-valued Hölder norm. -/
def c03_holder_normR (s : ℝ) (I : Set ℝ) (g : ℝ → E) : ℝ := (c03_holder_norm s I g).toReal

/-- Blueprint: def:c03_holder.  `sup_I |g|` (real-valued; the `L^∞(I)` norm of a continuous `g`). -/
def c03_holder_supNorm (I : Set ℝ) (g : ℝ → E) : ℝ := (⨆ x ∈ I, ‖g x‖ₑ).toReal

/-- Blueprint: def:c03_holder.  `C^s(I) = {g ∈ C^k(I) : ‖g‖_{C^s(I)} < ∞}` (used for `s ∉ ℕ` and
`I` a compact interval, or `I = univ` for the global space `C^s(ℝ)`). -/
def c03_holder (s : ℝ) (I : Set ℝ) : Set (ℝ → E) :=
  {g | ContDiffOn ℝ ⌊s⌋₊ g I ∧ c03_holder_norm s I g < ⊤}

/-- Blueprint: def:c03_holder.  `C^s_loc(U)`: `g ∈ C^k(U)` with `g|_I ∈ C^s(I)` for every compact
interval `I ⊆ U`.  `C^s_loc = C^s_loc(ℝ)` is `c03_holder_loc s univ`. -/
def c03_holder_loc (s : ℝ) (U : Set ℝ) : Set (ℝ → E) :=
  {g | ContDiffOn ℝ ⌊s⌋₊ g U ∧ ∀ a b : ℝ, Icc a b ⊆ U → g ∈ c03_holder s (Icc a b)}

/-- Blueprint: def:c03_holder.  For `0 < s₀ < 1` every locally Lipschitz function is in
`C^{s₀}_loc`. -/
theorem c03_holder_loc_of_locallyLipschitz (s₀ : ℝ) (hs₀ : 0 < s₀) (hs₁ : s₀ < 1)
    (g : ℝ → E) (hg : LocallyLipschitz g) : g ∈ c03_holder_loc s₀ univ := by
  have hfl : ⌊s₀⌋₊ = 0 := Nat.floor_eq_zero.2 hs₁
  have hcont : Continuous g := hg.continuous
  refine ⟨by rw [hfl]; exact contDiffOn_zero.2 hcont.continuousOn, fun a b _ => ?_⟩
  refine ⟨by rw [hfl]; exact contDiffOn_zero.2 hcont.continuousOn, ?_⟩
  unfold c03_holder_norm c03_Ck_norm
  rw [hfl]
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, iteratedDerivWithin_zero,
    Nat.cast_zero, sub_zero]
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨K, hK⟩ := (hg.locallyLipschitzOn (s := Icc a b)).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  set D : ℝ≥0 := Real.toNNReal (b - a)
  have hD : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, edist x y ≤ D := by
    intro x hx y hy
    rw [edist_dist, Real.dist_eq]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩)
  have hθ : Real.toNNReal s₀ ≤ 1 := by
    rw [Real.toNNReal_le_one]; exact hs₁.le
  have hH := hK.holderOnWith.of_le hD hθ
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_) (ENNReal.ofReal_lt_top (r := C))
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC x hx)
  · exact lt_of_le_of_lt (iInf_le_of_le _ (iInf_le_of_le hH le_rfl)) ENNReal.coe_lt_top

end Holder

section HolderAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Criterion for `g ∈ C^s(I)`: `C^k` on `I`, bounded derivatives `≤ k`, Hölder `k`-th
derivative. -/
theorem c03_aux_holder_of (s : ℝ) (I : Set ℝ) (g : ℝ → E) (hg : ContDiffOn ℝ ⌊s⌋₊ g I)
    (hb : ∀ i ≤ ⌊s⌋₊, ∃ M : ℝ, ∀ x ∈ I, ‖iteratedDerivWithin i g I x‖ ≤ M)
    (hH : ∃ C : ℝ≥0, HolderOnWith C (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ g I) I) :
    g ∈ c03_holder s I := by
  refine ⟨hg, ?_⟩
  unfold c03_holder_norm c03_Ck_norm
  obtain ⟨C, hC⟩ := hH
  refine ENNReal.add_lt_top.2 ⟨ENNReal.sum_lt_top.2 fun i hi => ?_,
    lt_of_le_of_lt (iInf_le_of_le C (iInf_le_of_le hC le_rfl)) ENNReal.coe_lt_top⟩
  obtain ⟨M, hM⟩ := hb i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_) (ENNReal.ofReal_lt_top (r := M))
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hM x hx)

/-- Extraction of the bounds from `g ∈ C^s(I)`. -/
theorem c03_aux_holder_bounds (s : ℝ) (I : Set ℝ) (g : ℝ → E) (hg : g ∈ c03_holder s I) :
    (∀ i ≤ ⌊s⌋₊, ∃ M : ℝ, ∀ x ∈ I, ‖iteratedDerivWithin i g I x‖ ≤ M) ∧
    ∃ C : ℝ≥0, HolderOnWith C (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ g I) I := by
  have hn := hg.2
  unfold c03_holder_norm at hn
  obtain ⟨hC, hH⟩ := ENNReal.add_lt_top.1 hn
  obtain ⟨C, hC'⟩ := iInf_lt_iff.1 hH
  obtain ⟨hHC, -⟩ := iInf_lt_iff.1 hC'
  refine ⟨fun i hi => ?_, C, hHC⟩
  unfold c03_Ck_norm at hC
  have hi' := (ENNReal.sum_lt_top.1 hC) i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  refine ⟨(⨆ x ∈ I, ‖iteratedDerivWithin i g I x‖ₑ).toReal, fun x hx => ?_⟩
  have := le_iSup₂ (f := fun x _ => ‖iteratedDerivWithin i g I x‖ₑ) x hx
  rw [← ofReal_norm] at this
  exact (ENNReal.ofReal_le_iff_le_toReal hi'.ne).1 this

/-- `θ = s - ⌊s⌋ ≤ 1`. -/
theorem c03_aux_theta_le (s : ℝ) : Real.toNNReal (s - ⌊s⌋₊) ≤ 1 := by
  rw [Real.toNNReal_le_one]
  rcases le_or_gt 0 s with hs | hs
  · linarith [Nat.lt_floor_add_one s]
  · rw [Nat.floor_eq_zero.2 (by linarith)]; simp; linarith

/-- On a degenerate interval every function is in `C^s`. -/
theorem c03_aux_holder_degen (s : ℝ) (a b : ℝ) (hab : b ≤ a) (g : ℝ → E) (hg : ContDiffOn ℝ ⌊s⌋₊ g (Icc a b)) :
    g ∈ c03_holder s (Icc a b) := by
  have hsub : (Icc a b).Subsingleton := Set.subsingleton_Icc_of_ge hab
  refine c03_aux_holder_of s _ g hg (fun i _ => ⟨‖iteratedDerivWithin i g (Icc a b) a‖, fun x hx => ?_⟩)
    ⟨0, hsub.holderOnWith 0 _ _⟩
  have : x = a := le_antisymm (hx.2.trans hab) hx.1
  rw [this]

/-- Globally `C^{k+1}` functions are in `C^s(I)` (`k = ⌊s⌋`) for every compact interval. -/
theorem c03_aux_holder_smooth (s : ℝ) (g : ℝ → E) (hg : ContDiff ℝ (⌊s⌋₊ + 1) g) (a b : ℝ) :
    g ∈ c03_holder s (Icc a b) := by
  set k := ⌊s⌋₊
  have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast Nat.le_succ k)
  rcases le_or_gt b a with hab | hab
  · exact c03_aux_holder_degen s a b hab g hgk.contDiffOn
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ x ∈ Icc a b, iteratedDerivWithin i g (Icc a b) x = iteratedDeriv i g x :=
    fun i hi x hx => iteratedDerivWithin_eq_iteratedDeriv hU
      ((hgk.of_le (by exact_mod_cast hi)).contDiffAt) hx
  refine c03_aux_holder_of s _ g hgk.contDiffOn (fun i hi => ?_) ?_
  · obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      ((hgk.continuous_iteratedDeriv i (by exact_mod_cast hi)).continuousOn)
    exact ⟨M, fun x hx => by rw [heq i hi x hx]; exact hM x hx⟩
  · have hk1 : ContDiff ℝ 1 (iteratedDeriv k g) := by
      have := ContDiff.iterate_deriv' 1 k (f := g) (by
        have e : ((1 + k : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
        rw [e]; exact hg)
      rw [iteratedDeriv_eq_iterate]; exact_mod_cast this
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      ((hk1.continuous_deriv le_rfl).continuousOn)
    have hLip : LipschitzOnWith (Real.toNNReal M) (iteratedDeriv k g) (Icc a b) :=
      Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hk1.differentiable one_ne_zero x)
        (fun x hx => by
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact (hM x hx).trans (Real.le_coe_toNNReal M)) (convex_Icc a b)
    set D : ℝ≥0 := Real.toNNReal (b - a)
    have hD : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, edist x y ≤ D := by
      intro x hx y hy
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩)
    obtain ⟨C', hH⟩ : ∃ C' : ℝ≥0, HolderOnWith C' (Real.toNNReal (s - k)) (iteratedDeriv k g)
        (Icc a b) := ⟨_, hLip.holderOnWith.of_le hD (c03_aux_theta_le s)⟩
    refine ⟨C', fun x hx y hy => ?_⟩
    rw [heq k le_rfl x hx, heq k le_rfl y hy]
    exact hH x hx y hy

/-- Left composition with a continuous linear map of norm `≤ 1` preserves `C^s(I)`. -/
theorem c03_aux_holder_clm (s : ℝ) (a b : ℝ) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (g : ℝ → E)
    (hg : g ∈ c03_holder s (Icc a b)) : (fun x => L (g x)) ∈ c03_holder s (Icc a b) := by
  set k := ⌊s⌋₊
  have hc : ContDiffOn ℝ k (fun x => L (g x)) (Icc a b) := L.contDiff.comp_contDiffOn hg.1
  rcases le_or_gt b a with hab | hab
  · exact c03_aux_holder_degen s a b hab _ hc
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ x ∈ Icc a b, iteratedDerivWithin i (fun x => L (g x)) (Icc a b) x =
      L (iteratedDerivWithin i g (Icc a b) x) := by
    intro i hi x hx
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin]
    have := L.iteratedFDerivWithin_comp_left (hg.1 x hx) hU hx (i := i) (by exact_mod_cast hi)
    rw [show (fun x => L (g x)) = ⇑L ∘ g from rfl, this]
    rfl
  obtain ⟨hb, C, hC⟩ := c03_aux_holder_bounds s _ g hg
  refine c03_aux_holder_of s _ _ hc (fun i hi => ?_) ⟨C, fun x hx y hy => ?_⟩
  · obtain ⟨M, hM⟩ := hb i hi
    refine ⟨M, fun x hx => ?_⟩
    rw [heq i hi x hx]
    exact (L.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (hM x hx))
  · rw [heq k le_rfl x hx, heq k le_rfl y hy]
    refine le_trans ?_ (hC x hx y hy)
    have hLL : LipschitzWith ‖L‖₊ L := L.lipschitzWith
    refine (hLL.edist_le_mul _ _).trans ?_
    calc (‖L‖₊ : ℝ≥0∞) * edist _ _ ≤ 1 * edist (iteratedDerivWithin k g (Icc a b) x)
          (iteratedDerivWithin k g (Icc a b) y) := by
          gcongr
          exact_mod_cast hL
      _ = _ := one_mul _

/-- `C^s(I)` is closed under addition. -/
theorem c03_aux_holder_add (s : ℝ) (a b : ℝ) (g h : ℝ → E)
    (hg : g ∈ c03_holder s (Icc a b)) (hh : h ∈ c03_holder s (Icc a b)) :
    (fun x => g x + h x) ∈ c03_holder s (Icc a b) := by
  set k := ⌊s⌋₊
  have hc : ContDiffOn ℝ k (fun x => g x + h x) (Icc a b) := hg.1.add hh.1
  rcases le_or_gt b a with hab | hab
  · exact c03_aux_holder_degen s a b hab _ hc
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ x ∈ Icc a b, iteratedDerivWithin i (fun x => g x + h x) (Icc a b) x =
      iteratedDerivWithin i g (Icc a b) x + iteratedDerivWithin i h (Icc a b) x := by
    intro i hi x hx
    exact iteratedDerivWithin_add hx hU ((hg.1.of_le (by exact_mod_cast hi)) x hx)
      ((hh.1.of_le (by exact_mod_cast hi)) x hx)
  obtain ⟨hbg, Cg, hCg⟩ := c03_aux_holder_bounds s _ g hg
  obtain ⟨hbh, Ch, hCh⟩ := c03_aux_holder_bounds s _ h hh
  refine c03_aux_holder_of s _ _ hc (fun i hi => ?_) ⟨Cg + Ch, fun x hx y hy => ?_⟩
  · obtain ⟨M1, hM1⟩ := hbg i hi
    obtain ⟨M2, hM2⟩ := hbh i hi
    exact ⟨M1 + M2, fun x hx => by
      rw [heq i hi x hx]; exact (norm_add_le _ _).trans (add_le_add (hM1 x hx) (hM2 x hx))⟩
  · rw [heq k le_rfl x hx, heq k le_rfl y hy]
    refine (edist_add_add_le _ _ _ _).trans ?_
    rw [ENNReal.coe_add, add_mul]
    exact add_le_add (hCg x hx y hy) (hCh x hx y hy)

end HolderAux

/-! ## Hölder library: interval interpolation, products and compositions -/

section HolderAPI
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hölder seminorm `[g^{(k)}]_{C^θ(I)}` (in `[0,∞]`), `k = ⌊s⌋`, `θ = s - k`. -/
def c03_aux_semi (s : ℝ) (I : Set ℝ) (g : ℝ → E) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : HolderOnWith C (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ g I) I),
    (C : ℝ≥0∞)

/-- `sup_I ‖g^{(i)}‖` (in `[0,∞]`). -/
def c03_aux_supD (i : ℕ) (I : Set ℝ) (g : ℝ → E) : ℝ≥0∞ :=
  ⨆ x ∈ I, ‖iteratedDerivWithin i g I x‖ₑ

theorem c03_aux_norm_eq (s : ℝ) (I : Set ℝ) (g : ℝ → E) :
    c03_holder_norm s I g =
      ∑ i ∈ Finset.range (⌊s⌋₊ + 1), c03_aux_supD i I g + c03_aux_semi s I g := rfl

theorem c03_aux_holderOnWith_of_dist {F : Type*} [PseudoMetricSpace F] {f : ℝ → F} {s : Set ℝ}
    {C r : ℝ≥0} (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C * dist x y ^ (r : ℝ)) :
    HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

theorem c03_aux_holderOnWith_iInf {F : Type*} [PseudoMetricSpace F] {f : ℝ → F} {s : Set ℝ}
    {r : ℝ≥0} (hfin : (⨅ (C : ℝ≥0) (_ : HolderOnWith C r f s), (C : ℝ≥0∞)) ≠ ⊤) :
    HolderOnWith (⨅ (C : ℝ≥0) (_ : HolderOnWith C r f s), (C : ℝ≥0∞)).toNNReal r f s := by
  intro x hx y hy
  rw [ENNReal.coe_toNNReal hfin]
  by_cases hxy : x = y
  · simp [hxy]
  have h₁ : edist x y ^ (r : ℝ) ≠ 0 :=
    (Ne.symm <| ne_of_lt <| ENNReal.rpow_pos (edist_pos.2 hxy) (edist_lt_top x y).ne)
  have h₂ : edist x y ^ (r : ℝ) ≠ ⊤ := by
    simp [(edist_lt_top x y).ne]
  rw [← ENNReal.div_le_iff h₁ h₂]
  refine le_iInf₂ fun C hC => ?_
  rw [ENNReal.div_le_iff h₁ h₂]
  exact hC x hx y hy

theorem c03_aux_semi_lt_top {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) :
    c03_aux_semi s I g < ⊤ :=
  lt_of_le_of_lt le_add_self hg.2

theorem c03_aux_supD_lt_top {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) {i : ℕ}
    (hi : i ≤ ⌊s⌋₊) : c03_aux_supD i I g < ⊤ := by
  have h1 : ∑ j ∈ Finset.range (⌊s⌋₊ + 1), c03_aux_supD j I g < ⊤ :=
    lt_of_le_of_lt le_self_add hg.2
  exact (ENNReal.sum_lt_top.1 h1) i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- The top derivative is Hölder with constant the seminorm. -/
theorem c03_aux_semi_holder {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) :
    HolderOnWith (c03_aux_semi s I g).toNNReal (Real.toNNReal (s - ⌊s⌋₊))
      (iteratedDerivWithin ⌊s⌋₊ g I) I :=
  c03_aux_holderOnWith_iInf (c03_aux_semi_lt_top hg).ne

theorem c03_aux_le_supD {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) {i : ℕ}
    (hi : i ≤ ⌊s⌋₊) {x : ℝ} (hx : x ∈ I) :
    ‖iteratedDerivWithin i g I x‖ ≤ (c03_aux_supD i I g).toReal := by
  have := le_iSup₂ (f := fun x _ => ‖iteratedDerivWithin i g I x‖ₑ) x hx
  rw [← ofReal_norm] at this
  exact (ENNReal.ofReal_le_iff_le_toReal (c03_aux_supD_lt_top hg hi).ne).1 this

theorem c03_aux_normR_eq {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) :
    c03_holder_normR s I g =
      ∑ i ∈ Finset.range (⌊s⌋₊ + 1), (c03_aux_supD i I g).toReal + (c03_aux_semi s I g).toReal := by
  unfold c03_holder_normR
  rw [c03_aux_norm_eq, ENNReal.toReal_add (ENNReal.sum_lt_top.2 fun i hi =>
      c03_aux_supD_lt_top hg (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).ne
    (c03_aux_semi_lt_top hg).ne, ENNReal.toReal_sum fun i hi =>
      (c03_aux_supD_lt_top hg (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).ne]

theorem c03_aux_supD_le_normR {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) {i : ℕ}
    (hi : i ≤ ⌊s⌋₊) : (c03_aux_supD i I g).toReal ≤ c03_holder_normR s I g := by
  rw [c03_aux_normR_eq hg]
  refine le_add_of_le_of_nonneg ?_ ENNReal.toReal_nonneg
  exact Finset.single_le_sum (f := fun j => (c03_aux_supD j I g).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

theorem c03_aux_semi_le_normR {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) :
    (c03_aux_semi s I g).toReal ≤ c03_holder_normR s I g := by
  rw [c03_aux_normR_eq hg]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

theorem c03_aux_le_normR {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) {i : ℕ}
    (hi : i ≤ ⌊s⌋₊) {x : ℝ} (hx : x ∈ I) :
    ‖iteratedDerivWithin i g I x‖ ≤ c03_holder_normR s I g :=
  (c03_aux_le_supD hg hi hx).trans (c03_aux_supD_le_normR hg hi)

theorem c03_aux_supNorm_eq (I : Set ℝ) (g : ℝ → E) :
    c03_holder_supNorm I g = (c03_aux_supD 0 I g).toReal := by
  simp [c03_holder_supNorm, c03_aux_supD, iteratedDerivWithin_zero]

theorem c03_aux_le_supNorm {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) {x : ℝ}
    (hx : x ∈ I) : ‖g x‖ ≤ c03_holder_supNorm I g := by
  have := c03_aux_le_supD hg (Nat.zero_le _) hx
  rwa [iteratedDerivWithin_zero, ← c03_aux_supNorm_eq] at this

theorem c03_aux_supNorm_le_normR {s : ℝ} {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) :
    c03_holder_supNorm I g ≤ c03_holder_normR s I g := by
  rw [c03_aux_supNorm_eq]; exact c03_aux_supD_le_normR hg (Nat.zero_le _)

theorem c03_aux_supNorm_nonneg (I : Set ℝ) (g : ℝ → E) : 0 ≤ c03_holder_supNorm I g :=
  ENNReal.toReal_nonneg

theorem c03_aux_normR_nonneg (s : ℝ) (I : Set ℝ) (g : ℝ → E) : 0 ≤ c03_holder_normR s I g :=
  ENNReal.toReal_nonneg

/-- Bounds on the derivatives and a Hölder constant give membership and a norm bound. -/
theorem c03_aux_normR_le (s : ℝ) (I : Set ℝ) (g : ℝ → E) (hg : ContDiffOn ℝ ⌊s⌋₊ g I)
    (A : ℕ → ℝ) (hA0 : ∀ i ≤ ⌊s⌋₊, 0 ≤ A i)
    (hA : ∀ i ≤ ⌊s⌋₊, ∀ x ∈ I, ‖iteratedDerivWithin i g I x‖ ≤ A i) (B : ℝ≥0)
    (hB : HolderOnWith B (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ g I) I) :
    g ∈ c03_holder s I ∧
      c03_holder_normR s I g ≤ ∑ i ∈ Finset.range (⌊s⌋₊ + 1), A i + B := by
  have hle : c03_holder_norm s I g ≤
      ENNReal.ofReal (∑ i ∈ Finset.range (⌊s⌋₊ + 1), A i + B) := by
    rw [c03_aux_norm_eq, ENNReal.ofReal_add (Finset.sum_nonneg fun i hi =>
      hA0 i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) B.coe_nonneg,
      ENNReal.ofReal_sum_of_nonneg fun i hi => hA0 i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
      ENNReal.ofReal_coe_nnreal]
    refine add_le_add (Finset.sum_le_sum fun i hi => iSup₂_le fun x hx => ?_)
      (iInf_le_of_le B (iInf_le_of_le hB le_rfl))
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hA i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) x hx)
  refine ⟨⟨hg, lt_of_le_of_lt hle ENNReal.ofReal_lt_top⟩, ?_⟩
  unfold c03_holder_normR
  exact (ENNReal.toReal_le_of_le_ofReal (add_nonneg (Finset.sum_nonneg fun i hi =>
      hA0 i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) B.coe_nonneg) hle)

end HolderAPI

/-- Blueprint: lem:c03_holder_product_base.  For `0 < θ < 1`, `‖uv‖_{C^θ(I)} ≤
‖u‖_∞ ‖v‖_{C^θ(I)} + ‖v‖_∞ ‖u‖_{C^θ(I)}`. -/
theorem c03_holder_product_base (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (a b : ℝ) (hab : a ≤ b)
    (u v : ℝ → ℂ) (hu : u ∈ c03_holder θ (Icc a b)) (hv : v ∈ c03_holder θ (Icc a b)) :
    (u * v) ∈ c03_holder θ (Icc a b) ∧
    c03_holder_normR θ (Icc a b) (u * v) ≤
      c03_holder_supNorm (Icc a b) u * c03_holder_normR θ (Icc a b) v +
        c03_holder_supNorm (Icc a b) v * c03_holder_normR θ (Icc a b) u := by
  have hk : ⌊θ⌋₊ = 0 := Nat.floor_eq_zero.2 hθ1
  set I := Icc a b
  set Su := c03_holder_supNorm I u
  set Sv := c03_holder_supNorm I v
  set Bu := (c03_aux_semi θ I u).toNNReal
  set Bv := (c03_aux_semi θ I v).toNNReal
  have hHu := c03_aux_semi_holder hu
  have hHv := c03_aux_semi_holder hv
  rw [hk, iteratedDerivWithin_zero] at hHu hHv
  have hSu : ∀ x ∈ I, ‖u x‖ ≤ Su := fun x hx => c03_aux_le_supNorm hu hx
  have hSv : ∀ x ∈ I, ‖v x‖ ≤ Sv := fun x hx => c03_aux_le_supNorm hv hx
  have hSu0 : 0 ≤ Su := c03_aux_supNorm_nonneg _ _
  have hSv0 : 0 ≤ Sv := c03_aux_supNorm_nonneg _ _
  have hcd : ContDiffOn ℝ ⌊θ⌋₊ (u * v) I := by
    rw [hk]; exact contDiffOn_zero.2 ((contDiffOn_zero.1 (hk ▸ hu.1)).mul (contDiffOn_zero.1 (hk ▸ hv.1)))
  have hH : HolderOnWith (Su.toNNReal * Bv + Sv.toNNReal * Bu) (Real.toNNReal (θ - ⌊θ⌋₊))
      (iteratedDerivWithin ⌊θ⌋₊ (u * v) I) I := by
    rw [hk, iteratedDerivWithin_zero]
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    have e : (u * v) x - (u * v) y = u x * (v x - v y) + v y * (u x - u y) := by
      simp only [Pi.mul_apply]; ring
    rw [dist_eq_norm, e]
    have h1 := hHv.dist_le hx hy
    have h2 := hHu.dist_le hx hy
    rw [dist_eq_norm] at h1 h2
    have hd : 0 ≤ dist x y ^ ((Real.toNNReal (θ - ↑0) : ℝ)) := Real.rpow_nonneg dist_nonneg _
    calc ‖u x * (v x - v y) + v y * (u x - u y)‖
        ≤ ‖u x‖ * ‖v x - v y‖ + ‖v y‖ * ‖u x - u y‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ Su * (Bv * dist x y ^ ((Real.toNNReal (θ - ↑0) : ℝ))) +
          Sv * (Bu * dist x y ^ ((Real.toNNReal (θ - ↑0) : ℝ))) := by
          gcongr
          · exact hSu x hx
          · exact h1
          · exact hSv y hy
          · exact h2
      _ = _ := by
          push_cast [Real.coe_toNNReal _ hSu0, Real.coe_toNNReal _ hSv0]; ring
  have hA0 : ∀ i ≤ ⌊θ⌋₊, (0:ℝ) ≤ (fun _ => Su * Sv) i := fun _ _ => mul_nonneg hSu0 hSv0
  have hA : ∀ i ≤ ⌊θ⌋₊, ∀ x ∈ I, ‖iteratedDerivWithin i (u * v) I x‖ ≤ (fun _ => Su * Sv) i := by
    intro i hi x hx
    rw [hk, Nat.le_zero] at hi
    subst hi
    rw [iteratedDerivWithin_zero, Pi.mul_apply, norm_mul]
    exact mul_le_mul (hSu x hx) (hSv x hx) (norm_nonneg _) hSu0
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le θ I (u * v) hcd _ hA0 hA _ hH
  refine ⟨hmem, hle.trans ?_⟩
  rw [hk, c03_aux_normR_eq hu, c03_aux_normR_eq hv, hk]
  simp only [zero_add, Finset.range_one, Finset.sum_singleton]
  rw [← c03_aux_supNorm_eq, ← c03_aux_supNorm_eq]
  push_cast [Real.coe_toNNReal _ hSu0, Real.coe_toNNReal _ hSv0]
  have : (0:ℝ) ≤ Su * Sv := mul_nonneg hSu0 hSv0
  simp only [Bu, Bv, ENNReal.coe_toNNReal_eq_toReal]
  nlinarith

-- Encoding: `‖DG(q)‖` is Lean's operator norm for the sup norm on `ℝ × ℝ`; it dominates the
-- Euclidean operator norm, and the conclusion holds with it (the difference bound uses
-- `|Δu| + |Δv| ≥ max(|Δu|,|Δv|)`).
/-- Blueprint: lem:c03_holder_composition_base.  `‖G(u,v)‖_{C^θ(I)} ≤ M(1 + ‖u‖_{C^θ} + ‖v‖_{C^θ})`
for `0 < θ < 1`, `|G| + ‖DG‖ ≤ M` on `[-K,K]²`, `|u|,|v| ≤ K`. -/
theorem c03_holder_composition_base (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (K M : ℝ) (hK : 0 < K)
    (hM : 0 ≤ M) (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ 1 G)
    (hGM : ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖G q‖ + ‖fderiv ℝ G q‖ ≤ M)
    (a b : ℝ) (u v : ℝ → ℝ) (hu : u ∈ c03_holder θ (Icc a b)) (hv : v ∈ c03_holder θ (Icc a b))
    (huv : ∀ x ∈ Icc a b, |u x| ≤ K ∧ |v x| ≤ K) :
    (fun x => G (u x, v x)) ∈ c03_holder θ (Icc a b) ∧
    c03_holder_normR θ (Icc a b) (fun x => G (u x, v x)) ≤
      M * (1 + c03_holder_normR θ (Icc a b) u + c03_holder_normR θ (Icc a b) v) := by
  have hk : ⌊θ⌋₊ = 0 := Nat.floor_eq_zero.2 hθ1
  set I := Icc a b
  set Q := Icc (-K) K ×ˢ Icc (-K) K
  set Bu := (c03_aux_semi θ I u).toNNReal
  set Bv := (c03_aux_semi θ I v).toNNReal
  have hHu := c03_aux_semi_holder hu
  have hHv := c03_aux_semi_holder hv
  rw [hk, iteratedDerivWithin_zero] at hHu hHv
  have hQ : ∀ x ∈ I, (u x, v x) ∈ Q := fun x hx =>
    ⟨abs_le.1 (huv x hx).1, abs_le.1 (huv x hx).2⟩
  have hcu : ContinuousOn u I := contDiffOn_zero.1 (hk ▸ hu.1)
  have hcv : ContinuousOn v I := contDiffOn_zero.1 (hk ▸ hv.1)
  have hcd : ContDiffOn ℝ ⌊θ⌋₊ (fun x => G (u x, v x)) I := by
    rw [hk]; exact contDiffOn_zero.2 (hG.continuous.comp_continuousOn (hcu.prodMk hcv))
  have hlip : ∀ p ∈ Q, ∀ q ∈ Q, ‖G p - G q‖ ≤ M * ‖p - q‖ := by
    intro p hp q hq
    have := (convex_Icc (-K) K).prod (convex_Icc (-K) K) |>.norm_image_sub_le_of_norm_fderiv_le
      (f := G) (C := M) (fun z _ => hG.differentiable one_ne_zero z)
      (fun z hz => le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hGM z hz)) hq hp
    exact this
  have hH : HolderOnWith (M.toNNReal * (Bu + Bv)) (Real.toNNReal (θ - ⌊θ⌋₊))
      (iteratedDerivWithin ⌊θ⌋₊ (fun x => G (u x, v x)) I) I := by
    rw [hk, iteratedDerivWithin_zero]
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [dist_eq_norm]
    have h1 := hHu.dist_le hx hy
    have h2 := hHv.dist_le hx hy
    rw [Real.dist_eq] at h1 h2
    refine (hlip _ (hQ x hx) _ (hQ y hy)).trans ?_
    have hn : ‖(u x, v x) - (u y, v y)‖ ≤ |u x - u y| + |v x - v y| := by
      rw [Prod.norm_def]
      simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    calc M * ‖(u x, v x) - (u y, v y)‖ ≤ M * (|u x - u y| + |v x - v y|) :=
          mul_le_mul_of_nonneg_left hn hM
      _ ≤ M * (Bu * dist x y ^ ((Real.toNNReal (θ - ↑0) : ℝ)) +
            Bv * dist x y ^ ((Real.toNNReal (θ - ↑0) : ℝ))) := by
          gcongr
          · exact h1
          · exact h2
      _ = _ := by push_cast [Real.coe_toNNReal _ hM]; ring
  have hA0 : ∀ i ≤ ⌊θ⌋₊, (0:ℝ) ≤ (fun _ => M) i := fun _ _ => hM
  have hA : ∀ i ≤ ⌊θ⌋₊, ∀ x ∈ I,
      ‖iteratedDerivWithin i (fun x => G (u x, v x)) I x‖ ≤ (fun _ => M) i := by
    intro i hi x hx
    rw [hk, Nat.le_zero] at hi
    subst hi
    rw [iteratedDerivWithin_zero]
    exact le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hGM _ (hQ x hx))
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le θ I _ hcd _ hA0 hA _ hH
  refine ⟨hmem, hle.trans ?_⟩
  rw [hk]
  simp only [zero_add, Finset.range_one, Finset.sum_singleton]
  have e1 := c03_aux_semi_le_normR hu
  have e2 := c03_aux_semi_le_normR hv
  push_cast [Real.coe_toNNReal _ hM]
  simp only [Bu, Bv, ENNReal.coe_toNNReal_eq_toReal]
  nlinarith

/-- Taylor expansion of order `k` with a Hölder `k`-th derivative (derivatives within `[a,b]`). -/
theorem c03_aux_taylor_holder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ≥0) (a b : ℝ) (hab : a < b) (g : ℝ → E)
    (hg : ContDiffOn ℝ k g (Icc a b)) (B : ℝ≥0)
    (hB : HolderOnWith B θ (iteratedDerivWithin k g (Icc a b)) (Icc a b))
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖g y - ∑ i ∈ Finset.range (k + 1),
        ((Nat.factorial i : ℝ)⁻¹ * (y - x) ^ i) • iteratedDerivWithin i g (Icc a b) x‖ ≤
      B * |y - x| ^ ((k : ℝ) + θ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set I := Icc a b
  rcases eq_or_ne x y with rfl | hxy
  · rw [Finset.sum_range_succ']
    simp only [sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, mul_zero, zero_smul, Finset.sum_const_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, inv_one, mul_one, iteratedDerivWithin_zero, one_smul, zero_add, norm_zero,
      abs_zero]
    positivity
  set J := uIcc x y
  have hJI : J ⊆ I := uIcc_subset_Icc hx hy
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_uIcc hxy
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ m + 1, ∀ t ∈ J, iteratedDerivWithin i g J t = iteratedDerivWithin i g I t := by
    intro i hi t ht
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_subset hJI hJ hI (hg.of_le (by exact_mod_cast hi)) ht]
  have hgJ : ContDiffOn ℝ ((m + 1 : ℕ)) g J := hg.mono hJI
  have hT := taylor_integral_remainder (n := m) hgJ
  rw [taylor_within_apply] at hT
  set D := iteratedDerivWithin (m + 1) g I
  set c : ℝ → ℝ := fun t => (y - t) ^ m / Nat.factorial m
  have hxJ : x ∈ J := left_mem_uIcc
  have hsum : ∑ i ∈ Finset.range (m + 1 + 1),
        ((Nat.factorial i : ℝ)⁻¹ * (y - x) ^ i) • iteratedDerivWithin i g I x =
      ∑ i ∈ Finset.range (m + 1), ((Nat.factorial i : ℝ)⁻¹ * (y - x) ^ i) • iteratedDerivWithin i g J x +
        ((Nat.factorial (m + 1) : ℝ)⁻¹ * (y - x) ^ (m + 1)) • D x := by
    rw [Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [heq i (by have := Finset.mem_range.1 hi; omega) x hxJ]
  have hcint : ∫ t in x..y, c t = (Nat.factorial (m + 1) : ℝ)⁻¹ * (y - x) ^ (m + 1) := by
    simp only [c]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t => t ^ m),
      integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have hcont_c : Continuous c := by fun_prop
  have hDJ : ContinuousOn (iteratedDerivWithin (m + 1) g J) J :=
    hgJ.continuousOn_iteratedDerivWithin le_rfl hJ
  have hi1 : IntervalIntegrable (fun t => c t • iteratedDerivWithin (m + 1) g J t) volume x y :=
    (hcont_c.continuousOn.smul hDJ).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => c t • D x) volume x y :=
    (hcont_c.smul continuous_const).intervalIntegrable _ _
  have hrep : g y - ∑ i ∈ Finset.range (m + 1 + 1),
        ((Nat.factorial i : ℝ)⁻¹ * (y - x) ^ i) • iteratedDerivWithin i g I x =
      ∫ t in x..y, c t • (iteratedDerivWithin (m + 1) g J t - D x) := by
    rw [hsum, ← sub_sub, hT, ← hcint, ← intervalIntegral.integral_smul_const,
      ← intervalIntegral.integral_sub hi1 hi2]
    simp only [smul_sub]
  rw [hrep]
  have hb : ∀ t ∈ Set.uIoc x y, ‖c t • (iteratedDerivWithin (m + 1) g J t - D x)‖ ≤
      |y - x| ^ m * (B * |y - x| ^ (θ : ℝ)) := by
    intro t ht
    have htJ : t ∈ J := uIoc_subset_uIcc ht
    rw [heq (m + 1) le_rfl t htJ, norm_smul]
    have h1 : ‖c t‖ ≤ |y - x| ^ m := by
      simp only [c, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
      rw [div_le_iff₀ (by positivity)]
      calc |y - t| ^ m ≤ |y - x| ^ m := pow_le_pow_left₀ (abs_nonneg _)
            (abs_sub_right_of_mem_uIcc htJ) m
        _ ≤ |y - x| ^ m * Nat.factorial m := le_mul_of_one_le_right (by positivity)
            (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m))
    have h2 : ‖D t - D x‖ ≤ B * |y - x| ^ (θ : ℝ) := by
      rw [← dist_eq_norm]
      refine (hB.dist_le (hJI htJ) hx).trans ?_
      gcongr
      rw [Real.dist_eq]; exact abs_sub_left_of_mem_uIcc htJ
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [Real.rpow_add' (abs_nonneg _) (by positivity), Real.rpow_natCast]
  push_cast
  ring

/-- Inverse of the Taylor–Vandermonde matrix `((σ j)^l / l!)_{j,l ≤ k}`. -/
theorem c03_aux_vandermonde_inv (k : ℕ) (σ : ℝ) (hσ : σ ≠ 0) :
    ∃ c : Fin (k + 1) → Fin (k + 1) → ℝ, ∀ i l : Fin (k + 1),
      ∑ j : Fin (k + 1), c i j * ((σ * ((j : ℕ) : ℝ)) ^ (l : ℕ) / (Nat.factorial l : ℝ)) =
        if i = l then 1 else 0 := by
  set V := Matrix.vandermonde (fun j : Fin (k + 1) => σ * ((j : ℕ) : ℝ))
  set D := Matrix.diagonal (fun l : Fin (k + 1) => ((Nat.factorial l : ℝ))⁻¹)
  set W := V * D
  have hW : ∀ j l, W j l = (σ * ((j : ℕ) : ℝ)) ^ (l : ℕ) / (Nat.factorial l : ℝ) := by
    intro j l
    simp [W, V, D, Matrix.mul_diagonal, Matrix.vandermonde_apply, div_eq_mul_inv]
  have hinj : Function.Injective (fun j : Fin (k + 1) => σ * ((j : ℕ) : ℝ)) := by
    intro j j' h
    have := mul_left_cancel₀ hσ h
    exact Fin.ext (by exact_mod_cast this)
  have hdet : IsUnit W.det := by
    rw [isUnit_iff_ne_zero, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.2 hinj)
      (Finset.prod_ne_zero_iff.2 fun l _ => inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _))
  refine ⟨fun i j => (W⁻¹ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) i j, fun i l => ?_⟩
  have := congrFun (congrFun (Matrix.nonsing_inv_mul W hdet) i) l
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [hW] at this
  exact this

theorem c03_aux_inv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (c W : Fin n → Fin n → ℝ) (h : ∀ i l, ∑ j, c i j * W j l = if i = l then 1 else 0)
    (a : Fin n → E) (i : Fin n) : ∑ j, c i j • ∑ l, W j l • a l = a i := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h]
  simp

theorem c03_holder_stencil_len {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ∃ C, 0 < C ∧ ∀ a b : ℝ, ℓ ≤ b - a → ∀ g : ℝ → E, g ∈ c03_holder ((k : ℝ) + θ) (Icc a b) →
      ∀ Cθ : ℝ≥0, HolderOnWith Cθ (Real.toNNReal θ) (iteratedDerivWithin k g (Icc a b)) (Icc a b) →
      ∀ x ∈ Icc a b, ∀ h : ℝ, 0 < h → h ≤ ℓ / (2 * ((k : ℝ) + 1)) → ∀ i ≤ k,
        ‖iteratedDerivWithin i g (Icc a b) x‖ ≤
          C * (h ^ (-(i : ℝ)) * c03_holder_supNorm (Icc a b) g +
            h ^ ((k : ℝ) + θ - i) * (Cθ : ℝ)) := by
  obtain ⟨cp, hcp⟩ := c03_aux_vandermonde_inv k 1 one_ne_zero
  obtain ⟨cm, hcm⟩ := c03_aux_vandermonde_inv k (-1) (by norm_num)
  set Cc : ℝ := ∑ i, ∑ j, (|cp i j| + |cm i j|) + 1 with hCc
  have hCc0 : 0 ≤ ∑ i, ∑ j, (|cp i j| + |cm i j|) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  set s : ℝ := (k : ℝ) + θ with hs
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hks : 1 ≤ (k : ℝ) ^ s := Real.one_le_rpow hk1 (by positivity)
  refine ⟨Cc * (k : ℝ) ^ s, by positivity, ?_⟩
  intro a b hab g hg Cθ hH x hx h hh0 hh i hi
  have hfl : ⌊s⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  have hab' : a < b := by linarith
  have hgk : ContDiffOn ℝ k g (Icc a b) := by have := hg.1; rwa [hfl] at this
  have hh2 : h * (2 * ((k : ℝ) + 1)) ≤ ℓ := by
    rwa [le_div_iff₀ (by positivity)] at hh
  have hjh : ∀ j : Fin (k + 1), 0 ≤ ((j : ℕ) : ℝ) * h ∧ ((j : ℕ) : ℝ) * h ≤ ℓ / 2 ∧
      ((j : ℕ) : ℝ) * h ≤ k * h := by
    intro j
    have hj : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 j.2
    refine ⟨by positivity, ?_, mul_le_mul_of_nonneg_right hj hh0.le⟩
    nlinarith
  obtain ⟨σ, c, hσ, hc, hcle, hpts⟩ : ∃ σ : ℝ, ∃ c : Fin (k + 1) → Fin (k + 1) → ℝ, |σ| = 1 ∧
      (∀ i l : Fin (k + 1), ∑ j : Fin (k + 1),
        c i j * ((σ * ((j : ℕ) : ℝ)) ^ (l : ℕ) / (Nat.factorial l : ℝ)) = if i = l then 1 else 0) ∧
      (∀ i j, |c i j| ≤ |cp i j| + |cm i j|) ∧
      ∀ j : Fin (k + 1), x + σ * ((j : ℕ) : ℝ) * h ∈ Icc a b := by
    by_cases hxb : x + ℓ / 2 ≤ b
    · refine ⟨1, cp, abs_one, hcp, fun i j => le_add_of_nonneg_right (abs_nonneg _), fun j => ?_⟩
      obtain ⟨h1, h2, -⟩ := hjh j
      constructor <;> nlinarith [hx.1, hx.2]
    · refine ⟨-1, cm, by norm_num, hcm, fun i j => le_add_of_nonneg_left (abs_nonneg _),
        fun j => ?_⟩
      obtain ⟨h1, h2, -⟩ := hjh j
      constructor <;> nlinarith [hx.1, hx.2]
  set I := Icc a b
  set U := c03_holder_supNorm I g
  set av : Fin (k + 1) → E := fun l => h ^ (l : ℕ) • iteratedDerivWithin l g I x
  set W : Fin (k + 1) → Fin (k + 1) → ℝ :=
    fun j l => (σ * ((j : ℕ) : ℝ)) ^ (l : ℕ) / (Nat.factorial l : ℝ)
  set bv : Fin (k + 1) → E := fun j => ∑ l, W j l • av l
  have hθnn : ((Real.toNNReal θ : ℝ≥0) : ℝ) = θ := Real.coe_toNNReal θ hθ0.le
  have key1 : ∀ j, ‖bv j‖ ≤ U + Cθ * ((k : ℝ) ^ s * h ^ s) := by
    intro j
    set y := x + σ * ((j : ℕ) : ℝ) * h
    have hT := c03_aux_taylor_holder k hk (Real.toNNReal θ) a b hab' g hgk Cθ hH x y hx (hpts j)
    have hbv : bv j = ∑ l ∈ Finset.range (k + 1),
        ((Nat.factorial l : ℝ)⁻¹ * (y - x) ^ l) • iteratedDerivWithin l g I x := by
      simp only [bv, W, av, smul_smul]
      rw [Fin.sum_univ_eq_sum_range (fun l => ((σ * ((j : ℕ) : ℝ)) ^ l / (Nat.factorial l : ℝ) *
        h ^ l) • iteratedDerivWithin l g I x) (k + 1)]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      simp only [y]; ring
    rw [hbv]
    have hyx : |y - x| = ((j : ℕ) : ℝ) * h := by
      simp only [y, add_sub_cancel_left, abs_mul, hσ, one_mul, abs_of_nonneg hh0.le, Nat.abs_cast]
    rw [hyx, hθnn] at hT
    have hgy : ‖g y‖ ≤ U := c03_aux_le_supNorm hg (hpts j)
    have hpow : (((j : ℕ) : ℝ) * h) ^ ((k : ℝ) + θ) ≤ (k : ℝ) ^ s * h ^ s := by
      rw [← Real.mul_rpow (by positivity) hh0.le]
      exact Real.rpow_le_rpow (hjh j).1 (hjh j).2.2 (by positivity)
    calc ‖∑ l ∈ Finset.range (k + 1),
          ((Nat.factorial l : ℝ)⁻¹ * (y - x) ^ l) • iteratedDerivWithin l g I x‖
        ≤ ‖g y‖ + ‖g y - ∑ l ∈ Finset.range (k + 1),
          ((Nat.factorial l : ℝ)⁻¹ * (y - x) ^ l) • iteratedDerivWithin l g I x‖ := by
          have := norm_sub_le (g y) (g y - ∑ l ∈ Finset.range (k + 1),
            ((Nat.factorial l : ℝ)⁻¹ * (y - x) ^ l) • iteratedDerivWithin l g I x)
          simpa using this
      _ ≤ U + Cθ * ((k : ℝ) ^ s * h ^ s) := by
          gcongr
          exact hT.trans (mul_le_mul_of_nonneg_left hpow Cθ.coe_nonneg)
  set i' : Fin (k + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  have key2 : av i' = ∑ j, c i' j • bv j := (c03_aux_inv_apply c W hc av i').symm
  have hcsum : ∑ j, |c i' j| ≤ Cc := by
    calc ∑ j, |c i' j| ≤ ∑ j, (|cp i' j| + |cm i' j|) := Finset.sum_le_sum fun j _ => hcle i' j
      _ ≤ ∑ i, ∑ j, (|cp i j| + |cm i j|) :=
          Finset.single_le_sum (f := fun i => ∑ j, (|cp i j| + |cm i j|))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i')
      _ ≤ Cc := by linarith
  have hU0 : 0 ≤ U := c03_aux_supNorm_nonneg _ _
  have hR0 : 0 ≤ U + Cθ * ((k : ℝ) ^ s * h ^ s) := by positivity
  have hav : ‖av i'‖ ≤ Cc * (U + Cθ * ((k : ℝ) ^ s * h ^ s)) := by
    rw [key2]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖c i' j • bv j‖ ≤ ∑ j, |c i' j| * (U + Cθ * ((k : ℝ) ^ s * h ^ s)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (key1 j) (abs_nonneg _)
      _ = (∑ j, |c i' j|) * (U + Cθ * ((k : ℝ) ^ s * h ^ s)) := (Finset.sum_mul _ _ _).symm
      _ ≤ Cc * (U + Cθ * ((k : ℝ) ^ s * h ^ s)) := mul_le_mul_of_nonneg_right hcsum hR0
  have hav' : ‖av i'‖ = h ^ i * ‖iteratedDerivWithin i g I x‖ := by
    simp only [av, i', norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hh0.le]
  rw [hav'] at hav
  have hhi : 0 < h ^ i := pow_pos hh0 i
  have hinv : h ^ (-(i : ℝ)) = (h ^ i)⁻¹ := by rw [Real.rpow_neg hh0.le, Real.rpow_natCast]
  have hsi : h ^ (s - i) = h ^ s * (h ^ i)⁻¹ := by
    rw [Real.rpow_sub hh0, Real.rpow_natCast, div_eq_mul_inv]
  rw [hinv, show (k : ℝ) + θ - i = s - i from rfl, hsi]
  have hnorm : ‖iteratedDerivWithin i g I x‖ ≤ (h ^ i)⁻¹ * (Cc * (U + Cθ * ((k : ℝ) ^ s * h ^ s))) := by
    rw [le_inv_mul_iff₀ hhi]; exact hav
  refine hnorm.trans ?_
  have hCc1 : 0 ≤ Cc := by positivity
  have hhs : 0 ≤ h ^ s := by positivity
  have hhinv : 0 ≤ (h ^ i)⁻¹ := by positivity
  have e1 : (h ^ i)⁻¹ * (Cc * U) ≤ (h ^ i)⁻¹ * (Cc * (k : ℝ) ^ s * U) := by
    gcongr; exact le_mul_of_one_le_right hCc1 hks
  nlinarith [mul_nonneg (mul_nonneg hhinv hCc1) (mul_nonneg Cθ.coe_nonneg hhs)]


-- Encoding: the seminorm `[g^{(k)}]_{C^θ(I)}` is encoded by quantifying over every
-- Hölder constant `Cθ` of `g^{(k)}` (the bound for all such `Cθ` is the bound for the infimum).
-- The statement is for an arbitrary real Banach space `E` (in particular `ℂ`, `ℝ`).
/-- Blueprint: lem:c03_holder_stencil.  `|g^{(i)}(x)| ≤ C(h^{-i}‖g‖_∞ + h^{s-i}[g^{(k)}]_θ)`
for `0 < h ≤ 1/(2(k+1))`, `s = k + θ`, on intervals of length `≥ 1` (derivatives within `I`). -/
theorem c03_holder_stencil {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C, 0 < C ∧ ∀ a b : ℝ, 1 ≤ b - a → ∀ g : ℝ → E, g ∈ c03_holder ((k : ℝ) + θ) (Icc a b) →
      ∀ Cθ : ℝ≥0, HolderOnWith Cθ (Real.toNNReal θ) (iteratedDerivWithin k g (Icc a b)) (Icc a b) →
      ∀ x ∈ Icc a b, ∀ h : ℝ, 0 < h → h ≤ 1 / (2 * ((k : ℝ) + 1)) → ∀ i ≤ k,
        ‖iteratedDerivWithin i g (Icc a b) x‖ ≤
          C * (h ^ (-(i : ℝ)) * c03_holder_supNorm (Icc a b) g +
            h ^ ((k : ℝ) + θ - i) * (Cθ : ℝ)) :=
  c03_holder_stencil_len k hk θ hθ0 hθ1 1 one_pos le_rfl
/-- Exponent bookkeeping: `(U/V)^β · U^{1-α} V^α = U^{1-(α-β)} V^{α-β}`. -/
theorem c03_aux_UV_mul {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (α β : ℝ) :
    (U / V) ^ β * (U ^ (1 - α) * V ^ α) = U ^ (1 - (α - β)) * V ^ (α - β) := by
  rw [Real.div_rpow hU.le hV.le, show 1 - (α - β) = (1 - α) + β by ring,
    show α - β = α + (-β) by ring, Real.rpow_add hU, Real.rpow_add hV, Real.rpow_neg hV.le]
  field_simp

theorem c03_aux_derivWithin_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (g : ℝ → E) (hg : ∀ x ∈ I, g x = 0) (i : ℕ) {x : ℝ} (hx : x ∈ I) :
    iteratedDerivWithin i g I x = 0 := by
  rw [iteratedDerivWithin_congr (f := g) (g := fun _ => (0 : E)) (fun y hy => hg y hy) hx]
  simp [iteratedDerivWithin_eq_iteratedFDerivWithin]

theorem c03_aux_interp_sup_len {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ∃ C, 1 ≤ C ∧ ∀ a b : ℝ, ℓ ≤ b - a → ∀ g : ℝ → E, g ∈ c03_holder s (Icc a b) →
      0 < c03_holder_supNorm (Icc a b) g → ∀ i ≤ ⌊s⌋₊, ∀ x ∈ Icc a b,
        ‖iteratedDerivWithin i g (Icc a b) x‖ ≤
          C * (c03_holder_supNorm (Icc a b) g ^ (1 - (i : ℝ) / s) *
            c03_holder_normR s (Icc a b) g ^ ((i : ℝ) / s)) := by
  set k := ⌊s⌋₊ with hk
  set θ := s - k with hθ
  have hks : (k : ℝ) ≤ s := Nat.floor_le hs.le
  have hθ0 : 0 < θ := by
    rcases (sub_nonneg.2 hks).lt_or_eq with h | h
    · exact h
    · exact absurd (by linarith : s = k) (hsN k)
  have hθ1 : θ < 1 := by have := Nat.lt_floor_add_one s; simp only [hθ]; linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · refine ⟨1, le_rfl, fun a b hab g hg hU i hi x hx => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [iteratedDerivWithin_zero, Nat.cast_zero, zero_div, sub_zero, Real.rpow_one,
      Real.rpow_zero, mul_one, one_mul]
    exact c03_aux_le_supNorm hg hx
  obtain ⟨Cst, hCst0, hCst⟩ := c03_holder_stencil_len (E := E) k hk0 θ hθ0 hθ1 ℓ hℓ0 hℓ1
  set c0 : ℝ := ℓ / (2 * ((k : ℝ) + 1))
  have hc00 : 0 < c0 := by positivity
  have hc01 : c0 ≤ 1 := by
    simp only [c0]; rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ k := by positivity
    linarith
  have hC1 : 0 ≤ Cst * (c0 ^ (-(k : ℝ)) + 1) := by positivity
  refine ⟨Cst * (c0 ^ (-(k : ℝ)) + 1) + 1, by linarith, fun a b hab g hg hU i hi x hx => ?_⟩
  set I := Icc a b
  set U := c03_holder_supNorm I g
  set V := c03_holder_normR s I g
  have hUV : U ≤ V := c03_aux_supNorm_le_normR hg
  have hV : 0 < V := hU.trans_le hUV
  set r : ℝ := (U / V) ^ (1 / s)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (div_pos hU hV) _
  have hr1 : r ≤ 1 := Real.rpow_le_one (div_pos hU hV).le ((div_le_one hV).2 hUV) (by positivity)
  set h := c0 * r
  have hh0 : 0 < h := mul_pos hc00 hr0
  have hh1 : h ≤ ℓ / (2 * ((k : ℝ) + 1)) := mul_le_of_le_one_right hc00.le hr1
  have hsk : s = (k : ℝ) + θ := by simp only [hθ]; ring
  have hg' : g ∈ c03_holder ((k : ℝ) + θ) I := hsk ▸ hg
  have hHk := c03_aux_semi_holder hg
  have hθ' : Real.toNNReal (s - ⌊s⌋₊) = Real.toNNReal θ := rfl
  rw [hθ'] at hHk
  have hst := hCst a b hab g hg' _ hHk x hx h hh0 hh1 i hi
  rw [← hsk] at hst
  have hsemi : ((c03_aux_semi s I g).toNNReal : ℝ) ≤ V := by
    rw [ENNReal.coe_toNNReal_eq_toReal]; exact c03_aux_semi_le_normR hg
  have hik : (i : ℝ) ≤ k := by exact_mod_cast hi
  -- the two terms
  set P := U ^ (1 - (i : ℝ) / s) * V ^ ((i : ℝ) / s)
  have hP0 : 0 ≤ P := by positivity
  have t1 : h ^ (-(i : ℝ)) * U ≤ c0 ^ (-(k : ℝ)) * P := by
    rw [Real.mul_rpow hc00.le hr0.le, ← Real.rpow_mul (div_pos hU hV).le]
    have e : (U / V) ^ (1 / s * -(i : ℝ)) * U = P := by
      have := c03_aux_UV_mul hU hV 0 (1 / s * -(i : ℝ))
      simp only [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one] at this
      rw [this]; simp only [P]; congr 2 <;> ring
    rw [mul_assoc, e]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hc00 hc01 (by linarith : -(k : ℝ) ≤ -(i : ℝ))) hP0
  have t2 : h ^ (s - i) * ((c03_aux_semi s I g).toNNReal : ℝ) ≤ P := by
    have hsi : 0 ≤ s - i := by linarith
    calc h ^ (s - i) * ((c03_aux_semi s I g).toNNReal : ℝ) ≤ h ^ (s - i) * V := by gcongr
      _ = c0 ^ (s - i) * ((U / V) ^ (1 / s * (s - i)) * V) := by
          rw [Real.mul_rpow hc00.le hr0.le, ← Real.rpow_mul (div_pos hU hV).le]; ring
      _ ≤ 1 * ((U / V) ^ (1 / s * (s - i)) * V) := by
          gcongr; exact Real.rpow_le_one hc00.le hc01 hsi
      _ = P := by
          have := c03_aux_UV_mul hU hV 1 (1 / s * (s - i))
          simp only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul] at this
          rw [one_mul, this]; simp only [P]; congr 2 <;> field_simp <;> ring
  calc ‖iteratedDerivWithin i g I x‖ ≤ Cst * (h ^ (-(i : ℝ)) * U +
        h ^ (s - i) * ((c03_aux_semi s I g).toNNReal : ℝ)) := hst
    _ ≤ Cst * (c0 ^ (-(k : ℝ)) * P + P) := by gcongr
    _ = Cst * (c0 ^ (-(k : ℝ)) + 1) * P := by ring
    _ ≤ (Cst * (c0 ^ (-(k : ℝ)) + 1) + 1) * P := by gcongr; linarith


theorem c03_holder_interpolation_len {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ∃ C, 0 < C ∧ ∀ a b : ℝ, ℓ ≤ b - a → ∀ g : ℝ → E, g ∈ c03_holder s (Icc a b) →
      (∀ i ≤ ⌊s⌋₊,
        (∀ x ∈ Icc a b, ‖iteratedDerivWithin i g (Icc a b) x‖ ≤
          C * c03_holder_supNorm (Icc a b) g ^ (1 - (i : ℝ) / s) *
            c03_holder_normR s (Icc a b) g ^ ((i : ℝ) / s)) ∧
        HolderOnWith (Real.toNNReal (C *
            c03_holder_supNorm (Icc a b) g ^ (1 - ((i : ℝ) + (s - ⌊s⌋₊)) / s) *
            c03_holder_normR s (Icc a b) g ^ (((i : ℝ) + (s - ⌊s⌋₊)) / s)))
          (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin i g (Icc a b)) (Icc a b)) ∧
      (c03_holder_supNorm (Icc a b) g = 0 →
        ∀ i ≤ ⌊s⌋₊, ∀ x ∈ Icc a b, iteratedDerivWithin i g (Icc a b) x = 0) := by
  obtain ⟨C1, hC1, hsup⟩ := c03_aux_interp_sup_len (E := E) s hs hsN ℓ hℓ0 hℓ1
  refine ⟨2 * C1 + 1, by linarith, ?_⟩
  intro a b hab g hg
  set k := ⌊s⌋₊ with hk
  set θ := s - k with hθ
  have hks : (k : ℝ) ≤ s := Nat.floor_le hs.le
  have hθ0 : 0 < θ := by
    rcases (sub_nonneg.2 hks).lt_or_eq with h | h
    · exact h
    · exact absurd (by linarith : s = k) (hsN k)
  have hθ1 : θ < 1 := by have := Nat.lt_floor_add_one s; simp only [hθ]; linarith
  have hθc : ((Real.toNNReal θ : ℝ≥0) : ℝ) = θ := Real.coe_toNNReal θ hθ0.le
  set I := Icc a b
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  set U := c03_holder_supNorm I g
  set V := c03_holder_normR s I g
  have hU0 : 0 ≤ U := c03_aux_supNorm_nonneg _ _
  have hUV : U ≤ V := c03_aux_supNorm_le_normR hg
  have hzero : U = 0 → ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i g I x = 0 := by
    intro hU i _ x hx
    refine c03_aux_derivWithin_zero I g (fun y hy => ?_) i hx
    have := c03_aux_le_supNorm hg hy
    have h0 : ‖g y‖ ≤ 0 := by rw [← hU]; exact this
    exact norm_le_zero_iff.1 h0
  refine ⟨fun i hi => ?_, hzero⟩
  have hC0 : 0 ≤ 2 * C1 + 1 := by linarith
  have hgen : ∀ α β : ℝ, 0 ≤ (2 * C1 + 1) * U ^ α * V ^ β := fun α β =>
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hU0 _))
      (Real.rpow_nonneg (c03_aux_normR_nonneg _ _ _) _)
  rcases hU0.lt_or_eq with hU | hU
  swap
  · -- `U = 0`
    have hz := hzero hU.symm i hi
    refine ⟨fun x hx => by rw [hz x hx, norm_zero]; exact hgen _ _, ?_⟩
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [hz x hx, hz y hy, dist_self]
    exact mul_nonneg (NNReal.coe_nonneg _) (Real.rpow_nonneg dist_nonneg _)
  have hV : 0 < V := hU.trans_le hUV
  have hC1' : C1 ≤ 2 * C1 + 1 := by linarith
  refine ⟨fun x hx => ?_, ?_⟩
  · have := hsup a b hab g hg hU i hi x hx
    refine this.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_right hC1' (by positivity)) ?_)
    ring
  set P' := U ^ (1 - ((i : ℝ) + θ) / s) * V ^ (((i : ℝ) + θ) / s)
  have hP'0 : 0 ≤ P' := by positivity
  have hCP : 0 ≤ (2 * C1 + 1) * U ^ (1 - ((i : ℝ) + θ) / s) * V ^ (((i : ℝ) + θ) / s) :=
    hgen _ _
  rcases hi.lt_or_eq with hik | hik
  swap
  · -- `i = k`
    subst hik
    have e : ((k : ℝ) + θ) / s = 1 := by rw [div_eq_one_iff_eq hs.ne']; simp only [hθ]; ring
    have hH := c03_aux_semi_holder hg
    refine hH.mono_const ?_
    rw [e, sub_self, Real.rpow_zero, Real.rpow_one, mul_one,
      Real.le_toNNReal_iff_coe_le (by nlinarith), ENNReal.coe_toNNReal_eq_toReal]
    exact (c03_aux_semi_le_normR hg).trans (le_mul_of_one_le_left hV.le (by linarith))
  -- `i < k`
  set r : ℝ := (U / V) ^ (1 / s)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (div_pos hU hV) _
  have hderiv : ∀ t ∈ I, HasDerivWithinAt (iteratedDerivWithin i g I)
      (iteratedDerivWithin (i + 1) g I t) I t := by
    intro t ht
    have hd := (hg.1.differentiableOn_iteratedDerivWithin (m := i) (by exact_mod_cast hik) hI) t ht
    rw [iteratedDerivWithin_succ]; exact hd.hasDerivWithinAt
  set P1 := U ^ (1 - ((i + 1 : ℕ) : ℝ) / s) * V ^ (((i + 1 : ℕ) : ℝ) / s)
  have hbd1 : ∀ t ∈ I, ‖iteratedDerivWithin (i + 1) g I t‖ ≤ C1 * P1 :=
    fun t ht => hsup a b hab g hg hU (i + 1) hik t ht
  set P0 := U ^ (1 - (i : ℝ) / s) * V ^ ((i : ℝ) / s)
  have hbd0 : ∀ t ∈ I, ‖iteratedDerivWithin i g I t‖ ≤ C1 * P0 :=
    fun t ht => hsup a b hab g hg hU i hi t ht
  have eA : r ^ (1 - θ) * P1 = P' := by
    rw [← Real.rpow_mul (div_pos hU hV).le, c03_aux_UV_mul hU hV]
    simp only [P']; congr 2 <;> push_cast <;> field_simp <;> ring
  have eB : r ^ (-θ) * P0 = P' := by
    rw [← Real.rpow_mul (div_pos hU hV).le, c03_aux_UV_mul hU hV]
    simp only [P']; congr 2 <;> field_simp <;> ring
  refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
  rw [Real.coe_toNNReal _ hCP, show Real.toNNReal (s - ⌊s⌋₊) = Real.toNNReal θ from rfl, hθc,
    show (2 * C1 + 1) * U ^ (1 - ((i : ℝ) + θ) / s) * V ^ (((i : ℝ) + θ) / s) = (2 * C1 + 1) * P'
      by simp only [P']; ring]
  set d := dist x y
  have hd0 : 0 ≤ d := dist_nonneg
  rcases le_or_gt d r with hdr | hdr
  · have hmv := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd1 hy hx
    rw [← dist_eq_norm, ← dist_eq_norm] at hmv
    have h1 : d ≤ d ^ θ * r ^ (1 - θ) := by
      rcases hd0.lt_or_eq with hd | hd
      · calc d = d ^ θ * d ^ (1 - θ) := by
              rw [← Real.rpow_add hd]; simp
          _ ≤ d ^ θ * r ^ (1 - θ) := by
              gcongr
      · rw [← hd]; positivity
    calc dist (iteratedDerivWithin i g I x) (iteratedDerivWithin i g I y) ≤ C1 * P1 * d := hmv
      _ ≤ C1 * P1 * (d ^ θ * r ^ (1 - θ)) := by gcongr
      _ = C1 * (r ^ (1 - θ) * P1) * d ^ θ := by ring
      _ = C1 * P' * d ^ θ := by rw [eA]
      _ ≤ (2 * C1 + 1) * P' * d ^ θ := by gcongr
      _ = (2 * C1 + 1) * P' * d ^ θ := rfl
  · have h2 : 1 ≤ d ^ θ * r ^ (-θ) := by
      rw [Real.rpow_neg hr0.le, ← div_eq_mul_inv, one_le_div (by positivity)]
      exact Real.rpow_le_rpow hr0.le hdr.le hθ0.le
    calc dist (iteratedDerivWithin i g I x) (iteratedDerivWithin i g I y)
        ≤ ‖iteratedDerivWithin i g I x‖ + ‖iteratedDerivWithin i g I y‖ := dist_le_norm_add_norm _ _
      _ ≤ C1 * P0 + C1 * P0 := add_le_add (hbd0 x hx) (hbd0 y hy)
      _ = 2 * C1 * P0 * 1 := by ring
      _ ≤ 2 * C1 * P0 * (d ^ θ * r ^ (-θ)) := by gcongr
      _ = 2 * C1 * (r ^ (-θ) * P0) * d ^ θ := by ring
      _ = 2 * C1 * P' * d ^ θ := by rw [eB]
      _ ≤ (2 * C1 + 1) * P' * d ^ θ := by gcongr; linarith


/-- Sup part of the interpolation inequality (the case `U > 0`). -/
theorem c03_aux_interp_sup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) :
    ∃ C, 1 ≤ C ∧ ∀ a b : ℝ, 1 ≤ b - a → ∀ g : ℝ → E, g ∈ c03_holder s (Icc a b) →
      0 < c03_holder_supNorm (Icc a b) g → ∀ i ≤ ⌊s⌋₊, ∀ x ∈ Icc a b,
        ‖iteratedDerivWithin i g (Icc a b) x‖ ≤
          C * (c03_holder_supNorm (Icc a b) g ^ (1 - (i : ℝ) / s) *
            c03_holder_normR s (Icc a b) g ^ ((i : ℝ) / s)) :=
  c03_aux_interp_sup_len s hs hsN 1 one_pos le_rfl
-- Encoding: the seminorm bound `[g^{(i)}]_{C^θ(I)} ≤ X` is encoded as
-- `HolderOnWith X.toNNReal θ g^{(i)} I`; "if `U = 0` all derivatives vanish" is the last conjunct.
-- Stated for an arbitrary real Banach space `E` (in particular `ℂ`, `ℝ`).
/-- Blueprint: lem:c03_holder_interpolation.  With `U = ‖g‖_∞`, `V = ‖g‖_{C^s(I)}`:
`‖g^{(i)}‖_∞ ≤ C U^{1-i/s} V^{i/s}` and `[g^{(i)}]_θ ≤ C U^{1-(i+θ)/s} V^{(i+θ)/s}`, `i ≤ k`. -/
theorem c03_holder_interpolation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) :
    ∃ C, 0 < C ∧ ∀ a b : ℝ, 1 ≤ b - a → ∀ g : ℝ → E, g ∈ c03_holder s (Icc a b) →
      (∀ i ≤ ⌊s⌋₊,
        (∀ x ∈ Icc a b, ‖iteratedDerivWithin i g (Icc a b) x‖ ≤
          C * c03_holder_supNorm (Icc a b) g ^ (1 - (i : ℝ) / s) *
            c03_holder_normR s (Icc a b) g ^ ((i : ℝ) / s)) ∧
        HolderOnWith (Real.toNNReal (C *
            c03_holder_supNorm (Icc a b) g ^ (1 - ((i : ℝ) + (s - ⌊s⌋₊)) / s) *
            c03_holder_normR s (Icc a b) g ^ (((i : ℝ) + (s - ⌊s⌋₊)) / s)))
          (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin i g (Icc a b)) (Icc a b)) ∧
      (c03_holder_supNorm (Icc a b) g = 0 →
        ∀ i ≤ ⌊s⌋₊, ∀ x ∈ Icc a b, iteratedDerivWithin i g (Icc a b) x = 0) :=
  c03_holder_interpolation_len s hs hsN 1 one_pos le_rfl
/-- `α ↦ U^{1-α} V^α` is nondecreasing on `[0,1]` when `0 ≤ U ≤ V`. -/
theorem c03_aux_UV_mono {U V α β : ℝ} (hU : 0 ≤ U) (hUV : U ≤ V) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ 1) : U ^ (1 - α) * V ^ α ≤ U ^ (1 - β) * V ^ β := by
  rcases hU.lt_or_eq with hU | hU
  · have hV : 0 < V := hU.trans_le hUV
    have e : ∀ γ : ℝ, U ^ (1 - γ) * V ^ γ = U * (V / U) ^ γ := by
      intro γ
      rw [Real.div_rpow hV.le hU.le, Real.rpow_sub hU, Real.rpow_one]; field_simp
    rw [e, e]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      ((one_le_div hU).2 hUV) hαβ) hU.le
  · subst hU
    rcases (sub_nonneg.2 (hαβ.trans hβ)).lt_or_eq with h | h
    · rw [Real.zero_rpow h.ne', zero_mul]
      exact mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg hUV _)
    · have hb1 : β = 1 := by linarith
      have ha1 : α = 1 := by linarith
      rw [ha1, hb1]

/-- `Ua^{1-σ}Va^σ · Ub^{1-τ}Vb^τ ≤ Va Ub + Ua Vb` for `τ ≤ 1 - σ`. -/
theorem c03_aux_UV_pair {Ua Va Ub Vb σ τ : ℝ} (hUa : 0 ≤ Ua) (hUVa : Ua ≤ Va) (hUb : 0 ≤ Ub)
    (hUVb : Ub ≤ Vb) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 - σ) :
    Ua ^ (1 - σ) * Va ^ σ * (Ub ^ (1 - τ) * Vb ^ τ) ≤ Va * Ub + Ua * Vb := by
  have hVa : 0 ≤ Va := hUa.trans hUVa
  have hVb : 0 ≤ Vb := hUb.trans hUVb
  have h1 := c03_aux_UV_mono hUb hUVb hτ0 hτ (by linarith)
  have h2 : Ua ^ (1 - σ) * Va ^ σ * (Ub ^ (1 - (1 - σ)) * Vb ^ (1 - σ)) =
      (Va * Ub) ^ σ * (Ua * Vb) ^ (1 - σ) := by
    rw [Real.mul_rpow hVa hUb, Real.mul_rpow hUa hVb, show 1 - (1 - σ) = σ by ring]; ring
  have h3 := Real.geom_mean_le_arith_mean2_weighted hσ0 (by linarith : 0 ≤ 1 - σ)
    (mul_nonneg hVa hUb) (mul_nonneg hUa hVb) (by ring)
  calc Ua ^ (1 - σ) * Va ^ σ * (Ub ^ (1 - τ) * Vb ^ τ)
      ≤ Ua ^ (1 - σ) * Va ^ σ * (Ub ^ (1 - (1 - σ)) * Vb ^ (1 - σ)) := by gcongr
    _ = (Va * Ub) ^ σ * (Ua * Vb) ^ (1 - σ) := h2
    _ ≤ σ * (Va * Ub) + (1 - σ) * (Ua * Vb) := h3
    _ ≤ Va * Ub + Ua * Vb := by
        have := mul_nonneg hVa hUb; have := mul_nonneg hUa hVb; nlinarith

theorem c03_holder_product_tame_len (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ∃ C, 0 < C ∧ ∀ a₀ b₀ : ℝ, ℓ ≤ b₀ - a₀ → ∀ a b : ℝ → ℂ,
      a ∈ c03_holder s (Icc a₀ b₀) → b ∈ c03_holder s (Icc a₀ b₀) →
      (a * b) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (a * b) ≤
        C * (c03_holder_supNorm (Icc a₀ b₀) a * c03_holder_normR s (Icc a₀ b₀) b +
          c03_holder_supNorm (Icc a₀ b₀) b * c03_holder_normR s (Icc a₀ b₀) a) := by
  obtain ⟨Ci, hCi0, hCi⟩ := c03_holder_interpolation_len (E := ℂ) s hs hsN ℓ hℓ0 hℓ1
  set k := ⌊s⌋₊ with hk
  set θ := s - k with hθ
  have hks : (k : ℝ) ≤ s := Nat.floor_le hs.le
  have hθ0 : 0 < θ := by
    rcases (sub_nonneg.2 hks).lt_or_eq with h | h
    · exact h
    · exact absurd (by linarith : s = k) (hsN k)
  have hθc : ((Real.toNNReal θ : ℝ≥0) : ℝ) = θ := Real.coe_toNNReal θ hθ0.le
  set N : ℝ := ∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ j + 2 * 2 ^ k with hN
  have hN0 : 0 < N := by positivity
  refine ⟨Ci ^ 2 * N, by positivity, ?_⟩
  intro a₀ b₀ hab a b ha hb
  set I := Icc a₀ b₀
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  set Ua := c03_holder_supNorm I a
  set Va := c03_holder_normR s I a
  set Ub := c03_holder_supNorm I b
  set Vb := c03_holder_normR s I b
  have hUa : 0 ≤ Ua := c03_aux_supNorm_nonneg _ _
  have hUb : 0 ≤ Ub := c03_aux_supNorm_nonneg _ _
  have hUVa : Ua ≤ Va := c03_aux_supNorm_le_normR ha
  have hUVb : Ub ≤ Vb := c03_aux_supNorm_le_normR hb
  have hVa : 0 ≤ Va := hUa.trans hUVa
  have hVb : 0 ≤ Vb := hUb.trans hUVb
  set Z := Va * Ub + Ua * Vb
  have hZ0 : 0 ≤ Z := by positivity
  obtain ⟨hia, -⟩ := hCi a₀ b₀ hab a ha
  obtain ⟨hib, -⟩ := hCi a₀ b₀ hab b hb
  have hterm : ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 → 0 ≤ τ → τ ≤ 1 - σ →
      (Ci * Ua ^ (1 - σ) * Va ^ σ) * (Ci * Ub ^ (1 - τ) * Vb ^ τ) ≤ Ci ^ 2 * Z := by
    intro σ τ h1 h2 h3 h4
    have := c03_aux_UV_pair hUa hUVa hUb hUVb h1 h2 h3 h4
    calc (Ci * Ua ^ (1 - σ) * Va ^ σ) * (Ci * Ub ^ (1 - τ) * Vb ^ τ)
        = Ci ^ 2 * (Ua ^ (1 - σ) * Va ^ σ * (Ub ^ (1 - τ) * Vb ^ τ)) := by ring
      _ ≤ Ci ^ 2 * Z := by gcongr
  have hleib : ∀ j ≤ k, ∀ x ∈ I, iteratedDerivWithin j (a * b) I x =
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℂ) * iteratedDerivWithin i a I x *
        iteratedDerivWithin (j - i) b I x := by
    intro j hj x hx
    exact iteratedDerivWithin_mul hx hI ((ha.1.of_le (by exact_mod_cast hj)) x hx)
      ((hb.1.of_le (by exact_mod_cast hj)) x hx)
  have hchoose : ∀ j : ℕ, ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
    intro j; exact_mod_cast Nat.sum_range_choose j
  have hcd : ContDiffOn ℝ k (a * b) I := ha.1.mul hb.1
  -- sup bounds
  have hA : ∀ j ≤ k, ∀ x ∈ I, ‖iteratedDerivWithin j (a * b) I x‖ ≤ 2 ^ j * (Ci ^ 2 * Z) := by
    intro j hj x hx
    rw [hleib j hj x hx]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ) * iteratedDerivWithin i a I x *
          iteratedDerivWithin (j - i) b I x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Ci ^ 2 * Z) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [norm_mul, norm_mul, Complex.norm_natCast, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have h1 := (hia i (hij.trans hj)).1 x hx
          have h2 := (hib (j - i) ((Nat.sub_le j i).trans hj)).1 x hx
          refine (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans ?_
          rw [Nat.cast_sub hij]
          have hjs : (j : ℝ) ≤ s := (Nat.cast_le.2 hj).trans hks
          have hi' : (i : ℝ) ≤ j := Nat.cast_le.2 hij
          refine hterm _ _ (by positivity) ?_ ?_ ?_
          · rw [div_le_one hs]; linarith
          · exact div_nonneg (by linarith) hs.le
          · rw [le_sub_iff_add_le, ← add_div, div_le_one hs]; linarith
      _ = 2 ^ j * (Ci ^ 2 * Z) := by rw [← Finset.sum_mul, hchoose]
  -- Hölder bound of the top derivative
  have hB : HolderOnWith (Real.toNNReal (2 * 2 ^ k * (Ci ^ 2 * Z))) (Real.toNNReal (s - ⌊s⌋₊))
      (iteratedDerivWithin ⌊s⌋₊ (a * b) I) I := by
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [Real.coe_toNNReal _ (by positivity), show Real.toNNReal (s - ⌊s⌋₊) = Real.toNNReal θ from rfl,
      hθc, hleib k le_rfl x hx, hleib k le_rfl y hy, dist_eq_norm, ← Finset.sum_sub_distrib]
    set d := dist x y
    refine (norm_sum_le _ _).trans ?_
    have hks' : (k : ℝ) ≤ s := hks
    calc ∑ i ∈ Finset.range (k + 1), ‖(k.choose i : ℂ) * iteratedDerivWithin i a I x *
          iteratedDerivWithin (k - i) b I x - (k.choose i : ℂ) * iteratedDerivWithin i a I y *
          iteratedDerivWithin (k - i) b I y‖
        ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (2 * (Ci ^ 2 * Z) * d ^ θ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          set A := iteratedDerivWithin i a I
          set B := iteratedDerivWithin (k - i) b I
          have e : (k.choose i : ℂ) * A x * B x - (k.choose i : ℂ) * A y * B y =
              (k.choose i : ℂ) * (A x * (B x - B y) + B y * (A x - A y)) := by ring
          rw [e, norm_mul, Complex.norm_natCast]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hsA := (hia i hik).1 x hx
          have hsB := (hib (k - i) (Nat.sub_le k i)).1 y hy
          have hhA := ((hia i hik).2).dist_le hx hy
          have hhB := ((hib (k - i) (Nat.sub_le k i)).2).dist_le hx hy
          rw [show Real.toNNReal (s - ⌊s⌋₊) = Real.toNNReal θ from rfl, hθc,
            Real.coe_toNNReal _ (by positivity), dist_eq_norm] at hhA hhB
          rw [Nat.cast_sub hik] at hsB hhB
          have hi' : (i : ℝ) ≤ k := Nat.cast_le.2 hik
          have hd : 0 ≤ d ^ θ := Real.rpow_nonneg dist_nonneg _
          have p1 := hterm ((i : ℝ) / s) (((k : ℝ) - i + θ) / s) (by positivity)
            (by rw [div_le_one hs]; linarith) (div_nonneg (by linarith) hs.le)
            (by rw [le_sub_iff_add_le, ← add_div, div_le_one hs]; simp only [hθ]; linarith)
          have p2 := hterm (((i : ℝ) + θ) / s) (((k : ℝ) - i) / s) (div_nonneg (by linarith) hs.le)
            (by rw [div_le_one hs]; simp only [hθ]; linarith) (div_nonneg (by linarith) hs.le)
            (by rw [le_sub_iff_add_le, ← add_div, div_le_one hs]; simp only [hθ]; linarith)
          calc ‖A x * (B x - B y) + B y * (A x - A y)‖
              ≤ ‖A x‖ * ‖B x - B y‖ + ‖B y‖ * ‖A x - A y‖ := by
                refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
            _ ≤ (Ci * Ua ^ (1 - (i : ℝ) / s) * Va ^ ((i : ℝ) / s)) *
                  (Ci * Ub ^ (1 - ((k : ℝ) - i + θ) / s) * Vb ^ (((k : ℝ) - i + θ) / s) * d ^ θ) +
                (Ci * Ub ^ (1 - ((k : ℝ) - i) / s) * Vb ^ (((k : ℝ) - i) / s)) *
                  (Ci * Ua ^ (1 - ((i : ℝ) + θ) / s) * Va ^ (((i : ℝ) + θ) / s) * d ^ θ) := by
                gcongr
            _ = ((Ci * Ua ^ (1 - (i : ℝ) / s) * Va ^ ((i : ℝ) / s)) *
                  (Ci * Ub ^ (1 - ((k : ℝ) - i + θ) / s) * Vb ^ (((k : ℝ) - i + θ) / s)) +
                (Ci * Ua ^ (1 - ((i : ℝ) + θ) / s) * Va ^ (((i : ℝ) + θ) / s)) *
                  (Ci * Ub ^ (1 - ((k : ℝ) - i) / s) * Vb ^ (((k : ℝ) - i) / s))) * d ^ θ := by
                ring
            _ ≤ (Ci ^ 2 * Z + Ci ^ 2 * Z) * d ^ θ := by gcongr
            _ = 2 * (Ci ^ 2 * Z) * d ^ θ := by ring
      _ = 2 * 2 ^ k * (Ci ^ 2 * Z) * d ^ θ := by
          rw [← Finset.sum_mul, hchoose]; ring
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I (a * b) hcd (fun j => 2 ^ j * (Ci ^ 2 * Z))
    (fun j _ => by positivity) hA _ hB
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [Real.coe_toNNReal _ (by positivity), ← Finset.sum_mul]
  simp only [N, Z]; ring



/-- Blueprint: lem:c03_holder_product_tame.  `‖ab‖_{C^s(I)} ≤ C(‖a‖_∞‖b‖_{C^s} + ‖b‖_∞‖a‖_{C^s})`
on intervals of length `≥ 1`, `s ∉ ℕ`. -/
theorem c03_holder_product_tame (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) :
    ∃ C, 0 < C ∧ ∀ a₀ b₀ : ℝ, 1 ≤ b₀ - a₀ → ∀ a b : ℝ → ℂ,
      a ∈ c03_holder s (Icc a₀ b₀) → b ∈ c03_holder s (Icc a₀ b₀) →
      (a * b) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (a * b) ≤
        C * (c03_holder_supNorm (Icc a₀ b₀) a * c03_holder_normR s (Icc a₀ b₀) b +
          c03_holder_supNorm (Icc a₀ b₀) b * c03_holder_normR s (Icc a₀ b₀) a) :=
  c03_holder_product_tame_len s hs hsN 1 one_pos le_rfl
section HolderAPI2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `C^s(I)` norms only depend on the values on `I`. -/
theorem c03_aux_holder_congr {s : ℝ} {I : Set ℝ} {f g : ℝ → E} (hfg : ∀ x ∈ I, f x = g x) :
    c03_holder_norm s I f = c03_holder_norm s I g ∧
      (f ∈ c03_holder s I ↔ g ∈ c03_holder s I) ∧
      c03_holder_normR s I f = c03_holder_normR s I g ∧
      c03_holder_supNorm I f = c03_holder_supNorm I g := by
  have hD : ∀ i, ∀ x ∈ I, iteratedDerivWithin i f I x = iteratedDerivWithin i g I x :=
    fun i x hx => iteratedDerivWithin_congr hfg hx
  have hn : c03_holder_norm s I f = c03_holder_norm s I g := by
    unfold c03_holder_norm c03_Ck_norm
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact iSup_congr fun x => iSup_congr fun hx => by rw [hD i x hx]
    · refine iInf_congr fun C => ?_
      have : HolderOnWith C (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ f I) I ↔
          HolderOnWith C (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ g I) I := by
        constructor
        · intro h x hx y hy; rw [← hD _ x hx, ← hD _ y hy]; exact h x hx y hy
        · intro h x hx y hy; rw [hD _ x hx, hD _ y hy]; exact h x hx y hy
      rw [iInf_congr_Prop this fun _ => rfl]
  refine ⟨hn, ⟨fun h => ⟨h.1.congr fun x hx => (hfg x hx).symm, hn ▸ h.2⟩,
    fun h => ⟨h.1.congr hfg, hn.symm ▸ h.2⟩⟩, by unfold c03_holder_normR; rw [hn], ?_⟩
  unfold c03_holder_supNorm
  congr 1
  exact iSup_congr fun x => iSup_congr fun hx => by rw [hfg x hx]

/-- Triangle inequality for the `C^s(I)` norm. -/
theorem c03_aux_normR_add_le {s : ℝ} {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hf : f ∈ c03_holder s (Icc a b)) (hg : g ∈ c03_holder s (Icc a b)) :
    (fun x => f x + g x) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun x => f x + g x) ≤
        c03_holder_normR s (Icc a b) f + c03_holder_normR s (Icc a b) g := by
  set k := ⌊s⌋₊
  set I := Icc a b
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i (fun x => f x + g x) I x =
      iteratedDerivWithin i f I x + iteratedDerivWithin i g I x := fun i hi x hx =>
    iteratedDerivWithin_add hx hU ((hf.1.of_le (by exact_mod_cast hi)) x hx)
      ((hg.1.of_le (by exact_mod_cast hi)) x hx)
  have hHf := c03_aux_semi_holder hf
  have hHg := c03_aux_semi_holder hg
  have hB : HolderOnWith ((c03_aux_semi s I f).toNNReal + (c03_aux_semi s I g).toNNReal)
      (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ (fun x => f x + g x) I) I := by
    intro x hx y hy
    rw [heq k le_rfl x hx, heq k le_rfl y hy]
    refine (edist_add_add_le _ _ _ _).trans ?_
    rw [ENNReal.coe_add, add_mul]
    exact add_le_add (hHf x hx y hy) (hHg x hx y hy)
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I _ (hf.1.add hg.1)
    (fun i => (c03_aux_supD i I f).toReal + (c03_aux_supD i I g).toReal)
    (fun _ _ => by positivity)
    (fun i hi x hx => by
      rw [heq i hi x hx]
      exact (norm_add_le _ _).trans (add_le_add (c03_aux_le_supD hf hi hx)
        (c03_aux_le_supD hg hi hx))) _ hB
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hf, c03_aux_normR_eq hg, Finset.sum_add_distrib]
  push_cast [ENNReal.coe_toNNReal_eq_toReal]
  ring

/-- Composition with a continuous linear map of norm `≤ 1` does not increase the norms. -/
theorem c03_aux_holder_clm_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : ℝ} {a b : ℝ} (hab : a < b) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) {g : ℝ → E}
    (hg : g ∈ c03_holder s (Icc a b)) :
    (fun x => L (g x)) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun x => L (g x)) ≤ c03_holder_normR s (Icc a b) g ∧
      c03_holder_supNorm (Icc a b) (fun x => L (g x)) ≤ c03_holder_supNorm (Icc a b) g := by
  set k := ⌊s⌋₊
  set I := Icc a b
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hc : ContDiffOn ℝ k (fun x => L (g x)) I := L.contDiff.comp_contDiffOn hg.1
  have heq : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i (fun x => L (g x)) I x =
      L (iteratedDerivWithin i g I x) := by
    intro i hi x hx
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin]
    have := L.iteratedFDerivWithin_comp_left (hg.1 x hx) hU hx (i := i) (by exact_mod_cast hi)
    rw [show (fun x => L (g x)) = ⇑L ∘ g from rfl, this]
    rfl
  have hLx : ∀ v : E, ‖L v‖ ≤ ‖v‖ := fun v =>
    (L.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _) hL)
  have hHg := c03_aux_semi_holder hg
  have hB : HolderOnWith (c03_aux_semi s I g).toNNReal (Real.toNNReal (s - ⌊s⌋₊))
      (iteratedDerivWithin ⌊s⌋₊ (fun x => L (g x)) I) I := by
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [heq k le_rfl x hx, heq k le_rfl y hy, dist_eq_norm, ← map_sub]
    exact (hLx _).trans (by rw [← dist_eq_norm]; exact hHg.dist_le hx hy)
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I _ hc (fun i => (c03_aux_supD i I g).toReal)
    (fun _ _ => by positivity)
    (fun i hi x hx => by rw [heq i hi x hx]; exact (hLx _).trans (c03_aux_le_supD hg hi hx)) _ hB
  refine ⟨hmem, hle.trans (le_of_eq ?_), ?_⟩
  · rw [c03_aux_normR_eq hg, ENNReal.coe_toNNReal_eq_toReal]
  · rw [c03_aux_supNorm_eq, c03_aux_supNorm_eq]
    refine ENNReal.toReal_mono (c03_aux_supD_lt_top hg (Nat.zero_le _)).ne
      (iSup₂_le fun x hx => ?_)
    rw [iteratedDerivWithin_zero]
    refine le_trans ?_ (le_iSup₂ (f := fun x _ => ‖iteratedDerivWithin 0 g I x‖ₑ) x hx)
    rw [iteratedDerivWithin_zero]
    exact enorm_le_iff_norm_le.2 (hLx _)

/-- The derivative of a `C^s` function is `C^{s-1}`, with `‖f'‖_{C^{s-1}} ≤ ‖f‖_{C^s}`. -/
theorem c03_aux_holder_deriv {s : ℝ} {k : ℕ} (hk : ⌊s⌋₊ = k + 1) (hk' : ⌊s - 1⌋₊ = k)
    {a b : ℝ} (hab : a < b) {f : ℝ → E} (hf : f ∈ c03_holder s (Icc a b)) :
    derivWithin f (Icc a b) ∈ c03_holder (s - 1) (Icc a b) ∧
      c03_holder_normR (s - 1) (Icc a b) (derivWithin f (Icc a b)) ≤
        c03_holder_normR s (Icc a b) f := by
  set I := Icc a b
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hc : ContDiffOn ℝ ⌊s - 1⌋₊ (derivWithin f I) I := by
    rw [hk']; exact hf.1.derivWithin hU (by rw [hk]; exact_mod_cast le_rfl)
  have heq : ∀ i, iteratedDerivWithin i (derivWithin f I) I = iteratedDerivWithin (i + 1) f I :=
    fun i => (iteratedDerivWithin_succ').symm
  have hθ : Real.toNNReal (s - 1 - ⌊s - 1⌋₊) = Real.toNNReal (s - ⌊s⌋₊) := by
    rw [hk, hk']; push_cast; ring_nf
  have hB : HolderOnWith (c03_aux_semi s I f).toNNReal (Real.toNNReal (s - 1 - ⌊s - 1⌋₊))
      (iteratedDerivWithin ⌊s - 1⌋₊ (derivWithin f I) I) I := by
    rw [hθ, heq, hk', ← hk]; exact c03_aux_semi_holder hf
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le (s - 1) I _ hc
    (fun i => (c03_aux_supD (i + 1) I f).toReal) (fun _ _ => by positivity)
    (fun i hi x hx => by
      rw [heq]; exact c03_aux_le_supD hf (by rw [hk]; rw [hk'] at hi; omega) hx) _ hB
  refine ⟨hmem, hle.trans ?_⟩
  rw [c03_aux_normR_eq hf, hk', hk, Finset.sum_range_succ' _ (k + 1),
    ENNReal.coe_toNNReal_eq_toReal]
  have : 0 ≤ (c03_aux_supD 0 I f).toReal := ENNReal.toReal_nonneg
  linarith

/-- `f ∈ C^s` from `f' ∈ C^{s-1}`: `‖f‖_{C^s} ≤ sup|f| + ‖f'‖_{C^{s-1}}`. -/
theorem c03_aux_holder_succ {s : ℝ} {k : ℕ} (hk : ⌊s⌋₊ = k + 1) (hk' : ⌊s - 1⌋₊ = k)
    {a b : ℝ} (hab : a < b) {f : ℝ → E} (hf : ContDiffOn ℝ (k + 1) f (Icc a b))
    (hf' : derivWithin f (Icc a b) ∈ c03_holder (s - 1) (Icc a b)) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ x ∈ Icc a b, ‖f x‖ ≤ A) :
    f ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) f ≤ A + c03_holder_normR (s - 1) (Icc a b) (derivWithin f (Icc a b)) := by
  set I := Icc a b
  have heq : ∀ i, iteratedDerivWithin (i + 1) f I = iteratedDerivWithin i (derivWithin f I) I :=
    fun i => iteratedDerivWithin_succ'
  have hθ : Real.toNNReal (s - 1 - ⌊s - 1⌋₊) = Real.toNNReal (s - ⌊s⌋₊) := by
    rw [hk, hk']; push_cast; ring_nf
  have hB : HolderOnWith (c03_aux_semi (s - 1) I (derivWithin f I)).toNNReal
      (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ f I) I := by
    rw [← hθ, hk, heq, ← hk']; exact c03_aux_semi_holder hf'
  set Af : ℕ → ℝ := fun i => if i = 0 then A else (c03_aux_supD (i - 1) I (derivWithin f I)).toReal
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I f (by rw [hk]; exact_mod_cast hf) Af
    (fun i _ => by simp only [Af]; split_ifs <;> positivity)
    (fun i hi x hx => by
      simp only [Af]
      split_ifs with h0
      · subst h0; rw [iteratedDerivWithin_zero]; exact hA x hx
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [heq, Nat.add_sub_cancel]
        exact c03_aux_le_supD hf' (by rw [hk']; rw [hk] at hi; omega) hx) _ hB
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hf', hk, hk', Finset.sum_range_succ' _ (k + 1),
    ENNReal.coe_toNNReal_eq_toReal]
  simp only [Af, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
    ite_true]
  ring

/-- Lowering the order by one: `‖f‖_{C^{s-1}} ≤ 3 ‖f‖_{C^s}`. -/
theorem c03_aux_holder_lower {s : ℝ} {k : ℕ} (hk : ⌊s⌋₊ = k + 1) (hk' : ⌊s - 1⌋₊ = k)
    (hθ0 : 0 ≤ s - ⌊s⌋₊) (hθ1 : s - ⌊s⌋₊ ≤ 1)
    {a b : ℝ} (hab : a < b) {f : ℝ → E} (hf : f ∈ c03_holder s (Icc a b)) :
    f ∈ c03_holder (s - 1) (Icc a b) ∧
      c03_holder_normR (s - 1) (Icc a b) f ≤ 3 * c03_holder_normR s (Icc a b) f := by
  set I := Icc a b
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  set θ := s - ⌊s⌋₊
  have hθ : Real.toNNReal (s - 1 - ⌊s - 1⌋₊) = Real.toNNReal θ := by
    simp only [θ]; rw [hk, hk']; push_cast; ring_nf
  have hθc : ((Real.toNNReal θ : ℝ≥0) : ℝ) = θ := Real.coe_toNNReal θ hθ0
  set S1 := (c03_aux_supD (k + 1) I f).toReal
  set S0 := (c03_aux_supD k I f).toReal
  have hderiv : ∀ t ∈ I, HasDerivWithinAt (iteratedDerivWithin k f I)
      (iteratedDerivWithin (k + 1) f I t) I t := by
    intro t ht
    have hd := (hf.1.differentiableOn_iteratedDerivWithin (m := k)
      (by rw [hk]; exact_mod_cast Nat.lt_succ_self k) hU) t ht
    rw [iteratedDerivWithin_succ]; exact hd.hasDerivWithinAt
  have hB : HolderOnWith (Real.toNNReal (S1 + 2 * S0)) (Real.toNNReal (s - 1 - ⌊s - 1⌋₊))
      (iteratedDerivWithin ⌊s - 1⌋₊ f I) I := by
    rw [hθ, hk']
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [Real.coe_toNNReal _ (by positivity), hθc]
    set d := dist x y
    have hd0 : 0 ≤ d := dist_nonneg
    rcases le_or_gt d 1 with hd1 | hd1
    · have hmv := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
        (fun t ht => c03_aux_le_supD hf (by rw [hk]) ht) hy hx
      rw [← dist_eq_norm, ← dist_eq_norm] at hmv
      have : d ≤ d ^ θ := by
        rcases hd0.lt_or_eq with hd | hd
        · calc d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
            _ ≤ d ^ θ := Real.rpow_le_rpow_of_exponent_ge hd hd1 hθ1
        · rw [← hd]; positivity
      calc dist (iteratedDerivWithin k f I x) (iteratedDerivWithin k f I y) ≤ S1 * d := hmv
        _ ≤ S1 * d ^ θ := by gcongr
        _ ≤ (S1 + 2 * S0) * d ^ θ := by gcongr; linarith [show (0:ℝ) ≤ S0 by positivity]
    · have h1 : 1 ≤ d ^ θ := Real.one_le_rpow hd1.le hθ0
      calc dist (iteratedDerivWithin k f I x) (iteratedDerivWithin k f I y)
          ≤ ‖iteratedDerivWithin k f I x‖ + ‖iteratedDerivWithin k f I y‖ :=
            dist_le_norm_add_norm _ _
        _ ≤ S0 + S0 := add_le_add (c03_aux_le_supD hf (by rw [hk]; omega) hx)
            (c03_aux_le_supD hf (by rw [hk]; omega) hy)
        _ ≤ (S1 + 2 * S0) * d ^ θ := by
            have : (0:ℝ) ≤ S1 := by positivity
            have : (0:ℝ) ≤ S0 := by positivity
            nlinarith
  have hc : ContDiffOn ℝ ⌊s - 1⌋₊ f I := hf.1.of_le (by rw [hk, hk']; exact_mod_cast Nat.le_succ k)
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le (s - 1) I f hc (fun i => (c03_aux_supD i I f).toReal)
    (fun _ _ => by positivity)
    (fun i hi x hx => c03_aux_le_supD hf (by rw [hk]; rw [hk'] at hi; omega) hx) _ hB
  refine ⟨hmem, hle.trans ?_⟩
  rw [Real.coe_toNNReal _ (by positivity), hk']
  have e := c03_aux_normR_eq hf
  rw [hk, Finset.sum_range_succ] at e
  have h0 : S0 ≤ ∑ i ∈ Finset.range (k + 1), (c03_aux_supD i I f).toReal :=
    Finset.single_le_sum (f := fun i => (c03_aux_supD i I f).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.2 (Nat.lt_succ_self k))
  have : 0 ≤ (c03_aux_semi s I f).toReal := ENNReal.toReal_nonneg
  have : 0 ≤ ∑ i ∈ Finset.range (k + 1), (c03_aux_supD i I f).toReal :=
    Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have : (0:ℝ) ≤ S1 := ENNReal.toReal_nonneg
  linarith

end HolderAPI2

theorem c03_aux_supNorm_le {E : Type*} [NormedAddCommGroup E] {I : Set ℝ} {g : ℝ → E} {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ x ∈ I, ‖g x‖ ≤ A) : c03_holder_supNorm I g ≤ A := by
  unfold c03_holder_supNorm
  refine ENNReal.toReal_le_of_le_ofReal hA0 (iSup₂_le fun x hx => ?_)
  rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hA x hx)

theorem c03_aux_not_nat (k : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∀ n : ℕ, (k : ℝ) + θ ≠ n := by
  intro n h
  rcases Nat.lt_or_ge k n with hkn | hkn
  · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    linarith
  · have : (n : ℝ) ≤ k := by exact_mod_cast hkn
    linarith

theorem c03_aux_floor_add (k : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ⌊(k : ℝ) + θ⌋₊ = k := by
  rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith

theorem c03_aux_comp_ind_len (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (k : ℕ) : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ K M : ℝ, 0 < K → 0 ≤ M →
    ∃ C, 0 < C ∧ ∀ a₀ b₀ : ℝ, ℓ ≤ b₀ - a₀ →
      ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G →
      (∀ j ≤ k + 2, ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖iteratedFDeriv ℝ j G q‖ ≤ M) →
      ∀ u v : ℝ → ℝ, u ∈ c03_holder ((k : ℝ) + θ) (Icc a₀ b₀) →
      v ∈ c03_holder ((k : ℝ) + θ) (Icc a₀ b₀) →
      (∀ x ∈ Icc a₀ b₀, |u x| ≤ K ∧ |v x| ≤ K) →
      (fun x => G (u x, v x)) ∈ c03_holder ((k : ℝ) + θ) (Icc a₀ b₀) ∧
      c03_holder_normR ((k : ℝ) + θ) (Icc a₀ b₀) (fun x => G (u x, v x)) ≤
        C * (1 + c03_holder_normR ((k : ℝ) + θ) (Icc a₀ b₀) u +
          c03_holder_normR ((k : ℝ) + θ) (Icc a₀ b₀) v) ^ (k + 1) := by
  induction k with
  | zero =>
    intro θ hθ0 hθ1 K M hK hM
    refine ⟨2 * M + 1, by linarith, ?_⟩
    intro a₀ b₀ hab G hG hGM u v hu hv huv
    simp only [Nat.cast_zero, zero_add] at hu hv ⊢
    have hGM' : ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖G q‖ + ‖fderiv ℝ G q‖ ≤ 2 * M := by
      intro q hq
      have h0 := hGM 0 (by omega) q hq
      have h1 := hGM 1 (by omega) q hq
      rw [norm_iteratedFDeriv_zero] at h0
      rw [norm_iteratedFDeriv_one] at h1
      linarith
    obtain ⟨hmem, hle⟩ := c03_holder_composition_base θ hθ0 hθ1 K (2 * M) hK (by linarith) G
      (hG.of_le (by exact_mod_cast le_top)) hGM' a₀ b₀ u v hu hv huv
    refine ⟨hmem, hle.trans ?_⟩
    have := c03_aux_normR_nonneg θ (Icc a₀ b₀) u
    have := c03_aux_normR_nonneg θ (Icc a₀ b₀) v
    rw [pow_one]; nlinarith
  | succ k ih =>
    intro θ hθ0 hθ1 K M hK hM
    obtain ⟨Cih, hCih0, hih⟩ := ih θ hθ0 hθ1 K M hK hM
    obtain ⟨Cp, hCp0, hprod⟩ := c03_holder_product_tame_len ((k : ℝ) + θ) (by positivity)
      (c03_aux_not_nat k hθ0 hθ1) ℓ hℓ0 hℓ1
    set Ctot := M + 2 * Cp * (M + Cih * 3 ^ (k + 1))
    refine ⟨Ctot + 1, by positivity, ?_⟩
    intro a₀ b₀ hab G hG hGM u v hu hv huv
    set s : ℝ := ((k + 1 : ℕ) : ℝ) + θ with hs
    have es : s - 1 = (k : ℝ) + θ := by simp only [s]; push_cast; ring
    have hfl : ⌊s⌋₊ = k + 1 := c03_aux_floor_add (k + 1) hθ0 hθ1
    have hfl' : ⌊s - 1⌋₊ = k := by rw [es]; exact c03_aux_floor_add k hθ0 hθ1
    have hθs : s - ⌊s⌋₊ = θ := by rw [hfl]; simp only [s]; ring
    have hab' : a₀ < b₀ := by linarith
    set I := Icc a₀ b₀
    have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab'
    set Q := Icc (-K) K ×ˢ Icc (-K) K
    have hQ : ∀ x ∈ I, (u x, v x) ∈ Q := fun x hx =>
      ⟨abs_le.1 (huv x hx).1, abs_le.1 (huv x hx).2⟩
    -- lowering and derivatives
    obtain ⟨hu1, hu1n⟩ := c03_aux_holder_lower hfl hfl' (by rw [hθs]; exact hθ0.le)
      (by rw [hθs]; exact hθ1.le) hab' hu
    obtain ⟨hv1, hv1n⟩ := c03_aux_holder_lower hfl hfl' (by rw [hθs]; exact hθ0.le)
      (by rw [hθs]; exact hθ1.le) hab' hv
    obtain ⟨hdu, hdun⟩ := c03_aux_holder_deriv hfl hfl' hab' hu
    obtain ⟨hdv, hdvn⟩ := c03_aux_holder_deriv hfl hfl' hab' hv
    rw [es] at hu1 hu1n hv1 hv1n hdu hdun hdv hdvn
    -- partial derivatives of `G`
    set G1 : ℝ × ℝ → ℂ := fun q => fderiv ℝ G q ((1 : ℝ), (0 : ℝ))
    set G2 : ℝ × ℝ → ℂ := fun q => fderiv ℝ G q ((0 : ℝ), (1 : ℝ))
    have hdG : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by simp)
    have hG1 : ContDiff ℝ (⊤ : ℕ∞) G1 := hdG.clm_apply contDiff_const
    have hG2 : ContDiff ℝ (⊤ : ℕ∞) G2 := hdG.clm_apply contDiff_const
    have hGjM : ∀ c : ℝ × ℝ, ‖c‖ ≤ 1 → ∀ j ≤ k + 2, ∀ q ∈ Q,
        ‖iteratedFDeriv ℝ j (fun q => fderiv ℝ G q c) q‖ ≤ M := by
      intro c hc j hj q hq
      refine (norm_iteratedFDeriv_clm_apply_const hdG.contDiffAt (by exact_mod_cast le_top)).trans ?_
      rw [norm_iteratedFDeriv_fderiv]
      have := hGM (j + 1) (by omega) q hq
      calc ‖c‖ * ‖iteratedFDeriv ℝ (j + 1) G q‖ ≤ 1 * M := by gcongr
        _ = M := one_mul M
    have hn10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
    have hn01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
    obtain ⟨hg1, hg1n⟩ := hih a₀ b₀ hab G1 hG1 (hGjM _ hn10) u v hu1 hv1 huv
    obtain ⟨hg2, hg2n⟩ := hih a₀ b₀ hab G2 hG2 (hGjM _ hn01) u v hu1 hv1 huv
    have hsup1 : c03_holder_supNorm I (fun x => G1 (u x, v x)) ≤ M := by
      refine c03_aux_supNorm_le hM fun x hx => ?_
      have := hGjM _ hn10 0 (by omega) _ (hQ x hx)
      rwa [norm_iteratedFDeriv_zero] at this
    have hsup2 : c03_holder_supNorm I (fun x => G2 (u x, v x)) ≤ M := by
      refine c03_aux_supNorm_le hM fun x hx => ?_
      have := hGjM _ hn01 0 (by omega) _ (hQ x hx)
      rwa [norm_iteratedFDeriv_zero] at this
    -- complexified derivatives
    set U' : ℝ → ℂ := fun x => Complex.ofRealCLM (derivWithin u I x)
    set V' : ℝ → ℂ := fun x => Complex.ofRealCLM (derivWithin v I x)
    obtain ⟨hU', hU'n, hU's⟩ := c03_aux_holder_clm_norm hab' Complex.ofRealCLM
      (by rw [Complex.ofRealCLM_norm]) hdu
    obtain ⟨hV', hV'n, hV's⟩ := c03_aux_holder_clm_norm hab' Complex.ofRealCLM
      (by rw [Complex.ofRealCLM_norm]) hdv
    obtain ⟨hP1, hP1n⟩ := hprod a₀ b₀ hab (fun x => G1 (u x, v x)) U' hg1 hU'
    obtain ⟨hP2, hP2n⟩ := hprod a₀ b₀ hab (fun x => G2 (u x, v x)) V' hg2 hV'
    obtain ⟨hsum, hsumn⟩ := c03_aux_normR_add_le hab' hP1 hP2
    -- the derivative of `G(u,v)`
    have hderiv_eq : ∀ x ∈ I, derivWithin (fun x => G (u x, v x)) I x =
        ((fun x => G1 (u x, v x)) * U') x + ((fun x => G2 (u x, v x)) * V') x := by
      intro x hx
      have h1 : (⌊s⌋₊ : WithTop ℕ∞) ≠ 0 := by
        rw [hfl]; exact_mod_cast Nat.succ_ne_zero k
      have hux : HasDerivWithinAt u (derivWithin u I x) I x :=
        ((hu.1.differentiableOn h1) x hx).hasDerivWithinAt
      have hvx : HasDerivWithinAt v (derivWithin v I x) I x :=
        ((hv.1.differentiableOn h1) x hx).hasDerivWithinAt
      have hGd : HasFDerivAt G (fderiv ℝ G (u x, v x)) (u x, v x) :=
        ((hG.differentiable (by simp)) _).hasFDerivAt
      have hc := hGd.comp_hasDerivWithinAt x (hux.prodMk hvx)
      have h2 : derivWithin (fun x => G (u x, v x)) I x =
          fderiv ℝ G (u x, v x) (derivWithin u I x, derivWithin v I x) :=
        hc.derivWithin (hI.uniqueDiffWithinAt hx)
      rw [h2]
      have e : ((derivWithin u I x, derivWithin v I x) : ℝ × ℝ) =
          derivWithin u I x • ((1 : ℝ), (0 : ℝ)) + derivWithin v I x • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      rw [e, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
      simp only [Pi.mul_apply, G1, G2, U', V', Complex.ofRealCLM_apply]
      ring
    have hf' : derivWithin (fun x => G (u x, v x)) I ∈ c03_holder (s - 1) I := by
      rw [es]; exact (c03_aux_holder_congr (s := (k : ℝ) + θ) hderiv_eq).2.1.2 hsum
    have hf'n : c03_holder_normR (s - 1) I (derivWithin (fun x => G (u x, v x)) I) =
        c03_holder_normR ((k : ℝ) + θ) I (fun x => ((fun x => G1 (u x, v x)) * U') x +
          ((fun x => G2 (u x, v x)) * V') x) := by
      rw [es]; exact (c03_aux_holder_congr (s := (k : ℝ) + θ) hderiv_eq).2.2.1
    have hfcd : ContDiffOn ℝ (k + 1 : ℕ) (fun x => G (u x, v x)) I :=
      (hG.of_le (by exact_mod_cast le_top)).comp_contDiffOn
        ((hfl ▸ hu.1).prodMk (hfl ▸ hv.1))
    obtain ⟨hmem, hle⟩ := c03_aux_holder_succ hfl hfl' hab' (by exact_mod_cast hfcd) hf' M hM
      (fun x hx => by
        have := hGM 0 (by omega) _ (hQ x hx)
        rwa [norm_iteratedFDeriv_zero] at this)
    refine ⟨hmem, hle.trans ?_⟩
    rw [hf'n]
    -- numerical bookkeeping
    set Nu := c03_holder_normR s I u
    set Nv := c03_holder_normR s I v
    have hNu : 0 ≤ Nu := c03_aux_normR_nonneg _ _ _
    have hNv : 0 ≤ Nv := c03_aux_normR_nonneg _ _ _
    set T := 1 + Nu + Nv
    have hT1 : 1 ≤ T := by simp only [T]; linarith
    have hTk : (1 + c03_holder_normR ((k : ℝ) + θ) I u + c03_holder_normR ((k : ℝ) + θ) I v) ^ (k + 1)
        ≤ 3 ^ (k + 1) * T ^ (k + 1) := by
      rw [← mul_pow]
      have := c03_aux_normR_nonneg ((k : ℝ) + θ) I u
      have := c03_aux_normR_nonneg ((k : ℝ) + θ) I v
      exact pow_le_pow_left₀ (by linarith) (by simp only [T]; linarith) _
    have hTT : T ≤ T ^ (k + 1 + 1) := le_self_pow₀ hT1 (by omega)
    have hTT' : T * T ^ (k + 1) = T ^ (k + 1 + 1) := by ring
    have hP : ∀ (g1 : ℝ → ℂ) (w : ℝ → ℝ) (W : ℝ → ℂ),
        c03_holder_supNorm I g1 ≤ M →
        c03_holder_normR ((k : ℝ) + θ) I g1 ≤ Cih * (1 + c03_holder_normR ((k : ℝ) + θ) I u +
          c03_holder_normR ((k : ℝ) + θ) I v) ^ (k + 1) →
        c03_holder_normR ((k : ℝ) + θ) I W ≤ T → c03_holder_supNorm I W ≤ T →
        Cp * (c03_holder_supNorm I g1 * c03_holder_normR ((k : ℝ) + θ) I W +
          c03_holder_supNorm I W * c03_holder_normR ((k : ℝ) + θ) I g1) ≤
          Cp * (M + Cih * 3 ^ (k + 1)) * T ^ (k + 1 + 1) := by
      intro g1 w W h1 h2 h3 h4
      have a1 := c03_aux_supNorm_nonneg I g1
      have a2 := c03_aux_normR_nonneg ((k : ℝ) + θ) I W
      have a3 := c03_aux_supNorm_nonneg I W
      have a4 := c03_aux_normR_nonneg ((k : ℝ) + θ) I g1
      have b1 : c03_holder_supNorm I g1 * c03_holder_normR ((k : ℝ) + θ) I W ≤ M * T ^ (k + 1 + 1) :=
        (mul_le_mul h1 h3 a2 hM).trans (mul_le_mul_of_nonneg_left hTT hM)
      have b2 : c03_holder_supNorm I W * c03_holder_normR ((k : ℝ) + θ) I g1 ≤
          Cih * 3 ^ (k + 1) * T ^ (k + 1 + 1) := by
        calc c03_holder_supNorm I W * c03_holder_normR ((k : ℝ) + θ) I g1
            ≤ T * (Cih * (3 ^ (k + 1) * T ^ (k + 1))) :=
              mul_le_mul h4 (h2.trans (mul_le_mul_of_nonneg_left hTk hCih0.le)) a4 (by positivity)
          _ = Cih * 3 ^ (k + 1) * T ^ (k + 1 + 1) := by rw [← hTT']; ring
      calc _ ≤ Cp * (M * T ^ (k + 1 + 1) + Cih * 3 ^ (k + 1) * T ^ (k + 1 + 1)) := by gcongr
        _ = _ := by ring
    have hu' : c03_holder_normR ((k : ℝ) + θ) I U' ≤ T :=
      hU'n.trans (hdun.trans (by simp only [T, Nu]; linarith))
    have hu's : c03_holder_supNorm I U' ≤ T :=
      hU's.trans ((c03_aux_supNorm_le_normR hdu).trans (hdun.trans (by simp only [T, Nu]; linarith)))
    have hv' : c03_holder_normR ((k : ℝ) + θ) I V' ≤ T :=
      hV'n.trans (hdvn.trans (by simp only [T, Nv]; linarith))
    have hv's : c03_holder_supNorm I V' ≤ T :=
      hV's.trans ((c03_aux_supNorm_le_normR hdv).trans (hdvn.trans (by simp only [T, Nv]; linarith)))
    have e1 := hP _ u U' hsup1 hg1n hu' hu's
    have e2 := hP _ v V' hsup2 hg2n hv' hv's
    have hTp : 1 ≤ T ^ (k + 1 + 1) := one_le_pow₀ hT1
    calc M + c03_holder_normR ((k : ℝ) + θ) I (fun x => ((fun x => G1 (u x, v x)) * U') x +
          ((fun x => G2 (u x, v x)) * V') x)
        ≤ M + (Cp * (M + Cih * 3 ^ (k + 1)) * T ^ (k + 1 + 1) +
            Cp * (M + Cih * 3 ^ (k + 1)) * T ^ (k + 1 + 1)) := by
          gcongr; exact hsumn.trans (add_le_add (hP1n.trans e1) (hP2n.trans e2))
      _ ≤ (Ctot + 1) * T ^ (k + 1 + 1) := by
          simp only [Ctot]
          have : 0 ≤ Cp * (M + Cih * 3 ^ (k + 1)) := by positivity
          nlinarith



theorem c03_aux_comp_ind (k : ℕ) : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ K M : ℝ, 0 < K → 0 ≤ M →
    ∃ C, 0 < C ∧ ∀ a₀ b₀ : ℝ, 1 ≤ b₀ - a₀ →
      ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G →
      (∀ j ≤ k + 2, ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖iteratedFDeriv ℝ j G q‖ ≤ M) →
      ∀ u v : ℝ → ℝ, u ∈ c03_holder ((k : ℝ) + θ) (Icc a₀ b₀) →
      v ∈ c03_holder ((k : ℝ) + θ) (Icc a₀ b₀) →
      (∀ x ∈ Icc a₀ b₀, |u x| ≤ K ∧ |v x| ≤ K) →
      (fun x => G (u x, v x)) ∈ c03_holder ((k : ℝ) + θ) (Icc a₀ b₀) ∧
      c03_holder_normR ((k : ℝ) + θ) (Icc a₀ b₀) (fun x => G (u x, v x)) ≤
        C * (1 + c03_holder_normR ((k : ℝ) + θ) (Icc a₀ b₀) u +
          c03_holder_normR ((k : ℝ) + θ) (Icc a₀ b₀) v) ^ (k + 1) :=
  c03_aux_comp_ind_len 1 one_pos le_rfl k
section HolderLib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Blueprint: lem:c03_holder_composition_higher.  `‖G(u,v)‖_{C^s(I)} ≤ C(1 + ‖u‖_{C^s} +
‖v‖_{C^s})^{k+1}`, `C = C(s,K,M)`, when `‖D^jG‖ ≤ M` on `[-K,K]²` for `j ≤ k+2`. -/
theorem c03_holder_composition_higher (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n)
    (K M : ℝ) (hK : 0 < K) (hM : 0 ≤ M) :
    ∃ C, 0 < C ∧ ∀ a₀ b₀ : ℝ, 1 ≤ b₀ - a₀ →
      ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G →
      (∀ j ≤ ⌊s⌋₊ + 2, ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖iteratedFDeriv ℝ j G q‖ ≤ M) →
      ∀ u v : ℝ → ℝ, u ∈ c03_holder s (Icc a₀ b₀) → v ∈ c03_holder s (Icc a₀ b₀) →
      (∀ x ∈ Icc a₀ b₀, |u x| ≤ K ∧ |v x| ≤ K) →
      (fun x => G (u x, v x)) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (fun x => G (u x, v x)) ≤
        C * (1 + c03_holder_normR s (Icc a₀ b₀) u +
          c03_holder_normR s (Icc a₀ b₀) v) ^ (⌊s⌋₊ + 1) := by
  set k := ⌊s⌋₊ with hk
  set θ := s - k with hθ
  have hks : (k : ℝ) ≤ s := Nat.floor_le hs.le
  have hθ0 : 0 < θ := by
    rcases (sub_nonneg.2 hks).lt_or_eq with h | h
    · exact h
    · exact absurd (by linarith : s = k) (hsN k)
  have hθ1 : θ < 1 := by have := Nat.lt_floor_add_one s; simp only [hθ]; linarith
  have e : (k : ℝ) + θ = s := by simp only [hθ]; ring
  obtain ⟨C, hC0, hC⟩ := c03_aux_comp_ind k θ hθ0 hθ1 K M hK hM
  refine ⟨C, hC0, fun a₀ b₀ hab G hG hGM u v hu hv huv => ?_⟩
  have := hC a₀ b₀ hab G hG hGM u v (by rw [e]; exact hu) (by rw [e]; exact hv) huv
  rw [e] at this
  exact this

/-- Uniform limits of derivatives on `[a,b]` are derivatives within `[a,b]`. -/
theorem c03_aux_hasDerivWithinAt_of_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b) {φ ψ : ℕ → ℝ → E} {Φ Ψ : ℝ → E}
    (hφ : ∀ n, ∀ x ∈ Icc a b, HasDerivWithinAt (φ n) (ψ n x) (Icc a b) x)
    (hψc : ∀ n, ContinuousOn (ψ n) (Icc a b))
    (hφu : TendstoUniformlyOn φ Φ atTop (Icc a b)) (hψu : TendstoUniformlyOn ψ Ψ atTop (Icc a b)) :
    ∀ x ∈ Icc a b, HasDerivWithinAt Φ (Ψ x) (Icc a b) x := by
  have hφc : ∀ n, ContinuousOn (φ n) (Icc a b) := fun n x hx => (hφ n x hx).continuousWithinAt
  have hΦc : ContinuousOn Φ (Icc a b) := hφu.continuousOn (Eventually.of_forall hφc).frequently
  have hΨc : ContinuousOn Ψ (Icc a b) := hψu.continuousOn (Eventually.of_forall hψc).frequently
  have hint : ∀ x ∈ Ioo a b, HasDerivAt Φ (Ψ x) x := by
    intro x hx
    refine hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hψu.mono Ioo_subset_Icc_self)
      (Eventually.of_forall fun n y hy => (hφ n y (Ioo_subset_Icc_self hy)).hasDerivAt
        (Icc_mem_nhds hy.1 hy.2)) (fun y hy => hφu.tendsto_at (Ioo_subset_Icc_self hy)) hx
  have hdiff : DifferentiableOn ℝ Φ (Ioo a b) := fun x hx => (hint x hx).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ Ioo a b, deriv Φ x = Ψ x := fun x hx => (hint x hx).deriv
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rw [← hxa]
    have ha : a ∈ Icc a b := left_mem_Icc.2 hab.le
    have h1 : Tendsto Ψ (𝓝[>] a) (𝓝 (Ψ a)) :=
      ((hΨc a ha).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hab)).tendsto
    have h2 : Tendsto (fun y => deriv Φ y) (𝓝[>] a) (𝓝 (Ψ a)) := by
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy
      exact (hderiv y hy).symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff ((hΦc a ha).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT hab) h2).mono Icc_subset_Ici_self
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · rw [hxb]
    have hb : b ∈ Icc a b := right_mem_Icc.2 hab.le
    have h1 : Tendsto Ψ (𝓝[<] b) (𝓝 (Ψ b)) :=
      ((hΨc b hb).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hab)).tendsto
    have h2 : Tendsto (fun y => deriv Φ y) (𝓝[<] b) (𝓝 (Ψ b)) := by
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hab] with y hy
      exact (hderiv y hy).symm
    exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff ((hΦc b hb).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsLT hab) h2).mono Icc_subset_Iic_self
  · exact (hint x ⟨hxa, hxb⟩).hasDerivWithinAt


/-- Approximate attainment of the supremum norm of a derivative on a nonempty set. -/
theorem c03_aux_approx_sup {E : Type*} [NormedAddCommGroup E] {I : Set ℝ} {a : ℝ} (ha : a ∈ I)
    {g : ℝ → E} {M : ℝ} (hg : ∀ x ∈ I, ‖g x‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ I, (⨆ y ∈ I, ‖g y‖ₑ).toReal - ε ≤ ‖g x‖ := by
  set S := ⨆ y ∈ I, ‖g y‖ₑ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hg a ha)
  have hfin : S ≤ ENNReal.ofReal M := iSup₂_le fun y hy => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hg y hy)
  have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
  by_cases hneg : S.toReal - ε < 0
  · exact ⟨a, ha, hneg.le.trans (norm_nonneg _)⟩
  push Not at hneg
  have hlt : ENNReal.ofReal (S.toReal - ε) < S := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hneg hSt]; linarith
  obtain ⟨x, hx⟩ := lt_iSup_iff.1 hlt
  obtain ⟨hxI, hx2⟩ := lt_iSup_iff.1 hx
  refine ⟨x, hxI, ?_⟩
  rw [← ofReal_norm] at hx2
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hneg).1 hx2).le

-- Encoding: stated for an arbitrary real Banach space `E` (in particular `ℂ`, and `ℝ` as
-- needed by `c03_linear_gain`); `f_n → f` uniformly on `I` is `TendstoUniformlyOn`.
-- Completeness of `E` is used to obtain the derivatives of the limit as limits of Cauchy
-- sequences of derivatives.
/-- Blueprint: lem:c03_holder_closed_ball.  A uniform limit on `I = [a,b]` of functions with
`‖f_n‖_{C^s(I)} ≤ M` lies in `C^s(I)` with `‖f‖_{C^s(I)} ≤ M`. -/
theorem c03_holder_closed_ball [CompleteSpace E] (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) (a b : ℝ) (hab : a < b)
    (M : ℝ) (hM : 0 ≤ M) (f : ℕ → ℝ → E) (F : ℝ → E) (hf : ∀ n, f n ∈ c03_holder s (Icc a b))
    (hfM : ∀ n, c03_holder_normR s (Icc a b) (f n) ≤ M)
    (hlim : TendstoUniformlyOn f F atTop (Icc a b)) :
    F ∈ c03_holder s (Icc a b) ∧ c03_holder_normR s (Icc a b) F ≤ M := by
  set k := ⌊s⌋₊ with hk
  set I := Icc a b with hI
  have hks : (k : ℝ) ≤ s := Nat.floor_le hs.le
  have hks' : (k : ℝ) < s := by
    rcases hks.lt_or_eq with h | h
    · exact h
    · exact absurd h.symm (hsN k)
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have haI : a ∈ I := left_mem_Icc.2 hab.le
  set ℓ := min (b - a) 1
  have hℓ0 : 0 < ℓ := lt_min (by linarith) one_pos
  obtain ⟨Ci, hCi0, hCi⟩ := c03_holder_interpolation_len (E := E) s hs hsN ℓ hℓ0 (min_le_right _ _)
  have hℓab : ℓ ≤ b - a := min_le_left _ _
  set D : ℕ → ℕ → ℝ → E := fun n i => iteratedDerivWithin i (f n) I with hD
  -- uniform Cauchy property of the derivatives
  have hcauchy : ∀ i ≤ k, UniformCauchySeqOn (fun n => D n i) atTop I := by
    intro i hi
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set α := 1 - (i : ℝ) / s
    have hα : 0 < α := by
      simp only [α]; rw [sub_pos, div_lt_one hs]; exact lt_of_le_of_lt (by exact_mod_cast hi) hks'
    set W := (2 * M + 1) ^ ((i : ℝ) / s)
    have hW : 0 ≤ W := by positivity
    have htend : Tendsto (fun U : ℝ => Ci * U ^ α * W) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun U : ℝ => U ^ α) (𝓝 0) (𝓝 0) := by
        have := (Real.continuous_rpow_const hα.le).tendsto 0
        rwa [Real.zero_rpow hα.ne'] at this
      simpa using (this.const_mul Ci).mul_const W
    obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 (htend.eventually (gt_mem_nhds hε))
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hlim.uniformCauchySeqOn (δ / 2)
      (by positivity)
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    set g : ℝ → E := fun y => f m y - f n y
    have hgeq : ∀ y, g y = f m y + (-ContinuousLinearMap.id ℝ E) (f n y) := fun y => by
      simp [g, sub_eq_add_neg]
    obtain ⟨hnf, hnfn, -⟩ := c03_aux_holder_clm_norm hab (-ContinuousLinearMap.id ℝ E)
      (by rw [norm_neg]; exact ContinuousLinearMap.norm_id_le) (hf n)
    obtain ⟨hg1, hg1n⟩ := c03_aux_normR_add_le hab (hf m) hnf
    have hcg := c03_aux_holder_congr (s := s) (I := I) (f := g)
      (g := fun y => f m y + (-ContinuousLinearMap.id ℝ E) (f n y)) (fun y _ => hgeq y)
    have hg : g ∈ c03_holder s I := hcg.2.1.2 hg1
    have hgV : c03_holder_normR s I g ≤ 2 * M + 1 := by
      rw [hcg.2.2.1]; linarith [hfM m, hfM n]
    have hgU : c03_holder_supNorm I g ≤ δ / 2 := by
      refine c03_aux_supNorm_le (by positivity) fun y hy => ?_
      rw [← dist_eq_norm]; exact (hN m hm n hn y hy).le
    have hgi := ((hCi a b hℓab g hg).1 i hi).1 x hx
    have hderiv : iteratedDerivWithin i g I x = D m i x - D n i x :=
      iteratedDerivWithin_sub hx hU (((hf m).1.of_le (by exact_mod_cast hi)) x hx)
        (((hf n).1.of_le (by exact_mod_cast hi)) x hx)
    rw [hderiv] at hgi
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hgi.trans ?_) (hδε (y := c03_holder_supNorm I g) ?_)
    · have hV0 := c03_aux_normR_nonneg s I g
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hV0 hgV (by positivity))
        (by have := c03_aux_supNorm_nonneg I g; positivity)
    · rw [Real.dist_eq, sub_zero, abs_of_nonneg (c03_aux_supNorm_nonneg I g)]; linarith
  -- the limits
  have hconv : ∀ i ≤ k, ∀ x ∈ I, ∃ L, Tendsto (fun n => D n i x) atTop (𝓝 L) := by
    intro i hi x hx
    exact cauchySeq_tendsto_of_complete ((hcauchy i hi).cauchySeq hx)
  set Lim : ℕ → ℝ → E := fun i x => limUnder atTop (fun n => D n i x) with hLim
  have hLt : ∀ i ≤ k, ∀ x ∈ I, Tendsto (fun n => D n i x) atTop (𝓝 (Lim i x)) := by
    intro i hi x hx
    obtain ⟨L, hL⟩ := hconv i hi x hx
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  have hLu : ∀ i ≤ k, TendstoUniformlyOn (fun n => D n i) (Lim i) atTop I := fun i hi =>
    (hcauchy i hi).tendstoUniformlyOn_of_tendsto (hLt i hi)
  have hL0 : ∀ x ∈ I, Lim 0 x = F x := by
    intro x hx
    refine tendsto_nhds_unique (hLt 0 (Nat.zero_le _) x hx) ?_
    simpa [D] using hlim.tendsto_at hx
  have hDc : ∀ n, ∀ i ≤ k, ContinuousOn (D n i) I := fun n i hi =>
    (hf n).1.continuousOn_iteratedDerivWithin (by exact_mod_cast hi) hU
  have hLd : ∀ i < k, ∀ x ∈ I, HasDerivWithinAt (Lim i) (Lim (i + 1) x) I x := by
    intro i hi
    refine c03_aux_hasDerivWithinAt_of_uniform hab (φ := fun n => D n i)
      (ψ := fun n => D n (i + 1)) (fun n x hx => ?_) (fun n => hDc n (i + 1) hi)
      (hLu i hi.le) (hLu (i + 1) hi)
    have hd := ((hf n).1.differentiableOn_iteratedDerivWithin (m := i) (by exact_mod_cast hi) hU) x hx
    simp only [D]
    rw [iteratedDerivWithin_succ]
    exact hd.hasDerivWithinAt
  have hid : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i F I x = Lim i x := by
    intro i
    induction i with
    | zero => intro _ x hx; rw [iteratedDerivWithin_zero, hL0 x hx]
    | succ i ih =>
      intro hi x hx
      rw [iteratedDerivWithin_succ]
      have heqOn : EqOn (iteratedDerivWithin i F I) (Lim i) I := fun y hy => ih (by omega) y hy
      rw [derivWithin_congr heqOn (heqOn hx)]
      exact (hLd i (by omega) x hx).derivWithin (hU x hx)
  -- smoothness
  have hcd : ContDiffOn ℝ k F I := by
    have key : ∀ j ≤ k, ContDiffOn ℝ j (Lim (k - j)) I := by
      intro j
      induction j with
      | zero =>
        intro _
        simp only [Nat.sub_zero, CharP.cast_eq_zero]
        exact contDiffOn_zero.2 ((hLu k le_rfl).continuousOn
          (Eventually.of_forall fun n => hDc n k le_rfl).frequently)
      | succ j ih =>
        intro hj
        have hjk : k - (j + 1) < k := by omega
        have e : k - (j + 1) + 1 = k - j := by omega
        rw [Nat.cast_add, Nat.cast_one]
        refine (contDiffOn_succ_iff_derivWithin (n := (j : WithTop ℕ∞)) hU).2 ⟨fun x hx =>
          (hLd _ hjk x hx).differentiableWithinAt, fun h => by simp at h, ?_⟩
        refine (ih (by omega)).congr fun x hx => ?_
        rw [(hLd _ hjk x hx).derivWithin (hU x hx), e]
    have := key k le_rfl
    simp only [Nat.sub_self] at this
    exact this.congr fun x hx => (hL0 x hx).symm
  -- uniform bounds from the approximants
  have hsumlim : ∀ xs : ℕ → ℝ, (∀ i, xs i ∈ I) →
      ∑ i ∈ Finset.range (k + 1), ‖Lim i (xs i)‖ ≤ M := by
    intro xs hxs
    have ht : Tendsto (fun n => ∑ i ∈ Finset.range (k + 1), ‖D n i (xs i)‖) atTop
        (𝓝 (∑ i ∈ Finset.range (k + 1), ‖Lim i (xs i)‖)) :=
      tendsto_finsetSum _ fun i hi =>
        (hLt i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (xs i) (hxs i)).norm
    refine le_of_tendsto' ht fun n => ?_
    calc ∑ i ∈ Finset.range (k + 1), ‖D n i (xs i)‖
        ≤ ∑ i ∈ Finset.range (k + 1), (c03_aux_supD i I (f n)).toReal :=
          Finset.sum_le_sum fun i hi =>
            c03_aux_le_supD (hf n) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (hxs i)
      _ ≤ c03_holder_normR s I (f n) := by
          rw [c03_aux_normR_eq (hf n)]; exact le_add_of_nonneg_right ENNReal.toReal_nonneg
      _ ≤ M := hfM n
  have hholdlim : ∀ xs : ℕ → ℝ, (∀ i, xs i ∈ I) → ∀ y ∈ I, ∀ y' ∈ I,
      (∑ i ∈ Finset.range (k + 1), ‖Lim i (xs i)‖) *
        dist y y' ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) + ‖Lim k y - Lim k y'‖ ≤
        M * dist y y' ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) := by
    intro xs hxs y hy y' hy'
    set dθ := dist y y' ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ)
    have hdθ : 0 ≤ dθ := Real.rpow_nonneg dist_nonneg _
    have ht : Tendsto (fun n => (∑ i ∈ Finset.range (k + 1), ‖D n i (xs i)‖) * dθ +
        ‖D n k y - D n k y'‖) atTop
        (𝓝 ((∑ i ∈ Finset.range (k + 1), ‖Lim i (xs i)‖) * dθ + ‖Lim k y - Lim k y'‖)) :=
      ((tendsto_finsetSum _ fun i hi =>
        (hLt i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (xs i) (hxs i)).norm).mul_const dθ).add
        ((hLt k le_rfl y hy).sub (hLt k le_rfl y' hy')).norm
    refine le_of_tendsto' ht fun n => ?_
    have h1 : ∑ i ∈ Finset.range (k + 1), ‖D n i (xs i)‖ ≤
        ∑ i ∈ Finset.range (k + 1), (c03_aux_supD i I (f n)).toReal :=
      Finset.sum_le_sum fun i hi =>
        c03_aux_le_supD (hf n) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (hxs i)
    have h2 : ‖D n k y - D n k y'‖ ≤ (c03_aux_semi s I (f n)).toReal * dθ := by
      rw [← dist_eq_norm]
      have := (c03_aux_semi_holder (hf n)).dist_le hy hy'
      rwa [ENNReal.coe_toNNReal_eq_toReal] at this
    have h3 := hfM n
    rw [c03_aux_normR_eq (hf n)] at h3
    calc (∑ i ∈ Finset.range (k + 1), ‖D n i (xs i)‖) * dθ + ‖D n k y - D n k y'‖
        ≤ (∑ i ∈ Finset.range (k + 1), (c03_aux_supD i I (f n)).toReal) * dθ +
            (c03_aux_semi s I (f n)).toReal * dθ := add_le_add (mul_le_mul_of_nonneg_right h1 hdθ) h2
      _ = (∑ i ∈ Finset.range (k + 1), (c03_aux_supD i I (f n)).toReal +
            (c03_aux_semi s I (f n)).toReal) * dθ := by ring
      _ ≤ M * dθ := mul_le_mul_of_nonneg_right h3 hdθ
  -- bounds on the derivatives of `F`
  have hFb : ∀ i ≤ k, ∀ x ∈ I, ‖iteratedDerivWithin i F I x‖ ≤ M := by
    intro i hi x hx
    have := hsumlim (fun j => if j = i then x else a) (fun j => by split_ifs <;> assumption)
    rw [hid i hi x hx]
    refine le_trans ?_ this
    have := Finset.single_le_sum (f := fun j => ‖Lim j (if j = i then x else a)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    simpa using this
  set S : ℕ → ℝ := fun i => (c03_aux_supD i I F).toReal with hS
  have hSb : ∀ i ≤ k, ∀ x ∈ I, ‖iteratedDerivWithin i F I x‖ ≤ S i := by
    intro i hi x hx
    have hfin : c03_aux_supD i I F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup₂_le fun y hy => by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hFb i hi y hy))
    have := le_iSup₂ (f := fun y _ => ‖iteratedDerivWithin i F I y‖ₑ) x hx
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 this
  -- approximate maximizers
  have happrox : ∀ ε > 0, ∃ xs : ℕ → ℝ, (∀ i, xs i ∈ I) ∧
      ∀ i ≤ k, S i - ε ≤ ‖Lim i (xs i)‖ := by
    intro ε hε
    have h : ∀ i, ∃ x ∈ I, i ≤ k → S i - ε ≤ ‖Lim i x‖ := by
      intro i
      by_cases hi : i ≤ k
      · obtain ⟨x, hx, hxε⟩ := c03_aux_approx_sup haI (hFb i hi) hε
        exact ⟨x, hx, fun _ => by rw [← hid i hi x hx]; exact hxε⟩
      · exact ⟨a, haI, fun h => absurd h hi⟩
    choose xs hxs hxε using h
    exact ⟨xs, hxs, fun i hi => hxε i hi⟩
  have hSε : ∀ ε > 0, ∀ xs : ℕ → ℝ, (∀ i ≤ k, S i - ε ≤ ‖Lim i (xs i)‖) →
      ∑ i ∈ Finset.range (k + 1), S i - (k + 1) * ε ≤
        ∑ i ∈ Finset.range (k + 1), ‖Lim i (xs i)‖ := by
    intro ε hε xs hxs
    have : ∑ i ∈ Finset.range (k + 1), (S i - ε) ≤ ∑ i ∈ Finset.range (k + 1), ‖Lim i (xs i)‖ :=
      Finset.sum_le_sum fun i hi => hxs i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    rw [Finset.sum_sub_distrib] at this
    simpa using this
  set SS := ∑ i ∈ Finset.range (k + 1), S i
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hSM : SS ≤ M := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨xs, hxs, hxε⟩ := happrox (ε / (k + 1)) (by positivity)
    have h1 := hSε _ (by positivity) xs hxε
    have h2 := hsumlim xs hxs
    have : (k + 1 : ℝ) * (ε / (k + 1)) = ε := by field_simp
    linarith
  have hB : HolderOnWith (Real.toNNReal (M - SS)) (Real.toNNReal (s - ⌊s⌋₊))
      (iteratedDerivWithin ⌊s⌋₊ F I) I := by
    refine c03_aux_holderOnWith_of_dist fun y hy y' hy' => ?_
    rw [Real.coe_toNNReal _ (by linarith), hid k le_rfl y hy, hid k le_rfl y' hy', dist_eq_norm]
    set dθ := dist y y' ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ)
    have hdθ : 0 ≤ dθ := Real.rpow_nonneg dist_nonneg _
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    set ε := ε' / ((k + 1) * (dθ + 1))
    have hε : 0 < ε := by positivity
    obtain ⟨xs, hxs, hxε⟩ := happrox ε hε
    have h1 := hSε ε hε xs hxε
    have h2 := hholdlim xs hxs y hy y' hy'
    have h3 : (SS - (k + 1) * ε) * dθ ≤ (∑ i ∈ Finset.range (k + 1), ‖Lim i (xs i)‖) * dθ :=
      mul_le_mul_of_nonneg_right h1 hdθ
    have h4 : (k + 1) * ε * dθ ≤ ε' := by
      have : (k + 1) * ε * dθ = ε' * (dθ / (dθ + 1)) := by simp only [ε]; field_simp
      rw [this]
      exact mul_le_of_le_one_right hε'.le ((div_le_one (by positivity)).2 (by linarith))
    nlinarith
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I F hcd S (fun _ _ => ENNReal.toReal_nonneg) hSb _ hB
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [Real.coe_toNNReal _ (by linarith)]
  ring

end HolderLib


/-- Blueprint: def:c03_secant.  The secant `S_f(y,z)` of this chapter is the shared `c01_secant`. -/
abbrev c03_secant : (ℝ → ℝ) → ℝ → ℝ → ℝ := c01_secant

/-- Blueprint: def:c03_secant.  For `f ∈ C¹`: `S_f(y,z) = ∫₀¹ f'(z+τ(y-z)) dτ` (also at `y = z`). -/
theorem c03_secant_eq_integral (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (y z : ℝ) :
    c03_secant f y z = ∫ τ in (0 : ℝ)..1, deriv f (z + τ * (y - z)) := by
  unfold c03_secant c01_secant
  split_ifs with h
  · subst h; simp
  · have hsub := intervalIntegral.smul_integral_comp_mul_add (f := deriv f) (a := 0) (b := 1)
      (y - z) z
    have hftc : ∫ x in z..y, deriv f x = f y - f z :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hf.differentiable one_ne_zero x)
        ((hf.continuous_deriv le_rfl).intervalIntegrable _ _)
    have heq : (fun τ => deriv f (z + τ * (y - z))) = fun τ => deriv f ((y - z) * τ + z) := by
      funext τ; ring_nf
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul, hftc] at hsub
    rw [heq, div_eq_iff (sub_ne_zero.2 h), mul_comm, hsub]

/-- Blueprint: def:c03_secant.  For `f ∈ C¹`, `S_f` is continuous on `ℝ²` and
`|S_f(y,z)| ≤ ‖f'‖_∞`. -/
theorem c03_secant_continuous_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (fun q : ℝ × ℝ => c03_secant f q.1 q.2) ∧
    ∀ M : ℝ, (∀ x, |deriv f x| ≤ M) → ∀ y z, |c03_secant f y z| ≤ M := by
  have hS : (fun q : ℝ × ℝ => c03_secant f q.1 q.2) =
      fun q : ℝ × ℝ => ∫ τ in (0 : ℝ)..1, deriv f (q.2 + τ * (q.1 - q.2)) :=
    funext fun q => c03_secant_eq_integral f hf q.1 q.2
  refine ⟨?_, fun M hM y z => ?_⟩
  · rw [hS]
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (hf.continuous_deriv le_rfl).comp (by fun_prop)
  · rw [c03_secant_eq_integral f hf]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := M)
      (f := fun τ => deriv f (z + τ * (y - z))) (fun τ _ => hM _)
    simpa using this

/-- Blueprint: def:c03_Gamma_eps.  `P_ε(u,v) = ∫_u^v (1 - A_ε(s)/A_ε(u)) ds`. -/
def c03_P_eps (p ε u v : ℝ) : ℝ := ∫ s in u..v, (1 - A_eps p ε s / A_eps p ε u)

/-- Blueprint: def:c03_Gamma_eps.
`Γ_ε(u,v) = c_α [p P_ε(u,v) + (v-u)(1 - A_ε(v)/A_ε(u))]`  (`B_ε = A_eps_B`, in `GSQG/Definitions`). -/
def c03_Gamma_eps (p ε u v : ℝ) : ℝ :=
  calpha p * (p * c03_P_eps p ε u v + (v - u) * (1 - A_eps p ε v / A_eps p ε u))

/-- Blueprint: def:c03_Gamma_eps.
`Γ̃_ε(u,v) = -(c_α/A_ε(u)) ∫₀¹ [1 + p(1-t)] A_ε'(u + t(v-u)) dt`. -/
def c03_Gamma_eps_tilde (p ε u v : ℝ) : ℝ :=
  -(calpha p / A_eps p ε u) *
    ∫ t in (0 : ℝ)..1, (1 + p * (1 - t)) * deriv (A_eps p ε) (u + t * (v - u))

/-- `1 + εs² > 0` for `ε ≥ 0`. -/
theorem c03_aux_base_pos {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) : 0 < 1 + ε * s ^ 2 := by positivity

/-- `A_ε'(s) = -(p+1) ε s (1+εs²)^{-(p+1)/2-1}`. -/
theorem c03_aux_A_hasDerivAt (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    HasDerivAt (A_eps p ε) (-(p + 1) * ε * s * (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1)) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + ε * s ^ 2) (ε * (2 * s)) s := by
    simpa using ((hasDerivAt_pow 2 s).const_mul ε).const_add 1
  have := h1.rpow_const (p := -(p + 1) / 2) (Or.inl (c03_aux_base_pos hε s).ne')
  unfold A_eps
  convert this using 1
  ring

/-- `deriv A_ε` in closed form. -/
theorem c03_aux_A_deriv (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    deriv (A_eps p ε) = fun s => -(p + 1) * ε * s * (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1) :=
  funext fun s => (c03_aux_A_hasDerivAt p hε s).deriv

/-- `A_ε` is `C^∞`. -/
theorem c03_aux_A_contDiff (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {n : WithTop ℕ∞} :
    ContDiff ℝ n (A_eps p ε) := by
  unfold A_eps
  exact ContDiff.rpow_const_of_ne (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
    (fun x => (c03_aux_base_pos hε x).ne')

/-- `B_ε` is `C^∞`. -/
theorem c03_aux_B_contDiff (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {n : WithTop ℕ∞} :
    ContDiff ℝ n (A_eps_B p ε) := by
  unfold A_eps_B
  exact ContDiff.rpow_const_of_ne (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
    (fun x => (c03_aux_base_pos hε x).ne')

/-- `A_ε > 0`. -/
theorem c03_aux_A_pos (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) : 0 < A_eps p ε s :=
  Real.rpow_pos_of_pos (c03_aux_base_pos hε s) _

/-- `B_ε = A_ε⁻¹`. -/
theorem c03_aux_B_eq (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) : A_eps_B p ε s = (A_eps p ε s)⁻¹ := by
  unfold A_eps A_eps_B
  rw [neg_div, Real.rpow_neg (c03_aux_base_pos hε s).le, inv_inv]

/-- `A_ε ≤ 1` (for `p > -1`). -/
theorem c03_aux_A_le_one (p : ℝ) (hp : 0 < p) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) : A_eps p ε s ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg s]) (by linarith)

/-- `|A_ε'(s)| ≤ (p+1) ε |s|`. -/
theorem c03_aux_A_deriv_le (p : ℝ) (hp : 0 < p) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    |deriv (A_eps p ε) s| ≤ (p + 1) * ε * |s| := by
  rw [(c03_aux_A_hasDerivAt p hε s).deriv]
  have h1 : (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg s]) (by linarith)
  have h2 : 0 ≤ (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1) := Real.rpow_nonneg (by positivity) _
  rw [show -(p + 1) * ε * s * (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1) =
    -((p + 1) * ε * s * (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1)) by ring, abs_neg, abs_mul,
    abs_mul, abs_mul, abs_of_pos (by linarith : 0 < p + 1), abs_of_nonneg hε, abs_of_nonneg h2]
  have : 0 ≤ (p + 1) * ε * |s| := by positivity
  nlinarith

/-- The primitive `F(x) = ∫_0^x A_ε` has derivative `A_ε`. -/
theorem c03_aux_A_prim_hasDerivAt (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, A_eps p ε s) (A_eps p ε x) x := by
  have hAc : Continuous (A_eps p ε) := (c03_aux_A_contDiff p hε (n := 0)).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hAc.intervalIntegrable _ _)
    (hAc.stronglyMeasurableAtFilter _ _) hAc.continuousAt

/-- `P_ε(u,v) = (v-u) - (F(v)-F(u))/A_ε(u)`, `F = ∫_0 A_ε`. -/
theorem c03_aux_P_eq (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (u v : ℝ) :
    c03_P_eps p ε u v = (v - u) - ((∫ s in (0 : ℝ)..v, A_eps p ε s) -
      (∫ s in (0 : ℝ)..u, A_eps p ε s)) / A_eps p ε u := by
  have hAc : Continuous (A_eps p ε) := (c03_aux_A_contDiff p hε (n := 0)).continuous
  unfold c03_P_eps
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((hAc.div_const _).intervalIntegrable _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_const, smul_eq_mul, mul_one,
    intervalIntegral.integral_interval_sub_left (hAc.intervalIntegrable _ _)
      (hAc.intervalIntegrable _ _)]

/-- Blueprint: def:c03_Gamma_eps.  For `ε ≥ 0` the functions `B_ε, P_ε, Γ_ε, Γ̃_ε` are `C^∞`. -/
theorem c03_Gamma_eps_smooth (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) :
    ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε) ∧ ContDiff ℝ (⊤ : ℕ∞) (A_eps_B p ε) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c03_P_eps p ε q.1 q.2) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c03_Gamma_eps_tilde p ε q.1 q.2) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε) := c03_aux_A_contDiff p hε
  have hne : ∀ q : ℝ × ℝ, A_eps p ε q.1 ≠ 0 := fun q => (c03_aux_A_pos p hε q.1).ne'
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ s in (0 : ℝ)..x, A_eps p ε s) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (c03_aux_A_prim_hasDerivAt p hε x).differentiableAt, ?_⟩
    rw [show deriv (fun x => ∫ s in (0 : ℝ)..x, A_eps p ε s) = A_eps p ε from
      funext fun x => (c03_aux_A_prim_hasDerivAt p hε x).deriv]
    exact hA
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c03_P_eps p ε q.1 q.2) := by
    simp_rw [c03_aux_P_eq p hε]
    exact (contDiff_snd.sub contDiff_fst).sub
      (((hF.comp contDiff_snd).sub (hF.comp contDiff_fst)).div (hA.comp contDiff_fst) hne)
  refine ⟨hA, c03_aux_B_contDiff p hε, hP, ?_, ?_⟩
  · unfold c03_Gamma_eps
    exact contDiff_const.mul ((contDiff_const.mul hP).add ((contDiff_snd.sub contDiff_fst).mul
      (contDiff_const.sub ((hA.comp contDiff_snd).div (hA.comp contDiff_fst) hne))))
  · unfold c03_Gamma_eps_tilde
    have hA' : ContDiff ℝ (⊤ : ℕ∞) (deriv (A_eps p ε)) := (contDiff_infty_iff_deriv.1 hA).2
    have hI : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ =>
        ∫ t in (0 : ℝ)..1, (1 + p * (1 - t)) * deriv (A_eps p ε) (q.1 + t * (q.2 - q.1))) := by
      simp_rw [intervalIntegral.integral_of_le zero_le_one]
      have hj : ContDiff ℝ (⊤ : ℕ∞) (fun x : (ℝ × ℝ) × ℝ =>
          (1 + p * (1 - x.2)) * deriv (A_eps p ε) (x.1.1 + x.2 * (x.1.2 - x.1.1))) :=
        (contDiff_const.add (contDiff_const.mul (contDiff_const.sub contDiff_snd))).mul
          (hA'.comp (by fun_prop))
      exact ContDiff.parametric_integral (μ := volume) isCompact_Icc Ioc_subset_Icc_self
        (by simp) hj
    exact (contDiff_const.div (hA.comp contDiff_fst) hne).neg.mul hI

/-- Blueprint: def:c03_I_eps.  `ℐ_ε(f)(y) = ∫ Γ_ε(f'(y), S_f(y,z)) / |y-z|^α dz`. -/
def c03_I_eps (p ε : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) / |y - z| ^ (p + 1)

/-- Vanishing in `𝒟'(ℝ)`: `∫ u φ = 0` for every test function `φ ∈ C_c^∞(ℝ)`. -/
def c03_distrib_zero (u : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, u y * φ y = 0

/-! ## Analysis of the equation -/

/-- Substitution `∫_u^v h = (v-u) ∫_0^1 h(u+t(v-u))`. -/
theorem c03_aux_subst (h : ℝ → ℝ) (u v : ℝ) :
    ∫ s in u..v, h s = (v - u) * ∫ t in (0 : ℝ)..1, h (u + t * (v - u)) := by
  have := intervalIntegral.smul_integral_comp_mul_add (f := h) (a := 0) (b := 1) (v - u) u
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at this
  rw [← this]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only; ring_nf

/-- Scaling bound: `|∂^k [g(√ε ·)](s)| ≤ (√ε)^k M` for `|s| ≤ R`, `0 ≤ ε ≤ 1`. -/
theorem c03_aux_scaled_bound (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (R : ℝ) (k : ℕ) :
    ∃ M, 0 ≤ M ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ s, |s| ≤ R →
      |iteratedDeriv k (fun s => g (Real.sqrt ε * s)) s| ≤ Real.sqrt ε ^ k * M := by
  have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn
    ((hg.continuous_iteratedDeriv k (by exact_mod_cast le_top)).continuousOn)
  refine ⟨max M 0, le_max_right _ _, fun ε hε hε1 s hs => ?_⟩
  rw [iteratedDeriv_comp_const_mul hgk, abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε1
  have hmem : Real.sqrt ε * s ∈ Icc (-R) R := by
    have : |Real.sqrt ε * s| ≤ R := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [abs_nonneg s, Real.sqrt_nonneg ε]
    exact abs_le.1 this
  have := hM _ hmem
  rw [Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_left (this.trans (le_max_left _ _)) (by positivity)

/-- `A_ε(s) = A_1(√ε s)`, `B_ε(s) = B_1(√ε s)`. -/
theorem c03_aux_A_scale (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    A_eps p ε = (fun s => A_eps p 1 (Real.sqrt ε * s)) ∧
    A_eps_B p ε = (fun s => A_eps_B p 1 (Real.sqrt ε * s)) := by
  constructor <;> funext s <;> simp only [A_eps, A_eps_B, mul_pow, Real.sq_sqrt hε, one_mul]

/-- `|1 - A_ε(s)| ≤ (p+1)/2 ε s²`. -/
theorem c03_aux_one_sub_A (p : ℝ) (hp : 0 < p) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    |1 - A_eps p ε s| ≤ (p + 1) / 2 * ε * s ^ 2 := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε) := c03_aux_A_contDiff p hε
  have hftc : ∫ x in (0 : ℝ)..s, deriv (A_eps p ε) x = A_eps p ε s - A_eps p ε 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hA.differentiable (by simp) x)
      ((hA.continuous_deriv (by simp)).intervalIntegrable _ _)
  have hA0 : A_eps p ε 0 = 1 := by simp [A_eps]
  rw [c03_aux_subst, hA0] at hftc
  rw [abs_sub_comm, ← hftc, abs_mul]
  have hint : |∫ t in (0 : ℝ)..1, deriv (A_eps p ε) (0 + t * (s - 0))| ≤
      ∫ t in (0 : ℝ)..1, (p + 1) * ε * |s| * t := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    · refine Eventually.of_forall (fun t ht => ?_)
      rw [Real.norm_eq_abs]
      refine (c03_aux_A_deriv_le p hp hε _).trans (le_of_eq ?_)
      rw [zero_add, sub_zero, abs_mul, abs_of_nonneg ht.1.le]; ring
    · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, integral_id] at hint
  rw [sub_zero]
  calc |s| * |∫ t in (0 : ℝ)..1, deriv (A_eps p ε) (0 + t * s)|
      ≤ |s| * ((p + 1) * ε * |s| * ((1 ^ 2 - 0 ^ 2) / 2)) := by
        simpa using mul_le_mul_of_nonneg_left hint (abs_nonneg s)
    _ = (p + 1) / 2 * ε * s ^ 2 := by rw [← sq_abs s]; ring

/-- Blueprint: lem:c03_A_eps_bounds.  Elementary bounds on `A_ε`, `A_ε'`, `B_ε`, with
constants uniform in `ε ∈ [0,1]` on `[-R,R]`. -/
theorem c03_A_eps_bounds (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 1 ≤ R) :
    (∀ ε, 0 ≤ ε → ε ≤ 1 →
      (∀ s, 0 < A_eps p ε s ∧ A_eps p ε s ≤ 1) ∧ A_eps p ε 0 = 1 ∧ deriv (A_eps p ε) 0 = 0 ∧
      (∀ s, deriv (A_eps p ε) s = -(p + 1) * ε * s * (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1)) ∧
      (∀ s, |deriv (A_eps p ε) s| ≤ (p + 1) * ε * |s|) ∧
      (∀ s, |1 - A_eps p ε s| ≤ (p + 1) / 2 * ε * s ^ 2)) ∧
    ∀ k : ℕ, ∃ C, 0 < C ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ s, |s| ≤ R →
      |iteratedDeriv k (deriv (A_eps p ε)) s| ≤ C * ε ∧
      |iteratedDeriv k (fun s => A_eps p ε s - 1) s| ≤ C * ε ∧
      |iteratedDeriv k (A_eps_B p ε) s| ≤ C := by
  refine ⟨fun ε hε _ => ⟨fun s => ⟨c03_aux_A_pos p hε s, c03_aux_A_le_one p hp hε s⟩,
    by simp [A_eps], by simp [(c03_aux_A_hasDerivAt p hε 0).deriv],
    fun s => (c03_aux_A_hasDerivAt p hε s).deriv, c03_aux_A_deriv_le p hp hε,
    c03_aux_one_sub_A p hp hε⟩, fun k => ?_⟩
  have hA1 : ContDiff ℝ (⊤ : ℕ∞) (A_eps p 1) := c03_aux_A_contDiff p zero_le_one
  have hB1 : ContDiff ℝ (⊤ : ℕ∞) (A_eps_B p 1) := c03_aux_B_contDiff p zero_le_one
  obtain ⟨M1, hM1, h1⟩ := c03_aux_scaled_bound _ hA1 R k
  obtain ⟨M2, hM2, h2⟩ := c03_aux_scaled_bound _ hA1 R (k + 1)
  obtain ⟨M3, hM3, h3⟩ := c03_aux_scaled_bound _ hB1 R k
  set C := (p + 1) * R ^ 2 + (p + 1) * R + M1 + M2 + M3 + 1 with hC
  have hR0 : 0 ≤ R := by linarith
  have hCX : ∀ X, X ≤ C → ∀ ε, 0 ≤ ε → X * ε ≤ C * ε := fun X hX ε hε =>
    mul_le_mul_of_nonneg_right hX hε
  have hpR : 0 ≤ (p + 1) * R := by positivity
  have hpR2 : 0 ≤ (p + 1) * R ^ 2 := by positivity
  refine ⟨C, by positivity, fun ε hε hε1 s hs => ?_⟩
  have hsq0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hsq1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε1
  have hsq2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  have hpow : ∀ j : ℕ, 2 ≤ j → Real.sqrt ε ^ j ≤ ε := fun j hj => by
    calc Real.sqrt ε ^ j = Real.sqrt ε ^ 2 * Real.sqrt ε ^ (j - 2) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ Real.sqrt ε ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hsq0 hsq1) (by positivity)
      _ = ε := by rw [mul_one, hsq2]
  have hRs : |s| ≤ R := hs
  have hA' : |deriv (A_eps p ε) s| ≤ (p + 1) * R * ε := by
    have := c03_aux_A_deriv_le p hp hε s
    have : (p + 1) * ε * |s| ≤ (p + 1) * R * ε := by
      have : 0 ≤ (p + 1) * ε := by positivity
      nlinarith
    linarith
  obtain ⟨hAs, hBs⟩ := c03_aux_A_scale p hε
  have hC1 : (p + 1) * R * ε ≤ C * ε := hCX _ (by linarith) ε hε
  refine ⟨?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hA'.trans hC1
    · rw [← iteratedDeriv_succ', hAs]
      refine (h2 ε hε hε1 s hs).trans ?_
      have := hpow (k + 1) (by omega)
      have : Real.sqrt ε ^ (k + 1) * M2 ≤ ε * M2 := mul_le_mul_of_nonneg_right this hM2
      have := hCX M2 (by linarith) ε hε
      linarith
  · rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · simp only [iteratedDeriv_zero]
        rw [abs_sub_comm]
        refine (c03_aux_one_sub_A p hp hε s).trans ?_
        have : s ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hRs 2
        have : (p + 1) / 2 * ε * s ^ 2 ≤ (p + 1) * R ^ 2 * ε := by
          have : 0 ≤ (p + 1) * ε := by positivity
          nlinarith
        have := hCX ((p + 1) * R ^ 2) (by linarith) ε hε
        linarith
      · rw [iteratedDeriv_one, deriv_sub_const]
        exact hA'.trans hC1
    · have hsub : iteratedDeriv k (fun s => A_eps p ε s - 1) s = iteratedDeriv k (A_eps p ε) s := by
        have := iteratedDeriv_sub (n := k) (x := s) (f := A_eps p ε) (g := fun _ => (1 : ℝ))
          ((c03_aux_A_contDiff p hε).contDiffAt) contDiffAt_const
        rw [show (fun s => A_eps p ε s - 1) = A_eps p ε - fun _ => (1 : ℝ) from rfl, this]
        simp [iteratedDeriv_const, show k ≠ 0 by omega]
      rw [hsub, hAs]
      refine (h1 ε hε hε1 s hs).trans ?_
      have : Real.sqrt ε ^ k * M1 ≤ ε * M1 := mul_le_mul_of_nonneg_right (hpow k hk) hM1
      have := hCX M1 (by linarith) ε hε
      linarith
  · rw [hBs]
    refine (h3 ε hε hε1 s hs).trans ?_
    have : Real.sqrt ε ^ k * M3 ≤ M3 :=
      mul_le_of_le_one_left hM3 (pow_le_one₀ hsq0 hsq1)
    linarith

/-- Blueprint: lem:c03_Gamma_quadratic_factor.  `Γ_ε(u,v) = (u-v)² Γ̃_ε(u,v)` and
`|P_ε(u,v)| ≤ ½ (v-u)² B_ε(u) sup_{[u,v]} |A_ε'|`. -/
theorem c03_Gamma_quadratic_factor (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (u v : ℝ) :
    c03_Gamma_eps p ε u v = (u - v) ^ 2 * c03_Gamma_eps_tilde p ε u v ∧
    ∀ M : ℝ, (∀ s ∈ uIcc u v, |deriv (A_eps p ε) s| ≤ M) →
      |c03_P_eps p ε u v| ≤ 1 / 2 * (v - u) ^ 2 * A_eps_B p ε u * M := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (A_eps p ε) := c03_aux_A_contDiff p hε
  have hAc : Continuous (A_eps p ε) := hA.continuous
  have hA'c : Continuous (deriv (A_eps p ε)) := hA.continuous_deriv (by simp)
  have hAu : 0 < A_eps p ε u := c03_aux_A_pos p hε u
  have hAd : ∀ x, HasDerivAt (A_eps p ε) (deriv (A_eps p ε) x) x :=
    fun x => (hA.differentiable (by simp) x).hasDerivAt
  refine ⟨?_, fun M hM => ?_⟩
  · -- integration by parts identity
    set d := v - u with hd
    have hφ : ∀ t, HasDerivAt (fun t => u + t * d) d t := fun t => by
      simpa using ((hasDerivAt_id t).mul_const d).const_add u
    have hH : ∀ t, HasDerivAt (fun t => (1 + p * (1 - t)) * A_eps p ε (u + t * d))
        (-p * A_eps p ε (u + t * d) +
          (1 + p * (1 - t)) * (deriv (A_eps p ε) (u + t * d) * d)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => 1 + p * (1 - t)) (-p) t := by
        simpa using ((hasDerivAt_id t).const_sub 1 |>.const_mul p).const_add 1
      have h2 := (hAd (u + t * d)).comp t (hφ t)
      exact h1.mul h2
    have hcont1 : Continuous (fun t => A_eps p ε (u + t * d)) := hAc.comp (by fun_prop)
    have hcont2 : Continuous (fun t => (1 + p * (1 - t)) * deriv (A_eps p ε) (u + t * d)) :=
      (by fun_prop : Continuous fun t : ℝ => 1 + p * (1 - t)).mul (hA'c.comp (by fun_prop))
    have hcont3 : Continuous
        (fun t => (1 + p * (1 - t)) * (deriv (A_eps p ε) (u + t * d) * d)) :=
      (by fun_prop : Continuous fun t : ℝ => 1 + p * (1 - t)).mul
        ((hA'c.comp (by fun_prop)).mul continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (fun t _ => hH t) (((continuous_const.mul hcont1).add hcont3).intervalIntegrable _ _)
    rw [intervalIntegral.integral_add (f := fun t => -p * A_eps p ε (u + t * d))
      (g := fun t => (1 + p * (1 - t)) * (deriv (A_eps p ε) (u + t * d) * d))
      ((continuous_const.mul hcont1).intervalIntegrable _ _) (hcont3.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul] at hftc
    have hJ : ∫ t in (0 : ℝ)..1, (1 + p * (1 - t)) * (deriv (A_eps p ε) (u + t * d) * d) =
        (∫ t in (0 : ℝ)..1, (1 + p * (1 - t)) * deriv (A_eps p ε) (u + t * d)) * d := by
      rw [← intervalIntegral.integral_mul_const]; congr 1; funext t; ring
    rw [hJ] at hftc
    simp only [mul_one, sub_self, mul_zero, add_zero, zero_mul, sub_zero, one_mul] at hftc
    have hP : c03_P_eps p ε u v = d - (∫ s in u..v, A_eps p ε s) / A_eps p ε u := by
      unfold c03_P_eps
      rw [intervalIntegral.integral_sub intervalIntegrable_const
          ((hAc.div_const _).intervalIntegrable _ _), intervalIntegral.integral_div,
        intervalIntegral.integral_const, smul_eq_mul, mul_one]
    have hv : u + d = v := by rw [hd]; ring
    rw [hv] at hftc
    unfold c03_Gamma_eps c03_Gamma_eps_tilde
    rw [hP, c03_aux_subst (A_eps p ε) u v, ← hd]
    generalize (∫ t in (0 : ℝ)..1, (1 + p * (1 - t)) * deriv (A_eps p ε) (u + t * d)) = J at hftc ⊢
    generalize (∫ t in (0 : ℝ)..1, A_eps p ε (u + t * d)) = K at hftc ⊢
    have hvu : u - v = -d := by rw [hd]; ring
    rw [hvu]
    field_simp
    linear_combination (calpha p * d) * hftc
  · have hBu : A_eps_B p ε u = (A_eps p ε u)⁻¹ := c03_aux_B_eq p hε u
    have hP2 : c03_P_eps p ε u v =
        (v - u) * ∫ t in (0 : ℝ)..1, (1 - A_eps p ε (u + t * (v - u)) / A_eps p ε u) := by
      unfold c03_P_eps; exact c03_aux_subst (fun s => 1 - A_eps p ε s / A_eps p ε u) u v
    have hpt : ∀ t ∈ Icc (0 : ℝ) 1, |1 - A_eps p ε (u + t * (v - u)) / A_eps p ε u| ≤
        (A_eps p ε u)⁻¹ * M * |v - u| * t := by
      intro t ht
      have hmem : u + t * (v - u) ∈ uIcc u v := by
        rw [Set.mem_uIcc]
        rcases le_total u v with h | h
        · left; constructor <;> nlinarith [ht.1, ht.2]
        · right; constructor <;> nlinarith [ht.1, ht.2]
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun x _ => (hAd x).differentiableAt) (fun x hx => by rw [Real.norm_eq_abs]; exact hM x hx)
        (convex_uIcc u v) left_mem_uIcc hmem
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        show u + t * (v - u) - u = t * (v - u) by ring, abs_mul, abs_of_nonneg ht.1] at hmvt
      have h1 : 1 - A_eps p ε (u + t * (v - u)) / A_eps p ε u =
          (A_eps p ε u)⁻¹ * (A_eps p ε u - A_eps p ε (u + t * (v - u))) := by
        field_simp
      rw [h1, abs_mul, abs_of_pos (inv_pos.2 hAu), abs_sub_comm]
      calc (A_eps p ε u)⁻¹ * |A_eps p ε (u + t * (v - u)) - A_eps p ε u|
          ≤ (A_eps p ε u)⁻¹ * (M * (t * |v - u|)) :=
            mul_le_mul_of_nonneg_left hmvt (inv_nonneg.2 hAu.le)
        _ = (A_eps p ε u)⁻¹ * M * |v - u| * t := by ring
    have hint : |∫ t in (0 : ℝ)..1, (1 - A_eps p ε (u + t * (v - u)) / A_eps p ε u)| ≤
        ∫ t in (0 : ℝ)..1, (A_eps p ε u)⁻¹ * M * |v - u| * t := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · exact Eventually.of_forall (fun t ht => by
          rw [Real.norm_eq_abs]; exact hpt t (Ioc_subset_Icc_self ht))
      · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    have hcalc : ∫ t in (0 : ℝ)..1, (A_eps p ε u)⁻¹ * M * |v - u| * t =
        (A_eps p ε u)⁻¹ * M * |v - u| / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    rw [hP2, abs_mul, hBu]
    calc |v - u| * |∫ t in (0 : ℝ)..1, (1 - A_eps p ε (u + t * (v - u)) / A_eps p ε u)|
        ≤ |v - u| * ((A_eps p ε u)⁻¹ * M * |v - u| / 2) :=
          mul_le_mul_of_nonneg_left (hint.trans hcalc.le) (abs_nonneg _)
      _ = 1 / 2 * (v - u) ^ 2 * (A_eps p ε u)⁻¹ * M := by rw [← sq_abs (v - u)]; ring


/-- The radial dominating function `Λ|t|^{-p}` (`|t| ≤ 1`), `M|t|^{-α}` (`|t| > 1`). -/
def c03_aux_psi (p Λ M t : ℝ) : ℝ := if |t| ≤ 1 then Λ * |t| ^ (-p) else M * |t| ^ (-(p + 1))

/-- `ψ ≥ 0`. -/
theorem c03_aux_psi_nonneg (p : ℝ) {Λ M : ℝ} (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (t : ℝ) :
    0 ≤ c03_aux_psi p Λ M t := by
  unfold c03_aux_psi; split_ifs <;> positivity

/-- `ψ` is integrable on `ℝ`. -/
theorem c03_aux_psi_integrable (p Λ M : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Integrable (c03_aux_psi p Λ M) := by
  set φ : ℝ → ℝ := fun t => if t ≤ 1 then Λ * t ^ (-p) else M * t ^ (-(p + 1))
  have hIoc : IntegrableOn (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -p) (by linarith))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.const_mul Λ
  have hIoi : IntegrableOn (fun t : ℝ => M * t ^ (-(p + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have e1 : EqOn φ (fun t : ℝ => Λ * t ^ (-p)) (Ioc 0 1) := by
    intro t ht; simp [φ, ht.2]
  have e2 : EqOn φ (fun t : ℝ => M * t ^ (-(p + 1))) (Ioi 1) := by
    intro t ht; simp [φ, not_le.mpr (show (1:ℝ) < t from ht)]
  have i1 : IntegrableOn φ (Ioc 0 1) := hIoc.congr_fun e1.symm measurableSet_Ioc
  have i2 : IntegrableOn φ (Ioi 1) := hIoi.congr_fun e2.symm measurableSet_Ioi
  have hU : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  have hφ : IntegrableOn φ (Ioi 0) := hU ▸ i1.union i2
  have hf' : IntegrableOn (fun x => φ |x|) (Ioi 0) := by
    refine hφ.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  have int_Iic : IntegrableOn (fun x ↦ φ |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  have := int_Iic.union hf'
  rw [Iic_union_Ioi, integrableOn_univ] at this
  exact this

/-- Pointwise domination by `ψ`: `|N|/|t|^α ≤ ψ(t)` from `|N| ≤ Λ|t|` (`|t| ≤ 1`), `|N| ≤ M`. -/
theorem c03_aux_psi_bound (p : ℝ) (hp : 0 < p) {Λ M : ℝ} (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (t N : ℝ)
    (hnear : |t| ≤ 1 → |N| ≤ Λ * |t|) (hfar : |N| ≤ M) :
    |N| / |t| ^ (p + 1) ≤ c03_aux_psi p Λ M t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [abs_zero, Real.zero_rpow (by linarith : p + 1 ≠ 0), div_zero]
    exact c03_aux_psi_nonneg p hΛ hM 0
  have hpos : 0 < |t| := abs_pos.2 ht
  have hden : 0 < |t| ^ (p + 1) := Real.rpow_pos_of_pos hpos _
  unfold c03_aux_psi
  split_ifs with h1
  · rw [div_le_iff₀ hden]
    calc |N| ≤ Λ * |t| := hnear h1
      _ = Λ * |t| ^ (-p) * |t| ^ (p + 1) := by
          rw [mul_assoc, ← Real.rpow_add hpos]; simp
  · rw [div_le_iff₀ hden]
    calc |N| ≤ M := hfar
      _ = M * |t| ^ (-(p + 1)) * |t| ^ (p + 1) := by
          rw [mul_assoc, ← Real.rpow_add hpos]; simp

/-- Monotonicity of `ψ` in the constants. -/
theorem c03_aux_psi_mono (p : ℝ) {Λ M Λ' M' : ℝ} (hΛ : Λ ≤ Λ') (hM : M ≤ M') (t : ℝ) :
    c03_aux_psi p Λ M t ≤ c03_aux_psi p Λ' M' t := by
  unfold c03_aux_psi
  split_ifs
  · exact mul_le_mul_of_nonneg_right hΛ (by positivity)
  · exact mul_le_mul_of_nonneg_right hM (by positivity)

/-- The secant at `z = y - t`, `t ≠ 0`. -/
theorem c03_aux_secant_sub (f : ℝ → ℝ) (y t : ℝ) (ht : t ≠ 0) :
    c01_secant f y (y - t) = (f y - f (y - t)) / t := by
  unfold c01_secant
  split_ifs with h
  · exact absurd (by linarith : t = 0) ht
  · rw [sub_sub_cancel]

/-- Measurability of `z ↦ S_f(y,z)` for continuous `f`. -/
theorem c03_aux_secant_measurable (f : ℝ → ℝ) (hf : Continuous f) (y : ℝ) :
    Measurable (fun z => c01_secant f y z) := by
  unfold c01_secant
  exact Measurable.ite (measurableSet_eq_fun measurable_const measurable_id) measurable_const
    ((measurable_const.sub hf.measurable).div (measurable_const.sub measurable_id))

/-- `|S_f(y,z)| ≤ K` when `|f'| ≤ K`. -/
theorem c03_aux_secant_le (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ x, |deriv f x| ≤ K)
    (y z : ℝ) : |c01_secant f y z| ≤ K := by
  unfold c01_secant
  split_ifs with h
  · exact hK y
  · have hyz : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 h)
    have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (hf.differentiable one_ne_zero x)) (fun x _ => by
        rw [Real.norm_eq_abs]; exact hK x) (mem_univ z) (mem_univ y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    rw [abs_div, div_le_iff₀ hyz]
    exact this

/-- `|S_f(y,y-t) - f'(y)| ≤ L|t|` if `f'` is `L`-Lipschitz on `[y-|t|, y+|t|]`. -/
theorem c03_aux_secant_sub_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (y t L : ℝ)
    (hL : ∀ x, |x - y| ≤ |t| → |deriv f x - deriv f y| ≤ L * |t|) :
    |c01_secant f y (y - t) - deriv f y| ≤ L * |t| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [c01_secant]
  rw [c03_aux_secant_sub f y t ht]
  set g : ℝ → ℝ := fun x => f x - deriv f y * x
  have hg : ∀ x, HasDerivAt g (deriv f x - deriv f y) x := fun x => by
    have := ((hf.differentiable one_ne_zero x).hasDerivAt).sub ((hasDerivAt_id x).const_mul (deriv f y))
    exact this.congr_deriv (by simp)
  have hmv := (convex_uIcc (y - t) y).norm_image_sub_le_of_norm_deriv_le
    (f := g) (fun x _ => (hg x).differentiableAt) (fun x hx => by
      rw [(hg x).deriv, Real.norm_eq_abs]
      apply hL
      rw [Set.mem_uIcc] at hx
      rcases hx with hx | hx <;> rw [abs_le] <;> constructor <;>
        cases abs_cases t <;> linarith [hx.1, hx.2])
    (left_mem_uIcc) (right_mem_uIcc)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_sub_cancel] at hmv
  have hpos : 0 < |t| := abs_pos.2 ht
  have : (f y - f (y - t)) / t - deriv f y = (g y - g (y - t)) / t := by
    simp only [g]; field_simp; ring
  rw [this, abs_div, div_le_iff₀ hpos]
  calc |g y - g (y - t)| ≤ L * |t| * |t| := hmv
    _ = L * |t| * |t| := rfl

/-- Linear bounds on `1 - A_ε(v)/A_ε(u)`, `P_ε(u,v)`, `Γ_ε(u,v)` when `B_ε(u) ≤ MB`. -/
theorem c03_aux_PG_bound (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) {MB : ℝ} (u : ℝ)
    (hBu : A_eps_B p ε u ≤ MB) (v : ℝ) :
    |1 - A_eps p ε v / A_eps p ε u| ≤ 1 + MB ∧
    |c03_P_eps p ε u v| ≤ (1 + MB) * |v - u| ∧
    |c03_Gamma_eps p ε u v| ≤ |calpha p| * (p + 1) * (1 + MB) * |v - u| := by
  have hρ : ∀ s, |1 - A_eps p ε s / A_eps p ε u| ≤ 1 + MB := fun s => by
    have h1 : A_eps p ε s / A_eps p ε u = A_eps p ε s * A_eps_B p ε u := by
      rw [c03_aux_B_eq p hε u, div_eq_mul_inv]
    have hA0 := c03_aux_A_pos p hε s
    have hA1 := c03_aux_A_le_one p hp hε s
    have hB0 : 0 < A_eps_B p ε u := by rw [c03_aux_B_eq p hε u]; exact inv_pos.2 (c03_aux_A_pos p hε u)
    rw [h1]
    have : A_eps p ε s * A_eps_B p ε u ≤ MB := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [mul_pos hA0 hB0]
  have hP : |c03_P_eps p ε u v| ≤ (1 + MB) * |v - u| := by
    unfold c03_P_eps
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v) (C := 1 + MB)
      (f := fun s => 1 - A_eps p ε s / A_eps p ε u) (fun s _ => by
        rw [Real.norm_eq_abs]; exact hρ s)
    rw [Real.norm_eq_abs] at this; exact this
  refine ⟨hρ v, hP, ?_⟩
  unfold c03_Gamma_eps
  rw [abs_mul]
  have h2 : |p * c03_P_eps p ε u v + (v - u) * (1 - A_eps p ε v / A_eps p ε u)| ≤
      (p + 1) * (1 + MB) * |v - u| := by
    calc _ ≤ |p * c03_P_eps p ε u v| + |(v - u) * (1 - A_eps p ε v / A_eps p ε u)| := abs_add_le _ _
      _ = p * |c03_P_eps p ε u v| + |v - u| * |1 - A_eps p ε v / A_eps p ε u| := by
          rw [abs_mul, abs_mul, abs_of_pos hp]
      _ ≤ p * ((1 + MB) * |v - u|) + |v - u| * (1 + MB) := by
          gcongr
          exact hρ v
      _ = (p + 1) * (1 + MB) * |v - u| := by ring
  calc |calpha p| * |p * c03_P_eps p ε u v + (v - u) * (1 - A_eps p ε v / A_eps p ε u)|
      ≤ |calpha p| * ((p + 1) * (1 + MB) * |v - u|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = _ := by ring

/-- All the pointwise bounds for the integrands of `|D|^p f'`, `𝒥̃_ε`, `ℐ_ε` and the
integration by parts, at `z = y - t`, `|y| ≤ R`: `≤ Λ|t|` for `|t| ≤ 1`, `≤ M` always. -/
theorem c03_aux_profile_bounds (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) (R : ℝ) :
    ∃ Λ M : ℝ, 0 ≤ Λ ∧ 0 ≤ M ∧ ∀ y ∈ Icc (-R) R, ∀ t : ℝ, ∀ B : ℝ, (B = Λ * |t| ∧ |t| ≤ 1) ∨ B = M →
      |deriv f y - deriv f (y - t)| ≤ B ∧
      |(deriv f y - deriv f (y - t)) *
        (A_eps p ε (c01_secant f y (y - t)) - A_eps p ε (deriv f y))| ≤ B ∧
      |(deriv f y - deriv f (y - t)) *
        (A_eps p ε (c01_secant f y (y - t)) / A_eps p ε (deriv f y) - 1)| ≤ B ∧
      |c03_Gamma_eps p ε (deriv f y) (c01_secant f y (y - t))| ≤ B ∧
      |c03_P_eps p ε (deriv f y) (c01_secant f y (y - t))| ≤ B ∧
      |(c01_secant f y (y - t) - deriv f y) *
        (1 - A_eps p ε (c01_secant f y (y - t)) / A_eps p ε (deriv f y))| ≤ B := by
  obtain ⟨hC1, ⟨K0, hK0⟩, hLL⟩ := hf
  set K := max K0 0
  have hK : ∀ x, |deriv f x| ≤ K := fun x => (hK0 x).trans (le_max_left _ _)
  have hK0' : 0 ≤ K := le_max_right _ _
  obtain ⟨Ln, hLn⟩ := (hLL.locallyLipschitzOn (s := Icc (-R - 1) (R + 1))).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  set L : ℝ := (Ln : ℝ)
  have hL0 : 0 ≤ L := Ln.2
  have hL : ∀ x ∈ Icc (-R - 1) (R + 1), ∀ w ∈ Icc (-R - 1) (R + 1),
      |deriv f x - deriv f w| ≤ L * |x - w| := fun x hx w hw => by
    have := hLn.dist_le_mul x hx w hw
    rwa [Real.dist_eq, Real.dist_eq] at this
  obtain ⟨MB0, hMB0⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
    (c03_aux_B_contDiff p hε (n := 0)).continuous.continuousOn
  set MB := max MB0 0
  have hMB : ∀ u, |u| ≤ K → A_eps_B p ε u ≤ MB := fun u hu => by
    have := hMB0 u (abs_le.1 hu)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hMB0' : 0 ≤ MB := le_max_right _ _
  set c := (1 + MB) * (|calpha p| * (p + 1) + 1)
  have hc1 : 1 ≤ c := by
    have : 0 ≤ |calpha p| * (p + 1) := by positivity
    nlinarith
  have hc2 : 1 + MB ≤ c := by
    have : 0 ≤ |calpha p| * (p + 1) := by positivity
    nlinarith
  have hc3 : |calpha p| * (p + 1) * (1 + MB) ≤ c := by
    have : 0 ≤ |calpha p| * (p + 1) := by positivity
    nlinarith
  refine ⟨c * L, c * (2 * K), by positivity, by positivity, fun y hy t B hB => ?_⟩
  set u := deriv f y
  set S := c01_secant f y (y - t)
  have hu : |u| ≤ K := hK y
  have hSK : |S| ≤ K := c03_aux_secant_le f hC1 hK y (y - t)
  -- `|d| ≤ X`, `|S - u| ≤ X` with `X = B / c`
  have hX : |deriv f y - deriv f (y - t)| ≤ B / c ∧ |S - u| ≤ B / c := by
    rcases hB with ⟨hB, ht⟩ | hB
    · 
      rw [hB, mul_comm c L, mul_assoc, mul_comm c, ← mul_assoc, mul_div_assoc,
        div_self (by linarith : c ≠ 0), mul_one]
      have hyR := hy
      have hmem : ∀ x, |x - y| ≤ |t| → x ∈ Icc (-R - 1) (R + 1) := fun x hx => by
        rw [abs_le] at hx; have := abs_le.1 ht
        exact ⟨by linarith [hyR.1], by linarith [hyR.2]⟩
      have hyy : y ∈ Icc (-R - 1) (R + 1) := hmem y (by simp)
      constructor
      · have := hL y hyy (y - t) (hmem _ (by simp))
        rwa [sub_sub_cancel] at this
      · apply c03_aux_secant_sub_deriv f hC1 y t L
        intro x hx
        exact (hL x (hmem x hx) y hyy).trans (mul_le_mul_of_nonneg_left hx hL0)
    · rw [hB, mul_div_cancel_left₀ _ (by linarith : c ≠ 0)]
      constructor
      · calc _ ≤ |deriv f y| + |deriv f (y - t)| := abs_sub _ _
          _ ≤ 2 * K := by linarith [hK y, hK (y - t)]
      · calc _ ≤ |S| + |u| := abs_sub _ _
          _ ≤ 2 * K := by linarith
  obtain ⟨hX1, hX2⟩ := hX
  have hB0 : 0 ≤ B / c := (abs_nonneg _).trans hX1
  have hBc : B = c * (B / c) := by field_simp
  obtain ⟨hρ, hP, hΓ⟩ := c03_aux_PG_bound p ε hp hε u (hMB u hu) S
  have hAA : |A_eps p ε S - A_eps p ε u| ≤ 1 := by
    have := c03_aux_A_pos p hε S; have := c03_aux_A_pos p hε u
    have := c03_aux_A_le_one p hp hε S; have := c03_aux_A_le_one p hp hε u
    rw [abs_le]; constructor <;> linarith
  have hρ' : |A_eps p ε S / A_eps p ε u - 1| ≤ 1 + MB := by rw [abs_sub_comm]; exact hρ
  have hSu : |S - u| = |u - S| := abs_sub_comm _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBc]; nlinarith
  · rw [abs_mul, hBc]; nlinarith [abs_nonneg (deriv f y - deriv f (y - t))]
  · rw [abs_mul, hBc]
    calc _ ≤ B / c * (1 + MB) := mul_le_mul hX1 hρ' (abs_nonneg _) hB0
      _ ≤ _ := by nlinarith
  · rw [hBc]
    calc _ ≤ |calpha p| * (p + 1) * (1 + MB) * |S - u| := hΓ
      _ ≤ |calpha p| * (p + 1) * (1 + MB) * (B / c) :=
          mul_le_mul_of_nonneg_left hX2 (by positivity)
      _ ≤ _ := by nlinarith
  · rw [hBc]
    calc _ ≤ (1 + MB) * |S - u| := hP
      _ ≤ (1 + MB) * (B / c) := mul_le_mul_of_nonneg_left hX2 (by positivity)
      _ ≤ _ := by nlinarith
  · rw [abs_mul, hBc]
    calc _ ≤ B / c * (1 + MB) := mul_le_mul hX2 hρ (abs_nonneg _) hB0
      _ ≤ _ := by nlinarith

/-- Generic dominated-convergence package: a kernel `G y z` dominated (in `t = y - z`) by `ψ`
locally uniformly in `y`, measurable in `z`, continuous in `y` for `t ≠ 0`, gives integrable
`G y` and continuous `y ↦ ∫ G y`. -/
theorem c03_aux_dom (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (G : ℝ → ℝ → ℝ)
    (hmeas : ∀ y, Measurable (G y))
    (hdom : ∀ R : ℝ, ∃ Λ M : ℝ, 0 ≤ Λ ∧ 0 ≤ M ∧ ∀ y ∈ Icc (-R) R, ∀ t : ℝ,
      |G y (y - t)| ≤ c03_aux_psi p Λ M t)
    (hcont : ∀ t : ℝ, t ≠ 0 → Continuous (fun y => G y (y - t))) :
    (∀ y, Integrable (G y)) ∧ Continuous (fun y => ∫ z, G y z) := by
  have hF : ∀ y, Integrable (fun t => G y (y - t)) := fun y => by
    obtain ⟨Λ, M, -, -, h⟩ := hdom |y|
    refine (c03_aux_psi_integrable p Λ M hp hp1).mono'
      ((hmeas y).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs]
    exact h y (abs_le.1 le_rfl) t
  refine ⟨fun y => ?_, ?_⟩
  · have := (hF y).comp_sub_left y
    simpa only [sub_sub_cancel] using this
  · have he : (fun y => ∫ z, G y z) = fun y => ∫ t, G y (y - t) :=
      funext fun y => (integral_sub_left_eq_self (G y) volume y).symm
    rw [he, continuous_iff_continuousAt]
    intro y₀
    obtain ⟨Λ, M, -, -, h⟩ := hdom (|y₀| + 1)
    have hnear : ∀ᶠ y in 𝓝 y₀, y ∈ Icc (-(|y₀| + 1)) (|y₀| + 1) := by
      filter_upwards [Ioo_mem_nhds (show y₀ - 1 < y₀ by linarith) (show y₀ < y₀ + 1 by linarith)]
        with y hy
      constructor <;> cases abs_cases y₀ <;> linarith [hy.1, hy.2]
    have hae : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]; simp
    refine continuousAt_of_dominated (bound := c03_aux_psi p Λ M)
      (Eventually.of_forall fun y =>
        ((hmeas y).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (hnear.mono fun y hy => Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]; exact h y hy t)
      (c03_aux_psi_integrable p Λ M hp hp1) ?_
    filter_upwards [hae] with t ht
    exact (hcont t ht).continuousAt

/-- `|a / k * b| = |a * b| / k` for `k = |t|^α ≥ 0`. -/
theorem c03_aux_rearr (a b t q : ℝ) : |a / |t| ^ q * b| = |a * b| / |t| ^ q := by
  rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) q)]; ring

/-- A continuous function vanishing in `𝒟'` vanishes identically. -/
theorem c03_aux_distrib_zero_iff (u : ℝ → ℝ) (hu : Continuous u) :
    c03_distrib_zero u ↔ ∀ y, u y = 0 := by
  constructor
  · intro h
    have hae : ∀ᵐ x, u x = 0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hu.locallyIntegrable (fun g hg hgc => by
        have := h g hg hgc
        simpa [smul_eq_mul, mul_comm] using this)
    have := (Continuous.ae_eq_iff_eq volume hu continuous_const).1 hae
    exact fun y => congrFun this y
  · intro h φ _ _
    simp [h]

/-- Integrability part of `c03_aux_dom` (single `y`). -/
theorem c03_aux_dom_int (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (g : ℝ → ℝ) (y : ℝ)
    (hmeas : Measurable g) (Λ M : ℝ) (h : ∀ t : ℝ, |g (y - t)| ≤ c03_aux_psi p Λ M t) :
    Integrable g := by
  have hF : Integrable (fun t => g (y - t)) :=
    (c03_aux_psi_integrable p Λ M hp hp1).mono'
      (hmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact h t)
  have := hF.comp_sub_left y
  simpa only [sub_sub_cancel] using this

/-- Directional iterated derivatives: `D^jF(q)(w,…,w) = (d/dt)^j F(q+tw)|_{t=0}`. -/
theorem c03_aux_dir_deriv (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (q w : ℝ × ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j F q (fun _ => w) = iteratedDeriv j (fun t : ℝ => F (q + t • w)) (0 : ℝ) := by
  set g : ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) w
  have hg : ∀ t, g t = t • w := fun t => rfl
  have hF' : ContDiff ℝ (⊤ : ℕ∞) (fun x => F (x + q)) := hF.comp (contDiff_id.add contDiff_const)
  have he : (fun t : ℝ => F (q + t • w)) = (fun x => F (x + q)) ∘ g := by
    funext t; simp only [Function.comp, hg, add_comm]
  rw [he, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right g hF' 0 (by exact_mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
  simp [hg]

/-- Norm of iterated derivatives of `q ↦ c H(c q)`. -/
theorem c03_aux_scale_norm (H : ℝ × ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (c : ℝ) (q : ℝ × ℝ)
    (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q => c * H (c • q)) q‖ ≤ |c| ^ (j + 1) * ‖iteratedFDeriv ℝ j H (c • q)‖ := by
  set g : ℝ × ℝ →L[ℝ] ℝ × ℝ := c • ContinuousLinearMap.id ℝ (ℝ × ℝ)
  have hg : ∀ x, g x = c • x := fun x => rfl
  have hgn : ‖g‖ ≤ |c| := by
    refine (norm_smul_le c (ContinuousLinearMap.id ℝ (ℝ × ℝ))).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have he : (fun q => c * H (c • q)) = c • (H ∘ g) := by
    funext x; simp [hg]
  rw [he, iteratedFDeriv_const_smul_apply ((hH.comp g.contDiff).contDiffAt.of_le
      (by exact_mod_cast le_top)),
    ContinuousLinearMap.iteratedFDeriv_comp_right g hH q (by exact_mod_cast le_top), norm_smul,
    Real.norm_eq_abs, hg]
  calc |c| * ‖(iteratedFDeriv ℝ j H (c • q)).compContinuousLinearMap fun _ => g‖
      ≤ |c| * (‖iteratedFDeriv ℝ j H (c • q)‖ * ∏ _i : Fin j, ‖g‖) :=
        mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
          (abs_nonneg c)
    _ ≤ |c| * (‖iteratedFDeriv ℝ j H (c • q)‖ * |c| ^ j) := by
        gcongr
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_pow_left₀ (norm_nonneg _) hgn j
    _ = _ := by ring

/-- `A_ε'(s) = √ε A_1'(√ε s)`. -/
theorem c03_aux_A_deriv_scale (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    deriv (A_eps p ε) s = Real.sqrt ε * deriv (A_eps p 1) (Real.sqrt ε * s) := by
  rw [c03_aux_A_deriv p hε, c03_aux_A_deriv p zero_le_one]
  simp only [mul_pow, Real.sq_sqrt hε, one_mul]
  have : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  set X := (1 + ε * s ^ 2) ^ (-(p + 1) / 2 - 1)
  linear_combination (-(p + 1) * s * X) * this.symm

/-- Scaling of `Γ̃_ε`: `Γ̃_ε(q) = √ε Γ̃_1(√ε q)`. -/
theorem c03_aux_Gt_scale (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (fun q : ℝ × ℝ => c03_Gamma_eps_tilde p ε q.1 q.2) =
      fun q => Real.sqrt ε * c03_Gamma_eps_tilde p 1 (Real.sqrt ε • q).1 (Real.sqrt ε • q).2 := by
  funext q
  unfold c03_Gamma_eps_tilde
  have hA := (c03_aux_A_scale p hε).1
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show A_eps p ε q.1 = A_eps p 1 (Real.sqrt ε * q.1) by rw [hA]]
  simp_rw [c03_aux_A_deriv_scale p hε]
  rw [← intervalIntegral.integral_const_mul]
  have : ∀ t : ℝ, (1 + p * (1 - t)) * (Real.sqrt ε * deriv (A_eps p 1) (Real.sqrt ε * (q.1 + t * (q.2 - q.1)))) =
      Real.sqrt ε * ((1 + p * (1 - t)) * deriv (A_eps p 1)
        (Real.sqrt ε * q.1 + t * (Real.sqrt ε * q.2 - Real.sqrt ε * q.1))) := fun t => by ring_nf
  simp_rw [this, intervalIntegral.integral_const_mul]
  ring

/-- Explicit bound `|Γ̃_ε(u,v)| ≤ c₀ ε (|u|+|v|)` for `|u| ≤ M`, `0 ≤ ε ≤ 1`. -/
theorem c03_aux_Gt_bound (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (M : ℝ) (u v : ℝ)
    (hu : |u| ≤ M) :
    |c03_Gamma_eps_tilde p ε u v| ≤
      |calpha p| * (1 + M ^ 2) ^ ((p + 1) / 2) * ((1 + p) * (p + 1)) * ε * (|u| + |v|) := by
  unfold c03_Gamma_eps_tilde
  have hAu := c03_aux_A_pos p hε u
  have hB : (A_eps p ε u)⁻¹ ≤ (1 + M ^ 2) ^ ((p + 1) / 2) := by
    rw [← c03_aux_B_eq p hε u]
    unfold A_eps_B
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    have : u ^ 2 ≤ M ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
    nlinarith [sq_nonneg u]
  have hI : |∫ t in (0 : ℝ)..1, (1 + p * (1 - t)) * deriv (A_eps p ε) (u + t * (v - u))| ≤
      (1 + p) * ((p + 1) * ε * (|u| + |v|)) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := (1 + p) * ((p + 1) * ε * (|u| + |v|)))
      (f := fun t => (1 + p * (1 - t)) * deriv (A_eps p ε) (u + t * (v - u))) (fun t ht => by
        rw [Set.uIoc_of_le zero_le_one] at ht
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |1 + p * (1 - t)| ≤ 1 + p := by
          rw [abs_of_nonneg (by nlinarith [ht.2])]; nlinarith [ht.1]
        have h2 : |u + t * (v - u)| ≤ |u| + |v| := by
          have : u + t * (v - u) = (1 - t) * u + t * v := by ring
          rw [this]
          calc |(1 - t) * u + t * v| ≤ |(1 - t) * u| + |t * v| := abs_add_le _ _
            _ = (1 - t) * |u| + t * |v| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [ht.2]), abs_of_pos ht.1]
            _ ≤ |u| + |v| := by nlinarith [abs_nonneg u, abs_nonneg v, ht.1, ht.2]
        have h3 := c03_aux_A_deriv_le p hp hε (u + t * (v - u))
        have h4 : (p + 1) * ε * |u + t * (v - u)| ≤ (p + 1) * ε * (|u| + |v|) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        exact mul_le_mul h1 (h3.trans h4) (abs_nonneg _) (by linarith))
    simpa using this
  rw [abs_mul, abs_neg, abs_div, abs_of_pos hAu, div_eq_mul_inv]
  calc |calpha p| * (A_eps p ε u)⁻¹ * |∫ t in (0 : ℝ)..1, (1 + p * (1 - t)) *
        deriv (A_eps p ε) (u + t * (v - u))|
      ≤ |calpha p| * (1 + M ^ 2) ^ ((p + 1) / 2) * ((1 + p) * ((p + 1) * ε * (|u| + |v|))) := by
        gcongr
    _ = _ := by ring

/-- Uniform bounds `‖∇^j Γ̃_ε(u,v)‖ ≤ C_j ε` on `[-R,R]²`, `0 ≤ ε ≤ 1`. -/
theorem c03_aux_Gt_deriv_bound (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 0 ≤ R) :
    ∃ Ct : ℕ → ℝ, (∀ j, 0 ≤ Ct j) ∧ ∀ j, ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ u v : ℝ, |u| ≤ R → |v| ≤ R →
      ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => c03_Gamma_eps_tilde p ε q.1 q.2) (u, v)‖ ≤ Ct j * ε := by
  have hG1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => c03_Gamma_eps_tilde p 1 q.1 q.2) :=
    (c03_Gamma_eps_smooth p 1 hp hp1 zero_le_one).2.2.2.2
  set c0 := |calpha p| * (1 + R ^ 2) ^ ((p + 1) / 2) * ((1 + p) * (p + 1))
  have hc0 : 0 ≤ c0 := by positivity
  have hbox : IsCompact (Icc (-R) R ×ˢ Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
  choose M hM using fun j : ℕ => hbox.exists_bound_of_continuousOn
    ((hG1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)
  refine ⟨fun j => c0 * (2 * R) + max (M j) 0, fun j => by positivity, fun j ε hε hε1 u v hu hv => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    refine (c03_aux_Gt_bound p ε hp hε hε1 R u v hu).trans ?_
    have : |u| + |v| ≤ 2 * R := by linarith
    have : c0 * ε * (|u| + |v|) ≤ c0 * (2 * R) * ε := by
      calc c0 * ε * (|u| + |v|) ≤ c0 * ε * (2 * R) :=
            mul_le_mul_of_nonneg_left this (mul_nonneg hc0 hε)
        _ = _ := by ring
    nlinarith [le_max_right (M 0) 0]
  · rw [c03_aux_Gt_scale p hε]
    refine (c03_aux_scale_norm _ hG1 (Real.sqrt ε) (u, v) j).trans ?_
    have hs0 := Real.sqrt_nonneg ε
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε1
    have hmem : Real.sqrt ε • (u, v) ∈ Icc (-R) R ×ˢ Icc (-R) R := by
      simp only [Prod.smul_mk, smul_eq_mul, Set.mem_prod, Set.mem_Icc]
      have h1 : |Real.sqrt ε * u| ≤ R := by
        rw [abs_mul, abs_of_nonneg hs0]; nlinarith [abs_nonneg u]
      have h2 : |Real.sqrt ε * v| ≤ R := by
        rw [abs_mul, abs_of_nonneg hs0]; nlinarith [abs_nonneg v]
      exact ⟨abs_le.1 h1, abs_le.1 h2⟩
    have hb := (hM j _ hmem).trans (le_max_left (M j) 0)
    have hpow : |Real.sqrt ε| ^ (j + 1) ≤ ε := by
      rw [abs_of_nonneg hs0]
      calc Real.sqrt ε ^ (j + 1) = Real.sqrt ε ^ 2 * Real.sqrt ε ^ (j - 1) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ Real.sqrt ε ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hs0 hs1) (by positivity)
        _ = ε := by rw [mul_one, Real.sq_sqrt hε]
    calc |Real.sqrt ε| ^ (j + 1) * ‖iteratedFDeriv ℝ j
          (fun q : ℝ × ℝ => c03_Gamma_eps_tilde p 1 q.1 q.2) (Real.sqrt ε • (u, v))‖
        ≤ ε * max (M j) 0 := mul_le_mul hpow hb (norm_nonneg _) hε
      _ ≤ (c0 * (2 * R) + max (M j) 0) * ε := by
          nlinarith [mul_nonneg (mul_nonneg hc0 (by linarith : (0:ℝ) ≤ 2 * R)) hε]

/-- Derivatives of `(u-v)²`: `‖∇^i (u-v)²‖ ≤ (u-v)², 4|u-v|, 8, 0` for `i = 0, 1, 2, ≥ 3`. -/
theorem c03_aux_sqL_bound (i : ℕ) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) q‖ ≤
      if i = 0 then (q.1 - q.2) ^ 2 else if i = 1 then 4 * |q.1 - q.2| else if i = 2 then 8 else 0 := by
  set L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : ∀ x, L x = x.1 - x.2 := fun x => rfl
  have hLn : ‖L‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    linarith [ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ, ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ]
  have he : (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) = (fun x : ℝ => x ^ 2) ∘ L := by
    funext x; simp [hL]
  have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  rw [he, ContinuousLinearMap.iteratedFDeriv_comp_right L hsq q (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate, iter_deriv_pow, hL, Real.norm_eq_abs]
  have hLi : ‖L‖ ^ i ≤ 2 ^ i := pow_le_pow_left₀ (norm_nonneg _) hLn i
  rcases i with _ | _ | _ | i
  · simp [sq_abs]
  · simp only [Nat.cast_ofNat, ite_true] at hLi ⊢
    rw [abs_mul, abs_pow]
    norm_num
    nlinarith [abs_nonneg (q.1 - q.2), norm_nonneg L]
  · simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num
    nlinarith [norm_nonneg L]
  · have h0 : ∏ k ∈ Finset.range (i + 3), ((2 : ℕ) - (k : ℝ)) = 0 :=
      Finset.prod_eq_zero (i := 2) (Finset.mem_range.2 (by omega)) (by norm_num)
    rw [h0]; simp

/-- `(∂₁+∂₂)^j [(u-v)² H] = (u-v)² (∂₁+∂₂)^j H`, as a bound. -/
theorem c03_aux_diag_bound (H : ℝ × ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (j : ℕ) (u v : ℝ) :
    |iteratedFDeriv ℝ j (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * H q) (u, v)
        (fun _ => ((1 : ℝ), (1 : ℝ)))| ≤ (u - v) ^ 2 * ‖iteratedFDeriv ℝ j H (u, v)‖ := by
  have hGc : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * H q) :=
    ((contDiff_fst.sub contDiff_snd).pow 2).mul hH
  rw [c03_aux_dir_deriv _ hGc]
  have hc : ContDiffAt ℝ j (fun t : ℝ => H ((u, v) + t • ((1 : ℝ), (1 : ℝ)))) 0 :=
    (hH.comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (u, v) + t • ((1 : ℝ), (1 : ℝ))))
      ).contDiffAt.of_le (by exact_mod_cast le_top)
  have hline : (fun t : ℝ => (((u, v) + t • ((1 : ℝ), (1 : ℝ))).1 -
      ((u, v) + t • ((1 : ℝ), (1 : ℝ))).2) ^ 2 * H ((u, v) + t • ((1 : ℝ), (1 : ℝ)))) =
      fun t => (u - v) ^ 2 * H ((u, v) + t • ((1 : ℝ), (1 : ℝ))) := by
    funext t
    congr 1
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk_add_mk]
    ring
  rw [hline, iteratedDeriv_const_mul _ hc, ← c03_aux_dir_deriv _ hH, abs_mul]
  have hop := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ j H (u, v))
    (fun _ => ((1 : ℝ), (1 : ℝ)))
  have h11 : ‖((1 : ℝ), (1 : ℝ))‖ = 1 := by simp
  simp only [h11, Finset.prod_const_one, mul_one] at hop
  rw [Real.norm_eq_abs] at hop
  rw [abs_pow, sq_abs]
  exact mul_le_mul_of_nonneg_left hop (sq_nonneg _)

/-- First derivative of `(u-v)² H`. -/
theorem c03_aux_prod_d1 (H : ℝ × ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (u v : ℝ) :
    ‖fderiv ℝ (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * H q) (u, v)‖ ≤
      (u - v) ^ 2 * ‖iteratedFDeriv ℝ 1 H (u, v)‖ + 4 * |u - v| * |H (u, v)| := by
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) :=
    (contDiff_fst.sub contDiff_snd).pow 2
  rw [← norm_iteratedFDeriv_one]
  refine (norm_iteratedFDeriv_mul_le (n := 1) hfc hH (u, v) (by simp)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, Nat.sub_self]
  have h0 : ‖iteratedFDeriv ℝ 0 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (u, v)‖ = (u - v) ^ 2 := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_pow, sq_abs]
  have h1 : ‖iteratedFDeriv ℝ 1 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (u, v)‖ ≤ 4 * |u - v| := by
    simpa using c03_aux_sqL_bound 1 (u, v)
  have h2 : ‖iteratedFDeriv ℝ 0 H (u, v)‖ = |H (u, v)| := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rw [h0, h2]
  gcongr

/-- Second derivative of `(u-v)² H`. -/
theorem c03_aux_prod_d2 (H : ℝ × ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (u v : ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * H q) (u, v)‖ ≤
      (u - v) ^ 2 * ‖iteratedFDeriv ℝ 2 H (u, v)‖ +
        8 * |u - v| * ‖iteratedFDeriv ℝ 1 H (u, v)‖ + 8 * |H (u, v)| := by
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) :=
    (contDiff_fst.sub contDiff_snd).pow 2
  refine (norm_iteratedFDeriv_mul_le (n := 2) hfc hH (u, v) (by simp)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right,
    Nat.choose_self, Nat.choose_one_right, Nat.cast_one, Nat.cast_ofNat, one_mul, Nat.sub_zero,
    Nat.sub_self, Nat.reduceSub]
  have h0 : ‖iteratedFDeriv ℝ 0 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (u, v)‖ = (u - v) ^ 2 := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_pow, sq_abs]
  have h1 : ‖iteratedFDeriv ℝ 1 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (u, v)‖ ≤ 4 * |u - v| := by
    simpa using c03_aux_sqL_bound 1 (u, v)
  have h2' : ‖iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (u, v)‖ ≤ 8 := by
    simpa using c03_aux_sqL_bound 2 (u, v)
  have h2 : ‖iteratedFDeriv ℝ 0 H (u, v)‖ = |H (u, v)| := by
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rw [h0, h2]
  have := norm_nonneg (iteratedFDeriv ℝ 1 H (u, v))
  have := abs_nonneg (H (u, v))
  nlinarith

/-- `n`-th derivative of `(u-v)² H`. -/
theorem c03_aux_prod_dn (H : ℝ × ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (u v : ℝ) (n : ℕ)
    (Fm B : ℝ) (hF : ∀ i, ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (u, v)‖ ≤ Fm)
    (hB : ∀ i ≤ n, ‖iteratedFDeriv ℝ i H (u, v)‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * H q) (u, v)‖ ≤ 2 ^ n * Fm * B := by
  have hfc : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) :=
    (contDiff_fst.sub contDiff_snd).pow 2
  have hF0 : 0 ≤ Fm := (norm_nonneg _).trans (hF 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  refine (norm_iteratedFDeriv_mul_le hfc hH (u, v) (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2) (u, v)‖ *
        ‖iteratedFDeriv ℝ (n - i) H (u, v)‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Fm * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hF i) (by positivity))
          (hB (n - i) (by omega)) (norm_nonneg _) (by positivity)
    _ = 2 ^ n * Fm * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast; ring

/-- Mixed derivative `(∂₁+∂₂)∇` of `(u-v)² H`. -/
theorem c03_aux_mixed (H : ℝ × ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (u v : ℝ) (w : ℝ × ℝ) :
    |iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => (q.1 - q.2) ^ 2 * H q) (u, v) ![((1 : ℝ), (1 : ℝ)), w]| ≤
      4 * |u - v| * ‖w‖ * ‖iteratedFDeriv ℝ 1 H (u, v)‖ +
        (u - v) ^ 2 * ‖w‖ * ‖iteratedFDeriv ℝ 2 H (u, v)‖ := by
  set e : ℝ × ℝ := ((1 : ℝ), (1 : ℝ)) with he
  set G : ℝ × ℝ → ℝ := fun q => (q.1 - q.2) ^ 2 * H q with hG
  have hGd : ContDiff ℝ (⊤ : ℕ∞) G := ((contDiff_fst.sub contDiff_snd).pow 2).mul hH
  have hG' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := (contDiff_infty_iff_fderiv.1 hGd).2
  have hH' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ H) := (contDiff_infty_iff_fderiv.1 hH).2
  have hHd : Differentiable ℝ H := hH.differentiable (by simp)
  have hH'd : Differentiable ℝ (fderiv ℝ H) := hH'.differentiable (by simp)
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  set h : ℝ × ℝ → ℝ := fun q => fderiv ℝ G q w with hh
  have hhd : ContDiff ℝ (⊤ : ℕ∞) h := hG'.clm_apply contDiff_const
  have hfd : fderiv ℝ (fderiv ℝ G) (u, v) e w = fderiv ℝ h (u, v) e := by
    rw [hh, fderiv_clm_apply (hG'.differentiable (by simp) _) (differentiableAt_const w)]
    simp
  -- formula for `h`
  have hform : ∀ q : ℝ × ℝ, h q = 2 * (q.1 - q.2) * (w.1 - w.2) * H q +
      (q.1 - q.2) ^ 2 * fderiv ℝ H q w := by
    intro q
    have hL : HasFDerivAt (fun q : ℝ × ℝ => q.1 - q.2)
        (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
      (hasFDerivAt_fst).sub hasFDerivAt_snd
    have hGeq : G = fun q : ℝ × ℝ => (q.1 - q.2) * (q.1 - q.2) * H q := by
      funext x; simp only [hG]; ring
    have hD : HasFDerivAt G (((q.1 - q.2) * (q.1 - q.2)) • fderiv ℝ H q + H q •
        ((q.1 - q.2) • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) +
          (q.1 - q.2) • (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))) q := by
      rw [hGeq]; exact (hL.mul hL).mul (hHd q).hasFDerivAt
    simp only [hh, hD.fderiv]
    simp
    ring
  rw [hfd]
  -- directional derivative along `e`
  have hdir := c03_aux_dir_deriv h hhd (u, v) e 1
  rw [iteratedFDeriv_one_apply, iteratedDeriv_one] at hdir
  rw [hdir]
  have hline : (fun t : ℝ => h ((u, v) + t • e)) = fun t =>
      2 * (u - v) * (w.1 - w.2) * H ((u, v) + t • e) +
        (u - v) ^ 2 * fderiv ℝ H ((u, v) + t • e) w := by
    funext t; rw [hform]
    simp only [he, Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk_add_mk]
    ring_nf
  have hℓ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (u, v) + t • e) e t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const e).const_add (u, v)
  have h1 : HasDerivAt (fun t : ℝ => H ((u, v) + t • e)) (fderiv ℝ H (u, v) e) 0 := by
    have := (hHd ((u, v) + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hℓ 0)
    simp only [zero_smul, add_zero] at this
    exact this
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ H ((u, v) + t • e) w)
      (fderiv ℝ (fderiv ℝ H) (u, v) e w) 0 := by
    have := (hH'd ((u, v) + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hℓ 0)
    have := this.clm_apply (hasDerivAt_const (0 : ℝ) w)
    simpa using this
  have hsum : HasDerivAt (fun t : ℝ => 2 * (u - v) * (w.1 - w.2) * H ((u, v) + t • e) +
      (u - v) ^ 2 * fderiv ℝ H ((u, v) + t • e) w)
      (2 * (u - v) * (w.1 - w.2) * fderiv ℝ H (u, v) e +
        (u - v) ^ 2 * fderiv ℝ (fderiv ℝ H) (u, v) e w) 0 :=
    (h1.const_mul _).add (h2.const_mul _)
  rw [hline, hsum.deriv]
  have hn1 : |fderiv ℝ H (u, v) e| ≤ ‖iteratedFDeriv ℝ 1 H (u, v)‖ := by
    rw [norm_iteratedFDeriv_one, ← Real.norm_eq_abs]
    refine ((fderiv ℝ H (u, v)).le_opNorm e).trans ?_
    simp [he]
  have hn2 : |fderiv ℝ (fderiv ℝ H) (u, v) e w| ≤ ‖iteratedFDeriv ℝ 2 H (u, v)‖ * ‖w‖ := by
    have := (iteratedFDeriv ℝ 2 H (u, v)).le_opNorm ![e, w]
    rw [iteratedFDeriv_two_apply] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.prod_univ_two,
      Real.norm_eq_abs] at this
    simpa [he] using this
  have hw : |w.1 - w.2| ≤ 2 * ‖w‖ := by
    have h1 : |w.1| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le w
    have h2 : |w.2| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le w
    linarith [abs_sub w.1 w.2]
  have hd0 := abs_nonneg (u - v)
  calc |2 * (u - v) * (w.1 - w.2) * fderiv ℝ H (u, v) e +
        (u - v) ^ 2 * fderiv ℝ (fderiv ℝ H) (u, v) e w|
      ≤ 2 * |u - v| * |w.1 - w.2| * |fderiv ℝ H (u, v) e| +
          (u - v) ^ 2 * |fderiv ℝ (fderiv ℝ H) (u, v) e w| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, sq_abs]; norm_num
    _ ≤ 2 * |u - v| * (2 * ‖w‖) * ‖iteratedFDeriv ℝ 1 H (u, v)‖ +
          (u - v) ^ 2 * (‖iteratedFDeriv ℝ 2 H (u, v)‖ * ‖w‖) := by
        gcongr
    _ = _ := by ring

/-- The near-diagonal consequence of rmk:analysis_vanishing_diagonal. -/
theorem c03_aux_vd_consequence (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 1 ≤ R) :
    ∀ K L : ℝ, 0 ≤ K → 0 ≤ L → ∃ C, 0 < C ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 →
      ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → (∀ x, |deriv f x| ≤ K) →
      (∀ x ∈ Icc (-R - 2) (R + 2), ∀ x' ∈ Icc (-R - 2) (R + 2),
        |deriv f x - deriv f x'| ≤ L * |x - x'|) →
      ∀ y z, |y| ≤ R → 0 < |y - z| → |y - z| ≤ 2 →
        |c03_Gamma_eps p ε (deriv f y) (c01_secant f y z)| / |y - z| ^ (p + 1) ≤
          C * ε * |y - z| ^ (2 - (p + 1)) := by
  intro K L hK hL
  set c0 := |calpha p| * (1 + K ^ 2) ^ ((p + 1) / 2) * ((1 + p) * (p + 1)) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  refine ⟨c0 * (2 * K) * L ^ 2 + 1, by positivity, fun ε hε hε1 f hf hK' hLip y z hy hyz hyz2 => ?_⟩
  set t := y - z with ht
  set u := deriv f y
  set S := c01_secant f y z
  have hu : |u| ≤ K := hK' y
  have hSK : |S| ≤ K := c03_aux_secant_le f hf.1 hK' y z
  have hSu : |S - u| ≤ L * |t| := by
    have := c03_aux_secant_sub_deriv f hf.1 y t L (fun x hx => by
      have hxR : x ∈ Icc (-R - 2) (R + 2) := by
        have := abs_le.1 hy; have := abs_le.1 (hx.trans hyz2)
        constructor <;> linarith
      have hyR : y ∈ Icc (-R - 2) (R + 2) := by
        have := abs_le.1 hy; constructor <;> linarith
      exact (hLip x hxR y hyR).trans (mul_le_mul_of_nonneg_left hx hL))
    rwa [ht, sub_sub_cancel] at this
  have hG := (c03_Gamma_quadratic_factor p ε hp hp1 hε u S).1
  have hGt := c03_aux_Gt_bound p ε hp hε hε1 K u S hu
  have htp : 0 < |t| ^ (p + 1) := Real.rpow_pos_of_pos hyz _
  rw [hG, abs_mul, div_le_iff₀ htp]
  have hsq : |(u - S) ^ 2| ≤ L ^ 2 * |t| ^ 2 := by
    rw [abs_pow, abs_sub_comm, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hSu 2
  have hpow : |t| ^ 2 = |t| ^ (2 - (p + 1)) * |t| ^ (p + 1) := by
    rw [← Real.rpow_add hyz]; simp
  calc |(u - S) ^ 2| * |c03_Gamma_eps_tilde p ε u S|
      ≤ (L ^ 2 * |t| ^ 2) * (c0 * ε * (|u| + |S|)) :=
        mul_le_mul hsq hGt (abs_nonneg _) (by positivity)
    _ ≤ (L ^ 2 * |t| ^ 2) * (c0 * ε * (2 * K)) := by
        gcongr; linarith
    _ = (c0 * (2 * K) * L ^ 2) * ε * |t| ^ (2 - (p + 1)) * |t| ^ (p + 1) := by
        rw [hpow]; ring
    _ ≤ (c0 * (2 * K) * L ^ 2 + 1) * ε * |t| ^ (2 - (p + 1)) * |t| ^ (p + 1) := by
        gcongr; linarith

/-- Blueprint: rmk:analysis_vanishing_diagonal.  Kernel bounds for `Γ̃_ε`, `Γ_ε` and their
derivatives (`∇^j` = `iteratedFDeriv`, `(∂₁+∂₂)^j` = `iteratedFDeriv` applied to `(1,1)`),
uniform in `ε ∈ [0,1]`, `|u|,|v| ≤ R`; and the near-diagonal consequence for the integrand
of `ℐ_ε`. -/
theorem analysis_vanishing_diagonal (p R : ℝ) (hp : 0 < p) (hp1 : p < 1) (hR : 1 ≤ R) :
    (∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 → ∀ u v : ℝ, |u| ≤ R → |v| ≤ R →
      -- (1)
      |c03_Gamma_eps_tilde p ε u v| ≤ C 0 * ε * (|u| + |v|) ∧
      (∀ j, ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => c03_Gamma_eps_tilde p ε q.1 q.2) (u, v)‖ ≤
        C j * ε) ∧
      -- (2)
      ‖fderiv ℝ (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) (u, v)‖ ≤
        C 1 * ε * |u - v| * (|u| + |v|) ∧
      ‖iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) (u, v)‖ ≤
        C 2 * ε * (|u| + |v|) ∧
      (∀ j, ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) (u, v)‖ ≤
        C j * ε) ∧
      -- (3)
      (∀ j, |iteratedFDeriv ℝ j (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) (u, v)
        (fun _ => ((1 : ℝ), (1 : ℝ)))| ≤ C j * ε * |u - v| ^ 2) ∧
      (∀ w : ℝ × ℝ, |iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) (u, v)
        ![((1 : ℝ), (1 : ℝ)), w]| ≤ C 1 * ε * |u - v| * ‖w‖)) ∧
    -- consequence
    (∀ K L : ℝ, 0 ≤ K → 0 ≤ L → ∃ C, 0 < C ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 →
      ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → (∀ x, |deriv f x| ≤ K) →
      (∀ x ∈ Icc (-R - 2) (R + 2), ∀ x' ∈ Icc (-R - 2) (R + 2),
        |deriv f x - deriv f x'| ≤ L * |x - x'|) →
      ∀ y z, |y| ≤ R → 0 < |y - z| → |y - z| ≤ 2 →
        |c03_Gamma_eps p ε (deriv f y) (c01_secant f y z)| / |y - z| ^ (p + 1) ≤
          C * ε * |y - z| ^ (2 - (p + 1))) := by
  have hR0 : 0 ≤ R := by linarith
  constructor
  · obtain ⟨Ct, hCt0, hCt⟩ := c03_aux_Gt_deriv_bound p R hp hp1 hR0
    set c0 := |calpha p| * (1 + R ^ 2) ^ ((p + 1) / 2) * ((1 + p) * (p + 1)) with hc0def
    have hc0 : 0 ≤ c0 := by positivity
    set Fm := 4 * R ^ 2 + 8 * R + 8 with hFm
    set S : ℕ → ℝ := fun n => ∑ m ∈ Finset.range (n + 1), Ct m with hS
    have hS0 : ∀ n, 0 ≤ S n := fun n => Finset.sum_nonneg fun m _ => hCt0 m
    have hSle : ∀ n m, m ≤ n → Ct m ≤ S n := fun n m hm =>
      Finset.single_le_sum (f := Ct) (fun i _ => hCt0 i) (Finset.mem_range.2 (by omega))
    set E := (Ct 1 + 4 * c0) + (2 * R * Ct 2 + 8 * Ct 1 + 8 * c0) + (4 * Ct 1 + 2 * R * Ct 2)
      with hE
    have hE0 : 0 ≤ E := by have := hCt0 1; have := hCt0 2; positivity
    refine ⟨fun j => 2 ^ j * Fm * S j + E + Ct j + c0 + 1, fun j => by
      have := hS0 j; have := hCt0 j; positivity, fun ε hε hε1 u v hu hv => ?_⟩
    have hFm0 : 0 ≤ Fm := by positivity
    have hCge : ∀ j, ∀ a, a ≤ 2 ^ j * Fm * S j + E + Ct j + c0 + 1 → ∀ X, 0 ≤ X →
        a * ε * X ≤ (2 ^ j * Fm * S j + E + Ct j + c0 + 1) * ε * X := fun j a ha X hX =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hε) hX
    have hbig : ∀ j, 0 ≤ 2 ^ j * Fm * S j := fun j => by have := hS0 j; positivity
    set Gt : ℝ × ℝ → ℝ := fun q => c03_Gamma_eps_tilde p ε q.1 q.2 with hGt
    set fq : ℝ × ℝ → ℝ := fun q => (q.1 - q.2) ^ 2 with hfq
    have hGtc : ContDiff ℝ (⊤ : ℕ∞) Gt := (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.2
    have hfc : ContDiff ℝ (⊤ : ℕ∞) fq := (contDiff_fst.sub contDiff_snd).pow 2
    have hGeq : (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) = fun q => fq q * Gt q := by
      funext q; exact (c03_Gamma_quadratic_factor p ε hp hp1 hε q.1 q.2).1
    set d := |u - v| with hd
    set s := |u| + |v| with hs
    have hds : d ≤ s := abs_sub _ _
    have hs2 : s ≤ 2 * R := by linarith
    have hd0 : 0 ≤ d := abs_nonneg _
    have hs0 : 0 ≤ s := by positivity
    have hdd : d ^ 2 ≤ d * s := by rw [sq]; exact mul_le_mul_of_nonneg_left hds hd0
    have hdR : d ^ 2 ≤ 2 * R * s := by
      rw [sq]
      calc d * d ≤ s * (2 * R) := mul_le_mul hds (hds.trans hs2) hd0 hs0
        _ = 2 * R * s := by ring
    have hT : ∀ j, ‖iteratedFDeriv ℝ j Gt (u, v)‖ ≤ Ct j * ε := fun j => hCt j ε hε hε1 u v hu hv
    have hT0 : |Gt (u, v)| ≤ c0 * ε * s := c03_aux_Gt_bound p ε hp hε hε1 R u v hu
    have hF0 : ‖iteratedFDeriv ℝ 0 fq (u, v)‖ = d ^ 2 := by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, hd, abs_pow, sq_abs]
    have hF1 : ‖iteratedFDeriv ℝ 1 fq (u, v)‖ ≤ 4 * d := by
      simpa using c03_aux_sqL_bound 1 (u, v)
    have hF2 : ‖iteratedFDeriv ℝ 2 fq (u, v)‖ ≤ 8 := by
      simpa using c03_aux_sqL_bound 2 (u, v)
    have hFall : ∀ i, ‖iteratedFDeriv ℝ i fq (u, v)‖ ≤ Fm := by
      intro i
      have h := c03_aux_sqL_bound i (u, v)
      have hd2 : d ≤ 2 * R := hds.trans hs2
      have hR2 := sq_nonneg R
      split_ifs at h with h0 h1 h2
      · subst h0; rw [hF0]
        calc d ^ 2 ≤ (2 * R) ^ 2 := pow_le_pow_left₀ hd0 hd2 2
          _ ≤ Fm := by rw [hFm]; linarith
      · subst h1; linarith [hF1]
      · subst h2; linarith [hF2]
      · linarith
    have hGt0 : ‖iteratedFDeriv ℝ 0 Gt (u, v)‖ = |Gt (u, v)| := by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    have hT1 := hT 1; have hT2 := hT 2
    have hC1 := hCt0 1; have hC2 := hCt0 2
    -- (3), second part, prepared below
    refine ⟨?_, fun j => ?_, ?_, ?_, fun j => ?_, fun j => ?_, fun w => ?_⟩
    · refine hT0.trans (hCge 0 c0 (by linarith [hbig 0, hCt0 0]) s (by positivity))
    · refine (hT j).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hbig j]) hε
    · rw [hGeq]
      refine (c03_aux_prod_d1 Gt hGtc u v).trans ?_
      rw [← sq_abs (u - v)]
      have h1 : d ^ 2 * ‖iteratedFDeriv ℝ 1 Gt (u, v)‖ ≤ d * s * (Ct 1 * ε) :=
        mul_le_mul hdd hT1 (norm_nonneg _) (by positivity)
      have h2 : 4 * d * |Gt (u, v)| ≤ 4 * d * (c0 * ε * s) :=
        mul_le_mul_of_nonneg_left hT0 (by positivity)
      calc _ ≤ d * s * (Ct 1 * ε) + 4 * d * (c0 * ε * s) := add_le_add h1 h2
        _ = (Ct 1 + 4 * c0) * ε * (d * s) := by ring
        _ ≤ _ := by
          rw [mul_assoc _ d s]
          refine hCge 1 _ ?_ _ (by positivity)
          linarith [hbig 1, mul_nonneg hR0 hC2]
    · rw [hGeq]
      refine (c03_aux_prod_d2 Gt hGtc u v).trans ?_
      rw [← sq_abs (u - v)]
      have h1 : d ^ 2 * ‖iteratedFDeriv ℝ 2 Gt (u, v)‖ ≤ (2 * R * s) * (Ct 2 * ε) :=
        mul_le_mul hdR hT2 (norm_nonneg _) (by positivity)
      have h2 : 8 * d * ‖iteratedFDeriv ℝ 1 Gt (u, v)‖ ≤ (8 * s) * (Ct 1 * ε) :=
        mul_le_mul (by linarith) hT1 (norm_nonneg _) (by positivity)
      have h3 : 8 * |Gt (u, v)| ≤ 8 * (c0 * ε * s) := by linarith
      calc _ ≤ (2 * R * s) * (Ct 2 * ε) + (8 * s) * (Ct 1 * ε) + 8 * (c0 * ε * s) := by
            linarith
        _ = (2 * R * Ct 2 + 8 * Ct 1 + 8 * c0) * ε * s := by ring
        _ ≤ _ := by
          refine hCge 2 _ ?_ _ (by positivity)
          linarith [hbig 2, mul_nonneg hR0 hC2]
    · rw [hGeq]
      refine (c03_aux_prod_dn Gt hGtc u v j Fm (S j * ε) hFall (fun i hi =>
        (hT i).trans (mul_le_mul_of_nonneg_right (hSle j i hi) hε))).trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith [hCt0 j]) hε
    · rw [hGeq]
      refine (c03_aux_diag_bound Gt hGtc j u v).trans ?_
      rw [← sq_abs, mul_comm]
      calc ‖iteratedFDeriv ℝ j Gt (u, v)‖ * d ^ 2
          ≤ (Ct j * ε) * d ^ 2 := mul_le_mul_of_nonneg_right (hT j) (by positivity)
        _ ≤ _ := hCge j _ (by linarith [hbig j]) _ (by positivity)
    · rw [hGeq]
      refine (c03_aux_mixed Gt hGtc u v w).trans ?_
      rw [← sq_abs (u - v)]
      have hw := norm_nonneg w
      have hd2 : d ^ 2 ≤ 2 * R * d := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (hds.trans hs2) hd0
      have h1 : 4 * d * ‖w‖ * ‖iteratedFDeriv ℝ 1 Gt (u, v)‖ ≤ 4 * d * ‖w‖ * (Ct 1 * ε) :=
        mul_le_mul_of_nonneg_left hT1 (by positivity)
      have h2 : d ^ 2 * ‖w‖ * ‖iteratedFDeriv ℝ 2 Gt (u, v)‖ ≤ (2 * R * d) * ‖w‖ * (Ct 2 * ε) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hd2 hw) hT2 (norm_nonneg _) (by positivity)
      calc _ ≤ 4 * d * ‖w‖ * (Ct 1 * ε) + (2 * R * d) * ‖w‖ * (Ct 2 * ε) := add_le_add h1 h2
        _ = (4 * Ct 1 + 2 * R * Ct 2) * ε * (d * ‖w‖) := by ring
        _ ≤ _ := by
          rw [mul_assoc _ d]
          refine hCge 1 _ ?_ _ (by positivity)
          linarith [hbig 1, mul_nonneg hR0 hC2]
  · exact c03_aux_vd_consequence p R hp hp1 hR

/-- Blueprint: lem:c03_I_well_defined.  Absolute convergence (locally uniform in `y`, expressed
by an integrable majorant in `t = y - z` for `|y| ≤ R`) and continuity of `|D|^p f'`, `𝒥̃_ε(f)`,
`ℐ_ε(f)`, `ℰ_ε(f)`; and `ℰ_ε(f) = 0` in `𝒟'` iff pointwise. -/
theorem c03_I_well_defined (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) :
    -- (1)
    (∀ y, Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1))) ∧
    Continuous (fracDdy p f) ∧
    -- (2)
    (∀ y, Integrable (fun z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
        (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y)))) ∧
    (∀ y, Integrable (fun z => |deriv f y - deriv f z| / |y - z| ^ (p + 1) *
        |A_eps p ε (c01_secant f y z) / A_eps p ε (deriv f y) - 1|)) ∧
    (∀ y, Integrable (fun z =>
        |c03_Gamma_eps p ε (deriv f y) (c01_secant f y z)| / |y - z| ^ (p + 1))) ∧
    (∀ R : ℝ, ∃ g : ℝ → ℝ, Integrable g ∧ ∀ y ∈ Icc (-R) R, ∀ t : ℝ,
      |(deriv f y - deriv f (y - t)) / |t| ^ (p + 1) *
          (A_eps p ε (c01_secant f y (y - t)) - A_eps p ε (deriv f y))| ≤ g t ∧
      |deriv f y - deriv f (y - t)| / |t| ^ (p + 1) *
          |A_eps p ε (c01_secant f y (y - t)) / A_eps p ε (deriv f y) - 1| ≤ g t ∧
      |c03_Gamma_eps p ε (deriv f y) (c01_secant f y (y - t))| / |t| ^ (p + 1) ≤ g t) ∧
    Continuous (J_eps p ε f) ∧ Continuous (c03_I_eps p ε f) ∧
    -- (3)
    Continuous (residual p ε f) ∧
    (c03_distrib_zero (residual p ε f) ↔ ∀ y, residual p ε f y = 0) := by
  have hf0 := hf
  obtain ⟨hC1, -, -⟩ := hf0
  have hfc : Continuous f := hC1.continuous
  have hdc : Continuous (deriv f) := hC1.continuous_deriv le_rfl
  have hA : Continuous (A_eps p ε) := (c03_aux_A_contDiff p hε (n := 0)).continuous
  have hΓ2 : Continuous (fun q : ℝ × ℝ => c03_Gamma_eps p ε q.1 q.2) :=
    (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.1.continuous
  have hSm : ∀ y, Measurable (fun z => c01_secant f y z) := c03_aux_secant_measurable f hfc
  have hkm : ∀ y, Measurable (fun z : ℝ => |y - z| ^ (p + 1)) := fun y =>
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ => Or.inr (by linarith))).measurable
  have hSc : ∀ t : ℝ, t ≠ 0 → Continuous (fun y => c01_secant f y (y - t)) := fun t ht => by
    simp_rw [c03_aux_secant_sub f _ t ht]
    exact (hfc.sub (hfc.comp (continuous_id.sub continuous_const))).div_const t
  have hdct : ∀ t : ℝ, Continuous (fun y => deriv f y - deriv f (y - t)) := fun t =>
    hdc.sub (hdc.comp (continuous_id.sub continuous_const))
  -- domination data
  have hD : ∀ R : ℝ, ∃ Λ M : ℝ, 0 ≤ Λ ∧ 0 ≤ M ∧ ∀ y ∈ Icc (-R) R, ∀ t : ℝ,
      |(deriv f y - deriv f (y - t)) / |t| ^ (p + 1)| ≤ c03_aux_psi p Λ M t ∧
      |(deriv f y - deriv f (y - t)) / |t| ^ (p + 1) *
          (A_eps p ε (c01_secant f y (y - t)) - A_eps p ε (deriv f y))| ≤ c03_aux_psi p Λ M t ∧
      |deriv f y - deriv f (y - t)| / |t| ^ (p + 1) *
          |A_eps p ε (c01_secant f y (y - t)) / A_eps p ε (deriv f y) - 1| ≤
        c03_aux_psi p Λ M t ∧
      |c03_Gamma_eps p ε (deriv f y) (c01_secant f y (y - t))| / |t| ^ (p + 1) ≤
        c03_aux_psi p Λ M t := by
    intro R
    obtain ⟨Λ, M, hΛ, hM, h⟩ := c03_aux_profile_bounds p ε hp hε f hf R
    refine ⟨Λ, M, hΛ, hM, fun y hy t => ?_⟩
    have hn := fun ht : |t| ≤ 1 => h y hy t _ (Or.inl ⟨rfl, ht⟩)
    have hfar := h y hy t _ (Or.inr rfl)
    have hk : |(|t| ^ (p + 1))| = |t| ^ (p + 1) :=
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [abs_div, hk]
      exact c03_aux_psi_bound p hp hΛ hM t _ (fun ht => (hn ht).1) hfar.1
    · rw [c03_aux_rearr]
      exact c03_aux_psi_bound p hp hΛ hM t _ (fun ht => (hn ht).2.1) hfar.2.1
    · rw [div_mul_eq_mul_div, ← abs_mul]
      exact c03_aux_psi_bound p hp hΛ hM t _ (fun ht => (hn ht).2.2.1) hfar.2.2.1
    · exact c03_aux_psi_bound p hp hΛ hM t _ (fun ht => (hn ht).2.2.2.1) hfar.2.2.2.1
  -- the kernels
  set G1 : ℝ → ℝ → ℝ := fun y z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) with hG1
  set G2 : ℝ → ℝ → ℝ := fun y z => (deriv f y - deriv f z) / |y - z| ^ (p + 1) *
        (A_eps p ε (c01_secant f y z) - A_eps p ε (deriv f y)) with hG2
  set G4 : ℝ → ℝ → ℝ := fun y z =>
    c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) / |y - z| ^ (p + 1) with hG4
  have hm1 : ∀ y, Measurable (G1 y) := fun y =>
    (measurable_const.sub hdc.measurable).div (hkm y)
  have hm2 : ∀ y, Measurable (G2 y) := fun y =>
    (hm1 y).mul ((hA.measurable.comp (hSm y)).sub measurable_const)
  have hm4 : ∀ y, Measurable (G4 y) := fun y =>
    (hΓ2.measurable.comp (measurable_const.prodMk (hSm y))).div (hkm y)
  obtain ⟨hi1, hc1⟩ := c03_aux_dom p hp hp1 G1 hm1
    (fun R => by
      obtain ⟨Λ, M, hΛ, hM, h⟩ := hD R
      exact ⟨Λ, M, hΛ, hM, fun y hy t => by simp only [hG1, sub_sub_cancel]; exact (h y hy t).1⟩)
    (fun t ht => by
      simp only [hG1, sub_sub_cancel]; exact (hdct t).div_const _)
  obtain ⟨hi2, hc2⟩ := c03_aux_dom p hp hp1 G2 hm2
    (fun R => by
      obtain ⟨Λ, M, hΛ, hM, h⟩ := hD R
      exact ⟨Λ, M, hΛ, hM, fun y hy t => by simp only [hG2, sub_sub_cancel]; exact (h y hy t).2.1⟩)
    (fun t ht => by
      simp only [hG2, sub_sub_cancel]
      exact ((hdct t).div_const _).mul ((hA.comp (hSc t ht)).sub (hA.comp hdc)))
  obtain ⟨hi4, hc4⟩ := c03_aux_dom p hp hp1 G4 hm4
    (fun R => by
      obtain ⟨Λ, M, hΛ, hM, h⟩ := hD R
      exact ⟨Λ, M, hΛ, hM, fun y hy t => by
        simp only [hG4, sub_sub_cancel]
        rw [abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
        exact (h y hy t).2.2.2⟩)
    (fun t ht => by
      simp only [hG4, sub_sub_cancel]
      exact (hΓ2.comp (hdc.prodMk (hSc t ht))).div_const _)
  have hJc : Continuous (J_eps p ε f) := by
    unfold J_eps; exact continuous_const.mul hc2
  have hFc : Continuous (fracDdy p f) := by
    unfold fracDdy fracD; exact continuous_const.mul hc1
  have hIc : Continuous (c03_I_eps p ε f) := by
    unfold c03_I_eps; exact hc4
  have hRc : Continuous (residual p ε f) := by
    unfold residual
    exact hFc.add (((hfc.sub (continuous_id.mul hdc)).add hJc).div (hA.comp hdc)
      (fun y => (c03_aux_A_pos p hε _).ne'))
  refine ⟨hi1, hFc, hi2, fun y => ?_, fun y => ?_, fun R => ?_, hJc, hIc, hRc,
    c03_aux_distrib_zero_iff _ hRc⟩
  · obtain ⟨Λ, M, -, -, h⟩ := hD |y|
    refine c03_aux_dom_int p hp hp1 _ y ?_ Λ M (fun t => ?_)
    · exact ((measurable_const.sub hdc.measurable).abs.div (hkm y)).mul
        (((hA.measurable.comp (hSm y)).div measurable_const).sub measurable_const).abs
    · simp only [sub_sub_cancel]
      rw [abs_of_nonneg (by positivity)]
      exact (h y (abs_le.1 le_rfl) t).2.2.1
  · have := (hi4 y).abs
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [hG4, abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (y - z)) _)]
  · obtain ⟨Λ, M, -, -, h⟩ := hD R
    exact ⟨c03_aux_psi p Λ M, c03_aux_psi_integrable p Λ M hp hp1,
      fun y hy t => ⟨(h y hy t).2.1, (h y hy t).2.2.1, (h y hy t).2.2.2⟩⟩

/-- `∂_v P_ε(u,v) = 1 - A_ε(v)/A_ε(u)`. -/
theorem c03_aux_P_hasDerivAt_snd (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (u v : ℝ) :
    HasDerivAt (fun v => c03_P_eps p ε u v) (1 - A_eps p ε v / A_eps p ε u) v := by
  have hP : (fun v => c03_P_eps p ε u v) = fun v => (v - u) - ((∫ s in (0 : ℝ)..v, A_eps p ε s) -
      (∫ s in (0 : ℝ)..u, A_eps p ε s)) / A_eps p ε u := funext fun v => c03_aux_P_eq p hε u v
  rw [hP]
  have := (((hasDerivAt_id v).sub_const u).sub
    (((c03_aux_A_prim_hasDerivAt p hε v).sub_const (∫ s in (0 : ℝ)..u, A_eps p ε s)).div_const
      (A_eps p ε u)))
  exact this

/-- Derivative of `(y-z)|y-z|^{-α}` in `z` (for `z ≠ y`). -/
theorem c03_aux_kernel_hasDerivAt (p y z : ℝ) (hz : z ≠ y) :
    HasDerivAt (fun z => (y - z) / |y - z| ^ (p + 1)) (p / |y - z| ^ (p + 1)) z := by
  rcases lt_or_gt_of_ne hz with h | h
  · -- z < y : `|y - z'| = y - z'` near `z`
    have hev : (fun z => (y - z) / |y - z| ^ (p + 1)) =ᶠ[𝓝 z]
        fun z => (y - z) / (y - z) ^ (p + 1) := by
      filter_upwards [gt_mem_nhds h] with z' hz'
      rw [abs_of_pos (by linarith)]
    have hg : HasDerivAt (fun z => y - z) (-1) z := by simpa using (hasDerivAt_id z).const_sub y
    have hpos : 0 < y - z := by linarith
    have hgp := hg.rpow_const (p := p + 1) (Or.inl hpos.ne')
    have hq := hg.div hgp (Real.rpow_pos_of_pos hpos _).ne'
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_pos hpos, add_sub_cancel_right]
    have h1 : (y - z) ^ (p + 1) = (y - z) ^ p * (y - z) := Real.rpow_add_one hpos.ne' p
    have h2 : 0 < (y - z) ^ p := Real.rpow_pos_of_pos hpos _
    rw [h1]; field_simp; ring
  · -- z > y : `|y - z'| = z' - y` near `z`
    have hev : (fun z => (y - z) / |y - z| ^ (p + 1)) =ᶠ[𝓝 z]
        fun z => -((z - y) / (z - y) ^ (p + 1)) := by
      filter_upwards [lt_mem_nhds h] with z' hz'
      rw [abs_of_neg (by linarith : y - z' < 0), neg_sub, ← neg_div, neg_sub]
    have hg : HasDerivAt (fun z => z - y) 1 z := by simpa using (hasDerivAt_id z).sub_const y
    have hpos : 0 < z - y := by linarith
    have hgp := hg.rpow_const (p := p + 1) (Or.inl hpos.ne')
    have hq := (hg.div hgp (Real.rpow_pos_of_pos hpos _).ne').neg
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [abs_of_neg (by linarith), neg_sub, add_sub_cancel_right]
    have h1 : (z - y) ^ (p + 1) = (z - y) ^ p * (z - y) := Real.rpow_add_one hpos.ne' p
    have h2 : 0 < (z - y) ^ p := Real.rpow_pos_of_pos hpos _
    rw [h1]; field_simp; ring

/-- Blueprint: lem:c03_secant_ibp.  For `f ∈ C¹`, `u = f'(y)`, `z ≠ y`:
`∂_z S_f(y,z) = (S_f(y,z) - f'(z))/(y-z)`, the integration-by-parts identity for
`∂_z P_ε(u, S_f(y,z))`, and `∂_z((y-z)|y-z|^{-α}) = p|y-z|^{-α}`. -/
theorem c03_secant_ibp (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (y z : ℝ) (hz : z ≠ y) :
    HasDerivAt (fun z => c03_secant f y z) ((c03_secant f y z - deriv f z) / (y - z)) z ∧
    DifferentiableAt ℝ (fun z => c03_P_eps p ε (deriv f y) (c03_secant f y z)) z ∧
    (y - z) * deriv (fun z => c03_P_eps p ε (deriv f y) (c03_secant f y z)) z =
      (c03_secant f y z - deriv f y) *
          (1 - A_eps p ε (c03_secant f y z) / A_eps p ε (deriv f y)) +
        (deriv f y - deriv f z) *
          (1 - A_eps p ε (c03_secant f y z) / A_eps p ε (deriv f y)) ∧
    HasDerivAt (fun z => (y - z) / |y - z| ^ (p + 1)) (p / |y - z| ^ (p + 1)) z := by
  have hyz : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have hS : HasDerivAt (fun z => c03_secant f y z) ((c03_secant f y z - deriv f z) / (y - z)) z := by
    have hev : (fun z => c03_secant f y z) =ᶠ[𝓝 z] fun z => (f y - f z) / (y - z) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
      simp [c03_secant, c01_secant, Ne.symm hz']
    have hfz : HasDerivAt f (deriv f z) z := (hf.differentiable one_ne_zero z).hasDerivAt
    have hq := (hfz.const_sub (f y)).div ((hasDerivAt_id z).const_sub y) hyz
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [show c03_secant f y z = (f y - f z) / (y - z) by simp [c03_secant, c01_secant, Ne.symm hz]]
    simp only [id]
    field_simp
    ring
  have hPS := (c03_aux_P_hasDerivAt_snd p hε (deriv f y) (c03_secant f y z)).comp z hS
  refine ⟨hS, hPS.differentiableAt, ?_, c03_aux_kernel_hasDerivAt p y z hz⟩
  rw [show (fun z => c03_P_eps p ε (deriv f y) (c03_secant f y z)) =
    (fun v => c03_P_eps p ε (deriv f y) v) ∘ (fun z => c03_secant f y z) from rfl, hPS.deriv]
  field_simp
  ring

/-- `a / a^{p+1} = a^{-p}` for `a ≥ 0`, `p + 1 ≠ 0`. -/
theorem c03_aux_div_rpow (p : ℝ) (hp : 0 < p) {a : ℝ} (ha : 0 ≤ a) : a / a ^ (p + 1) = a ^ (-p) := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith), div_zero]
  · rw [Real.rpow_add ha, Real.rpow_one, Real.rpow_neg ha.le]; field_simp

/-- Blueprint: prop:analysis_semilinear_kernel.  `𝒥̃_ε(f)/A_ε(f') = ℐ_ε(f)`, hence
`ℰ_ε(f) = |D|^p f' + B_ε(f')(f - y f') + ℐ_ε(f)`. -/
theorem analysis_semilinear_kernel (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε)
    (f : ℝ → ℝ) (hf : f ∈ c01_admissible_class) :
    (∀ y, J_eps p ε f y / A_eps p ε (deriv f y) = c03_I_eps p ε f y) ∧
    (∀ y, residual p ε f y =
      fracDdy p f y + A_eps_B p ε (deriv f y) * (f y - y * deriv f y) + c03_I_eps p ε f y) := by
  have hf0 := hf
  obtain ⟨hC1, -, -⟩ := hf0
  have hfc : Continuous f := hC1.continuous
  have hdc : Continuous (deriv f) := hC1.continuous_deriv le_rfl
  have hA : Continuous (A_eps p ε) := (c03_aux_A_contDiff p hε (n := 0)).continuous
  have hP2 : Continuous (fun q : ℝ × ℝ => c03_P_eps p ε q.1 q.2) :=
    (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.1.continuous
  have hSm : ∀ y, Measurable (fun z => c01_secant f y z) := c03_aux_secant_measurable f hfc
  have hkm : ∀ y, Measurable (fun z : ℝ => |y - z| ^ (p + 1)) := fun y =>
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ => Or.inr (by linarith))).measurable
  have key : ∀ y, J_eps p ε f y / A_eps p ε (deriv f y) = c03_I_eps p ε f y := by
    intro y
    set u := deriv f y with hu
    have hAu : A_eps p ε u ≠ 0 := (c03_aux_A_pos p hε u).ne'
    obtain ⟨Λ, M, hΛ, hM, hb⟩ := c03_aux_profile_bounds p ε hp hε f hf |y|
    have hy : y ∈ Icc (-|y|) |y| := abs_le.1 le_rfl
    have hn := fun t (ht : |t| ≤ 1) => hb y hy t _ (Or.inl ⟨rfl, ht⟩)
    have hfar := fun t => hb y hy t _ (Or.inr rfl)
    have hk : ∀ t : ℝ, |(|t| ^ (p + 1))| = |t| ^ (p + 1) := fun t =>
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)
    set S : ℝ → ℝ := fun z => c01_secant f y z with hS
    set T0 : ℝ → ℝ := fun z => c03_P_eps p ε u (S z) / |y - z| ^ (p + 1) with hT0
    set T1 : ℝ → ℝ := fun z => (S z - u) * (1 - A_eps p ε (S z) / A_eps p ε u) /
      |y - z| ^ (p + 1) with hT1
    set T2 : ℝ → ℝ := fun z => (u - deriv f z) * (1 - A_eps p ε (S z) / A_eps p ε u) /
      |y - z| ^ (p + 1) with hT2
    have hρm : Measurable (fun z => 1 - A_eps p ε (S z) / A_eps p ε u) :=
      measurable_const.sub ((hA.measurable.comp (hSm y)).div measurable_const)
    have hi0 : Integrable T0 := by
      refine c03_aux_dom_int p hp hp1 _ y
        ((hP2.measurable.comp (measurable_const.prodMk (hSm y))).div (hkm y)) Λ M (fun t => ?_)
      simp only [hT0, hS, sub_sub_cancel]
      rw [abs_div, hk]
      exact c03_aux_psi_bound p hp hΛ hM t _ (fun ht => (hn t ht).2.2.2.2.1) (hfar t).2.2.2.2.1
    have hi1 : Integrable T1 := by
      refine c03_aux_dom_int p hp hp1 _ y
        ((((hSm y).sub measurable_const).mul hρm).div (hkm y)) Λ M (fun t => ?_)
      simp only [hT1, hS, sub_sub_cancel]
      rw [abs_div, hk]
      exact c03_aux_psi_bound p hp hΛ hM t _ (fun ht => (hn t ht).2.2.2.2.2) (hfar t).2.2.2.2.2
    have hi2 : Integrable T2 := by
      refine c03_aux_dom_int p hp hp1 _ y
        (((measurable_const.sub hdc.measurable).mul hρm).div (hkm y)) Λ M (fun t => ?_)
      simp only [hT2, hS, sub_sub_cancel]
      rw [abs_div, hk]
      have e : ∀ a b : ℝ, |(u - a) * (1 - b)| = |(u - a) * (b - 1)| := fun a b => by
        rw [abs_mul, abs_mul, abs_sub_comm 1 b]
      rw [e]
      exact c03_aux_psi_bound p hp hΛ hM t _ (fun ht => (hn t ht).2.2.1) (hfar t).2.2.1
    -- the primitive
    set G : ℝ → ℝ := fun z => (y - z) / |y - z| ^ (p + 1) * c03_P_eps p ε u (S z) with hG
    set G' : ℝ → ℝ := fun z => p * T0 z + T1 z + T2 z with hG'
    have hderiv : ∀ z, z ≠ y → HasDerivAt G (G' z) z := by
      intro z hz
      obtain ⟨hSd, -, -, hkd⟩ := c03_secant_ibp p ε hp hp1 hε f hC1 y z hz
      have hPd := (c03_aux_P_hasDerivAt_snd p hε u (S z)).comp z hSd
      have := hkd.mul hPd
      refine this.congr_deriv ?_
      have hyz : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
      simp only [hG', hT0, hT1, hT2, Function.comp]
      field_simp
      ring
    have hG'i : Integrable G' := ((hi0.const_mul p).add hi1).add hi2
    have hGy : G y = 0 := by simp [hG]
    -- `|G z| = |y-z|^{-p} |P|`
    have hGabs : ∀ z, |G z| = |y - z| ^ (-p) * |c03_P_eps p ε u (S z)| := fun z => by
      simp only [hG]
      rw [abs_mul, abs_div, hk, c03_aux_div_rpow p hp (abs_nonneg _)]
    have hPb : ∀ z, |c03_P_eps p ε u (S z)| ≤ M := fun z => by
      have := (hfar (y - z)).2.2.2.2.1
      simpa only [sub_sub_cancel] using this
    have hcont0 : Tendsto G (𝓝 y) (𝓝 0) := by
      have hc : Continuous (fun z : ℝ => Λ * |y - z| ^ (1 - p)) :=
        continuous_const.mul ((continuous_const.sub continuous_id).abs.rpow_const
          (fun _ => Or.inr (by linarith)))
      have h0 : Tendsto (fun z : ℝ => Λ * |y - z| ^ (1 - p)) (𝓝 y) (𝓝 0) := by
        have := hc.tendsto y
        simpa [Real.zero_rpow (by linarith : (1 - p) ≠ 0)] using this
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [Icc_mem_nhds (show y - 1 < y by linarith) (show y < y + 1 by linarith)]
        with z hz
      rw [Real.norm_eq_abs, hGabs]
      have ht : |y - z| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
      have := (hn (y - z) ht).2.2.2.2.1
      simp only [sub_sub_cancel] at this
      calc |y - z| ^ (-p) * |c03_P_eps p ε u (S z)| ≤ |y - z| ^ (-p) * (Λ * |y - z|) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Λ * |y - z| ^ (1 - p) := by
            rcases (abs_nonneg (y - z)).eq_or_lt with h | h
            · rw [← h, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]; ring
            · rw [show (1 - p) = -p + 1 by ring, Real.rpow_add_one h.ne']; ring
    have hinf : ∀ l : Filter ℝ, Tendsto (fun z => |y - z|) l atTop → Tendsto G l (𝓝 0) := by
      intro l hl
      have h0 : Tendsto (fun z : ℝ => M * |y - z| ^ (-p)) l (𝓝 0) := by
        have := ((tendsto_rpow_neg_atTop hp).comp hl).const_mul M
        simpa using this
      refine squeeze_zero_norm' (Eventually.of_forall fun z => ?_) h0
      rw [Real.norm_eq_abs, hGabs, mul_comm M]
      exact mul_le_mul_of_nonneg_left (hPb z) (by positivity)
    have htop : Tendsto G atTop (𝓝 0) := hinf _ (by
      have : Tendsto (fun z : ℝ => z - y) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
      exact (tendsto_abs_atTop_atTop.comp this).congr (fun z => by simp only [Function.comp]; exact abs_sub_comm _ _))
    have hbot : Tendsto G atBot (𝓝 0) := hinf _ (by
      have : Tendsto (fun z : ℝ => z - y) atBot atBot := tendsto_atBot_add_const_right _ _ tendsto_id
      exact (tendsto_abs_atBot_atTop.comp this).congr (fun z => by simp only [Function.comp]; exact abs_sub_comm _ _))
    have hIoi := integral_Ioi_of_hasDerivAt_of_tendsto (f := G) (f' := G') (a := y) (m := 0)
      (by rw [ContinuousWithinAt, hGy]; exact hcont0.mono_left nhdsWithin_le_nhds)
      (fun z hz => hderiv z (ne_of_gt hz)) hG'i.integrableOn htop
    have hIic := integral_Iic_of_hasDerivAt_of_tendsto (f := G) (f' := G') (a := y) (m := 0)
      (by rw [ContinuousWithinAt, hGy]; exact hcont0.mono_left nhdsWithin_le_nhds)
      (fun z hz => hderiv z (ne_of_lt hz)) hG'i.integrableOn hbot
    have hzero : ∫ z, G' z = 0 := by
      rw [← intervalIntegral.integral_Iic_add_Ioi hG'i.integrableOn hG'i.integrableOn, hIoi, hIic,
        hGy]; ring
    have e1 : ∫ z, (p * T0 z + T1 z) = p * (∫ z, T0 z) + ∫ z, T1 z := by
      rw [integral_add (hi0.const_mul p) hi1, integral_const_mul]
    have hsplit : ∫ z, G' z = p * (∫ z, T0 z) + (∫ z, T1 z) + ∫ z, T2 z := by
      simp only [hG']
      rw [integral_add (f := fun z => p * T0 z + T1 z) ((hi0.const_mul p).add hi1) hi2, e1]
    -- assemble
    have hJ : J_eps p ε f y / A_eps p ε u = calpha p * -(∫ z, T2 z) := by
      unfold J_eps
      rw [mul_div_assoc, ← integral_div, ← integral_neg]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      have hAu' : A_eps p ε (deriv f y) ≠ 0 := hAu
      simp only [hT2, hS, hu]
      field_simp
      ring
    have hI : c03_I_eps p ε f y = calpha p * (p * (∫ z, T0 z) + ∫ z, T1 z) := by
      unfold c03_I_eps
      rw [← e1, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hT0, hT1, hS, hu, c03_Gamma_eps]
      ring
    rw [hJ, hI]
    have : p * (∫ z, T0 z) + ∫ z, T1 z = -∫ z, T2 z := by linarith [hzero.symm.trans hsplit]
    rw [this]
  refine ⟨key, fun y => ?_⟩
  unfold residual
  rw [c03_aux_B_eq p hε, add_div, key y]
  field_simp
  ring

/-- `∂₁Γ_ε(0,v) = c_α (A_ε(v) - 1)`. -/
theorem c03_aux_Gamma_d1_zero (p : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (v : ℝ) :
    deriv (fun u => c03_Gamma_eps p ε u v) 0 = calpha p * (A_eps p ε v - 1) := by
  have hA0 : A_eps p ε 0 = 1 := by simp [A_eps]
  have hA'0 : HasDerivAt (A_eps p ε) 0 0 := by
    simpa using c03_aux_A_hasDerivAt p hε 0
  have hne : A_eps p ε 0 ≠ 0 := by rw [hA0]; exact one_ne_zero
  have hF := c03_aux_A_prim_hasDerivAt p hε 0
  have hP : HasDerivAt (fun u => c03_P_eps p ε u v) 0 0 := by
    have e : (fun u => c03_P_eps p ε u v) = fun u => (v - u) - ((∫ s in (0 : ℝ)..v, A_eps p ε s) -
        (∫ s in (0 : ℝ)..u, A_eps p ε s)) / A_eps p ε u := funext fun u => c03_aux_P_eq p hε u v
    rw [e]
    have := ((hasDerivAt_id (0 : ℝ)).const_sub v).sub ((hF.const_sub
      (∫ s in (0 : ℝ)..v, A_eps p ε s)).div hA'0 hne)
    exact this.congr_deriv (by rw [hA0]; simp)
  have hQ : HasDerivAt (fun u => (v - u) * (1 - A_eps p ε v / A_eps p ε u))
      (-1 * (1 - A_eps p ε v / A_eps p ε 0) + (v - 0) * (-((0 * A_eps p ε 0 - A_eps p ε v * 0) /
        A_eps p ε 0 ^ 2))) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_sub v |>.congr_deriv (by simp)).mul
      (((hasDerivAt_const (0 : ℝ) (A_eps p ε v)).div hA'0 hne).const_sub 1)
  have hG := ((hP.const_mul p).add hQ).const_mul (calpha p)
  unfold c03_Gamma_eps
  exact hG.deriv.trans (by rw [hA0]; ring)

/-- `W'(y) = 0` for `y > 0`. -/
theorem c03_aux_corner_deriv {y : ℝ} (hy : 0 < y) : deriv corner y = 0 := by
  have hev : corner =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [lt_mem_nhds hy] with x hx
    simp [corner, hx.le]
  rw [hev.deriv_eq]; simp

/-- The secant of the corner for `y > 0`. -/
theorem c03_aux_corner_secant {y : ℝ} (hy : 0 < y) (z : ℝ) :
    c03_secant corner y z = if z < 0 then z / (y - z) else 0 := by
  unfold c03_secant c01_secant
  split_ifs with h1 h2 h2
  · subst h1; linarith
  · exact c03_aux_corner_deriv hy
  · simp [corner, hy.le, max_eq_left (le_of_lt (neg_pos.2 h2))]
  · have hz : 0 ≤ z := not_lt.1 h2
    simp [corner, hy.le, hz]


/-- `c_α > 0` for `0 < p < 1`. -/
theorem c03_aux_calpha_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : 0 < calpha p := by
  unfold calpha
  have h1 : 0 < Real.Gamma (1 + p) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.sin (π * p / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  positivity

/-- `(1-t)^{p-1}` is integrable on `(0,1)`, with integral `1/p`. -/
theorem c03_aux_one_sub_rpow (p : ℝ) (hp : 0 < p) :
    IntervalIntegrable (fun t : ℝ => (1 - t) ^ (p - 1)) volume 0 1 ∧
    ∫ t in (0 : ℝ)..1, (1 - t) ^ (p - 1) = 1 / p := by
  constructor
  · have := (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0) (r := p - 1)
      (by linarith)).comp_sub_left 1
    simpa using this
  · rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ (p - 1)), sub_self, sub_zero,
      integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.one_rpow,
      Real.zero_rpow hp.ne', sub_zero]

/-- The main computation of `lem:analysis_coefficient` (for `y > 1`). -/
theorem c03_aux_coefficient_main (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (y : ℝ)
    (hy : 1 < y) :
    Integrable (fun z => deriv (fun u => c03_Gamma_eps p ε u (c03_secant corner y z))
        (deriv corner y) / |y - z| ^ (p + 1)) ∧
      ∫ z, deriv (fun u => c03_Gamma_eps p ε u (c03_secant corner y z)) (deriv corner y) /
        |y - z| ^ (p + 1) = c_eps p ε * y ^ (-p) := by
  have hy0 : 0 < y := by linarith
  set c := calpha p
  set A := A_eps p ε
  set h : ℝ → ℝ := fun z => c * (A (z / (y - z)) - 1) / (y - z) ^ (p + 1) with hh
  have hfun : (fun z => deriv (fun u => c03_Gamma_eps p ε u (c03_secant corner y z))
      (deriv corner y) / |y - z| ^ (p + 1)) = (Iio (0 : ℝ)).indicator h := by
    funext z
    rw [c03_aux_corner_deriv hy0, c03_aux_Gamma_d1_zero p hε, c03_aux_corner_secant hy0]
    by_cases hz : z < 0
    · simp only [hz, ↓reduceIte]
      rw [indicator_of_mem (mem_Iio.2 hz), abs_of_pos (by linarith)]
    · simp only [hz, ↓reduceIte]
      rw [indicator_of_notMem (by simpa using hz)]
      simp [A_eps]
  -- the change of variables `z = φ(t) = -yt/(1-t)`
  set φ : ℝ → ℝ := fun t => -y * t / (1 - t) with hφ
  set φ' : ℝ → ℝ := fun t => -y / (1 - t) ^ 2 with hφ'
  have hφd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (φ' t) (Ioo 0 1) t := by
    intro t ht
    have h1t : (1 - t) ≠ 0 := by linarith [ht.2]
    have := ((hasDerivAt_id t).const_mul (-y)).div ((hasDerivAt_id t).const_sub 1) h1t
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [hφ', id, mul_one]
    field_simp
    ring
  have hinj : InjOn φ (Ioo 0 1) := by
    intro t₁ ht₁ t₂ ht₂ he
    simp only [hφ] at he
    have h1 : 1 - t₁ ≠ 0 := by linarith [ht₁.2]
    have h2 : 1 - t₂ ≠ 0 := by linarith [ht₂.2]
    rw [div_eq_div_iff h1 h2] at he
    have : y * (t₁ - t₂) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have himage : φ '' Ioo 0 1 = Iio 0 := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      simp only [hφ, mem_Iio]
      apply div_neg_of_neg_of_pos _ (by linarith [ht.2])
      nlinarith [ht.1]
    · intro hz
      rw [mem_Iio] at hz
      refine ⟨-z / (y - z), ⟨div_pos (by linarith) (by linarith), ?_⟩, ?_⟩
      · rw [div_lt_one (by linarith)]; linarith
      · simp only [hφ]
        have : y - z ≠ 0 := by linarith
        have hy0' : y ≠ 0 := hy0.ne'
        field_simp
        rw [show y - z - -z = y by ring]; field_simp
  -- the transformed integrand
  set K : ℝ → ℝ := fun t => c * y ^ (-p) * ((A t - 1) * (1 - t) ^ (p - 1)) with hK
  have hKeq : ∀ t ∈ Ioo (0 : ℝ) 1, |φ' t| • h (φ t) = K t := by
    intro t ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have hyφ : y - φ t = y / (1 - t) := by
      simp only [hφ]; field_simp; ring
    have hφq : φ t / (y - φ t) = -t := by
      rw [hyφ]; simp only [hφ]; field_simp
    have hAeven : A (-t) = A t := by simp [A, A_eps]
    simp only [hh, hK, smul_eq_mul]
    rw [hφq, hAeven, hyφ, Real.div_rpow hy0.le h1t.le]
    have hφ'abs : |φ' t| = y / (1 - t) ^ 2 := by
      simp only [hφ']; rw [abs_div, abs_neg, abs_of_pos hy0, abs_of_pos (by positivity)]
    rw [hφ'abs]
    have e1 : y ^ (p + 1) = y ^ p * y := Real.rpow_add_one hy0.ne' p
    have e2 : (1 - t) ^ (p + 1) = (1 - t) ^ (p - 1) * (1 - t) ^ 2 := by
      rw [show p + 1 = (p - 1) + 2 by ring, Real.rpow_add h1t, Real.rpow_two]
    have e3 : y ^ (-p) = (y ^ p)⁻¹ := Real.rpow_neg hy0.le p
    have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy0 p
    rw [e1, e2, e3]
    field_simp
  -- integrability on `(0,1)`
  obtain ⟨hint1, hval1⟩ := c03_aux_one_sub_rpow p hp
  have hAc : Continuous A := (c03_aux_A_contDiff p hε (n := 0)).continuous
  have hKint : IntegrableOn K (Ioo 0 1) := by
    have hg : IntegrableOn (fun t : ℝ => (1 - t) ^ (p - 1)) (Ioo 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 hint1
    have := hg.bdd_mul (f := fun t => A t - 1) (c := 1)
      ((hAc.sub continuous_const).aestronglyMeasurable)
      (Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [c03_aux_A_pos p hε t, c03_aux_A_le_one p hp hε t]))
    exact this.const_mul (c * y ^ (-p))
  have hhint : IntegrableOn h (Iio 0) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hφd hinj]
    exact hKint.congr_fun (fun t ht => (hKeq t ht).symm) measurableSet_Ioo
  have hhval : ∫ z in Iio 0, h z = c_eps p ε * y ^ (-p) := by
    rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hφd hinj,
      setIntegral_congr_fun measurableSet_Ioo hKeq]
    simp only [hK]
    rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      zero_le_one, c_eps]
    ring
  rw [hfun]
  exact ⟨(integrable_indicator_iff measurableSet_Iio).2 hhint,
    by rw [integral_indicator measurableSet_Iio, hhval]⟩

/-- Blueprint: lem:analysis_coefficient.  For `y > 1` the integral
`∫ ∂₁Γ_ε(W'(y), S_W(y,z)) |y-z|^{-α} dz` converges absolutely and equals `c_ε y^{-p}`
(`c_ε = GSQG.c_eps`, in `GSQG/Definitions`); hence `b_ε(y) = c_ε χ₊(y) y^{-p}` for any cutoff `χ₊` as in the
blueprint; and `|c_ε| ≤ c_α α ε/(2p)`, `c_0 = 0`. -/
theorem analysis_coefficient (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∀ y, 1 < y →
      Integrable (fun z => deriv (fun u => c03_Gamma_eps p ε u (c03_secant corner y z))
        (deriv corner y) / |y - z| ^ (p + 1)) ∧
      ∫ z, deriv (fun u => c03_Gamma_eps p ε u (c03_secant corner y z)) (deriv corner y) /
        |y - z| ^ (p + 1) = c_eps p ε * y ^ (-p)) ∧
    (∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → (∀ x ≤ 1, χ x = 0) → (∀ x ≥ 2, χ x = 1) →
      ∀ y : ℝ, (if 1 < y then χ y * ∫ z, deriv (fun u => c03_Gamma_eps p ε u
          (c03_secant corner y z)) (deriv corner y) / |y - z| ^ (p + 1) else 0) =
        c_eps p ε * χ y * y ^ (-p)) ∧
    |c_eps p ε| ≤ calpha p * (p + 1) / (2 * p) * ε ∧
    c_eps p 0 = 0 := by
  refine ⟨fun y hy => c03_aux_coefficient_main p ε hp hp1 hε y hy, fun χ _ hχ0 _ y => ?_, ?_, ?_⟩
  · split_ifs with hy
    · rw [(c03_aux_coefficient_main p ε hp hp1 hε y hy).2]; ring
    · rw [hχ0 y (not_lt.1 hy)]; ring
  · obtain ⟨hint1, hval1⟩ := c03_aux_one_sub_rpow p hp
    have hc := c03_aux_calpha_pos p hp hp1
    unfold c_eps
    rw [abs_mul, abs_of_pos hc]
    have hb : ‖∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * (1 - t) ^ (p - 1)‖ ≤
        ∫ t in (0 : ℝ)..1, (p + 1) / 2 * ε * (1 - t) ^ (p - 1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · refine Eventually.of_forall (fun t ht => ?_)
        have h1 : 0 ≤ (1 - t) ^ (p - 1) := Real.rpow_nonneg (by linarith [ht.2]) _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_sub_comm]
        have h2 := c03_aux_one_sub_A p hp hε t
        have h3 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
        have h4 : (p + 1) / 2 * ε * t ^ 2 ≤ (p + 1) / 2 * ε := by
          have : 0 ≤ (p + 1) / 2 * ε := by positivity
          nlinarith
        exact mul_le_mul_of_nonneg_right (h2.trans h4) h1
      · exact hint1.const_mul _
    rw [intervalIntegral.integral_const_mul, hval1, Real.norm_eq_abs] at hb
    calc calpha p * |∫ t in (0 : ℝ)..1, (A_eps p ε t - 1) * (1 - t) ^ (p - 1)|
        ≤ calpha p * ((p + 1) / 2 * ε * (1 / p)) := mul_le_mul_of_nonneg_left hb hc.le
      _ = calpha p * (p + 1) / (2 * p) * ε := by field_simp
  · simp [c_eps, A_eps]

/-! ## Smoothness of profiles: Hölder calculus -/

/-- Blueprint: lem:c03_holder_calculus.  Product estimate and composition estimate in `C^s(I)`,
`I` a compact interval of length `≥ 1`. -/
theorem c03_holder_calculus (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) :
    (∃ C, 0 < C ∧ ∀ a₀ b₀ : ℝ, 1 ≤ b₀ - a₀ → ∀ a b : ℝ → ℂ,
      a ∈ c03_holder s (Icc a₀ b₀) → b ∈ c03_holder s (Icc a₀ b₀) →
      (a * b) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (a * b) ≤
        C * (c03_holder_supNorm (Icc a₀ b₀) a * c03_holder_normR s (Icc a₀ b₀) b +
          c03_holder_normR s (Icc a₀ b₀) a * c03_holder_supNorm (Icc a₀ b₀) b)) ∧
    (∀ K M : ℝ, 0 < K → 0 ≤ M → ∃ C', 0 < C' ∧ ∀ a₀ b₀ : ℝ, 1 ≤ b₀ - a₀ →
      ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G →
      (∀ j ≤ ⌈s⌉₊ + 1, ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖iteratedFDeriv ℝ j G q‖ ≤ M) →
      ∀ u v : ℝ → ℝ, u ∈ c03_holder s (Icc a₀ b₀) → v ∈ c03_holder s (Icc a₀ b₀) →
      (∀ x ∈ Icc a₀ b₀, |u x| ≤ K ∧ |v x| ≤ K) →
      (fun x => G (u x, v x)) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (fun x => G (u x, v x)) ≤
        C' * (1 + c03_holder_normR s (Icc a₀ b₀) u +
          c03_holder_normR s (Icc a₀ b₀) v) ^ ⌈s⌉₊) := by
  set k := ⌊s⌋₊ with hk
  have hks : (k : ℝ) ≤ s := Nat.floor_le hs.le
  have hks' : (k : ℝ) < s := by
    rcases hks.lt_or_eq with h | h
    · exact h
    · exact absurd h.symm (hsN k)
  have hceil : ⌈s⌉₊ = k + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero k)]
    push_cast
    constructor
    · linarith
    · exact (Nat.lt_floor_add_one s).le
  obtain ⟨Cp, hCp0, hCp⟩ := c03_holder_product_tame s hs hsN
  refine ⟨⟨Cp, hCp0, fun a₀ b₀ hab a b ha hb => ?_⟩, fun K M hK hM => ?_⟩
  · obtain ⟨hmem, hle⟩ := hCp a₀ b₀ hab a b ha hb
    exact ⟨hmem, hle.trans (le_of_eq (by ring))⟩
  · obtain ⟨C, hC0, hC⟩ := c03_holder_composition_higher s hs hsN K M hK hM
    refine ⟨C, hC0, fun a₀ b₀ hab G hG hGM u v hu hv huv => ?_⟩
    rw [hceil]
    exact hC a₀ b₀ hab G hG (fun j hj q hq => hGM j (by rw [hceil]; omega) q hq) u v hu hv huv

/-- Differentiation under the integral sign, within a convex set. -/
theorem c03_aux_hasDerivWithinAt_integral {T : Type*} [MeasurableSpace T] {ν : Measure T}
    {I : Set ℝ} (hI : Convex ℝ I) {φ ψ : ℝ → T → ℂ} {B : T → ℝ} (hB : Integrable B ν)
    (hφint : ∀ x ∈ I, Integrable (φ x) ν) (hψmeas : ∀ x ∈ I, AEStronglyMeasurable (ψ x) ν)
    (hderiv : ∀ᵐ τ ∂ν, ∀ y ∈ I, HasDerivWithinAt (fun y => φ y τ) (ψ y τ) I y)
    (hbound : ∀ᵐ τ ∂ν, ∀ y ∈ I, ‖ψ y τ‖ ≤ B τ) {x : ℝ} (hx : x ∈ I) :
    HasDerivWithinAt (fun y => ∫ τ, φ y τ ∂ν) (∫ τ, ψ x τ ∂ν) I x := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hev : ∀ᶠ y in 𝓝[I \ {x}] x, slope (fun y => ∫ τ, φ y τ ∂ν) x y =
      ∫ τ, slope (fun y => φ y τ) x y ∂ν := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope, vsub_eq_sub]
    rw [← integral_sub (hφint y hy.1) (hφint x hx), integral_smul]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hB ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope, vsub_eq_sub]
    exact (((hφint y hy.1).sub (hφint x hx)).smul ((y - x)⁻¹)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with y hy
    filter_upwards [hderiv, hbound] with τ hτ hτb
    have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le hτ hτb hx hy.1
    have hne : y - x ≠ 0 := sub_ne_zero.2 hy.2
    simp only [slope, vsub_eq_sub, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [Real.norm_eq_abs] at hmv
    rw [inv_mul_le_iff₀ (abs_pos.2 hne)]
    linarith [hmv, mul_comm (B τ) |y - x|]
  · filter_upwards [hderiv] with τ hτ
    exact (hasDerivWithinAt_iff_tendsto_slope.1 (hτ x hx))

theorem c03_aux_sum_lintegral_le {T : Type*} [MeasurableSpace T] {ν : Measure T} (n : ℕ)
    (f : ℕ → T → ℝ≥0∞) :
    ∑ i ∈ Finset.range n, ∫⁻ τ, f i τ ∂ν ≤ ∫⁻ τ, ∑ i ∈ Finset.range n, f i τ ∂ν := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    exact (add_le_add ih le_rfl).trans (le_lintegral_add _ _)

/-- A function continuous on `[a,b]` is bounded there by its supremum over the rational points of
`[a,b]` together with the left endpoint. -/
theorem c03_aux_le_rat_sup {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ≥0∞} (hf : ContinuousOn f (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    f x ≤ f a ⊔ ⨆ q : ℚ, (if (q : ℝ) ∈ Icc a b then f q else 0) := by
  rcases hab.lt_or_eq with hab | rfl
  · set c := f a ⊔ ⨆ q : ℚ, (if (q : ℝ) ∈ Icc a b then f q else 0)
    have hsub : Icc a b ⊆ closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) := by
      rw [← closure_Ioo hab.ne]
      refine closure_minimal ((Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo).trans
        (closure_mono fun y hy => hy)) isClosed_closure
    have hcl : closure (Ioo a b ∩ range ((↑) : ℚ → ℝ)) ⊆ Icc a b :=
      (closure_mono inter_subset_left).trans (closure_Ioo hab.ne ▸ subset_rfl)
    refine le_on_closure (f := f) (g := fun _ => c) (fun y hy => ?_) (hf.mono hcl)
      continuousOn_const (hsub hx)
    obtain ⟨hy, q, rfl⟩ := hy
    refine le_sup_of_le_right (le_iSup_of_le q ?_)
    simp [Ioo_subset_Icc_self hy]
  · have : x = a := le_antisymm hx.2 hx.1
    rw [this]; exact le_sup_left

theorem c03_aux_derivWithin_Icc_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a x : ℝ} (hx : x ∈ Icc a a) : derivWithin f (Icc a a) x = 0 := by
  have hxa : x = a := le_antisymm hx.2 hx.1
  subst hxa
  apply derivWithin_zero_of_not_accPt
  rw [accPt_iff_nhds]
  push Not
  exact ⟨univ, univ_mem, fun y hy => le_antisymm hy.2.2 hy.2.1⟩

/-- Blueprint: lem:c03_parametric_holder.  `F(x) = ∫ H(x,τ) dν(τ)` is in `C^s(I)` with
`‖F‖_{C^s(I)} ≤ ∫ ‖H(·,τ)‖_{C^s(I)} dν`. -/
theorem c03_parametric_holder (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) (a₀ b₀ : ℝ)
    (hab : a₀ ≤ b₀) {T : Type*} [MeasurableSpace T] (ν : Measure T) [SigmaFinite ν]
    (H : ℝ → T → ℂ)
    (hH : ∀ᵐ τ ∂ν, (fun x => H x τ) ∈ c03_holder s (Icc a₀ b₀))
    (hmeas : ∀ i ≤ ⌊s⌋₊, Measurable (fun q : (Icc a₀ b₀) × T =>
      iteratedDerivWithin i (fun x => H x q.2) (Icc a₀ b₀) q.1))
    (hint : ∫⁻ τ, c03_holder_norm s (Icc a₀ b₀) (fun x => H x τ) ∂ν < ⊤) :
    (fun x => ∫ τ, H x τ ∂ν) ∈ c03_holder s (Icc a₀ b₀) ∧
    c03_holder_norm s (Icc a₀ b₀) (fun x => ∫ τ, H x τ ∂ν) ≤
      ∫⁻ τ, c03_holder_norm s (Icc a₀ b₀) (fun x => H x τ) ∂ν := by
  set k := ⌊s⌋₊ with hk
  set I := Icc a₀ b₀ with hI
  set D : ℕ → ℝ → T → ℂ := fun i x τ => iteratedDerivWithin i (fun x => H x τ) I x with hD
  set F : ℝ → ℂ := fun x => ∫ τ, H x τ ∂ν with hF
  have ha₀ : a₀ ∈ I := left_mem_Icc.2 hab
  have hDmeas : ∀ i ≤ k, ∀ x ∈ I, Measurable (D i x) := fun i hi x hx =>
    (hmeas i hi).comp (measurable_prodMk_left (x := (⟨x, hx⟩ : I)))
  -- continuity on `I` of the derivatives of the good sections
  have hcont : ∀ τ, (fun x => H x τ) ∈ c03_holder s I → ∀ i ≤ k,
      ContinuousOn (fun x => D i x τ) I := by
    intro τ hτ i hi
    rcases hab.lt_or_eq with hlt | heq
    · exact hτ.1.continuousOn_iteratedDerivWithin (by exact_mod_cast hi) (uniqueDiffOn_Icc hlt)
    · intro x hx
      have : I = {a₀} := by rw [hI, heq, Icc_self]
      rw [this] at hx ⊢
      rw [mem_singleton_iff] at hx
      subst hx
      exact continuousWithinAt_singleton
  -- measurable majorants
  set Bi : ℕ → T → ℝ≥0∞ := fun i τ =>
    ‖D i a₀ τ‖ₑ ⊔ ⨆ q : ℚ, (if (q : ℝ) ∈ I then ‖D i q τ‖ₑ else 0) with hBi
  have hBimeas : ∀ i ≤ k, Measurable (Bi i) := by
    intro i hi
    refine (hDmeas i hi a₀ ha₀).enorm.sup (Measurable.iSup fun q => ?_)
    by_cases hq : (q : ℝ) ∈ I
    · simp only [hq, if_true]; exact (hDmeas i hi q hq).enorm
    · simp only [hq, if_false]; exact measurable_const
  have hBi_le : ∀ τ, (fun x => H x τ) ∈ c03_holder s I → ∀ i ≤ k,
      Bi i τ ≤ c03_aux_supD i I (fun x => H x τ) := by
    intro τ _ i _
    refine sup_le (le_iSup₂ (f := fun x _ => ‖D i x τ‖ₑ) a₀ ha₀) (iSup_le fun q => ?_)
    split_ifs with hq
    · exact le_iSup₂ (f := fun x _ => ‖D i x τ‖ₑ) (q : ℝ) hq
    · exact bot_le
  have hD_le : ∀ τ, (fun x => H x τ) ∈ c03_holder s I → ∀ i ≤ k, ∀ x ∈ I,
      ‖D i x τ‖ₑ ≤ Bi i τ := fun τ hτ i hi x hx =>
    c03_aux_le_rat_sup hab (continuous_enorm.comp_continuousOn (hcont τ hτ i hi)) hx
  have hBi_fin : ∀ τ, (fun x => H x τ) ∈ c03_holder s I → ∀ i ≤ k, Bi i τ < ⊤ :=
    fun τ hτ i hi => (hBi_le τ hτ i hi).trans_lt (c03_aux_supD_lt_top hτ hi)
  set B : T → ℝ := fun τ => ∑ i ∈ Finset.range (k + 1), (Bi i τ).toReal with hB
  have hBmeas : Measurable B := Finset.measurable_sum _ fun i hi =>
    (hBimeas i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).ennreal_toReal
  have hBint : Integrable B ν := by
    refine ⟨hBmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint
    filter_upwards [hH] with τ hτ
    have hB0 : 0 ≤ B τ := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    rw [Real.enorm_eq_ofReal hB0, ENNReal.ofReal_sum_of_nonneg fun _ _ => ENNReal.toReal_nonneg,
      c03_aux_norm_eq]
    refine le_trans ?_ le_self_add
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [ENNReal.ofReal_toReal (hBi_fin τ hτ i hi').ne]
    exact hBi_le τ hτ i hi'
  have hDbd : ∀ τ, (fun x => H x τ) ∈ c03_holder s I → ∀ i ≤ k, ∀ x ∈ I, ‖D i x τ‖ ≤ B τ := by
    intro τ hτ i hi x hx
    have h1 : ‖D i x τ‖ ≤ (Bi i τ).toReal := by
      have := hD_le τ hτ i hi x hx
      rw [← ofReal_norm] at this
      exact (ENNReal.ofReal_le_iff_le_toReal (hBi_fin τ hτ i hi).ne).1 this
    exact h1.trans (Finset.single_le_sum (f := fun i => (Bi i τ).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
  have hDint : ∀ i ≤ k, ∀ x ∈ I, Integrable (D i x) ν := fun i hi x hx =>
    hBint.mono' (hDmeas i hi x hx).aestronglyMeasurable
      (by filter_upwards [hH] with τ hτ; exact hDbd τ hτ i hi x hx)
  -- derivatives of the integral
  have hderI : a₀ < b₀ → ∀ i < k, ∀ x ∈ I, HasDerivWithinAt (fun y => ∫ τ, D i y τ ∂ν)
      (∫ τ, D (i + 1) x τ ∂ν) I x := by
    intro hlt i hi x hx
    have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hlt
    refine c03_aux_hasDerivWithinAt_integral (convex_Icc a₀ b₀) hBint (hDint i hi.le)
      (fun y hy => (hDmeas (i + 1) hi y hy).aestronglyMeasurable) ?_ ?_ hx
    · filter_upwards [hH] with τ hτ
      intro y hy
      have hd := (hτ.1.differentiableOn_iteratedDerivWithin (m := i) (by exact_mod_cast hi) hU) y hy
      simp only [D]
      rw [iteratedDerivWithin_succ]
      exact hd.hasDerivWithinAt
    · filter_upwards [hH] with τ hτ
      exact fun y hy => hDbd τ hτ (i + 1) hi y hy
  have hid : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i F I x = ∫ τ, D i x τ ∂ν := by
    intro i
    induction i with
    | zero => intro _ x _; simp [D, F]
    | succ i ih =>
      intro hi x hx
      rw [iteratedDerivWithin_succ]
      have heqOn : EqOn (iteratedDerivWithin i F I) (fun y => ∫ τ, D i y τ ∂ν) I :=
        fun y hy => ih (by omega) y hy
      rw [derivWithin_congr heqOn (heqOn hx)]
      rcases hab.lt_or_eq with hlt | heq
      · exact (hderI hlt i (by omega) x hx).derivWithin ((uniqueDiffOn_Icc hlt) x hx)
      · have hx' : x ∈ Icc a₀ a₀ := by
          have h1 := hx; rw [hI, ← heq] at h1; exact h1
        have e1 : ∀ g : ℝ → ℂ, derivWithin g I x = 0 := fun g => by
          rw [hI, ← heq]; exact c03_aux_derivWithin_Icc_self g hx'
        rw [e1]
        have : ∀ τ, D (i + 1) x τ = 0 := fun τ => by
          simp only [D]; rw [iteratedDerivWithin_succ]; exact e1 _
        simp [this]
  -- smoothness of `F`
  have hcd : ContDiffOn ℝ k F I := by
    rcases hab.lt_or_eq with hlt | heq
    · have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hlt
      have key : ∀ j ≤ k, ContDiffOn ℝ j (fun y => ∫ τ, D (k - j) y τ ∂ν) I := by
        intro j
        induction j with
        | zero =>
          intro _
          simp only [Nat.sub_zero, CharP.cast_eq_zero]
          refine contDiffOn_zero.2 (continuousOn_of_dominated
            (fun x hx => (hDmeas k le_rfl x hx).aestronglyMeasurable)
            (fun x hx => by filter_upwards [hH] with τ hτ; exact hDbd τ hτ k le_rfl x hx) hBint ?_)
          filter_upwards [hH] with τ hτ
          exact hcont τ hτ k le_rfl
        | succ j ih =>
          intro hj
          have hjk : k - (j + 1) < k := by omega
          have e : k - (j + 1) + 1 = k - j := by omega
          rw [Nat.cast_add, Nat.cast_one]
          refine (contDiffOn_succ_iff_derivWithin (n := (j : WithTop ℕ∞)) hU).2 ⟨fun x hx =>
            (hderI hlt _ hjk x hx).differentiableWithinAt, fun h => by simp at h, ?_⟩
          refine (ih (by omega)).congr fun x hx => ?_
          rw [(hderI hlt _ hjk x hx).derivWithin (hU x hx), e]
      have := key k le_rfl
      simp only [Nat.sub_self] at this
      refine this.congr fun x _ => ?_
      simp [D, F]
    · intro x hx
      have : I = {a₀} := by rw [hI, heq, Icc_self]
      rw [this] at hx ⊢
      rw [mem_singleton_iff] at hx
      subst hx
      exact contDiffWithinAt_singleton
  -- the norm bound
  have hsupF : ∀ i ≤ k, c03_aux_supD i I F ≤ ∫⁻ τ, c03_aux_supD i I (fun x => H x τ) ∂ν := by
    intro i hi
    refine iSup₂_le fun x hx => ?_
    rw [hid i hi x hx]
    exact (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono fun τ => le_iSup₂ (f := fun x _ => ‖D i x τ‖ₑ) x hx)
  set Sm := ∫⁻ τ, c03_aux_semi s I (fun x => H x τ) ∂ν
  have hSm : Sm < ⊤ := lt_of_le_of_lt (lintegral_mono fun τ => le_add_self) hint
  have hsemiF : c03_aux_semi s I F ≤ Sm := by
    refine iInf_le_of_le Sm.toNNReal (iInf_le_of_le ?_ (by rw [ENNReal.coe_toNNReal hSm.ne]))
    intro x hx y hy
    rw [hid k le_rfl x hx, hid k le_rfl y hy, edist_eq_enorm_sub,
      ← integral_sub (hDint k le_rfl x hx) (hDint k le_rfl y hy), ENNReal.coe_toNNReal hSm.ne]
    calc ‖∫ τ, (D k x τ - D k y τ) ∂ν‖ₑ ≤ ∫⁻ τ, ‖D k x τ - D k y τ‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ τ, c03_aux_semi s I (fun x => H x τ) *
            edist x y ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hH] with τ hτ
          have := c03_aux_semi_holder hτ x hx y hy
          rw [edist_eq_enorm_sub, ENNReal.coe_toNNReal (c03_aux_semi_lt_top hτ).ne] at this
          exact this
      _ = Sm * edist x y ^ ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) :=
          lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (NNReal.coe_nonneg _)
            (edist_ne_top x y))
  have hnorm : c03_holder_norm s I F ≤ ∫⁻ τ, c03_holder_norm s I (fun x => H x τ) ∂ν := by
    rw [c03_aux_norm_eq]
    calc ∑ i ∈ Finset.range (k + 1), c03_aux_supD i I F + c03_aux_semi s I F
        ≤ ∑ i ∈ Finset.range (k + 1), ∫⁻ τ, c03_aux_supD i I (fun x => H x τ) ∂ν + Sm :=
          add_le_add (Finset.sum_le_sum fun i hi =>
            hsupF i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) hsemiF
      _ ≤ ∫⁻ τ, ∑ i ∈ Finset.range (k + 1), c03_aux_supD i I (fun x => H x τ) ∂ν + Sm :=
          add_le_add (c03_aux_sum_lintegral_le _ _) le_rfl
      _ ≤ ∫⁻ τ, (∑ i ∈ Finset.range (k + 1), c03_aux_supD i I (fun x => H x τ) +
            c03_aux_semi s I (fun x => H x τ)) ∂ν := le_lintegral_add _ _
      _ = ∫⁻ τ, c03_holder_norm s I (fun x => H x τ) ∂ν := by
          congr 1
  exact ⟨⟨hcd, lt_of_le_of_lt hnorm hint⟩, hnorm⟩


/-- Blueprint: lem:c03_I_near.  The near part
`ℐ^near_ε(f)(y) = ∫ χ(t) Γ_ε(f'(y), S_f(y,y-t)) |t|^{-α} dt`. -/
def c03_I_near_op (p ε : ℝ) (χ : ℝ → ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t, χ t * c03_Gamma_eps p ε (deriv f y) (c01_secant f y (y - t)) / |t| ^ (p + 1)

/-- Blueprint: lem:c03_I_far.  The far part
`ℐ^far_ε(f)(y) = ∫ (1-χ(y-z)) Γ_ε(f'(y), S_f(y,z)) |y-z|^{-α} dz`. -/
def c03_I_far_op (p ε : ℝ) (χ : ℝ → ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z, (1 - χ (y - z)) * c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) / |y - z| ^ (p + 1)

/-- Uniform bounds on `‖∇^j G‖`, `j ≤ N`, on `[-K,K]²`. -/
theorem c03_aux_G_bound (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (N : ℕ) (K : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j ≤ N, ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖iteratedFDeriv ℝ j G q‖ ≤ M := by
  choose M hM using fun j : ℕ => (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-K) K ×ˢ Icc (-K) K)).exists_bound_of_continuousOn
    ((hG.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)
  refine ⟨∑ j ∈ Finset.range (N + 1), max (M j) 0, Finset.sum_nonneg fun j _ => le_max_right _ _,
    fun j hj q hq => (hM j q hq).trans ((le_max_left (M j) 0).trans ?_)⟩
  exact Finset.single_le_sum (f := fun j => max (M j) 0) (fun i _ => le_max_right _ _)
    (Finset.mem_range.2 (by omega))

section NearAux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restriction of a globally `C^k` function to a subinterval does not increase the norm. -/
theorem c03_aux_holder_restrict {s : ℝ} {g : ℝ → E} (hg : ContDiff ℝ ⌊s⌋₊ g) {a b c d : ℝ}
    (hcd : c < d) (hsub : Icc c d ⊆ Icc a b) (hgI : g ∈ c03_holder s (Icc a b)) :
    g ∈ c03_holder s (Icc c d) ∧ c03_holder_normR s (Icc c d) g ≤ c03_holder_normR s (Icc a b) g := by
  set k := ⌊s⌋₊
  have hab : a < b := by
    have h1 := hsub ⟨le_rfl, hcd.le⟩; have h2 := hsub ⟨hcd.le, le_rfl⟩
    linarith [h1.1, h2.2]
  have hU1 : UniqueDiffOn ℝ (Icc c d) := uniqueDiffOn_Icc hcd
  have hU2 : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ x ∈ Icc c d,
      iteratedDerivWithin i g (Icc c d) x = iteratedDerivWithin i g (Icc a b) x := by
    intro i hi x hx
    have hca : ContDiffAt ℝ i g x := (hg.of_le (by exact_mod_cast hi)).contDiffAt
    rw [iteratedDerivWithin_eq_iteratedDeriv hU1 hca hx,
      iteratedDerivWithin_eq_iteratedDeriv hU2 hca (hsub hx)]
  have hH := c03_aux_semi_holder hgI
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s (Icc c d) g hg.contDiffOn
    (fun i => (c03_aux_supD i (Icc a b) g).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun i hi x hx => by rw [heq i hi x hx]; exact c03_aux_le_supD hgI hi (hsub hx))
    (c03_aux_semi s (Icc a b) g).toNNReal
    (fun x hx y hy => by
      rw [heq k le_rfl x hx, heq k le_rfl y hy]; exact hH x (hsub hx) y (hsub hy))
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hgI, ENNReal.coe_toNNReal_eq_toReal]

/-- Multiplication by a complex constant. -/
theorem c03_aux_normR_const_mul {s : ℝ} {a b : ℝ} (hab : a < b) (c : ℂ) {g : ℝ → ℂ}
    (hg : g ∈ c03_holder s (Icc a b)) :
    (fun x => c * g x) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun x => c * g x) ≤ ‖c‖ * c03_holder_normR s (Icc a b) g := by
  set k := ⌊s⌋₊
  set I := Icc a b
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have heq : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i (fun x => c * g x) I x =
      c * iteratedDerivWithin i g I x := fun i hi x hx =>
    iteratedDerivWithin_const_mul hx hU c ((hg.1.of_le (by exact_mod_cast hi)) x hx)
  have hH := c03_aux_semi_holder hg
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I _ (contDiffOn_const.mul hg.1)
    (fun i => ‖c‖ * (c03_aux_supD i I g).toReal) (fun _ _ => by positivity)
    (fun i hi x hx => by
      rw [heq i hi x hx, norm_mul]
      exact mul_le_mul_of_nonneg_left (c03_aux_le_supD hg hi hx) (norm_nonneg _))
    (‖c‖₊ * (c03_aux_semi s I g).toNNReal)
    (by
      refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
      rw [heq k le_rfl x hx, heq k le_rfl y hy, dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
      push_cast
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hH.dist_le hx hy) (norm_nonneg _))
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hg, ← Finset.mul_sum]
  push_cast [ENNReal.coe_toNNReal_eq_toReal]
  ring

/-- Derivatives of the difference quotient `(f(y) - f(y-t))/t`. -/
theorem c03_aux_iteratedDeriv_dq {f : ℝ → ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (t : ℝ) {i : ℕ}
    (hi : i ≤ n) (y : ℝ) :
    iteratedDeriv i (fun y => (f y - f (y - t)) / t) y =
      (iteratedDeriv i f y - iteratedDeriv i f (y - t)) / t := by
  have h1 : ContDiffAt ℝ i f y := (hf.of_le (by exact_mod_cast hi)).contDiffAt
  have h2 : ContDiffAt ℝ i (fun y => f (y - t)) y :=
    ((hf.of_le (by exact_mod_cast hi)).comp (contDiff_id.sub contDiff_const)).contDiffAt
  rw [iteratedDeriv_div_const, iteratedDeriv_fun_sub h1 h2, iteratedDeriv_comp_sub_const]

end NearAux

/-- The difference quotient `y ↦ (f(y) - f(y-t))/t`, `0 < |t| ≤ 2`, satisfies
`‖·‖_{C^s([a,b])} ≤ ‖f'‖_{C^s([a-2,b+2])}`. -/
theorem c03_aux_dq_holder {s : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ (⌊s⌋₊ + 1) f)
    {a b : ℝ} (hab : a < b) (hJ : deriv f ∈ c03_holder s (Icc (a - 2) (b + 2))) {t : ℝ}
    (ht0 : t ≠ 0) (ht2 : |t| ≤ 2) :
    (fun y => (f y - f (y - t)) / t) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun y => (f y - f (y - t)) / t) ≤
        c03_holder_normR s (Icc (a - 2) (b + 2)) (deriv f) := by
  set k := ⌊s⌋₊
  set I := Icc a b
  set J := Icc (a - 2) (b + 2)
  set g : ℝ → ℝ := fun y => (f y - f (y - t)) / t
  have hab' : a - 2 < b + 2 := by linarith
  have hUI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hUJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc hab'
  have hg : ContDiff ℝ (k + 1) g :=
    (hf.sub (hf.comp (contDiff_id.sub contDiff_const))).div_const t
  have hf' : ContDiff ℝ k (deriv f) := by
    have := hf.iterate_deriv' k 1
    simpa using this
  have htpos : 0 < |t| := abs_pos.2 ht0
  have hFd : ∀ i ≤ k, ∀ u, HasDerivAt (iteratedDeriv i f) (iteratedDeriv i (deriv f) u) u := by
    intro i hi u
    have hd : Differentiable ℝ (iteratedDeriv i f) :=
      hf.differentiable_iteratedDeriv i (by exact_mod_cast Nat.lt_succ_of_le hi)
    have := (hd u).hasDerivAt
    rwa [← iteratedDeriv_succ, iteratedDeriv_succ'] at this
  have hgI : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i g I x =
      (iteratedDeriv i f x - iteratedDeriv i f (x - t)) / t := by
    intro i hi x hx
    rw [iteratedDerivWithin_eq_iteratedDeriv hUI
      ((hg.of_le (by exact_mod_cast Nat.le_succ_of_le hi)).contDiffAt) hx]
    exact c03_aux_iteratedDeriv_dq hf t (Nat.le_succ_of_le hi) x
  have hfJ : ∀ i ≤ k, ∀ x ∈ J, iteratedDerivWithin i (deriv f) J x = iteratedDeriv i (deriv f) x :=
    fun i hi x hx => iteratedDerivWithin_eq_iteratedDeriv hUJ
      ((hf'.of_le (by exact_mod_cast hi)).contDiffAt) hx
  have hxJ : ∀ x ∈ I, ∀ u, |u| ≤ 2 → x + u ∈ J := fun x hx u hu =>
    ⟨by linarith [hx.1, (abs_le.1 hu).1], by linarith [hx.2, (abs_le.1 hu).2]⟩
  have hseg : ∀ x ∈ I, uIcc (x - t) x ⊆ J := by
    intro x hx
    have h1 := hxJ x hx (-t) (by rwa [abs_neg])
    have h2 := hxJ x hx 0 (by simp)
    rw [← sub_eq_add_neg] at h1
    rw [add_zero] at h2
    exact uIcc_subset_Icc h1 h2
  -- sup bounds
  have hA : ∀ i ≤ k, ∀ x ∈ I, ‖iteratedDerivWithin i g I x‖ ≤
      (c03_aux_supD i J (deriv f)).toReal := by
    intro i hi x hx
    rw [hgI i hi x hx]
    set S := (c03_aux_supD i J (deriv f)).toReal
    have hmv := (convex_uIcc (x - t) x).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := iteratedDeriv i f) (f' := iteratedDeriv i (deriv f)) (C := S)
      (fun u _ => (hFd i hi u).hasDerivWithinAt)
      (fun u hu => by
        rw [← hfJ i hi u (hseg x hx hu)]; exact c03_aux_le_supD hJ hi (hseg x hx hu))
      left_mem_uIcc right_mem_uIcc
    rw [show x - (x - t) = t by ring] at hmv
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 ht0)]
    exact hmv
  -- Hölder bound of the top derivative
  have hHJ := c03_aux_semi_holder hJ
  set Bf := (c03_aux_semi s J (deriv f)).toNNReal
  have hB : HolderOnWith Bf (Real.toNNReal (s - ⌊s⌋₊)) (iteratedDerivWithin ⌊s⌋₊ g I) I := by
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [hgI k le_rfl x hx, hgI k le_rfl y hy, dist_eq_norm]
    set F := iteratedDeriv k f
    set P := iteratedDeriv k (deriv f)
    set θr : ℝ := ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ)
    have hφ : ∀ u ∈ uIcc (-t) 0, HasDerivWithinAt (fun u => F (x + u) - F (y + u))
        (P (x + u) - P (y + u)) (uIcc (-t) 0) u := fun u _ =>
      (((hFd k le_rfl (x + u)).comp_const_add x u).sub
        ((hFd k le_rfl (y + u)).comp_const_add y u)).hasDerivWithinAt
    have hu2 : ∀ u ∈ uIcc (-t) 0, |u| ≤ 2 := fun u hu => by
      have := abs_sub_right_of_mem_uIcc hu
      simp only [zero_sub, abs_neg, sub_neg_eq_add, zero_add] at this
      linarith
    have hbd : ∀ u ∈ uIcc (-t) 0, ‖P (x + u) - P (y + u)‖ ≤ Bf * dist x y ^ θr := by
      intro u hu
      have h1 := hxJ x hx u (hu2 u hu)
      have h2 := hxJ y hy u (hu2 u hu)
      have e1 : P (x + u) = iteratedDerivWithin k (deriv f) J (x + u) := (hfJ k le_rfl _ h1).symm
      have e2 : P (y + u) = iteratedDerivWithin k (deriv f) J (y + u) := (hfJ k le_rfl _ h2).symm
      rw [e1, e2, ← dist_eq_norm]
      have := hHJ.dist_le h1 h2
      rwa [show dist (x + u) (y + u) = dist x y by simp [Real.dist_eq]] at this
    have hmv := (convex_uIcc (-t) 0).norm_image_sub_le_of_norm_hasDerivWithin_le hφ hbd
      left_mem_uIcc right_mem_uIcc
    simp only [add_zero, zero_sub, norm_neg, Real.norm_eq_abs] at hmv
    have e : (F x - F (x - t)) / t - (F y - F (y - t)) / t =
        ((F (x + 0) - F (y + 0)) - (F (x + -t) - F (y + -t))) / t := by
      simp only [add_zero, ← sub_eq_add_neg]; ring
    rw [e, norm_div, div_le_iff₀ (norm_pos_iff.2 ht0), Real.norm_eq_abs, Real.norm_eq_abs]
    simpa using hmv
  have hcd : ContDiffOn ℝ ⌊s⌋₊ g I := (hg.of_le (by exact_mod_cast Nat.le_succ k)).contDiffOn
  obtain ⟨hmem, hle⟩ := c03_aux_normR_le s I g hcd (fun i => (c03_aux_supD i J (deriv f)).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) hA Bf hB
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  rw [c03_aux_normR_eq hJ, ENNReal.coe_toNNReal_eq_toReal]

/-- `|f'(y) - (f(y)-f(y-t))/t| ≤ L|t|` for `f'` `L`-Lipschitz on the segment. -/
theorem c03_aux_dq_sub_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {L : ℝ} (hL0 : 0 ≤ L) {J : Set ℝ}
    (hL : ∀ x ∈ J, ∀ x' ∈ J, |deriv f x - deriv f x'| ≤ L * |x - x'|) {y t : ℝ} (ht0 : t ≠ 0)
    (hseg : uIcc (y - t) y ⊆ J) : |deriv f y - (f y - f (y - t)) / t| ≤ L * |t| := by
  have hyJ : y ∈ J := hseg right_mem_uIcc
  have hφ : ∀ u ∈ uIcc (y - t) y, HasDerivWithinAt (fun u => f u - u * deriv f y)
      (deriv f u - deriv f y) (uIcc (y - t) y) u := fun u _ => by
    have h1 := ((hf.differentiable one_ne_zero) u).hasDerivAt
    have h2 := (hasDerivAt_id u).mul_const (deriv f y)
    have h3 : HasDerivAt (fun u => f u - u * deriv f y) (deriv f u - 1 * deriv f y) u := h1.sub h2
    rw [one_mul] at h3
    exact h3.hasDerivWithinAt
  have hb : ∀ u ∈ uIcc (y - t) y, ‖deriv f u - deriv f y‖ ≤ L * |t| := by
    intro u hu
    rw [Real.norm_eq_abs]
    refine (hL u (hseg hu) y hyJ).trans ?_
    have h1 := abs_sub_right_of_mem_uIcc hu
    rw [show y - (y - t) = t by ring] at h1
    rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left h1 hL0
  have hmv := (convex_uIcc (y - t) y).norm_image_sub_le_of_norm_hasDerivWithin_le hφ hb
    left_mem_uIcc right_mem_uIcc
  rw [show y - (y - t) = t by ring, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have e : deriv f y - (f y - f (y - t)) / t =
      -((f y - y * deriv f y - (f (y - t) - (y - t) * deriv f y)) / t) := by
    field_simp; ring
  rw [e, abs_neg, abs_div, div_le_iff₀ (abs_pos.2 ht0)]
  linarith

/-- Joint measurability of a derivative within `[a,b]` (as a limit of difference quotients). -/
theorem c03_aux_measurable_derivWithin {T : Type*} [MeasurableSpace T] {a b : ℝ} (hab : a < b)
    {φ : ℝ → T → ℂ} (hφ : Measurable (fun q : Icc a b × T => φ q.1 q.2))
    (hd : ∀ t, ∀ y ∈ Icc a b, DifferentiableWithinAt ℝ (fun y => φ y t) (Icc a b) y) :
    Measurable (fun q : Icc a b × T => derivWithin (fun y => φ y q.2) (Icc a b) q.1) := by
  set c := (a + b) / 2
  set δ := (b - a) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  set σ : ℝ → ℝ := fun y => if y ≤ c then 1 else -1
  have hσm : Measurable σ := Measurable.ite measurableSet_Iic measurable_const measurable_const
  set h : ℕ → ℝ := fun n => δ / (n + 1)
  have hh0 : ∀ n, 0 < h n := fun n => by positivity
  have hhδ : ∀ n, h n ≤ δ := fun n => div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have hmem : ∀ n, ∀ y : Icc a b, (y : ℝ) + σ y * h n ∈ Icc a b := by
    intro n y
    obtain ⟨hy1, hy2⟩ := y.2
    have h1 := hhδ n
    have h2 := hh0 n
    have e1 : c = (a + b) / 2 := rfl
    have e2 : δ = (b - a) / 2 := rfl
    simp only [σ]
    split_ifs with hc
    · constructor <;> nlinarith
    · push Not at hc
      constructor <;> nlinarith
  set yn : ℕ → Icc a b × T → Icc a b × T := fun n q => (⟨q.1 + σ q.1 * h n, hmem n q.1⟩, q.2)
  have hynm : ∀ n, Measurable (yn n) := by
    intro n
    refine Measurable.prodMk (Measurable.subtype_mk ?_) measurable_snd
    exact (measurable_subtype_coe.comp measurable_fst).add
      ((hσm.comp (measurable_subtype_coe.comp measurable_fst)).mul measurable_const)
  set Q : ℕ → Icc a b × T → ℂ := fun n q =>
    (σ q.1 * h n)⁻¹ • (φ (q.1 + σ q.1 * h n) q.2 - φ q.1 q.2)
  have hQm : ∀ n, Measurable (Q n) := by
    intro n
    have h1 : Measurable (fun q : Icc a b × T => (σ q.1 * h n)⁻¹) :=
      ((hσm.comp (measurable_subtype_coe.comp measurable_fst)).mul measurable_const).inv
    have h2 : Measurable (fun q : Icc a b × T => φ (q.1 + σ q.1 * h n) q.2 - φ q.1 q.2) :=
      (hφ.comp (hynm n)).sub hφ
    exact h1.smul h2
  refine measurable_of_tendsto_metrizable hQm (tendsto_pi_nhds.2 fun q => ?_)
  have hD := (hd q.2 q.1 q.1.2).hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hD
  have hσ1 : σ q.1 ≠ 0 := by simp only [σ]; split_ifs <;> norm_num
  have hlim : Tendsto (fun n => (q.1 : ℝ) + σ q.1 * h n) atTop (𝓝[Icc a b \ {(q.1 : ℝ)}] q.1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ⟨hmem n q.1, ?_⟩⟩
    · have : Tendsto h atTop (𝓝 0) := by
        simp only [h]
        exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1
          tendsto_natCast_atTop_atTop)
      simpa using (this.const_mul (σ q.1)).const_add (q.1 : ℝ)
    · simp only [mem_singleton_iff, add_eq_left]
      exact mul_ne_zero hσ1 (hh0 n).ne'
  refine (hD.comp hlim).congr fun n => ?_
  simp only [Function.comp, slope, vsub_eq_sub, Q, add_sub_cancel_left]

/-- Joint measurability of iterated derivatives within `[a,b]`. -/
theorem c03_aux_measurable_iteratedDerivWithin {T : Type*} [MeasurableSpace T] {a b : ℝ}
    (hab : a < b) {n : ℕ} {φ : ℝ → T → ℂ} (hφ : Measurable (fun q : Icc a b × T => φ q.1 q.2))
    (hcd : ∀ t, ContDiffOn ℝ n (fun y => φ y t) (Icc a b)) :
    ∀ i ≤ n, Measurable (fun q : Icc a b × T =>
      iteratedDerivWithin i (fun y => φ y q.2) (Icc a b) q.1) := by
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  intro i
  induction i with
  | zero => intro _; simpa using hφ
  | succ i ih =>
    intro hi
    simp only [iteratedDerivWithin_succ]
    exact c03_aux_measurable_derivWithin hab (φ := fun y t => iteratedDerivWithin i (fun y => φ y t)
      (Icc a b) y) (ih (by omega)) fun t y hy =>
        ((hcd t).differentiableOn_iteratedDerivWithin (m := i) (by exact_mod_cast hi) hU) y hy


/-- The `C^s` norm in `[0,∞]` is the `ofReal` of the real norm for members. -/
theorem c03_aux_norm_eq_ofReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ℝ}
    {I : Set ℝ} {g : ℝ → E} (hg : g ∈ c03_holder s I) :
    c03_holder_norm s I g = ENNReal.ofReal (c03_holder_normR s I g) := by
  unfold c03_holder_normR; rw [ENNReal.ofReal_toReal hg.2.ne]

/-- The zero function on an interval. -/
theorem c03_aux_holder_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℝ) {a b : ℝ}
    (hab : a < b) : (fun _ : ℝ => (0 : E)) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun _ : ℝ => (0 : E)) ≤ 0 := by
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have h0 : ∀ i, ∀ x ∈ Icc a b, iteratedDerivWithin i (fun _ : ℝ => (0 : E)) (Icc a b) x = 0 :=
    fun i x hx => c03_aux_derivWithin_zero _ _ (fun _ _ => rfl) i hx
  obtain ⟨hm, hle⟩ := c03_aux_normR_le s (Icc a b) (fun _ : ℝ => (0 : E)) contDiffOn_const
    (fun _ => 0) (fun _ _ => le_rfl) (fun i _ x hx => by rw [h0 i x hx, norm_zero]) 0
    (c03_aux_holderOnWith_of_dist fun x hx y hy => by rw [h0 _ x hx, h0 _ y hy]; simp)
  exact ⟨hm, by simpa using hle⟩

/-- `C^s` composition estimate on intervals of length `≥ ℓ` (`s`-form of `c03_aux_comp_ind_len`). -/
theorem c03_aux_comp_len (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) (ℓ : ℝ) (hℓ0 : 0 < ℓ)
    (hℓ1 : ℓ ≤ 1) (K M : ℝ) (hK : 0 < K) (hM : 0 ≤ M) :
    ∃ C, 0 < C ∧ ∀ a₀ b₀ : ℝ, ℓ ≤ b₀ - a₀ →
      ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G →
      (∀ j ≤ ⌊s⌋₊ + 2, ∀ q ∈ Icc (-K) K ×ˢ Icc (-K) K, ‖iteratedFDeriv ℝ j G q‖ ≤ M) →
      ∀ u v : ℝ → ℝ, u ∈ c03_holder s (Icc a₀ b₀) → v ∈ c03_holder s (Icc a₀ b₀) →
      (∀ x ∈ Icc a₀ b₀, |u x| ≤ K ∧ |v x| ≤ K) →
      (fun x => G (u x, v x)) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (fun x => G (u x, v x)) ≤
        C * (1 + c03_holder_normR s (Icc a₀ b₀) u +
          c03_holder_normR s (Icc a₀ b₀) v) ^ (⌊s⌋₊ + 1) := by
  set k := ⌊s⌋₊ with hk
  set θ := s - k with hθ
  have hks : (k : ℝ) ≤ s := Nat.floor_le hs.le
  have hθ0 : 0 < θ := by
    rcases (sub_nonneg.2 hks).lt_or_eq with h | h
    · exact h
    · exact absurd (by linarith : s = k) (hsN k)
  have hθ1 : θ < 1 := by have := Nat.lt_floor_add_one s; simp only [hθ]; linarith
  have e : (k : ℝ) + θ = s := by simp only [hθ]; ring
  obtain ⟨C, hC0, hC⟩ := c03_aux_comp_ind_len ℓ hℓ0 hℓ1 k θ hθ0 hθ1 K M hK hM
  refine ⟨C, hC0, fun a₀ b₀ hab G hG hGM u v hu hv huv => ?_⟩
  have := hC a₀ b₀ hab G hG hGM u v (by rw [e]; exact hu) (by rw [e]; exact hv) huv
  rw [e] at this
  exact this

/-- The near integrand `y ↦ χ(t) Γ_ε(f'(y), S_f(y,y-t)) |t|^{-α}` on `[a,b]`, for fixed `t`:
membership in `C^s` and the bound `ψ(t)` (integrable in `t`). -/
theorem c03_aux_near_slice (p ε s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hs : 0 < s)
    (ℓ : ℝ) (hℓ0 : 0 < ℓ) (K' L' M' MG Cc Cp : ℝ) (hK' : 0 < K') (hL' : 0 ≤ L') (hM' : 0 ≤ M')
    (hMG0 : 0 ≤ MG) (hCc0 : 0 < Cc) (hCp0 : 0 < Cp)
    (hMG : ∀ j ≤ ⌊s⌋₊ + 2, ∀ q ∈ Icc (-K') K' ×ˢ Icc (-K') K',
      ‖iteratedFDeriv ℝ j (fun q : ℝ × ℝ => ((c03_Gamma_eps_tilde p ε q.1 q.2 : ℝ) : ℂ)) q‖ ≤ MG)
    (hCc : ∀ a₀ b₀ : ℝ, ℓ ≤ b₀ - a₀ →
      ∀ G : ℝ × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G →
      (∀ j ≤ ⌊s⌋₊ + 2, ∀ q ∈ Icc (-K') K' ×ˢ Icc (-K') K', ‖iteratedFDeriv ℝ j G q‖ ≤ MG) →
      ∀ u v : ℝ → ℝ, u ∈ c03_holder s (Icc a₀ b₀) → v ∈ c03_holder s (Icc a₀ b₀) →
      (∀ x ∈ Icc a₀ b₀, |u x| ≤ K' ∧ |v x| ≤ K') →
      (fun x => G (u x, v x)) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (fun x => G (u x, v x)) ≤
        Cc * (1 + c03_holder_normR s (Icc a₀ b₀) u +
          c03_holder_normR s (Icc a₀ b₀) v) ^ (⌊s⌋₊ + 1))
    (hCp : ∀ a₀ b₀ : ℝ, ℓ ≤ b₀ - a₀ → ∀ a b : ℝ → ℂ,
      a ∈ c03_holder s (Icc a₀ b₀) → b ∈ c03_holder s (Icc a₀ b₀) →
      (a * b) ∈ c03_holder s (Icc a₀ b₀) ∧
      c03_holder_normR s (Icc a₀ b₀) (a * b) ≤
        Cp * (c03_holder_supNorm (Icc a₀ b₀) a * c03_holder_normR s (Icc a₀ b₀) b +
          c03_holder_supNorm (Icc a₀ b₀) b * c03_holder_normR s (Icc a₀ b₀) a))
    (χ : ℝ → ℝ) (hχ2 : ∀ t, 2 < |t| → χ t = 0) (hχ01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (f : ℝ → ℝ) (hf1c : ContDiff ℝ 1 f) (hf1 : ContDiff ℝ (⌊s⌋₊ + 1) f)
    (hfk : ContDiff ℝ ⌊s⌋₊ (deriv f)) (hKK : ∀ x, |deriv f x| ≤ K')
    (a b : ℝ) (hab : ℓ ≤ b - a)
    (hLJ : ∀ x ∈ Icc (a - 2) (b + 2), ∀ x' ∈ Icc (a - 2) (b + 2),
      |deriv f x - deriv f x'| ≤ L' * |x - x'|)
    (hfJ : deriv f ∈ c03_holder s (Icc (a - 2) (b + 2)))
    (hJM : c03_holder_normR s (Icc (a - 2) (b + 2)) (deriv f) ≤ M') (t : ℝ) :
    (fun y => ((χ t * c03_Gamma_eps p ε (deriv f y) (c01_secant f y (y - t)) / |t| ^ (p + 1) : ℝ)
      : ℂ)) ∈ c03_holder s (Icc a b) ∧
    c03_holder_normR s (Icc a b) (fun y => ((χ t * c03_Gamma_eps p ε (deriv f y)
      (c01_secant f y (y - t)) / |t| ^ (p + 1) : ℝ) : ℂ)) ≤
      c03_aux_psi p (Cp * (2 * L' ^ 2 * (Cc * (1 + M' + M') ^ (⌊s⌋₊ + 1)) +
        MG * (4 * Cp * L' * M'))) (2 * (Cp * (2 * L' ^ 2 * (Cc * (1 + M' + M') ^ (⌊s⌋₊ + 1)) +
        MG * (4 * Cp * L' * M')))) t := by
  set k := ⌊s⌋₊ with hk
  have hab' : a < b := by linarith
  set I := Icc a b with hI
  set J := Icc (a - 2) (b + 2) with hJdef
  have hIJ : I ⊆ J := Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨hfI, hfIn⟩ := c03_aux_holder_restrict hfk hab' hIJ hfJ
  have hfIM : c03_holder_normR s I (deriv f) ≤ M' := hfIn.trans hJM
  have hseg : ∀ x ∈ I, ∀ t : ℝ, |t| ≤ 2 → uIcc (x - t) x ⊆ J := by
    intro x hx t ht
    have h1 : x - t ∈ J := ⟨by linarith [hx.1, (abs_le.1 ht).2], by linarith [hx.2, (abs_le.1 ht).1]⟩
    have h2 : x ∈ J := hIJ hx
    exact uIcc_subset_Icc h1 h2
  set Gt : ℝ × ℝ → ℂ := fun q => ((c03_Gamma_eps_tilde p ε q.1 q.2 : ℝ) : ℂ) with hGt_def
  have hGtc : ContDiff ℝ (⊤ : ℕ∞) Gt :=
    Complex.ofRealCLM.contDiff.comp (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.2
  set A1 := Cc * (1 + M' + M') ^ (k + 1)
  have hA1 : 0 ≤ A1 := by positivity
  set C2 := Cp * (2 * L' ^ 2 * A1 + MG * (4 * Cp * L' * M'))
  have hC2 : 0 ≤ C2 := by positivity
  have hψ0 : ∀ t, 0 ≤ c03_aux_psi p C2 (2 * C2) t := c03_aux_psi_nonneg p hC2 (by positivity)
  set Hf : ℝ → ℝ → ℂ := fun y t =>
    ((χ t * c03_Gamma_eps p ε (deriv f y) (c01_secant f y (y - t)) / |t| ^ (p + 1) : ℝ) : ℂ)
    with hHf
  have hp1' : p + 1 ≠ 0 := by linarith
  show (fun y => Hf y t) ∈ c03_holder s I ∧
      c03_holder_normR s I (fun y => Hf y t) ≤ c03_aux_psi p C2 (2 * C2) t
  by_cases hzero : t = 0 ∨ 2 < |t|
  · have hz : ∀ y, Hf y t = 0 := by
      intro y
      rcases hzero with rfl | ht
      · simp [Hf, Real.zero_rpow hp1']
      · simp [Hf, hχ2 t ht]
    obtain ⟨hm, hn⟩ := c03_aux_holder_zero (E := ℂ) s hab'
    have hc := c03_aux_holder_congr (s := s) (I := I) (f := fun y => Hf y t)
      (g := fun _ => (0 : ℂ)) (fun y _ => hz y)
    exact ⟨hc.2.1.2 hm, by rw [hc.2.2.1]; exact hn.trans (hψ0 t)⟩
  push Not at hzero
  obtain ⟨ht0, ht2⟩ := hzero
  set v : ℝ → ℝ := fun y => (f y - f (y - t)) / t with hv_def
  obtain ⟨hv, hvn⟩ := c03_aux_dq_holder hf1 hab' hfJ ht0 ht2
  have hvM : c03_holder_normR s I v ≤ M' := hvn.trans hJM
  have hvK : ∀ y, |v y| ≤ K' := by
    intro y
    have hmv := (convex_uIcc (y - t) y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := deriv f) (C := K')
      (fun u _ => ((hf1c.differentiable one_ne_zero) u).hasDerivAt.hasDerivWithinAt)
      (fun u _ => by rw [Real.norm_eq_abs]; exact hKK u) left_mem_uIcc right_mem_uIcc
    rw [show y - (y - t) = t by ring, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    simp only [v, abs_div]
    rw [div_le_iff₀ (abs_pos.2 ht0)]
    exact hmv
  -- composition
  obtain ⟨hG1, hG1n⟩ := hCc a b hab Gt hGtc (fun j hj q hq => hMG j hj q hq) (deriv f) v
    hfI hv (fun x _ => ⟨hKK x, hvK x⟩)
  have hG1A : c03_holder_normR s I (fun x => Gt (deriv f x, v x)) ≤ A1 := by
    refine hG1n.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) hCc0.le)
    · have := c03_aux_normR_nonneg s I (deriv f); have := c03_aux_normR_nonneg s I v; linarith
    · linarith
  have hG1s : c03_holder_supNorm I (fun x => Gt (deriv f x, v x)) ≤ MG := by
    refine c03_aux_supNorm_le hMG0 fun x _ => ?_
    have := hMG 0 (by omega) (deriv f x, v x) ⟨abs_le.1 (hKK x), abs_le.1 (hvK x)⟩
    rwa [norm_iteratedFDeriv_zero] at this
  -- `d = f' - v`
  obtain ⟨hnv, hnvn, -⟩ := c03_aux_holder_clm_norm hab' (-ContinuousLinearMap.id ℝ ℝ)
    (by rw [norm_neg]; exact ContinuousLinearMap.norm_id_le) hv
  obtain ⟨hd, hdn⟩ := c03_aux_normR_add_le hab' hfI hnv
  obtain ⟨hD, hDn, -⟩ := c03_aux_holder_clm_norm hab' Complex.ofRealCLM
    (by rw [Complex.ofRealCLM_norm]) hd
  set D : ℝ → ℂ := fun x => Complex.ofRealCLM (deriv f x + (-ContinuousLinearMap.id ℝ ℝ) (v x))
    with hD_def
  have hDval : ∀ x, D x = ((deriv f x - v x : ℝ) : ℂ) := by
    intro x; simp [D, sub_eq_add_neg]
  have hDM : c03_holder_normR s I D ≤ 2 * M' := hDn.trans (hdn.trans (by linarith))
  have hDs : c03_holder_supNorm I D ≤ L' * |t| := by
    refine c03_aux_supNorm_le (by positivity) fun x hx => ?_
    rw [hDval, Complex.norm_real, Real.norm_eq_abs]
    exact c03_aux_dq_sub_deriv hf1c hL' hLJ ht0 (hseg x hx t ht2)
  have hDs0 := c03_aux_supNorm_nonneg I D
  -- `D * D`
  obtain ⟨hDD, hDDn⟩ := hCp a b hab D D hD hD
  have hDDn' : c03_holder_normR s I (D * D) ≤ 4 * Cp * L' * M' * |t| := by
    refine hDDn.trans ?_
    have h1 : c03_holder_supNorm I D * c03_holder_normR s I D ≤ L' * |t| * (2 * M') :=
      mul_le_mul hDs hDM (c03_aux_normR_nonneg _ _ _) (by positivity)
    nlinarith
  have hDDs : c03_holder_supNorm I (D * D) ≤ 2 * L' ^ 2 * |t| := by
    refine c03_aux_supNorm_le (by positivity) fun x hx => ?_
    have h1 : ‖D x‖ ≤ L' * |t| := (c03_aux_le_supNorm hD hx).trans hDs
    rw [Pi.mul_apply, norm_mul]
    have h2 : ‖D x‖ * ‖D x‖ ≤ (L' * |t|) * (L' * |t|) :=
      mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
    have h3 : |t| * |t| ≤ 2 * |t| := mul_le_mul_of_nonneg_right ht2 (abs_nonneg _)
    nlinarith
  -- `Γ`
  obtain ⟨hΓm, hΓn⟩ := hCp a b hab (D * D) (fun x => Gt (deriv f x, v x)) hDD hG1
  have hΓn' : c03_holder_normR s I ((D * D) * fun x => Gt (deriv f x, v x)) ≤ C2 * |t| := by
    refine hΓn.trans ?_
    have h1 : c03_holder_supNorm I (D * D) * c03_holder_normR s I (fun x => Gt (deriv f x, v x))
        ≤ 2 * L' ^ 2 * |t| * A1 :=
      mul_le_mul hDDs hG1A (c03_aux_normR_nonneg _ _ _) (by positivity)
    have h2 : c03_holder_supNorm I (fun x => Gt (deriv f x, v x)) * c03_holder_normR s I (D * D)
        ≤ MG * (4 * Cp * L' * M' * |t|) :=
      mul_le_mul hG1s hDDn' (c03_aux_normR_nonneg _ _ _) hMG0
    calc Cp * (c03_holder_supNorm I (D * D) *
          c03_holder_normR s I (fun x => Gt (deriv f x, v x)) +
          c03_holder_supNorm I (fun x => Gt (deriv f x, v x)) * c03_holder_normR s I (D * D))
        ≤ Cp * (2 * L' ^ 2 * |t| * A1 + MG * (4 * Cp * L' * M' * |t|)) := by gcongr
      _ = C2 * |t| := by simp only [C2]; ring
  -- identification of the integrand
  set c : ℝ := χ t / |t| ^ (p + 1)
  have htp : 0 < |t| ^ (p + 1) := Real.rpow_pos_of_pos (abs_pos.2 ht0) _
  have hc0 : 0 ≤ c := div_nonneg (hχ01 t).1 htp.le
  have hid : ∀ y, Hf y t = (c : ℂ) * (((D * D) * fun x => Gt (deriv f x, v x)) y) := by
    intro y
    have hsec : c01_secant f y (y - t) = v y := by
      simp only [c01_secant, v]
      rw [if_neg (by intro h; apply ht0; linarith)]
      congr 1; ring
    have hq := (c03_Gamma_quadratic_factor p ε hp hp1 hε (deriv f y) (v y)).1
    simp only [Hf, hsec, hq, Pi.mul_apply, hDval, Gt, c]
    push_cast; ring
  obtain ⟨hcm, hcn⟩ := c03_aux_normR_const_mul hab' (c : ℂ) hΓm
  have hcg := c03_aux_holder_congr (s := s) (I := I) (f := fun y => Hf y t)
    (g := fun y => (c : ℂ) * (((D * D) * fun x => Gt (deriv f x, v x)) y)) (fun y _ => hid y)
  refine ⟨hcg.2.1.2 hcm, ?_⟩
  rw [hcg.2.2.1]
  refine hcn.trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hC2t : 0 ≤ C2 * |t| := mul_nonneg hC2 (abs_nonneg t)
  have hN0 : 0 ≤ χ t * (C2 * |t|) := mul_nonneg (hχ01 t).1 hC2t
  have hb := c03_aux_psi_bound p hp hC2 (mul_nonneg zero_le_two hC2) t (χ t * (C2 * |t|))
    (fun _ => by
      rw [abs_of_nonneg hN0]
      exact mul_le_of_le_one_left hC2t (hχ01 t).2)
    (by
      rw [abs_of_nonneg hN0]
      calc χ t * (C2 * |t|) ≤ 1 * (C2 * 2) :=
            mul_le_mul (hχ01 t).2 (mul_le_mul_of_nonneg_left ht2 hC2) hC2t zero_le_one
        _ = 2 * C2 := by ring)
  calc c * c03_holder_normR s I ((D * D) * fun x => Gt (deriv f x, v x))
      ≤ c * (C2 * |t|) := mul_le_mul_of_nonneg_left hΓn' hc0
    _ = |χ t * (C2 * |t|)| / |t| ^ (p + 1) := by
        rw [abs_of_nonneg hN0]; simp only [c]; ring
    _ ≤ c03_aux_psi p C2 (2 * C2) t := hb


/-- Real parametric integrals: from per-parameter `C^s` bounds `ψ(t)` (complexified) to the
integral. -/
theorem c03_aux_param_real (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) {a b : ℝ} (hab : a < b)
    (Hr : ℝ → ℝ → ℝ) (hHm : Measurable (fun q : ℝ × ℝ => Hr q.1 q.2)) (ψ : ℝ → ℝ)
    (hψ0 : ∀ t, 0 ≤ ψ t) (hψi : Integrable ψ)
    (hper : ∀ t, (fun y => ((Hr y t : ℝ) : ℂ)) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun y => ((Hr y t : ℝ) : ℂ)) ≤ ψ t) :
    (fun y => ∫ t, Hr y t) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun y => ∫ t, Hr y t) ≤ ∫ t, ψ t := by
  set I := Icc a b
  set Hf : ℝ → ℝ → ℂ := fun y t => ((Hr y t : ℝ) : ℂ) with hHf
  have hHfm : Measurable (fun q : ℝ × ℝ => Hf q.1 q.2) := Complex.measurable_ofReal.comp hHm
  have hmeas : ∀ i ≤ ⌊s⌋₊, Measurable (fun q : I × ℝ =>
      iteratedDerivWithin i (fun x => Hf x q.2) I q.1) :=
    c03_aux_measurable_iteratedDerivWithin hab
      (hHfm.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
      (fun t => (hper t).1.1)
  have hint : ∫⁻ t, c03_holder_norm s I (fun x => Hf x t) ≤ ENNReal.ofReal (∫ t, ψ t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hψi (ae_of_all _ hψ0)]
    exact lintegral_mono fun t => by
      rw [c03_aux_norm_eq_ofReal (hper t).1]; exact ENNReal.ofReal_le_ofReal (hper t).2
  obtain ⟨hFm, hFn⟩ := c03_parametric_holder s hs hsN a b hab.le volume Hf
    (ae_of_all _ fun t => (hper t).1) hmeas (lt_of_le_of_lt hint ENNReal.ofReal_lt_top)
  obtain ⟨hRm, hRn, -⟩ := c03_aux_holder_clm_norm hab Complex.reCLM
    (by rw [Complex.reCLM_norm]) hFm
  have hre : (fun x => Complex.reCLM (∫ t, Hf x t)) = fun y => ∫ t, Hr y t :=
    funext fun x => by
      simp only [Hf, Complex.reCLM_apply]
      rw [show (∫ t, ((Hr x t : ℝ) : ℂ)) = ((∫ t, Hr x t : ℝ) : ℂ) from integral_ofReal,
        Complex.ofReal_re]
  rw [hre] at hRm hRn
  refine ⟨hRm, hRn.trans ?_⟩
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFn.trans hint)
  rw [ENNReal.toReal_ofReal (integral_nonneg hψ0)] at h1
  exact h1


theorem c03_aux_near_meas (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) {χ : ℝ → ℝ}
    (hχ : Continuous χ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Measurable (fun q : ℝ × ℝ => χ q.2 * c03_Gamma_eps p ε (deriv f q.1)
      (c01_secant f q.1 (q.1 - q.2)) / |q.2| ^ (p + 1)) := by
  have hfd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hsec : Measurable (fun q : ℝ × ℝ => c01_secant f q.1 (q.1 - q.2)) := by
    have h1 : Measurable (fun q : ℝ × ℝ => deriv f q.1) := hfd.measurable.comp measurable_fst
    have hfm : Measurable f := hf.continuous.measurable
    have h2 : Measurable (fun q : ℝ × ℝ => (f q.1 - f (q.1 - q.2)) / (q.1 - (q.1 - q.2))) := by
      fun_prop
    have h3 : MeasurableSet {q : ℝ × ℝ | q.1 = q.1 - q.2} :=
      measurableSet_eq_fun measurable_fst (measurable_fst.sub measurable_snd)
    exact Measurable.ite h3 h1 h2
  have hΓc : Measurable (fun r : ℝ × ℝ => c03_Gamma_eps p ε r.1 r.2) :=
    (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.1.continuous.measurable
  have hpair : Measurable (fun q : ℝ × ℝ => (deriv f q.1, c01_secant f q.1 (q.1 - q.2))) :=
    (hfd.measurable.comp measurable_fst).prodMk hsec
  have hΓm : Measurable (fun q : ℝ × ℝ =>
      c03_Gamma_eps p ε (deriv f q.1) (c01_secant f q.1 (q.1 - q.2))) := by
    have h := hΓc.comp hpair
    simp only [Function.comp_def] at h
    exact h
  have hχm : Measurable (fun q : ℝ × ℝ => χ q.2) := hχ.measurable.comp measurable_snd
  have hdm : Measurable (fun q : ℝ × ℝ => |q.2| ^ (p + 1)) :=
    (continuous_abs.measurable.comp measurable_snd).pow_const (p + 1)
  exact (hχm.mul hΓm).div hdm

theorem c03_aux_near_core (p ε s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (ℓ : ℝ) (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (K L M : ℝ) :
    ∃ C, 0 < C ∧ ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → (∀ t, 2 < |t| → χ t = 0) →
      (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
      ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
      (∀ x, |deriv f x| ≤ K) → ∀ a b : ℝ, ℓ ≤ b - a →
      (∀ x ∈ Icc (a - 2) (b + 2), ∀ x' ∈ Icc (a - 2) (b + 2),
        |deriv f x - deriv f x'| ≤ L * |x - x'|) →
      c03_holder_normR s (Icc (a - 2) (b + 2)) (deriv f) ≤ M →
      c03_I_near_op p ε χ f ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (c03_I_near_op p ε χ f) ≤ C := by
  set K' := max K 1
  set L' := max L 0
  set M' := max M 0
  have hK' : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hL' : 0 ≤ L' := le_max_right _ _
  have hM' : 0 ≤ M' := le_max_right _ _
  have hGtc : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ((c03_Gamma_eps_tilde p ε q.1 q.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.2
  obtain ⟨MG, hMG0, hMG⟩ := c03_aux_G_bound _ hGtc (⌊s⌋₊ + 2) K'
  obtain ⟨Cc, hCc0, hCc⟩ := c03_aux_comp_len s hs hsN ℓ hℓ0 hℓ1 K' MG hK' hMG0
  obtain ⟨Cp, hCp0, hCp⟩ := c03_holder_product_tame_len s hs hsN ℓ hℓ0 hℓ1
  set C2 := Cp * (2 * L' ^ 2 * (Cc * (1 + M' + M') ^ (⌊s⌋₊ + 1)) + MG * (4 * Cp * L' * M'))
  have hC2 : 0 ≤ C2 := by positivity
  set ψ := c03_aux_psi p C2 (2 * C2)
  have hψ0 : ∀ t, 0 ≤ ψ t := c03_aux_psi_nonneg p hC2 (by positivity)
  have hψi : Integrable ψ := c03_aux_psi_integrable p C2 (2 * C2) hp hp1
  have hIψ : 0 ≤ ∫ t, ψ t := integral_nonneg hψ0
  refine ⟨(∫ t, ψ t) + 1, by positivity, ?_⟩
  intro χ hχ hχ2 hχ01 f hf hf' hK a b hab hL hM
  have hab' : a < b := by linarith
  obtain ⟨hf1c, -, -⟩ := hf
  have hfk : ContDiff ℝ ⌊s⌋₊ (deriv f) := contDiffOn_univ.1 hf'.1
  have hf1 : ContDiff ℝ (⌊s⌋₊ + 1) f :=
    contDiff_succ_iff_deriv.2 ⟨hf1c.differentiable one_ne_zero, by simp, hfk⟩
  have hfJ : deriv f ∈ c03_holder s (Icc (a - 2) (b + 2)) := hf'.2 _ _ (subset_univ _)
  have hLJ : ∀ x ∈ Icc (a - 2) (b + 2), ∀ x' ∈ Icc (a - 2) (b + 2),
      |deriv f x - deriv f x'| ≤ L' * |x - x'| := fun x hx x' hx' =>
    (hL x hx x' hx').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hKK : ∀ x, |deriv f x| ≤ K' := fun x => (hK x).trans (le_max_left _ _)
  have hJM : c03_holder_normR s (Icc (a - 2) (b + 2)) (deriv f) ≤ M' := hM.trans (le_max_left _ _)
  have hper := c03_aux_near_slice p ε s hp hp1 hε hs ℓ hℓ0 K' L' M' MG Cc Cp hK' hL' hM' hMG0
    hCc0 hCp0 hMG hCc hCp χ hχ2 hχ01 f hf1c hf1 hfk hKK a b hab hLJ hfJ hJM
  obtain ⟨hm, hn⟩ := c03_aux_param_real s hs hsN hab' (fun y t => χ t * c03_Gamma_eps p ε
    (deriv f y) (c01_secant f y (y - t)) / |t| ^ (p + 1))
    (c03_aux_near_meas p ε hp hp1 hε hχ.continuous hf1c) ψ hψ0 hψi hper
  exact ⟨hm, hn.trans (by linarith)⟩

/-- Blueprint: lem:c03_I_near.  `ℐ^near_ε(f) ∈ C^s_loc`, with `‖ℐ^near_ε(f)‖_{C^s([-R,R])} ≤ C`,
`C` depending on `s, R, ε, α` and bounds `K ≥ ‖f'‖_∞`, `L ≥ ‖f''‖_{L^∞(-R-2,R+2)}` (as a Lipschitz
constant of `f'`), `M ≥ ‖f'‖_{C^s([-R-2,R+2])}`. -/
theorem c03_I_near (p ε s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) :
    (∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → (∀ t ∈ Icc (-1) 1, χ t = 1) →
      (∀ t, 2 < |t| → χ t = 0) → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
      ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
        c03_I_near_op p ε χ f ∈ c03_holder_loc s univ) ∧
    ∀ R K L M : ℝ, 0 < R → ∃ C, 0 < C ∧
      ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → (∀ t ∈ Icc (-1) 1, χ t = 1) →
      (∀ t, 2 < |t| → χ t = 0) → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
      ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
      (∀ x, |deriv f x| ≤ K) →
      (∀ x ∈ Icc (-R - 2) (R + 2), ∀ x' ∈ Icc (-R - 2) (R + 2),
        |deriv f x - deriv f x'| ≤ L * |x - x'|) →
      c03_holder_normR s (Icc (-R - 2) (R + 2)) (deriv f) ≤ M →
      c03_holder_normR s (Icc (-R) R) (c03_I_near_op p ε χ f) ≤ C := by
  -- membership on every nondegenerate interval
  have hmem : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → (∀ t, 2 < |t| → χ t = 0) →
      (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) →
      ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
      ∀ a b : ℝ, a < b → c03_I_near_op p ε χ f ∈ c03_holder s (Icc a b) := by
    intro χ hχ hχ2 hχ01 f hf hf' a b hab
    obtain ⟨-, ⟨K, hK⟩, hLip⟩ := id hf
    obtain ⟨L, hL⟩ := (hLip.locallyLipschitzOn (s := Icc (a - 2) (b + 2))).exists_lipschitzOnWith_of_compact
      isCompact_Icc
    set ℓ := min (b - a) 1
    have hℓ0 : 0 < ℓ := lt_min (by linarith) one_pos
    obtain ⟨C, -, hC⟩ := c03_aux_near_core p ε s hp hp1 hε hs hsN ℓ hℓ0 (min_le_right _ _) K L
      (c03_holder_normR s (Icc (a - 2) (b + 2)) (deriv f))
    refine (hC χ hχ hχ2 hχ01 f hf hf' hK a b (min_le_left _ _) (fun x hx x' hx' => ?_) le_rfl).1
    have := hL.dist_le_mul x hx x' hx'
    rwa [Real.dist_eq, Real.dist_eq] at this
  refine ⟨fun χ hχ _ _ hχ2 hχ01 f hf hf' => ?_, fun R K L M hR => ?_⟩
  · have hcd : ContDiff ℝ ⌊s⌋₊ (c03_I_near_op p ε χ f) := by
      refine contDiff_iff_contDiffAt.2 fun x => ?_
      have h := hmem χ hχ hχ2 hχ01 f hf hf' (x - 1) (x + 1) (by linarith)
      exact h.1.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
    refine ⟨hcd.contDiffOn, fun a b _ => ?_⟩
    rcases lt_or_ge a b with hab | hab
    · exact hmem χ hχ hχ2 hχ01 f hf hf' a b hab
    · exact c03_aux_holder_degen s a b hab _ hcd.contDiffOn
  · set ℓ := min (2 * R) 1
    have hℓ0 : 0 < ℓ := lt_min (by linarith) one_pos
    obtain ⟨C, hC0, hC⟩ := c03_aux_near_core p ε s hp hp1 hε hs hsN ℓ hℓ0 (min_le_right _ _) K L M
    refine ⟨C, hC0, fun χ hχ _ _ hχ2 hχ01 f hf hf' hK hL hM => ?_⟩
    have hℓR : ℓ ≤ R - -R := (min_le_left _ _).trans (by linarith)
    exact (hC χ hχ hχ2 hχ01 f hf hf' hK (-R) R hℓR hL hM).2

/-- A globally `C^{k+1}` function with all derivatives up to order `k+1` bounded by `A` on
`[a,b]` lies in `C^s([a,b])` with norm `≤ (k+2+(b-a)) A`. -/
theorem c03_aux_holder_of_derivs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℝ)
    {g : ℝ → E} (hg : ContDiff ℝ (⌊s⌋₊ + 1) g) {a b : ℝ} (hab : a < b) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ i ≤ ⌊s⌋₊ + 1, ∀ x ∈ Icc a b, ‖iteratedDeriv i g x‖ ≤ A) :
    g ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) g ≤ (⌊s⌋₊ + 1) * A + A * (1 + (b - a)) := by
  set k := ⌊s⌋₊
  set I := Icc a b
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast Nat.le_succ k)
  have heq : ∀ i ≤ k, ∀ x ∈ I, iteratedDerivWithin i g I x = iteratedDeriv i g x :=
    fun i hi x hx => iteratedDerivWithin_eq_iteratedDeriv hU
      ((hgk.of_le (by exact_mod_cast hi)).contDiffAt) hx
  have hθ0 : 0 ≤ s - ⌊s⌋₊ ∨ True := Or.inr trivial
  have hθ1 : ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ) ≤ 1 := by
    have : Real.toNNReal (s - ⌊s⌋₊) ≤ 1 := by
      rw [Real.toNNReal_le_one]
      rcases le_or_gt 0 s with hs | hs
      · linarith [Nat.lt_floor_add_one s]
      · rw [Nat.floor_eq_zero.2 (by linarith)]; simp; linarith
    exact_mod_cast this
  have hB : HolderOnWith (Real.toNNReal (A * (1 + (b - a)))) (Real.toNNReal (s - ⌊s⌋₊))
      (iteratedDerivWithin ⌊s⌋₊ g I) I := by
    refine c03_aux_holderOnWith_of_dist fun x hx y hy => ?_
    rw [heq k le_rfl x hx, heq k le_rfl y hy, Real.coe_toNNReal _ (by positivity)]
    have hd : Differentiable ℝ (iteratedDeriv k g) :=
      hg.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
    have hmv := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := iteratedDeriv k g) (f' := fun t => iteratedDeriv (k + 1) g t) (C := A)
      (fun t _ => by
        have := (hd t).hasDerivAt
        rw [← iteratedDeriv_succ] at this
        exact this.hasDerivWithinAt) (fun t ht => hA (k + 1) le_rfl t ht) hy hx
    rw [← dist_eq_norm, ← dist_eq_norm] at hmv
    set θr := ((Real.toNNReal (s - ⌊s⌋₊) : ℝ≥0) : ℝ)
    have hθr0 : 0 ≤ θr := NNReal.coe_nonneg _
    have hdd : dist x y ≤ b - a := by
      rw [Real.dist_eq, abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have key : dist x y ≤ (1 + (b - a)) * dist x y ^ θr := by
      rcases le_or_gt (dist x y) 1 with h1 | h1
      · calc dist x y = dist x y ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ dist x y ^ θr := Real.rpow_le_rpow_of_exponent_ge' dist_nonneg h1 hθr0 hθ1
          _ ≤ (1 + (b - a)) * dist x y ^ θr := le_mul_of_one_le_left (by positivity)
              (by linarith)
      · have : 1 ≤ dist x y ^ θr := Real.one_le_rpow h1.le hθr0
        nlinarith
    calc dist (iteratedDeriv k g x) (iteratedDeriv k g y) ≤ A * dist x y := hmv
      _ ≤ A * ((1 + (b - a)) * dist x y ^ θr) := mul_le_mul_of_nonneg_left key hA0
      _ = A * (1 + (b - a)) * dist x y ^ θr := by ring
  obtain ⟨hm, hle⟩ := c03_aux_normR_le s I g hgk.contDiffOn (fun _ => A) (fun _ _ => hA0)
    (fun i hi x hx => by rw [heq i hi x hx]; exact hA i (by omega) x hx) _ hB
  refine ⟨hm, hle.trans (le_of_eq ?_)⟩
  rw [Real.coe_toNNReal _ (by positivity), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- Peetre-type inequality. -/
theorem c03_aux_peetre (y z : ℝ) : 1 + |z| ≤ (1 + |y|) * (1 + |y - z|) := by
  have := abs_sub_abs_le_abs_sub z y
  rw [abs_sub_comm] at this
  nlinarith [abs_nonneg y, abs_nonneg (y - z)]


theorem c03_aux_iteratedDeriv_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {x : ℝ} (h : f =ᶠ[𝓝 x] g) (n : ℕ) :
    iteratedDeriv n f x = iteratedDeriv n g x := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  have h' : f =ᶠ[𝓝[univ] x] g := by rw [nhdsWithin_univ]; exact h
  exact h'.iteratedDerivWithin_eq h.eq_of_nhds

/-- Bounds on a compact set for the derivatives of a smooth function. -/
theorem c03_aux_deriv_bound_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → E} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : ℕ) (R : ℝ) :
    ∃ B, 0 ≤ B ∧ ∀ t ∈ Icc (-R) R, ‖iteratedDeriv i φ t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    ((hφ.continuous_iteratedDeriv i (by exact_mod_cast le_top)).continuousOn)
  exact ⟨max B 0, le_max_right _ _, fun t ht => (hB t ht).trans (le_max_left _ _)⟩

/-- The cutoff reciprocal `ψ(t) = (1 - χ(2t))/t`. -/
def c03_aux_farpsi (χ : ℝ → ℝ) (t : ℝ) : ℝ := (1 - χ (2 * t)) / t

/-- The cutoff kernel `ω(t) = (1 - χ(t))/|t|^{p+1}`. -/
def c03_aux_faromega (p : ℝ) (χ : ℝ → ℝ) (t : ℝ) : ℝ := (1 - χ t) / |t| ^ (p + 1)

theorem c03_aux_farpsi_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1) : ContDiff ℝ (⊤ : ℕ∞) (c03_aux_farpsi χ) := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · have h : c03_aux_farpsi χ =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [Icc_mem_nhds (by norm_num : (-1/2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1/2)]
        with u hu
      simp only [c03_aux_farpsi]
      rw [hχ1 (2 * u) ⟨by linarith [hu.1], by linarith [hu.2]⟩]; simp
    exact contDiffAt_const.congr_of_eventuallyEq h
  · exact ((contDiffAt_const.sub ((hχ.comp (contDiff_const.mul contDiff_id)).contDiffAt)).div
      contDiffAt_id ht)

theorem c03_aux_faromega_smooth (p : ℝ) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1) : ContDiff ℝ (⊤ : ℕ∞) (c03_aux_faromega p χ) := by
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  rcases eq_or_ne t 0 with rfl | ht
  · have h : c03_aux_faromega p χ =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
        with u hu
      simp only [c03_aux_faromega]
      rw [hχ1 u hu]; simp
    exact contDiffAt_const.congr_of_eventuallyEq h
  · have habs : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => |u|) t := contDiffAt_abs ht
    have hpow : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => |u| ^ (p + 1)) t :=
      (Real.contDiffAt_rpow_const_of_ne (abs_ne_zero.2 ht)).comp t habs
    exact (contDiffAt_const.sub hχ.contDiffAt).div hpow
      (Real.rpow_pos_of_pos (abs_pos.2 ht) _).ne'


theorem c03_aux_farpsi_decay {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1) (hχ2 : ∀ t, 2 < |t| → χ t = 0) (i : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv i (c03_aux_farpsi χ) t‖ ≤ C * (1 + |t|)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := c03_aux_deriv_bound_compact (c03_aux_farpsi_smooth hχ hχ1) i 1
  refine ⟨2 * B + 2 * (Nat.factorial i), by positivity, fun t => ?_⟩
  have h1t : 0 < 1 + |t| := by positivity
  rcases le_or_gt |t| 1 with ht | ht
  · have := hB t (abs_le.1 ht)
    have h2 : 1 ≤ 2 * (1 + |t|)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ h1t]; linarith
    calc ‖iteratedDeriv i (c03_aux_farpsi χ) t‖ ≤ B := this
      _ ≤ 2 * B * (1 + |t|)⁻¹ := by nlinarith
      _ ≤ (2 * B + 2 * (Nat.factorial i)) * (1 + |t|)⁻¹ := by
          gcongr; have : (0:ℝ) ≤ Nat.factorial i := by positivity
          linarith
  · have hev : c03_aux_farpsi χ =ᶠ[𝓝 t] Inv.inv := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs : IsOpen {u : ℝ | 1 < |u|}).mem_nhds
        (show t ∈ {u : ℝ | 1 < |u|} from ht)] with u hu
      simp only [c03_aux_farpsi, mem_setOf_eq] at hu ⊢
      rw [hχ2 (2 * u) (by rw [abs_mul, abs_two]; linarith)]; simp [div_eq_mul_inv]
    rw [c03_aux_iteratedDeriv_congr hev, iteratedDeriv_eq_iterate, iter_deriv_inv]
    have htpos : 0 < |t| := by linarith
    have hz : |t| ^ (-1 - (i : ℤ)) ≤ |t|⁻¹ := by
      rw [← zpow_neg_one]
      exact zpow_le_zpow_right₀ ht.le (by omega)
    have hinv : |t|⁻¹ ≤ 2 * (1 + |t|)⁻¹ := by
      rw [← div_eq_mul_inv, inv_le_comm₀ htpos (by positivity), inv_div]
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.abs_cast, abs_zpow]
    have hf : (0 : ℝ) ≤ Nat.factorial i := by positivity
    calc (Nat.factorial i : ℝ) * |t| ^ (-1 - (i : ℤ)) ≤ (Nat.factorial i) * (2 * (1 + |t|)⁻¹) :=
          mul_le_mul_of_nonneg_left (hz.trans hinv) hf
      _ ≤ (2 * B + 2 * (Nat.factorial i)) * (1 + |t|)⁻¹ := by
          have : 0 ≤ (1 + |t|)⁻¹ := by positivity
          nlinarith

/-- Bound for the derivatives of `x ↦ x^{-α}` for `x ≥ 1`. -/
theorem c03_aux_rpow_neg_deriv_bound (α : ℝ) (hα : 0 ≤ α) (i : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    |iteratedDeriv i (fun v : ℝ => v ^ (-α)) x| ≤
      |(descPochhammer ℝ i).eval (-α)| * 2 ^ α * (1 + x) ^ (-α) := by
  rw [iteratedDeriv_eq_iterate, iter_deriv_rpow_const, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 : x ^ (-α - i) ≤ x ^ (-α) := Real.rpow_le_rpow_of_exponent_le hx (by
    have : (0 : ℝ) ≤ i := by positivity
    linarith)
  have h2 : x ^ (-α) ≤ ((1 + x) / 2) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h3 : ((1 + x) / 2) ^ (-α) = 2 ^ α * (1 + x) ^ (-α) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      div_eq_mul_inv, inv_inv]; ring
  linarith

theorem c03_aux_faromega_decay (p : ℝ) (hp : 0 < p) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1) (hχ2 : ∀ t, 2 < |t| → χ t = 0) (i : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t, ‖iteratedDeriv i (c03_aux_faromega p χ) t‖ ≤
      C * (1 + |t|) ^ (-(p + 1)) := by
  set α := p + 1
  have hα : 0 ≤ α := by simp only [α]; linarith
  obtain ⟨B, hB0, hB⟩ := c03_aux_deriv_bound_compact (c03_aux_faromega_smooth p hχ hχ1) i 3
  set P := |(descPochhammer ℝ i).eval (-α)| * 2 ^ α
  have hP : 0 ≤ P := by positivity
  refine ⟨B * 4 ^ α + P, by positivity, fun t => ?_⟩
  have h1t : 0 < 1 + |t| := by positivity
  have hw0 : 0 ≤ (1 + |t|) ^ (-α) := Real.rpow_nonneg h1t.le _
  rcases le_or_gt |t| 3 with ht | ht
  · have := hB t (abs_le.1 ht)
    have h4 : 1 ≤ 4 ^ α * (1 + |t|) ^ (-α) := by
      have : (4 : ℝ) ^ (-α) ≤ (1 + |t|) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos h1t (by linarith) (by linarith)
      have e : (4 : ℝ) ^ α * 4 ^ (-α) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) α]
    calc ‖iteratedDeriv i (c03_aux_faromega p χ) t‖ ≤ B := this
      _ ≤ B * (4 ^ α * (1 + |t|) ^ (-α)) := le_mul_of_one_le_right hB0 h4
      _ ≤ (B * 4 ^ α + P) * (1 + |t|) ^ (-α) := by nlinarith
  · rw [Real.norm_eq_abs]
    rcases lt_or_gt_of_ne (show t ≠ 0 by intro h; rw [h] at ht; norm_num at ht) with hneg | hpos
    · have hev : c03_aux_faromega p χ =ᶠ[𝓝 t] fun u => (fun v : ℝ => v ^ (-α)) (-u) := by
        filter_upwards [(isOpen_lt continuous_id continuous_const : IsOpen {u : ℝ | u < -2}).mem_nhds
          (show t ∈ {u : ℝ | u < -2} by
            show t < -2; rw [abs_of_neg hneg] at ht; linarith)] with u hu
        simp only [c03_aux_faromega, mem_setOf_eq, id] at hu ⊢
        rw [hχ2 u (by rw [abs_of_neg (by linarith)]; linarith), abs_of_neg (by linarith),
          Real.rpow_neg (by linarith), div_eq_mul_inv]; ring
      have hcn := iteratedDeriv_comp_neg i (fun v : ℝ => v ^ (-α)) t
      rw [c03_aux_iteratedDeriv_congr hev, hcn, smul_eq_mul, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul]
      have hb := c03_aux_rpow_neg_deriv_bound α hα i (x := -t) (by rw [abs_of_neg hneg] at ht; linarith)
      rw [abs_of_neg hneg]
      calc _ ≤ P * (1 + -t) ^ (-α) := hb
        _ ≤ (B * 4 ^ α + P) * (1 + -t) ^ (-α) := by
            have : 0 ≤ (1 + -t) ^ (-α) := Real.rpow_nonneg (by linarith) _
            have h4 : 0 ≤ B * 4 ^ α := mul_nonneg hB0 (Real.rpow_nonneg (by norm_num) α)
            exact mul_le_mul_of_nonneg_right (by linarith) this
    · have hev : c03_aux_faromega p χ =ᶠ[𝓝 t] fun v : ℝ => v ^ (-α) := by
        filter_upwards [(isOpen_lt continuous_const continuous_id : IsOpen {u : ℝ | 2 < u}).mem_nhds
          (show t ∈ {u : ℝ | 2 < u} by
            show 2 < t; rw [abs_of_pos hpos] at ht; linarith)] with u hu
        simp only [c03_aux_faromega, mem_setOf_eq, id] at hu ⊢
        rw [hχ2 u (by rw [abs_of_pos (by linarith)]; linarith), abs_of_pos (by linarith),
          Real.rpow_neg (by linarith), div_eq_mul_inv]; ring
      rw [c03_aux_iteratedDeriv_congr hev]
      have hb := c03_aux_rpow_neg_deriv_bound α hα i (x := t) (by rw [abs_of_pos hpos] at ht; linarith)
      rw [abs_of_pos hpos]
      calc _ ≤ P * (1 + t) ^ (-α) := hb
        _ ≤ (B * 4 ^ α + P) * (1 + t) ^ (-α) := by
            have : 0 ≤ (1 + t) ^ (-α) := Real.rpow_nonneg (by linarith) _
            have h4 : 0 ≤ B * 4 ^ α := mul_nonneg hB0 (Real.rpow_nonneg (by norm_num) α)
            exact mul_le_mul_of_nonneg_right (by linarith) this


/-- Shifted functions with decaying derivatives: `‖φ(·-z)‖_{C^s([a,b])} ≲ (1+|z|)^{-r}`. -/
theorem c03_aux_shift_holder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℝ)
    {φ : ℝ → E} (hφ : ContDiff ℝ (⌊s⌋₊ + 1) φ) {r C : ℝ} (hr : 0 ≤ r) (hC0 : 0 ≤ C)
    (hdec : ∀ i ≤ ⌊s⌋₊ + 1, ∀ t, ‖iteratedDeriv i φ t‖ ≤ C * (1 + |t|) ^ (-r))
    {a b : ℝ} (hab : a < b) (z : ℝ) :
    (fun y => φ (y - z)) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun y => φ (y - z)) ≤
        ((⌊s⌋₊ + 1) + (1 + (b - a))) * (C * (1 + (|a| + |b|)) ^ r) * (1 + |z|) ^ (-r) := by
  set R1 := |a| + |b|
  set A := C * (1 + R1) ^ r * (1 + |z|) ^ (-r)
  have hA0 : 0 ≤ A := by positivity
  have hg : ContDiff ℝ (⌊s⌋₊ + 1) (fun y => φ (y - z)) := hφ.comp (contDiff_id.sub contDiff_const)
  obtain ⟨hm, hn⟩ := c03_aux_holder_of_derivs s hg hab hA0 (fun i hi x hx => by
    rw [iteratedDeriv_comp_sub_const]
    refine (hdec i hi (x - z)).trans ?_
    have hx1 : 1 + |x| ≤ 1 + R1 := by
      have : |x| ≤ |a| + |b| := by
        rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
          linarith [hx.1, hx.2]
      linarith
    have hp := c03_aux_peetre x z
    have h1 : 0 < 1 + |x - z| := by positivity
    have h2 : 0 < 1 + |x| := by positivity
    have h3 : (1 + |x - z|) ^ (-r) ≤ (1 + R1) ^ r * (1 + |z|) ^ (-r) := by
      have h4 : (1 + |z|) / (1 + |x|) ≤ 1 + |x - z| := by
        rw [div_le_iff₀ h2]; linarith
      calc (1 + |x - z|) ^ (-r) ≤ ((1 + |z|) / (1 + |x|)) ^ (-r) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h4 (by linarith)
        _ = (1 + |x|) ^ r * (1 + |z|) ^ (-r) := by
            rw [Real.div_rpow (by positivity) h2.le, Real.rpow_neg h2.le, div_eq_mul_inv, inv_inv]
            ring
        _ ≤ (1 + R1) ^ r * (1 + |z|) ^ (-r) := by
            gcongr
    calc C * (1 + |x - z|) ^ (-r) ≤ C * ((1 + R1) ^ r * (1 + |z|) ^ (-r)) :=
          mul_le_mul_of_nonneg_left h3 hC0
      _ = A := by simp only [A]; ring)
  exact ⟨hm, hn.trans (le_of_eq (by simp only [A]; ring))⟩


/-- `y ↦ f(y) - f(z)` on `[a,b]`: `‖·‖_{C^s} ≲ K(|a|+|b|+|z|) + K + ‖f'‖_{C^s([a,b])}`. -/
theorem c03_aux_far_u (s : ℝ) {f : ℝ → ℝ} (hf1 : ContDiff ℝ (⌊s⌋₊ + 1) f) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, |deriv f x| ≤ K) {a b : ℝ} (hab : a < b)
    (hfI : deriv f ∈ c03_holder s (Icc a b)) (z : ℝ) :
    (fun y => f y - f z) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun y => f y - f z) ≤
        ((⌊s⌋₊ + 1) + (1 + (b - a))) *
          (K * (|a| + |b| + |z|) + K + c03_holder_normR s (Icc a b) (deriv f)) := by
  set k := ⌊s⌋₊
  set I := Icc a b
  set N := c03_holder_normR s I (deriv f)
  have hN0 : 0 ≤ N := c03_aux_normR_nonneg _ _ _
  have hU : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have hf1' : ContDiff ℝ 1 f := hf1.of_le (by exact_mod_cast Nat.le_add_left 1 k)
  have hfk : ContDiff ℝ k (deriv f) := by
    have := hf1.iterate_deriv' k 1
    simpa using this
  set A := K * (|a| + |b| + |z|) + K + N
  have hA0 : 0 ≤ A := by positivity
  have hg : ContDiff ℝ (k + 1) (fun y => f y - f z) := hf1.sub contDiff_const
  obtain ⟨hm, hn⟩ := c03_aux_holder_of_derivs s hg hab hA0 (fun i hi x hx => by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [iteratedDeriv_zero, Real.norm_eq_abs]
      have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := f) (f' := deriv f) (C := K)
        (fun u _ => ((hf1'.differentiable one_ne_zero) u).hasDerivAt.hasDerivWithinAt)
        (fun u _ => by rw [Real.norm_eq_abs]; exact hK u) (mem_univ z) (mem_univ x)
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
      have hxz : |x - z| ≤ |a| + |b| + |z| := by
        have : |x| ≤ |a| + |b| := by
          rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
            linarith [hx.1, hx.2]
        have := abs_sub x z
        linarith
      calc |f x - f z| ≤ K * |x - z| := hmv
        _ ≤ K * (|a| + |b| + |z|) := mul_le_mul_of_nonneg_left hxz hK0
        _ ≤ A := by simp only [A]; linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have e : iteratedDeriv (j + 1) (fun y => f y - f z) x = iteratedDeriv j (deriv f) x := by
        rw [iteratedDeriv_fun_sub ((hf1.of_le (by exact_mod_cast hi)).contDiffAt)
          contDiffAt_const, iteratedDeriv_const, if_neg (by omega), sub_zero, iteratedDeriv_succ']
      rw [e, ← iteratedDerivWithin_eq_iteratedDeriv hU
        ((hfk.of_le (by exact_mod_cast (show j ≤ k by omega))).contDiffAt) hx]
      have hNA : N ≤ A := by
        have h1 : 0 ≤ K * (|a| + |b| + |z|) := by positivity
        simp only [A]; linarith
      exact (c03_aux_le_normR hfI (by omega) hx).trans hNA)
  exact ⟨hm, hn.trans (le_of_eq (by ring))⟩


/-- Uniform constant for finitely many derivative bounds. -/
theorem c03_aux_uniform_const {P : ℕ → ℝ → Prop} (hmono : ∀ i C C', C ≤ C' → P i C → P i C')
    (h : ∀ i, ∃ C, 0 ≤ C ∧ P i C) (N : ℕ) : ∃ C, 0 ≤ C ∧ ∀ i ≤ N, P i C := by
  choose C hC0 hC using h
  refine ⟨∑ i ∈ Finset.range (N + 1), C i, Finset.sum_nonneg fun i _ => hC0 i, fun i hi => ?_⟩
  exact hmono i _ _ (Finset.single_le_sum (f := C) (fun j _ => hC0 j)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))) (hC i)

/-- The far secant replacement `V_z(y) = (f(y)-f(z)) ψ(y-z)`: uniformly bounded in `C^s([a,b])`. -/
theorem c03_aux_far_V (s : ℝ) (hs : 0 < s) (hsN : ∀ n : ℕ, s ≠ n) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1)
    (hχ2 : ∀ t, 2 < |t| → χ t = 0) (hχ01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (K N : ℝ) (hK0 : 0 ≤ K)
    (hN0 : 0 ≤ N) {a b : ℝ} (hab : a < b) :
    ∃ CV, 0 ≤ CV ∧ ∀ f : ℝ → ℝ, ContDiff ℝ (⌊s⌋₊ + 1) f → (∀ x, |deriv f x| ≤ K) →
      deriv f ∈ c03_holder s (Icc a b) → c03_holder_normR s (Icc a b) (deriv f) ≤ N → ∀ z : ℝ,
      (fun y => (f y - f z) * c03_aux_farpsi χ (y - z)) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun y => (f y - f z) * c03_aux_farpsi χ (y - z)) ≤ CV ∧
      ∀ y, |(f y - f z) * c03_aux_farpsi χ (y - z)| ≤ K := by
  set k := ⌊s⌋₊
  set I := Icc a b
  set ℓ := min (b - a) 1
  have hℓ0 : 0 < ℓ := lt_min (by linarith) one_pos
  obtain ⟨Cp, hCp0, hCp⟩ := c03_holder_product_tame_len s hs hsN ℓ hℓ0 (min_le_right _ _)
  obtain ⟨Cψ, hCψ0, hCψ⟩ := c03_aux_uniform_const
    (P := fun i C => ∀ t, ‖iteratedDeriv i (c03_aux_farpsi χ) t‖ ≤ C * (1 + |t|) ^ (-(1:ℝ)))
    (fun i C C' hCC' h t => (h t).trans (mul_le_mul_of_nonneg_right hCC' (by positivity)))
    (fun i => by
      obtain ⟨C, hC0, hC⟩ := c03_aux_farpsi_decay hχ hχ1 hχ2 i
      exact ⟨C, hC0, fun t => by rw [Real.rpow_neg_one]; exact hC t⟩) (k + 1)
  set R1 := |a| + |b|
  set cΨ := ((k + 1) + (1 + (b - a))) * (Cψ * (1 + R1) ^ (1 : ℝ))
  set cU := ((k + 1) + (1 + (b - a))) * (K * R1 + K + N + K)
  have hcΨ : 0 ≤ cΨ := by positivity
  have hcU : 0 ≤ cU := by positivity
  refine ⟨Cp * (2 * (cU * cΨ)), by positivity, ?_⟩
  intro f hf1 hK hfI hfN z
  have hz1 : 0 < 1 + |z| := by positivity
  -- the two factors (complexified)
  obtain ⟨hu, hun⟩ := c03_aux_far_u s hf1 hK0 hK hab hfI z
  have hun' : c03_holder_normR s I (fun y => f y - f z) ≤ cU * (1 + |z|) := by
    refine hun.trans ?_
    simp only [cU]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : 0 ≤ (K * R1 + K + N) * |z| := by positivity
    have e : (K * R1 + K + N + K) * (1 + |z|) - (K * (|a| + |b| + |z|) + K + N) =
        K + (K * R1 + K + N) * |z| := by simp only [R1]; ring
    linarith
  obtain ⟨hψ, hψn⟩ := c03_aux_shift_holder (E := ℝ) s
    ((c03_aux_farpsi_smooth hχ hχ1).of_le (by exact_mod_cast le_top)) zero_le_one hCψ0 hCψ hab z
  have hψn' : c03_holder_normR s I (fun y => c03_aux_farpsi χ (y - z)) ≤ cΨ * (1 + |z|)⁻¹ := by
    refine hψn.trans (le_of_eq ?_); rw [Real.rpow_neg_one]
  obtain ⟨hU, hUn, hUs⟩ := c03_aux_holder_clm_norm hab Complex.ofRealCLM
    (by rw [Complex.ofRealCLM_norm]) hu
  obtain ⟨hΨ, hΨn, hΨs⟩ := c03_aux_holder_clm_norm hab Complex.ofRealCLM
    (by rw [Complex.ofRealCLM_norm]) hψ
  obtain ⟨hP, hPn⟩ := hCp a b (min_le_left _ _) _ _ hU hΨ
  obtain ⟨hR, hRn, -⟩ := c03_aux_holder_clm_norm hab Complex.reCLM (by rw [Complex.reCLM_norm]) hP
  have hre : (fun x => Complex.reCLM (((fun y => Complex.ofRealCLM (f y - f z)) *
      (fun y => Complex.ofRealCLM (c03_aux_farpsi χ (y - z)))) x)) =
      fun y => (f y - f z) * c03_aux_farpsi χ (y - z) := by
    funext x; simp [Complex.ofRealCLM_apply]
  rw [hre] at hR hRn
  refine ⟨hR, hRn.trans (hPn.trans ?_), fun y => ?_⟩
  · -- `Cp (sup U ‖Ψ‖ + sup Ψ ‖U‖) ≤ 2 Cp ‖U‖ ‖Ψ‖`
    set nU := c03_holder_normR s I (fun y => f y - f z)
    set nΨ := c03_holder_normR s I (fun y => c03_aux_farpsi χ (y - z))
    have h1 := (hUs.trans (c03_aux_supNorm_le_normR hu))
    have h2 := (hΨs.trans (c03_aux_supNorm_le_normR hψ))
    have hnU0 := c03_aux_normR_nonneg s I (fun y => f y - f z)
    have hnΨ0 := c03_aux_normR_nonneg s I (fun y => c03_aux_farpsi χ (y - z))
    have hs1 := c03_aux_supNorm_nonneg I (fun y => Complex.ofRealCLM (f y - f z))
    have hs2 := c03_aux_supNorm_nonneg I (fun y => Complex.ofRealCLM (c03_aux_farpsi χ (y - z)))
    have hprod : nU * nΨ ≤ cU * cΨ := by
      calc nU * nΨ ≤ (cU * (1 + |z|)) * (cΨ * (1 + |z|)⁻¹) :=
            mul_le_mul hun' hψn' hnΨ0 (by positivity)
        _ = cU * cΨ := by field_simp
    have e1 : c03_holder_supNorm I (fun y => Complex.ofRealCLM (f y - f z)) *
        c03_holder_normR s I (fun y => Complex.ofRealCLM (c03_aux_farpsi χ (y - z))) ≤ nU * nΨ :=
      mul_le_mul h1 hΨn (c03_aux_normR_nonneg _ _ _) hnU0
    have e2 : c03_holder_supNorm I (fun y => Complex.ofRealCLM (c03_aux_farpsi χ (y - z))) *
        c03_holder_normR s I (fun y => Complex.ofRealCLM (f y - f z)) ≤ nU * nΨ := by
      rw [mul_comm nU]; exact mul_le_mul h2 hUn (c03_aux_normR_nonneg _ _ _) hnΨ0
    exact mul_le_mul_of_nonneg_left (by linarith) hCp0.le
  · -- pointwise bound
    rcases eq_or_ne y z with rfl | hyz
    · simp [c03_aux_farpsi]; exact hK0
    have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := deriv f) (C := K)
      (fun u _ => (((hf1.of_le (by exact_mod_cast Nat.le_add_left 1 k)).differentiable
        one_ne_zero) u).hasDerivAt.hasDerivWithinAt)
      (fun u _ => by rw [Real.norm_eq_abs]; exact hK u) (mem_univ z) (mem_univ y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hyz' : 0 < |y - z| := abs_pos.2 (sub_ne_zero.2 hyz)
    simp only [c03_aux_farpsi, abs_mul, abs_div]
    have hχb : |1 - χ (2 * (y - z))| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hχ01 (2 * (y - z))]
    calc |f y - f z| * (|1 - χ (2 * (y - z))| / |y - z|) ≤ (K * |y - z|) * (1 / |y - z|) := by
          gcongr
      _ = K := by field_simp


/-- Per-`z` estimate for the far integrand on `[a,b]`. -/
theorem c03_aux_far_slice (p ε s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1) (hχ2 : ∀ t, 2 < |t| → χ t = 0)
    (hχ01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (K N : ℝ) (hK0 : 0 ≤ K) (hN0 : 0 ≤ N) {a b : ℝ}
    (hab : a < b) :
    ∃ CH, 0 ≤ CH ∧ ∀ f : ℝ → ℝ, ContDiff ℝ (⌊s⌋₊ + 1) f → (∀ x, |deriv f x| ≤ K) →
      deriv f ∈ c03_holder s (Icc a b) → c03_holder_normR s (Icc a b) (deriv f) ≤ N → ∀ z : ℝ,
      (fun y => (((1 - χ (y - z)) * c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) /
        |y - z| ^ (p + 1) : ℝ) : ℂ)) ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (fun y => (((1 - χ (y - z)) *
        c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) / |y - z| ^ (p + 1) : ℝ) : ℂ)) ≤
        CH * (1 + |z|) ^ (-(p + 1)) := by
  set k := ⌊s⌋₊
  set I := Icc a b
  set ℓ := min (b - a) 1
  have hℓ0 : 0 < ℓ := lt_min (by linarith) one_pos
  have hℓab : ℓ ≤ b - a := min_le_left _ _
  set K' := max K 1
  have hK' : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨CV, hCV0, hV⟩ := c03_aux_far_V s hs hsN hχ hχ1 hχ2 hχ01 K N hK0 hN0 hab
  set Gc : ℝ × ℝ → ℂ := fun q => ((c03_Gamma_eps p ε q.1 q.2 : ℝ) : ℂ)
  have hGc : ContDiff ℝ (⊤ : ℕ∞) Gc :=
    Complex.ofRealCLM.contDiff.comp (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.1
  obtain ⟨MG, hMG0, hMG⟩ := c03_aux_G_bound Gc hGc (k + 2) K'
  obtain ⟨Cc, hCc0, hCc⟩ := c03_aux_comp_len s hs hsN ℓ hℓ0 (min_le_right _ _) K' MG hK' hMG0
  obtain ⟨Cp, hCp0, hCp⟩ := c03_holder_product_tame_len s hs hsN ℓ hℓ0 (min_le_right _ _)
  obtain ⟨Cω, hCω0, hCω⟩ := c03_aux_uniform_const
    (P := fun i C => ∀ t, ‖iteratedDeriv i (c03_aux_faromega p χ) t‖ ≤ C * (1 + |t|) ^ (-(p + 1)))
    (fun i C C' hCC' h t => (h t).trans (mul_le_mul_of_nonneg_right hCC' (by positivity)))
    (fun i => c03_aux_faromega_decay p hp hχ hχ1 hχ2 i) (k + 1)
  set cω := ((k + 1) + (1 + (b - a))) * (Cω * (1 + (|a| + |b|)) ^ (p + 1))
  have hcω : 0 ≤ cω := by positivity
  set AΓ := Cc * (1 + N + CV) ^ (k + 1)
  have hAΓ : 0 ≤ AΓ := by positivity
  refine ⟨Cp * cω * (MG + AΓ), by positivity, ?_⟩
  intro f hf1 hK hfI hfN z
  set w := (1 + |z|) ^ (-(p + 1))
  have hw : 0 ≤ w := by positivity
  obtain ⟨hVm, hVn, hVb⟩ := hV f hf1 hK hfI hfN z
  set V := fun y => (f y - f z) * c03_aux_farpsi χ (y - z)
  -- `Γ(f', V)`
  obtain ⟨hΓm, hΓn⟩ := hCc a b hℓab Gc hGc hMG (deriv f) V hfI hVm
    (fun x _ => ⟨(hK x).trans (le_max_left _ _), (hVb x).trans (le_max_left _ _)⟩)
  have hΓn' : c03_holder_normR s I (fun x => Gc (deriv f x, V x)) ≤ AΓ := by
    refine hΓn.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) hCc0.le)
    · have := c03_aux_normR_nonneg s I (deriv f); have := c03_aux_normR_nonneg s I V; linarith
    · linarith
  have hΓs : c03_holder_supNorm I (fun x => Gc (deriv f x, V x)) ≤ MG := by
    refine c03_aux_supNorm_le hMG0 fun x _ => ?_
    have := hMG 0 (by omega) (deriv f x, V x)
      ⟨abs_le.1 ((hK x).trans (le_max_left _ _)), abs_le.1 ((hVb x).trans (le_max_left _ _))⟩
    rwa [norm_iteratedFDeriv_zero] at this
  -- `ω(· - z)`
  obtain ⟨hω, hωn⟩ := c03_aux_shift_holder (E := ℝ) s
    ((c03_aux_faromega_smooth p hχ hχ1).of_le (by exact_mod_cast le_top)) (by linarith) hCω0 hCω
    hab z
  obtain ⟨hωc, hωcn, hωcs⟩ := c03_aux_holder_clm_norm hab Complex.ofRealCLM
    (by rw [Complex.ofRealCLM_norm]) hω
  have hωn' : c03_holder_normR s I (fun y => Complex.ofRealCLM (c03_aux_faromega p χ (y - z))) ≤
      cω * w := hωcn.trans hωn
  have hωs' : c03_holder_supNorm I (fun y => Complex.ofRealCLM (c03_aux_faromega p χ (y - z))) ≤
      cω * w := (c03_aux_supNorm_le_normR hωc).trans hωn'
  obtain ⟨hPm, hPn⟩ := hCp a b hℓab _ _ hΓm hωc
  -- identification
  have hid : ∀ y, (((1 - χ (y - z)) * c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) /
      |y - z| ^ (p + 1) : ℝ) : ℂ) = ((fun x => Gc (deriv f x, V x)) *
        fun y => Complex.ofRealCLM (c03_aux_faromega p χ (y - z))) y := by
    intro y
    simp only [Pi.mul_apply, Gc, Complex.ofRealCLM_apply, c03_aux_faromega]
    rcases le_or_gt |y - z| 1 with h1 | h1
    · rw [hχ1 (y - z) (abs_le.1 h1)]; simp
    · have hyz : y ≠ z := by intro h; rw [h, sub_self, abs_zero] at h1; linarith
      have hsec : c01_secant f y z = V y := by
        simp only [c01_secant, if_neg hyz, V, c03_aux_farpsi]
        rw [hχ2 (2 * (y - z)) (by rw [abs_mul, abs_two]; linarith)]
        field_simp [sub_ne_zero.2 hyz]
        ring
      rw [hsec]; push_cast; ring
  have hcg := c03_aux_holder_congr (s := s) (I := I) (fun y _ => hid y)
  refine ⟨hcg.2.1.2 hPm, ?_⟩
  rw [hcg.2.2.1]
  refine hPn.trans ?_
  have h1 : c03_holder_supNorm I (fun x => Gc (deriv f x, V x)) *
      c03_holder_normR s I (fun y => Complex.ofRealCLM (c03_aux_faromega p χ (y - z))) ≤
      MG * (cω * w) := mul_le_mul hΓs hωn' (c03_aux_normR_nonneg _ _ _) hMG0
  have h2 : c03_holder_supNorm I (fun y => Complex.ofRealCLM (c03_aux_faromega p χ (y - z))) *
      c03_holder_normR s I (fun x => Gc (deriv f x, V x)) ≤ (cω * w) * AΓ :=
    mul_le_mul hωs' hΓn' (c03_aux_normR_nonneg _ _ _) (by positivity)
  calc Cp * (c03_holder_supNorm I (fun x => Gc (deriv f x, V x)) *
        c03_holder_normR s I (fun y => Complex.ofRealCLM (c03_aux_faromega p χ (y - z))) +
        c03_holder_supNorm I (fun y => Complex.ofRealCLM (c03_aux_faromega p χ (y - z))) *
        c03_holder_normR s I (fun x => Gc (deriv f x, V x)))
      ≤ Cp * (MG * (cω * w) + (cω * w) * AΓ) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCp0.le
    _ = Cp * cω * (MG + AΓ) * w := by ring


theorem c03_aux_kernel_meas (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) {χ : ℝ → ℝ}
    (hχ : Continuous χ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Measurable (fun q : ℝ × ℝ => (1 - χ (q.1 - q.2)) * c03_Gamma_eps p ε (deriv f q.1)
      (c01_secant f q.1 q.2) / |q.1 - q.2| ^ (p + 1)) := by
  have hfd : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hsec : Measurable (fun q : ℝ × ℝ => c01_secant f q.1 q.2) := by
    have h1 : Measurable (fun q : ℝ × ℝ => deriv f q.1) := hfd.measurable.comp measurable_fst
    have hfm : Measurable f := hf.continuous.measurable
    have h2 : Measurable (fun q : ℝ × ℝ => (f q.1 - f q.2) / (q.1 - q.2)) := by fun_prop
    have h3 : MeasurableSet {q : ℝ × ℝ | q.1 = q.2} := measurableSet_eq_fun measurable_fst measurable_snd
    exact Measurable.ite h3 h1 h2
  have hΓc : Measurable (fun r : ℝ × ℝ => c03_Gamma_eps p ε r.1 r.2) :=
    (c03_Gamma_eps_smooth p ε hp hp1 hε).2.2.2.1.continuous.measurable
  have hpair : Measurable (fun q : ℝ × ℝ => (deriv f q.1, c01_secant f q.1 q.2)) :=
    (hfd.measurable.comp measurable_fst).prodMk hsec
  have hΓm : Measurable (fun q : ℝ × ℝ => c03_Gamma_eps p ε (deriv f q.1) (c01_secant f q.1 q.2)) := by
    have h := hΓc.comp hpair
    simp only [Function.comp_def] at h
    exact h
  have hχm : Measurable (fun q : ℝ × ℝ => 1 - χ (q.1 - q.2)) :=
    measurable_const.sub (hχ.measurable.comp (measurable_fst.sub measurable_snd))
  have hdm : Measurable (fun q : ℝ × ℝ => |q.1 - q.2| ^ (p + 1)) :=
    (continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)).pow_const (p + 1)
  exact (hχm.mul hΓm).div hdm

theorem c03_aux_far_core (p ε s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ t ∈ Icc (-1 : ℝ) 1, χ t = 1) (hχ2 : ∀ t, 2 < |t| → χ t = 0)
    (hχ01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (K N : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ C, 0 < C ∧ ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
      (∀ x, |deriv f x| ≤ K) → c03_holder_normR s (Icc a b) (deriv f) ≤ N →
      c03_I_far_op p ε χ f ∈ c03_holder s (Icc a b) ∧
      c03_holder_normR s (Icc a b) (c03_I_far_op p ε χ f) ≤ C := by
  set K' := max K 0
  set N' := max N 0
  obtain ⟨CH, hCH0, hCH⟩ := c03_aux_far_slice p ε s hp hp1 hε hs hsN hχ hχ1 hχ2 hχ01 K' N'
    (le_max_right _ _) (le_max_right _ _) hab
  set ψ : ℝ → ℝ := fun z => CH * (1 + |z|) ^ (-(p + 1))
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => by positivity
  have hψi : Integrable ψ := by
    have h : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(p + 1))) volume :=
      integrable_one_add_norm (by simp; linarith)
    simpa [ψ, Real.norm_eq_abs] using h.const_mul CH
  refine ⟨(∫ z, ψ z) + 1, by have := integral_nonneg (μ := volume) hψ0; linarith, ?_⟩
  intro f hf hf' hK hN
  obtain ⟨hf1c, -, -⟩ := hf
  have hfk : ContDiff ℝ ⌊s⌋₊ (deriv f) := contDiffOn_univ.1 hf'.1
  have hf1 : ContDiff ℝ (⌊s⌋₊ + 1) f :=
    contDiff_succ_iff_deriv.2 ⟨hf1c.differentiable one_ne_zero, by simp, hfk⟩
  have hfI : deriv f ∈ c03_holder s (Icc a b) := hf'.2 _ _ (subset_univ _)
  have hper := hCH f hf1 (fun x => (hK x).trans (le_max_left _ _)) hfI
    (hN.trans (le_max_left _ _))
  obtain ⟨hm, hn⟩ := c03_aux_param_real s hs hsN hab (fun y z => (1 - χ (y - z)) *
    c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) / |y - z| ^ (p + 1))
    (c03_aux_kernel_meas p ε hp hp1 hε hχ.continuous hf1c) ψ hψ0 hψi hper
  exact ⟨hm, hn.trans (by linarith)⟩


-- Encoding: `C` depends on `(s,R,ε,α,‖f'‖_∞,‖f'‖_{C^s})` and also on the fixed cutoff `χ` (through `(1-χ(y-z))`), so `χ` is
-- quantified before `∃ C`.
/-- Blueprint: lem:c03_I_far.  `ℐ^far_ε(f) = ℐ_ε(f) - ℐ^near_ε(f) ∈ C^s_loc` with
`‖ℐ^far_ε(f)‖_{C^s([-R,R])} ≤ C(s,R,ε,α,χ, K ≥ ‖f'‖_∞, M ≥ ‖f'‖_{C^s([-R,R])})`. -/
theorem c03_I_far (p ε s : ℝ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 ≤ ε) (hs : 0 < s)
    (hsN : ∀ n : ℕ, s ≠ n) (χ : ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχ1 : ∀ t ∈ Icc (-1) 1, χ t = 1)
    (hχ2 : ∀ t, 2 < |t| → χ t = 0) (hχ01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) :
    (∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
      (∀ y, c03_I_far_op p ε χ f y = c03_I_eps p ε f y - c03_I_near_op p ε χ f y) ∧
      c03_I_far_op p ε χ f ∈ c03_holder_loc s univ) ∧
    ∀ R K M : ℝ, 0 < R → ∃ C, 0 < C ∧
      ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
      (∀ x, |deriv f x| ≤ K) → c03_holder_normR s (Icc (-R) R) (deriv f) ≤ M →
      c03_holder_normR s (Icc (-R) R) (c03_I_far_op p ε χ f) ≤ C := by
  have hmem : ∀ f : ℝ → ℝ, f ∈ c01_admissible_class → deriv f ∈ c03_holder_loc s univ →
      ∀ a b : ℝ, a < b → c03_I_far_op p ε χ f ∈ c03_holder s (Icc a b) := by
    intro f hf hf' a b hab
    obtain ⟨-, ⟨K, hK⟩, -⟩ := id hf
    obtain ⟨C, -, hC⟩ := c03_aux_far_core p ε s hp hp1 hε hs hsN hχ hχ1 hχ2 hχ01 K
      (c03_holder_normR s (Icc a b) (deriv f)) hab
    exact (hC f hf hf' hK le_rfl).1
  refine ⟨fun f hf hf' => ⟨fun y => ?_, ?_⟩, fun R K M hR => ?_⟩
  · -- the splitting identity
    obtain ⟨hf1c, -, -⟩ := id hf
    have hwd := (c03_I_well_defined p ε hp hp1 hε f hf).2.2.2.2.1 y
    have hm0 := c03_aux_kernel_meas p ε hp hp1 hε (χ := fun _ => (0 : ℝ)) continuous_const hf1c
    simp only [sub_zero, one_mul] at hm0
    have hmy : Measurable (fun z => c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) /
        |y - z| ^ (p + 1)) := by
      have h := hm0.comp (measurable_prodMk_left (x := y))
      simp only [Function.comp_def] at h
      exact h
    have hΓi : Integrable (fun z => c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) /
        |y - z| ^ (p + 1)) := by
      refine hwd.mono' hmy.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    set g : ℝ → ℝ := fun z => χ (y - z) * c03_Gamma_eps p ε (deriv f y) (c01_secant f y z) /
      |y - z| ^ (p + 1)
    have hgm : Measurable g := by
      have := c03_aux_kernel_meas p ε hp hp1 hε (χ := fun t => 1 - χ t)
        (continuous_const.sub hχ.continuous) hf1c
      simp only [sub_sub_cancel] at this
      have h := this.comp (measurable_prodMk_left (x := y))
      simp only [Function.comp_def] at h
      exact h
    have hgi : Integrable g := by
      refine hwd.mono' hgm.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      simp only [g, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (y - z)) (p + 1))]
      have h1 : |χ (y - z)| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hχ01 (y - z)]
      gcongr
      exact mul_le_of_le_one_left (abs_nonneg _) h1
    have hnear : c03_I_near_op p ε χ f y = ∫ z, g z := by
      unfold c03_I_near_op
      rw [← integral_sub_left_eq_self g (μ := volume) y]
      congr 1; funext t
      simp only [g, sub_sub_cancel]
    rw [hnear]
    unfold c03_I_far_op c03_I_eps
    rw [← integral_sub hΓi hgi]
    congr 1; funext z
    simp only [g]; ring
  · have hcd : ContDiff ℝ ⌊s⌋₊ (c03_I_far_op p ε χ f) := by
      refine contDiff_iff_contDiffAt.2 fun x => ?_
      have h := hmem f hf hf' (x - 1) (x + 1) (by linarith)
      exact h.1.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
    refine ⟨hcd.contDiffOn, fun a b _ => ?_⟩
    rcases lt_or_ge a b with hab | hab
    · exact hmem f hf hf' a b hab
    · exact c03_aux_holder_degen s a b hab _ hcd.contDiffOn
  · obtain ⟨C, hC0, hC⟩ := c03_aux_far_core p ε s hp hp1 hε hs hsN hχ hχ1 hχ2 hχ01 K M
      (show -R < R by linarith)
    exact ⟨C, hC0, fun f hf hf' hK hM => (hC f hf hf' hK hM).2⟩


/-! ## Smoothness of profiles: the linear gain and the bootstrap -/


-- Encoding: `GSQG/Definitions` defines `|D|^p` (`fracD`) by the singular integral with the constant
-- `c_α = calpha p`; the identity `c_p = c_α` (last-but-one conjunct) makes explicit that this
-- agrees with the Fourier multiplier `|ξ|^p` ("as in def:frac_multiplier").
/-- Blueprint: lem:c03_frac_kernel_formula.  `c_p ∫ (1-e^{iλz})/|z|^{1+p} dz = |λ|^p`, and
`|D|^p g(y) = c_p ∫ (g(y)-g(y+z))/|z|^{1+p} dz` for Schwartz `g` (Fourier side) and for bounded
`C¹` functions with bounded derivative (the shared `fracD`). -/
theorem c03_frac_kernel_formula (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Integrable (fun z : ℝ => (1 - Real.cos z) / |z| ^ (1 + p)) ∧ 0 < c03_cp p ∧
    (∀ lam : ℝ, Integrable (fun z : ℝ =>
        (1 - Complex.exp (Complex.I * lam * z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
      (c03_cp p : ℂ) * ∫ z : ℝ, (1 - Complex.exp (Complex.I * lam * z)) /
        ((|z| ^ (1 + p) : ℝ) : ℂ) = ((|lam| ^ p : ℝ) : ℂ)) ∧
    (∀ g : SchwartzMap ℝ ℂ, ∀ y : ℝ,
      fourierMultiplier (fun ξ => ((|ξ| ^ p : ℝ) : ℂ)) (⇑g) y =
        (c03_cp p : ℂ) * ∫ z : ℝ, (g y - g (y + z)) / ((|z| ^ (1 + p) : ℝ) : ℂ)) ∧
    c03_cp p = calpha p ∧
    (∀ g : ℝ → ℝ, ContDiff ℝ 1 g → (∃ M, ∀ x, |g x| ≤ M) → (∃ M, ∀ x, |deriv g x| ≤ M) →
      ∀ y, Integrable (fun z => (g y - g (y + z)) / |z| ^ (1 + p)) ∧
        fracD p g y = c03_cp p * ∫ z, (g y - g (y + z)) / |z| ^ (1 + p)) := by
  apply c03c_c03_frac_kernel_formula <;> assumption

-- The Schauder estimate, the linear gain and the smoothness bootstrap are in
-- `GSQG/Sec4_Analysis/Smoothness.lean`, downstream of the `SchauderEstimate/` proof of `c03_schauder_RS`.

end GSQG
