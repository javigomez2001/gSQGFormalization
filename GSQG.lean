/-
Lean 4 formalization of J. Gómez-Serrano and M. Pasquariello,
"Self-Similar Solutions for the gSQG patch equations" (manuscript: `paper/gsqg_Nov26.tex`).

The modules follow the sections of the paper. `docs/PAPER_MAP.md` lists every numbered statement
of the paper with its Lean declaration.
-/

-- Shared definitions (equation, operators, function spaces, approximate family, statements)
import GSQG.Definitions
import GSQG.Auxiliary.SpecialIntegrals

-- §1–2  Introduction and setup: self-similar reduction; the geometric front equation
import GSQG.Sec1_Introduction.SelfSimilarReduction
import GSQG.Sec1_Introduction.GeometricFrontEquation

-- §3  Fixed point argument: Theorems 3.1–3.4 and the proof of Theorem 1.1
import GSQG.Sec3_FixedPoint.FixedPointArgument
import GSQG.Sec3_FixedPoint.MainTheorem

-- §4  Analysis of the equation: Proposition 4.1, Lemma 4.3, Theorem 3.5 (smoothness)
import GSQG.Sec4_Analysis.Equation
import GSQG.Sec4_Analysis.Smoothness

-- §5  Construction of the approximate solution: Lemma 5.1 – Proposition 5.18
import GSQG.Sec5_ApproximateSolution.OscillatoryIntegrals
import GSQG.Sec5_ApproximateSolution.FamilyAndE1toE4
import GSQG.Sec5_ApproximateSolution.E5
import GSQG.Sec5_ApproximateSolution.E6toE9
import GSQG.Sec5_ApproximateSolution.ResidualBounds

-- §6  Linear inverse: Lemma 6.1 – Proposition 6.14
import GSQG.Sec6_LinearInverse.ConjugationAndLowFrequency
import GSQG.Sec6_LinearInverse.HighFrequency

-- §7  Nonlinear estimates: Definition 7.1 – Proposition 7.5
import GSQG.Sec7_NonlinearEstimates.NonlinearEstimates

-- Appendices A and B: Propositions A.1–A.2, Lemmas B.1–B.5 (statements and supporting toolbox)
import GSQG.AppendixAB.Statements
import GSQG.AppendixAB.PhaseToolbox
import GSQG.AppendixAB.SymbolCalculus
import GSQG.AppendixAB.StationaryPhaseCompact
import GSQG.AppendixAB.StationaryPhaseHomogeneous
import GSQG.AppendixAB.OscillatoryMultiplier

-- Beyond the paper (1): the interior fractional Schauder estimate cited in §4 (as Ros-Oton–Serra,
-- Cor. 2.4), proved here as Prop. 2.2 of the arXiv version with n = 1, for smooth w and β, β+p ∉ ℕ
import GSQG.SchauderEstimate.Setup
import GSQG.SchauderEstimate.Kernels
import GSQG.SchauderEstimate.HolderTransport
import GSQG.SchauderEstimate.Commutator
import GSQG.SchauderEstimate.FourierFactorization
import GSQG.SchauderEstimate.TaylorCancellation
import GSQG.SchauderEstimate.DyadicIncrements
import GSQG.SchauderEstimate.Reconstruction

-- Beyond the paper (2): derivation of the front equation from the canonical 2D weak patch system
import GSQG.PatchEquation.Setup
import GSQG.PatchEquation.CancellationOperator
import GSQG.PatchEquation.FourierNormalization
import GSQG.PatchEquation.GraphFlux
import GSQG.PatchEquation.Velocity
import GSQG.PatchEquation.NormalTrace
import GSQG.PatchEquation.BulkToContour
import GSQG.PatchEquation.WeakFormulation
import GSQG.PatchEquation.Equivalence
import GSQG.PatchEquation.MainTheorem
