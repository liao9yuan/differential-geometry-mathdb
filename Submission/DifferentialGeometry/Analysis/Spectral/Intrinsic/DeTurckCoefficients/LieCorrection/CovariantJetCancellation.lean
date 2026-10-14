import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHS.PathOrderSplitting
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.Field
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.TameLipschitz.LieTermChartValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Topology _root_.Manifold _root_.BigOperators _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [BoundarylessManifold I M]

omit [SigmaCompactSpace M] in
theorem lieSlope_eq_terms
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    lieDeTurckChartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg x i j s
        (extChartAt I x x) =
      unitModel (I := I) (M := M) g₀ 2
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
              (deTurckLieCoeffField (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg +
                lieCorrectionZeroField (I := I) (M := M) g₀
                  (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
            operatorFieldApply (I := I) (M := M) g₀ 3 2
              (deTurckLieFirstOrderCoeff (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg)
              (iteratedCovGrad (I := I) g₀ 0 2 1
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T'))) +
            operatorFieldApply (I := I) (M := M) g₀ 4 2
              (deTurckLieSecondOrderPrincipalCoeff (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
              (iteratedCovGrad (I := I) g₀ 0 2 2
                (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
          ![(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i, (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j] := by
  classical
  have hy : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless
      (I := I) x (mem_extChartAt_target x)
  have hsplit := lieDeTurckChartSlope_eq_orderSplit (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' g_bg x i j s hy
  have h0 := lie0_order0_eq (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' g_bg s x i j
  have h1 := lieTerm_firstOrder_value_eq_order1Raw_add_tail (I := I) g₀ g_bg T T'
    hδ_lt hδ hδ'_lt hδ' s x i j
  have h2 := lieTop_cov_eq_principalSymbolExprRaw_add_tail (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) x i j
  rw [lieTopTail] at h2
  refine hsplit.trans ?_
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add (I := I) g₀ 2, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add (I := I) g₀ 2,
    add_apply, add_apply]
  linear_combination -h0 - h1 - h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSlope_eq_terms then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSlope_eq_terms"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSlope_eq_terms ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.lieSlope_eq_terms

end DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
