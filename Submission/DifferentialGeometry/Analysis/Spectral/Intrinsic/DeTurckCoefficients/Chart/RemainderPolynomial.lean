import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.LieDerivativeStructuralDifference
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.MatrixChartIdentification
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDerivative.ChartFrame
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Matrix _root_.Submission.Matrix
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace DeTurckCoefficients

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

def chartDeTurckRicciRHS (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  -2 * chartRicciTensor (I := I) g α i k y +
    chartLieDeTurckComp (I := I) g g_bg α i k y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [I.Boundaryless] in
theorem chartDeTurckRicciRHS_def (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRicciRHS (I := I) g g_bg α i k y =
      -2 * chartRicciTensor (I := I) g α i k y +
        chartLieDeTurckComp (I := I) g g_bg α i k y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_def ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_def

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS
    (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α) :
    DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg g x
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) =
      chartDeTurckRicciRHS (I := I) g g_bg α i k (extChartAt I α x) := by
  classical
  rw [DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_apply]
  rw [DifferentialGeometry.Geometry.Connection.ricciTensor_chartBasisVec_alpha_eq
      (I := I) g α i k hx]
  rw [← DifferentialGeometry.PDE.DeTurck.chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis
      (I := I) g (DifferentialGeometry.PDE.DeTurck.deTurckVF (I := I) g g_bg) α i k x hx]
  rw [chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp (I := I) g g_bg α i k hx]
  rw [chartDeTurckRicciRHS_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.deTurckRicciRHS_chartBasisVecFiber_eq_chartDeTurckRicciRHS

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckRicciRHS_sub_eq
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRicciRHS (I := I) g₁ g_bg α i k y -
        chartDeTurckRicciRHS (I := I) g₂ g_bg α i k y =
      -2 *
          ((∑ j : Fin (Module.finrank ℝ E),
              ((DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₁ α i k j) y -
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j (chartChristoffel (I := I) g₂ α i k j) y) -
                (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₁ α i j j) y -
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartChristoffel (I := I) g₂ α i j j) y))) +
            (∑ j : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
              (((chartChristoffel (I := I) g₁ α j m j y -
                      chartChristoffel (I := I) g₂ α j m j y) *
                    chartChristoffel (I := I) g₁ α i k m y +
                  chartChristoffel (I := I) g₂ α j m j y *
                    (chartChristoffel (I := I) g₁ α i k m y -
                      chartChristoffel (I := I) g₂ α i k m y)) -
                ((chartChristoffel (I := I) g₁ α k m j y -
                      chartChristoffel (I := I) g₂ α k m j y) *
                    chartChristoffel (I := I) g₁ α i j m y +
                  chartChristoffel (I := I) g₂ α k m j y *
                    (chartChristoffel (I := I) g₁ α i j m y -
                      chartChristoffel (I := I) g₂ α i j m y))))) +
        ((∑ kk : Fin (Module.finrank ℝ E),
            ((chartDeTurckVFComp (I := I) g₁ g_bg α kk y -
                  chartDeTurckVFComp (I := I) g₂ g_bg α kk y) *
                DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y +
              chartDeTurckVFComp (I := I) g₂ g_bg α kk y *
                (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y -
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) kk (chartGramOnE (I := I) g₂ α i k) y))) +
          (∑ kk : Fin (Module.finrank ℝ E),
              ((chartGramOnE (I := I) g₁ α kk k y - chartGramOnE (I := I) g₂ α kk k y) *
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                chartGramOnE (I := I) g₂ α kk k y *
                  (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α kk) y))) +
            (∑ kk : Fin (Module.finrank ℝ E),
              ((chartGramOnE (I := I) g₁ α i kk y - chartGramOnE (I := I) g₂ α i kk y) *
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                chartGramOnE (I := I) g₂ α i kk y *
                  (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₂ g_bg α kk) y)))) := by
  classical
  rw [chartDeTurckRicciRHS_def, chartDeTurckRicciRHS_def]
  rw [show -2 * chartRicciTensor (I := I) g₁ α i k y +
            chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
          (-2 * chartRicciTensor (I := I) g₂ α i k y +
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) =
        -2 * (chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y) +
          (chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) from by ring]
  rw [chartRicciTensor_sub_eq_christoffelDiff (I := I) g₁ g₂ α i k y,
    chartLieDeTurckComp_sub_eq (I := I) g₁ g₂ g_bg α i k y]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq

omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRicciRHS (I := I) g₁ g_bg α i k y -
        chartDeTurckRicciRHS (I := I) g₂ g_bg α i k y =
      -2 * ricciDiffPrincipalSymbol (I := I) g₁ g₂ α i k y +
        (-2 *
            (chartRicciDiffFirstOrderRemainder (I := I) g₁ g₂ α i k y +
              (chartRicciFirstOrderTerm (I := I) g₁ α i k y -
                chartRicciFirstOrderTerm (I := I) g₂ α i k y)) +
          ((∑ kk : Fin (Module.finrank ℝ E),
              ((chartDeTurckVFComp (I := I) g₁ g_bg α kk y -
                    chartDeTurckVFComp (I := I) g₂ g_bg α kk y) *
                  DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y +
                chartDeTurckVFComp (I := I) g₂ g_bg α kk y *
                  (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) kk (chartGramOnE (I := I) g₁ α i k) y -
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) kk (chartGramOnE (I := I) g₂ α i k) y))) +
            (∑ kk : Fin (Module.finrank ℝ E),
                ((chartGramOnE (I := I) g₁ α kk k y - chartGramOnE (I := I) g₂ α kk k y) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                  chartGramOnE (I := I) g₂ α kk k y *
                    (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i (chartDeTurckVFComp (I := I) g₂ g_bg α kk) y))) +
              (∑ kk : Fin (Module.finrank ℝ E),
                ((chartGramOnE (I := I) g₁ α i kk y - chartGramOnE (I := I) g₂ α i kk y) *
                    DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y +
                  chartGramOnE (I := I) g₂ α i kk y *
                    (DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₁ g_bg α kk) y -
                      DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (chartDeTurckVFComp (I := I) g₂ g_bg α kk)
                        y))))) := by
  classical
  rw [chartDeTurckRicciRHS_def, chartDeTurckRicciRHS_def]
  rw [show -2 * chartRicciTensor (I := I) g₁ α i k y +
            chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
          (-2 * chartRicciTensor (I := I) g₂ α i k y +
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) =
        -2 * (chartRicciTensor (I := I) g₁ α i k y - chartRicciTensor (I := I) g₂ α i k y) +
          (chartLieDeTurckComp (I := I) g₁ g_bg α i k y -
            chartLieDeTurckComp (I := I) g₂ g_bg α i k y) from by ring]
  rw [chartRicciTensor_sub_eq_principalSymbol_add_lowerOrder (I := I) g₁ g₂ α i k y,
    chartLieDeTurckComp_sub_eq (I := I) g₁ g₂ g_bg α i k y]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.chartDeTurckRicciRHS_sub_eq_principalSymbol_add_lowerOrder

end InnerProductSpaceModel

end DeTurckCoefficients
end Spectral
end Analysis
end DifferentialGeometry

end
