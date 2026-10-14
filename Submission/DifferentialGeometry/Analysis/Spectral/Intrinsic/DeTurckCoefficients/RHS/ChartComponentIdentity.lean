import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHS.Symmetry
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.MatrixChartIdentification
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDerivative.ChartFrame
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.SlotCorrectionComponent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.RealInnerProductSpace _root_.InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace DeTurckCoefficients

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.DeTurck
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem tensorChartComponentRaw_deTurckRHSSectionBackground_eq_deTurckRicciRHS
    (g_bg g₁ : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ (chartAt H α).source)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
        (deTurckRHSSectionBackground (I := I) g_bg g₁) α Idx Jdx b =
      deTurckRicciRHS (I := I) g_bg g₁ b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 0) b)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 1) b) := by
  classical
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g_bg 0 2
    (deTurckRHSSectionBackground (I := I) g_bg g₁) α hb Idx Jdx]
  have hframe : chartFrameBasisModel (I := I) (M := M) α b 0 Idx =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α b 0 Idx v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe]
  have hmodel := deTurckRHSSection_eval (I := I) g_bg g₁ b
    (fun k : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx k) b)
  rw [show (deTurckRHSSectionBackground (I := I) g_bg g₁).toSection b =
      (deTurckRHSSection (I := I) g_bg g₁).toSection b from rfl]
  have hdirect :
      ((deTurckRHSSection (I := I) g_bg g₁).toSection b
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I b) ℝ)
        (fun k : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx k) b) =
      Tensor0SSpace.eval
        ((deTurckRHSSection (I := I) g_bg g₁).toSection b
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I b) (1 : ℝ)))
        (fun k : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx k) b) := rfl
  rw [hdirect, hmodel]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBackground_eq_deTurckRicciRHS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBackground_eq_deTurckRicciRHS target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_deTurckRHSSectionBackground_eq_chartRicciLie
    (g_bg g₁ : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g_bg 0 2
        (deTurckRHSSectionBackground (I := I) g_bg g₁) α Idx Jdx b =
      (-2 : ℝ) * chartRicciTensor (I := I) g₁ α (Jdx 0) (Jdx 1) (extChartAt I α b) +
        chartLieDeTurckComp (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
  classical
  have hb_source : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  set v₀ : TangentSpace I b := DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 0) b with hv₀_def
  set v₁ : TangentSpace I b := DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 1) b with hv₁_def
  rw [tensorChartComponentRaw_deTurckRHSSectionBackground_eq_deTurckRicciRHS (I := I) (M := M) g_bg g₁ α
      hb_source Idx Jdx]
  rw [show DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 0) b = v₀ from rfl,
    show DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (Jdx 1) b = v₁ from rfl]
  rw [deTurckRicciRHS, add_apply, add_apply,
    smul_apply, smul_apply, smul_eq_mul]
  have hRic :
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g₁) b v₀ v₁ =
        chartRicciTensor (I := I) g₁ α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
    have h := ricciTensor_chartBasisVec_alpha_eq (I := I) g₁ α (Jdx 0) (Jdx 1) hb
    rw [hv₀_def, hv₁_def]
    exact h
  have hLie :
      lieDerivMetricClm (I := I) g₁
        (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
          (smoothRiemannianMetricToInfty (I := I) g_bg)) b v₀ v₁ =
        chartLieDeTurckComp (I := I) g₁ g_bg α (Jdx 0) (Jdx 1) (extChartAt I α b) := by
    rw [lieDerivMetricClm_apply]
    have hmat := chartLieDerivMetricMatrix_eq_lieDerivMetric_chartBasis (I := I)
      (smoothRiemannianMetricToInfty (I := I) g₁)
      (deTurckVF (I := I) (smoothRiemannianMetricToInfty (I := I) g₁)
        (smoothRiemannianMetricToInfty (I := I) g_bg))
      α (Jdx 0) (Jdx 1) b hb
    rw [hv₀_def, hv₁_def, ← hmat]
    exact chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp (I := I) g₁ g_bg α
      (Jdx 0) (Jdx 1) hb
  rw [hRic, hLie]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBackground_eq_chartRicciLie then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBackground_eq_chartRicciLie"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBackground_eq_chartRicciLie ``Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.tensorChartComponentRaw_deTurckRHSSectionBackground_eq_chartRicciLie

end DeTurckCoefficients
end Spectral
end Analysis
end DifferentialGeometry

end
