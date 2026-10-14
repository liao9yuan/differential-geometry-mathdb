import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartTensorRSInputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun i : Fin r =>
                (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                  (tangentLinearMapToModel
                    (tangentSlotCLM (I := I) r k
                      (chartLeviCivitaParallelCLM (I := I) g α b B) i))))))
        (fun j : Fin s =>
          chartTrivializationLinearMapSymm (I := I) (M := M) α b
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j))) = _
  rw [Tensor0SSpace.toModel_apply_model_vector]
  change Tensor0SSpace.eval
      (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j)))) = _
  rw [chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
    (Tensor0SSpace.ofModel
      ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
    (fun j : Fin s =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j))))]
  have hsubst :
      tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))) =
        Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun i : Fin r =>
              (chartTrivializationLinearMap (I := I) (M := M) α b).comp
                (tangentLinearMapToModel
                  (tangentSlotCLM (I := I) r k
                    (chartLeviCivitaParallelCLM (I := I) g α b B) i)))) := by
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext ?_
    intro v
    change Tensor0SSpace.eval
        (tensorSlotSubstCLM (I := I) r b
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B))
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
        (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i)) =
      ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun i : Fin r =>
          (chartTrivializationLinearMap (I := I) (M := M) α b).comp
            (tangentLinearMapToModel
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i)))) v
    rw [tensorSlotSubstCLM_apply (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b B))
      (Tensor0SSpace.ofModel
        ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
      (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i))]
    change ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B) i
            ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm (v i)))) = _
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
  rw [hsubst, Tensor0SSpace.toModel_apply_model_vector]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chartComp_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chartComp_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chartComp_formula ``Submission.DifferentialGeometry.Analysis.Elliptic.chartTensorRSInputSlotCorrection_chartComp_formula

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartTensorRSOutputSlotCorrection_chartComp_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (Tensor0SSpace.ofModel
            ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
        (fun j : Fin s =>
          tangentLinearMapToModel
            (tangentSlotCLM (I := I) s l
              (chartLeviCivitaParallelCLM (I := I) g α b B) j)
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j)))) := by
  classical
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)]
  rw [tensorChartComponentProjection_apply]
  rw [chartRSTwistInv_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        chartTrivializationLinearMapSymm (I := I) (M := M) α b
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j))) = _
  rw [Tensor0SSpace.toModel_apply_model_vector]
  change Tensor0SSpace.eval
      (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l
        (Tensor0SSpace.ofModel
          ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j : Fin s =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j)))) = _
  rw [chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l]
  change Tensor0SSpace.eval
      (T b (Tensor0SSpace.ofModel
        ((dualCoordinateProductMultilinearMap (E := E) r Idx).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))))
      (fun j => tangentSlotCLM (I := I) s l
        (chartLeviCivitaParallelCLM (I := I) g α b B) j
          ((tangentSpaceModelContinuousLinearEquiv (I := I) b).symm
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx j))))) = _
  rw [Tensor0SSpace.toModel_apply_model_vector]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chartComp_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chartComp_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chartComp_formula ``Submission.DifferentialGeometry.Analysis.Elliptic.chartTensorRSOutputSlotCorrection_chartComp_formula

end Elliptic
end Analysis
end DifferentialGeometry
