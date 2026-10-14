import Submission.DifferentialGeometry.Geometry.Curvature.SecondOrderDefect.GradientSlotLeibniz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SNabla
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricTrace2_covDeriv_comm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) (w : TangentSpace I x) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x w =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x w := by
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T.toSection y)) :=
    T.toSection.contMDiff
  rw [show (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
        (fun z : M => T.toSection z) y) =
      (fun y : M => rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) y) from by
    funext y
    exact (rawTensorConnLap_eq_metricTrace2 (I := I) g r s
      (fun z : M => T.toSection z) y).symm]
  exact covDeriv_rawConnLap_eq_frozenFrameTrace_sum (I := I) g r s hT x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm ``Submission.DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricTrace2_covDeriv_comm_map
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (x : M) :
    (tensorCov (I := I) g r s).toFun
        (fun y : M => metricTrace2 (I := I) g r s (tensorSecondCovDeriv (I := I) g r s)
          (fun z : M => T.toSection z) y) x =
      ∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g r s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (fun z : M => T.toSection z) y) x := by
  refine ContinuousLinearMap.ext (fun w => ?_)
  rw [sum_apply]
  exact metricTrace2_covDeriv_comm (I := I) g r s T x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm_map ``Submission.DifferentialGeometry.Geometry.Curvature.metricTrace2_covDeriv_comm_map

end Curvature
end Geometry
end DifferentialGeometry

end
