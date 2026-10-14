import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.SlotZeroFrameTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

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
  [T2Space M]

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

noncomputable def covGradRoughLapTraceDiscrepancy
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  tensor0SCurry (I := I) (M := M) 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) w -
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) (M := M) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy

omit [CompactSpace M] in
lemma covGradRoughLapTraceDiscrepancy_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapTraceDiscrepancy (I := I) (M := M) g T₀ x w =
      tensor0SCurry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (rawTensorConnLapSmooth (I := I) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g 0 2).toFun
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g 0 2)
                  (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
              (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_def ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_def

omit [CompactSpace M] in
theorem covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      covGradRoughLapTraceDiscrepancy (I := I) (M := M) g T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  have hdef : (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x := by
    rw [covGradRoughLapCurv, SmoothCcTensor.toSection_sub]; rfl
  rw [hdef]
  rw [sub_apply, map_sub, sub_apply]
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  have hswap := frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (I := I) (M := M) g T₀ x w
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w] at hswap
  rw [covGradRoughLapTraceDiscrepancy_def (I := I) (M := M) g T₀ x w]
  rw [hswap]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual

noncomputable def covGradRoughLapTraceDiscrepancyCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace s I x :=
  tensor0SCurry (I := I) (M := M) s x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T₀)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) w -
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 s)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
      (unitZeroSec (I := I) (M := M) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancyCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancyCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancyCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancyCovariantTensor

omit [CompactSpace M] in
lemma covGradRoughLapTraceDiscrepancy_gen_def
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapTraceDiscrepancyCovariantTensor (I := I) (M := M) g s T₀ x w =
      tensor0SCurry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
              (covGrad (I := I) (M := M) g 0 s T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        (∑ i : Fin (Module.finrank ℝ E),
            (tensorCov (I := I) g 0 s).toFun
              (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                (covApply (tensorCov (I := I) g 0 s)
                  (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
              (smoothOrthoFrame (I := I) g x i x))
          (unitZeroSec (I := I) (M := M) x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_gen_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_gen_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_gen_def ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapTraceDiscrepancy_gen_def

omit [CompactSpace M] in
theorem covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGradRoughLapCurvCovariantTensor (I := I) (M := M) g s T₀).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      covGradRoughLapTraceDiscrepancyCovariantTensor (I := I) (M := M) g s T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s T₀ x w := by
  have hdef : (covGradRoughLapCurvCovariantTensor (I := I) (M := M) g s T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T₀)).toSection x := by
    rw [covGradRoughLapCurvCovariantTensor, SmoothCcTensor.toSection_sub]; rfl
  rw [hdef]
  rw [sub_apply, map_sub, sub_apply]
  rw [covGrad_rawConnLap_unit_eval_curry_covariantTensor (I := I) (M := M) g s T₀ x w]
  have hswap := frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_covariantTensor
    (I := I) (M := M) g s T₀ x w
  rw [covGrad_rawConnLap_unit_eval_curry_covariantTensor (I := I) (M := M) g s T₀ x w] at hswap
  rw [covGradRoughLapTraceDiscrepancy_gen_def (I := I) (M := M) g s T₀ x w]
  rw [hswap]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_covariantTensor

end Curvature
end Geometry
end DifferentialGeometry

end
