import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.FreeDirection

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

noncomputable def covGradRoughLapCurv
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 0 3 :=
  rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) -
    covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv

omit [CompactSpace M] in
theorem covGradRoughLap_commutator_eq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) =
      covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T₀)
        + covGradRoughLapCurv (I := I) (M := M) g T₀ := by
  rw [covGradRoughLapCurv]
  rw [add_comm]
  rw [sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLap_commutator_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLap_commutator_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLap_commutator_eq ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLap_commutator_eq

noncomputable def fixedFrameSwapTraceUnit
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  (∑ i : Fin (Module.finrank ℝ E),
      (tensorCov (I := I) g 0 2).toFun
        (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))) x
        (smoothExtensionTangent (I := I) x w x))
    (unitZeroSec (I := I) (M := M) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnit ``Submission.DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnit

noncomputable def covGradRoughLapMovingFrameResidual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace 2 I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorCovDerivAt (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
      (unitZeroSec (I := I) (M := M) x) -
    fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual

omit [CompactSpace M] in
lemma covGradRoughLapMovingFrameResidual_def
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
          (unitZeroSec (I := I) (M := M) x) -
        fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_def ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_def

omit [CompactSpace M] in
theorem rhs_curry_eq_swap_add_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀) x w)
        (unitZeroSec (I := I) (M := M) x) =
      fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w +
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  rw [covGradRoughLapMovingFrameResidual_def]
  rw [add_comm]
  rw [sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual ``Submission.DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual

omit [CompactSpace M] in
theorem covGrad_rawConnLap_curry_eq_swap_add_residual
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w +
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w := by
  rw [covGrad_rawConnLap_unit_eval_curry (I := I) (M := M) g T₀ x w]
  exact rhs_curry_eq_swap_add_residual (I := I) (M := M) g T₀ x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual

omit [CompactSpace M] in
theorem frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 2).toFun
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      tensor0SCurry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g 0 2
              (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 2 (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  rw [frame_trace_third_eq_swap_unit (I := I) (M := M) g T₀ x w]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 2).toFun
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) =
        fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w from rfl]
  rw [show fixedFrameSwapTraceUnit (I := I) (M := M) g T₀ x w =
        tensor0SCurry (I := I) (M := M) 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
              (covGrad (I := I) (M := M) g 0 2
                (rawTensorConnLapSmooth g 0 2 T₀)).toSection x)
              (unitZeroSec (I := I) (M := M) x)) w -
          covGradRoughLapMovingFrameResidual (I := I) (M := M) g T₀ x w from by
      rw [covGrad_rawConnLap_curry_eq_swap_add_residual (I := I) (M := M) g T₀ x w]
      rw [add_sub_cancel_right]]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv ``Submission.DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv

noncomputable def covGradRoughLapCurvCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  rawTensorConnLapSmooth (I := I) g 0 (s + 1) (covGrad (I := I) (M := M) g 0 s T₀) -
    covGrad (I := I) (M := M) g 0 s (rawTensorConnLapSmooth (I := I) g 0 s T₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurvCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurvCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurvCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurvCovariantTensor

omit [CompactSpace M] in
lemma covGrad_rawConnLap_unit_eval_curry_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth g 0 s T₀) x w)
        (unitZeroSec (I := I) (M := M) x) :=
  curry_covGrad_unit_eval (I := I) (M := M) g s
    (rawTensorConnLapSmooth g 0 s T₀) x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_unit_eval_curry_covariantTensor

noncomputable def fixedFrameSwapTraceUnitCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace s I x :=
  (∑ i : Fin (Module.finrank ℝ E),
      (tensorCov (I := I) g 0 s).toFun
        (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))) x
        (smoothExtensionTangent (I := I) x w x))
    (unitZeroSec (I := I) (M := M) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnitCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnitCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnitCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.fixedFrameSwapTraceUnitCovariantTensor

noncomputable def covGradRoughLapMovingFrameResidualCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    Tensor0SSpace s I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s T₀) x w)
      (unitZeroSec (I := I) (M := M) x) -
    fixedFrameSwapTraceUnitCovariantTensor (I := I) (M := M) g s T₀ x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidualCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidualCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidualCovariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidualCovariantTensor

omit [CompactSpace M] in
lemma covGradRoughLapMovingFrameResidual_gen_def
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s T₀ x w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth (I := I) g 0 s T₀) x w)
          (unitZeroSec (I := I) (M := M) x) -
        fixedFrameSwapTraceUnitCovariantTensor (I := I) (M := M) g s T₀ x w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_gen_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_gen_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_gen_def ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapMovingFrameResidual_gen_def

omit [CompactSpace M] in
theorem rhs_curry_eq_swap_add_residual_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorCovDerivAt (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T₀) x w)
        (unitZeroSec (I := I) (M := M) x) =
      fixedFrameSwapTraceUnitCovariantTensor (I := I) (M := M) g s T₀ x w +
        covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s T₀ x w := by
  rw [covGradRoughLapMovingFrameResidual_gen_def]
  rw [add_comm]
  rw [sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.rhs_curry_eq_swap_add_residual_covariantTensor

omit [CompactSpace M] in
theorem covGrad_rawConnLap_curry_eq_swap_add_residual_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      fixedFrameSwapTraceUnitCovariantTensor (I := I) (M := M) g s T₀ x w +
        covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s T₀ x w := by
  rw [covGrad_rawConnLap_unit_eval_curry_covariantTensor (I := I) (M := M) g s T₀ x w]
  exact rhs_curry_eq_swap_add_residual_covariantTensor (I := I) (M := M) g s T₀ x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_rawConnLap_curry_eq_swap_add_residual_covariantTensor

omit [CompactSpace M] [I.Boundaryless] in
lemma frame_trace_third_eq_swap_unit_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 s)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff x w
  have hT₀ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b (T₀.toSection b)) :=
    T₀.toSection.contMDiff
  have hswap := frame_trace_thirdCovDeriv_swap (I := I) g 0 s
    (W := smoothExtensionTangent (I := I) x w) (T := fun y : M => T₀.toSection y) (x := x)
    hW hT₀
  have happ := congrArg
    (fun (φ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) =>
      φ (unitZeroSec (I := I) (M := M) x)) hswap
  simpa only [sum_apply, add_apply] using happ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.frame_trace_third_eq_swap_unit_covariantTensor

omit [CompactSpace M] in
theorem frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T₀ : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E),
        (tensorCov (I := I) g 0 s).toFun
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 s)
              (smoothExtensionTangent (I := I) x w) (fun y : M => T₀.toSection y))) x
          (smoothOrthoFrame (I := I) g x i x))
        (unitZeroSec (I := I) (M := M) x) =
      tensor0SCurry (I := I) (M := M) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g 0 s
              (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) w -
        covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s T₀ x w +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
            (fun y : M => T₀.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) := by
  rw [frame_trace_third_eq_swap_unit_covariantTensor (I := I) (M := M) g s T₀ x w]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
                (fun y : M => T₀.toSection y))) x
            (smoothExtensionTangent (I := I) x w x))
          (unitZeroSec (I := I) (M := M) x) =
        fixedFrameSwapTraceUnitCovariantTensor (I := I) (M := M) g s T₀ x w from rfl]
  rw [show fixedFrameSwapTraceUnitCovariantTensor (I := I) (M := M) g s T₀ x w =
        tensor0SCurry (I := I) (M := M) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (covGrad (I := I) (M := M) g 0 s
                (rawTensorConnLapSmooth g 0 s T₀)).toSection x)
              (unitZeroSec (I := I) (M := M) x)) w -
          covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s T₀ x w from by
      rw [covGrad_rawConnLap_curry_eq_swap_add_residual_covariantTensor (I := I) (M := M) g s T₀ x w]
      rw [add_sub_cancel_right]]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.frame_trace_thirdW_eq_covGrad_rawConnLap_sub_residual_add_curv_covariantTensor

end Curvature
end Geometry
end DifferentialGeometry

end
