import Submission.DifferentialGeometry.Geometry.Curvature.SecondOrderDefect.MetricTraceFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
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

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

section DifferentialIdentities

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

omit [CompactSpace M] in
theorem covGradRoughLapCurv_toSection_eq_sub
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x =
      (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x -
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toSection x := by
  rw [covGradRoughLapCurv]
  rw [SmoothCcTensor.toSection_sub]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_toSection_eq_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_toSection_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_toSection_eq_sub ``Submission.DifferentialGeometry.Geometry.Curvature.covGradRoughLapCurv_toSection_eq_sub

omit [CompactSpace M] in
theorem rawTensorConnLap_gradTensor_toSection_eq_frame_trace
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    (rawTensorConnLapSmooth (I := I) g 0 3
        (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorSecondCovDeriv (I := I) g 0 3
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x := by
  rw [rawTensorConnLapSmooth_toSection_apply]
  exact rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 3
    (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace ``Submission.DifferentialGeometry.Geometry.Curvature.rawTensorConnLap_gradTensor_toSection_eq_frame_trace

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem secondCovDeriv_gradTensor_antisymm_eq_riemannOp
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g 0 3 X Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x -
      tensorSecondCovDeriv (I := I) g 0 3 Y X
        (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x =
      riemannOp (tensorCov (I := I) g 0 3) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) :=
  tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 3
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
    hX hY (covGrad_contMDiff_totalSpaceMk (I := I) (M := M) g T₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.secondCovDeriv_gradTensor_antisymm_eq_riemannOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.secondCovDeriv_gradTensor_antisymm_eq_riemannOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.secondCovDeriv_gradTensor_antisymm_eq_riemannOp ``Submission.DifferentialGeometry.Geometry.Curvature.secondCovDeriv_gradTensor_antisymm_eq_riemannOp

end DifferentialIdentities

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem riemannOp_gradTensor_offDiag_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ v w : TangentSpace I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (riemannOp (tensorCov (I := I) g 0 3) x v w
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g 3 x
  refine ⟨Cx, hCx_nonneg, fun v w => ?_⟩
  exact hbound v w ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_fiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_fiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_fiberNormSq_le ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_fiberNormSq_le

omit [CompactSpace M] in
theorem riemannOp_gradTensor_offDiag_frame_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ i j : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            (riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
          Cx * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    riemannOp_gradTensor_offDiag_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨Cx, hCx_nonneg, fun i j => ?_⟩
  have hii : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    simpa using this
  have hjj : g.inner x (smoothOrthoFrame (I := I) g x j x)
      (smoothOrthoFrame (I := I) g x j x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x j j
    simpa using this
  have h := hbound (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x)
  rw [hii, hjj] at h
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_frame_fiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_frame_fiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_frame_fiberNormSq_le ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_gradTensor_offDiag_frame_fiberNormSq_le

end Curvature

end Geometry

end DifferentialGeometry

end
