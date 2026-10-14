import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.Tensor.Pointwise.Basic
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotCurry.Reconstruction
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.TraceDiscrepancy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

omit [CompactSpace M] in
lemma pointwiseTensorCurv_eq_covGradRoughLapCurv_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    pointwiseTensorCurv (I := I) (M := M) g s S =
      covGradRoughLapCurvCovariantTensor (I := I) (M := M) g s S := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_eq_covGradRoughLapCurv_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_eq_covGradRoughLapCurv_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_eq_covGradRoughLapCurv_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_eq_covGradRoughLapCurv_covariantTensor

omit [CompactSpace M] in
lemma tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (w : TangentSpace I x) :
    tensor0SCurry (I := I) (M := M) s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
          (unitZeroSec (I := I) (M := M) x)) w =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
        (covGradRoughLapTraceDiscrepancyCovariantTensor (I := I) (M := M) g s S x w +
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
              (fun y : M => S.toSection y) x)
            (unitZeroSec (I := I) (M := M) x) -
          covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s S x w) := by
  rw [pointwiseTensorCurv_eq_covGradRoughLapCurv_covariantTensor (I := I) (M := M) g s S]
  rw [covGradRoughLapCurv_curry_eq_discrepancy_add_curv_sub_residual_covariantTensor
    (I := I) (M := M) g s S x w]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensorThirdOrderCurvatureDefect (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [Tensor3rdCurv_eq_genuine_add_bracket (I := I) g 0 s
      (smoothExtensionTangent (I := I) x w) (fun y : M => S.toSection y) x]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x +
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) +
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x w)
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x) from rfl]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction

noncomputable def genuineThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → E) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        tensor3rdCurvGenuine (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
          (fun y : M => S.toSection y) x)
        (unitZeroSec (I := I) (M := M) x)) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib ``Submission.DifferentialGeometry.Geometry.Curvature.genuineThirdCurvFieldFib

noncomputable def bracketThirdCurvFieldFib
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (w : TangentSpace I x)
    (m : Fin s → E) : ℝ :=
  ∑ a : Fin n, g.inner x (e a) w •
    Tensor0SSpace.toModel
      (covGradRoughLapTraceDiscrepancyCovariantTensor (I := I) (M := M) g s S x (e a) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensor3rdCurvBracket (I := I) g 0 s (smoothExtensionTangent (I := I) x (e a))
            (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) -
        covGradRoughLapMovingFrameResidualCovariantTensor (I := I) (M := M) g s S x (e a)) m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.bracketThirdCurvFieldFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.bracketThirdCurvFieldFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.bracketThirdCurvFieldFib ``Submission.DifferentialGeometry.Geometry.Curvature.bracketThirdCurvFieldFib

omit [CompactSpace M] in
theorem pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ (w : TangentSpace I x) (m : Fin s → E),
        Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
              (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
              (unitZeroSec (I := I) (M := M) x))
              (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x w) m) =
          genuineThirdCurvFieldFib (I := I) (M := M) g s S x e w m +
            bracketThirdCurvFieldFib (I := I) (M := M) g s S x e w m := by
  classical
  obtain ⟨n, e, hn, horth, hrecon⟩ :=
    tensor0S_eq_sum_slot0_uncurry (I := I) (M := M) g s x
  refine ⟨n, e, hn, horth, fun w m => ?_⟩
  rw [hrecon
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
      (unitZeroSec (I := I) (M := M) x)) w m]
  rw [genuineThirdCurvFieldFib, bracketThirdCurvFieldFib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensor0S_curry_pointwiseTensorCurv_eq_genuine_add_obstruction
    (I := I) (M := M) g s S x (e a)]
  rw [Tensor0SSpace.toModel_add, add_apply, smul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field ``Submission.DifferentialGeometry.Geometry.Curvature.pointwiseTensorCurv_toSection_eq_genuine_add_bracket_field

end Curvature
end Geometry
end DifferentialGeometry
