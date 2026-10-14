import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.CurvatureDefect
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.PointwiseCurvatureBound
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Tensor.Pointwise
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Tensor.FiberNorm
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner

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

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannSec_covApply_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    {X Y : Π b : M, TangentSpace I b} (x : M)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannSec (tensorCov (I := I) g 0 2) X Y
            (covApply (tensorCov (I := I) g 0 2) X (fun y : M => T₀.toSection y)) x) ≤
        Cx * g.inner x (X x) (X x) * g.inner x (Y x) (Y x) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (covApply (tensorCov (I := I) g 0 2) X
              (fun y : M => T₀.toSection y) x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g 2 x
  refine ⟨Cx, hCx_nonneg, ?_⟩
  have hZ := covApplyRS_contMDiff (I := I) g 0 2 (T := fun y : M => T₀.toSection y)
    T₀.toSection.contMDiff (X := X) hX
  rw [riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 2) hX hY hZ]
  exact hbound (X x) (Y x) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannSec_covApply_fiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannSec_covApply_fiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannSec_covApply_fiberNormSq_le ``Submission.DifferentialGeometry.Geometry.Curvature.riemannSec_covApply_fiberNormSq_le

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem riemannSec_orthoFrame_covApply_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (riemannSec (tensorCov (I := I) g 0 2)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => T₀.toSection y)) x) ≤
        Cx * riemannianFiberNormSq (I := I) (M := M) g 0 2 x
            (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => T₀.toSection y) x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    riemannSec_covApply_fiberNormSq_le (I := I) (M := M) g T₀
      (X := smoothOrthoFrame (I := I) g x i) (Y := smoothOrthoFrame (I := I) g x i) x
      (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i)
  refine ⟨Cx, hCx_nonneg, ?_⟩
  have hortho : g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    simpa using this
  rw [hortho] at hbound
  simpa using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannSec_orthoFrame_covApply_fiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannSec_orthoFrame_covApply_fiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannSec_orthoFrame_covApply_fiberNormSq_le ``Submission.DifferentialGeometry.Geometry.Curvature.riemannSec_orthoFrame_covApply_fiberNormSq_le

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem orthoFrame_pair_covApply_commutator
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (i a : Fin (Module.finrank ℝ E)) :
    covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
        (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x a)
          (fun y : M => T₀.toSection y)) =
      covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x a)
          (covApply (tensorCov (I := I) g 0 2) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => T₀.toSection y))
        + covApply (tensorCov (I := I) g 0 2)
            (VectorField.mlieBracket I (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame (I := I) g x a)) (fun y : M => T₀.toSection y)
        + (fun b : M => riemannSec (tensorCov (I := I) g 0 2)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
            (fun y : M => T₀.toSection y) b) :=
  covApply_covApply_eq_section (tensorCov (I := I) g 0 2)
    (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x a)
    (fun y : M => T₀.toSection y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.orthoFrame_pair_covApply_commutator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.orthoFrame_pair_covApply_commutator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.orthoFrame_pair_covApply_commutator ``Submission.DifferentialGeometry.Geometry.Curvature.orthoFrame_pair_covApply_commutator

end Curvature
end Geometry
end DifferentialGeometry

end
