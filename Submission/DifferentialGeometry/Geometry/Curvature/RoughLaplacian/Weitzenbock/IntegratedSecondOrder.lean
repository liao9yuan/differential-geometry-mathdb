import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Weitzenbock.IntegratedCovariantTensor
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorCommutator
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Tensor.FiberNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

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


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem secondCovDeriv_covGrad_antisymm_eq_riemannOp_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g 0 (s + 1) X Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
      tensorSecondCovDeriv (I := I) g 0 (s + 1) Y X
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x =
      riemannOp (tensorCov (I := I) g 0 (s + 1)) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
  tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 (s + 1)
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y)
    hX hY (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.secondCovDeriv_covGrad_antisymm_eq_riemannOp_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.secondCovDeriv_covGrad_antisymm_eq_riemannOp_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.secondCovDeriv_covGrad_antisymm_eq_riemannOp_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.secondCovDeriv_covGrad_antisymm_eq_riemannOp_covariantTensor


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem riemannOp_covGrad_fiberNormSq_le_covariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ v w : TangentSpace I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (riemannOp (tensorCov (I := I) g 0 (s + 1)) x v w
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g (s + 1) x
  refine ⟨Cx, hCx_nonneg, fun v w => ?_⟩
  exact hbound v w ((covGrad (I := I) (M := M) g 0 s S).toSection x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_covGrad_fiberNormSq_le_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_covGrad_fiberNormSq_le_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_covGrad_fiberNormSq_le_covariantTensor ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_covGrad_fiberNormSq_le_covariantTensor

end Curvature
end Geometry
end DifferentialGeometry

end
