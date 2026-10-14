import Submission.DifferentialGeometry.Geometry.Connection.Hessian.Restriction
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.SubbundleRestriction
import Submission.DifferentialGeometry.Geometry.Connection.SelfAdjointRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
variable [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
variable [IsContMDiffRiemannianBundle I ∞ F V]

namespace CovariantDerivative
open _root_.CovariantDerivative

open _root_.CovariantDerivative in
theorem selfAdjoint_hessian_subtypeVal
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ∀ (A : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (x : M) (X Y : TangentSpace I x),
      ((cov.selfAdjoint hcov).hessian base A x X Y : V x →L[ℝ] V x) =
        (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov).hessian base (fun y => (A y : V y →L[ℝ] V y)) x X Y := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.restrict_hessian_subtypeVal S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov) base

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.selfAdjoint_hessian_subtypeVal then
    throwError "Refusing to shadow existing declaration CovariantDerivative.selfAdjoint_hessian_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.selfAdjoint_hessian_subtypeVal ``Submission.CovariantDerivative.selfAdjoint_hessian_subtypeVal

end CovariantDerivative

namespace DifferentialGeometry.Geometry.Connection

theorem rawBundleConnLap_selfAdjoint_subtypeVal
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯) (x : M),
      (rawBundleConnLap g (cov.selfAdjoint hcov) A x : V x →L[ℝ] V x) =
        rawBundleEndomorphismConnLap g cov (fun y => (A y : V y →L[ℝ] V y)) x := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  exact rawBundleConnLap_restrict_subtypeVal g
    (HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov) S
    (HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint cov hcov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_selfAdjoint_subtypeVal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_selfAdjoint_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_selfAdjoint_subtypeVal ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_selfAdjoint_subtypeVal

end DifferentialGeometry.Geometry.Connection
