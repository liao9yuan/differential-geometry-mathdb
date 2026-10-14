import Submission.DifferentialGeometry.Geometry.Metric.SelfAdjointSubbundle
import Submission.DifferentialGeometry.Geometry.Connection.SubbundleRestriction
import Submission.DifferentialGeometry.Geometry.Connection.HomBundle.Basic

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
def selfAdjoint
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible) :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    CovariantDerivative I (Fin S.rank → ℝ) (fun x => S.fiber x) := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  letI := S.totalSpaceTopology
  letI := S.fiberBundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.restrict S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.selfAdjoint then
    throwError "Refusing to shadow existing declaration CovariantDerivative.selfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.selfAdjoint ``Submission.CovariantDerivative.selfAdjoint

open _root_.CovariantDerivative in
theorem selfAdjoint_subtypeVal
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible) :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin S.rank → ℝ, fun x => S.fiber x⟯)
      (x : M) (v : TangentSpace I x),
      (cov.selfAdjoint hcov A x v : V x →L[ℝ] V x) =
        DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov
          (fun y => (A y : V y →L[ℝ] V y)) x v := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.restrict_subtypeVal S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.selfAdjoint_subtypeVal then
    throwError "Refusing to shadow existing declaration CovariantDerivative.selfAdjoint_subtypeVal"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.selfAdjoint_subtypeVal ``Submission.CovariantDerivative.selfAdjoint_subtypeVal

open _root_.CovariantDerivative in
theorem contMDiff_selfAdjoint
    (cov : CovariantDerivative I F V) (hcov : cov.IsMetricCompatible)
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    ContMDiffCovariantDerivative (cov.selfAdjoint hcov) ∞ := by
  let S := Bundle.selfAdjointSubbundle (I := I) (F := F) (V := V) (n := ∞)
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  exact (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V cov cov)
    |>.contMDiff_restrict S
      (DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_isCovariantlyInvariant_selfAdjoint
        cov hcov) inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.contMDiff_selfAdjoint then
    throwError "Refusing to shadow existing declaration CovariantDerivative.contMDiff_selfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.contMDiff_selfAdjoint ``Submission.CovariantDerivative.contMDiff_selfAdjoint

end CovariantDerivative
