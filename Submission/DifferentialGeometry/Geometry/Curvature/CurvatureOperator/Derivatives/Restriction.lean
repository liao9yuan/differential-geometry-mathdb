import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.MetricRestriction
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry
local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1

theorem curvCovDeriv_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (k : ℕ) (x : U)
    (slots : Fin (k + 4) → TangentSpace I x) :
    curvCovDeriv (g.restrictOpen U) k x slots = curvCovDeriv g k (x : M) slots := by
  induction k generalizing x with
  | zero =>
    change metricRm04 (g.restrictOpen U) x slots = metricRm04 g (x : M) slots
    rw [metricRm04_apply, metricRm04_apply]
    have hvec : vec4 (slots 0) (slots 1) (slots 2) (slots 3) = slots := by
      ext i
      fin_cases i <;> rfl
    have h := metricRm04StandardAt_restrictOpen g U x (slots 0) (slots 1) (slots 2) (slots 3)
    simp only [metricRm04StandardAt_apply, mfderiv_subtype_val_apply] at h
    rw [hvec] at h
    exact h
  | succ k ih =>
    change totalNabla0SFun (k + 4) (metricCov (g.restrictOpen U))
        (curvCovDeriv (g.restrictOpen U) k) x slots =
      totalNabla0SFun (k + 4) (metricCov g) (curvCovDeriv g k) (x : M) slots
    have hA : curvCovDeriv (g.restrictOpen U) k =
        restrictOpen0S (k + 4) (curvCovDeriv g k) := by
      ext y v
      exact ih y v
    rw [hA, totalNabla0SFun_metricCov_restrictOpen]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_restrictOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_restrictOpen

theorem curvDerivNorm_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (k : ℕ) (x : U) :
    curvDerivNorm k (g.restrictOpen U) x = curvDerivNorm k g (x : M) := by
  have h : curvCovDeriv (g.restrictOpen U) k x = curvCovDeriv g k (x : M) := by
    ext slots
    exact curvCovDeriv_restrictOpen g U k x slots
  unfold curvDerivNorm curvDerivNormSq
  rw [normSq0S_restrictOpen_apply, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_restrictOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_restrictOpen

end DifferentialGeometry.CheegerGromovCompactness
