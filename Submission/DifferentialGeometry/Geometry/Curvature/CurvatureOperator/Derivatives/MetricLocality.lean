import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem curvCovDeriv_eq_of_metric_eventuallyEq
    (g h : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner y v w) (m : ℕ) :
    curvCovDeriv g m x = curvCovDeriv h m x := by
  obtain ⟨s, hs, hopen, hxs⟩ := mem_nhds_iff.mp hmetric
  let U : _root_.TopologicalSpace.Opens M := ⟨s, hopen⟩
  let y : U := ⟨x, hxs⟩
  have heq : g.restrictOpen U = h.restrictOpen U :=
    SmoothRiemannianMetric.ext_inner (fun z v w => hs z.property v w)
  ext slots
  exact (curvCovDeriv_restrictOpen g U m y slots).symm.trans
    ((congrArg (fun k : SmoothRiemannianMetric I U => curvCovDeriv k m y slots) heq).trans
      (curvCovDeriv_restrictOpen h U m y slots))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_eq_of_metric_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_eq_of_metric_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_eq_of_metric_eventuallyEq ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_eq_of_metric_eventuallyEq

theorem curvDerivNorm_eq_of_metric_eventuallyEq
    (g h : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner y v w) (m : ℕ) :
    curvDerivNorm m g x = curvDerivNorm m h x := by
  obtain ⟨s, hs, hopen, hxs⟩ := mem_nhds_iff.mp hmetric
  let U : _root_.TopologicalSpace.Opens M := ⟨s, hopen⟩
  let y : U := ⟨x, hxs⟩
  have heq : g.restrictOpen U = h.restrictOpen U :=
    SmoothRiemannianMetric.ext_inner (fun z v w => hs z.property v w)
  exact (curvDerivNorm_restrictOpen g U m y).symm.trans
    ((congrArg (fun k : SmoothRiemannianMetric I U => curvDerivNorm m k y) heq).trans
      (curvDerivNorm_restrictOpen h U m y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_metric_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_metric_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_metric_eventuallyEq ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_eq_of_metric_eventuallyEq

theorem curvDerivNormSq_eq_of_metric_eventuallyEq
    (g h : SmoothRiemannianMetric I M) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace I y,
      g.inner y v w = h.inner y v w) (m : ℕ) :
    curvDerivNormSq m g x = curvDerivNormSq m h x := by
  have hh := congrArg (fun t : ℝ => t ^ 2)
    (curvDerivNorm_eq_of_metric_eventuallyEq g h x hmetric m)
  simpa only [curvDerivNorm, curvDerivNormSq,
    Real.sq_sqrt (Tensor0SBundle.normSq0S_nonneg _ _ _ _)] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_eq_of_metric_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_eq_of_metric_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_eq_of_metric_eventuallyEq ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_eq_of_metric_eventuallyEq


end DifferentialGeometry.CheegerGromovCompactness
