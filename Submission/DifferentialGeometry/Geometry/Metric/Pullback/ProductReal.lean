import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Euclidean
import Submission.DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem Diffeomorph.pullbackMetric_euclidean_translation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (c : E) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := E))
      (Topology.translateDiffeomorph c) = euclideanMetric := by
  have hd (x : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (Topology.translateDiffeomorph c) x = ContinuousLinearMap.id ℝ E := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun y : E => y + c) x = ContinuousLinearMap.id ℝ E
    exact ((hasFDerivAt_id x).add_const c).fderiv
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner, hd, euclideanMetric_inner, euclideanMetric_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_translation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_translation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_translation ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem Diffeomorph.pullbackMetricCross_prod_real_translation
    (g : SmoothRiemannianMetric I M) (c : ℝ) :
    Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ)))
      ((Diffeomorph.refl I M ∞).prodCongr (Topology.translateDiffeomorph c)) =
        g.prod (euclideanMetric (E := ℝ)) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl,
    Diffeomorph.pullbackMetric_euclidean_translation]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_translation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_translation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_translation ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_translation

theorem Diffeomorph.pullbackMetricCross_prod_real_reflection
    (g : SmoothRiemannianMetric I M) :
    Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ)))
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv.toDiffeomorph) =
      g.prod (euclideanMetric (E := ℝ)) := by
  rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl,
    LinearIsometryEquiv.pullbackMetric_euclidean]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_reflection ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_prod_real_reflection

end DifferentialGeometry
