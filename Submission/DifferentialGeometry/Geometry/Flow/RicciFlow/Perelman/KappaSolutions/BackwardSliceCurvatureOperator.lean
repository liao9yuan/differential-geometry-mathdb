import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backwardSliceLimit_curvatureOperator_nonnegative
    (F : PointedFlowData.{u, uE, uH} I D) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, uE, uH} I} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i) :
    ∀ x : L.M, metricAlgebraicCurvatureTensorAt L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) := by
  let _ : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 2 F.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 3 F.M := IsManifold.of_le (n := ∞) (by decide)
  apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence C hcanonical
  intro K _hK
  refine Eventually.of_forall fun i y _hy _hsource => ?_
  change metricAlgebraicCurvatureTensorAt
    (scaleMetric (tau (phi i))⁻¹ (inv_pos.mpr (htau (phi i)))
      (F.S.base.metric (-tau (phi i)))) (Phi.map i y) ∈ _
  rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
  apply algebraicCurvatureOperatorNonnegativeCone.smul_mem _ (inv_pos.mpr (htau (phi i))).le
  apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
  intro n c v w
  have htime : -tau (phi i) ∈ D.carrier := by
    rw [hF.carrier_eq]
    exact neg_nonpos.mpr (htau (phi i)).le
  have hh := hF.nonnegativeCurvatureOperator _ htime (Phi.map i y) n c v w
  simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
    tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_curvatureOperator_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_curvatureOperator_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_curvatureOperator_nonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardSliceLimit_curvatureOperator_nonnegative

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
