import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import Submission.DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem liftedMetric_eq_localPullMetric
    (g : SmoothRiemannianMetric I M) :
    liftedMetric (I := I) g = localPullMetric g
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
      (proj_localDiffeo (I := I)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, (hasMFDerivAt_proj (I := I) x).mfderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_eq_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_eq_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_eq_localPullMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric_eq_localPullMetric

theorem normalizedGradientRicciSoliton_liftedMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f) :
    let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
    let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
    normalizedGradientRicciSoliton (I := I) (liftedMetric (I := I) g)
      (f.comp ⟨proj, proj_contMDiff (I := I)⟩) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have hc := liftedMetric_complete g h.1
  rw [liftedMetric_eq_localPullMetric] at hc ⊢
  exact normalizedGradientRicciSoliton_localPullMetric h (proj_localDiffeo (I := I)) hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normalizedGradientRicciSoliton_liftedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normalizedGradientRicciSoliton_liftedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normalizedGradientRicciSoliton_liftedMetric ``Submission.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.normalizedGradientRicciSoliton_liftedMetric

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
