import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

def PointedCGHMaps.atTimeWithMetric
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps X P phi) (t : ℝ) (g : SmoothRiemannianMetric I P.M) :
    PointedRiemannianConvergenceMaps (X.atTime t)
      ({ P with metric := g } : PointedRiemannianManifold (I := I)) phi where
  partialDiffeomorph k := Phi.partialDiffeomorph k
  source_exhausts := Phi.source_exhausts
  base_mem k := Phi.base_mem k
  basepoint_map k := Phi.basepoint_map k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTimeWithMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTimeWithMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTimeWithMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.atTimeWithMetric

end DifferentialGeometry.CheegerGromovCompactness

end
