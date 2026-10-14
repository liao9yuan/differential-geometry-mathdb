import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.DiagonalCylinderDistance
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.BoundedCrossAngle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval}

theorem ShrinkingCylinderCover.tendsto_rays_comparisonAngle_zero_of_diagonalModel
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) (p : P.M)
    (a b : ℝ≥0 → P.M)
    (ha : ∀ s, metricDistance (P.S.base.metric 0) p (a s) = s)
    (hb : ∀ s, metricDistance (P.S.base.metric 0) p (b s) = s) :
    _root_.Filter.Tendsto (fun s : ℝ≥0 => Geometry.Comparison.Toponogov.comparisonAngle s s
      (metricDistance (P.S.base.metric 0) (a s) (b s))) _root_.Filter.atTop (𝓝 0) := by
  obtain ⟨B, _, hB⟩ := C.exists_cross_distance_bound_of_diagonalModel hdiag hbase p
  exact Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_bounded_cross_distance
    (fun _ => ENNReal.toReal_nonneg) (fun s => hB (a s) (b s) ((ha s).trans (hb s).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.tendsto_rays_comparisonAngle_zero_of_diagonalModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.tendsto_rays_comparisonAngle_zero_of_diagonalModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.tendsto_rays_comparisonAngle_zero_of_diagonalModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.tendsto_rays_comparisonAngle_zero_of_diagonalModel

theorem ShrinkingCylinderCover.not_eventually_comparisonAngle_lower_of_diagonalModel
    (C : ShrinkingCylinderCover P) (hdiag : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1) (p : P.M)
    (a b : ℝ≥0 → P.M)
    (ha : ∀ s, metricDistance (P.S.base.metric 0) p (a s) = s)
    (hb : ∀ s, metricDistance (P.S.base.metric 0) p (b s) = s)
    {theta : ℝ} (htheta : 0 < theta) :
    ¬ ∀ᶠ s : ℝ≥0 in _root_.Filter.atTop, theta ≤ Geometry.Comparison.Toponogov.comparisonAngle s s
      (metricDistance (P.S.base.metric 0) (a s) (b s)) := by
  intro hbound
  have hlim := C.tendsto_rays_comparisonAngle_zero_of_diagonalModel hdiag hbase p a b ha hb
  have hh : theta ≤ 0 := ge_of_tendsto hlim hbound
  exact (not_le_of_gt htheta) hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_eventually_comparisonAngle_lower_of_diagonalModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_eventually_comparisonAngle_lower_of_diagonalModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_eventually_comparisonAngle_lower_of_diagonalModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.not_eventually_comparisonAngle_lower_of_diagonalModel

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
