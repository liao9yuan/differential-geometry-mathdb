import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.ENNReal _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Toponogov

open _root_.Submission.DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def riemannianDistance (g : SmoothRiemannianMetric I M) (x y : M) : ℝ :=
  (riemannianEDistOf (I := I) g x y).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.riemannianDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.riemannianDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.riemannianDistance ``Submission.DifferentialGeometry.Toponogov.riemannianDistance

def riemannianComparisonAngle (g : SmoothRiemannianMetric I M)
    (x o y : M) : ℝ :=
  comparisonAngle (riemannianDistance (I := I) g o x)
    (riemannianDistance (I := I) g o y)
    (riemannianDistance (I := I) g x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.riemannianComparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.riemannianComparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.riemannianComparisonAngle ``Submission.DifferentialGeometry.Toponogov.riemannianComparisonAngle

theorem riemannianDistance_scale_sq (g : SmoothRiemannianMetric I M)
    {scale : ℝ} (hscale : 0 < scale) (x y : M) :
    riemannianDistance (I := I)
        (scaleMetric (I := I) (scale ^ 2) (sq_pos_of_pos hscale) g) x y =
      scale * riemannianDistance (I := I) g x y := by
  unfold riemannianDistance
  rw [edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg (scale ^ 2)),
    Real.sqrt_sq hscale.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.riemannianDistance_scale_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.riemannianDistance_scale_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.riemannianDistance_scale_sq ``Submission.DifferentialGeometry.Toponogov.riemannianDistance_scale_sq

theorem riemannianComparisonAngle_scale_sq
    (g : SmoothRiemannianMetric I M) {scale : ℝ} (hscale : 0 < scale)
    {x o y : M}
    (hox : 0 < riemannianDistance (I := I) g o x)
    (hoy : 0 < riemannianDistance (I := I) g o y) :
    riemannianComparisonAngle (I := I)
        (scaleMetric (I := I) (scale ^ 2) (sq_pos_of_pos hscale) g) x o y =
      riemannianComparisonAngle (I := I) g x o y := by
  unfold riemannianComparisonAngle
  rw [riemannianDistance_scale_sq (I := I) g hscale o x,
    riemannianDistance_scale_sq (I := I) g hscale o y,
    riemannianDistance_scale_sq (I := I) g hscale x y]
  exact comparisonAngle_scale hox hoy hscale

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.riemannianComparisonAngle_scale_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.riemannianComparisonAngle_scale_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.riemannianComparisonAngle_scale_sq ``Submission.DifferentialGeometry.Toponogov.riemannianComparisonAngle_scale_sq

end DifferentialGeometry.Toponogov
