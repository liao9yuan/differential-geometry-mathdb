import Submission.DifferentialGeometry.Geometry.Metric.ConeDistance
import Submission.DifferentialGeometry.Topology.MetricSpace.ContinuousDistance
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set

namespace Metric

def ConeAnnulus (a b : ℝ) (Y : Type*) := _root_.Set.Icc a b × Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.ConeAnnulus then
    throwError "Refusing to shadow existing declaration Metric.ConeAnnulus"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.ConeAnnulus ``Submission.Metric.ConeAnnulus

instance ConeAnnulus.instTopologicalSpace (a b : ℝ) (Y : Type*) [TopologicalSpace Y] :
    TopologicalSpace (ConeAnnulus a b Y) := inferInstanceAs (TopologicalSpace (_root_.Set.Icc a b × Y))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Metric.ConeAnnulus
  let env ← Lean.getEnv
  if env.contains `Metric.ConeAnnulus.instTopologicalSpace then
    throwError "Refusing to shadow existing declaration Metric.ConeAnnulus.instTopologicalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.ConeAnnulus.instTopologicalSpace ``Submission.Metric.ConeAnnulus.instTopologicalSpace

instance ConeAnnulus.instCompactSpace (a b : ℝ) (Y : Type*) [TopologicalSpace Y]
    [CompactSpace Y] : CompactSpace (ConeAnnulus a b Y) :=
  inferInstanceAs (CompactSpace (_root_.Set.Icc a b × Y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.ConeAnnulus.instCompactSpace then
    throwError "Refusing to shadow existing declaration Metric.ConeAnnulus.instCompactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.ConeAnnulus.instCompactSpace ``Submission.Metric.ConeAnnulus.instCompactSpace

end Metric
