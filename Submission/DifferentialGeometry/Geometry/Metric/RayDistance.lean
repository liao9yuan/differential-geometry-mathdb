import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open scoped _root_.NNReal

namespace DifferentialGeometry.Geometry.Metric

theorem dist_rays_le_of_near_common_point
    {X : Type*} [PseudoMetricSpace X] {c d : ℝ≥0 → X} {p z : X}
    (hc : Isometry c) (hd : Isometry d) (hc0 : c 0 = p) (hd0 : d 0 = p)
    (r s t : ℝ≥0) {D : ℝ} (hr : _root_.Dist.dist p z = r)
    (hs : _root_.Dist.dist (c s) z ≤ D) (ht : _root_.Dist.dist (d t) z ≤ D) :
    dist (c r) (d r) ≤ 4 * D := by
  have hcs : _root_.Dist.dist (c s) p = (s : ℝ) := by
    rw [← hc0, hc.dist_eq, NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero, abs_of_nonneg s.coe_nonneg]
  have hdt : _root_.Dist.dist (d t) p = (t : ℝ) := by
    rw [← hd0, hd.dist_eq, NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
  have hsr : |(s : ℝ) - r| ≤ D := by
    have hh := (abs_dist_sub_le (c s) z p).trans hs
    simpa only [hcs, dist_comm z p, hr] using hh
  have htr : |(t : ℝ) - r| ≤ D := by
    have hh := (abs_dist_sub_le (d t) z p).trans ht
    simpa only [hdt, dist_comm z p, hr] using hh
  have hcrs : _root_.Dist.dist (c r) (c s) ≤ D := by
    simpa only [hc.dist_eq, NNReal.dist_eq, abs_sub_comm] using hsr
  have hdtr : _root_.Dist.dist (d t) (d r) ≤ D := by
    simpa only [hd.dist_eq, NNReal.dist_eq] using htr
  have hzdt : _root_.Dist.dist z (d t) ≤ D := by simpa only [dist_comm] using ht
  calc
    dist (c r) (d r) ≤ _root_.Dist.dist (c r) z + _root_.Dist.dist z (d r) := dist_triangle _ _ _
    _ ≤ (_root_.Dist.dist (c r) (c s) + _root_.Dist.dist (c s) z) + (_root_.Dist.dist z (d t) + _root_.Dist.dist (d t) (d r)) :=
      add_le_add (dist_triangle _ _ _) (dist_triangle _ _ _)
    _ ≤ 4 * D := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.dist_rays_le_of_near_common_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.dist_rays_le_of_near_common_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.dist_rays_le_of_near_common_point ``Submission.DifferentialGeometry.Geometry.Metric.dist_rays_le_of_near_common_point

end DifferentialGeometry.Geometry.Metric
