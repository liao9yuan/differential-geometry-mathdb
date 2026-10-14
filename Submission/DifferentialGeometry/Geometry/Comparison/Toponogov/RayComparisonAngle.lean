import Submission.DifferentialGeometry.Geometry.Metric.RayDistance
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_comparisonAngle_zero_of_rays_near_common_points
    {X ι : Type*} [PseudoMetricSpace X] {f : Filter ι}
    {c d : ℝ≥0 → X} {p : X}
    (hc : Isometry c) (hd : Isometry d) (hc0 : c 0 = p) (hd0 : d 0 = p)
    (r : ι → ℝ≥0) (z : ι → X) (D : ι → ℝ)
    (hr : ∀ᶠ i in f, 0 < r i) (hz : ∀ᶠ i in f, _root_.Dist.dist p (z i) = r i)
    (hcross : ∀ᶠ i in f, ∃ s t : ℝ≥0,
      _root_.Dist.dist (c s) (z i) ≤ D i ∧ _root_.Dist.dist (d t) (z i) ≤ D i)
    (hthin : _root_.Filter.Tendsto (fun i => D i / (r i : ℝ)) f (𝓝 0)) :
    _root_.Filter.Tendsto (fun i => comparisonAngle (r i) (r i) (_root_.Dist.dist (c (r i)) (d (r i))))
      f (𝓝 0) := by
  have hbound : ∀ᶠ i in f, _root_.Dist.dist (c (r i)) (d (r i)) ≤ 4 * D i := by
    filter_upwards [hz, hcross] with i hzi hci
    obtain ⟨s, t, hs, ht⟩ := hci
    exact Geometry.Metric.dist_rays_le_of_near_common_point hc hd hc0 hd0
      (r i) s t hzi hs ht
  have hupper : _root_.Filter.Tendsto (fun i => 4 * (D i / (r i : ℝ))) f (𝓝 0) := by
    simpa only [_root_.MulZeroClass.mul_zero] using tendsto_const_nhds.mul hthin
  have hratio : _root_.Filter.Tendsto (fun i => _root_.Dist.dist (c (r i)) (d (r i)) / (r i : ℝ)) f (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun i => div_nonneg dist_nonneg (r i).coe_nonneg)
      (hbound.mono fun i hi => by
        have hh := div_le_div_of_nonneg_right hi (r i).coe_nonneg
        simpa only [mul_div_assoc] using hh) hupper
  have hangle := tendsto_comparisonAngle (a0 := (1 : ℝ)) (b0 := (1 : ℝ))
    tendsto_const_nhds tendsto_const_nhds hratio zero_lt_one zero_lt_one
  have heq : ∀ᶠ i in f,
      comparisonAngle 1 1 (_root_.Dist.dist (c (r i)) (d (r i)) / (r i : ℝ)) =
        comparisonAngle (r i) (r i) (_root_.Dist.dist (c (r i)) (d (r i))) := by
    filter_upwards [hr] with i hri
    have hrpos : 0 < (r i : ℝ) := hri
    simpa only [inv_mul_cancel₀ hrpos.ne', ← div_eq_mul_inv, mul_comm] using
      comparisonAngle_scale (r i) (r i) (_root_.Dist.dist (c (r i)) (d (r i)))
        (inv_pos.mpr hrpos)
  have hzero : comparisonAngle 1 1 0 = 0 := by
    simpa only [sub_self, abs_zero] using comparisonAngle_abs_sub zero_lt_one zero_lt_one
  change _root_.Filter.Tendsto (fun i => comparisonAngle 1 1 (_root_.Dist.dist (c (r i)) (d (r i)) / (r i : ℝ)))
    f (𝓝 (comparisonAngle 1 1 0)) at hangle
  rw [hzero] at hangle
  exact hangle.congr' heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_rays_near_common_points then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_rays_near_common_points"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_rays_near_common_points ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_rays_near_common_points

end DifferentialGeometry.Geometry.Comparison.Toponogov
