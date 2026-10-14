import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finite_horn_two_scale_lower_bound {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : _root_.Filter.Tendsto d _root_.Filter.atTop (nhds 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in _root_.Filter.atTop,
      c ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 := by
  obtain ⟨c, hc, hlower⟩ := H.curvature_distance_lower
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H 0
  refine ⟨c, hc, ?_⟩
  filter_upwards [(tendsto_order.1 hzero).2 delta hdelta] with i hi
  have hmem : ray.point (d i) ∈ H.subend 0 := by
    apply hball
    rw [ray.radial (d i) (hd i)]
    exact hi
  simpa only [ray.radial (d i) (hd i)] using hlower (ray.point (d i)) hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_lower_bound

theorem finite_horn_two_scale_comparison_of_upper_bound {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : _root_.Filter.Tendsto d _root_.Filter.atTop (nhds 0))
    (hupper : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in _root_.Filter.atTop,
      metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ C) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop,
      c ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 ∧
      metricScalarAt g (ray.point (d i)) * d i ^ 2 ≤ C := by
  obtain ⟨c, hc, hlower⟩ := finite_horn_two_scale_lower_bound H ray d hd hzero
  obtain ⟨C, hC, hupper⟩ := hupper
  refine ⟨c, _root_.Max.max C c, hc, le_max_right _ _, ?_⟩
  filter_upwards [hlower, hupper] with i hli hhi
  exact ⟨hli, hhi.trans (le_max_left _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison_of_upper_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison_of_upper_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison_of_upper_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_horn_two_scale_comparison_of_upper_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
