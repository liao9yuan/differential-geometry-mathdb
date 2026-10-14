import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import Submission.DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import Submission.DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.BallChart

variable {n : ℕ}


local instance _root_.Submission.DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat ``Submission.DifferentialGeometry.Topology.BallChart.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  (c : BallChart (n + 1) (𝓡 (n + 1)) M)

private def angularHeightChart (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ((_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) × ℝ) (EuclideanSpace ℝ (Fin (n + 1))) ∞ :=
  (PartialDiffeomorph.prod (PartialDiffeomorph.extendedChart (I := 𝓡 n) z)
    (translateDiffeomorph (-1 : ℝ)).toPartialDiffeomorph).trans
      (signedNormalFirstDiffeomorph n _root_.Bool.true).toPartialDiffeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.angularHeightChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.angularHeightChart target :: scope.openDecls } }

private def unrestrictedRadialBoundaryChart (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) M (EuclideanSpace ℝ (Fin (n + 1))) ∞ :=
  (c.chart.symm.trans (Manifold.spherePolarChart (n := n) z).symm).trans
    (angularHeightChart z)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.unrestrictedRadialBoundaryChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.unrestrictedRadialBoundaryChart target :: scope.openDecls } }

private theorem unrestrictedRadialBoundaryChart_zero (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (x : M) :
    unrestrictedRadialBoundaryChart c z x 0 = ‖c.chart.symm x‖ - 1 := by
  change signedNormalFirstEquiv n _root_.Bool.true (_, ‖c.chart.symm x‖ + -1) 0 = _
  rw [signedNormalFirstEquiv_zero]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.unrestrictedRadialBoundaryChart_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.unrestrictedRadialBoundaryChart_zero target :: scope.openDecls } }

private theorem chart_sphere_mem_unrestrictedRadialBoundaryChart_source (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    c.chart z ∈ (unrestrictedRadialBoundaryChart c z).source := by
  have hz : (z : (EuclideanSpace ℝ (Fin (n + 1)))) ∈ c.chart.source := c.sphere_subset_source z.property
  have hpoint : c.chart.symm (c.chart z) = (z : (EuclideanSpace ℝ (Fin (n + 1)))) := c.chart.left_inv hz
  change (c.chart z ∈ c.chart.target ∧ c.chart.symm (c.chart z) ≠ 0) ∧
    (Manifold.spherePolarChart (n := n) z).symm (c.chart.symm (c.chart z)) ∈
      (angularHeightChart z).source
  rw [hpoint]
  refine ⟨⟨c.chart.map_source hz, ne_zero_of_mem_unit_sphere z⟩, ?_⟩
  change ((Manifold.sphereDirection z z ∈ (extChartAt (𝓡 n) z).source ∧ True) ∧ True)
  have hs : Manifold.sphereDirection z (z : (EuclideanSpace ℝ (Fin (n + 1)))) = z := by
    simpa only [one_smul] using Manifold.sphereDirection_pos_smul z z zero_lt_one
  rw [hs]
  exact ⟨⟨mem_extChartAt_source z, trivial⟩, trivial⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.chart_sphere_mem_unrestrictedRadialBoundaryChart_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.chart_sphere_mem_unrestrictedRadialBoundaryChart_source target :: scope.openDecls } }

def radialBoundaryChart (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) M (EuclideanSpace ℝ (Fin (n + 1))) ∞ :=
  PartialDiffeomorph.restrict (unrestrictedRadialBoundaryChart c z)
    (c.chart '' _root_.Metric.ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 2)
    (c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source _root_.Metric.isOpen_ball
      (fun _ hx => c.closedBall_subset_source (_root_.Metric.ball_subset_closedBall hx)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.radialBoundaryChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.radialBoundaryChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.radialBoundaryChart ``Submission.DifferentialGeometry.Topology.BallChart.radialBoundaryChart

theorem chart_sphere_mem_radialBoundaryChart_source (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    c.chart z ∈ (c.radialBoundaryChart z).source := by
  refine ⟨chart_sphere_mem_unrestrictedRadialBoundaryChart_source c z, z, ?_, rfl⟩
  simp only [_root_.Metric.mem_ball, dist_zero_right, norm_eq_of_mem_sphere]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.chart_sphere_mem_radialBoundaryChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.chart_sphere_mem_radialBoundaryChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.chart_sphere_mem_radialBoundaryChart_source ``Submission.DifferentialGeometry.Topology.BallChart.chart_sphere_mem_radialBoundaryChart_source

theorem radialBoundaryChart_zero (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) (x : M) :
    c.radialBoundaryChart z x 0 = ‖c.chart.symm x‖ - 1 :=
  unrestrictedRadialBoundaryChart_zero c z x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero ``Submission.DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero

theorem radialBoundaryChart_source_subset_image_ball (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    (c.radialBoundaryChart z).source ⊆ c.chart '' _root_.Metric.ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 2 :=
  fun _ hx => hx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.radialBoundaryChart_source_subset_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.radialBoundaryChart_source_subset_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.radialBoundaryChart_source_subset_image_ball ``Submission.DifferentialGeometry.Topology.BallChart.radialBoundaryChart_source_subset_image_ball

theorem not_mem_ball_iff_radialBoundaryChart_nonneg (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) {x : M}
    (hx : x ∈ (c.radialBoundaryChart z).source) :
    x ∉ c.chart '' _root_.Metric.ball (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 ↔ 0 ≤ c.radialBoundaryChart z x 0 := by
  have hxt : x ∈ c.chart.target := hx.1.1.1
  rw [radialBoundaryChart_zero]
  constructor
  · intro h
    by_contra hn
    apply h
    refine ⟨c.chart.symm x, ?_, c.chart.right_inv hxt⟩
    rw [_root_.Metric.mem_ball, dist_zero_right]
    linarith [not_le.mp hn]
  · rintro h ⟨y, hy, rfl⟩
    change 0 ≤ ‖c.chart.symm (c.chart y)‖ - 1 at h
    have hn : ‖c.chart.symm (c.chart y)‖ = ‖y‖ :=
      congrArg _root_.Norm.norm (c.chart.left_inv (c.ball_subset_source hy))
    have hy1 : ‖y‖ < 1 := by simpa only [_root_.Metric.mem_ball, dist_zero_right] using hy
    linarith [hn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.not_mem_ball_iff_radialBoundaryChart_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.not_mem_ball_iff_radialBoundaryChart_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.not_mem_ball_iff_radialBoundaryChart_nonneg ``Submission.DifferentialGeometry.Topology.BallChart.not_mem_ball_iff_radialBoundaryChart_nonneg

theorem radialBoundaryChart_zero_iff_mem_sphere (z : (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) {x : M}
    (hx : x ∈ (c.radialBoundaryChart z).source) :
    c.radialBoundaryChart z x 0 = 0 ↔ x ∈ c.chart '' _root_.Metric.sphere (0 : (EuclideanSpace ℝ (Fin (n + 1)))) 1 := by
  have hxt : x ∈ c.chart.target := hx.1.1.1
  rw [radialBoundaryChart_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨c.chart.symm x, by simpa only [_root_.Metric.mem_sphere, dist_zero_right] using h,
      c.chart.right_inv hxt⟩
  · rintro ⟨y, hy, rfl⟩
    change ‖c.chart.symm (c.chart y)‖ = 1
    exact (congrArg _root_.Norm.norm (c.chart.left_inv (c.sphere_subset_source hy))).trans
      (by simpa only [_root_.Metric.mem_sphere, dist_zero_right] using hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero_iff_mem_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero_iff_mem_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero_iff_mem_sphere ``Submission.DifferentialGeometry.Topology.BallChart.radialBoundaryChart_zero_iff_mem_sphere

end DifferentialGeometry.Topology.BallChart
