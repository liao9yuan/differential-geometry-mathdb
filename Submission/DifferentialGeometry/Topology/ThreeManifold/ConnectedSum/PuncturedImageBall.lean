import Submission.DifferentialGeometry.Topology.PuncturedConnected
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Piecewise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

section EuclideanRank

open _root_.Module

private theorem one_lt_rank_euclideanSpace {n : ℕ} (hn : 2 ≤ n) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
  have h : (2 : Cardinal) ≤ Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast hn
  exact lt_of_lt_of_le (by norm_num : (1 : Cardinal) < 2) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.one_lt_rank_euclideanSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.one_lt_rank_euclideanSpace target :: scope.openDecls } }

end EuclideanRank

namespace BallChart

section

variable {n : ℕ} {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem isPathConnected_punctured (c : BallChart n I M) [T2Space M] [ConnectedSpace M]
    (hn : 2 ≤ n) : IsPathConnected ((c.chart '' Metric.ball 0 1)ᶜ : Set M) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) H := I.toHomeomorph.symm.chartedSpace
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin n)) H M
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  exact isPathConnected_compl_image_ball c.chart.toOpenPartialHomeomorph (one_lt_rank_euclideanSpace hn)
    (fun z hz => c.closedBall_subset_source (Metric.closedBall_subset_closedBall (by norm_num) hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.isPathConnected_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.isPathConnected_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.isPathConnected_punctured ``Submission.DifferentialGeometry.Topology.BallChart.isPathConnected_punctured

theorem connectedSpace_punctured (c : BallChart n I M) [T2Space M] [ConnectedSpace M]
    (hn : 2 ≤ n) : ConnectedSpace c.Punctured :=
  isConnected_iff_connectedSpace.mp (c.isPathConnected_punctured hn).isConnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.connectedSpace_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.connectedSpace_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.connectedSpace_punctured ``Submission.DifferentialGeometry.Topology.BallChart.connectedSpace_punctured

theorem pathConnectedSpace_punctured (c : BallChart n I M) [T2Space M] [ConnectedSpace M]
    (hn : 2 ≤ n) : PathConnectedSpace c.Punctured :=
  isPathConnected_iff_pathConnectedSpace.mp (c.isPathConnected_punctured hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.pathConnectedSpace_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.pathConnectedSpace_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.pathConnectedSpace_punctured ``Submission.DifferentialGeometry.Topology.BallChart.pathConnectedSpace_punctured

end

section Three

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

instance instConnectedSpacePuncturedThree (c : BallChart 3 I M) [T2Space M] [ConnectedSpace M] :
    ConnectedSpace c.Punctured :=
  c.connectedSpace_punctured (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.instConnectedSpacePuncturedThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.instConnectedSpacePuncturedThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.instConnectedSpacePuncturedThree ``Submission.DifferentialGeometry.Topology.BallChart.instConnectedSpacePuncturedThree

instance instPathConnectedSpacePuncturedThree (c : BallChart 3 I M) [T2Space M] [ConnectedSpace M] :
    PathConnectedSpace c.Punctured :=
  c.pathConnectedSpace_punctured (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.instPathConnectedSpacePuncturedThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.instPathConnectedSpacePuncturedThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.instPathConnectedSpacePuncturedThree ``Submission.DifferentialGeometry.Topology.BallChart.instPathConnectedSpacePuncturedThree

end Three

end BallChart

end DifferentialGeometry.Topology
