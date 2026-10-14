import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private local instance _root_.Submission.DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry (k : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Handle.instFactEqNatFinrankRealEuclideanSpaceFinHAddOfNat_differentialGeometry target :: scope.openDecls } }

theorem not_surjective_closedCell_of_isSmoothEmbedding (m : ℕ)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M]
    {n : ℕ∞ω} (hn : n ≠ 0) {u : ClosedCell (m + 1) → M}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) I n u) :
    ¬ Function.Surjective u := by
  let x : ClosedCell (m + 1) := ⟨EuclideanSpace.single 0 1, by simp⟩
  apply hu.not_surjective_of_isBoundaryPoint hn (x := x)
  change x ∈ (𝓡∂ (m + 1)).boundary (ClosedCell (m + 1))
  rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere]
  simp [x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.not_surjective_closedCell_of_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.not_surjective_closedCell_of_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.not_surjective_closedCell_of_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.Handle.not_surjective_closedCell_of_isSmoothEmbedding

theorem exists_stereographic_source_superset_range_closedCell (m k : ℕ)
    {n : ℕ∞ω} (hn : n ≠ 0)
    {u : ClosedCell (m + 1) → Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1}
    (hu : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 k) n u) :
    ∃ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
      Set.range u ⊆ (stereographic' k p).source := by
  obtain ⟨p, hp⟩ := not_forall.mp (not_surjective_closedCell_of_isSmoothEmbedding m hn hu)
  refine ⟨p, ?_⟩
  rintro y ⟨x, rfl⟩
  simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using
    (show u x ≠ p from fun h => hp ⟨x, h⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Handle.exists_stereographic_source_superset_range_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Handle.exists_stereographic_source_superset_range_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Handle.exists_stereographic_source_superset_range_closedCell ``Submission.DifferentialGeometry.Topology.Handle.exists_stereographic_source_superset_range_closedCell

end DifferentialGeometry.Topology.Handle
