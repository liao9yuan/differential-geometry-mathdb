import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionRegions
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import Submission.DifferentialGeometry.Topology.Connected.CompactRegion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalSolidTorus.isConnected_frontier
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsTopologicalSolidTorus T)
    (hclosed : IsClosed T) : IsConnected (frontier T) := by
  obtain ⟨φ⟩ := hT.nonempty_homeomorph_frontier hclosed
  let _ : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  exact isConnected_iff_connectedSpace.mpr (φ.connectedSpace_iff.mpr inferInstance)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_frontier

theorem IsTopologicalSolidTorus.interior_nonempty
    {T : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsTopologicalSolidTorus T) :
    (interior T).Nonempty := by
  obtain ⟨φ⟩ := hT
  obtain ⟨z, hz⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let v : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨0, by simp⟩
  exact ⟨φ.symm (v, ⟨z, hz⟩),
    mem_interior_of_homeomorph_closedBall_prod_sphere φ v ⟨z, hz⟩ (by simp [v])⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.interior_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.interior_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.interior_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.interior_nonempty

theorem IsTopologicalSolidTorus.isConnected_compl_of_combinatorial_manifold
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hT : IsTopologicalSolidTorus K.space)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) : IsConnected K.spaceᶜ := by
  exact (isConnected_interior_space_and_compl (Set.toFinite K.faces) hK
    (hT.isConnected_frontier (isPolyhedron_space K).isClosed) hT.interior_nonempty).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_compl_of_combinatorial_manifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_compl_of_combinatorial_manifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_compl_of_combinatorial_manifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.isConnected_compl_of_combinatorial_manifold

theorem IsTopologicalSolidTorus.exists_isPLBall_subset_of_sphere
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} [Finite K.faces]
    (hT : IsTopologicalSolidTorus K.space)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S) (hST : S ⊆ K.space) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 B ∧ frontier B = S ∧ B ⊆ K.space := by
  obtain ⟨B, hB, hfront, -⟩ := hS.exists_isPLBall_frontier_eq
  refine ⟨B, hB, hfront, ?_⟩
  exact DifferentialGeometry.Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
    hB.isPolyhedron.isCompact (isPolyhedron_space K).isCompact
    (hT.isConnected_compl_of_combinatorial_manifold hK).isPreconnected (hfront ▸ hST)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.exists_isPLBall_subset_of_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.exists_isPLBall_subset_of_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.exists_isPLBall_subset_of_sphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus.exists_isPLBall_subset_of_sphere

end DifferentialGeometry.Topology.PiecewiseLinear
