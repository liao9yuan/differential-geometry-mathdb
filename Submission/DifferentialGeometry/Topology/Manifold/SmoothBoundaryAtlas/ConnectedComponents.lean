import Submission.DifferentialGeometry.Topology.Manifold.ConnectedInterior
import Submission.DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import Submission.DifferentialGeometry.Topology.Connected.RegularClosedComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

theorem ambientChart_eq_zero_iff_mem_frontier (x : K) :
    C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K := by
  have h : (C.ambientChart x).toOpenPartialHomeomorph.IsImage K
      {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} := by
    intro y hy
    exact (C.mem_iff x y hy).symm
  have hf := h.frontier (C.mem_source x)
  rw [frontier_halfSpace] at hf
  change (0 = C.ambientChart x x.val 0 ↔ x.val ∈ frontier K) at hf
  exact eq_comm.trans hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.ambientChart_eq_zero_iff_mem_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.ambientChart_eq_zero_iff_mem_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.ambientChart_eq_zero_iff_mem_frontier ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.ambientChart_eq_zero_iff_mem_frontier

include C in
theorem isPreconnected_interior_connectedComponentIn
    (x : M) : IsPreconnected (interior (connectedComponentIn K x)) := by
  by_cases hx : x ∈ K
  · let _ := C.toChartedSpace
    let _ := C.isManifold
    let _ : LocallyConnectedSpace K :=
      ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace n) K
    have h := (Manifold.isPreconnected_manifold_interior_inter_connectedComponent
      (I := 𝓡∂ n) (⟨x, hx⟩ : K)).image Subtype.val continuous_subtype_val.continuousOn
    have heq : Subtype.val '' ((𝓡∂ n).interior K ∩ connectedComponent (⟨x, hx⟩ : K)) =
        interior (connectedComponentIn K x) := by
      rw [interior_connectedComponentIn_eq_inter, connectedComponentIn_eq_image hx,
        ← C.image_interior_subtype_val C.ambientChart_eq_zero_iff_mem_frontier,
        _root_.Set.image_inter Subtype.val_injective]
    exact heq ▸ h
  · rw [connectedComponentIn_eq_empty hx, interior_empty]
    exact isPreconnected_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isPreconnected_interior_connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.isPreconnected_interior_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.isPreconnected_interior_connectedComponentIn ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.isPreconnected_interior_connectedComponentIn
include C in
theorem connectedComponentIn_interior_eq_interior_connectedComponentIn
    {x : M} (hx : x ∈ interior K) :
    connectedComponentIn (interior K) x = interior (connectedComponentIn K x) := by
  let _ := C.toChartedSpace
  let _ := C.isManifold
  let _ : LocallyConnectedSpace K :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace n) K
  apply Subset.antisymm
  · rw [interior_connectedComponentIn_eq_inter]
    exact _root_.Set.subset_inter (connectedComponentIn_subset (interior K) x)
      (connectedComponentIn_mono x interior_subset)
  · apply (C.isPreconnected_interior_connectedComponentIn x).subset_connectedComponentIn
    · rw [interior_connectedComponentIn_eq_inter]
      exact ⟨hx, mem_connectedComponentIn (interior_subset hx)⟩
    · exact interior_mono (connectedComponentIn_subset K x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothBoundaryAtlas.connectedComponentIn_interior_eq_interior_connectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothBoundaryAtlas.connectedComponentIn_interior_eq_interior_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothBoundaryAtlas.connectedComponentIn_interior_eq_interior_connectedComponentIn ``Submission.DifferentialGeometry.Topology.SmoothBoundaryAtlas.connectedComponentIn_interior_eq_interior_connectedComponentIn

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
