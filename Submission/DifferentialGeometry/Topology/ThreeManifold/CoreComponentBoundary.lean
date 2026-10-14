import Submission.DifferentialGeometry.Topology.ThreeManifold.CoreComponentGeometry
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapUncutComponentRealization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

include C in
theorem exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent
    (x : T.core) :
    (∃ (b : T.Boundary) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      T.coreBoundarySphere b q ∈ connectedComponent x) ∨
      Subtype.val '' connectedComponent x = connectedComponent x.val := by
  classical
  by_cases h : ∃ (b : T.Boundary) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      T.coreBoundarySphere b q ∈ connectedComponent x
  · exact Or.inl h
  right
  obtain ⟨_, hconn, _, _, hfront⟩ := C.coreComponent_geometry x
  have hfrontempty : frontier (Subtype.val '' connectedComponent x) = ∅ := by
    rw [hfront]
    apply iUnion_eq_empty.mpr
    intro b
    exact (h ⟨b.val, b.property⟩).elim
  have hcl := isClopen_iff_frontier_eq_empty.mpr hfrontempty
  have hx : x.val ∈ Subtype.val '' connectedComponent x :=
    ⟨x, mem_connectedComponent, rfl⟩
  exact Subset.antisymm (hconn.isPreconnected.subset_connectedComponent hx)
    (hcl.connectedComponent_subset hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCapping.exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCapping.exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCapping.exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent ``Submission.DifferentialGeometry.Topology.SphericalCapping.exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent

end DifferentialGeometry.Topology.SphericalCapping

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty
    (x : E.tubes.core) :
    (∃ (b : E.tubes.Boundary) (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      E.tubes.coreBoundarySphere b q ∈ connectedComponent x) ∨
      E.cutIndices (ConnectedComponents.mk x.val) = ∅ := by
  rcases E.capping.exists_boundarySphere_mem_coreComponent_or_image_eq_connectedComponent x with h | h
  · exact Or.inl h
  right
  have hcore : connectedComponent x.val ⊆ E.tubes.core := by
    rw [← h]
    rintro z ⟨y, _, rfl⟩
    exact y.property
  apply (E.cutIndices_eq_empty_iff _).mpr
  rintro j ⟨q, hq⟩
  let q₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × _root_.Set.Icc (-2 : ℝ) 2 :=
    (q₀, ⟨0, by norm_num⟩)
  have hzcomp : E.tubes.tube j z ∈ connectedComponent x.val := by
    have htube := (E.tubes.isPreconnected_range_tube j).subset_connectedComponent
      (_root_.Set.mem_range_self q) (_root_.Set.mem_range_self z)
    rw [ClosedOrientedManifold.componentSet_mk] at hq
    rwa [← connectedComponent_eq hq] at htube
  exact hcore hzcomp (mem_iUnion.mpr ⟨j, z, by norm_num [z], rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.exists_boundarySphere_mem_coreComponent_or_cutIndices_eq_empty

end DifferentialGeometry.Topology.SphericalCutCapTransition
