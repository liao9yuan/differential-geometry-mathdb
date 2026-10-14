import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Embedding

open _root_.Set

theorem image_interior_of_isOpenEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding f) (A : Set X) :
    f '' interior A = interior (f '' A) := by
  have hpre : f ⁻¹' interior (f '' A) = interior A := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
      _root_.Set.preimage_image_eq _ hf.injective]
  rw [← hpre]
  exact _root_.Set.image_preimage_eq_of_subset (interior_subset.trans (_root_.Set.image_subset_range _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding

theorem image_frontier_of_isOpenEmbedding_of_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding f) {A : Set X}
    (hA : IsCompact A) : f '' frontier A = frontier (f '' A) := by
  have hpre : f ⁻¹' frontier (f '' A) = frontier A := by
    rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
      _root_.Set.preimage_image_eq _ hf.injective]
  rw [← hpre]
  exact _root_.Set.image_preimage_eq_of_subset
    ((hA.image hf.continuous).isClosed.frontier_subset.trans (_root_.Set.image_subset_range _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact ``Submission.DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact

end DifferentialGeometry.Topology.Embedding
