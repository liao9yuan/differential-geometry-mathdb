import Submission.DifferentialGeometry.Topology.Embedding.CompactFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology

namespace DifferentialGeometry.Topology.Embedding

theorem interior_image_of_isOpenEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding f) (A : Set X) :
    interior (f '' A) = f '' interior A :=
  (image_interior_of_isOpenEmbedding hf A).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding

theorem frontier_image_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsEmbedding f) (A : Set X) :
    frontier (f '' A) = f '' frontier A ∪ (frontier (_root_.Set.range f) ∩ closure (f '' A)) := by
  have hsub : f '' A ⊆ _root_.Set.range f := by
    rintro y ⟨x, _, hxy⟩
    exact ⟨x, hxy⟩
  apply Subset.antisymm
  · intro y hy
    by_cases hr : y ∈ frontier (_root_.Set.range f)
    · exact Or.inr ⟨hr, hy.1⟩
    · have hri : y ∈ interior (_root_.Set.range f) := by
        by_contra h
        exact hr ⟨closure_mono hsub hy.1, h⟩
      obtain ⟨x, rfl⟩ := interior_subset hri
      have hxc : x ∈ closure A := by
        rw [hf.closure_eq_preimage_closure_image]
        exact hy.1
      refine Or.inl ⟨x, ⟨hxc, ?_⟩, rfl⟩
      intro hxi
      have hn : f '' A ∈ Filter.map f (𝓝 x) :=
        Filter.image_mem_map (mem_interior_iff_mem_nhds.mp hxi)
      rw [hf.map_nhds_of_mem x (mem_interior_iff_mem_nhds.mp hri)] at hn
      exact hy.2 (mem_interior_iff_mem_nhds.mpr hn)
  · rintro y (⟨x, hx, rfl⟩ | ⟨hr, hc⟩)
    · refine ⟨image_closure_subset_closure_image hf.continuous ⟨x, hx.1, rfl⟩, ?_⟩
      intro hi
      have hxi : x ∈ interior (f ⁻¹' (f '' A)) :=
        preimage_interior_subset_interior_preimage hf.continuous hi
      rw [hf.injective.preimage_image] at hxi
      exact hx.2 hxi
    · exact ⟨hc, fun hi ↦ hr.2 (interior_mono hsub hi)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.frontier_image_of_isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.frontier_image_of_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.frontier_image_of_isEmbedding ``Submission.DifferentialGeometry.Topology.Embedding.frontier_image_of_isEmbedding

theorem frontier_image_subset_of_isEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : _root_.Topology.IsEmbedding f) (A : Set X) :
    frontier (f '' A) ⊆ frontier (_root_.Set.range f) ∪ f '' frontier A := by
  rw [frontier_image_of_isEmbedding hf A]
  exact _root_.Set.union_subset _root_.Set.subset_union_right (inter_subset_left.trans _root_.Set.subset_union_left)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.frontier_image_subset_of_isEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.frontier_image_subset_of_isEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.frontier_image_subset_of_isEmbedding ``Submission.DifferentialGeometry.Topology.Embedding.frontier_image_subset_of_isEmbedding

end DifferentialGeometry.Topology.Embedding

open _root_.Topology _root_.Topology.IsOpenEmbedding in
theorem Topology.IsOpenEmbedding.frontier_insert_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) {q : Y} (hq : q ∉ _root_.Set.range f)
    {S : Set X} (hclosed : IsClosed (_root_.Insert.insert q (f '' S)))
    (hnhds : _root_.Insert.insert q (f '' S) ∈ 𝓝 q) :
    frontier (_root_.Insert.insert q (f '' S)) = f '' frontier S := by
  have hpre : f ⁻¹' _root_.Insert.insert q (f '' S) = S := by
    ext x
    simp only [_root_.Set.mem_preimage, _root_.Set.mem_insert_iff, hf.injective.mem_set_image]
    exact or_iff_right (fun hx => hq ⟨x, hx⟩)
  have hfront := hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous (_root_.Insert.insert q (f '' S))
  rw [hpre] at hfront
  apply Subset.antisymm
  · intro y hy
    rcases hclosed.frontier_subset hy with rfl | hyS
    · exact False.elim (hy.2 (mem_interior_iff_mem_nhds.mpr hnhds))
    · obtain ⟨x, _, rfl⟩ := hyS
      exact ⟨x, hfront ▸ hy, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    change x ∈ f ⁻¹' frontier (_root_.Insert.insert q (f '' S))
    rwa [hfront]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Topology
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Topology.IsOpenEmbedding
  let env ← Lean.getEnv
  if env.contains `Topology.IsOpenEmbedding.frontier_insert_image then
    throwError "Refusing to shadow existing declaration Topology.IsOpenEmbedding.frontier_insert_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsOpenEmbedding.frontier_insert_image ``Submission.Topology.IsOpenEmbedding.frontier_insert_image
