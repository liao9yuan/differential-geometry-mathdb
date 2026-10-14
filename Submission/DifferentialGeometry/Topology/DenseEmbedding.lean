import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [WeaklyLocallyCompactSpace X] [T2Space Y] {f : X → Y}

open _root_.IsDenseInducing in
theorem IsDenseInducing.isOpen_range (hf : IsDenseInducing f) : IsOpen (_root_.Set.range f) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, rfl⟩
  obtain ⟨K, hK, hxK⟩ := _root_.WeaklyLocallyCompactSpace.exists_compact_mem_nhds x
  have h := hf.closure_image_mem_nhds hxK
  rw [(hK.image hf.continuous).isClosed.closure_eq] at h
  exact _root_.Filter.mem_of_superset h (_root_.Set.image_subset_range _ _)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsDenseInducing
  let env ← Lean.getEnv
  if env.contains `IsDenseInducing.isOpen_range then
    throwError "Refusing to shadow existing declaration IsDenseInducing.isOpen_range"
  Lean.modifyEnv fun env => Lean.addAlias env `IsDenseInducing.isOpen_range ``Submission.IsDenseInducing.isOpen_range

open _root_.IsDenseEmbedding in
theorem IsDenseEmbedding.isOpenEmbedding (hf : IsDenseEmbedding f) : _root_.Topology.IsOpenEmbedding f :=
  ⟨hf.isEmbedding, hf.isDenseInducing.isOpen_range⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsDenseEmbedding
  let env ← Lean.getEnv
  if env.contains `IsDenseEmbedding.isOpenEmbedding then
    throwError "Refusing to shadow existing declaration IsDenseEmbedding.isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `IsDenseEmbedding.isOpenEmbedding ``Submission.IsDenseEmbedding.isOpenEmbedding
