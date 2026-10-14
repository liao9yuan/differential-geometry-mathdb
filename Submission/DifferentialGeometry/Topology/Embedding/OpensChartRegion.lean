import Submission.DifferentialGeometry.Topology.Embedding.CompactFrontier
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Embedding

open _root_.Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (O : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y) (e : O ≃ₜ V)

theorem interior_opens_chart_image (A : Set X) :
    interior ((fun p : O ↦ (e p : Y)) '' ((Subtype.val : O → X) ⁻¹' A)) =
      (fun p : O ↦ (e p : Y)) '' ((Subtype.val : O → X) ⁻¹' interior A) := by
  have hf : _root_.Topology.IsOpenEmbedding (fun p : O ↦ (e p : Y)) :=
    V.isOpenEmbedding'.comp e.isOpenEmbedding
  rw [← image_interior_of_isOpenEmbedding hf,
    ← O.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
      continuous_subtype_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.interior_opens_chart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.interior_opens_chart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.interior_opens_chart_image ``Submission.DifferentialGeometry.Topology.Embedding.interior_opens_chart_image

theorem frontier_opens_chart_image [T2Space Y] {A : Set X}
    (hA : IsCompact A) (hAO : A ⊆ O) :
    frontier ((fun p : O ↦ (e p : Y)) '' ((Subtype.val : O → X) ⁻¹' A)) =
      (fun p : O ↦ (e p : Y)) '' ((Subtype.val : O → X) ⁻¹' frontier A) := by
  have hcompact : IsCompact ((Subtype.val : O → X) ⁻¹' A) :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hA
      (fun x hx ↦ ⟨⟨x, hAO hx⟩, rfl⟩)
  have hf : _root_.Topology.IsOpenEmbedding (fun p : O ↦ (e p : Y)) :=
    V.isOpenEmbedding'.comp e.isOpenEmbedding
  rw [← image_frontier_of_isOpenEmbedding_of_isCompact hf hcompact,
    ← O.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.frontier_opens_chart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.frontier_opens_chart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.frontier_opens_chart_image ``Submission.DifferentialGeometry.Topology.Embedding.frontier_opens_chart_image

theorem closure_interior_opens_chart_image [T2Space Y] {A : Set X}
    (hA : IsCompact A) (hAO : A ⊆ O) (hreg : closure (interior A) = A) :
    closure (interior
      ((fun p : O ↦ (e p : Y)) '' ((Subtype.val : O → X) ⁻¹' A))) =
      (fun p : O ↦ (e p : Y)) '' ((Subtype.val : O → X) ⁻¹' A) := by
  let f : O → Y := fun p ↦ (e p : Y)
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hcompact : IsCompact ((Subtype.val : O → X) ⁻¹' A) :=
    _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hA
      (fun x hx ↦ ⟨⟨x, hAO hx⟩, rfl⟩)
  apply subset_antisymm
  · exact closure_minimal interior_subset (hcompact.image hf).isClosed
  · rw [interior_opens_chart_image]
    have hpre : (Subtype.val : O → X) ⁻¹' A =
        closure ((Subtype.val : O → X) ⁻¹' interior A) := by
      rw [← O.isOpenEmbedding'.isOpenMap.preimage_closure_eq_closure_preimage
        continuous_subtype_val, hreg]
    calc
      f '' ((Subtype.val : O → X) ⁻¹' A) =
          f '' closure ((Subtype.val : O → X) ⁻¹' interior A) := congrArg (f '' ·) hpre
      _ ⊆ closure (f '' ((Subtype.val : O → X) ⁻¹' interior A)) :=
        image_closure_subset_closure_image hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.closure_interior_opens_chart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.closure_interior_opens_chart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.closure_interior_opens_chart_image ``Submission.DifferentialGeometry.Topology.Embedding.closure_interior_opens_chart_image

theorem isPreconnected_interior_opens_chart_image {A : Set X}
    (hA : IsPreconnected (interior A)) (hAO : interior A ⊆ O) :
    IsPreconnected (interior
      ((fun p : O ↦ (e p : Y)) '' ((Subtype.val : O → X) ⁻¹' A))) := by
  rw [interior_opens_chart_image]
  exact (hA.preimage_of_isOpenMap Subtype.val_injective O.isOpenEmbedding'.isOpenMap
    (fun x hx ↦ ⟨⟨x, hAO hx⟩, rfl⟩)).image _
      (continuous_subtype_val.comp e.continuous).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Embedding.isPreconnected_interior_opens_chart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Embedding.isPreconnected_interior_opens_chart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Embedding.isPreconnected_interior_opens_chart_image ``Submission.DifferentialGeometry.Topology.Embedding.isPreconnected_interior_opens_chart_image

end DifferentialGeometry.Topology.Embedding
