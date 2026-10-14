/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

theorem closure_preimage_subtype_val_of_frontier_subset
    {X : Type*} [TopologicalSpace X] {A Y : Set X} (h : frontier A ⊆ interior Y) :
    closure (((↑) : Y → X) ⁻¹' A) = ((↑) : Y → X) ⁻¹' closure A := by
  rw [_root_.Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
    Subtype.image_preimage_coe]
  apply Subset.antisymm (_root_.Set.preimage_mono (closure_mono _root_.Set.inter_subset_right))
  intro x hx
  by_cases hxA : (x : X) ∈ A
  · exact subset_closure ⟨x.property, hxA⟩
  · exact closure_mono (_root_.Set.inter_subset_inter_left _ interior_subset)
      (isOpen_interior.inter_closure ⟨h ⟨hx, fun hi => hxA (interior_subset hi)⟩, hx⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closure_preimage_subtype_val_of_frontier_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closure_preimage_subtype_val_of_frontier_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closure_preimage_subtype_val_of_frontier_subset ``Submission.DifferentialGeometry.Topology.closure_preimage_subtype_val_of_frontier_subset

end DifferentialGeometry.Topology
