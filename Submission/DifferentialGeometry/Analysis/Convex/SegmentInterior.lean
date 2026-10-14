/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Convex.Topology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

open _root_.Convex in
theorem Convex.openSegment_subset_interior_or_disjoint {C : Set E} (hC : Convex 𝕜 C)
    {p q : E} (hp : p ∈ C) (hq : q ∈ C) :
    openSegment 𝕜 p q ⊆ interior C ∨ Disjoint (openSegment 𝕜 p q) (interior C) := by
  by_cases hmeet : (openSegment 𝕜 p q ∩ interior C).Nonempty
  · obtain ⟨z, hz, hzC⟩ := hmeet
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t, -, rfl⟩ := hz
    exact Or.inl ((openSegment_subset_union p q ⟨t, rfl⟩).trans
      (insert_subset_iff.mpr ⟨hzC, _root_.Set.union_subset
        (hC.openSegment_self_interior_subset_interior hp hzC)
        (hC.openSegment_interior_self_subset_interior hzC hq)⟩))
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Convex
  let env ← Lean.getEnv
  if env.contains `Convex.openSegment_subset_interior_or_disjoint then
    throwError "Refusing to shadow existing declaration Convex.openSegment_subset_interior_or_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `Convex.openSegment_subset_interior_or_disjoint ``Submission.Convex.openSegment_subset_interior_or_disjoint
