/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Analysis.Convex.CompactFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem exists_mem_frontier_apply_lt_iff {P : Set E} (hP : IsCompact P)
    (ℓ : E →L[ℝ] ℝ) (a : ℝ) :
    (∃ x ∈ frontier P, ℓ x < a) ↔ ∃ x ∈ P, ℓ x < a := by
  refine ⟨fun ⟨x, hx, hxa⟩ => ⟨x, hP.isClosed.frontier_subset hx, hxa⟩, ?_⟩
  rintro ⟨x, hx, hxa⟩
  by_contra h
  push Not at h
  have hsub : P ⊆ ℓ ⁻¹' _root_.Set.Ici a :=
    Analysis.IsCompact.subset_of_frontier_subset_convex_closed hP
      ((convex_Ici a).linear_preimage ℓ.toLinearMap) (isClosed_Ici.preimage ℓ.continuous) h
  exact hxa.not_ge (hsub hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_mem_frontier_apply_lt_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_mem_frontier_apply_lt_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_mem_frontier_apply_lt_iff ``Submission.DifferentialGeometry.Topology.exists_mem_frontier_apply_lt_iff

theorem exists_mem_frontier_lt_apply_iff {P : Set E} (hP : IsCompact P)
    (ℓ : E →L[ℝ] ℝ) (a : ℝ) :
    (∃ x ∈ frontier P, a < ℓ x) ↔ ∃ x ∈ P, a < ℓ x := by
  simpa only [neg_apply, neg_lt_neg_iff] using exists_mem_frontier_apply_lt_iff hP (-ℓ) (-a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_mem_frontier_lt_apply_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_mem_frontier_lt_apply_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_mem_frontier_lt_apply_iff ``Submission.DifferentialGeometry.Topology.exists_mem_frontier_lt_apply_iff

end DifferentialGeometry.Topology
