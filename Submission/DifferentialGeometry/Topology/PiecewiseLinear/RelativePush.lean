/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSeparation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PushProperty

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem HasPushPropertyAt.exists_homeomorph_fixed_on_of_inter_subset
    {C D A U : Set (EuclideanSpace ℝ (Fin 3))} (hCD : HasPushPropertyAt C D)
    {f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D)
    (hA : IsPolyhedron A) (hCA : C ∩ A ⊆ f '' stdSimplexBoundary 2)
    (hdense : A ⊆ closure (A \ C)) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ h '' D = closure (frontier C \ D) ∧
      _root_.Set.EqOn h id A ∧ _root_.Set.EqOn h id Uᶜ ∧
      h '' (D ∪ A) = closure (frontier C \ D) ∪ A := by
  obtain ⟨N, hN, hCN, hNU, hNA⟩ :=
    exists_isPolyhedron_neighborhood_sdiff hCD.1.isPolyhedron hA hU hCU
  have hNbd : C \ (f '' stdSimplexBoundary 2) ⊆ interior N := by
    intro x hx
    exact hCN ⟨hx.1, fun hxA => hx.2 (hCA ⟨hx.1, hxA⟩)⟩
  obtain ⟨h, hh, hD, hfix⟩ := hCD.2.2.2 f hf N hN hNbd
  have hfix' : _root_.Set.EqOn h id (A \ C) := by
    intro x hx
    apply hfix
    intro hxN
    exact hx.2 ((hNA ▸ (show x ∈ N ∩ A from ⟨hxN, hx.1⟩)).1)
  have hfixA : _root_.Set.EqOn h id A := (hfix'.closure h.continuous continuous_id).mono hdense
  refine ⟨h, hh, hD, hfixA, fun x hx => hfix (fun hxN => hx (hNU hxN)), ?_⟩
  rw [_root_.Set.image_union, hD, hfixA.image_eq, _root_.Set.image_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.exists_homeomorph_fixed_on_of_inter_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.exists_homeomorph_fixed_on_of_inter_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.exists_homeomorph_fixed_on_of_inter_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.exists_homeomorph_fixed_on_of_inter_subset

end DifferentialGeometry.Topology.PiecewiseLinear
