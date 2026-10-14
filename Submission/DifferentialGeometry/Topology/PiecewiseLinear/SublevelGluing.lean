/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.SlabBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_frontier_sublevel_of_slab (I : SchoenfliesInput)
    {P : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsClosed P)
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {a b : ℝ} (hab : a < b)
    (hleft : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' _root_.Set.Iic a)))
    (hslab : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' _root_.Set.Icc a b)))
    {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (P ∩ {x | ℓ x = a}))
    (hgb : g '' stdSimplexBoundary 2 = frontier P ∩ {x | ℓ x = a}) :
    IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' _root_.Set.Iic b)) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => f x) h
  have h := I.isSimplyEmbedded_union_sdiff_diskInterior _ _ _ g ℓ.toLinearMap a
    hleft hslab hg hlinear _root_.Set.inter_subset_right (Topology.frontier_sublevel_inter_frontier_slab hP ℓ
        hℓ hab.le)
  rw [hgb] at h
  rwa [Topology.frontier_sublevel_slab_union_sdiff hP ℓ hℓ hab] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_sublevel_of_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_sublevel_of_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_sublevel_of_slab ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_sublevel_of_slab

theorem isSimplyEmbedded_frontier_of_sublevel_superlevel (I : SchoenfliesInput)
    {P : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsClosed P)
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (a : ℝ)
    (hleft : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' _root_.Set.Iic a)))
    (hright : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' _root_.Set.Ici a)))
    {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (P ∩ {x | ℓ x = a}))
    (hgb : g '' stdSimplexBoundary 2 = frontier P ∩ {x | ℓ x = a}) :
    IsSimplyEmbedded (frontier P) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => f x) h
  have h := I.isSimplyEmbedded_union_sdiff_diskInterior _ _ _ g ℓ.toLinearMap a
    hleft hright hg hlinear _root_.Set.inter_subset_right (Topology.frontier_sublevel_inter_frontier_superlevel
        hP ℓ hℓ a)
  rw [hgb] at h
  rwa [Topology.frontier_sublevel_union_superlevel_sdiff hP ℓ hℓ a] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_of_sublevel_superlevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_of_sublevel_superlevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_of_sublevel_superlevel ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isSimplyEmbedded_frontier_of_sublevel_superlevel

end DifferentialGeometry.Topology.PiecewiseLinear
