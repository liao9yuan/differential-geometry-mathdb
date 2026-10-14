/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SmoothAnnulusCollar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TwoHandleAlignment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isSmoothHandleStage_adjunction_two
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (ψ : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1} → M)
    (hψ : _root_.Topology.IsClosedEmbedding ψ) (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ → M)
    (hf : _root_.Manifold.IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ f)
    (hfbd : _root_.Set.range f ⊆ (𝓡∂ 3).boundary M)
    (hrange : _root_.Set.range ψ = f '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :
    IsSmoothHandleStage
      (AdjunctionSpace (Subtype.val : _ → stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \
          ψ '' {z | z.val.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1}) ∪
        adjunctionCell Subtype.val ψ ''
          {z | z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)}) := by
  obtain ⟨a, V, θ, Θ, ha, ha2, hV, hθV, hΘO, hΘθ, hθΘ, hΘf, hθs, hΘs⟩ :=
    exists_twoHandleCollar_of_isSmoothEmbedding f hf hfbd
  obtain ⟨Ext, g, hExt, hExtr, hExt1, hExt2, hg, hExtg⟩ :=
    exists_twoHandle_alignment ψ hψ f hf.isEmbedding hrange
  have hA : CompactSpace {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1} := hψ.compactSpace
  have hP : CompactSpace (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) :=
    isCompact_iff_compactSpace.mp ((isCompact_stdSimplex ℝ (Fin 3)).prod _root_.CompactIccSpace.isCompact_Icc)
  have hi : _root_.Topology.IsClosedEmbedding (Subtype.val : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1} → stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    continuous_subtype_val.isClosedEmbedding Subtype.val_injective
  have hExti : ∀ b, ‖(Ext b).1‖ = 1 ↔ b ∈ _root_.Set.range (Subtype.val :
      {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
        z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1} →
          stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    intro b
    rw [hExt1, Subtype.range_coe]
    exact ⟨fun h => ⟨h, b.2.2⟩, fun h => h.1⟩
  have hΘi : ∀ z : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1}, Θ (Ext z.val) = ψ z := by
    intro z
    rw [hExtg z, hΘf, ← hg z]
    congr 1
    exact Prod.ext rfl (by ring)
  have hstage := isSmoothHandleStage_adjunction_of_twoHandleCollar hi hψ hExt hExtr hExti ha
    ha2 hV hθV hΘO hΘθ hθΘ hΘi hθs hΘs
  have hFr : {b : (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) |
      |(Ext b).2| = 1} = {z | z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := by
    ext b
    change |(Ext b).2| = 1 ↔ b.val.1 ∈ stdSimplex ℝ (Fin 3) ∧ b.val.2 ∈ ({0, 1} : Set ℝ)
    rw [hExt2]
    simp only [_root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff]
    exact ⟨fun h => ⟨b.2.1, h⟩, fun h => h.2⟩
  have hRFr : ∀ z : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1},
      z ∉ {z : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
        z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1} |
          z.val.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1} →
      z.val ∈ {z : (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) |
        z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := z.2
    refine ⟨z.val.2.1, ?_⟩
    simp only [_root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff]
    by_contra hne
    push Not at hne
    exact hz ⟨h1, lt_of_le_of_ne h2 (Ne.symm hne.1), lt_of_le_of_ne h3 hne.2⟩
  rw [adjunctionLower_boundary_sdiff_union_eq hRFr, ← hFr]
  exact hstage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_two

end DifferentialGeometry.Topology.PiecewiseLinear
