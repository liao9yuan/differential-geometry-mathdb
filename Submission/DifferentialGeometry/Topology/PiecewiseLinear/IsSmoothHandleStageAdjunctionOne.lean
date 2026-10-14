/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OneHandleAlignment
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SmoothDiskPairCollar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

noncomputable def planarReflectionDiffeomorph :
    Diffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) ∞ where
  toEquiv := planarReflection.toLinearEquiv.toEquiv
  contMDiff_toFun := planarReflection.toContinuousLinearEquiv.contDiff.contMDiff
  contMDiff_invFun := planarReflection.symm.toContinuousLinearEquiv.contDiff.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.planarReflectionDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.planarReflectionDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.planarReflectionDiffeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.planarReflectionDiffeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isSmoothHandleStage_adjunction_one
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (ψ : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} → M)
    (hψ : _root_.Topology.IsClosedEmbedding ψ) (f : Fin 2 → EuclideanSpace ℝ (Fin 2) → M)
    (hf : ∀ j, _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (f j))
    (hfbd : ∀ j, _root_.Set.range (f j) ⊆ (𝓡∂ 3).boundary M)
    (hdisj : Disjoint (_root_.Set.range (f 0)) (_root_.Set.range (f 1)))
    (hrange : _root_.Set.range ψ = ⋃ j, f j '' Metric.closedBall 0 1) :
    IsSmoothHandleStage
      (AdjunctionSpace (Subtype.val : _ → stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \
          ψ '' {z | z.val.val ∈ (stdSimplex ℝ (Fin 3) \ stdSimplexBoundary 2) ×ˢ
            ({0, 1} : Set ℝ)}) ∪
        adjunctionCell Subtype.val ψ '' {z | z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1}) := by
  classical
  obtain ⟨Fb, Ft, hFF, hb, ht⟩ := exists_oneHandle_end_assignment ψ hψ.continuous f
    (fun j => (hf j).contMDiff.continuous) hdisj hrange
  have hFbS : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ Fb := by
    rcases hFF with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hf 0
    · exact hf 1
  have hFtS : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ Ft := by
    rcases hFF with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hf 1
    · exact hf 0
  have hFbbd : _root_.Set.range Fb ⊆ (𝓡∂ 3).boundary M := by
    rcases hFF with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hfbd 0
    · exact hfbd 1
  have hFtbd : _root_.Set.range Ft ⊆ (𝓡∂ 3).boundary M := by
    rcases hFF with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hfbd 1
    · exact hfbd 0
  have hFdisj : Disjoint (_root_.Set.range Fb) (_root_.Set.range Ft) := by
    rcases hFF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdisj
    · exact hdisj.symm
  obtain ⟨L, Ext, hL, hExt, hExtr, hExt1, hExt2, hEb, hEt⟩ :=
    exists_oneHandle_alignment ψ hψ Fb Ft hFbS.isEmbedding hFtS.isEmbedding hb ht
  have hFtL : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (Ft ∘ L) := by
    rcases hL with rfl | rfl
    · exact hFtS
    · exact hFtS.comp_diffeomorph planarReflectionDiffeomorph
  have hrangeL : _root_.Set.range (Ft ∘ L) = _root_.Set.range Ft := by
    rcases hL with rfl | rfl
    · exact Function.surjective_id.range_comp Ft
    · exact planarReflection.surjective.range_comp Ft
  let Fc : Fin 2 → EuclideanSpace ℝ (Fin 2) → M := ![Fb, Ft ∘ L]
  have hFcS : ∀ j, _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (Fc j) := by
    intro j
    fin_cases j
    · exact hFbS
    · exact hFtL
  have hFcbd : ∀ j, _root_.Set.range (Fc j) ⊆ (𝓡∂ 3).boundary M := by
    intro j
    fin_cases j
    · exact hFbbd
    · change _root_.Set.range (Ft ∘ L) ⊆ _
      rw [hrangeL]
      exact hFtbd
  have hFcdisj : Disjoint (_root_.Set.range (Fc 0)) (_root_.Set.range (Fc 1)) := by
    change Disjoint (_root_.Set.range Fb) (_root_.Set.range (Ft ∘ L))
    rw [hrangeL]
    exact hFdisj
  obtain ⟨a, V, θ, Θ, ha, ha2, hV, hθV, hΘO, hΘθ, hθΘ, hΘb, hΘt, hθs, hΘs⟩ :=
    exists_oneHandleCollar_of_isSmoothEmbedding Fc hFcS hFcbd hFcdisj
  have hA : CompactSpace {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := hψ.compactSpace
  have hP : CompactSpace (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) :=
    isCompact_iff_compactSpace.mp ((isCompact_stdSimplex ℝ (Fin 3)).prod _root_.CompactIccSpace.isCompact_Icc)
  have hi : _root_.Topology.IsClosedEmbedding (Subtype.val : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} →
        stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    continuous_subtype_val.isClosedEmbedding Subtype.val_injective
  have hExti : ∀ b, |(Ext b).2| = 1 ↔ b ∈ _root_.Set.range (Subtype.val :
      {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
        z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} →
          stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    intro b
    rw [hExt2, Subtype.range_coe]
    exact ⟨fun h => ⟨b.2.1, h⟩, fun h => h.2⟩
  have hΘi : ∀ z : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)}, Θ (Ext z.val) = ψ z := by
    intro z
    rcases z.2.2 with h | h
    · obtain ⟨h1, h2⟩ := hEb z h
      have he : Ext z.val = ((Ext z.val).1, -1) := Prod.ext rfl h1
      rw [he, hΘb]
      exact h2
    · obtain ⟨h1, h2⟩ := hEt z h
      have he : Ext z.val = ((Ext z.val).1, 1) := Prod.ext rfl h1
      rw [he, hΘt]
      exact h2
  have hstage := isSmoothHandleStage_adjunction_of_oneHandleCollar hi hψ hExt hExtr hExti ha
    ha2 hV hθV hΘO hΘθ hθΘ hΘi hθs hΘs
  have hFr : {b : (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) |
      ‖(Ext b).1‖ = 1} = {z | z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1} := by
    ext b
    change ‖(Ext b).1‖ = 1 ↔ b.val.1 ∈ stdSimplexBoundary 2 ∧ b.val.2 ∈ _root_.Set.Icc (0 : ℝ) 1
    rw [hExt1]
    exact ⟨fun h => ⟨h, b.2.2⟩, fun h => h.1⟩
  have hRFr : ∀ z : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)},
      z ∉ {z : {z : stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 |
        z.val ∈ stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} |
          z.val.val ∈ (stdSimplex ℝ (Fin 3) \ stdSimplexBoundary 2) ×ˢ ({0, 1} : Set ℝ)} →
      z.val ∈ {z : (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) |
        z.val ∈ stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1} := by
    intro z hz
    refine ⟨?_, z.val.2.2⟩
    by_contra hbd
    exact hz ⟨⟨z.2.1, hbd⟩, z.2.2⟩
  rw [adjunctionLower_boundary_sdiff_union_eq hRFr, ← hFr]
  exact hstage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_one

end DifferentialGeometry.Topology.PiecewiseLinear
