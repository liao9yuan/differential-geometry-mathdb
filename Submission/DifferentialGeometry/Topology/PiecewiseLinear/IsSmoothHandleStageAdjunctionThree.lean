/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Attachment.CellExtension
import Submission.DifferentialGeometry.Topology.Cell.Coordinates
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SmoothBoundarySphereCollar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SmoothCapAttachment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_closedCell_homeomorph_of_range_eq {M : Type} [TopologicalSpace M]
    (ψ : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : _root_.Topology.IsEmbedding ψ) (d : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M)
    (hd : _root_.Topology.IsEmbedding d) (hrange : _root_.Set.range d = _root_.Set.range ψ) :
    ∃ Ext : stdSimplex ℝ (Fin 4) ≃ₜ ClosedCell 3,
      (∀ z, ‖(Ext z : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔ z.val ∈ stdSimplexBoundary 3) ∧
      ∀ (z : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3})
        (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        (u : EuclideanSpace ℝ (Fin 3)) = Ext z.val → d u = ψ z := by
  classical
  let c₀ := DifferentialGeometry.Cell.stdSimplexClosedCellHomeomorph 3
  have hcb : ∀ x : stdSimplex ℝ (Fin 4),
      ‖((c₀ x : ClosedCell 3) : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔
        x.val ∈ stdSimplexBoundary 3 := by
    intro x
    change ‖((DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm x).val : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔ _
    simpa [stdSimplexBoundary, DifferentialGeometry.Simplex.boundary] using
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
        (e := (EuclideanSpace.equiv (Fin 3) ℝ).symm) x)
  let a₀ : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hψ.toHomeomorph.trans ((Homeomorph.setCongr hrange.symm).trans hd.toHomeomorph.symm)
  have ha₀ : ∀ z, d (a₀ z) = ψ z := by
    intro z
    have h := hd.toHomeomorph.apply_symm_apply
      ((Homeomorph.setCongr hrange.symm) (hψ.toHomeomorph z))
    exact congrArg Subtype.val h
  let c₀B : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} ≃ₜ CellBoundary 3 :=
    { toFun := fun z => ⟨(c₀ z.val : EuclideanSpace ℝ (Fin 3)), (hcb _).mpr z.2⟩
      invFun := fun u => ⟨c₀.symm (cellBoundaryInclusion 3 u), (hcb _).mp (by
        rw [Homeomorph.apply_symm_apply]
        exact u.2)⟩
      left_inv := fun z => by
        apply Subtype.ext
        have h : cellBoundaryInclusion 3 ⟨(c₀ z.val : EuclideanSpace ℝ (Fin 3)),
            (hcb _).mpr z.2⟩ = c₀ z.val := Subtype.ext rfl
        change c₀.symm (cellBoundaryInclusion 3 ⟨(c₀ z.val : EuclideanSpace ℝ (Fin 3)),
          (hcb _).mpr z.2⟩) = z.val
        rw [h, Homeomorph.symm_apply_apply]
      right_inv := fun u => by
        apply Subtype.ext
        exact congrArg (fun w : ClosedCell 3 => (w : EuclideanSpace ℝ (Fin 3)))
          (c₀.apply_symm_apply (cellBoundaryInclusion 3 u))
      continuous_toFun :=
        (continuous_subtype_val.comp (c₀.continuous.comp continuous_subtype_val)).subtype_mk _
      continuous_invFun :=
        (c₀.symm.continuous.comp (continuous_cellBoundaryInclusion 3)).subtype_mk _ }
  let sCB : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ CellBoundary 3 :=
    Homeomorph.setCongr (by ext x; exact mem_sphere_zero_iff_norm)
  let β : CellBoundary 3 ≃ₜ CellBoundary 3 := c₀B.symm.trans (a₀.trans sCB)
  refine ⟨c₀.trans (closedCellHomeomorphExtension β), fun z => ?_, fun z u hu => ?_⟩
  · change ‖(closedCellHomeomorphExtension β (c₀ z) : EuclideanSpace ℝ (Fin 3))‖ = 1 ↔ _
    rw [norm_closedCellHomeomorphExtension]
    exact hcb z
  · have hz : c₀ z.val = cellBoundaryInclusion 3 (c₀B z) := Subtype.ext rfl
    have hExt : (closedCellHomeomorphExtension β (c₀ z.val) : EuclideanSpace ℝ (Fin 3)) =
        (a₀ z : EuclideanSpace ℝ (Fin 3)) := by
      rw [hz, closedCellHomeomorphExtension_boundary]
      change ((sCB (a₀ (c₀B.symm (c₀B z)))) : EuclideanSpace ℝ (Fin 3)) = _
      rw [Homeomorph.symm_apply_apply]
      rfl
    have hu' : u = a₀ z := Subtype.ext (hu.trans hExt)
    rw [hu', ha₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_closedCell_homeomorph_of_range_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_closedCell_homeomorph_of_range_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_closedCell_homeomorph_of_range_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_closedCell_homeomorph_of_range_eq

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isSmoothHandleStage_adjunction_three
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (ψ : {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → M)
    (hψ : _root_.Topology.IsClosedEmbedding ψ) (d : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M)
    (hd : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ d) (hdbd : _root_.Set.range d ⊆ (𝓡∂ 3).boundary M)
    (hrange : _root_.Set.range d = _root_.Set.range ψ) :
    IsSmoothHandleStage (AdjunctionSpace (Subtype.val : _ → stdSimplex ℝ (Fin 4)) ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ _root_.Set.range ψ)) := by
  obtain ⟨a, V, θ, Θ, ha, hV, -, hθV, hΘV, hΘθ, hθΘ, hΘd, hθs, hΘs⟩ :=
    exists_radialCollar_of_isSmoothEmbedding_sphere d hd hdbd
  obtain ⟨Ext, hExt1, hExt2⟩ :=
    exists_closedCell_homeomorph_of_range_eq ψ hψ.isEmbedding d hd.isEmbedding hrange
  have hA : CompactSpace {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} :=
    hψ.compactSpace
  have hi : _root_.Topology.IsClosedEmbedding (Subtype.val :
      {z : stdSimplex ℝ (Fin 4) | z.val ∈ stdSimplexBoundary 3} → stdSimplex ℝ (Fin 4)) :=
    continuous_subtype_val.isClosedEmbedding Subtype.val_injective
  refine isSmoothHandleStage_adjunction_of_radialCollar hi hψ Ext (fun z => ?_) ha hV hθV hΘV
    hΘθ hθΘ (fun z => ?_) hθs hΘs
  · rw [hExt1, Subtype.range_coe]
    rfl
  · have hn : ‖(Ext z.val : EuclideanSpace ℝ (Fin 3))‖ = 1 := (hExt1 _).mpr z.2
    have hmem : (Ext z.val : EuclideanSpace ℝ (Fin 3)) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := mem_sphere_zero_iff_norm.mpr hn
    have h1 := hΘd ⟨_, hmem⟩
    have h2 := hExt2 z ⟨_, hmem⟩ rfl
    exact h1.trans h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_three

end DifferentialGeometry.Topology.PiecewiseLinear
