/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import Submission.DifferentialGeometry.Topology.Attachment.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.Classical in
def IsPLCellAttachment (n : ℕ) (P B : Set F) (L : Geometry.SimplicialComplex ℝ E)
    (C N : Set E) : Prop :=
  IsPLBall n P ∧ B ⊆ P ∧
    ∃ g : F → E, IsPLHomeomorphOn g P C ∧ IsPLHomeomorphOn g B (C ∩ L.space) ∧
      let A : Set P := {z | z.val ∈ B}
      ∃ φ : A → L.space, _root_.Topology.IsClosedEmbedding φ ∧
        (∀ z, (φ z : E) = g z.val.val) ∧
        (∀ z, (φ z : E) ∈ (boundaryComplex n L).space) ∧
        ∃ e : AdjunctionSpace (Subtype.val : A → P) φ ≃ₜ N,
          (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
          ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment

theorem IsPLCellAttachment.nonempty {n : ℕ} {P B : Set F}
    {L : Geometry.SimplicialComplex ℝ E} {C N : Set E}
    (h : IsPLCellAttachment n P B L C N) : C.Nonempty := by
  obtain ⟨hP, _, g, hg, _⟩ := h
  obtain ⟨x, hx⟩ := hP.nonempty
  exact ⟨g x, hg.bijOn.mapsTo hx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.nonempty

theorem IsPLCellAttachment.cell_subset {n : ℕ} {P B : Set F}
    {L : Geometry.SimplicialComplex ℝ E} {C N : Set E}
    (h : IsPLCellAttachment n P B L C N) : C ⊆ N := by
  obtain ⟨_, _, g, hg, _, φ, _, _, _, e, _, he⟩ := h
  intro x hx
  obtain ⟨z, hz, rfl⟩ := hg.bijOn.surjOn hx
  exact he ⟨z, hz⟩ ▸ (e (adjunctionCell Subtype.val φ ⟨z, hz⟩)).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.cell_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.cell_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.cell_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.cell_subset

theorem IsPLCellAttachment.lower_subset {n : ℕ} {P B : Set F}
    {L : Geometry.SimplicialComplex ℝ E} {C N : Set E}
    (h : IsPLCellAttachment n P B L C N) : L.space ⊆ N := by
  obtain ⟨_, _, _, _, _, φ, _, _, _, e, he, _⟩ := h
  intro x hx
  have hxe : (e (adjunctionLower φ ⟨x, hx⟩) : E) = x := he ⟨x, hx⟩
  exact hxe ▸ (e (adjunctionLower φ ⟨x, hx⟩)).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.lower_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.lower_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.lower_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.lower_subset

open _root_.Classical in
def IsPLThreeHandleAttachment (k : Fin 4) (L : Geometry.SimplicialComplex ℝ E)
    (C N : Set E) : Prop :=
  match k.val with
  | 0 => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 4)) ∅ L C N
  | 1 => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (stdSimplex ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)) L C N
  | 2 => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) L C N
  | _ => IsPLCellAttachment 3 (stdSimplex ℝ (Fin 4)) (stdSimplexBoundary 3) L C N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLThreeHandleAttachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLThreeHandleAttachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLThreeHandleAttachment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLThreeHandleAttachment

open _root_.Classical in
def IsPLCellAttachmentWith (n : ℕ) (P B : Set F) (L : Geometry.SimplicialComplex ℝ E)
    (C N : Set E) (g : F → E) : Prop :=
  IsPLBall n P ∧ B ⊆ P ∧ IsPLHomeomorphOn g P C ∧ IsPLHomeomorphOn g B (C ∩ L.space) ∧
    let A : Set P := {z | z.val ∈ B}
    ∃ φ : A → L.space, _root_.Topology.IsClosedEmbedding φ ∧
      (∀ z, (φ z : E) = g z.val.val) ∧
      (∀ z, (φ z : E) ∈ (boundaryComplex n L).space) ∧
      ∃ e : AdjunctionSpace (Subtype.val : A → P) φ ≃ₜ N,
        (∀ x, (e (adjunctionLower φ x) : E) = x) ∧
        ∀ z, (e (adjunctionCell Subtype.val φ z) : E) = g z.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachmentWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachmentWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachmentWith ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachmentWith

theorem IsPLCellAttachment.exists_isPLCellAttachmentWith {n : ℕ} {P B : Set F}
    {L : Geometry.SimplicialComplex ℝ E} {C N : Set E}
    (h : IsPLCellAttachment n P B L C N) : ∃ g : F → E, IsPLCellAttachmentWith n P B L C N g := by
  obtain ⟨hP, hBP, g, hg, hgB, hrest⟩ := h
  exact ⟨g, hP, hBP, hg, hgB, hrest⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.exists_isPLCellAttachmentWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.exists_isPLCellAttachmentWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.exists_isPLCellAttachmentWith ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellAttachment.exists_isPLCellAttachmentWith

end DifferentialGeometry.Topology.PiecewiseLinear
