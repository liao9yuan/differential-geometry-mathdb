/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.LocalAtTarget
import Submission.DifferentialGeometry.Topology.LocallyPathConnected
import Submission.DifferentialGeometry.Topology.VanKampen.EmbeddedCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

noncomputable section

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Handle

structure TwoSidedCellCollar {M : Type u} [TopologicalSpace M]
    (c : ClosedCell 3 → M) where

  toFun : CellBoundary 3 × ℝ → M

  isOpenEmbedding_toFun : _root_.Topology.IsOpenEmbedding toFun

  zero_eq : ∀ b, toFun (b, 0) = c (cellBoundaryInclusion 3 b)

  mem_complement_iff : ∀ p,
    toFun p ∈ embeddedCellComplement c ↔ 0 ≤ p.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar

namespace TwoSidedCellCollar

variable {M : Type u} [TopologicalSpace M] {c : ClosedCell 3 → M}


def complementMap (h : TwoSidedCellCollar c) :
    h.toFun ⁻¹' embeddedCellComplement c → embeddedCellComplement c :=
  (embeddedCellComplement c).restrictPreimage h.toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.complementMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.complementMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.complementMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.complementMap


theorem isOpenEmbedding_complementMap (h : TwoSidedCellCollar c) :
    IsOpenEmbedding h.complementMap :=
  h.isOpenEmbedding_toFun.restrictPreimage (embeddedCellComplement c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.isOpenEmbedding_complementMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.isOpenEmbedding_complementMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.isOpenEmbedding_complementMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.isOpenEmbedding_complementMap


theorem preimage_complement (h : TwoSidedCellCollar c) :
    h.toFun ⁻¹' embeddedCellComplement c =
      (Set.univ : Set (CellBoundary 3)) ×ˢ Set.Ici (0 : ℝ) := by
  ext p
  simp only [_root_.Set.mem_preimage, _root_.Set.mem_prod, _root_.Set.mem_univ, true_and, _root_.Set.mem_Ici]
  exact h.mem_complement_iff p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.preimage_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.preimage_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.preimage_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.preimage_complement


theorem locallyPathConnectedSpace_complementPreimage (h : TwoSidedCellCollar c) :
    LocallyPathConnectedSpace (h.toFun ⁻¹' embeddedCellComplement c) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (CellBoundary 3) :=
    cellBoundaryChartedSpace 3
  let _ : LocallyPathConnectedSpace (CellBoundary 3) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) (CellBoundary 3)
  let _ : LocallyPathConnectedSpace (Set.Ici (0 : ℝ)) :=
    (convex_Ici (0 : ℝ)).locallyPathConnectedSpace
  let e : (h.toFun ⁻¹' embeddedCellComplement c) ≃ₜ
      CellBoundary 3 × Set.Ici (0 : ℝ) :=
    (Homeomorph.setCongr h.preimage_complement).trans
      ((Homeomorph.Set.prod Set.univ (Set.Ici (0 : ℝ))).trans
        ((Homeomorph.Set.univ (CellBoundary 3)).prodCongr
          (Homeomorph.refl (Set.Ici (0 : ℝ)))))
  exact e.isOpenEmbedding.locallyPathConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_complementPreimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_complementPreimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_complementPreimage ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_complementPreimage


theorem locallyPathConnectedSpace_range_complementMap (h : TwoSidedCellCollar c) :
    LocallyPathConnectedSpace (Set.range h.complementMap) := by
  let _ : LocallyPathConnectedSpace (h.toFun ⁻¹' embeddedCellComplement c) :=
    h.locallyPathConnectedSpace_complementPreimage
  let e : (h.toFun ⁻¹' embeddedCellComplement c) ≃ₜ Set.range h.complementMap :=
    (Homeomorph.Set.univ _).symm.trans
      ((h.isOpenEmbedding_complementMap.toIsEmbedding.homeomorphImage Set.univ).trans
        (Homeomorph.setCongr (by simp)))
  exact e.symm.isOpenEmbedding.locallyPathConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_range_complementMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_range_complementMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_range_complementMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCellCollar.locallyPathConnectedSpace_range_complementMap

end TwoSidedCellCollar


def embeddedCellExterior {M : Type u} (c : ClosedCell 3 → M) :
    Set (embeddedCellComplement c) :=
  Subtype.val ⁻¹' (Set.range c)ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.embeddedCellExterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.embeddedCellExterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.embeddedCellExterior ``Submission.DifferentialGeometry.Topology.ThreeManifold.embeddedCellExterior

def embeddedCellExteriorHomeomorph {M : Type u} [TopologicalSpace M]
    (c : ClosedCell 3 → M) :
    embeddedCellExterior c ≃ₜ ((Set.range c)ᶜ : Set M) where
  toFun q := ⟨q.1.1, q.2⟩
  invFun q := ⟨⟨q.1, by
    intro hq
    exact q.2 ⟨Classical.choose hq, Classical.choose_spec hq |>.2⟩⟩, q.2⟩
  left_inv q := rfl
  right_inv q := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.embeddedCellExteriorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.embeddedCellExteriorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.embeddedCellExteriorHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.embeddedCellExteriorHomeomorph


theorem isOpen_embeddedCellExterior {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : ClosedCell 3 → M) (hcont : Continuous c) :
    IsOpen (embeddedCellExterior c) := by
  apply continuous_subtype_val.isOpen_preimage
  exact (isCompact_range hcont).isClosed.isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.isOpen_embeddedCellExterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.isOpen_embeddedCellExterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.isOpen_embeddedCellExterior ``Submission.DifferentialGeometry.Topology.ThreeManifold.isOpen_embeddedCellExterior


theorem locallyPathConnectedSpace_embeddedCellExterior
    {M : Type u} [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    (c : ClosedCell 3 → M) (hcont : Continuous c) :
    LocallyPathConnectedSpace (embeddedCellExterior c) := by
  let _ : LocallyPathConnectedSpace ((Set.range c)ᶜ : Set M) :=
    (isCompact_range hcont).isClosed.isOpen_compl.locallyPathConnectedSpace
  exact (embeddedCellExteriorHomeomorph c).isOpenEmbedding.locallyPathConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellExterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellExterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellExterior ``Submission.DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellExterior


theorem locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar
    {M : Type u} [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
    (c : ClosedCell 3 → M) (hcont : Continuous c)
    (hcollar : TwoSidedCellCollar c) :
    LocallyPathConnectedSpace (embeddedCellComplement c) := by
  let U : Bool → Set (embeddedCellComplement c)
    | false => embeddedCellExterior c
    | true => Set.range hcollar.complementMap
  apply DifferentialGeometry.Topology.locallyPathConnectedSpace_of_openCover U
  · intro i
    cases i with
    | false => exact isOpen_embeddedCellExterior c hcont
    | true => exact hcollar.isOpenEmbedding_complementMap.isOpen_range
  · intro q
    by_cases hq : (q : M) ∈ Set.range c
    · rcases hq with ⟨d, hd⟩
      have hdK : c d ∈ embeddedCellComplement c := by
        rw [hd]
        exact q.2
      rcases cellBoundary_of_image_mem_embeddedCellComplement c d hdK with ⟨b, hb⟩
      refine ⟨true, ?_⟩
      change q ∈ Set.range hcollar.complementMap
      let p : CellBoundary 3 × ℝ := (b, 0)
      have hpK : hcollar.toFun p ∈ embeddedCellComplement c :=
        (hcollar.mem_complement_iff p).mpr (by simp [p])
      refine ⟨⟨p, hpK⟩, Subtype.ext ?_⟩
      change hcollar.toFun (b, 0) = (q : M)
      rw [hcollar.zero_eq, hb, hd]
    · exact ⟨false, hq⟩
  · intro i
    cases i with
    | false => exact locallyPathConnectedSpace_embeddedCellExterior c hcont
    | true => exact hcollar.locallyPathConnectedSpace_range_complementMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar

theorem pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    (hcollar : TwoSidedCellCollar c) :
    PathConnectedSpace (embeddedCellComplement c) := by
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let _ : LocallyPathConnectedSpace (embeddedCellComplement c) :=
    locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar
      c hcont hcollar
  exact pathConnectedSpace_embeddedCellComplement c hc hcont
    (isOpen_embeddedCellInteriorImage_of_isSmoothEmbedding c hsmooth)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar

noncomputable def fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    (hcollar : TwoSidedCellCollar c) (x : embeddedCellComplement c) :
    FundamentalGroup (embeddedCellComplement c) x ≃* FundamentalGroup M (x : M) := by
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let _ : LocallyPathConnectedSpace (embeddedCellComplement c) :=
    locallyPathConnectedSpace_embeddedCellComplement_of_twoSidedCellCollar
      c hcont hcollar
  exact fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbedding c hc hcont hsmooth x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar


theorem fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar_toMonoidHom
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    (hcollar : TwoSidedCellCollar c) (x : embeddedCellComplement c) :
    (↑(fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar
        c hc hcont hsmooth hcollar x) :
      FundamentalGroup (embeddedCellComplement c) x →* FundamentalGroup M (x : M)) =
      FundamentalGroup.map (embeddedCellComplementInclusion c) x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar_toMonoidHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar_toMonoidHom

end DifferentialGeometry.Topology.ThreeManifold
