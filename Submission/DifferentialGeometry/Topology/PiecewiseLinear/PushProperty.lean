/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def HasPushPropertyAt (C D : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsPLBall 3 C ∧ IsPLBall 2 D ∧ D ⊆ frontier C ∧
    ∀ f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D →
      ∀ N : Set (EuclideanSpace ℝ (Fin 3)), IsPolyhedron N →
        C \ (f '' stdSimplexBoundary 2) ⊆ interior N →
        ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
          IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧ h '' D = closure (frontier C \ D) ∧ _root_.Set.EqOn h id Nᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt

def HasPushProperty (C : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsPLBall 3 C ∧ ∀ D : Set (EuclideanSpace ℝ (Fin 3)),
    IsPLBall 2 D → D ⊆ frontier C → HasPushPropertyAt C D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty

theorem HasPushPropertyAt.image {C D : Set (EuclideanSpace ℝ (Fin 3))}
    (hCD : HasPushPropertyAt C D)
    {e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)}
    (he : IsPLHomeomorphOn e _root_.Set.univ _root_.Set.univ) : HasPushPropertyAt (e '' C) (e '' D) := by
  obtain ⟨hC, hD, hDC, hpush⟩ := hCD
  have heC := he.restrict hC.isPolyhedron (_root_.Set.subset_univ C)
  have heD := he.restrict hD.isPolyhedron (_root_.Set.subset_univ D)
  have hC' := hC.of_isPLHomeomorphOn heC
  have hD' := hD.of_isPLHomeomorphOn heD
  refine ⟨hC', hD', ?_, ?_⟩
  · rw [← e.image_frontier]
    exact _root_.Set.image_mono hDC
  intro f hf N hN hCN
  have hback := he.homeomorph_symm.restrict hD'.isPolyhedron (_root_.Set.subset_univ _)
  rw [e.image_symm, e.injective.preimage_image] at hback
  have hg := hf.trans hback
  have hN' : IsPolyhedron (e ⁻¹' N) := by
    simpa only [_root_.Set.univ_inter] using he.isPolyhedron_preimage hN (_root_.Set.subset_univ N)
  have hCN' : C \ ((e.symm ∘ f) '' stdSimplexBoundary 2) ⊆ interior (e ⁻¹' N) := by
    rw [← e.preimage_interior]
    intro x hx
    apply hCN
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    apply hx.2
    refine ⟨z, hz, ?_⟩
    change e.symm (f z) = x
    rw [hzx, e.symm_apply_apply]
  obtain ⟨k, hk, hkD, hkfix⟩ := hpush (e.symm ∘ f) hg (e ⁻¹' N) hN' hCN'
  let H := e.symm.trans (k.trans e)
  refine ⟨H, (he.homeomorph_symm.trans hk).trans he, ?_, ?_⟩
  · calc
      H '' (e '' D) = e '' (k '' D) := by
        rw [_root_.Set.image_image, _root_.Set.image_image]
        congr 1
        funext x
        simp [H]
      _ = e '' closure (frontier C \ D) := congrArg (Set.image e) hkD
      _ = closure (frontier (e '' C) \ (e '' D)) := by
        rw [e.image_closure, Set.image_sdiff e.injective, e.image_frontier]
  · intro y hy
    have hpre : e.symm y ∈ (e ⁻¹' N)ᶜ := by
      simpa only [_root_.Set.mem_compl_iff, _root_.Set.mem_preimage, e.apply_symm_apply] using hy
    change e (k (e.symm y)) = y
    rw [hkfix hpre]
    exact e.apply_symm_apply y

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPushPropertyAt.image

theorem HasPushProperty.image {C : Set (EuclideanSpace ℝ (Fin 3))}
    (hC : HasPushProperty C)
    {e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)}
    (he : IsPLHomeomorphOn e _root_.Set.univ _root_.Set.univ) : HasPushProperty (e '' C) := by
  refine ⟨hC.1.of_isPLHomeomorphOn (he.restrict hC.1.isPolyhedron (_root_.Set.subset_univ C)), ?_⟩
  intro D hD hDC
  have hD' := hD.of_isPLHomeomorphOn
    (he.homeomorph_symm.restrict hD.isPolyhedron (_root_.Set.subset_univ D))
  have hboundary : e.symm '' frontier (e '' C) = frontier C := by
    rw [e.symm.image_frontier, e.image_symm, e.injective.preimage_image]
  have hD'C : e.symm '' D ⊆ frontier C := (_root_.Set.image_mono hDC).trans hboundary.le
  have h := (hC.2 (e.symm '' D) hD' hD'C).image he
  have heD : e '' (e.symm '' D) = D := by
    rw [e.image_eq_preimage_symm, e.symm.injective.preimage_image]
  rwa [heD] at h

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty.image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty.image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty.image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPushProperty.image

theorem hasPushProperty_image_iff {C : Set (EuclideanSpace ℝ (Fin 3))}
    {e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)}
    (he : IsPLHomeomorphOn e _root_.Set.univ _root_.Set.univ) : HasPushProperty (e '' C) ↔ HasPushProperty C := by
  constructor
  · intro h
    have h' := h.image he.homeomorph_symm
    rwa [e.image_symm, e.injective.preimage_image] at h'
  · exact fun h => h.image he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.hasPushProperty_image_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.hasPushProperty_image_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.hasPushProperty_image_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.hasPushProperty_image_iff

end DifferentialGeometry.Topology.PiecewiseLinear
