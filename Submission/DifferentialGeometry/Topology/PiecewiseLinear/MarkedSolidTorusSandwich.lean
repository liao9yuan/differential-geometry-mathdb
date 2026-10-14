/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SpineNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Disk" => Metric.closedBall (0 : Plane) 1
local notation "Circle" => Metric.sphere (0 : Plane) 1

theorem IsSpine.image {P R : Set E3} {h : E3 → E3}
    (hR : IsSpine P R) (hh : _root_.Topology.IsEmbedding (P.domRestrict h)) :
    IsSpine (h '' P) (h '' R) := by
  obtain ⟨Φ, p, hp, hR⟩ := hR
  let e := hh.toHomeomorph.trans (Homeomorph.setCongr (_root_.Set.range_domRestrict h P))
  refine ⟨Φ.trans e, p, hp, ?_⟩
  rw [hR]
  simp only [_root_.Set.image_image]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsSpine.image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsSpine.image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsSpine.image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSpine.image

theorem exists_toroidalShell_sandwich_of_marked_product_image
    {P R T V : Set E3} {h : E3 → E3}
    (hh : _root_.Topology.IsEmbedding (V.domRestrict h)) (hPV : P ⊆ V)
    (Φ : (Disk × Circle) ≃ₜ P)
    (hR : R = Subtype.val '' (Φ '' {z | (z.1 : Plane) = 0}))
    (hRT : h '' R ⊆ interior T) (hTP : T ⊆ interior (h '' P)) :
    ∃ S₁ S₂ : Set E3, IsTopologicalSolidTorus S₁ ∧ IsTopologicalSolidTorus S₂ ∧
      S₁ ⊆ interior T ∧ T ⊆ interior S₂ ∧
      IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂) ∧
      IsSpine S₁ (h '' R) := by
  have hP : _root_.Topology.IsEmbedding (P.domRestrict h) := hh.comp (IsEmbedding.inclusion hPV)
  have hspine : IsSpine P R := by
    refine ⟨Φ, 0, ?_, hR⟩
    rw [interior_closedBall _ one_ne_zero]
    exact Metric.mem_ball_self zero_lt_one
  have hspineImage := hspine.image hP
  obtain ⟨S₁, hS₁, hS₁T, -, hshell, hcore⟩ :=
    hspineImage.exists_inner_torus_of_isOpen isOpen_interior hRT
  let e := hP.toHomeomorph.trans (Homeomorph.setCongr (_root_.Set.range_domRestrict h P))
  exact ⟨S₁, h '' P, hS₁, ⟨(Φ.trans e).symm⟩, hS₁T, hTP, hshell, hcore⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_toroidalShell_sandwich_of_marked_product_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_toroidalShell_sandwich_of_marked_product_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_toroidalShell_sandwich_of_marked_product_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_toroidalShell_sandwich_of_marked_product_image

end DifferentialGeometry.Topology.PiecewiseLinear
