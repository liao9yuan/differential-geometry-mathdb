/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.of_isPLHomeomorphOn {X Y J₀ J₁ : Set E3} {f : E3 → E3}
    (h : IsPLAnnulusWithEnds X J₀ J₁) (hf : IsPLHomeomorphOn f X Y) :
    IsPLAnnulusWithEnds Y (f '' J₀) (f '' J₁) := by
  obtain ⟨J, ρ, hJ, hρ, h₀, h₁⟩ := h
  exact ⟨J, f ∘ ρ, hJ, hρ.trans hf, by rw [_root_.Set.image_comp, h₀], by rw [_root_.Set.image_comp, h₁]⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn

theorem IsPLAnnulusWithEnds.of_isPLHomeomorphOn_eqOn {X Y J₀ J₁ : Set E3} {f : E3 → E3}
    (h : IsPLAnnulusWithEnds X J₀ J₁) (hf : IsPLHomeomorphOn f X Y)
    (hfix : _root_.Set.EqOn f id (J₀ ∪ J₁)) : IsPLAnnulusWithEnds Y J₀ J₁ := by
  have h₀ : f '' J₀ = J₀ := by
    simpa only [_root_.Set.image_id] using (hfix.mono _root_.Set.subset_union_left).image_eq
  have h₁ : f '' J₁ = J₁ := by
    simpa only [_root_.Set.image_id] using (hfix.mono _root_.Set.subset_union_right).image_eq
  simpa only [h₀, h₁] using h.of_isPLHomeomorphOn hf

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn_eqOn with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn_eqOn"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn_eqOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.of_isPLHomeomorphOn_eqOn

theorem IsPLAnnulusWithEnds.exists_complex [d : DecidableEq E3] {X J₀ J₁ : Set E3}
    (h : IsPLAnnulusWithEnds X J₀ J₁) :
    ∃ K : Geometry.SimplicialComplex ℝ E3, K.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 K ∧ IsConnected K.space ∧ K.space = X ∧
      (boundaryComplex 2 K).space = J₀ ∪ J₁ := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨J, ρ, hJ, hρ, h₀, h₁⟩ := h
  obtain ⟨K, hKfin, hK, hconn, hspace, hboundary⟩ := hρ.exists_annulus_complex hJ zero_lt_one
  have hpair : J ×ˢ ({0, 1} : Set ℝ) = (J ×ˢ {0}) ∪ (J ×ˢ {1}) := by
    ext p
    simp only [_root_.Set.mem_prod, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_union]
    tauto
  refine ⟨K, hKfin, hK, hconn, hspace, ?_⟩
  rw [hboundary, hpair, _root_.Set.image_union, ← h₀, ← h₁]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.exists_complex with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.exists_complex"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.exists_complex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.exists_complex

end DifferentialGeometry.Topology.PiecewiseLinear
