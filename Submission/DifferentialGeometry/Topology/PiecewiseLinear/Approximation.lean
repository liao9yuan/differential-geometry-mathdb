/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Groupoid
import Submission.DifferentialGeometry.Topology.Manifold.PartialAtlas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.Topology.Manifold (AtlasOn)

universe u

def PLApproximation (n : ℕ) : Prop :=
  ∀ {X₁ X₂ : Type u} [TopologicalSpace X₁] [T2Space X₁] [SecondCountableTopology X₁]
    [MetricSpace X₂] [SecondCountableTopology X₂] {O₁ : Set X₁} {O₂ : Set X₂}
    (A : AtlasOn (plGroupoid n) O₁) (B : AtlasOn (plGroupoid n) O₂)
    (h : OpenPartialHomeomorph X₁ X₂), h.source = O₁ → h.target = O₂ →
    ∀ φ : X₁ → ℝ, ContinuousOn φ O₁ → (∀ x ∈ O₁, 0 < φ x) →
    ∃ f : OpenPartialHomeomorph X₁ X₂, f.source = O₁ ∧ f.target = O₂ ∧
      (∀ x ∈ O₁, _root_.Dist.dist (f x) (h x) < φ x) ∧
      ∀ e ∈ A.charts, ∀ e' ∈ B.charts, e.symm ≫ₕ f ≫ₕ e' ∈ plGroupoid n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLApproximation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLApproximation

theorem plApproximation_zero : PLApproximation.{u} 0 := by
  intro X₁ X₂ _ _ _ _ _ O₁ O₂ A B h hs ht φ _ hpos
  have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
    (WithLp.equiv 2 (Fin 0 → ℝ)).subsingleton
  exact ⟨h, hs, ht, fun x hx => by simpa using hpos x hx, fun e _ e' _ =>
    mem_plGroupoid_of_isPiecewiseAffineOn (isPiecewiseAffineOn_of_subsingleton _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_zero

end DifferentialGeometry.Topology.PiecewiseLinear
