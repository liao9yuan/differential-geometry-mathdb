/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

universe u

noncomputable def complementHomeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) : (Aᶜ : Set X) ≃ₜ ((e '' A)ᶜ : Set Y) :=
  e.subtype (fun x => by
    constructor
    · intro hx hy
      obtain ⟨a, ha, hea⟩ := hy
      exact hx (e.injective hea ▸ ha)
    · intro hx hAx
      exact hx ⟨x, hAx, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.complementHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.complementHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.complementHomeomorph ``Submission.DifferentialGeometry.Topology.complementHomeomorph

noncomputable def integralComplementHomologyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : X ≃ₜ Y) (A : Set X) :
    integralSingularHomology n (Aᶜ : Set X) ≃ₗ[ℤ]
      integralSingularHomology n ((e '' A)ᶜ : Set Y) :=
  integralSingularHomologyHomotopyEquiv n (complementHomeomorph e A).toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralComplementHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralComplementHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralComplementHomologyEquiv ``Submission.DifferentialGeometry.Topology.integralComplementHomologyEquiv

theorem subsingleton_integralComplementHomology_iff
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (e : X ≃ₜ Y) (A : Set X) :
    Subsingleton (integralSingularHomology n (Aᶜ : Set X)) ↔
      Subsingleton (integralSingularHomology n ((e '' A)ᶜ : Set Y)) := by
  constructor
  · intro h
    let _ := h
    exact (integralComplementHomologyEquiv n e A).symm.toEquiv.subsingleton
  · intro h
    let _ := h
    exact (integralComplementHomologyEquiv n e A).toEquiv.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralComplementHomology_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralComplementHomology_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralComplementHomology_iff ``Submission.DifferentialGeometry.Topology.subsingleton_integralComplementHomology_iff

end DifferentialGeometry.Topology
