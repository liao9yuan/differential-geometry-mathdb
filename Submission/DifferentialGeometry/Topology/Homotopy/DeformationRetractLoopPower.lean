/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.LoopPower
import Submission.DifferentialGeometry.Topology.Homotopy.DeformationRetractPath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Homotopy

universe u

open _root_.ContinuousMap
open _root_.unitInterval

namespace StrongDeformationRetract

variable {X : Type u} [TopologicalSpace X] {A : Set X}

noncomputable def retractLoopSubtype (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) : Path (⟨x, hx⟩ : A) ⟨x, hx⟩ where
  toFun s := r.retraction (ℓ s)
  continuous_toFun := (_root_.ContinuousMapClass.map_continuous r.retraction).comp (_root_.ContinuousMapClass.map_continuous ℓ)
  source' := by
    have h0 : ℓ 0 = x := ℓ.source
    change r.retraction (ℓ 0) = _
    rw [h0]
    exact Subtype.ext (r.retraction_eq hx)
  target' := by
    have h1 : ℓ 1 = x := ℓ.target
    change r.retraction (ℓ 1) = _
    rw [h1]
    exact Subtype.ext (r.retraction_eq hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.retractLoopSubtype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.retractLoopSubtype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.retractLoopSubtype ``Submission.DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.retractLoopSubtype

theorem map_retractLoopSubtype (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) :
    (r.retractLoopSubtype hx ℓ).map continuous_subtype_val = r.retractLoop hx ℓ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.map_retractLoopSubtype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.map_retractLoopSubtype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.map_retractLoopSubtype ``Submission.DifferentialGeometry.Topology.Homotopy.StrongDeformationRetract.map_retractLoopSubtype

end StrongDeformationRetract

theorem exists_homotopic_loopZPow_of_strongDeformationRetract {X : Type u} [TopologicalSpace X]
    {A : Set X} (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (p : Path (⟨x, hx⟩ : A) ⟨x, hx⟩)
    (hgen : ∀ ℓ : Path (⟨x, hx⟩ : A) ⟨x, hx⟩, ∃ k : ℤ, ℓ.Homotopic (loopZPow p k))
    (m : Path x x) :
    ∃ k : ℤ, m.Homotopic (loopZPow (p.map continuous_subtype_val) k) := by
  obtain ⟨k, hk⟩ := hgen (r.retractLoopSubtype hx m)
  have hmap := hk.map (⟨((↑) : A → X), continuous_subtype_val⟩ : C(A, X))
  rw [loopZPow_map] at hmap
  exact ⟨k, (r.homotopic_retractLoop hx m).trans hmap⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.exists_homotopic_loopZPow_of_strongDeformationRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.exists_homotopic_loopZPow_of_strongDeformationRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.exists_homotopic_loopZPow_of_strongDeformationRetract ``Submission.DifferentialGeometry.Topology.Homotopy.exists_homotopic_loopZPow_of_strongDeformationRetract

end DifferentialGeometry.Topology.Homotopy
