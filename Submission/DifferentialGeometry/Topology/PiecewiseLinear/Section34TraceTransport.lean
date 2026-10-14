/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

open _root_.Homeomorph in
theorem Homeomorph.image_connectedComponentIn_family {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (Ψ : X ≃ₜ Y) (S : Set X) :
    (fun A : Set X => Ψ '' A) '' ((fun x => connectedComponentIn S x) '' S) =
      (fun y => connectedComponentIn (Ψ '' S) y) '' (Ψ '' S) := by
  rw [_root_.Set.image_image, _root_.Set.image_image]
  apply _root_.Set.image_congr
  intro x hx
  exact Ψ.image_connectedComponentIn hx

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Homeomorph
  let env ← Lean.getEnv
  if env.contains `Homeomorph.image_connectedComponentIn_family then
    throwError "Refusing to shadow existing declaration Homeomorph.image_connectedComponentIn_family"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.image_connectedComponentIn_family ``Submission.Homeomorph.image_connectedComponentIn_family

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

open _root_.Classical in
theorem section34TraceComponents_update_image
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3)
    (Ψ : M₂ ≃ₜ M₂) (hSf : Ψ '' frontier (⋃ w, tgtV w) = frontier (⋃ w, tgtV w)) :
    section34TraceComponents tgtV (Function.update fblBd s (Ψ '' fblBd s)) s =
      (fun A : Set M₂ => Ψ '' A) '' section34TraceComponents tgtV fblBd s := by
  have htrace : Ψ '' fblBd s ∩ frontier (⋃ w, tgtV w) =
      Ψ '' (fblBd s ∩ frontier (⋃ w, tgtV w)) := by
    rw [_root_.Set.image_inter Ψ.injective, hSf]
  simp only [section34TraceComponents, Function.update_self, htrace]
  exact (Ψ.image_connectedComponentIn_family _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34TraceComponents_update_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34TraceComponents_update_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34TraceComponents_update_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34TraceComponents_update_image

open _root_.Classical in
theorem section34TraceCount_update_image
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) (s : Section34SimplexIndex 𝒦 3)
    (Ψ : M₂ ≃ₜ M₂) (hSf : Ψ '' frontier (⋃ w, tgtV w) = frontier (⋃ w, tgtV w)) :
    section34TraceCount tgtV (Function.update fblBd s (Ψ '' fblBd s)) s =
      section34TraceCount tgtV fblBd s := by
  rw [section34TraceCount, section34TraceComponents_update_image tgtV fblBd s Ψ hSf]
  exact _root_.Set.ncard_image_of_injective _ Ψ.injective.image_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34TraceCount_update_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34TraceCount_update_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34TraceCount_update_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34TraceCount_update_image

end DifferentialGeometry.Topology.PiecewiseLinear
