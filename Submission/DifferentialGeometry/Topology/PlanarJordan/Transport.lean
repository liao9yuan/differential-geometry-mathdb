/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.Schoenflies.JordanClosed
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PlanarJordan

open _root_.Submission.Schoenflies

theorem isArcBetween_image (e : Plane ≃ₜ Plane) {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) : IsArcBetween (e '' A) (e p) (e q) := by
  obtain ⟨f, hfc, hfi, hf, hp, hq⟩ := hA
  refine ⟨e ∘ f, e.continuous.comp_continuousOn hfc,
    fun _ hx _ hy hxy => hfi hx hy (e.injective hxy), ?_, ?_, ?_⟩
  · rw [_root_.Set.image_comp, hf]
  · exact congrArg e hp
  · exact congrArg e hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.isArcBetween_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.isArcBetween_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.isArcBetween_image ``Submission.DifferentialGeometry.Topology.PlanarJordan.isArcBetween_image

theorem isJordanCurve_image (e : Plane ≃ₜ Plane) {C : Set Plane}
    (hC : IsJordanCurve C) : IsJordanCurve (e '' C) := by
  obtain ⟨f, hf, himage⟩ := hC
  refine ⟨e ∘ f, ⟨e.continuous.comp_continuousOn hf.continuousOn,
    congrArg e hf.closes, fun _ hx _ hy hxy => hf.injOn hx hy (e.injective hxy)⟩, ?_⟩
  rw [_root_.Set.image_comp, himage]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image ``Submission.DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image

private theorem mapsTo_inside (e : Plane ≃ₜ Plane) (C : Set Plane) :
    MapsTo e (inside C) (inside (e '' C)) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, hxy⟩
    exact hx.1 (e.injective hxy ▸ hy)
  · rw [← e.image_compl, ← e.image_connectedComponentIn hx.1]
    exact ((Metric.isCompact_of_isClosed_isBounded isClosed_closure hx.2.closure).image
      e.continuous).isBounded.subset (_root_.Set.image_mono subset_closure)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.mapsTo_inside
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.mapsTo_inside target :: scope.openDecls } }

theorem image_inside (e : Plane ≃ₜ Plane) (C : Set Plane) :
    e '' inside C = inside (e '' C) := by
  apply Subset.antisymm (mapsTo_inside e C).image_subset
  intro y hy
  have hx := mapsTo_inside e.symm (e '' C) hy
  simp only [_root_.Set.image_image, e.symm_apply_apply, _root_.Set.image_id'] at hx
  exact ⟨e.symm y, hx, e.apply_symm_apply y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.image_inside then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.image_inside"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.image_inside ``Submission.DifferentialGeometry.Topology.PlanarJordan.image_inside

end DifferentialGeometry.Topology.PlanarJordan
