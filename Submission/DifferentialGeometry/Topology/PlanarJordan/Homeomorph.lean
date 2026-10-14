import Submission.DifferentialGeometry.External.Schoenflies.CrosscutCells
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace Schoenflies

theorem image_inside_homeomorph (F : Plane ≃ₜ Plane) (C : Set Plane) :
    F '' inside C = inside (F '' C) := by
  have hmap (G : Plane ≃ₜ Plane) (A : Set Plane) : _root_.Set.MapsTo G (inside A) (inside (G '' A)) := by
    intro x hx
    refine ⟨fun hg => hx.1 (G.injective.mem_set_image.mp hg), ?_⟩
    have he := G.image_connectedComponentIn (show x ∈ Aᶜ from hx.1)
    rw [G.image_compl] at he
    rw [← he]
    exact ((hx.2.isCompact_closure.image G.continuous).isBounded).subset
      (_root_.Set.image_mono subset_closure)
  apply Subset.antisymm (hmap F C).image_subset
  intro y hy
  have hs := hmap F.symm (F '' C) hy
  simp only [_root_.Set.image_image, F.symm_apply_apply, _root_.Set.image_id'] at hs
  exact ⟨F.symm y, hs, F.apply_symm_apply y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.image_inside_homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.image_inside_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.image_inside_homeomorph ``Submission.Schoenflies.image_inside_homeomorph

theorem image_outside_homeomorph (F : Plane ≃ₜ Plane) (C : Set Plane) :
    F '' outside C = outside (F '' C) := by
  have he (A : Set Plane) : outside A = Aᶜ \ inside A := by
    ext x
    simp only [mem_outside_iff, _root_.Set.mem_sdiff, _root_.Set.mem_compl_iff, mem_inside_iff]
    tauto
  rw [he, _root_.Set.image_sdiff F.injective, F.image_compl, image_inside_homeomorph, he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.image_outside_homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.image_outside_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.image_outside_homeomorph ``Submission.Schoenflies.image_outside_homeomorph

theorem image_closure_inside_homeomorph (F : Plane ≃ₜ Plane) (C : Set Plane) :
    F '' closure (inside C) = closure (inside (F '' C)) := by
  rw [F.image_closure, image_inside_homeomorph]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.image_closure_inside_homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.image_closure_inside_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.image_closure_inside_homeomorph ``Submission.Schoenflies.image_closure_inside_homeomorph

end Schoenflies
