/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off {X Y : Type*}
    {f g : X → Y} {P : Set X} {V : Set Y}
    (h : ∀ z ∉ V, P ∩ g ⁻¹' {z} = P ∩ f ⁻¹' {z}) :
    doublePointSet g P \ V = doublePointSet f P \ V := by
  have key : ∀ u v : X → Y, (∀ z ∉ V, P ∩ u ⁻¹' {z} = P ∩ v ⁻¹' {z}) →
      doublePointSet u P \ V ⊆ doublePointSet v P \ V := by
    rintro u v huv y ⟨⟨a, ha, b, hb, hab, hau, hbu⟩, hyV⟩
    have hfibre : ∀ x ∈ P, u x = y → v x = y := by
      intro x hx hxy
      have hx' : x ∈ P ∩ u ⁻¹' {y} :=
        ⟨hx, Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hxy)⟩
      rw [huv y hyV] at hx'
      exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx'.2)
    exact ⟨⟨a, ha, b, hb, hab, hfibre a ha hau, hfibre b hb hbu⟩, hyV⟩
  exact Set.Subset.antisymm (key g f h) (key f g (fun z hz => (h z hz).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off

theorem doublePointSet_sdiff_eq_of_preimage_singleton_eq_off {X Y : Type*} {f g : X → Y}
    (P : Set X) {V : Set Y} (h : ∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}) :
    doublePointSet g P \ V = doublePointSet f P \ V :=
  doublePointSet_sdiff_eq_of_inter_preimage_singleton_eq_off (fun z hz => by rw [h z hz])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_preimage_singleton_eq_off then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_preimage_singleton_eq_off"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_preimage_singleton_eq_off ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_sdiff_eq_of_preimage_singleton_eq_off

theorem preimage_singleton_eq_off_iff {X Y : Type*} {f g : X → Y} {V : Set Y} :
    (∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}) ↔
      (∀ x, f x ∉ V → g x = f x) ∧ ∀ x, f x ∈ V → g x ∈ V := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hmem : x ∈ f ⁻¹' {f x} := Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr rfl)
      rw [← h (f x) hx] at hmem
      exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)
    · by_contra hgx
      have hmem : x ∈ g ⁻¹' {g x} := Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr rfl)
      rw [h (g x) hgx] at hmem
      have hfg : f x = g x := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hmem)
      exact hgx (hfg ▸ hx)
  · rintro ⟨hone, htwo⟩ z hz
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hgx
      have hfx : f x ∉ V := fun hf => hz (hgx ▸ htwo x hf)
      exact (hone x hfx).symm.trans hgx
    · intro hfx
      have hfV : f x ∉ V := fun hf => hz (hfx ▸ hf)
      exact (hone x hfV).trans hfx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.preimage_singleton_eq_off_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.preimage_singleton_eq_off_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.preimage_singleton_eq_off_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.preimage_singleton_eq_off_iff

theorem doublePointSet_subset_of_preimage_singleton_eq_off {X Y : Type*} {f g : X → Y}
    (P : Set X) {U V : Set Y} (h : ∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z})
    (hf : doublePointSet f P ⊆ U) (hVU : V ⊆ U) : doublePointSet g P ⊆ U := by
  intro y hy
  by_cases hyV : y ∈ V
  · exact hVU hyV
  · have hmem : y ∈ doublePointSet g P \ V := ⟨hy, hyV⟩
    rw [doublePointSet_sdiff_eq_of_preimage_singleton_eq_off P h] at hmem
    exact hf hmem.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_subset_of_preimage_singleton_eq_off then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_subset_of_preimage_singleton_eq_off"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_subset_of_preimage_singleton_eq_off ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_subset_of_preimage_singleton_eq_off

end DifferentialGeometry.Topology.PiecewiseLinear
