/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Set.Card

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem image_inter_eq_sdiff_of_supported_disjoint {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K A C : Set X} (hfix : _root_.Set.EqOn f id Kᶜ)
    (hdisj : Disjoint (f '' (A ∩ K)) (C ∩ K)) :
    f '' A ∩ C = (A ∩ C) \ K := by
  have hmaps : _root_.Set.MapsTo f K K := by
    intro x hx
    by_contra hfx
    exact hfx ((hf (hfix hfx)).symm ▸ hx)
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxc⟩
    have hxK : x ∉ K := fun hxK =>
      disjoint_left.mp hdisj ⟨x, ⟨hx, hxK⟩, rfl⟩ ⟨hxc, hmaps hxK⟩
    rw [hfix hxK] at hxc ⊢
    exact ⟨⟨hx, hxc⟩, hxK⟩
  · rintro ⟨⟨hyA, hyC⟩, hyK⟩
    exact ⟨⟨y, hyA, hfix hyK⟩, hyC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_inter_eq_sdiff_of_supported_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_inter_eq_sdiff_of_supported_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_inter_eq_sdiff_of_supported_disjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_inter_eq_sdiff_of_supported_disjoint

theorem ncard_image_inter_add_two_of_supported_disjoint {X : Type*} {f : X → X}
    (hf : Function.Injective f) {K A C : Set X} (hfix : _root_.Set.EqOn f id Kᶜ)
    (hdisj : Disjoint (f '' (A ∩ K)) (C ∩ K))
    {p q : X} (hpq : p ≠ q) (hcross : (A ∩ C) ∩ K = {p, q})
    (hfin : (A ∩ C).Finite) : (f '' A ∩ C).ncard + 2 = (A ∩ C).ncard := by
  rw [image_inter_eq_sdiff_of_supported_disjoint hf hfix hdisj]
  have hcard := _root_.Set.ncard_inter_add_ncard_sdiff_eq_ncard (A ∩ C) K hfin
  rw [hcross, _root_.Set.ncard_pair hpq] at hcard
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.ncard_image_inter_add_two_of_supported_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.ncard_image_inter_add_two_of_supported_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.ncard_image_inter_add_two_of_supported_disjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.ncard_image_inter_add_two_of_supported_disjoint

end DifferentialGeometry.Topology.PiecewiseLinear
