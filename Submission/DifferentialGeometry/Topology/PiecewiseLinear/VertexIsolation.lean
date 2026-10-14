/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LinkSubspace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hzero : (SimplicialComplex.geometricLink K {p}).space ∩
      {x | ℓ x = ℓ p} = ∅) :
    {p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p := by
  have hstar : ∀ᶠ x in 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p,
      x ∈ closedStar K p ↔ x ∈ K.space :=
    (eventually_mem_closedStar_iff K p).filter_mono nhdsWithin_le_nhds
  filter_upwards [hstar, self_mem_nhdsWithin]
    with x hxstar hx
  have hxclosed : x ∈ closedStar K p := hxstar.mpr hx.1
  rw [closedStar_eq_coneComplex_space K hp] at hxclosed
  rcases (mem_coneComplex_space_iff _).mp hxclosed with hxp | ⟨z, hz, s, hs, hs1, hzx⟩
  · exact hxp ▸ _root_.Set.mem_singleton p
  · have hzlevel : ℓ z = ℓ p := by
      have hlevel := hx.2
      change ℓ x = ℓ p at hlevel
      rw [hzx, map_add, map_smul, map_sub, smul_eq_mul] at hlevel
      have hmul : s * (ℓ z - ℓ p) = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hs.ne')
    have hzmem : z ∈ (SimplicialComplex.geometricLink K {p}).space ∩
        {y | ℓ y = ℓ p} := ⟨hz, hzlevel⟩
    rw [hzero] at hzmem
    exact hzmem.elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty

theorem notMem_heightSingularPoints_of_geometricLink_section_eq_empty
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hzero : (SimplicialComplex.geometricLink K {p}).space ∩
      {x | ℓ x = ℓ p} = ∅) :
    p ∉ heightSingularPoints K.space ℓ :=
  notMem_heightSingularPoints_of_isolated
    (singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty K hp ℓ hzero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_section_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_section_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_section_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_section_eq_empty

theorem notMem_heightSingularPoints_of_geometricLink_strictly_above
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (habove : ∀ x ∈ (SimplicialComplex.geometricLink K {p}).space, ℓ p < ℓ x) :
    p ∉ heightSingularPoints K.space ℓ := by
  apply notMem_heightSingularPoints_of_geometricLink_section_eq_empty K hp ℓ
  rw [_root_.Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxeq⟩
  exact (habove x hx).ne' hxeq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_above then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_above"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_above ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_above

theorem notMem_heightSingularPoints_of_geometricLink_strictly_below
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hbelow : ∀ x ∈ (SimplicialComplex.geometricLink K {p}).space, ℓ x < ℓ p) :
    p ∉ heightSingularPoints K.space ℓ := by
  apply notMem_heightSingularPoints_of_geometricLink_section_eq_empty K hp ℓ
  rw [_root_.Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxeq⟩
  exact (hbelow x hx).ne hxeq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_below then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_below"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_below ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.notMem_heightSingularPoints_of_geometricLink_strictly_below

end DifferentialGeometry.Topology.PiecewiseLinear
