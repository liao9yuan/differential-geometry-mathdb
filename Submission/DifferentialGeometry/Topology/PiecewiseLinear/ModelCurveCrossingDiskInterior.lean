/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingCellInterior
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLModelIntersection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
  {P : Set E3} {u : E3 → M}

theorem IsPLHomeomorphInto.closure_image_of_isCompact
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsCompact P) {A : Set E3} (hAP : A ⊆ P) :
    closure (u '' A) = u '' closure A := by
  have hcl : closure A ⊆ P := closure_minimal hAP hP.isClosed
  have hclosed : IsClosed (u '' closure A) :=
    ((hP.of_isClosed_subset isClosed_closure hcl).image_of_continuousOn
      (hu.continuousOn.mono hcl)).isClosed
  exact subset_antisymm (closure_minimal (_root_.Set.image_mono subset_closure) hclosed)
    (ContinuousOn.image_closure (hu.continuousOn.mono hcl))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.closure_image_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.closure_image_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.closure_image_of_isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.closure_image_of_isCompact

theorem IsPLHomeomorphInto.eventually_mem_image_iff_of_isCompact
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsCompact P)
    {A B : Set E3} (hAP : A ⊆ P) (hBP : B ⊆ P) {x : E3} (hxP : x ∈ P)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    ∀ᶠ y in 𝓝 (u x), y ∈ u '' A ↔ y ∈ u '' B := by
  obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hlocal
  have hclosed : IsClosed (u '' (P \ O)) :=
    ((hP.diff hO).image_of_continuousOn (hu.continuousOn.mono _root_.Set.sdiff_subset)).isClosed
  have hxout : u x ∉ u '' (P \ O) := by
    rintro ⟨z, hz, hzx⟩
    exact hz.2 (hu.injOn hz.1 hxP hzx ▸ hxO)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hxout] with y hy
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzO : z ∈ O := by
      by_contra hzO
      exact hy ⟨z, ⟨hAP hz, hzO⟩, rfl⟩
    exact ⟨z, (hOO hzO).mp hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hzO : z ∈ O := by
      by_contra hzO
      exact hy ⟨z, ⟨hBP hz, hzO⟩, rfl⟩
    exact ⟨z, (hOO hzO).mpr hz, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.eventually_mem_image_iff_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.eventually_mem_image_iff_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.eventually_mem_image_iff_of_isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.eventually_mem_image_iff_of_isCompact

theorem HasPLCurveCrossingOnAt.mem_closure_inter_model_diskInterior_in_chart
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsCompact P)
    {S A B D : Set E3} (hSP : S ⊆ P) (hAP : A ⊆ P) (hBP : B ⊆ P)
    {x : E3} (hxP : x ∈ P) (c : OpenPartialHomeomorph M E3) (hxc : u x ∈ c.source)
    (hc : HasPLCurveCrossingOnAt (c '' ((u '' S) ∩ c.source))
      (c '' ((u '' A) ∩ c.source)) (c '' ((u '' B) ∩ c.source)) (c (u x)))
    {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) (hDS : D ⊆ S)
    (hboundary : ∀ᶠ y in 𝓝 x, y ∈ q '' stdSimplexBoundary 2 ↔ y ∈ B) :
    x ∈ closure (A ∩ (D \ q '' stdSimplexBoundary 2)) := by
  have hDP : D ⊆ P := hDS.trans hSP
  have hDbD : q '' stdSimplexBoundary 2 ⊆ D := by
    rw [← hq.image_eq]
    exact _root_.Set.image_mono fun z hz => hz.1
  have hcell : IsPLCellOn 2 (u '' D) (u '' (q '' stdSimplexBoundary 2)) :=
    ⟨D, q, u, hq, hu.mono_of_polyhedron (IsPLBall.isPolyhedron ⟨q, hq⟩) hDP, rfl, rfl⟩
  have hlocal := hu.eventually_mem_image_iff_of_isCompact hP (hDbD.trans hDP) hBP hxP hboundary
  have hacc := HasPLCurveCrossingOnAt.mem_closure_inter_cellInterior_in_chart c hxc hc
    hcell (_root_.Set.image_mono hDS) hlocal
  have himage : u '' (A ∩ (D \ q '' stdSimplexBoundary 2)) =
      (u '' A) ∩ ((u '' D) \ u '' (q '' stdSimplexBoundary 2)) := by
    rw [hu.injOn.image_inter hAP (sdiff_subset.trans hDP),
      (hu.injOn.mono hDP).image_sdiff_subset hDbD]
  have hsub : A ∩ (D \ q '' stdSimplexBoundary 2) ⊆ P := inter_subset_left.trans hAP
  rw [← himage, hu.closure_image_of_isCompact hP hsub] at hacc
  obtain ⟨z, hz, hzx⟩ := hacc
  have hzP : z ∈ P := closure_minimal hsub hP.isClosed hz
  exact hu.injOn hzP hxP hzx ▸ hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasPLCurveCrossingOnAt.mem_closure_inter_model_diskInterior_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasPLCurveCrossingOnAt.mem_closure_inter_model_diskInterior_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasPLCurveCrossingOnAt.mem_closure_inter_model_diskInterior_in_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasPLCurveCrossingOnAt.mem_closure_inter_model_diskInterior_in_chart

end DifferentialGeometry.Topology.PiecewiseLinear
