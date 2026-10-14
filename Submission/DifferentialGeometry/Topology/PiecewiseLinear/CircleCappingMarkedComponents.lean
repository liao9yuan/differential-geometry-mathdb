/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleCappingComponentInvariants
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCircleCapping.exists_component_equiv_preserving_marks
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces]
    {T B : Set E3} (hcap : IsCircleCapping K.space Q.space T B) :
    ∃ G ∈ traceCircles K.space T, boundsDiskIn G T ∧
      ∃ e : ConnectedComponents K.space ≃ ConnectedComponents Q.space,
        ∀ c, (B \ G) ∩ (connectedComponentComplex K c).space ⊆
          (connectedComponentComplex Q (e c)).space := by
  obtain ⟨D, r, f, hr, hDT, hmeet, hG, -, hf, hfix⟩ := hcap
  obtain ⟨c₀, e, -, hcomp, -, -⟩ :=
    IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment K Q hr hmeet hf
  refine ⟨r '' stdSimplexBoundary 2, hG, ⟨D, r, hr, hDT, rfl⟩, e, ?_⟩
  intro c x hx
  have hfx : f x = x := hfix hx.1
  exact hfx ▸ (hcomp c).bijOn.mapsTo (Or.inl hx.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCircleCapping.exists_component_equiv_preserving_marks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCircleCapping.exists_component_equiv_preserving_marks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCircleCapping.exists_component_equiv_preserving_marks ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCircleCapping.exists_component_equiv_preserving_marks

theorem IsPLHomeomorphOn.exists_component_equiv_preserving_marks
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces]
    {f : E3 → E3} {B : Set E3} (hf : IsPLHomeomorphOn f K.space Q.space)
    (hfix : _root_.Set.EqOn f id B) :
    ∃ e : ConnectedComponents K.space ≃ ConnectedComponents Q.space,
      ∀ c, B ∩ (connectedComponentComplex K c).space ⊆
        (connectedComponentComplex Q (e c)).space := by
  obtain ⟨e, he⟩ := hf.exists_component_equiv K Q
  refine ⟨e, fun c x hx => ?_⟩
  have hfx : f x = x := hfix hx.1
  exact hfx ▸ (he c).bijOn.mapsTo hx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv_preserving_marks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv_preserving_marks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv_preserving_marks ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_component_equiv_preserving_marks

end DifferentialGeometry.Topology.PiecewiseLinear
