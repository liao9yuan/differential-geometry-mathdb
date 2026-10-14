/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.interior_eq_empty_of_lt_three {d : ℕ} {C B : Set M}
    (hC : IsPLCellOn d C B) (hd : d < 3) : interior C = ∅ := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hC
  rw [← hu.image_interior]
  have hP : IsPLBall d P := ⟨r, hr⟩
  rw [hP.interior_eq_empty_of_lt_finrank (by simpa using hd), _root_.Set.image_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.interior_eq_empty_of_lt_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.interior_eq_empty_of_lt_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.interior_eq_empty_of_lt_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.interior_eq_empty_of_lt_three

private theorem cell_subset_closure_interior {C B : Set M} (hC : IsPLCellOn 3 C B) :
    C ⊆ closure (interior C) := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hC
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  rw [← hu.image_interior]
  have hcont : ContinuousOn u (closure (interior P)) := by
    rw [hP.closure_interior]
    exact hu.continuousOn
  have h := hcont.image_closure
  rwa [hP.closure_interior] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cell_subset_closure_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.cell_subset_closure_interior target :: scope.openDecls } }

theorem IsPLCellOn.inter_subset_boundary_of_isPLCellOn
    {C CB D DB I : Set M} (hC : IsPLCellOn 3 C CB) (hD : IsPLCellOn 3 D DB)
    (hI : IsPLCellOn 2 (C ∩ D) I) : C ∩ D ⊆ CB := by
  have hdis : interior C ∩ interior D = ∅ := by
    rw [← interior_inter]
    exact hI.interior_eq_empty_of_lt_three (by decide)
  intro x hx
  by_contra hxB
  have hxint : x ∈ interior C := hC.sdiff_boundary_eq_interior.subset ⟨hx.1, hxB⟩
  have hxcl : x ∈ closure (interior C ∩ interior D) :=
    isOpen_interior.inter_closure ⟨hxint, cell_subset_closure_interior hD hx.2⟩
  simp only [hdis, closure_empty, _root_.Set.mem_empty_iff_false] at hxcl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.inter_subset_boundary_of_isPLCellOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.inter_subset_boundary_of_isPLCellOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.inter_subset_boundary_of_isPLCellOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.inter_subset_boundary_of_isPLCellOn

end DifferentialGeometry.Topology.PiecewiseLinear
