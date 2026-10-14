/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Retraction
import Submission.DifferentialGeometry.Topology.VanKampen.CellAttachmentFundamentalGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem fundamentalGroup_map_surjective_of_path
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x x₀ : X} (p : Path x x₀)
    (h₀ : Function.Surjective (FundamentalGroup.map f x₀)) :
    Function.Surjective (FundamentalGroup.map f x) := by
  let eX := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  let eY := FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
  intro a
  obtain ⟨b, hb⟩ := h₀ (eY a)
  refine ⟨eX.symm b, eY.injective ?_⟩
  rw [DifferentialGeometry.Topology.fundamentalGroup_map_changeBasepoint]
  simpa only [eX, MulEquiv.apply_symm_apply] using hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroup_map_surjective_of_path
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.fundamentalGroup_map_surjective_of_path target :: scope.openDecls } }

theorem surjective_fundamentalGroup_map_of_continuous_section
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace X]
    (f : C(X, Y)) (s : C(Y, X)) (hs : Function.RightInverse s f) (x : X) :
    Function.Surjective (FundamentalGroup.map f x) := by
  have hsection := DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_leftInverse
    s f hs (f x)
  have hsurj : Function.Surjective (FundamentalGroup.mapOfEq f (hs (f x))) :=
    fun a => ⟨FundamentalGroup.map s (f x) a, hsection a⟩
  have hbase : Function.Surjective (FundamentalGroup.map f (s (f x))) := by
    let e := (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk (hs (f x)))).conj
    intro a
    obtain ⟨b, hb⟩ := hsurj (e a)
    exact ⟨b, e.injective hb⟩
  exact fundamentalGroup_map_surjective_of_path f
    (PathConnectedSpace.somePath x (s (f x))) hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_map_of_continuous_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_map_of_continuous_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_map_of_continuous_section ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.surjective_fundamentalGroup_map_of_continuous_section

end DifferentialGeometry.Topology.PiecewiseLinear
