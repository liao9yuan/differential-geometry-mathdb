/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]

theorem simplyConnectedSpace_iff_fundamentalGroup_eq_one (x : X) :
    SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 := by
  constructor
  · intro h
    let _ := h
    exact fun g => Subsingleton.elim g 1
  · intro h
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, fun y p => ?_⟩
    let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y x
    apply Path.Homotopic.Quotient.exact
    change Path.Homotopic.Quotient.mk p = (1 : FundamentalGroup X y)
    apply e.injective
    rw [map_one]
    exact h _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnectedSpace_iff_fundamentalGroup_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnectedSpace_iff_fundamentalGroup_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnectedSpace_iff_fundamentalGroup_eq_one ``Submission.DifferentialGeometry.Topology.simplyConnectedSpace_iff_fundamentalGroup_eq_one

theorem exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace
    (h : ¬ SimplyConnectedSpace X) (x : X) :
    ∃ g : FundamentalGroup X x, g ≠ 1 := by
  classical
  exact not_forall.mp ((simplyConnectedSpace_iff_fundamentalGroup_eq_one x).not.mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace ``Submission.DifferentialGeometry.Topology.exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace

end DifferentialGeometry.Topology
