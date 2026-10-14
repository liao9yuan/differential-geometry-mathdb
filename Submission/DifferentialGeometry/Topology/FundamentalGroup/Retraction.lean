/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology

theorem fundamentalGroup_mapOfEq_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (r : C(Y, X)) (hr : Function.LeftInverse r f) (x₀ : X) :
    Function.LeftInverse (FundamentalGroup.mapOfEq r (hr x₀))
      (FundamentalGroup.map f x₀) := by
  intro p
  rw [FundamentalGroup.mapOfEq_apply]
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk
      (((p.map f.continuous).map r.continuous).cast (hr x₀).symm (hr x₀).symm) =
        Path.Homotopic.Quotient.mk p
    congr 1
    ext t
    exact hr (p t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_leftInverse ``Submission.DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_leftInverse

theorem injective_fundamentalGroup_map_of_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (r : C(Y, X)) (hr : Function.LeftInverse r f) (x₀ : X) :
    Function.Injective (FundamentalGroup.map f x₀) :=
  (fundamentalGroup_mapOfEq_leftInverse f r hr x₀).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_leftInverse ``Submission.DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_leftInverse

theorem bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : Y ≃ₕ X) (f : C(X, Y)) (hf : Function.LeftInverse e f) (x : X) :
    Function.Bijective (FundamentalGroup.map f x) := by
  have hi := fundamentalGroup_mapOfEq_leftInverse f e.toFun hf x
  have he := fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv e (f x) x (hf x)
  refine ⟨hi.injective, ?_⟩
  intro a
  exact ⟨FundamentalGroup.mapOfEq e.toFun (hf x) a, he.1 (hi _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse ``Submission.DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse

end DifferentialGeometry.Topology
