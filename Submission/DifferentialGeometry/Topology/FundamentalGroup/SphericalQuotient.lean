/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.MetricSpace.IsometricSMul
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

universe u v

namespace DifferentialGeometry.Topology

abbrev MulActionOrbitQuotient (G E : Type*) [Group G] [MulAction G E] :=
  Quotient (MulAction.orbitRel G E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.MulActionOrbitQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.MulActionOrbitQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.MulActionOrbitQuotient ``Submission.DifferentialGeometry.Topology.MulActionOrbitQuotient

noncomputable def fundamentalGroupFiniteFreeQuotientEquivOpposite
    {G : Type u} {E : Type v} [Group G] [Finite G]
    [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
    [SimplyConnectedSpace E] (e : E) :
    FundamentalGroup (MulActionOrbitQuotient G E)
        (Quotient.mk (MulAction.orbitRel G E) e) ≃* Gᵐᵒᵖ :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.fundamentalGroupEquiv
    (⟨e, rfl⟩ :
      ((Quotient.mk (MulAction.orbitRel G E)) ⁻¹'
        {Quotient.mk (MulAction.orbitRel G E) e}))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquivOpposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquivOpposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquivOpposite ``Submission.DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquivOpposite

noncomputable def fundamentalGroupFiniteFreeQuotientEquiv
    {G : Type u} {E : Type v} [Group G] [Finite G]
    [TopologicalSpace E] [T2Space E] [LocallyCompactSpace E]
    [MulAction G E] [ContinuousConstSMul G E] [IsCancelSMul G E]
    [SimplyConnectedSpace E] (e : E) :
    FundamentalGroup (MulActionOrbitQuotient G E)
        (Quotient.mk (MulAction.orbitRel G E) e) ≃* G :=
  (fundamentalGroupFiniteFreeQuotientEquivOpposite e).trans (MulEquiv.inv' G).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquiv ``Submission.DifferentialGeometry.Topology.fundamentalGroupFiniteFreeQuotientEquiv

noncomputable def fundamentalGroupFiniteFreeSphereThreeQuotientEquiv
    {G : Type u} [Group G] [Finite G]
    [MulAction G SphereThree] [ContinuousConstSMul G SphereThree] [IsCancelSMul G SphereThree] :
    FundamentalGroup (MulActionOrbitQuotient G SphereThree)
        (Quotient.mk (MulAction.orbitRel G SphereThree) sphereThreeNorth) ≃* G :=
  fundamentalGroupFiniteFreeQuotientEquiv sphereThreeNorth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeQuotientEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeQuotientEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeQuotientEquiv ``Submission.DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeQuotientEquiv

noncomputable def fundamentalGroupFiniteFreeSphereThreeIsometricQuotientEquiv
    {G : Type u} [Group G] [Finite G]
    [MulAction G SphereThree] [IsIsometricSMul G SphereThree] [IsCancelSMul G SphereThree] :
    FundamentalGroup (MulActionOrbitQuotient G SphereThree)
        (Quotient.mk (MulAction.orbitRel G SphereThree) sphereThreeNorth) ≃* G :=
  fundamentalGroupFiniteFreeSphereThreeQuotientEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeIsometricQuotientEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeIsometricQuotientEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeIsometricQuotientEquiv ``Submission.DifferentialGeometry.Topology.fundamentalGroupFiniteFreeSphereThreeIsometricQuotientEquiv

end DifferentialGeometry.Topology
