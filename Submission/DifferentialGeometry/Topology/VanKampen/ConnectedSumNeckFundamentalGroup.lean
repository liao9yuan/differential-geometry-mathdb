/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.VanKampen.ConnectedSumNeckHomotopy
import Submission.DifferentialGeometry.Topology.VanKampen.ConnectorFreeProductCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap _root_.unitInterval

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.CellAttachment
open _root_.Submission.DifferentialGeometry.Topology.VanKampen


noncomputable def connectedSumNeckLeftConnectorTime (t : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) / 2, by
    constructor
    · linarith [t.2.2]
    · linarith [t.2.1]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime

theorem continuous_connectedSumNeckLeftConnectorTime :
    Continuous connectedSumNeckLeftConnectorTime := by
  apply Continuous.subtype_mk
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftConnectorTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftConnectorTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftConnectorTime ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftConnectorTime

@[simp]
theorem connectedSumNeckLeftConnectorTime_zero :
    connectedSumNeckLeftConnectorTime 0 = ⟨1 / 2, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  norm_num [connectedSumNeckLeftConnectorTime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_zero

@[simp]
theorem connectedSumNeckLeftConnectorTime_one :
    connectedSumNeckLeftConnectorTime 1 = 0 := by
  apply Subtype.ext
  norm_num [connectedSumNeckLeftConnectorTime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_one ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnectorTime_one


noncomputable def connectedSumNeckRightConnectorTime (t : unitInterval) : unitInterval :=
  ⟨(1 + (t : ℝ)) / 2, by
    constructor
    · linarith [t.2.1]
    · linarith [t.2.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime

theorem continuous_connectedSumNeckRightConnectorTime :
    Continuous connectedSumNeckRightConnectorTime := by
  apply Continuous.subtype_mk
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckRightConnectorTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckRightConnectorTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckRightConnectorTime ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckRightConnectorTime

@[simp]
theorem connectedSumNeckRightConnectorTime_zero :
    connectedSumNeckRightConnectorTime 0 = ⟨1 / 2, by constructor <;> norm_num⟩ := by
  apply Subtype.ext
  norm_num [connectedSumNeckRightConnectorTime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_zero

@[simp]
theorem connectedSumNeckRightConnectorTime_one :
    connectedSumNeckRightConnectorTime 1 = 1 := by
  apply Subtype.ext
  norm_num [connectedSumNeckRightConnectorTime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_one ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnectorTime_one


noncomputable def connectedSumNeckLeftConnector
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (b : CellBoundary 3) :
    Path
      (leftBasepoint (connectedSumNeckLeft leftBoundary rightBoundary glue)
        (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
        (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b).1)
      (connectedSumNeckLeftHomotopyEquiv
        leftBoundary hleft rightBoundary glue (leftBoundary b)) where
  toFun t := ⟨adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
      (b, connectedSumNeckLeftConnectorTime t), by
        change ((connectedSumNeckLeftConnectorTime t : unitInterval) : ℝ) < 2 / 3
        dsimp [connectedSumNeckLeftConnectorTime]
        linarith [t.2.1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp
        (continuous_const.prodMk continuous_connectedSumNeckLeftConnectorTime)
  source' := by
    apply Subtype.ext
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckLeftConnectorTime 0) =
      connectedSumNeckMidpoint leftBoundary rightBoundary glue b
    rw [connectedSumNeckLeftConnectorTime_zero]
    rfl
  target' := by
    apply Subtype.ext
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckLeftConnectorTime 1) =
      connectedSumNeckLeftInclusion leftBoundary rightBoundary glue (leftBoundary b)
    rw [connectedSumNeckLeftConnectorTime_one]
    exact (connectedSumNeckLeftInclusion_boundary
      leftBoundary rightBoundary glue b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnector ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftConnector


noncomputable def connectedSumNeckRightConnector
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    Path
      (rightBasepoint (connectedSumNeckRight leftBoundary rightBoundary glue)
        (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
        (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b).2)
      (connectedSumNeckRightHomotopyEquiv
        leftBoundary rightBoundary hright glue (rightBoundary (glue b))) where
  toFun t := ⟨adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
      (b, connectedSumNeckRightConnectorTime t), by
        change 1 / 3 < ((connectedSumNeckRightConnectorTime t : unitInterval) : ℝ)
        dsimp [connectedSumNeckRightConnectorTime]
        linarith [t.2.1]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp
        (continuous_const.prodMk continuous_connectedSumNeckRightConnectorTime)
  source' := by
    apply Subtype.ext
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckRightConnectorTime 0) =
      connectedSumNeckMidpoint leftBoundary rightBoundary glue b
    rw [connectedSumNeckRightConnectorTime_zero]
    rfl
  target' := by
    apply Subtype.ext
    rw [connectedSumNeckRightHomotopyEquiv_apply]
    change adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (b, connectedSumNeckRightConnectorTime 1) =
      connectedSumNeckRightInclusion leftBoundary rightBoundary glue (rightBoundary (glue b))
    rw [connectedSumNeckRightConnectorTime_one]
    exact (connectedSumNeckRightInclusion_boundary
      leftBoundary rightBoundary glue b).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnector ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightConnector



noncomputable def fundamentalGroupEquivConnectedSumNeck
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace K] [PathConnectedSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    fundamentalGroupSourceFreeProduct
        (leftBoundary b) (rightBoundary (glue b)) ≃*
      FundamentalGroup (ConnectedSumNeck leftBoundary rightBoundary glue)
        (connectedSumNeckMidpoint leftBoundary rightBoundary glue b) := by
  let _ : PathConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckLeft
      leftBoundary hleft rightBoundary glue
  let _ : PathConnectedSpace
      ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckRight
      leftBoundary rightBoundary hright glue
  let _ : SimplyConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
    simplyConnectedSpace_connectedSumNeck_inter
      leftBoundary rightBoundary glue
  exact fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
    (connectedSumNeckLeft leftBoundary rightBoundary glue)
    (connectedSumNeckRight leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckRight leftBoundary rightBoundary glue)
    (connectedSumNeckLeft_union_right leftBoundary rightBoundary glue)
    (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
    (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b)
    (leftBoundary b) (rightBoundary (glue b))
    (connectedSumNeckLeftHomotopyEquiv
      leftBoundary hleft rightBoundary glue)
    (connectedSumNeckLeftConnector
      leftBoundary hleft rightBoundary glue b)
    (connectedSumNeckRightHomotopyEquiv
      leftBoundary rightBoundary hright glue)
    (connectedSumNeckRightConnector
      leftBoundary rightBoundary hright glue b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck

theorem fundamentalGroupEquivConnectedSumNeck_comp_left
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace K] [PathConnectedSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    (↑(fundamentalGroupEquivConnectedSumNeck
      leftBoundary hleft rightBoundary hright glue b) :
        fundamentalGroupSourceFreeProduct
            (leftBoundary b) (rightBoundary (glue b)) →*
          FundamentalGroup (ConnectedSumNeck leftBoundary rightBoundary glue)
            (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)).comp
      (Monoid.CoprodI.of
        (M := fundamentalGroupSourceFactor
          (leftBoundary b) (rightBoundary (glue b))) (i := _root_.Bool.false)) =
      (fundamentalGroupLeftToAmbient
          (connectedSumNeckLeft leftBoundary rightBoundary glue)
          (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
          (connectedSumNeckMidpoint_mem_inter
            leftBoundary rightBoundary glue b).1).hom.comp
        ((DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint
          (connectedSumNeckLeftConnector
            leftBoundary hleft rightBoundary glue b)).toMonoidHom.comp
          (FundamentalGroup.mapOfEq
            (connectedSumNeckLeftHomotopyEquiv
              leftBoundary hleft rightBoundary glue).toFun rfl)) := by
  let _ : PathConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckLeft
      leftBoundary hleft rightBoundary glue
  let _ : PathConnectedSpace
      ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckRight
      leftBoundary rightBoundary hright glue
  let _ : SimplyConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
    simplyConnectedSpace_connectedSumNeck_inter
      leftBoundary rightBoundary glue
  exact fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left
    (connectedSumNeckLeft leftBoundary rightBoundary glue)
    (connectedSumNeckRight leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckRight leftBoundary rightBoundary glue)
    (connectedSumNeckLeft_union_right leftBoundary rightBoundary glue)
    (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
    (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b)
    (leftBoundary b) (rightBoundary (glue b))
    (connectedSumNeckLeftHomotopyEquiv
      leftBoundary hleft rightBoundary glue)
    (connectedSumNeckLeftConnector
      leftBoundary hleft rightBoundary glue b)
    (connectedSumNeckRightHomotopyEquiv
      leftBoundary rightBoundary hright glue)
    (connectedSumNeckRightConnector
      leftBoundary rightBoundary hright glue b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_left ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_left

theorem fundamentalGroupEquivConnectedSumNeck_comp_right
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace K] [PathConnectedSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (hright : Continuous rightBoundary)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    (↑(fundamentalGroupEquivConnectedSumNeck
      leftBoundary hleft rightBoundary hright glue b) :
        fundamentalGroupSourceFreeProduct
            (leftBoundary b) (rightBoundary (glue b)) →*
          FundamentalGroup (ConnectedSumNeck leftBoundary rightBoundary glue)
            (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)).comp
      (Monoid.CoprodI.of
        (M := fundamentalGroupSourceFactor
          (leftBoundary b) (rightBoundary (glue b))) (i := _root_.Bool.true)) =
      (fundamentalGroupRightToAmbient
          (connectedSumNeckRight leftBoundary rightBoundary glue)
          (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
          (connectedSumNeckMidpoint_mem_inter
            leftBoundary rightBoundary glue b).2).hom.comp
        ((DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint
          (connectedSumNeckRightConnector
            leftBoundary rightBoundary hright glue b)).toMonoidHom.comp
          (FundamentalGroup.mapOfEq
            (connectedSumNeckRightHomotopyEquiv
              leftBoundary rightBoundary hright glue).toFun rfl)) := by
  let _ : PathConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckLeft
      leftBoundary hleft rightBoundary glue
  let _ : PathConnectedSpace
      ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
    pathConnectedSpace_connectedSumNeckRight
      leftBoundary rightBoundary hright glue
  let _ : SimplyConnectedSpace
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue ∩
        connectedSumNeckRight leftBoundary rightBoundary glue) :=
    simplyConnectedSpace_connectedSumNeck_inter
      leftBoundary rightBoundary glue
  exact fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right
    (connectedSumNeckLeft leftBoundary rightBoundary glue)
    (connectedSumNeckRight leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue)
    (isOpen_connectedSumNeckRight leftBoundary rightBoundary glue)
    (connectedSumNeckLeft_union_right leftBoundary rightBoundary glue)
    (connectedSumNeckMidpoint leftBoundary rightBoundary glue b)
    (connectedSumNeckMidpoint_mem_inter leftBoundary rightBoundary glue b)
    (leftBoundary b) (rightBoundary (glue b))
    (connectedSumNeckLeftHomotopyEquiv
      leftBoundary hleft rightBoundary glue)
    (connectedSumNeckLeftConnector
      leftBoundary hleft rightBoundary glue b)
    (connectedSumNeckRightHomotopyEquiv
      leftBoundary rightBoundary hright glue)
    (connectedSumNeckRightConnector
      leftBoundary rightBoundary hright glue b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_right ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquivConnectedSumNeck_comp_right

end DifferentialGeometry.Topology.ThreeManifold
