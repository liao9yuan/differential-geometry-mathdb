/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.VanKampen.ConnectedSumNeckFundamentalGroup
import Submission.DifferentialGeometry.Topology.VanKampen.EmbeddedCellCollar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap _root_.Manifold _root_.ContDiff

noncomputable section

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.VanKampen


structure SmoothEmbeddedClosedThreeCellWithCollar
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where

  toFun : ClosedCell 3 → M

  injective_toFun : Function.Injective toFun

  continuous_toFun : Continuous toFun

  isSmoothEmbedding_interior : Manifold.IsSmoothEmbedding
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
    (embeddedCellInteriorMap toFun)

  twoSidedCollar : TwoSidedCellCollar toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar


abbrev SmoothEmbeddedClosedThreeCellWithCollar.complement
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (B : SmoothEmbeddedClosedThreeCellWithCollar M) :=
  embeddedCellComplement B.toFun

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.complement


def SmoothEmbeddedClosedThreeCellWithCollar.boundaryMap
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (B : SmoothEmbeddedClosedThreeCellWithCollar M) :
    CellBoundary 3 → B.complement :=
  embeddedCellBoundaryMap B.toFun B.injective_toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.boundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.boundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.boundaryMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.boundaryMap

theorem SmoothEmbeddedClosedThreeCellWithCollar.continuous_boundaryMap
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (B : SmoothEmbeddedClosedThreeCellWithCollar M) :
    Continuous B.boundaryMap :=
  continuous_embeddedCellBoundaryMap B.toFun B.injective_toFun B.continuous_toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.continuous_boundaryMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.continuous_boundaryMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.continuous_boundaryMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.continuous_boundaryMap


abbrev connectedSumLeftGluingPoint
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M) (b : CellBoundary 3) :
    BM.complement :=
  BM.boundaryMap b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftGluingPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftGluingPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftGluingPoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftGluingPoint


abbrev connectedSumRightGluingPoint
    {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    BN.complement :=
  BN.boundaryMap (glue b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightGluingPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumRightGluingPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightGluingPoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumRightGluingPoint


abbrev EmbeddedCellConnectedSum
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :=
  ConnectedSumNeck BM.boundaryMap BN.boundaryMap glue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.EmbeddedCellConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.EmbeddedCellConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.EmbeddedCellConnectedSum ``Submission.DifferentialGeometry.Topology.ThreeManifold.EmbeddedCellConnectedSum


noncomputable def SmoothEmbeddedClosedThreeCellWithCollar.fundamentalGroupComplementEquiv
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (B : SmoothEmbeddedClosedThreeCellWithCollar M) (x : B.complement) :
    FundamentalGroup B.complement x ≃* FundamentalGroup M (x : M) :=
  fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbeddingOfCollar
    B.toFun B.injective_toFun B.continuous_toFun B.isSmoothEmbedding_interior
      B.twoSidedCollar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.fundamentalGroupComplementEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.fundamentalGroupComplementEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.fundamentalGroupComplementEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothEmbeddedClosedThreeCellWithCollar.fundamentalGroupComplementEquiv

noncomputable def connectedSumAmbientToComplementFactorEquiv
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    ∀ i,
      fundamentalGroupSourceFactor
          (connectedSumLeftGluingPoint BM b : M)
          (connectedSumRightGluingPoint BN glue b : N) i ≃*
        fundamentalGroupSourceFactor
          (connectedSumLeftGluingPoint BM b)
          (connectedSumRightGluingPoint BN glue b) i
  | false => (BM.fundamentalGroupComplementEquiv
      (connectedSumLeftGluingPoint BM b)).symm
  | true => (BN.fundamentalGroupComplementEquiv
      (connectedSumRightGluingPoint BN glue b)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFactorEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFactorEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFactorEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFactorEquiv

noncomputable def connectedSumAmbientToComplementFreeProductEquiv
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    fundamentalGroupSourceFreeProduct
        (connectedSumLeftGluingPoint BM b : M)
        (connectedSumRightGluingPoint BN glue b : N) ≃*
      fundamentalGroupSourceFreeProduct
        (connectedSumLeftGluingPoint BM b)
        (connectedSumRightGluingPoint BN glue b) :=
  DifferentialGeometry.Algebra.Group.coprodIMulEquiv
    (fundamentalGroupSourceFactor
      (connectedSumLeftGluingPoint BM b : M)
      (connectedSumRightGluingPoint BN glue b : N))
    (fundamentalGroupSourceFactor
      (connectedSumLeftGluingPoint BM b)
      (connectedSumRightGluingPoint BN glue b))
    (connectedSumAmbientToComplementFactorEquiv BM BN glue b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFreeProductEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFreeProductEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFreeProductEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumAmbientToComplementFreeProductEquiv

noncomputable def fundamentalGroupEquiv_connectedSum
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    fundamentalGroupSourceFreeProduct
        (connectedSumLeftGluingPoint BM b : M)
        (connectedSumRightGluingPoint BN glue b : N) ≃*
      FundamentalGroup (EmbeddedCellConnectedSum BM BN glue)
        (connectedSumNeckMidpoint BM.boundaryMap BN.boundaryMap glue b) := by
  let _ : PathConnectedSpace BM.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BM.toFun BM.injective_toFun BM.continuous_toFun BM.isSmoothEmbedding_interior
        BM.twoSidedCollar
  let _ : PathConnectedSpace BN.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BN.toFun BN.injective_toFun BN.continuous_toFun BN.isSmoothEmbedding_interior
        BN.twoSidedCollar
  exact (connectedSumAmbientToComplementFreeProductEquiv BM BN glue b).trans
    (fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum

noncomputable def connectedSumLeftFactorHom
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    FundamentalGroup M (connectedSumLeftGluingPoint BM b : M) →*
      FundamentalGroup (EmbeddedCellConnectedSum BM BN glue)
        (connectedSumNeckMidpoint BM.boundaryMap BN.boundaryMap glue b) := by
  let _ : PathConnectedSpace BM.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BM.toFun BM.injective_toFun BM.continuous_toFun BM.isSmoothEmbedding_interior
        BM.twoSidedCollar
  let _ : PathConnectedSpace BN.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BN.toFun BN.injective_toFun BN.continuous_toFun BN.isSmoothEmbedding_interior
        BN.twoSidedCollar
  exact ((fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (BM.boundaryMap b)
            (BN.boundaryMap (glue b))) (i := _root_.Bool.false))).comp
      (BM.fundamentalGroupComplementEquiv
        (connectedSumLeftGluingPoint BM b)).symm.toMonoidHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom

noncomputable def connectedSumRightFactorHom
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    FundamentalGroup N (connectedSumRightGluingPoint BN glue b : N) →*
      FundamentalGroup (EmbeddedCellConnectedSum BM BN glue)
        (connectedSumNeckMidpoint BM.boundaryMap BN.boundaryMap glue b) := by
  let _ : PathConnectedSpace BM.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BM.toFun BM.injective_toFun BM.continuous_toFun BM.isSmoothEmbedding_interior
        BM.twoSidedCollar
  let _ : PathConnectedSpace BN.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BN.toFun BN.injective_toFun BN.continuous_toFun BN.isSmoothEmbedding_interior
        BN.twoSidedCollar
  exact ((fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (BM.boundaryMap b)
            (BN.boundaryMap (glue b))) (i := _root_.Bool.true))).comp
      (BN.fundamentalGroupComplementEquiv
        (connectedSumRightGluingPoint BN glue b)).symm.toMonoidHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom

theorem connectedSumLeftFactorHom_eq_inverseBallDeletion_then_inclusion
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    connectedSumLeftFactorHom BM BN glue b =
      ((fundamentalGroupLeftToAmbient
          (connectedSumNeckLeft BM.boundaryMap BN.boundaryMap glue)
          (connectedSumNeckMidpoint BM.boundaryMap BN.boundaryMap glue b)
          (connectedSumNeckMidpoint_mem_inter
            BM.boundaryMap BN.boundaryMap glue b).1).hom.comp
        ((DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint
          (connectedSumNeckLeftConnector BM.boundaryMap BM.continuous_boundaryMap
            BN.boundaryMap glue b)).toMonoidHom.comp
          (FundamentalGroup.mapOfEq
            (connectedSumNeckLeftHomotopyEquiv
              BM.boundaryMap BM.continuous_boundaryMap BN.boundaryMap glue).toFun rfl))).comp
        (BM.fundamentalGroupComplementEquiv
          (connectedSumLeftGluingPoint BM b)).symm.toMonoidHom := by
  let _ : PathConnectedSpace BM.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BM.toFun BM.injective_toFun BM.continuous_toFun BM.isSmoothEmbedding_interior
        BM.twoSidedCollar
  let _ : PathConnectedSpace BN.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BN.toFun BN.injective_toFun BN.continuous_toFun BN.isSmoothEmbedding_interior
        BN.twoSidedCollar
  ext g
  change (fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
        (Monoid.CoprodI.of (i := _root_.Bool.false)
          ((BM.fundamentalGroupComplementEquiv
            (connectedSumLeftGluingPoint BM b)).symm g)) = _
  convert DFunLike.congr_fun
    (fundamentalGroupEquivConnectedSumNeck_comp_left
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
      ((BM.fundamentalGroupComplementEquiv
        (connectedSumLeftGluingPoint BM b)).symm g) using 1 <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom_eq_inverseBallDeletion_then_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom_eq_inverseBallDeletion_then_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom_eq_inverseBallDeletion_then_inclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftFactorHom_eq_inverseBallDeletion_then_inclusion

theorem connectedSumRightFactorHom_eq_inverseBallDeletion_then_inclusion
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    connectedSumRightFactorHom BM BN glue b =
      ((fundamentalGroupRightToAmbient
          (connectedSumNeckRight BM.boundaryMap BN.boundaryMap glue)
          (connectedSumNeckMidpoint BM.boundaryMap BN.boundaryMap glue b)
          (connectedSumNeckMidpoint_mem_inter
            BM.boundaryMap BN.boundaryMap glue b).2).hom.comp
        ((DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint
          (connectedSumNeckRightConnector BM.boundaryMap BN.boundaryMap
            BN.continuous_boundaryMap glue b)).toMonoidHom.comp
          (FundamentalGroup.mapOfEq
            (connectedSumNeckRightHomotopyEquiv
              BM.boundaryMap BN.boundaryMap BN.continuous_boundaryMap glue).toFun rfl))).comp
        (BN.fundamentalGroupComplementEquiv
          (connectedSumRightGluingPoint BN glue b)).symm.toMonoidHom := by
  let _ : PathConnectedSpace BM.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BM.toFun BM.injective_toFun BM.continuous_toFun BM.isSmoothEmbedding_interior
        BM.twoSidedCollar
  let _ : PathConnectedSpace BN.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BN.toFun BN.injective_toFun BN.continuous_toFun BN.isSmoothEmbedding_interior
        BN.twoSidedCollar
  ext g
  change (fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
        (Monoid.CoprodI.of (i := _root_.Bool.true)
          ((BN.fundamentalGroupComplementEquiv
            (connectedSumRightGluingPoint BN glue b)).symm g)) = _
  convert DFunLike.congr_fun
    (fundamentalGroupEquivConnectedSumNeck_comp_right
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
      ((BN.fundamentalGroupComplementEquiv
        (connectedSumRightGluingPoint BN glue b)).symm g) using 1 <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom_eq_inverseBallDeletion_then_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom_eq_inverseBallDeletion_then_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom_eq_inverseBallDeletion_then_inclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumRightFactorHom_eq_inverseBallDeletion_then_inclusion

theorem fundamentalGroupEquiv_connectedSum_comp_left
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    (fundamentalGroupEquiv_connectedSum BM BN glue b).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (connectedSumLeftGluingPoint BM b : M)
            (connectedSumRightGluingPoint BN glue b : N)) (i := _root_.Bool.false)) =
      connectedSumLeftFactorHom BM BN glue b := by
  let _ : PathConnectedSpace BM.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BM.toFun BM.injective_toFun BM.continuous_toFun BM.isSmoothEmbedding_interior
        BM.twoSidedCollar
  let _ : PathConnectedSpace BN.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BN.toFun BN.injective_toFun BN.continuous_toFun BN.isSmoothEmbedding_interior
        BN.twoSidedCollar
  ext g
  change (fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
    ((connectedSumAmbientToComplementFreeProductEquiv BM BN glue b)
      (Monoid.CoprodI.of (i := _root_.Bool.false) g)) =
    (fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
      (Monoid.CoprodI.of
        (M := fundamentalGroupSourceFactor
          (connectedSumLeftGluingPoint BM b)
          (connectedSumRightGluingPoint BN glue b)) (i := _root_.Bool.false)
        ((BM.fundamentalGroupComplementEquiv
          (connectedSumLeftGluingPoint BM b)).symm g))
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_left ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_left

theorem fundamentalGroupEquiv_connectedSum_comp_right
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3) :
    (fundamentalGroupEquiv_connectedSum BM BN glue b).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (connectedSumLeftGluingPoint BM b : M)
            (connectedSumRightGluingPoint BN glue b : N)) (i := _root_.Bool.true)) =
      connectedSumRightFactorHom BM BN glue b := by
  let _ : PathConnectedSpace BM.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BM.toFun BM.injective_toFun BM.continuous_toFun BM.isSmoothEmbedding_interior
        BM.twoSidedCollar
  let _ : PathConnectedSpace BN.complement :=
    pathConnectedSpace_embeddedCellComplement_of_smoothEmbedding_of_twoSidedCellCollar
      BN.toFun BN.injective_toFun BN.continuous_toFun BN.isSmoothEmbedding_interior
        BN.twoSidedCollar
  ext g
  change (fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
    ((connectedSumAmbientToComplementFreeProductEquiv BM BN glue b)
      (Monoid.CoprodI.of (i := _root_.Bool.true) g)) =
    (fundamentalGroupEquivConnectedSumNeck
      BM.boundaryMap BM.continuous_boundaryMap
      BN.boundaryMap BN.continuous_boundaryMap glue b)
      (Monoid.CoprodI.of
        (M := fundamentalGroupSourceFactor
          (connectedSumLeftGluingPoint BM b)
          (connectedSumRightGluingPoint BN glue b)) (i := _root_.Bool.true)
        ((BN.fundamentalGroupComplementEquiv
          (connectedSumRightGluingPoint BN glue b)).symm g))
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_right ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_connectedSum_comp_right



noncomputable def connectedSumLeftTransportedFactorHom
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3)
    {m : M} (β : Path (connectedSumLeftGluingPoint BM b : M) m) :
    FundamentalGroup M m →*
      FundamentalGroup (EmbeddedCellConnectedSum BM BN glue)
        (connectedSumNeckMidpoint BM.boundaryMap BN.boundaryMap glue b) :=
  DifferentialGeometry.Topology.transportedFundamentalGroupHom
    (connectedSumLeftFactorHom BM BN glue b) β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom


theorem connectedSumLeftTransportedFactorHom_apply
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3)
    {m : M} (β : Path (connectedSumLeftGluingPoint BM b : M) m)
    (g : FundamentalGroup M m) :
    connectedSumLeftTransportedFactorHom BM BN glue b β g =
      connectedSumLeftFactorHom BM BN glue b
        ((Path.Homotopic.Quotient.trans ⟦β⟧ g).trans
          (Path.Homotopic.Quotient.symm ⟦β⟧)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_apply

theorem connectedSumLeftTransportedFactorHom_connector
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3)
    {m : M} (β β' : Path (connectedSumLeftGluingPoint BM b : M) m) :
    connectedSumLeftTransportedFactorHom BM BN glue b β' =
      (MulAut.conj
        (connectedSumLeftFactorHom BM BN glue b
          (DifferentialGeometry.Topology.connectorLoop β β'))⁻¹).toMonoidHom.comp
        (connectedSumLeftTransportedFactorHom BM BN glue b β) :=
  DifferentialGeometry.Topology.transportedFundamentalGroupHom_connector
    (connectedSumLeftFactorHom BM BN glue b) β β'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_connector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_connector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_connector ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumLeftTransportedFactorHom_connector

noncomputable def connectedSumRightTransportedFactorHom
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3)
    {n : N} (β : Path (connectedSumRightGluingPoint BN glue b : N) n) :
    FundamentalGroup N n →*
      FundamentalGroup (EmbeddedCellConnectedSum BM BN glue)
        (connectedSumNeckMidpoint BM.boundaryMap BN.boundaryMap glue b) :=
  DifferentialGeometry.Topology.transportedFundamentalGroupHom
    (connectedSumRightFactorHom BM BN glue b) β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom


theorem connectedSumRightTransportedFactorHom_apply
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3)
    {n : N} (β : Path (connectedSumRightGluingPoint BN glue b : N) n)
    (g : FundamentalGroup N n) :
    connectedSumRightTransportedFactorHom BM BN glue b β g =
      connectedSumRightFactorHom BM BN glue b
        ((Path.Homotopic.Quotient.trans ⟦β⟧ g).trans
          (Path.Homotopic.Quotient.symm ⟦β⟧)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_apply

theorem connectedSumRightTransportedFactorHom_connector
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [ConnectedSpace M] [ConnectedSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (BM : SmoothEmbeddedClosedThreeCellWithCollar M)
    (BN : SmoothEmbeddedClosedThreeCellWithCollar N)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (b : CellBoundary 3)
    {n : N} (β β' : Path (connectedSumRightGluingPoint BN glue b : N) n) :
    connectedSumRightTransportedFactorHom BM BN glue b β' =
      (MulAut.conj
        (connectedSumRightFactorHom BM BN glue b
          (DifferentialGeometry.Topology.connectorLoop β β'))⁻¹).toMonoidHom.comp
        (connectedSumRightTransportedFactorHom BM BN glue b β) :=
  DifferentialGeometry.Topology.transportedFundamentalGroupHom_connector
    (connectedSumRightFactorHom BM BN glue b) β β'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_connector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_connector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_connector ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumRightTransportedFactorHom_connector

end DifferentialGeometry.Topology.ThreeManifold
