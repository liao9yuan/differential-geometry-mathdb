/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Geometry.Manifold.Instances.Sphere
import Submission.DifferentialGeometry.Topology.Algebra.Group.FreeProductAssociativity
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Sphere
import Submission.DifferentialGeometry.Topology.VanKampen.ConnectedSum

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
open _root_.Submission.DifferentialGeometry.Algebra.Group
open _root_.Submission.DifferentialGeometry.Topology.VanKampen

structure BasedConnectedClosedSmoothThreeManifold where

  Carrier : Type u

  topology : TopologicalSpace Carrier

  charted : @ChartedSpace (EuclideanSpace ℝ (Fin 3)) inferInstance Carrier topology

  t2 : @T2Space Carrier topology

  connected : @ConnectedSpace Carrier topology

  compact : @CompactSpace Carrier topology

  smooth : @IsManifold ℝ inferInstance (EuclideanSpace ℝ (Fin 3)) inferInstance inferInstance
    (EuclideanSpace ℝ (Fin 3)) inferInstance 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ Carrier
      topology charted

  basepoint : Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.BasedConnectedClosedSmoothThreeManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.BasedConnectedClosedSmoothThreeManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.BasedConnectedClosedSmoothThreeManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.BasedConnectedClosedSmoothThreeManifold

instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instCoeSortBasedConnectedClosedSmoothThreeManifoldType : CoeSort BasedConnectedClosedSmoothThreeManifold (Type u) :=
  ⟨BasedConnectedClosedSmoothThreeManifold.Carrier⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.instCoeSortBasedConnectedClosedSmoothThreeManifoldType then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.instCoeSortBasedConnectedClosedSmoothThreeManifoldType"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.instCoeSortBasedConnectedClosedSmoothThreeManifoldType ``Submission.DifferentialGeometry.Topology.ThreeManifold.instCoeSortBasedConnectedClosedSmoothThreeManifoldType

instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instTopologicalSpaceCarrier (M : BasedConnectedClosedSmoothThreeManifold) : TopologicalSpace M := M.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.instTopologicalSpaceCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.instTopologicalSpaceCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.instTopologicalSpaceCarrier ``Submission.DifferentialGeometry.Topology.ThreeManifold.instTopologicalSpaceCarrier
instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instChartedSpaceEuclideanSpaceRealFinOfNatNatCarrier (M : BasedConnectedClosedSmoothThreeManifold) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := M.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.instChartedSpaceEuclideanSpaceRealFinOfNatNatCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.instChartedSpaceEuclideanSpaceRealFinOfNatNatCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.instChartedSpaceEuclideanSpaceRealFinOfNatNatCarrier ``Submission.DifferentialGeometry.Topology.ThreeManifold.instChartedSpaceEuclideanSpaceRealFinOfNatNatCarrier
instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instT2SpaceCarrier (M : BasedConnectedClosedSmoothThreeManifold) : T2Space M := M.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.instT2SpaceCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.instT2SpaceCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.instT2SpaceCarrier ``Submission.DifferentialGeometry.Topology.ThreeManifold.instT2SpaceCarrier
instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instConnectedSpaceCarrier (M : BasedConnectedClosedSmoothThreeManifold) : ConnectedSpace M := M.connected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.instConnectedSpaceCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.instConnectedSpaceCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.instConnectedSpaceCarrier ``Submission.DifferentialGeometry.Topology.ThreeManifold.instConnectedSpaceCarrier
instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instCompactSpaceCarrier (M : BasedConnectedClosedSmoothThreeManifold) : CompactSpace M := M.compact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.instCompactSpaceCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.instCompactSpaceCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.instCompactSpaceCarrier ``Submission.DifferentialGeometry.Topology.ThreeManifold.instCompactSpaceCarrier
instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopCarrier (M : BasedConnectedClosedSmoothThreeManifold) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ M := M.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopCarrier ``Submission.DifferentialGeometry.Topology.ThreeManifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopCarrier

noncomputable def fundamentalGroupSourceFreeProductEquivCoprod
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B) :
    fundamentalGroupSourceFreeProduct a b ≃*
      Monoid.Coprod (FundamentalGroup A a) (FundamentalGroup B b) :=
  (coprodIMulEquiv
    (fundamentalGroupSourceFactor a b)
    (boolCoprodFamily (FundamentalGroup A a) (FundamentalGroup B b)) fun
      | false => (MulEquiv.ulift : ULift.{u} (FundamentalGroup A a) ≃*
          FundamentalGroup A a).symm
      | true => (MulEquiv.ulift : ULift.{u} (FundamentalGroup B b) ≃*
          FundamentalGroup B b).symm).trans
    (coprodIBoolEquivCoprod (FundamentalGroup A a) (FundamentalGroup B b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod


theorem fundamentalGroupSourceFreeProductEquivCoprod_of_false
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (g : FundamentalGroup A a) :
    fundamentalGroupSourceFreeProductEquivCoprod a b
        (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor a b) (i := _root_.Bool.false) g) =
      Monoid.Coprod.inl g := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_false then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_false"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_false ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_false


theorem fundamentalGroupSourceFreeProductEquivCoprod_of_true
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (a : A) (b : B)
    (g : FundamentalGroup B b) :
    fundamentalGroupSourceFreeProductEquivCoprod a b
        (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor a b) (i := _root_.Bool.true) g) =
      Monoid.Coprod.inr g := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_true then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_true"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_true ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupSourceFreeProductEquivCoprod_of_true


structure ConnectedSumStep
    (A B C : BasedConnectedClosedSmoothThreeManifold) where

  leftCell : SmoothEmbeddedClosedThreeCellWithCollar A

  rightCell : SmoothEmbeddedClosedThreeCellWithCollar B

  glue : CellBoundary 3 ≃ₜ CellBoundary 3

  boundaryPoint : CellBoundary 3

  leftConnector : Path
    (connectedSumLeftGluingPoint leftCell boundaryPoint : A) A.basepoint

  rightConnector : Path
    (connectedSumRightGluingPoint rightCell glue boundaryPoint : B) B.basepoint

  realization : EmbeddedCellConnectedSum leftCell rightCell glue ≃ₜ C

  realization_basepoint : realization
    (connectedSumNeckMidpoint leftCell.boundaryMap rightCell.boundaryMap glue boundaryPoint) =
      C.basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep


noncomputable def ConnectedSumStep.sourceBasepointEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    fundamentalGroupSourceFreeProduct A.basepoint B.basepoint ≃*
      fundamentalGroupSourceFreeProduct
        (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
        (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B) :=
  coprodIMulEquiv
    (fundamentalGroupSourceFactor A.basepoint B.basepoint)
    (fundamentalGroupSourceFactor
      (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
      (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B)) fun
    | false => DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector
    | true => DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.sourceBasepointEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.sourceBasepointEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.sourceBasepointEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.sourceBasepointEquiv

noncomputable def ConnectedSumStep.realizationFundamentalGroupEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup (EmbeddedCellConnectedSum s.leftCell s.rightCell s.glue)
        (connectedSumNeckMidpoint s.leftCell.boundaryMap s.rightCell.boundaryMap
          s.glue s.boundaryPoint) ≃*
      FundamentalGroup C C.basepoint :=
  DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    s.realization.toHomotopyEquiv
    (connectedSumNeckMidpoint s.leftCell.boundaryMap s.rightCell.boundaryMap
      s.glue s.boundaryPoint)
    C.basepoint s.realization_basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.realizationFundamentalGroupEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.realizationFundamentalGroupEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.realizationFundamentalGroupEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.realizationFundamentalGroupEquiv

noncomputable def ConnectedSumStep.forwardFundamentalGroupEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    Monoid.Coprod (FundamentalGroup A A.basepoint) (FundamentalGroup B B.basepoint) ≃*
      FundamentalGroup C C.basepoint :=
  (fundamentalGroupSourceFreeProductEquivCoprod A.basepoint B.basepoint).symm.trans <|
    (s.sourceBasepointEquiv.trans <|
      (fundamentalGroupEquiv_connectedSum
        s.leftCell s.rightCell s.glue s.boundaryPoint).trans <|
          s.realizationFundamentalGroupEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv


noncomputable def ConnectedSumStep.fundamentalGroupEquiv
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup C C.basepoint ≃*
      Monoid.Coprod (FundamentalGroup A A.basepoint) (FundamentalGroup B B.basepoint) :=
  s.forwardFundamentalGroupEquiv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv

noncomputable def ConnectedSumStep.leftFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup A A.basepoint →* FundamentalGroup C C.basepoint :=
  s.realizationFundamentalGroupEquiv.toMonoidHom.comp
    (connectedSumLeftTransportedFactorHom
      s.leftCell s.rightCell s.glue s.boundaryPoint s.leftConnector)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.leftFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.leftFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.leftFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.leftFactorHom

noncomputable def ConnectedSumStep.rightFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    FundamentalGroup B B.basepoint →* FundamentalGroup C C.basepoint :=
  s.realizationFundamentalGroupEquiv.toMonoidHom.comp
    (connectedSumRightTransportedFactorHom
      s.leftCell s.rightCell s.glue s.boundaryPoint s.rightConnector)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.rightFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.rightFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.rightFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.rightFactorHom


theorem ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inl
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.forwardFundamentalGroupEquiv.toMonoidHom.comp Monoid.Coprod.inl =
      s.leftFactorHom := by
  ext g
  change
    s.realizationFundamentalGroupEquiv
      ((fundamentalGroupEquiv_connectedSum
        s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of (i := _root_.Bool.false)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g))) = _
  have h := DFunLike.congr_fun
    (fundamentalGroupEquiv_connectedSum_comp_left
      s.leftCell s.rightCell s.glue s.boundaryPoint)
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g)
  change
    (fundamentalGroupEquiv_connectedSum
      s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
            (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B))
          (i := _root_.Bool.false)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g)) =
      connectedSumLeftFactorHom s.leftCell s.rightCell s.glue s.boundaryPoint
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.leftConnector g) at h
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inl ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inl


theorem ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inr
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.forwardFundamentalGroupEquiv.toMonoidHom.comp Monoid.Coprod.inr =
      s.rightFactorHom := by
  ext g
  change
    s.realizationFundamentalGroupEquiv
      ((fundamentalGroupEquiv_connectedSum
        s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of (i := _root_.Bool.true)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g))) = _
  have h := DFunLike.congr_fun
    (fundamentalGroupEquiv_connectedSum_comp_right
      s.leftCell s.rightCell s.glue s.boundaryPoint)
    (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g)
  change
    (fundamentalGroupEquiv_connectedSum
      s.leftCell s.rightCell s.glue s.boundaryPoint)
        (Monoid.CoprodI.of
          (M := fundamentalGroupSourceFactor
            (connectedSumLeftGluingPoint s.leftCell s.boundaryPoint : A)
            (connectedSumRightGluingPoint s.rightCell s.glue s.boundaryPoint : B))
          (i := _root_.Bool.true)
          (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g)) =
      connectedSumRightFactorHom s.leftCell s.rightCell s.glue s.boundaryPoint
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint s.rightConnector g) at h
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inr ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.forwardFundamentalGroupEquiv_comp_inr

theorem ConnectedSumStep.fundamentalGroupEquiv_comp_leftFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.fundamentalGroupEquiv.toMonoidHom.comp s.leftFactorHom = Monoid.Coprod.inl := by
  ext g
  apply s.forwardFundamentalGroupEquiv.injective
  change s.forwardFundamentalGroupEquiv
      (s.forwardFundamentalGroupEquiv.symm (s.leftFactorHom g)) =
    s.forwardFundamentalGroupEquiv (Monoid.Coprod.inl g)
  rw [s.forwardFundamentalGroupEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun s.forwardFundamentalGroupEquiv_comp_inl g).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_leftFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_leftFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_leftFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_leftFactorHom

theorem ConnectedSumStep.fundamentalGroupEquiv_comp_rightFactorHom
    {A B C : BasedConnectedClosedSmoothThreeManifold} (s : ConnectedSumStep A B C) :
    s.fundamentalGroupEquiv.toMonoidHom.comp s.rightFactorHom = Monoid.Coprod.inr := by
  ext g
  apply s.forwardFundamentalGroupEquiv.injective
  change s.forwardFundamentalGroupEquiv
      (s.forwardFundamentalGroupEquiv.symm (s.rightFactorHom g)) =
    s.forwardFundamentalGroupEquiv (Monoid.Coprod.inr g)
  rw [s.forwardFundamentalGroupEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun s.forwardFundamentalGroupEquiv_comp_inr g).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_rightFactorHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_rightFactorHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_rightFactorHom ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumStep.fundamentalGroupEquiv_comp_rightFactorHom

inductive LeftAssociatedConnectedSumConstruction :
    (r : ℕ) → BasedConnectedClosedSmoothThreeManifold → Type (u + 1)
  | empty (result : BasedConnectedClosedSmoothThreeManifold)
      (sphereRealization : result ≃ₜ DifferentialGeometry.Topology.SphereThree)
      (sphereRealization_basepoint :
        sphereRealization result.basepoint = DifferentialGeometry.Topology.sphereThreeNorth) :
      LeftAssociatedConnectedSumConstruction 0 result
  | singleton (factor : BasedConnectedClosedSmoothThreeManifold) :
      LeftAssociatedConnectedSumConstruction 1 factor
  | append {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
      (previous : LeftAssociatedConnectedSumConstruction r previousResult)
      (nonempty : 0 < r)
      (factor result : BasedConnectedClosedSmoothThreeManifold)
      (step : ConnectedSumStep previousResult factor result) :
      LeftAssociatedConnectedSumConstruction (r + 1) result

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction

def LeftAssociatedConnectedSumConstruction.factorManifold
    {r : ℕ} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : LeftAssociatedConnectedSumConstruction r result) :
    Fin r → BasedConnectedClosedSmoothThreeManifold :=
  match c with
  | .empty _ _ _ => fun i => Fin.elim0 i
  | .singleton factor => fun _ => factor
  | .append previous _ factor _ _ =>
      Fin.lastCases factor previous.factorManifold

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold

@[simp]
theorem LeftAssociatedConnectedSumConstruction.factorManifold_singleton
    (factor : BasedConnectedClosedSmoothThreeManifold) (i : Fin 1) :
    (LeftAssociatedConnectedSumConstruction.singleton factor).factorManifold i = factor := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_singleton ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_singleton

@[simp]
theorem LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorManifold
        (Fin.castSucc i) =
      previous.factorManifold i := by
  simp [LeftAssociatedConnectedSumConstruction.factorManifold]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc

@[simp]
theorem LeftAssociatedConnectedSumConstruction.factorManifold_append_last
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorManifold
        (Fin.last r) = factor := by
  simp [LeftAssociatedConnectedSumConstruction.factorManifold]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_last ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorManifold_append_last


abbrev LeftAssociatedConnectedSumConstruction.factorFundamentalGroup
    {r : ℕ} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : LeftAssociatedConnectedSumConstruction r result) (i : Fin r) :=
  FundamentalGroup (c.factorManifold i) (c.factorManifold i).basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroup ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroup

noncomputable instance LeftAssociatedConnectedSumConstruction.factorFundamentalGroupGroup
    {r : ℕ} {result : BasedConnectedClosedSmoothThreeManifold}
    (c : LeftAssociatedConnectedSumConstruction r result) (i : Fin r) :
    Group (c.factorFundamentalGroup i) := by
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroupGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroupGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroupGroup ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorFundamentalGroupGroup


def basedFundamentalGroupEquivOfEq
    {A B : BasedConnectedClosedSmoothThreeManifold} (h : A = B) :
    FundamentalGroup A A.basepoint ≃* FundamentalGroup B B.basepoint := by
  subst B
  exact MulEquiv.refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.basedFundamentalGroupEquivOfEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.basedFundamentalGroupEquivOfEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.basedFundamentalGroupEquivOfEq ``Submission.DifferentialGeometry.Topology.ThreeManifold.basedFundamentalGroupEquivOfEq

noncomputable def appendCastSuccFactorEquiv
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorFundamentalGroup
        (Fin.castSucc i) ≃*
      previous.factorFundamentalGroup i :=
  basedFundamentalGroupEquivOfEq
    (LeftAssociatedConnectedSumConstruction.factorManifold_append_castSucc
      previous nonempty factor result step i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendCastSuccFactorEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendCastSuccFactorEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendCastSuccFactorEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendCastSuccFactorEquiv

noncomputable def appendLastFactorEquiv
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (LeftAssociatedConnectedSumConstruction.append previous nonempty factor result step).factorFundamentalGroup
        (Fin.last r) ≃*
      FundamentalGroup factor factor.basepoint :=
  basedFundamentalGroupEquivOfEq
    (LeftAssociatedConnectedSumConstruction.factorManifold_append_last
      previous nonempty factor result step)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendLastFactorEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendLastFactorEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendLastFactorEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendLastFactorEquiv


def factorToSingletonConnectedSumFreeProduct
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    FundamentalGroup factor factor.basepoint →*
      Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup :=
  Monoid.CoprodI.of (M :=
    (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup) (i := 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.factorToSingletonConnectedSumFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.factorToSingletonConnectedSumFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.factorToSingletonConnectedSumFreeProduct ``Submission.DifferentialGeometry.Topology.ThreeManifold.factorToSingletonConnectedSumFreeProduct


def singletonConnectedSumFreeProductToFactor
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup →*
      FundamentalGroup factor factor.basepoint :=
  Monoid.CoprodI.lift fun _ => MonoidHom.id _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProductToFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProductToFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProductToFactor ``Submission.DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProductToFactor

theorem singletonConnectedSumFreeProduct_forward_inverse
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    (singletonConnectedSumFreeProductToFactor factor).comp
        (factorToSingletonConnectedSumFreeProduct factor) =
      MonoidHom.id (FundamentalGroup factor factor.basepoint) := by
  ext g
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_forward_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_forward_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_forward_inverse ``Submission.DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_forward_inverse

theorem singletonConnectedSumFreeProduct_inverse_forward
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    (factorToSingletonConnectedSumFreeProduct factor).comp
        (singletonConnectedSumFreeProductToFactor factor) =
      MonoidHom.id
        (Monoid.CoprodI
          (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_inverse_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_inverse_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_inverse_forward ``Submission.DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFreeProduct_inverse_forward

noncomputable def singletonConnectedSumFundamentalGroupEquiv
    (factor : BasedConnectedClosedSmoothThreeManifold) :
    FundamentalGroup factor factor.basepoint ≃*
      Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup :=
  MonoidHom.toMulEquiv
    (factorToSingletonConnectedSumFreeProduct factor)
    (singletonConnectedSumFreeProductToFactor factor)
    (singletonConnectedSumFreeProduct_forward_inverse factor)
    (singletonConnectedSumFreeProduct_inverse_forward factor)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv


theorem singletonConnectedSumFundamentalGroupEquiv_apply
    (factor : BasedConnectedClosedSmoothThreeManifold)
    (g : FundamentalGroup factor factor.basepoint) :
    singletonConnectedSumFundamentalGroupEquiv factor g =
      Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.singleton factor).factorFundamentalGroup)
        (i := 0) g := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.singletonConnectedSumFundamentalGroupEquiv_apply


def appendFactorFreeProductToCoprod
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    Monoid.CoprodI ((LeftAssociatedConnectedSumConstruction.append
      previous nonempty factor result step).factorFundamentalGroup) →*
      Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
        (FundamentalGroup factor factor.basepoint) :=
  Monoid.CoprodI.lift <| Fin.lastCases
    (Monoid.Coprod.inr.comp
      (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom)
    (fun i => Monoid.Coprod.inl.comp <|
      (Monoid.CoprodI.of (M := previous.factorFundamentalGroup) (i := i)).comp
        (appendCastSuccFactorEquiv previous nonempty factor result step i).toMonoidHom)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductToCoprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductToCoprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductToCoprod ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductToCoprod


def coprodToAppendFactorFreeProduct
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
        (FundamentalGroup factor factor.basepoint) →*
      Monoid.CoprodI ((LeftAssociatedConnectedSumConstruction.append
        previous nonempty factor result step).factorFundamentalGroup) :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.lift fun i =>
      (Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)
        (i := Fin.castSucc i)).comp
          (appendCastSuccFactorEquiv previous nonempty factor result step i).symm.toMonoidHom)
    ((Monoid.CoprodI.of
      (M := (LeftAssociatedConnectedSumConstruction.append
        previous nonempty factor result step).factorFundamentalGroup)
      (i := Fin.last r)).comp
        (appendLastFactorEquiv previous nonempty factor result step).symm.toMonoidHom)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.coprodToAppendFactorFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.coprodToAppendFactorFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.coprodToAppendFactorFreeProduct ``Submission.DifferentialGeometry.Topology.ThreeManifold.coprodToAppendFactorFreeProduct

theorem appendFactorFreeProduct_forward_inverse
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (appendFactorFreeProductToCoprod previous nonempty factor result step).comp
        (coprodToAppendFactorFreeProduct previous nonempty factor result step) =
      MonoidHom.id
        (Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
          (FundamentalGroup factor factor.basepoint)) := by
  apply Monoid.Coprod.hom_ext
  · apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]
  · ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_forward_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_forward_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_forward_inverse ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_forward_inverse

theorem appendFactorFreeProduct_inverse_forward
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (coprodToAppendFactorFreeProduct previous nonempty factor result step).comp
        (appendFactorFreeProductToCoprod previous nonempty factor result step) =
      MonoidHom.id
        (Monoid.CoprodI ((LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]
  · ext g
    simp [appendFactorFreeProductToCoprod, coprodToAppendFactorFreeProduct]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_inverse_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_inverse_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_inverse_forward ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProduct_inverse_forward

noncomputable def appendFactorFreeProductEquiv
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup ≃*
      Monoid.Coprod (Monoid.CoprodI previous.factorFundamentalGroup)
        (FundamentalGroup factor factor.basepoint) :=
  MonoidHom.toMulEquiv
    (appendFactorFreeProductToCoprod previous nonempty factor result step)
    (coprodToAppendFactorFreeProduct previous nonempty factor result step)
    (appendFactorFreeProduct_inverse_forward previous nonempty factor result step)
    (appendFactorFreeProduct_forward_inverse previous nonempty factor result step)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv


theorem appendFactorFreeProductEquiv_comp_castSucc
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := (LeftAssociatedConnectedSumConstruction.append
            previous nonempty factor result step).factorFundamentalGroup)
          (i := Fin.castSucc i)) =
      Monoid.Coprod.inl.comp
        ((Monoid.CoprodI.of (M := previous.factorFundamentalGroup) (i := i)).comp
          (appendCastSuccFactorEquiv
            previous nonempty factor result step i).toMonoidHom) := by
  ext g
  simp [appendFactorFreeProductEquiv, appendFactorFreeProductToCoprod]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_castSucc ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_castSucc


theorem appendFactorFreeProductEquiv_comp_last
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).toMonoidHom.comp
        (Monoid.CoprodI.of
          (M := (LeftAssociatedConnectedSumConstruction.append
            previous nonempty factor result step).factorFundamentalGroup)
          (i := Fin.last r)) =
      Monoid.Coprod.inr.comp
        (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom := by
  ext g
  simp [appendFactorFreeProductEquiv, appendFactorFreeProductToCoprod]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_last ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_comp_last

theorem appendFactorFreeProductEquiv_symm_comp_inl_castSucc
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) (i : Fin r) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).symm.toMonoidHom.comp
        (Monoid.Coprod.inl.comp
          ((Monoid.CoprodI.of (M := previous.factorFundamentalGroup) (i := i)).comp
            (appendCastSuccFactorEquiv
              previous nonempty factor result step i).toMonoidHom)) =
      (Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)
        (i := Fin.castSucc i)) := by
  ext g
  apply (appendFactorFreeProductEquiv previous nonempty factor result step).injective
  change (appendFactorFreeProductEquiv previous nonempty factor result step)
      ((appendFactorFreeProductEquiv previous nonempty factor result step).symm
        (Monoid.Coprod.inl
          (Monoid.CoprodI.of
            ((appendCastSuccFactorEquiv previous nonempty factor result step i) g)))) =
    (appendFactorFreeProductEquiv previous nonempty factor result step)
      (Monoid.CoprodI.of g)
  rw [(appendFactorFreeProductEquiv previous nonempty factor result step).apply_symm_apply]
  exact (DFunLike.congr_fun
    (appendFactorFreeProductEquiv_comp_castSucc
      previous nonempty factor result step i) g).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inl_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inl_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inl_castSucc ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inl_castSucc

theorem appendFactorFreeProductEquiv_symm_comp_inr_last
    {r : ℕ} {previousResult : BasedConnectedClosedSmoothThreeManifold}
    (previous : LeftAssociatedConnectedSumConstruction r previousResult)
    (nonempty : 0 < r)
    (factor result : BasedConnectedClosedSmoothThreeManifold)
    (step : ConnectedSumStep previousResult factor result) :
    (appendFactorFreeProductEquiv previous nonempty factor result step).symm.toMonoidHom.comp
        (Monoid.Coprod.inr.comp
          (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom) =
      (Monoid.CoprodI.of
        (M := (LeftAssociatedConnectedSumConstruction.append
          previous nonempty factor result step).factorFundamentalGroup)
        (i := Fin.last r)) := by
  ext g
  apply (appendFactorFreeProductEquiv previous nonempty factor result step).injective
  change (appendFactorFreeProductEquiv previous nonempty factor result step)
      ((appendFactorFreeProductEquiv previous nonempty factor result step).symm
        (Monoid.Coprod.inr
          ((appendLastFactorEquiv previous nonempty factor result step) g))) =
    (appendFactorFreeProductEquiv previous nonempty factor result step)
      (Monoid.CoprodI.of g)
  rw [(appendFactorFreeProductEquiv previous nonempty factor result step).apply_symm_apply]
  exact (DFunLike.congr_fun
    (appendFactorFreeProductEquiv_comp_last
      previous nonempty factor result step) g).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inr_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inr_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inr_last ``Submission.DifferentialGeometry.Topology.ThreeManifold.appendFactorFreeProductEquiv_symm_comp_inr_last

noncomputable def emptyConnectedSumFundamentalGroupEquiv
    (result : BasedConnectedClosedSmoothThreeManifold)
    (sphereRealization : result ≃ₜ DifferentialGeometry.Topology.SphereThree)
    (sphereRealization_basepoint :
      sphereRealization result.basepoint = DifferentialGeometry.Topology.sphereThreeNorth) :
    FundamentalGroup result result.basepoint ≃*
      Monoid.CoprodI
        (LeftAssociatedConnectedSumConstruction.empty result sphereRealization
          sphereRealization_basepoint).factorFundamentalGroup := by
  let sphereEquiv : FundamentalGroup result result.basepoint ≃*
      FundamentalGroup DifferentialGeometry.Topology.SphereThree DifferentialGeometry.Topology.sphereThreeNorth :=
    DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      sphereRealization.toHomotopyEquiv result.basepoint
        DifferentialGeometry.Topology.sphereThreeNorth sphereRealization_basepoint
  let target := Monoid.CoprodI
    (LeftAssociatedConnectedSumConstruction.empty result sphereRealization
      sphereRealization_basepoint).factorFundamentalGroup
  letI : Subsingleton target :=
    (coprodI_subsingleton_iff _).mpr fun i => Fin.elim0 i
  letI : Unique target :=
    { default := 1
      uniq := fun x => Subsingleton.elim x 1 }
  letI : Unique (FundamentalGroup DifferentialGeometry.Topology.SphereThree
      DifferentialGeometry.Topology.sphereThreeNorth) :=
    { default := 1
      uniq := fun x => Subsingleton.elim x 1 }
  exact sphereEquiv.trans MulEquiv.ofUnique

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.emptyConnectedSumFundamentalGroupEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.emptyConnectedSumFundamentalGroupEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.emptyConnectedSumFundamentalGroupEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.emptyConnectedSumFundamentalGroupEquiv

noncomputable def fundamentalGroupEquiv_finiteConnectedSum :
    {r : ℕ} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : LeftAssociatedConnectedSumConstruction r result) →
      FundamentalGroup result result.basepoint ≃*
        Monoid.CoprodI c.factorFundamentalGroup
  | _, _, .empty result sphereRealization sphereRealization_basepoint =>
      emptyConnectedSumFundamentalGroupEquiv
        result sphereRealization sphereRealization_basepoint
  | _, _, .singleton factor => singletonConnectedSumFundamentalGroupEquiv factor
  | _, _, .append previous nonempty factor result step =>
      step.fundamentalGroupEquiv.trans <|
        ((fundamentalGroupEquiv_finiteConnectedSum previous).coprodCongr
          (MulEquiv.refl (FundamentalGroup factor factor.basepoint))).trans <|
            (appendFactorFreeProductEquiv previous nonempty factor result step).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum

noncomputable def LeftAssociatedConnectedSumConstruction.factorToResult :
    {r : ℕ} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : LeftAssociatedConnectedSumConstruction r result) →
      (i : Fin r) → c.factorFundamentalGroup i →*
        FundamentalGroup result result.basepoint
  | _, _, .empty _ _ _, i => Fin.elim0 i
  | _, _, .singleton factor, i =>
      (basedFundamentalGroupEquivOfEq
        (LeftAssociatedConnectedSumConstruction.factorManifold_singleton factor i)).toMonoidHom
  | _, _, .append previous nonempty factor result step, i =>
      Fin.lastCases
        (step.rightFactorHom.comp
          (appendLastFactorEquiv previous nonempty factor result step).toMonoidHom)
        (fun j => step.leftFactorHom.comp <|
          (previous.factorToResult j).comp
            (appendCastSuccFactorEquiv
              previous nonempty factor result step j).toMonoidHom)
        i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorToResult then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorToResult"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorToResult ``Submission.DifferentialGeometry.Topology.ThreeManifold.LeftAssociatedConnectedSumConstruction.factorToResult

theorem fundamentalGroupEquiv_finiteConnectedSum_comp_factorToResult :
    {r : ℕ} → {result : BasedConnectedClosedSmoothThreeManifold} →
      (c : LeftAssociatedConnectedSumConstruction r result) → (i : Fin r) →
      (fundamentalGroupEquiv_finiteConnectedSum c).toMonoidHom.comp
          (c.factorToResult i) =
        (Monoid.CoprodI.of : c.factorFundamentalGroup i →*
          Monoid.CoprodI c.factorFundamentalGroup) := by
  intro r result c
  induction c with
  | empty result sphereRealization sphereRealization_basepoint =>
      intro i
      exact Fin.elim0 i
  | singleton factor =>
      intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      ext g
      rfl
  | @append r previousResult previous nonempty factor result step ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · ext g
        simp only [fundamentalGroupEquiv_finiteConnectedSum,
          LeftAssociatedConnectedSumConstruction.factorToResult,
          Fin.lastCases_last, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
            (((fundamentalGroupEquiv_finiteConnectedSum previous).coprodCongr
              (MulEquiv.refl (FundamentalGroup factor factor.basepoint)))
                (step.fundamentalGroupEquiv
                  (step.rightFactorHom
                    ((appendLastFactorEquiv
                      previous nonempty factor result step) g)))) =
            Monoid.CoprodI.of g
        have hstep := DFunLike.congr_fun step.fundamentalGroupEquiv_comp_rightFactorHom
          ((appendLastFactorEquiv previous nonempty factor result step) g)
        change step.fundamentalGroupEquiv
            (step.rightFactorHom
              ((appendLastFactorEquiv previous nonempty factor result step) g)) =
          Monoid.Coprod.inr
            ((appendLastFactorEquiv previous nonempty factor result step) g) at hstep
        rw [hstep]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
              (Monoid.Coprod.inr
                ((appendLastFactorEquiv previous nonempty factor result step) g)) =
            Monoid.CoprodI.of g
        exact DFunLike.congr_fun
          (appendFactorFreeProductEquiv_symm_comp_inr_last
            previous nonempty factor result step) g
      · ext g
        simp only [fundamentalGroupEquiv_finiteConnectedSum,
          LeftAssociatedConnectedSumConstruction.factorToResult,
          Fin.lastCases_castSucc, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
            (((fundamentalGroupEquiv_finiteConnectedSum previous).coprodCongr
              (MulEquiv.refl (FundamentalGroup factor factor.basepoint)))
                (step.fundamentalGroupEquiv
                  (step.leftFactorHom
                    (previous.factorToResult j
                      ((appendCastSuccFactorEquiv
                        previous nonempty factor result step j) g))))) =
            Monoid.CoprodI.of g
        have hstep := DFunLike.congr_fun step.fundamentalGroupEquiv_comp_leftFactorHom
          (previous.factorToResult j
            ((appendCastSuccFactorEquiv previous nonempty factor result step j) g))
        change step.fundamentalGroupEquiv
            (step.leftFactorHom
              (previous.factorToResult j
                ((appendCastSuccFactorEquiv previous nonempty factor result step j) g))) =
          Monoid.Coprod.inl
            (previous.factorToResult j
              ((appendCastSuccFactorEquiv
                previous nonempty factor result step j) g)) at hstep
        rw [hstep]
        change
          (appendFactorFreeProductEquiv previous nonempty factor result step).symm
            (Monoid.Coprod.inl
              ((fundamentalGroupEquiv_finiteConnectedSum previous)
                (previous.factorToResult j
                  ((appendCastSuccFactorEquiv
                    previous nonempty factor result step j) g)))) =
            Monoid.CoprodI.of g
        have hih := DFunLike.congr_fun (ih j)
          ((appendCastSuccFactorEquiv previous nonempty factor result step j) g)
        change
          (fundamentalGroupEquiv_finiteConnectedSum previous)
              (previous.factorToResult j
                ((appendCastSuccFactorEquiv previous nonempty factor result step j) g)) =
            Monoid.CoprodI.of
              ((appendCastSuccFactorEquiv previous nonempty factor result step j) g) at hih
        rw [hih]
        exact DFunLike.congr_fun
          (appendFactorFreeProductEquiv_symm_comp_inl_castSucc
            previous nonempty factor result step j) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum_comp_factorToResult then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum_comp_factorToResult"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum_comp_factorToResult ``Submission.DifferentialGeometry.Topology.ThreeManifold.fundamentalGroupEquiv_finiteConnectedSum_comp_factorToResult

end DifferentialGeometry.Topology.ThreeManifold
