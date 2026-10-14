import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor03.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

noncomputable local instance tensor03CalculusModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedAddCommGroup

noncomputable local instance tensor03CalculusModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelDualNormedSpace

noncomputable local instance tensor03CalculusModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedAddCommGroup

noncomputable local instance tensor03CalculusModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelBilinearNormedSpace

noncomputable local instance tensor03CalculusModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedAddCommGroup

noncomputable local instance tensor03CalculusModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelTrilinearNormedSpace

noncomputable local instance tensor03CalculusModelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedAddCommGroup

noncomputable local instance tensor03CalculusModelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusModelQuadrilinearNormedSpace

noncomputable local instance tensor03CalculusTangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentDualNormedSpace

noncomputable local instance tensor03CalculusTangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentBilinearNormedSpace

noncomputable local instance tensor03CalculusTangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearNormedSpace

local instance tensor03CalculusTangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tensor03CalculusTangentTrilinearNormedAddCommGroup x).toAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearAddCommGroup

local instance tensor03CalculusTangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensor03CalculusTangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensor03CalculusTangentTrilinearNormedSpace x
  exact NormedSpace.toModule

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearModule ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearModule

local instance tensor03CalculusTangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (tensor03CalculusTangentTrilinearModule x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearSMul ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearSMul

local instance tensor03CalculusTangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    tensor03CalculusTangentTrilinearNormedAddCommGroup x
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearTopology ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentTrilinearTopology

local instance tensor03CalculusSectionAddCommGroup :
    AddCommGroup
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.addCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionAddCommGroup

local instance tensor03CalculusSectionModule :
    Module ℝ
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.module M _ ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionModule ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusSectionModule

noncomputable local instance tensor03CalculusTangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedAddCommGroup

noncomputable local instance tensor03CalculusTangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTangentQuadrilinearNormedSpace

local instance tensor03CalculusTensor01TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01TotalSpaceTopology

local instance tensor03CalculusTensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01FiberBundle

local instance tensor03CalculusTensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01VectorBundle

local instance tensor03CalculusTensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor01ContMDiffVectorBundle

local instance tensor03CalculusTensor02TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor02TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor02TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor02TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor02TotalSpaceTopology

local instance tensor03CalculusIteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02FiberBundle

local instance tensor03CalculusIteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02VectorBundle

local instance tensor03CalculusIteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusIteratedTensor02ContMDiffVectorBundle

local instance tensor03CalculusTensor03TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03TotalSpaceTopology

local instance tensor03CalculusTensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03FiberBundle

local instance tensor03CalculusTensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03VectorBundle

local instance tensor03CalculusTensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CalculusTensor03ContMDiffVectorBundle

theorem tensor03Cov_pairing
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x)
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x)
    (v : TangentSpace I x) :
    mvfderiv (I := I) (fun b => T b (Y b) (Z b) (W b)) x v =
      ((tensor03Cov cov).toFun T x v) (Y x) (Z x) (W x)
        + T x (cov.toFun Y x v) (Z x) (W x)
        + T x (Y x) (cov.toFun Z x v) (W x)
        + T x (Y x) (Z x) (cov.toFun W x v) := by
  classical
  set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
  have hXx : X x = v := by simp [X]
  rw [show v = X x from hXx.symm]
  rw [tensor03Cov_toFun, tensor03CovFun_apply,
      tensor03CovAt_apply_of_diff_extend cov hT hY hZ hW]
  unfold tensor03Scalar
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03Cov_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03Cov_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03Cov_pairing ``Submission.DifferentialGeometry.Geometry.Connection.tensor03Cov_pairing

def tensor02CovIterate
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
      (Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  fun T => (tensor03Cov cov).toFun ((tensor02Cov cov).toFun T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor02CovIterate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor02CovIterate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor02CovIterate ``Submission.DifferentialGeometry.Geometry.Connection.tensor02CovIterate

@[simp] lemma tensor02CovIterate_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    tensor02CovIterate cov T x =
      (tensor03Cov cov).toFun ((tensor02Cov cov).toFun T) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor02CovIterate_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor02CovIterate_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor02CovIterate_apply ``Submission.DifferentialGeometry.Geometry.Connection.tensor02CovIterate_apply

theorem tensor03Cov_add
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    (tensor03Cov cov).toFun (T + T') x =
      (tensor03Cov cov).toFun T x + (tensor03Cov cov).toFun T' x := by
  set D := tensor03Cov cov
  exact D.isCovariantDerivativeOnUniv.add hT hT' (Set.mem_univ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03Cov_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03Cov_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03Cov_add ``Submission.DifferentialGeometry.Geometry.Connection.tensor03Cov_add

theorem tensor03Cov_smul
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (a : ℝ) (hT : MDiffAtTensor03 T x) :
    (tensor03Cov cov).toFun (a • T) x = a • (tensor03Cov cov).toFun T x := by
  set D := tensor03Cov cov
  exact D.isCovariantDerivativeOnUniv.smul_const a hT (Set.mem_univ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03Cov_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03Cov_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03Cov_smul ``Submission.DifferentialGeometry.Geometry.Connection.tensor03Cov_smul

theorem tensor03Cov_sub
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    (tensor03Cov cov).toFun (T - T') x =
      (tensor03Cov cov).toFun T x - (tensor03Cov cov).toFun T' x := by
  have hT'neg : MDiffAtTensor03 (-T') x := mdifferentiableAt_neg_section hT'
  have hneg : (tensor03Cov cov).toFun (-T') x = -(tensor03Cov cov).toFun T' x := by
    simpa only [neg_one_smul] using tensor03Cov_smul cov (-1) hT'
  rw [sub_eq_add_neg, tensor03Cov_add cov hT hT'neg, hneg, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03Cov_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03Cov_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03Cov_sub ``Submission.DifferentialGeometry.Geometry.Connection.tensor03Cov_sub

end Connection
end Geometry
end DifferentialGeometry

end
