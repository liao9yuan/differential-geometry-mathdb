import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor03.Tensoriality

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

noncomputable local instance covariantDerivativeModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedAddCommGroup

noncomputable local instance covariantDerivativeModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelDualNormedSpace

noncomputable local instance covariantDerivativeModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedAddCommGroup

noncomputable local instance covariantDerivativeModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelBilinearNormedSpace

noncomputable local instance covariantDerivativeModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedAddCommGroup

noncomputable local instance covariantDerivativeModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelTrilinearNormedSpace

noncomputable local instance covariantDerivativeModelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedAddCommGroup

noncomputable local instance covariantDerivativeModelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeModelQuadrilinearNormedSpace

noncomputable local instance covariantDerivativeTangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentDualNormedSpace

noncomputable local instance covariantDerivativeTangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentBilinearNormedSpace

noncomputable local instance covariantDerivativeTangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearNormedSpace

local instance covariantDerivativeTangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (covariantDerivativeTangentTrilinearNormedAddCommGroup x).toAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearAddCommGroup

local instance covariantDerivativeTangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    covariantDerivativeTangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    covariantDerivativeTangentTrilinearNormedSpace x
  exact NormedSpace.toModule

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearModule ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearModule

local instance covariantDerivativeTangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (covariantDerivativeTangentTrilinearModule
    x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearSMul ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearSMul

local instance covariantDerivativeTangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    covariantDerivativeTangentTrilinearNormedAddCommGroup x
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearTopology ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentTrilinearTopology

noncomputable local instance covariantDerivativeTangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedAddCommGroup

noncomputable local instance covariantDerivativeTangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTangentQuadrilinearNormedSpace

local instance covariantDerivativeTensor01TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01TotalSpaceTopology

local instance covariantDerivativeTensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01FiberBundle

local instance covariantDerivativeTensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01VectorBundle

local instance covariantDerivativeTensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor01ContMDiffVectorBundle

local instance covariantDerivativeTensor02TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor02TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor02TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor02TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor02TotalSpaceTopology

local instance covariantDerivativeIteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02FiberBundle

local instance covariantDerivativeIteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02VectorBundle

local instance covariantDerivativeIteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeIteratedTensor02ContMDiffVectorBundle

local instance covariantDerivativeTensor03TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03TotalSpaceTopology ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03TotalSpaceTopology

local instance covariantDerivativeTensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03FiberBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03FiberBundle

local instance covariantDerivativeTensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03VectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03VectorBundle

local instance covariantDerivativeTensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03ContMDiffVectorBundle ``Submission.DifferentialGeometry.Geometry.Connection.covariantDerivativeTensor03ContMDiffVectorBundle

private lemma tensor03CovFun_add_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x)
    (v y z w : TangentSpace I x) :
    tensor03CovFun cov (T + T') x v y z w =
      tensor03CovFun cov T x v y z w + tensor03CovFun cov T' x v y z w := by
    classical
    have hT_t : MDiffAtTensor03 T x := hT
    have hT'_t : MDiffAtTensor03 T' x := hT'
    have hsum_T : MDiffAtTensor03 (T + T') x := mdifferentiableAt_add_section hT hT'
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hY : MDiffAt (T% Y) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    have hWx : W x = w := by simp [W]
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [tensor03CovFun_apply, tensor03CovFun_apply, tensor03CovFun_apply]
    rw [tensor03CovAt_apply_of_diff_extend cov hsum_T hY hZ hW,
        tensor03CovAt_apply_of_diff_extend cov hT_t hY hZ hW,
        tensor03CovAt_apply_of_diff_extend cov hT'_t hY hZ hW]
    change mvfderiv (I := I) (fun b => (T + T') b (Y b) (Z b) (W b)) x (X x)
        - (T + T') x (cov.toFun Y x (X x)) (Z x) (W x)
        - (T + T') x (Y x) (cov.toFun Z x (X x)) (W x)
        - (T + T') x (Y x) (Z x) (cov.toFun W x (X x)) =
      (mvfderiv (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (mvfderiv (I := I) (fun b => T' b (Y b) (Z b) (W b)) x (X x)
        - T' x (cov.toFun Y x (X x)) (Z x) (W x)
        - T' x (Y x) (cov.toFun Z x (X x)) (W x)
        - T' x (Y x) (Z x) (cov.toFun W x (X x)))
    have hpair_T : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT_t hY hZ hW
    have hpair_T' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T' b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT'_t hY hZ hW
    have hpair_eq : (fun b : M => (T + T') b (Y b) (Z b) (W b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) +
          (fun b : M => T' b (Y b) (Z b) (W b)) := by
      funext b
      simp only [Pi.add_apply, add_apply]
    have hext_add : mvfderiv (I := I) (fun b => (T + T') b (Y b) (Z b) (W b)) x =
        mvfderiv (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        mvfderiv (I := I) (fun b => T' b (Y b) (Z b) (W b)) x := by
      rw [hpair_eq, mvfderiv_add hpair_T hpair_T']
    rw [hext_add]
    simp only [Pi.add_apply, add_apply]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CovFun_add_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.tensor03CovFun_add_apply target :: scope.openDecls } }

private lemma tensor03CovFun_add
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    tensor03CovFun cov (T + T') x =
      tensor03CovFun cov T x + tensor03CovFun cov T' x := by
  ext v y z w
  exact tensor03CovFun_add_apply cov hT hT' v y z w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CovFun_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.tensor03CovFun_add target :: scope.openDecls } }

private lemma tensor03CovFun_leibniz_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {g : M → ℝ} {x : M} (hT : MDiffAtTensor03 T x) (hg : MDiffAt g x)
    (v y z w : TangentSpace I x) :
    tensor03CovFun cov (g • T) x v y z w =
      g x • tensor03CovFun cov T x v y z w +
        mvfderiv (I := I) g x v • T x y z w := by
    classical
    have hT_t : MDiffAtTensor03 T x := hT
    have hsum_T : MDiffAtTensor03 (g • T) x := hg.smul_section hT
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hY : MDiffAt (T% Y) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := _root_.FiberBundle.mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    have hWx : W x = w := by simp [W]
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [tensor03CovFun_apply, tensor03CovFun_apply]
    rw [tensor03CovAt_apply_of_diff_extend cov hsum_T hY hZ hW]
    rw [tensor03CovAt_apply_of_diff_extend cov hT_t hY hZ hW]
    change mvfderiv (I := I) (fun b => (g • T) b (Y b) (Z b) (W b)) x (X x)
        - (g • T) x (cov.toFun Y x (X x)) (Z x) (W x)
        - (g • T) x (Y x) (cov.toFun Z x (X x)) (W x)
        - (g • T) x (Y x) (Z x) (cov.toFun W x (X x)) =
      g x • (mvfderiv (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      mvfderiv (I := I) g x (X x) • T x (Y x) (Z x) (W x)
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT_t hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hpair_eq : (fun b : M => (g • T) b (Y b) (Z b) (W b)) = (fun b : M => g b * h b) := by
      funext b
      simp only [Pi.smul_apply', smul_apply, smul_eq_mul, hh_def]
    rw [hpair_eq, mvfderiv_mul_apply hg' hh]
    simp only [Pi.smul_apply', smul_apply]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [smul_eq_mul]
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CovFun_leibniz_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.tensor03CovFun_leibniz_apply target :: scope.openDecls } }

private lemma tensor03CovFun_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {g : M → ℝ} {x : M} (hT : MDiffAtTensor03 T x) (hg : MDiffAt g x) :
    tensor03CovFun cov (g • T) x =
      g x • tensor03CovFun cov T x + (mvfderiv (I := I) g x).smulRight (T x) := by
  ext v y z w
  simpa only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply] using tensor03CovFun_leibniz_apply cov hT hg v y z w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CovFun_leibniz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.tensor03CovFun_leibniz target :: scope.openDecls } }

lemma tensor03CovFun_isCovariantDerivativeOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (V := (fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (tensor03CovFun cov) Set.univ where
  add hT hT' _hx := tensor03CovFun_add cov hT hT'
  leibniz hT hg _hx := tensor03CovFun_leibniz cov hT hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03CovFun_isCovariantDerivativeOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03CovFun_isCovariantDerivativeOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03CovFun_isCovariantDerivativeOn ``Submission.DifferentialGeometry.Geometry.Connection.tensor03CovFun_isCovariantDerivativeOn

def tensor03Cov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  toFun := tensor03CovFun cov
  isCovariantDerivativeOnUniv := tensor03CovFun_isCovariantDerivativeOn cov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03Cov then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03Cov"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03Cov ``Submission.DifferentialGeometry.Geometry.Connection.tensor03Cov

lemma tensor03Cov_toFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (tensor03Cov cov).toFun = tensor03CovFun cov := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tensor03Cov_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tensor03Cov_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tensor03Cov_toFun ``Submission.DifferentialGeometry.Geometry.Connection.tensor03Cov_toFun

end Connection
end Geometry
end DifferentialGeometry

end
