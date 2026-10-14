import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Differentiability.Tensor
import Submission.DifferentialGeometry.Tensor.Multilinear.Curry.FiniteNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable local instance pointwiseModelDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedAddCommGroup

noncomputable local instance pointwiseModelDualNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelDualNormedSpace

noncomputable local instance pointwiseModelBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedAddCommGroup

noncomputable local instance pointwiseModelBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelBilinearNormedSpace

noncomputable local instance pointwiseModelTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedAddCommGroup

noncomputable local instance pointwiseModelTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelTrilinearNormedSpace

noncomputable local instance pointwiseModelQuadrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedAddCommGroup

noncomputable local instance pointwiseModelQuadrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseModelQuadrilinearNormedSpace

noncomputable local instance pointwiseTangentDualNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedAddCommGroup

noncomputable local instance pointwiseTangentDualNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentDualNormedSpace

noncomputable local instance pointwiseTangentBilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedAddCommGroup

noncomputable local instance pointwiseTangentBilinearNormedSpace (x : M) :
    NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearNormedSpace

noncomputable local instance pointwiseTangentTrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedAddCommGroup

noncomputable local instance pointwiseTangentTrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearNormedSpace

local instance pointwiseTangentTrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (pointwiseTangentTrilinearNormedAddCommGroup x).toAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearAddCommGroup

local instance pointwiseTangentTrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    pointwiseTangentTrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    pointwiseTangentTrilinearNormedSpace x
  exact NormedSpace.toModule

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearModule ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearModule

local instance pointwiseTangentTrilinearSMul (x : M) :
    SMul ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (pointwiseTangentTrilinearModule x).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearSMul ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearSMul

local instance pointwiseTangentTrilinearTopology (x : M) :
    TopologicalSpace
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    pointwiseTangentTrilinearNormedAddCommGroup x
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearTopology ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentTrilinearTopology

local instance pointwiseSectionAddCommGroup :
    AddCommGroup
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.addCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseSectionAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseSectionAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseSectionAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseSectionAddCommGroup

local instance pointwiseSectionModule :
    Module ℝ
      (Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.module M _ ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseSectionModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseSectionModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseSectionModule ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseSectionModule

noncomputable local instance pointwiseTangentQuadrilinearNormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedAddCommGroup

noncomputable local instance pointwiseTangentQuadrilinearNormedSpace (x : M) :
    NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearNormedSpace

local instance pointwiseTangentQuadrilinearAddCommGroup (x : M) :
    AddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
  (pointwiseTangentQuadrilinearNormedAddCommGroup x).toAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearAddCommGroup

local instance pointwiseTangentQuadrilinearModule (x : M) :
    Module ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
    pointwiseTangentQuadrilinearNormedAddCommGroup x
  letI : NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ) :=
    pointwiseTangentQuadrilinearNormedSpace x
  exact NormedSpace.toModule

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearModule ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentQuadrilinearModule

local instance pointwiseTangentBilinearAddCommGroup (x : M) :
    AddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  (pointwiseTangentBilinearNormedAddCommGroup x).toAddCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearAddCommGroup

local instance pointwiseTangentBilinearModule (x : M) :
    Module ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    pointwiseTangentBilinearNormedAddCommGroup x
  letI : NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
    pointwiseTangentBilinearNormedSpace x
  exact NormedSpace.toModule

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearModule ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTangentBilinearModule

local instance pointwiseBilinearSectionAddCommGroup :
    AddCommGroup (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.addCommGroup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionAddCommGroup

local instance pointwiseBilinearSectionModule :
    Module ℝ (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Pi.module M _ ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionModule ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseBilinearSectionModule

local instance pointwiseTensor0SModelNormedAddCommGroup {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.instNormedAddCommGroupTensor0SModel s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedAddCommGroup

local instance pointwiseTensor0SModelNormedSpace {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModelNormedSpace s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor0SModelNormedSpace

local instance pointwiseTensorRSModelNormedAddCommGroup {r s : ℕ} :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedAddCommGroup

local instance pointwiseTensorRSModelNormedSpace {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedSpace ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSModelNormedSpace

local instance pointwiseTensor01TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor01TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01TotalSpaceTopology ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor01TotalSpaceTopology

local instance pointwiseTensor01FiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor01FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01FiberBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor01FiberBundle

local instance pointwiseTensor01VectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) ℝ (fun _ : M => ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor01VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01VectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor01VectorBundle

local instance pointwiseTensor01ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor01ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor01ContMDiffVectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor01ContMDiffVectorBundle

local instance pointwiseTensor02TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor02TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor02TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor02TotalSpaceTopology ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor02TotalSpaceTopology

local instance pointwiseIteratedTensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02FiberBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02FiberBundle

local instance pointwiseIteratedTensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02VectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02VectorBundle

local instance pointwiseIteratedTensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02ContMDiffVectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseIteratedTensor02ContMDiffVectorBundle

local instance pointwiseTensor03TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor03TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03TotalSpaceTopology ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor03TotalSpaceTopology

local instance pointwiseTensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor03FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03FiberBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor03FiberBundle

local instance pointwiseTensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor03VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03VectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor03VectorBundle

local instance pointwiseTensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor03ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor03ContMDiffVectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor03ContMDiffVectorBundle

local instance pointwiseTensor04TotalSpaceTopology :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04TotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor04TotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04TotalSpaceTopology ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor04TotalSpaceTopology

local instance pointwiseTensor04FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04FiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor04FiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04FiberBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor04FiberBundle

local instance pointwiseTensor04VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id ℝ)
    E (TangentSpace I) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04VectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor04VectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04VectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor04VectorBundle

local instance pointwiseTensor04ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04ContMDiffVectorBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensor04ContMDiffVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensor04ContMDiffVectorBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensor04ContMDiffVectorBundle

local instance pointwiseTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundleTopology r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSTotalSpaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSTotalSpaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSTotalSpaceTopology ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSTotalSpaceTopology

local instance pointwiseTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundleFiber r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSFiberBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSFiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSFiberBundle ``Submission.DifferentialGeometry.Analysis.Spectral.pointwiseTensorRSFiberBundle

end Spectral
end Analysis
end DifferentialGeometry

end
