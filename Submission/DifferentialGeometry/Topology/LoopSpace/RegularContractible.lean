import Submission.DifferentialGeometry.Topology.LoopSpace.Regular

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Function _root_.ContinuousMap _root_.Manifold
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Topology


abbrev regularContractibleLoop (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] :=
  {γ : regularLoop E M // γ.val.Nullhomotopic}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularContractibleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularContractibleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularContractibleLoop ``Submission.DifferentialGeometry.Topology.regularContractibleLoop

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]


@[instance_reducible] def regularContractibleLoopTopology (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) : TopologicalSpace (regularContractibleLoop E M) :=
  TopologicalSpace.induced Subtype.val (regularLoopTopology e he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularContractibleLoopTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularContractibleLoopTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularContractibleLoopTopology ``Submission.DifferentialGeometry.Topology.regularContractibleLoopTopology


def regularContractibleLoopInclusion (γ : regularContractibleLoop E M) : contractibleLoop M :=
  ⟨γ.val.val, γ.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularContractibleLoopInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularContractibleLoopInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularContractibleLoopInclusion ``Submission.DifferentialGeometry.Topology.regularContractibleLoopInclusion



theorem continuous_regularContractibleLoopInclusion (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) (hemb : _root_.Topology.IsEmbedding e) :
    Continuous[regularContractibleLoopTopology e he, inferInstance]
      (regularContractibleLoopInclusion (E := E) (M := M)) := by
  let : TopologicalSpace (regularLoop E M) := regularLoopTopology e he
  let : TopologicalSpace (regularContractibleLoop E M) := regularContractibleLoopTopology e he
  have hval : Continuous (fun γ : regularContractibleLoop E M => γ.val) := continuous_induced_dom
  exact ((continuous_regularLoop_inclusion e he hemb).comp hval).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_regularContractibleLoopInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_regularContractibleLoopInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_regularContractibleLoopInclusion ``Submission.DifferentialGeometry.Topology.continuous_regularContractibleLoopInclusion



theorem continuous_regularContractibleLoop_iff {K : Type*} [TopologicalSpace K]
    (e : M → F) (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e)
    (Γ : K → regularContractibleLoop E M) :
    Continuous[inferInstance, regularContractibleLoopTopology e he] Γ ↔
      Continuous[inferInstance, regularLoopTopology e he] (fun k => (Γ k).val) :=
  continuous_induced_rng

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_regularContractibleLoop_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_regularContractibleLoop_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_regularContractibleLoop_iff ``Submission.DifferentialGeometry.Topology.continuous_regularContractibleLoop_iff


def regularContractibleLoopConst (q : M) : regularContractibleLoop E M :=
  ⟨⟨.const loopCircle q, contMDiff_const⟩, _root_.ContinuousMap.nullhomotopic_of_constant q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.regularContractibleLoopConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.regularContractibleLoopConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.regularContractibleLoopConst ``Submission.DifferentialGeometry.Topology.regularContractibleLoopConst


theorem continuous_regularContractibleLoopConst (e : M → F)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 e) :
    Continuous[inferInstance, regularContractibleLoopTopology e he]
      (regularContractibleLoopConst (E := E) (M := M)) := by
  apply (continuous_regularContractibleLoop_iff e he _).mpr
  apply (continuous_regularLoop_iff e he _).mpr
  constructor
  · exact he.continuous.comp continuous_fst
  · simp only [regularContractibleLoopConst, ContinuousMap.const_apply, deriv_const]
    exact continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_regularContractibleLoopConst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_regularContractibleLoopConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_regularContractibleLoopConst ``Submission.DifferentialGeometry.Topology.continuous_regularContractibleLoopConst

end DifferentialGeometry.Topology
