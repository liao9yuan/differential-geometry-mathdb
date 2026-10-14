import Submission.DifferentialGeometry.Topology.Homotopy.LoopTopology
import Submission.DifferentialGeometry.Topology.LoopSpace.BasedAdjunction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X]



def genLoopFreeLoopHomeomorph (x : X) :
    GenLoop N (freeLoop X) (FreeLoop.constants x) ≃ₜ freeLoop (GenLoop N X x) where
  toFun p := ⟨fun θ => ⟨⟨fun t => p t θ,
      (_root_.ContinuousEvalConst.continuous_eval_const θ).comp p.val.continuous⟩,
      fun t ht => congrArg (fun γ : freeLoop X => γ θ) (GenLoop.boundary p t ht)⟩,
    by
      apply Continuous.subtype_mk
      apply _root_.ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : loopCircle × (N → unitInterval) => p.val z.2 z.1)
      exact continuous_eval.comp ((p.val.continuous.comp continuous_snd).prodMk continuous_fst)⟩
  invFun γ := ⟨⟨fun t => ⟨fun θ => γ θ t,
      by
        change Continuous (fun θ => (γ θ).val t)
        exact (_root_.ContinuousEvalConst.continuous_eval_const t).comp (continuous_subtype_val.comp γ.continuous)⟩,
      _root_.ContinuousMap.continuous_of_continuous_uncurry _
        (continuous_eval.comp
          ((continuous_subtype_val.comp (γ.continuous.comp continuous_snd)).prodMk continuous_fst))⟩,
    fun t ht => by
      ext θ
      exact GenLoop.boundary (γ θ) t ht⟩
  left_inv p := by ext t θ; rfl
  right_inv γ := by ext θ t; rfl
  continuous_toFun := by
    apply _root_.ContinuousMap.continuous_of_continuous_uncurry
    apply Continuous.subtype_mk
    apply _root_.ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (GenLoop N (freeLoop X) (FreeLoop.constants x) × loopCircle) ×
      (N → unitInterval) => z.1.1.val z.2 z.1.2)
    exact continuous_eval.comp
      ((continuous_eval.comp
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd)).prodMk
          (continuous_snd.comp continuous_fst))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply _root_.ContinuousMap.continuous_of_continuous_uncurry
    apply _root_.ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (freeLoop (GenLoop N X x) × (N → unitInterval)) × loopCircle =>
      (z.1.1 z.2).val z.1.2)
    exact continuous_eval.comp
      ((continuous_subtype_val.comp
        (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))).prodMk
          (continuous_snd.comp continuous_fst))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph


theorem genLoopFreeLoopHomeomorph_apply (x : X)
    (p : GenLoop N (freeLoop X) (FreeLoop.constants x)) (θ : loopCircle)
    (t : N → unitInterval) :
    genLoopFreeLoopHomeomorph x p θ t = p t θ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_apply ``Submission.DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_apply



theorem genLoopFreeLoopHomeomorph_homotopic_iff (x : X)
    (p q : GenLoop N (freeLoop X) (FreeLoop.constants x)) :
    (genLoopFreeLoopHomeomorph x p).Homotopic (genLoopFreeLoopHomeomorph x q) ↔
      GenLoop.Homotopic p q := by
  rw [homotopic_iff_joined, genLoop_homotopic_iff_joined]
  constructor
  · intro h
    simpa only [(genLoopFreeLoopHomeomorph x).symm_apply_apply] using
      h.map (genLoopFreeLoopHomeomorph x).symm.continuous
  · exact fun h => h.map (genLoopFreeLoopHomeomorph x).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_homotopic_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_homotopic_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_homotopic_iff ``Submission.DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_homotopic_iff


def basedCircleInclusion (x : X) : C(basedCircleLoop x, freeLoop X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleInclusion ``Submission.DifferentialGeometry.Topology.basedCircleInclusion



theorem genLoopFreeLoopHomeomorph_inclusion_zero (x : X)
    (p : GenLoop N (basedCircleLoop x) (basedCircleConstant x)) :
    genLoopFreeLoopHomeomorph x
      (genLoopBasedMap (basedCircleInclusion x) (basedCircleConstant x)
        (FreeLoop.constants x) rfl p) 0 = GenLoop.const := by
  ext t
  exact (p t).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_inclusion_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_inclusion_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_inclusion_zero ``Submission.DifferentialGeometry.Topology.genLoopFreeLoopHomeomorph_inclusion_zero

end DifferentialGeometry.Topology
