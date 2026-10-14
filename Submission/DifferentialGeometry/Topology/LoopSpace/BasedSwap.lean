import Submission.DifferentialGeometry.Topology.LoopSpace.FreeAdjunction

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



def genLoopBasedCircleHomeomorph (x : X) :
    GenLoop N (basedCircleLoop x) (basedCircleConstant x) ≃ₜ
      basedCircleLoop (GenLoop.const : GenLoop N X x) where
  toFun p := ⟨genLoopFreeLoopHomeomorph x
    (genLoopBasedMap (basedCircleInclusion x) (basedCircleConstant x)
      (FreeLoop.constants x) rfl p), genLoopFreeLoopHomeomorph_inclusion_zero x p⟩
  invFun γ := ⟨⟨fun t => ⟨(genLoopFreeLoopHomeomorph x).symm γ.val t,
      congrArg (fun p : GenLoop N X x => p t) γ.property⟩,
      ((genLoopFreeLoopHomeomorph x).symm γ.val).val.continuous.subtype_mk _⟩,
    fun t ht => by
      apply Subtype.ext
      exact GenLoop.boundary ((genLoopFreeLoopHomeomorph x).symm γ.val) t ht⟩
  left_inv p := by ext t θ; rfl
  right_inv γ := by ext θ t; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (genLoopFreeLoopHomeomorph x).continuous.comp
    exact ((_root_.ContinuousMap.continuous_postcomp (basedCircleInclusion x)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply _root_.ContinuousMap.continuous_of_continuous_uncurry
    apply Continuous.subtype_mk
    change Continuous (fun z : basedCircleLoop (GenLoop.const : GenLoop N X x) ×
      (N → unitInterval) => (genLoopFreeLoopHomeomorph x).symm z.1.val |>.val z.2)
    exact continuous_eval.comp
      ((continuous_subtype_val.comp
        ((genLoopFreeLoopHomeomorph x).symm.continuous.comp
          (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph


theorem genLoopBasedCircleHomeomorph_apply (x : X)
    (p : GenLoop N (basedCircleLoop x) (basedCircleConstant x))
    (θ : loopCircle) (t : N → unitInterval) :
    (genLoopBasedCircleHomeomorph x p).val θ t = (p t).val θ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph_apply ``Submission.DifferentialGeometry.Topology.genLoopBasedCircleHomeomorph_apply

end DifferentialGeometry.Topology
