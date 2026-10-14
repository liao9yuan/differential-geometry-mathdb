import Submission.DifferentialGeometry.Topology.Homotopy.LoopTopology
import Submission.DifferentialGeometry.Topology.Homotopy.Map

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {K N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


theorem genLoop_uncurry_apply (x : X) (p : GenLoop K (GenLoop N X x) GenLoop.const)
    (t : K ⊕ N → unitInterval) :
    GenLoop.genLoopGenLoopEquiv x p t = p (t ∘ Sum.inl) (t ∘ Sum.inr) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoop_uncurry_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoop_uncurry_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoop_uncurry_apply ``Submission.DifferentialGeometry.Topology.genLoop_uncurry_apply


theorem genLoop_uncurry_transAt [DecidableEq K] [DecidableEq N]
    (x : X) (i : K) (p q : GenLoop K (GenLoop N X x) GenLoop.const) :
    GenLoop.genLoopGenLoopEquiv x (GenLoop.transAt i p q) =
      GenLoop.transAt (Sum.inl i) (GenLoop.genLoopGenLoopEquiv x p)
        (GenLoop.genLoopGenLoopEquiv x q) := by
  ext t
  simp only [genLoop_uncurry_apply, GenLoop.transAt, GenLoop.coe_copy, Function.comp_apply]
  split_ifs <;> congr 2 <;> funext j <;> simp [Function.update_apply, Function.comp_def]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoop_uncurry_transAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoop_uncurry_transAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoop_uncurry_transAt ``Submission.DifferentialGeometry.Topology.genLoop_uncurry_transAt



def homotopyGroupIteratedLoopMulEquiv [DecidableEq K] [DecidableEq N] [Nonempty K] (x : X) :
    HomotopyGroup K (GenLoop N X x) GenLoop.const ≃* HomotopyGroup (K ⊕ N) X x where
  toEquiv := homotopyGroupIteratedLoopEquiv x
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        let i : K := Classical.arbitrary K
        have hmul := congrArg (homotopyGroupIteratedLoopEquiv (K := K) (N := N) x)
          (HomotopyGroup.mul_spec (i := i) (p := p) (q := q))
        refine hmul.trans ?_
        have heq := congrArg
          (fun r : GenLoop (K ⊕ N) X x => (⟦r⟧ : HomotopyGroup (K ⊕ N) X x))
          (genLoop_uncurry_transAt x i q p)
        exact heq.trans (HomotopyGroup.mul_spec (i := Sum.inl i)
          (p := GenLoop.genLoopGenLoopEquiv x p) (q := GenLoop.genLoopGenLoopEquiv x q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupIteratedLoopMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupIteratedLoopMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupIteratedLoopMulEquiv ``Submission.DifferentialGeometry.Topology.homotopyGroupIteratedLoopMulEquiv

end DifferentialGeometry.Topology
