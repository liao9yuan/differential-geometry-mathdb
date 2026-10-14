import Submission.DifferentialGeometry.Topology.Homotopy.Adjunction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N]



def genLoopFundamentalGroupMulEquiv (x : X) :
    FundamentalGroup (GenLoop N X x) GenLoop.const ≃* HomotopyGroup (Fin 1 ⊕ N) X x :=
  (HomotopyGroup.pi1MulEquivFundamentalGroup (X := GenLoop N X x) (x := GenLoop.const)).symm.trans
    (homotopyGroupIteratedLoopMulEquiv x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopFundamentalGroupMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopFundamentalGroupMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopFundamentalGroupMulEquiv ``Submission.DifferentialGeometry.Topology.genLoopFundamentalGroupMulEquiv

omit [DecidableEq N] in
theorem genLoopFundamentalGroup_mul_comm [Nonempty N] (x : X)
    (a b : FundamentalGroup (GenLoop N X x) GenLoop.const) : a * b = b * a := by
  classical
  let : Nontrivial (Fin 1 ⊕ N) :=
    ⟨⟨Sum.inl 0, Sum.inr (Classical.arbitrary N), by intro h; cases h⟩⟩
  apply (genLoopFundamentalGroupMulEquiv x).injective
  simp only [map_mul]
  exact @mul_comm (HomotopyGroup (Fin 1 ⊕ N) X x) _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopFundamentalGroup_mul_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopFundamentalGroup_mul_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopFundamentalGroup_mul_comm ``Submission.DifferentialGeometry.Topology.genLoopFundamentalGroup_mul_comm

end DifferentialGeometry.Topology
