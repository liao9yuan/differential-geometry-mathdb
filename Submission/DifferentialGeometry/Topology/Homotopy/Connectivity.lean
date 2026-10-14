import Submission.DifferentialGeometry.Topology.Homotopy.Adjunction
import Submission.DifferentialGeometry.Topology.Homotopy.Reindex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

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



theorem genLoop_pathConnected_of_subsingleton (x : X)
    [Subsingleton (HomotopyGroup N X x)] : PathConnectedSpace (GenLoop N X x) where
  nonempty := ⟨GenLoop.const⟩
  joined p q := by
    have heq := @Subsingleton.elim (HomotopyGroup N X x) inferInstance ⟦p⟧ ⟦q⟧
    exact (genLoop_homotopic_iff_joined p q).mp (Quotient.exact heq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoop_pathConnected_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoop_pathConnected_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoop_pathConnected_of_subsingleton ``Submission.DifferentialGeometry.Topology.genLoop_pathConnected_of_subsingleton



theorem simplyConnected_of_subsingleton_piOne [PathConnectedSpace X] (x : X)
    [Subsingleton (HomotopyGroup (Fin 1) X x)] : SimplyConnectedSpace X := by
  let : Subsingleton (FundamentalGroup X x) :=
    (HomotopyGroup.pi1EquivFundamentalGroup (x := x)).surjective.subsingleton
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun y p => ?_⟩
  let : Subsingleton (FundamentalGroup X y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (PathConnectedSpace.somePath x y)).surjective.subsingleton
  have heq := @Subsingleton.elim (FundamentalGroup X y) inferInstance
    (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk (Path.refl y))
  exact Path.Homotopic.Quotient.eq.mp heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnected_of_subsingleton_piOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnected_of_subsingleton_piOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnected_of_subsingleton_piOne ``Submission.DifferentialGeometry.Topology.simplyConnected_of_subsingleton_piOne



theorem genLoop_simplyConnected_of_subsingleton (x : X)
    [Subsingleton (HomotopyGroup N X x)]
    [Subsingleton (HomotopyGroup (Fin 1 ⊕ N) X x)] :
    SimplyConnectedSpace (GenLoop N X x) := by
  let := genLoop_pathConnected_of_subsingleton (N := N) x
  let : Subsingleton (HomotopyGroup (Fin 1) (GenLoop N X x) GenLoop.const) :=
    (homotopyGroupIteratedLoopEquiv (K := Fin 1) (N := N) x).injective.subsingleton
  exact simplyConnected_of_subsingleton_piOne GenLoop.const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoop_simplyConnected_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoop_simplyConnected_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoop_simplyConnected_of_subsingleton ``Submission.DifferentialGeometry.Topology.genLoop_simplyConnected_of_subsingleton

end DifferentialGeometry.Topology
