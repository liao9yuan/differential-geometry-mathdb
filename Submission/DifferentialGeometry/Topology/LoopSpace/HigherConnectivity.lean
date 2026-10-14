import Submission.DifferentialGeometry.Topology.Homotopy.Connectivity
import Submission.DifferentialGeometry.Topology.LoopSpace.FreeAdjunction
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SimplyConnectedTarget

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]


theorem piOne_subsingleton_of_simplyConnected (x : X) :
    Subsingleton (HomotopyGroup (Fin 1) X x) :=
  (HomotopyGroup.pi1EquivFundamentalGroup (x := x)).injective.subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piOne_subsingleton_of_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piOne_subsingleton_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piOne_subsingleton_of_simplyConnected ``Submission.DifferentialGeometry.Topology.piOne_subsingleton_of_simplyConnected


theorem basedCircle_pathConnected (x : X) : PathConnectedSpace (basedCircleLoop x) := by
  let := piOne_subsingleton_of_simplyConnected x
  let := genLoop_pathConnected_of_subsingleton (N := Fin 1) x
  exact (genLoopCircleHomeomorph x).surjective.pathConnectedSpace
    (genLoopCircleHomeomorph x).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircle_pathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircle_pathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircle_pathConnected ``Submission.DifferentialGeometry.Topology.basedCircle_pathConnected


theorem basedCircle_simplyConnected_of_piTwo (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    SimplyConnectedSpace (basedCircleLoop x) := by
  let := basedCircle_pathConnected x
  let : Subsingleton
      (HomotopyGroup (Fin 1) (basedCircleLoop x) (basedCircleConstant x)) :=
    (basedCirclePiOneMulEquiv x).injective.subsingleton
  exact simplyConnected_of_subsingleton_piOne (basedCircleConstant x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircle_simplyConnected_of_piTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircle_simplyConnected_of_piTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircle_simplyConnected_of_piTwo ``Submission.DifferentialGeometry.Topology.basedCircle_simplyConnected_of_piTwo





theorem freeLoop_simplyConnected_of_piTwo (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] : SimplyConnectedSpace (freeLoop X) := by
  let := piOne_subsingleton_of_simplyConnected x
  let : Subsingleton (HomotopyGroup (Fin 1 ⊕ Fin 1) X x) :=
    (homotopyGroupReindexMulEquiv (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) x).injective.subsingleton
  let := genLoop_simplyConnected_of_subsingleton (N := Fin 1) x
  have hs : Subsingleton (HomotopyGroup (Fin 1) (freeLoop X) (FreeLoop.constants x)) := by
    constructor
    intro a b
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        apply Quotient.sound
        apply (genLoopFreeLoopHomeomorph_homotopic_iff x p q).mp
        exact (FreeLoop.homotopic_iff_joined _ _).mpr (joined_freeLoops _ _)
  exact simplyConnected_of_subsingleton_piOne (FreeLoop.constants x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeLoop_simplyConnected_of_piTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeLoop_simplyConnected_of_piTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeLoop_simplyConnected_of_piTwo ``Submission.DifferentialGeometry.Topology.freeLoop_simplyConnected_of_piTwo



theorem contractibleLoop_simplyConnected_of_piTwo (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    SimplyConnectedSpace (contractibleLoop X) := by
  let := freeLoop_simplyConnected_of_piTwo x
  exact (contractibleLoopHomeomorphFreeLoop X).toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.contractibleLoop_simplyConnected_of_piTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.contractibleLoop_simplyConnected_of_piTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.contractibleLoop_simplyConnected_of_piTwo ``Submission.DifferentialGeometry.Topology.contractibleLoop_simplyConnected_of_piTwo

end DifferentialGeometry.Topology
