import Submission.DifferentialGeometry.Topology.LoopSpace.FiberNaturality
import Submission.DifferentialGeometry.Topology.LoopSpace.HigherConnectivity
import Submission.DifferentialGeometry.Topology.LoopSpace.Family
import Submission.DifferentialGeometry.Topology.Homotopy.SphereNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [SimplyConnectedSpace P] [SimplyConnectedSpace Q]



def freeLoopContractiblePiTwoMulEquiv (q : Q) :
    HomotopyGroup (Fin 2) (freeLoop Q) (FreeLoop.constants q) ≃*
      HomotopyGroup (Fin 2) (contractibleLoop Q) (ContractibleLoop.constants q) :=
  homotopyGroupBasedHomeomorphMulEquiv (contractibleLoopHomeomorphFreeLoop Q).symm
    (FreeLoop.constants q) (ContractibleLoop.constants q) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv ``Submission.DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv



def piThreeContractibleLoopPiTwoMulEquiv (q : Q)
    [Subsingleton (HomotopyGroup (Fin 2) Q q)] :
    HomotopyGroup (Fin 3) Q q ≃*
      HomotopyGroup (Fin 2) (contractibleLoop Q) (ContractibleLoop.constants q) :=
  (piThreeFreeLoopPiTwoMulEquiv q).trans (freeLoopContractiblePiTwoMulEquiv q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv ``Submission.DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv



def piThreeLoopFamilyEquiv (q : Q) [Subsingleton (HomotopyGroup (Fin 2) Q q)] :
    HomotopyGroup (Fin 3) Q q ≃ loopFamilyClass Q := by
  let := contractibleLoop_simplyConnected_of_piTwo q
  exact (piThreeContractibleLoopPiTwoMulEquiv q).toEquiv.trans
    (homotopyGroupFreeSphereEquiv 1 (ContractibleLoop.constants q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeLoopFamilyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv ``Submission.DifferentialGeometry.Topology.piThreeLoopFamilyEquiv


theorem piThreeLoopFamilyEquiv_one (q : Q) [Subsingleton (HomotopyGroup (Fin 2) Q q)] :
    piThreeLoopFamilyEquiv q 1 = LoopFamily.nullClass q := by
  change homotopyGroupToFreeSphere 1 (ContractibleLoop.constants q)
    (piThreeContractibleLoopPiTwoMulEquiv q 1) = _
  rw [map_one]
  exact homotopyGroupToFreeSphere_one 1 (ContractibleLoop.constants q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_one ``Submission.DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_one


theorem piThreeLoopFamilyEquiv_ne_null_iff (q : Q)
    [Subsingleton (HomotopyGroup (Fin 2) Q q)] (a : HomotopyGroup (Fin 3) Q q) :
    piThreeLoopFamilyEquiv q a ≠ LoopFamily.nullClass q ↔ a ≠ 1 := by
  rw [← piThreeLoopFamilyEquiv_one q]
  exact not_congr (piThreeLoopFamilyEquiv q).injective.eq_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_ne_null_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_ne_null_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_ne_null_iff ``Submission.DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_ne_null_iff


theorem freeLoopContractiblePiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    (a : HomotopyGroup (Fin 2) (freeLoop P) (FreeLoop.constants p)) :
    freeLoopContractiblePiTwoMulEquiv (f p)
      (homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
        (FreeLoop.constants (f p)) rfl a) =
      homotopyGroupBasedMap (ContractibleLoop.postcompose f) (ContractibleLoop.constants p)
        (ContractibleLoop.constants (f p)) rfl (freeLoopContractiblePiTwoMulEquiv p a) := by
  induction a using Quotient.inductionOn with
  | h Γ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv_natural ``Submission.DifferentialGeometry.Topology.freeLoopContractiblePiTwoMulEquiv_natural


theorem piThreeContractibleLoopPiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    [Subsingleton (HomotopyGroup (Fin 2) P p)]
    [Subsingleton (HomotopyGroup (Fin 2) Q (f p))] (a : HomotopyGroup (Fin 3) P p) :
    piThreeContractibleLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a) =
      homotopyGroupBasedMap (ContractibleLoop.postcompose f) (ContractibleLoop.constants p)
        (ContractibleLoop.constants (f p)) rfl (piThreeContractibleLoopPiTwoMulEquiv p a) := by
  change freeLoopContractiblePiTwoMulEquiv (f p)
      (piThreeFreeLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a)) = _
  rw [piThreeFreeLoopPiTwoMulEquiv_natural, freeLoopContractiblePiTwoMulEquiv_natural]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv_natural ``Submission.DifferentialGeometry.Topology.piThreeContractibleLoopPiTwoMulEquiv_natural



theorem piThreeLoopFamilyEquiv_natural (f : C(P, Q)) (p : P)
    [Subsingleton (HomotopyGroup (Fin 2) P p)]
    [Subsingleton (HomotopyGroup (Fin 2) Q (f p))] (a : HomotopyGroup (Fin 3) P p) :
    piThreeLoopFamilyEquiv (f p) (homotopyGroupMap f p a) =
      LoopFamily.postcompose f (piThreeLoopFamilyEquiv p a) := by
  change homotopyGroupToFreeSphere 1 (ContractibleLoop.constants (f p))
      (piThreeContractibleLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a)) = _
  rw [piThreeContractibleLoopPiTwoMulEquiv_natural]
  exact homotopyGroupToFreeSphere_natural 1 (ContractibleLoop.postcompose f)
    (ContractibleLoop.constants p) (ContractibleLoop.constants (f p)) rfl
      (piThreeContractibleLoopPiTwoMulEquiv p a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_natural ``Submission.DifferentialGeometry.Topology.piThreeLoopFamilyEquiv_natural

end DifferentialGeometry.Topology
