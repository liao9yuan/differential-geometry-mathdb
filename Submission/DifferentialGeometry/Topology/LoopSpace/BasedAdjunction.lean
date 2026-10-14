import Submission.DifferentialGeometry.Topology.Homotopy.PathModel
import Submission.DifferentialGeometry.Topology.Homotopy.BasedMap
import Submission.DifferentialGeometry.Topology.Homotopy.Adjunction
import Submission.DifferentialGeometry.Topology.Homotopy.Reindex
import Submission.DifferentialGeometry.Topology.LoopSpace.BasedNaturality
import Mathlib.Logic.Equiv.Fin.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q]


def basedCircleConstant (q : Q) : basedCircleLoop q := ⟨FreeLoop.constants q, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleConstant ``Submission.DifferentialGeometry.Topology.basedCircleConstant


def genLoopCircleHomeomorph (q : Q) : GenLoop (Fin 1) Q q ≃ₜ basedCircleLoop q :=
  (genLoopPathHomeomorph (Fin 1) q).trans (basedPathCircleHomeomorph q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCircleHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCircleHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCircleHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopCircleHomeomorph


theorem genLoopCircleHomeomorph_const (q : Q) :
    genLoopCircleHomeomorph q GenLoop.const = basedCircleConstant q := by
  change basedPathCircleHomeomorph q (genLoopPathHomeomorph (Fin 1) q GenLoop.const) = _
  rw [genLoopPathHomeomorph_const]
  apply Subtype.ext
  exact basedPathCircleHomeomorph_refl q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCircleHomeomorph_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCircleHomeomorph_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCircleHomeomorph_const ``Submission.DifferentialGeometry.Topology.genLoopCircleHomeomorph_const


theorem genLoopCircleHomeomorph_symm_constant (q : Q) :
    (genLoopCircleHomeomorph q).symm (basedCircleConstant q) = GenLoop.const := by
  rw [← genLoopCircleHomeomorph_const q]
  exact (genLoopCircleHomeomorph q).symm_apply_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCircleHomeomorph_symm_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCircleHomeomorph_symm_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCircleHomeomorph_symm_constant ``Submission.DifferentialGeometry.Topology.genLoopCircleHomeomorph_symm_constant



def basedCircleHomotopyGroupMulEquiv (n : ℕ) (q : Q) :
    HomotopyGroup (Fin (n + 1)) (basedCircleLoop q) (basedCircleConstant q) ≃*
      HomotopyGroup (Fin (n + 1) ⊕ Fin 1) Q q :=
  (homotopyGroupBasedHomeomorphMulEquiv (N := Fin (n + 1))
    (genLoopCircleHomeomorph q).symm (basedCircleConstant q) GenLoop.const
      (genLoopCircleHomeomorph_symm_constant q)).trans
    (homotopyGroupIteratedLoopMulEquiv (K := Fin (n + 1)) (N := Fin 1) q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv ``Submission.DifferentialGeometry.Topology.basedCircleHomotopyGroupMulEquiv



def basedCirclePiTwoMulEquiv (q : Q) :
    HomotopyGroup (Fin 2) (basedCircleLoop q) (basedCircleConstant q) ≃*
      HomotopyGroup (Fin 3) Q q :=
  (basedCircleHomotopyGroupMulEquiv 1 q).trans
    (homotopyGroupReindexMulEquiv (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3) q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv ``Submission.DifferentialGeometry.Topology.basedCirclePiTwoMulEquiv


def basedCirclePiOneMulEquiv (q : Q) :
    HomotopyGroup (Fin 1) (basedCircleLoop q) (basedCircleConstant q) ≃*
      HomotopyGroup (Fin 2) Q q :=
  (basedCircleHomotopyGroupMulEquiv 0 q).trans
    (homotopyGroupReindexMulEquiv (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCirclePiOneMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCirclePiOneMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCirclePiOneMulEquiv ``Submission.DifferentialGeometry.Topology.basedCirclePiOneMulEquiv

end DifferentialGeometry.Topology
