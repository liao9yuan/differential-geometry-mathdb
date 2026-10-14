import Submission.DifferentialGeometry.Topology.LoopSpace.BasedSwap
import Submission.DifferentialGeometry.Topology.LoopSpace.FreeHomotopyInjection
import Submission.DifferentialGeometry.Topology.LoopSpace.FreeHomotopySurjection
import Submission.DifferentialGeometry.Topology.Homotopy.FundamentalLoop
import Submission.DifferentialGeometry.Topology.Homotopy.Connectivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N] [Nonempty N]


def basedCircleInclusionHom (x : X) :
    HomotopyGroup N (basedCircleLoop x) (basedCircleConstant x) →*
      HomotopyGroup N (freeLoop X) (FreeLoop.constants x) :=
  homotopyGroupBasedMapHom (basedCircleInclusion x) (basedCircleConstant x)
    (FreeLoop.constants x) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleInclusionHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleInclusionHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleInclusionHom ``Submission.DifferentialGeometry.Topology.basedCircleInclusionHom


theorem basedCircleInclusionHom_injective (x : X) :
    Injective (basedCircleInclusionHom (N := N) x) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      intro h
      apply Quotient.sound
      have hfree := (genLoopFreeLoopHomeomorph_homotopic_iff x _ _).mpr (Quotient.exact h)
      have hj := basedCircle_joined_of_free (genLoopFundamentalGroup_mul_comm (N := N) x)
        (genLoopBasedCircleHomeomorph x p) (genLoopBasedCircleHomeomorph x q) hfree
      apply (genLoop_homotopic_iff_joined p q).mpr
      simpa only [Homeomorph.symm_apply_apply] using
        hj.map (genLoopBasedCircleHomeomorph x).symm.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleInclusionHom_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleInclusionHom_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleInclusionHom_injective ``Submission.DifferentialGeometry.Topology.basedCircleInclusionHom_injective



theorem basedCircleInclusionHom_surjective (x : X)
    [Subsingleton (HomotopyGroup N X x)] :
    Surjective (basedCircleInclusionHom (N := N) x) := by
  let := genLoop_pathConnected_of_subsingleton (N := N) x
  intro b
  induction b using Quotient.inductionOn with
  | h p =>
    obtain ⟨δ, hδ⟩ := exists_basedCircle_free_homotopic
      (GenLoop.const : GenLoop N X x) (genLoopFreeLoopHomeomorph x p)
    let a := (genLoopBasedCircleHomeomorph x).symm δ
    refine ⟨⟦a⟧, Quotient.sound ?_⟩
    apply (genLoopFreeLoopHomeomorph_homotopic_iff x _ p).mp
    change (genLoopBasedCircleHomeomorph x a).val.Homotopic (genLoopFreeLoopHomeomorph x p)
    simpa only [a, Homeomorph.apply_symm_apply] using hδ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleInclusionHom_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleInclusionHom_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleInclusionHom_surjective ``Submission.DifferentialGeometry.Topology.basedCircleInclusionHom_surjective



def basedCircleInclusionMulEquiv (x : X) [Subsingleton (HomotopyGroup N X x)] :
    HomotopyGroup N (basedCircleLoop x) (basedCircleConstant x) ≃*
      HomotopyGroup N (freeLoop X) (FreeLoop.constants x) :=
  MulEquiv.ofBijective (basedCircleInclusionHom x)
    ⟨basedCircleInclusionHom_injective x, basedCircleInclusionHom_surjective x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleInclusionMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleInclusionMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleInclusionMulEquiv ``Submission.DifferentialGeometry.Topology.basedCircleInclusionMulEquiv




def piThreeFreeLoopPiTwoMulEquiv (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    HomotopyGroup (Fin 3) X x ≃*
      HomotopyGroup (Fin 2) (freeLoop X) (FreeLoop.constants x) :=
  (basedCirclePiTwoMulEquiv x).symm.trans (basedCircleInclusionMulEquiv x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv ``Submission.DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv

end DifferentialGeometry.Topology
