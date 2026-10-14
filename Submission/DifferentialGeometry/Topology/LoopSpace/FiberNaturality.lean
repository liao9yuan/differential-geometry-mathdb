import Submission.DifferentialGeometry.Topology.LoopSpace.FiberInclusion
import Submission.DifferentialGeometry.Topology.LoopSpace.BasedAdjunctionNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]



theorem basedCircleInclusionHom_natural [DecidableEq N] [Nonempty N]
    (f : C(P, Q)) (p : P)
    (a : HomotopyGroup N (basedCircleLoop p) (basedCircleConstant p)) :
    basedCircleInclusionHom (f p)
      (homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p) a) =
      homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
        (FreeLoop.constants (f p)) rfl (basedCircleInclusionHom p a) := by
  induction a using Quotient.inductionOn with
  | h Γ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.basedCircleInclusionHom_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.basedCircleInclusionHom_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.basedCircleInclusionHom_natural ``Submission.DifferentialGeometry.Topology.basedCircleInclusionHom_natural



theorem piThreeFreeLoopPiTwoMulEquiv_natural (f : C(P, Q)) (p : P)
    [Subsingleton (HomotopyGroup (Fin 2) P p)]
    [Subsingleton (HomotopyGroup (Fin 2) Q (f p))]
    (a : HomotopyGroup (Fin 3) P p) :
    piThreeFreeLoopPiTwoMulEquiv (f p) (homotopyGroupMap f p a) =
      homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
        (FreeLoop.constants (f p)) rfl (piThreeFreeLoopPiTwoMulEquiv p a) := by
  have hinv : (basedCirclePiTwoMulEquiv (f p)).symm (homotopyGroupMap f p a) =
      homotopyGroupBasedMap (basedCirclePostcompose f p) (basedCircleConstant p)
        (basedCircleConstant (f p)) (basedCirclePostcompose_constant f p)
          ((basedCirclePiTwoMulEquiv p).symm a) := by
    apply (basedCirclePiTwoMulEquiv (f p)).injective
    rw [MulEquiv.apply_symm_apply, basedCirclePiTwoMulEquiv_natural, MulEquiv.apply_symm_apply]
  change basedCircleInclusionHom (f p)
      ((basedCirclePiTwoMulEquiv (f p)).symm (homotopyGroupMap f p a)) =
    homotopyGroupBasedMap (FreeLoop.postcompose f) (FreeLoop.constants p)
      (FreeLoop.constants (f p)) rfl
        (basedCircleInclusionHom p ((basedCirclePiTwoMulEquiv p).symm a))
  rw [hinv]
  exact basedCircleInclusionHom_natural f p _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv_natural ``Submission.DifferentialGeometry.Topology.piThreeFreeLoopPiTwoMulEquiv_natural

end DifferentialGeometry.Topology
