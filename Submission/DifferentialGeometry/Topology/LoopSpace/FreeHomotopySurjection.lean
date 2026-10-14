import Submission.DifferentialGeometry.Topology.LoopSpace.Rotation
import Mathlib.Topology.Connected.PathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y : X}



theorem pathToCircle_conjugate_homotopic (p : Path x y) (q : Path y y) :
    (pathToCircle (p.trans (q.trans p.symm))).Homotopic (pathToCircle q) := by
  apply (pathToCircle_trans_homotopic_comm p (q.trans p.symm)).trans
  apply pathToCircle_homotopic
  exact (Path.Homotopic.trans_assoc q p.symm p).trans
    (((Path.Homotopic.refl q).hcomp (Path.Homotopic.symm_trans p)).trans
      (Path.Homotopic.trans_refl q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathToCircle_conjugate_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathToCircle_conjugate_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathToCircle_conjugate_homotopic ``Submission.DifferentialGeometry.Topology.pathToCircle_conjugate_homotopic



theorem exists_basedCircle_free_homotopic [PathConnectedSpace X] (x : X) (γ : freeLoop X) :
    ∃ δ : basedCircleLoop x, δ.val.Homotopic γ := by
  let y := γ 0
  let q := circleToPath (⟨γ, rfl⟩ : basedCircleLoop y)
  let p := PathConnectedSpace.somePath x y
  refine ⟨basedPathCircleHomeomorph x (p.trans (q.trans p.symm)), ?_⟩
  have heq : pathToCircle q = γ := by
    ext θ
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    exact pathToCircle_coe q t
  exact (pathToCircle_conjugate_homotopic p q).trans (heq ▸ ContinuousMap.Homotopic.refl _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_basedCircle_free_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_basedCircle_free_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_basedCircle_free_homotopic ``Submission.DifferentialGeometry.Topology.exists_basedCircle_free_homotopic

end DifferentialGeometry.Topology
