import Submission.DifferentialGeometry.Topology.Homotopy.ExtensionUniqueness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x y z : X}



def cubePathHomotopy (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x) :
    Γ.val.Homotopy (genLoopTransport n p Γ).val where
  toContinuousMap := ⟨cubePathExtension n p Γ, continuous_cubePathExtension n p Γ⟩
  map_zero_left := cubePathExtension_zero n p Γ
  map_one_left _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathHomotopy ``Submission.DifferentialGeometry.Topology.cubePathHomotopy


theorem cubePathHomotopy_boundary (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) (t : unitInterval)
    (v : Fin (n + 1) → unitInterval) (hv : v ∈ Cube.boundary (Fin (n + 1))) :
    cubePathHomotopy n p Γ (t, v) = p t := cubePathExtension_boundary n p Γ t v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathHomotopy_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathHomotopy_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathHomotopy_boundary ``Submission.DifferentialGeometry.Topology.cubePathHomotopy_boundary



theorem genLoopTransport_trans_homotopic (n : ℕ) (p : Path x y) (q : Path y z)
    (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic (genLoopTransport n q (genLoopTransport n p Γ))
      (genLoopTransport n (p.trans q) Γ) := by
  let H := (cubePathHomotopy n p Γ).trans (cubePathHomotopy n q (genLoopTransport n p Γ))
  apply genLoopTransport_extension_unique n (p.trans q) Γ _ H.toContinuousMap
    H.apply_zero H.apply_one
  intro t v hv
  change H (t, v) = (p.trans q) t
  simp only [H, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact cubePathHomotopy_boundary n p Γ _ v hv
  · exact cubePathHomotopy_boundary n q (genLoopTransport n p Γ) _ v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTransport_trans_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTransport_trans_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTransport_trans_homotopic ``Submission.DifferentialGeometry.Topology.genLoopTransport_trans_homotopic

end DifferentialGeometry.Topology
