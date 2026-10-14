import Submission.DifferentialGeometry.Topology.Homotopy.CubePathExtension
import Submission.DifferentialGeometry.Topology.Homotopy.CubePrismDeformation

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



theorem cubePathExtension_retract_eq (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x)
    (F : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (h0 : ∀ v, F (0, v) = Γ v)
    (hb : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t)
    (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    F (cubePrismRetract n z) = cubePathExtension n p Γ z := by
  unfold cubePathExtension
  split_ifs with h
  · have ht := cubePrismRetract_time_zero n z h
    have heq : cubePrismRetract n z = (0, (cubePrismRetract n z).2) := Prod.ext ht rfl
    rw [heq]
    exact h0 _
  · exact hb _ _ (cubePrismRetract_position_boundary n z (le_of_not_ge h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathExtension_retract_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathExtension_retract_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathExtension_retract_eq ``Submission.DifferentialGeometry.Topology.cubePathExtension_retract_eq



theorem genLoopTransport_extension_unique (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) (Δ : GenLoop (Fin (n + 1)) X y)
    (F : C(unitInterval × (Fin (n + 1) → unitInterval), X))
    (h0 : ∀ v, F (0, v) = Γ v) (h1 : ∀ v, F (1, v) = Δ v)
    (hb : ∀ t v, v ∈ Cube.boundary (Fin (n + 1)) → F (t, v) = p t) :
    GenLoop.Homotopic Δ (genLoopTransport n p Γ) := by
  refine ⟨{
    toFun := fun z => F (cubePrismDeformation n (z.1, (1, z.2)))
    continuous_toFun := F.continuous.comp ((cubePrismDeformation n).continuous.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro v
    rw [(cubePrismDeformation n).apply_zero]
    exact h1 v
  · intro v
    rw [(cubePrismDeformation n).apply_one]
    exact cubePathExtension_retract_eq n p Γ F h0 hb (1, v)
  · intro s v hv
    change F (cubePrismDeformation n (s, (1, v))) = Δ v
    rw [(cubePrismDeformation n).eq_fst s (show (1, v) ∈
      {z : unitInterval × (Fin (n + 1) → unitInterval) |
        z.1 = 0 ∨ z.2 ∈ Cube.boundary (Fin (n + 1))} from Or.inr hv)]
    exact h1 v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTransport_extension_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTransport_extension_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTransport_extension_unique ``Submission.DifferentialGeometry.Topology.genLoopTransport_extension_unique



theorem genLoopTransport_refl_homotopic (n : ℕ) (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic (genLoopTransport n (Path.refl x) Γ) Γ := by
  exact (genLoopTransport_extension_unique n (Path.refl x) Γ Γ
    (Γ.val.comp ContinuousMap.snd) (fun _ => rfl) (fun _ => rfl)
      (fun _ v hv => GenLoop.boundary Γ v hv)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTransport_refl_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTransport_refl_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTransport_refl_homotopic ``Submission.DifferentialGeometry.Topology.genLoopTransport_refl_homotopic

end DifferentialGeometry.Topology
