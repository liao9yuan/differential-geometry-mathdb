import Submission.DifferentialGeometry.Topology.Homotopy.CubePathExtension
import Submission.DifferentialGeometry.Topology.Homotopy.Map

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X}



theorem continuous_cubePathExtension_joint (n : ℕ) :
    Continuous (fun z : (Path x y × GenLoop (Fin (n + 1)) X x) ×
      (unitInterval × (Fin (n + 1) → unitInterval)) =>
        cubePathExtension n z.1.1 z.1.2 z.2) := by
  apply Continuous.if
  · intro z hz
    have heq := frontier_le_subset_eq
      ((continuous_cubeRadius n).comp (continuous_snd.comp continuous_snd))
      (continuous_const.sub
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).div_const 2)) hz
    exact cubePathExtension_interface n z.1.1 z.1.2 z.2 heq
  · exact continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_cubePrismRetract n).snd.comp continuous_snd))
  · exact (Path.continuous_uncurry_iff.mpr continuous_id).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_cubePrismRetract n).fst.comp continuous_snd))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_cubePathExtension_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_cubePathExtension_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_cubePathExtension_joint ``Submission.DifferentialGeometry.Topology.continuous_cubePathExtension_joint


theorem continuous_genLoopTransport (n : ℕ) :
    Continuous (fun z : Path x y × GenLoop (Fin (n + 1)) X x => genLoopTransport n z.1 z.2) := by
  apply Continuous.subtype_mk
  apply _root_.ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (Path x y × GenLoop (Fin (n + 1)) X x) ×
    (Fin (n + 1) → unitInterval) => cubePathExtension n z.1.1 z.1.2 (1, z.2))
  apply Continuous.if
  · intro z hz
    have heq := frontier_le_subset_eq ((continuous_cubeRadius n).comp continuous_snd)
      (continuous_const (y := (1 - (1 : ℝ) / 2))) hz
    exact cubePathExtension_interface n z.1.1 z.1.2 (1, z.2) heq
  · exact continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
        ((continuous_cubePrismRetract n).snd.comp (continuous_const.prodMk continuous_snd)))
  · exact (Path.continuous_uncurry_iff.mpr continuous_id).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_cubePrismRetract n).fst.comp (continuous_const.prodMk continuous_snd)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_genLoopTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_genLoopTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_genLoopTransport ``Submission.DifferentialGeometry.Topology.continuous_genLoopTransport


theorem genLoopTransport_homotopic (n : ℕ) (p : Path x y)
    {Γ Δ : GenLoop (Fin (n + 1)) X x} (h : GenLoop.Homotopic Γ Δ) :
    GenLoop.Homotopic (genLoopTransport n p Γ) (genLoopTransport n p Δ) := by
  apply (genLoop_homotopic_iff_joined _ _).mpr
  exact ((genLoop_homotopic_iff_joined Γ Δ).mp h).map
    ((continuous_genLoopTransport n).comp (continuous_const.prodMk continuous_id))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTransport_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTransport_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTransport_homotopic ``Submission.DifferentialGeometry.Topology.genLoopTransport_homotopic



theorem genLoopTransport_path_homotopic (n : ℕ) {p q : Path x y}
    (h : p.Homotopic q) (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic (genLoopTransport n p Γ) (genLoopTransport n q Γ) := by
  obtain ⟨H⟩ := h
  let P : Path p q :=
    ⟨⟨H.eval, Path.continuous_uncurry_iff.mp H.continuous⟩, H.eval_zero, H.eval_one⟩
  have hj : Joined p q := ⟨P⟩
  exact (genLoop_homotopic_iff_joined _ _).mpr
    (hj.map ((continuous_genLoopTransport n).comp (continuous_id.prodMk continuous_const)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTransport_path_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTransport_path_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTransport_path_homotopic ``Submission.DifferentialGeometry.Topology.genLoopTransport_path_homotopic


theorem genLoopTransport_natural (n : ℕ) (f : C(X, Y)) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) :
    genLoopTransport n (p.map f.continuous) (genLoopPostcompose f x Γ) =
      genLoopPostcompose f y (genLoopTransport n p Γ) := by
  ext v
  change cubePathExtension n (p.map f.continuous) (genLoopPostcompose f x Γ) (1, v) =
    f (cubePathExtension n p Γ (1, v))
  unfold cubePathExtension
  split_ifs <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTransport_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTransport_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTransport_natural ``Submission.DifferentialGeometry.Topology.genLoopTransport_natural

end DifferentialGeometry.Topology
