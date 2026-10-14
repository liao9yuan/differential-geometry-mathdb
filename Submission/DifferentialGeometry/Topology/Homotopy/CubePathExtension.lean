import Submission.DifferentialGeometry.Topology.Homotopy.CubePrismImage
import Submission.DifferentialGeometry.Topology.Homotopy.LoopTopology
import Mathlib.Topology.Piecewise

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



def cubePathExtension (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x)
    (z : unitInterval × (Fin (n + 1) → unitInterval)) : X :=
  if cubeRadius n z.2 ≤ 1 - z.1.val / 2 then Γ (cubePrismRetract n z).2
  else p (cubePrismRetract n z).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathExtension ``Submission.DifferentialGeometry.Topology.cubePathExtension


theorem cubePathExtension_interface (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x)
    (z : unitInterval × (Fin (n + 1) → unitInterval))
    (hz : cubeRadius n z.2 = 1 - z.1.val / 2) :
    Γ (cubePrismRetract n z).2 = p (cubePrismRetract n z).1 := by
  rw [GenLoop.boundary Γ _ (cubePrismRetract_position_boundary n z hz.ge),
    cubePrismRetract_time_zero n z hz.le, p.source]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathExtension_interface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathExtension_interface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathExtension_interface ``Submission.DifferentialGeometry.Topology.cubePathExtension_interface



theorem continuous_cubePathExtension (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) : Continuous (cubePathExtension n p Γ) := by
  apply Continuous.if
  · intro z hz
    have heq := frontier_le_subset_eq
      ((continuous_cubeRadius n).comp continuous_snd)
      (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)) hz
    exact cubePathExtension_interface n p Γ z heq
  · exact Γ.val.continuous.comp (continuous_cubePrismRetract n).snd
  · exact p.continuous.comp (continuous_cubePrismRetract n).fst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_cubePathExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_cubePathExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_cubePathExtension ``Submission.DifferentialGeometry.Topology.continuous_cubePathExtension


theorem cubePathExtension_zero (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x)
    (v : Fin (n + 1) → unitInterval) : cubePathExtension n p Γ (0, v) = Γ v := by
  have hc : cubeRadius n v ≤ 1 - (0 : ℝ) / 2 := by
    simpa only [zero_div, sub_zero] using cubeRadius_le_one n v
  change (if cubeRadius n v ≤ 1 - (0 : ℝ) / 2 then Γ (cubePrismRetract n (0, v)).2
    else p (cubePrismRetract n (0, v)).1) = Γ v
  rw [if_pos hc, cubePrismRetract_bottom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathExtension_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathExtension_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathExtension_zero ``Submission.DifferentialGeometry.Topology.cubePathExtension_zero



theorem cubePathExtension_boundary (n : ℕ) (p : Path x y)
    (Γ : GenLoop (Fin (n + 1)) X x) (t : unitInterval)
    (v : Fin (n + 1) → unitInterval) (hv : v ∈ Cube.boundary (Fin (n + 1))) :
    cubePathExtension n p Γ (t, v) = p t := by
  unfold cubePathExtension
  rw [cubePrismRetract_side n t v hv]
  split_ifs with h
  · have hrad := (cubeRadius_eq_one_iff n v).mpr hv
    have ht : t = 0 := Subtype.ext (show t.val = (0 : ℝ) by
      have ht0 := t.property.1
      change cubeRadius n v ≤ 1 - t.val / 2 at h
      rw [hrad] at h
      linarith)
    rw [ht, p.source, GenLoop.boundary Γ v hv]
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubePathExtension_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubePathExtension_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubePathExtension_boundary ``Submission.DifferentialGeometry.Topology.cubePathExtension_boundary


def genLoopTransport (n : ℕ) (p : Path x y) (Γ : GenLoop (Fin (n + 1)) X x) :
    GenLoop (Fin (n + 1)) X y :=
  ⟨⟨fun v => cubePathExtension n p Γ (1, v),
    (continuous_cubePathExtension n p Γ).comp (continuous_const.prodMk continuous_id)⟩,
    fun v hv => (cubePathExtension_boundary n p Γ 1 v hv).trans p.target⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopTransport ``Submission.DifferentialGeometry.Topology.genLoopTransport

end DifferentialGeometry.Topology
