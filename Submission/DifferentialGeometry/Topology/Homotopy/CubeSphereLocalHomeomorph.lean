import Submission.DifferentialGeometry.Topology.Homotopy.CubeSphereProjection
import Submission.DifferentialGeometry.Topology.Homotopy.OpenCollapseLocalHomeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

universe u

namespace DifferentialGeometry.Topology

def cubeSphereProjectionOpenPartialHomeomorph (n : ℕ) :
    OpenPartialHomeomorph (Fin (n + 1) → unitInterval)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  (openCollapseOpenPartialHomeomorph (cubeInterior (Fin (n + 1))) (isOpen_cubeInterior _)).transHomeomorph
    (cubeInteriorSphereHomeomorph n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph ``Submission.DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph

theorem cubeSphereProjectionOpenPartialHomeomorph_apply (n : ℕ) (x : Fin (n + 1) → unitInterval) :
    cubeSphereProjectionOpenPartialHomeomorph n x = cubeSphereProjection n x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_apply ``Submission.DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_apply

theorem cubeSphereProjectionOpenPartialHomeomorph_source (n : ℕ) :
    (cubeSphereProjectionOpenPartialHomeomorph n).source = cubeInterior (Fin (n + 1)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_source ``Submission.DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_source

theorem cubeSphereProjection_eq_of_mem (n : ℕ) {x y : Fin (n + 1) → unitInterval}
    (hx : x ∈ cubeInterior (Fin (n + 1)))
    (h : cubeSphereProjection n y = cubeSphereProjection n x) : y = x :=
  openCollapse_eq_of_mem hx ((cubeInteriorSphereHomeomorph n).injective h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjection_eq_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjection_eq_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjection_eq_of_mem ``Submission.DifferentialGeometry.Topology.cubeSphereProjection_eq_of_mem

theorem cubeSphereProjectionOpenPartialHomeomorph_target (n : ℕ) :
    (cubeSphereProjectionOpenPartialHomeomorph n).target = {cubeSphereBasepoint n}ᶜ := by
  change (cubeInteriorSphereHomeomorph n).symm ⁻¹'
    (openCollapseOpenPartialHomeomorph (cubeInterior (Fin (n + 1))) (isOpen_cubeInterior _)).target = _
  rw [openCollapseOpenPartialHomeomorph_target]
  ext z
  change (cubeInteriorSphereHomeomorph n).symm z ≠ OnePoint.infty ↔ z ≠ cubeSphereBasepoint n
  exact not_congr (Homeomorph.symm_apply_eq (cubeInteriorSphereHomeomorph n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_target ``Submission.DifferentialGeometry.Topology.cubeSphereProjectionOpenPartialHomeomorph_target

def liftedCubeSphereProjectionOpenPartialHomeomorph (n : ℕ) :
    OpenPartialHomeomorph (ULift.{u} (Fin (n + 1) → unitInterval)) (ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :=
  (Homeomorph.ulift.transOpenPartialHomeomorph
    (cubeSphereProjectionOpenPartialHomeomorph n)).transHomeomorph Homeomorph.ulift.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph ``Submission.DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph

theorem liftedCubeSphereProjectionOpenPartialHomeomorph_apply (n : ℕ)
    (x : ULift.{u} (Fin (n + 1) → unitInterval)) :
    liftedCubeSphereProjectionOpenPartialHomeomorph n x = ULift.up (cubeSphereProjection n x.down) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_apply ``Submission.DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_apply

theorem liftedCubeSphereProjectionOpenPartialHomeomorph_source (n : ℕ) :
    (liftedCubeSphereProjectionOpenPartialHomeomorph.{u} n).source =
      {x | x.down ∈ cubeInterior (Fin (n + 1))} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_source ``Submission.DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_source

theorem liftedCubeSphereProjectionOpenPartialHomeomorph_target (n : ℕ) :
    (liftedCubeSphereProjectionOpenPartialHomeomorph.{u} n).target = {ULift.up (cubeSphereBasepoint n)}ᶜ := by
  change (Homeomorph.ulift : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) ≃ₜ _) ⁻¹'
    (cubeSphereProjectionOpenPartialHomeomorph n).target = _
  rw [cubeSphereProjectionOpenPartialHomeomorph_target]
  ext z
  change z.down ≠ cubeSphereBasepoint n ↔ z ≠ ULift.up (cubeSphereBasepoint n)
  exact not_congr ⟨fun h => ULift.ext _ _ h, congrArg ULift.down⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_target ``Submission.DifferentialGeometry.Topology.liftedCubeSphereProjectionOpenPartialHomeomorph_target

def liftedCubeSphereProjection (n : ℕ) :
    C(ULift.{u} (Fin (n + 1) → unitInterval),
      ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)) :=
  ⟨fun y => ULift.up (cubeSphereProjection n y.down),
    continuous_uliftUp.comp ((cubeSphereProjection n).continuous.comp continuous_uliftDown)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeSphereProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeSphereProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeSphereProjection ``Submission.DifferentialGeometry.Topology.liftedCubeSphereProjection

theorem liftedCubeSphereProjection_eq_of_mem (n : ℕ)
    {x y : ULift.{u} (Fin (n + 1) → unitInterval)}
    (hx : x.down ∈ cubeInterior (Fin (n + 1)))
    (h : liftedCubeSphereProjection n y = liftedCubeSphereProjection n x) : y = x := by
  apply ULift.ext
  exact cubeSphereProjection_eq_of_mem n hx (congrArg ULift.down h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeSphereProjection_eq_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeSphereProjection_eq_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeSphereProjection_eq_of_mem ``Submission.DifferentialGeometry.Topology.liftedCubeSphereProjection_eq_of_mem

theorem liftedCubeSphereProjection_mapsTo (n : ℕ)
    (x : ULift.{u} (Fin (n + 1) → unitInterval))
    (hx : x.down ∈ cubeInterior (Fin (n + 1))) :
    _root_.Set.MapsTo (liftedCubeSphereProjection n) ({x}ᶜ : Set _)
      ({liftedCubeSphereProjection n x}ᶜ : Set _) :=
  fun _ hy h => hy (liftedCubeSphereProjection_eq_of_mem n hx h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedCubeSphereProjection_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedCubeSphereProjection_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedCubeSphereProjection_mapsTo ``Submission.DifferentialGeometry.Topology.liftedCubeSphereProjection_mapsTo

end DifferentialGeometry.Topology
