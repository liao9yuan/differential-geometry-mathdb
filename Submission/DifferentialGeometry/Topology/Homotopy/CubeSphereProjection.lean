import Submission.DifferentialGeometry.Topology.Homotopy.CubeCompactification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]


def cubeSphereProjection (n : ℕ) :
    C(Fin (n + 1) → unitInterval, Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  ⟨fun t => cubeInteriorSphereHomeomorph n (openCollapse (cubeInterior (Fin (n + 1))) t),
    (cubeInteriorSphereHomeomorph n).continuous.comp
      (continuous_openCollapse _ (isOpen_cubeInterior _))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjection ``Submission.DifferentialGeometry.Topology.cubeSphereProjection


theorem cubeSphereProjection_boundary (n : ℕ) (t : Fin (n + 1) → unitInterval)
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    cubeSphereProjection n t = cubeSphereBasepoint n := by
  change cubeInteriorSphereHomeomorph n (openCollapse _ t) = _
  rw [openCollapse_of_notMem _ (by
    simpa only [cubeInterior_eq_compl_boundary, _root_.Set.mem_compl_iff, _root_.Classical.not_not] using ht)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjection_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjection_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjection_boundary ``Submission.DifferentialGeometry.Topology.cubeSphereProjection_boundary


theorem cubeSphereProjection_surjective (n : ℕ) : _root_.Function.Surjective (cubeSphereProjection n) :=
  (cubeInteriorSphereHomeomorph n).surjective.comp
    (openCollapse_surjective _ (cubeInterior_compl_nonempty _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereProjection_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereProjection_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereProjection_surjective ``Submission.DifferentialGeometry.Topology.cubeSphereProjection_surjective


theorem genLoopSphereHomeomorph_projection (n : ℕ) (x : X)
    (p : GenLoop (Fin (n + 1)) X x) (t : Fin (n + 1) → unitInterval) :
    (genLoopSphereHomeomorph n x p).val (cubeSphereProjection n t) = p t := by
  have h := basedMappingSpaceDomainHomeomorph_apply (cubeInteriorSphereHomeomorph n).symm
    (cubeSphereBasepoint n) OnePoint.infty
    ((cubeInteriorSphereHomeomorph n).symm_apply_apply OnePoint.infty) x
    (genLoopCompactificationHomeomorph x p) (cubeSphereProjection n t)
  refine h.trans ?_
  change collapseDescendValue (cubeInterior (Fin (n + 1))) x
    (genLoopCollapseConstantHomeomorph x p)
      ((cubeInteriorSphereHomeomorph n).symm
        (cubeInteriorSphereHomeomorph n (openCollapse _ t))) = p t
  rw [Homeomorph.symm_apply_apply]
  exact collapseDescendValue_comp _ x (genLoopCollapseConstantHomeomorph x p) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSphereHomeomorph_projection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSphereHomeomorph_projection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSphereHomeomorph_projection ``Submission.DifferentialGeometry.Topology.genLoopSphereHomeomorph_projection


theorem genLoopSphereHomeomorph_const (n : ℕ) (x : X) :
    (genLoopSphereHomeomorph n x GenLoop.const).val = ContinuousMap.const _ x := by
  ext z
  obtain ⟨t, rfl⟩ := cubeSphereProjection_surjective n z
  exact genLoopSphereHomeomorph_projection n x GenLoop.const t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSphereHomeomorph_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSphereHomeomorph_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSphereHomeomorph_const ``Submission.DifferentialGeometry.Topology.genLoopSphereHomeomorph_const

end DifferentialGeometry.Topology
