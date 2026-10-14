import Submission.DifferentialGeometry.Topology.Homotopy.CubeInterior
import Submission.DifferentialGeometry.Topology.Homotopy.CollapseMaps
import Submission.DifferentialGeometry.Topology.Homotopy.BasedMappingSpace
import Mathlib.Topology.Compactification.OnePoint.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X]



def genLoopCollapseConstantHomeomorph (x : X) :
    GenLoop N X x ≃ₜ collapseConstantMaps (cubeInterior N) x where
  toFun p := ⟨p.val, fun t ht => GenLoop.boundary p t (by
    simpa only [cubeInterior_eq_compl_boundary, _root_.Set.mem_compl_iff, _root_.Classical.not_not] using ht)⟩
  invFun f := ⟨f.val, fun t ht => f.property t (by
    simpa only [cubeInterior_eq_compl_boundary, _root_.Set.mem_compl_iff, _root_.Classical.not_not] using ht)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCollapseConstantHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCollapseConstantHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCollapseConstantHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopCollapseConstantHomeomorph



def genLoopCompactificationHomeomorph [Finite N] [Nonempty N] (x : X) :
    GenLoop N X x ≃ₜ basedOnePointMaps (cubeInterior N) x :=
  (genLoopCollapseConstantHomeomorph x).trans
    (collapseMapsHomeomorph (cubeInterior N) (isOpen_cubeInterior N)
      (cubeInterior_compl_nonempty N) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopCompactificationHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopCompactificationHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopCompactificationHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopCompactificationHomeomorph



def cubeInteriorSphereHomeomorph (n : ℕ) :
    OnePoint (cubeInterior (Fin (n + 1))) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  (euclideanCubeInteriorHomeomorph (Fin (n + 1))).symm.onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (V := Fin (n + 1) → ℝ) (ι := Fin (n + 2)) (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeInteriorSphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeInteriorSphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeInteriorSphereHomeomorph ``Submission.DifferentialGeometry.Topology.cubeInteriorSphereHomeomorph


def cubeSphereBasepoint (n : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
  cubeInteriorSphereHomeomorph n OnePoint.infty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeSphereBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeSphereBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeSphereBasepoint ``Submission.DifferentialGeometry.Topology.cubeSphereBasepoint



def genLoopSphereHomeomorph (n : ℕ) (x : X) :
    GenLoop (Fin (n + 1)) X x ≃ₜ basedMappingSpace (cubeSphereBasepoint n) x :=
  (genLoopCompactificationHomeomorph x).trans
    (basedMappingSpaceDomainHomeomorph (cubeInteriorSphereHomeomorph n).symm
      (cubeSphereBasepoint n) OnePoint.infty
      ((cubeInteriorSphereHomeomorph n).symm_apply_apply OnePoint.infty) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSphereHomeomorph ``Submission.DifferentialGeometry.Topology.genLoopSphereHomeomorph



theorem genLoopSphereHomeomorph_homotopic_iff (n : ℕ) (x : X)
    (p q : GenLoop (Fin (n + 1)) X x) :
    (genLoopSphereHomeomorph n x p).val.HomotopicRel
      (genLoopSphereHomeomorph n x q).val {cubeSphereBasepoint n} ↔ GenLoop.Homotopic p q := by
  rw [← basedMappingSpace_joined_iff, genLoop_homotopic_iff_joined]
  constructor
  · intro h
    simpa only [Homeomorph.symm_apply_apply] using
      h.map (genLoopSphereHomeomorph n x).symm.continuous
  · exact fun h => h.map (genLoopSphereHomeomorph n x).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSphereHomeomorph_homotopic_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSphereHomeomorph_homotopic_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSphereHomeomorph_homotopic_iff ``Submission.DifferentialGeometry.Topology.genLoopSphereHomeomorph_homotopic_iff

end DifferentialGeometry.Topology
