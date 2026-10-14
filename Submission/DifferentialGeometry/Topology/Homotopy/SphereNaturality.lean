import Submission.DifferentialGeometry.Topology.Homotopy.SphereClasses
import Submission.DifferentialGeometry.Topology.Homotopy.BasedMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



theorem genLoopSphereHomeomorph_natural (n : ℕ) (f : C(X, Y))
    (x : X) (y : Y) (hf : f x = y) (Γ : GenLoop (Fin (n + 1)) X x) :
    (genLoopSphereHomeomorph n y (genLoopBasedMap f x y hf Γ)).val =
      f.comp (genLoopSphereHomeomorph n x Γ).val := by
  ext z
  obtain ⟨v, rfl⟩ := cubeSphereProjection_surjective n z
  rw [genLoopSphereHomeomorph_projection, ContinuousMap.comp_apply,
    genLoopSphereHomeomorph_projection]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.genLoopSphereHomeomorph_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.genLoopSphereHomeomorph_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.genLoopSphereHomeomorph_natural ``Submission.DifferentialGeometry.Topology.genLoopSphereHomeomorph_natural


def freeSpherePostcompose (n : ℕ) (f : C(X, Y)) :
    ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) →
      ZerothHomotopy C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, Y) :=
  ZerothHomotopy.lift (fun Γ => ZerothHomotopy.mk (f.comp Γ))
    (fun {_ _} p => ZerothHomotopy.sound (p.map (_root_.ContinuousMap.continuous_postcomp f)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSpherePostcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSpherePostcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSpherePostcompose ``Submission.DifferentialGeometry.Topology.freeSpherePostcompose

@[simp] theorem freeSpherePostcompose_mk (n : ℕ) (f : C(X, Y))
    (Γ : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    freeSpherePostcompose n f (ZerothHomotopy.mk Γ) = ZerothHomotopy.mk (f.comp Γ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeSpherePostcompose_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeSpherePostcompose_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeSpherePostcompose_mk ``Submission.DifferentialGeometry.Topology.freeSpherePostcompose_mk


theorem homotopyGroupToFreeSphere_natural (n : ℕ) (f : C(X, Y))
    (x : X) (y : Y) (hf : f x = y) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupToFreeSphere n y (homotopyGroupBasedMap f x y hf a) =
      freeSpherePostcompose n f (homotopyGroupToFreeSphere n x a) := by
  induction a using Quotient.inductionOn with
  | h Γ =>
    exact congrArg ZerothHomotopy.mk (genLoopSphereHomeomorph_natural n f x y hf Γ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_natural ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_natural



theorem homotopyGroupToFreeSphere_ne_constant_iff [SimplyConnectedSpace X]
    (n : ℕ) (x : X) (a : HomotopyGroup (Fin (n + 1)) X x) :
    homotopyGroupToFreeSphere n x a ≠ ZerothHomotopy.mk (ContinuousMap.const _ x) ↔ a ≠ 1 := by
  rw [← homotopyGroupToFreeSphere_one n x]
  exact not_congr (homotopyGroupToFreeSphere_injective n x).eq_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_ne_constant_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopyGroupToFreeSphere_ne_constant_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopyGroupToFreeSphere_ne_constant_iff ``Submission.DifferentialGeometry.Topology.homotopyGroupToFreeSphere_ne_constant_iff

end DifferentialGeometry.Topology
