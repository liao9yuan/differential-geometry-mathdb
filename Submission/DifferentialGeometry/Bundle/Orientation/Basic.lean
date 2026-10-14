import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.LinearAlgebra.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Bundle
open scoped _root_.Topology
set_option autoImplicit false

namespace DifferentialGeometry.VectorBundle

variable {m : ℕ} {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def IsCompatibleOrientation (o : ∀ x, Orientation ℝ (V x) (Fin m)) : Prop :=
  ∀ x : B, ∃ t : _root_.Bundle.Trivialization F (π F V), ∃ _ht : MemTrivializationAtlas t,
    ∃ U ∈ 𝓝 x, ∃ hU : U ⊆ t.baseSet, ∃ p : Orientation ℝ F (Fin m),
      ∀ y (hy : y ∈ U),
        Orientation.map (Fin m) (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv (o y) = p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.IsCompatibleOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.IsCompatibleOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.IsCompatibleOrientation ``Submission.DifferentialGeometry.VectorBundle.IsCompatibleOrientation

theorem IsCompatibleOrientation.neg {o : ∀ x, Orientation ℝ (V x) (Fin m)}
    (ho : IsCompatibleOrientation (F := F) V o) :
    IsCompatibleOrientation (F := F) V (fun x => -o x) := by
  intro x
  obtain ⟨t, ht, U, hUx, hU, p, hp⟩ := ho x
  refine ⟨t, ht, U, hUx, hU, -p, ?_⟩
  intro y hy
  rw [Orientation.map_neg, hp y hy]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.VectorBundle.IsCompatibleOrientation
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.IsCompatibleOrientation.neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.IsCompatibleOrientation.neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.IsCompatibleOrientation.neg ``Submission.DifferentialGeometry.VectorBundle.IsCompatibleOrientation.neg

theorem isCompatibleOrientation_trivial (B : Type*) [TopologicalSpace B]
    (p : Orientation ℝ F (Fin m)) :
    IsCompatibleOrientation (F := F) (Bundle.Trivial B F) (fun _ => p) := by
  intro x
  refine ⟨Bundle.Trivial.trivialization B F, ⟨mem_singleton _⟩, _root_.Set.univ, Filter.univ_mem,
    (fun _ _ => _root_.Set.mem_univ _), p, ?_⟩
  intro y hy
  rw [Bundle.Trivial.continuousLinearEquivAt_trivialization]
  exact congrArg (fun q => q p) (Orientation.map_refl (Fin m))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorBundle.isCompatibleOrientation_trivial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorBundle.isCompatibleOrientation_trivial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorBundle.isCompatibleOrientation_trivial ``Submission.DifferentialGeometry.VectorBundle.isCompatibleOrientation_trivial

end DifferentialGeometry.VectorBundle
