import Submission.DifferentialGeometry.Bundle.Section
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

def IsCovariantlyInvariantSubmoduleFamily
    (cov : CovariantDerivative I F V)
    (S : ∀ x, Submodule ℝ (V x)) : Prop :=
  ∀ (s : Cₛ^∞⟮I; F, V⟯) (U : Set M), IsOpen U →
    (∀ x ∈ U, s x ∈ S x) →
    ∀ x ∈ U, ∀ v : TangentSpace I x, cov s x v ∈ S x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily ``Submission.DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily

namespace IsCovariantlyInvariantSubmoduleFamily

omit [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I] in
theorem covariantDerivative_mem
    {cov : CovariantDerivative I F V} {S : ∀ x, Submodule ℝ (V x)}
    (h : IsCovariantlyInvariantSubmoduleFamily cov S)
    (s : Cₛ^∞⟮I; F, V⟯) {U : Set M} (hU : IsOpen U)
    (hs : ∀ x ∈ U, s x ∈ S x) {x : M} (hx : x ∈ U)
    (v : TangentSpace I x) :
    cov s x v ∈ S x :=
  h s U hU hs x hx v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily.covariantDerivative_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily.covariantDerivative_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily.covariantDerivative_mem ``Submission.DifferentialGeometry.Geometry.Connection.IsCovariantlyInvariantSubmoduleFamily.covariantDerivative_mem

end IsCovariantlyInvariantSubmoduleFamily

end DifferentialGeometry.Geometry.Connection
