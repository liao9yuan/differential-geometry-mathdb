import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Explicit augmentation of the original integral singular chains -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Sum of the actual integer coefficients in degree zero. -/
def integralSingularAugmentation : (integralSingularChains X).X 0 →ₗ[ℤ] ℤ :=
  (integralSingularChainBasis 0 X).constr (M' := ℤ) ℕ (fun _ => 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularAugmentation ``Submission.DifferentialGeometry.Topology.integralSingularAugmentation

/-- Every original coefficient-one vertex has augmentation one. -/
theorem integralSingularAugmentation_simplex (σ : integralSingularSimplex 0 X) :
    integralSingularAugmentation (integralSimplexChain 0 σ) = 1 := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularAugmentation_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularAugmentation_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularAugmentation_simplex ``Submission.DifferentialGeometry.Topology.integralSingularAugmentation_simplex

/-- The actual boundary has zero augmentation in degree zero. -/
theorem integralSingularAugmentation_boundary :
    integralSingularAugmentation.comp ((integralSingularChains X).d 1 0).hom = 0 := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  change integralSingularAugmentation ((integralSingularChains X).d 1 0
    (integralSimplexChain 1 σ)) = 0
  rw [integralSimplexChain_boundary_one, map_sub,
    integralSingularAugmentation_simplex, integralSingularAugmentation_simplex, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularAugmentation_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularAugmentation_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularAugmentation_boundary ``Submission.DifferentialGeometry.Topology.integralSingularAugmentation_boundary

end DifferentialGeometry.Topology
