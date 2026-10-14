import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexEvaluation
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionHomotopyNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Subdivision and its same homotopy on all original singular chains -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

/-- The original universal affine subdivision, exactly restricted to its
same lifted simplex body. -/
def universalSimplexSubdivision (n : ℕ) : integralSingularChainsIn n (liftedSimplexBody.{u} n) :=
  ⟨affineSingularSubdivision n (affineSingularChain n (liftedSimplexVertex n)),
    affineSingularChainsIn_le n (convex_liftedSimplexBody n)
      (affineSingularSubdivision_mem n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.universalSimplexSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.universalSimplexSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.universalSimplexSubdivision ``Submission.DifferentialGeometry.Topology.universalSimplexSubdivision

/-- The SAME universal affine homotopy, carried by the same lifted simplex body. -/
def universalSimplexHomotopy (n : ℕ) : integralSingularChainsIn (n + 1) (liftedSimplexBody.{u} n) :=
  ⟨affineSubdivisionHomotopy n (affineSingularChain n (liftedSimplexVertex n)),
    affineSingularChainsIn_le (n + 1) (convex_liftedSimplexBody n)
      (affineSubdivisionHomotopy_mem n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.universalSimplexHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.universalSimplexHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.universalSimplexHomotopy ``Submission.DifferentialGeometry.Topology.universalSimplexHomotopy

variable {X : Type u} [TopologicalSpace X]

/-- Subdivision on EVERY original singular simplex, by evaluation of its
same universal subdivided simplex, extended on the original singular basis. -/
def integralSingularSubdivision (n : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X n :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains X).X n) ℕ
    (fun σ => singularSimplexChainPush n n σ (universalSimplexSubdivision n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivision ``Submission.DifferentialGeometry.Topology.integralSingularSubdivision

/-- Exact evaluation formula on each original coefficient-one singular simplex. -/
theorem integralSingularSubdivision_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSubdivision n (integralSimplexChain n σ) =
      singularSimplexChainPush n n σ (universalSimplexSubdivision n) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivision_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivision_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivision_simplex ``Submission.DifferentialGeometry.Topology.integralSingularSubdivision_simplex

/-- The original universal homotopy similarly acts on EVERY original singular simplex. -/
def integralSingularSubdivisionHomotopy (n : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X (n + 1) :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains X).X (n + 1)) ℕ
    (fun σ => singularSimplexChainPush n (n + 1) σ (universalSimplexHomotopy n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy

/-- The same homotopy component on each original coefficient-one simplex. -/
theorem integralSingularSubdivisionHomotopy_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSubdivisionHomotopy n (integralSimplexChain n σ) =
      singularSimplexChainPush n (n + 1) σ (universalSimplexHomotopy n) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_simplex ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_simplex

/-- Subdivision is the original identity in degree zero. -/
theorem integralSingularSubdivision_zero :
    integralSingularSubdivision (X := X) 0 = LinearMap.id := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, integralSingularSubdivision_simplex]
  exact singularSimplexChainPush_identity 0 σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivision_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivision_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivision_zero ``Submission.DifferentialGeometry.Topology.integralSingularSubdivision_zero

/-- The SAME homotopy has zero degree-zero component. -/
theorem integralSingularSubdivisionHomotopy_zero :
    integralSingularSubdivisionHomotopy (X := X) 0 = 0 := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, integralSingularSubdivisionHomotopy_simplex]
  exact (singularSimplexChainPush 0 1 σ).map_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_zero ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_zero

end DifferentialGeometry.Topology
