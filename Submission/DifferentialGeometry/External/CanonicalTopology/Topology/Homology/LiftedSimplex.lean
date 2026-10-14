import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineNaturality
import Mathlib.Analysis.Normed.Operator.LinearIsometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual standard simplex in the singular chain universe -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

/-- The standard finite coordinate space, lifted only to the target universe. -/
abbrev liftedSimplexSpace (n : ℕ) := ULift.{u} (Fin (n + 1) → ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexSpace ``Submission.DifferentialGeometry.Topology.liftedSimplexSpace

/-- The actual barycentric simplex as a convex subset of that lifted space. -/
def liftedSimplexBody (n : ℕ) : Set (liftedSimplexSpace.{u} n) :=
  {x | x.down ∈ stdSimplex ℝ (Fin (n + 1))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexBody then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexBody"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexBody ``Submission.DifferentialGeometry.Topology.liftedSimplexBody

/-- Its original ordered vertices, with only the universe lift added. -/
def liftedSimplexVertex (n : ℕ) (i : Fin (n + 1)) : liftedSimplexSpace.{u} n :=
  ULift.up (Pi.single i 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexVertex ``Submission.DifferentialGeometry.Topology.liftedSimplexVertex

/-- The lifted body is convex for the original real scalar action. -/
theorem convex_liftedSimplexBody (n : ℕ) : Convex ℝ (liftedSimplexBody.{u} n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).linear_preimage
    (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ)).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.convex_liftedSimplexBody then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.convex_liftedSimplexBody"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.convex_liftedSimplexBody ``Submission.DifferentialGeometry.Topology.convex_liftedSimplexBody

/-- Each lifted original vertex belongs to the same lifted body. -/
theorem liftedSimplexVertex_mem (n : ℕ) (i : Fin (n + 1)) :
    liftedSimplexVertex.{u} n i ∈ liftedSimplexBody n := single_mem_stdSimplex ℝ i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexVertex_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexVertex_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexVertex_mem ``Submission.DifferentialGeometry.Topology.liftedSimplexVertex_mem

/-- The actual original standard simplex and this body have exactly the
same points, parameters and topology, modulo the universe lift. -/
def liftedSimplexHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ liftedSimplexBody.{u} n where
  toFun t := ⟨ULift.up t.val, t.property⟩
  invFun t := ⟨t.val.down, t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((Homeomorph.ulift.symm.continuous).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((Homeomorph.ulift.continuous).comp continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexHomeomorph ``Submission.DifferentialGeometry.Topology.liftedSimplexHomeomorph

/-- The original affine simplex on these vertices is exactly the lifted
identity parametrization of the same standard simplex. -/
theorem affineSimplexMap_liftedSimplexVertex (n : ℕ) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplexMap (liftedSimplexVertex.{u} n) t = ULift.up t.val := by
  apply (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ)).injective
  change (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (∑ i, t.val i • liftedSimplexVertex n i) = t.val
  rw [map_sum]
  simp only [map_smul]
  funext j
  simp [Finset.sum_apply, liftedSimplexVertex, Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexMap_liftedSimplexVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexMap_liftedSimplexVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexMap_liftedSimplexVertex ``Submission.DifferentialGeometry.Topology.affineSimplexMap_liftedSimplexVertex

/-- The original universal affine simplex chain lies in that same body. -/
theorem liftedSimplexChain_mem (n : ℕ) :
    affineSingularChain n (liftedSimplexVertex.{u} n) ∈ affineSingularChainsIn n (liftedSimplexBody n) :=
  affineSingularChain_mem n _ _ (liftedSimplexVertex_mem n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexChain_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexChain_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexChain_mem ``Submission.DifferentialGeometry.Topology.liftedSimplexChain_mem

end DifferentialGeometry.Topology
