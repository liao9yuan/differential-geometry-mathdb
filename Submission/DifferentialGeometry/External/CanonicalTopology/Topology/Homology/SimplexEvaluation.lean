import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LiftedSimplex
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Evaluating universal original chains through the same singular simplex -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

/-- The original identity simplex with values in its same lifted body. -/
def liftedSimplexIdentity (n : ℕ) : integralSingularSimplex n (liftedSimplexBody.{u} n) :=
  (integralSingularSimplexEquiv n _).symm ⟨liftedSimplexHomeomorph.{u} n,
    (liftedSimplexHomeomorph.{u} n).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexIdentity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexIdentity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexIdentity ``Submission.DifferentialGeometry.Topology.liftedSimplexIdentity

/-- Including that identity gives the actual affine simplex on the original vertices. -/
theorem liftedSimplexIdentity_inclusion (n : ℕ) :
    integralSingularSimplexMap n (singularSubspaceInclusion (liftedSimplexBody.{u} n))
      (liftedSimplexIdentity n) = affineSingularSimplex n (liftedSimplexVertex n) := by
  apply (integralSingularSimplexEquiv n _).injective
  rw [integralSingularSimplexMap_apply]
  unfold liftedSimplexIdentity affineSingularSimplex
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro t
  exact (affineSimplexMap_liftedSimplexVertex n t).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexIdentity_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexIdentity_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexIdentity_inclusion ``Submission.DifferentialGeometry.Topology.liftedSimplexIdentity_inclusion

/-- Exact restriction of the universal affine identity chain gives that
SAME singular identity chain on the lifted body. -/
theorem liftedSimplexChain_restriction (n : ℕ) :
    integralSingularChainRestriction n (liftedSimplexBody.{u} n)
      ⟨affineSingularChain n (liftedSimplexVertex n),
        affineSingularChainsIn_le n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n)⟩ =
      integralSimplexChain n (liftedSimplexIdentity n) := by
  apply integralSingularChainInclusion_injective n (liftedSimplexBody n)
  rw [integralSingularChainRestriction_inclusion, integralSimplexChain_map, liftedSimplexIdentity_inclusion]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexChain_restriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexChain_restriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexChain_restriction ``Submission.DifferentialGeometry.Topology.liftedSimplexChain_restriction

variable {X : Type u} [TopologicalSpace X]

/-- Evaluate an original singular simplex on its same lifted barycentric body. -/
def singularSimplexEvaluation (n : ℕ) (σ : integralSingularSimplex n X) :
    C(liftedSimplexBody.{u} n, X) :=
  (integralSingularSimplexEquiv n X σ).comp
    ⟨(liftedSimplexHomeomorph.{u} n).symm, (liftedSimplexHomeomorph.{u} n).symm.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexEvaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexEvaluation ``Submission.DifferentialGeometry.Topology.singularSimplexEvaluation

/-- This evaluation sends the original identity simplex to the SAME input
singular simplex, with no replacement or reparametrization. -/
theorem singularSimplexEvaluation_identity (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSimplexMap n (singularSimplexEvaluation n σ) (liftedSimplexIdentity n) = σ := by
  apply (integralSingularSimplexEquiv n X).injective
  rw [integralSingularSimplexMap_apply]
  unfold liftedSimplexIdentity
  rw [Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro t
  change integralSingularSimplexEquiv n X σ
    ((liftedSimplexHomeomorph.{u} n).symm (liftedSimplexHomeomorph.{u} n t)) = _
  rw [Homeomorph.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexEvaluation_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexEvaluation_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexEvaluation_identity ``Submission.DifferentialGeometry.Topology.singularSimplexEvaluation_identity

/-- Push an original chain carried by the lifted simplex through the SAME
original singular simplex, by exact restriction and its actual induced map. -/
def singularSimplexChainPush (n k : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularChainsIn k (liftedSimplexBody.{u} n) →ₗ[ℤ] (integralSingularChains X).X k :=
  ((integralSingularChainMap (singularSimplexEvaluation n σ)).f k).hom.comp
    (integralSingularChainRestriction k (liftedSimplexBody n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexChainPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexChainPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexChainPush ``Submission.DifferentialGeometry.Topology.singularSimplexChainPush

/-- Pushing the original affine identity chain recovers the input coefficient-one simplex. -/
theorem singularSimplexChainPush_identity (n : ℕ) (σ : integralSingularSimplex n X) :
    singularSimplexChainPush n n σ
      ⟨affineSingularChain n (liftedSimplexVertex n),
        affineSingularChainsIn_le n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n)⟩ =
      integralSimplexChain n σ := by
  unfold singularSimplexChainPush
  rw [LinearMap.comp_apply, liftedSimplexChain_restriction, integralSimplexChain_map,
    singularSimplexEvaluation_identity]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexChainPush_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexChainPush_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexChainPush_identity ``Submission.DifferentialGeometry.Topology.singularSimplexChainPush_identity

/-- Pushing these same carrier chains commutes with their actual original boundary. -/
theorem singularSimplexChainPush_boundary (n k : ℕ) (σ : integralSingularSimplex n X)
    (c : integralSingularChainsIn (k + 1) (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush n k σ
      ⟨(integralSingularChains (liftedSimplexSpace n)).d (k + 1) k c.val,
        integralSingularChainsIn_boundary k _ c.property⟩ =
      (integralSingularChains X).d (k + 1) k (singularSimplexChainPush n (k + 1) σ c) := by
  unfold singularSimplexChainPush
  rw [LinearMap.comp_apply, integralSingularChainRestriction_boundary,
    integralSingularChainMap_boundary]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularSimplexChainPush_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularSimplexChainPush_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularSimplexChainPush_boundary ``Submission.DifferentialGeometry.Topology.singularSimplexChainPush_boundary

end DifferentialGeometry.Topology
