import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainsIn
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SubdivisionNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Exact restriction of original singular chains to their carrier -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Retain the original carrier submodule's integer scalar action. -/
instance integralSingularChainsInModule (n : ℕ) (A : Set X) :
    Module ℤ (integralSingularChainsIn n A) := (integralSingularChainsIn n A).module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsInModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsInModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsInModule ``Submission.DifferentialGeometry.Topology.integralSingularChainsInModule

/-- Inclusion is injective in each original chain degree. -/
theorem integralSingularChainInclusion_injective (n : ℕ) (A : Set X) :
    Function.Injective ((integralSingularChainMap (singularSubspaceInclusion A)).f n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainInclusion_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainInclusion_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainInclusion_injective ``Submission.DifferentialGeometry.Topology.integralSingularChainInclusion_injective

/-- Chains on the original subspace are exactly the original chains carried
by it, with the same coefficients and boundary parametrizations. -/
def integralSingularChainCarrierEquiv (n : ℕ) (A : Set X) :
    (integralSingularChains A).X n ≃ₗ[ℤ] integralSingularChainsIn n A :=
  (LinearEquiv.ofInjective ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom
    (integralSingularChainInclusion_injective n A)).trans
      (LinearEquiv.ofEq _ _ (integralSingularChainsIn_eq_range n A).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainCarrierEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainCarrierEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainCarrierEquiv ``Submission.DifferentialGeometry.Topology.integralSingularChainCarrierEquiv

/-- This equivalence has the original inclusion as its underlying map. -/
theorem integralSingularChainCarrierEquiv_coe (n : ℕ) (A : Set X)
    (c : (integralSingularChains A).X n) :
    (integralSingularChainCarrierEquiv n A c).val =
      (integralSingularChainMap (singularSubspaceInclusion A)).f n c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainCarrierEquiv_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainCarrierEquiv_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainCarrierEquiv_coe ``Submission.DifferentialGeometry.Topology.integralSingularChainCarrierEquiv_coe

/-- Exact linear restriction to the actual carrier, inverse to inclusion. -/
def integralSingularChainRestriction (n : ℕ) (A : Set X) :
    integralSingularChainsIn n A →ₗ[ℤ] (integralSingularChains A).X n :=
  (integralSingularChainCarrierEquiv n A).symm.toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainRestriction ``Submission.DifferentialGeometry.Topology.integralSingularChainRestriction

/-- Including a restricted chain recovers that SAME original chain. -/
theorem integralSingularChainRestriction_inclusion (n : ℕ) (A : Set X)
    (c : integralSingularChainsIn n A) :
    (integralSingularChainMap (singularSubspaceInclusion A)).f n
      (integralSingularChainRestriction n A c) = c.val :=
  congrArg Subtype.val ((integralSingularChainCarrierEquiv n A).apply_symm_apply c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainRestriction_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainRestriction_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainRestriction_inclusion ``Submission.DifferentialGeometry.Topology.integralSingularChainRestriction_inclusion

/-- Restriction commutes with the actual boundary, through the proved
carrier preservation of that same boundary. -/
theorem integralSingularChainRestriction_boundary (n : ℕ) (A : Set X)
    (c : integralSingularChainsIn (n + 1) A) :
    integralSingularChainRestriction n A
      ⟨(integralSingularChains X).d (n + 1) n c.val, integralSingularChainsIn_boundary n A c.property⟩ =
      (integralSingularChains A).d (n + 1) n (integralSingularChainRestriction (n + 1) A c) := by
  apply integralSingularChainInclusion_injective n A
  rw [integralSingularChainRestriction_inclusion, integralSingularChainMap_boundary,
    integralSingularChainRestriction_inclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainRestriction_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainRestriction_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainRestriction_boundary ``Submission.DifferentialGeometry.Topology.integralSingularChainRestriction_boundary

end DifferentialGeometry.Topology
