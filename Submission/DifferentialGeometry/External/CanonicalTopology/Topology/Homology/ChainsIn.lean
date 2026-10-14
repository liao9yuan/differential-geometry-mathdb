import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual singular chains carried by a prescribed subspace -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Chains carried by A are spanned by original simplices whose actual
continuous maps have image in A. -/
def integralSingularChainsIn (n : ℕ) (A : Set X) :
    Submodule ℤ ((integralSingularChains X).X n) :=
  Submodule.span ℤ {c | ∃ σ : integralSingularSimplex n X,
    _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ A ∧ c = integralSimplexChain n σ}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn

/-- The same actual simplex factors through its original image subspace. -/
def integralSingularSimplexRestriction (n : ℕ) (A : Set X) (σ : integralSingularSimplex n X)
    (hσ : _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ A) : integralSingularSimplex n A :=
  (integralSingularSimplexEquiv n A).symm
    ⟨fun t => ⟨integralSingularSimplexEquiv n X σ t, hσ ⟨t, rfl⟩⟩,
      (integralSingularSimplexEquiv n X σ).continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSimplexRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSimplexRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSimplexRestriction ``Submission.DifferentialGeometry.Topology.integralSingularSimplexRestriction

/-- Inclusion recovers the same simplex with its exact original parameters. -/
theorem integralSingularSimplexRestriction_inclusion (n : ℕ) (A : Set X)
    (σ : integralSingularSimplex n X) (hσ : _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ A) :
    integralSingularSimplexMap n (singularSubspaceInclusion A)
      (integralSingularSimplexRestriction n A σ hσ) = σ := by
  apply (integralSingularSimplexEquiv n X).injective
  rw [integralSingularSimplexMap_apply]
  unfold integralSingularSimplexRestriction
  rw [Equiv.apply_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSimplexRestriction_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSimplexRestriction_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSimplexRestriction_inclusion ``Submission.DifferentialGeometry.Topology.integralSingularSimplexRestriction_inclusion

/-- The support description is exactly the range of the original subspace
inclusion on actual singular chains. -/
theorem integralSingularChainsIn_eq_range (n : ℕ) (A : Set X) :
    integralSingularChainsIn n A =
      LinearMap.range ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro c ⟨σ, hσ, rfl⟩
    refine ⟨integralSimplexChain n (integralSingularSimplexRestriction n A σ hσ), ?_⟩
    rw [integralSimplexChain_map, integralSingularSimplexRestriction_inclusion]
  · have htop : Submodule.comap
        ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom
          (integralSingularChainsIn n A) = ⊤ := by
      apply top_unique
      rw [← (integralSingularChainBasis n A).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨σ, rfl⟩
      change (integralSingularChainMap (singularSubspaceInclusion A)).f n
        (integralSingularChainBasis n A σ) ∈ integralSingularChainsIn n A
      rw [integralSingularChainBasis_apply, integralSimplexChain_map]
      apply Submodule.subset_span
      refine ⟨integralSingularSimplexMap n (singularSubspaceInclusion A) σ, ?_, rfl⟩
      rintro _ ⟨t, rfl⟩
      rw [integralSingularSimplexMap_apply]
      exact (integralSingularSimplexEquiv n A σ t).property
    rintro c ⟨b, rfl⟩
    exact show b ∈ Submodule.comap
      ((integralSingularChainMap (singularSubspaceInclusion A)).f n).hom
        (integralSingularChainsIn n A) from htop.symm ▸ Submodule.mem_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_eq_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_eq_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_eq_range ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_eq_range

/-- The original boundary preserves the actual carrier. -/
theorem integralSingularChainsIn_boundary (n : ℕ) (A : Set X)
    {c : (integralSingularChains X).X (n + 1)} (hc : c ∈ integralSingularChainsIn (n + 1) A) :
    (integralSingularChains X).d (n + 1) n c ∈ integralSingularChainsIn n A := by
  rw [integralSingularChainsIn_eq_range] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  refine ⟨(integralSingularChains A).d (n + 1) n b, ?_⟩
  exact (congrArg (fun h : (integralSingularChains A).X (n + 1) ⟶
    (integralSingularChains X).X n => h b)
      ((integralSingularChainMap (singularSubspaceInclusion A)).comm (n + 1) n)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_boundary ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_boundary

end DifferentialGeometry.Topology
