import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual maps of singular-chain carriers and exact restrictions -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original induced chain map carries chains in A to chains in B
whenever the original continuous map takes A into B. -/
theorem integralSingularChainsIn_map (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : _root_.Set.MapsTo f A B) {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    (integralSingularChainMap f).f n c ∈ integralSingularChainsIn n B := by
  have h : integralSingularChainsIn n A ≤
      Submodule.comap ((integralSingularChainMap f).f n).hom (integralSingularChainsIn n B) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change (integralSingularChainMap f).f n (integralSimplexChain n σ) ∈ integralSingularChainsIn n B
    rw [integralSimplexChain_map]
    apply Submodule.subset_span
    refine ⟨integralSingularSimplexMap n f σ, ?_, rfl⟩
    rintro _ ⟨t, rfl⟩
    rw [integralSingularSimplexMap_apply]
    exact hf (hσ ⟨t, rfl⟩)
  exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_map ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_map

/-- The actual induced map restricted to the corresponding original carriers. -/
def singularCarrierMap (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : _root_.Set.MapsTo f A B) :
    integralSingularChainsIn n A →ₗ[ℤ] integralSingularChainsIn n B :=
  ((integralSingularChainMap f).f n).hom.restrict (fun _ hc => integralSingularChainsIn_map n f hf hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.singularCarrierMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.singularCarrierMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.singularCarrierMap ``Submission.DifferentialGeometry.Topology.singularCarrierMap

/-- Exact restriction commutes with the SAME original map of subspaces. -/
theorem integralSingularChainRestriction_map (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : _root_.Set.MapsTo f A B) (c : integralSingularChainsIn n A) :
    integralSingularChainRestriction n B (singularCarrierMap n f hf c) =
      (integralSingularChainMap (singularPairRestriction f hf)).f n (integralSingularChainRestriction n A c) := by
  apply integralSingularChainInclusion_injective n B
  rw [integralSingularChainRestriction_inclusion]
  have h := congrArg (fun h : integralSingularChains A ⟶ integralSingularChains Y =>
    h.f n (integralSingularChainRestriction n A c)) (integralSingularChainMap_pair_square f hf)
  change (integralSingularChainMap f).f n ((integralSingularChainMap (singularSubspaceInclusion A)).f n
    (integralSingularChainRestriction n A c)) =
      (integralSingularChainMap (singularSubspaceInclusion B)).f n
        ((integralSingularChainMap (singularPairRestriction f hf)).f n
          (integralSingularChainRestriction n A c)) at h
  rw [integralSingularChainRestriction_inclusion] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainRestriction_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainRestriction_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainRestriction_map ``Submission.DifferentialGeometry.Topology.integralSingularChainRestriction_map

end DifferentialGeometry.Topology
