import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainsIn
import Mathlib.LinearAlgebra.Basis.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Finite support and intersections for the original singular chains -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The geometric carrier submodule is the span of the corresponding
subset of the original proved singular basis. -/
theorem integralSingularChainsIn_eq_span_basis (n : ℕ) (A : Set X) :
    integralSingularChainsIn n A = Submodule.span ℤ
      (integralSingularChainBasis n X ''
        {σ | _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ A}) := by
  unfold integralSingularChainsIn
  congr 1
  ext c
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, integralSingularChainBasis_apply n σ⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, integralSingularChainBasis_apply n σ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_eq_span_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_eq_span_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_eq_span_basis ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_eq_span_basis

/-- A chain lies in A precisely when each original simplex with nonzero
integer coefficient has its actual image in A. -/
theorem integralSingularChainsIn_mem_iff (n : ℕ) (A : Set X)
    (c : (integralSingularChains X).X n) :
    c ∈ integralSingularChainsIn n A ↔
      ∀ σ : integralSingularSimplex n X, integralSingularChainRepr n X c σ ≠ 0 →
        range (integralSingularSimplexEquiv n X σ) ⊆ A := by
  rw [integralSingularChainsIn_eq_span_basis, (integralSingularChainBasis n X).mem_span_image]
  change (↑(integralSingularChainRepr n X c).support : Set _) ⊆
    {σ | _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ A} ↔ _
  constructor
  · intro h σ hσ
    exact h (Finsupp.mem_support_iff.mpr hσ)
  · intro h σ hσ
    exact h σ (Finsupp.mem_support_iff.mp hσ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_mem_iff ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_mem_iff

/-- The support description respects inclusion of actual carriers. -/
theorem integralSingularChainsIn_mono (n : ℕ) {A B : Set X} (h : A ⊆ B) :
    integralSingularChainsIn n A ≤ integralSingularChainsIn n B := by
  intro c hc
  rw [integralSingularChainsIn_mem_iff] at hc ⊢
  exact fun σ hσ => (hc σ hσ).trans h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_mono ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_mono

/-- Intersections of original subspaces give intersections of their actual
singular-chain ranges, by uniqueness of the original basis coefficients. -/
theorem integralSingularChainsIn_inter (n : ℕ) (A B : Set X) :
    integralSingularChainsIn n (A ∩ B) =
      integralSingularChainsIn n A ⊓ integralSingularChainsIn n B := by
  apply le_antisymm
  · exact le_inf (integralSingularChainsIn_mono n _root_.Set.inter_subset_left)
      (integralSingularChainsIn_mono n _root_.Set.inter_subset_right)
  · intro c hc
    rw [integralSingularChainsIn_mem_iff]
    intro σ hσ
    exact _root_.Set.subset_inter ((integralSingularChainsIn_mem_iff n A c).mp hc.1 σ hσ)
      ((integralSingularChainsIn_mem_iff n B c).mp hc.2 σ hσ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_inter ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_inter

/-- Every actual singular chain is carried by the whole space. -/
theorem integralSingularChainsIn_univ (n : ℕ) :
    integralSingularChainsIn n (_root_.Set.univ : Set X) = ⊤ := by
  apply top_unique
  intro c _
  exact (integralSingularChainsIn_mem_iff n _root_.Set.univ c).mpr (fun _ _ => _root_.Set.subset_univ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_univ ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_univ

/-- The empty subspace carries only the original zero chain. -/
theorem integralSingularChainsIn_empty (n : ℕ) :
    integralSingularChainsIn n (∅ : Set X) = ⊥ := by
  apply bot_unique
  intro c hc
  change c = 0
  apply (integralSingularChainRepr n X).injective
  rw [map_zero]
  apply Finsupp.ext
  intro σ
  by_contra hσ
  have h := (integralSingularChainsIn_mem_iff n ∅ c).mp hc σ hσ
  exact (_root_.Set.range_nonempty (integralSingularSimplexEquiv n X σ)).ne_empty
    (subset_empty_iff.mp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsIn_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsIn_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsIn_empty ``Submission.DifferentialGeometry.Topology.integralSingularChainsIn_empty

end DifferentialGeometry.Topology
