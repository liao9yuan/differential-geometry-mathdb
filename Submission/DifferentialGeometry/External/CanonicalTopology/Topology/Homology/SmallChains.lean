import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The original small-chain submodules for a family of subspaces -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Small chains are sums of actual chains carried by members of the
specified family. No subdivision or excision conclusion is assumed. -/
def integralSingularSmallChains (n : ℕ) (U : ι → Set X) :
    Submodule ℤ ((integralSingularChains X).X n) :=
  ⨆ i, integralSingularChainsIn n (U i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSmallChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSmallChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSmallChains ``Submission.DifferentialGeometry.Topology.integralSingularSmallChains

/-- The same submodule is spanned by original simplices individually
contained in one of the specified subspaces. -/
theorem integralSingularSmallChains_eq_span_basis (n : ℕ) (U : ι → Set X) :
    integralSingularSmallChains n U = Submodule.span ℤ
      (integralSingularChainBasis n X ''
        {σ | ∃ i, _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ U i}) := by
  unfold integralSingularSmallChains
  simp_rw [integralSingularChainsIn_eq_span_basis]
  rw [← Submodule.span_iUnion, ← Set.image_iUnion]
  have hs : (⋃ i, {σ | _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ U i}) =
      {σ | ∃ i, _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ U i} := by
    ext σ
    simp
  rw [hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSmallChains_eq_span_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSmallChains_eq_span_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSmallChains_eq_span_basis ``Submission.DifferentialGeometry.Topology.integralSingularSmallChains_eq_span_basis

/-- Smallness is a condition on the actual nonzero coefficients of the
original chain, rather than on a chosen expression with possible cancellation. -/
theorem integralSingularSmallChains_mem_iff (n : ℕ) (U : ι → Set X)
    (c : (integralSingularChains X).X n) :
    c ∈ integralSingularSmallChains n U ↔
      ∀ σ : integralSingularSimplex n X, integralSingularChainRepr n X c σ ≠ 0 →
        ∃ i, _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ U i := by
  rw [integralSingularSmallChains_eq_span_basis, (integralSingularChainBasis n X).mem_span_image]
  change (↑(integralSingularChainRepr n X c).support : Set _) ⊆
    {σ | ∃ i, _root_.Set.range (integralSingularSimplexEquiv n X σ) ⊆ U i} ↔ _
  constructor
  · intro h σ hσ
    exact h (Finsupp.mem_support_iff.mpr hσ)
  · intro h σ hσ
    exact h σ (Finsupp.mem_support_iff.mp hσ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSmallChains_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSmallChains_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSmallChains_mem_iff ``Submission.DifferentialGeometry.Topology.integralSingularSmallChains_mem_iff

/-- The original boundary of a small chain is small for the same family. -/
theorem integralSingularSmallChains_boundary (n : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X (n + 1)} (hc : c ∈ integralSingularSmallChains (n + 1) U) :
    (integralSingularChains X).d (n + 1) n c ∈ integralSingularSmallChains n U := by
  have h : integralSingularSmallChains (n + 1) U ≤
      Submodule.comap ((integralSingularChains X).d (n + 1) n).hom
        (integralSingularSmallChains n U) := by
    apply iSup_le
    intro i b hb
    exact Submodule.mem_iSup_of_mem i (integralSingularChainsIn_boundary n (U i) hb)
  exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSmallChains_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSmallChains_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSmallChains_boundary ``Submission.DifferentialGeometry.Topology.integralSingularSmallChains_boundary

/-- In all degrees, including the shape-zero positions, the original
differential restricts to the same small chains. -/
theorem integralSingularSmallChains_d (i j : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X i} (hc : c ∈ integralSingularSmallChains i U) :
    (integralSingularChains X).d i j c ∈ integralSingularSmallChains j U := by
  by_cases h : j + 1 = i
  · subst i
    exact integralSingularSmallChains_boundary j U hc
  · rw [(integralSingularChains X).shape i j h]
    exact Submodule.zero_mem _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSmallChains_d then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSmallChains_d"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSmallChains_d ``Submission.DifferentialGeometry.Topology.integralSingularSmallChains_d

/-- Refining carriers preserves smallness of the actual chains. -/
theorem integralSingularSmallChains_refinement {κ : Type*} (n : ℕ)
    (U : ι → Set X) (V : κ → Set X) (h : ∀ i, ∃ j, U i ⊆ V j) :
    integralSingularSmallChains n U ≤ integralSingularSmallChains n V := by
  intro c hc
  rw [integralSingularSmallChains_mem_iff] at hc ⊢
  intro σ hσ
  obtain ⟨i, hi⟩ := hc σ hσ
  obtain ⟨j, hj⟩ := h i
  exact ⟨j, hi.trans hj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSmallChains_refinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSmallChains_refinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSmallChains_refinement ``Submission.DifferentialGeometry.Topology.integralSingularSmallChains_refinement

end DifferentialGeometry.Topology
