/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ChainSupport
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cycles
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.CategoryTheory

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

theorem exists_isCompact_support_of_mem_integralSingularChainsIn (n : ℕ) {A : Set X}
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ A ∧ c ∈ integralSingularChainsIn n K := by
  classical
  let F := (integralSingularChainRepr n X c).support
  let K := ⋃ σ ∈ F, _root_.Set.range (integralSingularSimplexEquiv n X σ)
  refine ⟨K, ?_, ?_, ?_⟩
  · exact F.finite_toSet.isCompact_biUnion fun σ _ =>
      isCompact_range (integralSingularSimplexEquiv n X σ).continuous
  · refine _root_.Set.iUnion₂_subset fun σ hσ => ?_
    exact (integralSingularChainsIn_mem_iff n A c).mp hc σ (Finsupp.mem_support_iff.mp hσ)
  · apply (integralSingularChainsIn_mem_iff n K c).mpr
    intro σ hσ
    exact _root_.Set.subset_iUnion₂_of_subset σ (Finsupp.mem_support_iff.mpr hσ) Subset.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_isCompact_support_of_mem_integralSingularChainsIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_isCompact_support_of_mem_integralSingularChainsIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_isCompact_support_of_mem_integralSingularChainsIn ``Submission.DifferentialGeometry.Topology.exists_isCompact_support_of_mem_integralSingularChainsIn

theorem subsingleton_integralSingularHomology_of_compact_carriers (n : ℕ) {A : Set X}
    (h : ∀ K : Set X, IsCompact K → K ⊆ A →
      ∃ B : Set X, K ⊆ B ∧ B ⊆ A ∧ Subsingleton (integralSingularHomology (n + 1) B)) :
    Subsingleton (integralSingularHomology (n + 1) A) := by
  apply (integralSingularHomology_vanishing_iff n A).mpr
  intro c hc
  let iA := singularSubspaceInclusion A
  let z := (integralSingularChainMap iA).f (n + 1) c
  have hz : z ∈ integralSingularChainsIn (n + 1) A := by
    rw [integralSingularChainsIn_eq_range]
    exact ⟨c, rfl⟩
  obtain ⟨K, hK, hKA, hzK⟩ := exists_isCompact_support_of_mem_integralSingularChainsIn (n + 1) hz
  obtain ⟨B, hKB, hBA, hB⟩ := h K hK hKA
  have hzB := integralSingularChainsIn_mono (n + 1) hKB hzK
  rw [integralSingularChainsIn_eq_range] at hzB
  obtain ⟨d, hd⟩ := hzB
  have hdc : (integralSingularChains B).d (n + 1) n d = 0 := by
    apply integralSingularChainInclusion_injective n B
    rw [integralSingularChainMap_boundary, hd]
    change (integralSingularChains X).d (n + 1) n
      ((integralSingularChainMap iA).f (n + 1) c) = _
    rw [← integralSingularChainMap_boundary, hc, map_zero, map_zero]
  obtain ⟨b, hb⟩ := (integralSingularHomology_vanishing_iff n B).mp hB d hdc
  let j : C(B, A) := ⟨inclusion hBA, continuous_inclusion hBA⟩
  refine ⟨(integralSingularChainMap j).f (n + 2) b, ?_⟩
  rw [← integralSingularChainMap_boundary, hb]
  apply integralSingularChainInclusion_injective (n + 1) A
  have hcomp := congrArg
    (fun f : integralSingularChains B ⟶ integralSingularChains X => f.f (n + 1) d)
    (integralSingularChainMap_comp j iA)
  exact hcomp.symm.trans hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_compact_carriers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_compact_carriers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_compact_carriers ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_of_compact_carriers

end DifferentialGeometry.Topology
