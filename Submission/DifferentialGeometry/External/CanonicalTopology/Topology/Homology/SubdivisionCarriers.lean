import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SingularSubdivisionNaturality
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Subdivision and its homotopy preserve the same original carriers -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- Full singular subdivision preserves every actual subspace carrier. -/
theorem integralSingularSubdivision_mem (n : ℕ) (A : Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    integralSingularSubdivision n c ∈ integralSingularChainsIn n A := by
  rw [integralSingularChainsIn_eq_range] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  exact ⟨integralSingularSubdivision n b, (integralSingularSubdivision_map n _ b).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivision_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivision_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivision_mem ``Submission.DifferentialGeometry.Topology.integralSingularSubdivision_mem

/-- The SAME full homotopy preserves every actual subspace carrier. -/
theorem integralSingularSubdivisionHomotopy_mem (n : ℕ) (A : Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    integralSingularSubdivisionHomotopy n c ∈ integralSingularChainsIn (n + 1) A := by
  rw [integralSingularChainsIn_eq_range] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  exact ⟨integralSingularSubdivisionHomotopy n b, (integralSingularSubdivisionHomotopy_map n _ b).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_mem ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_mem

/-- Subdivision of an original small chain is small for the same family. -/
theorem integralSingularSubdivision_small (n : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularSmallChains n U) :
    integralSingularSubdivision n c ∈ integralSingularSmallChains n U := by
  have h : integralSingularSmallChains n U ≤
      Submodule.comap (integralSingularSubdivision n) (integralSingularSmallChains n U) := by
    apply iSup_le
    intro i b hb
    exact Submodule.mem_iSup_of_mem i (integralSingularSubdivision_mem n (U i) hb)
  exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivision_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivision_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivision_small ``Submission.DifferentialGeometry.Topology.integralSingularSubdivision_small

/-- The SAME homotopy on an original small chain is small for the same family. -/
theorem integralSingularSubdivisionHomotopy_small (n : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularSmallChains n U) :
    integralSingularSubdivisionHomotopy n c ∈ integralSingularSmallChains (n + 1) U := by
  have h : integralSingularSmallChains n U ≤
      Submodule.comap (integralSingularSubdivisionHomotopy n) (integralSingularSmallChains (n + 1) U) := by
    apply iSup_le
    intro i b hb
    exact Submodule.mem_iSup_of_mem i (integralSingularSubdivisionHomotopy_mem n (U i) hb)
  exact h hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_small ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_small

end DifferentialGeometry.Topology
