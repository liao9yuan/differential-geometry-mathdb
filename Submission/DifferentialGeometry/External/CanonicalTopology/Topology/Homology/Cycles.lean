import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Relative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Concrete cycles and boundaries of the original singular complex -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- Positive-degree cycles in the actual singular chain group. -/
abbrev integralSingularCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  LinearMap.ker ((integralSingularChains X).d (n + 1) n).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCycles ``Submission.DifferentialGeometry.Topology.integralSingularCycles

/-- Use the original kernel's scalar action explicitly, avoiding the fallback
integer action on an arbitrary additive group during elaboration. -/
instance integralSingularCyclesModule (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Module ℤ (integralSingularCycles n X) :=
  (LinearMap.ker ((integralSingularChains X).d (n + 1) n).hom).module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCyclesModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCyclesModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCyclesModule ``Submission.DifferentialGeometry.Topology.integralSingularCyclesModule

/-- The actual next boundary lands in the preceding cycles by d squared zero. -/
def integralSingularBoundaryToCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :
    (integralSingularChains X).X (n + 2) →ₗ[ℤ] integralSingularCycles n X :=
  ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatToCycles

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularBoundaryToCycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularBoundaryToCycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularBoundaryToCycles ``Submission.DifferentialGeometry.Topology.integralSingularBoundaryToCycles

/-- The original categorical homology is exactly cycles modulo actual
boundaries, with no replacement homology group. -/
def integralSingularHomologyCycleEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularHomology (n + 1) X ≃+
      (integralSingularCycles n X ⧸ LinearMap.range (integralSingularBoundaryToCycles n X)) :=
  (ShortComplex.homologyMapIso ((integralSingularChains X).isoSc'
      (n + 2) (n + 1) n (by simp) (by simp)) ≪≫
    ((integralSingularChains X).sc' (n + 2) (n + 1) n).moduleCatHomologyIso).toLinearEquiv.toAddEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyCycleEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyCycleEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyCycleEquiv ``Submission.DifferentialGeometry.Topology.integralSingularHomologyCycleEquiv

/-- Vanishing is equivalent to every actual cycle being the boundary of an
actual chain in the same original complex. This is the concrete criterion
used to construct the missing low-degree topology proofs. -/
theorem integralSingularHomology_vanishing_iff (n : ℕ) (X : Type u) [TopologicalSpace X] :
    Subsingleton (integralSingularHomology (n + 1) X) ↔
      ∀ c : (integralSingularChains X).X (n + 1),
        (integralSingularChains X).d (n + 1) n c = 0 →
          ∃ b : (integralSingularChains X).X (n + 2),
            (integralSingularChains X).d (n + 2) (n + 1) b = c := by
  rw [← ModuleCat.isZero_iff_subsingleton, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_vanishing_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_vanishing_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_vanishing_iff ``Submission.DifferentialGeometry.Topology.integralSingularHomology_vanishing_iff

end DifferentialGeometry.Topology
