/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.FieldPathCones

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

variable {k X : Type} [Field k] [TopologicalSpace X]

noncomputable abbrev fieldSingularCycles (n : ℕ) :=
  LinearMap.ker ((fieldSingularChains (k := k) (X := X)).d (n + 1) n).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularCycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularCycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularCycles ``Submission.DifferentialGeometry.Topology.fieldSingularCycles

noncomputable def fieldSingularBoundaryToCycles (n : ℕ) :
    (fieldSingularChains (k := k) (X := X)).X (n + 2) →ₗ[k]
      fieldSingularCycles (k := k) (X := X) n :=
  ((fieldSingularChains (k := k) (X := X)).sc' (n + 2) (n + 1) n).moduleCatToCycles

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularBoundaryToCycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularBoundaryToCycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularBoundaryToCycles ``Submission.DifferentialGeometry.Topology.fieldSingularBoundaryToCycles

noncomputable def fieldSingularHomologyCycleEquiv (n : ℕ) :
    (fieldSingularChains (k := k) (X := X)).homology (n + 1) ≃ₗ[k]
      (fieldSingularCycles (k := k) (X := X) n ⧸
        LinearMap.range (fieldSingularBoundaryToCycles (k := k) (X := X) n)) :=
  (CategoryTheory.ShortComplex.homologyMapIso
      ((fieldSingularChains (k := k) (X := X)).isoSc'
        (n + 2) (n + 1) n (by simp) (by simp)) ≪≫
    ((fieldSingularChains (k := k) (X := X)).sc'
      (n + 2) (n + 1) n).moduleCatHomologyIso).toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fieldSingularHomologyCycleEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fieldSingularHomologyCycleEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fieldSingularHomologyCycleEquiv ``Submission.DifferentialGeometry.Topology.fieldSingularHomologyCycleEquiv

end DifferentialGeometry.Topology
