/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

theorem isOpen_setOf_isLocalDiffeomorphAt
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G) (n : WithTop ℕ∞) (f : M → N) :
    IsOpen {x | IsLocalDiffeomorphAt I J n f x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨φ, hx, hφ⟩
  exact Filter.mem_of_superset (φ.open_source.mem_nhds hx) (fun y hy => ⟨φ, hy, hφ⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `isOpen_setOf_isLocalDiffeomorphAt then
    throwError "Refusing to shadow existing declaration isOpen_setOf_isLocalDiffeomorphAt"
  Lean.modifyEnv fun env => Lean.addAlias env `isOpen_setOf_isLocalDiffeomorphAt ``Submission.isOpen_setOf_isLocalDiffeomorphAt
