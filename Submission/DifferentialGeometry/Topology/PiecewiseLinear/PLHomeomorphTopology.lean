/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import Submission.DifferentialGeometry.Topology.InvarianceOfDomainManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPLHomeomorphOn.image_closure [FiniteDimensional ℝ E] {f : E → F} {P A : Set E} {Q : Set F}
    (hf : IsPLHomeomorphOn f P Q) (hP : IsCompact P) (hAP : A ⊆ P) :
    f '' closure A = closure (f '' A) := by
  have hcl : closure A ⊆ P := closure_minimal hAP hP.isClosed
  exact image_closure_of_isCompact (hP.of_isClosed_subset isClosed_closure hcl)
    (hf.isPiecewiseAffineOn.continuousOn.mono hcl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_closure ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_closure

theorem IsPLHomeomorphOn.image_interior_subset [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : f '' interior P ⊆ interior Q := by
  apply interior_maximal (image_subset_iff.mpr (hf.bijOn.mapsTo.mono_left interior_subset))
  exact invariance_of_domain_isOpen_image_of_finrank_eq hdim isOpen_interior
    (hf.isPiecewiseAffineOn.continuousOn.mono interior_subset) (hf.bijOn.injOn.mono interior_subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior_subset

theorem IsPLHomeomorphOn.image_interior [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : f '' interior P = interior Q := by
  apply Subset.antisymm (hf.image_interior_subset hdim)
  intro y hy
  exact ⟨Function.invFunOn f P y, hf.symm.image_interior_subset hdim.symm ⟨y, hy, rfl⟩,
    hf.bijOn.invOn_invFunOn.2 (interior_subset hy)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_interior

theorem IsPLHomeomorphOn.image_frontier [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hP : IsClosed P) (hQ : IsClosed Q) :
    f '' frontier P = frontier Q := by
  rw [frontier, hP.closure_eq, hf.bijOn.injOn.image_sdiff_subset interior_subset,
    hf.image_eq, hf.image_interior hdim, frontier, hQ.closure_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_frontier

end DifferentialGeometry.Topology.PiecewiseLinear
