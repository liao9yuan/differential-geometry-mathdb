import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def openSubtypePartialDiffeomorph (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M ∞ where
  toPartialEquiv := (U.openPartialHomeomorphSubtypeCoe hU).toPartialEquiv
  open_source := (U.openPartialHomeomorphSubtypeCoe hU).open_source
  open_target := (U.openPartialHomeomorphSubtypeCoe hU).open_target
  contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff U _ x).mp
    have htarget : x ∈ U := by
      simpa only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using! hx
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds htarget] with y hy
    exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv (by
      simpa only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ``Submission.DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph

@[simp]
theorem openSubtypePartialDiffeomorph_apply (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) (x : U) : openSubtypePartialDiffeomorph I U hU x = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_apply ``Submission.DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_apply

@[simp]
theorem openSubtypePartialDiffeomorph_source (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) : (openSubtypePartialDiffeomorph I U hU).source = univ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source ``Submission.DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source

@[simp]
theorem openSubtypePartialDiffeomorph_target (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) : (openSubtypePartialDiffeomorph I U hU).target = U :=
  U.openPartialHomeomorphSubtypeCoe_target hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target ``Submission.DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target

theorem openSubtypePartialDiffeomorph_symm_apply (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) {x : M} (hx : x ∈ U) :
    (openSubtypePartialDiffeomorph I U hU).symm x = ⟨x, hx⟩ := by
  apply Subtype.ext
  exact (openSubtypePartialDiffeomorph I U hU).right_inv (by simpa using hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply

end DifferentialGeometry.Manifold
