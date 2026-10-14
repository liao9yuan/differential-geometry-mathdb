import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extChartAt_opens_target (U : TopologicalSpace.Opens F) (α : U) :
    (extChartAt 𝓘(ℝ, F) α).target = (U : Set F) := by
  change Set.univ ∩ ((OpenPartialHomeomorph.refl F).subtypeRestr (s := U) ⟨α⟩).target = U
  rw [Set.univ_inter]
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_refl,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.extChartAt_opens_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.extChartAt_opens_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.extChartAt_opens_target ``Submission.DifferentialGeometry.extChartAt_opens_target

theorem interior_extChartAt_opens_target (U : TopologicalSpace.Opens F) (α : U) :
    interior (extChartAt 𝓘(ℝ, F) α).target = (U : Set F) := by
  rw [extChartAt_opens_target, U.isOpen.interior_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.interior_extChartAt_opens_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.interior_extChartAt_opens_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.interior_extChartAt_opens_target ``Submission.DifferentialGeometry.interior_extChartAt_opens_target

end DifferentialGeometry
