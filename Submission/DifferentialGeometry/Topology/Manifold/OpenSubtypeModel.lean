import Submission.DifferentialGeometry.Topology.Manifold.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem extChartAt_opens_apply (U : TopologicalSpace.Opens E) (a x : U) :
    extChartAt 𝓘(ℝ, E) a x = (x : E) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.extChartAt_opens_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.extChartAt_opens_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.extChartAt_opens_apply ``Submission.DifferentialGeometry.extChartAt_opens_apply

theorem extChartAt_opens_source (U : TopologicalSpace.Opens E) (a : U) :
    (extChartAt 𝓘(ℝ, E) a).source = Set.univ := by
  simp only [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source,
    Set.preimage_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.extChartAt_opens_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.extChartAt_opens_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.extChartAt_opens_source ``Submission.DifferentialGeometry.extChartAt_opens_source

theorem extChartAt_opens_target (U : TopologicalSpace.Opens E) (a : U) :
    (extChartAt 𝓘(ℝ, E) a).target = (U : Set E) := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_def, chartAt_self_eq, mfld_simps]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.extChartAt_opens_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.extChartAt_opens_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.extChartAt_opens_target ``Submission.DifferentialGeometry.extChartAt_opens_target

theorem extChartAt_opens_symm_apply (U : TopologicalSpace.Opens E) (a x : U) :
    (extChartAt 𝓘(ℝ, E) a).symm (x : E) = x :=
  (extChartAt 𝓘(ℝ, E) a).left_inv (by rw [extChartAt_opens_source]; trivial)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.extChartAt_opens_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.extChartAt_opens_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.extChartAt_opens_symm_apply ``Submission.DifferentialGeometry.extChartAt_opens_symm_apply

theorem mem_interior_extChartAt_opens_target (U : TopologicalSpace.Opens E) (a x : U) :
    (x : E) ∈ interior (extChartAt 𝓘(ℝ, E) a).target := by
  rw [extChartAt_opens_target, U.isOpen.interior_eq]
  exact x.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mem_interior_extChartAt_opens_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mem_interior_extChartAt_opens_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mem_interior_extChartAt_opens_target ``Submission.DifferentialGeometry.mem_interior_extChartAt_opens_target

theorem continuousLinearMapAt_opens_model (U : TopologicalSpace.Opens E) (a x : U) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).continuousLinearMapAt ℝ x =
      ContinuousLinearMap.id ℝ E := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
      chartAt_self_eq]
    trivial)]
  exact mfderiv_subtype_val U x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.continuousLinearMapAt_opens_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.continuousLinearMapAt_opens_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.continuousLinearMapAt_opens_model ``Submission.DifferentialGeometry.continuousLinearMapAt_opens_model

theorem symmL_opens_model (U : TopologicalSpace.Opens E) (a x : U) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).symmL ℝ x =
      ContinuousLinearMap.id ℝ E := by
  ext v
  have hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq]
    trivial
  have h := (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).symmL_continuousLinearMapAt (R := ℝ) hx v
  rw [continuousLinearMapAt_opens_model] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.symmL_opens_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.symmL_opens_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.symmL_opens_model ``Submission.DifferentialGeometry.symmL_opens_model

end DifferentialGeometry
