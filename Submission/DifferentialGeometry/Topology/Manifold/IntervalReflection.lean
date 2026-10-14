import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Algebra.LieGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

def unitIntervalReflection : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) unitInterval unitInterval ∞ where
  toEquiv := unitInterval.symmHomeomorph.toEquiv
  contMDiff_toFun := by
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    exact ⟨unitInterval.continuous_symm, contMDiff_const.sub contMDiff_subtypeVal_Icc⟩
  contMDiff_invFun := by
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    exact ⟨unitInterval.continuous_symm, contMDiff_const.sub contMDiff_subtypeVal_Icc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.unitIntervalReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.unitIntervalReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.unitIntervalReflection ``Submission.DifferentialGeometry.Topology.Manifold.unitIntervalReflection

@[simp] theorem unitIntervalReflection_apply (t : unitInterval) :
    unitIntervalReflection t = unitInterval.symm t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.unitIntervalReflection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.unitIntervalReflection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.unitIntervalReflection_apply ``Submission.DifferentialGeometry.Topology.Manifold.unitIntervalReflection_apply

@[simp] theorem unitIntervalReflection_symm_apply (t : unitInterval) :
    unitIntervalReflection.symm t = unitInterval.symm t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.unitIntervalReflection_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.unitIntervalReflection_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.unitIntervalReflection_symm_apply ``Submission.DifferentialGeometry.Topology.Manifold.unitIntervalReflection_symm_apply

end DifferentialGeometry.Topology.Manifold
