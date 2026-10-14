import Submission.DifferentialGeometry.Topology.Embedding.CylinderCap
import Submission.DifferentialGeometry.Topology.Morse.CriticalPoints

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.Morse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isCriticalPointAt_cylinderCap_snd_iff {a : ℝ} (ha : a ≠ 0) (x : E) :
    IsCriticalPointAt 𝓘(ℝ, E) (fun y : E => (EuclideanGeometry.cylinderCap a y).2) x ↔ x = 0 := by
  rw [IsCriticalPointAt, mfderiv_eq_fderiv]
  exact EuclideanGeometry.fderiv_cylinderCap_snd_eq_zero_iff ha x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.isCriticalPointAt_cylinderCap_snd_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.isCriticalPointAt_cylinderCap_snd_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.isCriticalPointAt_cylinderCap_snd_iff ``Submission.DifferentialGeometry.Topology.Morse.isCriticalPointAt_cylinderCap_snd_iff

theorem isNondegenerateCriticalPointAt_cylinderCap_snd {a : ℝ} (ha : a ≠ 0) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E)
      (fun y : E => (EuclideanGeometry.cylinderCap a y).2) 0 := by
  have hf : ContDiff ℝ 2 (fun y : E => (EuclideanGeometry.cylinderCap a y).2) :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)
  apply (isNondegenerateCriticalPointAt_model_iff hf.contDiffAt).mpr
  refine ⟨(EuclideanGeometry.fderiv_cylinderCap_snd_eq_zero_iff ha 0).mpr rfl, ?_⟩
  rw [EuclideanGeometry.fderiv_fderiv_cylinderCap_snd]
  intro x y h
  have he : innerSL ℝ x = innerSL ℝ y :=
    (smul_right_injective (E →L[ℝ] ℝ) (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha)) h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← innerSL_apply_norm ℝ, map_sub, he, sub_self, norm_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.isNondegenerateCriticalPointAt_cylinderCap_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.isNondegenerateCriticalPointAt_cylinderCap_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.isNondegenerateCriticalPointAt_cylinderCap_snd ``Submission.DifferentialGeometry.Topology.Morse.isNondegenerateCriticalPointAt_cylinderCap_snd

end DifferentialGeometry.Topology.Morse
