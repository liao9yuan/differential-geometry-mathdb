import Submission.DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.OpenPartialHomeomorph in
theorem fderiv_comp_symm_eq_id
    (e : OpenPartialHomeomorph E F) {z : F} (hz : z ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm z)) (hi : DifferentiableAt ℝ e.symm z) :
    (fderiv ℝ e (e.symm z)).comp (fderiv ℝ e.symm z) = ContinuousLinearMap.id ℝ F := by
  have hh := (he.hasFDerivAt.comp z hi.hasFDerivAt).fderiv
  have heq : (fun w => e (e.symm w)) =ᶠ[𝓝 z] id := e.eventually_right_inverse hz
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (fun w => e (e.symm w)) z = _ at hh
  rw [hh] at hd
  exact hd.trans fderiv_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.fderiv_comp_symm_eq_id then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.fderiv_comp_symm_eq_id"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.fderiv_comp_symm_eq_id ``Submission.OpenPartialHomeomorph.fderiv_comp_symm_eq_id

open _root_.OpenPartialHomeomorph in
theorem fderiv_ne_zero_of_differentiable_symm [Nontrivial F]
    (e : OpenPartialHomeomorph E F) {z : F} (hz : z ∈ e.target)
    (he : DifferentiableAt ℝ e (e.symm z)) (hi : DifferentiableAt ℝ e.symm z) :
    fderiv ℝ e (e.symm z) ≠ 0 := by
  intro hzero
  have hh := e.fderiv_comp_symm_eq_id hz he hi
  rw [hzero, ContinuousLinearMap.zero_comp] at hh
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  have hc := congrArg (fun L : F →L[ℝ] F => L v) hh
  exact hv hc.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.fderiv_ne_zero_of_differentiable_symm then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.fderiv_ne_zero_of_differentiable_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.fderiv_ne_zero_of_differentiable_symm ``Submission.OpenPartialHomeomorph.fderiv_ne_zero_of_differentiable_symm

end OpenPartialHomeomorph

end

end
