import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Submission.DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Function
open scoped _root_.ContDiff _root_.NNReal

namespace DifferentialGeometry.Analysis



theorem deriv_affinePeriodic {ψ : ℝ → ℝ} (hp : ∀ t, ψ (t + 1) = ψ t + 1) :
    Periodic (deriv ψ) 1 := by
  intro t
  have h := congrArg (fun f : ℝ → ℝ => deriv f t) (funext hp)
  simpa only [deriv_comp_add_const, deriv_add_const] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_affinePeriodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_affinePeriodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_affinePeriodic ``Submission.DifferentialGeometry.Analysis.deriv_affinePeriodic



theorem exists_lipschitz_affinePeriodic {ψ : ℝ → ℝ} (hc : ContDiff ℝ 1 ψ)
    (hp : ∀ t, ψ (t + 1) = ψ t + 1) : ∃ C : ℝ≥0, LipschitzWith C ψ := by
  obtain ⟨B, hB, hb⟩ := exists_bound_of_continuous_unit_periodic
    (hc.continuous_deriv le_rfl) (deriv_affinePeriodic hp)
  refine ⟨⟨B, hB.le⟩, lipschitzWith_of_nnnorm_deriv_le (hc.differentiable one_ne_zero) ?_⟩
  intro x
  exact_mod_cast hb x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_lipschitz_affinePeriodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_lipschitz_affinePeriodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_lipschitz_affinePeriodic ``Submission.DifferentialGeometry.Analysis.exists_lipschitz_affinePeriodic

end DifferentialGeometry.Analysis

open _root_.Set

namespace Function.Periodic
open _root_.Function _root_.Function.Periodic

open _root_.Function _root_.Function.Periodic in
theorem fderiv
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {c : E} (hf : Function.Periodic f c) :
    Function.Periodic (_root_.fderiv 𝕜 f) c := by
  intro x
  rw [← fderiv_comp_add_right]
  exact congrArg (fun g : E → F => _root_.fderiv 𝕜 g x) (funext hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.Periodic.fderiv then
    throwError "Refusing to shadow existing declaration Function.Periodic.fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Periodic.fderiv ``Submission.Function.Periodic.fderiv

open _root_.Function _root_.Function.Periodic in
theorem lipschitzWith_of_norm_fderiv_le_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {c : ℝ} (hp : Function.Periodic f c) (hc : 0 < c)
    (hf : Differentiable ℝ f) {L : NNReal}
    (hbound : ∀ x ∈ _root_.Set.Icc (0 : ℝ) c, ‖_root_.fderiv ℝ f x‖ ≤ (L : ℝ)) :
    LipschitzWith L f := by
  apply lipschitzWith_of_nnnorm_fderiv_le hf
  intro x
  obtain ⟨y, hy, hxy⟩ := (hp.fderiv (𝕜 := ℝ)).exists_mem_Ico₀ hc x
  rw [hxy]
  exact_mod_cast hbound y ⟨hy.1, hy.2.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.Periodic.lipschitzWith_of_norm_fderiv_le_Icc then
    throwError "Refusing to shadow existing declaration Function.Periodic.lipschitzWith_of_norm_fderiv_le_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Periodic.lipschitzWith_of_norm_fderiv_le_Icc ``Submission.Function.Periodic.lipschitzWith_of_norm_fderiv_le_Icc

end Function.Periodic

namespace Function.Periodic
open _root_.Function _root_.Function.Periodic

open _root_.Function _root_.Function.Periodic in
theorem iteratedFDeriv
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {c : E} (hf : Function.Periodic f c) (n : ℕ) :
    Function.Periodic (_root_.iteratedFDeriv 𝕜 n f) c := by
  intro x
  rw [← iteratedFDeriv_comp_add_right n c x]
  exact congrArg (fun g : E → F => _root_.iteratedFDeriv 𝕜 n g x) (funext hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.Periodic.iteratedFDeriv then
    throwError "Refusing to shadow existing declaration Function.Periodic.iteratedFDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Periodic.iteratedFDeriv ``Submission.Function.Periodic.iteratedFDeriv

end Function.Periodic
