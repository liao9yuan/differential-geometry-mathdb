import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
theorem parameterDerivativeHs_comp_parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    (parameterDerivativeHs g n).comp
        ((tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)).comp
            (parameterSecondDerivativeHs g (n + 1))) =
      (parameterSecondDerivativeHs g n).comp
        ((tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num)).comp
            ((parameterDerivativeHs g (n + 2)).comp
              (tensorHsInclusion (g := g) (r := 0) (s := 0)
                (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by
                  push_cast
                  linarith)))) := by
  apply DFunLike.coe_injective
  apply (ccToHsLin_dense g 0 (by positivity :
    (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 2)).equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext S
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
  rw [parameterSecondDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterSecondDerivativeHs_apply_ccTensorToHs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHs_comp_parameterSecondDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHs_comp_parameterSecondDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHs_comp_parameterSecondDerivativeHs ``Submission.AddCircle.parameterDerivativeHs_comp_parameterSecondDerivativeHs

open _root_.AddCircle in
theorem parameterDerivativeHs_parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : TensorHs g 0 0 (((n + 1 : ℕ) : ℝ) + 2)) :
    parameterDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)
          (parameterSecondDerivativeHs g (n + 1) u)) =
      parameterSecondDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num)
          (parameterDerivativeHs g (n + 2)
            (tensorHsInclusion
              (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by
                push_cast
                linarith) u))) :=
  DFunLike.congr_fun (parameterDerivativeHs_comp_parameterSecondDerivativeHs g n) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHs_parameterSecondDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHs_parameterSecondDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHs_parameterSecondDerivativeHs ``Submission.AddCircle.parameterDerivativeHs_parameterSecondDerivativeHs

open _root_.AddCircle in
theorem parameterDerivativeHsPi_comp_parameterSecondDerivativeHsPi
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    (parameterDerivativeHsPi (ι := ι) g n).comp
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num))).comp
              (parameterSecondDerivativeHsPi g (n + 1))) =
      (parameterSecondDerivativeHsPi g n).comp
        ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ) by norm_num))).comp
              ((parameterDerivativeHsPi g (n + 2)).comp
                (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                  tensorHsInclusion (g := g) (r := 0) (s := 0)
                    (show ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2 by
                      push_cast
                      linarith))))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact parameterDerivativeHs_parameterSecondDerivativeHs g n (u i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHsPi_comp_parameterSecondDerivativeHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHsPi_comp_parameterSecondDerivativeHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHsPi_comp_parameterSecondDerivativeHsPi ``Submission.AddCircle.parameterDerivativeHsPi_comp_parameterSecondDerivativeHsPi

end AddCircle
