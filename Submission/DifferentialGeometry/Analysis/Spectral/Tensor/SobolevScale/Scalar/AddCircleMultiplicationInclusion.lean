import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.H0MultiplicationInclusion
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

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
theorem tensorHsInclusion_scalarHsMul_parameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 1)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    J (scalarHsMul g 1 (by norm_num) a (parameterDerivativeHs g 1 u)) =
      scalarH0ContinuousMul g (C a) (Z (parameterDerivativeHs g 0
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 1) u))) := by
  intro J C Z
  rw [tensorHsInclusion_scalarHsMul_zero, parameterDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorHsInclusion_scalarHsMul_parameterDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.tensorHsInclusion_scalarHsMul_parameterDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorHsInclusion_scalarHsMul_parameterDerivativeHs ``Submission.AddCircle.tensorHsInclusion_scalarHsMul_parameterDerivativeHs

open _root_.AddCircle in
theorem tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (a : TensorHs g 0 0 ((1 : ℕ) : ℝ))
    (u : TensorHs g 0 0 (((1 : ℕ) : ℝ) + 2)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    let C := (scalarH1ToContinuous g).comp (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)))
    let Z := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    J (scalarHsMul g 1 (by norm_num) a (parameterSecondDerivativeHs g 1 u)) =
      scalarH0ContinuousMul g (C a) (Z (parameterSecondDerivativeHs g 0
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : ((0 : ℕ) : ℝ) + 2 ≤ ((1 : ℕ) : ℝ) + 2) u))) := by
  intro J C Z
  rw [tensorHsInclusion_scalarHsMul_zero, parameterSecondDerivativeHs_tensorHsInclusion g (by omega : 0 ≤ 1)]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs ``Submission.AddCircle.tensorHsInclusion_scalarHsMul_parameterSecondDerivativeHs

end AddCircle
