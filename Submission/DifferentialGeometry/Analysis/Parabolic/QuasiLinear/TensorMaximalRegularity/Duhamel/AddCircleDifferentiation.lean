import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.LinearTransport
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

variable {ι : Type*} [Fintype ι]

def parameterDerivativeDuhamelForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
    let D := (AddCircle.parameterDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))))
    let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let L₁ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 1 : ℕ) : ℝ))
    let L₀ := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
    D.compLpL 2 (timeMeasure T) F +
      (D.comp L₁ - L₀.comp Dh).compLpL 2 (timeMeasure T) U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeDuhamelForcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeDuhamelForcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeDuhamelForcing ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivativeDuhamelForcing

theorem parameterDerivative_duhamel_vector_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 1 : ℕ) : ℝ))) T) :
    let D := (AddCircle.parameterDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ))))
    let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      ((AddCircle.parameterDerivativeHsPi (ι := ι) g (n + 2)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
          (g := g) (r := 0) (s := 0)
            (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2))))
    let U := maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0)
      (a := ((n + 1 : ℕ) : ℝ)) hT 0 F
    let G := parameterDerivativeDuhamelForcing g n hT F
    Dh.compLpL 2 (timeMeasure T) U =
        maximalRegularityDuhamelVectorField (g := g) (r := 0) (s := 0) (a := n) hT 0 G ∧
      (maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0) (a := n) hT 0 G).initial = 0 ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0) (a := n) hT 0 G).toFun t =
          D ((maximalRegularityDuhamelVectorMap (g := g) (r := 0) (s := 0)
            (a := ((n + 1 : ℕ) : ℝ)) hT 0 F).toFun t) := by
  intro D Dh U G
  have hc := DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) g 0 0
  exact duhamel_vector_comp_zero_eq (ι := ι) (E := ℝ) (H := ℝ)
    (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ)) (g := g) (r := 0) (s := 0)
    (a := n) (b := ((n + 1 : ℕ) : ℝ)) hT hc D Dh (by
      apply ContinuousLinearMap.ext
      intro f
      apply PiLp.ext
      intro i
      simp only [D, Dh, ContinuousLinearMap.comp_apply, ContinuousLinearMap.piLpMap_apply,
        AddCircle.parameterDerivativeHsPi_apply]
      rw [← tensorHsInclusion_trans_apply, ← tensorHsInclusion_trans_apply]
      have hi := AddCircle.parameterDerivativeHs_tensorHsInclusion g
        (show n ≤ n + 2 by omega)
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by push_cast; linarith : ((n + 2 : ℕ) : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 2) (f i))
      rw [← tensorHsInclusion_trans_apply] at hi
      exact hi.symm) F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivative_duhamel_vector_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivative_duhamel_vector_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivative_duhamel_vector_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterDerivative_duhamel_vector_eq


section
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

def parameterSecondDerivativeDuhamelForcing
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 : ℕ) : ℝ))) T) :
    timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) T :=
  let D := (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n).comp
    (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))))
  let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
    (g := g) (r := 0) (s := 0)
      (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
    (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (n + 2))
  let U := maximalRegularityDuhamelVectorField hT 0 F
  let Lh := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) ((n + 2 : ℕ) : ℝ))
  let Ll := ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ))
  D.compLpL 2 (timeMeasure T) F + (D.comp Lh - Ll.comp Dh).compLpL 2 (timeMeasure T) U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivativeDuhamelForcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivativeDuhamelForcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivativeDuhamelForcing ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivativeDuhamelForcing

theorem parameterSecondDerivative_duhamel_vector_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    {T : ℝ} (hT : 0 < T)
    (F : timeL2 (PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n + 2 : ℕ) : ℝ))) T) :
    let D := (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g n).comp
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (g := g) (r := 0) (s := 0)
          (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ))))
    let Dh := (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (g := g) (r := 0) (s := 0)
        (by push_cast; rfl : (n : ℝ) + 2 ≤ ((n + 2 : ℕ) : ℝ)))).comp
      (AddCircle.parameterSecondDerivativeHsPi (ι := ι) g (n + 2))
    let U := maximalRegularityDuhamelVectorField hT 0 F
    let G := parameterSecondDerivativeDuhamelForcing g n hT F
    Dh.compLpL 2 (timeMeasure T) U = maximalRegularityDuhamelVectorField hT 0 G ∧
      (maximalRegularityDuhamelVectorMap hT 0 G).initial = 0 ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
        (maximalRegularityDuhamelVectorMap hT 0 G).toFun t =
          D ((maximalRegularityDuhamelVectorMap hT 0 F).toFun t) := by
  intro D Dh U G
  apply duhamel_vector_comp_zero_eq hT (tensorResolventL2_isCompactOperator g 0 0) D Dh
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  simp only [D, Dh, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.piLpMap_apply, AddCircle.parameterSecondDerivativeHsPi_apply]
  rw [← tensorHsInclusion_trans_apply]
  have hi := AddCircle.parameterSecondDerivativeHs_tensorHsInclusion g
    (show n ≤ n + 2 by omega) (u i)
  rw [← tensorHsInclusion_trans_apply]
  exact hi.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivative_duhamel_vector_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivative_duhamel_vector_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivative_duhamel_vector_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.parameterSecondDerivative_duhamel_vector_eq

end

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
