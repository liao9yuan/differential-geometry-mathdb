import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleLaplacian
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.LaplacianNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
theorem exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 0,
      ‖ccTensorToHs g 0 ((n : ℝ) + 2) S‖ ≤
        C * (‖ccTensorToHs g 0 (n : ℝ) S‖ +
          ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖) := by
  let A := appHs g 0 0 n (scalarCc g (laplacianPrincipalCoefficient g))
  let B := appHs g 0 0 n (scalarCc g (laplacianDriftCoefficient g))
  let D := parameterDerivativeHs g n
  refine ⟨1 + ‖A‖ * ‖D‖ + ‖B‖, by positivity, ?_⟩
  intro S
  have hD : ‖ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S))‖ ≤
      ‖D‖ * ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖ := by
    have hh := (parameterDerivativeHs g n).le_opNorm
      (ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S))
    rw [parameterDerivativeHs_apply_ccTensorToHs] at hh
    exact hh
  have hB : ‖ccTensorToHs g 0 (n : ℝ) (parameterDerivativeCcTensor g S)‖ ≤
      ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖ :=
    ccToHs_norm_mono g 0 (by linarith) _
  have hmul (a : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯) (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 (n : ℝ) (scalarSmul g 0 0 a W)‖ ≤
        ‖appHs g 0 0 n (scalarCc g a)‖ * ‖ccTensorToHs g 0 (n : ℝ) W‖ := by
    have hh := (appHs g 0 0 n (scalarCc g a)).le_opNorm
      (ccTensorToHs g 0 (n : ℝ) W)
    rw [appHs_apply_ccTensorToHs, app_scalarCc] at hh
    exact hh
  have hsub (U V : SmoothCcTensor g 0 0) :
      ccTensorToHs g 0 (n : ℝ) (U - V) = ccTensorToHs g 0 (n : ℝ) U - ccTensorToHs g 0 (n : ℝ) V :=
    (ccToHsLin g 0 (n : ℝ)).map_sub U V
  calc
    ‖ccTensorToHs g 0 ((n : ℝ) + 2) S‖ =
        ‖ccTensorToHs g 0 (n : ℝ) (oneMinusConnLapSmooth g 0 0 S)‖ := by
      exact ccTensorToHs_add_two_norm_eq_oneMinusConnLap g 0 (n : ℝ) S
    _ ≤ ‖ccTensorToHs g 0 (n : ℝ) S‖ +
        ‖ccTensorToHs g 0 (n : ℝ) (rawTensorConnLapSmooth g 0 0 S)‖ := by
      rw [oneMinusConnLapSmooth, hsub]
      exact norm_sub_le _ _
    _ ≤ ‖ccTensorToHs g 0 (n : ℝ) S‖ +
        (‖A‖ * (‖D‖ * ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖) +
          ‖B‖ * ‖ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)‖) := by
      rw [add_le_add_iff_left]
      rw [rawTensorConnLapSmooth_eq_principal_add_drift, ccTensorToHs_add]
      exact (norm_add_le _ _).trans (add_le_add
        ((hmul _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg A)))
        ((hmul _ _).trans (mul_le_mul_of_nonneg_left hB (norm_nonneg B))))
    _ ≤ _ := by
      nlinarith [norm_nonneg (ccTensorToHs g 0 (n : ℝ) S),
        norm_nonneg (ccTensorToHs g 0 ((n : ℝ) + 1) (parameterDerivativeCcTensor g S)),
        mul_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg D))
          (norm_nonneg (ccTensorToHs g 0 (n : ℝ) S)),
        mul_nonneg (norm_nonneg B) (norm_nonneg (ccTensorToHs g 0 (n : ℝ) S))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative then
    throwError "Refusing to shadow existing declaration AddCircle.exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative ``Submission.AddCircle.exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative

open _root_.AddCircle in
theorem exists_norm_ccTensorToHs_two_le_add_parameterDerivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 0,
      ‖ccTensorToHs g 0 2 S‖ ≤
        C * (‖ccTensorToHs g 0 0 S‖ +
          ‖ccTensorToHs g 0 1 (parameterDerivativeCcTensor g S)‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_ccTensorToHs_add_two_le_add_parameterDerivative g 0
  refine ⟨C, hC, fun S => ?_⟩
  have hn {a b : ℝ} (h : a = b) (W : SmoothCcTensor g 0 0) :
      ‖ccTensorToHs g 0 a W‖ = ‖ccTensorToHs g 0 b W‖ :=
    congrArg (fun t : ℝ => ‖ccTensorToHs g 0 t W‖) h
  have h := hbound S
  rw [hn (show ((0 : ℕ) : ℝ) + 2 = 2 by norm_num),
    hn (show ((0 : ℕ) : ℝ) = 0 by norm_num),
    hn (show ((0 : ℕ) : ℝ) + 1 = 1 by norm_num)] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.exists_norm_ccTensorToHs_two_le_add_parameterDerivative then
    throwError "Refusing to shadow existing declaration AddCircle.exists_norm_ccTensorToHs_two_le_add_parameterDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.exists_norm_ccTensorToHs_two_le_add_parameterDerivative ``Submission.AddCircle.exists_norm_ccTensorToHs_two_le_add_parameterDerivative

end AddCircle
