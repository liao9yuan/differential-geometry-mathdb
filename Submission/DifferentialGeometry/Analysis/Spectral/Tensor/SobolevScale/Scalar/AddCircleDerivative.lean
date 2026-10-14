import Submission.DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ScalarEvaluation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Application.IteratedCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.Application
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import Submission.DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

open _root_.AddCircle in
def parameterTangentSection :
    ContMDiffSection 𝓘(ℝ, ℝ) ℝ ∞ (TangentSpace 𝓘(ℝ, ℝ) : AddCircle (1 : ℝ) → Type _) where
  toFun := parameterTangent
  contMDiff_toFun := contMDiff_parameterTangent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangentSection then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangentSection"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangentSection ``Submission.AddCircle.parameterTangentSection

open _root_.AddCircle in
theorem parameterTangentSection_apply (z : AddCircle (1 : ℝ)) :
    parameterTangentSection z = parameterTangent z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangentSection_apply then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangentSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangentSection_apply ``Submission.AddCircle.parameterTangentSection_apply

open _root_.AddCircle in
def parameterTangentCcTensor (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) :
    SmoothCcTensor g 1 0 :=
  covectorEvaluationCcTensor g parameterTangentSection

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangentCcTensor then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangentCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangentCcTensor ``Submission.AddCircle.parameterTangentCcTensor

open _root_.AddCircle in
theorem parameterTangentCcTensor_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (z : AddCircle (1 : ℝ)) (α : Tensor0SSpace 1 𝓘(ℝ, ℝ) z)
    (w : Fin 0 → TangentSpace 𝓘(ℝ, ℝ) z) :
    (parameterTangentCcTensor g).toSection z α w = α (fun _ => parameterTangent z) := by
  change interiorProduct 0 z (parameterTangent z) α w = _
  rw [interior_product_apply]
  congr 1
  funext i
  fin_cases i
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterTangentCcTensor_apply then
    throwError "Refusing to shadow existing declaration AddCircle.parameterTangentCcTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterTangentCcTensor_apply ``Submission.AddCircle.parameterTangentCcTensor_apply


end AddCircle

end

end

section

noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open _root_.AddCircle in
def parameterDerivativeCcTensor
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) : SmoothCcTensor g 0 0 :=
  operatorFieldApply g 1 0 (parameterTangentCcTensor g) (covGrad g 0 0 S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeCcTensor then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeCcTensor ``Submission.AddCircle.parameterDerivativeCcTensor

open _root_.AddCircle in
theorem scalar0_parameterDerivativeCcTensor
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) (z : AddCircle (1 : ℝ)) :
    TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection z =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (TensorRSField.scalar0 S.toSection) z (parameterTangent z) := by
  exact scalar0_covectorEvaluationCcTensor_covGrad g parameterTangentSection S z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.scalar0_parameterDerivativeCcTensor then
    throwError "Refusing to shadow existing declaration AddCircle.scalar0_parameterDerivativeCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.scalar0_parameterDerivativeCcTensor ``Submission.AddCircle.scalar0_parameterDerivativeCcTensor

open _root_.AddCircle in
theorem scalar0_parameterDerivativeCcTensor_coe
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) (x : ℝ) :
    TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection (x : AddCircle (1 : ℝ)) =
      deriv (fun t : ℝ => TensorRSField.scalar0 S.toSection (t : AddCircle (1 : ℝ))) x := by
  rw [scalar0_parameterDerivativeCcTensor]
  exact (deriv_comp_coe (TensorRSField.scalar0_smooth S.toSection |>.mdifferentiableAt (by decide))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.scalar0_parameterDerivativeCcTensor_coe then
    throwError "Refusing to shadow existing declaration AddCircle.scalar0_parameterDerivativeCcTensor_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.scalar0_parameterDerivativeCcTensor_coe ``Submission.AddCircle.scalar0_parameterDerivativeCcTensor_coe

end AddCircle

end

end

section

noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.AddCircle in
theorem scalar0_parameterDerivativeCcTensor_twice_coe
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) (x : ℝ) :
    TensorRSField.scalar0
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)).toSection
        (x : AddCircle (1 : ℝ)) =
      deriv (deriv (fun t : ℝ => TensorRSField.scalar0 S.toSection (t : AddCircle (1 : ℝ)))) x := by
  rw [scalar0_parameterDerivativeCcTensor_coe]
  congr 1
  funext t
  exact scalar0_parameterDerivativeCcTensor_coe g S t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.scalar0_parameterDerivativeCcTensor_twice_coe then
    throwError "Refusing to shadow existing declaration AddCircle.scalar0_parameterDerivativeCcTensor_twice_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.scalar0_parameterDerivativeCcTensor_twice_coe ``Submission.AddCircle.scalar0_parameterDerivativeCcTensor_twice_coe

end AddCircle

end

end

section

noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation (TensorHs)

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
def parameterDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 1) →L[ℝ] TensorHs g 0 0 (n : ℝ) :=
  (appHs g 1 0 n (parameterTangentCcTensor g)).comp
    ((iterCovGradHs g 0 1 n).comp
      (TensorHs.castEquiv (g := g) (r := 0) (s := 0)
        (by norm_num : (n : ℝ) + 1 = (n : ℝ) + ((1 : ℕ) : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHs ``Submission.AddCircle.parameterDerivativeHs

open _root_.AddCircle in
theorem parameterDerivativeHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : SmoothCcTensor g 0 0) :
    parameterDerivativeHs g n (ccTensorToHs g 0 ((n : ℝ) + 1) W) =
      ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g W) := by
  have hcast :
      (TensorHs.castEquiv (g := g) (r := 0) (s := 0)
        (by norm_num : (n : ℝ) + 1 = (n : ℝ) + ((1 : ℕ) : ℝ)))
        (ccTensorToHs g 0 ((n : ℝ) + 1) W) =
      ccTensorToHs g 0 ((n : ℝ) + ((1 : ℕ) : ℝ)) W := by
    apply TensorHs.ext
    funext i
    simp only [TensorHs.castEquiv_coeff, ccTensorToHs_coeff]
  change (appHs g 1 0 n (parameterTangentCcTensor g))
    ((iterCovGradHs g 0 1 n)
      ((TensorHs.castEquiv (g := g) (r := 0) (s := 0)
        (by norm_num : (n : ℝ) + 1 = (n : ℝ) + ((1 : ℕ) : ℝ)))
        (ccTensorToHs g 0 ((n : ℝ) + 1) W))) = _
  rw [hcast, iterCovGradHs_apply_ccTensorToHs, appHs_apply_ccTensorToHs]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHs_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHs_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHs_apply_ccTensorToHs ``Submission.AddCircle.parameterDerivativeHs_apply_ccTensorToHs

end AddCircle

end

end

section

open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 target :: scope.openDecls } }

open _root_.AddCircle in
theorem parameterDerivativeHs_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterDerivativeHs g n).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1)) =
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp
          (parameterDerivativeHs g m) := by
  let L := (parameterDerivativeHs g n).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1))
  let R := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp (parameterDerivativeHs g m)
  have heq : (L : _ → _) = R := (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ (m : ℝ) + 1)).equalizer L.continuous R.continuous (by
    funext S
    simp only [Function.comp_apply, L, R, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
    rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
      parameterDerivativeHs_apply_ccTensorToHs, tensorHsInclusion_ccTensorToHs])
  exact DFunLike.coe_injective heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHs_comp_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHs_comp_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHs_comp_tensorHsInclusion ``Submission.AddCircle.parameterDerivativeHs_comp_tensorHsInclusion

open _root_.AddCircle in
theorem parameterDerivativeHs_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) (u : TensorHs g 0 0 ((m : ℝ) + 1)) :
    parameterDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by
          exact_mod_cast Nat.add_le_add_right h 1) u) =
      tensorHsInclusion (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)
        (parameterDerivativeHs g m u) :=
  DFunLike.congr_fun (parameterDerivativeHs_comp_tensorHsInclusion g h) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHs_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHs_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHs_tensorHsInclusion ``Submission.AddCircle.parameterDerivativeHs_tensorHsInclusion

end AddCircle

end

section

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2 target :: scope.openDecls } }

variable {ι : Type*}

open _root_.AddCircle in
def parameterDerivativeHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) :=
  ContinuousLinearMap.piLpMap 2 (fun _ => parameterDerivativeHs g n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHsPi ``Submission.AddCircle.parameterDerivativeHsPi

open _root_.AddCircle in
@[simp] theorem parameterDerivativeHsPi_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 1))) (i : ι) :
    parameterDerivativeHsPi g n u i = parameterDerivativeHs g n (u i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHsPi_apply then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHsPi_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHsPi_apply ``Submission.AddCircle.parameterDerivativeHsPi_apply

open _root_.AddCircle in
theorem parameterDerivativeHsPi_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : ι → SmoothCcTensor g 0 0) :
    parameterDerivativeHsPi g n
        (WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((n : ℝ) + 1) (W i))) =
      WithLp.toLp 2 (fun i => ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (W i))) := by
  apply PiLp.ext
  intro i
  exact parameterDerivativeHs_apply_ccTensorToHs g n (W i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHsPi_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHsPi_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHsPi_apply_ccTensorToHs ``Submission.AddCircle.parameterDerivativeHsPi_apply_ccTensorToHs

open _root_.AddCircle in
theorem norm_parameterDerivativeHsPi_le [Fintype ι]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ‖parameterDerivativeHsPi (ι := ι) g n‖ ≤ ‖parameterDerivativeHs g n‖ := by
  exact ContinuousLinearMap.norm_piLpMap_le (fun _ : ι => parameterDerivativeHs g n)
    (norm_nonneg _) (fun _ => le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.norm_parameterDerivativeHsPi_le then
    throwError "Refusing to shadow existing declaration AddCircle.norm_parameterDerivativeHsPi_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.norm_parameterDerivativeHsPi_le ``Submission.AddCircle.norm_parameterDerivativeHsPi_le

open _root_.AddCircle in
def parameterSecondDerivativeHsPi
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) :=
  (parameterDerivativeHsPi g n).comp
    ((ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num))).comp
      ((parameterDerivativeHsPi g (n + 1)).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2 by push_cast; linarith)))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHsPi then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHsPi"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHsPi ``Submission.AddCircle.parameterSecondDerivativeHsPi

open _root_.AddCircle in
theorem parameterSecondDerivativeHsPi_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : ι → SmoothCcTensor g 0 0) :
    parameterSecondDerivativeHsPi g n
        (WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((n : ℝ) + 2) (W i))) =
      WithLp.toLp 2 (fun i => ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g (W i)))) := by
  apply PiLp.ext
  intro i
  simp only [parameterSecondDerivativeHsPi, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.piLpMap_apply, parameterDerivativeHsPi_apply]
  rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHsPi_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHsPi_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHsPi_apply_ccTensorToHs ``Submission.AddCircle.parameterSecondDerivativeHsPi_apply_ccTensorToHs

open _root_.AddCircle in
theorem parameterDerivativeHsPi_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterDerivativeHsPi (ι := ι) g n).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (m : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right h 1))) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h))).comp
            (parameterDerivativeHsPi g m) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact parameterDerivativeHs_tensorHsInclusion g h (u i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterDerivativeHsPi_comp_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.parameterDerivativeHsPi_comp_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterDerivativeHsPi_comp_tensorHsInclusion ``Submission.AddCircle.parameterDerivativeHsPi_comp_tensorHsInclusion

end AddCircle

end

end


noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3 target :: scope.openDecls } }

open _root_.AddCircle in
def parameterSecondDerivativeHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    TensorHs g 0 0 ((n : ℝ) + 2) →L[ℝ] TensorHs g 0 0 (n : ℝ) :=
  (parameterDerivativeHs g n).comp
    ((tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)).comp
      ((parameterDerivativeHs g (n + 1)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2 by push_cast; linarith))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHs ``Submission.AddCircle.parameterSecondDerivativeHs

open _root_.AddCircle in
theorem parameterSecondDerivativeHs_apply_ccTensorToHs
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (W : SmoothCcTensor g 0 0) :
    parameterSecondDerivativeHs g n (ccTensorToHs g 0 ((n : ℝ) + 2) W) =
      ccTensorToHs g 0 (n : ℝ)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g W)) := by
  simp only [parameterSecondDerivativeHs, ContinuousLinearMap.comp_apply]
  rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHs_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHs_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHs_apply_ccTensorToHs ``Submission.AddCircle.parameterSecondDerivativeHs_apply_ccTensorToHs

open _root_.AddCircle in
@[simp] theorem parameterSecondDerivativeHsPi_apply {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (u : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((n : ℝ) + 2))) (i : ι) :
    parameterSecondDerivativeHsPi g n u i = parameterSecondDerivativeHs g n (u i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHsPi_apply then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHsPi_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHsPi_apply ``Submission.AddCircle.parameterSecondDerivativeHsPi_apply

open _root_.AddCircle in
theorem parameterSecondDerivativeHs_comp_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterSecondDerivativeHs g n).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right h 2)) =
      (tensorHsInclusion (g := g) (r := 0) (s := 0)
        (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp
          (parameterSecondDerivativeHs g m) := by
  let L := (parameterSecondDerivativeHs g n).comp
    (tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right h 2))
  let R := (tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)).comp (parameterSecondDerivativeHs g m)
  have heq : (L : _ → _) = R := (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ (m : ℝ) + 2)).equalizer L.continuous R.continuous (by
    funext S
    simp only [Function.comp_apply, L, R, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
    rw [tensorHsInclusion_ccTensorToHs, parameterSecondDerivativeHs_apply_ccTensorToHs,
      parameterSecondDerivativeHs_apply_ccTensorToHs, tensorHsInclusion_ccTensorToHs])
  exact DFunLike.coe_injective heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHs_comp_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHs_comp_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHs_comp_tensorHsInclusion ``Submission.AddCircle.parameterSecondDerivativeHs_comp_tensorHsInclusion

open _root_.AddCircle in
theorem parameterSecondDerivativeHs_tensorHsInclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) (u : TensorHs g 0 0 ((m : ℝ) + 2)) :
    parameterSecondDerivativeHs g n
        (tensorHsInclusion (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by
          exact_mod_cast Nat.add_le_add_right h 2) u) =
      tensorHsInclusion (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)
        (parameterSecondDerivativeHs g m u) :=
  DFunLike.congr_fun (parameterSecondDerivativeHs_comp_tensorHsInclusion g h) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHs_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHs_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHs_tensorHsInclusion ``Submission.AddCircle.parameterSecondDerivativeHs_tensorHsInclusion

open _root_.AddCircle in
theorem parameterSecondDerivativeHsPi_comp_tensorHsInclusion
    {ι : Type*} (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    {n m : ℕ} (h : n ≤ m) :
    (parameterSecondDerivativeHsPi (ι := ι) g n).comp
        (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 2 ≤ (m : ℝ) + 2 by exact_mod_cast Nat.add_le_add_right h 2))) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h))).comp
            (parameterSecondDerivativeHsPi g m) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact parameterSecondDerivativeHs_tensorHsInclusion g h (u i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHsPi_comp_tensorHsInclusion then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHsPi_comp_tensorHsInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHsPi_comp_tensorHsInclusion ``Submission.AddCircle.parameterSecondDerivativeHsPi_comp_tensorHsInclusion

end AddCircle
