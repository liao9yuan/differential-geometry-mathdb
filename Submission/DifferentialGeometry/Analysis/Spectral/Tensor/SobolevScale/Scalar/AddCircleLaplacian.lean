import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.AddCircle
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.RankZeroRealization
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry target :: scope.openDecls } }

open _root_.AddCircle in
private theorem scalar0_rawTensorConnLapSmooth_flatMetric
    (S : SmoothCcTensor flatMetric 0 0) (x : ℝ) :
    TensorRSField.scalar0 (rawTensorConnLapSmooth flatMetric 0 0 S).toSection
        (x : AddCircle (1 : ℝ)) =
      TensorRSField.scalar0
        (parameterDerivativeCcTensor flatMetric
          (parameterDerivativeCcTensor flatMetric S)).toSection
        (x : AddCircle (1 : ℝ)) := by
  rw [rawLap_cc_scalar, scalar0_parameterDerivativeCcTensor_twice_coe]
  rw [← laplacian_levi_eq flatMetric (TensorRSField.scalar0_smooth S.toSection)]
  exact laplacian_flatMetric_coe
    ((TensorRSField.scalar0_smooth S.toSection).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)) x

run_cmd do
  let target := ``Submission.AddCircle.scalar0_rawTensorConnLapSmooth_flatMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.scalar0_rawTensorConnLapSmooth_flatMetric target :: scope.openDecls } }

open _root_.AddCircle in
theorem rawTensorConnLapSmooth_flatMetric
    (S : SmoothCcTensor flatMetric 0 0) :
    rawTensorConnLapSmooth flatMetric 0 0 S =
      parameterDerivativeCcTensor flatMetric (parameterDerivativeCcTensor flatMetric S) := by
  apply SmoothCcTensor.ext
  have h : TensorRSField.scalar0 (rawTensorConnLapSmooth flatMetric 0 0 S).toSection =
      TensorRSField.scalar0
        (parameterDerivativeCcTensor flatMetric
          (parameterDerivativeCcTensor flatMetric S)).toSection := by
    funext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact scalar0_rawTensorConnLapSmooth_flatMetric S x
  rw [← TensorRSField.lift_scalar0 (rawTensorConnLapSmooth flatMetric 0 0 S).toSection,
    ← TensorRSField.lift_scalar0
      (parameterDerivativeCcTensor flatMetric
        (parameterDerivativeCcTensor flatMetric S)).toSection]
  congr 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.rawTensorConnLapSmooth_flatMetric then
    throwError "Refusing to shadow existing declaration AddCircle.rawTensorConnLapSmooth_flatMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.rawTensorConnLapSmooth_flatMetric ``Submission.AddCircle.rawTensorConnLapSmooth_flatMetric

end AddCircle

end

section

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_1 target :: scope.openDecls } }

open _root_.AddCircle in
private theorem parameterSecondDerivativeHsPi_eq_of_core
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (hcore : ∀ S : SmoothCcTensor g 0 0,
      parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S) =
        rawTensorConnLapSmooth g 0 0 S) :
    parameterSecondDerivativeHsPi (ι := ι) g n =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
          (g := g) (r := 0) (s := 0) (n : ℝ)) := by
  let L := (parameterDerivativeHs g n).comp
    ((tensorHsInclusion (g := g) (r := 0) (s := 0)
      (show (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) by norm_num)).comp
      ((parameterDerivativeHs g (n + 1)).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show ((n + 1 : ℕ) : ℝ) + 1 ≤ (n : ℝ) + 2 by push_cast; linarith))))
  let R := tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
    (g := g) (r := 0) (s := 0) (n : ℝ)
  have heq : (L : _ → _) = R := (ccToHsLin_dense g 0 (by positivity :
      (0 : ℝ) ≤ (n : ℝ) + 2)).equalizer L.continuous R.continuous (by
    funext S
    simp only [Function.comp_apply, L, R, ContinuousLinearMap.comp_apply, ccToHsLin_apply]
    rw [tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
      tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
      hcore, tensorScaleLaplacian_apply_ccTensorToHs])
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  exact congrFun heq (u i)

run_cmd do
  let target := ``Submission.AddCircle.parameterSecondDerivativeHsPi_eq_of_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.parameterSecondDerivativeHsPi_eq_of_core target :: scope.openDecls } }

open _root_.AddCircle in
theorem parameterSecondDerivativeHsPi_flatMetric {ι : Type*} (n : ℕ) :
    parameterSecondDerivativeHsPi (ι := ι) flatMetric n =
      ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorScaleLaplacian (I := 𝓘(ℝ, ℝ)) (M := AddCircle (1 : ℝ))
          (g := flatMetric) (r := 0) (s := 0) (n : ℝ)) :=
  parameterSecondDerivativeHsPi_eq_of_core flatMetric n
    (fun S => (rawTensorConnLapSmooth_flatMetric S).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.parameterSecondDerivativeHsPi_flatMetric then
    throwError "Refusing to shadow existing declaration AddCircle.parameterSecondDerivativeHsPi_flatMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.parameterSecondDerivativeHsPi_flatMetric ``Submission.AddCircle.parameterSecondDerivativeHsPi_flatMetric

end AddCircle

end

end

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_2 target :: scope.openDecls } }

open _root_.AddCircle in
theorem rawTensorConnLapSmooth_eq_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (S : SmoothCcTensor g 0 0) :
    rawTensorConnLapSmooth g 0 0 S =
      scalarSmul g 0 0 (laplacianPrincipalCoefficient g)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
      scalarSmul g 0 0 (laplacianDriftCoefficient g)
        (parameterDerivativeCcTensor g S) := by
  apply SmoothCcTensor.ext
  have h : TensorRSField.scalar0 (rawTensorConnLapSmooth g 0 0 S).toSection =
      TensorRSField.scalar0
        (scalarSmul g 0 0 (laplacianPrincipalCoefficient g)
          (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
        scalarSmul g 0 0 (laplacianDriftCoefficient g)
          (parameterDerivativeCcTensor g S)).toSection := by
    funext z
    rw [SmoothCcTensor.toSection_add, TensorRSField.scalar0_add, Pi.add_apply,
      scalar0_smul_cc, scalar0_smul_cc]
    rw [rawLap_cc_scalar,
      ← laplacian_levi_eq g (TensorRSField.scalar0_smooth S.toSection)]
    rw [laplacian_eq_principal_add_drift g
      ((TensorRSField.scalar0_smooth S.toSection).contMDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ ∞))]
    rw [scalar0_parameterDerivativeCcTensor, scalar0_parameterDerivativeCcTensor]
    have hD : TensorRSField.scalar0 (parameterDerivativeCcTensor g S).toSection =
        fun y => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (TensorRSField.scalar0 S.toSection) y
          (parameterTangent y) := funext (scalar0_parameterDerivativeCcTensor g S)
    rw [hD]
    rfl
  rw [← TensorRSField.lift_scalar0 (rawTensorConnLapSmooth g 0 0 S).toSection,
    ← TensorRSField.lift_scalar0
      (scalarSmul g 0 0 (laplacianPrincipalCoefficient g)
        (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
      scalarSmul g 0 0 (laplacianDriftCoefficient g)
        (parameterDerivativeCcTensor g S)).toSection]
  congr 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.rawTensorConnLapSmooth_eq_principal_add_drift then
    throwError "Refusing to shadow existing declaration AddCircle.rawTensorConnLapSmooth_eq_principal_add_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.rawTensorConnLapSmooth_eq_principal_add_drift ``Submission.AddCircle.rawTensorConnLapSmooth_eq_principal_add_drift

end AddCircle

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace AddCircle
open _root_.AddCircle

open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

open _root_.AddCircle in
private local instance _root_.Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3 : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.instNeZeroNatFinrankReal_differentialGeometry_3 target :: scope.openDecls } }

open _root_.AddCircle in
private theorem tensorScaleLaplacian_eq_of_scalar_core
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (a b : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯)
    (hcore : ∀ S : SmoothCcTensor g 0 0,
      rawTensorConnLapSmooth g 0 0 S =
        scalarSmul g 0 0 a (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
          scalarSmul g 0 0 b (parameterDerivativeCcTensor g S)) :
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ) =
      (appHs g 0 0 n (scalarCc g a)).comp
        (parameterSecondDerivativeHs g n) +
      (appHs g 0 0 n (scalarCc g b)).comp
        ((parameterDerivativeHs g n).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))) := by
  let L := tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)
  let R := (appHs g 0 0 n (scalarCc g a)).comp (parameterSecondDerivativeHs g n) +
    (appHs g 0 0 n (scalarCc g b)).comp
      ((parameterDerivativeHs g n).comp
        (tensorHsInclusion (g := g) (r := 0) (s := 0)
          (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)))
  have heq : (L : _ → _) = R :=
    (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2)).equalizer
      L.continuous R.continuous (by
        funext S
        simp only [Function.comp_apply, L, R, add_apply,
          ContinuousLinearMap.comp_apply, ccToHsLin_apply]
        rw [tensorScaleLaplacian_apply_ccTensorToHs,
          parameterSecondDerivativeHs_apply_ccTensorToHs,
          tensorHsInclusion_ccTensorToHs, parameterDerivativeHs_apply_ccTensorToHs,
          appHs_apply_ccTensorToHs, appHs_apply_ccTensorToHs,
          app_scalarCc, app_scalarCc, hcore, ccTensorToHs_add])
  exact ContinuousLinearMap.coeFn_injective heq

run_cmd do
  let target := ``Submission.AddCircle.tensorScaleLaplacian_eq_of_scalar_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.tensorScaleLaplacian_eq_of_scalar_core target :: scope.openDecls } }

open _root_.AddCircle in
private local instance piLp_continuousAdd {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ContinuousAdd (PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))) where
  continuous_add := by
    change Continuous (fun z : PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) ×
      PiLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) =>
        WithLp.toLp 2 (fun i => z.1 i + z.2 i))
    apply (PiLp.continuous_toLp 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ))).comp
    apply continuous_pi
    intro i
    exact ((PiLp.continuous_apply 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) i).comp
      continuous_fst).add
      ((PiLp.continuous_apply 2 (fun _ : ι => TensorHs g 0 0 (n : ℝ)) i).comp continuous_snd)

run_cmd do
  let target := ``Submission.AddCircle.piLp_continuousAdd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.piLp_continuousAdd target :: scope.openDecls } }


open _root_.AddCircle in
private theorem piLpMap_tensorScaleLaplacian_eq_of_scalar_core
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ)
    (a b : C^∞⟮𝓘(ℝ, ℝ), AddCircle (1 : ℝ); ℝ⟯)
    (hcore : ∀ S : SmoothCcTensor g 0 0,
      rawTensorConnLapSmooth g 0 0 S =
        scalarSmul g 0 0 a (parameterDerivativeCcTensor g (parameterDerivativeCcTensor g S)) +
          scalarSmul g 0 0 b (parameterDerivativeCcTensor g S)) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => appHs g 0 0 n (scalarCc g a))).comp
        (parameterSecondDerivativeHsPi g n) +
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι => appHs g 0 0 n (scalarCc g b))).comp
        ((parameterDerivativeHsPi g n).comp
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  have h := congrArg (fun L => L (u i)) (tensorScaleLaplacian_eq_of_scalar_core g n a b hcore)
  exact h

run_cmd do
  let target := ``Submission.AddCircle.piLpMap_tensorScaleLaplacian_eq_of_scalar_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `AddCircle.piLpMap_tensorScaleLaplacian_eq_of_scalar_core target :: scope.openDecls } }

open _root_.AddCircle in
theorem tensorScaleLaplacian_eq_principal_add_drift
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ) =
      (appHs g 0 0 n (scalarCc g (laplacianPrincipalCoefficient g))).comp
        (parameterSecondDerivativeHs g n) +
      (appHs g 0 0 n (scalarCc g (laplacianDriftCoefficient g))).comp
        ((parameterDerivativeHs g n).comp
          (tensorHsInclusion (g := g) (r := 0) (s := 0)
            (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith))) :=
  tensorScaleLaplacian_eq_of_scalar_core g n _ _
    (rawTensorConnLapSmooth_eq_principal_add_drift g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.tensorScaleLaplacian_eq_principal_add_drift then
    throwError "Refusing to shadow existing declaration AddCircle.tensorScaleLaplacian_eq_principal_add_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.tensorScaleLaplacian_eq_principal_add_drift ``Submission.AddCircle.tensorScaleLaplacian_eq_principal_add_drift

open _root_.AddCircle in
theorem piLpMap_tensorScaleLaplacian_eq_principal_add_drift
    {ι : Type*}
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (n : ℕ) :
    ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorScaleLaplacian (g := g) (r := 0) (s := 0) (n : ℝ)) =
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        appHs g 0 0 n (scalarCc g (laplacianPrincipalCoefficient g)))).comp
        (parameterSecondDerivativeHsPi g n) +
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        appHs g 0 0 n (scalarCc g (laplacianDriftCoefficient g)))).comp
        ((parameterDerivativeHsPi g n).comp
          (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
            tensorHsInclusion (g := g) (r := 0) (s := 0)
              (show (n : ℝ) + 1 ≤ (n : ℝ) + 2 by linarith)))) :=
  piLpMap_tensorScaleLaplacian_eq_of_scalar_core g n _ _
    (rawTensorConnLapSmooth_eq_principal_add_drift g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AddCircle.piLpMap_tensorScaleLaplacian_eq_principal_add_drift then
    throwError "Refusing to shadow existing declaration AddCircle.piLpMap_tensorScaleLaplacian_eq_principal_add_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `AddCircle.piLpMap_tensorScaleLaplacian_eq_principal_add_drift ``Submission.AddCircle.piLpMap_tensorScaleLaplacian_eq_principal_add_drift

end AddCircle
