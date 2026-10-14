import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.RankZeroRealization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

noncomputable def covectorEvaluationField
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    TensorRSField (𝕜 := ℝ) (I := I) (M := M) ∞ 1 0 where
  toFun x := interiorProduct (𝕜 := ℝ) (I := I) 0 x (X x)
  contMDiff_toFun := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
      (F₂ := Tensor0SModel 0 ℝ E) (V₂ := fun x : M => Tensor0SSpace 0 I x)
      (φ := fun x => interiorProduct (𝕜 := ℝ) (I := I) 0 x (X x))
    intro β
    exact DeTurck.interiorProductField_contMDiff (I := I) 0
      (fun x => β x) β.contMDiff X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covectorEvaluationField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covectorEvaluationField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covectorEvaluationField ``Submission.DifferentialGeometry.Analysis.Spectral.covectorEvaluationField

noncomputable def covectorEvaluationCcTensor [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) : SmoothCcTensor g 1 0 where
  toSection := covectorEvaluationField X
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covectorEvaluationCcTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covectorEvaluationCcTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covectorEvaluationCcTensor ``Submission.DifferentialGeometry.Analysis.Spectral.covectorEvaluationCcTensor

theorem covectorEvaluationField_apply
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (α : Tensor0SSpace 1 I x) :
    tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) x
      (covectorEvaluationField X x α) = Tensor0SSpace.eval α (fun _ => X x) := by
  rw [Tensor0SSpace.evalScalar_apply]
  change interiorProduct (𝕜 := ℝ) (I := I) 0 x (X x) α Fin.elim0 = _
  rw [interior_product_apply]
  congr 1
  funext i
  fin_cases i
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covectorEvaluationField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covectorEvaluationField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covectorEvaluationField_apply ``Submission.DifferentialGeometry.Analysis.Spectral.covectorEvaluationField_apply

theorem scalar0_covectorEvaluationCcTensor_apply [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (W : SmoothCcTensor g 0 1) (x : M) :
    TensorRSField.scalar0
      (operatorFieldApply (I := I) (M := M) g 1 0 (covectorEvaluationCcTensor g X) W).toSection x =
      Tensor0SSpace.eval (W.toSection x (unitZeroSec (I := I) (M := M) x)) (fun _ => X x) := by
  change tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) x
    (covectorEvaluationField X x (W.toSection x (Tensor0SField.one0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ x))) = _
  rw [covectorEvaluationField_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_apply ``Submission.DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_apply

end DifferentialGeometry.Analysis.Spectral

end

section

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem covGrad_scalar0_apply
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 0)
    (x : M) (X : TangentSpace I x) :
    Tensor0SSpace.eval
      ((covGrad (I := I) (M := M) g 0 0 S).toSection x
        (unitZeroSec (I := I) (M := M) x)) (fun _ : Fin 1 => X) =
      mfderiv I 𝓘(ℝ) (TensorRSField.scalar0 S.toSection) x X := by
  let f := TensorRSField.scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection
  let hf := TensorRSField.scalar0_smooth (n := (∞ : WithTop ℕ∞)) S.toSection
  let A : Tensor0SField ∞ 0 (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) :=
    Tensor0SField.fromScalarField ∞ f hf
  have hunit (y : M) :
      (tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) (M := M) y)
        (unitZeroSec (I := I) (M := M) y) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    change ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) 1
      Fin.elim0 = 1
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
  have hlift : A.toTensorRSField ∞ = S.toSection :=
    TensorRSField.lift_scalar0 (n := (∞ : WithTop ℕ∞)) S.toSection
  have hsection :
      (fun y : M => S.toSection y (unitZeroSec (I := I) (M := M) y)) =
        fun y : M => A y := by
    funext y
    rw [← hlift, Tensor0SField.toRS0_apply, hunit, one_smul]
  have hscalar : Tensor0SNabla.scalarFn I M (fun y : M => A y) = f := by
    funext y
    rw [Tensor0SNabla.scalarFn_eq_apply_zero]
    change Tensor0SField.toScalarField ∞ A y = f y
    exact congrFun (Tensor0SField.toScalarField_fromScalarField ∞ f hf) y
  rw [covGrad_toSection_apply_natural (I := I) (M := M) g 0 0 S x
    (unitZeroSec (I := I) (M := M) x) (fun _ : Fin 1 => X)]
  rw [tensorCovDerivAt_def, tensorRSCovariantDerivative_zeroS_unit_eval,
    hsection, Tensor0SNabla.tensor0SCovariantDerivative_apply_zero, hscalar]
  change Tensor0SNabla.tensor0Iso I M x
      ((Tensor0SNabla.tensor0Iso I M x).symm (mvfderiv (I := I) f x X)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_scalar0_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_scalar0_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_scalar0_apply ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_scalar0_apply

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem scalar0_covectorEvaluationCcTensor_covGrad
    (g : SmoothRiemannianMetric I M)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (S : SmoothCcTensor g 0 0) (x : M) :
    TensorRSField.scalar0
      (operatorFieldApply (I := I) (M := M) g 1 0 (covectorEvaluationCcTensor g X)
        (covGrad (I := I) (M := M) g 0 0 S)).toSection x =
      mfderiv I 𝓘(ℝ) (TensorRSField.scalar0 S.toSection) x (X x) := by
  rw [scalar0_covectorEvaluationCcTensor_apply, covGrad_scalar0_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_covGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_covGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_covGrad ``Submission.DifferentialGeometry.Analysis.Spectral.scalar0_covectorEvaluationCcTensor_covGrad

end DifferentialGeometry.Analysis.Spectral

end
