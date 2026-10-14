import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTwoTensor.Pointwise
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.FirstOrder.LoweredCovariantDerivative
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorCommutator
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.FrameTrace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor0SNabla _root_.Submission.DifferentialGeometry.TensorRSNabla
    DifferentialGeometry.TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

def covDerivAlongVFraw
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, TensorRSSpace 0 2 I y :=
  covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
    (fun y : M => B y) (fun y : M => T y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma covDerivAlongVFraw_apply
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFraw (I := I) (M := M) g T B y =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma covDerivAlongVFraw_contMDiff
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y
        (covDerivAlongVFraw (I := I) (M := M) g T B y)) := by
  classical
  set cov := tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) with hcov_def
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
    exact T.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (B y)) :=
    B.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) y
        (covApply cov (fun y : M => B y) (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT
  rw [← contMDiffOn_univ]
  exact hOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFraw_contMDiff

def covDerivAlongVFSection
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covDerivAlongVFraw (I := I) (M := M) g T B y)
    (covDerivAlongVFraw_contMDiff (I := I) (M := M) g T B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma covDerivAlongVFSection_apply
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSection (I := I) (M := M) g T B y =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlongVFSection_lowered_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 2 y
        (TensorRSSpace.toModel (covDerivAlongVFSection (I := I) (M := M) g T B y)) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 2 T y (B y)) := by
  rw [(loweredCovDerivAt_eq_lower_tensorCovDerivAt
    (I := I) (M := M) g T y (B y))]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_lowered_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_lowered_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_lowered_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSection_lowered_eq

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma toModel_liftedTensorSection_covDerivAlongVFSection
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T B) y) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 2 T y (B y)) := by
  rw [toModel_liftedTensorSection]
  exact covDerivAlongVFSection_lowered_eq (I := I) (M := M) g T B y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSection ``Submission.DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSection

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlong_covDerivAlongVFSection_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T B) B y =
      tensorSecondCovDeriv (I := I) g 0 2
          (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) y +
        (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun b : M => T b) y
          ((LeviCivita (I := I) g).toFun (fun b : M => B b) y (B y)) := by
  rw [tensorSecondCovDeriv_def]
  change (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
      (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
        (fun b : M => B b) (fun b : M => T b)) y (B y) = _
  rw [show tensorCov (I := I) g 0 2 =
      tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) from rfl]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSection_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSection_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSection_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSection_eq

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace.toModel
        (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
          (covDerivAlongVFSection (I := I) (M := M) g T B) B x) =
      lowerAllUpperIndices (I := I) (M := M) g 0 2 x
        (TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g 0 2
            (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) x +
          (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
            (fun b : M => T b) x
            ((LeviCivita (I := I) g).toFun (fun b : M => B b) x (B x)))) := by
  rw [loweredCovDerivAlongVF_apply]
  rw [loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g
    (covDerivAlongVFSection (I := I) (M := M) g T B) x (B x)]
  congr 1
  exact congrArg TensorRSSpace.toModel
    (covDerivAlong_covDerivAlongVFSection_eq (I := I) (M := M) g T B x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.toModel_loweredCovDerivAlongVF_covDerivAlongVFSection_eq

theorem integral_secondOrder_combined_eq_zero
    (g : SmoothRiemannianMetric I M)
    (T v : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∫ x, (covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) B x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2 v x))
          + covariantTensorInnerPointwise (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x))
          + tensorInnerScalar (I := I) (M := M) g 0 2
              (covDerivAlongVFSection (I := I) (M := M) g T B) v x
            * divergenceG (I := I) g B x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
  integral_tensorInner_covDeriv_combined_eq_zero (I := I) (M := M) g 0 2
    (covDerivAlongVFSection (I := I) (M := M) g T B) v B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.integral_secondOrder_combined_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.integral_secondOrder_combined_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.integral_secondOrder_combined_eq_zero ``Submission.DifferentialGeometry.Analysis.Elliptic.integral_secondOrder_combined_eq_zero

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlong_secondOrder_eq_fixedFrame_summand
    (g : SmoothRiemannianMetric I M)
    (T : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T B) B b -
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) b
        (covApply (LeviCivita (I := I) g) (fun y : M => B y) (fun y : M => B y) b) =
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (covApply (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g))
            (fun y : M => B y) (fun y : M => T y)) b (B b) -
        (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlong_secondOrder_eq_fixedFrame_summand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlong_secondOrder_eq_fixedFrame_summand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlong_secondOrder_eq_fixedFrame_summand ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlong_secondOrder_eq_fixedFrame_summand

end Elliptic
end Analysis
end DifferentialGeometry

end
