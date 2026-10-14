import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.SecondOrder.Basic
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTwoTensor.Basic
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTwoTensor.Pointwise
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.FirstOrder.DirichletPairing
import Submission.DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Iterates
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.MixedCompatibility
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorCommutator
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Lowering
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.FirstOrder.CovariantDerivative
import Submission.DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.Support
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
    CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.Tensor0SNabla _root_.Submission.DifferentialGeometry.TensorRSNabla
    DifferentialGeometry.TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
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

def LoweringIntertwiner (g : SmoothRiemannianMetric I M) (s : ℕ) : Prop :=
  ∀ (S : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (x : M) (v : TangentSpace I x),
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s S x v) =
      lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) S x v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.LoweringIntertwiner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.LoweringIntertwiner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.LoweringIntertwiner ``Submission.DifferentialGeometry.Analysis.Elliptic.LoweringIntertwiner

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma loweringIntertwiner_two (g : SmoothRiemannianMetric I M) :
    LoweringIntertwiner (I := I) (M := M) g 2 :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt (I := I) (M := M) g S x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_two ``Submission.DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_two

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem loweredCovDerivAt_eq_lower_tensorCovDerivAt_three
    (g : SmoothRiemannianMetric I M)
    (S : Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun x : M => TensorRSSpace 0 3 I x)⟯)
    (x : M) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 3 S x v) =
      lowerAllUpperIndices (I := I) (M := M) g 0 3 x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v)) := by
  classical
  let unitSec : Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
    ⟨fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
      contMDiff_unitZeroSection (I := I) (M := M)⟩
  have hcoe : (fun y : M => unitSec y) =
      fun _ : M => Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl
  have hunit_model : Tensor0SSpace.toModel (unitSec x) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    change Tensor0SSpace.toModel (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = _
    rw [Tensor0SSpace.toModel_ofModel]
  have hlowerA :
      lowerAllUpperIndices (I := I) (M := M) g 0 3 x
          (TensorRSSpace.toModel
            (tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v)) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 3) I x from
              tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v)
            (unitSec x)) := by
    rw [toModel_tensorRS_apply (I := I) (M := M) 0 3 x
      (tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g) S x v) (unitSec x)]
    rw [hunit_model]
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [lowerAllUpperIndices_apply, separableFormAt_zero]
    congr 1
    funext j
    exact congrArg u (Fin.ext (by simp))
  rw [hlowerA]
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 3
    (LeviCivita (I := I) g) S unitSec x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitSec y) x v) = 0 from by
    rw [hcoe]
    exact tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]
  rw [loweredCovDerivAt_def]
  have hsec : (fun y : M =>
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace (0 + 3) I y from S y) (unitSec y)) =
      liftedTensorSection (I := I) (M := M) g 0 3 S := by
    funext y
    refine Tensor0SSpace.toModel_injective ?_
    refine ContinuousMultilinearMap.ext (fun u => ?_)
    rw [toModel_liftedTensorSection_zero_eq_apply_unit_reindex (I := I) (M := M) g 3 S y u]
    congr 1
    funext j
    exact congrArg u (Fin.ext (by simp))
  rw [hsec]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_three ``Submission.DifferentialGeometry.Analysis.Elliptic.loweredCovDerivAt_eq_lower_tensorCovDerivAt_three

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma loweringIntertwiner_three (g : SmoothRiemannianMetric I M) :
    LoweringIntertwiner (I := I) (M := M) g 3 :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_three (I := I) (M := M) g S x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_three ``Submission.DifferentialGeometry.Analysis.Elliptic.loweringIntertwiner_three

def covDerivAlongVFrawCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, TensorRSSpace 0 s I y :=
  covApply (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g))
    (fun y : M => B y) (fun y : M => T y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma covDerivAlongVFrawCovariantTensor_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFrawCovariantTensor (I := I) (M := M) g s T B y =
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma covDerivAlongVFrawCovariantTensor_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covDerivAlongVFrawCovariantTensor (I := I) (M := M) g s T B y)) := by
  classical
  set cov := tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) with hcov_def
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from rfl]
    exact T.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (B y)) :=
    B.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply cov (fun y : M => B y) (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT
  rw [← contMDiffOn_univ]
  exact hOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFrawCovariantTensor_contMDiff

def covDerivAlongVFSectionCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covDerivAlongVFrawCovariantTensor (I := I) (M := M) g s T B y)
    (covDerivAlongVFrawCovariantTensor_contMDiff (I := I) (M := M) g s T B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma covDerivAlongVFSectionCovariantTensor_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T B y =
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_apply

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlongVFSectionCovariantTensor_lowered_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s y
        (TensorRSSpace.toModel (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T B y)) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s T y (B y)) := by
  rw [hint T y (B y)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_lowered_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_lowered_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_lowered_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlongVFSectionCovariantTensor_lowered_eq

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g 0 s
          (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T B) y) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g 0 s T y (B y)) := by
  rw [toModel_liftedTensorSection]
  exact covDerivAlongVFSectionCovariantTensor_lowered_eq (I := I) (M := M) g s hint T B y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma covDerivAlong_covDerivAlongVFSectionCovariantTensor_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun x : M => TensorRSSpace 0 s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s
        (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T B) B y =
      tensorSecondCovDeriv (I := I) g 0 s
          (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) y +
        (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun b : M => T b) y
          ((LeviCivita (I := I) g).toFun (fun b : M => B b) y (B y)) := by
  rw [tensorSecondCovDeriv_def]
  change (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
      (covApply (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g))
        (fun b : M => B b) (fun b : M => T b)) y (B y) = _
  rw [show tensorCov (I := I) g 0 s =
      tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g) from rfl]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSectionCovariantTensor_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSectionCovariantTensor_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSectionCovariantTensor_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.covDerivAlong_covDerivAlongVFSectionCovariantTensor_eq

def dirichletFormCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g 0 s b
    (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 s T b X))
    (TensorRSSpace.toModel (v.toSection b))
  map_add' X Y := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 s T b (X + Y) =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b X +
          tensorCovDerivAt (I := I) (M := M) g 0 s T b Y := by
      change (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (X + Y) = _
      rw [ContinuousLinearMap.map_add]
      rfl
    rw [hcov, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  map_smul' c X := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 s T b (c • X) =
        c • tensorCovDerivAt (I := I) (M := M) g 0 s T b X := by
      change (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (c • X) = _
      rw [ContinuousLinearMap.map_smul]
      rfl
    rw [hcov, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma dirichletFormCovariantTensor_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M)
    (X : TangentSpace I b) :
    dirichletFormCovariantTensor (I := I) (M := M) g s T v b X =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 s T b X))
        (TensorRSSpace.toModel (v.toSection b)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor_apply

def dirichletVFCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (dirichletFormCovariantTensor (I := I) (M := M) g s T v b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma inner_dirichletVFCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M)
    (X : TangentSpace I b) :
    g.inner b (dirichletVFCovariantTensor (I := I) (M := M) g s T v b) X =
      dirichletFormCovariantTensor (I := I) (M := M) g s T v b X := by
  rw [dirichletVFCovariantTensor]
  exact inner_metricSharp (I := I) g b (dirichletFormCovariantTensor (I := I) (M := M) g s T v b) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFCovariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.inner_dirichletVFCovariantTensor

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma dirichletFormCovariantTensor_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => dirichletFormCovariantTensor (I := I) (M := M) g s T v b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  have hcov_section : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun y : M => TensorRSSpace 0 s I y) b
        (tensorCovDerivAt (I := I) (M := M) g 0 s T b
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g 0 s T α j
  have hcov_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 s T b
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g 0 s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 s T b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)) α hcov_section
  have hv_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 s α b
        (TensorRSSpace.toModel (v.toSection b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g 0 s v.toSection α
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)))
          (TensorRSSpace.toModel (v.toSection b)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g 0 s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 s T b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
      (fun b : M => v.toSection b) α hcov_lowered hv_lowered
  have hbase_eq : (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [dirichletFormCovariantTensor_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor_chartBasis_component_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.dirichletFormCovariantTensor_chartBasis_component_contMDiffOn target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma dirichletVFCovariantTensor_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (dirichletVFCovariantTensor (I := I) (M := M) g s T v b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => dirichletFormCovariantTensor (I := I) (M := M) g s T v b)
    (fun α j => dirichletFormCovariantTensor_chartBasis_component_contMDiffOn
      (I := I) (M := M) g s T v α j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor_contMDiff ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFCovariantTensor_contMDiff

def dirichletVFSectionCovariantTensor
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => dirichletVFCovariantTensor (I := I) (M := M) g s T v b)
    (dirichletVFCovariantTensor_contMDiff (I := I) (M := M) g s T v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] lemma dirichletVFSectionCovariantTensor_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    dirichletVFSectionCovariantTensor (I := I) (M := M) g s T v b =
      dirichletVFCovariantTensor (I := I) (M := M) g s T v b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor_apply ``Submission.DifferentialGeometry.Analysis.Elliptic.dirichletVFSectionCovariantTensor_apply

omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma divergence_dirichletVFCovariantTensor_summand_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (dirichletVFSectionCovariantTensor (I := I) (M := M) g s T v).toFun b
          (smoothOrthoFrame (I := I) g b i b))
        (smoothOrthoFrame (I := I) g b i b) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorSecondCovDeriv (I := I) g 0 s
              (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
              (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g b i y,
      smoothOrthoFrame_smooth (I := I) g b i⟩ with hB_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionCovariantTensor (I := I) (M := M) g s T v with hZ_def
  have hBb : (B : ∀ y, TangentSpace I y) b = smoothOrthoFrame (I := I) g b i b := rfl
  have hleib := leibniz_inner (I := I) g
    (V := fun y : M => Z y) (W := fun y : M => B y)
    Z.contMDiff B.contMDiff
    (x := b) ((B : ∀ y, TangentSpace I y) b)
  have hfun : (fun y : M => g.inner y (Z y) (B y)) =
      tensorInnerScalar (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B) v.toSection := by
    funext y
    rw [hZ_def, dirichletVFSectionCovariantTensor_apply, inner_dirichletVFCovariantTensor, dirichletFormCovariantTensor_apply,
      tensorInnerScalar_apply, covDerivAlongVFSectionCovariantTensor_apply]
    rfl
  have hprod : tangentSectionAction (I := I) B
        (fun y : M => g.inner y (Z y) (B y)) b =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s
              (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B) B b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s v.toSection B b)) := by
    rw [show tangentSectionAction (I := I) B
            (fun y : M => g.inner y (Z y) (B y)) =
          tangentSectionAction (I := I) B
            (tensorInnerScalar (I := I) (M := M) g 0 s
              (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B) v.toSection) from by
      rw [hfun]]
    rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g 0 s
      (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B) v.toSection B b]
    congr 1
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s
          (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B) B)
        v.toSection b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s hint
        (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B) B b]
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 s
        (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B)
        (covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s v.toSection B) b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s hint
        T.toSection B b,
        toModel_liftedTensorSection_covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s hint v.toSection
          B b]
  have haccel : g.inner b (Z b)
        ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
          ((B : ∀ y, TangentSpace I y) b)) =
      tensorInnerPointwise (I := I) (M := M) g 0 s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 s T b
            ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
              ((B : ∀ y, TangentSpace I y) b))))
        (TensorRSSpace.toModel (v.toSection b)) := by
    rw [hZ_def, dirichletVFSectionCovariantTensor_apply, inner_dirichletVFCovariantTensor, dirichletFormCovariantTensor_apply]
  have hsecond := covDerivAlong_covDerivAlongVFSectionCovariantTensor_eq (I := I) (M := M) g s T.toSection B
    b
  have hsummand : g.inner b
        ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
          ((B : ∀ y, TangentSpace I y) b))
        ((B : ∀ y, TangentSpace I y) b) =
      tangentSectionAction (I := I) B (fun y : M => g.inner y (Z y) (B y)) b
        - g.inner b (Z b)
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := by
    rw [tangentSectionAction_def]
    rw [hleib]; ring
  change g.inner b
      ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
        ((B : ∀ y, TangentSpace I y) b))
      ((B : ∀ y, TangentSpace I y) b) = _
  rw [hsummand, hprod, haccel]
  rw [hsecond, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have haccel_eq :
      (tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := rfl
  rw [haccel_eq]
  rw [show covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s T.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 s T b ((B : ∀ y, TangentSpace I y) b) from rfl,
    show covDerivAlongVFSectionCovariantTensor (I := I) (M := M) g s v.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 s v b ((B : ∀ y, TangentSpace I y) b) from rfl]
  rw [hBb]
  rw [show (fun y : M => (B : ∀ z : M, TangentSpace I z) y) =
        (fun y : M => smoothOrthoFrame (I := I) g b i y) from rfl]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFCovariantTensor_summand_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFCovariantTensor_summand_eq target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma tensorCovDerivPointwiseInnerCovariantTensor_eq_smoothOrthoFrame_diag
    (g : SmoothRiemannianMetric I M) (s : ℕ) (T v : SmoothCcTensor g 0 s) (b : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 s v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), _root_.MulZeroClass.mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I b) := by
    rw [Fintype.card_fin]
    rfl
  set tangentFrame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I b) :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hframe_def
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    tangentFrame.map
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).toLinearEquiv with hframe_model_def
  have hframe_eq : ∀ i, frame i =
      tangentSpaceModelContinuousLinearEquiv (I := I) b
        (smoothOrthoFrame (I := I) g b i b) := by
    intro i
    rw [hframe_model_def, Module.Basis.map_apply, hframe_def]
    change tangentSpaceModelContinuousLinearEquiv (I := I) b
        ((basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
          Fin (Module.finrank ℝ E) → TangentSpace I b) i) = _
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      modelInnerAt (I := I) (M := M) g b (frame i) (frame j) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hframe_eq i, hframe_eq j, modelInnerAt_apply,
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply,
      (tangentSpaceModelContinuousLinearEquiv (I := I) b).symm_apply_apply]
    exact hB_orth i j
  rw [tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (I := I) (M := M) g 0 s T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i, tangentSpaceModelContinuousLinearEquiv_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInnerCovariantTensor_eq_smoothOrthoFrame_diag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.tensorCovDerivPointwiseInnerCovariantTensor_eq_smoothOrthoFrame_diag target :: scope.openDecls } }

omit [CompactSpace M] [SigmaCompactSpace M] in
lemma divergence_dirichletVFCovariantTensor_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) (b : M) :
    divergenceG (I := I) g (dirichletVFSectionCovariantTensor (I := I) (M := M) g s T v) b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
  classical
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g
    (dirichletVFSectionCovariantTensor (I := I) (M := M) g s T v) b]
  rw [Finset.sum_congr rfl (fun i _ =>
    divergence_dirichletVFCovariantTensor_summand_eq (I := I) (M := M) g s hint T v b i)]
  rw [Finset.sum_add_distrib]
  rw [← tensorCovDerivPointwiseInnerCovariantTensor_eq_smoothOrthoFrame_diag (I := I) (M := M) g s T v b]
  rw [add_comm]
  congr 1
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 s
    (fun y : M => T.toSection y) b]
  rw [show TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g 0 s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) from ?_]
  · rw [show (∑ i : Fin (Module.finrank ℝ E),
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b)) =
          ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g 0 s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
    rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 s b Finset.univ _ _ _]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul]
  · exact map_sum (tensorRSSpaceContinuousLinearEquiv (I := I) 0 s b)
      (fun i => tensorSecondCovDeriv (I := I) g 0 s
        (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
        (fun y : M => T.toSection y) b) Finset.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFCovariantTensor_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFCovariantTensor_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFCovariantTensor_eq ``Submission.DifferentialGeometry.Analysis.Elliptic.divergence_dirichletVFCovariantTensor_eq

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (hint : LoweringIntertwiner (I := I) (M := M) g s)
    (T v : SmoothCcTensor g 0 s) :
    tensorL2Inner (I := I) (M := M) g 0 (s + 1)
        (covGrad (I := I) (M := M) g 0 s T).toFun
        (covGrad (I := I) (M := M) g 0 s v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 s
          (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionCovariantTensor (I := I) (M := M) g s T v with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hdiv_zero : ∫ b, divergenceG (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergenceG (I := I) g Z b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b
        + tensorInnerPointwise (I := I) (M := M) g 0 s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
    intro b; rw [hZ_def]; exact divergence_dirichletVFCovariantTensor_eq (I := I) (M := M) g s hint T v b
  rw [_root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_int : _root_.MeasureTheory.Integrable
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 s T v b) μ :=
    tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g 0 s T v
  have hsecond_int : _root_.MeasureTheory.Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) μ := by
    simpa only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply] using
      (rawTensorConnLapSmooth (I := I) g 0 s T).integrable_inner_cross v
  rw [_root_.MeasureTheory.integral_add hcross_int hsecond_int] at hdiv_zero
  rw [tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
    (I := I) (M := M) g 0 s T v, ← hμ_def]
  rw [show tensorL2Inner (I := I) (M := M) g 0 s
        (rawTensorConnLapSmooth (I := I) g 0 s T).toFun v.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b)) ∂μ from ?_]
  · linarith [hdiv_zero]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 3) :
    tensorL2Inner (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3 T).toFun
        (covGrad (I := I) (M := M) g 0 3 v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3 T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap
    (I := I) (M := M) g 3 (loweringIntertwiner_three (I := I) (M := M) g) T v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun
        (covGrad (I := I) (M := M) g 0 2 v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap
    (I := I) (M := M) g 2 (loweringIntertwiner_two (I := I) (M := M) g) T v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two

end Elliptic
end Analysis
end DifferentialGeometry

end
