import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivSupport
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.FrameInvariance
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.Continuity
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRS.Basic
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.MetricLowering
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Riemannian
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_symm (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorH1Inner (I := I) (M := M) g r s T S := by
  unfold tensorH1Inner
  congr 1
  · exact tensorL2Inner_symm (I := I) (M := M) g r s S.toFun T.toFun
  · refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact tensorCovDerivPointwiseInner_symm (I := I) (M := M) g r s S T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_symm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_symm

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    0 ≤ tensorH1Inner (I := I) (M := M) g r s S S := by
  unfold tensorH1Inner
  refine add_nonneg ?_ ?_
  · exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  · refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s S x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_nonneg

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (S₁ + S₂) T =
      tensorH1Inner (I := I) (M := M) g r s S₁ T +
        tensorH1Inner (I := I) (M := M) g r s S₂ T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
        tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
          tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (S₁ + S₂) T x) =
      (fun x : M => tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_add_left
      (I := I) (M := M) g r s S₁ S₂ T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_add
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₁ T)
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₂ T)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_add_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_add_left

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorH1Inner_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (c • S) T =
      c * tensorH1Inner (I := I) (M := M) g r s S T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
        c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (c • S) T x) =
      (fun x : M => c * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_smul_left
      (I := I) (M := M) g r s c S T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_const_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_smul_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorH1Inner_smul_left

structure SmoothCcTensorH1 (g : SmoothRiemannianMetric I M) (r s : ℕ) where
  toCcTensor : SmoothCcTensor g r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1

namespace SmoothCcTensorH1

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[ext] theorem ext {S T : SmoothCcTensorH1 g r s}
    (h : S.toCcTensor = T.toCcTensor) : S = T := by
  cases S; cases T; congr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.ext ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.ext

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma toCcTensor_injective :
    Function.Injective (fun S : SmoothCcTensorH1 g r s => S.toCcTensor) := by
  intro S T h
  exact ext h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_injective ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_injective

instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instZero : Zero (SmoothCcTensorH1 g r s) := ⟨⟨0⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instZero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instZero
instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAdd : Add (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAdd ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAdd
instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instNeg : Neg (SmoothCcTensorH1 g r s) := ⟨fun S => ⟨-S.toCcTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instNeg ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instNeg
instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSub : Sub (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSub ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSub
instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulReal : SMul ℝ (SmoothCcTensorH1 g r s) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulReal ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulReal

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorH1 g r s).toCcTensor = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zero
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_add (S T : SmoothCcTensorH1 g r s) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_add
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_neg (S : SmoothCcTensorH1 g r s) :
    (-S).toCcTensor = -S.toCcTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_neg ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_neg
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorH1 g r s) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_sub
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorH1 g r s) :
    (c • S).toCcTensor = c • S.toCcTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_smul

instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulNat : SMul ℕ (SmoothCcTensorH1 g r s) := ⟨nsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulNat ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulNat
instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulInt : SMul ℤ (SmoothCcTensorH1 g r s) := ⟨zsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulInt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instSMulInt

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorH1 g r s) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toCcTensor = (0 : ℕ) • S.toCcTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toCcTensor = (n + 1) • S.toCcTensor
      change (nsmulRec n S + S).toCcTensor = (n + 1) • S.toCcTensor
      have hn : (nsmulRec n S).toCcTensor = n • S.toCcTensor := ih
      rw [toCcTensor_add, hn, succ_nsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_nsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_nsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_nsmul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_nsmul

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorH1 g r s) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor := by
  rcases z with n | n
  · change (n • S).toCcTensor = (Int.ofNat n) • S.toCcTensor
    rw [toCcTensor_nsmul]; simp
  · change (-((n + 1) • S)).toCcTensor = (Int.negSucc n) • S.toCcTensor
    rw [toCcTensor_neg, toCcTensor_nsmul]
    show -((n + 1) • S.toCcTensor) = Int.negSucc n • S.toCcTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zsmul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensor_zsmul

instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAddCommGroup : AddCommGroup (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAddCommGroup ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instAddCommGroup

def toCcTensorAddHom : SmoothCcTensorH1 g r s →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensorAddHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensorAddHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensorAddHom ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.toCcTensorAddHom

instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instModuleReal : Module ℝ (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instModuleReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instModuleReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instModuleReal ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.instModuleReal

end SmoothCcTensorH1


noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorH1 g r s) where
  inner S T := tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
  conj_inner_symm S T := by
    change (tensorH1Inner (I := I) (M := M) g r s T.toCcTensor S.toCcTensor : ℝ) =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    exact tensorH1Inner_symm (I := I) (M := M) g r s T.toCcTensor S.toCcTensor
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor
    exact tensorH1Inner_nonneg (I := I) (M := M) g r s S.toCcTensor
  add_left S₁ S₂ T := by
    change tensorH1Inner (I := I) (M := M) g r s
        (S₁ + S₂).toCcTensor T.toCcTensor =
      tensorH1Inner (I := I) (M := M) g r s S₁.toCcTensor T.toCcTensor +
        tensorH1Inner (I := I) (M := M) g r s S₂.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact tensorH1Inner_add_left (I := I) (M := M) g r s
      S₁.toCcTensor S₂.toCcTensor T.toCcTensor
  smul_left S T c := by
    change tensorH1Inner (I := I) (M := M) g r s
        (c • S).toCcTensor T.toCcTensor =
      c * tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact tensorH1Inner_smul_left (I := I) (M := M) g r s
      c S.toCcTensor T.toCcTensor

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instPreInnerProductSpaceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instPreInnerProductSpaceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instPreInnerProductSpaceCore ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instPreInnerProductSpaceCore


noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instSeminormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instSeminormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instSeminormedAddCommGroup ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instSeminormedAddCommGroup


noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.ofCore _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instInnerProductSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instInnerProductSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instInnerProductSpace ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instInnerProductSpace


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem SmoothCcTensorH1.inner_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensorH1 g r s) :
    ⟪S, T⟫_ℝ =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.inner_def ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.inner_def


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem SmoothCcTensorH1.norm_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ = Real.sqrt (tensorH1Inner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_def ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_def

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
