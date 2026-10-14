import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


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

abbrev TensorH1Compl (g : SmoothRiemannianMetric I M) (r s : ℕ) : Type _ :=
  UniformSpace.Completion (SmoothCcTensorH1 g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1Compl

noncomputable def smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s :=
  UniformSpace.Completion.toComplL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothToTensorH1Compl_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothToTensorH1Compl (I := I) (M := M) g r s S =
      (S : TensorH1Compl g r s) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothToTensorH1Compl_apply


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma SmoothCcTensor.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    ‖S‖ ^ 2 = tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
  have h := real_inner_self_eq_norm_sq S
  rw [SmoothCcTensor.inner_def] at h
  exact h.symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensor
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.norm_sq_eq_inner_self
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ ^ 2 =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor := by
  have h := real_inner_self_eq_norm_sq S
  rw [SmoothCcTensorH1.inner_def] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_sq_eq_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_sq_eq_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_sq_eq_inner_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.norm_sq_eq_inner_self


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.l2NormSq_le_h1NormSq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ^ 2 ≤ ‖S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M) S.toCcTensor,
    SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S,
    tensorH1Inner_def]
  have h_grad_nonneg :
      0 ≤ ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
              S.toCcTensor S.toCcTensor x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s
      S.toCcTensor x
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2NormSq_le_h1NormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2NormSq_le_h1NormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2NormSq_le_h1NormSq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2NormSq_le_h1NormSq


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.l2Norm_le_h1Norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ≤ ‖S‖ := by
  have h_sq := SmoothCcTensorH1.l2NormSq_le_h1NormSq (I := I) (M := M) S
  have h_rhs_nn : 0 ≤ ‖S‖ := norm_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nn |>.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_h1Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_h1Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_h1Norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_h1Norm


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S.toCcTensor‖ ≤ 1 * ‖S‖ := by
  rw [one_mul]; exact SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm

noncomputable def smoothCcTensorH1ToTensorL2Lin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] TensorL2 r s g where
  toFun S := (S.toCcTensor : TensorL2 r s g)
  map_add' S T := by
    change ((S + T).toCcTensor : TensorL2 r s g) =
      (S.toCcTensor : TensorL2 r s g) + (T.toCcTensor : TensorL2 r s g)
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c S := by
    change ((c • S).toCcTensor : TensorL2 r s g) =
      c • (S.toCcTensor : TensorL2 r s g)
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact UniformSpace.Completion.coe_smul _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma smoothCcTensorH1ToTensorL2Lin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S =
      (S.toCcTensor : TensorL2 r s g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_apply


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma smoothCcTensorH1ToTensorL2Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S‖ ≤ 1 * ‖S‖ := by
  have h_coe_norm :
      ‖(S.toCcTensor : TensorL2 r s g)‖ = ‖S.toCcTensor‖ :=
    UniformSpace.Completion.norm_coe _
  calc ‖smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s S‖
      = ‖(S.toCcTensor : TensorL2 r s g)‖ := rfl
    _ = ‖S.toCcTensor‖ := h_coe_norm
    _ ≤ 1 * ‖S‖ :=
      SmoothCcTensorH1.l2Norm_le_one_mul_h1Norm (I := I) (M := M) S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2Lin_norm_le

noncomputable def smoothCcTensorH1ToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r s g :=
  (smoothCcTensorH1ToTensorL2Lin (I := I) (M := M) g r s).mkContinuous 1
    (fun S => smoothCcTensorH1ToTensorL2Lin_norm_le (I := I) (M := M) g r s S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma smoothCcTensorH1ToTensorL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s S =
      (S.toCcTensor : TensorL2 r s g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smoothCcTensorH1ToTensorL2_apply

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_toComplL_smoothCcTensorH1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange
      (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s) := by
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.denseRange_toComplL_smoothCcTensorH1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.denseRange_toComplL_smoothCcTensorH1 target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_toComplL_smoothCcTensorH1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing
      (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s) := by
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_toComplL_smoothCcTensorH1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_toComplL_smoothCcTensorH1 target :: scope.openDecls } }

noncomputable def TensorH1ComplToTensorL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorL2 r s g :=
  ContinuousLinearMap.extend (smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s)
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorH1 g r s →L[ℝ] TensorH1Compl g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma TensorH1ComplToTensorL2_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s S := by
  unfold TensorH1ComplToTensorL2
  exact ContinuousLinearMap.extend_eq
    (smoothCcTensorH1ToTensorL2 (I := I) (M := M) g r s)
    (e := UniformSpace.Completion.toComplL)
    (denseRange_toComplL_smoothCcTensorH1 (I := I) (M := M) g r s)
    (isUniformInducing_toComplL_smoothCcTensorH1 (I := I) (M := M) g r s) S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      (S.toCcTensor : TensorL2 r s g) := by
  rw [TensorH1ComplToTensorL2_smoothToTensorH1Compl,
    smoothCcTensorH1ToTensorL2_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
