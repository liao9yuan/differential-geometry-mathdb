import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Bridge.Metric
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma tensorL2Inner_covGrad_self_eq_dirichlet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s S).toFun
        (covGrad (I := I) (M := M) g r s S).toFun =
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  unfold tensorL2Inner
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  change tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x))
      (TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g r s S).toSection x)) =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x
  exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s S S x).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2Inner_covGrad_self_eq_dirichlet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2Inner_covGrad_self_eq_dirichlet target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma covGrad_l2NormSq_le_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ^ 2 ≤ ‖S‖ ^ 2 := by
  have h_coe_norm :
      ‖((covGrad (I := I) (M := M) g r s S.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)‖ =
        ‖(covGrad (I := I) (M := M) g r s S.toCcTensor :
          SmoothCcTensor g r (s + 1))‖ :=
    UniformSpace.Completion.norm_coe _
  rw [h_coe_norm]
  rw [SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)
    (covGrad (I := I) (M := M) g r s S.toCcTensor)]
  rw [tensorL2Inner_covGrad_self_eq_dirichlet (I := I) (M := M) g r s S.toCcTensor]
  rw [SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S]
  rw [tensorH1Inner_def]
  have h_l2_nonneg :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
            S.toCcTensor.toFun S.toCcTensor.toFun :=
    tensorL2Inner_nonneg (I := I) (M := M) g r s S.toCcTensor.toFun
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_l2NormSq_le_h1NormSq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_l2NormSq_le_h1NormSq target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma covGrad_l2Norm_le_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ≤ ‖S‖ := by
  have h_sq := covGrad_l2NormSq_le_h1NormSq (I := I) (M := M) g r s S
  have h_rhs_nn : 0 ≤ ‖S‖ := norm_nonneg _
  exact (abs_le_of_sq_le_sq' h_sq h_rhs_nn).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_l2Norm_le_h1Norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_l2Norm_le_h1Norm target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma covGrad_l2Norm_le_one_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ‖((covGrad (I := I) (M := M) g r s S.toCcTensor : SmoothCcTensor g r (s + 1)) :
        TensorL2 r (s + 1) g)‖ ≤ 1 * ‖S‖ := by
  rw [one_mul]
  exact covGrad_l2Norm_le_h1Norm (I := I) (M := M) g r s S

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_l2Norm_le_one_mul_h1Norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_l2Norm_le_one_mul_h1Norm target :: scope.openDecls } }

noncomputable def covGradL2Lin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] TensorL2 r (s + 1) g where
  toFun w :=
    ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
  map_add' w₁ w₂ := by
    change ((covGrad (I := I) (M := M) g r s (w₁ + w₂).toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) =
        ((covGrad (I := I) (M := M) g r s w₁.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) +
          ((covGrad (I := I) (M := M) g r s w₂.toCcTensor :
              SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
    rw [SmoothCcTensorH1.toCcTensor_add,
      covGrad_add (I := I) (M := M) g r s w₁.toCcTensor w₂.toCcTensor]
    exact UniformSpace.Completion.coe_add _ _
  map_smul' c w := by
    change ((covGrad (I := I) (M := M) g r s (c • w).toCcTensor :
          SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) =
        c • ((covGrad (I := I) (M := M) g r s w.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g)
    rw [SmoothCcTensorH1.toCcTensor_smul,
      covGrad_smul (I := I) (M := M) g r s c w.toCcTensor]
    exact UniformSpace.Completion.coe_smul _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma covGradL2Lin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    covGradL2Lin (I := I) (M := M) g r s w =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin_apply


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma covGradL2Lin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    ‖covGradL2Lin (I := I) (M := M) g r s w‖ ≤ 1 * ‖w‖ := by
  rw [covGradL2Lin_apply]
  exact covGrad_l2Norm_le_one_mul_h1Norm (I := I) (M := M) g r s w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGradL2Lin_norm_le target :: scope.openDecls } }

noncomputable def tensorCovGradL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensorH1 g r s →L[ℝ] TensorL2 r (s + 1) g :=
  (covGradL2Lin (I := I) (M := M) g r s).mkContinuous 1
    (fun w => covGradL2Lin_norm_le (I := I) (M := M) g r s w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2 ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
@[simp] lemma tensorCovGradL2_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2 (I := I) (M := M) g r s w =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_apply

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    DenseRange (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.denseRange_smoothToTensorH1Compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.denseRange_smoothToTensorH1Compl target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorH1Compl
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.isUniformInducing_smoothToTensorH1Compl target :: scope.openDecls } }

noncomputable def tensorCovGradL2Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorL2 r (s + 1) g :=
  ContinuousLinearMap.extend (tensorCovGradL2 (I := I) (M := M) g r s)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorCovGradL2Compl_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2Compl (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
      tensorCovGradL2 (I := I) (M := M) g r s w := by
  unfold tensorCovGradL2Compl
  exact ContinuousLinearMap.extend_eq
    (tensorCovGradL2 (I := I) (M := M) g r s)
    (e := smoothToTensorH1Compl (I := I) (M := M) g r s)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl (I := I) (M := M) g r s) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) :
    tensorCovGradL2Compl (I := I) (M := M) g r s
        (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
      ((covGrad (I := I) (M := M) g r s w.toCcTensor :
        SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) := by
  rw [tensorCovGradL2Compl_smoothToTensorH1Compl (I := I) (M := M) g r s w,
    tensorCovGradL2_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorCovGradL2_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ‖tensorCovGradL2 (I := I) (M := M) g r s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le (covGradL2Lin (I := I) (M := M) g r s)
    zero_le_one (fun w => covGradL2Lin_norm_le (I := I) (M := M) g r s w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_opNorm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_opNorm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_opNorm_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_opNorm_le_one


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorCovGradL2Compl_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : TensorH1Compl g r s) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s x‖ ≤ ‖x‖ := by
  have h_closed :
      IsClosed {y : TensorH1Compl g r s |
        ‖tensorCovGradL2Compl (I := I) (M := M) g r s y‖ ≤ ‖y‖} :=
    isClosed_le
      ((tensorCovGradL2Compl (I := I) (M := M) g r s).continuous.norm)
      continuous_norm
  have h_dense :
      ∀ w : SmoothCcTensorH1 g r s,
        ‖tensorCovGradL2Compl (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s w)‖ ≤
          ‖smoothToTensorH1Compl (I := I) (M := M) g r s w‖ := by
    intro w
    have h_rhs :
        ‖smoothToTensorH1Compl (I := I) (M := M) g r s w‖ = ‖w‖ := by
      rw [smoothToTensorH1Compl_apply, UniformSpace.Completion.norm_coe]
    have h_lhs :
        tensorCovGradL2Compl (I := I) (M := M) g r s
            (smoothToTensorH1Compl (I := I) (M := M) g r s w) =
          ((covGrad (I := I) (M := M) g r s w.toCcTensor :
            SmoothCcTensor g r (s + 1)) : TensorL2 r (s + 1) g) :=
      tensorCovGradL2Compl_smoothToTensorH1Compl_eq_coe (I := I) (M := M)
        g r s w
    rw [h_lhs, h_rhs]
    exact covGrad_l2Norm_le_h1Norm (I := I) (M := M) g r s w
  exact (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s).induction_on
    x h_closed h_dense

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_apply_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_apply_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_apply_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_apply_norm_le


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorCovGradL2Compl_opNorm_le_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by
      rw [one_mul]
      exact tensorCovGradL2Compl_apply_norm_le (I := I) (M := M) g r s x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_opNorm_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_opNorm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_opNorm_le_one ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2Compl_opNorm_le_one


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorCovGradL2_inner_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : SmoothCcTensorH1 g r s) (T : SmoothCcTensor g r (s + 1)) :
    ⟪tensorCovGradL2 (I := I) (M := M) g r s w, (T : TensorL2 r (s + 1) g)⟫_ℝ =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r (s + 1) x
          ((covGrad (I := I) (M := M) g r s w.toCcTensor).toFun x)
          (T.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorCovGradL2_apply]
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def
      (covGrad (I := I) (M := M) g r s w.toCcTensor) T]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_inner_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_inner_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_inner_smooth ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovGradL2_inner_smooth

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
