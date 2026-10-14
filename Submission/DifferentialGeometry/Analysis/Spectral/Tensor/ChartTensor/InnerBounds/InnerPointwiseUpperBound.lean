import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerUpperBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

section UpperBoundViaTwist

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ T : TensorRSModel r s ℝ E,
          tensorInnerPointwise (I := I) (M := M) g r s b
              (chartRSTwist (I := I) (M := M) α b r s T)
              (chartRSTwist (I := I) (M := M) α b r s T) ≤
            C * ‖T‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_chart⟩ :=
    exists_chartTensorInnerPointwise_rs_model_upper_bound_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro b hb T
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have h := h_chart b hb T
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_tensorInnerPointwise_le_chartRSTwistInv_norm_sq_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ S : TensorRSModel r s ℝ E,
          tensorInnerPointwise (I := I) (M := M) g r s b S S ≤
            C * ‖chartRSTwistInv (I := I) (M := M) α b r s S‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_twist⟩ :=
    exists_tensorInnerPointwise_chartRSTwist_upper_bound_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro b hb S
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  set T : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s S with hT_def
  have h_round : chartRSTwist (I := I) (M := M) α b r s T = S := by
    rw [hT_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s S
  have h := h_twist b hb T
  rw [h_round] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_chartRSTwistInv_norm_sq_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_chartRSTwistInv_norm_sq_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_chartRSTwistInv_norm_sq_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_chartRSTwistInv_norm_sq_on_pouTsupport

end UpperBoundViaTwist

section UpperBoundViaTrivProj

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_tensorInnerPointwise_le_tensorTrivProj_norm_sq_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        b ∈ tsupport (fun x : M =>
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) ≤
            C * ‖tensorTrivProj (I := I) (M := M) (E := E) g r s S α b‖ ^ 2 := by
  classical
  obtain ⟨C, hC_nn, h_inv⟩ :=
    exists_tensorInnerPointwise_le_chartRSTwistInv_norm_sq_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S b hb
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have h := h_inv b hb (S.toFun b)
  have h_proj := tensorTrivProj_eq_chartRSTwistInv_toFun
    (I := I) (M := M) g r s α S hb_base
  rw [← h_proj] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_tensorTrivProj_norm_sq_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_tensorTrivProj_norm_sq_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_tensorTrivProj_norm_sq_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_tensorInnerPointwise_le_tensorTrivProj_norm_sq_on_pouTsupport

end UpperBoundViaTrivProj

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
