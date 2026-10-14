import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Tensor.RSTensor.BundleTrivialization.ChartJacobianMatrixEntrySmoothness
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Bilinear

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
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
lemma chartJ_self (b : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b) (b := b) (mem_chart_source H b)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b) b
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H b) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_self

omit [Module.Finite ℝ E] in
lemma chartJinv_self (b : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) b).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b) (b := b) (mem_chart_source H b)]
  ext v
  exact (tangentBundleCore I M).coordChange_self (achart H b) b
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H b) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_self ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_self

omit [Module.Finite ℝ E] in
theorem chartJinv_wrapped_continuousAt
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContinuousAt
      (fun b : M =>
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b ∘L
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b
            : E →L[ℝ] E))
      b₀ :=
  (contMDiffAt_tangentTrivialization_coordChangeL_alpha_to_b0 (I := I) (M := M) α hb₀).continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_continuousAt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_continuousAt

omit [Module.Finite ℝ E] in
theorem chartJ_wrapped_continuousAt
    (α : M) {b₀ : M} (hb₀ : b₀ ∈ (chartAt H α).source) :
    ContinuousAt
      (fun b : M =>
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b ∘L
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b
            : E →L[ℝ] E))
      b₀ :=
  (contMDiffAt_tangentTrivialization_coordChangeL_b0_to_alpha (I := I) (M := M) α hb₀).continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_continuousAt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_continuousAt

omit [Module.Finite ℝ E] in
theorem chartJinv_wrapped_centre_eq
    (α : M) (b₀ : M) :
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b₀ ∘L
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b₀
        : E →L[ℝ] E) =
    chartTrivializationLinearMapSymm (I := I) (M := M) α b₀ := by
  rw [chartJ_self (I := I) (M := M) b₀]
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_centre_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_centre_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_centre_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJinv_wrapped_centre_eq

omit [Module.Finite ℝ E] in
theorem chartJ_wrapped_centre_eq
    (α : M) (b₀ : M) :
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b₀ ∘L
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) b₀).symmL ℝ b₀
        : E →L[ℝ] E) =
    chartTrivializationLinearMap (I := I) (M := M) α b₀ := by
  rw [chartJinv_self (I := I) (M := M) b₀]
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_centre_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_centre_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_centre_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartJ_wrapped_centre_eq

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
