import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normSq0S_sub_smul_metricTensor0S
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (a : ℝ) :
    normSq0S g x 2 (A - a • metricTensor0S g x) =
      normSq0S g x 2 A - 2 * a * metricTracePair0SAt g A +
        a ^ 2 * (Module.finrank ℝ E : ℝ) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  have hinv : MetricInverseInBasis g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hmetric : normSq0S g x 2 (metricTensor0S g x) =
      (Module.finrank ℝ E : ℝ) := by
    change normSq0S g x 2 (metricTensor0S g x) =
      (Module.finrank ℝ (TangentSpace I x) : ℝ)
    simpa only [Fintype.card_fin] using
      normSq0S_metricTensor0S_eq_card g basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinv
  rw [_root_.Submission.Tensor0SBundle.normSq0S_sub,
    _root_.Submission.Tensor0SBundle.inner0S_smul_right,
    normSq0S_eq_inner (A := a • metricTensor0S g x), _root_.Submission.Tensor0SBundle.inner0S_smul_left,
    _root_.Submission.Tensor0SBundle.inner0S_smul_right, ← normSq0S_eq_inner, hmetric]
  rw [inner0S_symm g x A (metricTensor0S g x)]
  change _ = _
  dsimp only [metricTracePair0SAt]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.normSq0S_sub_smul_metricTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.normSq0S_sub_smul_metricTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.normSq0S_sub_smul_metricTensor0S ``Submission.DifferentialGeometry.Tensor0SBundle.normSq0S_sub_smul_metricTensor0S

end DifferentialGeometry.Tensor0SBundle
