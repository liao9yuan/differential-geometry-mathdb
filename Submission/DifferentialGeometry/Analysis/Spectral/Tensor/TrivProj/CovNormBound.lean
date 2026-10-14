import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerCovDiagonalBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerPointwiseUpperBound

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

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

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

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ K_M →
        ∀ X : TensorRSModel r s ℝ E,
          ‖chartRSTwistInv (I := I) (M := M) α b r s X‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b X X := by
  classical
  obtain ⟨K, hK_nn, h_chart⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_compact
      (I := I) (M := M) (E := E) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨K, hK_nn, ?_⟩
  intro b hb X
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    hK_M_sub_baseSet hb
  set T : TensorRSModel r s ℝ E :=
    chartRSTwistInv (I := I) (M := M) α b r s X with hT_def
  have h_T : ‖T‖ ^ 2 ≤ K *
      chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T T :=
    h_chart b hb T
  have h_bridge :
      chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b T T =
        tensorInnerPointwise (I := I) (M := M) g r s b
          (chartRSTwist (I := I) (M := M) α b r s T)
          (chartRSTwist (I := I) (M := M) α b r s T) :=
    chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
      (I := I) (M := M) g r s α hb_base T T
  have h_round : chartRSTwist (I := I) (M := M) α b r s T = X := by
    rw [hT_def]
    exact chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s X
  rw [h_bridge, h_round] at h_T
  exact h_T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact

omit [CompactSpace M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ K_M →
        ∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2 ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
  classical
  obtain ⟨K, hK_nn, h_per⟩ :=
    chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  obtain ⟨C', hC'_nn, h_diag⟩ :=
    exists_sum_tensorInner_cov_chartBasis_diagonal_le_const_mul_covDerivInner_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨K * C', mul_nonneg hK_nn hC'_nn, ?_⟩
  intro S b hb
  set cov : Fin (Module.finrank ℝ E) → TensorRSModel r s ℝ E := fun i =>
    TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)) with hcov_def
  set D : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b (cov i) (cov i) with hD_def
  have h_D_le : D ≤ C' * tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s S S b := by
    rw [hD_def]
    exact h_diag S hb
  have h_sum_le_KD :
      ∑ i : Fin (Module.finrank ℝ E),
          ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2 ≤
        K * D := by
    rw [hD_def, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    exact h_per hb (cov i)
  have h_KD_le : K * D ≤
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) :=
    mul_le_mul_of_nonneg_left h_D_le hK_nn
  have h_assoc :
      K * (C' * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b) =
        (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
    ring
  calc ∑ i : Fin (Module.finrank ℝ E),
        ‖chartRSTwistInv (I := I) (M := M) α b r s (cov i)‖ ^ 2
      ≤ K * D := h_sum_le_KD
    _ ≤ K * (C' * tensorCovDerivPointwiseInner
              (I := I) (M := M) g r s S S b) := h_KD_le
    _ = (K * C') *
          tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := h_assoc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∀ X : TensorRSModel r s ℝ E,
          ‖chartRSTwistInv (I := I) (M := M) α b r s X‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b X X :=
  chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartRSTwistInv_sq_norm_le_const_mul_tensorInnerPointwise_on_pouTsupport

omit [NeZero (Module.finrank ℝ E)] in
theorem
    exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) →
        ∑ i : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2 ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b :=
  exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact
    (I := I) (M := M) g r s α
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_subset_baseSet (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_pouTsupport

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
