import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.CovNormBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
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

omit [CompactSpace M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
private lemma
    chartWeight_mul_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (w : M → ℝ) (hw_nn : ∀ x, 0 ≤ w x) (hw_le_one : ∀ x, w x ≤ 1)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hw_support : tsupport w ⊆ K_M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        w b ^ 2 *
            (∑ i : Fin (Module.finrank ℝ E),
              ‖chartRSTwistInv (I := I) (M := M) α b r s
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S b
                      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2) ≤
          C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b := by
  classical
  obtain ⟨C, hC_nn, h_sum⟩ :=
    exists_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner_on_compact
      (I := I) (M := M) g r s α hK_M_compact hK_M_sub_baseSet
  refine ⟨C, hC_nn, ?_⟩
  intro S b
  set SqSum : ℝ :=
    ∑ i : Fin (Module.finrank ℝ E),
      ‖chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2 with hSqSum_def
  set Q : ℝ :=
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S b with hQ_def
  have hSqSum_nn : 0 ≤ SqSum := by
    rw [hSqSum_def]
    refine Finset.sum_nonneg ?_
    intro i _
    exact sq_nonneg _
  have hQ_nn : 0 ≤ Q := by
    rw [hQ_def]
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s S b
  by_cases hb : b ∈ K_M
  · have hw_b_nn : 0 ≤ w b := hw_nn b
    have hw_b_le_one : w b ≤ 1 := hw_le_one b
    have hw_sq_le_one : w b ^ 2 ≤ 1 := by
      have hsq : w b * w b ≤ 1 * 1 :=
        mul_le_mul hw_b_le_one hw_b_le_one hw_b_nn (by linarith)
      have hsq' : w b * w b ≤ 1 := by linarith
      rw [sq]; exact hsq'
    have hSqSum_le : SqSum ≤ C * Q := by
      rw [hSqSum_def, hQ_def]
      exact h_sum S hb
    have hCQ_nn : 0 ≤ C * Q := mul_nonneg hC_nn hQ_nn
    calc w b ^ 2 * SqSum
        ≤ 1 * (C * Q) :=
          mul_le_mul hw_sq_le_one hSqSum_le hSqSum_nn (by linarith)
      _ = C * Q := one_mul _
  · have hw_zero : w b = 0 := by
      by_contra hne
      exact hb (hw_support (subset_tsupport _ hne))
    have hLHS_zero : w b ^ 2 * SqSum = 0 := by
      rw [hw_zero]; ring
    rw [hLHS_zero]
    exact mul_nonneg hC_nn hQ_nn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartWeight_mul_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartWeight_mul_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner target :: scope.openDecls } }

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : _root_.MeasureTheory.Measure α) (f : α → ℝ) :
    (_root_.MeasureTheory.eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine _root_.MeasureTheory.lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_eLpNorm_two_eq_lintegral_enorm_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_eLpNorm_two_eq_lintegral_enorm_sq target :: scope.openDecls } }

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sqrt_of_sq_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.le_sqrt_of_sq_le target :: scope.openDecls } }

private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_ofReal_eq_ofReal_sqrt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_ofReal_eq_ofReal_sqrt target :: scope.openDecls } }

private lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (_root_.MeasureTheory.eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_two_le_ofReal_sqrt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_two_le_ofReal_sqrt target :: scope.openDecls } }

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm x]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma integral_tensorCovDerivPointwiseInner_le_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ∫ b, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        S.toCcTensor S.toCcTensor b
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ‖S‖ ^ 2 := by
  classical
  have h_norm_sq :
      ‖S‖ ^ 2 =
        tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor :=
    SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
            S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine _root_.MeasureTheory.integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  rw [h_norm_sq, tensorH1Inner_def]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.integral_tensorCovDerivPointwiseInner_le_h1NormSq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.integral_tensorCovDerivPointwiseInner_le_h1NormSq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
private lemma sq_eLpNorm_chartWeight_mul_sqrt_sum_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (w : M → ℝ) (hw_nn : ∀ x, 0 ≤ w x) (hw_le_one : ∀ x, w x ≤ 1)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hw_support : tsupport w ⊆ K_M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        (_root_.MeasureTheory.eLpNorm
            (fun b : M =>
              w b *
                Real.sqrt
                  (∑ i : Fin (Module.finrank ℝ E),
                    ‖chartRSTwistInv (I := I) (M := M) α b r s
                        (TensorRSSpace.toModel
                          (tensorCovDerivAt (I := I) (M := M) g r s
                            S.toCcTensor b
                            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C * ‖S‖ ^ 2) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    chartWeight_mul_sum_chartRSTwistInv_cov_sq_norm_le_const_mul_tensorCovDerivPointwiseInner
      (I := I) (M := M) g r s α w hw_nn hw_le_one hK_M_compact hK_M_sub_baseSet
      hw_support
  refine ⟨C, hC_nn, ?_⟩
  intro S
  set ρ : M → ℝ := w with hρ_def
  set SqSum : M → ℝ := fun b : M =>
    ∑ i : Fin (Module.finrank ℝ E),
      ‖chartRSTwistInv (I := I) (M := M) α b r s
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S.toCcTensor b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2 with hSqSum_def
  set f : M → ℝ := fun b : M => ρ b * Real.sqrt (SqSum b) with hf_def
  set μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have hSqSum_nn : ∀ b : M, 0 ≤ SqSum b := by
    intro b
    rw [hSqSum_def]
    refine Finset.sum_nonneg ?_
    intro i _
    exact sq_nonneg _
  have h_pt_sq : ∀ b : M, (f b) ^ 2 ≤
      C * tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        S.toCcTensor S.toCcTensor b := by
    intro b
    have h_eq : (f b) ^ 2 = ρ b ^ 2 * SqSum b := by
      rw [hf_def, mul_pow]
      rw [show Real.sqrt (SqSum b) ^ 2 = SqSum b from Real.sq_sqrt (hSqSum_nn b)]
    rw [h_eq]
    exact h_pt S.toCcTensor b
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt_sq b)
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
  have h_grad_int :
      _root_.MeasureTheory.Integrable (tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor) μ :=
    tensorCovDerivPointwiseInner_integrable
      (I := I) (M := M) g r s S.toCcTensor S.toCcTensor
  have h_C_smul_int :
      _root_.MeasureTheory.Integrable (fun b : M => C *
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          S.toCcTensor S.toCcTensor b) μ :=
    h_grad_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C *
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          S.toCcTensor S.toCcTensor b) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s _ b)
  have h_lint_le :
      ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
        ∫⁻ b, ENNReal.ofReal (C * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b) ∂μ := by
    refine _root_.MeasureTheory.lintegral_mono_ae ?_
    filter_upwards with b using h_pt_enn b
  have h_lint_eq :
      ∫⁻ b, ENNReal.ofReal (C * tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b) ∂μ =
        ENNReal.ofReal (∫ b, C * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm
  rw [h_lint_eq] at h_lint_le
  have h_int_const_mul :
      ∫ b, C * tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ =
        C * ∫ b, tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ :=
    _root_.MeasureTheory.integral_const_mul _ _
  rw [h_int_const_mul] at h_lint_le
  have h_int_le :
      ∫ b, tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ ≤
      ‖S‖ ^ 2 :=
    integral_tensorCovDerivPointwiseInner_le_h1NormSq
      (I := I) (M := M) g r s S
  have h_norm_sq_nn : 0 ≤ ‖S‖ ^ 2 := sq_nonneg _
  have h_RHS_le :
      ENNReal.ofReal (C *
        ∫ b, tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S.toCcTensor S.toCcTensor b ∂μ) ≤
        ENNReal.ofReal (C * ‖S‖ ^ 2) := by
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_left h_int_le hC_nn
  exact h_lint_le.trans h_RHS_le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_eLpNorm_chartWeight_mul_sqrt_sum_le_const_mul_h1NormSq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_eLpNorm_chartWeight_mul_sqrt_sum_le_const_mul_h1NormSq target :: scope.openDecls } }

omit [CompactSpace M] [NeZero (Module.finrank ℝ E)] in
theorem exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (w : M → ℝ) (hw_nn : ∀ x, 0 ≤ w x) (hw_le_one : ∀ x, w x ≤ 1)
    {K_M : Set M} (hK_M_compact : IsCompact K_M)
    (hK_M_sub_baseSet :
      K_M ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (hw_support : tsupport w ⊆ K_M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        _root_.MeasureTheory.eLpNorm
            (fun b : M =>
              w b *
                Real.sqrt
                  (∑ i : Fin (Module.finrank ℝ E),
                    ‖chartRSTwistInv (I := I) (M := M) α b r s
                        (TensorRSSpace.toModel
                          (tensorCovDerivAt (I := I) (M := M) g r s
                            S.toCcTensor b
                            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_chartWeight_mul_sqrt_sum_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α w hw_nn hw_le_one hK_M_compact hK_M_sub_baseSet
      hw_support
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S
  set T : ℝ := C * ‖S‖ ^ 2 with hT_def
  have hT_nn : 0 ≤ T := mul_nonneg hC_nn (sq_nonneg _)
  have h_eLpNorm_le :=
    eLpNorm_two_le_ofReal_sqrt hT_nn (h_sq S)
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_factor :
      Real.sqrt T = Real.sqrt C * ‖S‖ := by
    rw [hT_def, Real.sqrt_mul hC_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring,
      Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  rw [show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
    (coe_nnnorm_eq_ofReal_norm S).symm] at h_eLpNorm_le
  exact h_eLpNorm_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        _root_.MeasureTheory.eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ i : Fin (Module.finrank ℝ E),
                    ‖chartRSTwistInv (I := I) (M := M) α b r s
                        (TensorRSSpace.toModel
                          (tensorCovDerivAt (I := I) (M := M) g r s
                            S.toCcTensor b
                            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i b)))‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  exists_eLpNorm_chartWeight_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
    (I := I) (M := M) g r s α
    (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    (fun x => (chartAtlasPOU I M).nonneg α x)
    (fun x => (chartAtlasPOU I M).le_one α x)
    ((isClosed_tsupport _).isCompact)
    (by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      exact (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α hx)
    (subset_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
