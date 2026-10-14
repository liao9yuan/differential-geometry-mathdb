import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2Bound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.NormComparison
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound
import Submission.DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartTensorInner_tensorTrivProj_eq_tensorInner_toFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    chartTensorInnerPointwiseRsModel (I := I) (M := M) g r s α b
        (tensorTrivProj (I := I) (M := M) g r s S α b)
        (tensorTrivProj (I := I) (M := M) g r s S α b) =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := by
  classical
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
    (I := I) (M := M) g r s α hb _ _]
  rw [tensorTrivProj_eq_chartRSTwistInv_toFun (I := I) (M := M) g r s α S hb]
  rw [chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb r s (S.toFun b)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorInner_tensorTrivProj_eq_tensorInner_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorInner_tensorTrivProj_eq_tensorInner_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorInner_tensorTrivProj_eq_tensorInner_toFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartTensorInner_tensorTrivProj_eq_tensorInner_toFun

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tensorTrivProj_norm_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (S : SmoothCcTensor g r s) (b : M),
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          ‖tensorTrivProj (I := I) (M := M) g r s S α b‖ ^ 2 ≤
            K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    chartTrivializationNorm_le_const_mul_chartTensorInnerPointwise_rs_model_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨K, hK_nn, ?_⟩
  intro S b hb
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have h := h_norm b hb (tensorTrivProj (I := I) (M := M) g r s S α b)
  rwa [chartTensorInner_tensorTrivProj_eq_tensorInner_toFun
    (I := I) (M := M) g r s α S hb_base] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_norm_sq_le_const_mul_tensorInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_norm_sq_le_const_mul_tensorInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_norm_sq_le_const_mul_tensorInner ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorTrivProj_norm_sq_le_const_mul_tensorInner

noncomputable def chartComponentProjectionUniformBound (r s : ℕ) : ℝ :=
  ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
    ‖tensorChartComponentProjection (E := E) r s p.1 p.2‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound

omit [NeZero (Module.finrank ℝ E)] in
lemma chartComponentProjectionUniformBound_nonneg (r s : ℕ) :
    0 ≤ chartComponentProjectionUniformBound (E := E) r s :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartComponentProjectionUniformBound_nonneg

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorChartComponentProjection_norm_le_uniform (r s : ℕ)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ ≤
      chartComponentProjectionUniformBound (E := E) r s := by
  classical
  set V : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E))) := Finset.univ
  have hmem : (Idx, Jdx) ∈ V := Finset.mem_univ _
  have h_split :
      chartComponentProjectionUniformBound (E := E) r s =
        ‖tensorChartComponentProjection (E := E) r s Idx Jdx‖ +
          ∑ p ∈ V.erase (Idx, Jdx),
            ‖tensorChartComponentProjection (E := E) r s p.1 p.2‖ := by
    unfold chartComponentProjectionUniformBound
    rw [← Finset.sum_erase_add _ _ hmem, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ p ∈ V.erase (Idx, Jdx),
        ‖tensorChartComponentProjection (E := E) r s p.1 p.2‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentProjection_norm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentProjection_norm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentProjection_norm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentProjection_norm_le_uniform

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tensorChartComponentScalar_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
        (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hsc_eq : tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx b = ρ b * P_IJ T := rfl
  by_cases hb : b ∈ tsupport ρ
  · have hρ_nn : 0 ≤ ρ b := (chartAtlasPOU I M).nonneg α b
    have hρ_le_one : ρ b ≤ 1 := (chartAtlasPOU I M).le_one α b
    have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
          (norm_nonneg _))
    have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
      have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [h_abs]
      have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
      have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by
        ring
      have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
      linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
    have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := h_norm S b hb
    have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
    have h_chain_sq : (P_IJ T) ^ 2 ≤
        C_proj ^ 2 *
          (K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b)) := by
      have h_mul := mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn
      exact h_proj_sq_le.trans h_mul
    have h_ρ_sq_le_one : ρ b ^ 2 ≤ 1 := by
      have h := mul_le_mul hρ_le_one hρ_le_one hρ_nn (by linarith)
      rw [sq]; linarith
    have h_KQ_nn : 0 ≤
        K * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := mul_nonneg hK_nn hQ_nn
    have h_rhs_inner_nn : 0 ≤
        C_proj ^ 2 *
          (K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b)) :=
      mul_nonneg hC_proj_sq_nn h_KQ_nn
    have h_factored : ρ b ^ 2 * (P_IJ T) ^ 2 ≤
        1 *
          (C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toFun b) (S.toFun b))) :=
      mul_le_mul h_ρ_sq_le_one h_chain_sq (sq_nonneg _) (by linarith)
    rw [hsc_eq, mul_pow]
    have h_rhs_rearr :
        1 *
          (C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toFun b) (S.toFun b))) =
          C_proj ^ 2 * K *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by ring
    linarith [h_factored, h_rhs_rearr.le, h_rhs_rearr.symm.le]
  · have hρ_zero : ρ b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    rw [hsc_eq, hρ_zero, _root_.MulZeroClass.zero_mul]
    have hC_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
    have h_KQ_nn : 0 ≤ K * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := mul_nonneg hK_nn hQ_nn
    have h_RHS_nn : 0 ≤ C_proj ^ 2 * K *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      have := mul_nonneg hC_sq_nn h_KQ_nn
      have heq : C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) =
          C_proj ^ 2 *
            (K * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b)) := by ring
      linarith [heq.le, heq.symm.le]
    have hzero_sq : (0 : ℝ) ^ 2 = 0 := by ring
    rw [hzero_sq]
    exact h_RHS_nn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_sq_le_const_mul_tensorInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_sq_le_const_mul_tensorInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_sq_le_const_mul_tensorInner ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_sq_le_const_mul_tensorInner

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma tensorChartComponentRaw_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        (tensorChartComponentRaw (I := I) (M := M)
            g r s S α Idx Jdx b) ^ 2 ≤
          C * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b hb
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
      (S.toFun b) (S.toFun b) :=
    tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have hraw_eq : tensorChartComponentRaw (I := I) (M := M)
      g r s S α Idx Jdx b = P_IJ T := rfl
  have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
        (norm_nonneg _))
  have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
    have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_abs]
    have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
    have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by ring
    have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
    linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
  have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := h_norm S b hb
  have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
  have h_chain_sq : (P_IJ T) ^ 2 ≤
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) :=
    h_proj_sq_le.trans (mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn)
  rw [hraw_eq]
  have h_rhs_rearr :
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) =
        C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  linarith [h_chain_sq, h_rhs_rearr.le, h_rhs_rearr.symm.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_sq_le_const_mul_tensorInner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_sq_le_const_mul_tensorInner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_sq_le_const_mul_tensorInner ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_sq_le_const_mul_tensorInner

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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma sq_eLpNorm_two_le_const_mul_tensorL2Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (_root_.MeasureTheory.eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C *
            tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    tensorChartComponentScalar_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := tensorChartComponentScalar (I := I) (M := M)
    g r s S α Idx Jdx
  set μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
          g r s b (S.toFun b) (S.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
  have h_inner_int := SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M) (g := g) (r := r) (s := s) S S
  have h_C_smul_int :
      _root_.MeasureTheory.Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
  have h_lint_le :
      ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
        ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ := by
    refine _root_.MeasureTheory.lintegral_mono_ae ?_
    filter_upwards with b using h_pt_enn b
  have h_lint_eq :
      ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ =
        ENNReal.ofReal (∫ b, C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm
  rw [h_lint_eq] at h_lint_le
  have h_int_const_mul :
      ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) ∂μ =
        C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    rw [_root_.MeasureTheory.integral_const_mul]
  rw [h_int_const_mul] at h_lint_le
  exact h_lint_le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_eLpNorm_two_le_const_mul_tensorL2Inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sq_eLpNorm_two_le_const_mul_tensorL2Inner target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_two_le_const_mul_tensorL2Inner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    refine _root_.MeasureTheory.integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  set S_total : ℝ := C *
    tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun with hS_total_def
  have hS_total_nn : 0 ≤ S_total := mul_nonneg hC_nn h_inner_nn
  have h_eLpNorm_le :=
    eLpNorm_two_le_ofReal_sqrt hS_total_nn (h_sq S Idx Jdx)
  have h_sqrt_factor :
      Real.sqrt S_total = Real.sqrt C *
        tensorL2Norm (I := I) (M := M) g r s S.toFun := by
    rw [hS_total_def, h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self
        (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun)]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  exact h_eLpNorm_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_uniform

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
