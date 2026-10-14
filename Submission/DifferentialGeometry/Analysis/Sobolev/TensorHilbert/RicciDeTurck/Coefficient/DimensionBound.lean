import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CometricTraceSelf
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalCometric.Extraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Integral.Connection

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

def pccJetC (i : ℕ) : ℝ :=
  operatorFieldApplicationGdiag (E := E) i * (Module.finrank ℝ E : ℝ) ^ 8

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.pccJetC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.pccJetC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.pccJetC ``Submission.DifferentialGeometry.Integral.Connection.pccJetC

def ricciJetC (i : ℕ) : ℝ := (10 / 4 : ℝ) * pccJetC (E := E) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.ricciJetC then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.ricciJetC"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.ricciJetC ``Submission.DifferentialGeometry.Integral.Connection.ricciJetC

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem pccJetC_nonneg (i : ℕ) : 0 ≤ pccJetC (E := E) i := by
  exact mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i) (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.pccJetC_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.pccJetC_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.pccJetC_nonneg ``Submission.DifferentialGeometry.Integral.Connection.pccJetC_nonneg

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem ricciJetC_nonneg (i : ℕ) : 0 ≤ ricciJetC (E := E) i := by
  exact mul_nonneg (by norm_num) (pccJetC_nonneg (E := E) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.ricciJetC_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.ricciJetC_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.ricciJetC_nonneg ``Submission.DifferentialGeometry.Integral.Connection.ricciJetC_nonneg

omit [SigmaCompactSpace M] in
theorem pcc_riemannianFiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x) := by
  have h := pcc_riemannianFiberNormSq_of_bound (I := I) (M := M) g₀ g₁
    (K := (Module.finrank ℝ E : ℝ) ^ 6) (by positivity)
    (fun b => cometricTrace_riemannianFiberNormSq (I := I) (M := M) g₀ b) i x
  convert h using 1
  simp only [pccJetC]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.pcc_riemannianFiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.pcc_riemannianFiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.pcc_riemannianFiberNormSq_le ``Submission.DifferentialGeometry.Integral.Connection.pcc_riemannianFiberNormSq_le

omit [SigmaCompactSpace M] in
theorem ricci_riemannianFiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁
            - ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₀)).toSection x) ≤
      ricciJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x) := by
  refine (ricci_sub_riemannianFiberNormSq (I := I) (M := M) g₀ g₁ i x).trans ?_
  calc
    _ ≤ (10 / 4 : ℝ) * (pccJetC (E := E) i *
          ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x)) :=
      mul_le_mul_of_nonneg_left (pcc_riemannianFiberNormSq_le (I := I) (M := M) g₀ g₁ i x) (by norm_num)
    _ = ricciJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 2 2 j
              (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x) := by
      simp only [ricciJetC]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.ricci_riemannianFiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.ricci_riemannianFiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.ricci_riemannianFiberNormSq_le ``Submission.DifferentialGeometry.Integral.Connection.ricci_riemannianFiberNormSq_le

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem traceCoeff_sub_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g₀ g₁ -
        traceHessianCoeff (I := I) (M := M) g₀ g₀ =
      reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
        traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    traceHessianCoeff_toSection, traceHessianCoeff_toSection,
    reindexCoefficientInputSlots_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [sub_apply, reindexCoefficientInputSlotsFiber_apply,
    deTurckPrincipalCometricCoeff_toSection_clm_eq,
    sub_apply, traceHessianFib, traceHessianFib,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    domDomCongrFib_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.traceCoeff_sub_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.traceCoeff_sub_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.traceCoeff_sub_eq ``Submission.DifferentialGeometry.Integral.Connection.traceCoeff_sub_eq

omit [SigmaCompactSpace M] in
theorem trace_riemannianFiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i
          (traceHessianCoeff (I := I) (M := M) g₀ g₁ -
            traceHessianCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j
            (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x) := by
  rw [traceCoeff_sub_eq (I := I) (M := M) g₀ g₁,
    riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq (I := I) (M := M) g₀ 4 2
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
      traceHessianSlotPerm i x]
  exact pcc_riemannianFiberNormSq_le (I := I) (M := M) g₀ g₁ i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.trace_riemannianFiberNormSq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.trace_riemannianFiberNormSq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.trace_riemannianFiberNormSq_le ``Submission.DifferentialGeometry.Integral.Connection.trace_riemannianFiberNormSq_le

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jetL2_of_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (A : SmoothCcTensor g 4 2)
    (B : SmoothCcTensor g 2 2) (C : ℝ) (i : ℕ)
    (h : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 (2 + i) x
          ((iteratedCovGrad (I := I) g 4 2 i A).toSection x) ≤
        C * ∑ j ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
            ((iteratedCovGrad (I := I) g 2 2 j B).toSection x)) :
    ‖iteratedCovGrad (I := I) g 4 2 i A‖ ^ 2 ≤
      C * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g 2 2 j B‖ ^ 2 := by
  have hF_int : MeasureTheory.Integrable
      (fun x => C * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
          ((iteratedCovGrad (I := I) g 2 2 j B).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (MeasureTheory.integrable_finsetSum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection
        (I := I) (M := M) g 2 (2 + j)
        (iteratedCovGrad (I := I) g 2 2 j B))).const_mul C
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g 4 (2 + i) (iteratedCovGrad (I := I) g 4 2 i A)
    (fun x => C * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g 2 (2 + j) x
        ((iteratedCovGrad (I := I) g 2 2 j B).toSection x)) hF_int h
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finsetSum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 2 (2 + j)
      (iteratedCovGrad (I := I) g 2 2 j B))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g 2 2 j B)]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (I := I) (M := M) g 2 (2 + j)
    (iteratedCovGrad (I := I) g 2 2 j B)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Connection.jetL2_of_riemannianFiberNormSq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Connection.jetL2_of_riemannianFiberNormSq target :: scope.openDecls } }

theorem pcc_l2_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 :=
  jetL2_of_riemannianFiberNormSq (I := I) (M := M) g₀
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
    (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) (pccJetC (E := E) i) i
    (pcc_riemannianFiberNormSq_le (I := I) (M := M) g₀ g₁ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.pcc_l2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.pcc_l2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.pcc_l2_le ``Submission.DifferentialGeometry.Integral.Connection.pcc_l2_le

theorem ricci_l2_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁ -
          ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
      ricciJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 :=
  jetL2_of_riemannianFiberNormSq (I := I) (M := M) g₀
    (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁ -
      ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₀)
    (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) (ricciJetC (E := E) i) i
    (ricci_riemannianFiberNormSq_le (I := I) (M := M) g₀ g₁ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.ricci_l2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.ricci_l2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.ricci_l2_le ``Submission.DifferentialGeometry.Integral.Connection.ricci_l2_le

theorem trace_l2_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (traceHessianCoeff (I := I) (M := M) g₀ g₁ -
          traceHessianCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
      pccJetC (E := E) i * ∑ j ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)‖ ^ 2 :=
  jetL2_of_riemannianFiberNormSq (I := I) (M := M) g₀
    (traceHessianCoeff (I := I) (M := M) g₀ g₁ -
      traceHessianCoeff (I := I) (M := M) g₀ g₀)
    (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) (pccJetC (E := E) i) i
    (trace_riemannianFiberNormSq_le (I := I) (M := M) g₀ g₁ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.trace_l2_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.trace_l2_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.trace_l2_le ``Submission.DifferentialGeometry.Integral.Connection.trace_l2_le

end DifferentialGeometry.Integral.Connection

end
