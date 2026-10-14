import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.FiberNormIdentity
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.CurvatureControlledSecondOrder
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.CurvatureDefect
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Submission.DifferentialGeometry.Analysis.Integration.L2.Tensor.FiberNormBounds
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.Tensor.Pointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section NormedL2Bounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private lemma sum_three_sq_le_sq_sum
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2 := by
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.sum_three_sq_le_sq_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.sum_three_sq_le_sq_sum target :: scope.openDecls } }

private lemma scale_sum_three_sq_le
    {C a b c : ℝ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2) :
    C ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (C * (a + b + c)) ^ 2 := by
  calc
    C ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ C ^ 2 * (a + b + c) ^ 2 :=
      mul_le_mul_of_nonneg_left h (sq_nonneg C)
    _ = (C * (a + b + c)) ^ 2 := by ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.scale_sum_three_sq_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.scale_sum_three_sq_le target :: scope.openDecls } }

private lemma nonneg_le_of_sq_le_sq
    {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  nlinarith [sq_nonneg (a - b)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.nonneg_le_of_sq_le_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.nonneg_le_of_sq_le_sq target :: scope.openDecls } }


omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorL2Norm_le_of_pointwise_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x))) :
    tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun ≤
      C₀ * (tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun +
        tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun +
        tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun) := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T₀ with hS_def
  set Hess : SmoothCcTensor g 0 (3 + 1) :=
    covGrad (I := I) (M := M) g 0 3 (covGrad (I := I) (M := M) g 0 2 T₀) with hHess_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun with hnT_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 S.toFun with hnGrad_def
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1) Hess.toFun with hnHess_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun with hnCurv_def
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (3 + 1) _
  have hnCurv_nn : 0 ≤ nCurv := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hbridgeT : nT ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ := by
    rw [hnT_def, hμ_def]
    have hfun : T₀.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 2) (x := x) (T₀.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 2 _
  have hbridgeGrad : nGrad ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ := by
    rw [hnGrad_def, hμ_def]
    have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3) (x := x) (S.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 3 _
  have hbridgeHess : nHess ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x) ∂μ := by
    rw [hnHess_def, hμ_def]
    have hfun : Hess.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3 + 1) (x := x) (Hess.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) _
  have hbridgeCurv : nCurv ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ := by
    rw [hnCurv_def, hμ_def]
    have hfun : Curv.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := 0) (s := 3) (x := x) (Curv.toSection x) := rfl
    rw [hfun]
    exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g 0 3 _
  have hintT := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 2 T₀
  have hintGrad := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 3 S
  have hintHess := integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g 0 (3 + 1) Hess
  set RHS : M → ℝ := fun x =>
    C₀ ^ 2 *
      (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) +
        riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x))
    with hRHS_def
  have hRHS_int : MeasureTheory.Integrable RHS μ := by
    rw [hRHS_def, hμ_def]
    exact ((hintT.add hintGrad).add hintHess).const_mul (C₀ ^ 2)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ≤ RHS x := by
    intro x
    rw [hRHS_def, hS_def, hHess_def]
    exact hpt x
  have hcurv_nn : (0 : M → ℝ) ≤ᵐ[μ]
      (fun x => riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x)) :=
    Filter.Eventually.of_forall (fun x =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 3 x _)
  have hint_le :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ) ≤
        ∫ x, RHS x ∂μ :=
    MeasureTheory.integral_mono_of_nonneg hcurv_nn hRHS_int
      (Filter.Eventually.of_forall hpt')
  have hRHS_integral :
      (∫ x, RHS x ∂μ) =
        C₀ ^ 2 *
          ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              (Hess.toSection x) ∂μ)) := by
    rw [hRHS_def]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hsplit12 :
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) ∂μ) =
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) :=
      MeasureTheory.integral_add hintT hintGrad
    have hsplit123 :
        (∫ x, ((riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x (Hess.toSection x)) ∂μ) =
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x)) ∂μ) +
            (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              (Hess.toSection x) ∂μ) :=
      MeasureTheory.integral_add (hintT.add hintGrad) hintHess
    rw [hsplit123, hsplit12]
  have hsq_bound : nCurv ^ 2 ≤ C₀ ^ 2 * (nT ^ 2 + nGrad ^ 2 + nHess ^ 2) := by
    rw [hbridgeCurv, hbridgeT, hbridgeGrad, hbridgeHess]
    calc (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (Curv.toSection x) ∂μ)
        ≤ ∫ x, RHS x ∂μ := hint_le
      _ = C₀ ^ 2 *
            ((∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 3 x (S.toSection x) ∂μ) +
              (∫ x, riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
                (Hess.toSection x) ∂μ)) := hRHS_integral
  clear_value nT nGrad nHess nCurv
  have hy_nn : 0 ≤ C₀ * (nT + nGrad + nHess) :=
    mul_nonneg hC₀ (by linarith [hnT_nn, hnGrad_nn, hnHess_nn])
  have hfinal_sq : nCurv ^ 2 ≤ (C₀ * (nT + nGrad + nHess)) ^ 2 := by
    exact hsq_bound.trans
      (scale_sum_three_sq_le (sum_three_sq_le_sq_sum hnT_nn hnGrad_nn hnHess_nn))
  exact nonneg_le_of_sq_le_sq hy_nn hfinal_sq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_le_of_pointwise_fiberNormSq_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_le_of_pointwise_fiberNormSq_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_le_of_pointwise_fiberNormSq_bound ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_le_of_pointwise_fiberNormSq_bound

end NormedL2Bounds

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_2 : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_2 : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_3 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instMeasurableSpace_differentialGeometry_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_3 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.instBorelSpace_differentialGeometry_3 target :: scope.openDecls } }


theorem secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGradRoughLapCurv (I := I) (M := M) g T₀).toSection x) ≤
        C₀ ^ 2 *
          (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T₀.toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g 0 (3 + 1) x
              ((covGrad (I := I) (M := M) g 0 3
                (covGrad (I := I) (M := M) g 0 2 T₀)).toSection x))) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      (2 + 3 * C₀ + 2 * C₀ ^ 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T₀.toFun ^ 2) := by
  refine secondCovGrad_l2NormSq_le_rawConnLap_covariantTensor (I := I) (M := M) g T₀
    (covGradRoughLapCurv (I := I) (M := M) g T₀) C₀ hC₀
    (covGradRoughLap_commutator_eq (I := I) (M := M) g T₀) ?_
  exact tensorL2Norm_le_of_pointwise_fiberNormSq_bound (I := I) (M := M) g T₀
    (covGradRoughLapCurv (I := I) (M := M) g T₀) C₀ hC₀ hpt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound ``Submission.DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_of_pointwise_curv_bound

end Elliptic
end Analysis
end DifferentialGeometry

end
