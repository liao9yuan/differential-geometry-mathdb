import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.SecondOrder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic


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

private lemma second_order_garding_sobolev_curv_real
    {C nGrad nLap nT nHess : ℝ}
    (hC : 0 ≤ C)
    (hstep : nHess ^ 2 ≤ nLap ^ 2 + C * (nT + nGrad + nHess) * nGrad)
    (horder : nGrad ^ 2 ≤ nLap * nT) :
    nHess ^ 2 ≤
      (2 + 3 * C + 2 * C ^ 2) * (nLap ^ 2 + nT ^ 2) := by
  have hgrad_sq_le : nGrad ^ 2 ≤ (nLap ^ 2 + nT ^ 2) / 2 := by
    have hy : nLap * nT ≤ (nLap ^ 2 + nT ^ 2) / 2 := by
      nlinarith [sq_nonneg (nLap - nT)]
    linarith
  have hyoung_hess :
      C * nHess * nGrad ≤ nHess ^ 2 / 2 + C ^ 2 * nGrad ^ 2 / 2 := by
    nlinarith [sq_nonneg (nHess - C * nGrad)]
  have hyoung_TG : nT * nGrad ≤ (nT ^ 2 + nGrad ^ 2) / 2 := by
    nlinarith [sq_nonneg (nT - nGrad)]
  have hstep2 :
      nHess ^ 2 ≤ nLap ^ 2 + nHess ^ 2 / 2 +
        C * (nT * nGrad) + C * nGrad ^ 2 + C ^ 2 * nGrad ^ 2 / 2 := by
    have hexpand : C * (nT + nGrad + nHess) * nGrad =
        C * (nT * nGrad) + C * nGrad ^ 2 + C * nHess * nGrad := by ring
    rw [hexpand] at hstep
    linarith
  have hstep3 :
      nHess ^ 2 ≤ 2 * nLap ^ 2 + 2 * C * (nT * nGrad)
        + 2 * C * nGrad ^ 2 + C ^ 2 * nGrad ^ 2 := by
    linarith
  have hTG_bound : nT * nGrad ≤ nLap ^ 2 / 4 + 3 * nT ^ 2 / 4 := by
    linarith
  have hgrad_term1 :
      2 * C * nGrad ^ 2 ≤ C * nLap ^ 2 + C * nT ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hgrad_sq_le hC
    nlinarith
  have hgrad_term2 :
      C ^ 2 * nGrad ^ 2 ≤ C ^ 2 * nLap ^ 2 / 2 + C ^ 2 * nT ^ 2 / 2 := by
    calc
      C ^ 2 * nGrad ^ 2 ≤ C ^ 2 * ((nLap ^ 2 + nT ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hgrad_sq_le (sq_nonneg C)
      _ = C ^ 2 * nLap ^ 2 / 2 + C ^ 2 * nT ^ 2 / 2 := by ring
  have hTG_term :
      2 * C * (nT * nGrad) ≤ C * nLap ^ 2 / 2 + 3 * C * nT ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hTG_bound hC
    nlinarith
  have hslack_lap :
      0 ≤ 3 * C * nLap ^ 2 / 2 + 3 * C ^ 2 * nLap ^ 2 / 2 := by
    positivity
  have hslack_T :
      0 ≤ C * nT ^ 2 / 2 + 3 * C ^ 2 * nT ^ 2 / 2 := by
    positivity
  nlinarith [sq_nonneg nT]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Elliptic.second_order_garding_sobolev_curv_real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Elliptic.second_order_garding_sobolev_curv_real target :: scope.openDecls } }


theorem secondCovGrad_l2NormSq_le_rawConnLap_covariantTensor
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hcomm :
      rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T) =
        covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T)
          + Curv)
    (hcurv :
      tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun ≤
        C₀ * (tensorL2Norm (I := I) (M := M) g 0 2 T.toFun +
          tensorL2Norm (I := I) (M := M) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T).toFun +
          tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
            (covGrad (I := I) (M := M) g 0 3
              (covGrad (I := I) (M := M) g 0 2 T)).toFun)) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T)).toFun ^ 2 ≤
      (2 + 3 * C₀ + 2 * C₀ ^ 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T.toFun ^ 2) := by
  classical
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T with hS_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 S.toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T.toFun with hnT_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun with hnCurv_def
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
    (covGrad (I := I) (M := M) g 0 3 S).toFun with hnHess_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnCurv_nn : 0 ≤ nCurv := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnHess_nn : 0 ≤ nHess := tensorL2Norm_nonneg (I := I) (M := M) g 0 (3 + 1) _
  have hgreen :
      nHess ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 3
            (rawTensorConnLapSmooth (I := I) g 0 3 S).toFun S.toFun := by
    rw [hnHess_def]
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (3 + 1)
      (covGrad (I := I) (M := M) g 0 3 S)]
    rw [hS_def]
    exact covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner (I := I) (M := M) g T
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3 S).toFun S.toFun =
        - nLap ^ 2 +
          tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun := by
    rw [hS_def, hnLap_def]
    exact rawConnLap_three_l2Inner_covGrad_eq (I := I) (M := M) g T Curv hcomm
  have hcombined :
      nHess ^ 2 =
        nLap ^ 2 - tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun := by
    rw [hgreen, hsplit]; ring
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 3 Curv.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) Curv)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Curv S)
  have hcross_le :
      - tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun ≤ nCurv * nGrad := by
    rw [hnCurv_def, hnGrad_def]
    exact le_trans (neg_le_abs _) hcs
  have hcurv' : nCurv ≤ C₀ * (nT + nGrad + nHess) := by
    rw [hnCurv_def, hnT_def, hnGrad_def, hnHess_def, hS_def]
    exact hcurv
  have hstep1 :
      nHess ^ 2 ≤ nLap ^ 2 + C₀ * (nT + nGrad + nHess) * nGrad := by
    rw [hcombined]
    have hprod : nCurv * nGrad ≤ C₀ * (nT + nGrad + nHess) * nGrad :=
      mul_le_mul_of_nonneg_right hcurv' hnGrad_nn
    linarith [hcross_le, hprod]
  have horder1 : nGrad ^ 2 ≤ nLap * nT := by
    rw [hnGrad_def, hS_def, hnLap_def, hnT_def]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  exact second_order_garding_sobolev_curv_real hC₀ hstep1 horder1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_covariantTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_covariantTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_covariantTensor ``Submission.DifferentialGeometry.Analysis.Elliptic.secondCovGrad_l2NormSq_le_rawConnLap_covariantTensor

end Elliptic
end Analysis
end DifferentialGeometry

end
