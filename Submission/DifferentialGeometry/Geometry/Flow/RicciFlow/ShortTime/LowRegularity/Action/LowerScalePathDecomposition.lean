import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.Remainder
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.LowOrderDecomposition
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.PathIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.intervalIntegral
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unitModel_add_app
    (g : SmoothRiemannianMetric I M) (A B : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  have hfun : unitModel (I := I) (M := M) g 2 (A + B) x =
      unitModel (I := I) (M := M) g 2 A x +
        unitModel (I := I) (M := M) g 2 B x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      add_apply, Tensor0SSpace.toModel_add]
  rw [hfun, add_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.unitModel_add_app
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.unitModel_add_app target :: scope.openDecls } }

theorem lowerScaleActionCoefficients_sum_eq_path_integral_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    let A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
    A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
              hδ_lt hδ hδ_lt hδZ +
            metricPrincipalDefectCurvCoeff (I := I) g g) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g g_bg T 0
            hδ_lt hδ hδ_lt hδZ)
          (iteratedCovGrad (I := I) g 0 2 1 T) +
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsTopPathIntegral (I := I) (M := M) g T 0
              hδ_lt hδ hδ_lt hδZ -
            deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  classical
  let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g g_bg
  have hsplitT := (hsplit T hTsymm hδ_le hδ0 hδ hδZ).1
  change A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T = _
  rw [← hsplitT]
  change
    (deTurckRHSAtMetricPerturbation (I := I) g g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g 0 2 T) -
      (deTurckRHSAtMetricPerturbation (I := I) g g_bg (0 : SmoothCcTensor g 0 2)
          hδ_lt hδZ -
        rawTensorConnLapSmooth (I := I) g 0 2
          (0 : SmoothCcTensor g 0 2)) = _
  have hlap0 : rawTensorConnLapSmooth (I := I) g 0 2
      (0 : SmoothCcTensor g 0 2) = 0 := by
    have hzero := rawTensorConnLapSmooth_sub
      (I := I) (M := M) g 0 2 T T
    rwa [sub_self, sub_self] at hzero
  rw [hlap0, sub_zero]
  rw [show
      (deTurckRHSAtMetricPerturbation (I := I) g g_bg T hδ_lt hδ -
          rawTensorConnLapSmooth (I := I) g 0 2 T) -
        deTurckRHSAtMetricPerturbation (I := I) g g_bg (0 : SmoothCcTensor g 0 2)
          hδ_lt hδZ =
      (deTurckRHSAtMetricPerturbation (I := I) g g_bg T hδ_lt hδ -
          deTurckRHSAtMetricPerturbation (I := I) g g_bg (0 : SmoothCcTensor g 0 2)
            hδ_lt hδZ) -
        rawTensorConnLapSmooth (I := I) g 0 2 T by abel]
  rw [de_turck_rhs_at_metric_perturbation_sub_eq_path_integrals (I := I) (M := M) g g_bg T 0
    hTsymm (zero_metricPerturbation_symmetric (I := I) (M := M) g)
    hδ_lt hδ hδ_lt hδZ]
  simp only [sub_zero, iteratedCovGrad_zero]
  have htop := principalCoefficientAction_decomposition (I := I) (M := M) g g T
  simp only [deTurckPrincipalCometricTerm, deTurckPrincipalCometricCoeff,
    sub_self, operatorFieldApplication_zero_left, add_zero] at htop
  have hlap : rawTensorConnLapSmooth (I := I) g 0 2 T =
      operatorFieldApply (I := I) (M := M) g 4 2
          (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
          (iteratedCovGrad (I := I) g 0 2 2 T) -
        operatorFieldApply (I := I) (M := M) g 2 2
          (metricPrincipalDefectCurvCoeff (I := I) g g) T := by
    exact (eq_sub_iff_add_eq).2 htop.symm
  rw [hlap]
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_sub_left]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleActionCoefficients_sum_eq_path_integral_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleActionCoefficients_sum_eq_path_integral_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleActionCoefficients_sum_eq_path_integral_decomposition ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleActionCoefficients_sum_eq_path_integral_decomposition

theorem oneMinusConnectionLaplacian_lowerScaleActionCoefficients_eq_path_terms
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
    let A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
    let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
      hδ_lt hδ hδ_lt hδZ
    let P1 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g g_bg T 0
      hδ_lt hδ hδ_lt hδZ
    let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
      hδ_lt hδ hδ_lt hδZ
    let Φ0 := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
    let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
    let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
    let B02 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 LT))
    oneMinusConnLapSmooth (I := I) g 0 2
          (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T) -
        operatorFieldApply (I := I) (M := M) g 4 2 (P2 - Φ0)
          (iteratedCovGrad (I := I) g 0 2 2 LT) =
      B02 +
        oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 3 2 P1
            (iteratedCovGrad (I := I) g 0 2 1 T)) +
        operatorFieldApply (I := I) (M := M) g 2 2 K0 LT := by
  classical
  let hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let A := lowerScaleActionCoefficients (I := I) (M := M) g g_bg T hδ_lt hδ hδZ
  let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
    hδ_lt hδ hδ_lt hδZ
  let P1 := ricciDeTurckRemainderFirstOrderPathIntegral (I := I) (M := M) g g_bg T 0
    hδ_lt hδ hδ_lt hδZ
  let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
    hδ_lt hδ hδ_lt hδZ
  let Φ0 := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  let B02 :=
    oneMinusConnLapSmooth (I := I) g 0 2
        (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
      (oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
        operatorFieldApply (I := I) (M := M) g 4 2 P2
          (iteratedCovGrad (I := I) g 0 2 2 LT))
  dsimp only
  have hpath := lowerScaleActionCoefficients_sum_eq_path_integral_decomposition (I := I) (M := M) g g_bg T hTsymm
    hδ_le hδ0 hδ hδZ
  dsimp only at hpath
  have hlap0 : rawTensorConnLapSmooth (I := I) g 0 2
      (0 : SmoothCcTensor g 0 2) = 0 := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g 0 2 T T
    simpa only [sub_self] using h
  have hlap_neg (X : SmoothCcTensor g 0 2) :
      rawTensorConnLapSmooth (I := I) g 0 2 (-X) =
        -rawTensorConnLapSmooth (I := I) g 0 2 X := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g 0 2
      (0 : SmoothCcTensor g 0 2) X
    simpa only [zero_sub, hlap0] using h
  have hlap_add (X Y : SmoothCcTensor g 0 2) :
      rawTensorConnLapSmooth (I := I) g 0 2 (X + Y) =
        rawTensorConnLapSmooth (I := I) g 0 2 X +
          rawTensorConnLapSmooth (I := I) g 0 2 Y := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g 0 2 X (-Y)
    simpa only [sub_neg_eq_add, hlap_neg] using h
  have hL_add (X Y : SmoothCcTensor g 0 2) :
      oneMinusConnLapSmooth (I := I) g 0 2 (X + Y) =
        oneMinusConnLapSmooth (I := I) g 0 2 X +
          oneMinusConnLapSmooth (I := I) g 0 2 Y := by
    unfold oneMinusConnLapSmooth
    rw [hlap_add]
    abel
  have hL_sub (X Y : SmoothCcTensor g 0 2) :
      oneMinusConnLapSmooth (I := I) g 0 2 (X - Y) =
        oneMinusConnLapSmooth (I := I) g 0 2 X -
          oneMinusConnLapSmooth (I := I) g 0 2 Y := by
    unfold oneMinusConnLapSmooth
    rw [rawTensorConnLapSmooth_sub]
    abel
  have hL_lap :
      oneMinusConnLapSmooth (I := I) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T) =
        rawTensorConnLapSmooth (I := I) g 0 2 LT := by
    simp only [LT, oneMinusConnLapSmooth,
      rawTensorConnLapSmooth_sub]
  have htopT := principalCoefficientAction_decomposition (I := I) (M := M) g g T
  have htopLT := principalCoefficientAction_decomposition (I := I) (M := M) g g LT
  simp only [deTurckPrincipalCometricTerm, deTurckPrincipalCometricCoeff,
    sub_self, operatorFieldApplication_zero_left, add_zero] at htopT htopLT
  have hinside :
      operatorFieldApply (I := I) (M := M) g 2 2 (P0 + K0) T +
          operatorFieldApply (I := I) (M := M) g 3 2 P1
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          operatorFieldApply (I := I) (M := M) g 4 2 (P2 - Φ0)
            (iteratedCovGrad (I := I) g 0 2 2 T) =
        (operatorFieldApply (I := I) (M := M) g 2 2 P0 T +
            operatorFieldApply (I := I) (M := M) g 3 2 P1
              (iteratedCovGrad (I := I) g 0 2 1 T) +
            operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          rawTensorConnLapSmooth (I := I) g 0 2 T := by
    rw [operatorFieldApplication_add_left, operatorFieldApplication_sub_left, htopT]
    module
  rw [hpath, hinside, hL_sub, hL_add, hL_add, operatorFieldApplication_sub_left,
    hL_lap, htopLT]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.oneMinusConnectionLaplacian_lowerScaleActionCoefficients_eq_path_terms then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.oneMinusConnectionLaplacian_lowerScaleActionCoefficients_eq_path_terms"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.oneMinusConnectionLaplacian_lowerScaleActionCoefficients_eq_path_terms ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.oneMinusConnectionLaplacian_lowerScaleActionCoefficients_eq_path_terms

omit [SigmaCompactSpace M] in
theorem low_order_path_integral_eq_decomposition_add_edge_pairing
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
          hdelta_lt hdelta hdelta_lt hdeltaZ) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (rhsDecomposition0Int (I := I) (M := M) g g_bg T
            hdelta_lt hdelta hdeltaZ) T +
        operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T hdelta_lt
            hdelta hdeltaZ ricciDecompositionQA ricciDecompositionQB
              lieDecompositionQ lieDecompositionEps) T := by
  classical
  let S : Set Real := metricPerturbationPathDomain (δ := delta) (δ' := delta)
  have hS : IsOpen S := metricPerturbationPathDomain_isOpen
  have hSI : Set.uIcc (0 : Real) 1 ⊆ S := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hdelta_lt hdelta_lt
  let A : Real → SmoothCcTensor g 2 2 := fun s =>
    ricciDeTurckRemainderZeroOrderCoefficient (I := I) (M := M) g g_bg T 0 hdelta hdeltaZ s
  let R : Real → SmoothCcTensor g 2 2 :=
    rhsDecomposition0 (I := I) (M := M) g g_bg T hdelta hdeltaZ
  let Q : Real → SmoothCcTensor g 2 2 :=
    ricciDeTurckTopOrderBilinearPairingCoefficient (I := I) (M := M) g T T hdelta hdeltaZ
      ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps
  have hA : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2 A
      (δ := delta) (δ' := delta) := by
    simpa only [A] using ricciDeTurckRemainderZeroOrderCoefficient_path_joint (I := I) (M := M)
      g g_bg T 0 hdelta hdeltaZ
  have hR : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2 R
      (δ := delta) (δ' := delta) := by
    simpa only [R] using rhsDecomposition0_joint (I := I) (M := M)
      g g_bg T hdelta hdeltaZ
  have hQ : linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 2 Q
      (δ := delta) (δ' := delta) := by
    rw [linearizedRicciCovariantJetJointSmoothness]
    exact ricciDeTurckTopOrderPairingCoefficient_joint_contDiff (I := I) (M := M)
      g T T hdelta hdeltaZ ricciDecompositionQA ricciDecompositionQB
        lieDecompositionQ lieDecompositionEps
  have hcA : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((A t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 2 2 A S hA x
  have hcR : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((R t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 2 2 R S hR x
  have hcQ : ∀ x : M, ContinuousOn (fun t : Real =>
      TensorRSSpace.toModel ((Q t).toSection x)) S := fun x =>
    jointContMDiff_toModel_continuous_slice (I := I) g 2 2 Q S hQ x
  have hPiA :
      ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
          hdelta_lt hdelta hdelta_lt hdeltaZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2
          A S hS hSI hA := rfl
  have hPiR :
      rhsDecomposition0Int (I := I) (M := M) g g_bg T
          hdelta_lt hdelta hdeltaZ =
        pathIntegralCoeffField (I := I) (M := M) g 2 2
          R S hS hSI hR := rfl
  have hPiQ :
      ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T T hdelta_lt
          hdelta hdeltaZ ricciDecompositionQA ricciDecompositionQB
            lieDecompositionQ lieDecompositionEps =
        pathIntegralCoeffField (I := I) (M := M) g 2 2
          Q S hS hSI hQ := rfl
  apply smoothCcTensor_ext_of_unitModel
  intro x
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel_add_app, hPiA, hPiR, hPiQ]
  rw [pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 A T S hS hSI hA hcA x v,
    pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 R T S hS hSI hR hcR x v,
    pathIntegralCoeffField_operatorFieldApplication_eq
      (I := I) (M := M) g 2 2 Q T S hS hSI hQ hcQ x v]
  have hIR : IntervalIntegrable (fun s : Real =>
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (R s) T) x v)
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g 2 2 R T S hSI hcR x v
  have hIQ : IntervalIntegrable (fun s : Real =>
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2 (Q s) T) x v)
      volume 0 1 :=
    coeffApp_integrable (I := I) (M := M) g 2 2 Q T S hSI hcQ x v
  rw [← intervalIntegral.integral_add hIR hIQ]
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  have hsI : s ∈ Set.Icc (0 : Real) 1 := by
    simpa only [Set.uIcc_of_le zero_le_one] using hs
  have hdiag :
      operatorFieldApply (I := I) (M := M) g 2 2 (Q s) T =
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
    change operatorFieldApply (I := I) (M := M) g 2 2
        (ricciDeTurckTopOrderPairingCoefficient (I := I) (M := M) g T hdelta hdeltaZ
          ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s) T = _
    simpa only [rhsDecomposition2, ricciDecomposition2, lieDecomposition2] using
      ricciDeTurckTopOrderPairingCoefficient_apply (I := I) (M := M) g T hdelta hdeltaZ
        ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps s
  have hpoint :
      operatorFieldApply (I := I) (M := M) g 2 2 (A s) T =
        operatorFieldApply (I := I) (M := M) g 2 2 (R s) T +
          operatorFieldApply (I := I) (M := M) g 2 2 (Q s) T := by
    rw [hdiag]
    have hcoeff :
        ricciDeTurckRemainderZeroOrderCoefficient
            (I := I) (M := M) g g_bg T 0 hdelta hdeltaZ s =
          DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient
            (I := I) (M := M) g g_bg T 0 hdelta hdeltaZ s := by
      with_unfolding_all rfl
    dsimp only [A, R]
    rw [hcoeff]
    exact rhsLow0_decomposition (I := I) (M := M)
      g g_bg T hTsymm hdelta_lt hdelta hdeltaZ hsI
  simpa only [unitModel_add_app] using congrArg
    (fun W => unitModel (I := I) (M := M) g 2 W x v) hpoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_order_path_integral_eq_decomposition_add_edge_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_order_path_integral_eq_decomposition_add_edge_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_order_path_integral_eq_decomposition_add_edge_pairing ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.low_order_path_integral_eq_decomposition_add_edge_pairing

omit [SigmaCompactSpace M] in
theorem lowerScaleZerothSecondOrderTerms_eq_raw_commutator_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta) :
    let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let R0 := rhsDecomposition0Int (I := I) (M := M) g g_bg T
      hdelta_lt hdelta hdeltaZ
    let Q := fun U : SmoothCcTensor g 0 2 =>
      ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T U hdelta_lt
        hdelta hdeltaZ ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps
    let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
    let B02 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 LT))
    let PairComm :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T) -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
    let RawComm :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 R0 T) + PairComm
    let TopComm :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 T)) -
        operatorFieldApply (I := I) (M := M) g 4 2 P2
          (iteratedCovGrad (I := I) g 0 2 2 LT)
    B02 =
      RawComm + TopComm +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T := by
  classical
  dsimp only
  rw [low_order_path_integral_eq_decomposition_add_edge_pairing (I := I) (M := M) g g_bg T hTsymm
    hdelta_lt hdelta hdeltaZ]
  rw [oneMinusConn_add (I := I) (M := M) g 0 2]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_raw_commutator_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_raw_commutator_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_raw_commutator_decomposition ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_raw_commutator_decomposition

omit [SigmaCompactSpace M] in
theorem lowerScaleZerothSecondOrderTerms_eq_centered_commutator_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {delta : Real} (hdelta_lt : delta < 1)
    (hdelta : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) delta)
    (hdeltaZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) delta) :
    let P0 := ricciDeTurckRemainderZeroOrderPathIntegral (I := I) (M := M) g g_bg T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let P2 := rhsTopPathIntegral (I := I) (M := M) g T 0
      hdelta_lt hdelta hdelta_lt hdeltaZ
    let R0 := rhsDecomposition0Int (I := I) (M := M) g g_bg T
      hdelta_lt hdelta hdeltaZ
    let Φ0 := deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
    let K0 := metricPrincipalDefectCurvCoeff (I := I) g g
    let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
    let Q := fun U : SmoothCcTensor g 0 2 =>
      ricciDeTurckTopOrderPathIntegralCoefficient (I := I) (M := M) g T U hdelta_lt
        hdelta hdeltaZ ricciDecompositionQA ricciDecompositionQB lieDecompositionQ lieDecompositionEps
    let Z := operatorFieldApply (I := I) (M := M) g 2 2 (Q T) T
    let Cross :=
      operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T +
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT
    let PairComm :=
      oneMinusConnLapSmooth (I := I) g 0 2 Z -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q LT) T -
        operatorFieldApply (I := I) (M := M) g 2 2 (Q T) LT + Z
    let C := P2 - Φ0
    let B02 :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 P0 T) +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 P2
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 P2
            (iteratedCovGrad (I := I) g 0 2 2 LT))
    let J :=
      oneMinusConnLapSmooth (I := I) g 0 2
          (operatorFieldApply (I := I) (M := M) g 2 2 (R0 + K0) T) +
        PairComm +
        (oneMinusConnLapSmooth (I := I) g 0 2
            (operatorFieldApply (I := I) (M := M) g 4 2 C
              (iteratedCovGrad (I := I) g 0 2 2 T)) -
          operatorFieldApply (I := I) (M := M) g 4 2 C
            (iteratedCovGrad (I := I) g 0 2 2 LT)) - Z
    B02 + operatorFieldApply (I := I) (M := M) g 2 2 K0 LT = J + Cross := by
  classical
  dsimp only
  have hraw := lowerScaleZerothSecondOrderTerms_eq_raw_commutator_decomposition (I := I) (M := M) g g_bg T hTsymm
    hdelta_lt hdelta hdeltaZ
  dsimp only at hraw
  rw [hraw]
  have hL_sub (X Y : SmoothCcTensor g 0 2) :
      oneMinusConnLapSmooth (I := I) g 0 2 (X - Y) =
        oneMinusConnLapSmooth (I := I) g 0 2 X -
          oneMinusConnLapSmooth (I := I) g 0 2 Y := by
    unfold oneMinusConnLapSmooth
    rw [rawTensorConnLapSmooth_sub]
    abel
  let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
  have hL_lap :
      oneMinusConnLapSmooth (I := I) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T) =
        rawTensorConnLapSmooth (I := I) g 0 2 LT := by
    simp only [LT, oneMinusConnLapSmooth, rawTensorConnLapSmooth_sub]
  have htopT := principalCoefficientAction_decomposition (I := I) (M := M) g g T
  have htopLT := principalCoefficientAction_decomposition (I := I) (M := M) g g LT
  simp only [deTurckPrincipalCometricTerm, deTurckPrincipalCometricCoeff,
    sub_self, operatorFieldApplication_zero_left, add_zero] at htopT htopLT
  rw [operatorFieldApplication_add_left, oneMinusConn_add (I := I) (M := M) g 0 2,
    operatorFieldApplication_sub_left, hL_sub, operatorFieldApplication_sub_left, htopT, htopLT,
    oneMinusConn_add (I := I) (M := M) g 0 2, hL_lap]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_centered_commutator_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_centered_commutator_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_centered_commutator_decomposition ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowerScaleZerothSecondOrderTerms_eq_centered_commutator_decomposition

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
