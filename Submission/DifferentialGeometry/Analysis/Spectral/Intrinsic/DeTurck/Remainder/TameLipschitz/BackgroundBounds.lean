import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import Submission.DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.ProductTwoTerm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Section
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.JointSmoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.Bilinear
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.UniformBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.FiberNorm.RawComponentBound
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Decomposition
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RawComponentIdentification
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.Chart.RicciRHSRealizeJet
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHS.ChartComponentIdentity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.InverseMetricDifferenceCoefficient
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.CurvatureCoefficientField
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.ApplicationJets
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.Realization.Section
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.OperatorField.Application
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.PathIntegralFibreNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.SymmetricCoefficientBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.PrincipalCoefficientBackgroundJetBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.ContinuousRealization
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Algebra
import Submission.DifferentialGeometry.Analysis.Estimates.ProductBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieHigherOrderCoefficientField
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.ChartLieDerivative
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.LieDerivative.RemainderOrderSplit
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.LieCoefficientApplication
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.ChartComponents
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.FirstOrderTerm.L2JetBound
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.SecondOrderTerm.L2JetBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.TameEstimates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature (chartRiemannTensor)
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
  (extChartAt_target_subset_interior_of_boundaryless)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_operatorFieldApplication_eq pathIntegralCoeffField_toSection linearizedRicciCovariantJetJointSmoothness
  linearizedRicciCovariantJetJointContinuity linearizedRicciCovariantJetJointSmoothness_zero
  exists_linearizedRicci_covariantJet_coeffFields ricciTensor_realize_sub_eq_covariantJet_operatorFieldApply
  linearizedRicciOrderZeroField linearizedRicciFirstOrderField linearizedRicciSecondOrderFieldLichnerowicz
  linearizedRicciOrderZeroBaseCoeff linearizedRicciOrderZeroCorrectionField linearizedRicciFirstOrderBaseCoeff
  linearizedRicciFirstOrderCorrectionField ricciDeTurckPrincipalCoefficient traceHessianCoeff
  linearizedRicci_orderZeroField_jointSmooth linearizedRicci_firstOrderField_jointSmooth
  linearizedRicci_secondOrderFieldLichnerowicz_jointSmooth ricciFirstOrderKoszulCoeff
  exists_firstOrderKoszul_metricPerturbationPath_riemannianFiberNormSq_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local operatorFieldApplication_zero_left_local ccTensor02Symm
  ccTensor02Symm_sub smoothCcTensorBilinForm_ccTensor02Symm iteratedCovGrad_ccTensor02Symm_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open _root_.Submission.DifferentialGeometry.PDE.DeTurck (deTurckVF)
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPathDomain metricPerturbationPathDomain_isOpen Icc_subset_metricPerturbationPathDomain linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum
  hasDerivAt_realizedRicciChartSum metricPerturbationPath)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (symmAbsorbedCoeff symmAbsorbedCoeff_operatorFieldApplication_eq exists_iteratedCovGrad_unitModel_domDomCongrSection
  symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpaceE_tame
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpaceE_tame target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck (cometricLmodel)
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (lieDeTurckChartSlope deriv_metricPerturbationPath_chartLieDeTurckComp_eq_chartSlope)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieSecondOrderPrincipalCoeff deTurckLieFirstOrderCoeff deTurckLieCoeffField
  deTurckLieSecondOrderPrincipalCoeff_metricPerturbationPath_jointSmooth deTurckLieFirstOrderCoeff_metricPerturbationPath_jointSmooth
  deTurckLieCoeffField_metricPerturbationPath_jointSmooth)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (reindexCoefficientInputSlots reindexCoefficientInputSlotsFiber reindexCoefficientInputSlotsFiber_apply reindexCoefficientInputSlots_toSection
  deTurckLieTraceCoeff deTurckLieTraceCoeff_toSection deTurckLieTraceFib traceHessianFib
  domDomCongrFibPerm_apply domDomCongrFib_apply traceHessianSlotPerm deTurckLieSecondOrderDivSlotPermA
  deTurckLieSecondOrderDivSlotPermAT traceHessianCoeff_toSection)

open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound metricPerturbationPath_inner_of_mem)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma de_turck_term_fibre_const_eq_one_of_finrank_eq_one (h1 : Module.finrank ℝ E = 1) :
    deTurckTermFibreConst (Module.finrank ℝ E) = 1 := by
  rw [h1]
  rw [deTurckTermFibreConst]
  rw [Nat.cast_one, one_pow, Real.sqrt_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.de_turck_term_fibre_const_eq_one_of_finrank_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.de_turck_term_fibre_const_eq_one_of_finrank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.de_turck_term_fibre_const_eq_one_of_finrank_eq_one ``Submission.DifferentialGeometry.Analysis.Spectral.de_turck_term_fibre_const_eq_one_of_finrank_eq_one

private lemma sqrt_natCast_mul_natCast_eq_deTurckTermFibreConst (n : ℕ) :
    Real.sqrt n * n = deTurckTermFibreConst n := by
  rw [deTurckTermFibreConst]
  rw [show ((n : ℝ)) ^ 3 = (n : ℝ) * (n : ℝ) ^ 2 from by ring]
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  rw [Real.sqrt_sq (Nat.cast_nonneg n)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.sqrt_natCast_mul_natCast_eq_deTurckTermFibreConst
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.sqrt_natCast_mul_natCast_eq_deTurckTermFibreConst target :: scope.openDecls } }

lemma background_coefficient_le_deTurckTermFibreConst_polynomial (n : ℕ) (hn : 2 ≤ n) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) (hδ₀half : δ₀ ≤ 1 / 2) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 13 / 2) :
    27 * Real.sqrt n * (1 - δ₀) * (c * n * (1 / (1 - δ₀)) ^ 2) ≤
      2 * (32 * deTurckTermFibreConst n ^ 3 - 28 * deTurckTermFibreConst n ^ 2) := by
  have h1δ : (0 : ℝ) < 1 - δ₀ := by linarith
  have hhalf : 1 / (1 - δ₀) ≤ 2 := by
    rw [div_le_iff₀ h1δ]
    linarith
  have hhalf0 : 0 < 1 / (1 - δ₀) := by positivity
  set f := deTurckTermFibreConst n with hf_def
  have hf0 : 0 ≤ f := de_turck_term_fibre_const_nonneg n
  have hf2 : f ^ 2 = (n : ℝ) ^ 3 := sq_de_turck_term_fibre_const n
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hf2ge : (8 : ℝ) ≤ f ^ 2 := by
    rw [hf2]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (n : ℝ) ^ 3 := by nlinarith [hn', sq_nonneg ((n : ℝ) - 2), sq_nonneg ((n : ℝ) + 2)]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2lb : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    have : (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) := by
      rw [Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2ub : Real.sqrt 2 ≤ (1.415 : ℝ) := by
    have h : Real.sqrt 2 ≤ Real.sqrt (1.415 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    rw [Real.sqrt_sq (by norm_num)] at h
    exact h
  have hfge : 2 * Real.sqrt 2 ≤ f := by
    have h8 : Real.sqrt 8 ≤ Real.sqrt (f ^ 2) := Real.sqrt_le_sqrt hf2ge
    have h8' : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 from by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      rw [Real.sqrt_sq (by norm_num)]
    rw [h8', Real.sqrt_sq hf0] at h8
    exact h8
  have hLHS : 27 * Real.sqrt n * (1 - δ₀) * (c * n * (1 / (1 - δ₀)) ^ 2) =
      27 * c * (Real.sqrt n * n) * ((1 - δ₀) * (1 / (1 - δ₀)) ^ 2) := by
    ring
  rw [sqrt_natCast_mul_natCast_eq_deTurckTermFibreConst n] at hLHS
  have hδfac : (1 - δ₀) * (1 / (1 - δ₀)) ^ 2 = 1 / (1 - δ₀) := by
    field_simp
  rw [hLHS, hδfac]
  have hstep : 27 * c * f * (1 / (1 - δ₀)) ≤ 54 * c * f := by
    have hcf : 0 ≤ 27 * c * f := by positivity
    calc 27 * c * f * (1 / (1 - δ₀)) ≤ 27 * c * f * 2 :=
          mul_le_mul_of_nonneg_left hhalf hcf
      _ = 54 * c * f := by ring
  refine le_trans hstep ?_
  have hcore : 27 * c ≤ 32 * f ^ 2 - 28 * f := by
    nlinarith only [hc, hfge, hs2, hs2lb, hs2ub, hf0,
      sq_nonneg (f - 2 * Real.sqrt 2)]
  nlinarith only [hcore, hf0, mul_nonneg hc0 hf0, hfge, hs2lb, hs2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.background_coefficient_le_deTurckTermFibreConst_polynomial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.background_coefficient_le_deTurckTermFibreConst_polynomial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.background_coefficient_le_deTurckTermFibreConst_polynomial ``Submission.DifferentialGeometry.Analysis.Spectral.background_coefficient_le_deTurckTermFibreConst_polynomial

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma metricCcTensor_unitModel_apply (g₀ g : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → E) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g) x m =
      g.inner x (m 0) (m 1) := by
  have hbase : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
      (M := M) g₀ 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g) x =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
          g x) := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel]
    change Tensor0SSpace.toModel
        ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
            g x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
            (1 : ℝ))) =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensorFib (I := I)
          g x)
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hbase]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.metricCcTensor_unitModel_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.metricCcTensor_unitModel_apply target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem eq_metricDifferenceCcTensor_of_inner_add (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    P = DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
      (I := I) (M := M) g₀ g₁ := by
  have hsymm : ccTensor02Symm (I := I) (M := M) g₀ P = P :=
    ccTensor02Symm_eq_self (I := I) (M := M) g₀ P hPsymm
  have hmd : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
      (I := I) (M := M) g₀ g₁ =
      ccTensor02Symm (I := I) (M := M) g₀ P := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
        (I := I) (M := M) g₀ g₁ =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g₁ -
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
          (M := M) g₀ g₀
        from rfl]
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub (I := I) (M := M) g₀ 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₁)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricCcTensor (I := I)
        (M := M) g₀ g₀) x]
    rw [sub_apply]
    rw [metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
      metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
    rw [show DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I)
        (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x m =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M)
          g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x ![m 0, m 1] from by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x (m 0) (m 1)]
    rw [smoothCcTensorBilinForm_ccTensor02Symm (I := I) (M := M) g₀ P x (m 0) (m 1)]
    rw [htie x (m 0) (m 1)]
    ring
  rw [hmd, hsymm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.eq_metricDifferenceCcTensor_of_inner_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.eq_metricDifferenceCcTensor_of_inner_add target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem ccTensor22_ext_of_operatorFieldApplication (g₀ : SmoothRiemannianMetric I M)
    (C D : SmoothCcTensor g₀ 2 2)
    (h : ∀ W : SmoothCcTensor g₀ 0 2,
      operatorFieldApply (I := I) (M := M) g₀ 2 2 C W = operatorFieldApply (I := I) (M := M) g₀ 2 2
        D W) : C = D := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  refine tensorRSSpace_ext 2 2 x (fun u => ?_)
  set V : TensorRSSpace 0 2 I x :=
    (show TensorRSSpace 0 2 I x from
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u))
    with hV_def
  obtain ⟨σW, hσW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (n := (⊤ : ℕ∞)) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) x V
  set W₀ : SmoothCcTensor g₀ 0 2 :=
    { toSection := σW
      hasCompactSupport := HasCompactSupport.of_compactSpace _ } with hW₀_def
  have h1 : (operatorFieldApply (I := I) (M := M) g₀ 2 2 C W₀).toSection x =
      (operatorFieldApply (I := I) (M := M) g₀ 2 2 D W₀).toSection x := by
    rw [h W₀]
  have h2 : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from C.toSection x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
          (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
            (M := M) x)) := by
    have h1' := congrArg (fun (T : TensorRSSpace 0 2 I x) =>
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T)
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
          (M := M) x)) h1
    exact h1'
  have hWval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W₀.toSection x)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I)
        (M := M) x) = u := by
    rw [show W₀.toSection x = V from hσW, hV_def]
    change ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight u)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x)
          (1 : ℝ)) = u
    rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
      ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rw [hWval] at h2
  exact h2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.ccTensor22_ext_of_operatorFieldApplication
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.ccTensor22_ext_of_operatorFieldApplication target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem half_ricciOrderZeroRiemannCoeff_difference_eq_residualFieldSum_add_kernelContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ P x v w = smoothCcTensorBilinForm (I := I) g₀ P x w v) :
    (1 / 2 : ℝ) •
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff
            (I := I) (M := M) g₀ g₁
          - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff
            (I := I) (M := M) g₀ g₀) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField
          (I := I) (M := M) g₀ g₁
        + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
            (I := I) (M := M) g₀ g₁
        + DifferentialGeometry.Analysis.Parabolic.TensorSpectral.decompositionKernelContractionField
            (I := I) (M := M) g₀ g₁
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)
            (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
            (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  classical
  have hP := eq_metricDifferenceCcTensor_of_inner_add (I := I) (M := M) g₀ g₁ P htie hPsymm
  rw [hP]
  refine ccTensor22_ext_of_operatorFieldApplication (I := I) (M := M) g₀ _ _ (fun W => ?_)
  have hprim :=
    ricciOrderZeroRiemannHalfBackgroundDiff_operatorFieldApplication_eq_residualFieldSum_add_decompositionKernelSecondGrad
      (I := I) (M := M) g₀ g₁ P htie hPsymm W
  rw [hP] at hprim
  rw [operatorFieldApplication_smul_left (I := I) (M := M) g₀ 2 2,
    operatorFieldApplication_sub_left (I := I) (M := M) g₀ 2 2]
  rw [hprim]
  rw [show (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₁
          - Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          Analysis.Parabolic.TensorSpectral.ricciCovariantTermSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciContractionRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁)) =
      Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
        (I := I) (M := M) g₀ g₁ from rfl]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField
        (I := I) (M := M) g₀ g₁
      + Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
        (I := I) (M := M) g₀ g₁)
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.decompositionKernelContractionField
      (I := I) (M := M) g₀ g₁
      (iteratedCovGrad (I := I) g₀ 0 2 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
          (I := I) (M := M) g₀ g₁))
      (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
      (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1) W]
  rw [operatorFieldApplication_add_left (I := I) (M := M) g₀ 2 2
    (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroAACommCoeffField
      (I := I) (M := M) g₀ g₁)
    (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
      (I := I) (M := M) g₀ g₁) W]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.operatorFieldApplication_decompositionKernelContractionField
    (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
        (I := I) (M := M) g₀ g₁))
    (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
    (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 W]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.half_ricciOrderZeroRiemannCoeff_difference_eq_residualFieldSum_add_kernelContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.half_ricciOrderZeroRiemannCoeff_difference_eq_residualFieldSum_add_kernelContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.half_ricciOrderZeroRiemannCoeff_difference_eq_residualFieldSum_add_kernelContraction ``Submission.DifferentialGeometry.Analysis.Spectral.half_ricciOrderZeroRiemannCoeff_difference_eq_residualFieldSum_add_kernelContraction

theorem riemannianFiberNormSq_iteratedCovGrad_bgRDiffDecompositionRemainderField_boundedFactorGridWindow_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
                (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciOrderZeroBackgroundRCommCoeffDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CS, hCS_nn, hCS⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciCovariantTermSharpGradKoszulResidualMetricDiff_gridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciContractionRemainderFieldMetricDifference_boundedFactorGridWindow_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨SW, hSW_nn, hSW⟩ := DifferentialGeometry.Analysis.Spectral.exists_riemannianFiberNormSq_iteratedCovGrad_bound (I := I) (M := M) g₀ 2 2
    (ccInputSlotSwapField (I := I) (M := M) g₀)
  refine ⟨fun i => 4 * (diagonalGridGrowthFactor (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l)
      + 4 * ((1 / 2 : ℝ) ^ 2 * CS i) + 2 * CR i,
    fun i => by
      have h1 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l :=
        mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hCB_nn i')
            (Finset.sum_nonneg fun l _ => hSW_nn l))
      have h2 := hCS_nn i
      have h3 := hCR_nn i
      positivity, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set w : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hw_def
  have hw_nn : 0 ≤ w := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn (i + 1) (i + 3)
  have hbg_eq :
    Analysis.Parabolic.TensorSpectral.backgroundRicciCommutatorDiffDecompositionRemainderField
      (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₁
          - Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀)
      + (1 / 2 : ℝ) •
          Analysis.Parabolic.TensorSpectral.ricciCovariantTermSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁)
      - DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciContractionRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁) := rfl
  rw [hbg_eq]
  rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i, iteratedCovGrad_add (I := I) g₀ 2 2 i]
  rw [DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_sub_apply
      (I := I) (M := M) g₀ (r := 2) (s := 2 + i),
    DifferentialGeometry.Analysis.Sobolev.smoothCcTensor_toSection_add_apply
      (I := I) (M := M) g₀ (r := 2) (s := 2 + i)]
  refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have hsplit2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
        (Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₁
          - Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
            (I := I) (M := M) g₀ g₀)
        (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i
      ((1 / 2 : ℝ) •
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCovariantTermSharpGradKoszulResidualField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x)
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2
          (Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₁
            - Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₀)
          (ccInputSlotSwapField (I := I) (M := M) g₀))).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l) * w := by
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 2 2 2
      (Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
          (I := I) (M := M) g₀ g₁
        - Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
          (I := I) (M := M) g₀ g₀)
      (ccInputSlotSwapField (I := I) (M := M) g₀) x) ?_
    have hrhs : (diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), CB i' * ∑ l ∈ Finset.range (i + 1 - i'), SW l) * w =
        diagonalGridGrowthFactor (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), (CB i' * w) * ∑ l ∈ Finset.range (i + 1 - i'), SW l := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i' _ => ?_)
      ring
    rw [hrhs]
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
    refine Finset.sum_le_sum (fun i' hi' => ?_)
    have hi'le : i' ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
    have hBGi' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 2 2 i'
          (Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₁
            - Analysis.Parabolic.TensorSpectral.ricciOrderZeroBackgroundCurvatureCoeffField
              (I := I) (M := M) g₀ g₀)).toSection x) ≤ CB i' * w := by
      refine le_trans (hCB g₁ P htie hδ_le hδ0 hbound i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCB_nn i')
      rw [hw_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb_nn
        (by omega) (by omega)
    refine mul_le_mul hBGi' ?_ ?_ (mul_nonneg (hCB_nn i') hw_nn)
    · refine Finset.sum_le_sum (fun l _ => hSW l x)
    · exact Finset.sum_nonneg (fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _)
  have hS : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        ((1 / 2 : ℝ) •
          Analysis.Parabolic.TensorSpectral.ricciCovariantTermSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁))).toSection x) ≤
      ((1 / 2 : ℝ) ^ 2 * CS i) * w := by
    rw [DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_smul (I := I) (M := M) g₀ 2 2 i (1 / 2)]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCovariantTermSharpGradKoszulResidualField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x) =
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 2 2 i
          (Analysis.Parabolic.TensorSpectral.ricciCovariantTermSharpGradKoszulResidualField
            (I := I) (M := M) g₀ g₁
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
              (I := I) (M := M) g₀ g₁))).toSection x from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 (2 + i) x (1 / 2) _]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hCS g₁ P htie hδ_le hδ0 hbound i x
  have hR : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciContractionRemainderField
          (I := I) (M := M) g₀ g₁
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.metricDifferenceCcTensor
            (I := I) (M := M) g₀ g₁))).toSection x) ≤ CR i * w :=
    hCR g₁ P htie hδ_le hδ0 hbound i x
  nlinarith [hsplit2, hA, hS, hR, hw_nn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_bgRDiffDecompositionRemainderField_boundedFactorGridWindow_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_bgRDiffDecompositionRemainderField_boundedFactorGridWindow_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_bgRDiffDecompositionRemainderField_boundedFactorGridWindow_le ``Submission.DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_bgRDiffDecompositionRemainderField_boundedFactorGridWindow_le

end DifferentialGeometry.Analysis.Spectral

end
