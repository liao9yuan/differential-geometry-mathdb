import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import Submission.DifferentialGeometry.Analysis.Sobolev.GagliardoNirenberg.ProductTwoTerm
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
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
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
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
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
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

private noncomputable def realizedDeTurckLiePathValue
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  lieDerivMetricClm (I := I)
    (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      (le_max_left 0 (_root_.Min.min s 1))
      (max_le zero_le_one (min_le_right s 1)))
    (deTurckVF (I := I)
      (smoothRiemannianMetricToInfty (I := I)
        (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (_root_.Min.min s 1))
          (max_le zero_le_one (min_le_right s 1))))
      (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem realizedDeTurckLiePathValue_one
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 1 =
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w := by
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (_root_.Min.min (1 : ℝ) 1))
          (max_le zero_le_one (min_le_right (1 : ℝ) 1)) =
        tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      tensorSectionRealizeMetric_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_convexPerturbation]
    have : _root_.Max.max (0 : ℝ) (_root_.Min.min 1 1) = 1 := by norm_num
    rw [this]; ring
  rw [realizedDeTurckLiePathValue, hmetric]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_one target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem realizedDeTurckLiePathValue_zero
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 0 =
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w := by
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (_root_.Min.min (0 : ℝ) 1))
          (max_le zero_le_one (min_le_right (0 : ℝ) 1)) =
        tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      tensorSectionRealizeMetric_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_convexPerturbation]
    have : _root_.Max.max (0 : ℝ) (_root_.Min.min 0 1) = 0 := by norm_num
    rw [this]; ring
  rw [realizedDeTurckLiePathValue, hmetric]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_zero target :: scope.openDecls } }

noncomputable def linearizedDeTurckLieAt
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s₀ : ℝ) : ℝ :=
  deriv (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt ``Submission.DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt

noncomputable def realizedDeTurckLieChartSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ j,
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x v)) i *
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x w)) j *
      DeTurckCoefficients.chartLieDeTurckComp (I := I)
        (DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
          (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLieChartSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.realizedDeTurckLieChartSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLieChartSum ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLieChartSum

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem realizedDeTurckLieChartSum_contDiffAt
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ}
    (hs : s₀ ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ')) :
    ContDiffAt ℝ ∞ (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s₀ := by
  have hG := DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath_chartGramFamilyJointSmoothOn
    (I := I) g₀ T T' hδ hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  unfold realizedDeTurckLieChartSum
  refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ => ?_))
  refine contDiffAt_const.mul ?_
  have hjoint := DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLieDeTurckComp_joint_contDiffAt
    (I := I) (DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
      (I := I) g₀ T T' hδ hδ') x hG g_bg i j hs hy
  have hcomp : (fun s : ℝ =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
            (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) =
      (fun p : ℝ × E =>
        DeTurckCoefficients.chartLieDeTurckComp (I := I)
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
            (I := I) g₀ T T' hδ hδ' p.1) g_bg x i j p.2) ∘
        (fun s : ℝ => (s, extChartAt I x x)) := by funext s; rfl
  rw [hcomp]
  exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLieChartSum_contDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLieChartSum_contDiffAt target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem realizedDeTurckLiePathValue_eq_chartSum_on_Icc
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w s := by
  obtain ⟨h0, h1⟩ := hs
  have hmem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨h0, h1⟩
  have hclamp : _root_.Max.max 0 (_root_.Min.min s 1) = s := by rw [min_eq_left h1, max_eq_right h0]
  have hxgood : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) x :=
    DifferentialGeometry.Geometry.Connection.self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hmetric :
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath
          (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          (le_max_left 0 (_root_.Min.min s 1))
          (max_le zero_le_one (min_le_right s 1)) =
        DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
          (I := I) g₀ T T' hδ hδ' s := by
    refine DifferentialGeometry.PDE.DeTurck.RicciLinearization.riemannianMetric_eq_of_inner
      _ _ (fun b u z => ?_)
    rw [DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedMetricPath_inner,
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath_inner_of_mem
        (I := I) g₀ T T' hδ hδ' hmem, hclamp]
  rw [realizedDeTurckLiePathValue, hmetric, lieDerivMetricClm_apply,
    realizedDeTurckLieChartSum]
  rw [DifferentialGeometry.PDE.DeTurck.lieDerivMetric_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [smoothRiemannianMetricToInfty]
  rw [DifferentialGeometry.PDE.DeTurck.lieDerivMetricMatrix_def_chart,
    DeTurckCoefficients.chartLieDerivMetricMatrix_deTurckVF_eq_chartLieDeTurckComp
      (I := I)
      (DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
        (I := I) g₀ T T' hδ hδ' s) g_bg x i j hxgood]
  simp only [DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_repr]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_eq_chartSum_on_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_eq_chartSum_on_Icc target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem realizedDeTurckLiePathValue_differentiableAt_Ioo
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ
      (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w) s₀ := by
  have heq : realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s₀] realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Set.mem_Icc_of_Ioo hs)
  have hmem : s₀ ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  exact ((realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ hδ' x v w
    hmem).differentiableAt (by simp)).congr_of_eventuallyEq heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_differentiableAt_Ioo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_differentiableAt_Ioo target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
      deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s := by
  have heq : realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
      =ᶠ[nhds s] realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w (Set.mem_Icc_of_Ioo ht)
  rw [linearizedDeTurckLieAt]
  exact Filter.EventuallyEq.deriv_eq heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo ``Submission.DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem deriv_realizedDeTurckLieChartSum_continuousOn
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := by
  have hcd : ContDiffOn ℝ ∞ (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ')) := fun s hs =>
    (realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ hδ' x v w
      hs).contDiffWithinAt
  exact hcd.continuousOn_deriv_of_isOpen metricPerturbationPathDomain_isOpen (by exact_mod_cast le_top)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.deriv_realizedDeTurckLieChartSum_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.deriv_realizedDeTurckLieChartSum_continuousOn target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem linearizedDeTurckLieAt_intervalIntegrable
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    IntervalIntegrable
      (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      MeasureTheory.volume 0 1 := by
  have hcont : ContinuousOn (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      (Set.Icc (0:ℝ) 1) :=
    (deriv_realizedDeTurckLieChartSum_continuousOn (I := I) g₀ g_bg T T' hδ hδ' x v
      w).mono
      (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt)
  have hii : IntervalIntegrable
      (deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w))
      MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  refine hii.congr_ae ?_
  have hsub : Set.Ioo (0:ℝ) 1 ⊆
      {s | deriv (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s =
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s} := by
    intro s hs
    exact (linearizedDeTurckLieAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs).symm
  have hnull : (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) 1)) (Set.Ioo (0:ℝ) 1)ᶜ = 0 := by
    rw [Set.uIoc_of_le zero_le_one]
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
    have hsub1 : (Set.Ioo (0:ℝ) 1)ᶜ ∩ Set.Ioc 0 1 ⊆ {1} := by
      intro t ht
      obtain ⟨htc, ht0, ht1⟩ := ht
      rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at htc
      rcases htc with h | h
      · exact absurd ht0 (not_lt.mpr h)
      · exact (le_antisymm ht1 h) ▸ rfl
    exact MeasureTheory.measure_mono_null hsub1 (by simp)
  refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
  exact fun hs' => hs (hsub hs')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_intervalIntegrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_intervalIntegrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_intervalIntegrable ``Submission.DifferentialGeometry.Analysis.Spectral.linearizedDeTurckLieAt_intervalIntegrable

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem realizedDeTurckLiePathValue_continuousOn_Icc
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
      (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.congr
    (f := realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) ?_ ?_
  · exact fun s hs =>
      (realizedDeTurckLieChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ hδ' x v w
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt hs)).continuousAt.continuousWithinAt
  · intro s hs
    exact realizedDeTurckLiePathValue_eq_chartSum_on_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
      x v w hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_continuousOn_Icc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.realizedDeTurckLiePathValue_continuousOn_Icc target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private theorem hasDerivAt_lieDeTurck_realizedMetricPath
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    (∀ s₀ ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
          (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s₀) s₀) ∧
      IntervalIntegrable
        (linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w)
        MeasureTheory.volume 0 1 := by
  refine ⟨fun s₀ hs₀ => ?_, ?_⟩
  · rw [linearizedDeTurckLieAt]
    exact (realizedDeTurckLiePathValue_differentiableAt_Ioo (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt
      hδ'
      x v w hs₀).hasDerivAt
  · exact linearizedDeTurckLieAt_intervalIntegrable (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.hasDerivAt_lieDeTurck_realizedMetricPath
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.hasDerivAt_lieDeTurck_realizedMetricPath target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w -
      lieDerivMetricClm (I := I)
        (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')
        (deTurckVF (I := I)
          (smoothRiemannianMetricToInfty (I := I)
            (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ'))
          (smoothRiemannianMetricToInfty (I := I) g_bg)) x v w =
      ∫ s in (0 : ℝ)..1,
        linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s := by
  obtain ⟨hderiv, hint⟩ :=
    hasDerivAt_lieDeTurck_realizedMetricPath (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hcont :=
    realizedDeTurckLiePathValue_continuousOn_Icc (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w
  have hFTC :
      ∫ s in (0 : ℝ)..1,
          linearizedDeTurckLieAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w s =
        realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 1 -
          realizedDeTurckLiePathValue (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [hFTC, realizedDeTurckLiePathValue_one, realizedDeTurckLiePathValue_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie ``Submission.DifferentialGeometry.Analysis.Spectral.lieDerivMetricClm_realized_sub_eq_integral_linearizedDeTurckLie

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hasDerivAt_realizedDeTurckLieChartSum
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w)
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x v)) i *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x w)) j *
          deriv (fun s : ℝ =>
            DeTurckCoefficients.chartLieDeTurckComp (I := I)
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s₀) s₀ := by
  have hmem : s₀ ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ') :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  have hG := DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath_chartGramFamilyJointSmoothOn
    (I := I) g₀ T T' hδ hδ' x
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hbody : (realizedDeTurckLieChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x v)) i *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv (I := I) x w)) j *
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) := by
    funext s; rw [realizedDeTurckLieChartSum]
  rw [hbody]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  refine HasDerivAt.fun_sum (fun j _ => ?_)
  have hcontdiff : ContDiffAt ℝ ∞
      (fun s : ℝ => DeTurckCoefficients.chartLieDeTurckComp (I := I)
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) s₀ := by
    have hjoint := DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartLieDeTurckComp_joint_contDiffAt
      (I := I) (metricPerturbationPath (I := I) g₀ T T' hδ hδ') x hG g_bg i j hmem hy
    have hcomp : (fun s : ℝ =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg x i j (extChartAt I x x)) =
        (fun p : ℝ × E =>
          DeTurckCoefficients.chartLieDeTurckComp (I := I)
            (metricPerturbationPath (I := I) g₀ T T' hδ hδ' p.1) g_bg x i j p.2) ∘
          (fun s : ℝ => (s, extChartAt I x x)) := by funext s; rfl
    rw [hcomp]
    exact hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)
  exact ((hcontdiff.differentiableAt (by simp)).hasDerivAt).const_mul _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hasDerivAt_realizedDeTurckLieChartSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hasDerivAt_realizedDeTurckLieChartSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hasDerivAt_realizedDeTurckLieChartSum ``Submission.DifferentialGeometry.Analysis.Spectral.hasDerivAt_realizedDeTurckLieChartSum

private noncomputable def deTurckLieTerm0Field
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M)
    g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckLieTerm0Field
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.deTurckLieTerm0Field target :: scope.openDecls } }

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieTerm0Field_eq_coeffField
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T')
      δ')
    (s : ℝ) :
    deTurckLieTerm0Field (I := I) g₀ g_bg T T' hδ hδ' s =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieCoeffField (I := I) (M := M)
        g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg :=
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckLieTerm0Field_eq_coeffField
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.deTurckLieTerm0Field_eq_coeffField target :: scope.openDecls } }

end DifferentialGeometry.Analysis.Spectral

end
