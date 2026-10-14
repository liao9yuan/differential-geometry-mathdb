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
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma dim1_smul_rep (h1 : Module.finrank ℝ E = 1) (e : E) (he : e ≠ 0) (v : E) :
    ∃ c : ℝ, c • e = v :=
  exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := E) h1 he v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.dim1_smul_rep
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.dim1_smul_rep target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
lemma dim1_domDomCongr_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) ℝ) (ρ : Equiv.Perm (Fin d)) :
    ContinuousMultilinearMap.domDomCongr ρ f = f := by
  classical
  have hpos : 0 < Module.finrank ℝ E := h1 ▸ Nat.one_pos
  set b := Module.finBasis ℝ E with hb
  set e : E := b ⟨0, hpos⟩ with he_def
  have he : e ≠ 0 := b.ne_zero _
  apply ContinuousMultilinearMap.ext
  intro v
  have hrep : ∀ i : Fin d, ∃ c : ℝ, c • e = v i := fun i => dim1_smul_rep h1 e he (v i)
  choose c hc using hrep
  have hv : v = fun i => c i • e := by
    funext i
    exact (hc i).symm
  rw [ContinuousMultilinearMap.domDomCongr_apply, hv]
  have hL : (f fun i => c (ρ i) • e) = (∏ i, c (ρ i)) • f (fun _ => e) :=
    f.map_smul_univ (fun i => c (ρ i)) (fun _ => e)
  have hR : (f fun i => c i • e) = (∏ i, c i) • f (fun _ => e) :=
    f.map_smul_univ c (fun _ => e)
  rw [hL, hR, Equiv.prod_comp ρ c]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.dim1_domDomCongr_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.dim1_domDomCongr_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.dim1_domDomCongr_eq ``Submission.DifferentialGeometry.Analysis.Spectral.dim1_domDomCongr_eq

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dim1_slotPermCLM_eq (h1 : Module.finrank ℝ E = 1) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (x : M) (D : Tensor0SBundle.Tensor0SSpace d I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ x D = D := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM_apply]
  rw [dim1_domDomCongr_eq h1 (Tensor0SBundle.Tensor0SSpace.toModel D) ρ]
  exact Tensor0SBundle.Tensor0SSpace.ofModel_toModel (𝕜 := ℝ) D

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.dim1_slotPermCLM_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.dim1_slotPermCLM_eq target :: scope.openDecls } }

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one (h1 : Module.finrank ℝ E = 1)
    (g₁ : SmoothRiemannianMetric I M) (x : M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM
      (I := I) g₁ x = 0 := by
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciCometricFourTraceCLM]
  have hF : ∀ ρ₁ ρ₂ ρ₃ : Equiv.Perm (Fin 4),
      (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₁ x)
        + (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₂ x)
        - DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x
        - (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceFib
            (I := I) g₁ 2 x).comp
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.slotPermCLM (I := I) ρ₃ x)
        = 0 := by
    intro ρ₁ ρ₂ ρ₃
    apply ContinuousLinearMap.ext
    intro Z
    rw [sub_apply, sub_apply,
      add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [dim1_slotPermCLM_eq (I := I) h1 ρ₁ x Z, dim1_slotPermCLM_eq (I := I) h1 ρ₂ x Z,
      dim1_slotPermCLM_eq (I := I) h1 ρ₃ x Z]
    rw [zero_apply]
    abel
  rw [hF]
  rw [smul_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma dim1_linearizedRicciConnectionDifferenceOrder0CoeffField_eq_zero
    (h1 : Module.finrank ℝ E = 1) (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CoeffField
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw
    [Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CoeffField_toSection]
  change
    (Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CometricTracedCLM
      (I := I) g₀ g₁ x) = _
  rw
    [Analysis.Parabolic.TensorSpectral.linearizedRicciConnectionDifferenceOrder0CometricTracedCLM]
  rw [ricciCometricFourTraceCLM_eq_zero_of_finrank_eq_one (I := I) h1 g₁ x]
  rw [ContinuousLinearMap.zero_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.dim1_linearizedRicciConnectionDifferenceOrder0CoeffField_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.dim1_linearizedRicciConnectionDifferenceOrder0CoeffField_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.dim1_linearizedRicciConnectionDifferenceOrder0CoeffField_eq_zero ``Submission.DifferentialGeometry.Analysis.Spectral.dim1_linearizedRicciConnectionDifferenceOrder0CoeffField_eq_zero

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma dim1_ricciOrderZeroRiemannCoeff_eq_zero (h1 : Module.finrank ℝ E = 1)
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff
      (I := I) (M := M) g₀ g₁ = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ricciOrderZeroRiemannCoeff_toSection]
  change (Tensor0SBundle.TensorRSSpace.ofCLM
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib (I := I) g₁ x)) = _
  have hfib : DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib
      (I := I) g₁ x = 0 := by
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFib]
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective (𝕜 := ℝ)
    apply ContinuousMultilinearMap.ext
    intro v
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannBiContrFibFixedFrame_toModel]
    have hz : ∀ a b : Fin (Module.finrank ℝ E),
        (g₁.inner x) (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g₁) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
            (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame (I := I) g₁ x a x)
            (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame (I := I) g₁ x b x))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) *
          D.toModel ![
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame
                (I := I) g₁ x a x),
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (DifferentialGeometry.Geometry.Connection.smoothOrthoFrame
                (I := I) g₁ x b x)] = 0 := by
      intro a b
      rw [riemannOp_eq_zero_of_finrank_le_one
        (DifferentialGeometry.Geometry.Connection.LeviCivita g₁) h1.le]
      rw [map_zero, zero_apply, _root_.MulZeroClass.zero_mul]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hz a b))]
    rw [Finset.sum_const, Finset.sum_const]
    simp only [smul_zero, _root_.MulZeroClass.mul_zero]
    have : (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.TensorRSSpace 2 2 I x) D)) v = 0 := by
      change (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        ((0 : Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) D)) v = 0
      rw [zero_apply]
      rw [show (Tensor0SBundle.Tensor0SSpace.toModel (𝕜 := ℝ)
        (0 : Tensor0SBundle.Tensor0SSpace 2 I x)) = 0 from map_zero _]
      rfl
    rw [this]
  rw [hfib]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.dim1_ricciOrderZeroRiemannCoeff_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.dim1_ricciOrderZeroRiemannCoeff_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.dim1_ricciOrderZeroRiemannCoeff_eq_zero ``Submission.DifferentialGeometry.Analysis.Spectral.dim1_ricciOrderZeroRiemannCoeff_eq_zero

end DifferentialGeometry.Analysis.Spectral

end
