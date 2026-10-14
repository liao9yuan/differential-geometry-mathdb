import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightLimit
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightDivergence
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.CoefficientLimits
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.ChartTestDecoupling
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.L2Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.L2Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.WeightedIntegrability
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.ChartPartial.WeakPartials
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.TensorChartBilinearData
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.AbstractChartPull
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionDirichlet
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapSource
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Product.Scalar
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.PartitionOfUnityApproximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian

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

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

def eigenvectorRotatedTestSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    SmoothCcTensor g r s :=
  rotatedTestSection (I := I) (M := M) g r s α P₀
    (chartTestPullback (I := I) (M := M) α ψ)
    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_support)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorRotatedTestSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorRotatedTestSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorRotatedTestSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorRotatedTestSection

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorComponentEuclid_eigenvectorRotatedTestSection_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P : TensorCompIdx (E := E) r s) :
    Set.EqOn
      (tensorComponentEuclid (I := I) (M := M) g r s
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_support) α P)
      (fun y => covChartMetricGramInv (I := I) (M := M) g r s α y P P₀ * ψ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [eigenvectorRotatedTestSection,
    tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s _ α P hy,
    rotatedTestSection_chartComp (I := I) (M := M) g r s α P₀
      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
      (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_support)
      P hy,
    chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α ψ hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorComponentEuclid_eigenvectorRotatedTestSection_eqOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorComponentEuclid_eigenvectorRotatedTestSection_eqOn target :: scope.openDecls } }

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenvectorRotatedTestSection_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
        hψ hψ_cs hψ_support).toFun ⊆ (chartAt H α).source := by
  classical
  refine (closure_minimal ?_
    (isClosed_tsupport (chartTestPullback (I := I) (M := M) α ψ))).trans
    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hψ_cs hψ_support)
  intro b hb
  rw [Function.mem_support] at hb
  by_contra hb_notin
  refine hb ?_
  rw [eigenvectorRotatedTestSection, rotatedTestSection]
  rw [show (∑ Q : CompIdx E r s,
        chartBasisTensorSection (I := I) (M := M) g r s α
          (fun c : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q c *
            chartTestPullback (I := I) (M := M) α ψ c)
          (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ))
          (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_support))
          Q).toFun b =
      ∑ Q : CompIdx E r s,
        (chartBasisTensorSection (I := I) (M := M) g r s α
          (fun c : M => gramInvWeight (I := I) (M := M) g r s α P₀ Q c *
            chartTestPullback (I := I) (M := M) α ψ c)
          (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ))
          (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
              hψ_cs hψ_support))
          Q).toFun b
      from by
        induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
        | empty => simp [SmoothCcTensor.toFun_apply, SmoothCcTensor.toSection_zero]
        | insert Q t hQ ih =>
            rw [Finset.sum_insert hQ, Finset.sum_insert hQ,
              SmoothCcTensor.toFun_add, Pi.add_apply, ih]]
  refine Finset.sum_eq_zero (fun Q _ => ?_)
  rw [SmoothCcTensor.toFun_apply, chartBasisTensorSection_toSection_apply,
    image_eq_zero_of_notMem_tsupport hb_notin, _root_.MulZeroClass.mul_zero, zero_smul,
    Tensor0SBundle.TensorRSSpace.toModel_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorRotatedTestSection_tsupport_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorRotatedTestSection_tsupport_subset target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
lemma eigenvectorMainDir_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_support)) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      _root_.Filter.atTop
      (𝓝 ((1 - i.fst.val) *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) α P₀ :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
  classical
  set vRot : SmoothCcTensor g r s :=
    eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_support
    with hvRot_def
  set φ : TensorL2 r s g :=
    tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i
    with hφ_def
  set Sh1 : SmoothCcTensorH1 g r s :=
    ⟨pouSmul (I := I) (M := M) g r s α vRot⟩ with hSh1_def
  have hSh1_to : Sh1.toCcTensor = pouSmul (I := I) (M := M) g r s α vRot := rfl
  have hw_tendsto :
      Filter.Tendsto
        (fun n => smoothToTensorH1Compl (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n))
        _root_.Filter.atTop
        (𝓝 (eigenvectorResolvent (I := I) (M := M) g r s i)) :=
    eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i
  have h_dir :=
    smoothApprox_dirichlet_tendsto (I := I) (M := M) g r s i Sh1
      hw_tendsto
  have h_weak :
      ⟪eigenvectorResolvent (I := I) (M := M) g r s i,
          smoothToTensorH1Compl (I := I) (M := M) g r s Sh1⟫_ℝ =
        ⟪(Sh1.toCcTensor : TensorL2 r s g), φ⟫_ℝ :=
    eigenWeakEquation (I := I) (M := M) g r s i Sh1
  have h_resolvent :
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i) =
        i.fst.val • φ := by
    have h_eq := eigenvector_eq_resolvent_smul (I := I) (M := M)
      g r s i
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    rw [hφ_def, h_eq, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
  have h_l2part :
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i),
          (Sh1.toCcTensor : TensorL2 r s g)⟫_ℝ =
        i.fst.val * ⟪(Sh1.toCcTensor : TensorL2 r s g), φ⟫_ℝ := by
    rw [h_resolvent, inner_smul_left, starRingEnd_apply, _root_.TrivialStar.star_trivial,
      real_inner_comm]
  have h_md_eq :
      ⟪eigenvectorResolvent (I := I) (M := M) g r s i,
            smoothToTensorH1Compl (I := I) (M := M) g r s Sh1⟫_ℝ -
          ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i),
            (Sh1.toCcTensor : TensorL2 r s g)⟫_ℝ =
        (1 - i.fst.val) *
          ⟪((pouSmul (I := I) (M := M) g r s α vRot : SmoothCcTensor g r s) :
              TensorL2 r s g), φ⟫_ℝ := by
    rw [h_weak, h_l2part, hSh1_to]; ring
  rw [h_md_eq] at h_dir
  have h_pull :
      ⟪((pouSmul (I := I) (M := M) g r s α vRot : SmoothCcTensor g r s) :
          TensorL2 r s g), φ⟫_ℝ =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s φ α Q :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    tensorL2Inner_pouSmul_tensorL2ChartComponent_pull (I := I) (M := M)
      g r s α φ vRot
      (eigenvectorRotatedTestSection_tsupport_subset (I := I) (M := M)
        g r s α P₀ hψ hψ_cs hψ_support)
  have h_collapse :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
                ((tensorL2ChartComponent (I := I) (M := M) g r s φ α Q :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine MeasureTheory.setIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y hy => ?_)
    have hcomp : ∀ P : CompIdx E r s,
        tensorComponentEuclid (I := I) (M := M) g r s vRot α P y =
          covChartMetricGramInv (I := I) (M := M) g r s α y P P₀ * ψ y :=
      fun P => tensorComponentEuclid_eigenvectorRotatedTestSection_eqOn
        (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_support P hy
    rw [show (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s φ α Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) =
        ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
        from ?_]
    · ring
    rw [Finset.sum_comm]
    have hstep : ∀ Q : CompIdx E r s,
        (∑ P : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s φ α Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) =
          (if Q = P₀ then (1 : ℝ) else 0) *
            (((tensorL2ChartComponent (I := I) (M := M) g r s φ α Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              ψ y) := by
      intro Q
      rw [show (∑ P : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s vRot α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s φ α Q :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) =
          (∑ P : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α Q P y *
              covChartMetricGramInv (I := I) (M := M) g r s α y P P₀) *
            (((tensorL2ChartComponent (I := I) (M := M) g r s φ α Q :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              ψ y)
        from by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun P _ => ?_)
          rw [hcomp P, covChartMetricGram_symm (I := I) (M := M) g r s α P Q y]
          ring]
      rw [covChartMetricGram_mul_inv_collapse (I := I) (M := M) g r s α hy Q P₀]
    rw [Finset.sum_congr rfl (fun Q _ => hstep Q),
      Finset.sum_eq_single P₀]
    · rw [if_pos rfl, one_mul]
    · intro Q _ hQ
      rw [if_neg hQ, _root_.MulZeroClass.zero_mul]
    · intro hP₀
      exact absurd (Finset.mem_univ P₀) hP₀
  have h_eq : (1 - i.fst.val) *
        ⟪((pouSmul (I := I) (M := M) g r s α vRot : SmoothCcTensor g r s) :
            TensorL2 r s g), φ⟫_ℝ =
      (1 - i.fst.val) *
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [h_pull, h_collapse]
  rw [hφ_def] at h_eq
  rw [← h_eq]
  exact h_dir

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorMainDir_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorMainDir_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorMainDir_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorMainDir_tendsto

omit [CompleteSpace E] in
private lemma crossLeftPairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r (s + 1))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2 (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n))
            α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
          tensorComponentEuclid (I := I) (M := M) g r (s + 1)
            (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α)
              (rotatedTestSection (I := I) (M := M) g r s α P₀
                (chartTestPullback (I := I) (M := M) α ψ)
                (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                  hψ_cs hψ_support)))
            α Q y))
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : _root_.MeasureTheory.MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
        crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    have h := density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_support
    exact h
  have hcut_memLp : _root_.MeasureTheory.MemLp (fun y =>
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2 (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n))
        α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := Lp.memLp _
  have hprod : _root_.MeasureTheory.MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2 (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n))
        α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hcut_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine (MeasureTheory.ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr
    (Filter.Eventually.of_forall (fun y hy => ?_))
  simp only []
  rw [tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_chartTestPullback_eqOn
    (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_support Q hy]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftPairing_integrable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftPairing_integrable target :: scope.openDecls } }

omit [CompleteSpace E] in
lemma crossLeftLimitPairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r (s + 1))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : _root_.MeasureTheory.MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
        crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_support
  have hlim_memLp : _root_.MeasureTheory.MemLp (fun y =>
      ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := Lp.memLp _
  have hprod : _root_.MeasureTheory.MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hlim_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitPairing_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitPairing_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitPairing_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitPairing_integrable

omit [CompleteSpace E] in
lemma eigenvectorCrossLeft_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_support) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      _root_.Filter.atTop
      (𝓝 (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                  crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossLeftLimitComponent (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
  classical
  set mtest : TensorCompIdx (E := E) r (s + 1) → TensorCompIdx (E := E) r (s + 1) →
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    fun P Q => (density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_support).toLp _ with hmtest_def
  have h_dir : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      Filter.Tendsto
        (fun n => ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2 (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n))
            α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α))
        _root_.Filter.atTop
        (𝓝 (∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α))) :=
    fun P Q => tendsto_lp_inner_integral
      (μ := chartLebesgueMeasure (I := I) (M := M) α) (mtest P Q)
      (crossLeftComponent_tendsto (I := I) (M := M) g r s i α P)
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n => ∑ P : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                (tensorCovGradL2 (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n))
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartLebesgueMeasure (I := I) (M := M) α))
        _root_.Filter.atTop
        (𝓝 (∑ P : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartLebesgueMeasure (I := I) (M := M) α))) :=
    tendsto_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun P _ => tendsto_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
        (fun Q _ => h_dir P Q))
  have h_cross_n : ∀ n : ℕ,
      ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_support) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2 (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n))
              α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartLebesgueMeasure (I := I) (M := M) α) := by
    intro n
    rw [eigenvectorRotatedTestSection,
      tensorCovDerivCrossLeft_integral_eq_chartPull (I := I) (M := M) g r s α
        (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
        (rotatedTestSection (I := I) (M := M) g r s α P₀
          (chartTestPullback (I := I) (M := M) α ψ)
          (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
          (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
            hψ_cs hψ_support))]
    have hpair : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n))
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y *
                tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                  (prependCovGradSlot (I := I) (M := M) g r s
                    (chartAtlasPOU I M α)
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      (chartTestPullback (I := I) (M := M) α ψ)
                      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                      (chartTestPullback_tsupport_subset_source
                        (I := I) (M := M) α hψ_cs hψ_support)))
                  α Q y)
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2 (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n))
              α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartLebesgueMeasure (I := I) (M := M) α) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine (MeasureTheory.integral_congr_ae ?_).symm
      filter_upwards [h_m_ae,
        (MeasureTheory.ae_restrict_iff'
          (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr
          (Filter.Eventually.of_forall (fun y hy =>
            tensorComponentEuclid_prependCovGradSlot_rotatedTestSection_chartTestPullback_eqOn
              (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_support Q hy))]
        with y hy_m hy_decouple
      rw [hy_m, hy_decouple]
      ring
    rw [show (fun y => densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r (s + 1),
            ∑ Q : TensorCompIdx (E := E) r (s + 1),
              covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n))
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y *
                tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                  (prependCovGradSlot (I := I) (M := M) g r s
                    (chartAtlasPOU I M α)
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      (chartTestPullback (I := I) (M := M) α ψ)
                      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                      (chartTestPullback_tsupport_subset_source
                        (I := I) (M := M) α hψ_cs hψ_support)))
                  α Q y)) =
        fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
                  (tensorCovGradL2 (I := I) (M := M) g r s
                    (eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n))
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y *
                tensorComponentEuclid (I := I) (M := M) g r (s + 1)
                  (prependCovGradSlot (I := I) (M := M) g r s
                    (chartAtlasPOU I M α)
                    (rotatedTestSection (I := I) (M := M) g r s α P₀
                      (chartTestPullback (I := I) (M := M) α ψ)
                      (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                      (chartTestPullback_tsupport_subset_source
                        (I := I) (M := M) α hψ_cs hψ_support)))
                  α Q y)
        from funext (fun y => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun P _ => Finset.mul_sum _ _ _))]
    rw [MeasureTheory.integral_finsetSum _ (fun P _ =>
        MeasureTheory.integrable_finsetSum _ (fun Q _ =>
          crossLeftPairing_integrable (I := I) (M := M) g r s i
            α P₀ P Q hψ hψ_cs hψ_support n))]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [MeasureTheory.integral_finsetSum _ (fun Q _ =>
        crossLeftPairing_integrable (I := I) (M := M) g r s i
          α P₀ P Q hψ hψ_cs hψ_support n)]
    exact Finset.sum_congr rfl (fun Q _ => hpair P Q)
  have h_limit_eq :
      ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartLebesgueMeasure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : TensorCompIdx (E := E) r (s + 1),
              ∑ Q : TensorCompIdx (E := E) r (s + 1),
                covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                    crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((crossLeftLimitComponent (I := I) (M := M)
                    g r s i α P :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have h_summand : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
        ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_m_ae] with y hy_m
      rw [hy_m]; ring
    rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
      (fun Q _ => h_summand P Q))]
    rw [Finset.sum_congr rfl (fun P _ =>
      (MeasureTheory.integral_finsetSum _ (fun Q _ =>
        crossLeftLimitPairing_integrable (I := I) (M := M)
          g r s i α P₀ P Q hψ hψ_cs hψ_support)).symm)]
    rw [← MeasureTheory.integral_finsetSum _ (fun P _ =>
      MeasureTheory.integrable_finsetSum _ (fun Q _ =>
        crossLeftLimitPairing_integrable (I := I) (M := M)
          g r s i α P₀ P Q hψ hψ_cs hψ_support))]
    refine MeasureTheory.setIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y _ => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [show (fun n => ∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_support) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (fun n => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r (s + 1)
              (tensorCovGradL2 (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n))
              α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartLebesgueMeasure (I := I) (M := M) α))
      from funext h_cross_n]
  rw [← h_limit_eq]
  exact h_sum_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeft_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeft_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeft_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossLeft_tendsto

omit [CompleteSpace E] in
private lemma crossRightValuePairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)
            α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : _root_.MeasureTheory.MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
        crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_support
  have hcut_memLp : _root_.MeasureTheory.MemLp (fun y =>
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g)
        α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := Lp.memLp _
  have hprod : _root_.MeasureTheory.MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g)
        α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hcut_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightValuePairing_integrable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightValuePairing_integrable target :: scope.openDecls } }

omit [CompleteSpace E] in
lemma crossRightValueLimitPairing_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (P Q : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hm_memLp : _root_.MeasureTheory.MemLp (fun y => densityOnEuclid (I := I) g α y *
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
        crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_support
  have hlim_memLp : _root_.MeasureTheory.MemLp (fun y =>
      ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := Lp.memLp _
  have hprod : _root_.MeasureTheory.MemLp (fun y =>
      (fun y => densityOnEuclid (I := I) g α y *
        (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y) y *
      ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 1
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hlim_memLp.mul' hm_memLp
  refine (memLp_one_iff_integrable.mp hprod).congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightValueLimitPairing_integrable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightValueLimitPairing_integrable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightValueLimitPairing_integrable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightValueLimitPairing_integrable

omit [CompleteSpace E] in
lemma eigenvectorCrossRight_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
      _root_.Filter.atTop
      (𝓝 (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((crossRightLimitComponent (I := I) (M := M)
                  g r s i α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
  classical
  set mtest : TensorCompIdx (E := E) r s → TensorCompIdx (E := E) r s →
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    fun P Q => (density_coeff_test_memLp (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      hψ hψ_cs hψ_support).toLp _ with hmtest_def
  have h_dir : ∀ (P Q : TensorCompIdx (E := E) r s),
      Filter.Tendsto
        (fun n => ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)
            α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α))
        _root_.Filter.atTop
        (𝓝 (∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α))) :=
    fun P Q => tendsto_lp_inner_integral
      (μ := chartLebesgueMeasure (I := I) (M := M) α) (mtest P Q)
      (crossRightComponent_tendsto (I := I) (M := M) g r s i α P)
  have h_sum_tendsto :
      Filter.Tendsto
        (fun n => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartLebesgueMeasure (I := I) (M := M) α))
        _root_.Filter.atTop
        (𝓝 (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartLebesgueMeasure (I := I) (M := M) α))) :=
    tendsto_finsetSum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => tendsto_finsetSum
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => h_dir P Q))
  have h_value_n : ∀ n : ℕ,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                covChartMetricGram (I := I) (M := M) g r s α P Q y *
                    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                    (((eigenvectorSmoothApprox (I := I) (M := M)
                        g r s i n).toCcTensor) : TensorL2 r s g)
                    α P :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∫ y, (mtest P Q : EuclN → ℝ) y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
              ∂(chartLebesgueMeasure (I := I) (M := M) α) := by
    intro n
    have hpair : ∀ (P Q : TensorCompIdx (E := E) r s),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
              ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor) : TensorL2 r s g)
              α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartLebesgueMeasure (I := I) (M := M) α) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine (MeasureTheory.integral_congr_ae ?_).symm
      filter_upwards [h_m_ae] with y hy_m
      rw [hy_m]; ring
    rw [show (fun y => densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) *
            ψ y) =
        fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            densityOnEuclid (I := I) g α y *
              (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                  EuclN → ℝ) y) *
              ψ y
        from funext (fun y => by
          simp only [Finset.sum_mul, Finset.mul_sum])]
    rw [MeasureTheory.integral_finsetSum _ (fun P _ =>
        MeasureTheory.integrable_finsetSum _ (fun Q _ =>
          crossRightValuePairing_integrable (I := I) (M := M) g r s i
            α P₀ P Q hψ hψ_cs hψ_support n))]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [MeasureTheory.integral_finsetSum _ (fun Q _ =>
        crossRightValuePairing_integrable (I := I) (M := M) g r s i
          α P₀ P Q hψ hψ_cs hψ_support n)]
    exact Finset.sum_congr rfl (fun Q _ => hpair P Q)
  have h_limit_eq :
      ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartLebesgueMeasure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                covChartMetricGram (I := I) (M := M) g r s α P Q y *
                    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((crossRightLimitComponent (I := I) (M := M)
                    g r s i α P :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have h_summand : ∀ (P Q : TensorCompIdx (E := E) r s),
        ∫ y, (mtest P Q : EuclN → ℝ) y *
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      intro P Q
      have h_m_ae : (mtest P Q : EuclN → ℝ)
          =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
          fun y => densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) * ψ y := by
        rw [hmtest_def]; exact MemLp.coeFn_toLp _
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_m_ae] with y hy_m
      rw [hy_m]; ring
    rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
      (fun Q _ => h_summand P Q))]
    rw [Finset.sum_congr rfl (fun P _ =>
      (MeasureTheory.integral_finsetSum _ (fun Q _ =>
        crossRightValueLimitPairing_integrable (I := I) (M := M)
          g r s i α P₀ P Q hψ hψ_cs hψ_support)).symm)]
    rw [← MeasureTheory.integral_finsetSum _ (fun P _ =>
      MeasureTheory.integrable_finsetSum _ (fun Q _ =>
        crossRightValueLimitPairing_integrable (I := I) (M := M)
          g r s i α P₀ P Q hψ hψ_cs hψ_support))]
    refine MeasureTheory.setIntegral_congr_fun
      (chartTargetEuclid_measurableSet (I := I) (M := M) α) (fun y _ => ?_)
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [show (fun n => ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      (fun n => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          ∫ y, (mtest P Q : EuclN → ℝ) y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor) : TensorL2 r s g)
              α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
            ∂(chartLebesgueMeasure (I := I) (M := M) α))
      from funext h_value_n]
  rw [← h_limit_eq]
  exact h_sum_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_tendsto

omit [CompleteSpace E] in
lemma eigenvectorCrossRightGrad_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α P₀ l y *
            euclidPartial (E := E) l ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
      _root_.Filter.atTop
      (𝓝 (-∫ y in chartTargetEuclid (I := I) (M := M) α,
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
  classical
  set m : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    (test_memLp (I := I) (M := M) α hψ hψ_cs).toLp _ with hm_def
  set gseq : ℕ → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) := fun n =>
    (crossRightGradCoeffDivSum_memLp (I := I) (M := M)
      g r s i α P₀ n).toLp _ with hgseq_def
  set glim : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    (crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s i α P₀).toLp _ with hglim_def
  have h_int_n : ∀ n : ℕ,
      ∑ l : Fin (Module.finrank ℝ E),
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
                crossRightTestGradTerm (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α P₀ l y *
              euclidPartial (E := E) l ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        -(∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α)) := by
    intro n
    rw [crossRightTestGradTerm_byParts (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor
      α P₀ hψ hψ_cs hψ_support]
    congr 1
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] ψ := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (fun z => densityOnEuclid (I := I) g α z *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α P₀ l z) y := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod :
        (fun y => (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (fun z => densityOnEuclid (I := I) g α z *
                crossRightTestGradTerm (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α P₀ l z) y) * ψ y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    exact MeasureTheory.integral_congr_ae h_ae_prod
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] ψ := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    exact MeasureTheory.integral_congr_ae h_ae_prod
  have h_tendsto_lp : Filter.Tendsto gseq _root_.Filter.atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact crossRightGradCoeffDivSum_tendsto (I := I) (M := M)
      g r s i α P₀
  have h_main := tendsto_lp_inner_integral
    (μ := chartLebesgueMeasure (I := I) (M := M) α) m h_tendsto_lp
  rw [h_int_lim] at h_main
  have h_neg := h_main.neg
  refine h_neg.congr ?_
  intro n
  exact (h_int_n n).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightGrad_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightGrad_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightGrad_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRightGrad_tendsto

omit [CompleteSpace E] in
lemma eigenvectorSource_integral_split
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_support) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
            hψ hψ_cs hψ_support)) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
    (∫ x, tensorCovDerivCrossLeft (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_support) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
    (∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_support) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  classical
  set wₙ : SmoothCcTensor g r s :=
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor
    with hwₙ_def
  set vRot : SmoothCcTensor g r s :=
    eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_support
    with hvRot_def
  set Amain : M → ℝ := fun x => tensorCovDerivPointwiseInner (I := I) (M := M)
    g r s wₙ (scalarSmul (I := I) (M := M) g r s (chartAtlasPOU I M α) vRot) x
    with hAmain_def
  set Bleft : M → ℝ := fun x => tensorCovDerivCrossLeft (I := I) (M := M)
    g r s (chartAtlasPOU I M α) wₙ vRot x with hBleft_def
  set Cright : M → ℝ := fun x => tensorCovDerivCrossRight (I := I) (M := M)
    g r s (chartAtlasPOU I M α) wₙ vRot x with hCright_def
  have hAmain_int : _root_.MeasureTheory.Integrable Amain
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s wₙ
      (scalarSmul (I := I) (M := M) g r s (chartAtlasPOU I M α) vRot)
  have hBleft_int : _root_.MeasureTheory.Integrable Bleft
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h_eq : Bleft = fun x => tensorInnerPointwise (I := I) (M := M)
        g r (s + 1) x
        ((covGrad (I := I) (M := M) g r s wₙ).toFun x)
        ((prependCovGradSlot (I := I) (M := M) g r s
          (chartAtlasPOU I M α) vRot).toFun x) := by
      funext x
      rw [hBleft_def]
      exact tensorCovDerivCrossLeft_eq_tensorInnerPointwise_grad
        (I := I) (M := M) g r s (chartAtlasPOU I M α) wₙ vRot x
    rw [h_eq]
    exact SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      (covGrad (I := I) (M := M) g r s wₙ)
      (prependCovGradSlot (I := I) (M := M) g r s (chartAtlasPOU I M α) vRot)
  have hCright_int : _root_.MeasureTheory.Integrable Cright
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    have h_eq : Cright = fun x => tensorInnerPointwise (I := I) (M := M)
        g r s x (wₙ.toFun x)
        ((covDerivAlongGrad (I := I) (M := M) g r s vRot
          (chartAtlasPOU I M α)).toFun x) := by
      funext x
      rw [hCright_def]
      exact tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
        (I := I) (M := M) g r s (chartAtlasPOU I M α) wₙ vRot x
    rw [h_eq]
    exact SmoothCcTensor.integrable_inner_cross (I := I) (M := M) wₙ
      (covDerivAlongGrad (I := I) (M := M) g r s vRot (chartAtlasPOU I M α))
  have h_pointwise : ∀ x,
      tensorCovDerivPointwiseInner (I := I) (M := M)
        g r s (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
        vRot x =
      Amain x - Bleft x + Cright x := by
    intro x
    rw [eigenvectorPouApprox, pouSmul_eq_scalarSmul (I := I) (M := M)
      g r s α wₙ, hAmain_def, hBleft_def, hCright_def]
    exact tensorCovDerivPointwiseInner_scalarSmul_left (I := I) (M := M)
      g r s (chartAtlasPOU I M α) wₙ vRot x
  calc ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
          vRot x ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      = ∫ x, ((fun x => Amain x - Bleft x) x + Cright x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall h_pointwise)
    _ = (∫ x, (fun x => Amain x - Bleft x) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, Cright x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        MeasureTheory.integral_add (hAmain_int.sub hBleft_int) hCright_int
    _ = ((∫ x, Amain x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
          ∫ x, Bleft x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, Cright x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [MeasureTheory.integral_sub hAmain_int hBleft_int]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSource_integral_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSource_integral_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSource_integral_split ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSource_integral_split

omit [CompleteSpace E] in
private lemma density_crossRightTestGradTerm_partialTest_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        crossRightTestGradTerm (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P₀ l y *
        euclidPartial (E := E) l ψ y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hdψ_cd : ContDiff ℝ ∞ (euclidPartial (E := E) l ψ) :=
    euclidPartial_contDiff (E := E) hψ l
  have hdψ_cs : HasCompactSupport (euclidPartial (E := E) l ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport ψ) hψ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyψ
    exact hy (euclidPartial_zero_off_tsupport (E := E) l hyψ)
  have hdψ_support : tsupport (euclidPartial (E := E) l ψ) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    refine (closure_minimal ?_ (isClosed_tsupport _)).trans hψ_support
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hz'
    exact hz (euclidPartial_zero_off_tsupport (E := E) l hz')
  have hcd : ContDiff ℝ ∞ (fun y => densityOnEuclid (I := I) g α y *
      crossRightTestGradTerm (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P₀ l y *
      euclidPartial (E := E) l ψ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (densityOnEuclid_mul_crossRightTestGradTerm_contDiffOn (I := I) (M := M)
        g r s (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P₀ l)
      hdψ_cd hdψ_support
  have hcs : HasCompactSupport (fun y => densityOnEuclid (I := I) g α y *
      crossRightTestGradTerm (I := I) (M := M) g r s
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor α P₀ l y *
      euclidPartial (E := E) l ψ y) :=
    hasCompactSupport_mul_chartTest (E := E) hdψ_cs
  exact (hcd.continuous.integrable_of_hasCompactSupport hcs).restrict

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.density_crossRightTestGradTerm_partialTest_integrable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.density_crossRightTestGradTerm_partialTest_integrable target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma density_crossRightValueSum_test_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_sum_int : _root_.MeasureTheory.Integrable (fun y => ∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        densityOnEuclid (I := I) g α y *
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (((eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor) : TensorL2 r s g)
              α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y)
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    MeasureTheory.integrable_finsetSum _ (fun P _ =>
      MeasureTheory.integrable_finsetSum _ (fun Q _ =>
        crossRightValuePairing_integrable (I := I) (M := M) g r s i
          α P₀ P Q hψ hψ_cs hψ_support n))
  refine h_sum_int.congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.density_crossRightValueSum_test_integrable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.density_crossRightValueSum_test_integrable target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma tensorL2ChartComponentCutoff_smoothApprox_ae_all
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (n : ℕ) :
    ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      ∀ P : TensorCompIdx (E := E) r s,
        ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (((eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) : TensorL2 r s g)
          α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y =
        cutoffComponentEuclid (I := I) (M := M) g r s
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor α P.1 P.2 y :=
  MeasureTheory.ae_all_iff.mpr (fun P =>
    tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn (I := I) (M := M)
      g r s (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor α P)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_smoothApprox_ae_all
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_smoothApprox_ae_all target :: scope.openDecls } }

omit [CompleteSpace E] in
lemma eigenvectorCrossRight_integral_eq_value_plus_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) (n : ℕ) :
    (∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
        (chartAtlasPOU I M α)
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor
        (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
          hψ hψ_cs hψ_support) x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    ∑ l : Fin (Module.finrank ℝ E),
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
            crossRightTestGradTerm (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀ l y *
          euclidPartial (E := E) l ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  rw [eigenvectorRotatedTestSection,
    tensorCovDerivCrossRight_integral_eq_chartPull (I := I) (M := M) g r s α
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor
      (rotatedTestSection (I := I) (M := M) g r s α P₀
        (chartTestPullback (I := I) (M := M) α ψ)
        (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
        (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
          hψ_cs hψ_support))]
  set valueIntegrand : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
    (∑ P : TensorCompIdx (E := E) r s,
      ∑ Q : TensorCompIdx (E := E) r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (((eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) : TensorL2 r s g)
            α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
    ψ y with hvalueIntegrand_def
  set gradIntegrand : EuclN → ℝ := fun y =>
    ∑ l : Fin (Module.finrank ℝ E),
      densityOnEuclid (I := I) g α y *
          crossRightTestGradTerm (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α P₀ l y *
        euclidPartial (E := E) l ψ y with hgradIntegrand_def
  have h_integrand_ae :
      (fun y => densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
            tensorComponentEuclid (I := I) (M := M) g r s
              (covDerivAlongGrad (I := I) (M := M) g r s
                (rotatedTestSection (I := I) (M := M) g r s α P₀
                  (chartTestPullback (I := I) (M := M) α ψ)
                  (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                  (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                    hψ_cs hψ_support))
                (chartAtlasPOU I M α)) α Q y))
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      fun y => valueIntegrand y + gradIntegrand y := by
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (chartTargetEuclid_measurableSet (I := I) (M := M) α),
      (tensorL2ChartComponentCutoff_smoothApprox_ae_all
        (I := I) (M := M) g r s i α n :
        ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α), _)]
      with y hy hcut
    have hdec : ∀ Q : CompIdx E r s,
        tensorComponentEuclid (I := I) (M := M) g r s
          (covDerivAlongGrad (I := I) (M := M) g r s
            (rotatedTestSection (I := I) (M := M) g r s α P₀
              (chartTestPullback (I := I) (M := M) α ψ)
              (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
              (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                hψ_cs hψ_support))
            (chartAtlasPOU I M α)) α Q y =
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y * ψ y +
          ∑ l : Fin (Module.finrank ℝ E),
            crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
              euclidPartial (E := E) l ψ y :=
      fun Q => tensorComponentEuclid_covDerivAlongGrad_rotatedTestSection_chartTestPullback_eqOn
        (I := I) (M := M) g r s α P₀ hψ hψ_cs hψ_support Q hy
    change densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
            tensorComponentEuclid (I := I) (M := M) g r s
              (covDerivAlongGrad (I := I) (M := M) g r s
                (rotatedTestSection (I := I) (M := M) g r s α P₀
                  (chartTestPullback (I := I) (M := M) α ψ)
                  (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                  (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                    hψ_cs hψ_support))
                (chartAtlasPOU I M α)) α Q y) =
      valueIntegrand y + gradIntegrand y
    rw [hvalueIntegrand_def, hgradIntegrand_def]
    beta_reduce
    have hgrad_per_l : ∀ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
            crossRightTestGradTerm (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀ l y *
          euclidPartial (E := E) l ψ y =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              (crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
                euclidPartial (E := E) l ψ y)) := by
      intro l
      rw [crossRightTestGradTerm, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [← hcut P]
      ring
    have hLHS : densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s
                (covDerivAlongGrad (I := I) (M := M) g r s
                  (rotatedTestSection (I := I) (M := M) g r s α P₀
                    (chartTestPullback (I := I) (M := M) α ψ)
                    (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
                    (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                      hψ_cs hψ_support))
                  (chartAtlasPOU I M α)) α Q y) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              (crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y * ψ y +
                ∑ l : Fin (Module.finrank ℝ E),
                  crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
                    euclidPartial (E := E) l ψ y)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [hdec Q]
    have hVal : densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (((eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor) : TensorL2 r s g)
                α P :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              (crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ψ y)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      ring
    have hGrad : (∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α P₀ l y *
            euclidPartial (E := E) l ψ y) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y *
              ∑ l : Fin (Module.finrank ℝ E),
                crossRightTestGradCoeff (I := I) (M := M) g r s α P₀ Q l y *
                  euclidPartial (E := E) l ψ y) := by
      rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hgrad_per_l l),
        Finset.sum_comm]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hLHS, hVal, hGrad, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  rw [MeasureTheory.integral_congr_ae h_integrand_ae]
  rw [MeasureTheory.integral_add
    (hvalueIntegrand_def ▸ density_crossRightValueSum_test_integrable
      (I := I) (M := M) g r s i α P₀ hψ hψ_cs hψ_support n)
    (hgradIntegrand_def ▸ MeasureTheory.integrable_finsetSum _
      (fun l _ => density_crossRightTestGradTerm_partialTest_integrable
        (I := I) (M := M) g r s i α P₀ l hψ hψ_cs hψ_support n))]
  congr 1
  rw [hgradIntegrand_def]
  exact MeasureTheory.integral_finsetSum _
    (fun l _ => density_crossRightTestGradTerm_partialTest_integrable
      (I := I) (M := M) g r s i α P₀ l hψ hψ_cs hψ_support n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_integral_eq_value_plus_grad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_integral_eq_value_plus_grad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_integral_eq_value_plus_grad ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorCrossRight_integral_eq_value_plus_grad

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
