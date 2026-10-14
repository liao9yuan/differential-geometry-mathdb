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
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.SourceRotationCoefficientLimits
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.RotatedTestCrossTerms

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

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
theorem eigenvectorChartVariationalIdentity
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i' j' y *
            eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i α P₀ i' y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  set μ : ℝ := i.fst.val with hμ_def
  have hμ_ne : μ ≠ 0 := i.fst.val_ne_zero
  set φ : TensorL2 r s g :=
    tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i
    with hφ_def
  set P : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    (∑ i' : Fin (Module.finrank ℝ E),
      ∑ j' : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i' j' y *
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i α P₀ i' y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j' 1))
    ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hP_def
  set U : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
    ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hU_def
  set CL : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
      ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hCL_def
  set CRV : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          covChartMetricGram (I := I) (M := M) g r s α P' Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
      ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hCRV_def
  set CRGdiv : ℝ := ∫ y in chartTargetEuclid (I := I) (M := M) α,
    crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hCRGdiv_def
  set PRC : ℝ := ∫ y, densityOnEuclid (I := I) g α y *
      covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hPRC_def
  set LOV : ℝ := ∫ y, densityOnEuclid (I := I) g α y *
      covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hLOV_def
  set GD : ℝ := ∫ y, (∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y) * ψ y
    ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) with hGD_def
  have hcTE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  have h_per_n : ∀ n : ℕ,
      (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀)
        ψ =
      ((∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
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
      ((∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P' : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                  crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (((eigenvectorSmoothApprox (I := I) (M := M)
                      g r s i n).toCcTensor) : TensorL2 r s g)
                  α P' :
                  Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
          ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      ∑ l : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
              crossRightTestGradTerm (I := I) (M := M) g r s
                (eigenvectorSmoothApprox (I := I) (M := M)
                  g r s i n).toCcTensor α P₀ l y *
            euclidPartial (E := E) l ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M)
              g r s i α n)
            α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M)
              g r s i α n)
            α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M)
                g r s i α n)
              α P₀ l) y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    intro n
    rw [tensorComponent_chartBilinIdentity_of_dirichlet (I := I) (M := M) g r s
      (eigenvectorPouApprox (I := I) (M := M) g r s i α n) α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α) P₀
      (eigenvectorPouApprox_tsupport_subset_source (I := I) (M := M)
        g r s i α n)
      (eigenvectorPouApprox_component_tsupport_subset (I := I) (M := M)
        g r s i α P₀ n) hψ hψ_cs hψ_support]
    rw [show (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            (rotatedTestSection (I := I) (M := M) g r s α P₀
              (chartTestPullback (I := I) (M := M) α ψ)
              (chartTestPullback_contMDiffOn (I := I) (M := M) α hψ)
              (chartTestPullback_tsupport_subset_source (I := I) (M := M) α
                hψ_cs hψ_support)) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            (eigenvectorRotatedTestSection (I := I) (M := M) g r s α P₀
              hψ hψ_cs hψ_support) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
    rw [eigenvectorSource_integral_split (I := I) (M := M) g r s i
      α P₀ hψ hψ_cs hψ_support n,
      eigenvectorCrossRight_integral_eq_value_plus_grad (I := I) (M := M)
        g r s i α P₀ hψ hψ_cs hψ_support n]
  set L : ℝ := ((1 - μ) * U - CL + (CRV + -CRGdiv) - PRC - LOV + GD) with hL_def
  have h_rhs_tendsto : Filter.Tendsto
      (fun n => ((∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s
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
        ((∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ P' : TensorCompIdx (E := E) r s,
              ∑ Q : TensorCompIdx (E := E) r s,
                covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                  ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                    (((eigenvectorSmoothApprox (I := I) (M := M)
                        g r s i n).toCcTensor) : TensorL2 r s g)
                    α P' :
                    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                    EuclN → ℝ) y) *
            ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        ∑ l : Fin (Module.finrank ℝ E),
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            densityOnEuclid (I := I) g α y *
                crossRightTestGradTerm (I := I) (M := M) g r s
                  (eigenvectorSmoothApprox (I := I) (M := M)
                    g r s i n).toCcTensor α P₀ l y *
              euclidPartial (E := E) l ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) -
        (∫ y, densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M)
                g r s i α n)
              α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        (∫ y, densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M)
                g r s i α n)
              α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M)
                  g r s i α n)
                α P₀ l) y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
      atTop (𝓝 L) := by
    rw [hL_def]
    have h_md := eigenvectorMainDir_tendsto (I := I) (M := M) g r s i
      α P₀ hψ hψ_cs hψ_support
    refine (((((h_md.sub
      (eigenvectorCrossLeft_tendsto (I := I) (M := M) g r s i
        α P₀ hψ hψ_cs hψ_support)).add
      ((eigenvectorCrossRight_tendsto (I := I) (M := M) g r s i
        α P₀ hψ hψ_cs hψ_support).add
        (eigenvectorCrossRightGrad_tendsto (I := I) (M := M) g r s i
          α P₀ hψ hψ_cs hψ_support))).sub
      (covPrincipalRotationCoeff_source_tendsto (I := I) (M := M) g r s
        i α P₀ hψ hψ_cs hψ_support)).sub
      (covLowerOrderRotationValueCoeff_source_tendsto (I := I) (M := M)
        g r s i α P₀ hψ hψ_cs hψ_support)).add
      (weightedGradCoeffDivSum_source_tendsto (I := I) (M := M) g r s
        i α P₀ hψ hψ_cs hψ_support)).congr ?_
    intro n
    rfl
  have h_lhs_tendsto : Filter.Tendsto
      (fun n => (tensorPrincipalForm (I := I) (M := M) g α
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M)
            g r s i α n) α P₀)
        ψ)
      atTop (𝓝 (μ * P)) := by
    rw [hμ_def, hP_def]
    exact bilin_eigenvectorPouApprox_tendsto (I := I) (M := M) g r s i
      α P₀ hψ hψ_cs hψ_support
  have h_mu_P : μ * P = L := by
    refine tendsto_nhds_unique (h_lhs_tendsto.congr ?_) h_rhs_tendsto
    intro n
    exact h_per_n n
  have h_one_div_density : ContDiffOn ℝ ∞
      (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
      (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')
  have h_rhs_integral :
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      μ⁻¹ * (U - CL + CRV - PRC - LOV + GD - CRGdiv) := by
    have hint_U : _root_.MeasureTheory.Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (Lp.memLp (tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀))
        hψ hψ_cs hψ_support
    have hint_CLsum : _root_.MeasureTheory.Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P' : TensorCompIdx (E := E) r (s + 1),
          ∑ Q : TensorCompIdx (E := E) r (s + 1),
            covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      have h_sum : _root_.MeasureTheory.Integrable (fun y => ∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossLeftLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        MeasureTheory.integrable_finsetSum _ (fun P' _ =>
          MeasureTheory.integrable_finsetSum _ (fun Q _ =>
            crossLeftLimitPairing_integrable (I := I) (M := M) g r s i
              α P₀ P' Q hψ hψ_cs hψ_support))
      refine h_sum.congr (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hint_CRVsum : _root_.MeasureTheory.Integrable (fun y => densityOnEuclid (I := I) g α y *
        (∑ P' : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
        ψ y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
      have h_sum : _root_.MeasureTheory.Integrable (fun y => ∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          densityOnEuclid (I := I) g α y *
            (covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P' :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) *
            ψ y)
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
        MeasureTheory.integrable_finsetSum _ (fun P' _ =>
          MeasureTheory.integrable_finsetSum _ (fun Q _ =>
            crossRightValueLimitPairing_integrable (I := I) (M := M)
              g r s i α P₀ P' Q hψ hψ_cs hψ_support))
      refine h_sum.congr (Filter.Eventually.of_forall (fun y => ?_))
      simp only [Finset.mul_sum, Finset.sum_mul]
    have hint_PRC : _root_.MeasureTheory.Integrable (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s i α P₀ y * ψ y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
          g r s i α P₀)
        hψ hψ_cs hψ_support
    have hint_LOV : _root_.MeasureTheory.Integrable (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
          g r s i α P₀ y * ψ y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_memLp2_test_integrable (I := I) (M := M) g α
        (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
          g r s i α P₀)
        hψ hψ_cs hψ_support
    have hint_GD : _root_.MeasureTheory.Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          ∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) * ψ y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_coeff_memLp2_test_integrable (I := I) (M := M) g α
        h_one_div_density
        (_root_.MeasureTheory.memLp_finsetSum (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l _ => weightedGradCoeffDivLimit_memLp (I := I) (M := M)
            g r s i α P₀ l))
        hψ hψ_cs hψ_support
    have hint_CRGD : _root_.MeasureTheory.Integrable (fun y => densityOnEuclid (I := I) g α y *
        ((1 / densityOnEuclid (I := I) g α y) *
          crossRightGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ y) * ψ y)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      density_coeff_memLp2_test_integrable (I := I) (M := M) g α
        h_one_div_density
        (crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
          g r s i α P₀)
        hψ hψ_cs hψ_support
    have h_integrand : Set.EqOn
        (fun y => densityOnEuclid (I := I) g α y *
          eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ y * ψ y)
        (fun y => μ⁻¹ *
          ((densityOnEuclid (I := I) g α y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
                Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                EuclN → ℝ) y * ψ y) -
            densityOnEuclid (I := I) g α y *
              (∑ P' : TensorCompIdx (E := E) r (s + 1),
                ∑ Q : TensorCompIdx (E := E) r (s + 1),
                  covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
                      crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
                    ((crossLeftLimitComponent (I := I) (M := M)
                      g r s i α P' :
                      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) * ψ y +
            densityOnEuclid (I := I) g α y *
              (∑ P' : TensorCompIdx (E := E) r s,
                ∑ Q : TensorCompIdx (E := E) r s,
                  covChartMetricGram (I := I) (M := M) g r s α P' Q y *
                      crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
                    ((crossRightLimitComponent (I := I) (M := M)
                      g r s i α P' :
                      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) :
                      EuclN → ℝ) y) * ψ y -
            densityOnEuclid (I := I) g α y *
              covPrincipalRotationCoeffLimit (I := I) (M := M)
                g r s i α P₀ y * ψ y -
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
                g r s i α P₀ y * ψ y +
            densityOnEuclid (I := I) g α y *
              ((1 / densityOnEuclid (I := I) g α y) *
                ∑ l : Fin (Module.finrank ℝ E),
                  weightedGradCoeffDivLimit (I := I) (M := M)
                    g r s i α P₀ l y) * ψ y -
            densityOnEuclid (I := I) g α y *
              ((1 / densityOnEuclid (I := I) g α y) *
                crossRightGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ y) * ψ y))
        (chartTargetEuclid (I := I) (M := M) α) := by
      intro y _hy
      simp only [eigenvectorChartRHS, eigenvectorChartRHSNumerator,
        eigenvectorChartComponentFun, eigenvectorChartCrossLeftContraction,
        eigenvectorChartCrossRightContraction, eigenvectorChartWeightedDivergence,
        eigenvectorChartCrossRightDivergence, Pi.add_apply, Pi.sub_apply, hφ_def]
      ring
    rw [MeasureTheory.setIntegral_congr_fun hcTE_meas h_integrand]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have hψ_zero : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α → ψ y = 0 :=
      fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_support h))
    have hD4 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeffLimit (I := I) (M := M)
              g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) = PRC := by
      rw [hPRC_def]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hψ_zero y hy, _root_.MulZeroClass.mul_zero])
    have hD5 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
              g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) = LOV := by
      rw [hLOV_def]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hψ_zero y hy, _root_.MulZeroClass.mul_zero])
    have hD6 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) = GD := by
      rw [hGD_def]
      rw [show (∫ y, (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)
        from (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [hψ_zero y hy, _root_.MulZeroClass.mul_zero])).symm]
      refine MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => ?_)
      rw [show densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              ∑ l : Fin (Module.finrank ℝ E),
                weightedGradCoeffDivLimit (I := I) (M := M)
                  g r s i α P₀ l y) * ψ y =
          (densityOnEuclid (I := I) g α y *
              (1 / densityOnEuclid (I := I) g α y)) *
            ((∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) * ψ y) from by ring]
      rw [mul_one_div, div_self (densityOnEuclid_pos (I := I) g α hy).ne',
        one_mul]
    have hD7 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ y) * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) = CRGdiv := by
      rw [hCRGdiv_def]
      refine MeasureTheory.setIntegral_congr_fun hcTE_meas (fun y hy => ?_)
      rw [show densityOnEuclid (I := I) g α y *
            ((1 / densityOnEuclid (I := I) g α y) *
              crossRightGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ y) * ψ y =
          (densityOnEuclid (I := I) g α y *
              (1 / densityOnEuclid (I := I) g α y)) *
            (crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ y * ψ y) from by ring]
      rw [mul_one_div, div_self (densityOnEuclid_pos (I := I) g α hy).ne',
        one_mul]
    set fU : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      ((tensorL2ChartComponent (I := I) (M := M) g r s φ α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y * ψ y
      with hfU_def
    set fCL : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          covChartMetricGram (I := I) (M := M) g r (s + 1) α P' Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) * ψ y
      with hfCL_def
    set fCRV : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      (∑ P' : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          covChartMetricGram (I := I) (M := M) g r s α P' Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P' :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) * ψ y
      with hfCRV_def
    set fPRC : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y with hfPRC_def
    set fLOV : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ y * ψ y with hfLOV_def
    set fGD : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      ((1 / densityOnEuclid (I := I) g α y) *
        ∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) * ψ y with hfGD_def
    set fCRGD : EuclN → ℝ := fun y => densityOnEuclid (I := I) g α y *
      ((1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y) * ψ y with hfCRGD_def
    have e1 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y + fGD y - fCRGD y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y + fGD y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fCRGD y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      MeasureTheory.integral_sub
        (((((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC).sub
          hint_LOV).add hint_GD) hint_CRGD
    have e2 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y + fGD y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fGD y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      MeasureTheory.integral_add
        ((((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC).sub hint_LOV)
        hint_GD
    have e3 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y - fLOV y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fLOV y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      MeasureTheory.integral_sub
        (((hint_U.sub hint_CLsum).add hint_CRVsum).sub hint_PRC) hint_LOV
    have e4 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y - fPRC y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fPRC y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      MeasureTheory.integral_sub
        ((hint_U.sub hint_CLsum).add hint_CRVsum) hint_PRC
    have e5 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y + fCRV y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fCRV y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      MeasureTheory.integral_add (hint_U.sub hint_CLsum) hint_CRVsum
    have e6 : (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fU y - fCL y)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α, fU y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) -
        ∫ y in chartTargetEuclid (I := I) (M := M) α, fCL y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
      MeasureTheory.integral_sub hint_U hint_CLsum
    rw [e1, e2, e3, e4, e5, e6, ← hU_def, ← hCL_def, ← hCRV_def,
      hD4, hD5, hD6, hD7]
  rw [hP_def, hU_def, h_rhs_integral, ← hU_def]
  rw [show U - CL + CRV - PRC - LOV + GD - CRGdiv =
      L + μ * U from by rw [hL_def]; ring]
  rw [← h_mu_P]
  rw [show μ⁻¹ * (μ * P + μ * U) = P + U from by
    rw [mul_add, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul,
      one_mul]]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartVariationalIdentity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartVariationalIdentity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartVariationalIdentity ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartVariationalIdentity

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
def eigenvectorTensorChartBilinearData
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀ :=
  ⟨{ uChart := fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y
     fChart := eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
     weakPartial := eigenvectorChartWeakPartial (I := I) (M := M)
       g r s i α P₀
     u_chart_memLp_weighted :=
       tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
         (tensorResolventEigenbasisVec (I := I) (M := M)
           (tensorResolventL2_isCompactOperator (I := I) (M := M)
             g r s) i) α P₀
     f_chart_memLp_weighted :=
       eigenvectorChartRHS_memLp_weighted (I := I) (M := M)
         g r s i α P₀
     weak_partial_locally_memLp := fun k _K hK hK_in =>
       eigenvectorChartWeakPartial_locally_memLp (I := I) (M := M)
         g r s i α P₀ k hK hK_in
     weak_partial_isWeakPartial := fun k =>
       eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
         g r s i α P₀ k
     variational_identity := fun _ψ hψ hψ_cs hψ_support =>
       eigenvectorChartVariationalIdentity (I := I) (M := M)
         g r s i α P₀ hψ hψ_cs hψ_support }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorTensorChartBilinearData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorTensorChartBilinearData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorTensorChartBilinearData ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorTensorChartBilinearData

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
