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

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeff_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
      _root_.Filter.atTop
      (𝓝 (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
  classical
  set μch : _root_.MeasureTheory.Measure EuclN := chartLebesgueMeasure (I := I) (M := M) α with hμch_def
  set m : _root_.MeasureTheory.Lp ℝ 2 μch :=
    (densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp _
    with hm_def
  set glim : _root_.MeasureTheory.Lp ℝ 2 μch :=
    (covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀).toLp _ with hglim_def
  set gseq : ℕ → _root_.MeasureTheory.Lp ℝ 2 μch := fun n =>
    (covPrincipalRotationCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ n).toLp _ with hgseq_def
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    intro n
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ) =ᵐ[μch]
        covPrincipalRotationCoeff (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
          α P₀ := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [_root_.MeasureTheory.integral_congr_ae h_ae_prod, hμch_def, chartLebesgueMeasure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_support h)), _root_.MulZeroClass.mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ) =ᵐ[μch]
        covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [_root_.MeasureTheory.integral_congr_ae h_ae_prod, hμch_def, chartLebesgueMeasure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_support h)), _root_.MulZeroClass.mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq _root_.Filter.atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact covPrincipalRotationCoeff_tendsto (I := I) (M := M)
      g r s i α P₀
  have h_main := tendsto_lp_inner_integral (μ := μch) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_source_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_source_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_source_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeff_source_tendsto

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeff_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
      _root_.Filter.atTop
      (𝓝 (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
  classical
  set μch : _root_.MeasureTheory.Measure EuclN := chartLebesgueMeasure (I := I) (M := M) α with hμch_def
  set m : _root_.MeasureTheory.Lp ℝ 2 μch :=
    (densityOnEuclid_mul_test_memLp (I := I) (M := M) g α hψ hψ_cs hψ_support).toLp _
    with hm_def
  set glim : _root_.MeasureTheory.Lp ℝ 2 μch :=
    (covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀).toLp _ with hglim_def
  set gseq : ℕ → _root_.MeasureTheory.Lp ℝ 2 μch := fun n =>
    (covLowerOrderRotationValueCoeff_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ n).toLp _ with hgseq_def
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    intro n
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (gseq n : EuclN → ℝ) =ᵐ[μch]
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
          (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
          α P₀ := by
      rw [hgseq_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [_root_.MeasureTheory.integral_congr_ae h_ae_prod, hμch_def, chartLebesgueMeasure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_support h)), _root_.MulZeroClass.mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y ∂μch =
        ∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have h_m_ae : (m : EuclN → ℝ) =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y * ψ y := by
      rw [hm_def]; exact MemLp.coeFn_toLp _
    have h_g_ae : (glim : EuclN → ℝ) =ᵐ[μch]
        covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
          g r s i α P₀ := by
      rw [hglim_def]; exact MemLp.coeFn_toLp _
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[μch]
        fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s i α P₀ y * ψ y := by
      filter_upwards [h_m_ae, h_g_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [_root_.MeasureTheory.integral_congr_ae h_ae_prod, hμch_def, chartLebesgueMeasure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_support h)), _root_.MulZeroClass.mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq _root_.Filter.atTop (𝓝 glim) := by
    rw [hgseq_def, hglim_def]
    exact covLowerOrderRotationValueCoeff_tendsto (I := I) (M := M)
      g r s i α P₀
  have h_main := tendsto_lp_inner_integral (μ := μch) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_source_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_source_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_source_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeff_source_tendsto

omit [CompleteSpace E] in
theorem weightedGradCoeffDivSum_source_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_support : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Filter.Tendsto
      (fun n => ∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
              α P₀ l) y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))
      _root_.Filter.atTop
      (𝓝 (∫ y, (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN))) := by
  classical
  set m : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    (test_memLp (I := I) (M := M) α hψ hψ_cs).toLp _ with hm_def
  set gseq : ℕ → _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) := fun n =>
    ∑ l : Fin (Module.finrank ℝ E),
      (euclidPartial_weightedGradCoeff_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ l n).toLp _ with hgseq_def
  set glim : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    ∑ l : Fin (Module.finrank ℝ E),
      (weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l).toLp _ with hglim_def
  have h_m_ae : (m : EuclN → ℝ) =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] ψ := by
    rw [hm_def]; exact MemLp.coeFn_toLp _
  have h_gseq_ae : ∀ n : ℕ, (gseq n : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s
            (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
            α P₀ l) y := fun n => by
    rw [hgseq_def]
    exact coeFn_finsetSum_toLp (I := I) (M := M) α
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => euclidPartial_weightedGradCoeff_pouSmul_memLp
        (I := I) (M := M) g r s i α P₀ l n)
  have h_glim_ae : (glim : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y := by
    rw [hglim_def]
    exact coeFn_finsetSum_toLp (I := I) (M := M) α
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l => weightedGradCoeffDivLimit_memLp (I := I) (M := M)
        g r s i α P₀ l)
  have h_int_n : ∀ n : ℕ,
      ∫ y, (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α) =
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) l
              (weightedGradCoeff (I := I) (M := M) g r s
                (eigenvectorPouApprox (I := I) (M := M)
                  g r s i α n)
                α P₀ l) y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    intro n
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (gseq n : EuclN → ℝ) y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s
              (eigenvectorPouApprox (I := I) (M := M) g r s i α n)
              α P₀ l) y) * ψ y := by
      filter_upwards [h_m_ae, h_gseq_ae n] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [_root_.MeasureTheory.integral_congr_ae h_ae_prod, chartLebesgueMeasure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_support h)), _root_.MulZeroClass.mul_zero]
  have h_int_lim :
      ∫ y, (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y
          ∂(chartLebesgueMeasure (I := I) (M := M) α) =
        ∫ y, (∑ l : Fin (Module.finrank ℝ E),
            weightedGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ l y) * ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    have h_ae_prod : (fun y => (m : EuclN → ℝ) y * (glim : EuclN → ℝ) y)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) * ψ y := by
      filter_upwards [h_m_ae, h_glim_ae] with y hy_m hy_g
      rw [hy_m, hy_g]; ring
    rw [_root_.MeasureTheory.integral_congr_ae h_ae_prod, chartLebesgueMeasure]
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ_support h)), _root_.MulZeroClass.mul_zero]
  have h_tendsto_lp : Filter.Tendsto gseq _root_.Filter.atTop (𝓝 glim) :=
    weightedGradCoeffDivSum_tendsto (I := I) (M := M)
      g r s i α P₀
  have h_main := tendsto_lp_inner_integral
    (μ := chartLebesgueMeasure (I := I) (M := M) α) m h_tendsto_lp
  rw [h_int_lim] at h_main
  exact h_main.congr (fun n => h_int_n n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_source_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_source_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_source_tendsto ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivSum_source_tendsto

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
