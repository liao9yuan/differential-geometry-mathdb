import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.L2Approximation
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.WeightedIntegrability
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.ChartTestDecoupling
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightDivergence

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
  RealInnerProductSpace InnerProductSpace

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
def eigenvectorChartComponentFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartComponentFun

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
def eigenvectorChartCrossLeftContraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
    ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossLeftContraction

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
def eigenvectorChartCrossRightContraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y => ∑ P : TensorCompIdx (E := E) r s,
    ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightContraction

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
def eigenvectorChartWeightedDivergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    ∑ l : Fin (Module.finrank ℝ E),
      weightedGradCoeffDivLimit (I := I) (M := M) g r s i α P₀ l y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartWeightedDivergence

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
def eigenvectorChartCrossRightDivergence
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y => (1 / densityOnEuclid (I := I) g α y) *
    crossRightGradCoeffDivLimit (I := I) (M := M) g r s i α P₀ y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartCrossRightDivergence

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
def eigenvectorChartRHSNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ -
    eigenvectorChartCrossLeftContraction (I := I) (M := M) g r s i α P₀ +
    eigenvectorChartCrossRightContraction (I := I) (M := M) g r s i α P₀ -
    covPrincipalRotationCoeffLimit (I := I) (M := M) g r s i α P₀ -
    covLowerOrderRotationValueCoeffLimit (I := I) (M := M) g r s i α P₀ +
    eigenvectorChartWeightedDivergence (I := I) (M := M) g r s i α P₀ -
    eigenvectorChartCrossRightDivergence (I := I) (M := M) g r s i α P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSNumerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSNumerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSNumerator ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHSNumerator

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
noncomputable def eigenvectorChartRHS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y => (i.fst.val)⁻¹ *
    eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀ y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
lemma eigenvectorChartRHS_eq_eigenvalue_inv_smul_numerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ =
      (i.fst.val)⁻¹ •
        eigenvectorChartRHSNumerator (I := I) (M := M) g r s i α P₀ := by
  funext y
  simp only [eigenvectorChartRHS, Pi.smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eq_eigenvalue_inv_smul_numerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eq_eigenvalue_inv_smul_numerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eq_eigenvalue_inv_smul_numerator ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_eq_eigenvalue_inv_smul_numerator

omit [CompleteSpace E] in
lemma crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ y = 0 := by
  classical
  rw [crossRightGradCoeffDivLimit,
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, _root_.MulZeroClass.zero_mul]))),
    Finset.sum_eq_zero (fun l _ => Finset.sum_eq_zero (fun P _ =>
      Finset.sum_eq_zero (fun Q _ => by
        rw [Set.indicator_of_notMem hy, _root_.MulZeroClass.zero_mul]))),
    add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel

omit [CompleteSpace E] in
private lemma crossRightGradCoeffDivLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : _root_.MeasureTheory.MemLp (crossRightGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    crossRightGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memLp_weighted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightGradCoeffDivLimit_memLp_weighted target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
theorem eigenvectorChartRHS_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have h_uchart : _root_.MeasureTheory.MemLp
      (fun y =>
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α P₀ :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    rw [hμw_def]
    exact tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) α P₀
  have h_crossLeft : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      _root_.MeasureTheory.MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossLeftLimitComponent_memLp_weighted (I := I) (M := M)
        g r s i α P)
      h_aezero
  have h_crossRight : ∀ (P Q : TensorCompIdx (E := E) r s),
      _root_.MeasureTheory.MemLp
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2 μw := by
    intro P Q
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      ((covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q))
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightLimitComponent_memLp_weighted (I := I) (M := M)
        g r s i α P)
      h_aezero
  have h_prc : _root_.MeasureTheory.MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
      g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covPrincipalRotationCoeffLimit_memLp_weighted
      (I := I) (M := M) g r s i α P₀
  have h_lov : _root_.MeasureTheory.MemLp (covLowerOrderRotationValueCoeffLimit
      (I := I) (M := M) g r s i α P₀) 2 μw := by
    rw [hμw_def]
    exact covLowerOrderRotationValueCoeffLimit_memLp_weighted
      (I := I) (M := M) g r s i α P₀
  have h_gradDiv : _root_.MeasureTheory.MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y)) 2 μw := by
    rw [hμw_def]
    have h_div_sum : _root_.MeasureTheory.MemLp
        (fun y => ∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      memLp_finsetSum (μ := (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l _ => weightedGradCoeffDivLimit_memLp_weighted
          (I := I) (M := M) g r s i α P₀ l)
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            (∑ l : Fin (Module.finrank ℝ E),
              weightedGradCoeffDivLimit (I := I) (M := M)
                g r s i α P₀ l y) = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        Finset.sum_eq_zero (fun l _ =>
          weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s i α P₀ l hy))
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      h_div_sum h_aezero
  have h_crossRightDiv : _root_.MeasureTheory.MemLp
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y) 2 μw := by
    rw [hμw_def]
    have h_aezero :
        ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α →
            crossRightGradCoeffDivLimit (I := I) (M := M)
              g r s i α P₀ y = 0 :=
      Filter.Eventually.of_forall (fun y hy =>
        crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ hy)
    exact memLp_weighted_contDiffOn_mul (I := I) (M := M) g α
      (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (crossRightGradCoeffDivLimit_memLp_weighted (I := I) (M := M)
        g r s i α P₀)
      h_aezero
  have h_crossLeft_sum : _root_.MeasureTheory.MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finsetSum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
        (fun Q _ => h_crossLeft P Q))
  have h_crossRight_sum : _root_.MeasureTheory.MemLp
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      2 μw :=
    memLp_finsetSum (μ := μw)
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P _ => _root_.MeasureTheory.memLp_finsetSum (μ := μw)
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q _ => h_crossRight P Q))
  have h_total :
      MemLp (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀) 2
        μw := by
    have h_bracket :=
      ((((((h_uchart.sub h_crossLeft_sum).add h_crossRight_sum).sub h_prc).sub
        h_lov).add h_gradDiv).sub h_crossRightDiv)
    have h_assembled := h_bracket.const_mul (i.fst.val)⁻¹
    refine h_assembled.ae_eq ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    simp only [eigenvectorChartRHS, eigenvectorChartRHSNumerator,
      eigenvectorChartComponentFun, eigenvectorChartCrossLeftContraction,
      eigenvectorChartCrossRightContraction, eigenvectorChartWeightedDivergence,
      eigenvectorChartCrossRightDivergence, Pi.add_apply, Pi.sub_apply]
  rw [hμw_def] at h_total
  exact h_total

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorChartRHS_memLp_weighted

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
