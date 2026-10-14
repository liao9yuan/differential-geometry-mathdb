import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Differentiated.Sobolev.Bounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.IteratedRegularity.SecondOrderSobolevBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.IteratedRegularity.CarrierExistence
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RightHandSide.Chart.Regularity
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.WeightedIntegrability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ c : ℝ, 0 ≤ c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartPouKernel (I := I) (M := M) α) ≤
        ENNReal.ofReal c •
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartPouKernel (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, le_of_lt (lt_of_lt_of_le hc_min_pos hc_le), ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [_root_.MeasureTheory.withDensity_apply _ (hA.inter hK_meas)]
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    refine MeasureTheory.setLIntegral_mono_ae' (hA.inter hK_meas) ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact ENNReal.ofReal_le_ofReal (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ENNReal.ofReal c_max * (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) (A ∩ K) :=
    MeasureTheory.setLIntegral_const _ _
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (α : M) {f : EuclN → ℝ}
    (hf : f =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      _root_.MeasureTheory.eLpNorm f 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          _root_.MeasureTheory.eLpNorm f 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ Ω := chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_meas : MeasurableSet (Ω \ K) := hΩ_open.measurableSet.diff hK_meas
  have hf' : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω),
      y ∉ K → f y = 0 := by
    rw [Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_iff' hV_meas] at hf
    rw [_root_.MeasureTheory.ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
  obtain ⟨c, hc_nn, hc_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
      (I := I) (M := M) g α
  refine ⟨Real.sqrt c, Real.sqrt_nonneg _, ?_⟩
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (_root_.MeasureTheory.withDensity_absolutelyContinuous (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) _).restrict Ω
  have hf_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → f y = 0 := h_abs.ae_le hf'
  have h_ind_w : f =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator f := by
    filter_upwards [hf_w] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  have h_ind_v : f =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω] K.indicator f := by
    filter_upwards [hf'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  rw [_root_.MeasureTheory.eLpNorm_congr_ae h_ind_w, _root_.MeasureTheory.eLpNorm_congr_ae h_ind_v,
    _root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    _root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hK_meas]
  rw [Measure.restrict_restrict_of_subset hK_in,
    Measure.restrict_restrict_of_subset hK_in]
  have h_mono :
      eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ _root_.MeasureTheory.eLpNorm f 2
            (ENNReal.ofReal c • ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)) :=
    _root_.MeasureTheory.eLpNorm_mono_measure f hc_le
  refine h_mono.trans ?_
  rw [_root_.MeasureTheory.eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  have h_pow_eq : ENNReal.ofReal c ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hc_nn (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
    {ι : Type*} (g : SmoothRiemannianMetric I M) (α : M) {f : ι → EuclN → ℝ}
    (hf : ∀ i, f i =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : ι,
        _root_.MeasureTheory.eLpNorm (f i) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            _root_.MeasureTheory.eLpNorm (f i) 2
              ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ Ω := chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_meas : MeasurableSet (Ω \ K) := hΩ_open.measurableSet.diff hK_meas
  obtain ⟨c, hc_nn, hc_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_on_chartPouKernel
      (I := I) (M := M) g α
  refine ⟨Real.sqrt c, Real.sqrt_nonneg _, fun i => ?_⟩
  have hf' : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω),
      y ∉ K → f i y = 0 := by
    have hf_i := hf i
    rw [Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_iff' hV_meas] at hf_i
    rw [_root_.MeasureTheory.ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf_i] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (_root_.MeasureTheory.withDensity_absolutelyContinuous (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) _).restrict Ω
  have hf_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → f i y = 0 := h_abs.ae_le hf'
  have h_ind_w : f i =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator (f i) := by
    filter_upwards [hf_w] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  have h_ind_v : f i =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω] K.indicator (f i) := by
    filter_upwards [hf'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  rw [_root_.MeasureTheory.eLpNorm_congr_ae h_ind_w, _root_.MeasureTheory.eLpNorm_congr_ae h_ind_v,
    _root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    _root_.MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hK_meas]
  rw [Measure.restrict_restrict_of_subset hK_in,
    Measure.restrict_restrict_of_subset hK_in]
  have h_mono :
      eLpNorm (f i) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ _root_.MeasureTheory.eLpNorm (f i) 2
            (ENNReal.ofReal c • ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)) :=
    _root_.MeasureTheory.eLpNorm_mono_measure (f i) hc_le
  refine h_mono.trans ?_
  rw [_root_.MeasureTheory.eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  have h_pow_eq : ENNReal.ofReal c ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hc_nn (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform target :: scope.openDecls } }

section MainBound

omit [CompleteSpace E] in
theorem eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (D_m : EigenvectorIteratedTensorChartBilinearData (I := I) (M := M)
      g r s i α P₀ m)
    (h_fChartEffective : D_m.diffChartForcing =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m directions)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      _root_.MeasureTheory.eLpNorm
          ((EigenvectorIteratedTensorChartBilinearData.toTensorChartBilinearH1ComplData
              (I := I) (M := M) g r s i α P₀ D_m h_parent).fChart)
          2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
  classical
  have h_f_chart_eq :
      (EigenvectorIteratedTensorChartBilinearData.toTensorChartBilinearH1ComplData
          (I := I) (M := M) g r s i α P₀ D_m h_parent).fChart =
        eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m directions := by
    change D_m.diffChartForcing =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m directions
    exact h_fChartEffective
  rw [h_f_chart_eq]
  have h_ae_zero :
      eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m directions
        =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s i α P₀ m directions
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel
      (I := I) (M := M) g α h_ae_zero
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le (I := I) (M := M)
      g r s i α P₀ m directions h_pou
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  calc
    eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m directions) 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) hCvol_bd
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le

omit [CompleteSpace E] in
theorem eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 0) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (D_m : EigenvectorIteratedTensorChartBilinearData
          (I := I) (M := M) g r s i α P₀ m)
        (_h_fChartEffective : D_m.diffChartForcing =
          eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions)
        (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)),
        _root_.MeasureTheory.eLpNorm
            ((EigenvectorIteratedTensorChartBilinearData.toTensorChartBilinearH1ComplData
                (I := I) (M := M) g r s i α P₀ D_m h_parent).fChart)
            2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * C) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m 0 directions := by
  classical
  have h_ae_zero :
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions
          =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) :=
    fun i => rhsDiff_ae_zero_off_chartPouKernel (I := I) (M := M)
      g r s i α P₀ m directions
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_chartPouKernel_uniform
      (I := I) (M := M)
      (ι := TensorEigenIdx (I := I) (M := M) g r s) g α h_ae_zero
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    eigenvectorChartRHSDiff_eLpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ m directions h_pou
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, ?_⟩
  intro i D_m h_fChartEffective h_parent
  have h_f_chart_eq :
      (EigenvectorIteratedTensorChartBilinearData.toTensorChartBilinearH1ComplData
          (I := I) (M := M) g r s i α P₀ D_m h_parent).fChart =
        eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ m directions := by
    change D_m.diffChartForcing =
      eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m directions
    exact h_fChartEffective
  rw [h_f_chart_eq]
  calc
    eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m directions) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Ccmp *
          eLpNorm (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m directions) 2
            ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hCcmp_bd i
    _ ≤ ENNReal.ofReal Ccmp *
          (ENNReal.ofReal ((i.fst.val)⁻¹ * Cvol) *
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m 0 directions) :=
          mul_le_mul' (le_refl _) (hCvol_bd i)
    _ = ENNReal.ofReal ((i.fst.val)⁻¹ * (Ccmp * Cvol)) *
          diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ m 0 directions := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn]
          congr 2
          ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le_uniform ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorIteratedCarrier_fChartEffective_eLpNorm_le_uniform

end MainBound

omit [CompleteSpace E] in
private lemma diffRHSHead_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    diffRHSHead (I := I) (M := M) g r s i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  have h_iter : ∀ (N j : ℕ) (idx : Fin j → Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) N 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro N j idx
    have h_comp : MemWkp (d := Module.finrank ℝ E) (N + j) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
      eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
        g r s i (N + j) α P₀
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s i α P₀ j N h_comp idx
  rw [diffRHSHead]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun a _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (h_iter (2 + K) (m + 1) (Fin.cons a (Fin.init l)))
  · exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (h_iter (2 + K) m (Fin.init l)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diffRHSHead_ne_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diffRHSHead_ne_top target :: scope.openDecls } }

omit [CompleteSpace E] in
private lemma rhsZeroAggregate_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  rw [rhsZeroAggregate]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ne_of_lt (wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
        g r s i K α P₀))
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr (fun Q _ => ?_),
        ENNReal.sum_lt_top.mpr (fun β' _ =>
          ENNReal.sum_lt_top.mpr (fun Q _ => ?_))⟩))
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β Q)
    · exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (h_pou β' Q)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun β _ =>
      ENNReal.sum_lt_top.mpr (fun Q _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (MemWkp.le_of_le (d := Module.finrank ℝ E)
        (by omega : K ≤ K + 1) (h_pou β Q))
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun k _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (partialLpLimit_memWkp (I := I) (M := M)
        g r s i α P k K h_pou)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (componentLpLimit_memWkp (I := I) (M := M)
        g r s i α p K h_pou)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ => ?_))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s i α P K h_pou)
  · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun P _ =>
      ENNReal.sum_lt_top.mpr (fun l _ => ?_)))
    exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E)
      (cutoffPartialLpLimit_memWkp (I := I) (M := M)
        g r s i α P l K h_pou)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rhsZeroAggregate_ne_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.rhsZeroAggregate_ne_top target :: scope.openDecls } }

omit [CompleteSpace E] in
theorem diffRHSAggregate_ne_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    diffRHSAggregate (I := I) (M := M) g r s i α P₀ m K l
      ≠ (⊤ : ℝ≥0∞) := by
  classical
  induction m generalizing K with
  | zero =>
      rw [show diffRHSAggregate (I := I) (M := M)
          g r s i α P₀ 0 K l =
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K from rfl]
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M)
                    g r s i))
                β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      exact rhsZeroAggregate_ne_top (I := I) (M := M)
        g r s i α P₀ K h_pou'
  | succ m ih =>
      rw [show diffRHSAggregate (I := I) (M := M)
            g r s i α P₀ (m + 1) K l =
          diffRHSHead (I := I) (M := M) g r s i α P₀ m K l +
            diffRHSAggregate (I := I) (M := M)
              g r s i α P₀ m (K + 1) (Fin.init l) from rfl]
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · exact diffRHSHead_ne_top (I := I) (M := M)
          g r s i α P₀ m K l
      · have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
            MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M)
                      g r s i))
                  β Q : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β) := by
          intro β Q
          have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
          rw [h_idx]
          exact h_pou β Q
        exact ih (K + 1) (Fin.init l) h_pou_prev

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diffRHSAggregate_ne_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diffRHSAggregate_ne_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diffRHSAggregate_ne_top ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diffRHSAggregate_ne_top

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
