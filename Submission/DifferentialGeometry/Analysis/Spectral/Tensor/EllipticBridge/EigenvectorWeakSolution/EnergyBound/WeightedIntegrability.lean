import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.RightLimit
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.LowerOrder.CoefficientLimits
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.TensorChartBilinearData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma ae_eq_zero_off_of_tendsto_Lp
    {μ : _root_.MeasureTheory.Measure EuclN} {K : Set EuclN} {F : ℕ → _root_.MeasureTheory.Lp ℝ 2 μ} {glim : _root_.MeasureTheory.Lp ℝ 2 μ}
    (hF : ∀ n, ∀ᵐ y ∂μ, y ∉ K → (F n : EuclN → ℝ) y = 0)
    (h_tendsto : Filter.Tendsto F _root_.Filter.atTop (𝓝 glim)) :
    ∀ᵐ y ∂μ, y ∉ K → (glim : EuclN → ℝ) y = 0 := by
  classical
  have h_inMeasure : _root_.MeasureTheory.TendstoInMeasure μ (fun n => (F n : EuclN → ℝ)) _root_.Filter.atTop
      (glim : EuclN → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp (p := 2) h_tendsto
  obtain ⟨ns, _hns_mono, h_ae⟩ := h_inMeasure.exists_seq_tendsto_ae
  have hF_sub : ∀ᵐ y ∂μ, ∀ i : ℕ, y ∉ K → (F (ns i) : EuclN → ℝ) y = 0 :=
    ae_all_iff.mpr (fun i => hF (ns i))
  filter_upwards [h_ae, hF_sub] with y h_lim h_zero hy
  have h_const : Filter.Tendsto (fun i => (F (ns i) : EuclN → ℝ) y) _root_.Filter.atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun i => (h_zero i hy).symm) tendsto_const_nhds
  exact tendsto_nhds_unique h_lim h_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_zero_off_of_tendsto_Lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_zero_off_of_tendsto_Lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_zero_off_of_tendsto_Lp ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ae_eq_zero_off_of_tendsto_Lp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartPulledWeightedMeasure_restrict_le_volume_of_compact
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        ENNReal.ofReal c • ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, lt_of_lt_of_le hc_min_pos hc_le, ?_⟩
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
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_le_volume_of_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_le_volume_of_compact target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (g : SmoothRiemannianMetric I M) (α : M) {w : EuclN → ℝ}
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hwK : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0)
    (hw : _root_.MeasureTheory.MemLp w 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))) :
    MemLp w 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (_root_.MeasureTheory.withDensity_absolutelyContinuous (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) _).restrict Ω
  have hwK' : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → w y = 0 :=
    h_abs.ae_le hwK
  have h_ind : w =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator w := by
    filter_upwards [hwK'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  refine MemLp.ae_eq h_ind.symm ?_
  rw [_root_.MeasureTheory.memLp_indicator_iff_restrict hK_meas]
  rw [Measure.restrict_restrict hK_meas, Set.inter_eq_self_of_subset_left hK_in]
  obtain ⟨c, _hc_pos, h_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_of_compact (I := I) (M := M)
      α hK_compact hK_meas hK_in
  have hw_K : _root_.MeasureTheory.MemLp w 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
    refine hw.mono_measure ?_
    rw [hΩ_def]
    exact Measure.restrict_mono hK_in le_rfl
  exact hw_K.of_measure_le_smul (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top h_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 := by
  classical
  have h_dense : DenseRange
      (fun S : SmoothCcTensor g r s => (S : TensorL2 r s g)) := by
    have h := UniformSpace.Completion.denseRange_coe
      (α := SmoothCcTensor g r s)
    exact h
  have h_mem : u ∈ closure (Set.range
      (fun S : SmoothCcTensor g r s => (S : TensorL2 r s g))) := h_dense u
  obtain ⟨x, hx_range, hx_tendsto⟩ :=
    mem_closure_iff_seq_limit.mp h_mem
  choose S hS using hx_range
  have h_comp_tendsto : Filter.Tendsto
      (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
        ((S n : TensorL2 r s g)) α P₀)
      _root_.Filter.atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀)) := by
    have h_clm := ((continuous_tensorL2ChartComponent (I := I) (M := M)
      g r s α P₀).tendsto u).comp hx_tendsto
    refine Filter.Tendsto.congr (fun n => ?_) h_clm
    simp only [Function.comp_apply, hS n]
  have h_term : ∀ n : ℕ,
      ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α →
          (tensorL2ChartComponent (I := I) (M := M) g r s
            ((S n : TensorL2 r s g)) α P₀ : EuclN → ℝ) y = 0 := by
    intro n
    have h_ae := tensorL2ChartComponent_smoothToTensorL2_coeFn
      (I := I) (M := M) g r s (S n) α P₀
    filter_upwards [h_ae] with y hy hyK
    rw [hy]
    exact tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s (S n) α P₀.1 P₀.2 hyK
  exact ae_eq_zero_off_of_tendsto_Lp h_term h_comp_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponent_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : _root_.MeasureTheory.MemLp (fun y => (tensorL2ChartComponent (I := I) (M := M)
      g r s u α P₀ : EuclN → ℝ) y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    Lp.memLp (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀)
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (tensorL2ChartComponent_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s u α P₀)
    h_plain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_memLp_weighted

def cutoffChartKernelEuclid (α : M) : Set EuclN :=
  toEuclidean '' (cutoffChartKernel (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffChartKernelEuclid_isCompact (α : M) :
    IsCompact (cutoffChartKernelEuclid (I := I) (M := M) α) :=
  (cutoffChartKernel_isCompact (I := I) (M := M) α).image
    (toEuclidean (E := E)).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_isCompact ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_isCompact

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffChartKernelEuclid_measurableSet (α : M) :
    MeasurableSet (cutoffChartKernelEuclid (I := I) (M := M) α) :=
  (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α).isClosed.measurableSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_measurableSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_measurableSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_measurableSet ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_measurableSet

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma cutoffChartKernelEuclid_subset_chartTargetEuclid (α : M) :
    cutoffChartKernelEuclid (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold cutoffChartKernelEuclid chartTargetEuclid
  exact Set.image_mono (cutoffChartKernel_subset_target (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_subset_chartTargetEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_subset_chartTargetEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_subset_chartTargetEuclid ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffChartKernelEuclid_subset_chartTargetEuclid

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma cutoffComponentEuclid_eq_zero_off_cutoffChartKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ cutoffChartKernelEuclid (I := I) (M := M) α) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  classical
  by_cases htar : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx
      htar]
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    have hb_notin : b ∉ tsupport (cutoffComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) := by
      intro hb_support
      apply hy
      refine ⟨extChartAt I α b, ?_, ?_⟩
      · exact cutoffComponentScalar_chartImage_subset_kernel
          (I := I) (M := M) g r s S α Idx Jdx ⟨b, hb_support, rfl⟩
      · have hmem : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
          DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
            (I := I) (M := M) htar
        rw [hb_def, (extChartAt I α).right_inv hmem, toEuclidean.apply_symm_apply]
    exact image_eq_zero_of_notMem_tsupport hb_notin
  · exact cutoffComponentEuclid_apply_of_notMem (I := I) (M := M) g r s S α
      Idx Jdx htar

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_eq_zero_off_cutoffChartKernelEuclid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cutoffComponentEuclid_eq_zero_off_cutoffChartKernelEuclid target :: scope.openDecls } }

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 := by
  classical
  have h_dense : DenseRange
      (fun S : SmoothCcTensor g r s => (S : TensorL2 r s g)) :=
    UniformSpace.Completion.denseRange_coe (α := SmoothCcTensor g r s)
  obtain ⟨x, hx_range, hx_tendsto⟩ :=
    mem_closure_iff_seq_limit.mp (h_dense u)
  choose S hS using hx_range
  have h_comp_tendsto : Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((S n : TensorL2 r s g)) α P₀)
      _root_.Filter.atTop
      (𝓝 (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)) := by
    have h_clm :=
      ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α
        P₀).continuous.tendsto u).comp hx_tendsto
    refine Filter.Tendsto.congr (fun n => ?_) h_clm
    simp only [Function.comp_apply, hS n, tensorL2ChartComponentCutoffCLM_apply]
  have h_term : ∀ n : ℕ,
      ∀ᵐ y ∂(chartLebesgueMeasure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            ((S n : TensorL2 r s g)) α P₀ : EuclN → ℝ) y = 0 := by
    intro n
    have h_ae := tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
      (I := I) (M := M) g r s (S n) α P₀
    filter_upwards [h_ae] with y hy hyK
    rw [hy]
    exact cutoffComponentEuclid_eq_zero_off_cutoffChartKernelEuclid
      (I := I) (M := M) g r s (S n) α P₀.1 P₀.2 hyK
  exact ae_eq_zero_off_of_tendsto_Lp h_term h_comp_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorL2ChartComponentCutoff_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (fun y => (tensorL2ChartComponentCutoff (I := I) (M := M)
        g r s u α P₀ : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : _root_.MeasureTheory.MemLp (fun y => (tensorL2ChartComponentCutoff (I := I) (M := M)
      g r s u α P₀ : EuclN → ℝ) y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    Lp.memLp (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
      (I := I) (M := M) g r s u α P₀)
    h_plain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_memLp_weighted

omit [CompleteSpace E] in
theorem crossLeftLimitComponent_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    MemLp (fun y => (crossLeftLimitComponent (I := I) (M := M)
        g r s i α P : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [crossLeftLimitComponent]
  exact tensorL2ChartComponentCutoff_memLp_weighted (I := I) (M := M)
    g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitComponent_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitComponent_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitComponent_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossLeftLimitComponent_memLp_weighted

omit [CompleteSpace E] in
theorem crossRightLimitComponent_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    MemLp (fun y => (crossRightLimitComponent (I := I) (M := M)
        g r s i α P : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [crossRightLimitComponent]
  exact tensorL2ChartComponentCutoff_memLp_weighted (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.crossRightLimitComponent_memLp_weighted

omit [CompleteSpace E] in
lemma covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀ y = 0 := by
  classical
  rw [covPrincipalRotationCoeffLimit]
  refine Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
    Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))))
  rw [Set.indicator_of_notMem hy, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel

omit [CompleteSpace E] in
lemma covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀ y = 0 := by
  classical
  rw [covLowerOrderRotationValueCoeffLimit,
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => by
        rw [Set.indicator_of_notMem hy, _root_.MulZeroClass.zero_mul])))),
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ =>
        Finset.sum_eq_zero (fun p _ => by
          rw [Set.indicator_of_notMem hy, _root_.MulZeroClass.zero_mul]))))),
    add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel

omit [CompleteSpace E] in
lemma weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y = 0 := by
  classical
  rw [weightedGradCoeffDivLimit,
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun p _ => by
        rw [Set.indicator_of_notMem hy, _root_.MulZeroClass.zero_mul])))),
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun p _ => by
        rw [Set.indicator_of_notMem hy, _root_.MulZeroClass.zero_mul])))),
    add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel

omit [CompleteSpace E] in
theorem covPrincipalRotationCoeffLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : _root_.MeasureTheory.MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
      g r s i α P₀) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    covPrincipalRotationCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covPrincipalRotationCoeffLimit_memLp_weighted

omit [CompleteSpace E] in
theorem covLowerOrderRotationValueCoeffLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : _root_.MeasureTheory.MemLp (covLowerOrderRotationValueCoeffLimit
      (I := I) (M := M) g r s i α P₀) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
      g r s i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy))
    h_plain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covLowerOrderRotationValueCoeffLimit_memLp_weighted

omit [CompleteSpace E] in
theorem weightedGradCoeffDivLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : _root_.MeasureTheory.MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
      g r s i α P₀ l) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    weightedGradCoeffDivLimit_memLp (I := I) (M := M)
      g r s i α P₀ l
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ l hy))
    h_plain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.weightedGradCoeffDivLimit_memLp_weighted

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem memLp_weighted_contDiffOn_mul
    (g : SmoothRiemannianMetric I M) (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (hw : _root_.MeasureTheory.MemLp w 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (hw_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0) :
    _root_.MeasureTheory.MemLp (fun y => c y * w y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set μw : _root_.MeasureTheory.Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hcontOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image
        (hcontOn_K.norm)
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  have hci_bd : ∀ y : EuclN, ‖K.indicator c y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]; exact hC_bd y hy
    · rw [Set.indicator_of_notMem hy, norm_zero]; exact hC_nn
  have hc_meas : _root_.MeasureTheory.AEStronglyMeasurable (K.indicator c) μw := by
    have hmeas_restr : _root_.MeasureTheory.AEStronglyMeasurable c (μw.restrict K) := by
      rw [hμw_def, Measure.restrict_restrict hK_meas,
        Set.inter_eq_self_of_subset_left hK_in]
      exact hcontOn_K.aestronglyMeasurable hK_meas
    exact (aestronglyMeasurable_indicator_iff hK_meas).mpr hmeas_restr
  have h_prod_eq : (fun y => c y * w y) =ᵐ[μw]
      (fun y => K.indicator c y * w y) := by
    filter_upwards [hw_zero] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.mul_zero]
  have h_bdd_mul : _root_.MeasureTheory.MemLp (fun y => K.indicator c y * w y) 2 μw := by
    refine ⟨hc_meas.mul hw.1, ?_⟩
    have hpt : ∀ y : EuclN, ‖K.indicator c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
      intro y
      have hlhs : ‖K.indicator c y * w y‖ = ‖K.indicator c y‖ * ‖w y‖ :=
        norm_mul _ _
      have hrhs : ‖(C : ℝ) • w y‖ = C * ‖w y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC_nn]
      rw [hlhs, hrhs]
      exact mul_le_mul_of_nonneg_right (hci_bd y) (norm_nonneg _)
    exact lt_of_le_of_lt (_root_.MeasureTheory.eLpNorm_mono (μ := μw) hpt) (hw.const_smul (C : ℝ)).2
  exact MemLp.ae_eq h_prod_eq.symm h_bdd_mul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_weighted_contDiffOn_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_weighted_contDiffOn_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_weighted_contDiffOn_mul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.memLp_weighted_contDiffOn_mul

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma chartPulledWeightedMeasure_restrict_absolutelyContinuous
    (g : SmoothRiemannianMetric I M) (α : M) :
    (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartPulledWeightedMeasure
  exact (_root_.MeasureTheory.withDensity_absolutelyContinuous (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) _).restrict _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_absolutelyContinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_absolutelyContinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_absolutelyContinuous ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartPulledWeightedMeasure_restrict_absolutelyContinuous

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 :=
  (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
    g α).ae_le
    (tensorL2ChartComponent_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s u α P₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 :=
  (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
    g α).ae_le
    (tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
      (I := I) (M := M) g r s u α P₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid_weighted

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
lemma componentLpLimit_ae_zero_off_chartPouKernel_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((componentLpLimit (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set uVec :=
    tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i
    with huVec_def
  have h_smul_w : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s uVec α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le
      (by rw [componentLpLimit]; exact Lp.coeFn_smul i.fst.val _)
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted
    (I := I) (M := M) g r s uVec α P
  filter_upwards [h_smul_w, h_comp_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_ae_zero_off_chartPouKernel_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_ae_zero_off_chartPouKernel_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_ae_zero_off_chartPouKernel_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_ae_zero_off_chartPouKernel_weighted

open _root_.Submission.DifferentialGeometry.Analysis.Spectral in
omit [CompleteSpace E] in
lemma componentLpLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    MemLp (fun y => ((componentLpLimit (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set uVec :=
    tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i
    with huVec_def
  have h_comp : _root_.MeasureTheory.MemLp (fun y => (tensorL2ChartComponent (I := I) (M := M)
      g r s uVec α P : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s uVec α P
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s uVec α P :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y) :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le
      (by rw [componentLpLimit]; exact Lp.coeFn_smul i.fst.val _)
  exact (h_comp.const_smul i.fst.val).ae_eq h_smul.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_memLp_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_memLp_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_memLp_weighted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.componentLpLimit_memLp_weighted

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
