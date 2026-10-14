import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Sobolev.Approximation.Density.Smooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartEffectiveSource

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def diffChartForcingNumerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (y : EuclN) : ℝ :=
  densityOnEuclid (I := I) g α y *
      chosenFChartDeriv (I := I) (M := M) g α hu_h l y
    - densityDerivOnEuclid (I := I) g α l y *
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).uChart y
    + densityDerivOnEuclid (I := I) g α l y *
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).fChart y
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weakPartial i y)
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i j y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator

noncomputable def diffChartForcing
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    EuclN → ℝ :=
  Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
    (fun y => diffChartForcingNumerator (I := I) (M := M) g α l hu_h y /
      densityOnEuclid (I := I) g α y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing

theorem diffChartForcing_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (y : EuclN) :
    diffChartForcing (I := I) (M := M) g α l hu_h y =
      Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
        (fun z => diffChartForcingNumerator (I := I) (M := M) g α l hu_h z /
          densityOnEuclid (I := I) g α z) y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_apply

theorem density_mul_diffChartForcing_eq_indicator_numerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (y : EuclN)
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    densityOnEuclid (I := I) g α y *
        diffChartForcing (I := I) (M := M) g α l hu_h y =
      Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
        (fun z => diffChartForcingNumerator (I := I) (M := M) g α l hu_h z) y := by
  classical
  rw [diffChartForcing_apply]
  by_cases hy_K : y ∈ chartImagePOUTsupport (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy_K, Set.indicator_of_mem hy_K]
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy
    field_simp
  · rw [Set.indicator_of_notMem hy_K, Set.indicator_of_notMem hy_K, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.density_mul_diffChartForcing_eq_indicator_numerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.density_mul_diffChartForcing_eq_indicator_numerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.density_mul_diffChartForcing_eq_indicator_numerator ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.density_mul_diffChartForcing_eq_indicator_numerator

theorem diffChartForcing_supported_in_chartImagePOUTsupport
    {g : SmoothRiemannianMetric I M} {α : M}
    {l : Fin (Module.finrank ℝ E)}
    {u_h : H1Compl g} {hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2} :
    Function.support (diffChartForcing (I := I) (M := M) g α l hu_h) ⊆
      chartImagePOUTsupport (I := I) (M := M) α := by
  unfold diffChartForcing
  exact Set.support_indicator_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_supported_in_chartImagePOUTsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_supported_in_chartImagePOUTsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_supported_in_chartImagePOUTsupport ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_supported_in_chartImagePOUTsupport

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma exists_bound_continuousOn_compact
    {f : EuclN → ℝ} {α : M}
    (hf_contOn :
      ContinuousOn f (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K, |f y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have hf_K : ContinuousOn f K := hf_contOn.mono hK_in
  have h_abs_K : ContinuousOn (fun y => |f y|) K :=
    continuous_abs.comp_continuousOn hf_K
  obtain ⟨y_max, _hy_max_K, h_max⟩ :=
    hK_compact.exists_isMaxOn hK_ne h_abs_K
  exact ⟨|f y_max|, fun y hy => h_max hy⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.exists_bound_continuousOn_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.exists_bound_continuousOn_compact target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma memLp_two_of_bounded_mul
    {f h : EuclN → ℝ} {K : Set EuclN}
    (hh_meas : _root_.MeasureTheory.AEStronglyMeasurable h ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K))
    {C : ℝ}
    (hh_bd : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K), |h y| ≤ C)
    (hf : _root_.MeasureTheory.MemLp f 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)) :
    MemLp (fun y => h y * f y) 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  have hh_memLp_top : _root_.MeasureTheory.MemLp h ∞ ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
    refine ⟨hh_meas, ?_⟩
    rw [_root_.MeasureTheory.eLpNorm_exponent_top]
    refine lt_of_le_of_lt ?_
      (show (ENNReal.ofReal (_root_.Max.max C 0) : ℝ≥0∞) < ⊤ from
        ENNReal.ofReal_lt_top)
    refine _root_.MeasureTheory.eLpNormEssSup_le_of_ae_enorm_bound (C := ENNReal.ofReal (_root_.Max.max C 0)) ?_
    refine hh_bd.mono (fun y hy => ?_)
    rw [Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    exact hy.trans (le_max_left _ _)
  exact MemLp.mul' (p := ∞) (q := 2) (r := 2) hf hh_memLp_top

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.memLp_two_of_bounded_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.memLp_two_of_bounded_mul target :: scope.openDecls } }

private abbrev Kα (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_compact (α : M) :
    IsCompact (Kα (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα_compact target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Kα_meas (α : M) :
    MeasurableSet (Kα (I := I) (M := M) α) :=
  (Kα_compact (I := I) (M := M) α).isClosed.measurableSet

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα_meas
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα_meas target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma Kα_subset_target (α : M) :
    Kα (I := I) (M := M) α ⊆ chartTargetEuclid (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα_subset_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.Kα_subset_target target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma memLp_two_continuousOn_mul_on_Kα
    {α : M} {h f : EuclN → ℝ}
    (hh_contOn : ContinuousOn h (chartTargetEuclid (I := I) (M := M) α))
    (hf : _root_.MeasureTheory.MemLp f 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α))) :
    _root_.MeasureTheory.MemLp (fun y => h y * f y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  obtain ⟨C, hC_bd⟩ :=
    exists_bound_continuousOn_compact (I := I) (M := M) (α := α)
      hh_contOn (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  have h_meas :
      _root_.MeasureTheory.AEStronglyMeasurable h
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    have h_K : ContinuousOn h (Kα (I := I) (M := M) α) :=
      hh_contOn.mono (Kα_subset_target (I := I) (M := M) α)
    exact h_K.aestronglyMeasurable (Kα_meas (I := I) (M := M) α)
  have h_ae_bd : ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (Kα (I := I) (M := M) α)),
      |h y| ≤ C := by
    refine (_root_.MeasureTheory.ae_restrict_iff' (Kα_meas (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact hC_bd y hy
  exact memLp_two_of_bounded_mul (h := h) h_meas h_ae_bd hf

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.memLp_two_continuousOn_mul_on_Kα
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.memLp_two_continuousOn_mul_on_Kα target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartPulledWeightedMeasure_restrict_compact_le_volume
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
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
  rw [Measure.restrict_apply hA, Measure.smul_apply,
    Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [_root_.MeasureTheory.withDensity_apply _ (hA.inter hK_meas)]
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hK_meas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
      ENNReal.ofReal c_max * (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.chartPulledWeightedMeasure_restrict_compact_le_volume
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.chartPulledWeightedMeasure_restrict_compact_le_volume target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma memLp_chartPulledWeighted_restrict_of_volume_restrict
    {g : SmoothRiemannianMetric I M} {α : M} {w : EuclN → ℝ}
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hw : _root_.MeasureTheory.MemLp w 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K)) :
    MemLp w 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K) := by
  obtain ⟨c, _hc_pos, h_le⟩ :=
    chartPulledWeightedMeasure_restrict_compact_le_volume (I := I) (M := M)
      α hK_compact hK_meas hK_in
  exact hw.of_measure_le_smul (c := ENNReal.ofReal c)
    ENNReal.ofReal_ne_top h_le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.memLp_chartPulledWeighted_restrict_of_volume_restrict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.memLp_chartPulledWeighted_restrict_of_volume_restrict target :: scope.openDecls } }

private lemma density_mul_chosenFChartDeriv_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => densityOnEuclid (I := I) g α y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  by_cases h_memW1p :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).fChart
        (chartTargetEuclid (I := I) (M := M) α)
  · have h_global :
        MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l) 2
          ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
      unfold chosenFChartDeriv
      exact chosenWeakPartialOrZero_memLp_of_mem h_memW1p l
    have hK_meas : MeasurableSet (Kα (I := I) (M := M) α) :=
      Kα_meas (I := I) (M := M) α
    have h_restrict :
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)).restrict
          (Kα (I := I) (M := M) α) =
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α) := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left (Kα_subset_target (I := I) (M := M) α)
    have h_K : _root_.MeasureTheory.MemLp (chosenFChartDeriv (I := I) (M := M) g α hu_h l) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
      rw [← h_restrict]
      exact h_global.restrict _
    exact memLp_two_continuousOn_mul_on_Kα (α := α)
      (densityOnEuclid_continuousOn (I := I) g α) h_K
  · have h_zero : chosenFChartDeriv (I := I) (M := M) g α hu_h l = 0 := by
      unfold chosenFChartDeriv
      exact chosenWeakPartialOrZero_of_not_mem h_memW1p l
    have : (fun y => densityOnEuclid (I := I) g α y *
        chosenFChartDeriv (I := I) (M := M) g α hu_h l y) = (fun _ => 0) := by
      funext y
      rw [h_zero]; simp
    rw [this]
    exact MemLp.zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.density_mul_chosenFChartDeriv_memLp_vol_K
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.density_mul_chosenFChartDeriv_memLp_vol_K target :: scope.openDecls } }

private lemma densityDerivOnEuclid_mul_u_chart_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => densityDerivOnEuclid (I := I) g α l y *
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).uChart y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_u_chart_K :
      MemLp ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).uChart) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
      (I := I) (M := M) (g := g) (α := α)
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).u_chart_memLp_weighted
      (Kα_compact (I := I) (M := M) α)
      (Kα_meas (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densityDerivOnEuclid_continuousOn (I := I) g α l) h_u_chart_K

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.densityDerivOnEuclid_mul_u_chart_memLp_vol_K
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.densityDerivOnEuclid_mul_u_chart_memLp_vol_K target :: scope.openDecls } }

private lemma densityDerivOnEuclid_mul_f_chart_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => densityDerivOnEuclid (I := I) g α l y *
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).fChart y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_f_chart_K :
      MemLp ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).fChart) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
      (I := I) (M := M) (g := g) (α := α)
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart_memLp_weighted
      (Kα_compact (I := I) (M := M) α)
      (Kα_meas (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (densityDerivOnEuclid_continuousOn (I := I) g α l) h_f_chart_K

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.densityDerivOnEuclid_mul_f_chart_memLp_vol_K
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.densityDerivOnEuclid_mul_f_chart_memLp_vol_K target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma weightedInvGramDerivOnEuclid_partial_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (EuclideanSpace.single j 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn :
      ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l)
        (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
  have h_fderiv_diff :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).contDiff
  have h := h_eval.contDiffOn.comp h_fderiv_diff (_root_.Set.mapsTo_univ _ _)
  exact h.continuousOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.weightedInvGramDerivOnEuclid_partial_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.weightedInvGramDerivOnEuclid_partial_continuousOn target :: scope.openDecls } }

private lemma weightedInvGramDerivOnEuclid_fderiv_mul_weak_partial_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    _root_.MeasureTheory.MemLp (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weakPartial i y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_wp_K :
      MemLp ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weakPartial i) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).weak_partial_locally_memLp i
      (Kα (I := I) (M := M) α)
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_partial_continuousOn
      (I := I) (M := M) g α i j l) h_wp_K

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.weightedInvGramDerivOnEuclid_fderiv_mul_weak_partial_memLp_vol_K
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.weightedInvGramDerivOnEuclid_fderiv_mul_weak_partial_memLp_vol_K target :: scope.openDecls } }

private lemma weightedInvGramDerivOnEuclid_mul_secondPartialChartPushedU_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i j : Fin (Module.finrank ℝ E)) :
    MemLp (fun y => weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_second_K :
      MemLp (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i j) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) :=
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i j
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_target (I := I) (M := M) α)
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l) h_second_K

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.weightedInvGramDerivOnEuclid_mul_secondPartialChartPushedU_memLp_vol_K
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.weightedInvGramDerivOnEuclid_mul_secondPartialChartPushedU_memLp_vol_K target :: scope.openDecls } }

private lemma diffChartForcingNumerator_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (diffChartForcingNumerator (I := I) (M := M) g α l hu_h) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_I := density_mul_chosenFChartDeriv_memLp_vol_K (I := I) (M := M) g α l hu_h
  have h_II := densityDerivOnEuclid_mul_u_chart_memLp_vol_K (I := I) (M := M) g α l hu_h
  have h_III := densityDerivOnEuclid_mul_f_chart_memLp_vol_K (I := I) (M := M) g α l hu_h
  have h_IV : _root_.MeasureTheory.MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weakPartial i y)) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply _root_.MeasureTheory.memLp_finsetSum
    intro i _
    apply _root_.MeasureTheory.memLp_finsetSum
    intro j _
    exact weightedInvGramDerivOnEuclid_fderiv_mul_weak_partial_memLp_vol_K (I := I) (M := M) g α l
      hu_h i j
  have h_V : _root_.MeasureTheory.MemLp (fun y => (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i j y)) 2
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
    apply _root_.MeasureTheory.memLp_finsetSum
    intro i _
    apply _root_.MeasureTheory.memLp_finsetSum
    intro j _
    exact weightedInvGramDerivOnEuclid_mul_secondPartialChartPushedU_memLp_vol_K (I := I) (M := M) g
      α l hu_h i j
  have h_step1 := h_I.sub h_II
  have h_step2 := h_step1.add h_III
  have h_step3 := h_step2.add h_IV
  have h_step4 := h_step3.add h_V
  unfold diffChartForcingNumerator
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun y => by
    simp only [Pi.add_apply, Pi.sub_apply]) h_step4

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator_memLp_vol_K
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator_memLp_vol_K target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma one_div_densityOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_cont := densityOnEuclid_continuousOn (I := I) g α
  have h_inv := h_cont.inv₀ (fun y hy =>
    (densityOnEuclid_pos (I := I) g α hy).ne')
  have h_eq : (fun y => 1 / densityOnEuclid (I := I) g α y) =
      (fun y => (densityOnEuclid (I := I) g α y)⁻¹) := by
    funext y; rw [one_div]
  rw [h_eq]
  exact h_inv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.one_div_densityOnEuclid_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.one_div_densityOnEuclid_continuousOn target :: scope.openDecls } }

private lemma diffChartForcingNumerator_div_density_memLp_vol_K
    (g : SmoothRiemannianMetric I M) (α : M)
    (l : Fin (Module.finrank ℝ E))
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    MemLp (fun y => diffChartForcingNumerator (I := I) (M := M) g α l hu_h y /
        densityOnEuclid (I := I) g α y) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Kα (I := I) (M := M) α)) := by
  classical
  have h_num := diffChartForcingNumerator_memLp_vol_K (I := I) (M := M) g α l hu_h
  have h_eq : (fun y => diffChartForcingNumerator (I := I) (M := M) g α l hu_h y /
      densityOnEuclid (I := I) g α y) =
      fun y => (1 / densityOnEuclid (I := I) g α y) *
        diffChartForcingNumerator (I := I) (M := M) g α l hu_h y := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  exact memLp_two_continuousOn_mul_on_Kα (α := α)
    (one_div_densityOnEuclid_continuousOn (I := I) (M := M) g α) h_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator_div_density_memLp_vol_K
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcingNumerator_div_density_memLp_vol_K target :: scope.openDecls } }

theorem diffChartForcing_memLp_two_weighted
    {g : SmoothRiemannianMetric I M} {α : M}
    {l : Fin (Module.finrank ℝ E)}
    {u_h : H1Compl g} {hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2} :
    MemLp (diffChartForcing (I := I) (M := M) g α l hu_h) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := Kα (I := I) (M := M) α with hK_def
  set f : EuclN → ℝ := fun y =>
    diffChartForcingNumerator (I := I) (M := M) g α l hu_h y /
      densityOnEuclid (I := I) g α y with hf_def
  have h_indicator_eq :
      diffChartForcing (I := I) (M := M) g α l hu_h = Set.indicator K f := by
    rfl
  rw [h_indicator_eq]
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_meas : MeasurableSet K := Kα_meas (I := I) (M := M) α
  have hK_compact : IsCompact K := Kα_compact (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    Kα_subset_target (I := I) (M := M) α
  rw [_root_.MeasureTheory.memLp_indicator_iff_restrict hK_meas]
  have h_double_restrict :
      ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (chartPulledWeightedMeasure (I := I) g α).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [h_double_restrict]
  refine memLp_chartPulledWeighted_restrict_of_volume_restrict
    (g := g) (α := α) hK_compact hK_meas hK_in ?_
  exact diffChartForcingNumerator_div_density_memLp_vol_K
    (I := I) (M := M) g α l hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_memLp_two_weighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_memLp_two_weighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_memLp_two_weighted ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_memLp_two_weighted

end DiffChartEffectiveSource
end Laplacian
end Analysis
end DifferentialGeometry

end
