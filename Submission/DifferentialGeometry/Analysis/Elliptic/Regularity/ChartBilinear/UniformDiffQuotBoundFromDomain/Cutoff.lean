import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.ChartBilinearVariationalIdentity
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth

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
namespace ChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeAssembly
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergSubstitutionNonSmooth
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem exists_cutoff_eq_one_on_cthickening_tsupport
    [I.Boundaryless]
    {α : M} {η : EuclN → ℝ} (hη_support : HasCompactSupport η)
    (h_cthick_1_in_chart : Metric.cthickening 1 (tsupport η) ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ χ : EuclN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      (∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ Metric.cthickening 1 (tsupport η), χ x = 1) ∧
      tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hη_tsupp_compact : IsCompact (tsupport η) := hη_support
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_cthick_1_compact : IsCompact (Metric.cthickening 1 (tsupport η)) :=
    hη_tsupp_compact.cthickening
  obtain ⟨δ, hδ_pos, hδ_in_chart⟩ :=
    h_cthick_1_compact.exists_cthickening_subset_open h_chart_open
      h_cthick_1_in_chart
  obtain ⟨χ, hχ_smooth, hχ_cs, hχ_one_nhds, hχ_tsupp, hχ_range⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact
      h_cthick_1_compact
      (Metric.isOpen_thickening (δ := δ)
        (E := Metric.cthickening 1 (tsupport η)))
      (Metric.self_subset_thickening hδ_pos _)
  have hχ_one : ∀ x ∈ Metric.cthickening 1 (tsupport η), χ x = 1 := fun _ hx =>
    hχ_one_nhds.self_of_nhdsSet hx
  have hχ_tsupp_in_chart : tsupport χ ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    intro x hx
    have h1 : x ∈ Metric.thickening δ (Metric.cthickening 1 (tsupport η)) :=
      hχ_tsupp hx
    have h2 : x ∈ Metric.cthickening δ (Metric.cthickening 1 (tsupport η)) :=
      Metric.thickening_subset_cthickening δ _ h1
    exact hδ_in_chart h2
  have hχ_nn : ∀ x : EuclN, 0 ≤ χ x ∧ χ x ≤ 1 := by
    intro x
    have hx_range : χ x ∈ Set.range χ := Set.mem_range_self x
    have hx_mem := hχ_range hx_range
    exact ⟨hx_mem.1, hx_mem.2⟩
  exact ⟨χ, hχ_smooth, hχ_cs, hχ_nn, hχ_one, hχ_tsupp_in_chart⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.exists_cutoff_eq_one_on_cthickening_tsupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.exists_cutoff_eq_one_on_cthickening_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.exists_cutoff_eq_one_on_cthickening_tsupport ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.exists_cutoff_eq_one_on_cthickening_tsupport

omit [NeZero (Module.finrank ℝ E)] in
theorem cutoff_mul_fChart_memLp_two
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {χ : EuclN → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_cs : HasCompactSupport χ)
    (hχ_support_in : tsupport χ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (fun x => χ x * D.fChart x) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
  classical
  have hχ_cont : Continuous χ := hχ_smooth.continuous
  obtain ⟨M_χ, hM_χ_nn, hM_χ_bd⟩ : ∃ M_χ : ℝ, 0 ≤ M_χ ∧ ∀ x, |χ x| ≤ M_χ := by
    by_cases hSupport_empty : (tsupport χ).Nonempty
    · obtain ⟨xMax, _hxMax_in, hxMax_max⟩ :=
        hχ_cs.exists_isMaxOn hSupport_empty hχ_cont.abs.continuousOn
      refine ⟨|χ xMax|, abs_nonneg _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact hxMax_max hx
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]; exact abs_nonneg _
    · refine ⟨0, le_refl _, ?_⟩
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact absurd ⟨x, hx⟩ hSupport_empty
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [hχx, abs_zero]
  have h_support_compact : IsCompact (tsupport χ) := hχ_cs
  have h_support_meas : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  have hf_l2_support : _root_.MeasureTheory.MemLp D.fChart 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
      D.f_chart_memLp_weighted h_support_compact h_support_meas hχ_support_in
  have h_f_aesm_restrict : _root_.MeasureTheory.AEStronglyMeasurable D.fChart
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hf_l2_support.aestronglyMeasurable
  have h_pt_le : ∀ᵐ x ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)),
      ‖χ x * D.fChart x‖ ≤ ‖M_χ * D.fChart x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hM_χ_nn]
    exact mul_le_mul_of_nonneg_right (hM_χ_bd x) (abs_nonneg _)
  have h_prod_aesm_restrict :
      _root_.MeasureTheory.AEStronglyMeasurable (fun x => χ x * D.fChart x)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    hχ_cont.aestronglyMeasurable.restrict.mul h_f_aesm_restrict
  have h_restrict_lp : _root_.MeasureTheory.MemLp (fun x => χ x * D.fChart x) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (tsupport χ)) :=
    MemLp.mono (hf_l2_support.const_mul M_χ) h_prod_aesm_restrict h_pt_le
  have h_indicator_eq : (tsupport χ).indicator (fun x => χ x * D.fChart x) =
      (fun x => χ x * D.fChart x) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hχx, _root_.MulZeroClass.zero_mul]
  have h_indicator_lp :
      _root_.MeasureTheory.MemLp ((tsupport χ).indicator (fun x => χ x * D.fChart x)) 2
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) :=
    (MeasureTheory.memLp_indicator_iff_restrict h_support_meas).mpr h_restrict_lp
  rw [h_indicator_eq] at h_indicator_lp
  exact h_indicator_lp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.cutoff_mul_fChart_memLp_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.cutoff_mul_fChart_memLp_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.cutoff_mul_fChart_memLp_two ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl.cutoff_mul_fChart_memLp_two

end ChartBilinearH1Compl

end Laplacian
end Analysis
end DifferentialGeometry
