import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartTest

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private lemma memLp_of_withDensity_lower_bound
    {A : Type*} [MeasurableSpace A] {μ : _root_.MeasureTheory.Measure A} {w : A → ℝ≥0∞}
    {s : Set A} (hs : MeasurableSet s) {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ⊤)
    (hbound : ∀ x ∈ s, c ≤ w x) {f : A → ℝ} {p : ℝ≥0∞}
    (hf : _root_.MeasureTheory.MemLp f p (μ.withDensity w))
    (hzero : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : _root_.MeasureTheory.MemLp f p μ := by
  have hmeasure : μ.restrict s ≤ c⁻¹ • μ.withDensity w := by
    rw [← _root_.MeasureTheory.withDensity_indicator_one hs, ← _root_.MeasureTheory.withDensity_smul' c⁻¹ w (by simpa using hc)]
    apply _root_.MeasureTheory.withDensity_mono
    filter_upwards [] with x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      calc
        1 = c⁻¹ * c := (ENNReal.inv_mul_cancel hc hct).symm
        _ ≤ c⁻¹ * w x := mul_le_mul le_rfl (hbound x hx) zero_le zero_le
    · simp only [Set.indicator_of_notMem hx, Pi.smul_apply, smul_eq_mul]
      exact zero_le
  have hlocal : _root_.MeasureTheory.MemLp f p (μ.restrict s) := hf.of_measure_le_smul (by simpa using hc) hmeasure
  apply ((_root_.MeasureTheory.memLp_indicator_iff_restrict hs).2 hlocal).ae_eq
  filter_upwards [hzero] with x hx
  by_cases hxs : x ∈ s
  · exact Set.indicator_of_mem hxs f
  · rw [Set.indicator_of_notMem hxs, hx hxs]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_of_withDensity_lower_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_of_withDensity_lower_bound target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }


theorem memLp_scalarOnE_of_support [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {p : ℝ≥0∞}
    (hf : _root_.MeasureTheory.MemLp f p (riemannianVolumeMeasure I M g))
    (hsupp : tsupport f ⊆ (chartAt H α).source) :
    MemLp (scalarOnE (I := I) α f) p
      ((modelHaar (E := E)).restrict (extChartAt I α).target) := by
  classical
  have hzero : ∀ x, x ∉ (chartAt H α).source → f x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
  have hchart : _root_.MeasureTheory.MemLp f p (chartLocalMeasure g α) := by
    have hlocal : _root_.MeasureTheory.MemLp f p ((chartLocalMeasure g α).restrict (chartAt H α).source) := by
      rw [← Chart.volume_restrict_eq g α]
      exact hf.restrict _
    apply ((_root_.MeasureTheory.memLp_indicator_iff_restrict (chartAt H α).open_source.measurableSet).2 hlocal).ae_eq
    filter_upwards [] with x
    by_cases hx : x ∈ (chartAt H α).source
    · exact Set.indicator_of_mem hx f
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  let ν := (modelHaar (E := E)).restrict (extChartAt I α).target
  let w : E → ℝ≥0∞ := fun y => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))
  have hweighted : _root_.MeasureTheory.MemLp (scalarOnE (I := I) α f) p (ν.withDensity w) := by
    exact hchart.comp_of_map
      ((aemeasurable_extChartAt_symm_restrict_target (I := I) (E := E) α).mono_ac
        (_root_.MeasureTheory.withDensity_absolutelyContinuous ν w))
  let K := (extChartAt I α) '' tsupport f
  obtain ⟨hK, hKT⟩ := Chart.image_extChartAt_tsupport_compact_subset_target (I := I) hsupp
  have hzeroK : ∀ᵐ y ∂ν, y ∉ K → scalarOnE (I := I) α f y = 0 := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem (measurableSet_extChartAt_target (I := I) α)] with y hy
    intro hyK
    change f ((extChartAt I α).symm y) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hfK
    apply hyK
    exact ⟨(extChartAt I α).symm y, hfK, (extChartAt I α).right_inv hy⟩
  by_cases hKne : K.Nonempty
  · obtain ⟨c, hc, hbound⟩ := Chart.exists_inf_chartDensity_on_compact g α hK hKne hKT
    exact memLp_of_withDensity_lower_bound hK.measurableSet
      (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top
      (fun y hy => ENNReal.ofReal_le_ofReal (hbound y hy)) hweighted hzeroK
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    apply (MemLp.zero).ae_eq
    filter_upwards [hzeroK] with y hy
    exact (hy (by simp only [hKe, Set.mem_empty_iff_false, not_false_eq_true])).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_scalarOnE_of_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_scalarOnE_of_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_scalarOnE_of_support ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_scalarOnE_of_support


theorem memLp_chartPushedRaw_of_support [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {p : ℝ≥0∞}
    (hf : _root_.MeasureTheory.MemLp f p (riemannianVolumeMeasure I M g))
    (hsupp : tsupport f ⊆ (chartAt H α).source) :
    _root_.MeasureTheory.MemLp (Chart.chartPushedRaw I α f) p
      (volume.restrict (Chart.chartTargetEuclid (I := I) α)) := by
  have hmeas : MeasurableEmbedding (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpres : _root_.MeasureTheory.MeasurePreserving (toEuclidean (E := E)) (modelHaar (E := E)) volume :=
    ⟨hmeas.measurable, map_toEuclidean_modelHaar_eq_volume⟩
  unfold Chart.chartTargetEuclid
  rw [← (hpres.restrict_image_emb hmeas (extChartAt I α).target).map_eq,
    hmeas.memLp_map_measure_iff]
  apply (memLp_scalarOnE_of_support g α hf hsupp).ae_eq
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (measurableSet_extChartAt_target (I := I) α)] with y hy
  have hyE : toEuclidean y ∈ Chart.chartTargetEuclid (I := I) α := ⟨y, hy, rfl⟩
  dsimp only [Function.comp_apply]
  rw [Chart.chartPushedRaw_apply_of_mem α f hyE, ContinuousLinearEquiv.symm_apply_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_chartPushedRaw_of_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_chartPushedRaw_of_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_chartPushedRaw_of_support ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_chartPushedRaw_of_support

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
