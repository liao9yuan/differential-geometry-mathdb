import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Completeness
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.MeasurablePullback
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Rellich
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.UniformSpace.UniformEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

section
variable [NeZero (Module.finrank ℝ E)]

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_cauchy_of_seminormCauchySeq
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (hf : CauchySeq f) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε := by
  intro ε hε_pos
  rw [Metric.cauchySeq_iff] at hf
  obtain ⟨N, hN⟩ := hf ε hε_pos
  refine ⟨N, ?_⟩
  intro m n hm hn
  have hdist := hN m hm n hn
  rw [dist_eq_norm] at hdist
  have h_norm_eq : ‖f m - f n‖ =
      (wkpNormChart (I := I) (M := M) k p (wkpChartFun (f m - f n))).toReal := rfl
  rw [h_norm_eq] at hdist
  have h_sub_val :
      wkpChartFun (f m - f n) =
        fun x => wkpChartFun (f m) x - wkpChartFun (f n) x := by
    ext x; rfl
  rw [h_sub_val] at hdist
  have h_lt_top : wkpNormChart (I := I) (M := M) k p
      (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp
      (MemWkpChart_sub (I := I) (M := M) hp
        (wkpChartFun_memWkpChart (f m)) (wkpChartFun_memWkpChart (f n)))
  have h_ne_top : wkpNormChart (I := I) (M := M) k p
      (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≠ ⊤ := h_lt_top.ne
  rw [← ENNReal.ofReal_toReal h_ne_top]
  exact ENNReal.ofReal_le_ofReal hdist.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_cauchy_of_seminormCauchySeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_cauchy_of_seminormCauchySeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_cauchy_of_seminormCauchySeq ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_cauchy_of_seminormCauchySeq

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_cauchy_of_wkpNormChart_cauchy
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f m)) y -
          chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  intro ε hε_pos
  obtain ⟨N, hN⟩ := h_cauchy ε hε_pos
  refine ⟨N, ?_⟩
  intro m n hm hn
  have h_le := hN m n hm hn
  have h_chartPushed_eq : (fun y => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (wkpChartFun (f m)) y -
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)) y) =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) := by
    funext y
    unfold chartPushed
    ring
  rw [h_chartPushed_eq]
  unfold wkpNormChart at h_le
  have h_summand_le_tsum :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑' α' : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α'
            (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x))
          (chartTargetEuclid (I := I) (M := M) α') :=
    ENNReal.le_tsum α
  exact le_trans h_summand_le_tsum h_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_cauchy_of_wkpNormChart_cauchy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_cauchy_of_wkpNormChart_cauchy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_cauchy_of_wkpNormChart_cauchy ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_cauchy_of_wkpNormChart_cauchy

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_chart_limit
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    ∃ v_α : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p v_α
        (chartTargetEuclid (I := I) (M := M) α) ∧
      _root_.Filter.Tendsto
        (fun n =>
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (fun y => chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
              (wkpChartFun (f n)) y - v_α y)
            (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) := by
  have h_chart_cauchy := chartPushed_cauchy_of_wkpNormChart_cauchy
    (I := I) (M := M) (hp := hp) h_cauchy α
  have h_chart_mem : ∀ n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)))
        (chartTargetEuclid (I := I) (M := M) α) := fun n =>
    (wkpChartFun_memWkpChart (f n)) α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    k p hp_one h_chart_mem h_chart_cauchy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.exists_chart_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.exists_chart_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.exists_chart_limit ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.exists_chart_limit

noncomputable def chartLimit
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  (exists_chart_limit (I := I) (M := M) hp_one h_cauchy α).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit

omit [NeZero (Module.finrank ℝ E)] in
lemma chartLimit_memWkp
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p
      (chartLimit (I := I) (M := M) hp_one h_cauchy α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (exists_chart_limit (I := I) (M := M) hp_one h_cauchy α).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_memWkp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_memWkp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_memWkp ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_memWkp

omit [NeZero (Module.finrank ℝ E)] in
lemma chartLimit_tendsto
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    _root_.Filter.Tendsto
      (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f n)) y -
            chartLimit (I := I) (M := M) hp_one h_cauchy α y)
          (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝓝 0) :=
  (exists_chart_limit (I := I) (M := M) hp_one h_cauchy α).choose_spec.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_tendsto ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_tendsto

omit [NeZero (Module.finrank ℝ E)] in
lemma chartLimit_ae_zero
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε)
    (α : M) :
    chartLimit (I := I) (M := M) hp_one h_cauchy α
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          toEuclidean ''
            ((extChartAt I α) ''
              (tsupport
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ))))]
        0 := by
  classical
  have h_v := chartLimit_tendsto (I := I) (M := M)
    hp_one h_cauchy α
  have h_eLp : _root_.Filter.Tendsto
      (fun n => _root_.MeasureTheory.eLpNorm
        (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)) y -
          chartLimit (I := I) (M := M) hp_one h_cauchy α y)
        p (volume.restrict (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε_pos
    rw [ENNReal.tendsto_atTop_zero] at h_v
    obtain ⟨N, hN⟩ := h_v ε hε_pos
    refine ⟨N, ?_⟩
    intro n hn
    have h_eLp_le_wkp :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm
        (d := Module.finrank ℝ E) (k := k) p
        (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (wkpChartFun (f n)) y -
          chartLimit (I := I) (M := M) hp_one h_cauchy α y)
        (chartTargetEuclid (I := I) (M := M) α) 0 (Nat.zero_le _) ![]
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
      at h_eLp_le_wkp
    exact le_trans h_eLp_le_wkp (hN n hn)
  have hp_zero : p ≠ 0 := by
    intro h
    rw [h] at hp_one
    exact absurd hp_one (by norm_num : ¬ ((1 : ℝ≥0∞) ≤ 0))
  have h_aesm_seq : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (wkpChartFun (f n)))
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := fun n =>
    ((wkpChartFun_memWkpChart (f n)) α).memLp.aestronglyMeasurable
  have h_aesm_lim : _root_.MeasureTheory.AEStronglyMeasurable
      (chartLimit (I := I) (M := M) hp_one h_cauchy α)
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
    (chartLimit_memWkp (I := I) (M := M)
      hp_one h_cauchy α).memLp.aestronglyMeasurable
  have h_meas : _root_.MeasureTheory.TendstoInMeasure
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α))
      (fun n => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (wkpChartFun (f n)))
      atTop (chartLimit (I := I) (M := M) hp_one h_cauchy α) :=
    _root_.MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_zero hp_top
      h_aesm_seq h_aesm_lim h_eLp
  obtain ⟨ns, _hns, h_ae⟩ := h_meas.exists_seq_tendsto_ae
  have hK_compact : IsCompact
      (toEuclidean ''
        ((extChartAt I α) ''
          (tsupport
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))) := by
    have h_tsupport : IsCompact
        (tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)) :=
      (isClosed_tsupport _).isCompact
    have h_sub :
        tsupport
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ) ⊆
          (extChartAt I α).source := by
      intro x hx
      have hx_source : x ∈ (chartAt H α).source :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hx
      rwa [extChartAt_source]
    have h_chart_image : IsCompact
        ((extChartAt I α) ''
          (tsupport
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ))) :=
      h_tsupport.image_of_continuousOn ((continuousOn_extChartAt α).mono h_sub)
    exact h_chart_image.image toEuclidean.continuous
  have h_off_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α \
        toEuclidean ''
          ((extChartAt I α) ''
            (tsupport
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))) :=
    (chartTargetEuclid_measurableSet (I := I) (M := M) α).diff
      hK_compact.measurableSet
  have h_ae_off :
      ∀ᵐ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          toEuclidean ''
            ((extChartAt I α) ''
              (tsupport
                ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α : M → ℝ)))),
        _root_.Filter.Tendsto
          (fun i => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (wkpChartFun (f (ns i))) y)
          _root_.Filter.atTop
          (𝓝 (chartLimit (I := I) (M := M) hp_one h_cauchy α y)) :=
    h_ae.filter_mono
      (_root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume Set.sdiff_subset))
  filter_upwards [h_ae_off, _root_.MeasureTheory.ae_restrict_mem h_off_meas] with y hy_tendsto hy_off
  have hzero : ∀ i, chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
      (wkpChartFun (f (ns i))) y = 0 := by
    intro i
    exact chartPushed_support_subset_compact_in_target (I := I) (M := M)
      α (wkpChartFun (f (ns i))) y hy_off.1 hy_off.2
  exact tendsto_nhds_unique hy_tendsto
    (by
      simp only [hzero]
      change _root_.Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) _root_.Filter.atTop (𝓝 (0 : ℝ))
      exact tendsto_const_nhds)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_ae_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_ae_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_ae_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.chartLimit_ae_zero

noncomputable def manifoldLimitFun
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε) : M → ℝ :=
  fun x =>
    ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I) (M := M),
      pullbackToManifold (I := I) β
        (chartLimit (I := I) (M := M) hp_one h_cauchy β) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.manifoldLimitFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.manifoldLimitFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.manifoldLimitFun ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.manifoldLimitFun

omit [NeZero (Module.finrank ℝ E)] in
lemma wkpChartFun_eq_finset_sum_pullback
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) k p hp) :
    (fun x : M => wkpChartFun u x) =
      fun x =>
        ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
            (I := I) (M := M),
          pullbackToManifold (I := I) β
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
              (wkpChartFun u)) x := by
  classical
  funext x
  have h_eq : ∀ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
        (I := I) (M := M),
      pullbackToManifold (I := I) β
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β
            (wkpChartFun u)) x =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x *
          wkpChartFun u x := by
    intro β _
    classical
    by_cases hxβ : x ∈ (chartAt H β).source
    · exact pullbackToManifold_chartPushed_apply_of_mem (I := I) β (wkpChartFun u) hxβ
    · rw [pullbackToManifold_apply_of_notMem (I := I) (α := β) _ hxβ]
      have h_subord :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate (I := I) (M := M)
      have h_tsupp : tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H β).source := h_subord β
      have h_x_notin : x ∉ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hxβ (h_tsupp h)
      have h_rho_zero :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport h_x_notin
      rw [h_rho_zero]; ring
  rw [Finset.sum_congr rfl h_eq]
  have h_factor :
      ∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
        (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x *
          wkpChartFun u x =
      (∑ β ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
        (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β : M → ℝ) x) *
        wkpChartFun u x := by
    rw [Finset.sum_mul]
  rw [h_factor]
  rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_eq_finset_sum_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_eq_finset_sum_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_eq_finset_sum_pullback ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.wkpChartFun_eq_finset_sum_pullback

end

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
