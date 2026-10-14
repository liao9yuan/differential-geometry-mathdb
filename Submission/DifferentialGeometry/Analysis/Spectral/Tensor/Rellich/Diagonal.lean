import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBoundPerSection
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich.OnManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponentScalar_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Measurable
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) := by
  have hsmooth :=
    tensorChartComponentScalar_contMDiff (I := I) (M := M) g r s S α Idx Jdx
  exact hsmooth.continuous.measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_measurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_measurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_measurable ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_measurable

private abbrev Triple (r s : ℕ) :=
  { α : M // α ∈ chartAtlasPOUFinset (I := I) (M := M) } ×
    (Fin r → Fin (Module.finrank ℝ E)) ×
    (Fin s → Fin (Module.finrank ℝ E))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Triple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Triple target :: scope.openDecls } }

private noncomputable def tripleFinset (r s : ℕ) :
    Finset (Triple (I := I) (M := M) r s) :=
  Finset.univ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tripleFinset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tripleFinset target :: scope.openDecls } }

private lemma single_triple_extraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ n,
      wkpNormChart (I := I) (M := M) 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ u_lim : M → ℝ,
        MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        Filter.Tendsto
          (fun j => _root_.MeasureTheory.eLpNorm
              (fun b => tensorChartComponentScalar (I := I) (M := M)
                g r s (S (σ j)).toCcTensor α Idx Jdx b - u_lim b)
              2 (riemannianVolumeMeasure (I := I) (M := M) g))
          Filter.atTop (𝓝 0) := by
  classical
  have hp_one : (1 : ℝ) < 2 := by norm_num
  have h_mem : ∀ n, MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal 2)
      (tensorChartComponentScalar (I := I) (M := M)
        g r s (S n).toCcTensor α Idx Jdx) := by
    intro n
    have h2_eq : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
      simp
    rw [← h2_eq]
    exact tensorChartComponent_memWkpChart_one_two
      (I := I) (M := M) g r s (S n) α Idx Jdx
  have h_meas : ∀ n, Measurable
      (tensorChartComponentScalar (I := I) (M := M)
        g r s (S n).toCcTensor α Idx Jdx) := by
    intro n
    exact tensorChartComponentScalar_measurable
      (I := I) (M := M) g r s (S n).toCcTensor α Idx Jdx
  have h_bdd : ∀ n, wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal 2)
      (tensorChartComponentScalar (I := I) (M := M)
        g r s (S n).toCcTensor α Idx Jdx) ≤ ENNReal.ofReal R := by
    intro n
    have h2_eq : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by simp
    rw [← h2_eq]
    exact hu_bdd n
  obtain ⟨σ, hσ_mono, u_lim, hu_lim_memLp, h_tendsto⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.rellich_kondrachov_chart_seq
      (I := I) (M := M) (E := E) (H := H) g hp_one
      h_meas h_mem h_bdd
  refine ⟨σ, hσ_mono, u_lim, ?_, ?_⟩
  · have h2_eq : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
    have h_vol :
        riemannianVolumeMeasure (I := I) (M := M) g =
          riemannianMeasure (I := I) g (chartAtlasPOU I M) :=
      riemannianVolumeMeasure_def (I := I) (M := M) g
    rw [h_vol, ← h2_eq]
    exact hu_lim_memLp
  · have h2_eq : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
    have h_vol :
        riemannianVolumeMeasure (I := I) (M := M) g =
          riemannianMeasure (I := I) g (chartAtlasPOU I M) :=
      riemannianVolumeMeasure_def (I := I) (M := M) g
    rw [h_vol, ← h2_eq]
    exact h_tendsto

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.single_triple_extraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.single_triple_extraction target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma tendsto_eLpNorm_diff_comp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {S : ℕ → SmoothCcTensorH1 g r s}
    {φ : ℕ → ℕ} {u_lim : M → ℝ}
    (h_tendsto :
      Filter.Tendsto
        (fun j => _root_.MeasureTheory.eLpNorm
            (fun b => tensorChartComponentScalar (I := I) (M := M)
              g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
            2 (riemannianVolumeMeasure (I := I) (M := M) g))
        Filter.atTop (𝓝 0))
    {ψ : ℕ → ℕ} (hψ_mono : StrictMono ψ) :
    Filter.Tendsto
      (fun j => _root_.MeasureTheory.eLpNorm
          (fun b => tensorChartComponentScalar (I := I) (M := M)
            g r s (S ((φ ∘ ψ) j)).toCcTensor α Idx Jdx b - u_lim b)
          2 (riemannianVolumeMeasure (I := I) (M := M) g))
      Filter.atTop (𝓝 0) := by
  have h_at_top : Filter.Tendsto ψ Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop_of_monotone hψ_mono.monotone
      (fun n => ⟨n, hψ_mono.id_le n⟩)
  exact h_tendsto.comp h_at_top

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_eLpNorm_diff_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tendsto_eLpNorm_diff_comp target :: scope.openDecls } }

private lemma diagonal_extraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R)
    (T : Finset (Triple (I := I) (M := M) r s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ t ∈ T, ∃ u_lim : M → ℝ,
        MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
        Filter.Tendsto
          (fun j => _root_.MeasureTheory.eLpNorm
              (fun b => tensorChartComponentScalar (I := I) (M := M)
                g r s (S (φ j)).toCcTensor t.1.1 t.2.1 t.2.2 b - u_lim b)
              2 (riemannianVolumeMeasure (I := I) (M := M) g))
          Filter.atTop (𝓝 0) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, fun t ht => ?_⟩
      exact absurd ht (Finset.notMem_empty t)
  | insert t T' ht_notin ih =>
      rcases ih with ⟨φ_T', hφ_T'_mono, hP_T'⟩
      have hu_bdd_comp : ∀ n,
          wkpNormChart (I := I) (M := M) 1 2
              (tensorChartComponentScalar (I := I) (M := M)
                g r s (S (φ_T' n)).toCcTensor t.1.1 t.2.1 t.2.2) ≤
            ENNReal.ofReal R := fun n => hu_bdd t.1.1 t.2.1 t.2.2 (φ_T' n)
      obtain ⟨σ_t, hσ_t_mono, u_t, hu_t_memLp, h_tendsto_t⟩ :=
        single_triple_extraction (I := I) (M := M) g r s t.1.1 t.2.1 t.2.2
          (S := fun n => S (φ_T' n))
          (R := R) hu_bdd_comp
      refine ⟨φ_T' ∘ σ_t, hφ_T'_mono.comp hσ_t_mono, ?_⟩
      intro t' ht'
      rcases Finset.mem_insert.mp ht' with rfl | ht'_T'
      · refine ⟨u_t, hu_t_memLp, ?_⟩
        exact h_tendsto_t
      · rcases hP_T' t' ht'_T' with ⟨u_t', hu_t'_memLp, h_tendsto_t'⟩
        refine ⟨u_t', hu_t'_memLp, ?_⟩
        exact tendsto_eLpNorm_diff_comp (I := I) (M := M) g r s t'.1.1 t'.2.1 t'.2.2
          h_tendsto_t' hσ_t_mono

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diagonal_extraction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.diagonal_extraction target :: scope.openDecls } }

theorem tensorChartComponent_rellich_extraction_of_uniform_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∃ u_lim : M → ℝ,
          MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          Filter.Tendsto
            (fun j => _root_.MeasureTheory.eLpNorm
                (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
                2 (riemannianVolumeMeasure (I := I) (M := M) g))
            Filter.atTop (𝓝 0) := by
  classical
  obtain ⟨φ, hφ_mono, hP⟩ :=
    diagonal_extraction (I := I) (M := M) g r s (S := S) (R := R) hu_bdd
      (tripleFinset (I := I) (M := M) r s)
  refine ⟨φ, hφ_mono, ?_⟩
  intro α hα Idx Jdx
  have hmem : (⟨⟨α, hα⟩, Idx, Jdx⟩ : Triple (I := I) (M := M) r s) ∈
      tripleFinset (I := I) (M := M) r s :=
    Finset.mem_univ _
  rcases hP ⟨⟨α, hα⟩, Idx, Jdx⟩ hmem with ⟨u_lim, hu_lim_memLp, h_tendsto⟩
  exact ⟨u_lim, hu_lim_memLp, h_tendsto⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_of_uniform_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_of_uniform_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_of_uniform_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_of_uniform_bound

theorem tensorChartComponent_rellich_extraction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∃ u_lim : M → ℝ,
          MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          Filter.Tendsto
            (fun j => _root_.MeasureTheory.eLpNorm
                (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
                2 (riemannianVolumeMeasure (I := I) (M := M) g))
            Filter.atTop (𝓝 0) :=
  tensorChartComponent_rellich_extraction_of_uniform_bound
    (I := I) (M := M) g r s (S := S) (R := R) hu_bdd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction

theorem tensorChartComponent_rellich_extraction_restricted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {S : ℕ → SmoothCcTensorH1 g r s}
    {R : ℝ}
    (hu_bdd : ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)) (n : ℕ),
      wkpNormChart (I := I) (M := M) 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s (S n).toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ chartAtlasPOUFinset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ∃ u_lim : M → ℝ,
          MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          Filter.Tendsto
            (fun j => _root_.MeasureTheory.eLpNorm
                (fun b => tensorChartComponentScalar (I := I) (M := M)
                  g r s (S (φ j)).toCcTensor α Idx Jdx b - u_lim b)
                2 (riemannianVolumeMeasure (I := I) (M := M) g))
            Filter.atTop (𝓝 0) := by
  classical
  suffices hgoal :
      ∀ T : Finset (Triple (I := I) (M := M) r s),
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ t ∈ T, ∃ u_lim : M → ℝ,
            MemLp u_lim 2 (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            Filter.Tendsto
              (fun j => _root_.MeasureTheory.eLpNorm
                  (fun b => tensorChartComponentScalar (I := I) (M := M)
                    g r s (S (φ j)).toCcTensor t.1.1 t.2.1 t.2.2 b - u_lim b)
                  2 (riemannianVolumeMeasure (I := I) (M := M) g))
              Filter.atTop (𝓝 0) by
    obtain ⟨φ, hφ_mono, hP_T⟩ := hgoal (tripleFinset (I := I) (M := M) r s)
    refine ⟨φ, hφ_mono, ?_⟩
    intro α hα Idx Jdx
    have hmem : (⟨⟨α, hα⟩, Idx, Jdx⟩ : Triple (I := I) (M := M) r s) ∈
        tripleFinset (I := I) (M := M) r s :=
      Finset.mem_univ _
    rcases hP_T ⟨⟨α, hα⟩, Idx, Jdx⟩ hmem with ⟨u_lim, hu_lim_memLp, h_tendsto⟩
    exact ⟨u_lim, hu_lim_memLp, h_tendsto⟩
  intro T
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, fun t ht => ?_⟩
      exact absurd ht (Finset.notMem_empty t)
  | insert t T' ht_notin ih =>
      rcases ih with ⟨φ_T', hφ_T'_mono, hP_T'⟩
      have hu_bdd_comp : ∀ n,
          wkpNormChart (I := I) (M := M) 1 2
              (tensorChartComponentScalar (I := I) (M := M)
                g r s (S (φ_T' n)).toCcTensor t.1.1 t.2.1 t.2.2) ≤
            ENNReal.ofReal R := fun n =>
        hu_bdd t.1.1 t.1.2 t.2.1 t.2.2 (φ_T' n)
      obtain ⟨σ_t, hσ_t_mono, u_t, hu_t_memLp, h_tendsto_t⟩ :=
        single_triple_extraction (I := I) (M := M) g r s t.1.1 t.2.1 t.2.2
          (S := fun n => S (φ_T' n))
          (R := R) hu_bdd_comp
      refine ⟨φ_T' ∘ σ_t, hφ_T'_mono.comp hσ_t_mono, ?_⟩
      intro t' ht'
      rcases Finset.mem_insert.mp ht' with rfl | ht'_T'
      · exact ⟨u_t, hu_t_memLp, h_tendsto_t⟩
      · rcases hP_T' t' ht'_T' with ⟨u_t', hu_t'_memLp, h_tendsto_t'⟩
        refine ⟨u_t', hu_t'_memLp, ?_⟩
        exact tendsto_eLpNorm_diff_comp (I := I) (M := M) g r s t'.1.1 t'.2.1 t'.2.2
          h_tendsto_t' hσ_t_mono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_restricted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_restricted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_restricted ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_rellich_extraction_restricted

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
