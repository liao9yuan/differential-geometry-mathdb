import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Approximation.Density.FirstOrder
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Subcritical
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Morrey.Basic
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.IntegrationByParts
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

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
namespace Equivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Equivalence.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

theorem eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, Measurable u →
        _root_.MeasureTheory.eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) 1 p u := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I) (M := M)
    with hS_def
  set ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M with hρ_def
  have h_bridge_α : ∀ α : M, ∃ C_α : ℝ, 0 < C_α ∧
      ∀ {u : M → ℝ}, Measurable u → tsupport u ⊆ tsupport (ρ α : M → ℝ) →
        _root_.MeasureTheory.eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ)
          ≤ ENNReal.ofReal C_α *
              _root_.MeasureTheory.eLpNorm
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) p
                ((_root_.MeasureTheory.MeasureSpace.volume :
                  _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                    (I := I) (M := M) α)) := by
    intro α
    set Kα : Set M := tsupport (ρ α : M → ℝ) with hKα_def
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    obtain ⟨C_α, hC_α_pos, hbound⟩ :=
      eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
        (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
    exact ⟨C_α, hC_α_pos, hbound⟩
  set Cα : M → ℝ := fun α => Classical.choose (h_bridge_α α) with hCα_def
  have hCα_pos : ∀ α : M, 0 < Cα α := fun α => (Classical.choose_spec (h_bridge_α α)).1
  have hCα_bound : ∀ α : M, ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ tsupport (ρ α : M → ℝ) →
      _root_.MeasureTheory.eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ)
        ≤ ENNReal.ofReal (Cα α) *
            _root_.MeasureTheory.eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) p
              ((_root_.MeasureTheory.MeasureSpace.volume :
                _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α)) := fun α =>
    (Classical.choose_spec (h_bridge_α α)).2
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => (hCα_pos α).le), ?_⟩
  intro u hu_meas
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I) (M := M) g]
  have h_eLpNorm_eq :
      _root_.MeasureTheory.eLpNorm u p (DifferentialGeometry.Integral.Measure.riemannianMeasure
          (I := I) g ρ) =
        _root_.MeasureTheory.eLpNorm (∑ α ∈ S, fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) := by
    refine _root_.MeasureTheory.eLpNorm_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S, (ρ α : M → ℝ) x * u x
    have hsum : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_eLpNorm_eq]
  have h_aesm : ∀ α ∈ S,
      _root_.MeasureTheory.AEStronglyMeasurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) := by
    intro α _
    have hcont : Continuous (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x) :=
      (ρ α).contMDiff.continuous
    exact (hcont.measurable.mul hu_meas).aestronglyMeasurable
  refine (_root_.MeasureTheory.eLpNorm_sum_le h_aesm hp_one).trans ?_
  have h_per_α : ∀ α ∈ S,
      _root_.MeasureTheory.eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) ≤
      ENNReal.ofReal (Cα α) *
        wkpNormChart (I := I) (M := M) 1 p u := by
    intro α _
    have h_support : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
        tsupport (ρ α : M → ℝ) := by
      have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
    have h_meas : Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) :=
      (ρ α).contMDiff.continuous.measurable.mul hu_meas
    have h_bridge := hCα_bound α h_meas h_support
    refine h_bridge.trans ?_
    have h_ae :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
        (I := I) (M := M) ρ α u
    have h_eLpNorm_eq :
        _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
              (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
            ((_root_.MeasureTheory.MeasureSpace.volume :
              _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) =
          _root_.MeasureTheory.eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M) ρ α u) p
            ((_root_.MeasureTheory.MeasureSpace.volume :
              _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) :=
      _root_.MeasureTheory.eLpNorm_congr_ae h_ae.symm
    rw [h_eLpNorm_eq]
    have h1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_p_le_wkpNorm_one
        (I := I) (M := M) (p := p) u α
    gcongr
  refine (Finset.sum_le_sum h_per_α).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from ?_]
  refine (ENNReal.ofReal_sum_of_nonneg (fun α _ => (hCα_pos α).le)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform

theorem eLpNorm_le_const_mul_wkpNormChart_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        _root_.MeasureTheory.eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) 1 p u := by
  obtain ⟨C, hC_nn, hbound⟩ :=
    eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g hp_one hp_top
  refine ⟨C, hC_nn, ?_⟩
  intro u hu_smooth
  exact hbound hu_smooth.continuous.measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_le_const_mul_wkpNormChart_smooth_uniform then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_le_const_mul_wkpNormChart_smooth_uniform"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_le_const_mul_wkpNormChart_smooth_uniform ``Submission.DifferentialGeometry.Analysis.Sobolev.Equivalence.eLpNorm_le_const_mul_wkpNormChart_smooth_uniform

end Equivalence
end Sobolev
end Analysis
end DifferentialGeometry
