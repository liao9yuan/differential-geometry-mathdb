import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich.Compactness

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
namespace Parabolic
namespace TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

private lemma abs_pou_mul_le_abs
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) (x : M) :
    |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| ≤ |u x| := by
  rw [abs_mul]
  have hρ_nn : 0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α x
  have hρ_le : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α x
  have hρ_abs_le_one : |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| ≤ 1 := by
    rw [abs_of_nonneg hρ_nn]; exact hρ_le
  calc |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| * |u x|
      ≤ 1 * |u x| := by
        gcongr
    _ = |u x| := one_mul _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_pou_mul_le_abs
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.abs_pou_mul_le_abs target :: scope.openDecls } }

theorem eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M)
    (u : M → ℝ) (hu_meas : Measurable u) :
    ∃ C : ℝ, 0 ≤ C ∧
      _root_.MeasureTheory.eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) 2
          ((MeasureTheory.volume :
              _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)) ≤
        ENNReal.ofReal C *
          _root_.MeasureTheory.eLpNorm u 2
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  refine ⟨C, hC_pos.le, ?_⟩
  set f : M → ℝ := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x with hf_def
  have hρ_cont : Continuous ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (ρ.contMDiff).continuous
  have hf_meas : Measurable f := hρ_cont.measurable.mul hu_meas
  have hf_support : tsupport f ⊆ Kα := by
    have h_eq : f = (fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • u x) := by
      funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_raw_bound :=
    hC_bound (u := f) hf_meas hf_support
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g from rfl]
    at h_raw_bound
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
      (I := I) (M := M)
      (ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      α u
  rw [_root_.MeasureTheory.eLpNorm_congr_ae h_ae]
  refine h_raw_bound.trans ?_
  gcongr
  refine _root_.MeasureTheory.eLpNorm_mono (f := f) (g := u) ?_
  intro x
  have h_norm_f : ‖f x‖ = |((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| := Real.norm_eq_abs _
  have h_norm_u : ‖u x‖ = |u x| := Real.norm_eq_abs _
  rw [h_norm_f, h_norm_u]
  exact abs_pou_mul_le_abs (I := I) (M := M) α u x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
