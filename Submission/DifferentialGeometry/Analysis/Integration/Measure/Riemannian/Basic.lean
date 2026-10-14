import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable (I M) in
def chartAtlasPOU [T2Space M] [SigmaCompactSpace M] :
    SmoothPartitionOfUnity M I M univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartAtlasPOU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartAtlasPOU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartAtlasPOU ``Submission.DifferentialGeometry.Integral.Measure.chartAtlasPOU

variable (I M) in
lemma chartAtlasPOU_isSubordinate [T2Space M] [SigmaCompactSpace M] :
    (chartAtlasPOU I M).IsSubordinate (fun x : M => (chartAt H x).source) :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate ``Submission.DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate

def riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.sum fun α : M =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianMeasure ``Submission.DifferentialGeometry.Integral.Measure.riemannianMeasure

lemma riemannianMeasure_def
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ) :
    riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : M =>
        (chartLocalMeasure (I := I) g α).withDensity
          (fun x : M => ENNReal.ofReal (ρ α x))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianMeasure_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianMeasure_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianMeasure_def ``Submission.DifferentialGeometry.Integral.Measure.riemannianMeasure_def

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma measurable_ofReal_pou_weight
    (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ) (α : M) :
    Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
  have hcont : Continuous (fun x : M => ρ α x) :=
    (ρ α).contMDiff.continuous
  exact ENNReal.measurable_ofReal.comp hcont.measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.measurable_ofReal_pou_weight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.measurable_ofReal_pou_weight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.measurable_ofReal_pou_weight ``Submission.DifferentialGeometry.Integral.Measure.measurable_ofReal_pou_weight

theorem riemannianMeasure_lintegral_eq
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(riemannianMeasure (I := I) g ρ) =
      ∑' α : M, ∫⁻ x, ENNReal.ofReal (ρ α x) * f x
          ∂(chartLocalMeasure (I := I) g α) := by
  classical
  rw [riemannianMeasure_def, _root_.MeasureTheory.lintegral_sum_measure]
  refine tsum_congr (fun α => ?_)
  have hρ : Measurable (fun x : M => ENNReal.ofReal (ρ α x)) := by
    have hcont : Continuous (fun x : M => ρ α x) := (ρ α).contMDiff.continuous
    exact ENNReal.measurable_ofReal.comp hcont.measurable
  have h :=
    lintegral_withDensity_eq_lintegral_mul (μ := chartLocalMeasure (I := I) g α)
      (f := fun x : M => ENNReal.ofReal (ρ α x)) hρ (g := f) hf
  simpa [Pi.mul_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_eq ``Submission.DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_eq

theorem riemannianMeasure_lintegral_finset_le
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ)
    {f : M → ℝ≥0∞} (hf : Measurable f) (s : Finset M) :
    ∑ α ∈ s, ∫⁻ x, ENNReal.ofReal (ρ α x) * f x
        ∂(chartLocalMeasure (I := I) g α)
      ≤ ∫⁻ x, f x ∂(riemannianMeasure (I := I) g ρ) := by
  rw [riemannianMeasure_lintegral_eq (I := I) g ρ hf]
  exact ENNReal.sum_le_tsum s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_finset_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_finset_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_finset_le ``Submission.DifferentialGeometry.Integral.Measure.riemannianMeasure_lintegral_finset_le

theorem chartLocalMeasure_withDensity_le_riemannianMeasure
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ) (α : M) :
    (chartLocalMeasure (I := I) g α).withDensity
        (fun x : M => ENNReal.ofReal (ρ α x))
      ≤ riemannianMeasure (I := I) g ρ := by
  rw [riemannianMeasure_def]
  exact MeasureTheory.Measure.le_sum _ α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartLocalMeasure_withDensity_le_riemannianMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartLocalMeasure_withDensity_le_riemannianMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartLocalMeasure_withDensity_le_riemannianMeasure ``Submission.DifferentialGeometry.Integral.Measure.chartLocalMeasure_withDensity_le_riemannianMeasure

end Measure
end Integral
end DifferentialGeometry
