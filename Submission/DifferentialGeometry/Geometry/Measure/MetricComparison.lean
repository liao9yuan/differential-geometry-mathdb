import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.MeasureTheory _root_.Bundle
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology
namespace DifferentialGeometry.Geometry.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem riemannianVolumeMeasure_apply_le_of_inner_le
    (g h : SmoothRiemannianMetric I M) {C : ℝ} (hC : 0 < C)
    {S : Set M} (hS : MeasurableSet S)
    (hcomp : ∀ x ∈ S, ∀ v : TangentSpace I x, h.inner x v v ≤ C * g.inner x v v) :
    riemannianVolumeMeasure I M h S ≤
      ENNReal.ofReal (Real.sqrt (C ^ Module.finrank ℝ E)) * riemannianVolumeMeasure I M g S := by
  let F : M → ℝ≥0∞ := S.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS
  let R : ℝ := Real.sqrt (C ^ Module.finrank ℝ E)
  have hlocal (α : M) :
      ∫⁻ x, ENNReal.ofReal (chartAtlasPOU I M α x) * F x ∂chartLocalMeasure h α ≤
        ENNReal.ofReal R *
          ∫⁻ x, ENNReal.ofReal (chartAtlasPOU I M α x) * F x ∂chartLocalMeasure g α := by
    have hm : Measurable (fun x => ENNReal.ofReal (chartAtlasPOU I M α x) * F x) :=
      (measurable_ofReal_pou_weight (chartAtlasPOU I M) α).mul hF
    rw [chartLocalMeasure_lintegral h α hm, chartLocalMeasure_lintegral g α hm,
      ← _root_.MeasureTheory.lintegral_const_mul' (ENNReal.ofReal R) _ ENNReal.ofReal_ne_top]
    apply _root_.MeasureTheory.lintegral_mono
    intro y
    let x := (extChartAt I α).symm y
    by_cases hx : x ∈ S
    · by_cases hρ : chartAtlasPOU I M α x = 0
      · change _ * (ENNReal.ofReal (chartAtlasPOU I M α x) * F x) ≤
          _ * (_ * (ENNReal.ofReal (chartAtlasPOU I M α x) * F x))
        simp only [hρ, ENNReal.ofReal_zero, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero, le_refl]
      · have hbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
          rw [trivializationAt_baseSet_eq_chartAt_source]
          exact chartAtlasPOU_isSubordinate I M α (subset_tsupport _ hρ)
        have hd := ENNReal.ofReal_le_ofReal (chartDensity_le g h hC α hbase (hcomp x hx))
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hd
        change ENNReal.ofReal (chartDensity h α x) *
          (ENNReal.ofReal (chartAtlasPOU I M α x) * F x) ≤
          ENNReal.ofReal R * (ENNReal.ofReal (chartDensity g α x) *
            (ENNReal.ofReal (chartAtlasPOU I M α x) * F x))
        calc
          _ ≤ (ENNReal.ofReal R * ENNReal.ofReal (chartDensity g α x)) *
              (ENNReal.ofReal (chartAtlasPOU I M α x) * F x) := mul_le_mul' hd le_rfl
          _ = _ := mul_assoc _ _ _
    · have hz : F x = 0 := _root_.Set.indicator_of_notMem hx _
      change _ * (_ * F x) ≤ _ * (_ * (_ * F x))
      simp [hz]
  rw [← _root_.MeasureTheory.lintegral_indicator_one hS, ← _root_.MeasureTheory.lintegral_indicator_one hS]
  change (∫⁻ x, F x ∂riemannianVolumeMeasure I M h) ≤
    ENNReal.ofReal R * ∫⁻ x, F x ∂riemannianVolumeMeasure I M g
  rw [riemannianVolumeMeasure_def, riemannianVolumeMeasure_def,
    riemannianMeasure_lintegral_eq h _ hF, riemannianMeasure_lintegral_eq g _ hF]
  exact (ENNReal.tsum_le_tsum hlocal).trans_eq ENNReal.tsum_mul_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le

end DifferentialGeometry.Geometry.Measure
