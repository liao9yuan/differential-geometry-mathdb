import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Integral.Measure

noncomputable section

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

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

private theorem sqrt_pow (c : Real) (hc : 0 ≤ c) (n : Nat) :
    Real.sqrt (c ^ n) = Real.sqrt c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hc n), ih, pow_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.sqrt_pow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.sqrt_pow target :: scope.openDecls } }

theorem chartGram_scale (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (scaleMetric (I := I) c hc g) x₀ x =
      c • DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g x₀ x := by
  ext i j
  simp [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, scaleMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartGram_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartGram_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartGram_scale ``Submission.DifferentialGeometry.Integral.Measure.chartGram_scale

theorem chartDensity_scale (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x₀ x : M) :
    chartDensity (scaleMetric (I := I) c hc g) x₀ x =
      Real.sqrt (c ^ Module.finrank Real E) * chartDensity g x₀ x := by
  unfold chartDensity
  rw [chartGram_scale (I := I) c hc g x₀ x, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_mul (pow_nonneg hc.le _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartDensity_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartDensity_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartDensity_scale ``Submission.DifferentialGeometry.Integral.Measure.chartDensity_scale

theorem chartLocal_scale (c : Real) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) (scaleMetric (I := I) c hc g) x₀ =
      ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E)) •
        chartLocalMeasure (I := I) g x₀ := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E))
  have hdensity :
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity (scaleMetric (I := I) c hc g) x₀
            ((extChartAt I x₀).symm y))) =
        a • fun y : E =>
          ENNReal.ofReal (chartDensity g x₀ ((extChartAt I x₀).symm y)) := by
    funext y
    rw [chartDensity_scale (I := I) c hc]
    simp only [a, Pi.smul_apply, smul_eq_mul]
    exact ENNReal.ofReal_mul (Real.sqrt_nonneg _)
  have ha : a ≠ (∞ : ℝ≥0∞) := by simp [a]
  unfold chartLocalMeasure
  rw [hdensity, _root_.MeasureTheory.withDensity_smul' a _ ha, Measure.map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chartLocal_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chartLocal_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chartLocal_scale ``Submission.DifferentialGeometry.Integral.Measure.chartLocal_scale

theorem riemMeasure_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (rho : SmoothPartitionOfUnity M I M Set.univ) :
    riemannianMeasure (I := I) (scaleMetric (I := I) c hc g) rho =
      ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E)) •
        riemannianMeasure (I := I) g rho := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (c ^ Module.finrank Real E))
  unfold riemannianMeasure
  have hterm :
      (fun alpha : M =>
        (chartLocalMeasure (I := I) (scaleMetric (I := I) c hc g) alpha).withDensity
          (fun x : M => ENNReal.ofReal (rho alpha x))) =
        fun alpha : M => a •
          (chartLocalMeasure (I := I) g alpha).withDensity
            (fun x : M => ENNReal.ofReal (rho alpha x)) := by
    funext alpha
    rw [chartLocal_scale (I := I) c hc]
    exact _root_.MeasureTheory.withDensity_smul_measure _ _
  rw [hterm]
  refine Measure.ext fun s hs => ?_
  rw [Measure.sum_apply _ hs, Measure.smul_apply, Measure.sum_apply _ hs]
  exact ENNReal.tsum_const_smul a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemMeasure_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemMeasure_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemMeasure_scale ``Submission.DifferentialGeometry.Integral.Measure.riemMeasure_scale

theorem volume_scaleMetric [T2Space M] [SigmaCompactSpace M]
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M)
        (scaleMetric (I := I) c hc g) =
      ENNReal.ofReal (Real.sqrt c) ^ Module.finrank Real E •
        riemannianVolumeMeasure (I := I) (M := M) g := by
  rw [riemannianVolumeMeasure_def, riemannianVolumeMeasure_def]
  simpa only [sqrt_pow c hc.le,
    ENNReal.ofReal_pow (Real.sqrt_nonneg c)] using
    riemMeasure_scale (I := I) (M := M) c hc g (chartAtlasPOU I M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volume_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volume_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volume_scaleMetric ``Submission.DifferentialGeometry.Integral.Measure.volume_scaleMetric

theorem volume_scale_apply [T2Space M] [SigmaCompactSpace M]
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M) (s : Set M) :
    riemannianVolumeMeasure (I := I) (M := M)
        (scaleMetric (I := I) c hc g) s =
      ENNReal.ofReal (Real.sqrt c) ^ Module.finrank Real E *
        riemannianVolumeMeasure (I := I) (M := M) g s := by
  have h := congrArg (fun mu : _root_.MeasureTheory.Measure M => mu s)
    (volume_scaleMetric (I := I) (M := M) c hc g)
  simpa only [Measure.smul_apply, smul_eq_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volume_scale_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volume_scale_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volume_scale_apply ``Submission.DifferentialGeometry.Integral.Measure.volume_scale_apply

end

end DifferentialGeometry.Integral.Measure
