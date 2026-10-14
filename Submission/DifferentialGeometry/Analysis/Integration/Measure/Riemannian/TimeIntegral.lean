import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityContinuity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {T : Type*} [MeasurableSpace T]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem aestronglyMeasurable_integral_riemannianVolumeMeasure
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : _root_.MeasureTheory.Measure T) {f : T × M → V}
    (hf : _root_.MeasureTheory.AEStronglyMeasurable
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2 • f z)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ := by
  let : _root_.MeasureTheory.SigmaFinite (riemannianVolumeMeasure (I := I) (M := M) q) :=
    riemannianVolumeMeasure_sigmaFinite q
  have heq (t : T) :=
    integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t)
      (fun x => f (t, x))
  exact hf.integral_prod_right'.congr (Filter.Eventually.of_forall fun t => (heq t).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure ``Submission.DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure


theorem aestronglyMeasurable_integral_riemannianVolumeMeasure_of_continuous_chartGram
    [TopologicalSpace T] [OpensMeasurableSpace T]
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : _root_.MeasureTheory.Measure T) {f : T × M → V}
    (hgram : ∀ (alpha : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun z : T × M =>
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g z.1) alpha z.2 i j)
        (_root_.Set.univ ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).baseSet))
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have hrho : Continuous
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2) := by
    rw [← continuousOn_univ]
    simpa only [_root_.Set.univ_prod_univ] using
      riemannianVolumeDensity_family_continuousOn q g hgram
  exact aestronglyMeasurable_integral_riemannianVolumeMeasure q g μ
    (hrho.aestronglyMeasurable.smul hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure_of_continuous_chartGram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure_of_continuous_chartGram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure_of_continuous_chartGram ``Submission.DifferentialGeometry.Integral.Measure.aestronglyMeasurable_integral_riemannianVolumeMeasure_of_continuous_chartGram

theorem integrable_integral_riemannianVolumeMeasure_of_integral_norm_le
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : _root_.MeasureTheory.Measure T) {f : T × M → V}
    (hf : _root_.MeasureTheory.AEStronglyMeasurable
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2 • f z)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {B : T → ℝ} (hB : _root_.MeasureTheory.Integrable B μ)
    (hbound : ∀ᵐ t ∂μ,
      (∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ B t) :
    _root_.MeasureTheory.Integrable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ ∧
      ‖∫ t, ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ‖ ≤
        ∫ t, B t ∂μ := by
  have hnorm : ∀ᵐ t ∂μ,
      ‖∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)‖ ≤ B t := by
    filter_upwards [hbound] with t ht
    exact (_root_.MeasureTheory.norm_integral_le_integral_norm _).trans ht
  exact ⟨hB.mono' (aestronglyMeasurable_integral_riemannianVolumeMeasure q g μ hf) hnorm,
    _root_.MeasureTheory.norm_integral_le_of_norm_le hB hnorm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_integral_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_integral_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_integral_norm_le ``Submission.DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_integral_norm_le

theorem integrable_integral_riemannianVolumeMeasure_of_uniform_integral_norm_bound
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : _root_.MeasureTheory.Measure T) [_root_.MeasureTheory.IsFiniteMeasure μ] {f : T × M → V}
    (hf : _root_.MeasureTheory.AEStronglyMeasurable
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2 • f z)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {C : ℝ} (hbound : ∀ᵐ t ∂μ,
      (∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ C) :
    _root_.MeasureTheory.Integrable
      (fun t => ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ ∧
      ‖∫ t, ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ‖ ≤
        C * μ.real univ := by
  obtain ⟨hi, hb⟩ := integrable_integral_riemannianVolumeMeasure_of_integral_norm_le
    q g μ hf (_root_.MeasureTheory.integrable_const C) hbound
  exact ⟨hi, by simpa only [_root_.MeasureTheory.integral_const, smul_eq_mul, mul_comm] using hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_uniform_integral_norm_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_uniform_integral_norm_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_uniform_integral_norm_bound ``Submission.DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure_of_uniform_integral_norm_bound

end DifferentialGeometry.Integral.Measure
