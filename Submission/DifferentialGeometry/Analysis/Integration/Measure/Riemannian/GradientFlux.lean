import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.TimeIntegral
import Submission.DifferentialGeometry.Analysis.Integration.Measure.GradientPairingFamily

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]

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

theorem integrable_integral_mul_inner_gradientFun_family
    (q : SmoothRiemannianMetric I M) (g : T → SmoothRiemannianMetric I M)
    (μ : _root_.MeasureTheory.Measure T) (f h : T → M → ℝ) (w : T × M → ℝ)
    (hf : Continuous (Function.uncurry f)) (hh : Continuous (Function.uncurry h))
    (hgram : ∀ (alpha : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun z : T × M => chartGramMatrix (g z.1) alpha z.2 i j)
        (_root_.Set.univ ×ˢ (chartAt H alpha).source))
    (hw : _root_.MeasureTheory.AEStronglyMeasurable w
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {B : T → ℝ} (hB : _root_.MeasureTheory.Integrable B μ)
    (hbound : ∀ᵐ t ∂μ,
      (∫ x, |w (t, x) * (g t).inner x
        (gradientFun (g t) (f t) x) (gradientFun (g t) (h t) x)|
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ B t) :
    _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) * (g t).inner x
      (gradientFun (g t) (f t) x) (gradientFun (g t) (h t) x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ ∧
      |∫ t, ∫ x, w (t, x) * (g t).inner x
        (gradientFun (g t) (f t) x) (gradientFun (g t) (h t) x)
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ| ≤ ∫ t, B t ∂μ := by
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have hrho : Continuous
      (fun z : T × M => riemannianVolumeDensity q (g z.1) z.2) := by
    rw [← continuousOn_univ]
    simpa only [_root_.Set.univ_prod_univ, trivializationAt_baseSet_eq_chartAt_source] using
      riemannianVolumeDensity_family_continuousOn q g (J := (_root_.Set.univ : Set T))
        (fun alpha i j => by
          simpa only [trivializationAt_baseSet_eq_chartAt_source] using hgram alpha i j)
  have hpair := measurable_inner_gradientFun_family g f h hf hh hgram
  have hflux := hw.mul hpair.aestronglyMeasurable
  simpa only [Real.norm_eq_abs, Pi.mul_apply] using
    integrable_integral_riemannianVolumeMeasure_of_integral_norm_le q g μ
      (hrho.aestronglyMeasurable.smul hflux) hB hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_integral_mul_inner_gradientFun_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_integral_mul_inner_gradientFun_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_integral_mul_inner_gradientFun_family ``Submission.DifferentialGeometry.Integral.Measure.integrable_integral_mul_inner_gradientFun_family

end DifferentialGeometry.Integral.Measure
