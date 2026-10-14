import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Metric
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Defs
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic

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
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
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


abbrev metricFamilyForMeasure
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real) :
    Real → SmoothRiemannianMetric I M :=
  fun t => G.metric t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.metricFamilyForMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.metricFamilyForMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.metricFamilyForMeasure ``Submission.DifferentialGeometry.Integral.Measure.metricFamilyForMeasure


abbrev metricFamilyForMeasureOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D) :
    Real → SmoothRiemannianMetric I M :=
  fun t => G.metric t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.metricFamilyForMeasureOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.metricFamilyForMeasureOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.metricFamilyForMeasureOn ``Submission.DifferentialGeometry.Integral.Measure.metricFamilyForMeasureOn


abbrev volumeMeasureFamily [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasure (I := I) (M := M) G)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureFamily ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureFamily

@[simp]
theorem volumeMeasureFamily_eq [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
      (t : Real) :
    volumeMeasureFamily (I := I) (M := M) G t =
      Measure.volumeMeasureAt (I := I) (M := M) G t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureFamily_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureFamily_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureFamily_eq ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureFamily_eq


abbrev volumeMeasureFamilyOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasureOn (I := I) (M := M) G)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn

@[simp]
theorem volumeMeasureFamilyOn_eq [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
      (t : Real) :
    volumeMeasureFamilyOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M)
        (G.metric t) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq

@[simp]
theorem volumeMeasureFamilyOn_eq_volumeMeasureOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
    volumeMeasureFamilyOn (I := I) (M := M) G (t : Real) =
      Measure.volumeMeasureOn (I := I) (M := M) G t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq_volumeMeasureOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq_volumeMeasureOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq_volumeMeasureOn ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureFamilyOn_eq_volumeMeasureOn


abbrev traceTimeDerivMetricAt
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
      (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt ``Submission.DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt

@[simp]
theorem traceTimeDerivMetricAt_eq
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
      (t : Real) (x : M) :
    traceTimeDerivMetricAt (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt_eq ``Submission.DifferentialGeometry.Integral.Measure.traceTimeDerivMetricAt_eq


abbrev traceTimeDerivMetricOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
      (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn ``Submission.DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn

@[simp]
theorem traceTimeDerivMetricOn_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
      (t : Real) (x : M) :
    traceTimeDerivMetricOn (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn_eq ``Submission.DifferentialGeometry.Integral.Measure.traceTimeDerivMetricOn_eq

theorem volume_variation_formula
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ := by
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  have hf_cont : ∀ᶠ s in 𝓝 t₀, Continuous (f s) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have hft₀_cont : Continuous (f t₀) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t₀, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t₀) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t₀, x))) :=
      hf.continuous_deriv_joint.comp (continuous_const.prodMk continuous_id)
    exact this
  have hh_cont : Continuous (fun x : M =>
      deriv (fun s : ℝ => f s x) t₀ +
      (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x) := by
    refine Continuous.add h_deriv_cont ?_
    refine Continuous.mul ?_ hft₀_cont
    refine Continuous.mul continuous_const ?_
    exact traceTimeDerivMetric_continuous (I := I) (M := M) hg
  refine volume_variation_formula_of_chart_derivs
    (I := I) (M := M) g_fam f t₀ hf_cont hh_cont ?_
  intro α hα
  exact per_chart_hasDerivAt (I := I) (M := M) hg hf α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volume_variation_formula then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volume_variation_formula"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volume_variation_formula ``Submission.DifferentialGeometry.Integral.Measure.volume_variation_formula


theorem volume_variation_formula_at
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamily, traceTimeDerivMetricAt] using
    (volume_variation_formula (I := I) (M := M)
      (g_fam := metricFamilyForMeasure (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volume_variation_formula_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volume_variation_formula_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volume_variation_formula_at ``Submission.DifferentialGeometry.Integral.Measure.volume_variation_formula_at

theorem volume_variation_formula_on
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamilyOn (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricOn (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamilyOn, traceTimeDerivMetricOn] using
    (volume_variation_formula (I := I) (M := M)
      (g_fam := metricFamilyForMeasureOn (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volume_variation_formula_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volume_variation_formula_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volume_variation_formula_on ``Submission.DifferentialGeometry.Integral.Measure.volume_variation_formula_on

end


end DifferentialGeometry.Integral.Measure
