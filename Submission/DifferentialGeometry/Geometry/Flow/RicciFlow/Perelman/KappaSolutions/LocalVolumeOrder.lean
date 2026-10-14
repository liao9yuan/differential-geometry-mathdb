import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance localVolumeOrderModelMeasurable : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderModelMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderModelMeasurable target :: scope.openDecls } }
private local instance localVolumeOrderModelBorel : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderModelBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderModelBorel target :: scope.openDecls } }
private local instance localVolumeOrderMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderMeasurable target :: scope.openDecls } }
private local instance localVolumeOrderBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrderBorel target :: scope.openDecls } }

private theorem localVolumeOrder_chart_lintegral_le
    (g h : SmoothRiemannianMetric I M) (alpha : M) {U : Set M}
    {Q : ℝ} (hQ : 0 < Q)
    (hcomp : ∀ x ∈ U, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hvanish : ∀ x : M, x ∉ U → F x = 0) :
    ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
        ∂(chartLocalMeasure (I := I) h alpha) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) g alpha) := by
  let rho : M → ℝ := fun x => (chartAtlasPOU I M alpha : M → ℝ) x
  have hrho : Measurable (fun x : M => ENNReal.ofReal (rho x)) :=
    ENNReal.measurable_ofReal.comp
      (chartAtlasPOU I M alpha).contMDiff.continuous.measurable
  have hprod : Measurable (fun x : M => ENNReal.ofReal (rho x) * F x) := hrho.mul hF
  rw [chartLocalMeasure_lintegral (I := I) h alpha hprod,
    chartLocalMeasure_lintegral (I := I) g alpha hprod]
  let target : Set E := (extChartAt I alpha).target
  let symm : E → M := fun y => (extChartAt I alpha).symm y
  calc
    ∫⁻ y in target,
        ENNReal.ofReal (chartDensity (I := I) h alpha (symm y)) *
          (ENNReal.ofReal (rho (symm y)) * F (symm y))
        ∂(modelHaar (E := E)) ≤
      ∫⁻ y in target, ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        (ENNReal.ofReal (chartDensity (I := I) g alpha (symm y)) *
          (ENNReal.ofReal (rho (symm y)) * F (symm y)))
        ∂(modelHaar (E := E)) := by
      refine _root_.MeasureTheory.lintegral_mono fun y => ?_
      by_cases hx : symm y ∈ U
      · by_cases hzero : rho (symm y) = 0
        · simp only [hzero, ENNReal.ofReal_zero, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero, le_refl]
        · have hsupport : symm y ∈ tsupport rho := subset_tsupport rho hzero
          have hbase : symm y ∈
              (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).baseSet := by
            rw [trivializationAt_baseSet_eq_chartAt_source]
            exact (chartAtlasPOU_isSubordinate I M) alpha hsupport
          have hd := chartDensity_le (I := I) g h hQ alpha hbase (hcomp (symm y) hx)
          have hdensity :
              ENNReal.ofReal (chartDensity (I := I) h alpha (symm y)) ≤
                ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
                  ENNReal.ofReal (chartDensity (I := I) g alpha (symm y)) := by
            have hbound := ENNReal.ofReal_le_ofReal hd
            rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hbound
            exact hbound
          have hmul := mul_le_mul_left hdensity
            (ENNReal.ofReal (rho (symm y)) * F (symm y))
          simpa only [mul_assoc] using hmul
      · simp only [hvanish (symm y) hx, _root_.MulZeroClass.mul_zero, le_refl]
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∫⁻ y in target,
          ENNReal.ofReal (chartDensity (I := I) g alpha (symm y)) *
            (ENNReal.ofReal (rho (symm y)) * F (symm y))
          ∂(modelHaar (E := E)) := by
      rw [_root_.MeasureTheory.lintegral_const_mul'
        (μ := (modelHaar (E := E)).restrict target)
        (ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E))) _ ENNReal.ofReal_ne_top]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrder_chart_lintegral_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrder_chart_lintegral_le target :: scope.openDecls } }

private theorem localVolumeOrder_lintegral_le
    (g h : SmoothRiemannianMetric I M) {U : Set M} {Q : ℝ} (hQ : 0 < Q)
    (hcomp : ∀ x ∈ U, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v)
    {F : M → ℝ≥0∞} (hF : Measurable F)
    (hvanish : ∀ x : M, x ∉ U → F x = 0) :
    (∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) h)) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  change (∫⁻ x, F x ∂riemannianMeasure (I := I) h (chartAtlasPOU I M)) ≤
    ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
      ∫⁻ x, F x ∂riemannianMeasure (I := I) g (chartAtlasPOU I M)
  rw [riemannianMeasure_lintegral_eq (I := I) h (chartAtlasPOU I M) hF,
    riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF]
  calc
    (∑' alpha : M, ∫⁻ x,
        ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) h alpha)) ≤
      ∑' alpha : M, ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∫⁻ x, ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
          ∂(chartLocalMeasure (I := I) g alpha) := by
      exact ENNReal.tsum_le_tsum fun alpha =>
        localVolumeOrder_chart_lintegral_le g h alpha hQ hcomp hF hvanish
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        ∑' alpha : M, ∫⁻ x,
          ENNReal.ofReal ((chartAtlasPOU I M alpha : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) g alpha) := ENNReal.tsum_mul_left

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrder_lintegral_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.localVolumeOrder_lintegral_le target :: scope.openDecls } }

theorem riemannianVolumeMeasure_le_on
    (g h : SmoothRiemannianMetric I M) {U : Set M} (hU : MeasurableSet U)
    {Q : ℝ} (hQ : 0 < Q)
    (hcomp : ∀ x ∈ U, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    riemannianVolumeMeasure (I := I) (M := M) h U ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := M) g U := by
  classical
  have hvanish : ∀ x : M, x ∉ U → U.indicator (1 : M → ℝ≥0∞) x = 0 :=
    fun x hx => Set.indicator_of_notMem hx _
  have hbound := localVolumeOrder_lintegral_le g h hQ hcomp
    (F := U.indicator (1 : M → ℝ≥0∞))
    (measurable_const.indicator hU) hvanish
  rw [_root_.MeasureTheory.lintegral_indicator_one hU, _root_.MeasureTheory.lintegral_indicator_one hU] at hbound
  exact hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on

theorem riemannianVolumeMeasure_restrict_le_of_inner_le_on
    (g h : SmoothRiemannianMetric I M) {U : Set M} (hU : MeasurableSet U)
    {Q : ℝ} (hQ : 0 < Q)
    (hcomp : ∀ x ∈ U, ∀ v : TangentSpace I x,
      h.inner x v v ≤ Q * g.inner x v v) :
    (riemannianVolumeMeasure (I := I) (M := M) h).restrict U ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) •
        (riemannianVolumeMeasure (I := I) (M := M) g).restrict U := by
  rw [Measure.le_iff]
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
  exact riemannianVolumeMeasure_le_on g h (hA.inter hU) hQ
    (fun x hx v => hcomp x hx.2 v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_restrict_le_of_inner_le_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_restrict_le_of_inner_le_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_restrict_le_of_inner_le_on ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_restrict_le_of_inner_le_on

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
