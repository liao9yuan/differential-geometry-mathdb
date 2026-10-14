import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeOrder
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

private theorem avrComparison_sqrt_pow (Q : ℝ) (hQ : 0 ≤ Q) (n : ℕ) :
    Real.sqrt (Q ^ n) = Real.sqrt Q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg hQ n), ih, pow_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparison_sqrt_pow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparison_sqrt_pow target :: scope.openDecls } }

private theorem avrComparison_denominator_tendsto_top (n : ℕ) (hn : n ≠ 0) :
    _root_.Filter.Tendsto (fun r : ℝ => euclideanUnitBallVolume n * ENNReal.ofReal (r ^ n))
      atTop (𝓝 (⊤ : ℝ≥0∞)) := by
  have hpow : _root_.Filter.Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ n))
      atTop (𝓝 (⊤ : ℝ≥0∞)) := by
    simpa only [Function.comp_def] using
      ENNReal.tendsto_ofReal_atTop.comp (_root_.Filter.tendsto_pow_atTop hn)
  have hmul := ENNReal.Tendsto.const_mul (a := euclideanUnitBallVolume n)
    hpow (Or.inl ENNReal.top_ne_zero)
  simpa only [ENNReal.mul_top (euclideanUnitBallVolume_pos n).ne'] using hmul

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparison_denominator_tendsto_top
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparison_denominator_tendsto_top target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance avrComparisonMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparisonMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparisonMeasurable target :: scope.openDecls } }
private local instance avrComparisonBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparisonBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparisonBorel target :: scope.openDecls } }

private theorem avrComparison_ballVolume_le_add
    (g h : SmoothRiemannianMetric I M) (p : M) {K : Set M} (hK : MeasurableSet K)
    {Q : ℝ} (hQ : 0 < Q)
    (hdist : ∀ x : M, riemannianEDistOf (I := I) h p x ≤
      riemannianEDistOf (I := I) g p x)
    (hmetric : ∀ x : M, x ∉ K → ∀ v : TangentSpace I x,
      Q * g.inner x v v ≤ h.inner x v v) (r : ℝ) :
    ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) ≤
      riemannianVolumeMeasure (I := I) (M := M) h (riemannianBallOf h p r) +
        ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
          riemannianVolumeMeasure (I := I) (M := M) g K := by
  let k : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E))
  let A : Set M := riemannianBallOf g p r \ K
  have hball : MeasurableSet (riemannianBallOf g p r) := by
    have hcont : Continuous (fun x : M => riemannianEDistOf (I := I) g p x) :=
      continuous_riemannianEDist (I := I) g p
    exact (isOpen_lt hcont continuous_const).measurableSet
  have hA : MeasurableSet A := hball.diff hK
  have hlocal := riemannianVolumeMeasure_le_on h (scaleMetric Q hQ g) hA
    (Q := 1) one_pos (fun x hx v => by
      simpa only [scaleMetric_inner, one_mul] using hmetric x hx.2 v)
  have hscale : riemannianVolumeMeasure (I := I) (M := M) (scaleMetric Q hQ g) A =
      k * riemannianVolumeMeasure (I := I) (M := M) g A := by
    rw [volume_scale_apply]
    dsimp only [k]
    rw [avrComparison_sqrt_pow Q hQ.le, ENNReal.ofReal_pow (Real.sqrt_nonneg Q)]
  rw [hscale] at hlocal
  simp only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hlocal
  have hAsubset : A ⊆ riemannianBallOf h p r := by
    intro x hx
    exact lt_of_le_of_lt (hdist x) hx.1
  have houtside : k * riemannianVolumeMeasure (I := I) (M := M) g A ≤
      riemannianVolumeMeasure (I := I) (M := M) h (riemannianBallOf h p r) :=
    hlocal.trans (_root_.MeasureTheory.measure_mono hAsubset)
  have hinside : k * riemannianVolumeMeasure (I := I) (M := M) g
      (riemannianBallOf g p r ∩ K) ≤ k * riemannianVolumeMeasure (I := I) (M := M) g K :=
    mul_le_mul_right (_root_.MeasureTheory.measure_mono _root_.Set.inter_subset_right) k
  change k * riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) ≤ _
  rw [← _root_.MeasureTheory.measure_sdiff_add_inter (riemannianBallOf g p r) hK, mul_add]
  exact add_le_add houtside hinside

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparison_ballVolume_le_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrComparison_ballVolume_le_add target :: scope.openDecls } }

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] [ConnectedSpace M]

theorem asymptoticVolumeRatio_mul_le_of_metric_lower_off_compact
    (g h : SmoothRiemannianMetric I M)
    (hgcomplete : RiemannianMetricComplete g) (hhcomplete : RiemannianMetricComplete h)
    (hgRic : RicciBoundedBelow (I := I) g 0) (hhRic : RicciBoundedBelow (I := I) h 0)
    (p : M) {K : Set M} (hK : IsCompact K) {Q : ℝ} (hQ : 0 < Q)
    (hdist : ∀ x : M, riemannianEDistOf (I := I) h p x ≤
      riemannianEDistOf (I := I) g p x)
    (hmetric : ∀ x : M, x ∉ K → ∀ v : TangentSpace I x,
      Q * g.inner x v v ≤ h.inner x v v) :
    ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) * asymptoticVolumeRatio g p ≤
      asymptoticVolumeRatio h p := by
  let k : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E))
  let den : ℝ → ℝ≥0∞ := fun r => euclideanUnitBallVolume (Module.finrank ℝ E) *
    ENNReal.ofReal (r ^ Module.finrank ℝ E)
  let C : ℝ≥0∞ := k * riemannianVolumeMeasure (I := I) (M := M) g K
  let _ : _root_.MeasureTheory.IsLocallyFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) g
  have hKfinite : riemannianVolumeMeasure (I := I) (M := M) g K ≠ ⊤ := hK.measure_lt_top.ne
  have hkfinite : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCfinite : C ≠ ⊤ := ENNReal.mul_ne_top hkfinite hKfinite
  have hden : _root_.Filter.Tendsto den _root_.Filter.atTop (𝓝 (⊤ : ℝ≥0∞)) :=
    avrComparison_denominator_tendsto_top _ (NeZero.ne (Module.finrank ℝ E))
  have herror : _root_.Filter.Tendsto (fun r : ℝ => C / den r) _root_.Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.div_top] using
      ENNReal.Tendsto.const_div (a := C) hden (Or.inr hCfinite)
  have hleft : _root_.Filter.Tendsto (fun r : ℝ => k * normalizedBallVolumeRatio g p r)
      atTop (𝓝 (k * asymptoticVolumeRatio g p)) :=
    ENNReal.Tendsto.const_mul (tendsto_normalizedBallVolumeRatio_atTop g hgcomplete hgRic p)
      (Or.inr hkfinite)
  have hright : _root_.Filter.Tendsto (fun r : ℝ => normalizedBallVolumeRatio h p r + C / den r)
      atTop (𝓝 (asymptoticVolumeRatio h p)) := by
    simpa only [add_zero] using
      (tendsto_normalizedBallVolumeRatio_atTop h hhcomplete hhRic p).add herror
  apply le_of_tendsto_of_tendsto' hleft hright
  intro r
  have hraw := avrComparison_ballVolume_le_add g h p hK.isClosed.measurableSet
    hQ hdist hmetric r
  change k * (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) / den r) ≤
    riemannianVolumeMeasure (I := I) (M := M) h (riemannianBallOf h p r) / den r + C / den r
  simpa only [div_eq_mul_inv, add_mul, mul_assoc, C, k] using
    mul_le_mul_left hraw (den r)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_mul_le_of_metric_lower_off_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_mul_le_of_metric_lower_off_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_mul_le_of_metric_lower_off_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_mul_le_of_metric_lower_off_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
