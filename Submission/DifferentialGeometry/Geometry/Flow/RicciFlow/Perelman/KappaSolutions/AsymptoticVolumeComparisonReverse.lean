import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticVolumeRatio
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison
import Mathlib.Topology.Algebra.Order.Field

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance avrReverseMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverseMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverseMeasurable target :: scope.openDecls } }
private local instance avrReverseBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverseBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverseBorel target :: scope.openDecls } }
private local instance avrReverseC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverseC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverseC1 target :: scope.openDecls } }

private theorem avrReverse_radius_denominator_change
    (g : SmoothRiemannianMetric I M) (p : M) (r a : ℝ) (ha : 0 < a) :
    riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p (a * r)) /
        (euclideanUnitBallVolume (Module.finrank ℝ E) *
          ENNReal.ofReal (r ^ Module.finrank ℝ E)) =
      ENNReal.ofReal (a ^ Module.finrank ℝ E) *
        normalizedBallVolumeRatio g p (a * r) := by
  let k : ℝ≥0∞ := ENNReal.ofReal (a ^ Module.finrank ℝ E)
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos ha _)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold normalizedBallVolumeRatio
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg ha.le _)]
  have hden : euclideanUnitBallVolume (Module.finrank ℝ E) *
      (k * ENNReal.ofReal (r ^ Module.finrank ℝ E)) =
      k * (euclideanUnitBallVolume (Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E)) := by ac_rfl
  change _ = k * (_ / (euclideanUnitBallVolume (Module.finrank ℝ E) *
    (k * ENNReal.ofReal (r ^ Module.finrank ℝ E))))
  rw [hden]
  let V := riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p (a * r))
  let b := euclideanUnitBallVolume (Module.finrank ℝ E) *
    ENNReal.ofReal (r ^ Module.finrank ℝ E)
  change V / b = k * (V / (k * b))
  symm
  calc
    k * (V / (k * b)) = (k * V) / (k * b) := by
      simp only [div_eq_mul_inv, mul_assoc]
    _ = _ := ENNReal.mul_div_mul_left _ _ hk0 hkt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverse_radius_denominator_change
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverse_radius_denominator_change target :: scope.openDecls } }

variable [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
private theorem avrReverse_mem_ball_iff
    (g : SmoothRiemannianMetric I M) (p x : M) (r : ℝ) :
    x ∈ riemannianBallOf g p r ↔ (riemannianEDistOf g p x).toReal < r := by
  let _ : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  change _root_.Manifold.riemannianEDist I p x < ENNReal.ofReal r ↔ (_root_.Manifold.riemannianEDist I p x).toReal < r
  constructor
  · exact ENNReal.toReal_lt_of_lt_ofReal
  · intro hx
    rw [← ENNReal.ofReal_toReal (riemannianEDist_ne_top (I := I) p x)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverse_mem_ball_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.avrReverse_mem_ball_iff target :: scope.openDecls } }

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)]

theorem asymptoticVolumeRatio_le_of_additive_distance_and_metric_le
    (g h : SmoothRiemannianMetric I M)
    (hgcomplete : RiemannianMetricComplete g) (hhcomplete : RiemannianMetricComplete h)
    (hgRic : RicciBoundedBelow (I := I) g 0) (hhRic : RicciBoundedBelow (I := I) h 0)
    (p : M) {C : ℝ} (hC : 0 ≤ C)
    (hdist : ∀ x : M, (riemannianEDistOf (I := I) g p x).toReal - C ≤
      (riemannianEDistOf (I := I) h p x).toReal)
    (hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      h.inner x v v ≤ g.inner x v v) :
    asymptoticVolumeRatio h p ≤ asymptoticVolumeRatio g p := by
  have hvolume : riemannianVolumeMeasure (I := I) (M := M) h ≤
      riemannianVolumeMeasure (I := I) (M := M) g := by
    simpa only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_smul] using
      volumeMeasure_le g h (Q := 1) one_pos (fun x v => by
        simpa only [one_mul] using hmetric x v)
  have hballs (r : ℝ) : riemannianBallOf h p r ⊆ riemannianBallOf g p (r + C) := by
    intro x hx
    apply (avrReverse_mem_ball_iff g p x (r + C)).mpr
    have hxreal := (avrReverse_mem_ball_iff h p x r).mp hx
    have hd := hdist x
    linarith
  have hfiniteRadius (r : ℝ) (hr : 0 < r) :
      normalizedBallVolumeRatio h p r ≤
        ENNReal.ofReal ((1 + C / r) ^ Module.finrank ℝ E) *
          normalizedBallVolumeRatio g p (r + C) := by
    have ha : 0 < 1 + C / r := by
      have hdiv := div_nonneg hC hr.le
      linarith
    have hscale : (1 + C / r) * r = r + C := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hr.ne']
    have hmeasure : riemannianVolumeMeasure (I := I) (M := M) h (riemannianBallOf h p r) ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p (r + C)) :=
      (hvolume (riemannianBallOf h p r)).trans (_root_.MeasureTheory.measure_mono (hballs r))
    calc
      normalizedBallVolumeRatio h p r ≤
          riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p (r + C)) /
            (euclideanUnitBallVolume (Module.finrank ℝ E) *
              ENNReal.ofReal (r ^ Module.finrank ℝ E)) :=
        mul_le_mul_left hmeasure _
      _ = ENNReal.ofReal ((1 + C / r) ^ Module.finrank ℝ E) *
          normalizedBallVolumeRatio g p (r + C) := by
        simpa only [hscale] using avrReverse_radius_denominator_change g p r (1 + C / r) ha
  have hfraction : _root_.Filter.Tendsto (fun r : ℝ => C / r) _root_.Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_id.const_div_atTop C
  have hsum : _root_.Filter.Tendsto (fun r : ℝ => 1 + C / r) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hfraction
  have hpower : _root_.Filter.Tendsto (fun r : ℝ => (1 + C / r) ^ Module.finrank ℝ E)
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow] using hsum.pow (Module.finrank ℝ E)
  have hfactor : _root_.Filter.Tendsto
      (fun r : ℝ => ENNReal.ofReal ((1 + C / r) ^ Module.finrank ℝ E))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      (ENNReal.continuous_ofReal.tendsto 1).comp hpower
  have hshift : _root_.Filter.Tendsto (fun r : ℝ => r + C) _root_.Filter.atTop atTop :=
    _root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop C _root_.Filter.tendsto_id
  have hratio : _root_.Filter.Tendsto (fun r : ℝ => normalizedBallVolumeRatio g p (r + C))
      atTop (𝓝 (asymptoticVolumeRatio g p)) := by
    simpa only [Function.comp_def] using
      (tendsto_normalizedBallVolumeRatio_atTop g hgcomplete hgRic p).comp hshift
  have hright : _root_.Filter.Tendsto
      (fun r : ℝ => ENNReal.ofReal ((1 + C / r) ^ Module.finrank ℝ E) *
        normalizedBallVolumeRatio g p (r + C))
      atTop (𝓝 (asymptoticVolumeRatio g p)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul hfactor (Or.inl one_ne_zero)
      hratio (Or.inr ENNReal.one_ne_top)
  apply le_of_tendsto_of_tendsto
    (tendsto_normalizedBallVolumeRatio_atTop h hhcomplete hhRic p) hright
  filter_upwards [_root_.Filter.eventually_ge_atTop (1 : ℝ)] with r hr
  exact hfiniteRadius r (one_pos.trans_le hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_le_of_additive_distance_and_metric_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_le_of_additive_distance_and_metric_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_le_of_additive_distance_and_metric_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.asymptoticVolumeRatio_le_of_additive_distance_and_metric_le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
