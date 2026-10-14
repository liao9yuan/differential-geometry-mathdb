import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SmallBallEuclideanRatio
import Mathlib.Topology.Order.IntermediateValue

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
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.Topology _root_.Submission.Topology

universe u uE uH

section Static

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [ConnectedSpace M]

private local instance halfScaleMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleMeasurable target :: scope.openDecls } }
private local instance halfScaleBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleBorel target :: scope.openDecls } }

theorem exists_halfEuclideanScale
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M)
    (hunit : riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p 1) <
      euclideanUnitBallVolume (Module.finrank ℝ E) / 2) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p delta) =
        (euclideanUnitBallVolume (Module.finrank ℝ E) / 2) *
          ENNReal.ofReal (delta ^ Module.finrank ℝ E) := by
  let n := Module.finrank ℝ E
  let omega := euclideanUnitBallVolume n
  let theta : ℝ → ℝ := fun r =>
    (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r)).toReal / r ^ n
  have homega : 0 < omega.toReal :=
    ENNReal.toReal_pos (euclideanUnitBallVolume_pos n).ne' (euclideanUnitBallVolume_ne_top n)
  have hhalftop : omega / 2 ≠ ⊤ :=
    ENNReal.div_ne_top (euclideanUnitBallVolume_ne_top n) (by norm_num)
  have hunitfinite :
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p 1) ≠ ⊤ :=
    ne_top_of_le_ne_top hhalftop hunit.le
  have htheta_one : theta 1 < omega.toReal / 2 := by
    have hreal := (ENNReal.toReal_lt_toReal hunitfinite hhalftop).2 hunit
    simpa only [theta, one_pow, div_one, ENNReal.toReal_div, ENNReal.toReal_ofNat] using hreal
  have hlimit : _root_.Filter.Tendsto theta (𝓝[>] (0 : ℝ)) (𝓝 omega.toReal) :=
    tendsto_riemannianBallOf_realVolume_div_pow_nhdsGT_zero g hcomplete p
  have hnear : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), omega.toReal / 2 < theta r :=
    hlimit.eventually (Ioi_mem_nhds (half_lt_self homega))
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ∈ _root_.Set.Ioo 0 1 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  obtain ⟨a, ha, htheta_a⟩ := (hsmall.and hnear).exists
  have hcontinuous : ContinuousOn theta (Set.Icc a 1) := by
    intro r hr
    exact (continuousAt_riemannianBallOf_realVolume_div_pow g hcomplete p
      (ha.1.trans_le hr.1)).continuousWithinAt
  obtain ⟨delta, hdelta, hequal⟩ :=
    intermediate_value_Icc' ha.2.le hcontinuous ⟨htheta_one.le, htheta_a.le⟩
  have hdelta_pos : 0 < delta := ha.1.trans_le hdelta.1
  have hdelta_lt : delta < 1 := by
    by_contra hn
    have hdelta_one : delta = 1 := le_antisymm hdelta.2 (le_of_not_gt hn)
    rw [hdelta_one] at hequal
    exact htheta_one.ne hequal
  have hdeltafinite :
      riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p delta) ≠ ⊤ :=
    ne_top_of_le_ne_top hunitfinite
      (_root_.MeasureTheory.measure_mono (riemannianBallOf_mono (I := I) g p hdelta.2))
  have hrealEqual :
      (riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p delta)).toReal =
        (omega.toReal / 2) * delta ^ n :=
    (div_eq_iff (pow_ne_zero _ hdelta_pos.ne')).1 hequal
  refine ⟨delta, hdelta_pos, hdelta_lt, ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' hdeltafinite
    (ENNReal.mul_ne_top hhalftop ENNReal.ofReal_ne_top)).1
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (pow_nonneg hdelta_pos.le _)] using hrealEqual

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScale ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScale

end Static

section VaryingPointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (X : PointedRiemannianSeq.{u, uE, uH} (I := I))

private local instance halfScaleSourceTopology (i : ℕ) : TopologicalSpace (X.obj i).M :=
  (X.obj i).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceTopology target :: scope.openDecls } }
private local instance halfScaleSourceCharted (i : ℕ) : ChartedSpace H (X.obj i).M :=
  (X.obj i).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceCharted target :: scope.openDecls } }
private local instance halfScaleSourceSmooth (i : ℕ) : IsManifold I ∞ (X.obj i).M :=
  (X.obj i).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceSmooth target :: scope.openDecls } }
private local instance halfScaleSourceT2 (i : ℕ) : T2Space (X.obj i).M := (X.obj i).t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceT2 target :: scope.openDecls } }
private local instance halfScaleSourceSigma (i : ℕ) : SigmaCompactSpace (X.obj i).M :=
  (X.obj i).sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceSigma target :: scope.openDecls } }
private local instance halfScaleSourceTangentT2 (i : ℕ) : T2Space (TangentBundle I (X.obj i).M) :=
  (X.obj i).t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceTangentT2 target :: scope.openDecls } }
private local instance halfScaleSourceMeasurable (i : ℕ) : MeasurableSpace (X.obj i).M :=
  borel (X.obj i).M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceMeasurable target :: scope.openDecls } }
private local instance halfScaleSourceBorel (i : ℕ) : BorelSpace (X.obj i).M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.halfScaleSourceBorel target :: scope.openDecls } }

theorem exists_halfEuclideanScales_tendsto_zero
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ, ConnectedSpace (X.obj i).M)
    (hunit : ∀ i : ℕ,
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint 1) <
          euclideanUnitBallVolume (Module.finrank ℝ E) / 2)
    (hcollapse : _root_.Filter.Tendsto (fun i : ℕ =>
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint 1))
      _root_.Filter.atTop (𝓝 0)) :
    ∃ delta : ℕ → ℝ,
      (∀ i : ℕ, 0 < delta i ∧ delta i < 1 ∧
        riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
          (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint (delta i)) =
            (euclideanUnitBallVolume (Module.finrank ℝ E) / 2) *
              ENNReal.ofReal ((delta i) ^ Module.finrank ℝ E)) ∧
      Tendsto delta _root_.Filter.atTop (𝓝 0) := by
  classical
  have hscales : ∀ i : ℕ, ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint delta) =
          (euclideanUnitBallVolume (Module.finrank ℝ E) / 2) *
            ENNReal.ofReal (delta ^ Module.finrank ℝ E) := by
    intro i
    let _ : ConnectedSpace (X.obj i).M := hconnected i
    have hg : RiemannianMetricComplete (I := I) (X.obj i).metric :=
      ⟨hcomplete.complete i⟩
    exact exists_halfEuclideanScale (I := I) (X.obj i).metric hg
      (X.obj i).basepoint (hunit i)
  choose delta hpositive hsmall hequal using hscales
  refine ⟨delta, fun i => ⟨hpositive i, hsmall i, hequal i⟩, ?_⟩
  let n := Module.finrank ℝ E
  let a : ℝ≥0∞ := euclideanUnitBallVolume n / 2
  have ha : 0 < a :=
    ENNReal.div_pos (euclideanUnitBallVolume_pos n).ne' (by norm_num)
  have hbound : ∀ i : ℕ, a * ENNReal.ofReal ((delta i) ^ n) ≤
      riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
        (riemannianBallOf (I := I) (X.obj i).metric (X.obj i).basepoint 1) := by
    intro i
    exact (hequal i).symm.le.trans
      (_root_.MeasureTheory.measure_mono (riemannianBallOf_mono (I := I) (X.obj i).metric
        (X.obj i).basepoint (hsmall i).le))
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have hthreshold : 0 < a * ENNReal.ofReal (epsilon ^ n) :=
    ENNReal.mul_pos ha.ne' (ENNReal.ofReal_pos.mpr (pow_pos hepsilon n)).ne'
  filter_upwards [hcollapse.eventually (Iio_mem_nhds hthreshold)] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpositive i).le]
  by_contra hn
  have hle : epsilon ≤ delta i := le_of_not_gt hn
  have hpower : ENNReal.ofReal (epsilon ^ n) ≤ ENNReal.ofReal ((delta i) ^ n) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hepsilon.le hle n)
  exact hi.not_ge ((mul_le_mul_right hpower a).trans (hbound i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScales_tendsto_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScales_tendsto_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScales_tendsto_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_halfEuclideanScales_tendsto_zero

end VaryingPointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
