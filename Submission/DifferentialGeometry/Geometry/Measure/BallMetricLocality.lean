import Submission.DifferentialGeometry.Geometry.Metric.Distance.MetricLocality
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.VolumeNaturality
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall
    (g g' : SmoothRiemannianMetric I M) {p x : M} {r ρ R : ℝ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hR : r + ρ ≤ R)
    (hx : x ∈ riemannianClosedBallOf g p r)
    (heq : ∀ z ∈ riemannianClosedBallOf g p R, g'.inner z = g.inner z)
    (hle : ∀ z (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) :
    riemannianVolumeMeasure I M g' (riemannianBallOf g' x ρ) =
      riemannianVolumeMeasure I M g (riemannianBallOf g x ρ) := by
  rw [riemannianBallOf_eq_of_eqOn_outer_closedBall g g' hr hρ hR hx heq hle]
  have hopen : IsOpen (riemannianBallOf g x ρ) :=
    isOpen_lt (by
      unfold riemannianEDistOf
      exact Riemannian.continuous_riemannianEDist g x) continuous_const
  apply Riemannian.VolumeComparison.riemannianVolumeMeasure_apply_eq_of_inner_eqOn
    g' g hopen.measurableSet
  intro z hz v
  change riemannianEDistOf g x z < ENNReal.ofReal ρ at hz
  have hzR := riemannianClosedBallOf_subset_of_add_radius_le g hr hρ hR hx (le_of_lt hz)
  exact congrArg (fun A => A v v) (heq z hzR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_eqOn_outer_closedBall

end DifferentialGeometry.Geometry.Measure
