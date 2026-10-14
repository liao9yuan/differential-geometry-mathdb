import Submission.DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import Submission.DifferentialGeometry.Geometry.Metric.Restriction.Ball
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

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

theorem riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (hU : IsClosed (U : Set M)) (x : U) (r : ℝ) :
    let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    riemannianVolumeMeasure I U (g.restrictOpen U)
        (riemannianBallOf (g.restrictOpen U) x r) =
      riemannianVolumeMeasure I M g (riemannianBallOf g x.val r) := by
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hpre : riemannianBallOf (g.restrictOpen U) x r =
      Subtype.val ⁻¹' riemannianBallOf g x.val r := by
    ext y
    change riemannianEDistOf (g.restrictOpen U) x y < ENNReal.ofReal r ↔
      riemannianEDistOf g x.val y.val < ENNReal.ofReal r
    rw [riemannianEDistOf_restrictOpen_of_isClosed g U hU]
  have hball : MeasurableSet (riemannianBallOf g x.val r) :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g x.val)
      continuous_const).measurableSet
  have hsub : riemannianBallOf g x.val r ⊆ U := by
    rw [riemannianBallOf_eq_image_restrictOpen_of_isClosed g U hU x r]
    rintro y ⟨z,_,rfl⟩
    exact z.property
  rw [hpre]
  exact Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    g U hball hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed ``Submission.DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_ball_restrictOpen_of_isClosed

end DifferentialGeometry.Integral.Measure
