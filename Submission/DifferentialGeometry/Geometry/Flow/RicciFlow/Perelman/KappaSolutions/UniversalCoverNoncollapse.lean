import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverCurvatureNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CoverBallVolume
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [CompleteSpace E] [T2Space M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M] [Inhabited M] in
private theorem coverNoncollapseSecondCountable (I : ModelWithCorners ℝ E H) :
    SecondCountableTopology M := by
  let _ : SecondCountableTopology H := I.secondCountableTopology
  exact ChartedSpace.secondCountable_of_sigmaCompact H M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseSecondCountable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseSecondCountable target :: scope.openDecls } }

private local instance coverNoncollapseMeasurable : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseMeasurable target :: scope.openDecls } }
private local instance coverNoncollapseBorel : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseBorel target :: scope.openDecls } }
private local instance coverNoncollapseLiftMeasurable :
    MeasurableSpace (UniversalCover M) := borel (UniversalCover M)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseLiftMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseLiftMeasurable target :: scope.openDecls } }
private local instance coverNoncollapseLiftBorel :
    BorelSpace (UniversalCover M) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseLiftBorel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseLiftBorel target :: scope.openDecls } }
private local instance coverNoncollapseC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseC1 target :: scope.openDecls } }
private local instance coverNoncollapseLiftC1 :
    IsManifold I 1 (UniversalCover M) := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseLiftC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverNoncollapseLiftC1 target :: scope.openDecls } }

theorem universalCover_tensor_noncollapsed
    (g : SmoothRiemannianMetric I M) (kappa : ℝ)
    (hnoncollapse : ∀ (p : M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) g p r,
        r ^ 4 * normSq0S (I := I) g y 4 (metricRm04At (I := I) g y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          (riemannianBallOf (I := I) g p r))
    (x : UniversalCover M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ y ∈
      riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r,
      r ^ 4 * normSq0S (I := I) (UniversalCover.liftedMetric (I := I) g) y 4
        (metricRm04At (I := I) (UniversalCover.liftedMetric (I := I) g) y) ≤ 1) :
    let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := UniversalCover M)
        (UniversalCover.liftedMetric (I := I) g)
        (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r) := by
  let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
  have himage := universalCover_image_ball_liftedMetric g x r hr
  have hbase : ∀ y ∈ riemannianBallOf (I := I) g (UniversalCover.proj x) r,
      r ^ 4 * normSq0S (I := I) g y 4 (metricRm04At (I := I) g y) ≤ 1 := by
    intro y hy
    rw [← himage] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    simpa only [UniversalCover.normSq0S_metricRm04At_liftedMetric] using hcurvature y' hy'
  have hopen : IsOpen
      (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r) :=
    isOpen_lt
      (continuous_riemannianEDist (I := I) (UniversalCover.liftedMetric (I := I) g) x)
      continuous_const
  have hvolume := universalCover_volume_image_le g
    (riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r) hopen
  rw [himage] at hvolume
  exact (hnoncollapse (UniversalCover.proj x) r hr hbase).trans hvolume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_tensor_noncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_tensor_noncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_tensor_noncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_tensor_noncollapsed

theorem universalCover_solution_slice_noncollapsed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (kappa : ℝ)
    (hnoncollapse : ∀ (time : RealTimeInterval.FlowTime D)
      (B : FlowMetricBall (I := I) (M := M) S time),
      B.IsSpatiallyKappaNoncollapsed kappa)
    (time : RealTimeInterval.FlowTime D) (x : UniversalCover M)
    (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ y ∈ riemannianBallOf (I := I)
      (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) x r,
      r ^ 4 * normSq0S (I := I)
        (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) y 4
        (metricRm04At (I := I)
          (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) y) ≤ 1) :
    let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := UniversalCover M)
        (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ)))
        (riemannianBallOf (I := I)
          (UniversalCover.liftedMetric (I := I) (S.base.metric (time : ℝ))) x r) := by
  let _ : SecondCountableTopology M := coverNoncollapseSecondCountable (M := M) I
  apply universalCover_tensor_noncollapsed (S.base.metric (time : ℝ))
    kappa ?_ x r hr hcurvature
  intro p rho hrho hRm
  let B : FlowMetricBall (I := I) (M := M) S time := ⟨p, rho, hrho⟩
  have hB : B.IsSpatiallyRmControlled := by
    intro y hy
    simpa only [B, FlowMetricBall.rmNormSq, SolutionFamily.rm04,
      metricRm04_apply] using hRm y hy
  have hvolume := (hnoncollapse time B hB).2
  change ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : ℝ))
      (riemannianBallOf (I := I) (S.base.metric (time : ℝ)) p rho) at hvolume
  exact hvolume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_solution_slice_noncollapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_solution_slice_noncollapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_solution_slice_noncollapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.universalCover_solution_slice_noncollapsed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
