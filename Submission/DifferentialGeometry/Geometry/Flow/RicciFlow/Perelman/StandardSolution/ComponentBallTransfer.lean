import Submission.DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import Submission.DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.Geometry.Metric
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance componentBallSigmaCompact (p : M) :
    SigmaCompactSpace (connectedComponentOpen (I := I) p) :=
  (isClosed_connectedComponent (x := p)).sigmaCompactSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.componentBallSigmaCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.componentBallSigmaCompact target :: scope.openDecls } }

theorem isSolutionOn_restrict_connCompOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) (p : M) :
    IsSolutionOn (I := I) (solutionOnRestrictOpen (I := I) S (connectedComponentOpen (I := I) p)) := by
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (connectedComponentOpen (I := I) p) := by
    simpa using (inferInstance : IsManifold I ∞ (connectedComponentOpen (I := I) p))
  exact isSolutionOn_restrictOpen (I := I) S hS (connectedComponentOpen (I := I) p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_restrict_connCompOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.isSolutionOn_restrict_connCompOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.isSolutionOn_restrict_connCompOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.isSolutionOn_restrict_connCompOpen

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem rmNormSq_solutionOnRestrictOpen
    (S : SolutionOn (I := I) (M := M) D) (U : _root_.TopologicalSpace.Opens M)
    [SigmaCompactSpace U] (t : ℝ) (x : U) :
    FlowMetricBall.rmNormSq (solutionOnRestrictOpen (I := I) S U) t x =
      FlowMetricBall.rmNormSq S t (x : M) := by
  have hsec : metricRm04 (I := I) (M := U) ((S.base.metric t).restrictOpen U) x =
      metricRm04 (I := I) (M := M) (S.base.metric t) (x : M) := by
    ext slots
    have h := metricRm04_restrictOpen_eval (I := I) (S.base.metric t) U x slots
    simp only [mfderiv_subtype_val_apply] at h
    exact h
  change normSq0S (I := I) (M := U) ((S.base.metric t).restrictOpen U) x 4
      (metricRm04 (I := I) (M := U) ((S.base.metric t).restrictOpen U) x) =
    normSq0S (I := I) (M := M) (S.base.metric t) (x : M) 4
      (metricRm04 (I := I) (M := M) (S.base.metric t) (x : M))
  rw [normSq0S_restrictOpen_apply, hsec]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rmNormSq_solutionOnRestrictOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rmNormSq_solutionOnRestrictOpen target :: scope.openDecls } }

theorem rmNormSq_restrict_connCompOpen
    (S : SolutionOn (I := I) (M := M) D) (p : M) (t : ℝ)
    (x : connectedComponentOpen (I := I) p) :
    FlowMetricBall.rmNormSq
        (solutionOnRestrictOpen (I := I) S (connectedComponentOpen (I := I) p)) t x =
      FlowMetricBall.rmNormSq S t (x : M) :=
  rmNormSq_solutionOnRestrictOpen S (connectedComponentOpen (I := I) p) t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rmNormSq_restrict_connCompOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rmNormSq_restrict_connCompOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rmNormSq_restrict_connCompOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.rmNormSq_restrict_connCompOpen

variable {S : SolutionOn (I := I) (M := M) D} {time : RealTimeInterval.FlowTime D}

def FlowMetricBall.onConnectedComponent (B : FlowMetricBall S time) :
    FlowMetricBall
      (solutionOnRestrictOpen (I := I) S (connectedComponentOpen (I := I) B.center)) time where
  center := connectedComponentPoint (I := I) B.center
  radius := B.radius
  radius_pos := B.radius_pos

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
theorem FlowMetricBall.set_subset_connCompOpen (B : FlowMetricBall S time) :
    B.set ⊆ (connectedComponentOpen (I := I) B.center : Set M) :=
  edistOf_ball_subset_connCompOpen (I := I) (S.base.metric (time : ℝ)) B.center B.radius

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.set_subset_connCompOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.set_subset_connCompOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.set_subset_connCompOpen ``Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.set_subset_connCompOpen

theorem FlowMetricBall.onConnectedComponent_set (B : FlowMetricBall S time) :
    (FlowMetricBall.onConnectedComponent B).set = (Subtype.val : connectedComponentOpen (I := I) B.center → M) ⁻¹' B.set := by
  ext x
  change riemannianEDistOf (I := I)
      ((S.base.metric (time : ℝ)).restrictOpen (connectedComponentOpen (I := I) B.center))
      (connectedComponentPoint (I := I) B.center) x < ENNReal.ofReal B.radius ↔
    riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center (x : M) <
      ENNReal.ofReal B.radius
  rw [edistOf_restrictOpen_connCompOpen (I := I)
    (S.base.metric (time : ℝ)) B.center (connectedComponentPoint (I := I) B.center) x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_set ``Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_set

theorem FlowMetricBall.onConnectedComponent_image_set (B : FlowMetricBall S time) :
    (Subtype.val : connectedComponentOpen (I := I) B.center → M) '' (FlowMetricBall.onConnectedComponent B).set = B.set := by
  rw [FlowMetricBall.onConnectedComponent_set B, _root_.Set.image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.mpr (FlowMetricBall.set_subset_connCompOpen B)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_image_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_image_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_image_set ``Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_image_set

theorem FlowMetricBall.onConnectedComponent_volume (B : FlowMetricBall S time) :
    (FlowMetricBall.onConnectedComponent B).volume = B.volume := by
  have hB : MeasurableSet B.set := by
    have hd : Continuous (fun y : M ↦
        riemannianEDistOf (I := I) (S.base.metric (time : ℝ)) B.center y) := by
      simpa only [riemannianEDistOf] using
        continuous_riemannianEDist (S.base.metric (time : ℝ)) B.center
    exact (isOpen_lt hd continuous_const).measurableSet
  change riemannianVolumeMeasure (I := I) (M := connectedComponentOpen (I := I) B.center)
      ((S.base.metric (time : ℝ)).restrictOpen (connectedComponentOpen (I := I) B.center))
      (FlowMetricBall.onConnectedComponent B).set =
    riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (time : ℝ)) B.set
  rw [FlowMetricBall.onConnectedComponent_set B]
  exact DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (I := I) (S.base.metric (time : ℝ)) (connectedComponentOpen (I := I) B.center)
    hB (FlowMetricBall.set_subset_connCompOpen B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_volume

theorem FlowMetricBall.onConnectedComponent_noncollapsed_iff
    (B : FlowMetricBall S time) (kappa : ℝ) :
    (FlowMetricBall.onConnectedComponent B).IsKappaNoncollapsed kappa ↔ B.IsKappaNoncollapsed kappa := by
  change (0 < kappa ∧ ENNReal.ofReal kappa * ENNReal.ofReal B.radius ^ Module.finrank ℝ E ≤
      (FlowMetricBall.onConnectedComponent B).volume) ↔
    (0 < kappa ∧ ENNReal.ofReal kappa * ENNReal.ofReal B.radius ^ Module.finrank ℝ E ≤ B.volume)
  rw [FlowMetricBall.onConnectedComponent_volume B]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_noncollapsed_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_noncollapsed_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_noncollapsed_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.onConnectedComponent_noncollapsed_iff

theorem FlowMetricBall.fixed_terminal_rm_control_onConnectedComponent
    (B : FlowMetricBall S time)
    (hslab : _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier)
    (hRm : ∀ t ∈ _root_.Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ x ∈ B.set,
      B.radius ^ 4 * normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ 1) :
    _root_.Set.Icc ((time : ℝ) - (FlowMetricBall.onConnectedComponent B).radius ^ 2) (time : ℝ) ⊆ D.carrier ∧
      ∀ t ∈ _root_.Set.Icc ((time : ℝ) - (FlowMetricBall.onConnectedComponent B).radius ^ 2) (time : ℝ),
        ∀ x ∈ (FlowMetricBall.onConnectedComponent B).set,
          (FlowMetricBall.onConnectedComponent B).radius ^ 4 * normSq0S (I := I)
            ((solutionOnRestrictOpen (I := I) S (connectedComponentOpen (I := I) B.center)).base.metric t)
            x 4
            ((solutionOnRestrictOpen (I := I) S (connectedComponentOpen (I := I) B.center)).base.rm04 t x)
            ≤ 1 := by
  refine ⟨hslab, ?_⟩
  intro t ht x hx
  have hxM : (x : M) ∈ B.set := by
    rwa [FlowMetricBall.onConnectedComponent_set B] at hx
  change B.radius ^ 4 * FlowMetricBall.rmNormSq
    (solutionOnRestrictOpen (I := I) S (connectedComponentOpen (I := I) B.center)) t x ≤ 1
  rw [rmNormSq_restrict_connCompOpen]
  exact hRm t ht (x : M) hxM

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.fixed_terminal_rm_control_onConnectedComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.fixed_terminal_rm_control_onConnectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.fixed_terminal_rm_control_onConnectedComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.FlowMetricBall.fixed_terminal_rm_control_onConnectedComponent

end DifferentialGeometry.PDE.RicciFlow

end
