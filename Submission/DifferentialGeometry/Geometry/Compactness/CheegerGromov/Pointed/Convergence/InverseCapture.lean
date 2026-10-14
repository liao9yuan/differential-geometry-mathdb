import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.QuadraticBounds
import Submission.DifferentialGeometry.Geometry.Comparison.BallCapture

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance inverseCaptureComplete : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureComplete target :: scope.openDecls } }

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

private local instance inverseCaptureLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitTopology target :: scope.openDecls } }
private local instance inverseCaptureLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitCharted target :: scope.openDecls } }
private local instance inverseCaptureLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitSmooth target :: scope.openDecls } }
private local instance inverseCaptureLimitOne : IsManifold I 1 L.M :=
  IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitOne target :: scope.openDecls } }
private local instance inverseCaptureLimitT2 : T2Space L.M := L.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitT2 target :: scope.openDecls } }
private local instance inverseCaptureLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureLimitSigma target :: scope.openDecls } }

private local instance inverseCaptureApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxTopology target :: scope.openDecls } }
private local instance inverseCaptureApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxCharted target :: scope.openDecls } }
private local instance inverseCaptureApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxSmooth target :: scope.openDecls } }
private local instance inverseCaptureApproxOne (k : ℕ) :
    IsManifold I 1 (X.obj k).M :=
  IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxOne target :: scope.openDecls } }
private local instance inverseCaptureApproxT2 (k : ℕ) :
    T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxT2 target :: scope.openDecls } }
private local instance inverseCaptureApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.inverseCaptureApproxSigma target :: scope.openDecls } }

theorem pointed_metric_eventually_inverse_ball_capture
    (z : L.M) {R r factor : ℝ} (hr : 0 ≤ r) (hfactor : 1 < factor)
    (hbuffer : factor * r < R)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric z R))
    (hconv : metricSourceConvergesOn Φ
      (CanonicalMetricCompactness.canonicalSourceData Φ)
      (riemannianClosedBallOf L.metric z R) 0) :
    ∀ᶠ k in _root_.Filter.atTop, riemannianClosedBallOf L.metric z R ⊆ Φ.source k ∧
      ∀ y ∈ riemannianClosedBallOf (X.obj (subseq k)).metric (Φ.map k z) r,
        y ∈ (Φ.partialDiffeomorph k).target ∧
        (Φ.partialDiffeomorph k).symm y ∈ Φ.source k ∧
        (Φ.partialDiffeomorph k).symm y ∈
          riemannianClosedBallOf L.metric z (factor * r) ∧
        Φ.map k ((Φ.partialDiffeomorph k).symm y) = y := by
  have hfactorpos : 0 < factor := zero_lt_one.trans hfactor
  have hfactorSq : 1 < factor ^ 2 := by nlinarith
  have hfactorSqPos : 0 < factor ^ 2 := sq_pos_of_pos hfactorpos
  let delta : ℝ := 1 - (factor ^ 2)⁻¹
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact sub_pos.mpr ((inv_lt_one₀ hfactorSqPos).2 hfactorSq)
  filter_upwards [pointed_metric_eventually_quadratic_bounds hcompact hconv hdelta] with k hk
  refine ⟨hk.1, ?_⟩
  intro y hy
  have hlower (x : L.M) (hx : x ∈ riemannianClosedBallOf L.metric z R)
      (v : TangentSpace I x) :
      L.metric.inner x v v ≤ factor ^ 2 *
        (X.obj (subseq k)).metric.inner (Φ.map k x)
          (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x v) := by
    have h := (hk.2 x hx v).1
    have hsmall : (factor ^ 2)⁻¹ * L.metric.inner x v v ≤
        (X.obj (subseq k)).metric.inner (Φ.map k x)
          (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x v) := by
      simpa only [delta, sub_sub_cancel] using h
    calc
      _ = factor ^ 2 * ((factor ^ 2)⁻¹ * L.metric.inner x v v) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hfactorSqPos), one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hfactorSqPos.le
  obtain ⟨hytarget, hyball⟩ :=
    PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower
      L.metric (X.obj (subseq k)).metric (Φ.partialDiffeomorph k) z
      hr hfactorpos hbuffer hcompact hk.1 hlower y hy
  exact ⟨hytarget, (Φ.partialDiffeomorph k).map_target' hytarget,
    hyball, (Φ.partialDiffeomorph k).right_inv' hytarget⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_inverse_ball_capture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_inverse_ball_capture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_inverse_ball_capture ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_inverse_ball_capture

end DifferentialGeometry.CheegerGromovCompactness

end
