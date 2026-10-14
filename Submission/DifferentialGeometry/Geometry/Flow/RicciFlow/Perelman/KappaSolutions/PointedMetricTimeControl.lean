import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimMetricTimeControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarCompactControl
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance pointedTimeTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeTopology target :: scope.openDecls } }
private local instance pointedTimeCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeCharted target :: scope.openDecls } }
private local instance pointedTimeSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeSmooth target :: scope.openDecls } }
private local instance pointedTimeC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeC1 target :: scope.openDecls } }
private local instance pointedTimeT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeT2 target :: scope.openDecls } }

private local instance pointedTimeMetricTopology
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricTopology target :: scope.openDecls } }
private local instance pointedTimeMetricCharted
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricCharted target :: scope.openDecls } }
private local instance pointedTimeMetricSmooth
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricSmooth target :: scope.openDecls } }
private local instance pointedTimeMetricC1
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricC1 target :: scope.openDecls } }
private local instance pointedTimeMetricT2
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedTimeMetricT2 target :: scope.openDecls } }

theorem exists_pointed_metric_time_modulus_on_compact
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (C : MetricConvergenceData (I := I) (Phi.atTime (L := L) 0))
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) 0) k)
    (K : Set L.M) (hK : IsCompact K) (a : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ i in _root_.Filter.atTop, K ⊆ Phi.source i ∧
      ∀ s ∈ _root_.Set.Icc a 0, ∀ t ∈ _root_.Set.Icc a 0, ∀ x ∈ K, ∀ v : TangentSpace I x,
        |((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) -
          ((X.term (phi i)).S.base.metric s).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v)| ≤
          B * (L.S.base.metric 0).inner x v v * |t - s| := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    have hdim := (hsource 0).dimension_ge_two
    omega⟩
  obtain ⟨C0, hC0, hscalar⟩ := exists_pointed_scalar_bound_on_compact C hcanonical K hK
  have href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    intro k
    rw [hcanonical k]
    rfl
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control
    C href K hK 1 zero_lt_one
  refine ⟨2 * C0 * Real.exp (C0 * (-a)), by positivity, ?_⟩
  filter_upwards [hscalar, Filter.eventually_ge_atTop k0] with i hi hik
  refine ⟨hi.1, fun s hs t ht x hx v => ?_⟩
  have hquad := (hk0 i hik).2 x hx v
  have hterminal : ((X.term (phi i)).S.base.metric 0).inner (Phi.map i x)
      (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) ≤
        2 * (L.S.base.metric 0).inner x v v := by
    have hupper := (abs_le.mp hquad).2
    change ((X.term (phi i)).S.base.metric 0).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) -
      (L.S.base.metric 0).inner x v v ≤ (1 : ℝ) * (L.S.base.metric 0).inner x v v at hupper
    linarith
  have hscalarSource : (X.term (phi i)).S.scalar 0 (Phi.map i x) ≤ C0 :=
    (le_abs_self _).trans (hi.2 x hx)
  have htime := (hsource (phi i)).metric_inner_time_difference_le
    hs ht (Phi.map i x) hscalarSource (mfderiv I I (Phi.map i) x v)
  apply htime.trans
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hterminal
      (by positivity : 0 ≤ C0 * Real.exp (C0 * (-a)))) (abs_nonneg (t - s))
  convert hmul using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_time_modulus_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_time_modulus_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_time_modulus_on_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_metric_time_modulus_on_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
