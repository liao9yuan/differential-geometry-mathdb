import Submission.DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowFlowPushforward

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Submission.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem ball_subset_image_capWindow_of_scaled_lower {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) {D : ℝ} (Ξ : standardCapWindow D → M)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (hinj : _root_.Function.Injective Ξ)
    (z₀ : standardCapWindow D) {r lam Lc : ℝ} (hr : 0 < r) (hlam : 0 < lam) (hLc : 0 < Lc)
    (hroom : ‖z₀.val‖ + r < D + 1)
    (hlower : ∀ (u : standardCapWindow D) (v : TangentSpace ThreeModel u),
      (StandardCap.metric.restrictOpen (standardCapWindow D)).inner u v v ≤
        Lc ^ 2 * (localPullMetric (scaleMetric lam hlam g) Ξ hΞ).inner u v v) :
    riemannianBallOf g (Ξ z₀) (r / (Lc * Real.sqrt lam)) ⊆
      Ξ '' {u : standardCapWindow D | ‖u.val‖ ≤ ‖z₀.val‖ + r} := by
  have hradial : riemannianClosedBallOf StandardCap.metric z₀.val r ⊆
      {y : ThreeSpace | ‖y‖ ≤ ‖z₀.val‖ + r} := by
    intro y hy
    have hd := (StandardCap.radial_difference_le_edist z₀.val y).trans hy
    have hab := (ENNReal.ofReal_le_ofReal_iff hr.le).mp hd
    change ‖y‖ ≤ ‖z₀.val‖ + r
    linarith [le_abs_self (‖y‖ - ‖z₀.val‖)]
  have hsource : riemannianClosedBallOf StandardCap.metric z₀.val r ⊆
      (standardCapWindow D : Set ThreeSpace) := fun y hy => by
    change ‖y‖ < D + 1
    exact (hradial hy).trans_lt hroom
  have hcompact : IsCompact (riemannianClosedBallOf StandardCap.metric z₀.val r) :=
    StandardCap.isCompact_metric_closedBall z₀.val r.toNNReal
  have hcap := DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
    (scaleMetric lam hlam g) StandardCap.metric (standardCapWindow D) Ξ hΞ hinj z₀ hr hLc
    hcompact hsource fun u _ v => by
      have h := hlower u v
      rwa [localPullMetric_inner] at h
  have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hrad : Real.sqrt lam * (r / (Lc * Real.sqrt lam)) = r / Lc := by
    field_simp
  intro y hy
  rw [← riemannianBallOf_scaleMetric lam hlam g, hrad] at hy
  obtain ⟨u, hu, rfl⟩ := hcap hy
  exact ⟨u, hradial hu, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ball_subset_image_capWindow_of_scaled_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ball_subset_image_capWindow_of_scaled_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ball_subset_image_capWindow_of_scaled_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ball_subset_image_capWindow_of_scaled_lower

universe u

theorem ObservedHistory.ball_subset_image_backwardSurvivor_capWindow (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) {s : ℝ}
    (G : (H.stage last).IncomingSlab (H.time last) s)
    (g : SmoothRiemannianMetric ThreeModel (H.stage last).Carrier) {D : ℝ}
    (Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (hinj : _root_.Function.Injective Ξ)
    (z₀ : standardCapWindow D) {r lam Lc : ℝ} (hr : 0 < r) (hlam : 0 < lam) (hLc : 0 < Lc)
    (hroom : ‖z₀.val‖ + r < D + 1)
    (hlower : ∀ (u : standardCapWindow D) (v : TangentSpace ThreeModel u),
      (StandardCap.metric.restrictOpen (standardCapWindow D)).inner u v v ≤
        Lc ^ 2 * (localPullMetric (scaleMetric lam hlam g) (fun w => (Ξ w).val.val)
          (H.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val first last hle G hΞ)).inner
            u v v) :
    riemannianBallOf g (Ξ z₀).val.val (r / (Lc * Real.sqrt lam)) ⊆
      (fun w => (Ξ w).val.val) '' {u : standardCapWindow D | ‖u.val‖ ≤ ‖z₀.val‖ + r} :=
  ball_subset_image_capWindow_of_scaled_lower g (fun w => (Ξ w).val.val)
    (H.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val first last hle G hΞ)
    (H.injective_backwardSurvivorIncomingDomain_val_val first last hle G hinj) z₀ hr hlam hLc
    hroom hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ball_subset_image_backwardSurvivor_capWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ball_subset_image_backwardSurvivor_capWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ball_subset_image_backwardSurvivor_capWindow ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ball_subset_image_backwardSurvivor_capWindow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
