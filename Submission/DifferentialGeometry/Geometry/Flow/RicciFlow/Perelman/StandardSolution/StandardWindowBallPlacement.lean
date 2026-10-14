import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.Distance.LocalBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (I3)

private theorem norm_le_of_edist_le {Λ c L : ℝ} (hΛ : 1 ≤ Λ) (hc : 1 ≤ c) (hL : 0 ≤ L)
    (g : SmoothRiemannianMetric I3 (EuclideanSpace ℝ (Fin 3)))
    (hup : ∀ (y : EuclideanSpace ℝ (Fin 3)) (v : TangentSpace I3 y),
      StandardCap.metric.inner y v v ≤ Λ * g.inner y v v)
    {z y : EuclideanSpace ℝ (Fin 3)}
    (hzy : riemannianEDistOf (I := I3) g z y ≤ ENNReal.ofReal (Real.sqrt c * L)) :
    ‖y‖ ≤ ‖z‖ + 2 * c * Λ * (L + 1) := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hcap := edistOf_le_of_quad (I := I3) g StandardCap.metric hΛ0 hup z y
  have htri := riemannianEDistOf_triangle (I := I3) StandardCap.metric 0 z y
  rw [StandardCap.edist_zero, StandardCap.edist_zero] at htri
  have hmul : riemannianEDistOf (I := I3) StandardCap.metric z y ≤
      ENNReal.ofReal (Real.sqrt Λ * (Real.sqrt c * L)) := by
    refine hcap.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact mul_le_mul' le_rfl hzy
  have hsum := htri.trans (add_le_add le_rfl hmul)
  rw [← ENNReal.ofReal_add (norm_nonneg _) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hsum
  have hsΛ : Real.sqrt Λ ≤ Λ := by
    rw [Real.sqrt_le_left hΛ0.le]
    nlinarith
  have hsc : Real.sqrt c ≤ c := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h1 : Real.sqrt Λ * (Real.sqrt c * L) ≤ Λ * (c * L) :=
    mul_le_mul hsΛ (mul_le_mul_of_nonneg_right hsc hL) (by positivity) hΛ0.le
  have hcΛ : 0 ≤ c * Λ := by positivity
  nlinarith [mul_nonneg hcΛ hL]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.norm_le_of_edist_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.norm_le_of_edist_le target :: scope.openDecls } }

theorem StandardSolution.exists_ball_placement {Θ : ℝ} (hΘ : Θ < 1) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ (Q : StandardSolution) (T : ℝ), T ∈ _root_.Set.Icc 0 Θ →
      ∀ (L : ℝ) (z : EuclideanSpace ℝ (Fin 3)), 0 ≤ L →
        IsCompact (riemannianClosedBallOf (I := I3) (Q.val.metric T) z L) ∧
          ∀ y ∈ riemannianClosedBallOf (I := I3) (Q.val.metric T) z L,
            ‖y‖ ≤ ‖z‖ + Λ * (L + 1) := by
  set Θp := _root_.Max.max Θ 0 with hΘp
  have hΘp0 : 0 ≤ Θp := le_max_right _ _
  have hΘp1 : Θp < 1 := max_lt hΘ zero_lt_one
  have hlt : ENNReal.ofReal Θp < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hΘp1
  obtain ⟨Λ, hΛ, hcmp⟩ := uniformStandardLifetime_metricComparison Θp hΘp0 hlt
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  refine ⟨2 * Λ, by linarith, ?_⟩
  intro Q T hT L z hL
  have hTp : T ∈ _root_.Set.Icc 0 Θp := ⟨hT.1, hT.2.trans (le_max_left _ _)⟩
  have hup : ∀ (y : EuclideanSpace ℝ (Fin 3)) (v : TangentSpace I3 y),
      StandardCap.metric.inner y v v ≤ Λ * (Q.val.metric T).inner y v v := by
    intro y v
    have h := ((hcmp Q T hTp).2 y v).1
    rwa [inv_mul_le_iff₀ hΛ0] at h
  have hplace : ∀ y ∈ riemannianClosedBallOf (I := I3) (Q.val.metric T) z L,
      ‖y‖ ≤ ‖z‖ + 2 * Λ * (L + 1) := by
    intro y hy
    have h := norm_le_of_edist_le (c := 1) hΛ le_rfl hL (Q.val.metric T) hup
      (by rw [Real.sqrt_one, one_mul]; exact hy)
    linarith
  refine ⟨?_, hplace⟩
  exact (_root_.ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (‖z‖ + 2 * Λ * (L + 1))).of_isClosed_subset
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
    (fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hplace y hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_ball_placement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_ball_placement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_ball_placement ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_ball_placement

theorem StandardSolution.exists_window_ball_placement {Θ : ℝ} (hΘ : Θ < 1) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ (D L : ℝ) (z : standardCapWindow D), 0 ≤ L →
      ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) < D + 1 →
      ∀ (Q : StandardSolution) (T : ℝ), T ∈ _root_.Set.Icc 0 Θ →
      ∀ g : SmoothRiemannianMetric I3 (standardCapWindow D),
        (∀ y (v : TangentSpace I3 y),
          (1 / 2) * ((Q.val.metric T).restrictOpen (standardCapWindow D)).inner y v v ≤
            g.inner y v v) →
        IsCompact (riemannianClosedBallOf (I := I3) g z L) ∧
          ∀ y ∈ riemannianClosedBallOf (I := I3) g z L,
            ‖(y : EuclideanSpace ℝ (Fin 3))‖ ≤ ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) := by
  set Θp := _root_.Max.max Θ 0 with hΘp
  have hΘp0 : 0 ≤ Θp := le_max_right _ _
  have hΘp1 : Θp < 1 := max_lt hΘ zero_lt_one
  have hlt : ENNReal.ofReal Θp < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hΘp1
  obtain ⟨Λ, hΛ, hcmp⟩ := uniformStandardLifetime_metricComparison Θp hΘp0 hlt
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  refine ⟨4 * Λ, by linarith, ?_⟩
  intro D L z hL hroom Q T hT g hg
  have hTp : T ∈ _root_.Set.Icc 0 Θp := ⟨hT.1, hT.2.trans (le_max_left _ _)⟩
  have hup : ∀ (y : EuclideanSpace ℝ (Fin 3)) (v : TangentSpace I3 y),
      StandardCap.metric.inner y v v ≤ Λ * (Q.val.metric T).inner y v v := by
    intro y v
    have h := ((hcmp Q T hTp).2 y v).1
    rwa [inv_mul_le_iff₀ hΛ0] at h
  have hplace : ∀ y ∈ riemannianClosedBallOf (I := I3) g z L,
      ‖(y : EuclideanSpace ℝ (Fin 3))‖ ≤ ‖(z : EuclideanSpace ℝ (Fin 3))‖ + 4 * Λ * (L + 1) := by
    intro y hy
    have hrestr := edistOf_le_of_quad (I := I3) g
      ((Q.val.metric T).restrictOpen (standardCapWindow D)) (c := 2) (by norm_num)
      (fun w v => by linarith [hg w v]) z y
    have hamb := riemannianEDistOf_le_restrictOpen (I := I3) (Q.val.metric T)
      (standardCapWindow D) z y
    have hzy : riemannianEDistOf (I := I3) (Q.val.metric T) (z : EuclideanSpace ℝ (Fin 3))
        (y : EuclideanSpace ℝ (Fin 3)) ≤ ENNReal.ofReal (Real.sqrt 2 * L) := by
      refine hamb.trans (hrestr.trans ?_)
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact mul_le_mul' le_rfl hy
    have h := norm_le_of_edist_le hΛ (by norm_num) hL (Q.val.metric T) hup hzy
    linarith
  refine ⟨?_, hplace⟩
  set c := ‖(z : EuclideanSpace ℝ (Fin 3))‖ + 4 * Λ * (L + 1) with hc
  have hK : IsCompact {y : standardCapWindow D | ‖(y : EuclideanSpace ℝ (Fin 3))‖ ≤ c} := by
    rw [Subtype.isCompact_iff]
    have himg : ((↑) : standardCapWindow D → EuclideanSpace ℝ (Fin 3)) ''
        {y : standardCapWindow D | ‖(y : EuclideanSpace ℝ (Fin 3))‖ ≤ c} =
        Metric.closedBall 0 c := by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hy
      · intro hw
        rw [Metric.mem_closedBall, dist_zero_right] at hw
        have hmem : w ∈ standardCapWindow D := by
          change ‖w‖ < D + 1
          linarith
        exact ⟨⟨w, hmem⟩, hw, rfl⟩
    rw [himg]
    exact _root_.ProperSpace.isCompact_closedBall _ _
  exact hK.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hplace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_window_ball_placement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_window_ball_placement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_window_ball_placement ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_window_ball_placement

end DifferentialGeometry.PDE.RicciFlow
