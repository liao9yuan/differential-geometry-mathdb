import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PresentedStaticCapHistory
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalBlowup
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem isCompact_standardCapWindow_norm_le (D : ℝ) :
    IsCompact {y : standardCapWindow D | ‖y.val‖ ≤ D} := by
  rw [Subtype.isCompact_iff]
  have himage : Subtype.val '' {y : standardCapWindow D | ‖y.val‖ ≤ D} =
      Metric.closedBall (0 : ThreeSpace) D := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      have hz' : ‖z‖ ≤ D := by simpa using hz
      exact ⟨⟨z, show ‖z‖ < D + 1 by linarith⟩, hz', rfl⟩
  rw [himage]
  exact _root_.ProperSpace.isCompact_closedBall 0 D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_standardCapWindow_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_standardCapWindow_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_standardCapWindow_norm_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isCompact_standardCapWindow_norm_le

namespace MetricCutCapEvent.PresentedStaticCap

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
  (S : E.PresentedStaticCap fixed D m ε b)

theorem metricDerivNorm_window_lt {i : ℕ} (hi : i ≤ m) (x : standardCapWindow D)
    (hx : ‖x.val‖ < D) :
    metricDerivNorm i S.witness.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) x < ε := by
  have hclose := S.witness.window_closeness
  rw [standardCapMetric_eq_metric] at hclose
  obtain ⟨C, -, hC⟩ := metricDerivNorm_bddOn (isCompact_standardCapWindow_norm_le D) m
    S.witness.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow D))
    (StandardCap.metric.restrictOpen (standardCapWindow D))
  have hbdd : BddAbove {r : ℝ | ∃ a' : ℕ, a' ≤ m ∧ ∃ y : standardCapWindow D,
      y ∈ {y : standardCapWindow D | ‖y.val‖ < D} ∧
      metricDerivNorm a' S.witness.windowMetric
        (StandardCap.metric.restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) y = r} := by
    refine ⟨C, ?_⟩
    rintro r ⟨a', ha', y, hy, rfl⟩
    exact hC a' ha' y (show ‖y.val‖ ≤ D from le_of_lt hy)
  exact (le_csSup hbdd ⟨i, hi, x, hx, rfl⟩).trans_lt hclose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricDerivNorm_window_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricDerivNorm_window_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricDerivNorm_window_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricDerivNorm_window_lt

theorem window_isLocalDiffeomorph : IsLocalDiffeomorph ThreeModel ThreeModel ∞ S.window :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv S.window
    S.window_smooth.contMDiff
    (fun p => (S.window_smooth.isImmersion.isImmersionAt p).injective_mfderiv (by simp)) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_isLocalDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.window_isLocalDiffeomorph

theorem curvDerivNormSq_output_window (i : ℕ) (x : standardCapWindow D) :
    curvDerivNormSq i E.outputMetric (S.window x) =
      S.neck.scale ^ (i + 2) * curvDerivNormSq i S.witness.windowMetric x :=
  curvDerivNormSq_eq_of_scaled_local_isometry S.witness.windowMetric E.outputMetric S.window
    S.window_isLocalDiffeomorph S.neck.scale_pos S.window_inner i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.curvDerivNormSq_output_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.curvDerivNormSq_output_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.curvDerivNormSq_output_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.curvDerivNormSq_output_window

theorem metricScalarAt_output_window (x : standardCapWindow D) :
    metricScalarAt E.outputMetric (S.window x) =
      S.neck.scale * metricScalarAt S.witness.windowMetric x := by
  have hq := S.neck.scale_pos
  have hg : S.witness.windowMetric = localPullMetric (scaleMetric S.neck.scale hq E.outputMetric)
      S.window S.window_isLocalDiffeomorph := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, scaleMetric_inner]
    exact S.window_inner y v w
  rw [hg, metricScalarAt_localPullMetric_scaleMetric, ← mul_assoc, mul_inv_cancel₀ hq.ne',
    one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricScalarAt_output_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricScalarAt_output_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricScalarAt_output_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.PresentedStaticCap.metricScalarAt_output_window

end MetricCutCapEvent.PresentedStaticCap

theorem exists_presentedStaticCap_window_curvature_bounds :
    ∃ ε₀ c B : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 ≤ B ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
        {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}
        (S : E.PresentedStaticCap fixed D m ε b), ε ≤ ε₀ → 4 ≤ m →
      ∀ x : standardCapWindow D, ‖x.val‖ < D →
        c * S.neck.scale ≤ metricScalarAt E.outputMetric (S.window x) ∧
        ∀ i ≤ 2, curvDerivNormSq i E.outputMetric (S.window x) ≤ B * S.neck.scale ^ (i + 2) := by
  obtain ⟨S₀⟩ := standard_solution_nonempty
  obtain ⟨ε₀, A₀, hε₀, hA₀, hjet₀⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      0 le_rfl zero_lt_one 0
  obtain ⟨ε₁, A₁, hε₁, hA₁, hjet₁⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      0 le_rfl zero_lt_one 1
  obtain ⟨ε₂, A₂, hε₂, hA₂, hjet₂⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      0 le_rfl zero_lt_one 2
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison 0 le_rfl zero_lt_one
  obtain ⟨c₀, hc₀, hscalar₀⟩ := exists_standard_scalar_lower_bound
  set B : ℝ := A₀ + A₁ + A₂ with hBdef
  set δ : ℝ := _root_.Min.min (_root_.Min.min ε₀ ε₁) (_root_.Min.min ε₂ eta) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hε₀ hε₁) (lt_min hε₂ heta)
  refine ⟨δ, c₀ / 2, B, hδ, by positivity, by positivity, ?_⟩
  intro P Q a s E fixed D ε m b S hε hm x hx
  have h0 : (0 : ℝ) ∈ _root_.Set.Icc 0 0 := ⟨le_rfl, le_rfl⟩
  have hsmall : ∀ i ≤ 4, metricDerivNorm i S.witness.windowMetric
      ((S₀.val.metric 0).restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) x ≤ δ := by
    intro i hi
    rw [S₀.val.initial]
    exact ((S.metricDerivNorm_window_lt (hi.trans hm) x hx).trans_le hε).le
  have hjS : ∀ i ≤ 2, curvDerivNormSq i S.witness.windowMetric x ≤ B := by
    intro i hi
    interval_cases i
    · have h := hjet₀ _ S.witness.windowMetric S₀ 0 h0 x fun i hi =>
        (hsmall i (by omega)).trans ((min_le_left _ _).trans (min_le_left _ _))
      linarith only [h, hBdef, hA₁, hA₂]
    · have h := hjet₁ _ S.witness.windowMetric S₀ 0 h0 x fun i hi =>
        (hsmall i (by omega)).trans ((min_le_left _ _).trans (min_le_right _ _))
      linarith only [h, hBdef, hA₀, hA₂]
    · have h := hjet₂ _ S.witness.windowMetric S₀ 0 h0 x fun i hi =>
        (hsmall i (by omega)).trans ((min_le_right _ _).trans (min_le_left _ _))
      linarith only [h, hBdef, hA₀, hA₁]
  have hRS : c₀ / 2 ≤ metricScalarAt S.witness.windowMetric x := by
    have h := (hlower S₀ (standardCapWindow D) S.witness.windowMetric 0 h0 x fun i hi =>
      (hsmall i (by omega)).trans ((min_le_right _ _).trans (min_le_right _ _))).2
    rw [metricScalarAt_restrictOpen] at h
    have hQ := hscalar₀ S₀ x.val 0 ⟨le_rfl, zero_lt_one⟩
    rw [sub_zero, div_one] at hQ
    linarith only [h, hQ]
  have hq := S.neck.scale_pos
  refine ⟨?_, fun i hi => ?_⟩
  · rw [S.metricScalarAt_output_window x, mul_comm (c₀ / 2)]
    exact mul_le_mul_of_nonneg_left hRS hq.le
  · rw [S.curvDerivNormSq_output_window i x, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hjS i hi) (pow_nonneg hq.le _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presentedStaticCap_window_curvature_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presentedStaticCap_window_curvature_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presentedStaticCap_window_curvature_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_presentedStaticCap_window_curvature_bounds

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
