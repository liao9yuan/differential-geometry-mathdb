import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCoreFrontierDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornChainBackwardTraces
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSeparationSliceTransfer

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem false_of_inv_sqrt_quarter_bound {R C a : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (ha : 0 ≤ a)
    (h : (Real.sqrt (R / (4 * (1 + C * a) ^ 2)))⁻¹ - (Real.sqrt R)⁻¹ ≤
      C / 2 * (a / Real.sqrt R)) : False := by
  have hCa : 0 ≤ C * a := mul_nonneg hC ha
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsq : Real.sqrt (R / (4 * (1 + C * a) ^ 2)) = Real.sqrt R / (2 * (1 + C * a)) := by
    rw [Real.sqrt_div hR.le, show (4 * (1 + C * a) ^ 2) = (2 * (1 + C * a)) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hsq, inv_div] at h
  have h2 : (2 * (1 + C * a) / Real.sqrt R - (Real.sqrt R)⁻¹) * Real.sqrt R ≤
      C / 2 * (a / Real.sqrt R) * Real.sqrt R := mul_le_mul_of_nonneg_right h hsR.le
  rw [sub_mul, div_mul_cancel₀ _ hsR.ne', inv_mul_cancel₀ hsR.ne', mul_assoc,
    div_mul_cancel₀ _ hsR.ne'] at h2
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.false_of_inv_sqrt_quarter_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.false_of_inv_sqrt_quarter_bound target :: scope.openDecls } }

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem quarter_scalar_le_on_closedBall_of_gradientBoundBefore {Cgrad : ℝ≥0} {q ρ τ : ℝ}
    (hgrad : G.GradientBoundBefore Cgrad q s) (hτ : τ ∈ _root_.Set.Ioo a s) (hq0 : 0 < q) (hρ : 0 ≤ ρ)
    (x : P.Carrier) (hq : q < G.flow.scalar τ x / (4 * (1 + Cgrad * ρ) ^ 2)) :
    ∀ w ∈ riemannianClosedBallOf (G.flow.base.metric τ) x
      (ρ / Real.sqrt (G.flow.scalar τ x)),
      G.flow.scalar τ x / (4 * (1 + Cgrad * ρ) ^ 2) ≤ G.flow.scalar τ w := by
  intro w hw
  have hCρ : 0 ≤ (Cgrad : ℝ) * ρ := mul_nonneg Cgrad.coe_nonneg hρ
  have hpos : 0 < G.flow.scalar τ x / (4 * (1 + Cgrad * ρ) ^ 2) := hq0.trans hq
  have hR : 0 < G.flow.scalar τ x := by
    by_contra hneg
    have : G.flow.scalar τ x / (4 * (1 + Cgrad * ρ) ^ 2) ≤ 0 :=
      div_nonpos_iff.mpr (Or.inr ⟨not_lt.mp hneg, by positivity⟩)
    linarith
  by_contra hlt
  have hkey :=
    Perelman.CanonicalNeighborhood.inv_sqrt_sub_inv_sqrt_scalar_le_of_threshold_gradient_bound
    G.flow Cgrad.coe_nonneg hq (fun z hz v => hgrad z τ hτ hz v)
    (div_le_self hR.le (by nlinarith)) (not_le.mp hlt).le (by positivity) hw
  exact false_of_inv_sqrt_quarter_bound hR Cgrad.coe_nonneg hρ hkey

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.quarter_scalar_le_on_closedBall_of_gradientBoundBefore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.quarter_scalar_le_on_closedBall_of_gradientBoundBefore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.quarter_scalar_le_on_closedBall_of_gradientBoundBefore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.quarter_scalar_le_on_closedBall_of_gradientBoundBefore

theorem TerminalLimitMetric.quarter_scalar_le_on_ball_of_gradientBoundBefore
    (L : G.TerminalLimitMetric) {Cgrad : ℝ≥0} {q ρ : ℝ} (hgrad : G.GradientBoundBefore Cgrad q s)
    (hq0 : 0 < q) (hρ : 0 ≤ ρ) (x : G.terminalRegularOpen)
    (hq : q < metricScalarAt L.metric x / (4 * (1 + Cgrad * ρ) ^ 2)) :
    ∀ w : G.terminalRegularOpen,
      riemannianEDistOf L.metric x w <
        ENNReal.ofReal (ρ / Real.sqrt (metricScalarAt L.metric x)) →
      metricScalarAt L.metric x / (4 * (1 + Cgrad * ρ) ^ 2) ≤ metricScalarAt L.metric w := by
  intro w hw
  have hCρ : 0 ≤ (Cgrad : ℝ) * ρ := mul_nonneg Cgrad.coe_nonneg hρ
  have hpos : 0 < metricScalarAt L.metric x / (4 * (1 + Cgrad * ρ) ^ 2) := hq0.trans hq
  have hR : 0 < metricScalarAt L.metric x := by
    by_contra hneg
    have : metricScalarAt L.metric x / (4 * (1 + Cgrad * ρ) ^ 2) ≤ 0 :=
      div_nonpos_iff.mpr (Or.inr ⟨not_lt.mp hneg, by positivity⟩)
    linarith
  by_contra hlt
  have hkey := L.inv_sqrt_sub_inv_sqrt_scalar_le_of_gradientBoundBefore hgrad hq
    (div_lt_self hR (by nlinarith)) (not_le.mp hlt) hw
  exact false_of_inv_sqrt_quarter_bound hR Cgrad.coe_nonneg hρ hkey

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.quarter_scalar_le_on_ball_of_gradientBoundBefore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.quarter_scalar_le_on_ball_of_gradientBoundBefore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.quarter_scalar_le_on_ball_of_gradientBoundBefore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.quarter_scalar_le_on_ball_of_gradientBoundBefore

theorem TerminalLimitMetric.scalar_le_on_slice_ball_of_image_closedBall
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) {r Q η τ : ℝ} (hr : 0 < r)
    (hL : ∀ w : G.terminalRegularOpen,
      riemannianEDistOf L.metric x w < ENNReal.ofReal (2 * r) → metricScalarAt L.metric w ≤ Q)
    (hsub : riemannianBallOf (G.flow.base.metric τ) x.val (16 * r / 17) ⊆
      Subtype.val '' riemannianClosedBallOf L.metric x r)
    (hclose : ∀ w ∈ riemannianClosedBallOf L.metric x r,
      |metricScalarAt (G.flow.base.metric τ) w.val - metricScalarAt L.metric w| < η) :
    ∀ z ∈ riemannianBallOf (G.flow.base.metric τ) x.val (16 * r / 17),
      G.flow.scalar τ z ≤ Q + η := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hsub hz
  have h1 := abs_lt.mp (hclose w hw)
  have h2 := hL w (lt_of_le_of_lt hw ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    (by linarith)))
  change metricScalarAt (G.flow.base.metric τ) w.val ≤ Q + η
  linarith [h1.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_on_slice_ball_of_image_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_on_slice_ball_of_image_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_on_slice_ball_of_image_closedBall ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.scalar_le_on_slice_ball_of_image_closedBall

end OrientedThreeStage.IncomingSlab

namespace TerminalCorePresentation

theorem riemannianBallOf_subset_hornHalfRange {D : OneStepIncoming.{u}} {ε Λ : ℝ}
    (P : TerminalCorePresentation D ε Λ) {c : ConnectedComponents D.slab.terminalRegularOpen}
    (hc : c ∈ P.component) {e : P.hornIndex c} {x : D.slab.terminalRegularOpen}
    (hx : x ∈ P.hornHalfRange c e) {r : ℝ} (hr : 0 < r)
    (hscal : ∀ y ∈ riemannianBallOf D.terminal.metric x r,
      Λ * (P.coreRadius ^ 2)⁻¹ < metricScalarAt D.terminal.metric y) :
    riemannianBallOf D.terminal.metric x r ⊆ P.hornHalfRange c e :=
  P.subset_hornHalfRange_of_isPreconnected_of_scalar_gt hc hx
    (IsPathConnected.isConnected
      (DifferentialGeometry.isPathConnected_riemannianBallOf D.terminal.metric x hr)).isPreconnected
    (by
      change riemannianEDistOf _ x x < _
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hr) hscal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.riemannianBallOf_subset_hornHalfRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.riemannianBallOf_subset_hornHalfRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.riemannianBallOf_subset_hornHalfRange ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation.riemannianBallOf_subset_hornHalfRange

end TerminalCorePresentation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
