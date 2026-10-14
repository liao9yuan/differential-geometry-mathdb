import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallPairTransport
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Collar
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.QuotientTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.E3 target :: scope.openDecls } }

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [TopologicalSpace N] [ChartedSpace E3 N]
  (c d : BallChart 3 (𝓡 3) M) (c' d' : BallChart 3 (𝓡 3) N)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (F : M ≃ₜ N)
  (hc : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = c'.chart x)
  (hd : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (d.chart x) = d'.chart x)

private theorem chart_image_ball_eq (e : BallChart 3 (𝓡 3) M) (e' : BallChart 3 (𝓡 3) N)
    (he : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (e.chart x) = e'.chart x) :
    F '' (e.chart '' Metric.ball 0 1) = e'.chart '' Metric.ball 0 1 := by
  rw [Set.image_image]
  exact Set.image_congr (fun x hx => he x (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) hx))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.chart_image_ball_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.chart_image_ball_eq target :: scope.openDecls } }

def coreHomeomorph : c.DoublePunctured d ≃ₜ c'.DoublePunctured d' :=
  F.subtype (fun x => by
    have himg : F '' (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1) =
        c'.chart '' Metric.ball 0 1 ∪ d'.chart '' Metric.ball 0 1 := by
      rw [Set.image_union, chart_image_ball_eq F c c' hc, chart_image_ball_eq F d d' hd]
    change x ∉ c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1 ↔
      F x ∉ c'.chart '' Metric.ball 0 1 ∪ d'.chart '' Metric.ball 0 1
    rw [← himg, F.injective.mem_set_image])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph

theorem coreHomeomorph_firstBoundary (z : Sphere (n := 3)) :
    coreHomeomorph c d c' d' F hc hd (c.firstBoundaryMap d hcd z) = c'.firstBoundaryMap d' hcd' z :=
  Subtype.ext (hc z (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.property]; norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_firstBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_firstBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_firstBoundary ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_firstBoundary

theorem coreHomeomorph_secondBoundary (z : Sphere (n := 3)) :
    coreHomeomorph c d c' d' F hc hd (c.secondBoundaryMap d hcd z) = c'.secondBoundaryMap d' hcd' z :=
  Subtype.ext (hd z (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.property]; norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_secondBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_secondBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_secondBoundary ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_secondBoundary

variable (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

def homeomorphOfChartTransport : Quotient c d hcd a ≃ₜ Quotient c' d' hcd' a :=
  adjunctionSpaceHomeomorphOfHomeomorph boundaryInclusion (attachingMap c d hcd a)
    boundaryInclusion (attachingMap c' d' hcd' a)
    (Homeomorph.refl _) (Homeomorph.refl _) (coreHomeomorph c d c' d' F hc hd)
    (fun _ => rfl) (by
      rintro ⟨b, z⟩
      cases b
      · exact coreHomeomorph_firstBoundary c d c' d' hcd hcd' F hc hd z
      · exact coreHomeomorph_secondBoundary c d c' d' hcd hcd' F hc hd (a z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport

theorem homeomorphOfChartTransport_core (x : c.DoublePunctured d) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (coreInclusion c d hcd a x) =
      coreInclusion c' d' hcd' a (coreHomeomorph c d c' d' F hc hd x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_core ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_core

theorem homeomorphOfChartTransport_band (x : Band (n := 3)) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (bandInclusion c d hcd a x) =
      bandInclusion c' d' hcd' a x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_band ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_band

private theorem coreHomeomorph_firstRadial (z : Sphere (n := 3)) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    coreHomeomorph c d c' d' F hc hd (c.firstRadialMap d hcd z r hr) =
      c'.firstRadialMap d' hcd' z r hr := by
  apply Subtype.ext
  apply hc
  rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
  exact hr.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_firstRadial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_firstRadial target :: scope.openDecls } }

private theorem coreHomeomorph_secondRadial (z : Sphere (n := 3)) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    coreHomeomorph c d c' d' F hc hd (c.secondRadialMap d hcd z r hr) =
      c'.secondRadialMap d' hcd' z r hr := by
  apply Subtype.ext
  apply hd
  rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
  exact hr.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_secondRadial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.coreHomeomorph_secondRadial target :: scope.openDecls } }

theorem homeomorphOfChartTransport_lowerCollar (p : CollarDomain) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (lowerCollar c d hcd a p) =
      lowerCollar c' d' hcd' a p := by
  by_cases ht : p.2.val ≤ 0
  · rw [lowerCollar_of_nonpos c d hcd a p ht, lowerCollar_of_nonpos c' d' hcd' a p ht,
      homeomorphOfChartTransport_core]
    exact congrArg (coreInclusion c' d' hcd' a)
      (coreHomeomorph_firstRadial c d c' d' hcd hcd' F hc hd p.1 (1 - p.2.val) _)
  · rw [lowerCollar_of_pos c d hcd a p (not_le.mp ht), lowerCollar_of_pos c' d' hcd' a p (not_le.mp ht),
      homeomorphOfChartTransport_band]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_lowerCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_lowerCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_lowerCollar ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_lowerCollar

theorem homeomorphOfChartTransport_upperCollar (p : CollarDomain) :
    homeomorphOfChartTransport c d c' d' hcd hcd' F hc hd a (upperCollar c d hcd a p) =
      upperCollar c' d' hcd' a p := by
  by_cases ht : 0 ≤ p.2.val
  · rw [upperCollar_of_nonneg c d hcd a p ht, upperCollar_of_nonneg c' d' hcd' a p ht,
      homeomorphOfChartTransport_core]
    exact congrArg (coreInclusion c' d' hcd' a)
      (coreHomeomorph_secondRadial c d c' d' hcd hcd' F hc hd (a p.1) (1 + p.2.val) _)
  · rw [upperCollar_of_neg c d hcd a p (not_le.mp ht), upperCollar_of_neg c' d' hcd' a p (not_le.mp ht),
      homeomorphOfChartTransport_band]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_upperCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_upperCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_upperCollar ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfChartTransport_upperCollar

end DifferentialGeometry.Topology.SelfAttachment
