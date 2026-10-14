import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Smooth
import Submission.DifferentialGeometry.Topology.Manifold.OrientedBallChartOpenImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SmoothSelfAttachment

universe u
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SmoothSelfAttachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SmoothSelfAttachment.E3 target :: scope.openDecls } }

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment} (s : SmoothSelfAttachment c d hcd a)

theorem exists_orientedBallChart_core (e : OrientedBallChart M.toClosedOrientedManifold)
    (havoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) :
    ∃ e' : OrientedBallChart s.toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : E3) 2,
        ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
          e'.chart x = SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph ⟨e.chart x, hx⟩ := by
  let _ := s.charts
  let _ := s.smooth
  let f : SelfAttachment.coreInterior c.toBallChart d.toBallChart → s.toConnectedClosedOrientedManifold.Carrier :=
    SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph
  have hi : _root_.Function.Injective f := by
    intro x y h
    have he := SelfAttachment.coreInclusion_injective c.toBallChart d.toBallChart hcd a.val.toHomeomorph h
    exact Subtype.ext (congrArg (fun q : c.toBallChart.DoublePunctured d.toBallChart => q.val) he)
  have hU : ∀ x ∈ Metric.closedBall (0 : E3) 2, e.chart x ∈ SelfAttachment.coreInterior c.toBallChart d.toBallChart := havoid
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f := s.core_localDiffeomorph
  have hfo : ∀ x, Orientation.map (Fin 3) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (M.orientation.orientation x.val) = s.toConnectedClosedOrientedManifold.orientation.orientation (f x) :=
    s.core_preserves_orientation
  obtain ⟨e', he'⟩ := OrientedBallChart.exists_orientedBallChart_of_open_embedding
    (M := M.toClosedOrientedManifold) (N := s.toConnectedClosedOrientedManifold.toClosedOrientedManifold)
    e (SelfAttachment.coreInterior c.toBallChart d.toBallChart) f hf hi hfo hU
  refine ⟨e', ?_⟩
  intro x hx
  refine ⟨(SelfAttachment.coreInteriorToCore c.toBallChart d.toBallChart ⟨e.chart x, hU x hx⟩).property, ?_⟩
  exact he' x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core ``Submission.DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core

theorem exists_orientedBallChart_core_image {ι : Type*}
    (e : ι → OrientedBallChart M.toClosedOrientedManifold)
    (havoid : ∀ i x, x ∈ Metric.closedBall (0 : E3) 2 →
      (e i).chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) :
    ∃ e' : ι → OrientedBallChart s.toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      ∀ i x, x ∈ Metric.closedBall (0 : E3) 2 →
        ∃ hx : (e i).chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
          (e' i).chart x = SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph ⟨(e i).chart x, hx⟩ := by
  choose e' he' using fun i => s.exists_orientedBallChart_core (e i) (havoid i)
  exact ⟨e', he'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core_image ``Submission.DifferentialGeometry.Topology.SmoothSelfAttachment.exists_orientedBallChart_core_image

end DifferentialGeometry.Topology.SmoothSelfAttachment
