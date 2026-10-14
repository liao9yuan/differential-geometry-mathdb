import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Defs
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarking

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

namespace OrientedBallChart

universe u

variable {M : ClosedOrientedManifold.{u} 3} (c d : OrientedBallChart M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))

def doubleMarking : BallMarking M Bool where
  ball b := if b then d else c
  reserve_disjoint := by
    intro b e h
    cases b <;> cases e
    · exact False.elim (h rfl)
    · exact hdisj.mono_right (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num)))
    · exact hdisj.symm.mono_right (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num)))
    · exact False.elim (h rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.doubleMarking then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.doubleMarking"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.doubleMarking ``Submission.DifferentialGeometry.Topology.OrientedBallChart.doubleMarking

theorem doubleMarking_ballImages :
    (c.doubleMarking d hdisj).ballImages =
      c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1 := by
  ext x
  simp only [BallMarking.ballImages, BallMarking.ballImage, doubleMarking, _root_.Set.mem_iUnion,
    _root_.Set.mem_union]
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (hc | hd)
    · exact ⟨false, hc⟩
    · exact ⟨true, hd⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.doubleMarking_ballImages then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.doubleMarking_ballImages"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.doubleMarking_ballImages ``Submission.DifferentialGeometry.Topology.OrientedBallChart.doubleMarking_ballImages

include hdisj in
theorem isPathConnected_doublePunctured [ConnectedSpace M.Carrier] :
    IsPathConnected ((c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ : Set M.Carrier) := by
  rw [← c.doubleMarking_ballImages d hdisj]
  exact (c.doubleMarking d hdisj).isPathConnected_ballImages_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.isPathConnected_doublePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.isPathConnected_doublePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.isPathConnected_doublePunctured ``Submission.DifferentialGeometry.Topology.OrientedBallChart.isPathConnected_doublePunctured

include hdisj in
theorem pathConnectedSpace_doublePunctured [ConnectedSpace M.Carrier] :
    PathConnectedSpace (c.toBallChart.DoublePunctured d.toBallChart) :=
  isPathConnected_iff_pathConnectedSpace.mp (c.isPathConnected_doublePunctured d hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.pathConnectedSpace_doublePunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.pathConnectedSpace_doublePunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.pathConnectedSpace_doublePunctured ``Submission.DifferentialGeometry.Topology.OrientedBallChart.pathConnectedSpace_doublePunctured

end OrientedBallChart

namespace SelfAttachment

universe u

variable {M : ClosedOrientedManifold.{u} 3} [ConnectedSpace M.Carrier]
  (c d : OrientedBallChart M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

theorem pathConnectedSpace_quotient :
    PathConnectedSpace (Quotient c.toBallChart d.toBallChart hdisj a) := by
  let _ : PathConnectedSpace (c.toBallChart.DoublePunctured d.toBallChart) :=
    c.pathConnectedSpace_doublePunctured d hdisj
  let _ : PathConnectedSpace (Sphere (n := 3)) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one)
  let _ : PathConnectedSpace (_root_.Set.Icc (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  exact pathConnectedSpace_adjunctionSpace _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.pathConnectedSpace_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.pathConnectedSpace_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.pathConnectedSpace_quotient ``Submission.DifferentialGeometry.Topology.SelfAttachment.pathConnectedSpace_quotient

theorem connectedSpace_quotient :
    ConnectedSpace (Quotient c.toBallChart d.toBallChart hdisj a) := by
  let _ := pathConnectedSpace_quotient c d hdisj a
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.connectedSpace_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.connectedSpace_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.connectedSpace_quotient ``Submission.DifferentialGeometry.Topology.SelfAttachment.connectedSpace_quotient

end SelfAttachment
end DifferentialGeometry.Topology
