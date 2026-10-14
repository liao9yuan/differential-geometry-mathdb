import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Transport

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))
  [ChartedSpace E3 (Quotient c d hcd a)]
  (e : BallChart 3 (𝓡 3) M) (e' : BallChart 3 (𝓡 3) (Quotient c d hcd a))
  (he : ∀ x ∈ Metric.closedBall (0 : E3) 2,
    ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
      e'.chart x = coreInclusion c d hcd a ⟨e.chart x, hx⟩)

private theorem ball_subset_closedBall_two {x : E3} (hx : x ∈ Metric.ball (0 : E3) 1) :
    x ∈ Metric.closedBall (0 : E3) 2 :=
  Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.ball_subset_closedBall_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.ball_subset_closedBall_two target :: scope.openDecls } }

include he in
theorem preimage_coreInclusion_retained_ball :
    coreInclusion c d hcd a ⁻¹' (e'.chart '' Metric.ball 0 1) =
      {x : c.DoublePunctured d | x.val ∈ e.chart '' Metric.ball 0 1} := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    rw [hmap] at hzx
    have hh := coreInclusion_injective c d hcd a hzx
    exact ⟨z, hz, congrArg (fun y : c.DoublePunctured d => y.val) hh⟩
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    exact ⟨z, hz, hmap.trans (congrArg (coreInclusion c d hcd a) (Subtype.ext hzx))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_ball ``Submission.DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_ball

include he in
theorem preimage_bandInclusion_retained_ball
    (havoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) :
    bandInclusion c d hcd a ⁻¹' (e'.chart '' Metric.ball 0 1) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p
  rintro ⟨z, hz, hzp⟩
  obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
  rw [hmap] at hzp
  obtain ⟨⟨b, w⟩, _, hbw⟩ := (bandInclusion_eq_coreInclusion_iff c d hcd a p ⟨e.chart z, hz'⟩).mp hzp.symm
  have hbw' := congrArg (fun y : c.DoublePunctured d => y.val) hbw
  cases b
  · exact havoid z (ball_subset_closedBall_two hz) (Or.inl
      ⟨w, Metric.sphere_subset_closedBall w.property, hbw'⟩)
  · exact havoid z (ball_subset_closedBall_two hz) (Or.inr
      ⟨a w, Metric.sphere_subset_closedBall (a w).property, hbw'⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_ball ``Submission.DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_ball

include he in
theorem retained_ball_eq_coreInclusion_image :
    e'.chart '' Metric.ball 0 1 =
      coreInclusion c d hcd a '' {x : c.DoublePunctured d | x.val ∈ e.chart '' Metric.ball 0 1} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    exact ⟨⟨e.chart z, hz'⟩, ⟨z, hz, rfl⟩, hmap.symm⟩
  · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    obtain ⟨hz', hmap⟩ := he z (ball_subset_closedBall_two hz)
    exact ⟨z, hz, hmap.trans (congrArg (coreInclusion c d hcd a) (Subtype.ext hzx))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.retained_ball_eq_coreInclusion_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.retained_ball_eq_coreInclusion_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.retained_ball_eq_coreInclusion_image ``Submission.DifferentialGeometry.Topology.SelfAttachment.retained_ball_eq_coreInclusion_image


include he in
theorem preimage_coreInclusion_retained_closedBall :
    coreInclusion c d hcd a ⁻¹' (e'.chart '' Metric.closedBall 0 1) =
      {x : c.DoublePunctured d | x.val ∈ e.chart '' Metric.closedBall 0 1} := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
    rw [hmap] at hzx
    have hh := coreInclusion_injective c d hcd a hzx
    exact ⟨z, hz, congrArg (fun y : c.DoublePunctured d => y.val) hh⟩
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨hz', hmap⟩ := he z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
    exact ⟨z, hz, hmap.trans (congrArg (coreInclusion c d hcd a) (Subtype.ext hzx))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_closedBall ``Submission.DifferentialGeometry.Topology.SelfAttachment.preimage_coreInclusion_retained_closedBall

include he in
theorem preimage_bandInclusion_retained_closedBall
    (havoid : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) :
    bandInclusion c d hcd a ⁻¹' (e'.chart '' Metric.closedBall 0 1) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p
  rintro ⟨z, hz, hzp⟩
  obtain ⟨hz', hmap⟩ := he z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz)
  rw [hmap] at hzp
  obtain ⟨⟨b, w⟩, _, hbw⟩ := (bandInclusion_eq_coreInclusion_iff c d hcd a p ⟨e.chart z, hz'⟩).mp hzp.symm
  have hbw' := congrArg (fun y : c.DoublePunctured d => y.val) hbw
  cases b
  · exact havoid z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz) (Or.inl
      ⟨w, Metric.sphere_subset_closedBall w.property, hbw'⟩)
  · exact havoid z (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hz) (Or.inr
      ⟨a w, Metric.sphere_subset_closedBall (a w).property, hbw'⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_closedBall ``Submission.DifferentialGeometry.Topology.SelfAttachment.preimage_bandInclusion_retained_closedBall

end DifferentialGeometry.Topology.SelfAttachment
