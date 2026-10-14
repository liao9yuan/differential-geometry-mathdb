import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Transport
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction

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
private local instance _root_.Submission.DifferentialGeometry.Topology.SelfAttachment.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  (c d c' d' : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (B : E3 ≃ₗᵢ[ℝ] E3)
  (hc : ∀ x ∈ Metric.closedBall (0 : E3) 2, c'.chart x = c.chart (B x))
  (hd : ∀ x ∈ Metric.closedBall (0 : E3) 2, d'.chart x = d.chart (B x))

private theorem chart_ball_image_of_isometry
    (e e' : BallChart 3 (𝓡 3) M)
    (he : ∀ x ∈ Metric.closedBall (0 : E3) 2, e'.chart x = e.chart (B x)) :
    e'.chart '' Metric.ball 0 1 = e.chart '' Metric.ball 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx2 : x ∈ Metric.closedBall (0 : E3) 2 :=
      Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hx)
    exact ⟨B x, by simpa only [Metric.mem_ball, dist_zero_right, B.norm_map] using hx, (he x hx2).symm⟩
  · rintro ⟨x, hx, rfl⟩
    have hy : B.symm x ∈ Metric.ball (0 : E3) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right, B.symm.norm_map] using hx
    refine ⟨B.symm x, hy, ?_⟩
    rw [he _ (Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hy)), B.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.chart_ball_image_of_isometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.chart_ball_image_of_isometry target :: scope.openDecls } }

def angularCoreHomeomorph : c'.DoublePunctured d' ≃ₜ c.DoublePunctured d :=
  Homeomorph.setCongr (by
    rw [chart_ball_image_of_isometry B c c' hc, chart_ball_image_of_isometry B d d' hd])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.angularCoreHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.angularCoreHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.angularCoreHomeomorph ``Submission.DifferentialGeometry.Topology.SelfAttachment.angularCoreHomeomorph

variable (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))
  (ha : ∀ z : Sphere (n := 3),
    DifferentialGeometry.Geometry.sphereDiffeo (n := 2) B (a z) =
      a (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) B z))

def homeomorphOfAngularTransport : Quotient c' d' hcd' a ≃ₜ Quotient c d hcd a := by
  let b := (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) B).toHomeomorph
  apply adjunctionSpaceHomeomorphOfHomeomorph boundaryInclusion (attachingMap c' d' hcd' a)
    boundaryInclusion (attachingMap c d hcd a)
    ((Homeomorph.refl Bool).prodCongr b) (b.prodCongr (Homeomorph.refl (_root_.Set.Icc (0 : ℝ) 1)))
    (angularCoreHomeomorph c d c' d' B hc hd)
  · rintro ⟨q, z⟩
    cases q <;> rfl
  · rintro ⟨q, z⟩
    cases q
    · apply Subtype.ext
      exact hc z (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.property]; norm_num)
    · apply Subtype.ext
      change d'.chart (a z).val = d.chart (a (b z)).val
      rw [hd _ (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp (a z).property]; norm_num)]
      exact congrArg d.chart (congrArg Subtype.val (ha z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport

theorem homeomorphOfAngularTransport_core (x : c'.DoublePunctured d') :
    homeomorphOfAngularTransport c d c' d' hcd hcd' B hc hd a ha (coreInclusion c' d' hcd' a x) =
      coreInclusion c d hcd a (angularCoreHomeomorph c d c' d' B hc hd x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_core ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_core

theorem homeomorphOfAngularTransport_band (x : Band (n := 3)) :
    homeomorphOfAngularTransport c d c' d' hcd hcd' B hc hd a ha (bandInclusion c' d' hcd' a x) =
      bandInclusion c d hcd a (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) B x.1, x.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_band ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_band


private theorem angularCoreHomeomorph_firstRadial (z : Sphere (n := 3)) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    angularCoreHomeomorph c d c' d' B hc hd (c'.firstRadialMap d' hcd' z r hr) =
      c.firstRadialMap d hcd (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) B z) r hr := by
  apply Subtype.ext
  change c'.chart (r • z.val) = c.chart (r • B z.val)
  rw [hc _ (by
    rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2), map_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.angularCoreHomeomorph_firstRadial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.angularCoreHomeomorph_firstRadial target :: scope.openDecls } }

private def angularCollar (p : CollarDomain) : CollarDomain :=
  (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) B p.1, p.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.angularCollar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.angularCollar target :: scope.openDecls } }

theorem homeomorphOfAngularTransport_lowerCollar (p : CollarDomain) :
    homeomorphOfAngularTransport c d c' d' hcd hcd' B hc hd a ha (lowerCollar c' d' hcd' a p) =
      lowerCollar c d hcd a (angularCollar B p) := by
  by_cases ht : p.2.val ≤ 0
  · rw [lowerCollar_of_nonpos c' d' hcd' a p ht,
      lowerCollar_of_nonpos c d hcd a (angularCollar B p) ht, homeomorphOfAngularTransport_core]
    exact congrArg (coreInclusion c d hcd a)
      (angularCoreHomeomorph_firstRadial c d c' d' hcd hcd' B hc hd p.1 (1 - p.2.val) _)
  · rw [lowerCollar_of_pos c' d' hcd' a p (not_le.mp ht),
      lowerCollar_of_pos c d hcd a (angularCollar B p) (not_le.mp ht), homeomorphOfAngularTransport_band]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_lowerCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_lowerCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_lowerCollar ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_lowerCollar

theorem homeomorphOfAngularTransport_upperCollar (p : CollarDomain) :
    homeomorphOfAngularTransport c d c' d' hcd hcd' B hc hd a ha (upperCollar c' d' hcd' a p) =
      upperCollar c d hcd a (angularCollar B p) := by
  by_cases ht : 0 ≤ p.2.val
  · rw [upperCollar_of_nonneg c' d' hcd' a p ht,
      upperCollar_of_nonneg c d hcd a (angularCollar B p) ht, homeomorphOfAngularTransport_core]
    apply congrArg (coreInclusion c d hcd a)
    apply Subtype.ext
    change d'.chart ((1 + p.2.val) • (a p.1).val) =
      d.chart ((1 + p.2.val) • (a (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) B p.1)).val)
    rw [hd _ (by
      rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial (a p.1) (by linarith)]
      linarith [p.2.property.2]), map_smul]
    exact congrArg (fun z : Sphere (n := 3) => d.chart ((1 + p.2.val) • z.val)) (ha p.1)
  · rw [upperCollar_of_neg c' d' hcd' a p (not_le.mp ht),
      upperCollar_of_neg c d hcd a (angularCollar B p) (not_le.mp ht), homeomorphOfAngularTransport_band]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_upperCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_upperCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_upperCollar ``Submission.DifferentialGeometry.Topology.SelfAttachment.homeomorphOfAngularTransport_upperCollar

end DifferentialGeometry.Topology.SelfAttachment
