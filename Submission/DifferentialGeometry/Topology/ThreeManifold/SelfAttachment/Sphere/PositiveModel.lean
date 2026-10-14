import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.StereographicBallChartOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.AngularTransport
import Submission.DifferentialGeometry.Topology.Manifold.ClosedOrientedPullback
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Sphere.Antipodal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

private theorem chart_closedBall_image_of_common_isometry
    (B : E3 ≃ₗᵢ[ℝ] E3) (c c' : BallChart 3 (𝓡 3) S3)
    (h : ∀ x, c'.chart x = c.chart (B x)) :
    c'.chart '' Metric.closedBall 0 1 = c.chart '' Metric.closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨B x, by simpa only [Metric.mem_closedBall, dist_zero_right, B.norm_map] using hx, (h x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨B.symm x, by simpa only [Metric.mem_closedBall, dist_zero_right, B.symm.norm_map] using hx, ?_⟩
    rw [h, B.apply_symm_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.chart_closedBall_image_of_common_isometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.chart_closedBall_image_of_common_isometry target :: scope.openDecls } }

private theorem sphereIsometry_comm_antipodal (B : E3 ≃ₗᵢ[ℝ] E3) (z : S2) :
    Geometry.sphereDiffeo (n := 2) B (antipodalAttachment z) =
      antipodalAttachment (Geometry.sphereDiffeo (n := 2) B z) := by
  apply Subtype.ext
  exact map_neg B z.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sphereIsometry_comm_antipodal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sphereIsometry_comm_antipodal target :: scope.openDecls } }

def positiveSphereAttachmentHomeomorph (P : S3)
    (c d : OrientedBallChart standardThreeSphere.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
    (B : E3 ≃ₗᵢ[ℝ] E3)
    (hc : ∀ x, c.chart x = (stereographicSmallBallChart P).chart (B x))
    (hd : ∀ x, d.chart x = (oppositeStereographicSmallBallChart P).chart (B x)) :
    SelfAttachment.Quotient c.toBallChart d.toBallChart hcd antipodalAttachment.toHomeomorph ≃ₜ
      SphereSelfAttachment P antipodalAttachment :=
  SelfAttachment.homeomorphOfAngularTransport (stereographicSmallBallChart P)
    (oppositeStereographicSmallBallChart P) c.toBallChart d.toBallChart
    (stereographicSmallBallChart_disjoint P) hcd B (fun x _ => hc x) (fun x _ => hd x)
    antipodalAttachment.toHomeomorph (sphereIsometry_comm_antipodal B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.positiveSphereAttachmentHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.positiveSphereAttachmentHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.positiveSphereAttachmentHomeomorph ``Submission.DifferentialGeometry.Topology.positiveSphereAttachmentHomeomorph

theorem exists_positive_sphere_selfAttachment_model (P : S3) :
    ∃ (c d : OrientedBallChart standardThreeSphere.toClosedOrientedManifold)
      (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)),
      ∃ (D : ℝ ≃ₘ[ℝ] ℝ) (hI : D '' _root_.Set.Icc (0 : ℝ) 1 = _root_.Set.Icc (0 : ℝ) 1)
        (h0 : D 0 = 0) (h1 : D 1 = 1),
      ∃ B : E3 ≃ₗᵢ[ℝ] E3,
      ∃ hc : ∀ x, c.chart x = (stereographicSmallBallChart P).chart (B x),
      ∃ hd : ∀ x, d.chart x = (oppositeStereographicSmallBallChart P).chart (B x),
      let _ := sphereSelfAttachmentStandardCharts P antipodalAttachment D hI h0 h1
        sphereMappingTorusIsotopyRefl sphereMappingTorusIsotopyRefl_target
      ∃ O : ManifoldOrientation (𝓡 3) (SphereSelfAttachment P antipodalAttachment) 3,
      let Q := sphereSelfAttachmentManifold P antipodalAttachment D hI h0 h1 sphereMappingTorusIsotopyRefl
        sphereMappingTorusIsotopyRefl_target O
      let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
      ∃ F : ClosedOrientedManifold.OrientedDiffeomorph (Q.pullback H).toClosedOrientedManifold
        sphereTwoTimesCircleLift.toClosedOrientedManifold,
        ∀ e : OrientedBallChart standardThreeSphere.toClosedOrientedManifold,
          (∀ x ∈ Metric.closedBall (0 : E3) 2,
            e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1) →
          ∃ e' : OrientedBallChart sphereTwoTimesCircleLift.toClosedOrientedManifold,
            ∀ x ∈ Metric.closedBall (0 : E3) 2,
              ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
                e'.chart x = F.val (SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd
                  antipodalAttachment.toHomeomorph ⟨e.chart x, hx⟩) := by
  obtain ⟨B, _, c, d, hc, hd, _, hcd⟩ := exists_oriented_stereographic_small_ballCharts P
  obtain ⟨D, hI, h0, h1, _, _, O, _, F₀, hmark⟩ := exists_antipodalSelfAttachment_oriented_model P
  refine ⟨c, d, hcd, D, hI, h0, h1, B, hc, hd, O, ?_⟩
  let Q := sphereSelfAttachmentManifold P antipodalAttachment D hI h0 h1 sphereMappingTorusIsotopyRefl
    sphereMappingTorusIsotopyRefl_target O
  let H := positiveSphereAttachmentHomeomorph P c d hcd B hc hd
  let F := (Q.pullbackOrientedDiffeomorph H).trans F₀
  refine ⟨F, ?_⟩
  intro e he
  have heRaw : ∀ x ∈ Metric.closedBall (0 : E3) 2,
      e.chart x ∉ (stereographicSmallBallChart P).chart '' Metric.closedBall 0 1 ∪
        (oppositeStereographicSmallBallChart P).chart '' Metric.closedBall 0 1 := by
    intro x hx
    rw [← chart_closedBall_image_of_common_isometry B (stereographicSmallBallChart P) c.toBallChart hc,
      ← chart_closedBall_image_of_common_isometry B (oppositeStereographicSmallBallChart P) d.toBallChart hd]
    exact he x hx
  obtain ⟨e', he'⟩ := hmark e heRaw
  refine ⟨e', ?_⟩
  intro x hx
  obtain ⟨hcore, hval⟩ := he' x hx
  have hxK : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ := by
    rintro (h | h)
    · exact he x hx (Or.inl (Set.image_mono Metric.ball_subset_closedBall h))
    · exact he x hx (Or.inr (Set.image_mono Metric.ball_subset_closedBall h))
  refine ⟨hxK, hval.trans ?_⟩
  change F₀.val (sphereSelfAttachmentCoreMap P antipodalAttachment D hI ⟨e.chart x, hcore⟩) =
    F₀.val (H (SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd
      antipodalAttachment.toHomeomorph ⟨e.chart x, hxK⟩))
  apply congrArg F₀.val
  obtain ⟨hraw, hmap⟩ := sphereSelfAttachmentCoreMap_eq P antipodalAttachment D hI ⟨e.chart x, hcore⟩
  rw [hmap]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_positive_sphere_selfAttachment_model then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_positive_sphere_selfAttachment_model"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_positive_sphere_selfAttachment_model ``Submission.DifferentialGeometry.Topology.exists_positive_sphere_selfAttachment_model

end DifferentialGeometry.Topology
