import Submission.DifferentialGeometry.Topology.Planar.PolygonDisk
import Submission.DifferentialGeometry.Topology.Planar.CanonicalRounding
import Submission.DifferentialGeometry.Topology.PlanarJordan.InnermostDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

theorem smooth_schoenflies
    {f : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ f) :
    ∃ Φ : Schoenflies.Plane ≃ₘ[ℝ] Schoenflies.Plane,
      Φ '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range f ∧
      Φ '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range f) ∧
      Φ '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (_root_.Set.range f)) := by
  obtain ⟨m, P, e, U, r, d, s, R, ε, φ, _, hnorm, hc, hdisj, hKU, hε, hR,
      _, hφ, _⟩ := Planar.exists_diffeomorph_finite_vertex_rounding hf
  obtain ⟨Ψ, hΨ⟩ := P.exists_diffeomorph_vertex_rounding e U r d s (fun _ => ε) R hnorm
    (fun i => (hc i).1) (fun i => (hc i).2.2.1) (fun i => (hc i).2.2.2.1)
    (fun _ => hε) hR hKU hdisj (fun i => (hc i).2.2.2.2)
  have hboundary : Ψ '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = φ '' _root_.Set.range f := by
    rw [← frontier_closedBall (0 : Schoenflies.Plane) (by norm_num : (1 : ℝ) ≠ 0)]
    change Ψ.toHomeomorph '' frontier (_root_.Metric.closedBall (0 : Schoenflies.Plane) 1) = _
    rw [Ψ.toHomeomorph.image_frontier, Diffeomorph.coe_toHomeomorph, hΨ, hφ]
  let Φ := Ψ.trans φ.symm
  have hΦ : Φ '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range f := by
    change (fun x => φ.symm (Ψ x)) '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range f
    rw [← _root_.Set.image_image, hboundary]
    exact φ.symm_image_image (_root_.Set.range f)
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · have h := image_ball_eq_inside_image_sphere Φ.toHomeomorph 0 zero_lt_one
    simpa only [Diffeomorph.coe_toHomeomorph, hΦ] using h
  · have h := image_closedBall_eq_closure_inside_image_sphere Φ.toHomeomorph 0 zero_lt_one
    simpa only [Diffeomorph.coe_toHomeomorph, hΦ] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.smooth_schoenflies then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.smooth_schoenflies"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.smooth_schoenflies ``Submission.DifferentialGeometry.Topology.PlanarJordan.smooth_schoenflies

end DifferentialGeometry.Topology.PlanarJordan
