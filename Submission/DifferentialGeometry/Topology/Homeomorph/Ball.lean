import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace Homeomorph
open _root_.Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Homeomorph in
theorem mapsTo_ball_of_image_sphere_eq {F : Type*} [PseudoMetricSpace F]
    (D : E ≃ₜ F) {c : E} {d : F} {r s : ℝ}
    (hr : 0 < r) (hsphere : D '' _root_.Metric.sphere c r = _root_.Metric.sphere d s)
    (hc : D c ∈ _root_.Metric.ball d s) : _root_.Set.MapsTo D (_root_.Metric.ball c r) (_root_.Metric.ball d s) := by
  intro x hx
  by_contra hn
  have hnx : s ≤ _root_.Dist.dist (D x) d := le_of_not_gt hn
  obtain ⟨y, hy, hyD⟩ := (convex_ball c r).isPreconnected.intermediate_value
    (_root_.Metric.mem_ball_self hr) hx (D.continuous.dist continuous_const).continuousOn
    (show s ∈ _root_.Set.Icc (_root_.Dist.dist (D c) d) (_root_.Dist.dist (D x) d) from ⟨hc.le, hnx⟩)
  have hyS : D y ∈ _root_.Metric.sphere d s := hyD
  obtain ⟨z, hz, hzy⟩ := hsphere.symm.subset hyS
  have hzy' := D.injective hzy
  subst z
  exact (mem_ball.mp hy).ne (mem_sphere.mp hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.mapsTo_ball_of_image_sphere_eq then
    throwError "Refusing to shadow existing declaration Homeomorph.mapsTo_ball_of_image_sphere_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.mapsTo_ball_of_image_sphere_eq ``Submission.Homeomorph.mapsTo_ball_of_image_sphere_eq

open _root_.Homeomorph in
theorem image_closedBall_of_image_sphere_eq_of_map_center
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (D : E ≃ₜ F)
    {c : E} {d : F} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hsphere : D '' _root_.Metric.sphere c r = _root_.Metric.sphere d s) (hc : D c = d) :
    D '' _root_.Metric.closedBall c r = _root_.Metric.closedBall d s := by
  have hball : D '' _root_.Metric.ball c r = _root_.Metric.ball d s := by
    apply Subset.antisymm
    · exact (D.mapsTo_ball_of_image_sphere_eq hr hsphere
        (by rw [hc]; exact _root_.Metric.mem_ball_self hs)).image_subset
    · intro y hy
      have hiS : D.symm '' _root_.Metric.sphere d s = _root_.Metric.sphere c r := by
        rw [← hsphere, _root_.Set.image_image]
        simp only [D.symm_apply_apply, _root_.Set.image_id']
      have hc' : D.symm d = c := by rw [← hc, D.symm_apply_apply]
      exact ⟨D.symm y,
        D.symm.mapsTo_ball_of_image_sphere_eq hs hiS (by rw [hc']; exact _root_.Metric.mem_ball_self hr) hy,
        D.apply_symm_apply y⟩
  rw [← closure_ball c hr.ne', D.image_closure, hball, closure_ball d hs.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.image_closedBall_of_image_sphere_eq_of_map_center then
    throwError "Refusing to shadow existing declaration Homeomorph.image_closedBall_of_image_sphere_eq_of_map_center"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.image_closedBall_of_image_sphere_eq_of_map_center ``Submission.Homeomorph.image_closedBall_of_image_sphere_eq_of_map_center

end Homeomorph
