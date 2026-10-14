import Submission.DifferentialGeometry.Analysis.Calculus.Retraction.Ball
import Mathlib.Topology.ContinuousMap.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.Topology
namespace DifferentialGeometry.Topology.ClosedBall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (a : E) {r : ℝ} (hr : 0 ≤ r)

def retraction : C(E, _root_.Metric.closedBall a r) := by
  refine ⟨fun x => ⟨a + DifferentialGeometry.Analysis.Calculus.ballRetraction r (x - a), ?_⟩, ?_⟩
  · rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact DifferentialGeometry.Analysis.Calculus.ballRetraction_mem_closedBall hr _
  · exact (continuous_const.add
      ((DifferentialGeometry.Analysis.Calculus.lipschitzWith_ballRetraction hr).continuous.comp
        (continuous_id.sub continuous_const))).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction


@[simp]
theorem retraction_apply (x : E) :
    (retraction a hr x : E) = a + _root_.Min.min 1 (r / ‖x - a‖) • (x - a) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction_apply ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction_apply


theorem retraction_apply_of_mem {x : E} (hx : x ∈ _root_.Metric.closedBall a r) :
    (retraction a hr x : E) = x := by
  change a + DifferentialGeometry.Analysis.Calculus.ballRetraction r (x - a) = x
  rw [DifferentialGeometry.Analysis.Calculus.ballRetraction_eq_self_of_mem
    (by simpa only [_root_.Metric.mem_closedBall, dist_eq_norm] using hx)]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction_apply_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction_apply_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction_apply_of_mem ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction_apply_of_mem


@[simp]
theorem retraction_coe (x : _root_.Metric.closedBall a r) : retraction a hr (x : E) = x :=
  Subtype.ext (retraction_apply_of_mem a hr x.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction_coe ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction_coe


theorem retraction_leftInverse : Function.LeftInverse (retraction a hr)
    (Subtype.val : _root_.Metric.closedBall a r → E) := retraction_coe a hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction_leftInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction_leftInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction_leftInverse ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction_leftInverse


theorem dist_retraction_center (x : E) :
    dist (retraction a hr x : E) a = _root_.Min.min (_root_.Dist.dist x a) r := by
  by_cases hx : x ∈ _root_.Metric.closedBall a r
  · rw [retraction_apply_of_mem a hr hx, min_eq_left hx]
  · have hlt : r < ‖x - a‖ := lt_of_not_ge (by simpa only [_root_.Metric.mem_closedBall, dist_eq_norm] using hx)
    have hnorm : 0 < ‖x - a‖ := hr.trans_lt hlt
    have hfactor : r / ‖x - a‖ ≤ 1 := (div_le_one hnorm).mpr hlt.le
    rw [retraction_apply, dist_eq_norm, add_sub_cancel_left, min_eq_right hfactor,
      norm_smul, Real.norm_of_nonneg (div_nonneg hr (norm_nonneg _)),
      div_mul_cancel₀ _ hnorm.ne', dist_eq_norm, min_eq_right hlt.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.dist_retraction_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.dist_retraction_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.dist_retraction_center ``Submission.DifferentialGeometry.Topology.ClosedBall.dist_retraction_center


theorem retraction_mem_sphere {x : E} (hx : r ≤ _root_.Dist.dist x a) :
    (retraction a hr x : E) ∈ _root_.Metric.sphere a r := by
  rw [_root_.Metric.mem_sphere, dist_retraction_center, min_eq_right hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere


theorem retraction_mem_sphere_of_not_mem {x : E} (hx : x ∉ _root_.Metric.closedBall a r) :
    (retraction a hr x : E) ∈ _root_.Metric.sphere a r :=
  retraction_mem_sphere a hr (le_of_lt (lt_of_not_ge hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere_of_not_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere_of_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere_of_not_mem ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction_mem_sphere_of_not_mem

theorem retraction_eventuallyEq_id {x : E} (hx : x ∈ _root_.Metric.ball a r) :
    (fun y => (retraction a hr y : E)) =ᶠ[𝓝 x] id := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact retraction_apply_of_mem a hr (_root_.Metric.ball_subset_closedBall hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedBall.retraction_eventuallyEq_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedBall.retraction_eventuallyEq_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedBall.retraction_eventuallyEq_id ``Submission.DifferentialGeometry.Topology.ClosedBall.retraction_eventuallyEq_id

end DifferentialGeometry.Topology.ClosedBall
