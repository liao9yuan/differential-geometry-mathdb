import Submission.DifferentialGeometry.Geometry.Measure.Area.Manifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Metric
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem riemannianArea_congr_on_open (g : SmoothRiemannianMetric I M)
    {u v : ℂ → M} {s : Set ℂ} (hs : IsOpen s) (huv : _root_.Set.EqOn u v s) :
    riemannianArea g u s = riemannianArea g v s := by
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hs.measurableSet] with z hz
  exact riemannianAreaDensity_congr g (huv.eventuallyEq_of_mem (hs.mem_nhds hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_congr_on_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_congr_on_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_congr_on_open ``Submission.DifferentialGeometry.Geometry.riemannianArea_congr_on_open


theorem riemannianArea_closedBall_eq_ball (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) (z : ℂ) (r : ℝ) :
    riemannianArea g u (_root_.Metric.closedBall z r) = riemannianArea g u (_root_.Metric.ball z r) := by
  unfold riemannianArea
  apply _root_.MeasureTheory.setIntegral_congr_set
  have hs : ∀ᵐ w : ℂ ∂volume, w ∉ _root_.Metric.sphere z r := by
    rw [_root_.MeasureTheory.ae_iff]
    convert MeasureTheory.Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume z r using 1
    congr 1
    ext w
    simp
  filter_upwards [hs] with w hw
  exact propext (by
    change _root_.Dist.dist w z ≤ r ↔ _root_.Dist.dist w z < r
    exact ⟨fun h => lt_of_le_of_ne h hw, le_of_lt⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_closedBall_eq_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_closedBall_eq_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_closedBall_eq_ball ``Submission.DifferentialGeometry.Geometry.riemannianArea_closedBall_eq_ball



theorem riemannianArea_congr_on_closedBall (g : SmoothRiemannianMetric I M)
    {u v : ℂ → M} {z : ℂ} {r : ℝ} (huv : _root_.Set.EqOn u v (_root_.Metric.closedBall z r)) :
    riemannianArea g u (_root_.Metric.closedBall z r) = riemannianArea g v (_root_.Metric.closedBall z r) := by
  rw [riemannianArea_closedBall_eq_ball, riemannianArea_closedBall_eq_ball]
  exact riemannianArea_congr_on_open g _root_.Metric.isOpen_ball (huv.mono _root_.Metric.ball_subset_closedBall)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_congr_on_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_congr_on_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_congr_on_closedBall ``Submission.DifferentialGeometry.Geometry.riemannianArea_congr_on_closedBall

end DifferentialGeometry.Geometry
