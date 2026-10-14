import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.DivergenceMaximumPrinciple
import Submission.DifferentialGeometry.Topology.PlanarJordan.DiskAlternatingCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ContDiff _root_.ENNReal

namespace DeGiorgi
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Topology.PlanarJordan

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem IsSolution.not_local_alternating_cross_of_coordinate_boundary
    {R : ℝ} (hR : 0 < R) {A : EllipticCoeff 2 (Metric.ball (0 : V) R)} {u v : V → ℝ}
    (hu : IsSolution A u) (B : SmoothEllipticBilinearForm 2 (_root_.Set.univ : Set V))
    (hAB : _root_.Set.EqOn A.a B.a (Metric.ball (0 : V) R))
    (hv : ContDiffOn ℝ 2 v (Metric.ball (0 : V) R))
    (hc : ContinuousOn v (Metric.closedBall (0 : V) R))
    (huv : u =ᵐ[volume.restrict (Metric.ball (0 : V) R)] v)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x 0)
    (e : OpenPartialHomeomorph (ℝ × ℝ) V)
    (he : (0 : ℝ × ℝ) ∈ e.source) (heR : e (0, 0) ∈ Metric.ball (0 : V) R)
    {η : ℝ} (hη : 0 < η)
    (hpositive : ∀ t : ℝ, 0 < |t| → |t| < η → v (e (0, 0)) < v (e (t, 0)))
    (hnegative : ∀ t : ℝ, 0 < |t| → |t| < η → v (e (0, t)) < v (e (0, 0))) : False := by
  apply not_local_alternating_cross_of_disk_maximum_minimum_principle hR hc hbd
    (fun S hS _ hsub a hfront => ?_) (fun S hS _ hsub a hfront => ?_)
    e he heR hη hpositive hnegative
  · apply hu.le_on_relatively_open_closedBall_of_le_frontier hR B hAB hv hc huv hS
      (fun x hx => ?_) hfront
    have hne : ‖(x : V)‖ ≠ R := hsub hx
    have hle : ‖(x : V)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    simpa using lt_of_le_of_ne hle hne
  · apply hu.le_on_relatively_open_closedBall_of_frontier_le hR B hAB hv hc huv hS
      (fun x hx => ?_) hfront
    have hne : ‖(x : V)‖ ≠ R := hsub hx
    have hle : ‖(x : V)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    simpa using lt_of_le_of_ne hle hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.IsSolution.not_local_alternating_cross_of_coordinate_boundary then
    throwError "Refusing to shadow existing declaration DeGiorgi.IsSolution.not_local_alternating_cross_of_coordinate_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.IsSolution.not_local_alternating_cross_of_coordinate_boundary ``Submission.DeGiorgi.IsSolution.not_local_alternating_cross_of_coordinate_boundary

end DeGiorgi

end

end
