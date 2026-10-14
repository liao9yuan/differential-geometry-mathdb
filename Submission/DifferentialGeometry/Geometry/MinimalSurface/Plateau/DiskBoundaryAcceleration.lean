import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantChain
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalConnection
import Mathlib.MeasureTheory.Integral.CircleIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.InnerProductSpace
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem diskMapBoundaryAcceleration_inner_radial
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q) (θ : ℝ) :
    let c := circleMap 0 1
    g.inner (U (c θ))
      (covDerivAlong g (U ∘ c) (fun r => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ c) r (1 : ℝ)) θ)
      (diskMapPartial U (c θ) (c θ)) =
        -diskMapConformalCoefficient g U (c θ) -
          fderiv ℝ (diskMapConformalCoefficient g U) (c θ) (c θ) / 2 := by
  let c := circleMap 0 1
  have hc : ContDiff ℝ ∞ c := contDiff_circleMap 0 1
  have hnorm : ‖c θ‖ = 1 := by simp [c]
  have hz : c θ ∈ Metric.closedBall (0 : ℂ) 1 := by simp [Metric.mem_closedBall, dist_zero_right, hnorm]
  have hd (r : ℝ) : deriv c r = Complex.I * c r := by simp [c, mul_comm]
  have hdd : deriv (deriv c) θ = -c θ := by
    rw [funext hd, deriv_const_mul _ (hc.differentiable (by simp) θ), hd,
      ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  change g.inner (U (c θ)) _ _ = _
  rw [covDerivAlong_diskMapVelocity g hs hU hc (hDs hz), hd, hdd]
  have hneg : diskMapPartial (E := E) U (c θ) (-c θ) = -diskMapPartial U (c θ) (c θ) := by
    unfold diskMapPartial
    exact map_neg _ _
  rw [hneg]
  simp only [map_add, _root_.add_apply, map_neg, _root_.neg_apply]
  rw [diskMapCovariantPartial_inner_conformal_closedDisk g hs hU hDs hconf hz,
    (hconf _ hz).inner_partials]
  have horth : _root_.Inner.inner ℝ (Complex.I * c θ) (c θ) = 0 := by
    simp [Complex.inner, Complex.mul_re, Complex.mul_im, mul_comm]
  have hrad : _root_.Inner.inner ℝ (c θ) (c θ) = 1 := by rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  have htan : _root_.Inner.inner ℝ (Complex.I * c θ) (Complex.I * c θ) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_mul, Complex.norm_I, hnorm]
    norm_num
  rw [horth, hrad, htan]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapBoundaryAcceleration_inner_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapBoundaryAcceleration_inner_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapBoundaryAcceleration_inner_radial ``Submission.DifferentialGeometry.Geometry.diskMapBoundaryAcceleration_inner_radial

end DifferentialGeometry.Geometry
