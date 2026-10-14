import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskConormal
import Submission.DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import Mathlib.MeasureTheory.Integral.CircleIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem contMDiff_diskMapBoundary {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (U ∘ circleMap 0 1) := by
  intro θ
  have hz : circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right]
  exact ((hU _ (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).comp θ
    (contDiff_circleMap 0 1).contMDiff.contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiff_diskMapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiff_diskMapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiff_diskMapBoundary ``Submission.DifferentialGeometry.Geometry.contMDiff_diskMapBoundary

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem mfderiv_diskMapBoundary {U : ℂ → M} {θ : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ)) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1) θ (1 : ℝ) =
      diskMapPartial U (circleMap 0 1 θ) (Complex.I * circleMap 0 1 θ) := by
  have h := congrArg (fun p : TangentBundle 𝓘(ℝ, E) M => (p.2 : E))
    (tangent_velocity_comp hU (differentiable_circleMap 0 1 θ))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ circleMap 0 1) θ (1 : ℝ) =
    diskMapPartial U (circleMap 0 1 θ) (deriv (circleMap 0 1) θ) at h
  simpa only [deriv_circleMap, mul_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.mfderiv_diskMapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.mfderiv_diskMapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.mfderiv_diskMapBoundary ``Submission.DifferentialGeometry.Geometry.mfderiv_diskMapBoundary



theorem riemannianCurveSpeed_diskMapBoundary
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {θ : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ))
    (hconf : DiskMapConformalAt g U (circleMap 0 1 θ)) :
    riemannianCurveSpeed g (U ∘ circleMap 0 1) θ =
      Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ)) := by
  unfold riemannianCurveSpeed
  erw [mfderiv_diskMapBoundary hU]
  exact hconf.boundary_arclengthDensity (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveSpeed_diskMapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveSpeed_diskMapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveSpeed_diskMapBoundary ``Submission.DifferentialGeometry.Geometry.riemannianCurveSpeed_diskMapBoundary

end DifferentialGeometry.Geometry
