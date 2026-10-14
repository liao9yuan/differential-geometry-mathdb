import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBoundaryAcceleration
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBoundaryMetric
import Submission.DifferentialGeometry.Geometry.Curvature.Curve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.InnerProductSpace
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem diskMapBoundaryCurvature_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    (θ : ℝ) (ha : 0 < diskMapConformalCoefficient g U (circleMap 0 1 θ)) :
    let c := circleMap 0 1
    g.inner (U (c θ)) (riemannianCurveCurvature g (U ∘ c) θ)
      (diskMapInwardConormal g U (c θ)) * Real.sqrt (diskMapConformalCoefficient g U (c θ)) =
        1 + fderiv ℝ (diskMapConformalCoefficient g U) (c θ) (c θ) /
          (2 * diskMapConformalCoefficient g U (c θ)) := by
  let c := circleMap 0 1
  have hz (r : ℝ) : c r ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [c, Metric.mem_closedBall, dist_zero_right]
  have hγ := contMDiff_diskMapBoundary hs hU hDs
  have hd := ((hU _ (hDs (hz θ))).contMDiffAt (hs.mem_nhds (hDs (hz θ)))).mdifferentiableAt (by simp)
  have hvel : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ c) θ (1 : ℝ) =
      diskMapPartial U (c θ) (Complex.I * c θ) := mfderiv_diskMapBoundary hd
  have hspeed : riemannianCurveSpeed g (U ∘ c) θ =
      Real.sqrt (diskMapConformalCoefficient g U (c θ)) :=
    riemannianCurveSpeed_diskMapBoundary g hd (hconf _ (hz θ))
  have hne : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ c) θ (1 : ℝ) ≠ 0 := by
    intro hzero
    have hpos := Real.sqrt_pos.mpr ha
    have hzeroSpeed : riemannianCurveSpeed g (U ∘ c) θ = 0 := by
      simp [riemannianCurveSpeed, hzero]
    rw [hspeed] at hzeroSpeed
    linarith
  have horth : g.inner (U (c θ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (U ∘ c) θ (1 : ℝ))
      (diskMapPartial U (c θ) (c θ)) = 0 := by
    erw [hvel, (hconf _ (hz θ)).inner_partials]
    simp [Complex.inner, Complex.mul_re, Complex.mul_im, mul_comm]
  have hcurv := riemannianCurveCurvature_inner_normal g hγ hne
    (diskMapPartial U (c θ) (c θ)) horth
  erw [diskMapBoundaryAcceleration_inner_radial g hs hU hDs hconf θ,
    hspeed, Real.sq_sqrt ha.le] at hcurv
  change g.inner (U (c θ)) _ _ * _ = _
  rw [(hconf _ (hz θ)).inwardConormal_flux]
  erw [hcurv]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapBoundaryCurvature_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapBoundaryCurvature_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapBoundaryCurvature_density ``Submission.DifferentialGeometry.Geometry.diskMapBoundaryCurvature_density

end DifferentialGeometry.Geometry
