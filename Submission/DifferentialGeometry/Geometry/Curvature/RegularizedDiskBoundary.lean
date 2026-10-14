import Submission.DifferentialGeometry.Geometry.Curvature.DiskTraceDensity
import Submission.DifferentialGeometry.Geometry.Curvature.RegularizedConformalDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem regularizedDisk_boundaryDensity_eq_trace
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hm : Monotone φ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f)
    (han : ∀ z, 0 ≤ a z) (θ : ℝ)
    (haeq : a =ᶠ[𝓝 (circleMap 0 1 θ)] diskMapConformalCoefficient g U)
    (hfν : fderiv ℝ f (circleMap 0 1 θ) (circleMap 0 1 θ) = -1)
    {ε : ℝ} (hε : ε ≠ 0) :
    let z := circleMap 0 1 θ
    conformalCircleGeodesicCurvature (regularizedConformalLogFactor a f ε)
        (contDiff_regularizedConformalLogFactor ha hf han hε) z *
      Real.sqrt ((regularizedConformalMetric a f ha hf han ε hε).inner z
        (Complex.I * z) (Complex.I * z)) =
      regularizedConformalWeight a f ε z * diskMapTraceBoundaryDensity g U γ φ θ := by
  dsimp only
  rw [regularizedConformalMetric_boundaryDensity ha hf han hε (by simp) hfν]
  by_cases hz : a (circleMap 0 1 θ) = 0
  · simp [regularizedConformalWeight, hz]
  · have hap : 0 < diskMapConformalCoefficient g U (circleMap 0 1 θ) := by
      rw [← haeq.eq_of_nhds]
      exact lt_of_le_of_ne (han _) (Ne.symm hz)
    have hb : diskMapTraceBoundaryDensity g U γ φ θ =
        1 + fderiv ℝ (diskMapConformalCoefficient g U) (circleMap 0 1 θ) (circleMap 0 1 θ) /
          (2 * diskMapConformalCoefficient g U (circleMap 0 1 θ)) :=
      diskMapTraceCurvature_density g hs hU hDs hconf hγ hi hφ hm htrace θ hap
    rw [hb, fderiv.log (ha.differentiable (by simp) _) hz]
    simp only [_root_.smul_apply, smul_eq_mul]
    rw [haeq.fderiv_eq, haeq.eq_of_nhds]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedDisk_boundaryDensity_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedDisk_boundaryDensity_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedDisk_boundaryDensity_eq_trace ``Submission.DifferentialGeometry.Geometry.regularizedDisk_boundaryDensity_eq_trace

end DifferentialGeometry.Geometry
