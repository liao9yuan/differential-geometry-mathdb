import Submission.DifferentialGeometry.Geometry.Curvature.DiskTraceDensity
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Vanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem tendsto_intervalIntegral_diskMapTraceBoundaryDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (htrace : U ∘ circleMap 0 1 = γ ∘ φ)
    {a f : ℂ → ℝ} (ha : Measurable a) (hf : Measurable f) (han : ∀ z, 0 ≤ a z)
    (haeq : ∀ z ∈ Metric.closedBall 0 1, a z = diskMapConformalCoefficient g U z) (l r : ℝ) :
    _root_.Filter.Tendsto (fun ε : ℝ => ∫ θ in l..r,
      regularizedConformalWeight a f ε (circleMap 0 1 θ) * diskMapTraceBoundaryDensity g U γ φ θ)
      (𝓝 0) (𝓝 (∫ θ in l..r, diskMapTraceBoundaryDensity g U γ φ θ)) := by
  have hzero (θ : ℝ) (hz : a (circleMap 0 1 θ) = 0) :
      diskMapTraceBoundaryDensity g U γ φ θ = 0 := by
    apply diskMapTraceBoundaryDensity_eq_zero
    rw [← haeq _ (by simp [Metric.mem_closedBall, dist_zero_right])]
    exact hz
  have hB := intervalIntegrable_diskMapTraceBoundaryDensity g hs hU hDs hconf hγ hi hφ htrace l r
  have hlim (ν : _root_.MeasureTheory.Measure ℝ) (hb : _root_.MeasureTheory.Integrable (diskMapTraceBoundaryDensity g U γ φ) ν) :=
    tendsto_integral_regularizedConformalWeight_comp_of_zero (measurable_circleMap 0 1) ha hf
      (Eventually.of_forall (fun θ => han _)) hb (Eventually.of_forall hzero)
  exact (hlim _ hB.1).sub (hlim _ hB.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tendsto_intervalIntegral_diskMapTraceBoundaryDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tendsto_intervalIntegral_diskMapTraceBoundaryDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tendsto_intervalIntegral_diskMapTraceBoundaryDensity ``Submission.DifferentialGeometry.Geometry.tendsto_intervalIntegral_diskMapTraceBoundaryDensity

end DifferentialGeometry.Geometry
