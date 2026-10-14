import Submission.DifferentialGeometry.Geometry.Curvature.DiskGauss
import Submission.DifferentialGeometry.Geometry.Curvature.RegularizedConformalDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem regularizedConformalMetric_eq_pullback_add
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hconf : DiskMapConformalAt g U z)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (heq : a z = diskMapConformalCoefficient g U z) (v w : ℂ) :
    (regularizedConformalMetric a f ha hf han ε hε).inner z v w =
      g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w) +
        ε ^ 2 * (conformalEuclideanMetric f hf).inner z v w := by
  rw [regularizedConformalMetric_inner, hconf.inner_partials, conformalEuclideanMetric_inner]
  unfold regularizedConformalCoefficient
  rw [heq]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedConformalMetric_eq_pullback_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedConformalMetric_eq_pullback_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedConformalMetric_eq_pullback_add ``Submission.DifferentialGeometry.Geometry.regularizedConformalMetric_eq_pullback_add





theorem regularizedDisk_curvatureDensity_le_sectional
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) {z : ℂ} (hz : z ∈ s)
    (heq : a =ᶠ[𝓝 z] diskMapConformalCoefficient g U) :
    planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I ≤
      regularizedConformalWeight a f ε z *
        (sectionalCurvature g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) *
          diskMapConformalCoefficient g U z) +
      (1 - regularizedConformalWeight a f ε z) * (-Laplacian.laplacian f z) := by
  apply (regularizedConformalMetric_curvatureDensity_le ha hf han hε z).trans
  refine add_le_add ?_ le_rfl
  by_cases hzero : a z = 0
  · have hw : regularizedConformalWeight a f ε z = 0 := by
      simp [regularizedConformalWeight, hzero]
    rw [if_pos hzero, hw, _root_.MulZeroClass.zero_mul]
  · rw [if_neg hzero]
    apply mul_le_mul_of_nonneg_left _ (regularizedConformalWeight_mem_Icc (han z) hε).1
    have hpos : 0 < diskMapConformalCoefficient g U z := by
      rw [← heq.eq_of_nhds]
      exact lt_of_le_of_ne (han z) (Ne.symm hzero)
    have hlog : (fun q => Real.log (a q)) =ᶠ[𝓝 z]
        (fun q => Real.log (diskMapConformalCoefficient g U q)) := heq.fun_comp Real.log
    rw [(_root_.InnerProductSpace.laplacian_congr_nhds hlog).eq_of_nhds]
    exact diskMap_curvature_density_le_sectional g hs hU hconf hharm hz hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedDisk_curvatureDensity_le_sectional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedDisk_curvatureDensity_le_sectional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedDisk_curvatureDensity_le_sectional ``Submission.DifferentialGeometry.Geometry.regularizedDisk_curvatureDensity_le_sectional

end DifferentialGeometry.Geometry
