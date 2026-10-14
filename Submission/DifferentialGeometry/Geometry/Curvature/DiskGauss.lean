import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskBochner
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalSecondPartial
import Submission.DifferentialGeometry.Geometry.Metric.OrthogonalPlaneNormal
import Submission.DifferentialGeometry.Geometry.Curvature.SectionalContraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def diskMapNormalPartial (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z v w : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  orthogonalPlaneNormal g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I)
    (diskMapCovariantPartial g U z v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapNormalPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapNormalPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapNormalPartial ``Submission.DifferentialGeometry.Geometry.diskMapNormalPartial





theorem diskMap_gauss_identity [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z =
      g.inner (U z) (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) (diskMapPartial U z 1) /
        diskMapConformalCoefficient g U z -
      (g.inner (U z) (diskMapNormalPartial g U z 1 1) (diskMapNormalPartial g U z 1 1) +
        g.inner (U z) (diskMapNormalPartial g U z Complex.I 1)
          (diskMapNormalPartial g U z Complex.I 1)) / diskMapConformalCoefficient g U z := by
  have hc := hconf z hz
  have hq : g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) ≠ 0 := by
    rw [← hc.2]
    exact ha.ne'
  have hreg : ContDiffAt ℝ 2 (diskMapConformalCoefficient g U) z :=
    ((contDiffOn_diskMapConformalCoefficient g hs hU z hz).contDiffAt
      (hs.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have ht := diskMapCovariantPartial_tangent_components g hs hU hconf hz
  rw [DifferentialGeometry.Analysis.laplacian_log hreg ha.ne',
    laplacian_diskMapConformalCoefficient_of_harmonic g hs hU hharm hz]
  unfold diskMapNormalPartial
  rw [orthogonalPlaneNormal_inner_self g (U z) _ _ _ hc.1 ha.ne' hq,
    orthogonalPlaneNormal_inner_self g (U z) _ _ _ hc.1 ha.ne' hq]
  rw [← hc.2, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
  change -(1 / 2 : ℝ) * (_ / diskMapConformalCoefficient g U z -
    _ / (diskMapConformalCoefficient g U z) ^ 2) = _
  change -(1 / 2 : ℝ) * (_ / diskMapConformalCoefficient g U z -
    _ / (diskMapConformalCoefficient g U z) ^ 2) =
    _ / diskMapConformalCoefficient g U z -
      ((_ - _ / diskMapConformalCoefficient g U z - _ / diskMapConformalCoefficient g U z) +
       (_ - _ / diskMapConformalCoefficient g U z - _ / diskMapConformalCoefficient g U z)) /
        diskMapConformalCoefficient g U z
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMap_gauss_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMap_gauss_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMap_gauss_identity ``Submission.DifferentialGeometry.Geometry.diskMap_gauss_identity



theorem diskMap_curvature_density_le [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z ≤
      g.inner (U z) (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) (diskMapPartial U z 1) /
        diskMapConformalCoefficient g U z := by
  rw [diskMap_gauss_identity g hs hU hconf hharm hz ha]
  have hnonneg (v w : ℂ) : 0 ≤
      g.inner (U z) (diskMapNormalPartial g U z v w) (diskMapNormalPartial g U z v w) :=
    (g.toRiemannianMetric.toCore (U z)).re_inner_nonneg (diskMapNormalPartial g U z v w)
  exact sub_le_self _ (div_nonneg (add_nonneg (hnonneg 1 1) (hnonneg Complex.I 1)) ha.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMap_curvature_density_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMap_curvature_density_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMap_curvature_density_le ``Submission.DifferentialGeometry.Geometry.diskMap_curvature_density_le



theorem DiskMapConformalAt.sectional_mul_coefficient [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) :
    sectionalCurvature g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) *
        diskMapConformalCoefficient g U z =
      g.inner (U z) (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) (diskMapPartial U z 1) /
        diskMapConformalCoefficient g U z := by
  by_cases ha : diskMapConformalCoefficient g U z = 0
  · simp only [ha, _root_.MulZeroClass.mul_zero, div_zero]
  · rw [sectionalCurvature_eq_riemann, hc.1, ← hc.2,
      g.symm (U z) (diskMapPartial U z 1)]
    change _ / (diskMapConformalCoefficient g U z * diskMapConformalCoefficient g U z - 0 ^ 2) *
      diskMapConformalCoefficient g U z = _ / diskMapConformalCoefficient g U z
    field_simp
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.sectional_mul_coefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.sectional_mul_coefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.sectional_mul_coefficient ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.sectional_mul_coefficient



theorem diskMap_curvature_density_le_sectional [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z ≤
      sectionalCurvature g (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) *
        diskMapConformalCoefficient g U z := by
  rw [(hconf z hz).sectional_mul_coefficient]
  exact diskMap_curvature_density_le g hs hU hconf hharm hz ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMap_curvature_density_le_sectional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMap_curvature_density_le_sectional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMap_curvature_density_le_sectional ``Submission.DifferentialGeometry.Geometry.diskMap_curvature_density_le_sectional

end DifferentialGeometry.Geometry
