import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.InnerProductSpace
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def diskMapInwardConormal (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  -(Real.sqrt (diskMapConformalCoefficient g U z))⁻¹ • diskMapPartial U z z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapInwardConormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapInwardConormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapInwardConormal ``Submission.DifferentialGeometry.Geometry.diskMapInwardConormal


theorem DiskMapConformalAt.boundary_arclengthDensity
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) (hz : ‖z‖ = 1) :
    Real.sqrt (g.inner (U z) (diskMapPartial U z (Complex.I * z))
      (diskMapPartial U z (Complex.I * z))) =
      Real.sqrt (diskMapConformalCoefficient g U z) := by
  rw [hc.inner_partials, real_inner_self_eq_norm_sq, norm_mul, Complex.norm_I, hz]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.boundary_arclengthDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.boundary_arclengthDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.boundary_arclengthDensity ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.boundary_arclengthDensity


theorem diskMapInwardConormal_eq_zero
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hz : diskMapConformalCoefficient g U z = 0) : diskMapInwardConormal g U z = 0 := by
  simp [diskMapInwardConormal, hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapInwardConormal_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapInwardConormal_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapInwardConormal_eq_zero ``Submission.DifferentialGeometry.Geometry.diskMapInwardConormal_eq_zero


theorem DiskMapConformalAt.inwardConormal_unit
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) (hz : ‖z‖ = 1)
    (ha : 0 < diskMapConformalCoefficient g U z) :
    g.inner (U z) (diskMapInwardConormal g U z) (diskMapInwardConormal g U z) = 1 := by
  unfold diskMapInwardConormal
  simp only [map_smul, smul_apply, smul_eq_mul, hc.inner_partials,
    real_inner_self_eq_norm_sq, hz, one_pow, mul_one]
  have hs := Real.sq_sqrt ha.le
  have hn := ne_of_gt (Real.sqrt_pos.mpr ha)
  field_simp [hn, hs]
  exact hs.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_unit ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_unit



theorem DiskMapConformalAt.inwardConormal_orthogonal
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) :
    g.inner (U z) (diskMapPartial U z (Complex.I * z)) (diskMapInwardConormal g U z) = 0 := by
  unfold diskMapInwardConormal
  simp only [map_smul, smul_eq_mul, hc.inner_partials]
  have horth : _root_.Inner.inner ℝ (Complex.I * z) z = 0 := by
    simp [Complex.inner, Complex.mul_re, Complex.mul_im, mul_comm]
  rw [horth]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_orthogonal ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_orthogonal




theorem DiskMapConformalAt.inwardConormal_flux
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (hc : DiskMapConformalAt g U z) (V : TangentSpace 𝓘(ℝ, E) (U z)) :
    g.inner (U z) V (diskMapInwardConormal g U z) *
      Real.sqrt (diskMapConformalCoefficient g U z) =
      -g.inner (U z) V (diskMapPartial U z z) := by
  by_cases ha : diskMapConformalCoefficient g U z = 0
  · have hd := hc.coefficient_eq_zero_iff.mp ha
    simp only [diskMapInwardConormal_eq_zero ha, map_zero, _root_.MulZeroClass.zero_mul, diskMapPartial, hd]
    change 0 = -g.inner (U z) V 0
    simp
  · have hp := lt_of_le_of_ne (diskMapConformalCoefficient_nonneg g U z) (Ne.symm ha)
    have hn := ne_of_gt (Real.sqrt_pos.mpr hp)
    unfold diskMapInwardConormal
    simp only [map_smul, smul_eq_mul]
    field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_flux ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.inwardConormal_flux

end DifferentialGeometry.Geometry
