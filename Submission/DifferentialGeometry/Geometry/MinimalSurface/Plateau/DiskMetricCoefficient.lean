import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalEnergy
import Submission.DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import Submission.DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def diskMapConformalCoefficient (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : ℝ :=
  g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapConformalCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapConformalCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapConformalCoefficient ``Submission.DifferentialGeometry.Geometry.diskMapConformalCoefficient



theorem DiskMapConformalAt.inner_partials
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) (v w : ℂ) :
    g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w) =
      diskMapConformalCoefficient g U z * _root_.Inner.inner ℝ v w := by
  have hpartial (x : ℂ) : diskMapPartial (E := E) U z x =
      x.re • diskMapPartial U z 1 + x.im • diskMapPartial U z Complex.I := by
    have hx : x = x.re • (1 : ℂ) + x.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    unfold diskMapPartial
    erw [← map_smul, ← map_smul, ← map_add]
    exact congrArg (fun q : ℂ => (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z q : E)) hx
  rw [hpartial v, hpartial w]
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    g.symm (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z 1), h.1, ← h.2,
    _root_.MulZeroClass.mul_zero, add_zero, zero_add]
  have hi : _root_.Inner.inner ℝ v w = v.re * w.re + v.im * w.im := by
    simp [Complex.inner, Complex.mul_re, mul_comm]
  rw [hi]
  unfold diskMapConformalCoefficient
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.inner_partials then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.inner_partials"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.inner_partials ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.inner_partials

theorem diskMapConformalCoefficient_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : 0 ≤ diskMapConformalCoefficient g U z := by
  by_cases h : diskMapPartial (E := E) U z 1 = 0
  · simp [diskMapConformalCoefficient, h]
  · exact (g.pos (U z) (diskMapPartial U z 1) h).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapConformalCoefficient_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapConformalCoefficient_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapConformalCoefficient_nonneg ``Submission.DifferentialGeometry.Geometry.diskMapConformalCoefficient_nonneg



theorem DiskMapConformalAt.coefficient_eq_energy
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) :
    diskMapConformalCoefficient g U z = diskMapEnergyDensity g U z := by
  unfold diskMapConformalCoefficient diskMapEnergyDensity
  rw [← h.2]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_energy ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_energy



theorem DiskMapConformalAt.coefficient_eq_zero_iff
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {U : ℂ → M} {z : ℂ}
    (h : DiskMapConformalAt g U z) :
    diskMapConformalCoefficient g U z = 0 ↔ mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 := by
  constructor
  · intro ha
    have h1 : diskMapPartial (E := E) U z 1 = 0 := by
      by_contra hv
      have hp := g.pos (U z) (diskMapPartial U z 1) hv
      change 0 < diskMapConformalCoefficient g U z at hp
      linarith
    have hI : diskMapPartial (E := E) U z Complex.I = 0 := by
      by_contra hv
      have hp := g.pos (U z) (diskMapPartial U z Complex.I) hv
      rw [← h.2] at hp
      change 0 < diskMapConformalCoefficient g U z at hp
      linarith
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    change diskMapPartial U z v = 0
    rw [hv]
    change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (v.re • (1 : ℂ) + v.im • Complex.I) = 0
    erw [map_add, map_smul, map_smul]
    change v.re • diskMapPartial U z 1 + v.im • diskMapPartial U z Complex.I = 0
    rw [h1, hI, smul_zero, smul_zero, add_zero]
  · intro hd
    unfold diskMapConformalCoefficient diskMapPartial
    rw [hd]
    change g.inner (U z) (0 : TangentSpace 𝓘(ℝ, E) (U z)) 0 = 0
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_zero_iff ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt.coefficient_eq_zero_iff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_diskMapMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) (v w : ℂ) :
    ContDiffOn ℝ ∞ (fun z => g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w)) s := by
  exact contDiffOn_sourceSectionPairing g hU
    (contMDiffOn_source_partial hs hU (by simp) v)
    (contMDiffOn_source_partial hs hU (by simp) w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_diskMapMetricPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_diskMapMetricPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_diskMapMetricPairing ``Submission.DifferentialGeometry.Geometry.contDiffOn_diskMapMetricPairing



theorem contDiffOn_diskMapConformalCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) :
    ContDiffOn ℝ ∞ (diskMapConformalCoefficient g U) s :=
  contDiffOn_diskMapMetricPairing g hs hU 1 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contDiffOn_diskMapConformalCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contDiffOn_diskMapConformalCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contDiffOn_diskMapConformalCoefficient ``Submission.DifferentialGeometry.Geometry.contDiffOn_diskMapConformalCoefficient

end DifferentialGeometry.Geometry
