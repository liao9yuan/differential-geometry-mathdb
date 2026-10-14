import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Submission.DifferentialGeometry.Geometry.Metric.InfinitesimalDistance
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space (TangentBundle 𝓘(ℝ, E) M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem norm_fderiv_le_sqrt_metric_of_edist_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {f : ℂ → ℝ} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (hf : DifferentiableAt ℝ f z)
    (hbound : ∀ w, _root_.EDist.edist (f z) (f w) ≤ riemannianEDistOf g (U z) (U w))
    (v : ℂ) :
    ‖fderiv ℝ f z v‖ ≤ Real.sqrt (g.inner (U z)
      (diskMapPartial U z v) (diskMapPartial U z v)) := by
  let : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
  have hmetric (x y : ℝ) : riemannianEDistOf (euclideanMetric (E := ℝ)) x y = _root_.EDist.edist x y := by
    exact (IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)) x y).symm
  have h := metric_differential_le_of_edist_le g (euclideanMetric (E := ℝ))
    (L := 1) hU hf.mdifferentiableAt (fun w => by
      rw [hmetric, ENNReal.coe_one, one_mul]
      exact hbound w) v
  rw [mfderiv_eq_fderiv] at h
  change Real.sqrt ((fderiv ℝ f z v) * (fderiv ℝ f z v)) ≤ _ at h
  simpa only [← sq, Real.sqrt_sq_eq_abs, Real.norm_eq_abs, NNReal.coe_one, one_mul,
    diskMapPartial] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.norm_fderiv_le_sqrt_metric_of_edist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.norm_fderiv_le_sqrt_metric_of_edist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.norm_fderiv_le_sqrt_metric_of_edist_le ``Submission.DifferentialGeometry.Geometry.norm_fderiv_le_sqrt_metric_of_edist_le

theorem fderiv_partials_sq_le_two_mul_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {f : ℂ → ℝ} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (hf : DifferentiableAt ℝ f z)
    (hbound : ∀ w, _root_.EDist.edist (f z) (f w) ≤ riemannianEDistOf g (U z) (U w)) :
    (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 ≤
      2 * diskMapEnergyDensity g U z := by
  have hsq (v : ℂ) : (fderiv ℝ f z v) ^ 2 ≤
      g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z v) := by
    have h := norm_fderiv_le_sqrt_metric_of_edist_le g hU hf hbound v
    have hh := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr h
    rw [Real.sq_sqrt (metric_inner_self_nonneg _ _ _)] at hh
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  unfold diskMapEnergyDensity
  linarith [hsq 1, hsq Complex.I]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.fderiv_partials_sq_le_two_mul_diskMapEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.fderiv_partials_sq_le_two_mul_diskMapEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.fderiv_partials_sq_le_two_mul_diskMapEnergyDensity ``Submission.DifferentialGeometry.Geometry.fderiv_partials_sq_le_two_mul_diskMapEnergyDensity

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

theorem ae_fderiv_partials_sq_le_two_mul_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {f : ℂ → ℝ} {C : ℝ≥0}
    (hU : ∀ z w, riemannianEDistOf g (U z) (U w) ≤ (C : ℝ≥0∞) * _root_.EDist.edist z w)
    (hcontract : ∀ z w, _root_.EDist.edist (f z) (f w) ≤ riemannianEDistOf g (U z) (U w)) :
    ∀ᵐ z ∂volume, (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 ≤
      2 * diskMapEnergyDensity g U z := by
  have hf : LipschitzWith C f := fun z w => (hcontract z w).trans (hU z w)
  have hmd : ∀ᵐ z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℂ), MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    ae_mdifferentiableAt_of_metric_lipschitz g hU
  filter_upwards [hmd, hf.ae_differentiableAt] with z hz hzf
  exact fderiv_partials_sq_le_two_mul_diskMapEnergyDensity g hz hzf (hcontract z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ae_fderiv_partials_sq_le_two_mul_diskMapEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ae_fderiv_partials_sq_le_two_mul_diskMapEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ae_fderiv_partials_sq_le_two_mul_diskMapEnergyDensity ``Submission.DifferentialGeometry.Geometry.ae_fderiv_partials_sq_le_two_mul_diskMapEnergyDensity

end DifferentialGeometry.Geometry

end

end
