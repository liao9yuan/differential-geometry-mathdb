import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import Mathlib.LinearAlgebra.Matrix.BilinearForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem paramGramMatrix_comp (g : SmoothRiemannianMetric I M)
    {Φ : E → M} {ψ : E → E} {x : E}
    (hΦ : MDifferentiableAt 𝓘(ℝ, E) I Φ (ψ x)) (hψ : DifferentiableAt ℝ ψ x) :
    paramGramMatrix g (Φ ∘ ψ) x =
      (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E) (fderiv ℝ ψ x).toLinearMap)ᵀ *
        paramGramMatrix g Φ (ψ x) *
          LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E) (fderiv ℝ ψ x).toLinearMap := by
  let D := mfderiv 𝓘(ℝ, E) I Φ (ψ x)
  let A := (fderiv ℝ ψ x).toLinearMap
  let B : LinearMap.BilinForm ℝ E := LinearMap.BilinForm.comp
    (g.inner (Φ (ψ x))).toLinearMap₁₂ D.toLinearMap D.toLinearMap
  have hchain : mfderiv 𝓘(ℝ, E) I (Φ ∘ ψ) x = D.comp (fderiv ℝ ψ x) := by
    rw [mfderiv_comp x hΦ hψ.mdifferentiableAt, mfderiv_eq_fderiv]
    rfl
  have hleft : paramGramMatrix g (Φ ∘ ψ) x = (B.comp A A).toMatrix (chartModelBasis E) := by
    ext i j
    simp only [paramGramMatrix_apply, hchain, LinearMap.BilinForm.toMatrix_apply]
    rfl
  have hbase : B.toMatrix (chartModelBasis E) = paramGramMatrix g Φ (ψ x) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, paramGramMatrix_apply]
    rfl
  rw [hleft, LinearMap.BilinForm.toMatrix_comp (chartModelBasis E) (chartModelBasis E), hbase]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramGramMatrix_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramGramMatrix_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramGramMatrix_comp ``Submission.DifferentialGeometry.Integral.Measure.paramGramMatrix_comp

theorem paramDensity_comp (g : SmoothRiemannianMetric I M)
    {Φ : E → M} {ψ : E → E} {x : E}
    (hΦ : MDifferentiableAt 𝓘(ℝ, E) I Φ (ψ x)) (hψ : DifferentiableAt ℝ ψ x) :
    paramDensity g (Φ ∘ ψ) x = |(fderiv ℝ ψ x).det| * paramDensity g Φ (ψ x) := by
  have hdet : (paramGramMatrix g (Φ ∘ ψ) x).det =
      (fderiv ℝ ψ x).det ^ 2 * (paramGramMatrix g Φ (ψ x)).det := by
    rw [paramGramMatrix_comp g hΦ hψ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      LinearMap.det_toMatrix]
    ring
  simp only [paramDensity_apply, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramDensity_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramDensity_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramDensity_comp ``Submission.DifferentialGeometry.Integral.Measure.paramDensity_comp

theorem paramDensity_ratio_comp_continuousLinearEquiv (g : SmoothRiemannianMetric I M)
    {Φ : E → M} (L : E ≃L[ℝ] E) {x : E}
    (hΦ : MDifferentiableAt 𝓘(ℝ, E) I Φ (L x))
    (hΦ₀ : MDifferentiableAt 𝓘(ℝ, E) I Φ 0) :
    paramDensity g (Φ ∘ L) x / paramDensity g (Φ ∘ L) 0 =
      paramDensity g Φ (L x) / paramDensity g Φ 0 := by
  have hzero : MDifferentiableAt 𝓘(ℝ, E) I Φ (L 0) := by simpa only [map_zero] using hΦ₀
  rw [paramDensity_comp g hΦ L.differentiableAt, paramDensity_comp g hzero L.differentiableAt]
  simp only [L.fderiv, map_zero]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr L.toLinearEquiv.isUnit_det'.ne_zero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramDensity_ratio_comp_continuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramDensity_ratio_comp_continuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramDensity_ratio_comp_continuousLinearEquiv ``Submission.DifferentialGeometry.Integral.Measure.paramDensity_ratio_comp_continuousLinearEquiv

end DifferentialGeometry.Integral.Measure
