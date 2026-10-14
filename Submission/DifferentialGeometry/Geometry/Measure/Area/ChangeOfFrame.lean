import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldDensity
import Submission.DifferentialGeometry.Tensor.LinearAlgebra.ComplexDeterminant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.InnerProductSpace _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem twoJacobian_changeOfFrame (v w : V) (a b c d : ℝ) :
    twoJacobian (a • v + b • w) (c • v + d • w) =
      |a * d - b * c| * twoJacobian v w := by
  unfold twoJacobian
  calc
    _ = Real.sqrt ((a * d - b * c) ^ 2 *
        (⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ ^ 2)) := by
      congr 1
      simp only [inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [real_inner_comm w v]
      ring
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_changeOfFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_changeOfFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_changeOfFrame ``Submission.DifferentialGeometry.Geometry.twoJacobian_changeOfFrame


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tangentTwoJacobian_changeOfFrame (g : SmoothRiemannianMetric I M) {x : M}
    (v w : TangentSpace I x) (a b c d : ℝ) :
    tangentTwoJacobian g (a • v + b • w) (c • v + d • w) =
      |a * d - b * c| * tangentTwoJacobian g v w := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact twoJacobian_changeOfFrame v w a b c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tangentTwoJacobian_changeOfFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tangentTwoJacobian_changeOfFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tangentTwoJacobian_changeOfFrame ``Submission.DifferentialGeometry.Geometry.tangentTwoJacobian_changeOfFrame

theorem tangentTwoJacobian_comp_complex (g : SmoothRiemannianMetric I M) {x : M}
    (B : ℂ →L[ℝ] TangentSpace I x) (A : ℂ →L[ℝ] ℂ) :
    tangentTwoJacobian g (B (A 1)) (B (A Complex.I)) =
      |A.toLinearMap.det| * tangentTwoJacobian g (B 1) (B Complex.I) := by
  have hv (z : ℂ) : B z = z.re • B 1 + z.im • B Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [Complex.real_smul, Complex.re_add_im]
  rw [hv (A 1), hv (A Complex.I), tangentTwoJacobian_changeOfFrame,
    complex_linearMap_det]
  simp only [ContinuousLinearMap.coe_coe, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.tangentTwoJacobian_comp_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.tangentTwoJacobian_comp_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.tangentTwoJacobian_comp_complex ``Submission.DifferentialGeometry.Geometry.tangentTwoJacobian_comp_complex

set_option backward.isDefEq.respectTransparency false in


theorem riemannianAreaDensity_precomp (g : SmoothRiemannianMetric I M)
    {u : ℂ → M} {φ : ℂ → ℂ} {z : ℂ}
    (hu : MDifferentiableAt 𝓘(ℝ, ℂ) I u (φ z)) (hφ : DifferentiableAt ℝ φ z) :
    riemannianAreaDensity g (u ∘ φ) z =
      |(fderiv ℝ φ z).toLinearMap.det| * riemannianAreaDensity g u (φ z) := by
  unfold riemannianAreaDensity
  rw [mfderiv_comp z hu hφ.mdifferentiableAt, mfderiv_eq_fderiv]
  exact tangentTwoJacobian_comp_complex g _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianAreaDensity_precomp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianAreaDensity_precomp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianAreaDensity_precomp ``Submission.DifferentialGeometry.Geometry.riemannianAreaDensity_precomp

end DifferentialGeometry.Geometry
