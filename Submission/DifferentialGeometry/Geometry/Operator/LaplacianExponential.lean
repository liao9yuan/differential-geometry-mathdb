import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem laplacian_exp
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {φ : M → ℝ} {x : M}
    (hφ : ContMDiffAt I 𝓘(ℝ, ℝ) 2 φ x) :
    laplacian cov g (fun y => Real.exp (φ y)) x =
      Real.exp (φ x) * (laplacian cov g φ x +
        g.inner x (gradientFun g φ x) (gradientFun g φ x)) := by
  have hφn : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) φ y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hφ).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  have hgrad := (gradientFun_contMDiffAt_one g hφ).mdifferentiableAt one_ne_zero
  have h := laplacian_comp_at cov g Real.differentiable_exp
    (by rw [Real.deriv_exp]; exact Real.differentiable_exp.differentiableAt) hφn hgrad
  simpa only [Real.deriv_exp, mul_add] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_exp ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_exp

theorem laplacian_exp_mul
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) {φ f : M → ℝ} {x : M}
    (hφ : ContMDiffAt I 𝓘(ℝ, ℝ) 2 φ x)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x) :
    laplacian cov g (fun y => Real.exp (φ y) * f y) x =
      Real.exp (φ x) * (laplacian cov g f x +
        2 * g.inner x (gradientFun g φ x) (gradientFun g f x) +
        (laplacian cov g φ x +
          g.inner x (gradientFun g φ x) (gradientFun g φ x)) * f x) := by
  have he : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => Real.exp (φ y)) x :=
    Real.contDiff_exp.contMDiff.contMDiffAt.comp x hφ
  have hen : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => Real.exp (φ z)) y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp he).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  have hfn : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  rw [laplacian_mul_at cov g hen hfn
    ((gradientFun_contMDiffAt_one g he).mdifferentiableAt one_ne_zero)
    ((gradientFun_contMDiffAt_one g hf).mdifferentiableAt one_ne_zero),
    laplacian_exp cov g hφ,
    gradientFun_comp g Real.differentiable_exp.differentiableAt
      (hφ.mdifferentiableAt (by norm_num))]
  simp only [Real.deriv_exp, map_smul, smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_exp_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_exp_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_exp_mul ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_exp_mul

end DifferentialGeometry.Geometry.Operator
