import Submission.DifferentialGeometry.Geometry.Metric.Euclidean
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Product
import Submission.DifferentialGeometry.Geometry.Metric.Scaling
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem LinearIsometryEquiv.pullbackMetric_euclidean (e : E ≃ₗᵢ[Real] E) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := E))
        e.toContinuousLinearEquiv.toDiffeomorph =
      euclideanMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner,
    DifferentialGeometry.euclideanMetric_inner,
    DifferentialGeometry.euclideanMetric_inner]
  change _root_.Inner.inner Real
      (mfderiv 𝓘(Real, E) 𝓘(Real, E) (e : E → E) x v)
      (mfderiv 𝓘(Real, E) 𝓘(Real, E) (e : E → E) x w) =
    _root_.Inner.inner Real v w
  rw [mfderiv_eq_fderiv]
  change _root_.Inner.inner Real
      ((fderiv Real e.toContinuousLinearEquiv.toContinuousLinearMap x) v)
      ((fderiv Real e.toContinuousLinearEquiv.toContinuousLinearMap x) w) =
    _root_.Inner.inner Real v w
  rw [ContinuousLinearMap.fderiv]
  exact e.inner_map_map v w

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.LinearIsometryEquiv
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LinearIsometryEquiv.pullbackMetric_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LinearIsometryEquiv.pullbackMetric_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LinearIsometryEquiv.pullbackMetric_euclidean ``Submission.DifferentialGeometry.LinearIsometryEquiv.pullbackMetric_euclidean

private theorem real_affine_of_deriv_sq_eq_one
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hsq : ∀ r, (deriv ψ r) ^ 2 = 1) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ r, ψ r = ε * r + ψ 0 := by
  have hcont : Continuous (deriv ψ) := hψ.continuous_deriv_one
  have hsign : ∀ a b, deriv ψ a = deriv ψ b := by
    intro a b
    rcases (sq_eq_one_iff.mp (hsq a)) with ha | ha <;>
      rcases (sq_eq_one_iff.mp (hsq b)) with hb | hb
    · exact ha.trans hb.symm
    · exfalso
      have hz := intermediate_value_univ b a hcont
        (show (0 : ℝ) ∈ Set.Icc (deriv ψ b) (deriv ψ a) by simp [ha, hb])
      rcases hz with ⟨x, hx⟩
      have h := hsq x
      simp [hx] at h
    · exfalso
      have hz := intermediate_value_univ a b hcont
        (show (0 : ℝ) ∈ Set.Icc (deriv ψ a) (deriv ψ b) by simp [ha, hb])
      rcases hz with ⟨x, hx⟩
      have h := hsq x
      simp [hx] at h
    · exact ha.trans hb.symm
  let ε := deriv ψ 0
  have hε : ε = 1 ∨ ε = -1 := sq_eq_one_iff.mp (hsq 0)
  have hderiv : ∀ r, deriv ψ r = deriv (fun r : ℝ => ε * r + ψ 0) r := by
    intro r
    rw [hsign r 0]
    simp [ε]
  refine ⟨ε, hε, ?_⟩
  have heq : ψ = (fun r : ℝ => ε * r + ψ 0) := by
    apply eq_of_fderiv_eq (hψ.differentiable (by decide)) (by fun_prop)
      (fun r => ?_) 0 (by simp)
    rw [← toSpanSingleton_deriv, ← toSpanSingleton_deriv, hderiv r]
  exact congrFun heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.real_affine_of_deriv_sq_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.real_affine_of_deriv_sq_eq_one target :: scope.openDecls } }

theorem Diffeomorph.real_affine_of_pullbackMetric_eq_euclidean
    (ψ : ℝ ≃ₘ[ℝ] ℝ)
    (hmetric : Diffeomorph.pullbackMetric (euclideanMetric (E := ℝ)) ψ = euclideanMetric) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ r, ψ r = ε * r + ψ 0 := by
  apply real_affine_of_deriv_sq_eq_one (ψ.contDiff.of_le (by simp))
  intro r
  have h := congrArg (fun g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) ℝ => g.inner r 1 1) hmetric
  rw [Diffeomorph.pullbackMetric_inner, euclideanMetric_inner, euclideanMetric_inner] at h
  rw [mfderiv_eq_fderiv] at h
  change (fderiv ℝ ψ r 1) * (fderiv ℝ ψ r 1) = 1 * 1 at h
  simpa only [fderiv_apply_one_eq_deriv, one_mul, pow_two] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.real_affine_of_pullbackMetric_eq_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.real_affine_of_pullbackMetric_eq_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.real_affine_of_pullbackMetric_eq_euclidean ``Submission.DifferentialGeometry.Diffeomorph.real_affine_of_pullbackMetric_eq_euclidean

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem Diffeomorph.pullbackMetric_euclidean_smul (c : ℝ) (hc : c ≠ 0) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := E))
      (LinearEquiv.smulOfNeZero ℝ E c hc).toContinuousLinearEquiv.toDiffeomorph =
        scaleMetric (c ^ 2) (sq_pos_of_ne_zero hc) (euclideanMetric (E := E)) := by
  let T := (LinearEquiv.smulOfNeZero ℝ E c hc).toContinuousLinearEquiv
  have hderiv (x : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) T.toDiffeomorph x =
      T.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (T.toContinuousLinearMap : E → E) x = _
    exact T.toContinuousLinearMap.fderiv
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner, hderiv, scaleMetric_inner,
    euclideanMetric_inner, euclideanMetric_inner]
  change _root_.Inner.inner ℝ (c • (v : E)) (c • (w : E)) = c ^ 2 * _root_.Inner.inner ℝ (v : E) (w : E)
  rw [real_inner_smul_left (F := E), real_inner_smul_right (F := E)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_smul ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetric_euclidean_smul

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem Diffeomorph.pullbackMetric_prod_euclidean_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : c ≠ 0) :
    Diffeomorph.pullbackMetric (g.prod (euclideanMetric (E := E)))
      ((Diffeomorph.refl I M ∞).prodCongr
        (LinearEquiv.smulOfNeZero ℝ E c hc).toContinuousLinearEquiv.toDiffeomorph) =
      g.prod (scaleMetric (c ^ 2) (sq_pos_of_ne_zero hc) (euclideanMetric (E := E))) := by
  rw [Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl,
    Diffeomorph.pullbackMetric_euclidean_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetric_prod_euclidean_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetric_prod_euclidean_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetric_prod_euclidean_smul ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetric_prod_euclidean_smul

end DifferentialGeometry
