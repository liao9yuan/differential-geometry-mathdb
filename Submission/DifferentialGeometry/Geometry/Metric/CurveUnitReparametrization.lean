import Submission.DifferentialGeometry.Geometry.Metric.CurveUnitTangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem velocity_reparam {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ t))
    (hφ : DifferentiableAt ℝ φ t) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ φ) t 1 =
      deriv φ t • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ t) 1 := by
  have h := congrArg (fun p : TangentBundle 𝓘(ℝ, E) M => (p.2 : E))
    (tangent_velocity_comp hγ hφ)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ φ) t 1 =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ t) (deriv φ t) at h
  apply h.trans
  erw [← map_smul]
  congr 1
  change deriv φ t = deriv φ t * (1 : ℝ)
  exact (mul_one _).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.velocity_reparam
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.velocity_reparam target :: scope.openDecls } }


theorem riemannianCurveSpeed_reparam (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ t))
    (hφ : DifferentiableAt ℝ φ t) :
    riemannianCurveSpeed g (γ ∘ φ) t = |deriv φ t| * riemannianCurveSpeed g γ (φ t) := by
  unfold riemannianCurveSpeed
  erw [velocity_reparam hγ hφ]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveSpeed_reparam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveSpeed_reparam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveSpeed_reparam ``Submission.DifferentialGeometry.Geometry.riemannianCurveSpeed_reparam



theorem riemannianCurveUnitTangent_reparam (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ t))
    (hφ : DifferentiableAt ℝ φ t) (hpos : 0 < deriv φ t) :
    riemannianCurveUnitTangent g (γ ∘ φ) t = riemannianCurveUnitTangent g γ (φ t) := by
  unfold riemannianCurveUnitTangent
  rw [riemannianCurveSpeed_reparam g hγ hφ, abs_of_pos hpos]
  erw [velocity_reparam hγ hφ]
  rw [smul_smul]
  congr 1
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveUnitTangent_reparam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveUnitTangent_reparam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveUnitTangent_reparam ``Submission.DifferentialGeometry.Geometry.riemannianCurveUnitTangent_reparam

end DifferentialGeometry.Geometry
