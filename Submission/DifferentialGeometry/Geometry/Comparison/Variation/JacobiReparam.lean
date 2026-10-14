import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

theorem IsJacobiAt.comp_affine
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {J : ∀ t, TangentSpace I (γ t)} {c d t : ℝ}
    (hJ : IsJacobiAt g γ J (c * t + d))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)) :
    IsJacobiAt g (fun s => γ (c * s + d)) (fun s => J (c * s + d)) t := by
  let δ : ℝ → M := fun s => γ (c * s + d)
  let L : ∀ s, TangentSpace I (δ s) := fun s => J (c * s + d)
  let DJ : ∀ s, TangentSpace I (γ s) :=
    fun s => covDerivAlong (I := I) g γ J s
  have hDL : (fun s => covDerivAlong (I := I) g δ L s) =
      fun s => c • DJ (c * s + d) := by
    funext s
    exact covDeriv_comp_affine (I := I) g γ J c d s
  have hD2 :
      covDerivAlong (I := I) g δ
          (fun s => covDerivAlong (I := I) g δ L s) t =
        (c * c) • covDerivAlong (I := I) g γ DJ (c * t + d) := by
    rw [hDL]
    rw [covDerivAlong_smul]
    rw [covDeriv_comp_affine (I := I) g γ DJ c d t, smul_smul]
  have hvel :
      curveVelocity (I := I) δ t =
        c • curveVelocity (I := I) γ (c * t + d) := by
    exact curveVelocity_comp_affine (I := I) γ c d t
      hγ
  change
    covDerivAlong (I := I) g δ
        (fun s => covDerivAlong (I := I) g δ L s) t +
      (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          (δ t))
        (L t) (curveVelocity (I := I) δ t)
        (curveVelocity (I := I) δ t) = 0
  rw [hD2, hvel]
  simp only [map_smul, smul_apply, smul_smul]
  rw [← smul_add, hJ, smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.comp_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.comp_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.comp_affine ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAt.comp_affine

theorem IsJacobiAlong.comp_affine
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    {J : ∀ t, TangentSpace I (γ t)}
    (hJ : IsJacobiAlong g γ J) (hγ : MDifferentiable 𝓘(ℝ, ℝ) I γ) (c d : ℝ) :
    IsJacobiAlong g (fun s => γ (c * s + d)) (fun s => J (c * s + d)) := by
  intro t
  exact (hJ (c * t + d)).comp_affine (hγ (c * t + d))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong.comp_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong.comp_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong.comp_affine ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.IsJacobiAlong.comp_affine

end DifferentialGeometry.Geometry.Riemannian.Variation
