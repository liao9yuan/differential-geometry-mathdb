import Submission.DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.EndpointPositivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem jacobi_eq_zero_of_endpoints_eq_zero
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {U : Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hU : IsOpen U) (hseg : _root_.Set.Icc a b ⊆ U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U)
    (hJdiff : ∀ t ∈ _root_.Set.Icc a b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ _root_.Set.Icc a b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hJac : ∀ t ∈ _root_.Set.Icc a b, IsJacobiAt (I := I) g γ J t)
    (hJa : J a = 0) (hJb : J b = 0)
    {κ : ℝ} (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2)
    (hcurv : ∀ t ∈ _root_.Set.Ioo a b,
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)) (J t) ≤
        κ * g.inner (γ t) (J t) (J t)) :
    ∀ t ∈ _root_.Set.Icc a b, J t = 0 := by
  by_contra hne
  have hp := jacobi_pair_pos g γ J hab hU hseg hγ hJdiff hDJdiff hJac hJa hne hκ hcurv
  simp only [hJb, map_zero, lt_self_iff_false] at hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_eq_zero_of_endpoints_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_eq_zero_of_endpoints_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_eq_zero_of_endpoints_eq_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.jacobi_eq_zero_of_endpoints_eq_zero

end DifferentialGeometry.Geometry.Riemannian.Variation
