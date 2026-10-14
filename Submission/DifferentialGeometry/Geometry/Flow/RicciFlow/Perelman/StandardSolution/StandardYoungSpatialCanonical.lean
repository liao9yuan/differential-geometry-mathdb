import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialSpatialCanonical
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSpatialCanonical

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

theorem StandardSolution.exists_youngSpatiallyCanonical_of_le_initial_time
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ τ C : ℝ, 0 < τ ∧ 1 ≤ C ∧ ∀ Θ τmin : ℝ, Θ < 1 → τmin ≤ τ →
      StandardSolution.YoungSpatiallyCanonical Θ eps C τmin := by
  obtain ⟨τ, C, hτ, hC, hinit⟩ :=
    StandardSolution.exists_initial_spatialCanonicalWitness_with_cap_neck_charts heps hsmall
  refine ⟨τ, C, hτ, hC, fun Θ τmin hΘ hτmin S x t ht hyoung => hinit S x t ⟨ht.1, ?_⟩⟩
  have hR := S.val.one_le_scalar t (S.mem_domain_of_mem_Icc hΘ ht) x
  nlinarith [ht.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_youngSpatiallyCanonical_of_le_initial_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_youngSpatiallyCanonical_of_le_initial_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_youngSpatiallyCanonical_of_le_initial_time ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_youngSpatiallyCanonical_of_le_initial_time

def StandardSolution.BoundedCurvatureSpatiallyCanonical (Θ eps τ₀ Λ C : ℝ) : Prop :=
  ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ), t ∈ _root_.Set.Icc τ₀ Θ →
    metricScalarAt (S.val.metric t) x ≤ Λ →
      ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.BoundedCurvatureSpatiallyCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.BoundedCurvatureSpatiallyCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.BoundedCurvatureSpatiallyCanonical ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.BoundedCurvatureSpatiallyCanonical

theorem StandardSolution.youngSpatiallyCanonical_of_bounded_curvature
    {eps Θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1)
    (hband : ∀ τ₀ Λ : ℝ, 0 < τ₀ →
      ∃ C : ℝ, 1 ≤ C ∧ StandardSolution.BoundedCurvatureSpatiallyCanonical Θ eps τ₀ Λ C) :
    ∀ τmin : ℝ, 0 < τmin →
      ∃ C : ℝ, 1 ≤ C ∧ StandardSolution.YoungSpatiallyCanonical Θ eps C τmin := by
  intro τmin _
  obtain ⟨τ, C₀, hτ, hC₀, hinit⟩ :=
    StandardSolution.exists_initial_spatialCanonicalWitness_with_cap_neck_charts heps hsmall
  obtain ⟨C₁, hC₁, hlate⟩ := hband τ (τmin / τ) hτ
  refine ⟨max C₀ C₁, hC₀.trans (le_max_left _ _), fun S x t ht hyoung => ?_⟩
  rcases le_or_gt t τ with htτ | htτ
  · obtain ⟨W, hW⟩ := hinit S x t ⟨ht.1, htτ⟩
    exact ⟨W.enlargeConstants (le_max_left _ _) (le_max_left _ _),
      hW.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩
  · have hR := S.val.one_le_scalar t (S.mem_domain_of_mem_Icc hΘ ht) x
    have hΛ : metricScalarAt (S.val.metric t) x ≤ τmin / τ := by
      rw [le_div_iff₀ hτ]
      nlinarith
    obtain ⟨W, hW⟩ := hlate S x t ⟨htτ.le, ht.2⟩ hΛ
    exact ⟨W.enlargeConstants (le_max_right _ _) (le_max_right _ _),
      hW.enlarge_constants (le_max_right _ _) (le_max_right _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.youngSpatiallyCanonical_of_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.youngSpatiallyCanonical_of_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.youngSpatiallyCanonical_of_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.youngSpatiallyCanonical_of_bounded_curvature

theorem StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_bounded_curvature
    {eps Θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1)
    (hband : ∀ τ₀ Λ : ℝ, 0 < τ₀ →
      ∃ C : ℝ, 1 ≤ C ∧ StandardSolution.BoundedCurvatureSpatiallyCanonical Θ eps τ₀ Λ C) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ _root_.Set.Icc 0 Θ →
        ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps :=
  StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_young heps hsmall hΘ
    (StandardSolution.youngSpatiallyCanonical_of_bounded_curvature heps hsmall hΘ hband)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_bounded_curvature

end DifferentialGeometry.PDE.RicciFlow
