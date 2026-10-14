import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveModelCover
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorPositiveSectional
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover ∧
      IsQuotientCoveringMap cover (coveringDeckGroup cover) := by
  apply exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_sectional_pos
    (I := I) (M := M) h hdim
  intro x v w hvw
  apply metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
    (I := I) (M := M) g x
      (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim)
      (hrank x) (hcone x) v w hvw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three ``Submission.DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three

theorem exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3) :
    ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f cover := by
  obtain ⟨cover, hcover, _⟩ :=
    exists_roundThreeSphere_solitonModelQuotientCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
      (I := I) (M := M) h hdim hcone hrank
  exact ⟨cover, hcover⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three ``Submission.DifferentialGeometry.Geometry.exists_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three

theorem isSphericalSpaceForm_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3) :
    isSphericalSpaceForm (I := I) (M := M) := by
  let hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StandardAt (I := I) (M := M) g x v w w v := by
    intro x v w hvw
    exact metricRm04StdAt_pos_of_metricCurvatureOperatorRankAt_eq_three_of_nonnegative
      (I := I) (M := M) g x
        (by
          rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
          exact hdim)
        (hrank x) (hcone x) v w hvw
  have hconst : admitsConstantPositiveSectionalCurvature (I := I) (M := M) := by
    refine ⟨g, (1 / 4 : Real), by norm_num, ?_⟩
    exact gradientRicciSoliton_constant_sectional_curvature_of_compact_of_finrank_eq_three_of_sectional_pos
      (I := I) (M := M) h.2.1 hdim hsec
  exact constant_positive_sectional_curvature_implies_spherical_space_form
    (I := I) (M := M) ⟨inferInstance, inferInstance, inferInstance, hdim⟩ hconst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.isSphericalSpaceForm_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.isSphericalSpaceForm_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.isSphericalSpaceForm_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three ``Submission.DifferentialGeometry.Geometry.isSphericalSpaceForm_of_compact_of_finrank_eq_three_of_nonnegative_of_rank_three

end DifferentialGeometry.Geometry
