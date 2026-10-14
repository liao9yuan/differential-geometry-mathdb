import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianModelCover
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.PositiveModelCover
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceCompactness
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceMorse

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

theorem exists_gaussian_or_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) :
    (∃ cover : E → M,
      solitonModelCovering (euclideanMetric (E := E))
        (gaussianPotential (E := E)) g f cover) ∨
      ∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M,
        solitonModelCovering roundTwoSphereShrinkerMetric
            roundTwoSphereShrinkerPotential g f cover ∧
          IsQuotientCoveringMap cover (coveringDeckGroup cover) ∧
          ((∃ e : Metric.sphere
              (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₜ M,
              ∀ x, e x = cover x) ∨
            (∃ e : RealProjectivePlane ≃ₜ M,
              ∀ x, e (realProjectivePlaneQuotientMap x) = cover x)) := by
  by_cases hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1
  · left
    exact exists_solitonModelCovering_of_isGaussianGradientRicciSoliton h hGaussian
  · right
    let _ : CompactSpace M :=
      normalizedGradientRicciSoliton_compactSpace_of_finrank_eq_two_of_not_isGaussian
        (I := I) h hdim hGaussian
    have hscalar :=
      normalizedGradientRicciSoliton_scalar_eq_one_of_compact_of_finrank_eq_two
        (I := I) (E := E) h hdim
    exact
      exists_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_compact_of_finrank_eq_two_of_scalar_eq_one
        (I := I) h hdim hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_gaussian_or_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_finrank_eq_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_gaussian_or_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_finrank_eq_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_gaussian_or_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_finrank_eq_two ``Submission.DifferentialGeometry.Geometry.exists_gaussian_or_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_finrank_eq_two

end DifferentialGeometry.Geometry
