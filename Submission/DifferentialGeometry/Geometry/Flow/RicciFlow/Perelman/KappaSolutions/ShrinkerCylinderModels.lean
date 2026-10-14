import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderModelEvolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} I)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem cylinder_antipodal_scalar_one (x : CylinderAntipodalQuotient) :
    metricScalarAt cylinderAntipodalQuotientMetric x = 1 := by
  obtain ⟨y, rfl⟩ := cylinderAntipodalQuotientMap_surjective x
  rw [← metricScalarAt_localPull cylinderAntipodalQuotientMetric
    cylinderAntipodalQuotientMap cylinderAntipodalQuotientMap_isLocalDiffeomorph,
    localPullMetric_cylinderAntipodalQuotientMetric]
  exact roundThreeCylinderShrinkerMetric_scalarCurvature y

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_antipodal_scalar_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_antipodal_scalar_one target :: scope.openDecls } }

private theorem cylinder_diagonal_scalar_one (x : DifferentialGeometry.Geometry.CylinderDiagonalQuotient) :
    metricScalarAt cylinderDiagonalQuotientMetric x = 1 := by
  obtain ⟨y, rfl⟩ := cylinderDiagonalQuotientMap_surjective x
  rw [← metricScalarAt_localPull cylinderDiagonalQuotientMetric
    cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph,
    localPullMetric_cylinderDiagonalQuotientMetric]
  exact roundThreeCylinderShrinkerMetric_scalarCurvature y

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_diagonal_scalar_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.cylinder_diagonal_scalar_one target :: scope.openDecls } }

theorem NoncompactShrinkerIsometryModels.scalar_eq_one
    {g : SmoothRiemannianMetric I L.M} {f : C^∞⟮I, L.M; ℝ⟯}
    (h : NoncompactShrinkerIsometryModels L g f) (x : L.M) : metricScalarAt g x = 1 := by
  rcases h with ⟨e, he, _hf⟩ | ⟨e, he, _hf⟩ | ⟨e, he, _hf⟩
  · have hh := metricScalar_cross g e (e.symm x)
    rw [e.apply_symm_apply, he] at hh
    exact hh.symm.trans (roundThreeCylinderShrinkerMetric_scalarCurvature _)
  · let d := cylinderAntipodalQuotientDiffeomorph.trans e
    have hd : Diffeomorph.pullbackMetricCross g d = cylinderAntipodalQuotientMetric := by
      rw [← Diffeomorph.pullbackMetricCross_trans, he,
        cylinderAntipodalQuotientDiffeomorph_pullbackMetric]
    have hh := metricScalar_cross g d (d.symm x)
    rw [d.apply_symm_apply, hd] at hh
    exact hh.symm.trans (cylinder_antipodal_scalar_one _)
  · have hh := metricScalar_cross g e (e.symm x)
    rw [e.apply_symm_apply, he] at hh
    exact hh.symm.trans (cylinder_diagonal_scalar_one _)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.scalar_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.scalar_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.scalar_eq_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.scalar_eq_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section
set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (L : PointedRiemannianManifold.{u, uE, uH} I)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

omit [CompleteSpace E] in
theorem NoncompactShrinkerIsometryModels.exists_shrinking_quotient_models
    {g : ℝ → SmoothRiemannianMetric I L.M} {f : C^∞⟮I, L.M; ℝ⟯}
    (h : NoncompactShrinkerIsometryModels L (g 0) f)
    (hflow : ∀ t : ℝ, t ≤ 0 → ∀ x : L.M, ∀ v w : TangentSpace I x,
      (g t).inner x v w = (g 0).inner x v w - 2 * t * ricciTensor (g 0) x v w) :
    (∃ d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0, Diffeomorph.pullbackMetricCross (g t) d =
        scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      ∀ x : SpatialNeckCylinder, f (d x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ d : (DifferentialGeometry.RealProjectivePlane × ℝ) ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (g t)
          (cylinderAntipodalQuotientDiffeomorph.trans d)) cylinderAntipodalQuotientMap
          cylinderAntipodalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      ∀ x : DifferentialGeometry.RealProjectivePlane × ℝ, f (d x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ d : DifferentialGeometry.Geometry.CylinderDiagonalQuotient ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (g t) d) cylinderDiagonalQuotientMap
          cylinderDiagonalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      ∀ x : DifferentialGeometry.Geometry.CylinderDiagonalQuotient,
        f (d x) = cylinderDiagonalQuotientPotential x) := by
  rcases h with ⟨d, hd, hf⟩ | ⟨d, hd, hf⟩ | ⟨d, hd, hf⟩
  · exact Or.inl ⟨d, fun t ht =>
      pullbackMetric_eq_shrinkingCylinderMetric_of_affine_ricci g hflow d hd t ht, hf⟩
  · refine Or.inr (Or.inl ⟨d, ?_, hf⟩)
    have hzero : Diffeomorph.pullbackMetricCross (g 0)
        (cylinderAntipodalQuotientDiffeomorph.trans d) = cylinderAntipodalQuotientMetric := by
      rw [← Diffeomorph.pullbackMetricCross_trans, hd,
        cylinderAntipodalQuotientDiffeomorph_pullbackMetric]
    exact fun t ht => pullback_antipodalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci
      g hflow (cylinderAntipodalQuotientDiffeomorph.trans d) hzero t ht
  · exact Or.inr (Or.inr ⟨d, fun t ht =>
      pullback_diagonalQuotient_metric_eq_shrinkingCylinderMetric_of_affine_ricci g hflow d hd t ht, hf⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.exists_shrinking_quotient_models then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.exists_shrinking_quotient_models"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.exists_shrinking_quotient_models ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerIsometryModels.exists_shrinking_quotient_models

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
