import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (three_bivector_quadratic_realized)
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_unit_area_plane_curvature_eq_leastCurvatureOperatorEigenvalueAt
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    ∃ v w : TangentSpace I x,
      g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 = 1 ∧
        tensor04StandardAt (A : Tensor04At (I := I) (M := M) x) v w w v =
          leastCurvatureOperatorEigenvalueAt g x A := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt g x hdim
  obtain ⟨c, hc, hmin⟩ := exists_leastCurvatureOperatorEigenvalueAt_rayleigh_minimizer
    g x basis horth A
  obtain ⟨v, w, hnorm, hcurv⟩ := three_bivector_quadratic_realized g x hdim A c
    (fun i => basis (bivectorIndex3 i).1) (fun i => basis (bivectorIndex3 i).2)
  exact ⟨v, w, hnorm.trans hc, hcurv.trans hmin⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_unit_area_plane_curvature_eq_leastCurvatureOperatorEigenvalueAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_unit_area_plane_curvature_eq_leastCurvatureOperatorEigenvalueAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_unit_area_plane_curvature_eq_leastCurvatureOperatorEigenvalueAt ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_unit_area_plane_curvature_eq_leastCurvatureOperatorEigenvalueAt

variable [T2Space M]

theorem exists_null_plane_of_leastCurvatureOperatorEigenvalueAt_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hzero : leastCurvatureOperatorEigenvalueAt g x
      (metricAlgebraicCurvatureTensorAt g x) = 0) :
    ∃ v w : TangentSpace I x,
      0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ∧
        metricRm04At g x (vec4 v w w v) = 0 := by
  obtain ⟨v, w, hnorm, hcurv⟩ :=
    exists_unit_area_plane_curvature_eq_leastCurvatureOperatorEigenvalueAt
      g x hdim (metricAlgebraicCurvatureTensorAt g x)
  refine ⟨v, w, by rw [hnorm]; norm_num, ?_⟩
  exact hcurv.trans hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_null_plane_of_leastCurvatureOperatorEigenvalueAt_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_null_plane_of_leastCurvatureOperatorEigenvalueAt_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_null_plane_of_leastCurvatureOperatorEigenvalueAt_eq_zero ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.exists_null_plane_of_leastCurvatureOperatorEigenvalueAt_eq_zero

end DifferentialGeometry.Geometry.Curvature.DimensionThree
