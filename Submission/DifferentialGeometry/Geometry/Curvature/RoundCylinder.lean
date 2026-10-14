import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.SurfaceProductRank
import Submission.DifferentialGeometry.Geometry.Curvature.Cylinder
import Submission.DifferentialGeometry.Geometry.Curvature.RoundSphere
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarTrace
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem ricciTensor_roundCylinder (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    ricciTensor (roundCylinderMetric (E := E) (n := n)) x v w =
      ((n : ℝ) - 1) * (roundMetric (E := E) (n := n)).inner x.1 v.1 w.1 := by
  exact (ricciTensor_cylinderMetric _ x v w).trans
    ((ricciTensor_scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n))
      x.1 v.1 w.1).trans
        (ricciTensor_roundSphere x.1 v.1 w.1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_roundCylinder ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_roundCylinder

theorem ricciSharp_roundCylinder (x : Metric.sphere (0 : E) 1 × ℝ)
    (v : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    ricciSharp (roundCylinderMetric (E := E) (n := n)) x v =
      ((((n : ℝ) - 1) / 2) • v.1, (0 : ℝ)) := by
  let g := roundCylinderMetric (E := E) (n := n)
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq g
  intro w
  rw [inner_ricciSharp, ricciTensor_roundCylinder]
  change _ = (cylinderMetric (scaleMetric 2 (by norm_num)
    (roundMetric (E := E) (n := n)))).inner x
      ((((n : ℝ) - 1) / 2) • v.1, (0 : ℝ)) w
  have hi := cylinderMetric_inner
    (scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n))) x
    (((((n : ℝ) - 1) / 2) • v.1, (0 : ℝ))) w
  rw [hi]
  change ((n : ℝ) - 1) * (roundMetric (E := E) (n := n)).inner x.1 v.1 w.1 =
    2 * (roundMetric (E := E) (n := n)).inner x.1 ((((n : ℝ) - 1) / 2) • v.1) w.1 +
      0 * w.2
  have hs := congrArg
    (fun L : TangentSpace (𝓡 n) x.1 →L[ℝ] ℝ ↦ L w.1)
    (((roundMetric (E := E) (n := n)).inner x.1).map_smul (((n : ℝ) - 1) / 2) v.1)
  change (roundMetric (E := E) (n := n)).inner x.1
      ((((n : ℝ) - 1) / 2) • v.1) w.1 =
    (((n : ℝ) - 1) / 2) * (roundMetric (E := E) (n := n)).inner x.1 v.1 w.1 at hs
  linear_combination (norm := ring!) -2 * hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciSharp_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciSharp_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciSharp_roundCylinder ``Submission.DifferentialGeometry.Geometry.Curvature.ricciSharp_roundCylinder

theorem metricScalarAt_roundCylinder (x : Metric.sphere (0 : E) 1 × ℝ) :
    metricScalarAt (roundCylinderMetric (E := E) (n := n)) x =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ)) := ⟨by simp⟩
  have he : ((ricciSharp (roundCylinderMetric (E := E) (n := n)) x).toLinearMap :
      (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ)) =
      LinearMap.prodMap ((((n : ℝ) - 1) / 2) •
        (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
        (0 : ℝ →ₗ[ℝ] ℝ) := by
    apply LinearMap.ext
    intro v
    exact ricciSharp_roundCylinder x v
  have ht := congrArg (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n) × ℝ)) he
  refine (metricScalar_eq_trace_ricciSharp _ x).trans (ht.trans ?_)
  rw [LinearMap.trace_prodMap', map_smul, LinearMap.trace_id, map_zero]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, add_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_roundCylinder ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_roundCylinder

end DifferentialGeometry.Geometry.Curvature

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2 + 1)]

theorem metricCurvatureOperatorRankAt_roundCylinder
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    metricCurvatureOperatorRankAt
      (Geometry.Metric.roundCylinderMetric (E := E) (n := 2)) x (by
        change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3
        simp [Module.finrank_prod]) = 1 := by
  let g := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  have hprod : Geometry.Metric.roundCylinderMetric (E := E) (n := 2) =
      g.prod (euclideanMetric (E := ℝ)) := by
    ext q v w
    rw [Geometry.Metric.roundCylinderMetric_inner, SmoothRiemannianMetric.prod_inner]
    change 2 * _root_.Inner.inner ℝ (dIncl q.1 v.1) (dIncl q.1 w.1) + v.2 * w.2 =
      2 * (roundMetric (E := E) (n := 2)).inner q.1 v.1 w.1 +
        _root_.Inner.inner ℝ v.2 w.2
    erw [roundMetric_inner]
    simp [mul_comm]
  have hscalar : metricScalarAt g x.1 ≠ 0 := by
    have hs := metricScalarAt_roundCylinder (E := E) (n := 2) x
    rw [hprod, metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp),
      add_zero] at hs
    norm_num at hs
    rw [hs]
    norm_num
  rw [hprod, metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
  exact curvatureOperatorImageAt_finrank_prod_real_eq_one_of_scalar_ne_zero
    g (by simp) x hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.metricCurvatureOperatorRankAt_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.metricCurvatureOperatorRankAt_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.metricCurvatureOperatorRankAt_roundCylinder ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.metricCurvatureOperatorRankAt_roundCylinder

theorem curvatureOperatorImageAt_finrank_roundCylinder
    (x : Metric.sphere (0 : E) 1 × ℝ) :
    Module.finrank ℝ (curvatureOperatorImageAt
      (Geometry.Metric.roundCylinderMetric (E := E) (n := 2)) x
      (metricAlgebraicCurvatureTensorAt
        (Geometry.Metric.roundCylinderMetric (E := E) (n := 2)) x)) = 1 := by
  have h := metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
    (Geometry.Metric.roundCylinderMetric (E := E) (n := 2)) x (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3
      simp [Module.finrank_prod])
  exact h.symm.trans (metricCurvatureOperatorRankAt_roundCylinder x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_roundCylinder ``Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_roundCylinder

end DifferentialGeometry.Geometry.Curvature.DimensionThree
