import Submission.DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinder
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarPerturbation
import Submission.DifferentialGeometry.Geometry.Metric.RoundCylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem metricScalarAt_restricted_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ)) (x : U) :
    metricScalarAt ((roundCylinderMetric (E := E) (n := n)).restrictOpen U) x =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ)) := ⟨by simp⟩
  have he : ((ricciSharp ((roundCylinderMetric (E := E) (n := n)).restrictOpen U)
      x).toLinearMap : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) × ℝ)) =
      LinearMap.prodMap ((((n : ℝ) - 1) / 2) •
        (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
        (0 : ℝ →ₗ[ℝ] ℝ) := by
    apply LinearMap.ext
    intro v
    exact ricciSharp_restricted_roundCylinder U x v
  have ht := congrArg (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n) × ℝ)) he
  refine (metricScalar_eq_trace_ricciSharp _ x).trans (ht.trans ?_)
  rw [LinearMap.trace_prodMap', map_smul, LinearMap.trace_id, map_zero]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, add_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_restricted_roundCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_restricted_roundCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_restricted_roundCylinder ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_restricted_roundCylinder

theorem abs_scalar_curvature_restricted_roundCylinder_sub_one_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (U : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) U)
    (x : U) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen U) x ≤ ε) :
    |metricScalarAt g x - 1| ≤ 4323 * ε := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩
  let gRef := (roundCylinderMetric (E := E) (n := 2)).restrictOpen U
  have h := abs_scalar_curvature_sub_le_of_ricci_operator_difference
    g gRef gRef x (1441 * ε)
    (fun v ↦ ricciSharp_restricted_roundCylinder_difference_bound U g x ε hε hsmall v)
  dsimp only [gRef] at h
  rw [metricScalarAt_restricted_roundCylinder] at h
  norm_num only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
  convert h using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.abs_scalar_curvature_restricted_roundCylinder_sub_one_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.abs_scalar_curvature_restricted_roundCylinder_sub_one_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.abs_scalar_curvature_restricted_roundCylinder_sub_one_le ``Submission.DifferentialGeometry.Geometry.Curvature.abs_scalar_curvature_restricted_roundCylinder_sub_one_le

end DifferentialGeometry.Geometry.Curvature
