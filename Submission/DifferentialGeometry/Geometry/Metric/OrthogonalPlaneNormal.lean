import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



def orthogonalPlaneNormal (g : SmoothRiemannianMetric I M) (x : M)
    (p q X : TangentSpace I x) : TangentSpace I x :=
  X - (g.inner x X p / g.inner x p p) • p - (g.inner x X q / g.inner x q q) • q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.orthogonalPlaneNormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.orthogonalPlaneNormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.orthogonalPlaneNormal ``Submission.DifferentialGeometry.Geometry.orthogonalPlaneNormal



theorem orthogonalPlaneNormal_inner_self (g : SmoothRiemannianMetric I M) (x : M)
    (p q X : TangentSpace I x) (hpq : g.inner x p q = 0)
    (hp : g.inner x p p ≠ 0) (hq : g.inner x q q ≠ 0) :
    g.inner x (orthogonalPlaneNormal g x p q X) (orthogonalPlaneNormal g x p q X) =
      g.inner x X X - (g.inner x X p) ^ 2 / g.inner x p p -
        (g.inner x X q) ^ 2 / g.inner x q q := by
  simp only [orthogonalPlaneNormal, map_sub, map_smul, _root_.sub_apply,
    _root_.smul_apply, smul_eq_mul, g.symm x p X, g.symm x q X, g.symm x q p, hpq,
    _root_.MulZeroClass.mul_zero, sub_zero]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.orthogonalPlaneNormal_inner_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.orthogonalPlaneNormal_inner_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.orthogonalPlaneNormal_inner_self ``Submission.DifferentialGeometry.Geometry.orthogonalPlaneNormal_inner_self


theorem orthogonalPlaneNormal_orthogonal (g : SmoothRiemannianMetric I M) (x : M)
    (p q X : TangentSpace I x) (hpq : g.inner x p q = 0)
    (hp : g.inner x p p ≠ 0) (hq : g.inner x q q ≠ 0) :
    g.inner x (orthogonalPlaneNormal g x p q X) p = 0 ∧
      g.inner x (orthogonalPlaneNormal g x p q X) q = 0 := by
  constructor <;>
    simp only [orthogonalPlaneNormal, map_sub, map_smul, _root_.sub_apply,
      _root_.smul_apply, smul_eq_mul, g.symm x q p, hpq, _root_.MulZeroClass.mul_zero, sub_zero]
  · rw [div_mul_cancel₀ _ hp, sub_self]
  · rw [div_mul_cancel₀ _ hq, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.orthogonalPlaneNormal_orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.orthogonalPlaneNormal_orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.orthogonalPlaneNormal_orthogonal ``Submission.DifferentialGeometry.Geometry.orthogonalPlaneNormal_orthogonal

end DifferentialGeometry.Geometry
