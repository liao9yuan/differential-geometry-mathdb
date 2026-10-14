import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Geometry.Operator.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normGradSqFun_scaleMetric
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (f : M → Real) (x : M) :
    normGradSqFun (I := I) (scaleMetric (I := I) c hc g) f x =
      c⁻¹ * normGradSqFun (I := I) g f x := by
  rw [normGradSqFun_def, normGradSqFun_def]
  rw [show gradFun (I := I) (scaleMetric (I := I) c hc g) f x =
      c⁻¹ • gradFun (I := I) g f x by
    exact gradientFun_scale (I := I) c hc g f x]
  rw [scaleMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_scaleMetric ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_scaleMetric

end DifferentialGeometry.Geometry.Operator
