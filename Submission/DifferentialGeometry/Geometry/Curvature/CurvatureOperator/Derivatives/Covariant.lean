import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem curvStep_eq_covStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    curvCovDerivStep (I := I) g a A =
      covStep (I := I) g (a + 4) A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvStep_eq_covStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvStep_eq_covStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvStep_eq_covStep ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvStep_eq_covStep

end DifferentialGeometry.CheegerGromovCompactness
