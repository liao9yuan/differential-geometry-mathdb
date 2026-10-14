import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem chartChristoffelContraction_opens_basepoint_eq
    (U : TopologicalSpace.Opens F) (G : SmoothRiemannianMetric 𝓘(ℝ, F) U)
    (α β : U) (v w y : F) :
    chartChristoffelContraction G α v w y =
      chartChristoffelContraction G β v w y := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_opens_basepoint_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_opens_basepoint_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_opens_basepoint_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.chartChristoffelContraction_opens_basepoint_eq

end DifferentialGeometry.Geometry.Riemannian.Geodesic
