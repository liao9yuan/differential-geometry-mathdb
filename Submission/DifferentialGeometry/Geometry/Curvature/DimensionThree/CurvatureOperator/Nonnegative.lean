import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3) :
    metricAlgebraicCurvatureTensorAt g x ∈ algebraicCurvatureOperatorNonnegativeCone (I := I) ↔
      ∀ v w : TangentSpace I x, 0 ≤ metricRm04StandardAt g x v w w v := by
  constructor
  · intro h v w
    have hq := mem_algebraicCurvatureOperatorNonnegativeCone.mp h 1
      (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
      metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using hq
  · intro h
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    obtain ⟨a, b, _hgram, hvalue⟩ :=
      DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.three_bivector_quadratic_realized
        g x hdim (metricAlgebraicCurvatureTensorAt g x) c v w
    rw [← hvalue]
    simpa only [metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using h a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional

end DifferentialGeometry.Geometry.Curvature
