import Submission.DifferentialGeometry.Geometry.Curvature.PositiveSectional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


theorem sectional_contraction_smul_pair (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (a b : ℝ) :
    metricRm04StandardAt g x (a • v) (b • w) (b • w) (a • v) =
      a ^ 2 * b ^ 2 * metricRm04StandardAt g x v w w v := by
  have h := (metricRm04At g x).map_smul_univ ![a, b, b, a] (vec4 v w w v)
  have hv : (fun i : Fin 4 => ![a, b, b, a] i • vec4 v w w v i) =
      vec4 (a • v) (b • w) (b • w) (a • v) := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  change metricRm04StandardAt g x (a • v) (b • w) (b • w) (a • v) = _ at h
  rw [h]
  simp only [Fin.prod_univ_four]
  change (a * b * b * a) * metricRm04StandardAt g x v w w v = _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sectional_contraction_smul_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sectional_contraction_smul_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sectional_contraction_smul_pair ``Submission.DifferentialGeometry.Geometry.sectional_contraction_smul_pair

end DifferentialGeometry.Geometry
