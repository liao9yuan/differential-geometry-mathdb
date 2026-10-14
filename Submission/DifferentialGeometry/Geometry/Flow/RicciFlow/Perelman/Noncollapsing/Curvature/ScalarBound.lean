import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem scalar_le_of_rm
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : ℝ} (ht : t ∈ Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ))
    {x : M} (hx : x ∈ B.setAt t) :
    DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4) := by
  have hnorm : FlowMetricBall.rmNormSq S t x ≤ 1 / B.radius ^ 4 := by
    apply (le_div_iff₀ (pow_pos B.radius_pos 4)).2
    simpa only [mul_comm] using hB.2 t ht x hx
  have hscalar :=
    DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
      (I := I) (M := M) (S.base.metric t) x
  have hscalar' :
      |DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| ≤
        (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
          Real.sqrt (FlowMetricBall.rmNormSq S t x) := by
    change |DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x| ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4
          (DifferentialGeometry.Geometry.Curvature.metricRm04At
            (I := I) (M := M) (S.base.metric t) x))
    exact hscalar
  calc
    DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x ≤
        |DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| := le_abs_self _
    _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (FlowMetricBall.rmNormSq S t x) := hscalar'
    _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnorm) (sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_le_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_le_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_le_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_le_of_rm

omit [SigmaCompactSpace M] in
theorem scalar_ge_of_rm
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : ℝ} (ht : t ∈ Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ))
    {x : M} (hx : x ∈ B.setAt t) :
    -((Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4)) ≤
      DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x := by
  have hnorm : FlowMetricBall.rmNormSq S t x ≤ 1 / B.radius ^ 4 := by
    apply (le_div_iff₀ (pow_pos B.radius_pos 4)).2
    simpa only [mul_comm] using hB.2 t ht x hx
  have hscalar :=
    DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm
      (I := I) (M := M) (S.base.metric t) x
  have hscalar' :
      |DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| ≤
        (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
          Real.sqrt (FlowMetricBall.rmNormSq S t x) := by
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04,
      DifferentialGeometry.Geometry.Curvature.metricRm04_apply] using hscalar
  have habs :
      |DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| ≤
        (Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
          Real.sqrt (1 / B.radius ^ 4) :=
    hscalar'.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnorm) (sq_nonneg _))
  calc
    -((Module.finrank ℝ (TangentSpace I x) : ℝ) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4)) ≤
        -|DifferentialGeometry.Geometry.Curvature.metricScalarAt
          (I := I) (M := M) (S.base.metric t) x| := neg_le_neg habs
    _ ≤ DifferentialGeometry.Geometry.Curvature.metricScalarAt
        (I := I) (M := M) (S.base.metric t) x := neg_abs_le _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_ge_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_ge_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_ge_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.scalar_ge_of_rm

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
