import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Defs

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

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem ricci_ge_of_rm
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : Real}
    (ht : t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    {x : M} (hx : x ∈ B.setAt t) (v : TangentSpace I x) :
    -((Module.finrank Real E : Real) ^ 2 *
        Real.sqrt (1 / B.radius ^ 4)) *
          (S.base.metric t).inner x v v ≤
      ricciTensor (I := I) (S.base.metric t) x v v := by
  have hnorm : FlowMetricBall.rmNormSq S t x ≤ 1 / B.radius ^ 4 := by
    apply (le_div_iff₀ (pow_pos B.radius_pos 4)).2
    simpa only [mul_comm] using hB.2 t ht x hx
  have hroot :
      Real.sqrt
          (Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4
            (metricRm04At (I := I) (M := M) (S.base.metric t) x)) ≤
        Real.sqrt (1 / B.radius ^ 4) := by
    apply Real.sqrt_le_sqrt
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04, metricRm04_apply] using hnorm
  exact Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm
    (I := I) (S.base.metric t) hroot v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_ge_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_ge_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_ge_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_ge_of_rm

omit [SigmaCompactSpace M] in
theorem ricci_abs_of_rm
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {t : Real}
    (ht : t ∈ Set.Icc ((time : Real) - B.radius ^ 2) (time : Real))
    {x : M} (hx : x ∈ B.setAt t) (v : TangentSpace I x) :
    |ricciTensor (I := I) (S.base.metric t) x v v| ≤
      (Module.finrank Real E : Real) ^ 2 *
          Real.sqrt (1 / B.radius ^ 4) *
        (S.base.metric t).inner x v v := by
  have hnorm : FlowMetricBall.rmNormSq S t x ≤ 1 / B.radius ^ 4 := by
    apply (le_div_iff₀ (pow_pos B.radius_pos 4)).2
    simpa only [mul_comm] using hB.2 t ht x hx
  simpa only [FlowMetricBall.rmNormSq] using
    (ricci_quadratic_form_bound_of_solution_curvature_bound (I := I) S x v hnorm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_abs_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_abs_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_abs_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.ricci_abs_of_rm

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
