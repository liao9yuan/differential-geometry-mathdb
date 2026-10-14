import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ChartGramContinuity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval}

namespace SolutionOn

theorem continuousOn_volume (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) :
    ContinuousOn (fun t => (riemannianVolumeMeasure I M (S.family.metric t) _root_.Set.univ).toReal)
      D.carrier := by
  have hi := continuousOn_integral_riemannianVolumeMeasure_of_compact_support
    S.family.metric
    hS.smoothMetric.metricTensor_cont.continuousOn_chartGram
    (fun _ _ => (1 : ℝ)) continuousOn_const isCompact_univ
    (fun _ _ _ hx => (hx (_root_.Set.mem_univ _)).elim)
  simpa only [_root_.MeasureTheory.integral_const, smul_eq_mul, mul_one, Measure.real_def] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_volume ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.continuousOn_volume

end SolutionOn

end DifferentialGeometry.PDE.RicciFlow
