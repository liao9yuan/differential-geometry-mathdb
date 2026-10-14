import Submission.DifferentialGeometry.Geometry.Metric.Family.Cartesian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow

theorem PartialStandardSolution.metricFamilySmoothOn (S : PartialStandardSolution) :
    MetricFamilySmoothOn (lifetimeInterval S.lifetime S.lifetime_pos) S.metric := by
  exact metricFamilySmoothOn_of_cartesian_smooth _ S.metric S.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metricFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metricFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metricFamilySmoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metricFamilySmoothOn

end DifferentialGeometry.PDE.RicciFlow
