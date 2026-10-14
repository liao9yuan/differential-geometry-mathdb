import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormChartConvergence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ChartConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

export DifferentialGeometry.CheegerGromovCompactness
  (tensor_norm_tendsto_of_smooth_chart_convergence
    tensor02_covariant_norm_tendsto_of_smooth_chart_convergence)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
