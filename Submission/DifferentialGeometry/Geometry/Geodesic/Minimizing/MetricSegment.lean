import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteMetricSegment
import Submission.DifferentialGeometry.Geometry.Geodesic.Minimizing.TriangleEquality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Riemannian

export DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
  (exists_intrinsicGeodesic_eq_metric_segment)

end DifferentialGeometry.Geometry.Riemannian
