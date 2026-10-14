import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.CompleteTriangleEquality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Riemannian

export DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
  (intrinsicGeodesic_continues_of_distance_add unit_intrinsic_vector_eq_of_short_endpoint
    exists_intrinsicGeodesic_eq_short_metric_segment
    exists_intrinsicGeodesic_eq_centered_metric_segment)

end DifferentialGeometry.Geometry.Riemannian
