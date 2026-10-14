/-
Native wrapper for qinz1yang/differential-geometry v0.1.3.
Upstream commit: 7a48598d35109aa99d1cc678e2724c213cdf4ff3.
Lean: v4.33.1. Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.
The proof is supplied by the DifferentialGeometry contributors (Apache-2.0).

This proves the compact, simply connected formulation. It is NOT a proof of
MathDB's frozen Problem.Target: that target assumes a homotopy equivalence
with the sphere and requires compactness to be derived. MathDB also does not
currently list DifferentialGeometry among its supported external imports.

Upstream CI built the pinned source successfully. This new wrapper has not
been compiled locally against v0.1.3; the release supplies no build cache.
-/

import DifferentialGeometry.Topology.ThreeManifold.Poincare

set_option autoImplicit false

namespace Submission

universe u

/-- The usual closed, simply connected topological Poincare theorem. -/
theorem solution
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  exact DifferentialGeometry.Topology.poincare_conjecture M

end Submission

#print axioms Submission.solution
