/-
Poincare homotopy-sphere adapter for MathDB's frozen problem.
Based on qinz1yang/differential-geometry v0.1.3 (7a48598d35109aa99d1cc678e2724c213cdf4ff3),
with the homotopy-sphere compactness bridge backported from v0.1.4.
The upstream mathematical proofs and their Apache-2.0 notices are preserved.
-/

import FtpEvalBench.YPoincare_poincare_conjecture
import DifferentialGeometry.Topology.ThreeManifold.Poincare
import DifferentialGeometry.Topology.Homology.Spheres.HomotopySphereCompactness
import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected

set_option autoImplicit false

namespace Submission

theorem solution : Problem.Target := by
  intro M _ _ _ h
  let : CompactSpace M :=
    DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere h
  let : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_two_le (by decide : 2 ≤ 3)
  let : SimplyConnectedSpace M := h.simplyConnectedSpace
  exact DifferentialGeometry.Topology.poincare_conjecture M

end Submission

#print axioms Submission.solution
