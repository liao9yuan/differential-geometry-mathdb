/-
Poincare homotopy-sphere adapter for MathDB's frozen problem.
This MathDB submission fork is based on Ziyang Qin's repository,
qinz1yang/differential-geometry v0.1.3 (7a48598d35109aa99d1cc678e2724c213cdf4ff3),
with the homotopy-sphere compactness bridge backported from v0.1.4.
The upstream mathematical proofs and their Apache-2.0 notices are preserved.
-/

import FtpEvalBench.YPoincare_poincare_conjecture
import Submission.DifferentialGeometry.Topology.ThreeManifold.Poincare
import Submission.DifferentialGeometry.Topology.Homology.Spheres.HomotopySphereCompactness
import Submission.DifferentialGeometry.Topology.Sphere.SphereSimplyConnected

set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

theorem solution : _root_.Problem.Target := by
  intro M _ _ _ h
  let : CompactSpace M :=
    _root_.Submission.DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere h
  let : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    _root_.Submission.DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_two_le (by decide : 2 ≤ 3)
  let : SimplyConnectedSpace M := h.simplyConnectedSpace
  exact _root_.Submission.DifferentialGeometry.Topology.poincare_conjecture M

end Submission

#print axioms Submission.solution
