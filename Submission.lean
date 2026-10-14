/-
Copyright 2026 The DifferentialGeometry contributors.
Released under the Apache License 2.0.

A submission entry point for the homotopy-sphere form of the Poincaré theorem,
using qinz1yang/differential-geometry release v0.1.4, commit
788efe97894474c032de6dfb1289d515f613d15a.

This file requires the upstream project's Lean/Mathlib v4.35.0-rc3 environment.
It proves the mathematical statement of MathDB's Poincaré Problem.Target,
but is not compatible with the frozen MathDB Lean v4.33.1 environment.
-/

import DifferentialGeometry.Topology.ThreeManifold.Poincare
import DifferentialGeometry.Topology.Homology.Spheres.HomotopySphereCompactness
import DifferentialGeometry.Topology.Sphere.SphereSimplyConnected

set_option autoImplicit false
open scoped ContinuousMap

namespace Submission

/-- Every Hausdorff topological three-manifold homotopy equivalent to the
unit three-sphere is homeomorphic to that sphere. -/
theorem solution :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
      M ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  intro M _ _ _ h
  let : CompactSpace M :=
    DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere h
  let : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphere_of_two_le (by decide : 2 ≤ 3)
  let : SimplyConnectedSpace M := h.simplyConnectedSpace
  exact DifferentialGeometry.Topology.poincare_conjecture M

end Submission

#print axioms Submission.solution
