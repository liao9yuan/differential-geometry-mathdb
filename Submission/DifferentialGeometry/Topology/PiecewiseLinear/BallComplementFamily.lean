/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPolyhedron.sdiff_iUnion_interior_of_isPLBall
    {n : ℕ} {ι : Type*} [Finite ι]
    {D : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {H : ι → Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hD : IsPolyhedron D) (hH : ∀ i, IsPLBall (n + 1) (H i)) :
    IsPolyhedron (D \ ⋃ i, interior (H i)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hind : ∀ d : Finset ι, IsPolyhedron (D \ ⋃ i ∈ d, interior (H i)) := by
    intro d
    induction d using Finset.induction_on with
    | empty => simpa using hD
    | @insert i d _ ih =>
      rw [Finset.set_biUnion_insert]
      convert ih.sdiff_interior_of_isPLBall (hH i) using 1
      ext x
      simp only [_root_.Set.mem_sdiff, _root_.Set.mem_union]
      tauto
  simpa only [Finset.mem_univ, _root_.Set.iUnion_true] using hind Finset.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_iUnion_interior_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_iUnion_interior_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_iUnion_interior_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_iUnion_interior_of_isPLBall

end DifferentialGeometry.Topology.PiecewiseLinear
