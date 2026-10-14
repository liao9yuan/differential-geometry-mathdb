/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

open _root_.Classical in
theorem PLPieceIn.isPLHomeomorphOn_euclidean {S : Set (EuclideanSpace ℝ (Fin n))}
    (T : PLPieceIn E n (EuclideanSpace ℝ (Fin n)) S) :
    IsPLHomeomorphOn T.map T.complex.space S := by
  refine ⟨T.bijOn, ?_, ?_⟩
  · have h := T.isPiecewiseAffineOn_chart (chartAt (EuclideanSpace ℝ (Fin n)) 0)
      (chart_mem_atlas _ _)
    simpa [chartAt_self_eq] using h
  · have h := T.isPiecewiseAffineOn_chart_symm (chartAt (EuclideanSpace ℝ (Fin n)) 0)
      (chart_mem_atlas _ _)
    simpa [chartAt_self_eq] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphOn_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphOn_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphOn_euclidean ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPLHomeomorphOn_euclidean

open _root_.Classical in
theorem IsPolyhedralManifold.exists_simplicialComplex {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsPolyhedralManifold (n := n) m S) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ K.space = S ∧ IsCombinatorialManifold m K := by
  obtain ⟨T, hT⟩ := hS
  let _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hf := T.piece.isPLHomeomorphOn_euclidean
  have hpoly : IsPolyhedron S := by
    rw [← hf.image_eq]
    exact T.piece.isPolyhedron_space.image_of_isPiecewiseAffineOn hf.isPiecewiseAffineOn
        hf.bijOn.injOn
  obtain ⟨K, hfinite, hspace⟩ := hpoly.exists_simplicialComplex
  let _ : Finite K.faces := hfinite.to_subtype
  refine ⟨K, hfinite, hspace, hT.of_isPLHomeomorphOn (f := T.piece.map) ?_⟩
  rwa [hspace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_simplicialComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_simplicialComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_simplicialComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_simplicialComplex

end DifferentialGeometry.Topology.PiecewiseLinear
