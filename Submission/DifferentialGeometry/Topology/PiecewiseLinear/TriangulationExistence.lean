/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ChartGlue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPiece.exists_union_chart [T2Space X] [HasGroupoid X (plGroupoid n)] {Y : Set X}
    (T : PLPiece n X Y) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) : Nonempty (PLPiece n X (Y ∪ e.symm '' C)) := by
  obtain ⟨T'⟩ := T.piece.exists_glue_chart e he hC hCe
  exact T'.exists_pLPiece

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.exists_union_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.exists_union_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.exists_union_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPiece.exists_union_chart

theorem exists_pLPiece_biUnion [T2Space X] [Nonempty X] [HasGroupoid X (plGroupoid n)]
    (V : X → Set X)
    (hV : ∀ x, ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope C ∧
      C ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).target ∧
      V x = (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C)
    (t : Finset X) : Nonempty (PLPiece n X (⋃ x ∈ t, V x)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hempty : (⋃ x ∈ (∅ : Finset X), V x) = ∅ := by simp
    rw [hempty]
    exact ⟨⟨0, PLPieceIn.empty _⟩⟩
  | @insert a t _ ih =>
    obtain ⟨T⟩ := ih
    obtain ⟨C, hC, hCe, hVa⟩ := hV a
    obtain ⟨T'⟩ := T.exists_union_chart _ (chart_mem_atlas _ a) hC hCe
    rw [Finset.set_biUnion_insert, _root_.Set.union_comm, hVa]
    exact ⟨T'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_biUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_biUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_biUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_biUnion

theorem exists_pLPiece_univ [CompactSpace X] [T2Space X] [Nonempty X]
    [HasGroupoid X (plGroupoid n)] : Nonempty (PLPiece n X _root_.Set.univ) := by
  classical
  choose C hC hCe hCnhds using exists_isHPolytope_image_symm_mem_nhds (n := n) (X := X)
  obtain ⟨t, -, hcover⟩ := isCompact_univ.elim_nhds_subcover
    (fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C x) fun x _ => hCnhds x
  obtain ⟨T⟩ := exists_pLPiece_biUnion
    (fun x => (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C x)
    (fun x => ⟨C x, hC x, hCe x, rfl⟩) t
  have huniv : (⋃ x ∈ t, (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C x) = univ :=
    _root_.Set.eq_univ_of_univ_subset hcover
  rw [huniv] at T
  exact ⟨T⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_univ ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_pLPiece_univ

theorem exists_pLTriangulation [CompactSpace X] [T2Space X] [Nonempty X]
    [HasGroupoid X (plGroupoid n)] : Nonempty (PLTriangulation n X) := by
  obtain ⟨T⟩ := exists_pLPiece_univ (n := n) (X := X)
  exact ⟨T.toPLTriangulation⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_pLTriangulation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_pLTriangulation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_pLTriangulation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_pLTriangulation

end DifferentialGeometry.Topology.PiecewiseLinear
