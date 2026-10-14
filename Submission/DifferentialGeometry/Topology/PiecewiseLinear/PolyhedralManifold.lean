/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

open _root_.Classical in
def IsPolyhedralManifoldWithBoundary (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsCombinatorialManifoldWithBoundary m T.piece.complex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary

open _root_.Classical in
def IsPolyhedralManifold (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsCombinatorialManifold m T.piece.complex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold

open _root_.Classical in
theorem IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece
    {m : ℕ} {P : Set X} (hP : IsPolyhedralManifoldWithBoundary (n := n) m P)
    (T : PLPiece n X P) : IsCombinatorialManifoldWithBoundary m T.piece.complex := by
  obtain ⟨T₀, hT₀⟩ := hP
  have := T₀.piece.finite_faces.to_subtype
  have := T.piece.finite_faces.to_subtype
  exact hT₀.of_isPLHomeomorphOn (T₀.piece.isPLHomeomorphOn_transition T.piece)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece

open _root_.Classical in
theorem IsPolyhedralManifold.isCombinatorialManifold_of_piece {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifold (n := n) m P) (T : PLPiece n X P) :
    IsCombinatorialManifold m T.piece.complex := by
  obtain ⟨T₀, hT₀⟩ := hP
  have := T₀.piece.finite_faces.to_subtype
  have := T.piece.finite_faces.to_subtype
  exact hT₀.of_isPLHomeomorphOn (T₀.piece.isPLHomeomorphOn_transition T.piece)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCombinatorialManifold_of_piece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCombinatorialManifold_of_piece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCombinatorialManifold_of_piece ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCombinatorialManifold_of_piece

open _root_.Classical in
theorem isPolyhedralManifoldWithBoundary_of_pieceIn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} {P : Set X} (T : PLPieceIn E n X P)
    (hT : IsCombinatorialManifoldWithBoundary m T.complex) :
    IsPolyhedralManifoldWithBoundary (n := n) m P := by
  obtain ⟨T'⟩ := T.exists_pLPiece
  have := T.finite_faces.to_subtype
  have := T'.piece.finite_faces.to_subtype
  exact ⟨T', hT.of_isPLHomeomorphOn (T.isPLHomeomorphOn_transition T'.piece)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifoldWithBoundary_of_pieceIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifoldWithBoundary_of_pieceIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifoldWithBoundary_of_pieceIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifoldWithBoundary_of_pieceIn

open _root_.Classical in
theorem isPolyhedralManifold_of_pieceIn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} {P : Set X} (T : PLPieceIn E n X P)
    (hT : IsCombinatorialManifold m T.complex) : IsPolyhedralManifold (n := n) m P := by
  obtain ⟨T'⟩ := T.exists_pLPiece
  have := T.finite_faces.to_subtype
  have := T'.piece.finite_faces.to_subtype
  exact ⟨T', hT.of_isPLHomeomorphOn (T.isPLHomeomorphOn_transition T'.piece)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifold_of_pieceIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifold_of_pieceIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifold_of_pieceIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedralManifold_of_pieceIn

theorem IsPolyhedralManifoldWithBoundary.isCompact {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n) m P) : IsCompact P := by
  obtain ⟨T, _⟩ := hP
  exact T.piece.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isCompact

theorem IsPolyhedralManifold.isCompact {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifold (n := n) m P) : IsCompact P := by
  obtain ⟨T, _⟩ := hP
  exact T.piece.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isCompact

theorem IsPolyhedralBall.isPolyhedralManifoldWithBoundary {m : ℕ} {P : Set X}
    (hP : IsPolyhedralBall (n := n) (m + 1) P) :
    IsPolyhedralManifoldWithBoundary (n := n) (m + 1) P := by
  obtain ⟨T, hT⟩ := hP
  have := T.piece.finite_faces.to_subtype
  exact ⟨T, hT.isCombinatorialManifoldWithBoundary⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPolyhedralManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPolyhedralManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPolyhedralManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPolyhedralManifoldWithBoundary

theorem IsPolyhedralSphere.isPolyhedralManifold {m : ℕ} {P : Set X}
    (hP : IsPolyhedralSphere (n := n) (m + 1) P) :
    IsPolyhedralManifold (n := n) (m + 1) P := by
  obtain ⟨T, hT⟩ := hP
  have := T.piece.finite_faces.to_subtype
  exact ⟨T, hT.isCombinatorialManifold⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.isPolyhedralManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.isPolyhedralManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.isPolyhedralManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.isPolyhedralManifold

theorem IsPolyhedralManifold.isPolyhedralManifoldWithBoundary {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifold (n := n) m P) :
    IsPolyhedralManifoldWithBoundary (n := n) m P := by
  obtain ⟨T, hT⟩ := hP
  exact ⟨T, hT.isCombinatorialManifoldWithBoundary⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isPolyhedralManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isPolyhedralManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isPolyhedralManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isPolyhedralManifoldWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
