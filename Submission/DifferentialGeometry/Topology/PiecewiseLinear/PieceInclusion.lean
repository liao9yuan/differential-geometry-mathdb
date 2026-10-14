/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem IsPolyhedralBall.nonempty {m : ℕ} {P : Set X}
    (hP : IsPolyhedralBall (n := n) m P) : P.Nonempty := by
  obtain ⟨T, hT⟩ := hP
  rw [← T.piece.bijOn.image_eq]
  exact hT.nonempty.image T.piece.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.nonempty

theorem IsPolyhedralBall.isPLBall_inter_preimage {m : ℕ} {P Y : Set X}
    (hP : IsPolyhedralBall (n := n) m P) (T : PLPieceIn E n X Y) (hPY : P ⊆ Y) :
    IsPLBall m (T.complex.space ∩ T.map ⁻¹' P) := by
  obtain ⟨S, hS⟩ := hP
  exact hS.of_isPLHomeomorphOn (S.piece.isPLHomeomorphOn_transition_of_subset T hPY)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLBall_inter_preimage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLBall_inter_preimage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLBall_inter_preimage ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLBall_inter_preimage

theorem PLPieceIn.exists_restrict_of_isPolyhedron {Y : Set X} (T : PLPieceIn E n X Y)
    {P : Set E} (hP : IsPolyhedron P) (hPK : P ⊆ T.complex.space) :
    ∃ S : PLPieceIn E n X (T.map '' P), S.complex.space = P ∧ S.map = T.map := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨K, hK, hfin, hrestrict⟩ := exists_isSubdivision_restrict_space T.complex hP hPK
  let T' := T.subdivide K hK hfin
  let S := T'.restrict (PiecewiseLinear.restrict K P) (restrict_faces_subset K P)
  have h : ∃ S : PLPieceIn E n X (T.map '' (PiecewiseLinear.restrict K P).space),
      S.complex.space = P ∧ S.map = T.map := ⟨S, hrestrict, rfl⟩
  rwa [hrestrict] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedron

theorem PLPieceIn.isPolyhedralBall_image {Y : Set X} (T : PLPieceIn E n X Y)
    {m : ℕ} {P : Set E} (hP : IsPLBall m P) (hPK : P ⊆ T.complex.space) :
    IsPolyhedralBall (n := n) m (T.map '' P) := by
  obtain ⟨S, hS, -⟩ := T.exists_restrict_of_isPolyhedron hP.isPolyhedron hPK
  exact isPolyhedralBall_of_pieceIn S (hS.symm ▸ hP)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPolyhedralBall_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPolyhedralBall_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPolyhedralBall_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.isPolyhedralBall_image

theorem PLPieceIn.exists_restrict_of_isPolyhedralBall {m : ℕ} {P Y : Set X}
    (T : PLPieceIn E n X Y) (hP : IsPolyhedralBall (n := n) m P) (hPY : P ⊆ Y) :
    ∃ S : PLPieceIn E n X P,
      S.complex.space = T.complex.space ∩ T.map ⁻¹' P ∧ S.map = T.map := by
  have hB := hP.isPLBall_inter_preimage T hPY
  obtain ⟨S, hspace, hmap⟩ := T.exists_restrict_of_isPolyhedron hB.isPolyhedron _root_.Set.inter_subset_left
  have himage : T.map '' (T.complex.space ∩ T.map ⁻¹' P) = P := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (hPY hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have h : ∃ S : PLPieceIn E n X (T.map '' (T.complex.space ∩ T.map ⁻¹' P)),
      S.complex.space = T.complex.space ∩ T.map ⁻¹' P ∧ S.map = T.map := ⟨S, hspace, hmap⟩
  rwa [himage] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedralBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedralBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedralBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_restrict_of_isPolyhedralBall

end DifferentialGeometry.Topology.PiecewiseLinear
