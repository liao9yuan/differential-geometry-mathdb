/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex

structure OpenCellProfile where
  vertices : ℕ
  edges : ℕ
  faces : ℕ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile

namespace OpenCellProfile

def eulerChar (C : OpenCellProfile) : ℤ := C.vertices - C.edges + C.faces

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar

inductive Operation where
  | alpha
  | beta
  | gamma
  | delta

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.Operation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.Operation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.Operation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.Operation

def apply (C : OpenCellProfile) : Operation → OpenCellProfile
  | .alpha => ⟨C.vertices + 1, C.edges + 1, C.faces⟩
  | .beta => ⟨C.vertices + 1, C.edges + 1, C.faces⟩
  | .gamma => ⟨C.vertices, C.edges + 1, C.faces + 1⟩
  | .delta => ⟨C.vertices, C.edges + 1, C.faces + 1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.apply

theorem eulerChar_apply (C : OpenCellProfile) (o : Operation) :
    eulerChar (apply C o) = eulerChar C := by
  cases o <;> simp [apply, eulerChar] <;> omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_apply

def applyOperations : OpenCellProfile → List Operation → OpenCellProfile
  | C, [] => C
  | C, o :: ops => applyOperations (apply C o) ops

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.applyOperations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.applyOperations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.applyOperations ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.applyOperations

theorem eulerChar_applyOperations (C : OpenCellProfile) (ops : List Operation) :
    eulerChar (applyOperations C ops) = eulerChar C := by
  induction ops generalizing C with
  | nil => rfl
  | cons o ops ih => rw [applyOperations, ih, eulerChar_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_applyOperations then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_applyOperations"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_applyOperations ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_applyOperations

def IsRefinement (C' C : OpenCellProfile) : Prop :=
  ∃ ops : List Operation, applyOperations C ops = C'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.IsRefinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.IsRefinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.IsRefinement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.IsRefinement

theorem eulerChar_eq_of_isRefinement {C' C : OpenCellProfile} (h : IsRefinement C' C) :
    eulerChar C' = eulerChar C := by
  obtain ⟨ops, rfl⟩ := h
  exact eulerChar_applyOperations C ops

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_eq_of_isRefinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_eq_of_isRefinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_eq_of_isRefinement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenCellProfile.eulerChar_eq_of_isRefinement

end OpenCellProfile

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def simplicialOpenCellProfile
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : OpenCellProfile where
  vertices := (facesOfCard K.toPreAbstractSimplicialComplex 1).card
  edges := (facesOfCard K.toPreAbstractSimplicialComplex 2).card
  faces := (facesOfCard K.toPreAbstractSimplicialComplex 3).card

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile

theorem simplicialOpenCellProfile_eulerChar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hd : ∀ s ∈ K.faces, s.card ≤ 3) :
    (simplicialOpenCellProfile K).eulerChar = eulerChar K := by
  rw [eulerChar, faceEulerChar_eq_of_card_le_three K.toPreAbstractSimplicialComplex hd]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile_eulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile_eulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile_eulerChar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialOpenCellProfile_eulerChar

open _root_.Classical in
theorem eulerChar_eq_of_faces_eq
    (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] (hfaces : K.faces = L.faces) :
    eulerChar K = eulerChar L := by
  apply faceEulerChar_congr
  ext s
  rw [hfaces]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_faces_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_faces_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_faces_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_of_faces_eq

open _root_.Classical in
theorem eulerChar_eq_add_sub_of_faces_union
    (M K L : Geometry.SimplicialComplex ℝ E)
    [Finite M.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : M.faces = K.faces ∪ L.faces) :
    eulerChar M = eulerChar K + eulerChar L - eulerChar (intersectionComplex K L) := by
  have hM : M.toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex := by
    ext s
    change s ∈ M.faces ↔ s ∈ K.faces ∪ L.faces
    rw [hfaces]
  have hI : (intersectionComplex K L).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex := by
    ext s
    rfl
  have hEuler := faceEulerChar_sup_add_faceEulerChar_inf
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex
  have hMchar := faceEulerChar_congr hM
  have hIchar := faceEulerChar_congr hI
  unfold eulerChar
  rw [hMchar, hIchar]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_sub_of_faces_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_sub_of_faces_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_sub_of_faces_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_sub_of_faces_union

open _root_.Classical in
theorem eulerChar_eq_zero_of_faces_eq_empty
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hfaces : K.faces = ∅) : eulerChar K = 0 := by
  have hK : K.toPreAbstractSimplicialComplex =
      (⊥ : PreAbstractSimplicialComplex E) := by
    ext s
    change s ∈ K.faces ↔ False
    rw [hfaces]
    simp
  unfold eulerChar
  exact (faceEulerChar_congr hK).trans faceEulerChar_bot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_zero_of_faces_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_zero_of_faces_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_zero_of_faces_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_zero_of_faces_eq_empty

open _root_.Classical in
theorem eulerChar_eq_add_of_faces_disjoint_union
    (M K L : Geometry.SimplicialComplex ℝ E)
    [Finite M.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : M.faces = K.faces ∪ L.faces) (hdisjoint : Disjoint K.faces L.faces) :
    eulerChar M = eulerChar K + eulerChar L := by
  have hI : (intersectionComplex K L).faces = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hdisjoint
  rw [eulerChar_eq_add_sub_of_faces_union M K L hfaces,
    eulerChar_eq_zero_of_faces_eq_empty (intersectionComplex K L) hI, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_disjoint_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_disjoint_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_disjoint_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_disjoint_union

open _root_.Classical in
theorem eulerChar_eq_add_of_faces_union_of_isPLSphere_one
    [FiniteDimensional ℝ E]
    (M K L : Geometry.SimplicialComplex ℝ E)
    [Finite M.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : M.faces = K.faces ∪ L.faces)
    (hinter : IsPLSphere 1 (intersectionComplex K L).space) :
    eulerChar M = eulerChar K + eulerChar L := by
  rw [eulerChar_eq_add_sub_of_faces_union M K L hfaces,
    eulerChar_of_isPLSphere_one (intersectionComplex K L) hinter, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_union_of_isPLSphere_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_union_of_isPLSphere_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_union_of_isPLSphere_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eulerChar_eq_add_of_faces_union_of_isPLSphere_one

end DifferentialGeometry.Topology.PiecewiseLinear
